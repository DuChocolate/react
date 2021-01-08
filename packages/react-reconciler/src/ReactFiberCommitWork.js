/**
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 * @flow
 */

import type {
  Instance,
  TextInstance,
  Container,
  ChildSet,
  UpdatePayload,
} from './ReactFiberHostConfig';
import type {Fiber} from './ReactFiber';
import type {FiberRoot} from './ReactFiberRoot';
import type {ExpirationTime} from './ReactFiberExpirationTime';
import type {CapturedValue, CapturedError} from './ReactCapturedValue';
import type {SuspenseState} from './ReactFiberSuspenseComponent';

import {
  enableSchedulerTracing,
  enableProfilerTimer,
} from 'shared/ReactFeatureFlags';
import {
  ClassComponent,
  HostRoot,
  HostComponent,
  HostText,
  HostPortal,
  Profiler,
  SuspenseComponent,
  IncompleteClassComponent,
} from 'shared/ReactWorkTags';
import {
  invokeGuardedCallback,
  hasCaughtError,
  clearCaughtError,
} from 'shared/ReactErrorUtils';
import {
  ContentReset,
  Placement,
  Snapshot,
  Update,
  Callback,
} from 'shared/ReactSideEffectTags';
import getComponentName from 'shared/getComponentName';
import invariant from 'shared/invariant';
import warningWithoutStack from 'shared/warningWithoutStack';

import {NoWork, Sync} from './ReactFiberExpirationTime';
import {onCommitUnmount} from './ReactFiberDevToolsHook';
import {startPhaseTimer, stopPhaseTimer} from './ReactDebugFiberPerf';
import {getStackByFiberInDevAndProd} from './ReactCurrentFiber';
import {logCapturedError} from './ReactFiberErrorLogger';
import {getCommitTime} from './ReactProfilerTimer';
import {commitUpdateQueue} from './ReactUpdateQueue';
import {
  getPublicInstance,
  supportsMutation,
  supportsPersistence,
  commitMount,
  commitUpdate,
  resetTextContent,
  commitTextUpdate,
  appendChild,
  appendChildToContainer,
  insertBefore,
  insertInContainerBefore,
  removeChild,
  removeChildFromContainer,
  replaceContainerChildren,
  createContainerChildSet,
  hideInstance,
  hideTextInstance,
  unhideInstance,
  unhideTextInstance,
} from './ReactFiberHostConfig';
import {
  captureCommitPhaseError,
  requestCurrentTime,
  scheduleWork,
} from './ReactFiberScheduler';

let didWarnAboutUndefinedSnapshotBeforeUpdate: Set<mixed> | null = null;
if (__DEV__) {
  didWarnAboutUndefinedSnapshotBeforeUpdate = new Set();
}

export function logError(boundary: Fiber, errorInfo: CapturedValue<mixed>) {
  const source = errorInfo.source;
  let stack = errorInfo.stack;
  if (stack === null && source !== null) {
    stack = getStackByFiberInDevAndProd(source);
  }

  const capturedError: CapturedError = {
    componentName: source !== null ? getComponentName(source.type) : null,
    componentStack: stack !== null ? stack : '',
    error: errorInfo.value,
    errorBoundary: null,
    errorBoundaryName: null,
    errorBoundaryFound: false,
    willRetry: false,
  };

  if (boundary !== null && boundary.tag === ClassComponent) {
    capturedError.errorBoundary = boundary.stateNode;
    capturedError.errorBoundaryName = getComponentName(boundary.type);
    capturedError.errorBoundaryFound = true;
    capturedError.willRetry = true;
  }

  try {
    logCapturedError(capturedError);
  } catch (e) {
    // This method must not throw, or React internal state will get messed up.
    // If console.error is overridden, or logCapturedError() shows a dialog that throws,
    // we want to report this error outside of the normal stack as a last resort.
    // https://github.com/facebook/react/issues/13188
    setTimeout(() => {
      throw e;
    });
  }
}

const callComponentWillUnmountWithTimer = function(current, instance) {
  startPhaseTimer(current, 'componentWillUnmount');
  instance.props = current.memoizedProps;
  instance.state = current.memoizedState;
  instance.componentWillUnmount();
  stopPhaseTimer();
};

// Capture errors so they don't interrupt unmounting.
function safelyCallComponentWillUnmount(current, instance) {
  if (__DEV__) {
    invokeGuardedCallback(
      null,
      callComponentWillUnmountWithTimer,
      null,
      current,
      instance,
    );
    if (hasCaughtError()) {
      const unmountError = clearCaughtError();
      captureCommitPhaseError(current, unmountError);
    }
  } else {
    try {
      callComponentWillUnmountWithTimer(current, instance);
    } catch (unmountError) {
      captureCommitPhaseError(current, unmountError);
    }
  }
}

function safelyDetachRef(current: Fiber) {
  const ref = current.ref;
  if (ref !== null) {
    if (typeof ref === 'function') {
      if (__DEV__) {
        invokeGuardedCallback(null, ref, null, null);
        if (hasCaughtError()) {
          const refError = clearCaughtError();
          captureCommitPhaseError(current, refError);
        }
      } else {
        try {
          ref(null);
        } catch (refError) {
          captureCommitPhaseError(current, refError);
        }
      }
    } else {
      ref.current = null;
    }
  }
}

/**
 * 该方法做的主要事情：
 * 1、在 class 组件中通过 prevProps、prevState 获取状态快照，用于 componentDidUpdate 生命周期；
 * 2、状态快照的获取通过 getSnapshotBeforeUpdate 生命周期执行后的返回值 
 * commitBeforeMutationLifeCycles 中只有在更新任务是 classComponent 时才有工作。
 */
function commitBeforeMutationLifeCycles(
  current: Fiber | null,
  finishedWork: Fiber,
): void {
  switch (finishedWork.tag) {
    case ClassComponent: {
      if (finishedWork.effectTag & Snapshot) {
        if (current !== null) {
          // 不是初次加载
          // 组件初次加载执行 DidMount 生命周期函数不走 DidUpdate 不需要保存快照对象
          const prevProps = current.memoizedProps;
          const prevState = current.memoizedState;
          startPhaseTimer(finishedWork, 'getSnapshotBeforeUpdate');
          // 得到当前 class 组件的实例
          const instance = finishedWork.stateNode;
          // 更新实例上的 props 和 state
          instance.props = finishedWork.memoizedProps;
          instance.state = finishedWork.memoizedState;
          // 调用 getSnapshotBeforeUpdate 生命周期方法
          const snapshot = instance.getSnapshotBeforeUpdate(
            prevProps,
            prevState,
          );
          if (__DEV__) {
            const didWarnSet = ((didWarnAboutUndefinedSnapshotBeforeUpdate: any): Set<
              mixed,
            >);
            if (snapshot === undefined && !didWarnSet.has(finishedWork.type)) {
              didWarnSet.add(finishedWork.type);
              warningWithoutStack(
                false,
                '%s.getSnapshotBeforeUpdate(): A snapshot value (or null) ' +
                  'must be returned. You have returned undefined.',
                getComponentName(finishedWork.type),
              );
            }
          }
          // 保存到 instance.__reactInternalSnapshotBeforeUpdate 给 DidUpdate 生命周期方法使用
          instance.__reactInternalSnapshotBeforeUpdate = snapshot;
          stopPhaseTimer();
        }
      }
      return;
    }
    case HostRoot:
    case HostComponent:
    case HostText:
    case HostPortal:
    case IncompleteClassComponent:
      // Nothing to do for these component types
      return;
    default: {
      invariant(
        false,
        'This unit of work tag should not have side-effects. This error is ' +
          'likely caused by a bug in React. Please file an issue.',
      );
    }
  }
}

/**
 * 这个方法会执行 componentDidMount 或者 componentDidUpdate 生命周期方法，最后调用 commitUpdateQueue。
 */
function commitLifeCycles(
  finishedRoot: FiberRoot,
  current: Fiber | null,
  finishedWork: Fiber,
  committedExpirationTime: ExpirationTime,
): void {
  switch (finishedWork.tag) {
    case ClassComponent: {
      const instance = finishedWork.stateNode;
      if (finishedWork.effectTag & Update) {
        if (current === null) {
          // 首次渲染
          startPhaseTimer(finishedWork, 'componentDidMount');
          instance.props = finishedWork.memoizedProps;
          instance.state = finishedWork.memoizedState;
          instance.componentDidMount();
          stopPhaseTimer();
        } else {
          // 组件更新
          const prevProps = current.memoizedProps;
          const prevState = current.memoizedState;
          startPhaseTimer(finishedWork, 'componentDidUpdate');
          instance.props = finishedWork.memoizedProps;
          instance.state = finishedWork.memoizedState;
          instance.componentDidUpdate(
            prevProps,
            prevState,
            instance.__reactInternalSnapshotBeforeUpdate,
          );
          stopPhaseTimer();
        }
      }
      const updateQueue = finishedWork.updateQueue;
      if (updateQueue !== null) {
        instance.props = finishedWork.memoizedProps;
        instance.state = finishedWork.memoizedState;
        commitUpdateQueue(
          finishedWork,
          updateQueue,
          instance,
          committedExpirationTime,
        );
      }
      return;
    }
    case HostRoot: {
      const updateQueue = finishedWork.updateQueue;
      if (updateQueue !== null) {
        let instance = null;
        if (finishedWork.child !== null) {
          switch (finishedWork.child.tag) {
            case HostComponent:
              instance = getPublicInstance(finishedWork.child.stateNode);
              break;
            case ClassComponent:
              instance = finishedWork.child.stateNode;
              break;
          }
        }
        // 因为ReactDOM.render也有回调函数，所以也要调用commitUpdateQueue。
        commitUpdateQueue(
          finishedWork,
          updateQueue,
          instance,
          committedExpirationTime,
        );
      }
      return;
    }
    case HostComponent: {
      const instance: Instance = finishedWork.stateNode;

      // Renderers may schedule work to be done after host components are mounted
      // (eg DOM renderer may schedule auto-focus for inputs and form controls).
      // These effects should only be committed when components are first mounted,
      // aka when there is no current/alternate.
      if (current === null && finishedWork.effectTag & Update) {
        const type = finishedWork.type;
        const props = finishedWork.memoizedProps;
        // 这个函数只是对 input 标签有 auto-focus 的情况进行处理
        commitMount(instance, type, props, finishedWork);
      }

      return;
    }
    case HostText: {
      // We have no life-cycles associated with text.
      return;
    }
    case HostPortal: {
      // We have no life-cycles associated with portals.
      return;
    }
    case Profiler: {
      if (enableProfilerTimer) {
        const onRender = finishedWork.memoizedProps.onRender;

        if (enableSchedulerTracing) {
          onRender(
            finishedWork.memoizedProps.id,
            current === null ? 'mount' : 'update',
            finishedWork.actualDuration,
            finishedWork.treeBaseDuration,
            finishedWork.actualStartTime,
            getCommitTime(),
            finishedRoot.memoizedInteractions,
          );
        } else {
          onRender(
            finishedWork.memoizedProps.id,
            current === null ? 'mount' : 'update',
            finishedWork.actualDuration,
            finishedWork.treeBaseDuration,
            finishedWork.actualStartTime,
            getCommitTime(),
          );
        }
      }
      return;
    }
    case SuspenseComponent: {
      if (finishedWork.effectTag & Callback) {
        // In non-strict mode, a suspense boundary times out by commiting
        // twice: first, by committing the children in an inconsistent state,
        // then hiding them and showing the fallback children in a subsequent
        // commit.
        const newState: SuspenseState = {
          alreadyCaptured: true,
          didTimeout: false,
          timedOutAt: NoWork,
        };
        finishedWork.memoizedState = newState;
        scheduleWork(finishedWork, Sync);
        return;
      }
      let oldState: SuspenseState | null =
        current !== null ? current.memoizedState : null;
      let newState: SuspenseState | null = finishedWork.memoizedState;
      let oldDidTimeout = oldState !== null ? oldState.didTimeout : false;

      let newDidTimeout;
      let primaryChildParent = finishedWork;
      if (newState === null) {
        newDidTimeout = false;
      } else {
        newDidTimeout = newState.didTimeout;
        if (newDidTimeout) {
          primaryChildParent = finishedWork.child;
          newState.alreadyCaptured = false;
          if (newState.timedOutAt === NoWork) {
            // If the children had not already timed out, record the time.
            // This is used to compute the elapsed time during subsequent
            // attempts to render the children.
            newState.timedOutAt = requestCurrentTime();
          }
        }
      }

      if (newDidTimeout !== oldDidTimeout && primaryChildParent !== null) {
        hideOrUnhideAllChildren(primaryChildParent, newDidTimeout);
      }
      return;
    }
    case IncompleteClassComponent:
      break;
    default: {
      invariant(
        false,
        'This unit of work tag should not have side-effects. This error is ' +
          'likely caused by a bug in React. Please file an issue.',
      );
    }
  }
}

function hideOrUnhideAllChildren(finishedWork, isHidden) {
  if (supportsMutation) {
    // We only have the top Fiber that was inserted but we need recurse down its
    // children to find all the terminal nodes.
    let node: Fiber = finishedWork;
    while (true) {
      if (node.tag === HostComponent) {
        const instance = node.stateNode;
        if (isHidden) {
          hideInstance(instance);
        } else {
          unhideInstance(node.stateNode, node.memoizedProps);
        }
      } else if (node.tag === HostText) {
        const instance = node.stateNode;
        if (isHidden) {
          hideTextInstance(instance);
        } else {
          unhideTextInstance(instance, node.memoizedProps);
        }
      } else if (node.child !== null) {
        node.child.return = node;
        node = node.child;
        continue;
      }
      if (node === finishedWork) {
        return;
      }
      while (node.sibling === null) {
        if (node.return === null || node.return === finishedWork) {
          return;
        }
        node = node.return;
      }
      node.sibling.return = node.return;
      node = node.sibling;
    }
  }
}

function commitAttachRef(finishedWork: Fiber) {
  const ref = finishedWork.ref;
  if (ref !== null) {
    const instance = finishedWork.stateNode;
    let instanceToUse;
    switch (finishedWork.tag) {
      case HostComponent:
        instanceToUse = getPublicInstance(instance);
        break;
      default:
        instanceToUse = instance;
    }
    if (typeof ref === 'function') {
      ref(instanceToUse);
    } else {
      if (__DEV__) {
        if (!ref.hasOwnProperty('current')) {
          warningWithoutStack(
            false,
            'Unexpected ref object provided for %s. ' +
              'Use either a ref-setter function or React.createRef().%s',
            getComponentName(finishedWork.type),
            getStackByFiberInDevAndProd(finishedWork),
          );
        }
      }

      ref.current = instanceToUse;
    }
  }
}

function commitDetachRef(current: Fiber) {
  const currentRef = current.ref;
  if (currentRef !== null) {
    if (typeof currentRef === 'function') {
      currentRef(null);
    } else {
      currentRef.current = null;
    }
  }
}

// User-originating errors (lifecycles and refs) should not interrupt
// deletion, so don't let them throw. Host-originating errors should
// interrupt deletion, so it's okay
/**
 * 这个方法会对不同的节点做不同的处理，对ClassComponent会执行它的生命周期以及卸载ref，
 * 对HostComponent卸载ref，对HostPortal重新调用unmountHostComponents，这里我们就明白了为什么上一个方法（commitNestedUnmounts）遇到HostPortal就停止了对它的子树的遍历，
 * 因为他会重新递归调用unmountHostComponents遍历子树。
 */
function commitUnmount(current: Fiber): void {
  onCommitUnmount(current);

  switch (current.tag) {
    case ClassComponent: {
      // 卸载ref
      safelyDetachRef(current);
      const instance = current.stateNode;
      // 执行WillUnmount方法，这个时候真实dom还没有卸载，即将卸载
      if (typeof instance.componentWillUnmount === 'function') {
        safelyCallComponentWillUnmount(current, instance);
      }
      return;
    }
    case HostComponent: {
      // 卸载ref
      safelyDetachRef(current);
      return;
    }
    case HostPortal: {
      // TODO: this is recursive.
      // We are also not using this parent because
      // the portal will get pushed immediately.
      if (supportsMutation) {
        // 递归调用，遍历子树
        unmountHostComponents(current);
      } else if (supportsPersistence) {
        emptyPortalContainer(current);
      }
      return;
    }
  }
}

/**
 * 这个方法使用深度优先遍历整棵dom节点为父节点的树。子节点还有可能是react组件或者HostPortal。
 * 这里对每个节点都要调用commitUnmount。
 * 如果遇到了HostPortal就会停止对它下面的子树进行遍历，因为在commitUnmount中会对HostPortal类型有个特殊的处理。
 */
function commitNestedUnmounts(root: Fiber): void {
  // While we're inside a removed host node we don't want to call
  // removeChild on the inner nodes because they're removed by the top
  // call anyway. We also want to call componentWillUnmount on all
  // composites before this host node is removed from the tree. Therefore
  // we do an inner loop while we're still inside the host node.
  let node: Fiber = root;
  while (true) {
    commitUnmount(node);
    // Visit children because they may contain more composite or host nodes.
    // Skip portals because commitUnmount() currently visits them recursively.
    if (
      node.child !== null &&
      // If we use mutation we drill down into portals using commitUnmount above.
      // If we don't use mutation we drill down into portals here instead.
      (!supportsMutation || node.tag !== HostPortal)
    ) {
      // 如果是HostPortal就直接跳过子树的遍历，所以下面不执行
      node.child.return = node;
      node = node.child;
      continue;
    }
    if (node === root) {
      return;
    }
    while (node.sibling === null) {
      if (node.return === null || node.return === root) {
        return;
      }
      node = node.return;
    }
    node.sibling.return = node.return;
    node = node.sibling;
  }
}

function detachFiber(current: Fiber) {
  // Cut off the return pointers to disconnect it from the tree. Ideally, we
  // should clear the child pointer of the parent alternate to let this
  // get GC:ed but we don't know which for sure which parent is the current
  // one so we'll settle for GC:ing the subtree of this child. This child
  // itself will be GC:ed when the parent updates the next time.
  current.return = null;
  current.child = null;
  if (current.alternate) {
    current.alternate.child = null;
    current.alternate.return = null;
  }
}

function emptyPortalContainer(current: Fiber) {
  if (!supportsPersistence) {
    return;
  }

  const portal: {containerInfo: Container, pendingChildren: ChildSet} =
    current.stateNode;
  const {containerInfo} = portal;
  const emptyChildSet = createContainerChildSet(containerInfo);
  replaceContainerChildren(containerInfo, emptyChildSet);
}

function commitContainer(finishedWork: Fiber) {
  if (!supportsPersistence) {
    return;
  }

  switch (finishedWork.tag) {
    case ClassComponent: {
      return;
    }
    case HostComponent: {
      return;
    }
    case HostText: {
      return;
    }
    case HostRoot:
    case HostPortal: {
      const portalOrRoot: {
        containerInfo: Container,
        pendingChildren: ChildSet,
      } =
        finishedWork.stateNode;
      const {containerInfo, pendingChildren} = portalOrRoot;
      replaceContainerChildren(containerInfo, pendingChildren);
      return;
    }
    default: {
      invariant(
        false,
        'This unit of work tag should not have side-effects. This error is ' +
          'likely caused by a bug in React. Please file an issue.',
      );
    }
  }
}

function getHostParentFiber(fiber: Fiber): Fiber {
  let parent = fiber.return;
  while (parent !== null) {
    if (isHostParent(parent)) {
      return parent;
    }
    parent = parent.return;
  }
  invariant(
    false,
    'Expected to find a host parent. This error is likely caused by a bug ' +
      'in React. Please file an issue.',
  );
}

function isHostParent(fiber: Fiber): boolean {
  return (
    fiber.tag === HostComponent ||
    fiber.tag === HostRoot ||
    fiber.tag === HostPortal
  );
}
/**
 * 这个方法用来找到当前要执行插入的节点的现有的第一个右侧节点，如果这个方法返回null，则会直接调用parent.appendChild。
 * 所以这个函数做的事情就是：剔除掉所有的非原始 dom 节点，找到我想要的 dom 节点。
 * 注：HostPortal 也是要被剔除的，因为它不是挂载在这个地方的。
 */
function getHostSibling(fiber: Fiber): ?Instance {
  // We're going to search forward into the tree until we find a sibling host
  // node. Unfortunately, if multiple insertions are done in a row we have to
  // search past them. This leads to exponential search for the next sibling.
  // TODO: Find a more efficient way to do this.
  let node: Fiber = fiber;
  // 外层 while 循环
  siblings: while (true) {
    // If we didn't find anything, let's try the next sibling.
    // 如果没有兄弟节点，向上查找父节点，但是这个父节点可能不是原生 dom 节点
    while (node.sibling === null) {
      if (node.return === null || isHostParent(node.return)) {
        // If we pop out of the root or hit the parent the fiber we are the
        // last sibling.
        // 如果到了根结点 root 了或者是原生 dom 节点，返回 null 说明在真实的 dom 中插入的这个节点没有兄弟节点
        return null;
      }
      node = node.return;
    }
    // 下面是有兄弟节点的情况
    node.sibling.return = node.return;
    node = node.sibling;
    // 兄弟节点不是 HostComponent 也不是 HostText
    while (node.tag !== HostComponent && node.tag !== HostText) {
      // If it is not host node and, we might have a host node inside it.
      // Try to search down until we find one.
      // 兄弟节点也是将要插入的节点，跳过这个节点查找下一个兄弟节点
      if (node.effectTag & Placement) {
        // If we don't have a child, try the siblings instead.
        continue siblings;
      }
      // If we don't have a child, try the siblings instead.
      // We also skip portals because they are not part of this host tree.
      if (node.child === null || node.tag === HostPortal) {
        continue siblings;
      } else {
        // 否则返回兄弟节点的子节点
        node.child.return = node;
        node = node.child;
      }
    }
    // Check if this host node is stable or about to be placed.
    // 如果兄弟节点也是新增节点，寻找下一个兄弟节点
    // 否则，就找到了
    if (!(node.effectTag & Placement)) {
      // Found it!
      return node.stateNode;
    }
  }
}
/**
 * 1、找到 finishedWork 的父节点 parentFiber。寻找的是原生的 dom 节点对应的 fiber。如果父级不是原生 dom，则继续往上寻找。
 * 2、得到 parentFiber 对应的原生 dom 节点 parent；
 * 3、找到插入节点的后一个节点，因为需要插在它前面；
 * 4、用 insertBefore 或者 appendChild 进行子节点插入操作。
 * 
 * 注：第4步插入操作需要分情况，比如如果是原生 dom 节点是直接插入，如果是 Class 子节点是需要深度优先遍历子节点进行插入的。
 */
function commitPlacement(finishedWork: Fiber): void {
  if (!supportsMutation) {
    return;
  }

  // Recursively insert all host nodes into the parent.
  // 找到 finishedWork 的父节点 parentFiber。寻找的是原生的 dom 节点对应的 fiber。如果父级不是原生 dom，则继续往上寻找。
  // 所以 parentFiber 只有三种类型的节点： HostComponent、HostRoot、HostPortal。
  const parentFiber = getHostParentFiber(finishedWork);

  // Note: these two variables *must* always be updated together.
  let parent;
  let isContainer;

  // 得到原生 dom 节点：parent
  switch (parentFiber.tag) {
    case HostComponent:
      parent = parentFiber.stateNode;
      isContainer = false;
      break;
    case HostRoot:
      parent = parentFiber.stateNode.containerInfo;
      isContainer = true;
      break;
    case HostPortal:
      parent = parentFiber.stateNode.containerInfo;
      isContainer = true;
      break;
    default:
      invariant(
        false,
        'Invalid host parent fiber. This error is likely caused by a bug ' +
          'in React. Please file an issue.',
      );
  }
  if (parentFiber.effectTag & ContentReset) {
    // Reset the text content of the parent before doing any insertions
    resetTextContent(parent);
    // Clear ContentReset from the effect tag
    parentFiber.effectTag &= ~ContentReset;
  }

  // 这里操作 dom 使用的是 insertBefore 原生 api
  // 这个方法用来找到当前要执行插入的节点的现有的第一个右侧节点，可能存在于
  // 1、父链中任一节点的右侧节点的子树中的第一个HostComponent
  // 2、他的右侧兄弟节点或者子树中的第一个HostComponent
  const before = getHostSibling(finishedWork);
  // We only have the top Fiber that was inserted but we need recurse down its
  // children to find all the terminal nodes.
  let node: Fiber = finishedWork;
  while (true) {
    // 如果当前节点是原生 dom 节点就直接进行插入
    if (node.tag === HostComponent || node.tag === HostText) {
      if (before) {
        // 有 before 就用 insertBefore
        if (isContainer) {
          insertInContainerBefore(parent, node.stateNode, before);
        } else {
          insertBefore(parent, node.stateNode, before);
        }
      } else {
        // 没有 before 就用 appendChild
        if (isContainer) {
          appendChildToContainer(parent, node.stateNode);
        } else {
          appendChild(parent, node.stateNode);
        }
      }
    } else if (node.tag === HostPortal) {
      // 是 HostPortal 直接跳过，因为不是插在这里的
      // If the insertion itself is a portal, then we don't want to traverse
      // down its children. Instead, we'll get insertions from each child in
      // the portal directly.
    } else if (node.child !== null) {
      // 上面条件不满足其实就是 class 组件
      // 查看子节点是否存在，存在的话把子节点进行插入 continue
      node.child.return = node;
      node = node.child;
      continue;
    }
    if (node === finishedWork) {
      // 对 finishedWork 已经结束
      return;
    }
    // 其实这是一个深度优先遍历
    // 深度优先遍历 class 组件的子节点，把 class 组件的原生 dom 节点全部进行插入操作
    // 下面是深度优先遍历的退回过程，如果没有兄弟节点，就往上退回。
    while (node.sibling === null) {
      if (node.return === null || node.return === finishedWork) {
        return;
      }
      node = node.return;
    }
    node.sibling.return = node.return;
    node = node.sibling;
  }
}

function unmountHostComponents(current): void {
  // We only have the top Fiber that was deleted but we need recurse down its
  // children to find all the terminal nodes.
  let node: Fiber = current;

  // Each iteration, currentParent is populated with node's host parent if not
  // currentParentIsValid.
  let currentParentIsValid = false;

  // Note: these two variables *must* always be updated together.
  let currentParent;
  let currentParentIsContainer;

  while (true) {
    // 找到父节点，这个父节点一定是个dom节点
    if (!currentParentIsValid) {
      let parent = node.return;
      findParent: while (true) {
        invariant(
          parent !== null,
          'Expected to find a host parent. This error is likely caused by ' +
            'a bug in React. Please file an issue.',
        );
        switch (parent.tag) {
          case HostComponent:
            currentParent = parent.stateNode;
            currentParentIsContainer = false;
            break findParent;
          case HostRoot:
            currentParent = parent.stateNode.containerInfo;
            currentParentIsContainer = true;
            break findParent;
          case HostPortal:
            currentParent = parent.stateNode.containerInfo;
            currentParentIsContainer = true;
            break findParent;
        }
        parent = parent.return;
      }
      currentParentIsValid = true;
    }

    if (node.tag === HostComponent || node.tag === HostText) {
      // 如果是原生dom节点
      commitNestedUnmounts(node);
      // After all the children have unmounted, it is now safe to remove the
      // node from the tree.
      if (currentParentIsContainer) {
        removeChildFromContainer((currentParent: any), node.stateNode);
      } else {
        removeChild((currentParent: any), node.stateNode);
      }
      // Don't visit children because we already visited them.
    } else if (node.tag === HostPortal) {
      // 如果是HostPortal不会做什么操作，直接向下遍历子节点，因为它没有ref，也没有生命周期
      // When we go into a portal, it becomes the parent to remove from.
      // We will reassign it back when we pop the portal on the way up.
      currentParent = node.stateNode.containerInfo;
      currentParentIsContainer = true;
      // Visit children because portals might contain host components.
      if (node.child !== null) {
        node.child.return = node;
        node = node.child;
        continue;
      }
    } else {
      // 到这里的话，其实就是react组件节点了，调用commitUnmount，这个方法里会有生命周期的调用，ref的卸载
      commitUnmount(node);
      // Visit children because we may find more host components below.
      // 继续遍历子节点
      if (node.child !== null) {
        node.child.return = node;
        node = node.child;
        continue;
      }
    }
    // 整棵树遍历完成
    if (node === current) {
      return;
    }
    // 如果没有兄弟节点，深度优先遍历可以向父节点返回了
    while (node.sibling === null) {
      if (node.return === null || node.return === current) {
        return;
      }
      node = node.return;
      if (node.tag === HostPortal) {
        // When we go out of the portal, we need to restore the parent.
        // Since we don't keep a stack of them, we will search for it.
        currentParentIsValid = false;
      }
    }
    // 到这里代表已经没有子节点了，就向兄弟节点方向遍历
    node.sibling.return = node.return;
    node = node.sibling;
  }
}
/**
 * 在删除一个节点的时候，并不是直接删除那么简单。
 * 在删除一个节点的时候，需要去遍历整棵子树。
 * 第一，如果dom节点下面还有class组件，那么我们是要调用它的生命周期方法的（componentWillUnmount），
 * 第二，如果有HostPortal，那么还要去删除HostPortal中的节点，所以我们必须要遍历子树。
 * 这里的遍历采用树的深度优先遍历。
 */
function commitDeletion(current: Fiber): void {
  if (supportsMutation) {
    // Recursively delete all host nodes from the parent.
    // Detach refs and call componentWillUnmount() on the whole subtree.
    unmountHostComponents(current);
  } else {
    // Detach refs and call componentWillUnmount() on the whole subtree.
    commitNestedUnmounts(current);
  }
  detachFiber(current);
}

/**
 * 1、commitWork 只会更新 HostComponent（dom节点）和 HostText（文本节点）；
 * 2、HostComponent 调用 commitUpdate 更新；
 * 3、HostText 调用 commitTextUpdate 更新。
 */
function commitWork(current: Fiber | null, finishedWork: Fiber): void {
  if (!supportsMutation) {
    commitContainer(finishedWork);
    return;
  }

  switch (finishedWork.tag) {
    case ClassComponent: {
      return;
    }
    case HostComponent: {
      const instance: Instance = finishedWork.stateNode;
      if (instance != null) {
        // Commit the work prepared earlier.
        const newProps = finishedWork.memoizedProps;
        // For hydration we reuse the update path but we treat the oldProps
        // as the newProps. The updatePayload will contain the real change in
        // this case.
        const oldProps = current !== null ? current.memoizedProps : newProps;
        const type = finishedWork.type;
        // TODO: Type the updateQueue to be specific to host components.
        // updatePayload 是数组格式，[key1, val1, key2, val2]
        const updatePayload: null | UpdatePayload = (finishedWork.updateQueue: any);
        finishedWork.updateQueue = null;
        if (updatePayload !== null) {
          commitUpdate(
            instance,
            updatePayload,
            type,
            oldProps,
            newProps,
            finishedWork,
          );
        }
      }
      return;
    }
    case HostText: {
      invariant(
        finishedWork.stateNode !== null,
        'This should have a text node initialized. This error is likely ' +
          'caused by a bug in React. Please file an issue.',
      );
      const textInstance: TextInstance = finishedWork.stateNode;
      const newText: string = finishedWork.memoizedProps;
      // For hydration we reuse the update path but we treat the oldProps
      // as the newProps. The updatePayload will contain the real change in
      // this case.
      const oldText: string =
        current !== null ? current.memoizedProps : newText;
      commitTextUpdate(textInstance, oldText, newText);
      return;
    }
    case HostRoot: {
      return;
    }
    case Profiler: {
      return;
    }
    case SuspenseComponent: {
      return;
    }
    case IncompleteClassComponent: {
      return;
    }
    default: {
      invariant(
        false,
        'This unit of work tag should not have side-effects. This error is ' +
          'likely caused by a bug in React. Please file an issue.',
      );
    }
  }
}

function commitResetTextContent(current: Fiber) {
  if (!supportsMutation) {
    return;
  }
  resetTextContent(current.stateNode);
}

export {
  commitBeforeMutationLifeCycles,
  commitResetTextContent,
  commitPlacement,
  commitDeletion,
  commitWork,
  commitLifeCycles,
  commitAttachRef,
  commitDetachRef,
};
