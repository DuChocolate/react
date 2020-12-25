/**
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 * @flow
 */

import type {ReactProviderType, ReactContext} from 'shared/ReactTypes';
import type {Fiber} from 'react-reconciler/src/ReactFiber';
import type {FiberRoot} from './ReactFiberRoot';
import type {ExpirationTime} from './ReactFiberExpirationTime';
import type {SuspenseState} from './ReactFiberSuspenseComponent';

import checkPropTypes from 'prop-types/checkPropTypes';

import {
  IndeterminateComponent,
  FunctionComponent,
  ClassComponent,
  HostRoot,
  HostComponent,
  HostText,
  HostPortal,
  ForwardRef,
  Fragment,
  Mode,
  ContextProvider,
  ContextConsumer,
  Profiler,
  SuspenseComponent,
  MemoComponent,
  SimpleMemoComponent,
  LazyComponent,
  IncompleteClassComponent,
} from 'shared/ReactWorkTags';
import {
  NoEffect,
  PerformedWork,
  Placement,
  ContentReset,
  DidCapture,
  Update,
  Ref,
} from 'shared/ReactSideEffectTags';
import ReactSharedInternals from 'shared/ReactSharedInternals';
import {
  debugRenderPhaseSideEffects,
  debugRenderPhaseSideEffectsForStrictMode,
  enableProfilerTimer,
} from 'shared/ReactFeatureFlags';
import invariant from 'shared/invariant';
import shallowEqual from 'shared/shallowEqual';
import getComponentName from 'shared/getComponentName';
import ReactStrictModeWarnings from './ReactStrictModeWarnings';
import warning from 'shared/warning';
import warningWithoutStack from 'shared/warningWithoutStack';
import * as ReactCurrentFiber from './ReactCurrentFiber';
import {startWorkTimer, cancelWorkTimer} from './ReactDebugFiberPerf';

import {
  mountChildFibers,
  reconcileChildFibers,
  cloneChildFibers,
} from './ReactChildFiber';
import {processUpdateQueue} from './ReactUpdateQueue';
import {NoWork, Never} from './ReactFiberExpirationTime';
import {ConcurrentMode, StrictMode} from './ReactTypeOfMode';
import {
  shouldSetTextContent,
  shouldDeprioritizeSubtree,
} from './ReactFiberHostConfig';   //真实文件是ReactFiberHostConfig.dom.js
import {pushHostContext, pushHostContainer} from './ReactFiberHostContext';
import {
  pushProvider,
  propagateContextChange,
  readContext,
  prepareToReadContext,
  calculateChangedBits,
} from './ReactFiberNewContext';
import {stopProfilerTimerIfRunning} from './ReactProfilerTimer';
import {
  getMaskedContext,
  getUnmaskedContext,
  hasContextChanged as hasLegacyContextChanged,
  pushContextProvider as pushLegacyContextProvider,
  isContextProvider as isLegacyContextProvider,
  pushTopLevelContextObject,
  invalidateContextProvider,
} from './ReactFiberContext';
import {
  enterHydrationState,
  resetHydrationState,
  tryToClaimNextHydratableInstance,
} from './ReactFiberHydrationContext';
import {
  adoptClassInstance,
  applyDerivedStateFromProps,
  constructClassInstance,
  mountClassInstance,
  resumeMountClassInstance,
  updateClassInstance,
} from './ReactFiberClassComponent';
import {readLazyComponentType} from './ReactFiberLazyComponent';
import {
  resolveLazyComponentTag,
  createFiberFromTypeAndProps,
  createFiberFromFragment,
  createWorkInProgress,
  isSimpleFunctionComponent,
} from './ReactFiber';

const ReactCurrentOwner = ReactSharedInternals.ReactCurrentOwner;

let didWarnAboutBadClass;
let didWarnAboutContextTypeOnFunctionComponent;
let didWarnAboutGetDerivedStateOnFunctionComponent;
let didWarnAboutFunctionRefs;

if (__DEV__) {
  didWarnAboutBadClass = {};
  didWarnAboutContextTypeOnFunctionComponent = {};
  didWarnAboutGetDerivedStateOnFunctionComponent = {};
  didWarnAboutFunctionRefs = {};
}

/**
 * 1、判断当前节点是否为null，如果是第一次渲染，current=null，则调用mountChildFibers，函数返回值赋给workInProgress.child；
 * 2、current=null，说明是更新节点。调用reconcileChildFibers(workInProgress, current.child, nextChildren)，函数返回值赋值给workInProgress.child。
 */
export function reconcileChildren(
  current: Fiber | null,
  workInProgress: Fiber,
  nextChildren: any,
  renderExpirationTime: ExpirationTime,
) {
  if (current === null) {   // 第一次渲染组件
    // If this is a fresh new component that hasn't been rendered yet, we
    // won't update its child set by applying minimal side-effects. Instead,
    // we will add them all to the child before it gets rendered. That means
    // we can optimize this reconciliation pass by not tracking side-effects.
    workInProgress.child = mountChildFibers(
      workInProgress,
      null,
      nextChildren,
      renderExpirationTime,
    );
  } else {   //更新组件
    // If the current child is the same as the work in progress, it means that
    // we haven't yet started any work on these children. Therefore, we use
    // the clone algorithm to create a copy of all the current children.

    // If we had any progressed work already, that is invalid at this point so
    // let's throw it out.
    workInProgress.child = reconcileChildFibers(
      workInProgress,
      current.child,
      nextChildren,
      renderExpirationTime,
    );
  }
}

function forceUnmountCurrentAndReconcile(
  current: Fiber,
  workInProgress: Fiber,
  nextChildren: any,
  renderExpirationTime: ExpirationTime,
) {
  // This function is fork of reconcileChildren. It's used in cases where we
  // want to reconcile without matching against the existing set. This has the
  // effect of all current children being unmounted; even if the type and key
  // are the same, the old child is unmounted and a new child is created.
  //
  // To do this, we're going to go through the reconcile algorithm twice. In
  // the first pass, we schedule a deletion for all the current children by
  // passing null.
  workInProgress.child = reconcileChildFibers(
    workInProgress,
    current.child,
    null,
    renderExpirationTime,
  );
  // In the second pass, we mount the new children. The trick here is that we
  // pass null in place of where we usually pass the current child set. This has
  // the effect of remounting all children regardless of whether their their
  // identity matches.
  workInProgress.child = reconcileChildFibers(
    workInProgress,
    null,
    nextChildren,
    renderExpirationTime,
  );
}

function updateForwardRef(
  current: Fiber | null,
  workInProgress: Fiber,
  type: any,
  nextProps: any,
  renderExpirationTime: ExpirationTime,
) {
  const render = type.render;
  const ref = workInProgress.ref;
  if (hasLegacyContextChanged()) {
    // Normally we can bail out on props equality but if context has changed
    // we don't do the bailout and we have to reuse existing props instead.
  } else if (workInProgress.memoizedProps === nextProps) {
    const currentRef = current !== null ? current.ref : null;
    if (ref === currentRef) {
      return bailoutOnAlreadyFinishedWork(
        current,
        workInProgress,
        renderExpirationTime,
      );
    }
  }

  let nextChildren;
  if (__DEV__) {
    ReactCurrentOwner.current = workInProgress;
    ReactCurrentFiber.setCurrentPhase('render');
    nextChildren = render(nextProps, ref);
    ReactCurrentFiber.setCurrentPhase(null);
  } else {
    nextChildren = render(nextProps, ref);
  }

  reconcileChildren(
    current,
    workInProgress,
    nextChildren,
    renderExpirationTime,
  );
  return workInProgress.child;
}

function updateMemoComponent(
  current: Fiber | null,
  workInProgress: Fiber,
  Component: any,
  nextProps: any,
  updateExpirationTime,
  renderExpirationTime: ExpirationTime,
): null | Fiber {
  if (current === null) {
    let type = Component.type;
    if (isSimpleFunctionComponent(type) && Component.compare === null) {
      // If this is a plain function component without default props,
      // and with only the default shallow comparison, we upgrade it
      // to a SimpleMemoComponent to allow fast path updates.
      workInProgress.tag = SimpleMemoComponent;
      workInProgress.type = type;
      return updateSimpleMemoComponent(
        current,
        workInProgress,
        type,
        nextProps,
        updateExpirationTime,
        renderExpirationTime,
      );
    }
    let child = createFiberFromTypeAndProps(
      Component.type,
      null,
      nextProps,
      null,
      workInProgress.mode,
      renderExpirationTime,
    );
    child.ref = workInProgress.ref;
    child.return = workInProgress;
    workInProgress.child = child;
    return child;
  }
  let currentChild = ((current.child: any): Fiber); // This is always exactly one child
  if (
    updateExpirationTime === NoWork ||
    updateExpirationTime > renderExpirationTime
  ) {
    // This will be the props with resolved defaultProps,
    // unlike current.memoizedProps which will be the unresolved ones.
    const prevProps = currentChild.memoizedProps;
    // Default to shallow comparison
    let compare = Component.compare;
    compare = compare !== null ? compare : shallowEqual;
    if (compare(prevProps, nextProps) && current.ref === workInProgress.ref) {
      return bailoutOnAlreadyFinishedWork(
        current,
        workInProgress,
        renderExpirationTime,
      );
    }
  }
  let newChild = createWorkInProgress(
    currentChild,
    nextProps,
    renderExpirationTime,
  );
  newChild.ref = workInProgress.ref;
  newChild.return = workInProgress;
  workInProgress.child = newChild;
  return newChild;
}

function updateSimpleMemoComponent(
  current: Fiber | null,
  workInProgress: Fiber,
  Component: any,
  nextProps: any,
  updateExpirationTime,
  renderExpirationTime: ExpirationTime,
): null | Fiber {
  if (
    current !== null &&
    (updateExpirationTime === NoWork ||
      updateExpirationTime > renderExpirationTime)
  ) {
    const prevProps = current.memoizedProps;
    if (
      shallowEqual(prevProps, nextProps) &&
      current.ref === workInProgress.ref
    ) {
      return bailoutOnAlreadyFinishedWork(
        current,
        workInProgress,
        renderExpirationTime,
      );
    }
  }
  return updateFunctionComponent(
    current,
    workInProgress,
    Component,
    nextProps,
    renderExpirationTime,
  );
}

function updateFragment(
  current: Fiber | null,
  workInProgress: Fiber,
  renderExpirationTime: ExpirationTime,
) {
  const nextChildren = workInProgress.pendingProps;
  reconcileChildren(
    current,
    workInProgress,
    nextChildren,
    renderExpirationTime,
  );
  return workInProgress.child;
}

function updateMode(
  current: Fiber | null,
  workInProgress: Fiber,
  renderExpirationTime: ExpirationTime,
) {
  const nextChildren = workInProgress.pendingProps.children;
  reconcileChildren(
    current,
    workInProgress,
    nextChildren,
    renderExpirationTime,
  );
  return workInProgress.child;
}

function updateProfiler(
  current: Fiber | null,
  workInProgress: Fiber,
  renderExpirationTime: ExpirationTime,
) {
  if (enableProfilerTimer) {
    workInProgress.effectTag |= Update;
  }
  const nextProps = workInProgress.pendingProps;
  const nextChildren = nextProps.children;
  reconcileChildren(
    current,
    workInProgress,
    nextChildren,
    renderExpirationTime,
  );
  return workInProgress.child;
}

function markRef(current: Fiber | null, workInProgress: Fiber) {
  const ref = workInProgress.ref;
  if (
    (current === null && ref !== null) ||
    (current !== null && current.ref !== ref)
  ) {
    // Schedule a Ref effect
    workInProgress.effectTag |= Ref;
  }
}

/**
 * 1、调用函数，即业务中写好的函数组件。得到一个ReactElement，即nextChildren；
 * 2、调用 reconcileChildren ，第一个参数 current=当前fiber节点。第二个参数 workInProgress=需要更新的fiber节点。第三个参数nextChildren，上面函数的返回值。
 * 3、上面调用的reconcileChildren方法，其实是改变了workInProgress.child。
 * 4、返回workInProgress.child。 
 */
function updateFunctionComponent(
  current,
  workInProgress,
  Component,
  nextProps: any,
  renderExpirationTime,
) {
  const unmaskedContext = getUnmaskedContext(workInProgress, Component, true);
  const context = getMaskedContext(workInProgress, unmaskedContext);

  let nextChildren;
  prepareToReadContext(workInProgress, renderExpirationTime);
  if (__DEV__) {
    ReactCurrentOwner.current = workInProgress;
    ReactCurrentFiber.setCurrentPhase('render');
    nextChildren = Component(nextProps, context);   
    ReactCurrentFiber.setCurrentPhase(null);
  } else {
    // Component 组件方法，这里就是我们声明组件的方式 function(props, context){}
    nextChildren = Component(nextProps, context);
  }

  // React DevTools reads this flag.
  workInProgress.effectTag |= PerformedWork;
  // 把 nextChildren 这些 ReactElement 变成 Fiber 对象，在workInProgress.child 挂载fiber。
  reconcileChildren(
    current,
    workInProgress,
    nextChildren,
    renderExpirationTime,
  );
  return workInProgress.child;
}

/**
 * 这个函数的作用是对未初始化的类组件进行初始化，对已经初始化的组件更新重用。
 * 
 * 1、如果还没创建实例，初始化，说明是第一次渲染（instance === null），
 *    调用constructClassInstance，执行构造函数，生成实例 instance，
 *    然后再调用 mountClassInstance 挂载实例，主要工作是更新 instance.state，并且执行一些生命周期。
 * 2、渲染被中断（instance !== null， current === null）调用resumeMountClassInstance复用实例但还是调用首次渲染的生命周期，这个函数如果反复 false 则组件无需更新。
 * 3、更新渲染（instance !== null， current !== null）调用updateClassInstance，调用 didUpdate 和 componentWillReceiveProp 生命周期，这个函数如果反复false在则组件无需更新。
 * 4、最终执行 finishClassComponent，进行错误判断的处理和判断是否可以跳过更新的过程，重新调和子节点 reconcileChildren。
 * 
 */
function updateClassComponent(
  current: Fiber | null,
  workInProgress: Fiber,
  Component: any,
  nextProps,
  renderExpirationTime: ExpirationTime,
) {
  // Push context providers early to prevent context stack mismatches.
  // During mounting we don't know the child context yet as the instance doesn't exist.
  // We will invalidate the child context in finishClassComponent() right after rendering.
  let hasContext;
  if (isLegacyContextProvider(Component)) {
    hasContext = true;
    pushLegacyContextProvider(workInProgress);
  } else {
    hasContext = false;
  }
  prepareToReadContext(workInProgress, renderExpirationTime);

  const instance = workInProgress.stateNode;
  let shouldUpdate;
  if (instance === null) {
    if (current !== null) {
      // An class component without an instance only mounts if it suspended
      // inside a non- concurrent tree, in an inconsistent state. We want to
      // tree it like a new mount, even though an empty version of it already
      // committed. Disconnect the alternate pointers.
      current.alternate = null;
      workInProgress.alternate = null;
      // Since this is conceptually a new fiber, schedule a Placement effect
      workInProgress.effectTag |= Placement;
    }
    // In the initial pass we might need to construct the instance.
    // 如果还没创建实例，初始化
    // 执行构造函数，得到实例 instance
    // workInProgress.stateNode = instance
    constructClassInstance(
      workInProgress,
      Component,
      nextProps,
      renderExpirationTime,
    );
    // 挂载
    // 主要工作是更新 instance.state， 并且执行一些生命周期
    mountClassInstance(
      workInProgress,
      Component,
      nextProps,
      renderExpirationTime,
    );
    shouldUpdate = true;
  } else if (current === null) {  // 渲染中断
    // In a resume, we'll already have an instance we can reuse.
    shouldUpdate = resumeMountClassInstance(
      workInProgress,
      Component,
      nextProps,
      renderExpirationTime,
    );
  } else {
    shouldUpdate = updateClassInstance(
      current,
      workInProgress,
      Component,
      nextProps,
      renderExpirationTime,
    );
  }
  // 完成 class 组件更新
  return finishClassComponent(
    current,
    workInProgress,
    Component,
    shouldUpdate,
    hasContext,
    renderExpirationTime,
  );
}

/**
 * 1、没更新也没错误捕获直接跳过，不会进行重新渲染；
 * 2、有错误捕获，class 组件没有 getDerivedStateFromError, nextChildren = null;
 * 3、有错误捕获，class 组件有 getDerivedStateFromError，直接执行 instance.render() 获得最新的 nextChildren，getDerivedStateFromError 在函数外 catch 到错误
 *    并且执行立即更新为正确的state，所以可以执行 instance.render() 。
 * 4、没错误捕获，执行nextChildren = instance.render();
 * 5、有错误强行计算child进行调和，调用 forceUnmountCurrentAndReconcile；
 * 6、正常情况直接调和子节点，调用 reconcileChildren。
 */
function finishClassComponent(
  current: Fiber | null,
  workInProgress: Fiber,
  Component: any,
  shouldUpdate: boolean,
  hasContext: boolean,
  renderExpirationTime: ExpirationTime,
) {
  // Refs should update even if shouldComponentUpdate returns false
  markRef(current, workInProgress);

  const didCaptureError = (workInProgress.effectTag & DidCapture) !== NoEffect;

  // 没更新也没错误捕获直接跳过
  if (!shouldUpdate && !didCaptureError) {
    // Context providers should defer to sCU for rendering
    if (hasContext) {
      invalidateContextProvider(workInProgress, Component, false);
    }

    return bailoutOnAlreadyFinishedWork(
      current,
      workInProgress,
      renderExpirationTime,
    );
  }

  const instance = workInProgress.stateNode;

  // Rerender
  ReactCurrentOwner.current = workInProgress;
  let nextChildren;
  // 有错误捕获
  if (
    didCaptureError &&
    typeof Component.getDerivedStateFromError !== 'function'
  ) {
    // If we captured an error, but getDerivedStateFrom catch is not defined,
    // unmount all the children. componentDidCatch will schedule an update to
    // re-render a fallback. This is temporary until we migrate everyone to
    // the new API.
    // TODO: Warn in a future release.
    // class 组件没有 getDerivedStateFromError, nextChildren = null
    nextChildren = null;

    if (enableProfilerTimer) {
      stopProfilerTimerIfRunning(workInProgress);
    }
  } else {
    if (__DEV__) {
      ReactCurrentFiber.setCurrentPhase('render');
      nextChildren = instance.render();
      if (
        debugRenderPhaseSideEffects ||
        (debugRenderPhaseSideEffectsForStrictMode &&
          workInProgress.mode & StrictMode)
      ) {
        instance.render();
      }
      ReactCurrentFiber.setCurrentPhase(null);
    } else {
      // class 组件有 getDerivedStateFromError，直接执行 instance.render() 获得最新的 nextChildren，
      // getDerivedStateFromError 在函数外 catch 到错误并且执行立即更新为正确的 state ，所以可以执行 instance.render().
      // 没捕获错误执行instance.render();
      nextChildren = instance.render();
    }
  }

  // React DevTools reads this flag.
  workInProgress.effectTag |= PerformedWork;
  if (current !== null && didCaptureError) { // 不是第一次渲染 并且 有错误捕获
    // If we're recovering from an error, reconcile without reusing any of
    // the existing children. Conceptually, the normal children and the children
    // that are shown on error are two different sets, so we shouldn't reuse
    // normal children even if their identities match.
    // 有错误强制计算 child 进行调和，调用 forceUnmountCurrentAndReconcile
    forceUnmountCurrentAndReconcile( 
      current,
      workInProgress,
      nextChildren,
      renderExpirationTime,
    );
  } else {
    // 正常情况直接调和子节点，调用 reconcileChildren
    reconcileChildren(
      current,
      workInProgress,
      nextChildren,
      renderExpirationTime,
    );
  }

  // Memoize state using the values we just used to render.
  // TODO: Restructure so we never read values from the instance.
  workInProgress.memoizedState = instance.state;

  // The context might have changed so we need to recalculate it.
  if (hasContext) {
    invalidateContextProvider(workInProgress, Component, true);
  }

  return workInProgress.child;
}

function pushHostRootContext(workInProgress) {
  const root = (workInProgress.stateNode: FiberRoot);
  if (root.pendingContext) {
    pushTopLevelContextObject(
      workInProgress,
      root.pendingContext,
      root.pendingContext !== root.context,
    );
  } else if (root.context) {
    // Should always be set
    pushTopLevelContextObject(workInProgress, root.context, false);
  }
  pushHostContainer(workInProgress, root.containerInfo);
}

/**
 * 这种情况只会出现在ReactDOM.render渲染的时候
 * 1、调用 processUpdateQueue 得到新的 state;
 * 2、nextChildren = nextState.element;
 * 3、第一次渲染 mountChildFibers;
 * 4、后续渲染 reconcileChildren。
 */
function updateHostRoot(current, workInProgress, renderExpirationTime) {
  pushHostRootContext(workInProgress);
  const updateQueue = workInProgress.updateQueue;
  invariant(
    updateQueue !== null,
    'If the root does not have an updateQueue, we should have already ' +
      'bailed out. This error is likely caused by a bug in React. Please ' +
      'file an issue.',
  );
  const nextProps = workInProgress.pendingProps;
  const prevState = workInProgress.memoizedState;
  const prevChildren = prevState !== null ? prevState.element : null;
  processUpdateQueue(
    workInProgress,
    updateQueue,
    nextProps,
    null,
    renderExpirationTime,
  );
  const nextState = workInProgress.memoizedState;
  // Caution: React DevTools currently depends on this property
  // being called "element".
  const nextChildren = nextState.element;
  if (nextChildren === prevChildren) {
    // If the state is the same as before, that's a bailout because we had
    // no work that expires at this time.
    resetHydrationState();
    return bailoutOnAlreadyFinishedWork(
      current,
      workInProgress,
      renderExpirationTime,
    );
  }
  const root: FiberRoot = workInProgress.stateNode;
  if (
    (current === null || current.child === null) &&
    root.hydrate &&
    enterHydrationState(workInProgress)
  ) {
    // If we don't have any current children this might be the first pass.
    // We always try to hydrate. If this isn't a hydration pass there won't
    // be any children to hydrate which is effectively the same thing as
    // not hydrating.

    // This is a bit of a hack. We track the host root as a placement to
    // know that we're currently in a mounting state. That way isMounted
    // works as expected. We must reset this before committing.
    // TODO: Delete this when we delete isMounted and findDOMNode.
    workInProgress.effectTag |= Placement;

    // Ensure that children mount into this root without tracking
    // side-effects. This ensures that we don't store Placement effects on
    // nodes that will be hydrated.
    workInProgress.child = mountChildFibers(
      workInProgress,
      null,
      nextChildren,
      renderExpirationTime,
    );
  } else {
    // Otherwise reset hydration state in case we aborted and resumed another
    // root.
    reconcileChildren(
      current,
      workInProgress,
      nextChildren,
      renderExpirationTime,
    );
    resetHydrationState();
  }
  return workInProgress.child;
}

/**
 * 1、dom 标签内是纯文本 nextChildren 为 null,直接渲染文本内容；
 * 2、判断 concurrentMode 异步组件是否有 hidden 属性，异步组件 hidden 永不更新；
 * 3、最后进行 reconcileChildren。 
 */
function updateHostComponent(current, workInProgress, renderExpirationTime) {
  pushHostContext(workInProgress);

  if (current === null) {
    tryToClaimNextHydratableInstance(workInProgress);
  }

  const type = workInProgress.type;
  const nextProps = workInProgress.pendingProps;
  const prevProps = current !== null ? current.memoizedProps : null;

  let nextChildren = nextProps.children;
  const isDirectTextChild = shouldSetTextContent(type, nextProps);   // 判断节点的 children 是否是纯字符串

  if (isDirectTextChild) {
    // We special case a direct text child of a host node. This is a common
    // case. We won't handle it as a reified child. We will instead handle
    // this in the host environment that also have access to this prop. That
    // avoids allocating another HostText fiber and traversing it.
    // dom 标签内是纯文本 nextChildren 为 null，直接渲染文本内容
    nextChildren = null;
  } else if (prevProps !== null && shouldSetTextContent(type, prevProps)) {
    // If we're switching from a direct text child to a normal child, or to
    // empty, we need to schedule the text content to be reset.
    workInProgress.effectTag |= ContentReset;
  }

  markRef(current, workInProgress);

  // Check the host config to see if the children are offscreen/hidden.
  if (
    renderExpirationTime !== Never &&
    workInProgress.mode & ConcurrentMode &&
    shouldDeprioritizeSubtree(type, nextProps)
  ) {
    // Schedule this fiber to re-render at offscreen priority. Then bailout.
    // 判断 concurrentMode 异步组件是否有 hidden 属性，异步组件 hidden 永不更新
    workInProgress.expirationTime = Never;
    return null;
  }

  // 最后进行 reconcileChildren
  reconcileChildren(
    current,
    workInProgress,
    nextChildren,
    renderExpirationTime,
  );
  return workInProgress.child;
}

// 文本内容不需要构建 fiber 结构，直接在提交阶段更新就行了，所以直接 return null。
function updateHostText(current, workInProgress) {
  if (current === null) {
    tryToClaimNextHydratableInstance(workInProgress);
  }
  // Nothing to do here. This is terminal. We'll do the completion step
  // immediately after.
  return null;
}

function resolveDefaultProps(Component, baseProps) {
  if (Component && Component.defaultProps) {
    // Resolve default props. Taken from ReactElement
    const props = Object.assign({}, baseProps);
    const defaultProps = Component.defaultProps;
    for (let propName in defaultProps) {
      if (props[propName] === undefined) {
        props[propName] = defaultProps[propName];
      }
    }
    return props;
  }
  return baseProps;
}

function mountLazyComponent(
  _current,
  workInProgress,
  elementType,
  updateExpirationTime,
  renderExpirationTime,
) {
  if (_current !== null) {
    // An lazy component only mounts if it suspended inside a non-
    // concurrent tree, in an inconsistent state. We want to tree it like
    // a new mount, even though an empty version of it already committed.
    // Disconnect the alternate pointers.
    _current.alternate = null;
    workInProgress.alternate = null;
    // Since this is conceptually a new fiber, schedule a Placement effect
    workInProgress.effectTag |= Placement;
  }

  const props = workInProgress.pendingProps;
  // We can't start a User Timing measurement with correct label yet.
  // Cancel and resume right after we know the tag.
  cancelWorkTimer(workInProgress);
  let Component = readLazyComponentType(elementType);
  // Store the unwrapped component in the type.
  workInProgress.type = Component;
  const resolvedTag = (workInProgress.tag = resolveLazyComponentTag(Component));
  startWorkTimer(workInProgress);
  const resolvedProps = resolveDefaultProps(Component, props);
  let child;
  switch (resolvedTag) {
    case FunctionComponent: {
      child = updateFunctionComponent(
        null,
        workInProgress,
        Component,
        resolvedProps,
        renderExpirationTime,
      );
      break;
    }
    case ClassComponent: {
      child = updateClassComponent(
        null,
        workInProgress,
        Component,
        resolvedProps,
        renderExpirationTime,
      );
      break;
    }
    case ForwardRef: {
      child = updateForwardRef(
        null,
        workInProgress,
        Component,
        resolvedProps,
        renderExpirationTime,
      );
      break;
    }
    case MemoComponent: {
      child = updateMemoComponent(
        null,
        workInProgress,
        Component,
        resolveDefaultProps(Component.type, resolvedProps), // The inner type can have defaults too
        updateExpirationTime,
        renderExpirationTime,
      );
      break;
    }
    default: {
      // This message intentionally doesn't metion ForwardRef or MemoComponent
      // because the fact that it's a separate type of work is an
      // implementation detail.
      invariant(
        false,
        'Element type is invalid. Received a promise that resolves to: %s. ' +
          'Promise elements must resolve to a class or function.',
        Component,
      );
    }
  }
  return child;
}

function mountIncompleteClassComponent(
  _current,
  workInProgress,
  Component,
  nextProps,
  renderExpirationTime,
) {
  if (_current !== null) {
    // An incomplete component only mounts if it suspended inside a non-
    // concurrent tree, in an inconsistent state. We want to tree it like
    // a new mount, even though an empty version of it already committed.
    // Disconnect the alternate pointers.
    _current.alternate = null;
    workInProgress.alternate = null;
    // Since this is conceptually a new fiber, schedule a Placement effect
    workInProgress.effectTag |= Placement;
  }

  // Promote the fiber to a class and try rendering again.
  workInProgress.tag = ClassComponent;

  // The rest of this function is a fork of `updateClassComponent`

  // Push context providers early to prevent context stack mismatches.
  // During mounting we don't know the child context yet as the instance doesn't exist.
  // We will invalidate the child context in finishClassComponent() right after rendering.
  let hasContext;
  if (isLegacyContextProvider(Component)) {
    hasContext = true;
    pushLegacyContextProvider(workInProgress);
  } else {
    hasContext = false;
  }
  prepareToReadContext(workInProgress, renderExpirationTime);

  constructClassInstance(
    workInProgress,
    Component,
    nextProps,
    renderExpirationTime,
  );
  mountClassInstance(
    workInProgress,
    Component,
    nextProps,
    renderExpirationTime,
  );

  return finishClassComponent(
    null,
    workInProgress,
    Component,
    true,
    hasContext,
    renderExpirationTime,
  );
}
/**
 * 1、在函数 createFiberFromTypeAndProps 中，fiber 刚创建的时候 fiberTag 都为 IndeterminateComponent 类型，只有当 class 组件有 construct 才为 class 组件类型；
 * 2、所以这个函数做以下判断：
 *    符合 class 组件条件按 class 组件更新；
 *    否则就按函数组件类型更新
 * 
 * 注：只存在于首次更新的时候，只有首次更新的时候不确定 fiberTag 类型。
 * 
 */
function mountIndeterminateComponent(   // functionComponent 只有第一次渲染会调用该方法
  _current,
  workInProgress,
  Component,
  renderExpirationTime,
) {
  if (_current !== null) {  // current !== null 说明是suspended组件
    // An indeterminate component only mounts if it suspended inside a non-
    // concurrent tree, in an inconsistent state. We want to tree it like
    // a new mount, even though an empty version of it already committed.
    // Disconnect the alternate pointers.
    _current.alternate = null;
    workInProgress.alternate = null;
    // Since this is conceptually a new fiber, schedule a Placement effect
    workInProgress.effectTag |= Placement;
  }

  const props = workInProgress.pendingProps;
  const unmaskedContext = getUnmaskedContext(workInProgress, Component, false);
  const context = getMaskedContext(workInProgress, unmaskedContext);

  prepareToReadContext(workInProgress, renderExpirationTime);

  let value;

  if (__DEV__) {
    if (
      Component.prototype &&
      typeof Component.prototype.render === 'function'
    ) {
      const componentName = getComponentName(Component) || 'Unknown';

      if (!didWarnAboutBadClass[componentName]) {
        warningWithoutStack(
          false,
          "The <%s /> component appears to have a render method, but doesn't extend React.Component. " +
            'This is likely to cause errors. Change %s to extend React.Component instead.',
          componentName,
          componentName,
        );
        didWarnAboutBadClass[componentName] = true;
      }
    }

    if (workInProgress.mode & StrictMode) {
      ReactStrictModeWarnings.recordLegacyContextWarning(workInProgress, null);
    }

    ReactCurrentOwner.current = workInProgress;
    value = Component(props, context);
  } else {
    value = Component(props, context);
  }
  // React DevTools reads this flag.
  workInProgress.effectTag |= PerformedWork;

  if (
    typeof value === 'object' &&
    value !== null &&
    typeof value.render === 'function' &&
    value.$$typeof === undefined
  ) {   // 以上条件都满足，说明该组件是个 classComponent
    // Proceed under the assumption that this is a class instance
    workInProgress.tag = ClassComponent;

    // Push context providers early to prevent context stack mismatches.
    // During mounting we don't know the child context yet as the instance doesn't exist.
    // We will invalidate the child context in finishClassComponent() right after rendering.
    let hasContext = false;
    if (isLegacyContextProvider(Component)) {
      hasContext = true;
      pushLegacyContextProvider(workInProgress);
    } else {
      hasContext = false;
    }

    workInProgress.memoizedState =
      value.state !== null && value.state !== undefined ? value.state : null;

    const getDerivedStateFromProps = Component.getDerivedStateFromProps;
    if (typeof getDerivedStateFromProps === 'function') {
      applyDerivedStateFromProps(
        workInProgress,
        Component,
        getDerivedStateFromProps,
        props,
      );
    }

    adoptClassInstance(workInProgress, value);
    mountClassInstance(workInProgress, Component, props, renderExpirationTime);
    return finishClassComponent(
      null,
      workInProgress,
      Component,
      true,
      hasContext,
      renderExpirationTime,
    );
  } else {
    // Proceed under the assumption that this is a function component
    workInProgress.tag = FunctionComponent;
    if (__DEV__) {
      if (Component) {
        warningWithoutStack(
          !Component.childContextTypes,
          '%s(...): childContextTypes cannot be defined on a function component.',
          Component.displayName || Component.name || 'Component',
        );
      }
      if (workInProgress.ref !== null) {
        let info = '';
        const ownerName = ReactCurrentFiber.getCurrentFiberOwnerNameInDevOrNull();
        if (ownerName) {
          info += '\n\nCheck the render method of `' + ownerName + '`.';
        }

        let warningKey = ownerName || workInProgress._debugID || '';
        const debugSource = workInProgress._debugSource;
        if (debugSource) {
          warningKey = debugSource.fileName + ':' + debugSource.lineNumber;
        }
        if (!didWarnAboutFunctionRefs[warningKey]) {
          didWarnAboutFunctionRefs[warningKey] = true;
          warning(
            false,
            'Function components cannot be given refs. ' +
              'Attempts to access this ref will fail.%s',
            info,
          );
        }
      }

      if (typeof Component.getDerivedStateFromProps === 'function') {
        const componentName = getComponentName(Component) || 'Unknown';

        if (!didWarnAboutGetDerivedStateOnFunctionComponent[componentName]) {
          warningWithoutStack(
            false,
            '%s: Function components do not support getDerivedStateFromProps.',
            componentName,
          );
          didWarnAboutGetDerivedStateOnFunctionComponent[componentName] = true;
        }
      }

      if (
        typeof Component.contextType === 'object' &&
        Component.contextType !== null
      ) {
        const componentName = getComponentName(Component) || 'Unknown';

        if (!didWarnAboutContextTypeOnFunctionComponent[componentName]) {
          warningWithoutStack(
            false,
            '%s: Function components do not support contextType.',
            componentName,
          );
          didWarnAboutContextTypeOnFunctionComponent[componentName] = true;
        }
      }
    }
    reconcileChildren(null, workInProgress, value, renderExpirationTime);
    return workInProgress.child;
  }
}

function updateSuspenseComponent(
  current,
  workInProgress,
  renderExpirationTime,
) {
  const mode = workInProgress.mode;
  const nextProps = workInProgress.pendingProps;

  // We should attempt to render the primary children unless this boundary
  // already suspended during this render (`alreadyCaptured` is true).
  let nextState: SuspenseState | null = workInProgress.memoizedState;
  if (nextState === null) {
    // An empty suspense state means this boundary has not yet timed out.
  } else {
    if (!nextState.alreadyCaptured) {
      // Since we haven't already suspended during this commit, clear the
      // existing suspense state. We'll try rendering again.
      nextState = null;
    } else {
      // Something in this boundary's subtree already suspended. Switch to
      // rendering the fallback children. Set `alreadyCaptured` to true.
      if (current !== null && nextState === current.memoizedState) {
        // Create a new suspense state to avoid mutating the current tree's.
        nextState = {
          alreadyCaptured: true,
          didTimeout: true,
          timedOutAt: nextState.timedOutAt,
        };
      } else {
        // Already have a clone, so it's safe to mutate.
        nextState.alreadyCaptured = true;
        nextState.didTimeout = true;
      }
    }
  }
  const nextDidTimeout = nextState !== null && nextState.didTimeout;

  // This next part is a bit confusing. If the children timeout, we switch to
  // showing the fallback children in place of the "primary" children.
  // However, we don't want to delete the primary children because then their
  // state will be lost (both the React state and the host state, e.g.
  // uncontrolled form inputs). Instead we keep them mounted and hide them.
  // Both the fallback children AND the primary children are rendered at the
  // same time. Once the primary children are un-suspended, we can delete
  // the fallback children — don't need to preserve their state.
  //
  // The two sets of children are siblings in the host environment, but
  // semantically, for purposes of reconciliation, they are two separate sets.
  // So we store them using two fragment fibers.
  //
  // However, we want to avoid allocating extra fibers for every placeholder.
  // They're only necessary when the children time out, because that's the
  // only time when both sets are mounted.
  //
  // So, the extra fragment fibers are only used if the children time out.
  // Otherwise, we render the primary children directly. This requires some
  // custom reconciliation logic to preserve the state of the primary
  // children. It's essentially a very basic form of re-parenting.

  // `child` points to the child fiber. In the normal case, this is the first
  // fiber of the primary children set. In the timed-out case, it's a
  // a fragment fiber containing the primary children.
  let child;
  // `next` points to the next fiber React should render. In the normal case,
  // it's the same as `child`: the first fiber of the primary children set.
  // In the timed-out case, it's a fragment fiber containing the *fallback*
  // children -- we skip over the primary children entirely.
  let next;
  if (current === null) {
    // This is the initial mount. This branch is pretty simple because there's
    // no previous state that needs to be preserved.
    if (nextDidTimeout) {
      // Mount separate fragments for primary and fallback children.
      const nextFallbackChildren = nextProps.fallback;
      const primaryChildFragment = createFiberFromFragment(
        null,
        mode,
        NoWork,
        null,
      );
      const fallbackChildFragment = createFiberFromFragment(
        nextFallbackChildren,
        mode,
        renderExpirationTime,
        null,
      );
      primaryChildFragment.sibling = fallbackChildFragment;
      child = primaryChildFragment;
      // Skip the primary children, and continue working on the
      // fallback children.
      next = fallbackChildFragment;
      child.return = next.return = workInProgress;
    } else {
      // Mount the primary children without an intermediate fragment fiber.
      const nextPrimaryChildren = nextProps.children;
      child = next = mountChildFibers(
        workInProgress,
        null,
        nextPrimaryChildren,
        renderExpirationTime,
      );
    }
  } else {
    // This is an update. This branch is more complicated because we need to
    // ensure the state of the primary children is preserved.
    const prevState = current.memoizedState;
    const prevDidTimeout = prevState !== null && prevState.didTimeout;
    if (prevDidTimeout) {
      // The current tree already timed out. That means each child set is
      // wrapped in a fragment fiber.
      const currentPrimaryChildFragment: Fiber = (current.child: any);
      const currentFallbackChildFragment: Fiber = (currentPrimaryChildFragment.sibling: any);
      if (nextDidTimeout) {
        // Still timed out. Reuse the current primary children by cloning
        // its fragment. We're going to skip over these entirely.
        const nextFallbackChildren = nextProps.fallback;
        const primaryChildFragment = createWorkInProgress(
          currentPrimaryChildFragment,
          currentPrimaryChildFragment.pendingProps,
          NoWork,
        );
        primaryChildFragment.effectTag |= Placement;
        // Clone the fallback child fragment, too. These we'll continue
        // working on.
        const fallbackChildFragment = (primaryChildFragment.sibling = createWorkInProgress(
          currentFallbackChildFragment,
          nextFallbackChildren,
          currentFallbackChildFragment.expirationTime,
        ));
        fallbackChildFragment.effectTag |= Placement;
        child = primaryChildFragment;
        primaryChildFragment.childExpirationTime = NoWork;
        // Skip the primary children, and continue working on the
        // fallback children.
        next = fallbackChildFragment;
        child.return = next.return = workInProgress;
      } else {
        // No longer suspended. Switch back to showing the primary children,
        // and remove the intermediate fragment fiber.
        const nextPrimaryChildren = nextProps.children;
        const currentPrimaryChild = currentPrimaryChildFragment.child;
        const currentFallbackChild = currentFallbackChildFragment.child;
        const primaryChild = reconcileChildFibers(
          workInProgress,
          currentPrimaryChild,
          nextPrimaryChildren,
          renderExpirationTime,
        );
        // Delete the fallback children.
        reconcileChildFibers(
          workInProgress,
          currentFallbackChild,
          null,
          renderExpirationTime,
        );
        // Continue rendering the children, like we normally do.
        child = next = primaryChild;
      }
    } else {
      // The current tree has not already timed out. That means the primary
      // children are not wrapped in a fragment fiber.
      const currentPrimaryChild: Fiber = (current.child: any);
      if (nextDidTimeout) {
        // Timed out. Wrap the children in a fragment fiber to keep them
        // separate from the fallback children.
        const nextFallbackChildren = nextProps.fallback;
        const primaryChildFragment = createFiberFromFragment(
          // It shouldn't matter what the pending props are because we aren't
          // going to render this fragment.
          null,
          mode,
          NoWork,
          null,
        );
        primaryChildFragment.effectTag |= Placement;
        primaryChildFragment.child = currentPrimaryChild;
        currentPrimaryChild.return = primaryChildFragment;
        // Create a fragment from the fallback children, too.
        const fallbackChildFragment = (primaryChildFragment.sibling = createFiberFromFragment(
          nextFallbackChildren,
          mode,
          renderExpirationTime,
          null,
        ));
        fallbackChildFragment.effectTag |= Placement;
        child = primaryChildFragment;
        primaryChildFragment.childExpirationTime = NoWork;
        // Skip the primary children, and continue working on the
        // fallback children.
        next = fallbackChildFragment;
        child.return = next.return = workInProgress;
      } else {
        // Still haven't timed out.  Continue rendering the children, like we
        // normally do.
        const nextPrimaryChildren = nextProps.children;
        next = child = reconcileChildFibers(
          workInProgress,
          currentPrimaryChild,
          nextPrimaryChildren,
          renderExpirationTime,
        );
      }
    }
  }

  workInProgress.memoizedState = nextState;
  workInProgress.child = child;
  return next;
}

function updatePortalComponent(
  current: Fiber | null,
  workInProgress: Fiber,
  renderExpirationTime: ExpirationTime,
) {
  pushHostContainer(workInProgress, workInProgress.stateNode.containerInfo);
  const nextChildren = workInProgress.pendingProps;
  if (current === null) {
    // Portals are special because we don't append the children during mount
    // but at commit. Therefore we need to track insertions which the normal
    // flow doesn't do during mount. This doesn't happen at the root because
    // the root always starts with a "current" with a null child.
    // TODO: Consider unifying this with how the root works.
    workInProgress.child = reconcileChildFibers(
      workInProgress,
      null,
      nextChildren,
      renderExpirationTime,
    );
  } else {
    reconcileChildren(
      current,
      workInProgress,
      nextChildren,
      renderExpirationTime,
    );
  }
  return workInProgress.child;
}

function updateContextProvider(
  current: Fiber | null,
  workInProgress: Fiber,
  renderExpirationTime: ExpirationTime,
) {
  const providerType: ReactProviderType<any> = workInProgress.type;
  const context: ReactContext<any> = providerType._context;

  const newProps = workInProgress.pendingProps;
  const oldProps = workInProgress.memoizedProps;

  const newValue = newProps.value;

  if (__DEV__) {
    const providerPropTypes = workInProgress.type.propTypes;

    if (providerPropTypes) {
      checkPropTypes(
        providerPropTypes,
        newProps,
        'prop',
        'Context.Provider',
        ReactCurrentFiber.getCurrentFiberStackInDev,
      );
    }
  }

  pushProvider(workInProgress, newValue);

  if (oldProps !== null) {
    const oldValue = oldProps.value;
    const changedBits = calculateChangedBits(context, newValue, oldValue);
    if (changedBits === 0) {
      // No change. Bailout early if children are the same.
      if (
        oldProps.children === newProps.children &&
        !hasLegacyContextChanged()
      ) {
        return bailoutOnAlreadyFinishedWork(
          current,
          workInProgress,
          renderExpirationTime,
        );
      }
    } else {
      // The context value changed. Search for matching consumers and schedule
      // them to update.
      propagateContextChange(
        workInProgress,
        context,
        changedBits,
        renderExpirationTime,
      );
    }
  }

  const newChildren = newProps.children;
  reconcileChildren(current, workInProgress, newChildren, renderExpirationTime);
  return workInProgress.child;
}

let hasWarnedAboutUsingContextAsConsumer = false;

function updateContextConsumer(
  current: Fiber | null,
  workInProgress: Fiber,
  renderExpirationTime: ExpirationTime,
) {
  let context: ReactContext<any> = workInProgress.type;
  // The logic below for Context differs depending on PROD or DEV mode. In
  // DEV mode, we create a separate object for Context.Consumer that acts
  // like a proxy to Context. This proxy object adds unnecessary code in PROD
  // so we use the old behaviour (Context.Consumer references Context) to
  // reduce size and overhead. The separate object references context via
  // a property called "_context", which also gives us the ability to check
  // in DEV mode if this property exists or not and warn if it does not.
  if (__DEV__) {
    if ((context: any)._context === undefined) {
      // This may be because it's a Context (rather than a Consumer).
      // Or it may be because it's older React where they're the same thing.
      // We only want to warn if we're sure it's a new React.
      if (context !== context.Consumer) {
        if (!hasWarnedAboutUsingContextAsConsumer) {
          hasWarnedAboutUsingContextAsConsumer = true;
          warning(
            false,
            'Rendering <Context> directly is not supported and will be removed in ' +
              'a future major release. Did you mean to render <Context.Consumer> instead?',
          );
        }
      }
    } else {
      context = (context: any)._context;
    }
  }
  const newProps = workInProgress.pendingProps;
  const render = newProps.children;

  if (__DEV__) {
    warningWithoutStack(
      typeof render === 'function',
      'A context consumer was rendered with multiple children, or a child ' +
        "that isn't a function. A context consumer expects a single child " +
        'that is a function. If you did pass a function, make sure there ' +
        'is no trailing or leading whitespace around it.',
    );
  }

  prepareToReadContext(workInProgress, renderExpirationTime);
  const newValue = readContext(context, newProps.unstable_observedBits);
  let newChildren;
  if (__DEV__) {
    ReactCurrentOwner.current = workInProgress;
    ReactCurrentFiber.setCurrentPhase('render');
    newChildren = render(newValue);
    ReactCurrentFiber.setCurrentPhase(null);
  } else {
    newChildren = render(newValue);
  }

  // React DevTools reads this flag.
  workInProgress.effectTag |= PerformedWork;
  reconcileChildren(current, workInProgress, newChildren, renderExpirationTime);
  return workInProgress.child;
}

/*
  function reuseChildrenEffects(returnFiber : Fiber, firstChild : Fiber) {
    let child = firstChild;
    do {
      // Ensure that the first and last effect of the parent corresponds
      // to the children's first and last effect.
      if (!returnFiber.firstEffect) {
        returnFiber.firstEffect = child.firstEffect;
      }
      if (child.lastEffect) {
        if (returnFiber.lastEffect) {
          returnFiber.lastEffect.nextEffect = child.firstEffect;
        }
        returnFiber.lastEffect = child.lastEffect;
      }
    } while (child = child.sibling);
  }
  */

function bailoutOnAlreadyFinishedWork(
  current: Fiber | null,
  workInProgress: Fiber,
  renderExpirationTime: ExpirationTime,
): Fiber | null {
  cancelWorkTimer(workInProgress);

  if (current !== null) {
    // Reuse previous context list
    workInProgress.firstContextDependency = current.firstContextDependency;
  }

  if (enableProfilerTimer) {
    // Don't update "base" render times for bailouts.
    stopProfilerTimerIfRunning(workInProgress);
  }

  // Check if the children have any pending work.
  const childExpirationTime = workInProgress.childExpirationTime;
  if (
    childExpirationTime === NoWork ||   // 子树没有更新
    childExpirationTime > renderExpirationTime   // 子树更新优先级较低
  ) {   // 直接跳过
    // The children don't have any work either. We can skip them.
    // TODO: Once we add back resuming, we should check if the children are
    // a work-in-progress set. If so, we need to transfer their effects.
    return null;
  } else {  // 该fiber没有更新，但其子树有更新要执行，直接clone其子树
    // This fiber doesn't have work, but its subtree does. Clone the child
    // fibers and continue.
    cloneChildFibers(current, workInProgress);
    return workInProgress.child;
  }
}

function beginWork(
  current: Fiber | null,    // current 是 workInProgress.alternate, 是fiber的替身，  current 一开始是RootFiber节点（也是个Fiber对象），它对应的tag是HostRoot
  workInProgress: Fiber,  // workInProgress 是真实的 Fiber对象
  renderExpirationTime: ExpirationTime,    // renderExpirationTime 是 FiberRoot.nextExpirationTimeToWorkOn;
): Fiber | null {
  //fiber对象上的expirationTime表示自身更新的过期时间，而RootFiber上的expirationTime只有在调用ReactDOM.render的时候才会有值
  const updateExpirationTime = workInProgress.expirationTime;

  // 只有调用ReactDOM.render的时候current是有值的，也就是说判断current是否为null相当于判断节点是不是第一次渲染，current !== null即第一次渲染
  if (current !== null) {
    const oldProps = current.memoizedProps;
    const newProps = workInProgress.pendingProps;
    if (    // 判断 props 和 context 是否改变，判断当前 fiber 的优先级是否小于本次渲染的优先级，小于的话可以跳过
      oldProps === newProps &&    //前后props一致
      !hasLegacyContextChanged() &&
      (updateExpirationTime === NoWork ||   // 此节点没有更新
        updateExpirationTime > renderExpirationTime)    //此节点有更新但是优先级较低
    ) {   // 跳过，以下都是优化的过程
      // This fiber does not have any pending work. Bailout without entering
      // the begin phase. There's still some bookkeeping we that needs to be done
      // in this optimized path, mostly pushing stuff onto the stack.
      // 通过 workInProgress.tag 判断当前是什么类型的节点
      // workInProgress.tag 的所有类型定义在 ReactWorkTags.js 里面
      switch (workInProgress.tag) {
        case HostRoot:
          pushHostRootContext(workInProgress);
          resetHydrationState();
          break;
        case HostComponent:
          pushHostContext(workInProgress);
          break;
        case ClassComponent: {
          const Component = workInProgress.type;
          if (isLegacyContextProvider(Component)) {
            pushLegacyContextProvider(workInProgress);
          }
          break;
        }
        case HostPortal:
          pushHostContainer(
            workInProgress,
            workInProgress.stateNode.containerInfo,
          );
          break;
        case ContextProvider: {
          const newValue = workInProgress.memoizedProps.value;
          pushProvider(workInProgress, newValue);
          break;
        }
        case Profiler:
          if (enableProfilerTimer) {
            workInProgress.effectTag |= Update;
          }
          break;
        case SuspenseComponent: {
          const state: SuspenseState | null = workInProgress.memoizedState;
          const didTimeout = state !== null && state.didTimeout;
          if (didTimeout) {
            // If this boundary is currently timed out, we need to decide
            // whether to retry the primary children, or to skip over it and
            // go straight to the fallback. Check the priority of the primary
            // child fragment.
            const primaryChildFragment: Fiber = (workInProgress.child: any);
            const primaryChildExpirationTime =
              primaryChildFragment.childExpirationTime;
            if (
              primaryChildExpirationTime !== NoWork &&
              primaryChildExpirationTime <= renderExpirationTime
            ) {
              // The primary children have pending work. Use the normal path
              // to attempt to render the primary children again.
              return updateSuspenseComponent(
                current,
                workInProgress,
                renderExpirationTime,
              );
            } else {
              // The primary children do not have pending work with sufficient
              // priority. Bailout.
              const child = bailoutOnAlreadyFinishedWork(
                current,
                workInProgress,
                renderExpirationTime,
              );
              if (child !== null) {
                // The fallback children have pending work. Skip over the
                // primary children and work on the fallback.
                return child.sibling;
              } else {
                return null;
              }
            }
          }
          break;
        }
      }
      // 该方法会帮助跳过该节点及子节点的更新
      // bailoutOnAlreadyFinishedWork 会判断这个 fiber 的子树是否需要更新，如果需要更新会 clone 一份到 workInProgress.child 返回到 workLoop 的 nextUnitOfWork，否则为null
      return bailoutOnAlreadyFinishedWork(
        current,
        workInProgress,
        renderExpirationTime,
      );
    }
  }

  // Before entering the begin phase, clear the expiration time.
  // 进行更新先把当前 fiber 的 expirationTime 设置为 NoWork
  workInProgress.expirationTime = NoWork;

  // 根据 fiber 的 tag 类型进行更新
  switch (workInProgress.tag) {
    case IndeterminateComponent: {   // 不确定是函数组件还是类组件
      const elementType = workInProgress.elementType;
      return mountIndeterminateComponent(
        current,
        workInProgress,
        elementType,
        renderExpirationTime,
      );
    }
    case LazyComponent: {
      const elementType = workInProgress.elementType;
      return mountLazyComponent(
        current,
        workInProgress,
        elementType,
        updateExpirationTime,
        renderExpirationTime,
      );
    }
    case FunctionComponent: {   // 函数组件
      const Component = workInProgress.type;
      const unresolvedProps = workInProgress.pendingProps;
      const resolvedProps =
        workInProgress.elementType === Component
          ? unresolvedProps
          : resolveDefaultProps(Component, unresolvedProps);
      return updateFunctionComponent(
        current,
        workInProgress,
        Component,
        resolvedProps,
        renderExpirationTime,
      );
    }
    case ClassComponent: {   // 类组件
      const Component = workInProgress.type;
      const unresolvedProps = workInProgress.pendingProps;
      const resolvedProps =
        workInProgress.elementType === Component
          ? unresolvedProps
          : resolveDefaultProps(Component, unresolvedProps);
      return updateClassComponent(
        current,
        workInProgress,
        Component,
        resolvedProps,
        renderExpirationTime,
      );
    }
    case HostRoot:    // 组件树根组件
      return updateHostRoot(current, workInProgress, renderExpirationTime);
    case HostComponent:    // 标准dom节点
      return updateHostComponent(current, workInProgress, renderExpirationTime);
    case HostText:   // 文本
      return updateHostText(current, workInProgress);
    case SuspenseComponent:
      return updateSuspenseComponent(
        current,
        workInProgress,
        renderExpirationTime,
      );
    case HostPortal:
      return updatePortalComponent(
        current,
        workInProgress,
        renderExpirationTime,
      );
    case ForwardRef: {
      const type = workInProgress.type;
      const unresolvedProps = workInProgress.pendingProps;
      const resolvedProps =
        workInProgress.elementType === type
          ? unresolvedProps
          : resolveDefaultProps(type, unresolvedProps);
      return updateForwardRef(
        current,
        workInProgress,
        type,
        resolvedProps,
        renderExpirationTime,
      );
    }
    case Fragment:
      return updateFragment(current, workInProgress, renderExpirationTime);
    case Mode:
      return updateMode(current, workInProgress, renderExpirationTime);
    case Profiler:
      return updateProfiler(current, workInProgress, renderExpirationTime);
    case ContextProvider:
      return updateContextProvider(
        current,
        workInProgress,
        renderExpirationTime,
      );
    case ContextConsumer:
      return updateContextConsumer(
        current,
        workInProgress,
        renderExpirationTime,
      );
    case MemoComponent: {
      const type = workInProgress.type;
      const unresolvedProps = workInProgress.pendingProps;
      const resolvedProps = resolveDefaultProps(type.type, unresolvedProps);
      return updateMemoComponent(
        current,
        workInProgress,
        type,
        resolvedProps,
        updateExpirationTime,
        renderExpirationTime,
      );
    }
    case SimpleMemoComponent: {
      return updateSimpleMemoComponent(
        current,
        workInProgress,
        workInProgress.type,
        workInProgress.pendingProps,
        updateExpirationTime,
        renderExpirationTime,
      );
    }
    case IncompleteClassComponent: {
      const Component = workInProgress.type;
      const unresolvedProps = workInProgress.pendingProps;
      const resolvedProps =
        workInProgress.elementType === Component
          ? unresolvedProps
          : resolveDefaultProps(Component, unresolvedProps);
      return mountIncompleteClassComponent(
        current,
        workInProgress,
        Component,
        resolvedProps,
        renderExpirationTime,
      );
    }
    default:
      invariant(
        false,
        'Unknown unit of work tag. This error is likely caused by a bug in ' +
          'React. Please file an issue.',
      );
  }
}

export {beginWork};
