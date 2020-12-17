/**
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 */

/* eslint-disable no-var */

// TODO: Use symbols?
var ImmediatePriority = 1;
var UserBlockingPriority = 2;
var NormalPriority = 3;
var IdlePriority = 4;

// Max 31 bit integer. The max integer size in V8 for 32-bit systems.
// Math.pow(2, 30) - 1
// 0b111111111111111111111111111111
var maxSigned31BitInt = 1073741823;

// Times out immediately
var IMMEDIATE_PRIORITY_TIMEOUT = -1;
// Eventually times out
var USER_BLOCKING_PRIORITY = 250;
var NORMAL_PRIORITY_TIMEOUT = 5000;
// Never times out
var IDLE_PRIORITY = maxSigned31BitInt;

// Callbacks are stored as a circular, doubly linked list.
var firstCallbackNode = null;

var currentPriorityLevel = NormalPriority;
var currentEventStartTime = -1;
var currentExpirationTime = -1;

// This is set when a callback is being executed, to prevent re-entrancy.
var isExecutingCallback = false;

var isHostCallbackScheduled = false;

var hasNativePerformanceNow =
  typeof performance === 'object' && typeof performance.now === 'function';

var timeRemaining;
if (hasNativePerformanceNow) {
  timeRemaining = function() {
    if (
      firstCallbackNode !== null &&
      firstCallbackNode.expirationTime < currentExpirationTime
    ) {
      // A higher priority callback was scheduled. Yield so we can switch to
      // working on that.
      return 0;
    }
    // We assume that if we have a performance timer that the rAF callback
    // gets a performance timer value. Not sure if this is always true.
    var remaining = getFrameDeadline() - performance.now();
    return remaining > 0 ? remaining : 0;
  };
} else {
  timeRemaining = function() {
    // Fallback to Date.now()
    if (
      firstCallbackNode !== null &&
      firstCallbackNode.expirationTime < currentExpirationTime
    ) {
      return 0;
    }
    var remaining = getFrameDeadline() - Date.now();
    return remaining > 0 ? remaining : 0;
  };
}

var deadlineObject = {
  timeRemaining,
  didTimeout: false,
};

/**
 * 判断是否已经存在host callback，如果已经存在，则cancelHostCallback，然后开始requestHostCallback(flushWork, expirationTime)，
 * 传入flushWork就是冲刷任务的函数和队首的任务节点的过期时间。
 * 这里我们没有立马执行flushWork，而是交给了requestHostCallback，因为我们并不想直接把任务链表的任务立马执行掉，也不是一口气把链表中的所有任务全部都执行掉。
 * JS是单线程的，我们执行这些任务一直占据着主线程，会导致浏览器的其他任务一直等待，比如动画就会出现卡顿，所以我们选择合适的时期去执行它。
 * 所以我们交给requestHostCallback去处理这件事情，把flushWork交给他，这里暂且可以把flushWork简单的想成执行链表中的任务。
 * 
 * 注：我们需要保证应用的流畅性，因为浏览器是一帧一帧渲染的，每一帧渲染结束之后会有一些空闲时间可以执行别的任务，
 * 那么我们就想利用这点空闲时间来执行我们的任务。
 */
function ensureHostCallbackIsScheduled() {
  if (isExecutingCallback) {   //已经开始调用callback
    // Don't schedule work yet; wait until the next time we yield.
    return;
  }
  // Schedule the host callback using the earliest expiration in the list.
  var expirationTime = firstCallbackNode.expirationTime;
  if (!isHostCallbackScheduled) {   //如果isHostCallbackScheduled为false，也就是还没开始调度，那么设为true，如果已经开始了，就直接取消，因为顺序可能变了。
    isHostCallbackScheduled = true;
  } else {
    // Cancel the existing host callback.
    cancelHostCallback();
  }
  requestHostCallback(flushWork, expirationTime);    //发起调度
}

/**
 * 这里是链表操作，执行完 firstCallback 后把这个 callback 从链表中删除。
 * 这里调用的是当前任务节点flushedNode.callback，那我们这个callback是什么？回到 scheduleCallbackWithExpirationTime 函数 scheduleDeferredCallback(performAsyncWork, {timeout})
 * 它其实就是我们进入Scheduler.js的入口函数。如它传入performAsyncWork作为回调函数，也就是在此函数中调用的回调函数就是这个。
 */
function flushFirstCallback() {
  var flushedNode = firstCallbackNode;

  // Remove the node from the list before calling the callback. That way the
  // list is in a consistent state even if the callback throws.
  // 从链表中取出firstCallbackNode，然后修改相邻节点的next及previous，（该链表是一个环）
  var next = firstCallbackNode.next;
  if (firstCallbackNode === next) {
    // This is the last callback in the list.
    firstCallbackNode = null;
    next = null;
  } else {
    var lastCallbackNode = firstCallbackNode.previous;
    firstCallbackNode = lastCallbackNode.next = next;
    next.previous = lastCallbackNode;
  }

  flushedNode.next = flushedNode.previous = null;

  // Now it's safe to call the callback.
  // 这个 callback 是 performAsyncWork 函数
  var callback = flushedNode.callback;
  var expirationTime = flushedNode.expirationTime;
  var priorityLevel = flushedNode.priorityLevel;
  var previousPriorityLevel = currentPriorityLevel;
  var previousExpirationTime = currentExpirationTime;
  currentPriorityLevel = priorityLevel;
  currentExpirationTime = expirationTime;
  var continuationCallback;
  try {
    continuationCallback = callback(deadlineObject);
  } finally {
    currentPriorityLevel = previousPriorityLevel;
    currentExpirationTime = previousExpirationTime;
  }

  // A callback may return a continuation. The continuation should be scheduled
  // with the same priority and expiration as the just-finished callback.
  if (typeof continuationCallback === 'function') {
    var continuationNode: CallbackNode = {
      callback: continuationCallback,
      priorityLevel,
      expirationTime,
      next: null,
      previous: null,
    };

    // Insert the new callback into the list, sorted by its expiration. This is
    // almost the same as the code in `scheduleCallback`, except the callback
    // is inserted into the list *before* callbacks of equal expiration instead
    // of after.
    if (firstCallbackNode === null) {
      // This is the first callback in the list.
      firstCallbackNode = continuationNode.next = continuationNode.previous = continuationNode;
    } else {
      var nextAfterContinuation = null;
      var node = firstCallbackNode;
      do {
        if (node.expirationTime >= expirationTime) {
          // This callback expires at or after the continuation. We will insert
          // the continuation *before* this callback.
          nextAfterContinuation = node;
          break;
        }
        node = node.next;
      } while (node !== firstCallbackNode);

      if (nextAfterContinuation === null) {
        // No equal or lower priority callback was found, which means the new
        // callback is the lowest priority callback in the list.
        nextAfterContinuation = firstCallbackNode;
      } else if (nextAfterContinuation === firstCallbackNode) {
        // The new callback is the highest priority callback in the list.
        firstCallbackNode = continuationNode;
        ensureHostCallbackIsScheduled();
      }

      var previous = nextAfterContinuation.previous;
      previous.next = nextAfterContinuation.previous = continuationNode;
      continuationNode.next = nextAfterContinuation;
      continuationNode.previous = previous;
    }
  }
}

function flushImmediateWork() {
  if (
    // Confirm we've exited the outer most event handler
    currentEventStartTime === -1 &&
    firstCallbackNode !== null &&
    firstCallbackNode.priorityLevel === ImmediatePriority
  ) {
    isExecutingCallback = true;
    deadlineObject.didTimeout = true;
    try {
      do {
        flushFirstCallback();
      } while (
        // Keep flushing until there are no more immediate callbacks
        firstCallbackNode !== null &&
        firstCallbackNode.priorityLevel === ImmediatePriority
      );
    } finally {
      isExecutingCallback = false;
      if (firstCallbackNode !== null) {
        // There's still work remaining. Request another callback.
        ensureHostCallbackIsScheduled();
      } else {
        isHostCallbackScheduled = false;
      }
    }
  }
}

/**
 * 1、flushWork 根据 didTimeout 参数有两种处理逻辑，如果为 true，就会把任务链表中的过期任务全都执行一遍；如果为false则在当前帧到期之前尽可能多的去执行任务。
 * 2、最后，如果还有任务的话，再启动一轮新的任务执行调度，ensureHostCallbackIsScheduled(),来重置callback链表。重置所有的调度常量，老callback就不会被执行。
 * 3、这里的执行任务是调用flushFirstCallback，执行callback中优先级最高的任务。
 * 
 */
function flushWork(didTimeout) {
  isExecutingCallback = true;
  deadlineObject.didTimeout = didTimeout;
  try {
    if (didTimeout) {
      // Flush all the expired callbacks without yielding.
      while (firstCallbackNode !== null) {
        // Read the current time. Flush all the callbacks that expire at or
        // earlier than that time. Then read the current time again and repeat.
        // This optimizes for as few performance.now calls as possible.
        var currentTime = getCurrentTime();
        if (firstCallbackNode.expirationTime <= currentTime) {
          do {
            flushFirstCallback();
          } while (
            firstCallbackNode !== null &&
            firstCallbackNode.expirationTime <= currentTime
          );
          continue;
        }
        break;
      }
    } else {
      // Keep flushing callbacks until we run out of time in the frame.
      if (firstCallbackNode !== null) {
        do {
          flushFirstCallback();
        } while (
          firstCallbackNode !== null &&
          getFrameDeadline() - getCurrentTime() > 0
        );
      }
    }
  } finally {
    isExecutingCallback = false;
    if (firstCallbackNode !== null) {
      // There's still work remaining. Request another callback.
      ensureHostCallbackIsScheduled();
    } else {
      isHostCallbackScheduled = false;
    }
    // Before exiting, flush all the immediate work that was scheduled.
    flushImmediateWork();
  }
}

function unstable_runWithPriority(priorityLevel, eventHandler) {
  switch (priorityLevel) {
    case ImmediatePriority:
    case UserBlockingPriority:
    case NormalPriority:
    case IdlePriority:
      break;
    default:
      priorityLevel = NormalPriority;
  }

  var previousPriorityLevel = currentPriorityLevel;
  var previousEventStartTime = currentEventStartTime;
  currentPriorityLevel = priorityLevel;
  currentEventStartTime = getCurrentTime();

  try {
    return eventHandler();
  } finally {
    currentPriorityLevel = previousPriorityLevel;
    currentEventStartTime = previousEventStartTime;

    // Before exiting, flush all the immediate work that was scheduled.
    flushImmediateWork();
  }
}

function unstable_wrapCallback(callback) {
  var parentPriorityLevel = currentPriorityLevel;
  return function() {
    // This is a fork of runWithPriority, inlined for performance.
    var previousPriorityLevel = currentPriorityLevel;
    var previousEventStartTime = currentEventStartTime;
    currentPriorityLevel = parentPriorityLevel;
    currentEventStartTime = getCurrentTime();

    try {
      return callback.apply(this, arguments);
    } finally {
      currentPriorityLevel = previousPriorityLevel;
      currentEventStartTime = previousEventStartTime;
      flushImmediateWork();
    }
  };
}

// callback 即 performAsyncWork
function unstable_scheduleCallback(callback, deprecated_options) {
  var startTime =
    currentEventStartTime !== -1 ? currentEventStartTime : getCurrentTime();

  var expirationTime;
  if (
    typeof deprecated_options === 'object' &&
    deprecated_options !== null &&
    typeof deprecated_options.timeout === 'number'
  ) {
    // FIXME: Remove this branch once we lift expiration times out of React.
    // 将来从React中删除了过期时间，就删除这个分支。
    expirationTime = startTime + deprecated_options.timeout;
  } else {
    switch (currentPriorityLevel) {
      case ImmediatePriority:
        expirationTime = startTime + IMMEDIATE_PRIORITY_TIMEOUT;   //IMMEDIATE_PRIORITY_TIMEOUT  -1
        break;
      case UserBlockingPriority:
        expirationTime = startTime + USER_BLOCKING_PRIORITY;   //USER_BLOCKING_PRIORITY 250
        break;
      case IdlePriority:
        expirationTime = startTime + IDLE_PRIORITY;   // IDLE_PRIORITY  maxSigned31BitInt
        break;
      case NormalPriority:
      default:
        expirationTime = startTime + NORMAL_PRIORITY_TIMEOUT;    // NORMAL_PRIORITY_TIMEOUT 5000
    }
  }

  // 环形链表结构
  var newNode = {
    callback,
    priorityLevel: currentPriorityLevel,
    expirationTime,
    next: null,
    previous: null,
  };

  // Insert the new callback into the list, ordered first by expiration, then
  // by insertion. So the new callback is inserted any other callback with
  // equal expiration.
  /**
   * 把任务按照过期时间拍好顺序，然后分两种情况去执行
   * 1、当添加第一个任务节点的时候开始启动任务执行；
   * 2、当新添加的任务取代之前的节点成为新的第一个节点的时候；
   * 因为1意味着任务从无到有，应该立刻启动。2意味着来了新的优先级最高的任务，应该停止掉之前要执行的任务，重新从新的任务开始执行。
   * 上面两种情况就对应 ensureHostCallbackIsScheduled 方法执行的两种情况
   */
  /**
   * 核心思路就是 firstCallbackNode 优先级最高，lastCallbackNode 优先级最低
   * 新生成一个newNode之后，就从头开始比较优先级
   * 如果新的高，就把新的往前插入，否则就往后插，直到没有一个node的优先级比他低
   * 那么新的节点就变成 lastCallbackNode
   * 在改变了 firstCallbackNode 的情况下，需要重新调度
   */
  if (firstCallbackNode === null) {
    // This is the first callback in the list.
    firstCallbackNode = newNode.next = newNode.previous = newNode;
    ensureHostCallbackIsScheduled();
  } else {
    // 以下代码是将firstCallbackNode链表按照expirationTime从小到大排序
    // expirationTime越小，优先级越高，放在最前面，最先调度
    var next = null;
    var node = firstCallbackNode;
    do {
      // 按照优先级从高到低排序（即expirationTime从小到大排序），优先级最大的排在最前面
      if (node.expirationTime > expirationTime) {    //找到第一个expirationTime比当前值大的node
        // The new callback expires before this one.
        next = node;
        break;
      }
      node = node.next;
    } while (node !== firstCallbackNode);

    if (next === null) {  // next为null，说明链表中没有比node.expirationTime值大的节点，即所有节点的优先级都比node高，node的优先级最低（即其expirationTime最大）
      // No callback with a later expiration was found, which means the new
      // callback has the latest expiration in the list.
      next = firstCallbackNode;
    } else if (next === firstCallbackNode) {   // node的优先级最高
      // The new callback has the earliest expiration in the entire list.
      firstCallbackNode = newNode;
      ensureHostCallbackIsScheduled();
    }

    var previous = next.previous;
    previous.next = next.previous = newNode;
    newNode.next = next;
    newNode.previous = previous;
  }

  return newNode;
}

function unstable_cancelCallback(callbackNode) {
  var next = callbackNode.next;
  if (next === null) {
    // Already cancelled.
    return;
  }

  if (next === callbackNode) {
    // This is the only scheduled callback. Clear the list.
    firstCallbackNode = null;
  } else {
    // Remove the callback from its position in the list.
    if (callbackNode === firstCallbackNode) {
      firstCallbackNode = next;
    }
    var previous = callbackNode.previous;
    previous.next = next;
    next.previous = previous;
  }

  callbackNode.next = callbackNode.previous = null;
}

function unstable_getCurrentPriorityLevel() {
  return currentPriorityLevel;
}

// The remaining code is essentially a polyfill for requestIdleCallback. It
// works by scheduling a requestAnimationFrame, storing the time for the start
// of the frame, then scheduling a postMessage which gets scheduled after paint.
// Within the postMessage handler do as much work as possible until time + frame
// rate. By separating the idle call into a separate event tick we ensure that
// layout, paint and other browser work is counted against the available time.
// The frame rate is dynamically adjusted.

// We capture a local reference to any global, in case it gets polyfilled after
// this module is initially evaluated. We want to be using a
// consistent implementation.
var localDate = Date;

// This initialization code may run even on server environments if a component
// just imports ReactDOM (e.g. for findDOMNode). Some environments might not
// have setTimeout or clearTimeout. However, we always expect them to be defined
// on the client. https://github.com/facebook/react/pull/13088
var localSetTimeout = typeof setTimeout === 'function' ? setTimeout : undefined;
var localClearTimeout =
  typeof clearTimeout === 'function' ? clearTimeout : undefined;

// We don't expect either of these to necessarily be defined, but we will error
// later if they are missing on the client.
var localRequestAnimationFrame =
  typeof requestAnimationFrame === 'function'
    ? requestAnimationFrame
    : undefined;
var localCancelAnimationFrame =
  typeof cancelAnimationFrame === 'function' ? cancelAnimationFrame : undefined;

var getCurrentTime;

// requestAnimationFrame does not run when the tab is in the background. If
// we're backgrounded we prefer for that work to happen so that the page
// continues to load in the background. So we also schedule a 'setTimeout' as
// a fallback.
// TODO: Need a better heuristic for backgrounded work.
var ANIMATION_FRAME_TIMEOUT = 100;
var rAFID;
var rAFTimeoutID;
// 调用requestAnimationFrame再加上设置了一个100ms的定时器，防止requestAnimationFrame太久不触发。
// 该函数是解决网页选项卡如果在未激活状态下requestAnimationFrame不会被触发的问题，这样的话，调度器是可以在后台继续做调度的，一方面也能提升用户体验，同时后台执行的时间间隔是以100ms为步长，这个是一个最佳实践，100ms是不会影响用户体验同时也不影响CPU能耗的一个折中时间间隔

/**
 * 这个函数其实可以理解为优化后的requestAnimationFrame。
 * 1、当我们调用 requestAnimationFrameWithTimeout 并传入一个callback的时候，会启动一个 requestAnimationFrame 和一个 setTimeout，两者都会去执行callback。
 * 但由于requestAnimationFrame执行优先级相对较高，它内部会调用clearTimeout取消下面定时器的操作。所以在页面active
 * 情况下的表现根requestAnimationFrame是一致的。
 * 2、requestAnimationFrame在页面切换到未激活的时候是不工作的，这时requestAnimationFrameWithTimeout 就相当于启动了一个100ms的定时器，接管任务的执行工作。
 * 这个执行频率不高也不低，既不影响cpu能耗，又能保证任务能有一定效率的执行。
 */
var requestAnimationFrameWithTimeout = function(callback) {
  // schedule rAF and also a setTimeout
  rAFID = localRequestAnimationFrame(function(timestamp) {
    // cancel the setTimeout
    localClearTimeout(rAFTimeoutID);
    callback(timestamp);
  });
  rAFTimeoutID = localSetTimeout(function() {
    // cancel the requestAnimationFrame
    localCancelAnimationFrame(rAFID);
    callback(getCurrentTime());
  }, ANIMATION_FRAME_TIMEOUT);
};

if (hasNativePerformanceNow) {
  var Performance = performance;
  getCurrentTime = function() {
    return Performance.now();
  };
} else {
  getCurrentTime = function() {
    return localDate.now();
  };
}

var requestHostCallback;
var cancelHostCallback;
var getFrameDeadline;

if (typeof window !== 'undefined' && window._schedMock) {
  // Dynamic injection, only for testing purposes.
  var impl = window._schedMock;
  requestHostCallback = impl[0];
  cancelHostCallback = impl[1];
  getFrameDeadline = impl[2];
} else if (   // 当前不处于浏览器环境
  // If Scheduler runs in a non-DOM environment, it falls back to a naive
  // implementation using setTimeout.
  typeof window === 'undefined' ||
  // "addEventListener" might not be available on the window object
  // if this is a mocked "window" object. So we need to validate that too.
  typeof window.addEventListener !== 'function'
) {
  var _callback = null;
  var _currentTime = -1;
  var _flushCallback = function(didTimeout, ms) {
    if (_callback !== null) {
      var cb = _callback;
      _callback = null;
      try {
        _currentTime = ms;
        cb(didTimeout);
      } finally {
        _currentTime = -1;
      }
    }
  };
  requestHostCallback = function(cb, ms) {
    if (_currentTime !== -1) {
      // Protect against re-entrancy.
      setTimeout(requestHostCallback, 0, cb, ms);
    } else {
      _callback = cb;
      setTimeout(_flushCallback, ms, true, ms);
      setTimeout(_flushCallback, maxSigned31BitInt, false, maxSigned31BitInt);
    }
  };
  cancelHostCallback = function() {
    _callback = null;
  };
  getFrameDeadline = function() {
    return Infinity;
  };
  getCurrentTime = function() {
    return _currentTime === -1 ? 0 : _currentTime;
  };
} else {
  if (typeof console !== 'undefined') {
    // TODO: Remove fb.me link
    if (typeof localRequestAnimationFrame !== 'function') {
      console.error(
        "This browser doesn't support requestAnimationFrame. " +
          'Make sure that you load a ' +
          'polyfill in older browsers. https://fb.me/react-polyfills',
      );
    }
    if (typeof localCancelAnimationFrame !== 'function') {
      console.error(
        "This browser doesn't support cancelAnimationFrame. " +
          'Make sure that you load a ' +
          'polyfill in older browsers. https://fb.me/react-polyfills',
      );
    }
  }

  var scheduledHostCallback = null;
  var isMessageEventScheduled = false;
  var timeoutTime = -1;

  var isAnimationFrameScheduled = false;

  var isFlushingHostCallback = false;

  var frameDeadline = 0;
  // We start out assuming that we run at 30fps but then the heuristic tracking
  // will adjust this value to a faster fps if we get more frequent animation
  // frames.
  // 开始我们假设以每秒30帧的速度运行，但是如果我们得到更频繁的动画帧，启发式跟踪会将这个值调整为更快的fps
  var previousFrameTime = 33;
  var activeFrameTime = 33;

  getFrameDeadline = function() {
    return frameDeadline;
  };

  // We use the postMessage trick to defer idle work until after the repaint.
  var messageKey =
    '__reactIdleCallback$' +
    Math.random()
      .toString(36)
      .slice(2);
  var idleTick = function(event) {
    if (event.source !== window || event.data !== messageKey) {
      return;
    }

    // 一些变量的设置
    isMessageEventScheduled = false;

    var prevScheduledCallback = scheduledHostCallback;
    var prevTimeoutTime = timeoutTime;
    scheduledHostCallback = null;
    timeoutTime = -1;

    // 获取当前时间
    var currentTime = getCurrentTime();

    var didTimeout = false;
    // 判断之前计算的时间是否小于当前时间，小的话说明时间超了，即浏览器渲染等任务执行时间超出了一帧，这一帧没有空闲时间了。
    if (frameDeadline - currentTime <= 0) {
      // There's no time left in this idle period. Check if the callback has
      // a timeout and whether it's been exceeded.
      // 判断当前任务是否过期，
      if (prevTimeoutTime !== -1 && prevTimeoutTime <= currentTime) {  //过期
        // Exceeded the timeout. Invoke the callback even though there's no
        // time left.
        didTimeout = true;
      } else {  // 没过期的话就丢到下一帧去执行
        // No timeout.
        if (!isAnimationFrameScheduled) {
          // Schedule another animation callback so we retry later.
          isAnimationFrameScheduled = true;
          requestAnimationFrameWithTimeout(animationTick);
        }
        // Exit without invoking the callback.
        scheduledHostCallback = prevScheduledCallback;
        timeoutTime = prevTimeoutTime;
        return;
      }
    }

    // 最后执行 flushWork，这里涉及到的 callback 全是 flushWork。
    if (prevScheduledCallback !== null) {
      isFlushingHostCallback = true;
      try {
        prevScheduledCallback(didTimeout);
      } finally {
        isFlushingHostCallback = false;
      }
    }
  };
  // Assumes that we have addEventListener in this environment. Might need
  // something better for old IE.
  window.addEventListener('message', idleTick, false);

  /**
   * 1、有任务再进行递归请求下一帧，没任务的话就可以结束了，退出递归；
   * 2、几个比较重要的全局变量：
   *    frameDeadline初始值为0，计算当前帧的截止时间；
   *    activeFrameTime初始值为33，一帧的渲染时间33ms，这里假设1s 30帧；
   *    var nextFrameTime = rafTime - frameDeadline + activeFrameTime；
   *      rafTime 是传入这个函数的参数，也就是当前帧开始的时间戳。
   *      nextFrameTime就代表一帧的实际渲染时间（第一次执行除外）。之后会根据这个值更新activeFrameTime。动态的根据不同的环境调每一帧的渲染时间，达到系统的刷新频率。
   * 3、在每一帧的回调函数最后，都会调用 window.postMessage(messageKey, '*');
   * 
   */
  var animationTick = function(rafTime) {
    if (scheduledHostCallback !== null) {
      // Eagerly schedule the next animation callback at the beginning of the
      // frame. If the scheduler queue is not empty at the end of the frame, it
      // will continue flushing inside that callback. If the queue *is* empty,
      // then it will exit immediately. Posting the callback at the start of the
      // frame ensures it's fired within the earliest possible frame. If we
      // waited until the end of the frame to post the callback, we risk the
      // browser skipping a frame and not firing the callback until the frame
      // after that.
      // 注意：这里的递归不是同步的，下一帧的时候才会再执行 animationTick
      requestAnimationFrameWithTimeout(animationTick);
    } else {
      // No pending work. Exit.
      isAnimationFrameScheduled = false;
      return;
    }

    // rafTime 就是Date.now()，无论是执行哪个定时器
    // 假如第一次执行animationTick，那么 frameDeadline = 0； activeFrameTime = 33；
    // 也就是此时 nextFrameTime = Date.now() + 33;
    // 为了便于后期计算，我们假设 nextFrameTime = 5000 + 33 = 5033；
    // 第一次执行完，previousFrameTime = 5033； frameDeadline = 5033；
    // 注：activeFrameTime 为什么是33？这里React假设刷新频率是30hz，一秒对应1000ms，1000 / 30 ≈ 33（ms/帧）；
    // ------------------------------------------以下注释是第二次递归
    // 第二次进来时已经是下一帧了，因为animationTick回调是在下一帧进行的，假如我们屏幕是60hz的刷新频率；
    // 那么一帧的时间为1000 / 60 ≈ 16（ms/帧）
    // 此时rafTime 为 rafTime + 16 = 5016；（上一帧的开始时间 + 实际上一帧的耗时时间）
    // 此时nextFrameTime = （5000 + 16）- 5033 + 33 = 16；
    // 第二次执行完，previousFrameTime = 16； frameDeadline = 5000 + 16 + 33 = 5049；
    // ------------------------------------------以下注释是第三次递归
    // 第三次执行时，nextFrameTime = （5000 + 16 * 2）- 5049 + 33 = 16；
    var nextFrameTime = rafTime - frameDeadline + activeFrameTime;
    // 这个if条件第一次肯定进不去
    //------------------------------------------以下注释是第二次递归
    // 第二次： 16 < 33 && 5033 < 33 = false，也就是说第二帧的时候这个if条件还是进不去
    //------------------------------------------以下注释是第三次递归
    // 第三次：16 < 33 && 16 < 33 = true，进入了条件，也就是说如果刷新频率大于30hz，那么得等两帧才会调整 activeFrameTime 的值。
    if (
      nextFrameTime < activeFrameTime &&
      previousFrameTime < activeFrameTime
    ) {
      // 这里小于8的判断，是因为不能处理大于120hz刷新率以上的浏览器了。
      if (nextFrameTime < 8) {
        // Defensive coding. We don't support higher frame rates than 120hz.
        // If the calculated frame time gets lower than 8, it is probably a bug.
        nextFrameTime = 8;
      }
      // If one frame goes long, then the next one can be short to catch up.
      // If two frames are short in a row, then that's an indication that we
      // actually have a higher frame rate than what we're currently optimizing.
      // We adjust our heuristic dynamically accordingly. For example, if we're
      // running on 120hz display or 90hz VR display.
      // Take the max of the two in case one of them was an anomaly due to
      // missed frame deadlines.
      // 第三帧进来以后，activeFrameTime 取 nextFrameTime、previousFrameTime两者中的较大值。（保守计算？）
      activeFrameTime =
        nextFrameTime < previousFrameTime ? previousFrameTime : nextFrameTime;
    } else {
      previousFrameTime = nextFrameTime;
    }
    frameDeadline = rafTime + activeFrameTime;
    // 确保这一帧内不再postMessage
    // postMessage 是宏任务，但先于 setTimeout 执行，执行顺序为： Promise -> onmessage -> setTimeout
    // 对于浏览器来说，当我们执行 requestAnimationFrame 回调后会先让页面渲染，然后判断是否要执行微任务，最后执行宏任务，并且会先执行onmessage；
    // 当前其实比onmessage更快的宏任务是setImmediate，但是这个API只能在高版本IE和Edge中才支持。

    /**
     * 此处解释为什么使用window.postMessage：
     * 1、我们想要的是在每一帧里面先执行浏览器的渲染任务，如果渲染完后还有空闲时间，再执行我们的任务。
     * 2、所以使用window.postMessage，它是macrotask，onmessage的回调函数的调用时机是在一帧的渲染paint完成之后，
     * react scheduler内部正是利用了这一点来在一帧渲染结束后的剩余时间来执行任务的。
     * 3、window.postMessage(messageKey, '*')对应的window.addEventListener('message', idleTick, false) 的监听，会触发idleTick函数的调用。
     * 4、所以我们的任务肯定是在 idleTick 这个事件回调中执行的。
     */
    if (!isMessageEventScheduled) {
      isMessageEventScheduled = true;
      window.postMessage(messageKey, '*');
    }
  };

  /**
   * 1、两个全局变量 scheduledHostCallback、timeoutTime 被赋值，分别代表第一个任务的callback和过期时间。
   * 2、进入这个函数就立马判断当前的任务是否过期，如果过期就立马执行。
   * 3、如果任务没有过期，就等到有空的时候再执行，即交给requestAnimationFrameWithTimeout。
   */
  requestHostCallback = function(callback, absoluteTimeout) {
    scheduledHostCallback = callback;
    timeoutTime = absoluteTimeout;
    // isFlushingHostCallback 只在 channel.port1.onmessage 被设为 true；
    // isFlushingHostCallback 表示所添加的任务需要立即执行；
    // absoluteTimeout < 0 说明超时了；
    if (isFlushingHostCallback || absoluteTimeout < 0) {   
      // Don't wait for the next frame. Continue working ASAP, in a new event.
      // 发送消息，channel.port1.onmessage 会监听到消息并执行；
      window.postMessage(messageKey, '*');
    } else if (!isAnimationFrameScheduled) {   // 还未进入调度循环
      // If rAF didn't already schedule one, we need to schedule a frame.
      // TODO: If this rAF doesn't materialize because the browser throttles, we
      // might want to still have setTimeout trigger rIC as a backup to ensure
      // that we keep performing work.
      isAnimationFrameScheduled = true;
      requestAnimationFrameWithTimeout(animationTick);
    }
  };

  cancelHostCallback = function() {
    scheduledHostCallback = null;
    isMessageEventScheduled = false;
    timeoutTime = -1;
  };
}

export {
  ImmediatePriority as unstable_ImmediatePriority,
  UserBlockingPriority as unstable_UserBlockingPriority,
  NormalPriority as unstable_NormalPriority,
  IdlePriority as unstable_IdlePriority,
  unstable_runWithPriority,
  unstable_scheduleCallback,
  unstable_cancelCallback,
  unstable_wrapCallback,
  unstable_getCurrentPriorityLevel,
  getCurrentTime as unstable_now,
};
