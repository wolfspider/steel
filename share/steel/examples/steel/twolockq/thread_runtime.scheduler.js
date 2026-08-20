//
// thread_runtime.js with the scheduler in JS.
//
// This is the interface half of "hook the JS scheduler in through
// thread_runtime.js". It only works for an **effects=cps** bundle, and the
// reason is worth stating precisely rather than discovering later:
//
//   A JS primitive can only suspend a thread if it is handed a continuation.
//   js_of_ocaml passes one only to its own effect primitives
//   (`caml_perform_effect(eff, k0)`); user primitives are called direct style.
//   In an effects=disabled bundle `caml_thread_yield(unit){return 0;}` receives
//   `unit` and nothing else, and the thread's remaining work is live JS stack
//   frames with nowhere to go. That is not a tooling gap -- the information is
//   not there.
//
// So `Yield` stays an effect on the OCaml side, and only the *queue and the
// dispatch* move here. JSThread keeps `perform`, and its handler hands the
// continuation out through `caml_jsthread_enqueue`. Continuations are opaque
// to this file: in a CPS bundle a continuation is a plain JS value (an array
// `[245, fiber, fiber]`), so it can sit in a JS queue and be handed back
// untouched.
//
// The run queue then lives on globalThis, which is also where the OCaml heap
// lives -- one context, one heap, no serialisation. That is what lets
// SharedEngine (engine/js_thread-shared.patch) host it across OS threads.
//
// Test with: node threads/scheduler-test.js
//

//Provides: caml_thread_initialize
function caml_thread_initialize(unit) {
  globalThis.__steel_thread_state = {
    next_id: 1,
    current: { id: 0, clos: null, done: true }
  };

  // The scheduler lives on the shared heap so anything in the process can read
  // it. Created by caml_jsthread_state() on first use rather than here, since
  // a JSThread_jsq program never calls this function at all.
  caml_jsthread_state();

  return 0;
}

//Provides: caml_thread_cleanup
function caml_thread_cleanup(unit) {
  return 0;
}

//Provides: caml_jsthread_state
function caml_jsthread_state() {
  // Lazily created, on purpose. `caml_thread_initialize` is only called if the
  // bundle links OCaml's `Thread`; a program using JSThread_jsq alone never
  // references it, so relying on it to set this up left every primitive
  // dereferencing undefined. Found by the first real build.
  if (globalThis.__jsthread === undefined) {
    globalThis.__jsthread = {
      runq: [],
      threads: [],
      next_id: 1,
      current: null,
      dispatches: 0,

      // ---- logical time and epochs (step 5) --------------------------------
      //
      // A runnable item belongs to (time, epoch). Everything sharing both is
      // one *frontier* and may be dispatched together. Work created while an
      // epoch is being dispatched lands in the *next* epoch, never back into
      // the running one -- which is what gives `yield` a precise meaning:
      //
      //     remain at the same logical time, become runnable next epoch.
      //
      // Without that rule a yielding thread could be handed straight back to a
      // worker and starve its peers, which is exactly the lopsided split the
      // un-batched pump produced.
      //
      // The epoch lives on each item rather than in a second queue, so `runq`
      // stays one FIFO array and anything that shifts it naively still sees
      // correct order -- it just ignores the barrier.
      logical_time: 0,
      epoch: 0,          // epoch of the item currently being dispatched
      frontier: 0        // epoch the scheduler is currently handing out
    };
  }
  return globalThis.__jsthread;
}

// ---------------------------------------------------------------------------
// The scheduler surface JSThread calls.
//
// Every one of these is a plain primitive: no continuation is captured here,
// only carried. `k` arrives already reified by js_of_ocaml.
// ---------------------------------------------------------------------------

//Provides: caml_jsthread_publish_driver_api
//Requires: caml_jsthread_dispatch, caml_jsthread_state
function caml_jsthread_publish_driver_api() {
  // An external driver (src/js_thread.rs::Scheduler) needs two things: the
  // queue, which is globalThis.__jsthread already, and a way to invoke a turn.
  //
  // This has to happen inside a //Provides: block. When this file is *linked*
  // into the build -- dune `javascript_files` -- js_of_ocaml includes only the
  // Provides blocks that are reachable and drops everything else, including the
  // footer that publishes these when the file is loaded standalone. So a linked
  // bundle has the primitives in its closure and nothing on globalThis.
  //
  // Reached from caml_jsthread_register, which every create/run_driven calls,
  // so it is always linked and always runs before the first dispatch.
  if (globalThis.caml_jsthread_dispatch === undefined) {
    globalThis.caml_jsthread_dispatch = caml_jsthread_dispatch;
  }
  return 0;
}

//Provides: caml_jsthread_register
//Requires: caml_jsthread_state, caml_jsthread_publish_driver_api
function caml_jsthread_register(unit) {
  var S = caml_jsthread_state();
  caml_jsthread_publish_driver_api();
  var t = { id: S.next_id++, done: false, waiters: [] };
  S.threads.push(t);
  return t;
}

//Provides: caml_jsthread_enqueue
function caml_jsthread_enqueue(t, k) {
  var S = caml_jsthread_state();
  // Next epoch, same logical time. See the note in caml_jsthread_state.
  S.runq.push({ t: t, k: k, epoch: S.epoch + 1, time: S.logical_time });
  return 0;
}

//Provides: caml_jsthread_submit
//Requires: caml_jsthread_state
function caml_jsthread_submit(t, k) {
  // Phase 2: `k` is a *complete OCaml turn* -- calling it runs one logical
  // thread under its own effect handler. The engine no longer asks OCaml to
  // dequeue anything; it just invokes what it was handed.
  var S = caml_jsthread_state();
  S.runq.push({ t: t, k: k, epoch: S.epoch + 1, time: S.logical_time });
  return 0;
}

//Provides: caml_jsthread_submit_js
//Requires: caml_jsthread_state
function caml_jsthread_submit_js(t, k) {
  // Same as submit, but marks the turn as an ordinary JS closure so dispatch
  // calls it directly instead of through caml_callback.
  var S = caml_jsthread_state();
  S.runq.push({ t: t, k: k, epoch: S.epoch + 1, time: S.logical_time, js: true });
  return 0;
}

//Provides: caml_jsthread_submit_after_js
//Requires: caml_jsthread_state
function caml_jsthread_submit_after_js(seconds, t, k) {
  var S = caml_jsthread_state();
  S.runq.push({
    t: t, k: k, epoch: 0, js: true,
    time: S.logical_time + (seconds > 0 ? seconds : 0)
  });
  return 0;
}

//Provides: caml_jsthread_submit_native
//Requires: caml_jsthread_state
function caml_jsthread_submit_native(payload, t, k) {
  // The thread is parked on *native* work: it is not runnable, so this does not
  // go on runq. The host drains this queue, performs the work off the engine
  // lock, and calls back with the result -- see __jsthread_native_take and
  // __jsthread_native_complete, which the driver installs.
  //
  // Under a host with no native worker (plain Node), the host implements the
  // same two entry points inline; the OCaml side cannot tell the difference.
  var S = caml_jsthread_state();
  if (S.nativeq === undefined) { S.nativeq = []; S.native_next_id = 0; }
  S.nativeq.push({ id: S.native_next_id++, payload: payload, t: t, k: k });
  return 0;
}

//Provides: caml_jsthread_dispatch
//Requires: caml_jsthread_state
function caml_jsthread_dispatch(job) {
  // The single place a turn is invoked. caml_callback because in a CPS bundle
  // every OCaml closure expects a continuation as its final argument; this
  // appends one and drives the trampoline.
  var S = caml_jsthread_state();
  S.epoch = job.epoch === undefined ? S.epoch : job.epoch;
  S.current = job.t;
  S.dispatches = S.dispatches + 1;
  if (job.js === true) {
    // A JS-native turn (the tests, or a pure-JS scheduler). Called directly,
    // because it is an ordinary closure and has no continuation convention.
    job.k();
    return 0;
  }
  var cb = typeof caml_callback !== "undefined"
    ? caml_callback
    : globalThis.caml_callback;
  if (typeof cb !== "function") {
    // Deliberately fatal rather than falling back to `job.k()`: an OCaml turn
    // invoked without a continuation would silently do the wrong thing.
    throw new Error("caml_jsthread_dispatch: no caml_callback. Link this file "
      + "into the js_of_ocaml build, or run the bundle through "
      + "patch-for-mqjs.js which publishes it.");
  }
  // `job.arg` is the result of native work, for a continuation parked by
  // caml_jsthread_submit_native. Ordinary turns take unit, i.e. 0.
  cb(job.k, [job.arg === undefined ? 0 : job.arg]);
  return 0;
}

//Provides: caml_jsthread_run_all
//Requires: caml_jsthread_state, caml_jsthread_dispatch, caml_jsthread_advance
function caml_jsthread_run_all(unit) {
  // Standalone dispatch loop, for a bundle using `run` rather than
  // `run_driven`. Under a driver this is never called -- the driver owns it.
  var S = caml_jsthread_state();
  for (;;) {
    if (S.runq.length === 0) {
      return 0;
    }
    caml_jsthread_dispatch(S.runq.shift());
  }
}

//Provides: caml_jsthread_enqueue_after
function caml_jsthread_enqueue_after(seconds, t, k) {
  // A real scheduling operation rather than a disguised yield: the item
  // becomes runnable at a later *logical* time, and the scheduler only
  // advances the clock when nothing at the current time is runnable. Items
  // maturing at the same time form their own frontier.
  var S = caml_jsthread_state();
  var due = S.logical_time + (seconds > 0 ? seconds : 0);
  S.runq.push({ t: t, k: k, epoch: 0, time: due });
  return 0;
}

//Provides: caml_jsthread_runq_empty
function caml_jsthread_runq_empty(unit) {
  return caml_jsthread_state().runq.length === 0 ? 1 : 0;
}

//Provides: caml_jsthread_dequeue
function caml_jsthread_dequeue(unit) {
  // Returns the OCaml tuple (t, k), i.e. a block `[0, t, k]`. Deliberately not
  // an option: `Some (t, k)` would be `[0, [0, t, k]]` -- one more level of
  // boxing than a tuple -- and getting that wrong is a silent misread on the
  // OCaml side rather than an error. Guard with caml_jsthread_runq_empty.
  var S = caml_jsthread_state();
  var job = S.runq.shift();
  S.current = job.t;
  S.dispatches = S.dispatches + 1;
  return [0, job.t, job.k];
}

//Provides: caml_jsthread_finish
function caml_jsthread_finish(t) {
  var S = caml_jsthread_state();
  if (t.done) {
    return 0;
  }
  t.done = true;
  // Waiters become runnable, in the order they blocked -- in the next epoch,
  // like any other work created during a dispatch.
  for (var i = 0; i < t.waiters.length; i++) {
    var w = t.waiters[i];
    w.epoch = S.epoch + 1;
    w.time = S.logical_time;   // `js` is preserved: it is set when parked
    S.runq.push(w);
  }
  t.waiters = [];
  return 0;
}

//Provides: caml_jsthread_wait_js
//Requires: caml_jsthread_state
function caml_jsthread_wait_js(target, owner, k) {
  // As caml_jsthread_wait, but marks the parked turn as an ordinary JS closure.
  // Without this a join continuation loses its js-ness and dispatch sends it
  // down the caml_callback path meant for OCaml turns.
  var S = caml_jsthread_state();
  if (target.done) {
    S.runq.push({ t: owner, k: k, epoch: S.epoch + 1, time: S.logical_time, js: true });
  } else {
    target.waiters.push({ t: owner, k: k, js: true });
  }
  return 0;
}

//Provides: caml_jsthread_wait
function caml_jsthread_wait(target, owner, k) {
  var S = caml_jsthread_state();
  if (target.done) {
    S.runq.push({ t: owner, k: k, epoch: S.epoch + 1, time: S.logical_time });
  } else {
    // Parked. Stamped when released by finish, not now -- it becomes runnable
    // at whatever time the release happens.
    target.waiters.push({ t: owner, k: k });
  }
  return 0;
}

//Provides: caml_jsthread_self
function caml_jsthread_self(unit) {
  return caml_jsthread_state().current;
}

//Provides: caml_jsthread_id
function caml_jsthread_id(t) {
  return t.id;
}

//Provides: caml_jsthread_done
function caml_jsthread_done(t) {
  return t.done ? 1 : 0;
}

//Provides: caml_jsthread_step_js
//Requires: caml_jsthread_state, caml_jsthread_dispatch
function caml_jsthread_step_js(unit) {
  // Dispatch one runnable turn. In phase 1 this was an OCaml closure published
  // through set_stepper; now the queue holds directly-callable turns, so it
  // lives here and needs nothing from OCaml. Kept under the same global name
  // so existing drivers keep working.
  var S = caml_jsthread_state();
  if (S.runq.length === 0) {
    return false;
  }
  caml_jsthread_dispatch(S.runq.shift());
  return true;
}

// ---------------------------------------------------------------------------
// Frontier handoff.
//
// Lets a native scheduler hand several runnable turns to several workers at
// once. The invariant that makes it safe: **the runnable value never leaves
// globalThis.** `take_n` moves items out of runq into `parked`, and the only
// thing crossing to native code is an integer token. Nothing GC-managed is ever
// held outside the engine, so there is no rooting problem and no lifetime
// question -- a token is just a number.
// ---------------------------------------------------------------------------

//Provides: caml_jsthread_handoff_state
function caml_jsthread_handoff_state() {
  if (globalThis.__jsthread_handoff === undefined) {
    globalThis.__jsthread_handoff = { next_id: 0, parked: [], parked_count: 0 };
  }
  return globalThis.__jsthread_handoff;
}

//Provides: caml_jsthread_take_n
//Requires: caml_jsthread_state, caml_jsthread_handoff_state
function caml_jsthread_take_n(n) {
  var s = caml_jsthread_state();
  var h = caml_jsthread_handoff_state();
  var ids = [];
  // Claim only from the current frontier: same logical time, same epoch.
  // Stopping at the boundary *is* the barrier -- the scheduler cannot hand out
  // epoch N+1 while epoch N is still being worked, because advancing is a
  // separate call the broker only makes when nothing is outstanding.
  for (var i = 0; i < s.runq.length && ids.length < n; ) {
    var item = s.runq[i];
    if (item.time !== s.logical_time || item.epoch !== s.frontier) {
      i = i + 1;              // not this frontier; leave it for later
      continue;
    }
    var id = h.next_id++;
    h.parked[id] = item;      // removed but NOT executed; still rooted here
    h.parked_count++;
    s.runq.splice(i, 1);
    ids.push(id);
  }
  return ids.join(",");
}

//Provides: caml_jsthread_advance
//Requires: caml_jsthread_state
function caml_jsthread_advance(unit) {
  // The barrier. Called only when the current frontier is exhausted *and*
  // nothing is outstanding natively, so every item of the old epoch has fully
  // returned before any of the next one starts.
  //
  // Returns 1 if there is now a frontier to dispatch, 0 if genuinely drained.
  var S = caml_jsthread_state();
  if (S.runq.length === 0) {
    return 0;
  }
  // Earliest logical time present, then earliest epoch at that time.
  var best_time = null;
  var best_epoch = null;
  for (var i = 0; i < S.runq.length; i++) {
    var it = S.runq[i];
    if (best_time === null || it.time < best_time
        || (it.time === best_time && it.epoch < best_epoch)) {
      best_time = it.time;
      best_epoch = it.epoch;
    }
  }
  S.logical_time = best_time;
  S.frontier = best_epoch;
  return 1;
}

//Provides: caml_jsthread_frontier_width
//Requires: caml_jsthread_state
function caml_jsthread_frontier_width(unit) {
  var S = caml_jsthread_state();
  var n = 0;
  for (var i = 0; i < S.runq.length; i++) {
    if (S.runq[i].time === S.logical_time && S.runq[i].epoch === S.frontier) {
      n = n + 1;
    }
  }
  return n;
}

//Provides: caml_jsthread_resume
//Requires: caml_jsthread_state, caml_jsthread_handoff_state, caml_jsthread_dispatch
function caml_jsthread_resume(id) {
  var s = caml_jsthread_state();
  var h = caml_jsthread_handoff_state();
  var work = h.parked[id];
  if (work === undefined || work === null) {
    throw new Error("invalid handoff token " + id);
  }
  h.parked[id] = null;
  h.parked_count--;
  // Every queued item is a complete turn -- `k` expands to `run_job owner f`
  // and so carries its own effect handler. Invoking it directly is the whole
  // point of phase 2; there is nothing to ask OCaml for.
  //
  // (A phase-1 bundle queued *bare continuations*, which had to go through
  // OCaml's own step to get a handler installed. That branch is gone with the
  // bundle shape that needed it.)
  caml_jsthread_dispatch(work);
  return true;
}

//Provides: caml_jsthread_drained
//Requires: caml_jsthread_state, caml_jsthread_handoff_state
function caml_jsthread_drained(unit) {
  return caml_jsthread_state().runq.length === 0
    && caml_jsthread_handoff_state().parked_count === 0 ? 1 : 0;
}

//Provides: caml_jsthread_stats
function caml_jsthread_stats(unit) {
  var S = caml_jsthread_state();
  return [0, S.threads.length, S.dispatches, S.runq.length];
}

// ---------------------------------------------------------------------------
// The original primitives, unchanged.
//
// With the scheduler above in use these are not what drives execution -- but a
// bundle that links `Thread` rather than JSThread still resolves against them,
// and they keep the documented behaviour: a thread body runs inline at join,
// to completion, so threads do not interleave. See ../probes/thread-semantics.js.
// ---------------------------------------------------------------------------

//Provides: caml_thread_new
function caml_thread_new(clos) {
  var state = globalThis.__steel_thread_state;
  return { id: state.next_id++, clos: clos, done: false };
}

//Provides: caml_thread_self
function caml_thread_self(unit) {
  return globalThis.__steel_thread_state.current;
}

//Provides: caml_thread_id
function caml_thread_id(thread) {
  return thread.id;
}

//Provides: caml_thread_join
//Requires: caml_call_gen
function caml_thread_join(thread) {
  if (!thread.done) {
    var state = globalThis.__steel_thread_state;
    var previous = state.current;
    state.current = thread;
    try {
      thread.done = true;
      caml_call_gen(thread.clos, [0]);
    } finally {
      state.current = previous;
    }
  }
  return 0;
}

//Provides: caml_thread_yield
function caml_thread_yield(unit) {
  return 0;
}

//Provides: caml_unix_sleep
function caml_unix_sleep(seconds) {
  return 0;
}

//Provides: caml_thread_uncaught_exception
function caml_thread_uncaught_exception(exn) {
  // console.log, not console.error: mquickjs has console.log but neither
  // console.error nor console.warn, so reporting an uncaught exception would
  // itself throw and lose the exception being reported. (prelude.js also
  // aliases the missing methods, which covers js_of_ocaml's own seven uses.)
  console.log("OCaml thread raised an exception:", exn);
  return 0;
}

// ---------------------------------------------------------------------------
// Publish to globalThis.
//
// Two reasons this is explicit rather than relying on top-level declarations:
//
//  - mquickjs keeps the global object and script globals separate ("properties
//    directly created in it are not visible as global variables", and the
//    converse also holds), so a bare `function foo(){}` in an -I file is not
//    reachable as `globalThis.foo`.
//  - it is what makes this file usable *without rebuilding*. js_of_ocaml's
//    --genprim dummies are written as
//        globalThis.NAME !== undefined ? globalThis.NAME : (throwing stub)
//    so a bundle built with "missing primitives" warnings still picks these up
//    at runtime if they are on the global object before it runs.
//
// Harmless when this file is instead passed to js_of_ocaml as a runtime file:
// the //Provides: annotations above are what matter there.
// ---------------------------------------------------------------------------

(function (G) {
  G.caml_thread_initialize = caml_thread_initialize;
  G.caml_thread_cleanup = caml_thread_cleanup;
  G.caml_jsthread_state = caml_jsthread_state;

  G.caml_jsthread_register = caml_jsthread_register;
  G.caml_jsthread_enqueue = caml_jsthread_enqueue;
  G.caml_jsthread_runq_empty = caml_jsthread_runq_empty;
  G.caml_jsthread_dequeue = caml_jsthread_dequeue;
  G.caml_jsthread_finish = caml_jsthread_finish;
  G.caml_jsthread_wait = caml_jsthread_wait;
  G.caml_jsthread_self = caml_jsthread_self;
  G.caml_jsthread_id = caml_jsthread_id;
  G.caml_jsthread_done = caml_jsthread_done;
  G.caml_jsthread_stats = caml_jsthread_stats;
  G.caml_jsthread_handoff_state = caml_jsthread_handoff_state;
  G.__jsthread_take_n = caml_jsthread_take_n;
  G.__jsthread_resume = caml_jsthread_resume;
  G.__jsthread_drained = caml_jsthread_drained;
  G.__jsthread_advance = caml_jsthread_advance;
  G.__jsthread_frontier_width = caml_jsthread_frontier_width;
  G.__jsthread_take_n = caml_jsthread_take_n;
  G.__jsthread_resume = caml_jsthread_resume;
  G.__jsthread_drained = caml_jsthread_drained;
  G.__jsthread_advance = caml_jsthread_advance;
  G.__jsthread_frontier_width = caml_jsthread_frontier_width;
  G.caml_jsthread_enqueue_after = caml_jsthread_enqueue_after;
  G.caml_jsthread_submit = caml_jsthread_submit;
  G.caml_jsthread_submit_js = caml_jsthread_submit_js;
  G.caml_jsthread_submit_after_js = caml_jsthread_submit_after_js;
  G.caml_jsthread_wait_js = caml_jsthread_wait_js;
  G.caml_jsthread_dispatch = caml_jsthread_dispatch;
  G.caml_jsthread_run_all = caml_jsthread_run_all;
  G.__jsthread_step = caml_jsthread_step_js;

  G.caml_thread_new = caml_thread_new;
  G.caml_thread_self = caml_thread_self;
  G.caml_thread_id = caml_thread_id;
  G.caml_thread_join = caml_thread_join;
  G.caml_thread_yield = caml_thread_yield;
  G.caml_unix_sleep = caml_unix_sleep;
  G.caml_thread_uncaught_exception = caml_thread_uncaught_exception;
})(typeof globalThis !== "undefined" ? globalThis : this);
