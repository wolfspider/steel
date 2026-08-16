//Provides: caml_thread_initialize
function caml_thread_initialize(unit) {
  globalThis.__steel_thread_state = {
    next_id: 1,
    current: {
      id: 0,
      clos: null,
      done: true
    }
  };
  return 0;
}

//Provides: caml_thread_cleanup
function caml_thread_cleanup(unit) {
  return 0;
}

//Provides: caml_thread_new
function caml_thread_new(clos) {
  var state = globalThis.__steel_thread_state;

  return {
    id: state.next_id++,
    clos: clos,
    done: false
  };
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
  console.error("OCaml thread raised an exception:", exn);
  return 0;
}