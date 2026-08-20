(* JSThread with its run queue in JS.

   The delta from your JSThread is small and entirely in the plumbing: `front`
   and `back` stop being OCaml refs and become the queue inside
   thread_runtime.scheduler.js, on globalThis. The effect handlers are
   unchanged in shape.

   `perform` stays here, and has to. js_of_ocaml hands a continuation only to
   its own effect primitives (`caml_perform_effect(eff, k0)`); a user primitive
   is called direct style even in a CPS bundle, so a JS `caml_thread_yield`
   receives `unit` and has nothing to suspend. The continuation must be captured
   on this side and *passed out* -- which is all the externals below do. They
   carry `k`, they never create it.

   Build with effects=cps. Under effects=disabled there are no continuations at
   all and this cannot work; see ../THREADS.md.

   NOT COMPILED HERE -- there is no OCaml toolchain on this machine. The JS half
   is tested (threads/scheduler-test.js, on both node and mqjs, 25000 per
   consumer); this half is written against that verified surface but has not
   been through a compiler. Expect to fix a type annotation or two. *)

open Effect
open Effect.Deep

(* The JS-side thread record. Abstract: it is a JS object, and nothing here
   inspects it. *)
type jsthread

type t = jsthread

type _ Effect.t +=
  | Yield : unit Effect.t
  | Join : t -> unit Effect.t
  | Delay : float -> unit Effect.t
  (* Native work requested *by the program*. The payload goes out, the thread
     parks, and the continuation is resumed with the result. This is the whole
     point: the work belongs to the task, not to the harness. *)
  | Native : string -> string Effect.t

(* The scheduler surface. Each of these is a plain primitive in
   thread_runtime.scheduler.js -- no continuation is captured by any of them. *)

external register : unit -> t = "caml_jsthread_register"

(* Submit one ready-to-run turn. Everything handed to the engine through this
   means the same thing: *execute exactly one logical-thread turn under the
   correct effect handler*. The engine never asks OCaml to dequeue and never
   needs to know what effects are -- it just invokes what it was given.

   That is the whole of phase 2. `runq_empty`, `dequeue`, `step` and
   `set_stepper` are gone: they existed only so the engine could ask OCaml to
   do the next thing. *)
external submit : t -> (unit -> unit) -> unit = "caml_jsthread_submit"

external finish_js : t -> unit = "caml_jsthread_finish"
external wait : t -> t -> (unit -> unit) -> unit = "caml_jsthread_wait"
external self : unit -> t = "caml_jsthread_self"
external id : t -> int = "caml_jsthread_id"
external is_done : t -> bool = "caml_jsthread_done"

(* Becomes runnable at a later *logical* time rather than in the next epoch.
   The scheduler only advances its clock when nothing at the current time is
   runnable, so a delay never blocks anything that still has work to do, and
   items maturing at the same time form their own frontier. *)
external submit_after_js :
  float -> t -> (unit -> unit) -> unit = "caml_jsthread_enqueue_after"

(* Park `k` on a native work queue with its payload. The continuation takes the
   *result*, not unit -- it is resumed with what the native side computed. *)
external submit_native :
  string -> t -> (string -> unit) -> unit = "caml_jsthread_submit_native"

(* Runs submitted turns until nothing is runnable. Only for standalone use --
   under an external driver the driver owns this loop. *)
external run_all : unit -> unit = "caml_jsthread_run_all"

let finish t = finish_js t

let yield () = perform Yield
let delay seconds = perform (Delay seconds)

let join t = if not (is_done t) then perform (Join t)

(* Hand `payload` to the host, park, and return its result. Under mquickjs the
   host runs this off the engine lock on a worker thread; under Node it runs
   inline. Either way it is the same OCaml program asking. *)
let native payload = perform (Native payload)

(* `run_job` is one schedulable turn, and is now also what every queued thunk
   expands to -- see submit_job below. Mutually recursive with the submit
   helpers because each effect re-submits the continuation wrapped in another
   turn. *)
let rec run_job (owner : t) (f : unit -> unit) =
  match_with f ()
    {
      retc = (fun () -> ());
      exnc =
        (fun exn ->
          Printf.eprintf "JsThread scheduler: %s\n%!" (Printexc.to_string exn));
      effc =
        (fun (type a) (eff : a Effect.t) ->
          match eff with
          | Yield ->
              Some
                (fun (k : (a, unit) continuation) ->
                  submit_job owner (fun () -> continue k ()))
          | Delay seconds ->
              (* Not a disguised yield: `submit_job` means "same logical time,
                 next epoch", this means "a later logical time". *)
              Some
                (fun (k : (a, unit) continuation) ->
                  submit_after seconds owner (fun () -> continue k ()))
          | Native payload ->
              Some
                (fun (k : (a, unit) continuation) ->
                  submit_native payload owner
                    (fun (r : string) -> run_job owner (fun () -> continue k r)))
          | Join target ->
              Some
                (fun (k : (a, unit) continuation) ->
                  (* wait handles both cases: already-done targets are made
                     runnable immediately, the rest are parked on the target. *)
                  wait_job target owner (fun () -> continue k ()))
          | _ -> None);
    }

(* Each of these queues a *complete turn*, not a bare continuation: what the
   engine receives already carries its own effect handler. *)
and submit_job owner f = submit owner (fun () -> run_job owner f)
and submit_after seconds owner f =
  submit_after_js seconds owner (fun () -> run_job owner f)
and wait_job target owner f = wait target owner (fun () -> run_job owner f)

(* Defined after the recursive group above, because it submits a turn and
   `submit_job` is part of that group. *)
let create f x =
  let t = register () in
  submit_job t (fun () ->
      (try
         f x
       with exn ->
         Printf.eprintf "JsThread %d raised: %s\n%!" (id t)
           (Printexc.to_string exn));
      finish t);
  t

(* Submit main and return. Dispatch belongs to whoever is driving; there is no
   longer a stepper to publish, because the queued thunks are directly callable
   and the engine needs nothing from OCaml to run them. *)
let run_driven f =
  let main = register () in
  submit_job main (fun () ->
      f ();
      finish main)

let run f =
  let main = register () in
  submit_job main (fun () ->
      f ();
      finish main);
  run_all ();
  if not (is_done main) then
    failwith "JsThread: scheduler stopped with main blocked"
