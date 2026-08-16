open Effect
open Effect.Deep

type t = {
  id : int;
  mutable done_ : bool;
  mutable waiters :
    (t * (unit, unit) continuation) list;
}

type _ Effect.t +=
  | Yield : unit Effect.t
  | Join : t -> unit Effect.t
  | Delay : float -> unit Effect.t

type job = t * (unit -> unit)

(* A simple two-list FIFO. *)
let front : job list ref = ref []
let back  : job list ref = ref []

let enqueue t f =
  back := (t, f) :: !back

let dequeue () =
  match !front with
  | x :: xs ->
      front := xs;
      Some x

  | [] ->
      front := List.rev !back;
      back := [];

      match !front with
      | [] ->
          None
      | x :: xs ->
          front := xs;
          Some x

let next_id = ref 1

let fresh_id () =
  let n = !next_id in
  incr next_id;
  n

let current : t option ref =
  ref None

let self () =
  match !current with
  | Some t -> t
  | None -> failwith "JsThread.self: no current thread"

let id t =
  t.id

let finish t =
  if not t.done_ then begin
    t.done_ <- true;

    let waiters = List.rev t.waiters in
    t.waiters <- [];

    List.iter
      (fun (owner, k) ->
         enqueue owner
           (fun () ->
              continue k ()))
      waiters
  end

let create f x =
  let t = {
    id = fresh_id ();
    done_ = false;
    waiters = [];
  } in

  enqueue t
    (fun () ->
       try
         f x;
         finish t
       with exn ->
         finish t;
         Printf.eprintf
           "JsThread %d raised: %s\n%!"
           t.id
           (Printexc.to_string exn));

  t

let yield () =
  perform Yield

let delay seconds =
  perform (Delay seconds)

let join t =
  if not t.done_ then
    perform (Join t)

let run_job (owner, f) =
  current := Some owner;

  match_with f ()
    {
      retc =
        (fun () -> ());

      exnc =
        (fun exn ->
           Printf.eprintf
             "JsThread scheduler: %s\n%!"
             (Printexc.to_string exn));

      effc =
        (fun (type a) (eff : a Effect.t) ->
           match eff with

           | Yield ->
               Some
                 (fun (k : (a, unit) continuation) ->
                    enqueue owner
                      (fun () ->
                         continue k ());
                    ())

           | Delay _seconds ->
               Some
                 (fun (k : (a, unit) continuation) ->
                    (* Initially treat delay as a cooperative yield.
                       We can wire this to setTimeout later. *)
                    enqueue owner
                      (fun () ->
                         continue k ());
                    ())

           | Join target ->
               Some
                 (fun (k : (a, unit) continuation) ->
                    if target.done_ then
                      enqueue owner
                        (fun () ->
                           continue k ())
                    else
                      target.waiters <-
                        (owner, k) :: target.waiters;
                    ())

           | _ ->
               None);
    }

let run f =
  let main = {
    id = 0;
    done_ = false;
    waiters = [];
  } in

  enqueue main
    (fun () ->
       try
         f ();
         finish main
       with exn ->
         finish main;
         raise exn);

  let rec loop () =
    match dequeue () with
    | None ->
        ()
    | Some job ->
        run_job job;
        loop ()
  in

  loop ();

  if not main.done_ then
    failwith "JsThread: scheduler stopped with main blocked"