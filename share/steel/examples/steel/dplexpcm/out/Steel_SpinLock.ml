
type lock_t = Eio.Mutex.t
type 'a lock = lock_t

let new_lock (_:unit) : 'unit lock =
  Eio.Mutex.create ()

let acquire (_:unit) (l:unit lock) : unit =
  Eio.Mutex.lock l

let release (_:unit) (l:unit lock) : unit =
  Eio.Mutex.unlock l