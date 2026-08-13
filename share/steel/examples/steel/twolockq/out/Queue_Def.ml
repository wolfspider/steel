open Prims
type 'a cell = {
  data: 'a ;
  next: 'a cell Steel_Reference.ref }
let __proj__Mkcell__item__data : 'a . 'a cell -> 'a =
  fun projectee -> match projectee with | { data; next;_} -> data
let __proj__Mkcell__item__next : 'a . 'a cell -> 'a cell Steel_Reference.ref
  = fun projectee -> match projectee with | { data; next;_} -> next
type 'a t = 'a cell Steel_Reference.ref
