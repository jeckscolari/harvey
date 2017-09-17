(** This module provides inter-processes utils *)

val out: string -> unit

val err: string -> unit

val failwith: string -> 'a

val get_trace: float -> string