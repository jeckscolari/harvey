(** This module provides inter-processes utils *)

open Lymp

let interpreter = "python3"
let py = init ~exec:interpreter "."
let m = get_module py "utils"


let out s =
    print_endline s
    (*call m "monitor_out" [Pystr s]*)


let err s =
    out s
    (*call m "monitor_err" [Pystr s]*)


let failwith s =
    err s;
    failwith s


let get_trace ts =
	let trace = get_string m "get_trace" [Pyfloat ts] in
        trace ^ "\n"
