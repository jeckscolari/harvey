type token =
  | AT
  | LPA
  | RPA
  | COM
  | STR of (string)
  | EOF
  | ERR

val signature :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> (Db.schema)
val tsdb :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> (MFOTL.timestamp * Db.db) option
