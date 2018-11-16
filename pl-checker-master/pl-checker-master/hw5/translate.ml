(*
 * SNU 4190.310 Programming Languages 
 * K-- to SM5 translator skeleton code
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
 *)

open K
open Sm5
module Translator = struct
  (* TODO : complete this function  *)
  let rec trans : K.program -> Sm5.command = function
  	| K.TRUE -> [Sm5.PUSH (Sm5.Val (Sm5.B true))]
	| K.FALSE -> [Sm5.PUSH (Sm5.Val (Sm5.B false))]
    | K.NUM i -> [Sm5.PUSH (Sm5.Val (Sm5.Z i))]
	| K.UNIT -> [Sm5.PUSH (Sm5.Val (Sm5.Unit))]
	| K.VAR i -> [Sm5.PUSH (Sm5.Id i)] @ [Sm5.LOAD]
    | K.ADD (e1, e2) -> trans e1 @ trans e2 @ [Sm5.ADD]
    | K.SUB (e1, e2) -> trans e1 @ trans e2 @ [Sm5.SUB]
    | K.MUL (e1, e2) -> trans e1 @ trans e2 @ [Sm5.MUL]
    | K.DIV (e1, e2) -> trans e1 @ trans e2 @ [Sm5.DIV]
    | K.EQUAL (e1, e2) -> trans e1 @ trans e2 @ [Sm5.EQ]
    | K.LESS (e1, e2) -> trans e1 @ trans e2 @ [Sm5.LESS]
    | K.NOT e -> trans e @ [Sm5.NOT]
    | K.ASSIGN (id, e) -> trans e @ [Sm5.PUSH (Sm5.Id id)] @ [Sm5.STORE] @ [Sm5.PUSH (Sm5.Id id)] @ [Sm5.LOAD]
    | K.SEQ (e1, e2) -> trans e1 @ [Sm5.POP] @ trans e2
    | K.IF (e1, e2, e3) -> trans e1 @ [Sm5.JTR(trans e2, trans e3)]
    | K.WHILE (e1, e2) -> trans (K.LETF ("@f@", "@v@", K.IF (K.VAR "@v@", K.SEQ (e2, K.CALLV ("@f@", e1)), K.UNIT), K.CALLV ("@f@", e1)))
    | K.FOR (id, e1, e2, e_body) ->
      let temp = K.WHILE (K.LESS (K.VAR id, K.ADD (K.VAR "@f2@", K.NUM 1)), K.SEQ (e_body, K.ASSIGN (id, K.ADD (K.VAR id, K.NUM 1)))) in
      trans (K.LETV("@f1@", e1, K.LETV("@f2@", e2, K.LETV(id, K.VAR("@f1@"), temp))))
    | K.LETV (x, e1, e2) ->
      trans e1 @ [Sm5.MALLOC; Sm5.BIND x; Sm5.PUSH (Sm5.Id x); Sm5.STORE] @
      trans e2 @ [Sm5.UNBIND; Sm5.POP]
	| K.LETF (f, x, e1, e2) ->
      let temp = [Sm5.BIND f] @ trans e1 @ [Sm5.UNBIND; Sm5.POP] in
      [Sm5.PUSH (Sm5.Fn (x, temp))] @ [Sm5.BIND f] @ trans e2 @ [Sm5.UNBIND] @ [Sm5.POP]
	| K.CALLV(id, e) -> [Sm5.PUSH (Sm5.Id id)] @ [Sm5.PUSH (Sm5.Id id)] @ trans e @ [Sm5.MALLOC] @ [Sm5.CALL]
 	| K.CALLR(f, x) -> [Sm5.PUSH (Sm5.Id f); Sm5.PUSH (Sm5.Id f); Sm5.PUSH (Sm5.Id x); Sm5.LOAD; Sm5.PUSH (Sm5.Id x); Sm5.CALL]
    | K.READ x -> [Sm5.GET; Sm5.PUSH (Sm5.Id x); Sm5.STORE; Sm5.PUSH (Sm5.Id x); Sm5.LOAD]
    | K.WRITE e ->
      trans e @ [Sm5.MALLOC] @ [Sm5.BIND "@w@"] @ [Sm5.PUSH (Sm5.Id "@w@")] @ [Sm5.STORE] @ [Sm5.PUSH (Sm5.Id "@w@")] @ 
      [Sm5.LOAD] @ [Sm5.PUT] @ [Sm5.PUSH (Sm5.Id "@w@")] @ [Sm5.LOAD] @ [Sm5.UNBIND] @ [Sm5.POP]
end
