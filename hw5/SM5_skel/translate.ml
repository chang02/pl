(* (*
 * SNU 4190.310 Programming Languages 
 * K-- to SM5 translator skeleton code
 *)

open K
open Sm5
module Translator = struct

  (* TODO : complete this function  *)
  let rec trans : K.program -> Sm5.command = function
    | K.NUM i -> [Sm5.PUSH (Sm5.Val (Sm5.Z i))]
    | K.TRUE -> [Sm5.PUSH (Sm5.Val (Sm5.B true))]
    | K.FALSE -> [Sm5.PUSH (Sm5.Val (Sm5.B false))]
    | K.UNIT -> [Sm5.PUSH (Sm5.Val (Sm5.Unit))]
    | K.VAR id -> [Sm5.PUSH (Sm5.Id id) ; Sm5.LOAD]

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
    | K.WHILE (e, e1) -> 
        (
            let fname = "$f" in
            let vname = "$v" in
            let func = K.IF (e, K.SEQ (e1, K.CALLV (fname, K.UNIT)), K.UNIT) in
            trans (K.LETF(fname, vname, func, K.CALLV (fname, K.UNIT)))
        )
    | K.FOR (id, e1, e2, e3) ->
        (
            let tvar = "$t" in
            trans (
                K.LETV (tvar, K.ADD (e2, K.NUM 1), K.LETV (id, e1, 
                    K.WHILE (K.LESS (K.VAR id, K.VAR tvar),
                        K.SEQ (e3, K.ASSIGN (id, K.ADD (K.VAR id, K.NUM 1)))
                    )
                ))
            )
        )
    | K.LETV (id, e1, e2) ->
        trans e1 @
        [Sm5.MALLOC] @ [Sm5.BIND id] @ [Sm5.PUSH (Sm5.Id id)] @ [Sm5.STORE] @
        trans e2 @
        [Sm5.UNBIND] @ [Sm5.POP]
    | K.LETF (id1, id2, e1, e2) ->
        [Sm5.PUSH (Sm5.Fn (id2, [Sm5.BIND id1] @ trans e1))] @ [Sm5.BIND id1] @
        trans e2 @
        [Sm5.UNBIND] @ [Sm5.POP] 
    | K.CALLV(id, e) -> 
        [Sm5.PUSH (Sm5.Id id)] @
        [Sm5.PUSH (Sm5.Id id)] @
        trans e @
        [Sm5.MALLOC] @
        [Sm5.CALL]
    | K.CALLR (id1, id2) -> 
        [Sm5.PUSH (Sm5.Id id1)] @
        [Sm5.PUSH (Sm5.Id id1)] @
        [Sm5.PUSH (Sm5.Id id2)] @
        [Sm5.LOAD] @
        [Sm5.PUSH (Sm5.Id id2)] @
        [Sm5.CALL]
    | K.READ x -> [Sm5.GET] @ [Sm5.PUSH (Sm5.Id x)] @ [Sm5.STORE] @ [Sm5.PUSH (Sm5.Id x)] @ [Sm5.LOAD]
    | K.WRITE e ->
        let wname = "$w" in
        trans e @ [Sm5.MALLOC] @ [Sm5.BIND wname] @
        [Sm5.PUSH (Sm5.Id wname)] @ [Sm5.STORE] @
        [Sm5.PUSH (Sm5.Id wname)] @ [Sm5.LOAD] @ [Sm5.PUT] @
        [Sm5.PUSH (Sm5.Id wname)] @ [Sm5.LOAD] @ [Sm5.UNBIND] @ [Sm5.POP]
    | _ -> failwith "Unimplemented"
end
 *)
 (*
 * SNU 4190.310 Programming Languages 
 * K-- to SM5 translator skeleton code
 * Jaeseung Choi (jschoi@ropas.snu.ac.kr)
 *)

open K
open Sm5
module Translator =
  struct
    let tmpV, tmpF, tmpI, tmpN = "@", "#", "$", "%"
    let push = fun id -> Sm5.PUSH (Sm5.Id id)

    let rec trans : K.program -> Sm5.command = function
      | K.NUM i -> [Sm5.PUSH (Sm5.Val (Sm5.Z i))]
      | K.TRUE -> [Sm5.PUSH (Sm5.Val (Sm5.B true))]
      | K.FALSE -> [Sm5.PUSH (Sm5.Val (Sm5.B false))]
      | K.UNIT -> [Sm5.PUSH (Sm5.Val (Sm5.Unit))]
      | K.ADD (e1, e2) -> trans e1 @ trans e2 @ [Sm5.ADD]
      | K.SUB (e1, e2) -> trans e1 @ trans e2 @ [Sm5.SUB]
      | K.MUL (e1, e2) -> trans e1 @ trans e2 @ [Sm5.MUL]
      | K.VAR x -> [push x; Sm5.LOAD]
      | K.DIV (e1, e2) -> trans e1 @ trans e2 @ [Sm5.DIV]
      | K.EQUAL (e1, e2) -> trans e1 @ trans e2 @ [Sm5.EQ]
      | K.LESS (e1, e2) -> trans e1 @ trans e2 @ [Sm5.LESS]
      | K.NOT e -> trans e @ [Sm5.NOT]
      | K.ASSIGN (x, e) -> trans e @ [push x; Sm5.STORE; push x; Sm5.LOAD]
      | K.SEQ (e1, e2) -> trans e1 @ [Sm5.POP] @ trans e2
      | K.IF (e, e1, e2) ->
          trans e @ [Sm5.JTR (trans e1, trans e2)]
      | K.WHILE (e1, e2) ->
          let f = K.IF (K.VAR tmpV, K.SEQ (e2, K.CALLV (tmpF, e1)), K.UNIT) in
          trans (K.LETF (tmpF, tmpV, f, K.CALLV (tmpF, e1)))
      | K.FOR (x, e1, e2, e3) ->
          let loop =
            K.WHILE
              (K.NOT (K.LESS (K.VAR tmpN, K.VAR tmpI)),
              K.SEQ
                (K.ASSIGN (x, K.VAR tmpI),
                K.SEQ (e3, K.ASSIGN (tmpI, K.ADD (K.VAR tmpI, K.NUM 1))))) in
          trans (K.LETV (tmpI, e1, K.LETV (tmpN, e2, loop)))
      | K.LETV (x, e1, e2) ->
          trans e1 @ [Sm5.MALLOC; Sm5.BIND x; push x; Sm5.STORE] @
          trans e2 @ [Sm5.UNBIND; Sm5.POP]
      | K.LETF (f, x, e1, e2) ->
          [Sm5.PUSH (Sm5.Fn (x, Sm5.BIND f :: trans e1)); Sm5.BIND f] @
          trans e2 @ [Sm5.UNBIND; Sm5.POP]
      | K.CALLV (f, e) -> [push f; push f] @ trans e @ [Sm5.MALLOC; Sm5.CALL]
      | K.CALLR (f, x) -> [push f; push f; push x; Sm5.LOAD; push x; Sm5.CALL]
      | K.READ x -> [Sm5.GET; push x; Sm5.STORE; push x; Sm5.LOAD]
      | K.WRITE e ->
          trans e @ [Sm5.MALLOC; Sm5.BIND tmpV; push tmpV; Sm5.STORE] @
          [push tmpV; Sm5.LOAD; Sm5.PUT; push tmpV; Sm5.LOAD; Sm5.UNBIND]

  end