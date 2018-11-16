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
module Translator = struct
  let rec trans (input: K.program): Sm5.command =
    let rec desugar (input: K.program): K.program =
      match input with
      | K.WHILE (econd, ebody) -> begin
        (*
         * while(econd) { ebody; }
         *
         * // ... is same with ...
         *
         * function f() {
         *   if (econd) {
         *     ebody;
         *     f()
         *   }
         * };
         * f()
         *)
        let tempname = "λwhile" in
        K.LETF (
          tempname, "γ",
            K.IF (econd,
              K.SEQ (
                ebody,
                desugar (K.CALLV (tempname, K.UNIT))
              ),
            K.UNIT),
          desugar (K.CALLV (tempname, K.UNIT))
        )
      end
      | K.FOR (i, efrom, eto, ebody) -> begin
        (*
         * for i in efrom..eto {
         *   ebody
         * }
         *
         * // ... is same with ...
         *
         * int from = efrom;
         * int to = eto;
         * if (to < from) {
         *   ()
         * } else {
         *   i = to;
         *   function f(i) {
         *     int temp = i;
         *     if (to < i) {
         *       ()
         *     } else {
         *       ebody;
         *       f(temp + 1);
         *     }
         *   };
         *   f(from)
         * }
         *)
        let vfrom = "αfrom" in
        let vto = "αto" in
        let vtemp = "αtemp" in
        let fname = "λfor" in

        K.LETV (vfrom, efrom,
        K.LETV (vto, eto,
        K.IF (K.LESS (K.VAR vto, K.VAR vfrom),
          K.UNIT,
          K.SEQ (
          K.ASSIGN (i, K.VAR vto),
          K.LETF (
            fname, i,
            K.LETV (vtemp, K.VAR i,
              K.IF (K.LESS(K.VAR vto, K.VAR i),
                K.UNIT,
                K.SEQ (
                  ebody,
                  desugar (K.CALLV (fname, K.ADD (K.VAR vtemp, K.NUM 1)))
                )
              )
            ),
            desugar (K.CALLV (fname, efrom))
          )
          )
        )
        )
        )
      end
      | K.CALLV (name, eparam) -> begin
        let tempname = "β" in
        K.LETV (tempname, eparam, K.CALLR(name, tempname))
      end
      | _ -> input
    in
    match (desugar input) with
    | K.NUM i -> [Sm5.PUSH (Sm5.Val (Sm5.Z i))]
    | K.TRUE -> [Sm5.PUSH (Sm5.Val (Sm5.B true))]
    | K.FALSE -> [Sm5.PUSH (Sm5.Val (Sm5.B false))]
    | K.UNIT -> [Sm5.PUSH (Sm5.Val (Sm5.Unit))]
    | K.VAR name -> [Sm5.PUSH (Sm5.Id name); Sm5.LOAD]
    | K.ADD (e1, e2) -> trans e1 @ trans e2 @ [Sm5.ADD]
    | K.SUB (e1, e2) -> trans e1 @ trans e2 @ [Sm5.SUB]
    | K.MUL (e1, e2) -> trans e1 @ trans e2 @ [Sm5.MUL]
    | K.DIV (e1, e2) -> trans e1 @ trans e2 @ [Sm5.DIV]
    | K.EQUAL (e1, e2) -> trans e1 @ trans e2 @ [Sm5.EQ]
    | K.LESS (e1, e2) -> trans e1 @ trans e2 @ [Sm5.LESS]
    | K.NOT exp -> trans exp @ [Sm5.NOT]
    | K.ASSIGN (name, exp) -> begin
      trans exp @ [Sm5.PUSH (Sm5.Id name); Sm5.STORE] @
      [Sm5.PUSH (Sm5.Id name); Sm5.LOAD]
    end
    | K.SEQ (ebefore, eafter) -> trans ebefore @ [Sm5.POP] @ trans eafter
    | K.IF (econd, ethen, eelse) -> trans econd @ [Sm5.JTR (trans ethen, trans eelse)]
    | K.LETV (x, e1, e2) -> begin
      trans e1 @ [Sm5.MALLOC; Sm5.BIND x; Sm5.PUSH (Sm5.Id x); Sm5.STORE] @
      trans e2 @ [Sm5.UNBIND; Sm5.POP]
    end
    | K.LETF (name, param, ebody, eafter) -> begin
      [Sm5.PUSH (Sm5.Fn (param, [Sm5.BIND name] @ trans ebody)); Sm5.BIND name] @
      trans eafter @ [Sm5.UNBIND; Sm5.POP]
    end
    | K.CALLR (name, param) -> begin
      [Sm5.PUSH (Sm5.Id name)] @ (* 함수 스택 맨 위에 푸쉬 *)
      [Sm5.PUSH (Sm5.Id name)] @ (* 함수 Push *)
      [Sm5.PUSH (Sm5.Id param); Sm5.LOAD] @ (* Value Push *)
      [Sm5.PUSH (Sm5.Id param)] @ (* Location Push *)
      [Sm5.CALL] (* CALL *)
    end
    | K.READ x -> [Sm5.GET; Sm5.PUSH (Sm5.Id x); Sm5.STORE; Sm5.PUSH (Sm5.Id x); Sm5.LOAD]
    | K.WRITE exp -> begin
      let tempname = "α" in
      [Sm5.MALLOC; Sm5.BIND tempname] @ (* 변수 선언 *)
      trans exp @ [Sm5.PUSH (Sm5.Id tempname); Sm5.STORE] @ (* 임시변수에 값 대입 *)
      [Sm5.PUSH (Sm5.Id tempname); Sm5.LOAD; Sm5.PUT] @ (* 값 출력 *)
      [Sm5.PUSH (Sm5.Id tempname); Sm5.LOAD] @ (* 스택 맨 위에 값 저장 *)
      [Sm5.UNBIND; Sm5.POP] (* 임시변수 해제 *)
    end
    | K.WHILE _ | K.FOR _ | K.CALLV _ -> [] (* Unreachable! *)
end