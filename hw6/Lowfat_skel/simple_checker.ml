(*
 * SNU 4190.310 Programming Languages
 * Type Checker Skeleton Code
 *)

open M
open Pp

type var = string

let count = ref 0 

let new_var () = 
  let _ = count := !count +1 in
  "x_" ^ (string_of_int !count)

type typ = 
  | TInt
  | TBool
  | TString
  | TPair of typ * typ
  | TLoc of typ
  | TFun of typ * typ
  | TVar of var
  | TPrint of var
  | TEqual of var
  (* Modify, or add more if needed *)

type typ_scheme = SimpleTyp of typ
type typ_env = (M.id * typ_scheme) list

let union_ftv ftv_1 ftv_2 =
  let ftv_1' = List.filter (fun v -> not (List.mem v ftv_2)) ftv_1 in
  ftv_1' @ ftv_2

let sub_ftv ftv_1 ftv_2 =
  List.filter (fun v -> not (List.mem v ftv_2)) ftv_1

let rec ftv_of_typ : typ -> var list = function
  | TPair (t1, t2) -> union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TLoc t -> ftv_of_typ t
  | TFun (t1, t2) ->  union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TVar v | TPrint v | TEqual v -> [v]
  | _ -> []

let ftv_of_scheme : typ_scheme -> var list = function
  | SimpleTyp t -> ftv_of_typ t

let ftv_of_env : typ_env -> var list = fun tyenv ->
  List.fold_left
    (fun acc_ftv (id, tyscm) -> union_ftv acc_ftv (ftv_of_scheme tyscm))
    [] tyenv

let generalize : typ_env -> typ -> typ_scheme = fun tyenv t ->
    SimpleTyp t

type subst = typ -> typ
let empty_subst : subst = fun t -> t

let make_subst : var -> typ -> subst = fun x t ->
  let rec subs t' = 
    match t' with
    | TVar x'
    | TPrint x'
    | TEqual x' -> if (x = x') then t else t'
    | TPair (t1, t2) -> TPair (subs t1, subs t2)
    | TLoc t'' -> TLoc (subs t'')
    | TFun (t1, t2) -> TFun (subs t1, subs t2)
    | _ -> t'
  in subs

let subst_scheme : subst -> typ_scheme -> typ_scheme = fun subs tyscm ->
  match tyscm with
  | SimpleTyp t -> SimpleTyp (subs t)

let (@@) s1 s2 = (fun t -> s1 (s2 t))

let subst_env : subst -> typ_env -> typ_env = fun subs tyenv ->
  List.map (fun (x, tyscm) -> (x, subst_scheme subs tyscm)) tyenv

let rec occurs : var -> typ -> bool = fun v t -> 
  match t with 
  | TLoc x -> occurs v x
  | TPair (x, y) -> occurs v x || occurs v y
  | TFun (x, y) -> occurs v x || occurs v y
  | TVar x | TEqual x | TPrint x -> (v = x)
  | _-> false

let rec expansive : M.exp -> bool = fun e -> 
  match e with
  | M.CONST _ -> false
  | M.VAR _ -> false
  | M.FN _ -> false
  | M.READ -> false  
  | M.APP _ -> true
  | M.MALLOC _ -> true  
  | M.LET (M.VAL (x, e1), e2) -> expansive e1 || expansive e2
  | M.LET (M.REC (f, x, e1), e2) -> expansive e1 || expansive e2
  | M.IF (e1, e2, e3) -> expansive e1 || expansive e2 || expansive e3
  | M.BOP (_, e1, e2) -> expansive e1 || expansive e2
  | M.WRITE e1 -> expansive e1
  | M.ASSIGN (e1, e2) -> expansive e1 || expansive e2
  | M.BANG e1 -> expansive e1
  | M.SEQ (e1, e2) -> expansive e1 || expansive e2
  | M.PAIR (e1, e2) -> expansive e1 || expansive e2
  | M.FST e1 -> expansive e1
  | M.SND e1 -> expansive e1 

let rec unify : typ -> typ -> subst = fun t1 t2 ->
  if t1 = t2 then empty_subst else (
  begin
  match t1, t2 with
  | TVar x, y -> 
    if (not (occurs x y)) then make_subst x y else raise (M.TypeError "Type Mismatch")
  | y, TVar x ->
    if (not (occurs x y)) then make_subst x y else raise (M.TypeError "Type Mismatch")
  | TLoc x, TLoc y -> unify x y
  | TPair(w, x), TPair(y, z) ->
    let tmp_subst = unify w y in
    (unify (tmp_subst x) (tmp_subst z)) @@ tmp_subst
  | TFun(w, x), TFun(y, z) -> 
    let tmp_subst = unify w y in
    (unify (tmp_subst x) (tmp_subst z)) @@ tmp_subst
  | TEqual x, y | y, TEqual x -> (
    begin
    if (occurs x y) then raise (M.TypeError "Type Mismatch") else
    (
      match y with
      | TPair _ | TFun _ | TVar _ -> 
        raise (M.TypeError "Type Mismatch")
      | _ -> make_subst x y 
    ) 
    end)
  | TPrint x, y | y, TPrint x -> (
    begin
    if (occurs x y) then raise (M.TypeError "Type Mismatch") else
    (
      match y with
      | TInt | TBool | TString | TPrint _ -> make_subst x y
      | _ -> raise (M.TypeError "Type Mismatch")
    )
    end)
  | _ -> raise (M.TypeError "Type Mismatch")
  end
  )

let rec check1 : typ_env * M.exp -> (subst * typ) = fun (env, exp) ->
  match exp with
  | M.CONST (M.S s) -> (empty_subst, TString)
  | M.CONST (M.N n) -> (empty_subst, TInt)
  | M.CONST (M.B b) -> (empty_subst, TBool)
  | M.VAR id ->
    if (List.mem_assoc id env)
    then let (SimpleTyp t) = List.assoc id env in (empty_subst, t)
    else raise (M.TypeError "Unbound variable")
  | M.FN (x, e) ->
    let a = new_var () in
    let (s, t) = check1((x, SimpleTyp (TVar a))::env, e) in
    (s, TFun (s (TVar a), t))
  | M.APP (e1, e2) ->
    let a = new_var () in
    let (s, t) = check1 (env, e1) in
    let (s', t') = check1 (subst_env s env, e2) in
    let s'' = unify (s' t) (TFun (t', TVar a)) in
    (s'' @@ s' @@ s, s'' (TVar a))
  | M.LET (M.VAL (x, e), e') ->
    let (s, t) = check1 (env, e) in
    if expansive(e)
    then let (s', t') = check1 ((x, SimpleTyp t)::(subst_env s env), e') in (s' @@ s, t')
    else let (s', t') = check1 ((x, generalize (subst_env s env) t)::(subst_env s env), e') in (s' @@ s, t')
  | M.LET (M.REC (f, x, e), e') ->
    let a = new_var () in
    let (s, t) = check1 ((f, SimpleTyp (TVar a))::env, M.FN (x, e)) in
    let s' = unify (s (TVar a)) t in
    let (s'', t') = check1 ((f, generalize (subst_env s env) (s' t))::(subst_env s env), e') in
    (s'' @@ s' @@ s, t')
  | M.IF (e1, e2, e3) ->
    let (s, t) = check1 (env, e1) in
    let s' = unify t TBool in
    let (s1, t1) = check1 (subst_env (s' @@ s) env, e2) in
    let (s2, t2) = check1 (subst_env (s' @@ s) env, e3) in
    let s'' = unify t1 t2 in
    (s'' @@ s2 @@ s1 @@ s' @@ s, t2)
  | M.BOP (b, e1, e2) ->
    (match b with
    | M.ADD | M.SUB ->
      let (s, t) = check1 (env, e1) in
      let (s', t') = check1 (subst_env s env, e2) in
      let s1 = unify (s' t) TInt in
      let s2 = unify (s1 t') TInt in
      (s2 @@ s1 @@ s' @@ s, s2 t')
    | M.AND | M.OR ->
      let (s, t) = check1 (env, e1) in
      let (s', t') = check1 (subst_env s env, e2) in
      let s1 = unify (s' t) TBool in
      let s2 = unify t' TBool in
      (s2 @@ s1 @@ s' @@ s, s2 t')
    | M.EQ ->
      let (s, t) = check1 (env, e1) in
      let (s', t') = check1 (subst_env s env, e2) in
      let v = new_var () in
      let s1 = unify (s' t) t' in
      let s2 = unify (s1 t') (TEqual v) in
      (s2 @@ s1 @@ s' @@ s, TBool)
    )
  | M.READ -> (empty_subst, TInt)
  | M.WRITE e ->
    let (s, t) = check1 (env, e) in
    let v = new_var () in
    let s' = unify t (TPrint v) in
    (s' @@ s, s' (TPrint v))
  | M.MALLOC e ->
    let (s, t) = check1 (env, e) in
    (s, TLoc t)
  | M.ASSIGN (e1, e2) ->
    let (s, t) = check1 (env, e1) in
    let (s', t') = check1 (subst_env s env, e2) in
    let s'' = unify (s' t) (TLoc t') in
    (s'' @@ s' @@ s, s'' t')
  | M.BANG e ->
    let (s, t) = check1 (env, e) in
    let v = new_var () in
    let s' = unify t (TLoc (TVar v)) in
    (s' @@ s, s' (TVar v))
  | M.SEQ (e1, e2) ->
    let (s, t) = check1 (env, e1) in
    let (s', t') = check1 (subst_env s env, e2) in
    (s' @@ s, t')
  | M.PAIR (e1, e2) ->
    let (s, t) = check1 (env, e1) in
    let (s', t') = check1 (subst_env s env, e2) in
    (s' @@ s, TPair (s' t, t'))
  | M.FST e ->
    let (s, t) = check1 (env, e) in
    let v1 = new_var () in
    let v2 = new_var () in
    let s' = unify t (TPair (TVar v1, TVar v2)) in
    (s' @@ s, s' (TVar v1))
  | M.SND e ->
    let (s, t) = check1 (env, e) in
    let v1 = new_var () in
    let v2 = new_var () in
    let s' = unify t (TPair (TVar v1, TVar v2)) in
    (s' @@ s, s' (TVar v2))


let rec check2 : typ -> M.types = fun tp ->
  match tp with
  | TInt -> M.TyInt
  | TBool -> M.TyBool
  | TString -> M.TyString
  | TPair (t1, t2) -> M.TyPair (check2 t1, check2 t2)
  | TLoc t1 -> M.TyLoc (check2 t1)
  | _ -> raise (M.TypeError "Type Mismatch")


(* TODO : Implement this function *)
let check : M.exp -> M.types = fun exp ->
  let (_, t) = check1 ([], exp) in
  check2 t
