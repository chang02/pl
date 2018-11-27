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


type typ_env = (M.id * typ) list
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
    | TInt | TBool | TString -> t'
  in subs

let (@@) s1 s2 = (fun t -> s1 (s2 t))

let subst_env : subst -> typ_env -> typ_env = fun subs tyenv ->
  List.map (fun (x, t) -> (x, subs t)) tyenv


let rec occurs : var -> typ -> bool = fun v t -> 
  match t with 
  | TLoc x -> occurs v x
  | TPair (x, y) -> occurs v x || occurs v y
  | TFun (x, y) -> occurs v x || occurs v y
  | TVar x | TEqual x | TPrint x -> (v = x)
  | _-> false


let rec unify : typ -> typ -> subst = fun t1 t2 ->
  if t1 = t2 then empty_subst
  else (
    match t1, t2 with
    | TVar x, y | y, TVar x-> 
      if (occurs x y) then raise (M.TypeError "Type Mismatch") else make_subst x y
    | TLoc x, TLoc y -> unify x y
    | TPair(x, y), TPair(z, w) | TFun(x, y), TFun(z, w) ->
      let tmp = unify x z in
      let tmp2 = (unify (tmp y) (tmp w)) in
      tmp2 @@ tmp
    | TEqual x, y | y, TEqual x -> 
      if (occurs x y) then raise (M.TypeError "Type Mismatch")
      else (
        match y with
        | TPair _ | TFun _ | TVar _ -> raise (M.TypeError "Type Mismatch")
        | _ -> make_subst x y 
      ) 
    | TPrint x, y | y, TPrint x -> 
      if (occurs x y) then raise (M.TypeError "Type Mismatch")
      else (
        match y with
        | TInt | TBool | TString | TPrint _ -> make_subst x y
        | _ -> raise (M.TypeError "Type Mismatch")
      )
    | _ -> raise (M.TypeError "Type Mismatch")
  )

let isExistId id env =
  let (a, b) = List.split env in
  if List.mem id a then true else false

let rec check1 : typ_env * M.exp -> (subst * typ) = fun (env, exp) ->
  match exp with
  | M.CONST (M.S s) -> (empty_subst, TString)
  | M.CONST (M.N n) -> (empty_subst, TInt)
  | M.CONST (M.B b) -> (empty_subst, TBool)
  | M.VAR id ->
    if (isExistId id env)
    then let t = List.assoc id env in (empty_subst, t)
    else raise (M.TypeError "Unbound variable")
  | M.FN (x, e) ->
    let v = TVar (new_var ()) in
    let (s, t) = check1((x, v)::env, e) in
    (s, TFun (s v, t))
  | M.APP (e1, e2) ->
    let v = TVar (new_var ()) in
    let (s, t) = check1 (env, e1) in
    let (s', t') = check1 (subst_env s env, e2) in
    let s'' = unify (s' t) (TFun (t', v)) in
    (s'' @@ s' @@ s, s'' v)
  | M.LET (M.VAL (x, e), e') ->
    let (s, t) = check1 (env, e) in
    let (s', t') = check1 ((x, t)::(subst_env s env), e') in
    (s' @@ s, t')
  | M.LET (M.REC (f, x, e), e') ->
    let v = TVar (new_var ()) in
    let (s, t) = check1 ((f, v)::env, M.FN (x, e)) in
    let s' = unify (s v) t in
    let (s'', t') = check1 ((f, s' t)::(subst_env s env), e') in
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
      let v = TEqual (new_var ()) in
      let s1 = unify (s' t) t' in
      let s2 = unify (s1 t') v in
      (s2 @@ s1 @@ s' @@ s, TBool)
    )
  | M.READ -> (empty_subst, TInt)
  | M.WRITE e ->
    let (s, t) = check1 (env, e) in
    let v = TPrint (new_var ()) in
    let s' = unify t v in
    (s' @@ s, s' v)
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
    let v = TVar (new_var ()) in
    let s' = unify t (TLoc v) in
    (s' @@ s, s' v)
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
    let v1 = TVar (new_var ()) in
    let v2 = TVar (new_var ()) in
    let s' = unify t (TPair (v1, v2)) in
    (s' @@ s, s' v1)
  | M.SND e ->
    let (s, t) = check1 (env, e) in
    let v1 = TVar (new_var ()) in
    let v2 = TVar (new_var ()) in
    let s' = unify t (TPair (v1, v2)) in
    (s' @@ s, s' v2)


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
