(*
 * SNU 4190.310 Programming Languages
 * Type Checker Skeleton
 *)

open M

type var = string

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

type typ_scheme =
  | SimpleTyp of typ 
  | GenTyp of (var list * typ)

type typ_env = (M.id * typ_scheme) list

let count = ref 0 

let new_var () = 
  let _ = count := !count +1 in
  "x_" ^ (string_of_int !count)

(* Definitions related to free type variable *)

let union_ftv ftv_1 ftv_2 = 
  let ftv_1' = List.filter (fun v -> not (List.mem v ftv_2)) ftv_1 in
  ftv_1' @ ftv_2
  
let sub_ftv ftv_1 ftv_2 =
  List.filter (fun v -> not (List.mem v ftv_2)) ftv_1

let rec ftv_of_typ : typ -> var list = function
  | TInt | TBool | TString -> []
  | TPair (t1, t2) -> union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TLoc t -> ftv_of_typ t
  | TFun (t1, t2) ->  union_ftv (ftv_of_typ t1) (ftv_of_typ t2)
  | TVar v -> [v]
  | TPrint v -> [v]
  | TEqual v -> [v]

let ftv_of_scheme : typ_scheme -> var list = function
  | SimpleTyp t -> ftv_of_typ t
  | GenTyp (alphas, t) -> sub_ftv (ftv_of_typ t) alphas 

let ftv_of_env : typ_env -> var list = fun tyenv ->
  List.fold_left 
    (fun acc_ftv (id, tyscm) -> union_ftv acc_ftv (ftv_of_scheme tyscm))
    [] tyenv 

(* Generalize given type into a type scheme *)
let generalize : typ_env -> typ -> typ_scheme = fun tyenv t ->
  let env_ftv = ftv_of_env tyenv in
  let typ_ftv = ftv_of_typ t in
  let ftv = sub_ftv typ_ftv env_ftv in
  if List.length ftv = 0 then
    SimpleTyp t
  else
    GenTyp(ftv, t)

(* Definitions related to substitution *)

type subst = typ -> typ

let empty_subst : subst = fun t -> t

let make_subst : var -> typ -> subst = fun x t ->
  let rec subs t' = 
    match t' with
    | TVar x' -> if (x = x') then t else t'
    | TPair (t1, t2) -> TPair (subs t1, subs t2)
    | TLoc t'' -> TLoc (subs t'')
    | TFun (t1, t2) -> TFun (subs t1, subs t2)
    | TInt | TBool | TString -> t'
    | TPrint x' -> 
      (match t with
      | TVar y -> TEqual y
      | _ -> t)
    | TEqual x' ->
      (match t with
      | TVar y | TEqual y -> TPrint y
      | _ -> t
      )
  in subs

let (@@) s1 s2 = (fun t -> s1 (s2 t)) (* substitution composition *)

let subst_scheme : subst -> typ_scheme -> typ_scheme = fun subs tyscm ->
  match tyscm with
  | SimpleTyp t -> SimpleTyp (subs t)
  | GenTyp (alphas, t) ->
    (* S (\all a.t) = \all b.S{a->b}t  (where b is new variable) *)
    let betas = List.map (fun _ -> new_var()) alphas in
    let s' =
      List.fold_left2
        (fun acc_subst alpha beta -> make_subst alpha (TVar beta) @@ acc_subst)
        empty_subst alphas betas
    in
    GenTyp (betas, subs (s' t))

let subst_env : subst -> typ_env -> typ_env = fun subs tyenv ->
  List.map (fun (x, tyscm) -> (x, subst_scheme subs tyscm)) tyenv

let rec expansive : M.exp -> bool = fun exp ->
  match exp with
  | M.CONST _ | M.VAR _ | M.FN _ | M.READ -> false
  | M.APP _ | M.MALLOC _ -> true
  | M.LET (M.VAL (_, e1), e2) | M.LET (M.REC (_, _, e1), e2) -> expansive e1 || expansive e2
  | M.IF (e1, e2, e3) -> expansive e1 || expansive e2 || expansive e3
  | M.BOP (_, e1, e2) | M.ASSIGN (e1, e2) | M.SEQ (e1, e2) | M.PAIR (e1, e2) -> expansive e1 || expansive e2
  | M.BANG e1 | M.WRITE e1 | M.FST e1 | M.SND e1 -> expansive e1

let rec occurs : var -> typ -> bool = fun v t -> 
  match t with 
  | TLoc x -> occurs v x
  | TPair (x, y) -> occurs v x || occurs v y
  | TFun (x, y) -> occurs v x || occurs v y
  | TVar x | TEqual x | TPrint x -> if (v = x) then true else false
  | _-> false

let rec unify : typ -> typ -> subst = fun t1 t2 ->
  if t1 = t2 then empty_subst
  else (
    match t1, t2 with
    | TVar x, y -> 
      if (occurs x y) then raise (M.TypeError "Type Mismatch") else make_subst x y
    | x, TVar y ->
      if (occurs y x) then raise (M.TypeError "Type Mismatch") else make_subst y x 
    | TLoc x, TLoc y -> unify x y
    | TPair(x, y), TPair(z, w) | TFun(x, y), TFun(z, w) ->
      let tmp = unify x z in
      let tmp2 = (unify (tmp y) (tmp w)) in
      tmp2 @@ tmp
    | TEqual x, y -> 
      if (occurs x y) then raise (M.TypeError "Type Mismatch")
      else (
        match y with
        | TPair _ | TFun _ | TVar _ -> raise (M.TypeError "Type Mismatch")
        | _ -> make_subst x y 
      )
    | x, TEqual y ->
      if (occurs y x) then raise (M.TypeError "Type Mismatch")
      else (
        match x with
        | TPair _ | TFun _ | TVar _ -> raise (M.TypeError "Type Mismatch")
        | _ -> make_subst y x 
      )
    | TPrint x, y -> 
      if (occurs x y) then raise (M.TypeError "Type Mismatch")
      else (
        match y with
        | TInt | TBool | TString | TPrint _ -> make_subst x y
        | _ -> raise (M.TypeError "Type Mismatch")
      )
    | x, TPrint y ->
      if (occurs y x) then raise (M.TypeError "Type Mismatch")
      else (
        match x with
        | TInt | TBool | TString | TPrint _ -> make_subst y x
        | _ -> raise (M.TypeError "Type Mismatch")
      )
    | _ -> raise (M.TypeError "Type Mismatch")
  )

let rec check1 : M.exp -> typ = fun e ->
  let rec check1' : typ_env -> M.exp -> (subst * typ) = fun env exp ->
    (match exp with
    | M.CONST (M.S s) -> (empty_subst, TString)
    | M.CONST (M.N n) -> (empty_subst, TInt)
    | M.CONST (M.B b) -> (empty_subst, TBool)
    | M.VAR id -> 
      let rec findById id env =
        (match env with
        | [] -> raise (M.TypeError "Unbound variable")
        | hd::tl -> if (fst hd) = id then (snd hd) else findById id tl)
      in
      let t = findById id env in
      (match t with
      | SimpleTyp t -> (empty_subst, t)
      | GenTyp (_, t) ->
        let GenTyp (_, t') = subst_scheme empty_subst t in
        (empty_subst, t'))
    | M.FN (x, e) ->
      let v = TVar (new_var ()) in
      let (s, t) = check1'((x, SimpleTyp v)::env, e) in
      (s, TFun (s v, t))
    | M.APP (e1, e2) ->
      let v = TVar (new_var ()) in
      let (s, t) = check1' (env, e1) in
      let (s', t') = check1' (subst_env s env, e2) in
      let s'' = unify (s' t) (TFun (t', v)) in
      (s'' @@ s' @@ s, s'' v)
    | M.LET (M.VAL (x, e1), e2) ->
      let (s1, t1) = check1' (env, e1) in
      let (s2, t2) = 
        (if (expansive e1)
        then check1' ((x, SimpleTyp t1)::(subst_env s1 env), e2)
        else check1' ((x, generalize (subst_env s1 env) t1)::(subst_env s1 env), e2))
      in
      (s2 @@ s1, t2)
    | M.LET (M.REC (f, x, e1), e2) ->
      let v = TVar (new_var ()) in
      let (s1, t1) = check1' ((f, SimpleTyp v)::env, M.FN (x, e1)) in
      let s' = unify (s1 v) t1 in
      let (s2, t2) = check1' ((f, generalize (subst_env s env) (s' t1))::(subst_env s1 env), e2) in
      (s2 @@ s' @@ s1, t2)
    | M.IF (e1, e2, e3) ->
      let (s1, t1) = check1' (env, e1) in
      let s' = unify t1 TBool in
      let (s2, t2) = check1' (subst_env (s' @@ s1) env, e2) in
      let (s3, t3) = check1' (subst_env (s' @@ s1) env, e3) in
      let s'' = unify t2 t3 in
      (s'' @@ s3 @@ s2 @@ s' @@ s1, t3)
    | M.BOP (b, e1, e2) ->
      (match b with
      | M.ADD | M.SUB ->
        let (s, t) = check1' (env, e1) in
        let (s', t') = check1' (subst_env s env, e2) in
        let s1 = unify (s' t) TInt in
        let s2 = unify (s1 t') TInt in
        (s2 @@ s1 @@ s' @@ s, s2 t')
      | M.AND | M.OR ->
        let (s, t) = check1' (env, e1) in
        let (s', t') = check1' (subst_env s env, e2) in
        let s1 = unify (s' t) TBool in
        let s2 = unify t' TBool in
        (s2 @@ s1 @@ s' @@ s, s2 t')
      | M.EQ ->
        let (s, t) = check1' (env, e1) in
        let (s', t') = check1' (subst_env s env, e2) in
        let v = TEqual (new_var ()) in
        let s1 = unify (s' t) t' in
        let s2 = unify (s1 t') v in
        (s2 @@ s1 @@ s' @@ s, TBool)
      )
    | M.READ -> (empty_subst, TInt)
    | M.WRITE e ->
      let (s, t) = check1' (env, e) in
      let v = TPrint (new_var ()) in
      let s' = unify t v in
      (s' @@ s, s' v)
    | M.MALLOC e ->
      let (s, t) = check1' (env, e) in
      (s, TLoc t)
    | M.ASSIGN (e1, e2) ->
      let (s, t) = check1' (env, e1) in
      let (s', t') = check1' (subst_env s env, e2) in
      let s'' = unify (s' t) (TLoc t') in
      (s'' @@ s' @@ s, s'' t')
    | M.BANG e ->
      let (s, t) = check1' (env, e) in
      let v = TVar (new_var ()) in
      let s' = unify t (TLoc v) in
      (s' @@ s, s' v)
    | M.SEQ (e1, e2) ->
      let (s, t) = check1' (env, e1) in
      let (s', t') = check1' (subst_env s env, e2) in
      (s' @@ s, t')
    | M.PAIR (e1, e2) ->
      let (s, t) = check1' (env, e1) in
      let (s', t') = check1' (subst_env s env, e2) in
      (s' @@ s, TPair (s' t, t'))
    | M.FST e ->
      let (s, t) = check1' (env, e) in
      let v1 = TVar (new_var ()) in
      let v2 = TVar (new_var ()) in
      let s' = unify t (TPair (v1, v2)) in
      (s' @@ s, s' v1)
    | M.SND e ->
      let (s, t) = check1' (env, e) in
      let v1 = TVar (new_var ()) in
      let v2 = TVar (new_var ()) in
      let s' = unify t (TPair (v1, v2)) in
      (s' @@ s, s' v2)
    )
  in
  snd (check1' [] e)


let rec check2 : typ -> M.types = fun tp ->
  match tp with
  | TInt -> M.TyInt
  | TBool -> M.TyBool
  | TString -> M.TyString
  | TPair (t1, t2) -> M.TyPair (check2 t1, check2 t2)
  | TLoc t1 -> M.TyLoc (check2 t1)
  | _ -> raise (M.TypeError "Type Mismatch")

let check : M.exp -> M.typ = fun exp ->
  check2 (check1 exp)
