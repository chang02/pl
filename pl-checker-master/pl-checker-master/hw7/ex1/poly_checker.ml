(*
 * SNU 4190.310 Programming Languages 2017 Fall
 * Type Checker Skeleton
 *)

open M

type var = string

type typ = 
  | TInt
  | TBool
  | TString
  | TWrite of var
  | TEq of var
  | TPair of typ * typ
  | TLoc of typ
  | TFun of typ * typ
  | TVar of var
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
  | TVar v | TWrite v | TEq v -> [v]

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
    | TEq x' | TWrite x' | TVar x' -> if (x = x') then t else t'
    | TPair (t1, t2) -> TPair (subs t1, subs t2)
    | TLoc t'' -> TLoc (subs t'')
    | TFun (t1, t2) -> TFun (subs t1, subs t2)
    | TInt | TBool | TString -> t'
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


(* TODO : Implement this function *)

let rec occurs (str: string) (t: typ) : bool =
  match t with
  | TVar x | TWrite x | TEq x -> str = x
  | TPair (t1, t2) -> occurs str t1 || occurs str t2
  | TLoc t' -> occurs str t'
  | TFun (t1, t2) -> occurs str t1 || occurs str t2
  | _ -> false

let rec unify (tt: typ * typ) : subst =
  match tt with
  | (TInt, TInt) | (TBool, TBool) | (TString, TString) -> empty_subst
  | (TVar x, TVar y)
  | (TVar x, TWrite y)
  | (TVar x, TEq y) -> if x = y then empty_subst else make_subst x (snd tt)
  | (TVar x, _) -> if occurs x (snd tt) then raise (M.TypeError "cannot occur") else make_subst x (snd tt)
  | (TEq x, TEq y)
  | (TEq x, TWrite y) -> if x = y then empty_subst else make_subst x (snd tt)
  | (TWrite x, TWrite y) -> if x = y then empty_subst else make_subst x (snd tt)
  | (TWrite x, TVar y)
  | (TWrite x, TEq y)
  | (TEq x, TVar y) -> if x = y then empty_subst else make_subst y (fst tt)
  | (_, TVar y) -> if occurs y (fst tt) then raise (M.TypeError "cannot occur") else make_subst y (fst tt)
  | (TPair (t1, t2), TPair (t1', t2')) ->
    let s = unify (t1, t1') in
    let s' = unify ((s t2), (s t2')) in
    s' @@ s
  | (TLoc t1, TLoc t2) -> unify (t1, t2)
  | (TFun (t1, t2), TFun (t1', t2')) ->
    let s = unify (t1, t1') in
    let s' = unify ((s t2), (s t2')) in
    s' @@ s
  | (TWrite x, TInt)
  | (TWrite x, TBool)
  | (TWrite x, TString)
  | (TEq x, TInt)
  | (TEq x, TBool)
  | (TEq x, TString) -> make_subst x (snd tt)
  | (TInt, TWrite y)
  | (TBool, TWrite y)
  | (TString, TWrite y)
  | (TInt, TEq y)
  | (TBool, TEq y)
  | (TString, TEq y) -> make_subst y (fst tt)
  | (TEq x, TLoc t2) -> if occurs x (snd tt) then raise (M.TypeError "cannot occur") else make_subst x (snd tt)
  | (TLoc t1, TEq y) -> if occurs y (fst tt) then raise (M.TypeError "cannot occur") else make_subst y (fst tt)
  | (_, _) -> raise (M.TypeError "cannot unify")

let rec typ_to_mtyp: typ -> M.typ = fun t ->
  match t with
  | TInt -> M.TyInt
  | TBool -> M.TyBool
  | TString -> M.TyString
  | TPair (t1, t2) -> M.TyPair(typ_to_mtyp t1, typ_to_mtyp t2)
  | TLoc t' -> M.TyLoc (typ_to_mtyp t')
  | _ -> raise (M.TypeError "Type not included in M")

let rec expansive (exp: M.exp) : bool =
  match exp with
  | M.CONST _ | M.VAR _ | M.FN _ | M.READ  -> false 
  | M.LET (M.REC (f, x, e), e') -> false
  | M.APP (e1, e2) -> true
  | M.MALLOC e -> true
  | M.IF (e1, e2, e3) -> expansive e1 || expansive e2 || expansive e3
  | M.BOP (_, e1, e2) -> expansive e1 || expansive e2
  | M.LET (M.VAL (x, e1), e2) -> expansive e1 || expansive e2
  | M.ASSIGN (e1, e2) | M.SEQ (e1, e2) | M.PAIR (e1, e2) -> expansive e1 || expansive e2
  | M.WRITE e | M.BANG e | M.FST e | M.SND e -> expansive e

let check  (exp: M.exp) : M.typ  =
  let rec eest ((env: typ_env), (exp: M.exp)) : subst * typ =
  match exp with
  | M.CONST const -> (
    match const with 
    | M.N n -> (empty_subst, TInt)
    | M.B b -> (empty_subst, TBool)
    | M.S str -> (empty_subst, TString)
    )
  | M.READ -> (empty_subst, TInt)
  | M.WRITE e ->
    let v = new_var() in
    let (s, t) = eest (env, e) in
    let s' = unify (t, (TWrite v)) in
    (s' @@ s, s' (TWrite v))
  | M.VAR x -> 
    if (List.mem_assoc x env) then
      begin
      let typscheme = List.assoc x env in 
      match typscheme with
      | SimpleTyp t -> (empty_subst, t)
      | GenTyp (a, t) ->
        let nextGen = subst_scheme empty_subst typscheme in
      	begin
      	  match nextGen with
      	  | SimpleTyp _ -> raise (M.TypeError "Cannot be SimpleTyp")
      	  | GenTyp (_, t') -> (empty_subst, t')
      	end
      end
    else
      raise (M.TypeError "Unbound variable")
  | M.PAIR (e1, e2) ->
    let (s1, t1) = eest (env, e1) in
    let (s2, t2) = eest (subst_env s1 env, e2) in
    (s2 @@ s1, TPair (s2 t1, t2))
  | M.FST e ->
    let v1 = new_var () in
    let v2 = new_var () in
    let (s, t) = eest (env, e) in
    let s' = unify (t, (TPair (TVar v1, TVar v2))) in
    (s' @@ s, s' (TVar v1))
  | M.SND e ->
    let v1 = new_var () in
    let v2 = new_var () in
    let (s, t) = eest (env, e) in
    let s' = unify (t, (TPair (TVar v1, TVar v2))) in
    (s' @@ s, s' (TVar v2))
  | M.FN (x, e) ->
    let v = new_var () in
    let (s, t) =  eest ((x, SimpleTyp (TVar v))::env, e)in
    (s, TFun (s (TVar v), t))
  | M.APP (e1, e2) ->
    let v = new_var () in
    let (s1, t1) = eest (env, e1) in
    let (s2, t2) = eest (subst_env s1 env, e2) in
    let s' = unify ((s2 t1), (TFun (t2, TVar v))) in
    (s' @@ s2 @@ s1, s' (TVar v))
  | M.LET (m, e') -> (
    match m with
    | M.VAL (x, e) ->
      let (s, t) = eest (env, e) in
      if (expansive e) then
        begin
      	let (s', t') = eest ((x, SimpleTyp t)::(subst_env s env), e') in
      	(s' @@ s, t')
      	end
      else
        begin
      	let (s', t') = eest ((x, generalize (subst_env s env) t)::(subst_env s env), e') in
      	(s' @@ s, t')
      	end
    | M.REC (f, x, e) ->
      let v = new_var () in
      let (s, t) = eest ((f, SimpleTyp (TVar v))::env, M.FN (x, e)) in
      let s' = unify ((s (TVar v)), t) in
      let (s'', t') = eest ((f, generalize (subst_env s env) (s' t))::(subst_env s env), e') in
      (s'' @@ s' @@ s, t')
    )
    
  | M.IF (ec, et, ef) ->
    let (sc, tc) = eest (env, ec) in
    let sc' = unify (tc, TBool) in
    let (st, tt) = eest (subst_env (sc' @@ sc) env, et) in
    let (sf, tf) = eest (subst_env (sc' @@ sc) env, ef) in
    let s' = unify (tt, tf) in
    (s' @@ sf @@ st @@ sc' @@ sc, tf)
  | M.BOP (m, e1, e2) -> (
     let (s1, t1) = eest (env, e1) in
     let (s2, t2) = eest (subst_env s1 env, e2) in
    match m with
    | M.EQ -> 
      let v = new_var () in
      let s' = unify ((s2 t1), t2) in
      let s'' = unify ((s' t2), (TEq v)) in
      (s'' @@ s' @@ s2 @@ s1, TBool)
    | M.ADD | M.SUB ->
      let s' = unify ((s2 t1), TInt) in
      let s'' = unify ((s' t2), TInt) in
      (s'' @@ s' @@ s2 @@ s1, s'' t2)
    | M.AND | M.OR ->
     let s' = unify ((s2 t1), TBool) in
     let s'' = unify ((s' t2), TBool) in
     (s'' @@ s' @@ s2 @@ s1, s'' t2)
     )
  | M.MALLOC e -> 
    let (s, t) = eest (env, e) in
    (s, TLoc t)
  | M.ASSIGN (e1, e2) ->
    let (s1, t1) = eest (env, e1) in
    let (s2, t2) = eest (subst_env s1 env, e2) in
    let s' = unify ((s2 t1), (TLoc t2)) in 
    (s' @@ s2 @@ s1, s' t2)
  | M.BANG e ->
    let v = new_var() in
    let (s, t) = eest (env, e) in
    let s' = unify (t, (TLoc (TVar v))) in
    (s' @@ s, (TVar v))
  | M.SEQ (e1, e2) ->
    let (s1, t1) = eest (env, e1) in
    let (s2, t2) = eest (subst_env s1 env, e2) in
    (s2 @@ s1, t2)
  in
  typ_to_mtyp (snd (eest ([], exp)))
