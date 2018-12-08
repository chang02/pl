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

type subst = typ -> typ

let empty_subst : subst = fun t -> t

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
  | TPrint v | TEqual v | TVar v -> [v]

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
let make_subst : var -> typ -> subst = fun x t ->
  let rec subs t' = 
    match t' with
    | TVar x' -> if (x = x') then t else t'
    | TPair (t1, t2) -> TPair (subs t1, subs t2)
    | TLoc t'' -> TLoc (subs t'')
    | TFun (t1, t2) -> TFun (subs t1, subs t2)
    | TInt | TBool | TString -> t'
    | TEqual x' -> (
      if (x' = x) 
      then ( match t with | TVar y -> TEqual y | _ -> t )
      else t')     
    | TPrint x' -> (
      if (x' = x) 
      then( match t with | TVar y | TEqual y -> TPrint y | _ -> t )
      else t')
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

(*****************************************************************************)
let rec occurs (v: var) (t: typ): bool = 
  match t with 
  | TInt | TBool | TString -> false
  | TLoc x -> occurs v x
  | TPair (x, y) -> occurs v x || occurs v y
  | TFun (x, y) -> occurs v x || occurs v y
  | TVar x | TEqual x | TPrint x -> (v = x)

let rec expansive (e: M.exp): bool = 
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

let rec unify (t1: typ) (t2: typ): subst =
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

let rec toMtype (t: typ) : M.typ =
  match t with
  | TInt -> M.TyInt
  | TBool -> M.TyBool
  | TString -> M.TyString
  | TPair (t1, t2) -> M.TyPair (toMtype t1, toMtype t2)
  | TLoc t1 -> M.TyLoc (toMtype t1)
  | _ -> raise (M.TypeError "Type Mismatch")

let find_operand x =
  let v1 = new_var() in
  match x with
  | M.ADD | M.SUB -> (TInt, TInt)
  | M.AND | M.OR -> (TBool, TBool)
  | M.EQ -> (TEqual v1, TBool)

let find_type (x: string) (env: typ_env): typ =
  if (List.mem_assoc x env)
  then (
    match List.assoc x env with 
    | SimpleTyp t -> t
    | GenTyp (alphas, t) -> (
        match (subst_scheme empty_subst (GenTyp (alphas, t))) with
        | GenTyp (_, t') -> t'
        | _ -> raise (M.TypeError "Type Mismatch")
    )
  )
  else raise (M.TypeError "Type Mismatch")  
  
let rec checkType (env: typ_env) (e: M.exp) (t: typ): subst =
  let v1 = new_var() in 
  let v2 = new_var() in
  match e with 
    | M.CONST M.S _ -> unify t TString
    | M.CONST M.N _ -> unify t TInt
    | M.CONST M.B _ -> unify t TBool
    | M.READ -> unify t TInt 
    | M.BANG x -> checkType env x (TLoc t)   
    | M.VAR x -> 
      let t' = find_type x env in
      unify t t'
    | M.FN (x, y) -> 
      let tmp_subst = unify t (TFun (TVar v1, TVar v2)) in
      let e' = subst_env tmp_subst env in 
      (checkType ([x, SimpleTyp (tmp_subst (TVar v1))] @ e') y (tmp_subst (TVar v2))) @@ tmp_subst
    | M.APP (x, y) -> 
      let tmp_subst = checkType env x (TFun (TVar v1, t)) in 
      let x' = tmp_subst (TVar v1) in
      let e' = subst_env tmp_subst env in 
      (checkType e' y x') @@ tmp_subst
    | M.LET (M.VAL (x, y), z) -> 
      begin
      let tmp_subst = checkType env y (TVar v1) in 
      let x' = tmp_subst (TVar v1) in 
      let e' = subst_env tmp_subst env in 
      let t' = tmp_subst t in 
      if (expansive y) 
      then (checkType ([x, SimpleTyp x'] @ e') z t') @@ tmp_subst
      else (checkType ([x, generalize e' x'] @ e') z t') @@ tmp_subst
      end 
    | M.LET (M.REC (w, x, y), z) -> 
      begin   
      let tmp_subst = checkType ([w, SimpleTyp (TVar v1)]@env) (M.FN (x, y)) (TVar v1) in 
      let x' = tmp_subst (TVar v1) in 
      let e' = subst_env tmp_subst env in 
      let t' = tmp_subst t in 
      let e'' = [w, generalize e' x'] @ e' in 
      (checkType e'' z t') @@ tmp_subst
      end
    | M.IF (x, y, z) -> 
      begin
      let tmp_subst = checkType env x TBool in 
      let e' = subst_env tmp_subst env in 
      let t' = tmp_subst t in 
      let tmp_subst2 = checkType e' y t' in 
      let e'' = subst_env tmp_subst2 e' in 
      let t'' = tmp_subst2 t' in 
      (checkType e'' z t'') @@ tmp_subst2 @@ tmp_subst
      end
    | M.BOP (x, y, z) -> 
      begin
      let ty = find_operand x in 
      let tmp_subst = unify t (snd ty) in 
      let x' = tmp_subst (fst ty) in 
      let e' = subst_env tmp_subst env in 
      let tmp_subst2 = checkType e' y x' in 
      let x'' = tmp_subst2 x' in 
      let e'' = subst_env tmp_subst2 e' in 
      (checkType e'' z x'') @@ tmp_subst2 @@ tmp_subst
      end
    | M.WRITE x -> 
      let tmp_subst = unify t (TPrint v1) in 
      let t' = tmp_subst t in 
      let e' = subst_env tmp_subst env in 
      (checkType e' x t') @@ tmp_subst
    | M.MALLOC x -> 
      let tmp_subst = checkType env x (TVar v1) in 
      let x' = tmp_subst (TVar v1) in 
      let t' = tmp_subst t in
      (unify t' (TLoc x')) @@ tmp_subst  
    | M.ASSIGN (x, y) -> 
      let tmp_subst = checkType env x (TLoc t) in 
      let e' = subst_env tmp_subst env in 
      let t' = tmp_subst t in
      (checkType e' y t') @@ tmp_subst
    | M.SEQ (x, y) ->
      let tmp_subst = checkType env x (TVar v1) in 
      let e' = subst_env tmp_subst env in 
      let t' = tmp_subst t in
      (checkType e' y t') @@ tmp_subst  
    | M.PAIR (x, y) ->
      let tmp_subst = unify t (TPair (TVar v1, TVar v2)) in 
      let x1 = tmp_subst (TVar v1) in 
      let x2 = tmp_subst (TVar v2) in 
      let e' = subst_env tmp_subst env in 
      let tmp_subst2 = (checkType e' x x1) in 
      let x3 = tmp_subst2 x2 in 
      let e'' = subst_env tmp_subst2 e' in 
      (checkType e'' y x3) @@ tmp_subst2 @@ tmp_subst
    | M.FST x -> 
      checkType env x (TPair (t, TVar v1))
    | M.SND x -> 
      checkType env x (TPair (TVar v1, t))

(* TODO : Implement this function *)

let check (e: M.exp): M.typ =
  let v = new_var() in 
  toMtype ((checkType [] e (TVar v)) (TVar v))
