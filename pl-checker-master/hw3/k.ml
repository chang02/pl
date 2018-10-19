(*
 * SNU 4190.310 Programming Languages 2018 Fall
 *  K- Interpreter Skeleton Code
 *)

(* Location Signature *)
module type LOC =
sig
  type t
  val base : t
  val equal : t -> t -> bool
  val diff : t -> t -> int
  val increase : t -> int -> t
end

module Loc : LOC =
struct
  type t = Location of int
  let base = Location(0)
  let equal (Location(a)) (Location(b)) = (a = b)
  let diff (Location(a)) (Location(b)) = a - b
  let increase (Location(base)) n = Location(base+n)
end

(* Memory Signature *)
module type MEM = 
sig
  type 'a t
  exception Not_allocated
  exception Not_initialized
  val empty : 'a t (* get empty memory *)
  val load : 'a t -> Loc.t  -> 'a (* load value : Mem.load mem loc => value *)
  val store : 'a t -> Loc.t -> 'a -> 'a t (* save value : Mem.store mem loc value => mem' *)
  val alloc : 'a t -> Loc.t * 'a t (* get fresh memory cell : Mem.alloc mem => (loc, mem') *)
end

(* Environment Signature *)
module type ENV =
sig
  type ('a, 'b) t
  exception Not_bound
  val empty : ('a, 'b) t (* get empty environment *)
  val lookup : ('a, 'b) t -> 'a -> 'b (* lookup environment : Env.lookup env key => content *)
  val bind : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) t  (* id binding : Env.bind env key content => env'*)
end

(* Memory Implementation *)
module Mem : MEM =
struct
  exception Not_allocated
  exception Not_initialized
  type 'a content = V of 'a | U
  type 'a t = M of Loc.t * 'a content list
  let empty = M (Loc.base,[])

  let rec replace_nth = fun l n c -> 
    match l with
    | h::t -> if n = 1 then c :: t else h :: (replace_nth t (n - 1) c)
    | [] -> raise Not_allocated

  let load (M (boundary,storage)) loc =
    match (List.nth storage ((Loc.diff boundary loc) - 1)) with
    | V v -> v 
    | U -> raise Not_initialized

  let store (M (boundary,storage)) loc content =
    M (boundary, replace_nth storage (Loc.diff boundary loc) (V content))

  let alloc (M (boundary,storage)) = 
    (boundary, M (Loc.increase boundary 1, U :: storage))
end

(* Environment Implementation *)
module Env : ENV=
struct
  exception Not_bound
  type ('a, 'b) t = E of ('a -> 'b)
  let empty = E (fun x -> raise Not_bound)
  let lookup (E (env)) id = env id
  let bind (E (env)) id loc = E (fun x -> if x = id then loc else env x)
end

(*
 * K- Interpreter
 *)
module type KMINUS =
sig
  exception Error of string
  type id = string
  type exp =
    | NUM of int | TRUE | FALSE | UNIT
    | VAR of id
    | ADD of exp * exp
    | SUB of exp * exp
    | MUL of exp * exp
    | DIV of exp * exp
    | EQUAL of exp * exp
    | LESS of exp * exp
    | NOT of exp
    | SEQ of exp * exp            (* sequence *)
    | IF of exp * exp * exp       (* if-then-else *)
    | WHILE of exp * exp          (* while loop *)
    | LETV of id * exp * exp      (* variable binding *)
    | LETF of id * id list * exp * exp (* procedure binding *)
    | CALLV of id * exp list      (* call by value *)
    | CALLR of id * id list       (* call by referenece *)
    | RECORD of (id * exp) list   (* record construction *)
    | FIELD of exp * id           (* access record field *)
    | ASSIGN of id * exp          (* assgin to variable *)
    | ASSIGNF of exp * id * exp   (* assign to record field *)
    | READ of id
    | WRITE of exp
    
  type program = exp
  type memory
  type env
  type value =
    | Num of int
    | Bool of bool
    | Unit
    | Record of (id -> Loc.t)
  val emptyMemory : memory
  val emptyEnv : env
  val run : memory * env * program -> value
end

module K : KMINUS =
struct
  exception Error of string

  type id = string
  type exp =
    | NUM of int | TRUE | FALSE | UNIT
    | VAR of id
    | ADD of exp * exp
    | SUB of exp * exp
    | MUL of exp * exp
    | DIV of exp * exp
    | EQUAL of exp * exp
    | LESS of exp * exp
    | NOT of exp
    | SEQ of exp * exp            (* sequence *)
    | IF of exp * exp * exp       (* if-then-else *)
    | WHILE of exp * exp          (* while loop *)
    | LETV of id * exp * exp      (* variable binding *)
    | LETF of id * id list * exp * exp (* procedure binding *)
    | CALLV of id * exp list      (* call by value *)
    | CALLR of id * id list       (* call by referenece *)
    | RECORD of (id * exp) list   (* record construction *)
    | FIELD of exp * id           (* access record field *)
    | ASSIGN of id * exp          (* assgin to variable *)
    | ASSIGNF of exp * id * exp   (* assign to record field *)
    | READ of id
    | WRITE of exp

  type program = exp

  type value =
    | Num of int
    | Bool of bool
    | Unit
    | Record of (id -> Loc.t)
    
  type memory = value Mem.t
  type env = (id, env_entry) Env.t
  and  env_entry = Addr of Loc.t | Proc of id list * exp * env

  let emptyMemory = Mem.empty
  let emptyEnv = Env.empty

  let value_int v =
    match v with
    | Num n -> n
    | _ -> raise (Error "TypeError : not int")

  let value_bool v =
    match v with
    | Bool b -> b
    | _ -> raise (Error "TypeError : not bool")

  let value_unit v =
    match v with
    | Unit -> ()
    | _ -> raise (Error "TypeError : not unit")

  let value_record v =
    match v with
    | Record r -> r
    | _ -> raise (Error "TypeError : not record")

  let lookup_env_loc e x =
    try
      (match Env.lookup e x with
      | Addr l -> l
      | Proc _ -> raise (Error "TypeError : not addr")) 
    with Env.Not_bound -> raise (Error "Unbound")

  let lookup_env_proc e f =
    try
      (match Env.lookup e f with
      | Addr _ -> raise (Error "TypeError : not proc") 
      | Proc (id_list, exp, env) -> (id_list, exp, env))
    with Env.Not_bound -> raise (Error "Unbound")

  let rec eval mem env e =
    match e with
    | READ x -> 
      let v = Num (read_int()) in
      let l = lookup_env_loc env x in
      (v, Mem.store mem l v)
    | WRITE e ->
      let (v, mem') = eval mem env e in
      let n = value_int v in
      let _ = print_endline (string_of_int n) in
      (v, mem')
    | LETV (x, e1, e2) ->
      let (v, mem') = eval mem env e1 in
      let (l, mem'') = Mem.alloc mem' in
      eval (Mem.store mem'' l v) (Env.bind env x (Addr l)) e2
    | NUM (n) -> (Num n, mem)
    | TRUE -> (Bool true, mem)
    | FALSE -> (Bool false, mem)
    | UNIT -> (Unit, mem)
    | VAR (i) -> ((Mem.load mem (lookup_env_loc env i)), mem)
    | ADD (e1, e2) ->
      let (n1, mem') = eval mem env e1 in
      let (n2, mem'') = eval mem' env e2 in
      (Num ((value_int n1) + (value_int n2)), mem'')
    | SUB (e1, e2) ->
      let (n1, mem') = eval mem env e1 in
      let (n2, mem'') = eval mem' env e2 in
      (Num ((value_int n1) - (value_int n2)), mem'')
    | MUL (e1, e2) ->
      let (n1, mem') = eval mem env e1 in
      let (n2, mem'') = eval mem' env e2 in
      (Num ((value_int n1) * (value_int n2)), mem'')
    | DIV (e1, e2) ->
      let (n1, mem') = eval mem env e1 in
      let (n2, mem'') = eval mem' env e2 in
      (Num ((value_int n1) / (value_int n2)), mem'')
    | EQUAL (e1, e2) ->
      let (v1, mem') = eval mem env e1 in
      let (v2, mem'') = eval mem' env e2 in
      ((Bool (v1 = v2)), mem'')
    | LESS (e1, e2) ->
      let (n1, mem') = eval mem env e1 in
      let (n2, mem'') = eval mem' env e2 in
      (match (n1, n2) with
      | (Num n1, Num n2) -> ((Bool (n1 < n2)), mem'')
      | _ -> raise (Error "TypeError : not int")
      )
    | NOT (e1) ->
      let (b, mem') = eval mem env e1 in
      ((Bool (not (value_bool b))), mem')
    | SEQ (e1, e2) ->
      let (v1, mem') = eval mem env e1 in
      let (v2, mem'') = eval mem' env e2 in
      (v2, mem'')
    | IF (e, e1, e2) ->
      let (v1, mem') = eval mem env e in
      (match v1 with
      | Bool true -> 
        let (v1, mem'') = eval mem' env e1 in
        (v1, mem'')
      | Bool false ->
        let (v2, mem'') = eval mem' env e2 in
        (v2, mem'')
      | _ -> raise (Error "Unbound")
      )
    | WHILE (e, e1) ->
      let (v, mem') = eval mem env e in
      (match v with
      | Bool true ->
        let (v1, mem1) = eval mem' env e1 in
        let (v2, mem2) = eval mem1 env (WHILE (e, e1)) in
        (v2, mem2)
      | Bool false -> (Unit, mem')
      | _ -> raise (Error "Unbound")
      )
    | LETF (id, idl, e1, e2) ->
      let env' = Env.bind env id (Proc (idl, e1, env)) in
      eval mem env' e2
    | CALLV (id, el) ->
      let (xl, e', env') = lookup_env_proc env id in
      let rec getMn f_el f_mem f_env =
        (match f_el with
        | [] -> f_mem
        | head::tail -> (let (tmp_v, tmp_mem) = eval f_mem f_env head in getMn tail tmp_mem f_env)
        )
      in
      let rec getVlist f_el f_mem f_env =
        (match f_el with
        | [] -> []
        | head::tail -> (let (tmp_v, tmp_mem) = eval f_mem f_env head in [tmp_v] @ getVlist tail tmp_mem f_env)
        )
      in
      let rec get_env_mem f_env f_mem f_vl f_xl= 
        (match f_vl with
        | [] -> if f_xl=[] then (f_env, f_mem) else raise (Error "InvalidArg")
        | head::tail -> if f_xl=[] then raise (Error "InvalidArg")
                        else
                        (let (l, temp_mem) = Mem.alloc f_mem in
                        let temp_mem = Mem.store temp_mem l head in
                        let temp_env = Env.bind f_env (List.hd f_xl) (Addr l) in
                        get_env_mem temp_env temp_mem tail (List.tl f_xl)
                        )
        )
      in
      let mn = getMn el mem env in
      let vl = getVlist el mem env in
      let (env'', mem'') = get_env_mem env' mn vl xl in
      let env'' = Env.bind env'' id (Proc (xl, e', env')) in
      let (v', mem') = eval mem'' env'' e' in
      (v', mem')
    | CALLR (id, idl) ->
      let (xl, e, env') = lookup_env_proc env id in
      let rec get_env f_env f_xl f_idl =
        (match f_xl with
        | [] -> if f_idl=[] then f_env else raise (Error "InvalidArg")
        | head::tail -> if f_idl = [] then raise (Error "InvalidArg") else
                        (get_env (Env.bind f_env (List.hd f_xl) (Addr (lookup_env_loc env (List.hd f_idl)))) (List.tl f_xl) (List.tl f_idl))
        )
      in
      let env'' = get_env env' xl idl in
      let env'' = Env.bind env'' id (Proc (xl, e, env')) in
      let (v, mem') = eval mem env'' e in
      (v, mem')
    | RECORD [] -> (Unit, mem)
    | RECORD iel ->
      let il, el = List.split iel in
      let rec getMn f_el f_mem f_env =
        (match f_el with
        | [] -> f_mem
        | head::tail -> (let (tmp_v, tmp_mem) = eval f_mem f_env head in getMn tail tmp_mem f_env)
        )
      in
      let rec getVlist f_el f_mem f_env =
        (match f_el with
        | [] -> []
        | head::tail -> (let (tmp_v, tmp_mem) = eval f_mem f_env head in [tmp_v] @ getVlist tail tmp_mem f_env)
        )
      in
      let rec get_xll_mem f_xll f_mem f_il f_vl =
        (match f_il with
        | [] -> (f_xll, f_mem)
        | head::tail -> (let (l, temp_mem) = Mem.alloc f_mem in
                        let temp_mem = Mem.store temp_mem l (List.hd f_vl) in
                        let temp_xl = (List.hd f_il, l) in
                        get_xll_mem (f_xll@[temp_xl]) temp_mem tail (List.tl f_vl)
                        )
        )
      in
      let rec get_by_id_in_xll f_xll f_id =
        (match f_xll with
        | [] -> raise (Error "Unbound")
        | (hh,ht)::tail -> if hh=f_id then ht else get_by_id_in_xll tail f_id
        )
      in
      let mn = getMn el mem env in
      let vl = getVlist el mem env in
      let (xll, mem') = get_xll_mem [] mem il vl in
      let record = Record (get_by_id_in_xll xll) in
      (record, mem')
    | FIELD (e, id) ->
      let (r, mem') = eval mem env e in
      (Mem.load mem' (value_record r id), mem')
    | ASSIGN (id, e) ->
      let (v, mem')= eval mem env e in
      (v, Mem.store mem' (lookup_env_loc env id) v)
    | ASSIGNF (e1, id, e2) ->
      let (r, mem1) = eval mem env e1 in
      let (v, mem2) = eval mem env e2 in
      (v, Mem.store mem2 (value_record r id) v)
    | _ -> failwith "Unimplemented" (* TODO : Implement rest of the cases *)

  let run (mem, env, pgm) = 
    let (v, _ ) = eval mem env pgm in
    v
end
