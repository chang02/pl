(*
 * SNU 4190.310 Programming Languages 2017 Fall
 *  K- Interpreter Skeleton Code
 * DongKwon Lee (dklee@ropas.snu.ac.kr)
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
    | RECORD il -> (* il (id * exp) list *)
      if il = [] then (Unit, mem) 
      else ( 
        let rec make_vmlist el vm = (* (x, v) list *) 
          begin
      	  if el=[] then [] else (
      	    let (mvmv, mvmm) = eval vm env (snd (List.hd el)) in
      	    (fst (List.hd el), mvmv)::(make_vmlist (List.tl el) mvmm) 
   	      )
  	 	  end 
  	    in 
  	    let rec rec_mem vml el vmem =
  	      begin
  	      	match vml with
  	      	| [] -> []
  	      	| vhd::vtl -> 
  	      	  (let (l, vmem'') = Mem.alloc vmem in
  	      	   let vmem1 = Mem.store vmem'' l (snd (List.hd vml)) in 
  	      	  (((fst (List.hd el), l), vmem1)::(rec_mem vtl (List.tl el) vmem1)) )
  	      end 
  	    in 
  	    let xvlist = make_vmlist il mem in 
  	    let (xllist, memlist) = List.split (rec_mem xvlist il mem) in
  	    let rec find_id id xllst = 
    	  begin 
    	  	match xllst with 
    	  	| [] -> raise (Error "Unbound")
    	  	| hd::tl -> if (fst hd) = id then (snd hd) else find_id id tl
  	      end
  	    in 
  	    let rec f x = find_id x xllist in
  	    (Record f, List.hd (List.rev memlist))
      )  
    | CALLV (i, exl) -> 
      let (xlist, e', sigma') = lookup_env_proc env i in
      let rec make_vmlist el vm = 
      	begin
      	if el=[] then [] else (
      	  let (mvmv, mvmm) = (eval vm env (List.hd el)) in
      	  (mvmv, mvmm)::(make_vmlist (List.tl el) mvmm) 
   	    )
  	 	end 
  	  in 
  	  let rec sigma_mem venv vmem vml xl iid =
  	    begin
  		  match vml with
  		  | [] -> (if xl=[] then ((Env.bind venv iid (Proc (xlist, e', sigma'))), vmem)
  		  		  else raise (Error "InvalidArg") )
  		  | vhd::vtl -> 
  		  (let (l, vmem'') = Mem.alloc vmem in
  		  sigma_mem (Env.bind venv (List.hd xl) (Addr l)) (Mem.store vmem'' l (fst vhd)) vtl (List.tl xl) iid)
  	    end
  	  in
  	  
  	  let vmlist = (make_vmlist exl mem) in
  	  let (env', mem') = sigma_mem sigma' (snd (List.hd (List.rev vmlist))) vmlist xlist i in 
  	  (eval mem' env' e')

  	| CALLR (i, il) -> 
  	  let (xlist, rexp, env') = lookup_env_proc env i in
  	  let rec iltoyl iil = 
  	    match iil with
  	    | [] -> [] 
  	    | hd::tl -> (Addr (lookup_env_loc env hd))::(iltoyl tl) in

  	  let rec bind_sigma xl yl ii benv = 
  	  	begin
  	 	 match (xl, yl) with
  		 | ([], []) -> Env.bind benv ii (Proc (xlist, rexp, env'))
  		 | (xd::xtl, yd::ytl) -> (bind_sigma xtl ytl ii (Env.bind benv xd yd))
  		 | _ -> raise (Error "InvalidArg") 
  		end
  	  in
  	  let (v, mem') = eval mem (bind_sigma xlist (iltoyl il) i env') rexp in
  	  (v, mem')

    | LETV (x, e1, e2) ->
      let (v, mem') = eval mem env e1 in
      let (l, mem'') = Mem.alloc mem' in
      eval (Mem.store mem'' l v) (Env.bind env x (Addr l)) e2
    | LETF (x, xl, e1, e2) -> 
      let (v, mem') = eval mem (Env.bind env x (Proc (xl, e1, env))) e2 in
      (v, mem') 
    | ASSIGN (x, e) ->
      let (v, mem') = eval mem env e in
      let l = lookup_env_loc env x in
      (v, Mem.store mem' l v)
    | ASSIGNF (e1, x, e2) -> 
      let (r, mem1) = eval mem env e1 in 
      let (v, mem2) = eval mem1 env e2 in
      (v, Mem.store mem2 (value_record r x) v) 
    | FIELD (e1, i1) ->
      let (r, mem') = eval mem env e1 in
      (Mem.load mem' (value_record r i1), mem')
    | NUM (n) -> (Num n, mem)
    | TRUE -> (Bool true, mem)
    | FALSE -> (Bool false, mem)
    | UNIT -> (Unit, mem)
    | VAR (i) -> (Mem.load mem (lookup_env_loc env i), mem)
    | ADD (e1, e2) -> 
      let (v1, mem') = eval mem env e1 in
      let (v2, mem'') = eval mem' env e2 in
      let n1 = value_int v1 in
      let n2 = value_int v2 in
      (Num (n1 + n2), mem'')
    | SUB (e1, e2) -> 
      let (v1, mem') = eval mem env e1 in
      let (v2, mem'') = eval mem' env e2 in
      let n1 = value_int v1 in
      let n2 = value_int v2 in
      (Num (n1 - n2), mem'')
    | MUL (e1, e2) -> 
      let (v1, mem') = eval mem env e1 in
      let (v2, mem'') = eval mem' env e2 in
      let n1 = value_int v1 in
      let n2 = value_int v2 in
      (Num (n1 * n2), mem'')
    | DIV (e1, e2) -> 
      let (v1, mem') = eval mem env e1 in
      let (v2, mem'') = eval mem' env e2 in
      let n1 = value_int v1 in
      let n2 = value_int v2 in
      (Num (n1 / n2), mem'')
    | EQUAL (e1, e2) -> 
      let (v1, mem') = eval mem env e1 in
      let (v2, mem'') = eval mem' env e2 in 
     (match (v1, v2) with
      | (Num (n1), Num (n2)) -> (Bool (n1=n2), mem'')
      | (Bool (b1), Bool(b2)) -> (Bool (b1=b2), mem'')
      | (Unit, Unit) -> (Bool (true), mem'')
      | _ -> (Bool (false), mem'')
  	 )
    | LESS (e1, e2) -> 
      let (v1, mem') = eval mem env e1 in
      let (v2, mem'') = eval mem' env e2 in
      let n1 = value_int v1 in
      let n2 = value_int v2 in
      (Bool (n1 < n2), mem'')
    | NOT (e) -> 
      let (v, mem') = eval mem env e in 
      let b = value_bool v in 
      (Bool (not(b)), mem')
    | SEQ (e1, e2) -> 
      let (v1, mem') = eval mem env e1 in 
      let (v2, mem'') = eval mem' env e2 in 
      (v2, mem'')
    | IF (e, e1, e2) -> 
      let (v, mem') = eval mem env e in 
     (match v with
	  | Bool (true) -> 
	  let (v1, mem'') = eval mem' env e1 in 
	  (v1, mem'')
	  | Bool (false) -> 
	  let (v1, mem'') = eval mem' env e2 in
	  (v1, mem'')
	  | _ -> raise (Error "Unbound")
     )
    | WHILE (e1, e2) -> 
      let (v, mem') = eval mem env e1 in 
      (match v with
      | Bool (false) -> (Unit, mem')
      | Bool (true) -> 
        (let (v1, mem1) = eval mem' env e2 in 
         let (v2, mem2) = eval mem1 env (WHILE (e1, e2)) in
         (v2, mem2) ) 
      | _ -> raise (Error "Unbound")
      ) 

    | _ -> failwith "Unimplemented" (* TODO : Implement rest of the cases *)



  let run (mem, env, pgm) = 
    let (v, _ ) = eval mem env pgm in
    v
end
