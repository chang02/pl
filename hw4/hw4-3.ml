type id = A | B | C | D | E

type gift = int

type cond = 
Items of gift list (* 선물들 *)
| Same of id (* 어느 조카의 선물들 *)
| Common of cond * cond (* 두조건에 공통된 선물들 *)
| Except of cond * gift list (* 조건에서 어느 선물들은 빼고 *)

type require = id * (cond list)


let rec sort_rql (rql: require list) : require list =
	let rec find rql id =
		match rql with
		| [] -> []
		| hd::tl -> if ((fst hd)=id) then (snd hd) else (find tl id)
	in
	[(A, find rql A)]@[(B, find rql B)]@[(C, find rql C)]@[(D, find rql D)]@[(E, find rql E)]

let rec common_gift ((gl1: gift list), (gl2: gift list), (res: gift list)) : gift list =
	match gl1 with
	| [] -> res
	| (hd::tl) -> if (List.mem hd gl2) then (common_gift (tl,gl2,(hd::res))) else (common_gift (tl,gl2,res))

let rec except_gift ((gl: gift list), (el: gift list), (res: gift list)) : gift list =
	match gl with
	| [] -> res
	| (hd::tl) -> if (List.mem hd el) then (except_gift (tl,el,res)) else (except_gift (tl,el,(hd::res)))


let rec precal_condl (condl: cond list) : gift list =
	match condl with
	| [] -> []
	| ((Items gl)::tl) -> [gl] @ (precal_condl tl)
	| ((Same i)::tl) -> pre_condl tl
	| ((Common (c1, c2))::tl) -> (common_gift ((precal_condl [c1]), (precal_cond1 [c2]), [])) @ (precal_condl tl)
	| ((Except (c, gl))::tl) -> (except_gift ((precal_condl [c]), gl, [])) @ (precal_condl tl)


let rec shoppingList (rql: require list) : (id * gift list) list =
	let sorted_rql = sort_rql rql in
	let idl, condll = List.split sorted_rql in
	let gl1 = List.map precal_condl condll in
	[(A, [1;2;3])]
