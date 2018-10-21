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


let rec shoppingList (rql: require list) : (id * gift list) list =
	let sorted_rql = sort_rql rql in
	[(A, [1;2]);(B, [2;3])]
