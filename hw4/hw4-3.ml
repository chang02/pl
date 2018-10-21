type id = A | B | C | D | E

type gift = int

type cond = 
Items of gift list (* 선물들 *)
| Same of id (* 어느 조카의 선물들 *)
| Common of cond * cond (* 두조건에 공통된 선물들 *)
| Except of cond * gift list (* 조건에서 어느 선물들은 빼고 *)

type require = id * (cond list)


let rec sort_rql (rql: require list) : require list =
	[(A, if ((List.assoc_opt A rql) = None) then [] else (List.assoc_opt A rql))]@
	[(B, if ((List.assoc_opt B rql) = None) then [] else (List.assoc_opt B rql))]@
	[(C, if ((List.assoc_opt C rql) = None) then [] else (List.assoc_opt C rql))]@
	[(D, if ((List.assoc_opt D rql) = None) then [] else (List.assoc_opt D rql))]@
	[(E, if ((List.assoc_opt E rql) = None) then [] else (List.assoc_opt E rql))]


let rec shoppingList (rql: require list) : (id * gift list) list =
	let sorted_rql = sort_rql rql in
	[(A, [1;2]);(B, [2;3]))
