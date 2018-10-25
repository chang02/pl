type id = A | B | C | D | E

type gift = int

type cond = 
Items of gift list
| Same of id
| Common of cond * cond
| Except of cond * gift list

type require = id * (cond list)

let rec sort_rql (rql: require list) : require list =
	let rec find rql id =
		match rql with
		| [] -> []
		| hd::tl -> if ((fst hd)=id) then (snd hd) else (find tl id)
	in
	[(A, find rql A)]@[(B, find rql B)]@[(C, find rql C)]@[(D, find rql D)]@[(E, find rql E)]

let rec remove_gll_dup (gll: gift list list) : gift list list =
	match gll with
	| [] -> []
	| hd::tl -> (List.sort_uniq compare hd)::remove_gll_dup(tl)

let rec common_gift ((gl1: gift list), (gl2: gift list), (res: gift list)) : gift list =
	match gl1 with
	| [] -> res
	| (hd::tl) -> if (List.mem hd gl2) then (common_gift (tl,gl2,(hd::res))) else (common_gift (tl,gl2,res))

let rec except_gift ((gl: gift list), (el: gift list), (res: gift list)) : gift list =
	match gl with
	| [] -> res
	| (hd::tl) -> if (List.mem hd el) then (except_gift (tl,el,res)) else (except_gift (tl,el,(hd::res)))

let rec cal_condl ((condl: cond list), (sl: (id * gift list) list)) : gift list =
	match condl with
	| [] -> []
	| (Items gl)::tl -> gl @ (cal_condl (tl, sl))
	| (Same id)::tl -> (List.assoc id sl) @ (cal_condl (tl, sl))
	| (Common (c1, c2))::tl -> (common_gift (cal_condl ([c1], sl), cal_condl ([c2], sl), [])) @ (cal_condl (tl, sl))
	| (Except (c, el))::tl -> (except_gift (cal_condl ([c], sl), el, [])) @ (cal_condl (tl, sl))

let rec cal_condll ((condll: cond list list), (sl: (id * gift list) list)) : gift list list =
	match condll with
	| [] -> []
	| hd::tl -> [(cal_condl (hd, sl))] @ (cal_condll (tl, sl))

let rec isEqual ((l1: gift list list), (l2: gift list list)) : bool =
	let rec isEqual2 ((g1: gift list), (g2: gift list)) : bool =
		(match (g1, g2) with
		| (hd1::tl1, hd2::tl2) -> if (hd1=hd2) then isEqual2 (tl1, tl2) else false
		| ([], []) -> true
		| _ -> false)
	in
	(match (l1, l2) with
	| (hd1::tl1, hd2::tl2) -> if isEqual2((List.sort compare hd1), (List.sort compare hd2)) then isEqual(tl1, tl2) else false
	| ([], []) -> true
	| _ -> false)

let rec do_cal_condll_while_diff ((condll: cond list list), (sl: (id * gift list) list)) : gift list list =
	let (idl, gll) = List.split sl in
	let nextgll = cal_condll (condll, sl) in
	let gll = remove_gll_dup gll in
	let nextgll = remove_gll_dup nextgll in
	if isEqual (nextgll, gll) then nextgll
	else do_cal_condll_while_diff (condll, (List.combine [A;B;C;D;E] nextgll))


let rec shoppingList (rql: require list) : (id * gift list) list =
	let sorted_rql = sort_rql rql in
	let idl, condll = List.split sorted_rql in
	let sl = List.combine [A;B;C;D;E] [[];[];[];[];[]] in
	List.combine [A;B;C;D;E] (do_cal_condll_while_diff (condll, sl))