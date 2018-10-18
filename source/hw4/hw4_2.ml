type require = id * (cond list)
and cond
	= Items of gift list 
	| Same of id 
	| Common of cond * cond 
	| Except of cond * gift list 
and gift = int 
and id = A | B | C | D | E 
let rec intersect a b = 
	let rec mem x = function | [] -> false | h::t -> h = x || mem x t in
	let rec remove y = function
  	| [] -> failwith "y not in list" | h::t -> if h = y then t else h::(remove y t) in
    match a with
    | [] -> if b = [] then [] else intersect b a
    | h::t ->
        if mem h b then
          let b' = remove h b in
          h::(intersect t b')
        else intersect t b
let diff l1 l2 = List.filter (fun x -> not (List.mem x l2)) l1  
let rec f r i = 
	if (fst (List.hd r)==i) then List.hd r else f (List. tl r) i
let rec nonexist r i =
	if r==[] then true else 
	  (if (fst (List.hd r)==i) then false else nonexist (List. tl r) i)
let rec full r idlist = 
	let make_full r i = if (nonexist r i) then (i, [])::r else r in
	match idlist with | [] -> r | hd::tl -> full (make_full r hd) tl
let sort r = 
	(f r A)::(f r B)::(f r C)::(f r D)::(f r E)::[]
let rec remove_one r man =
	if r==[] then [] else (
	  if (fst (List.hd r)) != man then (List.hd r)::(remove_one (List.tl r) man)
	  else remove_one (List.tl r) man) 
let rec init r = 
	let rec ic cl = (* cl is id * (cond list) *)
	  if cl==[] then [] else
	  (match List.hd cl with | Items g -> List.sort compare g | _ -> ic (List.tl cl)) in
	if r==[] then [] else 
	(match List.hd r with | (i, c) -> (i, ic c)::(init (List.tl r)))
let plus_items man item result =
	let man_items = List.sort_uniq compare ((snd (f result man))@item) in
	(man, man_items)::(remove_one result man)
let same_gift man1 man2 result = 
	List.sort_uniq compare ((snd (f result man1))@(snd (f result man2)))
let rec list_sort result = 
	match result with 
	| hd::tl -> (fst hd, List.sort_uniq compare (snd hd))::(list_sort tl)
	| [] -> []
let rec one_result one_r result = (* (id * cond list) result  ->  item list *)
	if (snd one_r)==[] then [] else(
	  match List.hd (snd one_r) with
	  | Items l -> List.sort_uniq compare (l@(one_result (fst one_r, List.tl (snd one_r)) result))
	  | Same i -> (same_gift (fst one_r) i result)@(one_result (fst one_r, List.tl (snd one_r)) result)
	  | Common (c1, c2) -> (intersect (one_result (fst one_r, c1::[]) result) (one_result (fst one_r, c2::[]) result))
	  						@(one_result (fst one_r, List.tl (snd one_r)) result)
	  | Except (c, i) -> (diff (one_result (fst one_r, c::[]) result) i)
	  						@(one_result (fst one_r, List.tl (snd one_r)) result)
	)
let rec make_result rlist result = 
	if rlist==[] then [] else (
		let ones = one_result (List.hd rlist) result in 
		let newr = plus_items (fst (List.hd rlist)) ones result in
		((fst (List.hd rlist)), ones)::(make_result (List.tl rlist) newr) 
	)
let rec rec_result rlist result = 
	let newr = sort (list_sort (make_result rlist result)) in 
	if newr = result then newr else rec_result rlist newr
let rec shoppingList r = 
	let sorted = sort (full r [A;B;C;D;E]) in 
	let result = init sorted in 
	rec_result sorted result