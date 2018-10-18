type expr = NUM of int
| PLUS of expr * expr
| MINUS of expr * expr

type formula = TRUE
| FALSE
| NOT of formula
| ANDALSO of formula * formula
| ORELSE of formula * formula
| IMPLY of formula * formula
| LESS of expr * expr

let rec calExpr (input : expr) : int =
	match input with
	|NUM a -> a
	|PLUS (a,b) -> (calExpr a) + (calExpr b)
	|MINUS (a,b) -> (calExpr a) - (calExpr b)

let isLess ((a : expr), (b : expr)) : bool =
	if (calExpr a) < (calExpr b) then true else false

let rec eval (input: formula) : bool =
	match input with
	|TRUE -> true
	|FALSE -> false
	|NOT a -> not (eval a)
	|ANDALSO (a, b) -> (eval a) && (eval b)
	|ORELSE (a, b) -> (eval a) || (eval b)
	|IMPLY (a, b) -> if (eval a) == false then true else if (eval b) == true then true else false
	|LESS (a, b) -> if isLess (a,b) then true else false


(* let _ = 
	if (eval (IMPLY (FALSE, FALSE))) then print_string "true" else print_string "false" *)
(* 
let _ =
	if eval (LESS (PLUS(NUM 3, NUM 4), MINUS(NUM 7, NUM 8))) = false then print_string "yes" else print_string "no" *)