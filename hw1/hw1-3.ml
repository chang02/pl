type team = Korea | France | Usa | Brazil | Japan | Nigeria | Cameroon | Poland | Portugal | Italy | Germany | Norway | Sweden | England | Argentina
type tourna = LEAF of team | NODE of tourna * tourna

let teamToString (input: team) : string =
	match input with
	|Korea -> "Korea"
	|France -> "France"
	|Usa -> "Usa"
	|Brazil -> "Brazil"
	|Japan -> "Japan"
	|Nigeria -> "Nigeria"
	|Cameroon -> "Cameroon"
	|Poland -> "Poland"
	|Portugal -> "Portugal"
	|Italy -> "Italy"
	|Germany -> "Germany"
	|Norway -> "Norway"
	|Sweden -> "Sweden"
	|England -> "England"
	|Argentina -> "Argentina"

let rec parenize (input: tourna) : string =
	match input with
	|LEAF a -> teamToString a
	|NODE (a,b) -> "(" ^ (parenize a) ^ " " ^ (parenize b) ^ ")"

(* let _ = print_string (parenize(NODE(NODE(LEAF Korea, LEAF Portugal), LEAF Brazil))) *)

(* let _ =
	if parenize (NODE(LEAF Norway, NODE(NODE(LEAF Cameroon, LEAF Poland), LEAF Sweden))) = "(Norway ((Cameroon Poland) Sweden))" then print_string "yes" else print_string "no" *)