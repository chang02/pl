exception InvalidArgument
type ae = CONST of int
| VAR of string
| POWER of string * int
| TIMES of ae list
| SUM of ae list


let rec diff ((a : ae), (s: string)) : ae =
	match a with
	|CONST x -> CONST 0
	|VAR x -> if x=s then CONST 1 else CONST 0
	|POWER (x,y) -> if x = s then (TIMES [CONST y ; POWER (x, y-1)]) else CONST 0
	|TIMES x -> 
		(match x with
		|[] -> raise InvalidArgument
		|(head::[]) -> diff (head, s)
		|(head::tail) -> (SUM [(TIMES [(diff (head, s)) ; TIMES tail]) ; (TIMES [head ; (diff ((TIMES tail), s))])])
		)
	|SUM x ->
		(match x with
		|[] -> raise InvalidArgument
		|(head::[]) -> diff (head, s)
		|(head::tail) -> (SUM [(diff (head, s)) ; (diff ((SUM tail), s))])
		)