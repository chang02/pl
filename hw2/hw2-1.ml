exception FreeVariable

type exp = X
| INT of int
| REAL of float
| ADD of exp * exp
| SUB of exp * exp
| MUL of exp * exp
| DIV of exp * exp
| SIGMA of exp * exp * exp
| INTEGRAL of exp * exp * exp

let rec f ((e: exp), (n:float)) : float =
	match e with
	|X -> n
	|INT x -> float_of_int x
    |REAL x -> x
    |ADD (x,y) -> (f (x, n)) +. (f (y, n))
    |SUB (x,y) -> (f (x, n)) -. (f (y, n))
    |MUL (x,y) -> (f (x, n)) *. (f (y, n))
    |DIV (x,y) -> (f (x, n)) /. (f (y, n))
    |SIGMA (x,y,z) -> sigma (int_of_float (calculate x),int_of_float (calculate y),z)
    |INTEGRAL (x,y,z) -> if calculate x > calculate y then calculate (MUL(REAL (-1.0), REAL (integral (calculate y, calculate x, z)))) else integral (calculate x, calculate y, z)

and integral ((x:float), (y:float),(z:exp)) : float =
    if y -. x < 0.1 then 0.0
    else (f(z, x) *. 0.1) +. (integral (x +. 0.1, y, z))

and sigma ((x:int),(y:int),(z:exp)) : float =
	if x>y then 0.0
	else f (z, float_of_int x) +. sigma (x + 1, y,z)

and calculate (e: exp) : float =
	match e with
	|X -> raise (FreeVariable)
	|INT x -> float_of_int x
    |REAL x -> x
    |ADD (x,y) -> (calculate x) +. (calculate y)
    |SUB (x,y) -> (calculate x) -. (calculate y)
    |MUL (x,y) -> (calculate x) *. (calculate y)
    |DIV (x,y) -> (calculate x) /. (calculate y)
    |SIGMA (x,y,z) -> sigma (int_of_float (calculate x), int_of_float (calculate y),z)
    |INTEGRAL (x,y,z) -> if calculate x > calculate y then calculate (MUL(REAL (-1.0), REAL (integral (calculate y, calculate x, z)))) else integral (calculate x, calculate y, z)
