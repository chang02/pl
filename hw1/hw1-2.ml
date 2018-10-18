let rec prod ((m : (int * int) -> float), (n : int), (k : int)) : float =
	if k==0 then 1.0
	else m(n, k) *. prod(m, n, k-1)

let rec sumprod ((m : (int * int) -> float), (n : int), (k : int)) : float =
	if n==0 then 0.0
	else prod(m,n,k) +. sumprod(m,n-1,k)




(* let x ((a: int), (b: int)) : float =
	float_of_int (a * b)

let _ = print_float (sumprod(x, 3, 3)) *)

(* let matrix (i, j) = ((float_of_int i) *. 10.) +. (float_of_int j)

let _ = print_float (sumprod (matrix, 2, 7)) *)