type nat = ZERO | SUCC of nat

let rec natadd ((a : nat), (b : nat)) : nat =
	match b with
	|ZERO -> a
	|SUCC x -> natadd (SUCC a, x)

let rec nataddn ((a : nat), (n: nat), (r: nat)) : nat =
	match n with
	|ZERO -> r
	|SUCC x -> nataddn(a, x, natadd (r, a))

let rec natmul ((a : nat), (b : nat)) : nat =
	if a = ZERO || b = ZERO then ZERO
	else (match b with
		|SUCC ZERO -> a
		|SUCC x -> nataddn (a, b, ZERO)
		|ZERO -> ZERO
	)


(* let _ =
	if natmul (SUCC (SUCC (SUCC (SUCC ZERO))), SUCC (SUCC (SUCC ZERO))) = SUCC(SUCC (SUCC (SUCC (SUCC (SUCC (SUCC (SUCC (SUCC (SUCC (SUCC (SUCC ZERO))))))))))) then print_string "yes" else print_string "no" *)