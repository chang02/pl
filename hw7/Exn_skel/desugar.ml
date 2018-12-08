(*
 * SNU 4190.310 Programming Languages 
 * Homework "Exceptions are sugar" Skeleton
 *)

open Xexp

let count = ref 0
let new_var () = 
	let _ = count := !count +1 in
	"@_" ^ (string_of_int !count)

let removeExn : xexp -> xexp = fun xexp ->
	let rec cps : xexp -> xexp = fun e ->
		match e with
		| Num _ | Var _ -> 
			let k, h = new_var (), new_var () in
			Fn (k, Fn (h, App (Var k, e)))
		| Fn (x, e) ->
			let k, h = new_var (), new_var () in
			Fn (k, Fn (h, App (Var k, Fn (x, cps e))))
		| App (e1, e2) ->
			let k, h, f, v = new_var (), new_var (), new_var (), new_var () in
			let tmp1 = Fn (v, App (App (App (Var f, Var v), Var k), Var h)) in
			let tmp2 = Fn (f, App (App ((cps e2), tmp1), (Var h))) in
			let tmp3 = App (App ((cps e1), tmp2), (Var h)) in
			Fn (k, Fn (h, tmp3))
		| If (e, e1, e2) ->
			let k, h, v1 = new_var (), new_var (), new_var () in
			let t1 = new_var () in
			let tmp1 = Fn (t1, App (Var k, Var t1)) in
			let tmp2 = App (App ((cps e1), tmp1), (Var h)) in
			let t2 = new_var () in
			let tmp3 = Fn (t2, App (Var k, Var t2)) in
			let tmp4 = App (App ((cps e2), tmp3), (Var h)) in
			let tmp5 = Fn (v1, If (Var v1, tmp2, tmp4)) in
			let tmp6 = App (App ((cps e), tmp5), (Var h)) in
			Fn (k, Fn (h, tmp6))
		| Equal (e1, e2) ->
			let k, h = new_var (), new_var () in
			let v1, v2 = new_var (), new_var () in
			let tmp1 = Fn (v2, App (Var k, Equal (Var v1, Var v2))) in
			let tmp2 = Fn (v1, App (App ((cps e2), tmp1), (Var h))) in
			let tmp3 = App (App ((cps e1), tmp2), (Var h)) in
			Fn (k, Fn (h, tmp3))
		| Handle (e1, n, e2) ->
			let k, h = new_var (), new_var () in
			let x = new_var () in
			let thn = App (App ((cps e2), (Var k)), (Var h)) in
			let els = App (Var h, Var x) in
			let tmp1 = Fn (x , If (Equal (Var x, Num n), thn, els)) in
			let tmp2 = App (App ((cps e1), (Var k)), tmp1) in
			Fn (k, Fn (h, tmp2))
		| Raise e -> 
			let k, h = new_var (), new_var () in
			Fn (k, Fn (h, App (App ((cps e), (Var h)), (Var h))))
	in

	let v = new_var () in
	App (App (cps xexp, Fn (v, Var v), Fn (v, Num 201712)))
