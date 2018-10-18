(*
 * SNU 4190.310 Programming Languages 
 * Homeworv1 "Exceptions are sugar" Sv1eleton
 *)
open Xexp

let count = ref 0
let var_name () = 
  let _ = count := !count + 1 in
  "#@#" ^ (string_of_int !count)

let rec cps : xexp -> xexp = fun e ->
  let v1 = var_name () in
  let v2 = var_name () in
  match e with
  | Num n -> Fn (v1, Fn (v2, App (Var v1, Num n)))
  | Var x -> Fn (v1, Fn (v2, App (Var v1, Var x)))
  | Fn (x, e) -> Fn (v1, Fn (v2, App (Var v1, Fn (x, cps e))))
  | App (e1, e2) ->
  	(begin
    let v3 = var_name() in
    let v4 = var_name() in
    Fn (v1, Fn (v2, 
    	App (App (cps e1, Fn (v3, 
   			App (App (cps e2, 
   				Fn (v4, App (App (App (Var v3, Var v4), Var v1), Var v2))), Var v2) 							
    			)
    		), 
    	Var v2)
	    )
	)
	end)

  | If (e1, e2, e3) -> 
  	(begin
    let v3 = var_name() in 
    let v4 = var_name() in
    let v5 = var_name() in
    let if_true = App (App (cps e2, Fn (v3, App (Var v1, Var v3))), Var v2)	in
    let if_false = App (App (cps e3, Fn (v4, App (Var v1, Var v4))), Var v2) in
    Fn (v1, Fn (v2, App (App (cps e1, Fn (v5, If (Var v5, if_true, if_false))), Var v2)))
	end)

  | Equal (e1, e2) -> 
  	(begin
  	let v3 = var_name() in 
  	let v4 = var_name() in
  	Fn (v1, Fn (v2,
  		App (
  			App (cps e1, 
  				Fn (v3, 
  					App (App (cps e2, (Fn (v4, App (Var v1, Equal (Var v3, Var v4))))), Var v2)
  					)
  				),
  			Var v2
  			)
  		)
  	)
  	end)

  | Raise e -> Fn (v1, Fn (v2, App (App (cps e, Var v2), Var v2)))

  | Handle (e1, n, e2) -> 
  	(begin
  	let v3 = var_name() in
  	Fn (v1, Fn (v2,
  		App (App (cps e1, Var v1),
  			(Fn (v3, 
  				If (Equal (Var v3, Num n), 
  					App (App (cps e2, Var v1), Var v2), App (Var v2, Var v3))	
  					)
  				)
  			) 
  		)
  	)
    end)
let removeExn : xexp -> xexp = fun e ->
  let var1 = var_name() in
  let var2 = var_name() in
  App (App (cps e, Fn (var1, Var var1)), Fn (var2, Num 201712))
