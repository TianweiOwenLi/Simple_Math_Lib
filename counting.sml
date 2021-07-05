fun fact 0 f = f (1) | fact n f = fact (n-1) (f o (fn x => n * x))

fun en 0 = [] | en n = n :: en (n-1)


fun part n [] = 0 
  | part n [x] = if n mod x = 0 then 1 else 0
  | part n (x::l) = if x > n then part n l 
                    else part (n-x) (x::l) + part n l;

(* fun cps_part n [] h = h 0
  | cps_part n [x] h = if n mod x = 0 then h 1 else h 0
  | cps_part n (x::l) h = 
    if x > n then cps_part n l h
    else cps_part (n-x) (x::l) (fn p1 => cps_part n l (fn p2 => h (p1 + p2))) 
*)