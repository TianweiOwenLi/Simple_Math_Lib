datatype 'a set = Set of 'a list

fun mp f (x, y) = (f x, f y)

fun setin (eq : 'a * 'a -> bool) (Set [] : 'a set) (n : 'a) : bool = false
  | setin eq (Set (x::xs)) (n) = eq (x, n) orelse setin eq (Set xs) n

fun setnin eq s n = not (setin eq s n)

fun setadd eq (Set xs) x = if setin eq (Set xs) x then Set xs else Set (x::xs)

fun no_dupes (eq : 'a * 'a -> bool) (Set ([]) : 'a set ) : 'a set = Set ([])
  | no_dupes eq (Set (x::xs)) = 
      if setin eq (Set (xs)) x then no_dupes eq (Set (xs)) 
      else setadd eq (no_dupes eq (Set xs)) x

fun U (eq : 'a * 'a -> bool) (Set [] : 'a set) (R : 'a set) : 'a set = R
  | U eq (Set (x::xs)) R = let 
                         val mid = U eq (Set xs) R
                       in
                         if setin eq R x then mid else setadd eq mid x
                       end

fun N (eq : 'a * 'a -> bool) (Set [] : 'a set) (R : 'a set) : 'a set = Set []
  | N eq (Set (x::xs)) R = let
                           val mid = N eq (Set xs) R
                         in
                           if setin eq R x then setadd eq mid x else mid
                         end

fun setmin (eq : 'a * 'a -> bool) (Set [] : 'a set) (R : 'a set) : 'a set = Set []
  | setmin eq (Set (x::xs)) R = let
                                  val mid = setmin eq (Set xs) R
                                in
                                  if setin eq R x then mid else setadd eq mid x
                                end

fun enum 0 = [] | enum n = n :: enum (n-1)

fun fact 0 = 1 | fact n = n * fact (n-1)


fun part n [] = 0 
  | part n [x] = if n mod x = 0 then 1 else 0
  | part n (x::l) = if x > n then part n l else part (n-x) (x::l) + part n l;






(* fun cps_fact 0 f = f (1) | cps_fact n f = fact (n-1) (f o (fn x => n * x)) *)

(* fun cps_part n [] h = h 0
  | cps_part n [x] h = if n mod x = 0 then h 1 else h 0
  | cps_part n (x::l) h = 
    if x > n then cps_part n l h
    else cps_part (n-x) (x::l) (fn p1 => cps_part n l (fn p2 => h (p1 + p2))) 
*)