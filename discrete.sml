datatype 'a set = Set of 'a list
type 'a cong = 'a * 'a -> bool
type 'a ord = 'a * 'a -> order
type 'a bin = 'a * 'a -> 'a
type 'a pred = 'a -> bool


(* mp : ('a -> 'b) -> 'a * 'a -> 'b * 'b
 * REQUIRES: true
 * ENSURES: f being applied separately on x and y, forming a resulting
 *  pair. Similar to map.
 *)
fun mp f (x, y) = (f x, f y)


(* setin : 'a cong -> 'a set -> 'a -> bool
 * REQUIRES: eq is total
 * ENSURES: setin eq S n ==> true if there exists some x in S such that 
 *  eq (x, n) = true, and setin eq S n ==> false otherwise. 
 *  (this checkes if a set contains some element. )
 *)
fun setin (eq : 'a cong) (Set [] : 'a set) (n : 'a) : bool = false
  | setin eq (Set (x::xs)) (n) = eq (x, n) orelse setin eq (Set xs) n


(* setnin : 'a cong -> 'a set -> 'a -> bool
 * REQUIRES: eq is total
 * ENSURES: setnin eq S n ==> false if there exists some x in S such that 
 *  eq (x, n) = true, and setin eq S n ==> true otherwise. 
 *  (this ckeckes if a set not contains some element. )
 *)
fun setnin eq s n = not (setin eq s n)


(* setadd : 'a cong -> 'a set -> 'a -> 'a set
 * REQUIRES: eq is total
 * ENSURES: setadd eq (Set xs) x ==> Set xs if setin eq (Set xs) x, 
 *  and setadd eq (Set xs) x ==> Set (x::xs) otherwise. 
 *  This is basically un-duplicated add.
 *)
fun setadd eq (Set xs) x = if setin eq (Set xs) x then Set xs else Set (x::xs)


(* no_dupes : 'a cong -> 'a set -> 'a set
 * REQUIRES: eq is total
 * ENSURES: no_dupes eq S ==> S', where S' has no duplicate elements.
 *  (Note that lists are only used to express the idea of sets, and 
 *   whether the list has duplicates or not won't make a difference 
 *   in the set it represents. This function is merely used for 
 *   cleaning up the list and make set representations more efficient. )
 *)
fun no_dupes (eq : 'a cong) (Set ([]) : 'a set ) : 'a set = Set ([])
  | no_dupes eq (Set (x::xs)) = 
      if setin eq (Set (xs)) x then no_dupes eq (Set (xs)) 
      else setadd eq (no_dupes eq (Set xs)) x


(* setfold : 'a bin -> 'a set -> 'a option
 * REQUIRES: f is well-defined over X S S
 * ENSURES: setfold f S ==> NONE if S is empty set, 
 *  and setfold f (S l) ==> SOME (fold l f x l) otherwise. 
 *)
fun setfold (f : 'a bin) (Set [] : 'a set) : 'a option = NONE
  | setfold f (Set (x::xs)) = SOME (foldl f x xs)


(* setmap : 'a bin -> 'a set -> 'a option
 * REQUIRES: f is well-defined over S
 * ENSURES: setmap f S ==> S' where mathematically f S = S'.
 *)
fun setmap (f : 'a -> 'b) (Set L : 'a set) : 'b set = Set (map f L)


(* needs setmappartial here. *)


(* setmap : 'a bin -> 'a set -> 'a option
 * REQUIRES: f is well-defined over S
 * ENSURES: setmap f S ==> S' where mathematically f S = S'.
 *)
fun setpick (f : 'a pred) (Set L : 'a set) : 'a set = Set (List.filter f L)


(* U : 'a cong -> 'a set -> 'a set -> 'a set
 * REQUIRES: eq is total
 * ENSURES: U eq L R ==> S, where S is the union of L and R. This means 
 *  for all x : 'a, we have setin eq S x iff setin eq L x or setin eq R x.
 *  Note that this function will not produce extra dupes.
 *)
fun U (eq : 'a cong) (Set [] : 'a set) (R : 'a set) : 'a set = R
  | U eq (Set (x::xs)) R = let 
                         val mid = U eq (Set xs) R
                       in
                         if setin eq R x then mid else setadd eq mid x
                       end


(* N : 'a cong -> 'a set -> 'a set -> 'a set
 * REQUIRES: eq is total
 * ENSURES: N eq L R ==> S, where S is the intersect of L and R. This means 
 *  for all x : 'a, we have setin eq S x iff setin eq L x and setin eq R x.
 *  Note that this function will not produce extra dupes.
 *)
fun N (eq : 'a cong) (Set [] : 'a set) (R : 'a set) : 'a set = Set []
  | N eq (Set (x::xs)) R = let
                           val mid = N eq (Set xs) R
                         in
                           if setin eq R x then setadd eq mid x else mid
                         end


(* setminus : 'a cong -> 'a set -> 'a set -> 'a set
 * REQUIRES: eq is total
 * ENSURES: setminus eq L R ==> S, where S is mathematically L \ R. This means 
 *  for all x : 'a, we have setin eq S x iff setin eq L x and setnin eq R x.
 *  Note that this function will not produce extra dupes.
 *)
fun setminus (eq : 'a cong) (Set [] : 'a set) (R : 'a set) : 'a set = Set []
  | setminus eq (Set (x::xs)) R = let
                                  val mid = setminus eq (Set xs) R
                                in
                                  if setin eq R x then mid else setadd eq mid x
                                end


(* X : 'a cong -> 'a set -> 'a set -> ('a * 'a) set
 * REQUIRES: eq is total
 * REQUIRES: (no_dupes eq L andalso no_dupes eq R) ==> true.
 * ENSURES: X eq L R = S, where S is the cartesian product of L and R.
 *)
fun X (Set L) (Set R) 
  = let
      fun arrX ([] : 'a list) (R : 'a list) : ('a * 'a) list = []
        | arrX (x::xs) R = foldr (op::) (arrX xs R) (map (fn r => (x, r)) R)
    in
      Set (arrX L R)
    end


(* enum : int -> int set
 * REQUIRES: n >= 0
 * ENSURES: enum n ==> S where S is a set containing exactly all 
 *  x : int that satisfy 0 <= x and x <= n.
 *)
fun enum n 
  = let
      fun enumlist 0 = [0] 
        | enumlist n = n :: enumlist (n-1)
    in
      Set (enumlist n)
    end


(* fact : int => int
 * REQUIRES: n >= 0
 * ENSURES: fact n ==> n! mathematically speaking. 
 *  Note that "fun fact 0 = 1" is a meme itself from CMU 15-150. 
 *)
fun fact 0 = 1 | fact n = n * fact (n-1)


(* ipart : int set -> int -> int
 * REQUIRES: setfold Int.min S ==> SOME (x) and x > 0.
 * ENSURES: ipart S n ==> k, where k is the number of ways to 
 *  sum up to n using each element in S zero or more times.
 *)
fun ipart (Set [] : int set) (n : int) : int = 0 
  | ipart (Set [x]) n = if n mod x = 0 then 1 else 0
  | ipart (Set (x::l)) n = if x > n then ipart (Set l) n
                           else ipart (Set (x::l)) (n-x) + ipart (Set l) n;


(* fun cps_fact 0 f = f (1) 
  | cps_fact n f = fact (n-1) (f o (fn x => n * x)) *)

(* fun cps_part n [] h = h 0
  | cps_part n [x] h = if n mod x = 0 then h 1 else h 0
  | cps_part n (x::l) h = 
    if x > n then cps_part n l h
    else cps_part (n-x) (x::l) (fn p1 => cps_part n l (fn p2 => h (p1 + p2))) 
*)