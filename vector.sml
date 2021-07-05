datatype vector = v of real list;

fun sum ([] : real list) = 0.0 | sum (l::L) = l + sum L

fun square x : real = x * x

infix **

fun x**0 = x | x**n = case n mod 2 of 1 => x * (x**(n-1)) | 0 => square (x**(n div 2))

fun abs x : real = ~1.0 * x if Real.compare (x, 0.0) = LESS orelse x

fun numSqrtH (x : real, i : real) = case Real.compare (x, i*i) of
                                      LESS =

fun numSqrt x : real = fun numSqrtH (x, 0)

fun norm (v(l), p) = sum (map (fn x => x**p) l)