(*** A library of standard functions for Standard ML

ML Programs from Appendix 2 of

  Term Rewriting and All That
  by Franz Baader and Tobias Nipkow,
  (Cambridge University Press, 1998)

Copyright (C) 1998 by Cambridge University Press.
Permission to use without fee is granted provided that this copyright
notice is included in any copy.
***)

(* concat: 'a list list -> 'a list *)
fun concat []      = []
  | concat (x::xs) = x @ (concat xs);

(* exists: ('a -> bool) -> 'a list -> bool *)
fun exists p []      = false
  | exists p (x::xs) = p(x) orelse exists p xs;

(* forall: ('a -> bool) -> 'a list -> bool *)
fun forall p []      = true
  | forall p (x::xs) = p(x) andalso forall p xs;

(* null: 'a list -> bool *)
fun null []     = true
  | null (_::_) = false;

(* zip: 'a list * 'b list -> ('a * 'b) list *)
fun zip ([], [])      = []
  | zip (x::xs, y::ys) = (x,y) :: zip(xs,ys);
