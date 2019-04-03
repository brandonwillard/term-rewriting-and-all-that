(*** Computation of critical pairs in SML

ML Programs from Chapter 6 of

  Term Rewriting and All That
  by Franz Baader and Tobias Nipkow,
  (Cambridge University Press, 1998)

Copyright (C) 1998 by Cambridge University Press.
Permission to use without fee is granted provided that this copyright
notice is included in any copy.
***)

fun max(i,j:int) = if i > j then i else j;

(* maxs: int list -> int *)
fun maxs (i::is) = max(i, maxs is)
  | maxs []     = 0;

(* maxindex: term -> int *)
fun maxindex (V(x,i))  = i
  | maxindex (T(_,ts)) = maxs(map maxindex ts);

(* rename: int -> term -> term *)
fun rename n (V(x,i))  = V(x,i+n)
  | rename n (T(f,ts)) = T(f, map (rename n) ts);

(* CP: (term -> term) -> term * term -> term * term -> (term * term) list *)
fun CP C (t,r) (l2,r2) = let val sigma = lift(unify(t,l2))
                         in [(sigma r, sigma(C r2))] end
                         handle UNIFY => [];

(* CPs: (term * term) list -> term * term -> (term * term) list *)
fun CPs R (l,r) =

  let fun cps C (V _, _) = []
        | cps C (T(f,ts),r) =
            concat(map (CP C (T(f,ts),r)) R) @ (innercps C (f,[],ts,r))

      and innercps _ (_, _, [], _) = []
        | innercps C (f, ts0, t::ts1, r) =
            let fun Cf s = C(T(f, ts0 @ [s] @ ts1))
            in (cps Cf (t,r)) @ (innercps C (f, ts0 @ [t], ts1, r)) end

      val m = maxs(map (fn (l,r) => max(maxindex l, maxindex r)) R) + 1

  in cps (fn t => t) (rename m l, rename m r) end;

fun CriticalPairs2 R1 R2 = concat(map (CPs R1) R2);

fun CriticalPairs R = CriticalPairs2 R R;
