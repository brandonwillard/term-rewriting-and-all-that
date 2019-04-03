(*** Combination of decision procedures for word problems

ML Programs from Chapter 9 of

  Term Rewriting and All That
  by Franz Baader and Tobias Nipkow,
  (Cambridge University Press, 1998)

Copyright (C) 1998 by Cambridge University Press.
Permission to use without fee is granted provided that this copyright
notice is included in any copy.
***)

fun theory(V _) = 0
  | theory(T(f,_)) = case f of "f" => 1 | "g" => 2 | "h" => 3;

fun varEq _ (x,y) = x=y;

fun commEq eq =
  let fun ceq (T("f",[s,t]), T("f",[u,v])) =
            (ceq(s,u) andalso ceq(t,v)) orelse
            (ceq(s,v) andalso ceq(t,u))
        | ceq (s,t) = eq(s,t)
  in ceq end;

fun assocEq eq (s,t) =
  let fun fringe(T("g",[s,t])) = (fringe s) @ (fringe t)
        | fringe(t) = [t];
      val fs = fringe s;
      val ft = fringe t
  in (length fs = length ft) andalso forall eq (zip(fs,ft)) end;

fun idempEq eq (s,t) =
  let fun seq (T("h",[s,t]), T("h",[u,v])) = seq(s,u) andalso seq(t,v)
        | seq (s,t)                        = eq(s,t)
      fun collapse(T("h",[s,t])) =
            let val cs = collapse s
                val ct = collapse t
            in if seq(cs,ct) then cs else T("h",[cs,ct]) end
        | collapse t = t
  in seq(collapse s, collapse t) end;

fun eq 0 = varEq
  | eq 1 = commEq
  | eq 2 = assocEq
  | eq 3 = idempEq;

fun cfeq (s,t) = (theory s = theory t)  andalso  (eq (theory s) cfeq (s,t));

(* aliens: int -> term -> term list *)
fun aliens k t = if theory(t) <> k then [t]
                else case t of V _     => []
                             | T(_,ts) => concat(map (aliens k) ts);

(* collapse: term -> term *)
fun collapse t =
  let fun collAliens k t = (case t of
            V _ => t
          | T(f,ts) => if theory(t) <> k then coll t
                       else T(f, map (collAliens k) ts))
      and coll s =
            let val k = theory s
                val t = collAliens k s
                fun try [] = t
                  | try (u::us) = if eq k cfeq (t,u) then u else try us
            in try(aliens k t) end
  in coll t end;

fun eqE (s,t) = cfeq (collapse s, collapse t);
