(*** The basics of term rewriting: terms, unification, matching, normalization

ML Programs from Chapter 4 of

  Term Rewriting and All That
  by Franz Baader and Tobias Nipkow,
  (Cambridge University Press, 1998)

Copyright (C) 1998 by Cambridge University Press.
Permission to use without fee is granted provided that this copyright
notice is included in any copy.
***)

type vname = string * int;

datatype term = V of vname | T of string * term list;

(* indom: vname -> subst -> bool *)
fun indom x s = exists (fn (y,_) => x = y) s;

(* app: subst -> vname -> term *)
fun app ((y,t)::s) x  =  if x=y then t else app s x;

(* lift: subst -> term -> term *)
fun lift s (V x)    = if indom x s then app s x else V x
  | lift s (T(f,ts)) = T(f, map (lift s) ts);

(* occurs: vname -> term -> bool *)
fun occurs x (V y)    = x=y
  | occurs x (T(_,ts)) = exists (occurs x) ts;

exception UNIFY;

(* solve: (term * term)list * subst -> subst *)
fun solve([], s) = s
  | solve((V x, t) :: S, s) =
      if V x = t then solve(S,s) else elim(x,t,S,s)
  | solve((t, V x) :: S, s) = elim(x,t,S,s)
  | solve((T(f,ts),T(g,us)) :: S, s) =
      if f = g then solve(zip(ts,us) @ S, s) else raise UNIFY

(* elim: vname * term * (term * term) list * subst -> subst *)
and elim(x,t,S,s) =
      if occurs x t then raise UNIFY
      else let val xt = lift [(x,t)]
           in solve(map (fn (t1,t2) => (xt t1, xt t2)) S,
                    (x,t) :: (map (fn (y,u) => (y, xt u)) s))
           end;

(* unify: term * term -> subst *)
fun unify(t1,t2) = solve([(t1,t2)], []);

(* matchs: (term * term) list * subst -> subst *)
fun matchs([], s) = s
  | matchs((V x, t) :: S, s) =
      if indom x s then if app s x = t then matchs(S,s) else raise UNIFY
      else matchs(S,(x,t)::s)
  | matchs((t, V x) :: S, s) = raise UNIFY
  | matchs((T(f,ts),T(g,us)) :: S, s) =
      if f = g then matchs(zip(ts,us) @ S, s) else raise UNIFY;

(* match: term * term -> subst *)
fun match(pat,obj) = matchs([(pat,obj)],[]);

exception NORM;

(* rewrite: (term * term) list -> term -> term *)
fun rewrite [] t = raise NORM
  | rewrite ((l,r)::R) t = lift(match(l,t)) r
                          handle UNIFY => rewrite R t;

(* norm: (term * term) list -> term -> term *)
fun norm R (V x) = V x
  | norm R (T(f,ts)) =
      let val u = T(f, map (norm R) ts)
      in (norm R (rewrite R u))  handle NORM => u  end;
