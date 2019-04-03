(*** Boolean unification in SML

ML Programs from Chapter 10 of

  Term Rewriting and All That
  by Franz Baader and Tobias Nipkow,
  (Cambridge University Press, 1998)

Copyright (C) 1998 by Cambridge University Press.
Permission to use without fee is granted provided that this copyright
notice is included in any copy.
***)

type monomial = int list;
type polynomial = monomial list;

(* ordVar: int * int -> order *)
fun ordVar(i,j:int) = if i=j then EQ else if i>j then GR else NGE;

(* addPP: polynomial * polynomial -> polynomial *)
fun addPP(p,[]) = p
  | addPP([],q) = q
  | addPP(m::p,n::q) = (case Lex ordVar (m,n) of
                           GR => n::addPP(m::p,q)
                         | EQ => addPP(p,q)
                         | NGE => m::addPP(p,n::q));

(* mulMM: monomial * monomial -> monomial *)
fun mulMM([],n) = n
  | mulMM(m,[]) = m
  | mulMM(a::m,b::n) = (case ordVar(a,b) of
                            EQ => a::mulMM(m,n)
                          | GR => b::mulMM(a::m,n)
                          | NGE => a::mulMM(m,b::n));

(* mulMP: monomial * polynomial -> polynomial *)
fun mulMP(m,[]) = []
  | mulMP(m,n::p) = addPP([mulMM(m,n)], mulMP(m,p));

(* mulPP: polynomial * polynomial -> polynomial *)
fun mulPP([],p) = []
  | mulPP(m::p,q) = addPP(mulMP(m,q), mulPP(p,q));

type subst = (int * polynomial) list;

(* substM: subst * monomial -> polynomial *)
fun substM(s,[]) = [[]]
  | substM(s,i::m) = if indom i s then mulPP(app s i, substM(s,m))
                     else mulMP([i], substM(s,m));

(* substP: subst * polynomial -> polynomial *)
fun substP(s,[]) = []
  | substP(s,m::p) = addPP(substM(s,m),substP(s,p));

(* decomp2: int * polynomial * polynomial * polynomial
            -> polynomial * polynomial *)
fun decomp2(_, [], r, s) = (r,s)
  | decomp2(x, (y::m)::p, r, s) =
      if x=y then decomp2(x, p, r@[m], s) else (r, s@(y::m)::p);

(* decomp: polynomial -> int * (polynomial * polynomial) *)
fun decomp ([]::(x::m)::p) = (x, decomp2(x,p,[m],[[]]))
  | decomp ((x::m)::p) = (x, decomp2(x,p,[m],[]));

exception BUnify;

fun bu [] = []
  | bu [[]] = raise BUnify
  | bu t =
      let val (x,(r,s)) = decomp t
          val r1  = addPP([[]],r)
          val u   = bu(mulPP(r1,s))
          val r1u = substP(u,r1)
          val su  = substP(u,s)
      in (x,addPP(mulMP([x],r1u),su)) :: u end;
