(*** Recursive path orders in SML

ML Programs from Chapter 5 of

  Term Rewriting and All That
  by Franz Baader and Tobias Nipkow,
  (Cambridge University Press, 1998)

Copyright (C) 1998 by Cambridge University Press.
Permission to use without fee is granted provided that this copyright
notice is included in any copy.
***)

(* (string * string -> order) -> term * term -> order *)
fun lpo ord (s,t) = case (s,t) of
      (s, V x) => if s = t then EQ
                  else if occurs x s then GR (*LaTeX{\bf{LPO1}}*) else NGE
    | (V _, T _) => NGE
    | (T(f,ss), T(g,ts)) => (*LaTeX{\bf{LPO2}}*)
        if forall (fn si => lpo ord (si,t) = NGE) ss
        then case ord(f,g) of
               GR => if forall (fn ti => lpo ord (s,ti) = GR) ts
                      then GR (*LaTeX{\bf{LPO2b}}*) else NGE
             | EQ => if forall (fn ti => lpo ord (s,ti) = GR) ts
                      then lex (lpo ord) (ss,ts) (*LaTeX{\bf{LPO2c}}*)
                      else NGE
             | NGE => NGE
        else GR (*LaTeX{\bf{LPO2a}}*);

(* rpo: (string -> (term * term -> order) -> term list * term list -> order)
        -> (string * string -> order) -> term * term -> order *)
fun rpo stat ord (s,t) = case (s,t) of
      (s, V x) => if s = t then EQ
                  else if occurs x s then GR else NGE
    | (V _, T _) => NGE
    | (T(f,ss), T(g,ts)) =>
        if forall (fn si => rpo stat ord (si,t) = NGE) ss
        then case ord(f,g) of
               GR => if forall (fn ti => rpo stat ord (s,ti) = GR) ts
                      then GR else NGE
             | EQ => if forall (fn ti => rpo stat ord (s,ti) = GR) ts
                      then (stat f) (rpo stat ord) (ss,ts)
                      else NGE
             | NGE => NGE
        else GR;
