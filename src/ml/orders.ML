(*** A library of SML functions for partial/strict/quasi orders

ML Programs from Chapter 2 of

  Term Rewriting and All That
  by Franz Baader and Tobias Nipkow,
  (Cambridge University Press, 1998)

Copyright (C) 1998 by Cambridge University Press.
Permission to use without fee is granted provided that this copyright
notice is included in any copy.
***)

datatype order = GR | EQ | NGE;

(* lex: ('a * 'b -> order) -> 'a list * 'b list -> order *)
fun lex ord ([],[]) = EQ
  | lex ord (x::xs,y::ys) = case ord(x,y) of
        GR => GR
      | EQ => lex ord (xs,ys)
      | NGE => NGE;

(* Lex: ('a * 'b -> order) -> 'a list * 'b list -> order *)
fun Lex ord ([], [])       = EQ
  | Lex ord ([], _::_)     = NGE
  | Lex ord (_::_, [])     = GR
  | Lex ord (x::xs, y::ys) = (case ord(x,y) of
                               GR  => GR
                             | EQ  => Lex ord (xs,ys)
                             | NGE => NGE);

(* rem1: ('a * 'b -> order) -> 'a list -> 'b -> 'a list *)
fun rem1 ord ([], _)    = []
  | rem1 ord (x::xs, y) = if ord(x,y) = EQ then xs
                          else x :: (rem1 ord (xs, y));

(* mdiff: ('a * 'b -> order) -> 'a list -> 'b list -> 'a list *)
fun mdiff ord (xs, [])    = xs
  | mdiff ord (xs, y::ys) = mdiff ord (rem1 ord (xs,y), ys);

(* mul: ('a * 'a -> order) -> 'a list * 'a list -> order *)
fun mul ord (ms,ns) =
  let val nms = mdiff ord (ns,ms)
      val mns = mdiff ord (ms,ns)
  in if null(nms) andalso null(mns) then EQ
     else if forall (fn n => exists (fn m => ord(m,n)=GR) mns) nms
          then GR else NGE
  end;
