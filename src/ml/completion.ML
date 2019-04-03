(*** Completion a la Huet in SML

ML Programs from Chapter 7 of

  Term Rewriting and All That
  by Franz Baader and Tobias Nipkow,
  (Cambridge University Press, 1998)

Copyright (C) 1998 by Cambridge University Press.
Permission to use without fee is granted provided that this copyright
notice is included in any copy.
***)

(* size: term -> int *)
fun size(V _) = 1
  | size(T(_,ts)) = sizes ts + 1
and sizes [] = 0
  | sizes(t::ts) = size t + sizes ts;

(* minRule: (term * term) * int * ids * ids -> (term * term) * ids *)
fun minRule(rl,n,[],      R') = (rl,R')
  | minRule(rl,n,(l,r)::R,R') =
      let val m = size l + size r
      in if m < n then minRule((l,r),m,R,rl::R')
                   else minRule(rl,n,R,(l,r)::R')
      end;

fun choose((l,r)::R) = minRule((l,r), size l + size r, R, []);

(* addRule: term * term * ids * ids * ids -> ids * ids * ids *)
fun addRule(l,r,E,S,R) =
  let fun simpl([],E',R') = (E',R')
        | simpl((g,d)::U,E',U') =
            let val g' = norm [(l,r)] g
            in if g' = g then let val d' = norm ((l,r)::R@S) d
                              in simpl(U, E', (g,d')::U') end
               else simpl(U, (g',d)::E', U')
            end
      val (E',S')  = simpl(S,E,[])
      val (E'',R') = simpl(R,E',[])
  in (E'', (l,r)::S', R') end;

exception FAIL;

(* orient: (term * term -> order) -> ids * ids * ids -> ids * ids *)
fun orient ord =
  let fun ori([],S,R) = (S,R)
        | ori((s,t)::E,S,R) =
            let val s' = norm (R@S) s
                val t' = norm (R@S) t
            in if s' = t' then ori(E,S,R) else
               if ord(s',t')=GR then ori(addRule(s',t',E,S,R)) else
               if ord(t',s')=GR then ori(addRule(t',s',E,S,R)) else raise FAIL
            end
  in ori end;

type ids = (term * term) list;

(* complete: (term * term -> order) -> ids -> ids *)
fun complete ord E =
  let fun compl(E,S,R) = case orient ord (E,S,R) of
            ([],R') => R'
          | (S',R') => let val (rl,S'') = choose S'
                           val cps = CriticalPairs2 [rl] R' @
                                     CriticalPairs2 R' [rl] @
                                     CriticalPairs2 [rl] [rl]
                       in compl(cps,S'',rl::R') end
  in compl(E,[],[]) end;
