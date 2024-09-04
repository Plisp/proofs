open bossLib;
open itreeTauTheory;
open relationTheory;
open pathTheory;
open arithmeticTheory;
open finite_mapTheory;

val m = Hol_pp.print_apropos;
val f = Hol_pp.print_find;

Definition weak_tau_def:
  weak_tau m = RTC (λs s'. m s NONE s')
End

Definition weak_trans_def:
  weak_trans m s e s' =
  (∃s'' s'''.
     weak_tau m s s'' ∧
     m s'' (SOME e) s''' ∧
     weak_tau m s''' s')
End

CoInductive safe:
[~ret]
  (∀s r m. safe m s (Ret r))
[~tau]
  (∀s t m. (∀s'. weak_tau m s s' ⇒ safe m s' t) ⇒
   safe m s (Tau t))
[~vis]
  (∀e k s m.
   (∀s'. weak_tau m s s' ⇒ ∃b s''. m s' (SOME(e,b)) s'') ∧
   (∀b s'. weak_trans m s (e,b) s' ⇒
           safe m s' (k b))
   ⇒ safe m s (Vis e k))
End

Datatype:
  prog = Comm 'ffi | Branch ('answer list -> bool) (prog list) (prog list)
End

Definition comp:
  comp locals l =
  case l of
    [] => Ret ()
  | (Comm ffi)::cs => Vis ffi (λa. comp (locals ++ [a]) cs)
  | (Branch c t f)::_ => if c locals
                         then comp locals t
                         else comp locals f
Termination
  cheat
End

Inductive psafe:
[~single]
  (∀m. psafe m [] [s])
[~base]
  (∀m. weak_trans m s e s' ⇒ psafe m [e] [s;s'])
[~vis]
  (∀m. psafe m as (ss ++ [s]) ∧ weak_trans m s e s' ⇒
       psafe m (as ++ [e]) (ss ++ [s;s']))
End

(* XXX failure in translation to tupled format *)
(* Definition gen_hyp: *)
(*   gen_hyp m prog locals = *)
(*   case prog of *)
(*     [] => (λs t. ∃r. t = Ret r) *)
(*   | (Comm ffi :: cs) *)
(*     => (λs t. ∃sts hist x. *)
(*          ((psafe m (ZIP (hist,locals)) sts ∧ *)
(*            s = LAST sts ∧ *)
(*            t = comp (locals ++ [x]) cs) ∨ *)
(*           (gen_hyp m cs (locals ++ [x]) s t))) *)
(*   | (Branch c tb fb :: _) *)
(*     => (λs t. T) (* hyp m s t ∨ *) *)
(* End *)

Definition gen_hyp:
  gen_hyp m prog locals assms s t =
  case prog of
    [] => (∃r. t = Ret r)
  | (Comm ffi :: cs)
    => (∃x. (∃sts hist.
              psafe m (ZIP (hist,locals)) sts ∧
              s = LAST sts ∧
              t = comp (locals ++ [x]) cs) ∨
            gen_hyp m cs (locals ++ [x]) assms s t)
  | (Branch c tb fb :: _)
    => (gen_hyp m tb locals (assms |+ (s,(λlocs. c locs = T))) s t ∨
        gen_hyp m fb locals (assms |+ (s,(λlocs. c locs = F))) s t)
Termination
  cheat
End

Definition curry_hyp:
  curry_hyp hyp trans = (λm s t. m = trans ∧ hyp trans s t)
End

(* example *)

Datatype:
  ffi = Send num | Recv | Qsize1 | Qsize2
End

Datatype:
  answer = Size num | Unit | Packet num
End

Definition get_no:
  get_no (Size x) = x ∧
  get_no (Packet x) = x
End

Inductive trans:
  trans (q1, q2) (SOME (Qsize1, Size (LENGTH q1))) (q1, q2) ∧
  trans (a::q1, q2) (SOME (Recv, Packet a)) (q1,q2) ∧
  trans (q1,q2) NONE (q1++[p], q2)
  ∧
  trans (q1, q2) (SOME (Qsize2, Size (LENGTH q2))) (q1, q2) ∧
  (LENGTH q2 < 5 ⇒ trans (q1, q2) (SOME (Send n, Unit)) (q1,q2 ++ [n])) ∧
  trans (q1, p::q2) NONE (q1, q2)
End

Datatype:
  prog = Comm ffi | Branch (answer list -> bool) (prog list) (prog list)
End

Definition rxdriver_code:
  rxdriver = [Comm Qsize1
              ;Comm Qsize2
              ;Branch (λl. case l of [x;y] => get_no x = 0 ∨ get_no y ≥ 5)
                      []
                      [Comm Recv ; Comm (Send 0)]]
End




Definition rxdriver_def:
  rxdriver = Vis Qsize1
                 (λx. Vis Qsize2
                          (λy. if get_no x = 0 ∨ get_no y ≥ 5
                               then Ret ()
                               else Vis Recv
                                        (λ(z : answer).
                                           Vis (Send (get_no z))
                                               (λ_. Ret ()))))
End

Theorem rxdriver:
  rxdriver = Vis Qsize1 (λx. Vis Qsize2 (λy.
             if get_no x = 0 ∨ get_no y ≥ 5 then Tau rxdriver
             else Vis Recv (λz. Vis (Send (get_no z)) (λ_. Ret ()))))
Proof
  rw[SimpL “$=”, rxdriver_def] >>
  gvs[Once itree_iter_thm, itree_bind_thm, FUN_EQ_THM] >>
  strip_tac >> strip_tac >>
  Cases_on ‘get_no x ≤ 0 ∨ get_no y >= 5’
  >- (simp[rxdriver_def]) >>
  gvs[Once itree_iter_thm, itree_bind_thm, FUN_EQ_THM]
QED



Theorem increasing_q1:
  weak_tau trans s s' ⇒ LENGTH (FST s) ≤ LENGTH (FST s')
Proof
  fs[weak_tau_def] >>
  Induct_on ‘RTC’ >>
  rw[] >>
  subgoal ‘LENGTH (FST s) ≤ LENGTH (FST s')’
  >- (rw[trans_cases] >> fs[trans_cases]) >>
  gvs[]
QED

Theorem decreasing_q2_tau:
  weak_tau trans s s' ⇒ LENGTH (SND s) ≥ LENGTH (SND s')
Proof
  fs[weak_tau_def] >>
  Induct_on ‘RTC’ >>
  rw[] >>
  subgoal ‘LENGTH (SND s) ≥ LENGTH (SND s')’
  >- (rw[Once trans_cases] >> fs[trans_cases]) >>
  gvs[]
QED

Theorem decreasing_q2_trans:
  weak_trans trans s (Recv, b) s' ⇒ LENGTH (SND s') ≤ LENGTH (SND s)
Proof
  rw[weak_trans_def] >>
  subgoal ‘LENGTH (SND s) ≥ LENGTH (SND s'') ∧ LENGTH (SND s'³') ≥ LENGTH (SND s')’
  >- gvs[decreasing_q2_tau] >>
  subgoal ‘LENGTH (SND s'') = LENGTH (SND s'³')’
  >- gvs[trans_cases] >> gvs[]
QED

Theorem increasing_q1_trans:
  weak_trans trans s (Qsize1, b) s' ⇒ get_no b ≤ LENGTH (FST s')
Proof
  rw[weak_trans_def] >>
  subgoal ‘LENGTH (FST s'³') ≤ LENGTH (FST s')’
  >- gvs[increasing_q1] >>
  subgoal ‘get_no b = LENGTH (FST s'³')’
  >- gvs[trans_cases, get_no] >> gvs[]
QED

Theorem Qsize2_trans:
  weak_trans trans s (Qsize2, b) s' ⇒ (get_no b ≥ LENGTH (SND s') ∧ LENGTH (FST s) ≤ LENGTH (FST s'))
Proof
  rw[Once weak_trans_def]
  >- (subgoal ‘LENGTH (SND s'³') ≥ LENGTH (SND s') ∧ get_no b = LENGTH (SND s'³')’
      >- gvs[decreasing_q2_tau, trans_cases, get_no] >> gvs[])
  >- (subgoal ‘LENGTH (FST s) ≤ LENGTH (FST s'') ∧
               LENGTH (FST s'³') ≤ LENGTH (FST s') ∧
               LENGTH (FST s'') = LENGTH (FST s'³')’
      >- gvs[increasing_q1, trans_cases] >> gvs[])
QED



Theorem safe_driver:
  safe trans ([],[]) rxdriver
Proof
  irule safe_coind >>
  qexists_tac ‘λm s t. ∃q1 q2. m = trans ∧ s = (q1, q2) ∧
                           ((LENGTH q1 > 0 ∧ LENGTH q2 < 5 ∧
                             strip_tau t (Vis Recv (λz. Vis (Send (get_no z)) (λ_. Ret ())))) ∨
                           (LENGTH q2 < 5 ∧ ∃z. strip_tau t (Vis (Send z) (λ_. Ret ()))) ∨
                           (∃x.
                             strip_tau t (Ret ()) ∨ (* can be 5 now *)
                             strip_tau t rxdriver ∨
                             ((get_no x > 0 ⇒ LENGTH q1 > 0) ∧
                              strip_tau t (Vis Qsize2 (λy.
                                            if get_no x = 0 ∨ get_no y ≥ 5 then Tau rxdriver
                                            else Vis Recv (λz. Vis (Send (get_no z)) (λ_. Ret ())))))))’ >>
  rw[] >> gvs[Once strip_tau_cases] >> rw[]
  >- (Cases_on ‘s'’ >> drule increasing_q1 >> drule decreasing_q2_tau >> gvs[])
  >- (Cases_on ‘s'’ >> Cases_on ‘q’ >> drule increasing_q1 >> rw[] >> gvs[trans_cases])
  >- (Cases_on ‘s'’ >> drule decreasing_q2_trans >> gvs[])
  >- (Cases_on ‘s'’ >> drule decreasing_q2_tau >> gvs[] >> metis_tac[])
  >- (Cases_on ‘s'’ >> drule decreasing_q2_tau >> gvs[trans_cases])
  >- (Cases_on ‘s'’ >> gvs[]) >- (Cases_on ‘s'’ >> gvs[]) >- (Cases_on ‘s'’ >> gvs[])
  >- (ntac 2 $ disj2_tac >> rw[Once rxdriver] >> Cases_on ‘s'’ >> gvs[trans_cases] >>
      qexists ‘b’ >> drule increasing_q1_trans >> gvs[])
  >- (Cases_on ‘s'’ >> gvs[] >> ntac 2 $ disj2_tac >> qexists ‘x’ >> drule increasing_q1 >> gvs[])
  >- (Cases_on ‘s'’ >> gvs[trans_cases])
  >- (Cases_on ‘s'’ >> metis_tac[strip_tau_cases, rxdriver])
  >- (Cases_on ‘s'’ >> metis_tac[strip_tau_cases, rxdriver])
  >- (Cases_on ‘s'’ >> rw[] >> drule Qsize2_trans >> gvs[])
  >- metis_tac[strip_tau_cases, rxdriver]
QED
