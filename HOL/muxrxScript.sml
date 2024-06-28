(*/ spec combinators
   - temporal logic?
 *)

(* future but with assumption that bytes written back fit in the passed array *)
Inductive future_safe:
  (P t ⇒ future_safe P t) ∧
  (future_safe P t ⇒ future_safe P (Tau t)) ∧
  (∀k s conf array.
    (∀outcome. future_safe P (k (FFI_final outcome))) ∧
    (∀new_ffi new_bytes. (LENGTH new_bytes = LENGTH array) ⇒
                         future_safe P (k (FFI_return new_ffi new_bytes)))
    ⇒ future_safe P (Vis (FFI_call s conf array) k))
End

val skip_tau = rw[Once future_safe_cases] >> disj2_tac;

(* needs to be α for type vars to match *)
Theorem future_safe_ignore_tau[simp]:
  (∀(t' : α sem32tree). ¬P (Tau t')) ⇒ (future_safe P (Tau t) ⇔ future_safe P t)
Proof
  rw[] >> rw[Once future_safe_cases]
QED

(*/ real
   XXX there's a semantic error caused by loading from drv_dequeue_c, read-only
   XXX pancake multiple definitions? shape access checks .0.0.0.0?

fun enq({1} root, {1} e) {
    var head_a = root - 2;
    var tail_a = root - 1;
    var head = load head_a;
    var tail = load tail_a;

    store ((root + head) % 999), e;
    store head_a, (head + 1);
    return 0;
}

fun deq({1} root) {
    var head_a = root - 2;
    var tail_a = root - 1;
    var head = load head_a;
    var tail = load tail_a;

    ret = load ((root + tail) % 999);
    store tail_a, (tail + 1);
    return ret;
}

   simp[ExclSF “LET”]
   Proof[exclude_frags = LET] ...
   DEP_REWRITE_TAC
 *)

val muxrx_ast = parse_pancake ‘
fun fn() {
  var drv_dequeue_c = @base;
  var drv_dequeue_a = @base + 1;
  #drv_dequeue_used(drv_dequeue_c, 1, drv_dequeue_a, 1);
// error, should not be written
  (* var drv_dequeue_ret = ldb drv_dequeue_c; *)
  var got_char = ldb drv_dequeue_a;
  (* if drv_dequeue_ret != 0 { return 1; } *)

  // Get the current status of the escape character from the ffi file

  var escape_character_a = @base + 3;
  #get_escape_character(0,0,escape_character_a, 1);
  var escape_character = ldb escape_character_a;

  if escape_character == 1 {
      // give the char to the client, previous character was an escape character
      #escape_1(0,0,0,0);

      var client_a = @base + 4;
      #get_client(0, 0, client_a, 1);
      var client = ldb client_a;

      // Check that we have requests by this client to get a char

      var check_num_to_get_chars_a = @base + 5;
      #check_num_to_get_chars(0, 0, check_num_to_get_chars_a, 1);
      var num_to_get_chars_ret = ldb check_num_to_get_chars_a;

      if num_to_get_chars_ret == 0 {
          return 0;
      }

      // Batch the dequeue and enqueue into the client's rings

      var cli_dequeue_enqueue_c = @base + 6;
      var cli_dequeue_enqueue_a = @base + 8;
      strb cli_dequeue_enqueue_c, client;
      strb cli_dequeue_enqueue_c + 1, got_char;
      #batch_cli_dequeue_enqueue(cli_dequeue_enqueue_c,2, cli_dequeue_enqueue_a,1);

      var set_escape_character_c = @base + 9;
      strb set_escape_character_c, 0;
     #set_escape_character(set_escape_character_c, 1, 0, 0);

      return 0;
  }

  if escape_character == 2 {
      // The previous character was "@". Switch input to a new client.
      #escape_2(0,0,0,0);

      var new_client = got_char - 48;
      if new_client >= 1 {
          var get_num_clients_a = @base + 4;
          #get_num_clients(0,0,get_num_clients_a, 1);
          var num_clients = ldb get_num_clients_a;

          if new_client <= num_clients {
              var set_client_c = @base + 5;
              strb set_client_c, new_client;
             #set_client(set_client_c, 1, 0, 0);
          }
      }

      var set_escape_character_c = @base + 9;
      strb set_escape_character_c, 0; // escape off
     #set_escape_character(set_escape_character_c, 1, 0, 0);

      return 0;
  }

  if escape_character == 0 {
      // No escape character has been set
      #escape_0(0,0,0,0);

      // Ascii for '\'
      if got_char == 92 {
          #escape_case(0,0,0,0);
          var set_escape_character_c = @base + 9;
          strb set_escape_character_c, 1; // escape
         #set_escape_character(set_escape_character_c, 1, 0, 0);

         return 0;
      }

      // Ascii for '@'
      if got_char == 64 {
          #at_case(0,0,0,0);
          var set_escape_character_c = @base + 9;
          strb set_escape_character_c, 2; // escape @
         #set_escape_character(set_escape_character_c, 1, 0, 0);

         return 0;
      }

      // Otherwise we just want to give the client the character
// note: this is exactly the same as the first branch
      var client_a = @base + 4;
      #get_client(0, 0, client_a, 1);
      var client = ldb client_a;

      // Check that we have requests by this client to get a char

      var check_num_to_get_chars_a = @base + 5;
      #check_num_to_get_chars(0, 0, check_num_to_get_chars_a, 1);
      var num_to_get_chars_ret = ldb check_num_to_get_chars_a;

      if num_to_get_chars_ret == 0 {
          return 0;
      }

      // Batch the dequeue and enqueue into the client's rings

      var cli_dequeue_enqueue_c = @base + 6;
      var cli_dequeue_enqueue_a = @base + 8;
      strb cli_dequeue_enqueue_c, client;
      strb cli_dequeue_enqueue_c + 1, got_char;
      #batch_cli_dequeue_enqueue(cli_dequeue_enqueue_c,2, cli_dequeue_enqueue_a,1);

      var set_escape_character_c = @base + 9;
      strb set_escape_character_c, 0;
     #set_escape_character(set_escape_character_c, 1, 0, 0);

      return 0;
  }
  return 0;
}’;

Definition muxrx_sem_def:
  muxrx_sem (s:('a,'ffi) panSem$state) =
  itree_evaluate (SND $ SND $ HD ^muxrx_ast) s
End

Definition mux_set_escape_pred_def:
  mux_set_escape_pred (escape : word8) t =
  ((∃k.
     t = Vis (FFI_call "set_escape_character" [escape] []) k ∧
     k (FFI_return ARB []) ≈ Ret (SOME (Return (ValWord 0w)))
   )
   ∨ ∃outcome. t = Ret (SOME (FinalFFI outcome)))
End

Theorem mux_set_escape_pred_notau:
  ¬mux_set_escape_pred e (Tau (t : α sem32tree))
Proof
  rw[mux_set_escape_pred_def]
QED

Definition mux_checked_set_escape_pred_def:
  mux_checked_set_escape_pred t =
  ((∃uninit k.
     t = Vis (FFI_call "check_num_to_get_chars" [] [uninit]) k ∧
     k (FFI_return ARB [0w]) ≈ Ret (SOME (Return (ValWord 0w))) ∧
     future_safe (mux_set_escape_pred 0w) (k (FFI_return ARB [1w]))
   )
   ∨ ∃outcome. t = Ret (SOME (FinalFFI outcome)))
End

Theorem mux_checked_set_escape_pred_notau:
  ¬mux_checked_set_escape_pred e (Tau (t : α sem32tree))
Proof
  rw[mux_checked_set_escape_pred_def]
QED

Definition mux_at_pred_def:
  mux_at_pred (gchar : word32) t =
  ((gchar - 48w < 1w ⇒ mux_set_escape_pred 0w t) ∧
   (1w ≤ gchar - 48w ⇒
    ∃k uninit.
     t = Vis (FFI_call "get_num_clients" [] [uninit]) k ∧
     ∀n.
     future_safe
     (λcont. ∃k2. (gchar - 48w) ≤ w2w n ⇒
                  cont = Vis (FFI_call "set_client" [w2w (gchar - 48w)] []) k2 ∧
                  future_safe (mux_set_escape_pred 0w) (k2 (FFI_return ARB [])))
     (k (FFI_return ARB [n])))
   ∨ ∃outcome. t = Ret (SOME (FinalFFI outcome)))
End

Theorem mux_at_pred_notau:
  ¬(mux_at_pred gchar) (Tau (t : α sem32tree))
Proof
  gvs[mux_at_pred_def, mux_set_escape_pred_def] >>
  rw[wordsTheory.WORD_LESS_OR_EQ] >>
  blastLib.BBLAST_TAC
QED

Definition mux_escape_pred_def:
  mux_escape_pred (gchar : word32) t =
  (((gchar = 92w) ⇒ mux_set_escape_pred 1w t) ∧
   ((gchar = 64w) ⇒ mux_set_escape_pred 2w t) ∧
   ((gchar ≠ 92w ∧ gchar ≠ 64w) ⇒ mux_checked_set_escape_pred t))
End

Theorem mux_escape_pred_notau:
  ¬mux_escape_pred e (Tau (t : α sem32tree))
Proof
  rw[mux_escape_pred_def,mux_set_escape_pred_def,mux_checked_set_escape_pred_def] >>
  blastLib.BBLAST_TAC
QED

Definition muxrx_pred_def:
  muxrx_pred t =
  ∀c.
  (∃k1 k2 uninit1 uninit2 uninit.
    (t = Vis (FFI_call "drv_dequeue_used" [uninit1] [uninit2]) k1) ∧
    (k1 (FFI_return ARB [c]) ≈
        Vis (FFI_call "get_escape_character" [] [uninit]) k2) ∧
    (* backslash escape case, transitions to zero *)
    future_safe mux_checked_set_escape_pred (k2 (FFI_return ARB [1w])) ∧
    future_safe (mux_at_pred (w2w c)) (k2 (FFI_return ARB [2w])) ∧
    future_safe (mux_escape_pred (w2w c)) (k2 (FFI_return ARB [0w]))
  ) ∨
  (∃outcome. t = Ret (SOME (FinalFFI outcome)))
End

Theorem muxrx_pred_notau:
  ¬muxrx_pred (Tau (t : α sem32tree))
Proof
  rw[muxrx_pred_def]
QED

(*
 the proof
*)

Triviality mux_uncond_set_branch:
  ∀branch.
  future_safe (mux_set_escape_pred e) (to_ffi branch)
  ⇒ future_safe (mux_set_escape_pred e)
                (to_ffi
                 (bind branch (λ(res,s'). if res = NONE
                                          then (f res s')
                                          else Ret (res,s'))))
Proof
  Induct_on ‘future_safe’ >>
  rw[] >-
   (fs[mux_set_escape_pred_def] >-
     (rw[Once future_safe_cases] >> disj1_tac >>
      rw[mux_set_escape_pred_def] >> disj1_tac >>
      gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      rw[to_ffi_seq]) >-
     (rw[Once future_safe_cases] >> disj1_tac >>
      gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      rw[mux_set_escape_pred_def])) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases] >>
    metis_tac[])
QED

Triviality mux_set_client_branch:
  ∀t.
  future_safe (λcont. ∃k2.
                e + 0xFFFFFFD0w ≤ w2w n ⇒
                cont =
                Vis (FFI_call "set_client" [w2w (e + 0xFFFFFFD0w)] []) k2 ∧
                future_safe (mux_set_escape_pred 0w) (k2 (FFI_return ARB [])))
  (to_ffi t) ⇒
  future_safe (λcont. ∃k2.
                e + 0xFFFFFFD0w ≤ w2w n ⇒
                cont =
                Vis (FFI_call "set_client" [w2w (e + 0xFFFFFFD0w)] []) k2 ∧
                future_safe (mux_set_escape_pred 0w) (k2 (FFI_return ARB [])))
              (to_ffi (bind t (λ(res,s'). if res = NONE
                                          then (f res s')
                                          else Ret (res,s'))))
Proof
  Induct_on ‘future_safe’ >>
  rw[] >-
   (rw[Once future_safe_cases] >> disj1_tac >>
    Cases_on ‘e + 0xFFFFFFD0w ≤ w2w n’ >>
    gvs[GSYM wordsTheory.WORD_NOT_LESS_EQUAL] >>
    gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[mux_uncond_set_branch]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases] >>
    metis_tac[])
QED

Triviality set_escape_seq:
  mux_checked_set_escape_pred (to_ffi t) ⇒
  mux_checked_set_escape_pred
  (to_ffi
   (bind t
         (λ(res,s'). if res = NONE then f NONE s' else Ret (res,s'))))
Proof
  gvs[mux_checked_set_escape_pred_def] >> rw[] >-
   (disj1_tac >>
    gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs(),
        Once itree_wbisim_cases] >>
    qmatch_goalsub_abbrev_tac ‘bind t _’ >>
    qmatch_goalsub_abbrev_tac ‘future_safe _ (to_ffi (bind t1 _))’ >>
    CONJ_TAC >-
     (qpat_x_assum ‘future_safe _ _’ kall_tac >> pop_assum kall_tac >>
      pop_last_assum mp_tac >> qid_spec_tac ‘t’ >> pop_assum kall_tac >>
      Induct_on ‘strip_tau’ >> rw[] >-
       (gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()]) >>
      gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()]) >>
    qpat_x_assum ‘strip_tau _ _’ kall_tac >> rw[Abbr ‘t’] >>
    rw[mux_uncond_set_branch]) >-
   (disj2_tac >>
    gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()])
QED

Triviality mux_checked_set_branch:
  ∀t.
  future_safe mux_checked_set_escape_pred (to_ffi t) ⇒
  future_safe mux_checked_set_escape_pred
  (to_ffi
   (bind t
         (λ(res,s'). if res = NONE then f NONE s' else Ret (res,s'))))
Proof
  Induct_on ‘future_safe’ >>
  rw[] >-
   (rw[Once future_safe_cases] >> disj1_tac >> rw[set_escape_seq]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases] >>
    metis_tac[]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases] >>
    metis_tac[])
QED

Triviality mux_return_branch_at:
 ∀branch.
 future_safe (mux_at_pred e) (to_ffi branch)
 ⇒ future_safe (mux_at_pred e)
               (to_ffi
                (bind branch (λ(res,s'). if res = NONE
                                         then (f res s')
                                         else Ret (res,s'))))
Proof
  Induct_on ‘future_safe’ >>
  rw[] >-
   (rw[Once future_safe_cases] >> disj1_tac >>
    fs[mux_at_pred_def] >>
    Cases_on ‘e + 0xFFFFFFD0w < 1w’ >> gvs[GSYM wordsTheory.WORD_NOT_LESS_EQUAL] >-
     (fs[mux_set_escape_pred_def] >>
      gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      rw[to_ffi_seq]) >-
     (gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      strip_tac >> pop_last_assum $ qspec_then ‘n’ assume_tac >>
      rw[mux_set_client_branch]) >-
     (gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()]) >-
     (gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()])) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases] >>
    metis_tac[])
QED

Triviality mux_return_branch_esc:
 ∀branch.
 future_safe (mux_escape_pred e) (to_ffi branch)
 ⇒ future_safe (mux_escape_pred e)
               (to_ffi
                (bind branch (λ(res,s'). if res = NONE
                                         then (f res s')
                                         else Ret (res,s'))))
Proof
  Induct_on ‘future_safe’ >>
  rw[] >-
   (rw[Once future_safe_cases] >> disj1_tac >>
    rw[mux_escape_pred_def] >> fs[mux_escape_pred_def] >-
     (fs[mux_set_escape_pred_def] >>
      gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      rw[to_ffi_seq]) >-
     (fs[mux_set_escape_pred_def] >>
      gvs[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
      rw[to_ffi_seq]) >-
     (fs[set_escape_seq])) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases]) >-
   (pop_assum mp_tac >>
    rw[Once $ DefnBase.one_line_ify NONE to_ffi_alt, AllCaseEqs()] >>
    rw[Once future_safe_cases] >>
    metis_tac[])
QED

Theorem escape_pred_to_backslash:
  ∀t. future_safe mux_checked_set_escape_pred t
      ⇒ (w2w c) ≠ (92w : word32) ∧ (w2w c) ≠ (64w : word32)
      ⇒ future_safe (mux_escape_pred (w2w c)) t
Proof
  Induct_on ‘future_safe’ >>
  rw[] >-
   (rw[Once future_safe_cases] >> disj1_tac >>
    rw[mux_escape_pred_def]) >-
   (rw[Once future_safe_cases] >> disj2_tac >>
    pop_last_assum irule >>
    gvs[Once future_safe_cases] >>
    fs[mux_checked_set_escape_pred_notau]) >>
  rw[Once future_safe_cases]
QED

(*
  proof TODO fix alignment assumption
 *)

Definition muxrx_mem_assms:
  muxrx_mem s =
  ((∀(w : word32). w ∈ (s : (32,α) state).memaddrs) ∧
  (byte_align s.base_addr = s.base_addr) ∧
  (byte_align (s.base_addr + 1w) = s.base_addr) ∧
  (byte_align (s.base_addr + 3w) = s.base_addr) ∧
  (byte_align (s.base_addr + 4w) = s.base_addr) ∧
  (byte_align (s.base_addr + 5w) = s.base_addr) ∧
  (byte_align (s.base_addr + 6w) = s.base_addr) ∧
  (byte_align (s.base_addr + 7w) = s.base_addr) ∧
  (byte_align (s.base_addr + 8w) = (s.base_addr + 8w)) ∧
  (byte_align (s.base_addr + 9w) = (s.base_addr + 8w)) ∧
  mem_has_word s.memory s.base_addr ∧
  mem_has_word s.memory (s.base_addr + 8w))
End

Theorem escape_set_branch:
  muxrx_mem (s : (32, α) state)
  ⇒
  future_safe
  (mux_checked_set_escape_pred : α sem32tree -> bool)
  (to_ffi
   (bind
    (itree_mrec h_prog
                (ExtCall «get_client» (Const 0w) (Const 0w)
                         (Var «client_a») (Const 1w),
                 s with
                   <|locals :=
                     s.locals |+ («drv_dequeue_c»,ValWord s.base_addr) |+
                      («drv_dequeue_a»,ValWord (s.base_addr + 1w)) |+
                      («got_char»,ValWord (w2w c)) |+
                      («escape_character_a»,ValWord (s.base_addr + 3w)) |+
                      («escape_character»,ValWord (w2w x)) |+
                      («client_a»,ValWord (s.base_addr + 4w));
                     memory :=
                     write_bytearray
                     (s.base_addr + 3w) [x]
                     (write_bytearray (s.base_addr + 1w) [c] s.memory
                                      s.memaddrs s.be) s.memaddrs s.be;
                     ffi := new_ffi|>))
    (λ(res,s').
       if res = NONE then
         Tau
         (itree_mrec
          h_prog
          (Dec «client» (LoadByte (Var «client_a»))
               (Dec «check_num_to_get_chars_a»
                    (Op Add [BaseAddr; Const 5w])
                    (Seq
                     (ExtCall «check_num_to_get_chars» (Const 0w)
                              (Const 0w) (Var «check_num_to_get_chars_a»)
                              (Const 1w))
                     (Dec «num_to_get_chars_ret»
                          (LoadByte (Var «check_num_to_get_chars_a»))
                          (Seq
                           (If
                            (Cmp Equal (Var «num_to_get_chars_ret»)
                                 (Const 0w)) (Return (Const 0w)) Skip)
                           (Dec «cli_dequeue_enqueue_c»
                                (Op Add [BaseAddr; Const 6w])
                                (Dec «cli_dequeue_enqueue_a»
                                     (Op Add [BaseAddr; Const 8w])
                                     (Seq
                                      (StoreByte
                                       (Var «cli_dequeue_enqueue_c»)
                                       (Var «client»))
                                      (Seq
                                       (StoreByte
                                        (Op Add
                                            [Var
                                             «cli_dequeue_enqueue_c»;
                                             Const 1w])
                                        (Var «got_char»))
                                       (Seq
                                        (ExtCall
                                         «batch_cli_dequeue_enqueue»
                                         (Var
                                          «cli_dequeue_enqueue_c»)
                                         (Const 2w)
                                         (Var
                                          «cli_dequeue_enqueue_a»)
                                         (Const 1w))
                                        (Dec
                                         «set_escape_character_c»
                                         (Op Add
                                             [BaseAddr; Const 9w])
                                         (Seq
                                          (StoreByte
                                           (Var
                                            «set_escape_character_c»)
                                           (Const 0w))
                                          (Seq
                                           (ExtCall
                                            «set_escape_character»
                                            (Var
                                             «set_escape_character_c»)
                                            (Const 1w)
                                            (Const 0w)
                                            (Const 0w))
                                           (Return (Const 0w)))))))))))))),s'))
       else Ret (res, s'))))
Proof
  ‘good_dimindex (:32)’ by EVAL_TAC >>
  assume_tac (GEN_ALL mux_checked_set_escape_pred_notau) >>
  assume_tac (GEN_ALL muxrx_pred_notau) >>
  rw[muxrx_mem_assms] >>
  gvs[mem_has_word_def] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
  rw[read_bytearray_1] >>
  simp[write_bytearray_preserve_words, mem_has_word_def,
       load_write_bytearray_other] >>
  rw[mem_load_byte_def] >>
  (* vis *)
  rw[Once future_safe_cases] >> disj2_tac >>
  rw[] >-
   (rw[Once future_safe_cases, mux_checked_set_escape_pred_def]) >>
  Cases_on ‘new_bytes’ >> fs[] >> pop_assum kall_tac >>
  qmatch_goalsub_abbrev_tac ‘Seq (ExtCall _ _ _ _ _) rest’ >>
  fs[Once dec_lifted, eval_def, mem_has_word_def,
     write_bytearray_preserve_words, load_write_bytearray_thm2] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
  rw[read_bytearray_1] >>
  fs[mem_has_word_def, write_bytearray_preserve_words,
     load_write_bytearray_other] >>
  rw[mem_load_byte_def] >>
  (* ffi check_num_to_get_chars, h' return *)
  rw[Once future_safe_cases] >> disj1_tac >>
  rw[mux_checked_set_escape_pred_def] >-
   (rw[Abbr ‘rest’] >>
    fs[Once dec_lifted, eval_def, mem_has_word_def,
       write_bytearray_preserve_words, load_write_bytearray_thm2] >>
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[h_prog_def, h_prog_rule_return_def, size_of_shape_def]) >>
  assume_tac (GEN_ALL mux_set_escape_pred_notau) >>
  rw[Abbr ‘rest’] >>
  qmatch_goalsub_abbrev_tac ‘Seq (ExtCall _ _ _ _ _) rest’ >>
  fs[Once dec_lifted, eval_def, mem_has_word_def,
     write_bytearray_preserve_words, load_write_bytearray_thm2] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
  rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  strb_tac >>
  qmatch_goalsub_abbrev_tac ‘(iter _ (_ (mem_store_byte thing _ _ _ _) _ _))’ >>
  subgoal ‘mem_has_word thing (s.base_addr + 6w)’ >-
   (qunabbrev_tac ‘thing’ >>
    gvs[mem_has_word_def, write_bytearray_preserve_words]) >>
  rw[store_bytearray_1] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_store_byte_def,
     eval_def, wordLangTheory.word_op_def] >>
  gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
  PURE_REWRITE_TAC[TWO] >> rw[miscTheory.read_bytearray_def] >>
  rw[load_write_bytearray_other, load_write_bytearray_thm2,
     mem_has_word_def, write_bytearray_preserve_words] >>
  PURE_REWRITE_TAC[ONE] >> rw[read_bytearray_1] >>
  rw[load_write_bytearray_thm2, mem_has_word_def, write_bytearray_preserve_words] >>
  qmatch_goalsub_abbrev_tac ‘(_ (mem_load_byte mem2 _ _ _) _ _)’ >>
  subgoal ‘mem_has_word mem2 (s.base_addr + 8w)’ >-
   (rw[Abbr ‘thing’, Abbr ‘mem2’] >>
    ‘mem_has_word s.memory (s.base_addr + 8w)’ by rw[mem_has_word_def] >>
    irule write_bytearray_preserve_words >>
    irule write_bytearray_preserve_words >> (* Cond_rewr.stack_limit = 6 *)
    gvs[write_bytearray_preserve_words]) >>
  fs[mem_has_word_def, mem_load_byte_def] >>
  rw[Once future_safe_cases] >> disj2_tac >>
  qunabbrev_tac ‘rest’ >> rw[] >-
   (rw[Once future_safe_cases, mux_set_escape_pred_def]) >>
  Cases_on ‘new_bytes’ >> fs[] >> pop_assum kall_tac >>
  strb_tac >>
  gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
  PURE_REWRITE_TAC[ONE] >>
  rw[read_bytearray_1] >>
  qmatch_goalsub_abbrev_tac
  ‘option_CASE (mem_load_byte (write_bytearray _ _ oldmem _ _) _ _ _) _ _’ >>
  subgoal ‘mem_has_word oldmem (s.base_addr + 9w)’ >-
   (gvs[Abbr ‘oldmem’, Abbr ‘thing’, mem_has_word_def,
        write_bytearray_preserve_words]) >>
  gvs[load_write_bytearray_thm2] >>
  (* almost there *)
  rw[Once future_safe_cases] >> disj1_tac >>
  rw[mux_set_escape_pred_def] >>
  (* show return 0 *)
  rw[itree_mrec_alt, h_prog_def, h_prog_rule_return_def, size_of_shape_def]
QED

Theorem muxrx_correct:
  muxrx_mem s ⇒ future_safe muxrx_pred (muxrx_sem s)
Proof
  ‘good_dimindex (:32)’ by EVAL_TAC >>
  rw[muxrx_mem_assms, muxrx_sem_def, itree_semantics_def, itree_evaluate_alt] >>
  assume_tac (GEN_ALL muxrx_pred_notau) >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
  rfs[read_bytearray_1, mem_has_word_def, mem_load_byte_def] >>
  rw[Once future_safe_cases] >> disj1_tac >> rw[muxrx_pred_def] >>
  fs[dec_lifted, eval_def, mem_has_word_def, load_write_bytearray_thm2] >>
  rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
  simp[read_bytearray_1, load_write_bytearray_other, mem_load_byte_def,
       mem_has_word_def] >>
  qpat_abbrev_tac ‘b3 = get_byte _ _ _’ >> qmatch_goalsub_abbrev_tac ‘Vis _ k2’ >>
  qexistsl_tac [‘k2’, ‘b3’] >>
  qunabbrev_tac ‘k2’ >> rw[itree_wbisim_refl] >-
   (* backslash *)
   (assume_tac (GEN_ALL mux_checked_set_escape_pred_notau) >> rw[] >>
    gvs[dec_lifted, eval_def, write_bytearray_preserve_words, mem_has_word_def,
       load_write_bytearray_thm2] >>
    (* if the first bind (if-branch) returns we're done, discard rest *)
    ho_match_mp_tac mux_checked_set_branch >>
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def] >>
    rw[GSYM itree_mrec_alt, seq_thm] >>
    (* escape_1 *)
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
    rw[Once future_safe_cases] >> disj2_tac >>
    rw[] >-
     (rw[Once future_safe_cases, mux_checked_set_escape_pred_def]) >>
    PURE_REWRITE_TAC[
        prove(“ValWord (1w : word32) = ValWord (w2w (1w : word8))”, rw[])] >>
    irule escape_set_branch >>
    gvs[muxrx_mem_assms, mem_has_word_def])
  >- (* part 2 *)
   (assume_tac (GEN_ALL mux_at_pred_notau) >> rw[] >>
    qmatch_goalsub_abbrev_tac ‘Seq (ExtCall _ _ _ _ _) rest’ >>
    fs[Once dec_lifted, eval_def, mem_has_word_def,
       write_bytearray_preserve_words, load_write_bytearray_thm2] >>
    (* not 1 *)
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[Once h_prog_def] >>
    (* not 2 *)
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def,
       Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[GSYM itree_mrec_alt, seq_thm] >>
    ho_match_mp_tac mux_return_branch_at >> rw[Abbr ‘rest’] >>
    (* making escape_2 call... *)
    rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
    rw[Once future_safe_cases] >> disj2_tac >>
    rw[] >-
     (rw[Once future_safe_cases, mux_at_pred_def, mux_set_escape_pred_def]) >>
    rw[dec_lifted, eval_def, wordLangTheory.word_op_def] >>

    reverse
    (rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def,
        Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE]) >-
     (strb_tac >>
      gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
      rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
      gvs[read_bytearray_1, write_bytearray_preserve_words,
          load_write_bytearray_thm2, mem_has_word_def] >>
      rw[Once future_safe_cases] >> disj1_tac >>
      rw[mux_at_pred_def] >-
       (rw[mux_set_escape_pred_def] >>
        rw[Once itree_mrec_alt, h_prog_def,
           h_prog_rule_return_def, size_of_shape_def]) >>
      Cases_on ‘¬(w2w c + 0xFFFFFFD0w < (1w : word32))’ >> gvs[] >>
      rw[wordsTheory.WORD_NOT_LESS_EQUAL]) >>
    rw[h_prog_def, h_prog_rule_dec_def, eval_def, wordLangTheory.word_op_def] >>
    rw[h_prog_rule_seq_def] >>
    rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
    gvs[read_bytearray_1, write_bytearray_preserve_words,
        load_write_bytearray_other, mem_has_word_def] >>
    rw[mem_load_byte_def] >>
    rw[Once future_safe_cases] >> disj1_tac >>
    simp[mux_at_pred_def] >>
    subgoal ‘¬(w2w c + 0xFFFFFFD0w < (1w : word32)) ∧
             (1w : word32) ≤ w2w c + 0xFFFFFFD0w’ >-
     (Cases_on ‘¬(w2w c + 0xFFFFFFD0w < (1w : word32))’ >> gvs[] >>
      metis_tac[wordsTheory.WORD_NOT_LESS_EQUAL]) >>
    rw[] >> skip_tau >> skip_tau >>
    rw[Once h_prog_def, h_prog_rule_dec_def, eval_def] >>
    gvs[read_bytearray_1, write_bytearray_preserve_words,
        load_write_bytearray_thm2, mem_has_word_def] >>
    skip_tau >>
    rw[itree_mrec_alt, h_prog_def, h_prog_rule_cond_def] >>
    reverse(
      rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE]) >-
     (skip_tau >>
      rw[Once future_safe_cases] >> disj1_tac >>
      subgoal ‘¬(w2w c + (0xFFFFFFD0w : word32) ≤ w2w n)’ >-
       (Cases_on ‘¬(w2w n < (w2w c) + (0xFFFFFFD0w : word32))’ >>
        gvs[wordsTheory.WORD_NOT_LESS_EQUAL]) >>
      rw[]) >>
    rw[] >> skip_tau >>
    rw[Once h_prog_def, h_prog_rule_dec_def,
       eval_def, wordLangTheory.word_op_def] >> skip_tau >>
    rw[Once h_prog_def, h_prog_rule_seq_def] >> skip_tau >>
    rw[Once h_prog_def, h_prog_rule_store_byte_def] >>
    gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
    rw[Once h_prog_def, h_prog_rule_store_byte_def] >>
    gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
    skip_tau >> rw[Once h_prog_def, h_prog_rule_ext_call_def] >>
    gvs[read_bytearray_1, write_bytearray_preserve_words,
        load_write_bytearray_thm2, mem_has_word_def] >>
    rw[Once future_safe_cases] >> disj1_tac >>
    qmatch_goalsub_abbrev_tac ‘_ ⇒ k2 = _ ∧ _’ >>
    qexists_tac ‘k2’ >> rw[] >>
    qunabbrev_tac ‘k2’ >> rw[] >> skip_tau >> skip_tau >> skip_tau >>
    rw[h_prog_def, h_prog_rule_seq_def] >> skip_tau >>
    rw[h_prog_rule_store_byte_def] >>
    qmatch_goalsub_abbrev_tac ‘(_ (mem_store_byte mem2 _ _ _ _) _ _)’ >>
    subgoal ‘mem_has_word mem2 (s.base_addr + 9w)’ >-
     (rw[Abbr ‘mem2’] >>
      ‘mem_has_word s.memory (s.base_addr + 9w)’ by rw[mem_has_word_def] >>
      gvs[write_bytearray_preserve_words]) >>
    gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
    skip_tau >>
    rw[h_prog_def, h_prog_rule_seq_def] >> skip_tau >>
    rw[h_prog_rule_ext_call_def] >>
    gvs[read_bytearray_1, write_bytearray_preserve_words,
        load_write_bytearray_thm2, mem_has_word_def] >>
    rw[Once future_safe_cases] >> disj1_tac >>
    rw[mux_set_escape_pred_def] >>
    rw[h_prog_def, h_prog_rule_return_def, size_of_shape_def])
  >- (* escape control received *)
   (assume_tac (GEN_ALL mux_escape_pred_notau) >> rw[] >>
    fs[Once dec_lifted, eval_def, mem_has_word_def,
       write_bytearray_preserve_words, load_write_bytearray_thm2] >>
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    (* not one *)
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[Once h_prog_def, h_prog_rule_seq_def] >>
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    rw[Once h_prog_def, h_prog_rule_seq_def] >>
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    (* making escape_0 call... *)
    ho_match_mp_tac mux_return_branch_esc >>
    rw[GSYM itree_mrec_alt, seq_thm] >>
    rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
    rw[Once future_safe_cases] >> disj2_tac >>
    rw[] >-
     (rw[Once future_safe_cases] >>
      simp[mux_escape_pred_def, mux_set_escape_pred_def] >>
      rw[Once future_safe_cases, mux_checked_set_escape_pred_def]) >>
    (* case split *)
    Cases_on ‘c = 92w’ >-
     (rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
      rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rw[GSYM itree_mrec_alt, seq_thm] >>
      (* escape_case call *)
      rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[] >-
       (rw[Once future_safe_cases, mux_escape_pred_def, mux_set_escape_pred_def]) >>
      ho_match_mp_tac mux_return_branch_esc >>
      (* exit after branch *)
      rw[baseaddr_ref] >>
      strb_tac >>
      gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
      rw[Once itree_mrec_alt, h_prog_def, h_prog_rule_ext_call_def] >>
      gvs[read_bytearray_1, write_bytearray_preserve_words,
          load_write_bytearray_thm2, mem_has_word_def] >>
      rw[Once future_safe_cases] >> disj1_tac >>
      rw[mux_escape_pred_def, mux_set_escape_pred_def] >>
      rw[itree_mrec_alt, h_prog_def, h_prog_rule_return_def, size_of_shape_def]) >>
    Cases_on ‘c = 64w’ >-
     (rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
      rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
      rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      (* escape_case call *)
      rw[GSYM itree_mrec_alt, seq_thm] >>
      rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
      rw[Once future_safe_cases] >> disj2_tac >>
      rw[] >-
       (rw[Once future_safe_cases, mux_escape_pred_def, mux_set_escape_pred_def]) >>
      ho_match_mp_tac mux_return_branch_esc >>
      rw[baseaddr_ref] >>
      strb_tac >>
      gvs[store_bytearray_1, mem_has_word_def, write_bytearray_preserve_words] >>
      rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_ext_call_def] >>
      gvs[read_bytearray_1, write_bytearray_preserve_words,
          load_write_bytearray_thm2, mem_has_word_def] >>
      rw[Once future_safe_cases] >> disj1_tac >>
      rw[mux_escape_pred_def, mux_set_escape_pred_def] >>
      rw[Once itree_mrec_alt, Once h_prog_def,
         h_prog_rule_return_def, size_of_shape_def]) >>
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    simp[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    subgoal ‘(w2w c) ≠ (92w : word32)’ >-
     (qspecl_then [‘c’,‘92w’] strip_assume_tac (cj 1 addressTheory.w2w_CLAUSES) >>
      fs[]) >>
    subgoal ‘(w2w c) ≠ (64w : word32)’ >-
     (qspecl_then [‘c’,‘64w’] strip_assume_tac (cj 1 addressTheory.w2w_CLAUSES) >>
      fs[]) >>
    rw[Once h_prog_def, h_prog_rule_seq_def] >>
    rw[Once itree_mrec_alt, Once h_prog_def, h_prog_rule_cond_def] >>
    rw[Once eval_def, asmTheory.word_cmp_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    irule escape_pred_to_backslash >> rw[] >>
    PURE_REWRITE_TAC[
        prove(“ValWord (0w : word32) = ValWord (w2w (0w : word8))”, rw[])] >>
    irule escape_set_branch >>
    rw[muxrx_mem_assms, mem_has_word_def])
QED
