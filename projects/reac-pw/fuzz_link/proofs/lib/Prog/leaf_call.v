(* reac-pw/fuzz_link, PLAIN build: a call to a function with a `leaf` contract (lib/Prog/link_mem.v),
   inside a walk over named registers (lib/Prog/mk_leaf.v `leaf_walk`).

   `leaf_call` runs the callee's contract at the call's state `mkR ra sp ... t6` and continues the
   walk at the callee's return from a register file in the same named form: the callee-saved words
   (sp, gp, tp, s0, s1, s2..s11) as they were, every other word new. The callee's return map is only
   equal to that form register by register, so the continuation's run moves over to it
   (lib/Lib/RegisterBridge.v `evt_register_transport`); the walk's final predicate must be closed
   under that equality, and `leaf_walk_close` gives the closure for the final predicate of
   `leaf_walk`. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss RegisterBridge.
Local Open Scope Z_scope.

(* the final predicate of `leaf_walk` is closed under register-by-register equality *)
Lemma leaf_walk_close : forall (K : Z) Wr Post (R : bvmap 5 word) (F : bvmap 5 word) (ra : word) (fc : bv 32)
    (m : word -> option byte) (lo : Z),
  post_ext Post ->
  forall c a,
    (exists (regs' : bvmap 5 word) (m' : word -> option byte),
       c = MS regs' F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       regs_preserved R regs' /\
       munch ((spZ R - K, spZ R) :: Wr R m) m m' /\
       wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (spZ R) /\
       Post R m regs' m') ->
    ms_eqv c a ->
    (exists (regs' : bvmap 5 word) (m' : word -> option byte),
       a = MS regs' F (ret_pc ra) fc None m' (seg_rom rsegs) /\
       regs_preserved R regs' /\
       munch ((spZ R - K, spZ R) :: Wr R m) m m' /\
       wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (spZ R) /\
       Post R m regs' m').
Proof.
  intros K Wr Post R F ra fc m lo HQ c a (regs' & m' & -> & RP & MU & WM & MI & ST & PO)
         (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  destruct a as [Ra Fa pca sva rva fca ma roa].
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst Fa pca sva rva fca ma roa.
  assert (GS : getr_same regs' Ra) by (intros r; apply getr_eqv, E1).
  assert (G0 : getr_same R R) by (intros r; reflexivity).
  exists Ra, m'. split; [reflexivity|].
  split; [exact (regs_preserved_same _ _ _ _ G0 GS RP)|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  exact (HQ _ _ _ _ _ _ G0 GS PO).
Qed.

Lemma leaf_call : forall (pc K : Z) Pre Wr Post (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  leaf pc K Pre Wr Post -> post_ext Post ->
  (forall c a, Q c -> ms_eqv c a -> Q a) ->
  Pre (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + K <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 ->
  (forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     munch ((bv_unsigned sp - K, bv_unsigned sp) ::
              Wr (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m)
           m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
     Post (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m
          (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               t3' t4' t5' t6') m' ->
     evt rsegs Q
       (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3' t4' t5' t6')
           F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros pc K Pre Wr Post Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
         t3 t4 t5 t6 F fc m lo HC HP HQ Hpre MI ST LO SP KT.
  eapply evt_cut; [exact (HC _ F fc m lo Hpre MI ST LO SP)|].
  intros ms' (regs' & m' & -> & RP & MU & WM & MI' & ST' & PO).
  assert (X2 : reg_get regs' 2 = sp) by exact (RP 2 ltac:(unfold callee_saved; lia)).
  assert (X3 : reg_get regs' 3 = gp) by exact (RP 3 ltac:(unfold callee_saved; lia)).
  assert (X4 : reg_get regs' 4 = tp) by exact (RP 4 ltac:(unfold callee_saved; lia)).
  assert (X8 : reg_get regs' 8 = s0) by exact (RP 8 ltac:(unfold callee_saved; lia)).
  assert (X9 : reg_get regs' 9 = s1) by exact (RP 9 ltac:(unfold callee_saved; lia)).
  assert (X18 : reg_get regs' 18 = s2) by exact (RP 18 ltac:(unfold callee_saved; lia)).
  assert (X19 : reg_get regs' 19 = s3) by exact (RP 19 ltac:(unfold callee_saved; lia)).
  assert (X20 : reg_get regs' 20 = s4) by exact (RP 20 ltac:(unfold callee_saved; lia)).
  assert (X21 : reg_get regs' 21 = s5) by exact (RP 21 ltac:(unfold callee_saved; lia)).
  assert (X22 : reg_get regs' 22 = s6) by exact (RP 22 ltac:(unfold callee_saved; lia)).
  assert (X23 : reg_get regs' 23 = s7) by exact (RP 23 ltac:(unfold callee_saved; lia)).
  assert (X24 : reg_get regs' 24 = s8) by exact (RP 24 ltac:(unfold callee_saved; lia)).
  assert (X25 : reg_get regs' 25 = s9) by exact (RP 25 ltac:(unfold callee_saved; lia)).
  assert (X26 : reg_get regs' 26 = s10) by exact (RP 26 ltac:(unfold callee_saved; lia)).
  assert (X27 : reg_get regs' 27 = s11) by exact (RP 27 ltac:(unfold callee_saved; lia)).
  pose (R' := mkR (reg_get regs' 1) sp gp tp (reg_get regs' 5) (reg_get regs' 6) (reg_get regs' 7) s0 s1
                  (reg_get regs' 10) (reg_get regs' 11) (reg_get regs' 12) (reg_get regs' 13) (reg_get regs' 14)
                  (reg_get regs' 15) (reg_get regs' 16) (reg_get regs' 17) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  (reg_get regs' 28) (reg_get regs' 29) (reg_get regs' 30) (reg_get regs' 31)).
  assert (EQ : xregs_eqv regs' R') by (apply mkR_eqv_of; first [reflexivity | assumption]).
  assert (GS : getr_same regs' R') by (intros r; apply getr_eqv, EQ).
  assert (G0 : getr_same (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6)
                         (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                              t3 t4 t5 t6)) by (intros r; reflexivity).
  pose proof (KT (reg_get regs' 1) (reg_get regs' 5) (reg_get regs' 6) (reg_get regs' 7) (reg_get regs' 10)
                 (reg_get regs' 11) (reg_get regs' 12) (reg_get regs' 13) (reg_get regs' 14) (reg_get regs' 15)
                 (reg_get regs' 16) (reg_get regs' 17) (reg_get regs' 28) (reg_get regs' 29) (reg_get regs' 30)
                 (reg_get regs' 31) m' MU WM MI' ST' (HP _ _ _ _ _ _ G0 GS PO)) as RUN.
  pose proof (evt_register_transport rsegs Q
                (MS R' F (ret_pc ra) fc None m' (seg_rom rsegs))
                (MS regs' F (ret_pc ra) fc None m' (seg_rom rsegs))) as T.
  eapply evt_mono; [apply T; [|exact RUN]|].
  - split; [apply xregs_eqv_sym, EQ|]. repeat split.
  - intros a (c & Hc & E). exact (HQ c a Hc E).
Qed.
