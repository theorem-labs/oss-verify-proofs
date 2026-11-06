(* Calling a `leaf` contract (lib/Prog/link_mem.v) from inside a walk over `mkR` registers, and going on
   with the walk. The leaf part of the mark lane's call kit lib/Prog/mk_call.v,
   with names prefixed `c45_` so the two can be loaded together.
   The callee returns a map regs' that agrees with the caller's on the callee-saved registers; the walk
   tactics need mkR form, so the continuation gets `mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' .. a7' s2 .. s11
   t3' .. t6'` and the result moves back with lib/Lib/RegisterBridge.v (canonical_contract_transport).
   That asks the goal to be closed under register-equivalent states: `eqv_cl P` (LDefs) is. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem mk_leaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Regs6ss RegisterBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs.
Local Open Scope Z_scope.

Definition c45_q_ext (Q : machine_state -> Prop) : Prop := forall c a, Q c -> ms_eqv c a -> Q a.

Lemma c45_ms_eqv_trans : forall a b c, ms_eqv a b -> ms_eqv b c -> ms_eqv a c.
Proof.
  intros a b c (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8) (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
  split; [intros r Hr; rewrite (A1 r Hr); exact (B1 r Hr)|].
  repeat split; congruence.
Qed.

Lemma c45_ms_eqv_refl : forall a, ms_eqv a a.
Proof. intros a. repeat split; reflexivity. Qed.

Lemma c45_eqv_cl_ext : forall P, c45_q_ext (eqv_cl P).
Proof.
  intros P c a (c0 & HP & E1) E2. exists c0. split; [exact HP|]. exact (c45_ms_eqv_trans _ _ _ E1 E2).
Qed.

(* a state that satisfies P satisfies eqv_cl P *)
Lemma c45_eqv_cl_of : forall (P : machine_state -> Prop) ms, P ms -> eqv_cl P ms.
Proof. intros P ms H. exists ms. split; [exact H | apply c45_ms_eqv_refl]. Qed.

(* eqv_cl of eqv_cl is eqv_cl *)
Lemma c45_eqv_cl_idem : forall (P : machine_state -> Prop) ms, eqv_cl (eqv_cl P) ms -> eqv_cl P ms.
Proof.
  intros P ms (c & (c0 & HP & E1) & E2). exists c0. split; [exact HP|]. exact (c45_ms_eqv_trans _ _ _ E1 E2).
Qed.

Lemma c45_evt_canon : forall Q R F pc fc rv m ro, c45_q_ext Q ->
  evt rsegs Q (MS (mkR_of R) F pc fc rv m ro) -> evt rsegs Q (MS R F pc fc rv m ro).
Proof.
  intros Q R F pc fc rv m ro HQ H.
  pose proof (canonical_contract_transport rsegs Q (MS R F pc fc rv m ro) H) as T.
  eapply evt_mono; [exact T|]. intros a (c & Hc & HE). exact (HQ c a Hc HE).
Qed.

(* the callee-saved words of a map that `regs_preserved` keeps from an `mkR` map *)
Section Saved.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Let R := mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Lemma c45_canon_of_preserved : forall regs', regs_preserved R regs' ->
  mkR_of regs' = mkR (reg_get regs' 1) sp gp tp (reg_get regs' 5) (reg_get regs' 6) (reg_get regs' 7) s0 s1
                     (reg_get regs' 10) (reg_get regs' 11) (reg_get regs' 12) (reg_get regs' 13)
                     (reg_get regs' 14) (reg_get regs' 15) (reg_get regs' 16) (reg_get regs' 17)
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                     (reg_get regs' 28) (reg_get regs' 29) (reg_get regs' 30) (reg_get regs' 31).
Proof.
  intros regs' RP.
  assert (C : forall r, callee_saved r -> reg_get regs' (Z_to_bv 5 r) = reg_get R (Z_to_bv 5 r)).
  { intros r Hr. pose proof (RP r Hr) as H. unfold YK11.getr in H. unfold callee_saved in Hr.
    replace (bv_eqb (Z_to_bv 5 r) 0) with false in H; [exact H|].
    symmetry. unfold bv_eqb. rewrite Z_to_bv_unsigned. apply Z.eqb_neq. unfold bv_wrap.
    change (bv_modulus 5) with 32. rewrite Z.mod_small by lia.
    intros E. assert (Z0 : bv_unsigned (0 : bv 5) = 0) by (vm_compute; reflexivity). rewrite Z0 in E. lia. }
  unfold mkR_of. f_equal;
    match goal with |- reg_get regs' ?l = _ =>
      let z := eval vm_compute in (bv_unsigned l) in exact (C z ltac:(unfold callee_saved; lia)) end.
Qed.
End Saved.

Lemma c45_leaf_call : forall pcC KC PreC WrC PostC, leaf pcC KC PreC WrC PostC -> post_ext PostC ->
  forall Q, c45_q_ext Q ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc m lo,
  PreC (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m ->
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + KC <= bv_unsigned sp -> bv_unsigned sp < 2 ^ 63 ->
  (forall ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
     munch ((bv_unsigned sp - KC, bv_unsigned sp)
            :: WrC (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m)
           m m' ->
     wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
     PostC (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) m
           (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           m' ->
     evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 pcC) fc None m (seg_rom rsegs)).
Proof.
  intros pcC KC PreC WrC PostC HC HPE Q HQ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6
    s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo HPre MI ST LO SP K.
  eapply evt_cut; [exact (HC _ F fc m lo HPre MI ST LO SP)|].
  intros ms' (regs' & m' & -> & RP & MU & WM & MI' & ST' & PO).
  apply c45_evt_canon; [exact HQ|].
  pose proof (mkR_of_same regs') as ES.
  rewrite (c45_canon_of_preserved ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 regs' RP) in ES |- *.
  apply K; try assumption.
  exact (HPE _ _ _ _ _ _ (fun r => eq_refl) ES PO).
Qed.
