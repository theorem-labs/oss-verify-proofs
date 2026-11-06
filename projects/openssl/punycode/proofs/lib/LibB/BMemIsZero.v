(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_miz stops := wp_go 0x1d0328 45%nat C_memiszero_eq C_memiszero stops.

Section MIZ.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (a n sp0 : Z).
Hypothesis Hn : 0 <= n <= 2 ^ 40.
Hypothesis Ha : 0 <= a /\ a + n < 2 ^ 63.
Hypothesis Hz : zeros M a n.
Hypothesis Hsp : 16 <= sp0 < 2 ^ 63.
Hypothesis Hfr : wr_ok BSEGS M (sp0 - 16) 16.
Hypothesis Hdj : a + n <= sp0 - 16 \/ sp0 <= a.

Definition KS : list nat := [10; 11; 12; 13; 14; 15; 16]%nat.
(* [comment removed for export] *)
Definition KSI : list nat := [1; 2; 10; 11; 12; 13; 14; 15; 16]%nat.
Definition FP (x : word) : Prop := inr x (sp0 - 16) 16.

Variable l0 : regfile.
Hypothesis Hl0 : length l0 = 32%nat.
Hypothesis H0sp : rget l0 2 = W sp0.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KS l0 l' -> rget l' 10 = W 1 ->
  unch M M' FP -> mem_grows M M' ->
  reach BSEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

Definition M1 : mem := wbytes M (W (sp0 + -16 + 8)) (word_to_le_bytes 8 (rget l0 1)).

Lemma M1_zeros : zeros M1 a n.
Proof.
  intros i Hi. unfold M1. rewrite wbytes_out; [apply Hz, Hi | lia | rewrite length_N_to_le_bytes; lia |].
  rewrite length_N_to_le_bytes. unfold inr. rewrite Wu by lia. lia.
Qed.

Lemma M1_unch : unch M M1 FP.
Proof. unfold M1. solve_unch ltac:(unfold FP, inr in *; lia). Qed.

Lemma M1_grows : mem_grows M M1.
Proof. unfold M1. solve_grows. Qed.

Lemma M1_ra : cell BSEGS M1 (sp0 + -16 + 8) 8 (rget l0 1).
Proof. unfold M1. apply cell_store_same; lia. Qed.

(* [comment removed for export] *)
Definition stable (l : regfile) : Prop :=
  length l = 32%nat /\ same_except KSI l0 l /\ rget l 2 = W (sp0 - 16) /\ rget l 11 = W 0.

(* [comment removed for export] *)
Lemma exit_blk : forall l, stable l -> reach BSEGS rom (Z_to_bv 64 0x1d03b4) l M1 Post.
Proof.
  intros l (Hl & Hse & H2 & H11). pose proof M1_ra as Cra.
  regs_open l Hl. subst sp a1.
  wp_miz (@nil Z). mem_auto.
  apply K; [reflexivity | | reflexivity | apply M1_unch | apply M1_grows].
  same_fix Hse. rewrite H0sp. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma tail_loop : forall k c x l, c = Z.of_nat k -> 0 < c -> a <= x -> x + c <= a + n ->
  stable l -> rget l 12 = W x -> rget l 14 = W c ->
  reach BSEGS rom (Z_to_bv 64 0x1d03a0) l M1 Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros c x l Hk Hc Hx Hxc (Hl & Hse & H2 & H11) H12 H14.
  regs_open l Hl. subst sp a1 a2 a4.
  wp_miz [0x1d03a0; 0x1d03b4].
  exists (W 0). split; [eapply load1_zeros; [apply M1_zeros | lia]|].
  rewrite ?addi_W. change (v_or (Z_to_bv 64 0) (Z_to_bv 64 0)) with (W 0).
  split; intros Hb.
  - eapply (IH (Z.to_nat (c - 1))) with (c := c - 1) (x := x + 1); try lia.
    + destruct (Z.eq_dec c 1) as [->|]; [exfalso; apply Hb; reflexivity | lia].
    + split; [reflexivity|]. split; [eapply same_except_trans; [exact Hse | same_ex]|]. split; reflexivity.
    + reflexivity.
    + cbn [rget lget]. reflexivity.
  - apply exit_blk. split; [reflexivity|]. split; [eapply same_except_trans; [exact Hse | same_ex]|]. split; reflexivity.
Qed.

Definition ab : Z := (a + 7) / 8 * 8.
Definition ae : Z := (a + n) / 8 * 8.

(* [comment removed for export] *)
Definition body (l : regfile) : Prop :=
  stable l /\ rget l 10 = W a /\ rget l 12 = W ae /\ rget l 14 = W (a + n).

Ltac open_body H l :=
  let Hl := fresh "Hl" in let Hse := fresh "Hse" in
  destruct H as ((Hl & Hse & ?H2 & ?H11) & ?H10 & ?H12 & ?H14); regs_open l Hl.

Ltac prove_stable Hse :=
  split; [reflexivity|]; split; [eapply same_except_trans; [exact Hse | same_ex]|]; split; reflexivity.

(* [comment removed for export] *)
Lemma tail_entry : forall l, body l -> reach BSEGS rom (Z_to_bv 64 0x1d0394) l M1 Post.
Proof.
  intros l Hb. open_body Hb l. subst sp a0 a1 a2 a4.
  pose proof (align_dn_le (a + n)) as Hae. fold ae in Hae.
  wp_miz [0x1d03a0; 0x1d03b4].
  rewrite ?sub_W. rewrite !Wu by (unfold ae in *; lia).
  split; intros Hb1; [apply exit_blk; prove_stable Hse|].
  split; intros Hb2; [apply exit_blk; prove_stable Hse|].
  eapply (tail_loop (Z.to_nat (a + n - ae))) with (c := a + n - ae) (x := ae); try lia;
    [prove_stable Hse | reflexivity | reflexivity].
Qed.

(* [comment removed for export] *)
Lemma word_loop : forall k x l, ae - x = Z.of_nat k -> x mod 8 = 0 -> a <= x < ae ->
  body l -> rget l 15 = W x ->
  reach BSEGS rom (Z_to_bv 64 0x1d0384) l M1 Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros x l Hk Hx8 Hx Hb H15.
  open_body Hb l. subst sp a0 a1 a2 a4 a5.
  pose proof (align_dn_le (a + n)) as Hae. fold ae in Hae.
  assert (Hae8 : ae mod 8 = 0) by apply align_dn_mod.
  pose proof (aligned_step x ae Hx8 Hae8 ltac:(lia)) as Hstep.
  wp_miz [0x1d0384; 0x1d0394].
  exists (W 0). split; [eapply load8_zeros; [apply M1_zeros | lia | lia]|].
  rewrite ?addi_W. change (v_or (Z_to_bv 64 0) (Z_to_bv 64 0)) with (W 0).
  rewrite !Wu by lia.
  split; intros Hb1.
  - eapply (IH (Z.to_nat (ae - (x + 8)))) with (x := x + 8); try lia.
    + split; [prove_stable Hse|]. cbn [rget lget]. repeat split; reflexivity.
    + reflexivity.
  - apply tail_entry. split; [prove_stable Hse|]. cbn [rget lget]. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma after_head : forall l, body l -> rget l 15 = W ab ->
  reach BSEGS rom (Z_to_bv 64 0x1d0380) l M1 Post.
Proof.
  intros l Hb H15. open_body Hb l. subst sp a0 a1 a2 a4 a5.
  pose proof (align_dn_le (a + n)) as Hae. fold ae in Hae.
  pose proof (align_up_le a) as Hab. fold ab in Hab.
  wp_miz [0x1d0384; 0x1d0394].
  assert (Hae0 : 0 <= ae) by (unfold ae; lia).
  rewrite !Wu by lia.
  split; intros Hb1.
  - apply tail_entry. split; [prove_stable Hse|]. cbn [rget lget]. repeat split; reflexivity.
  - eapply (word_loop (Z.to_nat (ae - ab))) with (x := ab); try lia.
    + apply align_dn_mod.
    + split; [prove_stable Hse|]. cbn [rget lget]. repeat split; reflexivity.
    + reflexivity.
Qed.

(* [comment removed for export] *)
Lemma head_loop : forall k m l, ab - m = Z.of_nat k -> a <= m < ab -> m < a + n ->
  body l -> rget l 15 = W ab -> rget l 13 = W (m + 1) ->
  reach BSEGS rom (Z_to_bv 64 0x1d0368) l M1 Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros m l Hk Hm Hmn Hb H15 H13.
  open_body Hb l. subst sp a0 a1 a2 a3 a4 a5.
  pose proof (align_up_le a) as Hab. fold ab in Hab.
  wp_miz [0x1d0368; 0x1d0380].
  rewrite ?addi_W. replace (m + 1 + -1) with m by lia.
  exists (W 0). split; [eapply load1_zeros; [apply M1_zeros | lia]|].
  change (v_or (Z_to_bv 64 0) (Z_to_bv 64 0)) with (W 0).
  rewrite !Wu by lia.
  split; intros Hb1.
  - apply after_head; [|reflexivity]. split; [prove_stable Hse|]. cbn [rget lget]. repeat split; reflexivity.
  - split; intros Hb2.
    + eapply (IH (Z.to_nat (ab - (m + 1)))) with (m := m + 1); try lia.
      * split; [prove_stable Hse|]. cbn [rget lget]. repeat split; reflexivity.
      * reflexivity.
      * reflexivity.
    + apply after_head; [|reflexivity]. split; [prove_stable Hse|]. cbn [rget lget]. repeat split; reflexivity.
Qed.

Lemma miz_body : forall l, length l = 32%nat -> l = l0 ->
  rget l 10 = W a -> rget l 11 = W n ->
  reach BSEGS rom (Z_to_bv 64 0x1d0328) l M Post.
Proof.
  intros l Hl El H10 H11. assert (Hse : same_except KSI l0 l) by (subst l; apply same_except_refl).
  assert (E1 : rget l 1 = rget l0 1) by (rewrite El; reflexivity).
  assert (E2 : rget l 2 = W sp0) by (rewrite El; exact H0sp).
  clear El. regs_open l Hl. cbn [rget lget] in E1, E2. subst a0 a1 sp ra.
  pose proof (align_up_le a) as Hab. fold ab in Hab.
  wp_miz [0x1d0368; 0x1d0380; 0x1d03c4].
  rewrite ?addi_W.
  split; [eapply wr_ok_store; [exact Hfr | lia | lia]|].
  change (wbytes M _ _) with M1.
  change (v_addi (v_slli (Z_to_bv 64 1) 40) 1) with (W (2 ^ 40 + 1)).
  rewrite ?add_W. rewrite ?andi_m8_W by lia. fold ab ae.
  pose proof (align_dn_le (a + n)) as Hae. fold ae in Hae.
  assert (Hae0 : 0 <= ae) by (unfold ae; lia).
  rewrite !Wu by lia.
  assert (Hst : forall r13 r16, stable [x0; lget l0 1; Z_to_bv 64 (sp0 + -16); gp; tp; t0; t1; t2; s0; s1;
             Z_to_bv 64 a; Z_to_bv 64 0; W ae; r13; W (a + n); W ab; r16; a7; s2; s3; s4; s5; s6;
             s7; s8; s9; s10; s11; t3; t4; t5; t6]).
  { intros r13 r16. split; [reflexivity|]. split; [eapply same_except_trans; [exact Hse | same_ex]|].
    split; [cbn [rget lget]; f_equal; lia | reflexivity]. }
  split; intros Hb; [exfalso; lia|]. clear Hb.
  split; intros Hb1.
  - apply after_head; [|reflexivity]. split; [apply Hst|]. cbn [rget lget]. repeat split; reflexivity.
  - split; intros Hb2.
    + apply after_head; [|reflexivity]. split; [apply Hst|]. cbn [rget lget]. repeat split; reflexivity.
    + rewrite ?addi_W.
      eapply (head_loop (Z.to_nat (ab - a))) with (m := a); try lia.
      * split; [apply Hst|]. cbn [rget lget]. repeat split; reflexivity.
      * reflexivity.
      * reflexivity.
Qed.

End MIZ.

(* [comment removed for export] *)
Theorem memiszero_cps : forall rom Post M a n sp0 l,
  0 <= n <= 2 ^ 40 -> 0 <= a /\ a + n < 2 ^ 63 -> zeros M a n ->
  16 <= sp0 < 2 ^ 63 -> wr_ok BSEGS M (sp0 - 16) 16 -> (a + n <= sp0 - 16 \/ sp0 <= a) ->
  length l = 32%nat -> rget l 2 = W sp0 -> rget l 10 = W a -> rget l 11 = W n ->
  (forall l' M', length l' = 32%nat -> same_except KS l l' -> rget l' 10 = W 1 ->
                 unch M M' (FP sp0) -> mem_grows M M' ->
                 reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1d0328) l M Post.
Proof.
  intros rom Post M a n sp0 l; intros.
  eapply (miz_body rom Post M a n sp0) with (l0 := l); eauto.
Qed.
