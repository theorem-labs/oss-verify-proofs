(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_imm stops := wp_go 0x1cfda0 22%nat C_imemmove_eq C_imemmove stops.

Section IMemmove.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (d s n : Z).
Hypothesis Hn : 0 <= n < 2 ^ 62.
Hypothesis Hs : 0 <= s /\ s + n < 2 ^ 63.
Hypothesis Hd : s < d /\ d + n < 2 ^ 63.
Hypothesis Hrd : rd_ok M s n.
Hypothesis Hwr : wr_ok BSEGS M d n.

Definition KS : list nat := [12; 13; 14; 15; 16]%nat.
Definition FP (x : word) : Prop := inr x d n.
Variable l0 : regfile.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KS l0 l' ->
  unch M M' FP -> mem_grows M M' ->
  reach BSEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

(* [comment removed for export] *)
Lemma bloop : forall k i l M', i = Z.of_nat k -> unch M M' FP -> mem_grows M M' -> 0 <= i < n ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 10 = W d -> rget l 11 = W s -> rget l 12 = W 1 -> rget l 13 = W i ->
  reach BSEGS rom (Z_to_bv 64 0x1cfdd8) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros i l M' Hk HU HG Hi Hl Hse H10 H11 H12 H13.
  regs_open l Hl. subst a0 a1 a2 a3.
  wp_imm [0x1cfdd8].
  rewrite ?add_W, ?addi_W.
  assert (exists v, load_ok BSEGS M' (W (s + i)) 1 v) as [v Hv]
    by (eapply load_rd; [eapply rd_ok_grows; [exact HG | exact Hrd] | lia..]).
  exists v. split; [exact Hv|]. clear Hv.
  split; [eapply wr_ok_store; [eapply wr_ok_grows; [exact HG | exact Hwr] | lia | lia]|].
  rewrite !Wu by lia. split; intros Hb.
  - eapply (IH (Z.to_nat (i - 1))) with (i := i - 1);
      [ lia | lia | solve_unch ltac:(unfold FP, inr in *; lia) | solve_grows | lia | reflexivity
      | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; f_equal; lia.
  - pose proof (Hse 1%nat ltac:(cbv; intuition lia)) as Hra. cbn [rget lget] in Hra.
    match type of Hra with ?x = _ => subst x end.
    apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex]
             | solve_unch ltac:(unfold FP, inr in *; lia) | solve_grows].
Qed.

Lemma imemmove_body : forall l, length l = 32%nat -> l = l0 ->
  rget l 10 = W d -> rget l 11 = W s -> rget l 12 = W n ->
  reach BSEGS rom (Z_to_bv 64 0x1cfda0) l M Post.
Proof.
  intros l Hl El H10 H11 H12. assert (Hse : same_except KS l0 l) by (subst l; apply same_except_refl).
  assert (E1 : rget l 1 = rget l0 1) by (rewrite El; reflexivity).
  clear El. regs_open l Hl. subst a0 a1 a2. cbn [rget lget] in E1.
  wp_imm [0x1cfda4; 0x1cfdd8].
  rewrite !Wu by lia. rewrite ?addi_W.
  split; intros Hb; [clear Hb | exfalso; lia].
  split; intros Hb; [exfalso; lia | clear Hb].
  rewrite Ws by lia. change (bv_signed (Z_to_bv 64 0)) with 0.
  split; intros Hb.
  - subst ra. apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex] | apply unch_refl | apply mem_grows_refl].
  - eapply (bloop (Z.to_nat (n - 1))) with (i := n - 1);
      [ lia | apply unch_refl | apply mem_grows_refl | lia | reflexivity
      | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; f_equal; lia.
Qed.

End IMemmove.

(* [comment removed for export] *)
Theorem imemmove_cps : forall rom Post M d s n l,
  0 <= n < 2 ^ 62 -> 0 <= s /\ s + n < 2 ^ 63 -> s < d /\ d + n < 2 ^ 63 ->
  rd_ok M s n -> wr_ok BSEGS M d n ->
  length l = 32%nat -> rget l 10 = W d -> rget l 11 = W s -> rget l 12 = W n ->
  (forall l' M', length l' = 32%nat -> same_except KS l l' -> unch M M' (FP d n) -> mem_grows M M' ->
                 reach BSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach BSEGS rom (Z_to_bv 64 0x1cfda0) l M Post.
Proof. intros rom Post M d s n l; intros. eapply (imemmove_body rom Post M d s n) with (l0 := l); eauto. Qed.
