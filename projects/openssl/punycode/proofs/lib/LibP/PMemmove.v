(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit WpTac.
From OSSVerify.Proofs.openssl.punycode.lib.LibP Require Import PCode PMemcpy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_mm stops := wp_go 0x276848 95%nat C_memmove_eq C_memmove stops.

Section Memmove.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (d s n : Z).
Hypothesis Hn : 0 <= n < 2 ^ 62.
Hypothesis Hs : 0 <= s /\ s + n < 2 ^ 63.
Hypothesis Hd : s < d /\ d + n < 2 ^ 63.
Hypothesis Hmis : (d - s) mod 8 <> 0.
Hypothesis Hsmall : n <= d - s -> n < 32.
Hypothesis Hrd : rd_ok M s n.
Hypothesis Hwr : wr_ok PSEGS M d n.

Definition KS : list nat := PMemcpy.KS.
Definition FP (x : word) : Prop := inr x d n.
Variable l0 : regfile.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KS l0 l' ->
  unch M M' FP -> mem_grows M M' ->
  reach PSEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

(* [comment removed for export] *)
Lemma bloop : forall k t l M', n - t = Z.of_nat k -> unch M M' FP -> mem_grows M M' -> 0 <= t < n ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 11 = W (s + n - 1 - t) -> rget l 12 = W (t - n) -> rget l 13 = W (d + n - 1 - t) ->
  reach PSEGS rom (Z_to_bv 64 0x2768bc) l M' Post.
Proof.
  induction k as [k IH] using lt_wf_ind; intros t l M' Hk HU HG Ht Hl Hse H11 H12 H13.
  regs_open l Hl. subst a1 a2 a3.
  wp_mm [0x2768bc].
  assert (exists v, load_ok PSEGS M' (W (s + n - 1 - t)) 1 v) as [v Hv]
    by (eapply load_rd; [eapply rd_ok_grows; [exact HG | exact Hrd] | lia..]).
  exists v. split; [exact Hv|]. clear Hv.
  split; [eapply wr_ok_store; [eapply wr_ok_grows; [exact HG | exact Hwr] | lia | lia]|].
  rewrite ?addi_W. split; intros Hb.
  - eapply (IH (Z.to_nat (n - (t + 1)))) with (t := t + 1);
      [ lia | lia | solve_unch ltac:(unfold FP, inr in *; lia) | solve_grows | | reflexivity
      | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try (f_equal; lia).
    destruct (Z.eq_dec (t + 1) n) as [E|E]; [|lia]. exfalso. apply Hb.
    replace (t - n + 1) with 0 by lia. reflexivity.
  - pose proof (Hse 1%nat ltac:(cbv; intuition lia)) as Hra. cbn [rget lget] in Hra.
    match type of Hra with ?x = _ => subst x end.
    apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex]
             | solve_unch ltac:(unfold FP, inr in *; lia) | solve_grows].
Qed.

Lemma memmove_body : forall l, length l = 32%nat -> l = l0 ->
  rget l 10 = W d -> rget l 11 = W s -> rget l 12 = W n ->
  reach PSEGS rom (Z_to_bv 64 0x276848) l M Post.
Proof.
  intros l Hl El H10 H11 H12. assert (Hse : same_except KS l0 l) by (subst l; apply same_except_refl).
  assert (E1 : rget l 1 = rget l0 1) by (rewrite El; reflexivity).
  clear El. regs_open l Hl. subst a0 a1 a2.
  wp_mm [0x27686c; 0x2768bc; 0x276918].
  rewrite ?add_W, ?sub_W. rewrite slli_W by lia. rewrite ?sub_W. rewrite !Wu_mod.
  rewrite (Z.mod_small d), (Z.mod_small s) by lia.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  replace (s - (n + d)) with (- (d - s + n)) by lia. rewrite mod_neg64 by lia.
  split; intros Hb.
  - (* [comment removed for export] *)
    assert (Hnd : n <= d - s).
    { destruct (Z.eq_dec n 0) as [->|Hn0]; [lia|].
      replace (0 - n * 2 ^ 1) with (- (2 * n)) in Hb by lia. rewrite mod_neg64 in Hb by lia. lia. }
    specialize (Hsmall Hnd).
    eapply (memcpy_cps rom Post M d s n); [lia | lia | lia | exact Hrd | exact Hwr | reflexivity | reflexivity | reflexivity | reflexivity |].
    intros l' M' Hl' Hse' HU' HG'. cbn [rget lget]. cbn [rget lget] in E1. rewrite E1.
    apply K; [exact Hl' | eapply same_except_trans; [exact Hse|]; eapply same_except_trans; [|exact Hse']; same_ex
             | exact HU' | exact HG'].
  - clear Hb. split; intros Hb; [clear Hb | exfalso; lia].
    rewrite xor_W by lia. change 7 with (Z.ones 3). rewrite u_andi_ones by lia.
    rewrite Wu by (apply Z_lxor_range; lia).
    split; intros Hb.
    + exfalso. apply lxor_mod8_zero in Hb; [|lia|lia]. apply Hmis.
      rewrite Zminus_mod, Hb, Z.sub_diag. reflexivity.
    + clear Hb. rewrite (Z.mod_small n) by lia. split; intros Hb.
      * pose proof (Hse 1%nat ltac:(cbv; intuition lia)) as Hra. cbn [rget lget] in Hra.
        match type of Hra with ?x = _ => subst x end.
        apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex] | apply unch_refl | apply mem_grows_refl].
      * rewrite ?addi_W, ?add_W, ?sub_W.
        eapply (bloop (Z.to_nat (n - 0)) 0);
          [ lia | apply unch_refl | apply mem_grows_refl | lia | reflexivity
          | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; f_equal; lia.
Qed.

End Memmove.

(* [comment removed for export] *)
Theorem memmove_cps : forall rom Post M d s n l,
  0 <= n < 2 ^ 62 -> 0 <= s /\ s + n < 2 ^ 63 -> s < d /\ d + n < 2 ^ 63 ->
  (d - s) mod 8 <> 0 -> (n <= d - s -> n < 32) ->
  rd_ok M s n -> wr_ok PSEGS M d n ->
  length l = 32%nat -> rget l 10 = W d -> rget l 11 = W s -> rget l 12 = W n ->
  (forall l' M', length l' = 32%nat -> same_except KS l l' -> unch M M' (FP d n) -> mem_grows M M' ->
                 reach PSEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach PSEGS rom (Z_to_bv 64 0x276848) l M Post.
Proof. intros rom Post M d s n l; intros. eapply (memmove_body rom Post M d s n) with (l0 := l); eauto. Qed.
