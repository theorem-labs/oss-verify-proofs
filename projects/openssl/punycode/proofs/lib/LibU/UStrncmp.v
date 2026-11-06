(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit HasZero StrKit WpTac.
From OSSVerify.Proofs.openssl.punycode.lib.LibU Require Import UCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_snc stops := wp_go 0x2bd3e0 24%nat C_strncmp_eq C_strncmp stops.

Section Strncmp.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (p N : Z) (B : Z -> byte) (k z q n : Z) (RB : Z -> byte).
Hypothesis HB : bytes_at M p N B.
Hypothesis Hp : 0 <= p.
Hypothesis HN : p + N < 2 ^ 64.
Hypothesis Hk : 0 <= k <= z.
Hypothesis Hz : z < N.
Hypothesis HBz : bv_unsigned (B z) = 0.
Hypothesis HBnz : forall j, k <= j < z -> bv_unsigned (B j) <> 0.
Hypothesis Hn : 0 <= n < 2 ^ 63.
Hypothesis Hq : 0 <= q /\ q + n < 2 ^ 64.
Hypothesis HR : forall i, 0 <= i < n -> load_ok USEGS M (W (q + i)) 1 (W (bv_unsigned (RB i))).
Hypothesis HRnz : forall i, 0 <= i < n -> bv_unsigned (RB i) <> 0.

Definition KS : list nat := [10; 11; 12; 13; 14]%nat.
Variable l0 : regfile.
Hypothesis K : forall l', length l' = 32%nat -> same_except KS l0 l' ->
  (bv_unsigned (rget l' 10) = 0 -> forall i, 0 <= i < n -> B (k + i) = RB i) ->
  reach USEGS rom (v_jalr (rget l0 1) 0) l' M Post.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. exact H. Qed.

Lemma byte_eq : forall a b : byte, bv_unsigned a = bv_unsigned b -> a = b.
Proof. intros a b H. apply bv_eq. exact H. Qed.

Lemma loop : forall m i l, n - 1 - i = Z.of_nat m -> 0 <= i < n -> k + i + 1 <= z ->
  (forall j, 0 <= j < i -> B (k + j) = RB j) ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 10 = W (p + k + i + 1) -> rget l 11 = W (q + i) -> rget l 12 = W (n - 1 - i) ->
  rget l 13 = W (bv_unsigned (B (k + i))) ->
  reach USEGS rom (Z_to_bv 64 0x2bd3f4) l M Post.
Proof.
  induction m as [m IH] using lt_wf_ind; intros i l Hm Hi Hiz Heq Hl Hse H10 H11 H12 H13.
  regs_open l Hl. subst a0 a1 a2 a3.
  pose proof (Hse 1%nat ltac:(cbv; intuition lia)) as Hra. cbn [rget lget] in Hra. subst ra.
  pose proof (byte_range (B (k + i))) as Hbi. pose proof (byte_range (RB i)) as Hri.
  wp_snc [0x2bd3f4].
  exists (W (bv_unsigned (RB i))). split; [apply HR; lia|].
  rewrite !Wu by lia. split; intros Hb.
  - (* [comment removed for export] *)
    exists (W (bv_unsigned (RB i))). split; [apply HR; lia|].
    apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex] |].
    cbn [lget]. intros H0. exfalso. apply Hb.
    rewrite andi255_byte, sub_W in H0 by lia. apply sub_zero_eq in H0; lia.
  - split; intros Hb2; [exfalso; apply (HRnz i); [lia | exact Hb2]|].
    rewrite ?addi_W. rewrite u_sltu0. rewrite Wu by lia.
    destruct (Z.eqb_spec (n - 1 - i) 0) as [En|En]; (split; intros Hb3; [|try (exfalso; lia)]); try (exfalso; lia).
    + (* [comment removed for export] *)
      exists (W (bv_unsigned (RB i))). split; [apply HR; lia|].
      apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex] |].
      intros _ j Hj. destruct (Z.eq_dec j i) as [->|]; [apply byte_eq; lia | apply Heq; lia].
    + exists (W (bv_unsigned (B (k + i + 1)))). split.
      { replace (p + k + i + 1) with (p + (k + i + 1)) by lia. apply (load1_bytes_at USEGS M p N B _ HB); lia. }
      pose proof (byte_range (B (k + i + 1))) as Hbi1. rewrite !Wu by lia. split; intros Hb4.
      * eapply (IH (Z.to_nat (n - 1 - (i + 1)))) with (i := i + 1); [lia | lia | lia | | | reflexivity
          | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try (f_equal; lia).
        -- assert (k + i + 1 <> z) by (intros E; apply Hb4; rewrite E; exact HBz). lia.
        -- intros j Hj. destruct (Z.eq_dec j i) as [->|]; [apply byte_eq; lia | apply Heq; lia].
        -- replace (k + (i + 1)) with (k + i + 1) by lia. reflexivity.
      * exists (W (bv_unsigned (RB (i + 1)))). split.
        { replace (q + i + 1) with (q + (i + 1)) by lia. apply HR; lia. }
        apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex] |].
        cbn [lget]. intros H0. exfalso. pose proof (byte_range (RB (i + 1))) as Hri1.
        rewrite andi255_byte, sub_W in H0 by lia. apply sub_zero_eq in H0; [|lia].
        apply (HRnz (i + 1)); lia.
Qed.

Lemma strncmp_body : forall l, length l = 32%nat -> l = l0 ->
  rget l 10 = W (p + k) -> rget l 11 = W q -> rget l 12 = W n ->
  reach USEGS rom (Z_to_bv 64 0x2bd3e0) l M Post.
Proof.
  intros l Hl El H10 H11 H12. assert (Hse : same_except KS l0 l) by (subst l; apply same_except_refl).
  clear El. regs_open l Hl. subst a0 a1 a2.
  wp_snc [0x2bd3f4].
  pose proof (Hse 1%nat ltac:(cbv; intuition lia)) as Hra. cbn [rget lget] in Hra. subst ra.
  rewrite Wu by lia. split; intros Hb.
  - apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex] |]. intros _ i Hi. exfalso; lia.
  - exists (W (bv_unsigned (B k))). split; [apply (load1_bytes_at USEGS M p N B _ HB); lia|].
    pose proof (byte_range (B k)) as Hbk. rewrite !Wu by lia. split; intros Hb2.
    + exists (W (bv_unsigned (RB 0))). split; [replace q with (q + 0) at 1 by lia; apply HR; lia|].
      apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex] |].
      cbn [lget]. intros H0. exfalso. pose proof (byte_range (RB 0)) as Hr0.
      rewrite sub_W in H0. apply sub_zero_eq in H0; [|lia]. apply (HRnz 0); lia.
    + rewrite ?addi_W.
      assert (k <> z) by (intros E; apply Hb2; rewrite E; exact HBz).
      eapply (loop (Z.to_nat (n - 1 - 0)) 0); [lia | lia | lia | intros j Hj; lia | reflexivity
        | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; rewrite ?Z.add_0_r; try reflexivity; f_equal; lia.
Qed.

End Strncmp.

Theorem strncmp_cps : forall rom Post M p N B k z q n RB l,
  bytes_at M p N B -> 0 <= p -> p + N < 2 ^ 64 -> 0 <= k <= z -> z < N ->
  bv_unsigned (B z) = 0 -> (forall j, k <= j < z -> bv_unsigned (B j) <> 0) ->
  0 <= n < 2 ^ 63 -> 0 <= q /\ q + n < 2 ^ 64 ->
  (forall i, 0 <= i < n -> load_ok USEGS M (W (q + i)) 1 (W (bv_unsigned (RB i)))) ->
  (forall i, 0 <= i < n -> bv_unsigned (RB i) <> 0) ->
  length l = 32%nat -> rget l 10 = W (p + k) -> rget l 11 = W q -> rget l 12 = W n ->
  (forall l', length l' = 32%nat -> same_except KS l l' ->
     (bv_unsigned (rget l' 10) = 0 -> forall i, 0 <= i < n -> B (k + i) = RB i) ->
     reach USEGS rom (v_jalr (rget l 1) 0) l' M Post) ->
  reach USEGS rom (Z_to_bv 64 0x2bd3e0) l M Post.
Proof.
  intros rom Post M p N B k z q n RB l HB Hp HN Hk Hz HBz HBnz Hn Hq HR HRnz Hl H10 H11 H12 K.
  eapply strncmp_body with (l0 := l); eauto.
Qed.

