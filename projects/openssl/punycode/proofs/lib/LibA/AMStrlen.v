(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import WpEngine LibKit HasZero StrKit WpTac.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import ACode ArCode.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac wp_eval_strlen := cbv beta iota zeta delta [wp cnth C_strlen in_stops pc_eqb rget lget rset lset vaddr val_imm val_sh val_op val_shw val_opw val_mul val_mulw br_yes br_no szn ext_load].

Ltac wp_strlen idx stops :=
  lazymatch goal with
  | |- reach _ ?rom (Z_to_bv 64 ?pc) ?l ?M ?Post =>
      change (Z_to_bv 64 pc) with (Z_to_bv 64 (0x52ade8 + 4 * Z.of_nat idx));
      apply (wp_sound ASEGS rom 0x52ade8 36 stops Post 100 true);
      rewrite C_strlen_eq; wp_eval_strlen; wp_simpl_goal
  end.

Section Strlen.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (p N : Z) (B : Z -> byte) (k z : Z).
Hypothesis HB : bytes_at M p N B.
Hypothesis Hp : 0 <= p.
Hypothesis HN : p + N < 2 ^ 64.
Hypothesis Hk : 0 <= k <= z.
Hypothesis Hz : z < N.
Hypothesis HBz : bv_unsigned (B z) = 0.
Hypothesis HBnz : forall j, k <= j < z -> bv_unsigned (B j) <> 0.
Hypothesis Hslack : (p + z) / 8 * 8 + 8 <= p + N.

Hypothesis Himg1 : img_ok M 0x10490 0x10498.
Hypothesis Himg2 : img_ok M 0x104c8 0x104d0.

Definition KS : list nat := [10; 11; 12; 13; 14; 15; 16]%nat.
Variable l0 : regfile.
Hypothesis K : forall l', length l' = 32%nat -> same_except KS l0 l' -> rget l' 10 = W (z - k) ->
  reach ASEGS rom (v_jalr (rget l0 1) 0) l' M Post.

Lemma first_zero : forall t, k <= t <= z -> bv_unsigned (B t) = 0 -> t = z.
Proof. intros t Ht H0. destruct (Z.eq_dec t z); [assumption|]. exfalso. apply (HBnz t); [lia | exact H0]. Qed.

(* [comment removed for export] *)
Lemma tail_loop : forall n t l, z - t = Z.of_nat n -> k <= t <= z ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 10 = W (p + k) -> rget l 11 = W (p + t - 1) -> rget l 12 = W (p + t) ->
  reach ASEGS rom (Z_to_bv 64 0x52ae58) l M Post.
Proof.
  induction n as [|n IH]; intros t l Hm Ht Hl Hse H10 H11 H12; regs_open l Hl; subst a0 a1 a2;
    wp_strlen 28%nat [0x52ae58];
    (exists (W (bv_unsigned (B t))); split; [apply (load1_bytes_at ASEGS M p N B t HB); lia|]);
    pose proof (bv_unsigned_in_range 8 (B t)) as HBt; change (bv_modulus 8) with 256 in HBt;
    rewrite Wu by lia; split; intros Hb; rewrite ?addi_W, ?sub_W.
  - exfalso. apply Hb. replace t with z by lia. exact HBz.
  - pose proof (Hse 1%nat ltac:(cbv; intuition lia)) as Hra. cbn [rget lget] in Hra. subst ra.
    apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex] |].
    cbn [lget]. f_equal. lia.
  - assert (t <> z) by (intros ->; apply Hb, HBz).
    eapply (IH (t + 1)); [lia | lia | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | | | ];
      cbn [rget lget]; f_equal; lia.
  - pose proof (Hse 1%nat ltac:(cbv; intuition lia)) as Hra. cbn [rget lget] in Hra. subst ra.
    apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex] |].
    cbn [lget]. f_equal. pose proof (first_zero t ltac:(lia) Hb). lia.
Qed.



Definition C1 : Z := 0x0101010101010100.
Definition HI8 : Z := 0x8080808080808080.

(* [comment removed for export] *)
Lemma word_loop : forall n i l, z - i = Z.of_nat n -> k <= i <= z -> (p + i) mod 8 = 0 ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 10 = W (p + k) -> rget l 11 = W (p + i - 9) -> rget l 12 = W (p + i - 8) ->
  rget l 13 = W C1 -> rget l 14 = W HI8 ->
  reach ASEGS rom (Z_to_bv 64 0x52ae3c) l M Post.
Proof.
  induction n as [n IH] using lt_wf_ind; intros i l Hm Hi Hal Hl Hse H10 H11 H12 H13 H14;
    regs_open l Hl; subst a0 a1 a2 a3 a4.
  assert (Hi8 : i + 8 <= N).
  { pose proof (Z.div_mod (p + z) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p + z) 8 ltac:(lia)).
    pose proof (Z.div_mod (p + i) 8 ltac:(lia)). 
    assert ((p + i) / 8 <= (p + z) / 8) by (apply Z.div_le_mono; lia). lia. }
  wp_strlen 21%nat [0x52ae3c; 0x52ae58].
  rewrite ?addi_W.
  exists (W (V (bl8 B i))). split.
  { replace (p + i - 8 + 8) with (p + i) by lia. apply (load8_bytes_at ASEGS M p N B i HB); lia. }
  rewrite ?sub_W, ?addi_W. rewrite u_and, u_or. unfold C1, HI8. rewrite !Wu_mod.
  split; intros Hb.
  - pose proof (hz_test B i Hb) as Hnz. clear Hb.
    assert (i + 8 <= z).
    { destruct (Z_lt_le_dec z (i + 8)); [|assumption]. exfalso.
      apply (Hnz (z - i)); [lia|]. replace (i + (z - i)) with z by lia. exact HBz. }
    eapply (IH (Z.to_nat (z - (i + 8)))) with (i := i + 8); [lia | lia | lia | | reflexivity
      | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; try (f_equal; lia).
  - eapply (tail_loop (Z.to_nat (z - i)) i); [lia | lia | reflexivity
      | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; f_equal; lia.
Qed.


(* [comment removed for export] *)
Lemma word_init : forall i l, k <= i <= z -> (p + i) mod 8 = 0 ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 10 = W (p + k) -> rget l 12 = W (p + i) ->
  reach ASEGS rom (Z_to_bv 64 0x52ae24) l M Post.
Proof.
  intros i l Hi Hal Hl Hse H10 H12. regs_open l Hl. subst a0 a2.
  wp_strlen 15%nat [0x52ae3c].
  rewrite ?addi_W.
  exists (W C1). split.
  { eapply (load_img ASEGS M _ _ 0x104c8 8); [exact Himg2 | lia | lia | lia | lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
  exists (W HI8). split.
  { eapply (load_img ASEGS M _ _ 0x10490 8); [exact Himg1 | lia | lia | lia | lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
  rewrite ?addi_W.
  eapply (word_loop (Z.to_nat (z - i)) i); [lia | lia | exact Hal | reflexivity
    | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma head_loop : forall n j l, z - (k + j) = Z.of_nat n -> 0 <= j -> k + j + 1 <= z ->
  length l = 32%nat -> same_except KS l0 l ->
  rget l 10 = W (p + k) -> rget l 11 = W (p + k + j) -> rget l 12 = W (p + k + j + 1) ->
  reach ASEGS rom (Z_to_bv 64 0x52ae04) l M Post.
Proof.
  induction n as [n IH] using lt_wf_ind; intros j l Hm Hj Hjz Hl Hse H10 H11 H12;
    regs_open l Hl; subst a0 a1 a2.
  wp_strlen 7%nat [0x52ae04; 0x52ae24].
  rewrite ?addi_W. change 7 with (Z.ones 3). rewrite u_andi_ones by lia. rewrite Wu by lia.
  split; intros Hb.
  - eapply (word_init (k + j + 1)); [lia | | reflexivity
      | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try (f_equal; lia).
  - clear Hb. exists (W (bv_unsigned (B (k + j + 1)))). split.
    { replace (p + k + j + 1) with (p + (k + j + 1)) by lia. apply (load1_bytes_at ASEGS M p N B _ HB); lia. }
    pose proof (bv_unsigned_in_range 8 (B (k + j + 1))) as HBt; change (bv_modulus 8) with 256 in HBt.
    rewrite Wu by lia. split; intros Hb; rewrite ?addi_W, ?sub_W.
    + assert (k + j + 1 <> z) by (intros E; rewrite E in Hb; apply Hb, HBz).
      eapply (IH (Z.to_nat (z - (k + (j + 1))))) with (j := j + 1); [lia | lia | lia | lia | reflexivity
        | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; f_equal; lia.
    + pose proof (Hse 1%nat ltac:(cbv; intuition lia)) as Hra. cbn [rget lget] in Hra. subst ra.
      apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex] |].
      cbn [lget]. f_equal. pose proof (first_zero (k + j + 1) ltac:(lia) Hb). lia.
Qed.

(* [comment removed for export] *)
Lemma strlen_body : forall l, length l = 32%nat -> l = l0 -> rget l 10 = W (p + k) ->
  reach ASEGS rom (Z_to_bv 64 0x52ade8) l M Post.
Proof.
  intros l Hl El H10. assert (Hse : same_except KS l0 l) by (subst l; apply same_except_refl).
  clear El. regs_open l Hl. subst a0.
  wp_strlen 0%nat [0x52ae04; 0x52ae24].
  change 7 with (Z.ones 3). rewrite u_andi_ones by lia. rewrite Wu by lia.
  split; intros Hb.
  - eapply (word_init k); [lia | exact Hb | reflexivity
      | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; reflexivity.
  - clear Hb. exists (W (bv_unsigned (B k))). split.
    { apply (load1_bytes_at ASEGS M p N B _ HB); lia. }
    pose proof (bv_unsigned_in_range 8 (B k)) as HBt; change (bv_modulus 8) with 256 in HBt.
    rewrite Wu by lia. split; intros Hb; rewrite ?addi_W, ?sub_W.
    + pose proof (Hse 1%nat ltac:(cbv; intuition lia)) as Hra. cbn [rget lget] in Hra. subst ra.
      apply K; [reflexivity | eapply same_except_trans; [exact Hse | same_ex] |].
      cbn [lget]. f_equal. pose proof (first_zero k ltac:(lia) Hb). lia.
    + assert (k <> z) by (intros E; rewrite E in Hb; apply Hb, HBz).
      eapply (head_loop (Z.to_nat (z - (k + 0))) 0); [lia | lia | lia | reflexivity
        | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; f_equal; lia.
Qed.

End Strlen.

(* [comment removed for export] *)
Theorem strlen_cps : forall rom Post M p N B k z l,
  bytes_at M p N B -> 0 <= p -> p + N < 2 ^ 64 -> 0 <= k <= z -> z < N ->
  bv_unsigned (B z) = 0 -> (forall j, k <= j < z -> bv_unsigned (B j) <> 0) ->
  (p + z) / 8 * 8 + 8 <= p + N ->
  img_ok M 0x10490 0x10498 -> img_ok M 0x104c8 0x104d0 ->
  length l = 32%nat -> rget l 10 = W (p + k) ->
  (forall l', length l' = 32%nat -> same_except KS l l' -> rget l' 10 = W (z - k) ->
              reach ASEGS rom (v_jalr (rget l 1) 0) l' M Post) ->
  reach ASEGS rom (Z_to_bv 64 0x52ade8) l M Post.
Proof. intros. eapply strlen_body with (l0 := l); eauto. Qed.

