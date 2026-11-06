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

Ltac wp_scn stops := wp_go 0x2bcfa0 56%nat C_strchrnul_eq C_strchrnul stops.

Section Strchrnul.
Variable rom : mem.
Variable Post : word -> regfile -> mem -> Prop.
Variables (M : mem) (p N : Z) (B : Z -> byte) (k r c spv : Z).
Hypothesis HB : bytes_at M p N B.
Hypothesis Hp : 0 <= p.
Hypothesis HN : p + N < 2 ^ 64.
Hypothesis Hk : 0 <= k <= r.
Hypothesis Hr : r < N.
Hypothesis Hc : 0 < c < 256.
Hypothesis HBr : bv_unsigned (B r) = 0 \/ bv_unsigned (B r) = c.
Hypothesis HBn : forall j, k <= j < r -> bv_unsigned (B j) <> 0 /\ bv_unsigned (B j) <> c.
Hypothesis Hslack : (p + r) / 8 * 8 + 8 <= p + N.
Hypothesis Himg1 : img_ok M 0x3a628 0x3a630.
Hypothesis Himg2 : img_ok M 0x3a660 0x3a668.
Hypothesis Hsp : 0x3a668 <= spv - 16.
Hypothesis Hsp64 : spv < 2 ^ 64.
Hypothesis Hfr : wr_ok USEGS M (spv - 16) 16.
Hypothesis Hdisj : spv <= p \/ p + N <= spv - 16.

Definition KS : list nat := [10; 11; 12; 13; 14; 15; 16; 17]%nat.
Definition FR (x : word) : Prop := inr x (spv - 16) 16.
Variable l0 : regfile.
Hypothesis Hsp0 : rget l0 2 = W spv.
Hypothesis K : forall l' M', length l' = 32%nat -> same_except KS l0 l' -> rget l' 10 = W (p + r) ->
  unch M M' FR -> mem_grows M M' ->
  reach USEGS rom (v_jalr (rget l0 1) 0) l' M' Post.

(* [comment removed for export] *)
Definition MI (M1 : mem) : Prop :=
  bytes_at M1 p N B /\ img_ok M1 0x3a628 0x3a630 /\ img_ok M1 0x3a660 0x3a668
  /\ cell USEGS M1 (spv - 8) 8 (rget l0 1) /\ cell USEGS M1 (spv - 16) 8 (rget l0 8)
  /\ unch M M1 FR /\ mem_grows M M1.

Lemma hit : forall t, k <= t <= r -> bv_unsigned (B t) = 0 \/ bv_unsigned (B t) = c -> t = r.
Proof.
  intros t Ht H. destruct (Z.eq_dec t r); [assumption|]. exfalso.
  destruct (HBn t ltac:(lia)) as [H0 Hc']. destruct H; contradiction.
Qed.

(* [comment removed for export] *)
Lemma exit_blk : forall l M1, MI M1 -> length l = 32%nat -> same_except (8 :: 1 :: 2 :: KS)%nat l0 l ->
  rget l 2 = W (spv - 16) -> rget l 10 = W (p + r) ->
  reach USEGS rom (Z_to_bv 64 0x2bd070) l M1 Post.
Proof.
  intros l M1 (HB1 & Hi1 & Hi2 & Cra & Cs0 & Hun & Hgr) Hl Hse H2 H10. regs_open l Hl. subst sp a0.
  wp_scn (@nil Z). rewrite ?addi_W.
  exists (rget l0 1). split.
  { replace (spv - 16 + 8) with (spv - 8) by lia. apply load_cell8. exact Cra. }
  exists (rget l0 8). split; [apply load_cell8; exact Cs0|].
  rewrite ?addi_W.
  apply K; [reflexivity | | reflexivity | exact Hun | exact Hgr].
  same_fix Hse. cbn [rget lget] in Hsp0. rewrite Hsp0. f_equal. lia.
Qed.

Definition KS' : list nat := (8 :: 1 :: 2 :: KS)%nat.

(* [comment removed for export] *)
Lemma scan_loop : forall n t l M1, r - t = Z.of_nat n -> k <= t <= r ->
  MI M1 -> length l = 32%nat -> same_except KS' l0 l ->
  rget l 2 = W (spv - 16) -> rget l 10 = W (p + t - 1) -> rget l 11 = W c ->
  reach USEGS rom (Z_to_bv 64 0x2bd060) l M1 Post.
Proof.
  induction n as [n IH] using lt_wf_ind; intros t l M1 Hm Ht HMI Hl Hse H2 H10 H11.
  pose proof HMI as (HB1 & _). regs_open l Hl. subst sp a0 a1.
  wp_scn [0x2bd060; 0x2bd070]. rewrite ?addi_W.
  exists (W (bv_unsigned (B t))). split.
  { replace (p + t - 1 + 1) with (p + t) by lia. apply (load1_bytes_at USEGS M1 p N B _ HB1); lia. }
  pose proof (bv_unsigned_in_range 8 (B t)) as HBt; change (bv_modulus 8) with 256 in HBt.
  rewrite !Wu by lia. split; intros Hb.
  - apply exit_blk; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity |].
    cbn [rget lget]. f_equal. pose proof (hit t Ht (or_introl Hb)). lia.
  - split; intros Hb2.
    + assert (t <> r) by (intros ->; destruct HBr; contradiction).
      eapply (IH (Z.to_nat (r - (t + 1)))) with (t := t + 1); [lia | lia | lia | exact HMI | reflexivity
        | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; f_equal; lia.
    + apply exit_blk; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity |].
      cbn [rget lget]. f_equal. pose proof (hit t Ht (or_intror Hb2)). lia.
Qed.

Definition C1 : Z := 0x0101010101010100.
Definition HI8 : Z := 0x8080808080808080.
Definition ONESc : Z := 0x0101010101010101.

Lemma word_in : forall i, k <= i <= r -> (p + i) mod 8 = 0 -> i + 8 <= N.
Proof.
  intros i Hi Hal.
  pose proof (Z.div_mod (p + r) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (p + r) 8 ltac:(lia)).
  pose proof (Z.div_mod (p + i) 8 ltac:(lia)).
  assert ((p + i) / 8 <= (p + r) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma word_loop : forall n i l M1, r - i = Z.of_nat n -> k <= i <= r -> (p + i) mod 8 = 0 ->
  (forall j, 0 <= j < 8 -> bv_unsigned (B (i + j)) <> 0) ->
  MI M1 -> length l = 32%nat -> same_except KS' l0 l ->
  rget l 2 = W (spv - 16) -> rget l 10 = W (p + i) -> rget l 11 = W c ->
  rget l 12 = W C1 -> rget l 13 = W HI8 -> rget l 14 = W (V (bl8 B i)) -> rget l 15 = W (c * ONESc) ->
  reach USEGS rom (Z_to_bv 64 0x2bd008) l M1 Post.
Proof.
  induction n as [n IH] using lt_wf_ind; intros i l M1 Hm Hi Hal Hnz HMI Hl Hse H2 H10 H11 H12 H13 H14 H15.
  pose proof HMI as (HB1 & _). pose proof (word_in i Hi Hal) as Hi8.
  regs_open l Hl. subst sp a0 a1 a2 a3 a4 a5.
  wp_scn [0x2bd008; 0x2bd060]. unfold C1, HI8, ONESc. split; intros Hb.
  - (* [comment removed for export] *)
    clear Hb. rewrite ?addi_W.
    eapply (scan_loop (Z.to_nat (r - i)) i); [lia | lia | exact HMI | reflexivity
      | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; f_equal; lia.
  - pose proof (test_c_machine B i c ltac:(lia) Hb) as Hnc. clear Hb.
    assert (Hr8 : i + 8 <= r).
    { destruct (Z_lt_le_dec r (i + 8)); [|assumption]. exfalso.
      replace r with (i + (r - i)) in HBr by lia.
      destruct HBr as [E|E]; [apply (Hnz (r - i)) | apply (Hnc (r - i))]; (lia || exact E). }
    assert (Hal8 : (p + (i + 8)) mod 8 = 0).
    { rewrite <- Hal. replace (p + (i + 8)) with (p + i + 1 * 8) by lia. apply Z_mod_plus_full. }
    pose proof (word_in (i + 8) ltac:(lia) Hal8) as Hi16.
    rewrite ?addi_W.
    exists (W (V (bl8 B (i + 8)))). split.
    { replace (p + i + 8) with (p + (i + 8)) by lia. apply (load8_bytes_at USEGS M1 p N B _ HB1); lia. }
    split; intros Hb.
    + pose proof (test_z_machine B (i + 8) Hb) as Hnz8. clear Hb.
      eapply (IH (Z.to_nat (r - (i + 8)))) with (i := i + 8); [lia | lia | lia | exact Hal8 | exact Hnz8 | exact HMI
        | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; f_equal; lia.
    + clear Hb. rewrite ?addi_W.
      eapply (scan_loop (Z.to_nat (r - (i + 8))) (i + 8)); [lia | lia | exact HMI | reflexivity
        | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; f_equal; lia.
Qed.

(* [comment removed for export] *)
Lemma word_init : forall i l M1, k <= i <= r -> (p + i) mod 8 = 0 ->
  MI M1 -> length l = 32%nat -> same_except KS' l0 l ->
  rget l 2 = W (spv - 16) -> rget l 10 = W (p + i) -> rget l 11 = W c ->
  reach USEGS rom (Z_to_bv 64 0x2bcfdc) l M1 Post.
Proof.
  intros i l M1 Hi Hal HMI Hl Hse H2 H10 H11.
  pose proof HMI as (HB1 & Hi1 & Hi2 & _). pose proof (word_in i Hi Hal) as Hi8.
  regs_open l Hl. subst sp a0 a1.
  wp_scn [0x2bd008; 0x2bd060]. rewrite ?addi_W.
  exists (W C1). split.
  { eapply (load_img USEGS M1 _ _ 0x3a660 8); [exact Hi2 | lia | lia | lia | lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
  exists (W (V (bl8 B i))). split; [apply (load8_bytes_at USEGS M1 p N B _ HB1); lia|].
  exists (W HI8). split.
  { eapply (load_img USEGS M1 _ _ 0x3a628 8); [exact Hi1 | lia | lia | lia | lia | vm_compute; reflexivity | vm_compute; reflexivity]. }
  unfold C1, HI8. split; intros Hb.
  - clear Hb. rewrite ?addi_W.
    eapply (scan_loop (Z.to_nat (r - i)) i); [lia | lia | exact HMI | reflexivity
      | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; f_equal; lia.
  - pose proof (test_z_machine B i Hb) as Hnz. clear Hb. rewrite ?addi_W, ?mul_W.
    eapply (word_loop (Z.to_nat (r - i)) i); [lia | lia | exact Hal | exact Hnz | exact HMI | reflexivity
      | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma head_loop : forall n t l M1, r - t = Z.of_nat n -> k <= t <= r ->
  MI M1 -> length l = 32%nat -> same_except KS' l0 l ->
  rget l 2 = W (spv - 16) -> rget l 10 = W (p + t) -> rget l 11 = W c -> rget l 12 = W (p + t + 1) ->
  reach USEGS rom (Z_to_bv 64 0x2bcfc0) l M1 Post.
Proof.
  induction n as [n IH] using lt_wf_ind; intros t l M1 Hm Ht HMI Hl Hse H2 H10 H11 H12.
  pose proof HMI as (HB1 & _). regs_open l Hl. subst sp a0 a1 a2.
  wp_scn [0x2bcfc0; 0x2bcfdc; 0x2bd070].
  exists (W (bv_unsigned (B t))). split; [apply (load1_bytes_at USEGS M1 p N B _ HB1); lia|].
  pose proof (bv_unsigned_in_range 8 (B t)) as HBt; change (bv_modulus 8) with 256 in HBt.
  rewrite !Wu by lia. split; intros Hb.
  - apply exit_blk; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity |].
    cbn [rget lget]. f_equal. pose proof (hit t Ht (or_introl Hb)). lia.
  - split; intros Hb2.
    + apply exit_blk; [exact HMI | reflexivity | eapply same_except_trans; [exact Hse | same_ex] | reflexivity |].
      cbn [rget lget]. f_equal. pose proof (hit t Ht (or_intror Hb2)). lia.
    + assert (t <> r) by (intros ->; destruct HBr; contradiction).
      rewrite ?addi_W. change 7 with (Z.ones 3). rewrite u_andi_ones by lia. rewrite Wu by lia.
      split; intros Hb3.
      * eapply (IH (Z.to_nat (r - (t + 1)))) with (t := t + 1); [lia | lia | lia | exact HMI | reflexivity
          | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; f_equal; lia.
      * eapply (word_init (t + 1)); [lia | | exact HMI | reflexivity
          | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; try (f_equal; lia).
Qed.

(* [comment removed for export] *)
Lemma MI_prologue :
  MI (wbytes (wbytes M (W (spv - 8)) (word_to_le_bytes 8 (rget l0 1))) (W (spv - 16)) (word_to_le_bytes 8 (rget l0 8))).
Proof.
  set (M1 := wbytes M (W (spv - 8)) (word_to_le_bytes 8 (rget l0 1))).
  set (M2 := wbytes M1 (W (spv - 16)) (word_to_le_bytes 8 (rget l0 8))).
  assert (U1 : unch M M1 FR).
  { apply unch_store; [apply unch_refl | lia | rewrite length_N_to_le_bytes; lia |].
    intros x Hx. rewrite length_N_to_le_bytes in Hx. unfold FR, inr in *. lia. }
  assert (U2 : unch M M2 FR).
  { apply unch_store; [exact U1 | lia | rewrite length_N_to_le_bytes; lia |].
    intros x Hx. rewrite length_N_to_le_bytes in Hx. unfold FR, inr in *. lia. }
  unfold MI. fold M1. fold M2. repeat split.
  - eapply bytes_at_unch; [exact U2 | exact Hp | exact HN | | exact HB]. intros x Hx. unfold FR, inr in *. lia.
  - eapply img_unch; [exact U2 | lia | lia | | exact Himg1]. intros x Hx. unfold FR, inr in *. lia.
  - eapply img_unch; [exact U2 | lia | lia | | exact Himg2]. intros x Hx. unfold FR, inr in *. lia.
  - apply cell_store_other; [lia | lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia |].
    apply cell_store_same; lia.
  - apply cell_store_same; lia.
  - exact U2.
  - eapply mem_grows_trans; apply wbytes_grows.
Qed.

Lemma strchrnul_body : forall l, length l = 32%nat -> l = l0 ->
  rget l 10 = W (p + k) -> bv_unsigned (rget l 11) mod 256 = c ->
  reach USEGS rom (Z_to_bv 64 0x2bcfa0) l M Post.
Proof.
  intros l Hl El H10 H11. assert (Hse : same_except KS' l0 l) by (subst l; apply same_except_refl).
  pose proof Hsp0 as H2. rewrite <- El in H2.
  assert (E1 : rget l 1 = rget l0 1) by (rewrite El; reflexivity).
  assert (E8 : rget l 8 = rget l0 8) by (rewrite El; reflexivity).
  clear El. regs_open l Hl. subst sp a0.
  assert (Ea1 : v_andi a1 255 = W c).
  { rewrite <- (W_u (v_andi a1 255)). f_equal. change 255 with (Z.ones 8). rewrite u_andi_ones by lia. exact H11. }
  wp_scn [0x2bcfc0; 0x2bcfdc]. rewrite ?addi_W, Ea1.
  split; [eapply wr_ok_store; [exact Hfr | lia | lia]|].
  split; [eapply wr_ok_store; [apply (wr_ok_grows USEGS _ _ _ _ (wbytes_grows _ _ _) Hfr) | lia | lia]|].
  rewrite Wu by lia.
  replace (spv + -16 + 8) with (spv - 8) by lia. replace (spv + -16) with (spv - 16) by lia.
  rewrite E1, E8. pose proof MI_prologue as HMI.
  split; intros Hb; [exfalso; lia|]. clear Hb.
  change 7 with (Z.ones 3). rewrite u_andi_ones by lia. rewrite Wu by lia.
  split; intros Hb.
  - eapply (word_init k); [lia | exact Hb | exact HMI | reflexivity
      | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; reflexivity.
  - clear Hb. eapply (head_loop (Z.to_nat (r - k)) k); [lia | lia | exact HMI | reflexivity
      | eapply same_except_trans; [exact Hse | same_ex] | .. ]; cbn [rget lget]; try reflexivity; f_equal; lia.
Qed.

End Strchrnul.

(* [comment removed for export] *)
Theorem strchrnul_cps : forall rom Post M p N B k r c spv l,
  bytes_at M p N B -> 0 <= p -> p + N < 2 ^ 64 -> 0 <= k <= r -> r < N -> 0 < c < 256 ->
  (bv_unsigned (B r) = 0 \/ bv_unsigned (B r) = c) ->
  (forall j, k <= j < r -> bv_unsigned (B j) <> 0 /\ bv_unsigned (B j) <> c) ->
  (p + r) / 8 * 8 + 8 <= p + N ->
  img_ok M 0x3a628 0x3a630 -> img_ok M 0x3a660 0x3a668 ->
  0x3a668 <= spv - 16 -> spv < 2 ^ 64 -> wr_ok USEGS M (spv - 16) 16 -> (spv <= p \/ p + N <= spv - 16) ->
  length l = 32%nat -> rget l 2 = W spv -> rget l 10 = W (p + k) -> bv_unsigned (rget l 11) mod 256 = c ->
  (forall l' M', length l' = 32%nat -> same_except KS l l' -> rget l' 10 = W (p + r) ->
                 unch M M' (FR spv) -> mem_grows M M' ->
                 reach USEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach USEGS rom (Z_to_bv 64 0x2bcfa0) l M Post.
Proof.
  intros rom Post M p N B k r c spv l HB Hp HN Hk Hr Hc HBr HBn Hsl Hi1 Hi2 Hsp Hsp64 Hfr Hdj Hl H2 H10 H11 K.
  eapply (strchrnul_body rom Post M p N B k r c spv HB Hp HN Hk Hr Hc HBr HBn Hsl Hi1 Hi2 Hsp Hsp64 Hfr Hdj l H2 K l Hl eq_refl H10 H11).
Qed.

(* [comment removed for export] *)
Ltac wp_sc stops := wp_go 0x2bcf64 15%nat C_strchr_eq C_strchr stops.

Definition FR2 (spv : Z) (x : word) : Prop := inr x (spv - 32) 32.

Theorem strchr_cps : forall rom Post M p N B k r c spv l,
  bytes_at M p N B -> 0 <= p -> p + N < 2 ^ 64 -> 0 <= k <= r -> r < N -> 0 < c < 256 ->
  (bv_unsigned (B r) = 0 \/ bv_unsigned (B r) = c) ->
  (forall j, k <= j < r -> bv_unsigned (B j) <> 0 /\ bv_unsigned (B j) <> c) ->
  (p + r) / 8 * 8 + 8 <= p + N ->
  img_ok M 0x3a628 0x3a630 -> img_ok M 0x3a660 0x3a668 ->
  0x3a668 <= spv - 32 -> spv < 2 ^ 64 -> wr_ok USEGS M (spv - 32) 32 -> (spv <= p \/ p + N <= spv - 32) ->
  length l = 32%nat -> rget l 2 = W spv -> rget l 10 = W (p + k) -> bv_unsigned (rget l 11) mod 256 = c ->
  (forall l' M', length l' = 32%nat -> same_except KS l l' ->
                 rget l' 10 = W (if Z.eqb (bv_unsigned (B r)) c then p + r else 0) ->
                 unch M M' (FR2 spv) -> mem_grows M M' ->
                 reach USEGS rom (v_jalr (rget l 1) 0) l' M' Post) ->
  reach USEGS rom (Z_to_bv 64 0x2bcf64) l M Post.
Proof.
  intros rom Post M p N B k r c spv l HB Hp HN Hk Hr Hc HBr HBn Hsl Hi1 Hi2 Hsp Hsp64 Hfr Hdj Hl H2 H10 H11 K.
  regs_open l Hl. subst sp a0.
  wp_sc (@nil Z). rewrite ?addi_W.
  split; [eapply wr_ok_store; [exact Hfr | lia | lia]|].
  split; [eapply wr_ok_store; [apply (wr_ok_grows USEGS _ _ _ _ (wbytes_grows _ _ _) Hfr) | lia | lia]|].
  replace (spv + -16 + 8) with (spv - 8) by lia. replace (spv + -16) with (spv - 16) by lia.
  set (M1 := wbytes M (W (spv - 8)) (word_to_le_bytes 8 ra)).
  set (M2 := wbytes M1 (W (spv - 16)) (word_to_le_bytes 8 s0)).
  assert (U2 : unch M M2 (FR2 spv)).
  { apply unch_store; [apply unch_store; [apply unch_refl | lia | rewrite length_N_to_le_bytes; lia |] | lia | rewrite length_N_to_le_bytes; lia |];
      intros x Hx; rewrite length_N_to_le_bytes in Hx; unfold FR2, inr in *; lia. }
  assert (G2 : mem_grows M M2) by (eapply mem_grows_trans; apply wbytes_grows).
  assert (Cra : cell USEGS M2 (spv - 8) 8 ra).
  { apply cell_store_other; [lia | lia | lia | rewrite length_N_to_le_bytes; lia | rewrite length_N_to_le_bytes; lia |].
    apply cell_store_same; lia. }
  assert (Cs0 : cell USEGS M2 (spv - 16) 8 s0) by (apply cell_store_same; lia).
  eapply (strchrnul_cps rom Post M2 p N B k r c (spv - 16)); try eassumption; try lia.
  - eapply bytes_at_unch; [exact U2 | exact Hp | exact HN | | exact HB]. intros x Hx. unfold FR2, inr in *. lia.
  - eapply img_unch; [exact U2 | lia | lia | | exact Hi1]. intros x Hx. unfold FR2, inr in *. lia.
  - eapply img_unch; [exact U2 | lia | lia | | exact Hi2]. intros x Hx. unfold FR2, inr in *. lia.
  - eapply wr_ok_sub; [apply (wr_ok_grows USEGS _ _ _ _ G2 Hfr) | lia | lia].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* [comment removed for export] *)
    intros l' M' Hl' Hse' H10' HU' HG'. cbn [rget lget].
    replace (v_jalr (Z_to_bv 64 2871160) 0) with (Z_to_bv 64 0x2bcf78) by reflexivity.
    assert (E2 : rget l' 2 = W (spv - 16)) by (rewrite (Hse' 2%nat) by (cbv; intuition lia); reflexivity).
    assert (E8 : rget l' 8 = a1) by (rewrite (Hse' 8%nat) by (cbv; intuition lia); reflexivity).
    assert (Hse2 : same_except (8 :: 1 :: 2 :: KS)%nat
              [x0; ra; Z_to_bv 64 spv; gp; tp; t0; t1; t2; s0; s1; Z_to_bv 64 (p + k); a1; a2; a3; a4; a5; a6; a7; s2; s3;
               s4; s5; s6; s7; s8; s9; s10; s11; t3; t4; t5; t6] l').
    { eapply same_except_trans; [|eapply same_except_weaken; [exact Hse'|]].
      - same_ex.
      - intros j Hj. cbn [In] in *. tauto. }
    clear Hse'. revert H11 HBr HBn Hc K. regs_open l' Hl'. subst. intros H11 HBr HBn Hc K.
    assert (HB' : bytes_at M' p N B).
    { eapply bytes_at_unch; [exact HU' | exact Hp | exact HN | |].
      - intros x Hx. unfold FR, inr in *. lia.
      - eapply bytes_at_unch; [exact U2 | exact Hp | exact HN | | exact HB]. intros x Hx. unfold FR2, inr in *. lia. }
    assert (Cra' : cell USEGS M' (spv - 8) 8 ra).
    { eapply cell_unch; [exact HU' | lia | lia | | exact Cra]. intros x Hx. unfold FR, inr in *. lia. }
    assert (Cs0' : cell USEGS M' (spv - 16) 8 s0).
    { eapply cell_unch; [exact HU' | lia | lia | | exact Cs0]. intros x Hx. unfold FR, inr in *. lia. }
    wp_sc (@nil Z). rewrite ?addi_W.
    exists (W (bv_unsigned (B r))). split; [apply (load1_bytes_at USEGS M' p N B _ HB'); lia|].
    exists ra. split; [replace (spv - 16 + 8) with (spv - 8) by lia; apply load_cell8; exact Cra'|].
    exists s0. split; [apply load_cell8; exact Cs0'|].
    rewrite ?addi_W.
    apply K; [reflexivity | | | | ].
    + same_fix Hse2. f_equal. lia.
    + cbn [lget].
      pose proof (bv_unsigned_in_range 8 (B r)) as HBt; change (bv_modulus 8) with 256 in HBt.
      assert (Ea : v_andi a1 255 = W c).
      { rewrite <- (W_u (v_andi a1 255)). f_equal. change 255 with (Z.ones 8). rewrite u_andi_ones by lia. exact H11. }
      rewrite Ea. rewrite xor_W by lia.
      destruct (Z.eqb_spec (bv_unsigned (B r)) c) as [E|E].
      * rewrite E, Z.lxor_nilpotent, sltu0_W0, addi_W. cbn [Z.add]. apply and_m1_l.
      * rewrite sltu0_nz.
        -- rewrite addi_W. cbn [Z.add]. apply and_0_l.
        -- rewrite Wu by (apply Z_lxor_range; lia). intros H0. apply Z.lxor_eq in H0. contradiction.
    + eapply unch_trans; [exact U2|]. eapply unch_weaken; [exact HU'|]. intros x Hx. unfold FR, FR2, inr in *. lia.
    + eapply mem_grows_trans; eassumption.
Qed.
