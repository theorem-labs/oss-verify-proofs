(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefEnframeArith.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import BothRegionPoisoned.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require BothMemset.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require MemsetLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require BothMemset_code.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VBothIcMemset_code.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastV.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan.BothRegionPoisoned.gr ::= gr_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := AsanUbsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zbv_wrap_sub : forall a, Z_to_bv 64 (a - 2 ^ 64) = Z_to_bv 64 a.
Proof. intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. apply (bv_wrap_sub_modulus_1 64 a). Qed.
Lemma zbv_wrap_add : forall a, Z_to_bv 64 (a + 2 ^ 64) = Z_to_bv 64 a.
Proof. intros a. apply bv_eq. rewrite !Z_to_bv_unsigned. apply (bv_wrap_add_modulus_1 64 a). Qed.
Lemma v_not_zbv : forall d, (0 <= d < 2 ^ 64)%Z -> v_xori (Z_to_bv 64 d) (-1) = Z_to_bv 64 (2 ^ 64 - 1 - d).
Proof. intros d Hd. rewrite <- (zbv_self (v_xori (Z_to_bv 64 d) (-1))). rewrite u_not by lia. reflexivity. Qed.
Lemma wbytes_agree : forall bs m1 m2 (a x : word), m1 x = m2 x -> wbytes m1 a bs x = wbytes m2 a bs x.
Proof.
  induction bs as [|b bs IH]; intros m1 m2 a x Hx; cbn [wbytes]; [exact Hx|].
  apply IH. cbv beta. destruct (bv_eqb x a); [reflexivity|exact Hx].
Qed.
Lemma wbytes_keep : forall bs m (a x : word), m x <> None -> wbytes m a bs x <> None.
Proof.
  induction bs as [|b bs IH]; intros m a x Hx; cbn [wbytes]; [exact Hx|].
  apply IH. cbv beta. destruct (bv_eqb x a); [discriminate|exact Hx].
Qed.
Lemma lit_cccec : v_addi (0x54598 : word) 4 = (0x5459c : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma lit_cce40 : v_addi (0x546ec : word) 4 = (0x546f0 : word). Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma ret_ok_cccec : ret_ok (0x5459c : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma ret_ok_cce40 : ret_ok (0x546f0 : word). Proof. apply ret_ok_even. vm_compute. reflexivity. Qed.
Lemma jalr_memset : v_jalr (Z_to_bv 64 0xa2bec) 0 = Z_to_bv 64 BothMemset_code.ms_base.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Definition IM_ENTRY : Z := 0x53e18.
Definition IM_FRAME : Z := 2216.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition im_cells (m : word -> option byte) : Prop :=
  cells m
  /\ cell m 0xaa020 0xb2899 /\ rdn SEGS m (Z_to_bv 64 0xb2899) 1 = Some [Z_to_bv 8 1]
  /\ cell m 0xab330 0xa2bec.

Record imH (mem : word -> option byte) (d c n usp : Z) : Prop := {
  im_n    : (0 <= n <= 2 ^ 40)%Z;
  im_d    : (0 <= d)%Z;
  im_c    : (0 <= c < 2 ^ 64)%Z;
  im_dn   : (d + n < 2 ^ 64)%Z;
  im_rng  : (0 < n)%Z -> (d + n <= kLowEnd)%Z \/ (kHighBeg <= d /\ d + n <= kHighEnd)%Z;
  im_sp   : (SB + IM_FRAME + 8 <= usp < 2 ^ 64)%Z;
  (* [comment removed for export] *)
  im_dst  : (n = 0 \/ usp <= d \/ d + n <= usp - IM_FRAME)%Z;
  im_shd  : (0 < n)%Z -> (SB + (d + n - 1) / 8 + 8 < usp - IM_FRAME)%Z;
  (* [comment removed for export] *)
  im_zero : forall g, (0 < n)%Z -> (d / 8 <= g < (d + n - 1) / 8)%Z -> mem (Z_to_bv 64 (SB + g)) = Some (Z_to_bv 8 0);
  im_last : (0 < n)%Z -> exists b1 : byte, mem (Z_to_bv 64 (SB + (d + n - 1) / 8)) = Some b1
                                     /\ (bv_unsigned b1 = 0%Z \/ ((d + n - 1) mod 8 < bv_unsigned b1 < 8)%Z);
  (* [comment removed for export] *)
  im_w1   : (0 < n)%Z -> exists w : word, rdn SEGS mem (Z_to_bv 64 ((SB + d / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w);
  im_w2   : (0 < n)%Z -> exists w : word, rdn SEGS mem (Z_to_bv 64 ((SB + (d + n - 1) / 8) / 8 * 8)) 8 = Some (word_to_le_bytes 8 w);
  (* [comment removed for export] *)
  im_dok  : forall j, (0 <= j < n)%Z -> store_ok SEGS mem (Z_to_bv 64 (d + j)) 1 = true;
  im_stk  : forall a, (usp - IM_FRAME <= a < usp)%Z -> store_ok SEGS mem (Z_to_bv 64 a) 1 = true;
  im_cel  : im_cells mem
}.

(* [comment removed for export] *)
Definition im_clob (r : reg) : bool :=
  (bv_eqb r 5 || bv_eqb r 6 || bv_eqb r 7 || bv_eqb r 10 || bv_eqb r 11 || bv_eqb r 12 || bv_eqb r 13 || bv_eqb r 14
   || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17 || bv_eqb r 28 || bv_eqb r 29 || bv_eqb r 30 || bv_eqb r 31)%bool.

Section IM.
  Variables (mem rom : word -> option byte) (d c n usp : Z).
  Hypothesis H : imH mem d c n usp.
  Variable regs0 : bvmap 5 word.
  Variable ra : word.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H01 : getr regs0 1 = ra.
  Hypothesis H02 : getr regs0 2 = Z_to_bv 64 usp.
  Hypothesis H010 : getr regs0 10 = Z_to_bv 64 d.
  Hypothesis H011 : getr regs0 11 = Z_to_bv 64 c.
  Hypothesis H012 : getr regs0 12 = Z_to_bv 64 n.

  Let Hn := im_n _ _ _ _ _ H.
  Let Hd := im_d _ _ _ _ _ H.
  #[using="mem d c n H"] Lemma Hsp : (0x7fff8000 + 2224 <= usp < 2 ^ 64)%Z.
  Proof. pose proof (im_sp _ _ _ _ _ H). unfold IM_FRAME, SB in *. lia. Qed.

  (* [comment removed for export] *)
  Definition p8 : word -> option byte :=
    let w (o : Z) (v : word) (m : word -> option byte) := wbytes m (Z_to_bv 64 (usp - o)) (word_to_le_bytes 8 v) in
    w 64%Z (getr regs0 22) (w 56%Z (getr regs0 21) (w 48%Z (getr regs0 20) (w 40%Z (getr regs0 19) (w 32%Z (getr regs0 18)
      (w 24%Z (getr regs0 9) (w 16%Z (getr regs0 8) (w 8%Z ra mem))))))).

  Ltac len8 := rewrite ?length_N_to_le_bytes; change (Z.of_nat 8) with 8%Z.

  #[using="d c n H"] Lemma p7_below : forall x : word, (bv_unsigned x < usp - 64)%Z -> p8 x = mem x.
  Proof.
    intros x Hx. unfold p8. pose proof Hsp. rewrite !wbytes_below; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
  Qed.

  #[using="d c n H"] Lemma p7_out : forall x : word, (bv_unsigned x < usp - 64 \/ usp <= bv_unsigned x)%Z -> p8 x = mem x.
  Proof.
    intros x [Hx|Hx]; [apply p7_below; exact Hx|]. unfold p8. pose proof Hsp.
    rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
  Qed.

  #[using="d c n H"] Lemma rdn_p8_below : forall (a : Z) k, (0 <= a)%Z -> (a + Z.of_nat k <= usp - 64)%Z ->
    rdn SEGS p8 (Z_to_bv 64 a) k = rdn SEGS mem (Z_to_bv 64 a) k.
  Proof.
    intros a k Ha Hk. pose proof Hsp. apply rdn_ext; [rewrite zbv_u by lia; lia|].
    intros x Hx. rewrite zbv_u in Hx by lia. apply p7_below. lia.
  Qed.

  #[using="d c n H"] Lemma stk8p : forall m a, (usp - IM_FRAME <= a)%Z -> (a + 8 <= usp)%Z ->
    (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS m x 1 = true) ->
    store_ok SEGS m (Z_to_bv 64 a) 8 = true.
  Proof.
    intros m a H1 H2 Hm. unfold IM_FRAME in *. pose proof Hsp. apply store_ok8_bytes; [lia|lia|].
    intros j Hj. apply Hm. apply (im_stk _ _ _ _ _ H). unfold IM_FRAME. lia.
  Qed.

  Definition keep (regs : bvmap 5 word) : Prop :=
    forall r : reg, im_clob r = false -> r <> 1 -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 -> r <> 20 -> r <> 21 -> r <> 22 ->
      getr regs r = getr regs0 r.

  Ltac msd F D o v Hbase :=
    mstep ltac:(eapply (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (usp - o)) v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn; apply (f_equal (Z_to_bv 64)); lia
                 | gr; first [reflexivity | assumption | symmetry; assumption]
                 | apply stk8p; [unfold IM_FRAME; lia | lia | intros x Hx; repeat apply store_ok1_wbytes; exact Hx] ]).

  (* [comment removed for export] *)
  #[using="H H01 H02 H010 H011 H012"] Lemma blk_P :
    exists regs,
      msteps SEGS (mkst regs0 (0x53e18 : word) mem rom) (mkst regs (0x54528 : word) p8 rom)
      /\ getr regs 2 = Z_to_bv 64 (usp - 2144) /\ getr regs 8 = Z_to_bv 64 usp
      /\ getr regs 10 = Z_to_bv 64 d /\ getr regs 11 = Z_to_bv 64 c /\ getr regs 12 = Z_to_bv 64 n
      /\ getr regs 1 = ra /\ keep regs.
  Proof.
    pose proof Hsp.
    eexists. split.
    - mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_53e18 eq_refl D_53e18)).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_544fc eq_refl D_544fc)). rewrite H02. zn.
      msd F_54500 D_54500 8%Z ra H02.
      msd F_54504 D_54504 16%Z (getr regs0 8) H02.
      msd F_54508 D_54508 24%Z (getr regs0 9) H02.
      msd F_5450c D_5450c 32%Z (getr regs0 18) H02.
      msd F_54510 D_54510 40%Z (getr regs0 19) H02.
      msd F_54514 D_54514 48%Z (getr regs0 20) H02.
      msd F_54518 D_54518 56%Z (getr regs0 21) H02.
      msd F_5451c D_5451c 64%Z (getr regs0 22) H02.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54520 eq_refl D_54520)). gr. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54524 eq_refl D_54524)). gr. zn.
      apply mst_refl.
    - gr. repeat split; try (apply (f_equal (Z_to_bv 64)); lia); try assumption.
      intros r Hr N1 N2 N8 N9 N18 N19 N20 N21 N22. unfold im_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; try discriminate; congruence)). reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="d c n H"] Lemma cells_p8 : im_cells p8.
  Proof.
    pose proof (im_cel _ _ _ _ _ H) as C. pose proof Hsp. pose proof SB_val.
    unfold im_cells, cells, cell in *. rewrite !rdn_p8_below by (cbn; lia). exact C.
  Qed.

  Definition b_clob (r : reg) : bool := (bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 21)%bool.

  #[using="c H Hn Hd"] Lemma blk_B : forall regs,
    getr regs 8 = Z_to_bv 64 usp -> getr regs 10 = Z_to_bv 64 d -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x54528 : word) p8 rom) (mkst regs' (0x54550 : word) p8 rom)
      /\ getr regs' 13 = Z_to_bv 64 (n - 65) /\ getr regs' 14 = Z_to_bv 64 (2 ^ 64 - 65)
      /\ getr regs' 21 = Z_to_bv 64 (usp - 2136)
      /\ (forall r, b_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs H8 H10 H12. pose proof Hsp. pose proof SB_val as HSB.
    pose proof (im_dn _ _ _ _ _ H) as Hdn.
    pose proof cells_p8 as (CC & G1 & B1 & G2).
    eexists. split.
    - mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xaa528) F_54528 eq_refl D_54528);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_5452c D_5452c 0xb2899%Z G1 H8.
      mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_54530 eq_refl D_54530);
                   gr; imm_norm; zn; rewrite Z.add_0_r; exact B1).
      change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_54534 eq_refl D_54534); gr; rewrite ?getr_zero; br_eq).
      mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_54538 eq_refl D_54538)). gr. rewrite H10. rewrite v_not_zbv by lia.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5453c eq_refl D_5453c)). gr. rewrite H8. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54540 eq_refl D_54540)). gr. zn.
      mstep ltac:(eapply (step_bltu_ft _ _ _ _ _ _ _ _ _ F_54544 eq_refl D_54544); gr; rewrite ?H12; br_lt).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54548 eq_refl D_54548)). gr. rewrite H12. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5454c eq_refl D_5454c)). rewrite getr_zero. zn.
      apply mst_refl.
    - gr. repeat split.
      + rewrite <- (zbv_wrap_add (-65)). apply (f_equal (Z_to_bv 64)). lia.
      + apply (f_equal (Z_to_bv 64)). lia.
      + intros r Hr. unfold b_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="d c H Hn"] Lemma blk_Z : forall regs,
    n = 0%Z -> getr regs 13 = Z_to_bv 64 (n - 65) -> getr regs 14 = Z_to_bv 64 (2 ^ 64 - 65) ->
    getr regs 12 = Z_to_bv 64 n ->
    msteps SEGS (mkst regs (0x54550 : word) p8 rom) (mkst regs (0x54590 : word) p8 rom).
  Proof.
    intros regs Hn0 H13 H14 H12.
    replace (Z_to_bv 64 (n - 65)) with (Z_to_bv 64 (2 ^ 64 - 65 + n)) in H13
      by (rewrite <- (zbv_wrap_add (n - 65)); apply (f_equal (Z_to_bv 64)); lia).
    mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_54550 eq_refl D_54550); gr; rewrite ?H13, ?H14; br_lt).
    mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_546a0 eq_refl D_546a0); gr; rewrite ?H12, ?getr_zero; br_eq).
    mstep ltac:(exact (step_jal_x0 _ _ _ _ _ _ _ F_546a4 eq_refl D_546a4)).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition BS : list byte := repeat (Z_to_bv 8 c) (Z.to_nat n).

  #[using="mem usp H Hn Hd"] Lemma blk_M : forall regs m,
    cell m 0xab330 0xa2bec ->
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 c -> getr regs 12 = Z_to_bv 64 n ->
    store_ok SEGS m (Z_to_bv 64 d) (Z.to_nat n) = true ->
    exists regs',
      msteps SEGS (mkst regs (0x54590 : word) m rom)
                  (mkst regs' (0x5459c : word) (wbytes m (Z_to_bv 64 d) BS) rom)
      /\ getr regs' 10 = Z_to_bv 64 d
      /\ (forall r, im_clob r = false -> r <> 1 -> getr regs' r = getr regs r).
  Proof.
    intros regs m CM H10 H11 H12 Hok. pose proof Hn. pose proof Hd. pose proof (im_dn _ _ _ _ _ H).
    pose proof (im_c _ _ _ _ _ H) as Hc.
    evar (rr : bvmap 5 word).
    edestruct (BothMemset.memset_summary m (Z_to_bv 64 d) (Z_to_bv 64 c) (0x5459c : word) n rom) with (regs := rr)
      as (r1 & M1 & R10 & AG); cycle -1.
    { exists r1. split; [|split].
      - mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xab590) F_54590 eq_refl D_54590);
                     [reflexivity | apply bv_eq; vm_compute; reflexivity]).
        mld F_54594 D_54594 0xa2bec%Z CM H10.
        mstep ltac:(eapply (step_jalr_link _ _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa2bec) F_54598 eq_refl D_54598);
                     [reflexivity | gr; reflexivity]).
        rewrite ?lit_cccec.
        match goal with |- msteps _ (mkst ?r ?pc ?mm ?ro) _ =>
          replace pc with (Z_to_bv 64 BothMemset_code.ms_base) by (apply bv_eq; vm_compute; reflexivity) end.
        subst rr. unfold BS. unfold MemsetLib.cbyte in M1. rewrite (zbv_u c) in M1 by lia. exact M1.
      - exact R10.
      - intros r Hr Hr1.
        rewrite (MemsetLib.ms_agree_getr _ _ r AG)
          by (unfold MemsetLib.ms_clob; cbn [In]; intros X;
              repeat (destruct X as [X|X]; [subst r; cbn in Hr; discriminate|]); exact X).
        subst rr. gr. rewrite !getr_other by (intros ->; cbn in Hr; first [discriminate | congruence]). reflexivity. }
    all: subst rr; gr; try reflexivity; try assumption; try lia; try apply ret_ok_cccec.
    rewrite zbv_u by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac rd_side := len8; rewrite !zbv_u by lia; lia.
  Ltac rd_slot := pose proof Hsp; unfold p8;
    repeat (first [ apply rdn_wbytes_hit8; rewrite zbv_u by lia; lia
                  | rewrite rdn_wbytes_out; [| rd_side | rd_side | rd_side] ]).

  #[using="d c n H"] Lemma rd_ra : rdn SEGS p8 (Z_to_bv 64 (usp - 8)) 8 = Some (word_to_le_bytes 8 ra).             Proof. rd_slot. Qed.
  #[using="d c n H"] Lemma rd_s0 : rdn SEGS p8 (Z_to_bv 64 (usp - 16)) 8 = Some (word_to_le_bytes 8 (getr regs0 8)). Proof. rd_slot. Qed.
  #[using="d c n H"] Lemma rd_s1 : rdn SEGS p8 (Z_to_bv 64 (usp - 24)) 8 = Some (word_to_le_bytes 8 (getr regs0 9)). Proof. rd_slot. Qed.
  #[using="d c n H"] Lemma rd_s2 : rdn SEGS p8 (Z_to_bv 64 (usp - 32)) 8 = Some (word_to_le_bytes 8 (getr regs0 18)). Proof. rd_slot. Qed.
  #[using="d c n H"] Lemma rd_s3 : rdn SEGS p8 (Z_to_bv 64 (usp - 40)) 8 = Some (word_to_le_bytes 8 (getr regs0 19)). Proof. rd_slot. Qed.
  #[using="d c n H"] Lemma rd_s4 : rdn SEGS p8 (Z_to_bv 64 (usp - 48)) 8 = Some (word_to_le_bytes 8 (getr regs0 20)). Proof. rd_slot. Qed.
  #[using="d c n H"] Lemma rd_s5 : rdn SEGS p8 (Z_to_bv 64 (usp - 56)) 8 = Some (word_to_le_bytes 8 (getr regs0 21)). Proof. rd_slot. Qed.
  #[using="d c n H"] Lemma rd_s6 : rdn SEGS p8 (Z_to_bv 64 (usp - 64)) 8 = Some (word_to_le_bytes 8 (getr regs0 22)). Proof. rd_slot. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mld2 F D v Hrd Hbase :=
    mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ v F eq_refl D);
                 [ gr; rewrite ?Hbase; imm_norm; zn;
                   match goal with |- rdn _ _ (Z_to_bv 64 ?a) 8 = _ =>
                     match type of Hrd with rdn _ _ (Z_to_bv 64 ?c) 8 = _ =>
                       replace a with c by lia end end; exact Hrd
                 | apply bytes_le_to_Z_8 ]).

  Definition f_clob (r : reg) : bool :=
    (bv_eqb r 1 || bv_eqb r 2 || bv_eqb r 8 || bv_eqb r 9 || bv_eqb r 18 || bv_eqb r 19
     || bv_eqb r 20 || bv_eqb r 21 || bv_eqb r 22)%bool.

  #[using="d c n H Hret"] Lemma blk_E : forall regs mF,
    getr regs 2 = Z_to_bv 64 (usp - 2144) ->
    (forall a, (usp - 64 <= a)%Z -> (a + 8 <= usp)%Z -> rdn SEGS mF (Z_to_bv 64 a) 8 = rdn SEGS p8 (Z_to_bv 64 a) 8) ->
    exists regs',
      msteps SEGS (mkst regs (0x5459c : word) mF rom) (mkst regs' ra mF rom)
      /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ getr regs' 22 = getr regs0 22
      /\ (forall r, f_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs mF H2 HF. pose proof Hsp.
    pose proof rd_ra as RD1. pose proof rd_s0 as RD8. pose proof rd_s1 as RD9. pose proof rd_s2 as RD18.
    pose proof rd_s3 as RD19. pose proof rd_s4 as RD20. pose proof rd_s5 as RD21. pose proof rd_s6 as RD22.
    rewrite <- HF in RD22 by lia. rewrite <- HF in RD1 by lia. rewrite <- HF in RD8 by lia. rewrite <- HF in RD9 by lia. rewrite <- HF in RD18 by lia.
    rewrite <- HF in RD19 by lia. rewrite <- HF in RD20 by lia. rewrite <- HF in RD21 by lia.
    eexists. split.
    - mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5459c eq_refl D_5459c)). rewrite H2. zn.
      mld2 F_545a0 D_545a0 ra RD1 H2.
      mld2 F_545a4 D_545a4 (getr regs0 8) RD8 H2.
      mld2 F_545a8 D_545a8 (getr regs0 9) RD9 H2.
      mld2 F_545ac D_545ac (getr regs0 18) RD18 H2.
      mld2 F_545b0 D_545b0 (getr regs0 19) RD19 H2.
      mld2 F_545b4 D_545b4 (getr regs0 20) RD20 H2.
      mld2 F_545b8 D_545b8 (getr regs0 21) RD21 H2.
      mld2 F_545bc D_545bc (getr regs0 22) RD22 H2.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_545c0 eq_refl D_545c0)). gr. zn.
      replace (usp - 2144 + 112 + 2032)%Z with usp by lia.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ ra F_545c4 eq_refl D_545c4); gr; reflexivity |].
      imm_norm. rewrite Hret. apply mst_refl.
    - gr. repeat split; try reflexivity.
      intros r Hr. unfold f_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let g1 : Z := ((d + n - 1) / 8)%Z.

  (* [comment removed for export] *)
  Definition mL (regs : bvmap 5 word) : word -> option byte :=
    rp_frame p8 (usp - 2144) (0x546f0 : word) (getr regs 8) (Z_to_bv 64 d) (Z_to_bv 64 n)
             (getr regs 19) (getr regs 20) (getr regs 21).

  #[using="c H g1"] Lemma mL_out : forall regs (x : word),
    (bv_unsigned x < usp - 2216 \/ usp - 2144 <= bv_unsigned x)%Z -> mL regs x = p8 x.
  Proof.
    intros regs x Hx. pose proof Hsp. unfold mL, rp_frame.
    destruct Hx as [Hx|Hx].
    - rewrite !wbytes_below; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
    - rewrite !wbytes_above; try reflexivity; len8; rewrite ?zbv_u by lia; lia.
  Qed.

  #[using="c H Hn Hd"] Lemma rp_pre : forall b1,
    (65 <= n)%Z -> mem (Z_to_bv 64 (SB + g1)) = Some b1 ->
    (bv_unsigned b1 = 0%Z \/ ((d + n - 1) mod 8 < bv_unsigned b1 < 8)%Z) ->
    rpH p8 d n (usp - 2144) b1.
  Proof.
    intros b1 Hn65 L1 Hb1. pose proof Hsp. pose proof SB_val. pose proof (im_dn _ _ _ _ _ H).
    pose proof (im_shd _ _ _ _ _ H ltac:(lia)) as Hshd. unfold IM_FRAME in Hshd.
    pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)).
    constructor.
    - lia.
    - exact Hd.
    - apply (im_rng _ _ _ _ _ H). lia.
    - lia.
    - unfold g1 in *. lia.
    - intros g Hg. rewrite p7_below by (rewrite zbv_u by lia; lia). apply (im_zero _ _ _ _ _ H); lia.
    - rewrite p7_below by (rewrite zbv_u by lia; unfold g1 in *; lia). exact L1.
    - exact Hb1.
    - intros a Ha. unfold p8. repeat apply store_ok1_wbytes. apply (im_stk _ _ _ _ _ H). unfold IM_FRAME. lia.
    - exact (proj1 cells_p8).
  Qed.

  Definition l_clob (r : reg) : bool :=
    (im_clob r || bv_eqb r 1 || bv_eqb r 9 || bv_eqb r 18 || bv_eqb r 19 || bv_eqb r 22)%bool.

  #[using="H Hn Hd g1"] Lemma blk_L : forall regs,
    (65 <= n)%Z ->
    getr regs 13 = Z_to_bv 64 (n - 65) -> getr regs 14 = Z_to_bv 64 (2 ^ 64 - 65) ->
    getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 c -> getr regs 12 = Z_to_bv 64 n ->
    getr regs 2 = Z_to_bv 64 (usp - 2144) ->
    exists regs',
      msteps SEGS (mkst regs (0x54550 : word) p8 rom) (mkst regs' (0x54590 : word) (mL regs) rom)
      /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 11 = Z_to_bv 64 c /\ getr regs' 12 = Z_to_bv 64 n
      /\ getr regs' 2 = Z_to_bv 64 (usp - 2144)
      /\ (forall r, l_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs Hn65 H13 H14 H10 H11 H12 H2. pose proof Hsp. pose proof (im_c _ _ _ _ _ H) as Hc.
    pose proof (im_dn _ _ _ _ _ H).
    destruct (im_last _ _ _ _ _ H ltac:(lia)) as (b1 & L1 & Hb1).
    evar (rr : bvmap 5 word).
    edestruct (as_region_is_poisoned p8 rom d n (usp - 2144) b1 (rp_pre b1 Hn65 L1 Hb1) rr (0x546f0 : word) ret_ok_cce40)
      as (r1 & M1 & R10 & R2 & R1 & K1); cycle -1.
    { eexists. split; [|split; [|split; [|split; [|split]]]].
      - mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_54550 eq_refl D_54550); gr; rewrite ?H13, ?H14; br_lt).
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_546a0 eq_refl D_546a0); gr; rewrite ?H12, ?getr_zero; br_eq).
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_546dc eq_refl D_546dc)). gr. rewrite H10. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_546e0 eq_refl D_546e0)). gr. rewrite H11. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_546e4 eq_refl D_546e4)). gr. rewrite H12. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_546e8 eq_refl D_546e8)). gr. rewrite H12. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_546ec eq_refl D_546ec)). rewrite lit_cce40.
        eapply msteps_trans; [subst rr; exact M1|].
        match goal with |- msteps _ (mkst _ _ ?mm _) _ =>
          replace mm with (mL regs) by (unfold mL; subst rr; gr; reflexivity) end.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_546f0 eq_refl D_546f0)).
        rewrite (K1 22) by reflexivity. subst rr. gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_546f4 eq_refl D_546f4)). gr.
        rewrite (K1 18) by reflexivity. gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_546f8 eq_refl D_546f8)). gr. rewrite R10. zn.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_546fc eq_refl D_546fc)). gr.
        rewrite (K1 9) by reflexivity. gr. zn. rewrite ?Z.add_0_r.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_54700 eq_refl D_54700); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      - subst rr. gr. reflexivity.
      - subst rr. gr. reflexivity.
      - subst rr. gr. reflexivity.
      - subst rr. gr. exact R2.
      - subst rr. intros r Hr. unfold l_clob, im_clob in Hr.
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)).
        rewrite K1 by (unfold rp_clob; repeat match type of Hr with (?a || ?b)%bool = false =>
                         apply orb_false_iff in Hr; destruct Hr as [Hr ?] end;
                       repeat match goal with Hb : bv_eqb r ?k = false |- _ => rewrite Hb end; reflexivity).
        repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity. }
    all: subst rr; gr; try reflexivity; try assumption.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let g0 : Z := (d / 8)%Z.

  Definition q_clob (r : reg) : bool :=
    (bv_eqb r 13 || bv_eqb r 14 || bv_eqb r 15 || bv_eqb r 16 || bv_eqb r 17)%bool.

  #[using="mem c H Hd"] Lemma qfacts : (0 < n)%Z ->
    (8 * g0 <= d < 8 * g0 + 8)%Z /\ (8 * g1 <= d + n - 1 < 8 * g1 + 8)%Z
    /\ ((d + n - 1) mod 8 = d + n - 1 - 8 * g1)%Z
    /\ (SB + g1 + 8 < usp - 2216)%Z /\ (g0 <= g1)%Z /\ SB = 0x7fff8000%Z.
  Proof.
    intros Hn0. pose proof (im_shd _ _ _ _ _ H Hn0) as Hshd. unfold IM_FRAME in Hshd. pose proof SB_val.
    unfold g0, g1 in *.
    pose proof (Z.div_mod d 8 ltac:(lia)). pose proof (Z.mod_pos_bound d 8 ltac:(lia)).
    pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)).
    assert (d / 8 <= (d + n - 1) / 8)%Z by (apply Z.div_le_mono; lia).
    lia.
  Qed.

  (* [comment removed for export] *)
  #[using="c H Hn Hd"] Lemma blk_Q1 : forall regs,
    (1 <= n <= 64)%Z ->
    getr regs 13 = Z_to_bv 64 (n - 65) -> getr regs 14 = Z_to_bv 64 (2 ^ 64 - 65) ->
    getr regs 10 = Z_to_bv 64 d -> getr regs 12 = Z_to_bv 64 n ->
    exists regs' (w : word),
      msteps SEGS (mkst regs (0x54550 : word) p8 rom) (mkst regs' (0x5458c : word) p8 rom)
      /\ getr regs' 13 = Z_to_bv 64 (SB + g0) /\ getr regs' 14 = Z_to_bv 64 (SB + g1)
      /\ getr regs' 15 = Z_to_bv 64 (d + n - 1) /\ getr regs' 16 = w
      /\ (forall r, q_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs Hn64 H13 H14 H10 H12. pose proof Hsp as HU. pose proof (im_dn _ _ _ _ _ H) as Hdn.
    destruct (qfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB).
    pose proof cells_p8 as ((C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8) & G1 & B1 & G2).
    destruct (im_w1 _ _ _ _ _ H ltac:(lia)) as [w1 W1]. destruct (im_w2 _ _ _ _ _ H ltac:(lia)) as [w2 W2].
    pose proof (Z.div_mod (SB + g0) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + g0) 8 ltac:(lia)).
    pose proof (Z.div_mod (SB + g1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SB + g1) 8 ltac:(lia)).
    assert (W1c : cell p8 ((SB + g0) / 8 * 8) (bv_unsigned w1)).
    { unfold cell. rewrite zbv_self. rewrite rdn_p8_below by (cbn; (ltac2:(LK.k [@Hd; @Hn64; @D0; @D1; @HSB; @H0; @H1; @Dshd]); lia)). exact W1. }
    assert (W2c : cell p8 ((SB + g1) / 8 * 8) (bv_unsigned w2)).
    { unfold cell. rewrite zbv_self. rewrite rdn_p8_below by (cbn; (ltac2:(LK.k [@Hd; @Hn64; @D0; @D1; @HSB; @H2; @H3; @Dshd]); lia)). exact W2. }
    replace (Z_to_bv 64 (n - 65)) with (Z_to_bv 64 (2 ^ 64 - 65 + n)) in H13
      by (rewrite <- (zbv_wrap_add (n - 65)); apply (f_equal (Z_to_bv 64)); lia).
    eexists. eexists. split.
    - mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_54550 eq_refl D_54550); gr; rewrite ?H13, ?H14; br_lt).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xa9554) F_54554 eq_refl D_54554);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mld F_54558 D_54558 0xb1bb8%Z C1 H10.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_5455c eq_refl D_5455c)). gr. rewrite H10, H12, v_add_zbv by (ltac2:(LK.k [@Hd; @Hn64; @Hdn; @D0; @D1; @HSB; @Hn]); lia).
      mld F_54560 D_54560 SB C2 H10.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_54564 eq_refl D_54564)). gr. rewrite H10, (v_srli_3 d) by (ltac2:(LK.k [@Hd; @Hn64; @Hdn; @D0; @D1; @HSB]); lia).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_54568 eq_refl D_54568)). gr. zn.
      replace (d + n + -1)%Z with (d + n - 1)%Z by lia.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_5456c eq_refl D_5456c)). gr. rewrite (v_srli_3 (d + n - 1)) by (ltac2:(LK.k [@Hd; @Hn64; @Hdn; @D0; @D1; @DM; @HSB]); lia).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_54570 eq_refl D_54570)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@Hd; @HSB; @Hn64; @Hdn; @D0]); lia).
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_54574 eq_refl D_54574)). gr. rewrite v_add_zbv by (ltac2:(LK.k [@Hd; @HSB; @Hn64; @Hdn; @D0; @D1; @DM]); lia).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_54578 eq_refl D_54578)). gr. rewrite v_andi_m8 by (ltac2:(LK.k [@Hd; @Hn64; @Hdn; @D0; @D1; @HSB]); lia).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_5457c eq_refl D_5457c)). gr. rewrite v_andi_m8 by (ltac2:(LK.k [@Hd; @Hn64; @Hdn; @D0; @D1; @DM; @HSB]); lia).
      fold g0. fold g1.
      mld F_54580 D_54580 (bv_unsigned w1) W1c H10.
      mld F_54584 D_54584 (bv_unsigned w2) W2c H10.
      mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_54588 eq_refl D_54588)). gr.
      apply mst_refl.
    - gr. repeat split; try reflexivity.
      intros r Hr. unfold q_clob in Hr.
      repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma v_lit_eq : forall a b : Z, a = b -> Z_to_bv 64 a = Z_to_bv 64 b.
  Proof. intros a b ->. reflexivity. Qed.

  #[using="c H Hd g0"] Lemma blk_Q2a : forall regs,
    (1 <= n <= 64)%Z ->
    getr regs 14 = Z_to_bv 64 (SB + g1) -> getr regs 15 = Z_to_bv 64 (d + n - 1) ->
    exists regs',
      msteps SEGS (mkst regs (0x546a8 : word) p8 rom) (mkst regs' (0x546c0 : word) p8 rom)
      /\ getr regs' 15 = Z_to_bv 64 0
      /\ (forall r, q_clob r = false -> getr regs' r = getr regs r)
      /\ getr regs' 13 = getr regs 13 /\ getr regs' 14 = getr regs 14.
  Proof.
    intros regs Hn64 H14 H15. pose proof Hsp as HU. pose proof (im_dn _ _ _ _ _ H) as Hdn.
    destruct (qfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB).
    destruct (im_last _ _ _ _ _ H ltac:(lia)) as (b1 & L1 & Hb1). pose proof (bv_unsigned_in_range 8 b1) as Hb1r.
    assert (L1' : rdn SEGS p8 (Z_to_bv 64 (SB + g1)) 1 = Some [b1]).
    { apply rdn1. rewrite p7_below by (rewrite zbv_u by lia; lia). exact L1. }
    assert (Hsg : bv_signed b1 = bv_unsigned b1) by (apply bv_signed_small8; lia).
    assert (AND0 : v_and (Z_to_bv 64 0) (v_xori (Z_to_bv 64 0) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    assert (AND1 : v_and (Z_to_bv 64 1) (v_xori (Z_to_bv 64 1) 1) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    destruct Hb1 as [Hz | Hpart].
    - eexists. split; [|split; [|split; [|split]]].
      + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_546a8 eq_refl D_546a8);
                     gr; rewrite ?H14; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
        unfold v_lb. rewrite Hsg, Hz.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_546ac eq_refl D_546ac)). gr. rewrite H15, v_andi_7 by lia.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_546b0 eq_refl D_546b0)). gr. rewrite getr_zero.
        unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_ge 0 0)) by lia.
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_546b4 eq_refl D_546b4)). gr.
        unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_ge _ 0)) by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_546b8 eq_refl D_546b8)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_546bc eq_refl D_546bc)). gr. rewrite AND0.
        apply mst_refl.
      + gr. reflexivity.
      + intros r Hr. unfold q_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
      + gr. reflexivity.
      + gr. reflexivity.
    - eexists. split; [|split; [|split; [|split]]].
      + mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ b1 F_546a8 eq_refl D_546a8);
                     gr; rewrite ?H14; imm_norm; zn; rewrite ?Z.add_0_r; exact L1').
        unfold v_lb. rewrite Hsg. rewrite <- (zbv_self (Z_to_bv 64 (bv_unsigned b1))). rewrite (zbv_u (bv_unsigned b1)) by lia.
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_546ac eq_refl D_546ac)). gr. rewrite H15, v_andi_7 by lia.
        mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_546b0 eq_refl D_546b0)). gr. rewrite getr_zero.
        unfold v_sltu. rewrite c_ltu_zbv by lia. rewrite (proj2 (Z.ltb_lt 0 _)) by lia.
        mstep ltac:(exact (step_slt _ _ _ _ _ _ _ _ _ F_546b4 eq_refl D_546b4)). gr.
        unfold v_slt. rewrite c_lts_zbv by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
        mstep ltac:(exact (step_xori _ _ _ _ _ _ _ _ _ F_546b8 eq_refl D_546b8)). gr.
        mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_546bc eq_refl D_546bc)). gr. rewrite AND1.
        apply mst_refl.
      + gr. reflexivity.
      + intros r Hr. unfold q_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
      + gr. reflexivity.
      + gr. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="c H Hd"] Lemma q_loop : forall (i : nat) regs g,
    (1 <= n <= 64)%Z ->
    getr regs 13 = Z_to_bv 64 (SB + g) -> getr regs 14 = Z_to_bv 64 (SB + g1) -> getr regs 15 = Z_to_bv 64 0 ->
    (g0 <= g < g1)%Z -> Z.of_nat i = (g1 - g)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x546c4 : word) p8 rom) (mkst regs' (0x546d4 : word) p8 rom)
      /\ getr regs' 15 = Z_to_bv 64 0
      /\ (forall r, q_clob r = false -> getr regs' r = getr regs r).
  Proof.
    pose proof Hsp as HU. pose proof (im_dn _ _ _ _ _ H) as Hdn.
    induction i as [|i IH]; intros regs g Hn64 H13 H14 H15 Hg Hi; [lia|].
    destruct (qfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB).
    assert (Z0 : rdn SEGS p8 (Z_to_bv 64 (SB + g)) 1 = Some [Z_to_bv 8 0]).
    { apply rdn1. rewrite p7_below by (rewrite zbv_u by lia; lia). apply (im_zero _ _ _ _ _ H); unfold g0, g1 in *; lia. }
    destruct (Z.eq_dec (g + 1) g1) as [Heq | Hne].
    - eexists. split; [|split].
      + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_546c4 eq_refl D_546c4);
                     gr; rewrite ?H13; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
        change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_546c8 eq_refl D_546c8)). gr. rewrite H13. zn.
        mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_546cc eq_refl D_546cc)). gr. rewrite H15, v_or_zero.
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_546d0 eq_refl D_546d0); gr; rewrite ?H14; br_eq).
        apply mst_refl.
      + gr. reflexivity.
      + intros r Hr. unfold q_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    - evar (rr : bvmap 5 word).
      edestruct (IH rr (g + 1)%Z Hn64) as (r2 & M2 & R15 & K2); cycle -1.
      { exists r2. split; [|split].
        + mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 0) F_546c4 eq_refl D_546c4);
                       gr; rewrite ?H13; imm_norm; zn; rewrite ?Z.add_0_r; exact Z0).
          change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_546c8 eq_refl D_546c8)). gr. rewrite H13. zn.
          mstep ltac:(exact (step_or _ _ _ _ _ _ _ _ _ F_546cc eq_refl D_546cc)). gr. rewrite H15, v_or_zero.
          mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_546d0 eq_refl D_546d0); gr; rewrite ?H14; br_eq).
          subst rr. exact M2.
        + exact R15.
        + intros r Hr. rewrite (K2 r Hr). subst rr. unfold q_clob in Hr.
          repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity. }
      all: subst rr; gr; try reflexivity; try assumption; try lia.
      apply (f_equal (Z_to_bv 64)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="c H Hd"] Lemma blk_Q2b : forall regs,
    (1 <= n <= 64)%Z ->
    getr regs 13 = Z_to_bv 64 (SB + g0) -> getr regs 14 = Z_to_bv 64 (SB + g1) -> getr regs 15 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x546c0 : word) p8 rom) (mkst regs' (0x54590 : word) p8 rom)
      /\ (forall r, q_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs Hn64 H13 H14 H15. pose proof Hsp as HU. pose proof (im_dn _ _ _ _ _ H) as Hdn.
    destruct (qfacts ltac:(lia)) as (D0 & D1 & DM & Dshd & D01 & HSB).
    assert (ANDI0 : v_andi (Z_to_bv 64 0) 255 = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    destruct (Z.eq_dec g0 g1) as [Heq | Hne].
    - eexists. split.
      + mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_546c0 eq_refl D_546c0); gr; rewrite ?H13, ?H14; br_lt).
        mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_546d4 eq_refl D_546d4)). gr. rewrite H15, ANDI0.
        mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_546d8 eq_refl D_546d8); gr; rewrite ?getr_zero; br_eq).
        apply mst_refl.
      + intros r Hr. unfold q_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)). reflexivity.
    - evar (rr : bvmap 5 word).
      edestruct (q_loop (Z.to_nat (g1 - g0)) rr g0 Hn64) as (r2 & M2 & R15 & K2); cycle -1.
      { eexists. split.
        + mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_546c0 eq_refl D_546c0); gr; rewrite ?H13, ?H14; br_lt).
          eapply msteps_trans; [subst rr; exact M2|].
          mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_546d4 eq_refl D_546d4)). rewrite R15, ANDI0.
          mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_546d8 eq_refl D_546d8); gr; rewrite ?getr_zero; br_eq).
          apply mst_refl.
        + intros r Hr. unfold q_clob in Hr. repeat (rewrite getr_other by (intros ->; cbn in Hr; discriminate)).
          rewrite (K2 r) by exact Hr. subst rr. reflexivity. }
      all: subst rr; try assumption; try lia.
  Qed.

  (* [comment removed for export] *)
  #[using="c H Hn Hd g1 g0"] Lemma blk_Q : forall regs,
    (1 <= n <= 64)%Z ->
    getr regs 13 = Z_to_bv 64 (n - 65) -> getr regs 14 = Z_to_bv 64 (2 ^ 64 - 65) ->
    getr regs 10 = Z_to_bv 64 d -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x54550 : word) p8 rom) (mkst regs' (0x54590 : word) p8 rom)
      /\ (forall r, q_clob r = false -> getr regs' r = getr regs r).
  Proof.
    intros regs Hn64 H13 H14 H10 H12.
    destruct (blk_Q1 regs Hn64 H13 H14 H10 H12) as (q1 & w & M1 & A13 & A14 & A15 & A16 & K1).
    pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64)%Z in Hw.
    destruct (bv_eq_dec _ w (Z_to_bv 64 0)) as [-> | NZ].
    - exists q1. split.
      + eapply msteps_trans; [exact M1|].
        mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_5458c eq_refl D_5458c); gr; rewrite ?A16, ?getr_zero; br_eq).
        apply mst_refl.
      + exact K1.
    - assert (NZu : bv_unsigned w <> 0%Z).
      { intros E. apply NZ. rewrite <- (zbv_self w), E. reflexivity. }
      destruct (blk_Q2a q1 Hn64 A14 A15) as (q2 & M2 & B15 & K2 & B13 & B14).
      destruct (blk_Q2b q2 Hn64) as (q3 & M3 & K3); [rewrite B13; exact A13 | rewrite B14; exact A14 | exact B15 |].
      exists q3. split.
      + eapply msteps_trans; [exact M1|].
        mstep ltac:(eapply (step_bne_tk _ _ _ _ _ _ _ _ _ F_5458c eq_refl D_5458c); gr; rewrite ?A16, ?getr_zero;
                     rewrite <- (zbv_self w); br_eq).
        eapply msteps_trans; [exact M2|]. exact M3.
      + intros r Hr. rewrite (K3 r Hr), (K2 r Hr). apply K1. exact Hr.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="H Hret Hn Hd g1 g0"] Lemma finish : forall q mX,
    (forall x : word, (bv_unsigned x < usp - 2216 \/ usp - 2144 <= bv_unsigned x)%Z -> mX x = p8 x) ->
    (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS mX x 1 = true) ->
    (forall x, mem x <> None -> mX x <> None) ->
    getr q 10 = Z_to_bv 64 d -> getr q 11 = Z_to_bv 64 c -> getr q 12 = Z_to_bv 64 n ->
    getr q 2 = Z_to_bv 64 (usp - 2144) ->
    exists regs' m',
      msteps SEGS (mkst q (0x54590 : word) mX rom) (mkst regs' ra m' rom)
      /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ getr regs' 8 = getr regs0 8 /\ getr regs' 9 = getr regs0 9 /\ getr regs' 18 = getr regs0 18
      /\ getr regs' 19 = getr regs0 19 /\ getr regs' 20 = getr regs0 20 /\ getr regs' 21 = getr regs0 21
      /\ getr regs' 22 = getr regs0 22
      /\ (forall r, im_clob r = false -> f_clob r = false -> getr regs' r = getr q r)
      /\ (forall x : word, (bv_unsigned x < usp - IM_FRAME \/ usp <= bv_unsigned x)%Z ->
            m' x = wbytes mem (Z_to_bv 64 d) BS x)
      /\ (forall x, mem x <> None -> m' x <> None).
  Proof.
    intros q mX MX MOK MG Q10 Q11 Q12 Q2. pose proof Hsp as HU. pose proof (im_dn _ _ _ _ _ H) as Hdn.
    pose proof (im_dst _ _ _ _ _ H) as Hdst. unfold IM_FRAME in Hdst.
    assert (LBS : Z.of_nat (length BS) = n) by (unfold BS; rewrite repeat_length; lia).
    assert (CM : cell mX 0xab330 0xa2bec).
    { pose proof cells_p8 as (_ & _ & _ & G2). unfold cell in *. rewrite <- G2.
      apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|].
      intros x Hx. rewrite zbv_u in Hx by lia. cbn in Hx. apply MX. lia. }
    assert (DOK : store_ok SEGS mX (Z_to_bv 64 d) (Z.to_nat n) = true).
    { apply store_ok_bytes; [lia | rewrite Z2Nat.id by lia; lia |]. intros j Hj. rewrite Z2Nat.id in Hj by lia.
      apply MOK. apply (im_dok _ _ _ _ _ H). lia. }
    destruct (blk_M q mX CM Q10 Q11 Q12 DOK) as (q5 & M5 & R10 & K5).
    destruct (blk_E q5 (wbytes mX (Z_to_bv 64 d) BS)) as (q6 & M6 & F2 & F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & FK).
    { rewrite (K5 2) by (reflexivity || (intros E; discriminate E)). exact Q2. }
    { intros a Ha1 Ha2.
      assert (RX : rdn SEGS mX (Z_to_bv 64 a) 8 = rdn SEGS p8 (Z_to_bv 64 a) 8).
      { apply rdn_ext; [rewrite zbv_u by lia; cbn; lia|]. intros x Hx. rewrite zbv_u in Hx by lia. cbn in Hx. apply MX. lia. }
      destruct (Z.eq_dec n 0) as [N0|N0].
      { unfold BS. rewrite N0. cbn [Z.to_nat repeat wbytes]. exact RX. }
      rewrite rdn_wbytes_out; [exact RX | rewrite !zbv_u by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                             | rewrite zbv_u by lia; cbn; lia | rewrite zbv_u by lia; lia ]. }
    exists q6, (wbytes mX (Z_to_bv 64 d) BS).
    split; [eapply msteps_trans; [exact M5 | exact M6] |].
    split; [rewrite (FK 10) by reflexivity; exact R10 |].
    split; [exact F2|]. split; [exact F1|]. split; [exact F8|]. split; [exact F9|]. split; [exact F18|].
    split; [exact F19|]. split; [exact F20|]. split; [exact F21|]. split; [exact F22|].
    split; [|split].
    - intros r Hr Hf. rewrite (FK r Hf). apply K5; [exact Hr|]. intros ->. cbn in Hf. discriminate.
    - intros x Hx. unfold IM_FRAME in Hx. apply wbytes_agree. rewrite MX by lia. apply p7_out. lia.
    - intros x Hx. apply wbytes_keep. apply MG. exact Hx.
  Qed.

  Ltac clob_false Hr N1 N2 N8 N9 N18 N19 N20 N21 N22 :=
    unfold f_clob, l_clob, q_clob, b_clob, im_clob; unfold im_clob in Hr;
    rewrite ?(bv_eqb_neq _ _ N1), ?(bv_eqb_neq _ _ N2), ?(bv_eqb_neq _ _ N8), ?(bv_eqb_neq _ _ N9),
            ?(bv_eqb_neq _ _ N18), ?(bv_eqb_neq _ _ N19), ?(bv_eqb_neq _ _ N20), ?(bv_eqb_neq _ _ N21), ?(bv_eqb_neq _ _ N22);
    repeat match type of Hr with (?a || ?b)%bool = false => apply orb_false_iff in Hr; destruct Hr as [Hr ?] end;
    repeat match goal with Hb : bv_eqb _ _ = false |- _ => rewrite Hb end; reflexivity.

  #[using="H Hret H01 H02 H010 H011 H012 Hn Hd g1 g0"] Theorem ic_memset_IM :
    exists regs' m',
      msteps SEGS (mkst regs0 (0x53e18 : word) mem rom) (mkst regs' ra m' rom)
      /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
      /\ (forall r, im_clob r = false -> getr regs' r = getr regs0 r)
      /\ (forall x : word, (bv_unsigned x < usp - IM_FRAME \/ usp <= bv_unsigned x)%Z ->
            m' x = wbytes mem (Z_to_bv 64 d) BS x)
      /\ (forall x, mem x <> None -> m' x <> None).
  Proof.
    pose proof Hsp as HU.
    destruct blk_P as (q1 & MP & P2 & P8 & P10 & P11 & P12 & P1 & PK).
    destruct (blk_B q1 P8 P10 P12) as (q2 & MB & B13 & B14 & B20 & BK).
    assert (B10 : getr q2 10 = Z_to_bv 64 d) by (rewrite BK by reflexivity; exact P10).
    assert (B11 : getr q2 11 = Z_to_bv 64 c) by (rewrite BK by reflexivity; exact P11).
    assert (B12 : getr q2 12 = Z_to_bv 64 n) by (rewrite BK by reflexivity; exact P12).
    assert (B2 : getr q2 2 = Z_to_bv 64 (usp - 2144)) by (rewrite BK by reflexivity; exact P2).
    assert (P8OK : forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS p8 x 1 = true).
    { intros x Hx. unfold p8. repeat apply store_ok1_wbytes. exact Hx. }
    assert (P8G : forall x, mem x <> None -> p8 x <> None).
    { intros x Hx. unfold p8. repeat apply wbytes_keep. exact Hx. }
    (* [comment removed for export] *)
    assert (ASM : forall q3 mX (kc : reg -> bool),
      msteps SEGS (mkst q2 (0x54550 : word) p8 rom) (mkst q3 (0x54590 : word) mX rom) ->
      (forall r, kc r = false -> getr q3 r = getr q2 r) ->
      (forall r : reg, im_clob r = false -> r <> 1 -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 -> r <> 20 -> r <> 21 -> r <> 22 ->
         kc r = false) ->
      (forall x : word, (bv_unsigned x < usp - 2216 \/ usp - 2144 <= bv_unsigned x)%Z -> mX x = p8 x) ->
      (forall x, store_ok SEGS mem x 1 = true -> store_ok SEGS mX x 1 = true) ->
      (forall x, mem x <> None -> mX x <> None) ->
      getr q3 10 = Z_to_bv 64 d -> getr q3 11 = Z_to_bv 64 c -> getr q3 12 = Z_to_bv 64 n ->
      getr q3 2 = Z_to_bv 64 (usp - 2144) ->
      exists regs' m',
        msteps SEGS (mkst regs0 (0x53e18 : word) mem rom) (mkst regs' ra m' rom)
        /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
        /\ (forall r, im_clob r = false -> getr regs' r = getr regs0 r)
        /\ (forall x : word, (bv_unsigned x < usp - IM_FRAME \/ usp <= bv_unsigned x)%Z ->
              m' x = wbytes mem (Z_to_bv 64 d) BS x)
        /\ (forall x, mem x <> None -> m' x <> None)).
    { intros q3 mX kc M3 K3 KC MX MOK MG Q10 Q11 Q12 Q2.
      destruct (finish q3 mX MX MOK MG Q10 Q11 Q12 Q2) as (q6 & m' & MF & F10 & F2 & F1 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & FK & ME & MGr).
      exists q6, m'. split; [|split; [exact F10|split; [exact F2|split; [exact F1|split; [|split; [exact ME|exact MGr]]]]]].
      - eapply msteps_trans; [exact MP|]. eapply msteps_trans; [exact MB|]. eapply msteps_trans; [exact M3|]. exact MF.
      - intros r Hr.
        destruct (bv_eq_dec _ r 1) as [-> | N1]; [rewrite F1; symmetry; exact H01|].
        destruct (bv_eq_dec _ r 2) as [-> | N2]; [rewrite F2; symmetry; exact H02|].
        destruct (bv_eq_dec _ r 8) as [-> | N8]; [exact F8|].
        destruct (bv_eq_dec _ r 9) as [-> | N9]; [exact F9|].
        destruct (bv_eq_dec _ r 18) as [-> | N18]; [exact F18|].
        destruct (bv_eq_dec _ r 19) as [-> | N19]; [exact F19|].
        destruct (bv_eq_dec _ r 20) as [-> | N20]; [exact F20|].
        destruct (bv_eq_dec _ r 21) as [-> | N21]; [exact F21|].
        destruct (bv_eq_dec _ r 22) as [-> | N22]; [exact F22|].
        rewrite (FK r Hr) by (unfold f_clob; rewrite (bv_eqb_neq _ _ N1), (bv_eqb_neq _ _ N2), (bv_eqb_neq _ _ N8),
                                (bv_eqb_neq _ _ N9), (bv_eqb_neq _ _ N18), (bv_eqb_neq _ _ N19), (bv_eqb_neq _ _ N20),
                                (bv_eqb_neq _ _ N21), (bv_eqb_neq _ _ N22); reflexivity).
        rewrite (K3 r) by (apply KC; assumption).
        assert (Hr' := Hr). unfold im_clob in Hr'.
        repeat match type of Hr' with (?a || ?b)%bool = false => apply orb_false_iff in Hr'; destruct Hr' as [Hr' ?] end.
        rewrite (BK r) by (unfold b_clob; rewrite (bv_eqb_neq _ _ N21);
                           repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb end; reflexivity).
        apply PK; assumption. }
    destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
    - (* [comment removed for export] *)
      apply (ASM q2 p8 (fun _ => false)).
      + apply blk_Z; assumption.
      + intros; reflexivity.
      + intros; reflexivity.
      + intros; reflexivity.
      + exact P8OK.
      + exact P8G.
      + exact B10.
      + exact B11.
      + exact B12.
      + exact B2.
    - destruct (Z.lt_ge_cases n 65) as [Hsmall | Hbig].
      + (* [comment removed for export] *)
        destruct (blk_Q q2 ltac:(lia) B13 B14 B10 B12) as (q3 & M3 & K3).
        apply (ASM q3 p8 q_clob M3 K3).
        * intros r Hr N1 N2 N8 N9 N18 N19 N20 N21 N22. assert (Hr' := Hr). unfold im_clob in Hr'.
          repeat match type of Hr' with (?a || ?b)%bool = false => apply orb_false_iff in Hr'; destruct Hr' as [Hr' ?] end.
          unfold q_clob. repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb end. reflexivity.
        * intros; reflexivity.
        * exact P8OK.
        * exact P8G.
        * rewrite K3 by reflexivity. exact B10.
        * rewrite K3 by reflexivity. exact B11.
        * rewrite K3 by reflexivity. exact B12.
        * rewrite K3 by reflexivity. exact B2.
      + (* [comment removed for export] *)
        destruct (blk_L q2 Hbig B13 B14 B10 B11 B12 B2) as (q3 & M3 & L10 & L11 & L12 & L2 & K3).
        apply (ASM q3 (mL q2) l_clob M3 K3).
        * intros r Hr N1 N2 N8 N9 N18 N19 N20 N21 N22. assert (Hr' := Hr). unfold im_clob in Hr'.
          repeat match type of Hr' with (?a || ?b)%bool = false => apply orb_false_iff in Hr'; destruct Hr' as [Hr' ?] end.
          unfold l_clob, im_clob. rewrite (bv_eqb_neq _ _ N1), (bv_eqb_neq _ _ N9), (bv_eqb_neq _ _ N18),
                                        (bv_eqb_neq _ _ N19), (bv_eqb_neq _ _ N22).
          repeat match goal with Hb : bv_eqb r _ = false |- _ => rewrite Hb end. reflexivity.
        * apply mL_out.
        * intros x Hx. unfold mL, rp_frame. repeat apply store_ok1_wbytes. first [exact Hx | apply P8OK; exact Hx].
        * intros x Hx. unfold mL, rp_frame. repeat apply wbytes_keep. first [exact Hx | apply P8G; exact Hx].
        * exact L10.
        * exact L11.
        * exact L12.
        * exact L2.
  Qed.
End IM.

(* [comment removed for export] *)
Theorem ic_memset_run :
  forall (mem rom : word -> option byte) (d c n usp : Z),
  imH mem d c n usp ->
  forall regs (ra : word),
  ret_ok ra -> getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 usp ->
  getr regs 10 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 c -> getr regs 12 = Z_to_bv 64 n ->
  exists regs' m',
    msteps SEGS (mkst regs (0x53e18 : word) mem rom) (mkst regs' ra m' rom)
    /\ getr regs' 10 = Z_to_bv 64 d /\ getr regs' 2 = Z_to_bv 64 usp /\ getr regs' 1 = ra
    /\ (forall r, im_clob r = false -> getr regs' r = getr regs r)
    /\ (forall x : word, (bv_unsigned x < usp - IM_FRAME \/ usp <= bv_unsigned x)%Z ->
          m' x = wbytes mem (Z_to_bv 64 d) (repeat (Z_to_bv 8 c) (Z.to_nat n)) x)
    /\ (forall x, mem x <> None -> m' x <> None).
Proof.
  intros mem rom d c n usp H regs ra Hret H1 H2 H10 H11 H12.
  exact (ic_memset_IM mem rom d c n usp H regs ra Hret H1 H2 H10 H11 H12).
Qed.
