(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ListFacts PropExec CatExec CatSim SeqExec StreamExec StreamSim MmapSim StepTac Hoare WalkTac StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib AgentLib MallocDefs.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefEnframeArith.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbEnframeBase UbEnframe_run1 UbEnframe_run2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Enframe.
  Variables (mem0 : word -> option byte) (c : word) (g M W idx n h3 o16 stride start off : Z).
  Hypothesis H : efH mem0 c g M W idx n h3 o16 stride start off.

  Ltac facts :=
    pose proof (stride_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (Sge & Smod & S31);
    pose proof (off_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (O1 & O2 & O3 & O4);
    pose proof (start_facts _ _ _ _ _ _ _ _ _ _ _ _ H) as (T1 & T2 & T3 & T4 & T5);
    pose proof (Hidx _ _ _ _ _ _ _ _ _ _ _ _ H) as Gidx;
    pose proof (Hn _ _ _ _ _ _ _ _ _ _ _ _ H) as Gn.

  Local Notation PP := (start + 16 * off).
  Local Notation EE := (start + stride - 4).
  Local Notation RR := (stride - 4 - n - 16 * off).
  Local Notation QQ := (stride * idx / 16 + off).

  (* [comment removed for export] *)
  Definition memF : memT :=
    mF idx n stride start off (mE idx n stride start off (mD start off mem0)).

  Definition RGN : list (word * Z) := [(Z_to_bv 64 (start - 3), stride - 1)].

  Ltac sidez :=
    rewrite ?length_wle2, ?length_wle4; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
    rewrite ?u64_lit by lia; lia.
  Ltac peel := rewrite rdn_wbytes_out; [ | sidez | sidez | sidez ].
  Ltac miss := rewrite wbytes_miss; [ | sidez | sidez ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma fm_layer : forall m a bs,
    start - 3 <= a -> a + Z.of_nat (length bs) <= start + stride - 4 ->
    frame_mod m (wbytes m (Z_to_bv 64 a) bs) RGN.
  Proof.
    intros m a bs Ha Hb. facts.
    eapply frame_mod_weaken; [| apply frame_mod_wbytes; rewrite u64_lit by lia; lia].
    intros x [Hx _]. split; [|exact I]. intros Hin. apply Hx.
    unfold in_rng in *. rewrite !u64_lit in * by lia. lia.
  Qed.

  Lemma fm_step : forall m m' a bs,
    frame_mod mem0 m RGN ->
    m' = wbytes m (Z_to_bv 64 a) bs ->
    start - 3 <= a -> a + Z.of_nat (length bs) <= start + stride - 4 ->
    frame_mod mem0 m' RGN.
  Proof.
    intros m m' a bs Hm -> Ha Hb. eapply frame_mod_trans_same; [exact Hm | apply fm_layer; assumption].
  Qed.

  Lemma frame_memF : frame_mod mem0 memF RGN.
  Proof.
    facts. unfold memF.
    assert (FD : frame_mod mem0 (mD start off mem0) RGN).
    { cbv delta [mD] beta. destruct (Z.eqb_spec off 0) as [Hz|Hz]; [apply frame_mod_refl|].
      eapply fm_step; [| reflexivity | lia | cbn [length]; lia].
      eapply fm_step; [| reflexivity | lia | rewrite length_wle2; cbn; lia].
      eapply fm_step; [apply frame_mod_refl | reflexivity | lia | cbn [length]; lia]. }
    set (m1 := mD start off mem0) in *. clearbody m1.
    assert (FE1 : frame_mod mem0 (mE1 idx stride start off m1) RGN).
    { cbv delta [mE1] beta.
      eapply fm_step; [| reflexivity | lia | rewrite length_wle2; cbn; lia].
      eapply fm_step; [exact FD | reflexivity | lia | cbn [length]; lia]. }
    assert (FE : frame_mod mem0 (mE idx n stride start off m1) RGN).
    { cbv delta [mE] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [exact FE1|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5].
      - eapply fm_step; [exact FE1 | reflexivity | lia | cbn [length]; lia].
      - eapply fm_step; [| reflexivity | lia | rewrite length_wle4; cbn; lia].
        eapply fm_step; [| reflexivity | lia | cbn [length]; lia].
        eapply fm_step; [exact FE1 | reflexivity | lia | cbn [length]; lia]. }
    cbv delta [mF] beta.
    eapply fm_step; [exact FE | reflexivity | lia | cbn [length]; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma post_memF : enframe_post memF idx n stride start off.
  Proof.
    facts. pose proof (qq_range _ _ _ _ _ _ _ _ _ _ _ _ H) as Qr.
    pose proof (R4 _ _ _ _ _ _ _ _ _ _ _ _ H) as L4.
    assert (Hrc : 0 <= res_code RR <= 5)
      by (unfold res_code; destruct (Z.ltb_spec RR 5); lia).
    unfold memF. set (m1 := mD start off mem0).
    (* [comment removed for export] *)
    assert (M4 : m1 (Z_to_bv 64 (PP - 4)) = Some (Z_to_bv 8 0)).
    { subst m1. cbv delta [mD] beta. destruct (Z.eqb_spec off 0) as [Hz|Hz].
      - rewrite <- L4. f_equal. f_equal. lia.
      - replace (PP - 4) with (start + 16 * off - 4) by lia. apply wbytes_hit1. }
    assert (M3 : off <> 0 -> m1 (Z_to_bv 64 (start - 3)) = Some (Z_to_bv 8 224)).
    { intros Hz. subst m1. cbv delta [mD] beta. rewrite (proj2 (Z.eqb_neq _ _) Hz).
      miss. miss. apply wbytes_hit1. }
    assert (M2 : off <> 0 -> rdn RSEGS m1 (Z_to_bv 64 (start - 2)) 2
                           = Some (word_to_le_bytes 2 (Z_to_bv 64 off))).
    { intros Hz. subst m1. cbv delta [mD] beta. rewrite (proj2 (Z.eqb_neq _ _) Hz).
      peel. apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 2 (Z_to_bv 64 off))). sidez. }
    clearbody m1.
    set (m2 := mE idx n stride start off m1).
    cbv delta [mF] beta.
    split.
    - (* [comment removed for export] *) miss.
      subst m2. cbv delta [mE mE1] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [miss; miss; exact M4|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [miss; miss; miss; exact M4|].
      miss. miss. miss. miss. miss. exact M4.
    - (* [comment removed for export] *) apply wbytes_hit1.
    - (* [comment removed for export] *) peel.
      subst m2. cbv delta [mE mE1] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0].
      + apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 2 (Z_to_bv 64 QQ))). sidez.
      + destruct (Z.ltb_spec RR 5) as [Hr5|Hr5].
        * peel. apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 2 (Z_to_bv 64 QQ))). sidez.
        * peel. peel. peel. apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 2 (Z_to_bv 64 QQ))). sidez.
    - (* [comment removed for export] *) intros Hr. miss.
      subst m2. cbv delta [mE] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [lia|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [apply wbytes_hit1|].
      miss. destruct (Z.eq_dec RR 5) as [H5|H5].
      + replace (start + stride - 4 - 5) with (PP + n) by lia. apply wbytes_hit1.
      + miss. apply wbytes_hit1.
    - (* [comment removed for export] *) intros Hr. miss.
      subst m2. cbv delta [mE] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [lia|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [lia|].
      miss. replace (EE - 5) with (start + stride - 4 - 5) by lia. apply wbytes_hit1.
    - (* [comment removed for export] *) intros Hr. peel.
      subst m2. cbv delta [mE] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [lia|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [lia|].
      replace (EE - 4) with (start + stride - 4 - 4) by lia.
      apply (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 RR))). sidez.
    - (* [comment removed for export] *) intros Hz. miss.
      subst m2. cbv delta [mE mE1] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [miss; miss; exact (M3 Hz)|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [miss; miss; miss; exact (M3 Hz)|].
      miss. miss. miss. miss. miss. exact (M3 Hz).
    - (* [comment removed for export] *) intros Hz. peel.
      subst m2. cbv delta [mE mE1] beta zeta.
      destruct (Z.eqb_spec RR 0) as [Hr0|Hr0]; [peel; peel; exact (M2 Hz)|].
      destruct (Z.ltb_spec RR 5) as [Hr5|Hr5]; [peel; peel; peel; exact (M2 Hz)|].
      peel. peel. peel. peel. peel. exact (M2 Hz).
    - lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma enframe_run : forall regs rom (ret : word),
    getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 idx ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 13 = c ->
    exists regs',
      msteps RSEGS (mkst regs (0x1d81c%bv : word) mem0 rom) (mkst regs' ret memF rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 PP.
  Proof.
    intros regs rom ret R1 Hret R10 R11 R12 R13. facts.
    (* [comment removed for export] *)
    destruct (blockA_run _ _ _ _ _ _ _ _ _ _ _ _ rom H regs R10) as (r1 & RUN1 & K1 & A14 & P1).
    assert (A10 : getr r1 10 = Z_to_bv 64 g) by (rewrite P1 by discriminate; exact R10).
    assert (A11 : getr r1 11 = Z_to_bv 64 idx) by (rewrite P1 by discriminate; exact R11).
    assert (A12 : getr r1 12 = Z_to_bv 64 n) by (rewrite P1 by discriminate; exact R12).
    assert (A13 : getr r1 13 = c) by (rewrite P1 by discriminate; exact R13).
    assert (A1 : getr r1 1 = ret) by (rewrite P1 by discriminate; exact R1).
    (* [comment removed for export] *)
    destruct (blockB_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r1 A10 A11 A12 A13 A14)
      as (r2 & RUN2 & K2 & (B15 & B16 & B17 & B5 & B6 & B7 & P2)).
    assert (B10 : getr r2 10 = Z_to_bv 64 g) by (rewrite P2 by discriminate; exact A10).
    assert (B11 : getr r2 11 = Z_to_bv 64 idx) by (rewrite P2 by discriminate; exact A11).
    assert (B12 : getr r2 12 = Z_to_bv 64 n) by (rewrite P2 by discriminate; exact A12).
    assert (B14 : getr r2 14 = Z_to_bv 64 stride) by (rewrite P2 by discriminate; exact A14).
    assert (B1 : getr r2 1 = ret) by (rewrite P2 by discriminate; exact A1).
    (* [comment removed for export] *)
    destruct (blockC_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r2 B17 B5 B6) as (r3 & RUN3 & K3 & C17 & P3).
    assert (C10 : getr r3 10 = Z_to_bv 64 g) by (rewrite P3 by discriminate; exact B10).
    assert (C11 : getr r3 11 = Z_to_bv 64 idx) by (rewrite P3 by discriminate; exact B11).
    assert (C12 : getr r3 12 = Z_to_bv 64 n) by (rewrite P3 by discriminate; exact B12).
    assert (C14 : getr r3 14 = Z_to_bv 64 stride) by (rewrite P3 by discriminate; exact B14).
    assert (C15 : getr r3 15 = Z_to_bv 64 start) by (rewrite P3 by discriminate; exact B15).
    assert (C16 : getr r3 16 = Z_to_bv 64 M) by (rewrite P3 by discriminate; exact B16).
    assert (C1 : getr r3 1 = ret) by (rewrite P3 by discriminate; exact B1).
    (* [comment removed for export] *)
    destruct (blockD_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r3 C15 C17 C10 C16) as (r4 & RUN4 & K4 & D13 & D16 & P4).
    assert (D11 : getr r4 11 = Z_to_bv 64 idx) by (rewrite P4 by discriminate; exact C11).
    assert (D12 : getr r4 12 = Z_to_bv 64 n) by (rewrite P4 by discriminate; exact C12).
    assert (D14 : getr r4 14 = Z_to_bv 64 stride) by (rewrite P4 by discriminate; exact C14).
    assert (D15 : getr r4 15 = Z_to_bv 64 start) by (rewrite P4 by discriminate; exact C15).
    assert (D1 : getr r4 1 = ret) by (rewrite P4 by discriminate; exact C1).
    set (m1 := mD start off mem0) in *.
    assert (G1 : mem_grows mem0 m1) by (subst m1; apply grows_mD).
    (* [comment removed for export] *)
    destruct (blockE1_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r4 m1 D13 D15 D14 D16 D12 D11 G1)
      as (r5 & RUN5 & K5 & E10 & E12 & E14 & E16 & P5).
    assert (E13 : getr r5 13 = Z_to_bv 64 PP) by (rewrite P5 by discriminate; exact D13).
    assert (E1' : getr r5 1 = ret) by (rewrite P5 by discriminate; exact D1).
    (* [comment removed for export] *)
    destruct (blockE2_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r5 m1 E16 E10 E12 E14 G1)
      as (r6 & RUN6 & K6 & F10 & P6).
    assert (F13 : getr r6 13 = Z_to_bv 64 PP) by (rewrite P6 by discriminate; exact E13).
    assert (F1 : getr r6 1 = ret) by (rewrite P6 by discriminate; exact E1').
    (* [comment removed for export] *)
    assert (G2 : mem_grows mem0 (mE idx n stride start off m1))
      by (eapply mem_grows_trans; [exact G1 | apply grows_mE]).
    destruct (blockF_run _ _ _ _ _ _ _ _ _ _ _ _ rom H r6 _ ret F13 F10 F1 Hret
                (rd_idx _ _ _ _ _ _ _ _ _ _ _ _ H m1) G2)
      as (r7 & RUN7 & K7 & Z10).
    exists r7. split; [|split].
    - unfold memF. fold m1.
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
      eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. exact RUN7.
    - repeat (eapply keeps_cs_trans; [eassumption|]); first [assumption | apply keeps_cs_refl].
    - exact Z10.
  Qed.
End Enframe.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_enframe :
  forall regs mem rom (ret c : word) (g M W idx n h3 o16 stride start off : Z),
    efH mem c g M W idx n h3 o16 stride start off ->
    getr regs 1 = ret -> ret_ok ret ->
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 idx ->
    getr regs 12 = Z_to_bv 64 n -> getr regs 13 = c ->
    exists regs' mem',
      msteps RSEGS (mkst regs (0x1d81c%bv : word) mem rom) (mkst regs' ret mem' rom)
      /\ keeps_cs regs regs'
      /\ getr regs' 10 = Z_to_bv 64 (start + 16 * off)
      /\ frame_mod mem mem' [(Z_to_bv 64 (start - 3), stride - 1)]
      /\ enframe_post mem' idx n stride start off.
Proof.
  intros regs mem rom ret c g M W idx n h3 o16 stride start off EH R1 Hret R10 R11 R12 R13.
  destruct (enframe_run mem c g M W idx n h3 o16 stride start off EH regs rom ret R1 Hret R10 R11 R12 R13)
    as (regs' & RUN & K & A0).
  exists regs', (memF mem idx n stride start off). split; [|split; [|split; [|split]]].
  - exact RUN.
  - exact K.
  - exact A0.
  - exact (frame_memF mem c g M W idx n h3 o16 stride start off EH).
  - exact (post_memF mem c g M W idx n h3 o16 stride start off EH).
Qed.

