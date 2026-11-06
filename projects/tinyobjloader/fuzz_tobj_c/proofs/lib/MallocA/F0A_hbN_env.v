(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "modulo"; "of_nat"; "pow"; "mul"; "sub"; "@Corelib.Numbers.BinNums"; "Z"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "rw"; "eval"; "rm"; "valuation"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry"; "PG"; "SHADOW_BAND_HI"; "SHADOW_BAND_LO"; "Sh"; "round_up"; "IMG_HI"; "kSpaceSize"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "aa_sec"; "sc_map_beg"; "sc_size"; "topG"; "AA"; "aa_geom"; "ag_ctx"; "ag_pab"; "ag_spacebeg"; "ag_thread"; "ageom"; "sc_map_size"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells"; "bview"; "cell_ok"; "mkACell"; "rtc_inv"; "view"; "present"; "@Corelib.Init.Datatypes"; "option"; "list"; "None"; "Some"; "length"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_hbN_env"; "bandz"; "hbenv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv"; "secondary_repr"; "AInvA"; "geom_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4"; "chunk_sh_zone"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc"; "vCTX"; "vT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind"; "blind_rel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states"; "mT"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface"; "top_high"; "tp_ok"; "@Stdlib.Lists.List"; "nth_error"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia Permutation FunctionalExtensionality.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import Asan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety SysSpec SysStep.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundL SymSoundV SymSoundM SymEntail SymFrame SymCFG SymCall SymSummary ExampleMemcpy Glue3 SymObj.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA SummaryA GlueA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocInv Glue ReprGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import AxXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Geometry Budget Model RtCells Inv Iface.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a1.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a5.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require GlueM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ad.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require aa.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ_defs SegQ_wf2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a6.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ae.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQtr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ak.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bc.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3R_loop.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bd.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b8.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require CertMallocSP.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ab.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require a2.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b9.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require be.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require ba.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b7.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bf.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require SegQ3M_glue SegQ_wf4.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require F0A_zones.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require b0.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require az.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bb.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require bv.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require RebuildM F0A_blind.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require cj.
Import OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Geometry OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Budget OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RtCells OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Iface OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a0.CertStackFree OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.CertStackMalloc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.CertMallocS1 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.GlueM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.GlueMA OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.SegD_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.InvFoot OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf2 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQsep OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a1.SegQ1_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQ3_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a4.SegQlib OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQpiece OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ae.SegQ3_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a6.SegQ3R_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a7.SegQ3D_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a8.SegQ3G_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQtr OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ak.SegQ3RM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3R_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3R_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bc.SegQ3DM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bd.SegQ3D_inv OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b8.SegQ3D_skel OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.CertMallocSP OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.aa.SegQI_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a9.SegQI OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ab.SegQI_side OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a2.SegQC_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQC OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_loop OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_exit OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b9.SegQ3D_qi_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.be.SegQ3D_qi_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b3.SegQ3D_qc_defs OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ba.SegQ3D_qc_arith OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qc OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.ad.GlueMU OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a3.SegQ_wf3 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b7.SegQ3D_qip OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bf.SegQ3D_qiq OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ3M_glue OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQ_wf4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.a5.SegQpieceM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_zones OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.b0.InvQ OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.az.InvQ4 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bb.InvQ10 OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.bv.SegQS_k OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.RebuildM OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.F0A_blind OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.F0A_hbN_states OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.cj.InvQ11.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition bandz (z : Z) : Prop := ltac2:(tb__ "0|0|
S0S4S16Vz;A2S6Vz;S15A2A2").

Lemma rtc_inv_band : ltac2:(tb__ "0|0|
S29S29S27S39R1A1ScS2S35R1A1A1S1S2fSeQ8A1A1R5R2A1R6R2A1A3F_;Fz;S2cR5R3A2S2cR5R4A2F_;F_;F_;FG;Fm';Fm;").
Proof.
  intros m m' G HG Hm H. unfold rtc_inv in *. apply (cells_ok_frame _ m m'); [|exact H]. intros z Hz. apply Hm. intros HB. unfold bandz in HB.
  destruct HG as (F1 & _ & T1 & C1 & D1 & _).
  destruct F1 as (_ & _ & _ & _ & _ & F5). destruct T1 as (_ & _ & _ & _ & _ & T5). destruct C1 as (_ & _ & _ & _ & C5). destruct D1 as (_ & _ & _ & _ & D5).
  assert (FST : FS_total = 0xb09000) by reflexivity. rewrite FST in F5.
  destruct (rtc_foot_cases G z Hz) as [X|[X|[X|[X|X]]]]; unfold IMG_LO, IMG_HI, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END in *; lia.
Qed.

Lemma secondary_repr_band : ltac2:(tb__ "0|4|
S29S29S21ScS2S35R1A1M0A1S1S2fSeQ8A1M1A1M2R4R2A1R5R2A1A3F_;Fz;ScG0S2S1G2R6R2A1S31G1A1M3A3A1S2S1G2R6R3A1G3A3A1F_;F_;Fz;S37R5R3A2S37R5R4A2F_;F_;F_;FA;Fm';Fm;").
Proof.
  intros m m' A Hout Hin (S1 & SP & S2 & S3 & S4 & I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9). unfold secondary_repr.
  assert (CO : forall c, (c_addr c + Z.of_nat (c_w c) <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= c_addr c) -> cell_ok m c -> cell_ok m' c).
  { intros c Hc. apply cell_ok_agree. intros k Hk. apply Hout. unfold bandz. lia. }
  assert (PO : forall lo hi, (hi <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= lo) -> present m lo hi -> present m' lo hi).
  { intros lo hi Hc. apply present_agree. intros z Hz. apply Hout. unfold bandz. lia. }
  pose proof S4 as (_ & P1 & P2 & P3 & P4 & P5). unfold kPtrArrayReserve in P1, P2, P3, P4, P5. pose proof S2 as S2'. unfold kPtrArrayReserve in S2'.
  assert (LIT : forall a w, a + w <= 0xee070 -> a + w <= SHADOW_BAND_LO \/ SHADOW_BAND_HI <= a) by (intros a w Ha; unfold SHADOW_BAND_LO, LOW_SHADOW_BEG; lia).
  split.
  { intros i ch Hi. destruct (S1 i ch Hi) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14).
    pose proof D10 as (X1 & X2 & X3 & X4 & X5).
    pose proof (proj1 (nth_error_Some (aa_sec A) i) ltac:(rewrite Hi; discriminate)) as LT.
    split; [(eapply CO; [|exact D1]; cbn; unfold PG in *; lia)|]. split; [(eapply CO; [|exact D2]; cbn; unfold PG in *; lia)|].
    split; [(eapply CO; [|exact D3]; cbn; unfold PG in *; lia)|]. split; [(eapply CO; [|exact D4]; cbn; unfold PG in *; lia)|].
    split; [(eapply CO; [|exact D5]; cbn; unfold PG in *; lia)|].
    repeat (split; [assumption|]). split.
    - intros z Hz NL. destruct (D13 z Hz NL) as [b Hb]. exists b. rewrite Hout; [exact Hb | unfold bandz; lia].
    - intros z Hz. destruct (D14 z Hz) as [b Hb]. destruct (m' z) eqn:E; [eexists; reflexivity|]. exfalso.
      destruct (Z_le_dec SHADOW_BAND_LO z) as [L1|L1]; [destruct (Z_lt_dec z SHADOW_BAND_HI) as [L2|L2]|].
      + apply (Hin z (conj L1 L2)); [rewrite Hb; discriminate | exact E].
      + rewrite Hout in E by (unfold bandz; lia). congruence.
      + rewrite Hout in E by (unfold bandz; lia). congruence. }
  split; [eapply PO; [|exact SP]; pose proof (Nat2Z.is_nonneg (length (aa_sec A))); lia|]. split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
  split; [(eapply CO; [|exact I1]; apply LIT; unfold SEC_INST; cbn; lia)|].
  split; [(eapply CO; [|exact I2]; apply LIT; unfold SEC_INST; cbn; lia)|].
  split; [(eapply CO; [|exact I3]; apply LIT; unfold SEC_INST; cbn; lia)|].
  split; [(eapply CO; [|exact I4]; apply LIT; unfold SEC_INST; cbn; lia)|].
  split; [(eapply CO; [|exact I5]; apply LIT; unfold SEC_INST; cbn; lia)|].
  split; [(eapply CO; [|exact I6]; apply LIT; unfold SEC_INST; cbn; lia)|].
  split; [eapply PO; [|exact I7]; unfold SHADOW_BAND_LO, LOW_SHADOW_BEG; lia|].
  split; [(eapply CO; [|exact I8]; apply LIT; cbn; lia)|].
  eapply PO; [|exact I9]. unfold SHADOW_BAND_LO, LOW_SHADOW_BEG; lia.
Qed.

Section HBEnv.
Variables (A : AA) (it : Z * Z) (i : nat) (ch : sec_chunk) (rho : valuation).
Let G : ageom := aa_geom A.
Let T : Z := ag_thread G.
Let CTX : Z := ag_ctx G.
Let SB : Z := ag_spacebeg G.
Let PAB : Z := ag_pab G.
Let h : Z := sc_map_beg ch.
Let ms : Z := sc_map_size ch.
Let u : Z := fst it.
Let n : Z := snd it.
Let NC : Z := Z.of_nat (length (aa_sec A)).
Let m : bview := ltac2:(tb__ "0|0|
S2dS1bS12Vrho;A1A2").
Record hbenv : Prop := mkHB {
  hb_hg : geom_ok G;
  hb_hsep3 : sep_geom3 G;
  hb_hrtc : rtc_inv m G;
  hb_hrig : rw rho 151%positive = Z_to_bv 64 T /\ rw rho 152%positive = Z_to_bv 64 CTX
            /\ rw rho 155%positive = Z_to_bv 64 SB /\ rw rho 195%positive = Z_to_bv 64 (SB + kSpaceSize);
  hb_hsr : secondary_repr m A;
  hb_hi : nth_error (aa_sec A) i = Some ch;
  hb_hu : u = h + PG + 2048;
  hb_hsz : sc_size ch = round_up n 8 + 4096;
  hb_hsep : (h + ms <= SB \/ SB + kSpaceSize + 4096 <= h) /\ (h + ms <= T \/ T + 0x1000 <= h) /\ (h + ms <= PAB \/ PAB + kPtrArrayReserve <= h)
            /\ (h + ms <= CTX \/ CTX + 0x1000 <= h)
            /\ (forall j ch', nth_error (aa_sec A) j = Some ch' -> i <> j -> h + ms <= sc_map_beg ch' \/ sc_map_beg ch' + sc_map_size ch' <= h);
  hb_him : True;
  hb_hstat : present m (T + 2768) (T + 3168);
  hb_hn : 1 <= n;
  hb_hv : rw rho 12%positive = Z_to_bv 64 u /\ rw rho 200%positive = Z_to_bv 64 PAB /\ rw rho 201%positive = Z_to_bv 64 NC /\ True /\ True
}.
End HBEnv.

Section Intro.
Variables (Kc : KcA).
Hypothesis HKc : Kc_ok Kc.
Variables (A : AA) (p n : Z) (i : nat) (ch : sec_chunk).
Hypothesis HI : ltac2:(tb__ "0|0|
S1S2fS1cA1S43S1cS1dVA;A1Vi;A3S32S1cVch;A2A3").
Hypothesis HU : ltac2:(tb__ "0|0|
S1ScVp;S5S5S1eVch;A1S14A2Z800A2A3").
Hypothesis HSZ : ltac2:(tb__ "0|0|
S1ScS1fVch;A1S5S18Vn;Z8A2Z1000A2A3").
Hypothesis HN : 1 <= n.

Lemma shz_bandz : ltac2:(tb__ "0|3|
S4Z0M0S1eVch;A1M1A2S4G0S28Vch;A1M2A2S4S5G1G2A2S9Z2Z2fA2A2ScS3aVch;R1A2S35R2A1F_;Fz;F_;F_;F_;").
Proof.
  intros H0 H1 H2 z Hz. unfold chunk_sh_zone in Hz.
  pose proof (Z.div_pos (sc_map_beg ch) 8 ltac:(lia) ltac:(lia)) as B1.
  pose proof (Z.div_le_upper_bound (sc_map_beg ch + sc_map_size ch) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as B2.
  unfold bandz, SHADOW_BAND_LO, SHADOW_BAND_HI, LOW_SHADOW_BEG, HIGH_SHADOW_END, Sh, SHADOW_OFF in *. lia.
Qed.

Lemma hbenv_intro : ltac2:(tb__ "0|4|
ScOF_;S13S13S30SeQ40M0A1M1A1S30S3cA1S3bS38S1bVA;R5R3R1A5VKc;R3R2A2S42VA;R7A2S41VA;R8A2S1G1S10R9P97A2SdG0S26S22VA;A1M2A1A2A3S1G1S10RaP98A2SdG0S23G2A1A2A3S1G1S10RbP9bA2SdG0S25G2A1M3A2A3S3fS1bS3aVch;A1RdRcRbA5S1G1S10RcPcA2SdG0Vp;A2A3S1G1S10RdPc8A2SdG0S24G2A1A2A3S1G1S10RePc9A2SdG0S8S33S1cS1dVA;A1A2A1A2A3S1G1S10RfPc3A2SdG0S5G3S1aA2A2A3S36VA;S34ScScVp;Vn;A4Vi;Vch;R10A5F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fmd;Ftr;Ftp;Frho;Frp;FTZ;").
Proof.
  intros TZ rp rho tp tr md HA HK Htp Htop E151 E152 E155 (BW & BL & BOUT & BIN & _) E12 E200 E201 E195.
  set (rpK := rho_sets rp [(156%positive, Z_to_bv 64 (ag_spacebeg (aa_geom A) + kSpaceSize))]).
  assert (ERM : rm rpK = rm rp) by (unfold rpK; apply rm_rho_sets).
  assert (OTH : forall v, v <> 156%positive -> rw rpK v = rw rp v) by (intros v Hv; unfold rpK; rewrite rho_sets_other; [reflexivity | cbn; intros [E|[]]; congruence]).
  assert (HK0 : K0 Kc A rpK tp tr md).
  { split; [|split; [exact HK|split; [|split]]].
    - pose proof (AInvA_Q A rp tp md HA) as HQ. unfold AInvQ in *. rewrite ERM. exact HQ.
    - unfold tp_ok in *. rewrite OTH by discriminate. exact Htp.
    - unfold top_high in *. unfold V_DEPTH in *. rewrite !OTH by discriminate. exact Htop.
    - unfold rigidQ. rewrite !OTH by discriminate. split; [exact E151|]. split; [exact E152|]. split; [exact E155|].
      unfold rpK. apply rho_sets_get; [cbn; repeat constructor; cbn; tauto | cbn; tauto]. }
  destruct (kq_facts segsA (K0 Kc) (K0_laws Kc HKc) A rpK tp _ _ HK0) as [HG _ HRTC _ HST _ _ _ _ _ HSEP3 _ _].
  pose proof (ks_repr segsA (K0 Kc) (K0_sec Kc HKc) A rpK tp tr md HK0) as HSR.
  pose proof (ks_sep segsA (K0 Kc) (K0_sec Kc HKc) A rpK tp tr md HK0 i ch HI) as KS. cbv zeta in KS.
  rewrite ERM in HRTC, HST, HSR.
  assert (CHN : 0 <= sc_map_beg ch /\ 0 <= sc_map_size ch /\ sc_map_beg ch + sc_map_size ch <= 2 ^ 47).
  { destruct HSR as (S1 & _). destruct (S1 i ch HI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & D10 & _). destruct D10 as (X1 & X2 & X3 & _).
    pose proof (topG_range (aa_geom A)) as TG. lia. }
  destruct CHN as (CH0 & CH1 & CH2).
  assert (OUT : forall z, ~ bandz z -> view segsA (rm rho) z = view segsA (rm rp) z) by (intros z Hz; apply BOUT; intros HZ; exact (Hz (shz_bandz CH0 CH1 CH2 z HZ))).
  assert (INB : forall z, bandz z -> view segsA (rm rp) z <> None -> view segsA (rm rho) z <> None).
  { intros z _ Hp. destruct (Z_le_dec (Sh (sc_map_beg ch)) z) as [L1|L1]; [destruct (Z_lt_dec z (Sh (sc_map_beg ch + sc_map_size ch))) as [L2|L2]|].
    - apply BIN; [unfold chunk_sh_zone; lia | exact Hp].
    - rewrite BOUT; [exact Hp | unfold chunk_sh_zone; lia].
    - rewrite BOUT; [exact Hp | unfold chunk_sh_zone; lia]. }
  constructor; cbn [fst snd].
  - exact HG.
  - exact HSEP3.
  - exact (rtc_inv_band _ _ _ HG OUT HRTC).
  - rewrite !BW. split; [exact E151|]. split; [exact E152|]. split; [exact E155|]. rewrite <- BW. exact E195.
  - exact (secondary_repr_band _ _ A OUT INB HSR).
  - exact HI.
  - exact HU.
  - exact HSZ.
  - exact KS.
  - exact I.
  - destruct (thr_facts (K0 Kc) (K0_laws Kc HKc) A rpK tp tr md HK0) as (T0 & _ & TB & _). cbv zeta in T0, TB.
    eapply present_agree; [|exact HST]. intros z Hz. apply OUT. unfold bandz. lia.
  - exact HN.
  - split; [exact E12|]. split; [exact E200|]. split; [exact E201|]. split; exact I.
Qed.
End Intro.

Section HBE.
Variables (A : AA) (it : Z * Z) (i : nat) (ch : sec_chunk) (rho : valuation).
Let G : ageom := aa_geom A.
Let T : Z := ag_thread G.
Let CTX : Z := ag_ctx G.
Let SB : Z := ag_spacebeg G.
Let PAB : Z := ag_pab G.
Let h : Z := sc_map_beg ch.
Let ms : Z := sc_map_size ch.
Let u : Z := fst it.
Let n : Z := snd it.
Let NC : Z := Z.of_nat (length (aa_sec A)).
Let m : bview := ltac2:(tb__ "0|0|
S2dS1bS12Vrho;A1A2").

Hypothesis QS : ltac2:(tb__ "0|0|
S36VA;Vit;Vi;Vch;Vrho;A5").
Ltac qs_open := pose proof QS as [HG HSEP3 HRTC HRIG HSR HI HU HSZ HSEP HIM HSTAT HN HV].
Ltac qs_unf := unfold NC, m, n, u, ms, h, PAB, SB, CTX, T, G in *.

Lemma qs_chunk : ltac2:(tb__ "0|6|
S0S1ScS7Vh;S14A2Z0M0A3S0S1ScS7Vms;S14A2G0A3S0S4Z12000Vms;A2S0S4S19Vh;A2S0S4S5Vh;Vms;A2M1S20VG;A1A2S0S3S4G1S16A2S4S15Vh;A2A2S0S4S5S14S1fVch;A1M2A2Vms;A2S0S1ScVms;S5S18G2S14A2S14A2A3S0S2aVm;S2bVh;U8M3Vh;A3A2S0S2aVm;S2bS5Vh;Z8M4A2G3Vms;A3A2S0S2aVm;S2bS5Vh;Z18A2G3S8Vi;A1M5A3A2S0S2aVm;S2bS5VPAB;SaG4G5A2A2G3Vh;A3A2S2eVm;S17Vh;A1S17G1A1A3A2A2A2A2A2A2A2A2A2A2A2A2").
Proof.
  qs_open. destruct HSR as (SC1 & _). destruct (SC1 i ch HI) as (C0 & C8 & _ & C24 & CP & D6 & D7 & D8 & D9 & D10 & D11 & D12 & _ & D14).
  pose proof (dyn_in_big _ _ _ D10) as BIG. destruct D10 as (_ & _ & _ & _ & DB).
  qs_unf. rewrite Z.add_0_r in C0.
  assert (MS : 73728 <= sc_map_size ch).
  { rewrite D11. unfold round_up, PG in *. pose proof (Z.div_mod (sc_size ch + (4096 - 1)) 4096 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (sc_size ch + (4096 - 1)) 4096 ltac:(lia)). nia. }
  repeat split; try assumption; try lia.
Qed.

Lemma qs_nums : ltac2:(tb__ "0|6|
S0S4Z1000M0VT;A2S0S4S5VT;G0A2M1S20VG;A1M2A2S0S4G0VCTX;A2S0S4S5VCTX;G0A2M3G2A2S0S0S4Z7fff7f800000G2A2S4G2Z7fffff800000A2A2S0S3S4G1Z10000M4A2S4Z646000M5VT;A2A2S0S3S4G3G4A2S4G5VCTX;A2A2S3S4G1VCTX;A2S4G3VT;A2A2A2A2A2A2A2A2A2").
Proof.
  qs_open. pose proof (geom_nums _ HG) as (_ & _ & _ & T0 & T1 & _ & C0 & C1 & _ & _ & _ & _ & _ & TG).
  pose proof (geom_bands _ HG) as (_ & _ & _ & _ & TI & CI & _). pose proof (geom_seps _ HG) as (_ & _ & _ & _ & Q5 & _).
  unfold IMG_LO, IMG_HI in *. qs_unf. repeat split; try assumption; lia.
Qed.

Lemma hb_E : ltac2:(tb__ "0|2|
S0S1ScSfQ40M0S11Vrho;S3eA2A2VT;A3S0S1ScSfG0S11Vrho;S3dA2A2VCTX;A3S0S1SeG0A1S11Vrho;S40A2SdG0SbVu;Z10A2M1A2A3S0S4Z0G1A2S6G1S9Z2Z2fA2A2A2A2A2A2").
Proof.
  qs_open. pose proof qs_nums as (T0 & T1 & C0 & C1 & TG & _). pose proof qs_chunk as (_ & _ & MS & IH & HT & _).
  destruct HRIG as (E151 & E152 & _). destruct HV as (E12 & _).
  unfold IMG_HI, PG in *. qs_unf.
  split; [unfold vT; cbn [eval]; rewrite E151; apply u64_lit; lia|]. split; [unfold vCTX; cbn [eval]; rewrite E152; apply u64_lit; lia|].
  split; [|lia]. unfold mT. apply (ev_add_lit rho (SVar 12) (fst it) (-16)); [cbn [eval]; exact E12 | lia | lia | lia].
Qed.
End HBE.
