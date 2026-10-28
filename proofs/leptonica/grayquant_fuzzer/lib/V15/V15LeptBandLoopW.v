(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptDefs LeptStructs LeptArith DitherLib DitherLoop KernelW.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL8a.
Import V15CL8a.V15LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptCmap2 V15LeptBandLoop V15LeptMaskBand.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section BandLoopW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Theorem band_loop_hop_W : band_loop_hop.
Proof.
  unfold band_loop_hop, BAND_WIN, BAND_HEAD, BAND_EXIT, BAND_CLOB.
  intros fx C A Ar M md regs s w h d datad datag S CK HW SUB Hlo Hhi HOK Hw1 Hh1 Hd Ld Ld0 Ld00 Lg NEdg Rd Rg H2 H18 H19 H20 H10 H9 H8 H23 Kh Kw Kd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (hdr_ok_1 w h d HOK Hw1 Hh1) as HOK1.
  destruct HOK as (DV & Hw2 & Hh2 & Hsz). destruct HOK1 as (_ & _ & _ & Hsz1).
  pose proof (wpl_of_range w d ltac:(lia) DV) as Hwr. pose proof (wpl_of_range w 1 ltac:(lia) ltac:(left; reflexivity)) as Hwr1.
  assert (HwD : (w * d <= 32 * wpl_of w d /\ wpl_of w d <= 5000)%Z).
  { unfold wpl_of. pose proof (Z.div_mod (w * d + 31) 32 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (w * d + 31) 32 ltac:(lia)) as MB.
    destruct Hd as [-> | [-> | ->]]; lia. }
  assert (Hw32 : (w <= 32 * wpl_of w 1 /\ wpl_of w 1 <= 5000)%Z).
  { unfold wpl_of. pose proof (Z.div_mod (w * 1 + 31) 32 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (w * 1 + 31) 32 ltac:(lia)) as MB. lia. }
  set (wplg := wpl_of w d) in *. set (wpld := wpl_of w 1) in *.
  set (n := (4 * (wpld * h))%Z) in *. set (ng := (4 * (wplg * h))%Z) in *.
  assert (Hn0 : (0 < n)%Z) by (assert (1 * 1 <= wpld * h)%Z by (apply Z.mul_le_mono_nonneg; lia); unfold n; lia).
  assert (Hng0 : (0 < ng)%Z) by (assert (1 * 1 <= wplg * h)%Z by (apply Z.mul_le_mono_nonneg; lia); unfold ng; lia).
  destruct (blk_range C A M md (Z_to_bv 64 datad) n CK HW Ld Hn0) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  destruct (blk_range C A M md (Z_to_bv 64 datag) ng CK HW Lg Hng0) as [Gg TOPg]. rewrite u_Z2bv in Gg, TOPg by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lg) as (_ & ALg & _). rewrite u_Z2bv in ALg by lia.
  assert (GEO : band_geom d (s - 128) datad datag w h wpld wplg).
  { unfold band_geom. fold n. fold ng. pose proof (mod16_mod4 _ ALd). pose proof (mod16_mod4 _ ALg). unfold n, ng in *. repeat split; first [assumption | lia]. }
  assert (GDJ : band_disj (s - 128) datad h wpld) by (unfold band_disj; fold n; lia).
  assert (RO : regions_ok SEGS M [RD datad h wpld; RS datag h wplg]).
  { intros r Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | []]]; unfold RD, RS; cbn [fst snd]; fold n; fold ng; (repeat split; try lia).
    - exact (blk_sok C A M md datad n CK HW Ld ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (blk_sok C A M md datag ng CK HW Lg ltac:(lia) ltac:(lia) ltac:(lia)). }
  assert (KC : kcs d (s - 128) w h M).
  { unfold kcs. replace (s - 128 + 12)%Z with (s + -116)%Z by lia. replace (s - 128 + 16)%Z with (s + -112)%Z by lia. replace (s - 128 + 20)%Z with (s + -108)%Z by lia.
    repeat split; assumption. }
  assert (H2' : getr regs 2 = Z_to_bv 64 (s - 128)) by (rewrite H2; f_equal; lia).
  assert (RUNX : exists regs' M', msteps SEGS (@mkst fx regs (Z_to_bv 64 115564) M al_rom) (@mkst fx regs' (Z_to_bv 64 116064) M' al_rom)
            /\ rinv [RD datad h wpld] M M' /\ regs_agree (fun r => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%list) regs regs').
  { destruct Hd as [-> | [-> | ->]].
    - exact (band_run_2 al_rom (s - 128) datad datag w h wpld wplg GEO GDJ M regs RO KC H2' H8 H9 H10 H18 H19 H20 H23).
    - exact (band_run_4 al_rom (s - 128) datad datag w h wpld wplg GEO GDJ M regs RO KC H2' H8 H9 H10 H18 H19 H20 H23).
    - exact (band_run_8 al_rom (s - 128) datad datag w h wpld wplg GEO GDJ M regs RO KC H2' H8 H9 H10 H18 H19 H20 H23). }
  destruct RUNX as (regs' & M' & RUN & RI & AG).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  destruct (rinv_WP C A Ar M md M' s [RD datad h wpld] CK HW SUB Hhi RI) as [HW' PM'].
  { intros r [<- | []]. right. exists (Z_to_bv 64 datad), n. rewrite u_Z2bv by lia. unfold RD. cbn [fst snd]. fold n. repeat split; first [assumption | lia]. }
  apply (HK regs' M' HW' PM' AG).
  intros x Hx. apply (proj2 RI). intros r [<- | []]. unfold RD, inreg. cbn [fst snd]. fold n. exact Hx.
Qed.
End BandLoopW.
