(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)

From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require StackLayout.
From LinuxProcessSemantics.LinuxProcessSem Require Fs.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Monad.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PropExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require CatSim.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StepTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Hoare.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require ShapeAlg.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require AllocIface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require PureModel.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require VmLedger.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StoreOk.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocCalloc.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require WalksLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require W2Lib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptDefs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptArith.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLib.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require DitherLoop.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require KernelW.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL8a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL10a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptCmap2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCopy.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15CL2a.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptDithBinLow.
Module V15LeptDithBinW.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StartupTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.WalkTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.W2Lib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.DitherLoop.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.KernelW.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL8a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCreate.
Import V15CL10a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptCmap2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopy.
Import V15CL2a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptDithBinLow.
(* [comment removed for export] *)









Import V15CL8a.V15LeptPixHdr.


Import V15CL10a.V15LeptCmapValid.


Import V15CL2a.V15LeptDithBin.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section DithBinW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma dith_wpl_facts : forall w h, hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  (1 <= wpl_of w 8 <= 5000 /\ 1 <= wpl_of w 1 <= 625 /\ w <= 4 * wpl_of w 8 /\ w <= 32 * wpl_of w 1 /\ wpl_of w 1 <= wpl_of w 8 /\
   wpl_of w 8 * h <= 2 ^ 24 /\ wpl_of w 1 * h <= 2 ^ 24 /\ 1 <= wpl_of w 8 * h /\ 1 <= wpl_of w 1 * h)%Z.
Proof.
  intros w h (DV & Hw & Hh & Hsz) Hw1 Hh1. unfold wpl_of in *.
  pose proof (Z.div_mod (w * 8 + 31) 32 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (w * 8 + 31) 32 ltac:(lia)) as M8.
  pose proof (Z.div_mod (w * 1 + 31) 32 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (w * 1 + 31) 32 ltac:(lia)) as M1.
  set (a := ((w * 8 + 31) / 32)%Z) in *. set (b := ((w * 1 + 31) / 32)%Z) in *.
  assert (Hba : (b <= a)%Z) by lia. assert (Hb1 : (1 <= b)%Z) by lia. assert (Ha1 : (1 <= a)%Z) by lia.
  pose proof (Z.mul_le_mono_nonneg_r b a h ltac:(lia) Hba) as P1.
  pose proof (Z.mul_le_mono_nonneg 1 a 1 h ltac:(lia) Ha1 ltac:(lia) Hh1) as P2.
  pose proof (Z.mul_le_mono_nonneg 1 b 1 h ltac:(lia) Hb1 ltac:(lia) Hh1) as P3.
  repeat split; lia.
Qed.

Theorem dbl_call_W : forall (fx : FPState) C A Ar M md regs (s w h datad datat bufs1 bufs2 lc uc : Z) (ret : word) (S : TSet),
  Cok C -> W C A M md -> sub_live Ar A ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 <= s)%Z -> (s + 16 <= c_top C)%Z ->
  hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z -> (0 <= lc <= 255)%Z -> (0 <= uc <= 255)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (wpl_of w 1 * h))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datat) = Some (4 * (wpl_of w 8 * h))%Z ->
  live A (Z_to_bv 64 bufs1) = Some (4 * wpl_of w 8)%Z -> live Ar (Z_to_bv 64 bufs1) = None -> live (c_A0 C) (Z_to_bv 64 bufs1) = None ->
  live A (Z_to_bv 64 bufs2) = Some (4 * wpl_of w 8)%Z -> live Ar (Z_to_bv 64 bufs2) = None -> live (c_A0 C) (Z_to_bv 64 bufs2) = None ->
  (0 <= datad < 2 ^ 64)%Z -> (0 <= datat < 2 ^ 64)%Z -> (0 <= bufs1 < 2 ^ 64)%Z -> (0 <= bufs2 < 2 ^ 64)%Z ->
  Z_to_bv 64 datad <> Z_to_bv 64 datat -> Z_to_bv 64 datad <> Z_to_bv 64 bufs1 -> Z_to_bv 64 datad <> Z_to_bv 64 bufs2 ->
  Z_to_bv 64 datat <> Z_to_bv 64 bufs1 -> Z_to_bv 64 datat <> Z_to_bv 64 bufs2 -> Z_to_bv 64 bufs1 <> Z_to_bv 64 bufs2 ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 w -> getr regs 12 = Z_to_bv 64 h -> getr regs 13 = Z_to_bv 64 (wpl_of w 1) ->
  getr regs 14 = Z_to_bv 64 datat -> getr regs 15 = Z_to_bv 64 (wpl_of w 8) -> getr regs 16 = Z_to_bv 64 bufs1 -> getr regs 17 = Z_to_bv 64 bufs2 ->
  getr regs 28 = Z_to_bv 64 lc -> getr regs 29 = Z_to_bv 64 uc ->
  (forall regs' m', W C A m' md -> POSTM C Ar s M m' -> cs_kept regs regs' ->
      (forall (q : word) k, live A q = Some k -> q <> Z_to_bv 64 datad -> q <> Z_to_bv 64 bufs1 -> q <> Z_to_bv 64 bufs2 ->
                            forall i, (0 <= i < k)%Z -> m' (at_ q i) = M (at_ q i)) ->
      realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 0x1b95c) M al_rom) md) S.
Proof.
  intros fx C A Ar M md regs s w h datad datat bufs1 bufs2 lc uc ret S CK HW SUB Hs16 Hlo Hhi16 HOK Hw1 Hh1 Hlc Huc
         Ld Ld0 Ld00 Lt L1 L10 L100 L2 L20 L200 Rd Rt R1 R2 NEdt NEd1 NEd2 NEt1 NEt2 NE12 H1 Hret H2 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL. assert (Hhi : (s <= c_top C)%Z) by lia.
  destruct (dith_wpl_facts w h HOK Hw1 Hh1) as (Gs & Gdw & Gw4 & Gw32 & Gds & Psh & Pdh & Psh1 & Pdh1).
  destruct HOK as (DV & Hw2 & Hh2 & Hsz).
  set (wpls := wpl_of w 8) in *. set (wpld := wpl_of w 1) in *.
  set (nd := (4 * (wpld * h))%Z) in *. set (ns := (4 * (wpls * h))%Z) in *. set (nb := (4 * wpls)%Z) in *.
  destruct (blk_range C A M md (Z_to_bv 64 datad) nd CK HW Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  destruct (blk_range C A M md (Z_to_bv 64 datat) ns CK HW Lt ltac:(lia)) as [Gt TOPt]. rewrite u_Z2bv in Gt, TOPt by lia.
  destruct (blk_range C A M md (Z_to_bv 64 bufs1) nb CK HW L1 ltac:(lia)) as [G1 TOP1]. rewrite u_Z2bv in G1, TOP1 by lia.
  destruct (blk_range C A M md (Z_to_bv 64 bufs2) nb CK HW L2 ltac:(lia)) as [G2 TOP2]. rewrite u_Z2bv in G2, TOP2 by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lt) as (_ & ALt & _). rewrite u_Z2bv in ALt by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) L1) as (_ & AL1 & _). rewrite u_Z2bv in AL1 by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) L2) as (_ & AL2 & _). rewrite u_Z2bv in AL2 by lia.
  assert (GEO : low_geom s datad w h wpld datat wpls bufs1 bufs2 lc uc).
  { unfold low_geom. fold nd ns nb. pose proof (mod16_mod4 _ ALd). pose proof (mod16_mod4 _ ALt). pose proof (mod16_mod4 _ AL1). pose proof (mod16_mod4 _ AL2).
    repeat split; first [assumption | lia]. }
  assert (GDJ : low_disj s datad h wpld datat wpls bufs1 bufs2).
  { pose proof (blk_apart C A M md _ _ nd ns CK HW Ld Lt NEdt ltac:(lia) ltac:(lia)) as APdt. rewrite !u_Z2bv in APdt by lia.
    pose proof (blk_apart C A M md _ _ nd nb CK HW Ld L1 NEd1 ltac:(lia) ltac:(lia)) as APd1. rewrite !u_Z2bv in APd1 by lia.
    pose proof (blk_apart C A M md _ _ nd nb CK HW Ld L2 NEd2 ltac:(lia) ltac:(lia)) as APd2. rewrite !u_Z2bv in APd2 by lia.
    pose proof (blk_apart C A M md _ _ ns nb CK HW Lt L1 NEt1 ltac:(lia) ltac:(lia)) as APt1. rewrite !u_Z2bv in APt1 by lia.
    pose proof (blk_apart C A M md _ _ ns nb CK HW Lt L2 NEt2 ltac:(lia) ltac:(lia)) as APt2. rewrite !u_Z2bv in APt2 by lia.
    pose proof (blk_apart C A M md _ _ nb nb CK HW L1 L2 NE12 ltac:(lia) ltac:(lia)) as AP12. rewrite !u_Z2bv in AP12 by lia.
    unfold low_disj, apart. fold nd ns nb.
    refine (conj _ (conj _ (conj _ (conj _ (conj APdt (conj APd1 (conj APd2 (conj APt1 (conj APt2 AP12))))))))); right; clear APdt APd1 APd2 APt1 APt2 AP12; lia. }
  assert (RO : regions_ok SEGS M [((s - 192)%Z, 192%Z); RD datad h wpld; RB1 wpls bufs1; RB2 wpls bufs2; RS h datat wpls]).
  { intros r Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; unfold RD, RB1, RB2, RS; cbn [fst snd]; fold nd ns nb; (repeat split; try lia).
    - exact (W_sok_win C A M md (s - 192) (Z.to_nat 192) CK HW ltac:(lia) ltac:(cbn; lia)).
    - exact (blk_sok C A M md datad nd CK HW Ld ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (blk_sok C A M md bufs1 nb CK HW L1 ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (blk_sok C A M md bufs2 nb CK HW L2 ltac:(lia) ltac:(lia) ltac:(lia)).
    - exact (blk_sok C A M md datat ns CK HW Lt ltac:(lia) ltac:(lia) ltac:(lia)). }
  destruct (dbl_run al_rom s datad w h wpld datat wpls bufs1 bufs2 lc uc GEO GDJ M regs ret Hret RO H2 H1 H10 H11 H12 H13 H14 H15 H16 H17 H28 H29)
    as (regs' & M' & RUN & RI & Q2 & CSV).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
  destruct (rinv_WP C A Ar M md M' s _ CK HW SUB Hhi RI) as [HW' PM'].
  { intros r Hr. unfold RALL in Hr. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | []]]]]; unfold RD, RB1, RB2; cbn [fst snd]; fold nd nb.
    - left. cbn [fst snd]. lia.
    - right. exists (Z_to_bv 64 datad), nd. rewrite u_Z2bv by lia. cbn [fst snd]. repeat split; first [assumption | lia].
    - right. exists (Z_to_bv 64 bufs1), nb. rewrite u_Z2bv by lia. cbn [fst snd]. repeat split; first [assumption | lia].
    - right. exists (Z_to_bv 64 bufs2), nb. rewrite u_Z2bv by lia. cbn [fst snd]. repeat split; first [assumption | lia]. }
  apply (HK regs' M' HW' PM').
  - apply cs_kept_intro; first [ (rewrite Q2, H2; reflexivity) | (apply CSV; cbn [In]; repeat (first [left; reflexivity | right])) ].
  - intros q k Lq NEqd NEq1 NEq2 i Hi. apply (proj2 RI).
    destruct (blk_range C A M md q k CK HW Lq ltac:(lia)) as [Gq TOPq].
    pose proof (blk_apart C A M md _ _ k nd CK HW Lq Ld NEqd ltac:(lia) ltac:(lia)) as APqd. rewrite !u_Z2bv in APqd by lia.
    pose proof (blk_apart C A M md _ _ k nb CK HW Lq L1 NEq1 ltac:(lia) ltac:(lia)) as APq1. rewrite !u_Z2bv in APq1 by lia.
    pose proof (blk_apart C A M md _ _ k nb CK HW Lq L2 NEq2 ltac:(lia) ltac:(lia)) as APq2. rewrite !u_Z2bv in APq2 by lia.
    assert (Ea : u (at_ q i) = (u q + i)%Z) by (unfold at_; rewrite u_Z2bv by lia; reflexivity).
    intros r Hr. unfold RALL in Hr. cbn [In] in Hr. unfold inreg. rewrite Ea.
    destruct Hr as [<- | [<- | [<- | [<- | []]]]]; unfold RD, RB1, RB2; cbn [fst snd]; fold nd nb; lia.
Qed.
End DithBinW.
End V15LeptDithBinW.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPSteps.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoomPC.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptRoom14.
Module V15LeptDither_iface.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptArith.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoomPC.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom14.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL8a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCreate.
Import V15CL10a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopy.
(* [comment removed for export] *)









Import V15CL8a.V15LeptPixHdr.


Import V15CL10a.V15LeptCmapValid.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition PC_pixDitherToBinary : Z := 0x1b5c4.
Definition PC_pixDitherTo2bpp : Z := 0x1c570.
Definition PC_pixcmapCreateLinear : Z := 0x185a0.
Definition PC_pixRemoveColormap : Z := 0x19f1c.
Definition PC_pixDestroy : Z := 0x170a4.
(* [comment removed for export] *)
Definition TP15 : Z := 0x455c0.

(* [comment removed for export] *)
Definition RMC_STACK : Z := 272 + 240 + LSF.                 (* [comment removed for export] *)
Definition CML_STACK : Z := 96 + CALLOC_STACK.               (* [comment removed for export] *)
Definition PXD2_STACK : Z := 64 + ALLOC_STACK.               (* [comment removed for export] *)
Definition DBIN_STACK : Z := 112 + RMC_STACK.                (* [comment removed for export] *)
Definition D2BPP_STACK : Z := 208 + RMC_STACK.               (* [comment removed for export] *)

(* [comment removed for export] *)
Definition RK_rmc : Z := RK_pix + 5.
Definition RB_rmc : Z := RB_pix14 + 5 * 2 ^ 17.
Definition RK_cml : Z := 2.
Definition RB_cml : Z := 2 * 2 ^ 17.
Definition RK_dbin : Z := RK_pix + RK_rmc + 2.                    (* [comment removed for export] *)
Definition RB_dbin : Z := RB_pix14 + RB_rmc + 2 * 2 ^ 21.        (* [comment removed for export] *)
Definition RK_d2bpp : Z := RK_pix + RK_rmc + 5 + RK_cml.          (* [comment removed for export] *)
Definition RB_d2bpp : Z := RB_pix14 + RB_rmc + 2 * 2 ^ 21 + 3 * 2 ^ 17 + RB_cml.   (* [comment removed for export] *)

Section DitherIface.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition cm_facts {fx : FPState} (A : AS) (m : word -> option byte) (cm : Z) (cv : cmapv) : Prop :=
  cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z).

(* [comment removed for export] *)
Definition cmap_new {fx : FPState} (C : lctx) (A A' : AS) (m' : word -> option byte) (cm : Z) (cv : cmapv) : Prop :=
  (4096 <= cm)%Z /\ (cm + 32 <= alloc_top (c_vm C))%Z /\ (4096 <= c_arr cv)%Z /\ (c_arr cv + 4 * c_nalloc cv <= alloc_top (c_vm C))%Z /\ cm <> c_arr cv /\
  live A (Z_to_bv 64 cm) = None /\ live A (Z_to_bv 64 (c_arr cv)) = None /\
  live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
  live A' (Z_to_bv 64 cm) = Some 24%Z /\ live A' (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
  CMAPat m' cm cv /\ cmap_ok cv /\
  (forall q, q <> Z_to_bv 64 cm -> q <> Z_to_bv 64 (c_arr cv) -> live A' q = live A q).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pixRemoveColormap_gray8_contract : Prop :=
  forall (fx : FPState) C A m md regs (s pixs w h cm data : Z) (cv : cmapv) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + RMC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP15 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 ->
  PIXat m pixs (hdv w h 8 cm data) -> hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 8 * h))%Z -> cm_facts A m cm cv ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_rmc <= kR)%Z -> (RB_rmc <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     ( (cm = 0%Z /\ getr regs' 10 = Z_to_bv 64 pixs /\ (forall q, live A' q = live A q) /\
        POSTM C A s (wbytes m (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2)) m')
       \/ (cm <> 0%Z /\ POSTM C A s m m' /\
           exists pixt datat, getr regs' 10 = Z_to_bv 64 pixt /\ pixt_new C A A' m' pixt w h 8 0 datat cv) ) ->
     aroom A' vm' (kR - RK_rmc) (bR - RB_rmc) ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_pixRemoveColormap) m al_rom) md) S.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pixDestroy_rc2_contract : Prop :=
  forall (fx : FPState) C A m md regs (s pp pix : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PXD2_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  PIXat m pix v -> p_rc v = 2%Z -> live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' ->
     POSTM C A (pp + 8) (wbytes (wbytes m (Z_to_bv 64 (pix + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 pp) (Z_to_le_bytes 8 0)) m' ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_pixDestroy) m al_rom) md) S.

(* [comment removed for export] *)
Definition pixcmapCreateLinear24_contract : Prop :=
  forall (fx : FPState) C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CML_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP15 ->
  getr regs 10 = Z_to_bv 64 2 -> getr regs 11 = Z_to_bv 64 4 ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_cml <= kR)%Z -> (RB_cml <= bR)%Z ->
  (forall A' m' vm' regs' (cm arr : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 cm -> cmap_new C A A' m' cm (CMAPV arr 2 4 4 0) ->
     aroom A' vm' (kR - RK_cml) (bR - RB_cml) ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_pixcmapCreateLinear) m al_rom) md) S.

(* [comment removed for export] *)
Definition dith_res {fx : FPState} (C : lctx) (A A' : AS) (m' : word -> option byte) (regs' : bvmap 5 word) (w h dd : Z) (cmapped : bool) : Prop :=
  (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
  \/ (exists pixd datad cd cv', getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h dd cd datad cv' /\
        (if cmapped then cd <> 0%Z /\ c_d cv' = 2%Z /\ c_nalloc cv' = 4%Z /\ c_n cv' = 4%Z else cd = 0%Z)).

(* [comment removed for export] *)
Definition pixDitherToBinary_contract : Prop :=
  forall (fx : FPState) C A m md regs (s pixs w h cm data : Z) (cv : cmapv) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + DBIN_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP15 ->
  getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h 8 cm data) -> hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 8 * h))%Z -> cm_facts A m cm cv ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_dbin <= kR)%Z -> (RB_dbin <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     POSTM C A s m m' -> dith_res C A A' m' regs' w h 1 false ->
     aroom A' vm' (kR - RK_dbin) (bR - RB_dbin) ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_pixDitherToBinary) m al_rom) md) S.

(* [comment removed for export] *)
Definition pixDitherTo2bpp_contract : Prop :=
  forall (fx : FPState) C A m md regs (s pixs w h cm data : Z) (cv : cmapv) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + D2BPP_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP15 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 ->
  PIXat m pixs (hdv w h 8 cm data) -> hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 8 * h))%Z -> cm_facts A m cm cv ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_d2bpp <= kR)%Z -> (RB_d2bpp <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     POSTM C A s m m' -> dith_res C A A' m' regs' w h 2 true ->
     aroom A' vm' (kR - RK_d2bpp) (bR - RB_d2bpp) ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_pixDitherTo2bpp) m al_rom) md) S.

(* [comment removed for export] *)
Definition dither_d_contract (entry : Z) : Prop :=
  forall (fx : FPState) C A m md regs (s pixs w h d cm data : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 32 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h d cm data) -> d <> 8%Z -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 entry) m al_rom) md) S.
Definition pixDitherToBinary_d_contract := dither_d_contract PC_pixDitherToBinary.
Definition pixDitherTo2bpp_d_contract := dither_d_contract PC_pixDitherTo2bpp.

End DitherIface.
End V15LeptDither_iface.

From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require MemSplit.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Amb.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymExec2Sound.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymRun.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExec.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExecW.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require V15LeptPixCopyA.
Module V15LeptThrLeaf.
Import Stdlib.ZArith.ZArith.
Import Stdlib.NArith.NArith.
Import Stdlib.Lists.List.
Import Stdlib.micromega.Lia.
Import Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.
Import LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.LinuxProcessSem.StackLayout.
Import LinuxProcessSemantics.LinuxProcessSem.Fs.
Import LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.LinuxProcessSem.Monad.
Import LinuxProcessSemantics.LinuxProcessSem.Specs.
Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.Riscv.Decode.
Import LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PropExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CatSim.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StepTac.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Hoare.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.ShapeAlg.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.AllocIface.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.PureModel.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.VmLedger.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.StoreOk.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.MemSplit.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPSteps.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.FPStepsV.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocBase.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocCalloc.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng.AllocSure.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.Amb.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymExec2Sound.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymRun.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver.SymDrive.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.WalksLib.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptDefs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptStructs.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptRoom.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExec.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecW.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.LeptExecFP.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptBase.
Import V15CL8a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCreate.
Import V15CL10a.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptCmap2.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopyA.
Import OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15.V15LeptPixCopy.
(* [comment removed for export] *)










Import V15CL8a.V15LeptPixHdr.


Import V15CL10a.V15LeptCmapValid.

Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.

Definition STOPS : list Z := []%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Lemma set_fmt_0 : forall v : pixv, p_fmt v = 0%Z -> set_fmt v 0 = v.
Proof. intros v H. destruct v; cbn in *; subst; reflexivity. Qed.

Lemma pixCopyRes0_W : forall (fx : FPState) C Ar A m md regs (s pixd pixs : Z) (vs vd : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (c_top C - LSTK + 16 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
  PIXat m pixs vs -> PIXat m pixd vd -> (p_xres vs = 0)%Z -> (p_yres vs = 0)%Z -> (p_xres vd = 0)%Z -> (p_yres vd = 0)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 pixd) = Some 64%Z ->
  live Ar (Z_to_bv 64 pixd) = None -> live (c_A0 C) (Z_to_bv 64 pixd) = None -> Z_to_bv 64 pixs <> Z_to_bv 64 pixd ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' -> PIXat m' pixd vd -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 95132) m al_rom) md) S.
Proof.
  intros fx C Ar A0 m0 md r0 s pixd pixs vs vd ret S CK HW0 SUBr H2 Hlo Hhi H1 Hret H10 H11 PXs PXd HP0 HP1 HP2 HP3 Lpixs_a0 Lpixd_a0 Fpixd F0pixd NEsd HC.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 16)%Z) by lia.
  assert (GLO2 : (s - 16 + Z.of_nat (Z.to_nat 16) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (16 <= s)%Z) by lia.
  pose proof PXs as (Hs0 & Hs64 & _). pose proof PXd as (Hd0 & Hd64 & _).
  assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia. assert (RRpixd : (0 <= pixd < 2 ^ 64)%Z) by lia.
  pose proof (exW_blk_apart_h C A0 m0 _ pixs pixd 64 64 CK HW0 Lpixs_a0 Lpixd_a0 NEsd RRpixs RRpixd ltac:(exW_cmp) ltac:(exW_cmp)) as AP_pixs_pixd.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 16 pixd 64 CK HW0 Lpixd_a0 eq_refl RRpixd GLO1) as WAPpixd.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 16 pixs 64 CK HW0 Lpixs_a0 eq_refl RRpixs GLO1) as WAPpixs.
  pose proof (PIX_rd_res0 SEGS m0 pixs vs PXs HP0 HP1) as Csrc. try rewrite HP0 in Csrc.
  destruct (exW_blk_rng C A0 m0 _ pixd 64 CK HW0 Lpixd_a0 RRpixd eq_refl) as (Gd1 & Gd2 & Gd3).
  destruct (exW_blk_rng C A0 m0 _ pixs 64 CK HW0 Lpixs_a0 RRpixs eq_refl) as (Gs1 & Gs2 & Gs3).
  pose proof (ai_live_hull A0 m0 (m_vmmaps (with_vmmaps vm0 md)) _ _ (w_inv _ _ _ _ HW0) Lpixd_a0) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  pose proof (ai_live_hull A0 m0 (m_vmmaps (with_vmmaps vm0 md)) _ _ (w_inv _ _ _ _ HW0) Lpixs_a0) as (_ & ALs & _). rewrite u_Z2bv in ALs by lia.
  pose proof (exW_kwr_blk2 SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixd; pixs; exW_canary SEGS 415784 m0]) (EVar 34) pixd 64 p16_segs CK HW0 Lpixd_a0 RRpixd eq_refl eq_refl) as HKw.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 16) (Z.to_nat 16) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixd; pixs; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixd; pixs; exW_canary SEGS 415784 m0]) (EVar 36) (EVar 32) (exW_canary SEGS 415784 m0) s 16 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixd; pixs; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 0 (2 ^ 63); KRange (EVar 34) 4096 (2 ^ 47); KRange (EVar 35) 4096 (2 ^ 47); KAlign (EVar 34) 16; KAlign (EVar 35) 16; KDisj (SA (EVar 35) 0) 64 (SA (EVar 34) 0) 64; KDisj (SA (EVar 32) (-16)) 16 (SA (EVar 34) 0) 64; KWord (SA (EVar 35) 24) 8 (ELit 0)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKw HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixd; pixs; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKw HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C Ar s m0 M0).
  { subst M0. apply (exW_win_blks C A0 Ar m0 _ E0 log0 (EVar 32) s 16 [(EVar 34, pixd, 64%Z)] CK HW0 SUBr Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRpixd (conj Lpixd_a0 (conj Fpixd F0pixd))))|]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BSF := [(32%nat, s); (34%nat, pixd); (35%nat, pixs)]).
  exW_regfactB BSF HR ex_r10 G10.
  assert (PXd' : PIXat M0 pixd vd).
  { subst M0 log0. cbn [mem_denot]. unfold adenot. cbn [a_base a_off]. change (edenot E0 (EVar 34)) with (Z_to_bv 64 pixd). rewrite zbv_addi. change (edenot E0 (ELit 0)) with (Z_to_bv 64 0). exact (PIX_wr_res0 m0 pixd vd PXd HP2 HP3). }
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  apply (HC M0 RcF HWs0).
  - lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end.
  - exact PMs0.
  - exact PXd'.
  - exact G10.
Qed.

Lemma pixCopyFmt0_W : forall (fx : FPState) C Ar A m md regs (s pixd pixs : Z) (vs vd : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (c_top C - LSTK + 16 <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs ->
  PIXat m pixs vs -> PIXat m pixd vd -> (p_fmt vs = 0)%Z -> (p_fmt vd = 0)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 pixd) = Some 64%Z ->
  live Ar (Z_to_bv 64 pixd) = None -> live (c_A0 C) (Z_to_bv 64 pixd) = None -> Z_to_bv 64 pixs <> Z_to_bv 64 pixd ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' -> PIXat m' pixd vd -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 95788) m al_rom) md) S.
Proof.
  intros fx C Ar A0 m0 md r0 s pixd pixs vs vd ret S CK HW0 SUBr H2 Hlo Hhi H1 Hret H10 H11 PXs PXd HP0 HP1 Lpixs_a0 Lpixd_a0 Fpixd F0pixd NEsd HC.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 16)%Z) by lia.
  assert (GLO2 : (s - 16 + Z.of_nat (Z.to_nat 16) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (16 <= s)%Z) by lia.
  pose proof PXs as (Hs0 & Hs64 & _). pose proof PXd as (Hd0 & Hd64 & _).
  assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia. assert (RRpixd : (0 <= pixd < 2 ^ 64)%Z) by lia.
  pose proof (exW_blk_apart_h C A0 m0 _ pixs pixd 64 64 CK HW0 Lpixs_a0 Lpixd_a0 NEsd RRpixs RRpixd ltac:(exW_cmp) ltac:(exW_cmp)) as AP_pixs_pixd.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 16 pixd 64 CK HW0 Lpixd_a0 eq_refl RRpixd GLO1) as WAPpixd.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 16 pixs 64 CK HW0 Lpixs_a0 eq_refl RRpixs GLO1) as WAPpixs.
  pose proof (PIX_rd_fmt SEGS m0 pixs vs PXs) as Csrc. try rewrite HP0 in Csrc.
  destruct (exW_blk_rng C A0 m0 _ pixd 64 CK HW0 Lpixd_a0 RRpixd eq_refl) as (Gd1 & Gd2 & Gd3).
  destruct (exW_blk_rng C A0 m0 _ pixs 64 CK HW0 Lpixs_a0 RRpixs eq_refl) as (Gs1 & Gs2 & Gs3).
  pose proof (ai_live_hull A0 m0 (m_vmmaps (with_vmmaps vm0 md)) _ _ (w_inv _ _ _ _ HW0) Lpixd_a0) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  pose proof (ai_live_hull A0 m0 (m_vmmaps (with_vmmaps vm0 md)) _ _ (w_inv _ _ _ _ HW0) Lpixs_a0) as (_ & ALs & _). rewrite u_Z2bv in ALs by lia.
  pose proof (exW_kwr_blk2 SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixd; pixs; exW_canary SEGS 415784 m0]) (EVar 34) pixd 64 p16_segs CK HW0 Lpixd_a0 RRpixd eq_refl eq_refl) as HKw.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 16) (Z.to_nat 16) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixd; pixs; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixd; pixs; exW_canary SEGS 415784 m0]) (EVar 36) (EVar 32) (exW_canary SEGS 415784 m0) s 16 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixd; pixs; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 0 (2 ^ 63); KRange (EVar 34) 4096 (2 ^ 47); KRange (EVar 35) 4096 (2 ^ 47); KAlign (EVar 34) 16; KAlign (EVar 35) 16; KDisj (SA (EVar 35) 0) 64 (SA (EVar 34) 0) 64; KDisj (SA (EVar 32) (-16)) 16 (SA (EVar 34) 0) 64; KWord (SA (EVar 35) 32) 4 (ELit 0)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKw HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixd; pixs; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKw HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C Ar s m0 M0).
  { subst M0. apply (exW_win_blks C A0 Ar m0 _ E0 log0 (EVar 32) s 16 [(EVar 34, pixd, 64%Z)] CK HW0 SUBr Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRpixd (conj Lpixd_a0 (conj Fpixd F0pixd))))|]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BSF := [(32%nat, s); (34%nat, pixd); (35%nat, pixs)]).
  exW_regfactB BSF HR ex_r10 G10.
  assert (PXd' : PIXat M0 pixd vd).
  { subst M0 log0. cbn [mem_denot]. unfold adenot. cbn [a_base a_off]. change (edenot E0 (EVar 34)) with (Z_to_bv 64 pixd). rewrite zbv_addi. change (edenot E0 (ELit 0)) with (Z_to_bv 64 0). pose proof (PIX_wr_fmt m0 pixd vd 0 PXd ltac:(lia)) as X. rewrite (set_fmt_0 vd HP1) in X. exact X. }
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  apply (HC M0 RcF HWs0).
  - lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end.
  - exact PMs0.
  - exact PXd'.
  - exact G10.
Qed.
End Chain.
End V15LeptThrLeaf.
