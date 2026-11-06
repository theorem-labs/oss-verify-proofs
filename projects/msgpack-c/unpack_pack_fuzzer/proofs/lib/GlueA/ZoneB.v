(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_asan_memcpy.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA DefsB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB MemFX RstageCtr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV GlueA CtrPre CtrFrame CtrNoDelta CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggGeo UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ReadC ReadPre MemOps RstageC MemsetFX RangePre MemsetPre MemsetPost RegRepl RstageSound RstagePost.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPost.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA RstageC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.I_memcpy.

Section ZoneG.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok asegs OPS E st ms mo.
Variables (r : int) (hargs : list sv) (wnl : list (int * sv * w64)) (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word).
Hypothesis CF : CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw.
Variables (kb : int) (wlen : sv).
Hypothesis WL : CtrA.win_lookup wnl kb = Some (wlen, CtrLib.K_BLOCK).
Let Db := bv_unsigned (ev E kb).
Let wlenZ := bv_unsigned (den E wlen).
Hypothesis OWIN : forall k len kd, CtrA.win_lookup wnl k = Some (len, kd) -> k <> kb ->
  forall x, bv_unsigned (ev E k) <= x < bv_unsigned (ev E k) + bv_unsigned (den E len) -> ~ (Db <= x < Db + wlenZ).

Lemma zone_regions_g : forall a, Db <= a < Db + wlenZ -> uband a ->
  forall k2 r2, IMap.find k2 (s_regs st) = Some r2 -> k2 <> kb -> PrimInt63.eqb k2 0%uint63 = false ->
  ~ (bv_unsigned (ev E k2) + loZ r2 <= a < bv_unsigned (ev E k2) + hiZ E r2).
Proof.
  intros a INB UB k2 r2 Hk2 NK K20 RG. pose proof atop_range as ATR.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  assert (KN0 : k2 <> 0%uint63) by (intros ->; discriminate K20).
  pose proof ARW as [HWW _].

  assert (TWB : forall k len, CtrA.win_lookup wnl k = Some (len, K_TWIN) ->
            forall x, bv_unsigned (ev E k) <= x < bv_unsigned (ev E k) + bv_unsigned (den E len) -> ~ uband x).
  { intros k len WLk x Hx U. pose proof (HeapCtrB.win_lookup_In _ _ _ _ WLk) as Ik.
    destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k len K_TWIN NW Ik) as (_ & _ & _ & INW).
    destruct TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as E1 E2.
    destruct (LB_twin_facts AI ACCT UNIV W _ LB (ms_mem ms) mo b HWW HbT) as (T1 & T2' & _).
    unfold uband, AIMG_HI, KLS in U. rewrite E1, E2 in Hx. lia. }
  destruct (CallA.aregion_just_sound asegs OPS E st ms mo wnl ks offs rss k2 r2 HS SPR AJ Hk2 KN0) as [[EQ TOPk]|[NE [(len0 & kd0 & WLS & LZ & HZ)|[[J1 J2]|VJ]]]].
  - subst k2. destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). rewrite Hrs in Hk2. injection Hk2 as <-.
    unfold uband, AIMG_HI, KLS in UB. lia.
  - apply (OWIN k2 len0 kd0 WLS NK a); [rewrite LZ in RG; lia| exact INB].
  - rewrite (CtrFrame.SP_den OPS E st ms mo HS) in J1. unfold uband, AIMG_HI, KLS in UB.
    assert (SPF : ATOP + 4096 <= bv_unsigned (AP.getr (ms_regs ms) 2%bv)) by (rewrite SPE; lia). lia.
  -
    destruct VJ as [VJ|SL]; [| exfalso; pose proof (CtrPre.sliver_low OPS E st ms mo ks offs rss k2 r2 hargs nn md A nw rest LB a HS SPR Hk2 KN0 NE SL Hf Eh Tnw Nn Ln WF RG) as SLO; unfold uband, AIMG_HI, KLS in UB; lia].
    pose proof (CallV.view_just_sound asegs OPS E st ms mo wnl ks offs rss k2 r2 HS SPR Hk2 KN0 VJ) as VS. unfold CallV.view_sem in VS. cbv zeta in VS.
    destruct VS as [(_ & blo & bhi & SHZ & BH & BL)|[(hs & n0 & sh & len1 & ZV & BT & _ & WLs & V1 & V2)|[(VI & v & Hv & V1 & V2)|(shD & kbD & nD & lenD & WLD & BTD & WLkD & STD & TND & ROD & LOD & HID)]]].
    + destruct (SHZ a RG) as (a' & Ha' & ->).
      assert (A0 : 0 <= a').
      { destruct BL as [(wlo & _ & ->)|[(rs & Frs & ->)|BL]].
        - pose proof (bv_unsigned_in_range 64 (den E (VP STACK_ID wlo))). lia.
        - destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). rewrite Hrs in Frs. injection Frs as <-. lia.
        - pose proof (bv_unsigned_in_range 64 (den E (getr st X2))). lia. }
      assert (SZ : CallV.shz a' = shad a') by (unfold CallV.shz, shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; lia).
      rewrite SZ in UB. exact (shad_not_uband a' ltac:(lia) UB).
    + apply (TWB sh len1 WLs a); [lia| exact UB].
    + unfold ActrA.IMGSH in Hv. cbn [In] in Hv. destruct Hv as [<-|[]]. cbn [fst snd] in V1, V2. unfold uband, AIMG_HI, KLS in UB. lia.
    +   apply (TWB shD lenD WLD a); [lia| exact UB].
Qed.
End ZoneG.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsB.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import ReadC.TwinB ReadPre.TwinB MemOps.TwinB RstageC.TwinB MemsetFX.TwinB RangePre.TwinB MemsetPre.TwinB MemsetPost.TwinB RegRepl.TwinB RstageSound.TwinB RstagePost.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA RstageC.TwinB.RstageC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.TwinB.I_memcpy.

Section ZoneG.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok bsegs OPS E st ms mo.
Variables (r : int) (hargs : list sv) (wnl : list (int * sv * w64)) (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word).
Hypothesis CF : CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw.
Variables (kb : int) (wlen : sv).
Hypothesis WL : CtrA.win_lookup wnl kb = Some (wlen, CtrLib.K_BLOCK).
Let Db := bv_unsigned (ev E kb).
Let wlenZ := bv_unsigned (den E wlen).
Hypothesis OWIN : forall k len kd, CtrA.win_lookup wnl k = Some (len, kd) -> k <> kb ->
  forall x, bv_unsigned (ev E k) <= x < bv_unsigned (ev E k) + bv_unsigned (den E len) -> ~ (Db <= x < Db + wlenZ).

Lemma zone_regions_g : forall a, Db <= a < Db + wlenZ -> uband a ->
  forall k2 r2, IMap.find k2 (s_regs st) = Some r2 -> k2 <> kb -> PrimInt63.eqb k2 0%uint63 = false ->
  ~ (bv_unsigned (ev E k2) + loZ r2 <= a < bv_unsigned (ev E k2) + hiZ E r2).
Proof.
  intros a INB UB k2 r2 Hk2 NK K20 RG. pose proof atop_range as ATR.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  assert (KN0 : k2 <> 0%uint63) by (intros ->; discriminate K20).
  pose proof ARW as [HWW _].

  assert (TWB : forall k len, CtrA.win_lookup wnl k = Some (len, K_TWIN) ->
            forall x, bv_unsigned (ev E k) <= x < bv_unsigned (ev E k) + bv_unsigned (den E len) -> ~ uband x).
  { intros k len WLk x Hx U. pose proof (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLk) as Ik.
    destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k len K_TWIN NW Ik) as (_ & _ & _ & INW).
    destruct TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as E1 E2.
    destruct (LB_twin_facts AI ACCT UNIV W _ LB (ms_mem ms) mo b HWW HbT) as (T1 & T2' & _).
    unfold uband, AIMG_HI, KLS in U. rewrite E1, E2 in Hx. lia. }
  destruct (CallA.TwinB.aregion_just_sound bsegs OPS E st ms mo wnl ks offs rss k2 r2 HS SPR AJ Hk2 KN0) as [[EQ TOPk]|[NE [(len0 & kd0 & WLS & LZ & HZ)|[[J1 J2]|VJ]]]].
  - subst k2. destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). rewrite Hrs in Hk2. injection Hk2 as <-.
    unfold uband, AIMG_HI, KLS in UB. lia.
  - apply (OWIN k2 len0 kd0 WLS NK a); [rewrite LZ in RG; lia| exact INB].
  - rewrite (CtrFrame.TwinB.SP_den OPS E st ms mo HS) in J1. unfold uband, AIMG_HI, KLS in UB.
    assert (SPF : ATOP + 4096 <= bv_unsigned (AP.getr (ms_regs ms) 2%bv)) by (rewrite SPE; lia). lia.
  -
    destruct VJ as [VJ|SL]; [| exfalso; pose proof (CtrPre.TwinB.sliver_low OPS E st ms mo ks offs rss k2 r2 hargs nn md A nw rest LB a HS SPR Hk2 KN0 NE SL Hf Eh Tnw Nn Ln WF RG) as SLO; unfold uband, AIMG_HI, KLS in UB; lia].
    pose proof (CallV.TwinB.view_just_sound bsegs OPS E st ms mo wnl ks offs rss k2 r2 HS SPR Hk2 KN0 VJ) as VS. unfold CallV.TwinB.view_sem in VS. cbv zeta in VS.
    destruct VS as [(_ & blo & bhi & SHZ & BH & BL)|[(hs & n0 & sh & len1 & ZV & BT & _ & WLs & V1 & V2)|[(VI & v & Hv & V1 & V2)|(shD & kbD & nD & lenD & WLD & BTD & WLkD & STD & TND & ROD & LOD & HID)]]].
    + destruct (SHZ a RG) as (a' & Ha' & ->).
      assert (A0 : 0 <= a').
      { destruct BL as [(wlo & _ & ->)|[(rs & Frs & ->)|BL]].
        - pose proof (bv_unsigned_in_range 64 (den E (VP STACK_ID wlo))). lia.
        - destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). rewrite Hrs in Frs. injection Frs as <-. lia.
        - pose proof (bv_unsigned_in_range 64 (den E (getr st X2))). lia. }
      assert (SZ : CallV.TwinB.shz a' = shad a') by (unfold CallV.TwinB.shz, shad, ASHOFF; rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 3) with 8; lia).
      rewrite SZ in UB. exact (shad_not_uband a' ltac:(lia) UB).
    + apply (TWB sh len1 WLs a); [lia| exact UB].
    + unfold ActrA.IMGSH in Hv. cbn [In] in Hv. destruct Hv as [<-|[]]. cbn [fst snd] in V1, V2. unfold uband, AIMG_HI, KLS in UB. lia.
    +   apply (TWB shD lenD WLD a); [lia| exact UB].
Qed.
End ZoneG.
End TwinB.
