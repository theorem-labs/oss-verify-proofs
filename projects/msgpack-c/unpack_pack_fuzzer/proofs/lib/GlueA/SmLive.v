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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AInstanceUF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase StepSoundMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CtrPre GlueA CtrFrame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require SmLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB SmShape SmWorld SmPost.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX.
Import ActrA.
Module UF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AInstanceUF.

Lemma frame_status_live : forall segs st l, ActrB.frame_status segs st l = ActrB.FLive ->
  exists kf rf rs, l = VP kf wzero /\ IMap.find kf (s_regs st) = Some rf
    /\ can_read segs (s_facts st) (s_priv st) kf rf 24%uint63 8%uint63 = true
    /\ region_load segs kf rf 24%uint63 8%uint63 false = Some rs
    /\ decide_ltu (s_facts st) rs (getr st X2) = Some false.
Proof.
  intros segs st l H. unfold ActrB.frame_status in H.
  destruct l as [|kf z| | | | | | | | |]; try discriminate H.
  destruct (weqb z wzero) eqn:Z0; [|discriminate H]. apply weqb_ok in Z0. subst z.
  destruct (IMap.find kf (s_regs st)) as [rf|] eqn:FR; [|discriminate H].
  destruct (can_read segs (s_facts st) (s_priv st) kf rf 24%uint63 8%uint63) eqn:CR; [|discriminate H].
  destruct (region_load segs kf rf 24%uint63 8%uint63 false) as [rs|] eqn:RL; [|discriminate H].
  destruct (decide_ltu (s_facts st) rs (getr st X2)) as [[|]|] eqn:DL; try discriminate H.
  exists kf, rf, rs. auto.
Qed.

Lemma frames_all_live_In : forall segs E st n ws wl, CtrA.nonstack_windows n ws = Some wl ->
  ActrB.frames_all_live segs n (firstn (3 * n) ws) st = true ->
  forall w, In w (wins_of E n ws) -> w_kind w = K_FRAMEz ->
  exists l, w_lo w = bv_unsigned (den E l) /\ ActrB.frame_status segs st l = ActrB.FLive.
Proof.
  intros segs E st n. induction n as [|n IH]; intros ws wl NW FL w Hw K; [destruct Hw|].
  destruct ws as [|lo [|len [|kd ws']]]; try (cbn in NW; discriminate NW).
  replace (3 * S n)%nat with (S (S (S (3 * n)))) in FL by lia. cbn [firstn ActrB.frames_all_live] in FL.
  cbn [CtrA.nonstack_windows] in NW. destruct kd as [kw| | | | | | | | | |]; try discriminate NW.
  destruct (CtrA.nonstack_windows n ws') as [l0|] eqn:NW'; [|discriminate NW].
  apply andb_prop in FL as [FL1 FL2]. rewrite wins_of_cons in Hw. destruct Hw as [<-|Hw].
  - cbn [w_kind w_lo] in K |- *. exists lo. split; [reflexivity|].
    assert (KF : sv_eqb (VL kw) (VL ActrB.K_FRAME) = true).
    { cbn [sv_eqb]. rewrite weqb_eqb. apply Z.eqb_eq. cbn [den] in K. rewrite wbv_unsigned in K. rewrite K. reflexivity. }
    rewrite KF in FL1. destruct (ActrB.frame_status segs st lo); try discriminate FL1. reflexivity.
  - exact (IH ws' l0 NW' FL2 w Hw K).
Qed.

Section Live.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.

Lemma frame_rs_bytes : forall E st ms mo kf rf rs, st_ok asegs OPS E st ms mo ->
  IMap.find kf (s_regs st) = Some rf -> can_read asegs (s_facts st) (s_priv st) kf rf 24%uint63 8%uint63 = true ->
  region_load asegs kf rf 24%uint63 8%uint63 false = Some rs ->
  0 <= bv_unsigned (ev E kf) + 24 -> bv_unsigned (ev E kf) + 32 <= 2 ^ 64 ->
  ALib.Mem.bytes_at asegs (ms_mem ms) (bv_unsigned (ev E kf) + 24) (ALib.Mem.le8 (den E rs)).
Proof.
  intros E st ms mo kf rf rs HS FR CR RL LO HI.
  pose proof (so_reg _ _ _ _ _ _ HS _ _ FR) as RO.
  destruct (MemP.region_load_sound asegs (s_priv st) E (ms_mem ms) (s_facts st) kf rf 24%uint63 8%uint63 false rs
              (so_facts _ _ _ _ _ _ HS) (so_zero _ _ _ _ _ _ HS) RO ltac:(right; right; right; reflexivity) CR RL) as (bs & LEN & OV & DEN).
  change (Z.to_nat (to_Z 8%uint63)) with 8%nat in LEN, OV. unfold addrZ in OV. change (keyZ 24%uint63) with 24 in OV.
  destruct (SmLib.ov_read_bytes_inv asegs (ms_mem ms) _ 8 bs OV LO ltac:(unfold two64; lia)) as [_ RB].
  assert (EBS : bs = ALib.Mem.le8 (den E rs)).
  { rewrite <- (SmLib.stored_is_loaded 8%uint63 (den E rs) bs ltac:(right; reflexivity) LEN).
    - rewrite <- StepM.store_bytes_64. apply ALib.Step.store_bytes_8'.
    - rewrite DEN. apply StepM.bytes_val_ext_word; [exact LEN| change (to_Z 8%uint63) with 8; lia]. }
  rewrite <- EBS. split; [exact LO|]. split; [rewrite LEN; lia|]. intros i Hi. rewrite LEN in Hi.
  change (ALib.Mem.mrd asegs (ms_mem ms) (ALib.Mem.wa (bv_unsigned (ev E kf) + 24 + Z.of_nat i))) with (rb asegs (ms_mem ms) (bv_unsigned (ev E kf) + 24 + Z.of_nat i)).
  rewrite (RB (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
Qed.

Theorem frames_live : forall E st ms mo cls hargs (L : alayout) (RNG : footprint) (sta : astate) (LBa LBk : list ablock),
  st_ok asegs OPS E st ms mo ->
  find_op HEAP_ID (s_ops st) = Some hargs -> ActrB.frames_pre asegs st hargs cls = true ->
  (forall b, In b LBa -> UF.fk_live L (ms_mem ms) (AP.getr (ms_regs ms) 2%bv) b -> In b LBk) ->
  live_stmt AI ACCT UNIV E st ms L RNG sta LBa LBk.
Proof.
  intros E st ms mo cls hargs L RNG sta LBa LBk HS FO FP KEEP2d W nn rest wnl aw LB mo0 WOF ARW TI (md & A & nw & FO' & Tnw & Nn & Ln) NW b Vb.
  rewrite FO in FO'. injection FO' as ->.
  assert (HN : heap_nwin (VL md :: A :: VL nw :: rest) = Some nn).
  { unfold heap_nwin. rewrite Tnw, <- Nn. destruct (Nat.leb_spec (3 * nn) (length rest)); [reflexivity| lia]. }
  unfold ActrB.frames_pre in FP. rewrite HN in FP.
  destruct WOF as (E1 & E2 & E3 & E4). apply KEEP2d; [rewrite <- E4; exact (proj1 Vb)|].
  destruct (kind_cases b) as [[p Hp]|HF].
  - destruct b as [kk aa n0]. cbn [ab_kind] in Hp. subst kk. apply UF.fk_live_heap.
  - destruct TI as (_ & _ & T3 & _). destruct (T3 b (conj Vb HF)) as [INF _].
    destruct (frames_all_live_In asegs E st nn rest wnl NW FP _ INF eq_refl) as (l & LO & FSL). cbn [w_lo] in LO.
    destruct (frame_status_live asegs st l FSL) as (kf & rf & rs & -> & FR & CR & RL & DL).
    rewrite HeapCtr.den_VPz in LO.
    destruct ARW as [HWW EMW]. pose proof HWW as (AH & _).
    destruct (blk_facts AI AI_fake _ _ _ _ _ b AH (proj1 Vb)) as (NP & BK & TOP & _). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
    pose proof (frame_rs_bytes E st ms mo kf rf rs HS FR CR RL ltac:(rewrite <- LO; lia) ltac:(rewrite <- LO; lia)) as BA. rewrite <- LO in BA.
    destruct b as [[p|c] Fb nb]; [destruct HF as [c' X]; discriminate X|]. cbn [ab_addr ab_size] in *.
    apply (UF.fk_live_of_rs L (ms_mem ms) (AP.getr (ms_regs ms) 2%bv) c Fb nb (den E rs) BA ltac:(lia)).
    pose proof (ValP.decide_ltu_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) rs (getr st X2) false DL) as X.
    apply (proj1 (ValP.ltu_iff _ _ false)) in X. rewrite (CtrFrame.SP_den OPS E st ms mo HS) in X. exact X.
Qed.
End Live.

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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import ActrB.TwinB SmShape.TwinB SmWorld.TwinB SmPost.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX.
Import ActrA.
Module UF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AInstanceUF.TwinB.

Lemma frame_status_live : forall segs st l, ActrB.TwinB.ActrB.frame_status segs st l = ActrB.TwinB.ActrB.FLive ->
  exists kf rf rs, l = VP kf wzero /\ IMap.find kf (s_regs st) = Some rf
    /\ can_read segs (s_facts st) (s_priv st) kf rf 24%uint63 8%uint63 = true
    /\ region_load segs kf rf 24%uint63 8%uint63 false = Some rs
    /\ decide_ltu (s_facts st) rs (getr st X2) = Some false.
Proof.
  intros segs st l H. unfold ActrB.TwinB.ActrB.frame_status in H.
  destruct l as [|kf z| | | | | | | | |]; try discriminate H.
  destruct (weqb z wzero) eqn:Z0; [|discriminate H]. apply weqb_ok in Z0. subst z.
  destruct (IMap.find kf (s_regs st)) as [rf|] eqn:FR; [|discriminate H].
  destruct (can_read segs (s_facts st) (s_priv st) kf rf 24%uint63 8%uint63) eqn:CR; [|discriminate H].
  destruct (region_load segs kf rf 24%uint63 8%uint63 false) as [rs|] eqn:RL; [|discriminate H].
  destruct (decide_ltu (s_facts st) rs (getr st X2)) as [[|]|] eqn:DL; try discriminate H.
  exists kf, rf, rs. auto.
Qed.

Lemma frames_all_live_In : forall segs E st n ws wl, CtrA.nonstack_windows n ws = Some wl ->
  ActrB.TwinB.ActrB.frames_all_live segs n (firstn (3 * n) ws) st = true ->
  forall w, In w (wins_of E n ws) -> w_kind w = K_FRAMEz ->
  exists l, w_lo w = bv_unsigned (den E l) /\ ActrB.TwinB.ActrB.frame_status segs st l = ActrB.TwinB.ActrB.FLive.
Proof.
  intros segs E st n. induction n as [|n IH]; intros ws wl NW FL w Hw K; [destruct Hw|].
  destruct ws as [|lo [|len [|kd ws']]]; try (cbn in NW; discriminate NW).
  replace (3 * S n)%nat with (S (S (S (3 * n)))) in FL by lia. cbn [firstn ActrB.TwinB.ActrB.frames_all_live] in FL.
  cbn [CtrA.nonstack_windows] in NW. destruct kd as [kw| | | | | | | | | |]; try discriminate NW.
  destruct (CtrA.nonstack_windows n ws') as [l0|] eqn:NW'; [|discriminate NW].
  apply andb_prop in FL as [FL1 FL2]. rewrite wins_of_cons in Hw. destruct Hw as [<-|Hw].
  - cbn [w_kind w_lo] in K |- *. exists lo. split; [reflexivity|].
    assert (KF : sv_eqb (VL kw) (VL ActrB.TwinB.ActrB.K_FRAME) = true).
    { cbn [sv_eqb]. rewrite weqb_eqb. apply Z.eqb_eq. cbn [den] in K. rewrite wbv_unsigned in K. rewrite K. reflexivity. }
    rewrite KF in FL1. destruct (ActrB.TwinB.ActrB.frame_status segs st lo); try discriminate FL1. reflexivity.
  - exact (IH ws' l0 NW' FL2 w Hw K).
Qed.

Section Live.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.

Lemma frame_rs_bytes : forall E st ms mo kf rf rs, st_ok bsegs OPS E st ms mo ->
  IMap.find kf (s_regs st) = Some rf -> can_read bsegs (s_facts st) (s_priv st) kf rf 24%uint63 8%uint63 = true ->
  region_load bsegs kf rf 24%uint63 8%uint63 false = Some rs ->
  0 <= bv_unsigned (ev E kf) + 24 -> bv_unsigned (ev E kf) + 32 <= 2 ^ 64 ->
  ALib.Mem.bytes_at bsegs (ms_mem ms) (bv_unsigned (ev E kf) + 24) (ALib.Mem.le8 (den E rs)).
Proof.
  intros E st ms mo kf rf rs HS FR CR RL LO HI.
  pose proof (so_reg _ _ _ _ _ _ HS _ _ FR) as RO.
  destruct (MemP.region_load_sound bsegs (s_priv st) E (ms_mem ms) (s_facts st) kf rf 24%uint63 8%uint63 false rs
              (so_facts _ _ _ _ _ _ HS) (so_zero _ _ _ _ _ _ HS) RO ltac:(right; right; right; reflexivity) CR RL) as (bs & LEN & OV & DEN).
  change (Z.to_nat (to_Z 8%uint63)) with 8%nat in LEN, OV. unfold addrZ in OV. change (keyZ 24%uint63) with 24 in OV.
  destruct (SmLib.TwinB.ov_read_bytes_inv bsegs (ms_mem ms) _ 8 bs OV LO ltac:(unfold two64; lia)) as [_ RB].
  assert (EBS : bs = ALib.Mem.le8 (den E rs)).
  { rewrite <- (SmLib.TwinB.stored_is_loaded 8%uint63 (den E rs) bs ltac:(right; reflexivity) LEN).
    - rewrite <- StepM.store_bytes_64. apply ALib.Step.store_bytes_8'.
    - rewrite DEN. apply StepM.bytes_val_ext_word; [exact LEN| change (to_Z 8%uint63) with 8; lia]. }
  rewrite <- EBS. split; [exact LO|]. split; [rewrite LEN; lia|]. intros i Hi. rewrite LEN in Hi.
  change (ALib.Mem.mrd bsegs (ms_mem ms) (ALib.Mem.wa (bv_unsigned (ev E kf) + 24 + Z.of_nat i))) with (rb bsegs (ms_mem ms) (bv_unsigned (ev E kf) + 24 + Z.of_nat i)).
  rewrite (RB (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id. reflexivity.
Qed.

Theorem frames_live : forall E st ms mo cls hargs (L : alayout) (RNG : footprint) (sta : astate) (LBa LBk : list ablock),
  st_ok bsegs OPS E st ms mo ->
  find_op HEAP_ID (s_ops st) = Some hargs -> ActrB.TwinB.ActrB.frames_pre bsegs st hargs cls = true ->
  (forall b, In b LBa -> UF.fk_live L (ms_mem ms) (AP.getr (ms_regs ms) 2%bv) b -> In b LBk) ->
  live_stmt AI ACCT UNIV E st ms L RNG sta LBa LBk.
Proof.
  intros E st ms mo cls hargs L RNG sta LBa LBk HS FO FP KEEP2d W nn rest wnl aw LB mo0 WOF ARW TI (md & A & nw & FO' & Tnw & Nn & Ln) NW b Vb.
  rewrite FO in FO'. injection FO' as ->.
  assert (HN : heap_nwin (VL md :: A :: VL nw :: rest) = Some nn).
  { unfold heap_nwin. rewrite Tnw, <- Nn. destruct (Nat.leb_spec (3 * nn) (length rest)); [reflexivity| lia]. }
  unfold ActrB.TwinB.ActrB.frames_pre in FP. rewrite HN in FP.
  destruct WOF as (E1 & E2 & E3 & E4). apply KEEP2d; [rewrite <- E4; exact (proj1 Vb)|].
  destruct (kind_cases b) as [[p Hp]|HF].
  - destruct b as [kk aa n0]. cbn [ab_kind] in Hp. subst kk. apply UF.fk_live_heap.
  - destruct TI as (_ & _ & T3 & _). destruct (T3 b (conj Vb HF)) as [INF _].
    destruct (frames_all_live_In bsegs E st nn rest wnl NW FP _ INF eq_refl) as (l & LO & FSL). cbn [w_lo] in LO.
    destruct (frame_status_live bsegs st l FSL) as (kf & rf & rs & -> & FR & CR & RL & DL).
    rewrite HeapCtr.TwinB.den_VPz in LO.
    destruct ARW as [HWW EMW]. pose proof HWW as (AH & _).
    destruct (blk_facts AI AI_fake _ _ _ _ _ b AH (proj1 Vb)) as (NP & BK & TOP & _). pose proof atop_range as ATR. unfold ablk, AIMG_HI, KLS in BK.
    pose proof (frame_rs_bytes E st ms mo kf rf rs HS FR CR RL ltac:(rewrite <- LO; lia) ltac:(rewrite <- LO; lia)) as BA. rewrite <- LO in BA.
    destruct b as [[p|c] Fb nb]; [destruct HF as [c' X]; discriminate X|]. cbn [ab_addr ab_size] in *.
    apply (UF.fk_live_of_rs L (ms_mem ms) (AP.getr (ms_regs ms) 2%bv) c Fb nb (den E rs) BA ltac:(lia)).
    pose proof (ValP.decide_ltu_sound E (s_facts st) (so_facts _ _ _ _ _ _ HS) rs (getr st X2) false DL) as X.
    apply (proj1 (ValP.ltu_iff _ _ false)) in X. rewrite (CtrFrame.TwinB.SP_den OPS E st ms mo HS) in X. exact X.
Qed.
End Live.
End TwinB.
