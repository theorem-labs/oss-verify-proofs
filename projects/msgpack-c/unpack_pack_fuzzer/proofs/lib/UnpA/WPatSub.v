(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require W64Proofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CtrPre CtrPat ShLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Seal Model Inv Ops OpsLaws TdOps PkOps ClientX.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Module WPatSub.
Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : FX.State.St.optable.
Hypothesis AI_fake : AI_fake_law AI.

Hypothesis Cw_zone_sealed : forall md ca LB ws m w a, cw_holds Cw md ca LB ws m -> In w ws ->
  (w_kind w = 4 \/ w_kind w = 5) -> in_iv (w_iv w) a -> OpsLaws.UOL.zone_sealed LB ws a.

Theorem w_pat_sub_zone : forall E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb,
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  CtrA.win_lookup wnl kd = Some (wlen, kind) -> (W64.w2Z kind = 4 \/ W64.w2Z kind = 5) ->
  forall lo hi, 0 <= lo -> lo < hi -> hi <= bv_unsigned (Val.den E wlen) ->
  In (HB p A nb) LBa -> A <= bv_unsigned (Val.ev E kd) + lo -> bv_unsigned (Val.ev E kd) + hi <= A + nb ->
  ablock_shadow (ms_mem ms) A nb.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb CF WL K45 lo hi L0 LH HW HIN BA1 BA2.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & Asv & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtrB.nonstack_windows_In E nn rest wnl kd wlen kind NW (HeapCtrB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
  set (w := Win (bv_unsigned (Val.ev E kd)) (bv_unsigned (Val.den E wlen)) (W64.w2Z kind)) in *.
  set (a := bv_unsigned (Val.ev E kd) + lo).
  assert (IA : in_iv (w_iv w) a) by (unfold in_iv, w_iv, a; cbn [fst snd w_lo w_len w]; lia).
  destruct (Cw_zone_sealed _ _ _ _ _ w a HC INW K45 IA) as (cs & c & [SEAL S8] & Hcc & HLB & INC & APART).
  destruct ARW as [HWW EMW]. destruct WOF as (E1 & E2 & E3 & E4).
  pose proof TI as (T1 & T2 & T3 & _).
  pose proof HWW as (AH & HT & _).
  set (v := Inv.chunk_block c) in *.

  destruct (LB_cases AI ACCT UNIV W aw LB (ms_mem ms) mo v HWW HLB) as [(b & Vb & Ev)|[(b & Hb & Ev)|(b & Vb & Ev)]].
  2:{ exfalso. pose proof (T1 b Hb) as WIN. apply (APART _ WIN ltac:(right; unfold K_GHOST, K_TWINz; cbn; lia) a); [| exact INC].
      unfold w_iv. cbn [w_lo w_len]. fold (twin_iv b). rewrite <- Ev. exact INC. }
  2:{ exfalso. destruct (T3 b Vb) as [_ WIN]. apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FTWINz; cbn; lia) a); [| exact INC].
      unfold w_iv. cbn [w_lo w_len]. fold (fsh_iv b). rewrite <- Ev. exact INC. }
  destruct (kind_cases b) as [HH|HF].
  2:{ exfalso. destruct (T3 b (conj Vb HF)) as [WIN _].
      destruct (blk_facts AI AI_fake _ _ _ _ _ b AH (proj1 Vb)) as (NP & _).
      destruct (AI_fake _ _ _ _ _ b AH (proj1 Vb) HF) as (_ & _ & _ & _ & N64 & _).
      apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FRAMEz; cbn; lia) (ab_addr b)).
      - unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. lia.
      - rewrite Ev. unfold in_iv, user_iv. cbn [fst snd]. rewrite (usz_fake b HF). lia. }
  assert (NT : ~ In b (w_T W)).
  { intros HbT. pose proof (T1 b HbT) as WIN. apply (SEAL _ WIN eq_refl c Hcc). cbn [w_lo]. rewrite ShLaw.shadZ_shad.
    replace (fst c) with (fst v) by reflexivity. rewrite Ev. reflexivity. }

  assert (EV1 : fst v = ab_addr b /\ snd v = ab_size b) by (rewrite Ev; unfold user_iv; cbn [fst snd]; rewrite (usz_heap b HH); split; reflexivity).
  destruct EV1 as [EA ES]. unfold in_iv in INC. rewrite EA, ES in INC.
  set (b1 := HB p A nb) in *.
  assert (AHm : AHEAP AI L RNG sta LBa (ms_mem ms)) by (rewrite <- E1, <- E2, <- E3, <- E4, <- EMW; exact AH).
  assert (HbL : In b LBa) by (rewrite <- E4; exact (proj1 Vb)).
  destruct (ablock_eq_dec b1 b) as [EQ|NE].
  - pose proof (CtrPat.aw_pat_in AI ACCT UNIV AI_fake W aw LB (ms_mem ms) mo b HWW Vb HH NT) as PAT. rewrite <- EQ in PAT. exact PAT.
  - exfalso. pose proof (AI_blocks_disjoint AI L RNG sta LBa (ms_mem ms) b1 b AHm HIN HbL NE) as D.
    unfold b1 in D. cbn [ab_addr ab_size] in D. unfold a in INC. lia.
Qed.

Corollary w_pat_sub_zone_b : forall E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb,
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  CtrA.win_lookup wnl kd = Some (wlen, kind) ->
  (W64.weqb kind (W64.wlit 4%uint63) || W64.weqb kind (W64.wlit 5%uint63))%bool = true ->
  forall lo hi, 0 <= lo -> lo < hi -> hi <= bv_unsigned (Val.den E wlen) ->
  In (HB p A nb) LBa -> A <= bv_unsigned (Val.ev E kd) + lo -> bv_unsigned (Val.ev E kd) + hi <= A + nb ->
  ablock_shadow (ms_mem ms) A nb.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb CF WL KB.
  apply (w_pat_sub_zone E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb CF WL).
  apply orb_prop in KB as [KB|KB]; apply W64Proofs.weqb_w2Z in KB; [left| right]; exact KB.
Qed.
End Sound.

Section Inst.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable segs : list Segment.
Hypothesis AI_fake : AI_fake_law AI.

Lemma xtp_no_zone : forall md ca LB ws m w, cw_holds (ClientX.CX.XTP segs) md ca LB ws m -> In w ws ->
  (w_kind w = Ops.UO.K_SLOT \/ w_kind w = Ops.UO.K_ZONE) -> False.
Proof.
  intros md ca LB ws m w H Hw KW. cbn [cw_holds ClientX.CX.XTP] in H. unfold ClientX.CX.x_holds in H.
  destruct (md =? TdOps.TD.CM_TD).
  - destruct H as [_ NS]. apply (proj1 (Forall_forall _ _) NS w Hw). unfold K_SUB, K_GHOST, Ops.UO.K_SLOT, Ops.UO.K_ZONE in *. lia.
  - destruct (md =? PkOps.PK.CM_PK); [| exact H].
    unfold PkOps.PK.cw_pk_holds in H. destruct (PkOps.PK.decode_pk ca) as [u|]; [| exact H].
    destruct H as (gg & ls & _ & _ & _ & Wk & _). unfold PkOps.PK.wins_pk in Wk.
    destruct (proj1 (Forall_forall _ _) Wk w Hw ltac:(unfold K_STACK, Ops.UO.K_SLOT, Ops.UO.K_ZONE in *; lia)) as [[[KB|KG] _]|[_ (K6 & _)]];
      unfold K_BLOCK, K_GHOST, PkOps.PK.K_ETOP, Ops.UO.K_SLOT, Ops.UO.K_ZONE in *; lia.
Qed.

Theorem w_pat_sub_unp : forall E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb,
  CtrPre.acallG AI ACCT UNIV (Ops.UO.unp_cw segs (ClientX.CX.XTP segs)) E st ms mo r hargs wnl L RNG sta LBa aw ->
  CtrA.win_lookup wnl kd = Some (wlen, kind) ->
  (W64.weqb kind (W64.wlit 4%uint63) || W64.weqb kind (W64.wlit 5%uint63))%bool = true ->
  forall lo hi, 0 <= lo -> lo < hi -> hi <= bv_unsigned (Val.den E wlen) ->
  In (HB p A nb) LBa -> A <= bv_unsigned (Val.ev E kd) + lo -> bv_unsigned (Val.ev E kd) + hi <= A + nb ->
  ablock_shadow (ms_mem ms) A nb.
Proof.
  apply (w_pat_sub_zone_b AI ACCT UNIV (Ops.UO.unp_cw segs (ClientX.CX.XTP segs)) AI_fake).
  intros md ca LB ws m w a H Hw KW Ia.
  exact (OpsLaws.UOL.cw_zone_sealed segs (ClientX.CX.XTP segs) xtp_no_zone md ca LB ws m w a H Hw KW Ia).
Qed.
End Inst.
End WPatSub.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Actr.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Module WPatSub.
Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : FX.State.St.optable.
Hypothesis AI_fake : AI_fake_law AI.

Hypothesis Cw_zone_sealed : forall md ca LB ws m w a, cw_holds Cw md ca LB ws m -> In w ws ->
  (w_kind w = 4 \/ w_kind w = 5) -> in_iv (w_iv w) a -> OpsLaws.UOL.zone_sealed LB ws a.

Theorem w_pat_sub_zone : forall E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb,
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  CtrA.win_lookup wnl kd = Some (wlen, kind) -> (W64.w2Z kind = 4 \/ W64.w2Z kind = 5) ->
  forall lo hi, 0 <= lo -> lo < hi -> hi <= bv_unsigned (Val.den E wlen) ->
  In (HB p A nb) LBa -> A <= bv_unsigned (Val.ev E kd) + lo -> bv_unsigned (Val.ev E kd) + hi <= A + nb ->
  ablock_shadow (ms_mem ms) A nb.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb CF WL K45 lo hi L0 LH HW HIN BA1 BA2.
  destruct CF as (LB & ks & offs & rss & ksp & nn & md & Asv & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                  & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl kd wlen kind NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL)) as (_ & _ & KD & INW).
  set (w := Win (bv_unsigned (Val.ev E kd)) (bv_unsigned (Val.den E wlen)) (W64.w2Z kind)) in *.
  set (a := bv_unsigned (Val.ev E kd) + lo).
  assert (IA : in_iv (w_iv w) a) by (unfold in_iv, w_iv, a; cbn [fst snd w_lo w_len w]; lia).
  destruct (Cw_zone_sealed _ _ _ _ _ w a HC INW K45 IA) as (cs & c & [SEAL S8] & Hcc & HLB & INC & APART).
  destruct ARW as [HWW EMW]. destruct WOF as (E1 & E2 & E3 & E4).
  pose proof TI as (T1 & T2 & T3 & _).
  pose proof HWW as (AH & HT & _).
  set (v := Inv.chunk_block c) in *.

  destruct (LB_cases AI ACCT UNIV W aw LB (ms_mem ms) mo v HWW HLB) as [(b & Vb & Ev)|[(b & Hb & Ev)|(b & Vb & Ev)]].
  2:{ exfalso. pose proof (T1 b Hb) as WIN. apply (APART _ WIN ltac:(right; unfold K_GHOST, K_TWINz; cbn; lia) a); [| exact INC].
      unfold w_iv. cbn [w_lo w_len]. fold (twin_iv b). rewrite <- Ev. exact INC. }
  2:{ exfalso. destruct (T3 b Vb) as [_ WIN]. apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FTWINz; cbn; lia) a); [| exact INC].
      unfold w_iv. cbn [w_lo w_len]. fold (fsh_iv b). rewrite <- Ev. exact INC. }
  destruct (kind_cases b) as [HH|HF].
  2:{ exfalso. destruct (T3 b (conj Vb HF)) as [WIN _].
      destruct (blk_facts AI AI_fake _ _ _ _ _ b AH (proj1 Vb)) as (NP & _).
      destruct (AI_fake _ _ _ _ _ b AH (proj1 Vb) HF) as (_ & _ & _ & _ & N64 & _).
      apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FRAMEz; cbn; lia) (ab_addr b)).
      - unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. lia.
      - rewrite Ev. unfold in_iv, user_iv. cbn [fst snd]. rewrite (usz_fake b HF). lia. }
  assert (NT : ~ In b (w_T W)).
  { intros HbT. pose proof (T1 b HbT) as WIN. apply (SEAL _ WIN eq_refl c Hcc). cbn [w_lo]. rewrite ShLaw.TwinB.shadZ_shad.
    replace (fst c) with (fst v) by reflexivity. rewrite Ev. reflexivity. }

  assert (EV1 : fst v = ab_addr b /\ snd v = ab_size b) by (rewrite Ev; unfold user_iv; cbn [fst snd]; rewrite (usz_heap b HH); split; reflexivity).
  destruct EV1 as [EA ES]. unfold in_iv in INC. rewrite EA, ES in INC.
  set (b1 := HB p A nb) in *.
  assert (AHm : AHEAP AI L RNG sta LBa (ms_mem ms)) by (rewrite <- E1, <- E2, <- E3, <- E4, <- EMW; exact AH).
  assert (HbL : In b LBa) by (rewrite <- E4; exact (proj1 Vb)).
  destruct (ablock_eq_dec b1 b) as [EQ|NE].
  - pose proof (CtrPat.TwinB.aw_pat_in AI ACCT UNIV AI_fake W aw LB (ms_mem ms) mo b HWW Vb HH NT) as PAT. rewrite <- EQ in PAT. exact PAT.
  - exfalso. pose proof (AI_blocks_disjoint AI L RNG sta LBa (ms_mem ms) b1 b AHm HIN HbL NE) as D.
    unfold b1 in D. cbn [ab_addr ab_size] in D. unfold a in INC. lia.
Qed.

Corollary w_pat_sub_zone_b : forall E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb,
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw ->
  CtrA.win_lookup wnl kd = Some (wlen, kind) ->
  (W64.weqb kind (W64.wlit 4%uint63) || W64.weqb kind (W64.wlit 5%uint63))%bool = true ->
  forall lo hi, 0 <= lo -> lo < hi -> hi <= bv_unsigned (Val.den E wlen) ->
  In (HB p A nb) LBa -> A <= bv_unsigned (Val.ev E kd) + lo -> bv_unsigned (Val.ev E kd) + hi <= A + nb ->
  ablock_shadow (ms_mem ms) A nb.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb CF WL KB.
  apply (w_pat_sub_zone E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb CF WL).
  apply orb_prop in KB as [KB|KB]; apply W64Proofs.weqb_w2Z in KB; [left| right]; exact KB.
Qed.
End Sound.

Section Inst.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable segs : list Segment.
Hypothesis AI_fake : AI_fake_law AI.

Lemma xtp_no_zone : forall md ca LB ws m w, cw_holds (ClientX.CX.XTP segs) md ca LB ws m -> In w ws ->
  (w_kind w = Ops.UO.K_SLOT \/ w_kind w = Ops.UO.K_ZONE) -> False.
Proof.
  intros md ca LB ws m w H Hw KW. cbn [cw_holds ClientX.CX.XTP] in H. unfold ClientX.CX.x_holds in H.
  destruct (md =? TdOps.TD.CM_TD).
  - destruct H as [_ NS]. apply (proj1 (Forall_forall _ _) NS w Hw). unfold K_SUB, K_GHOST, Ops.UO.K_SLOT, Ops.UO.K_ZONE in *. lia.
  - destruct (md =? PkOps.PK.CM_PK); [| exact H].
    unfold PkOps.PK.cw_pk_holds in H. destruct (PkOps.PK.decode_pk ca) as [u|]; [| exact H].
    destruct H as (gg & ls & _ & _ & _ & Wk & _). unfold PkOps.PK.wins_pk in Wk.
    destruct (proj1 (Forall_forall _ _) Wk w Hw ltac:(unfold K_STACK, Ops.UO.K_SLOT, Ops.UO.K_ZONE in *; lia)) as [[[KB|KG] _]|[_ (K6 & _)]];
      unfold K_BLOCK, K_GHOST, PkOps.PK.K_ETOP, Ops.UO.K_SLOT, Ops.UO.K_ZONE in *; lia.
Qed.

Theorem w_pat_sub_unp : forall E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb,
  CtrPre.TwinB.acallG AI ACCT UNIV (Ops.UO.unp_cw segs (ClientX.CX.XTP segs)) E st ms mo r hargs wnl L RNG sta LBa aw ->
  CtrA.win_lookup wnl kd = Some (wlen, kind) ->
  (W64.weqb kind (W64.wlit 4%uint63) || W64.weqb kind (W64.wlit 5%uint63))%bool = true ->
  forall lo hi, 0 <= lo -> lo < hi -> hi <= bv_unsigned (Val.den E wlen) ->
  In (HB p A nb) LBa -> A <= bv_unsigned (Val.ev E kd) + lo -> bv_unsigned (Val.ev E kd) + hi <= A + nb ->
  ablock_shadow (ms_mem ms) A nb.
Proof.
  apply (w_pat_sub_zone_b AI ACCT UNIV (Ops.UO.unp_cw segs (ClientX.CX.XTP segs)) AI_fake).
  intros md ca LB ws m w a H Hw KW Ia.
  exact (OpsLaws.UOL.cw_zone_sealed segs (ClientX.CX.XTP segs) xtp_no_zone md ca LB ws m w a H Hw KW Ia).
Qed.
End Inst.
End WPatSub.
End TwinB.
