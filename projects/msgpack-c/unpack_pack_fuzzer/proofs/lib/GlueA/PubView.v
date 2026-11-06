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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB MemFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA GlueA CtrPre CtrFrame CtrNoDelta CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggGeo UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import MemOps MemsetFX RangePre MemsetPost PubImg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPost.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Section Leaf.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.cov1 HEAP_ID args z.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AI L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (AM.wa a) = m (AM.wa a)) -> wmono asegs m m' -> AHEAP AI L RNG st LB m'.
Lemma HEAP_frame_v : forall args m m' mo,
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS HEAP_ID args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  wmono asegs m m' ->
  (forall a, AIMG_HI <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  op_holds OPS HEAP_ID args m mo -> op_holds OPS HEAP_ID args m' mo.
Proof.
  intros args m m' mo AG WMv DM H. apply OPS_holds1. apply OPS_holds1 in H. rewrite OPS_fp1 in AG.
  exact (heap_frameX_v AI IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.wmono_ofA asegs) AI_fake Cw args m m' mo AG WMv DM H).
Qed.

Lemma st_ok_view_ext : forall E st ms mo (m' : amem) (lo hi : Z),
  st_ok asegs OPS E st ms mo ->
  (forall a, 0 <= a < two64 -> ~ (lo <= a < hi) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
  (forall a, lo <= a < hi -> rb asegs m' a = rb asegs (ms_mem ms) a) ->
  in_pubw lo hi ->
  (forall a, lo <= a < hi -> ~ in_priv (s_priv st) a) ->
  AM.mem_inv asegs m' ->
  st_ok asegs OPS E st (ms_with_mem ms m') mo.
Proof.
  intros E st ms mo m' lo hi HS OUT INV PW NPRIV MINV. pose proof (in_pubw_bounds _ _ PW) as [HLO HHI].
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (RB : forall a, 0 <= a < two64 -> rb asegs m' a = rb asegs (ms_mem ms) a).
  { intros a Ha. destruct (Z_le_gt_dec lo a) as [L1|L1]; [destruct (Z_lt_ge_dec a hi) as [L2|L2]|].
    - apply INV. lia.
    - apply ReadPost.rb_ext. apply OUT; [exact Ha| lia].
    - apply ReadPost.rb_ext. apply OUT; [exact Ha| lia]. }
  assert (WB : forall a, 0 <= a < two64 -> wb asegs (ms_mem ms) a = true -> wb asegs m' a = true).
  { intros a Ha Wb. destruct (Z_le_gt_dec lo a) as [L1|L1]; [destruct (Z_lt_ge_dec a hi) as [L2|L2]|].
    - exact (proj1 (pub_window_rw m' a (in_pubw_sub lo hi a (a + 1) PW ltac:(lia) ltac:(lia)))).
    - rewrite (ReadPost.wb_ext (ms_mem ms) m' a); [exact Wb| apply OUT; [exact Ha| lia]].
    - rewrite (ReadPost.wb_ext (ms_mem ms) m' a); [exact Wb| apply OUT; [exact Ha| lia]]. }
  assert (WM : wmono asegs (ms_mem ms) m').
  { intros x Hx. pose proof (bv_unsigned_in_range 64 x) as RX. change (bv_modulus 64) with two64 in RX.
    assert (EX : AM.wa (bv_unsigned x) = x) by (unfold AM.wa; apply Z_to_bv_bv_unsigned).
    rewrite <- EX. apply (GlueA.wb_wviewA asegs). apply WB; [exact RX|]. apply (GlueA.wb_wviewA asegs). rewrite EX. exact Hx. }
  assert (DMH : forall a, AIMG_HI <= a < two64 -> ms_mem ms (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None).
  { intros a Ha H. rewrite OUT; [exact H| unfold AIMG_HI in Ha; lia| unfold AIMG_HI in *; lia]. }
  split; cbn [ms_with_mem ms_upd ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom core_of c_regs c_fregs c_pc c_fcsr c_resv] in *;
    try assumption; try reflexivity.
  - intros k r0 Hk. exact (MemFX.MemFX.region_ok_view_frame asegs _ _ (ms_mem ms) m' k r0 (Preg k r0 Hk) RB WB).
  - apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Pops o Ho) as OH.
    pose proof (proj1 (Forall_forall _ _) Papart o Ho) as AP. cbv beta in OH, AP |- *.
    assert (FPD : forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))) ->
                   ms_mem ms (Z_to_bv 64 a) = m' (Z_to_bv 64 a)).
    { intros a Ha FP. symmetry. apply OUT; [exact Ha|]. intros IN. destruct (AP a FP) as [_ PRIVa].
      destruct (pub_window_rw m' a (in_pubw_sub lo hi a (a + 1) PW ltac:(lia) ltac:(lia))) as (_ & _ & SEG). exact (NPRIV a IN (PRIVa SEG)). }
    destruct (PrimInt63.eqb (op_id o) HEAP_ID) eqn:QH.
    + apply Uint63.eqb_correct in QH. rewrite QH in *. exact (HEAP_frame_v _ (ms_mem ms) m' mo FPD WM DMH OH).
    + apply Uint63.eqb_false_spec in QH. apply (OPS_frame_other _ _ (ms_mem ms) m' mo QH OH FPD). intros a Ha _ Wb. exact (WB a Ha Wb).
  - intros a b Hab seg Hseg. pose proof (MINV a b Hab) as RO. unfold AM.ro_addr in RO. rewrite Hseg in RO. apply negb_false_iff in RO. exact RO.
Qed.

End Leaf.

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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import MemOps.TwinB MemsetFX.TwinB RangePre.TwinB MemsetPost.TwinB PubImg.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Section Leaf.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.TwinB.cov1 HEAP_ID args z.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AI L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (AM.wa a) = m (AM.wa a)) -> wmono bsegs m m' -> AHEAP AI L RNG st LB m'.
Lemma HEAP_frame_v : forall args m m' mo,
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS HEAP_ID args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  wmono bsegs m m' ->
  (forall a, AIMG_HI <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  op_holds OPS HEAP_ID args m mo -> op_holds OPS HEAP_ID args m' mo.
Proof.
  intros args m m' mo AG WMv DM H. apply OPS_holds1. apply OPS_holds1 in H. rewrite OPS_fp1 in AG.
  exact (heap_frameX_v AI IMGX IMGX_aci ACCT UNIV AI_frame_top (GlueA.TwinB.wmono_ofA bsegs) AI_fake Cw args m m' mo AG WMv DM H).
Qed.

Lemma st_ok_view_ext : forall E st ms mo (m' : amem) (lo hi : Z),
  st_ok bsegs OPS E st ms mo ->
  (forall a, 0 <= a < two64 -> ~ (lo <= a < hi) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) ->
  (forall a, lo <= a < hi -> rb bsegs m' a = rb bsegs (ms_mem ms) a) ->
  in_pubw lo hi ->
  (forall a, lo <= a < hi -> ~ in_priv (s_priv st) a) ->
  AM.mem_inv bsegs m' ->
  st_ok bsegs OPS E st (ms_with_mem ms m') mo.
Proof.
  intros E st ms mo m' lo hi HS OUT INV PW NPRIV MINV. pose proof (in_pubw_bounds _ _ PW) as [HLO HHI].
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (RB : forall a, 0 <= a < two64 -> rb bsegs m' a = rb bsegs (ms_mem ms) a).
  { intros a Ha. destruct (Z_le_gt_dec lo a) as [L1|L1]; [destruct (Z_lt_ge_dec a hi) as [L2|L2]|].
    - apply INV. lia.
    - apply ReadPost.TwinB.rb_ext. apply OUT; [exact Ha| lia].
    - apply ReadPost.TwinB.rb_ext. apply OUT; [exact Ha| lia]. }
  assert (WB : forall a, 0 <= a < two64 -> wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true).
  { intros a Ha Wb. destruct (Z_le_gt_dec lo a) as [L1|L1]; [destruct (Z_lt_ge_dec a hi) as [L2|L2]|].
    - exact (proj1 (pub_window_rw m' a (in_pubw_sub lo hi a (a + 1) PW ltac:(lia) ltac:(lia)))).
    - rewrite (ReadPost.TwinB.wb_ext (ms_mem ms) m' a); [exact Wb| apply OUT; [exact Ha| lia]].
    - rewrite (ReadPost.TwinB.wb_ext (ms_mem ms) m' a); [exact Wb| apply OUT; [exact Ha| lia]]. }
  assert (WM : wmono bsegs (ms_mem ms) m').
  { intros x Hx. pose proof (bv_unsigned_in_range 64 x) as RX. change (bv_modulus 64) with two64 in RX.
    assert (EX : AM.wa (bv_unsigned x) = x) by (unfold AM.wa; apply Z_to_bv_bv_unsigned).
    rewrite <- EX. apply (GlueA.TwinB.wb_wviewA bsegs). apply WB; [exact RX|]. apply (GlueA.TwinB.wb_wviewA bsegs). rewrite EX. exact Hx. }
  assert (DMH : forall a, AIMG_HI <= a < two64 -> ms_mem ms (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None).
  { intros a Ha H. rewrite OUT; [exact H| unfold AIMG_HI in Ha; lia| unfold AIMG_HI in *; lia]. }
  split; cbn [ms_with_mem ms_upd ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom core_of c_regs c_fregs c_pc c_fcsr c_resv] in *;
    try assumption; try reflexivity.
  - intros k r0 Hk. exact (MemFX.MemFX.region_ok_view_frame bsegs _ _ (ms_mem ms) m' k r0 (Preg k r0 Hk) RB WB).
  - apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Pops o Ho) as OH.
    pose proof (proj1 (Forall_forall _ _) Papart o Ho) as AP. cbv beta in OH, AP |- *.
    assert (FPD : forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))) ->
                   ms_mem ms (Z_to_bv 64 a) = m' (Z_to_bv 64 a)).
    { intros a Ha FP. symmetry. apply OUT; [exact Ha|]. intros IN. destruct (AP a FP) as [_ PRIVa].
      destruct (pub_window_rw m' a (in_pubw_sub lo hi a (a + 1) PW ltac:(lia) ltac:(lia))) as (_ & _ & SEG). exact (NPRIV a IN (PRIVa SEG)). }
    destruct (PrimInt63.eqb (op_id o) HEAP_ID) eqn:QH.
    + apply Uint63.eqb_correct in QH. rewrite QH in *. exact (HEAP_frame_v _ (ms_mem ms) m' mo FPD WM DMH OH).
    + apply Uint63.eqb_false_spec in QH. apply (OPS_frame_other _ _ (ms_mem ms) m' mo QH OH FPD). intros a Ha _ Wb. exact (WB a Ha Wb).
  - intros a b Hab seg Hseg. pose proof (MINV a b Hab) as RO. unfold AM.ro_addr in RO. rewrite Hseg in RO. apply negb_false_iff in RO. exact RO.
Qed.

End Leaf.
End TwinB.
