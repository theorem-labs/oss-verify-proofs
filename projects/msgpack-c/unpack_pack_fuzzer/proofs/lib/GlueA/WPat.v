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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require GlueA CtrPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggLib UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require RangeC.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CtrPat.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import MemsetPre.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Section WPat.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : FX.State.St.optable.
Hypothesis AI_fake : AI_fake_law AI.

Hypothesis W_PAT_SUB : w_pat_sub_stmt AI ACCT UNIV Cw.

Theorem w_pat_ok : w_pat_ev_stmt AI ACCT UNIV Cw OPS.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb HS CF AH WL KT NF7 NF8 PK lo hi L0 LH HW HIN BA1 BA2.
  unfold RangeC.RangeC.pat_ok in PK. destruct (W64.weqb kind CtrLib.K_BLOCK) eqn:KB.
  2:{ exact (W_PAT_SUB E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb CF WL KT KB NF7 NF8 PK lo hi L0 LH HW HIN BA1 BA2). }

  destruct (CtrPat.twin_pat_sound AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake E st ms mo r hargs wnl L RNG sta LBa aw kd HS CF PK) as (p' & n & WL' & HIN' & PAT).
  rewrite WL in WL'. injection WL' as <- _.
  set (b1 := HB p A nb) in *. set (b2 := HB p' (bv_unsigned (Val.ev E kd)) (bv_unsigned (Val.den E wlen))) in *.
  destruct (ablock_eq_dec b1 b2) as [EQ|NE].
  - unfold b1, b2 in EQ. injection EQ as _ EA EN. rewrite EA, EN. exact PAT.
  - exfalso. pose proof (AI_blocks_disjoint AI L RNG sta LBa (ms_mem ms) b1 b2 AH HIN HIN' NE) as D.
    unfold b1, b2 in D. cbn [ab_addr ab_size] in D. lia.
Qed.
End WPat.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import Ledger.TwinB Op.TwinB.
Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs.
Import MemsetPre.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Section WPat.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : FX.State.St.optable.
Hypothesis AI_fake : AI_fake_law AI.

Hypothesis W_PAT_SUB : w_pat_sub_stmt AI ACCT UNIV Cw.

Theorem w_pat_ok : w_pat_ev_stmt AI ACCT UNIV Cw OPS.
Proof.
  intros E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb HS CF AH WL KT NF7 NF8 PK lo hi L0 LH HW HIN BA1 BA2.
  unfold RangeC.TwinB.RangeC.pat_ok in PK. destruct (W64.weqb kind CtrLib.K_BLOCK) eqn:KB.
  2:{ exact (W_PAT_SUB E st ms mo r hargs wnl L RNG sta LBa aw kd wlen kind p A nb CF WL KT KB NF7 NF8 PK lo hi L0 LH HW HIN BA1 BA2). }

  destruct (CtrPat.TwinB.twin_pat_sound AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake E st ms mo r hargs wnl L RNG sta LBa aw kd HS CF PK) as (p' & n & WL' & HIN' & PAT).
  rewrite WL in WL'. injection WL' as <- _.
  set (b1 := HB p A nb) in *. set (b2 := HB p' (bv_unsigned (Val.ev E kd)) (bv_unsigned (Val.den E wlen))) in *.
  destruct (ablock_eq_dec b1 b2) as [EQ|NE].
  - unfold b1, b2 in EQ. injection EQ as _ EA EN. rewrite EA, EN. exact PAT.
  - exfalso. pose proof (AI_blocks_disjoint AI L RNG sta LBa (ms_mem ms) b1 b2 AH HIN HIN' NE) as D.
    unfold b1, b2 in D. cbn [ab_addr ab_size] in D. lia.
Qed.
End WPat.
End TwinB.
