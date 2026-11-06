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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import MemOps RangeC SinkC MemsetFX RangePre MemsetPre MemsetPost RegRepl MemcpySound Memcpy0Sound RstageSound RstagePost.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require MemcpyCtr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import RtCells.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPost.
Import ValP MemP StepB CtrFX ActrA SinkC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.I_memcpy.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import SinkSound.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CtrPat.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh RangeC RangeFX MemcpyC RangePre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require ShLaw.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv GLib PkOps PkLib PkBody.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require Import VecCopy2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require Import PkBodyAC PkBodySrc.
Import UG.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Ops ClientX PkInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require LdPart.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require Import PkBodyA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require Import PkRegrowAC PkRegrowInst.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require Import PkExtbA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require Import LdPartSoundA.
Unset Nia Cache. Unset Nra Cache.
Import UO CX.

Module PkInstB.
Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Notation Cw := (UO.unp_cw asegs (CX.XTP asegs)).
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
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).
Hypothesis OPS_holds_ssh : forall m mo, op_holds OPS RangeC.SSH_ID [] m mo -> ssh_holds m.
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.
Variable SYM : Z.
Hypothesis WALK : memcpy_walk_stmt SYM.
Variable FRM0 : Z.
Hypothesis FR0 : 0 < FRM0 <= 8192.
Hypothesis WALK0 : memcpy0_walk_stmt SYM FRM0.
Variable AWx : alloc_world asegs IMGX.
Hypothesis HOPS : heap_ops asegs IMGX AWx Cw OPS.

Variable MEMCPY_PC : int.
Hypothesis HPCZ : to_Z MEMCPY_PC = SYM.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma cw3 : forall ca LB ws m, cw_holds Cw 3 ca LB ws m -> PK.cw_pk_holds asegs ca LB ws m.
Proof. intros ca LB ws m H. exact H. Qed.
Lemma cw3' : forall ca LB ws m, PK.cw_pk_holds asegs ca LB ws m -> cw_holds Cw 3 ca LB ws m.
Proof. intros ca LB ws m H. exact H. Qed.

Theorem pkregrowa_sound : contract_sound asegs OPS MP PB (PkRegrowAC.pkregrow_contract ActrA.twin_pat_ok_t MEMCPY_PC).
Proof.
  exact (PkRegrowInst.pkregrowa_sound AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           Cw_sub_ghost W_PAT MP PB NMAXt ACCT_rng ACCT_rng_aimg ACCT_silent SYM WALK FRM0 FR0 WALK0 MEMCPY_PC HPCZ AWx HOPS cw3 cw3').
Qed.

Theorem pkbody_sound : contract_sound asegs OPS MP PB (PkBodyAC.pkbody_c asegs MEMCPY_PC).
Proof.
  exact (PkBodyA.pkbody_sound AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           Cw_sub_ghost W_PAT MP PB NMAXt ACCT_rng ACCT_rng_aimg ACCT_silent OPS_holds_ssh ACCT_rng_stk_sh ACCT_frng SYM WALK FRM0 FR0 WALK0 AWx HOPS cw3
           MEMCPY_PC HPCZ).
Qed.

Theorem pkextb_sound : forall pc, contract_sound asegs OPS MP PB (PkBody.pkextb_c asegs pc).
Proof. exact (PkExtbA.pkextb_sound asegs IMGX AWx Cw OPS HOPS cw3 MP PB HMPA). Qed.

Theorem ldpart_sound : forall pc, contract_sound asegs OPS MP PB (LdPart.LdPart.ldpart_c asegs pc).
Proof. exact (LdPartSoundA.ldpart_sound asegs OPS MP PB HMPA). Qed.

End Sound.
End PkInstB.

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

Import UnreggSound.TwinB.
Import MemOps.TwinB RangeC.TwinB SinkC.TwinB MemsetFX.TwinB RangePre.TwinB MemsetPre.TwinB MemsetPost.TwinB RegRepl.TwinB MemcpySound.TwinB Memcpy0Sound.TwinB RstageSound.TwinB RstagePost.TwinB.

Import RtCells.TwinB.

Import ValP MemP StepB CtrFX ActrA SinkC.TwinB.SinkC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.TwinB.I_memcpy.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Import SinkSound.TwinB.

Import StackSh.TwinB RangeC.TwinB RangeFX.TwinB MemcpyC.TwinB RangePre.TwinB.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Model OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Layout OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkOps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkBody.
Import VecCopy2.TwinB.
Import PkBodyAC.TwinB PkBodySrc.TwinB.
Import UG.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Ops OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.ClientX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkInst.

Import PkBodyA.TwinB.
Import PkRegrowAC.TwinB PkRegrowInst.TwinB.
Import PkExtbA.TwinB.
Import LdPartSoundA.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import UO CX.

Module PkInstB.
Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Notation Cw := (UO.unp_cw bsegs (CX.XTP bsegs)).
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Bridge.Op.TwinB.cov1 HEAP_ID args z.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Hypothesis W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable NMAXt : nat.
Notation twfS := (twfA node nstepA nexitA (nsafeA NMAXt) fstepS NMAXt).
Hypothesis ACCT_rng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (ATOP + 4096) (2^47 - (ATOP + 4096)).
Hypothesis ACCT_rng_aimg : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng_aimg RNG.
Hypothesis ACCT_silent : forall aw L RNG st LBa mo,
  ACCT aw L RNG st LBa mo -> MP mo ->
  exists A0 moc, mrel A0 moc mo /\ minvA moc /\ m_halted moc = None /\
    twfS RNG A0 (Ret (Exc.Ok tt)) moc (acct_leaf_silent ACCT OPS OTHER MP mo aw L st LBa).
Hypothesis OPS_holds_ssh : forall m mo, op_holds OPS RangeC.TwinB.RangeC.SSH_ID [] m mo -> ssh_holds m.
Hypothesis ACCT_rng_stk_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG (shad ATOP) (Shadow.KHIGH - shad ATOP).
Hypothesis ACCT_frng : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> FRNG AI AI_fake L RNG.
Variable SYM : Z.
Hypothesis WALK : memcpy_walk_stmt SYM.
Variable FRM0 : Z.
Hypothesis FR0 : 0 < FRM0 <= 8192.
Hypothesis WALK0 : memcpy0_walk_stmt SYM FRM0.
Variable AWx : alloc_world bsegs IMGX.
Hypothesis HOPS : heap_ops bsegs IMGX AWx Cw OPS.

Variable MEMCPY_PC : int.
Hypothesis HPCZ : to_Z MEMCPY_PC = SYM.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma cw3 : forall ca LB ws m, cw_holds Cw 3 ca LB ws m -> PK.cw_pk_holds bsegs ca LB ws m.
Proof. intros ca LB ws m H. exact H. Qed.
Lemma cw3' : forall ca LB ws m, PK.cw_pk_holds bsegs ca LB ws m -> cw_holds Cw 3 ca LB ws m.
Proof. intros ca LB ws m H. exact H. Qed.

Theorem pkregrowa_sound : contract_sound bsegs OPS MP PB (PkRegrowAC.TwinB.PkRegrowAC.pkregrow_contract ActrA.twin_pat_ok_t MEMCPY_PC).
Proof.
  exact (PkRegrowInst.TwinB.PkRegrowInst.pkregrowa_sound AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           Cw_sub_ghost W_PAT MP PB NMAXt ACCT_rng ACCT_rng_aimg ACCT_silent SYM WALK FRM0 FR0 WALK0 MEMCPY_PC HPCZ AWx HOPS cw3 cw3').
Qed.

Theorem pkbody_sound : contract_sound bsegs OPS MP PB (PkBodyAC.TwinB.PkBodyAC.pkbody_c bsegs MEMCPY_PC).
Proof.
  exact (PkBodyA.TwinB.PkBodyA.pkbody_sound AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           Cw_sub_ghost W_PAT MP PB NMAXt ACCT_rng ACCT_rng_aimg ACCT_silent OPS_holds_ssh ACCT_rng_stk_sh ACCT_frng SYM WALK FRM0 FR0 WALK0 AWx HOPS cw3
           MEMCPY_PC HPCZ).
Qed.

Theorem pkextb_sound : forall pc, contract_sound bsegs OPS MP PB (PkBody.pkextb_c bsegs pc).
Proof. exact (PkExtbA.TwinB.PkExtbA.pkextb_sound bsegs IMGX AWx Cw OPS HOPS cw3 MP PB HMPA). Qed.

Theorem ldpart_sound : forall pc, contract_sound bsegs OPS MP PB (LdPart.LdPart.ldpart_c bsegs pc).
Proof. exact (LdPartSoundA.TwinB.LdPartSoundA.ldpart_sound bsegs OPS MP PB HMPA). Qed.

End Sound.
End PkInstB.
End TwinB.
