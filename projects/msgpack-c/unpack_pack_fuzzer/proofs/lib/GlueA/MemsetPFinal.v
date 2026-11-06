(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import UnreggSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StackSh RangeC MemsetC MemsetPre MemsetSound MemsetPost MemsetFinal PubC PubImg MemsetPC MemsetPSound MemsetPPost.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_asan_memcpy.
Module IAM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.I_asan_memset.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require WPat.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp ActrA MemsetC MemsetPC.
Open Scope Z_scope.

Section Final.
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

Hypothesis W_PAT_SUB : w_pat_sub_stmt AI ACCT UNIV Cw.
Let W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS := WPat.w_pat_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake W_PAT_SUB.
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.

Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc4000.
Hypothesis OPS_holds_zpb : forall m mo, op_holds OPS PubC.ZPB_ID [] m mo -> zpb_holds m.
Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AI L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (ALib.Mem.wa a) = m (ALib.Mem.wa a)) -> wmono asegs m m' -> AHEAP AI L RNG st LB m'.

Theorem amemsetp_sound_at : forall SYM, memset_walk_stmt SYM ->
  forall pc, to_Z pc = SYM -> contract_sound asegs OPS MP PB (amemsetp_c asegs pc).
Proof.
  intros SYM WALK.
  apply (amemsetp_sound_of_leaf AI ACCT UNIV Cw OPS AI_fake OPS_holds1 OTHER MP PB NMAXt SYM WALK ACCT_rng ACCT_rng_aimg ACCT_silent ACCT_rng_aimg_sh OPS_holds_zpb).
  exact (amemsetp_leaf_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
           OPS_cov0_img MP PB AI_frame_top).
Qed.

Theorem amemsetp_sound : forall pc, to_Z pc = MEMSET_SYM -> contract_sound asegs OPS MP PB (amemsetp_c asegs pc).
Proof. exact (amemsetp_sound_at MEMSET_SYM memset_walk_i). Qed.
Theorem aasan_memsetp_sound : forall pc, to_Z pc = ASAN_MEMSET_SYM -> contract_sound asegs OPS MP PB (amemsetp_c asegs pc).
Proof. exact (amemsetp_sound_at ASAN_MEMSET_SYM memset_walk_asan). Qed.
End Final.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB Actr.TwinB.
Import UnreggSound.TwinB.
Import StackSh.TwinB RangeC.TwinB MemsetC.TwinB MemsetPre.TwinB MemsetSound.TwinB MemsetPost.TwinB MemsetFinal.TwinB PubC.TwinB PubImg.TwinB MemsetPC.TwinB MemsetPSound.TwinB MemsetPPost.TwinB.

Module IAM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.TwinB.I_asan_memset.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp ActrA MemsetC.TwinB.MemsetC MemsetPC.TwinB.MemsetPC.
Open Scope Z_scope.

Section Final.
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

Hypothesis W_PAT_SUB : w_pat_sub_stmt AI ACCT UNIV Cw.
Let W_PAT : w_pat_ev_stmt AI ACCT UNIV Cw OPS := WPat.TwinB.w_pat_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake W_PAT_SUB.
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.

Hypothesis ACCT_rng_aimg_sh : forall aw L RNG st LBa mo, ACCT aw L RNG st LBa mo -> rng RNG 0x7fffa000 0xc5000.
Hypothesis OPS_holds_zpb : forall m mo, op_holds OPS PubC.TwinB.PubC.ZPB_ID [] m mo -> zpb_holds m.
Hypothesis AI_frame_top : forall L RNG st LB m m',
  AHEAP AI L RNG st LB m -> (forall a, 0 <= a < 2^47 -> m' (ALib.Mem.wa a) = m (ALib.Mem.wa a)) -> wmono bsegs m m' -> AHEAP AI L RNG st LB m'.

Theorem amemsetp_sound_at : forall SYM, memset_walk_stmt SYM ->
  forall pc, to_Z pc = SYM -> contract_sound bsegs OPS MP PB (amemsetp_c bsegs pc).
Proof.
  intros SYM WALK.
  apply (amemsetp_sound_of_leaf AI ACCT UNIV Cw OPS AI_fake OPS_holds1 OTHER MP PB NMAXt SYM WALK ACCT_rng ACCT_rng_aimg ACCT_silent ACCT_rng_aimg_sh OPS_holds_zpb).
  exact (amemsetp_leaf_ok AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other
           OPS_cov0_img MP PB AI_frame_top).
Qed.

Theorem amemsetp_sound : forall pc, to_Z pc = MEMSET_SYM -> contract_sound bsegs OPS MP PB (amemsetp_c bsegs pc).
Proof. exact (amemsetp_sound_at MEMSET_SYM memset_walk_i). Qed.
Theorem aasan_memsetp_sound : forall pc, to_Z pc = ASAN_MEMSET_SYM -> contract_sound bsegs OPS MP PB (amemsetp_c bsegs pc).
Proof. exact (amemsetp_sound_at ASAN_MEMSET_SYM memset_walk_asan). Qed.
End Final.

End TwinB.
