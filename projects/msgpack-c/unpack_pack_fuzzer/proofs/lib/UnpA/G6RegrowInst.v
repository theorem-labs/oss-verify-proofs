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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import VecCopy.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CtrPat.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib Ops.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA Require Import G6RegrowAC G6RegrowA.
Unset Nia Cache. Unset Nra Cache.
Import UG.

Module G6RegrowInst.
Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable XW : client_world.
Let Cw : client_world := UO.unp_cw asegs XW.
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
Variable SYM : Z.
Hypothesis WALK : memcpy_walk_stmt SYM.
Variable MEMCPY_PC : int.
Hypothesis HPCZ : to_Z MEMCPY_PC = SYM.
Variable AWx : alloc_world asegs IMGX.
Hypothesis HOPS : heap_ops asegs IMGX AWx Cw OPS.
Variable isV : bool.

Lemma src_cb : forall st E ms mo r hargs wnl kb nsv md aw ws ca,
  st_ok asegs OPS E st ms mo ->
  ActrA.twin_pat_ok_t st wnl kb nsv = true -> the_op st = Some (md, aw, ws, ca) ->
  (forall LB, cw_holds Cw (to_Z md) (map (den E) ca) LB (map (wden E) ws) (ms_mem ms) ->
     In (bv_unsigned (ev E kb), bv_unsigned (den E nsv)) LB /\
     (forall w, In w (map (wden E) ws) -> (w_kind w = HeapOp.K_BLOCK \/ K_GHOST <= w_kind w) ->
                forall a, in_iv (w_iv w) a -> ~ in_iv (bv_unsigned (ev E kb), bv_unsigned (den E nsv)) a)) ->
  forall L RNG sta LBa aw', CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw' -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  exists ps, In (HB ps (bv_unsigned (ev E kb)) (bv_unsigned (den E nsv))) LBa /\ ablock_shadow (ms_mem ms) (bv_unsigned (ev E kb)) (bv_unsigned (den E nsv)).
Proof.
  intros st E ms mo r hargs wnl kb nsv md aw ws ca HS SP TO CB L RNG sta LBa aw' CF AH.
  pose proof CF as (LB & ks & offs & rss & ksp & nn & mdw & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                    & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (the_op_full st md aw ws ca TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof (ReadPost.count_one_args HEAP_ID (s_ops st) o hargs (op_in_In st o OPS1) OID Hc Hf) as EA.
  pose proof (decode_hargs E mdw A nw rest nn Tnw Nn Ln) as D1. rewrite <- Eh, <- EA, (DECf E) in D1. injection D1 as M1 _ W1 C1.
  change (nn + (nn + (nn + 0)))%nat with (3 * nn)%nat in C1.
  rewrite <- M1, <- C1, <- W1 in HC.
  destruct (CB LB HC) as (INLB & APART).
  set (v := (bv_unsigned (ev E kb), bv_unsigned (den E nsv))) in *.
  destruct ARW as [HW WMS]. pose proof TI as (T1 & T2 & T3 & _). rewrite <- W1 in T1, T2, T3.
  pose proof HW as (AHw & HT & _).
  destruct WOF as (_ & _ & _ & WLBa).
  destruct (LB_cases AI ACCT UNIV W aw' LB (ms_mem ms) mo v HW INLB) as [(b & Vb & Ev)|[(b & Hb & Ev)|(b & Vb & Ev)]].
  - destruct (kind_cases b) as [HH|HF].
    + destruct HH as [p KP]. exists p.
      assert (EB : HB p (fst v) (snd v) = b).
      { rewrite Ev. unfold user_iv. cbn [fst snd]. rewrite (usz_heap b (ex_intro _ p KP)). destruct b as [kd ad sz]. cbn [ab_kind ab_addr ab_size] in *. subst kd. reflexivity. }
      assert (INB : In (HB p (fst v) (snd v)) LBa) by (rewrite EB, <- WLBa; exact (proj1 Vb)).
      split; [exact INB|].
      exact (CtrPat.twin_pat_sound_t AI ACCT UNIV Cw OPS E st ms mo r hargs wnl L RNG sta LBa aw' kb nsv p HS CF SP INB).
    + exfalso. destruct (T3 b (conj Vb HF)) as [WIN _].
      destruct (blk_facts AI AI_fake _ _ _ _ _ b AHw (proj1 Vb)) as (NP & _).
      destruct (AI_fake _ _ _ _ _ b AHw (proj1 Vb) HF) as (_ & _ & _ & _ & N64 & _).
      apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FRAMEz; cbn; lia) (ab_addr b)).
      * unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. lia.
      * rewrite Ev. unfold in_iv, user_iv. cbn [fst snd]. rewrite (usz_fake b HF). lia.
  - exfalso. pose proof (T1 b Hb) as WIN. destruct (LB_twin_facts AI ACCT UNIV W aw' LB (ms_mem ms) mo b HW Hb) as (_ & _ & P1).
    apply (APART _ WIN ltac:(right; unfold K_GHOST, K_TWINz; cbn; lia) (fst v)).
    + unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. rewrite Ev. unfold twin_iv. cbn [fst snd]. lia.
    + unfold in_iv. rewrite Ev. unfold twin_iv. cbn [fst snd]. lia.
  - exfalso. destruct (T3 b Vb) as [_ WIN]. destruct (LB_fsh_facts AI ACCT UNIV AI_fake W aw' LB (ms_mem ms) mo b HW Vb) as (_ & _ & P1 & _).
    apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FTWINz; cbn; lia) (fst v)).
    + unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. rewrite Ev. unfold fsh_iv. cbn [fst snd]. lia.
    + unfold in_iv. rewrite Ev. unfold fsh_iv. cbn [fst snd]. lia.
Qed.

Theorem g6regrow_sound : contract_sound asegs OPS MP PB (G6RegrowAC.g6r_contract ActrA.twin_pat_ok_t isV MEMCPY_PC).
Proof.
  apply (G6RegrowA.g6r_sound asegs IMGX AWx XW OPS HOPS MP PB ActrA.twin_pat_ok_t isV MEMCPY_PC).

  intros st K E ms mo r hargs wnl st1 ka ra wlena kb nsv nZ md aw ws ca HS HMP Hpc PRE D10 FA BG LO RW WL PATa N0 NH HW CELLS D11 D12 SEP SP NL TO CB LEAF.
  apply (veccopy_cps AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           Cw_sub_ghost W_PAT MP NMAXt ACCT_rng ACCT_rng_aimg ACCT_silent SYM WALK
           st K E ms mo r hargs wnl st1 ka ra wlena (wlit 1%uint63) (bv_unsigned (ev E kb)) nZ HS HMP ltac:(rewrite Hpc; exact HPCZ) PRE D10 FA BG LO RW WL
           ltac:(vm_compute; reflexivity) PATa N0 NH HW CELLS D11 D12 SEP).
  - intros L RNG sta LBa aw' CF AH.
    destruct (src_cb st E ms mo r hargs wnl kb nsv md aw ws ca HS SP TO CB L RNG sta LBa aw' CF AH) as (ps & IN & PAT).
    exists ps, (bv_unsigned (ev E kb)), (bv_unsigned (den E nsv)). split; [exact IN|]. split; [apply Z.le_refl|]. split; [lia| exact PAT].
  - exact LEAF.
Qed.
End Sound.
End G6RegrowInst.

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
Import VecCopy.TwinB.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Ops.
Import G6RegrowAC.TwinB G6RegrowA.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import UG.

Module G6RegrowInst.
Section Sound.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable XW : client_world.
Let Cw : client_world := UO.unp_cw bsegs XW.
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
Variable SYM : Z.
Hypothesis WALK : memcpy_walk_stmt SYM.
Variable MEMCPY_PC : int.
Hypothesis HPCZ : to_Z MEMCPY_PC = SYM.
Variable AWx : alloc_world bsegs IMGX.
Hypothesis HOPS : heap_ops bsegs IMGX AWx Cw OPS.
Variable isV : bool.

Lemma src_cb : forall st E ms mo r hargs wnl kb nsv md aw ws ca,
  st_ok bsegs OPS E st ms mo ->
  ActrA.twin_pat_ok_t st wnl kb nsv = true -> the_op st = Some (md, aw, ws, ca) ->
  (forall LB, cw_holds Cw (to_Z md) (map (den E) ca) LB (map (wden E) ws) (ms_mem ms) ->
     In (bv_unsigned (ev E kb), bv_unsigned (den E nsv)) LB /\
     (forall w, In w (map (wden E) ws) -> (w_kind w = HeapOp.K_BLOCK \/ K_GHOST <= w_kind w) ->
                forall a, in_iv (w_iv w) a -> ~ in_iv (bv_unsigned (ev E kb), bv_unsigned (den E nsv)) a)) ->
  forall L RNG sta LBa aw', CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw' -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  exists ps, In (HB ps (bv_unsigned (ev E kb)) (bv_unsigned (den E nsv))) LBa /\ ablock_shadow (ms_mem ms) (bv_unsigned (ev E kb)) (bv_unsigned (den E nsv)).
Proof.
  intros st E ms mo r hargs wnl kb nsv md aw ws ca HS SP TO CB L RNG sta LBa aw' CF AH.
  pose proof CF as (LB & ks & offs & rss & ksp & nn & mdw & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                    & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (the_op_full st md aw ws ca TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof (ReadPost.TwinB.count_one_args HEAP_ID (s_ops st) o hargs (op_in_In st o OPS1) OID Hc Hf) as EA.
  pose proof (decode_hargs E mdw A nw rest nn Tnw Nn Ln) as D1. rewrite <- Eh, <- EA, (DECf E) in D1. injection D1 as M1 _ W1 C1.
  change (nn + (nn + (nn + 0)))%nat with (3 * nn)%nat in C1.
  rewrite <- M1, <- C1, <- W1 in HC.
  destruct (CB LB HC) as (INLB & APART).
  set (v := (bv_unsigned (ev E kb), bv_unsigned (den E nsv))) in *.
  destruct ARW as [HW WMS]. pose proof TI as (T1 & T2 & T3 & _). rewrite <- W1 in T1, T2, T3.
  pose proof HW as (AHw & HT & _).
  destruct WOF as (_ & _ & _ & WLBa).
  destruct (LB_cases AI ACCT UNIV W aw' LB (ms_mem ms) mo v HW INLB) as [(b & Vb & Ev)|[(b & Hb & Ev)|(b & Vb & Ev)]].
  - destruct (kind_cases b) as [HH|HF].
    + destruct HH as [p KP]. exists p.
      assert (EB : HB p (fst v) (snd v) = b).
      { rewrite Ev. unfold user_iv. cbn [fst snd]. rewrite (usz_heap b (ex_intro _ p KP)). destruct b as [kd ad sz]. cbn [ab_kind ab_addr ab_size] in *. subst kd. reflexivity. }
      assert (INB : In (HB p (fst v) (snd v)) LBa) by (rewrite EB, <- WLBa; exact (proj1 Vb)).
      split; [exact INB|].
      exact (CtrPat.TwinB.twin_pat_sound_t AI ACCT UNIV Cw OPS E st ms mo r hargs wnl L RNG sta LBa aw' kb nsv p HS CF SP INB).
    + exfalso. destruct (T3 b (conj Vb HF)) as [WIN _].
      destruct (blk_facts AI AI_fake _ _ _ _ _ b AHw (proj1 Vb)) as (NP & _).
      destruct (AI_fake _ _ _ _ _ b AHw (proj1 Vb) HF) as (_ & _ & _ & _ & N64 & _).
      apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FRAMEz; cbn; lia) (ab_addr b)).
      * unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. lia.
      * rewrite Ev. unfold in_iv, user_iv. cbn [fst snd]. rewrite (usz_fake b HF). lia.
  - exfalso. pose proof (T1 b Hb) as WIN. destruct (LB_twin_facts AI ACCT UNIV W aw' LB (ms_mem ms) mo b HW Hb) as (_ & _ & P1).
    apply (APART _ WIN ltac:(right; unfold K_GHOST, K_TWINz; cbn; lia) (fst v)).
    + unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. rewrite Ev. unfold twin_iv. cbn [fst snd]. lia.
    + unfold in_iv. rewrite Ev. unfold twin_iv. cbn [fst snd]. lia.
  - exfalso. destruct (T3 b Vb) as [_ WIN]. destruct (LB_fsh_facts AI ACCT UNIV AI_fake W aw' LB (ms_mem ms) mo b HW Vb) as (_ & _ & P1 & _).
    apply (APART _ WIN ltac:(right; unfold K_GHOST, K_FTWINz; cbn; lia) (fst v)).
    + unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. rewrite Ev. unfold fsh_iv. cbn [fst snd]. lia.
    + unfold in_iv. rewrite Ev. unfold fsh_iv. cbn [fst snd]. lia.
Qed.

Theorem g6regrow_sound : contract_sound bsegs OPS MP PB (G6RegrowAC.TwinB.G6RegrowAC.g6r_contract ActrA.twin_pat_ok_t isV MEMCPY_PC).
Proof.
  apply (G6RegrowA.TwinB.G6RegrowA.g6r_sound bsegs IMGX AWx XW OPS HOPS MP PB ActrA.twin_pat_ok_t isV MEMCPY_PC).

  intros st K E ms mo r hargs wnl st1 ka ra wlena kb nsv nZ md aw ws ca HS HMP Hpc PRE D10 FA BG LO RW WL PATa N0 NH HW CELLS D11 D12 SEP SP NL TO CB LEAF.
  apply (veccopy_cps AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           Cw_sub_ghost W_PAT MP NMAXt ACCT_rng ACCT_rng_aimg ACCT_silent SYM WALK
           st K E ms mo r hargs wnl st1 ka ra wlena (wlit 1%uint63) (bv_unsigned (ev E kb)) nZ HS HMP ltac:(rewrite Hpc; exact HPCZ) PRE D10 FA BG LO RW WL
           ltac:(vm_compute; reflexivity) PATa N0 NH HW CELLS D11 D12 SEP).
  - intros L RNG sta LBa aw' CF AH.
    destruct (src_cb st E ms mo r hargs wnl kb nsv md aw ws ca HS SP TO CB L RNG sta LBa aw' CF AH) as (ps & IN & PAT).
    exists ps, (bv_unsigned (ev E kb)), (bv_unsigned (den E nsv)). split; [exact IN|]. split; [apply Z.le_refl|]. split; [lia| exact PAT].
  - exact LEAF.
Qed.
End Sound.
End G6RegrowInst.
End TwinB.
