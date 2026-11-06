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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_printf_icpt.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import HalfC HalfFX MemOps MemsetFX MemcpyFX RangePre MemsetPost HalfPost VprintfC VprintfSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPost.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA HalfC VprintfC.
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

Lemma avprintf_leaf_ok : VprintfSound.avprintf_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold VprintfSound.avprintf_leaf.
  intros st K E ms mo r hargs wnl st1 st3 L RNG sta LBa aw HS HPB HK PRE G10 PUSH CP FS CF AH MI BOT LO SPT ms' mo' HQ HMP' HMI' OTH ACP.
  set (R := ms_regs ms) in *. set (sp := bv_unsigned (AP.getr R 2)) in *.
  destruct HQ as (t0 & t1 & t2 & x13 & x14 & x15 & x16 & x17 & t3 & t4 & t5 & t6 & m' & j24 & j16 & EMS & MU & WM & MINV' & STK' & FR1 & FR2 & _).
  fold sp in EMS, MU, STK', FR1, FR2.
  pose proof atop_range as ATR.
  match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
  set (RA := mixR R R'). set (Fv := CtrFree.cfvF RA). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.E' E st Fv Gv).
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.reg_of_X1, (GlueA.getr_RA asegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.den_wlit. }

  assert (STKM : stk asegs m' (CtrPre.sp_lo E st) sp).
  { pose proof (stk_of_rw_cells asegs m' _ _ FR2) as S2. pose proof (stk_of_rw_cells asegs m' _ _ FR1) as S1.
    cbn [cells_size csize Nat.add] in S1, S2. change (Z.of_nat 48) with 48 in S1, S2.
    replace (sp - 96 + 48) with (sp - 48) in S2 by lia. replace (sp - 48 + 48) with sp in S1 by lia.
    apply (stk_merge asegs m' _ (sp - 96) _ STK'); [| lia]. apply (stk_merge asegs m' _ (sp - 48) _ S2 S1). lia. }

  pose proof (HeapCtr.fresh_ok_inv st FOK) as (SVB & _).
  assert (RFB : rf_allb (sv_vars_below (s_next st)) (s_rf st) = true).
  { unfold st_vars_below in SVB. do 5 (apply andb_prop in SVB as [SVB _]). exact SVB. }
  assert (DR : forall x, den E' (getr st x) = AP.getr R (reg_of_r5 x)).
  { intros x. unfold E', getr. rewrite (CtrFrame.den_E' E st Fv Gv _ (PlanS.rf_allb_get _ _ _ RFB x)). symmetry. exact (GlueA.getr_RA asegs OPS E st ms mo HS x). }
  assert (DSP : den E' (vp_sp st) = Z_to_bv 64 (sp - 96)).
  { unfold vp_sp. rewrite den_sv_alu. cbn [alu64 alu den]. rewrite (DR X2). apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (AP.getr R (reg_of_r5 X2)) with (AP.getr R 2). fold sp. change (bv_unsigned (wbv NEG96)) with (2 ^ 64 - 96).
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). replace (sp + (2 ^ 64 - 96)) with (sp - 96 + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. reflexivity. }
  assert (DOFF : forall off : int, 0 <= to_Z off < 96 -> den E' (sv_alu ALU_ADD (vp_sp st) (VL (wlit off))) = Z_to_bv 64 (sp - 96 + to_Z off)).
  { intros off Ho. rewrite MemsetFX.MemsetFX.den_add_lit, DSP. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity. }
  idtac "VL-1".

  Time destruct (half_leaf_B1 AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img MP
              st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' 2416 (VL STDOUT) (vp_sp st) (vp_cells st r) st3 HS CP FS CF AH BOT LO SPT
              ltac:(lia) MU WM MI MINV' STKM ltac:(reflexivity) OTH HMI' ACP PUSH)
    as (msB & HSB & MB1 & MB2 & MB3 & MB4 & MB5 & MB6 & MB7 & SRF & SFF & SRV & SFA & SOP & SPV & SNX).
  {
    intros off v Hin x. change (CtrFrame.E' E st (CtrFree.cfvF (mixR (ms_regs ms) R')) (fun _ _ : Z => Z_to_bv 8 0)) with E'. unfold vp_cells in Hin. cbn [In] in Hin.
    assert (LOWSP : 0x62f000 <= sp - 96) by lia.
    repeat destruct Hin as [Hin|Hin]; try (injection Hin as <- <-); try contradiction.
    - rewrite (DOFF 16%uint63 ltac:(change (to_Z 16%uint63) with 16; lia)). match goal with |- context [den E' ?vv] => replace (den E' vv) with (AP.getr R (reg_of_r5 X18)) by (symmetry; exact (DR X18)) end. change (to_Z 16%uint63) with (Z.of_nat 16).
      apply (ghost_c8 m' (sp - 96) _ 16 _ FR2 eq_refl LOWSP).
    - rewrite (DOFF 24%uint63 ltac:(change (to_Z 24%uint63) with 24; lia)). match goal with |- context [den E' ?vv] => replace (den E' vv) with (AP.getr R (reg_of_r5 X11)) by (symmetry; exact (DR X11)) end. change (to_Z 24%uint63) with (Z.of_nat 24).
      apply (ghost_c8 m' (sp - 96) _ 24 _ FR2 eq_refl LOWSP).
    - rewrite (DOFF 32%uint63 ltac:(change (to_Z 32%uint63) with 32; lia)). match goal with |- context [den E' ?vv] => replace (den E' vv) with (AP.getr R (reg_of_r5 X10)) by (symmetry; exact (DR X10)) end. change (to_Z 32%uint63) with (Z.of_nat 32).
      apply (ghost_c8 m' (sp - 96) _ 32 _ FR2 eq_refl LOWSP).
    - rewrite (DOFF 40%uint63 ltac:(change (to_Z 40%uint63) with 40; lia)). change (to_Z 40%uint63) with (Z.of_nat 40).
      change (den E' (VL RET_VP)) with (Z_to_bv 64 327204).
      apply (ghost_c8 m' (sp - 96) _ 40 _ FR2 eq_refl LOWSP).
    - rewrite (DOFF 72%uint63 ltac:(change (to_Z 72%uint63) with 72; lia)). match goal with |- context [den E' ?vv] => replace (den E' vv) with (AP.getr R (reg_of_r5 X9)) by (symmetry; exact (DR X9)) end. replace (sp - 96 + to_Z 72%uint63) with (sp - 48 + Z.of_nat 24) by (change (to_Z 72%uint63) with 72; lia).
      apply (ghost_c8 m' (sp - 48) _ 24 _ FR1 eq_refl ltac:(lia)).
    - rewrite (DOFF 80%uint63 ltac:(change (to_Z 80%uint63) with 80; lia)). match goal with |- context [den E' ?vv] => replace (den E' vv) with (AP.getr R (reg_of_r5 X8)) by (symmetry; exact (DR X8)) end. replace (sp - 96 + to_Z 80%uint63) with (sp - 48 + Z.of_nat 32) by (change (to_Z 80%uint63) with 80; lia).
      apply (ghost_c8 m' (sp - 48) _ 32 _ FR1 eq_refl ltac:(lia)).
    - rewrite (DOFF 88%uint63 ltac:(change (to_Z 88%uint63) with 88; lia)). replace (sp - 96 + to_Z 88%uint63) with (sp - 48 + Z.of_nat 40) by (change (to_Z 88%uint63) with 88; lia).
      replace (den E' (VL (wlit r))) with (AP.getr R 1%bv) by (rewrite RAEQ; symmetry; exact (HeapCtr.den_wlit E' r)).
      apply (ghost_c8 m' (sp - 48) _ 40 _ FR1 eq_refl ltac:(lia)). }
  idtac "VL-2".

  assert (RGA : forall (RR : bvmap 5 word) F0 pc0 fc0 rv0 x, rget (Core RR F0 pc0 fc0 rv0) (reg_of_r5 x) = AP.getr RR (reg_of_r5 x)).
  { intros RR F0 pc0 fc0 rv0 x. unfold rget, AP.getr. cbn [c_regs]. destruct x; reflexivity. }
  idtac "VL-3".
  apply (HK _ ltac:(left; reflexivity) E' ms' mo' (CtrFrame.EXT E st Fv Gv) HMP').
  subst ms'.
  apply (HalfFX.st_ok_set_regs_pc asegs OPS E' st3 msB _ mo' (vp_regs st) REAL_VF HSB).
  1-7: cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending]; first [reflexivity | symmetry; assumption].
  - unfold vp_regs. repeat (apply Forall_cons; [cbn [fst]; discriminate|]). apply Forall_nil.
  -
    intros x. cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending]. rewrite RGA.
    pose proof (GlueA.getr_RA asegs OPS E' st3 msB mo' HSB x) as GX. rewrite MB1 in GX. unfold getr in GX.
    unfold vp_regs.
    destruct x; cbv [HalfFX.lookup_regs r5_eqb r5_to_Z Z.eqb Pos.eqb];
      try (match goal with |- _ = den E' (rf_get (s_rf st3) _) => rewrite <- GX; reflexivity end).
    all: idtac "REG".
    +   reflexivity.
    +   change (den E' (sv_alu ALU_ADD (getr st X2) (VL NEG96))) with (den E' (vp_sp st)). rewrite DSP. reflexivity.
    +   transitivity (AP.getr R (reg_of_r5 X10)); [reflexivity | symmetry; exact (DR X10)].
    +   reflexivity.
    +   transitivity (AP.getr R (reg_of_r5 X10)); [reflexivity | symmetry; exact (DR X10)].
    +   transitivity (AP.getr R (reg_of_r5 X11)); [reflexivity | symmetry; exact (DR X11)].
    +   transitivity (AP.getr R (reg_of_r5 X11)); [reflexivity | symmetry; exact (DR X11)].
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

Import HalfC.TwinB HalfFX.TwinB MemOps.TwinB MemsetFX.TwinB MemcpyFX.TwinB RangePre.TwinB MemsetPost.TwinB HalfPost.TwinB VprintfC.TwinB VprintfSound.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA HalfC.TwinB.HalfC VprintfC.TwinB.VprintfC.
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

Lemma avprintf_leaf_ok : VprintfSound.TwinB.avprintf_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold VprintfSound.TwinB.avprintf_leaf.
  intros st K E ms mo r hargs wnl st1 st3 L RNG sta LBa aw HS HPB HK PRE G10 PUSH CP FS CF AH MI BOT LO SPT ms' mo' HQ HMP' HMI' OTH ACP.
  set (R := ms_regs ms) in *. set (sp := bv_unsigned (AP.getr R 2)) in *.
  destruct HQ as (t0 & t1 & t2 & x13 & x14 & x15 & x16 & x17 & t3 & t4 & t5 & t6 & m' & j24 & j16 & EMS & MU & WM & MINV' & STK' & FR1 & FR2 & _).
  fold sp in EMS, MU, STK', FR1, FR2.
  pose proof atop_range as ATR.
  match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
  set (RA := mixR R R'). set (Fv := CtrFree.TwinB.cfvF RA). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.TwinB.E' E st Fv Gv).
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X1, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.TwinB.den_wlit. }

  assert (STKM : stk bsegs m' (CtrPre.TwinB.sp_lo E st) sp).
  { pose proof (stk_of_rw_cells bsegs m' _ _ FR2) as S2. pose proof (stk_of_rw_cells bsegs m' _ _ FR1) as S1.
    cbn [cells_size csize Nat.add] in S1, S2. change (Z.of_nat 48) with 48 in S1, S2.
    replace (sp - 96 + 48) with (sp - 48) in S2 by lia. replace (sp - 48 + 48) with sp in S1 by lia.
    apply (stk_merge bsegs m' _ (sp - 96) _ STK'); [| lia]. apply (stk_merge bsegs m' _ (sp - 48) _ S2 S1). lia. }

  pose proof (HeapCtr.TwinB.fresh_ok_inv st FOK) as (SVB & _).
  assert (RFB : rf_allb (sv_vars_below (s_next st)) (s_rf st) = true).
  { unfold st_vars_below in SVB. do 5 (apply andb_prop in SVB as [SVB _]). exact SVB. }
  assert (DR : forall x, den E' (getr st x) = AP.getr R (reg_of_r5 x)).
  { intros x. unfold E', getr. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv _ (PlanS.rf_allb_get _ _ _ RFB x)). symmetry. exact (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS x). }
  assert (DSP : den E' (vp_sp st) = Z_to_bv 64 (sp - 96)).
  { unfold vp_sp. rewrite den_sv_alu. cbn [alu64 alu den]. rewrite (DR X2). apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned.
    change (AP.getr R (reg_of_r5 X2)) with (AP.getr R 2). fold sp. change (bv_unsigned (wbv NEG96)) with (2 ^ 64 - 96).
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). replace (sp + (2 ^ 64 - 96)) with (sp - 96 + 1 * 2 ^ 64) by lia.
    rewrite Z.mod_add by lia. reflexivity. }
  assert (DOFF : forall off : int, 0 <= to_Z off < 96 -> den E' (sv_alu ALU_ADD (vp_sp st) (VL (wlit off))) = Z_to_bv 64 (sp - 96 + to_Z off)).
  { intros off Ho. rewrite MemsetFX.TwinB.MemsetFX.den_add_lit, DSP. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity. }
  idtac "VL-1".

  Time destruct (half_leaf_B1 AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img MP
              st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' 2416 (VL STDOUT) (vp_sp st) (vp_cells st r) st3 HS CP FS CF AH BOT LO SPT
              ltac:(lia) MU WM MI MINV' STKM ltac:(reflexivity) OTH HMI' ACP PUSH)
    as (msB & HSB & MB1 & MB2 & MB3 & MB4 & MB5 & MB6 & MB7 & SRF & SFF & SRV & SFA & SOP & SPV & SNX).
  {
    intros off v Hin x. change (CtrFrame.TwinB.E' E st (CtrFree.TwinB.cfvF (mixR (ms_regs ms) R')) (fun _ _ : Z => Z_to_bv 8 0)) with E'. unfold vp_cells in Hin. cbn [In] in Hin.
    assert (LOWSP : 0x631000 <= sp - 96) by lia.
    repeat destruct Hin as [Hin|Hin]; try (injection Hin as <- <-); try contradiction.
    - rewrite (DOFF 16%uint63 ltac:(change (to_Z 16%uint63) with 16; lia)). match goal with |- context [den E' ?vv] => replace (den E' vv) with (AP.getr R (reg_of_r5 X18)) by (symmetry; exact (DR X18)) end. change (to_Z 16%uint63) with (Z.of_nat 16).
      apply (ghost_c8 m' (sp - 96) _ 16 _ FR2 eq_refl LOWSP).
    - rewrite (DOFF 24%uint63 ltac:(change (to_Z 24%uint63) with 24; lia)). match goal with |- context [den E' ?vv] => replace (den E' vv) with (AP.getr R (reg_of_r5 X11)) by (symmetry; exact (DR X11)) end. change (to_Z 24%uint63) with (Z.of_nat 24).
      apply (ghost_c8 m' (sp - 96) _ 24 _ FR2 eq_refl LOWSP).
    - rewrite (DOFF 32%uint63 ltac:(change (to_Z 32%uint63) with 32; lia)). match goal with |- context [den E' ?vv] => replace (den E' vv) with (AP.getr R (reg_of_r5 X10)) by (symmetry; exact (DR X10)) end. change (to_Z 32%uint63) with (Z.of_nat 32).
      apply (ghost_c8 m' (sp - 96) _ 32 _ FR2 eq_refl LOWSP).
    - rewrite (DOFF 40%uint63 ltac:(change (to_Z 40%uint63) with 40; lia)). change (to_Z 40%uint63) with (Z.of_nat 40).
      change (den E' (VL RET_VP)) with (Z_to_bv 64 329652).
      apply (ghost_c8 m' (sp - 96) _ 40 _ FR2 eq_refl LOWSP).
    - rewrite (DOFF 72%uint63 ltac:(change (to_Z 72%uint63) with 72; lia)). match goal with |- context [den E' ?vv] => replace (den E' vv) with (AP.getr R (reg_of_r5 X9)) by (symmetry; exact (DR X9)) end. replace (sp - 96 + to_Z 72%uint63) with (sp - 48 + Z.of_nat 24) by (change (to_Z 72%uint63) with 72; lia).
      apply (ghost_c8 m' (sp - 48) _ 24 _ FR1 eq_refl ltac:(lia)).
    - rewrite (DOFF 80%uint63 ltac:(change (to_Z 80%uint63) with 80; lia)). match goal with |- context [den E' ?vv] => replace (den E' vv) with (AP.getr R (reg_of_r5 X8)) by (symmetry; exact (DR X8)) end. replace (sp - 96 + to_Z 80%uint63) with (sp - 48 + Z.of_nat 32) by (change (to_Z 80%uint63) with 80; lia).
      apply (ghost_c8 m' (sp - 48) _ 32 _ FR1 eq_refl ltac:(lia)).
    - rewrite (DOFF 88%uint63 ltac:(change (to_Z 88%uint63) with 88; lia)). replace (sp - 96 + to_Z 88%uint63) with (sp - 48 + Z.of_nat 40) by (change (to_Z 88%uint63) with 88; lia).
      replace (den E' (VL (wlit r))) with (AP.getr R 1%bv) by (rewrite RAEQ; symmetry; exact (HeapCtr.TwinB.den_wlit E' r)).
      apply (ghost_c8 m' (sp - 48) _ 40 _ FR1 eq_refl ltac:(lia)). }
  idtac "VL-2".

  assert (RGA : forall (RR : bvmap 5 word) F0 pc0 fc0 rv0 x, rget (Core RR F0 pc0 fc0 rv0) (reg_of_r5 x) = AP.getr RR (reg_of_r5 x)).
  { intros RR F0 pc0 fc0 rv0 x. unfold rget, AP.getr. cbn [c_regs]. destruct x; reflexivity. }
  idtac "VL-3".
  apply (HK _ ltac:(left; reflexivity) E' ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) HMP').
  subst ms'.
  apply (HalfFX.TwinB.HalfFX.st_ok_set_regs_pc bsegs OPS E' st3 msB _ mo' (vp_regs st) REAL_VF HSB).
  1-7: cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending]; first [reflexivity | symmetry; assumption].
  - unfold vp_regs. repeat (apply Forall_cons; [cbn [fst]; discriminate|]). apply Forall_nil.
  -
    intros x. cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending]. rewrite RGA.
    pose proof (GlueA.TwinB.getr_RA bsegs OPS E' st3 msB mo' HSB x) as GX. rewrite MB1 in GX. unfold getr in GX.
    unfold vp_regs.
    destruct x; cbv [HalfFX.TwinB.HalfFX.lookup_regs r5_eqb r5_to_Z Z.eqb Pos.eqb];
      try (match goal with |- _ = den E' (rf_get (s_rf st3) _) => rewrite <- GX; reflexivity end).
    all: idtac "REG".
    +   reflexivity.
    +   change (den E' (sv_alu ALU_ADD (getr st X2) (VL NEG96))) with (den E' (vp_sp st)). rewrite DSP. reflexivity.
    +   transitivity (AP.getr R (reg_of_r5 X10)); [reflexivity | symmetry; exact (DR X10)].
    +   reflexivity.
    +   transitivity (AP.getr R (reg_of_r5 X10)); [reflexivity | symmetry; exact (DR X10)].
    +   transitivity (AP.getr R (reg_of_r5 X11)); [reflexivity | symmetry; exact (DR X11)].
    +   transitivity (AP.getr R (reg_of_r5 X11)); [reflexivity | symmetry; exact (DR X11)].
Qed.
End Leaf.
End TwinB.
