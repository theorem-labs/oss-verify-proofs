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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import MemcpyC MemOps MemsetFX MemcpyFX RangePre MemcpySound MemsetPost PubImg MemcpyPC MemcpyPSound PubView.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPost.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA MemcpyC MemcpyPC.
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

Lemma amemcpyp_leaf_ok : MemcpyPSound.amemcpyp_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold MemcpyPSound.amemcpyp_leaf.
  intros st sts K E ms mo r hargs wnl st1 a srcv sofs n L RNG sta LBa aw src HS HPB HK PRE G10 G11 G12 WTA WTN NR CPY CP FS CF AH MI BOT LO SPT
         PW0 NPRIV HI1 POS1 DISJ EA0 EA1 EA2 LSRC ms' mo' HQ HMP' HMI' OTH ACP.
  pose proof (in_pubw_bounds _ _ PW0) as [LOW0 HI0].
  set (R := ms_regs ms) in *. set (len := to_Z (wl n)) in *.
  set (A0 := to_Z (wl a)) in *. set (A1 := bv_unsigned (den E srcv)) in *.
  assert (A1pos : 0 <= A1) by (unfold A1; pose proof (bv_unsigned_in_range 64 (den E srcv)); lia).
  destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & DSTP & SRCP).
  rewrite EA0, EA2 in MU, DSTP. rewrite EA1 in SRCP.
  pose proof atop_range as ATR.
  match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
  set (Fv := CtrFree.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.E' E st Fv Gv).
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.reg_of_X1, (GlueA.getr_RA asegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.den_wlit. }
  assert (EMS' : ms' = CtrFrame.ms' ms r R' m').
  { rewrite EMS. unfold CtrFrame.ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
    - pose proof (int_range r) as RR. rewrite two63_eq in RR. lia.
    - pose proof (HeapCtr.call_pre_even st r CP) as EV.
      pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
  destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  assert (RVN : s_resv st = RNone) by (unfold call_pre in CP; destruct (s_resv st); try discriminate CP; reflexivity).
  assert (VBd : sv_vars_below (s_next st) (VL a) = true) by reflexivity.
  pose proof (HeapCtr.fresh_ok_inv st FOK) as (SVB & _).
  assert (RFB : rf_allb (sv_vars_below (s_next st)) (s_rf st) = true).
  { unfold st_vars_below in SVB. do 5 (apply andb_prop in SVB as [SVB _]). exact SVB. }
  assert (VBs : sv_vars_below (s_next st) srcv = true) by (rewrite <- G11; exact (PlanS.rf_allb_get _ _ _ RFB X11)).
  assert (DVP : den E' (VL a) = AP.getr R' 10%bv).
  { unfold E'. rewrite (CtrFrame.den_E' E st Fv Gv _ VBd), <- G10. symmetry. exact (GlueA.getr_RA asegs OPS E st ms mo HS X10). }
  assert (DA0 : bv_unsigned (den E' (VL a)) = A0) by (rewrite DVP; exact EA0).
  assert (DA1 : bv_unsigned (den E' srcv) = A1).
  { unfold E'. rewrite (CtrFrame.den_E' E st Fv Gv _ VBs). reflexivity. }
  assert (POS0 : A0 + len <= ATOP \/ bv_unsigned (AP.getr R 2) <= A0) by (left; lia).

  pose proof (phaseA_ms AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' A0 len 2240 (VL a) (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT
                ltac:(lia) POS0 ltac:(lia) MU WM MI MINV' STK'
                ltac:(intros rg Hrg; unfold CtrFrame.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                DVP OTH HMI' ACP) as HSA.
  fold Fv Gv E' in HSA.
  assert (SH2 : setpc (setr (clobber st1) X10 (VL a)) r
              = SS r (rf_set (s_rf (clobber st1)) X10 (VL a)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1))).
  { rewrite <- FF1, <- RV1, <- FS1, <- OP1, <- PV1, <- FF, <- RV, <- RG, <- FS0, <- OP, <- PV. destruct (clobber st1); reflexivity. }
  unfold copy_post_p in CPY. rewrite SH2 in CPY.
  match type of CPY with match ?cbx with _ => _ end = _ => destruct cbx as [stn|] eqn:CBY; [|discriminate CPY] end. injection CPY as <-.
  destruct (MemcpyFX.copy_bytes_sound asegs OPS _ 0%uint63 srcv (VL a) sofs (wl a) (wl n) _ stn E' _ mo' HSA RVN eq_refl CBY
              ltac:(change (to_Z 0%uint63) with 0; fold len; lia) ltac:(rewrite DA0; fold len; unfold two64 in *; lia)
              ltac:(rewrite DA1; fold len; unfold two64; lia) ltac:(rewrite DA0, DA1; fold len; exact DISJ))
    as (mc & HSc & FRc & INc & MONOc & _ & _ & _ & _ & _ & _ & PRIVc & _).
  rewrite DA0 in FRc, INc. rewrite DA1 in INc. fold len in FRc, INc. change (to_Z 0%uint63) with 0 in FRc, INc. cbn [ms_mem CtrFrame.ms'] in FRc, INc.
  cbn [s_priv] in PRIVc.

  assert (SRCV : forall j, 0 <= j < len -> rb asegs m' (A1 + j) = nth_error src (Z.to_nat j)).
  { intros j Hj. destruct SRCP as (_ & _ & BY). rewrite (GlueA.rb_mrdA asegs). replace (A1 + j) with (A1 + Z.of_nat (Z.to_nat j)) by lia. apply BY. lia. }
  assert (DSTV : forall j, 0 <= j < len -> rb asegs m' (A0 + j) = nth_error src (Z.to_nat j)).
  { intros j Hj. destruct DSTP as [[_ (_ & _ & BY)] _]. rewrite (GlueA.rb_mrdA asegs). replace (A0 + j) with (A0 + Z.of_nat (Z.to_nat j)) by lia.
    rewrite (BY (Z.to_nat j)); [cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. lia. }

  apply (HK stn ltac:(left; reflexivity) E' ms' mo' (CtrFrame.EXT E st Fv Gv) HMP').
  rewrite EMS'.
  change (CtrFrame.ms' ms r R' m') with (ms_with_mem (ms_with_mem (CtrFrame.ms' ms r R' (mjoinR A0 (A0 + len) (ms_mem ms) m')) mc) m').
  apply (st_ok_view_ext AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_frame_other AI_frame_top
           E' stn (ms_with_mem (CtrFrame.ms' ms r R' (mjoinR A0 (A0 + len) (ms_mem ms) m')) mc) mo' m' A0 (A0 + len) HSc).
  -
    intros x Hx NIN. cbn [ms_mem ms_with_mem ms_upd]. rewrite (FRc x Hx ltac:(lia)).
    change (ms_mem (CtrFrame.ms' ms r R' (mjoinR A0 (A0 + len) (ms_mem ms) m'))) with (mjoinR A0 (A0 + len) (ms_mem ms) m').
    symmetry. apply (mjr_final (ms_mem ms) m' A0 len x); [unfold two64 in Hx; lia| exact NIN].
  -
    intros x Hx. cbn [ms_mem ms_with_mem ms_upd]. set (j := x - A0). replace x with (A0 + j) by (unfold j; lia).
    assert (Hj : 0 <= j < len) by (unfold j; lia).
    destruct (INc j Hj) as (b & RBJ & MCJ).
    change (ms_mem (CtrFrame.ms' ms r R' (mjoinR A0 (A0 + len) (ms_mem ms) m'))) with (mjoinR A0 (A0 + len) (ms_mem ms) m') in RBJ.
    assert (EJ : mjoinR A0 (A0 + len) (ms_mem ms) m' (Z_to_bv 64 (A1 + j)) = m' (Z_to_bv 64 (A1 + j))).
    { unfold mjoinR, in_rng. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus in *; lia).
      assert (NIN : ((A0 <=? A1 + j) && (A1 + j <? A0 + len))%bool = false).
      { apply andb_false_iff. destruct DISJ as [Q|Q]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
      rewrite NIN. reflexivity. }
    rewrite (ReadPost.rb_ext m' _ (A1 + j) EJ) in RBJ. rewrite (SRCV j Hj) in RBJ.
    rewrite (DSTV j Hj), RBJ. rewrite MemP.rb_unfold, MCJ. reflexivity.
  - exact PW0.
  - intros x Hx. rewrite PRIVc. exact (NPRIV x Hx).
  - exact MINV'.
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

Import MemcpyC.TwinB MemOps.TwinB MemsetFX.TwinB MemcpyFX.TwinB RangePre.TwinB MemcpySound.TwinB MemsetPost.TwinB PubImg.TwinB MemcpyPC.TwinB MemcpyPSound.TwinB PubView.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA MemcpyC.TwinB.MemcpyC MemcpyPC.TwinB.MemcpyPC.
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

Lemma amemcpyp_leaf_ok : MemcpyPSound.TwinB.amemcpyp_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold MemcpyPSound.TwinB.amemcpyp_leaf.
  intros st sts K E ms mo r hargs wnl st1 a srcv sofs n L RNG sta LBa aw src HS HPB HK PRE G10 G11 G12 WTA WTN NR CPY CP FS CF AH MI BOT LO SPT
         PW0 NPRIV HI1 POS1 DISJ EA0 EA1 EA2 LSRC ms' mo' HQ HMP' HMI' OTH ACP.
  pose proof (in_pubw_bounds _ _ PW0) as [LOW0 HI0].
  set (R := ms_regs ms) in *. set (len := to_Z (wl n)) in *.
  set (A0 := to_Z (wl a)) in *. set (A1 := bv_unsigned (den E srcv)) in *.
  assert (A1pos : 0 <= A1) by (unfold A1; pose proof (bv_unsigned_in_range 64 (den E srcv)); lia).
  destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & DSTP & SRCP).
  rewrite EA0, EA2 in MU, DSTP. rewrite EA1 in SRCP.
  pose proof atop_range as ATR.
  match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
  set (Fv := CtrFree.TwinB.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.TwinB.E' E st Fv Gv).
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X1, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.TwinB.den_wlit. }
  assert (EMS' : ms' = CtrFrame.TwinB.ms' ms r R' m').
  { rewrite EMS. unfold CtrFrame.TwinB.ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
    - pose proof (int_range r) as RR. rewrite two63_eq in RR. lia.
    - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EV.
      pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
  destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  assert (RVN : s_resv st = RNone) by (unfold call_pre in CP; destruct (s_resv st); try discriminate CP; reflexivity).
  assert (VBd : sv_vars_below (s_next st) (VL a) = true) by reflexivity.
  pose proof (HeapCtr.TwinB.fresh_ok_inv st FOK) as (SVB & _).
  assert (RFB : rf_allb (sv_vars_below (s_next st)) (s_rf st) = true).
  { unfold st_vars_below in SVB. do 5 (apply andb_prop in SVB as [SVB _]). exact SVB. }
  assert (VBs : sv_vars_below (s_next st) srcv = true) by (rewrite <- G11; exact (PlanS.rf_allb_get _ _ _ RFB X11)).
  assert (DVP : den E' (VL a) = AP.getr R' 10%bv).
  { unfold E'. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv _ VBd), <- G10. symmetry. exact (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10). }
  assert (DA0 : bv_unsigned (den E' (VL a)) = A0) by (rewrite DVP; exact EA0).
  assert (DA1 : bv_unsigned (den E' srcv) = A1).
  { unfold E'. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv _ VBs). reflexivity. }
  assert (POS0 : A0 + len <= ATOP \/ bv_unsigned (AP.getr R 2) <= A0) by (left; lia).

  pose proof (phaseA_ms AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' A0 len 2240 (VL a) (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT
                ltac:(lia) POS0 ltac:(lia) MU WM MI MINV' STK'
                ltac:(intros rg Hrg; unfold CtrFrame.TwinB.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                DVP OTH HMI' ACP) as HSA.
  fold Fv Gv E' in HSA.
  assert (SH2 : setpc (setr (clobber st1) X10 (VL a)) r
              = SS r (rf_set (s_rf (clobber st1)) X10 (VL a)) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1))).
  { rewrite <- FF1, <- RV1, <- FS1, <- OP1, <- PV1, <- FF, <- RV, <- RG, <- FS0, <- OP, <- PV. destruct (clobber st1); reflexivity. }
  unfold copy_post_p in CPY. rewrite SH2 in CPY.
  match type of CPY with match ?cbx with _ => _ end = _ => destruct cbx as [stn|] eqn:CBY; [|discriminate CPY] end. injection CPY as <-.
  destruct (MemcpyFX.TwinB.MemcpyFX.copy_bytes_sound bsegs OPS _ 0%uint63 srcv (VL a) sofs (wl a) (wl n) _ stn E' _ mo' HSA RVN eq_refl CBY
              ltac:(change (to_Z 0%uint63) with 0; fold len; lia) ltac:(rewrite DA0; fold len; unfold two64 in *; lia)
              ltac:(rewrite DA1; fold len; unfold two64; lia) ltac:(rewrite DA0, DA1; fold len; exact DISJ))
    as (mc & HSc & FRc & INc & MONOc & _ & _ & _ & _ & _ & _ & PRIVc & _).
  rewrite DA0 in FRc, INc. rewrite DA1 in INc. fold len in FRc, INc. change (to_Z 0%uint63) with 0 in FRc, INc. cbn [ms_mem CtrFrame.TwinB.ms'] in FRc, INc.
  cbn [s_priv] in PRIVc.

  assert (SRCV : forall j, 0 <= j < len -> rb bsegs m' (A1 + j) = nth_error src (Z.to_nat j)).
  { intros j Hj. destruct SRCP as (_ & _ & BY). rewrite (GlueA.TwinB.rb_mrdA bsegs). replace (A1 + j) with (A1 + Z.of_nat (Z.to_nat j)) by lia. apply BY. lia. }
  assert (DSTV : forall j, 0 <= j < len -> rb bsegs m' (A0 + j) = nth_error src (Z.to_nat j)).
  { intros j Hj. destruct DSTP as [[_ (_ & _ & BY)] _]. rewrite (GlueA.TwinB.rb_mrdA bsegs). replace (A0 + j) with (A0 + Z.of_nat (Z.to_nat j)) by lia.
    rewrite (BY (Z.to_nat j)); [cbn [cells_bytes cbytes]; rewrite app_nil_r; reflexivity|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. lia. }

  apply (HK stn ltac:(left; reflexivity) E' ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) HMP').
  rewrite EMS'.
  change (CtrFrame.TwinB.ms' ms r R' m') with (ms_with_mem (ms_with_mem (CtrFrame.TwinB.ms' ms r R' (mjoinR A0 (A0 + len) (ms_mem ms) m')) mc) m').
  apply (st_ok_view_ext AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_frame_other AI_frame_top
           E' stn (ms_with_mem (CtrFrame.TwinB.ms' ms r R' (mjoinR A0 (A0 + len) (ms_mem ms) m')) mc) mo' m' A0 (A0 + len) HSc).
  -
    intros x Hx NIN. cbn [ms_mem ms_with_mem ms_upd]. rewrite (FRc x Hx ltac:(lia)).
    change (ms_mem (CtrFrame.TwinB.ms' ms r R' (mjoinR A0 (A0 + len) (ms_mem ms) m'))) with (mjoinR A0 (A0 + len) (ms_mem ms) m').
    symmetry. apply (mjr_final (ms_mem ms) m' A0 len x); [unfold two64 in Hx; lia| exact NIN].
  -
    intros x Hx. cbn [ms_mem ms_with_mem ms_upd]. set (j := x - A0). replace x with (A0 + j) by (unfold j; lia).
    assert (Hj : 0 <= j < len) by (unfold j; lia).
    destruct (INc j Hj) as (b & RBJ & MCJ).
    change (ms_mem (CtrFrame.TwinB.ms' ms r R' (mjoinR A0 (A0 + len) (ms_mem ms) m'))) with (mjoinR A0 (A0 + len) (ms_mem ms) m') in RBJ.
    assert (EJ : mjoinR A0 (A0 + len) (ms_mem ms) m' (Z_to_bv 64 (A1 + j)) = m' (Z_to_bv 64 (A1 + j))).
    { unfold mjoinR, in_rng. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus in *; lia).
      assert (NIN : ((A0 <=? A1 + j) && (A1 + j <? A0 + len))%bool = false).
      { apply andb_false_iff. destruct DISJ as [Q|Q]; [left; apply Z.leb_gt; lia | right; apply Z.ltb_ge; lia]. }
      rewrite NIN. reflexivity. }
    rewrite (ReadPost.TwinB.rb_ext m' _ (A1 + j) EJ) in RBJ. rewrite (SRCV j Hj) in RBJ.
    rewrite (DSTV j Hj), RBJ. rewrite MemP.rb_unfold, MCJ. reflexivity.
  - exact PW0.
  - intros x Hx. rewrite PRIVc. exact (NPRIV x Hx).
  - exact MINV'.
Qed.
End Leaf.
End TwinB.
