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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_fwrite.
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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import HalfC HalfFX MemOps MemsetFX MemcpyFX RangePre MemsetPost HalfPost VprintfC FwritePostC FwritePostSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPost.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPost.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA HalfC FwritePostC.
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

Lemma afwrite_post_leaf_ok : FwritePostSound.afwrite_post_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold FwritePostSound.afwrite_post_leaf.
  intros st K E ms mo r hargs wnl st1 ks o8 res v5 v4 v3 v2 v1 v0 rav L RNG sta LBa aw s5v s4v s3v s2v s1v s0v ravv HS HPB HK PRE G8 G10
         L0 L1 L2 L3 L4 L5 L6 WRAV RAVLT RAVEV CP FS CF AH MI BOT LO SPT F1 F2 F3 ms' mo' HQ HMP' HMI' OTH ACP.
  set (R := ms_regs ms) in *. set (spm := bv_unsigned (AP.getr R 2)) in *. set (sp0 := bv_unsigned (AP.getr R 8)) in *.
  destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK').
  fold sp0 in MU, STK'.
  pose proof atop_range as ATR.
  match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
  set (RA := mixR R R'). set (Fv := CtrFree.cfvF RA). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.E' E st Fv Gv).
  set (st2 := setpc (setr (clobber st1) X10 (VL res)) r) in *.
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & _).
  pose proof (HeapCtr.fresh_ok_inv st FOK) as (SVB & _).
  assert (RFB : rf_allb (sv_vars_below (s_next st)) (s_rf st) = true).
  { unfold st_vars_below in SVB. do 5 (apply andb_prop in SVB as [SVB _]). exact SVB. }
  assert (DR : forall x, den E' (getr st x) = AP.getr R (reg_of_r5 x)).
  { intros x. unfold E', getr. rewrite (CtrFrame.den_E' E st Fv Gv _ (PlanS.rf_allb_get _ _ _ RFB x)). symmetry. exact (GlueA.getr_RA asegs OPS E st ms mo HS x). }
  assert (DFP : den E' (VP ks o8) = AP.getr R 8) by (rewrite <- G8; exact (DR X8)).

  assert (MU80 : munch [(spm - 80, spm)]%Z (ms_mem ms) m').
  { intros x OUT. apply MU. cbn [outside] in OUT |- *. lia. }
  assert (STKM : stk asegs m' (CtrPre.sp_lo E st) spm) by (apply (proj1 (stk_split asegs m' _ spm _ STK' ltac:(lia)))).
  idtac "PL-1".
  destruct (half_leaf_B1 AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img MP
              st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' 80 (VL res) (VP ks o8) [] st2 HS CP FS CF AH BOT LO SPT
              ltac:(lia) MU80 WM MI MINV' STKM ltac:(reflexivity) OTH HMI' ACP eq_refl ltac:(intros off v []))
    as (msB & HSB & MB1 & MB2 & MB3 & MB4 & MB5 & MB6 & MB7 & SRF & SFF & SRV & SFA & SOP & SPV & SNX).
  idtac "PL-2".

  assert (LOAD : forall (i : int) (k : nat) v (w : word), to_Z i <= 6 -> k = Z.to_nat (8 * to_Z i) ->
            load8 asegs st2 (cell_addr (VP ks o8) i) = Some v ->
            cell_at [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ravv] k = Some (C8 w) -> den E' v = w).
  { intros i k v w Hi -> LD CA. pose proof (int_range i) as Ri. unfold load8 in LD.
    destruct (do_load asegs st2 (cell_addr (VP ks o8) i) 8%uint63 false) as [[v'|]|] eqn:DL; try discriminate LD. injection LD as ->.
    destruct (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem.StepM.do_load_sound asegs OPS E' st2 msB mo' _ 8%uint63 false v HSB ltac:(right; right; right; reflexivity) DL) as (bs & LEN & OV & DV).
    rewrite MB7 in OV. change (Z.to_nat (to_Z 8%uint63)) with 8%nat in OV, LEN. change (to_Z 8%uint63) with 8 in DV.

    assert (DA : den E' (cell_addr (VP ks o8) i) = Z_to_bv 64 (sp0 - 56 + 8 * to_Z i)).
    { unfold cell_addr. rewrite den_sv_alu. cbn [alu64 alu den]. fold (den E' (VP ks o8)). rewrite DFP.
      apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned, wbv_unsigned, wsub_ok, !wlit_ok. fold sp0.
      rewrite Uint63.mul_spec. change (to_Z 8%uint63) with 8. rewrite (Z.mod_small (8 * to_Z i)) by (change wB with (2 ^ 63); lia).
      unfold bv_wrap, bv_modulus, two64. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. change (to_Z 56%uint63) with 56. f_equal. lia. }
    rewrite DA in OV.

    pose proof (AS.rw_cells_read asegs (ms_mem ms) _ _ (Z.to_nat (8 * to_Z i)) (C8 w) F3 CA) as OVm. cbn [csize cbytes] in OVm. unfold AM.wa in OVm.
    rewrite Z2Nat.id in OVm by lia. fold sp0 in OVm.
    destruct (MemcpyFX.ov_read_bytes_inv asegs (ms_mem ms) (sp0 - 56 + 8 * to_Z i) 8 _ OVm ltac:(lia) ltac:(unfold two64; lia)) as [_ RBm].
    assert (OV' : ov_read_bytes asegs m' (Z_to_bv 64 (sp0 - 56 + 8 * to_Z i)) 8 = Some (AM.le8 w)).
    { apply MemP.ov_read_bytes_rb; [lia | unfold two64; lia | | apply AM.length_le8].
      intros t Ht. rewrite <- (RBm t Ht). apply ReadPost.rb_ext. refine (MU (Z_to_bv 64 _) _).
      rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia). cbn [outside]. lia. }
    rewrite OV' in OV. injection OV as <-. rewrite DV, ValP.ext_word_id64. apply AM.le_bytes_to_word_le8. }
  pose proof (LOAD 0%uint63 _ v5 s5v ltac:(change (to_Z 0%uint63) with 0; lia) eq_refl L0 eq_refl) as D5.
  pose proof (LOAD 1%uint63 _ v4 s4v ltac:(change (to_Z 1%uint63) with 1; lia) eq_refl L1 eq_refl) as D4.
  pose proof (LOAD 2%uint63 _ v3 s3v ltac:(change (to_Z 2%uint63) with 2; lia) eq_refl L2 eq_refl) as D3.
  pose proof (LOAD 3%uint63 _ v2 s2v ltac:(change (to_Z 3%uint63) with 3; lia) eq_refl L3 eq_refl) as D2.
  pose proof (LOAD 4%uint63 _ v1 s1v ltac:(change (to_Z 4%uint63) with 4; lia) eq_refl L4 eq_refl) as D1.
  pose proof (LOAD 5%uint63 _ v0 s0v ltac:(change (to_Z 5%uint63) with 5; lia) eq_refl L5 eq_refl) as D0.
  pose proof (LOAD 6%uint63 _ (VL rav) ravv ltac:(change (to_Z 6%uint63) with 6; lia) eq_refl L6 eq_refl) as DRA.
  idtac "PL-3".

  assert (ERA : ravv = Z_to_bv 64 (to_Z (wl rav))).
  { rewrite <- DRA. cbn [den]. unfold wbv, w2Z. rewrite WRAV. reflexivity. }
  assert (EPC : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState.ret_pc ravv = Z_to_bv 64 (to_Z (wl rav))).
  { rewrite ERA. apply OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState.ret_pc_even; [pose proof (int_range (wl rav)); lia|].
    pose proof (land_mk (wl rav) 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite RAVEV in LM. change (to_Z 0%uint63) with 0 in LM.
    change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }

  assert (RGA : forall (RR : bvmap 5 word) F0 pc0 fc0 rv0 x, rget (Core RR F0 pc0 fc0 rv0) (reg_of_r5 x) = AP.getr RR (reg_of_r5 x)).
  { intros RR F0 pc0 fc0 rv0 x. unfold rget, AP.getr. cbn [c_regs]. destruct x; reflexivity. }
  apply (HK _ ltac:(left; reflexivity) E' ms' mo' (CtrFrame.EXT E st Fv Gv) HMP').
  subst ms'.
  apply (HalfFX.st_ok_set_regs_pc asegs OPS E' st2 msB _ mo' (fwp_regs (VP ks o8) rav v5 v4 v3 v2 v1 v0) (wl rav) HSB).
  1-7: cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending]; first [exact EPC | reflexivity | symmetry; assumption].
  - unfold fwp_regs. repeat (apply Forall_cons; [cbn [fst]; discriminate|]). apply Forall_nil.
  -
    intros x. cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending]. rewrite RGA.
    pose proof (GlueA.getr_RA asegs OPS E' st2 msB mo' HSB x) as GX. rewrite MB1 in GX. unfold getr in GX.
    unfold fwp_regs.
    destruct x; cbv [HalfFX.lookup_regs r5_eqb r5_to_Z Z.eqb Pos.eqb];
      try (match goal with |- _ = den E' (rf_get (s_rf st2) _) => rewrite <- GX; reflexivity end).
    all: idtac "REG".
    +   rewrite DRA. reflexivity.
    +   rewrite DFP. reflexivity.
    +   rewrite D0. reflexivity.
    +   rewrite D1. reflexivity.
    +   rewrite D2. reflexivity.
    +   rewrite D3. reflexivity.
    +   rewrite D4. reflexivity.
    +   rewrite D5. reflexivity.
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

Import HalfC.TwinB HalfFX.TwinB MemOps.TwinB MemsetFX.TwinB MemcpyFX.TwinB RangePre.TwinB MemsetPost.TwinB HalfPost.TwinB VprintfC.TwinB FwritePostC.TwinB FwritePostSound.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA HalfC.TwinB.HalfC FwritePostC.TwinB.FwritePostC.
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

Lemma afwrite_post_leaf_ok : FwritePostSound.TwinB.afwrite_post_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold FwritePostSound.TwinB.afwrite_post_leaf.
  intros st K E ms mo r hargs wnl st1 ks o8 res v5 v4 v3 v2 v1 v0 rav L RNG sta LBa aw s5v s4v s3v s2v s1v s0v ravv HS HPB HK PRE G8 G10
         L0 L1 L2 L3 L4 L5 L6 WRAV RAVLT RAVEV CP FS CF AH MI BOT LO SPT F1 F2 F3 ms' mo' HQ HMP' HMI' OTH ACP.
  set (R := ms_regs ms) in *. set (spm := bv_unsigned (AP.getr R 2)) in *. set (sp0 := bv_unsigned (AP.getr R 8)) in *.
  destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK').
  fold sp0 in MU, STK'.
  pose proof atop_range as ATR.
  match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
  set (RA := mixR R R'). set (Fv := CtrFree.TwinB.cfvF RA). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.TwinB.E' E st Fv Gv).
  set (st2 := setpc (setr (clobber st1) X10 (VL res)) r) in *.
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & _).
  pose proof (HeapCtr.TwinB.fresh_ok_inv st FOK) as (SVB & _).
  assert (RFB : rf_allb (sv_vars_below (s_next st)) (s_rf st) = true).
  { unfold st_vars_below in SVB. do 5 (apply andb_prop in SVB as [SVB _]). exact SVB. }
  assert (DR : forall x, den E' (getr st x) = AP.getr R (reg_of_r5 x)).
  { intros x. unfold E', getr. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv _ (PlanS.rf_allb_get _ _ _ RFB x)). symmetry. exact (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS x). }
  assert (DFP : den E' (VP ks o8) = AP.getr R 8) by (rewrite <- G8; exact (DR X8)).

  assert (MU80 : munch [(spm - 80, spm)]%Z (ms_mem ms) m').
  { intros x OUT. apply MU. cbn [outside] in OUT |- *. lia. }
  assert (STKM : stk bsegs m' (CtrPre.TwinB.sp_lo E st) spm) by (apply (proj1 (stk_split bsegs m' _ spm _ STK' ltac:(lia)))).
  idtac "PL-1".
  destruct (half_leaf_B1 AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img MP
              st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' 80 (VL res) (VP ks o8) [] st2 HS CP FS CF AH BOT LO SPT
              ltac:(lia) MU80 WM MI MINV' STKM ltac:(reflexivity) OTH HMI' ACP eq_refl ltac:(intros off v []))
    as (msB & HSB & MB1 & MB2 & MB3 & MB4 & MB5 & MB6 & MB7 & SRF & SFF & SRV & SFA & SOP & SPV & SNX).
  idtac "PL-2".

  assert (LOAD : forall (i : int) (k : nat) v (w : word), to_Z i <= 6 -> k = Z.to_nat (8 * to_Z i) ->
            load8 bsegs st2 (cell_addr (VP ks o8) i) = Some v ->
            cell_at [C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ravv] k = Some (C8 w) -> den E' v = w).
  { intros i k v w Hi -> LD CA. pose proof (int_range i) as Ri. unfold load8 in LD.
    destruct (do_load bsegs st2 (cell_addr (VP ks o8) i) 8%uint63 false) as [[v'|]|] eqn:DL; try discriminate LD. injection LD as ->.
    destruct (OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem.StepM.do_load_sound bsegs OPS E' st2 msB mo' _ 8%uint63 false v HSB ltac:(right; right; right; reflexivity) DL) as (bs & LEN & OV & DV).
    rewrite MB7 in OV. change (Z.to_nat (to_Z 8%uint63)) with 8%nat in OV, LEN. change (to_Z 8%uint63) with 8 in DV.

    assert (DA : den E' (cell_addr (VP ks o8) i) = Z_to_bv 64 (sp0 - 56 + 8 * to_Z i)).
    { unfold cell_addr. rewrite den_sv_alu. cbn [alu64 alu den]. fold (den E' (VP ks o8)). rewrite DFP.
      apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned, wbv_unsigned, wsub_ok, !wlit_ok. fold sp0.
      rewrite Uint63.mul_spec. change (to_Z 8%uint63) with 8. rewrite (Z.mod_small (8 * to_Z i)) by (change wB with (2 ^ 63); lia).
      unfold bv_wrap, bv_modulus, two64. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. change (to_Z 56%uint63) with 56. f_equal. lia. }
    rewrite DA in OV.

    pose proof (AS.rw_cells_read bsegs (ms_mem ms) _ _ (Z.to_nat (8 * to_Z i)) (C8 w) F3 CA) as OVm. cbn [csize cbytes] in OVm. unfold AM.wa in OVm.
    rewrite Z2Nat.id in OVm by lia. fold sp0 in OVm.
    destruct (MemcpyFX.TwinB.MemcpyFX.ov_read_bytes_inv bsegs (ms_mem ms) (sp0 - 56 + 8 * to_Z i) 8 _ OVm ltac:(lia) ltac:(unfold two64; lia)) as [_ RBm].
    assert (OV' : ov_read_bytes bsegs m' (Z_to_bv 64 (sp0 - 56 + 8 * to_Z i)) 8 = Some (AM.le8 w)).
    { apply MemP.ov_read_bytes_rb; [lia | unfold two64; lia | | apply AM.length_le8].
      intros t Ht. rewrite <- (RBm t Ht). apply ReadPost.TwinB.rb_ext. refine (MU (Z_to_bv 64 _) _).
      rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia). cbn [outside]. lia. }
    rewrite OV' in OV. injection OV as <-. rewrite DV, ValP.ext_word_id64. apply AM.le_bytes_to_word_le8. }
  pose proof (LOAD 0%uint63 _ v5 s5v ltac:(change (to_Z 0%uint63) with 0; lia) eq_refl L0 eq_refl) as D5.
  pose proof (LOAD 1%uint63 _ v4 s4v ltac:(change (to_Z 1%uint63) with 1; lia) eq_refl L1 eq_refl) as D4.
  pose proof (LOAD 2%uint63 _ v3 s3v ltac:(change (to_Z 2%uint63) with 2; lia) eq_refl L2 eq_refl) as D3.
  pose proof (LOAD 3%uint63 _ v2 s2v ltac:(change (to_Z 3%uint63) with 3; lia) eq_refl L3 eq_refl) as D2.
  pose proof (LOAD 4%uint63 _ v1 s1v ltac:(change (to_Z 4%uint63) with 4; lia) eq_refl L4 eq_refl) as D1.
  pose proof (LOAD 5%uint63 _ v0 s0v ltac:(change (to_Z 5%uint63) with 5; lia) eq_refl L5 eq_refl) as D0.
  pose proof (LOAD 6%uint63 _ (VL rav) ravv ltac:(change (to_Z 6%uint63) with 6; lia) eq_refl L6 eq_refl) as DRA.
  idtac "PL-3".

  assert (ERA : ravv = Z_to_bv 64 (to_Z (wl rav))).
  { rewrite <- DRA. cbn [den]. unfold wbv, w2Z. rewrite WRAV. reflexivity. }
  assert (EPC : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState.ret_pc ravv = Z_to_bv 64 (to_Z (wl rav))).
  { rewrite ERA. apply OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState.ret_pc_even; [pose proof (int_range (wl rav)); lia|].
    pose proof (land_mk (wl rav) 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
    change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite RAVEV in LM. change (to_Z 0%uint63) with 0 in LM.
    change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }

  assert (RGA : forall (RR : bvmap 5 word) F0 pc0 fc0 rv0 x, rget (Core RR F0 pc0 fc0 rv0) (reg_of_r5 x) = AP.getr RR (reg_of_r5 x)).
  { intros RR F0 pc0 fc0 rv0 x. unfold rget, AP.getr. cbn [c_regs]. destruct x; reflexivity. }
  apply (HK _ ltac:(left; reflexivity) E' ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) HMP').
  subst ms'.
  apply (HalfFX.TwinB.HalfFX.st_ok_set_regs_pc bsegs OPS E' st2 msB _ mo' (fwp_regs (VP ks o8) rav v5 v4 v3 v2 v1 v0) (wl rav) HSB).
  1-7: cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending]; first [exact EPC | reflexivity | symmetry; assumption].
  - unfold fwp_regs. repeat (apply Forall_cons; [cbn [fst]; discriminate|]). apply Forall_nil.
  -
    intros x. cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending]. rewrite RGA.
    pose proof (GlueA.TwinB.getr_RA bsegs OPS E' st2 msB mo' HSB x) as GX. rewrite MB1 in GX. unfold getr in GX.
    unfold fwp_regs.
    destruct x; cbv [HalfFX.TwinB.HalfFX.lookup_regs r5_eqb r5_to_Z Z.eqb Pos.eqb];
      try (match goal with |- _ = den E' (rf_get (s_rf st2) _) => rewrite <- GX; reflexivity end).
    all: idtac "REG".
    +   rewrite DRA. reflexivity.
    +   rewrite DFP. reflexivity.
    +   rewrite D0. reflexivity.
    +   rewrite D1. reflexivity.
    +   rewrite D2. reflexivity.
    +   rewrite D3. reflexivity.
    +   rewrite D4. reflexivity.
    +   rewrite D5. reflexivity.
Qed.
End Leaf.
End TwinB.
