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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import MemOps MemsetFX RangePre MemsetPost FprintfSC StrnlenC StrnlenSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_fwrite.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import StrFun.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPost.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA StrnlenC.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module IS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_fwrite.I_strnlen.

Lemma setpc_addfact : forall X f r, setpc (addfact X f) r = addfact (setpc X r) f.
Proof. reflexivity. Qed.

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

Lemma astrnlen_leaf_ok : StrnlenSound.astrnlen_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold StrnlenSound.astrnlen_leaf.
  intros st K E ms mo r hargs wnl st1 k m rs j sstr slack L RNG sta LBa aw HS HPB HK PRE G10 G11 Hks Bj HIZ NONUL CP FS CF AH MI BOT LO LOR SPT EN LEN
         ms' mo' HQ HMP' HMI' OTH ACP.
  set (R := ms_regs ms) in *.
  destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & BYT').
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
  idtac "SL-1".

  set (NS := Z.of_nat (length sstr) + 1) in *.
  pose proof (bv_unsigned_in_range _ (den E (rg_hi rs))) as RNS. change (bv_unsigned (den E (rg_hi rs))) with (hiZ E rs) in RNS. rewrite HIZ in RNS.
  unfold bv_modulus in RNS. change (2 ^ Z.of_N 64) with (2 ^ 64) in RNS.
  assert (RES : strnlen_res (bv_unsigned (AP.getr R 11)) (sstr ++ Z_to_bv 8 0 :: slack) = NS - 1).
  { rewrite (strnlen_res_cstr 0 _ sstr slack NONUL). rewrite EN. unfold NS in *. lia. }
  destruct (CtrFrame.reg_E' OPS E st ms mo HS FOK Fv Gv k rs Hks) as (EVk & EHk & _ & _). fold E' in EVk, EHk.
  assert (EL : den E' (sv_alu ALU_SUB (rg_hi rs) (VL wone)) = Z_to_bv 64 (NS - 1)).
  { rewrite ValP.den_sv_alu. cbn [alu64 alu]. apply bv_eq. rewrite bv_sub_unsigned, unsigned_VL, Z_to_bv_unsigned.
    change (bv_unsigned (den E' (rg_hi rs))) with (hiZ E' rs). rewrite EHk, HIZ. change (w2Z wone) with 1. reflexivity. }
  assert (DV : den E' (sv_alu ALU_SUB (rg_hi rs) (VL wone)) = AP.getr R' 10%bv).
  { rewrite EL, <- RES. reflexivity. }
  idtac "SL-2".

  assert (MU0 : munch [(bv_unsigned (AP.getr R 2) - 4384, bv_unsigned (AP.getr R 2)); (0, 0 + 0)]%Z (ms_mem ms) m').
  { intros x OUT. apply MU. cbn [outside] in OUT |- *. tauto. }
  pose proof (phaseA_ms_g AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' 0 0 4384 (sv_alu ALU_SUB (rg_hi rs) (VL wone)) (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT
                ltac:(lia) ltac:(left; lia) ltac:(split; [lia| exact LOR]) MU0 WM MI MINV' STK'
                ltac:(intros rg Hrg; unfold CtrFrame.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                DV OTH HMI' ACP) as HSA.
  fold Fv Gv E' in HSA.
  assert (PW0 : forall x, m' x = ms_mem (CtrFrame.ms' ms r R' (mjoinR 0 (0 + 0) (ms_mem ms) m')) x).
  { intros x. change (ms_mem (CtrFrame.ms' ms r R' (mjoinR 0 (0 + 0) (ms_mem ms) m')) x) with (mjoinR 0 (0 + 0) (ms_mem ms) m' x).
    unfold mjoinR, in_rng. replace ((0 <=? bv_unsigned x) && (bv_unsigned x <? 0 + 0))%bool with false; [reflexivity|].
    symmetry. apply andb_false_iff. right. apply Z.ltb_ge. pose proof (bv_unsigned_in_range _ x). lia. }
  pose proof (st_ok_mem_ext_g OPS E' _ _ mo' m' PW0 HSA) as HS1.
  idtac "SL-3".

  assert (F1 : fact_holds E' (FULt (sv_alu ALU_SUB (rg_hi rs) (VL wone)) (rg_hi rs))).
  { cbn [fact_holds]. rewrite EL, Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); unfold NS in *; lia).
    change (bv_unsigned (den E' (rg_hi rs))) with (hiZ E' rs). rewrite EHk, HIZ. lia. }
  assert (F2 : fact_holds E' (FULt (sv_alu ALU_SUB (rg_hi rs) (VL wone)) (VL m))).
  { cbn [fact_holds]. rewrite EL, Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); unfold NS in *; lia).
    rewrite unsigned_VL. unfold NS in *. lia. }
  assert (F3 : fact_holds E' (FEq (sv_ext false 0%uint63 1%uint63 (VBlob false j (sv_alu ALU_SUB (rg_hi rs) (VL wone)) 1%uint63)) (VL wzero))).
  { cbn [fact_holds]. rewrite ValP.den_sv_ext by (unfold width_ok; change (to_Z 0%uint63) with 0; change (to_Z 1%uint63) with 1; lia).
    cbn [den]. rewrite EL, Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); unfold NS in *; lia).
    unfold E', CtrFrame.E'. rewrite eb_above. rewrite Bj. unfold blob_bytes. change (to_Z 1%uint63) with 1. change (to_Z 0%uint63) with 0.
    replace (Z.to_nat (NS - 1)) with (length sstr) by (unfold NS; lia). rewrite skipn_app, skipn_all, Nat.sub_diag. cbn. reflexivity. }
  pose proof (MemFX.MemFX.addfact_sound asegs OPS E' _ _ mo' _ (MemFX.MemFX.addfact_sound asegs OPS E' _ _ mo' _ (MemFX.MemFX.addfact_sound asegs OPS E' _ _ mo' _ HS1 F1) F2) F3) as HS3.
  idtac "SL-4".

  assert (SH2 : setpc (setr (clobber st1) X10 (sv_alu ALU_SUB (rg_hi rs) (VL wone))) r
              = SS r (rf_set (s_rf (clobber st1)) X10 (sv_alu ALU_SUB (rg_hi rs) (VL wone))) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1))).
  { rewrite <- FF1, <- RV1, <- FS1, <- OP1, <- PV1, <- FF, <- RV, <- RG, <- FS0, <- OP, <- PV. destruct (clobber st1); reflexivity. }
  apply (HK _ (or_introl eq_refl) E' ms' mo' (CtrFrame.EXT E st Fv Gv) HMP').
  rewrite EMS'. unfold strnlen_post. rewrite !setpc_addfact, SH2. exact HS3.
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

Import MemOps.TwinB MemsetFX.TwinB RangePre.TwinB MemsetPost.TwinB FprintfSC.TwinB StrnlenC.TwinB StrnlenSound.TwinB.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA StrnlenC.TwinB.StrnlenC.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.
Module IS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_fwrite.TwinB.I_strnlen.

Lemma setpc_addfact : forall X f r, setpc (addfact X f) r = addfact (setpc X r) f.
Proof. reflexivity. Qed.

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

Lemma astrnlen_leaf_ok : StrnlenSound.TwinB.astrnlen_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold StrnlenSound.TwinB.astrnlen_leaf.
  intros st K E ms mo r hargs wnl st1 k m rs j sstr slack L RNG sta LBa aw HS HPB HK PRE G10 G11 Hks Bj HIZ NONUL CP FS CF AH MI BOT LO LOR SPT EN LEN
         ms' mo' HQ HMP' HMI' OTH ACP.
  set (R := ms_regs ms) in *.
  destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & BYT').
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
  idtac "SL-1".

  set (NS := Z.of_nat (length sstr) + 1) in *.
  pose proof (bv_unsigned_in_range _ (den E (rg_hi rs))) as RNS. change (bv_unsigned (den E (rg_hi rs))) with (hiZ E rs) in RNS. rewrite HIZ in RNS.
  unfold bv_modulus in RNS. change (2 ^ Z.of_N 64) with (2 ^ 64) in RNS.
  assert (RES : strnlen_res (bv_unsigned (AP.getr R 11)) (sstr ++ Z_to_bv 8 0 :: slack) = NS - 1).
  { rewrite (strnlen_res_cstr 0 _ sstr slack NONUL). rewrite EN. unfold NS in *. lia. }
  destruct (CtrFrame.TwinB.reg_E' OPS E st ms mo HS FOK Fv Gv k rs Hks) as (EVk & EHk & _ & _). fold E' in EVk, EHk.
  assert (EL : den E' (sv_alu ALU_SUB (rg_hi rs) (VL wone)) = Z_to_bv 64 (NS - 1)).
  { rewrite ValP.den_sv_alu. cbn [alu64 alu]. apply bv_eq. rewrite bv_sub_unsigned, unsigned_VL, Z_to_bv_unsigned.
    change (bv_unsigned (den E' (rg_hi rs))) with (hiZ E' rs). rewrite EHk, HIZ. change (w2Z wone) with 1. reflexivity. }
  assert (DV : den E' (sv_alu ALU_SUB (rg_hi rs) (VL wone)) = AP.getr R' 10%bv).
  { rewrite EL, <- RES. reflexivity. }
  idtac "SL-2".

  assert (MU0 : munch [(bv_unsigned (AP.getr R 2) - 4384, bv_unsigned (AP.getr R 2)); (0, 0 + 0)]%Z (ms_mem ms) m').
  { intros x OUT. apply MU. cbn [outside] in OUT |- *. tauto. }
  pose proof (phaseA_ms_g AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' 0 0 4384 (sv_alu ALU_SUB (rg_hi rs) (VL wone)) (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT
                ltac:(lia) ltac:(left; lia) ltac:(split; [lia| exact LOR]) MU0 WM MI MINV' STK'
                ltac:(intros rg Hrg; unfold CtrFrame.TwinB.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                DV OTH HMI' ACP) as HSA.
  fold Fv Gv E' in HSA.
  assert (PW0 : forall x, m' x = ms_mem (CtrFrame.TwinB.ms' ms r R' (mjoinR 0 (0 + 0) (ms_mem ms) m')) x).
  { intros x. change (ms_mem (CtrFrame.TwinB.ms' ms r R' (mjoinR 0 (0 + 0) (ms_mem ms) m')) x) with (mjoinR 0 (0 + 0) (ms_mem ms) m' x).
    unfold mjoinR, in_rng. replace ((0 <=? bv_unsigned x) && (bv_unsigned x <? 0 + 0))%bool with false; [reflexivity|].
    symmetry. apply andb_false_iff. right. apply Z.ltb_ge. pose proof (bv_unsigned_in_range _ x). lia. }
  pose proof (st_ok_mem_ext_g OPS E' _ _ mo' m' PW0 HSA) as HS1.
  idtac "SL-3".

  assert (F1 : fact_holds E' (FULt (sv_alu ALU_SUB (rg_hi rs) (VL wone)) (rg_hi rs))).
  { cbn [fact_holds]. rewrite EL, Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); unfold NS in *; lia).
    change (bv_unsigned (den E' (rg_hi rs))) with (hiZ E' rs). rewrite EHk, HIZ. lia. }
  assert (F2 : fact_holds E' (FULt (sv_alu ALU_SUB (rg_hi rs) (VL wone)) (VL m))).
  { cbn [fact_holds]. rewrite EL, Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); unfold NS in *; lia).
    rewrite unsigned_VL. unfold NS in *. lia. }
  assert (F3 : fact_holds E' (FEq (sv_ext false 0%uint63 1%uint63 (VBlob false j (sv_alu ALU_SUB (rg_hi rs) (VL wone)) 1%uint63)) (VL wzero))).
  { cbn [fact_holds]. rewrite ValP.den_sv_ext by (unfold width_ok; change (to_Z 0%uint63) with 0; change (to_Z 1%uint63) with 1; lia).
    cbn [den]. rewrite EL, Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); unfold NS in *; lia).
    unfold E', CtrFrame.TwinB.E'. rewrite eb_above. rewrite Bj. unfold blob_bytes. change (to_Z 1%uint63) with 1. change (to_Z 0%uint63) with 0.
    replace (Z.to_nat (NS - 1)) with (length sstr) by (unfold NS; lia). rewrite skipn_app, skipn_all, Nat.sub_diag. cbn. reflexivity. }
  pose proof (MemFX.MemFX.addfact_sound bsegs OPS E' _ _ mo' _ (MemFX.MemFX.addfact_sound bsegs OPS E' _ _ mo' _ (MemFX.MemFX.addfact_sound bsegs OPS E' _ _ mo' _ HS1 F1) F2) F3) as HS3.
  idtac "SL-4".

  assert (SH2 : setpc (setr (clobber st1) X10 (sv_alu ALU_SUB (rg_hi rs) (VL wone))) r
              = SS r (rf_set (s_rf (clobber st1)) X10 (sv_alu ALU_SUB (rg_hi rs) (VL wone))) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1))).
  { rewrite <- FF1, <- RV1, <- FS1, <- OP1, <- PV1, <- FF, <- RV, <- RG, <- FS0, <- OP, <- PV. destruct (clobber st1); reflexivity. }
  apply (HK _ (or_introl eq_refl) E' ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) HMP').
  rewrite EMS'. unfold strnlen_post. rewrite !setpc_addfact, SH2. exact HS3.
Qed.
End Leaf.
End TwinB.
