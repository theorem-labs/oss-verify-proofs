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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import HalfC HalfFX MemOps MemsetFX MemcpyFX RangePre MemsetPost.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPost.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA HalfC.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Lemma write_ext : forall bs (m1 m2 : amem) a, (forall x, m1 x = m2 x) -> forall x, write_to_mem m1 a bs x = write_to_mem m2 a bs x.
Proof.
  induction bs as [|b bs IH]; intros m1 m2 a H x; cbn [write_to_mem]; [apply H|].
  apply IH. intros y. destruct (bv_eqb y a); [reflexivity| apply H].
Qed.

Lemma push_mem_same : forall cells E (m0 m : amem) base, (forall x, m x = m0 x) ->
  (forall off v, In (off, v) cells -> forall x, write_to_mem m0 (den E (sv_alu ALU_ADD base (VL (wlit off)))) (store_bytes 8%uint63 (den E v)) x = m0 x) ->
  forall x, HalfFX.push_mem E m base cells x = m0 x.
Proof.
  induction cells as [|[off v] tl IH]; intros E m0 m base EQ G x; cbn [HalfFX.push_mem]; [apply EQ|].
  apply IH; [| intros off' v' Hin; apply G; right; exact Hin].
  intros y. rewrite (write_ext _ _ m0 _ EQ). apply G. left. reflexivity.
Qed.

Section Ghost.
Context {rc : runConstT}.

Lemma ghost_c8 : forall (m' : amem) A cs k (v : word),
  AS.rw_cells asegs m' A cs -> cell_at cs k = Some (C8 v) -> 0x62f000 <= A ->
  forall x, write_to_mem m' (Z_to_bv 64 (A + Z.of_nat k)) (store_bytes 8%uint63 v) x = m' x.
Proof.
  intros m' A cs k v RW CA LOW.
  pose proof (AS.rw_cells_read asegs m' A cs k (C8 v) RW CA) as OV. cbn [csize cbytes] in OV.
  pose proof (AS.rw_cells_bound asegs m' A cs RW) as [B0 B1].
  assert (KB : Z.of_nat k + 8 <= Z.of_nat (cells_size cs)).
  { clear -CA. revert k CA. induction cs as [|c cs IH]; intros k CA; cbn [cell_at] in CA; [discriminate|].
    destruct (Nat.eqb k 0) eqn:K0.
    - apply Nat.eqb_eq in K0. subst k. injection CA as ->. cbn [cells_size csize]. lia.
    - destruct (Nat.ltb k (csize c)) eqn:LT; [discriminate|]. apply Nat.ltb_ge in LT. specialize (IH _ CA). cbn [cells_size]. lia. }
  unfold AM.wa in OV.
  destruct (MemcpyFX.ov_read_bytes_inv asegs m' (A + Z.of_nat k) 8 (AM.le8 v) OV ltac:(lia) ltac:(unfold two64; lia)) as [_ RB].
  assert (SB : store_bytes 8%uint63 v = AM.le8 v) by (rewrite <- OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem.StepM.store_bytes_64; apply AS.store_bytes_8').
  rewrite SB. apply HalfFX.write_same; [lia| rewrite AM.length_le8; unfold two64; lia|].
  rewrite AM.length_le8. intros i Hi. change (Z.of_nat 8) with 8 in *.
  pose proof (RB i Hi) as RBi.
  destruct (nth_error (AM.le8 v) (Z.to_nat i)) as [b|] eqn:NB; [| exfalso; apply nth_error_None in NB; rewrite AM.length_le8 in NB; lia].
  apply raw_of_view; [lia| exact RBi].
Qed.
End Ghost.

Definition mixR (R R' : bvmap 5 word) : bvmap 5 word :=
  mkR (AP.getr R' 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R' 5) (AP.getr R' 6) (AP.getr R' 7) (AP.getr R 8)
      (AP.getr R 9) (AP.getr R' 10) (AP.getr R' 11) (AP.getr R' 12) (AP.getr R' 13) (AP.getr R' 14) (AP.getr R' 15) (AP.getr R' 16)
      (AP.getr R' 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
      (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R' 28) (AP.getr R' 29) (AP.getr R' 30) (AP.getr R' 31).

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

Lemma half_leaf_B1 : forall st E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (m' : amem) (R' : bvmap 5 word) (mo' : Model) (FRM : Z) (v10 base : sv) (cells : list (int * sv)) (st3 : sstate),
  st_ok asegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in
  ATOP + 4096 <= CtrPre.sp_lo E st -> CtrPre.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 -> 0 < FRM <= 4096 ->
  munch [(sp - FRM, sp)]%Z (ms_mem ms) m' -> wmono asegs (ms_mem ms) m' ->
  AM.mem_inv asegs (ms_mem ms) -> AM.mem_inv asegs m' -> stk asegs m' (CtrPre.sp_lo E st) sp ->
  let RA := mixR R R' in
  let Fv := CtrFree.cfvF RA in let Gv := fun (_ _ : Z) => Z_to_bv 8 0 in let E' := CtrFrame.E' E st Fv Gv in
  den E' v10 = AP.getr R' 10%bv ->
  OTHER mo mo' -> op_minv OPS mo' -> ACCT aw L RNG sta LBa mo' ->
  HalfC.push_cells asegs (setpc (setr (clobber st1) X10 v10) r) base cells = Some st3 ->
  (forall off v, In (off, v) cells -> forall x,
     write_to_mem m' (den E' (sv_alu ALU_ADD base (VL (wlit off)))) (store_bytes 8%uint63 (den E' v)) x = m' x) ->
  exists msB, st_ok asegs OPS E' st3 msB mo'
    /\ ms_regs msB = RA /\ ms_fregs msB = ms_fregs ms /\ ms_svc_pending msB = None /\ ms_resv msB = None /\ ms_fcsr msB = ms_fcsr ms
    /\ ms_rom msB = seg_rom asegs /\ ms_mem msB = m'
    /\ s_rf st3 = rf_set (s_rf (clobber st1)) X10 v10 /\ s_ff st3 = s_ff st /\ s_resv st3 = s_resv st /\ s_facts st3 = s_facts st
    /\ s_ops st3 = s_ops st /\ s_priv st3 = s_priv st /\ s_next st3 = s_next (clobber st1).
Proof.
  intros st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' FRM v10 base cells st3 HS CP FS CF AH R sp BOT LO SPT FRMok MU WM MI MI' STK' RA Fv Gv E' DV OTH HMI' ACP PUSH GHOST.
  pose proof atop_range as ATR.
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
  destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  assert (RVN : s_resv st = RNone) by (unfold call_pre in CP; destruct (s_resv st); try discriminate CP; reflexivity).

  assert (MU0 : munch [(sp - FRM, sp); (0, 0 + 0)]%Z (ms_mem ms) m').
  { intros x OUT. apply MU. cbn [outside] in OUT |- *. tauto. }
  pose proof (phaseA_ms AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                st E ms mo r hargs wnl st1 L RNG sta LBa aw m' RA mo' 0 0 FRM v10 (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT
                ltac:(lia) ltac:(left; lia) FRMok MU0 WM MI MI' STK'
                ltac:(intros rg Hrg; unfold CtrFrame.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                DV OTH HMI' ACP) as HSA.
  fold Fv Gv E' in HSA.
  assert (SH2 : setpc (setr (clobber st1) X10 v10) r
              = SS r (rf_set (s_rf (clobber st1)) X10 v10) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1))).
  { rewrite <- FF1, <- RV1, <- FS1, <- OP1, <- PV1, <- FF, <- RV, <- RG, <- FS0, <- OP, <- PV. destruct (clobber st1); reflexivity. }
  rewrite SH2 in PUSH.

  assert (PW0 : forall x, m' x = ms_mem (CtrFrame.ms' ms r RA (mjoinR 0 (0 + 0) (ms_mem ms) m')) x).
  { intros x. change (ms_mem (CtrFrame.ms' ms r RA (mjoinR 0 (0 + 0) (ms_mem ms) m')) x) with (mjoinR 0 (0 + 0) (ms_mem ms) m' x).
    unfold mjoinR, in_rng. replace ((0 <=? bv_unsigned x) && (bv_unsigned x <? 0 + 0))%bool with false; [reflexivity|].
    symmetry. apply andb_false_iff. right. apply Z.ltb_ge. pose proof (bv_unsigned_in_range _ x). lia. }
  pose proof (st_ok_mem_ext_g OPS E' _ _ mo' m' PW0 HSA) as HS1.

  destruct (HalfFX.push_cells_sound asegs OPS cells _ base st3 E' _ mo' HS1 RVN eq_refl PUSH) as (HS3 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  cbn [ms_mem ms_with_mem ms_upd] in HS3.
  assert (PW1 : forall x, m' x = HalfFX.push_mem E' m' base cells x).
  { intros x. symmetry. apply (push_mem_same cells E' m' m' base (fun _ => eq_refl) GHOST). }
  match type of HS3 with st_ok _ _ _ _ ?msx _ => pose proof (st_ok_mem_ext_g OPS E' st3 msx mo' m' PW1 HS3) as HS4 end.
  eexists. split; [exact HS4|].
  cbn [s_pc s_rf s_ff s_resv s_facts s_ops s_priv s_next] in F1, F2, F3, F5, F6, F7, F8.
  repeat split; try reflexivity; try assumption. rewrite F4. symmetry. exact RVN.
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

Import HalfC.TwinB HalfFX.TwinB MemOps.TwinB MemsetFX.TwinB MemcpyFX.TwinB RangePre.TwinB MemsetPost.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA HalfC.TwinB.HalfC.
Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AS := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step.

Lemma write_ext : forall bs (m1 m2 : amem) a, (forall x, m1 x = m2 x) -> forall x, write_to_mem m1 a bs x = write_to_mem m2 a bs x.
Proof.
  induction bs as [|b bs IH]; intros m1 m2 a H x; cbn [write_to_mem]; [apply H|].
  apply IH. intros y. destruct (bv_eqb y a); [reflexivity| apply H].
Qed.

Lemma push_mem_same : forall cells E (m0 m : amem) base, (forall x, m x = m0 x) ->
  (forall off v, In (off, v) cells -> forall x, write_to_mem m0 (den E (sv_alu ALU_ADD base (VL (wlit off)))) (store_bytes 8%uint63 (den E v)) x = m0 x) ->
  forall x, HalfFX.TwinB.HalfFX.push_mem E m base cells x = m0 x.
Proof.
  induction cells as [|[off v] tl IH]; intros E m0 m base EQ G x; cbn [HalfFX.TwinB.HalfFX.push_mem]; [apply EQ|].
  apply IH; [| intros off' v' Hin; apply G; right; exact Hin].
  intros y. rewrite (write_ext _ _ m0 _ EQ). apply G. left. reflexivity.
Qed.

Section Ghost.
Context {rc : runConstT}.

Lemma ghost_c8 : forall (m' : amem) A cs k (v : word),
  AS.rw_cells bsegs m' A cs -> cell_at cs k = Some (C8 v) -> 0x631000 <= A ->
  forall x, write_to_mem m' (Z_to_bv 64 (A + Z.of_nat k)) (store_bytes 8%uint63 v) x = m' x.
Proof.
  intros m' A cs k v RW CA LOW.
  pose proof (AS.rw_cells_read bsegs m' A cs k (C8 v) RW CA) as OV. cbn [csize cbytes] in OV.
  pose proof (AS.rw_cells_bound bsegs m' A cs RW) as [B0 B1].
  assert (KB : Z.of_nat k + 8 <= Z.of_nat (cells_size cs)).
  { clear -CA. revert k CA. induction cs as [|c cs IH]; intros k CA; cbn [cell_at] in CA; [discriminate|].
    destruct (Nat.eqb k 0) eqn:K0.
    - apply Nat.eqb_eq in K0. subst k. injection CA as ->. cbn [cells_size csize]. lia.
    - destruct (Nat.ltb k (csize c)) eqn:LT; [discriminate|]. apply Nat.ltb_ge in LT. specialize (IH _ CA). cbn [cells_size]. lia. }
  unfold AM.wa in OV.
  destruct (MemcpyFX.TwinB.MemcpyFX.ov_read_bytes_inv bsegs m' (A + Z.of_nat k) 8 (AM.le8 v) OV ltac:(lia) ltac:(unfold two64; lia)) as [_ RB].
  assert (SB : store_bytes 8%uint63 v = AM.le8 v) by (rewrite <- OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem.StepM.store_bytes_64; apply AS.store_bytes_8').
  rewrite SB. apply HalfFX.TwinB.HalfFX.write_same; [lia| rewrite AM.length_le8; unfold two64; lia|].
  rewrite AM.length_le8. intros i Hi. change (Z.of_nat 8) with 8 in *.
  pose proof (RB i Hi) as RBi.
  destruct (nth_error (AM.le8 v) (Z.to_nat i)) as [b|] eqn:NB; [| exfalso; apply nth_error_None in NB; rewrite AM.length_le8 in NB; lia].
  apply raw_of_view; [lia| exact RBi].
Qed.
End Ghost.

Definition mixR (R R' : bvmap 5 word) : bvmap 5 word :=
  mkR (AP.getr R' 1) (AP.getr R 2) (AP.getr R 3) (AP.getr R 4) (AP.getr R' 5) (AP.getr R' 6) (AP.getr R' 7) (AP.getr R 8)
      (AP.getr R 9) (AP.getr R' 10) (AP.getr R' 11) (AP.getr R' 12) (AP.getr R' 13) (AP.getr R' 14) (AP.getr R' 15) (AP.getr R' 16)
      (AP.getr R' 17) (AP.getr R 18) (AP.getr R 19) (AP.getr R 20) (AP.getr R 21) (AP.getr R 22) (AP.getr R 23) (AP.getr R 24)
      (AP.getr R 25) (AP.getr R 26) (AP.getr R 27) (AP.getr R' 28) (AP.getr R' 29) (AP.getr R' 30) (AP.getr R' 31).

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

Lemma half_leaf_B1 : forall st E ms mo r hargs wnl st1 (L : alayout) (RNG : footprint) (sta : astate) (LBa : list ablock) (aw : word)
    (m' : amem) (R' : bvmap 5 word) (mo' : Model) (FRM : Z) (v10 base : sv) (cells : list (int * sv)) (st3 : sstate),
  st_ok bsegs OPS E st ms mo -> call_pre st = Some r -> forget_stack_below_sp_g st = Some st1 ->
  CtrPre.TwinB.acallG AI ACCT UNIV Cw E st ms mo r hargs wnl L RNG sta LBa aw -> AHEAP AI L RNG sta LBa (ms_mem ms) ->
  let R := ms_regs ms in let sp := bv_unsigned (AP.getr R 2) in
  ATOP + 4096 <= CtrPre.TwinB.sp_lo E st -> CtrPre.TwinB.sp_lo E st <= sp - 4096 -> sp < 2 ^ 47 -> 0 < FRM <= 4096 ->
  munch [(sp - FRM, sp)]%Z (ms_mem ms) m' -> wmono bsegs (ms_mem ms) m' ->
  AM.mem_inv bsegs (ms_mem ms) -> AM.mem_inv bsegs m' -> stk bsegs m' (CtrPre.TwinB.sp_lo E st) sp ->
  let RA := mixR R R' in
  let Fv := CtrFree.TwinB.cfvF RA in let Gv := fun (_ _ : Z) => Z_to_bv 8 0 in let E' := CtrFrame.TwinB.E' E st Fv Gv in
  den E' v10 = AP.getr R' 10%bv ->
  OTHER mo mo' -> op_minv OPS mo' -> ACCT aw L RNG sta LBa mo' ->
  HalfC.TwinB.HalfC.push_cells bsegs (setpc (setr (clobber st1) X10 v10) r) base cells = Some st3 ->
  (forall off v, In (off, v) cells -> forall x,
     write_to_mem m' (den E' (sv_alu ALU_ADD base (VL (wlit off)))) (store_bytes 8%uint63 (den E' v)) x = m' x) ->
  exists msB, st_ok bsegs OPS E' st3 msB mo'
    /\ ms_regs msB = RA /\ ms_fregs msB = ms_fregs ms /\ ms_svc_pending msB = None /\ ms_resv msB = None /\ ms_fcsr msB = ms_fcsr ms
    /\ ms_rom msB = seg_rom bsegs /\ ms_mem msB = m'
    /\ s_rf st3 = rf_set (s_rf (clobber st1)) X10 v10 /\ s_ff st3 = s_ff st /\ s_resv st3 = s_resv st /\ s_facts st3 = s_facts st
    /\ s_ops st3 = s_ops st /\ s_priv st3 = s_priv st /\ s_next st3 = s_next (clobber st1).
Proof.
  intros st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' FRM v10 base cells st3 HS CP FS CF AH R sp BOT LO SPT FRMok MU WM MI MI' STK' RA Fv Gv E' DV OTH HMI' ACP PUSH GHOST.
  pose proof atop_range as ATR.
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
  destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  assert (RVN : s_resv st = RNone) by (unfold call_pre in CP; destruct (s_resv st); try discriminate CP; reflexivity).

  assert (MU0 : munch [(sp - FRM, sp); (0, 0 + 0)]%Z (ms_mem ms) m').
  { intros x OUT. apply MU. cbn [outside] in OUT |- *. tauto. }
  pose proof (phaseA_ms AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                st E ms mo r hargs wnl st1 L RNG sta LBa aw m' RA mo' 0 0 FRM v10 (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT
                ltac:(lia) ltac:(left; lia) FRMok MU0 WM MI MI' STK'
                ltac:(intros rg Hrg; unfold CtrFrame.TwinB.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                DV OTH HMI' ACP) as HSA.
  fold Fv Gv E' in HSA.
  assert (SH2 : setpc (setr (clobber st1) X10 v10) r
              = SS r (rf_set (s_rf (clobber st1)) X10 v10) (s_ff st) (s_resv st) (s_regs st1) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1))).
  { rewrite <- FF1, <- RV1, <- FS1, <- OP1, <- PV1, <- FF, <- RV, <- RG, <- FS0, <- OP, <- PV. destruct (clobber st1); reflexivity. }
  rewrite SH2 in PUSH.

  assert (PW0 : forall x, m' x = ms_mem (CtrFrame.TwinB.ms' ms r RA (mjoinR 0 (0 + 0) (ms_mem ms) m')) x).
  { intros x. change (ms_mem (CtrFrame.TwinB.ms' ms r RA (mjoinR 0 (0 + 0) (ms_mem ms) m')) x) with (mjoinR 0 (0 + 0) (ms_mem ms) m' x).
    unfold mjoinR, in_rng. replace ((0 <=? bv_unsigned x) && (bv_unsigned x <? 0 + 0))%bool with false; [reflexivity|].
    symmetry. apply andb_false_iff. right. apply Z.ltb_ge. pose proof (bv_unsigned_in_range _ x). lia. }
  pose proof (st_ok_mem_ext_g OPS E' _ _ mo' m' PW0 HSA) as HS1.

  destruct (HalfFX.TwinB.HalfFX.push_cells_sound bsegs OPS cells _ base st3 E' _ mo' HS1 RVN eq_refl PUSH) as (HS3 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
  cbn [ms_mem ms_with_mem ms_upd] in HS3.
  assert (PW1 : forall x, m' x = HalfFX.TwinB.HalfFX.push_mem E' m' base cells x).
  { intros x. symmetry. apply (push_mem_same cells E' m' m' base (fun _ => eq_refl) GHOST). }
  match type of HS3 with st_ok _ _ _ _ ?msx _ => pose proof (st_ok_mem_ext_g OPS E' st3 msx mo' m' PW1 HS3) as HS4 end.
  eexists. split; [exact HS4|].
  cbn [s_pc s_rf s_ff s_resv s_facts s_ops s_priv s_next] in F1, F2, F3, F5, F6, F7, F8.
  repeat split; try reflexivity; try assumption. rewrite F4. symmetry. exact RVN.
Qed.
End Leaf.
End TwinB.
