(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
Set Warnings "-require-in-module".
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel. From Stdlib Require ZArith NArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run. From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC. From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.musl.Mh_0067. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0079. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.
Module Ns0Sums.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.MemsetLib.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.musl.Mh_0067. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0079. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.musl.Mh_0067 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0079.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSound. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AsanPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSound.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.AsanPlanSoundSums OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SumsSpecLib.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma src0_copy_spec_memcpy : forall fx : PropExec.FPState, @APSX.copy_spec fx RSEGS 0xb9978.
Proof.
  intros fx mem0 dst src n bs regs ret Hn Hlen Hrd Hst Hdisj Hnws Hnwd Hret R1 R10 R11 R12.
  pose proof (u64_range dst) as Hdr.
  assert (HOK : Ns0MemcpyBase.mcH mem0 dst src n bs) by (constructor; try assumption; lia).
  destruct (Ns0Memcpy.ref_memcpy mem0 dst src n bs (seg_rom RSEGS) HOK regs ret Hret R1 R10 R11 R12) as (regs' & Hms & Hk).
  exists regs'. split; [replace (Z_to_bv 64 0xb9978) with (0xb9978%bv : word) by (apply bv_eq; reflexivity); exact Hms|].
  split; [apply kept_ok_of_keeps; exact Hk|].
  rewrite <- R10. apply Hk. unfold callee_kept. in_list.
Qed.

Lemma src0_fill_spec_memset : forall fx : PropExec.FPState, @APSX.fill_spec fx RSEGS 0xb9ef8 AX2.two64.
Proof.
  intros fx. apply fill_spec_of_memset. intros mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1.
  exact (Ns0SumsMemset.memset_summary mem0 d cv ret n rom Hn Hnw Hst Hret regs R10 R11 R12 R1).
Qed.

End Ns0Sums.
From Stdlib Require ZArith List Lia Bool. From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
Module Ns0SumsStrlen.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.SeqExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.Hoare OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0056.RefMemcpyLib.
Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.musl.Mh_0067. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0079. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.musl.Mh_0067.Ns0Memchr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0079.SegStrlen OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun.
Import ListNotations. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma src0_strlen_spec : SR.strlen_spec Plain.M.loaded_segments 0x13880 0x13898 0xba3dc.
Proof.
  intros fx mem s buf K rom regs ret Hbuf Hwin Hnw HK0 Hz Hnz Hro Hret H1 H10.
  assert (HOK : slenH mem s buf K) by (constructor; assumption).
  destruct (ref_strlen mem s buf K rom regs ret HOK Hret H1 H10) as (regs' & Hms & Hag & Ha0).
  exists regs'. split; [|split; [|exact Ha0]].
  - replace (Z_to_bv 64 0xba3dc) with (0xba3dc%bv : word) by (apply bv_eq; reflexivity). exact Hms.
  - intros r N10 N11 N12 N13 N14 N15 N16. apply (sl_agree_getr _ _ r Hag).
    unfold sl_clob. cbn [In]. intros [H|[H|[H|[H|[H|[H|[H|[]]]]]]]]; subst r; contradiction.
Qed.

End Ns0SumsStrlen.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan.
Module Ns0PlanKit.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AsanPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.AsanPlanSoundSums OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegRunStrlen OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0Sums OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0SumsStrlen OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.

Definition X_CPY : Z := 0xb9978.  Definition X_SET : Z := 0xb9ef8.  Definition X_LEN : Z := 0xba3dc.
Definition RO_LO : Z := 0x13880.  Definition RO_HI : Z := 0x13898.
(* [comment removed for export] *)
Definition A0 : APC.atable := APC.AT 0x10000 0xfa000 0%nat 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 [].

Lemma src0_in_hull : forall a : word, APS.in_hull A0 (bv_unsigned a) = false -> find_segment RSEGS (bv_unsigned a) 1 = None.
Proof. apply SGP.in_hull_of_b. vm_compute. reflexivity. Qed.
Lemma src0_hull_ok : APS.hull_ok A0.
Proof. unfold APS.hull_ok. cbn [APC.img_lo APC.img_hi A0]. unfold APC.KHI. repeat split; reflexivity || lia. Qed.

Theorem src0_plan_sound2 :
  forall (itr : list (Z * nat)) (BFUEL : nat) (nx0 : nat) (BR : list SGP.bfact)
         (XSTEP : list SGP.region -> nat -> sym_state -> option sym_state)
         (XSTEP2 : list SGP.region -> nat -> sym_state -> option (sym_state * sym_state)) (F : list SGP.region) PSS p pc0 sr0 kn0,
  SGP.cert_ok RSEGS (itab_of RSEGS itr) X_CPY X_SET X_LEN RO_LO RO_HI BFUEL A0 nx0 BR XSTEP XSTEP2 F PSS p pc0 sr0 kn0 = true ->
  (forall M0, SGP.XSTEP_ok RSEGS nx0 BR XSTEP F M0) ->
  (forall M0, SGP.XSTEP2_ok RSEGS nx0 BR XSTEP2 F M0) ->
  forall (fx : FPState) E R M,
  regs_ok E sr0 R -> know_ok RSEGS E M kn0 -> SGP.bfacts_ok BR E ->
  exists (fx' : FPState) E' R' M' i ps,
       nth_error PSS i = Some ps
    /\ env_agree nx0 E E'
    /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom RSEGS))
    /\ (forall i e, In (i, e) (SR.ps_regs ps) -> (0 < i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e)
    /\ getr R' (Z_to_bv 5 0) = Z_to_bv 64 0
    /\ SGP.regions_ok E' F
    /\ (forall a : word, SGP.outside E' F a -> M' a = M a)
    /\ (forall K, In K (SR.ps_cells ps) -> kentry_ok RSEGS E' M' K)
    /\ mem_grows M M'.
Proof.
  intros itr BFUEL nx0 BR XSTEP XSTEP2 F PSS p pc0 sr0 kn0 Hc HXS HXS2 fx E R M HR HK HBF.
  exact (SGP.plan_entry_sound RSEGS (itab_of RSEGS itr) X_CPY X_SET X_LEN RO_LO RO_HI BFUEL A0 nx0 BR XSTEP XSTEP2
           (itab_of_sound _ _) src0_copy_spec_memcpy src0_fill_spec_memset
           (SRS.strlen_step_sound _ _ _ _ src0_strlen_spec) src0_in_hull src0_hull_ok
           F PSS p pc0 sr0 kn0 fx E R M Hc HXS HXS2 HR HK HBF).
Qed.

(* [comment removed for export] *)
Theorem src0_plan_sound :
  forall (itr : list (Z * nat)) (BFUEL : nat) (nx0 : nat) (BR : list SGP.bfact)
         (XSTEP : list SGP.region -> nat -> sym_state -> option sym_state) (F : list SGP.region) PSS p pc0 sr0 kn0,
  SGP.cert_ok RSEGS (itab_of RSEGS itr) X_CPY X_SET X_LEN RO_LO RO_HI BFUEL A0 nx0 BR XSTEP SGP.xstep2_none F PSS p pc0 sr0 kn0 = true ->
  (forall M0, SGP.XSTEP_ok RSEGS nx0 BR XSTEP F M0) ->
  forall (fx : FPState) E R M,
  regs_ok E sr0 R -> know_ok RSEGS E M kn0 -> SGP.bfacts_ok BR E ->
  exists (fx' : FPState) E' R' M' i ps,
       nth_error PSS i = Some ps
    /\ env_agree nx0 E E'
    /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom RSEGS))
    /\ (forall i e, In (i, e) (SR.ps_regs ps) -> (0 < i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e)
    /\ getr R' (Z_to_bv 5 0) = Z_to_bv 64 0
    /\ SGP.regions_ok E' F
    /\ (forall a : word, SGP.outside E' F a -> M' a = M a)
    /\ (forall K, In K (SR.ps_cells ps) -> kentry_ok RSEGS E' M' K)
    /\ mem_grows M M'.
Proof.
  intros itr BFUEL nx0 BR XSTEP F PSS p pc0 sr0 kn0 Hc HXS.
  exact (src0_plan_sound2 itr BFUEL nx0 BR XSTEP SGP.xstep2_none F PSS p pc0 sr0 kn0 Hc HXS (fun M0 => SGP.xstep2_none_ok RSEGS nx0 BR F M0)).
Qed.

End Ns0PlanKit.
Module Ns0PlanKitIt.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AxSymExec3Sound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require AsanPlanSound. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require SegPlan. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.CatExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0030.CatSim OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AxSymExec3B OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AxSymExec3Sound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AxSymRun3 OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0075.AsanPlanCore OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.AsanPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.AsanPlanSound OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.AsanPlanSoundSums OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0112.LibSym OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0130.SegRun OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0137.SegRunStrlen OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0Sums OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0SumsStrlen OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.SegPlan OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0140.Ns0PlanKit.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Abbreviation RSEGS := Plain.M.loaded_segments.

Theorem src0_plan_sound_it :
  forall (IT : itab), itab_sound RSEGS IT ->
  forall (BFUEL : nat) (nx0 : nat) (BR : list SGP.bfact)
         (XSTEP : list SGP.region -> nat -> sym_state -> option sym_state) (F : list SGP.region) PSS p pc0 sr0 kn0,
  SGP.cert_ok RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BFUEL A0 nx0 BR XSTEP SGP.xstep2_none F PSS p pc0 sr0 kn0 = true ->
  (forall M0, SGP.XSTEP_ok RSEGS nx0 BR XSTEP F M0) ->
  forall (fx : FPState) E R M,
  regs_ok E sr0 R -> know_ok RSEGS E M kn0 -> SGP.bfacts_ok BR E ->
  exists (fx' : FPState) E' R' M' i ps,
       nth_error PSS i = Some ps
    /\ env_agree nx0 E E'
    /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom RSEGS))
    /\ (forall i e, In (i, e) (SR.ps_regs ps) -> (0 < i < 32)%nat /\ getr R' (Z_to_bv 5 (Z.of_nat i)) = edenot E' e)
    /\ getr R' (Z_to_bv 5 0) = Z_to_bv 64 0
    /\ SGP.regions_ok E' F
    /\ (forall a : word, SGP.outside E' F a -> M' a = M a)
    /\ (forall K, In K (SR.ps_cells ps) -> kentry_ok RSEGS E' M' K)
    /\ mem_grows M M'.
Proof.
  intros IT HIT BFUEL nx0 BR XSTEP F PSS p pc0 sr0 kn0 Hc HXS fx E R M HR HK HBF.
  exact (SGP.plan_entry_sound RSEGS IT X_CPY X_SET X_LEN RO_LO RO_HI BFUEL A0 nx0 BR XSTEP SGP.xstep2_none
           HIT src0_copy_spec_memcpy src0_fill_spec_memset
           (SRS.strlen_step_sound _ _ _ _ src0_strlen_spec) src0_in_hull src0_hull_ok
           F PSS p pc0 sr0 kn0 fx E R M Hc HXS (fun M0 => SGP.xstep2_none_ok RSEGS nx0 BR F M0) HR HK HBF).
Qed.

End Ns0PlanKitIt.
