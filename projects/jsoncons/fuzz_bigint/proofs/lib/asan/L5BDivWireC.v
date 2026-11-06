(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA IcptIfaceAB0 LibIface
     AsanAcct L5Defs L5DefsAB0 L5CoreAB0 L5CoreSpecsAB0 L5DivLeafSpecsAB0 L5DivSpecsAB0 L5OpmodSpecsAB0 L5DivInnerSpecsAB0 L5UnwindSpecsAB0 XIcptAB0 XIcptAs0KitB0
     L5CoreSliceAB0 L5BOpdel L5BAssign L5BCopy L5BCopyAS L5BCopyS16 L5BCmpSpec L5BCmp L5BShl16 L5BMulM16 L5BNorm L5BOpModF
     L5BDivN L5BDivO1 L5BDivO2 L5BDivGNb L5BDivGO2d L5BDivGO1b L5BE2Top L5BE3Top L5BDivWire.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module L5ADWIREC.
Import L5A. Import L5CA. Import L5CSA.
Section SCFG_1.
Context {SCFG_P : ScfgP}.

Section WithIface.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (IL : icpt_layout) (HI : asan_iface).
Hypothesis LY : as0_layout L C.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis HIok : asan_iface_ok L ar C SCFG HI.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis HFILL : XIAS0.fill_spec.
Hypothesis HCOPY : XIAS0.copy_spec.
Hypothesis HTLS : XIAS0.tls_spec.
Hypothesis UNWL : L5USA.as0_unw_layout L.

(* [comment removed for export] *)
Lemma c_opnew : opnew_spec L ar HI. Proof. exact (L5SLICEA.opnew_ok L ar C HI LY HIok). Qed.
Lemma c_reserve : reserve_spec L ar HI. Proof. exact (L5SLICEA.reserve_ok L ar C HI LY HIok). Qed.
Lemma c_resize : resize_spec L ar HI. Proof. exact (L5SLICEA.resize_ok L ar C HI LY HIok). Qed.
Lemma c_opdel : opdel_sized_spec L ar HI. Proof. exact (L5ADEL.opdel_sized_ok L ar C HI LY HIok). Qed.
Lemma c_assign : assign_spec L ar HI. Proof. exact (L5AASG.assign_ok L ar C HI LY HIok c_resize). Qed.
Lemma c_copya : copya_spec L ar HI. Proof. exact (L5ACPY.copya_ok L ar C HI LY HIok c_opnew). Qed.
Lemma c_copya_stk : L5ACPAS.copya_stk_spec L ar HI. Proof. exact (L5ACPAS.copya_stk_ok L ar C HI LY HIok c_opnew). Qed.
Lemma c_copya_ssrc : L5ACPAS.copya_ssrc_spec L ar HI. Proof. exact (L5ACPAS.copya_ssrc_ok L ar C HI LY HIok). Qed.
Lemma c_resize0 : L5DLA.resize_spec_at 0 L ar HI. Proof. exact (L5DLA.resize_spec_at_0 L ar HI c_resize). Qed.
Lemma c_norm : L5DLA.norm_specA L ar HI.
Proof. exact (L5ANORM.norm_okA L ar C HI LY HIok (L5ASHL16.shl_ok_at L ar C HI LY HIok c_resize0) (L5AMULM16.mulm_ok_at L ar C HI LY HIok c_resize0)). Qed.

(* [comment removed for export] *)
Theorem gen_N_closed : L5ADVN.gen_N L ar HI.
Proof. exact (L5ADVGNB.gen_N_ok L ar C HI LY HIok c_opdel c_assign c_copya_stk c_norm c_resize). Qed.
Theorem unnorm_closed : L5DIA.unnorm_specA L ar HI.
Proof. exact (L5ADWIRE.unnorm_of_gen L ar C HI LY HIok c_copya L5ACMP.cmp_runA c_copya_ssrc c_opdel c_resize gen_N_closed). Qed.
Theorem gen_O1_closed : L5ADVO1.gen_O1 L ar HI.
Proof. exact (L5ADVGO1B.gen_O1_ok L ar C HI LY HIok c_copya_stk c_norm c_resize c_assign c_opdel unnorm_closed). Qed.
Theorem gen_O2_closed : L5ADVO2.gen_O2 L ar HI.
Proof. exact (L5ADVGO2D.gen_O2_ok L ar C HI LY HIok c_copya_stk c_norm c_resize c_assign c_opdel unnorm_closed). Qed.

(* [comment removed for export] *)
Theorem Hom1_closed :
  L5OMA.opmod1A_spec L ar HI L5USA.XS (L5USA.xs_pre ar) L5USA.xs_foot (L5USA.e2_landed L) (L5USA.e3_landed L) 73728 6 0 4 8 (fun c => 8 * c + 640).
Proof.
  exact (L5ADWIRE.Hom1_of_gen L ar C HI LY HIok c_copya L5ACMP.cmp_runA c_assign c_opdel c_resize gen_O1_closed
           (L5BE2Top.e2_chainA_ok L ar C IL HI LY ILY HIok ICok HFILL HCOPY HTLS UNWL)
           (L5BE3Top.e3_chainA_ok L ar C IL HI LY ILY HIok ICok HFILL HCOPY HTLS UNWL) UNWL).
Qed.
Theorem Hom2_closed : L5OMA.opmod2A_spec L ar HI 73728 6 0 4 8 (fun c => 24 * c + 640).
Proof. exact (L5ADWIRE.Hom2_of_gen L ar C HI LY HIok c_copya L5ACMP.cmp_runA c_assign c_opdel gen_O2_closed). Qed.

(* [comment removed for export] *)
Lemma c_copy_stk16 : L5BCPS16.copy_stk16_spec L ar HI. Proof. exact (L5BCPS16.copy_stk16_ok L ar C HI LY HIok c_opnew). Qed.
Theorem Homf1_closed :
  L5BOMF.opmodf1_spec L ar HI L5USA.XS (L5USA.xs_pre ar) L5USA.xs_foot (L5USA.e2_landed L) (L5USA.e3_landed L) 73728 (73728 + 4288) 6 0 4 8 (fun c => 8 * c + 640).
Proof.
  refine (L5BOMF.opmodf1_ok L ar C HI LY HIok L5USA.XS (L5USA.xs_pre ar) L5USA.xs_foot (L5USA.e2_landed L) (L5USA.e3_landed L) 73728 (73728 + 4288) 6 0 4 8 (fun c => 8 * c + 640) _ _ _ _ Hom1_closed c_copy_stk16).
  - split. Lia.lia. reflexivity.
  - change COPY_SCR with 4256. split; Lia.lia.
  - Lia.lia.
  - split. Lia.lia. intros c Hc. Lia.lia.
Qed.
Theorem Homf2_closed : L5BOMF.opmodf2_spec L ar HI 73728 (73728 + 4288) 6 0 4 8 (fun c => 24 * c + 640).
Proof.
  refine (L5BOMF.opmodf2_ok L ar C HI LY HIok 73728 (73728 + 4288) 6 0 4 8 (fun c => 24 * c + 640) _ _ _ _ Hom2_closed c_copy_stk16).
  - split. Lia.lia. reflexivity.
  - change COPY_SCR with 4256. split; Lia.lia.
  - Lia.lia.
  - split. Lia.lia. intros c Hc. Lia.lia.
Qed.

End WithIface.
End SCFG_1.
End L5ADWIREC.
