(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import HeapIface LibIface L5Defs
     L5DivSpecs L5DivSpecsU L5DivSpecsO L5OpMod2SpecU L5UnwindSpecs L5UnwindSpecsU L5Top L5TopU L5TopBind L5TopBindU BigintFinal.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import HeapInst0 HeapInst1.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
#[export] Instance ScfgP_cfg0 : ScfgP := {| SCFG := cfg0 |}.

Lemma sc_alloc_cfg0 : sc_alloc (@SCFG ScfgP_cfg0) = false.
Proof. reflexivity. Qed.

Definition sptop_window (sptop : Z) : Prop := 0x7fff80000000 <= sptop <= 2 ^ 47.

(* [comment removed for export] *)
Definition OPMOD1_src0 : Prop := forall sptop, sptop_window sptop -> L5TOPB.OPMOD1_TAIL (L0 sptop) (HI0 sptop).
Definition OPMOD2_src0 : Prop := forall sptop, sptop_window sptop -> L5DS.opmod2_spec (L0 sptop) (HI0 sptop).
Definition OPMOD1_ub0 : Prop := forall sptop, sptop_window sptop -> L5TOPBU.OPMOD1_TAIL (L1 sptop) (HI1 sptop).
Definition OPMOD2_ub0 : Prop := forall sptop, sptop_window sptop -> L5OM2SU.opmodf2_spec (L1 sptop) (HI1 sptop).   (* [comment removed for export] *)

Lemma valid_sp_window : forall sp, valid_sp sp -> sptop_window (bv_unsigned sp).
Proof.
  intros sp (Hlo & Hhi & _). unfold sptop_window. unfold sp_window_lo in Hlo. unfold sp_window_hi in Hhi.
  split; [exact Hlo | exact Hhi].
Qed.

(* [comment removed for export] *)
Lemma LIB0_of_divide : OPMOD1_src0 -> OPMOD2_src0 ->
  forall sp, valid_sp sp ->
    lib_iface_ok (L5TOP.TopLay (L0 (bv_unsigned sp))) cfg0 (HI0 (bv_unsigned sp)) (L5TOP.TopLS (L0 (bv_unsigned sp))).
Proof.
  intros O1 O2 sp V. pose proof (valid_sp_window sp V) as W.
  exact (@L5TOPB.top_iface_L0 ScfgP_cfg0 (bv_unsigned sp) W sc_alloc_cfg0 (O1 _ W) (O2 _ W)).
Qed.

Lemma LIB1_of_divide : OPMOD1_ub0 -> OPMOD2_ub0 ->
  forall sp, valid_sp sp ->
    lib_iface_ok (L5TOPU.TopLay (L1 (bv_unsigned sp))) cfg0 (HI1 (bv_unsigned sp)) (L5TOPU.TopLS (L1 (bv_unsigned sp))).
Proof.
  intros O1 O2 sp V. pose proof (valid_sp_window sp V) as W.
  exact (@L5TOPBU.top_iface_L1 ScfgP_cfg0 (bv_unsigned sp) W sc_alloc_cfg0 (O1 _ W) (O2 _ W)).
Qed.

(* [comment removed for export] *)
Theorem fuzz_bigint_ubsan_modulo_divide :
  OPMOD1_src0 -> OPMOD2_src0 -> OPMOD1_ub0 -> OPMOD2_ub0 ->
  strong_universal_error_free_T_scfg cfg0
    (mkImage Plain.M.loaded_segments Plain.M.init_pc
             Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  intros O1 O2 O1U O2U.
  exact (fuzz_bigint_ubsan_final (LIB0_of_divide O1 O2) (LIB1_of_divide O1U O2U)).
Qed.
