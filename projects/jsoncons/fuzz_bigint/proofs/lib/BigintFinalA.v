(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the input facts are read by shape, not by position, and the two sides take the launch facts (valid_launch and the entry's launch conjunct) and the channel reader. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import HeapInst0 HeapInst1 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Src0DrvLibL Ub0DrvLibL Src0DrvG Ub0DrvG Src0DrvMain Ub0DrvMain
  Src0HeapBridge Ub0HeapBridge BigintTop2 L5Top L5TopU BigintFinal KillFree.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

Theorem fuzz_bigint_ubsan_final_abort :
  (forall sp, valid_sp sp ->
     lib_iface_ok (L5Top.L5TOP.TopLay (HeapInst0.L0 (bv_unsigned sp))) cfg0 (HeapInst0.HI0 (bv_unsigned sp))
                  (L5Top.L5TOP.TopLS (HeapInst0.L0 (bv_unsigned sp)))) ->
  (forall sp, valid_sp sp ->
     lib_iface_ok (L5TopU.L5TOPU.TopLay (HeapInst1.L1 (bv_unsigned sp))) cfg0 (HeapInst1.HI1 (bv_unsigned sp))
                  (L5TopU.L5TOPU.TopLS (HeapInst1.L1 (bv_unsigned sp)))) ->
  strong_universal_error_free_T_scfg_budgets_abort cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  intros LIB0 LIB1.
  pose proof (src0_realizes_spec_heap cfg0 eq_refl eq_refl
                (fun sp => L5Top.L5TOP.TopLay (HeapInst0.L0 (bv_unsigned sp)))
                (fun sp => L5Top.L5TOP.TopLS (HeapInst0.L0 (bv_unsigned sp)))
                drv_lib_layout_top0 LIB0 budget0) as SRC.
  pose proof (ub0_realizes_spec_heap cfg0 eq_refl eq_refl
                (fun sp => L5TopU.L5TOPU.TopLay (HeapInst1.L1 (bv_unsigned sp)))
                (fun sp => L5TopU.L5TOPU.TopLS (HeapInst1.L1 (bv_unsigned sp)))
                drv_lib_layout_top1 LIB1 budget1) as TGT.
  intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid _.
  pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as [Hrsp [Hrbrk [Hrmb [_ Hrlau]]]]. destruct Hent as [Hasp [Habrk [Hamb [_ Halau]]]].
  (* LPS 727298f3: the specs read the launch and the reader; [valid_input_abort]'s clauses are
     read by shape, not by position (the via_* lemmas, lines 52-67 of projects/jsoncons/fuzz_json_cursor/proofs/lib/PmFinalSan.v as in the LPS 727298f3 update, do the same). *)
  assert (Hvl : valid_launch inp) by (red in Hvalid; tauto).
  assert (Hrd : in_channel_reader inp = true) by (red in Hvalid; tauto).
  assert (Hargv : valid_argv (in_argv inp)) by (red in Hvalid; tauto).
  assert (Henvp : valid_envp (in_envp inp)) by (red in Hvalid; tauto).
  assert (Hfs : valid_fs (in_fs inp)) by (red in Hvalid; tauto).
  assert (Hcreds : valid_creds inp) by (red in Hvalid; tauto).
  specialize (SRC rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hvl Hrlau Hargv Henvp Hfs Hcreds Hrd).
  specialize (TGT asp abrk amb arnd inp Hasp Habrk Hamb Hvl Halau Hargv Henvp Hfs Hcreds Hrd).
  unfold ShippedBudgets.lim_source, ShippedBudgets.lim_target.
  split; [| split].
  - eapply srealizes_error_free_unkilled; [exact SRC | apply kill_free_spec].
  - eapply srealizes_error_free_unkilled; [exact TGT | apply kill_free_spec].
  - intro tr.
    rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr SRC).
    rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr TGT).
    reflexivity.
Qed.

End FPX_1.
