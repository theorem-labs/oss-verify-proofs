(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the input facts are read from valid_input_either by type (vie_parts) in place of a positional destruct, and the two sides take the launch facts and the channel reader. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec HeapIface LibIface.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import HeapInst0 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Src0DrvLibL Src0DrvG Src0DrvMain Src0HeapBridge BigintTop2 L5Top BigintFinal KillFree BigintBaseH BigintBaseS0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import AsanAcct HeapIfaceA IcptIfaceAB0 LibIfaceA AsanInitK Bo0DefsK Bo0MainPhaseA BigintTopAB0.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FPX_1.
#[local] Existing Instance PropExec.fx0.

Theorem fuzz_bigint_both_final_scfg :
  as0_tgt_stmt cfg0 ->
  strong_universal_error_free_T_scfg cfg0
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  intros TGT.
  pose proof (src0_realizes_spec_heap cfg0 eq_refl eq_refl
                (fun sp => L5Top.L5TOP.TopLay (HeapInst0.L0 (bv_unsigned sp)))
                (fun sp => L5Top.L5TOP.TopLS (HeapInst0.L0 (bv_unsigned sp)))
                drv_lib_layout_top0 (LIB0_of_divide OPMOD1_src0_ok OPMOD2_src0_ok) budget0) as SRC.
  intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as [Hrsp [Hrbrk [Hrmb [_ Hrlau]]]]. destruct Hent as [Hasp [Habrk [Hamb [Hafit Halau]]]].
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  (* [valid_input] is the published statement's own binder, so the
     [valid_input_either] premise is discharged from it and not invented. *)
  pose proof (valid_input_either_of_valid_input inp Hvalid) as Hvi.
  destruct (vie_parts inp Hvi) as (Hargv & Henvp & Hfs & Hcreds & _ & _ & Hrd & _).
  specialize (SRC rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hvl Hrlau Hargv Henvp Hfs Hcreds Hrd).
  specialize (TGT asp abrk amb arnd inp Hasp Habrk Hamb Hafit Halau Hvl Hvi).
  split; [| split].
  - eapply srealizes_error_free; exact SRC.
  - eapply srealizes_error_free; exact TGT.
  - intro tr.
    rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr SRC).
    rewrite (srealizes_traces_iff cfg0 _ _ _ _ _ _ _ _ _ _ tr TGT).
    reflexivity.
Qed.

(* [comment removed for export] *)
Theorem fuzz_bigint_both_base_scfg_modulo :
  forall (L : asan_layout) (C : asan_statics_cells) (IL : icpt_layout) (Lay : lib_layoutA) (LSt : asan_run -> LibIface.lib_statics) (BUDGET : Z),
    2 ^ 34 <= BUDGET -> BUDGET <= 2 ^ 39 - 2 ^ 35 ->
    inst_ok_stmt cfg0 L C BUDGET -> free_null_stmt cfg0 L BUDGET -> h4e_stmt BUDGET -> icpt_ok_stmt cfg0 L IL BUDGET -> lib_ok_stmt cfg0 L C IL Lay LSt -> dla_ok_stmt cfg0 L C IL -> drv_consts_stmt L C IL ->
    drv_main_stmt cfg0 L C IL Lay LSt -> usage_stmt cfg0 ->
    strong_universal_error_free_T_scfg cfg0
      (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
      (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof.
  intros L C IL Lay LSt BUDGET B1 B2 H1 H1n H2 H3 H4 H5 H6 H7 H8.
  apply fuzz_bigint_both_final_scfg. apply as0_tgt_of_run.
  intros sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt sdf ur kb execfn Hsp Hbrk Hmb Hva Hve Hfit Hlau Hvl Huid Hhw Hvfs.
  eapply (as0_realizes_spec_run cfg0 eq_refl eq_refl L C IL Lay LSt BUDGET B1 B2 H1 H1n H2 H3 H4 H5 H6 H7 H8);
    first [eassumption | reflexivity].
Qed.

End FPX_1.
