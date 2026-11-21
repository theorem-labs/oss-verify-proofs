(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the entry's fifth conjunct (the launch) and the input facts are read through the model's accessors, never by position, and the two sides take the launch facts and the channel reader. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ShapeAlg DivergeSim SpinAlg SpinAlgX ShapeEF Spec BigintSpec Src0DrvMain Ub0DrvMain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Variable scfg : SpuriousCfg.

Theorem fuzz_bigint_ubsan_ok2 :
  src_realizes_stmt2 scfg -> tgt_realizes_stmt2 scfg ->
  strong_universal_error_free_T_scfg scfg
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  intros SRC TGT.
  intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
  (* LPS 727298f3: [valid_entry]'s fifth conjunct is the launch ([Run.valid_entry_sv48]); the
     input facts are read through the model's accessors, never by position. *)
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as [Hrsp [Hrbrk [Hrmb [_ Hrlau]]]]. destruct Hent as [Hasp [Habrk [Hamb [_ Halau]]]].
  pose proof (valid_input_launch _ Hvalid) as Hvl.
  pose proof (valid_input_channel_reader _ Hvalid) as Hrd.
  pose proof (valid_input_argv _ Hvalid) as Hargv. pose proof (valid_input_envp _ Hvalid) as Henvp.
  pose proof (valid_input_fs _ Hvalid) as Hfs. pose proof (valid_input_creds _ Hvalid) as Hcreds.
  apply (shape_strong_equiv_efs scfg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
  - exact (SRC rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hvl Hrlau Hargv Henvp Hfs Hcreds Hrd).
  - exact (TGT asp abrk amb arnd inp Hasp Habrk Hamb Hvl Halau Hargv Henvp Hfs Hcreds Hrd).
Qed.

End FPX_1.
