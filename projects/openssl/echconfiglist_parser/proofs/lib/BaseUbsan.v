(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (both binaries' theorems take the mmap-base, channel-reader and launch facts of Run.valid_input and Run.valid_entry; FZ_p, the plain binary's library, has type Ref.ECH_LibTop.fuzz_vc_type, and FZ_u, the ubsan binary's library, has type Ub.ECH_LibTop.fuzz_vc_type). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List ZArith Lia Bool.
Require OSSVerify.openssl.echconfiglist_parser.images.Plain.
Require OSSVerify.openssl.echconfiglist_parser.images.Ubsan.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import Scfg ShapeAlg ShapeEF Spec HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Cfg Require Import RomStable.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require RefTop.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require ECH_LibTop.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require UbTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.

Definition CFG : SpuriousCfg := Run.mkSpuriousCfg false true true true true true.

Section WithLib.
  (* [comment removed for export] *)
  Hypothesis FZ_p : OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref.ECH_LibTop.fuzz_vc_type.
  Hypothesis FZ_u : OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub.ECH_LibTop.fuzz_vc_type.

  (* [comment removed for export] *)
  Theorem ubsan_base_scfg :
    strong_universal_error_free_T_scfg CFG
      (mkImage OSSVerify.openssl.echconfiglist_parser.images.Plain.M.loaded_segments
               OSSVerify.openssl.echconfiglist_parser.images.Plain.M.init_pc
               OSSVerify.openssl.echconfiglist_parser.images.Plain.M.phdrs)
      (mkImage OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.loaded_segments
               OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.init_pc
               OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.phdrs).
  Proof.
    intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hens as [Hrsp [Hrbrk [Hrmb [Hrfit Hrlau]]]]. destruct Hent as [Hasp [Habrk [Hamb [Hafit Halau]]]].
    pose proof (valid_input_channel_reader _ Hvalid) as Hrd. pose proof (valid_input_launch _ Hvalid) as Hvl.
    destruct Hvalid as (Hargv & Henvp & Hfs & _).
    change CFG with (@the_scfg hunspell_scfg).
    apply (shape_strong_equiv_ef_scfg _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
    (* The run reads each binary against [run_segments ..] from the run's own start; each
       binary's theorem states its walk there, with the launch facts [Run.valid_input] and
       [Run.valid_entry] give. *)
    - exact (RefTop.ref_realizes_spec FZ_p rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs Hrmb Hrd Hvl Hrlau).
    - exact (OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub.UbTop.ub_realizes_spec FZ_u asp abrk amb arnd inp Hasp Habrk Hafit Hargv Henvp Hfs Hamb Hrd Hvl Halau).
  Qed.

  (* [comment removed for export] *)
  Theorem ubsan_base :
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
      CFG
      LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
      LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.Plain.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Plain.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Plain.M.phdrs)
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.loaded_segments OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.init_pc OSSVerify.openssl.echconfiglist_parser.images.Ubsan.M.phdrs).
  Proof.
    intros en_source en_target inp Hens Hent Hvalid _.
    unfold ShippedBudgets.lim_source, ShippedBudgets.lim_target.
    exact (ubsan_base_scfg en_source en_target inp Hens Hent Hvalid).
  Qed.
End WithLib.
