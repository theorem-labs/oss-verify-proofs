(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (valid_entry's new fifth conjunct, the launch check, is destructed, and halts_src2 is proved over the run's segment list, run_segments, with the vDSO pair, through RomStable.run_init). *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 YN05 YN0b YN01 YH04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07 YP08.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YZ02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import RomStable.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Theorem halts_src2 :
halts_allowed_T_scfg may_fail_cfg AnyExit.codes
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Proof.
intros [sp brk mb rnd] inp Hen Hinp.
pose proof (valid_input_va_size _ Hinp) as Hsv48.
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
destruct Hen as [Hsp [Hbrk [Hmb [Hfit Hlau]]]].
unfold must_exit_in_scfg. cbv zeta.
(* the run reads the binary against its own segments and the vDSO pair ([RomStable.run_init]) *)
apply (halts_of_realizes (run_segments src2segs inp sp mb) byte_codes _ _ sp brk mb rnd source_alloc_limit inp (SPEC inp)).
- apply run_init; [first [reflexivity | unfold vdso_image, vdso_text_seg; vm_compute; reflexivity] |].
  apply src2_realizes; try assumption. apply SRC_LIM_MIN_le_source.
- apply SPEC_tsafe.
Qed.
