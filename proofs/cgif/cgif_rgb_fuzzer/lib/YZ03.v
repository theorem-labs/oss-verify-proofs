(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OssFuzzTheorems.cgif.cgif_rgb_fuzzer.images Require Import Plain.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK15 YN05 YN0b YN01 YH04.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP07 YP08.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YZ02.
Unset Lia Cache. Unset Nia Cache.
#[local] Existing Instance YK11.fx0.
Theorem halts_src2 :
halts_allowed_T_scfg may_fail_cfg AnyExit.codes
(mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs).
Proof.
intros [sp brk mb rnd] inp Hen Hinp.
pose proof (valid_input_va_size _ Hinp) as Hsv48.
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
unfold must_exit_in_scfg.
apply (halts_of_realizes src2segs byte_codes _ _ sp brk mb rnd source_alloc_limit inp (SPEC inp)).
- apply src2_realizes; try assumption. apply SRC_LIM_MIN_le_source.
- apply SPEC_tsafe.
Qed.
