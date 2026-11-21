(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import ShapeAlg ShapeEF Spec S0FuzzStmt U0FuzzStmt.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.FO Require Import FOCore.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound Require Import RunCtx.

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.MrP0 Require S0MainHs.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.MrP0 Require U0MainHs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section FZ.
(* the library statements for every run *)
Hypothesis HS : forall RCx : RunCtx, @s0_fuzz_stmt RCx.
Hypothesis HU : forall RCx : RunCtx, @u0_fuzz_stmt RCx.

Theorem thm_of_fuzz :
  strong_universal_error_free_T_scfg alloc_forced_cfg
    (mkImage Src_zlib_checksum_fuzzer_repro.M.loaded_segments Src_zlib_checksum_fuzzer_repro.M.init_pc Src_zlib_checksum_fuzzer_repro.M.phdrs)
    (mkImage Tgt_checksum_fuzzer_ubsan.M.loaded_segments Tgt_checksum_fuzzer_ubsan.M.init_pc
             Tgt_checksum_fuzzer_ubsan.M.phdrs).
Proof.
  intros [rsp rbrk rmb rdraw] [asp abrk amb adraw] inp Hens Hent Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as [Hrsp [Hrbrk [Hrmb Hrfits]]]. destruct Hent as [Hasp [Habrk [Hamb Hafits]]].
  destruct Hvalid as [Hargv [Henvp [Hfs Hrest]]].
  apply (shape_strong_equiv_ef _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (spec (in_argv inp) (in_fs inp))).
  - (* the 727 launch premises *)
    assert (Hvl : valid_launch inp) by (decompose [and] Hrest; assumption).
    assert (Hcr : in_channel_reader inp = true) by (decompose [and] Hrest; assumption).
    exact (S0MainHs.s0_realizes_spec_hs HS
             rsp rbrk rmb rdraw inp Hrsp Hrbrk Hargv Henvp Hfs Hvl (proj2 Hrfits) Hcr).
  - assert (Hvl : valid_launch inp) by (decompose [and] Hrest; assumption).
    assert (Hcr : in_channel_reader inp = true) by (decompose [and] Hrest; assumption).
    exact (U0MainHs.u0_realizes_spec_hs HU
             asp abrk amb adraw inp Hasp Habrk Hargv Henvp Hfs Hvl (proj2 Hafits) Hcr).
Qed.

End FZ.
