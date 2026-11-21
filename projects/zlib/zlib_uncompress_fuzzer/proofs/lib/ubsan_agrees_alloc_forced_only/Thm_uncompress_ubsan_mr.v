(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_zlib_uncompress_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import ShapeAlg ShapeEF Spec S9LibStmt U9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.FO Require Import FOCore.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.

From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP9 Require S9MainHs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.MrP9 Require U9MainHs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ZC.
Variable CS : forall RCx : RunCtx, @zlib_u2_contract_S9 RCx.  (* the library contract for every run *)
Variable CU : forall RCx : RunCtx, @zlib_u2_contract_U9 RCx.  (* the library contract for every run *)

Theorem thm_of_lib :
  strong_universal_error_free_T_scfg alloc_forced_cfg
    (mkImage Src_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments Src_zlib_zlib_uncompress_fuzzer_repro.M.init_pc Src_zlib_zlib_uncompress_fuzzer_repro.M.phdrs)
    (mkImage Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments Tgt_zlib_uncompress_fuzzer_ubsan.M.init_pc
             Tgt_zlib_uncompress_fuzzer_ubsan.M.phdrs).
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
    exact (S9MainHs.s9_realizes_spec_hs CS
             rsp rbrk rmb rdraw inp Hrsp Hrbrk Hargv Henvp Hfs Hvl (proj2 Hrfits) Hcr).
  - assert (Hvl : valid_launch inp) by (decompose [and] Hrest; assumption).
    assert (Hcr : in_channel_reader inp = true) by (decompose [and] Hrest; assumption).
    exact (U9MainHs.u9_realizes_spec_hs CU
             asp abrk amb adraw inp Hasp Habrk Hargv Henvp Hfs Hvl (proj2 Hafits) Hcr).
Qed.

End ZC.
