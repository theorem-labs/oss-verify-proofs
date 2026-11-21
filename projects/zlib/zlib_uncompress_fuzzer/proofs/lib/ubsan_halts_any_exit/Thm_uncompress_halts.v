(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to the model, comments removed. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_zlib_uncompress_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_zlib_uncompress_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import ShapeAlg Spec ShapeHalts SpecHalts S9LibStmt U9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.MrP9 Require S9MainHs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.MrP9 Require U9LMainHs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section ZC.
Variable CS : forall RCx : RunCtx, @zlib_u2_contract_S9 RCx.  (* the library contract for every run *)
Variable CU : forall RCx : RunCtx, @zlib_u2_contract_U9 RCx.  (* the library contract for every run *)

Theorem halts_plain :
  halts_allowed_T_scfg may_fail_cfg AnyExit.codes
    (mkImage Src_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments Src_zlib_zlib_uncompress_fuzzer_repro.M.init_pc Src_zlib_zlib_uncompress_fuzzer_repro.M.phdrs).
Proof.
  intros [sp brk mb draw] inp Hen Hvalid.
  apply (proj2 (must_exit_in_scfg_may_fail _ _ _ _ _)). cbn [must_exit_in].
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as [Hsp [Hbrk [Hmb Hfits]]]. destruct Hvalid as [Hargv [Henvp [Hfs Hrest]]].
  apply (realizes_must_exit_init _ AnyExit.codes _ (spec (in_argv inp) (in_fs inp))).
  - assert (Hvl : valid_launch inp) by (decompose [and] Hrest; assumption).
    assert (Hcr : in_channel_reader inp = true) by (decompose [and] Hrest; assumption).
    exact (S9MainHs.s9_realizes_spec_hs CS sp brk mb draw inp Hsp Hbrk Hargv Henvp Hfs Hvl (proj2 Hfits) Hcr).
  - apply spec_ends_in.
  - reflexivity.
Qed.

Theorem halts_ubsan :
  halts_allowed_T_scfg may_fail_cfg AnyExit.codes
    (mkImage Tgt_zlib_uncompress_fuzzer_ubsan.M.loaded_segments Tgt_zlib_uncompress_fuzzer_ubsan.M.init_pc Tgt_zlib_uncompress_fuzzer_ubsan.M.phdrs).
Proof.
  intros [sp brk mb draw] inp Hen Hvalid.
  apply (proj2 (must_exit_in_scfg_may_fail _ _ _ _ _)). cbn [must_exit_in].
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as [Hsp [Hbrk [Hmb Hfits]]]. destruct Hvalid as [Hargv [Henvp [Hfs Hrest]]].
  apply (realizes_must_exit_init _ AnyExit.codes _ (spec (in_argv inp) (in_fs inp))).
  - assert (Hvl : valid_launch inp) by (decompose [and] Hrest; assumption).
    assert (Hcr : in_channel_reader inp = true) by (decompose [and] Hrest; assumption).
    exact (U9LMainHs.u9_realizes_spec_hs CU sp brk mb draw inp Hsp Hbrk Hargv Henvp Hfs Hvl (proj2 Hfits) Hcr).
  - apply spec_ends_in.
  - reflexivity.
Qed.

End ZC.
