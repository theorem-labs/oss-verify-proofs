(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD2m.v, with its module paths changed; AB1v's tfibsegs is A/AWalkFw0.v's. *)
(* Modified by Theorem Labs, 2026-10: derived from lib/A/AD2m.v of this library by derive_y.py: module names A.Axyz -> AU.Yxyz, addresses moved from libreac/fuzz_knock's asan image to its asan-ubsan image. The Modified-by lines above describe how lib/A/AD2m.v was made and quote that file's asan-image values; the code below carries the asan-ubsan values. *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import AWalkFw0.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YG0f YG00 YG0n YG0d YG0q.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.AU Require Import YF0m YD20 YD1i YE31 YE33.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YO09.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Lemma tfib_AICPY : aintrin_realizes tfibsegs B OCpy (pc_wrap_memcpy (as_code B)).
Proof.
pose proof (memcpy_icpt_realizes B (AR_laws_ok tfibsegs B) HB) as H.
unfold aintrin_realizes. rewrite (ts_code B HB). exact H.
Qed.
Lemma tfib_ARDCHK : aread_check_stmt B.
Proof.
exact (aread_check_realizes B (AR_laws_ok tfibsegs B) HB).
Qed.
End a.
