(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD2m.v (donor image sha256 1c29845fe605), with its module paths changed, names TfibSyms -> GrantSyms. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YM05 YG0f YG00 YG0n YG0d YG0q. From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YB1v YF0m YD20 YD1i YE31 YE33.


Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YO09.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.
Hypothesis HB : GrantSyms B.
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
