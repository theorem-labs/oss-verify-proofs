(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/A/AD2m.v (donor image sha256 7093581aab04), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from A/AD2m.v for the ASan run at the 16 GiB limit (lib/BudgetWit/AW), with the modules it imports from that set renamed to their twins (suffix _w). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0f YG00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import YG0n_w YG0d_w YG0q_w.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A Require Import AF0m.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.BudgetWit.AW Require Import AD20_w AD1i_w AE31_w AE33_w.
Unset Lia Cache. Unset Nia Cache.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO09.
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
