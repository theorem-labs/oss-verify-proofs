(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YN05 YB1u YG0h YG00 YG0u YG0d YG0w YF9j YD1v YD1f
YE3e YE3g.
Unset Lia Cache. Unset Nia Cache.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable B : asyms.
Hypothesis HB : TrbSyms B.
Lemma trb_AICPY : aintrin_realizes trbsegs B OCpy (pc_wrap_memcpy (as_code B)).
Proof.
pose proof (memcpy_icpt_realizes B (AR_laws_ok trbsegs B) HB) as H.
unfold aintrin_realizes. rewrite (ts_code B HB). exact H.
Qed.
Lemma trb_ARDCHK : aread_check_stmt B.
Proof.
exact (aread_check_realizes B (AR_laws_ok trbsegs B) HB).
Qed.
End a.
