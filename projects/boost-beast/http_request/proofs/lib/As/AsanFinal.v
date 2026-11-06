(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PairAsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require RefTop.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AsTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Final.
  Hypothesis AF : AFUZZ.
  Hypothesis AC : ACOST.

  Definition as_REAL : PairAsan.AS_REALIZES := as_realizes_spec AF AC.
  Definition as_SREAL : PairAsan.AS_SREALIZES := as_srealizes_spec AF AC.

  Definition asan_must_exit_of := PairAsan.asan_must_exit_scfg as_REAL.
  Definition halts_asan_of := PairAsan.halts_asan as_REAL.

  Section WithPlain.
    Hypothesis XF_plain : RefTop.XFUZZ.
    Definition asan_base_of := PairAsan.asan_base XF_plain as_SREAL.
    Definition asan_base_scfg_of := PairAsan.asan_base_scfg XF_plain as_SREAL.
  End WithPlain.
End Final.

Check as_REAL.
Check halts_asan_of.
Check asan_base_of.
