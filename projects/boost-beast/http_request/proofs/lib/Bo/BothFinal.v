(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PairBoth.
From OSSVerify.Proofs.boost_beast.http_request.lib Require RefTop.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BoTop.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Final.
  Hypothesis BF : BFUZZ.
  Hypothesis BC : BCOST.

  Definition bo_REAL : PairBoth.BO_REALIZES := bo_realizes_spec BF BC.
  Definition bo_SREAL : PairBoth.BO_SREALIZES := bo_srealizes_spec BF BC.

  Definition both_must_exit_of := PairBoth.both_must_exit_scfg bo_REAL.
  Definition halts_both_of := PairBoth.halts_both bo_REAL.

  Section WithPlain.
    Hypothesis XF_plain : RefTop.XFUZZ.
    Definition both_base_of := PairBoth.both_base XF_plain bo_SREAL.
    Definition both_base_scfg_of := PairBoth.both_base_scfg XF_plain bo_SREAL.
  End WithPlain.
End Final.

Check bo_REAL.
Check halts_both_of.
Check both_base_of.
