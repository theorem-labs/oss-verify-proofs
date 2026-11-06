(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import Layout.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.K5.B08 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface Cf_iface Cf_clone Cf_boxcreate Cf_boxacreate Cf_parr16create Cf_boxaaddbox Cf_pixacreate Cf_boxadestroy_empty Cf_boxadestroy_one Cf_pixadestroy CfY_pixdestroy_null CfY_pixdestroy_rc CfY_numaadestroy CfY_dnaadestroy Cf_cfcreate Cf_cfdestroy.

Section CfTop.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis RERR : returnError_cps RT e_returnErrorPtr.

Theorem l_colorfillCreate_closed : l_colorfillCreate_cps RT.
Proof using AF GP RERR.
  exact (l_colorfillCreate_ok RT AF GP RERR (boxaCreate_ok RT AF GP) (boxCreate_ok RT AF GP) (boxaAddBox_ok RT AF GP) (pixClone_ok RT AF GP)
           (numaaCreate_ok RT AF GP) (l_dnaaCreate_ok RT AF GP) (pixaCreate_ok RT AF GP (boxaCreate_ok RT AF GP))).
Qed.

Theorem l_colorfillDestroy_closed : l_colorfillDestroy_cps RT.
Proof using AF GP.
  exact (l_colorfillDestroy_ok RT AF GP (pixDestroy_rc_ok RT AF GP) (pixDestroy_null_ok RT AF GP) (boxaDestroy_one_ok RT AF GP)
           (pixaDestroy_null_ok RT AF GP) (numaaDestroy_ok RT AF GP) (l_dnaaDestroy_ok RT AF GP)
           (pixaDestroy_ok RT AF GP (boxaDestroy_empty_ok RT AF GP))).
Qed.

(* [comment removed for export] *)
Theorem cf_cone_of_fuzz :
  (l_colorfillCreate_cps RT -> l_colorfillDestroy_cps RT -> cf_fuzz_one_cps RT) -> cf_fuzz_one_cps RT.
Proof using AF GP RERR. intros FZ. exact (FZ l_colorfillCreate_closed l_colorfillDestroy_closed). Qed.
End CfTop.
