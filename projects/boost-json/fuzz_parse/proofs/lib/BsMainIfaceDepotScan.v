(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import BothPlanImagesHexZ BsMainIface.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "46Stdlib6ZArith6BinInt1Z04to_N69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsanHexTree~~~~~~he3zpt59OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan~~~~~~m2h7AsanUbsan_seg_bytes_00303sub" s.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma tab_zero_scan : ltac2:(zQ "40!h8!lc!pa!r5@3$1$2@1$0@2$3+ipvgl8+hrkgg0@1$0+kgggg0").
Proof. exact asan_tab_zero. Qed.
