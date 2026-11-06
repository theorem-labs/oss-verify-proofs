(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Top0Gc4. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsPlanImagesHexZ AsMainIface.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "46Stdlib6ZArith6BinInt1Z04to_N69OSSVerify6Proofsaboost_jsonafuzz_parse3libbAsanHexTree~~~~~~he3zpt59OSSVerifyaboost_jsonafuzz_parse6images4Asan~~~~~~m2h2Asan_seg_bytes_00303sub" s.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma tab_zero_scan : ltac2:(zQ "40!h8!lc!p5!qb@3$1$2@1$0@2$3+iqihh8+hrngg0@1$0+kgggg0").
Proof.
  apply (AsanHexTree.ztree_scan_sound _ ((120355%positive, 3%nat) :: (30089%positive, 5%nat) :: (15045%positive, 6%nat) :: (7523%positive, 7%nat) :: (1881%positive, 9%nat) :: (941%positive, 10%nat) :: (471%positive, 11%nat) :: (59%positive, 14%nat) :: (15%positive, 16%nat) :: (1%positive, 20%nat) :: (1%positive, 21%nat) :: (8%positive, 19%nat) :: (18%positive, 18%nat) :: (38%positive, 17%nat) :: (156%positive, 15%nat) :: (628%positive, 13%nat) :: (1258%positive, 12%nat) :: (20144%positive, 8%nat) :: (322320%positive, 4%nat) :: (644642%positive, 3%nat) :: nil)).
  - AsanHexTree.gall_vm.
  - vm_compute; reflexivity.
Qed.
