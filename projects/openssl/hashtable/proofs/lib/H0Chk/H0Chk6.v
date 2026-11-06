(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Uint63.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxHandoff FxDrive.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan H0Atable H0FiPre H0FiTail.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import H0FamilyAllDefs.
From OSSVerify.Proofs.openssl.hashtable.lib.H0Chk Require Import H0BrGlue2 H0GlueK H0ChkFast.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma chk_6 : forallb (leaf_chk 6 (TB_std 6) (CSL 6) XRNGf (XCHKf 6)) (tree_leaves (the_tree 6 FUEL)) = true.
Proof. apply forallb_leaf_chkL2_ok. vm_cast_no_check (eq_refl true). Qed.   (* [comment removed for export] *)
