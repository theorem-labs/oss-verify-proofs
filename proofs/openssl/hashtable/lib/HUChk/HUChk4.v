(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Uint63.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxHandoff FxDrive.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AsanPlanCore CxPlan HUAtable HUFiPre HUFiTail.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import HUFamilyAllDefs.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib.HUChk Require Import HUBrGlue2 HUGlueK HUChkFast.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma chk_4 : forallb (leaf_chk 4 (TB_std 4) (CSL 4) XRNGf (XCHKf 4)) (tree_leaves (the_tree 4 FUEL)) = true.
Proof. apply forallb_leaf_chkL2_ok. vm_cast_no_check (eq_refl true). Qed.   (* [comment removed for export] *)
