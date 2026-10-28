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
Lemma chk_7 : forallb (leaf_chk 7 (TB_std 7) (CSL 7) XRNGf (XCHKf 7)) (tree_leaves (the_tree 7 FUEL)) = true.
Proof. apply forallb_leaf_chkL2_ok. vm_cast_no_check (eq_refl true). Qed.   (* [comment removed for export] *)
