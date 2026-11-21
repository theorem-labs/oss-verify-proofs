(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import NArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZPropExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZSeqExecP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import MemRel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DSLayout.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import LmatchModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import FillWinMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeMem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import SendModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BitsModel2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesTab.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import TreesRod.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeRod.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import BuildTreeModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import GenBitlenModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require  GenCodesModel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import DeflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import Trees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBitsLib.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefTreesApi.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTreeLib.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefPqdown_run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefGenCodes_run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTree1.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTree2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTree3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTree4.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTree5.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTree6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTree7.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefBuildTree8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Walk.
Variable F : franges.
Variable S : Z.
Variable p : ds_ptrs.
Variable PBL : Z.
Variable ds : deflate_state.
Variable sp : Z.
Variable (t : tree_id).
Local Notation PB := (p_pending_buf p).
Local Notation T := (S + toff t).
Local Notation E := (sd_elems t).
Local Notation SP := (sp - 192).
Local Notation U := (bt_upd ds t).
Let Htt : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ 1 <= tsize t <= 573 := toff_tsize t.
Local Notation stree_dl := (RefBuildTree1.stree_dl t).
Local Notation stF := (RefBuildTree1.stF t).
Local Notation X0 := (RefBuildTree1.X0 ds t).
Local Notation L1 := (RefBuildTree1.L1 t).
Local Notation tsize_elems := (RefBuildTree1.tsize_elems t).
Local Notation elems_range := (RefBuildTree1.elems_range t).
Local Notation dsc_off_val := (RefBuildTree1.dsc_off_val t).
Local Notation SDA_range := (RefBuildTree1.SDA_range t).
Local Notation STP_range := (RefBuildTree1.STP_range t).
Local Notation slen := (RefBuildTree2.slen t).
Local Notation slen_ge := (RefBuildTree2.slen_ge t).
Local Notation STP_rod := (RefBuildTree2.STP_rod t).
Local Notation stree_pb := (RefBuildTree2.stree_pb t).
Local Notation stree_dl_bound := (RefBuildTree2.stree_dl_bound t).
Local Notation stree_Len_dl := (RefBuildTree2.stree_Len_dl t).
Local Notation xbits := (GenBitlenModel.xbits t).
Local Notation stree_has_STP := (RefBuildTree2.stree_has_STP t).
Local Notation ml_range := (RefBuildTree5.ml_range t).
Local Notation base_range := (RefBuildTree5.base_range t).
Local Notation EXP_range := (RefBuildTree5.EXP_range t).
Local Notation L2 := (RefBuildTree2.L2 t).

Local Ltac nf := cbn [RefBuildTree1.stF].

Definition FB9 : list (nat * Z) :=
  [(0%nat, 65536); (1%nat, 65536); (2%nat, 573); (3%nat, 256); (4%nat, 65536); (5%nat, 16); (6%nat, 65536)].

Definition VB9 : bounds :=
  [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 64);
   (36%nat, 2 ^ 64); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64);
   (42%nat, 2 ^ 64); (43%nat, 2 ^ 64); (44%nat, 2 ^ 64); (45%nat, 2 ^ 64); (46%nat, 2 ^ 64); (47%nat, 2 ^ 64)].

Local Notation ML := (sd_max_length t).
Local Notation BASE := (sd_extra_base t).

End Walk.
