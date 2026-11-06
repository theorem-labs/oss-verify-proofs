(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ Require MallocInstS1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.R Require RImage RBridge.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocBlocks Malloc_iface.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import AcLia.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma mi_s1_heap_owned : forall (A : AS MallocInstS1.MI_S1) (M : LibIface.mem) (model : Model) (a : Z),
  ainv MallocInstS1.MI_S1 A M model -> 0 < a < alloc_ceiling -> ~ in_ranges (ly_img S1Layout.L) a ->
  (forall q k, In (q, k) (live MallocInstS1.MI_S1 A) -> ~ (q <= a < q + k)) ->
  owned MallocInstS1.MI_S1 A a.
Proof.
  intros A M model a _ Ha Himg Hlive. cbn. unfold MallocInstS1.a_owned, RBridge.rowned. right.
  split; [| split; [exact Ha|]].
  - pose proof (proj2 (MallocInstS1.in_ranges_img a)) as H. destruct (Z_lt_le_dec a R.RImage.RIMG_LO); [left; lia|].
    destruct (Z_lt_le_dec a R.RImage.RIMG_HI); [| right; lia]. exfalso. apply Himg, H. lia.
  - intros (b & Hin & Hb). apply (Hlive (blk_addr b) (blk_size b)); [| exact Hb].
    cbn. unfold MallocInstS1.a_live. apply in_map_iff. exists b. split; [reflexivity | exact Hin].
Qed.

End AC_1.
