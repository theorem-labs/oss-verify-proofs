(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib FPSteps LibIface LibEff.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section LibCall.
Context {AC : AllocCeiling}.
  Variable SEGS : list Segment.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.

  Variable LLVM_ENTRY : Z.
  Variable EMPTY_OBJ  : Z.
  Variable LIB_STACK  : Z.

  Variable LIB_CAPS   : Z -> Z.
  Variable LIB_BIGCAP : Z.

  Variable TD_LOCALE : Z.
  Variable GLOBAL_LOCALE : Z.

  #[local] Notation cfg fx R pc M model :=
    (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

  Definition lib_call_stmt : Prop :=
    forall (fx : FPState) (A : AS MI) (s : SX ST) (R : bvmap 5 word) (M : LibIface.mem) (model : Model)
           (sp ret p n : Z) (payload : list byte) (K : TSet),

      ainv MI A M model -> mstd model -> sx_inv ST s M -> sx_handler_set ST s ->
      ro_clear L M ->
      rdn SEGS M (Z_to_bv 64 TD_LOCALE) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 GLOBAL_LOCALE)) ->
      (forall a, owned MI A a -> ~ sx_region ST a) ->
      (forall a, errno_win L a -> ~ sx_region ST a) ->
      caps MI A = LIB_CAPS -> bigcap MI A = LIB_BIGCAP ->
      (length (live MI A) <= 2)%nat ->
      (forall q k, In (q, k) (live MI A) -> 0 < k <= 2 ^ 26) ->

      call_regs L R sp ret ->
      getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 n ->
      frm_zero (@fp_csr fx) ->

      0 <= n < 2 ^ 26 -> Z.of_nat (length payload) = n -> p mod 16 = 0 ->
      ((n = 0 /\ p = EMPTY_OBJ) \/ (0 < n /\ In (p, n) (live MI A))) ->
      rdn SEGS M (Z_to_bv 64 p) (Z.to_nat n) = Some payload ->

      alloc_ceiling + LIB_STACK <= sp -> stack_room SEGS M sp LIB_STACK ->
      (forall a, zwin (sp - LIB_STACK) sp a -> ~ owned MI A a /\ ~ sx_region ST a) ->

      (forall (fx' : FPState) A' s' R' M' model',
          ainv MI A' M' model' -> mstd model' -> m_fs model' = m_fs model -> m_fds model' = m_fds model ->
          sx_inv ST s' M' -> sx_le ST s s' ->
          kept R R' -> getr R' 10%bv = Z_to_bv 64 0 ->
          frm_zero (@fp_csr fx') ->
          (forall q k, In (q, k) (live MI A') <-> In (q, k) (live MI A)) ->
          eff MI A A' M M' (sp - LIB_STACK, sp) (sx_region ST) ->
          srealizes SEGS (cfg fx' R' ret M' model') K) ->
      srealizes SEGS (cfg fx R LLVM_ENTRY M model) K.
End LibCall.
