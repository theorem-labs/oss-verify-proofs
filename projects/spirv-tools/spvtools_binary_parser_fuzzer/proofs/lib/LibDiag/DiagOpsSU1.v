(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibBudget LibEff U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsNeeds.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DRepU1 DiagU1 DiagStmtsU1 SbOverflowU1 XsputnU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module Ly := U1Layout.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition PDIAG_STK : Z := 304.

Section OpsS.
Context {AC : AllocCeiling}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.
  #[local] Notation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).

  Definition pdiagS_stmt : Prop :=
    forall (fx : FPState) A (s : SX ST) R M model (sp ret S ds p pcons icount err : Z) (K : TSet),
      callB MI ST A s R M model sp ret S -> PDIAG_STK <= S -> ro_clear Ly.L M ->
      getr R 10%bv = Z_to_bv 64 ds -> getr R 11%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 (err mod 2 ^ 64) ->
      - 2 ^ 31 <= err < 0 ->
      fld SEGS M (p + 8) 8 pcons -> fld SEGS M (p + 80) 8 icount -> 0 <= p -> p + 88 <= 2 ^ 47 ->
      (forall a, zwin p (p + 88) a -> ~ zwin (sp - S) sp a) ->
      0 <= icount < 2 ^ 63 ->
      above_sp MI A sp ds DS_SIZE -> ds mod 8 = 0 -> mdef M ds DS_SIZE ->
      obj_ok MI A sp S pcons 48 -> pcons + 48 <= 2 ^ 47 -> pcons mod 16 = 0 -> fld SEGS M (pcons + 32) 8 0 ->
      (forall a, zwin ds (ds + DS_SIZE) a -> ~ zwin pcons (pcons + 48) a) ->
      (forall A' R' M' model' B,
          retB MI ST A' s R R' M' model model' ->
          ds_rep MI A' M' ds err 0 B ->
          blk_xfer [] B (live MI A) (live MI A') ->
          eff MI A A' M M' (sp - S, sp) (ds_foot ds B) ->
          srealizes SEGS (cfg fx R' ret M' model') K) ->
      srealizes SEGS (cfg fx R A_PDIAGE M model) K.

  Definition put_cstrS_stmt : Prop :=
    forall (fx : FPState) A (s : SX ST) R M model (sp ret S ds err len p n m : Z) (B : list (Z * Z)) (K : TSet),
      callB MI ST A s R M model sp ret S -> 192 + XS_STK MI <= S -> ro_clear Ly.L M ->
      getr R 10%bv = Z_to_bv 64 ds -> getr R 11%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 m ->
      ds_rep MI A M ds err len B -> above_sp MI A sp ds DS_SIZE ->
      ro_cstr SEGS Ly.L p n -> 0 <= m <= n -> len + m <= DS_MAXLEN -> ds_room SEGS Ly.L MI A ->
      (forall A' R' M' model' B' (J : Z -> Prop),
          retB MI ST A' s R R' M' model model' -> getr R' 10%bv = Z_to_bv 64 ds ->
          ds_rep MI A' M' ds err (len + m) B' -> blk_xfer B B' (live MI A) (live MI A') -> junk_ok MI A J ->
          eff MI A A' M M' (sp - S, sp) (fun a => ds_foot ds B a \/ ds_foot ds B' a \/ J a) ->
          srealizes SEGS (cfg fx R' ret M' model') K) ->
      srealizes SEGS (cfg fx R A_PUT_CSTR M model) K.
End OpsS.
