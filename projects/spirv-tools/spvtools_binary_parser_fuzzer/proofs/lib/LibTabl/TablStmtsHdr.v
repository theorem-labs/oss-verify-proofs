(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibEff.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablStmts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section StmtsHdr.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
#[local] Abbreviation fld := (CRep.fld SEGS).
#[local] Abbreviation sx32 := TablStmts.sx32.

Definition header_get_stmt (entry stk : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (pb ph words n e sp : Z) (ret : word),
    ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 pb -> getr R 11%bv = Z_to_bv 64 e -> getr R 12%bv = Z_to_bv 64 ph ->
    getr R 2%bv = Z_to_bv 64 sp ->
    fld M pb 8 words -> fld M (pb + 8) 8 n -> 5 <= n < 2 ^ 61 -> 0 < words -> words + 4 * n <= 2 ^ 47 ->
    mdef M words 20 -> 0 <= e < 2 ->
    alloc_ceiling <= ph -> ph + 32 <= 2 ^ 47 -> mdef M ph 32 ->
    alloc_ceiling <= pb -> pb + 16 <= 2 ^ 47 ->
    pb mod 8 = 0 -> ph mod 8 = 0 -> words mod 4 = 0 ->
    (forall a, zwin (sp - stk) sp a -> ~ zwin ph (ph + 32) a /\ ~ zwin pb (pb + 16) a /\ ~ zwin words (words + 20) a) ->
    (forall a, zwin ph (ph + 32) a -> ~ zwin pb (pb + 16) a /\ ~ zwin words (words + 20) a) ->
    stack_room SEGS M sp stk -> alloc_ceiling <= sp - stk -> sp < 2 ^ 47 -> sp mod 16 = 0 ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R' M' (r : Z),
      msteps SEGS (@mkst fx R (Z_to_bv 64 entry) M (seg_rom SEGS)) (@mkst fx R' ret M' (seg_rom SEGS))
      /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ (r = 0 \/ r = -4)
      /\ frame_eq (fun a => zwin ph (ph + 32) a \/ zwin (sp - stk) sp a) M M'
      /\ (forall a : word, M a <> None -> M' a <> None).

Definition peek_at_stmt (entry : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (p i words e : Z) (ret : word),
    ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 i ->
    fld M (p + 48) 8 words -> fld M (p + 88) 4 e -> 0 <= e < 2 ->
    0 < words -> words mod 4 = 0 -> 0 <= i -> words + 4 * i + 4 <= 2 ^ 47 -> mdef M (words + 4 * i) 4 ->
    alloc_ceiling <= p -> p + 96 <= 2 ^ 47 -> p mod 8 = 0 ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R',
      msteps SEGS (@mkst fx R (Z_to_bv 64 entry) M (seg_rom SEGS)) (@mkst fx R' ret M (seg_rom SEGS))
      /\ kept R R' /\ exists r, 0 <= r < 2 ^ 32 /\ getr R' 10%bv = Z_to_bv 64 (sx32 r).
End StmtsHdr.
