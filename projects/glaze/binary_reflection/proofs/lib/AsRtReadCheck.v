(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIcpyS.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPGen1.
Context {fx : FPState}.
#[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Definition rdchk_words : list (option (bv 32)) :=
  [Some W_5e260; Some W_5e264; Some W_5e268; Some W_5e26c; Some W_5e270; Some W_5e274; Some W_5e278; None; None;
   Some W_5e284; Some W_5e288; Some W_5e28c; Some W_5e290; Some W_5e294; Some W_5e298; Some W_5e29c; Some W_5e2a0;
   Some W_5e2a4; Some W_5e2a8; Some W_5e2ac; Some W_5e2b0; Some W_5e2b4].




Section RC.
  Variable segs : list Segment.
  Variable base : word.
  Variables g_shoff p_shoff : Z.
  Hypothesis HCODE : code_ato segs base 0 rdchk_words.
  Hypothesis G28 : gload segs base 28 11 g_shoff.





















  Variables (mem rom : word -> option byte) (dst : word) (res : Z).
  Hypothesis Hres : (1 <= res <= 64)%Z.
  Hypothesis Hdst : (0x10007fff8000 <= U dst)%Z /\ (U dst + 72 <= 0x800000000000)%Z.
  Hypothesis Hcells : (0 <= g_shoff /\ g_shoff + 8 <= 2 ^ 64)%Z /\ (0 <= p_shoff /\ p_shoff + 8 <= 2 ^ 64)%Z.
  Hypothesis Rg : rdn segs mem (Z_to_bv 64 g_shoff) 8 = Some (LE8 p_shoff).
  Hypothesis Rsb : rdn segs mem (Z_to_bv 64 p_shoff) 8 = Some (LE8 0x7fff8000).
  Hypothesis Rz : forall a : word, (down8 (Sh (U dst)) <= U a < down8 (Sh (U dst)) + 16)%Z ->
                    rdn segs mem a 1 = Some [Z_to_bv 8 0].

  #[local] Abbreviation E := (U dst + res - 1)%Z.



  Ltac gl G Hr := eapply msteps_trans; [ eapply G; exact Hr | ]; zlit_at.
  Ltac cld F D vv Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
        [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Hr | apply bytes_le_to_Z_8]
      | step_simpl]; vn.
  Ltac cldz F D Hr :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := zeros 8) (v := Z_to_bv 64 0);
        [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0; exact Hr | reflexivity]
      | step_simpl]; vn.


End RC.

End FPGen1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Section FPGen2.
Context {fx : FPState}.
#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).




End FPGen2.
