(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/fast_float/from_chars/lib/PTgt7.v, with its module paths and module names changed; 331 of its 352 lines of code are new or changed and 151 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/tinyobjloader/fuzz_tobj_c/lib/U/L1/lo_entry.v, with its module paths and module names changed; 10 of its 32 lines of code are new or changed and 330 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocLayout MallocLaws Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymCFG SymEntail SymFrame SymSummary Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv CursorGlue TobjJV TobjJVx TobjJVA TobjJVAx TobjJVAy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L1 Require Import S_lo.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* The text buffer handed to a handler lies in a block the fuzz input owns. *)
Lemma txt_extra_ok_U : forall FB rho0 rho kept R o a,
  LD.P0_lo FB rho0 -> agree_vals LD.NP rho0 rho -> In o R -> LD.is_txt o = true ->
  fst (obj_range rho o) <= a < snd (obj_range rho o) -> pclF segsU C_U rho0 (FBx FB rho kept) a.
Proof.
  intros FB rho0 rho kept R o a HP0 Hav Ho Ht Hr. unfold LD.is_txt in Ht.
  apply andb_prop in Ht as [Ht H3]. apply andb_prop in Ht as [H1 H2].
  apply sv_eqb_sound in H1. apply sv_eqb_sound in H2. apply sv_eqb_sound in H3.
  unfold obj_range, obj_lo_of, obj_hi_of in Hr. rewrite H1, H2, H3 in Hr. cbn [fst snd] in Hr.
  unfold LD.vB, LD.vL in Hr. rewrite soff_lit_small in Hr by lia. unfold soff in Hr. rewrite !eval_var in Hr.
  destruct Hav as [Hw _]. rewrite <- (Hw 13%positive ltac:(reflexivity)), <- (Hw 14%positive ltac:(reflexivity)) in Hr.
  rewrite bv_signed_U in Hr.
  right; right.
  pose proof (bv_urange (rw rho0 14)) as R14.
  destruct HP0 as [Hz | (b & n & Hin & Hb & Hbn)].
  - exfalso. rewrite Hz in Hr. destruct (Zsigned_spec 0) as [[_ X]|[X1 X]]; rewrite X in Hr; lia.
  - exists b, n. split; [apply In_FBx; left; exact Hin|].
    destruct (Zsigned_spec (bv_unsigned (rw rho0 14))) as [[_ X]|[X1 X]]; rewrite X in Hr; unfold M64v in *; lia.
Qed.
