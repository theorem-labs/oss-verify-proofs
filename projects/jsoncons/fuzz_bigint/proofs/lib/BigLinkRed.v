(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk AxSymExec3 BigBranchSrc0 BigLinkBase BigLinkGlue.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module BR.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).

Lemma reg_lit15 : (15%bv : bv 5) = Z_to_bv 5 (Z.of_nat 15). Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_lit12 : (12%bv : bv 5) = Z_to_bv 5 (Z.of_nat 12). Proof. apply bv_eq. reflexivity. Qed.
Lemma reg_lit13 : (13%bv : bv 5) = Z_to_bv 5 (Z.of_nat 13). Proof. apply bv_eq. reflexivity. Qed.
Lemma pc_lit (z : Z) (w : word) : bv_unsigned w = z -> Z_to_bv 64 z = w.
Proof. intros H. symmetry. apply BG.word_of_unsigned. exact H. Qed.
Lemma br2155c_tk fx M R : getr R (reg 15) <> Z_to_bv 64 0 ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 0x21604) M (seg_rom RSEGS)) (@mkst fx R (Z_to_bv 64 0x21618) M (seg_rom RSEGS)).
Proof. intros H. rewrite (pc_lit 0x21604 (0x21604%bv : word)) by reflexivity. rewrite (pc_lit 0x21618 (0x21618%bv : word)) by reflexivity.
  apply br_2155c_tk. rewrite reg_lit15. exact H. Qed.
Lemma br2155c_ft fx M R : getr R (reg 15) = Z_to_bv 64 0 ->
  msteps RSEGS (@mkst fx R (Z_to_bv 64 0x21604) M (seg_rom RSEGS)) (@mkst fx R (Z_to_bv 64 0x21608) M (seg_rom RSEGS)).
Proof. intros H. rewrite (pc_lit 0x21604 (0x21604%bv : word)) by reflexivity. rewrite (pc_lit 0x21608 (0x21608%bv : word)) by reflexivity.
  apply br_2155c_ft. rewrite reg_lit15. exact H. Qed.
End BR.
