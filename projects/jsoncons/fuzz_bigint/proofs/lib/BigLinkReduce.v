(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk AxSymExec3 Src0_code_21134_21d54 BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkShl.
Import ListNotations.
Open Scope Z_scope.

Module BRED.
Import BSHL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation RSEGS := Plain.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).

Lemma ret_to fx R M (pc : Z) (W : bv 32) r :
  fetch_word RSEGS (Z_to_bv 64 pc) = Some W -> is_ecall W = false -> decode_any W = Some (Jalr 0 1 0, 4%Z) ->
  getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R pc M) (st fx R r M).
Proof.
  intros HF HEC HD H1 Hr He. eapply mst_step; [reflexivity | | apply mst_refl].
  assert (D: decode_any W = Some (Jalr 0 (reg 1) (0%bv : bv 12), 4%Z)). { rewrite HD. repeat f_equal; apply bv_eq; reflexivity. }
  rewrite (step_jalr_x0 RSEGS R _ M (seg_rom RSEGS) _ (reg 1) (0%bv : bv 12) (Z_to_bv 64 r) HF HEC D H1).
  f_equal. f_equal. unfold v_jalr. f_equal. unfold jalr_tgtZ. change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r.
  rewrite BG.unsigned_lit by lia. apply land_m2_even; lia.
Qed.
Lemma ret_21574 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R 0x2161c M) (st fx R r M).
Proof. intros H1 Hr He. apply (ret_to fx R M 0x2161c W_2161c r F_2161c eq_refl D_2161c H1 Hr He). Qed.
Lemma ret_21580 fx R M r : getr R (reg 1) = Z_to_bv 64 r -> 0 <= r < 2 ^ 47 -> r mod 2 = 0 -> msteps RSEGS (st fx R 0x21628 M) (st fx R r M).
Proof. intros H1 Hr He. apply (ret_to fx R M 0x21628 W_21628 r F_21628 eq_refl D_21628 H1 Hr He). Qed.
End BRED.
