(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare
     AxSymExec3 AxSymExec3Sound SegRun L5Defs L5Core L5CoreKit L5Kn L5KnA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanPlanCore AsanPlanSoundSums. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.muslA Require Import Ba0Sums_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnADec128P5_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNAREL.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation mem := (word -> option byte).

Lemma kept_reg regs regs' (k : nat) : APSX.kept_ok regs regs' -> (0 < k < 32)%nat -> ~ In k APC.caller_saved -> getr regs' (reg k) = getr regs (reg k).
Proof.
  intros H Hk NI. apply H.
  - intros E. apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E.
    rewrite Z.mod_small in E by lia. change (bv_unsigned (0%bv : bv 5)) with 0 in E. lia.
  - unfold AX2.ridx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. rewrite Nat2Z.id. exact NI.
Qed.

(* [comment removed for export] *)
Definition KEPT : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Theorem setshadow_f5_run (fx : FPState) (R : bvmap 5 word) (M : mem) (sh n rr : Z) :
  L5.img_clear M 1249280 1282048 -> L5.u64_at RSEGS M 1309752 2147450880 -> L5.u32_at RSEGS M 1309760 1 -> L5.u64_at RSEGS M 1283280 1219844 ->
  getr R (reg 10) = Z_to_bv 64 sh -> getr R (reg 11) = Z_to_bv 64 n -> getr R (reg 1) = Z_to_bv 64 rr -> rr mod 2 = 0 -> 0 <= rr < 2 ^ 64 ->
  0 <= n -> 0 <= sh -> sh + n < 2 ^ 64 -> L5.writable RSEGS M sh n ->
  exists (fx' : FPState) (R' : bvmap 5 word),
    msteps RSEGS (L5SAR.st fx R 0x7b90c M) (L5SAR.st fx' R' rr (wbytes M (Z_to_bv 64 sh) (repeat (Z_to_bv 8 245) (Z.to_nat n))))
    /\ (forall j, In j KEPT -> getr R' (reg j) = getr R (reg j)).
Proof.
  intros IMG CSB CUAR RMS Ra0 Ra1 Rra Hrr Hrr2 Hn Hsh Hshn WR.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 2))) as B2. change (bv_modulus 64) with (2 ^ 64) in B2.
  pose proof (PNADP5.adkQt_conc fx R M (fun j => match j with 2%nat => bv_unsigned (getr R (reg 2)) | _ => 0 end)) as P. cbn beta iota in P.
  specialize (P B2 (eq_sym (Z_to_bv_bv_unsigned 64 (getr R (reg 2)))) IMG CSB CUAR RMS).
  destruct P as (fx2 & R2 & M2 & _ & tFR & _ & (tMS & tKS & tR6 & tR11 & tR12)).
  assert (E2 : M2 = M) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply tFR). subst M2.
  destruct (as0_fill_spec_memset fx2 M (Z_to_bv 64 sh) (Z_to_bv 64 245) n R2 (Z_to_bv 64 rr)) as (R3 & MS3 & KO3 & _).
  { exact Hn. }
  { rewrite L5.unsigned_lit by (clear - Hsh Hshn Hn; lia). exact Hshn. }
  { pose proof (WR 0 (Z.to_nat n) ltac:(clear; lia) ltac:(clear - Hn; lia)) as X0. rewrite Z.add_0_r in X0. exact X0. }
  { rewrite L5.unsigned_lit by (clear; lia). unfold AX2.two64. clear; lia. }
  { apply Hoare.ret_ok_even. rewrite L5.unsigned_lit by (clear - Hrr2; lia). exact Hrr. }
  { rewrite L5K.rl1, (tKS 1%nat) by inl. exact Rra. }
  { rewrite L5K.rl10, (tKS 10%nat) by inl. exact Ra0. }
  { rewrite L5K.rl11. exact tR11. }
  { rewrite L5K.rl12, tR12. exact Ra1. }
  exists fx2, R3. split.
  - eapply msteps_trans; [exact tMS|]. rewrite (L5.unsigned_lit 245) in MS3 by (clear; lia). exact MS3.
  - intros j Hj. rewrite (kept_reg R2 R3 j KO3).
    + apply tKS. revert Hj. apply (L5K.incl_b KEPT PNADP5.KS_adkQt). vm_compute; reflexivity.
    + unfold KEPT in Hj. cbn [In] in Hj. clear - Hj. lia.
    + unfold KEPT in Hj. cbn [In] in Hj. unfold APC.caller_saved. cbn [In]. clear - Hj. lia.
Qed.
End PNAREL.
