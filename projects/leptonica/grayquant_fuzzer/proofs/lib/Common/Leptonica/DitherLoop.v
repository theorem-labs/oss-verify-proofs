(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk MemSplit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib DitherLib.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma al4_add : forall a k, a mod 4 = 0 -> (a + 4 * k) mod 4 = 0.
Proof. intros a k H. rewrite Z.add_mod by lia. rewrite H. rewrite Z.mul_comm, Z_mod_mult. reflexivity. Qed.
Lemma al16_sub : forall a k, a mod 16 = 0 -> k mod 16 = 0 -> (a - k) mod 16 = 0.
Proof.
  intros a k Ha Hk. destruct (Z.mod_divide a 16 ltac:(lia)) as [Da _]. destruct (Z.mod_divide k 16 ltac:(lia)) as [Dk _].
  destruct (Da Ha) as [x ->]. destruct (Dk Hk) as [y ->]. replace (x * 16 - y * 16) with ((x - y) * 16) by ring. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma row_bounds : forall wpl i h, 0 <= wpl -> 0 <= i -> i + 1 <= h -> 0 <= wpl * i /\ wpl * i + wpl <= wpl * h.
Proof.
  intros wpl i h Hw Hi Hh. split; [apply Z.mul_nonneg_nonneg; lia|].
  replace (wpl * i + wpl) with (wpl * (i + 1)) by ring. apply Z.mul_le_mono_nonneg_l; lia.
Qed.

Section WithSegs.
Context {fx : FPState}.
Variable segs : list Segment.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma rinv_weaken : forall r1 r2 (M0 Mi : word -> option byte), rinv r1 M0 Mi ->
  (forall r, In r r1 -> exists r', In r' r2 /\ fst r' <= fst r /\ fst r + snd r <= fst r' + snd r') -> rinv r2 M0 Mi.
Proof.
  intros r1 r2 M0 Mi [G F] I. split; [exact G|]. intros a Ha. apply F. intros r Hr IR.
  destruct (I r Hr) as (r' & Hr' & H1 & H2). apply (Ha r' Hr'). unfold inreg in *. lia.
Qed.

(* [comment removed for export] *)
Lemma rinv_wbytes : forall regs (M0 Mi : word -> option byte) (z n : Z) (bs : list byte), rinv regs M0 Mi ->
  Z.of_nat (length bs) = n -> 0 <= z < 2 ^ 64 -> z + n <= 2 ^ 64 ->
  (exists r, In r regs /\ fst r <= z /\ z + n <= fst r + snd r) -> rinv regs M0 (wbytes Mi (Z_to_bv 64 z) bs).
Proof.
  intros regs M0 Mi z n bs RI L Hz Hn (r & Hr & H1 & H2).
  apply (rinv_mframe regs [(z, n)] M0 Mi _ RI).
  - apply (mframe_wbytes [(z, n)] Mi Mi z _ bs n (mframe_refl _ _) eq_refl Hz Hn L). left. reflexivity.
  - intros c [<- | []]. exists r. cbn [fst snd]. split; [exact Hr | lia].
Qed.

Lemma regions_ok_grows : forall (M0 M1 : word -> option byte) regs, regions_ok segs M0 regs -> mem_grows M0 M1 -> regions_ok segs M1 regs.
Proof. intros M0 M1 regs RO G r Hr. destruct (RO r Hr) as (A & B & C & D). repeat split; try assumption. eapply store_ok_mono; eassumption. Qed.

End WithSegs.
