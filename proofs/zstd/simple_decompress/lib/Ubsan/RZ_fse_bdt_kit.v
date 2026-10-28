(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FseReadSound ZdFrame ZdSeqBuild ZdSeqBuildThm ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildW4.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_hft_iface RZ_hft_bdt_defs.
Import ListNotations.
Open Scope Z_scope.

Definition BDU (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : fmem) (SPV lo DT NC W wlen maxSV tl : Z) (norm : list Z)
    (h0 h1 : word) (tb sn sp : list Z) (m1 : fmem) : Prop :=
  rw_cells usegs m1 DT [C2 h0; C2 h1]
  /\ u8arr usegs m1 (DT + 4) (map (Z_to_bv 8) tb) /\ zlenF tb = 4 * 2^tl /\ Forall isbyte tb
  /\ u8arr usegs m1 W (u16s (map (Z_to_bv 64) sn)) /\ zlenF sn = maxSV + 1
  /\ u8arr usegs m1 (W + 2 * (maxSV + 1)) (map (Z_to_bv 8) sp) /\ zlenF sp = wlen - 2 * (maxSV + 1) /\ Forall isbyte sp
  /\ bytes_at usegs m1 NC (u16s (map (Z_to_bv 64) norm))
  /\ stk usegs m1 lo (SPV + -128)
  /\ rw_cells usegs m1 (SPV + -128) [C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (W + 2 * maxSV)); C8 (Z_to_bv 64 tl);
                                     C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ mem_inv usegs m1 /\ munch [(DT, DT + 4 + 4 * 2^tl); (W, W + wlen); (SPV - 128, SPV)] m m1 /\ wmono usegs m m1.

Lemma hdr_wordU : forall tl fast, 5 <= tl <= 9 -> 0 <= fast <= 1 ->
  le4 (Z_to_bv 64 (65536 * fast + tl)) = le2 (Z_to_bv 64 tl) ++ le2 (Z_to_bv 64 fast).
Proof.
  intros tl fast Ht Hf.
  assert (C : (tl = 5 \/ tl = 6 \/ tl = 7 \/ tl = 8 \/ tl = 9) /\ (fast = 0 \/ fast = 1)) by lia.
  destruct C as ([E|[E|[E|[E|E]]]] & [E2|E2]); subst tl fast; unfold le4, le2; cbn [Z_to_le_bytes app];
    repeat (f_equal; try (apply bv_eq; vm_compute; reflexivity)).
Qed.

Lemma land1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. apply (Z.land_ones x 1). lia. Qed.
Lemma land255 : forall x, Z.land x 255 = x mod 256.
Proof. intros x. apply (Z.land_ones x 8). lia. Qed.
Lemma land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. apply (Z.land_ones x 2). lia. Qed.

Lemma hdr_c4 : forall segs m A h0 h1, rw_cells segs m A [C2 h0; C2 h1] ->
  rw_cells segs m A [C4 (le_bytes_to_word (le2 h0 ++ le2 h1))].
Proof.
  intros segs m A h0 h1 HDR.
  eapply rw_cells_recell; [exact HDR | cbn; split; exact Logic.I |].
  cbn [cells_bytes cbytes app]. rewrite app_nil_r.
  pose proof (le_val_range _ (bytes_ok_map (le2 h0 ++ le2 h1))) as HR4. rewrite length_map, length_app, !length_le2 in HR4.
  change (256 ^ Z.of_nat (2 + 2)) with 4294967296 in HR4. rewrite <- bytes_le_to_Z_le_val in HR4.
  unfold le4, le_bytes_to_word. rewrite unsigned_lit by lia.
  change 4%nat with (length (le2 h0 ++ le2 h1)) at 1. rewrite Z_to_le_bytes_to_Z. reflexivity.
Qed.

Lemma Zupd_comm : forall (l : list Z) a b x y, 0 <= a -> 0 <= b -> a <> b ->
  Zupd a x (Zupd b y l) = Zupd b y (Zupd a x l).
Proof.
  intros l a b x y Ha Hb Hab. unfold Zupd.
  assert (NE : Z.to_nat a <> Z.to_nat b) by lia.
  revert NE. generalize (Z.to_nat a) (Z.to_nat b). clear Ha Hb Hab.
  induction l as [|h t IH]; intros [|i] [|j] NE; cbn [upd_nat]; try reflexivity.
  - exfalso. apply NE. reflexivity.
  - f_equal. apply IH. congruence.
Qed.

Lemma shl32_shr31 : forall x, 0 <= x < 2^31 -> ((x ≪ 32) mod 18446744073709551616) ≫ 31 = 2 * x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (x * 2^32) with ((2 * x) * 2^31) by (change (2^32) with (2 * 2^31); lia). apply Z.div_mul. lia.
Qed.
Lemma shl32_shr32 : forall x, 0 <= x < 2^32 -> ((x ≪ 32) mod 18446744073709551616) ≫ 32 = x.
Proof. intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_mul. lia. Qed.

Notation znot x := (Z.lxor x 18446744073709551615).

Ltac bd_chk := let K := fresh "KC" in
  if_cases K; zify_cond K;
  [exfalso; rewrite ?land1, ?land3 in K; rewrite ?zb_lxor_ones in K by lia; Z.div_mod_to_equations; lia | clear K].
