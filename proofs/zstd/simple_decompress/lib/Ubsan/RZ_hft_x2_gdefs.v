(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition x2_geo (SPV lo DT WK wksz : Z) : Prop :=
  4096 <= lo /\ lo <= SPV - 1024 /\ SPV < 2^47
  /\ 4096 <= DT /\ DT + 16388 < 2^47 /\ 4096 <= WK /\ 2124 <= wksz < 2^32 /\ WK + wksz < 2^47
  /\ (DT + 16388 <= lo \/ SPV <= DT) /\ (WK + wksz <= lo \/ SPV <= WK) /\ (DT + 16388 <= WK \/ WK + wksz <= DT).
Ltac open_geo G := pose proof G as (LO0 & LOS & SPR & DTL & DTH & WKL & WKSZ & WKH & OFFDT & OFFWK & DTWK).

(* [comment removed for export] *)
Definition x2_frame (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (SPV DT WK tl T maxW : Z) (k0 k8 k16 k24 : word) (r0 : Z)
    (k136 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k240 k248 k264 k272 k280 : word) (wn wt : word) : list cell :=
  [C8 k0; C8 k8; C8 k16; C8 k24; C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (maxW + 1)); C8 (Z_to_bv 64 (tl + 1 - T));
   C8 (Z_to_bv 64 223338299392); C8 (Z_to_bv 64 (- (DT + 4) - 1)); C8 (Z_to_bv 64 12); C8 (Z_to_bv 64 (DT + 20));
   C8 (Z_to_bv 64 (tl + 1 - maxW)); C8 (Z_to_bv 64 (tl + 1)); C8 (Z_to_bv 64 WK); C8 (Z_to_bv 64 (- WK - 1)); C8 (Z_to_bv 64 (WK + 676));
   C8 k136; C8 k144; C8 k152; C8 k160; C8 k168; C8 k176; C8 k184; C8 k192; C8 k200; C8 k208; C8 k216; C8 k224;
   C8 (Z_to_bv 64 (DT + 4)); C8 k240; C8 k248; C8 (Z_to_bv 64 maxW); C8 k264; C8 k272; C8 k280; C4 wn; C4 wt;
   C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition okwT (T v : Z) : Prop := 0 <= v mod 256 <= T /\ 1 <= (v / 256) mod 256 <= 2.
Definition PREF2T (T cur : Z) (cw : list Z) : Prop := forall i, 0 <= i < cur -> okwT T (Znth (2 * i + 1) cw).

Lemma okwT_val T nb len : 0 <= nb <= T -> nb < 256 -> 1 <= len <= 2 -> okwT T (nb + 256 * len).
Proof.
  intros Hn H256 Hl. unfold okwT. replace ((nb + 256 * len) mod 256) with nb by (Z.div_mod_to_equations; lia).
  replace ((nb + 256 * len) / 256) with len by (Z.div_mod_to_equations; lia). rewrite Z.mod_small by lia. lia.
Qed.

Lemma pref2T_0 T cw : PREF2T T 0 cw.
Proof. intros i Hi. lia. Qed.

Lemma pref2T_mono T a b cw : PREF2T T b cw -> a <= b -> PREF2T T a cw.
Proof. intros P Hab i Hi. apply P. lia. Qed.

Lemma pref2T_T_le T T' cur cw : PREF2T T cur cw -> T <= T' -> PREF2T T' cur cw.
Proof. intros P HT i Hi. destruct (P i Hi) as (A & B). split; [lia | exact B]. Qed.

Lemma pref2T_pref2 T cur cw : PREF2T T cur cw -> T <= 12 -> PREF2 cur cw.
Proof. intros P HT i Hi. destruct (P i Hi) as (A & B). split; [lia | exact B]. Qed.

Lemma pref2T_write T cur cw cw' pos n v : PREF2T T cur cw -> cells_written cw cw' pos n v -> okwT T v -> 0 <= pos <= cur -> 0 <= n ->
  PREF2T T (Z.max cur (pos + n)) cw'.
Proof.
  intros PR (L & S & V) OKV Hp Hn i Hi.
  destruct (Z.lt_ge_cases i pos) as [A|A]; [rewrite S by lia; apply PR; lia|].
  destruct (Z.lt_ge_cases i (pos + n)) as [B|B]; [rewrite V by lia; exact OKV|].
  rewrite S by lia. apply PR. lia.
Qed.

(* [comment removed for export] *)
Definition x2_models (rank : list Z) (tl T maxW : Z) (rvl rs0 : list Z) : Prop :=
  Z.of_nat (length rvl) = 156 /\ Z.of_nat (length rs0) = 15 /\
  (forall w, 1 <= w <= maxW -> Znth w rvl = rv0 rank tl T w) /\
  (forall c w, tl + 1 - maxW <= c <= T - (tl + 1 - maxW) -> 1 <= w <= maxW -> Znth (13 * c + w) rvl = rvc rank tl T c w) /\
  (forall w, 1 <= w <= maxW + 1 -> Znth w rs0 = xs1 rank w).

(* [comment removed for export] *)
Definition X2G (m : fmem) (SPV lo DT WK wksz : Z) (fr : list cell) (hdr : list byte) (cw rvl rank rs0 : list Z) (syb : list byte) (m1 : fmem) : Prop :=
  rw_cells usegs m1 DT [CB 4 hdr] /\ x2_cells m1 DT cw
  /\ u32arr usegs m1 WK (map (Z_to_bv 64) rvl)
  /\ u32arr usegs m1 (WK + 624) (map (Z_to_bv 64) rank)
  /\ u32arr usegs m1 (WK + 676) (map (Z_to_bv 64) rs0)
  /\ bytes_at usegs m1 (WK + 736) syb /\ Z.of_nat (length syb) = 256 /\ stk usegs m1 (WK + 736) (WK + 992)
  /\ stk usegs m1 (WK + 992) (WK + wksz)
  /\ rw_cells usegs m1 (SPV + -400) fr /\ cells_size fr = 400%nat /\ stk usegs m1 lo (SPV + -400)
  /\ mem_inv usegs m1 /\ munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 1024, SPV)] m m1 /\ wmono usegs m m1.
Ltac open_x2g I := destruct I as (HDRC & CWS & RVA & RKA & RSA & SYB & SYLEN & SYS & WKR & FR & FRSZ & STK & MI & MU & WM).
Ltac close_x2g := unfold X2G; repeat (split; [eassumption|]); eassumption.
