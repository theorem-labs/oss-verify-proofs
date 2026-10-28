(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_blk_iface RZ_bfse_defs.
Import ListNotations.
Open Scope Z_scope.

Definition bf_al (DT W NC BASE : Z) : Prop := DT mod 4 = 0 /\ W mod 2 = 0 /\ NC mod 2 = 0 /\ BASE mod 4 = 0.

Lemma swrap32_negb2z : forall b, bv_swrap 32 (0 - Z.b2z b) = 0 - Z.b2z b.
Proof. destruct b; reflexivity. Qed.

Lemma lor_shl32_shr : forall f x, 0 <= f < 2^32 -> 0 <= x -> Z.shiftr (Z.lor f (Z.shiftl x 32)) 32 = x.
Proof.
  intros f x Hf Hx. rewrite Z.shiftr_lor, Z.shiftr_shiftl_l by lia. rewrite Z.sub_diag, Z.shiftl_0_r.
  rewrite (Z.shiftr_div_pow2 f 32) by lia. rewrite Z.div_small by lia. apply Z.lor_0_l.
Qed.

Lemma set_cell_fields_u : forall cells0 u0 n a b v, 0 <= u0 < FseNCount.Zlength cells0 ->
  let c1 := set_cell u0 (with_nbBits (cell_nth cells0 u0) b) cells0 in
  let c2 := set_cell u0 (with_next (cell_nth c1 u0) n) c1 in
  let c3 := set_cell u0 (with_nbAdd (cell_nth c2 u0) a) c2 in
  set_cell u0 (with_base (cell_nth c3 u0) v) c3 = set_cell u0 (mkSS n a b v) cells0.
Proof.
  intros cells0 u0 n a b v Hu c1 c2 c3.
  assert (L1 : FseNCount.Zlength c1 = FseNCount.Zlength cells0) by (unfold FseNCount.Zlength, c1; rewrite set_cell_length; reflexivity).
  assert (L2 : FseNCount.Zlength c2 = FseNCount.Zlength cells0) by (unfold FseNCount.Zlength, c2; rewrite set_cell_length; exact L1).
  assert (E1 : cell_nth c1 u0 = with_nbBits (cell_nth cells0 u0) b) by (unfold c1; apply cell_nth_set_cell_same; lia).
  assert (E2 : cell_nth c2 u0 = with_next (cell_nth c1 u0) n) by (unfold c2; apply cell_nth_set_cell_same; lia).
  assert (E3 : cell_nth c3 u0 = with_nbAdd (cell_nth c2 u0) a) by (unfold c3; apply cell_nth_set_cell_same; lia).
  rewrite E3, E2, E1. unfold c3, c2, c1. rewrite !set_cell_twice. reflexivity.
Qed.

Definition BFU (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : fmem) (SPV lo DT NC BASE BITS W tl : Z) (k : seq_kind)
    (wlen : nat) (norm : list Z) (h0 h1 w8 w16 : word) (cells : list seqsym) (symNext spread : list Z) (m1 : fmem) : Prop :=
  rw_cells usegs m1 DT [C4 h0; C4 h1]
  /\ u8arr usegs m1 (DT + 8) (cellsB cells) /\ zlenF cells = 2^tl
  /\ u8arr usegs m1 W (u16s (map (Z_to_bv 64) symNext)) /\ zlenF symNext = 53
  /\ u8arr usegs m1 (W + 106) (map (Z_to_bv 8) spread) /\ zlenF spread = Z.of_nat wlen - 106
  /\ bytes_at usegs m1 NC (u16s (map (Z_to_bv 64) norm))
  /\ bytes_at usegs m1 BASE (u32s (map (Z_to_bv 64) (kind_base k)))
  /\ bytes_at usegs m1 BITS (map (Z_to_bv 8) (kind_bits k))
  /\ stk usegs m1 lo (SPV + -128)
  /\ rw_cells usegs m1 (SPV + -128)
        [C8 (Z_to_bv 64 DT); C8 w8; C8 w16; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ mem_inv usegs m1 /\ munch [(DT, DT + 8 + 8 * 2^tl); (W, W + Z.of_nat wlen); (SPV - 128, SPV)] m m1 /\ wmono usegs m m1.
Ltac open_bfu I := destruct I as (HDR & CEL & CLEN & SNX & SNLEN & SPRD & SPLEN & NCB & BASEB & BITSB & STK & FR & MI & MU & WM).
Ltac close_bfu := split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
                  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption.
