(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface
  RF_huf_x4body_iface RF_huf_x4body RF_huf_x4e RF_huf_x4sf.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Theorem dec_4x1_proof : dec4_int_stmt x1_tab PHUF_DX1_4X.
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m DST dcap SR DT mtl flags src jd lo
    MTL TAB HD DC SRCB BYS NSM S16 SP0 DT0 DT8 DTL DL SL DJ1 DJ2 DJ3 STK LOS SP16 SP47 MI FL E0 E1 E2 E3 E4 E5.
  subst a0 a1 a2 a3 a4 a5.
  destruct TAB as (tl & cells & HDR & ZC & TOK & TLE & CBB).
  pose proof TOK as (TL & TLEN & _). unfold HUF_TABLELOG_MAX in TL.
  assert (P0 : 0 < 2^tl) by (apply Z.pow_pos_nonneg; lia).
  assert (P2 : 2^tl <= 2^(mtl+1)) by (apply Z.pow_le_mono_r; lia).
  assert (P2' : 2^(mtl+1) = 2 * 2^mtl) by (rewrite Z.pow_add_r by lia; lia).
  unfold DTABLE_BYTES, HufHarness.DT_BYTES in DTL, DJ1.
  unfold HUF_DEC_STACK in LOS.
  assert (DTA : DT mod 4 = 0) by (Z.div_mod_to_equations; lia).
  assert (LCB : zlen (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells)) = 2 * 2^tl)
    by (rewrite length_firstn, x1_bytes'_length; lia).
  assert (BUF : exists buf, u8arr usegs m DST (map (Z_to_bv 8) buf) /\ zlen buf = dcap).
  { destruct HD as [(-> & ->) | (DP & D8 & RW)].
    - exists []. split; [| reflexivity]. split; [apply bytes_at_nil; lia |].
      unfold wr_at. cbn [map length Z.of_nat]. split; [lia | split; [lia | intros; lia]].
    - exists (map bv_unsigned jd).
      pose proof (proj1 (proj1 RW)) as WF. cbn in WF. destruct WF as (WF & _).
      rewrite map_map, (map_ext _ (fun x => x))
        by (intros; apply bv_eq; rewrite Z_to_bv_unsigned;
            first [apply bv_wrap_bv_unsigned | apply bv_wrap_small, bv_unsigned_in_range]).
      rewrite map_id.
      split; [exact (u8arr_of_rw_cells usegs m DST _ jd RW) | rewrite length_map; lia]. }
  destruct BUF as (buf & ARR & LB).
  eapply (x4_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DST dcap SR DT mtl tl lo src cells
            (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells))).
  all: try (intros mm xra x5 x6 x7 x9 y0 y1 y2 y6 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HX;
            eapply (x4s_slow ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DST dcap SR DT mtl tl lo src cells
                      (firstn (Z.to_nat (2 * 2^tl)) (x1_bytes' cells))); [ .. | exact HX ]).
  all: try exact x4_body_proof.
  all: try first [ exact ARR | exact CBB | exact LB | eassumption | reflexivity ].
  all: try (destruct HD as [(? & ?) | (? & ? & ?)]; intros; lia).
  all: try (destruct DJ1; lia).
  all: lia.
Qed.
End CANSEC1.
