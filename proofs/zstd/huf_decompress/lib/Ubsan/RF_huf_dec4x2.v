(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_tac FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_fa_iface
  RF_huf_y4s_iface RF_huf_fargs RF_huf_y4e RF_huf_y4fast RF_huf_y4fin4.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Theorem dec_4x2_proof_slow : y4_slow_stmt -> dec4_int_stmt x2_tab PHUF_DX2_4X.
Proof.
  intros YS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m DST dcap SR DT mtl flags src jd lo
    MTL TAB HD DC SRCB BYS NSM S16 SP0 DT0 DT8 DTL DL SL DJ1 DJ2 DJ3 STK LOS SP16 SP47 MI FL E0 E1 E2 E3 E4 E5.
  subst a0 a1 a2 a3 a4 a5.
  destruct TAB as (tl & cells & HDR & ZC & TOK & TLE & CBB).
  pose proof TOK as (TL & TLEN & _). unfold HUF_TABLELOG_MAX in TL.
  assert (P0 : 0 < 2^tl) by (apply Z.pow_pos_nonneg; lia).
  assert (P2 : 2^tl <= 2^mtl) by (apply Z.pow_le_mono_r; lia).
  assert (DT4 : DT mod 4 = 0) by (Z.div_mod_to_equations; lia).
  unfold DTABLE_BYTES, HufHarness.DT_BYTES in DTL, DJ1.
  unfold HUF_DEC_STACK in LOS.
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
  assert (DPOS : 0 < dcap -> 8 <= DST) by (destruct HD as [(? & ?) | (? & ? & ?)]; intros; [lia | Z.div_mod_to_equations; lia]).
  assert (DNN : 0 <= DST) by (destruct HD as [(? & ?) | (? & ? & ?)]; lia).
  assert (LCB : zlen (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells)) = 4 * 2^tl)
    by (rewrite length_firstn, x2_bytes'_length; lia).
  eapply (y4_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DST dcap SR DT mtl tl lo src cells
            (firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells))).
  all: try first [ exact ARR | exact LB | exact SRCB | exact CBB | exact HDR | exact STK | exact MI | exact FL
                 | exact LCB | eassumption | reflexivity | lia ].
  - eapply YS; first [ eassumption | reflexivity | lia ].
  - intros TL11 DCP SG. subst tl.
    assert (E11 : 2^11 = 2048) by reflexivity. rewrite E11 in *.
    intros. eapply y4_outer; try eassumption; try reflexivity; try lia.
    all: try (change (4 * 2^11) with 8192; first [ reflexivity | lia ]).
    all: intros; eapply (y4_wb ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m DST dcap SR DT lo src cells);
      first [ eassumption | reflexivity | lia ].
Qed.
End CANSEC1.
