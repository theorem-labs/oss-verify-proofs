(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_stage1_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section WS.
  Variable E : s1env.
  Hypothesis OK : env_ok_b E.
  Hypothesis SHZ : b1_shz E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma b1_ws_loop : forall (Q : machine_state -> Prop) (fw : nat) (i : Z) (out : list Z) (err : Z) xa1 xa2 xa3 xs5 xs6 xt6 (m1 : mem),
    B1INV E m1 out i err -> (0 <= i < len)%Z -> (len - i <= Z.of_nat fw)%Z ->
    (forall xt5' xt6' m1', B1INV E m1' out (ws_run bs fw i) err ->
       evt bsegs Q (B1ST E 0xb3538 xa1 (Z_to_bv 64 len) xa3 (Z_to_bv 64 len) xs5 xs6 xt5' xt6' m1')) ->
    evt bsegs Q (B1ST E 0xb34d8 xa1 xa2 xa3 (Z_to_bv 64 len) xs5 xs6 (Z_to_bv 64 i) xt6 m1).
  Proof using OK SHZ.
    intros Q fw. induction fw as [|fw IH]; intros i out err xa1 xa2 xa3 xs5 xs6 xt6 m1 INV Hi Hfw HX; [exfalso; lia|].
    destruct OK as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, B1_STACK, B1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (B_range bs i BOK) as CR. set (c := B bs i) in *.
    pose proof (tbl_range c) as TR.
    pose proof INV as INV'. b1_open_inv INV'.
    pose proof (rw_cells_CB_bytes_at _ _ _ _ _ FRtb) as TBL.
    pose proof (buf_read m1 (e_BUF E) bs i BUFRO ltac:(lia)) as RD1. fold c in RD1.
    pose proof (tbl_read m1 _ c TBL CR) as RD2.
    rewrite ws_run_S in HX. fold c in HX.
    zstep. zstep. s1norm. zstep. zstep.
    if_cases G1; zify_cond G1; [|exfalso; lia].
    zstep. if_cases G2; zify_cond G2; [|exfalso; lia].
    b1_shz_buf SHZ (e_BUF E + i)%Z.
    zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_false.
    zstep. s1norm. zstep. zstep. s1norm. zstep. zstep. s1norm. zstep.
    if_cases K; zify_cond K.
    -
      assert (TS : t_space c = false) by (unfold t_space; rewrite (proj2 (Z.eqb_eq _ _) K); reflexivity).
      rewrite TS in HX.
      apply HX. exact INV.
    - assert (TS : t_space c = true) by (unfold t_space; rewrite (proj2 (Z.eqb_neq _ _) K); reflexivity).
      rewrite TS in HX.
      zstep. s1norm. zstep. zstep.
      s1_cur_mem ltac:(fun mm => assert (INV2 : B1INV E mm out (i + 1) err) by b1_close_inv).
      if_cases K2; zify_cond K2.
      + assert (LT : (i + 1 <? len)%Z = true) by (apply Z.ltb_lt; lia).
        rewrite LT in HX.
        apply (IH (i + 1)%Z out err); try assumption; lia.
      + assert (LT : (i + 1 <? len)%Z = false) by (apply Z.ltb_ge; lia).
        rewrite LT in HX.
        zstep.
        apply HX. exact INV2.
  Qed.
End WS.
