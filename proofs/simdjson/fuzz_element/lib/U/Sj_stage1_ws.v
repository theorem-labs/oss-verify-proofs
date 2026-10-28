(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage1_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section WS.
  Variable E : s1env.
  Hypothesis OK : env_ok_u E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma u1_ws_loop : forall (Q : machine_state -> Prop) (fw : nat) (i : Z) (out : list Z) (err : Z) xra xa0 xa3 xa5 xt3 xt5 xt6 (m1 : mem),
    U1INV E m1 out i err -> (0 <= i < len)%Z -> (len - i <= Z.of_nat fw)%Z ->
    (forall xt5' m1', (ws_run bs fw i < len)%Z -> t_space (B bs (ws_run bs fw i)) = false -> U1INV E m1' out (ws_run bs fw i) err ->
       evt usegs Q (U1ST E 0x41b68 xra xa0 (Z_to_bv 64 len) xa5 (Z_to_bv 64 (ws_run bs fw i)) (Z_to_bv 64 len) xt3 xt5' xt6 m1')) ->
    (forall xa3' xt5' m1', (len <= ws_run bs fw i)%Z -> U1INV E m1' out (ws_run bs fw i) err ->
       evt usegs Q (U1ST E 0x41f10 xra xa0 xa3' xa5 (Z_to_bv 64 (ws_run bs fw i)) (Z_to_bv 64 len) xt3 xt5' xt6 m1')) ->
    evt usegs Q (U1ST E 0x41b24 xra xa0 xa3 xa5 (Z_to_bv 64 i) (Z_to_bv 64 len) xt3 xt5 xt6 m1).
  Proof using OK.
    intros Q fw. induction fw as [|fw IH]; intros i out err xra xa0 xa3 xa5 xt3 xt5 xt6 m1 INV Hi Hfw HA HB; [exfalso; lia|].
    destruct OK as [OKB BUFP IDXP ALIGN].
    destruct OKB as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, U1_STACK, U1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (B_range bs i BOK) as CR. set (c := B bs i) in *.
    pose proof (tbl_range c) as TR.
    pose proof INV as INV'. u1_open_inv INV'.
    pose proof (rw_cells_CB_bytes_at _ _ _ _ _ FRtb) as TBL.
    pose proof (ubuf_read m1 (e_BUF E) bs i BUFRO ltac:(lia)) as RD1. fold c in RD1.
    pose proof (utbl_read m1 _ c TBL CR) as RD2.
    rewrite ws_run_S in HA, HB. fold c in HA, HB.
    zstep. zstep. s1norm. zstep. zstep.
    if_cases G1; zify_cond G1; [|exfalso; lia].
    zstep. if_cases G2; zify_cond G2; [|exfalso; lia].
    zstep. s1norm. zstep. zstep. s1norm. zstep. zstep. s1norm. zstep.
    if_cases K; zify_cond K.
    -
      assert (TS : t_space c = false) by (unfold t_space; rewrite (proj2 (Z.eqb_eq _ _) K); reflexivity).
      rewrite TS in HA.
      zstep. if_cases KGE; zify_cond KGE; [exfalso; lia|].
      apply HA; [lia | exact TS| exact INV].
    - assert (TS : t_space c = true) by (unfold t_space; rewrite (proj2 (Z.eqb_neq _ _) K); reflexivity).
      rewrite TS in HA, HB.
      zstep. s1norm. zstep. zstep.
      assert (INV2 : U1INV E m out (i + 1) err) by u1_close_inv.
      if_cases K2; zify_cond K2.
      + assert (LT : (i + 1 <? len)%Z = true) by (apply Z.ltb_lt; lia).
        rewrite LT in HA, HB.
        apply (IH (i + 1)%Z out err); try assumption; lia.
      + assert (LT : (i + 1 <? len)%Z = false) by (apply Z.ltb_ge; lia).
        rewrite LT in HB.
        zstep. if_cases KGE; zify_cond KGE; [|exfalso; lia].
        apply HB; [lia| exact INV2].
  Qed.
End WS.
