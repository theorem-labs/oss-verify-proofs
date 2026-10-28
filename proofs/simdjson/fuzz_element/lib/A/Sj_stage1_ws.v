(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_stage1_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WS.
  Variable E : s1env.
  Hypothesis OK : env_ok E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma a1_ws_loop : forall (Q : machine_state -> Prop) (fw : nat) (i : Z) xra xa0 xa1 xa2 xa3 xs11 xt3 xt4 (m1 : mem),
    bytes_at asegs m1 (e_BUF E) (padded_bytes bs) ->
    bytes_at asegs m1 (bv_unsigned (e_sp E) + -400) TABLE_BYTES ->
    shz m1 (e_BUF E) (len + 8) ->
    (0 <= i < len)%Z -> (len - i <= Z.of_nat fw)%Z ->
    (forall xt3', (ws_run bs fw i < len)%Z -> t_space (B bs (ws_run bs fw i)) = false ->
       evt asegs Q (A1ST E 0xba498 xra (Z_to_bv 64 (ws_run bs fw i + 2)) (Z_to_bv 64 len) xa0 (Z_to_bv 64 (e_BUF E + ws_run bs fw i)) xa2 xa3
                         (Z_to_bv 64 (ws_run bs fw i)) (Z_to_bv 64 ((e_BUF E + ws_run bs fw i) / 8 + 2147450880)) (Z_to_bv 64 0) xt3'
                         (Z_to_bv 64 (e_BUF E)) m1)) ->
    (forall xt1' xa1' xs9' xs11' xt3' xt4', (len <= ws_run bs fw i)%Z ->
       evt asegs Q (A1ST E 0xba928 xra xt1' (Z_to_bv 64 len) xa0 xa1' xa2 xa3 xs9' (Z_to_bv 64 (e_BUF E)) xs11' xt3' xt4' m1)) ->
    evt asegs Q (A1ST E 0xba444 xra (Z_to_bv 64 (i + 2)) (Z_to_bv 64 len) xa0 xa1 xa2 xa3 (Z_to_bv 64 i) (Z_to_bv 64 (e_BUF E)) xs11 xt3 xt4 m1).
  Proof using OK.
    intros Q fw. induction fw as [|fw IH]; intros i xra xa0 xa1 xa2 xa3 xs11 xt3 xt4 m1 BUFRO TBL SHZB Hi Hfw HA HB; [exfalso; lia|].
    destruct OK as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, A1_STACK, A1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (B_range bs i BOK) as CR. set (c := B bs i) in *.
    pose proof (tbl_range c) as TR.
    pose proof (buf_read m1 (e_BUF E) bs i BUFRO ltac:(lia)) as RD1. fold c in RD1.
    pose proof (tbl_read m1 _ c TBL CR) as RD2.
    pose proof (SHZB (e_BUF E + i)%Z ltac:(lia)) as RD0.
    zstep. zstep. s1norm. zstep. zstep. zstep. rewrite shr3_div. zstep.
    zstep. rewrite sxb_z8. zstep. if_false.
    zstep. s1norm. zstep. zstep. s1norm. zstep. zstep.
    if_cases K; zify_cond K.
    -
      assert (TS : t_space c = false) by (unfold t_space; rewrite (proj2 (Z.eqb_eq _ _) K); reflexivity).
      rewrite ws_run_S in HA. fold c in HA. rewrite TS in HA.
      eapply evt_eq; [| eapply HA; [lia | exact TS]]. s1_st_eq.
    - assert (TS : t_space c = true) by (unfold t_space; rewrite (proj2 (Z.eqb_neq _ _) K); reflexivity).
      rewrite ws_run_S in HA, HB. fold c in HA, HB. rewrite TS in HA, HB.
      zstep. s1norm. zstep. zstep. zstep.
      if_cases K2; zify_cond K2.
      +
        assert (LT : (i + 1 <? len)%Z = true) by (apply Z.ltb_lt; lia).
        rewrite LT in HA, HB.
        replace (Z_to_bv 64 (i + 3)) with (Z_to_bv 64 (i + 1 + 2)) by (f_equal; lia).
        apply IH; try assumption; lia.
      +
        assert (LT : (i + 1 <? len)%Z = false) by (apply Z.ltb_ge; lia).
        rewrite LT in HB.
        zstep. apply HB. lia.
  Qed.
End WS.
