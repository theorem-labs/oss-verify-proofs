(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjStage1.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section WS.
  Variable E : s1env.
  Hypothesis OK : env_ok E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma s1_ws_loop : forall (Q : machine_state -> Prop) (fw : nat) (i : Z) xra xa2 xa5 xa6 xs11 xt4 xt5 xt6 (m1 : mem),
    bytes_at psegs m1 (e_BUF E) (padded_bytes bs) ->
    bytes_at psegs m1 (bv_unsigned (e_sp E) + -400) TABLE_BYTES ->
    (0 <= i < len)%Z -> (len - i <= Z.of_nat fw)%Z ->
    (forall xs11', (ws_run bs fw i < len)%Z -> t_space (B bs (ws_run bs fw i)) = false ->
       evt psegs Q (S1ST E 0x298b8 xra (Z_to_bv 64 (ws_run bs fw i + 2)) xa2 xa5 xa6 (Z_to_bv 64 (ws_run bs fw i)) xs11'
                         (Z_to_bv 64 len) (Z_to_bv 64 (e_BUF E + ws_run bs fw i)) xt5 xt6 m1)) ->
    (forall xt2' xs10' xs11' xt3' xt4', (len <= ws_run bs fw i)%Z ->
       evt psegs Q (S1ST E 0x29bbc xra xt2' xa2 xa5 xa6 xs10' xs11' xt3' xt4' xt5 xt6 m1)) ->
    evt psegs Q (S1ST E 0x29888 xra (Z_to_bv 64 (i + 2)) xa2 xa5 xa6 (Z_to_bv 64 i) xs11 (Z_to_bv 64 len) xt4 xt5 xt6 m1).
  Proof using OK.
    intros Q fw. induction fw as [|fw IH]; intros i xra xa2 xa5 xa6 xs11 xt4 xt5 xt6 m1 BUFRO TBL Hi Hfw HA HB; [exfalso; lia|].
    destruct OK as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, S1_STACK, S1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (B_range bs i BOK) as CR. set (c := B bs i) in *.
    pose proof (tbl_range c) as TR.
    pose proof (buf_read m1 (e_BUF E) bs i BUFRO ltac:(lia)) as RD1. fold c in RD1.
    pose proof (tbl_read m1 _ c TBL CR) as RD2.
    zstep. zstep. s1norm. zstep. zstep. s1norm. zstep. zstep. s1norm. zstep. zstep.
    if_cases K; zify_cond K.
    -
      assert (TS : t_space c = false) by (unfold t_space; rewrite (proj2 (Z.eqb_eq _ _) K); reflexivity).
      rewrite ws_run_S in HA. fold c in HA. rewrite TS in HA.
      apply HA; [lia | exact TS].
    - assert (TS : t_space c = true) by (unfold t_space; rewrite (proj2 (Z.eqb_neq _ _) K); reflexivity).
      rewrite ws_run_S in HA, HB. fold c in HA, HB. rewrite TS in HA, HB.
      zstep. s1norm. zstep. zstep.
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
