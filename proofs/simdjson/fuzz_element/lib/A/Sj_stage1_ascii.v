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

Section ASCII.
  Variable E : s1env.
  Hypothesis OK : env_ok E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma a1_ascii_loop : forall (Q : machine_state -> Prop) (fa : nat) (i : Z) xt1 xa0 xa1 xa2 xa3 xs10 xs11 xt3 (m1 : mem),
    bytes_at asegs m1 (e_BUF E) (padded_bytes bs) ->
    bytes_at asegs m1 (bv_unsigned (e_sp E) + -400) TABLE_BYTES ->
    shz m1 (e_BUF E) (len + 8) ->
    (0 <= i < len)%Z -> (len - i <= Z.of_nat fa)%Z ->
    (forall xa1', (ascii_run bs fa i < len)%Z -> t_ascii_stop (B bs (ascii_run bs fa i)) = true ->
       evt asegs Q (A1ST E 0xba534 (Z_to_bv 64 len) xt1 (Z_to_bv 64 len) (Z_to_bv 64 (e_BUF E + ascii_run bs fa i)) xa1' xa2 xa3
                         (Z_to_bv 64 (ascii_run bs fa i)) xs10 (Z_to_bv 64 ((e_BUF E + ascii_run bs fa i) / 8 + 2147450880)) (Z_to_bv 64 0)
                         (Z_to_bv 64 (e_BUF E)) m1)) ->
    (forall xa0' xa1' xs11' xt3', (ascii_run bs fa i = len)%Z ->
       evt asegs Q (A1ST E 0xba898 (Z_to_bv 64 len) xt1 (Z_to_bv 64 len) xa0' xa1' xa2 xa3 (Z_to_bv 64 len) xs10 xs11' xt3'
                         (Z_to_bv 64 (e_BUF E)) m1)) ->
    evt asegs Q (A1ST E 0xba4ec (Z_to_bv 64 len) xt1 (Z_to_bv 64 len) xa0 xa1 xa2 xa3 (Z_to_bv 64 i) xs10 xs11 xt3 (Z_to_bv 64 (e_BUF E)) m1).
  Proof using OK.
    intros Q fa. induction fa as [|fa IH]; intros i xt1 xa0 xa1 xa2 xa3 xs10 xs11 xt3 m1 BUFRO TBL SHZB Hi Hfa HA HB; [exfalso; lia|].
    destruct OK as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, A1_STACK, A1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (B_range bs i BOK) as CR. set (c := B bs i) in *.
    pose proof (tbl_range c) as TR.
    pose proof (buf_read m1 (e_BUF E) bs i BUFRO ltac:(lia)) as RD1. fold c in RD1.
    pose proof (tbl_read m1 _ c TBL CR) as RD2.
    pose proof (SHZB (e_BUF E + i)%Z ltac:(lia)) as RD0.
    rewrite ascii_run_S in HA, HB. fold c in HA, HB.
    zstep. zstep. s1norm. zstep. zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_false.
    zstep. s1norm. zstep. zstep. s1norm. zstep. zstep.
    if_cases K; zify_cond K.
    -
      assert (TS : t_ascii_stop c = true) by (unfold t_ascii_stop; rewrite (proj2 (Z.eqb_neq _ _) K); reflexivity).
      rewrite TS in HA. eapply evt_eq; [| eapply HA; [lia | exact TS]]. s1_st_eq.
    - assert (TS : t_ascii_stop c = false) by (unfold t_ascii_stop; rewrite (proj2 (Z.eqb_eq _ _) K); reflexivity).
      rewrite TS in HA, HB.
      zstep. s1norm. zstep.
      if_cases K2; zify_cond K2.
      + assert (LT : (i + 1 <? len)%Z = true) by (apply Z.ltb_lt; lia).
        rewrite LT in HA, HB.
        apply IH; try assumption; lia.
      + assert (LT : (i + 1 <? len)%Z = false) by (apply Z.ltb_ge; lia).
        rewrite LT in HB.
        zstep.
        replace (Z_to_bv 64 (i + 1)) with (Z_to_bv 64 len) by (f_equal; lia).
        apply HB. lia.
  Qed.
End ASCII.
