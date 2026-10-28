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

Section PRIM.
  Variable E : s1env.
  Hypothesis OK : env_ok E.
  Notation len := (e_len E).
  Notation bs := (e_bs E).

  Lemma a1_prim_loop : forall (Q : machine_state -> Prop) (f : nat) (k : Z) xra xa0 xa2 xa3 xs11 xt3 (m1 : mem),
    bytes_at asegs m1 (e_BUF E) (padded_bytes bs) ->
    bytes_at asegs m1 (bv_unsigned (e_sp E) + -400) TABLE_BYTES ->
    shz m1 (e_BUF E) (len + 8) ->
    (1 <= k < len)%Z -> (len - k <= Z.of_nat f)%Z ->
    (forall xt1' xa0' xa1' xt3', evt asegs Q (A1ST E 0xba8a4 xra xt1' (Z_to_bv 64 (len + -1)) xa0' xa1' xa2 xa3 (Z_to_bv 64 (prim_run bs f k))
                                                  (Z_to_bv 64 (len + -2)) xs11 xt3' (Z_to_bv 64 (e_BUF E)) m1)) ->
    (forall xt1' xa0' xa1' xt3', prim_run bs f k = (len - 1)%Z ->
       evt asegs Q (A1ST E 0xba8bc xra xt1' (Z_to_bv 64 (len + -1)) xa0' xa1' xa2 xa3 (Z_to_bv 64 (len + -2))
                         (Z_to_bv 64 (len + -2)) xs11 xt3' (Z_to_bv 64 (e_BUF E)) m1)) ->
    evt asegs Q (A1ST E 0xba844 xra (Z_to_bv 64 (e_BUF E + k + 1)) (Z_to_bv 64 (len + -1)) xa0 (Z_to_bv 64 (e_BUF E + k + 1)) xa2 xa3
                      (Z_to_bv 64 (k - 1)) (Z_to_bv 64 (len + -2)) xs11 xt3 (Z_to_bv 64 (e_BUF E)) m1).
  Proof using OK.
    intros Q f. induction f as [|f IH]; intros k xra xa0 xa2 xa3 xs11 xt3 m1 BUFRO TBL SHZB Hk Hf HBOT HC; [exfalso; lia|].
    destruct OK as [BOK LEN GLO ROOM [TH0 TH1] [IX0 IX1] [BF0 BF1] CAPOK S_TI S_TB S_IB].
    unfold S1_LEN_MAX, A1_STACK, A1_GTOP in *.
    pose proof (bv_unsigned_in_range 64 (e_sp E)) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    rewrite prim_run_S in HBOT, HC.
    zstep.
    if_cases K; zify_cond K.
    -
      assert (LT : (k + 1 <? len)%Z = false) by (apply Z.ltb_ge; lia).
      rewrite LT in HC. cbn [andb] in HC.
      replace (Z_to_bv 64 (k - 1)) with (Z_to_bv 64 (len + -2)) by (f_equal; lia).
      apply HC. lia.
    - assert (LT : (k + 1 <? len)%Z = true) by (apply Z.ltb_lt; lia).
      rewrite LT in HBOT, HC. cbn [andb] in HBOT, HC.
      pose proof (B_range bs (k + 1) BOK) as CR. set (c := B bs (k + 1)) in *.
      pose proof (tbl_range c) as TR.
      pose proof (buf_read m1 (e_BUF E) bs (k + 1) BUFRO ltac:(lia)) as RD1. fold c in RD1.
      pose proof (tbl_read m1 _ c TBL CR) as RD2.
      pose proof (SHZB (e_BUF E + k + 1)%Z ltac:(lia)) as RD0.
      zstep. rewrite shr3_div. zstep. zstep. rewrite sxb_z8. zstep. if_false.
      zstep. s1norm. zstep. s1norm. zstep.
      replace (Z_to_bv 64 (k - 1 + 1)) with (Z_to_bv 64 k) by (f_equal; lia).
      if_cases K30; zify_cond K30.
      +
        assert (E30 : (c =? 30)%Z = true) by (apply Z.eqb_eq; lia).
        rewrite E30 in HBOT. rewrite andb_false_r in HBOT. apply HBOT.
      + assert (E30 : (c =? 30)%Z = false) by (apply Z.eqb_neq; lia).
        rewrite E30 in HBOT, HC. rewrite andb_true_r in HBOT, HC.
        zstep. zstep. s1norm. zstep. zstep. zstep. zstep.
        if_cases K3; zify_cond K3.
        *
          assert (TS : t_space_or_op c = false) by (unfold t_space_or_op; rewrite (proj2 (Z.eqb_eq _ _) K3); reflexivity).
          rewrite TS in HBOT, HC. cbn [negb] in HBOT, HC.
          replace (Z_to_bv 64 (e_BUF E + k + 2)) with (Z_to_bv 64 (e_BUF E + (k + 1) + 1)) by (f_equal; lia).
          replace (Z_to_bv 64 k) with (Z_to_bv 64 (k + 1 - 1)) by (f_equal; lia).
          apply IH; try assumption; try lia.
        * assert (TS : t_space_or_op c = true) by (unfold t_space_or_op; rewrite (proj2 (Z.eqb_neq _ _) K3); reflexivity).
          rewrite TS in HBOT. cbn [negb] in HBOT.
          zstep. apply HBOT.
  Qed.
End PRIM.
