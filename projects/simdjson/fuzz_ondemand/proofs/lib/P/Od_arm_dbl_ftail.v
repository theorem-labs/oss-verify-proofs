(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_arm_dbl_defs Od_arm_int.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section ArmDblFracTail.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation RINV st neg w56 w64 v128 m1 :=
    (DBLINVc E st [C8 (Z_to_bv 64 DBL_K0); C8 (Z_to_bv 64 DBL_K8); C8 (Z_to_bv 64 (o_IDX E + 4 * o_pos st))]
                  [C8 w56; C8 w64; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (o_act E)); C8 (Z_to_bv 64 neg)] [C8 v128; C8 (Z_to_bv 64 0x640001)] m1).

  Lemma dbl_zskip_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 p z : Z) w56 w64 v128
      xt0 xt1 xt2 xa0 xa3 xa5 xa6 xa7 xt4 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    RINV st neg w56 w64 v128 m1 -> od_plus_k E Q st -> dbl_E_k E Q st ->
    (0 <= neg <= 1)%Z -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (q0 <= p <= o_len E + 2)%Z ->
    (0 <= z <= o_len E + 4)%Z -> (blen bs + 5 - z <= Z.of_nat f)%Z ->
    evt psegs Q (ODST E 0x28460 xt0 xt1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q0)) (Z_to_bv 64 (o_BUF E + z)) xa3 (Z_to_bv 64 48) xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (B bs p)) xt4 (Z_to_bv 64 (o_BUF E + p)) xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HK HE NGR Hq0 Hp Hz Hf; [exfalso; lia|].
    pose proof HH as (HP & HD & HEr & HAL & HB).
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K0, DBL_K8 in *.
    pose proof (od_B_range E BOK z) as R1.
    pose proof (tokB_read m1 E z BUFRO ltac:(lia)) as RB1.
    set (c := B bs z) in *.
    zstep. odnorm. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - assert (ZL : (z < blen bs)%Z) by (apply B_nonzero_lt_len; fold c; lia).
      eapply evt_eq; [| eapply (IH Q st neg q0 p (z + 1)%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact NGR| exact Hq0| exact Hp| lia| lia]].
      od_st_eq.
    - do 11 zstep.
      forget_56 FR56. forget_C8 FR128.
      eapply evt_eq; [| eapply (HE neg q0 p); [exact NGR | exact Hq0 | exact Hp | exact FRM | unfold DBL_K0, DBL_K8; dbl_close_inv]].
      od_st_eq.
  Qed.

  Lemma dbl_frac_end : forall (Q : machine_state -> Prop) st (neg q0 p : Z) w56 w64 v128
      xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt4 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    RINV st neg w56 w64 v128 m1 -> od_plus_k E Q st -> dbl_E_k E Q st ->
    (0 <= neg <= 1)%Z -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (q0 <= p <= o_len E + 2)%Z ->
    evt psegs Q (ODST E 0x28208 xt0 xt1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (B bs p)) xt4 (Z_to_bv 64 (o_BUF E + p)) xF xfc m1).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV HK HE NGR Hq0 Hp.
    pose proof HH as (HP & HD & HEr & HAL & HB).
    dbl_open_inv INV. od_env OK. unfold DBL_K0, DBL_K8 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    assert (KE : forall xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt4,
      evt psegs Q (ODST E 0x28224 xt0 xt1 xt2 xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (B bs p)) xt4 (Z_to_bv 64 (o_BUF E + p)) xF xfc m1)).
    { intros. forget_56 FR56. forget_C8 FR128.
      eapply (HE neg q0 p); [exact NGR | exact Hq0 | exact Hp | exact FRM | unfold DBL_K0, DBL_K8; dbl_close_inv]. }
    zstep. zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K; clear K; [eapply evt_eq; [| eapply KE]; od_st_eq|].
    pose proof (rw_cells_C8_read1_g _ _ _ _ _ FR128) as RDS.
    step. zstep.
    if_cases K; zify_cond K; clear K; [| eapply evt_eq; [| eapply KE]; od_st_eq].
    clear RDS.
    do 7 zstep.
    eapply evt_eq; [| eapply (dbl_zskip_loop (Z.to_nat (blen bs + 5)) Q st neg q0 p (q0 + 2)%Z); [exact HLAST| exact HH| exact FRM| | exact HK| exact HE| exact NGR| exact Hq0| exact Hp| lia| lia]].
    - od_st_eq.
    - unfold DBL_K0, DBL_K8. dbl_close_inv.
  Qed.

  Lemma dbl_frac_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 q k : Z) w56 w64 v128
      xt0 xt2' xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    RINV st neg w56 w64 v128 m1 -> od_plus_k E Q st -> dbl_E_k E Q st ->
    (0 <= neg <= 1)%Z -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (q0 <= q)%Z -> (1 <= k)%Z -> (48 <= B bs (q + k) <= 57)%Z ->
    (blen bs - (q + k) <= Z.of_nat f)%Z -> xt2' = Z_to_bv 64 (o_BUF E + q) ->
    evt psegs Q (ODST E 0x281d8 xt0 (Z_to_bv 64 k) xt2' xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HK HE NGR Hq0 Hq Hk HDIG Hf ->.
    - exfalso. assert (q + k < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (q + k < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      pose proof HH as (HP & HD & HEr & HAL & HB).
      assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K0, DBL_K8 in *.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_B_range E BOK (q + k + 1)) as R1.
      pose proof (tokB_read m1 E (q + k + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (q + k + 1)) in *.
      zstep. zstep. odnorm. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      if_cases K; zify_cond K.
      + eapply evt_eq; [| eapply (IH Q st neg q0 q (k + 1)%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact NGR| exact Hq0| exact Hq| lia| | | reflexivity]].
        * od_st_eq.
        * replace (q + (k + 1))%Z with (q + k + 1)%Z by lia. fold c. apply (zxb_digit c R1 K).
        * lia.
      + zstep. zstep.
        eapply evt_eq; [| eapply (dbl_frac_end Q st neg q0 (q + k + 1)%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact NGR| exact Hq0| lia]].
        od_st_eq.
  Qed.

  Theorem dbl_frac_tail : forall (Q : machine_state -> Prop) st,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_E_k E Q st -> dbl_R_k E Q st.
  Proof using OK.
    intros Q st HLAST HH HK HE. unfold dbl_R_k.
    intros neg q0 q k1 w56 w64 v128 xt0 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1 NGR Hq0 Hq Hk1 Hqk FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB).
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K0, DBL_K8 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK (q + k1)) as R1.
    pose proof (tokB_read m1 E (q + k1) BUFRO ltac:(lia)) as RB1.
    set (c := B bs (q + k1)) in *.
    zstep. zstep. odnorm. zstep. zstep. zstep. zstep.
    if_cases K; zify_cond K.
    -
      zstep. if_cases K2; zify_cond K2.
      + apply (HK st); [| exact FRM| dbl_close_od].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
      + eapply evt_eq; [| eapply (dbl_frac_end Q st neg q0 (q + k1)%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact NGR| exact Hq0| lia]].
        od_st_eq.
    - eapply evt_eq; [| eapply (dbl_frac_loop (Z.to_nat (blen bs)) Q st neg q0 q k1); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact NGR| exact Hq0| exact Hq| exact Hk1| | lia| reflexivity]].
      + od_st_eq.
      + fold c. apply (zxb_digit c R1). lia.
  Qed.
End ArmDblFracTail.
