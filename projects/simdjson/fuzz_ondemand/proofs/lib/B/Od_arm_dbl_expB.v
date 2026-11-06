(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Od_arm_int.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit Od_defsB Od_arm_dbl_defsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_image | solve_load_base ].

Section ArmDblExpB.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Notation XST q0 v4 neg pc xra xt1 xt2 xa1 xa2 xa3 xa6 xs3 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m :=
    (DBLST E pc xra (Z_to_bv 64 DBL_KT0) xt1 xt2 (Z_to_bv 64 (o_BUF E + q0)) xa1 xa2 xa3 v4 (Z_to_bv 64 neg) xa6 (Z_to_bv 64 DBL_KA7)
           xs3 (Z_to_bv 64 (o_act E)) (Z_to_bv 64 2) xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m).

  Lemma dbl_exp_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 e0 j : Z) v4
      xra xt1 xt2 xa6 xs3 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 ->
    od_plus_k E Q st -> dbl_T_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= e0)%Z -> (0 <= j)%Z -> (48 <= B bs (e0 + j) <= 57)%Z ->
    (blen bs - (e0 + j) <= Z.of_nat f)%Z ->
    evt bsegs Q (XST q0 v4 neg 0x999c0 xra xt1 xt2 (Z_to_bv 64 (o_BUF E + e0)) (Z_to_bv 64 (o_BUF E + e0 + j)) (Z_to_bv 64 (o_BUF E + e0 + j + 1)) xa6
                     xs3 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HK HT PS SG He0 Hj HDIG Hf.
    - exfalso. assert (e0 + j < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (e0 + j < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
      assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
      pose proof HK as HK0. unfold od_plus_k, OD_PLUS in HK0.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_B_range E BOK (e0 + j + 1)) as R1.
      pose proof (tokB_read m1 E (e0 + j + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (e0 + j + 1)) in *.
      ddata xt4. ddata xt5. ddata xt1. ddata xa6. ddata xt3.
      clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

      dstep. dgok. dstep. dstep. dstep. dstep. if_false. dstep. dstep. odnorm. clear RB1. dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep.
      if_cases KB; zify_cond KB.
      +
        eapply evt_eq; [| eapply (IH Q st neg q0 e0 (j + 1)%Z v4);
                          [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact PS| exact SG| exact He0| lia| | lia]];
          [ od_st_eq | replace (e0 + (j + 1))%Z with (e0 + j + 1)%Z by lia; fold c; apply (zxb_digit c R1 KB) ].
      +
        clear KB IH.
        dstep. dstep. dstep. dstep.
        if_cases KN; zify_cond KN; [exfalso; lia|]. clear KN.

        dstep. dstep. dstep.
        if_cases K19; try clear K19.
        *
          eapply evt_eq; [| eapply (HK0 st)]; [od_st_eq| | exact FRM| od_close_inv].
          apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
        *
          dstep. dstep.
          if_cases KS; try clear KS.
          -- dstep. dstep.
             eapply evt_eq; [| eapply (HT neg q0 (e0 + j + 1)%Z v4); [exact PS| exact SG| lia| exact FRM| exact INV2]]. od_st_eq.
          -- dstep. dstep. dstep.
             eapply evt_eq; [| eapply (HT neg q0 (e0 + j + 1)%Z v4); [exact PS| exact SG| lia| exact FRM| exact INV2]]. od_st_eq.
  Qed.

  Lemma dbl_exp_dig : forall (Q : machine_state -> Prop) st (neg q0 p sg : Z) v4
      xra xt1 xt2 xa6 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 ->
    od_plus_k E Q st -> dbl_T_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= p)%Z -> (0 <= sg <= 1)%Z -> (p + sg + 1 <= blen bs)%Z ->
    evt bsegs Q (XST q0 v4 neg 0x99984 xra xt1 xt2 (Z_to_bv 64 (o_BUF E + p + 1 + sg)) (Z_to_bv 64 (o_BUF E + p)) (Z_to_bv 64 sg) xa6
                     (Z_to_bv 64 (oa_F E + 224)) xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros until m1; intros HLAST HH FRM INV HK HT PS SG Hp Hsg HL.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
    pose proof HK as HK0. unfold od_plus_k, OD_PLUS in HK0.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK (p + 1 + sg)) as R2.
    pose proof (tokB_read m1 E (p + 1 + sg) BUFRO ltac:(lia)) as RB2.
    set (c2 := B bs (p + 1 + sg)) in *.
    ddata xt1. ddata xa6. ddata xt3.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    dstep. dstep. dstep. dstep. if_true. dstep. odnorm. clear RB2. dstep. dstep. dstep. dstep.
    if_cases KD; zify_cond KD.
    -
      assert (DG : (48 <= c2 <= 57)%Z) by (apply (zxb_digit c2 R2); lia).
      clear KD.
      dstep. dstep. dstep. dstep.
      eapply evt_eq; [| eapply (dbl_exp_loop (Z.to_nat (blen bs)) Q st neg q0 (p + 1 + sg)%Z 0%Z v4);
                        [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact PS| exact SG| lia| lia| | lia]];
        [ od_st_eq | replace (p + 1 + sg + 0)%Z with (p + 1 + sg)%Z by lia; exact DG ].
    -
      clear KD.
      dstep. dstep. dstep. dstep. dstep. dstep. if_true.
      eapply evt_eq; [| eapply (HK0 st)]; [od_st_eq| | exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
  Qed.

  Lemma dbl_exp_none : forall (Q : machine_state -> Prop) st (neg q0 p : Z) v4
      xra xt1 xt2 xa1 xa3 xa6 xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 -> dbl_T_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= p <= o_len E + 2)%Z ->
    evt bsegs Q (XST q0 v4 neg 0x99940 xra xt1 xt2 xa1 (Z_to_bv 64 (o_BUF E + p)) xa3 xa6
                     (Z_to_bv 64 (oa_F E + 224)) xs6 xs10 (Z_to_bv 64 (oa_F E + 192)) xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros until m1; intros HLAST HH FRM INV HT PS SG Hp.
    assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
    ddata xt1. ddata xa6. ddata xt3.

    dstep. dstep. dstep.
    eapply evt_eq; [| eapply (HT neg q0 p v4); [exact PS| exact SG| lia| exact FRM| exact INV2]]. od_st_eq.
  Qed.

  Lemma dbl_exp_e : forall (Q : machine_state -> Prop) st (neg q0 p : Z) v4
      xra xt1 xt2 xa1 xa3 xa6 xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 ->
    od_plus_k E Q st -> dbl_T_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= p)%Z -> (p < blen bs)%Z ->
    evt bsegs Q (XST q0 v4 neg 0x99944 xra xt1 xt2 xa1 (Z_to_bv 64 (o_BUF E + p)) xa3 xa6
                     (Z_to_bv 64 (oa_F E + 224)) xs6 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros until m1; intros HLAST HH FRM INV HK HT PS SG Hp QL.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    ddata xt1. ddata xa6. ddata xt3.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.
    pose proof (od_B_range E BOK (p + 1)) as R1.
    pose proof (tokB_read m1 E (p + 1) BUFRO ltac:(lia)) as RB1.
    set (c1 := B bs (p + 1)) in *.

    dstep. dstep. dgok. dstep. dstep. dstep. dstep. if_true. dstep. odnorm. clear RB1. dstep. dstep. dstep.
    first [ match goal with |- context [Z.b2z (?x <? ?y)%Z] => destruct (Z.ltb_spec x y) as [SGN|NS] end
          | match goal with |- context [Z.b2z (?x =? ?y)%Z] => destruct (Z.eqb_spec x y) as [SGN|NS] end ]; cbn [Z.b2z].
    -
      assert (Q1 : (p + 1 < blen bs)%Z) by (apply B_nonzero_lt_len; fold c1; apply (sign_nonzero c1 R1); lia). clear SGN.
      dstep. dstep. dgok. dstep.
      eapply evt_eq; [| eapply (dbl_exp_dig Q st neg q0 p 1%Z v4);
                        [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact PS| exact SG| lia| lia| lia]].
      od_st_eq.
    - clear NS.
      dstep. dstep. dgok. dstep.
      eapply evt_eq; [| eapply (dbl_exp_dig Q st neg q0 p 0%Z v4);
                        [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact PS| exact SG| lia| lia| lia]].
      od_st_eq.
  Qed.

  Theorem dbl_exp : forall (Q : machine_state -> Prop) st,
    HLASTP E -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_T_k E Q st -> dbl_E_k E Q st.
  Proof using OK.
    intros Q st HLAST HH HK HT. unfold dbl_E_k.
    intros neg q0 p v4 xra xt1 xt2 xa1 xa3 xa6 xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m1 PS SG Hp FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK p) as R0.
    pose proof (tokB_read m1 E p BUFRO ltac:(lia)) as RB0.
    set (c := B bs p) in *.
    ddata xt1. ddata xa6. ddata xt3.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    dstep. dstep. dstep. dstep. if_true. dstep. odnorm. clear RB0. dstep. dstep. dstep.
    if_cases KE; zify_cond KE.
    -
      assert (QL : (p < blen bs)%Z) by (apply B_nonzero_lt_len; fold c; apply (ori32_e_nonzero c R0 KE)). clear KE.
      eapply evt_eq; [| eapply (dbl_exp_e Q st neg q0 p v4); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact PS| exact SG| lia| exact QL]].
      od_st_eq.
    - clear KE.
      eapply evt_eq; [| eapply (dbl_exp_none Q st neg q0 p v4); [exact HLAST| exact HH| exact FRM| exact INV2| exact HT| exact PS| exact SG| exact Hp]].
      od_st_eq.
  Qed.
End ArmDblExpB.
