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

Definition DBLINVi (E : oaenv) (st : ost) (m1 : mem) : Prop :=
  exists j96 j104 j224 j232 j272 j320,
    ODINVc E (oa_F E + 192) 0 2 1 (o_IDX E) 1 1 (o_IDX E + 4 * o_pos st)
           (CB 8 j96) (CB 8 j104) (CB 8 j224) (CB 8 j232) (CB 8 j272)
           (C8 (wz (oa_F E + 200))) (CB 8 j320) (C8 (wz 2)) st m1.

Section ArmDblIntB.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Lemma dbl_int_tail : forall (Q : machine_state -> Prop) st (neg q0 q : Z) v4 (w2 w6 wa2 : word)
      xra xt0 xa3 xa7 xs5 xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m1,
    od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVi E st m1 ->
    dbl_F_k E Q st -> dbl_E_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= q <= o_len E + 2)%Z ->
    evt bsegs Q (DBLST E 0x981cc xra xt0 (Z_to_bv 64 (B bs q)) w2 (Z_to_bv 64 (o_BUF E + q0)) (Z_to_bv 64 (o_BUF E + q)) wa2 xa3 v4 (Z_to_bv 64 neg) w6 xa7
                       (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192)) xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros until m1; intros HH FRM INV HF HE PS SG Hq.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    destruct INV as (j96 & j104 & j224 & j232 & j272 & j320 & INV). od_open_invc INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK q) as R0.
    set (c := B bs q) in *.
    ddata w2. ddata w6. ddata wa2.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    dstep. dstep. dstep. dsstep. dstep.
    od_cur_mem ltac:(fun mm => assert (INV2 : DBLINVs E st mm) by (unfold DBLINVs; do 5 eexists; od_close_invc)).
    if_cases KP; zify_cond KP.
    -
      eapply evt_eq; [| eapply (HF neg q0 q v4); [exact PS| exact SG| exact Hq| fold c; lia| exact FRM| exact INV2]]. unfold DBL_KT0, DBL_KA7. od_st_eq.
    -
      clear KP.
      dstep. dstep. dstep. dstep. dstep. dstep. dstep.
      eapply evt_eq; [| eapply (HE neg q0 q v4); [exact PS| exact SG| exact Hq| exact FRM| exact INV2]]. unfold DBL_KT0, DBL_KA7. od_st_eq.
  Qed.

  Lemma dbl_int_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 j : Z) v4 (w3 w6 w7 : word)
      xra xt1 xt2 xs5 xs6 xs10 xt4 xt5 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVi E st m1 ->
    od_plus_k E Q st -> dbl_F_k E Q st -> dbl_E_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (1 <= j)%Z -> (48 <= B bs (q0 + j) <= 57)%Z ->
    (blen bs - (q0 + j) <= Z.of_nat f)%Z ->
    evt bsegs Q (DBLST E 0x98144 xra (Z_to_bv 64 (o_BUF E + q0 + 1)) xt1 xt2 (Z_to_bv 64 (o_BUF E + q0)) (Z_to_bv 64 (o_BUF E + q0 + j)) (Z_to_bv 64 j) w3
                       v4 (Z_to_bv 64 neg) w6 w7 (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192))
                       (Z_to_bv 64 2) xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HK HF HE PS SG Hj HDIG Hf.
    - exfalso. assert (q0 + j < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (q0 + j < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
      assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & j320 & INV). od_open_invc INV. od_env OK.
      pose proof HK as HK0. unfold od_plus_k, OD_PLUS in HK0.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_B_range E BOK (q0 + j + 1)) as R1.
      pose proof (tokB_read m1 E (q0 + j + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (q0 + j + 1)) in *.
      ddata w3. ddata w6. ddata w7.
      clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

      dstep. dstep. dgok. dstep. dstep. dstep. dstep. dstep. dstep. if_false. dstep. dstep. odnorm. clear RB1. dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep.
      if_cases KB; zify_cond KB.
      +
        eapply evt_eq; [| eapply (IH Q st neg q0 (j + 1)%Z v4);
                          [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HF| exact HE| exact PS| exact SG| lia| | lia]];
          [ od_st_eq | replace (q0 + (j + 1))%Z with (q0 + j + 1)%Z by lia; fold c; apply (zxb_digit c R1 KB) ].
      +
        clear KB IH.
        dstep. dstep. dstep.
        if_cases KN; zify_cond KN; [| exfalso; lia]. clear KN.
        dstep. dstep.
        if_cases KZ; try clear KZ.
        * eapply evt_eq; [| eapply (dbl_int_tail Q st neg q0 (q0 + j + 1)%Z v4); [exact HH| exact FRM| exact INV2| exact HF| exact HE| exact PS| exact SG| lia]].
          fold c. od_st_eq.
        *
          dstep. dstep. dgok. dstep. dstep.
          if_cases K1; zify_cond K1; [exfalso; lia|]. clear K1.
          dstep.
          eapply evt_eq; [| eapply (HK0 st)]; [od_st_eq| | exact FRM| od_close_inv].
          apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
  Qed.

  Local Ltac b2z_split H1 H2 :=
    first [ match goal with |- context [Z.b2z (?x <? ?y)%Z] => destruct (Z.ltb_spec x y) as [H1|H2] end
          | match goal with |- context [Z.b2z (?x =? ?y)%Z] => destruct (Z.eqb_spec x y) as [H1|H2] end ]; cbn [Z.b2z].

  Lemma dbl_int_dig : forall (Q : machine_state -> Prop) st (neg q0 : Z) v4
      xra xt0 xt1 xt2 xa1 xa2 xa3 xa6 xa7 xs5 xs6 xs10 xt5 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVi E st m1 ->
    od_plus_k E Q st -> dbl_F_k E Q st -> dbl_E_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= blen bs)%Z ->
    evt bsegs Q (DBLST E 0x980d8 xra xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E + q0)) xa1 xa2 xa3 v4 (Z_to_bv 64 neg) xa6 xa7
                       (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192))
                       (Z_to_bv 64 2) (Z_to_bv 64 2) xt5 xt6 xF xfc m1).
  Proof using OK.
    intros until m1; intros HLAST HH FRM INV HK HF HE PS SG HQ.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & j320 & INV). od_open_invc INV. od_env OK.
    pose proof HK as HK0. unfold od_plus_k, OD_PLUS in HK0.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK q0) as R0. pose proof (od_B_range E BOK (q0 + 1)) as R1.
    pose proof (tokB_read m1 E q0 BUFRO ltac:(lia)) as RB0.
    set (d0 := B bs q0) in *. set (d1 := B bs (q0 + 1)) in *.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    dstep. dstep. dstep. dstep. if_true. dstep. odnorm. dstep. dstep. dstep.
    b2z_split DG ND.
    -
      assert (D0 : (48 <= d0 <= 57)%Z) by (apply (zxb_digit d0 R0); lia). clear DG.
      assert (QL : (q0 < blen bs)%Z) by (apply B_nonzero_lt_len; fold d0; lia).
      clear RB0. pose proof (tokB_read m1 E (q0 + 1) BUFRO ltac:(lia)) as RB1. fold d1 in RB1.
      dstep. dstep. dgok. dstep. dstep. dstep. dstep. dstep. if_true. dstep. odnorm. clear RB1. dstep. dstep. dstep. dstep. dstep. dstep. dstep.
      if_cases KB; zify_cond KB.
      +
        clear KB.
        dstep. if_true. dstep. dstep.
        if_cases KZ; try clear KZ.
        * eapply evt_eq; [| eapply (dbl_int_tail Q st neg q0 (q0 + 1)%Z v4); [exact HH| exact FRM| exact INV2| exact HF| exact HE| exact PS| exact SG| lia]].
          fold d1. od_st_eq.
        *
          dstep. dstep. dgok. dstep. dstep. if_true.
          eapply evt_eq; [| eapply (dbl_int_tail Q st neg q0 (q0 + 1)%Z v4); [exact HH| exact FRM| exact INV2| exact HF| exact HE| exact PS| exact SG| lia]].
          fold d1. od_st_eq.
      +
        assert (D1 : (48 <= d1 <= 57)%Z) by (apply (zxb_digit d1 R1); lia). clear KB.
        dstep.
        eapply evt_eq; [| eapply (dbl_int_loop (Z.to_nat (blen bs)) Q st neg q0 1%Z v4);
                          [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HF| exact HE| exact PS| exact SG| lia| exact D1| lia]].
        od_st_eq.
    -
      dstep. dstep. dgok. dstep. dstep. dstep. dstep. dstep. if_true. dstep. odnorm. clear RB0. dstep. dstep. dstep. dstep. dstep. dstep. dstep.
      if_cases KB; zify_cond KB; [| exfalso; lia]. clear KB ND.
      dstep. if_false. dstep.
      eapply evt_eq; [| eapply (HK0 st)]; [od_st_eq| | exact FRM| od_close_inv].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
  Qed.

  Theorem od_dbl_int : forall (Q : machine_state -> Prop) st,
    HLASTP E -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_F_k E Q st -> dbl_E_k E Q st -> arm_k E Q 0x97818 st.
  Proof using OK.
    intros Q st HLAST HH HK HF HE. unfold arm_k.
    intros xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs10 xt3 xt5 xt6 xF xfc m1 FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB).
    assert (HD2 : o_depth st = 2%Z) by lia.
    od_open_inv INV. od_env OK. rewrite HD2 in ITER.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0.
    set (c0 := B bs off) in *.

    zstep. if_true.
    ostep. dgtrap. ostep. ual. ostep. dgtrap. ostep. ostep. ostep. ostep. ostep. ostep. if_true. ostep. ostep. if_true.

    ostep. ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. ostep. dgok. ostep. dgok. ostep. ostep. dgok. ostep. ostep. ostep. ostep. if_true.
    ostep. dgok. ostep. ual. ostep. dgok. ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. clear RD1. ostep. ostep. dgok.
    ostep. ostep. ostep. unz. ostep. dgok. dsstep. ostep. dgok. dsstep.
    od_cur_mem ltac:(fun mm => assert (INVI : DBLINVi E st mm) by (unfold DBLINVi; do 6 eexists; od_close_invc);
                               pose proof (tokB_read mm E off ltac:(eassumption) ltac:(lia)) as RB0).
    fold c0 in RB0.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    ostep. ostep. ostep. ostep. if_true. ostep. odnorm. clear RB0. ostep. ostep.
    b2z_split SGN NS.
    -
      assert (C45 : c0 = 45%Z) by (clear -SGN R0; Z.div_mod_to_equations; lia).
      assert (QL : (off < blen bs)%Z) by (apply B_nonzero_lt_len; fold c0; lia).
      ostep. ostep. dgok. ostep.
      eapply evt_eq; [| eapply (dbl_int_dig Q st 1%Z (off + 1)%Z); [exact HLAST| exact HH| exact FRM| exact INVI| exact HK| exact HF| exact HE| split; [lia| reflexivity]| | lia]];
        [od_st_eq| intros H; exfalso; lia].
    - assert (V4 : bv_unsigned (Z_to_bv 64 (c0 + -45)) <> 0%Z).
      { rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. clear -NS. lia. }
      ostep. ostep. dgok. ostep.
      eapply evt_eq; [| eapply (dbl_int_dig Q st 0%Z off); [exact HLAST| exact HH| exact FRM| exact INVI| exact HK| exact HF| exact HE| split; [lia| lia]| intros _; exact V4| lia]].
      od_st_eq.
  Qed.
End ArmDblIntB.
