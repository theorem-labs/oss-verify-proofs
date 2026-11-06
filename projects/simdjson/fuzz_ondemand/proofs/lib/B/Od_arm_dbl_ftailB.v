(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjNumber SjNumSwar.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Od_arm_dbl_swar Od_arm_int.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Sj_akit Od_defsB Od_arm_dbl_defsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ od_load_hook | solve_load_image | solve_load_base ].

Lemma d_lxor_sign : forall x, (0 <= x < 18446744073709551616)%Z ->
  Z.lxor x 9223372036854775808 = ((x + 9223372036854775808) mod 18446744073709551616)%Z.
Proof. intros x H. apply (zb_lxor_sign x). exact H. Qed.
Ltac dsgn H :=
  repeat match type of H with
  | context [Z.lxor ?x 9223372036854775808] => rewrite (d_lxor_sign x) in H by first [ lia | apply Z.mod_pos_bound; lia ]
  end.
Ltac db2z H :=
  repeat match type of H with
  | context [Z.b2z (?a <? ?b)%Z] => destruct (Z.ltb_spec a b); cbn [Z.b2z] in H
  end.
Ltac dkill H := first [ lia | (progress (num_signed_lits_in H); lia) | (Z.div_mod_to_equations; lia) | (progress (dsgn H); first [ lia | Z.div_mod_to_equations; lia | db2z H; Z.div_mod_to_equations; lia ]) ].

Ltac dgoks := let G := fresh "UG" in if_cases G; zify_cond G; [| exfalso; dkill G]; try clear G.

Section ArmDblFracTailB.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Notation FST q0 v4 neg pc xra xt1 xt2 xa1 xa2 xa3 xa6 xs5 xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m :=
    (DBLST E pc xra (Z_to_bv 64 DBL_KT0) xt1 xt2 (Z_to_bv 64 (o_BUF E + q0)) xa1 xa2 xa3 v4 (Z_to_bv 64 neg) xa6 (Z_to_bv 64 DBL_KA7)
           (Z_to_bv 64 (oa_F E + 224)) (Z_to_bv 64 (o_act E)) xs5 xs6 xs10 (Z_to_bv 64 (oa_F E + 192)) xt3 xt4 xt5 xt6 xF xfc m).

  Lemma dbl_zskip_out : forall (Q : machine_state -> Prop) st (neg q0 p : Z) v4
      xra xt1 xt2 xa1 xa3 xa6 xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m1,
    frm0 xfc -> DBLINVs E st m1 -> dbl_E_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= p <= o_len E + 2)%Z ->
    evt bsegs Q (FST q0 v4 neg 0x9b120 xra xt1 xt2 xa1 (Z_to_bv 64 (o_BUF E + p)) xa3 xa6 (Z_to_bv 64 2) xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros until m1. intros FRM INV HE PS SG Hp.
    ddata xa1.

    dstep0. dstep0. dstep0. dstep0.
    eapply evt_eq; [| eapply (HE neg q0 p v4); [exact PS| exact SG| exact Hp| exact FRM| exact INV]]. od_st_eq.
  Qed.

  Lemma dbl_zskip_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 p z : Z) v4
      xra xt1 xt2 xa6 xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 ->
    dbl_E_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= p <= o_len E + 2)%Z -> (0 <= z)%Z -> B bs z = 48%Z -> (blen bs - z <= Z.of_nat f)%Z ->
    evt bsegs Q (FST q0 v4 neg 0x9b0c8 xra xt1 xt2 (Z_to_bv 64 (o_BUF E + z)) (Z_to_bv 64 (o_BUF E + p)) (Z_to_bv 64 (o_BUF E + z + 1)) xa6
                     (Z_to_bv 64 2) xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HE PS SG Hp Hz HZ Hf.
    - exfalso. assert (z < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (ZL : (z < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
      assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_B_range E BOK (z + 1)) as R1.
      pose proof (tokB_read m1 E (z + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (z + 1)) in *.
      clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

      ostep. ostep. dgok. ostep. ostep. ostep. ostep. if_false. ostep. ostep. odnorm. clear RB1. ostep. ostep. ostep.
      if_cases KB; zify_cond KB.
      + eapply evt_eq; [| eapply (IH Q st neg q0 p (z + 1)%Z v4);
                          [exact HLAST| exact HH| exact FRM| exact INV2| exact HE| exact PS| exact SG| exact Hp| lia| fold c; lia| lia]].
        od_st_eq.
      + clear KB IH.

        ostep.
        eapply evt_eq; [| eapply (dbl_zskip_out Q st neg q0 p v4); [exact FRM| exact INV2| exact HE| exact PS| exact SG| exact Hp]]. od_st_eq.
  Qed.

  Lemma dbl_frac_end : forall (Q : machine_state -> Prop) st (neg q0 p k : Z) v4 (w2 : word)
      xra xa1 xa3 xa6 xs5 xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 ->
    dbl_E_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= p <= o_len E + 2)%Z -> (2 <= k <= o_len E + 2)%Z ->
    evt bsegs Q (FST q0 v4 neg 0x998d4 xra (Z_to_bv 64 k) w2 xa1 (Z_to_bv 64 (o_BUF E + p)) xa3 xa6 xs5 xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV HE PS SG Hp Hk.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK (q0 + 2)) as R1.
    pose proof (tokB_read m1 E (q0 + 2) BUFRO ltac:(lia)) as RB1.
    set (c := B bs (q0 + 2)) in *.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    ostep. ostep. ostep. ostep. ostep. ostep.
    dgoks.

    ostep. ostep. ostep.
    dgoks.

    ostep. ostep. ostep. ostep.
    if_cases KT2; try clear KT2.
    { eapply evt_eq; [| eapply (HE neg q0 p v4); [exact PS| exact SG| exact Hp| exact FRM| exact INV2]]. od_st_eq. }

    ostep. ostep.
    if_cases K20; try clear K20.
    { eapply evt_eq; [| eapply (HE neg q0 p v4); [exact PS| exact SG| exact Hp| exact FRM| exact INV2]]. od_st_eq. }

    ostep. ostep. ostep. dgok. ostep. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. clear RB1. ostep. ostep.
    if_cases KZ; zify_cond KZ.
    -
      clear KZ.
      ostep. ostep. ostep. ostep. ostep. ostep.
      eapply evt_eq; [| eapply (dbl_zskip_out Q st neg q0 p v4); [exact FRM| exact INV2| exact HE| exact PS| exact SG| exact Hp]]. od_st_eq.
    -
      ostep. ostep. ostep. ostep. ostep. ostep. ostep.
      eapply evt_eq; [| eapply (dbl_zskip_loop (Z.to_nat (blen bs)) Q st neg q0 p (q0 + 2)%Z v4);
                        [exact HLAST| exact HH| exact FRM| exact INV2| exact HE| exact PS| exact SG| exact Hp| lia| fold c; lia| lia]].
      od_st_eq.
  Qed.

  Lemma dbl_frac_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 q k : Z) v4 (w2 : word)
      xra xa3 xa6 xs5 xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DBLINVs E st m1 ->
    dbl_E_k E Q st ->
    dbl_pos E st neg q0 -> dbl_sgn neg v4 -> (q0 <= q)%Z -> (1 <= k)%Z -> (48 <= B bs (q + k) <= 57)%Z ->
    (blen bs - (q + k) <= Z.of_nat f)%Z ->
    evt bsegs Q (FST q0 v4 neg 0x99878 xra (Z_to_bv 64 k) w2 (Z_to_bv 64 (o_BUF E + q)) (Z_to_bv 64 (o_BUF E + q + 1)) xa3 xa6
                     xs5 xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HE PS SG Hq Hk HDIG Hf.
    - exfalso. assert (q + k < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (q + k < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
      assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_B_range E BOK (q + k + 1)) as R1.
      pose proof (tokB_read m1 E (q + k + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (q + k + 1)) in *.
      ddata xa3. ddata xa6.
      clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

      ostep. ostep. ostep. ostep. ostep. ostep. if_false. ostep. odnorm. clear RB1. dstep. dstep. dstep. dstep. dstep. dstep. dstep. dstep.
      if_cases KB; zify_cond KB.
      + eapply evt_eq; [| eapply (IH Q st neg q0 q (k + 1)%Z v4 w2);
                          [exact HLAST| exact HH| exact FRM| exact INV2| exact HE| exact PS| exact SG| exact Hq| lia| | lia]];
          [ od_st_eq | replace (q + (k + 1))%Z with (q + k + 1)%Z by lia; fold c; apply (zxb_digit c R1 KB) ].
      + clear KB IH.

        ostep. ostep.
        eapply evt_eq; [| eapply (dbl_frac_end Q st neg q0 (q + k + 1)%Z (k + 1)%Z v4 w2);
                          [exact HLAST| exact HH| exact FRM| exact INV2| exact HE| exact PS| exact SG| lia| lia]].
        od_st_eq.
  Qed.

  Theorem dbl_frac_tail : forall (Q : machine_state -> Prop) st,
    HLASTP E -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_E_k E Q st -> dbl_R_k E Q st.
  Proof using OK.
    intros Q st HLAST HH HK HE. unfold dbl_R_k.
    intros neg q0 q k1 v4 w2 w6 xra xa2 xa3 xs5 xs6 xs10 xt3 xt4 xt5 xt6 xF xfc m1 PS SG Hq Hk1 Hqk FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). destruct INV as (j96 & j104 & j224 & j232 & j272 & INV). od_open_invc INV. od_env OK. unfold DBL_KT0, DBL_KA7 in *.
    pose proof HK as HK0. unfold od_plus_k, OD_PLUS in HK0.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK (q + k1)) as R1.
    pose proof (tokB_read m1 E (q + k1) BUFRO ltac:(lia)) as RB1.
    set (c := B bs (q + k1)) in *.
    clear F_M F_I F_S F_B IX8 IM8 SB8 CP8 F64 S32 USP16 FSH.

    ostep. ostep. ostep. ostep. ostep. if_true. ostep. odnorm. clear RB1. ostep. ostep. ostep. ostep.
    if_cases KD; zify_cond KD.
    -
      clear KD.
      ostep. ostep.
      if_cases K1; zify_cond K1.
      + eapply evt_eq; [| eapply (dbl_frac_end Q st neg q0 (q + k1)%Z k1 v4 w2);
                          [exact HLAST| exact HH| exact FRM| exact INV2| exact HE| exact PS| exact SG| lia| lia]].
        od_st_eq.
      + clear K1. ostep.
        eapply evt_eq; [| eapply (HK0 st)]; [od_st_eq| | exact FRM| od_close_inv].
        apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
    -
      assert (DG : (48 <= c <= 57)%Z) by (apply (zxb_digit c R1); lia).
      clear KD.
      ostep.
      eapply evt_eq; [| eapply (dbl_frac_loop (Z.to_nat (blen bs)) Q st neg q0 q k1 v4 w2);
                        [exact HLAST| exact HH| exact FRM| exact INV2| exact HE| exact PS| exact SG| exact Hq| exact Hk1| exact DG| lia]].
      od_st_eq.
  Qed.
End ArmDblFracTailB.
