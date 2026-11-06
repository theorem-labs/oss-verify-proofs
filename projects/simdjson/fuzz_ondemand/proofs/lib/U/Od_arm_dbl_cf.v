(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjNumber SjNumSwar.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Sj_num_walk Od_arm_int.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Sj_num_iface Sj_num_kitu Od_fromch Od_tables Od_pow5u Od_arm_dbl_defs Od_arm_dbl_exit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma upow5_idx : forall x, (0 <= x < 18446744073709551616)%Z -> (x < 309 \/ 18446744073709551274 <= x)%Z ->
  exists i, (0 <= i <= 650)%Z /\ bv_swrap 32 ((2 * x) mod 18446744073709551616 + 684) = (2 * i)%Z.
Proof.
  intros x Hx [L|G].
  - exists (x + 342)%Z. split; [lia|]. rewrite Z.mod_small by lia. rewrite swrap32_small by lia. lia.
  - exists (x - 18446744073709551616 + 342)%Z. split; [lia|].
    rewrite bv_swrap32. unfold swrap32. Z.div_mod_to_equations. lia.
Qed.
Lemma lor_2i_1 : forall i, (0 <= i)%Z -> Z.lor (2 * i) 1 = (2 * i + 1)%Z.
Proof.
  intros i Hi. apply (lor_disj (2 * i) 1 1); [lia | lia | | change (2 ^ 1)%Z with 2%Z; lia].
  change (2 ^ 1)%Z with 2%Z. rewrite Z.mul_comm. apply Z.mod_mul. lia.
Qed.
Lemma lor_16i_8 : forall i, (0 <= i)%Z -> Z.lor (8 * (2 * i)) 8 = (16 * i + 8)%Z.
Proof.
  intros i Hi. rewrite (lor_disj (8 * (2 * i)) 8 4); [lia | lia | lia | | change (2 ^ 4)%Z with 16%Z; lia].
  change (2 ^ 4)%Z with 16%Z. replace (8 * (2 * i))%Z with (i * 16)%Z by lia. apply Z.mod_mul. lia.
Qed.

Lemma cf_range : forall t2 x, (0 <= x < 18446744073709551616)%Z ->
  Z.lor t2 (Z.b2z ((x + -309) mod 18446744073709551616 <? 18446744073709550965)) = 0%Z ->
  (x < 309 \/ 18446744073709551274 <= x)%Z.
Proof. intros t2 x Hx H. apply Z.lor_eq_0_iff in H. destruct H as [_ H]. Z.div_mod_to_equations. lia. Qed.

Section ArmDblCf.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis OKU : od_oku E.
  Hypothesis HFROMCH : fromchu_stmt_g usegs OD_FROMCH OD_GTOP.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation DINV st v24 v32 j40 j48 m1 :=
    (DBLINVu E st [C8 v24; C8 v32; CB 8 j40; CB 8 j48] [C8 (Z_to_bv 64 DBL_K88)] [C8 (Z_to_bv 64 DBL_K168)] m1).

  Local Ltac cf_exit Q st neg q0 HLAST HH FRM INV HK SG Hq0 pc :=
    lazymatch pc with
    | 0x290b4%Z => first [ eapply evt_eq; [| eapply (dbl_success E OK OKU Q st); [exact HLAST | exact HH | exact FRM | exact INV | exact HK]]; od_st_eq
                         | fail 100 "cut" pc ]
    | 0x2905c%Z => first [ eapply evt_eq; [| eapply (dbl_slow E OK OKU HFROMCH Q st neg q0); [exact HLAST | exact HH | exact FRM | exact INV | exact HK | exact SG | exact Hq0]]; od_st_eq
                         | fail 100 "cut" pc ]
    end.

  Lemma dbl_cf_c3 : forall (Q : machine_state -> Prop) st neg q0 v24 v32 j40 j48
      xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    DINV st v24 v32 j40 j48 m1 -> od_plus_k E Q st ->
    dbl_sgn neg v24 -> q0 = (tokI bs idxs (o_pos st) + neg)%Z ->
    evt usegs Q (ODST E 0x28ff4 xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 (o_BUF E + q0)) xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg) xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU HFROMCH.
    intros until m1. intros HLAST HH FRM INV HK SG Hq0.
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI. unfold DBL_K88, DBL_K168 in *.
    ddata xa1. ddata xa3. ddata xa4. ddata xa5. ddata xa6. ddata xa7. ddata xt0. ddata xt1. ddata xt2. ddata xt3. ddata xt4.
    dwalkv ltac:(cf_exit Q st neg q0 HLAST HH FRM INV2 HK SG Hq0).
  Qed.

  Local Ltac cf1_K Q st neg q0 w6 i EA HLAST HH FRM INV2 HK SG Hq0 pc :=
    lazymatch pc with
    | 0x28f0c%Z => first [ rewrite EA; ddata w6; dstep; dwalkv ltac:(cf1_K Q st neg q0 w6 i EA HLAST HH FRM INV2 HK SG Hq0) | fail 100 "cut" pc ]
    | 0x28fd0%Z => first [ rewrite (lor_16i_8 i) by lia; dstep; dwalkv ltac:(cf1_K Q st neg q0 w6 i EA HLAST HH FRM INV2 HK SG Hq0) | fail 100 "cut" pc ]
    | 0x28fd8%Z => first [ rewrite (lor_2i_1 i) by lia; dstep; dwalkv ltac:(cf1_K Q st neg q0 w6 i EA HLAST HH FRM INV2 HK SG Hq0) | fail 100 "cut" pc ]
    | 0x28ff4%Z => first [ eapply evt_eq; [| eapply (dbl_cf_c3 Q st neg q0); [exact HLAST | exact HH | exact FRM | exact INV2 | exact HK | exact SG | exact Hq0]]; od_st_eq
                         | fail 100 "cut" pc ]
    | 0x290b4%Z => first [ eapply evt_eq; [| eapply (dbl_success E OK OKU Q st); [exact HLAST | exact HH | exact FRM | exact INV2 | exact HK]]; od_st_eq
                         | fail 100 "cut" pc ]
    end.

  Lemma dbl_cf_c1 : forall (Q : machine_state -> Prop) st neg q0 (w6 : word) v24 v32 j40 j48
      xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa7 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    DINV st v24 v32 j40 j48 m1 -> od_plus_k E Q st ->
    dbl_sgn neg v24 -> q0 = (tokI bs idxs (o_pos st) + neg)%Z ->
    (bv_unsigned w6 < 309 \/ 18446744073709551274 <= bv_unsigned w6)%Z ->
    evt usegs Q (ODST E 0x28f00 xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 (o_BUF E + q0)) xa3 xa4 xa5 w6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg) xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU HFROMCH.
    intros until m1. intros HLAST HH FRM INV HK SG Hq0 RW.
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI. unfold DBL_K88, DBL_K168 in *.
    pose proof (bv_unsigned_in_range 64 w6) as R6. unfold bv_modulus in R6. cbn in R6.
    destruct (upow5_idx (bv_unsigned w6) R6 RW) as (i & Hi & EA).
    destruct (upow5_read m1 (2 * i) MI ltac:(lia)) as [pv0 RD0].
    destruct (upow5_read m1 (2 * i + 1) MI ltac:(lia)) as [pv1 RD1].
    ddata xa3. ddata pv0. ddata pv1.
    dwalkv ltac:(cf1_K Q st neg q0 w6 i EA HLAST HH FRM INV2 HK SG Hq0).
  Qed.

  Theorem dbl_cf : forall (Q : machine_state -> Prop) st,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_T_k E Q st.
  Proof using OK OKU HFROMCH.
    intros Q st HLAST HH HK. unfold dbl_T_k.
    intros neg q0 c v24 v32 j40 j48 xra xt0 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 xF xfc m1 SG Hq0 Rc FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB).
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI. unfold DBL_K88, DBL_K168 in *.
    pose proof (usown_read m1 c MI Rc) as RT. unfold UT_SOWN in RT.
    pose proof (osown_range c) as RTR.
    pose proof (bv_unsigned_in_range 64 xa6) as R6. unfold bv_modulus in R6. cbn in R6.
    ddata xa3.
    dwalk ltac:(fun pc => lazymatch pc with
      | 0x2877c%Z => first [ apply (HK st); [| exact FRM| dbl_close_od];
                             apply (acc_arm_out bs idxs st _ S1 HLAST HH); apply acc_none
                           | fail 100 "cut" pc ]
      | 0x2905c%Z => first [ eapply evt_eq; [| eapply (dbl_slow E OK OKU HFROMCH Q st neg q0); [exact HLAST | exact HH | exact FRM | exact INV2 | exact HK | exact SG | exact Hq0]]; od_st_eq
                           | fail 100 "cut" pc ]
      | 0x290b4%Z => first [ eapply evt_eq; [| eapply (dbl_success E OK OKU Q st); [exact HLAST | exact HH | exact FRM | exact INV2 | exact HK]]; od_st_eq
                           | fail 100 "cut" pc ]
      | 0x28f00%Z => first [ lazymatch goal with KBR : Z.lor _ (Z.b2z _) = 0%Z |- _ =>
                               eapply evt_eq; [| eapply (dbl_cf_c1 Q st neg q0 xa6);
                                                 [exact HLAST | exact HH | exact FRM | exact INV2 | exact HK | exact SG | exact Hq0 | exact (cf_range _ _ R6 KBR)]];
                               od_st_eq end
                           | fail 100 "cut" pc ]
      end).
  Qed.
End ArmDblCf.
