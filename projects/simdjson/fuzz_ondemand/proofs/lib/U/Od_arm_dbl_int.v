(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_arm_int.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_arm_dbl_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section ArmDblInt.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis OKU : od_oku E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation IINV st v24 j32 j40 j48 j88 j168 m1 :=
    (DBLINVu E st [C8 v24; CB 8 j32; CB 8 j40; CB 8 j48] [CB 8 j88] [CB 8 j168] m1).

  Local Ltac od_st_eq_B :=
    unfold wz; cbv delta [mkR];
    lazymatch goal with
    | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal
    end;
    repeat lazymatch goal with
    | |- TNode _ _ _ = TNode _ _ _ => f_equal
    | |- Some _ = Some _ => f_equal
    end;
    try reflexivity;
    lazymatch goal with
    | |- Z_to_bv 64 (B _ _) = Z_to_bv 64 (B _ _) => f_equal; f_equal; lia
    | |- Z_to_bv 64 ?c = Z_to_bv 64 (B _ _) => unfold c; f_equal; f_equal; lia
    | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [ exact wz_m1 | f_equal; lia ]
    end.

  Lemma dbl_int_tail : forall (Q : machine_state -> Prop) st (neg q0 k : Z) v24 j32 j40 j48 j88 j168
      xra xt0 xa0 xa1 xa3 xa4 xa5 xa6 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    IINV st v24 j32 j40 j48 j88 j168 m1 ->
    od_plus_k E Q st -> dbl_F_k E Q st -> dbl_E_k E Q st ->
    dbl_sgn neg v24 -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (0 <= k)%Z -> (q0 + k <= o_len E + 2)%Z ->
    evt usegs Q (ODST E 0x27f64 xra xt0 (Z_to_bv 64 (B bs (q0 + k))) (Z_to_bv 64 k) xa0 xa1 (Z_to_bv 64 (o_BUF E + q0)) xa3 xa4 xa5 xa6 (Z_to_bv 64 (o_BUF E + (q0 + k)))
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg) xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros until m1. intros HLAST HH FRM INV HK HF HE SG Hq0 Hk Hqk.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof SG as [NGR NV].
    dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK (q0 + k)) as R0.
    set (c := B bs (q0 + k)) in *.
    ddata xa4. ddata xa3.
    dwalk ltac:(fun pc => lazymatch pc with
      | 0x2877c%Z => first [ apply (HK st); [| exact FRM| dbl_close_od];
                             apply (acc_arm_out bs idxs st _ S1 HLAST HH); apply acc_none
                           | fail 100 "cut" pc ]
      | 0x27fa8%Z => first [ lazymatch goal with KB : (c = 46)%Z |- _ =>
                               eapply evt_eq; [| eapply (HF neg q0 (q0 + k)%Z); [exact SG | exact Hq0 | lia | exact KB | exact FRM | unfold DBL_K88, DBL_K168; dbl_close_inv]];
                               od_st_eq end
                           | fail 100 "cut" pc ]
      | 0x28978%Z => first [ eapply evt_eq; [| eapply (HE neg q0 (q0 + k)%Z); [exact SG | exact Hq0 | lia | exact FRM | unfold DBL_K88, DBL_K168; dbl_close_inv]];
                             od_st_eq
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma dbl_int_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 k : Z) v24 j32 j40 j48 j88 j168
      xra xt0 xt1 xa0 xa1 xa3 xa4 xa5 xa6 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    IINV st v24 j32 j40 j48 j88 j168 m1 ->
    od_plus_k E Q st -> dbl_F_k E Q st -> dbl_E_k E Q st ->
    dbl_sgn neg v24 -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (1 <= k)%Z -> (48 <= B bs (q0 + k) <= 57)%Z ->
    (blen bs - (q0 + k) <= Z.of_nat f)%Z ->
    evt usegs Q (ODST E 0x27f2c xra xt0 xt1 (Z_to_bv 64 k) xa0 xa1 (Z_to_bv 64 (o_BUF E + q0)) xa3 xa4 xa5 xa6 (Z_to_bv 64 (o_BUF E + (q0 + k)))
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg) xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HK HF HE SG Hq0 Hk HDIG Hf.
    - exfalso. assert (q0 + k < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (q0 + k < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      pose proof HH as (HP & HD & HEr & HAL & HB). pose proof SG as [NGR NV].
      assert (INV2 := INV). dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_B_range E BOK (q0 + k + 1)) as R1.
      pose proof (tokB_read m1 E (q0 + k + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (q0 + k + 1)) in *.
      ddata xa3. ddata xa5.
      dwalk ltac:(fun pc => lazymatch pc with
        | 0x27f2c%Z => lazymatch goal with
                       | KB : (_ < 10)%Z |- _ =>
                           first [ eapply evt_eq; [| eapply (IH Q st neg q0 (k + 1)%Z);
                                     [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HF| exact HE| exact SG| exact Hq0| lia| | lia]];
                                   [ od_st_eq | replace (q0 + (k + 1))%Z with (q0 + k + 1)%Z by lia; fold c; apply (zxb_digit c R1 KB) ]
                                 | fail 100 "cut" pc ]
                       end
        | 0x27f64%Z => first [ eapply evt_eq; [| eapply (dbl_int_tail Q st neg q0 (k + 1)%Z);
                                 [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HF| exact HE| exact SG| exact Hq0| lia| lia]];
                               [ od_st_eq_B ]
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Lemma u64_of_Z : forall z, bv_unsigned (Z_to_bv 64 z) = (z mod 18446744073709551616)%Z.
  Proof. intros z. rewrite Z_to_bv_unsigned. reflexivity. Qed.

  Local Ltac int_K Q st neg q0 k c1 R1 HLAST HH FRM HK HF HE SG Hq0 pc :=
    lazymatch pc with
    | 0x27f64%Z => first [ od_cur_mem ltac:(fun mm =>
                             eapply evt_eq; [| eapply (dbl_int_tail Q st neg q0 k);
                               [exact HLAST| exact HH| exact FRM| dbl_close_inv | exact HK| exact HF| exact HE| exact SG| exact Hq0| lia| lia]]);
                           od_st_eq_B
                         | fail 100 "cut" pc ]
    | 0x27f2c%Z => first [ od_cur_mem ltac:(fun mm =>
                             eapply evt_eq; [| eapply (dbl_int_loop (Z.to_nat (blen bs)) Q st neg q0 1%Z);
                               [exact HLAST| exact HH| exact FRM| dbl_close_inv | exact HK| exact HF| exact HE| exact SG| exact Hq0| lia| | lia]]);
                           [ od_st_eq | fold c1; apply (zxb_digit c1 R1); lia ]
                         | fail 100 "cut" pc ]
    end.

  Theorem od_dbl_int : forall (Q : machine_state -> Prop) st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> ODINV E st m1 ->
    od_plus_k E Q st -> dbl_F_k E Q st -> dbl_E_k E Q st ->
    evt usegs Q (ODST E 0x279b0 xra xt0 xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros Q st xra xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1 HLAST HH FRM INV HK HF HE.
    pose proof HH as (HP & HD & HEr & HAL & HB).
    od_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (off := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK off) as R0.
    pose proof (tokB_read m1 E off BUFRO ltac:(lia)) as RB0.
    set (b0 := B bs off) in *.
    assert (A8 : ((bv_unsigned (o_sp E) + -272) mod 8 = 0)%Z) by (apply od_sp_al8; [exact USP| reflexivity]).
    assert (A4 : ((o_IDX E + 4 * o_pos st) mod 4 = 0)%Z) by (apply od_idx_al4; lia).
    dwalk ltac:(fun pc => lazymatch pc with 0x27edc%Z => idtac end).

    match goal with |- context [Z.b2z (?x <? 1)] => set (neg := Z.b2z (x <? 1)) in * end.
    assert (SG : dbl_sgn neg (Z_to_bv 64 (b0 + -45))).
    { unfold dbl_sgn, neg. rewrite u64_of_Z. destruct (Z.ltb_spec ((b0 + -45) mod 18446744073709551616) 1); cbn [Z.b2z]; split; lia. }
    pose proof SG as [NGR NV].
    clearbody neg. set (v24 := Z_to_bv 64 (b0 + -45)) in *. clearbody v24.
    od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (off + neg) BUFRO ltac:(lia)) as RBn).
    pose proof (od_B_range E BOK (off + neg)) as Rn.
    set (d0 := B bs (off + neg)) in *.
    dwalk ltac:(fun pc => lazymatch pc with 0x27efc%Z => idtac end).
    destruct (Z.ltb_spec (Z.land ((d0 + -48) mod 18446744073709551616) 255) 10) as [DG|ND]; cbn [Z.b2z].
    -
      pose proof (zxb_digit d0 Rn DG) as D0.
      assert (QL : (off + neg < blen bs)%Z) by (apply B_nonzero_lt_len; fold d0; lia).
      od_cur_mem ltac:(fun mm => pose proof (tokB_read mm E (off + neg + 1) BUFRO ltac:(lia)) as RB1).
      pose proof (od_B_range E BOK (off + neg + 1)) as R1.
      set (d1 := B bs (off + neg + 1)) in *.
      dwalk ltac:(int_K Q st neg (off + neg)%Z 1%Z d1 R1 HLAST HH FRM HK HF HE SG (eq_refl (off + neg)%Z)).
    -
      dwalk ltac:(int_K Q st neg (off + neg)%Z 0%Z d0 Rn HLAST HH FRM HK HF HE SG (eq_refl (off + neg)%Z)).
  Qed.
End ArmDblInt.
