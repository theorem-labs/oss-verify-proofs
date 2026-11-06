(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjNumber SjNumSwar.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Od_arm_dbl_swar Od_arm_int.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow Sj_akit Od_defsA Od_cpsA Od_arm_dbl_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Local Ltac solve_load ::= first [ od_load_hook | solve_load_image | solve_load_base ].

Section ArmDblIntA.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation off st := (tokI (o_bs E) (o_idxs E) (o_pos st)).
  Notation IINV st neg j0 j8 j16 j24 j104 j112 v176 m1 :=
    (DBLINVa E st [CB 8 j0; CB 8 j8; CB 8 j16; CB 8 j24] [CB 8 j104; CB 8 j112; C8 (Z_to_bv 64 neg)] [C8 v176] m1).

  Lemma dbl_int_tail : forall (Q : machine_state -> Prop) st (neg q0 q : Z) j0 j8 j16 j24 j104 j112 v176
      xt0 xt1 xt2 xa1 xa2 xa3 xa5 xa6 xa7 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> IINV st neg j0 j8 j16 j24 j104 j112 v176 m1 ->
    od_plus_k E Q st -> dbl_F_k E Q st -> dbl_E_k E Q st ->
    dbl_pos E st neg q0 -> (q0 <= q <= o_len E + 2)%Z ->
    evt asegs Q (ODST E 0x97cb0 xt0 xt1 xt2 (Z_to_bv 64 (B bs q)) xa1 xa2 xa3 (Z_to_bv 64 (o_BUF E + q)) xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_BUF E + q0))
                      (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (off st)) xF xfc m1).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV HK HF HE PS Hq.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    dbl_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK q) as R0.
    set (c := B bs q) in *.
    ddata xa1. ddata xa2. ddata xa5.
    dwalkk ltac:(fun pc => lazymatch pc with
      | 0x98e3c%Z => first [ apply (HK st); [| exact FRM| dbl_close_od];
                             apply (acc_arm_out bs idxs st _ S1 HLAST HH); apply acc_none
                           | fail 100 "cut" pc ]
      | 0x97ce4%Z => first [ lazymatch goal with KB : (c = 46)%Z |- _ =>
                               eapply evt_eq; [| eapply (HF neg q0 q); [exact PS | exact Hq | exact KB | exact FRM | unfold DBL_K16, DBL_K24; dbl_close_inv]];
                               od_st_eq end
                           | fail 100 "cut" pc ]
      | 0x9933c%Z => first [ eapply evt_eq; [| eapply (HE neg q0 q); [exact PS | exact Hq | exact FRM | unfold DBL_K16, DBL_K24; dbl_close_inv]];
                             od_st_eq
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma dbl_int_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 k : Z) j0 j8 j16 j24 j104 j112 v176
      xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> IINV st neg j0 j8 j16 j24 j104 j112 v176 m1 ->
    od_plus_k E Q st -> dbl_F_k E Q st -> dbl_E_k E Q st ->
    dbl_pos E st neg q0 -> (2 <= k)%Z -> (48 <= B bs (q0 + k - 1) <= 57)%Z ->
    (blen bs - (q0 + k - 1) <= Z.of_nat f)%Z ->
    evt asegs Q (ODST E 0x975c8 (Z_to_bv 64 10) xt1 xt2 xa0 xa1 xa2 xa3 (Z_to_bv 64 k) xa5 xa6 (Z_to_bv 64 (o_BUF E + q0))
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_BUF E + q0))
                      (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (off st)) xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HK HF HE PS Hk HDIG Hf.
    - exfalso. assert (q0 + k - 1 < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (q0 + k - 1 < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
      assert (INV2 := INV). dbl_open_inv INV. od_env OK.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_B_range E BOK (q0 + k)) as R1.
      pose proof (tokB_read m1 E (q0 + k) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (q0 + k)) in *.
      ddata xa5. ddata xa3. ddata xa2.
      dwalkk ltac:(fun pc => lazymatch pc with
        | 0x975c8%Z => lazymatch goal with
                       | KB : (_ < 10)%Z |- _ =>
                           first [ eapply evt_eq; [| eapply (IH Q st neg q0 (k + 1)%Z);
                                     [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HF| exact HE| exact PS| lia| | lia]];
                                   [ od_st_eq | replace (q0 + (k + 1) - 1)%Z with (q0 + k)%Z by lia; fold c; apply (zxb_digit c R1 KB) ]
                                 | fail 100 "cut" pc ]
                       end
        | 0x98e3c%Z => first [ apply (HK st); [| exact FRM| dbl_close_od];
                               apply (acc_arm_out bs idxs st _ S1 HLAST HH); apply acc_none
                             | fail 100 "cut" pc ]
        | 0x97cb0%Z => first [ eapply evt_eq; [| eapply (dbl_int_tail Q st neg q0 (q0 + k)%Z);
                                 [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HF| exact HE| exact PS| lia]];
                               od_st_eq
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Local Ltac int_K Q st neg q0 c1 R1 HLAST HH FRM HK HF HE PS pc :=
    lazymatch pc with
    | 0x98e3c%Z => first [ apply (HK st); [| exact FRM| dbl_close_od];
                           apply (acc_arm_out (o_bs E) (o_idxs E) st _ ltac:(eassumption) HLAST HH); apply acc_none
                         | fail 100 "cut" pc ]
    | 0x97cb0%Z => first [ eapply evt_eq; [| eapply (dbl_int_tail Q st neg q0 (q0 + 1)%Z);
                             [exact HLAST| exact HH| exact FRM| dbl_close_inv | exact HK| exact HF| exact HE| exact PS| lia]];
                           od_st_eq
                         | fail 100 "cut" pc ]
    | 0x975c8%Z => first [ lazymatch goal with KB : (_ <= 9)%Z |- _ =>
                             eapply evt_eq; [| eapply (dbl_int_loop (Z.to_nat (blen (o_bs E))) Q st neg q0 2%Z);
                               [exact HLAST| exact HH| exact FRM| dbl_close_inv | exact HK| exact HF| exact HE| exact PS| lia| | lia]];
                             [ od_st_eq | replace (q0 + 2 - 1)%Z with (q0 + 1)%Z by lia; fold c1; apply (zxb_digit c1 R1); lia ] end
                         | fail 100 "cut" pc ]
    end.

  Theorem od_dbl_int : forall (Q : machine_state -> Prop) st,
    HLASTP E -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_F_k E Q st -> dbl_E_k E Q st -> arm_k E Q 0x974f0 st.
  Proof using OK.
    intros Q st HLAST HH HK HF HE. unfold arm_k.
    intros xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xF xfc m1 FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB).
    od_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokI_read m1 E ws (o_pos st) IDXA (conj IDXL IDXF) ltac:(lia)) as RD1.
    set (o := tokI bs idxs (o_pos st)) in *.
    pose proof (od_B_range E BOK o) as R0.
    pose proof (tokB_read m1 E o BUFRO ltac:(lia)) as RB0.
    set (b0 := B bs o) in *.
    dwalkk ltac:(fun pc => lazymatch pc with 0x9754c%Z => idtac end).
    match goal with |- context [Z.b2z (?x <? 1)] => set (neg := Z.b2z (x <? 1)) in * end.
    assert (NGR : (0 <= neg <= 1)%Z) by (unfold neg; destruct (_ <? 1)%Z; cbn; lia). clearbody neg.
    assert (PS : dbl_pos E st neg (o + neg)) by (split; [exact NGR | reflexivity]).
    clear RB0.
    pose proof (tokB_read m1 E (o + neg) BUFRO ltac:(lia)) as RBn.
    pose proof (od_B_range E BOK (o + neg)) as Rn.
    set (d0 := B bs (o + neg)) in *.
    dwalkk ltac:(fun pc => lazymatch pc with 0x97578%Z => idtac end).
    destruct (Z.ltb_spec (Z.land ((d0 + -48) mod 18446744073709551616) 255) 10) as [DG|ND]; cbn [Z.b2z].
    -
      pose proof (zxb_digit d0 Rn DG) as D0.
      assert (QL : (o + neg < blen bs)%Z) by (apply B_nonzero_lt_len; fold d0; lia).
      pose proof (tokB_read m1 E (o + neg + 1) BUFRO ltac:(lia)) as RB1.
      pose proof (od_B_range E BOK (o + neg + 1)) as R1.
      set (d1 := B bs (o + neg + 1)) in *.
      dwalkk ltac:(int_K Q st neg (o + neg)%Z d1 R1 HLAST HH FRM HK HF HE PS).
    -
      dwalkk ltac:(fun pc => lazymatch pc with
        | 0x98e3c%Z => first [ apply (HK st); [| exact FRM| dbl_close_od];
                               apply (acc_arm_out bs idxs st _ S1 HLAST HH); apply acc_none
                             | fail 100 "cut" pc ]
        | 0x975b8%Z => first [ exfalso; lazymatch goal with KB : (_ <= 9)%Z |- _ => clear - KB ND; lia end | fail 100 "cut (dead)" pc ]
        end).
  Qed.
End ArmDblIntA.
