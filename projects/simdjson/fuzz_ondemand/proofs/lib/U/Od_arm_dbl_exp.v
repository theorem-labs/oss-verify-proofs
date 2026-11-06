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

Section ArmDblExp.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis OKU : od_oku E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation DINV st v24 v32 j40 j48 m1 :=
    (DBLINVu E st [C8 v24; C8 v32; CB 8 j40; CB 8 j48] [C8 (Z_to_bv 64 DBL_K88)] [C8 (Z_to_bv 64 DBL_K168)] m1).

  Notation XST st neg q0 pc xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 xF xfc m :=
    (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2
             (Z_to_bv 64 (o_COPY E)) (Z_to_bv 64 10) xa0 xa1 (Z_to_bv 64 (o_BUF E + q0)) xa3 xa4 xa5 xa6 xa7
             (Z_to_bv 64 2) (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 (o_act E)) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (FR_IT E)) xs7 (Z_to_bv 64 122)
             (Z_to_bv 64 4) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg) xt3 xt4 xt5 xt6)
        xF (Z_to_bv 64 pc) xfc None m (seg_rom usegs)).

  Lemma dbl_exp_tail : forall (Q : machine_state -> Prop) st (neg q0 c : Z) v24 v32 j40 j48
      xra xt0 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    DINV st v24 v32 j40 j48 m1 -> od_plus_k E Q st -> dbl_T_k E Q st ->
    dbl_sgn neg v24 -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (0 <= c < 256)%Z ->
    evt usegs Q (XST st neg q0 0x28e28 xra xt0 (Z_to_bv 64 c) xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros until m1. intros HLAST HH FRM INV HK HT SG Hq0 Rc.
    pose proof HH as (HP & HD & HEr & HAL & HB).
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI. unfold DBL_K88, DBL_K168 in *.
    ddata xt0. ddata xa6. ddata xa7. ddata xt4. ddata xt6.
    dwalkv ltac:(fun pc => lazymatch pc with
      | 0x2877c%Z => first [ apply (HK st); [| exact FRM| dbl_close_od];
                             apply (acc_arm_out bs idxs st _ S1 HLAST HH); apply acc_none
                           | fail 100 "cut" pc ]
      | 0x28e4c%Z => first [ eapply evt_eq; [| eapply (HT neg q0 c); [exact SG | exact Hq0 | exact Rc | exact FRM | exact INV2]]; od_st_eq
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma dbl_exp_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 r : Z) v24 v32 j40 j48
      xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    DINV st v24 v32 j40 j48 m1 -> od_plus_k E Q st -> dbl_T_k E Q st ->
    dbl_sgn neg v24 -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (0 <= r)%Z -> (48 <= B bs r <= 57)%Z ->
    (blen bs - r <= Z.of_nat f)%Z ->
    evt usegs Q (XST st neg q0 0x289d0 xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (o_BUF E + r))
                     (Z_to_bv 64 (o_BUF E + r)) xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HK HT SG Hq0 Hr HDIG Hf.
    - exfalso. assert (r < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (r < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      pose proof HH as (HP & HD & HEr & HAL & HB).
      assert (INV2 := INV). dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI. unfold DBL_K88, DBL_K168 in *.
      pose proof (od_B_range E BOK (r + 1)) as R1.
      pose proof (tokB_read m1 E (r + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (r + 1)) in *.
      ddata xt0. ddata xt5.
      dwalk ltac:(fun pc => lazymatch pc with
        | 0x289d0%Z => lazymatch goal with
                       | KB : (_ < 10)%Z |- _ =>
                           first [ eapply evt_eq; [| eapply (IH Q st neg q0 (r + 1)%Z);
                                     [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact SG| exact Hq0| lia| | lia]];
                                   [ od_st_eq | fold c; apply (zxb_digit c R1 KB) ]
                                 | fail 100 "cut" pc ]
                       end
        | 0x28e28%Z => first [ eapply evt_eq; [| eapply (dbl_exp_tail Q st neg q0 c); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact SG| exact Hq0| exact R1]];
                               od_st_eq
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Theorem dbl_exp : forall (Q : machine_state -> Prop) st,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_T_k E Q st -> dbl_E_k E Q st.
  Proof using OK OKU.
    intros Q st HLAST HH HK HT. unfold dbl_E_k.
    intros neg q0 p v24 v32 j40 j48 xra xt0 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt4 xt5 xt6 xF xfc m1 SG Hq0 Hp FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB).
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI. unfold DBL_K88, DBL_K168 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof SG as [NGR NV].
    pose proof (od_B_range E BOK p) as R0.
    set (c := B bs p) in *.
    ddata xa6.
    dwalk ltac:(fun pc => lazymatch pc with
      | 0x28e4c%Z => first [ eapply evt_eq; [| eapply (HT neg q0 c); [exact SG | exact Hq0 | exact R0 | exact FRM | exact INV2]]; od_st_eq
                           | fail 100 "cut" pc ]
      | 0x28984%Z => idtac
      end).

    lazymatch goal with KB : Z.lor c 32 = 101%Z |- _ =>
      assert (QL : (p < blen bs)%Z) by (apply B_nonzero_lt_len; fold c; apply (ori32_e_nonzero c R0 KB)); clear KB end.
    pose proof (od_B_range E BOK (p + 1)) as R1.
    pose proof (tokB_read m1 E (p + 1) BUFRO ltac:(lia)) as RB1.
    set (c1 := B bs (p + 1)) in *.
    dwalk ltac:(fun pc => lazymatch pc with 0x289a0%Z => idtac end).
    destruct (Z.ltb_spec (Z.land ((c1 + -43) mod 18446744073709551616) 18446744073709551613) 1) as [SGN|NS]; cbn [Z.b2z].
    -
      assert (Q1 : (p + 1 < blen bs)%Z) by (apply B_nonzero_lt_len; fold c1; apply (sign_nonzero c1 R1 SGN)).
      pose proof (od_B_range E BOK (p + 2)) as R2.
      pose proof (tokB_read m1 E (p + 2) BUFRO ltac:(lia)) as RB2.
      set (c2 := B bs (p + 2)) in *.
      dwalk ltac:(fun pc => lazymatch pc with
        | 0x28e28%Z => first [ eapply evt_eq; [| eapply (dbl_exp_tail Q st neg q0 c2); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact SG| exact Hq0| exact R2]];
                               od_st_eq
                             | fail 100 "cut" pc ]
        | 0x289d0%Z => lazymatch goal with
                       | KB : (_ <= 9)%Z |- _ =>
                           first [ eapply evt_eq; [| eapply (dbl_exp_loop (Z.to_nat (blen bs)) Q st neg q0 (p + 2)%Z);
                                     [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact SG| exact Hq0| lia| | lia]];
                                   [ od_st_eq | fold c2; apply (zxb_digit c2 R2); lia ]
                                 | fail 100 "cut" pc ]
                       end
        end).
    - dwalk ltac:(fun pc => lazymatch pc with
        | 0x28e28%Z => first [ eapply evt_eq; [| eapply (dbl_exp_tail Q st neg q0 c1); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact SG| exact Hq0| exact R1]];
                               od_st_eq
                             | fail 100 "cut" pc ]
        | 0x289d0%Z => lazymatch goal with
                       | KB : (_ <= 9)%Z |- _ =>
                           first [ eapply evt_eq; [| eapply (dbl_exp_loop (Z.to_nat (blen bs)) Q st neg q0 (p + 1)%Z);
                                     [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact SG| exact Hq0| lia| | lia]];
                                   [ od_st_eq | fold c1; apply (zxb_digit c1 R1); lia ]
                                 | fail 100 "cut" pc ]
                       end
        end).
  Qed.
End ArmDblExp.
