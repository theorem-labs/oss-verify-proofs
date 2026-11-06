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

Section ArmDblFracTail.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis OKU : od_oku E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation RINV st neg v24 v32 m1 :=
    (DBLINVu E st [C8 v24; C8 v32; C8 (Z_to_bv 64 neg); C8 (Z_to_bv 64 (o_act E))] [C8 (Z_to_bv 64 DBL_K88)] [C8 (Z_to_bv 64 DBL_K168)] m1).

  Local Ltac to_E HE neg q0 p SG Hq0 FRM pc :=
    lazymatch pc with
    | 0x28978%Z => first [ lazymatch goal with FR24 : rw_cells _ _ (bv_unsigned (o_sp E) + -472)%Z _ |- _ => forget_40 FR24 end;
                           eapply evt_eq; [| eapply (HE neg q0 p); [exact SG | exact Hq0 | lia | exact FRM | unfold DBL_K88, DBL_K168; dbl_close_inv]];
                           od_st_eq
                         | fail 100 "cut" pc ]
    end.

  Lemma dbl_zskip_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 p z : Z) v24 v32
      xra xt0 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    RINV st neg v24 v32 m1 -> od_plus_k E Q st -> dbl_E_k E Q st ->
    dbl_sgn neg v24 -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (q0 <= p <= o_len E + 2)%Z ->
    (0 <= z)%Z -> B bs z = 48%Z -> (blen bs - z <= Z.of_nat f)%Z ->
    evt usegs Q (ODST E 0x29130 xra xt0 (Z_to_bv 64 (B bs p)) xt2 xa0 xa1 (Z_to_bv 64 (o_BUF E + q0)) xa3 xa4 xa5 xa6 (Z_to_bv 64 (o_BUF E + z))
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg)
                      (Z_to_bv 64 (o_BUF E + p)) xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HK HE SG Hq0 Hp Hz HZ Hf.
    - exfalso. assert (z < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (ZL : (z < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      pose proof HH as (HP & HD & HEr & HAL & HB). pose proof SG as [NGR NV].
      assert (INV2 := INV). dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI. unfold DBL_K88, DBL_K168 in *.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_B_range E BOK (z + 1)) as R1.
      pose proof (tokB_read m1 E (z + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (z + 1)) in *.
      dwalk ltac:(fun pc => lazymatch pc with
        | 0x29130%Z => lazymatch goal with
                       | KB : (c = 48)%Z |- _ =>
                           first [ eapply evt_eq; [| eapply (IH Q st neg q0 p (z + 1)%Z);
                                     [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact SG| exact Hq0| exact Hp| lia| exact KB | lia]];
                                   od_st_eq
                                 | fail 100 "cut" pc ]
                       end
        | 0x28978%Z => to_E HE neg q0 p SG Hq0 FRM pc
        end).
  Qed.

  Lemma dbl_frac_end : forall (Q : machine_state -> Prop) st (neg q0 q k p c : Z) v24 v32
      xra xt0 xt2 xa0 xa1 xa3 xa4 xa5 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    RINV st neg v24 v32 m1 -> od_plus_k E Q st -> dbl_E_k E Q st ->
    dbl_sgn neg v24 -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (q0 <= q)%Z -> (1 <= k)%Z -> (q + k <= o_len E + 2)%Z ->
    p = (q + k)%Z -> c = B bs p ->
    evt usegs Q (ODST E 0x2893c xra xt0 (Z_to_bv 64 c) xt2 xa0 xa1 (Z_to_bv 64 (o_BUF E + q0)) xa3 xa4 xa5 (Z_to_bv 64 k) (Z_to_bv 64 (o_BUF E + q))
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg)
                      (Z_to_bv 64 (o_BUF E + p)) xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros until m1. intros HLAST HH FRM INV HK HE SG Hq0 Hq Hk Hqk Hp ->.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof SG as [NGR NV].
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI. unfold DBL_K88, DBL_K168 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK (q0 + 2)) as R2.
    pose proof (tokB_read m1 E (q0 + 2) BUFRO ltac:(lia)) as RB2.
    set (c2 := B bs (q0 + 2)) in *.
    ddata v32.
    dwalk ltac:(fun pc => lazymatch pc with
      | 0x28978%Z => to_E HE neg q0 p SG Hq0 FRM pc
      | 0x29130%Z => lazymatch goal with
                     | KB : (c2 = 48)%Z |- _ =>
                         first [ eapply evt_eq; [| eapply (dbl_zskip_loop (Z.to_nat (blen bs)) Q st neg q0 p (q0 + 2)%Z);
                                   [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact SG| exact Hq0| lia| lia| exact KB | lia]];
                                 od_st_eq
                               | fail 100 "cut" pc ]
                     end
      end).
  Qed.

  Lemma dbl_frac_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 q k : Z) v24 v32
      xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    RINV st neg v24 v32 m1 -> od_plus_k E Q st -> dbl_E_k E Q st ->
    dbl_sgn neg v24 -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (q0 <= q)%Z -> (1 <= k)%Z -> (48 <= B bs (q + k) <= 57)%Z ->
    (blen bs - (q + k) <= Z.of_nat f)%Z ->
    evt usegs Q (ODST E 0x28908 xra xt0 xt1 xt2 xa0 xa1 (Z_to_bv 64 (o_BUF E + q0)) xa3 xa4 xa5 (Z_to_bv 64 k) (Z_to_bv 64 (o_BUF E + q))
                      (Z_to_bv 64 2) (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 neg) xt3 xt4 xt5 xt6 xF xfc m1).
  Proof using OK OKU.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HK HE SG Hq0 Hq Hk HDIG Hf.
    - exfalso. assert (q + k < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (q + k < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      pose proof HH as (HP & HD & HEr & HAL & HB). pose proof SG as [NGR NV].
      assert (INV2 := INV). dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI. unfold DBL_K88, DBL_K168 in *.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_B_range E BOK (q + k + 1)) as R1.
      pose proof (tokB_read m1 E (q + k + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (q + k + 1)) in *.
      ddata xa3. ddata xt2.
      dwalk ltac:(fun pc => lazymatch pc with
        | 0x28908%Z => lazymatch goal with
                       | KB : (_ < 10)%Z |- _ =>
                           first [ eapply evt_eq; [| eapply (IH Q st neg q0 q (k + 1)%Z);
                                     [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact SG| exact Hq0| exact Hq| lia| | lia]];
                                   [ od_st_eq | replace (q + (k + 1))%Z with (q + k + 1)%Z by lia; fold c; apply (zxb_digit c R1 KB) ]
                                 | fail 100 "cut" pc ]
                       end
        | 0x2893c%Z => first [ eapply evt_eq; [| eapply (dbl_frac_end Q st neg q0 q (k + 1)%Z (q + k + 1)%Z c);
                                 [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact SG| exact Hq0| exact Hq| lia| lia| lia| reflexivity]];
                               od_st_eq
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Theorem dbl_frac_tail : forall (Q : machine_state -> Prop) st,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_E_k E Q st -> dbl_R_k E Q st.
  Proof using OK OKU.
    intros Q st HLAST HH HK HE. unfold dbl_R_k.
    intros neg q0 q k1 v24 v32 xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xs11 xt3 xt4 xt5 xt6 xF xfc m1 SG Hq0 Hq Hk1 Hqk FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof SG as [NGR NV].
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI. unfold DBL_K88, DBL_K168 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK (q + k1)) as R1.
    pose proof (tokB_read m1 E (q + k1) BUFRO ltac:(lia)) as RB1.
    set (c := B bs (q + k1)) in *.
    ddata xa3.
    dwalk ltac:(fun pc => lazymatch pc with
      | 0x2877c%Z => first [ apply (HK st); [| exact FRM| dbl_close_od];
                             apply (acc_arm_out bs idxs st _ S1 HLAST HH); apply acc_none
                           | fail 100 "cut" pc ]
      | 0x28908%Z => lazymatch goal with
                     | KB : (_ <= 9)%Z |- _ =>
                         first [ eapply evt_eq; [| eapply (dbl_frac_loop (Z.to_nat (blen bs)) Q st neg q0 q k1);
                                   [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact SG| exact Hq0| exact Hq| exact Hk1| | lia]];
                                 [ od_st_eq | fold c; apply (zxb_digit c R1); lia ]
                               | fail 100 "cut" pc ]
                     end
      | 0x2893c%Z => first [ eapply evt_eq; [| eapply (dbl_frac_end Q st neg q0 q k1 (q + k1)%Z c);
                               [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact SG| exact Hq0| exact Hq| lia| lia| lia| reflexivity]];
                             od_st_eq
                           | fail 100 "cut" pc ]
      end).
  Qed.
End ArmDblFracTail.
