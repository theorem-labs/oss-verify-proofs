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

Section ArmDblFracTailA.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation off st := (tokI (o_bs E) (o_idxs E) (o_pos st)).

  Local Ltac to_E HE neg q0 p PS FRM INV2 pc :=
    lazymatch pc with
    | 0x9933c%Z => first [ eapply evt_eq; [| eapply (HE neg q0 p); [exact PS | lia | exact FRM | exact INV2]]; od_st_eq
                         | fail 100 "cut" pc ]
    end.

  Lemma dbl_zskip_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 p z : Z) j0 j8 j104 j112 v176
      xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DINVa E st neg j0 j8 j104 j112 v176 m1 ->
    od_plus_k E Q st -> dbl_E_k E Q st ->
    dbl_pos E st neg q0 -> (q0 <= p <= o_len E + 2)%Z -> (0 <= z <= o_len E + 4)%Z -> (blen bs + 5 - z <= Z.of_nat f)%Z ->
    evt asegs Q (ODST E 0x996d8 xt0 xt1 xt2 (Z_to_bv 64 (o_BUF E + z)) (Z_to_bv 64 (o_BUF E + z)) (Z_to_bv 64 (o_BUF E + p)) xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_BUF E + q0)) xt3 xt4 xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HK HE PS Hp Hz Hf; [exfalso; lia|].
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K16, DBL_K24 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK z) as R1.
    pose proof (tokB_read m1 E z BUFRO ltac:(lia)) as RB1.
    set (c := B bs z) in *.
    ddata xa4. ddata xa5.
    dwalkk ltac:(fun pc => lazymatch pc with
      | 0x996d8%Z => lazymatch goal with
                     | KB : (c = 48)%Z |- _ =>
                         first [ assert (ZL : (z < blen bs)%Z) by (apply B_nonzero_lt_len; fold c; lia);
                                 eapply evt_eq; [| eapply (IH Q st neg q0 p (z + 1)%Z);
                                   [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact PS| exact Hp| lia| lia]];
                                 od_st_eq
                               | fail 100 "cut" pc ]
                     end
      | 0x9933c%Z => to_E HE neg q0 p PS FRM INV2 pc
      end).
  Qed.

  Lemma dbl_frac_end : forall (Q : machine_state -> Prop) st (neg q0 p : Z) j0 j8 j104 j112 v176
      xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DINVa E st neg j0 j8 j104 j112 v176 m1 ->
    od_plus_k E Q st -> dbl_E_k E Q st ->
    dbl_pos E st neg q0 -> (q0 <= p <= o_len E + 2)%Z ->
    evt asegs Q (ODST E 0x9931c (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (off st)) xt2 xa0 xa1 (Z_to_bv 64 (o_BUF E + p)) xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_BUF E + q0)) xt3 xt4 xF xfc m1).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV HK HE PS Hp.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K16, DBL_K24 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    ddata xa5. ddata xt3.
    dwalkv ltac:(fun pc => lazymatch pc with
      | 0x9933c%Z => to_E HE neg q0 p PS FRM INV2 pc
      | 0x99334%Z => first [ pose proof (rw_cells_C8_read1_g _ _ _ _ _ FR176) as RDS; dstep0; clear RDS;
                             dwalkv ltac:(fun pc => lazymatch pc with
                               | 0x9933c%Z => to_E HE neg q0 p PS FRM INV2 pc
                               | 0x996d8%Z => first [ eapply evt_eq; [| eapply (dbl_zskip_loop (Z.to_nat (blen bs + 5)) Q st neg q0 p (q0 + 2)%Z);
                                                        [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact PS| exact Hp| lia| lia]];
                                                      od_st_eq
                                                    | fail 100 "cut" pc ]
                               end)
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma dbl_frac_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 q k : Z) j0 j8 j104 j112 v176
      xt2 xa0 xa2 xa3 xa5 xa7 xt4 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DINVa E st neg j0 j8 j104 j112 v176 m1 ->
    od_plus_k E Q st -> dbl_E_k E Q st ->
    dbl_pos E st neg q0 -> (q0 <= q)%Z -> (1 <= k)%Z -> (48 <= B bs (q + k) <= 57)%Z ->
    (blen bs - (q + k) <= Z.of_nat f)%Z ->
    evt asegs Q (ODST E 0x992c4 (Z_to_bv 64 (o_BUF E)) (Z_to_bv 64 (off st)) xt2 xa0 (Z_to_bv 64 (o_BUF E + q + 1)) xa2 xa3
                      (Z_to_bv 64 (o_BUF E + q)) xa5 (Z_to_bv 64 10) xa7
                      (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_BUF E + q0))
                      (Z_to_bv 64 k) xt4 xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HK HE PS Hq Hk HDIG Hf.
    - exfalso. assert (q + k < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (q + k < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
      assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K16, DBL_K24 in *.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_B_range E BOK (q + k + 1)) as R1.
      pose proof (tokB_read m1 E (q + k + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (q + k + 1)) in *.
      ddata xa5. ddata xa0.
      dwalkk ltac:(fun pc => lazymatch pc with
        | 0x992c4%Z => lazymatch goal with
                       | KB : (_ < 10)%Z |- _ =>
                           first [ eapply evt_eq; [| eapply (IH Q st neg q0 q (k + 1)%Z);
                                     [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact PS| exact Hq| lia| | lia]];
                                   [ od_st_eq | replace (q + (k + 1))%Z with (q + k + 1)%Z by lia; fold c; apply (zxb_digit c R1 KB) ]
                                 | fail 100 "cut" pc ]
                       end
        | 0x9931c%Z => first [ eapply evt_eq; [| eapply (dbl_frac_end Q st neg q0 (q + k + 1)%Z);
                                 [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact PS| lia]];
                               od_st_eq
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Theorem dbl_frac_tail : forall (Q : machine_state -> Prop) st,
    HLASTP E -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_E_k E Q st -> dbl_R_k E Q st.
  Proof using OK.
    intros Q st HLAST HH HK HE. unfold dbl_R_k.
    intros neg q0 q k1 j0 j8 j104 j112 v176 xt2 xa0 xa1 xa2 xa3 xa5 xa7 xt4 xF xfc m1 PS Hq Hk1 Hqk FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K16, DBL_K24 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK (q + k1)) as R1.
    pose proof (tokB_read m1 E (q + k1) BUFRO ltac:(lia)) as RB1.
    set (c := B bs (q + k1)) in *.
    ddata xa5.
    dwalkk ltac:(fun pc => lazymatch pc with
      | 0x98e3c%Z => first [ apply (HK st); [| exact FRM| dbl_close_od];
                             apply (acc_arm_out bs idxs st _ S1 HLAST HH); apply acc_none
                           | fail 100 "cut" pc ]
      | 0x992c4%Z => lazymatch goal with
                     | KB : (_ <= 9)%Z |- _ =>
                         first [ eapply evt_eq; [| eapply (dbl_frac_loop (Z.to_nat (blen bs)) Q st neg q0 q k1);
                                   [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact PS| exact Hq| exact Hk1| | lia]];
                                 [ od_st_eq | fold c; apply (zxb_digit c R1); lia ]
                               | fail 100 "cut" pc ]
                     end
      | 0x9931c%Z => first [ eapply evt_eq; [| eapply (dbl_frac_end Q st neg q0 (q + k1)%Z);
                               [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HE| exact PS| lia]];
                             od_st_eq
                           | fail 100 "cut" pc ]
      end).
  Qed.
End ArmDblFracTailA.
