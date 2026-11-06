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

Section ArmDblExpA.
  Variable E : oaenv.
  Hypothesis OK : od_oka E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).

  Notation XST st q0 pc xt0 xt1 xt2 xa0 xa1 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m :=
    (MS (mkR (Z_to_bv 64 (o_act E)) (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
             (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 (Z_to_bv 64 (o_BUF E + q0)) xa4 xa5 xa6 xa7
             (Z_to_bv 64 10) (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
             (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) (Z_to_bv 64 (oa_F E + 200))
             (Z_to_bv 64 2) (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 (Z_to_bv 64 1))
        xF (Z_to_bv 64 pc) xfc None m (seg_rom asegs)).

  Lemma dbl_exp_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 e0 j : Z) j0 j8 j104 j112 v176
      xt0 xt1 xa0 xa2 xa4 xa5 xa6 xt3 xt4 xt5 xF xfc m1,
    HLASTP E -> od_head_ok bs idxs 1 st -> frm0 xfc -> DINVa E st neg j0 j8 j104 j112 v176 m1 ->
    od_plus_k E Q st -> dbl_T_k E Q st ->
    dbl_pos E st neg q0 -> (q0 <= e0)%Z -> (0 <= j)%Z -> (48 <= B bs (e0 + j) <= 57)%Z ->
    (blen bs - (e0 + j) <= Z.of_nat f)%Z ->
    evt asegs Q (XST st q0 0x993cc xt0 xt1 (Z_to_bv 64 (o_BUF E + e0 + 1)) xa0 (Z_to_bv 64 (o_BUF E + e0)) xa2 xa4 xa5 xa6 (Z_to_bv 64 j) xt3 xt4 xt5 xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HK HT PS He0 Hj HDIG Hf.
    - exfalso. assert (e0 + j < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (e0 + j < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
      assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K16, DBL_K24 in *.
      pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
      pose proof (od_B_range E BOK (e0 + j + 1)) as R1.
      pose proof (tokB_read m1 E (e0 + j + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (e0 + j + 1)) in *.
      ddata xa4. ddata xt1. ddata xa0. ddata xt3.
      dwalkk ltac:(fun pc => lazymatch pc with
        | 0x993cc%Z => lazymatch goal with
                       | KB : (_ < 10)%Z |- _ =>
                           first [ eapply evt_eq; [| eapply (IH Q st neg q0 e0 (j + 1)%Z);
                                     [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact PS| exact He0| lia| | lia]];
                                   [ od_st_eq | replace (e0 + (j + 1))%Z with (e0 + j + 1)%Z by lia; fold c; apply (zxb_digit c R1 KB) ]
                                 | fail 100 "cut" pc ]
                       end
        | 0x98e3c%Z => first [ apply (HK st); [| exact FRM| dbl_close_od];
                               apply (acc_arm_out bs idxs st _ S1 HLAST HH); apply acc_none
                             | fail 100 "cut" pc ]
        | 0x99440%Z => first [ eapply evt_eq; [| eapply (HT neg q0 (e0 + j + 1)%Z); [exact PS | lia | exact FRM | exact INV2]]; od_st_eq
                             | fail 100 "cut" pc ]
        end).
  Qed.

  Local Ltac exp_K Q st neg q0 e0 ce Re HLAST HH FRM HK HT PS pc :=
    lazymatch pc with
    | 0x98e3c%Z => first [ apply (HK st); [| exact FRM| dbl_close_od];
                           apply (acc_arm_out (o_bs E) (o_idxs E) st _ ltac:(eassumption) HLAST HH); apply acc_none
                         | fail 100 "cut" pc ]
    | 0x993cc%Z => first [ lazymatch goal with KB : (_ <= 9)%Z |- _ =>
                             eapply evt_eq; [| eapply (dbl_exp_loop (Z.to_nat (blen (o_bs E))) Q st neg q0 e0 0%Z);
                               [exact HLAST| exact HH| exact FRM| unfold DBL_K16, DBL_K24; dbl_close_inv | exact HK| exact HT| exact PS| lia| lia| | lia]];
                             [ od_st_eq | replace (e0 + 0)%Z with e0 by lia; fold ce; apply (zxb_digit ce Re); lia ] end
                         | fail 100 "cut" pc ]
    end.

  Theorem dbl_exp : forall (Q : machine_state -> Prop) st,
    HLASTP E -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_T_k E Q st -> dbl_E_k E Q st.
  Proof using OK.
    intros Q st HLAST HH HK HT. unfold dbl_E_k.
    intros neg q0 p j0 j8 j104 j112 v176 xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xF xfc m1 PS Hp FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof PS as [NGR Hq0].
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K16, DBL_K24 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK p) as R0.
    pose proof (tokB_read m1 E p BUFRO ltac:(lia)) as RB0.
    set (c := B bs p) in *.
    ddata xa5. ddata xt3.
    dwalkk ltac:(fun pc => lazymatch pc with
      | 0x99440%Z => first [ eapply evt_eq; [| eapply (HT neg q0 p); [exact PS | lia | exact FRM | exact INV2]]; od_st_eq
                           | fail 100 "cut" pc ]
      | 0x9935c%Z => idtac
      end).
    lazymatch goal with KB : Z.lor c 32 = 101%Z |- _ =>
      assert (QL : (p < blen bs)%Z) by (apply B_nonzero_lt_len; fold c; apply (ori32_e_nonzero c R0 KB)); clear KB end.
    clear RB0.
    pose proof (od_B_range E BOK (p + 1)) as R1.
    pose proof (tokB_read m1 E (p + 1) BUFRO ltac:(lia)) as RB1.
    set (c1 := B bs (p + 1)) in *.
    dwalkk ltac:(fun pc => lazymatch pc with 0x99380%Z => idtac end).
    destruct (Z.ltb_spec (Z.land ((c1 + -43) mod 18446744073709551616) 18446744073709551613) 1) as [SGN|NS]; cbn [Z.b2z].
    -
      assert (Q1 : (p + 1 < blen bs)%Z) by (apply B_nonzero_lt_len; fold c1; apply (sign_nonzero c1 R1 SGN)).
      pose proof (od_B_range E BOK (p + 2)) as R2.
      pose proof (tokB_read m1 E (p + 2) BUFRO ltac:(lia)) as RB2.
      set (c2 := B bs (p + 2)) in *.
      dwalkk ltac:(exp_K Q st neg q0 (p + 2)%Z c2 R2 HLAST HH FRM HK HT PS).
    - dwalkk ltac:(exp_K Q st neg q0 (p + 1)%Z c1 R1 HLAST HH FRM HK HT PS).
  Qed.
End ArmDblExpA.
