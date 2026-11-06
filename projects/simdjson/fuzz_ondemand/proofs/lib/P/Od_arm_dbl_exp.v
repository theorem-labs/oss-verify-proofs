(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_arm_dbl_defs Od_arm_int.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma byte_forall : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true -> forall c, (0 <= c < 256)%Z -> P c = true.
Proof.
  intros P H c Hc. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma ori32_e_nonzero : forall c, (0 <= c < 256)%Z -> Z.lor c 32 = 101%Z -> c <> 0%Z.
Proof. intros c Hc H ->. vm_compute in H. discriminate. Qed.
Lemma sign_nonzero : forall c, (0 <= c < 256)%Z -> (Z.land ((c + -43) mod 18446744073709551616) 18446744073709551613 < 1)%Z -> c <> 0%Z.
Proof. intros c Hc H ->. vm_compute in H. discriminate. Qed.

Section ArmDblExp.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation DINV st neg j56 j64 j72 j80 j128 j136 m1 :=
    (DBLINVc E st [C8 (Z_to_bv 64 DBL_K0); C8 (Z_to_bv 64 DBL_K8); C8 (Z_to_bv 64 (o_IDX E + 4 * o_pos st))]
                  [CB 8 j56; CB 8 j64; CB 8 j72; CB 8 j80; C8 (Z_to_bv 64 neg)] [CB 8 j128; CB 8 j136] m1).

  Lemma dbl_exp_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 e0 k : Z) j56 j64 j72 j80 j128 j136
      xt1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET ->
    od_head_ok bs idxs 1 st -> frm0 xfc -> DINV st neg j56 j64 j72 j80 j128 j136 m1 ->
    od_plus_k E Q st -> dbl_T_k E Q st ->
    (0 <= neg <= 1)%Z -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (0 <= e0)%Z -> (0 <= k)%Z -> (48 <= B bs (e0 + k) <= 57)%Z ->
    (blen bs - (e0 + k) <= Z.of_nat f)%Z ->
    evt psegs Q (ODST E 0x2826c (Z_to_bv 64 k) xt1 (Z_to_bv 64 (o_BUF E + e0 + 1)) xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HK HT NGR Hq0 He0 Hk HDIG Hf.
    - exfalso. assert (e0 + k < blen bs)%Z by (apply B_nonzero_lt_len; lia). lia.
    - assert (QL : (e0 + k < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
      pose proof HH as (HP & HD & HE & HAL & HB).
      assert (INV2 := INV). dbl_open_inv INV. od_env OK.
      pose proof (od_B_range E BOK (e0 + k + 1)) as R1.
      pose proof (tokB_read m1 E (e0 + k + 1) BUFRO ltac:(lia)) as RB1.
      set (c := B bs (e0 + k + 1)) in *.
      zstep. zstep. odnorm. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      if_cases K; zify_cond K.
      + eapply evt_eq; [| eapply (IH Q st neg q0 e0 (k + 1)%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact NGR| exact Hq0| lia| lia| | ]].
        * od_st_eq.
        * replace (e0 + (k + 1))%Z with (e0 + k + 1)%Z by lia. fold c. apply (zxb_digit c R1 K).
        * lia.
      + zstep. zstep. if_cases K2; zify_cond K2.
        * apply (HK st); [| exact FRM| dbl_close_od].
          apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none.
        * zstep. zstep. if_cases K3; zify_cond K3.
          -- zstep. eapply evt_eq; [| eapply (HT neg q0 c); [exact NGR | exact Hq0 | exact R1 | exact FRM | exact INV2]]. od_st_eq.
          -- zstep. zstep. eapply evt_eq; [| eapply (HT neg q0 c); [exact NGR | exact Hq0 | exact R1 | exact FRM | exact INV2]]. od_st_eq.
  Qed.

  Theorem dbl_exp : forall (Q : machine_state -> Prop) st,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_T_k E Q st -> dbl_E_k E Q st.
  Proof using OK.
    intros Q st HLAST HH HK HT. unfold dbl_E_k.
    intros neg q0 q j56 j64 j72 j80 j128 j136 xt0 xt1 xt2 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xt4 xF xfc m1 NGR Hq0 Hq FRM INV.
    pose proof HH as (HP & HD & HE & HAL & HB).
    assert (INV2 := INV). dbl_open_inv INV. od_env OK.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK q) as R0.
    set (c := B bs q) in *.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    { eapply evt_eq; [| eapply (HT neg q0 c); [exact NGR | exact Hq0 | exact R0 | exact FRM | exact INV2]]. od_st_eq. }
    assert (QL : (q < blen bs)%Z) by (apply B_nonzero_lt_len; fold c; apply (ori32_e_nonzero c R0); lia).
    pose proof (od_B_range E BOK (q + 1)) as R1.
    pose proof (tokB_read m1 E (q + 1) BUFRO ltac:(lia)) as RB1.
    set (c1 := B bs (q + 1)) in *.
    zstep. odnorm. zstep. zstep. zstep. zstep.
    assert (KNONE : forall xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5,
      evt psegs Q (ODST E OD_PLUS xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xt3 xt4 xt5 xF xfc m1)).
    { intros. apply (HK st); [| exact FRM| dbl_close_od].
      apply (acc_arm_out bs idxs st _ S1 HLAST HH). apply acc_none. }
    unfold OD_PLUS in KNONE.
    destruct (Z.ltb_spec (Z.land ((c1 + -43) mod 18446744073709551616) 18446744073709551613) 1) as [SG|NS]; cbn [Z.b2z].
    -
      assert (Q1 : (q + 1 < blen bs)%Z) by (apply B_nonzero_lt_len; fold c1; apply (sign_nonzero c1 R1 SG)).
      pose proof (od_B_range E BOK (q + 2)) as R2.
      pose proof (tokB_read m1 E (q + 2) BUFRO ltac:(lia)) as RB2.
      set (c2 := B bs (q + 2)) in *.
      zstep. zstep. odnorm. zstep. zstep. zstep. zstep.
      if_cases K1; zify_cond K1; [apply KNONE|].
      zstep. zstep. zstep. zstep.
      eapply evt_eq; [| eapply (dbl_exp_loop (Z.to_nat (blen bs)) Q st neg q0 (q + 2)%Z 0%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact NGR| exact Hq0| lia| lia| | lia]].
      + od_st_eq.
      + replace (q + 2 + 0)%Z with (q + 2)%Z by lia. fold c2. apply (zxb_digit c2 R2). lia.
    - zstep. zstep. odnorm. zstep. zstep. zstep. zstep.
      if_cases K1; zify_cond K1; [apply KNONE|].
      zstep. zstep. zstep. zstep.
      eapply evt_eq; [| eapply (dbl_exp_loop (Z.to_nat (blen bs)) Q st neg q0 (q + 1)%Z 0%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HK| exact HT| exact NGR| exact Hq0| lia| lia| | lia]].
      + od_st_eq.
      + replace (q + 1 + 0)%Z with (q + 1)%Z by lia. fold c1. apply (zxb_digit c1 R1). lia.
  Qed.
End ArmDblExp.
