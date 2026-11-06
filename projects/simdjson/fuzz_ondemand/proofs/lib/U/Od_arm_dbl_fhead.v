(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjNumber SjNumSwar.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Od_arm_dbl_swar Od_arm_int.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_arm_dbl_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section ArmDblFhead.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Hypothesis OKU : od_oku E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation RINV st neg v24 v32 m1 :=
    (DBLINVu E st [C8 v24; C8 v32; C8 (Z_to_bv 64 neg); C8 (Z_to_bv 64 (o_act E))] [C8 (Z_to_bv 64 DBL_K88)] [C8 (Z_to_bv 64 DBL_K168)] m1).

  Notation HST st q0 q k pc xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xs3 xs4 xs7 xs8 xs11 xt3 xt4 xt5 xt6 xF xfc m :=
    (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 xt1 xt2
             (Z_to_bv 64 (o_COPY E)) (Z_to_bv 64 10) xa0 xa1 (Z_to_bv 64 (o_BUF E + q0)) xa3 xa4 xa5 (Z_to_bv 64 k) (Z_to_bv 64 (o_BUF E + q))
             (Z_to_bv 64 2) xs3 xs4 (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 (FR_IT E)) xs7 xs8
             (Z_to_bv 64 4) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) xs11 xt3 xt4 xt5 xt6)
        xF (Z_to_bv 64 pc) xfc None m (seg_rom usegs)).

  Lemma dbl_fh_p4 : forall (Q : machine_state -> Prop) st (neg q0 q k b0 b1 b2 b3 hi : Z) v24 v32
      xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xs3 xs4 xs7 xs8 xs11 xt3 xt4 xt5 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    RINV st neg v24 v32 m1 -> dbl_R_k E Q st ->
    dbl_sgn neg v24 -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (q0 <= q)%Z -> (1 <= k)%Z -> (q + k <= o_len E)%Z ->
    b0 = B bs (q + k) -> b1 = B bs (q + k + 1) -> b2 = B bs (q + k + 2) -> b3 = B bs (q + k + 3) ->
    evt usegs Q (HST st q0 q k 0x2888c xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xs3 xs4 xs7 xs8 xs11 xt3 xt4 xt5
                     (Z_to_bv 64 (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * hi))))) xF xfc m1).
  Proof using OK OKU.
    intros until m1. intros HLAST HH FRM INV HR SG Hq0 Hq Hk Hqk Hb0 Hb1 Hb2 Hb3.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof SG as [NGR NV].
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI. unfold DBL_K88, DBL_K168 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK (q + k)) as R0. pose proof (od_B_range E BOK (q + k + 1)) as R1.
    pose proof (od_B_range E BOK (q + k + 2)) as R2. pose proof (od_B_range E BOK (q + k + 3)) as R3.
    rewrite <- Hb0 in R0. rewrite <- Hb1 in R1. rewrite <- Hb2 in R2. rewrite <- Hb3 in R3.
    set (w := (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * hi))))%Z) in *.
    do 8 dstep0.
    if_cases K; zify_cond K.
    -
      clear K. clearbody w.
      do 4 dstep0.
      eapply evt_eq; [| eapply (HR neg q0 q k); [exact SG | exact Hq0 | exact Hq | lia | lia | exact FRM | exact INV2]].
      od_st_eq.
    -
      assert (G : (48 <= b0 /\ 48 <= b1 /\ 48 <= b2 /\ 48 <= b3)%Z).
      { rewrite !bv_swrap32, !swrap32_mod64 in K. unfold swrap32 in K.
        eapply swar4_ge48; [exact R0 | exact R1 | exact R2 | exact R3 | exact K]. }
      assert (QL : (q + k + 3 < blen bs)%Z) by (apply B_nonzero_lt_len; rewrite <- Hb3; lia).
      clear K. clearbody w.
      do 16 dstep0.
      eapply evt_eq; [| eapply (HR neg q0 q (k + 4)%Z); [exact SG | exact Hq0 | exact Hq | lia | lia | exact FRM | exact INV2]].
      od_st_eq.
  Qed.

  Lemma dbl_fh_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 q k : Z) v24 v32
      xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xs3 xs4 xs7 xs8 xs11 xt3 xt4 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    RINV st neg v24 v32 m1 -> dbl_R_k E Q st ->
    dbl_sgn neg v24 -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (q0 <= q)%Z -> (1 <= k)%Z -> (q + k + 8 <= o_len E)%Z ->
    (blen bs - (q + k) <= Z.of_nat f)%Z ->
    xt1 = Z_to_bv 64 1085102592571150095 -> xt2 = Z_to_bv 64 17361641481138401520 ->
    xt3 = Z_to_bv 64 434041037028460038 -> xt4 = Z_to_bv 64 3689348814741910323 ->
    evt usegs Q (HST st q0 q k 0x28064 xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xs3 xs4 xs7 xs8 xs11 xt3 xt4 (Z_to_bv 64 (o_BUF E + q + k + 8)) xt6 xF xfc m1).
  Proof using OK OKU.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HR SG Hq0 Hq Hk Hqk Hf -> -> -> ->; [exfalso; lia|].
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof SG as [NGR NV].
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI. unfold DBL_K88, DBL_K168 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (tokB_read m1 E (q + k + 8) BUFRO ltac:(lia)) as RB0. pose proof (tokB_read m1 E (q + k + 9) BUFRO ltac:(lia)) as RB1.
    pose proof (tokB_read m1 E (q + k + 10) BUFRO ltac:(lia)) as RB2. pose proof (tokB_read m1 E (q + k + 11) BUFRO ltac:(lia)) as RB3.
    pose proof (tokB_read m1 E (q + k + 12) BUFRO ltac:(lia)) as RB4. pose proof (tokB_read m1 E (q + k + 13) BUFRO ltac:(lia)) as RB5.
    pose proof (tokB_read m1 E (q + k + 14) BUFRO ltac:(lia)) as RB6. pose proof (tokB_read m1 E (q + k + 15) BUFRO ltac:(lia)) as RB7.
    pose proof (od_B_range E BOK (q + k + 8)) as R0. pose proof (od_B_range E BOK (q + k + 9)) as R1.
    pose proof (od_B_range E BOK (q + k + 10)) as R2. pose proof (od_B_range E BOK (q + k + 11)) as R3.
    pose proof (od_B_range E BOK (q + k + 12)) as R4. pose proof (od_B_range E BOK (q + k + 13)) as R5.
    pose proof (od_B_range E BOK (q + k + 14)) as R6. pose proof (od_B_range E BOK (q + k + 15)) as R7.
    set (c0 := B bs (q + k + 8)) in *. set (c1 := B bs (q + k + 9)) in *. set (c2 := B bs (q + k + 10)) in *. set (c3 := B bs (q + k + 11)) in *.
    set (c4 := B bs (q + k + 12)) in *. set (c5 := B bs (q + k + 13)) in *. set (c6 := B bs (q + k + 14)) in *. set (c7 := B bs (q + k + 15)) in *.
    do 6 dstep0. odnorm. do 10 dstep0. odnorm. do 3 dstep0. odnorm.
    do 24 dstep0.
    if_cases K; zify_cond K.
    -
      fold (le4z c4 c5 c6 c7) in K. fold (le4z c0 c1 c2 c3) in K. fold (le8z c0 c1 c2 c3 c4 c5 c6 c7) in K.
      pose proof (swar8n_machine c0 c1 c2 c3 c4 c5 c6 c7 _ R0 R1 R2 R3 R4 R5 R6 R7 K) as (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7).
      assert (QL : (q + k + 15 < blen bs)%Z) by (apply B_nonzero_lt_len; fold c7; lia).
      clear K.
      eapply evt_eq; [| eapply (IH Q st neg q0 q (k + 8)%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HR| exact SG| exact Hq0| exact Hq| lia| lia| lia
                                                              | reflexivity | reflexivity | reflexivity | reflexivity]].
      od_st_eq.
    - clear K. dstep0.
      fold (le4z c4 c5 c6 c7). fold (le4z c0 c1 c2 c3). fold (le8z c0 c1 c2 c3 c4 c5 c6 c7).
      rewrite (le8z_eq c0 c1 c2 c3 c4 c5 c6 c7 R0 R1 R2 R3 R4 R5 R6 R7).
      eapply evt_eq; [| eapply (dbl_fh_p4 Q st neg q0 q (k + 8)%Z c0 c1 c2 c3 (c4 + 256 * (c5 + 256 * (c6 + 256 * c7)))%Z);
                        [exact HLAST| exact HH| exact FRM| exact INV2| exact HR| exact SG| exact Hq0| exact Hq| lia| lia
                        | unfold c0; f_equal; lia | unfold c1; f_equal; lia | unfold c2; f_equal; lia | unfold c3; f_equal; lia]].
      od_st_eq.
  Qed.

  Theorem dbl_fhead : forall (Q : machine_state -> Prop) st,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st ->
    od_plus_k E Q st -> dbl_R_k E Q st -> dbl_F_k E Q st.
  Proof using OK OKU.
    intros Q st HLAST HH HK HR. unfold dbl_F_k.
    intros neg q0 q v24 v32 j40 j48 xra xt0 xt1 xt2 xa0 xa1 xa3 xa4 xa5 xa6 xt3 xt4 xt5 xt6 xF xfc m1 SG Hq0 Hq HDOT FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB). pose proof SG as [NGR NV].
    dbl_open_inv INV. od_env OK. od_envu OKU. clear S_SB S_SI S_SM SBI. unfold DBL_K88, DBL_K168 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    assert (QL : (q < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
    dwalk ltac:(fun pc => lazymatch pc with 0x27fb0%Z => idtac end).
    dstep0. dstep0.
    od_cur_mem ltac:(fun mm =>
      assert (INV2 : RINV st neg v24 v32 mm) by (unfold DBL_K88, DBL_K168; dbl_close_inv);
      pose proof (tokB_read mm E (q + 1) BUFRO ltac:(lia)) as RB1;
      pose proof (tokB_read mm E (q + 2) BUFRO ltac:(lia)) as RB2;
      pose proof (tokB_read mm E (q + 3) BUFRO ltac:(lia)) as RB3;
      pose proof (tokB_read mm E (q + 4) BUFRO ltac:(lia)) as RB4;
      pose proof (tokB_read mm E (q + 5) BUFRO ltac:(lia)) as RB5;
      pose proof (tokB_read mm E (q + 6) BUFRO ltac:(lia)) as RB6;
      pose proof (tokB_read mm E (q + 7) BUFRO ltac:(lia)) as RB7;
      pose proof (tokB_read mm E (q + 8) BUFRO ltac:(lia)) as RB8).
    pose proof (od_B_range E BOK (q + 1)) as R1. pose proof (od_B_range E BOK (q + 2)) as R2.
    pose proof (od_B_range E BOK (q + 3)) as R3. pose proof (od_B_range E BOK (q + 4)) as R4.
    pose proof (od_B_range E BOK (q + 5)) as R5. pose proof (od_B_range E BOK (q + 6)) as R6.
    pose proof (od_B_range E BOK (q + 7)) as R7. pose proof (od_B_range E BOK (q + 8)) as R8.
    set (b1 := B bs (q + 1)) in *. set (b2 := B bs (q + 2)) in *. set (b3 := B bs (q + 3)) in *. set (b4 := B bs (q + 4)) in *.
    set (b5 := B bs (q + 5)) in *. set (b6 := B bs (q + 6)) in *. set (b7 := B bs (q + 7)) in *. set (b8 := B bs (q + 8)) in *.
    do 4 dstep0. odnorm. do 7 dstep0. odnorm. do 3 dstep0. odnorm.
    do 22 dstep0.
    if_cases K; zify_cond K.
    -
      clear K. dstep0.
      fold (le4z b5 b6 b7 b8). fold (le4z b1 b2 b3 b4). fold (le8z b1 b2 b3 b4 b5 b6 b7 b8).
      rewrite (le8z_eq b1 b2 b3 b4 b5 b6 b7 b8 R1 R2 R3 R4 R5 R6 R7 R8).
      eapply evt_eq; [| eapply (dbl_fh_p4 Q st neg q0 q 1%Z b1 b2 b3 b4 (b5 + 256 * (b6 + 256 * (b7 + 256 * b8)))%Z);
                        [exact HLAST| exact HH| exact FRM| exact INV2| exact HR| exact SG| exact Hq0| lia| lia| lia
                        | reflexivity | unfold b2; f_equal; lia | unfold b3; f_equal; lia | unfold b4; f_equal; lia]].
      od_st_eq.
    -
      fold (le4z b5 b6 b7 b8) in K. fold (le4z b1 b2 b3 b4) in K. fold (le8z b1 b2 b3 b4 b5 b6 b7 b8) in K.
      pose proof (swar8n_machine b1 b2 b3 b4 b5 b6 b7 b8 _ R1 R2 R3 R4 R5 R6 R7 R8 K) as (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7).
      assert (QL8 : (q + 8 < blen bs)%Z) by (apply B_nonzero_lt_len; fold b8; lia).
      clear K.
      do 7 dstep0.
      eapply evt_eq; [| eapply (dbl_fh_loop (Z.to_nat (blen bs)) Q st neg q0 q 1%Z);
                        [exact HLAST| exact HH| exact FRM| exact INV2| exact HR| exact SG| exact Hq0| lia| lia| lia| lia
                        | reflexivity | reflexivity | reflexivity | reflexivity]].
      od_st_eq.
  Qed.
End ArmDblFhead.
