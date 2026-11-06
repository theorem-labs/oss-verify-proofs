(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjNumber SjNumSwar.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_num_kit Od_arm_dbl_swar Od_arm_dbl_defs Od_arm_int.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section ArmDblFhead.
  Variable E : odenv.
  Hypothesis OK : od_ok E.
  Notation bs := (o_bs E).
  Notation idxs := (o_idxs E).
  Notation RINV st neg w56 w64 v128 m1 :=
    (DBLINVc E st [C8 (Z_to_bv 64 DBL_K0); C8 (Z_to_bv 64 DBL_K8); C8 (Z_to_bv 64 (o_IDX E + 4 * o_pos st))]
                  [C8 w56; C8 w64; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 (o_act E)); C8 (Z_to_bv 64 neg)] [C8 v128; C8 (Z_to_bv 64 0x640001)] m1).

  Lemma dbl_fh_p4 : forall (Q : machine_state -> Prop) st (neg q0 q k b0 b1 b2 b3 hi : Z) w56 w64 v128
      xra xt0 xs1 xa0 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs10 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    RINV st neg w56 w64 v128 m1 -> dbl_R_k E Q st ->
    (0 <= neg <= 1)%Z -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (q0 <= q)%Z -> (1 <= k)%Z -> (q + k <= o_len E)%Z ->
    b0 = B bs (q + k) -> b1 = B bs (q + k + 1) -> b2 = B bs (q + k + 2) -> b3 = B bs (q + k + 3) ->
    evt psegs Q (MS (mkR xra (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 (Z_to_bv 64 k) (Z_to_bv 64 (o_BUF E + q))
                         (Z_to_bv 64 (FR_IT E)) xs1 xa0 (Z_to_bv 64 (o_BUF E + q0))
                         (Z_to_bv 64 (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * hi)))))
                         xa3 xa4 xa5 xa6 xa7
                         xs2 xs3 xs4 (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 (o_IDX E + 4 * o_pos st))
                         (Z_to_bv 64 10) xs10 (Z_to_bv 64 122) xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 0x28140) xfc None m1 (seg_rom psegs)).
  Proof using OK.
    intros until m1. intros HLAST HH FRM INV HR NGR Hq0 Hq Hk Hqk Hb0 Hb1 Hb2 Hb3.
    pose proof HH as (HP & HD & HEr & HAL & HB).
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K0, DBL_K8 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    pose proof (od_B_range E BOK (q + k)) as R0. pose proof (od_B_range E BOK (q + k + 1)) as R1.
    pose proof (od_B_range E BOK (q + k + 2)) as R2. pose proof (od_B_range E BOK (q + k + 3)) as R3.
    rewrite <- Hb0 in R0. rewrite <- Hb1 in R1. rewrite <- Hb2 in R2. rewrite <- Hb3 in R3.
    set (w := (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * hi))))%Z) in *.
    do 8 zstep.
    if_cases K; zify_cond K.
    -
      assert (G : (48 <= b0 /\ 48 <= b1 /\ 48 <= b2 /\ 48 <= b3)%Z).
      { rewrite !bv_swrap32, !swrap32_mod64 in K. unfold swrap32 in K.
        eapply swar4_ge48; [exact R0 | exact R1 | exact R2 | exact R3 | exact K]. }
      assert (QL : (q + k + 3 < blen bs)%Z) by (apply B_nonzero_lt_len; rewrite <- Hb3; lia).
      clear K. clearbody w.
      do 20 zstep.
      eapply evt_eq; [| eapply (HR neg q0 q (k + 4)%Z); [exact NGR | exact Hq0 | exact Hq | lia | lia | exact FRM | exact INV2]].
      od_st_eq.
    - clear K. clearbody w.
      do 10 zstep.
      eapply evt_eq; [| eapply (HR neg q0 q k); [exact NGR | exact Hq0 | exact Hq | lia | lia | exact FRM | exact INV2]].
      od_st_eq.
  Qed.

  Lemma dbl_fh_loop : forall (f : nat) (Q : machine_state -> Prop) st (neg q0 q k : Z) w56 w64 v128
      xt0 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs10 xt3 xt4 xt5 xt6 xF xfc m1,
    tokT bs idxs (o_n E - 1) = C_RBRACKET -> od_head_ok bs idxs 1 st -> frm0 xfc ->
    RINV st neg w56 w64 v128 m1 -> dbl_R_k E Q st ->
    (0 <= neg <= 1)%Z -> q0 = (tokI bs idxs (o_pos st) + neg)%Z -> (q0 <= q)%Z -> (1 <= k)%Z -> (q + k + 8 <= o_len E)%Z ->
    (blen bs - (q + k) <= Z.of_nat f)%Z ->
    xt3 = Z_to_bv 64 1085102592571150095 -> xt4 = Z_to_bv 64 17361641481138401520 ->
    xt5 = Z_to_bv 64 434041037028460038 -> xt6 = Z_to_bv 64 3689348814741910323 ->
    evt psegs Q (MS (mkR (Z_to_bv 64 (o_BUF E + q + k + 8)) (Z_to_bv 64 (FR E)) (o_gp E) (o_tp E) xt0 (Z_to_bv 64 k) (Z_to_bv 64 (o_BUF E + q))
                         (Z_to_bv 64 (FR_IT E)) xs1 xa0 (Z_to_bv 64 (o_BUF E + q0)) xa2 xa3 xa4 xa5 xa6 xa7
                         xs2 xs3 xs4 (Z_to_bv 64 (FR_IT E)) (Z_to_bv 64 2) (Z_to_bv 64 1) (Z_to_bv 64 (o_IDX E + 4 * o_pos st))
                         (Z_to_bv 64 10) xs10 (Z_to_bv 64 122) xt3 xt4 xt5 xt6)
                    xF (Z_to_bv 64 0x27c00) xfc None m1 (seg_rom psegs)).
  Proof using OK.
    intros f. induction f as [|f IH]; intros until m1; intros HLAST HH FRM INV HR NGR Hq0 Hq Hk Hqk Hf -> -> -> ->; [exfalso; lia|].
    pose proof HH as (HP & HD & HEr & HAL & HB).
    assert (INV2 := INV). dbl_open_inv INV. od_env OK. unfold DBL_K0, DBL_K8 in *.
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
    do 6 zstep. odnorm. do 10 zstep. odnorm. do 3 zstep. odnorm.
    do 24 zstep.
    if_cases K; zify_cond K.
    -
      fold (le4z c4 c5 c6 c7) in K. fold (le4z c0 c1 c2 c3) in K. fold (le8z c0 c1 c2 c3 c4 c5 c6 c7) in K.
      pose proof (swar8n_machine c0 c1 c2 c3 c4 c5 c6 c7 _ R0 R1 R2 R3 R4 R5 R6 R7 K) as (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7).
      assert (QL : (q + k + 15 < blen bs)%Z) by (apply B_nonzero_lt_len; fold c7; lia).
      clear K.
      eapply evt_eq; [| eapply (IH Q st neg q0 q (k + 8)%Z); [exact HLAST| exact HH| exact FRM| exact INV2| exact HR| exact NGR| exact Hq0| exact Hq| lia| lia| lia
                                                              | reflexivity | reflexivity | reflexivity | reflexivity]].
      od_st_eq.
    - clear K. zstep.
      fold (le4z c4 c5 c6 c7). fold (le4z c0 c1 c2 c3). fold (le8z c0 c1 c2 c3 c4 c5 c6 c7).
      rewrite (le8z_eq c0 c1 c2 c3 c4 c5 c6 c7 R0 R1 R2 R3 R4 R5 R6 R7).
      eapply evt_eq; [| eapply (dbl_fh_p4 Q st neg q0 q (k + 8)%Z c0 c1 c2 c3 (c4 + 256 * (c5 + 256 * (c6 + 256 * c7)))%Z);
                        [exact HLAST| exact HH| exact FRM| exact INV2| exact HR| exact NGR| exact Hq0| exact Hq| lia| lia
                        | unfold c0; f_equal; lia | unfold c1; f_equal; lia | unfold c2; f_equal; lia | unfold c3; f_equal; lia]].
      od_st_eq.
  Qed.

  Theorem dbl_fhead : dbl_fhead_stmt E.
  Proof using OK.
    unfold dbl_fhead_stmt. intros Q st HLAST HH HK HR. unfold dbl_F_k.
    intros neg q0 q v128 j56 j64 j72 j80 j136 xt0 xt1 xa0 xa2 xa3 xa4 xa7 xt3 xt4 xt5 xF xfc m1 NGR Hq0 Hq HDOT FRM INV.
    pose proof HH as (HP & HD & HEr & HAL & HB).
    dbl_open_inv INV. od_env OK. unfold DBL_K0, DBL_K8 in *.
    pose proof (od_tokI_range E S1 (o_pos st) ltac:(lia)) as TR.
    assert (QL : (q < blen bs)%Z) by (apply B_nonzero_lt_len; lia).
    zstep. zstep. lstep. zstep. lstep.
    od_cur_mem ltac:(fun mm =>
      assert (INV2 : RINV st neg xt0 xa7 v128 mm) by (unfold DBL_K0, DBL_K8; dbl_close_inv);
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
    zstep. zstep. zstep. zstep. odnorm.
    do 10 zstep. odnorm. do 10 zstep. do 10 zstep.
    if_cases K; zify_cond K.
    -
      clear K. zstep.
      fold (le4z b5 b6 b7 b8). fold (le4z b1 b2 b3 b4). fold (le8z b1 b2 b3 b4 b5 b6 b7 b8).
      rewrite (le8z_eq b1 b2 b3 b4 b5 b6 b7 b8 R1 R2 R3 R4 R5 R6 R7 R8).
      eapply evt_eq; [| eapply (dbl_fh_p4 Q st neg q0 q 1%Z b1 b2 b3 b4 (b5 + 256 * (b6 + 256 * (b7 + 256 * b8)))%Z);
                        [exact HLAST| exact HH| exact FRM| exact INV2| exact HR| exact NGR| exact Hq0| lia| lia| lia
                        | reflexivity | unfold b2; f_equal; lia | unfold b3; f_equal; lia | unfold b4; f_equal; lia]].
      od_st_eq.
    -
      fold (le4z b5 b6 b7 b8) in K. fold (le4z b1 b2 b3 b4) in K. fold (le8z b1 b2 b3 b4 b5 b6 b7 b8) in K.
      pose proof (swar8n_machine b1 b2 b3 b4 b5 b6 b7 b8 _ R1 R2 R3 R4 R5 R6 R7 R8 K) as (G0 & G1 & G2 & G3 & G4 & G5 & G6 & G7).
      assert (QL8 : (q + 8 < blen bs)%Z) by (apply B_nonzero_lt_len; fold b8; lia).
      clear K.
      do 7 zstep.
      eapply evt_eq; [| eapply (dbl_fh_loop (Z.to_nat (blen bs)) Q st neg q0 q 1%Z);
                        [exact HLAST| exact HH| exact FRM| exact INV2| exact HR| exact NGR| exact Hq0| lia| lia| lia| lia
                        | reflexivity | reflexivity | reflexivity | reflexivity]].
      od_st_eq.
  Qed.
End ArmDblFhead.
