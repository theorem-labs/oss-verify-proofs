(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the recorded node shapes of the r-free W1 certificates are removed with those certificates, and the hole tables stay for the released tree that the per-layout W1 trees are collected from. *)
(* The hole tables of the W1 tree W1TreeB.v, from which the per-r W1 trees are collected. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB  ItabBoth W0BStates1 W1BSt1 W1BSt2 W1BSt3 W1BSt4 W1BSt5 W1BSt6 W1BSt7 W1BSt8 W1BSt9 W1BSt10 W1BSt11 W1BSt12 W1BSt13 W1BSt14 W1BPlans.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition rsh_1 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) 0 (SCase (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SEmitP 1 [SPLit [48; 10]] (SExit 0)) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SEmitP 1 [SPLit [48; 10; 48; 10]] (SExit 0)) (SEmitP 1 [SPLit [48; 10; 48; 10; 48; 10]] (SExit 0)))))) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SCase (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SEmitP 1 [SPLit [48; 10]] (SExit 0)) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SEmitP 1 [SPLit [48; 10; 48; 10]] (SExit 0)) (SEmitP 1 [SPLit [48; 10; 48; 10; 48; 10]] (SExit 0)))))) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SCase (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SEmitP 1 [SPLit [48; 10]] (SExit 0)) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SEmitP 1 [SPLit [48; 10; 48; 10]] (SExit 0)) (SEmitP 1 [SPLit [48; 10; 48; 10; 48; 10]] (SExit 0)))))) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SCase (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SEmitP 1 [SPLit [48; 10]] (SExit 0)) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SEmitP 1 [SPLit [48; 10; 48; 10]] (SExit 0)) (SEmitP 1 [SPLit [48; 10; 48; 10; 48; 10]] (SExit 0)))))) (SCase (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SEmitP 1 [SPLit [48; 10]] (SExit 0)) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SEmitP 1 [SPLit [48; 10; 48; 10]] (SExit 0)) (SEmitP 1 [SPLit [48; 10; 48; 10; 48; 10]] (SExit 0)))))))))).
Definition rsh_2 : shape := SCase (EBlob true 8 1 1) 9223372036854775807 (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0)) (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0)).
Definition HT_1 : list (nat * (nat * acs)) := [(101%nat, (2%nat, ST_cb_s1))].
Definition HT_2 : list (nat * (nat * acs)) := [(131%nat, (2%nat, ST_cb_f1))].
Definition HT_3 : list (nat * (nat * acs)) := [(14%nat, (2%nat, ST_tb1_cont))].
Definition HR_4 : list (nat * (shape * acs)) := [(2520%nat, (rsh_1, T_g1b)); (1001%nat, (rsh_2, ST_tb1_a29_h1001)); (1003%nat, (rsh_2, ST_tb1_a29_h1003))].
Definition HR_5 : list (nat * (shape * acs)) := [(2530%nat, (rsh_2, T_w1n))].
Definition HR_6 : list (nat * (shape * acs)) := [(2520%nat, (rsh_1, T_g1b)); (1001%nat, (rsh_2, ST_tb1_a30_h1001)); (1003%nat, (rsh_2, ST_tb1_a30_h1003))].
Definition HR_7 : list (nat * (shape * acs)) := [(2600%nat, (rsh_1, T_g5b)); (1000%nat, (rsh_2, ST_tb1_as_h1000))].
Definition HT_8 : list (nat * (nat * acs)) := [(102%nat, (1%nat, ST_cb_r1))].
Definition HT_9 : list (nat * (nat * acs)) := [(103%nat, (2%nat, ST_cb_s2))].
Definition HT_10 : list (nat * (nat * acs)) := [(132%nat, (2%nat, ST_cb_f2))].
Definition HT_11 : list (nat * (nat * acs)) := [(14%nat, (2%nat, ST_tb2_cont))].
Definition HR_12 : list (nat * (shape * acs)) := [(2600%nat, (rsh_1, T_g5b)); (1000%nat, (rsh_2, ST_tb2_arm_h1000))].
Definition HT_13 : list (nat * (nat * acs)) := [(104%nat, (1%nat, ST_cb_r2))].
Definition HT_14 : list (nat * (nat * acs)) := [(105%nat, (2%nat, ST_cb_s3))].
Definition HT_15 : list (nat * (nat * acs)) := [(133%nat, (2%nat, ST_cb_f3))].
Definition HT_16 : list (nat * (nat * acs)) := [(14%nat, (2%nat, ST_tb3_cont))].
Definition HR_17 : list (nat * (shape * acs)) := [(2600%nat, (rsh_1, T_g5b)); (1000%nat, (rsh_2, ST_tb3_arm_h1000))].
Definition HT_18 : list (nat * (nat * acs)) := [(106%nat, (1%nat, ST_cb_r3))].
Definition HT_19 : list (nat * (nat * acs)) := [(107%nat, (2%nat, ST_cb_s4))].
Definition HT_20 : list (nat * (nat * acs)) := [(134%nat, (2%nat, ST_cb_f4))].
Definition HT_21 : list (nat * (nat * acs)) := [(14%nat, (2%nat, ST_tb4_cont))].
Definition HR_22 : list (nat * (shape * acs)) := [(2600%nat, (rsh_1, T_g5b)); (1000%nat, (rsh_2, ST_tb4_a_h1000))].
Definition HR_23 : list (nat * (shape * acs)) := [(2600%nat, (rsh_1, T_g5b)); (1000%nat, (rsh_2, ST_tb4_b_h1000))].
Definition HT_24 : list (nat * (nat * acs)) := [(108%nat, (1%nat, ST_cb_r4))].
Definition HT_25 : list (nat * (nat * acs)) := [(109%nat, (2%nat, ST_cb_s5))].
Definition HT_26 : list (nat * (nat * acs)) := [(135%nat, (2%nat, ST_cb_f5))].
Definition HT_27 : list (nat * (nat * acs)) := [(14%nat, (2%nat, ST_tb5_cont))].
Definition HR_28 : list (nat * (shape * acs)) := [(2350%nat, (rsh_1, T_d2xb5)); (1000%nat, (rsh_2, ST_tb5_arm_h1000))].
Definition HR_29 : list (nat * (shape * acs)) := [(900%nat, (rsh_1, T_d2xb5s))].
Definition HR_30 : list (nat * (shape * acs)) := [(2310%nat, (rsh_2, T_d2mb))].
Definition HT_31 : list (nat * (nat * acs)) := [(110%nat, (1%nat, ST_cb_r5))].
Definition HT_32 : list (nat * (nat * acs)) := [(111%nat, (2%nat, ST_cb_s6))].
Definition HT_33 : list (nat * (nat * acs)) := [(136%nat, (2%nat, ST_cb_f6))].
Definition HT_34 : list (nat * (nat * acs)) := [(14%nat, (2%nat, ST_tb6_cont))].
Definition HR_35 : list (nat * (shape * acs)) := [(2350%nat, (rsh_1, T_d2xb5)); (1000%nat, (rsh_2, ST_tb6_arm_h1000))].
Definition HT_36 : list (nat * (nat * acs)) := [(112%nat, (1%nat, ST_cb_r6))].
Definition HT_37 : list (nat * (nat * acs)) := [(113%nat, (2%nat, ST_cb_s7))].
Definition HT_38 : list (nat * (nat * acs)) := [(137%nat, (2%nat, ST_cb_f7))].
Definition HT_39 : list (nat * (nat * acs)) := [(14%nat, (2%nat, ST_tb7_cont))].
Definition HR_40 : list (nat * (shape * acs)) := [(2350%nat, (rsh_1, T_d2xb5)); (1000%nat, (rsh_2, ST_tb7_arm_h1000))].
Definition HT_41 : list (nat * (nat * acs)) := [(114%nat, (1%nat, ST_cb_r7))].
Definition HT_42 : list (nat * (nat * acs)) := [(115%nat, (2%nat, ST_cb_s8))].
Definition HT_43 : list (nat * (nat * acs)) := [(138%nat, (2%nat, ST_cb_f8))].
Definition HT_44 : list (nat * (nat * acs)) := [(14%nat, (2%nat, ST_tb8_cont))].
Definition HR_45 : list (nat * (shape * acs)) := [(2350%nat, (rsh_1, T_d2xb5)); (1000%nat, (rsh_2, ST_tb8_arm_h1000))].
Definition HT_46 : list (nat * (nat * acs)) := [(116%nat, (1%nat, ST_cb_r8))].
Definition HT_47 : list (nat * (nat * acs)) := [(117%nat, (2%nat, ST_cb_s9))].
Definition HT_48 : list (nat * (nat * acs)) := [(139%nat, (2%nat, ST_cb_f9))].
Definition HT_49 : list (nat * (nat * acs)) := [(14%nat, (2%nat, ST_tb9_cont))].
Definition HR_50 : list (nat * (shape * acs)) := [(2350%nat, (rsh_1, T_d2xb5)); (1000%nat, (rsh_2, ST_tb9_arm_h1000))].
Definition HT_51 : list (nat * (nat * acs)) := [(118%nat, (1%nat, ST_cb_r9))].
Definition HT_52 : list (nat * (nat * acs)) := [(119%nat, (2%nat, ST_cb_s10))].
Definition HT_53 : list (nat * (nat * acs)) := [(140%nat, (2%nat, ST_cb_f10))].
Definition HT_54 : list (nat * (nat * acs)) := [(14%nat, (2%nat, ST_tb10_cont))].
Definition HR_55 : list (nat * (shape * acs)) := [(2350%nat, (rsh_1, T_d2xb5)); (1000%nat, (rsh_2, ST_tb10_arm_h1000))].
