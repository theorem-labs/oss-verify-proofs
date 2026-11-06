(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue  ItabAsan W0States1 W1St1 W1St2 W1St3 W1St4 W1St5 W1St6 W1St7 W1St8 W1St9 W1St10 W1St11 W1St12 W1St13 W1Plans Main5W1AsanDefs Main5W1AsanCerts0 Main5W1AsanCerts1 Main5W1AsanCerts2 Main5W1AsanCerts3 Main5W1AsanCerts4 Main5W1AsanCerts5 Main5W1AsanCerts6 Main5W1AsanCerts7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition t_1 : mtree := (MEmpty 2%nat).
Definition r_2 : rtree := (RLeaf ts_g1).
Definition r_3 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_2).
Definition r_4 : rtree := (RLeaf nl_w1n).
Definition r_5 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_4).
Definition r_6 : rtree := (RPreS nf_w1n_hj HR_5 [(2530%nat, r_5)]).
Definition r_7 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_6).
Definition r_8 : rtree := (RPreS nf_w1n_1001_a29 HR_5 [(2530%nat, r_5)]).
Definition r_9 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_8).
Definition r_10 : rtree := (RPreS nf_w1n_1003 HR_5 [(2530%nat, r_5)]).
Definition r_11 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_10).
Definition t_12 : mtree := (MPreS 2%nat t1_a29g1 HR_4 [(2520%nat, r_3); (1001%nat, r_9); (1003%nat, r_11)]).
Definition r_13 : rtree := (RPreS nf_w1n_1001_a30 HR_5 [(2530%nat, r_5)]).
Definition r_14 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_13).
Definition t_15 : mtree := (MPreS 2%nat t1_a30g1 HR_6 [(2520%nat, r_3); (1001%nat, r_14); (1003%nat, r_11)]).
Definition r_16 : rtree := (RLeaf ts_g5).
Definition r_17 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) r_16).
Definition r_18 : rtree := (RLeaf nl_d0n).
Definition r_19 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 262143)]) r_18).
Definition r_20 : rtree := (RPreS t1_as_nulld0 HR_8 [(2410%nat, r_19)]).
Definition r_21 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_20).
Definition t_22 : mtree := (MPreS 2%nat t1_asd5 HR_7 [(2600%nat, r_17); (1000%nat, r_21)]).
Definition t_23 : mtree := (MCase (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 64512 t_15 t_22).
Definition t_24 : mtree := (MCase (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128 t_12 t_23).
Definition t_25 : mtree := (MPre 2%nat p1 HT_3 [(14%nat, t_24)]).
Definition t_26 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_25).
Definition t_27 : mtree := (MSplit QRoom 131065 t_26 t_1).
Definition t_28 : mtree := (MSplit QRoom 32762 t_1 t_27).
Definition t_29 : mtree := (MPre 2%nat c_f1 HT_2 [(131%nat, t_28)]).
Definition t_30 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) t_29).
Definition r_31 : rtree := (RPreS t2_arm_nulld0 HR_8 [(2410%nat, r_19)]).
Definition r_32 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) r_31).
Definition t_33 : mtree := (MPreS 2%nat t2_armd5 HR_13 [(2600%nat, r_17); (1000%nat, r_32)]).
Definition t_34 : mtree := (MPre 2%nat p2pre HT_12 [(14%nat, t_33)]).
Definition t_35 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) t_34).
Definition t_36 : mtree := (MSplit QRoom 262137 t_35 t_1).
Definition t_37 : mtree := (MSplit QRoom 98298 t_1 t_36).
Definition t_38 : mtree := (MPre 2%nat c_f2 HT_11 [(132%nat, t_37)]).
Definition t_39 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) t_38).
Definition r_40 : rtree := (RLeaf t3_arm_n1000).
Definition r_41 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) r_40).
Definition t_42 : mtree := (MPreS 2%nat t3_armd5 HR_18 [(2600%nat, r_17); (1000%nat, r_41)]).
Definition t_43 : mtree := (MPre 2%nat p3pre HT_17 [(14%nat, t_42)]).
Definition t_44 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) t_43).
Definition t_45 : mtree := (MSplit QRoom 524281 t_44 t_1).
Definition t_46 : mtree := (MSplit QRoom 229370 t_1 t_45).
Definition t_47 : mtree := (MPre 2%nat c_f3 HT_16 [(133%nat, t_46)]).
Definition t_48 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) t_47).
Definition r_49 : rtree := (RLeaf nl_g4n).
Definition r_50 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) r_49).
Definition r_51 : rtree := (RPreS t4_a_nulld4 HR_24 [(2510%nat, r_50)]).
Definition r_52 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) r_51).
Definition t_53 : mtree := (MPreS 2%nat t4_ad5 HR_23 [(2600%nat, r_17); (1000%nat, r_52)]).
Definition r_54 : rtree := (RPreS t4_b_nulld4 HR_24 [(2510%nat, r_50)]).
Definition r_55 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) r_54).
Definition t_56 : mtree := (MPreS 2%nat t4_bd5 HR_25 [(2600%nat, r_17); (1000%nat, r_55)]).
Definition t_57 : mtree := (MCase (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 524287 t_53 t_56).
Definition t_58 : mtree := (MPre 2%nat p4 HT_22 [(14%nat, t_57)]).
Definition t_59 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) t_58).
Definition t_60 : mtree := (MSplit QRoom 1048569 t_59 t_1).
Definition t_61 : mtree := (MSplit QRoom 491514 t_1 t_60).
Definition t_62 : mtree := (MPre 2%nat c_f4 HT_21 [(134%nat, t_61)]).
Definition t_63 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) t_62).
Definition r_64 : rtree := (RLeaf ts_d2xs).
Definition r_65 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) r_64).
Definition r_66 : rtree := (RPreS armxs HR_31 [(900%nat, r_65)]).
Definition r_67 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) r_66).
Definition r_68 : rtree := (RLeaf nl_d2m).
Definition r_69 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) r_68).
Definition r_70 : rtree := (RPreS t5_arm_nulld2m HR_32 [(2310%nat, r_69)]).
Definition r_71 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) r_70).
Definition t_72 : mtree := (MPreS 2%nat t5_arm_x2 HR_30 [(2350%nat, r_67); (1000%nat, r_71)]).
Definition t_73 : mtree := (MPre 2%nat p5pre HT_29 [(14%nat, t_72)]).
Definition t_74 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) t_73).
Definition t_75 : mtree := (MSplit QRoom 2097145 t_74 t_1).
Definition t_76 : mtree := (MSplit QRoom 1015802 t_1 t_75).
Definition t_77 : mtree := (MPre 2%nat c_f5 HT_28 [(135%nat, t_76)]).
Definition t_78 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) t_77).
Definition r_79 : rtree := (RPreS t6_arm_nulld2m HR_32 [(2310%nat, r_69)]).
Definition r_80 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) r_79).
Definition t_81 : mtree := (MPreS 2%nat t6_arm_x2 HR_37 [(2350%nat, r_67); (1000%nat, r_80)]).
Definition t_82 : mtree := (MPre 2%nat p6pre HT_36 [(14%nat, t_81)]).
Definition t_83 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) t_82).
Definition t_84 : mtree := (MSplit QRoom 4194297 t_83 t_1).
Definition t_85 : mtree := (MSplit QRoom 2064378 t_1 t_84).
Definition t_86 : mtree := (MPre 2%nat c_f6 HT_35 [(136%nat, t_85)]).
Definition t_87 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) t_86).
Definition r_88 : rtree := (RPreS t7_arm_nulld2m HR_32 [(2310%nat, r_69)]).
Definition r_89 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) r_88).
Definition t_90 : mtree := (MPreS 2%nat t7_arm_x2 HR_42 [(2350%nat, r_67); (1000%nat, r_89)]).
Definition t_91 : mtree := (MPre 2%nat p7pre HT_41 [(14%nat, t_90)]).
Definition t_92 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) t_91).
Definition t_93 : mtree := (MSplit QRoom 8388601 t_92 t_1).
Definition t_94 : mtree := (MSplit QRoom 4161530 t_1 t_93).
Definition t_95 : mtree := (MPre 2%nat c_f7 HT_40 [(137%nat, t_94)]).
Definition t_96 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) t_95).
Definition r_97 : rtree := (RPreS t8_arm_nulld2m HR_32 [(2310%nat, r_69)]).
Definition r_98 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) r_97).
Definition t_99 : mtree := (MPreS 2%nat t8_arm_x2 HR_47 [(2350%nat, r_67); (1000%nat, r_98)]).
Definition t_100 : mtree := (MPre 2%nat p8pre HT_46 [(14%nat, t_99)]).
Definition t_101 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) t_100).
Definition t_102 : mtree := (MSplit QRoom 16777209 t_101 t_1).
Definition t_103 : mtree := (MSplit QRoom 8355834 t_1 t_102).
Definition t_104 : mtree := (MPre 2%nat c_f8 HT_45 [(138%nat, t_103)]).
Definition t_105 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) t_104).
Definition r_106 : rtree := (RPreS t9_arm_nulld2m HR_32 [(2310%nat, r_69)]).
Definition r_107 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) r_106).
Definition t_108 : mtree := (MPreS 2%nat t9_arm_x2 HR_52 [(2350%nat, r_67); (1000%nat, r_107)]).
Definition t_109 : mtree := (MPre 2%nat p9pre HT_51 [(14%nat, t_108)]).
Definition t_110 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) t_109).
Definition t_111 : mtree := (MSplit QRoom 33554425 t_110 t_1).
Definition t_112 : mtree := (MSplit QRoom 16744442 t_1 t_111).
Definition t_113 : mtree := (MPre 2%nat c_f9 HT_50 [(139%nat, t_112)]).
Definition t_114 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) t_113).
Definition r_115 : rtree := (RPreS t10_arm_nulld2m HR_32 [(2310%nat, r_69)]).
Definition r_116 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) r_115).
Definition t_117 : mtree := (MPreS 2%nat t10_arm_x2 HR_57 [(2350%nat, r_67); (1000%nat, r_116)]).
Definition t_118 : mtree := (MPre 2%nat p10pre HT_56 [(14%nat, t_117)]).
Definition t_119 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) t_118).
Definition t_120 : mtree := (MSplit QRoom 67108857 t_119 t_1).
Definition t_121 : mtree := (MSplit QRoom 33521658 t_1 t_120).
Definition t_122 : mtree := (MPre 2%nat c_f10 HT_55 [(140%nat, t_121)]).
Definition t_123 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) t_122).
Definition t_124 : mtree := (MLeaf 2%nat c_r10).
Definition t_125 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]) t_124).
Definition t_126 : mtree := (MSplit QFlen 67108863 t_123 t_125).
Definition t_127 : mtree := (MPre 1%nat c_s10 HT_54 [(119%nat, t_126)]).
Definition t_128 : mtree := (MPre 1%nat c_r9 HT_53 [(118%nat, t_127)]).
Definition t_129 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) t_128).
Definition t_130 : mtree := (MSplit QFlen 33554431 t_114 t_129).
Definition t_131 : mtree := (MPre 1%nat c_s9 HT_49 [(117%nat, t_130)]).
Definition t_132 : mtree := (MPre 1%nat c_r8 HT_48 [(116%nat, t_131)]).
Definition t_133 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) t_132).
Definition t_134 : mtree := (MSplit QFlen 16777215 t_105 t_133).
Definition t_135 : mtree := (MPre 1%nat c_s8 HT_44 [(115%nat, t_134)]).
Definition t_136 : mtree := (MPre 1%nat c_r7 HT_43 [(114%nat, t_135)]).
Definition t_137 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) t_136).
Definition t_138 : mtree := (MSplit QFlen 8388607 t_96 t_137).
Definition t_139 : mtree := (MPre 1%nat c_s7 HT_39 [(113%nat, t_138)]).
Definition t_140 : mtree := (MPre 1%nat c_r6 HT_38 [(112%nat, t_139)]).
Definition t_141 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) t_140).
Definition t_142 : mtree := (MSplit QFlen 4194303 t_87 t_141).
Definition t_143 : mtree := (MPre 1%nat c_s6 HT_34 [(111%nat, t_142)]).
Definition t_144 : mtree := (MPre 1%nat c_r5 HT_33 [(110%nat, t_143)]).
Definition t_145 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) t_144).
Definition t_146 : mtree := (MSplit QFlen 2097151 t_78 t_145).
Definition t_147 : mtree := (MPre 1%nat c_s5 HT_27 [(109%nat, t_146)]).
Definition t_148 : mtree := (MPre 1%nat c_r4 HT_26 [(108%nat, t_147)]).
Definition t_149 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) t_148).
Definition t_150 : mtree := (MSplit QFlen 1048575 t_63 t_149).
Definition t_151 : mtree := (MPre 1%nat c_s4 HT_20 [(107%nat, t_150)]).
Definition t_152 : mtree := (MPre 1%nat c_r3 HT_19 [(106%nat, t_151)]).
Definition t_153 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) t_152).
Definition t_154 : mtree := (MSplit QFlen 524287 t_48 t_153).
Definition t_155 : mtree := (MPre 1%nat c_s3 HT_15 [(105%nat, t_154)]).
Definition t_156 : mtree := (MPre 1%nat c_r2 HT_14 [(104%nat, t_155)]).
Definition t_157 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) t_156).
Definition t_158 : mtree := (MSplit QFlen 262143 t_39 t_157).
Definition t_159 : mtree := (MPre 1%nat c_s2 HT_10 [(103%nat, t_158)]).
Definition t_160 : mtree := (MPre 1%nat c_r1 HT_9 [(102%nat, t_159)]).
Definition t_161 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) t_160).
Definition t_162 : mtree := (MSplit QFlen 131071 t_30 t_161).
Definition t_163 : mtree := (MPre 1%nat c_s1 HT_1 [(101%nat, t_162)]).
Definition t_164 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) t_163).
Lemma le_59 : class_le ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_63 : class_seg_ok (lv_of HT_1) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) s_62 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_64 : mcover HT_1 [(101%nat, t_162)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_67 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) ++ [(QFlen, QMIN, 131071)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_71 : class_seg_ok (lv_of HT_2) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) s_70 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_72 : mcover HT_2 [(131%nat, t_28)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_75 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, QMIN, 32762)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_78 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_82 : class_seg_ok (lv_of HT_3) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) s_81 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_83 : mcover HT_3 [(14%nat, t_24)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma lsh_85 : lshape_eqb (lvl_shape t_12) (lvl_shape t_23) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_89 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) (subst_holes (rs_of HR_4) s_88) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_90 : mcoverS HR_4 [(2520%nat, r_3); (1001%nat, r_9); (1003%nat, r_11)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_92 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_96 : shape_eqb (subst_holes (rs_of HR_5) s_95) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma vl_97 : shape_vars_lt NX0 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_98 : mcoverS HR_5 [(2530%nat, r_5)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_100 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_104 : shape_eqb s_103 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_110 : shape_eqb (subst_holes (rs_of HR_5) s_109) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_116 : shape_eqb (subst_holes (rs_of HR_5) s_115) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_122 : shape_eqb s_121 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma vl_123 : shape_vars_lt NX0 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma lsh_126 : lshape_eqb (lvl_shape t_15) (lvl_shape t_22) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_130 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) (subst_holes (rs_of HR_6) s_129) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_131 : mcoverS HR_6 [(2520%nat, r_3); (1001%nat, r_14); (1003%nat, r_11)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_136 : shape_eqb (subst_holes (rs_of HR_5) s_135) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_142 : shape_eqb (subst_holes (rs_of HR_5) s_141) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_148 : shape_eqb (subst_holes (rs_of HR_5) s_147) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_154 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) (subst_holes (rs_of HR_7) s_153) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_155 : mcoverS HR_7 [(2600%nat, r_17); (1000%nat, r_21)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_160 : shape_eqb (subst_holes (rs_of HR_8) s_159) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_161 : mcoverS HR_8 [(2410%nat, r_19)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_163 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 262143)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_167 : shape_eqb s_166 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_170 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_174 : shape_eqb s_173 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_178 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, 131065 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_181 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) ++ [(QFlen, 131071 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_185 : class_seg_ok (lv_of HT_9) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) s_184 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_186 : mcover HT_9 [(102%nat, t_159)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_190 : class_seg_ok (lv_of HT_10) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) s_189 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_191 : mcover HT_10 [(103%nat, t_158)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_194 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) ++ [(QFlen, QMIN, 262143)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_198 : class_seg_ok (lv_of HT_11) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) s_197 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_199 : mcover HT_11 [(132%nat, t_37)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_202 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, QMIN, 98298)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_205 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, QMIN, 262137)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_209 : class_seg_ok (lv_of HT_12) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) s_208 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_210 : mcover HT_12 [(14%nat, t_33)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_214 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) (subst_holes (rs_of HR_13) s_213) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_215 : mcoverS HR_13 [(2600%nat, r_17); (1000%nat, r_32)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_217 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_221 : shape_eqb (subst_holes (rs_of HR_8) s_220) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_223 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 262143)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_226 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_230 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, 262137 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_233 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) ++ [(QFlen, 262143 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_237 : class_seg_ok (lv_of HT_14) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) s_236 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_238 : mcover HT_14 [(104%nat, t_155)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_242 : class_seg_ok (lv_of HT_15) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) s_241 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_243 : mcover HT_15 [(105%nat, t_154)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_246 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) ++ [(QFlen, QMIN, 524287)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_250 : class_seg_ok (lv_of HT_16) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) s_249 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_251 : mcover HT_16 [(133%nat, t_46)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_254 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, QMIN, 229370)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_257 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, QMIN, 524281)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_261 : class_seg_ok (lv_of HT_17) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) s_260 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_262 : mcover HT_17 [(14%nat, t_42)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_266 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) (subst_holes (rs_of HR_18) s_265) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_267 : mcoverS HR_18 [(2600%nat, r_17); (1000%nat, r_41)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_269 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_273 : shape_eqb s_272 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_275 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_279 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, 524281 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_282 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) ++ [(QFlen, 524287 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_286 : class_seg_ok (lv_of HT_19) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) s_285 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_287 : mcover HT_19 [(106%nat, t_151)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_291 : class_seg_ok (lv_of HT_20) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) s_290 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_292 : mcover HT_20 [(107%nat, t_150)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_295 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) ++ [(QFlen, QMIN, 1048575)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_299 : class_seg_ok (lv_of HT_21) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) s_298 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_300 : mcover HT_21 [(134%nat, t_61)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_303 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, QMIN, 491514)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_306 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, QMIN, 1048569)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_310 : class_seg_ok (lv_of HT_22) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) s_309 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_311 : mcover HT_22 [(14%nat, t_57)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma lsh_313 : lshape_eqb (lvl_shape t_53) (lvl_shape t_56) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_317 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) (subst_holes (rs_of HR_23) s_316) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_318 : mcoverS HR_23 [(2600%nat, r_17); (1000%nat, r_52)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_320 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_324 : shape_eqb (subst_holes (rs_of HR_24) s_323) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_325 : mcoverS HR_24 [(2510%nat, r_50)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_327 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_331 : shape_eqb s_330 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_334 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_339 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) (subst_holes (rs_of HR_25) s_338) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_340 : mcoverS HR_25 [(2600%nat, r_17); (1000%nat, r_55)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_345 : shape_eqb (subst_holes (rs_of HR_24) s_344) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_350 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, 1048569 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_353 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) ++ [(QFlen, 1048575 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_357 : class_seg_ok (lv_of HT_26) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) s_356 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_358 : mcover HT_26 [(108%nat, t_147)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_362 : class_seg_ok (lv_of HT_27) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) s_361 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_363 : mcover HT_27 [(109%nat, t_146)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_366 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) ++ [(QFlen, QMIN, 2097151)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_370 : class_seg_ok (lv_of HT_28) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) s_369 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_371 : mcover HT_28 [(135%nat, t_76)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_374 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, QMIN, 1015802)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_377 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, QMIN, 2097145)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_381 : class_seg_ok (lv_of HT_29) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) s_380 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_382 : mcover HT_29 [(14%nat, t_72)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_386 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) (subst_holes (rs_of HR_30) s_385) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_387 : mcoverS HR_30 [(2350%nat, r_67); (1000%nat, r_71)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_389 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_393 : shape_eqb (subst_holes (rs_of HR_32) s_392) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_394 : mcoverS HR_32 [(2310%nat, r_69)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_396 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_400 : shape_eqb s_399 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_403 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_407 : shape_eqb (subst_holes (rs_of HR_31) s_406) (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_408 : mcoverS HR_31 [(900%nat, r_65)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_410 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_414 : shape_eqb s_413 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_419 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, 2097145 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_422 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) ++ [(QFlen, 2097151 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_426 : class_seg_ok (lv_of HT_33) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) s_425 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_427 : mcover HT_33 [(110%nat, t_143)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_431 : class_seg_ok (lv_of HT_34) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) s_430 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_432 : mcover HT_34 [(111%nat, t_142)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_435 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) ++ [(QFlen, QMIN, 4194303)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_439 : class_seg_ok (lv_of HT_35) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) s_438 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_440 : mcover HT_35 [(136%nat, t_85)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_443 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, QMIN, 2064378)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_446 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, QMIN, 4194297)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_450 : class_seg_ok (lv_of HT_36) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) s_449 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_451 : mcover HT_36 [(14%nat, t_81)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_455 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) (subst_holes (rs_of HR_37) s_454) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_456 : mcoverS HR_37 [(2350%nat, r_67); (1000%nat, r_80)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_458 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_462 : shape_eqb (subst_holes (rs_of HR_32) s_461) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_464 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_467 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_471 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, 4194297 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_474 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) ++ [(QFlen, 4194303 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_478 : class_seg_ok (lv_of HT_38) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) s_477 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_479 : mcover HT_38 [(112%nat, t_139)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_483 : class_seg_ok (lv_of HT_39) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) s_482 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_484 : mcover HT_39 [(113%nat, t_138)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_487 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) ++ [(QFlen, QMIN, 8388607)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_491 : class_seg_ok (lv_of HT_40) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) s_490 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_492 : mcover HT_40 [(137%nat, t_94)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_495 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, QMIN, 4161530)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_498 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, QMIN, 8388601)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_502 : class_seg_ok (lv_of HT_41) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) s_501 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_503 : mcover HT_41 [(14%nat, t_90)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_507 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) (subst_holes (rs_of HR_42) s_506) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_508 : mcoverS HR_42 [(2350%nat, r_67); (1000%nat, r_89)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_510 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_514 : shape_eqb (subst_holes (rs_of HR_32) s_513) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_516 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_519 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_523 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, 8388601 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_526 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) ++ [(QFlen, 8388607 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_530 : class_seg_ok (lv_of HT_43) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) s_529 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_531 : mcover HT_43 [(114%nat, t_135)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_535 : class_seg_ok (lv_of HT_44) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) s_534 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_536 : mcover HT_44 [(115%nat, t_134)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_539 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) ++ [(QFlen, QMIN, 16777215)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_543 : class_seg_ok (lv_of HT_45) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) s_542 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_544 : mcover HT_45 [(138%nat, t_103)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_547 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, QMIN, 8355834)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_550 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, QMIN, 16777209)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_554 : class_seg_ok (lv_of HT_46) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) s_553 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_555 : mcover HT_46 [(14%nat, t_99)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_559 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) (subst_holes (rs_of HR_47) s_558) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_560 : mcoverS HR_47 [(2350%nat, r_67); (1000%nat, r_98)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_562 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_566 : shape_eqb (subst_holes (rs_of HR_32) s_565) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_568 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_571 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_575 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, 16777209 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_578 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) ++ [(QFlen, 16777215 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_582 : class_seg_ok (lv_of HT_48) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) s_581 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_583 : mcover HT_48 [(116%nat, t_131)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_587 : class_seg_ok (lv_of HT_49) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) s_586 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_588 : mcover HT_49 [(117%nat, t_130)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_591 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) ++ [(QFlen, QMIN, 33554431)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_595 : class_seg_ok (lv_of HT_50) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) s_594 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_596 : mcover HT_50 [(139%nat, t_112)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_599 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, QMIN, 16744442)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_602 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, QMIN, 33554425)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_606 : class_seg_ok (lv_of HT_51) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) s_605 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_607 : mcover HT_51 [(14%nat, t_108)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_611 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) (subst_holes (rs_of HR_52) s_610) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_612 : mcoverS HR_52 [(2350%nat, r_67); (1000%nat, r_107)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_614 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_618 : shape_eqb (subst_holes (rs_of HR_32) s_617) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_620 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_623 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_627 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, 33554425 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_630 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) ++ [(QFlen, 33554431 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_634 : class_seg_ok (lv_of HT_53) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) s_633 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_635 : mcover HT_53 [(118%nat, t_127)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_639 : class_seg_ok (lv_of HT_54) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) s_638 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_640 : mcover HT_54 [(119%nat, t_126)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_643 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) ++ [(QFlen, QMIN, 67108863)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_647 : class_seg_ok (lv_of HT_55) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) s_646 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_648 : mcover HT_55 [(140%nat, t_121)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_651 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, QMIN, 33521658)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_654 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, QMIN, 67108857)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_658 : class_seg_ok (lv_of HT_56) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) s_657 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_659 : mcover HT_56 [(14%nat, t_117)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_663 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) (subst_holes (rs_of HR_57) s_662) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_664 : mcoverS HR_57 [(2350%nat, r_67); (1000%nat, r_116)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_666 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_670 : shape_eqb (subst_holes (rs_of HR_32) s_669) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_672 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_675 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_679 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, 67108857 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_682 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) ++ [(QFlen, 67108863 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_686 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]) s_685 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma nd_74 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, QMIN, 32762)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, QMIN, 32762)]) 2%nat eq_refl emp_75). Qed.
Lemma rn_101 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_w1n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_4 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_w1n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) nl_w1n _ c_102 eq_104 vl_97). Qed.
Lemma rn_99 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_w1n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_5 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_w1n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) _ le_100 rn_101). Qed.
Lemma rf_105 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(2530%nat, r_5)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2530%nat r_5 _ (rsh_2) T_w1n eq_refl rn_99 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma rn_93 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a29_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_10 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a29_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) nf_w1n_1003 HR_5 [(2530%nat, r_5)] _ c_94 req_96 vl_97 covs_98 rf_105). Qed.
Lemma rn_91 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a29_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) r_11 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a29_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) _ le_92 rn_93). Qed.
Lemma rf_111 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(2530%nat, r_5)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2530%nat r_5 _ (rsh_2) T_w1n eq_refl rn_99 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma rn_107 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a29_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_8 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a29_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) nf_w1n_1001_a29 HR_5 [(2530%nat, r_5)] _ c_108 req_110 vl_97 covs_98 rf_111). Qed.
Lemma rn_106 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a29_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) r_9 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a29_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) _ le_92 rn_107). Qed.
Lemma rf_117 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(2530%nat, r_5)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2530%nat r_5 _ (rsh_2) T_w1n eq_refl rn_99 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma rn_119 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_g1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_2 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_g1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ts_g1 _ c_120 eq_122 vl_123). Qed.
Lemma rn_118 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_g1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) r_3 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_g1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) _ le_92 rn_119). Qed.
Lemma rf_124 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) [(2520%nat, r_3); (1001%nat, r_9); (1003%nat, r_11)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 2520%nat r_3 _ (rsh_1) T_g1 eq_refl rn_118 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 1001%nat r_9 _ (rsh_2) ST_t1_a29_h1001 eq_refl rn_106 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 1003%nat r_11 _ (rsh_2) ST_t1_a29_h1003 eq_refl rn_91 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]))))). Qed.
Lemma nd_86 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat (mcase_lo ST_t1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_12 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat (mcase_lo ST_t1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 2%nat t1_a29g1 HR_4 [(2520%nat, r_3); (1001%nat, r_9); (1003%nat, r_11)] _ eq_refl c_87 pay_89 covs_90 rf_124). Qed.
Lemma rf_137 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(2530%nat, r_5)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2530%nat r_5 _ (rsh_2) T_w1n eq_refl rn_99 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma rn_133 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a30_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_10 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a30_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) nf_w1n_1003 HR_5 [(2530%nat, r_5)] _ c_134 req_136 vl_97 covs_98 rf_137). Qed.
Lemma rn_132 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a30_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) r_11 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a30_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) _ le_92 rn_133). Qed.
Lemma rf_143 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(2530%nat, r_5)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2530%nat r_5 _ (rsh_2) T_w1n eq_refl rn_99 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma rn_139 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a30_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_13 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a30_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) nf_w1n_1001_a30 HR_5 [(2530%nat, r_5)] _ c_140 req_142 vl_97 covs_98 rf_143). Qed.
Lemma rn_138 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a30_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) r_14 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_a30_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) _ le_92 rn_139). Qed.
Lemma rf_149 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(2530%nat, r_5)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2530%nat r_5 _ (rsh_2) T_w1n eq_refl rn_99 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma rf_150 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) [(2520%nat, r_3); (1001%nat, r_14); (1003%nat, r_11)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 2520%nat r_3 _ (rsh_1) T_g1 eq_refl rn_118 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 1001%nat r_14 _ (rsh_2) ST_t1_a30_h1001 eq_refl rn_138 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 1003%nat r_11 _ (rsh_2) ST_t1_a30_h1003 eq_refl rn_132 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]))))). Qed.
Lemma nd_127 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat (mcase_lo (mcase_hi ST_t1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 64512) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_15 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat (mcase_lo (mcase_hi ST_t1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 64512) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 2%nat t1_a30g1 HR_6 [(2520%nat, r_3); (1001%nat, r_14); (1003%nat, r_11)] _ eq_refl c_128 pay_130 covs_131 rf_150). Qed.
Lemma rn_164 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d0n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 262143)]) r_18 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d0n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 262143)]) nl_d0n _ c_165 eq_167 vl_97). Qed.
Lemma rn_162 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d0n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_19 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d0n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 262143)]) _ le_163 rn_164). Qed.
Lemma rf_168 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(2410%nat, r_19)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2410%nat r_19 _ (rsh_2) T_d0n eq_refl rn_162 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma rn_157 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_as_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_20 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_as_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) t1_as_nulld0 HR_8 [(2410%nat, r_19)] _ c_158 req_160 vl_97 covs_161 rf_168). Qed.
Lemma rn_156 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_as_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) r_21 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t1_as_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) _ le_92 rn_157). Qed.
Lemma rn_171 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_g5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) r_16 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_g5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) ts_g5 _ c_172 eq_174 vl_123). Qed.
Lemma rn_169 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_g5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) r_17 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_g5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) _ le_170 rn_171). Qed.
Lemma rf_175 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) [(2600%nat, r_17); (1000%nat, r_21)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 2600%nat r_17 _ (rsh_1) T_g5 eq_refl rn_169 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 1000%nat r_21 _ (rsh_2) ST_t1_as_h1000 eq_refl rn_156 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)])))). Qed.
Lemma nd_151 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat (mcase_hi (mcase_hi ST_t1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 64512) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_22 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat (mcase_hi (mcase_hi ST_t1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 64512) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 2%nat t1_asd5 HR_7 [(2600%nat, r_17); (1000%nat, r_21)] _ eq_refl c_152 pay_154 covs_155 rf_175). Qed.
Lemma nd_125 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat (mcase_hi ST_t1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_23 = true.
Proof. exact (mtree_ok_case 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat (mcase_hi ST_t1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 64512 t_15 t_22 lsh_126 nd_127 nd_151). Qed.
Lemma nd_84 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t1_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_24 = true.
Proof. exact (mtree_ok_case 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t1_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128 t_12 t_23 lsh_85 nd_86 nd_125). Qed.
Lemma fo_176 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) [(14%nat, t_24)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 14%nat t_24 _ 2%nat ST_t1_cont eq_refl nd_84 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]))). Qed.
Lemma nd_79 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_25 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 2%nat p1 HT_3 [(14%nat, t_24)] _ eq_refl c_80 seg_82 cov_83 fo_176). Qed.
Lemma nd_77 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f1 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) t_26 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f1 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_25 le_78 nd_79). Qed.
Lemma nd_177 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f1 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, 131065 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f1 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, 131065 + 1, QMAX)]) 2%nat eq_refl emp_178). Qed.
Lemma nd_76 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) t_27 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) QRoom 131065 t_26 t_1 nd_77 nd_177). Qed.
Lemma nd_73 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) t_28 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) QRoom 32762 t_1 t_27 nd_74 nd_76). Qed.
Lemma fo_179 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(131%nat, t_28)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 131%nat t_28 _ 2%nat ST_c_f1 eq_refl nd_73 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma nd_68 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) t_29 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2%nat c_f1 HT_2 [(131%nat, t_28)] _ eq_refl c_69 seg_71 cov_72 fo_179). Qed.
Lemma nd_66 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) ++ [(QFlen, QMIN, 131071)]) t_30 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) ++ [(QFlen, QMIN, 131071)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) t_29 le_67 nd_68). Qed.
Lemma nd_201 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, QMIN, 98298)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, QMIN, 98298)]) 2%nat eq_refl emp_202). Qed.
Lemma rn_222 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d0n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) r_19 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d0n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 262143)]) _ le_223 rn_164). Qed.
Lemma rf_224 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) [(2410%nat, r_19)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) 2410%nat r_19 _ (rsh_2) T_d0n eq_refl rn_222 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]))). Qed.
Lemma rn_218 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t2_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) r_31 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t2_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) t2_arm_nulld0 HR_8 [(2410%nat, r_19)] _ c_219 req_221 vl_97 covs_161 rf_224). Qed.
Lemma rn_216 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t2_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) r_32 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t2_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) _ le_217 rn_218). Qed.
Lemma rn_225 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_g5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) r_17 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_g5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) _ le_226 rn_171). Qed.
Lemma rf_227 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_13 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) [(2600%nat, r_17); (1000%nat, r_32)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_13 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) 2600%nat r_17 _ (rsh_1) T_g5 eq_refl rn_225 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_13 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) 1000%nat r_32 _ (rsh_2) ST_t2_arm_h1000 eq_refl rn_216 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_13 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)])))). Qed.
Lemma nd_211 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t2_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) t_33 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t2_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) 2%nat t2_armd5 HR_13 [(2600%nat, r_17); (1000%nat, r_32)] _ eq_refl c_212 pay_214 covs_215 rf_227). Qed.
Lemma fo_228 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_12 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) [(14%nat, t_33)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_12 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) 14%nat t_33 _ 2%nat ST_t2_cont eq_refl nd_211 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_12 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]))). Qed.
Lemma nd_206 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) t_34 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) 2%nat p2pre HT_12 [(14%nat, t_33)] _ eq_refl c_207 seg_209 cov_210 fo_228). Qed.
Lemma nd_204 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f2 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, QMIN, 262137)]) t_35 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f2 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, QMIN, 262137)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) t_34 le_205 nd_206). Qed.
Lemma nd_229 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f2 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, 262137 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f2 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, 262137 + 1, QMAX)]) 2%nat eq_refl emp_230). Qed.
Lemma nd_203 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) t_36 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) QRoom 262137 t_35 t_1 nd_204 nd_229). Qed.
Lemma nd_200 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) t_37 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) QRoom 98298 t_1 t_36 nd_201 nd_203). Qed.
Lemma fo_231 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_11 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) [(132%nat, t_37)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_11 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) 132%nat t_37 _ 2%nat ST_c_f2 eq_refl nd_200 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_11 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]))). Qed.
Lemma nd_195 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) t_38 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) 2%nat c_f2 HT_11 [(132%nat, t_37)] _ eq_refl c_196 seg_198 cov_199 fo_231). Qed.
Lemma nd_193 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) ++ [(QFlen, QMIN, 262143)]) t_39 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) ++ [(QFlen, QMIN, 262143)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) t_38 le_194 nd_195). Qed.
Lemma nd_253 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, QMIN, 229370)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, QMIN, 229370)]) 2%nat eq_refl emp_254). Qed.
Lemma rn_270 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t3_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) r_40 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t3_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) t3_arm_n1000 _ c_271 eq_273 vl_97). Qed.
Lemma rn_268 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t3_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) r_41 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t3_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) _ le_269 rn_270). Qed.
Lemma rn_274 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_g5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) r_17 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_g5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) _ le_275 rn_171). Qed.
Lemma rf_276 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_18 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) [(2600%nat, r_17); (1000%nat, r_41)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_18 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) 2600%nat r_17 _ (rsh_1) T_g5 eq_refl rn_274 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_18 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) 1000%nat r_41 _ (rsh_2) ST_t3_arm_h1000 eq_refl rn_268 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_18 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)])))). Qed.
Lemma nd_263 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t3_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) t_42 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t3_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) 2%nat t3_armd5 HR_18 [(2600%nat, r_17); (1000%nat, r_41)] _ eq_refl c_264 pay_266 covs_267 rf_276). Qed.
Lemma fo_277 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_17 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) [(14%nat, t_42)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_17 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) 14%nat t_42 _ 2%nat ST_t3_cont eq_refl nd_263 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_17 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]))). Qed.
Lemma nd_258 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) t_43 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) 2%nat p3pre HT_17 [(14%nat, t_42)] _ eq_refl c_259 seg_261 cov_262 fo_277). Qed.
Lemma nd_256 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f3 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, QMIN, 524281)]) t_44 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f3 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, QMIN, 524281)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) t_43 le_257 nd_258). Qed.
Lemma nd_278 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f3 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, 524281 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f3 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, 524281 + 1, QMAX)]) 2%nat eq_refl emp_279). Qed.
Lemma nd_255 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) t_45 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) QRoom 524281 t_44 t_1 nd_256 nd_278). Qed.
Lemma nd_252 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) t_46 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) QRoom 229370 t_1 t_45 nd_253 nd_255). Qed.
Lemma fo_280 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_16 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) [(133%nat, t_46)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_16 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) 133%nat t_46 _ 2%nat ST_c_f3 eq_refl nd_252 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_16 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]))). Qed.
Lemma nd_247 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) t_47 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) 2%nat c_f3 HT_16 [(133%nat, t_46)] _ eq_refl c_248 seg_250 cov_251 fo_280). Qed.
Lemma nd_245 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) ++ [(QFlen, QMIN, 524287)]) t_48 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) ++ [(QFlen, QMIN, 524287)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) t_47 le_246 nd_247). Qed.
Lemma nd_302 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, QMIN, 491514)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, QMIN, 491514)]) 2%nat eq_refl emp_303). Qed.
Lemma rn_328 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_g4n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) r_49 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_g4n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) nl_g4n _ c_329 eq_331 vl_97). Qed.
Lemma rn_326 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_g4n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) r_50 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_g4n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) _ le_327 rn_328). Qed.
Lemma rf_332 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_24 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) [(2510%nat, r_50)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_24 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) 2510%nat r_50 _ (rsh_2) T_g4n eq_refl rn_326 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_24 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]))). Qed.
Lemma rn_321 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t4_a_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) r_51 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t4_a_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) t4_a_nulld4 HR_24 [(2510%nat, r_50)] _ c_322 req_324 vl_97 covs_325 rf_332). Qed.
Lemma rn_319 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t4_a_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) r_52 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t4_a_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) _ le_320 rn_321). Qed.
Lemma rn_333 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_g5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) r_17 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_g5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) _ le_334 rn_171). Qed.
Lemma rf_335 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_23 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) [(2600%nat, r_17); (1000%nat, r_52)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_23 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 2600%nat r_17 _ (rsh_1) T_g5 eq_refl rn_333 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_23 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 1000%nat r_52 _ (rsh_2) ST_t4_a_h1000 eq_refl rn_319 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_23 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)])))). Qed.
Lemma nd_314 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat (mcase_lo ST_t4_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 524287) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) t_53 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat (mcase_lo ST_t4_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 524287) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 2%nat t4_ad5 HR_23 [(2600%nat, r_17); (1000%nat, r_52)] _ eq_refl c_315 pay_317 covs_318 rf_335). Qed.
Lemma rf_346 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_24 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) [(2510%nat, r_50)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_24 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) 2510%nat r_50 _ (rsh_2) T_g4n eq_refl rn_326 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_24 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]))). Qed.
Lemma rn_342 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t4_b_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) r_54 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t4_b_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) t4_b_nulld4 HR_24 [(2510%nat, r_50)] _ c_343 req_345 vl_97 covs_325 rf_346). Qed.
Lemma rn_341 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t4_b_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) r_55 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t4_b_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) _ le_320 rn_342). Qed.
Lemma rf_347 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_25 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) [(2600%nat, r_17); (1000%nat, r_55)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_25 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 2600%nat r_17 _ (rsh_1) T_g5 eq_refl rn_333 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_25 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 1000%nat r_55 _ (rsh_2) ST_t4_b_h1000 eq_refl rn_341 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_25 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)])))). Qed.
Lemma nd_336 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat (mcase_hi ST_t4_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 524287) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) t_56 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat (mcase_hi ST_t4_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 524287) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 2%nat t4_bd5 HR_25 [(2600%nat, r_17); (1000%nat, r_55)] _ eq_refl c_337 pay_339 covs_340 rf_347). Qed.
Lemma nd_312 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t4_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) t_57 = true.
Proof. exact (mtree_ok_case 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t4_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 524287 t_53 t_56 lsh_313 nd_314 nd_336). Qed.
Lemma fo_348 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_22 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) [(14%nat, t_57)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_22 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 14%nat t_57 _ 2%nat ST_t4_cont eq_refl nd_312 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_22 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]))). Qed.
Lemma nd_307 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) t_58 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 2%nat p4 HT_22 [(14%nat, t_57)] _ eq_refl c_308 seg_310 cov_311 fo_348). Qed.
Lemma nd_305 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f4 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, QMIN, 1048569)]) t_59 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f4 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, QMIN, 1048569)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) t_58 le_306 nd_307). Qed.
Lemma nd_349 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f4 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, 1048569 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f4 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, 1048569 + 1, QMAX)]) 2%nat eq_refl emp_350). Qed.
Lemma nd_304 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) t_60 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) QRoom 1048569 t_59 t_1 nd_305 nd_349). Qed.
Lemma nd_301 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) t_61 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) QRoom 491514 t_1 t_60 nd_302 nd_304). Qed.
Lemma fo_351 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_21 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) [(134%nat, t_61)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_21 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) 134%nat t_61 _ 2%nat ST_c_f4 eq_refl nd_301 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_21 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]))). Qed.
Lemma nd_296 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) t_62 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) 2%nat c_f4 HT_21 [(134%nat, t_61)] _ eq_refl c_297 seg_299 cov_300 fo_351). Qed.
Lemma nd_294 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) ++ [(QFlen, QMIN, 1048575)]) t_63 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) ++ [(QFlen, QMIN, 1048575)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) t_62 le_295 nd_296). Qed.
Lemma nd_373 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, QMIN, 1015802)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, QMIN, 1015802)]) 2%nat eq_refl emp_374). Qed.
Lemma rn_397 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) r_68 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) nl_d2m _ c_398 eq_400 vl_97). Qed.
Lemma rn_395 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) r_69 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_396 rn_397). Qed.
Lemma rf_401 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) [(2310%nat, r_69)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) 2310%nat r_69 _ (rsh_2) T_d2m eq_refl rn_395 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]))). Qed.
Lemma rn_390 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t5_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) r_70 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t5_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) t5_arm_nulld2m HR_32 [(2310%nat, r_69)] _ c_391 req_393 vl_97 covs_394 rf_401). Qed.
Lemma rn_388 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t5_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) r_71 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t5_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) _ le_389 rn_390). Qed.
Lemma rn_411 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2xs ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) r_64 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2xs ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) ts_d2xs _ c_412 eq_414 vl_123). Qed.
Lemma rn_409 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2xs ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) r_65 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2xs ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_410 rn_411). Qed.
Lemma rf_415 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_31 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) [(900%nat, r_65)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_31 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) 900%nat r_65 _ (rsh_1) T_d2xs eq_refl rn_409 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_31 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]))). Qed.
Lemma rn_404 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) r_66 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) armxs HR_31 [(900%nat, r_65)] _ c_405 req_407 vl_123 covs_408 rf_415). Qed.
Lemma rn_402 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) r_67 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_403 rn_404). Qed.
Lemma rf_416 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) [(2350%nat, r_67); (1000%nat, r_71)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) 2350%nat r_67 _ (rsh_1) T_d2x eq_refl rn_402 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) 1000%nat r_71 _ (rsh_2) ST_t5_arm_h1000 eq_refl rn_388 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)])))). Qed.
Lemma nd_383 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t5_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) t_72 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t5_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) 2%nat t5_arm_x2 HR_30 [(2350%nat, r_67); (1000%nat, r_71)] _ eq_refl c_384 pay_386 covs_387 rf_416). Qed.
Lemma fo_417 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_29 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) [(14%nat, t_72)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_29 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) 14%nat t_72 _ 2%nat ST_t5_cont eq_refl nd_383 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_29 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]))). Qed.
Lemma nd_378 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) t_73 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) 2%nat p5pre HT_29 [(14%nat, t_72)] _ eq_refl c_379 seg_381 cov_382 fo_417). Qed.
Lemma nd_376 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f5 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, QMIN, 2097145)]) t_74 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f5 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, QMIN, 2097145)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) t_73 le_377 nd_378). Qed.
Lemma nd_418 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f5 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, 2097145 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f5 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, 2097145 + 1, QMAX)]) 2%nat eq_refl emp_419). Qed.
Lemma nd_375 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) t_75 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) QRoom 2097145 t_74 t_1 nd_376 nd_418). Qed.
Lemma nd_372 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) t_76 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) QRoom 1015802 t_1 t_75 nd_373 nd_375). Qed.
Lemma fo_420 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_28 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) [(135%nat, t_76)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_28 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) 135%nat t_76 _ 2%nat ST_c_f5 eq_refl nd_372 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_28 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]))). Qed.
Lemma nd_367 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) t_77 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) 2%nat c_f5 HT_28 [(135%nat, t_76)] _ eq_refl c_368 seg_370 cov_371 fo_420). Qed.
Lemma nd_365 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) ++ [(QFlen, QMIN, 2097151)]) t_78 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) ++ [(QFlen, QMIN, 2097151)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) t_77 le_366 nd_367). Qed.
Lemma nd_442 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, QMIN, 2064378)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, QMIN, 2064378)]) 2%nat eq_refl emp_443). Qed.
Lemma rn_463 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) r_69 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_464 rn_397). Qed.
Lemma rf_465 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) [(2310%nat, r_69)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) 2310%nat r_69 _ (rsh_2) T_d2m eq_refl rn_463 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]))). Qed.
Lemma rn_459 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t6_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) r_79 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t6_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) t6_arm_nulld2m HR_32 [(2310%nat, r_69)] _ c_460 req_462 vl_97 covs_394 rf_465). Qed.
Lemma rn_457 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t6_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) r_80 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t6_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) _ le_458 rn_459). Qed.
Lemma rn_466 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) r_67 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_467 rn_404). Qed.
Lemma rf_468 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_37 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) [(2350%nat, r_67); (1000%nat, r_80)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_37 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) 2350%nat r_67 _ (rsh_1) T_d2x eq_refl rn_466 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_37 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) 1000%nat r_80 _ (rsh_2) ST_t6_arm_h1000 eq_refl rn_457 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_37 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)])))). Qed.
Lemma nd_452 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t6_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) t_81 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t6_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) 2%nat t6_arm_x2 HR_37 [(2350%nat, r_67); (1000%nat, r_80)] _ eq_refl c_453 pay_455 covs_456 rf_468). Qed.
Lemma fo_469 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_36 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) [(14%nat, t_81)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_36 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) 14%nat t_81 _ 2%nat ST_t6_cont eq_refl nd_452 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_36 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]))). Qed.
Lemma nd_447 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) t_82 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) 2%nat p6pre HT_36 [(14%nat, t_81)] _ eq_refl c_448 seg_450 cov_451 fo_469). Qed.
Lemma nd_445 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f6 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, QMIN, 4194297)]) t_83 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f6 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, QMIN, 4194297)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) t_82 le_446 nd_447). Qed.
Lemma nd_470 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f6 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, 4194297 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f6 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, 4194297 + 1, QMAX)]) 2%nat eq_refl emp_471). Qed.
Lemma nd_444 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) t_84 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) QRoom 4194297 t_83 t_1 nd_445 nd_470). Qed.
Lemma nd_441 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) t_85 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) QRoom 2064378 t_1 t_84 nd_442 nd_444). Qed.
Lemma fo_472 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_35 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) [(136%nat, t_85)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_35 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) 136%nat t_85 _ 2%nat ST_c_f6 eq_refl nd_441 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_35 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]))). Qed.
Lemma nd_436 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) t_86 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) 2%nat c_f6 HT_35 [(136%nat, t_85)] _ eq_refl c_437 seg_439 cov_440 fo_472). Qed.
Lemma nd_434 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) ++ [(QFlen, QMIN, 4194303)]) t_87 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) ++ [(QFlen, QMIN, 4194303)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) t_86 le_435 nd_436). Qed.
Lemma nd_494 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, QMIN, 4161530)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, QMIN, 4161530)]) 2%nat eq_refl emp_495). Qed.
Lemma rn_515 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) r_69 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_516 rn_397). Qed.
Lemma rf_517 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) [(2310%nat, r_69)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) 2310%nat r_69 _ (rsh_2) T_d2m eq_refl rn_515 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]))). Qed.
Lemma rn_511 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t7_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) r_88 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t7_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) t7_arm_nulld2m HR_32 [(2310%nat, r_69)] _ c_512 req_514 vl_97 covs_394 rf_517). Qed.
Lemma rn_509 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t7_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) r_89 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t7_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) _ le_510 rn_511). Qed.
Lemma rn_518 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) r_67 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_519 rn_404). Qed.
Lemma rf_520 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_42 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) [(2350%nat, r_67); (1000%nat, r_89)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_42 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) 2350%nat r_67 _ (rsh_1) T_d2x eq_refl rn_518 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_42 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) 1000%nat r_89 _ (rsh_2) ST_t7_arm_h1000 eq_refl rn_509 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_42 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)])))). Qed.
Lemma nd_504 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t7_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) t_90 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t7_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) 2%nat t7_arm_x2 HR_42 [(2350%nat, r_67); (1000%nat, r_89)] _ eq_refl c_505 pay_507 covs_508 rf_520). Qed.
Lemma fo_521 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_41 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) [(14%nat, t_90)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_41 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) 14%nat t_90 _ 2%nat ST_t7_cont eq_refl nd_504 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_41 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]))). Qed.
Lemma nd_499 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) t_91 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) 2%nat p7pre HT_41 [(14%nat, t_90)] _ eq_refl c_500 seg_502 cov_503 fo_521). Qed.
Lemma nd_497 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f7 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, QMIN, 8388601)]) t_92 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f7 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, QMIN, 8388601)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) t_91 le_498 nd_499). Qed.
Lemma nd_522 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f7 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, 8388601 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f7 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, 8388601 + 1, QMAX)]) 2%nat eq_refl emp_523). Qed.
Lemma nd_496 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) t_93 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) QRoom 8388601 t_92 t_1 nd_497 nd_522). Qed.
Lemma nd_493 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) t_94 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) QRoom 4161530 t_1 t_93 nd_494 nd_496). Qed.
Lemma fo_524 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_40 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) [(137%nat, t_94)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_40 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) 137%nat t_94 _ 2%nat ST_c_f7 eq_refl nd_493 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_40 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]))). Qed.
Lemma nd_488 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) t_95 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) 2%nat c_f7 HT_40 [(137%nat, t_94)] _ eq_refl c_489 seg_491 cov_492 fo_524). Qed.
Lemma nd_486 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) ++ [(QFlen, QMIN, 8388607)]) t_96 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) ++ [(QFlen, QMIN, 8388607)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) t_95 le_487 nd_488). Qed.
Lemma nd_546 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, QMIN, 8355834)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, QMIN, 8355834)]) 2%nat eq_refl emp_547). Qed.
Lemma rn_567 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) r_69 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_568 rn_397). Qed.
Lemma rf_569 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) [(2310%nat, r_69)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) 2310%nat r_69 _ (rsh_2) T_d2m eq_refl rn_567 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]))). Qed.
Lemma rn_563 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t8_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) r_97 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t8_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) t8_arm_nulld2m HR_32 [(2310%nat, r_69)] _ c_564 req_566 vl_97 covs_394 rf_569). Qed.
Lemma rn_561 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t8_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) r_98 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t8_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) _ le_562 rn_563). Qed.
Lemma rn_570 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) r_67 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_571 rn_404). Qed.
Lemma rf_572 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_47 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) [(2350%nat, r_67); (1000%nat, r_98)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_47 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) 2350%nat r_67 _ (rsh_1) T_d2x eq_refl rn_570 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_47 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) 1000%nat r_98 _ (rsh_2) ST_t8_arm_h1000 eq_refl rn_561 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_47 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)])))). Qed.
Lemma nd_556 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t8_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) t_99 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t8_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) 2%nat t8_arm_x2 HR_47 [(2350%nat, r_67); (1000%nat, r_98)] _ eq_refl c_557 pay_559 covs_560 rf_572). Qed.
Lemma fo_573 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_46 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) [(14%nat, t_99)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_46 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) 14%nat t_99 _ 2%nat ST_t8_cont eq_refl nd_556 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_46 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]))). Qed.
Lemma nd_551 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) t_100 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) 2%nat p8pre HT_46 [(14%nat, t_99)] _ eq_refl c_552 seg_554 cov_555 fo_573). Qed.
Lemma nd_549 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f8 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, QMIN, 16777209)]) t_101 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f8 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, QMIN, 16777209)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) t_100 le_550 nd_551). Qed.
Lemma nd_574 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f8 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, 16777209 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f8 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, 16777209 + 1, QMAX)]) 2%nat eq_refl emp_575). Qed.
Lemma nd_548 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) t_102 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) QRoom 16777209 t_101 t_1 nd_549 nd_574). Qed.
Lemma nd_545 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) t_103 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) QRoom 8355834 t_1 t_102 nd_546 nd_548). Qed.
Lemma fo_576 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_45 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) [(138%nat, t_103)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_45 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) 138%nat t_103 _ 2%nat ST_c_f8 eq_refl nd_545 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_45 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]))). Qed.
Lemma nd_540 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) t_104 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) 2%nat c_f8 HT_45 [(138%nat, t_103)] _ eq_refl c_541 seg_543 cov_544 fo_576). Qed.
Lemma nd_538 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) ++ [(QFlen, QMIN, 16777215)]) t_105 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) ++ [(QFlen, QMIN, 16777215)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) t_104 le_539 nd_540). Qed.
Lemma nd_598 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, QMIN, 16744442)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, QMIN, 16744442)]) 2%nat eq_refl emp_599). Qed.
Lemma rn_619 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) r_69 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_620 rn_397). Qed.
Lemma rf_621 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) [(2310%nat, r_69)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) 2310%nat r_69 _ (rsh_2) T_d2m eq_refl rn_619 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]))). Qed.
Lemma rn_615 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t9_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) r_106 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t9_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) t9_arm_nulld2m HR_32 [(2310%nat, r_69)] _ c_616 req_618 vl_97 covs_394 rf_621). Qed.
Lemma rn_613 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t9_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) r_107 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t9_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) _ le_614 rn_615). Qed.
Lemma rn_622 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) r_67 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_623 rn_404). Qed.
Lemma rf_624 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_52 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) [(2350%nat, r_67); (1000%nat, r_107)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_52 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) 2350%nat r_67 _ (rsh_1) T_d2x eq_refl rn_622 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_52 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) 1000%nat r_107 _ (rsh_2) ST_t9_arm_h1000 eq_refl rn_613 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_52 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)])))). Qed.
Lemma nd_608 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t9_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) t_108 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t9_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) 2%nat t9_arm_x2 HR_52 [(2350%nat, r_67); (1000%nat, r_107)] _ eq_refl c_609 pay_611 covs_612 rf_624). Qed.
Lemma fo_625 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_51 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) [(14%nat, t_108)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_51 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) 14%nat t_108 _ 2%nat ST_t9_cont eq_refl nd_608 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_51 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]))). Qed.
Lemma nd_603 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) t_109 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) 2%nat p9pre HT_51 [(14%nat, t_108)] _ eq_refl c_604 seg_606 cov_607 fo_625). Qed.
Lemma nd_601 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f9 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, QMIN, 33554425)]) t_110 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f9 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, QMIN, 33554425)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) t_109 le_602 nd_603). Qed.
Lemma nd_626 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f9 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, 33554425 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f9 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, 33554425 + 1, QMAX)]) 2%nat eq_refl emp_627). Qed.
Lemma nd_600 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) t_111 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) QRoom 33554425 t_110 t_1 nd_601 nd_626). Qed.
Lemma nd_597 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) t_112 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) QRoom 16744442 t_1 t_111 nd_598 nd_600). Qed.
Lemma fo_628 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_50 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) [(139%nat, t_112)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_50 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) 139%nat t_112 _ 2%nat ST_c_f9 eq_refl nd_597 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_50 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]))). Qed.
Lemma nd_592 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) t_113 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) 2%nat c_f9 HT_50 [(139%nat, t_112)] _ eq_refl c_593 seg_595 cov_596 fo_628). Qed.
Lemma nd_590 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) ++ [(QFlen, QMIN, 33554431)]) t_114 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) ++ [(QFlen, QMIN, 33554431)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) t_113 le_591 nd_592). Qed.
Lemma nd_650 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, QMIN, 33521658)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, QMIN, 33521658)]) 2%nat eq_refl emp_651). Qed.
Lemma rn_671 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) r_69 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) T_d2m ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_672 rn_397). Qed.
Lemma rf_673 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) [(2310%nat, r_69)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) 2310%nat r_69 _ (rsh_2) T_d2m eq_refl rn_671 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]))). Qed.
Lemma rn_667 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t10_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) r_115 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t10_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) t10_arm_nulld2m HR_32 [(2310%nat, r_69)] _ c_668 req_670 vl_97 covs_394 rf_673). Qed.
Lemma rn_665 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t10_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) r_116 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_2) ST_t10_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) _ le_666 rn_667). Qed.
Lemma rn_674 : rtree_ok 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) r_67 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_asan (rsh_1) T_d2x ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_675 rn_404). Qed.
Lemma rf_676 : rforest_ok 0%nat 400000%nat 5000%nat IT_asan HR_57 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) [(2350%nat, r_67); (1000%nat, r_116)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_57 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) 2350%nat r_67 _ (rsh_1) T_d2x eq_refl rn_674 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan HR_57 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) 1000%nat r_116 _ (rsh_2) ST_t10_arm_h1000 eq_refl rn_665 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan HR_57 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)])))). Qed.
Lemma nd_660 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t10_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) t_117 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_t10_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) 2%nat t10_arm_x2 HR_57 [(2350%nat, r_67); (1000%nat, r_116)] _ eq_refl c_661 pay_663 covs_664 rf_676). Qed.
Lemma fo_677 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_56 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) [(14%nat, t_117)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_56 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) 14%nat t_117 _ 2%nat ST_t10_cont eq_refl nd_660 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_56 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]))). Qed.
Lemma nd_655 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) t_118 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) 2%nat p10pre HT_56 [(14%nat, t_117)] _ eq_refl c_656 seg_658 cov_659 fo_677). Qed.
Lemma nd_653 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f10 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, QMIN, 67108857)]) t_119 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f10 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, QMIN, 67108857)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) t_118 le_654 nd_655). Qed.
Lemma nd_678 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f10 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, 67108857 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f10 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, 67108857 + 1, QMAX)]) 2%nat eq_refl emp_679). Qed.
Lemma nd_652 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) t_120 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) QRoom 67108857 t_119 t_1 nd_653 nd_678). Qed.
Lemma nd_649 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) t_121 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 2%nat 2%nat ST_c_f10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) QRoom 33521658 t_1 t_120 nd_650 nd_652). Qed.
Lemma fo_680 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_55 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) [(140%nat, t_121)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_55 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) 140%nat t_121 _ 2%nat ST_c_f10 eq_refl nd_649 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 2%nat HT_55 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]))). Qed.
Lemma nd_644 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) t_122 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) 2%nat c_f10 HT_55 [(140%nat, t_121)] _ eq_refl c_645 seg_647 cov_648 fo_680). Qed.
Lemma nd_642 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) ++ [(QFlen, QMIN, 67108863)]) t_123 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) ++ [(QFlen, QMIN, 67108863)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) t_122 le_643 nd_644). Qed.
Lemma nd_683 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]) t_124 = true.
Proof. exact (mtree_ok_leaf 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]) 2%nat c_r10 _ eq_refl c_684 pay_686). Qed.
Lemma nd_681 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) ++ [(QFlen, 67108863 + 1, QMAX)]) t_125 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) ++ [(QFlen, 67108863 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]) t_124 le_682 nd_683). Qed.
Lemma nd_641 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) t_126 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) QFlen 67108863 t_123 t_125 nd_642 nd_681). Qed.
Lemma fo_687 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_54 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) [(119%nat, t_126)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_54 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) 119%nat t_126 _ 2%nat ST_c_s10 eq_refl nd_641 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_54 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]))). Qed.
Lemma nd_636 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) t_127 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) 1%nat c_s10 HT_54 [(119%nat, t_126)] _ eq_refl c_637 seg_639 cov_640 fo_687). Qed.
Lemma fo_688 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_53 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) [(118%nat, t_127)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_53 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) 118%nat t_127 _ 1%nat ST_c_r9 eq_refl nd_636 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_53 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]))). Qed.
Lemma nd_631 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) t_128 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) 1%nat c_r9 HT_53 [(118%nat, t_127)] _ eq_refl c_632 seg_634 cov_635 fo_688). Qed.
Lemma nd_629 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) ++ [(QFlen, 33554431 + 1, QMAX)]) t_129 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) ++ [(QFlen, 33554431 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) t_128 le_630 nd_631). Qed.
Lemma nd_589 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) t_130 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) QFlen 33554431 t_114 t_129 nd_590 nd_629). Qed.
Lemma fo_689 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_49 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) [(117%nat, t_130)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_49 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) 117%nat t_130 _ 2%nat ST_c_s9 eq_refl nd_589 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_49 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]))). Qed.
Lemma nd_584 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) t_131 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) 1%nat c_s9 HT_49 [(117%nat, t_130)] _ eq_refl c_585 seg_587 cov_588 fo_689). Qed.
Lemma fo_690 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_48 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) [(116%nat, t_131)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_48 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) 116%nat t_131 _ 1%nat ST_c_r8 eq_refl nd_584 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_48 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]))). Qed.
Lemma nd_579 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) t_132 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) 1%nat c_r8 HT_48 [(116%nat, t_131)] _ eq_refl c_580 seg_582 cov_583 fo_690). Qed.
Lemma nd_577 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) ++ [(QFlen, 16777215 + 1, QMAX)]) t_133 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) ++ [(QFlen, 16777215 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) t_132 le_578 nd_579). Qed.
Lemma nd_537 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) t_134 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) QFlen 16777215 t_105 t_133 nd_538 nd_577). Qed.
Lemma fo_691 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_44 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) [(115%nat, t_134)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_44 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) 115%nat t_134 _ 2%nat ST_c_s8 eq_refl nd_537 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_44 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]))). Qed.
Lemma nd_532 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) t_135 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) 1%nat c_s8 HT_44 [(115%nat, t_134)] _ eq_refl c_533 seg_535 cov_536 fo_691). Qed.
Lemma fo_692 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_43 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) [(114%nat, t_135)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_43 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) 114%nat t_135 _ 1%nat ST_c_r7 eq_refl nd_532 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_43 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]))). Qed.
Lemma nd_527 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) t_136 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) 1%nat c_r7 HT_43 [(114%nat, t_135)] _ eq_refl c_528 seg_530 cov_531 fo_692). Qed.
Lemma nd_525 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) ++ [(QFlen, 8388607 + 1, QMAX)]) t_137 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) ++ [(QFlen, 8388607 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) t_136 le_526 nd_527). Qed.
Lemma nd_485 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) t_138 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) QFlen 8388607 t_96 t_137 nd_486 nd_525). Qed.
Lemma fo_693 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_39 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) [(113%nat, t_138)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_39 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) 113%nat t_138 _ 2%nat ST_c_s7 eq_refl nd_485 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_39 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]))). Qed.
Lemma nd_480 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) t_139 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) 1%nat c_s7 HT_39 [(113%nat, t_138)] _ eq_refl c_481 seg_483 cov_484 fo_693). Qed.
Lemma fo_694 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_38 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) [(112%nat, t_139)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_38 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) 112%nat t_139 _ 1%nat ST_c_r6 eq_refl nd_480 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_38 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]))). Qed.
Lemma nd_475 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) t_140 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) 1%nat c_r6 HT_38 [(112%nat, t_139)] _ eq_refl c_476 seg_478 cov_479 fo_694). Qed.
Lemma nd_473 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) ++ [(QFlen, 4194303 + 1, QMAX)]) t_141 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) ++ [(QFlen, 4194303 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) t_140 le_474 nd_475). Qed.
Lemma nd_433 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) t_142 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) QFlen 4194303 t_87 t_141 nd_434 nd_473). Qed.
Lemma fo_695 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_34 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) [(111%nat, t_142)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_34 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) 111%nat t_142 _ 2%nat ST_c_s6 eq_refl nd_433 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_34 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]))). Qed.
Lemma nd_428 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) t_143 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) 1%nat c_s6 HT_34 [(111%nat, t_142)] _ eq_refl c_429 seg_431 cov_432 fo_695). Qed.
Lemma fo_696 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_33 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) [(110%nat, t_143)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_33 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) 110%nat t_143 _ 1%nat ST_c_r5 eq_refl nd_428 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_33 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]))). Qed.
Lemma nd_423 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) t_144 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) 1%nat c_r5 HT_33 [(110%nat, t_143)] _ eq_refl c_424 seg_426 cov_427 fo_696). Qed.
Lemma nd_421 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) ++ [(QFlen, 2097151 + 1, QMAX)]) t_145 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) ++ [(QFlen, 2097151 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) t_144 le_422 nd_423). Qed.
Lemma nd_364 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) t_146 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) QFlen 2097151 t_78 t_145 nd_365 nd_421). Qed.
Lemma fo_697 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_27 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) [(109%nat, t_146)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_27 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) 109%nat t_146 _ 2%nat ST_c_s5 eq_refl nd_364 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_27 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]))). Qed.
Lemma nd_359 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) t_147 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) 1%nat c_s5 HT_27 [(109%nat, t_146)] _ eq_refl c_360 seg_362 cov_363 fo_697). Qed.
Lemma fo_698 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_26 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) [(108%nat, t_147)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_26 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) 108%nat t_147 _ 1%nat ST_c_r4 eq_refl nd_359 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_26 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]))). Qed.
Lemma nd_354 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) t_148 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) 1%nat c_r4 HT_26 [(108%nat, t_147)] _ eq_refl c_355 seg_357 cov_358 fo_698). Qed.
Lemma nd_352 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) ++ [(QFlen, 1048575 + 1, QMAX)]) t_149 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) ++ [(QFlen, 1048575 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) t_148 le_353 nd_354). Qed.
Lemma nd_293 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) t_150 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) QFlen 1048575 t_63 t_149 nd_294 nd_352). Qed.
Lemma fo_699 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_20 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) [(107%nat, t_150)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_20 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) 107%nat t_150 _ 2%nat ST_c_s4 eq_refl nd_293 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_20 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]))). Qed.
Lemma nd_288 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) t_151 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) 1%nat c_s4 HT_20 [(107%nat, t_150)] _ eq_refl c_289 seg_291 cov_292 fo_699). Qed.
Lemma fo_700 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_19 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) [(106%nat, t_151)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_19 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) 106%nat t_151 _ 1%nat ST_c_r3 eq_refl nd_288 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_19 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]))). Qed.
Lemma nd_283 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) t_152 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) 1%nat c_r3 HT_19 [(106%nat, t_151)] _ eq_refl c_284 seg_286 cov_287 fo_700). Qed.
Lemma nd_281 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) ++ [(QFlen, 524287 + 1, QMAX)]) t_153 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) ++ [(QFlen, 524287 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) t_152 le_282 nd_283). Qed.
Lemma nd_244 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) t_154 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) QFlen 524287 t_48 t_153 nd_245 nd_281). Qed.
Lemma fo_701 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_15 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) [(105%nat, t_154)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_15 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) 105%nat t_154 _ 2%nat ST_c_s3 eq_refl nd_244 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_15 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]))). Qed.
Lemma nd_239 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) t_155 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) 1%nat c_s3 HT_15 [(105%nat, t_154)] _ eq_refl c_240 seg_242 cov_243 fo_701). Qed.
Lemma fo_702 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_14 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) [(104%nat, t_155)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_14 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) 104%nat t_155 _ 1%nat ST_c_r2 eq_refl nd_239 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_14 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]))). Qed.
Lemma nd_234 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) t_156 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) 1%nat c_r2 HT_14 [(104%nat, t_155)] _ eq_refl c_235 seg_237 cov_238 fo_702). Qed.
Lemma nd_232 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) ++ [(QFlen, 262143 + 1, QMAX)]) t_157 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) ++ [(QFlen, 262143 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) t_156 le_233 nd_234). Qed.
Lemma nd_192 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) t_158 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) QFlen 262143 t_39 t_157 nd_193 nd_232). Qed.
Lemma fo_703 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) [(103%nat, t_158)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) 103%nat t_158 _ 2%nat ST_c_s2 eq_refl nd_192 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]))). Qed.
Lemma nd_187 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) t_159 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat ST_c_r1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) 1%nat c_s2 HT_10 [(103%nat, t_158)] _ eq_refl c_188 seg_190 cov_191 fo_703). Qed.
Lemma fo_704 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) [(102%nat, t_159)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) 102%nat t_159 _ 1%nat ST_c_r1 eq_refl nd_187 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]))). Qed.
Lemma nd_182 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) t_160 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) 1%nat c_r1 HT_9 [(102%nat, t_159)] _ eq_refl c_183 seg_185 cov_186 fo_704). Qed.
Lemma nd_180 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) ++ [(QFlen, 131071 + 1, QMAX)]) t_161 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) ++ [(QFlen, 131071 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) t_160 le_181 nd_182). Qed.
Lemma nd_65 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) t_162 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_asan 1%nat 2%nat ST_c_s1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) QFlen 131071 t_30 t_161 nd_66 nd_180). Qed.
Lemma fo_705 : mforest_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) [(101%nat, t_162)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) 101%nat t_162 _ 2%nat ST_c_s1 eq_refl nd_65 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_asan 1%nat HT_1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]))). Qed.
Lemma nd_60 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat HG1_s ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) t_163 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat HG1_s ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) 1%nat c_s1 HT_1 [(101%nat, t_162)] _ eq_refl c_61 seg_63 cov_64 fo_705). Qed.
Lemma nd_58 : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat HG1_s ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) t_164 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat HG1_s ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) t_163 le_59 nd_60). Qed.
Definition TW1 : mtree := t_164.
Lemma TW1_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat HG1_s ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) TW1 = true.
Proof. exact nd_58. Qed.
