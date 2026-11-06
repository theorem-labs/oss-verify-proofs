(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB  ItabBoth W0BStates1 W1BSt1 W1BSt2 W1BSt3 W1BSt4 W1BSt5 W1BSt6 W1BSt7 W1BSt8 W1BSt9 W1BSt10 W1BSt11 W1BSt12 W1BSt13 W1BSt14 W1BPlans Main5W1BothDefs Main5W1BothCerts0 Main5W1BothCerts1 Main5W1BothCerts2 Main5W1BothCerts3 Main5W1BothCerts4 Main5W1BothCerts5 Main5W1BothCerts6 Main5W1BothCerts7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition t_1 : mtree := (MEmpty 2%nat).
Definition r_2 : rtree := (RLeaf ts_g1b).
Definition r_3 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_2).
Definition r_4 : rtree := (RLeaf nl_w1n).
Definition r_5 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_4).
Definition r_6 : rtree := (RPreS nf_w1n_hj HR_5 [(2530%nat, r_5)]).
Definition r_7 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_6).
Definition r_8 : rtree := (RPreS nf_w1n_1001_a29 HR_5 [(2530%nat, r_5)]).
Definition r_9 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_8).
Definition r_10 : rtree := (RPreS nf_w1n_1003 HR_5 [(2530%nat, r_5)]).
Definition r_11 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_10).
Definition t_12 : mtree := (MPreS 2%nat tb1_a29g1b HR_4 [(2520%nat, r_3); (1001%nat, r_9); (1003%nat, r_11)]).
Definition r_13 : rtree := (RPreS nf_w1n_1001_a30 HR_5 [(2530%nat, r_5)]).
Definition r_14 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_13).
Definition t_15 : mtree := (MPreS 2%nat tb1_a30g1b HR_6 [(2520%nat, r_3); (1001%nat, r_14); (1003%nat, r_11)]).
Definition r_16 : rtree := (RLeaf ts_g5b).
Definition r_17 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) r_16).
Definition r_18 : rtree := (RLeaf tb1_as_n1000).
Definition r_19 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_18).
Definition t_20 : mtree := (MPreS 2%nat tb1_asd5b HR_7 [(2600%nat, r_17); (1000%nat, r_19)]).
Definition t_21 : mtree := (MCase (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 64512 t_15 t_20).
Definition t_22 : mtree := (MCase (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128 t_12 t_21).
Definition t_23 : mtree := (MPre 2%nat pb1 HT_3 [(14%nat, t_22)]).
Definition t_24 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_23).
Definition t_25 : mtree := (MSplit QRoom 131065 t_24 t_1).
Definition t_26 : mtree := (MSplit QRoom 32762 t_1 t_25).
Definition t_27 : mtree := (MPre 2%nat cb_f1 HT_2 [(131%nat, t_26)]).
Definition t_28 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) t_27).
Definition r_29 : rtree := (RLeaf tb2_arm_n1000).
Definition r_30 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) r_29).
Definition t_31 : mtree := (MPreS 2%nat tb2_armd5b HR_12 [(2600%nat, r_17); (1000%nat, r_30)]).
Definition t_32 : mtree := (MPre 2%nat pb2pre HT_11 [(14%nat, t_31)]).
Definition t_33 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) t_32).
Definition t_34 : mtree := (MSplit QRoom 262137 t_33 t_1).
Definition t_35 : mtree := (MSplit QRoom 98298 t_1 t_34).
Definition t_36 : mtree := (MPre 2%nat cb_f2 HT_10 [(132%nat, t_35)]).
Definition t_37 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) t_36).
Definition r_38 : rtree := (RLeaf tb3_arm_n1000).
Definition r_39 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) r_38).
Definition t_40 : mtree := (MPreS 2%nat tb3_armd5b HR_17 [(2600%nat, r_17); (1000%nat, r_39)]).
Definition t_41 : mtree := (MPre 2%nat pb3pre HT_16 [(14%nat, t_40)]).
Definition t_42 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) t_41).
Definition t_43 : mtree := (MSplit QRoom 524281 t_42 t_1).
Definition t_44 : mtree := (MSplit QRoom 229370 t_1 t_43).
Definition t_45 : mtree := (MPre 2%nat cb_f3 HT_15 [(133%nat, t_44)]).
Definition t_46 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) t_45).
Definition r_47 : rtree := (RLeaf tb4_a_n1000).
Definition r_48 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) r_47).
Definition t_49 : mtree := (MPreS 2%nat tb4_ad5b HR_22 [(2600%nat, r_17); (1000%nat, r_48)]).
Definition r_50 : rtree := (RLeaf tb4_b_n1000).
Definition r_51 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) r_50).
Definition t_52 : mtree := (MPreS 2%nat tb4_bd5b HR_23 [(2600%nat, r_17); (1000%nat, r_51)]).
Definition t_53 : mtree := (MCase (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 524287 t_49 t_52).
Definition t_54 : mtree := (MPre 2%nat pb4 HT_21 [(14%nat, t_53)]).
Definition t_55 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) t_54).
Definition t_56 : mtree := (MSplit QRoom 1048569 t_55 t_1).
Definition t_57 : mtree := (MSplit QRoom 491514 t_1 t_56).
Definition t_58 : mtree := (MPre 2%nat cb_f4 HT_20 [(134%nat, t_57)]).
Definition t_59 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) t_58).
Definition r_60 : rtree := (RLeaf ts_d2xb5s).
Definition r_61 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) r_60).
Definition r_62 : rtree := (RPreS armxb HR_29 [(900%nat, r_61)]).
Definition r_63 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) r_62).
Definition r_64 : rtree := (RLeaf nl_d2mb).
Definition r_65 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) r_64).
Definition r_66 : rtree := (RPreS tb5_arm_nulld2mb HR_30 [(2310%nat, r_65)]).
Definition r_67 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) r_66).
Definition t_68 : mtree := (MPreS 2%nat tb5_arm_x2 HR_28 [(2350%nat, r_63); (1000%nat, r_67)]).
Definition t_69 : mtree := (MPre 2%nat pb5pre HT_27 [(14%nat, t_68)]).
Definition t_70 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) t_69).
Definition t_71 : mtree := (MSplit QRoom 2097145 t_70 t_1).
Definition t_72 : mtree := (MSplit QRoom 1015802 t_1 t_71).
Definition t_73 : mtree := (MPre 2%nat cb_f5 HT_26 [(135%nat, t_72)]).
Definition t_74 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) t_73).
Definition r_75 : rtree := (RPreS tb6_arm_nulld2mb HR_30 [(2310%nat, r_65)]).
Definition r_76 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) r_75).
Definition t_77 : mtree := (MPreS 2%nat tb6_arm_x2 HR_35 [(2350%nat, r_63); (1000%nat, r_76)]).
Definition t_78 : mtree := (MPre 2%nat pb6pre HT_34 [(14%nat, t_77)]).
Definition t_79 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) t_78).
Definition t_80 : mtree := (MSplit QRoom 4194297 t_79 t_1).
Definition t_81 : mtree := (MSplit QRoom 2064378 t_1 t_80).
Definition t_82 : mtree := (MPre 2%nat cb_f6 HT_33 [(136%nat, t_81)]).
Definition t_83 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) t_82).
Definition r_84 : rtree := (RPreS tb7_arm_nulld2mb HR_30 [(2310%nat, r_65)]).
Definition r_85 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) r_84).
Definition t_86 : mtree := (MPreS 2%nat tb7_arm_x2 HR_40 [(2350%nat, r_63); (1000%nat, r_85)]).
Definition t_87 : mtree := (MPre 2%nat pb7pre HT_39 [(14%nat, t_86)]).
Definition t_88 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) t_87).
Definition t_89 : mtree := (MSplit QRoom 8388601 t_88 t_1).
Definition t_90 : mtree := (MSplit QRoom 4161530 t_1 t_89).
Definition t_91 : mtree := (MPre 2%nat cb_f7 HT_38 [(137%nat, t_90)]).
Definition t_92 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) t_91).
Definition r_93 : rtree := (RPreS tb8_arm_nulld2mb HR_30 [(2310%nat, r_65)]).
Definition r_94 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) r_93).
Definition t_95 : mtree := (MPreS 2%nat tb8_arm_x2 HR_45 [(2350%nat, r_63); (1000%nat, r_94)]).
Definition t_96 : mtree := (MPre 2%nat pb8pre HT_44 [(14%nat, t_95)]).
Definition t_97 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) t_96).
Definition t_98 : mtree := (MSplit QRoom 16777209 t_97 t_1).
Definition t_99 : mtree := (MSplit QRoom 8355834 t_1 t_98).
Definition t_100 : mtree := (MPre 2%nat cb_f8 HT_43 [(138%nat, t_99)]).
Definition t_101 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) t_100).
Definition r_102 : rtree := (RPreS tb9_arm_nulld2mb HR_30 [(2310%nat, r_65)]).
Definition r_103 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) r_102).
Definition t_104 : mtree := (MPreS 2%nat tb9_arm_x2 HR_50 [(2350%nat, r_63); (1000%nat, r_103)]).
Definition t_105 : mtree := (MPre 2%nat pb9pre HT_49 [(14%nat, t_104)]).
Definition t_106 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) t_105).
Definition t_107 : mtree := (MSplit QRoom 33554425 t_106 t_1).
Definition t_108 : mtree := (MSplit QRoom 16744442 t_1 t_107).
Definition t_109 : mtree := (MPre 2%nat cb_f9 HT_48 [(139%nat, t_108)]).
Definition t_110 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) t_109).
Definition r_111 : rtree := (RPreS tb10_arm_nulld2mb HR_30 [(2310%nat, r_65)]).
Definition r_112 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) r_111).
Definition t_113 : mtree := (MPreS 2%nat tb10_arm_x2 HR_55 [(2350%nat, r_63); (1000%nat, r_112)]).
Definition t_114 : mtree := (MPre 2%nat pb10pre HT_54 [(14%nat, t_113)]).
Definition t_115 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) t_114).
Definition t_116 : mtree := (MSplit QRoom 67108857 t_115 t_1).
Definition t_117 : mtree := (MSplit QRoom 33521658 t_1 t_116).
Definition t_118 : mtree := (MPre 2%nat cb_f10 HT_53 [(140%nat, t_117)]).
Definition t_119 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) t_118).
Definition t_120 : mtree := (MLeaf 2%nat cb_r10).
Definition t_121 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]) t_120).
Definition t_122 : mtree := (MSplit QFlen 67108863 t_119 t_121).
Definition t_123 : mtree := (MPre 1%nat cb_s10 HT_52 [(119%nat, t_122)]).
Definition t_124 : mtree := (MPre 1%nat cb_r9 HT_51 [(118%nat, t_123)]).
Definition t_125 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) t_124).
Definition t_126 : mtree := (MSplit QFlen 33554431 t_110 t_125).
Definition t_127 : mtree := (MPre 1%nat cb_s9 HT_47 [(117%nat, t_126)]).
Definition t_128 : mtree := (MPre 1%nat cb_r8 HT_46 [(116%nat, t_127)]).
Definition t_129 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) t_128).
Definition t_130 : mtree := (MSplit QFlen 16777215 t_101 t_129).
Definition t_131 : mtree := (MPre 1%nat cb_s8 HT_42 [(115%nat, t_130)]).
Definition t_132 : mtree := (MPre 1%nat cb_r7 HT_41 [(114%nat, t_131)]).
Definition t_133 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) t_132).
Definition t_134 : mtree := (MSplit QFlen 8388607 t_92 t_133).
Definition t_135 : mtree := (MPre 1%nat cb_s7 HT_37 [(113%nat, t_134)]).
Definition t_136 : mtree := (MPre 1%nat cb_r6 HT_36 [(112%nat, t_135)]).
Definition t_137 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) t_136).
Definition t_138 : mtree := (MSplit QFlen 4194303 t_83 t_137).
Definition t_139 : mtree := (MPre 1%nat cb_s6 HT_32 [(111%nat, t_138)]).
Definition t_140 : mtree := (MPre 1%nat cb_r5 HT_31 [(110%nat, t_139)]).
Definition t_141 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) t_140).
Definition t_142 : mtree := (MSplit QFlen 2097151 t_74 t_141).
Definition t_143 : mtree := (MPre 1%nat cb_s5 HT_25 [(109%nat, t_142)]).
Definition t_144 : mtree := (MPre 1%nat cb_r4 HT_24 [(108%nat, t_143)]).
Definition t_145 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) t_144).
Definition t_146 : mtree := (MSplit QFlen 1048575 t_59 t_145).
Definition t_147 : mtree := (MPre 1%nat cb_s4 HT_19 [(107%nat, t_146)]).
Definition t_148 : mtree := (MPre 1%nat cb_r3 HT_18 [(106%nat, t_147)]).
Definition t_149 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) t_148).
Definition t_150 : mtree := (MSplit QFlen 524287 t_46 t_149).
Definition t_151 : mtree := (MPre 1%nat cb_s3 HT_14 [(105%nat, t_150)]).
Definition t_152 : mtree := (MPre 1%nat cb_r2 HT_13 [(104%nat, t_151)]).
Definition t_153 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) t_152).
Definition t_154 : mtree := (MSplit QFlen 262143 t_37 t_153).
Definition t_155 : mtree := (MPre 1%nat cb_s2 HT_9 [(103%nat, t_154)]).
Definition t_156 : mtree := (MPre 1%nat cb_r1 HT_8 [(102%nat, t_155)]).
Definition t_157 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) t_156).
Definition t_158 : mtree := (MSplit QFlen 131071 t_28 t_157).
Definition t_159 : mtree := (MPre 1%nat cb_s1 HT_1 [(101%nat, t_158)]).
Definition t_160 : mtree := (MClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) t_159).
Lemma le_57 : class_le ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_61 : class_seg_ok (lv_of HT_1) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) s_60 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_62 : mcover HT_1 [(101%nat, t_158)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_65 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) ++ [(QFlen, QMIN, 131071)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_69 : class_seg_ok (lv_of HT_2) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) s_68 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_70 : mcover HT_2 [(131%nat, t_26)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_73 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, QMIN, 32762)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_76 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_80 : class_seg_ok (lv_of HT_3) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) s_79 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_81 : mcover HT_3 [(14%nat, t_22)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma lsh_83 : lshape_eqb (lvl_shape t_12) (lvl_shape t_21) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_87 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) (subst_holes (rs_of HR_4) s_86) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_88 : mcoverS HR_4 [(2520%nat, r_3); (1001%nat, r_9); (1003%nat, r_11)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_90 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_94 : shape_eqb (subst_holes (rs_of HR_5) s_93) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma vl_95 : shape_vars_lt NX0 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_96 : mcoverS HR_5 [(2530%nat, r_5)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_98 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_102 : shape_eqb s_101 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_108 : shape_eqb (subst_holes (rs_of HR_5) s_107) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_114 : shape_eqb (subst_holes (rs_of HR_5) s_113) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_120 : shape_eqb s_119 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma vl_121 : shape_vars_lt NX0 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma lsh_124 : lshape_eqb (lvl_shape t_15) (lvl_shape t_20) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_128 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) (subst_holes (rs_of HR_6) s_127) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_129 : mcoverS HR_6 [(2520%nat, r_3); (1001%nat, r_14); (1003%nat, r_11)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_134 : shape_eqb (subst_holes (rs_of HR_5) s_133) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_140 : shape_eqb (subst_holes (rs_of HR_5) s_139) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_146 : shape_eqb (subst_holes (rs_of HR_5) s_145) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_152 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) (subst_holes (rs_of HR_7) s_151) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_153 : mcoverS HR_7 [(2600%nat, r_17); (1000%nat, r_19)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_158 : shape_eqb s_157 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_160 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_164 : shape_eqb s_163 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_168 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, 131065 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_171 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) ++ [(QFlen, 131071 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_175 : class_seg_ok (lv_of HT_8) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) s_174 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_176 : mcover HT_8 [(102%nat, t_155)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_180 : class_seg_ok (lv_of HT_9) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) s_179 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_181 : mcover HT_9 [(103%nat, t_154)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_184 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) ++ [(QFlen, QMIN, 262143)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_188 : class_seg_ok (lv_of HT_10) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) s_187 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_189 : mcover HT_10 [(132%nat, t_35)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_192 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, QMIN, 98298)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_195 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, QMIN, 262137)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_199 : class_seg_ok (lv_of HT_11) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) s_198 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_200 : mcover HT_11 [(14%nat, t_31)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_204 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) (subst_holes (rs_of HR_12) s_203) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_205 : mcoverS HR_12 [(2600%nat, r_17); (1000%nat, r_30)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_207 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_211 : shape_eqb s_210 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_213 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_217 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, 262137 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_220 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) ++ [(QFlen, 262143 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_224 : class_seg_ok (lv_of HT_13) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) s_223 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_225 : mcover HT_13 [(104%nat, t_151)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_229 : class_seg_ok (lv_of HT_14) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) s_228 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_230 : mcover HT_14 [(105%nat, t_150)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_233 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) ++ [(QFlen, QMIN, 524287)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_237 : class_seg_ok (lv_of HT_15) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) s_236 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_238 : mcover HT_15 [(133%nat, t_44)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_241 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, QMIN, 229370)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_244 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, QMIN, 524281)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_248 : class_seg_ok (lv_of HT_16) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) s_247 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_249 : mcover HT_16 [(14%nat, t_40)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_253 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) (subst_holes (rs_of HR_17) s_252) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_254 : mcoverS HR_17 [(2600%nat, r_17); (1000%nat, r_39)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_256 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_260 : shape_eqb s_259 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_262 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_266 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, 524281 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_269 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) ++ [(QFlen, 524287 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_273 : class_seg_ok (lv_of HT_18) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) s_272 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_274 : mcover HT_18 [(106%nat, t_147)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_278 : class_seg_ok (lv_of HT_19) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) s_277 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_279 : mcover HT_19 [(107%nat, t_146)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_282 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) ++ [(QFlen, QMIN, 1048575)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_286 : class_seg_ok (lv_of HT_20) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) s_285 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_287 : mcover HT_20 [(134%nat, t_57)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_290 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, QMIN, 491514)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_293 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, QMIN, 1048569)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_297 : class_seg_ok (lv_of HT_21) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) s_296 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_298 : mcover HT_21 [(14%nat, t_53)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma lsh_300 : lshape_eqb (lvl_shape t_49) (lvl_shape t_52) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_304 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) (subst_holes (rs_of HR_22) s_303) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_305 : mcoverS HR_22 [(2600%nat, r_17); (1000%nat, r_48)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_307 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_311 : shape_eqb s_310 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_313 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_318 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) (subst_holes (rs_of HR_23) s_317) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_319 : mcoverS HR_23 [(2600%nat, r_17); (1000%nat, r_51)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_324 : shape_eqb s_323 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_328 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, 1048569 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_331 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) ++ [(QFlen, 1048575 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_335 : class_seg_ok (lv_of HT_24) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) s_334 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_336 : mcover HT_24 [(108%nat, t_143)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_340 : class_seg_ok (lv_of HT_25) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) s_339 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_341 : mcover HT_25 [(109%nat, t_142)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_344 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) ++ [(QFlen, QMIN, 2097151)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_348 : class_seg_ok (lv_of HT_26) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) s_347 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_349 : mcover HT_26 [(135%nat, t_72)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_352 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, QMIN, 1015802)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_355 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, QMIN, 2097145)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_359 : class_seg_ok (lv_of HT_27) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) s_358 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_360 : mcover HT_27 [(14%nat, t_68)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_364 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) (subst_holes (rs_of HR_28) s_363) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_365 : mcoverS HR_28 [(2350%nat, r_63); (1000%nat, r_67)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_367 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_371 : shape_eqb (subst_holes (rs_of HR_30) s_370) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_372 : mcoverS HR_30 [(2310%nat, r_65)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_374 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_378 : shape_eqb s_377 (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_381 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_385 : shape_eqb (subst_holes (rs_of HR_29) s_384) (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_386 : mcoverS HR_29 [(900%nat, r_61)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_388 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma eq_392 : shape_eqb s_391 (rsh_1) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_397 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, 2097145 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_400 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) ++ [(QFlen, 2097151 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_404 : class_seg_ok (lv_of HT_31) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) s_403 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_405 : mcover HT_31 [(110%nat, t_139)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_409 : class_seg_ok (lv_of HT_32) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) s_408 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_410 : mcover HT_32 [(111%nat, t_138)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_413 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) ++ [(QFlen, QMIN, 4194303)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_417 : class_seg_ok (lv_of HT_33) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) s_416 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_418 : mcover HT_33 [(136%nat, t_81)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_421 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, QMIN, 2064378)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_424 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, QMIN, 4194297)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_428 : class_seg_ok (lv_of HT_34) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) s_427 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_429 : mcover HT_34 [(14%nat, t_77)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_433 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) (subst_holes (rs_of HR_35) s_432) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_434 : mcoverS HR_35 [(2350%nat, r_63); (1000%nat, r_76)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_436 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_440 : shape_eqb (subst_holes (rs_of HR_30) s_439) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_442 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_445 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_449 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, 4194297 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_452 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) ++ [(QFlen, 4194303 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_456 : class_seg_ok (lv_of HT_36) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) s_455 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_457 : mcover HT_36 [(112%nat, t_135)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_461 : class_seg_ok (lv_of HT_37) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) s_460 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_462 : mcover HT_37 [(113%nat, t_134)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_465 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) ++ [(QFlen, QMIN, 8388607)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_469 : class_seg_ok (lv_of HT_38) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) s_468 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_470 : mcover HT_38 [(137%nat, t_90)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_473 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, QMIN, 4161530)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_476 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, QMIN, 8388601)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_480 : class_seg_ok (lv_of HT_39) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) s_479 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_481 : mcover HT_39 [(14%nat, t_86)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_485 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) (subst_holes (rs_of HR_40) s_484) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_486 : mcoverS HR_40 [(2350%nat, r_63); (1000%nat, r_85)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_488 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_492 : shape_eqb (subst_holes (rs_of HR_30) s_491) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_494 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_497 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_501 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, 8388601 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_504 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) ++ [(QFlen, 8388607 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_508 : class_seg_ok (lv_of HT_41) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) s_507 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_509 : mcover HT_41 [(114%nat, t_131)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_513 : class_seg_ok (lv_of HT_42) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) s_512 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_514 : mcover HT_42 [(115%nat, t_130)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_517 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) ++ [(QFlen, QMIN, 16777215)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_521 : class_seg_ok (lv_of HT_43) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) s_520 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_522 : mcover HT_43 [(138%nat, t_99)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_525 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, QMIN, 8355834)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_528 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, QMIN, 16777209)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_532 : class_seg_ok (lv_of HT_44) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) s_531 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_533 : mcover HT_44 [(14%nat, t_95)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_537 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) (subst_holes (rs_of HR_45) s_536) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_538 : mcoverS HR_45 [(2350%nat, r_63); (1000%nat, r_94)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_540 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_544 : shape_eqb (subst_holes (rs_of HR_30) s_543) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_546 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_549 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_553 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, 16777209 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_556 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) ++ [(QFlen, 16777215 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_560 : class_seg_ok (lv_of HT_46) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) s_559 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_561 : mcover HT_46 [(116%nat, t_127)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_565 : class_seg_ok (lv_of HT_47) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) s_564 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_566 : mcover HT_47 [(117%nat, t_126)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_569 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) ++ [(QFlen, QMIN, 33554431)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_573 : class_seg_ok (lv_of HT_48) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) s_572 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_574 : mcover HT_48 [(139%nat, t_108)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_577 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, QMIN, 16744442)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_580 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, QMIN, 33554425)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_584 : class_seg_ok (lv_of HT_49) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) s_583 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_585 : mcover HT_49 [(14%nat, t_104)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_589 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) (subst_holes (rs_of HR_50) s_588) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_590 : mcoverS HR_50 [(2350%nat, r_63); (1000%nat, r_103)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_592 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_596 : shape_eqb (subst_holes (rs_of HR_30) s_595) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_598 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_601 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_605 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, 33554425 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_608 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) ++ [(QFlen, 33554431 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_612 : class_seg_ok (lv_of HT_51) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) s_611 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_613 : mcover HT_51 [(118%nat, t_123)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_617 : class_seg_ok (lv_of HT_52) 1%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) s_616 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_618 : mcover HT_52 [(119%nat, t_122)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_621 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) ++ [(QFlen, QMIN, 67108863)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_625 : class_seg_ok (lv_of HT_53) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) s_624 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_626 : mcover HT_53 [(140%nat, t_117)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_629 : class_empty (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, QMIN, 33521658)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_632 : class_le ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, QMIN, 67108857)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma seg_636 : class_seg_ok (lv_of HT_54) 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) s_635 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma cov_637 : mcover HT_54 [(14%nat, t_113)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_641 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) (subst_holes (rs_of HR_55) s_640) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma covs_642 : mcoverS HR_55 [(2350%nat, r_63); (1000%nat, r_112)] = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_644 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma req_648 : shape_eqb (subst_holes (rs_of HR_30) s_647) (rsh_2) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_650 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_653 : class_le ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma emp_657 : class_empty ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, 67108857 + 1, QMAX)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma le_660 : class_le (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) ++ [(QFlen, 67108863 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]) = true.
Proof. vm_compute; reflexivity. Qed.
Lemma pay_664 : class_pay_ok 2%nat ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]) s_663 = true.
Proof. vm_compute; reflexivity. Qed.
Lemma nd_72 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, QMIN, 32762)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, QMIN, 32762)]) 2%nat eq_refl emp_73). Qed.
Lemma rn_99 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_w1n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_4 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_w1n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) nl_w1n _ c_100 eq_102 vl_95). Qed.
Lemma rn_97 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_w1n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_5 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_w1n ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) _ le_98 rn_99). Qed.
Lemma rf_103 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(2530%nat, r_5)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2530%nat r_5 _ (rsh_2) T_w1n eq_refl rn_97 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma rn_91 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a29_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_10 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a29_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) nf_w1n_1003 HR_5 [(2530%nat, r_5)] _ c_92 req_94 vl_95 covs_96 rf_103). Qed.
Lemma rn_89 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a29_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) r_11 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a29_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) _ le_90 rn_91). Qed.
Lemma rf_109 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(2530%nat, r_5)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2530%nat r_5 _ (rsh_2) T_w1n eq_refl rn_97 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma rn_105 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a29_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_8 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a29_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) nf_w1n_1001_a29 HR_5 [(2530%nat, r_5)] _ c_106 req_108 vl_95 covs_96 rf_109). Qed.
Lemma rn_104 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a29_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) r_9 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a29_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) _ le_90 rn_105). Qed.
Lemma rf_115 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(2530%nat, r_5)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2530%nat r_5 _ (rsh_2) T_w1n eq_refl rn_97 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma rn_117 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_g1b ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_2 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_g1b ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ts_g1b _ c_118 eq_120 vl_121). Qed.
Lemma rn_116 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_g1b ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) r_3 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_g1b ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) _ le_90 rn_117). Qed.
Lemma rf_122 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) [(2520%nat, r_3); (1001%nat, r_9); (1003%nat, r_11)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 2520%nat r_3 _ (rsh_1) T_g1b eq_refl rn_116 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 1001%nat r_9 _ (rsh_2) ST_tb1_a29_h1001 eq_refl rn_104 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 1003%nat r_11 _ (rsh_2) ST_tb1_a29_h1003 eq_refl rn_89 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]))))). Qed.
Lemma nd_84 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat (mcase_lo ST_tb1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_12 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat (mcase_lo ST_tb1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 2%nat tb1_a29g1b HR_4 [(2520%nat, r_3); (1001%nat, r_9); (1003%nat, r_11)] _ eq_refl c_85 pay_87 covs_88 rf_122). Qed.
Lemma rf_135 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(2530%nat, r_5)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2530%nat r_5 _ (rsh_2) T_w1n eq_refl rn_97 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma rn_131 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a30_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_10 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a30_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) nf_w1n_1003 HR_5 [(2530%nat, r_5)] _ c_132 req_134 vl_95 covs_96 rf_135). Qed.
Lemma rn_130 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a30_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) r_11 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a30_h1003 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) _ le_90 rn_131). Qed.
Lemma rf_141 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(2530%nat, r_5)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2530%nat r_5 _ (rsh_2) T_w1n eq_refl rn_97 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma rn_137 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a30_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_13 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a30_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) nf_w1n_1001_a30 HR_5 [(2530%nat, r_5)] _ c_138 req_140 vl_95 covs_96 rf_141). Qed.
Lemma rn_136 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a30_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) r_14 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_a30_h1001 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) _ le_90 rn_137). Qed.
Lemma rf_147 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(2530%nat, r_5)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2530%nat r_5 _ (rsh_2) T_w1n eq_refl rn_97 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma rf_148 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) [(2520%nat, r_3); (1001%nat, r_14); (1003%nat, r_11)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 2520%nat r_3 _ (rsh_1) T_g1b eq_refl rn_116 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 1001%nat r_14 _ (rsh_2) ST_tb1_a30_h1001 eq_refl rn_136 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 1003%nat r_11 _ (rsh_2) ST_tb1_a30_h1003 eq_refl rn_130 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]))))). Qed.
Lemma nd_125 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat (mcase_lo (mcase_hi ST_tb1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 64512) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_15 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat (mcase_lo (mcase_hi ST_tb1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 64512) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 2%nat tb1_a30g1b HR_6 [(2520%nat, r_3); (1001%nat, r_14); (1003%nat, r_11)] _ eq_refl c_126 pay_128 covs_129 rf_148). Qed.
Lemma rn_155 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_as_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) r_18 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_as_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) tb1_as_n1000 _ c_156 eq_158 vl_95). Qed.
Lemma rn_154 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_as_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) r_19 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb1_as_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) _ le_90 rn_155). Qed.
Lemma rn_161 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_g5b ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) r_16 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_g5b ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) ts_g5b _ c_162 eq_164 vl_121). Qed.
Lemma rn_159 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_g5b ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) r_17 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_g5b ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) _ le_160 rn_161). Qed.
Lemma rf_165 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) [(2600%nat, r_17); (1000%nat, r_19)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 2600%nat r_17 _ (rsh_1) T_g5b eq_refl rn_159 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 1000%nat r_19 _ (rsh_2) ST_tb1_as_h1000 eq_refl rn_154 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)])))). Qed.
Lemma nd_149 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat (mcase_hi (mcase_hi ST_tb1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 64512) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_20 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat (mcase_hi (mcase_hi ST_tb1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 64512) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 2%nat tb1_asd5b HR_7 [(2600%nat, r_17); (1000%nat, r_19)] _ eq_refl c_150 pay_152 covs_153 rf_165). Qed.
Lemma nd_123 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat (mcase_hi ST_tb1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_21 = true.
Proof. exact (mtree_ok_case 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat (mcase_hi ST_tb1_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 64512 t_15 t_20 lsh_124 nd_125 nd_149). Qed.
Lemma nd_82 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb1_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_22 = true.
Proof. exact (mtree_ok_case 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb1_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 48128 t_12 t_21 lsh_83 nd_84 nd_123). Qed.
Lemma fo_166 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) [(14%nat, t_22)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 14%nat t_22 _ 2%nat ST_tb1_cont eq_refl nd_82 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]))). Qed.
Lemma nd_77 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_23 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) 2%nat pb1 HT_3 [(14%nat, t_22)] _ eq_refl c_78 seg_80 cov_81 fo_166). Qed.
Lemma nd_75 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f1 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) t_24 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f1 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, QMIN, 131065)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071); (QRoom, 32763, 131065)]) t_23 le_76 nd_77). Qed.
Lemma nd_167 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f1 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, 131065 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f1 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) ++ [(QRoom, 131065 + 1, QMAX)]) 2%nat eq_refl emp_168). Qed.
Lemma nd_74 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) t_25 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) ++ [(QRoom, 32762 + 1, QMAX)]) QRoom 131065 t_24 t_1 nd_75 nd_167). Qed.
Lemma nd_71 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) t_26 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) QRoom 32762 t_1 t_25 nd_72 nd_74). Qed.
Lemma fo_169 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) [(131%nat, t_26)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 131%nat t_26 _ 2%nat ST_cb_f1 eq_refl nd_71 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]))). Qed.
Lemma nd_66 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) t_27 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) 2%nat cb_f1 HT_2 [(131%nat, t_26)] _ eq_refl c_67 seg_69 cov_70 fo_169). Qed.
Lemma nd_64 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) ++ [(QFlen, QMIN, 131071)]) t_28 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) ++ [(QFlen, QMIN, 131071)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 131071)]) t_27 le_65 nd_66). Qed.
Lemma nd_191 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, QMIN, 98298)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, QMIN, 98298)]) 2%nat eq_refl emp_192). Qed.
Lemma rn_208 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb2_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) r_29 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb2_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) tb2_arm_n1000 _ c_209 eq_211 vl_95). Qed.
Lemma rn_206 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb2_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) r_30 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb2_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) _ le_207 rn_208). Qed.
Lemma rn_212 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_g5b ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) r_17 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_g5b ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) _ le_213 rn_161). Qed.
Lemma rf_214 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_12 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) [(2600%nat, r_17); (1000%nat, r_30)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_12 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) 2600%nat r_17 _ (rsh_1) T_g5b eq_refl rn_212 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_12 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) 1000%nat r_30 _ (rsh_2) ST_tb2_arm_h1000 eq_refl rn_206 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_12 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)])))). Qed.
Lemma nd_201 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb2_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) t_31 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb2_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) 2%nat tb2_armd5b HR_12 [(2600%nat, r_17); (1000%nat, r_30)] _ eq_refl c_202 pay_204 covs_205 rf_214). Qed.
Lemma fo_215 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_11 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) [(14%nat, t_31)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_11 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) 14%nat t_31 _ 2%nat ST_tb2_cont eq_refl nd_201 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_11 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]))). Qed.
Lemma nd_196 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) t_32 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) 2%nat pb2pre HT_11 [(14%nat, t_31)] _ eq_refl c_197 seg_199 cov_200 fo_215). Qed.
Lemma nd_194 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f2 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, QMIN, 262137)]) t_33 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f2 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, QMIN, 262137)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143); (QRoom, 98299, 262137)]) t_32 le_195 nd_196). Qed.
Lemma nd_216 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f2 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, 262137 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f2 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) ++ [(QRoom, 262137 + 1, QMAX)]) 2%nat eq_refl emp_217). Qed.
Lemma nd_193 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) t_34 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) ++ [(QRoom, 98298 + 1, QMAX)]) QRoom 262137 t_33 t_1 nd_194 nd_216). Qed.
Lemma nd_190 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) t_35 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) QRoom 98298 t_1 t_34 nd_191 nd_193). Qed.
Lemma fo_218 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) [(132%nat, t_35)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) 132%nat t_35 _ 2%nat ST_cb_f2 eq_refl nd_190 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]))). Qed.
Lemma nd_185 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) t_36 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) 2%nat cb_f2 HT_10 [(132%nat, t_35)] _ eq_refl c_186 seg_188 cov_189 fo_218). Qed.
Lemma nd_183 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) ++ [(QFlen, QMIN, 262143)]) t_37 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) ++ [(QFlen, QMIN, 262143)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 262143)]) t_36 le_184 nd_185). Qed.
Lemma nd_240 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, QMIN, 229370)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, QMIN, 229370)]) 2%nat eq_refl emp_241). Qed.
Lemma rn_257 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb3_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) r_38 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb3_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) tb3_arm_n1000 _ c_258 eq_260 vl_95). Qed.
Lemma rn_255 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb3_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) r_39 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb3_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) _ le_256 rn_257). Qed.
Lemma rn_261 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_g5b ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) r_17 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_g5b ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) _ le_262 rn_161). Qed.
Lemma rf_263 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_17 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) [(2600%nat, r_17); (1000%nat, r_39)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_17 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) 2600%nat r_17 _ (rsh_1) T_g5b eq_refl rn_261 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_17 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) 1000%nat r_39 _ (rsh_2) ST_tb3_arm_h1000 eq_refl rn_255 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_17 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)])))). Qed.
Lemma nd_250 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb3_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) t_40 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb3_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) 2%nat tb3_armd5b HR_17 [(2600%nat, r_17); (1000%nat, r_39)] _ eq_refl c_251 pay_253 covs_254 rf_263). Qed.
Lemma fo_264 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_16 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) [(14%nat, t_40)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_16 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) 14%nat t_40 _ 2%nat ST_tb3_cont eq_refl nd_250 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_16 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]))). Qed.
Lemma nd_245 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) t_41 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) 2%nat pb3pre HT_16 [(14%nat, t_40)] _ eq_refl c_246 seg_248 cov_249 fo_264). Qed.
Lemma nd_243 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f3 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, QMIN, 524281)]) t_42 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f3 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, QMIN, 524281)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287); (QRoom, 229371, 524281)]) t_41 le_244 nd_245). Qed.
Lemma nd_265 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f3 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, 524281 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f3 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) ++ [(QRoom, 524281 + 1, QMAX)]) 2%nat eq_refl emp_266). Qed.
Lemma nd_242 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) t_43 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) ++ [(QRoom, 229370 + 1, QMAX)]) QRoom 524281 t_42 t_1 nd_243 nd_265). Qed.
Lemma nd_239 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) t_44 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) QRoom 229370 t_1 t_43 nd_240 nd_242). Qed.
Lemma fo_267 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_15 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) [(133%nat, t_44)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_15 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) 133%nat t_44 _ 2%nat ST_cb_f3 eq_refl nd_239 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_15 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]))). Qed.
Lemma nd_234 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) t_45 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) 2%nat cb_f3 HT_15 [(133%nat, t_44)] _ eq_refl c_235 seg_237 cov_238 fo_267). Qed.
Lemma nd_232 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) ++ [(QFlen, QMIN, 524287)]) t_46 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) ++ [(QFlen, QMIN, 524287)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 524287)]) t_45 le_233 nd_234). Qed.
Lemma nd_289 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, QMIN, 491514)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, QMIN, 491514)]) 2%nat eq_refl emp_290). Qed.
Lemma rn_308 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb4_a_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) r_47 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb4_a_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) tb4_a_n1000 _ c_309 eq_311 vl_95). Qed.
Lemma rn_306 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb4_a_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) r_48 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb4_a_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) _ le_307 rn_308). Qed.
Lemma rn_312 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_g5b ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) r_17 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_g5b ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 1048575)]) _ le_313 rn_161). Qed.
Lemma rf_314 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_22 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) [(2600%nat, r_17); (1000%nat, r_48)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_22 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 2600%nat r_17 _ (rsh_1) T_g5b eq_refl rn_312 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_22 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 1000%nat r_48 _ (rsh_2) ST_tb4_a_h1000 eq_refl rn_306 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_22 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)])))). Qed.
Lemma nd_301 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat (mcase_lo ST_tb4_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 524287) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) t_49 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat (mcase_lo ST_tb4_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 524287) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 2%nat tb4_ad5b HR_22 [(2600%nat, r_17); (1000%nat, r_48)] _ eq_refl c_302 pay_304 covs_305 rf_314). Qed.
Lemma rn_321 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb4_b_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) r_50 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb4_b_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) tb4_b_n1000 _ c_322 eq_324 vl_95). Qed.
Lemma rn_320 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb4_b_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) r_51 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb4_b_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) _ le_307 rn_321). Qed.
Lemma rf_325 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_23 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) [(2600%nat, r_17); (1000%nat, r_51)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_23 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 2600%nat r_17 _ (rsh_1) T_g5b eq_refl rn_312 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_23 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 1000%nat r_51 _ (rsh_2) ST_tb4_b_h1000 eq_refl rn_320 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_23 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)])))). Qed.
Lemma nd_315 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat (mcase_hi ST_tb4_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 524287) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) t_52 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat (mcase_hi ST_tb4_cont (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 524287) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 2%nat tb4_bd5b HR_23 [(2600%nat, r_17); (1000%nat, r_51)] _ eq_refl c_316 pay_318 covs_319 rf_325). Qed.
Lemma nd_299 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb4_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) t_53 = true.
Proof. exact (mtree_ok_case 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb4_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) (EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EVar 45) (EMd Instr.M_MUL (ELit (-1)) (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)))) (ELit (-6))) 524287 t_49 t_52 lsh_300 nd_301 nd_315). Qed.
Lemma fo_326 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_21 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) [(14%nat, t_53)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_21 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 14%nat t_53 _ 2%nat ST_tb4_cont eq_refl nd_299 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_21 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]))). Qed.
Lemma nd_294 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) t_54 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) 2%nat pb4 HT_21 [(14%nat, t_53)] _ eq_refl c_295 seg_297 cov_298 fo_326). Qed.
Lemma nd_292 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f4 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, QMIN, 1048569)]) t_55 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f4 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, QMIN, 1048569)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575); (QRoom, 491515, 1048569)]) t_54 le_293 nd_294). Qed.
Lemma nd_327 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f4 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, 1048569 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f4 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) ++ [(QRoom, 1048569 + 1, QMAX)]) 2%nat eq_refl emp_328). Qed.
Lemma nd_291 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) t_56 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) ++ [(QRoom, 491514 + 1, QMAX)]) QRoom 1048569 t_55 t_1 nd_292 nd_327). Qed.
Lemma nd_288 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) t_57 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) QRoom 491514 t_1 t_56 nd_289 nd_291). Qed.
Lemma fo_329 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_20 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) [(134%nat, t_57)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_20 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) 134%nat t_57 _ 2%nat ST_cb_f4 eq_refl nd_288 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_20 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]))). Qed.
Lemma nd_283 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) t_58 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) 2%nat cb_f4 HT_20 [(134%nat, t_57)] _ eq_refl c_284 seg_286 cov_287 fo_329). Qed.
Lemma nd_281 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) ++ [(QFlen, QMIN, 1048575)]) t_59 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) ++ [(QFlen, QMIN, 1048575)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 1048575)]) t_58 le_282 nd_283). Qed.
Lemma nd_351 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, QMIN, 1015802)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, QMIN, 1015802)]) 2%nat eq_refl emp_352). Qed.
Lemma rn_375 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) r_64 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) nl_d2mb _ c_376 eq_378 vl_95). Qed.
Lemma rn_373 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) r_65 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_374 rn_375). Qed.
Lemma rf_379 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) [(2310%nat, r_65)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) 2310%nat r_65 _ (rsh_2) T_d2mb eq_refl rn_373 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]))). Qed.
Lemma rn_368 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb5_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) r_66 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb5_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) tb5_arm_nulld2mb HR_30 [(2310%nat, r_65)] _ c_369 req_371 vl_95 covs_372 rf_379). Qed.
Lemma rn_366 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb5_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) r_67 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb5_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) _ le_367 rn_368). Qed.
Lemma rn_389 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5s ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) r_60 = true.
Proof. exact (rtree_ok_leaf 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5s ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) ts_d2xb5s _ c_390 eq_392 vl_121). Qed.
Lemma rn_387 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5s ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) r_61 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5s ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_388 rn_389). Qed.
Lemma rf_393 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_29 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) [(900%nat, r_61)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_29 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) 900%nat r_61 _ (rsh_1) T_d2xb5s eq_refl rn_387 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_29 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]))). Qed.
Lemma rn_382 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) r_62 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) armxb HR_29 [(900%nat, r_61)] _ c_383 req_385 vl_121 covs_386 rf_393). Qed.
Lemma rn_380 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) r_63 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_381 rn_382). Qed.
Lemma rf_394 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_28 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) [(2350%nat, r_63); (1000%nat, r_67)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_28 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) 2350%nat r_63 _ (rsh_1) T_d2xb5 eq_refl rn_380 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_28 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) 1000%nat r_67 _ (rsh_2) ST_tb5_arm_h1000 eq_refl rn_366 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_28 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)])))). Qed.
Lemma nd_361 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb5_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) t_68 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb5_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) 2%nat tb5_arm_x2 HR_28 [(2350%nat, r_63); (1000%nat, r_67)] _ eq_refl c_362 pay_364 covs_365 rf_394). Qed.
Lemma fo_395 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_27 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) [(14%nat, t_68)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_27 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) 14%nat t_68 _ 2%nat ST_tb5_cont eq_refl nd_361 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_27 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]))). Qed.
Lemma nd_356 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) t_69 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) 2%nat pb5pre HT_27 [(14%nat, t_68)] _ eq_refl c_357 seg_359 cov_360 fo_395). Qed.
Lemma nd_354 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f5 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, QMIN, 2097145)]) t_70 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f5 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, QMIN, 2097145)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151); (QRoom, 1015803, 2097145)]) t_69 le_355 nd_356). Qed.
Lemma nd_396 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f5 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, 2097145 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f5 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) ++ [(QRoom, 2097145 + 1, QMAX)]) 2%nat eq_refl emp_397). Qed.
Lemma nd_353 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) t_71 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) ++ [(QRoom, 1015802 + 1, QMAX)]) QRoom 2097145 t_70 t_1 nd_354 nd_396). Qed.
Lemma nd_350 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) t_72 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) QRoom 1015802 t_1 t_71 nd_351 nd_353). Qed.
Lemma fo_398 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_26 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) [(135%nat, t_72)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_26 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) 135%nat t_72 _ 2%nat ST_cb_f5 eq_refl nd_350 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_26 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]))). Qed.
Lemma nd_345 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) t_73 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) 2%nat cb_f5 HT_26 [(135%nat, t_72)] _ eq_refl c_346 seg_348 cov_349 fo_398). Qed.
Lemma nd_343 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) ++ [(QFlen, QMIN, 2097151)]) t_74 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) ++ [(QFlen, QMIN, 2097151)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 2097151)]) t_73 le_344 nd_345). Qed.
Lemma nd_420 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, QMIN, 2064378)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, QMIN, 2064378)]) 2%nat eq_refl emp_421). Qed.
Lemma rn_441 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) r_65 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_442 rn_375). Qed.
Lemma rf_443 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) [(2310%nat, r_65)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) 2310%nat r_65 _ (rsh_2) T_d2mb eq_refl rn_441 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]))). Qed.
Lemma rn_437 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb6_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) r_75 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb6_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) tb6_arm_nulld2mb HR_30 [(2310%nat, r_65)] _ c_438 req_440 vl_95 covs_372 rf_443). Qed.
Lemma rn_435 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb6_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) r_76 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb6_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) _ le_436 rn_437). Qed.
Lemma rn_444 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) r_63 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_445 rn_382). Qed.
Lemma rf_446 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_35 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) [(2350%nat, r_63); (1000%nat, r_76)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_35 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) 2350%nat r_63 _ (rsh_1) T_d2xb5 eq_refl rn_444 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_35 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) 1000%nat r_76 _ (rsh_2) ST_tb6_arm_h1000 eq_refl rn_435 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_35 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)])))). Qed.
Lemma nd_430 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb6_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) t_77 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb6_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) 2%nat tb6_arm_x2 HR_35 [(2350%nat, r_63); (1000%nat, r_76)] _ eq_refl c_431 pay_433 covs_434 rf_446). Qed.
Lemma fo_447 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_34 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) [(14%nat, t_77)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_34 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) 14%nat t_77 _ 2%nat ST_tb6_cont eq_refl nd_430 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_34 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]))). Qed.
Lemma nd_425 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) t_78 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) 2%nat pb6pre HT_34 [(14%nat, t_77)] _ eq_refl c_426 seg_428 cov_429 fo_447). Qed.
Lemma nd_423 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f6 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, QMIN, 4194297)]) t_79 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f6 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, QMIN, 4194297)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303); (QRoom, 2064379, 4194297)]) t_78 le_424 nd_425). Qed.
Lemma nd_448 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f6 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, 4194297 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f6 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) ++ [(QRoom, 4194297 + 1, QMAX)]) 2%nat eq_refl emp_449). Qed.
Lemma nd_422 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) t_80 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) ++ [(QRoom, 2064378 + 1, QMAX)]) QRoom 4194297 t_79 t_1 nd_423 nd_448). Qed.
Lemma nd_419 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) t_81 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) QRoom 2064378 t_1 t_80 nd_420 nd_422). Qed.
Lemma fo_450 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_33 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) [(136%nat, t_81)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_33 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) 136%nat t_81 _ 2%nat ST_cb_f6 eq_refl nd_419 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_33 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]))). Qed.
Lemma nd_414 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) t_82 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) 2%nat cb_f6 HT_33 [(136%nat, t_81)] _ eq_refl c_415 seg_417 cov_418 fo_450). Qed.
Lemma nd_412 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) ++ [(QFlen, QMIN, 4194303)]) t_83 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) ++ [(QFlen, QMIN, 4194303)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 4194303)]) t_82 le_413 nd_414). Qed.
Lemma nd_472 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, QMIN, 4161530)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, QMIN, 4161530)]) 2%nat eq_refl emp_473). Qed.
Lemma rn_493 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) r_65 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_494 rn_375). Qed.
Lemma rf_495 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) [(2310%nat, r_65)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) 2310%nat r_65 _ (rsh_2) T_d2mb eq_refl rn_493 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]))). Qed.
Lemma rn_489 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb7_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) r_84 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb7_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) tb7_arm_nulld2mb HR_30 [(2310%nat, r_65)] _ c_490 req_492 vl_95 covs_372 rf_495). Qed.
Lemma rn_487 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb7_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) r_85 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb7_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) _ le_488 rn_489). Qed.
Lemma rn_496 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) r_63 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_497 rn_382). Qed.
Lemma rf_498 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_40 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) [(2350%nat, r_63); (1000%nat, r_85)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_40 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) 2350%nat r_63 _ (rsh_1) T_d2xb5 eq_refl rn_496 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_40 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) 1000%nat r_85 _ (rsh_2) ST_tb7_arm_h1000 eq_refl rn_487 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_40 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)])))). Qed.
Lemma nd_482 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb7_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) t_86 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb7_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) 2%nat tb7_arm_x2 HR_40 [(2350%nat, r_63); (1000%nat, r_85)] _ eq_refl c_483 pay_485 covs_486 rf_498). Qed.
Lemma fo_499 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_39 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) [(14%nat, t_86)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_39 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) 14%nat t_86 _ 2%nat ST_tb7_cont eq_refl nd_482 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_39 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]))). Qed.
Lemma nd_477 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) t_87 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) 2%nat pb7pre HT_39 [(14%nat, t_86)] _ eq_refl c_478 seg_480 cov_481 fo_499). Qed.
Lemma nd_475 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f7 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, QMIN, 8388601)]) t_88 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f7 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, QMIN, 8388601)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607); (QRoom, 4161531, 8388601)]) t_87 le_476 nd_477). Qed.
Lemma nd_500 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f7 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, 8388601 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f7 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) ++ [(QRoom, 8388601 + 1, QMAX)]) 2%nat eq_refl emp_501). Qed.
Lemma nd_474 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) t_89 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) ++ [(QRoom, 4161530 + 1, QMAX)]) QRoom 8388601 t_88 t_1 nd_475 nd_500). Qed.
Lemma nd_471 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) t_90 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) QRoom 4161530 t_1 t_89 nd_472 nd_474). Qed.
Lemma fo_502 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_38 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) [(137%nat, t_90)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_38 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) 137%nat t_90 _ 2%nat ST_cb_f7 eq_refl nd_471 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_38 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]))). Qed.
Lemma nd_466 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) t_91 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) 2%nat cb_f7 HT_38 [(137%nat, t_90)] _ eq_refl c_467 seg_469 cov_470 fo_502). Qed.
Lemma nd_464 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) ++ [(QFlen, QMIN, 8388607)]) t_92 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) ++ [(QFlen, QMIN, 8388607)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 8388607)]) t_91 le_465 nd_466). Qed.
Lemma nd_524 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, QMIN, 8355834)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, QMIN, 8355834)]) 2%nat eq_refl emp_525). Qed.
Lemma rn_545 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) r_65 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_546 rn_375). Qed.
Lemma rf_547 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) [(2310%nat, r_65)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) 2310%nat r_65 _ (rsh_2) T_d2mb eq_refl rn_545 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]))). Qed.
Lemma rn_541 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb8_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) r_93 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb8_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) tb8_arm_nulld2mb HR_30 [(2310%nat, r_65)] _ c_542 req_544 vl_95 covs_372 rf_547). Qed.
Lemma rn_539 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb8_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) r_94 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb8_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) _ le_540 rn_541). Qed.
Lemma rn_548 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) r_63 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_549 rn_382). Qed.
Lemma rf_550 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_45 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) [(2350%nat, r_63); (1000%nat, r_94)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_45 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) 2350%nat r_63 _ (rsh_1) T_d2xb5 eq_refl rn_548 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_45 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) 1000%nat r_94 _ (rsh_2) ST_tb8_arm_h1000 eq_refl rn_539 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_45 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)])))). Qed.
Lemma nd_534 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb8_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) t_95 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb8_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) 2%nat tb8_arm_x2 HR_45 [(2350%nat, r_63); (1000%nat, r_94)] _ eq_refl c_535 pay_537 covs_538 rf_550). Qed.
Lemma fo_551 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_44 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) [(14%nat, t_95)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_44 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) 14%nat t_95 _ 2%nat ST_tb8_cont eq_refl nd_534 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_44 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]))). Qed.
Lemma nd_529 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) t_96 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) 2%nat pb8pre HT_44 [(14%nat, t_95)] _ eq_refl c_530 seg_532 cov_533 fo_551). Qed.
Lemma nd_527 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f8 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, QMIN, 16777209)]) t_97 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f8 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, QMIN, 16777209)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215); (QRoom, 8355835, 16777209)]) t_96 le_528 nd_529). Qed.
Lemma nd_552 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f8 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, 16777209 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f8 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) ++ [(QRoom, 16777209 + 1, QMAX)]) 2%nat eq_refl emp_553). Qed.
Lemma nd_526 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) t_98 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) ++ [(QRoom, 8355834 + 1, QMAX)]) QRoom 16777209 t_97 t_1 nd_527 nd_552). Qed.
Lemma nd_523 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) t_99 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) QRoom 8355834 t_1 t_98 nd_524 nd_526). Qed.
Lemma fo_554 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_43 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) [(138%nat, t_99)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_43 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) 138%nat t_99 _ 2%nat ST_cb_f8 eq_refl nd_523 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_43 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]))). Qed.
Lemma nd_518 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) t_100 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) 2%nat cb_f8 HT_43 [(138%nat, t_99)] _ eq_refl c_519 seg_521 cov_522 fo_554). Qed.
Lemma nd_516 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) ++ [(QFlen, QMIN, 16777215)]) t_101 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) ++ [(QFlen, QMIN, 16777215)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 16777215)]) t_100 le_517 nd_518). Qed.
Lemma nd_576 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, QMIN, 16744442)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, QMIN, 16744442)]) 2%nat eq_refl emp_577). Qed.
Lemma rn_597 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) r_65 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_598 rn_375). Qed.
Lemma rf_599 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) [(2310%nat, r_65)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) 2310%nat r_65 _ (rsh_2) T_d2mb eq_refl rn_597 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]))). Qed.
Lemma rn_593 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb9_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) r_102 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb9_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) tb9_arm_nulld2mb HR_30 [(2310%nat, r_65)] _ c_594 req_596 vl_95 covs_372 rf_599). Qed.
Lemma rn_591 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb9_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) r_103 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb9_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) _ le_592 rn_593). Qed.
Lemma rn_600 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) r_63 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_601 rn_382). Qed.
Lemma rf_602 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_50 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) [(2350%nat, r_63); (1000%nat, r_103)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_50 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) 2350%nat r_63 _ (rsh_1) T_d2xb5 eq_refl rn_600 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_50 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) 1000%nat r_103 _ (rsh_2) ST_tb9_arm_h1000 eq_refl rn_591 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_50 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)])))). Qed.
Lemma nd_586 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb9_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) t_104 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb9_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) 2%nat tb9_arm_x2 HR_50 [(2350%nat, r_63); (1000%nat, r_103)] _ eq_refl c_587 pay_589 covs_590 rf_602). Qed.
Lemma fo_603 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_49 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) [(14%nat, t_104)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_49 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) 14%nat t_104 _ 2%nat ST_tb9_cont eq_refl nd_586 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_49 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]))). Qed.
Lemma nd_581 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) t_105 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) 2%nat pb9pre HT_49 [(14%nat, t_104)] _ eq_refl c_582 seg_584 cov_585 fo_603). Qed.
Lemma nd_579 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f9 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, QMIN, 33554425)]) t_106 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f9 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, QMIN, 33554425)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431); (QRoom, 16744443, 33554425)]) t_105 le_580 nd_581). Qed.
Lemma nd_604 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f9 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, 33554425 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f9 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) ++ [(QRoom, 33554425 + 1, QMAX)]) 2%nat eq_refl emp_605). Qed.
Lemma nd_578 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) t_107 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) ++ [(QRoom, 16744442 + 1, QMAX)]) QRoom 33554425 t_106 t_1 nd_579 nd_604). Qed.
Lemma nd_575 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) t_108 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) QRoom 16744442 t_1 t_107 nd_576 nd_578). Qed.
Lemma fo_606 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_48 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) [(139%nat, t_108)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_48 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) 139%nat t_108 _ 2%nat ST_cb_f9 eq_refl nd_575 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_48 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]))). Qed.
Lemma nd_570 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) t_109 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) 2%nat cb_f9 HT_48 [(139%nat, t_108)] _ eq_refl c_571 seg_573 cov_574 fo_606). Qed.
Lemma nd_568 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) ++ [(QFlen, QMIN, 33554431)]) t_110 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) ++ [(QFlen, QMIN, 33554431)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 33554431)]) t_109 le_569 nd_570). Qed.
Lemma nd_628 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, QMIN, 33521658)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, QMIN, 33521658)]) 2%nat eq_refl emp_629). Qed.
Lemma rn_649 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) r_65 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) T_d2mb ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_650 rn_375). Qed.
Lemma rf_651 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) [(2310%nat, r_65)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) 2310%nat r_65 _ (rsh_2) T_d2mb eq_refl rn_649 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_30 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]))). Qed.
Lemma rn_645 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb10_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) r_111 = true.
Proof. exact (rtree_ok_preS 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb10_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) tb10_arm_nulld2mb HR_30 [(2310%nat, r_65)] _ c_646 req_648 vl_95 covs_372 rf_651). Qed.
Lemma rn_643 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb10_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) r_112 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_2) ST_tb10_arm_h1000 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) _ le_644 rn_645). Qed.
Lemma rn_652 : rtree_ok 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) r_63 = true.
Proof. exact (rtree_ok_class 0%nat 400000%nat 5000%nat IT_both (rsh_1) T_d2xb5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108863)]) _ le_653 rn_382). Qed.
Lemma rf_654 : rforest_ok 0%nat 400000%nat 5000%nat IT_both HR_55 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) [(2350%nat, r_63); (1000%nat, r_112)] = true.
Proof. exact (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_55 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) 2350%nat r_63 _ (rsh_1) T_d2xb5 eq_refl rn_652 (rforest_ok_cons 0%nat 400000%nat 5000%nat IT_both HR_55 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) 1000%nat r_112 _ (rsh_2) ST_tb10_arm_h1000 eq_refl rn_643 (rforest_ok_nil 0%nat 400000%nat 5000%nat IT_both HR_55 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)])))). Qed.
Lemma nd_638 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb10_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) t_113 = true.
Proof. exact (mtree_ok_preS 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_tb10_cont ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) 2%nat tb10_arm_x2 HR_55 [(2350%nat, r_63); (1000%nat, r_112)] _ eq_refl c_639 pay_641 covs_642 rf_654). Qed.
Lemma fo_655 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_54 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) [(14%nat, t_113)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_54 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) 14%nat t_113 _ 2%nat ST_tb10_cont eq_refl nd_638 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_54 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]))). Qed.
Lemma nd_633 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) t_114 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) 2%nat pb10pre HT_54 [(14%nat, t_113)] _ eq_refl c_634 seg_636 cov_637 fo_655). Qed.
Lemma nd_631 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f10 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, QMIN, 67108857)]) t_115 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f10 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, QMIN, 67108857)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863); (QRoom, 33521659, 67108857)]) t_114 le_632 nd_633). Qed.
Lemma nd_656 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f10 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, 67108857 + 1, QMAX)]) t_1 = true.
Proof. exact (mtree_ok_empty 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f10 ((([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) ++ [(QRoom, 67108857 + 1, QMAX)]) 2%nat eq_refl emp_657). Qed.
Lemma nd_630 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) t_116 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) ++ [(QRoom, 33521658 + 1, QMAX)]) QRoom 67108857 t_115 t_1 nd_631 nd_656). Qed.
Lemma nd_627 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) t_117 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 2%nat 2%nat ST_cb_f10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) QRoom 33521658 t_1 t_116 nd_628 nd_630). Qed.
Lemma fo_658 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 2%nat HT_53 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) [(140%nat, t_117)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 2%nat HT_53 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) 140%nat t_117 _ 2%nat ST_cb_f10 eq_refl nd_627 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 2%nat HT_53 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]))). Qed.
Lemma nd_622 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) t_118 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) 2%nat cb_f10 HT_53 [(140%nat, t_117)] _ eq_refl c_623 seg_625 cov_626 fo_658). Qed.
Lemma nd_620 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) ++ [(QFlen, QMIN, 67108863)]) t_119 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) ++ [(QFlen, QMIN, 67108863)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108863)]) t_118 le_621 nd_622). Qed.
Lemma nd_661 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]) t_120 = true.
Proof. exact (mtree_ok_leaf 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]) 2%nat cb_r10 _ eq_refl c_662 pay_664). Qed.
Lemma nd_659 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) ++ [(QFlen, 67108863 + 1, QMAX)]) t_121 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s10 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) ++ [(QFlen, 67108863 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 67108864, 67108864)]) t_120 le_660 nd_661). Qed.
Lemma nd_619 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) t_122 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s10 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) QFlen 67108863 t_119 t_121 nd_620 nd_659). Qed.
Lemma fo_665 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_52 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) [(119%nat, t_122)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_52 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) 119%nat t_122 _ 2%nat ST_cb_s10 eq_refl nd_619 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_52 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]))). Qed.
Lemma nd_614 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) t_123 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) 1%nat cb_s10 HT_52 [(119%nat, t_122)] _ eq_refl c_615 seg_617 cov_618 fo_665). Qed.
Lemma fo_666 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_51 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) [(118%nat, t_123)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_51 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) 118%nat t_123 _ 1%nat ST_cb_r9 eq_refl nd_614 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_51 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]))). Qed.
Lemma nd_609 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) t_124 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) 1%nat cb_r9 HT_51 [(118%nat, t_123)] _ eq_refl c_610 seg_612 cov_613 fo_666). Qed.
Lemma nd_607 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) ++ [(QFlen, 33554431 + 1, QMAX)]) t_125 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s9 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) ++ [(QFlen, 33554431 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 33554432, 67108864)]) t_124 le_608 nd_609). Qed.
Lemma nd_567 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) t_126 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) QFlen 33554431 t_110 t_125 nd_568 nd_607). Qed.
Lemma fo_667 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_47 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) [(117%nat, t_126)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_47 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) 117%nat t_126 _ 2%nat ST_cb_s9 eq_refl nd_567 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_47 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]))). Qed.
Lemma nd_562 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) t_127 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) 1%nat cb_s9 HT_47 [(117%nat, t_126)] _ eq_refl c_563 seg_565 cov_566 fo_667). Qed.
Lemma fo_668 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_46 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) [(116%nat, t_127)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_46 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) 116%nat t_127 _ 1%nat ST_cb_r8 eq_refl nd_562 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_46 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]))). Qed.
Lemma nd_557 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) t_128 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) 1%nat cb_r8 HT_46 [(116%nat, t_127)] _ eq_refl c_558 seg_560 cov_561 fo_668). Qed.
Lemma nd_555 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) ++ [(QFlen, 16777215 + 1, QMAX)]) t_129 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s8 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) ++ [(QFlen, 16777215 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 16777216, 67108864)]) t_128 le_556 nd_557). Qed.
Lemma nd_515 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) t_130 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) QFlen 16777215 t_101 t_129 nd_516 nd_555). Qed.
Lemma fo_669 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_42 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) [(115%nat, t_130)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_42 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) 115%nat t_130 _ 2%nat ST_cb_s8 eq_refl nd_515 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_42 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]))). Qed.
Lemma nd_510 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) t_131 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) 1%nat cb_s8 HT_42 [(115%nat, t_130)] _ eq_refl c_511 seg_513 cov_514 fo_669). Qed.
Lemma fo_670 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_41 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) [(114%nat, t_131)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_41 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) 114%nat t_131 _ 1%nat ST_cb_r7 eq_refl nd_510 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_41 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]))). Qed.
Lemma nd_505 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) t_132 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) 1%nat cb_r7 HT_41 [(114%nat, t_131)] _ eq_refl c_506 seg_508 cov_509 fo_670). Qed.
Lemma nd_503 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) ++ [(QFlen, 8388607 + 1, QMAX)]) t_133 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s7 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) ++ [(QFlen, 8388607 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 8388608, 67108864)]) t_132 le_504 nd_505). Qed.
Lemma nd_463 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) t_134 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s7 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) QFlen 8388607 t_92 t_133 nd_464 nd_503). Qed.
Lemma fo_671 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_37 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) [(113%nat, t_134)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_37 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) 113%nat t_134 _ 2%nat ST_cb_s7 eq_refl nd_463 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_37 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]))). Qed.
Lemma nd_458 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) t_135 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) 1%nat cb_s7 HT_37 [(113%nat, t_134)] _ eq_refl c_459 seg_461 cov_462 fo_671). Qed.
Lemma fo_672 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_36 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) [(112%nat, t_135)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_36 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) 112%nat t_135 _ 1%nat ST_cb_r6 eq_refl nd_458 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_36 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]))). Qed.
Lemma nd_453 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) t_136 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) 1%nat cb_r6 HT_36 [(112%nat, t_135)] _ eq_refl c_454 seg_456 cov_457 fo_672). Qed.
Lemma nd_451 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) ++ [(QFlen, 4194303 + 1, QMAX)]) t_137 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s6 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) ++ [(QFlen, 4194303 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 4194304, 67108864)]) t_136 le_452 nd_453). Qed.
Lemma nd_411 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) t_138 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s6 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) QFlen 4194303 t_83 t_137 nd_412 nd_451). Qed.
Lemma fo_673 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) [(111%nat, t_138)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) 111%nat t_138 _ 2%nat ST_cb_s6 eq_refl nd_411 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_32 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]))). Qed.
Lemma nd_406 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) t_139 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) 1%nat cb_s6 HT_32 [(111%nat, t_138)] _ eq_refl c_407 seg_409 cov_410 fo_673). Qed.
Lemma fo_674 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_31 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) [(110%nat, t_139)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_31 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) 110%nat t_139 _ 1%nat ST_cb_r5 eq_refl nd_406 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_31 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]))). Qed.
Lemma nd_401 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) t_140 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) 1%nat cb_r5 HT_31 [(110%nat, t_139)] _ eq_refl c_402 seg_404 cov_405 fo_674). Qed.
Lemma nd_399 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) ++ [(QFlen, 2097151 + 1, QMAX)]) t_141 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s5 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) ++ [(QFlen, 2097151 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 2097152, 67108864)]) t_140 le_400 nd_401). Qed.
Lemma nd_342 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) t_142 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s5 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) QFlen 2097151 t_74 t_141 nd_343 nd_399). Qed.
Lemma fo_675 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_25 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) [(109%nat, t_142)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_25 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) 109%nat t_142 _ 2%nat ST_cb_s5 eq_refl nd_342 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_25 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]))). Qed.
Lemma nd_337 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) t_143 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) 1%nat cb_s5 HT_25 [(109%nat, t_142)] _ eq_refl c_338 seg_340 cov_341 fo_675). Qed.
Lemma fo_676 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_24 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) [(108%nat, t_143)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_24 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) 108%nat t_143 _ 1%nat ST_cb_r4 eq_refl nd_337 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_24 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]))). Qed.
Lemma nd_332 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) t_144 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) 1%nat cb_r4 HT_24 [(108%nat, t_143)] _ eq_refl c_333 seg_335 cov_336 fo_676). Qed.
Lemma nd_330 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) ++ [(QFlen, 1048575 + 1, QMAX)]) t_145 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s4 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) ++ [(QFlen, 1048575 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 1048576, 67108864)]) t_144 le_331 nd_332). Qed.
Lemma nd_280 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) t_146 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s4 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) QFlen 1048575 t_59 t_145 nd_281 nd_330). Qed.
Lemma fo_677 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_19 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) [(107%nat, t_146)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_19 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) 107%nat t_146 _ 2%nat ST_cb_s4 eq_refl nd_280 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_19 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]))). Qed.
Lemma nd_275 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) t_147 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) 1%nat cb_s4 HT_19 [(107%nat, t_146)] _ eq_refl c_276 seg_278 cov_279 fo_677). Qed.
Lemma fo_678 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_18 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) [(106%nat, t_147)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_18 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) 106%nat t_147 _ 1%nat ST_cb_r3 eq_refl nd_275 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_18 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]))). Qed.
Lemma nd_270 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) t_148 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) 1%nat cb_r3 HT_18 [(106%nat, t_147)] _ eq_refl c_271 seg_273 cov_274 fo_678). Qed.
Lemma nd_268 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) ++ [(QFlen, 524287 + 1, QMAX)]) t_149 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s3 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) ++ [(QFlen, 524287 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 524288, 67108864)]) t_148 le_269 nd_270). Qed.
Lemma nd_231 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) t_150 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s3 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) QFlen 524287 t_46 t_149 nd_232 nd_268). Qed.
Lemma fo_679 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_14 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) [(105%nat, t_150)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_14 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) 105%nat t_150 _ 2%nat ST_cb_s3 eq_refl nd_231 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_14 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]))). Qed.
Lemma nd_226 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) t_151 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) 1%nat cb_s3 HT_14 [(105%nat, t_150)] _ eq_refl c_227 seg_229 cov_230 fo_679). Qed.
Lemma fo_680 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_13 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) [(104%nat, t_151)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_13 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) 104%nat t_151 _ 1%nat ST_cb_r2 eq_refl nd_226 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_13 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]))). Qed.
Lemma nd_221 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) t_152 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) 1%nat cb_r2 HT_13 [(104%nat, t_151)] _ eq_refl c_222 seg_224 cov_225 fo_680). Qed.
Lemma nd_219 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) ++ [(QFlen, 262143 + 1, QMAX)]) t_153 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s2 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) ++ [(QFlen, 262143 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 262144, 67108864)]) t_152 le_220 nd_221). Qed.
Lemma nd_182 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) t_154 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s2 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) QFlen 262143 t_37 t_153 nd_183 nd_219). Qed.
Lemma fo_681 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) [(103%nat, t_154)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) 103%nat t_154 _ 2%nat ST_cb_s2 eq_refl nd_182 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_9 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]))). Qed.
Lemma nd_177 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) t_155 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat ST_cb_r1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) 1%nat cb_s2 HT_9 [(103%nat, t_154)] _ eq_refl c_178 seg_180 cov_181 fo_681). Qed.
Lemma fo_682 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) [(102%nat, t_155)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) 102%nat t_155 _ 1%nat ST_cb_r1 eq_refl nd_177 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_8 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]))). Qed.
Lemma nd_172 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) t_156 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) 1%nat cb_r1 HT_8 [(102%nat, t_155)] _ eq_refl c_173 seg_175 cov_176 fo_682). Qed.
Lemma nd_170 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) ++ [(QFlen, 131071 + 1, QMAX)]) t_157 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s1 (([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) ++ [(QFlen, 131071 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 131072, 67108864)]) t_156 le_171 nd_172). Qed.
Lemma nd_63 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) t_158 = true.
Proof. exact (mtree_ok_split 0%nat 400000%nat 5000%nat IT_both 1%nat 2%nat ST_cb_s1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) QFlen 131071 t_28 t_157 nd_64 nd_170). Qed.
Lemma fo_683 : mforest_ok 0%nat 400000%nat 5000%nat IT_both 1%nat HT_1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) [(101%nat, t_158)] = true.
Proof. exact (mforest_ok_cons 0%nat 400000%nat 5000%nat IT_both 1%nat HT_1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) 101%nat t_158 _ 2%nat ST_cb_s1 eq_refl nd_63 (mforest_ok_nil 0%nat 400000%nat 5000%nat IT_both 1%nat HT_1 ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]))). Qed.
Lemma nd_58 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat HG1_s ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) t_159 = true.
Proof. exact (mtree_ok_seg 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat HG1_s ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) 1%nat cb_s1 HT_1 [(101%nat, t_158)] _ eq_refl c_59 seg_61 cov_62 fo_683). Qed.
Lemma nd_56 : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat HG1_s ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) t_160 = true.
Proof. exact (mtree_ok_class 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat HG1_s ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, 65536, 67108864)]) t_159 le_57 nd_58). Qed.
Definition TW1 : mtree := t_160.
Lemma TW1_ok : mtree_ok 0%nat 400000%nat 5000%nat IT_both 1%nat 1%nat HG1_s ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) TW1 = true.
Proof. exact nd_56. Qed.
