(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)


From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.json_c.json_object_fuzzer.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_20814 : bv 32 := 0xffff0197.
Lemma F_20814 : fetch_word Plain.M.loaded_segments (0x20874 : word) = Some W_20814.
Proof. vm_refl. Qed.
Lemma D_20814 : decode_any W_20814 = Some (Auipc 3 1048560, 4%Z).
Proof. vm_refl. Qed.

Definition W_20818 : bv 32 := 0xf8c18193.
Lemma F_20818 : fetch_word Plain.M.loaded_segments (0x20878 : word) = Some W_20818.
Proof. vm_refl. Qed.
Lemma D_20818 : decode_any W_20818 = Some (OpImm ALU_ADD 3 3 3980, 4%Z).
Proof. vm_refl. Qed.

Definition W_2081c : bv 32 := 0x00010513.
Lemma F_2081c : fetch_word Plain.M.loaded_segments (0x2087c : word) = Some W_2081c.
Proof. vm_refl. Qed.
Lemma D_2081c : decode_any W_2081c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20820 : bv 32 := 0xfffdf597.
Lemma F_20820 : fetch_word Plain.M.loaded_segments (0x20880 : word) = Some W_20820.
Proof. vm_refl. Qed.
Lemma D_20820 : decode_any W_20820 = Some (Auipc 11 1048543, 4%Z).
Proof. vm_refl. Qed.

Definition W_20824 : bv 32 := 0x78058593.
Lemma F_20824 : fetch_word Plain.M.loaded_segments (0x20884 : word) = Some W_20824.
Proof. vm_refl. Qed.
Lemma D_20824 : decode_any W_20824 = Some (OpImm ALU_ADD 11 11 1920, 4%Z).
Proof. vm_refl. Qed.

Definition W_20828 : bv 32 := 0xff017113.
Lemma F_20828 : fetch_word Plain.M.loaded_segments (0x20888 : word) = Some W_20828.
Proof. vm_refl. Qed.
Lemma D_20828 : decode_any W_20828 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_2082c : bv 32 := 0x0040006f.
Lemma F_2082c : fetch_word Plain.M.loaded_segments (0x2088c : word) = Some W_2082c.
Proof. vm_refl. Qed.
Lemma D_2082c : decode_any W_2082c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_20830 : bv 32 := 0x00052583.
Lemma F_20830 : fetch_word Plain.M.loaded_segments (0x20890 : word) = Some W_20830.
Proof. vm_refl. Qed.
Lemma D_20830 : decode_any W_20830 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20834 : bv 32 := 0x00043617.
Lemma F_20834 : fetch_word Plain.M.loaded_segments (0x20894 : word) = Some W_20834.
Proof. vm_refl. Qed.
Lemma D_20834 : decode_any W_20834 = Some (Auipc 12 67, 4%Z).
Proof. vm_refl. Qed.

Definition W_20838 : bv 32 := 0x00043697.
Lemma F_20838 : fetch_word Plain.M.loaded_segments (0x20898 : word) = Some W_20838.
Proof. vm_refl. Qed.
Lemma D_20838 : decode_any W_20838 = Some (Auipc 13 67, 4%Z).
Proof. vm_refl. Qed.

Definition W_2083c : bv 32 := 0x00043717.
Lemma F_2083c : fetch_word Plain.M.loaded_segments (0x2089c : word) = Some W_2083c.
Proof. vm_refl. Qed.
Lemma D_2083c : decode_any W_2083c = Some (Auipc 14 67, 4%Z).
Proof. vm_refl. Qed.

Definition W_20840 : bv 32 := 0x49c63783.
Lemma F_20840 : fetch_word Plain.M.loaded_segments (0x208a0 : word) = Some W_20840.
Proof. vm_refl. Qed.
Lemma D_20840 : decode_any W_20840 = Some (Load SZ8 true 15 12 1180, 4%Z).
Proof. vm_refl. Qed.

Definition W_20844 : bv 32 := 0x4a06b683.
Lemma F_20844 : fetch_word Plain.M.loaded_segments (0x208a4 : word) = Some W_20844.
Proof. vm_refl. Qed.
Lemma D_20844 : decode_any W_20844 = Some (Load SZ8 true 13 13 1184, 4%Z).
Proof. vm_refl. Qed.

Definition W_20848 : bv 32 := 0x4a473703.
Lemma F_20848 : fetch_word Plain.M.loaded_segments (0x208a8 : word) = Some W_20848.
Proof. vm_refl. Qed.
Lemma D_20848 : decode_any W_20848 = Some (Load SZ8 true 14 14 1188, 4%Z).
Proof. vm_refl. Qed.

Definition W_2084c : bv 32 := 0x00850613.
Lemma F_2084c : fetch_word Plain.M.loaded_segments (0x208ac : word) = Some W_2084c.
Proof. vm_refl. Qed.
Lemma D_2084c : decode_any W_2084c = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_20850 : bv 32 := 0x00078513.
Lemma F_20850 : fetch_word Plain.M.loaded_segments (0x208b0 : word) = Some W_20850.
Proof. vm_refl. Qed.
Lemma D_20850 : decode_any W_20850 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20854 : bv 32 := 0x00000793.
Lemma F_20854 : fetch_word Plain.M.loaded_segments (0x208b4 : word) = Some W_20854.
Proof. vm_refl. Qed.
Lemma D_20854 : decode_any W_20854 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20858 : bv 32 := 0x1c82e06f.
Lemma F_20858 : fetch_word Plain.M.loaded_segments (0x208b8 : word) = Some W_20858.
Proof. vm_refl. Qed.
Lemma D_20858 : decode_any W_20858 = Some (Jal 0 188872, 4%Z).
Proof. vm_refl. Qed.

Definition W_2085c : bv 32 := 0xff010113.
Lemma F_2085c : fetch_word Plain.M.loaded_segments (0x208bc : word) = Some W_2085c.
Proof. vm_refl. Qed.
Lemma D_2085c : decode_any W_2085c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_20860 : bv 32 := 0x00113423.
Lemma F_20860 : fetch_word Plain.M.loaded_segments (0x208c0 : word) = Some W_20860.
Proof. vm_refl. Qed.
Lemma D_20860 : decode_any W_20860 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_20864 : bv 32 := 0x00813023.
Lemma F_20864 : fetch_word Plain.M.loaded_segments (0x208c4 : word) = Some W_20864.
Proof. vm_refl. Qed.
Lemma D_20864 : decode_any W_20864 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20868 : bv 32 := 0x01010413.
Lemma F_20868 : fetch_word Plain.M.loaded_segments (0x208c8 : word) = Some W_20868.
Proof. vm_refl. Qed.
Lemma D_20868 : decode_any W_20868 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2086c : bv 32 := 0x00045517.
Lemma F_2086c : fetch_word Plain.M.loaded_segments (0x208cc : word) = Some W_2086c.
Proof. vm_refl. Qed.
Lemma D_2086c : decode_any W_2086c = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_20870 : bv 32 := 0x8d450513.
Lemma F_20870 : fetch_word Plain.M.loaded_segments (0x208d0 : word) = Some W_20870.
Proof. vm_refl. Qed.
Lemma D_20870 : decode_any W_20870 = Some (OpImm ALU_ADD 10 10 2260, 4%Z).
Proof. vm_refl. Qed.

Definition W_20874 : bv 32 := 0x00054503.
Lemma F_20874 : fetch_word Plain.M.loaded_segments (0x208d4 : word) = Some W_20874.
Proof. vm_refl. Qed.
Lemma D_20874 : decode_any W_20874 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20878 : bv 32 := 0x00157513.
Lemma F_20878 : fetch_word Plain.M.loaded_segments (0x208d8 : word) = Some W_20878.
Proof. vm_refl. Qed.
Lemma D_20878 : decode_any W_20878 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2087c : bv 32 := 0x00050663.
Lemma F_2087c : fetch_word Plain.M.loaded_segments (0x208dc : word) = Some W_2087c.
Proof. vm_refl. Qed.
Lemma D_2087c : decode_any W_2087c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_20888 : bv 32 := 0x00045517.
Lemma F_20888 : fetch_word Plain.M.loaded_segments (0x208e8 : word) = Some W_20888.
Proof. vm_refl. Qed.
Lemma D_20888 : decode_any W_20888 = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_2088c : bv 32 := 0x8b850593.
Lemma F_2088c : fetch_word Plain.M.loaded_segments (0x208ec : word) = Some W_2088c.
Proof. vm_refl. Qed.
Lemma D_2088c : decode_any W_2088c = Some (OpImm ALU_ADD 11 10 2232, 4%Z).
Proof. vm_refl. Qed.

Definition W_20890 : bv 32 := 0x00100513.
Lemma F_20890 : fetch_word Plain.M.loaded_segments (0x208f0 : word) = Some W_20890.
Proof. vm_refl. Qed.
Lemma D_20890 : decode_any W_20890 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_20894 : bv 32 := 0x00a58023.
Lemma F_20894 : fetch_word Plain.M.loaded_segments (0x208f4 : word) = Some W_20894.
Proof. vm_refl. Qed.
Lemma D_20894 : decode_any W_20894 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20898 : bv 32 := 0x00043517.
Lemma F_20898 : fetch_word Plain.M.loaded_segments (0x208f8 : word) = Some W_20898.
Proof. vm_refl. Qed.
Lemma D_20898 : decode_any W_20898 = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

Definition W_2089c : bv 32 := 0x45053503.
Lemma F_2089c : fetch_word Plain.M.loaded_segments (0x208fc : word) = Some W_2089c.
Proof. vm_refl. Qed.
Lemma D_2089c : decode_any W_2089c = Some (Load SZ8 true 10 10 1104, 4%Z).
Proof. vm_refl. Qed.

Definition W_208a0 : bv 32 := 0x02050063.
Lemma F_208a0 : fetch_word Plain.M.loaded_segments (0x20900 : word) = Some W_208a0.
Proof. vm_refl. Qed.
Lemma D_208a0 : decode_any W_208a0 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_208c0 : bv 32 := 0x00813083.
Lemma F_208c0 : fetch_word Plain.M.loaded_segments (0x20920 : word) = Some W_208c0.
Proof. vm_refl. Qed.
Lemma D_208c0 : decode_any W_208c0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_208c4 : bv 32 := 0x00013403.
Lemma F_208c4 : fetch_word Plain.M.loaded_segments (0x20924 : word) = Some W_208c4.
Proof. vm_refl. Qed.
Lemma D_208c4 : decode_any W_208c4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_208c8 : bv 32 := 0x01010113.
Lemma F_208c8 : fetch_word Plain.M.loaded_segments (0x20928 : word) = Some W_208c8.
Proof. vm_refl. Qed.
Lemma D_208c8 : decode_any W_208c8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_208cc : bv 32 := 0x00008067.
Lemma F_208cc : fetch_word Plain.M.loaded_segments (0x2092c : word) = Some W_208cc.
Proof. vm_refl. Qed.
Lemma D_208cc : decode_any W_208cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_208d0 : bv 32 := 0xff010113.
Lemma F_208d0 : fetch_word Plain.M.loaded_segments (0x20930 : word) = Some W_208d0.
Proof. vm_refl. Qed.
Lemma D_208d0 : decode_any W_208d0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_208d4 : bv 32 := 0x00113423.
Lemma F_208d4 : fetch_word Plain.M.loaded_segments (0x20934 : word) = Some W_208d4.
Proof. vm_refl. Qed.
Lemma D_208d4 : decode_any W_208d4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_208d8 : bv 32 := 0x00813023.
Lemma F_208d8 : fetch_word Plain.M.loaded_segments (0x20938 : word) = Some W_208d8.
Proof. vm_refl. Qed.
Lemma D_208d8 : decode_any W_208d8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_208dc : bv 32 := 0x01010413.
Lemma F_208dc : fetch_word Plain.M.loaded_segments (0x2093c : word) = Some W_208dc.
Proof. vm_refl. Qed.
Lemma D_208dc : decode_any W_208dc = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_208e0 : bv 32 := 0x00045517.
Lemma F_208e0 : fetch_word Plain.M.loaded_segments (0x20940 : word) = Some W_208e0.
Proof. vm_refl. Qed.
Lemma D_208e0 : decode_any W_208e0 = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_208e4 : bv 32 := 0x8a850513.
Lemma F_208e4 : fetch_word Plain.M.loaded_segments (0x20944 : word) = Some W_208e4.
Proof. vm_refl. Qed.
Lemma D_208e4 : decode_any W_208e4 = Some (OpImm ALU_ADD 10 10 2216, 4%Z).
Proof. vm_refl. Qed.

Definition W_208e8 : bv 32 := 0x00054503.
Lemma F_208e8 : fetch_word Plain.M.loaded_segments (0x20948 : word) = Some W_208e8.
Proof. vm_refl. Qed.
Lemma D_208e8 : decode_any W_208e8 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_208ec : bv 32 := 0x00157513.
Lemma F_208ec : fetch_word Plain.M.loaded_segments (0x2094c : word) = Some W_208ec.
Proof. vm_refl. Qed.
Lemma D_208ec : decode_any W_208ec = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_208f0 : bv 32 := 0x00050663.
Lemma F_208f0 : fetch_word Plain.M.loaded_segments (0x20950 : word) = Some W_208f0.
Proof. vm_refl. Qed.
Lemma D_208f0 : decode_any W_208f0 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_208fc : bv 32 := 0x00045517.
Lemma F_208fc : fetch_word Plain.M.loaded_segments (0x2095c : word) = Some W_208fc.
Proof. vm_refl. Qed.
Lemma D_208fc : decode_any W_208fc = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_20900 : bv 32 := 0x88c50593.
Lemma F_20900 : fetch_word Plain.M.loaded_segments (0x20960 : word) = Some W_20900.
Proof. vm_refl. Qed.
Lemma D_20900 : decode_any W_20900 = Some (OpImm ALU_ADD 11 10 2188, 4%Z).
Proof. vm_refl. Qed.

Definition W_20904 : bv 32 := 0x00100513.
Lemma F_20904 : fetch_word Plain.M.loaded_segments (0x20964 : word) = Some W_20904.
Proof. vm_refl. Qed.
Lemma D_20904 : decode_any W_20904 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_20908 : bv 32 := 0x00a58023.
Lemma F_20908 : fetch_word Plain.M.loaded_segments (0x20968 : word) = Some W_20908.
Proof. vm_refl. Qed.
Lemma D_20908 : decode_any W_20908 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2090c : bv 32 := 0x00043517.
Lemma F_2090c : fetch_word Plain.M.loaded_segments (0x2096c : word) = Some W_2090c.
Proof. vm_refl. Qed.
Lemma D_2090c : decode_any W_2090c = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

Definition W_20910 : bv 32 := 0x3e453503.
Lemma F_20910 : fetch_word Plain.M.loaded_segments (0x20970 : word) = Some W_20910.
Proof. vm_refl. Qed.
Lemma D_20910 : decode_any W_20910 = Some (Load SZ8 true 10 10 996, 4%Z).
Proof. vm_refl. Qed.

Definition W_20914 : bv 32 := 0x00050e63.
Lemma F_20914 : fetch_word Plain.M.loaded_segments (0x20974 : word) = Some W_20914.
Proof. vm_refl. Qed.
Lemma D_20914 : decode_any W_20914 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_20918 : bv 32 := 0x0040006f.
Lemma F_20918 : fetch_word Plain.M.loaded_segments (0x20978 : word) = Some W_20918.
Proof. vm_refl. Qed.
Lemma D_20918 : decode_any W_20918 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_2091c : bv 32 := 0x00044517.
Lemma F_2091c : fetch_word Plain.M.loaded_segments (0x2097c : word) = Some W_2091c.
Proof. vm_refl. Qed.
Lemma D_2091c : decode_any W_2091c = Some (Auipc 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_20920 : bv 32 := 0x53450513.
Lemma F_20920 : fetch_word Plain.M.loaded_segments (0x20980 : word) = Some W_20920.
Proof. vm_refl. Qed.
Lemma D_20920 : decode_any W_20920 = Some (OpImm ALU_ADD 10 10 1332, 4%Z).
Proof. vm_refl. Qed.

Definition W_20924 : bv 32 := 0x00053503.
Lemma F_20924 : fetch_word Plain.M.loaded_segments (0x20984 : word) = Some W_20924.
Proof. vm_refl. Qed.
Lemma D_20924 : decode_any W_20924 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20928 : bv 32 := 0x6402e0ef.
Lemma F_20928 : fetch_word Plain.M.loaded_segments (0x20988 : word) = Some W_20928.
Proof. vm_refl. Qed.
Lemma D_20928 : decode_any W_20928 = Some (Jal 1 190016, 4%Z).
Proof. vm_refl. Qed.

Definition W_2092c : bv 32 := 0x0040006f.
Lemma F_2092c : fetch_word Plain.M.loaded_segments (0x2098c : word) = Some W_2092c.
Proof. vm_refl. Qed.
Lemma D_2092c : decode_any W_2092c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_20930 : bv 32 := 0x00043517.
Lemma F_20930 : fetch_word Plain.M.loaded_segments (0x20990 : word) = Some W_20930.
Proof. vm_refl. Qed.
Lemma D_20930 : decode_any W_20930 = Some (Auipc 10 67, 4%Z).
Proof. vm_refl. Qed.

Definition W_20934 : bv 32 := 0x3c853503.
Lemma F_20934 : fetch_word Plain.M.loaded_segments (0x20994 : word) = Some W_20934.
Proof. vm_refl. Qed.
Lemma D_20934 : decode_any W_20934 = Some (Load SZ8 true 10 10 968, 4%Z).
Proof. vm_refl. Qed.

Definition W_20938 : bv 32 := 0x00050c63.
Lemma F_20938 : fetch_word Plain.M.loaded_segments (0x20998 : word) = Some W_20938.
Proof. vm_refl. Qed.
Lemma D_20938 : decode_any W_20938 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_20950 : bv 32 := 0x00813083.
Lemma F_20950 : fetch_word Plain.M.loaded_segments (0x209b0 : word) = Some W_20950.
Proof. vm_refl. Qed.
Lemma D_20950 : decode_any W_20950 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_20954 : bv 32 := 0x00013403.
Lemma F_20954 : fetch_word Plain.M.loaded_segments (0x209b4 : word) = Some W_20954.
Proof. vm_refl. Qed.
Lemma D_20954 : decode_any W_20954 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20958 : bv 32 := 0x01010113.
Lemma F_20958 : fetch_word Plain.M.loaded_segments (0x209b8 : word) = Some W_20958.
Proof. vm_refl. Qed.
Lemma D_20958 : decode_any W_20958 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2095c : bv 32 := 0x00008067.
Lemma F_2095c : fetch_word Plain.M.loaded_segments (0x209bc : word) = Some W_2095c.
Proof. vm_refl. Qed.
Lemma D_2095c : decode_any W_2095c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20d88 : bv 32 := 0x00054517.
Lemma F_20d88 : fetch_word Plain.M.loaded_segments (0x20de8 : word) = Some W_20d88.
Proof. vm_refl. Qed.
Lemma D_20d88 : decode_any W_20d88 = Some (Auipc 10 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_20d8c : bv 32 := 0x40c54503.
Lemma F_20d8c : fetch_word Plain.M.loaded_segments (0x20dec : word) = Some W_20d8c.
Proof. vm_refl. Qed.
Lemma D_20d8c : decode_any W_20d8c = Some (Load SZ1 false 10 10 1036, 4%Z).
Proof. vm_refl. Qed.

Definition W_20d90 : bv 32 := 0x00051463.
Lemma F_20d90 : fetch_word Plain.M.loaded_segments (0x20df0 : word) = Some W_20d90.
Proof. vm_refl. Qed.
Lemma D_20d90 : decode_any W_20d90 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_20d94 : bv 32 := 0x00008067.
Lemma F_20d94 : fetch_word Plain.M.loaded_segments (0x20df4 : word) = Some W_20d94.
Proof. vm_refl. Qed.
Lemma D_20d94 : decode_any W_20d94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
