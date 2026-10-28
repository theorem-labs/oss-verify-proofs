(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)


From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_20814 : bv 32 := 0xffff0197.
Lemma F_20814 : fetch_word Ubsan.M.loaded_segments (0x20a38 : word) = Some W_20814.
Proof. vm_refl. Qed.
Lemma D_20814 : decode_any W_20814 = Some (Auipc 3 1048560, 4%Z).
Proof. vm_refl. Qed.

Definition W_20818 : bv 32 := 0xdc818193.
Lemma F_20818 : fetch_word Ubsan.M.loaded_segments (0x20a3c : word) = Some W_20818.
Proof. vm_refl. Qed.
Lemma D_20818 : decode_any W_20818 = Some (OpImm ALU_ADD 3 3 3528, 4%Z).
Proof. vm_refl. Qed.

Definition W_2081c : bv 32 := 0x00010513.
Lemma F_2081c : fetch_word Ubsan.M.loaded_segments (0x20a40 : word) = Some W_2081c.
Proof. vm_refl. Qed.
Lemma D_2081c : decode_any W_2081c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20820 : bv 32 := 0xfffdf597.
Lemma F_20820 : fetch_word Ubsan.M.loaded_segments (0x20a44 : word) = Some W_20820.
Proof. vm_refl. Qed.
Lemma D_20820 : decode_any W_20820 = Some (Auipc 11 1048543, 4%Z).
Proof. vm_refl. Qed.

Definition W_20824 : bv 32 := 0x5bc58593.
Lemma F_20824 : fetch_word Ubsan.M.loaded_segments (0x20a48 : word) = Some W_20824.
Proof. vm_refl. Qed.
Lemma D_20824 : decode_any W_20824 = Some (OpImm ALU_ADD 11 11 1468, 4%Z).
Proof. vm_refl. Qed.

Definition W_20828 : bv 32 := 0xff017113.
Lemma F_20828 : fetch_word Ubsan.M.loaded_segments (0x20a4c : word) = Some W_20828.
Proof. vm_refl. Qed.
Lemma D_20828 : decode_any W_20828 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_2082c : bv 32 := 0x0040006f.
Lemma F_2082c : fetch_word Ubsan.M.loaded_segments (0x20a50 : word) = Some W_2082c.
Proof. vm_refl. Qed.
Lemma D_2082c : decode_any W_2082c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_20830 : bv 32 := 0x00052583.
Lemma F_20830 : fetch_word Ubsan.M.loaded_segments (0x20a54 : word) = Some W_20830.
Proof. vm_refl. Qed.
Lemma D_20830 : decode_any W_20830 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20834 : bv 32 := 0x00045617.
Lemma F_20834 : fetch_word Ubsan.M.loaded_segments (0x20a58 : word) = Some W_20834.
Proof. vm_refl. Qed.
Lemma D_20834 : decode_any W_20834 = Some (Auipc 12 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_20838 : bv 32 := 0x00045697.
Lemma F_20838 : fetch_word Ubsan.M.loaded_segments (0x20a5c : word) = Some W_20838.
Proof. vm_refl. Qed.
Lemma D_20838 : decode_any W_20838 = Some (Auipc 13 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_2083c : bv 32 := 0x00045717.
Lemma F_2083c : fetch_word Ubsan.M.loaded_segments (0x20a60 : word) = Some W_2083c.
Proof. vm_refl. Qed.
Lemma D_2083c : decode_any W_2083c = Some (Auipc 14 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_20840 : bv 32 := 0xe2063783.
Lemma F_20840 : fetch_word Ubsan.M.loaded_segments (0x20a64 : word) = Some W_20840.
Proof. vm_refl. Qed.
Lemma D_20840 : decode_any W_20840 = Some (Load SZ8 true 15 12 3616, 4%Z).
Proof. vm_refl. Qed.

Definition W_20844 : bv 32 := 0xe246b683.
Lemma F_20844 : fetch_word Ubsan.M.loaded_segments (0x20a68 : word) = Some W_20844.
Proof. vm_refl. Qed.
Lemma D_20844 : decode_any W_20844 = Some (Load SZ8 true 13 13 3620, 4%Z).
Proof. vm_refl. Qed.

Definition W_20848 : bv 32 := 0xe2873703.
Lemma F_20848 : fetch_word Ubsan.M.loaded_segments (0x20a6c : word) = Some W_20848.
Proof. vm_refl. Qed.
Lemma D_20848 : decode_any W_20848 = Some (Load SZ8 true 14 14 3624, 4%Z).
Proof. vm_refl. Qed.

Definition W_2084c : bv 32 := 0x00850613.
Lemma F_2084c : fetch_word Ubsan.M.loaded_segments (0x20a70 : word) = Some W_2084c.
Proof. vm_refl. Qed.
Lemma D_2084c : decode_any W_2084c = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_20850 : bv 32 := 0x00078513.
Lemma F_20850 : fetch_word Ubsan.M.loaded_segments (0x20a74 : word) = Some W_20850.
Proof. vm_refl. Qed.
Lemma D_20850 : decode_any W_20850 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20854 : bv 32 := 0x00000793.
Lemma F_20854 : fetch_word Ubsan.M.loaded_segments (0x20a78 : word) = Some W_20854.
Proof. vm_refl. Qed.
Lemma D_20854 : decode_any W_20854 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20858 : bv 32 := 0x58d2f06f.
Lemma F_20858 : fetch_word Ubsan.M.loaded_segments (0x20a7c : word) = Some W_20858.
Proof. vm_refl. Qed.
Lemma D_20858 : decode_any W_20858 = Some (Jal 0 195980, 4%Z).
Proof. vm_refl. Qed.

Definition W_2085c : bv 32 := 0xff010113.
Lemma F_2085c : fetch_word Ubsan.M.loaded_segments (0x20a80 : word) = Some W_2085c.
Proof. vm_refl. Qed.
Lemma D_2085c : decode_any W_2085c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_20860 : bv 32 := 0x00113423.
Lemma F_20860 : fetch_word Ubsan.M.loaded_segments (0x20a84 : word) = Some W_20860.
Proof. vm_refl. Qed.
Lemma D_20860 : decode_any W_20860 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_20864 : bv 32 := 0x00813023.
Lemma F_20864 : fetch_word Ubsan.M.loaded_segments (0x20a88 : word) = Some W_20864.
Proof. vm_refl. Qed.
Lemma D_20864 : decode_any W_20864 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20868 : bv 32 := 0x01010413.
Lemma F_20868 : fetch_word Ubsan.M.loaded_segments (0x20a8c : word) = Some W_20868.
Proof. vm_refl. Qed.
Lemma D_20868 : decode_any W_20868 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2086c : bv 32 := 0x00046517.
Lemma F_2086c : fetch_word Ubsan.M.loaded_segments (0x20a90 : word) = Some W_2086c.
Proof. vm_refl. Qed.
Lemma D_2086c : decode_any W_2086c = Some (Auipc 10 70, 4%Z).
Proof. vm_refl. Qed.

Definition W_20870 : bv 32 := 0x4a050513.
Lemma F_20870 : fetch_word Ubsan.M.loaded_segments (0x20a94 : word) = Some W_20870.
Proof. vm_refl. Qed.
Lemma D_20870 : decode_any W_20870 = Some (OpImm ALU_ADD 10 10 1184, 4%Z).
Proof. vm_refl. Qed.

Definition W_20874 : bv 32 := 0x00054503.
Lemma F_20874 : fetch_word Ubsan.M.loaded_segments (0x20a98 : word) = Some W_20874.
Proof. vm_refl. Qed.
Lemma D_20874 : decode_any W_20874 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20878 : bv 32 := 0x00157513.
Lemma F_20878 : fetch_word Ubsan.M.loaded_segments (0x20a9c : word) = Some W_20878.
Proof. vm_refl. Qed.
Lemma D_20878 : decode_any W_20878 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_2087c : bv 32 := 0x00050663.
Lemma F_2087c : fetch_word Ubsan.M.loaded_segments (0x20aa0 : word) = Some W_2087c.
Proof. vm_refl. Qed.
Lemma D_2087c : decode_any W_2087c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_20888 : bv 32 := 0x00046517.
Lemma F_20888 : fetch_word Ubsan.M.loaded_segments (0x20aac : word) = Some W_20888.
Proof. vm_refl. Qed.
Lemma D_20888 : decode_any W_20888 = Some (Auipc 10 70, 4%Z).
Proof. vm_refl. Qed.

Definition W_2088c : bv 32 := 0x48450593.
Lemma F_2088c : fetch_word Ubsan.M.loaded_segments (0x20ab0 : word) = Some W_2088c.
Proof. vm_refl. Qed.
Lemma D_2088c : decode_any W_2088c = Some (OpImm ALU_ADD 11 10 1156, 4%Z).
Proof. vm_refl. Qed.

Definition W_20890 : bv 32 := 0x00100513.
Lemma F_20890 : fetch_word Ubsan.M.loaded_segments (0x20ab4 : word) = Some W_20890.
Proof. vm_refl. Qed.
Lemma D_20890 : decode_any W_20890 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_20894 : bv 32 := 0x00a58023.
Lemma F_20894 : fetch_word Ubsan.M.loaded_segments (0x20ab8 : word) = Some W_20894.
Proof. vm_refl. Qed.
Lemma D_20894 : decode_any W_20894 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20898 : bv 32 := 0x00045517.
Lemma F_20898 : fetch_word Ubsan.M.loaded_segments (0x20abc : word) = Some W_20898.
Proof. vm_refl. Qed.
Lemma D_20898 : decode_any W_20898 = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_2089c : bv 32 := 0xdd453503.
Lemma F_2089c : fetch_word Ubsan.M.loaded_segments (0x20ac0 : word) = Some W_2089c.
Proof. vm_refl. Qed.
Lemma D_2089c : decode_any W_2089c = Some (Load SZ8 true 10 10 3540, 4%Z).
Proof. vm_refl. Qed.

Definition W_208a0 : bv 32 := 0x02050063.
Lemma F_208a0 : fetch_word Ubsan.M.loaded_segments (0x20ac4 : word) = Some W_208a0.
Proof. vm_refl. Qed.
Lemma D_208a0 : decode_any W_208a0 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_208c0 : bv 32 := 0x00813083.
Lemma F_208c0 : fetch_word Ubsan.M.loaded_segments (0x20ae4 : word) = Some W_208c0.
Proof. vm_refl. Qed.
Lemma D_208c0 : decode_any W_208c0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_208c4 : bv 32 := 0x00013403.
Lemma F_208c4 : fetch_word Ubsan.M.loaded_segments (0x20ae8 : word) = Some W_208c4.
Proof. vm_refl. Qed.
Lemma D_208c4 : decode_any W_208c4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_208c8 : bv 32 := 0x01010113.
Lemma F_208c8 : fetch_word Ubsan.M.loaded_segments (0x20aec : word) = Some W_208c8.
Proof. vm_refl. Qed.
Lemma D_208c8 : decode_any W_208c8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_208cc : bv 32 := 0x00008067.
Lemma F_208cc : fetch_word Ubsan.M.loaded_segments (0x20af0 : word) = Some W_208cc.
Proof. vm_refl. Qed.
Lemma D_208cc : decode_any W_208cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_208d0 : bv 32 := 0xff010113.
Lemma F_208d0 : fetch_word Ubsan.M.loaded_segments (0x20af4 : word) = Some W_208d0.
Proof. vm_refl. Qed.
Lemma D_208d0 : decode_any W_208d0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_208d4 : bv 32 := 0x00113423.
Lemma F_208d4 : fetch_word Ubsan.M.loaded_segments (0x20af8 : word) = Some W_208d4.
Proof. vm_refl. Qed.
Lemma D_208d4 : decode_any W_208d4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_208d8 : bv 32 := 0x00813023.
Lemma F_208d8 : fetch_word Ubsan.M.loaded_segments (0x20afc : word) = Some W_208d8.
Proof. vm_refl. Qed.
Lemma D_208d8 : decode_any W_208d8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_208dc : bv 32 := 0x01010413.
Lemma F_208dc : fetch_word Ubsan.M.loaded_segments (0x20b00 : word) = Some W_208dc.
Proof. vm_refl. Qed.
Lemma D_208dc : decode_any W_208dc = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_208e0 : bv 32 := 0x00046517.
Lemma F_208e0 : fetch_word Ubsan.M.loaded_segments (0x20b04 : word) = Some W_208e0.
Proof. vm_refl. Qed.
Lemma D_208e0 : decode_any W_208e0 = Some (Auipc 10 70, 4%Z).
Proof. vm_refl. Qed.

Definition W_208e4 : bv 32 := 0x47450513.
Lemma F_208e4 : fetch_word Ubsan.M.loaded_segments (0x20b08 : word) = Some W_208e4.
Proof. vm_refl. Qed.
Lemma D_208e4 : decode_any W_208e4 = Some (OpImm ALU_ADD 10 10 1140, 4%Z).
Proof. vm_refl. Qed.

Definition W_208e8 : bv 32 := 0x00054503.
Lemma F_208e8 : fetch_word Ubsan.M.loaded_segments (0x20b0c : word) = Some W_208e8.
Proof. vm_refl. Qed.
Lemma D_208e8 : decode_any W_208e8 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_208ec : bv 32 := 0x00157513.
Lemma F_208ec : fetch_word Ubsan.M.loaded_segments (0x20b10 : word) = Some W_208ec.
Proof. vm_refl. Qed.
Lemma D_208ec : decode_any W_208ec = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_208f0 : bv 32 := 0x00050663.
Lemma F_208f0 : fetch_word Ubsan.M.loaded_segments (0x20b14 : word) = Some W_208f0.
Proof. vm_refl. Qed.
Lemma D_208f0 : decode_any W_208f0 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_208fc : bv 32 := 0x00046517.
Lemma F_208fc : fetch_word Ubsan.M.loaded_segments (0x20b20 : word) = Some W_208fc.
Proof. vm_refl. Qed.
Lemma D_208fc : decode_any W_208fc = Some (Auipc 10 70, 4%Z).
Proof. vm_refl. Qed.

Definition W_20900 : bv 32 := 0x45850593.
Lemma F_20900 : fetch_word Ubsan.M.loaded_segments (0x20b24 : word) = Some W_20900.
Proof. vm_refl. Qed.
Lemma D_20900 : decode_any W_20900 = Some (OpImm ALU_ADD 11 10 1112, 4%Z).
Proof. vm_refl. Qed.

Definition W_20904 : bv 32 := 0x00100513.
Lemma F_20904 : fetch_word Ubsan.M.loaded_segments (0x20b28 : word) = Some W_20904.
Proof. vm_refl. Qed.
Lemma D_20904 : decode_any W_20904 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_20908 : bv 32 := 0x00a58023.
Lemma F_20908 : fetch_word Ubsan.M.loaded_segments (0x20b2c : word) = Some W_20908.
Proof. vm_refl. Qed.
Lemma D_20908 : decode_any W_20908 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_2090c : bv 32 := 0x00045517.
Lemma F_2090c : fetch_word Ubsan.M.loaded_segments (0x20b30 : word) = Some W_2090c.
Proof. vm_refl. Qed.
Lemma D_2090c : decode_any W_2090c = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_20910 : bv 32 := 0xd6853503.
Lemma F_20910 : fetch_word Ubsan.M.loaded_segments (0x20b34 : word) = Some W_20910.
Proof. vm_refl. Qed.
Lemma D_20910 : decode_any W_20910 = Some (Load SZ8 true 10 10 3432, 4%Z).
Proof. vm_refl. Qed.

Definition W_20914 : bv 32 := 0x00050e63.
Lemma F_20914 : fetch_word Ubsan.M.loaded_segments (0x20b38 : word) = Some W_20914.
Proof. vm_refl. Qed.
Lemma D_20914 : decode_any W_20914 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_20918 : bv 32 := 0x0040006f.
Lemma F_20918 : fetch_word Ubsan.M.loaded_segments (0x20b3c : word) = Some W_20918.
Proof. vm_refl. Qed.
Lemma D_20918 : decode_any W_20918 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_2091c : bv 32 := 0x00046517.
Lemma F_2091c : fetch_word Ubsan.M.loaded_segments (0x20b40 : word) = Some W_2091c.
Proof. vm_refl. Qed.
Lemma D_2091c : decode_any W_2091c = Some (Auipc 10 70, 4%Z).
Proof. vm_refl. Qed.

Definition W_20920 : bv 32 := 0xeb850513.
Lemma F_20920 : fetch_word Ubsan.M.loaded_segments (0x20b44 : word) = Some W_20920.
Proof. vm_refl. Qed.
Lemma D_20920 : decode_any W_20920 = Some (OpImm ALU_ADD 10 10 3768, 4%Z).
Proof. vm_refl. Qed.

Definition W_20924 : bv 32 := 0x00053503.
Lemma F_20924 : fetch_word Ubsan.M.loaded_segments (0x20b48 : word) = Some W_20924.
Proof. vm_refl. Qed.
Lemma D_20924 : decode_any W_20924 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20928 : bv 32 := 0x204300ef.
Lemma F_20928 : fetch_word Ubsan.M.loaded_segments (0x20b4c : word) = Some W_20928.
Proof. vm_refl. Qed.
Lemma D_20928 : decode_any W_20928 = Some (Jal 1 197124, 4%Z).
Proof. vm_refl. Qed.

Definition W_2092c : bv 32 := 0x0040006f.
Lemma F_2092c : fetch_word Ubsan.M.loaded_segments (0x20b50 : word) = Some W_2092c.
Proof. vm_refl. Qed.
Lemma D_2092c : decode_any W_2092c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_20930 : bv 32 := 0x00045517.
Lemma F_20930 : fetch_word Ubsan.M.loaded_segments (0x20b54 : word) = Some W_20930.
Proof. vm_refl. Qed.
Lemma D_20930 : decode_any W_20930 = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_20934 : bv 32 := 0xd4c53503.
Lemma F_20934 : fetch_word Ubsan.M.loaded_segments (0x20b58 : word) = Some W_20934.
Proof. vm_refl. Qed.
Lemma D_20934 : decode_any W_20934 = Some (Load SZ8 true 10 10 3404, 4%Z).
Proof. vm_refl. Qed.

Definition W_20938 : bv 32 := 0x00050c63.
Lemma F_20938 : fetch_word Ubsan.M.loaded_segments (0x20b5c : word) = Some W_20938.
Proof. vm_refl. Qed.
Lemma D_20938 : decode_any W_20938 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_20950 : bv 32 := 0x00813083.
Lemma F_20950 : fetch_word Ubsan.M.loaded_segments (0x20b74 : word) = Some W_20950.
Proof. vm_refl. Qed.
Lemma D_20950 : decode_any W_20950 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_20954 : bv 32 := 0x00013403.
Lemma F_20954 : fetch_word Ubsan.M.loaded_segments (0x20b78 : word) = Some W_20954.
Proof. vm_refl. Qed.
Lemma D_20954 : decode_any W_20954 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20958 : bv 32 := 0x01010113.
Lemma F_20958 : fetch_word Ubsan.M.loaded_segments (0x20b7c : word) = Some W_20958.
Proof. vm_refl. Qed.
Lemma D_20958 : decode_any W_20958 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_2095c : bv 32 := 0x00008067.
Lemma F_2095c : fetch_word Ubsan.M.loaded_segments (0x20b80 : word) = Some W_2095c.
Proof. vm_refl. Qed.
Lemma D_2095c : decode_any W_2095c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_20d88 : bv 32 := 0x00056517.
Lemma F_20d88 : fetch_word Ubsan.M.loaded_segments (0x20fac : word) = Some W_20d88.
Proof. vm_refl. Qed.
Lemma D_20d88 : decode_any W_20d88 = Some (Auipc 10 86, 4%Z).
Proof. vm_refl. Qed.

Definition W_20d8c : bv 32 := 0xfd854503.
Lemma F_20d8c : fetch_word Ubsan.M.loaded_segments (0x20fb0 : word) = Some W_20d8c.
Proof. vm_refl. Qed.
Lemma D_20d8c : decode_any W_20d8c = Some (Load SZ1 false 10 10 4056, 4%Z).
Proof. vm_refl. Qed.

Definition W_20d90 : bv 32 := 0x00051463.
Lemma F_20d90 : fetch_word Ubsan.M.loaded_segments (0x20fb4 : word) = Some W_20d90.
Proof. vm_refl. Qed.
Lemma D_20d90 : decode_any W_20d90 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_20d94 : bv 32 := 0x00008067.
Lemma F_20d94 : fetch_word Ubsan.M.loaded_segments (0x20fb8 : word) = Some W_20d94.
Proof. vm_refl. Qed.
Lemma D_20d94 : decode_any W_20d94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
