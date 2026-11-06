(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AB1u.v (donor image sha256 7093581aab04), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/AB1u.v (donor image sha256 43654a025fd0), with its module paths changed and its addresses moved to reac-pw/fuzz_role's ASan build. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/A/AB1u.v at 9f8c843f0e03 (image sha256 614cffc0864c), with its module paths changed and its addresses moved to reac-pw/fuzz_headamp's ASan build (image sha256 f3e0669d2819) by alreloc a5c53bb2bed4; comments kept as the source has them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_headamp/lib/A/AB1u.v at b0cad0df5623 (image sha256 f3e0669d2819), with its module names changed (A.Axyz -> AU.Yxyz) and its addresses moved to reac-pw/fuzz_headamp's ASan+UBSan build (image sha256 53edda9bdeeb) by derive_y.py b7b132fb12a7; the Modified-by lines above describe how lib/A/AB1u.v was made and quote its ASan-build values. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.reac_pw.fuzz_headamp.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.
Definition W_11d080 : bv 32 := 0x0035f693.
Lemma F_11d080 : fetch_word AsanUbsan.M.loaded_segments (0x95924 : word) = Some W_11d080.
Proof. vm_refl. Qed.
Lemma D_11d080 : decode_any W_11d080 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d084 : bv 32 := 0x10068863.
Lemma F_11d084 : fetch_word AsanUbsan.M.loaded_segments (0x95928 : word) = Some W_11d084.
Proof. vm_refl. Qed.
Lemma D_11d084 : decode_any W_11d084 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d088 : bv 32 := 0x02060e63.
Lemma F_11d088 : fetch_word AsanUbsan.M.loaded_segments (0x9592c : word) = Some W_11d088.
Proof. vm_refl. Qed.
Lemma D_11d088 : decode_any W_11d088 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d08c : bv 32 := 0x00158713.
Lemma F_11d08c : fetch_word AsanUbsan.M.loaded_segments (0x95930 : word) = Some W_11d08c.
Proof. vm_refl. Qed.
Lemma D_11d08c : decode_any W_11d08c = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d090 : bv 32 := 0x00100793.
Lemma F_11d090 : fetch_word AsanUbsan.M.loaded_segments (0x95934 : word) = Some W_11d090.
Proof. vm_refl. Qed.
Lemma D_11d090 : decode_any W_11d090 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d094 : bv 32 := 0x00050693.
Lemma F_11d094 : fetch_word AsanUbsan.M.loaded_segments (0x95938 : word) = Some W_11d094.
Proof. vm_refl. Qed.
Lemma D_11d094 : decode_any W_11d094 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d098 : bv 32 := 0x0005c883.
Lemma F_11d098 : fetch_word AsanUbsan.M.loaded_segments (0x9593c : word) = Some W_11d098.
Proof. vm_refl. Qed.
Lemma D_11d098 : decode_any W_11d098 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d09c : bv 32 := 0x00060813.
Lemma F_11d09c : fetch_word AsanUbsan.M.loaded_segments (0x95940 : word) = Some W_11d09c.
Proof. vm_refl. Qed.
Lemma D_11d09c : decode_any W_11d09c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0a0 : bv 32 := 0x00158593.
Lemma F_11d0a0 : fetch_word AsanUbsan.M.loaded_segments (0x95944 : word) = Some W_11d0a0.
Proof. vm_refl. Qed.
Lemma D_11d0a0 : decode_any W_11d0a0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0a4 : bv 32 := 0x00377293.
Lemma F_11d0a4 : fetch_word AsanUbsan.M.loaded_segments (0x95948 : word) = Some W_11d0a4.
Proof. vm_refl. Qed.
Lemma D_11d0a4 : decode_any W_11d0a4 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0a8 : bv 32 := 0x01168023.
Lemma F_11d0a8 : fetch_word AsanUbsan.M.loaded_segments (0x9594c : word) = Some W_11d0a8.
Proof. vm_refl. Qed.
Lemma D_11d0a8 : decode_any W_11d0a8 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0ac : bv 32 := 0x00168693.
Lemma F_11d0ac : fetch_word AsanUbsan.M.loaded_segments (0x95950 : word) = Some W_11d0ac.
Proof. vm_refl. Qed.
Lemma D_11d0ac : decode_any W_11d0ac = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0b0 : bv 32 := 0xfff60613.
Lemma F_11d0b0 : fetch_word AsanUbsan.M.loaded_segments (0x95954 : word) = Some W_11d0b0.
Proof. vm_refl. Qed.
Lemma D_11d0b0 : decode_any W_11d0b0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0b4 : bv 32 := 0x00028a63.
Lemma F_11d0b4 : fetch_word AsanUbsan.M.loaded_segments (0x95958 : word) = Some W_11d0b4.
Proof. vm_refl. Qed.
Lemma D_11d0b4 : decode_any W_11d0b4 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0b8 : bv 32 := 0x00170713.
Lemma F_11d0b8 : fetch_word AsanUbsan.M.loaded_segments (0x9595c : word) = Some W_11d0b8.
Proof. vm_refl. Qed.
Lemma D_11d0b8 : decode_any W_11d0b8 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0bc : bv 32 := 0xfcf81ee3.
Lemma F_11d0bc : fetch_word AsanUbsan.M.loaded_segments (0x95960 : word) = Some W_11d0bc.
Proof. vm_refl. Qed.
Lemma D_11d0bc : decode_any W_11d0bc = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0c0 : bv 32 := 0x0080006f.
Lemma F_11d0c0 : fetch_word AsanUbsan.M.loaded_segments (0x95964 : word) = Some W_11d0c0.
Proof. vm_refl. Qed.
Lemma D_11d0c0 : decode_any W_11d0c0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0c4 : bv 32 := 0x00050693.
Lemma F_11d0c4 : fetch_word AsanUbsan.M.loaded_segments (0x95968 : word) = Some W_11d0c4.
Proof. vm_refl. Qed.
Lemma D_11d0c4 : decode_any W_11d0c4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0c8 : bv 32 := 0x0036f793.
Lemma F_11d0c8 : fetch_word AsanUbsan.M.loaded_segments (0x9596c : word) = Some W_11d0c8.
Proof. vm_refl. Qed.
Lemma D_11d0c8 : decode_any W_11d0c8 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0cc : bv 32 := 0x0c078a63.
Lemma F_11d0cc : fetch_word AsanUbsan.M.loaded_segments (0x95970 : word) = Some W_11d0cc.
Proof. vm_refl. Qed.
Lemma D_11d0cc : decode_any W_11d0cc = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0d0 : bv 32 := 0x02000713.
Lemma F_11d0d0 : fetch_word AsanUbsan.M.loaded_segments (0x95974 : word) = Some W_11d0d0.
Proof. vm_refl. Qed.
Lemma D_11d0d0 : decode_any W_11d0d0 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0d4 : bv 32 := 0x02e67063.
Lemma F_11d0d4 : fetch_word AsanUbsan.M.loaded_segments (0x95978 : word) = Some W_11d0d4.
Proof. vm_refl. Qed.
Lemma D_11d0d4 : decode_any W_11d0d4 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0d8 : bv 32 := 0x01000713.
Lemma F_11d0d8 : fetch_word AsanUbsan.M.loaded_segments (0x9597c : word) = Some W_11d0d8.
Proof. vm_refl. Qed.
Lemma D_11d0d8 : decode_any W_11d0d8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0dc : bv 32 := 0x24e67863.
Lemma F_11d0dc : fetch_word AsanUbsan.M.loaded_segments (0x95980 : word) = Some W_11d0dc.
Proof. vm_refl. Qed.
Lemma D_11d0dc : decode_any W_11d0dc = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0e0 : bv 32 := 0x00867713.
Lemma F_11d0e0 : fetch_word AsanUbsan.M.loaded_segments (0x95984 : word) = Some W_11d0e0.
Proof. vm_refl. Qed.
Lemma D_11d0e0 : decode_any W_11d0e0 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0e4 : bv 32 := 0x2c071e63.
Lemma F_11d0e4 : fetch_word AsanUbsan.M.loaded_segments (0x95988 : word) = Some W_11d0e4.
Proof. vm_refl. Qed.
Lemma D_11d0e4 : decode_any W_11d0e4 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0e8 : bv 32 := 0x00467713.
Lemma F_11d0e8 : fetch_word AsanUbsan.M.loaded_segments (0x9598c : word) = Some W_11d0e8.
Proof. vm_refl. Qed.
Lemma D_11d0e8 : decode_any W_11d0e8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0ec : bv 32 := 0x32071463.
Lemma F_11d0ec : fetch_word AsanUbsan.M.loaded_segments (0x95990 : word) = Some W_11d0ec.
Proof. vm_refl. Qed.
Lemma D_11d0ec : decode_any W_11d0ec = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0f0 : bv 32 := 0x3500006f.
Lemma F_11d0f0 : fetch_word AsanUbsan.M.loaded_segments (0x95994 : word) = Some W_11d0f0.
Proof. vm_refl. Qed.
Lemma D_11d0f0 : decode_any W_11d0f0 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0f4 : bv 32 := 0x0005a703.
Lemma F_11d0f4 : fetch_word AsanUbsan.M.loaded_segments (0x95998 : word) = Some W_11d0f4.
Proof. vm_refl. Qed.
Lemma D_11d0f4 : decode_any W_11d0f4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0f8 : bv 32 := 0x00300813.
Lemma F_11d0f8 : fetch_word AsanUbsan.M.loaded_segments (0x9599c : word) = Some W_11d0f8.
Proof. vm_refl. Qed.
Lemma D_11d0f8 : decode_any W_11d0f8 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d0fc : bv 32 := 0x11078e63.
Lemma F_11d0fc : fetch_word AsanUbsan.M.loaded_segments (0x959a0 : word) = Some W_11d0fc.
Proof. vm_refl. Qed.
Lemma D_11d0fc : decode_any W_11d0fc = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d100 : bv 32 := 0x00200813.
Lemma F_11d100 : fetch_word AsanUbsan.M.loaded_segments (0x959a4 : word) = Some W_11d100.
Proof. vm_refl. Qed.
Lemma D_11d100 : decode_any W_11d100 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d104 : bv 32 := 0x19079c63.
Lemma F_11d104 : fetch_word AsanUbsan.M.loaded_segments (0x959a8 : word) = Some W_11d104.
Proof. vm_refl. Qed.
Lemma D_11d104 : decode_any W_11d104 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d108 : bv 32 := 0x00875793.
Lemma F_11d108 : fetch_word AsanUbsan.M.loaded_segments (0x959ac : word) = Some W_11d108.
Proof. vm_refl. Qed.
Lemma D_11d108 : decode_any W_11d108 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d10c : bv 32 := 0xffe60613.
Lemma F_11d10c : fetch_word AsanUbsan.M.loaded_segments (0x959b0 : word) = Some W_11d10c.
Proof. vm_refl. Qed.
Lemma D_11d10c : decode_any W_11d10c = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d110 : bv 32 := 0x00e68023.
Lemma F_11d110 : fetch_word AsanUbsan.M.loaded_segments (0x959b4 : word) = Some W_11d110.
Proof. vm_refl. Qed.
Lemma D_11d110 : decode_any W_11d110 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d114 : bv 32 := 0x00f680a3.
Lemma F_11d114 : fetch_word AsanUbsan.M.loaded_segments (0x959b8 : word) = Some W_11d114.
Proof. vm_refl. Qed.
Lemma D_11d114 : decode_any W_11d114 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d118 : bv 32 := 0x00268693.
Lemma F_11d118 : fetch_word AsanUbsan.M.loaded_segments (0x959bc : word) = Some W_11d118.
Proof. vm_refl. Qed.
Lemma D_11d118 : decode_any W_11d118 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d11c : bv 32 := 0x01058593.
Lemma F_11d11c : fetch_word AsanUbsan.M.loaded_segments (0x959c0 : word) = Some W_11d11c.
Proof. vm_refl. Qed.
Lemma D_11d11c : decode_any W_11d11c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d120 : bv 32 := 0x01100793.
Lemma F_11d120 : fetch_word AsanUbsan.M.loaded_segments (0x959c4 : word) = Some W_11d120.
Proof. vm_refl. Qed.
Lemma D_11d120 : decode_any W_11d120 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d124 : bv 32 := 0x0107581b.
Lemma F_11d124 : fetch_word AsanUbsan.M.loaded_segments (0x959c8 : word) = Some W_11d124.
Proof. vm_refl. Qed.
Lemma D_11d124 : decode_any W_11d124 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d128 : bv 32 := 0xff45a883.
Lemma F_11d128 : fetch_word AsanUbsan.M.loaded_segments (0x959cc : word) = Some W_11d128.
Proof. vm_refl. Qed.
Lemma D_11d128 : decode_any W_11d128 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d12c : bv 32 := 0xff85a283.
Lemma F_11d12c : fetch_word AsanUbsan.M.loaded_segments (0x959d0 : word) = Some W_11d12c.
Proof. vm_refl. Qed.
Lemma D_11d12c : decode_any W_11d12c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d130 : bv 32 := 0xffc5a303.
Lemma F_11d130 : fetch_word AsanUbsan.M.loaded_segments (0x959d4 : word) = Some W_11d130.
Proof. vm_refl. Qed.
Lemma D_11d130 : decode_any W_11d130 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d134 : bv 32 := 0x0005a703.
Lemma F_11d134 : fetch_word AsanUbsan.M.loaded_segments (0x959d8 : word) = Some W_11d134.
Proof. vm_refl. Qed.
Lemma D_11d134 : decode_any W_11d134 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d138 : bv 32 := 0x01089393.
Lemma F_11d138 : fetch_word AsanUbsan.M.loaded_segments (0x959dc : word) = Some W_11d138.
Proof. vm_refl. Qed.
Lemma D_11d138 : decode_any W_11d138 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d13c : bv 32 := 0x0108d89b.
Lemma F_11d13c : fetch_word AsanUbsan.M.loaded_segments (0x959e0 : word) = Some W_11d13c.
Proof. vm_refl. Qed.
Lemma D_11d13c : decode_any W_11d13c = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d140 : bv 32 := 0x0103e833.
Lemma F_11d140 : fetch_word AsanUbsan.M.loaded_segments (0x959e4 : word) = Some W_11d140.
Proof. vm_refl. Qed.
Lemma D_11d140 : decode_any W_11d140 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d144 : bv 32 := 0x01029393.
Lemma F_11d144 : fetch_word AsanUbsan.M.loaded_segments (0x959e8 : word) = Some W_11d144.
Proof. vm_refl. Qed.
Lemma D_11d144 : decode_any W_11d144 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d148 : bv 32 := 0x0102d29b.
Lemma F_11d148 : fetch_word AsanUbsan.M.loaded_segments (0x959ec : word) = Some W_11d148.
Proof. vm_refl. Qed.
Lemma D_11d148 : decode_any W_11d148 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d14c : bv 32 := 0x0113e8b3.
Lemma F_11d14c : fetch_word AsanUbsan.M.loaded_segments (0x959f0 : word) = Some W_11d14c.
Proof. vm_refl. Qed.
Lemma D_11d14c : decode_any W_11d14c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d150 : bv 32 := 0x01031393.
Lemma F_11d150 : fetch_word AsanUbsan.M.loaded_segments (0x959f4 : word) = Some W_11d150.
Proof. vm_refl. Qed.
Lemma D_11d150 : decode_any W_11d150 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d154 : bv 32 := 0x0103531b.
Lemma F_11d154 : fetch_word AsanUbsan.M.loaded_segments (0x959f8 : word) = Some W_11d154.
Proof. vm_refl. Qed.
Lemma D_11d154 : decode_any W_11d154 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d158 : bv 32 := 0x0053e2b3.
Lemma F_11d158 : fetch_word AsanUbsan.M.loaded_segments (0x959fc : word) = Some W_11d158.
Proof. vm_refl. Qed.
Lemma D_11d158 : decode_any W_11d158 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d15c : bv 32 := 0x01071393.
Lemma F_11d15c : fetch_word AsanUbsan.M.loaded_segments (0x95a00 : word) = Some W_11d15c.
Proof. vm_refl. Qed.
Lemma D_11d15c : decode_any W_11d15c = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d160 : bv 32 := 0x0063e333.
Lemma F_11d160 : fetch_word AsanUbsan.M.loaded_segments (0x95a04 : word) = Some W_11d160.
Proof. vm_refl. Qed.
Lemma D_11d160 : decode_any W_11d160 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d164 : bv 32 := 0xff060613.
Lemma F_11d164 : fetch_word AsanUbsan.M.loaded_segments (0x95a08 : word) = Some W_11d164.
Proof. vm_refl. Qed.
Lemma D_11d164 : decode_any W_11d164 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d168 : bv 32 := 0x0106a023.
Lemma F_11d168 : fetch_word AsanUbsan.M.loaded_segments (0x95a0c : word) = Some W_11d168.
Proof. vm_refl. Qed.
Lemma D_11d168 : decode_any W_11d168 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d16c : bv 32 := 0x0116a223.
Lemma F_11d16c : fetch_word AsanUbsan.M.loaded_segments (0x95a10 : word) = Some W_11d16c.
Proof. vm_refl. Qed.
Lemma D_11d16c : decode_any W_11d16c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d170 : bv 32 := 0x0056a423.
Lemma F_11d170 : fetch_word AsanUbsan.M.loaded_segments (0x95a14 : word) = Some W_11d170.
Proof. vm_refl. Qed.
Lemma D_11d170 : decode_any W_11d170 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d174 : bv 32 := 0x0066a623.
Lemma F_11d174 : fetch_word AsanUbsan.M.loaded_segments (0x95a18 : word) = Some W_11d174.
Proof. vm_refl. Qed.
Lemma D_11d174 : decode_any W_11d174 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d178 : bv 32 := 0x01068693.
Lemma F_11d178 : fetch_word AsanUbsan.M.loaded_segments (0x95a1c : word) = Some W_11d178.
Proof. vm_refl. Qed.
Lemma D_11d178 : decode_any W_11d178 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d17c : bv 32 := 0x01058593.
Lemma F_11d17c : fetch_word AsanUbsan.M.loaded_segments (0x95a20 : word) = Some W_11d17c.
Proof. vm_refl. Qed.
Lemma D_11d17c : decode_any W_11d17c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d180 : bv 32 := 0xfac7e2e3.
Lemma F_11d180 : fetch_word AsanUbsan.M.loaded_segments (0x95a24 : word) = Some W_11d180.
Proof. vm_refl. Qed.
Lemma D_11d180 : decode_any W_11d180 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d184 : bv 32 := 0xff258593.
Lemma F_11d184 : fetch_word AsanUbsan.M.loaded_segments (0x95a28 : word) = Some W_11d184.
Proof. vm_refl. Qed.
Lemma D_11d184 : decode_any W_11d184 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d188 : bv 32 := 0x01000713.
Lemma F_11d188 : fetch_word AsanUbsan.M.loaded_segments (0x95a2c : word) = Some W_11d188.
Proof. vm_refl. Qed.
Lemma D_11d188 : decode_any W_11d188 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d18c : bv 32 := 0xf4e66ae3.
Lemma F_11d18c : fetch_word AsanUbsan.M.loaded_segments (0x95a30 : word) = Some W_11d18c.
Proof. vm_refl. Qed.
Lemma D_11d18c : decode_any W_11d18c = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d190 : bv 32 := 0x19c0006f.
Lemma F_11d190 : fetch_word AsanUbsan.M.loaded_segments (0x95a34 : word) = Some W_11d190.
Proof. vm_refl. Qed.
Lemma D_11d190 : decode_any W_11d190 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d194 : bv 32 := 0x00050693.
Lemma F_11d194 : fetch_word AsanUbsan.M.loaded_segments (0x95a38 : word) = Some W_11d194.
Proof. vm_refl. Qed.
Lemma D_11d194 : decode_any W_11d194 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d198 : bv 32 := 0x00357793.
Lemma F_11d198 : fetch_word AsanUbsan.M.loaded_segments (0x95a3c : word) = Some W_11d198.
Proof. vm_refl. Qed.
Lemma D_11d198 : decode_any W_11d198 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d19c : bv 32 := 0xf2079ae3.
Lemma F_11d19c : fetch_word AsanUbsan.M.loaded_segments (0x95a40 : word) = Some W_11d19c.
Proof. vm_refl. Qed.
Lemma D_11d19c : decode_any W_11d19c = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1a0 : bv 32 := 0x01000713.
Lemma F_11d1a0 : fetch_word AsanUbsan.M.loaded_segments (0x95a44 : word) = Some W_11d1a0.
Proof. vm_refl. Qed.
Lemma D_11d1a0 : decode_any W_11d1a0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1a4 : bv 32 := 0x02e66c63.
Lemma F_11d1a4 : fetch_word AsanUbsan.M.loaded_segments (0x95a48 : word) = Some W_11d1a4.
Proof. vm_refl. Qed.
Lemma D_11d1a4 : decode_any W_11d1a4 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1a8 : bv 32 := 0x00f00713.
Lemma F_11d1a8 : fetch_word AsanUbsan.M.loaded_segments (0x95a4c : word) = Some W_11d1a8.
Proof. vm_refl. Qed.
Lemma D_11d1a8 : decode_any W_11d1a8 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1ac : bv 32 := 0x0005a783.
Lemma F_11d1ac : fetch_word AsanUbsan.M.loaded_segments (0x95a50 : word) = Some W_11d1ac.
Proof. vm_refl. Qed.
Lemma D_11d1ac : decode_any W_11d1ac = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1b0 : bv 32 := 0x0045a803.
Lemma F_11d1b0 : fetch_word AsanUbsan.M.loaded_segments (0x95a54 : word) = Some W_11d1b0.
Proof. vm_refl. Qed.
Lemma D_11d1b0 : decode_any W_11d1b0 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1b4 : bv 32 := 0x0085a883.
Lemma F_11d1b4 : fetch_word AsanUbsan.M.loaded_segments (0x95a58 : word) = Some W_11d1b4.
Proof. vm_refl. Qed.
Lemma D_11d1b4 : decode_any W_11d1b4 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1b8 : bv 32 := 0x00c5a283.
Lemma F_11d1b8 : fetch_word AsanUbsan.M.loaded_segments (0x95a5c : word) = Some W_11d1b8.
Proof. vm_refl. Qed.
Lemma D_11d1b8 : decode_any W_11d1b8 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1bc : bv 32 := 0x01058593.
Lemma F_11d1bc : fetch_word AsanUbsan.M.loaded_segments (0x95a60 : word) = Some W_11d1bc.
Proof. vm_refl. Qed.
Lemma D_11d1bc : decode_any W_11d1bc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1c0 : bv 32 := 0xff060613.
Lemma F_11d1c0 : fetch_word AsanUbsan.M.loaded_segments (0x95a64 : word) = Some W_11d1c0.
Proof. vm_refl. Qed.
Lemma D_11d1c0 : decode_any W_11d1c0 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1c4 : bv 32 := 0x00f6a023.
Lemma F_11d1c4 : fetch_word AsanUbsan.M.loaded_segments (0x95a68 : word) = Some W_11d1c4.
Proof. vm_refl. Qed.
Lemma D_11d1c4 : decode_any W_11d1c4 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1c8 : bv 32 := 0x0106a223.
Lemma F_11d1c8 : fetch_word AsanUbsan.M.loaded_segments (0x95a6c : word) = Some W_11d1c8.
Proof. vm_refl. Qed.
Lemma D_11d1c8 : decode_any W_11d1c8 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1cc : bv 32 := 0x0116a423.
Lemma F_11d1cc : fetch_word AsanUbsan.M.loaded_segments (0x95a70 : word) = Some W_11d1cc.
Proof. vm_refl. Qed.
Lemma D_11d1cc : decode_any W_11d1cc = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1d0 : bv 32 := 0x0056a623.
Lemma F_11d1d0 : fetch_word AsanUbsan.M.loaded_segments (0x95a74 : word) = Some W_11d1d0.
Proof. vm_refl. Qed.
Lemma D_11d1d0 : decode_any W_11d1d0 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1d4 : bv 32 := 0x01068693.
Lemma F_11d1d4 : fetch_word AsanUbsan.M.loaded_segments (0x95a78 : word) = Some W_11d1d4.
Proof. vm_refl. Qed.
Lemma D_11d1d4 : decode_any W_11d1d4 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1d8 : bv 32 := 0xfcc76ae3.
Lemma F_11d1d8 : fetch_word AsanUbsan.M.loaded_segments (0x95a7c : word) = Some W_11d1d8.
Proof. vm_refl. Qed.
Lemma D_11d1d8 : decode_any W_11d1d8 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1dc : bv 32 := 0x00800713.
Lemma F_11d1dc : fetch_word AsanUbsan.M.loaded_segments (0x95a80 : word) = Some W_11d1dc.
Proof. vm_refl. Qed.
Lemma D_11d1dc : decode_any W_11d1dc = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1e0 : bv 32 := 0x00e66e63.
Lemma F_11d1e0 : fetch_word AsanUbsan.M.loaded_segments (0x95a84 : word) = Some W_11d1e0.
Proof. vm_refl. Qed.
Lemma D_11d1e0 : decode_any W_11d1e0 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1e4 : bv 32 := 0x0005a703.
Lemma F_11d1e4 : fetch_word AsanUbsan.M.loaded_segments (0x95a88 : word) = Some W_11d1e4.
Proof. vm_refl. Qed.
Lemma D_11d1e4 : decode_any W_11d1e4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1e8 : bv 32 := 0x0045a783.
Lemma F_11d1e8 : fetch_word AsanUbsan.M.loaded_segments (0x95a8c : word) = Some W_11d1e8.
Proof. vm_refl. Qed.
Lemma D_11d1e8 : decode_any W_11d1e8 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1ec : bv 32 := 0x00e6a023.
Lemma F_11d1ec : fetch_word AsanUbsan.M.loaded_segments (0x95a90 : word) = Some W_11d1ec.
Proof. vm_refl. Qed.
Lemma D_11d1ec : decode_any W_11d1ec = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1f0 : bv 32 := 0x00f6a223.
Lemma F_11d1f0 : fetch_word AsanUbsan.M.loaded_segments (0x95a94 : word) = Some W_11d1f0.
Proof. vm_refl. Qed.
Lemma D_11d1f0 : decode_any W_11d1f0 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1f4 : bv 32 := 0x00868693.
Lemma F_11d1f4 : fetch_word AsanUbsan.M.loaded_segments (0x95a98 : word) = Some W_11d1f4.
Proof. vm_refl. Qed.
Lemma D_11d1f4 : decode_any W_11d1f4 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1f8 : bv 32 := 0x00858593.
Lemma F_11d1f8 : fetch_word AsanUbsan.M.loaded_segments (0x95a9c : word) = Some W_11d1f8.
Proof. vm_refl. Qed.
Lemma D_11d1f8 : decode_any W_11d1f8 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d1fc : bv 32 := 0x00467713.
Lemma F_11d1fc : fetch_word AsanUbsan.M.loaded_segments (0x95aa0 : word) = Some W_11d1fc.
Proof. vm_refl. Qed.
Lemma D_11d1fc : decode_any W_11d1fc = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d200 : bv 32 := 0x24070063.
Lemma F_11d200 : fetch_word AsanUbsan.M.loaded_segments (0x95aa4 : word) = Some W_11d200.
Proof. vm_refl. Qed.
Lemma D_11d200 : decode_any W_11d200 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d204 : bv 32 := 0x0005a703.
Lemma F_11d204 : fetch_word AsanUbsan.M.loaded_segments (0x95aa8 : word) = Some W_11d204.
Proof. vm_refl. Qed.
Lemma D_11d204 : decode_any W_11d204 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d208 : bv 32 := 0x00458593.
Lemma F_11d208 : fetch_word AsanUbsan.M.loaded_segments (0x95aac : word) = Some W_11d208.
Proof. vm_refl. Qed.
Lemma D_11d208 : decode_any W_11d208 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d20c : bv 32 := 0x00e6a023.
Lemma F_11d20c : fetch_word AsanUbsan.M.loaded_segments (0x95ab0 : word) = Some W_11d20c.
Proof. vm_refl. Qed.
Lemma D_11d20c : decode_any W_11d20c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d210 : bv 32 := 0x00468693.
Lemma F_11d210 : fetch_word AsanUbsan.M.loaded_segments (0x95ab4 : word) = Some W_11d210.
Proof. vm_refl. Qed.
Lemma D_11d210 : decode_any W_11d210 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d214 : bv 32 := 0x22c0006f.
Lemma F_11d214 : fetch_word AsanUbsan.M.loaded_segments (0x95ab8 : word) = Some W_11d214.
Proof. vm_refl. Qed.
Lemma D_11d214 : decode_any W_11d214 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d218 : bv 32 := 0x00e68023.
Lemma F_11d218 : fetch_word AsanUbsan.M.loaded_segments (0x95abc : word) = Some W_11d218.
Proof. vm_refl. Qed.
Lemma D_11d218 : decode_any W_11d218 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d21c : bv 32 := 0x00168693.
Lemma F_11d21c : fetch_word AsanUbsan.M.loaded_segments (0x95ac0 : word) = Some W_11d21c.
Proof. vm_refl. Qed.
Lemma D_11d21c : decode_any W_11d21c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d220 : bv 32 := 0xfff60613.
Lemma F_11d220 : fetch_word AsanUbsan.M.loaded_segments (0x95ac4 : word) = Some W_11d220.
Proof. vm_refl. Qed.
Lemma D_11d220 : decode_any W_11d220 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d224 : bv 32 := 0x01058593.
Lemma F_11d224 : fetch_word AsanUbsan.M.loaded_segments (0x95ac8 : word) = Some W_11d224.
Proof. vm_refl. Qed.
Lemma D_11d224 : decode_any W_11d224 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d228 : bv 32 := 0x01200793.
Lemma F_11d228 : fetch_word AsanUbsan.M.loaded_segments (0x95acc : word) = Some W_11d228.
Proof. vm_refl. Qed.
Lemma D_11d228 : decode_any W_11d228 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d22c : bv 32 := 0x0087581b.
Lemma F_11d22c : fetch_word AsanUbsan.M.loaded_segments (0x95ad0 : word) = Some W_11d22c.
Proof. vm_refl. Qed.
Lemma D_11d22c : decode_any W_11d22c = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d230 : bv 32 := 0xff45a883.
Lemma F_11d230 : fetch_word AsanUbsan.M.loaded_segments (0x95ad4 : word) = Some W_11d230.
Proof. vm_refl. Qed.
Lemma D_11d230 : decode_any W_11d230 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d234 : bv 32 := 0xff85a283.
Lemma F_11d234 : fetch_word AsanUbsan.M.loaded_segments (0x95ad8 : word) = Some W_11d234.
Proof. vm_refl. Qed.
Lemma D_11d234 : decode_any W_11d234 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d238 : bv 32 := 0xffc5a303.
Lemma F_11d238 : fetch_word AsanUbsan.M.loaded_segments (0x95adc : word) = Some W_11d238.
Proof. vm_refl. Qed.
Lemma D_11d238 : decode_any W_11d238 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d23c : bv 32 := 0x0005a703.
Lemma F_11d23c : fetch_word AsanUbsan.M.loaded_segments (0x95ae0 : word) = Some W_11d23c.
Proof. vm_refl. Qed.
Lemma D_11d23c : decode_any W_11d23c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d240 : bv 32 := 0x01889393.
Lemma F_11d240 : fetch_word AsanUbsan.M.loaded_segments (0x95ae4 : word) = Some W_11d240.
Proof. vm_refl. Qed.
Lemma D_11d240 : decode_any W_11d240 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d244 : bv 32 := 0x0088d89b.
Lemma F_11d244 : fetch_word AsanUbsan.M.loaded_segments (0x95ae8 : word) = Some W_11d244.
Proof. vm_refl. Qed.
Lemma D_11d244 : decode_any W_11d244 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d248 : bv 32 := 0x0103e833.
Lemma F_11d248 : fetch_word AsanUbsan.M.loaded_segments (0x95aec : word) = Some W_11d248.
Proof. vm_refl. Qed.
Lemma D_11d248 : decode_any W_11d248 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d24c : bv 32 := 0x01829393.
Lemma F_11d24c : fetch_word AsanUbsan.M.loaded_segments (0x95af0 : word) = Some W_11d24c.
Proof. vm_refl. Qed.
Lemma D_11d24c : decode_any W_11d24c = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d250 : bv 32 := 0x0082d29b.
Lemma F_11d250 : fetch_word AsanUbsan.M.loaded_segments (0x95af4 : word) = Some W_11d250.
Proof. vm_refl. Qed.
Lemma D_11d250 : decode_any W_11d250 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d254 : bv 32 := 0x0113e8b3.
Lemma F_11d254 : fetch_word AsanUbsan.M.loaded_segments (0x95af8 : word) = Some W_11d254.
Proof. vm_refl. Qed.
Lemma D_11d254 : decode_any W_11d254 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d258 : bv 32 := 0x01831393.
Lemma F_11d258 : fetch_word AsanUbsan.M.loaded_segments (0x95afc : word) = Some W_11d258.
Proof. vm_refl. Qed.
Lemma D_11d258 : decode_any W_11d258 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d25c : bv 32 := 0x0083531b.
Lemma F_11d25c : fetch_word AsanUbsan.M.loaded_segments (0x95b00 : word) = Some W_11d25c.
Proof. vm_refl. Qed.
Lemma D_11d25c : decode_any W_11d25c = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d260 : bv 32 := 0x0053e2b3.
Lemma F_11d260 : fetch_word AsanUbsan.M.loaded_segments (0x95b04 : word) = Some W_11d260.
Proof. vm_refl. Qed.
Lemma D_11d260 : decode_any W_11d260 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d264 : bv 32 := 0x01871393.
Lemma F_11d264 : fetch_word AsanUbsan.M.loaded_segments (0x95b08 : word) = Some W_11d264.
Proof. vm_refl. Qed.
Lemma D_11d264 : decode_any W_11d264 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d268 : bv 32 := 0x0063e333.
Lemma F_11d268 : fetch_word AsanUbsan.M.loaded_segments (0x95b0c : word) = Some W_11d268.
Proof. vm_refl. Qed.
Lemma D_11d268 : decode_any W_11d268 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d26c : bv 32 := 0xff060613.
Lemma F_11d26c : fetch_word AsanUbsan.M.loaded_segments (0x95b10 : word) = Some W_11d26c.
Proof. vm_refl. Qed.
Lemma D_11d26c : decode_any W_11d26c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d270 : bv 32 := 0x0106a023.
Lemma F_11d270 : fetch_word AsanUbsan.M.loaded_segments (0x95b14 : word) = Some W_11d270.
Proof. vm_refl. Qed.
Lemma D_11d270 : decode_any W_11d270 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d274 : bv 32 := 0x0116a223.
Lemma F_11d274 : fetch_word AsanUbsan.M.loaded_segments (0x95b18 : word) = Some W_11d274.
Proof. vm_refl. Qed.
Lemma D_11d274 : decode_any W_11d274 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d278 : bv 32 := 0x0056a423.
Lemma F_11d278 : fetch_word AsanUbsan.M.loaded_segments (0x95b1c : word) = Some W_11d278.
Proof. vm_refl. Qed.
Lemma D_11d278 : decode_any W_11d278 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d27c : bv 32 := 0x0066a623.
Lemma F_11d27c : fetch_word AsanUbsan.M.loaded_segments (0x95b20 : word) = Some W_11d27c.
Proof. vm_refl. Qed.
Lemma D_11d27c : decode_any W_11d27c = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d280 : bv 32 := 0x01068693.
Lemma F_11d280 : fetch_word AsanUbsan.M.loaded_segments (0x95b24 : word) = Some W_11d280.
Proof. vm_refl. Qed.
Lemma D_11d280 : decode_any W_11d280 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d284 : bv 32 := 0x01058593.
Lemma F_11d284 : fetch_word AsanUbsan.M.loaded_segments (0x95b28 : word) = Some W_11d284.
Proof. vm_refl. Qed.
Lemma D_11d284 : decode_any W_11d284 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d288 : bv 32 := 0xfac7e2e3.
Lemma F_11d288 : fetch_word AsanUbsan.M.loaded_segments (0x95b2c : word) = Some W_11d288.
Proof. vm_refl. Qed.
Lemma D_11d288 : decode_any W_11d288 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d28c : bv 32 := 0xff158593.
Lemma F_11d28c : fetch_word AsanUbsan.M.loaded_segments (0x95b30 : word) = Some W_11d28c.
Proof. vm_refl. Qed.
Lemma D_11d28c : decode_any W_11d28c = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d290 : bv 32 := 0x01000713.
Lemma F_11d290 : fetch_word AsanUbsan.M.loaded_segments (0x95b34 : word) = Some W_11d290.
Proof. vm_refl. Qed.
Lemma D_11d290 : decode_any W_11d290 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d294 : bv 32 := 0xe4e666e3.
Lemma F_11d294 : fetch_word AsanUbsan.M.loaded_segments (0x95b38 : word) = Some W_11d294.
Proof. vm_refl. Qed.
Lemma D_11d294 : decode_any W_11d294 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d298 : bv 32 := 0x0940006f.
Lemma F_11d298 : fetch_word AsanUbsan.M.loaded_segments (0x95b3c : word) = Some W_11d298.
Proof. vm_refl. Qed.
Lemma D_11d298 : decode_any W_11d298 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d29c : bv 32 := 0x00875793.
Lemma F_11d29c : fetch_word AsanUbsan.M.loaded_segments (0x95b40 : word) = Some W_11d29c.
Proof. vm_refl. Qed.
Lemma D_11d29c : decode_any W_11d29c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2a0 : bv 32 := 0x01075813.
Lemma F_11d2a0 : fetch_word AsanUbsan.M.loaded_segments (0x95b44 : word) = Some W_11d2a0.
Proof. vm_refl. Qed.
Lemma D_11d2a0 : decode_any W_11d2a0 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2a4 : bv 32 := 0xffd60613.
Lemma F_11d2a4 : fetch_word AsanUbsan.M.loaded_segments (0x95b48 : word) = Some W_11d2a4.
Proof. vm_refl. Qed.
Lemma D_11d2a4 : decode_any W_11d2a4 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2a8 : bv 32 := 0x00e68023.
Lemma F_11d2a8 : fetch_word AsanUbsan.M.loaded_segments (0x95b4c : word) = Some W_11d2a8.
Proof. vm_refl. Qed.
Lemma D_11d2a8 : decode_any W_11d2a8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2ac : bv 32 := 0x00f680a3.
Lemma F_11d2ac : fetch_word AsanUbsan.M.loaded_segments (0x95b50 : word) = Some W_11d2ac.
Proof. vm_refl. Qed.
Lemma D_11d2ac : decode_any W_11d2ac = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2b0 : bv 32 := 0x01068123.
Lemma F_11d2b0 : fetch_word AsanUbsan.M.loaded_segments (0x95b54 : word) = Some W_11d2b0.
Proof. vm_refl. Qed.
Lemma D_11d2b0 : decode_any W_11d2b0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2b4 : bv 32 := 0x00368693.
Lemma F_11d2b4 : fetch_word AsanUbsan.M.loaded_segments (0x95b58 : word) = Some W_11d2b4.
Proof. vm_refl. Qed.
Lemma D_11d2b4 : decode_any W_11d2b4 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2b8 : bv 32 := 0x01058593.
Lemma F_11d2b8 : fetch_word AsanUbsan.M.loaded_segments (0x95b5c : word) = Some W_11d2b8.
Proof. vm_refl. Qed.
Lemma D_11d2b8 : decode_any W_11d2b8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2bc : bv 32 := 0x01000793.
Lemma F_11d2bc : fetch_word AsanUbsan.M.loaded_segments (0x95b60 : word) = Some W_11d2bc.
Proof. vm_refl. Qed.
Lemma D_11d2bc : decode_any W_11d2bc = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2c0 : bv 32 := 0x0187581b.
Lemma F_11d2c0 : fetch_word AsanUbsan.M.loaded_segments (0x95b64 : word) = Some W_11d2c0.
Proof. vm_refl. Qed.
Lemma D_11d2c0 : decode_any W_11d2c0 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2c4 : bv 32 := 0xff45a883.
Lemma F_11d2c4 : fetch_word AsanUbsan.M.loaded_segments (0x95b68 : word) = Some W_11d2c4.
Proof. vm_refl. Qed.
Lemma D_11d2c4 : decode_any W_11d2c4 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2c8 : bv 32 := 0xff85a283.
Lemma F_11d2c8 : fetch_word AsanUbsan.M.loaded_segments (0x95b6c : word) = Some W_11d2c8.
Proof. vm_refl. Qed.
Lemma D_11d2c8 : decode_any W_11d2c8 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2cc : bv 32 := 0xffc5a303.
Lemma F_11d2cc : fetch_word AsanUbsan.M.loaded_segments (0x95b70 : word) = Some W_11d2cc.
Proof. vm_refl. Qed.
Lemma D_11d2cc : decode_any W_11d2cc = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2d0 : bv 32 := 0x0005a703.
Lemma F_11d2d0 : fetch_word AsanUbsan.M.loaded_segments (0x95b74 : word) = Some W_11d2d0.
Proof. vm_refl. Qed.
Lemma D_11d2d0 : decode_any W_11d2d0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2d4 : bv 32 := 0x00889393.
Lemma F_11d2d4 : fetch_word AsanUbsan.M.loaded_segments (0x95b78 : word) = Some W_11d2d4.
Proof. vm_refl. Qed.
Lemma D_11d2d4 : decode_any W_11d2d4 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2d8 : bv 32 := 0x0188d89b.
Lemma F_11d2d8 : fetch_word AsanUbsan.M.loaded_segments (0x95b7c : word) = Some W_11d2d8.
Proof. vm_refl. Qed.
Lemma D_11d2d8 : decode_any W_11d2d8 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2dc : bv 32 := 0x0103e833.
Lemma F_11d2dc : fetch_word AsanUbsan.M.loaded_segments (0x95b80 : word) = Some W_11d2dc.
Proof. vm_refl. Qed.
Lemma D_11d2dc : decode_any W_11d2dc = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2e0 : bv 32 := 0x00829393.
Lemma F_11d2e0 : fetch_word AsanUbsan.M.loaded_segments (0x95b84 : word) = Some W_11d2e0.
Proof. vm_refl. Qed.
Lemma D_11d2e0 : decode_any W_11d2e0 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2e4 : bv 32 := 0x0182d29b.
Lemma F_11d2e4 : fetch_word AsanUbsan.M.loaded_segments (0x95b88 : word) = Some W_11d2e4.
Proof. vm_refl. Qed.
Lemma D_11d2e4 : decode_any W_11d2e4 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2e8 : bv 32 := 0x0113e8b3.
Lemma F_11d2e8 : fetch_word AsanUbsan.M.loaded_segments (0x95b8c : word) = Some W_11d2e8.
Proof. vm_refl. Qed.
Lemma D_11d2e8 : decode_any W_11d2e8 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2ec : bv 32 := 0x00831393.
Lemma F_11d2ec : fetch_word AsanUbsan.M.loaded_segments (0x95b90 : word) = Some W_11d2ec.
Proof. vm_refl. Qed.
Lemma D_11d2ec : decode_any W_11d2ec = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2f0 : bv 32 := 0x0183531b.
Lemma F_11d2f0 : fetch_word AsanUbsan.M.loaded_segments (0x95b94 : word) = Some W_11d2f0.
Proof. vm_refl. Qed.
Lemma D_11d2f0 : decode_any W_11d2f0 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2f4 : bv 32 := 0x0053e2b3.
Lemma F_11d2f4 : fetch_word AsanUbsan.M.loaded_segments (0x95b98 : word) = Some W_11d2f4.
Proof. vm_refl. Qed.
Lemma D_11d2f4 : decode_any W_11d2f4 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2f8 : bv 32 := 0x00871393.
Lemma F_11d2f8 : fetch_word AsanUbsan.M.loaded_segments (0x95b9c : word) = Some W_11d2f8.
Proof. vm_refl. Qed.
Lemma D_11d2f8 : decode_any W_11d2f8 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d2fc : bv 32 := 0x0063e333.
Lemma F_11d2fc : fetch_word AsanUbsan.M.loaded_segments (0x95ba0 : word) = Some W_11d2fc.
Proof. vm_refl. Qed.
Lemma D_11d2fc : decode_any W_11d2fc = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d300 : bv 32 := 0xff060613.
Lemma F_11d300 : fetch_word AsanUbsan.M.loaded_segments (0x95ba4 : word) = Some W_11d300.
Proof. vm_refl. Qed.
Lemma D_11d300 : decode_any W_11d300 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d304 : bv 32 := 0x0106a023.
Lemma F_11d304 : fetch_word AsanUbsan.M.loaded_segments (0x95ba8 : word) = Some W_11d304.
Proof. vm_refl. Qed.
Lemma D_11d304 : decode_any W_11d304 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d308 : bv 32 := 0x0116a223.
Lemma F_11d308 : fetch_word AsanUbsan.M.loaded_segments (0x95bac : word) = Some W_11d308.
Proof. vm_refl. Qed.
Lemma D_11d308 : decode_any W_11d308 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d30c : bv 32 := 0x0056a423.
Lemma F_11d30c : fetch_word AsanUbsan.M.loaded_segments (0x95bb0 : word) = Some W_11d30c.
Proof. vm_refl. Qed.
Lemma D_11d30c : decode_any W_11d30c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d310 : bv 32 := 0x0066a623.
Lemma F_11d310 : fetch_word AsanUbsan.M.loaded_segments (0x95bb4 : word) = Some W_11d310.
Proof. vm_refl. Qed.
Lemma D_11d310 : decode_any W_11d310 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d314 : bv 32 := 0x01068693.
Lemma F_11d314 : fetch_word AsanUbsan.M.loaded_segments (0x95bb8 : word) = Some W_11d314.
Proof. vm_refl. Qed.
Lemma D_11d314 : decode_any W_11d314 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d318 : bv 32 := 0x01058593.
Lemma F_11d318 : fetch_word AsanUbsan.M.loaded_segments (0x95bbc : word) = Some W_11d318.
Proof. vm_refl. Qed.
Lemma D_11d318 : decode_any W_11d318 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d31c : bv 32 := 0xfac7e2e3.
Lemma F_11d31c : fetch_word AsanUbsan.M.loaded_segments (0x95bc0 : word) = Some W_11d31c.
Proof. vm_refl. Qed.
Lemma D_11d31c : decode_any W_11d31c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d320 : bv 32 := 0xff358593.
Lemma F_11d320 : fetch_word AsanUbsan.M.loaded_segments (0x95bc4 : word) = Some W_11d320.
Proof. vm_refl. Qed.
Lemma D_11d320 : decode_any W_11d320 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d324 : bv 32 := 0x01000713.
Lemma F_11d324 : fetch_word AsanUbsan.M.loaded_segments (0x95bc8 : word) = Some W_11d324.
Proof. vm_refl. Qed.
Lemma D_11d324 : decode_any W_11d324 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d328 : bv 32 := 0xdae66ce3.
Lemma F_11d328 : fetch_word AsanUbsan.M.loaded_segments (0x95bcc : word) = Some W_11d328.
Proof. vm_refl. Qed.
Lemma D_11d328 : decode_any W_11d328 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d32c : bv 32 := 0x0005c703.
Lemma F_11d32c : fetch_word AsanUbsan.M.loaded_segments (0x95bd0 : word) = Some W_11d32c.
Proof. vm_refl. Qed.
Lemma D_11d32c : decode_any W_11d32c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d330 : bv 32 := 0x0015c783.
Lemma F_11d330 : fetch_word AsanUbsan.M.loaded_segments (0x95bd4 : word) = Some W_11d330.
Proof. vm_refl. Qed.
Lemma D_11d330 : decode_any W_11d330 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d334 : bv 32 := 0x0025c803.
Lemma F_11d334 : fetch_word AsanUbsan.M.loaded_segments (0x95bd8 : word) = Some W_11d334.
Proof. vm_refl. Qed.
Lemma D_11d334 : decode_any W_11d334 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d338 : bv 32 := 0x0035c883.
Lemma F_11d338 : fetch_word AsanUbsan.M.loaded_segments (0x95bdc : word) = Some W_11d338.
Proof. vm_refl. Qed.
Lemma D_11d338 : decode_any W_11d338 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d33c : bv 32 := 0x0045c283.
Lemma F_11d33c : fetch_word AsanUbsan.M.loaded_segments (0x95be0 : word) = Some W_11d33c.
Proof. vm_refl. Qed.
Lemma D_11d33c : decode_any W_11d33c = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d340 : bv 32 := 0x0055c303.
Lemma F_11d340 : fetch_word AsanUbsan.M.loaded_segments (0x95be4 : word) = Some W_11d340.
Proof. vm_refl. Qed.
Lemma D_11d340 : decode_any W_11d340 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d344 : bv 32 := 0x0065c383.
Lemma F_11d344 : fetch_word AsanUbsan.M.loaded_segments (0x95be8 : word) = Some W_11d344.
Proof. vm_refl. Qed.
Lemma D_11d344 : decode_any W_11d344 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d348 : bv 32 := 0x0075ce03.
Lemma F_11d348 : fetch_word AsanUbsan.M.loaded_segments (0x95bec : word) = Some W_11d348.
Proof. vm_refl. Qed.
Lemma D_11d348 : decode_any W_11d348 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d34c : bv 32 := 0x00e68023.
Lemma F_11d34c : fetch_word AsanUbsan.M.loaded_segments (0x95bf0 : word) = Some W_11d34c.
Proof. vm_refl. Qed.
Lemma D_11d34c : decode_any W_11d34c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d350 : bv 32 := 0x00f680a3.
Lemma F_11d350 : fetch_word AsanUbsan.M.loaded_segments (0x95bf4 : word) = Some W_11d350.
Proof. vm_refl. Qed.
Lemma D_11d350 : decode_any W_11d350 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d354 : bv 32 := 0x01068123.
Lemma F_11d354 : fetch_word AsanUbsan.M.loaded_segments (0x95bf8 : word) = Some W_11d354.
Proof. vm_refl. Qed.
Lemma D_11d354 : decode_any W_11d354 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d358 : bv 32 := 0x011681a3.
Lemma F_11d358 : fetch_word AsanUbsan.M.loaded_segments (0x95bfc : word) = Some W_11d358.
Proof. vm_refl. Qed.
Lemma D_11d358 : decode_any W_11d358 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d35c : bv 32 := 0x0085c703.
Lemma F_11d35c : fetch_word AsanUbsan.M.loaded_segments (0x95c00 : word) = Some W_11d35c.
Proof. vm_refl. Qed.
Lemma D_11d35c : decode_any W_11d35c = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d360 : bv 32 := 0x0095c783.
Lemma F_11d360 : fetch_word AsanUbsan.M.loaded_segments (0x95c04 : word) = Some W_11d360.
Proof. vm_refl. Qed.
Lemma D_11d360 : decode_any W_11d360 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d364 : bv 32 := 0x00a5c803.
Lemma F_11d364 : fetch_word AsanUbsan.M.loaded_segments (0x95c08 : word) = Some W_11d364.
Proof. vm_refl. Qed.
Lemma D_11d364 : decode_any W_11d364 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d368 : bv 32 := 0x00b5c883.
Lemma F_11d368 : fetch_word AsanUbsan.M.loaded_segments (0x95c0c : word) = Some W_11d368.
Proof. vm_refl. Qed.
Lemma D_11d368 : decode_any W_11d368 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d36c : bv 32 := 0x00568223.
Lemma F_11d36c : fetch_word AsanUbsan.M.loaded_segments (0x95c10 : word) = Some W_11d36c.
Proof. vm_refl. Qed.
Lemma D_11d36c : decode_any W_11d36c = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d370 : bv 32 := 0x006682a3.
Lemma F_11d370 : fetch_word AsanUbsan.M.loaded_segments (0x95c14 : word) = Some W_11d370.
Proof. vm_refl. Qed.
Lemma D_11d370 : decode_any W_11d370 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d374 : bv 32 := 0x00768323.
Lemma F_11d374 : fetch_word AsanUbsan.M.loaded_segments (0x95c18 : word) = Some W_11d374.
Proof. vm_refl. Qed.
Lemma D_11d374 : decode_any W_11d374 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d378 : bv 32 := 0x01c683a3.
Lemma F_11d378 : fetch_word AsanUbsan.M.loaded_segments (0x95c1c : word) = Some W_11d378.
Proof. vm_refl. Qed.
Lemma D_11d378 : decode_any W_11d378 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d37c : bv 32 := 0x00c5c283.
Lemma F_11d37c : fetch_word AsanUbsan.M.loaded_segments (0x95c20 : word) = Some W_11d37c.
Proof. vm_refl. Qed.
Lemma D_11d37c : decode_any W_11d37c = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d380 : bv 32 := 0x00d5c303.
Lemma F_11d380 : fetch_word AsanUbsan.M.loaded_segments (0x95c24 : word) = Some W_11d380.
Proof. vm_refl. Qed.
Lemma D_11d380 : decode_any W_11d380 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d384 : bv 32 := 0x00e5c383.
Lemma F_11d384 : fetch_word AsanUbsan.M.loaded_segments (0x95c28 : word) = Some W_11d384.
Proof. vm_refl. Qed.
Lemma D_11d384 : decode_any W_11d384 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d388 : bv 32 := 0x00f5ce03.
Lemma F_11d388 : fetch_word AsanUbsan.M.loaded_segments (0x95c2c : word) = Some W_11d388.
Proof. vm_refl. Qed.
Lemma D_11d388 : decode_any W_11d388 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d38c : bv 32 := 0x01058593.
Lemma F_11d38c : fetch_word AsanUbsan.M.loaded_segments (0x95c30 : word) = Some W_11d38c.
Proof. vm_refl. Qed.
Lemma D_11d38c : decode_any W_11d38c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d390 : bv 32 := 0x00e68423.
Lemma F_11d390 : fetch_word AsanUbsan.M.loaded_segments (0x95c34 : word) = Some W_11d390.
Proof. vm_refl. Qed.
Lemma D_11d390 : decode_any W_11d390 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d394 : bv 32 := 0x00f684a3.
Lemma F_11d394 : fetch_word AsanUbsan.M.loaded_segments (0x95c38 : word) = Some W_11d394.
Proof. vm_refl. Qed.
Lemma D_11d394 : decode_any W_11d394 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d398 : bv 32 := 0x01068523.
Lemma F_11d398 : fetch_word AsanUbsan.M.loaded_segments (0x95c3c : word) = Some W_11d398.
Proof. vm_refl. Qed.
Lemma D_11d398 : decode_any W_11d398 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d39c : bv 32 := 0x011685a3.
Lemma F_11d39c : fetch_word AsanUbsan.M.loaded_segments (0x95c40 : word) = Some W_11d39c.
Proof. vm_refl. Qed.
Lemma D_11d39c : decode_any W_11d39c = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3a0 : bv 32 := 0x01068713.
Lemma F_11d3a0 : fetch_word AsanUbsan.M.loaded_segments (0x95c44 : word) = Some W_11d3a0.
Proof. vm_refl. Qed.
Lemma D_11d3a0 : decode_any W_11d3a0 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3a4 : bv 32 := 0x00568623.
Lemma F_11d3a4 : fetch_word AsanUbsan.M.loaded_segments (0x95c48 : word) = Some W_11d3a4.
Proof. vm_refl. Qed.
Lemma D_11d3a4 : decode_any W_11d3a4 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3a8 : bv 32 := 0x006686a3.
Lemma F_11d3a8 : fetch_word AsanUbsan.M.loaded_segments (0x95c4c : word) = Some W_11d3a8.
Proof. vm_refl. Qed.
Lemma D_11d3a8 : decode_any W_11d3a8 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3ac : bv 32 := 0x00768723.
Lemma F_11d3ac : fetch_word AsanUbsan.M.loaded_segments (0x95c50 : word) = Some W_11d3ac.
Proof. vm_refl. Qed.
Lemma D_11d3ac : decode_any W_11d3ac = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3b0 : bv 32 := 0x01c687a3.
Lemma F_11d3b0 : fetch_word AsanUbsan.M.loaded_segments (0x95c54 : word) = Some W_11d3b0.
Proof. vm_refl. Qed.
Lemma D_11d3b0 : decode_any W_11d3b0 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3b4 : bv 32 := 0x00070693.
Lemma F_11d3b4 : fetch_word AsanUbsan.M.loaded_segments (0x95c58 : word) = Some W_11d3b4.
Proof. vm_refl. Qed.
Lemma D_11d3b4 : decode_any W_11d3b4 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3b8 : bv 32 := 0x00867713.
Lemma F_11d3b8 : fetch_word AsanUbsan.M.loaded_segments (0x95c5c : word) = Some W_11d3b8.
Proof. vm_refl. Qed.
Lemma D_11d3b8 : decode_any W_11d3b8 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3bc : bv 32 := 0xd20706e3.
Lemma F_11d3bc : fetch_word AsanUbsan.M.loaded_segments (0x95c60 : word) = Some W_11d3bc.
Proof. vm_refl. Qed.
Lemma D_11d3bc : decode_any W_11d3bc = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3c0 : bv 32 := 0x0005c703.
Lemma F_11d3c0 : fetch_word AsanUbsan.M.loaded_segments (0x95c64 : word) = Some W_11d3c0.
Proof. vm_refl. Qed.
Lemma D_11d3c0 : decode_any W_11d3c0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3c4 : bv 32 := 0x0015c783.
Lemma F_11d3c4 : fetch_word AsanUbsan.M.loaded_segments (0x95c68 : word) = Some W_11d3c4.
Proof. vm_refl. Qed.
Lemma D_11d3c4 : decode_any W_11d3c4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3c8 : bv 32 := 0x0025c803.
Lemma F_11d3c8 : fetch_word AsanUbsan.M.loaded_segments (0x95c6c : word) = Some W_11d3c8.
Proof. vm_refl. Qed.
Lemma D_11d3c8 : decode_any W_11d3c8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3cc : bv 32 := 0x0035c883.
Lemma F_11d3cc : fetch_word AsanUbsan.M.loaded_segments (0x95c70 : word) = Some W_11d3cc.
Proof. vm_refl. Qed.
Lemma D_11d3cc : decode_any W_11d3cc = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3d0 : bv 32 := 0x0045c283.
Lemma F_11d3d0 : fetch_word AsanUbsan.M.loaded_segments (0x95c74 : word) = Some W_11d3d0.
Proof. vm_refl. Qed.
Lemma D_11d3d0 : decode_any W_11d3d0 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3d4 : bv 32 := 0x0055c303.
Lemma F_11d3d4 : fetch_word AsanUbsan.M.loaded_segments (0x95c78 : word) = Some W_11d3d4.
Proof. vm_refl. Qed.
Lemma D_11d3d4 : decode_any W_11d3d4 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3d8 : bv 32 := 0x0065c383.
Lemma F_11d3d8 : fetch_word AsanUbsan.M.loaded_segments (0x95c7c : word) = Some W_11d3d8.
Proof. vm_refl. Qed.
Lemma D_11d3d8 : decode_any W_11d3d8 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3dc : bv 32 := 0x0075ce03.
Lemma F_11d3dc : fetch_word AsanUbsan.M.loaded_segments (0x95c80 : word) = Some W_11d3dc.
Proof. vm_refl. Qed.
Lemma D_11d3dc : decode_any W_11d3dc = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3e0 : bv 32 := 0x00858593.
Lemma F_11d3e0 : fetch_word AsanUbsan.M.loaded_segments (0x95c84 : word) = Some W_11d3e0.
Proof. vm_refl. Qed.
Lemma D_11d3e0 : decode_any W_11d3e0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3e4 : bv 32 := 0x00e68023.
Lemma F_11d3e4 : fetch_word AsanUbsan.M.loaded_segments (0x95c88 : word) = Some W_11d3e4.
Proof. vm_refl. Qed.
Lemma D_11d3e4 : decode_any W_11d3e4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3e8 : bv 32 := 0x00f680a3.
Lemma F_11d3e8 : fetch_word AsanUbsan.M.loaded_segments (0x95c8c : word) = Some W_11d3e8.
Proof. vm_refl. Qed.
Lemma D_11d3e8 : decode_any W_11d3e8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3ec : bv 32 := 0x01068123.
Lemma F_11d3ec : fetch_word AsanUbsan.M.loaded_segments (0x95c90 : word) = Some W_11d3ec.
Proof. vm_refl. Qed.
Lemma D_11d3ec : decode_any W_11d3ec = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3f0 : bv 32 := 0x011681a3.
Lemma F_11d3f0 : fetch_word AsanUbsan.M.loaded_segments (0x95c94 : word) = Some W_11d3f0.
Proof. vm_refl. Qed.
Lemma D_11d3f0 : decode_any W_11d3f0 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3f4 : bv 32 := 0x00868713.
Lemma F_11d3f4 : fetch_word AsanUbsan.M.loaded_segments (0x95c98 : word) = Some W_11d3f4.
Proof. vm_refl. Qed.
Lemma D_11d3f4 : decode_any W_11d3f4 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3f8 : bv 32 := 0x00568223.
Lemma F_11d3f8 : fetch_word AsanUbsan.M.loaded_segments (0x95c9c : word) = Some W_11d3f8.
Proof. vm_refl. Qed.
Lemma D_11d3f8 : decode_any W_11d3f8 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d3fc : bv 32 := 0x006682a3.
Lemma F_11d3fc : fetch_word AsanUbsan.M.loaded_segments (0x95ca0 : word) = Some W_11d3fc.
Proof. vm_refl. Qed.
Lemma D_11d3fc : decode_any W_11d3fc = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d400 : bv 32 := 0x00768323.
Lemma F_11d400 : fetch_word AsanUbsan.M.loaded_segments (0x95ca4 : word) = Some W_11d400.
Proof. vm_refl. Qed.
Lemma D_11d400 : decode_any W_11d400 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d404 : bv 32 := 0x01c683a3.
Lemma F_11d404 : fetch_word AsanUbsan.M.loaded_segments (0x95ca8 : word) = Some W_11d404.
Proof. vm_refl. Qed.
Lemma D_11d404 : decode_any W_11d404 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d408 : bv 32 := 0x00070693.
Lemma F_11d408 : fetch_word AsanUbsan.M.loaded_segments (0x95cac : word) = Some W_11d408.
Proof. vm_refl. Qed.
Lemma D_11d408 : decode_any W_11d408 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d40c : bv 32 := 0x00467713.
Lemma F_11d40c : fetch_word AsanUbsan.M.loaded_segments (0x95cb0 : word) = Some W_11d40c.
Proof. vm_refl. Qed.
Lemma D_11d40c : decode_any W_11d40c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d410 : bv 32 := 0x02070863.
Lemma F_11d410 : fetch_word AsanUbsan.M.loaded_segments (0x95cb4 : word) = Some W_11d410.
Proof. vm_refl. Qed.
Lemma D_11d410 : decode_any W_11d410 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d414 : bv 32 := 0x0005c703.
Lemma F_11d414 : fetch_word AsanUbsan.M.loaded_segments (0x95cb8 : word) = Some W_11d414.
Proof. vm_refl. Qed.
Lemma D_11d414 : decode_any W_11d414 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d418 : bv 32 := 0x0015c783.
Lemma F_11d418 : fetch_word AsanUbsan.M.loaded_segments (0x95cbc : word) = Some W_11d418.
Proof. vm_refl. Qed.
Lemma D_11d418 : decode_any W_11d418 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d41c : bv 32 := 0x0025c803.
Lemma F_11d41c : fetch_word AsanUbsan.M.loaded_segments (0x95cc0 : word) = Some W_11d41c.
Proof. vm_refl. Qed.
Lemma D_11d41c : decode_any W_11d41c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d420 : bv 32 := 0x0035c883.
Lemma F_11d420 : fetch_word AsanUbsan.M.loaded_segments (0x95cc4 : word) = Some W_11d420.
Proof. vm_refl. Qed.
Lemma D_11d420 : decode_any W_11d420 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d424 : bv 32 := 0x00458593.
Lemma F_11d424 : fetch_word AsanUbsan.M.loaded_segments (0x95cc8 : word) = Some W_11d424.
Proof. vm_refl. Qed.
Lemma D_11d424 : decode_any W_11d424 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d428 : bv 32 := 0x00468293.
Lemma F_11d428 : fetch_word AsanUbsan.M.loaded_segments (0x95ccc : word) = Some W_11d428.
Proof. vm_refl. Qed.
Lemma D_11d428 : decode_any W_11d428 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d42c : bv 32 := 0x00e68023.
Lemma F_11d42c : fetch_word AsanUbsan.M.loaded_segments (0x95cd0 : word) = Some W_11d42c.
Proof. vm_refl. Qed.
Lemma D_11d42c : decode_any W_11d42c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d430 : bv 32 := 0x00f680a3.
Lemma F_11d430 : fetch_word AsanUbsan.M.loaded_segments (0x95cd4 : word) = Some W_11d430.
Proof. vm_refl. Qed.
Lemma D_11d430 : decode_any W_11d430 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d434 : bv 32 := 0x01068123.
Lemma F_11d434 : fetch_word AsanUbsan.M.loaded_segments (0x95cd8 : word) = Some W_11d434.
Proof. vm_refl. Qed.
Lemma D_11d434 : decode_any W_11d434 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d438 : bv 32 := 0x011681a3.
Lemma F_11d438 : fetch_word AsanUbsan.M.loaded_segments (0x95cdc : word) = Some W_11d438.
Proof. vm_refl. Qed.
Lemma D_11d438 : decode_any W_11d438 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d43c : bv 32 := 0x00028693.
Lemma F_11d43c : fetch_word AsanUbsan.M.loaded_segments (0x95ce0 : word) = Some W_11d43c.
Proof. vm_refl. Qed.
Lemma D_11d43c : decode_any W_11d43c = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d440 : bv 32 := 0x00267713.
Lemma F_11d440 : fetch_word AsanUbsan.M.loaded_segments (0x95ce4 : word) = Some W_11d440.
Proof. vm_refl. Qed.
Lemma D_11d440 : decode_any W_11d440 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d444 : bv 32 := 0x00071863.
Lemma F_11d444 : fetch_word AsanUbsan.M.loaded_segments (0x95ce8 : word) = Some W_11d444.
Proof. vm_refl. Qed.
Lemma D_11d444 : decode_any W_11d444 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d448 : bv 32 := 0x00167613.
Lemma F_11d448 : fetch_word AsanUbsan.M.loaded_segments (0x95cec : word) = Some W_11d448.
Proof. vm_refl. Qed.
Lemma D_11d448 : decode_any W_11d448 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d44c : bv 32 := 0x02061663.
Lemma F_11d44c : fetch_word AsanUbsan.M.loaded_segments (0x95cf0 : word) = Some W_11d44c.
Proof. vm_refl. Qed.
Lemma D_11d44c : decode_any W_11d44c = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d450 : bv 32 := 0x00008067.
Lemma F_11d450 : fetch_word AsanUbsan.M.loaded_segments (0x95cf4 : word) = Some W_11d450.
Proof. vm_refl. Qed.
Lemma D_11d450 : decode_any W_11d450 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d454 : bv 32 := 0x0005c703.
Lemma F_11d454 : fetch_word AsanUbsan.M.loaded_segments (0x95cf8 : word) = Some W_11d454.
Proof. vm_refl. Qed.
Lemma D_11d454 : decode_any W_11d454 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d458 : bv 32 := 0x0015c783.
Lemma F_11d458 : fetch_word AsanUbsan.M.loaded_segments (0x95cfc : word) = Some W_11d458.
Proof. vm_refl. Qed.
Lemma D_11d458 : decode_any W_11d458 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d45c : bv 32 := 0x00258593.
Lemma F_11d45c : fetch_word AsanUbsan.M.loaded_segments (0x95d00 : word) = Some W_11d45c.
Proof. vm_refl. Qed.
Lemma D_11d45c : decode_any W_11d45c = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d460 : bv 32 := 0x00268813.
Lemma F_11d460 : fetch_word AsanUbsan.M.loaded_segments (0x95d04 : word) = Some W_11d460.
Proof. vm_refl. Qed.
Lemma D_11d460 : decode_any W_11d460 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d464 : bv 32 := 0x00e68023.
Lemma F_11d464 : fetch_word AsanUbsan.M.loaded_segments (0x95d08 : word) = Some W_11d464.
Proof. vm_refl. Qed.
Lemma D_11d464 : decode_any W_11d464 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d468 : bv 32 := 0x00f680a3.
Lemma F_11d468 : fetch_word AsanUbsan.M.loaded_segments (0x95d0c : word) = Some W_11d468.
Proof. vm_refl. Qed.
Lemma D_11d468 : decode_any W_11d468 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d46c : bv 32 := 0x00080693.
Lemma F_11d46c : fetch_word AsanUbsan.M.loaded_segments (0x95d10 : word) = Some W_11d46c.
Proof. vm_refl. Qed.
Lemma D_11d46c : decode_any W_11d46c = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d470 : bv 32 := 0x00167613.
Lemma F_11d470 : fetch_word AsanUbsan.M.loaded_segments (0x95d14 : word) = Some W_11d470.
Proof. vm_refl. Qed.
Lemma D_11d470 : decode_any W_11d470 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d474 : bv 32 := 0xfc060ee3.
Lemma F_11d474 : fetch_word AsanUbsan.M.loaded_segments (0x95d18 : word) = Some W_11d474.
Proof. vm_refl. Qed.
Lemma D_11d474 : decode_any W_11d474 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d478 : bv 32 := 0x0005c583.
Lemma F_11d478 : fetch_word AsanUbsan.M.loaded_segments (0x95d1c : word) = Some W_11d478.
Proof. vm_refl. Qed.
Lemma D_11d478 : decode_any W_11d478 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d47c : bv 32 := 0x00b68023.
Lemma F_11d47c : fetch_word AsanUbsan.M.loaded_segments (0x95d20 : word) = Some W_11d47c.
Proof. vm_refl. Qed.
Lemma D_11d47c : decode_any W_11d47c = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.
Definition W_11d480 : bv 32 := 0x00008067.
Lemma F_11d480 : fetch_word AsanUbsan.M.loaded_segments (0x95d24 : word) = Some W_11d480.
Proof. vm_refl. Qed.
Lemma D_11d480 : decode_any W_11d480 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
