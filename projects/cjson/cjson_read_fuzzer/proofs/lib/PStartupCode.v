(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_12000 : bv 32 := 0xfffff197.
Lemma F_12000 : fetch_word Plain.M.loaded_segments (0x12000 : word) = Some W_12000.
Proof. vm_refl. Qed.
Lemma D_12000 : decode_any W_12000 = Some (Auipc 3 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12004 : bv 32 := 0x80018193.
Lemma F_12004 : fetch_word Plain.M.loaded_segments (0x12004 : word) = Some W_12004.
Proof. vm_refl. Qed.
Lemma D_12004 : decode_any W_12004 = Some (OpImm ALU_ADD 3 3 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12008 : bv 32 := 0x00010513.
Lemma F_12008 : fetch_word Plain.M.loaded_segments (0x12008 : word) = Some W_12008.
Proof. vm_refl. Qed.
Lemma D_12008 : decode_any W_12008 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1200c : bv 32 := 0xfffee597.
Lemma F_1200c : fetch_word Plain.M.loaded_segments (0x1200c : word) = Some W_1200c.
Proof. vm_refl. Qed.
Lemma D_1200c : decode_any W_1200c = Some (Auipc 11 1048558, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12010 : bv 32 := 0xff458593.
Lemma F_12010 : fetch_word Plain.M.loaded_segments (0x12010 : word) = Some W_12010.
Proof. vm_refl. Qed.
Lemma D_12010 : decode_any W_12010 = Some (OpImm ALU_ADD 11 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12014 : bv 32 := 0xff017113.
Lemma F_12014 : fetch_word Plain.M.loaded_segments (0x12014 : word) = Some W_12014.
Proof. vm_refl. Qed.
Lemma D_12014 : decode_any W_12014 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12018 : bv 32 := 0x0040006f.
Lemma F_12018 : fetch_word Plain.M.loaded_segments (0x12018 : word) = Some W_12018.
Proof. vm_refl. Qed.
Lemma D_12018 : decode_any W_12018 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1201c : bv 32 := 0x00052583.
Lemma F_1201c : fetch_word Plain.M.loaded_segments (0x1201c : word) = Some W_1201c.
Proof. vm_refl. Qed.
Lemma D_1201c : decode_any W_1201c = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12020 : bv 32 := 0x00010617.
Lemma F_12020 : fetch_word Plain.M.loaded_segments (0x12020 : word) = Some W_12020.
Proof. vm_refl. Qed.
Lemma D_12020 : decode_any W_12020 = Some (Auipc 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12024 : bv 32 := 0x00010697.
Lemma F_12024 : fetch_word Plain.M.loaded_segments (0x12024 : word) = Some W_12024.
Proof. vm_refl. Qed.
Lemma D_12024 : decode_any W_12024 = Some (Auipc 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12028 : bv 32 := 0x00010717.
Lemma F_12028 : fetch_word Plain.M.loaded_segments (0x12028 : word) = Some W_12028.
Proof. vm_refl. Qed.
Lemma D_12028 : decode_any W_12028 = Some (Auipc 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1202c : bv 32 := 0x45863783.
Lemma F_1202c : fetch_word Plain.M.loaded_segments (0x1202c : word) = Some W_1202c.
Proof. vm_refl. Qed.
Lemma D_1202c : decode_any W_1202c = Some (Load SZ8 true 15 12 1112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12030 : bv 32 := 0x45c6b683.
Lemma F_12030 : fetch_word Plain.M.loaded_segments (0x12030 : word) = Some W_12030.
Proof. vm_refl. Qed.
Lemma D_12030 : decode_any W_12030 = Some (Load SZ8 true 13 13 1116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12034 : bv 32 := 0x46073703.
Lemma F_12034 : fetch_word Plain.M.loaded_segments (0x12034 : word) = Some W_12034.
Proof. vm_refl. Qed.
Lemma D_12034 : decode_any W_12034 = Some (Load SZ8 true 14 14 1120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12038 : bv 32 := 0x00850613.
Lemma F_12038 : fetch_word Plain.M.loaded_segments (0x12038 : word) = Some W_12038.
Proof. vm_refl. Qed.
Lemma D_12038 : decode_any W_12038 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1203c : bv 32 := 0x00078513.
Lemma F_1203c : fetch_word Plain.M.loaded_segments (0x1203c : word) = Some W_1203c.
Proof. vm_refl. Qed.
Lemma D_1203c : decode_any W_1203c = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12040 : bv 32 := 0x00000793.
Lemma F_12040 : fetch_word Plain.M.loaded_segments (0x12040 : word) = Some W_12040.
Proof. vm_refl. Qed.
Lemma D_12040 : decode_any W_12040 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12044 : bv 32 := 0x2350206f.
Lemma F_12044 : fetch_word Plain.M.loaded_segments (0x12044 : word) = Some W_12044.
Proof. vm_refl. Qed.
Lemma D_12044 : decode_any W_12044 = Some (Jal 0 10804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12048 : bv 32 := 0xff010113.
Lemma F_12048 : fetch_word Plain.M.loaded_segments (0x12048 : word) = Some W_12048.
Proof. vm_refl. Qed.
Lemma D_12048 : decode_any W_12048 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1204c : bv 32 := 0x00113423.
Lemma F_1204c : fetch_word Plain.M.loaded_segments (0x1204c : word) = Some W_1204c.
Proof. vm_refl. Qed.
Lemma D_1204c : decode_any W_1204c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12050 : bv 32 := 0x00813023.
Lemma F_12050 : fetch_word Plain.M.loaded_segments (0x12050 : word) = Some W_12050.
Proof. vm_refl. Qed.
Lemma D_12050 : decode_any W_12050 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12054 : bv 32 := 0x01010413.
Lemma F_12054 : fetch_word Plain.M.loaded_segments (0x12054 : word) = Some W_12054.
Proof. vm_refl. Qed.
Lemma D_12054 : decode_any W_12054 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12058 : bv 32 := 0x00011517.
Lemma F_12058 : fetch_word Plain.M.loaded_segments (0x12058 : word) = Some W_12058.
Proof. vm_refl. Qed.
Lemma D_12058 : decode_any W_12058 = Some (Auipc 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1205c : bv 32 := 0x6d850513.
Lemma F_1205c : fetch_word Plain.M.loaded_segments (0x1205c : word) = Some W_1205c.
Proof. vm_refl. Qed.
Lemma D_1205c : decode_any W_1205c = Some (OpImm ALU_ADD 10 10 1752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12060 : bv 32 := 0x00054503.
Lemma F_12060 : fetch_word Plain.M.loaded_segments (0x12060 : word) = Some W_12060.
Proof. vm_refl. Qed.
Lemma D_12060 : decode_any W_12060 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12064 : bv 32 := 0x00157513.
Lemma F_12064 : fetch_word Plain.M.loaded_segments (0x12064 : word) = Some W_12064.
Proof. vm_refl. Qed.
Lemma D_12064 : decode_any W_12064 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12068 : bv 32 := 0x00050663.
Lemma F_12068 : fetch_word Plain.M.loaded_segments (0x12068 : word) = Some W_12068.
Proof. vm_refl. Qed.
Lemma D_12068 : decode_any W_12068 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12074 : bv 32 := 0x00011517.
Lemma F_12074 : fetch_word Plain.M.loaded_segments (0x12074 : word) = Some W_12074.
Proof. vm_refl. Qed.
Lemma D_12074 : decode_any W_12074 = Some (Auipc 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12078 : bv 32 := 0x6bc50593.
Lemma F_12078 : fetch_word Plain.M.loaded_segments (0x12078 : word) = Some W_12078.
Proof. vm_refl. Qed.
Lemma D_12078 : decode_any W_12078 = Some (OpImm ALU_ADD 11 10 1724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1207c : bv 32 := 0x00100513.
Lemma F_1207c : fetch_word Plain.M.loaded_segments (0x1207c : word) = Some W_1207c.
Proof. vm_refl. Qed.
Lemma D_1207c : decode_any W_1207c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12080 : bv 32 := 0x00a58023.
Lemma F_12080 : fetch_word Plain.M.loaded_segments (0x12080 : word) = Some W_12080.
Proof. vm_refl. Qed.
Lemma D_12080 : decode_any W_12080 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12084 : bv 32 := 0x00010517.
Lemma F_12084 : fetch_word Plain.M.loaded_segments (0x12084 : word) = Some W_12084.
Proof. vm_refl. Qed.
Lemma D_12084 : decode_any W_12084 = Some (Auipc 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_12088 : bv 32 := 0x40c53503.
Lemma F_12088 : fetch_word Plain.M.loaded_segments (0x12088 : word) = Some W_12088.
Proof. vm_refl. Qed.
Lemma D_12088 : decode_any W_12088 = Some (Load SZ8 true 10 10 1036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1208c : bv 32 := 0x02050063.
Lemma F_1208c : fetch_word Plain.M.loaded_segments (0x1208c : word) = Some W_1208c.
Proof. vm_refl. Qed.
Lemma D_1208c : decode_any W_1208c = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_120ac : bv 32 := 0x00813083.
Lemma F_120ac : fetch_word Plain.M.loaded_segments (0x120ac : word) = Some W_120ac.
Proof. vm_refl. Qed.
Lemma D_120ac : decode_any W_120ac = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_120b0 : bv 32 := 0x00013403.
Lemma F_120b0 : fetch_word Plain.M.loaded_segments (0x120b0 : word) = Some W_120b0.
Proof. vm_refl. Qed.
Lemma D_120b0 : decode_any W_120b0 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_120b4 : bv 32 := 0x01010113.
Lemma F_120b4 : fetch_word Plain.M.loaded_segments (0x120b4 : word) = Some W_120b4.
Proof. vm_refl. Qed.
Lemma D_120b4 : decode_any W_120b4 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_120b8 : bv 32 := 0x00008067.
Lemma F_120b8 : fetch_word Plain.M.loaded_segments (0x120b8 : word) = Some W_120b8.
Proof. vm_refl. Qed.
Lemma D_120b8 : decode_any W_120b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_147fc : bv 32 := 0x00008067.
Lemma F_147fc : fetch_word Plain.M.loaded_segments (0x147fc : word) = Some W_147fc.
Proof. vm_refl. Qed.
Lemma D_147fc : decode_any W_147fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14800 : bv 32 := 0xe8010113.
Lemma F_14800 : fetch_word Plain.M.loaded_segments (0x14800 : word) = Some W_14800.
Proof. vm_refl. Qed.
Lemma D_14800 : decode_any W_14800 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14804 : bv 32 := 0x16113c23.
Lemma F_14804 : fetch_word Plain.M.loaded_segments (0x14804 : word) = Some W_14804.
Proof. vm_refl. Qed.
Lemma D_14804 : decode_any W_14804 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14808 : bv 32 := 0x16813823.
Lemma F_14808 : fetch_word Plain.M.loaded_segments (0x14808 : word) = Some W_14808.
Proof. vm_refl. Qed.
Lemma D_14808 : decode_any W_14808 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1480c : bv 32 := 0x16913423.
Lemma F_1480c : fetch_word Plain.M.loaded_segments (0x1480c : word) = Some W_1480c.
Proof. vm_refl. Qed.
Lemma D_1480c : decode_any W_1480c = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14810 : bv 32 := 0x17213023.
Lemma F_14810 : fetch_word Plain.M.loaded_segments (0x14810 : word) = Some W_14810.
Proof. vm_refl. Qed.
Lemma D_14810 : decode_any W_14810 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14814 : bv 32 := 0x00058413.
Lemma F_14814 : fetch_word Plain.M.loaded_segments (0x14814 : word) = Some W_14814.
Proof. vm_refl. Qed.
Lemma D_14814 : decode_any W_14814 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14818 : bv 32 := 0x00050493.
Lemma F_14818 : fetch_word Plain.M.loaded_segments (0x14818 : word) = Some W_14818.
Proof. vm_refl. Qed.
Lemma D_14818 : decode_any W_14818 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1481c : bv 32 := 0x03010513.
Lemma F_1481c : fetch_word Plain.M.loaded_segments (0x1481c : word) = Some W_1481c.
Proof. vm_refl. Qed.
Lemma D_1481c : decode_any W_1481c = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14820 : bv 32 := 0x13000613.
Lemma F_14820 : fetch_word Plain.M.loaded_segments (0x14820 : word) = Some W_14820.
Proof. vm_refl. Qed.
Lemma D_14820 : decode_any W_14820 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14824 : bv 32 := 0x00000593.
Lemma F_14824 : fetch_word Plain.M.loaded_segments (0x14824 : word) = Some W_14824.
Proof. vm_refl. Qed.
Lemma D_14824 : decode_any W_14824 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14828 : bv 32 := 0x5c40c0ef.
Lemma F_14828 : fetch_word Plain.M.loaded_segments (0x14828 : word) = Some W_14828.
Proof. vm_refl. Qed.
Lemma D_14828 : decode_any W_14828 = Some (Jal 1 50628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1482c : bv 32 := 0x0000e517.
Lemma F_1482c : fetch_word Plain.M.loaded_segments (0x1482c : word) = Some W_1482c.
Proof. vm_refl. Qed.
Lemma D_1482c : decode_any W_1482c = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14830 : bv 32 := 0xc9453503.
Lemma F_14830 : fetch_word Plain.M.loaded_segments (0x14830 : word) = Some W_14830.
Proof. vm_refl. Qed.
Lemma D_14830 : decode_any W_14830 = Some (Load SZ8 true 10 10 3220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14834 : bv 32 := 0x00953023.
Lemma F_14834 : fetch_word Plain.M.loaded_segments (0x14834 : word) = Some W_14834.
Proof. vm_refl. Qed.
Lemma D_14834 : decode_any W_14834 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14838 : bv 32 := 0x0004b503.
Lemma F_14838 : fetch_word Plain.M.loaded_segments (0x14838 : word) = Some W_14838.
Proof. vm_refl. Qed.
Lemma D_14838 : decode_any W_14838 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1483c : bv 32 := 0x00848493.
Lemma F_1483c : fetch_word Plain.M.loaded_segments (0x1483c : word) = Some W_1483c.
Proof. vm_refl. Qed.
Lemma D_1483c : decode_any W_1483c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14840 : bv 32 := 0xfe051ce3.
Lemma F_14840 : fetch_word Plain.M.loaded_segments (0x14840 : word) = Some W_14840.
Proof. vm_refl. Qed.
Lemma D_14840 : decode_any W_14840 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14844 : bv 32 := 0x0003f517.
Lemma F_14844 : fetch_word Plain.M.loaded_segments (0x14844 : word) = Some W_14844.
Proof. vm_refl. Qed.
Lemma D_14844 : decode_any W_14844 = Some (Auipc 10 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14848 : bv 32 := 0x2d450913.
Lemma F_14848 : fetch_word Plain.M.loaded_segments (0x14848 : word) = Some W_14848.
Proof. vm_refl. Qed.
Lemma D_14848 : decode_any W_14848 = Some (OpImm ALU_ADD 18 10 724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1484c : bv 32 := 0x00993423.
Lemma F_1484c : fetch_word Plain.M.loaded_segments (0x1484c : word) = Some W_1484c.
Proof. vm_refl. Qed.
Lemma D_1484c : decode_any W_1484c = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14850 : bv 32 := 0x0004b583.
Lemma F_14850 : fetch_word Plain.M.loaded_segments (0x14850 : word) = Some W_14850.
Proof. vm_refl. Qed.
Lemma D_14850 : decode_any W_14850 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14854 : bv 32 := 0x04058c63.
Lemma F_14854 : fetch_word Plain.M.loaded_segments (0x14854 : word) = Some W_14854.
Proof. vm_refl. Qed.
Lemma D_14854 : decode_any W_14854 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14858 : bv 32 := 0x01048493.
Lemma F_14858 : fetch_word Plain.M.loaded_segments (0x14858 : word) = Some W_14858.
Proof. vm_refl. Qed.
Lemma D_14858 : decode_any W_14858 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1485c : bv 32 := 0x02500513.
Lemma F_1485c : fetch_word Plain.M.loaded_segments (0x1485c : word) = Some W_1485c.
Proof. vm_refl. Qed.
Lemma D_1485c : decode_any W_1485c = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14860 : bv 32 := 0x03010613.
Lemma F_14860 : fetch_word Plain.M.loaded_segments (0x14860 : word) = Some W_14860.
Proof. vm_refl. Qed.
Lemma D_14860 : decode_any W_14860 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14864 : bv 32 := 0x0100006f.
Lemma F_14864 : fetch_word Plain.M.loaded_segments (0x14864 : word) = Some W_14864.
Proof. vm_refl. Qed.
Lemma D_14864 : decode_any W_14864 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14868 : bv 32 := 0x0004b583.
Lemma F_14868 : fetch_word Plain.M.loaded_segments (0x14868 : word) = Some W_14868.
Proof. vm_refl. Qed.
Lemma D_14868 : decode_any W_14868 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1486c : bv 32 := 0x01048493.
Lemma F_1486c : fetch_word Plain.M.loaded_segments (0x1486c : word) = Some W_1486c.
Proof. vm_refl. Qed.
Lemma D_1486c : decode_any W_1486c = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14870 : bv 32 := 0x00058e63.
Lemma F_14870 : fetch_word Plain.M.loaded_segments (0x14870 : word) = Some W_14870.
Proof. vm_refl. Qed.
Lemma D_14870 : decode_any W_14870 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14874 : bv 32 := 0xfeb56ae3.
Lemma F_14874 : fetch_word Plain.M.loaded_segments (0x14874 : word) = Some W_14874.
Proof. vm_refl. Qed.
Lemma D_14874 : decode_any W_14874 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14878 : bv 32 := 0xff84b683.
Lemma F_14878 : fetch_word Plain.M.loaded_segments (0x14878 : word) = Some W_14878.
Proof. vm_refl. Qed.
Lemma D_14878 : decode_any W_14878 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1487c : bv 32 := 0x00359593.
Lemma F_1487c : fetch_word Plain.M.loaded_segments (0x1487c : word) = Some W_1487c.
Proof. vm_refl. Qed.
Lemma D_1487c : decode_any W_1487c = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14880 : bv 32 := 0x00b605b3.
Lemma F_14880 : fetch_word Plain.M.loaded_segments (0x14880 : word) = Some W_14880.
Proof. vm_refl. Qed.
Lemma D_14880 : decode_any W_14880 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14884 : bv 32 := 0x00d5b023.
Lemma F_14884 : fetch_word Plain.M.loaded_segments (0x14884 : word) = Some W_14884.
Proof. vm_refl. Qed.
Lemma D_14884 : decode_any W_14884 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14888 : bv 32 := 0xfe1ff06f.
Lemma F_14888 : fetch_word Plain.M.loaded_segments (0x14888 : word) = Some W_14888.
Proof. vm_refl. Qed.
Lemma D_14888 : decode_any W_14888 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1488c : bv 32 := 0x0b013583.
Lemma F_1488c : fetch_word Plain.M.loaded_segments (0x1488c : word) = Some W_1488c.
Proof. vm_refl. Qed.
Lemma D_1488c : decode_any W_1488c = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14890 : bv 32 := 0x13013503.
Lemma F_14890 : fetch_word Plain.M.loaded_segments (0x14890 : word) = Some W_14890.
Proof. vm_refl. Qed.
Lemma D_14890 : decode_any W_14890 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14894 : bv 32 := 0x0003f617.
Lemma F_14894 : fetch_word Plain.M.loaded_segments (0x14894 : word) = Some W_14894.
Proof. vm_refl. Qed.
Lemma D_14894 : decode_any W_14894 = Some (Auipc 12 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14898 : bv 32 := 0x2eb63623.
Lemma F_14898 : fetch_word Plain.M.loaded_segments (0x14898 : word) = Some W_14898.
Proof. vm_refl. Qed.
Lemma D_14898 : decode_any W_14898 = Some (Store SZ8 12 11 748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1489c : bv 32 := 0x00050c63.
Lemma F_1489c : fetch_word Plain.M.loaded_segments (0x1489c : word) = Some W_1489c.
Proof. vm_refl. Qed.
Lemma D_1489c : decode_any W_1489c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148b4 : bv 32 := 0x06013503.
Lemma F_148b4 : fetch_word Plain.M.loaded_segments (0x148b4 : word) = Some W_148b4.
Proof. vm_refl. Qed.
Lemma D_148b4 : decode_any W_148b4 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148b8 : bv 32 := 0x02a93823.
Lemma F_148b8 : fetch_word Plain.M.loaded_segments (0x148b8 : word) = Some W_148b8.
Proof. vm_refl. Qed.
Lemma D_148b8 : decode_any W_148b8 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148bc : bv 32 := 0x00041463.
Lemma F_148bc : fetch_word Plain.M.loaded_segments (0x148bc : word) = Some W_148bc.
Proof. vm_refl. Qed.
Lemma D_148bc : decode_any W_148bc = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148c4 : bv 32 := 0x00041663.
Lemma F_148c4 : fetch_word Plain.M.loaded_segments (0x148c4 : word) = Some W_148c4.
Proof. vm_refl. Qed.
Lemma D_148c4 : decode_any W_148c4 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148d0 : bv 32 := 0x0000e517.
Lemma F_148d0 : fetch_word Plain.M.loaded_segments (0x148d0 : word) = Some W_148d0.
Proof. vm_refl. Qed.
Lemma D_148d0 : decode_any W_148d0 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148d4 : bv 32 := 0xbf853583.
Lemma F_148d4 : fetch_word Plain.M.loaded_segments (0x148d4 : word) = Some W_148d4.
Proof. vm_refl. Qed.
Lemma D_148d4 : decode_any W_148d4 = Some (Load SZ8 true 11 10 3064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148d8 : bv 32 := 0x0000e517.
Lemma F_148d8 : fetch_word Plain.M.loaded_segments (0x148d8 : word) = Some W_148d8.
Proof. vm_refl. Qed.
Lemma D_148d8 : decode_any W_148d8 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148dc : bv 32 := 0xbf853503.
Lemma F_148dc : fetch_word Plain.M.loaded_segments (0x148dc : word) = Some W_148dc.
Proof. vm_refl. Qed.
Lemma D_148dc : decode_any W_148dc = Some (Load SZ8 true 10 10 3064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148e0 : bv 32 := 0x0085b023.
Lemma F_148e0 : fetch_word Plain.M.loaded_segments (0x148e0 : word) = Some W_148e0.
Proof. vm_refl. Qed.
Lemma D_148e0 : decode_any W_148e0 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148e4 : bv 32 := 0x00140593.
Lemma F_148e4 : fetch_word Plain.M.loaded_segments (0x148e4 : word) = Some W_148e4.
Proof. vm_refl. Qed.
Lemma D_148e4 : decode_any W_148e4 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148e8 : bv 32 := 0x00853023.
Lemma F_148e8 : fetch_word Plain.M.loaded_segments (0x148e8 : word) = Some W_148e8.
Proof. vm_refl. Qed.
Lemma D_148e8 : decode_any W_148e8 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148ec : bv 32 := 0x02f00613.
Lemma F_148ec : fetch_word Plain.M.loaded_segments (0x148ec : word) = Some W_148ec.
Proof. vm_refl. Qed.
Lemma D_148ec : decode_any W_148ec = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148f0 : bv 32 := 0x00c0006f.
Lemma F_148f0 : fetch_word Plain.M.loaded_segments (0x148f0 : word) = Some W_148f0.
Proof. vm_refl. Qed.
Lemma D_148f0 : decode_any W_148f0 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148f4 : bv 32 := 0x00b53023.
Lemma F_148f4 : fetch_word Plain.M.loaded_segments (0x148f4 : word) = Some W_148f4.
Proof. vm_refl. Qed.
Lemma D_148f4 : decode_any W_148f4 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148f8 : bv 32 := 0x00158593.
Lemma F_148f8 : fetch_word Plain.M.loaded_segments (0x148f8 : word) = Some W_148f8.
Proof. vm_refl. Qed.
Lemma D_148f8 : decode_any W_148f8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_148fc : bv 32 := 0xfff5c683.
Lemma F_148fc : fetch_word Plain.M.loaded_segments (0x148fc : word) = Some W_148fc.
Proof. vm_refl. Qed.
Lemma D_148fc : decode_any W_148fc = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14900 : bv 32 := 0xfec68ae3.
Lemma F_14900 : fetch_word Plain.M.loaded_segments (0x14900 : word) = Some W_14900.
Proof. vm_refl. Qed.
Lemma D_14900 : decode_any W_14900 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14904 : bv 32 := 0xfe069ae3.
Lemma F_14904 : fetch_word Plain.M.loaded_segments (0x14904 : word) = Some W_14904.
Proof. vm_refl. Qed.
Lemma D_14904 : decode_any W_14904 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14908 : bv 32 := 0x03010513.
Lemma F_14908 : fetch_word Plain.M.loaded_segments (0x14908 : word) = Some W_14908.
Proof. vm_refl. Qed.
Lemma D_14908 : decode_any W_14908 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1490c : bv 32 := 0x214000ef.
Lemma F_1490c : fetch_word Plain.M.loaded_segments (0x1490c : word) = Some W_1490c.
Proof. vm_refl. Qed.
Lemma D_1490c : decode_any W_1490c = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14910 : bv 32 := 0x0f813503.
Lemma F_14910 : fetch_word Plain.M.loaded_segments (0x14910 : word) = Some W_14910.
Proof. vm_refl. Qed.
Lemma D_14910 : decode_any W_14910 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14914 : bv 32 := 0x015000ef.
Lemma F_14914 : fetch_word Plain.M.loaded_segments (0x14914 : word) = Some W_14914.
Proof. vm_refl. Qed.
Lemma D_14914 : decode_any W_14914 = Some (Jal 1 2068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14918 : bv 32 := 0x08813503.
Lemma F_14918 : fetch_word Plain.M.loaded_segments (0x14918 : word) = Some W_14918.
Proof. vm_refl. Qed.
Lemma D_14918 : decode_any W_14918 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1491c : bv 32 := 0x09013583.
Lemma F_1491c : fetch_word Plain.M.loaded_segments (0x1491c : word) = Some W_1491c.
Proof. vm_refl. Qed.
Lemma D_1491c : decode_any W_1491c = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14920 : bv 32 := 0x00b51c63.
Lemma F_14920 : fetch_word Plain.M.loaded_segments (0x14920 : word) = Some W_14920.
Proof. vm_refl. Qed.
Lemma D_14920 : decode_any W_14920 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14924 : bv 32 := 0x09813503.
Lemma F_14924 : fetch_word Plain.M.loaded_segments (0x14924 : word) = Some W_14924.
Proof. vm_refl. Qed.
Lemma D_14924 : decode_any W_14924 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14928 : bv 32 := 0x0a013583.
Lemma F_14928 : fetch_word Plain.M.loaded_segments (0x14928 : word) = Some W_14928.
Proof. vm_refl. Qed.
Lemma D_14928 : decode_any W_14928 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1492c : bv 32 := 0x00b51663.
Lemma F_1492c : fetch_word Plain.M.loaded_segments (0x1492c : word) = Some W_1492c.
Proof. vm_refl. Qed.
Lemma D_1492c : decode_any W_1492c = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14930 : bv 32 := 0x0e813503.
Lemma F_14930 : fetch_word Plain.M.loaded_segments (0x14930 : word) = Some W_14930.
Proof. vm_refl. Qed.
Lemma D_14930 : decode_any W_14930 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14934 : bv 32 := 0x0e050063.
Lemma F_14934 : fetch_word Plain.M.loaded_segments (0x14934 : word) = Some W_14934.
Proof. vm_refl. Qed.
Lemma D_14934 : decode_any W_14934 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a14 : bv 32 := 0x17813083.
Lemma F_14a14 : fetch_word Plain.M.loaded_segments (0x14a14 : word) = Some W_14a14.
Proof. vm_refl. Qed.
Lemma D_14a14 : decode_any W_14a14 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a18 : bv 32 := 0x17013403.
Lemma F_14a18 : fetch_word Plain.M.loaded_segments (0x14a18 : word) = Some W_14a18.
Proof. vm_refl. Qed.
Lemma D_14a18 : decode_any W_14a18 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a1c : bv 32 := 0x16813483.
Lemma F_14a1c : fetch_word Plain.M.loaded_segments (0x14a1c : word) = Some W_14a1c.
Proof. vm_refl. Qed.
Lemma D_14a1c : decode_any W_14a1c = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a20 : bv 32 := 0x16013903.
Lemma F_14a20 : fetch_word Plain.M.loaded_segments (0x14a20 : word) = Some W_14a20.
Proof. vm_refl. Qed.
Lemma D_14a20 : decode_any W_14a20 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a24 : bv 32 := 0x18010113.
Lemma F_14a24 : fetch_word Plain.M.loaded_segments (0x14a24 : word) = Some W_14a24.
Proof. vm_refl. Qed.
Lemma D_14a24 : decode_any W_14a24 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a28 : bv 32 := 0x00008067.
Lemma F_14a28 : fetch_word Plain.M.loaded_segments (0x14a28 : word) = Some W_14a28.
Proof. vm_refl. Qed.
Lemma D_14a28 : decode_any W_14a28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a2c : bv 32 := 0xfe010113.
Lemma F_14a2c : fetch_word Plain.M.loaded_segments (0x14a2c : word) = Some W_14a2c.
Proof. vm_refl. Qed.
Lemma D_14a2c : decode_any W_14a2c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a30 : bv 32 := 0x00113c23.
Lemma F_14a30 : fetch_word Plain.M.loaded_segments (0x14a30 : word) = Some W_14a30.
Proof. vm_refl. Qed.
Lemma D_14a30 : decode_any W_14a30 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a34 : bv 32 := 0x00813823.
Lemma F_14a34 : fetch_word Plain.M.loaded_segments (0x14a34 : word) = Some W_14a34.
Proof. vm_refl. Qed.
Lemma D_14a34 : decode_any W_14a34 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a38 : bv 32 := 0x00913423.
Lemma F_14a38 : fetch_word Plain.M.loaded_segments (0x14a38 : word) = Some W_14a38.
Proof. vm_refl. Qed.
Lemma D_14a38 : decode_any W_14a38 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a3c : bv 32 := 0xdc1ff0ef.
Lemma F_14a3c : fetch_word Plain.M.loaded_segments (0x14a3c : word) = Some W_14a3c.
Proof. vm_refl. Qed.
Lemma D_14a3c : decode_any W_14a3c = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a40 : bv 32 := 0x0000e517.
Lemma F_14a40 : fetch_word Plain.M.loaded_segments (0x14a40 : word) = Some W_14a40.
Proof. vm_refl. Qed.
Lemma D_14a40 : decode_any W_14a40 = Some (Auipc 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a44 : bv 32 := 0x0000e597.
Lemma F_14a44 : fetch_word Plain.M.loaded_segments (0x14a44 : word) = Some W_14a44.
Proof. vm_refl. Qed.
Lemma D_14a44 : decode_any W_14a44 = Some (Auipc 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a48 : bv 32 := 0xa9853403.
Lemma F_14a48 : fetch_word Plain.M.loaded_segments (0x14a48 : word) = Some W_14a48.
Proof. vm_refl. Qed.
Lemma D_14a48 : decode_any W_14a48 = Some (Load SZ8 true 8 10 2712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a4c : bv 32 := 0xa9c5b483.
Lemma F_14a4c : fetch_word Plain.M.loaded_segments (0x14a4c : word) = Some W_14a4c.
Proof. vm_refl. Qed.
Lemma D_14a4c : decode_any W_14a4c = Some (Load SZ8 true 9 11 2716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a50 : bv 32 := 0x0084fa63.
Lemma F_14a50 : fetch_word Plain.M.loaded_segments (0x14a50 : word) = Some W_14a50.
Proof. vm_refl. Qed.
Lemma D_14a50 : decode_any W_14a50 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a54 : bv 32 := 0x0004b503.
Lemma F_14a54 : fetch_word Plain.M.loaded_segments (0x14a54 : word) = Some W_14a54.
Proof. vm_refl. Qed.
Lemma D_14a54 : decode_any W_14a54 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a58 : bv 32 := 0x000500e7.
Lemma F_14a58 : fetch_word Plain.M.loaded_segments (0x14a58 : word) = Some W_14a58.
Proof. vm_refl. Qed.
Lemma D_14a58 : decode_any W_14a58 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a5c : bv 32 := 0x00848493.
Lemma F_14a5c : fetch_word Plain.M.loaded_segments (0x14a5c : word) = Some W_14a5c.
Proof. vm_refl. Qed.
Lemma D_14a5c : decode_any W_14a5c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a60 : bv 32 := 0xfe84eae3.
Lemma F_14a60 : fetch_word Plain.M.loaded_segments (0x14a60 : word) = Some W_14a60.
Proof. vm_refl. Qed.
Lemma D_14a60 : decode_any W_14a60 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a64 : bv 32 := 0x01813083.
Lemma F_14a64 : fetch_word Plain.M.loaded_segments (0x14a64 : word) = Some W_14a64.
Proof. vm_refl. Qed.
Lemma D_14a64 : decode_any W_14a64 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a68 : bv 32 := 0x01013403.
Lemma F_14a68 : fetch_word Plain.M.loaded_segments (0x14a68 : word) = Some W_14a68.
Proof. vm_refl. Qed.
Lemma D_14a68 : decode_any W_14a68 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a6c : bv 32 := 0x00813483.
Lemma F_14a6c : fetch_word Plain.M.loaded_segments (0x14a6c : word) = Some W_14a6c.
Proof. vm_refl. Qed.
Lemma D_14a6c : decode_any W_14a6c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a70 : bv 32 := 0x02010113.
Lemma F_14a70 : fetch_word Plain.M.loaded_segments (0x14a70 : word) = Some W_14a70.
Proof. vm_refl. Qed.
Lemma D_14a70 : decode_any W_14a70 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a74 : bv 32 := 0x00008067.
Lemma F_14a74 : fetch_word Plain.M.loaded_segments (0x14a74 : word) = Some W_14a74.
Proof. vm_refl. Qed.
Lemma D_14a74 : decode_any W_14a74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a78 : bv 32 := 0xfe010113.
Lemma F_14a78 : fetch_word Plain.M.loaded_segments (0x14a78 : word) = Some W_14a78.
Proof. vm_refl. Qed.
Lemma D_14a78 : decode_any W_14a78 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a7c : bv 32 := 0x00113c23.
Lemma F_14a7c : fetch_word Plain.M.loaded_segments (0x14a7c : word) = Some W_14a7c.
Proof. vm_refl. Qed.
Lemma D_14a7c : decode_any W_14a7c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a80 : bv 32 := 0x00813823.
Lemma F_14a80 : fetch_word Plain.M.loaded_segments (0x14a80 : word) = Some W_14a80.
Proof. vm_refl. Qed.
Lemma D_14a80 : decode_any W_14a80 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a84 : bv 32 := 0x00913423.
Lemma F_14a84 : fetch_word Plain.M.loaded_segments (0x14a84 : word) = Some W_14a84.
Proof. vm_refl. Qed.
Lemma D_14a84 : decode_any W_14a84 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a88 : bv 32 := 0x01213023.
Lemma F_14a88 : fetch_word Plain.M.loaded_segments (0x14a88 : word) = Some W_14a88.
Proof. vm_refl. Qed.
Lemma D_14a88 : decode_any W_14a88 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a8c : bv 32 := 0x00060413.
Lemma F_14a8c : fetch_word Plain.M.loaded_segments (0x14a8c : word) = Some W_14a8c.
Proof. vm_refl. Qed.
Lemma D_14a8c : decode_any W_14a8c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a90 : bv 32 := 0x00058493.
Lemma F_14a90 : fetch_word Plain.M.loaded_segments (0x14a90 : word) = Some W_14a90.
Proof. vm_refl. Qed.
Lemma D_14a90 : decode_any W_14a90 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a94 : bv 32 := 0x00050913.
Lemma F_14a94 : fetch_word Plain.M.loaded_segments (0x14a94 : word) = Some W_14a94.
Proof. vm_refl. Qed.
Lemma D_14a94 : decode_any W_14a94 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a98 : bv 32 := 0x00063583.
Lemma F_14a98 : fetch_word Plain.M.loaded_segments (0x14a98 : word) = Some W_14a98.
Proof. vm_refl. Qed.
Lemma D_14a98 : decode_any W_14a98 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14a9c : bv 32 := 0x00349513.
Lemma F_14a9c : fetch_word Plain.M.loaded_segments (0x14a9c : word) = Some W_14a9c.
Proof. vm_refl. Qed.
Lemma D_14a9c : decode_any W_14a9c = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14aa0 : bv 32 := 0x00a60533.
Lemma F_14aa0 : fetch_word Plain.M.loaded_segments (0x14aa0 : word) = Some W_14aa0.
Proof. vm_refl. Qed.
Lemma D_14aa0 : decode_any W_14aa0 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14aa4 : bv 32 := 0x00850513.
Lemma F_14aa4 : fetch_word Plain.M.loaded_segments (0x14aa4 : word) = Some W_14aa4.
Proof. vm_refl. Qed.
Lemma D_14aa4 : decode_any W_14aa4 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14aa8 : bv 32 := 0xd59ff0ef.
Lemma F_14aa8 : fetch_word Plain.M.loaded_segments (0x14aa8 : word) = Some W_14aa8.
Proof. vm_refl. Qed.
Lemma D_14aa8 : decode_any W_14aa8 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14aac : bv 32 := 0x00000517.
Lemma F_14aac : fetch_word Plain.M.loaded_segments (0x14aac : word) = Some W_14aac.
Proof. vm_refl. Qed.
Lemma D_14aac : decode_any W_14aac = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ab0 : bv 32 := 0x02c50313.
Lemma F_14ab0 : fetch_word Plain.M.loaded_segments (0x14ab0 : word) = Some W_14ab0.
Proof. vm_refl. Qed.
Lemma D_14ab0 : decode_any W_14ab0 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ab4 : bv 32 := 0x00090513.
Lemma F_14ab4 : fetch_word Plain.M.loaded_segments (0x14ab4 : word) = Some W_14ab4.
Proof. vm_refl. Qed.
Lemma D_14ab4 : decode_any W_14ab4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ab8 : bv 32 := 0x00048593.
Lemma F_14ab8 : fetch_word Plain.M.loaded_segments (0x14ab8 : word) = Some W_14ab8.
Proof. vm_refl. Qed.
Lemma D_14ab8 : decode_any W_14ab8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14abc : bv 32 := 0x00040613.
Lemma F_14abc : fetch_word Plain.M.loaded_segments (0x14abc : word) = Some W_14abc.
Proof. vm_refl. Qed.
Lemma D_14abc : decode_any W_14abc = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ac0 : bv 32 := 0x01813083.
Lemma F_14ac0 : fetch_word Plain.M.loaded_segments (0x14ac0 : word) = Some W_14ac0.
Proof. vm_refl. Qed.
Lemma D_14ac0 : decode_any W_14ac0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ac4 : bv 32 := 0x01013403.
Lemma F_14ac4 : fetch_word Plain.M.loaded_segments (0x14ac4 : word) = Some W_14ac4.
Proof. vm_refl. Qed.
Lemma D_14ac4 : decode_any W_14ac4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ac8 : bv 32 := 0x00813483.
Lemma F_14ac8 : fetch_word Plain.M.loaded_segments (0x14ac8 : word) = Some W_14ac8.
Proof. vm_refl. Qed.
Lemma D_14ac8 : decode_any W_14ac8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14acc : bv 32 := 0x00013903.
Lemma F_14acc : fetch_word Plain.M.loaded_segments (0x14acc : word) = Some W_14acc.
Proof. vm_refl. Qed.
Lemma D_14acc : decode_any W_14acc = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ad0 : bv 32 := 0x02010113.
Lemma F_14ad0 : fetch_word Plain.M.loaded_segments (0x14ad0 : word) = Some W_14ad0.
Proof. vm_refl. Qed.
Lemma D_14ad0 : decode_any W_14ad0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ad4 : bv 32 := 0x00030067.
Lemma F_14ad4 : fetch_word Plain.M.loaded_segments (0x14ad4 : word) = Some W_14ad4.
Proof. vm_refl. Qed.
Lemma D_14ad4 : decode_any W_14ad4 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ad8 : bv 32 := 0xfd010113.
Lemma F_14ad8 : fetch_word Plain.M.loaded_segments (0x14ad8 : word) = Some W_14ad8.
Proof. vm_refl. Qed.
Lemma D_14ad8 : decode_any W_14ad8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14adc : bv 32 := 0x02113423.
Lemma F_14adc : fetch_word Plain.M.loaded_segments (0x14adc : word) = Some W_14adc.
Proof. vm_refl. Qed.
Lemma D_14adc : decode_any W_14adc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ae0 : bv 32 := 0x02813023.
Lemma F_14ae0 : fetch_word Plain.M.loaded_segments (0x14ae0 : word) = Some W_14ae0.
Proof. vm_refl. Qed.
Lemma D_14ae0 : decode_any W_14ae0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ae4 : bv 32 := 0x00913c23.
Lemma F_14ae4 : fetch_word Plain.M.loaded_segments (0x14ae4 : word) = Some W_14ae4.
Proof. vm_refl. Qed.
Lemma D_14ae4 : decode_any W_14ae4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ae8 : bv 32 := 0x01213823.
Lemma F_14ae8 : fetch_word Plain.M.loaded_segments (0x14ae8 : word) = Some W_14ae8.
Proof. vm_refl. Qed.
Lemma D_14ae8 : decode_any W_14ae8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14aec : bv 32 := 0x01313423.
Lemma F_14aec : fetch_word Plain.M.loaded_segments (0x14aec : word) = Some W_14aec.
Proof. vm_refl. Qed.
Lemma D_14aec : decode_any W_14aec = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14af0 : bv 32 := 0x00060413.
Lemma F_14af0 : fetch_word Plain.M.loaded_segments (0x14af0 : word) = Some W_14af0.
Proof. vm_refl. Qed.
Lemma D_14af0 : decode_any W_14af0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14af4 : bv 32 := 0x00058493.
Lemma F_14af4 : fetch_word Plain.M.loaded_segments (0x14af4 : word) = Some W_14af4.
Proof. vm_refl. Qed.
Lemma D_14af4 : decode_any W_14af4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14af8 : bv 32 := 0x00050913.
Lemma F_14af8 : fetch_word Plain.M.loaded_segments (0x14af8 : word) = Some W_14af8.
Proof. vm_refl. Qed.
Lemma D_14af8 : decode_any W_14af8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14afc : bv 32 := 0x00359513.
Lemma F_14afc : fetch_word Plain.M.loaded_segments (0x14afc : word) = Some W_14afc.
Proof. vm_refl. Qed.
Lemma D_14afc : decode_any W_14afc = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b00 : bv 32 := 0x00a60533.
Lemma F_14b00 : fetch_word Plain.M.loaded_segments (0x14b00 : word) = Some W_14b00.
Proof. vm_refl. Qed.
Lemma D_14b00 : decode_any W_14b00 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b04 : bv 32 := 0x00850993.
Lemma F_14b04 : fetch_word Plain.M.loaded_segments (0x14b04 : word) = Some W_14b04.
Proof. vm_refl. Qed.
Lemma D_14b04 : decode_any W_14b04 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b08 : bv 32 := 0xf25ff0ef.
Lemma F_14b08 : fetch_word Plain.M.loaded_segments (0x14b08 : word) = Some W_14b08.
Proof. vm_refl. Qed.
Lemma D_14b08 : decode_any W_14b08 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b0c : bv 32 := 0x00048513.
Lemma F_14b0c : fetch_word Plain.M.loaded_segments (0x14b0c : word) = Some W_14b0c.
Proof. vm_refl. Qed.
Lemma D_14b0c : decode_any W_14b0c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b10 : bv 32 := 0x00040593.
Lemma F_14b10 : fetch_word Plain.M.loaded_segments (0x14b10 : word) = Some W_14b10.
Proof. vm_refl. Qed.
Lemma D_14b10 : decode_any W_14b10 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b14 : bv 32 := 0x00098613.
Lemma F_14b14 : fetch_word Plain.M.loaded_segments (0x14b14 : word) = Some W_14b14.
Proof. vm_refl. Qed.
Lemma D_14b14 : decode_any W_14b14 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b18 : bv 32 := 0x000900e7.
Lemma F_14b18 : fetch_word Plain.M.loaded_segments (0x14b18 : word) = Some W_14b18.
Proof. vm_refl. Qed.
Lemma D_14b18 : decode_any W_14b18 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b20 : bv 32 := 0xfc010113.
Lemma F_14b20 : fetch_word Plain.M.loaded_segments (0x14b20 : word) = Some W_14b20.
Proof. vm_refl. Qed.
Lemma D_14b20 : decode_any W_14b20 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b24 : bv 32 := 0x02113c23.
Lemma F_14b24 : fetch_word Plain.M.loaded_segments (0x14b24 : word) = Some W_14b24.
Proof. vm_refl. Qed.
Lemma D_14b24 : decode_any W_14b24 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b28 : bv 32 := 0x02813823.
Lemma F_14b28 : fetch_word Plain.M.loaded_segments (0x14b28 : word) = Some W_14b28.
Proof. vm_refl. Qed.
Lemma D_14b28 : decode_any W_14b28 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b2c : bv 32 := 0x02913423.
Lemma F_14b2c : fetch_word Plain.M.loaded_segments (0x14b2c : word) = Some W_14b2c.
Proof. vm_refl. Qed.
Lemma D_14b2c : decode_any W_14b2c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b30 : bv 32 := 0x03213023.
Lemma F_14b30 : fetch_word Plain.M.loaded_segments (0x14b30 : word) = Some W_14b30.
Proof. vm_refl. Qed.
Lemma D_14b30 : decode_any W_14b30 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b34 : bv 32 := 0x01313c23.
Lemma F_14b34 : fetch_word Plain.M.loaded_segments (0x14b34 : word) = Some W_14b34.
Proof. vm_refl. Qed.
Lemma D_14b34 : decode_any W_14b34 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b38 : bv 32 := 0x01413823.
Lemma F_14b38 : fetch_word Plain.M.loaded_segments (0x14b38 : word) = Some W_14b38.
Proof. vm_refl. Qed.
Lemma D_14b38 : decode_any W_14b38 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b3c : bv 32 := 0x01513423.
Lemma F_14b3c : fetch_word Plain.M.loaded_segments (0x14b3c : word) = Some W_14b3c.
Proof. vm_refl. Qed.
Lemma D_14b3c : decode_any W_14b3c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b40 : bv 32 := 0x02853683.
Lemma F_14b40 : fetch_word Plain.M.loaded_segments (0x14b40 : word) = Some W_14b40.
Proof. vm_refl. Qed.
Lemma D_14b40 : decode_any W_14b40 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b44 : bv 32 := 0x0003f597.
Lemma F_14b44 : fetch_word Plain.M.loaded_segments (0x14b44 : word) = Some W_14b44.
Proof. vm_refl. Qed.
Lemma D_14b44 : decode_any W_14b44 = Some (Auipc 11 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b48 : bv 32 := 0xd5458593.
Lemma F_14b48 : fetch_word Plain.M.loaded_segments (0x14b48 : word) = Some W_14b48.
Proof. vm_refl. Qed.
Lemma D_14b48 : decode_any W_14b48 = Some (OpImm ALU_ADD 11 11 3412, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b4c : bv 32 := 0x0003f617.
Lemma F_14b4c : fetch_word Plain.M.loaded_segments (0x14b4c : word) = Some W_14b4c.
Proof. vm_refl. Qed.
Lemma D_14b4c : decode_any W_14b4c = Some (Auipc 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b50 : bv 32 := 0xfcc60493.
Lemma F_14b50 : fetch_word Plain.M.loaded_segments (0x14b50 : word) = Some W_14b50.
Proof. vm_refl. Qed.
Lemma D_14b50 : decode_any W_14b50 = Some (OpImm ALU_ADD 9 12 4044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b54 : bv 32 := 0x0c068e63.
Lemma F_14b54 : fetch_word Plain.M.loaded_segments (0x14b54 : word) = Some W_14b54.
Proof. vm_refl. Qed.
Lemma D_14b54 : decode_any W_14b54 = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b58 : bv 32 := 0x00000613.
Lemma F_14b58 : fetch_word Plain.M.loaded_segments (0x14b58 : word) = Some W_14b58.
Proof. vm_refl. Qed.
Lemma D_14b58 : decode_any W_14b58 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b5c : bv 32 := 0x00000893.
Lemma F_14b5c : fetch_word Plain.M.loaded_segments (0x14b5c : word) = Some W_14b5c.
Proof. vm_refl. Qed.
Lemma D_14b5c : decode_any W_14b5c = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b60 : bv 32 := 0x0000f717.
Lemma F_14b60 : fetch_word Plain.M.loaded_segments (0x14b60 : word) = Some W_14b60.
Proof. vm_refl. Qed.
Lemma D_14b60 : decode_any W_14b60 = Some (Auipc 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b64 : bv 32 := 0x01853783.
Lemma F_14b64 : fetch_word Plain.M.loaded_segments (0x14b64 : word) = Some W_14b64.
Proof. vm_refl. Qed.
Lemma D_14b64 : decode_any W_14b64 = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b68 : bv 32 := 0x02053503.
Lemma F_14b68 : fetch_word Plain.M.loaded_segments (0x14b68 : word) = Some W_14b68.
Proof. vm_refl. Qed.
Lemma D_14b68 : decode_any W_14b68 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b6c : bv 32 := 0x00600813.
Lemma F_14b6c : fetch_word Plain.M.loaded_segments (0x14b6c : word) = Some W_14b6c.
Proof. vm_refl. Qed.
Lemma D_14b6c : decode_any W_14b6c = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b70 : bv 32 := 0x0000e297.
Lemma F_14b70 : fetch_word Plain.M.loaded_segments (0x14b70 : word) = Some W_14b70.
Proof. vm_refl. Qed.
Lemma D_14b70 : decode_any W_14b70 = Some (Auipc 5 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b74 : bv 32 := 0xbc076f03.
Lemma F_14b74 : fetch_word Plain.M.loaded_segments (0x14b74 : word) = Some W_14b74.
Proof. vm_refl. Qed.
Lemma D_14b74 : decode_any W_14b74 = Some (Load SZ4 false 30 14 3008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b78 : bv 32 := 0x9002b283.
Lemma F_14b78 : fetch_word Plain.M.loaded_segments (0x14b78 : word) = Some W_14b78.
Proof. vm_refl. Qed.
Lemma D_14b78 : decode_any W_14b78 = Some (Load SZ8 true 5 5 2304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b7c : bv 32 := 0x00200313.
Lemma F_14b7c : fetch_word Plain.M.loaded_segments (0x14b7c : word) = Some W_14b7c.
Proof. vm_refl. Qed.
Lemma D_14b7c : decode_any W_14b7c = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b80 : bv 32 := 0x00700393.
Lemma F_14b80 : fetch_word Plain.M.loaded_segments (0x14b80 : word) = Some W_14b80.
Proof. vm_refl. Qed.
Lemma D_14b80 : decode_any W_14b80 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b84 : bv 32 := 0x6474ee37.
Lemma F_14b84 : fetch_word Plain.M.loaded_segments (0x14b84 : word) = Some W_14b84.
Proof. vm_refl. Qed.
Lemma D_14b84 : decode_any W_14b84 = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b88 : bv 32 := 0x551e0e1b.
Lemma F_14b88 : fetch_word Plain.M.loaded_segments (0x14b88 : word) = Some W_14b88.
Proof. vm_refl. Qed.
Lemma D_14b88 : decode_any W_14b88 = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b8c : bv 32 := 0x00078e93.
Lemma F_14b8c : fetch_word Plain.M.loaded_segments (0x14b8c : word) = Some W_14b8c.
Proof. vm_refl. Qed.
Lemma D_14b8c : decode_any W_14b8c = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b90 : bv 32 := 0x0180006f.
Lemma F_14b90 : fetch_word Plain.M.loaded_segments (0x14b90 : word) = Some W_14b90.
Proof. vm_refl. Qed.
Lemma D_14b90 : decode_any W_14b90 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b94 : bv 32 := 0x010eb603.
Lemma F_14b94 : fetch_word Plain.M.loaded_segments (0x14b94 : word) = Some W_14b94.
Proof. vm_refl. Qed.
Lemma D_14b94 : decode_any W_14b94 = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14b98 : bv 32 := 0x40c78633.
Lemma F_14b98 : fetch_word Plain.M.loaded_segments (0x14b98 : word) = Some W_14b98.
Proof. vm_refl. Qed.
Lemma D_14b98 : decode_any W_14b98 = Some (Op ALU_SUB 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14b9c : bv 32 := 0xfff68693.
Lemma F_14b9c : fetch_word Plain.M.loaded_segments (0x14b9c : word) = Some W_14b9c.
Proof. vm_refl. Qed.
Lemma D_14b9c : decode_any W_14b9c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ba0 : bv 32 := 0x00ae8eb3.
Lemma F_14ba0 : fetch_word Plain.M.loaded_segments (0x14ba0 : word) = Some W_14ba0.
Proof. vm_refl. Qed.
Lemma D_14ba0 : decode_any W_14ba0 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ba4 : bv 32 := 0x04068a63.
Lemma F_14ba4 : fetch_word Plain.M.loaded_segments (0x14ba4 : word) = Some W_14ba4.
Proof. vm_refl. Qed.
Lemma D_14ba4 : decode_any W_14ba4 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14ba8 : bv 32 := 0x000ea403.
Lemma F_14ba8 : fetch_word Plain.M.loaded_segments (0x14ba8 : word) = Some W_14ba8.
Proof. vm_refl. Qed.
Lemma D_14ba8 : decode_any W_14ba8 = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bac : bv 32 := 0xff0404e3.
Lemma F_14bac : fetch_word Plain.M.loaded_segments (0x14bac : word) = Some W_14bac.
Proof. vm_refl. Qed.
Lemma D_14bac : decode_any W_14bac = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bb0 : bv 32 := 0x00028a63.
Lemma F_14bb0 : fetch_word Plain.M.loaded_segments (0x14bb0 : word) = Some W_14bb0.
Proof. vm_refl. Qed.
Lemma D_14bb0 : decode_any W_14bb0 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_14bb4 : bv 32 := 0x00641863.
Lemma F_14bb4 : fetch_word Plain.M.loaded_segments (0x14bb4 : word) = Some W_14bb4.
Proof. vm_refl. Qed.
Lemma D_14bb4 : decode_any W_14bb4 = Some (Branch BC_NE 8 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14bb8 : bv 32 := 0x010eb603.
Lemma F_14bb8 : fetch_word Plain.M.loaded_segments (0x14bb8 : word) = Some W_14bb8.
Proof. vm_refl. Qed.
Lemma D_14bb8 : decode_any W_14bb8 = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14bbc : bv 32 := 0x40c28633.
Lemma F_14bbc : fetch_word Plain.M.loaded_segments (0x14bbc : word) = Some W_14bbc.
Proof. vm_refl. Qed.
Lemma D_14bbc : decode_any W_14bbc = Some (Op ALU_SUB 12 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_14bc0 : bv 32 := 0xfddff06f.
Lemma F_14bc0 : fetch_word Plain.M.loaded_segments (0x14bc0 : word) = Some W_14bc0.
Proof. vm_refl. Qed.
Lemma D_14bc0 : decode_any W_14bc0 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bc4 : bv 32 := 0x000e8f93.
Lemma F_14bc4 : fetch_word Plain.M.loaded_segments (0x14bc4 : word) = Some W_14bc4.
Proof. vm_refl. Qed.
Lemma D_14bc4 : decode_any W_14bc4 = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bc8 : bv 32 := 0x00740463.
Lemma F_14bc8 : fetch_word Plain.M.loaded_segments (0x14bc8 : word) = Some W_14bc8.
Proof. vm_refl. Qed.
Lemma D_14bc8 : decode_any W_14bc8 = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bcc : bv 32 := 0x00088f93.
Lemma F_14bcc : fetch_word Plain.M.loaded_segments (0x14bcc : word) = Some W_14bcc.
Proof. vm_refl. Qed.
Lemma D_14bcc : decode_any W_14bcc = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bd0 : bv 32 := 0x03c41063.
Lemma F_14bd0 : fetch_word Plain.M.loaded_segments (0x14bd0 : word) = Some W_14bd0.
Proof. vm_refl. Qed.
Lemma D_14bd0 : decode_any W_14bd0 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bd4 : bv 32 := 0x028eb883.
Lemma F_14bd4 : fetch_word Plain.M.loaded_segments (0x14bd4 : word) = Some W_14bd4.
Proof. vm_refl. Qed.
Lemma D_14bd4 : decode_any W_14bd4 = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bd8 : bv 32 := 0x011f7c63.
Lemma F_14bd8 : fetch_word Plain.M.loaded_segments (0x14bd8 : word) = Some W_14bd8.
Proof. vm_refl. Qed.
Lemma D_14bd8 : decode_any W_14bd8 = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_14bdc : bv 32 := 0x00800f37.
Lemma F_14bdc : fetch_word Plain.M.loaded_segments (0x14bdc : word) = Some W_14bdc.
Proof. vm_refl. Qed.
Lemma D_14bdc : decode_any W_14bdc = Some (Lui 30 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_14be0 : bv 32 := 0x01e8e463.
Lemma F_14be0 : fetch_word Plain.M.loaded_segments (0x14be0 : word) = Some W_14be0.
Proof. vm_refl. Qed.
Lemma D_14be0 : decode_any W_14be0 = Some (Branch BC_LTU 17 30 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14be4 : bv 32 := 0x008008b7.
Lemma F_14be4 : fetch_word Plain.M.loaded_segments (0x14be4 : word) = Some W_14be4.
Proof. vm_refl. Qed.
Lemma D_14be4 : decode_any W_14be4 = Some (Lui 17 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_14be8 : bv 32 := 0xbd172023.
Lemma F_14be8 : fetch_word Plain.M.loaded_segments (0x14be8 : word) = Some W_14be8.
Proof. vm_refl. Qed.
Lemma D_14be8 : decode_any W_14be8 = Some (Store SZ4 14 17 3008, 4%Z).
Proof. vm_refl. Qed.

Definition W_14bec : bv 32 := 0x00088f13.
Lemma F_14bec : fetch_word Plain.M.loaded_segments (0x14bec : word) = Some W_14bec.
Proof. vm_refl. Qed.
Lemma D_14bec : decode_any W_14bec = Some (OpImm ALU_ADD 30 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bf0 : bv 32 := 0x000f8893.
Lemma F_14bf0 : fetch_word Plain.M.loaded_segments (0x14bf0 : word) = Some W_14bf0.
Proof. vm_refl. Qed.
Lemma D_14bf0 : decode_any W_14bf0 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bf4 : bv 32 := 0xfa9ff06f.
Lemma F_14bf4 : fetch_word Plain.M.loaded_segments (0x14bf4 : word) = Some W_14bf4.
Proof. vm_refl. Qed.
Lemma D_14bf4 : decode_any W_14bf4 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14bf8 : bv 32 := 0x02088c63.
Lemma F_14bf8 : fetch_word Plain.M.loaded_segments (0x14bf8 : word) = Some W_14bf8.
Proof. vm_refl. Qed.
Lemma D_14bf8 : decode_any W_14bf8 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_14bfc : bv 32 := 0x00858713.
Lemma F_14bfc : fetch_word Plain.M.loaded_segments (0x14bfc : word) = Some W_14bfc.
Proof. vm_refl. Qed.
Lemma D_14bfc : decode_any W_14bfc = Some (OpImm ALU_ADD 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c00 : bv 32 := 0x0108b783.
Lemma F_14c00 : fetch_word Plain.M.loaded_segments (0x14c00 : word) = Some W_14c00.
Proof. vm_refl. Qed.
Lemma D_14c00 : decode_any W_14c00 = Some (Load SZ8 true 15 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c04 : bv 32 := 0x0208b803.
Lemma F_14c04 : fetch_word Plain.M.loaded_segments (0x14c04 : word) = Some W_14c04.
Proof. vm_refl. Qed.
Lemma D_14c04 : decode_any W_14c04 = Some (Load SZ8 true 16 17 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c08 : bv 32 := 0x0288b683.
Lemma F_14c08 : fetch_word Plain.M.loaded_segments (0x14c08 : word) = Some W_14c08.
Proof. vm_refl. Qed.
Lemma D_14c08 : decode_any W_14c08 = Some (Load SZ8 true 13 17 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c0c : bv 32 := 0x0308b503.
Lemma F_14c0c : fetch_word Plain.M.loaded_segments (0x14c0c : word) = Some W_14c0c.
Proof. vm_refl. Qed.
Lemma D_14c0c : decode_any W_14c0c = Some (Load SZ8 true 10 17 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c10 : bv 32 := 0x00c78633.
Lemma F_14c10 : fetch_word Plain.M.loaded_segments (0x14c10 : word) = Some W_14c10.
Proof. vm_refl. Qed.
Lemma D_14c10 : decode_any W_14c10 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c14 : bv 32 := 0x00100793.
Lemma F_14c14 : fetch_word Plain.M.loaded_segments (0x14c14 : word) = Some W_14c14.
Proof. vm_refl. Qed.
Lemma D_14c14 : decode_any W_14c14 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c18 : bv 32 := 0x00c5b823.
Lemma F_14c18 : fetch_word Plain.M.loaded_segments (0x14c18 : word) = Some W_14c18.
Proof. vm_refl. Qed.
Lemma D_14c18 : decode_any W_14c18 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c1c : bv 32 := 0x0105bc23.
Lemma F_14c1c : fetch_word Plain.M.loaded_segments (0x14c1c : word) = Some W_14c1c.
Proof. vm_refl. Qed.
Lemma D_14c1c : decode_any W_14c1c = Some (Store SZ8 11 16 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c20 : bv 32 := 0x02a5b423.
Lemma F_14c20 : fetch_word Plain.M.loaded_segments (0x14c20 : word) = Some W_14c20.
Proof. vm_refl. Qed.
Lemma D_14c20 : decode_any W_14c20 = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c24 : bv 32 := 0x00e4b823.
Lemma F_14c24 : fetch_word Plain.M.loaded_segments (0x14c24 : word) = Some W_14c24.
Proof. vm_refl. Qed.
Lemma D_14c24 : decode_any W_14c24 = Some (Store SZ8 9 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c28 : bv 32 := 0x02f4b423.
Lemma F_14c28 : fetch_word Plain.M.loaded_segments (0x14c28 : word) = Some W_14c28.
Proof. vm_refl. Qed.
Lemma D_14c28 : decode_any W_14c28 = Some (Store SZ8 9 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c2c : bv 32 := 0x0100006f.
Lemma F_14c2c : fetch_word Plain.M.loaded_segments (0x14c2c : word) = Some W_14c2c.
Proof. vm_refl. Qed.
Lemma D_14c2c : decode_any W_14c2c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c30 : bv 32 := 0x0105b603.
Lemma F_14c30 : fetch_word Plain.M.loaded_segments (0x14c30 : word) = Some W_14c30.
Proof. vm_refl. Qed.
Lemma D_14c30 : decode_any W_14c30 = Some (Load SZ8 true 12 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c34 : bv 32 := 0x0205b683.
Lemma F_14c34 : fetch_word Plain.M.loaded_segments (0x14c34 : word) = Some W_14c34.
Proof. vm_refl. Qed.
Lemma D_14c34 : decode_any W_14c34 = Some (Load SZ8 true 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c38 : bv 32 := 0x0285b503.
Lemma F_14c38 : fetch_word Plain.M.loaded_segments (0x14c38 : word) = Some W_14c38.
Proof. vm_refl. Qed.
Lemma D_14c38 : decode_any W_14c38 = Some (Load SZ8 true 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c3c : bv 32 := 0x00c68733.
Lemma F_14c3c : fetch_word Plain.M.loaded_segments (0x14c3c : word) = Some W_14c3c.
Proof. vm_refl. Qed.
Lemma D_14c3c : decode_any W_14c3c = Some (Op ALU_ADD 14 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c40 : bv 32 := 0xfff50793.
Lemma F_14c40 : fetch_word Plain.M.loaded_segments (0x14c40 : word) = Some W_14c40.
Proof. vm_refl. Qed.
Lemma D_14c40 : decode_any W_14c40 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c44 : bv 32 := 0x40e00733.
Lemma F_14c44 : fetch_word Plain.M.loaded_segments (0x14c44 : word) = Some W_14c44.
Proof. vm_refl. Qed.
Lemma D_14c44 : decode_any W_14c44 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c48 : bv 32 := 0x00c7f633.
Lemma F_14c48 : fetch_word Plain.M.loaded_segments (0x14c48 : word) = Some W_14c48.
Proof. vm_refl. Qed.
Lemma D_14c48 : decode_any W_14c48 = Some (Op ALU_AND 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c4c : bv 32 := 0x00e7f733.
Lemma F_14c4c : fetch_word Plain.M.loaded_segments (0x14c4c : word) = Some W_14c4c.
Proof. vm_refl. Qed.
Lemma D_14c4c : decode_any W_14c4c = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c50 : bv 32 := 0x00700793.
Lemma F_14c50 : fetch_word Plain.M.loaded_segments (0x14c50 : word) = Some W_14c50.
Proof. vm_refl. Qed.
Lemma D_14c50 : decode_any W_14c50 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c54 : bv 32 := 0x00d706b3.
Lemma F_14c54 : fetch_word Plain.M.loaded_segments (0x14c54 : word) = Some W_14c54.
Proof. vm_refl. Qed.
Lemma D_14c54 : decode_any W_14c54 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c58 : bv 32 := 0x02d5b023.
Lemma F_14c58 : fetch_word Plain.M.loaded_segments (0x14c58 : word) = Some W_14c58.
Proof. vm_refl. Qed.
Lemma D_14c58 : decode_any W_14c58 = Some (Store SZ8 11 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c5c : bv 32 := 0x02c5b823.
Lemma F_14c5c : fetch_word Plain.M.loaded_segments (0x14c5c : word) = Some W_14c5c.
Proof. vm_refl. Qed.
Lemma D_14c5c : decode_any W_14c5c = Some (Store SZ8 11 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c60 : bv 32 := 0x00a7e663.
Lemma F_14c60 : fetch_word Plain.M.loaded_segments (0x14c60 : word) = Some W_14c60.
Proof. vm_refl. Qed.
Lemma D_14c60 : decode_any W_14c60 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c64 : bv 32 := 0x00800513.
Lemma F_14c64 : fetch_word Plain.M.loaded_segments (0x14c64 : word) = Some W_14c64.
Proof. vm_refl. Qed.
Lemma D_14c64 : decode_any W_14c64 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c68 : bv 32 := 0x02a5b423.
Lemma F_14c68 : fetch_word Plain.M.loaded_segments (0x14c68 : word) = Some W_14c68.
Proof. vm_refl. Qed.
Lemma D_14c68 : decode_any W_14c68 = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c6c : bv 32 := 0x00d60633.
Lemma F_14c6c : fetch_word Plain.M.loaded_segments (0x14c6c : word) = Some W_14c6c.
Proof. vm_refl. Qed.
Lemma D_14c6c : decode_any W_14c6c = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c70 : bv 32 := 0x000205b7.
Lemma F_14c70 : fetch_word Plain.M.loaded_segments (0x14c70 : word) = Some W_14c70.
Proof. vm_refl. Qed.
Lemma D_14c70 : decode_any W_14c70 = Some (Lui 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c74 : bv 32 := 0x00a60633.
Lemma F_14c74 : fetch_word Plain.M.loaded_segments (0x14c74 : word) = Some W_14c74.
Proof. vm_refl. Qed.
Lemma D_14c74 : decode_any W_14c74 = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c78 : bv 32 := 0x0d15869b.
Lemma F_14c78 : fetch_word Plain.M.loaded_segments (0x14c78 : word) = Some W_14c78.
Proof. vm_refl. Qed.
Lemma D_14c78 : decode_any W_14c78 = Some (OpImm32 13 11 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c7c : bv 32 := 0x0df60593.
Lemma F_14c7c : fetch_word Plain.M.loaded_segments (0x14c7c : word) = Some W_14c7c.
Proof. vm_refl. Qed.
Lemma D_14c7c : decode_any W_14c7c = Some (OpImm ALU_ADD 11 12 223, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c80 : bv 32 := 0xff85f593.
Lemma F_14c80 : fetch_word Plain.M.loaded_segments (0x14c80 : word) = Some W_14c80.
Proof. vm_refl. Qed.
Lemma D_14c80 : decode_any W_14c80 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c84 : bv 32 := 0x00b4bc23.
Lemma F_14c84 : fetch_word Plain.M.loaded_segments (0x14c84 : word) = Some W_14c84.
Proof. vm_refl. Qed.
Lemma D_14c84 : decode_any W_14c84 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c88 : bv 32 := 0x02a4b023.
Lemma F_14c88 : fetch_word Plain.M.loaded_segments (0x14c88 : word) = Some W_14c88.
Proof. vm_refl. Qed.
Lemma D_14c88 : decode_any W_14c88 = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14c8c : bv 32 := 0x02d5ea63.
Lemma F_14c8c : fetch_word Plain.M.loaded_segments (0x14c8c : word) = Some W_14c8c.
Proof. vm_refl. Qed.
Lemma D_14c8c : decode_any W_14c8c = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c90 : bv 32 := 0xffffc597.
Lemma F_14c90 : fetch_word Plain.M.loaded_segments (0x14c90 : word) = Some W_14c90.
Proof. vm_refl. Qed.
Lemma D_14c90 : decode_any W_14c90 = Some (Auipc 11 1048572, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c94 : bv 32 := 0x04000893.
Lemma F_14c94 : fetch_word Plain.M.loaded_segments (0x14c94 : word) = Some W_14c94.
Proof. vm_refl. Qed.
Lemma D_14c94 : decode_any W_14c94 = Some (OpImm ALU_ADD 17 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c98 : bv 32 := 0x00200513.
Lemma F_14c98 : fetch_word Plain.M.loaded_segments (0x14c98 : word) = Some W_14c98.
Proof. vm_refl. Qed.
Lemma D_14c98 : decode_any W_14c98 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_14c9c : bv 32 := 0xb3458593.
Lemma F_14c9c : fetch_word Plain.M.loaded_segments (0x14c9c : word) = Some W_14c9c.
Proof. vm_refl. Qed.
Lemma D_14c9c : decode_any W_14c9c = Some (OpImm ALU_ADD 11 11 2868, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ca0 : bv 32 := 0x05b00613.
Lemma F_14ca0 : fetch_word Plain.M.loaded_segments (0x14ca0 : word) = Some W_14ca0.
Proof. vm_refl. Qed.
Lemma D_14ca0 : decode_any W_14ca0 = Some (OpImm ALU_ADD 12 0 91, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ca4 : bv 32 := 0x00000073.
Lemma F_14ca4 : fetch_word Plain.M.loaded_segments (0x14ca4 : word) = Some W_14ca4.
Proof. vm_refl. Qed.
Lemma D_14ca4 : decode_any W_14ca4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_14ca4 : is_ecall W_14ca4 = true.
Proof. reflexivity. Qed.

Definition W_14ca8 : bv 32 := 0x00000023.
Lemma F_14ca8 : fetch_word Plain.M.loaded_segments (0x14ca8 : word) = Some W_14ca8.
Proof. vm_refl. Qed.
Lemma D_14ca8 : decode_any W_14ca8 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cac : bv 32 := 0x05e00893.
Lemma F_14cac : fetch_word Plain.M.loaded_segments (0x14cac : word) = Some W_14cac.
Proof. vm_refl. Qed.
Lemma D_14cac : decode_any W_14cac = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cb0 : bv 32 := 0x07f00513.
Lemma F_14cb0 : fetch_word Plain.M.loaded_segments (0x14cb0 : word) = Some W_14cb0.
Proof. vm_refl. Qed.
Lemma D_14cb0 : decode_any W_14cb0 = Some (OpImm ALU_ADD 10 0 127, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cb4 : bv 32 := 0x00000073.
Lemma F_14cb4 : fetch_word Plain.M.loaded_segments (0x14cb4 : word) = Some W_14cb4.
Proof. vm_refl. Qed.
Lemma D_14cb4 : decode_any W_14cb4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_14cb4 : is_ecall W_14cb4 = true.
Proof. reflexivity. Qed.

Definition W_14cb8 : bv 32 := 0x0184b583.
Lemma F_14cb8 : fetch_word Plain.M.loaded_segments (0x14cb8 : word) = Some W_14cb8.
Proof. vm_refl. Qed.
Lemma D_14cb8 : decode_any W_14cb8 = Some (Load SZ8 true 11 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cbc : bv 32 := 0x0204b503.
Lemma F_14cbc : fetch_word Plain.M.loaded_segments (0x14cbc : word) = Some W_14cbc.
Proof. vm_refl. Qed.
Lemma D_14cbc : decode_any W_14cbc = Some (Load SZ8 true 10 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cc0 : bv 32 := 0x0001f697.
Lemma F_14cc0 : fetch_word Plain.M.loaded_segments (0x14cc0 : word) = Some W_14cc0.
Proof. vm_refl. Qed.
Lemma D_14cc0 : decode_any W_14cc0 = Some (Auipc 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cc4 : bv 32 := 0x0104b983.
Lemma F_14cc4 : fetch_word Plain.M.loaded_segments (0x14cc4 : word) = Some W_14cc4.
Proof. vm_refl. Qed.
Lemma D_14cc4 : decode_any W_14cc4 = Some (Load SZ8 true 19 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cc8 : bv 32 := 0x0284b603.
Lemma F_14cc8 : fetch_word Plain.M.loaded_segments (0x14cc8 : word) = Some W_14cc8.
Proof. vm_refl. Qed.
Lemma D_14cc8 : decode_any W_14cc8 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ccc : bv 32 := 0xfff50713.
Lemma F_14ccc : fetch_word Plain.M.loaded_segments (0x14ccc : word) = Some W_14ccc.
Proof. vm_refl. Qed.
Lemma D_14ccc : decode_any W_14ccc = Some (OpImm ALU_ADD 14 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cd0 : bv 32 := 0xf3800793.
Lemma F_14cd0 : fetch_word Plain.M.loaded_segments (0x14cd0 : word) = Some W_14cd0.
Proof. vm_refl. Qed.
Lemma D_14cd0 : decode_any W_14cd0 = Some (OpImm ALU_ADD 15 0 3896, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cd4 : bv 32 := 0xb0868513.
Lemma F_14cd4 : fetch_word Plain.M.loaded_segments (0x14cd4 : word) = Some W_14cd4.
Proof. vm_refl. Qed.
Lemma D_14cd4 : decode_any W_14cd4 = Some (OpImm ALU_ADD 10 13 2824, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cd8 : bv 32 := 0x40a787b3.
Lemma F_14cd8 : fetch_word Plain.M.loaded_segments (0x14cd8 : word) = Some W_14cd8.
Proof. vm_refl. Qed.
Lemma D_14cd8 : decode_any W_14cd8 = Some (Op ALU_SUB 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cdc : bv 32 := 0x00f77733.
Lemma F_14cdc : fetch_word Plain.M.loaded_segments (0x14cdc : word) = Some W_14cdc.
Proof. vm_refl. Qed.
Lemma D_14cdc : decode_any W_14cdc = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ce0 : bv 32 := 0xfff64693.
Lemma F_14ce0 : fetch_word Plain.M.loaded_segments (0x14ce0 : word) = Some W_14ce0.
Proof. vm_refl. Qed.
Lemma D_14ce0 : decode_any W_14ce0 = Some (OpImm ALU_XOR 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ce4 : bv 32 := 0x00e50933.
Lemma F_14ce4 : fetch_word Plain.M.loaded_segments (0x14ce4 : word) = Some W_14ce4.
Proof. vm_refl. Qed.
Lemma D_14ce4 : decode_any W_14ce4 = Some (Op ALU_ADD 18 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_14ce8 : bv 32 := 0x00369693.
Lemma F_14ce8 : fetch_word Plain.M.loaded_segments (0x14ce8 : word) = Some W_14ce8.
Proof. vm_refl. Qed.
Lemma D_14ce8 : decode_any W_14ce8 = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cec : bv 32 := 0x00d506b3.
Lemma F_14cec : fetch_word Plain.M.loaded_segments (0x14cec : word) = Some W_14cec.
Proof. vm_refl. Qed.
Lemma D_14cec : decode_any W_14cec = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cf0 : bv 32 := 0x00b68a33.
Lemma F_14cf0 : fetch_word Plain.M.loaded_segments (0x14cf0 : word) = Some W_14cf0.
Proof. vm_refl. Qed.
Lemma D_14cf0 : decode_any W_14cf0 = Some (Op ALU_ADD 20 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14cf4 : bv 32 := 0x0c890413.
Lemma F_14cf4 : fetch_word Plain.M.loaded_segments (0x14cf4 : word) = Some W_14cf4.
Proof. vm_refl. Qed.
Lemma D_14cf4 : decode_any W_14cf4 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cf8 : bv 32 := 0x04098463.
Lemma F_14cf8 : fetch_word Plain.M.loaded_segments (0x14cf8 : word) = Some W_14cf8.
Proof. vm_refl. Qed.
Lemma D_14cf8 : decode_any W_14cf8 = Some (Branch BC_EQ 19 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_14cfc : bv 32 := 0x00361613.
Lemma F_14cfc : fetch_word Plain.M.loaded_segments (0x14cfc : word) = Some W_14cfc.
Proof. vm_refl. Qed.
Lemma D_14cfc : decode_any W_14cfc = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d00 : bv 32 := 0x40c50533.
Lemma F_14d00 : fetch_word Plain.M.loaded_segments (0x14d00 : word) = Some W_14d00.
Proof. vm_refl. Qed.
Lemma D_14d00 : decode_any W_14d00 = Some (Op ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d04 : bv 32 := 0x00b50ab3.
Lemma F_14d04 : fetch_word Plain.M.loaded_segments (0x14d04 : word) = Some W_14d04.
Proof. vm_refl. Qed.
Lemma D_14d04 : decode_any W_14d04 = Some (Op ALU_ADD 21 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d08 : bv 32 := 0x0289b503.
Lemma F_14d08 : fetch_word Plain.M.loaded_segments (0x14d08 : word) = Some W_14d08.
Proof. vm_refl. Qed.
Lemma D_14d08 : decode_any W_14d08 = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d0c : bv 32 := 0x00a40533.
Lemma F_14d0c : fetch_word Plain.M.loaded_segments (0x14d0c : word) = Some W_14d0c.
Proof. vm_refl. Qed.
Lemma D_14d0c : decode_any W_14d0c = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d10 : bv 32 := 0x7ff50513.
Lemma F_14d10 : fetch_word Plain.M.loaded_segments (0x14d10 : word) = Some W_14d10.
Proof. vm_refl. Qed.
Lemma D_14d10 : decode_any W_14d10 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d14 : bv 32 := 0x00150513.
Lemma F_14d14 : fetch_word Plain.M.loaded_segments (0x14d14 : word) = Some W_14d14.
Proof. vm_refl. Qed.
Lemma D_14d14 : decode_any W_14d14 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d18 : bv 32 := 0x00aab023.
Lemma F_14d18 : fetch_word Plain.M.loaded_segments (0x14d18 : word) = Some W_14d18.
Proof. vm_refl. Qed.
Lemma D_14d18 : decode_any W_14d18 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d1c : bv 32 := 0x0289b503.
Lemma F_14d1c : fetch_word Plain.M.loaded_segments (0x14d1c : word) = Some W_14d1c.
Proof. vm_refl. Qed.
Lemma D_14d1c : decode_any W_14d1c = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d20 : bv 32 := 0x0089b583.
Lemma F_14d20 : fetch_word Plain.M.loaded_segments (0x14d20 : word) = Some W_14d20.
Proof. vm_refl. Qed.
Lemma D_14d20 : decode_any W_14d20 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d24 : bv 32 := 0x0109b603.
Lemma F_14d24 : fetch_word Plain.M.loaded_segments (0x14d24 : word) = Some W_14d24.
Proof. vm_refl. Qed.
Lemma D_14d24 : decode_any W_14d24 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d28 : bv 32 := 0x00a40533.
Lemma F_14d28 : fetch_word Plain.M.loaded_segments (0x14d28 : word) = Some W_14d28.
Proof. vm_refl. Qed.
Lemma D_14d28 : decode_any W_14d28 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d2c : bv 32 := 0x4bd0b0ef.
Lemma F_14d2c : fetch_word Plain.M.loaded_segments (0x14d2c : word) = Some W_14d2c.
Proof. vm_refl. Qed.
Lemma D_14d2c : decode_any W_14d2c = Some (Jal 1 48316, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d30 : bv 32 := 0x0009b983.
Lemma F_14d30 : fetch_word Plain.M.loaded_segments (0x14d30 : word) = Some W_14d30.
Proof. vm_refl. Qed.
Lemma D_14d30 : decode_any W_14d30 = Some (Load SZ8 true 19 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d34 : bv 32 := 0x008a8a93.
Lemma F_14d34 : fetch_word Plain.M.loaded_segments (0x14d34 : word) = Some W_14d34.
Proof. vm_refl. Qed.
Lemma D_14d34 : decode_any W_14d34 = Some (OpImm ALU_ADD 21 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d38 : bv 32 := 0xfc0998e3.
Lemma F_14d38 : fetch_word Plain.M.loaded_segments (0x14d38 : word) = Some W_14d38.
Proof. vm_refl. Qed.
Lemma D_14d38 : decode_any W_14d38 = Some (Branch BC_NE 19 0 8144, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d3c : bv 32 := 0x0284b603.
Lemma F_14d3c : fetch_word Plain.M.loaded_segments (0x14d3c : word) = Some W_14d3c.
Proof. vm_refl. Qed.
Lemma D_14d3c : decode_any W_14d3c = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d40 : bv 32 := 0x00ca3023.
Lemma F_14d40 : fetch_word Plain.M.loaded_segments (0x14d40 : word) = Some W_14d40.
Proof. vm_refl. Qed.
Lemma D_14d40 : decode_any W_14d40 = Some (Store SZ8 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_14d44 : bv 32 := 0x0d493023.
Lemma F_14d44 : fetch_word Plain.M.loaded_segments (0x14d44 : word) = Some W_14d44.
Proof. vm_refl. Qed.
Lemma D_14d44 : decode_any W_14d44 = Some (Store SZ8 18 20 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d48 : bv 32 := 0x01293023.
Lemma F_14d48 : fetch_word Plain.M.loaded_segments (0x14d48 : word) = Some W_14d48.
Proof. vm_refl. Qed.
Lemma D_14d48 : decode_any W_14d48 = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d4c : bv 32 := 0x00040513.
Lemma F_14d4c : fetch_word Plain.M.loaded_segments (0x14d4c : word) = Some W_14d4c.
Proof. vm_refl. Qed.
Lemma D_14d4c : decode_any W_14d4c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d50 : bv 32 := 0x5ec0c0ef.
Lemma F_14d50 : fetch_word Plain.M.loaded_segments (0x14d50 : word) = Some W_14d50.
Proof. vm_refl. Qed.
Lemma D_14d50 : decode_any W_14d50 = Some (Jal 1 50668, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d54 : bv 32 := 0x04054a63.
Lemma F_14d54 : fetch_word Plain.M.loaded_segments (0x14d54 : word) = Some W_14d54.
Proof. vm_refl. Qed.
Lemma D_14d54 : decode_any W_14d54 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d58 : bv 32 := 0x00051663.
Lemma F_14d58 : fetch_word Plain.M.loaded_segments (0x14d58 : word) = Some W_14d58.
Proof. vm_refl. Qed.
Lemma D_14d58 : decode_any W_14d58 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d5c : bv 32 := 0x00100513.
Lemma F_14d5c : fetch_word Plain.M.loaded_segments (0x14d5c : word) = Some W_14d5c.
Proof. vm_refl. Qed.
Lemma D_14d5c : decode_any W_14d5c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d60 : bv 32 := 0x00a48023.
Lemma F_14d60 : fetch_word Plain.M.loaded_segments (0x14d60 : word) = Some W_14d60.
Proof. vm_refl. Qed.
Lemma D_14d60 : decode_any W_14d60 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d64 : bv 32 := 0x00200513.
Lemma F_14d64 : fetch_word Plain.M.loaded_segments (0x14d64 : word) = Some W_14d64.
Proof. vm_refl. Qed.
Lemma D_14d64 : decode_any W_14d64 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d68 : bv 32 := 0x0003f597.
Lemma F_14d68 : fetch_word Plain.M.loaded_segments (0x14d68 : word) = Some W_14d68.
Proof. vm_refl. Qed.
Lemma D_14d68 : decode_any W_14d68 = Some (Auipc 11 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d6c : bv 32 := 0x02a92423.
Lemma F_14d6c : fetch_word Plain.M.loaded_segments (0x14d6c : word) = Some W_14d6c.
Proof. vm_refl. Qed.
Lemma D_14d6c : decode_any W_14d6c = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d70 : bv 32 := 0x06000893.
Lemma F_14d70 : fetch_word Plain.M.loaded_segments (0x14d70 : word) = Some W_14d70.
Proof. vm_refl. Qed.
Lemma D_14d70 : decode_any W_14d70 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d74 : bv 32 := 0xb3058513.
Lemma F_14d74 : fetch_word Plain.M.loaded_segments (0x14d74 : word) = Some W_14d74.
Proof. vm_refl. Qed.
Lemma D_14d74 : decode_any W_14d74 = Some (OpImm ALU_ADD 10 11 2864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d78 : bv 32 := 0x03848593.
Lemma F_14d78 : fetch_word Plain.M.loaded_segments (0x14d78 : word) = Some W_14d78.
Proof. vm_refl. Qed.
Lemma D_14d78 : decode_any W_14d78 = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d7c : bv 32 := 0x00000073.
Lemma F_14d7c : fetch_word Plain.M.loaded_segments (0x14d7c : word) = Some W_14d7c.
Proof. vm_refl. Qed.
Lemma D_14d7c : decode_any W_14d7c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_14d7c : is_ecall W_14d7c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_14d80 : bv 32 := 0x07890613.
Lemma F_14d80 : fetch_word Plain.M.loaded_segments (0x14d80 : word) = Some W_14d80.
Proof. vm_refl. Qed.
Lemma D_14d80 : decode_any W_14d80 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d84 : bv 32 := 0x02a92023.
Lemma F_14d84 : fetch_word Plain.M.loaded_segments (0x14d84 : word) = Some W_14d84.
Proof. vm_refl. Qed.
Lemma D_14d84 : decode_any W_14d84 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d88 : bv 32 := 0x08b93c23.
Lemma F_14d88 : fetch_word Plain.M.loaded_segments (0x14d88 : word) = Some W_14d88.
Proof. vm_refl. Qed.
Lemma D_14d88 : decode_any W_14d88 = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d8c : bv 32 := 0x06c93c23.
Lemma F_14d8c : fetch_word Plain.M.loaded_segments (0x14d8c : word) = Some W_14d8c.
Proof. vm_refl. Qed.
Lemma D_14d8c : decode_any W_14d8c = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d90 : bv 32 := 0x0003f517.
Lemma F_14d90 : fetch_word Plain.M.loaded_segments (0x14d90 : word) = Some W_14d90.
Proof. vm_refl. Qed.
Lemma D_14d90 : decode_any W_14d90 = Some (Auipc 10 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d94 : bv 32 := 0xd7053503.
Lemma F_14d94 : fetch_word Plain.M.loaded_segments (0x14d94 : word) = Some W_14d94.
Proof. vm_refl. Qed.
Lemma D_14d94 : decode_any W_14d94 = Some (Load SZ8 true 10 10 3440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d98 : bv 32 := 0x01293423.
Lemma F_14d98 : fetch_word Plain.M.loaded_segments (0x14d98 : word) = Some W_14d98.
Proof. vm_refl. Qed.
Lemma D_14d98 : decode_any W_14d98 = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14d9c : bv 32 := 0x01293823.
Lemma F_14d9c : fetch_word Plain.M.loaded_segments (0x14d9c : word) = Some W_14d9c.
Proof. vm_refl. Qed.
Lemma D_14d9c : decode_any W_14d9c = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14da0 : bv 32 := 0x00a93c23.
Lemma F_14da0 : fetch_word Plain.M.loaded_segments (0x14da0 : word) = Some W_14da0.
Proof. vm_refl. Qed.
Lemma D_14da0 : decode_any W_14da0 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14da4 : bv 32 := 0x0080006f.
Lemma F_14da4 : fetch_word Plain.M.loaded_segments (0x14da4 : word) = Some W_14da4.
Proof. vm_refl. Qed.
Lemma D_14da4 : decode_any W_14da4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_14da8 : bv 32 := 0x00000023.
Lemma F_14da8 : fetch_word Plain.M.loaded_segments (0x14da8 : word) = Some W_14da8.
Proof. vm_refl. Qed.
Lemma D_14da8 : decode_any W_14da8 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dac : bv 32 := 0x03813083.
Lemma F_14dac : fetch_word Plain.M.loaded_segments (0x14dac : word) = Some W_14dac.
Proof. vm_refl. Qed.
Lemma D_14dac : decode_any W_14dac = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14db0 : bv 32 := 0x03013403.
Lemma F_14db0 : fetch_word Plain.M.loaded_segments (0x14db0 : word) = Some W_14db0.
Proof. vm_refl. Qed.
Lemma D_14db0 : decode_any W_14db0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14db4 : bv 32 := 0x02813483.
Lemma F_14db4 : fetch_word Plain.M.loaded_segments (0x14db4 : word) = Some W_14db4.
Proof. vm_refl. Qed.
Lemma D_14db4 : decode_any W_14db4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14db8 : bv 32 := 0x02013903.
Lemma F_14db8 : fetch_word Plain.M.loaded_segments (0x14db8 : word) = Some W_14db8.
Proof. vm_refl. Qed.
Lemma D_14db8 : decode_any W_14db8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dbc : bv 32 := 0x01813983.
Lemma F_14dbc : fetch_word Plain.M.loaded_segments (0x14dbc : word) = Some W_14dbc.
Proof. vm_refl. Qed.
Lemma D_14dbc : decode_any W_14dbc = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dc0 : bv 32 := 0x01013a03.
Lemma F_14dc0 : fetch_word Plain.M.loaded_segments (0x14dc0 : word) = Some W_14dc0.
Proof. vm_refl. Qed.
Lemma D_14dc0 : decode_any W_14dc0 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dc4 : bv 32 := 0x00813a83.
Lemma F_14dc4 : fetch_word Plain.M.loaded_segments (0x14dc4 : word) = Some W_14dc4.
Proof. vm_refl. Qed.
Lemma D_14dc4 : decode_any W_14dc4 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dc8 : bv 32 := 0x04010113.
Lemma F_14dc8 : fetch_word Plain.M.loaded_segments (0x14dc8 : word) = Some W_14dc8.
Proof. vm_refl. Qed.
Lemma D_14dc8 : decode_any W_14dc8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14dcc : bv 32 := 0x00008067.
Lemma F_14dcc : fetch_word Plain.M.loaded_segments (0x14dcc : word) = Some W_14dcc.
Proof. vm_refl. Qed.
Lemma D_14dcc : decode_any W_14dcc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15128 : bv 32 := 0xff010113.
Lemma F_15128 : fetch_word Plain.M.loaded_segments (0x15128 : word) = Some W_15128.
Proof. vm_refl. Qed.
Lemma D_15128 : decode_any W_15128 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1512c : bv 32 := 0x00113423.
Lemma F_1512c : fetch_word Plain.M.loaded_segments (0x1512c : word) = Some W_1512c.
Proof. vm_refl. Qed.
Lemma D_1512c : decode_any W_1512c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15130 : bv 32 := 0x00050e63.
Lemma F_15130 : fetch_word Plain.M.loaded_segments (0x15130 : word) = Some W_15130.
Proof. vm_refl. Qed.
Lemma D_15130 : decode_any W_15130 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15134 : bv 32 := 0x00050593.
Lemma F_15134 : fetch_word Plain.M.loaded_segments (0x15134 : word) = Some W_15134.
Proof. vm_refl. Qed.
Lemma D_15134 : decode_any W_15134 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15138 : bv 32 := 0x0000d517.
Lemma F_15138 : fetch_word Plain.M.loaded_segments (0x15138 : word) = Some W_15138.
Proof. vm_refl. Qed.
Lemma D_15138 : decode_any W_15138 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1513c : bv 32 := 0x3b053503.
Lemma F_1513c : fetch_word Plain.M.loaded_segments (0x1513c : word) = Some W_1513c.
Proof. vm_refl. Qed.
Lemma D_1513c : decode_any W_1513c = Some (Load SZ8 true 10 10 944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15140 : bv 32 := 0x00800613.
Lemma F_15140 : fetch_word Plain.M.loaded_segments (0x15140 : word) = Some W_15140.
Proof. vm_refl. Qed.
Lemma D_15140 : decode_any W_15140 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15144 : bv 32 := 0x0a50b0ef.
Lemma F_15144 : fetch_word Plain.M.loaded_segments (0x15144 : word) = Some W_15144.
Proof. vm_refl. Qed.
Lemma D_15144 : decode_any W_15144 = Some (Jal 1 47268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15148 : bv 32 := 0x01c0006f.
Lemma F_15148 : fetch_word Plain.M.loaded_segments (0x15148 : word) = Some W_15148.
Proof. vm_refl. Qed.
Lemma D_15148 : decode_any W_15148 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15164 : bv 32 := 0x0000d517.
Lemma F_15164 : fetch_word Plain.M.loaded_segments (0x15164 : word) = Some W_15164.
Proof. vm_refl. Qed.
Lemma D_15164 : decode_any W_15164 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15168 : bv 32 := 0x38453503.
Lemma F_15168 : fetch_word Plain.M.loaded_segments (0x15168 : word) = Some W_15168.
Proof. vm_refl. Qed.
Lemma D_15168 : decode_any W_15168 = Some (Load SZ8 true 10 10 900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1516c : bv 32 := 0x000500a3.
Lemma F_1516c : fetch_word Plain.M.loaded_segments (0x1516c : word) = Some W_1516c.
Proof. vm_refl. Qed.
Lemma D_1516c : decode_any W_1516c = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15170 : bv 32 := 0x00053503.
Lemma F_15170 : fetch_word Plain.M.loaded_segments (0x15170 : word) = Some W_15170.
Proof. vm_refl. Qed.
Lemma D_15170 : decode_any W_15170 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15174 : bv 32 := 0x00020593.
Lemma F_15174 : fetch_word Plain.M.loaded_segments (0x15174 : word) = Some W_15174.
Proof. vm_refl. Qed.
Lemma D_15174 : decode_any W_15174 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15178 : bv 32 := 0xfea5b823.
Lemma F_15178 : fetch_word Plain.M.loaded_segments (0x15178 : word) = Some W_15178.
Proof. vm_refl. Qed.
Lemma D_15178 : decode_any W_15178 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1517c : bv 32 := 0x00813083.
Lemma F_1517c : fetch_word Plain.M.loaded_segments (0x1517c : word) = Some W_1517c.
Proof. vm_refl. Qed.
Lemma D_1517c : decode_any W_1517c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15180 : bv 32 := 0x01010113.
Lemma F_15180 : fetch_word Plain.M.loaded_segments (0x15180 : word) = Some W_15180.
Proof. vm_refl. Qed.
Lemma D_15180 : decode_any W_15180 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15184 : bv 32 := 0x00008067.
Lemma F_15184 : fetch_word Plain.M.loaded_segments (0x15184 : word) = Some W_15184.
Proof. vm_refl. Qed.
Lemma D_15184 : decode_any W_15184 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_209e8 : bv 32 := 0x0035f693.
Lemma F_209e8 : fetch_word Plain.M.loaded_segments (0x209e8 : word) = Some W_209e8.
Proof. vm_refl. Qed.
Lemma D_209e8 : decode_any W_209e8 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_209ec : bv 32 := 0x10068863.
Lemma F_209ec : fetch_word Plain.M.loaded_segments (0x209ec : word) = Some W_209ec.
Proof. vm_refl. Qed.
Lemma D_209ec : decode_any W_209ec = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20afc : bv 32 := 0x00050693.
Lemma F_20afc : fetch_word Plain.M.loaded_segments (0x20afc : word) = Some W_20afc.
Proof. vm_refl. Qed.
Lemma D_20afc : decode_any W_20afc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b00 : bv 32 := 0x00357793.
Lemma F_20b00 : fetch_word Plain.M.loaded_segments (0x20b00 : word) = Some W_20b00.
Proof. vm_refl. Qed.
Lemma D_20b00 : decode_any W_20b00 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b04 : bv 32 := 0xf2079ae3.
Lemma F_20b04 : fetch_word Plain.M.loaded_segments (0x20b04 : word) = Some W_20b04.
Proof. vm_refl. Qed.
Lemma D_20b04 : decode_any W_20b04 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b08 : bv 32 := 0x01000713.
Lemma F_20b08 : fetch_word Plain.M.loaded_segments (0x20b08 : word) = Some W_20b08.
Proof. vm_refl. Qed.
Lemma D_20b08 : decode_any W_20b08 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b0c : bv 32 := 0x02e66c63.
Lemma F_20b0c : fetch_word Plain.M.loaded_segments (0x20b0c : word) = Some W_20b0c.
Proof. vm_refl. Qed.
Lemma D_20b0c : decode_any W_20b0c = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b44 : bv 32 := 0x00800713.
Lemma F_20b44 : fetch_word Plain.M.loaded_segments (0x20b44 : word) = Some W_20b44.
Proof. vm_refl. Qed.
Lemma D_20b44 : decode_any W_20b44 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b48 : bv 32 := 0x00e66e63.
Lemma F_20b48 : fetch_word Plain.M.loaded_segments (0x20b48 : word) = Some W_20b48.
Proof. vm_refl. Qed.
Lemma D_20b48 : decode_any W_20b48 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b4c : bv 32 := 0x0005a703.
Lemma F_20b4c : fetch_word Plain.M.loaded_segments (0x20b4c : word) = Some W_20b4c.
Proof. vm_refl. Qed.
Lemma D_20b4c : decode_any W_20b4c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b50 : bv 32 := 0x0045a783.
Lemma F_20b50 : fetch_word Plain.M.loaded_segments (0x20b50 : word) = Some W_20b50.
Proof. vm_refl. Qed.
Lemma D_20b50 : decode_any W_20b50 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b54 : bv 32 := 0x00e6a023.
Lemma F_20b54 : fetch_word Plain.M.loaded_segments (0x20b54 : word) = Some W_20b54.
Proof. vm_refl. Qed.
Lemma D_20b54 : decode_any W_20b54 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b58 : bv 32 := 0x00f6a223.
Lemma F_20b58 : fetch_word Plain.M.loaded_segments (0x20b58 : word) = Some W_20b58.
Proof. vm_refl. Qed.
Lemma D_20b58 : decode_any W_20b58 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b5c : bv 32 := 0x00868693.
Lemma F_20b5c : fetch_word Plain.M.loaded_segments (0x20b5c : word) = Some W_20b5c.
Proof. vm_refl. Qed.
Lemma D_20b5c : decode_any W_20b5c = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b60 : bv 32 := 0x00858593.
Lemma F_20b60 : fetch_word Plain.M.loaded_segments (0x20b60 : word) = Some W_20b60.
Proof. vm_refl. Qed.
Lemma D_20b60 : decode_any W_20b60 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b64 : bv 32 := 0x00467713.
Lemma F_20b64 : fetch_word Plain.M.loaded_segments (0x20b64 : word) = Some W_20b64.
Proof. vm_refl. Qed.
Lemma D_20b64 : decode_any W_20b64 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20b68 : bv 32 := 0x24070063.
Lemma F_20b68 : fetch_word Plain.M.loaded_segments (0x20b68 : word) = Some W_20b68.
Proof. vm_refl. Qed.
Lemma D_20b68 : decode_any W_20b68 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20da8 : bv 32 := 0x00267713.
Lemma F_20da8 : fetch_word Plain.M.loaded_segments (0x20da8 : word) = Some W_20da8.
Proof. vm_refl. Qed.
Lemma D_20da8 : decode_any W_20da8 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20dac : bv 32 := 0x00071863.
Lemma F_20dac : fetch_word Plain.M.loaded_segments (0x20dac : word) = Some W_20dac.
Proof. vm_refl. Qed.
Lemma D_20dac : decode_any W_20dac = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20db0 : bv 32 := 0x00167613.
Lemma F_20db0 : fetch_word Plain.M.loaded_segments (0x20db0 : word) = Some W_20db0.
Proof. vm_refl. Qed.
Lemma D_20db0 : decode_any W_20db0 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20db4 : bv 32 := 0x02061663.
Lemma F_20db4 : fetch_word Plain.M.loaded_segments (0x20db4 : word) = Some W_20db4.
Proof. vm_refl. Qed.
Lemma D_20db4 : decode_any W_20db4 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20db8 : bv 32 := 0x00008067.
Lemma F_20db8 : fetch_word Plain.M.loaded_segments (0x20db8 : word) = Some W_20db8.
Proof. vm_refl. Qed.
Lemma D_20db8 : decode_any W_20db8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20dec : bv 32 := 0x0e060a63.
Lemma F_20dec : fetch_word Plain.M.loaded_segments (0x20dec : word) = Some W_20dec.
Proof. vm_refl. Qed.
Lemma D_20dec : decode_any W_20dec = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20df0 : bv 32 := 0x00b50023.
Lemma F_20df0 : fetch_word Plain.M.loaded_segments (0x20df0 : word) = Some W_20df0.
Proof. vm_refl. Qed.
Lemma D_20df0 : decode_any W_20df0 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20df4 : bv 32 := 0x00c506b3.
Lemma F_20df4 : fetch_word Plain.M.loaded_segments (0x20df4 : word) = Some W_20df4.
Proof. vm_refl. Qed.
Lemma D_20df4 : decode_any W_20df4 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20df8 : bv 32 := 0x00300713.
Lemma F_20df8 : fetch_word Plain.M.loaded_segments (0x20df8 : word) = Some W_20df8.
Proof. vm_refl. Qed.
Lemma D_20df8 : decode_any W_20df8 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20dfc : bv 32 := 0xfeb68fa3.
Lemma F_20dfc : fetch_word Plain.M.loaded_segments (0x20dfc : word) = Some W_20dfc.
Proof. vm_refl. Qed.
Lemma D_20dfc : decode_any W_20dfc = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e00 : bv 32 := 0x0ee66063.
Lemma F_20e00 : fetch_word Plain.M.loaded_segments (0x20e00 : word) = Some W_20e00.
Proof. vm_refl. Qed.
Lemma D_20e00 : decode_any W_20e00 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e04 : bv 32 := 0x00b500a3.
Lemma F_20e04 : fetch_word Plain.M.loaded_segments (0x20e04 : word) = Some W_20e04.
Proof. vm_refl. Qed.
Lemma D_20e04 : decode_any W_20e04 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e08 : bv 32 := 0x00b50123.
Lemma F_20e08 : fetch_word Plain.M.loaded_segments (0x20e08 : word) = Some W_20e08.
Proof. vm_refl. Qed.
Lemma D_20e08 : decode_any W_20e08 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e0c : bv 32 := 0x00700713.
Lemma F_20e0c : fetch_word Plain.M.loaded_segments (0x20e0c : word) = Some W_20e0c.
Proof. vm_refl. Qed.
Lemma D_20e0c : decode_any W_20e0c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e10 : bv 32 := 0xfeb68ea3.
Lemma F_20e10 : fetch_word Plain.M.loaded_segments (0x20e10 : word) = Some W_20e10.
Proof. vm_refl. Qed.
Lemma D_20e10 : decode_any W_20e10 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e14 : bv 32 := 0xfeb68f23.
Lemma F_20e14 : fetch_word Plain.M.loaded_segments (0x20e14 : word) = Some W_20e14.
Proof. vm_refl. Qed.
Lemma D_20e14 : decode_any W_20e14 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e18 : bv 32 := 0x0ce66463.
Lemma F_20e18 : fetch_word Plain.M.loaded_segments (0x20e18 : word) = Some W_20e18.
Proof. vm_refl. Qed.
Lemma D_20e18 : decode_any W_20e18 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e1c : bv 32 := 0x00b501a3.
Lemma F_20e1c : fetch_word Plain.M.loaded_segments (0x20e1c : word) = Some W_20e1c.
Proof. vm_refl. Qed.
Lemma D_20e1c : decode_any W_20e1c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e20 : bv 32 := 0x00900793.
Lemma F_20e20 : fetch_word Plain.M.loaded_segments (0x20e20 : word) = Some W_20e20.
Proof. vm_refl. Qed.
Lemma D_20e20 : decode_any W_20e20 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e24 : bv 32 := 0xfeb68e23.
Lemma F_20e24 : fetch_word Plain.M.loaded_segments (0x20e24 : word) = Some W_20e24.
Proof. vm_refl. Qed.
Lemma D_20e24 : decode_any W_20e24 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e28 : bv 32 := 0x0af66c63.
Lemma F_20e28 : fetch_word Plain.M.loaded_segments (0x20e28 : word) = Some W_20e28.
Proof. vm_refl. Qed.
Lemma D_20e28 : decode_any W_20e28 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e2c : bv 32 := 0x40a006bb.
Lemma F_20e2c : fetch_word Plain.M.loaded_segments (0x20e2c : word) = Some W_20e2c.
Proof. vm_refl. Qed.
Lemma D_20e2c : decode_any W_20e2c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e30 : bv 32 := 0x03859813.
Lemma F_20e30 : fetch_word Plain.M.loaded_segments (0x20e30 : word) = Some W_20e30.
Proof. vm_refl. Qed.
Lemma D_20e30 : decode_any W_20e30 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e34 : bv 32 := 0x101015b7.
Lemma F_20e34 : fetch_word Plain.M.loaded_segments (0x20e34 : word) = Some W_20e34.
Proof. vm_refl. Qed.
Lemma D_20e34 : decode_any W_20e34 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e38 : bv 32 := 0x0036f693.
Lemma F_20e38 : fetch_word Plain.M.loaded_segments (0x20e38 : word) = Some W_20e38.
Proof. vm_refl. Qed.
Lemma D_20e38 : decode_any W_20e38 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e3c : bv 32 := 0x00459713.
Lemma F_20e3c : fetch_word Plain.M.loaded_segments (0x20e3c : word) = Some W_20e3c.
Proof. vm_refl. Qed.
Lemma D_20e3c : decode_any W_20e3c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e40 : bv 32 := 0x40d60633.
Lemma F_20e40 : fetch_word Plain.M.loaded_segments (0x20e40 : word) = Some W_20e40.
Proof. vm_refl. Qed.
Lemma D_20e40 : decode_any W_20e40 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e44 : bv 32 := 0x00d505b3.
Lemma F_20e44 : fetch_word Plain.M.loaded_segments (0x20e44 : word) = Some W_20e44.
Proof. vm_refl. Qed.
Lemma D_20e44 : decode_any W_20e44 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e48 : bv 32 := 0x10070693.
Lemma F_20e48 : fetch_word Plain.M.loaded_segments (0x20e48 : word) = Some W_20e48.
Proof. vm_refl. Qed.
Lemma D_20e48 : decode_any W_20e48 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e4c : bv 32 := 0xffc67713.
Lemma F_20e4c : fetch_word Plain.M.loaded_segments (0x20e4c : word) = Some W_20e4c.
Proof. vm_refl. Qed.
Lemma D_20e4c : decode_any W_20e4c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e50 : bv 32 := 0x02d83633.
Lemma F_20e50 : fetch_word Plain.M.loaded_segments (0x20e50 : word) = Some W_20e50.
Proof. vm_refl. Qed.
Lemma D_20e50 : decode_any W_20e50 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e54 : bv 32 := 0x00c5a023.
Lemma F_20e54 : fetch_word Plain.M.loaded_segments (0x20e54 : word) = Some W_20e54.
Proof. vm_refl. Qed.
Lemma D_20e54 : decode_any W_20e54 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e58 : bv 32 := 0x00e586b3.
Lemma F_20e58 : fetch_word Plain.M.loaded_segments (0x20e58 : word) = Some W_20e58.
Proof. vm_refl. Qed.
Lemma D_20e58 : decode_any W_20e58 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e5c : bv 32 := 0xfec6ae23.
Lemma F_20e5c : fetch_word Plain.M.loaded_segments (0x20e5c : word) = Some W_20e5c.
Proof. vm_refl. Qed.
Lemma D_20e5c : decode_any W_20e5c = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e60 : bv 32 := 0x08f76063.
Lemma F_20e60 : fetch_word Plain.M.loaded_segments (0x20e60 : word) = Some W_20e60.
Proof. vm_refl. Qed.
Lemma D_20e60 : decode_any W_20e60 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e64 : bv 32 := 0x00c5a223.
Lemma F_20e64 : fetch_word Plain.M.loaded_segments (0x20e64 : word) = Some W_20e64.
Proof. vm_refl. Qed.
Lemma D_20e64 : decode_any W_20e64 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e68 : bv 32 := 0x00c5a423.
Lemma F_20e68 : fetch_word Plain.M.loaded_segments (0x20e68 : word) = Some W_20e68.
Proof. vm_refl. Qed.
Lemma D_20e68 : decode_any W_20e68 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e6c : bv 32 := 0x01900793.
Lemma F_20e6c : fetch_word Plain.M.loaded_segments (0x20e6c : word) = Some W_20e6c.
Proof. vm_refl. Qed.
Lemma D_20e6c : decode_any W_20e6c = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e70 : bv 32 := 0xfec6aa23.
Lemma F_20e70 : fetch_word Plain.M.loaded_segments (0x20e70 : word) = Some W_20e70.
Proof. vm_refl. Qed.
Lemma D_20e70 : decode_any W_20e70 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e74 : bv 32 := 0xfec6ac23.
Lemma F_20e74 : fetch_word Plain.M.loaded_segments (0x20e74 : word) = Some W_20e74.
Proof. vm_refl. Qed.
Lemma D_20e74 : decode_any W_20e74 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e78 : bv 32 := 0x06f76463.
Lemma F_20e78 : fetch_word Plain.M.loaded_segments (0x20e78 : word) = Some W_20e78.
Proof. vm_refl. Qed.
Lemma D_20e78 : decode_any W_20e78 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e7c : bv 32 := 0x00c5a623.
Lemma F_20e7c : fetch_word Plain.M.loaded_segments (0x20e7c : word) = Some W_20e7c.
Proof. vm_refl. Qed.
Lemma D_20e7c : decode_any W_20e7c = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e80 : bv 32 := 0x00c5a823.
Lemma F_20e80 : fetch_word Plain.M.loaded_segments (0x20e80 : word) = Some W_20e80.
Proof. vm_refl. Qed.
Lemma D_20e80 : decode_any W_20e80 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e84 : bv 32 := 0x00c5aa23.
Lemma F_20e84 : fetch_word Plain.M.loaded_segments (0x20e84 : word) = Some W_20e84.
Proof. vm_refl. Qed.
Lemma D_20e84 : decode_any W_20e84 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e88 : bv 32 := 0x00c5ac23.
Lemma F_20e88 : fetch_word Plain.M.loaded_segments (0x20e88 : word) = Some W_20e88.
Proof. vm_refl. Qed.
Lemma D_20e88 : decode_any W_20e88 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e8c : bv 32 := 0x0045f793.
Lemma F_20e8c : fetch_word Plain.M.loaded_segments (0x20e8c : word) = Some W_20e8c.
Proof. vm_refl. Qed.
Lemma D_20e8c : decode_any W_20e8c = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e90 : bv 32 := 0x02000813.
Lemma F_20e90 : fetch_word Plain.M.loaded_segments (0x20e90 : word) = Some W_20e90.
Proof. vm_refl. Qed.
Lemma D_20e90 : decode_any W_20e90 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e94 : bv 32 := 0x01878793.
Lemma F_20e94 : fetch_word Plain.M.loaded_segments (0x20e94 : word) = Some W_20e94.
Proof. vm_refl. Qed.
Lemma D_20e94 : decode_any W_20e94 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e98 : bv 32 := 0x40f70733.
Lemma F_20e98 : fetch_word Plain.M.loaded_segments (0x20e98 : word) = Some W_20e98.
Proof. vm_refl. Qed.
Lemma D_20e98 : decode_any W_20e98 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20e9c : bv 32 := 0xfec6a223.
Lemma F_20e9c : fetch_word Plain.M.loaded_segments (0x20e9c : word) = Some W_20e9c.
Proof. vm_refl. Qed.
Lemma D_20e9c : decode_any W_20e9c = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ea0 : bv 32 := 0xfec6a423.
Lemma F_20ea0 : fetch_word Plain.M.loaded_segments (0x20ea0 : word) = Some W_20ea0.
Proof. vm_refl. Qed.
Lemma D_20ea0 : decode_any W_20ea0 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ea4 : bv 32 := 0xfec6a623.
Lemma F_20ea4 : fetch_word Plain.M.loaded_segments (0x20ea4 : word) = Some W_20ea4.
Proof. vm_refl. Qed.
Lemma D_20ea4 : decode_any W_20ea4 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ea8 : bv 32 := 0xfec6a823.
Lemma F_20ea8 : fetch_word Plain.M.loaded_segments (0x20ea8 : word) = Some W_20ea8.
Proof. vm_refl. Qed.
Lemma D_20ea8 : decode_any W_20ea8 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20eac : bv 32 := 0x03076a63.
Lemma F_20eac : fetch_word Plain.M.loaded_segments (0x20eac : word) = Some W_20eac.
Proof. vm_refl. Qed.
Lemma D_20eac : decode_any W_20eac = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20eb0 : bv 32 := 0x02061613.
Lemma F_20eb0 : fetch_word Plain.M.loaded_segments (0x20eb0 : word) = Some W_20eb0.
Proof. vm_refl. Qed.
Lemma D_20eb0 : decode_any W_20eb0 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20eb4 : bv 32 := 0x00f585b3.
Lemma F_20eb4 : fetch_word Plain.M.loaded_segments (0x20eb4 : word) = Some W_20eb4.
Proof. vm_refl. Qed.
Lemma D_20eb4 : decode_any W_20eb4 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20eb8 : bv 32 := 0x02065693.
Lemma F_20eb8 : fetch_word Plain.M.loaded_segments (0x20eb8 : word) = Some W_20eb8.
Proof. vm_refl. Qed.
Lemma D_20eb8 : decode_any W_20eb8 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ebc : bv 32 := 0x00d66633.
Lemma F_20ebc : fetch_word Plain.M.loaded_segments (0x20ebc : word) = Some W_20ebc.
Proof. vm_refl. Qed.
Lemma D_20ebc : decode_any W_20ebc = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ec0 : bv 32 := 0x01f00693.
Lemma F_20ec0 : fetch_word Plain.M.loaded_segments (0x20ec0 : word) = Some W_20ec0.
Proof. vm_refl. Qed.
Lemma D_20ec0 : decode_any W_20ec0 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ec4 : bv 32 := 0x00c5b023.
Lemma F_20ec4 : fetch_word Plain.M.loaded_segments (0x20ec4 : word) = Some W_20ec4.
Proof. vm_refl. Qed.
Lemma D_20ec4 : decode_any W_20ec4 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ec8 : bv 32 := 0x00c5b423.
Lemma F_20ec8 : fetch_word Plain.M.loaded_segments (0x20ec8 : word) = Some W_20ec8.
Proof. vm_refl. Qed.
Lemma D_20ec8 : decode_any W_20ec8 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ecc : bv 32 := 0x00c5b823.
Lemma F_20ecc : fetch_word Plain.M.loaded_segments (0x20ecc : word) = Some W_20ecc.
Proof. vm_refl. Qed.
Lemma D_20ecc : decode_any W_20ecc = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ed0 : bv 32 := 0x00c5bc23.
Lemma F_20ed0 : fetch_word Plain.M.loaded_segments (0x20ed0 : word) = Some W_20ed0.
Proof. vm_refl. Qed.
Lemma D_20ed0 : decode_any W_20ed0 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ed4 : bv 32 := 0xfe070713.
Lemma F_20ed4 : fetch_word Plain.M.loaded_segments (0x20ed4 : word) = Some W_20ed4.
Proof. vm_refl. Qed.
Lemma D_20ed4 : decode_any W_20ed4 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ed8 : bv 32 := 0x02058593.
Lemma F_20ed8 : fetch_word Plain.M.loaded_segments (0x20ed8 : word) = Some W_20ed8.
Proof. vm_refl. Qed.
Lemma D_20ed8 : decode_any W_20ed8 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20edc : bv 32 := 0xfee6e4e3.
Lemma F_20edc : fetch_word Plain.M.loaded_segments (0x20edc : word) = Some W_20edc.
Proof. vm_refl. Qed.
Lemma D_20edc : decode_any W_20edc = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_20ee0 : bv 32 := 0x00008067.
Lemma F_20ee0 : fetch_word Plain.M.loaded_segments (0x20ee0 : word) = Some W_20ee0.
Proof. vm_refl. Qed.
Lemma D_20ee0 : decode_any W_20ee0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2133c : bv 32 := 0x00050213.
Lemma F_2133c : fetch_word Plain.M.loaded_segments (0x2133c : word) = Some W_2133c.
Proof. vm_refl. Qed.
Lemma D_2133c : decode_any W_2133c = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21340 : bv 32 := 0x00000513.
Lemma F_21340 : fetch_word Plain.M.loaded_segments (0x21340 : word) = Some W_21340.
Proof. vm_refl. Qed.
Lemma D_21340 : decode_any W_21340 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_21344 : bv 32 := 0x00008067.
Lemma F_21344 : fetch_word Plain.M.loaded_segments (0x21344 : word) = Some W_21344.
Proof. vm_refl. Qed.
Lemma D_21344 : decode_any W_21344 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
