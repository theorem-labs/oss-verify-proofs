(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_16fa0 : bv 32 := 0xfe010113.
Lemma F_16fa0 : fetch_word Ubsan.M.loaded_segments (0x170a4 : word) = Some W_16fa0.
Proof. vm_refl. Qed.
Lemma D_16fa0 : decode_any W_16fa0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fa4 : bv 32 := 0x00113c23.
Lemma F_16fa4 : fetch_word Ubsan.M.loaded_segments (0x170a8 : word) = Some W_16fa4.
Proof. vm_refl. Qed.
Lemma D_16fa4 : decode_any W_16fa4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fa8 : bv 32 := 0x00813823.
Lemma F_16fa8 : fetch_word Ubsan.M.loaded_segments (0x170ac : word) = Some W_16fa8.
Proof. vm_refl. Qed.
Lemma D_16fa8 : decode_any W_16fa8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fac : bv 32 := 0x00913423.
Lemma F_16fac : fetch_word Ubsan.M.loaded_segments (0x170b0 : word) = Some W_16fac.
Proof. vm_refl. Qed.
Lemma D_16fac : decode_any W_16fac = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fb0 : bv 32 := 0x08050063.
Lemma F_16fb0 : fetch_word Ubsan.M.loaded_segments (0x170b4 : word) = Some W_16fb0.
Proof. vm_refl. Qed.
Lemma D_16fb0 : decode_any W_16fb0 = Some (Branch BC_EQ 10 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fb4 : bv 32 := 0x00757593.
Lemma F_16fb4 : fetch_word Ubsan.M.loaded_segments (0x170b8 : word) = Some W_16fb4.
Proof. vm_refl. Qed.
Lemma D_16fb4 : decode_any W_16fb4 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fb8 : bv 32 := 0x0c059263.
Lemma F_16fb8 : fetch_word Ubsan.M.loaded_segments (0x170bc : word) = Some W_16fb8.
Proof. vm_refl. Qed.
Lemma D_16fb8 : decode_any W_16fb8 = Some (Branch BC_NE 11 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fbc : bv 32 := 0x00053403.
Lemma F_16fbc : fetch_word Ubsan.M.loaded_segments (0x170c0 : word) = Some W_16fbc.
Proof. vm_refl. Qed.
Lemma D_16fbc : decode_any W_16fbc = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fc0 : bv 32 := 0x0a040463.
Lemma F_16fc0 : fetch_word Ubsan.M.loaded_segments (0x170c4 : word) = Some W_16fc0.
Proof. vm_refl. Qed.
Lemma D_16fc0 : decode_any W_16fc0 = Some (Branch BC_EQ 8 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fc4 : bv 32 := 0x00747593.
Lemma F_16fc4 : fetch_word Ubsan.M.loaded_segments (0x170c8 : word) = Some W_16fc4.
Proof. vm_refl. Qed.
Lemma D_16fc4 : decode_any W_16fc4 = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fc8 : bv 32 := 0x0a059a63.
Lemma F_16fc8 : fetch_word Ubsan.M.loaded_segments (0x170cc : word) = Some W_16fc8.
Proof. vm_refl. Qed.
Lemma D_16fc8 : decode_any W_16fc8 = Some (Branch BC_NE 11 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fcc : bv 32 := 0x01440593.
Lemma F_16fcc : fetch_word Ubsan.M.loaded_segments (0x170d0 : word) = Some W_16fcc.
Proof. vm_refl. Qed.
Lemma D_16fcc : decode_any W_16fcc = Some (OpImm ALU_ADD 11 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fd0 : bv 32 := 0xfff00613.
Lemma F_16fd0 : fetch_word Ubsan.M.loaded_segments (0x170d4 : word) = Some W_16fd0.
Proof. vm_refl. Qed.
Lemma D_16fd0 : decode_any W_16fd0 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fd4 : bv 32 := 0x06c5a5af.
Lemma F_16fd4 : fetch_word Ubsan.M.loaded_segments (0x170d8 : word) = Some W_16fd4.
Proof. vm_refl. Qed.
Lemma D_16fd4 : decode_any W_16fd4 = Some (Amo AMO_ADD AW true true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fd8 : bv 32 := 0x00100613.
Lemma F_16fd8 : fetch_word Ubsan.M.loaded_segments (0x170dc : word) = Some W_16fd8.
Proof. vm_refl. Qed.
Lemma D_16fd8 : decode_any W_16fd8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fdc : bv 32 := 0x04c59663.
Lemma F_16fdc : fetch_word Ubsan.M.loaded_segments (0x170e0 : word) = Some W_16fdc.
Proof. vm_refl. Qed.
Lemma D_16fdc : decode_any W_16fdc = Some (Branch BC_NE 11 12 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fe0 : bv 32 := 0x00050493.
Lemma F_16fe0 : fetch_word Ubsan.M.loaded_segments (0x170e4 : word) = Some W_16fe0.
Proof. vm_refl. Qed.
Lemma D_16fe0 : decode_any W_16fe0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fe4 : bv 32 := 0x03843503.
Lemma F_16fe4 : fetch_word Ubsan.M.loaded_segments (0x170e8 : word) = Some W_16fe4.
Proof. vm_refl. Qed.
Lemma D_16fe4 : decode_any W_16fe4 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fe8 : bv 32 := 0x00050863.
Lemma F_16fe8 : fetch_word Ubsan.M.loaded_segments (0x170ec : word) = Some W_16fe8.
Proof. vm_refl. Qed.
Lemma D_16fe8 : decode_any W_16fe8 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16fec : bv 32 := 0x0001e597.
Lemma F_16fec : fetch_word Ubsan.M.loaded_segments (0x170f0 : word) = Some W_16fec.
Proof. vm_refl. Qed.
Lemma D_16fec : decode_any W_16fec = Some (Auipc 11 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ff0 : bv 32 := 0x1905b583.
Lemma F_16ff0 : fetch_word Ubsan.M.loaded_segments (0x170f4 : word) = Some W_16ff0.
Proof. vm_refl. Qed.
Lemma D_16ff0 : decode_any W_16ff0 = Some (Load SZ8 true 11 11 400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ff4 : bv 32 := 0x000580e7.
Lemma F_16ff4 : fetch_word Ubsan.M.loaded_segments (0x170f8 : word) = Some W_16ff4.
Proof. vm_refl. Qed.
Lemma D_16ff4 : decode_any W_16ff4 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ff8 : bv 32 := 0x02843503.
Lemma F_16ff8 : fetch_word Ubsan.M.loaded_segments (0x170fc : word) = Some W_16ff8.
Proof. vm_refl. Qed.
Lemma D_16ff8 : decode_any W_16ff8 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16ffc : bv 32 := 0x00050463.
Lemma F_16ffc : fetch_word Ubsan.M.loaded_segments (0x17100 : word) = Some W_16ffc.
Proof. vm_refl. Qed.
Lemma D_16ffc : decode_any W_16ffc = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17004 : bv 32 := 0x03043503.
Lemma F_17004 : fetch_word Ubsan.M.loaded_segments (0x17108 : word) = Some W_17004.
Proof. vm_refl. Qed.
Lemma D_17004 : decode_any W_17004 = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17008 : bv 32 := 0x00a13023.
Lemma F_17008 : fetch_word Ubsan.M.loaded_segments (0x1710c : word) = Some W_17008.
Proof. vm_refl. Qed.
Lemma D_17008 : decode_any W_17008 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1700c : bv 32 := 0x00050863.
Lemma F_1700c : fetch_word Ubsan.M.loaded_segments (0x17110 : word) = Some W_1700c.
Proof. vm_refl. Qed.
Lemma D_1700c : decode_any W_1700c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17010 : bv 32 := 0x00010513.
Lemma F_17010 : fetch_word Ubsan.M.loaded_segments (0x17114 : word) = Some W_17010.
Proof. vm_refl. Qed.
Lemma D_17010 : decode_any W_17010 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17014 : bv 32 := 0x289010ef.
Lemma F_17014 : fetch_word Ubsan.M.loaded_segments (0x17118 : word) = Some W_17014.
Proof. vm_refl. Qed.
Lemma D_17014 : decode_any W_17014 = Some (Jal 1 6792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17018 : bv 32 := 0x02043823.
Lemma F_17018 : fetch_word Ubsan.M.loaded_segments (0x1711c : word) = Some W_17018.
Proof. vm_refl. Qed.
Lemma D_17018 : decode_any W_17018 = Some (Store SZ8 8 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1701c : bv 32 := 0x00040513.
Lemma F_1701c : fetch_word Ubsan.M.loaded_segments (0x17120 : word) = Some W_1701c.
Proof. vm_refl. Qed.
Lemma D_1701c : decode_any W_1701c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17020 : bv 32 := 0x131110ef.
Lemma F_17020 : fetch_word Ubsan.M.loaded_segments (0x17124 : word) = Some W_17020.
Proof. vm_refl. Qed.
Lemma D_17020 : decode_any W_17020 = Some (Jal 1 71984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17024 : bv 32 := 0x00048513.
Lemma F_17024 : fetch_word Ubsan.M.loaded_segments (0x17128 : word) = Some W_17024.
Proof. vm_refl. Qed.
Lemma D_17024 : decode_any W_17024 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17028 : bv 32 := 0x00053023.
Lemma F_17028 : fetch_word Ubsan.M.loaded_segments (0x1712c : word) = Some W_17028.
Proof. vm_refl. Qed.
Lemma D_17028 : decode_any W_17028 = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1702c : bv 32 := 0x03c0006f.
Lemma F_1702c : fetch_word Ubsan.M.loaded_segments (0x17130 : word) = Some W_1702c.
Proof. vm_refl. Qed.
Lemma D_1702c : decode_any W_1702c = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17068 : bv 32 := 0x01813083.
Lemma F_17068 : fetch_word Ubsan.M.loaded_segments (0x1716c : word) = Some W_17068.
Proof. vm_refl. Qed.
Lemma D_17068 : decode_any W_17068 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1706c : bv 32 := 0x01013403.
Lemma F_1706c : fetch_word Ubsan.M.loaded_segments (0x17170 : word) = Some W_1706c.
Proof. vm_refl. Qed.
Lemma D_1706c : decode_any W_1706c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17070 : bv 32 := 0x00813483.
Lemma F_17070 : fetch_word Ubsan.M.loaded_segments (0x17174 : word) = Some W_17070.
Proof. vm_refl. Qed.
Lemma D_17070 : decode_any W_17070 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17074 : bv 32 := 0x02010113.
Lemma F_17074 : fetch_word Ubsan.M.loaded_segments (0x17178 : word) = Some W_17074.
Proof. vm_refl. Qed.
Lemma D_17074 : decode_any W_17074 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17078 : bv 32 := 0x00008067.
Lemma F_17078 : fetch_word Ubsan.M.loaded_segments (0x1717c : word) = Some W_17078.
Proof. vm_refl. Qed.
Lemma D_17078 : decode_any W_17078 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

