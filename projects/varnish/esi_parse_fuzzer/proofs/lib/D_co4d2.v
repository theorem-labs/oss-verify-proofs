(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_17a18 : bv 32 := 0xffff9197.
Lemma F_17a18 : fetch_word Plain.M.loaded_segments (0x17a18 : word) = Some W_17a18.
Proof. vm_refl. Qed.
Lemma D_17a18 : decode_any W_17a18 = Some (Auipc 3 1048569, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a1c : bv 32 := 0xde818193.
Lemma F_17a1c : fetch_word Plain.M.loaded_segments (0x17a1c : word) = Some W_17a1c.
Proof. vm_refl. Qed.
Lemma D_17a1c : decode_any W_17a1c = Some (OpImm ALU_ADD 3 3 3560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a20 : bv 32 := 0x00010513.
Lemma F_17a20 : fetch_word Plain.M.loaded_segments (0x17a20 : word) = Some W_17a20.
Proof. vm_refl. Qed.
Lemma D_17a20 : decode_any W_17a20 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a24 : bv 32 := 0xfffe8597.
Lemma F_17a24 : fetch_word Plain.M.loaded_segments (0x17a24 : word) = Some W_17a24.
Proof. vm_refl. Qed.
Lemma D_17a24 : decode_any W_17a24 = Some (Auipc 11 1048552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a28 : bv 32 := 0x5dc58593.
Lemma F_17a28 : fetch_word Plain.M.loaded_segments (0x17a28 : word) = Some W_17a28.
Proof. vm_refl. Qed.
Lemma D_17a28 : decode_any W_17a28 = Some (OpImm ALU_ADD 11 11 1500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a2c : bv 32 := 0xff017113.
Lemma F_17a2c : fetch_word Plain.M.loaded_segments (0x17a2c : word) = Some W_17a2c.
Proof. vm_refl. Qed.
Lemma D_17a2c : decode_any W_17a2c = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a30 : bv 32 := 0x0040006f.
Lemma F_17a30 : fetch_word Plain.M.loaded_segments (0x17a30 : word) = Some W_17a30.
Proof. vm_refl. Qed.
Lemma D_17a30 : decode_any W_17a30 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a34 : bv 32 := 0x00052583.
Lemma F_17a34 : fetch_word Plain.M.loaded_segments (0x17a34 : word) = Some W_17a34.
Proof. vm_refl. Qed.
Lemma D_17a34 : decode_any W_17a34 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a38 : bv 32 := 0x00019617.
Lemma F_17a38 : fetch_word Plain.M.loaded_segments (0x17a38 : word) = Some W_17a38.
Proof. vm_refl. Qed.
Lemma D_17a38 : decode_any W_17a38 = Some (Auipc 12 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a3c : bv 32 := 0x00019697.
Lemma F_17a3c : fetch_word Plain.M.loaded_segments (0x17a3c : word) = Some W_17a3c.
Proof. vm_refl. Qed.
Lemma D_17a3c : decode_any W_17a3c = Some (Auipc 13 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a40 : bv 32 := 0x00019717.
Lemma F_17a40 : fetch_word Plain.M.loaded_segments (0x17a40 : word) = Some W_17a40.
Proof. vm_refl. Qed.
Lemma D_17a40 : decode_any W_17a40 = Some (Auipc 14 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a44 : bv 32 := 0x96063783.
Lemma F_17a44 : fetch_word Plain.M.loaded_segments (0x17a44 : word) = Some W_17a44.
Proof. vm_refl. Qed.
Lemma D_17a44 : decode_any W_17a44 = Some (Load SZ8 true 15 12 2400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a48 : bv 32 := 0x9646b683.
Lemma F_17a48 : fetch_word Plain.M.loaded_segments (0x17a48 : word) = Some W_17a48.
Proof. vm_refl. Qed.
Lemma D_17a48 : decode_any W_17a48 = Some (Load SZ8 true 13 13 2404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a4c : bv 32 := 0x96873703.
Lemma F_17a4c : fetch_word Plain.M.loaded_segments (0x17a4c : word) = Some W_17a4c.
Proof. vm_refl. Qed.
Lemma D_17a4c : decode_any W_17a4c = Some (Load SZ8 true 14 14 2408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a50 : bv 32 := 0x00850613.
Lemma F_17a50 : fetch_word Plain.M.loaded_segments (0x17a50 : word) = Some W_17a50.
Proof. vm_refl. Qed.
Lemma D_17a50 : decode_any W_17a50 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a54 : bv 32 := 0x00078513.
Lemma F_17a54 : fetch_word Plain.M.loaded_segments (0x17a54 : word) = Some W_17a54.
Proof. vm_refl. Qed.
Lemma D_17a54 : decode_any W_17a54 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a58 : bv 32 := 0x00000793.
Lemma F_17a58 : fetch_word Plain.M.loaded_segments (0x17a58 : word) = Some W_17a58.
Proof. vm_refl. Qed.
Lemma D_17a58 : decode_any W_17a58 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a5c : bv 32 := 0x0dd0a06f.
Lemma F_17a5c : fetch_word Plain.M.loaded_segments (0x17a5c : word) = Some W_17a5c.
Proof. vm_refl. Qed.
Lemma D_17a5c : decode_any W_17a5c = Some (Jal 0 43228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a60 : bv 32 := 0xff010113.
Lemma F_17a60 : fetch_word Plain.M.loaded_segments (0x17a60 : word) = Some W_17a60.
Proof. vm_refl. Qed.
Lemma D_17a60 : decode_any W_17a60 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a64 : bv 32 := 0x00113423.
Lemma F_17a64 : fetch_word Plain.M.loaded_segments (0x17a64 : word) = Some W_17a64.
Proof. vm_refl. Qed.
Lemma D_17a64 : decode_any W_17a64 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a68 : bv 32 := 0x00813023.
Lemma F_17a68 : fetch_word Plain.M.loaded_segments (0x17a68 : word) = Some W_17a68.
Proof. vm_refl. Qed.
Lemma D_17a68 : decode_any W_17a68 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a6c : bv 32 := 0x01010413.
Lemma F_17a6c : fetch_word Plain.M.loaded_segments (0x17a6c : word) = Some W_17a6c.
Proof. vm_refl. Qed.
Lemma D_17a6c : decode_any W_17a6c = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a70 : bv 32 := 0x0001a517.
Lemma F_17a70 : fetch_word Plain.M.loaded_segments (0x17a70 : word) = Some W_17a70.
Proof. vm_refl. Qed.
Lemma D_17a70 : decode_any W_17a70 = Some (Auipc 10 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a74 : bv 32 := 0xd4050513.
Lemma F_17a74 : fetch_word Plain.M.loaded_segments (0x17a74 : word) = Some W_17a74.
Proof. vm_refl. Qed.
Lemma D_17a74 : decode_any W_17a74 = Some (OpImm ALU_ADD 10 10 3392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a78 : bv 32 := 0x00054503.
Lemma F_17a78 : fetch_word Plain.M.loaded_segments (0x17a78 : word) = Some W_17a78.
Proof. vm_refl. Qed.
Lemma D_17a78 : decode_any W_17a78 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a7c : bv 32 := 0x00157513.
Lemma F_17a7c : fetch_word Plain.M.loaded_segments (0x17a7c : word) = Some W_17a7c.
Proof. vm_refl. Qed.
Lemma D_17a7c : decode_any W_17a7c = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a80 : bv 32 := 0x00050663.
Lemma F_17a80 : fetch_word Plain.M.loaded_segments (0x17a80 : word) = Some W_17a80.
Proof. vm_refl. Qed.
Lemma D_17a80 : decode_any W_17a80 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a8c : bv 32 := 0x0001a517.
Lemma F_17a8c : fetch_word Plain.M.loaded_segments (0x17a8c : word) = Some W_17a8c.
Proof. vm_refl. Qed.
Lemma D_17a8c : decode_any W_17a8c = Some (Auipc 10 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a90 : bv 32 := 0xd2450593.
Lemma F_17a90 : fetch_word Plain.M.loaded_segments (0x17a90 : word) = Some W_17a90.
Proof. vm_refl. Qed.
Lemma D_17a90 : decode_any W_17a90 = Some (OpImm ALU_ADD 11 10 3364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a94 : bv 32 := 0x00100513.
Lemma F_17a94 : fetch_word Plain.M.loaded_segments (0x17a94 : word) = Some W_17a94.
Proof. vm_refl. Qed.
Lemma D_17a94 : decode_any W_17a94 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a98 : bv 32 := 0x00a58023.
Lemma F_17a98 : fetch_word Plain.M.loaded_segments (0x17a98 : word) = Some W_17a98.
Proof. vm_refl. Qed.
Lemma D_17a98 : decode_any W_17a98 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17a9c : bv 32 := 0x00019517.
Lemma F_17a9c : fetch_word Plain.M.loaded_segments (0x17a9c : word) = Some W_17a9c.
Proof. vm_refl. Qed.
Lemma D_17a9c : decode_any W_17a9c = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17aa0 : bv 32 := 0x91453503.
Lemma F_17aa0 : fetch_word Plain.M.loaded_segments (0x17aa0 : word) = Some W_17aa0.
Proof. vm_refl. Qed.
Lemma D_17aa0 : decode_any W_17aa0 = Some (Load SZ8 true 10 10 2324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17aa4 : bv 32 := 0x02050063.
Lemma F_17aa4 : fetch_word Plain.M.loaded_segments (0x17aa4 : word) = Some W_17aa4.
Proof. vm_refl. Qed.
Lemma D_17aa4 : decode_any W_17aa4 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ac4 : bv 32 := 0x00813083.
Lemma F_17ac4 : fetch_word Plain.M.loaded_segments (0x17ac4 : word) = Some W_17ac4.
Proof. vm_refl. Qed.
Lemma D_17ac4 : decode_any W_17ac4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ac8 : bv 32 := 0x00013403.
Lemma F_17ac8 : fetch_word Plain.M.loaded_segments (0x17ac8 : word) = Some W_17ac8.
Proof. vm_refl. Qed.
Lemma D_17ac8 : decode_any W_17ac8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17acc : bv 32 := 0x01010113.
Lemma F_17acc : fetch_word Plain.M.loaded_segments (0x17acc : word) = Some W_17acc.
Proof. vm_refl. Qed.
Lemma D_17acc : decode_any W_17acc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ad0 : bv 32 := 0x00008067.
Lemma F_17ad0 : fetch_word Plain.M.loaded_segments (0x17ad0 : word) = Some W_17ad0.
Proof. vm_refl. Qed.
Lemma D_17ad0 : decode_any W_17ad0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ad4 : bv 32 := 0xff010113.
Lemma F_17ad4 : fetch_word Plain.M.loaded_segments (0x17ad4 : word) = Some W_17ad4.
Proof. vm_refl. Qed.
Lemma D_17ad4 : decode_any W_17ad4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ad8 : bv 32 := 0x00113423.
Lemma F_17ad8 : fetch_word Plain.M.loaded_segments (0x17ad8 : word) = Some W_17ad8.
Proof. vm_refl. Qed.
Lemma D_17ad8 : decode_any W_17ad8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17adc : bv 32 := 0x00813023.
Lemma F_17adc : fetch_word Plain.M.loaded_segments (0x17adc : word) = Some W_17adc.
Proof. vm_refl. Qed.
Lemma D_17adc : decode_any W_17adc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ae0 : bv 32 := 0x01010413.
Lemma F_17ae0 : fetch_word Plain.M.loaded_segments (0x17ae0 : word) = Some W_17ae0.
Proof. vm_refl. Qed.
Lemma D_17ae0 : decode_any W_17ae0 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ae4 : bv 32 := 0x0001a517.
Lemma F_17ae4 : fetch_word Plain.M.loaded_segments (0x17ae4 : word) = Some W_17ae4.
Proof. vm_refl. Qed.
Lemma D_17ae4 : decode_any W_17ae4 = Some (Auipc 10 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ae8 : bv 32 := 0xd1450513.
Lemma F_17ae8 : fetch_word Plain.M.loaded_segments (0x17ae8 : word) = Some W_17ae8.
Proof. vm_refl. Qed.
Lemma D_17ae8 : decode_any W_17ae8 = Some (OpImm ALU_ADD 10 10 3348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17aec : bv 32 := 0x00054503.
Lemma F_17aec : fetch_word Plain.M.loaded_segments (0x17aec : word) = Some W_17aec.
Proof. vm_refl. Qed.
Lemma D_17aec : decode_any W_17aec = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17af0 : bv 32 := 0x00157513.
Lemma F_17af0 : fetch_word Plain.M.loaded_segments (0x17af0 : word) = Some W_17af0.
Proof. vm_refl. Qed.
Lemma D_17af0 : decode_any W_17af0 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17af4 : bv 32 := 0x00050663.
Lemma F_17af4 : fetch_word Plain.M.loaded_segments (0x17af4 : word) = Some W_17af4.
Proof. vm_refl. Qed.
Lemma D_17af4 : decode_any W_17af4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b00 : bv 32 := 0x0001a517.
Lemma F_17b00 : fetch_word Plain.M.loaded_segments (0x17b00 : word) = Some W_17b00.
Proof. vm_refl. Qed.
Lemma D_17b00 : decode_any W_17b00 = Some (Auipc 10 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b04 : bv 32 := 0xcf850593.
Lemma F_17b04 : fetch_word Plain.M.loaded_segments (0x17b04 : word) = Some W_17b04.
Proof. vm_refl. Qed.
Lemma D_17b04 : decode_any W_17b04 = Some (OpImm ALU_ADD 11 10 3320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b08 : bv 32 := 0x00100513.
Lemma F_17b08 : fetch_word Plain.M.loaded_segments (0x17b08 : word) = Some W_17b08.
Proof. vm_refl. Qed.
Lemma D_17b08 : decode_any W_17b08 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b0c : bv 32 := 0x00a58023.
Lemma F_17b0c : fetch_word Plain.M.loaded_segments (0x17b0c : word) = Some W_17b0c.
Proof. vm_refl. Qed.
Lemma D_17b0c : decode_any W_17b0c = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b10 : bv 32 := 0x00019517.
Lemma F_17b10 : fetch_word Plain.M.loaded_segments (0x17b10 : word) = Some W_17b10.
Proof. vm_refl. Qed.
Lemma D_17b10 : decode_any W_17b10 = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b14 : bv 32 := 0x8a853503.
Lemma F_17b14 : fetch_word Plain.M.loaded_segments (0x17b14 : word) = Some W_17b14.
Proof. vm_refl. Qed.
Lemma D_17b14 : decode_any W_17b14 = Some (Load SZ8 true 10 10 2216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b18 : bv 32 := 0x00050e63.
Lemma F_17b18 : fetch_word Plain.M.loaded_segments (0x17b18 : word) = Some W_17b18.
Proof. vm_refl. Qed.
Lemma D_17b18 : decode_any W_17b18 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b1c : bv 32 := 0x0040006f.
Lemma F_17b1c : fetch_word Plain.M.loaded_segments (0x17b1c : word) = Some W_17b1c.
Proof. vm_refl. Qed.
Lemma D_17b1c : decode_any W_17b1c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b20 : bv 32 := 0x0001a517.
Lemma F_17b20 : fetch_word Plain.M.loaded_segments (0x17b20 : word) = Some W_17b20.
Proof. vm_refl. Qed.
Lemma D_17b20 : decode_any W_17b20 = Some (Auipc 10 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b24 : bv 32 := 0x93850513.
Lemma F_17b24 : fetch_word Plain.M.loaded_segments (0x17b24 : word) = Some W_17b24.
Proof. vm_refl. Qed.
Lemma D_17b24 : decode_any W_17b24 = Some (OpImm ALU_ADD 10 10 2360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b28 : bv 32 := 0x00053503.
Lemma F_17b28 : fetch_word Plain.M.loaded_segments (0x17b28 : word) = Some W_17b28.
Proof. vm_refl. Qed.
Lemma D_17b28 : decode_any W_17b28 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b2c : bv 32 := 0x5550a0ef.
Lemma F_17b2c : fetch_word Plain.M.loaded_segments (0x17b2c : word) = Some W_17b2c.
Proof. vm_refl. Qed.
Lemma D_17b2c : decode_any W_17b2c = Some (Jal 1 44372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b30 : bv 32 := 0x0040006f.
Lemma F_17b30 : fetch_word Plain.M.loaded_segments (0x17b30 : word) = Some W_17b30.
Proof. vm_refl. Qed.
Lemma D_17b30 : decode_any W_17b30 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b34 : bv 32 := 0x00019517.
Lemma F_17b34 : fetch_word Plain.M.loaded_segments (0x17b34 : word) = Some W_17b34.
Proof. vm_refl. Qed.
Lemma D_17b34 : decode_any W_17b34 = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b38 : bv 32 := 0x88c53503.
Lemma F_17b38 : fetch_word Plain.M.loaded_segments (0x17b38 : word) = Some W_17b38.
Proof. vm_refl. Qed.
Lemma D_17b38 : decode_any W_17b38 = Some (Load SZ8 true 10 10 2188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b3c : bv 32 := 0x00050c63.
Lemma F_17b3c : fetch_word Plain.M.loaded_segments (0x17b3c : word) = Some W_17b3c.
Proof. vm_refl. Qed.
Lemma D_17b3c : decode_any W_17b3c = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b54 : bv 32 := 0x00813083.
Lemma F_17b54 : fetch_word Plain.M.loaded_segments (0x17b54 : word) = Some W_17b54.
Proof. vm_refl. Qed.
Lemma D_17b54 : decode_any W_17b54 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b58 : bv 32 := 0x00013403.
Lemma F_17b58 : fetch_word Plain.M.loaded_segments (0x17b58 : word) = Some W_17b58.
Proof. vm_refl. Qed.
Lemma D_17b58 : decode_any W_17b58 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b5c : bv 32 := 0x01010113.
Lemma F_17b5c : fetch_word Plain.M.loaded_segments (0x17b5c : word) = Some W_17b5c.
Proof. vm_refl. Qed.
Lemma D_17b5c : decode_any W_17b5c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17b60 : bv 32 := 0x00008067.
Lemma F_17b60 : fetch_word Plain.M.loaded_segments (0x17b60 : word) = Some W_17b60.
Proof. vm_refl. Qed.
Lemma D_17b60 : decode_any W_17b60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17eac : bv 32 := 0x00090493.
Lemma F_17eac : fetch_word Plain.M.loaded_segments (0x17eac : word) = Some W_17eac.
Proof. vm_refl. Qed.
Lemma D_17eac : decode_any W_17eac = Some (OpImm ALU_ADD 9 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17eb0 : bv 32 := 0x0340006f.
Lemma F_17eb0 : fetch_word Plain.M.loaded_segments (0x17eb0 : word) = Some W_17eb0.
Proof. vm_refl. Qed.
Lemma D_17eb0 : decode_any W_17eb0 = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ee4 : bv 32 := 0x00000b13.
Lemma F_17ee4 : fetch_word Plain.M.loaded_segments (0x17ee4 : word) = Some W_17ee4.
Proof. vm_refl. Qed.
Lemma D_17ee4 : decode_any W_17ee4 = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ee8 : bv 32 := 0xffe00b93.
Lemma F_17ee8 : fetch_word Plain.M.loaded_segments (0x17ee8 : word) = Some W_17ee8.
Proof. vm_refl. Qed.
Lemma D_17ee8 : decode_any W_17ee8 = Some (OpImm ALU_ADD 23 0 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17eec : bv 32 := 0x00100513.
Lemma F_17eec : fetch_word Plain.M.loaded_segments (0x17eec : word) = Some W_17eec.
Proof. vm_refl. Qed.
Lemma D_17eec : decode_any W_17eec = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ef0 : bv 32 := 0x00aa0223.
Lemma F_17ef0 : fetch_word Plain.M.loaded_segments (0x17ef0 : word) = Some W_17ef0.
Proof. vm_refl. Qed.
Lemma D_17ef0 : decode_any W_17ef0 = Some (Store SZ1 20 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ef4 : bv 32 := 0x00048513.
Lemma F_17ef4 : fetch_word Plain.M.loaded_segments (0x17ef4 : word) = Some W_17ef4.
Proof. vm_refl. Qed.
Lemma D_17ef4 : decode_any W_17ef4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17ef8 : bv 32 := 0x00040593.
Lemma F_17ef8 : fetch_word Plain.M.loaded_segments (0x17ef8 : word) = Some W_17ef8.
Proof. vm_refl. Qed.
Lemma D_17ef8 : decode_any W_17ef8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17efc : bv 32 := 0x14c000ef.
Lemma F_17efc : fetch_word Plain.M.loaded_segments (0x17efc : word) = Some W_17efc.
Proof. vm_refl. Qed.
Lemma D_17efc : decode_any W_17efc = Some (Jal 1 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f00 : bv 32 := 0x00050993.
Lemma F_17f00 : fetch_word Plain.M.loaded_segments (0x17f00 : word) = Some W_17f00.
Proof. vm_refl. Qed.
Lemma D_17f00 : decode_any W_17f00 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f04 : bv 32 := 0x000a0223.
Lemma F_17f04 : fetch_word Plain.M.loaded_segments (0x17f04 : word) = Some W_17f04.
Proof. vm_refl. Qed.
Lemma D_17f04 : decode_any W_17f04 = Some (Store SZ1 20 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f08 : bv 32 := 0x00050593.
Lemma F_17f08 : fetch_word Plain.M.loaded_segments (0x17f08 : word) = Some W_17f08.
Proof. vm_refl. Qed.
Lemma D_17f08 : decode_any W_17f08 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f0c : bv 32 := 0x0b0000ef.
Lemma F_17f0c : fetch_word Plain.M.loaded_segments (0x17f0c : word) = Some W_17f0c.
Proof. vm_refl. Qed.
Lemma D_17f0c : decode_any W_17f0c = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f10 : bv 32 := 0xfff9899b.
Lemma F_17f10 : fetch_word Plain.M.loaded_segments (0x17f10 : word) = Some W_17f10.
Proof. vm_refl. Qed.
Lemma D_17f10 : decode_any W_17f10 = Some (OpImm32 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f14 : bv 32 := 0x0179f463.
Lemma F_17f14 : fetch_word Plain.M.loaded_segments (0x17f14 : word) = Some W_17f14.
Proof. vm_refl. Qed.
Lemma D_17f14 : decode_any W_17f14 = Some (Branch BC_GEU 19 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f1c : bv 32 := 0xfffa8a9b.
Lemma F_17f1c : fetch_word Plain.M.loaded_segments (0x17f1c : word) = Some W_17f1c.
Proof. vm_refl. Qed.
Lemma D_17f1c : decode_any W_17f1c = Some (OpImm32 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f20 : bv 32 := 0xfc0a96e3.
Lemma F_17f20 : fetch_word Plain.M.loaded_segments (0x17f20 : word) = Some W_17f20.
Proof. vm_refl. Qed.
Lemma D_17f20 : decode_any W_17f20 = Some (Branch BC_NE 21 0 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f8c : bv 32 := 0x0002a517.
Lemma F_17f8c : fetch_word Plain.M.loaded_segments (0x17f8c : word) = Some W_17f8c.
Proof. vm_refl. Qed.
Lemma D_17f8c : decode_any W_17f8c = Some (Auipc 10 42, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f90 : bv 32 := 0x87854503.
Lemma F_17f90 : fetch_word Plain.M.loaded_segments (0x17f90 : word) = Some W_17f90.
Proof. vm_refl. Qed.
Lemma D_17f90 : decode_any W_17f90 = Some (Load SZ1 false 10 10 2168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f94 : bv 32 := 0x00051463.
Lemma F_17f94 : fetch_word Plain.M.loaded_segments (0x17f94 : word) = Some W_17f94.
Proof. vm_refl. Qed.
Lemma D_17f94 : decode_any W_17f94 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_17f98 : bv 32 := 0x00008067.
Lemma F_17f98 : fetch_word Plain.M.loaded_segments (0x17f98 : word) = Some W_17f98.
Proof. vm_refl. Qed.
Lemma D_17f98 : decode_any W_17f98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
