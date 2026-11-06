(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_66a14 : bv 32 := 0x00155593.
Lemma F_66a14 : fetch_word AsanUbsan.M.loaded_segments (0x66870 : word) = Some W_66a14.
Proof. vm_refl. Qed.
Lemma D_66a14 : decode_any W_66a14 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a18 : bv 32 := 0x55555637.
Lemma F_66a18 : fetch_word AsanUbsan.M.loaded_segments (0x66874 : word) = Some W_66a18.
Proof. vm_refl. Qed.
Lemma D_66a18 : decode_any W_66a18 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a1c : bv 32 := 0x333336b7.
Lemma F_66a1c : fetch_word AsanUbsan.M.loaded_segments (0x66878 : word) = Some W_66a1c.
Proof. vm_refl. Qed.
Lemma D_66a1c : decode_any W_66a1c = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a20 : bv 32 := 0x0f0f1737.
Lemma F_66a20 : fetch_word AsanUbsan.M.loaded_segments (0x6687c : word) = Some W_66a20.
Proof. vm_refl. Qed.
Lemma D_66a20 : decode_any W_66a20 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a24 : bv 32 := 0x010107b7.
Lemma F_66a24 : fetch_word AsanUbsan.M.loaded_segments (0x66880 : word) = Some W_66a24.
Proof. vm_refl. Qed.
Lemma D_66a24 : decode_any W_66a24 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a28 : bv 32 := 0x00b56533.
Lemma F_66a28 : fetch_word AsanUbsan.M.loaded_segments (0x66884 : word) = Some W_66a28.
Proof. vm_refl. Qed.
Lemma D_66a28 : decode_any W_66a28 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a2c : bv 32 := 0x5556059b.
Lemma F_66a2c : fetch_word AsanUbsan.M.loaded_segments (0x66888 : word) = Some W_66a2c.
Proof. vm_refl. Qed.
Lemma D_66a2c : decode_any W_66a2c = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a30 : bv 32 := 0x3336861b.
Lemma F_66a30 : fetch_word AsanUbsan.M.loaded_segments (0x6688c : word) = Some W_66a30.
Proof. vm_refl. Qed.
Lemma D_66a30 : decode_any W_66a30 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a34 : bv 32 := 0xf0f7069b.
Lemma F_66a34 : fetch_word AsanUbsan.M.loaded_segments (0x66890 : word) = Some W_66a34.
Proof. vm_refl. Qed.
Lemma D_66a34 : decode_any W_66a34 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a38 : bv 32 := 0x1017871b.
Lemma F_66a38 : fetch_word AsanUbsan.M.loaded_segments (0x66894 : word) = Some W_66a38.
Proof. vm_refl. Qed.
Lemma D_66a38 : decode_any W_66a38 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a3c : bv 32 := 0x00255793.
Lemma F_66a3c : fetch_word AsanUbsan.M.loaded_segments (0x66898 : word) = Some W_66a3c.
Proof. vm_refl. Qed.
Lemma D_66a3c : decode_any W_66a3c = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a40 : bv 32 := 0x00f56533.
Lemma F_66a40 : fetch_word AsanUbsan.M.loaded_segments (0x6689c : word) = Some W_66a40.
Proof. vm_refl. Qed.
Lemma D_66a40 : decode_any W_66a40 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a44 : bv 32 := 0x02059793.
Lemma F_66a44 : fetch_word AsanUbsan.M.loaded_segments (0x668a0 : word) = Some W_66a44.
Proof. vm_refl. Qed.
Lemma D_66a44 : decode_any W_66a44 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a48 : bv 32 := 0x00f585b3.
Lemma F_66a48 : fetch_word AsanUbsan.M.loaded_segments (0x668a4 : word) = Some W_66a48.
Proof. vm_refl. Qed.
Lemma D_66a48 : decode_any W_66a48 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a4c : bv 32 := 0x02061793.
Lemma F_66a4c : fetch_word AsanUbsan.M.loaded_segments (0x668a8 : word) = Some W_66a4c.
Proof. vm_refl. Qed.
Lemma D_66a4c : decode_any W_66a4c = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a50 : bv 32 := 0x00f60633.
Lemma F_66a50 : fetch_word AsanUbsan.M.loaded_segments (0x668ac : word) = Some W_66a50.
Proof. vm_refl. Qed.
Lemma D_66a50 : decode_any W_66a50 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a54 : bv 32 := 0x02069793.
Lemma F_66a54 : fetch_word AsanUbsan.M.loaded_segments (0x668b0 : word) = Some W_66a54.
Proof. vm_refl. Qed.
Lemma D_66a54 : decode_any W_66a54 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a58 : bv 32 := 0x00f686b3.
Lemma F_66a58 : fetch_word AsanUbsan.M.loaded_segments (0x668b4 : word) = Some W_66a58.
Proof. vm_refl. Qed.
Lemma D_66a58 : decode_any W_66a58 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a5c : bv 32 := 0x02071793.
Lemma F_66a5c : fetch_word AsanUbsan.M.loaded_segments (0x668b8 : word) = Some W_66a5c.
Proof. vm_refl. Qed.
Lemma D_66a5c : decode_any W_66a5c = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a60 : bv 32 := 0x00f70733.
Lemma F_66a60 : fetch_word AsanUbsan.M.loaded_segments (0x668bc : word) = Some W_66a60.
Proof. vm_refl. Qed.
Lemma D_66a60 : decode_any W_66a60 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a64 : bv 32 := 0x00455793.
Lemma F_66a64 : fetch_word AsanUbsan.M.loaded_segments (0x668c0 : word) = Some W_66a64.
Proof. vm_refl. Qed.
Lemma D_66a64 : decode_any W_66a64 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a68 : bv 32 := 0x00f56533.
Lemma F_66a68 : fetch_word AsanUbsan.M.loaded_segments (0x668c4 : word) = Some W_66a68.
Proof. vm_refl. Qed.
Lemma D_66a68 : decode_any W_66a68 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a6c : bv 32 := 0x00855793.
Lemma F_66a6c : fetch_word AsanUbsan.M.loaded_segments (0x668c8 : word) = Some W_66a6c.
Proof. vm_refl. Qed.
Lemma D_66a6c : decode_any W_66a6c = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a70 : bv 32 := 0x00f56533.
Lemma F_66a70 : fetch_word AsanUbsan.M.loaded_segments (0x668cc : word) = Some W_66a70.
Proof. vm_refl. Qed.
Lemma D_66a70 : decode_any W_66a70 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a74 : bv 32 := 0x01055793.
Lemma F_66a74 : fetch_word AsanUbsan.M.loaded_segments (0x668d0 : word) = Some W_66a74.
Proof. vm_refl. Qed.
Lemma D_66a74 : decode_any W_66a74 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a78 : bv 32 := 0x00f56533.
Lemma F_66a78 : fetch_word AsanUbsan.M.loaded_segments (0x668d4 : word) = Some W_66a78.
Proof. vm_refl. Qed.
Lemma D_66a78 : decode_any W_66a78 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a7c : bv 32 := 0x02055793.
Lemma F_66a7c : fetch_word AsanUbsan.M.loaded_segments (0x668d8 : word) = Some W_66a7c.
Proof. vm_refl. Qed.
Lemma D_66a7c : decode_any W_66a7c = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a80 : bv 32 := 0x00f56533.
Lemma F_66a80 : fetch_word AsanUbsan.M.loaded_segments (0x668dc : word) = Some W_66a80.
Proof. vm_refl. Qed.
Lemma D_66a80 : decode_any W_66a80 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a84 : bv 32 := 0xfff54513.
Lemma F_66a84 : fetch_word AsanUbsan.M.loaded_segments (0x668e0 : word) = Some W_66a84.
Proof. vm_refl. Qed.
Lemma D_66a84 : decode_any W_66a84 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.
