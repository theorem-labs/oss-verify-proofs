(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_729a8 : bv 32 := 0x00155593.
Lemma F_729a8 : fetch_word Asan.M.loaded_segments (0x729a8 : word) = Some W_729a8.
Proof. vm_refl. Qed.
Lemma D_729a8 : decode_any W_729a8 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729ac : bv 32 := 0x55555637.
Lemma F_729ac : fetch_word Asan.M.loaded_segments (0x729ac : word) = Some W_729ac.
Proof. vm_refl. Qed.
Lemma D_729ac : decode_any W_729ac = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729b0 : bv 32 := 0x333336b7.
Lemma F_729b0 : fetch_word Asan.M.loaded_segments (0x729b0 : word) = Some W_729b0.
Proof. vm_refl. Qed.
Lemma D_729b0 : decode_any W_729b0 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729b4 : bv 32 := 0x0f0f1737.
Lemma F_729b4 : fetch_word Asan.M.loaded_segments (0x729b4 : word) = Some W_729b4.
Proof. vm_refl. Qed.
Lemma D_729b4 : decode_any W_729b4 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729b8 : bv 32 := 0x010107b7.
Lemma F_729b8 : fetch_word Asan.M.loaded_segments (0x729b8 : word) = Some W_729b8.
Proof. vm_refl. Qed.
Lemma D_729b8 : decode_any W_729b8 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729bc : bv 32 := 0x00b56533.
Lemma F_729bc : fetch_word Asan.M.loaded_segments (0x729bc : word) = Some W_729bc.
Proof. vm_refl. Qed.
Lemma D_729bc : decode_any W_729bc = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729c0 : bv 32 := 0x5556059b.
Lemma F_729c0 : fetch_word Asan.M.loaded_segments (0x729c0 : word) = Some W_729c0.
Proof. vm_refl. Qed.
Lemma D_729c0 : decode_any W_729c0 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729c4 : bv 32 := 0x3336861b.
Lemma F_729c4 : fetch_word Asan.M.loaded_segments (0x729c4 : word) = Some W_729c4.
Proof. vm_refl. Qed.
Lemma D_729c4 : decode_any W_729c4 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729c8 : bv 32 := 0xf0f7069b.
Lemma F_729c8 : fetch_word Asan.M.loaded_segments (0x729c8 : word) = Some W_729c8.
Proof. vm_refl. Qed.
Lemma D_729c8 : decode_any W_729c8 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729cc : bv 32 := 0x1017871b.
Lemma F_729cc : fetch_word Asan.M.loaded_segments (0x729cc : word) = Some W_729cc.
Proof. vm_refl. Qed.
Lemma D_729cc : decode_any W_729cc = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729d0 : bv 32 := 0x00255793.
Lemma F_729d0 : fetch_word Asan.M.loaded_segments (0x729d0 : word) = Some W_729d0.
Proof. vm_refl. Qed.
Lemma D_729d0 : decode_any W_729d0 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729d4 : bv 32 := 0x00f56533.
Lemma F_729d4 : fetch_word Asan.M.loaded_segments (0x729d4 : word) = Some W_729d4.
Proof. vm_refl. Qed.
Lemma D_729d4 : decode_any W_729d4 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729d8 : bv 32 := 0x02059793.
Lemma F_729d8 : fetch_word Asan.M.loaded_segments (0x729d8 : word) = Some W_729d8.
Proof. vm_refl. Qed.
Lemma D_729d8 : decode_any W_729d8 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729dc : bv 32 := 0x00f585b3.
Lemma F_729dc : fetch_word Asan.M.loaded_segments (0x729dc : word) = Some W_729dc.
Proof. vm_refl. Qed.
Lemma D_729dc : decode_any W_729dc = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729e0 : bv 32 := 0x02061793.
Lemma F_729e0 : fetch_word Asan.M.loaded_segments (0x729e0 : word) = Some W_729e0.
Proof. vm_refl. Qed.
Lemma D_729e0 : decode_any W_729e0 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729e4 : bv 32 := 0x00f60633.
Lemma F_729e4 : fetch_word Asan.M.loaded_segments (0x729e4 : word) = Some W_729e4.
Proof. vm_refl. Qed.
Lemma D_729e4 : decode_any W_729e4 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729e8 : bv 32 := 0x02069793.
Lemma F_729e8 : fetch_word Asan.M.loaded_segments (0x729e8 : word) = Some W_729e8.
Proof. vm_refl. Qed.
Lemma D_729e8 : decode_any W_729e8 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729ec : bv 32 := 0x00f686b3.
Lemma F_729ec : fetch_word Asan.M.loaded_segments (0x729ec : word) = Some W_729ec.
Proof. vm_refl. Qed.
Lemma D_729ec : decode_any W_729ec = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729f0 : bv 32 := 0x02071793.
Lemma F_729f0 : fetch_word Asan.M.loaded_segments (0x729f0 : word) = Some W_729f0.
Proof. vm_refl. Qed.
Lemma D_729f0 : decode_any W_729f0 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729f4 : bv 32 := 0x00f70733.
Lemma F_729f4 : fetch_word Asan.M.loaded_segments (0x729f4 : word) = Some W_729f4.
Proof. vm_refl. Qed.
Lemma D_729f4 : decode_any W_729f4 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729f8 : bv 32 := 0x00455793.
Lemma F_729f8 : fetch_word Asan.M.loaded_segments (0x729f8 : word) = Some W_729f8.
Proof. vm_refl. Qed.
Lemma D_729f8 : decode_any W_729f8 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_729fc : bv 32 := 0x00f56533.
Lemma F_729fc : fetch_word Asan.M.loaded_segments (0x729fc : word) = Some W_729fc.
Proof. vm_refl. Qed.
Lemma D_729fc : decode_any W_729fc = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a00 : bv 32 := 0x00855793.
Lemma F_72a00 : fetch_word Asan.M.loaded_segments (0x72a00 : word) = Some W_72a00.
Proof. vm_refl. Qed.
Lemma D_72a00 : decode_any W_72a00 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a04 : bv 32 := 0x00f56533.
Lemma F_72a04 : fetch_word Asan.M.loaded_segments (0x72a04 : word) = Some W_72a04.
Proof. vm_refl. Qed.
Lemma D_72a04 : decode_any W_72a04 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a08 : bv 32 := 0x01055793.
Lemma F_72a08 : fetch_word Asan.M.loaded_segments (0x72a08 : word) = Some W_72a08.
Proof. vm_refl. Qed.
Lemma D_72a08 : decode_any W_72a08 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a0c : bv 32 := 0x00f56533.
Lemma F_72a0c : fetch_word Asan.M.loaded_segments (0x72a0c : word) = Some W_72a0c.
Proof. vm_refl. Qed.
Lemma D_72a0c : decode_any W_72a0c = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a10 : bv 32 := 0x02055793.
Lemma F_72a10 : fetch_word Asan.M.loaded_segments (0x72a10 : word) = Some W_72a10.
Proof. vm_refl. Qed.
Lemma D_72a10 : decode_any W_72a10 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a14 : bv 32 := 0x00f56533.
Lemma F_72a14 : fetch_word Asan.M.loaded_segments (0x72a14 : word) = Some W_72a14.
Proof. vm_refl. Qed.
Lemma D_72a14 : decode_any W_72a14 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a18 : bv 32 := 0xfff54513.
Lemma F_72a18 : fetch_word Asan.M.loaded_segments (0x72a18 : word) = Some W_72a18.
Proof. vm_refl. Qed.
Lemma D_72a18 : decode_any W_72a18 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a1c : bv 32 := 0x00155793.
Lemma F_72a1c : fetch_word Asan.M.loaded_segments (0x72a1c : word) = Some W_72a1c.
Proof. vm_refl. Qed.
Lemma D_72a1c : decode_any W_72a1c = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a20 : bv 32 := 0x00b7f5b3.
Lemma F_72a20 : fetch_word Asan.M.loaded_segments (0x72a20 : word) = Some W_72a20.
Proof. vm_refl. Qed.
Lemma D_72a20 : decode_any W_72a20 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a24 : bv 32 := 0x40b50533.
Lemma F_72a24 : fetch_word Asan.M.loaded_segments (0x72a24 : word) = Some W_72a24.
Proof. vm_refl. Qed.
Lemma D_72a24 : decode_any W_72a24 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a28 : bv 32 := 0x00c575b3.
Lemma F_72a28 : fetch_word Asan.M.loaded_segments (0x72a28 : word) = Some W_72a28.
Proof. vm_refl. Qed.
Lemma D_72a28 : decode_any W_72a28 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a2c : bv 32 := 0x00255513.
Lemma F_72a2c : fetch_word Asan.M.loaded_segments (0x72a2c : word) = Some W_72a2c.
Proof. vm_refl. Qed.
Lemma D_72a2c : decode_any W_72a2c = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a30 : bv 32 := 0x00c57533.
Lemma F_72a30 : fetch_word Asan.M.loaded_segments (0x72a30 : word) = Some W_72a30.
Proof. vm_refl. Qed.
Lemma D_72a30 : decode_any W_72a30 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a34 : bv 32 := 0x00a58533.
Lemma F_72a34 : fetch_word Asan.M.loaded_segments (0x72a34 : word) = Some W_72a34.
Proof. vm_refl. Qed.
Lemma D_72a34 : decode_any W_72a34 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a38 : bv 32 := 0x00455593.
Lemma F_72a38 : fetch_word Asan.M.loaded_segments (0x72a38 : word) = Some W_72a38.
Proof. vm_refl. Qed.
Lemma D_72a38 : decode_any W_72a38 = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a3c : bv 32 := 0x00b50533.
Lemma F_72a3c : fetch_word Asan.M.loaded_segments (0x72a3c : word) = Some W_72a3c.
Proof. vm_refl. Qed.
Lemma D_72a3c : decode_any W_72a3c = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a40 : bv 32 := 0x00d57533.
Lemma F_72a40 : fetch_word Asan.M.loaded_segments (0x72a40 : word) = Some W_72a40.
Proof. vm_refl. Qed.
Lemma D_72a40 : decode_any W_72a40 = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a44 : bv 32 := 0x02e50533.
Lemma F_72a44 : fetch_word Asan.M.loaded_segments (0x72a44 : word) = Some W_72a44.
Proof. vm_refl. Qed.
Lemma D_72a44 : decode_any W_72a44 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a48 : bv 32 := 0x03855513.
Lemma F_72a48 : fetch_word Asan.M.loaded_segments (0x72a48 : word) = Some W_72a48.
Proof. vm_refl. Qed.
Lemma D_72a48 : decode_any W_72a48 = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a4c : bv 32 := 0x40a0053b.
Lemma F_72a4c : fetch_word Asan.M.loaded_segments (0x72a4c : word) = Some W_72a4c.
Proof. vm_refl. Qed.
Lemma D_72a4c : decode_any W_72a4c = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a50 : bv 32 := 0xfff00593.
Lemma F_72a50 : fetch_word Asan.M.loaded_segments (0x72a50 : word) = Some W_72a50.
Proof. vm_refl. Qed.
Lemma D_72a50 : decode_any W_72a50 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a54 : bv 32 := 0x00a59533.
Lemma F_72a54 : fetch_word Asan.M.loaded_segments (0x72a54 : word) = Some W_72a54.
Proof. vm_refl. Qed.
Lemma D_72a54 : decode_any W_72a54 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_72a58 : bv 32 := 0xfff54513.
Lemma F_72a58 : fetch_word Asan.M.loaded_segments (0x72a58 : word) = Some W_72a58.
Proof. vm_refl. Qed.
Lemma D_72a58 : decode_any W_72a58 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.
