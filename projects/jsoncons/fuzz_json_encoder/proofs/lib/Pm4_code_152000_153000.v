(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_152960 : bv 32 := 0x0ff5f593.
Lemma F_152960 : fetch_word Asan.M.loaded_segments (0x1529a4 : word) = Some W_152960.
Proof. vm_refl. Qed.
Lemma D_152960 : decode_any W_152960 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152964 : bv 32 := 0x00757693.
Lemma F_152964 : fetch_word Asan.M.loaded_segments (0x1529a8 : word) = Some W_152964.
Proof. vm_refl. Qed.
Lemma D_152964 : decode_any W_152964 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152968 : bv 32 := 0x00c03733.
Lemma F_152968 : fetch_word Asan.M.loaded_segments (0x1529ac : word) = Some W_152968.
Proof. vm_refl. Qed.
Lemma D_152968 : decode_any W_152968 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15296c : bv 32 := 0x02068c63.
Lemma F_15296c : fetch_word Asan.M.loaded_segments (0x1529b0 : word) = Some W_15296c.
Proof. vm_refl. Qed.
Lemma D_15296c : decode_any W_15296c = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152970 : bv 32 := 0x02060a63.
Lemma F_152970 : fetch_word Asan.M.loaded_segments (0x1529b4 : word) = Some W_152970.
Proof. vm_refl. Qed.
Lemma D_152970 : decode_any W_152970 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152974 : bv 32 := 0x00150793.
Lemma F_152974 : fetch_word Asan.M.loaded_segments (0x1529b8 : word) = Some W_152974.
Proof. vm_refl. Qed.
Lemma D_152974 : decode_any W_152974 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152978 : bv 32 := 0x00100813.
Lemma F_152978 : fetch_word Asan.M.loaded_segments (0x1529bc : word) = Some W_152978.
Proof. vm_refl. Qed.
Lemma D_152978 : decode_any W_152978 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15297c : bv 32 := 0x00054703.
Lemma F_15297c : fetch_word Asan.M.loaded_segments (0x1529c0 : word) = Some W_15297c.
Proof. vm_refl. Qed.
Lemma D_15297c : decode_any W_15297c = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152980 : bv 32 := 0x00060693.
Lemma F_152980 : fetch_word Asan.M.loaded_segments (0x1529c4 : word) = Some W_152980.
Proof. vm_refl. Qed.
Lemma D_152980 : decode_any W_152980 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152984 : bv 32 := 0x06b70e63.
Lemma F_152984 : fetch_word Asan.M.loaded_segments (0x1529c8 : word) = Some W_152984.
Proof. vm_refl. Qed.
Lemma D_152984 : decode_any W_152984 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152988 : bv 32 := 0x00150513.
Lemma F_152988 : fetch_word Asan.M.loaded_segments (0x1529cc : word) = Some W_152988.
Proof. vm_refl. Qed.
Lemma D_152988 : decode_any W_152988 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15298c : bv 32 := 0xfff68613.
Lemma F_15298c : fetch_word Asan.M.loaded_segments (0x1529d0 : word) = Some W_15298c.
Proof. vm_refl. Qed.
Lemma D_15298c : decode_any W_15298c = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152990 : bv 32 := 0x0077f893.
Lemma F_152990 : fetch_word Asan.M.loaded_segments (0x1529d4 : word) = Some W_152990.
Proof. vm_refl. Qed.
Lemma D_152990 : decode_any W_152990 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152994 : bv 32 := 0x00c03733.
Lemma F_152994 : fetch_word Asan.M.loaded_segments (0x1529d8 : word) = Some W_152994.
Proof. vm_refl. Qed.
Lemma D_152994 : decode_any W_152994 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152998 : bv 32 := 0x00088663.
Lemma F_152998 : fetch_word Asan.M.loaded_segments (0x1529dc : word) = Some W_152998.
Proof. vm_refl. Qed.
Lemma D_152998 : decode_any W_152998 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15299c : bv 32 := 0x00178793.
Lemma F_15299c : fetch_word Asan.M.loaded_segments (0x1529e0 : word) = Some W_15299c.
Proof. vm_refl. Qed.
Lemma D_15299c : decode_any W_15299c = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529a0 : bv 32 := 0xfd069ee3.
Lemma F_1529a0 : fetch_word Asan.M.loaded_segments (0x1529e4 : word) = Some W_1529a0.
Proof. vm_refl. Qed.
Lemma D_1529a0 : decode_any W_1529a0 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529a4 : bv 32 := 0x06070863.
Lemma F_1529a4 : fetch_word Asan.M.loaded_segments (0x1529e8 : word) = Some W_1529a4.
Proof. vm_refl. Qed.
Lemma D_1529a4 : decode_any W_1529a4 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529a8 : bv 32 := 0x00054683.
Lemma F_1529a8 : fetch_word Asan.M.loaded_segments (0x1529ec : word) = Some W_1529a8.
Proof. vm_refl. Qed.
Lemma D_1529a8 : decode_any W_1529a8 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529ac : bv 32 := 0x04b68663.
Lemma F_1529ac : fetch_word Asan.M.loaded_segments (0x1529f0 : word) = Some W_1529ac.
Proof. vm_refl. Qed.
Lemma D_1529ac : decode_any W_1529ac = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529b0 : bv 32 := 0x00800693.
Lemma F_1529b0 : fetch_word Asan.M.loaded_segments (0x1529f4 : word) = Some W_1529b0.
Proof. vm_refl. Qed.
Lemma D_1529b0 : decode_any W_1529b0 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529b4 : bv 32 := 0x04d66263.
Lemma F_1529b4 : fetch_word Asan.M.loaded_segments (0x1529f8 : word) = Some W_1529b4.
Proof. vm_refl. Qed.
Lemma D_1529b4 : decode_any W_1529b4 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529b8 : bv 32 := 0xffebe697.
Lemma F_1529b8 : fetch_word Asan.M.loaded_segments (0x1529fc : word) = Some W_1529b8.
Proof. vm_refl. Qed.
Lemma D_1529b8 : decode_any W_1529b8 = Some (Auipc 13 1048254, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529bc : bv 32 := 0x9dc6b683.
Lemma F_1529bc : fetch_word Asan.M.loaded_segments (0x152a00 : word) = Some W_1529bc.
Proof. vm_refl. Qed.
Lemma D_1529bc : decode_any W_1529bc = Some (Load SZ8 true 13 13 2524, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529c0 : bv 32 := 0xffebe717.
Lemma F_1529c0 : fetch_word Asan.M.loaded_segments (0x152a04 : word) = Some W_1529c0.
Proof. vm_refl. Qed.
Lemma D_1529c0 : decode_any W_1529c0 = Some (Auipc 14 1048254, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529c4 : bv 32 := 0x9bc73703.
Lemma F_1529c4 : fetch_word Asan.M.loaded_segments (0x152a08 : word) = Some W_1529c4.
Proof. vm_refl. Qed.
Lemma D_1529c4 : decode_any W_1529c4 = Some (Load SZ8 true 14 14 2492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529c8 : bv 32 := 0x00168793.
Lemma F_1529c8 : fetch_word Asan.M.loaded_segments (0x152a0c : word) = Some W_1529c8.
Proof. vm_refl. Qed.
Lemma D_1529c8 : decode_any W_1529c8 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529cc : bv 32 := 0x02f587b3.
Lemma F_1529cc : fetch_word Asan.M.loaded_segments (0x152a10 : word) = Some W_1529cc.
Proof. vm_refl. Qed.
Lemma D_1529cc : decode_any W_1529cc = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529d0 : bv 32 := 0x00700813.
Lemma F_1529d0 : fetch_word Asan.M.loaded_segments (0x152a14 : word) = Some W_1529d0.
Proof. vm_refl. Qed.
Lemma D_1529d0 : decode_any W_1529d0 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529d4 : bv 32 := 0x00053883.
Lemma F_1529d4 : fetch_word Asan.M.loaded_segments (0x152a18 : word) = Some W_1529d4.
Proof. vm_refl. Qed.
Lemma D_1529d4 : decode_any W_1529d4 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529d8 : bv 32 := 0x00f8c8b3.
Lemma F_1529d8 : fetch_word Asan.M.loaded_segments (0x152a1c : word) = Some W_1529d8.
Proof. vm_refl. Qed.
Lemma D_1529d8 : decode_any W_1529d8 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529dc : bv 32 := 0x411682b3.
Lemma F_1529dc : fetch_word Asan.M.loaded_segments (0x152a20 : word) = Some W_1529dc.
Proof. vm_refl. Qed.
Lemma D_1529dc : decode_any W_1529dc = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529e0 : bv 32 := 0x0112e8b3.
Lemma F_1529e0 : fetch_word Asan.M.loaded_segments (0x152a24 : word) = Some W_1529e0.
Proof. vm_refl. Qed.
Lemma D_1529e0 : decode_any W_1529e0 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529e4 : bv 32 := 0x00e8f8b3.
Lemma F_1529e4 : fetch_word Asan.M.loaded_segments (0x152a28 : word) = Some W_1529e4.
Proof. vm_refl. Qed.
Lemma D_1529e4 : decode_any W_1529e4 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529e8 : bv 32 := 0x02e89a63.
Lemma F_1529e8 : fetch_word Asan.M.loaded_segments (0x152a2c : word) = Some W_1529e8.
Proof. vm_refl. Qed.
Lemma D_1529e8 : decode_any W_1529e8 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529ec : bv 32 := 0xff860613.
Lemma F_1529ec : fetch_word Asan.M.loaded_segments (0x152a30 : word) = Some W_1529ec.
Proof. vm_refl. Qed.
Lemma D_1529ec : decode_any W_1529ec = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529f0 : bv 32 := 0x00850513.
Lemma F_1529f0 : fetch_word Asan.M.loaded_segments (0x152a34 : word) = Some W_1529f0.
Proof. vm_refl. Qed.
Lemma D_1529f0 : decode_any W_1529f0 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529f4 : bv 32 := 0xfec860e3.
Lemma F_1529f4 : fetch_word Asan.M.loaded_segments (0x152a38 : word) = Some W_1529f4.
Proof. vm_refl. Qed.
Lemma D_1529f4 : decode_any W_1529f4 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529f8 : bv 32 := 0x00060693.
Lemma F_1529f8 : fetch_word Asan.M.loaded_segments (0x152a3c : word) = Some W_1529f8.
Proof. vm_refl. Qed.
Lemma D_1529f8 : decode_any W_1529f8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1529fc : bv 32 := 0x00060c63.
Lemma F_1529fc : fetch_word Asan.M.loaded_segments (0x152a40 : word) = Some W_1529fc.
Proof. vm_refl. Qed.
Lemma D_1529fc : decode_any W_1529fc = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a00 : bv 32 := 0x00054603.
Lemma F_152a00 : fetch_word Asan.M.loaded_segments (0x152a44 : word) = Some W_152a00.
Proof. vm_refl. Qed.
Lemma D_152a00 : decode_any W_152a00 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a04 : bv 32 := 0x00b60a63.
Lemma F_152a04 : fetch_word Asan.M.loaded_segments (0x152a48 : word) = Some W_152a04.
Proof. vm_refl. Qed.
Lemma D_152a04 : decode_any W_152a04 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a08 : bv 32 := 0xfff68693.
Lemma F_152a08 : fetch_word Asan.M.loaded_segments (0x152a4c : word) = Some W_152a08.
Proof. vm_refl. Qed.
Lemma D_152a08 : decode_any W_152a08 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a0c : bv 32 := 0x00150513.
Lemma F_152a0c : fetch_word Asan.M.loaded_segments (0x152a50 : word) = Some W_152a0c.
Proof. vm_refl. Qed.
Lemma D_152a0c : decode_any W_152a0c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a10 : bv 32 := 0xfe0698e3.
Lemma F_152a10 : fetch_word Asan.M.loaded_segments (0x152a54 : word) = Some W_152a10.
Proof. vm_refl. Qed.
Lemma D_152a10 : decode_any W_152a10 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a18 : bv 32 := 0x00008067.
Lemma F_152a18 : fetch_word Asan.M.loaded_segments (0x152a5c : word) = Some W_152a18.
Proof. vm_refl. Qed.
Lemma D_152a18 : decode_any W_152a18 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a1c : bv 32 := 0x00060693.
Lemma F_152a1c : fetch_word Asan.M.loaded_segments (0x152a60 : word) = Some W_152a1c.
Proof. vm_refl. Qed.
Lemma D_152a1c : decode_any W_152a1c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a20 : bv 32 := 0x00054603.
Lemma F_152a20 : fetch_word Asan.M.loaded_segments (0x152a64 : word) = Some W_152a20.
Proof. vm_refl. Qed.
Lemma D_152a20 : decode_any W_152a20 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a24 : bv 32 := 0xfeb612e3.
Lemma F_152a24 : fetch_word Asan.M.loaded_segments (0x152a68 : word) = Some W_152a24.
Proof. vm_refl. Qed.
Lemma D_152a24 : decode_any W_152a24 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a28 : bv 32 := 0xff1ff06f.
Lemma F_152a28 : fetch_word Asan.M.loaded_segments (0x152a6c : word) = Some W_152a28.
Proof. vm_refl. Qed.
Lemma D_152a28 : decode_any W_152a28 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a5c : bv 32 := 0x0035f693.
Lemma F_152a5c : fetch_word Asan.M.loaded_segments (0x152aa0 : word) = Some W_152a5c.
Proof. vm_refl. Qed.
Lemma D_152a5c : decode_any W_152a5c = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a60 : bv 32 := 0x10068863.
Lemma F_152a60 : fetch_word Asan.M.loaded_segments (0x152aa4 : word) = Some W_152a60.
Proof. vm_refl. Qed.
Lemma D_152a60 : decode_any W_152a60 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a64 : bv 32 := 0x02060e63.
Lemma F_152a64 : fetch_word Asan.M.loaded_segments (0x152aa8 : word) = Some W_152a64.
Proof. vm_refl. Qed.
Lemma D_152a64 : decode_any W_152a64 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a68 : bv 32 := 0x00158713.
Lemma F_152a68 : fetch_word Asan.M.loaded_segments (0x152aac : word) = Some W_152a68.
Proof. vm_refl. Qed.
Lemma D_152a68 : decode_any W_152a68 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a6c : bv 32 := 0x00100793.
Lemma F_152a6c : fetch_word Asan.M.loaded_segments (0x152ab0 : word) = Some W_152a6c.
Proof. vm_refl. Qed.
Lemma D_152a6c : decode_any W_152a6c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a70 : bv 32 := 0x00050693.
Lemma F_152a70 : fetch_word Asan.M.loaded_segments (0x152ab4 : word) = Some W_152a70.
Proof. vm_refl. Qed.
Lemma D_152a70 : decode_any W_152a70 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a74 : bv 32 := 0x0005c883.
Lemma F_152a74 : fetch_word Asan.M.loaded_segments (0x152ab8 : word) = Some W_152a74.
Proof. vm_refl. Qed.
Lemma D_152a74 : decode_any W_152a74 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a78 : bv 32 := 0x00060813.
Lemma F_152a78 : fetch_word Asan.M.loaded_segments (0x152abc : word) = Some W_152a78.
Proof. vm_refl. Qed.
Lemma D_152a78 : decode_any W_152a78 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a7c : bv 32 := 0x00158593.
Lemma F_152a7c : fetch_word Asan.M.loaded_segments (0x152ac0 : word) = Some W_152a7c.
Proof. vm_refl. Qed.
Lemma D_152a7c : decode_any W_152a7c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a80 : bv 32 := 0x00377293.
Lemma F_152a80 : fetch_word Asan.M.loaded_segments (0x152ac4 : word) = Some W_152a80.
Proof. vm_refl. Qed.
Lemma D_152a80 : decode_any W_152a80 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a84 : bv 32 := 0x01168023.
Lemma F_152a84 : fetch_word Asan.M.loaded_segments (0x152ac8 : word) = Some W_152a84.
Proof. vm_refl. Qed.
Lemma D_152a84 : decode_any W_152a84 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a88 : bv 32 := 0x00168693.
Lemma F_152a88 : fetch_word Asan.M.loaded_segments (0x152acc : word) = Some W_152a88.
Proof. vm_refl. Qed.
Lemma D_152a88 : decode_any W_152a88 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a8c : bv 32 := 0xfff60613.
Lemma F_152a8c : fetch_word Asan.M.loaded_segments (0x152ad0 : word) = Some W_152a8c.
Proof. vm_refl. Qed.
Lemma D_152a8c : decode_any W_152a8c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a90 : bv 32 := 0x00028a63.
Lemma F_152a90 : fetch_word Asan.M.loaded_segments (0x152ad4 : word) = Some W_152a90.
Proof. vm_refl. Qed.
Lemma D_152a90 : decode_any W_152a90 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a94 : bv 32 := 0x00170713.
Lemma F_152a94 : fetch_word Asan.M.loaded_segments (0x152ad8 : word) = Some W_152a94.
Proof. vm_refl. Qed.
Lemma D_152a94 : decode_any W_152a94 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a98 : bv 32 := 0xfcf81ee3.
Lemma F_152a98 : fetch_word Asan.M.loaded_segments (0x152adc : word) = Some W_152a98.
Proof. vm_refl. Qed.
Lemma D_152a98 : decode_any W_152a98 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152a9c : bv 32 := 0x0080006f.
Lemma F_152a9c : fetch_word Asan.M.loaded_segments (0x152ae0 : word) = Some W_152a9c.
Proof. vm_refl. Qed.
Lemma D_152a9c : decode_any W_152a9c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152aa0 : bv 32 := 0x00050693.
Lemma F_152aa0 : fetch_word Asan.M.loaded_segments (0x152ae4 : word) = Some W_152aa0.
Proof. vm_refl. Qed.
Lemma D_152aa0 : decode_any W_152aa0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152aa4 : bv 32 := 0x0036f793.
Lemma F_152aa4 : fetch_word Asan.M.loaded_segments (0x152ae8 : word) = Some W_152aa4.
Proof. vm_refl. Qed.
Lemma D_152aa4 : decode_any W_152aa4 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152aa8 : bv 32 := 0x0c078a63.
Lemma F_152aa8 : fetch_word Asan.M.loaded_segments (0x152aec : word) = Some W_152aa8.
Proof. vm_refl. Qed.
Lemma D_152aa8 : decode_any W_152aa8 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152aac : bv 32 := 0x02000713.
Lemma F_152aac : fetch_word Asan.M.loaded_segments (0x152af0 : word) = Some W_152aac.
Proof. vm_refl. Qed.
Lemma D_152aac : decode_any W_152aac = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ab0 : bv 32 := 0x02e67063.
Lemma F_152ab0 : fetch_word Asan.M.loaded_segments (0x152af4 : word) = Some W_152ab0.
Proof. vm_refl. Qed.
Lemma D_152ab0 : decode_any W_152ab0 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ab4 : bv 32 := 0x01000713.
Lemma F_152ab4 : fetch_word Asan.M.loaded_segments (0x152af8 : word) = Some W_152ab4.
Proof. vm_refl. Qed.
Lemma D_152ab4 : decode_any W_152ab4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ab8 : bv 32 := 0x24e67863.
Lemma F_152ab8 : fetch_word Asan.M.loaded_segments (0x152afc : word) = Some W_152ab8.
Proof. vm_refl. Qed.
Lemma D_152ab8 : decode_any W_152ab8 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152abc : bv 32 := 0x00867713.
Lemma F_152abc : fetch_word Asan.M.loaded_segments (0x152b00 : word) = Some W_152abc.
Proof. vm_refl. Qed.
Lemma D_152abc : decode_any W_152abc = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ac0 : bv 32 := 0x2c071e63.
Lemma F_152ac0 : fetch_word Asan.M.loaded_segments (0x152b04 : word) = Some W_152ac0.
Proof. vm_refl. Qed.
Lemma D_152ac0 : decode_any W_152ac0 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ac4 : bv 32 := 0x00467713.
Lemma F_152ac4 : fetch_word Asan.M.loaded_segments (0x152b08 : word) = Some W_152ac4.
Proof. vm_refl. Qed.
Lemma D_152ac4 : decode_any W_152ac4 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ac8 : bv 32 := 0x32071463.
Lemma F_152ac8 : fetch_word Asan.M.loaded_segments (0x152b0c : word) = Some W_152ac8.
Proof. vm_refl. Qed.
Lemma D_152ac8 : decode_any W_152ac8 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152acc : bv 32 := 0x3500006f.
Lemma F_152acc : fetch_word Asan.M.loaded_segments (0x152b10 : word) = Some W_152acc.
Proof. vm_refl. Qed.
Lemma D_152acc : decode_any W_152acc = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ad0 : bv 32 := 0x0005a703.
Lemma F_152ad0 : fetch_word Asan.M.loaded_segments (0x152b14 : word) = Some W_152ad0.
Proof. vm_refl. Qed.
Lemma D_152ad0 : decode_any W_152ad0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ad4 : bv 32 := 0x00300813.
Lemma F_152ad4 : fetch_word Asan.M.loaded_segments (0x152b18 : word) = Some W_152ad4.
Proof. vm_refl. Qed.
Lemma D_152ad4 : decode_any W_152ad4 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ad8 : bv 32 := 0x11078e63.
Lemma F_152ad8 : fetch_word Asan.M.loaded_segments (0x152b1c : word) = Some W_152ad8.
Proof. vm_refl. Qed.
Lemma D_152ad8 : decode_any W_152ad8 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152adc : bv 32 := 0x00200813.
Lemma F_152adc : fetch_word Asan.M.loaded_segments (0x152b20 : word) = Some W_152adc.
Proof. vm_refl. Qed.
Lemma D_152adc : decode_any W_152adc = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ae0 : bv 32 := 0x19079c63.
Lemma F_152ae0 : fetch_word Asan.M.loaded_segments (0x152b24 : word) = Some W_152ae0.
Proof. vm_refl. Qed.
Lemma D_152ae0 : decode_any W_152ae0 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ae4 : bv 32 := 0x00875793.
Lemma F_152ae4 : fetch_word Asan.M.loaded_segments (0x152b28 : word) = Some W_152ae4.
Proof. vm_refl. Qed.
Lemma D_152ae4 : decode_any W_152ae4 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ae8 : bv 32 := 0xffe60613.
Lemma F_152ae8 : fetch_word Asan.M.loaded_segments (0x152b2c : word) = Some W_152ae8.
Proof. vm_refl. Qed.
Lemma D_152ae8 : decode_any W_152ae8 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152aec : bv 32 := 0x00e68023.
Lemma F_152aec : fetch_word Asan.M.loaded_segments (0x152b30 : word) = Some W_152aec.
Proof. vm_refl. Qed.
Lemma D_152aec : decode_any W_152aec = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152af0 : bv 32 := 0x00f680a3.
Lemma F_152af0 : fetch_word Asan.M.loaded_segments (0x152b34 : word) = Some W_152af0.
Proof. vm_refl. Qed.
Lemma D_152af0 : decode_any W_152af0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152af4 : bv 32 := 0x00268693.
Lemma F_152af4 : fetch_word Asan.M.loaded_segments (0x152b38 : word) = Some W_152af4.
Proof. vm_refl. Qed.
Lemma D_152af4 : decode_any W_152af4 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152af8 : bv 32 := 0x01058593.
Lemma F_152af8 : fetch_word Asan.M.loaded_segments (0x152b3c : word) = Some W_152af8.
Proof. vm_refl. Qed.
Lemma D_152af8 : decode_any W_152af8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152afc : bv 32 := 0x01100793.
Lemma F_152afc : fetch_word Asan.M.loaded_segments (0x152b40 : word) = Some W_152afc.
Proof. vm_refl. Qed.
Lemma D_152afc : decode_any W_152afc = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b00 : bv 32 := 0x0107581b.
Lemma F_152b00 : fetch_word Asan.M.loaded_segments (0x152b44 : word) = Some W_152b00.
Proof. vm_refl. Qed.
Lemma D_152b00 : decode_any W_152b00 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b04 : bv 32 := 0xff45a883.
Lemma F_152b04 : fetch_word Asan.M.loaded_segments (0x152b48 : word) = Some W_152b04.
Proof. vm_refl. Qed.
Lemma D_152b04 : decode_any W_152b04 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b08 : bv 32 := 0xff85a283.
Lemma F_152b08 : fetch_word Asan.M.loaded_segments (0x152b4c : word) = Some W_152b08.
Proof. vm_refl. Qed.
Lemma D_152b08 : decode_any W_152b08 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b0c : bv 32 := 0xffc5a303.
Lemma F_152b0c : fetch_word Asan.M.loaded_segments (0x152b50 : word) = Some W_152b0c.
Proof. vm_refl. Qed.
Lemma D_152b0c : decode_any W_152b0c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b10 : bv 32 := 0x0005a703.
Lemma F_152b10 : fetch_word Asan.M.loaded_segments (0x152b54 : word) = Some W_152b10.
Proof. vm_refl. Qed.
Lemma D_152b10 : decode_any W_152b10 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b14 : bv 32 := 0x01089393.
Lemma F_152b14 : fetch_word Asan.M.loaded_segments (0x152b58 : word) = Some W_152b14.
Proof. vm_refl. Qed.
Lemma D_152b14 : decode_any W_152b14 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b18 : bv 32 := 0x0108d89b.
Lemma F_152b18 : fetch_word Asan.M.loaded_segments (0x152b5c : word) = Some W_152b18.
Proof. vm_refl. Qed.
Lemma D_152b18 : decode_any W_152b18 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b1c : bv 32 := 0x0103e833.
Lemma F_152b1c : fetch_word Asan.M.loaded_segments (0x152b60 : word) = Some W_152b1c.
Proof. vm_refl. Qed.
Lemma D_152b1c : decode_any W_152b1c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b20 : bv 32 := 0x01029393.
Lemma F_152b20 : fetch_word Asan.M.loaded_segments (0x152b64 : word) = Some W_152b20.
Proof. vm_refl. Qed.
Lemma D_152b20 : decode_any W_152b20 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b24 : bv 32 := 0x0102d29b.
Lemma F_152b24 : fetch_word Asan.M.loaded_segments (0x152b68 : word) = Some W_152b24.
Proof. vm_refl. Qed.
Lemma D_152b24 : decode_any W_152b24 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b28 : bv 32 := 0x0113e8b3.
Lemma F_152b28 : fetch_word Asan.M.loaded_segments (0x152b6c : word) = Some W_152b28.
Proof. vm_refl. Qed.
Lemma D_152b28 : decode_any W_152b28 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b2c : bv 32 := 0x01031393.
Lemma F_152b2c : fetch_word Asan.M.loaded_segments (0x152b70 : word) = Some W_152b2c.
Proof. vm_refl. Qed.
Lemma D_152b2c : decode_any W_152b2c = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b30 : bv 32 := 0x0103531b.
Lemma F_152b30 : fetch_word Asan.M.loaded_segments (0x152b74 : word) = Some W_152b30.
Proof. vm_refl. Qed.
Lemma D_152b30 : decode_any W_152b30 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b34 : bv 32 := 0x0053e2b3.
Lemma F_152b34 : fetch_word Asan.M.loaded_segments (0x152b78 : word) = Some W_152b34.
Proof. vm_refl. Qed.
Lemma D_152b34 : decode_any W_152b34 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b38 : bv 32 := 0x01071393.
Lemma F_152b38 : fetch_word Asan.M.loaded_segments (0x152b7c : word) = Some W_152b38.
Proof. vm_refl. Qed.
Lemma D_152b38 : decode_any W_152b38 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b3c : bv 32 := 0x0063e333.
Lemma F_152b3c : fetch_word Asan.M.loaded_segments (0x152b80 : word) = Some W_152b3c.
Proof. vm_refl. Qed.
Lemma D_152b3c : decode_any W_152b3c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b40 : bv 32 := 0xff060613.
Lemma F_152b40 : fetch_word Asan.M.loaded_segments (0x152b84 : word) = Some W_152b40.
Proof. vm_refl. Qed.
Lemma D_152b40 : decode_any W_152b40 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b44 : bv 32 := 0x0106a023.
Lemma F_152b44 : fetch_word Asan.M.loaded_segments (0x152b88 : word) = Some W_152b44.
Proof. vm_refl. Qed.
Lemma D_152b44 : decode_any W_152b44 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b48 : bv 32 := 0x0116a223.
Lemma F_152b48 : fetch_word Asan.M.loaded_segments (0x152b8c : word) = Some W_152b48.
Proof. vm_refl. Qed.
Lemma D_152b48 : decode_any W_152b48 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b4c : bv 32 := 0x0056a423.
Lemma F_152b4c : fetch_word Asan.M.loaded_segments (0x152b90 : word) = Some W_152b4c.
Proof. vm_refl. Qed.
Lemma D_152b4c : decode_any W_152b4c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b50 : bv 32 := 0x0066a623.
Lemma F_152b50 : fetch_word Asan.M.loaded_segments (0x152b94 : word) = Some W_152b50.
Proof. vm_refl. Qed.
Lemma D_152b50 : decode_any W_152b50 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b54 : bv 32 := 0x01068693.
Lemma F_152b54 : fetch_word Asan.M.loaded_segments (0x152b98 : word) = Some W_152b54.
Proof. vm_refl. Qed.
Lemma D_152b54 : decode_any W_152b54 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b58 : bv 32 := 0x01058593.
Lemma F_152b58 : fetch_word Asan.M.loaded_segments (0x152b9c : word) = Some W_152b58.
Proof. vm_refl. Qed.
Lemma D_152b58 : decode_any W_152b58 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b5c : bv 32 := 0xfac7e2e3.
Lemma F_152b5c : fetch_word Asan.M.loaded_segments (0x152ba0 : word) = Some W_152b5c.
Proof. vm_refl. Qed.
Lemma D_152b5c : decode_any W_152b5c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b60 : bv 32 := 0xff258593.
Lemma F_152b60 : fetch_word Asan.M.loaded_segments (0x152ba4 : word) = Some W_152b60.
Proof. vm_refl. Qed.
Lemma D_152b60 : decode_any W_152b60 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b64 : bv 32 := 0x01000713.
Lemma F_152b64 : fetch_word Asan.M.loaded_segments (0x152ba8 : word) = Some W_152b64.
Proof. vm_refl. Qed.
Lemma D_152b64 : decode_any W_152b64 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b68 : bv 32 := 0xf4e66ae3.
Lemma F_152b68 : fetch_word Asan.M.loaded_segments (0x152bac : word) = Some W_152b68.
Proof. vm_refl. Qed.
Lemma D_152b68 : decode_any W_152b68 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b6c : bv 32 := 0x19c0006f.
Lemma F_152b6c : fetch_word Asan.M.loaded_segments (0x152bb0 : word) = Some W_152b6c.
Proof. vm_refl. Qed.
Lemma D_152b6c : decode_any W_152b6c = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b70 : bv 32 := 0x00050693.
Lemma F_152b70 : fetch_word Asan.M.loaded_segments (0x152bb4 : word) = Some W_152b70.
Proof. vm_refl. Qed.
Lemma D_152b70 : decode_any W_152b70 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b74 : bv 32 := 0x00357793.
Lemma F_152b74 : fetch_word Asan.M.loaded_segments (0x152bb8 : word) = Some W_152b74.
Proof. vm_refl. Qed.
Lemma D_152b74 : decode_any W_152b74 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b78 : bv 32 := 0xf2079ae3.
Lemma F_152b78 : fetch_word Asan.M.loaded_segments (0x152bbc : word) = Some W_152b78.
Proof. vm_refl. Qed.
Lemma D_152b78 : decode_any W_152b78 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b7c : bv 32 := 0x01000713.
Lemma F_152b7c : fetch_word Asan.M.loaded_segments (0x152bc0 : word) = Some W_152b7c.
Proof. vm_refl. Qed.
Lemma D_152b7c : decode_any W_152b7c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b80 : bv 32 := 0x02e66c63.
Lemma F_152b80 : fetch_word Asan.M.loaded_segments (0x152bc4 : word) = Some W_152b80.
Proof. vm_refl. Qed.
Lemma D_152b80 : decode_any W_152b80 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b84 : bv 32 := 0x00f00713.
Lemma F_152b84 : fetch_word Asan.M.loaded_segments (0x152bc8 : word) = Some W_152b84.
Proof. vm_refl. Qed.
Lemma D_152b84 : decode_any W_152b84 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b88 : bv 32 := 0x0005a783.
Lemma F_152b88 : fetch_word Asan.M.loaded_segments (0x152bcc : word) = Some W_152b88.
Proof. vm_refl. Qed.
Lemma D_152b88 : decode_any W_152b88 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b8c : bv 32 := 0x0045a803.
Lemma F_152b8c : fetch_word Asan.M.loaded_segments (0x152bd0 : word) = Some W_152b8c.
Proof. vm_refl. Qed.
Lemma D_152b8c : decode_any W_152b8c = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b90 : bv 32 := 0x0085a883.
Lemma F_152b90 : fetch_word Asan.M.loaded_segments (0x152bd4 : word) = Some W_152b90.
Proof. vm_refl. Qed.
Lemma D_152b90 : decode_any W_152b90 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b94 : bv 32 := 0x00c5a283.
Lemma F_152b94 : fetch_word Asan.M.loaded_segments (0x152bd8 : word) = Some W_152b94.
Proof. vm_refl. Qed.
Lemma D_152b94 : decode_any W_152b94 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b98 : bv 32 := 0x01058593.
Lemma F_152b98 : fetch_word Asan.M.loaded_segments (0x152bdc : word) = Some W_152b98.
Proof. vm_refl. Qed.
Lemma D_152b98 : decode_any W_152b98 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152b9c : bv 32 := 0xff060613.
Lemma F_152b9c : fetch_word Asan.M.loaded_segments (0x152be0 : word) = Some W_152b9c.
Proof. vm_refl. Qed.
Lemma D_152b9c : decode_any W_152b9c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ba0 : bv 32 := 0x00f6a023.
Lemma F_152ba0 : fetch_word Asan.M.loaded_segments (0x152be4 : word) = Some W_152ba0.
Proof. vm_refl. Qed.
Lemma D_152ba0 : decode_any W_152ba0 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ba4 : bv 32 := 0x0106a223.
Lemma F_152ba4 : fetch_word Asan.M.loaded_segments (0x152be8 : word) = Some W_152ba4.
Proof. vm_refl. Qed.
Lemma D_152ba4 : decode_any W_152ba4 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ba8 : bv 32 := 0x0116a423.
Lemma F_152ba8 : fetch_word Asan.M.loaded_segments (0x152bec : word) = Some W_152ba8.
Proof. vm_refl. Qed.
Lemma D_152ba8 : decode_any W_152ba8 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bac : bv 32 := 0x0056a623.
Lemma F_152bac : fetch_word Asan.M.loaded_segments (0x152bf0 : word) = Some W_152bac.
Proof. vm_refl. Qed.
Lemma D_152bac : decode_any W_152bac = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bb0 : bv 32 := 0x01068693.
Lemma F_152bb0 : fetch_word Asan.M.loaded_segments (0x152bf4 : word) = Some W_152bb0.
Proof. vm_refl. Qed.
Lemma D_152bb0 : decode_any W_152bb0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bb4 : bv 32 := 0xfcc76ae3.
Lemma F_152bb4 : fetch_word Asan.M.loaded_segments (0x152bf8 : word) = Some W_152bb4.
Proof. vm_refl. Qed.
Lemma D_152bb4 : decode_any W_152bb4 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bb8 : bv 32 := 0x00800713.
Lemma F_152bb8 : fetch_word Asan.M.loaded_segments (0x152bfc : word) = Some W_152bb8.
Proof. vm_refl. Qed.
Lemma D_152bb8 : decode_any W_152bb8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bbc : bv 32 := 0x00e66e63.
Lemma F_152bbc : fetch_word Asan.M.loaded_segments (0x152c00 : word) = Some W_152bbc.
Proof. vm_refl. Qed.
Lemma D_152bbc : decode_any W_152bbc = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bc0 : bv 32 := 0x0005a703.
Lemma F_152bc0 : fetch_word Asan.M.loaded_segments (0x152c04 : word) = Some W_152bc0.
Proof. vm_refl. Qed.
Lemma D_152bc0 : decode_any W_152bc0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bc4 : bv 32 := 0x0045a783.
Lemma F_152bc4 : fetch_word Asan.M.loaded_segments (0x152c08 : word) = Some W_152bc4.
Proof. vm_refl. Qed.
Lemma D_152bc4 : decode_any W_152bc4 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bc8 : bv 32 := 0x00e6a023.
Lemma F_152bc8 : fetch_word Asan.M.loaded_segments (0x152c0c : word) = Some W_152bc8.
Proof. vm_refl. Qed.
Lemma D_152bc8 : decode_any W_152bc8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bcc : bv 32 := 0x00f6a223.
Lemma F_152bcc : fetch_word Asan.M.loaded_segments (0x152c10 : word) = Some W_152bcc.
Proof. vm_refl. Qed.
Lemma D_152bcc : decode_any W_152bcc = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bd0 : bv 32 := 0x00868693.
Lemma F_152bd0 : fetch_word Asan.M.loaded_segments (0x152c14 : word) = Some W_152bd0.
Proof. vm_refl. Qed.
Lemma D_152bd0 : decode_any W_152bd0 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bd4 : bv 32 := 0x00858593.
Lemma F_152bd4 : fetch_word Asan.M.loaded_segments (0x152c18 : word) = Some W_152bd4.
Proof. vm_refl. Qed.
Lemma D_152bd4 : decode_any W_152bd4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bd8 : bv 32 := 0x00467713.
Lemma F_152bd8 : fetch_word Asan.M.loaded_segments (0x152c1c : word) = Some W_152bd8.
Proof. vm_refl. Qed.
Lemma D_152bd8 : decode_any W_152bd8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bdc : bv 32 := 0x24070063.
Lemma F_152bdc : fetch_word Asan.M.loaded_segments (0x152c20 : word) = Some W_152bdc.
Proof. vm_refl. Qed.
Lemma D_152bdc : decode_any W_152bdc = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152be0 : bv 32 := 0x0005a703.
Lemma F_152be0 : fetch_word Asan.M.loaded_segments (0x152c24 : word) = Some W_152be0.
Proof. vm_refl. Qed.
Lemma D_152be0 : decode_any W_152be0 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152be4 : bv 32 := 0x00458593.
Lemma F_152be4 : fetch_word Asan.M.loaded_segments (0x152c28 : word) = Some W_152be4.
Proof. vm_refl. Qed.
Lemma D_152be4 : decode_any W_152be4 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152be8 : bv 32 := 0x00e6a023.
Lemma F_152be8 : fetch_word Asan.M.loaded_segments (0x152c2c : word) = Some W_152be8.
Proof. vm_refl. Qed.
Lemma D_152be8 : decode_any W_152be8 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bec : bv 32 := 0x00468693.
Lemma F_152bec : fetch_word Asan.M.loaded_segments (0x152c30 : word) = Some W_152bec.
Proof. vm_refl. Qed.
Lemma D_152bec : decode_any W_152bec = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bf0 : bv 32 := 0x22c0006f.
Lemma F_152bf0 : fetch_word Asan.M.loaded_segments (0x152c34 : word) = Some W_152bf0.
Proof. vm_refl. Qed.
Lemma D_152bf0 : decode_any W_152bf0 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bf4 : bv 32 := 0x00e68023.
Lemma F_152bf4 : fetch_word Asan.M.loaded_segments (0x152c38 : word) = Some W_152bf4.
Proof. vm_refl. Qed.
Lemma D_152bf4 : decode_any W_152bf4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bf8 : bv 32 := 0x00168693.
Lemma F_152bf8 : fetch_word Asan.M.loaded_segments (0x152c3c : word) = Some W_152bf8.
Proof. vm_refl. Qed.
Lemma D_152bf8 : decode_any W_152bf8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152bfc : bv 32 := 0xfff60613.
Lemma F_152bfc : fetch_word Asan.M.loaded_segments (0x152c40 : word) = Some W_152bfc.
Proof. vm_refl. Qed.
Lemma D_152bfc : decode_any W_152bfc = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c00 : bv 32 := 0x01058593.
Lemma F_152c00 : fetch_word Asan.M.loaded_segments (0x152c44 : word) = Some W_152c00.
Proof. vm_refl. Qed.
Lemma D_152c00 : decode_any W_152c00 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c04 : bv 32 := 0x01200793.
Lemma F_152c04 : fetch_word Asan.M.loaded_segments (0x152c48 : word) = Some W_152c04.
Proof. vm_refl. Qed.
Lemma D_152c04 : decode_any W_152c04 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c08 : bv 32 := 0x0087581b.
Lemma F_152c08 : fetch_word Asan.M.loaded_segments (0x152c4c : word) = Some W_152c08.
Proof. vm_refl. Qed.
Lemma D_152c08 : decode_any W_152c08 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c0c : bv 32 := 0xff45a883.
Lemma F_152c0c : fetch_word Asan.M.loaded_segments (0x152c50 : word) = Some W_152c0c.
Proof. vm_refl. Qed.
Lemma D_152c0c : decode_any W_152c0c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c10 : bv 32 := 0xff85a283.
Lemma F_152c10 : fetch_word Asan.M.loaded_segments (0x152c54 : word) = Some W_152c10.
Proof. vm_refl. Qed.
Lemma D_152c10 : decode_any W_152c10 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c14 : bv 32 := 0xffc5a303.
Lemma F_152c14 : fetch_word Asan.M.loaded_segments (0x152c58 : word) = Some W_152c14.
Proof. vm_refl. Qed.
Lemma D_152c14 : decode_any W_152c14 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c18 : bv 32 := 0x0005a703.
Lemma F_152c18 : fetch_word Asan.M.loaded_segments (0x152c5c : word) = Some W_152c18.
Proof. vm_refl. Qed.
Lemma D_152c18 : decode_any W_152c18 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c1c : bv 32 := 0x01889393.
Lemma F_152c1c : fetch_word Asan.M.loaded_segments (0x152c60 : word) = Some W_152c1c.
Proof. vm_refl. Qed.
Lemma D_152c1c : decode_any W_152c1c = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c20 : bv 32 := 0x0088d89b.
Lemma F_152c20 : fetch_word Asan.M.loaded_segments (0x152c64 : word) = Some W_152c20.
Proof. vm_refl. Qed.
Lemma D_152c20 : decode_any W_152c20 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c24 : bv 32 := 0x0103e833.
Lemma F_152c24 : fetch_word Asan.M.loaded_segments (0x152c68 : word) = Some W_152c24.
Proof. vm_refl. Qed.
Lemma D_152c24 : decode_any W_152c24 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c28 : bv 32 := 0x01829393.
Lemma F_152c28 : fetch_word Asan.M.loaded_segments (0x152c6c : word) = Some W_152c28.
Proof. vm_refl. Qed.
Lemma D_152c28 : decode_any W_152c28 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c2c : bv 32 := 0x0082d29b.
Lemma F_152c2c : fetch_word Asan.M.loaded_segments (0x152c70 : word) = Some W_152c2c.
Proof. vm_refl. Qed.
Lemma D_152c2c : decode_any W_152c2c = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c30 : bv 32 := 0x0113e8b3.
Lemma F_152c30 : fetch_word Asan.M.loaded_segments (0x152c74 : word) = Some W_152c30.
Proof. vm_refl. Qed.
Lemma D_152c30 : decode_any W_152c30 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c34 : bv 32 := 0x01831393.
Lemma F_152c34 : fetch_word Asan.M.loaded_segments (0x152c78 : word) = Some W_152c34.
Proof. vm_refl. Qed.
Lemma D_152c34 : decode_any W_152c34 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c38 : bv 32 := 0x0083531b.
Lemma F_152c38 : fetch_word Asan.M.loaded_segments (0x152c7c : word) = Some W_152c38.
Proof. vm_refl. Qed.
Lemma D_152c38 : decode_any W_152c38 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c3c : bv 32 := 0x0053e2b3.
Lemma F_152c3c : fetch_word Asan.M.loaded_segments (0x152c80 : word) = Some W_152c3c.
Proof. vm_refl. Qed.
Lemma D_152c3c : decode_any W_152c3c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c40 : bv 32 := 0x01871393.
Lemma F_152c40 : fetch_word Asan.M.loaded_segments (0x152c84 : word) = Some W_152c40.
Proof. vm_refl. Qed.
Lemma D_152c40 : decode_any W_152c40 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c44 : bv 32 := 0x0063e333.
Lemma F_152c44 : fetch_word Asan.M.loaded_segments (0x152c88 : word) = Some W_152c44.
Proof. vm_refl. Qed.
Lemma D_152c44 : decode_any W_152c44 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c48 : bv 32 := 0xff060613.
Lemma F_152c48 : fetch_word Asan.M.loaded_segments (0x152c8c : word) = Some W_152c48.
Proof. vm_refl. Qed.
Lemma D_152c48 : decode_any W_152c48 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c4c : bv 32 := 0x0106a023.
Lemma F_152c4c : fetch_word Asan.M.loaded_segments (0x152c90 : word) = Some W_152c4c.
Proof. vm_refl. Qed.
Lemma D_152c4c : decode_any W_152c4c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c50 : bv 32 := 0x0116a223.
Lemma F_152c50 : fetch_word Asan.M.loaded_segments (0x152c94 : word) = Some W_152c50.
Proof. vm_refl. Qed.
Lemma D_152c50 : decode_any W_152c50 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c54 : bv 32 := 0x0056a423.
Lemma F_152c54 : fetch_word Asan.M.loaded_segments (0x152c98 : word) = Some W_152c54.
Proof. vm_refl. Qed.
Lemma D_152c54 : decode_any W_152c54 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c58 : bv 32 := 0x0066a623.
Lemma F_152c58 : fetch_word Asan.M.loaded_segments (0x152c9c : word) = Some W_152c58.
Proof. vm_refl. Qed.
Lemma D_152c58 : decode_any W_152c58 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c5c : bv 32 := 0x01068693.
Lemma F_152c5c : fetch_word Asan.M.loaded_segments (0x152ca0 : word) = Some W_152c5c.
Proof. vm_refl. Qed.
Lemma D_152c5c : decode_any W_152c5c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c60 : bv 32 := 0x01058593.
Lemma F_152c60 : fetch_word Asan.M.loaded_segments (0x152ca4 : word) = Some W_152c60.
Proof. vm_refl. Qed.
Lemma D_152c60 : decode_any W_152c60 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c64 : bv 32 := 0xfac7e2e3.
Lemma F_152c64 : fetch_word Asan.M.loaded_segments (0x152ca8 : word) = Some W_152c64.
Proof. vm_refl. Qed.
Lemma D_152c64 : decode_any W_152c64 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c68 : bv 32 := 0xff158593.
Lemma F_152c68 : fetch_word Asan.M.loaded_segments (0x152cac : word) = Some W_152c68.
Proof. vm_refl. Qed.
Lemma D_152c68 : decode_any W_152c68 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c6c : bv 32 := 0x01000713.
Lemma F_152c6c : fetch_word Asan.M.loaded_segments (0x152cb0 : word) = Some W_152c6c.
Proof. vm_refl. Qed.
Lemma D_152c6c : decode_any W_152c6c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c70 : bv 32 := 0xe4e666e3.
Lemma F_152c70 : fetch_word Asan.M.loaded_segments (0x152cb4 : word) = Some W_152c70.
Proof. vm_refl. Qed.
Lemma D_152c70 : decode_any W_152c70 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c74 : bv 32 := 0x0940006f.
Lemma F_152c74 : fetch_word Asan.M.loaded_segments (0x152cb8 : word) = Some W_152c74.
Proof. vm_refl. Qed.
Lemma D_152c74 : decode_any W_152c74 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c78 : bv 32 := 0x00875793.
Lemma F_152c78 : fetch_word Asan.M.loaded_segments (0x152cbc : word) = Some W_152c78.
Proof. vm_refl. Qed.
Lemma D_152c78 : decode_any W_152c78 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c7c : bv 32 := 0x01075813.
Lemma F_152c7c : fetch_word Asan.M.loaded_segments (0x152cc0 : word) = Some W_152c7c.
Proof. vm_refl. Qed.
Lemma D_152c7c : decode_any W_152c7c = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c80 : bv 32 := 0xffd60613.
Lemma F_152c80 : fetch_word Asan.M.loaded_segments (0x152cc4 : word) = Some W_152c80.
Proof. vm_refl. Qed.
Lemma D_152c80 : decode_any W_152c80 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c84 : bv 32 := 0x00e68023.
Lemma F_152c84 : fetch_word Asan.M.loaded_segments (0x152cc8 : word) = Some W_152c84.
Proof. vm_refl. Qed.
Lemma D_152c84 : decode_any W_152c84 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c88 : bv 32 := 0x00f680a3.
Lemma F_152c88 : fetch_word Asan.M.loaded_segments (0x152ccc : word) = Some W_152c88.
Proof. vm_refl. Qed.
Lemma D_152c88 : decode_any W_152c88 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c8c : bv 32 := 0x01068123.
Lemma F_152c8c : fetch_word Asan.M.loaded_segments (0x152cd0 : word) = Some W_152c8c.
Proof. vm_refl. Qed.
Lemma D_152c8c : decode_any W_152c8c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c90 : bv 32 := 0x00368693.
Lemma F_152c90 : fetch_word Asan.M.loaded_segments (0x152cd4 : word) = Some W_152c90.
Proof. vm_refl. Qed.
Lemma D_152c90 : decode_any W_152c90 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c94 : bv 32 := 0x01058593.
Lemma F_152c94 : fetch_word Asan.M.loaded_segments (0x152cd8 : word) = Some W_152c94.
Proof. vm_refl. Qed.
Lemma D_152c94 : decode_any W_152c94 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c98 : bv 32 := 0x01000793.
Lemma F_152c98 : fetch_word Asan.M.loaded_segments (0x152cdc : word) = Some W_152c98.
Proof. vm_refl. Qed.
Lemma D_152c98 : decode_any W_152c98 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152c9c : bv 32 := 0x0187581b.
Lemma F_152c9c : fetch_word Asan.M.loaded_segments (0x152ce0 : word) = Some W_152c9c.
Proof. vm_refl. Qed.
Lemma D_152c9c : decode_any W_152c9c = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ca0 : bv 32 := 0xff45a883.
Lemma F_152ca0 : fetch_word Asan.M.loaded_segments (0x152ce4 : word) = Some W_152ca0.
Proof. vm_refl. Qed.
Lemma D_152ca0 : decode_any W_152ca0 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ca4 : bv 32 := 0xff85a283.
Lemma F_152ca4 : fetch_word Asan.M.loaded_segments (0x152ce8 : word) = Some W_152ca4.
Proof. vm_refl. Qed.
Lemma D_152ca4 : decode_any W_152ca4 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ca8 : bv 32 := 0xffc5a303.
Lemma F_152ca8 : fetch_word Asan.M.loaded_segments (0x152cec : word) = Some W_152ca8.
Proof. vm_refl. Qed.
Lemma D_152ca8 : decode_any W_152ca8 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cac : bv 32 := 0x0005a703.
Lemma F_152cac : fetch_word Asan.M.loaded_segments (0x152cf0 : word) = Some W_152cac.
Proof. vm_refl. Qed.
Lemma D_152cac : decode_any W_152cac = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cb0 : bv 32 := 0x00889393.
Lemma F_152cb0 : fetch_word Asan.M.loaded_segments (0x152cf4 : word) = Some W_152cb0.
Proof. vm_refl. Qed.
Lemma D_152cb0 : decode_any W_152cb0 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cb4 : bv 32 := 0x0188d89b.
Lemma F_152cb4 : fetch_word Asan.M.loaded_segments (0x152cf8 : word) = Some W_152cb4.
Proof. vm_refl. Qed.
Lemma D_152cb4 : decode_any W_152cb4 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cb8 : bv 32 := 0x0103e833.
Lemma F_152cb8 : fetch_word Asan.M.loaded_segments (0x152cfc : word) = Some W_152cb8.
Proof. vm_refl. Qed.
Lemma D_152cb8 : decode_any W_152cb8 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cbc : bv 32 := 0x00829393.
Lemma F_152cbc : fetch_word Asan.M.loaded_segments (0x152d00 : word) = Some W_152cbc.
Proof. vm_refl. Qed.
Lemma D_152cbc : decode_any W_152cbc = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cc0 : bv 32 := 0x0182d29b.
Lemma F_152cc0 : fetch_word Asan.M.loaded_segments (0x152d04 : word) = Some W_152cc0.
Proof. vm_refl. Qed.
Lemma D_152cc0 : decode_any W_152cc0 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cc4 : bv 32 := 0x0113e8b3.
Lemma F_152cc4 : fetch_word Asan.M.loaded_segments (0x152d08 : word) = Some W_152cc4.
Proof. vm_refl. Qed.
Lemma D_152cc4 : decode_any W_152cc4 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cc8 : bv 32 := 0x00831393.
Lemma F_152cc8 : fetch_word Asan.M.loaded_segments (0x152d0c : word) = Some W_152cc8.
Proof. vm_refl. Qed.
Lemma D_152cc8 : decode_any W_152cc8 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ccc : bv 32 := 0x0183531b.
Lemma F_152ccc : fetch_word Asan.M.loaded_segments (0x152d10 : word) = Some W_152ccc.
Proof. vm_refl. Qed.
Lemma D_152ccc : decode_any W_152ccc = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cd0 : bv 32 := 0x0053e2b3.
Lemma F_152cd0 : fetch_word Asan.M.loaded_segments (0x152d14 : word) = Some W_152cd0.
Proof. vm_refl. Qed.
Lemma D_152cd0 : decode_any W_152cd0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cd4 : bv 32 := 0x00871393.
Lemma F_152cd4 : fetch_word Asan.M.loaded_segments (0x152d18 : word) = Some W_152cd4.
Proof. vm_refl. Qed.
Lemma D_152cd4 : decode_any W_152cd4 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cd8 : bv 32 := 0x0063e333.
Lemma F_152cd8 : fetch_word Asan.M.loaded_segments (0x152d1c : word) = Some W_152cd8.
Proof. vm_refl. Qed.
Lemma D_152cd8 : decode_any W_152cd8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cdc : bv 32 := 0xff060613.
Lemma F_152cdc : fetch_word Asan.M.loaded_segments (0x152d20 : word) = Some W_152cdc.
Proof. vm_refl. Qed.
Lemma D_152cdc : decode_any W_152cdc = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ce0 : bv 32 := 0x0106a023.
Lemma F_152ce0 : fetch_word Asan.M.loaded_segments (0x152d24 : word) = Some W_152ce0.
Proof. vm_refl. Qed.
Lemma D_152ce0 : decode_any W_152ce0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ce4 : bv 32 := 0x0116a223.
Lemma F_152ce4 : fetch_word Asan.M.loaded_segments (0x152d28 : word) = Some W_152ce4.
Proof. vm_refl. Qed.
Lemma D_152ce4 : decode_any W_152ce4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ce8 : bv 32 := 0x0056a423.
Lemma F_152ce8 : fetch_word Asan.M.loaded_segments (0x152d2c : word) = Some W_152ce8.
Proof. vm_refl. Qed.
Lemma D_152ce8 : decode_any W_152ce8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cec : bv 32 := 0x0066a623.
Lemma F_152cec : fetch_word Asan.M.loaded_segments (0x152d30 : word) = Some W_152cec.
Proof. vm_refl. Qed.
Lemma D_152cec : decode_any W_152cec = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cf0 : bv 32 := 0x01068693.
Lemma F_152cf0 : fetch_word Asan.M.loaded_segments (0x152d34 : word) = Some W_152cf0.
Proof. vm_refl. Qed.
Lemma D_152cf0 : decode_any W_152cf0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cf4 : bv 32 := 0x01058593.
Lemma F_152cf4 : fetch_word Asan.M.loaded_segments (0x152d38 : word) = Some W_152cf4.
Proof. vm_refl. Qed.
Lemma D_152cf4 : decode_any W_152cf4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cf8 : bv 32 := 0xfac7e2e3.
Lemma F_152cf8 : fetch_word Asan.M.loaded_segments (0x152d3c : word) = Some W_152cf8.
Proof. vm_refl. Qed.
Lemma D_152cf8 : decode_any W_152cf8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152cfc : bv 32 := 0xff358593.
Lemma F_152cfc : fetch_word Asan.M.loaded_segments (0x152d40 : word) = Some W_152cfc.
Proof. vm_refl. Qed.
Lemma D_152cfc : decode_any W_152cfc = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d00 : bv 32 := 0x01000713.
Lemma F_152d00 : fetch_word Asan.M.loaded_segments (0x152d44 : word) = Some W_152d00.
Proof. vm_refl. Qed.
Lemma D_152d00 : decode_any W_152d00 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d04 : bv 32 := 0xdae66ce3.
Lemma F_152d04 : fetch_word Asan.M.loaded_segments (0x152d48 : word) = Some W_152d04.
Proof. vm_refl. Qed.
Lemma D_152d04 : decode_any W_152d04 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d08 : bv 32 := 0x0005c703.
Lemma F_152d08 : fetch_word Asan.M.loaded_segments (0x152d4c : word) = Some W_152d08.
Proof. vm_refl. Qed.
Lemma D_152d08 : decode_any W_152d08 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d0c : bv 32 := 0x0015c783.
Lemma F_152d0c : fetch_word Asan.M.loaded_segments (0x152d50 : word) = Some W_152d0c.
Proof. vm_refl. Qed.
Lemma D_152d0c : decode_any W_152d0c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d10 : bv 32 := 0x0025c803.
Lemma F_152d10 : fetch_word Asan.M.loaded_segments (0x152d54 : word) = Some W_152d10.
Proof. vm_refl. Qed.
Lemma D_152d10 : decode_any W_152d10 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d14 : bv 32 := 0x0035c883.
Lemma F_152d14 : fetch_word Asan.M.loaded_segments (0x152d58 : word) = Some W_152d14.
Proof. vm_refl. Qed.
Lemma D_152d14 : decode_any W_152d14 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d18 : bv 32 := 0x0045c283.
Lemma F_152d18 : fetch_word Asan.M.loaded_segments (0x152d5c : word) = Some W_152d18.
Proof. vm_refl. Qed.
Lemma D_152d18 : decode_any W_152d18 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d1c : bv 32 := 0x0055c303.
Lemma F_152d1c : fetch_word Asan.M.loaded_segments (0x152d60 : word) = Some W_152d1c.
Proof. vm_refl. Qed.
Lemma D_152d1c : decode_any W_152d1c = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d20 : bv 32 := 0x0065c383.
Lemma F_152d20 : fetch_word Asan.M.loaded_segments (0x152d64 : word) = Some W_152d20.
Proof. vm_refl. Qed.
Lemma D_152d20 : decode_any W_152d20 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d24 : bv 32 := 0x0075ce03.
Lemma F_152d24 : fetch_word Asan.M.loaded_segments (0x152d68 : word) = Some W_152d24.
Proof. vm_refl. Qed.
Lemma D_152d24 : decode_any W_152d24 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d28 : bv 32 := 0x00e68023.
Lemma F_152d28 : fetch_word Asan.M.loaded_segments (0x152d6c : word) = Some W_152d28.
Proof. vm_refl. Qed.
Lemma D_152d28 : decode_any W_152d28 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d2c : bv 32 := 0x00f680a3.
Lemma F_152d2c : fetch_word Asan.M.loaded_segments (0x152d70 : word) = Some W_152d2c.
Proof. vm_refl. Qed.
Lemma D_152d2c : decode_any W_152d2c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d30 : bv 32 := 0x01068123.
Lemma F_152d30 : fetch_word Asan.M.loaded_segments (0x152d74 : word) = Some W_152d30.
Proof. vm_refl. Qed.
Lemma D_152d30 : decode_any W_152d30 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d34 : bv 32 := 0x011681a3.
Lemma F_152d34 : fetch_word Asan.M.loaded_segments (0x152d78 : word) = Some W_152d34.
Proof. vm_refl. Qed.
Lemma D_152d34 : decode_any W_152d34 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d38 : bv 32 := 0x0085c703.
Lemma F_152d38 : fetch_word Asan.M.loaded_segments (0x152d7c : word) = Some W_152d38.
Proof. vm_refl. Qed.
Lemma D_152d38 : decode_any W_152d38 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d3c : bv 32 := 0x0095c783.
Lemma F_152d3c : fetch_word Asan.M.loaded_segments (0x152d80 : word) = Some W_152d3c.
Proof. vm_refl. Qed.
Lemma D_152d3c : decode_any W_152d3c = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d40 : bv 32 := 0x00a5c803.
Lemma F_152d40 : fetch_word Asan.M.loaded_segments (0x152d84 : word) = Some W_152d40.
Proof. vm_refl. Qed.
Lemma D_152d40 : decode_any W_152d40 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d44 : bv 32 := 0x00b5c883.
Lemma F_152d44 : fetch_word Asan.M.loaded_segments (0x152d88 : word) = Some W_152d44.
Proof. vm_refl. Qed.
Lemma D_152d44 : decode_any W_152d44 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d48 : bv 32 := 0x00568223.
Lemma F_152d48 : fetch_word Asan.M.loaded_segments (0x152d8c : word) = Some W_152d48.
Proof. vm_refl. Qed.
Lemma D_152d48 : decode_any W_152d48 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d4c : bv 32 := 0x006682a3.
Lemma F_152d4c : fetch_word Asan.M.loaded_segments (0x152d90 : word) = Some W_152d4c.
Proof. vm_refl. Qed.
Lemma D_152d4c : decode_any W_152d4c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d50 : bv 32 := 0x00768323.
Lemma F_152d50 : fetch_word Asan.M.loaded_segments (0x152d94 : word) = Some W_152d50.
Proof. vm_refl. Qed.
Lemma D_152d50 : decode_any W_152d50 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d54 : bv 32 := 0x01c683a3.
Lemma F_152d54 : fetch_word Asan.M.loaded_segments (0x152d98 : word) = Some W_152d54.
Proof. vm_refl. Qed.
Lemma D_152d54 : decode_any W_152d54 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d58 : bv 32 := 0x00c5c283.
Lemma F_152d58 : fetch_word Asan.M.loaded_segments (0x152d9c : word) = Some W_152d58.
Proof. vm_refl. Qed.
Lemma D_152d58 : decode_any W_152d58 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d5c : bv 32 := 0x00d5c303.
Lemma F_152d5c : fetch_word Asan.M.loaded_segments (0x152da0 : word) = Some W_152d5c.
Proof. vm_refl. Qed.
Lemma D_152d5c : decode_any W_152d5c = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d60 : bv 32 := 0x00e5c383.
Lemma F_152d60 : fetch_word Asan.M.loaded_segments (0x152da4 : word) = Some W_152d60.
Proof. vm_refl. Qed.
Lemma D_152d60 : decode_any W_152d60 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d64 : bv 32 := 0x00f5ce03.
Lemma F_152d64 : fetch_word Asan.M.loaded_segments (0x152da8 : word) = Some W_152d64.
Proof. vm_refl. Qed.
Lemma D_152d64 : decode_any W_152d64 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d68 : bv 32 := 0x01058593.
Lemma F_152d68 : fetch_word Asan.M.loaded_segments (0x152dac : word) = Some W_152d68.
Proof. vm_refl. Qed.
Lemma D_152d68 : decode_any W_152d68 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d6c : bv 32 := 0x00e68423.
Lemma F_152d6c : fetch_word Asan.M.loaded_segments (0x152db0 : word) = Some W_152d6c.
Proof. vm_refl. Qed.
Lemma D_152d6c : decode_any W_152d6c = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d70 : bv 32 := 0x00f684a3.
Lemma F_152d70 : fetch_word Asan.M.loaded_segments (0x152db4 : word) = Some W_152d70.
Proof. vm_refl. Qed.
Lemma D_152d70 : decode_any W_152d70 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d74 : bv 32 := 0x01068523.
Lemma F_152d74 : fetch_word Asan.M.loaded_segments (0x152db8 : word) = Some W_152d74.
Proof. vm_refl. Qed.
Lemma D_152d74 : decode_any W_152d74 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d78 : bv 32 := 0x011685a3.
Lemma F_152d78 : fetch_word Asan.M.loaded_segments (0x152dbc : word) = Some W_152d78.
Proof. vm_refl. Qed.
Lemma D_152d78 : decode_any W_152d78 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d7c : bv 32 := 0x01068713.
Lemma F_152d7c : fetch_word Asan.M.loaded_segments (0x152dc0 : word) = Some W_152d7c.
Proof. vm_refl. Qed.
Lemma D_152d7c : decode_any W_152d7c = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d80 : bv 32 := 0x00568623.
Lemma F_152d80 : fetch_word Asan.M.loaded_segments (0x152dc4 : word) = Some W_152d80.
Proof. vm_refl. Qed.
Lemma D_152d80 : decode_any W_152d80 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d84 : bv 32 := 0x006686a3.
Lemma F_152d84 : fetch_word Asan.M.loaded_segments (0x152dc8 : word) = Some W_152d84.
Proof. vm_refl. Qed.
Lemma D_152d84 : decode_any W_152d84 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d88 : bv 32 := 0x00768723.
Lemma F_152d88 : fetch_word Asan.M.loaded_segments (0x152dcc : word) = Some W_152d88.
Proof. vm_refl. Qed.
Lemma D_152d88 : decode_any W_152d88 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d8c : bv 32 := 0x01c687a3.
Lemma F_152d8c : fetch_word Asan.M.loaded_segments (0x152dd0 : word) = Some W_152d8c.
Proof. vm_refl. Qed.
Lemma D_152d8c : decode_any W_152d8c = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d90 : bv 32 := 0x00070693.
Lemma F_152d90 : fetch_word Asan.M.loaded_segments (0x152dd4 : word) = Some W_152d90.
Proof. vm_refl. Qed.
Lemma D_152d90 : decode_any W_152d90 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d94 : bv 32 := 0x00867713.
Lemma F_152d94 : fetch_word Asan.M.loaded_segments (0x152dd8 : word) = Some W_152d94.
Proof. vm_refl. Qed.
Lemma D_152d94 : decode_any W_152d94 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d98 : bv 32 := 0xd20706e3.
Lemma F_152d98 : fetch_word Asan.M.loaded_segments (0x152ddc : word) = Some W_152d98.
Proof. vm_refl. Qed.
Lemma D_152d98 : decode_any W_152d98 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152d9c : bv 32 := 0x0005c703.
Lemma F_152d9c : fetch_word Asan.M.loaded_segments (0x152de0 : word) = Some W_152d9c.
Proof. vm_refl. Qed.
Lemma D_152d9c : decode_any W_152d9c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152da0 : bv 32 := 0x0015c783.
Lemma F_152da0 : fetch_word Asan.M.loaded_segments (0x152de4 : word) = Some W_152da0.
Proof. vm_refl. Qed.
Lemma D_152da0 : decode_any W_152da0 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152da4 : bv 32 := 0x0025c803.
Lemma F_152da4 : fetch_word Asan.M.loaded_segments (0x152de8 : word) = Some W_152da4.
Proof. vm_refl. Qed.
Lemma D_152da4 : decode_any W_152da4 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152da8 : bv 32 := 0x0035c883.
Lemma F_152da8 : fetch_word Asan.M.loaded_segments (0x152dec : word) = Some W_152da8.
Proof. vm_refl. Qed.
Lemma D_152da8 : decode_any W_152da8 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152dac : bv 32 := 0x0045c283.
Lemma F_152dac : fetch_word Asan.M.loaded_segments (0x152df0 : word) = Some W_152dac.
Proof. vm_refl. Qed.
Lemma D_152dac : decode_any W_152dac = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152db0 : bv 32 := 0x0055c303.
Lemma F_152db0 : fetch_word Asan.M.loaded_segments (0x152df4 : word) = Some W_152db0.
Proof. vm_refl. Qed.
Lemma D_152db0 : decode_any W_152db0 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152db4 : bv 32 := 0x0065c383.
Lemma F_152db4 : fetch_word Asan.M.loaded_segments (0x152df8 : word) = Some W_152db4.
Proof. vm_refl. Qed.
Lemma D_152db4 : decode_any W_152db4 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152db8 : bv 32 := 0x0075ce03.
Lemma F_152db8 : fetch_word Asan.M.loaded_segments (0x152dfc : word) = Some W_152db8.
Proof. vm_refl. Qed.
Lemma D_152db8 : decode_any W_152db8 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152dbc : bv 32 := 0x00858593.
Lemma F_152dbc : fetch_word Asan.M.loaded_segments (0x152e00 : word) = Some W_152dbc.
Proof. vm_refl. Qed.
Lemma D_152dbc : decode_any W_152dbc = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152dc0 : bv 32 := 0x00e68023.
Lemma F_152dc0 : fetch_word Asan.M.loaded_segments (0x152e04 : word) = Some W_152dc0.
Proof. vm_refl. Qed.
Lemma D_152dc0 : decode_any W_152dc0 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152dc4 : bv 32 := 0x00f680a3.
Lemma F_152dc4 : fetch_word Asan.M.loaded_segments (0x152e08 : word) = Some W_152dc4.
Proof. vm_refl. Qed.
Lemma D_152dc4 : decode_any W_152dc4 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152dc8 : bv 32 := 0x01068123.
Lemma F_152dc8 : fetch_word Asan.M.loaded_segments (0x152e0c : word) = Some W_152dc8.
Proof. vm_refl. Qed.
Lemma D_152dc8 : decode_any W_152dc8 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152dcc : bv 32 := 0x011681a3.
Lemma F_152dcc : fetch_word Asan.M.loaded_segments (0x152e10 : word) = Some W_152dcc.
Proof. vm_refl. Qed.
Lemma D_152dcc : decode_any W_152dcc = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152dd0 : bv 32 := 0x00868713.
Lemma F_152dd0 : fetch_word Asan.M.loaded_segments (0x152e14 : word) = Some W_152dd0.
Proof. vm_refl. Qed.
Lemma D_152dd0 : decode_any W_152dd0 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152dd4 : bv 32 := 0x00568223.
Lemma F_152dd4 : fetch_word Asan.M.loaded_segments (0x152e18 : word) = Some W_152dd4.
Proof. vm_refl. Qed.
Lemma D_152dd4 : decode_any W_152dd4 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152dd8 : bv 32 := 0x006682a3.
Lemma F_152dd8 : fetch_word Asan.M.loaded_segments (0x152e1c : word) = Some W_152dd8.
Proof. vm_refl. Qed.
Lemma D_152dd8 : decode_any W_152dd8 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ddc : bv 32 := 0x00768323.
Lemma F_152ddc : fetch_word Asan.M.loaded_segments (0x152e20 : word) = Some W_152ddc.
Proof. vm_refl. Qed.
Lemma D_152ddc : decode_any W_152ddc = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152de0 : bv 32 := 0x01c683a3.
Lemma F_152de0 : fetch_word Asan.M.loaded_segments (0x152e24 : word) = Some W_152de0.
Proof. vm_refl. Qed.
Lemma D_152de0 : decode_any W_152de0 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152de4 : bv 32 := 0x00070693.
Lemma F_152de4 : fetch_word Asan.M.loaded_segments (0x152e28 : word) = Some W_152de4.
Proof. vm_refl. Qed.
Lemma D_152de4 : decode_any W_152de4 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152de8 : bv 32 := 0x00467713.
Lemma F_152de8 : fetch_word Asan.M.loaded_segments (0x152e2c : word) = Some W_152de8.
Proof. vm_refl. Qed.
Lemma D_152de8 : decode_any W_152de8 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152dec : bv 32 := 0x02070863.
Lemma F_152dec : fetch_word Asan.M.loaded_segments (0x152e30 : word) = Some W_152dec.
Proof. vm_refl. Qed.
Lemma D_152dec : decode_any W_152dec = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152df0 : bv 32 := 0x0005c703.
Lemma F_152df0 : fetch_word Asan.M.loaded_segments (0x152e34 : word) = Some W_152df0.
Proof. vm_refl. Qed.
Lemma D_152df0 : decode_any W_152df0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152df4 : bv 32 := 0x0015c783.
Lemma F_152df4 : fetch_word Asan.M.loaded_segments (0x152e38 : word) = Some W_152df4.
Proof. vm_refl. Qed.
Lemma D_152df4 : decode_any W_152df4 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152df8 : bv 32 := 0x0025c803.
Lemma F_152df8 : fetch_word Asan.M.loaded_segments (0x152e3c : word) = Some W_152df8.
Proof. vm_refl. Qed.
Lemma D_152df8 : decode_any W_152df8 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152dfc : bv 32 := 0x0035c883.
Lemma F_152dfc : fetch_word Asan.M.loaded_segments (0x152e40 : word) = Some W_152dfc.
Proof. vm_refl. Qed.
Lemma D_152dfc : decode_any W_152dfc = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e00 : bv 32 := 0x00458593.
Lemma F_152e00 : fetch_word Asan.M.loaded_segments (0x152e44 : word) = Some W_152e00.
Proof. vm_refl. Qed.
Lemma D_152e00 : decode_any W_152e00 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e04 : bv 32 := 0x00468293.
Lemma F_152e04 : fetch_word Asan.M.loaded_segments (0x152e48 : word) = Some W_152e04.
Proof. vm_refl. Qed.
Lemma D_152e04 : decode_any W_152e04 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e08 : bv 32 := 0x00e68023.
Lemma F_152e08 : fetch_word Asan.M.loaded_segments (0x152e4c : word) = Some W_152e08.
Proof. vm_refl. Qed.
Lemma D_152e08 : decode_any W_152e08 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e0c : bv 32 := 0x00f680a3.
Lemma F_152e0c : fetch_word Asan.M.loaded_segments (0x152e50 : word) = Some W_152e0c.
Proof. vm_refl. Qed.
Lemma D_152e0c : decode_any W_152e0c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e10 : bv 32 := 0x01068123.
Lemma F_152e10 : fetch_word Asan.M.loaded_segments (0x152e54 : word) = Some W_152e10.
Proof. vm_refl. Qed.
Lemma D_152e10 : decode_any W_152e10 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e14 : bv 32 := 0x011681a3.
Lemma F_152e14 : fetch_word Asan.M.loaded_segments (0x152e58 : word) = Some W_152e14.
Proof. vm_refl. Qed.
Lemma D_152e14 : decode_any W_152e14 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e18 : bv 32 := 0x00028693.
Lemma F_152e18 : fetch_word Asan.M.loaded_segments (0x152e5c : word) = Some W_152e18.
Proof. vm_refl. Qed.
Lemma D_152e18 : decode_any W_152e18 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e1c : bv 32 := 0x00267713.
Lemma F_152e1c : fetch_word Asan.M.loaded_segments (0x152e60 : word) = Some W_152e1c.
Proof. vm_refl. Qed.
Lemma D_152e1c : decode_any W_152e1c = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e20 : bv 32 := 0x00071863.
Lemma F_152e20 : fetch_word Asan.M.loaded_segments (0x152e64 : word) = Some W_152e20.
Proof. vm_refl. Qed.
Lemma D_152e20 : decode_any W_152e20 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e24 : bv 32 := 0x00167613.
Lemma F_152e24 : fetch_word Asan.M.loaded_segments (0x152e68 : word) = Some W_152e24.
Proof. vm_refl. Qed.
Lemma D_152e24 : decode_any W_152e24 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e28 : bv 32 := 0x02061663.
Lemma F_152e28 : fetch_word Asan.M.loaded_segments (0x152e6c : word) = Some W_152e28.
Proof. vm_refl. Qed.
Lemma D_152e28 : decode_any W_152e28 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e2c : bv 32 := 0x00008067.
Lemma F_152e2c : fetch_word Asan.M.loaded_segments (0x152e70 : word) = Some W_152e2c.
Proof. vm_refl. Qed.
Lemma D_152e2c : decode_any W_152e2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e30 : bv 32 := 0x0005c703.
Lemma F_152e30 : fetch_word Asan.M.loaded_segments (0x152e74 : word) = Some W_152e30.
Proof. vm_refl. Qed.
Lemma D_152e30 : decode_any W_152e30 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e34 : bv 32 := 0x0015c783.
Lemma F_152e34 : fetch_word Asan.M.loaded_segments (0x152e78 : word) = Some W_152e34.
Proof. vm_refl. Qed.
Lemma D_152e34 : decode_any W_152e34 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e38 : bv 32 := 0x00258593.
Lemma F_152e38 : fetch_word Asan.M.loaded_segments (0x152e7c : word) = Some W_152e38.
Proof. vm_refl. Qed.
Lemma D_152e38 : decode_any W_152e38 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e3c : bv 32 := 0x00268813.
Lemma F_152e3c : fetch_word Asan.M.loaded_segments (0x152e80 : word) = Some W_152e3c.
Proof. vm_refl. Qed.
Lemma D_152e3c : decode_any W_152e3c = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e40 : bv 32 := 0x00e68023.
Lemma F_152e40 : fetch_word Asan.M.loaded_segments (0x152e84 : word) = Some W_152e40.
Proof. vm_refl. Qed.
Lemma D_152e40 : decode_any W_152e40 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e44 : bv 32 := 0x00f680a3.
Lemma F_152e44 : fetch_word Asan.M.loaded_segments (0x152e88 : word) = Some W_152e44.
Proof. vm_refl. Qed.
Lemma D_152e44 : decode_any W_152e44 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e48 : bv 32 := 0x00080693.
Lemma F_152e48 : fetch_word Asan.M.loaded_segments (0x152e8c : word) = Some W_152e48.
Proof. vm_refl. Qed.
Lemma D_152e48 : decode_any W_152e48 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e4c : bv 32 := 0x00167613.
Lemma F_152e4c : fetch_word Asan.M.loaded_segments (0x152e90 : word) = Some W_152e4c.
Proof. vm_refl. Qed.
Lemma D_152e4c : decode_any W_152e4c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e50 : bv 32 := 0xfc060ee3.
Lemma F_152e50 : fetch_word Asan.M.loaded_segments (0x152e94 : word) = Some W_152e50.
Proof. vm_refl. Qed.
Lemma D_152e50 : decode_any W_152e50 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e54 : bv 32 := 0x0005c583.
Lemma F_152e54 : fetch_word Asan.M.loaded_segments (0x152e98 : word) = Some W_152e54.
Proof. vm_refl. Qed.
Lemma D_152e54 : decode_any W_152e54 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e58 : bv 32 := 0x00b68023.
Lemma F_152e58 : fetch_word Asan.M.loaded_segments (0x152e9c : word) = Some W_152e58.
Proof. vm_refl. Qed.
Lemma D_152e58 : decode_any W_152e58 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e5c : bv 32 := 0x00008067.
Lemma F_152e5c : fetch_word Asan.M.loaded_segments (0x152ea0 : word) = Some W_152e5c.
Proof. vm_refl. Qed.
Lemma D_152e5c : decode_any W_152e5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e60 : bv 32 := 0x0e060a63.
Lemma F_152e60 : fetch_word Asan.M.loaded_segments (0x152ea4 : word) = Some W_152e60.
Proof. vm_refl. Qed.
Lemma D_152e60 : decode_any W_152e60 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e64 : bv 32 := 0x00b50023.
Lemma F_152e64 : fetch_word Asan.M.loaded_segments (0x152ea8 : word) = Some W_152e64.
Proof. vm_refl. Qed.
Lemma D_152e64 : decode_any W_152e64 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e68 : bv 32 := 0x00c506b3.
Lemma F_152e68 : fetch_word Asan.M.loaded_segments (0x152eac : word) = Some W_152e68.
Proof. vm_refl. Qed.
Lemma D_152e68 : decode_any W_152e68 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e6c : bv 32 := 0x00300713.
Lemma F_152e6c : fetch_word Asan.M.loaded_segments (0x152eb0 : word) = Some W_152e6c.
Proof. vm_refl. Qed.
Lemma D_152e6c : decode_any W_152e6c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e70 : bv 32 := 0xfeb68fa3.
Lemma F_152e70 : fetch_word Asan.M.loaded_segments (0x152eb4 : word) = Some W_152e70.
Proof. vm_refl. Qed.
Lemma D_152e70 : decode_any W_152e70 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e74 : bv 32 := 0x0ee66063.
Lemma F_152e74 : fetch_word Asan.M.loaded_segments (0x152eb8 : word) = Some W_152e74.
Proof. vm_refl. Qed.
Lemma D_152e74 : decode_any W_152e74 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e78 : bv 32 := 0x00b500a3.
Lemma F_152e78 : fetch_word Asan.M.loaded_segments (0x152ebc : word) = Some W_152e78.
Proof. vm_refl. Qed.
Lemma D_152e78 : decode_any W_152e78 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e7c : bv 32 := 0x00b50123.
Lemma F_152e7c : fetch_word Asan.M.loaded_segments (0x152ec0 : word) = Some W_152e7c.
Proof. vm_refl. Qed.
Lemma D_152e7c : decode_any W_152e7c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e80 : bv 32 := 0x00700713.
Lemma F_152e80 : fetch_word Asan.M.loaded_segments (0x152ec4 : word) = Some W_152e80.
Proof. vm_refl. Qed.
Lemma D_152e80 : decode_any W_152e80 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e84 : bv 32 := 0xfeb68ea3.
Lemma F_152e84 : fetch_word Asan.M.loaded_segments (0x152ec8 : word) = Some W_152e84.
Proof. vm_refl. Qed.
Lemma D_152e84 : decode_any W_152e84 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e88 : bv 32 := 0xfeb68f23.
Lemma F_152e88 : fetch_word Asan.M.loaded_segments (0x152ecc : word) = Some W_152e88.
Proof. vm_refl. Qed.
Lemma D_152e88 : decode_any W_152e88 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e8c : bv 32 := 0x0ce66463.
Lemma F_152e8c : fetch_word Asan.M.loaded_segments (0x152ed0 : word) = Some W_152e8c.
Proof. vm_refl. Qed.
Lemma D_152e8c : decode_any W_152e8c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e90 : bv 32 := 0x00b501a3.
Lemma F_152e90 : fetch_word Asan.M.loaded_segments (0x152ed4 : word) = Some W_152e90.
Proof. vm_refl. Qed.
Lemma D_152e90 : decode_any W_152e90 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e94 : bv 32 := 0x00900793.
Lemma F_152e94 : fetch_word Asan.M.loaded_segments (0x152ed8 : word) = Some W_152e94.
Proof. vm_refl. Qed.
Lemma D_152e94 : decode_any W_152e94 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e98 : bv 32 := 0xfeb68e23.
Lemma F_152e98 : fetch_word Asan.M.loaded_segments (0x152edc : word) = Some W_152e98.
Proof. vm_refl. Qed.
Lemma D_152e98 : decode_any W_152e98 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152e9c : bv 32 := 0x0af66c63.
Lemma F_152e9c : fetch_word Asan.M.loaded_segments (0x152ee0 : word) = Some W_152e9c.
Proof. vm_refl. Qed.
Lemma D_152e9c : decode_any W_152e9c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ea0 : bv 32 := 0x40a006bb.
Lemma F_152ea0 : fetch_word Asan.M.loaded_segments (0x152ee4 : word) = Some W_152ea0.
Proof. vm_refl. Qed.
Lemma D_152ea0 : decode_any W_152ea0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ea4 : bv 32 := 0x03859813.
Lemma F_152ea4 : fetch_word Asan.M.loaded_segments (0x152ee8 : word) = Some W_152ea4.
Proof. vm_refl. Qed.
Lemma D_152ea4 : decode_any W_152ea4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ea8 : bv 32 := 0x101015b7.
Lemma F_152ea8 : fetch_word Asan.M.loaded_segments (0x152eec : word) = Some W_152ea8.
Proof. vm_refl. Qed.
Lemma D_152ea8 : decode_any W_152ea8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152eac : bv 32 := 0x0036f693.
Lemma F_152eac : fetch_word Asan.M.loaded_segments (0x152ef0 : word) = Some W_152eac.
Proof. vm_refl. Qed.
Lemma D_152eac : decode_any W_152eac = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152eb0 : bv 32 := 0x00459713.
Lemma F_152eb0 : fetch_word Asan.M.loaded_segments (0x152ef4 : word) = Some W_152eb0.
Proof. vm_refl. Qed.
Lemma D_152eb0 : decode_any W_152eb0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152eb4 : bv 32 := 0x40d60633.
Lemma F_152eb4 : fetch_word Asan.M.loaded_segments (0x152ef8 : word) = Some W_152eb4.
Proof. vm_refl. Qed.
Lemma D_152eb4 : decode_any W_152eb4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152eb8 : bv 32 := 0x00d505b3.
Lemma F_152eb8 : fetch_word Asan.M.loaded_segments (0x152efc : word) = Some W_152eb8.
Proof. vm_refl. Qed.
Lemma D_152eb8 : decode_any W_152eb8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ebc : bv 32 := 0x10070693.
Lemma F_152ebc : fetch_word Asan.M.loaded_segments (0x152f00 : word) = Some W_152ebc.
Proof. vm_refl. Qed.
Lemma D_152ebc : decode_any W_152ebc = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ec0 : bv 32 := 0xffc67713.
Lemma F_152ec0 : fetch_word Asan.M.loaded_segments (0x152f04 : word) = Some W_152ec0.
Proof. vm_refl. Qed.
Lemma D_152ec0 : decode_any W_152ec0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ec4 : bv 32 := 0x02d83633.
Lemma F_152ec4 : fetch_word Asan.M.loaded_segments (0x152f08 : word) = Some W_152ec4.
Proof. vm_refl. Qed.
Lemma D_152ec4 : decode_any W_152ec4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ec8 : bv 32 := 0x00c5a023.
Lemma F_152ec8 : fetch_word Asan.M.loaded_segments (0x152f0c : word) = Some W_152ec8.
Proof. vm_refl. Qed.
Lemma D_152ec8 : decode_any W_152ec8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ecc : bv 32 := 0x00e586b3.
Lemma F_152ecc : fetch_word Asan.M.loaded_segments (0x152f10 : word) = Some W_152ecc.
Proof. vm_refl. Qed.
Lemma D_152ecc : decode_any W_152ecc = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ed0 : bv 32 := 0xfec6ae23.
Lemma F_152ed0 : fetch_word Asan.M.loaded_segments (0x152f14 : word) = Some W_152ed0.
Proof. vm_refl. Qed.
Lemma D_152ed0 : decode_any W_152ed0 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ed4 : bv 32 := 0x08f76063.
Lemma F_152ed4 : fetch_word Asan.M.loaded_segments (0x152f18 : word) = Some W_152ed4.
Proof. vm_refl. Qed.
Lemma D_152ed4 : decode_any W_152ed4 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ed8 : bv 32 := 0x00c5a223.
Lemma F_152ed8 : fetch_word Asan.M.loaded_segments (0x152f1c : word) = Some W_152ed8.
Proof. vm_refl. Qed.
Lemma D_152ed8 : decode_any W_152ed8 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152edc : bv 32 := 0x00c5a423.
Lemma F_152edc : fetch_word Asan.M.loaded_segments (0x152f20 : word) = Some W_152edc.
Proof. vm_refl. Qed.
Lemma D_152edc : decode_any W_152edc = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ee0 : bv 32 := 0x01900793.
Lemma F_152ee0 : fetch_word Asan.M.loaded_segments (0x152f24 : word) = Some W_152ee0.
Proof. vm_refl. Qed.
Lemma D_152ee0 : decode_any W_152ee0 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ee4 : bv 32 := 0xfec6aa23.
Lemma F_152ee4 : fetch_word Asan.M.loaded_segments (0x152f28 : word) = Some W_152ee4.
Proof. vm_refl. Qed.
Lemma D_152ee4 : decode_any W_152ee4 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ee8 : bv 32 := 0xfec6ac23.
Lemma F_152ee8 : fetch_word Asan.M.loaded_segments (0x152f2c : word) = Some W_152ee8.
Proof. vm_refl. Qed.
Lemma D_152ee8 : decode_any W_152ee8 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152eec : bv 32 := 0x06f76463.
Lemma F_152eec : fetch_word Asan.M.loaded_segments (0x152f30 : word) = Some W_152eec.
Proof. vm_refl. Qed.
Lemma D_152eec : decode_any W_152eec = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ef0 : bv 32 := 0x00c5a623.
Lemma F_152ef0 : fetch_word Asan.M.loaded_segments (0x152f34 : word) = Some W_152ef0.
Proof. vm_refl. Qed.
Lemma D_152ef0 : decode_any W_152ef0 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ef4 : bv 32 := 0x00c5a823.
Lemma F_152ef4 : fetch_word Asan.M.loaded_segments (0x152f38 : word) = Some W_152ef4.
Proof. vm_refl. Qed.
Lemma D_152ef4 : decode_any W_152ef4 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152ef8 : bv 32 := 0x00c5aa23.
Lemma F_152ef8 : fetch_word Asan.M.loaded_segments (0x152f3c : word) = Some W_152ef8.
Proof. vm_refl. Qed.
Lemma D_152ef8 : decode_any W_152ef8 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152efc : bv 32 := 0x00c5ac23.
Lemma F_152efc : fetch_word Asan.M.loaded_segments (0x152f40 : word) = Some W_152efc.
Proof. vm_refl. Qed.
Lemma D_152efc : decode_any W_152efc = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f00 : bv 32 := 0x0045f793.
Lemma F_152f00 : fetch_word Asan.M.loaded_segments (0x152f44 : word) = Some W_152f00.
Proof. vm_refl. Qed.
Lemma D_152f00 : decode_any W_152f00 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f04 : bv 32 := 0x02000813.
Lemma F_152f04 : fetch_word Asan.M.loaded_segments (0x152f48 : word) = Some W_152f04.
Proof. vm_refl. Qed.
Lemma D_152f04 : decode_any W_152f04 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f08 : bv 32 := 0x01878793.
Lemma F_152f08 : fetch_word Asan.M.loaded_segments (0x152f4c : word) = Some W_152f08.
Proof. vm_refl. Qed.
Lemma D_152f08 : decode_any W_152f08 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f0c : bv 32 := 0x40f70733.
Lemma F_152f0c : fetch_word Asan.M.loaded_segments (0x152f50 : word) = Some W_152f0c.
Proof. vm_refl. Qed.
Lemma D_152f0c : decode_any W_152f0c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f10 : bv 32 := 0xfec6a223.
Lemma F_152f10 : fetch_word Asan.M.loaded_segments (0x152f54 : word) = Some W_152f10.
Proof. vm_refl. Qed.
Lemma D_152f10 : decode_any W_152f10 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f14 : bv 32 := 0xfec6a423.
Lemma F_152f14 : fetch_word Asan.M.loaded_segments (0x152f58 : word) = Some W_152f14.
Proof. vm_refl. Qed.
Lemma D_152f14 : decode_any W_152f14 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f18 : bv 32 := 0xfec6a623.
Lemma F_152f18 : fetch_word Asan.M.loaded_segments (0x152f5c : word) = Some W_152f18.
Proof. vm_refl. Qed.
Lemma D_152f18 : decode_any W_152f18 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f1c : bv 32 := 0xfec6a823.
Lemma F_152f1c : fetch_word Asan.M.loaded_segments (0x152f60 : word) = Some W_152f1c.
Proof. vm_refl. Qed.
Lemma D_152f1c : decode_any W_152f1c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f20 : bv 32 := 0x03076a63.
Lemma F_152f20 : fetch_word Asan.M.loaded_segments (0x152f64 : word) = Some W_152f20.
Proof. vm_refl. Qed.
Lemma D_152f20 : decode_any W_152f20 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f24 : bv 32 := 0x02061613.
Lemma F_152f24 : fetch_word Asan.M.loaded_segments (0x152f68 : word) = Some W_152f24.
Proof. vm_refl. Qed.
Lemma D_152f24 : decode_any W_152f24 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f28 : bv 32 := 0x00f585b3.
Lemma F_152f28 : fetch_word Asan.M.loaded_segments (0x152f6c : word) = Some W_152f28.
Proof. vm_refl. Qed.
Lemma D_152f28 : decode_any W_152f28 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f2c : bv 32 := 0x02065693.
Lemma F_152f2c : fetch_word Asan.M.loaded_segments (0x152f70 : word) = Some W_152f2c.
Proof. vm_refl. Qed.
Lemma D_152f2c : decode_any W_152f2c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f30 : bv 32 := 0x00d66633.
Lemma F_152f30 : fetch_word Asan.M.loaded_segments (0x152f74 : word) = Some W_152f30.
Proof. vm_refl. Qed.
Lemma D_152f30 : decode_any W_152f30 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f34 : bv 32 := 0x01f00693.
Lemma F_152f34 : fetch_word Asan.M.loaded_segments (0x152f78 : word) = Some W_152f34.
Proof. vm_refl. Qed.
Lemma D_152f34 : decode_any W_152f34 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f38 : bv 32 := 0x00c5b023.
Lemma F_152f38 : fetch_word Asan.M.loaded_segments (0x152f7c : word) = Some W_152f38.
Proof. vm_refl. Qed.
Lemma D_152f38 : decode_any W_152f38 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f3c : bv 32 := 0x00c5b423.
Lemma F_152f3c : fetch_word Asan.M.loaded_segments (0x152f80 : word) = Some W_152f3c.
Proof. vm_refl. Qed.
Lemma D_152f3c : decode_any W_152f3c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f40 : bv 32 := 0x00c5b823.
Lemma F_152f40 : fetch_word Asan.M.loaded_segments (0x152f84 : word) = Some W_152f40.
Proof. vm_refl. Qed.
Lemma D_152f40 : decode_any W_152f40 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f44 : bv 32 := 0x00c5bc23.
Lemma F_152f44 : fetch_word Asan.M.loaded_segments (0x152f88 : word) = Some W_152f44.
Proof. vm_refl. Qed.
Lemma D_152f44 : decode_any W_152f44 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f48 : bv 32 := 0xfe070713.
Lemma F_152f48 : fetch_word Asan.M.loaded_segments (0x152f8c : word) = Some W_152f48.
Proof. vm_refl. Qed.
Lemma D_152f48 : decode_any W_152f48 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f4c : bv 32 := 0x02058593.
Lemma F_152f4c : fetch_word Asan.M.loaded_segments (0x152f90 : word) = Some W_152f4c.
Proof. vm_refl. Qed.
Lemma D_152f4c : decode_any W_152f4c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f50 : bv 32 := 0xfee6e4e3.
Lemma F_152f50 : fetch_word Asan.M.loaded_segments (0x152f94 : word) = Some W_152f50.
Proof. vm_refl. Qed.
Lemma D_152f50 : decode_any W_152f50 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_152f54 : bv 32 := 0x00008067.
Lemma F_152f54 : fetch_word Asan.M.loaded_segments (0x152f98 : word) = Some W_152f54.
Proof. vm_refl. Qed.
Lemma D_152f54 : decode_any W_152f54 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

