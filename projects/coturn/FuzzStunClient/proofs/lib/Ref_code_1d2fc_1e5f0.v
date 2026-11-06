(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.


(* [comment removed for export] *)
Definition W_1d374 : bv 32 := 0x02053703.
Lemma F_1d374 : fetch_word Plain.M.loaded_segments (0x1d374 : word) = Some W_1d374.
Proof. vm_refl. Qed.
Lemma D_1d374 : decode_any W_1d374 = Some (Load SZ8 true 14 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d378 : bv 32 := 0x00c75793.
Lemma F_1d378 : fetch_word Plain.M.loaded_segments (0x1d378 : word) = Some W_1d378.
Proof. vm_refl. Qed.
Lemma D_1d378 : decode_any W_1d378 = Some (ShiftImm ALU_SRL 15 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d37c : bv 32 := 0x00078e63.
Lemma F_1d37c : fetch_word Plain.M.loaded_segments (0x1d37c : word) = Some W_1d37c.
Proof. vm_refl. Qed.
Lemma D_1d37c : decode_any W_1d37c = Some (Branch BC_EQ 15 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d380 : bv 32 := 0x01f77793.
Lemma F_1d380 : fetch_word Plain.M.loaded_segments (0x1d380 : word) = Some W_1d380.
Proof. vm_refl. Qed.
Lemma D_1d380 : decode_any W_1d380 = Some (OpImm ALU_AND 15 14 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d384 : bv 32 := 0x00079a63.
Lemma F_1d384 : fetch_word Plain.M.loaded_segments (0x1d384 : word) = Some W_1d384.
Proof. vm_refl. Qed.
Lemma D_1d384 : decode_any W_1d384 = Some (Branch BC_NE 15 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d388 : bv 32 := 0xfffff7b7.
Lemma F_1d388 : fetch_word Plain.M.loaded_segments (0x1d388 : word) = Some W_1d388.
Proof. vm_refl. Qed.
Lemma D_1d388 : decode_any W_1d388 = Some (Lui 15 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d38c : bv 32 := 0x00f77733.
Lemma F_1d38c : fetch_word Plain.M.loaded_segments (0x1d38c : word) = Some W_1d38c.
Proof. vm_refl. Qed.
Lemma D_1d38c : decode_any W_1d38c = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d390 : bv 32 := 0xff070713.
Lemma F_1d390 : fetch_word Plain.M.loaded_segments (0x1d390 : word) = Some W_1d390.
Proof. vm_refl. Qed.
Lemma D_1d390 : decode_any W_1d390 = Some (OpImm ALU_ADD 14 14 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d394 : bv 32 := 0x0200006f.
Lemma F_1d394 : fetch_word Plain.M.loaded_segments (0x1d394 : word) = Some W_1d394.
Proof. vm_refl. Qed.
Lemma D_1d394 : decode_any W_1d394 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d398 : bv 32 := 0x00575713.
Lemma F_1d398 : fetch_word Plain.M.loaded_segments (0x1d398 : word) = Some W_1d398.
Proof. vm_refl. Qed.
Lemma D_1d398 : decode_any W_1d398 = Some (ShiftImm ALU_SRL 14 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d39c : bv 32 := 0xffff4797.
Lemma F_1d39c : fetch_word Plain.M.loaded_segments (0x1d39c : word) = Some W_1d39c.
Proof. vm_refl. Qed.
Lemma D_1d39c : decode_any W_1d39c = Some (Auipc 15 1048564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3a0 : bv 32 := 0x07e77713.
Lemma F_1d3a0 : fetch_word Plain.M.loaded_segments (0x1d3a0 : word) = Some W_1d3a0.
Proof. vm_refl. Qed.
Lemma D_1d3a0 : decode_any W_1d3a0 = Some (OpImm ALU_AND 14 14 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3a4 : bv 32 := 0xd2478793.
Lemma F_1d3a4 : fetch_word Plain.M.loaded_segments (0x1d3a4 : word) = Some W_1d3a4.
Proof. vm_refl. Qed.
Lemma D_1d3a4 : decode_any W_1d3a4 = Some (OpImm ALU_ADD 15 15 3364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3a8 : bv 32 := 0x00e78733.
Lemma F_1d3a8 : fetch_word Plain.M.loaded_segments (0x1d3a8 : word) = Some W_1d3a8.
Proof. vm_refl. Qed.
Lemma D_1d3a8 : decode_any W_1d3a8 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3ac : bv 32 := 0x00075703.
Lemma F_1d3ac : fetch_word Plain.M.loaded_segments (0x1d3ac : word) = Some W_1d3ac.
Proof. vm_refl. Qed.
Lemma D_1d3ac : decode_any W_1d3ac = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3b0 : bv 32 := 0x00471713.
Lemma F_1d3b0 : fetch_word Plain.M.loaded_segments (0x1d3b0 : word) = Some W_1d3b0.
Proof. vm_refl. Qed.
Lemma D_1d3b0 : decode_any W_1d3b0 = Some (ShiftImm ALU_SLL 14 14 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3b4 : bv 32 := 0x01053803.
Lemma F_1d3b4 : fetch_word Plain.M.loaded_segments (0x1d3b4 : word) = Some W_1d3b4.
Proof. vm_refl. Qed.
Lemma D_1d3b4 : decode_any W_1d3b4 = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3b8 : bv 32 := 0x02b707b3.
Lemma F_1d3b8 : fetch_word Plain.M.loaded_segments (0x1d3b8 : word) = Some W_1d3b8.
Proof. vm_refl. Qed.
Lemma D_1d3b8 : decode_any W_1d3b8 = Some (Mul M_MUL 15 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3bc : bv 32 := 0x00f807b3.
Lemma F_1d3bc : fetch_word Plain.M.loaded_segments (0x1d3bc : word) = Some W_1d3bc.
Proof. vm_refl. Qed.
Lemma D_1d3bc : decode_any W_1d3bc = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3c0 : bv 32 := 0x00d7c883.
Lemma F_1d3c0 : fetch_word Plain.M.loaded_segments (0x1d3c0 : word) = Some W_1d3c0.
Proof. vm_refl. Qed.
Lemma D_1d3c0 : decode_any W_1d3c0 = Some (Load SZ1 false 17 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3c4 : bv 32 := 0x40c702b3.
Lemma F_1d3c4 : fetch_word Plain.M.loaded_segments (0x1d3c4 : word) = Some W_1d3c4.
Proof. vm_refl. Qed.
Lemma D_1d3c4 : decode_any W_1d3c4 = Some (Op ALU_SUB 5 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3c8 : bv 32 := 0xffc28293.
Lemma F_1d3c8 : fetch_word Plain.M.loaded_segments (0x1d3c8 : word) = Some W_1d3c8.
Proof. vm_refl. Qed.
Lemma D_1d3c8 : decode_any W_1d3c8 = Some (OpImm ALU_ADD 5 5 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3cc : bv 32 := 0x01078793.
Lemma F_1d3cc : fetch_word Plain.M.loaded_segments (0x1d3cc : word) = Some W_1d3cc.
Proof. vm_refl. Qed.
Lemma D_1d3cc : decode_any W_1d3cc = Some (OpImm ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3d0 : bv 32 := 0x00088663.
Lemma F_1d3d0 : fetch_word Plain.M.loaded_segments (0x1d3d0 : word) = Some W_1d3d0.
Proof. vm_refl. Qed.
Lemma D_1d3d0 : decode_any W_1d3d0 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3d4 : bv 32 := 0xffe7d683.
Lemma F_1d3d4 : fetch_word Plain.M.loaded_segments (0x1d3d4 : word) = Some W_1d3d4.
Proof. vm_refl. Qed.
Lemma D_1d3d4 : decode_any W_1d3d4 = Some (Load SZ2 false 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3d8 : bv 32 := 0x00168693.
Lemma F_1d3d8 : fetch_word Plain.M.loaded_segments (0x1d3d8 : word) = Some W_1d3d8.
Proof. vm_refl. Qed.
Lemma D_1d3d8 : decode_any W_1d3d8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3dc : bv 32 := 0xffc7c383.
Lemma F_1d3dc : fetch_word Plain.M.loaded_segments (0x1d3dc : word) = Some W_1d3dc.
Proof. vm_refl. Qed.
Lemma D_1d3dc : decode_any W_1d3dc = Some (Load SZ1 false 7 15 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3e0 : bv 32 := 0x0042d313.
Lemma F_1d3e0 : fetch_word Plain.M.loaded_segments (0x1d3e0 : word) = Some W_1d3e0.
Proof. vm_refl. Qed.
Lemma D_1d3e0 : decode_any W_1d3e0 = Some (ShiftImm ALU_SRL 6 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3e4 : bv 32 := 0x0ff6f893.
Lemma F_1d3e4 : fetch_word Plain.M.loaded_segments (0x1d3e4 : word) = Some W_1d3e4.
Proof. vm_refl. Qed.
Lemma D_1d3e4 : decode_any W_1d3e4 = Some (OpImm ALU_AND 17 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3e8 : bv 32 := 0x00038463.
Lemma F_1d3e8 : fetch_word Plain.M.loaded_segments (0x1d3e8 : word) = Some W_1d3e8.
Proof. vm_refl. Qed.
Lemma D_1d3e8 : decode_any W_1d3e8 = Some (Branch BC_EQ 7 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3f0 : bv 32 := 0x03137e63.
Lemma F_1d3f0 : fetch_word Plain.M.loaded_segments (0x1d3f0 : word) = Some W_1d3f0.
Proof. vm_refl. Qed.
Lemma D_1d3f0 : decode_any W_1d3f0 = Some (Branch BC_GEU 6 17 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3f4 : bv 32 := 0x0052d693.
Lemma F_1d3f4 : fetch_word Plain.M.loaded_segments (0x1d3f4 : word) = Some W_1d3f4.
Proof. vm_refl. Qed.
Lemma D_1d3f4 : decode_any W_1d3f4 = Some (ShiftImm ALU_SRL 13 5 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3f8 : bv 32 := 0x00d366b3.
Lemma F_1d3f8 : fetch_word Plain.M.loaded_segments (0x1d3f8 : word) = Some W_1d3f8.
Proof. vm_refl. Qed.
Lemma D_1d3f8 : decode_any W_1d3f8 = Some (Op ALU_OR 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d3fc : bv 32 := 0x0026d293.
Lemma F_1d3fc : fetch_word Plain.M.loaded_segments (0x1d3fc : word) = Some W_1d3fc.
Proof. vm_refl. Qed.
Lemma D_1d3fc : decode_any W_1d3fc = Some (ShiftImm ALU_SRL 5 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d400 : bv 32 := 0x00d2e6b3.
Lemma F_1d400 : fetch_word Plain.M.loaded_segments (0x1d400 : word) = Some W_1d400.
Proof. vm_refl. Qed.
Lemma D_1d400 : decode_any W_1d400 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d404 : bv 32 := 0x0046d293.
Lemma F_1d404 : fetch_word Plain.M.loaded_segments (0x1d404 : word) = Some W_1d404.
Proof. vm_refl. Qed.
Lemma D_1d404 : decode_any W_1d404 = Some (ShiftImm ALU_SRL 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d408 : bv 32 := 0x00d2e6b3.
Lemma F_1d408 : fetch_word Plain.M.loaded_segments (0x1d408 : word) = Some W_1d408.
Proof. vm_refl. Qed.
Lemma D_1d408 : decode_any W_1d408 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d40c : bv 32 := 0x00d8f6b3.
Lemma F_1d40c : fetch_word Plain.M.loaded_segments (0x1d40c : word) = Some W_1d40c.
Proof. vm_refl. Qed.
Lemma D_1d40c : decode_any W_1d40c = Some (Op ALU_AND 13 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d410 : bv 32 := 0x00d338b3.
Lemma F_1d410 : fetch_word Plain.M.loaded_segments (0x1d410 : word) = Some W_1d410.
Proof. vm_refl. Qed.
Lemma D_1d410 : decode_any W_1d410 = Some (Op ALU_SLTU 17 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d414 : bv 32 := 0xfff34293.
Lemma F_1d414 : fetch_word Plain.M.loaded_segments (0x1d414 : word) = Some W_1d414.
Proof. vm_refl. Qed.
Lemma D_1d414 : decode_any W_1d414 = Some (OpImm ALU_XOR 5 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d418 : bv 32 := 0x411008bb.
Lemma F_1d418 : fetch_word Plain.M.loaded_segments (0x1d418 : word) = Some W_1d418.
Proof. vm_refl. Qed.
Lemma D_1d418 : decode_any W_1d418 = Some (Op32 ALU_SUB 17 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d41c : bv 32 := 0x0058f8b3.
Lemma F_1d41c : fetch_word Plain.M.loaded_segments (0x1d41c : word) = Some W_1d41c.
Proof. vm_refl. Qed.
Lemma D_1d41c : decode_any W_1d41c = Some (Op ALU_AND 17 17 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d420 : bv 32 := 0x00d888bb.
Lemma F_1d420 : fetch_word Plain.M.loaded_segments (0x1d420 : word) = Some W_1d420.
Proof. vm_refl. Qed.
Lemma D_1d420 : decode_any W_1d420 = Some (Op32 ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d424 : bv 32 := 0x01137463.
Lemma F_1d424 : fetch_word Plain.M.loaded_segments (0x1d424 : word) = Some W_1d424.
Proof. vm_refl. Qed.
Lemma D_1d424 : decode_any W_1d424 = Some (Branch BC_GEU 6 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d42c : bv 32 := 0x00078693.
Lemma F_1d42c : fetch_word Plain.M.loaded_segments (0x1d42c : word) = Some W_1d42c.
Proof. vm_refl. Qed.
Lemma D_1d42c : decode_any W_1d42c = Some (OpImm ALU_ADD 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d430 : bv 32 := 0x02088063.
Lemma F_1d430 : fetch_word Plain.M.loaded_segments (0x1d430 : word) = Some W_1d430.
Proof. vm_refl. Qed.
Lemma D_1d430 : decode_any W_1d430 = Some (Branch BC_EQ 17 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d434 : bv 32 := 0xfe000813.
Lemma F_1d434 : fetch_word Plain.M.loaded_segments (0x1d434 : word) = Some W_1d434.
Proof. vm_refl. Qed.
Lemma D_1d434 : decode_any W_1d434 = Some (OpImm ALU_ADD 16 0 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d438 : bv 32 := 0x0048969b.
Lemma F_1d438 : fetch_word Plain.M.loaded_segments (0x1d438 : word) = Some W_1d438.
Proof. vm_refl. Qed.
Lemma D_1d438 : decode_any W_1d438 = Some (ShiftImm32 ALU_SLL 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d43c : bv 32 := 0x00d786b3.
Lemma F_1d43c : fetch_word Plain.M.loaded_segments (0x1d43c : word) = Some W_1d43c.
Proof. vm_refl. Qed.
Lemma D_1d43c : decode_any W_1d43c = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d440 : bv 32 := 0xff078ea3.
Lemma F_1d440 : fetch_word Plain.M.loaded_segments (0x1d440 : word) = Some W_1d440.
Proof. vm_refl. Qed.
Lemma D_1d440 : decode_any W_1d440 = Some (Store SZ1 15 16 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d444 : bv 32 := 0xff179f23.
Lemma F_1d444 : fetch_word Plain.M.loaded_segments (0x1d444 : word) = Some W_1d444.
Proof. vm_refl. Qed.
Lemma D_1d444 : decode_any W_1d444 = Some (Store SZ2 15 17 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d448 : bv 32 := 0xfe068e23.
Lemma F_1d448 : fetch_word Plain.M.loaded_segments (0x1d448 : word) = Some W_1d448.
Proof. vm_refl. Qed.
Lemma D_1d448 : decode_any W_1d448 = Some (Store SZ1 13 0 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d44c : bv 32 := 0x01053803.
Lemma F_1d44c : fetch_word Plain.M.loaded_segments (0x1d44c : word) = Some W_1d44c.
Proof. vm_refl. Qed.
Lemma D_1d44c : decode_any W_1d44c = Some (Load SZ8 true 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d450 : bv 32 := 0x00e78733.
Lemma F_1d450 : fetch_word Plain.M.loaded_segments (0x1d450 : word) = Some W_1d450.
Proof. vm_refl. Qed.
Lemma D_1d450 : decode_any W_1d450 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d454 : bv 32 := 0x410687bb.
Lemma F_1d454 : fetch_word Plain.M.loaded_segments (0x1d454 : word) = Some W_1d454.
Proof. vm_refl. Qed.
Lemma D_1d454 : decode_any W_1d454 = Some (Op32 ALU_SUB 15 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d458 : bv 32 := 0x00d60633.
Lemma F_1d458 : fetch_word Plain.M.loaded_segments (0x1d458 : word) = Some W_1d458.
Proof. vm_refl. Qed.
Lemma D_1d458 : decode_any W_1d458 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d45c : bv 32 := 0xffc70513.
Lemma F_1d45c : fetch_word Plain.M.loaded_segments (0x1d45c : word) = Some W_1d45c.
Proof. vm_refl. Qed.
Lemma D_1d45c : decode_any W_1d45c = Some (OpImm ALU_ADD 10 14 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d460 : bv 32 := 0xff078793.
Lemma F_1d460 : fetch_word Plain.M.loaded_segments (0x1d460 : word) = Some W_1d460.
Proof. vm_refl. Qed.
Lemma D_1d460 : decode_any W_1d460 = Some (OpImm ALU_ADD 15 15 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d464 : bv 32 := 0x0047d793.
Lemma F_1d464 : fetch_word Plain.M.loaded_segments (0x1d464 : word) = Some W_1d464.
Proof. vm_refl. Qed.
Lemma D_1d464 : decode_any W_1d464 = Some (ShiftImm ALU_SRL 15 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d468 : bv 32 := 0x40c5083b.
Lemma F_1d468 : fetch_word Plain.M.loaded_segments (0x1d468 : word) = Some W_1d468.
Proof. vm_refl. Qed.
Lemma D_1d468 : decode_any W_1d468 = Some (Op32 ALU_SUB 16 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d46c : bv 32 := 0xfeb68ea3.
Lemma F_1d46c : fetch_word Plain.M.loaded_segments (0x1d46c : word) = Some W_1d46c.
Proof. vm_refl. Qed.
Lemma D_1d46c : decode_any W_1d46c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d470 : bv 32 := 0xfef69f23.
Lemma F_1d470 : fetch_word Plain.M.loaded_segments (0x1d470 : word) = Some W_1d470.
Proof. vm_refl. Qed.
Lemma D_1d470 : decode_any W_1d470 = Some (Store SZ2 13 15 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d474 : bv 32 := 0x02080463.
Lemma F_1d474 : fetch_word Plain.M.loaded_segments (0x1d474 : word) = Some W_1d474.
Proof. vm_refl. Qed.
Lemma D_1d474 : decode_any W_1d474 = Some (Branch BC_EQ 16 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d478 : bv 32 := 0x40c505bb.
Lemma F_1d478 : fetch_word Plain.M.loaded_segments (0x1d478 : word) = Some W_1d478.
Proof. vm_refl. Qed.
Lemma D_1d478 : decode_any W_1d478 = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d47c : bv 32 := 0x40b0063b.
Lemma F_1d47c : fetch_word Plain.M.loaded_segments (0x1d47c : word) = Some W_1d47c.
Proof. vm_refl. Qed.
Lemma D_1d47c : decode_any W_1d47c = Some (Op32 ALU_SUB 12 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d480 : bv 32 := 0x00c50633.
Lemma F_1d480 : fetch_word Plain.M.loaded_segments (0x1d480 : word) = Some W_1d480.
Proof. vm_refl. Qed.
Lemma D_1d480 : decode_any W_1d480 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d484 : bv 32 := 0x00500513.
Lemma F_1d484 : fetch_word Plain.M.loaded_segments (0x1d484 : word) = Some W_1d484.
Proof. vm_refl. Qed.
Lemma D_1d484 : decode_any W_1d484 = Some (OpImm ALU_ADD 10 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d488 : bv 32 := 0x00060023.
Lemma F_1d488 : fetch_word Plain.M.loaded_segments (0x1d488 : word) = Some W_1d488.
Proof. vm_refl. Qed.
Lemma D_1d488 : decode_any W_1d488 = Some (Store SZ1 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d48c : bv 32 := 0x00a5cc63.
Lemma F_1d48c : fetch_word Plain.M.loaded_segments (0x1d48c : word) = Some W_1d48c.
Proof. vm_refl. Qed.
Lemma D_1d48c : decode_any W_1d48c = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d490 : bv 32 := 0xfe070ba3.
Lemma F_1d490 : fetch_word Plain.M.loaded_segments (0x1d490 : word) = Some W_1d490.
Proof. vm_refl. Qed.
Lemma D_1d490 : decode_any W_1d490 = Some (Store SZ1 14 0 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d494 : bv 32 := 0xfeb72c23.
Lemma F_1d494 : fetch_word Plain.M.loaded_segments (0x1d494 : word) = Some W_1d494.
Proof. vm_refl. Qed.
Lemma D_1d494 : decode_any W_1d494 = Some (Store SZ4 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d498 : bv 32 := 0x0100006f.
Lemma F_1d498 : fetch_word Plain.M.loaded_segments (0x1d498 : word) = Some W_1d498.
Proof. vm_refl. Qed.
Lemma D_1d498 : decode_any W_1d498 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d49c : bv 32 := 0x00000513.
Lemma F_1d49c : fetch_word Plain.M.loaded_segments (0x1d49c : word) = Some W_1d49c.
Proof. vm_refl. Qed.
Lemma D_1d49c : decode_any W_1d49c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d4a0 : bv 32 := 0x0080006f.
Lemma F_1d4a0 : fetch_word Plain.M.loaded_segments (0x1d4a0 : word) = Some W_1d4a0.
Proof. vm_refl. Qed.
Lemma D_1d4a0 : decode_any W_1d4a0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d4a4 : bv 32 := 0x00058513.
Lemma F_1d4a4 : fetch_word Plain.M.loaded_segments (0x1d4a4 : word) = Some W_1d4a4.
Proof. vm_refl. Qed.
Lemma D_1d4a4 : decode_any W_1d4a4 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d4a8 : bv 32 := 0xffd6c583.
Lemma F_1d4a8 : fetch_word Plain.M.loaded_segments (0x1d4a8 : word) = Some W_1d4a8.
Proof. vm_refl. Qed.
Lemma D_1d4a8 : decode_any W_1d4a8 = Some (Load SZ1 false 11 13 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d4ac : bv 32 := 0x01f5f593.
Lemma F_1d4ac : fetch_word Plain.M.loaded_segments (0x1d4ac : word) = Some W_1d4ac.
Proof. vm_refl. Qed.
Lemma D_1d4ac : decode_any W_1d4ac = Some (OpImm ALU_AND 11 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d4b0 : bv 32 := 0x00551513.
Lemma F_1d4b0 : fetch_word Plain.M.loaded_segments (0x1d4b0 : word) = Some W_1d4b0.
Proof. vm_refl. Qed.
Lemma D_1d4b0 : decode_any W_1d4b0 = Some (ShiftImm ALU_SLL 10 10 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d4b4 : bv 32 := 0x00b56533.
Lemma F_1d4b4 : fetch_word Plain.M.loaded_segments (0x1d4b4 : word) = Some W_1d4b4.
Proof. vm_refl. Qed.
Lemma D_1d4b4 : decode_any W_1d4b4 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d4b8 : bv 32 := 0xfea68ea3.
Lemma F_1d4b8 : fetch_word Plain.M.loaded_segments (0x1d4b8 : word) = Some W_1d4b8.
Proof. vm_refl. Qed.
Lemma D_1d4b8 : decode_any W_1d4b8 = Some (Store SZ1 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d4bc : bv 32 := 0x00068513.
Lemma F_1d4bc : fetch_word Plain.M.loaded_segments (0x1d4bc : word) = Some W_1d4bc.
Proof. vm_refl. Qed.
Lemma D_1d4bc : decode_any W_1d4bc = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d4c0 : bv 32 := 0x00008067.
Lemma F_1d4c0 : fetch_word Plain.M.loaded_segments (0x1d4c0 : word) = Some W_1d4c0.
Proof. vm_refl. Qed.
Lemma D_1d4c0 : decode_any W_1d4c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d848 : bv 32 := 0x00008067.
Lemma F_1d848 : fetch_word Plain.M.loaded_segments (0x1d848 : word) = Some W_1d848.
Proof. vm_refl. Qed.
Lemma D_1d848 : decode_any W_1d848 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dd84 : bv 32 := 0xff010113.
Lemma F_1dd84 : fetch_word Plain.M.loaded_segments (0x1dd84 : word) = Some W_1dd84.
Proof. vm_refl. Qed.
Lemma D_1dd84 : decode_any W_1dd84 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dd88 : bv 32 := 0x00113423.
Lemma F_1dd88 : fetch_word Plain.M.loaded_segments (0x1dd88 : word) = Some W_1dd88.
Proof. vm_refl. Qed.
Lemma D_1dd88 : decode_any W_1dd88 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dd8c : bv 32 := 0x00813023.
Lemma F_1dd8c : fetch_word Plain.M.loaded_segments (0x1dd8c : word) = Some W_1dd8c.
Proof. vm_refl. Qed.
Lemma D_1dd8c : decode_any W_1dd8c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dd90 : bv 32 := 0x5d0000ef.
Lemma F_1dd90 : fetch_word Plain.M.loaded_segments (0x1dd90 : word) = Some W_1dd90.
Proof. vm_refl. Qed.
Lemma D_1dd90 : decode_any W_1dd90 = Some (Jal 1 1488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dd94 : bv 32 := 0x00053403.
Lemma F_1dd94 : fetch_word Plain.M.loaded_segments (0x1dd94 : word) = Some W_1dd94.
Proof. vm_refl. Qed.
Lemma D_1dd94 : decode_any W_1dd94 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dd98 : bv 32 := 0x12041663.
Lemma F_1dd98 : fetch_word Plain.M.loaded_segments (0x1dd98 : word) = Some W_1dd98.
Proof. vm_refl. Qed.
Lemma D_1dd98 : decode_any W_1dd98 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dd9c : bv 32 := 0x00008517.
Lemma F_1dd9c : fetch_word Plain.M.loaded_segments (0x1dd9c : word) = Some W_1dd9c.
Proof. vm_refl. Qed.
Lemma D_1dd9c : decode_any W_1dd9c = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dda0 : bv 32 := 0x7a453403.
Lemma F_1dda0 : fetch_word Plain.M.loaded_segments (0x1dda0 : word) = Some W_1dda0.
Proof. vm_refl. Qed.
Lemma D_1dda0 : decode_any W_1dda0 = Some (Load SZ8 true 8 10 1956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dda4 : bv 32 := 0x04040a63.
Lemma F_1dda4 : fetch_word Plain.M.loaded_segments (0x1dda4 : word) = Some W_1dda4.
Proof. vm_refl. Qed.
Lemma D_1dda4 : decode_any W_1dda4 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dda8 : bv 32 := 0x08c42503.
Lemma F_1dda8 : fetch_word Plain.M.loaded_segments (0x1dda8 : word) = Some W_1dda8.
Proof. vm_refl. Qed.
Lemma D_1dda8 : decode_any W_1dda8 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ddac : bv 32 := 0x00054663.
Lemma F_1ddac : fetch_word Plain.M.loaded_segments (0x1ddac : word) = Some W_1ddac.
Proof. vm_refl. Qed.
Lemma D_1ddac : decode_any W_1ddac = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ddb8 : bv 32 := 0x02843503.
Lemma F_1ddb8 : fetch_word Plain.M.loaded_segments (0x1ddb8 : word) = Some W_1ddb8.
Proof. vm_refl. Qed.
Lemma D_1ddb8 : decode_any W_1ddb8 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ddbc : bv 32 := 0x03843583.
Lemma F_1ddbc : fetch_word Plain.M.loaded_segments (0x1ddbc : word) = Some W_1ddbc.
Proof. vm_refl. Qed.
Lemma D_1ddbc : decode_any W_1ddbc = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ddc0 : bv 32 := 0x00b50c63.
Lemma F_1ddc0 : fetch_word Plain.M.loaded_segments (0x1ddc0 : word) = Some W_1ddc0.
Proof. vm_refl. Qed.
Lemma D_1ddc0 : decode_any W_1ddc0 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ddd8 : bv 32 := 0x00843503.
Lemma F_1ddd8 : fetch_word Plain.M.loaded_segments (0x1ddd8 : word) = Some W_1ddd8.
Proof. vm_refl. Qed.
Lemma D_1ddd8 : decode_any W_1ddd8 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dddc : bv 32 := 0x01043583.
Lemma F_1dddc : fetch_word Plain.M.loaded_segments (0x1dddc : word) = Some W_1dddc.
Proof. vm_refl. Qed.
Lemma D_1dddc : decode_any W_1dddc = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dde0 : bv 32 := 0x00b50c63.
Lemma F_1dde0 : fetch_word Plain.M.loaded_segments (0x1dde0 : word) = Some W_1dde0.
Proof. vm_refl. Qed.
Lemma D_1dde0 : decode_any W_1dde0 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ddf8 : bv 32 := 0x00009517.
Lemma F_1ddf8 : fetch_word Plain.M.loaded_segments (0x1ddf8 : word) = Some W_1ddf8.
Proof. vm_refl. Qed.
Lemma D_1ddf8 : decode_any W_1ddf8 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ddfc : bv 32 := 0x83853403.
Lemma F_1ddfc : fetch_word Plain.M.loaded_segments (0x1ddfc : word) = Some W_1ddfc.
Proof. vm_refl. Qed.
Lemma D_1ddfc : decode_any W_1ddfc = Some (Load SZ8 true 8 10 2104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de00 : bv 32 := 0x04040a63.
Lemma F_1de00 : fetch_word Plain.M.loaded_segments (0x1de00 : word) = Some W_1de00.
Proof. vm_refl. Qed.
Lemma D_1de00 : decode_any W_1de00 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de04 : bv 32 := 0x08c42503.
Lemma F_1de04 : fetch_word Plain.M.loaded_segments (0x1de04 : word) = Some W_1de04.
Proof. vm_refl. Qed.
Lemma D_1de04 : decode_any W_1de04 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de08 : bv 32 := 0x00054663.
Lemma F_1de08 : fetch_word Plain.M.loaded_segments (0x1de08 : word) = Some W_1de08.
Proof. vm_refl. Qed.
Lemma D_1de08 : decode_any W_1de08 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de14 : bv 32 := 0x02843503.
Lemma F_1de14 : fetch_word Plain.M.loaded_segments (0x1de14 : word) = Some W_1de14.
Proof. vm_refl. Qed.
Lemma D_1de14 : decode_any W_1de14 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de18 : bv 32 := 0x03843583.
Lemma F_1de18 : fetch_word Plain.M.loaded_segments (0x1de18 : word) = Some W_1de18.
Proof. vm_refl. Qed.
Lemma D_1de18 : decode_any W_1de18 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de1c : bv 32 := 0x00b50c63.
Lemma F_1de1c : fetch_word Plain.M.loaded_segments (0x1de1c : word) = Some W_1de1c.
Proof. vm_refl. Qed.
Lemma D_1de1c : decode_any W_1de1c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de20 : bv 32 := 0x04843683.
Lemma F_1de20 : fetch_word Plain.M.loaded_segments (0x1de20 : word) = Some W_1de20.
Proof. vm_refl. Qed.
Lemma D_1de20 : decode_any W_1de20 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de24 : bv 32 := 0x00040513.
Lemma F_1de24 : fetch_word Plain.M.loaded_segments (0x1de24 : word) = Some W_1de24.
Proof. vm_refl. Qed.
Lemma D_1de24 : decode_any W_1de24 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de28 : bv 32 := 0x00000593.
Lemma F_1de28 : fetch_word Plain.M.loaded_segments (0x1de28 : word) = Some W_1de28.
Proof. vm_refl. Qed.
Lemma D_1de28 : decode_any W_1de28 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de2c : bv 32 := 0x00000613.
Lemma F_1de2c : fetch_word Plain.M.loaded_segments (0x1de2c : word) = Some W_1de2c.
Proof. vm_refl. Qed.
Lemma D_1de2c : decode_any W_1de2c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de30 : bv 32 := 0x000680e7.
Lemma F_1de30 : fetch_word Plain.M.loaded_segments (0x1de30 : word) = Some W_1de30.
Proof. vm_refl. Qed.
Lemma D_1de30 : decode_any W_1de30 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de34 : bv 32 := 0x00843503.
Lemma F_1de34 : fetch_word Plain.M.loaded_segments (0x1de34 : word) = Some W_1de34.
Proof. vm_refl. Qed.
Lemma D_1de34 : decode_any W_1de34 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de38 : bv 32 := 0x01043583.
Lemma F_1de38 : fetch_word Plain.M.loaded_segments (0x1de38 : word) = Some W_1de38.
Proof. vm_refl. Qed.
Lemma D_1de38 : decode_any W_1de38 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de3c : bv 32 := 0x00b50c63.
Lemma F_1de3c : fetch_word Plain.M.loaded_segments (0x1de3c : word) = Some W_1de3c.
Proof. vm_refl. Qed.
Lemma D_1de3c : decode_any W_1de3c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de54 : bv 32 := 0x00008517.
Lemma F_1de54 : fetch_word Plain.M.loaded_segments (0x1de54 : word) = Some W_1de54.
Proof. vm_refl. Qed.
Lemma D_1de54 : decode_any W_1de54 = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de58 : bv 32 := 0x5fc53403.
Lemma F_1de58 : fetch_word Plain.M.loaded_segments (0x1de58 : word) = Some W_1de58.
Proof. vm_refl. Qed.
Lemma D_1de58 : decode_any W_1de58 = Some (Load SZ8 true 8 10 1532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de5c : bv 32 := 0x0a040e63.
Lemma F_1de5c : fetch_word Plain.M.loaded_segments (0x1de5c : word) = Some W_1de5c.
Proof. vm_refl. Qed.
Lemma D_1de5c : decode_any W_1de5c = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de60 : bv 32 := 0x08c42503.
Lemma F_1de60 : fetch_word Plain.M.loaded_segments (0x1de60 : word) = Some W_1de60.
Proof. vm_refl. Qed.
Lemma D_1de60 : decode_any W_1de60 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de64 : bv 32 := 0x00054663.
Lemma F_1de64 : fetch_word Plain.M.loaded_segments (0x1de64 : word) = Some W_1de64.
Proof. vm_refl. Qed.
Lemma D_1de64 : decode_any W_1de64 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de70 : bv 32 := 0x02843503.
Lemma F_1de70 : fetch_word Plain.M.loaded_segments (0x1de70 : word) = Some W_1de70.
Proof. vm_refl. Qed.
Lemma D_1de70 : decode_any W_1de70 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de74 : bv 32 := 0x03843583.
Lemma F_1de74 : fetch_word Plain.M.loaded_segments (0x1de74 : word) = Some W_1de74.
Proof. vm_refl. Qed.
Lemma D_1de74 : decode_any W_1de74 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de78 : bv 32 := 0x00b50c63.
Lemma F_1de78 : fetch_word Plain.M.loaded_segments (0x1de78 : word) = Some W_1de78.
Proof. vm_refl. Qed.
Lemma D_1de78 : decode_any W_1de78 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de90 : bv 32 := 0x00843503.
Lemma F_1de90 : fetch_word Plain.M.loaded_segments (0x1de90 : word) = Some W_1de90.
Proof. vm_refl. Qed.
Lemma D_1de90 : decode_any W_1de90 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de94 : bv 32 := 0x01043583.
Lemma F_1de94 : fetch_word Plain.M.loaded_segments (0x1de94 : word) = Some W_1de94.
Proof. vm_refl. Qed.
Lemma D_1de94 : decode_any W_1de94 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1de98 : bv 32 := 0x08b50063.
Lemma F_1de98 : fetch_word Plain.M.loaded_segments (0x1de98 : word) = Some W_1de98.
Proof. vm_refl. Qed.
Lemma D_1de98 : decode_any W_1de98 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df18 : bv 32 := 0x00813083.
Lemma F_1df18 : fetch_word Plain.M.loaded_segments (0x1df18 : word) = Some W_1df18.
Proof. vm_refl. Qed.
Lemma D_1df18 : decode_any W_1df18 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df1c : bv 32 := 0x00013403.
Lemma F_1df1c : fetch_word Plain.M.loaded_segments (0x1df1c : word) = Some W_1df1c.
Proof. vm_refl. Qed.
Lemma D_1df1c : decode_any W_1df1c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df20 : bv 32 := 0x01010113.
Lemma F_1df20 : fetch_word Plain.M.loaded_segments (0x1df20 : word) = Some W_1df20.
Proof. vm_refl. Qed.
Lemma D_1df20 : decode_any W_1df20 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df24 : bv 32 := 0x00008067.
Lemma F_1df24 : fetch_word Plain.M.loaded_segments (0x1df24 : word) = Some W_1df24.
Proof. vm_refl. Qed.
Lemma D_1df24 : decode_any W_1df24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df28 : bv 32 := 0xf9010113.
Lemma F_1df28 : fetch_word Plain.M.loaded_segments (0x1df28 : word) = Some W_1df28.
Proof. vm_refl. Qed.
Lemma D_1df28 : decode_any W_1df28 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df2c : bv 32 := 0x06113423.
Lemma F_1df2c : fetch_word Plain.M.loaded_segments (0x1df2c : word) = Some W_1df2c.
Proof. vm_refl. Qed.
Lemma D_1df2c : decode_any W_1df2c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df30 : bv 32 := 0x06813023.
Lemma F_1df30 : fetch_word Plain.M.loaded_segments (0x1df30 : word) = Some W_1df30.
Proof. vm_refl. Qed.
Lemma D_1df30 : decode_any W_1df30 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df34 : bv 32 := 0x04913c23.
Lemma F_1df34 : fetch_word Plain.M.loaded_segments (0x1df34 : word) = Some W_1df34.
Proof. vm_refl. Qed.
Lemma D_1df34 : decode_any W_1df34 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df38 : bv 32 := 0x05213823.
Lemma F_1df38 : fetch_word Plain.M.loaded_segments (0x1df38 : word) = Some W_1df38.
Proof. vm_refl. Qed.
Lemma D_1df38 : decode_any W_1df38 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df3c : bv 32 := 0x05313423.
Lemma F_1df3c : fetch_word Plain.M.loaded_segments (0x1df3c : word) = Some W_1df3c.
Proof. vm_refl. Qed.
Lemma D_1df3c : decode_any W_1df3c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df40 : bv 32 := 0x05413023.
Lemma F_1df40 : fetch_word Plain.M.loaded_segments (0x1df40 : word) = Some W_1df40.
Proof. vm_refl. Qed.
Lemma D_1df40 : decode_any W_1df40 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df44 : bv 32 := 0x03513c23.
Lemma F_1df44 : fetch_word Plain.M.loaded_segments (0x1df44 : word) = Some W_1df44.
Proof. vm_refl. Qed.
Lemma D_1df44 : decode_any W_1df44 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df48 : bv 32 := 0x03613823.
Lemma F_1df48 : fetch_word Plain.M.loaded_segments (0x1df48 : word) = Some W_1df48.
Proof. vm_refl. Qed.
Lemma D_1df48 : decode_any W_1df48 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df4c : bv 32 := 0x00060413.
Lemma F_1df4c : fetch_word Plain.M.loaded_segments (0x1df4c : word) = Some W_1df4c.
Proof. vm_refl. Qed.
Lemma D_1df4c : decode_any W_1df4c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df50 : bv 32 := 0x00050493.
Lemma F_1df50 : fetch_word Plain.M.loaded_segments (0x1df50 : word) = Some W_1df50.
Proof. vm_refl. Qed.
Lemma D_1df50 : decode_any W_1df50 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df54 : bv 32 := 0x00007517.
Lemma F_1df54 : fetch_word Plain.M.loaded_segments (0x1df54 : word) = Some W_1df54.
Proof. vm_refl. Qed.
Lemma D_1df54 : decode_any W_1df54 = Some (Auipc 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df58 : bv 32 := 0x3a453a83.
Lemma F_1df58 : fetch_word Plain.M.loaded_segments (0x1df58 : word) = Some W_1df58.
Proof. vm_refl. Qed.
Lemma D_1df58 : decode_any W_1df58 = Some (Load SZ8 true 21 10 932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df5c : bv 32 := 0x000ab503.
Lemma F_1df5c : fetch_word Plain.M.loaded_segments (0x1df5c : word) = Some W_1df5c.
Proof. vm_refl. Qed.
Lemma D_1df5c : decode_any W_1df5c = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df60 : bv 32 := 0x02a13423.
Lemma F_1df60 : fetch_word Plain.M.loaded_segments (0x1df60 : word) = Some W_1df60.
Proof. vm_refl. Qed.
Lemma D_1df60 : decode_any W_1df60 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df64 : bv 32 := 0x0284b503.
Lemma F_1df64 : fetch_word Plain.M.loaded_segments (0x1df64 : word) = Some W_1df64.
Proof. vm_refl. Qed.
Lemma D_1df64 : decode_any W_1df64 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df68 : bv 32 := 0x0384b603.
Lemma F_1df68 : fetch_word Plain.M.loaded_segments (0x1df68 : word) = Some W_1df68.
Proof. vm_refl. Qed.
Lemma D_1df68 : decode_any W_1df68 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df6c : bv 32 := 0x40c50b33.
Lemma F_1df6c : fetch_word Plain.M.loaded_segments (0x1df6c : word) = Some W_1df6c.
Proof. vm_refl. Qed.
Lemma D_1df6c : decode_any W_1df6c = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df70 : bv 32 := 0x00c546b3.
Lemma F_1df70 : fetch_word Plain.M.loaded_segments (0x1df70 : word) = Some W_1df70.
Proof. vm_refl. Qed.
Lemma D_1df70 : decode_any W_1df70 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df74 : bv 32 := 0x00c13423.
Lemma F_1df74 : fetch_word Plain.M.loaded_segments (0x1df74 : word) = Some W_1df74.
Proof. vm_refl. Qed.
Lemma D_1df74 : decode_any W_1df74 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df78 : bv 32 := 0x01613823.
Lemma F_1df78 : fetch_word Plain.M.loaded_segments (0x1df78 : word) = Some W_1df78.
Proof. vm_refl. Qed.
Lemma D_1df78 : decode_any W_1df78 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df7c : bv 32 := 0x00b13c23.
Lemma F_1df7c : fetch_word Plain.M.loaded_segments (0x1df7c : word) = Some W_1df7c.
Proof. vm_refl. Qed.
Lemma D_1df7c : decode_any W_1df7c = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df80 : bv 32 := 0x02813023.
Lemma F_1df80 : fetch_word Plain.M.loaded_segments (0x1df80 : word) = Some W_1df80.
Proof. vm_refl. Qed.
Lemma D_1df80 : decode_any W_1df80 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df84 : bv 32 := 0x008b0b33.
Lemma F_1df84 : fetch_word Plain.M.loaded_segments (0x1df84 : word) = Some W_1df84.
Proof. vm_refl. Qed.
Lemma D_1df84 : decode_any W_1df84 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df88 : bv 32 := 0x00d03933.
Lemma F_1df88 : fetch_word Plain.M.loaded_segments (0x1df88 : word) = Some W_1df88.
Proof. vm_refl. Qed.
Lemma D_1df88 : decode_any W_1df88 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df8c : bv 32 := 0x00c50663.
Lemma F_1df8c : fetch_word Plain.M.loaded_segments (0x1df8c : word) = Some W_1df8c.
Proof. vm_refl. Qed.
Lemma D_1df8c : decode_any W_1df8c = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df90 : bv 32 := 0x00810993.
Lemma F_1df90 : fetch_word Plain.M.loaded_segments (0x1df90 : word) = Some W_1df90.
Proof. vm_refl. Qed.
Lemma D_1df90 : decode_any W_1df90 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df94 : bv 32 := 0x0080006f.
Lemma F_1df94 : fetch_word Plain.M.loaded_segments (0x1df94 : word) = Some W_1df94.
Proof. vm_refl. Qed.
Lemma D_1df94 : decode_any W_1df94 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df98 : bv 32 := 0x01810993.
Lemma F_1df98 : fetch_word Plain.M.loaded_segments (0x1df98 : word) = Some W_1df98.
Proof. vm_refl. Qed.
Lemma D_1df98 : decode_any W_1df98 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1df9c : bv 32 := 0x0784a503.
Lemma F_1df9c : fetch_word Plain.M.loaded_segments (0x1df9c : word) = Some W_1df9c.
Proof. vm_refl. Qed.
Lemma D_1df9c : decode_any W_1df9c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfa0 : bv 32 := 0x00190913.
Lemma F_1dfa0 : fetch_word Plain.M.loaded_segments (0x1dfa0 : word) = Some W_1dfa0.
Proof. vm_refl. Qed.
Lemma D_1dfa0 : decode_any W_1dfa0 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfa4 : bv 32 := 0x04200893.
Lemma F_1dfa4 : fetch_word Plain.M.loaded_segments (0x1dfa4 : word) = Some W_1dfa4.
Proof. vm_refl. Qed.
Lemma D_1dfa4 : decode_any W_1dfa4 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfa8 : bv 32 := 0x00098593.
Lemma F_1dfa8 : fetch_word Plain.M.loaded_segments (0x1dfa8 : word) = Some W_1dfa8.
Proof. vm_refl. Qed.
Lemma D_1dfa8 : decode_any W_1dfa8 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfac : bv 32 := 0x00090613.
Lemma F_1dfac : fetch_word Plain.M.loaded_segments (0x1dfac : word) = Some W_1dfac.
Proof. vm_refl. Qed.
Lemma D_1dfac : decode_any W_1dfac = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfb0 : bv 32 := 0x00000073.
Lemma F_1dfb0 : fetch_word Plain.M.loaded_segments (0x1dfb0 : word) = Some W_1dfb0.
Proof. vm_refl. Qed.
Lemma D_1dfb0 : decode_any W_1dfb0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1dfb0 : is_ecall W_1dfb0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1dfb4 : bv 32 := 0xc9dfd0ef.
Lemma F_1dfb4 : fetch_word Plain.M.loaded_segments (0x1dfb4 : word) = Some W_1dfb4.
Proof. vm_refl. Qed.
Lemma D_1dfb4 : decode_any W_1dfb4 = Some (Jal 1 2088092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfb8 : bv 32 := 0x09651863.
Lemma F_1dfb8 : fetch_word Plain.M.loaded_segments (0x1dfb8 : word) = Some W_1dfb8.
Proof. vm_refl. Qed.
Lemma D_1dfb8 : decode_any W_1dfb8 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfbc : bv 32 := 0x0584b503.
Lemma F_1dfbc : fetch_word Plain.M.loaded_segments (0x1dfbc : word) = Some W_1dfbc.
Proof. vm_refl. Qed.
Lemma D_1dfbc : decode_any W_1dfbc = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfc0 : bv 32 := 0x0604b583.
Lemma F_1dfc0 : fetch_word Plain.M.loaded_segments (0x1dfc0 : word) = Some W_1dfc0.
Proof. vm_refl. Qed.
Lemma D_1dfc0 : decode_any W_1dfc0 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfc4 : bv 32 := 0x00b505b3.
Lemma F_1dfc4 : fetch_word Plain.M.loaded_segments (0x1dfc4 : word) = Some W_1dfc4.
Proof. vm_refl. Qed.
Lemma D_1dfc4 : decode_any W_1dfc4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfc8 : bv 32 := 0x02b4b023.
Lemma F_1dfc8 : fetch_word Plain.M.loaded_segments (0x1dfc8 : word) = Some W_1dfc8.
Proof. vm_refl. Qed.
Lemma D_1dfc8 : decode_any W_1dfc8 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfcc : bv 32 := 0x02a4b423.
Lemma F_1dfcc : fetch_word Plain.M.loaded_segments (0x1dfcc : word) = Some W_1dfcc.
Proof. vm_refl. Qed.
Lemma D_1dfcc : decode_any W_1dfcc = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfd0 : bv 32 := 0x02a4bc23.
Lemma F_1dfd0 : fetch_word Plain.M.loaded_segments (0x1dfd0 : word) = Some W_1dfd0.
Proof. vm_refl. Qed.
Lemma D_1dfd0 : decode_any W_1dfd0 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfd4 : bv 32 := 0x00040513.
Lemma F_1dfd4 : fetch_word Plain.M.loaded_segments (0x1dfd4 : word) = Some W_1dfd4.
Proof. vm_refl. Qed.
Lemma D_1dfd4 : decode_any W_1dfd4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfd8 : bv 32 := 0x000ab583.
Lemma F_1dfd8 : fetch_word Plain.M.loaded_segments (0x1dfd8 : word) = Some W_1dfd8.
Proof. vm_refl. Qed.
Lemma D_1dfd8 : decode_any W_1dfd8 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfdc : bv 32 := 0x02813603.
Lemma F_1dfdc : fetch_word Plain.M.loaded_segments (0x1dfdc : word) = Some W_1dfdc.
Proof. vm_refl. Qed.
Lemma D_1dfdc : decode_any W_1dfdc = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfe0 : bv 32 := 0x0cc59a63.
Lemma F_1dfe0 : fetch_word Plain.M.loaded_segments (0x1dfe0 : word) = Some W_1dfe0.
Proof. vm_refl. Qed.
Lemma D_1dfe0 : decode_any W_1dfe0 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfe4 : bv 32 := 0x06813083.
Lemma F_1dfe4 : fetch_word Plain.M.loaded_segments (0x1dfe4 : word) = Some W_1dfe4.
Proof. vm_refl. Qed.
Lemma D_1dfe4 : decode_any W_1dfe4 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfe8 : bv 32 := 0x06013403.
Lemma F_1dfe8 : fetch_word Plain.M.loaded_segments (0x1dfe8 : word) = Some W_1dfe8.
Proof. vm_refl. Qed.
Lemma D_1dfe8 : decode_any W_1dfe8 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dfec : bv 32 := 0x05813483.
Lemma F_1dfec : fetch_word Plain.M.loaded_segments (0x1dfec : word) = Some W_1dfec.
Proof. vm_refl. Qed.
Lemma D_1dfec : decode_any W_1dfec = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dff0 : bv 32 := 0x05013903.
Lemma F_1dff0 : fetch_word Plain.M.loaded_segments (0x1dff0 : word) = Some W_1dff0.
Proof. vm_refl. Qed.
Lemma D_1dff0 : decode_any W_1dff0 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dff4 : bv 32 := 0x04813983.
Lemma F_1dff4 : fetch_word Plain.M.loaded_segments (0x1dff4 : word) = Some W_1dff4.
Proof. vm_refl. Qed.
Lemma D_1dff4 : decode_any W_1dff4 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dff8 : bv 32 := 0x04013a03.
Lemma F_1dff8 : fetch_word Plain.M.loaded_segments (0x1dff8 : word) = Some W_1dff8.
Proof. vm_refl. Qed.
Lemma D_1dff8 : decode_any W_1dff8 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1dffc : bv 32 := 0x03813a83.
Lemma F_1dffc : fetch_word Plain.M.loaded_segments (0x1dffc : word) = Some W_1dffc.
Proof. vm_refl. Qed.
Lemma D_1dffc : decode_any W_1dffc = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e000 : bv 32 := 0x03013b03.
Lemma F_1e000 : fetch_word Plain.M.loaded_segments (0x1e000 : word) = Some W_1e000.
Proof. vm_refl. Qed.
Lemma D_1e000 : decode_any W_1e000 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e004 : bv 32 := 0x07010113.
Lemma F_1e004 : fetch_word Plain.M.loaded_segments (0x1e004 : word) = Some W_1e004.
Proof. vm_refl. Qed.
Lemma D_1e004 : decode_any W_1e004 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e008 : bv 32 := 0x00008067.
Lemma F_1e008 : fetch_word Plain.M.loaded_segments (0x1e008 : word) = Some W_1e008.
Proof. vm_refl. Qed.
Lemma D_1e008 : decode_any W_1e008 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e00c : bv 32 := 0x00800713.
Lemma F_1e00c : fetch_word Plain.M.loaded_segments (0x1e00c : word) = Some W_1e00c.
Proof. vm_refl. Qed.
Lemma D_1e00c : decode_any W_1e00c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e010 : bv 32 := 0x000a0593.
Lemma F_1e010 : fetch_word Plain.M.loaded_segments (0x1e010 : word) = Some W_1e010.
Proof. vm_refl. Qed.
Lemma D_1e010 : decode_any W_1e010 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e014 : bv 32 := 0x00e98733.
Lemma F_1e014 : fetch_word Plain.M.loaded_segments (0x1e014 : word) = Some W_1e014.
Proof. vm_refl. Qed.
Lemma D_1e014 : decode_any W_1e014 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e018 : bv 32 := 0x00073783.
Lemma F_1e018 : fetch_word Plain.M.loaded_segments (0x1e018 : word) = Some W_1e018.
Proof. vm_refl. Qed.
Lemma D_1e018 : decode_any W_1e018 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e01c : bv 32 := 0x40ab0b33.
Lemma F_1e01c : fetch_word Plain.M.loaded_segments (0x1e01c : word) = Some W_1e01c.
Proof. vm_refl. Qed.
Lemma D_1e01c : decode_any W_1e01c = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e020 : bv 32 := 0x0784a503.
Lemma F_1e020 : fetch_word Plain.M.loaded_segments (0x1e020 : word) = Some W_1e020.
Proof. vm_refl. Qed.
Lemma D_1e020 : decode_any W_1e020 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e024 : bv 32 := 0x40c9093b.
Lemma F_1e024 : fetch_word Plain.M.loaded_segments (0x1e024 : word) = Some W_1e024.
Proof. vm_refl. Qed.
Lemma D_1e024 : decode_any W_1e024 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e028 : bv 32 := 0x40d787b3.
Lemma F_1e028 : fetch_word Plain.M.loaded_segments (0x1e028 : word) = Some W_1e028.
Proof. vm_refl. Qed.
Lemma D_1e028 : decode_any W_1e028 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e02c : bv 32 := 0x00f73023.
Lemma F_1e02c : fetch_word Plain.M.loaded_segments (0x1e02c : word) = Some W_1e02c.
Proof. vm_refl. Qed.
Lemma D_1e02c : decode_any W_1e02c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e030 : bv 32 := 0x04200893.
Lemma F_1e030 : fetch_word Plain.M.loaded_segments (0x1e030 : word) = Some W_1e030.
Proof. vm_refl. Qed.
Lemma D_1e030 : decode_any W_1e030 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e034 : bv 32 := 0x00090613.
Lemma F_1e034 : fetch_word Plain.M.loaded_segments (0x1e034 : word) = Some W_1e034.
Proof. vm_refl. Qed.
Lemma D_1e034 : decode_any W_1e034 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e038 : bv 32 := 0x00000073.
Lemma F_1e038 : fetch_word Plain.M.loaded_segments (0x1e038 : word) = Some W_1e038.
Proof. vm_refl. Qed.
Lemma D_1e038 : decode_any W_1e038 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1e038 : is_ecall W_1e038 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1e03c : bv 32 := 0xc15fd0ef.
Lemma F_1e03c : fetch_word Plain.M.loaded_segments (0x1e03c : word) = Some W_1e03c.
Proof. vm_refl. Qed.
Lemma D_1e03c : decode_any W_1e03c = Some (Jal 1 2087956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e040 : bv 32 := 0x000a0993.
Lemma F_1e040 : fetch_word Plain.M.loaded_segments (0x1e040 : word) = Some W_1e040.
Proof. vm_refl. Qed.
Lemma D_1e040 : decode_any W_1e040 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e044 : bv 32 := 0xf7650ce3.
Lemma F_1e044 : fetch_word Plain.M.loaded_segments (0x1e044 : word) = Some W_1e044.
Proof. vm_refl. Qed.
Lemma D_1e044 : decode_any W_1e044 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e048 : bv 32 := 0x02054c63.
Lemma F_1e048 : fetch_word Plain.M.loaded_segments (0x1e048 : word) = Some W_1e048.
Proof. vm_refl. Qed.
Lemma D_1e048 : decode_any W_1e048 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e04c : bv 32 := 0x0089b583.
Lemma F_1e04c : fetch_word Plain.M.loaded_segments (0x1e04c : word) = Some W_1e04c.
Proof. vm_refl. Qed.
Lemma D_1e04c : decode_any W_1e04c = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e050 : bv 32 := 0x00a5b633.
Lemma F_1e050 : fetch_word Plain.M.loaded_segments (0x1e050 : word) = Some W_1e050.
Proof. vm_refl. Qed.
Lemma D_1e050 : decode_any W_1e050 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e054 : bv 32 := 0x00461a13.
Lemma F_1e054 : fetch_word Plain.M.loaded_segments (0x1e054 : word) = Some W_1e054.
Proof. vm_refl. Qed.
Lemma D_1e054 : decode_any W_1e054 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e058 : bv 32 := 0x01498a33.
Lemma F_1e058 : fetch_word Plain.M.loaded_segments (0x1e058 : word) = Some W_1e058.
Proof. vm_refl. Qed.
Lemma D_1e058 : decode_any W_1e058 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e05c : bv 32 := 0x000a3703.
Lemma F_1e05c : fetch_word Plain.M.loaded_segments (0x1e05c : word) = Some W_1e05c.
Proof. vm_refl. Qed.
Lemma D_1e05c : decode_any W_1e05c = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e060 : bv 32 := 0x40c006b3.
Lemma F_1e060 : fetch_word Plain.M.loaded_segments (0x1e060 : word) = Some W_1e060.
Proof. vm_refl. Qed.
Lemma D_1e060 : decode_any W_1e060 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e064 : bv 32 := 0x00b6f6b3.
Lemma F_1e064 : fetch_word Plain.M.loaded_segments (0x1e064 : word) = Some W_1e064.
Proof. vm_refl. Qed.
Lemma D_1e064 : decode_any W_1e064 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e068 : bv 32 := 0x40d506b3.
Lemma F_1e068 : fetch_word Plain.M.loaded_segments (0x1e068 : word) = Some W_1e068.
Proof. vm_refl. Qed.
Lemma D_1e068 : decode_any W_1e068 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e06c : bv 32 := 0x00d70733.
Lemma F_1e06c : fetch_word Plain.M.loaded_segments (0x1e06c : word) = Some W_1e06c.
Proof. vm_refl. Qed.
Lemma D_1e06c : decode_any W_1e06c = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e070 : bv 32 := 0x00ea3023.
Lemma F_1e070 : fetch_word Plain.M.loaded_segments (0x1e070 : word) = Some W_1e070.
Proof. vm_refl. Qed.
Lemma D_1e070 : decode_any W_1e070 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e074 : bv 32 := 0xf8a5fce3.
Lemma F_1e074 : fetch_word Plain.M.loaded_segments (0x1e074 : word) = Some W_1e074.
Proof. vm_refl. Qed.
Lemma D_1e074 : decode_any W_1e074 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e078 : bv 32 := 0x01800713.
Lemma F_1e078 : fetch_word Plain.M.loaded_segments (0x1e078 : word) = Some W_1e078.
Proof. vm_refl. Qed.
Lemma D_1e078 : decode_any W_1e078 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e07c : bv 32 := 0xf95ff06f.
Lemma F_1e07c : fetch_word Plain.M.loaded_segments (0x1e07c : word) = Some W_1e07c.
Proof. vm_refl. Qed.
Lemma D_1e07c : decode_any W_1e07c = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e360 : bv 32 := 0xff010113.
Lemma F_1e360 : fetch_word Plain.M.loaded_segments (0x1e360 : word) = Some W_1e360.
Proof. vm_refl. Qed.
Lemma D_1e360 : decode_any W_1e360 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e364 : bv 32 := 0x00113423.
Lemma F_1e364 : fetch_word Plain.M.loaded_segments (0x1e364 : word) = Some W_1e364.
Proof. vm_refl. Qed.
Lemma D_1e364 : decode_any W_1e364 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e368 : bv 32 := 0x00813023.
Lemma F_1e368 : fetch_word Plain.M.loaded_segments (0x1e368 : word) = Some W_1e368.
Proof. vm_refl. Qed.
Lemma D_1e368 : decode_any W_1e368 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e36c : bv 32 := 0x00039517.
Lemma F_1e36c : fetch_word Plain.M.loaded_segments (0x1e36c : word) = Some W_1e36c.
Proof. vm_refl. Qed.
Lemma D_1e36c : decode_any W_1e36c = Some (Auipc 10 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e370 : bv 32 := 0xaec50413.
Lemma F_1e370 : fetch_word Plain.M.loaded_segments (0x1e370 : word) = Some W_1e370.
Proof. vm_refl. Qed.
Lemma D_1e370 : decode_any W_1e370 = Some (OpImm ALU_ADD 8 10 2796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e374 : bv 32 := 0x00040513.
Lemma F_1e374 : fetch_word Plain.M.loaded_segments (0x1e374 : word) = Some W_1e374.
Proof. vm_refl. Qed.
Lemma D_1e374 : decode_any W_1e374 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e378 : bv 32 := 0x209050ef.
Lemma F_1e378 : fetch_word Plain.M.loaded_segments (0x1e378 : word) = Some W_1e378.
Proof. vm_refl. Qed.
Lemma D_1e378 : decode_any W_1e378 = Some (Jal 1 23048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e37c : bv 32 := 0x00840513.
Lemma F_1e37c : fetch_word Plain.M.loaded_segments (0x1e37c : word) = Some W_1e37c.
Proof. vm_refl. Qed.
Lemma D_1e37c : decode_any W_1e37c = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e380 : bv 32 := 0x00813083.
Lemma F_1e380 : fetch_word Plain.M.loaded_segments (0x1e380 : word) = Some W_1e380.
Proof. vm_refl. Qed.
Lemma D_1e380 : decode_any W_1e380 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e384 : bv 32 := 0x00013403.
Lemma F_1e384 : fetch_word Plain.M.loaded_segments (0x1e384 : word) = Some W_1e384.
Proof. vm_refl. Qed.
Lemma D_1e384 : decode_any W_1e384 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e388 : bv 32 := 0x01010113.
Lemma F_1e388 : fetch_word Plain.M.loaded_segments (0x1e388 : word) = Some W_1e388.
Proof. vm_refl. Qed.
Lemma D_1e388 : decode_any W_1e388 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1e38c : bv 32 := 0x00008067.
Lemma F_1e38c : fetch_word Plain.M.loaded_segments (0x1e38c : word) = Some W_1e38c.
Proof. vm_refl. Qed.
Lemma D_1e38c : decode_any W_1e38c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
