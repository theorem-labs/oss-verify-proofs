(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6b184 : bv 32 := 0x00008067.
Lemma F_6b184 : fetch_word Ubsan.M.loaded_segments (0x6b184 : word) = Some W_6b184.
Proof. vm_refl. Qed.
Lemma D_6b184 : decode_any W_6b184 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b188 : bv 32 := 0xe8010113.
Lemma F_6b188 : fetch_word Ubsan.M.loaded_segments (0x6b188 : word) = Some W_6b188.
Proof. vm_refl. Qed.
Lemma D_6b188 : decode_any W_6b188 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b18c : bv 32 := 0x16113c23.
Lemma F_6b18c : fetch_word Ubsan.M.loaded_segments (0x6b18c : word) = Some W_6b18c.
Proof. vm_refl. Qed.
Lemma D_6b18c : decode_any W_6b18c = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b190 : bv 32 := 0x16813823.
Lemma F_6b190 : fetch_word Ubsan.M.loaded_segments (0x6b190 : word) = Some W_6b190.
Proof. vm_refl. Qed.
Lemma D_6b190 : decode_any W_6b190 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b194 : bv 32 := 0x16913423.
Lemma F_6b194 : fetch_word Ubsan.M.loaded_segments (0x6b194 : word) = Some W_6b194.
Proof. vm_refl. Qed.
Lemma D_6b194 : decode_any W_6b194 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b198 : bv 32 := 0x17213023.
Lemma F_6b198 : fetch_word Ubsan.M.loaded_segments (0x6b198 : word) = Some W_6b198.
Proof. vm_refl. Qed.
Lemma D_6b198 : decode_any W_6b198 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b19c : bv 32 := 0x00058413.
Lemma F_6b19c : fetch_word Ubsan.M.loaded_segments (0x6b19c : word) = Some W_6b19c.
Proof. vm_refl. Qed.
Lemma D_6b19c : decode_any W_6b19c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1a0 : bv 32 := 0x00050493.
Lemma F_6b1a0 : fetch_word Ubsan.M.loaded_segments (0x6b1a0 : word) = Some W_6b1a0.
Proof. vm_refl. Qed.
Lemma D_6b1a0 : decode_any W_6b1a0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1a4 : bv 32 := 0x03010513.
Lemma F_6b1a4 : fetch_word Ubsan.M.loaded_segments (0x6b1a4 : word) = Some W_6b1a4.
Proof. vm_refl. Qed.
Lemma D_6b1a4 : decode_any W_6b1a4 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1a8 : bv 32 := 0x13000613.
Lemma F_6b1a8 : fetch_word Ubsan.M.loaded_segments (0x6b1a8 : word) = Some W_6b1a8.
Proof. vm_refl. Qed.
Lemma D_6b1a8 : decode_any W_6b1a8 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1ac : bv 32 := 0x00000593.
Lemma F_6b1ac : fetch_word Ubsan.M.loaded_segments (0x6b1ac : word) = Some W_6b1ac.
Proof. vm_refl. Qed.
Lemma D_6b1ac : decode_any W_6b1ac = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1b0 : bv 32 := 0x1210e0ef.
Lemma F_6b1b0 : fetch_word Ubsan.M.loaded_segments (0x6b1b0 : word) = Some W_6b1b0.
Proof. vm_refl. Qed.
Lemma D_6b1b0 : decode_any W_6b1b0 = Some (Jal 1 59680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1b4 : bv 32 := 0x00019517.
Lemma F_6b1b4 : fetch_word Ubsan.M.loaded_segments (0x6b1b4 : word) = Some W_6b1b4.
Proof. vm_refl. Qed.
Lemma D_6b1b4 : decode_any W_6b1b4 = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1b8 : bv 32 := 0x98453503.
Lemma F_6b1b8 : fetch_word Ubsan.M.loaded_segments (0x6b1b8 : word) = Some W_6b1b8.
Proof. vm_refl. Qed.
Lemma D_6b1b8 : decode_any W_6b1b8 = Some (Load SZ8 true 10 10 2436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1bc : bv 32 := 0x00953023.
Lemma F_6b1bc : fetch_word Ubsan.M.loaded_segments (0x6b1bc : word) = Some W_6b1bc.
Proof. vm_refl. Qed.
Lemma D_6b1bc : decode_any W_6b1bc = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1c0 : bv 32 := 0x0004b503.
Lemma F_6b1c0 : fetch_word Ubsan.M.loaded_segments (0x6b1c0 : word) = Some W_6b1c0.
Proof. vm_refl. Qed.
Lemma D_6b1c0 : decode_any W_6b1c0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1c4 : bv 32 := 0x00848493.
Lemma F_6b1c4 : fetch_word Ubsan.M.loaded_segments (0x6b1c4 : word) = Some W_6b1c4.
Proof. vm_refl. Qed.
Lemma D_6b1c4 : decode_any W_6b1c4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1c8 : bv 32 := 0xfe051ce3.
Lemma F_6b1c8 : fetch_word Ubsan.M.loaded_segments (0x6b1c8 : word) = Some W_6b1c8.
Proof. vm_refl. Qed.
Lemma D_6b1c8 : decode_any W_6b1c8 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1cc : bv 32 := 0x0004c517.
Lemma F_6b1cc : fetch_word Ubsan.M.loaded_segments (0x6b1cc : word) = Some W_6b1cc.
Proof. vm_refl. Qed.
Lemma D_6b1cc : decode_any W_6b1cc = Some (Auipc 10 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1d0 : bv 32 := 0xa3450913.
Lemma F_6b1d0 : fetch_word Ubsan.M.loaded_segments (0x6b1d0 : word) = Some W_6b1d0.
Proof. vm_refl. Qed.
Lemma D_6b1d0 : decode_any W_6b1d0 = Some (OpImm ALU_ADD 18 10 2612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1d4 : bv 32 := 0x00993423.
Lemma F_6b1d4 : fetch_word Ubsan.M.loaded_segments (0x6b1d4 : word) = Some W_6b1d4.
Proof. vm_refl. Qed.
Lemma D_6b1d4 : decode_any W_6b1d4 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1d8 : bv 32 := 0x0004b583.
Lemma F_6b1d8 : fetch_word Ubsan.M.loaded_segments (0x6b1d8 : word) = Some W_6b1d8.
Proof. vm_refl. Qed.
Lemma D_6b1d8 : decode_any W_6b1d8 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1dc : bv 32 := 0x04058c63.
Lemma F_6b1dc : fetch_word Ubsan.M.loaded_segments (0x6b1dc : word) = Some W_6b1dc.
Proof. vm_refl. Qed.
Lemma D_6b1dc : decode_any W_6b1dc = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1e0 : bv 32 := 0x01048493.
Lemma F_6b1e0 : fetch_word Ubsan.M.loaded_segments (0x6b1e0 : word) = Some W_6b1e0.
Proof. vm_refl. Qed.
Lemma D_6b1e0 : decode_any W_6b1e0 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1e4 : bv 32 := 0x02500513.
Lemma F_6b1e4 : fetch_word Ubsan.M.loaded_segments (0x6b1e4 : word) = Some W_6b1e4.
Proof. vm_refl. Qed.
Lemma D_6b1e4 : decode_any W_6b1e4 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1e8 : bv 32 := 0x03010613.
Lemma F_6b1e8 : fetch_word Ubsan.M.loaded_segments (0x6b1e8 : word) = Some W_6b1e8.
Proof. vm_refl. Qed.
Lemma D_6b1e8 : decode_any W_6b1e8 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1ec : bv 32 := 0x0100006f.
Lemma F_6b1ec : fetch_word Ubsan.M.loaded_segments (0x6b1ec : word) = Some W_6b1ec.
Proof. vm_refl. Qed.
Lemma D_6b1ec : decode_any W_6b1ec = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1f0 : bv 32 := 0x0004b583.
Lemma F_6b1f0 : fetch_word Ubsan.M.loaded_segments (0x6b1f0 : word) = Some W_6b1f0.
Proof. vm_refl. Qed.
Lemma D_6b1f0 : decode_any W_6b1f0 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1f4 : bv 32 := 0x01048493.
Lemma F_6b1f4 : fetch_word Ubsan.M.loaded_segments (0x6b1f4 : word) = Some W_6b1f4.
Proof. vm_refl. Qed.
Lemma D_6b1f4 : decode_any W_6b1f4 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1f8 : bv 32 := 0x00058e63.
Lemma F_6b1f8 : fetch_word Ubsan.M.loaded_segments (0x6b1f8 : word) = Some W_6b1f8.
Proof. vm_refl. Qed.
Lemma D_6b1f8 : decode_any W_6b1f8 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b1fc : bv 32 := 0xfeb56ae3.
Lemma F_6b1fc : fetch_word Ubsan.M.loaded_segments (0x6b1fc : word) = Some W_6b1fc.
Proof. vm_refl. Qed.
Lemma D_6b1fc : decode_any W_6b1fc = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b200 : bv 32 := 0xff84b683.
Lemma F_6b200 : fetch_word Ubsan.M.loaded_segments (0x6b200 : word) = Some W_6b200.
Proof. vm_refl. Qed.
Lemma D_6b200 : decode_any W_6b200 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b204 : bv 32 := 0x00359593.
Lemma F_6b204 : fetch_word Ubsan.M.loaded_segments (0x6b204 : word) = Some W_6b204.
Proof. vm_refl. Qed.
Lemma D_6b204 : decode_any W_6b204 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b208 : bv 32 := 0x00b605b3.
Lemma F_6b208 : fetch_word Ubsan.M.loaded_segments (0x6b208 : word) = Some W_6b208.
Proof. vm_refl. Qed.
Lemma D_6b208 : decode_any W_6b208 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b20c : bv 32 := 0x00d5b023.
Lemma F_6b20c : fetch_word Ubsan.M.loaded_segments (0x6b20c : word) = Some W_6b20c.
Proof. vm_refl. Qed.
Lemma D_6b20c : decode_any W_6b20c = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b210 : bv 32 := 0xfe1ff06f.
Lemma F_6b210 : fetch_word Ubsan.M.loaded_segments (0x6b210 : word) = Some W_6b210.
Proof. vm_refl. Qed.
Lemma D_6b210 : decode_any W_6b210 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b214 : bv 32 := 0x0b013583.
Lemma F_6b214 : fetch_word Ubsan.M.loaded_segments (0x6b214 : word) = Some W_6b214.
Proof. vm_refl. Qed.
Lemma D_6b214 : decode_any W_6b214 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b218 : bv 32 := 0x13013503.
Lemma F_6b218 : fetch_word Ubsan.M.loaded_segments (0x6b218 : word) = Some W_6b218.
Proof. vm_refl. Qed.
Lemma D_6b218 : decode_any W_6b218 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b21c : bv 32 := 0x0004c617.
Lemma F_6b21c : fetch_word Ubsan.M.loaded_segments (0x6b21c : word) = Some W_6b21c.
Proof. vm_refl. Qed.
Lemma D_6b21c : decode_any W_6b21c = Some (Auipc 12 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b220 : bv 32 := 0xa4b63623.
Lemma F_6b220 : fetch_word Ubsan.M.loaded_segments (0x6b220 : word) = Some W_6b220.
Proof. vm_refl. Qed.
Lemma D_6b220 : decode_any W_6b220 = Some (Store SZ8 12 11 2636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b224 : bv 32 := 0x00050c63.
Lemma F_6b224 : fetch_word Ubsan.M.loaded_segments (0x6b224 : word) = Some W_6b224.
Proof. vm_refl. Qed.
Lemma D_6b224 : decode_any W_6b224 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b228 : bv 32 := 0x0004c597.
Lemma F_6b228 : fetch_word Ubsan.M.loaded_segments (0x6b228 : word) = Some W_6b228.
Proof. vm_refl. Qed.
Lemma D_6b228 : decode_any W_6b228 = Some (Auipc 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b22c : bv 32 := 0x9ca5b023.
Lemma F_6b22c : fetch_word Ubsan.M.loaded_segments (0x6b22c : word) = Some W_6b22c.
Proof. vm_refl. Qed.
Lemma D_6b22c : decode_any W_6b22c = Some (Store SZ8 11 10 2496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b230 : bv 32 := 0x00c0006f.
Lemma F_6b230 : fetch_word Ubsan.M.loaded_segments (0x6b230 : word) = Some W_6b230.
Proof. vm_refl. Qed.
Lemma D_6b230 : decode_any W_6b230 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b234 : bv 32 := 0x0004c517.
Lemma F_6b234 : fetch_word Ubsan.M.loaded_segments (0x6b234 : word) = Some W_6b234.
Proof. vm_refl. Qed.
Lemma D_6b234 : decode_any W_6b234 = Some (Auipc 10 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b238 : bv 32 := 0xa2053a23.
Lemma F_6b238 : fetch_word Ubsan.M.loaded_segments (0x6b238 : word) = Some W_6b238.
Proof. vm_refl. Qed.
Lemma D_6b238 : decode_any W_6b238 = Some (Store SZ8 10 0 2612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b23c : bv 32 := 0x06013503.
Lemma F_6b23c : fetch_word Ubsan.M.loaded_segments (0x6b23c : word) = Some W_6b23c.
Proof. vm_refl. Qed.
Lemma D_6b23c : decode_any W_6b23c = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b240 : bv 32 := 0x02a93823.
Lemma F_6b240 : fetch_word Ubsan.M.loaded_segments (0x6b240 : word) = Some W_6b240.
Proof. vm_refl. Qed.
Lemma D_6b240 : decode_any W_6b240 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b244 : bv 32 := 0x00041463.
Lemma F_6b244 : fetch_word Ubsan.M.loaded_segments (0x6b244 : word) = Some W_6b244.
Proof. vm_refl. Qed.
Lemma D_6b244 : decode_any W_6b244 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b248 : bv 32 := 0x12813403.
Lemma F_6b248 : fetch_word Ubsan.M.loaded_segments (0x6b248 : word) = Some W_6b248.
Proof. vm_refl. Qed.
Lemma D_6b248 : decode_any W_6b248 = Some (Load SZ8 true 8 2 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b24c : bv 32 := 0x00041663.
Lemma F_6b24c : fetch_word Ubsan.M.loaded_segments (0x6b24c : word) = Some W_6b24c.
Proof. vm_refl. Qed.
Lemma D_6b24c : decode_any W_6b24c = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b250 : bv 32 := 0xfffa6517.
Lemma F_6b250 : fetch_word Ubsan.M.loaded_segments (0x6b250 : word) = Some W_6b250.
Proof. vm_refl. Qed.
Lemma D_6b250 : decode_any W_6b250 = Some (Auipc 10 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b254 : bv 32 := 0x22b50413.
Lemma F_6b254 : fetch_word Ubsan.M.loaded_segments (0x6b254 : word) = Some W_6b254.
Proof. vm_refl. Qed.
Lemma D_6b254 : decode_any W_6b254 = Some (OpImm ALU_ADD 8 10 555, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b258 : bv 32 := 0x00019517.
Lemma F_6b258 : fetch_word Ubsan.M.loaded_segments (0x6b258 : word) = Some W_6b258.
Proof. vm_refl. Qed.
Lemma D_6b258 : decode_any W_6b258 = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b25c : bv 32 := 0x8e853583.
Lemma F_6b25c : fetch_word Ubsan.M.loaded_segments (0x6b25c : word) = Some W_6b25c.
Proof. vm_refl. Qed.
Lemma D_6b25c : decode_any W_6b25c = Some (Load SZ8 true 11 10 2280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b260 : bv 32 := 0x00019517.
Lemma F_6b260 : fetch_word Ubsan.M.loaded_segments (0x6b260 : word) = Some W_6b260.
Proof. vm_refl. Qed.
Lemma D_6b260 : decode_any W_6b260 = Some (Auipc 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b264 : bv 32 := 0x8e853503.
Lemma F_6b264 : fetch_word Ubsan.M.loaded_segments (0x6b264 : word) = Some W_6b264.
Proof. vm_refl. Qed.
Lemma D_6b264 : decode_any W_6b264 = Some (Load SZ8 true 10 10 2280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b268 : bv 32 := 0x0085b023.
Lemma F_6b268 : fetch_word Ubsan.M.loaded_segments (0x6b268 : word) = Some W_6b268.
Proof. vm_refl. Qed.
Lemma D_6b268 : decode_any W_6b268 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b26c : bv 32 := 0x00140593.
Lemma F_6b26c : fetch_word Ubsan.M.loaded_segments (0x6b26c : word) = Some W_6b26c.
Proof. vm_refl. Qed.
Lemma D_6b26c : decode_any W_6b26c = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b270 : bv 32 := 0x00853023.
Lemma F_6b270 : fetch_word Ubsan.M.loaded_segments (0x6b270 : word) = Some W_6b270.
Proof. vm_refl. Qed.
Lemma D_6b270 : decode_any W_6b270 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b274 : bv 32 := 0x02f00613.
Lemma F_6b274 : fetch_word Ubsan.M.loaded_segments (0x6b274 : word) = Some W_6b274.
Proof. vm_refl. Qed.
Lemma D_6b274 : decode_any W_6b274 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b278 : bv 32 := 0x00c0006f.
Lemma F_6b278 : fetch_word Ubsan.M.loaded_segments (0x6b278 : word) = Some W_6b278.
Proof. vm_refl. Qed.
Lemma D_6b278 : decode_any W_6b278 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b27c : bv 32 := 0x00b53023.
Lemma F_6b27c : fetch_word Ubsan.M.loaded_segments (0x6b27c : word) = Some W_6b27c.
Proof. vm_refl. Qed.
Lemma D_6b27c : decode_any W_6b27c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b280 : bv 32 := 0x00158593.
Lemma F_6b280 : fetch_word Ubsan.M.loaded_segments (0x6b280 : word) = Some W_6b280.
Proof. vm_refl. Qed.
Lemma D_6b280 : decode_any W_6b280 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b284 : bv 32 := 0xfff5c683.
Lemma F_6b284 : fetch_word Ubsan.M.loaded_segments (0x6b284 : word) = Some W_6b284.
Proof. vm_refl. Qed.
Lemma D_6b284 : decode_any W_6b284 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b288 : bv 32 := 0xfec68ae3.
Lemma F_6b288 : fetch_word Ubsan.M.loaded_segments (0x6b288 : word) = Some W_6b288.
Proof. vm_refl. Qed.
Lemma D_6b288 : decode_any W_6b288 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b28c : bv 32 := 0xfe069ae3.
Lemma F_6b28c : fetch_word Ubsan.M.loaded_segments (0x6b28c : word) = Some W_6b28c.
Proof. vm_refl. Qed.
Lemma D_6b28c : decode_any W_6b28c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b290 : bv 32 := 0x03010513.
Lemma F_6b290 : fetch_word Ubsan.M.loaded_segments (0x6b290 : word) = Some W_6b290.
Proof. vm_refl. Qed.
Lemma D_6b290 : decode_any W_6b290 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b294 : bv 32 := 0x2ec000ef.
Lemma F_6b294 : fetch_word Ubsan.M.loaded_segments (0x6b294 : word) = Some W_6b294.
Proof. vm_refl. Qed.
Lemma D_6b294 : decode_any W_6b294 = Some (Jal 1 748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b298 : bv 32 := 0x0f813503.
Lemma F_6b298 : fetch_word Ubsan.M.loaded_segments (0x6b298 : word) = Some W_6b298.
Proof. vm_refl. Qed.
Lemma D_6b298 : decode_any W_6b298 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b29c : bv 32 := 0x594000ef.
Lemma F_6b29c : fetch_word Ubsan.M.loaded_segments (0x6b29c : word) = Some W_6b29c.
Proof. vm_refl. Qed.
Lemma D_6b29c : decode_any W_6b29c = Some (Jal 1 1428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2a0 : bv 32 := 0x08813503.
Lemma F_6b2a0 : fetch_word Ubsan.M.loaded_segments (0x6b2a0 : word) = Some W_6b2a0.
Proof. vm_refl. Qed.
Lemma D_6b2a0 : decode_any W_6b2a0 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2a4 : bv 32 := 0x09013583.
Lemma F_6b2a4 : fetch_word Ubsan.M.loaded_segments (0x6b2a4 : word) = Some W_6b2a4.
Proof. vm_refl. Qed.
Lemma D_6b2a4 : decode_any W_6b2a4 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2a8 : bv 32 := 0x00b51c63.
Lemma F_6b2a8 : fetch_word Ubsan.M.loaded_segments (0x6b2a8 : word) = Some W_6b2a8.
Proof. vm_refl. Qed.
Lemma D_6b2a8 : decode_any W_6b2a8 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2ac : bv 32 := 0x09813503.
Lemma F_6b2ac : fetch_word Ubsan.M.loaded_segments (0x6b2ac : word) = Some W_6b2ac.
Proof. vm_refl. Qed.
Lemma D_6b2ac : decode_any W_6b2ac = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2b0 : bv 32 := 0x0a013583.
Lemma F_6b2b0 : fetch_word Ubsan.M.loaded_segments (0x6b2b0 : word) = Some W_6b2b0.
Proof. vm_refl. Qed.
Lemma D_6b2b0 : decode_any W_6b2b0 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2b4 : bv 32 := 0x00b51663.
Lemma F_6b2b4 : fetch_word Ubsan.M.loaded_segments (0x6b2b4 : word) = Some W_6b2b4.
Proof. vm_refl. Qed.
Lemma D_6b2b4 : decode_any W_6b2b4 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2b8 : bv 32 := 0x0e813503.
Lemma F_6b2b8 : fetch_word Ubsan.M.loaded_segments (0x6b2b8 : word) = Some W_6b2b8.
Proof. vm_refl. Qed.
Lemma D_6b2b8 : decode_any W_6b2b8 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2bc : bv 32 := 0x0e050063.
Lemma F_6b2bc : fetch_word Ubsan.M.loaded_segments (0x6b2bc : word) = Some W_6b2bc.
Proof. vm_refl. Qed.
Lemma D_6b2bc : decode_any W_6b2bc = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2c0 : bv 32 := 0x00200693.
Lemma F_6b2c0 : fetch_word Ubsan.M.loaded_segments (0x6b2c0 : word) = Some W_6b2c0.
Proof. vm_refl. Qed.
Lemma D_6b2c0 : decode_any W_6b2c0 = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2c4 : bv 32 := 0x00100793.
Lemma F_6b2c4 : fetch_word Ubsan.M.loaded_segments (0x6b2c4 : word) = Some W_6b2c4.
Proof. vm_refl. Qed.
Lemma D_6b2c4 : decode_any W_6b2c4 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2c8 : bv 32 := 0x00013423.
Lemma F_6b2c8 : fetch_word Ubsan.M.loaded_segments (0x6b2c8 : word) = Some W_6b2c8.
Proof. vm_refl. Qed.
Lemma D_6b2c8 : decode_any W_6b2c8 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2cc : bv 32 := 0x00013823.
Lemma F_6b2cc : fetch_word Ubsan.M.loaded_segments (0x6b2cc : word) = Some W_6b2cc.
Proof. vm_refl. Qed.
Lemma D_6b2cc : decode_any W_6b2cc = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2d0 : bv 32 := 0x04900893.
Lemma F_6b2d0 : fetch_word Ubsan.M.loaded_segments (0x6b2d0 : word) = Some W_6b2d0.
Proof. vm_refl. Qed.
Lemma D_6b2d0 : decode_any W_6b2d0 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2d4 : bv 32 := 0x01810513.
Lemma F_6b2d4 : fetch_word Ubsan.M.loaded_segments (0x6b2d4 : word) = Some W_6b2d4.
Proof. vm_refl. Qed.
Lemma D_6b2d4 : decode_any W_6b2d4 = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2d8 : bv 32 := 0x00300593.
Lemma F_6b2d8 : fetch_word Ubsan.M.loaded_segments (0x6b2d8 : word) = Some W_6b2d8.
Proof. vm_refl. Qed.
Lemma D_6b2d8 : decode_any W_6b2d8 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2dc : bv 32 := 0x00810613.
Lemma F_6b2dc : fetch_word Ubsan.M.loaded_segments (0x6b2dc : word) = Some W_6b2dc.
Proof. vm_refl. Qed.
Lemma D_6b2dc : decode_any W_6b2dc = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2e0 : bv 32 := 0x00800713.
Lemma F_6b2e0 : fetch_word Ubsan.M.loaded_segments (0x6b2e0 : word) = Some W_6b2e0.
Proof. vm_refl. Qed.
Lemma D_6b2e0 : decode_any W_6b2e0 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2e4 : bv 32 := 0x00013c23.
Lemma F_6b2e4 : fetch_word Ubsan.M.loaded_segments (0x6b2e4 : word) = Some W_6b2e4.
Proof. vm_refl. Qed.
Lemma D_6b2e4 : decode_any W_6b2e4 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2e8 : bv 32 := 0x02f13023.
Lemma F_6b2e8 : fetch_word Ubsan.M.loaded_segments (0x6b2e8 : word) = Some W_6b2e8.
Proof. vm_refl. Qed.
Lemma D_6b2e8 : decode_any W_6b2e8 = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2ec : bv 32 := 0x02d13423.
Lemma F_6b2ec : fetch_word Ubsan.M.loaded_segments (0x6b2ec : word) = Some W_6b2ec.
Proof. vm_refl. Qed.
Lemma D_6b2ec : decode_any W_6b2ec = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2f0 : bv 32 := 0x00000693.
Lemma F_6b2f0 : fetch_word Ubsan.M.loaded_segments (0x6b2f0 : word) = Some W_6b2f0.
Proof. vm_refl. Qed.
Lemma D_6b2f0 : decode_any W_6b2f0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2f4 : bv 32 := 0x00000073.
Lemma F_6b2f4 : fetch_word Ubsan.M.loaded_segments (0x6b2f4 : word) = Some W_6b2f4.
Proof. vm_refl. Qed.
Lemma D_6b2f4 : decode_any W_6b2f4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6b2f4 : is_ecall W_6b2f4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b2f8 : bv 32 := 0x02051513.
Lemma F_6b2f8 : fetch_word Ubsan.M.loaded_segments (0x6b2f8 : word) = Some W_6b2f8.
Proof. vm_refl. Qed.
Lemma D_6b2f8 : decode_any W_6b2f8 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b2fc : bv 32 := 0x00055463.
Lemma F_6b2fc : fetch_word Ubsan.M.loaded_segments (0x6b2fc : word) = Some W_6b2fc.
Proof. vm_refl. Qed.
Lemma D_6b2fc : decode_any W_6b2fc = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b300 : bv 32 := 0x00000023.
Lemma F_6b300 : fetch_word Ubsan.M.loaded_segments (0x6b300 : word) = Some W_6b300.
Proof. vm_refl. Qed.
Lemma D_6b300 : decode_any W_6b300 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b304 : bv 32 := 0x01e15503.
Lemma F_6b304 : fetch_word Ubsan.M.loaded_segments (0x6b304 : word) = Some W_6b304.
Proof. vm_refl. Qed.
Lemma D_6b304 : decode_any W_6b304 = Some (Load SZ2 false 10 2 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b308 : bv 32 := 0x02057513.
Lemma F_6b308 : fetch_word Ubsan.M.loaded_segments (0x6b308 : word) = Some W_6b308.
Proof. vm_refl. Qed.
Lemma D_6b308 : decode_any W_6b308 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b30c : bv 32 := 0x02050463.
Lemma F_6b30c : fetch_word Ubsan.M.loaded_segments (0x6b30c : word) = Some W_6b30c.
Proof. vm_refl. Qed.
Lemma D_6b30c : decode_any W_6b30c = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b310 : bv 32 := 0xfffaa517.
Lemma F_6b310 : fetch_word Ubsan.M.loaded_segments (0x6b310 : word) = Some W_6b310.
Proof. vm_refl. Qed.
Lemma D_6b310 : decode_any W_6b310 = Some (Auipc 10 1048490, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b314 : bv 32 := 0x00008637.
Lemma F_6b314 : fetch_word Ubsan.M.loaded_segments (0x6b314 : word) = Some W_6b314.
Proof. vm_refl. Qed.
Lemma D_6b314 : decode_any W_6b314 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b318 : bv 32 := 0x03800893.
Lemma F_6b318 : fetch_word Ubsan.M.loaded_segments (0x6b318 : word) = Some W_6b318.
Proof. vm_refl. Qed.
Lemma D_6b318 : decode_any W_6b318 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b31c : bv 32 := 0xaff50593.
Lemma F_6b31c : fetch_word Ubsan.M.loaded_segments (0x6b31c : word) = Some W_6b31c.
Proof. vm_refl. Qed.
Lemma D_6b31c : decode_any W_6b31c = Some (OpImm ALU_ADD 11 10 2815, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b320 : bv 32 := 0x0026061b.
Lemma F_6b320 : fetch_word Ubsan.M.loaded_segments (0x6b320 : word) = Some W_6b320.
Proof. vm_refl. Qed.
Lemma D_6b320 : decode_any W_6b320 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b324 : bv 32 := 0xf9c00513.
Lemma F_6b324 : fetch_word Ubsan.M.loaded_segments (0x6b324 : word) = Some W_6b324.
Proof. vm_refl. Qed.
Lemma D_6b324 : decode_any W_6b324 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b328 : bv 32 := 0x00000073.
Lemma F_6b328 : fetch_word Ubsan.M.loaded_segments (0x6b328 : word) = Some W_6b328.
Proof. vm_refl. Qed.
Lemma D_6b328 : decode_any W_6b328 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6b328 : is_ecall W_6b328 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b32c : bv 32 := 0x00055463.
Lemma F_6b32c : fetch_word Ubsan.M.loaded_segments (0x6b32c : word) = Some W_6b32c.
Proof. vm_refl. Qed.
Lemma D_6b32c : decode_any W_6b32c = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b330 : bv 32 := 0x00000023.
Lemma F_6b330 : fetch_word Ubsan.M.loaded_segments (0x6b330 : word) = Some W_6b330.
Proof. vm_refl. Qed.
Lemma D_6b330 : decode_any W_6b330 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b334 : bv 32 := 0x02615503.
Lemma F_6b334 : fetch_word Ubsan.M.loaded_segments (0x6b334 : word) = Some W_6b334.
Proof. vm_refl. Qed.
Lemma D_6b334 : decode_any W_6b334 = Some (Load SZ2 false 10 2 38, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b338 : bv 32 := 0x02057513.
Lemma F_6b338 : fetch_word Ubsan.M.loaded_segments (0x6b338 : word) = Some W_6b338.
Proof. vm_refl. Qed.
Lemma D_6b338 : decode_any W_6b338 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b33c : bv 32 := 0x02050463.
Lemma F_6b33c : fetch_word Ubsan.M.loaded_segments (0x6b33c : word) = Some W_6b33c.
Proof. vm_refl. Qed.
Lemma D_6b33c : decode_any W_6b33c = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b340 : bv 32 := 0xfffaa517.
Lemma F_6b340 : fetch_word Ubsan.M.loaded_segments (0x6b340 : word) = Some W_6b340.
Proof. vm_refl. Qed.
Lemma D_6b340 : decode_any W_6b340 = Some (Auipc 10 1048490, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b344 : bv 32 := 0x00008637.
Lemma F_6b344 : fetch_word Ubsan.M.loaded_segments (0x6b344 : word) = Some W_6b344.
Proof. vm_refl. Qed.
Lemma D_6b344 : decode_any W_6b344 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b348 : bv 32 := 0x03800893.
Lemma F_6b348 : fetch_word Ubsan.M.loaded_segments (0x6b348 : word) = Some W_6b348.
Proof. vm_refl. Qed.
Lemma D_6b348 : decode_any W_6b348 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b34c : bv 32 := 0xacf50593.
Lemma F_6b34c : fetch_word Ubsan.M.loaded_segments (0x6b34c : word) = Some W_6b34c.
Proof. vm_refl. Qed.
Lemma D_6b34c : decode_any W_6b34c = Some (OpImm ALU_ADD 11 10 2767, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b350 : bv 32 := 0x0026061b.
Lemma F_6b350 : fetch_word Ubsan.M.loaded_segments (0x6b350 : word) = Some W_6b350.
Proof. vm_refl. Qed.
Lemma D_6b350 : decode_any W_6b350 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b354 : bv 32 := 0xf9c00513.
Lemma F_6b354 : fetch_word Ubsan.M.loaded_segments (0x6b354 : word) = Some W_6b354.
Proof. vm_refl. Qed.
Lemma D_6b354 : decode_any W_6b354 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b358 : bv 32 := 0x00000073.
Lemma F_6b358 : fetch_word Ubsan.M.loaded_segments (0x6b358 : word) = Some W_6b358.
Proof. vm_refl. Qed.
Lemma D_6b358 : decode_any W_6b358 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6b358 : is_ecall W_6b358 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b35c : bv 32 := 0x00055463.
Lemma F_6b35c : fetch_word Ubsan.M.loaded_segments (0x6b35c : word) = Some W_6b35c.
Proof. vm_refl. Qed.
Lemma D_6b35c : decode_any W_6b35c = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b360 : bv 32 := 0x00000023.
Lemma F_6b360 : fetch_word Ubsan.M.loaded_segments (0x6b360 : word) = Some W_6b360.
Proof. vm_refl. Qed.
Lemma D_6b360 : decode_any W_6b360 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b364 : bv 32 := 0x02e15503.
Lemma F_6b364 : fetch_word Ubsan.M.loaded_segments (0x6b364 : word) = Some W_6b364.
Proof. vm_refl. Qed.
Lemma D_6b364 : decode_any W_6b364 = Some (Load SZ2 false 10 2 46, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b368 : bv 32 := 0x02057513.
Lemma F_6b368 : fetch_word Ubsan.M.loaded_segments (0x6b368 : word) = Some W_6b368.
Proof. vm_refl. Qed.
Lemma D_6b368 : decode_any W_6b368 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b36c : bv 32 := 0x02050463.
Lemma F_6b36c : fetch_word Ubsan.M.loaded_segments (0x6b36c : word) = Some W_6b36c.
Proof. vm_refl. Qed.
Lemma D_6b36c : decode_any W_6b36c = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b370 : bv 32 := 0xfffaa517.
Lemma F_6b370 : fetch_word Ubsan.M.loaded_segments (0x6b370 : word) = Some W_6b370.
Proof. vm_refl. Qed.
Lemma D_6b370 : decode_any W_6b370 = Some (Auipc 10 1048490, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b374 : bv 32 := 0x00008637.
Lemma F_6b374 : fetch_word Ubsan.M.loaded_segments (0x6b374 : word) = Some W_6b374.
Proof. vm_refl. Qed.
Lemma D_6b374 : decode_any W_6b374 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b378 : bv 32 := 0x03800893.
Lemma F_6b378 : fetch_word Ubsan.M.loaded_segments (0x6b378 : word) = Some W_6b378.
Proof. vm_refl. Qed.
Lemma D_6b378 : decode_any W_6b378 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b37c : bv 32 := 0xa9f50593.
Lemma F_6b37c : fetch_word Ubsan.M.loaded_segments (0x6b37c : word) = Some W_6b37c.
Proof. vm_refl. Qed.
Lemma D_6b37c : decode_any W_6b37c = Some (OpImm ALU_ADD 11 10 2719, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b380 : bv 32 := 0x0026061b.
Lemma F_6b380 : fetch_word Ubsan.M.loaded_segments (0x6b380 : word) = Some W_6b380.
Proof. vm_refl. Qed.
Lemma D_6b380 : decode_any W_6b380 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b384 : bv 32 := 0xf9c00513.
Lemma F_6b384 : fetch_word Ubsan.M.loaded_segments (0x6b384 : word) = Some W_6b384.
Proof. vm_refl. Qed.
Lemma D_6b384 : decode_any W_6b384 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b388 : bv 32 := 0x00000073.
Lemma F_6b388 : fetch_word Ubsan.M.loaded_segments (0x6b388 : word) = Some W_6b388.
Proof. vm_refl. Qed.
Lemma D_6b388 : decode_any W_6b388 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6b388 : is_ecall W_6b388 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6b38c : bv 32 := 0x00055463.
Lemma F_6b38c : fetch_word Ubsan.M.loaded_segments (0x6b38c : word) = Some W_6b38c.
Proof. vm_refl. Qed.
Lemma D_6b38c : decode_any W_6b38c = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b390 : bv 32 := 0x00000023.
Lemma F_6b390 : fetch_word Ubsan.M.loaded_segments (0x6b390 : word) = Some W_6b390.
Proof. vm_refl. Qed.
Lemma D_6b390 : decode_any W_6b390 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b394 : bv 32 := 0x00100513.
Lemma F_6b394 : fetch_word Ubsan.M.loaded_segments (0x6b394 : word) = Some W_6b394.
Proof. vm_refl. Qed.
Lemma D_6b394 : decode_any W_6b394 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b398 : bv 32 := 0x00a90123.
Lemma F_6b398 : fetch_word Ubsan.M.loaded_segments (0x6b398 : word) = Some W_6b398.
Proof. vm_refl. Qed.
Lemma D_6b398 : decode_any W_6b398 = Some (Store SZ1 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b39c : bv 32 := 0x17813083.
Lemma F_6b39c : fetch_word Ubsan.M.loaded_segments (0x6b39c : word) = Some W_6b39c.
Proof. vm_refl. Qed.
Lemma D_6b39c : decode_any W_6b39c = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3a0 : bv 32 := 0x17013403.
Lemma F_6b3a0 : fetch_word Ubsan.M.loaded_segments (0x6b3a0 : word) = Some W_6b3a0.
Proof. vm_refl. Qed.
Lemma D_6b3a0 : decode_any W_6b3a0 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3a4 : bv 32 := 0x16813483.
Lemma F_6b3a4 : fetch_word Ubsan.M.loaded_segments (0x6b3a4 : word) = Some W_6b3a4.
Proof. vm_refl. Qed.
Lemma D_6b3a4 : decode_any W_6b3a4 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3a8 : bv 32 := 0x16013903.
Lemma F_6b3a8 : fetch_word Ubsan.M.loaded_segments (0x6b3a8 : word) = Some W_6b3a8.
Proof. vm_refl. Qed.
Lemma D_6b3a8 : decode_any W_6b3a8 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3ac : bv 32 := 0x18010113.
Lemma F_6b3ac : fetch_word Ubsan.M.loaded_segments (0x6b3ac : word) = Some W_6b3ac.
Proof. vm_refl. Qed.
Lemma D_6b3ac : decode_any W_6b3ac = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3b0 : bv 32 := 0x00008067.
Lemma F_6b3b0 : fetch_word Ubsan.M.loaded_segments (0x6b3b0 : word) = Some W_6b3b0.
Proof. vm_refl. Qed.
Lemma D_6b3b0 : decode_any W_6b3b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3b4 : bv 32 := 0xfe010113.
Lemma F_6b3b4 : fetch_word Ubsan.M.loaded_segments (0x6b3b4 : word) = Some W_6b3b4.
Proof. vm_refl. Qed.
Lemma D_6b3b4 : decode_any W_6b3b4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3b8 : bv 32 := 0x00113c23.
Lemma F_6b3b8 : fetch_word Ubsan.M.loaded_segments (0x6b3b8 : word) = Some W_6b3b8.
Proof. vm_refl. Qed.
Lemma D_6b3b8 : decode_any W_6b3b8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3bc : bv 32 := 0x00813823.
Lemma F_6b3bc : fetch_word Ubsan.M.loaded_segments (0x6b3bc : word) = Some W_6b3bc.
Proof. vm_refl. Qed.
Lemma D_6b3bc : decode_any W_6b3bc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3c0 : bv 32 := 0x00913423.
Lemma F_6b3c0 : fetch_word Ubsan.M.loaded_segments (0x6b3c0 : word) = Some W_6b3c0.
Proof. vm_refl. Qed.
Lemma D_6b3c0 : decode_any W_6b3c0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3c4 : bv 32 := 0xdc1ff0ef.
Lemma F_6b3c4 : fetch_word Ubsan.M.loaded_segments (0x6b3c4 : word) = Some W_6b3c4.
Proof. vm_refl. Qed.
Lemma D_6b3c4 : decode_any W_6b3c4 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3c8 : bv 32 := 0x00018517.
Lemma F_6b3c8 : fetch_word Ubsan.M.loaded_segments (0x6b3c8 : word) = Some W_6b3c8.
Proof. vm_refl. Qed.
Lemma D_6b3c8 : decode_any W_6b3c8 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3cc : bv 32 := 0x00018597.
Lemma F_6b3cc : fetch_word Ubsan.M.loaded_segments (0x6b3cc : word) = Some W_6b3cc.
Proof. vm_refl. Qed.
Lemma D_6b3cc : decode_any W_6b3cc = Some (Auipc 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3d0 : bv 32 := 0x78853403.
Lemma F_6b3d0 : fetch_word Ubsan.M.loaded_segments (0x6b3d0 : word) = Some W_6b3d0.
Proof. vm_refl. Qed.
Lemma D_6b3d0 : decode_any W_6b3d0 = Some (Load SZ8 true 8 10 1928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3d4 : bv 32 := 0x78c5b483.
Lemma F_6b3d4 : fetch_word Ubsan.M.loaded_segments (0x6b3d4 : word) = Some W_6b3d4.
Proof. vm_refl. Qed.
Lemma D_6b3d4 : decode_any W_6b3d4 = Some (Load SZ8 true 9 11 1932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3d8 : bv 32 := 0x0084fa63.
Lemma F_6b3d8 : fetch_word Ubsan.M.loaded_segments (0x6b3d8 : word) = Some W_6b3d8.
Proof. vm_refl. Qed.
Lemma D_6b3d8 : decode_any W_6b3d8 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3dc : bv 32 := 0x0004b503.
Lemma F_6b3dc : fetch_word Ubsan.M.loaded_segments (0x6b3dc : word) = Some W_6b3dc.
Proof. vm_refl. Qed.
Lemma D_6b3dc : decode_any W_6b3dc = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3e0 : bv 32 := 0x000500e7.
Lemma F_6b3e0 : fetch_word Ubsan.M.loaded_segments (0x6b3e0 : word) = Some W_6b3e0.
Proof. vm_refl. Qed.
Lemma D_6b3e0 : decode_any W_6b3e0 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3e4 : bv 32 := 0x00848493.
Lemma F_6b3e4 : fetch_word Ubsan.M.loaded_segments (0x6b3e4 : word) = Some W_6b3e4.
Proof. vm_refl. Qed.
Lemma D_6b3e4 : decode_any W_6b3e4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3e8 : bv 32 := 0xfe84eae3.
Lemma F_6b3e8 : fetch_word Ubsan.M.loaded_segments (0x6b3e8 : word) = Some W_6b3e8.
Proof. vm_refl. Qed.
Lemma D_6b3e8 : decode_any W_6b3e8 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3ec : bv 32 := 0x01813083.
Lemma F_6b3ec : fetch_word Ubsan.M.loaded_segments (0x6b3ec : word) = Some W_6b3ec.
Proof. vm_refl. Qed.
Lemma D_6b3ec : decode_any W_6b3ec = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3f0 : bv 32 := 0x01013403.
Lemma F_6b3f0 : fetch_word Ubsan.M.loaded_segments (0x6b3f0 : word) = Some W_6b3f0.
Proof. vm_refl. Qed.
Lemma D_6b3f0 : decode_any W_6b3f0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3f4 : bv 32 := 0x00813483.
Lemma F_6b3f4 : fetch_word Ubsan.M.loaded_segments (0x6b3f4 : word) = Some W_6b3f4.
Proof. vm_refl. Qed.
Lemma D_6b3f4 : decode_any W_6b3f4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3f8 : bv 32 := 0x02010113.
Lemma F_6b3f8 : fetch_word Ubsan.M.loaded_segments (0x6b3f8 : word) = Some W_6b3f8.
Proof. vm_refl. Qed.
Lemma D_6b3f8 : decode_any W_6b3f8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b3fc : bv 32 := 0x00008067.
Lemma F_6b3fc : fetch_word Ubsan.M.loaded_segments (0x6b3fc : word) = Some W_6b3fc.
Proof. vm_refl. Qed.
Lemma D_6b3fc : decode_any W_6b3fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b400 : bv 32 := 0xfe010113.
Lemma F_6b400 : fetch_word Ubsan.M.loaded_segments (0x6b400 : word) = Some W_6b400.
Proof. vm_refl. Qed.
Lemma D_6b400 : decode_any W_6b400 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b404 : bv 32 := 0x00113c23.
Lemma F_6b404 : fetch_word Ubsan.M.loaded_segments (0x6b404 : word) = Some W_6b404.
Proof. vm_refl. Qed.
Lemma D_6b404 : decode_any W_6b404 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b408 : bv 32 := 0x00813823.
Lemma F_6b408 : fetch_word Ubsan.M.loaded_segments (0x6b408 : word) = Some W_6b408.
Proof. vm_refl. Qed.
Lemma D_6b408 : decode_any W_6b408 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b40c : bv 32 := 0x00913423.
Lemma F_6b40c : fetch_word Ubsan.M.loaded_segments (0x6b40c : word) = Some W_6b40c.
Proof. vm_refl. Qed.
Lemma D_6b40c : decode_any W_6b40c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b410 : bv 32 := 0x01213023.
Lemma F_6b410 : fetch_word Ubsan.M.loaded_segments (0x6b410 : word) = Some W_6b410.
Proof. vm_refl. Qed.
Lemma D_6b410 : decode_any W_6b410 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b414 : bv 32 := 0x00060413.
Lemma F_6b414 : fetch_word Ubsan.M.loaded_segments (0x6b414 : word) = Some W_6b414.
Proof. vm_refl. Qed.
Lemma D_6b414 : decode_any W_6b414 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b418 : bv 32 := 0x00058493.
Lemma F_6b418 : fetch_word Ubsan.M.loaded_segments (0x6b418 : word) = Some W_6b418.
Proof. vm_refl. Qed.
Lemma D_6b418 : decode_any W_6b418 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b41c : bv 32 := 0x00050913.
Lemma F_6b41c : fetch_word Ubsan.M.loaded_segments (0x6b41c : word) = Some W_6b41c.
Proof. vm_refl. Qed.
Lemma D_6b41c : decode_any W_6b41c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b420 : bv 32 := 0x00063583.
Lemma F_6b420 : fetch_word Ubsan.M.loaded_segments (0x6b420 : word) = Some W_6b420.
Proof. vm_refl. Qed.
Lemma D_6b420 : decode_any W_6b420 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b424 : bv 32 := 0x00349513.
Lemma F_6b424 : fetch_word Ubsan.M.loaded_segments (0x6b424 : word) = Some W_6b424.
Proof. vm_refl. Qed.
Lemma D_6b424 : decode_any W_6b424 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b428 : bv 32 := 0x00a60533.
Lemma F_6b428 : fetch_word Ubsan.M.loaded_segments (0x6b428 : word) = Some W_6b428.
Proof. vm_refl. Qed.
Lemma D_6b428 : decode_any W_6b428 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b42c : bv 32 := 0x00850513.
Lemma F_6b42c : fetch_word Ubsan.M.loaded_segments (0x6b42c : word) = Some W_6b42c.
Proof. vm_refl. Qed.
Lemma D_6b42c : decode_any W_6b42c = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b430 : bv 32 := 0xd59ff0ef.
Lemma F_6b430 : fetch_word Ubsan.M.loaded_segments (0x6b430 : word) = Some W_6b430.
Proof. vm_refl. Qed.
Lemma D_6b430 : decode_any W_6b430 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b434 : bv 32 := 0x00000517.
Lemma F_6b434 : fetch_word Ubsan.M.loaded_segments (0x6b434 : word) = Some W_6b434.
Proof. vm_refl. Qed.
Lemma D_6b434 : decode_any W_6b434 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b438 : bv 32 := 0x02c50313.
Lemma F_6b438 : fetch_word Ubsan.M.loaded_segments (0x6b438 : word) = Some W_6b438.
Proof. vm_refl. Qed.
Lemma D_6b438 : decode_any W_6b438 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b43c : bv 32 := 0x00090513.
Lemma F_6b43c : fetch_word Ubsan.M.loaded_segments (0x6b43c : word) = Some W_6b43c.
Proof. vm_refl. Qed.
Lemma D_6b43c : decode_any W_6b43c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b440 : bv 32 := 0x00048593.
Lemma F_6b440 : fetch_word Ubsan.M.loaded_segments (0x6b440 : word) = Some W_6b440.
Proof. vm_refl. Qed.
Lemma D_6b440 : decode_any W_6b440 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b444 : bv 32 := 0x00040613.
Lemma F_6b444 : fetch_word Ubsan.M.loaded_segments (0x6b444 : word) = Some W_6b444.
Proof. vm_refl. Qed.
Lemma D_6b444 : decode_any W_6b444 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b448 : bv 32 := 0x01813083.
Lemma F_6b448 : fetch_word Ubsan.M.loaded_segments (0x6b448 : word) = Some W_6b448.
Proof. vm_refl. Qed.
Lemma D_6b448 : decode_any W_6b448 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b44c : bv 32 := 0x01013403.
Lemma F_6b44c : fetch_word Ubsan.M.loaded_segments (0x6b44c : word) = Some W_6b44c.
Proof. vm_refl. Qed.
Lemma D_6b44c : decode_any W_6b44c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b450 : bv 32 := 0x00813483.
Lemma F_6b450 : fetch_word Ubsan.M.loaded_segments (0x6b450 : word) = Some W_6b450.
Proof. vm_refl. Qed.
Lemma D_6b450 : decode_any W_6b450 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b454 : bv 32 := 0x00013903.
Lemma F_6b454 : fetch_word Ubsan.M.loaded_segments (0x6b454 : word) = Some W_6b454.
Proof. vm_refl. Qed.
Lemma D_6b454 : decode_any W_6b454 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b458 : bv 32 := 0x02010113.
Lemma F_6b458 : fetch_word Ubsan.M.loaded_segments (0x6b458 : word) = Some W_6b458.
Proof. vm_refl. Qed.
Lemma D_6b458 : decode_any W_6b458 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b45c : bv 32 := 0x00030067.
Lemma F_6b45c : fetch_word Ubsan.M.loaded_segments (0x6b45c : word) = Some W_6b45c.
Proof. vm_refl. Qed.
Lemma D_6b45c : decode_any W_6b45c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b460 : bv 32 := 0xfd010113.
Lemma F_6b460 : fetch_word Ubsan.M.loaded_segments (0x6b460 : word) = Some W_6b460.
Proof. vm_refl. Qed.
Lemma D_6b460 : decode_any W_6b460 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b464 : bv 32 := 0x02113423.
Lemma F_6b464 : fetch_word Ubsan.M.loaded_segments (0x6b464 : word) = Some W_6b464.
Proof. vm_refl. Qed.
Lemma D_6b464 : decode_any W_6b464 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b468 : bv 32 := 0x02813023.
Lemma F_6b468 : fetch_word Ubsan.M.loaded_segments (0x6b468 : word) = Some W_6b468.
Proof. vm_refl. Qed.
Lemma D_6b468 : decode_any W_6b468 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b46c : bv 32 := 0x00913c23.
Lemma F_6b46c : fetch_word Ubsan.M.loaded_segments (0x6b46c : word) = Some W_6b46c.
Proof. vm_refl. Qed.
Lemma D_6b46c : decode_any W_6b46c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b470 : bv 32 := 0x01213823.
Lemma F_6b470 : fetch_word Ubsan.M.loaded_segments (0x6b470 : word) = Some W_6b470.
Proof. vm_refl. Qed.
Lemma D_6b470 : decode_any W_6b470 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b474 : bv 32 := 0x01313423.
Lemma F_6b474 : fetch_word Ubsan.M.loaded_segments (0x6b474 : word) = Some W_6b474.
Proof. vm_refl. Qed.
Lemma D_6b474 : decode_any W_6b474 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b478 : bv 32 := 0x00060413.
Lemma F_6b478 : fetch_word Ubsan.M.loaded_segments (0x6b478 : word) = Some W_6b478.
Proof. vm_refl. Qed.
Lemma D_6b478 : decode_any W_6b478 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b47c : bv 32 := 0x00058493.
Lemma F_6b47c : fetch_word Ubsan.M.loaded_segments (0x6b47c : word) = Some W_6b47c.
Proof. vm_refl. Qed.
Lemma D_6b47c : decode_any W_6b47c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b480 : bv 32 := 0x00050913.
Lemma F_6b480 : fetch_word Ubsan.M.loaded_segments (0x6b480 : word) = Some W_6b480.
Proof. vm_refl. Qed.
Lemma D_6b480 : decode_any W_6b480 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b484 : bv 32 := 0x00359513.
Lemma F_6b484 : fetch_word Ubsan.M.loaded_segments (0x6b484 : word) = Some W_6b484.
Proof. vm_refl. Qed.
Lemma D_6b484 : decode_any W_6b484 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b488 : bv 32 := 0x00a60533.
Lemma F_6b488 : fetch_word Ubsan.M.loaded_segments (0x6b488 : word) = Some W_6b488.
Proof. vm_refl. Qed.
Lemma D_6b488 : decode_any W_6b488 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b48c : bv 32 := 0x00850993.
Lemma F_6b48c : fetch_word Ubsan.M.loaded_segments (0x6b48c : word) = Some W_6b48c.
Proof. vm_refl. Qed.
Lemma D_6b48c : decode_any W_6b48c = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b490 : bv 32 := 0xf25ff0ef.
Lemma F_6b490 : fetch_word Ubsan.M.loaded_segments (0x6b490 : word) = Some W_6b490.
Proof. vm_refl. Qed.
Lemma D_6b490 : decode_any W_6b490 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b494 : bv 32 := 0x00048513.
Lemma F_6b494 : fetch_word Ubsan.M.loaded_segments (0x6b494 : word) = Some W_6b494.
Proof. vm_refl. Qed.
Lemma D_6b494 : decode_any W_6b494 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b498 : bv 32 := 0x00040593.
Lemma F_6b498 : fetch_word Ubsan.M.loaded_segments (0x6b498 : word) = Some W_6b498.
Proof. vm_refl. Qed.
Lemma D_6b498 : decode_any W_6b498 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b49c : bv 32 := 0x00098613.
Lemma F_6b49c : fetch_word Ubsan.M.loaded_segments (0x6b49c : word) = Some W_6b49c.
Proof. vm_refl. Qed.
Lemma D_6b49c : decode_any W_6b49c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4a0 : bv 32 := 0x000900e7.
Lemma F_6b4a0 : fetch_word Ubsan.M.loaded_segments (0x6b4a0 : word) = Some W_6b4a0.
Proof. vm_refl. Qed.
Lemma D_6b4a0 : decode_any W_6b4a0 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6b4a4 : bv 32 := 0x700000ef.
Lemma F_6b4a4 : fetch_word Ubsan.M.loaded_segments (0x6b4a4 : word) = Some W_6b4a4.
Proof. vm_refl. Qed.
Lemma D_6b4a4 : decode_any W_6b4a4 = Some (Jal 1 1792, 4%Z).
Proof. vm_refl. Qed.
