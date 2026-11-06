(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6d928 : bv 32 := 0x00050663.
Lemma F_6d928 : fetch_word Plain.M.loaded_segments (0x6d980 : word) = Some W_6d928.
Proof. vm_refl. Qed.
Lemma D_6d928 : decode_any W_6d928 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d92c : bv 32 := 0x00852503.
Lemma F_6d92c : fetch_word Plain.M.loaded_segments (0x6d984 : word) = Some W_6d92c.
Proof. vm_refl. Qed.
Lemma D_6d92c : decode_any W_6d92c = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d930 : bv 32 := 0x00008067.
Lemma F_6d930 : fetch_word Plain.M.loaded_segments (0x6d988 : word) = Some W_6d930.
Proof. vm_refl. Qed.
Lemma D_6d930 : decode_any W_6d930 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b168 : bv 32 := 0xfa010113.
Lemma F_9b168 : fetch_word Plain.M.loaded_segments (0x9b1c0 : word) = Some W_9b168.
Proof. vm_refl. Qed.
Lemma D_9b168 : decode_any W_9b168 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b16c : bv 32 := 0x04113c23.
Lemma F_9b16c : fetch_word Plain.M.loaded_segments (0x9b1c4 : word) = Some W_9b16c.
Proof. vm_refl. Qed.
Lemma D_9b16c : decode_any W_9b16c = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b170 : bv 32 := 0x04813823.
Lemma F_9b170 : fetch_word Plain.M.loaded_segments (0x9b1c8 : word) = Some W_9b170.
Proof. vm_refl. Qed.
Lemma D_9b170 : decode_any W_9b170 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b174 : bv 32 := 0x04913423.
Lemma F_9b174 : fetch_word Plain.M.loaded_segments (0x9b1cc : word) = Some W_9b174.
Proof. vm_refl. Qed.
Lemma D_9b174 : decode_any W_9b174 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b178 : bv 32 := 0x05213023.
Lemma F_9b178 : fetch_word Plain.M.loaded_segments (0x9b1d0 : word) = Some W_9b178.
Proof. vm_refl. Qed.
Lemma D_9b178 : decode_any W_9b178 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b17c : bv 32 := 0x03313c23.
Lemma F_9b17c : fetch_word Plain.M.loaded_segments (0x9b1d4 : word) = Some W_9b17c.
Proof. vm_refl. Qed.
Lemma D_9b17c : decode_any W_9b17c = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b180 : bv 32 := 0x03413823.
Lemma F_9b180 : fetch_word Plain.M.loaded_segments (0x9b1d8 : word) = Some W_9b180.
Proof. vm_refl. Qed.
Lemma D_9b180 : decode_any W_9b180 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b184 : bv 32 := 0x02813427.
Lemma F_9b184 : fetch_word Plain.M.loaded_segments (0x9b1dc : word) = Some W_9b184.
Proof. vm_refl. Qed.
Lemma D_9b184 : decode_any W_9b184 = Some (FStore FMT_D 2 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b188 : bv 32 := 0x02913027.
Lemma F_9b188 : fetch_word Plain.M.loaded_segments (0x9b1e0 : word) = Some W_9b188.
Proof. vm_refl. Qed.
Lemma D_9b188 : decode_any W_9b188 = Some (FStore FMT_D 2 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b18c : bv 32 := 0x0e050863.
Lemma F_9b18c : fetch_word Plain.M.loaded_segments (0x9b1e4 : word) = Some W_9b18c.
Proof. vm_refl. Qed.
Lemma D_9b18c : decode_any W_9b18c = Some (Branch BC_EQ 10 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b190 : bv 32 := 0x00070913.
Lemma F_9b190 : fetch_word Plain.M.loaded_segments (0x9b1e8 : word) = Some W_9b190.
Proof. vm_refl. Qed.
Lemma D_9b190 : decode_any W_9b190 = Some (OpImm ALU_ADD 18 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b194 : bv 32 := 0x00068493.
Lemma F_9b194 : fetch_word Plain.M.loaded_segments (0x9b1ec : word) = Some W_9b194.
Proof. vm_refl. Qed.
Lemma D_9b194 : decode_any W_9b194 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b198 : bv 32 := 0x00060993.
Lemma F_9b198 : fetch_word Plain.M.loaded_segments (0x9b1f0 : word) = Some W_9b198.
Proof. vm_refl. Qed.
Lemma D_9b198 : decode_any W_9b198 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b19c : bv 32 := 0x00058a13.
Lemma F_9b19c : fetch_word Plain.M.loaded_segments (0x9b1f4 : word) = Some W_9b19c.
Proof. vm_refl. Qed.
Lemma D_9b19c : decode_any W_9b19c = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1a0 : bv 32 := 0x20b58453.
Lemma F_9b1a0 : fetch_word Plain.M.loaded_segments (0x9b1f8 : word) = Some W_9b1a0.
Proof. vm_refl. Qed.
Lemma D_9b1a0 : decode_any W_9b1a0 = Some (Fsgnj F_SGNJ FMT_S 8 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1a4 : bv 32 := 0x20a504d3.
Lemma F_9b1a4 : fetch_word Plain.M.loaded_segments (0x9b1fc : word) = Some W_9b1a4.
Proof. vm_refl. Qed.
Lemma D_9b1a4 : decode_any W_9b1a4 = Some (Fsgnj F_SGNJ FMT_S 9 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1a8 : bv 32 := 0x00050413.
Lemma F_9b1a8 : fetch_word Plain.M.loaded_segments (0x9b200 : word) = Some W_9b1a8.
Proof. vm_refl. Qed.
Lemma D_9b1a8 : decode_any W_9b1a8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1ac : bv 32 := 0xf7cd20ef.
Lemma F_9b1ac : fetch_word Plain.M.loaded_segments (0x9b204 : word) = Some W_9b1ac.
Proof. vm_refl. Qed.
Lemma D_9b1ac : decode_any W_9b1ac = Some (Jal 1 1910652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1b0 : bv 32 := 0x00100593.
Lemma F_9b1b0 : fetch_word Plain.M.loaded_segments (0x9b208 : word) = Some W_9b1b0.
Proof. vm_refl. Qed.
Lemma D_9b1b0 : decode_any W_9b1b0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1b4 : bv 32 := 0x0cb51463.
Lemma F_9b1b4 : fetch_word Plain.M.loaded_segments (0x9b20c : word) = Some W_9b1b4.
Proof. vm_refl. Qed.
Lemma D_9b1b4 : decode_any W_9b1b4 = Some (Branch BC_NE 10 11 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1b8 : bv 32 := 0x01810593.
Lemma F_9b1b8 : fetch_word Plain.M.loaded_segments (0x9b210 : word) = Some W_9b1b8.
Proof. vm_refl. Qed.
Lemma D_9b1b8 : decode_any W_9b1b8 = Some (OpImm ALU_ADD 11 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1bc : bv 32 := 0x00040513.
Lemma F_9b1bc : fetch_word Plain.M.loaded_segments (0x9b214 : word) = Some W_9b1bc.
Proof. vm_refl. Qed.
Lemma D_9b1bc : decode_any W_9b1bc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1c0 : bv 32 := 0x00000613.
Lemma F_9b1c0 : fetch_word Plain.M.loaded_segments (0x9b218 : word) = Some W_9b1c0.
Proof. vm_refl. Qed.
Lemma D_9b1c0 : decode_any W_9b1c0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1c4 : bv 32 := 0x00000693.
Lemma F_9b1c4 : fetch_word Plain.M.loaded_segments (0x9b21c : word) = Some W_9b1c4.
Proof. vm_refl. Qed.
Lemma D_9b1c4 : decode_any W_9b1c4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1c8 : bv 32 := 0x00090713.
Lemma F_9b1c8 : fetch_word Plain.M.loaded_segments (0x9b220 : word) = Some W_9b1c8.
Proof. vm_refl. Qed.
Lemma D_9b1c8 : decode_any W_9b1c8 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1cc : bv 32 := 0x218000ef.
Lemma F_9b1cc : fetch_word Plain.M.loaded_segments (0x9b224 : word) = Some W_9b1cc.
Proof. vm_refl. Qed.
Lemma D_9b1cc : decode_any W_9b1cc = Some (Jal 1 536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1d0 : bv 32 := 0x00100593.
Lemma F_9b1d0 : fetch_word Plain.M.loaded_segments (0x9b228 : word) = Some W_9b1d0.
Proof. vm_refl. Qed.
Lemma D_9b1d0 : decode_any W_9b1d0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1d4 : bv 32 := 0x00040513.
Lemma F_9b1d4 : fetch_word Plain.M.loaded_segments (0x9b22c : word) = Some W_9b1d4.
Proof. vm_refl. Qed.
Lemma D_9b1d4 : decode_any W_9b1d4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1d8 : bv 32 := 0xe10ec0ef.
Lemma F_9b1d8 : fetch_word Plain.M.loaded_segments (0x9b230 : word) = Some W_9b1d8.
Proof. vm_refl. Qed.
Lemma D_9b1d8 : decode_any W_9b1d8 = Some (Jal 1 2016784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1dc : bv 32 := 0x00a13423.
Lemma F_9b1dc : fetch_word Plain.M.loaded_segments (0x9b234 : word) = Some W_9b1dc.
Proof. vm_refl. Qed.
Lemma D_9b1dc : decode_any W_9b1dc = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1e0 : bv 32 := 0x01410593.
Lemma F_9b1e0 : fetch_word Plain.M.loaded_segments (0x9b238 : word) = Some W_9b1e0.
Proof. vm_refl. Qed.
Lemma D_9b1e0 : decode_any W_9b1e0 = Some (OpImm ALU_ADD 11 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1e4 : bv 32 := 0x00000613.
Lemma F_9b1e4 : fetch_word Plain.M.loaded_segments (0x9b23c : word) = Some W_9b1e4.
Proof. vm_refl. Qed.
Lemma D_9b1e4 : decode_any W_9b1e4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1e8 : bv 32 := 0x00000693.
Lemma F_9b1e8 : fetch_word Plain.M.loaded_segments (0x9b240 : word) = Some W_9b1e8.
Proof. vm_refl. Qed.
Lemma D_9b1e8 : decode_any W_9b1e8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1ec : bv 32 := 0x00090713.
Lemma F_9b1ec : fetch_word Plain.M.loaded_segments (0x9b244 : word) = Some W_9b1ec.
Proof. vm_refl. Qed.
Lemma D_9b1ec : decode_any W_9b1ec = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1f0 : bv 32 := 0x1f4000ef.
Lemma F_9b1f0 : fetch_word Plain.M.loaded_segments (0x9b248 : word) = Some W_9b1f0.
Proof. vm_refl. Qed.
Lemma D_9b1f0 : decode_any W_9b1f0 = Some (Jal 1 500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1f4 : bv 32 := 0x00810513.
Lemma F_9b1f4 : fetch_word Plain.M.loaded_segments (0x9b24c : word) = Some W_9b1f4.
Proof. vm_refl. Qed.
Lemma D_9b1f4 : decode_any W_9b1f4 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1f8 : bv 32 := 0x8edd10ef.
Lemma F_9b1f8 : fetch_word Plain.M.loaded_segments (0x9b250 : word) = Some W_9b1f8.
Proof. vm_refl. Qed.
Lemma D_9b1f8 : decode_any W_9b1f8 = Some (Jal 1 1906924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b1fc : bv 32 := 0x000a0663.
Lemma F_9b1fc : fetch_word Plain.M.loaded_segments (0x9b254 : word) = Some W_9b1fc.
Proof. vm_refl. Qed.
Lemma D_9b1fc : decode_any W_9b1fc = Some (Branch BC_EQ 20 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b200 : bv 32 := 0x01812787.
Lemma F_9b200 : fetch_word Plain.M.loaded_segments (0x9b258 : word) = Some W_9b200.
Proof. vm_refl. Qed.
Lemma D_9b200 : decode_any W_9b200 = Some (FLoad FMT_S 15 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b204 : bv 32 := 0x00fa2027.
Lemma F_9b204 : fetch_word Plain.M.loaded_segments (0x9b25c : word) = Some W_9b204.
Proof. vm_refl. Qed.
Lemma D_9b204 : decode_any W_9b204 = Some (FStore FMT_S 20 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b208 : bv 32 := 0x01412587.
Lemma F_9b208 : fetch_word Plain.M.loaded_segments (0x9b260 : word) = Some W_9b208.
Proof. vm_refl. Qed.
Lemma D_9b208 : decode_any W_9b208 = Some (FLoad FMT_S 11 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b20c : bv 32 := 0x00098463.
Lemma F_9b20c : fetch_word Plain.M.loaded_segments (0x9b264 : word) = Some W_9b20c.
Proof. vm_refl. Qed.
Lemma D_9b20c : decode_any W_9b20c = Some (Branch BC_EQ 19 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b210 : bv 32 := 0x00b9a027.
Lemma F_9b210 : fetch_word Plain.M.loaded_segments (0x9b268 : word) = Some W_9b210.
Proof. vm_refl. Qed.
Lemma D_9b210 : decode_any W_9b210 = Some (FStore FMT_S 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b214 : bv 32 := 0x01812507.
Lemma F_9b214 : fetch_word Plain.M.loaded_segments (0x9b26c : word) = Some W_9b214.
Proof. vm_refl. Qed.
Lemma D_9b214 : decode_any W_9b214 = Some (FLoad FMT_S 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b218 : bv 32 := 0x01c10513.
Lemma F_9b218 : fetch_word Plain.M.loaded_segments (0x9b270 : word) = Some W_9b218.
Proof. vm_refl. Qed.
Lemma D_9b218 : decode_any W_9b218 = Some (OpImm ALU_ADD 10 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b21c : bv 32 := 0x20948653.
Lemma F_9b21c : fetch_word Plain.M.loaded_segments (0x9b274 : word) = Some W_9b21c.
Proof. vm_refl. Qed.
Lemma D_9b21c : decode_any W_9b21c = Some (Fsgnj F_SGNJ FMT_S 12 9 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b220 : bv 32 := 0x208406d3.
Lemma F_9b220 : fetch_word Plain.M.loaded_segments (0x9b278 : word) = Some W_9b220.
Proof. vm_refl. Qed.
Lemma D_9b220 : decode_any W_9b220 = Some (Fsgnj F_SGNJ FMT_S 13 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b224 : bv 32 := 0x00090593.
Lemma F_9b224 : fetch_word Plain.M.loaded_segments (0x9b27c : word) = Some W_9b224.
Proof. vm_refl. Qed.
Lemma D_9b224 : decode_any W_9b224 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b228 : bv 32 := 0x71c000ef.
Lemma F_9b228 : fetch_word Plain.M.loaded_segments (0x9b280 : word) = Some W_9b228.
Proof. vm_refl. Qed.
Lemma D_9b228 : decode_any W_9b228 = Some (Jal 1 1820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b22c : bv 32 := 0x00077517.
Lemma F_9b22c : fetch_word Plain.M.loaded_segments (0x9b284 : word) = Some W_9b22c.
Proof. vm_refl. Qed.
Lemma D_9b22c : decode_any W_9b22c = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b230 : bv 32 := 0x34453503.
Lemma F_9b230 : fetch_word Plain.M.loaded_segments (0x9b288 : word) = Some W_9b230.
Proof. vm_refl. Qed.
Lemma D_9b230 : decode_any W_9b230 = Some (Load SZ8 true 10 10 836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b234 : bv 32 := 0x01c12583.
Lemma F_9b234 : fetch_word Plain.M.loaded_segments (0x9b28c : word) = Some W_9b234.
Proof. vm_refl. Qed.
Lemma D_9b234 : decode_any W_9b234 = Some (Load SZ4 true 11 2 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b238 : bv 32 := 0x00052503.
Lemma F_9b238 : fetch_word Plain.M.loaded_segments (0x9b290 : word) = Some W_9b238.
Proof. vm_refl. Qed.
Lemma D_9b238 : decode_any W_9b238 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b23c : bv 32 := 0x00400613.
Lemma F_9b23c : fetch_word Plain.M.loaded_segments (0x9b294 : word) = Some W_9b23c.
Proof. vm_refl. Qed.
Lemma D_9b23c : decode_any W_9b23c = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b240 : bv 32 := 0x14b66a63.
Lemma F_9b240 : fetch_word Plain.M.loaded_segments (0x9b298 : word) = Some W_9b240.
Proof. vm_refl. Qed.
Lemma D_9b240 : decode_any W_9b240 = Some (Branch BC_LTU 12 11 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b244 : bv 32 := 0x00259593.
Lemma F_9b244 : fetch_word Plain.M.loaded_segments (0x9b29c : word) = Some W_9b244.
Proof. vm_refl. Qed.
Lemma D_9b244 : decode_any W_9b244 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b248 : bv 32 := 0xfff85617.
Lemma F_9b248 : fetch_word Plain.M.loaded_segments (0x9b2a0 : word) = Some W_9b248.
Proof. vm_refl. Qed.
Lemma D_9b248 : decode_any W_9b248 = Some (Auipc 12 1048453, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b24c : bv 32 := 0x99460613.
Lemma F_9b24c : fetch_word Plain.M.loaded_segments (0x9b2a4 : word) = Some W_9b24c.
Proof. vm_refl. Qed.
Lemma D_9b24c : decode_any W_9b24c = Some (OpImm ALU_ADD 12 12 2452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b250 : bv 32 := 0x00c585b3.
Lemma F_9b250 : fetch_word Plain.M.loaded_segments (0x9b2a8 : word) = Some W_9b250.
Proof. vm_refl. Qed.
Lemma D_9b250 : decode_any W_9b250 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b254 : bv 32 := 0x0005a583.
Lemma F_9b254 : fetch_word Plain.M.loaded_segments (0x9b2ac : word) = Some W_9b254.
Proof. vm_refl. Qed.
Lemma D_9b254 : decode_any W_9b254 = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b258 : bv 32 := 0x00c585b3.
Lemma F_9b258 : fetch_word Plain.M.loaded_segments (0x9b2b0 : word) = Some W_9b258.
Proof. vm_refl. Qed.
Lemma D_9b258 : decode_any W_9b258 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b25c : bv 32 := 0x00058067.
Lemma F_9b25c : fetch_word Plain.M.loaded_segments (0x9b2b4 : word) = Some W_9b25c.
Proof. vm_refl. Qed.
Lemma D_9b25c : decode_any W_9b25c = Some (Jalr 0 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b260 : bv 32 := 0x00300593.
Lemma F_9b260 : fetch_word Plain.M.loaded_segments (0x9b2b8 : word) = Some W_9b260.
Proof. vm_refl. Qed.
Lemma D_9b260 : decode_any W_9b260 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b264 : bv 32 := 0x12a5c263.
Lemma F_9b264 : fetch_word Plain.M.loaded_segments (0x9b2bc : word) = Some W_9b264.
Proof. vm_refl. Qed.
Lemma D_9b264 : decode_any W_9b264 = Some (Branch BC_LT 11 10 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b268 : bv 32 := 0xfff76517.
Lemma F_9b268 : fetch_word Plain.M.loaded_segments (0x9b2c0 : word) = Some W_9b268.
Proof. vm_refl. Qed.
Lemma D_9b268 : decode_any W_9b268 = Some (Auipc 10 1048438, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b26c : bv 32 := 0xfff75597.
Lemma F_9b26c : fetch_word Plain.M.loaded_segments (0x9b2c4 : word) = Some W_9b26c.
Proof. vm_refl. Qed.
Lemma D_9b26c : decode_any W_9b26c = Some (Auipc 11 1048437, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b270 : bv 32 := 0x0eb50513.
Lemma F_9b270 : fetch_word Plain.M.loaded_segments (0x9b2c8 : word) = Some W_9b270.
Proof. vm_refl. Qed.
Lemma D_9b270 : decode_any W_9b270 = Some (OpImm ALU_ADD 10 10 235, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b274 : bv 32 := 0x29858593.
Lemma F_9b274 : fetch_word Plain.M.loaded_segments (0x9b2cc : word) = Some W_9b274.
Proof. vm_refl. Qed.
Lemma D_9b274 : decode_any W_9b274 = Some (OpImm ALU_ADD 11 11 664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b278 : bv 32 := 0x10c0006f.
Lemma F_9b278 : fetch_word Plain.M.loaded_segments (0x9b2d0 : word) = Some W_9b278.
Proof. vm_refl. Qed.
Lemma D_9b278 : decode_any W_9b278 = Some (Jal 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b27c : bv 32 := 0x00077517.
Lemma F_9b27c : fetch_word Plain.M.loaded_segments (0x9b2d4 : word) = Some W_9b27c.
Proof. vm_refl. Qed.
Lemma D_9b27c : decode_any W_9b27c = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b280 : bv 32 := 0x2f453503.
Lemma F_9b280 : fetch_word Plain.M.loaded_segments (0x9b2d8 : word) = Some W_9b280.
Proof. vm_refl. Qed.
Lemma D_9b280 : decode_any W_9b280 = Some (Load SZ8 true 10 10 756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b284 : bv 32 := 0x00052503.
Lemma F_9b284 : fetch_word Plain.M.loaded_segments (0x9b2dc : word) = Some W_9b284.
Proof. vm_refl. Qed.
Lemma D_9b284 : decode_any W_9b284 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b288 : bv 32 := 0x00500593.
Lemma F_9b288 : fetch_word Plain.M.loaded_segments (0x9b2e0 : word) = Some W_9b288.
Proof. vm_refl. Qed.
Lemma D_9b288 : decode_any W_9b288 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b28c : bv 32 := 0x04a5c063.
Lemma F_9b28c : fetch_word Plain.M.loaded_segments (0x9b2e4 : word) = Some W_9b28c.
Proof. vm_refl. Qed.
Lemma D_9b28c : decode_any W_9b28c = Some (Branch BC_LT 11 10 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b290 : bv 32 := 0xfff80517.
Lemma F_9b290 : fetch_word Plain.M.loaded_segments (0x9b2e8 : word) = Some W_9b290.
Proof. vm_refl. Qed.
Lemma D_9b290 : decode_any W_9b290 = Some (Auipc 10 1048448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b294 : bv 32 := 0xfff75597.
Lemma F_9b294 : fetch_word Plain.M.loaded_segments (0x9b2ec : word) = Some W_9b294.
Proof. vm_refl. Qed.
Lemma D_9b294 : decode_any W_9b294 = Some (Auipc 11 1048437, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b298 : bv 32 := 0x7e750513.
Lemma F_9b298 : fetch_word Plain.M.loaded_segments (0x9b2f0 : word) = Some W_9b298.
Proof. vm_refl. Qed.
Lemma D_9b298 : decode_any W_9b298 = Some (OpImm ALU_ADD 10 10 2023, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b29c : bv 32 := 0x27058593.
Lemma F_9b29c : fetch_word Plain.M.loaded_segments (0x9b2f4 : word) = Some W_9b29c.
Proof. vm_refl. Qed.
Lemma D_9b29c : decode_any W_9b29c = Some (OpImm ALU_ADD 11 11 624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2a0 : bv 32 := 0x00000613.
Lemma F_9b2a0 : fetch_word Plain.M.loaded_segments (0x9b2f8 : word) = Some W_9b2a0.
Proof. vm_refl. Qed.
Lemma D_9b2a0 : decode_any W_9b2a0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2a4 : bv 32 := 0x05813083.
Lemma F_9b2a4 : fetch_word Plain.M.loaded_segments (0x9b2fc : word) = Some W_9b2a4.
Proof. vm_refl. Qed.
Lemma D_9b2a4 : decode_any W_9b2a4 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2a8 : bv 32 := 0x05013403.
Lemma F_9b2a8 : fetch_word Plain.M.loaded_segments (0x9b300 : word) = Some W_9b2a8.
Proof. vm_refl. Qed.
Lemma D_9b2a8 : decode_any W_9b2a8 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2ac : bv 32 := 0x04813483.
Lemma F_9b2ac : fetch_word Plain.M.loaded_segments (0x9b304 : word) = Some W_9b2ac.
Proof. vm_refl. Qed.
Lemma D_9b2ac : decode_any W_9b2ac = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2b0 : bv 32 := 0x04013903.
Lemma F_9b2b0 : fetch_word Plain.M.loaded_segments (0x9b308 : word) = Some W_9b2b0.
Proof. vm_refl. Qed.
Lemma D_9b2b0 : decode_any W_9b2b0 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2b4 : bv 32 := 0x03813983.
Lemma F_9b2b4 : fetch_word Plain.M.loaded_segments (0x9b30c : word) = Some W_9b2b4.
Proof. vm_refl. Qed.
Lemma D_9b2b4 : decode_any W_9b2b4 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2b8 : bv 32 := 0x03013a03.
Lemma F_9b2b8 : fetch_word Plain.M.loaded_segments (0x9b310 : word) = Some W_9b2b8.
Proof. vm_refl. Qed.
Lemma D_9b2b8 : decode_any W_9b2b8 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2bc : bv 32 := 0x02813407.
Lemma F_9b2bc : fetch_word Plain.M.loaded_segments (0x9b314 : word) = Some W_9b2bc.
Proof. vm_refl. Qed.
Lemma D_9b2bc : decode_any W_9b2bc = Some (FLoad FMT_D 8 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2c0 : bv 32 := 0x02013487.
Lemma F_9b2c0 : fetch_word Plain.M.loaded_segments (0x9b318 : word) = Some W_9b2c0.
Proof. vm_refl. Qed.
Lemma D_9b2c0 : decode_any W_9b2c0 = Some (FLoad FMT_D 9 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2c4 : bv 32 := 0x06010113.
Lemma F_9b2c4 : fetch_word Plain.M.loaded_segments (0x9b31c : word) = Some W_9b2c4.
Proof. vm_refl. Qed.
Lemma D_9b2c4 : decode_any W_9b2c4 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2c8 : bv 32 := 0xdfdc706f.
Lemma F_9b2c8 : fetch_word Plain.M.loaded_segments (0x9b320 : word) = Some W_9b2c8.
Proof. vm_refl. Qed.
Lemma D_9b2c8 : decode_any W_9b2c8 = Some (Jal 0 1867260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2d4 : bv 32 := 0x00300593.
Lemma F_9b2d4 : fetch_word Plain.M.loaded_segments (0x9b32c : word) = Some W_9b2d4.
Proof. vm_refl. Qed.
Lemma D_9b2d4 : decode_any W_9b2d4 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2d8 : bv 32 := 0x00a5cc63.
Lemma F_9b2d8 : fetch_word Plain.M.loaded_segments (0x9b330 : word) = Some W_9b2d8.
Proof. vm_refl. Qed.
Lemma D_9b2d8 : decode_any W_9b2d8 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2dc : bv 32 := 0xfff77517.
Lemma F_9b2dc : fetch_word Plain.M.loaded_segments (0x9b334 : word) = Some W_9b2dc.
Proof. vm_refl. Qed.
Lemma D_9b2dc : decode_any W_9b2dc = Some (Auipc 10 1048439, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2e0 : bv 32 := 0xfff75597.
Lemma F_9b2e0 : fetch_word Plain.M.loaded_segments (0x9b338 : word) = Some W_9b2e0.
Proof. vm_refl. Qed.
Lemma D_9b2e0 : decode_any W_9b2e0 = Some (Auipc 11 1048437, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2e4 : bv 32 := 0xe8150513.
Lemma F_9b2e4 : fetch_word Plain.M.loaded_segments (0x9b33c : word) = Some W_9b2e4.
Proof. vm_refl. Qed.
Lemma D_9b2e4 : decode_any W_9b2e4 = Some (OpImm ALU_ADD 10 10 3713, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2e8 : bv 32 := 0x22458593.
Lemma F_9b2e8 : fetch_word Plain.M.loaded_segments (0x9b340 : word) = Some W_9b2e8.
Proof. vm_refl. Qed.
Lemma D_9b2e8 : decode_any W_9b2e8 = Some (OpImm ALU_ADD 11 11 548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2ec : bv 32 := 0xd3dc70ef.
Lemma F_9b2ec : fetch_word Plain.M.loaded_segments (0x9b344 : word) = Some W_9b2ec.
Proof. vm_refl. Qed.
Lemma D_9b2ec : decode_any W_9b2ec = Some (Jal 1 1867068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2f0 : bv 32 := 0x00048663.
Lemma F_9b2f0 : fetch_word Plain.M.loaded_segments (0x9b348 : word) = Some W_9b2f0.
Proof. vm_refl. Qed.
Lemma D_9b2f0 : decode_any W_9b2f0 = Some (Branch BC_EQ 9 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2f4 : bv 32 := 0x10e00513.
Lemma F_9b2f4 : fetch_word Plain.M.loaded_segments (0x9b34c : word) = Some W_9b2f4.
Proof. vm_refl. Qed.
Lemma D_9b2f4 : decode_any W_9b2f4 = Some (OpImm ALU_ADD 10 0 270, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2f8 : bv 32 := 0x00a4a023.
Lemma F_9b2f8 : fetch_word Plain.M.loaded_segments (0x9b350 : word) = Some W_9b2f8.
Proof. vm_refl. Qed.
Lemma D_9b2f8 : decode_any W_9b2f8 = Some (Store SZ4 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b2fc : bv 32 := 0x00300593.
Lemma F_9b2fc : fetch_word Plain.M.loaded_segments (0x9b354 : word) = Some W_9b2fc.
Proof. vm_refl. Qed.
Lemma D_9b2fc : decode_any W_9b2fc = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b300 : bv 32 := 0x0600006f.
Lemma F_9b300 : fetch_word Plain.M.loaded_segments (0x9b358 : word) = Some W_9b300.
Proof. vm_refl. Qed.
Lemma D_9b300 : decode_any W_9b300 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b304 : bv 32 := 0x00300593.
Lemma F_9b304 : fetch_word Plain.M.loaded_segments (0x9b35c : word) = Some W_9b304.
Proof. vm_refl. Qed.
Lemma D_9b304 : decode_any W_9b304 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b308 : bv 32 := 0x00a5cc63.
Lemma F_9b308 : fetch_word Plain.M.loaded_segments (0x9b360 : word) = Some W_9b308.
Proof. vm_refl. Qed.
Lemma D_9b308 : decode_any W_9b308 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b30c : bv 32 := 0xfff76517.
Lemma F_9b30c : fetch_word Plain.M.loaded_segments (0x9b364 : word) = Some W_9b30c.
Proof. vm_refl. Qed.
Lemma D_9b30c : decode_any W_9b30c = Some (Auipc 10 1048438, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b310 : bv 32 := 0xfff75597.
Lemma F_9b310 : fetch_word Plain.M.loaded_segments (0x9b368 : word) = Some W_9b310.
Proof. vm_refl. Qed.
Lemma D_9b310 : decode_any W_9b310 = Some (Auipc 11 1048437, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b314 : bv 32 := 0x08150513.
Lemma F_9b314 : fetch_word Plain.M.loaded_segments (0x9b36c : word) = Some W_9b314.
Proof. vm_refl. Qed.
Lemma D_9b314 : decode_any W_9b314 = Some (OpImm ALU_ADD 10 10 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b318 : bv 32 := 0x1f458593.
Lemma F_9b318 : fetch_word Plain.M.loaded_segments (0x9b370 : word) = Some W_9b318.
Proof. vm_refl. Qed.
Lemma D_9b318 : decode_any W_9b318 = Some (OpImm ALU_ADD 11 11 500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b31c : bv 32 := 0xd0dc70ef.
Lemma F_9b31c : fetch_word Plain.M.loaded_segments (0x9b374 : word) = Some W_9b31c.
Proof. vm_refl. Qed.
Lemma D_9b31c : decode_any W_9b31c = Some (Jal 1 1867020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b320 : bv 32 := 0x00048663.
Lemma F_9b320 : fetch_word Plain.M.loaded_segments (0x9b378 : word) = Some W_9b320.
Proof. vm_refl. Qed.
Lemma D_9b320 : decode_any W_9b320 = Some (Branch BC_EQ 9 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b324 : bv 32 := 0x05a00513.
Lemma F_9b324 : fetch_word Plain.M.loaded_segments (0x9b37c : word) = Some W_9b324.
Proof. vm_refl. Qed.
Lemma D_9b324 : decode_any W_9b324 = Some (OpImm ALU_ADD 10 0 90, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b328 : bv 32 := 0x00a4a023.
Lemma F_9b328 : fetch_word Plain.M.loaded_segments (0x9b380 : word) = Some W_9b328.
Proof. vm_refl. Qed.
Lemma D_9b328 : decode_any W_9b328 = Some (Store SZ4 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b32c : bv 32 := 0x00100593.
Lemma F_9b32c : fetch_word Plain.M.loaded_segments (0x9b384 : word) = Some W_9b32c.
Proof. vm_refl. Qed.
Lemma D_9b32c : decode_any W_9b32c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b330 : bv 32 := 0x0300006f.
Lemma F_9b330 : fetch_word Plain.M.loaded_segments (0x9b388 : word) = Some W_9b330.
Proof. vm_refl. Qed.
Lemma D_9b330 : decode_any W_9b330 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b334 : bv 32 := 0x00300593.
Lemma F_9b334 : fetch_word Plain.M.loaded_segments (0x9b38c : word) = Some W_9b334.
Proof. vm_refl. Qed.
Lemma D_9b334 : decode_any W_9b334 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b338 : bv 32 := 0x00a5cc63.
Lemma F_9b338 : fetch_word Plain.M.loaded_segments (0x9b390 : word) = Some W_9b338.
Proof. vm_refl. Qed.
Lemma D_9b338 : decode_any W_9b338 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b33c : bv 32 := 0xfff83517.
Lemma F_9b33c : fetch_word Plain.M.loaded_segments (0x9b394 : word) = Some W_9b33c.
Proof. vm_refl. Qed.
Lemma D_9b33c : decode_any W_9b33c = Some (Auipc 10 1048451, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b340 : bv 32 := 0xfff75597.
Lemma F_9b340 : fetch_word Plain.M.loaded_segments (0x9b398 : word) = Some W_9b340.
Proof. vm_refl. Qed.
Lemma D_9b340 : decode_any W_9b340 = Some (Auipc 11 1048437, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b344 : bv 32 := 0x2db50513.
Lemma F_9b344 : fetch_word Plain.M.loaded_segments (0x9b39c : word) = Some W_9b344.
Proof. vm_refl. Qed.
Lemma D_9b344 : decode_any W_9b344 = Some (OpImm ALU_ADD 10 10 731, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b348 : bv 32 := 0x1c458593.
Lemma F_9b348 : fetch_word Plain.M.loaded_segments (0x9b3a0 : word) = Some W_9b348.
Proof. vm_refl. Qed.
Lemma D_9b348 : decode_any W_9b348 = Some (OpImm ALU_ADD 11 11 452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b34c : bv 32 := 0xcddc70ef.
Lemma F_9b34c : fetch_word Plain.M.loaded_segments (0x9b3a4 : word) = Some W_9b34c.
Proof. vm_refl. Qed.
Lemma D_9b34c : decode_any W_9b34c = Some (Jal 1 1866972, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b350 : bv 32 := 0x00048663.
Lemma F_9b350 : fetch_word Plain.M.loaded_segments (0x9b3a8 : word) = Some W_9b350.
Proof. vm_refl. Qed.
Lemma D_9b350 : decode_any W_9b350 = Some (Branch BC_EQ 9 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b354 : bv 32 := 0x0b400513.
Lemma F_9b354 : fetch_word Plain.M.loaded_segments (0x9b3ac : word) = Some W_9b354.
Proof. vm_refl. Qed.
Lemma D_9b354 : decode_any W_9b354 = Some (OpImm ALU_ADD 10 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b358 : bv 32 := 0x00a4a023.
Lemma F_9b358 : fetch_word Plain.M.loaded_segments (0x9b3b0 : word) = Some W_9b358.
Proof. vm_refl. Qed.
Lemma D_9b358 : decode_any W_9b358 = Some (Store SZ4 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b35c : bv 32 := 0x00200593.
Lemma F_9b35c : fetch_word Plain.M.loaded_segments (0x9b3b4 : word) = Some W_9b35c.
Proof. vm_refl. Qed.
Lemma D_9b35c : decode_any W_9b35c = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b360 : bv 32 := 0x00040513.
Lemma F_9b360 : fetch_word Plain.M.loaded_segments (0x9b3b8 : word) = Some W_9b360.
Proof. vm_refl. Qed.
Lemma D_9b360 : decode_any W_9b360 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b364 : bv 32 := 0xbdcec0ef.
Lemma F_9b364 : fetch_word Plain.M.loaded_segments (0x9b3bc : word) = Some W_9b364.
Proof. vm_refl. Qed.
Lemma D_9b364 : decode_any W_9b364 = Some (Jal 1 2016220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b368 : bv 32 := 0x0540006f.
Lemma F_9b368 : fetch_word Plain.M.loaded_segments (0x9b3c0 : word) = Some W_9b368.
Proof. vm_refl. Qed.
Lemma D_9b368 : decode_any W_9b368 = Some (Jal 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b36c : bv 32 := 0x00300593.
Lemma F_9b36c : fetch_word Plain.M.loaded_segments (0x9b3c4 : word) = Some W_9b36c.
Proof. vm_refl. Qed.
Lemma D_9b36c : decode_any W_9b36c = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b370 : bv 32 := 0x00a5cc63.
Lemma F_9b370 : fetch_word Plain.M.loaded_segments (0x9b3c8 : word) = Some W_9b370.
Proof. vm_refl. Qed.
Lemma D_9b370 : decode_any W_9b370 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b374 : bv 32 := 0xfff77517.
Lemma F_9b374 : fetch_word Plain.M.loaded_segments (0x9b3cc : word) = Some W_9b374.
Proof. vm_refl. Qed.
Lemma D_9b374 : decode_any W_9b374 = Some (Auipc 10 1048439, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b378 : bv 32 := 0xfff75597.
Lemma F_9b378 : fetch_word Plain.M.loaded_segments (0x9b3d0 : word) = Some W_9b378.
Proof. vm_refl. Qed.
Lemma D_9b378 : decode_any W_9b378 = Some (Auipc 11 1048437, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b37c : bv 32 := 0x51c50513.
Lemma F_9b37c : fetch_word Plain.M.loaded_segments (0x9b3d4 : word) = Some W_9b37c.
Proof. vm_refl. Qed.
Lemma D_9b37c : decode_any W_9b37c = Some (OpImm ALU_ADD 10 10 1308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b380 : bv 32 := 0x18c58593.
Lemma F_9b380 : fetch_word Plain.M.loaded_segments (0x9b3d8 : word) = Some W_9b380.
Proof. vm_refl. Qed.
Lemma D_9b380 : decode_any W_9b380 = Some (OpImm ALU_ADD 11 11 396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b384 : bv 32 := 0xca5c70ef.
Lemma F_9b384 : fetch_word Plain.M.loaded_segments (0x9b3dc : word) = Some W_9b384.
Proof. vm_refl. Qed.
Lemma D_9b384 : decode_any W_9b384 = Some (Jal 1 1866916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b388 : bv 32 := 0x02048463.
Lemma F_9b388 : fetch_word Plain.M.loaded_segments (0x9b3e0 : word) = Some W_9b388.
Proof. vm_refl. Qed.
Lemma D_9b388 : decode_any W_9b388 = Some (Branch BC_EQ 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b38c : bv 32 := 0x0004a023.
Lemma F_9b38c : fetch_word Plain.M.loaded_segments (0x9b3e4 : word) = Some W_9b38c.
Proof. vm_refl. Qed.
Lemma D_9b38c : decode_any W_9b38c = Some (Store SZ4 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b390 : bv 32 := 0x0200006f.
Lemma F_9b390 : fetch_word Plain.M.loaded_segments (0x9b3e8 : word) = Some W_9b390.
Proof. vm_refl. Qed.
Lemma D_9b390 : decode_any W_9b390 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3b0 : bv 32 := 0x00000513.
Lemma F_9b3b0 : fetch_word Plain.M.loaded_segments (0x9b408 : word) = Some W_9b3b0.
Proof. vm_refl. Qed.
Lemma D_9b3b0 : decode_any W_9b3b0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3b4 : bv 32 := 0x00040593.
Lemma F_9b3b4 : fetch_word Plain.M.loaded_segments (0x9b40c : word) = Some W_9b3b4.
Proof. vm_refl. Qed.
Lemma D_9b3b4 : decode_any W_9b3b4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3b8 : bv 32 := 0x870d20ef.
Lemma F_9b3b8 : fetch_word Plain.M.loaded_segments (0x9b410 : word) = Some W_9b3b8.
Proof. vm_refl. Qed.
Lemma D_9b3b8 : decode_any W_9b3b8 = Some (Jal 1 1908848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3bc : bv 32 := 0x05813083.
Lemma F_9b3bc : fetch_word Plain.M.loaded_segments (0x9b414 : word) = Some W_9b3bc.
Proof. vm_refl. Qed.
Lemma D_9b3bc : decode_any W_9b3bc = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3c0 : bv 32 := 0x05013403.
Lemma F_9b3c0 : fetch_word Plain.M.loaded_segments (0x9b418 : word) = Some W_9b3c0.
Proof. vm_refl. Qed.
Lemma D_9b3c0 : decode_any W_9b3c0 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3c4 : bv 32 := 0x04813483.
Lemma F_9b3c4 : fetch_word Plain.M.loaded_segments (0x9b41c : word) = Some W_9b3c4.
Proof. vm_refl. Qed.
Lemma D_9b3c4 : decode_any W_9b3c4 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3c8 : bv 32 := 0x04013903.
Lemma F_9b3c8 : fetch_word Plain.M.loaded_segments (0x9b420 : word) = Some W_9b3c8.
Proof. vm_refl. Qed.
Lemma D_9b3c8 : decode_any W_9b3c8 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3cc : bv 32 := 0x03813983.
Lemma F_9b3cc : fetch_word Plain.M.loaded_segments (0x9b424 : word) = Some W_9b3cc.
Proof. vm_refl. Qed.
Lemma D_9b3cc : decode_any W_9b3cc = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3d0 : bv 32 := 0x03013a03.
Lemma F_9b3d0 : fetch_word Plain.M.loaded_segments (0x9b428 : word) = Some W_9b3d0.
Proof. vm_refl. Qed.
Lemma D_9b3d0 : decode_any W_9b3d0 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3d4 : bv 32 := 0x02813407.
Lemma F_9b3d4 : fetch_word Plain.M.loaded_segments (0x9b42c : word) = Some W_9b3d4.
Proof. vm_refl. Qed.
Lemma D_9b3d4 : decode_any W_9b3d4 = Some (FLoad FMT_D 8 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3d8 : bv 32 := 0x02013487.
Lemma F_9b3d8 : fetch_word Plain.M.loaded_segments (0x9b430 : word) = Some W_9b3d8.
Proof. vm_refl. Qed.
Lemma D_9b3d8 : decode_any W_9b3d8 = Some (FLoad FMT_D 9 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3dc : bv 32 := 0x06010113.
Lemma F_9b3dc : fetch_word Plain.M.loaded_segments (0x9b434 : word) = Some W_9b3dc.
Proof. vm_refl. Qed.
Lemma D_9b3dc : decode_any W_9b3dc = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b3e0 : bv 32 := 0x00008067.
Lemma F_9b3e0 : fetch_word Plain.M.loaded_segments (0x9b438 : word) = Some W_9b3e0.
Proof. vm_refl. Qed.
Lemma D_9b3e0 : decode_any W_9b3e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
