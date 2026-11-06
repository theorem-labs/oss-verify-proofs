(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushU9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5d0e8 : bv 32 := 0xfd010113.
Lemma F_5d0e8 : fetch_word Ubsan.M.loaded_segments (0x5d140 : word) = Some W_5d0e8.
Proof. vm_refl. Qed.
Lemma D_5d0e8 : decode_any W_5d0e8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0ec : bv 32 := 0x02113423.
Lemma F_5d0ec : fetch_word Ubsan.M.loaded_segments (0x5d144 : word) = Some W_5d0ec.
Proof. vm_refl. Qed.
Lemma D_5d0ec : decode_any W_5d0ec = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0f0 : bv 32 := 0x02813023.
Lemma F_5d0f0 : fetch_word Ubsan.M.loaded_segments (0x5d148 : word) = Some W_5d0f0.
Proof. vm_refl. Qed.
Lemma D_5d0f0 : decode_any W_5d0f0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0f4 : bv 32 := 0x00913c23.
Lemma F_5d0f4 : fetch_word Ubsan.M.loaded_segments (0x5d14c : word) = Some W_5d0f4.
Proof. vm_refl. Qed.
Lemma D_5d0f4 : decode_any W_5d0f4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0f8 : bv 32 := 0x00058413.
Lemma F_5d0f8 : fetch_word Ubsan.M.loaded_segments (0x5d150 : word) = Some W_5d0f8.
Proof. vm_refl. Qed.
Lemma D_5d0f8 : decode_any W_5d0f8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0fc : bv 32 := 0x00300593.
Lemma F_5d0fc : fetch_word Ubsan.M.loaded_segments (0x5d154 : word) = Some W_5d0fc.
Proof. vm_refl. Qed.
Lemma D_5d0fc : decode_any W_5d0fc = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d100 : bv 32 := 0x04b46863.
Lemma F_5d100 : fetch_word Ubsan.M.loaded_segments (0x5d158 : word) = Some W_5d100.
Proof. vm_refl. Qed.
Lemma D_5d100 : decode_any W_5d100 = Some (Branch BC_LTU 8 11 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d104 : bv 32 := 0x00050493.
Lemma F_5d104 : fetch_word Ubsan.M.loaded_segments (0x5d15c : word) = Some W_5d104.
Proof. vm_refl. Qed.
Lemma D_5d104 : decode_any W_5d104 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d108 : bv 32 := 0x00000517.
Lemma F_5d108 : fetch_word Ubsan.M.loaded_segments (0x5d160 : word) = Some W_5d108.
Proof. vm_refl. Qed.
Lemma D_5d108 : decode_any W_5d108 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d10c : bv 32 := 0x06050513.
Lemma F_5d10c : fetch_word Ubsan.M.loaded_segments (0x5d164 : word) = Some W_5d10c.
Proof. vm_refl. Qed.
Lemma D_5d10c : decode_any W_5d10c = Some (OpImm ALU_ADD 10 10 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d110 : bv 32 := 0x1f8000ef.
Lemma F_5d110 : fetch_word Ubsan.M.loaded_segments (0x5d168 : word) = Some W_5d110.
Proof. vm_refl. Qed.
Lemma D_5d110 : decode_any W_5d110 = Some (Jal 1 504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d114 : bv 32 := 0x00048513.
Lemma F_5d114 : fetch_word Ubsan.M.loaded_segments (0x5d16c : word) = Some W_5d114.
Proof. vm_refl. Qed.
Lemma D_5d114 : decode_any W_5d114 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d118 : bv 32 := 0x00040593.
Lemma F_5d118 : fetch_word Ubsan.M.loaded_segments (0x5d170 : word) = Some W_5d118.
Proof. vm_refl. Qed.
Lemma D_5d118 : decode_any W_5d118 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d11c : bv 32 := 0x3501f0ef.
Lemma F_5d11c : fetch_word Ubsan.M.loaded_segments (0x5d174 : word) = Some W_5d11c.
Proof. vm_refl. Qed.
Lemma D_5d11c : decode_any W_5d11c = Some (Jal 1 127824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d120 : bv 32 := 0x00a13823.
Lemma F_5d120 : fetch_word Ubsan.M.loaded_segments (0x5d178 : word) = Some W_5d120.
Proof. vm_refl. Qed.
Lemma D_5d120 : decode_any W_5d120 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d124 : bv 32 := 0x02050663.
Lemma F_5d124 : fetch_word Ubsan.M.loaded_segments (0x5d17c : word) = Some W_5d124.
Proof. vm_refl. Qed.
Lemma D_5d124 : decode_any W_5d124 = Some (Branch BC_EQ 10 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d128 : bv 32 := 0x00100593.
Lemma F_5d128 : fetch_word Ubsan.M.loaded_segments (0x5d180 : word) = Some W_5d128.
Proof. vm_refl. Qed.
Lemma D_5d128 : decode_any W_5d128 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d12c : bv 32 := 0x00100613.
Lemma F_5d12c : fetch_word Ubsan.M.loaded_segments (0x5d184 : word) = Some W_5d12c.
Proof. vm_refl. Qed.
Lemma D_5d12c : decode_any W_5d12c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d130 : bv 32 := 0x00100693.
Lemma F_5d130 : fetch_word Ubsan.M.loaded_segments (0x5d188 : word) = Some W_5d130.
Proof. vm_refl. Qed.
Lemma D_5d130 : decode_any W_5d130 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d134 : bv 32 := 0x00c10713.
Lemma F_5d134 : fetch_word Ubsan.M.loaded_segments (0x5d18c : word) = Some W_5d134.
Proof. vm_refl. Qed.
Lemma D_5d134 : decode_any W_5d134 = Some (OpImm ALU_ADD 14 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d138 : bv 32 := 0x00810793.
Lemma F_5d138 : fetch_word Ubsan.M.loaded_segments (0x5d190 : word) = Some W_5d138.
Proof. vm_refl. Qed.
Lemma D_5d138 : decode_any W_5d138 = Some (OpImm ALU_ADD 15 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d13c : bv 32 := 0x00410813.
Lemma F_5d13c : fetch_word Ubsan.M.loaded_segments (0x5d194 : word) = Some W_5d13c.
Proof. vm_refl. Qed.
Lemma D_5d13c : decode_any W_5d13c = Some (OpImm ALU_ADD 16 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d140 : bv 32 := 0x00000893.
Lemma F_5d140 : fetch_word Ubsan.M.loaded_segments (0x5d198 : word) = Some W_5d140.
Proof. vm_refl. Qed.
Lemma D_5d140 : decode_any W_5d140 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d144 : bv 32 := 0x264250ef.
Lemma F_5d144 : fetch_word Ubsan.M.loaded_segments (0x5d19c : word) = Some W_5d144.
Proof. vm_refl. Qed.
Lemma D_5d144 : decode_any W_5d144 = Some (Jal 1 152164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d148 : bv 32 := 0x01010513.
Lemma F_5d148 : fetch_word Ubsan.M.loaded_segments (0x5d1a0 : word) = Some W_5d148.
Proof. vm_refl. Qed.
Lemma D_5d148 : decode_any W_5d148 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d14c : bv 32 := 0x524060ef.
Lemma F_5d14c : fetch_word Ubsan.M.loaded_segments (0x5d1a4 : word) = Some W_5d14c.
Proof. vm_refl. Qed.
Lemma D_5d14c : decode_any W_5d14c = Some (Jal 1 25892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d150 : bv 32 := 0x00000513.
Lemma F_5d150 : fetch_word Ubsan.M.loaded_segments (0x5d1a8 : word) = Some W_5d150.
Proof. vm_refl. Qed.
Lemma D_5d150 : decode_any W_5d150 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d154 : bv 32 := 0x02813083.
Lemma F_5d154 : fetch_word Ubsan.M.loaded_segments (0x5d1ac : word) = Some W_5d154.
Proof. vm_refl. Qed.
Lemma D_5d154 : decode_any W_5d154 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d158 : bv 32 := 0x02013403.
Lemma F_5d158 : fetch_word Ubsan.M.loaded_segments (0x5d1b0 : word) = Some W_5d158.
Proof. vm_refl. Qed.
Lemma D_5d158 : decode_any W_5d158 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d15c : bv 32 := 0x01813483.
Lemma F_5d15c : fetch_word Ubsan.M.loaded_segments (0x5d1b4 : word) = Some W_5d15c.
Proof. vm_refl. Qed.
Lemma D_5d15c : decode_any W_5d15c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d160 : bv 32 := 0x03010113.
Lemma F_5d160 : fetch_word Ubsan.M.loaded_segments (0x5d1b8 : word) = Some W_5d160.
Proof. vm_refl. Qed.
Lemma D_5d160 : decode_any W_5d160 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d164 : bv 32 := 0x00008067.
Lemma F_5d164 : fetch_word Ubsan.M.loaded_segments (0x5d1bc : word) = Some W_5d164.
Proof. vm_refl. Qed.
Lemma D_5d164 : decode_any W_5d164 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d308 : bv 32 := 0x00051663.
Lemma F_5d308 : fetch_word Ubsan.M.loaded_segments (0x5d360 : word) = Some W_5d308.
Proof. vm_refl. Qed.
Lemma D_5d308 : decode_any W_5d308 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d314 : bv 32 := 0x0009d597.
Lemma F_5d314 : fetch_word Ubsan.M.loaded_segments (0x5d36c : word) = Some W_5d314.
Proof. vm_refl. Qed.
Lemma D_5d314 : decode_any W_5d314 = Some (Auipc 11 157, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d318 : bv 32 := 0xf8a5be23.
Lemma F_5d318 : fetch_word Ubsan.M.loaded_segments (0x5d370 : word) = Some W_5d318.
Proof. vm_refl. Qed.
Lemma D_5d318 : decode_any W_5d318 = Some (Store SZ8 11 10 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d31c : bv 32 := 0x00008067.
Lemma F_5d31c : fetch_word Ubsan.M.loaded_segments (0x5d374 : word) = Some W_5d31c.
Proof. vm_refl. Qed.
Lemma D_5d31c : decode_any W_5d31c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2dc : bv 32 := 0xfd010113.
Lemma F_5e2dc : fetch_word Ubsan.M.loaded_segments (0x5e334 : word) = Some W_5e2dc.
Proof. vm_refl. Qed.
Lemma D_5e2dc : decode_any W_5e2dc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2e0 : bv 32 := 0x02113423.
Lemma F_5e2e0 : fetch_word Ubsan.M.loaded_segments (0x5e338 : word) = Some W_5e2e0.
Proof. vm_refl. Qed.
Lemma D_5e2e0 : decode_any W_5e2e0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2e4 : bv 32 := 0x02813023.
Lemma F_5e2e4 : fetch_word Ubsan.M.loaded_segments (0x5e33c : word) = Some W_5e2e4.
Proof. vm_refl. Qed.
Lemma D_5e2e4 : decode_any W_5e2e4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2e8 : bv 32 := 0x00913c23.
Lemma F_5e2e8 : fetch_word Ubsan.M.loaded_segments (0x5e340 : word) = Some W_5e2e8.
Proof. vm_refl. Qed.
Lemma D_5e2e8 : decode_any W_5e2e8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2ec : bv 32 := 0x01213823.
Lemma F_5e2ec : fetch_word Ubsan.M.loaded_segments (0x5e344 : word) = Some W_5e2ec.
Proof. vm_refl. Qed.
Lemma D_5e2ec : decode_any W_5e2ec = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2f0 : bv 32 := 0x01313423.
Lemma F_5e2f0 : fetch_word Ubsan.M.loaded_segments (0x5e348 : word) = Some W_5e2f0.
Proof. vm_refl. Qed.
Lemma D_5e2f0 : decode_any W_5e2f0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2f4 : bv 32 := 0x04050e63.
Lemma F_5e2f4 : fetch_word Ubsan.M.loaded_segments (0x5e34c : word) = Some W_5e2f4.
Proof. vm_refl. Qed.
Lemma D_5e2f4 : decode_any W_5e2f4 = Some (Branch BC_EQ 10 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2f8 : bv 32 := 0x00050413.
Lemma F_5e2f8 : fetch_word Ubsan.M.loaded_segments (0x5e350 : word) = Some W_5e2f8.
Proof. vm_refl. Qed.
Lemma D_5e2f8 : decode_any W_5e2f8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e2fc : bv 32 := 0x00757513.
Lemma F_5e2fc : fetch_word Ubsan.M.loaded_segments (0x5e354 : word) = Some W_5e2fc.
Proof. vm_refl. Qed.
Lemma D_5e2fc : decode_any W_5e2fc = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e300 : bv 32 := 0x12051063.
Lemma F_5e300 : fetch_word Ubsan.M.loaded_segments (0x5e358 : word) = Some W_5e300.
Proof. vm_refl. Qed.
Lemma D_5e300 : decode_any W_5e300 = Some (Branch BC_NE 10 0 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e304 : bv 32 := 0x00043483.
Lemma F_5e304 : fetch_word Ubsan.M.loaded_segments (0x5e35c : word) = Some W_5e304.
Proof. vm_refl. Qed.
Lemma D_5e304 : decode_any W_5e304 = Some (Load SZ8 true 9 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e308 : bv 32 := 0x08060663.
Lemma F_5e308 : fetch_word Ubsan.M.loaded_segments (0x5e360 : word) = Some W_5e308.
Proof. vm_refl. Qed.
Lemma D_5e308 : decode_any W_5e308 = Some (Branch BC_EQ 12 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e30c : bv 32 := 0x00058913.
Lemma F_5e30c : fetch_word Ubsan.M.loaded_segments (0x5e364 : word) = Some W_5e30c.
Proof. vm_refl. Qed.
Lemma D_5e30c : decode_any W_5e30c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e310 : bv 32 := 0x00100513.
Lemma F_5e310 : fetch_word Ubsan.M.loaded_segments (0x5e368 : word) = Some W_5e310.
Proof. vm_refl. Qed.
Lemma D_5e310 : decode_any W_5e310 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e314 : bv 32 := 0x00060993.
Lemma F_5e314 : fetch_word Ubsan.M.loaded_segments (0x5e36c : word) = Some W_5e314.
Proof. vm_refl. Qed.
Lemma D_5e314 : decode_any W_5e314 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e318 : bv 32 := 0x00060593.
Lemma F_5e318 : fetch_word Ubsan.M.loaded_segments (0x5e370 : word) = Some W_5e318.
Proof. vm_refl. Qed.
Lemma D_5e318 : decode_any W_5e318 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e31c : bv 32 := 0x10c840ef.
Lemma F_5e31c : fetch_word Ubsan.M.loaded_segments (0x5e374 : word) = Some W_5e31c.
Proof. vm_refl. Qed.
Lemma D_5e31c : decode_any W_5e31c = Some (Jal 1 540940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e320 : bv 32 := 0x08048663.
Lemma F_5e320 : fetch_word Ubsan.M.loaded_segments (0x5e378 : word) = Some W_5e320.
Proof. vm_refl. Qed.
Lemma D_5e320 : decode_any W_5e320 = Some (Branch BC_EQ 9 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e324 : bv 32 := 0x0a050a63.
Lemma F_5e324 : fetch_word Ubsan.M.loaded_segments (0x5e37c : word) = Some W_5e324.
Proof. vm_refl. Qed.
Lemma D_5e324 : decode_any W_5e324 = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e328 : bv 32 := 0x01396463.
Lemma F_5e328 : fetch_word Ubsan.M.loaded_segments (0x5e380 : word) = Some W_5e328.
Proof. vm_refl. Qed.
Lemma D_5e328 : decode_any W_5e328 = Some (Branch BC_LTU 18 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e330 : bv 32 := 0x00050993.
Lemma F_5e330 : fetch_word Ubsan.M.loaded_segments (0x5e388 : word) = Some W_5e330.
Proof. vm_refl. Qed.
Lemma D_5e330 : decode_any W_5e330 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e334 : bv 32 := 0x00048593.
Lemma F_5e334 : fetch_word Ubsan.M.loaded_segments (0x5e38c : word) = Some W_5e334.
Proof. vm_refl. Qed.
Lemma D_5e334 : decode_any W_5e334 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e338 : bv 32 := 0x00090613.
Lemma F_5e338 : fetch_word Ubsan.M.loaded_segments (0x5e390 : word) = Some W_5e338.
Proof. vm_refl. Qed.
Lemma D_5e338 : decode_any W_5e338 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e33c : bv 32 := 0x6f4920ef.
Lemma F_5e33c : fetch_word Ubsan.M.loaded_segments (0x5e394 : word) = Some W_5e33c.
Proof. vm_refl. Qed.
Lemma D_5e33c : decode_any W_5e33c = Some (Jal 1 599796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e340 : bv 32 := 0x00048513.
Lemma F_5e340 : fetch_word Ubsan.M.loaded_segments (0x5e398 : word) = Some W_5e340.
Proof. vm_refl. Qed.
Lemma D_5e340 : decode_any W_5e340 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e344 : bv 32 := 0x21c840ef.
Lemma F_5e344 : fetch_word Ubsan.M.loaded_segments (0x5e39c : word) = Some W_5e344.
Proof. vm_refl. Qed.
Lemma D_5e344 : decode_any W_5e344 = Some (Jal 1 541212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e348 : bv 32 := 0x00098513.
Lemma F_5e348 : fetch_word Ubsan.M.loaded_segments (0x5e3a0 : word) = Some W_5e348.
Proof. vm_refl. Qed.
Lemma D_5e348 : decode_any W_5e348 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e34c : bv 32 := 0x0580006f.
Lemma F_5e34c : fetch_word Ubsan.M.loaded_segments (0x5e3a4 : word) = Some W_5e34c.
Proof. vm_refl. Qed.
Lemma D_5e34c : decode_any W_5e34c = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3a4 : bv 32 := 0x00043023.
Lemma F_5e3a4 : fetch_word Ubsan.M.loaded_segments (0x5e3fc : word) = Some W_5e3a4.
Proof. vm_refl. Qed.
Lemma D_5e3a4 : decode_any W_5e3a4 = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e3a8 : bv 32 := 0x05c0006f.
Lemma F_5e3a8 : fetch_word Ubsan.M.loaded_segments (0x5e400 : word) = Some W_5e3a8.
Proof. vm_refl. Qed.
Lemma D_5e3a8 : decode_any W_5e3a8 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e404 : bv 32 := 0x02813083.
Lemma F_5e404 : fetch_word Ubsan.M.loaded_segments (0x5e45c : word) = Some W_5e404.
Proof. vm_refl. Qed.
Lemma D_5e404 : decode_any W_5e404 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e408 : bv 32 := 0x02013403.
Lemma F_5e408 : fetch_word Ubsan.M.loaded_segments (0x5e460 : word) = Some W_5e408.
Proof. vm_refl. Qed.
Lemma D_5e408 : decode_any W_5e408 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e40c : bv 32 := 0x01813483.
Lemma F_5e40c : fetch_word Ubsan.M.loaded_segments (0x5e464 : word) = Some W_5e40c.
Proof. vm_refl. Qed.
Lemma D_5e40c : decode_any W_5e40c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e410 : bv 32 := 0x01013903.
Lemma F_5e410 : fetch_word Ubsan.M.loaded_segments (0x5e468 : word) = Some W_5e410.
Proof. vm_refl. Qed.
Lemma D_5e410 : decode_any W_5e410 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e414 : bv 32 := 0x00813983.
Lemma F_5e414 : fetch_word Ubsan.M.loaded_segments (0x5e46c : word) = Some W_5e414.
Proof. vm_refl. Qed.
Lemma D_5e414 : decode_any W_5e414 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e418 : bv 32 := 0x03010113.
Lemma F_5e418 : fetch_word Ubsan.M.loaded_segments (0x5e470 : word) = Some W_5e418.
Proof. vm_refl. Qed.
Lemma D_5e418 : decode_any W_5e418 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5e41c : bv 32 := 0x00008067.
Lemma F_5e41c : fetch_word Ubsan.M.loaded_segments (0x5e474 : word) = Some W_5e41c.
Proof. vm_refl. Qed.
Lemma D_5e41c : decode_any W_5e41c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61368 : bv 32 := 0xf8010113.
Lemma F_61368 : fetch_word Ubsan.M.loaded_segments (0x613c0 : word) = Some W_61368.
Proof. vm_refl. Qed.
Lemma D_61368 : decode_any W_61368 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6136c : bv 32 := 0x06113c23.
Lemma F_6136c : fetch_word Ubsan.M.loaded_segments (0x613c4 : word) = Some W_6136c.
Proof. vm_refl. Qed.
Lemma D_6136c : decode_any W_6136c = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61370 : bv 32 := 0x06813823.
Lemma F_61370 : fetch_word Ubsan.M.loaded_segments (0x613c8 : word) = Some W_61370.
Proof. vm_refl. Qed.
Lemma D_61370 : decode_any W_61370 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61374 : bv 32 := 0x06913423.
Lemma F_61374 : fetch_word Ubsan.M.loaded_segments (0x613cc : word) = Some W_61374.
Proof. vm_refl. Qed.
Lemma D_61374 : decode_any W_61374 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61378 : bv 32 := 0x07213023.
Lemma F_61378 : fetch_word Ubsan.M.loaded_segments (0x613d0 : word) = Some W_61378.
Proof. vm_refl. Qed.
Lemma D_61378 : decode_any W_61378 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6137c : bv 32 := 0x05313c23.
Lemma F_6137c : fetch_word Ubsan.M.loaded_segments (0x613d4 : word) = Some W_6137c.
Proof. vm_refl. Qed.
Lemma D_6137c : decode_any W_6137c = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61380 : bv 32 := 0x05413823.
Lemma F_61380 : fetch_word Ubsan.M.loaded_segments (0x613d8 : word) = Some W_61380.
Proof. vm_refl. Qed.
Lemma D_61380 : decode_any W_61380 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61384 : bv 32 := 0x05513423.
Lemma F_61384 : fetch_word Ubsan.M.loaded_segments (0x613dc : word) = Some W_61384.
Proof. vm_refl. Qed.
Lemma D_61384 : decode_any W_61384 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61388 : bv 32 := 0x05613023.
Lemma F_61388 : fetch_word Ubsan.M.loaded_segments (0x613e0 : word) = Some W_61388.
Proof. vm_refl. Qed.
Lemma D_61388 : decode_any W_61388 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6138c : bv 32 := 0x03713c23.
Lemma F_6138c : fetch_word Ubsan.M.loaded_segments (0x613e4 : word) = Some W_6138c.
Proof. vm_refl. Qed.
Lemma D_6138c : decode_any W_6138c = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61390 : bv 32 := 0x03813823.
Lemma F_61390 : fetch_word Ubsan.M.loaded_segments (0x613e8 : word) = Some W_61390.
Proof. vm_refl. Qed.
Lemma D_61390 : decode_any W_61390 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61394 : bv 32 := 0x03913423.
Lemma F_61394 : fetch_word Ubsan.M.loaded_segments (0x613ec : word) = Some W_61394.
Proof. vm_refl. Qed.
Lemma D_61394 : decode_any W_61394 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61398 : bv 32 := 0x02813027.
Lemma F_61398 : fetch_word Ubsan.M.loaded_segments (0x613f0 : word) = Some W_61398.
Proof. vm_refl. Qed.
Lemma D_61398 : decode_any W_61398 = Some (FStore FMT_D 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6139c : bv 32 := 0x00913c27.
Lemma F_6139c : fetch_word Ubsan.M.loaded_segments (0x613f4 : word) = Some W_6139c.
Proof. vm_refl. Qed.
Lemma D_6139c : decode_any W_6139c = Some (FStore FMT_D 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613a0 : bv 32 := 0x01213827.
Lemma F_613a0 : fetch_word Ubsan.M.loaded_segments (0x613f8 : word) = Some W_613a0.
Proof. vm_refl. Qed.
Lemma D_613a0 : decode_any W_613a0 = Some (FStore FMT_D 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613a4 : bv 32 := 0x00058a13.
Lemma F_613a4 : fetch_word Ubsan.M.loaded_segments (0x613fc : word) = Some W_613a4.
Proof. vm_refl. Qed.
Lemma D_613a4 : decode_any W_613a4 = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613a8 : bv 32 := 0x20a50453.
Lemma F_613a8 : fetch_word Ubsan.M.loaded_segments (0x61400 : word) = Some W_613a8.
Proof. vm_refl. Qed.
Lemma D_613a8 : decode_any W_613a8 = Some (Fsgnj F_SGNJ FMT_S 8 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613ac : bv 32 := 0x00050413.
Lemma F_613ac : fetch_word Ubsan.M.loaded_segments (0x61404 : word) = Some W_613ac.
Proof. vm_refl. Qed.
Lemma D_613ac : decode_any W_613ac = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613b0 : bv 32 := 0x00058863.
Lemma F_613b0 : fetch_word Ubsan.M.loaded_segments (0x61408 : word) = Some W_613b0.
Proof. vm_refl. Qed.
Lemma D_613b0 : decode_any W_613b0 = Some (Branch BC_EQ 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613c0 : bv 32 := 0x02040863.
Lemma F_613c0 : fetch_word Ubsan.M.loaded_segments (0x61418 : word) = Some W_613c0.
Proof. vm_refl. Qed.
Lemma D_613c0 : decode_any W_613c0 = Some (Branch BC_EQ 8 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613c4 : bv 32 := 0xf0000953.
Lemma F_613c4 : fetch_word Ubsan.M.loaded_segments (0x6141c : word) = Some W_613c4.
Proof. vm_refl. Qed.
Lemma D_613c4 : decode_any W_613c4 = Some (Fmv FMV_F_X FMT_S 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613c8 : bv 32 := 0xa1241553.
Lemma F_613c8 : fetch_word Ubsan.M.loaded_segments (0x61420 : word) = Some W_613c8.
Proof. vm_refl. Qed.
Lemma D_613c8 : decode_any W_613c8 = Some (Fcmp F_LT FMT_S 10 8 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_613cc : bv 32 := 0x08050a63.
Lemma F_613cc : fetch_word Ubsan.M.loaded_segments (0x61424 : word) = Some W_613cc.
Proof. vm_refl. Qed.
Lemma D_613cc : decode_any W_613cc = Some (Branch BC_EQ 10 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61460 : bv 32 := 0x00040513.
Lemma F_61460 : fetch_word Ubsan.M.loaded_segments (0x614b8 : word) = Some W_61460.
Proof. vm_refl. Qed.
Lemma D_61460 : decode_any W_61460 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61464 : bv 32 := 0x4b4000ef.
Lemma F_61464 : fetch_word Ubsan.M.loaded_segments (0x614bc : word) = Some W_61464.
Proof. vm_refl. Qed.
Lemma D_61464 : decode_any W_61464 = Some (Jal 1 1204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61468 : bv 32 := 0x00050913.
Lemma F_61468 : fetch_word Ubsan.M.loaded_segments (0x614c0 : word) = Some W_61468.
Proof. vm_refl. Qed.
Lemma D_61468 : decode_any W_61468 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6146c : bv 32 := 0x00000513.
Lemma F_6146c : fetch_word Ubsan.M.loaded_segments (0x614c4 : word) = Some W_6146c.
Proof. vm_refl. Qed.
Lemma D_6146c : decode_any W_6146c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61470 : bv 32 := 0x1c0000ef.
Lemma F_61470 : fetch_word Ubsan.M.loaded_segments (0x614c8 : word) = Some W_61470.
Proof. vm_refl. Qed.
Lemma D_61470 : decode_any W_61470 = Some (Jal 1 448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61474 : bv 32 := 0x00050493.
Lemma F_61474 : fetch_word Ubsan.M.loaded_segments (0x614cc : word) = Some W_61474.
Proof. vm_refl. Qed.
Lemma D_61474 : decode_any W_61474 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61478 : bv 32 := 0x020a0063.
Lemma F_61478 : fetch_word Ubsan.M.loaded_segments (0x614d0 : word) = Some W_61478.
Proof. vm_refl. Qed.
Lemma D_61478 : decode_any W_61478 = Some (Branch BC_EQ 20 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61498 : bv 32 := 0x00000993.
Lemma F_61498 : fetch_word Ubsan.M.loaded_segments (0x614f0 : word) = Some W_61498.
Proof. vm_refl. Qed.
Lemma D_61498 : decode_any W_61498 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6149c : bv 32 := 0x00c10613.
Lemma F_6149c : fetch_word Ubsan.M.loaded_segments (0x614f4 : word) = Some W_6149c.
Proof. vm_refl. Qed.
Lemma D_6149c : decode_any W_6149c = Some (OpImm ALU_ADD 12 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614a0 : bv 32 := 0x00040513.
Lemma F_614a0 : fetch_word Ubsan.M.loaded_segments (0x614f8 : word) = Some W_614a0.
Proof. vm_refl. Qed.
Lemma D_614a0 : decode_any W_614a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614a4 : bv 32 := 0x00000593.
Lemma F_614a4 : fetch_word Ubsan.M.loaded_segments (0x614fc : word) = Some W_614a4.
Proof. vm_refl. Qed.
Lemma D_614a4 : decode_any W_614a4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614a8 : bv 32 := 0x5d0000ef.
Lemma F_614a8 : fetch_word Ubsan.M.loaded_segments (0x61500 : word) = Some W_614a8.
Proof. vm_refl. Qed.
Lemma D_614a8 : decode_any W_614a8 = Some (Jal 1 1488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614ac : bv 32 := 0x00200513.
Lemma F_614ac : fetch_word Ubsan.M.loaded_segments (0x61504 : word) = Some W_614ac.
Proof. vm_refl. Qed.
Lemma D_614ac : decode_any W_614ac = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614b0 : bv 32 := 0x12a94c63.
Lemma F_614b0 : fetch_word Ubsan.M.loaded_segments (0x61508 : word) = Some W_614b0.
Proof. vm_refl. Qed.
Lemma D_614b0 : decode_any W_614b0 = Some (Branch BC_LT 18 10 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614b4 : bv 32 := 0x00100a93.
Lemma F_614b4 : fetch_word Ubsan.M.loaded_segments (0x6150c : word) = Some W_614b4.
Proof. vm_refl. Qed.
Lemma D_614b4 : decode_any W_614b4 = Some (OpImm ALU_ADD 21 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614b8 : bv 32 := 0x00810613.
Lemma F_614b8 : fetch_word Ubsan.M.loaded_segments (0x61510 : word) = Some W_614b8.
Proof. vm_refl. Qed.
Lemma D_614b8 : decode_any W_614b8 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614bc : bv 32 := 0x00040513.
Lemma F_614bc : fetch_word Ubsan.M.loaded_segments (0x61514 : word) = Some W_614bc.
Proof. vm_refl. Qed.
Lemma D_614bc : decode_any W_614bc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614c0 : bv 32 := 0x000a8593.
Lemma F_614c0 : fetch_word Ubsan.M.loaded_segments (0x61518 : word) = Some W_614c0.
Proof. vm_refl. Qed.
Lemma D_614c0 : decode_any W_614c0 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614c4 : bv 32 := 0x5b4000ef.
Lemma F_614c4 : fetch_word Ubsan.M.loaded_segments (0x6151c : word) = Some W_614c4.
Proof. vm_refl. Qed.
Lemma D_614c4 : decode_any W_614c4 = Some (Jal 1 1460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614c8 : bv 32 := 0x00812487.
Lemma F_614c8 : fetch_word Ubsan.M.loaded_segments (0x61520 : word) = Some W_614c8.
Proof. vm_refl. Qed.
Lemma D_614c8 : decode_any W_614c8 = Some (FLoad FMT_S 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614cc : bv 32 := 0x00c12787.
Lemma F_614cc : fetch_word Ubsan.M.loaded_segments (0x61524 : word) = Some W_614cc.
Proof. vm_refl. Qed.
Lemma D_614cc : decode_any W_614cc = Some (FLoad FMT_S 15 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614d0 : bv 32 := 0x08f4f753.
Lemma F_614d0 : fetch_word Ubsan.M.loaded_segments (0x61528 : word) = Some W_614d0.
Proof. vm_refl. Qed.
Lemma D_614d0 : decode_any W_614d0 = Some (Fari F_SUB FMT_S 14 9 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614d4 : bv 32 := 0xa1271553.
Lemma F_614d4 : fetch_word Ubsan.M.loaded_segments (0x6152c : word) = Some W_614d4.
Proof. vm_refl. Qed.
Lemma D_614d4 : decode_any W_614d4 = Some (Fcmp F_LT FMT_S 10 14 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614d8 : bv 32 := 0x00050463.
Lemma F_614d8 : fetch_word Ubsan.M.loaded_segments (0x61530 : word) = Some W_614d8.
Proof. vm_refl. Qed.
Lemma D_614d8 : decode_any W_614d8 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614dc : bv 32 := 0x20e71753.
Lemma F_614dc : fetch_word Ubsan.M.loaded_segments (0x61534 : word) = Some W_614dc.
Proof. vm_refl. Qed.
Lemma D_614dc : decode_any W_614dc = Some (Fsgnj F_SGNJN FMT_S 14 14 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614e0 : bv 32 := 0xa0e40553.
Lemma F_614e0 : fetch_word Ubsan.M.loaded_segments (0x61538 : word) = Some W_614e0.
Proof. vm_refl. Qed.
Lemma D_614e0 : decode_any W_614e0 = Some (Fcmp F_LE FMT_S 10 8 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614e4 : bv 32 := 0x00051863.
Lemma F_614e4 : fetch_word Ubsan.M.loaded_segments (0x6153c : word) = Some W_614e4.
Proof. vm_refl. Qed.
Lemma D_614e4 : decode_any W_614e4 = Some (Branch BC_NE 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614e8 : bv 32 := 0x001a8a9b.
Lemma F_614e8 : fetch_word Ubsan.M.loaded_segments (0x61540 : word) = Some W_614e8.
Proof. vm_refl. Qed.
Lemma D_614e8 : decode_any W_614e8 = Some (OpImm32 21 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614ec : bv 32 := 0xfd5916e3.
Lemma F_614ec : fetch_word Ubsan.M.loaded_segments (0x61544 : word) = Some W_614ec.
Proof. vm_refl. Qed.
Lemma D_614ec : decode_any W_614ec = Some (Branch BC_NE 18 21 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614f0 : bv 32 := 0x0f80006f.
Lemma F_614f0 : fetch_word Ubsan.M.loaded_segments (0x61548 : word) = Some W_614f0.
Proof. vm_refl. Qed.
Lemma D_614f0 : decode_any W_614f0 = Some (Jal 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614f4 : bv 32 := 0x001a8a1b.
Lemma F_614f4 : fetch_word Ubsan.M.loaded_segments (0x6154c : word) = Some W_614f4.
Proof. vm_refl. Qed.
Lemma D_614f4 : decode_any W_614f4 = Some (OpImm32 20 21 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614f8 : bv 32 := 0x0f2a5863.
Lemma F_614f8 : fetch_word Ubsan.M.loaded_segments (0x61550 : word) = Some W_614f8.
Proof. vm_refl. Qed.
Lemma D_614f8 : decode_any W_614f8 = Some (Branch BC_GE 20 18 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_614fc : bv 32 := 0xa0979553.
Lemma F_614fc : fetch_word Ubsan.M.loaded_segments (0x61554 : word) = Some W_614fc.
Proof. vm_refl. Qed.
Lemma D_614fc : decode_any W_614fc = Some (Fcmp F_LT FMT_S 10 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61500 : bv 32 := 0x00100b13.
Lemma F_61500 : fetch_word Ubsan.M.loaded_segments (0x61558 : word) = Some W_61500.
Proof. vm_refl. Qed.
Lemma D_61500 : decode_any W_61500 = Some (OpImm ALU_ADD 22 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61504 : bv 32 := 0xfff5051b.
Lemma F_61504 : fetch_word Ubsan.M.loaded_segments (0x6155c : word) = Some W_61504.
Proof. vm_refl. Qed.
Lemma D_61504 : decode_any W_61504 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61508 : bv 32 := 0x00156c93.
Lemma F_61508 : fetch_word Ubsan.M.loaded_segments (0x61560 : word) = Some W_61508.
Proof. vm_refl. Qed.
Lemma D_61508 : decode_any W_61508 = Some (OpImm ALU_OR 25 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6150c : bv 32 := 0xfff00b93.
Lemma F_6150c : fetch_word Ubsan.M.loaded_segments (0x61564 : word) = Some W_6150c.
Proof. vm_refl. Qed.
Lemma D_6150c : decode_any W_6150c = Some (OpImm ALU_ADD 23 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61510 : bv 32 := 0x20948953.
Lemma F_61510 : fetch_word Ubsan.M.loaded_segments (0x61568 : word) = Some W_61510.
Proof. vm_refl. Qed.
Lemma D_61510 : decode_any W_61510 = Some (Fsgnj F_SGNJ FMT_S 18 9 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61514 : bv 32 := 0x01c0006f.
Lemma F_61514 : fetch_word Ubsan.M.loaded_segments (0x6156c : word) = Some W_61514.
Proof. vm_refl. Qed.
Lemma D_61514 : decode_any W_61514 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61518 : bv 32 := 0x000a0a93.
Lemma F_61518 : fetch_word Ubsan.M.loaded_segments (0x61570 : word) = Some W_61518.
Proof. vm_refl. Qed.
Lemma D_61518 : decode_any W_61518 = Some (OpImm ALU_ADD 21 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6151c : bv 32 := 0x00100c13.
Lemma F_6151c : fetch_word Ubsan.M.loaded_segments (0x61574 : word) = Some W_6151c.
Proof. vm_refl. Qed.
Lemma D_6151c : decode_any W_6151c = Some (OpImm ALU_ADD 24 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61520 : bv 32 := 0x20f78953.
Lemma F_61520 : fetch_word Ubsan.M.loaded_segments (0x61578 : word) = Some W_61520.
Proof. vm_refl. Qed.
Lemma D_61520 : decode_any W_61520 = Some (Fsgnj F_SGNJ FMT_S 18 15 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61524 : bv 32 := 0x001a0a1b.
Lemma F_61524 : fetch_word Ubsan.M.loaded_segments (0x6157c : word) = Some W_61524.
Proof. vm_refl. Qed.
Lemma D_61524 : decode_any W_61524 = Some (OpImm32 20 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61528 : bv 32 := 0x000c0c93.
Lemma F_61528 : fetch_word Ubsan.M.loaded_segments (0x61580 : word) = Some W_61528.
Proof. vm_refl. Qed.
Lemma D_61528 : decode_any W_61528 = Some (OpImm ALU_ADD 25 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6152c : bv 32 := 0x0b490e63.
Lemma F_6152c : fetch_word Ubsan.M.loaded_segments (0x61584 : word) = Some W_6152c.
Proof. vm_refl. Qed.
Lemma D_6152c : decode_any W_6152c = Some (Branch BC_EQ 18 20 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61530 : bv 32 := 0x00810613.
Lemma F_61530 : fetch_word Ubsan.M.loaded_segments (0x61588 : word) = Some W_61530.
Proof. vm_refl. Qed.
Lemma D_61530 : decode_any W_61530 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61534 : bv 32 := 0x00040513.
Lemma F_61534 : fetch_word Ubsan.M.loaded_segments (0x6158c : word) = Some W_61534.
Proof. vm_refl. Qed.
Lemma D_61534 : decode_any W_61534 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61538 : bv 32 := 0x000a0593.
Lemma F_61538 : fetch_word Ubsan.M.loaded_segments (0x61590 : word) = Some W_61538.
Proof. vm_refl. Qed.
Lemma D_61538 : decode_any W_61538 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6153c : bv 32 := 0x53c000ef.
Lemma F_6153c : fetch_word Ubsan.M.loaded_segments (0x61594 : word) = Some W_6153c.
Proof. vm_refl. Qed.
Lemma D_6153c : decode_any W_6153c = Some (Jal 1 1340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61540 : bv 32 := 0x00812787.
Lemma F_61540 : fetch_word Ubsan.M.loaded_segments (0x61598 : word) = Some W_61540.
Proof. vm_refl. Qed.
Lemma D_61540 : decode_any W_61540 = Some (FLoad FMT_S 15 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61544 : bv 32 := 0x016c9663.
Lemma F_61544 : fetch_word Ubsan.M.loaded_segments (0x6159c : word) = Some W_61544.
Proof. vm_refl. Qed.
Lemma D_61544 : decode_any W_61544 = Some (Branch BC_NE 25 22 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61548 : bv 32 := 0xa0f91553.
Lemma F_61548 : fetch_word Ubsan.M.loaded_segments (0x615a0 : word) = Some W_61548.
Proof. vm_refl. Qed.
Lemma D_61548 : decode_any W_61548 = Some (Fcmp F_LT FMT_S 10 18 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6154c : bv 32 := 0xfc0516e3.
Lemma F_6154c : fetch_word Ubsan.M.loaded_segments (0x615a4 : word) = Some W_6154c.
Proof. vm_refl. Qed.
Lemma D_6154c : decode_any W_6154c = Some (Branch BC_NE 10 0 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61550 : bv 32 := 0xfff00c13.
Lemma F_61550 : fetch_word Ubsan.M.loaded_segments (0x615a8 : word) = Some W_61550.
Proof. vm_refl. Qed.
Lemma D_61550 : decode_any W_61550 = Some (OpImm ALU_ADD 24 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61554 : bv 32 := 0x018c9c63.
Lemma F_61554 : fetch_word Ubsan.M.loaded_segments (0x615ac : word) = Some W_61554.
Proof. vm_refl. Qed.
Lemma D_61554 : decode_any W_61554 = Some (Branch BC_NE 25 24 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61558 : bv 32 := 0xa0979553.
Lemma F_61558 : fetch_word Ubsan.M.loaded_segments (0x615b0 : word) = Some W_61558.
Proof. vm_refl. Qed.
Lemma D_61558 : decode_any W_61558 = Some (Fcmp F_LT FMT_S 10 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6155c : bv 32 := 0x00050863.
Lemma F_6155c : fetch_word Ubsan.M.loaded_segments (0x615b4 : word) = Some W_6155c.
Proof. vm_refl. Qed.
Lemma D_6155c : decode_any W_6155c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61560 : bv 32 := 0x000a0a93.
Lemma F_61560 : fetch_word Ubsan.M.loaded_segments (0x615b8 : word) = Some W_61560.
Proof. vm_refl. Qed.
Lemma D_61560 : decode_any W_61560 = Some (OpImm ALU_ADD 21 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61564 : bv 32 := 0x20f784d3.
Lemma F_61564 : fetch_word Ubsan.M.loaded_segments (0x615bc : word) = Some W_61564.
Proof. vm_refl. Qed.
Lemma D_61564 : decode_any W_61564 = Some (Fsgnj F_SGNJ FMT_S 9 15 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61568 : bv 32 := 0xfbdff06f.
Lemma F_61568 : fetch_word Ubsan.M.loaded_segments (0x615c0 : word) = Some W_61568.
Proof. vm_refl. Qed.
Lemma D_61568 : decode_any W_61568 = Some (Jal 0 2097084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6156c : bv 32 := 0x036c9c63.
Lemma F_6156c : fetch_word Ubsan.M.loaded_segments (0x615c4 : word) = Some W_6156c.
Proof. vm_refl. Qed.
Lemma D_6156c : decode_any W_6156c = Some (Branch BC_NE 25 22 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61570 : bv 32 := 0x08f977d3.
Lemma F_61570 : fetch_word Ubsan.M.loaded_segments (0x615c8 : word) = Some W_61570.
Proof. vm_refl. Qed.
Lemma D_61570 : decode_any W_61570 = Some (Fari F_SUB FMT_S 15 18 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61574 : bv 32 := 0xa0f40553.
Lemma F_61574 : fetch_word Ubsan.M.loaded_segments (0x615cc : word) = Some W_61574.
Proof. vm_refl. Qed.
Lemma D_61574 : decode_any W_61574 = Some (Fcmp F_LE FMT_S 10 8 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61578 : bv 32 := 0x06050463.
Lemma F_61578 : fetch_word Ubsan.M.loaded_segments (0x615d0 : word) = Some W_61578.
Proof. vm_refl. Qed.
Lemma D_61578 : decode_any W_61578 = Some (Branch BC_EQ 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6157c : bv 32 := 0xd00af553.
Lemma F_6157c : fetch_word Ubsan.M.loaded_segments (0x615d4 : word) = Some W_6157c.
Proof. vm_refl. Qed.
Lemma D_6157c : decode_any W_6157c = Some (Fcvt FC_S FC_W 10 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61580 : bv 32 := 0x00048513.
Lemma F_61580 : fetch_word Ubsan.M.loaded_segments (0x615d8 : word) = Some W_61580.
Proof. vm_refl. Qed.
Lemma D_61580 : decode_any W_61580 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61584 : bv 32 := 0x26c000ef.
Lemma F_61584 : fetch_word Ubsan.M.loaded_segments (0x615dc : word) = Some W_61584.
Proof. vm_refl. Qed.
Lemma D_61584 : decode_any W_61584 = Some (Jal 1 620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61588 : bv 32 := 0x00098863.
Lemma F_61588 : fetch_word Ubsan.M.loaded_segments (0x615e0 : word) = Some W_61588.
Proof. vm_refl. Qed.
Lemma D_61588 : decode_any W_61588 = Some (Branch BC_EQ 19 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61598 : bv 32 := 0x00812487.
Lemma F_61598 : fetch_word Ubsan.M.loaded_segments (0x615f0 : word) = Some W_61598.
Proof. vm_refl. Qed.
Lemma D_61598 : decode_any W_61598 = Some (FLoad FMT_S 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6159c : bv 32 := 0x000a0a93.
Lemma F_6159c : fetch_word Ubsan.M.loaded_segments (0x615f4 : word) = Some W_6159c.
Proof. vm_refl. Qed.
Lemma D_6159c : decode_any W_6159c = Some (OpImm ALU_ADD 21 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615a0 : bv 32 := 0xf85ff06f.
Lemma F_615a0 : fetch_word Ubsan.M.loaded_segments (0x615f8 : word) = Some W_615a0.
Proof. vm_refl. Qed.
Lemma D_615a0 : decode_any W_615a0 = Some (Jal 0 2097028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615a4 : bv 32 := 0x017c8663.
Lemma F_615a4 : fetch_word Ubsan.M.loaded_segments (0x615fc : word) = Some W_615a4.
Proof. vm_refl. Qed.
Lemma D_615a4 : decode_any W_615a4 = Some (Branch BC_EQ 25 23 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615b0 : bv 32 := 0x0897f7d3.
Lemma F_615b0 : fetch_word Ubsan.M.loaded_segments (0x61608 : word) = Some W_615b0.
Proof. vm_refl. Qed.
Lemma D_615b0 : decode_any W_615b0 = Some (Fari F_SUB FMT_S 15 15 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615b4 : bv 32 := 0xa0f40553.
Lemma F_615b4 : fetch_word Ubsan.M.loaded_segments (0x6160c : word) = Some W_615b4.
Proof. vm_refl. Qed.
Lemma D_615b4 : decode_any W_615b4 = Some (Fcmp F_LE FMT_S 10 8 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615b8 : bv 32 := 0xf60506e3.
Lemma F_615b8 : fetch_word Ubsan.M.loaded_segments (0x61610 : word) = Some W_615b8.
Proof. vm_refl. Qed.
Lemma D_615b8 : decode_any W_615b8 = Some (Branch BC_EQ 10 0 8044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615bc : bv 32 := 0xd00af553.
Lemma F_615bc : fetch_word Ubsan.M.loaded_segments (0x61614 : word) = Some W_615bc.
Proof. vm_refl. Qed.
Lemma D_615bc : decode_any W_615bc = Some (Fcvt FC_S FC_W 10 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615c0 : bv 32 := 0x00048513.
Lemma F_615c0 : fetch_word Ubsan.M.loaded_segments (0x61618 : word) = Some W_615c0.
Proof. vm_refl. Qed.
Lemma D_615c0 : decode_any W_615c0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615c4 : bv 32 := 0x22c000ef.
Lemma F_615c4 : fetch_word Ubsan.M.loaded_segments (0x6161c : word) = Some W_615c4.
Proof. vm_refl. Qed.
Lemma D_615c4 : decode_any W_615c4 = Some (Jal 1 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615c8 : bv 32 := 0x00098863.
Lemma F_615c8 : fetch_word Ubsan.M.loaded_segments (0x61620 : word) = Some W_615c8.
Proof. vm_refl. Qed.
Lemma D_615c8 : decode_any W_615c8 = Some (Branch BC_EQ 19 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615d8 : bv 32 := 0x00812907.
Lemma F_615d8 : fetch_word Ubsan.M.loaded_segments (0x61630 : word) = Some W_615d8.
Proof. vm_refl. Qed.
Lemma D_615d8 : decode_any W_615d8 = Some (FLoad FMT_S 18 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615dc : bv 32 := 0x000a0a93.
Lemma F_615dc : fetch_word Ubsan.M.loaded_segments (0x61634 : word) = Some W_615dc.
Proof. vm_refl. Qed.
Lemma D_615dc : decode_any W_615dc = Some (OpImm ALU_ADD 21 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615e0 : bv 32 := 0x00100c13.
Lemma F_615e0 : fetch_word Ubsan.M.loaded_segments (0x61638 : word) = Some W_615e0.
Proof. vm_refl. Qed.
Lemma D_615e0 : decode_any W_615e0 = Some (OpImm ALU_ADD 24 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615e4 : bv 32 := 0xf41ff06f.
Lemma F_615e4 : fetch_word Ubsan.M.loaded_segments (0x6163c : word) = Some W_615e4.
Proof. vm_refl. Qed.
Lemma D_615e4 : decode_any W_615e4 = Some (Jal 0 2096960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615e8 : bv 32 := 0x00048513.
Lemma F_615e8 : fetch_word Ubsan.M.loaded_segments (0x61640 : word) = Some W_615e8.
Proof. vm_refl. Qed.
Lemma D_615e8 : decode_any W_615e8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615ec : bv 32 := 0x07813083.
Lemma F_615ec : fetch_word Ubsan.M.loaded_segments (0x61644 : word) = Some W_615ec.
Proof. vm_refl. Qed.
Lemma D_615ec : decode_any W_615ec = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615f0 : bv 32 := 0x07013403.
Lemma F_615f0 : fetch_word Ubsan.M.loaded_segments (0x61648 : word) = Some W_615f0.
Proof. vm_refl. Qed.
Lemma D_615f0 : decode_any W_615f0 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615f4 : bv 32 := 0x06813483.
Lemma F_615f4 : fetch_word Ubsan.M.loaded_segments (0x6164c : word) = Some W_615f4.
Proof. vm_refl. Qed.
Lemma D_615f4 : decode_any W_615f4 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615f8 : bv 32 := 0x06013903.
Lemma F_615f8 : fetch_word Ubsan.M.loaded_segments (0x61650 : word) = Some W_615f8.
Proof. vm_refl. Qed.
Lemma D_615f8 : decode_any W_615f8 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_615fc : bv 32 := 0x05813983.
Lemma F_615fc : fetch_word Ubsan.M.loaded_segments (0x61654 : word) = Some W_615fc.
Proof. vm_refl. Qed.
Lemma D_615fc : decode_any W_615fc = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61600 : bv 32 := 0x05013a03.
Lemma F_61600 : fetch_word Ubsan.M.loaded_segments (0x61658 : word) = Some W_61600.
Proof. vm_refl. Qed.
Lemma D_61600 : decode_any W_61600 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61604 : bv 32 := 0x04813a83.
Lemma F_61604 : fetch_word Ubsan.M.loaded_segments (0x6165c : word) = Some W_61604.
Proof. vm_refl. Qed.
Lemma D_61604 : decode_any W_61604 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61608 : bv 32 := 0x04013b03.
Lemma F_61608 : fetch_word Ubsan.M.loaded_segments (0x61660 : word) = Some W_61608.
Proof. vm_refl. Qed.
Lemma D_61608 : decode_any W_61608 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6160c : bv 32 := 0x03813b83.
Lemma F_6160c : fetch_word Ubsan.M.loaded_segments (0x61664 : word) = Some W_6160c.
Proof. vm_refl. Qed.
Lemma D_6160c : decode_any W_6160c = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61610 : bv 32 := 0x03013c03.
Lemma F_61610 : fetch_word Ubsan.M.loaded_segments (0x61668 : word) = Some W_61610.
Proof. vm_refl. Qed.
Lemma D_61610 : decode_any W_61610 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61614 : bv 32 := 0x02813c83.
Lemma F_61614 : fetch_word Ubsan.M.loaded_segments (0x6166c : word) = Some W_61614.
Proof. vm_refl. Qed.
Lemma D_61614 : decode_any W_61614 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61618 : bv 32 := 0x02013407.
Lemma F_61618 : fetch_word Ubsan.M.loaded_segments (0x61670 : word) = Some W_61618.
Proof. vm_refl. Qed.
Lemma D_61618 : decode_any W_61618 = Some (FLoad FMT_D 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6161c : bv 32 := 0x01813487.
Lemma F_6161c : fetch_word Ubsan.M.loaded_segments (0x61674 : word) = Some W_6161c.
Proof. vm_refl. Qed.
Lemma D_6161c : decode_any W_6161c = Some (FLoad FMT_D 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61620 : bv 32 := 0x01013907.
Lemma F_61620 : fetch_word Ubsan.M.loaded_segments (0x61678 : word) = Some W_61620.
Proof. vm_refl. Qed.
Lemma D_61620 : decode_any W_61620 = Some (FLoad FMT_D 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61624 : bv 32 := 0x08010113.
Lemma F_61624 : fetch_word Ubsan.M.loaded_segments (0x6167c : word) = Some W_61624.
Proof. vm_refl. Qed.
Lemma D_61624 : decode_any W_61624 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61628 : bv 32 := 0x00008067.
Lemma F_61628 : fetch_word Ubsan.M.loaded_segments (0x61680 : word) = Some W_61628.
Proof. vm_refl. Qed.
Lemma D_61628 : decode_any W_61628 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61630 : bv 32 := 0xfe010113.
Lemma F_61630 : fetch_word Ubsan.M.loaded_segments (0x61688 : word) = Some W_61630.
Proof. vm_refl. Qed.
Lemma D_61630 : decode_any W_61630 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61634 : bv 32 := 0x00113c23.
Lemma F_61634 : fetch_word Ubsan.M.loaded_segments (0x6168c : word) = Some W_61634.
Proof. vm_refl. Qed.
Lemma D_61634 : decode_any W_61634 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61638 : bv 32 := 0x00813823.
Lemma F_61638 : fetch_word Ubsan.M.loaded_segments (0x61690 : word) = Some W_61638.
Proof. vm_refl. Qed.
Lemma D_61638 : decode_any W_61638 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6163c : bv 32 := 0x00913423.
Lemma F_6163c : fetch_word Ubsan.M.loaded_segments (0x61694 : word) = Some W_6163c.
Proof. vm_refl. Qed.
Lemma D_6163c : decode_any W_6163c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61640 : bv 32 := 0x00050413.
Lemma F_61640 : fetch_word Ubsan.M.loaded_segments (0x61698 : word) = Some W_61640.
Proof. vm_refl. Qed.
Lemma D_61640 : decode_any W_61640 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61644 : bv 32 := 0xfa0a2537.
Lemma F_61644 : fetch_word Ubsan.M.loaded_segments (0x6169c : word) = Some W_61644.
Proof. vm_refl. Qed.
Lemma D_61644 : decode_any W_61644 = Some (Lui 10 1024162, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61648 : bv 32 := 0xeff50593.
Lemma F_61648 : fetch_word Ubsan.M.loaded_segments (0x616a0 : word) = Some W_61648.
Proof. vm_refl. Qed.
Lemma D_61648 : decode_any W_61648 = Some (OpImm ALU_ADD 11 10 3839, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6164c : bv 32 := 0x00b405bb.
Lemma F_6164c : fetch_word Ubsan.M.loaded_segments (0x616a4 : word) = Some W_6164c.
Proof. vm_refl. Qed.
Lemma D_6164c : decode_any W_6164c = Some (Op32 ALU_ADD 11 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61650 : bv 32 := 0xf005051b.
Lemma F_61650 : fetch_word Ubsan.M.loaded_segments (0x616a8 : word) = Some W_61650.
Proof. vm_refl. Qed.
Lemma D_61650 : decode_any W_61650 = Some (OpImm32 10 10 3840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61654 : bv 32 := 0x00a5f463.
Lemma F_61654 : fetch_word Ubsan.M.loaded_segments (0x616ac : word) = Some W_61654.
Proof. vm_refl. Qed.
Lemma D_61654 : decode_any W_61654 = Some (Branch BC_GEU 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61658 : bv 32 := 0x03200413.
Lemma F_61658 : fetch_word Ubsan.M.loaded_segments (0x616b0 : word) = Some W_61658.
Proof. vm_refl. Qed.
Lemma D_61658 : decode_any W_61658 = Some (OpImm ALU_ADD 8 0 50, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6165c : bv 32 := 0x00100513.
Lemma F_6165c : fetch_word Ubsan.M.loaded_segments (0x616b4 : word) = Some W_6165c.
Proof. vm_refl. Qed.
Lemma D_6165c : decode_any W_6165c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61660 : bv 32 := 0x02000593.
Lemma F_61660 : fetch_word Ubsan.M.loaded_segments (0x616b8 : word) = Some W_61660.
Proof. vm_refl. Qed.
Lemma D_61660 : decode_any W_61660 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61664 : bv 32 := 0x5c5800ef.
Lemma F_61664 : fetch_word Ubsan.M.loaded_segments (0x616bc : word) = Some W_61664.
Proof. vm_refl. Qed.
Lemma D_61664 : decode_any W_61664 = Some (Jal 1 527812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61668 : bv 32 := 0x00050493.
Lemma F_61668 : fetch_word Ubsan.M.loaded_segments (0x616c0 : word) = Some W_61668.
Proof. vm_refl. Qed.
Lemma D_61668 : decode_any W_61668 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6166c : bv 32 := 0x00400593.
Lemma F_6166c : fetch_word Ubsan.M.loaded_segments (0x616c4 : word) = Some W_6166c.
Proof. vm_refl. Qed.
Lemma D_6166c : decode_any W_6166c = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61670 : bv 32 := 0x00040513.
Lemma F_61670 : fetch_word Ubsan.M.loaded_segments (0x616c8 : word) = Some W_61670.
Proof. vm_refl. Qed.
Lemma D_61670 : decode_any W_61670 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61674 : bv 32 := 0x5b5800ef.
Lemma F_61674 : fetch_word Ubsan.M.loaded_segments (0x616cc : word) = Some W_61674.
Proof. vm_refl. Qed.
Lemma D_61674 : decode_any W_61674 = Some (Jal 1 527796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61678 : bv 32 := 0x0c048063.
Lemma F_61678 : fetch_word Ubsan.M.loaded_segments (0x616d0 : word) = Some W_61678.
Proof. vm_refl. Qed.
Lemma D_61678 : decode_any W_61678 = Some (Branch BC_EQ 9 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6167c : bv 32 := 0x0074f613.
Lemma F_6167c : fetch_word Ubsan.M.loaded_segments (0x616d4 : word) = Some W_6167c.
Proof. vm_refl. Qed.
Lemma D_6167c : decode_any W_6167c = Some (OpImm ALU_AND 12 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61680 : bv 32 := 0x0a061c63.
Lemma F_61680 : fetch_word Ubsan.M.loaded_segments (0x616d8 : word) = Some W_61680.
Proof. vm_refl. Qed.
Lemma D_61680 : decode_any W_61680 = Some (Branch BC_NE 12 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61684 : bv 32 := 0x00a4bc23.
Lemma F_61684 : fetch_word Ubsan.M.loaded_segments (0x616dc : word) = Some W_61684.
Proof. vm_refl. Qed.
Lemma D_61684 : decode_any W_61684 = Some (Store SZ8 9 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61688 : bv 32 := 0x02050663.
Lemma F_61688 : fetch_word Ubsan.M.loaded_segments (0x616e0 : word) = Some W_61688.
Proof. vm_refl. Qed.
Lemma D_61688 : decode_any W_61688 = Some (Branch BC_EQ 10 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6168c : bv 32 := 0x0084a023.
Lemma F_6168c : fetch_word Ubsan.M.loaded_segments (0x616e4 : word) = Some W_6168c.
Proof. vm_refl. Qed.
Lemma D_6168c : decode_any W_6168c = Some (Store SZ4 9 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61690 : bv 32 := 0x0004a223.
Lemma F_61690 : fetch_word Ubsan.M.loaded_segments (0x616e8 : word) = Some W_61690.
Proof. vm_refl. Qed.
Lemma D_61690 : decode_any W_61690 = Some (Store SZ4 9 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61694 : bv 32 := 0x0310000f.
Lemma F_61694 : fetch_word Ubsan.M.loaded_segments (0x616ec : word) = Some W_61694.
Proof. vm_refl. Qed.
Lemma D_61694 : decode_any W_61694 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61698 : bv 32 := 0x00100593.
Lemma F_61698 : fetch_word Ubsan.M.loaded_segments (0x616f0 : word) = Some W_61698.
Proof. vm_refl. Qed.
Lemma D_61698 : decode_any W_61698 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6169c : bv 32 := 0x00b4a423.
Lemma F_6169c : fetch_word Ubsan.M.loaded_segments (0x616f4 : word) = Some W_6169c.
Proof. vm_refl. Qed.
Lemma D_6169c : decode_any W_6169c = Some (Store SZ4 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_616a0 : bv 32 := 0x3f8005b7.
Lemma F_616a0 : fetch_word Ubsan.M.loaded_segments (0x616f8 : word) = Some W_616a0.
Proof. vm_refl. Qed.
Lemma D_616a0 : decode_any W_616a0 = Some (Lui 11 260096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_616a4 : bv 32 := 0x0330000f.
Lemma F_616a4 : fetch_word Ubsan.M.loaded_segments (0x616fc : word) = Some W_616a4.
Proof. vm_refl. Qed.
Lemma D_616a4 : decode_any W_616a4 = Some (Fence 0 3 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_616a8 : bv 32 := 0x0004a623.
Lemma F_616a8 : fetch_word Ubsan.M.loaded_segments (0x61700 : word) = Some W_616a8.
Proof. vm_refl. Qed.
Lemma D_616a8 : decode_any W_616a8 = Some (Store SZ4 9 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_616ac : bv 32 := 0x00b4a823.
Lemma F_616ac : fetch_word Ubsan.M.loaded_segments (0x61704 : word) = Some W_616ac.
Proof. vm_refl. Qed.
Lemma D_616ac : decode_any W_616ac = Some (Store SZ4 9 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_616b0 : bv 32 := 0x0700006f.
Lemma F_616b0 : fetch_word Ubsan.M.loaded_segments (0x61708 : word) = Some W_616b0.
Proof. vm_refl. Qed.
Lemma D_616b0 : decode_any W_616b0 = Some (Jal 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61720 : bv 32 := 0x00048513.
Lemma F_61720 : fetch_word Ubsan.M.loaded_segments (0x61778 : word) = Some W_61720.
Proof. vm_refl. Qed.
Lemma D_61720 : decode_any W_61720 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61724 : bv 32 := 0x01813083.
Lemma F_61724 : fetch_word Ubsan.M.loaded_segments (0x6177c : word) = Some W_61724.
Proof. vm_refl. Qed.
Lemma D_61724 : decode_any W_61724 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61728 : bv 32 := 0x01013403.
Lemma F_61728 : fetch_word Ubsan.M.loaded_segments (0x61780 : word) = Some W_61728.
Proof. vm_refl. Qed.
Lemma D_61728 : decode_any W_61728 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6172c : bv 32 := 0x00813483.
Lemma F_6172c : fetch_word Ubsan.M.loaded_segments (0x61784 : word) = Some W_6172c.
Proof. vm_refl. Qed.
Lemma D_6172c : decode_any W_6172c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61730 : bv 32 := 0x02010113.
Lemma F_61730 : fetch_word Ubsan.M.loaded_segments (0x61788 : word) = Some W_61730.
Proof. vm_refl. Qed.
Lemma D_61730 : decode_any W_61730 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61734 : bv 32 := 0x00008067.
Lemma F_61734 : fetch_word Ubsan.M.loaded_segments (0x6178c : word) = Some W_61734.
Proof. vm_refl. Qed.
Lemma D_61734 : decode_any W_61734 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6173c : bv 32 := 0xfe010113.
Lemma F_6173c : fetch_word Ubsan.M.loaded_segments (0x61794 : word) = Some W_6173c.
Proof. vm_refl. Qed.
Lemma D_6173c : decode_any W_6173c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61740 : bv 32 := 0x00113c23.
Lemma F_61740 : fetch_word Ubsan.M.loaded_segments (0x61798 : word) = Some W_61740.
Proof. vm_refl. Qed.
Lemma D_61740 : decode_any W_61740 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61744 : bv 32 := 0x00813823.
Lemma F_61744 : fetch_word Ubsan.M.loaded_segments (0x6179c : word) = Some W_61744.
Proof. vm_refl. Qed.
Lemma D_61744 : decode_any W_61744 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61748 : bv 32 := 0x00913423.
Lemma F_61748 : fetch_word Ubsan.M.loaded_segments (0x617a0 : word) = Some W_61748.
Proof. vm_refl. Qed.
Lemma D_61748 : decode_any W_61748 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6174c : bv 32 := 0x04050a63.
Lemma F_6174c : fetch_word Ubsan.M.loaded_segments (0x617a4 : word) = Some W_6174c.
Proof. vm_refl. Qed.
Lemma D_6174c : decode_any W_6174c = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61750 : bv 32 := 0x00757593.
Lemma F_61750 : fetch_word Ubsan.M.loaded_segments (0x617a8 : word) = Some W_61750.
Proof. vm_refl. Qed.
Lemma D_61750 : decode_any W_61750 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61754 : bv 32 := 0x08059c63.
Lemma F_61754 : fetch_word Ubsan.M.loaded_segments (0x617ac : word) = Some W_61754.
Proof. vm_refl. Qed.
Lemma D_61754 : decode_any W_61754 = Some (Branch BC_NE 11 0 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61758 : bv 32 := 0x00053403.
Lemma F_61758 : fetch_word Ubsan.M.loaded_segments (0x617b0 : word) = Some W_61758.
Proof. vm_refl. Qed.
Lemma D_61758 : decode_any W_61758 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6175c : bv 32 := 0x06040e63.
Lemma F_6175c : fetch_word Ubsan.M.loaded_segments (0x617b4 : word) = Some W_6175c.
Proof. vm_refl. Qed.
Lemma D_6175c : decode_any W_6175c = Some (Branch BC_EQ 8 0 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61760 : bv 32 := 0x00747593.
Lemma F_61760 : fetch_word Ubsan.M.loaded_segments (0x617b8 : word) = Some W_61760.
Proof. vm_refl. Qed.
Lemma D_61760 : decode_any W_61760 = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61764 : bv 32 := 0x08059463.
Lemma F_61764 : fetch_word Ubsan.M.loaded_segments (0x617bc : word) = Some W_61764.
Proof. vm_refl. Qed.
Lemma D_61764 : decode_any W_61764 = Some (Branch BC_NE 11 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61768 : bv 32 := 0x00840593.
Lemma F_61768 : fetch_word Ubsan.M.loaded_segments (0x617c0 : word) = Some W_61768.
Proof. vm_refl. Qed.
Lemma D_61768 : decode_any W_61768 = Some (OpImm ALU_ADD 11 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6176c : bv 32 := 0xfff00613.
Lemma F_6176c : fetch_word Ubsan.M.loaded_segments (0x617c4 : word) = Some W_6176c.
Proof. vm_refl. Qed.
Lemma D_6176c : decode_any W_6176c = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61770 : bv 32 := 0x06c5a5af.
Lemma F_61770 : fetch_word Ubsan.M.loaded_segments (0x617c8 : word) = Some W_61770.
Proof. vm_refl. Qed.
Lemma D_61770 : decode_any W_61770 = Some (Amo AMO_ADD AW true true 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61774 : bv 32 := 0x00100613.
Lemma F_61774 : fetch_word Ubsan.M.loaded_segments (0x617cc : word) = Some W_61774.
Proof. vm_refl. Qed.
Lemma D_61774 : decode_any W_61774 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61778 : bv 32 := 0x02c59063.
Lemma F_61778 : fetch_word Ubsan.M.loaded_segments (0x617d0 : word) = Some W_61778.
Proof. vm_refl. Qed.
Lemma D_61778 : decode_any W_61778 = Some (Branch BC_NE 11 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6177c : bv 32 := 0x00050493.
Lemma F_6177c : fetch_word Ubsan.M.loaded_segments (0x617d4 : word) = Some W_6177c.
Proof. vm_refl. Qed.
Lemma D_6177c : decode_any W_6177c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61780 : bv 32 := 0x01843503.
Lemma F_61780 : fetch_word Ubsan.M.loaded_segments (0x617d8 : word) = Some W_61780.
Proof. vm_refl. Qed.
Lemma D_61780 : decode_any W_61780 = Some (Load SZ8 true 10 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61784 : bv 32 := 0x00050463.
Lemma F_61784 : fetch_word Ubsan.M.loaded_segments (0x617dc : word) = Some W_61784.
Proof. vm_refl. Qed.
Lemma D_61784 : decode_any W_61784 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61788 : bv 32 := 0x5d9800ef.
Lemma F_61788 : fetch_word Ubsan.M.loaded_segments (0x617e0 : word) = Some W_61788.
Proof. vm_refl. Qed.
Lemma D_61788 : decode_any W_61788 = Some (Jal 1 527832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6178c : bv 32 := 0x00040513.
Lemma F_6178c : fetch_word Ubsan.M.loaded_segments (0x617e4 : word) = Some W_6178c.
Proof. vm_refl. Qed.
Lemma D_6178c : decode_any W_6178c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61790 : bv 32 := 0x5d1800ef.
Lemma F_61790 : fetch_word Ubsan.M.loaded_segments (0x617e8 : word) = Some W_61790.
Proof. vm_refl. Qed.
Lemma D_61790 : decode_any W_61790 = Some (Jal 1 527824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61794 : bv 32 := 0x00048513.
Lemma F_61794 : fetch_word Ubsan.M.loaded_segments (0x617ec : word) = Some W_61794.
Proof. vm_refl. Qed.
Lemma D_61794 : decode_any W_61794 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61798 : bv 32 := 0x00053023.
Lemma F_61798 : fetch_word Ubsan.M.loaded_segments (0x617f0 : word) = Some W_61798.
Proof. vm_refl. Qed.
Lemma D_61798 : decode_any W_61798 = Some (Store SZ8 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6179c : bv 32 := 0x03c0006f.
Lemma F_6179c : fetch_word Ubsan.M.loaded_segments (0x617f4 : word) = Some W_6179c.
Proof. vm_refl. Qed.
Lemma D_6179c : decode_any W_6179c = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_617d8 : bv 32 := 0x01813083.
Lemma F_617d8 : fetch_word Ubsan.M.loaded_segments (0x61830 : word) = Some W_617d8.
Proof. vm_refl. Qed.
Lemma D_617d8 : decode_any W_617d8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_617dc : bv 32 := 0x01013403.
Lemma F_617dc : fetch_word Ubsan.M.loaded_segments (0x61834 : word) = Some W_617dc.
Proof. vm_refl. Qed.
Lemma D_617dc : decode_any W_617dc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_617e0 : bv 32 := 0x00813483.
Lemma F_617e0 : fetch_word Ubsan.M.loaded_segments (0x61838 : word) = Some W_617e0.
Proof. vm_refl. Qed.
Lemma D_617e0 : decode_any W_617e0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_617e4 : bv 32 := 0x02010113.
Lemma F_617e4 : fetch_word Ubsan.M.loaded_segments (0x6183c : word) = Some W_617e4.
Proof. vm_refl. Qed.
Lemma D_617e4 : decode_any W_617e4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_617e8 : bv 32 := 0x00008067.
Lemma F_617e8 : fetch_word Ubsan.M.loaded_segments (0x61840 : word) = Some W_617e8.
Proof. vm_refl. Qed.
Lemma D_617e8 : decode_any W_617e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_617f0 : bv 32 := 0xfe010113.
Lemma F_617f0 : fetch_word Ubsan.M.loaded_segments (0x61848 : word) = Some W_617f0.
Proof. vm_refl. Qed.
Lemma D_617f0 : decode_any W_617f0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_617f4 : bv 32 := 0x00113c23.
Lemma F_617f4 : fetch_word Ubsan.M.loaded_segments (0x6184c : word) = Some W_617f4.
Proof. vm_refl. Qed.
Lemma D_617f4 : decode_any W_617f4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_617f8 : bv 32 := 0x00813823.
Lemma F_617f8 : fetch_word Ubsan.M.loaded_segments (0x61850 : word) = Some W_617f8.
Proof. vm_refl. Qed.
Lemma D_617f8 : decode_any W_617f8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_617fc : bv 32 := 0x00913423.
Lemma F_617fc : fetch_word Ubsan.M.loaded_segments (0x61854 : word) = Some W_617fc.
Proof. vm_refl. Qed.
Lemma D_617fc : decode_any W_617fc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61800 : bv 32 := 0x00813027.
Lemma F_61800 : fetch_word Ubsan.M.loaded_segments (0x61858 : word) = Some W_61800.
Proof. vm_refl. Qed.
Lemma D_61800 : decode_any W_61800 = Some (FStore FMT_D 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61804 : bv 32 := 0x0a050863.
Lemma F_61804 : fetch_word Ubsan.M.loaded_segments (0x6185c : word) = Some W_61804.
Proof. vm_refl. Qed.
Lemma D_61804 : decode_any W_61804 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61808 : bv 32 := 0x00757593.
Lemma F_61808 : fetch_word Ubsan.M.loaded_segments (0x61860 : word) = Some W_61808.
Proof. vm_refl. Qed.
Lemma D_61808 : decode_any W_61808 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6180c : bv 32 := 0x10059463.
Lemma F_6180c : fetch_word Ubsan.M.loaded_segments (0x61864 : word) = Some W_6180c.
Proof. vm_refl. Qed.
Lemma D_6180c : decode_any W_6180c = Some (Branch BC_NE 11 0 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61810 : bv 32 := 0x00052583.
Lemma F_61810 : fetch_word Ubsan.M.loaded_segments (0x61868 : word) = Some W_61810.
Proof. vm_refl. Qed.
Lemma D_61810 : decode_any W_61810 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61814 : bv 32 := 0x00452483.
Lemma F_61814 : fetch_word Ubsan.M.loaded_segments (0x6186c : word) = Some W_61814.
Proof. vm_refl. Qed.
Lemma D_61814 : decode_any W_61814 = Some (Load SZ4 true 9 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61818 : bv 32 := 0x04b4c463.
Lemma F_61818 : fetch_word Ubsan.M.loaded_segments (0x61870 : word) = Some W_61818.
Proof. vm_refl. Qed.
Lemma D_61818 : decode_any W_61818 = Some (Branch BC_LT 9 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6181c : bv 32 := 0x00050413.
Lemma F_6181c : fetch_word Ubsan.M.loaded_segments (0x61874 : word) = Some W_6181c.
Proof. vm_refl. Qed.
Lemma D_6181c : decode_any W_6181c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61820 : bv 32 := 0x20a50453.
Lemma F_61820 : fetch_word Ubsan.M.loaded_segments (0x61878 : word) = Some W_61820.
Proof. vm_refl. Qed.
Lemma D_61820 : decode_any W_61820 = Some (Fsgnj F_SGNJ FMT_S 8 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61824 : bv 32 := 0x140000ef.
Lemma F_61824 : fetch_word Ubsan.M.loaded_segments (0x6187c : word) = Some W_61824.
Proof. vm_refl. Qed.
Lemma D_61824 : decode_any W_61824 = Some (Jal 1 320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61828 : bv 32 := 0x20840553.
Lemma F_61828 : fetch_word Ubsan.M.loaded_segments (0x61880 : word) = Some W_61828.
Proof. vm_refl. Qed.
Lemma D_61828 : decode_any W_61828 = Some (Fsgnj F_SGNJ FMT_S 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6182c : bv 32 := 0x00050593.
Lemma F_6182c : fetch_word Ubsan.M.loaded_segments (0x61884 : word) = Some W_6182c.
Proof. vm_refl. Qed.
Lemma D_6182c : decode_any W_6182c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61830 : bv 32 := 0x00040513.
Lemma F_61830 : fetch_word Ubsan.M.loaded_segments (0x61888 : word) = Some W_61830.
Proof. vm_refl. Qed.
Lemma D_61830 : decode_any W_61830 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61834 : bv 32 := 0x02058663.
Lemma F_61834 : fetch_word Ubsan.M.loaded_segments (0x6188c : word) = Some W_61834.
Proof. vm_refl. Qed.
Lemma D_61834 : decode_any W_61834 = Some (Branch BC_EQ 11 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61860 : bv 32 := 0x01853603.
Lemma F_61860 : fetch_word Ubsan.M.loaded_segments (0x618b8 : word) = Some W_61860.
Proof. vm_refl. Qed.
Lemma D_61860 : decode_any W_61860 = Some (Load SZ8 true 12 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61864 : bv 32 := 0x00249593.
Lemma F_61864 : fetch_word Ubsan.M.loaded_segments (0x618bc : word) = Some W_61864.
Proof. vm_refl. Qed.
Lemma D_61864 : decode_any W_61864 = Some (ShiftImm ALU_SLL 11 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61868 : bv 32 := 0x00b605b3.
Lemma F_61868 : fetch_word Ubsan.M.loaded_segments (0x618c0 : word) = Some W_61868.
Proof. vm_refl. Qed.
Lemma D_61868 : decode_any W_61868 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6186c : bv 32 := 0x00c036b3.
Lemma F_6186c : fetch_word Ubsan.M.loaded_segments (0x618c4 : word) = Some W_6186c.
Proof. vm_refl. Qed.
Lemma D_6186c : decode_any W_6186c = Some (Op ALU_SLTU 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61870 : bv 32 := 0x0015b713.
Lemma F_61870 : fetch_word Ubsan.M.loaded_segments (0x618c8 : word) = Some W_61870.
Proof. vm_refl. Qed.
Lemma D_61870 : decode_any W_61870 = Some (OpImm ALU_SLTU 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61874 : bv 32 := 0x0ae68063.
Lemma F_61874 : fetch_word Ubsan.M.loaded_segments (0x618cc : word) = Some W_61874.
Proof. vm_refl. Qed.
Lemma D_61874 : decode_any W_61874 = Some (Branch BC_EQ 13 14 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61878 : bv 32 := 0x00c5b6b3.
Lemma F_61878 : fetch_word Ubsan.M.loaded_segments (0x618d0 : word) = Some W_61878.
Proof. vm_refl. Qed.
Lemma D_61878 : decode_any W_61878 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6187c : bv 32 := 0x0004a713.
Lemma F_6187c : fetch_word Ubsan.M.loaded_segments (0x618d4 : word) = Some W_6187c.
Proof. vm_refl. Qed.
Lemma D_6187c : decode_any W_6187c = Some (OpImm ALU_SLT 14 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61880 : bv 32 := 0x00e6c6b3.
Lemma F_61880 : fetch_word Ubsan.M.loaded_segments (0x618d8 : word) = Some W_61880.
Proof. vm_refl. Qed.
Lemma D_61880 : decode_any W_61880 = Some (Op ALU_XOR 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61884 : bv 32 := 0x0016c693.
Lemma F_61884 : fetch_word Ubsan.M.loaded_segments (0x618dc : word) = Some W_61884.
Proof. vm_refl. Qed.
Lemma D_61884 : decode_any W_61884 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61888 : bv 32 := 0x08068663.
Lemma F_61888 : fetch_word Ubsan.M.loaded_segments (0x618e0 : word) = Some W_61888.
Proof. vm_refl. Qed.
Lemma D_61888 : decode_any W_61888 = Some (Branch BC_EQ 13 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6188c : bv 32 := 0x08060463.
Lemma F_6188c : fetch_word Ubsan.M.loaded_segments (0x618e4 : word) = Some W_6188c.
Proof. vm_refl. Qed.
Lemma D_6188c : decode_any W_6188c = Some (Branch BC_EQ 12 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61890 : bv 32 := 0x0035f613.
Lemma F_61890 : fetch_word Ubsan.M.loaded_segments (0x618e8 : word) = Some W_61890.
Proof. vm_refl. Qed.
Lemma D_61890 : decode_any W_61890 = Some (OpImm ALU_AND 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61894 : bv 32 := 0x08061063.
Lemma F_61894 : fetch_word Ubsan.M.loaded_segments (0x618ec : word) = Some W_61894.
Proof. vm_refl. Qed.
Lemma D_61894 : decode_any W_61894 = Some (Branch BC_NE 12 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61898 : bv 32 := 0x00452683.
Lemma F_61898 : fetch_word Ubsan.M.loaded_segments (0x618f0 : word) = Some W_61898.
Proof. vm_refl. Qed.
Lemma D_61898 : decode_any W_61898 = Some (Load SZ4 true 13 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6189c : bv 32 := 0x0016861b.
Lemma F_6189c : fetch_word Ubsan.M.loaded_segments (0x618f4 : word) = Some W_6189c.
Proof. vm_refl. Qed.
Lemma D_6189c : decode_any W_6189c = Some (OpImm32 12 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618a0 : bv 32 := 0x00a5a027.
Lemma F_618a0 : fetch_word Ubsan.M.loaded_segments (0x618f8 : word) = Some W_618a0.
Proof. vm_refl. Qed.
Lemma D_618a0 : decode_any W_618a0 = Some (FStore FMT_S 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618a4 : bv 32 := 0x06d64863.
Lemma F_618a4 : fetch_word Ubsan.M.loaded_segments (0x618fc : word) = Some W_618a4.
Proof. vm_refl. Qed.
Lemma D_618a4 : decode_any W_618a4 = Some (Branch BC_LT 12 13 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618a8 : bv 32 := 0x00000593.
Lemma F_618a8 : fetch_word Ubsan.M.loaded_segments (0x61900 : word) = Some W_618a8.
Proof. vm_refl. Qed.
Lemma D_618a8 : decode_any W_618a8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618ac : bv 32 := 0x00c52223.
Lemma F_618ac : fetch_word Ubsan.M.loaded_segments (0x61904 : word) = Some W_618ac.
Proof. vm_refl. Qed.
Lemma D_618ac : decode_any W_618ac = Some (Store SZ4 10 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618b0 : bv 32 := 0x0480006f.
Lemma F_618b0 : fetch_word Ubsan.M.loaded_segments (0x61908 : word) = Some W_618b0.
Proof. vm_refl. Qed.
Lemma D_618b0 : decode_any W_618b0 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618f8 : bv 32 := 0x00058513.
Lemma F_618f8 : fetch_word Ubsan.M.loaded_segments (0x61950 : word) = Some W_618f8.
Proof. vm_refl. Qed.
Lemma D_618f8 : decode_any W_618f8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_618fc : bv 32 := 0x01813083.
Lemma F_618fc : fetch_word Ubsan.M.loaded_segments (0x61954 : word) = Some W_618fc.
Proof. vm_refl. Qed.
Lemma D_618fc : decode_any W_618fc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61900 : bv 32 := 0x01013403.
Lemma F_61900 : fetch_word Ubsan.M.loaded_segments (0x61958 : word) = Some W_61900.
Proof. vm_refl. Qed.
Lemma D_61900 : decode_any W_61900 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61904 : bv 32 := 0x00813483.
Lemma F_61904 : fetch_word Ubsan.M.loaded_segments (0x6195c : word) = Some W_61904.
Proof. vm_refl. Qed.
Lemma D_61904 : decode_any W_61904 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61908 : bv 32 := 0x00013407.
Lemma F_61908 : fetch_word Ubsan.M.loaded_segments (0x61960 : word) = Some W_61908.
Proof. vm_refl. Qed.
Lemma D_61908 : decode_any W_61908 = Some (FLoad FMT_D 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6190c : bv 32 := 0x02010113.
Lemma F_6190c : fetch_word Ubsan.M.loaded_segments (0x61964 : word) = Some W_6190c.
Proof. vm_refl. Qed.
Lemma D_6190c : decode_any W_6190c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61910 : bv 32 := 0x00008067.
Lemma F_61910 : fetch_word Ubsan.M.loaded_segments (0x61968 : word) = Some W_61910.
Proof. vm_refl. Qed.
Lemma D_61910 : decode_any W_61910 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61918 : bv 32 := 0x00050a63.
Lemma F_61918 : fetch_word Ubsan.M.loaded_segments (0x61970 : word) = Some W_61918.
Proof. vm_refl. Qed.
Lemma D_61918 : decode_any W_61918 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6191c : bv 32 := 0x00757593.
Lemma F_6191c : fetch_word Ubsan.M.loaded_segments (0x61974 : word) = Some W_6191c.
Proof. vm_refl. Qed.
Lemma D_6191c : decode_any W_6191c = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61920 : bv 32 := 0x04059063.
Lemma F_61920 : fetch_word Ubsan.M.loaded_segments (0x61978 : word) = Some W_61920.
Proof. vm_refl. Qed.
Lemma D_61920 : decode_any W_61920 = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61924 : bv 32 := 0x00452503.
Lemma F_61924 : fetch_word Ubsan.M.loaded_segments (0x6197c : word) = Some W_61924.
Proof. vm_refl. Qed.
Lemma D_61924 : decode_any W_61924 = Some (Load SZ4 true 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61928 : bv 32 := 0x00008067.
Lemma F_61928 : fetch_word Ubsan.M.loaded_segments (0x61980 : word) = Some W_61928.
Proof. vm_refl. Qed.
Lemma D_61928 : decode_any W_61928 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61964 : bv 32 := 0xff010113.
Lemma F_61964 : fetch_word Ubsan.M.loaded_segments (0x619bc : word) = Some W_61964.
Proof. vm_refl. Qed.
Lemma D_61964 : decode_any W_61964 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61968 : bv 32 := 0x00113423.
Lemma F_61968 : fetch_word Ubsan.M.loaded_segments (0x619c0 : word) = Some W_61968.
Proof. vm_refl. Qed.
Lemma D_61968 : decode_any W_61968 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6196c : bv 32 := 0x00813023.
Lemma F_6196c : fetch_word Ubsan.M.loaded_segments (0x619c4 : word) = Some W_6196c.
Proof. vm_refl. Qed.
Lemma D_6196c : decode_any W_6196c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61970 : bv 32 := 0x00757593.
Lemma F_61970 : fetch_word Ubsan.M.loaded_segments (0x619c8 : word) = Some W_61970.
Proof. vm_refl. Qed.
Lemma D_61970 : decode_any W_61970 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61974 : bv 32 := 0x10059063.
Lemma F_61974 : fetch_word Ubsan.M.loaded_segments (0x619cc : word) = Some W_61974.
Proof. vm_refl. Qed.
Lemma D_61974 : decode_any W_61974 = Some (Branch BC_NE 11 0 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61978 : bv 32 := 0x00056603.
Lemma F_61978 : fetch_word Ubsan.M.loaded_segments (0x619d0 : word) = Some W_61978.
Proof. vm_refl. Qed.
Lemma D_61978 : decode_any W_61978 = Some (Load SZ4 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6197c : bv 32 := 0x05f5e5b7.
Lemma F_6197c : fetch_word Ubsan.M.loaded_segments (0x619d4 : word) = Some W_6197c.
Proof. vm_refl. Qed.
Lemma D_6197c : decode_any W_6197c = Some (Lui 11 24414, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61980 : bv 32 := 0x1015859b.
Lemma F_61980 : fetch_word Ubsan.M.loaded_segments (0x619d8 : word) = Some W_61980.
Proof. vm_refl. Qed.
Lemma D_61980 : decode_any W_61980 = Some (OpImm32 11 11 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61984 : bv 32 := 0x02b66663.
Lemma F_61984 : fetch_word Ubsan.M.loaded_segments (0x619dc : word) = Some W_61984.
Proof. vm_refl. Qed.
Lemma D_61984 : decode_any W_61984 = Some (Branch BC_LTU 12 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_619b0 : bv 32 := 0x02faf5b7.
Lemma F_619b0 : fetch_word Ubsan.M.loaded_segments (0x61a08 : word) = Some W_619b0.
Proof. vm_refl. Qed.
Lemma D_619b0 : decode_any W_619b0 = Some (Lui 11 12207, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_619b4 : bv 32 := 0x0815859b.
Lemma F_619b4 : fetch_word Ubsan.M.loaded_segments (0x61a0c : word) = Some W_619b4.
Proof. vm_refl. Qed.
Lemma D_619b4 : decode_any W_619b4 = Some (OpImm32 11 11 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_619b8 : bv 32 := 0x02b66663.
Lemma F_619b8 : fetch_word Ubsan.M.loaded_segments (0x61a10 : word) = Some W_619b8.
Proof. vm_refl. Qed.
Lemma D_619b8 : decode_any W_619b8 = Some (Branch BC_LTU 12 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_619e4 : bv 32 := 0x00261593.
Lemma F_619e4 : fetch_word Ubsan.M.loaded_segments (0x61a3c : word) = Some W_619e4.
Proof. vm_refl. Qed.
Lemma D_619e4 : decode_any W_619e4 = Some (ShiftImm ALU_SLL 11 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_619e8 : bv 32 := 0x00361613.
Lemma F_619e8 : fetch_word Ubsan.M.loaded_segments (0x61a40 : word) = Some W_619e8.
Proof. vm_refl. Qed.
Lemma D_619e8 : decode_any W_619e8 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_619ec : bv 32 := 0x01850693.
Lemma F_619ec : fetch_word Ubsan.M.loaded_segments (0x61a44 : word) = Some W_619ec.
Proof. vm_refl. Qed.
Lemma D_619ec : decode_any W_619ec = Some (OpImm ALU_ADD 13 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_619f0 : bv 32 := 0x00050413.
Lemma F_619f0 : fetch_word Ubsan.M.loaded_segments (0x61a48 : word) = Some W_619f0.
Proof. vm_refl. Qed.
Lemma D_619f0 : decode_any W_619f0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_619f4 : bv 32 := 0x00068513.
Lemma F_619f4 : fetch_word Ubsan.M.loaded_segments (0x61a4c : word) = Some W_619f4.
Proof. vm_refl. Qed.
Lemma D_619f4 : decode_any W_619f4 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_619f8 : bv 32 := 0x8e5fc0ef.
Lemma F_619f8 : fetch_word Ubsan.M.loaded_segments (0x61a50 : word) = Some W_619f8.
Proof. vm_refl. Qed.
Lemma D_619f8 : decode_any W_619f8 = Some (Jal 1 2083044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_619fc : bv 32 := 0x00a43c23.
Lemma F_619fc : fetch_word Ubsan.M.loaded_segments (0x61a54 : word) = Some W_619fc.
Proof. vm_refl. Qed.
Lemma D_619fc : decode_any W_619fc = Some (Store SZ8 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a00 : bv 32 := 0x02050463.
Lemma F_61a00 : fetch_word Ubsan.M.loaded_segments (0x61a58 : word) = Some W_61a00.
Proof. vm_refl. Qed.
Lemma D_61a00 : decode_any W_61a00 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a04 : bv 32 := 0x00040593.
Lemma F_61a04 : fetch_word Ubsan.M.loaded_segments (0x61a5c : word) = Some W_61a04.
Proof. vm_refl. Qed.
Lemma D_61a04 : decode_any W_61a04 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a08 : bv 32 := 0x00042603.
Lemma F_61a08 : fetch_word Ubsan.M.loaded_segments (0x61a60 : word) = Some W_61a08.
Proof. vm_refl. Qed.
Lemma D_61a08 : decode_any W_61a08 = Some (Load SZ4 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a0c : bv 32 := 0x40000537.
Lemma F_61a0c : fetch_word Ubsan.M.loaded_segments (0x61a64 : word) = Some W_61a0c.
Proof. vm_refl. Qed.
Lemma D_61a0c : decode_any W_61a0c = Some (Lui 10 262144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a10 : bv 32 := 0x00a6053b.
Lemma F_61a10 : fetch_word Ubsan.M.loaded_segments (0x61a68 : word) = Some W_61a10.
Proof. vm_refl. Qed.
Lemma D_61a10 : decode_any W_61a10 = Some (Op32 ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a14 : bv 32 := 0x06054063.
Lemma F_61a14 : fetch_word Ubsan.M.loaded_segments (0x61a6c : word) = Some W_61a14.
Proof. vm_refl. Qed.
Lemma D_61a14 : decode_any W_61a14 = Some (Branch BC_LT 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a18 : bv 32 := 0x00000513.
Lemma F_61a18 : fetch_word Ubsan.M.loaded_segments (0x61a70 : word) = Some W_61a18.
Proof. vm_refl. Qed.
Lemma D_61a18 : decode_any W_61a18 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a1c : bv 32 := 0x00161613.
Lemma F_61a1c : fetch_word Ubsan.M.loaded_segments (0x61a74 : word) = Some W_61a1c.
Proof. vm_refl. Qed.
Lemma D_61a1c : decode_any W_61a1c = Some (ShiftImm ALU_SLL 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a20 : bv 32 := 0x00c5a023.
Lemma F_61a20 : fetch_word Ubsan.M.loaded_segments (0x61a78 : word) = Some W_61a20.
Proof. vm_refl. Qed.
Lemma D_61a20 : decode_any W_61a20 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a24 : bv 32 := 0x0400006f.
Lemma F_61a24 : fetch_word Ubsan.M.loaded_segments (0x61a7c : word) = Some W_61a24.
Proof. vm_refl. Qed.
Lemma D_61a24 : decode_any W_61a24 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a64 : bv 32 := 0x00813083.
Lemma F_61a64 : fetch_word Ubsan.M.loaded_segments (0x61abc : word) = Some W_61a64.
Proof. vm_refl. Qed.
Lemma D_61a64 : decode_any W_61a64 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a68 : bv 32 := 0x00013403.
Lemma F_61a68 : fetch_word Ubsan.M.loaded_segments (0x61ac0 : word) = Some W_61a68.
Proof. vm_refl. Qed.
Lemma D_61a68 : decode_any W_61a68 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a6c : bv 32 := 0x01010113.
Lemma F_61a6c : fetch_word Ubsan.M.loaded_segments (0x61ac4 : word) = Some W_61a6c.
Proof. vm_refl. Qed.
Lemma D_61a6c : decode_any W_61a6c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a70 : bv 32 := 0x00008067.
Lemma F_61a70 : fetch_word Ubsan.M.loaded_segments (0x61ac8 : word) = Some W_61a70.
Proof. vm_refl. Qed.
Lemma D_61a70 : decode_any W_61a70 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a78 : bv 32 := 0x06060063.
Lemma F_61a78 : fetch_word Ubsan.M.loaded_segments (0x61ad0 : word) = Some W_61a78.
Proof. vm_refl. Qed.
Lemma D_61a78 : decode_any W_61a78 = Some (Branch BC_EQ 12 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a7c : bv 32 := 0x00367693.
Lemma F_61a7c : fetch_word Ubsan.M.loaded_segments (0x61ad4 : word) = Some W_61a7c.
Proof. vm_refl. Qed.
Lemma D_61a7c : decode_any W_61a7c = Some (OpImm ALU_AND 13 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a80 : bv 32 := 0x0e069263.
Lemma F_61a80 : fetch_word Ubsan.M.loaded_segments (0x61ad8 : word) = Some W_61a80.
Proof. vm_refl. Qed.
Lemma D_61a80 : decode_any W_61a80 = Some (Branch BC_NE 13 0 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a84 : bv 32 := 0x00062023.
Lemma F_61a84 : fetch_word Ubsan.M.loaded_segments (0x61adc : word) = Some W_61a84.
Proof. vm_refl. Qed.
Lemma D_61a84 : decode_any W_61a84 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a88 : bv 32 := 0x0a050463.
Lemma F_61a88 : fetch_word Ubsan.M.loaded_segments (0x61ae0 : word) = Some W_61a88.
Proof. vm_refl. Qed.
Lemma D_61a88 : decode_any W_61a88 = Some (Branch BC_EQ 10 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a8c : bv 32 := 0x0605cc63.
Lemma F_61a8c : fetch_word Ubsan.M.loaded_segments (0x61ae4 : word) = Some W_61a8c.
Proof. vm_refl. Qed.
Lemma D_61a8c : decode_any W_61a8c = Some (Branch BC_LT 11 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a90 : bv 32 := 0x00757693.
Lemma F_61a90 : fetch_word Ubsan.M.loaded_segments (0x61ae8 : word) = Some W_61a90.
Proof. vm_refl. Qed.
Lemma D_61a90 : decode_any W_61a90 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a94 : bv 32 := 0x0c069863.
Lemma F_61a94 : fetch_word Ubsan.M.loaded_segments (0x61aec : word) = Some W_61a94.
Proof. vm_refl. Qed.
Lemma D_61a94 : decode_any W_61a94 = Some (Branch BC_NE 13 0 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a98 : bv 32 := 0x00452683.
Lemma F_61a98 : fetch_word Ubsan.M.loaded_segments (0x61af0 : word) = Some W_61a98.
Proof. vm_refl. Qed.
Lemma D_61a98 : decode_any W_61a98 = Some (Load SZ4 true 13 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61a9c : bv 32 := 0x06d5d463.
Lemma F_61a9c : fetch_word Ubsan.M.loaded_segments (0x61af4 : word) = Some W_61a9c.
Proof. vm_refl. Qed.
Lemma D_61a9c : decode_any W_61a9c = Some (Branch BC_GE 11 13 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61aa0 : bv 32 := 0x01853503.
Lemma F_61aa0 : fetch_word Ubsan.M.loaded_segments (0x61af8 : word) = Some W_61aa0.
Proof. vm_refl. Qed.
Lemma D_61aa0 : decode_any W_61aa0 = Some (Load SZ8 true 10 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61aa4 : bv 32 := 0x00259593.
Lemma F_61aa4 : fetch_word Ubsan.M.loaded_segments (0x61afc : word) = Some W_61aa4.
Proof. vm_refl. Qed.
Lemma D_61aa4 : decode_any W_61aa4 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61aa8 : bv 32 := 0x00b505b3.
Lemma F_61aa8 : fetch_word Ubsan.M.loaded_segments (0x61b00 : word) = Some W_61aa8.
Proof. vm_refl. Qed.
Lemma D_61aa8 : decode_any W_61aa8 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61aac : bv 32 := 0x0aa5ec63.
Lemma F_61aac : fetch_word Ubsan.M.loaded_segments (0x61b04 : word) = Some W_61aac.
Proof. vm_refl. Qed.
Lemma D_61aac : decode_any W_61aac = Some (Branch BC_LTU 11 10 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ab0 : bv 32 := 0x00a036b3.
Lemma F_61ab0 : fetch_word Ubsan.M.loaded_segments (0x61b08 : word) = Some W_61ab0.
Proof. vm_refl. Qed.
Lemma D_61ab0 : decode_any W_61ab0 = Some (Op ALU_SLTU 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ab4 : bv 32 := 0x0015b713.
Lemma F_61ab4 : fetch_word Ubsan.M.loaded_segments (0x61b0c : word) = Some W_61ab4.
Proof. vm_refl. Qed.
Lemma D_61ab4 : decode_any W_61ab4 = Some (OpImm ALU_SLTU 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ab8 : bv 32 := 0x00e6c6b3.
Lemma F_61ab8 : fetch_word Ubsan.M.loaded_segments (0x61b10 : word) = Some W_61ab8.
Proof. vm_refl. Qed.
Lemma D_61ab8 : decode_any W_61ab8 = Some (Op ALU_XOR 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61abc : bv 32 := 0x0a068463.
Lemma F_61abc : fetch_word Ubsan.M.loaded_segments (0x61b14 : word) = Some W_61abc.
Proof. vm_refl. Qed.
Lemma D_61abc : decode_any W_61abc = Some (Branch BC_EQ 13 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ac0 : bv 32 := 0x0a050263.
Lemma F_61ac0 : fetch_word Ubsan.M.loaded_segments (0x61b18 : word) = Some W_61ac0.
Proof. vm_refl. Qed.
Lemma D_61ac0 : decode_any W_61ac0 = Some (Branch BC_EQ 10 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ac4 : bv 32 := 0x0035f513.
Lemma F_61ac4 : fetch_word Ubsan.M.loaded_segments (0x61b1c : word) = Some W_61ac4.
Proof. vm_refl. Qed.
Lemma D_61ac4 : decode_any W_61ac4 = Some (OpImm ALU_AND 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ac8 : bv 32 := 0x08051e63.
Lemma F_61ac8 : fetch_word Ubsan.M.loaded_segments (0x61b20 : word) = Some W_61ac8.
Proof. vm_refl. Qed.
Lemma D_61ac8 : decode_any W_61ac8 = Some (Branch BC_NE 10 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61acc : bv 32 := 0x0005a787.
Lemma F_61acc : fetch_word Ubsan.M.loaded_segments (0x61b24 : word) = Some W_61acc.
Proof. vm_refl. Qed.
Lemma D_61acc : decode_any W_61acc = Some (FLoad FMT_S 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ad0 : bv 32 := 0x00f62027.
Lemma F_61ad0 : fetch_word Ubsan.M.loaded_segments (0x61b28 : word) = Some W_61ad0.
Proof. vm_refl. Qed.
Lemma D_61ad0 : decode_any W_61ad0 = Some (FStore FMT_S 12 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_61ad4 : bv 32 := 0x00008067.
Lemma F_61ad4 : fetch_word Ubsan.M.loaded_segments (0x61b2c : word) = Some W_61ad4.
Proof. vm_refl. Qed.
Lemma D_61ad4 : decode_any W_61ad4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_645dc : bv 32 := 0x00050a63.
Lemma F_645dc : fetch_word Ubsan.M.loaded_segments (0x64634 : word) = Some W_645dc.
Proof. vm_refl. Qed.
Lemma D_645dc : decode_any W_645dc = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_645e0 : bv 32 := 0x00757593.
Lemma F_645e0 : fetch_word Ubsan.M.loaded_segments (0x64638 : word) = Some W_645e0.
Proof. vm_refl. Qed.
Lemma D_645e0 : decode_any W_645e0 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_645e4 : bv 32 := 0x04059063.
Lemma F_645e4 : fetch_word Ubsan.M.loaded_segments (0x6463c : word) = Some W_645e4.
Proof. vm_refl. Qed.
Lemma D_645e4 : decode_any W_645e4 = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_645e8 : bv 32 := 0x00852503.
Lemma F_645e8 : fetch_word Ubsan.M.loaded_segments (0x64640 : word) = Some W_645e8.
Proof. vm_refl. Qed.
Lemma D_645e8 : decode_any W_645e8 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_645ec : bv 32 := 0x00008067.
Lemma F_645ec : fetch_word Ubsan.M.loaded_segments (0x64644 : word) = Some W_645ec.
Proof. vm_refl. Qed.
Lemma D_645ec : decode_any W_645ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7c46c : bv 32 := 0x0fc0006f.
Lemma F_7c46c : fetch_word Ubsan.M.loaded_segments (0x7c4c4 : word) = Some W_7c46c.
Proof. vm_refl. Qed.
Lemma D_7c46c : decode_any W_7c46c = Some (Jal 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823a8 : bv 32 := 0xf9010113.
Lemma F_823a8 : fetch_word Ubsan.M.loaded_segments (0x82400 : word) = Some W_823a8.
Proof. vm_refl. Qed.
Lemma D_823a8 : decode_any W_823a8 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823ac : bv 32 := 0x06113423.
Lemma F_823ac : fetch_word Ubsan.M.loaded_segments (0x82404 : word) = Some W_823ac.
Proof. vm_refl. Qed.
Lemma D_823ac : decode_any W_823ac = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823b0 : bv 32 := 0x06813023.
Lemma F_823b0 : fetch_word Ubsan.M.loaded_segments (0x82408 : word) = Some W_823b0.
Proof. vm_refl. Qed.
Lemma D_823b0 : decode_any W_823b0 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823b4 : bv 32 := 0x04913c23.
Lemma F_823b4 : fetch_word Ubsan.M.loaded_segments (0x8240c : word) = Some W_823b4.
Proof. vm_refl. Qed.
Lemma D_823b4 : decode_any W_823b4 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823b8 : bv 32 := 0x05213823.
Lemma F_823b8 : fetch_word Ubsan.M.loaded_segments (0x82410 : word) = Some W_823b8.
Proof. vm_refl. Qed.
Lemma D_823b8 : decode_any W_823b8 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823bc : bv 32 := 0x05313423.
Lemma F_823bc : fetch_word Ubsan.M.loaded_segments (0x82414 : word) = Some W_823bc.
Proof. vm_refl. Qed.
Lemma D_823bc : decode_any W_823bc = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823c0 : bv 32 := 0x05413023.
Lemma F_823c0 : fetch_word Ubsan.M.loaded_segments (0x82418 : word) = Some W_823c0.
Proof. vm_refl. Qed.
Lemma D_823c0 : decode_any W_823c0 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823c4 : bv 32 := 0x03513c23.
Lemma F_823c4 : fetch_word Ubsan.M.loaded_segments (0x8241c : word) = Some W_823c4.
Proof. vm_refl. Qed.
Lemma D_823c4 : decode_any W_823c4 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823c8 : bv 32 := 0x03613823.
Lemma F_823c8 : fetch_word Ubsan.M.loaded_segments (0x82420 : word) = Some W_823c8.
Proof. vm_refl. Qed.
Lemma D_823c8 : decode_any W_823c8 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823cc : bv 32 := 0x03713423.
Lemma F_823cc : fetch_word Ubsan.M.loaded_segments (0x82424 : word) = Some W_823cc.
Proof. vm_refl. Qed.
Lemma D_823cc : decode_any W_823cc = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823d0 : bv 32 := 0x03813023.
Lemma F_823d0 : fetch_word Ubsan.M.loaded_segments (0x82428 : word) = Some W_823d0.
Proof. vm_refl. Qed.
Lemma D_823d0 : decode_any W_823d0 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823d4 : bv 32 := 0x01913c23.
Lemma F_823d4 : fetch_word Ubsan.M.loaded_segments (0x8242c : word) = Some W_823d4.
Proof. vm_refl. Qed.
Lemma D_823d4 : decode_any W_823d4 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823d8 : bv 32 := 0x00088a93.
Lemma F_823d8 : fetch_word Ubsan.M.loaded_segments (0x82430 : word) = Some W_823d8.
Proof. vm_refl. Qed.
Lemma D_823d8 : decode_any W_823d8 = Some (OpImm ALU_ADD 21 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823dc : bv 32 := 0x00080413.
Lemma F_823dc : fetch_word Ubsan.M.loaded_segments (0x82434 : word) = Some W_823dc.
Proof. vm_refl. Qed.
Lemma D_823dc : decode_any W_823dc = Some (OpImm ALU_ADD 8 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823e0 : bv 32 := 0x00078913.
Lemma F_823e0 : fetch_word Ubsan.M.loaded_segments (0x82438 : word) = Some W_823e0.
Proof. vm_refl. Qed.
Lemma D_823e0 : decode_any W_823e0 = Some (OpImm ALU_ADD 18 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823e4 : bv 32 := 0x00070993.
Lemma F_823e4 : fetch_word Ubsan.M.loaded_segments (0x8243c : word) = Some W_823e4.
Proof. vm_refl. Qed.
Lemma D_823e4 : decode_any W_823e4 = Some (OpImm ALU_ADD 19 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823e8 : bv 32 := 0x00068493.
Lemma F_823e8 : fetch_word Ubsan.M.loaded_segments (0x82440 : word) = Some W_823e8.
Proof. vm_refl. Qed.
Lemma D_823e8 : decode_any W_823e8 = Some (OpImm ALU_ADD 9 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823ec : bv 32 := 0x00060a13.
Lemma F_823ec : fetch_word Ubsan.M.loaded_segments (0x82444 : word) = Some W_823ec.
Proof. vm_refl. Qed.
Lemma D_823ec : decode_any W_823ec = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823f0 : bv 32 := 0x00058b13.
Lemma F_823f0 : fetch_word Ubsan.M.loaded_segments (0x82448 : word) = Some W_823f0.
Proof. vm_refl. Qed.
Lemma D_823f0 : decode_any W_823f0 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823f4 : bv 32 := 0x00050b93.
Lemma F_823f4 : fetch_word Ubsan.M.loaded_segments (0x8244c : word) = Some W_823f4.
Proof. vm_refl. Qed.
Lemma D_823f4 : decode_any W_823f4 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823f8 : bv 32 := 0x00070863.
Lemma F_823f8 : fetch_word Ubsan.M.loaded_segments (0x82450 : word) = Some W_823f8.
Proof. vm_refl. Qed.
Lemma D_823f8 : decode_any W_823f8 = Some (Branch BC_EQ 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_823fc : bv 32 := 0x0039f513.
Lemma F_823fc : fetch_word Ubsan.M.loaded_segments (0x82454 : word) = Some W_823fc.
Proof. vm_refl. Qed.
Lemma D_823fc : decode_any W_823fc = Some (OpImm ALU_AND 10 19 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82400 : bv 32 := 0x30051663.
Lemma F_82400 : fetch_word Ubsan.M.loaded_segments (0x82458 : word) = Some W_82400.
Proof. vm_refl. Qed.
Lemma D_82400 : decode_any W_82400 = Some (Branch BC_NE 10 0 780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82404 : bv 32 := 0x0009a023.
Lemma F_82404 : fetch_word Ubsan.M.loaded_segments (0x8245c : word) = Some W_82404.
Proof. vm_refl. Qed.
Lemma D_82404 : decode_any W_82404 = Some (Store SZ4 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82408 : bv 32 := 0x00090863.
Lemma F_82408 : fetch_word Ubsan.M.loaded_segments (0x82460 : word) = Some W_82408.
Proof. vm_refl. Qed.
Lemma D_82408 : decode_any W_82408 = Some (Branch BC_EQ 18 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8240c : bv 32 := 0x00397513.
Lemma F_8240c : fetch_word Ubsan.M.loaded_segments (0x82464 : word) = Some W_8240c.
Proof. vm_refl. Qed.
Lemma D_8240c : decode_any W_8240c = Some (OpImm ALU_AND 10 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82410 : bv 32 := 0x2e051e63.
Lemma F_82410 : fetch_word Ubsan.M.loaded_segments (0x82468 : word) = Some W_82410.
Proof. vm_refl. Qed.
Lemma D_82410 : decode_any W_82410 = Some (Branch BC_NE 10 0 764, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82414 : bv 32 := 0x00092023.
Lemma F_82414 : fetch_word Ubsan.M.loaded_segments (0x8246c : word) = Some W_82414.
Proof. vm_refl. Qed.
Lemma D_82414 : decode_any W_82414 = Some (Store SZ4 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82418 : bv 32 := 0x08040263.
Lemma F_82418 : fetch_word Ubsan.M.loaded_segments (0x82470 : word) = Some W_82418.
Proof. vm_refl. Qed.
Lemma D_82418 : decode_any W_82418 = Some (Branch BC_EQ 8 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8241c : bv 32 := 0x00347513.
Lemma F_8241c : fetch_word Ubsan.M.loaded_segments (0x82474 : word) = Some W_8241c.
Proof. vm_refl. Qed.
Lemma D_8241c : decode_any W_8241c = Some (OpImm ALU_AND 10 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82420 : bv 32 := 0x2e051663.
Lemma F_82420 : fetch_word Ubsan.M.loaded_segments (0x82478 : word) = Some W_82420.
Proof. vm_refl. Qed.
Lemma D_82420 : decode_any W_82420 = Some (Branch BC_NE 10 0 748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82424 : bv 32 := 0x0129e533.
Lemma F_82424 : fetch_word Ubsan.M.loaded_segments (0x8247c : word) = Some W_82424.
Proof. vm_refl. Qed.
Lemma D_82424 : decode_any W_82424 = Some (Op ALU_OR 10 19 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82428 : bv 32 := 0x00042023.
Lemma F_82428 : fetch_word Ubsan.M.loaded_segments (0x82480 : word) = Some W_82428.
Proof. vm_refl. Qed.
Lemma D_82428 : decode_any W_82428 = Some (Store SZ4 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8242c : bv 32 := 0x00a03c33.
Lemma F_8242c : fetch_word Ubsan.M.loaded_segments (0x82484 : word) = Some W_8242c.
Proof. vm_refl. Qed.
Lemma D_8242c : decode_any W_8242c = Some (Op ALU_SLTU 24 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82430 : bv 32 := 0x040b8263.
Lemma F_82430 : fetch_word Ubsan.M.loaded_segments (0x82488 : word) = Some W_82430.
Proof. vm_refl. Qed.
Lemma D_82430 : decode_any W_82430 = Some (Branch BC_EQ 23 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82434 : bv 32 := 0x000b8513.
Lemma F_82434 : fetch_word Ubsan.M.loaded_segments (0x8248c : word) = Some W_82434.
Proof. vm_refl. Qed.
Lemma D_82434 : decode_any W_82434 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82438 : bv 32 := 0x9a4e20ef.
Lemma F_82438 : fetch_word Ubsan.M.loaded_segments (0x82490 : word) = Some W_82438.
Proof. vm_refl. Qed.
Lemma D_82438 : decode_any W_82438 = Some (Jal 1 1974692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8243c : bv 32 := 0x00100593.
Lemma F_8243c : fetch_word Ubsan.M.loaded_segments (0x82494 : word) = Some W_8243c.
Proof. vm_refl. Qed.
Lemma D_8243c : decode_any W_8243c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82440 : bv 32 := 0x02b51a63.
Lemma F_82440 : fetch_word Ubsan.M.loaded_segments (0x82498 : word) = Some W_82440.
Proof. vm_refl. Qed.
Lemma D_82440 : decode_any W_82440 = Some (Branch BC_NE 10 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82444 : bv 32 := 0x00400513.
Lemma F_82444 : fetch_word Ubsan.M.loaded_segments (0x8249c : word) = Some W_82444.
Proof. vm_refl. Qed.
Lemma D_82444 : decode_any W_82444 = Some (OpImm ALU_ADD 10 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82448 : bv 32 := 0x08ab6663.
Lemma F_82448 : fetch_word Ubsan.M.loaded_segments (0x824a0 : word) = Some W_82448.
Proof. vm_refl. Qed.
Lemma D_82448 : decode_any W_82448 = Some (Branch BC_LTU 22 10 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82474 : bv 32 := 0x00077517.
Lemma F_82474 : fetch_word Ubsan.M.loaded_segments (0x824cc : word) = Some W_82474.
Proof. vm_refl. Qed.
Lemma D_82474 : decode_any W_82474 = Some (Auipc 10 119, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82478 : bv 32 := 0xc5453503.
Lemma F_82478 : fetch_word Ubsan.M.loaded_segments (0x824d0 : word) = Some W_82478.
Proof. vm_refl. Qed.
Lemma D_82478 : decode_any W_82478 = Some (Load SZ8 true 10 10 3156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8247c : bv 32 := 0x00052503.
Lemma F_8247c : fetch_word Ubsan.M.loaded_segments (0x824d4 : word) = Some W_8247c.
Proof. vm_refl. Qed.
Lemma D_8247c : decode_any W_8247c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82480 : bv 32 := 0x00500593.
Lemma F_82480 : fetch_word Ubsan.M.loaded_segments (0x824d8 : word) = Some W_82480.
Proof. vm_refl. Qed.
Lemma D_82480 : decode_any W_82480 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82484 : bv 32 := 0x1aa5cc63.
Lemma F_82484 : fetch_word Ubsan.M.loaded_segments (0x824dc : word) = Some W_82484.
Proof. vm_refl. Qed.
Lemma D_82484 : decode_any W_82484 = Some (Branch BC_LT 11 10 440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82488 : bv 32 := 0xfff8f517.
Lemma F_82488 : fetch_word Ubsan.M.loaded_segments (0x824e0 : word) = Some W_82488.
Proof. vm_refl. Qed.
Lemma D_82488 : decode_any W_82488 = Some (Auipc 10 1048463, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8248c : bv 32 := 0xfff93597.
Lemma F_8248c : fetch_word Ubsan.M.loaded_segments (0x824e4 : word) = Some W_8248c.
Proof. vm_refl. Qed.
Lemma D_8248c : decode_any W_8248c = Some (Auipc 11 1048467, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82490 : bv 32 := 0x0f750513.
Lemma F_82490 : fetch_word Ubsan.M.loaded_segments (0x824e8 : word) = Some W_82490.
Proof. vm_refl. Qed.
Lemma D_82490 : decode_any W_82490 = Some (OpImm ALU_ADD 10 10 247, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82494 : bv 32 := 0xe0958593.
Lemma F_82494 : fetch_word Ubsan.M.loaded_segments (0x824ec : word) = Some W_82494.
Proof. vm_refl. Qed.
Lemma D_82494 : decode_any W_82494 = Some (OpImm ALU_ADD 11 11 3593, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82498 : bv 32 := 0x16c0006f.
Lemma F_82498 : fetch_word Ubsan.M.loaded_segments (0x824f0 : word) = Some W_82498.
Proof. vm_refl. Qed.
Lemma D_82498 : decode_any W_82498 = Some (Jal 0 364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824d4 : bv 32 := 0x0b405e63.
Lemma F_824d4 : fetch_word Ubsan.M.loaded_segments (0x8252c : word) = Some W_824d4.
Proof. vm_refl. Qed.
Lemma D_824d4 : decode_any W_824d4 = Some (Branch BC_GE 0 20 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824d8 : bv 32 := 0x0e905063.
Lemma F_824d8 : fetch_word Ubsan.M.loaded_segments (0x82530 : word) = Some W_824d8.
Proof. vm_refl. Qed.
Lemma D_824d8 : decode_any W_824d8 = Some (Branch BC_GE 0 9 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824dc : bv 32 := 0x000b8513.
Lemma F_824dc : fetch_word Ubsan.M.loaded_segments (0x82534 : word) = Some W_824dc.
Proof. vm_refl. Qed.
Lemma D_824dc : decode_any W_824dc = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824e0 : bv 32 := 0x000b0593.
Lemma F_824e0 : fetch_word Ubsan.M.loaded_segments (0x82538 : word) = Some W_824e0.
Proof. vm_refl. Qed.
Lemma D_824e0 : decode_any W_824e0 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824e4 : bv 32 := 0x000a8613.
Lemma F_824e4 : fetch_word Ubsan.M.loaded_segments (0x8253c : word) = Some W_824e4.
Proof. vm_refl. Qed.
Lemma D_824e4 : decode_any W_824e4 = Some (OpImm ALU_ADD 12 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824e8 : bv 32 := 0x228000ef.
Lemma F_824e8 : fetch_word Ubsan.M.loaded_segments (0x82540 : word) = Some W_824e8.
Proof. vm_refl. Qed.
Lemma D_824e8 : decode_any W_824e8 = Some (Jal 1 552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824ec : bv 32 := 0x00a13423.
Lemma F_824ec : fetch_word Ubsan.M.loaded_segments (0x82544 : word) = Some W_824ec.
Proof. vm_refl. Qed.
Lemma D_824ec : decode_any W_824ec = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824f0 : bv 32 := 0x0e050863.
Lemma F_824f0 : fetch_word Ubsan.M.loaded_segments (0x82548 : word) = Some W_824f0.
Proof. vm_refl. Qed.
Lemma D_824f0 : decode_any W_824f0 = Some (Branch BC_EQ 10 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824f4 : bv 32 := 0x00050b13.
Lemma F_824f4 : fetch_word Ubsan.M.loaded_segments (0x8254c : word) = Some W_824f4.
Proof. vm_refl. Qed.
Lemma D_824f4 : decode_any W_824f4 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824f8 : bv 32 := 0xc20df0ef.
Lemma F_824f8 : fetch_word Ubsan.M.loaded_segments (0x82550 : word) = Some W_824f8.
Proof. vm_refl. Qed.
Lemma D_824f8 : decode_any W_824f8 = Some (Jal 1 1963040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_824fc : bv 32 := 0x00100593.
Lemma F_824fc : fetch_word Ubsan.M.loaded_segments (0x82554 : word) = Some W_824fc.
Proof. vm_refl. Qed.
Lemma D_824fc : decode_any W_824fc = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82500 : bv 32 := 0x1ea5de63.
Lemma F_82500 : fetch_word Ubsan.M.loaded_segments (0x82558 : word) = Some W_82500.
Proof. vm_refl. Qed.
Lemma D_82500 : decode_any W_82500 = Some (Branch BC_GE 11 10 508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82504 : bv 32 := 0x00050a93.
Lemma F_82504 : fetch_word Ubsan.M.loaded_segments (0x8255c : word) = Some W_82504.
Proof. vm_refl. Qed.
Lemma D_82504 : decode_any W_82504 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82508 : bv 32 := 0x1a0c0663.
Lemma F_82508 : fetch_word Ubsan.M.loaded_segments (0x82560 : word) = Some W_82508.
Proof. vm_refl. Qed.
Lemma D_82508 : decode_any W_82508 = Some (Branch BC_EQ 24 0 428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8250c : bv 32 := 0x01410613.
Lemma F_8250c : fetch_word Ubsan.M.loaded_segments (0x82564 : word) = Some W_8250c.
Proof. vm_refl. Qed.
Lemma D_8250c : decode_any W_8250c = Some (OpImm ALU_ADD 12 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82510 : bv 32 := 0x000b0513.
Lemma F_82510 : fetch_word Ubsan.M.loaded_segments (0x82568 : word) = Some W_82510.
Proof. vm_refl. Qed.
Lemma D_82510 : decode_any W_82510 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82514 : bv 32 := 0x00000593.
Lemma F_82514 : fetch_word Ubsan.M.loaded_segments (0x8256c : word) = Some W_82514.
Proof. vm_refl. Qed.
Lemma D_82514 : decode_any W_82514 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82518 : bv 32 := 0xe50df0ef.
Lemma F_82518 : fetch_word Ubsan.M.loaded_segments (0x82570 : word) = Some W_82518.
Proof. vm_refl. Qed.
Lemma D_82518 : decode_any W_82518 = Some (Jal 1 1963600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8251c : bv 32 := 0x00000b93.
Lemma F_8251c : fetch_word Ubsan.M.loaded_segments (0x82574 : word) = Some W_8251c.
Proof. vm_refl. Qed.
Lemma D_8251c : decode_any W_8251c = Some (OpImm ALU_ADD 23 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82520 : bv 32 := 0x00000c13.
Lemma F_82520 : fetch_word Ubsan.M.loaded_segments (0x82578 : word) = Some W_82520.
Proof. vm_refl. Qed.
Lemma D_82520 : decode_any W_82520 = Some (OpImm ALU_ADD 24 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82524 : bv 32 := 0x00100b13.
Lemma F_82524 : fetch_word Ubsan.M.loaded_segments (0x8257c : word) = Some W_82524.
Proof. vm_refl. Qed.
Lemma D_82524 : decode_any W_82524 = Some (OpImm ALU_ADD 22 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82528 : bv 32 := 0x80000cb7.
Lemma F_82528 : fetch_word Ubsan.M.loaded_segments (0x82580 : word) = Some W_82528.
Proof. vm_refl. Qed.
Lemma D_82528 : decode_any W_82528 = Some (Lui 25 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8252c : bv 32 := 0x0100006f.
Lemma F_8252c : fetch_word Ubsan.M.loaded_segments (0x82584 : word) = Some W_8252c.
Proof. vm_refl. Qed.
Lemma D_8252c : decode_any W_8252c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82530 : bv 32 := 0x001b0b1b.
Lemma F_82530 : fetch_word Ubsan.M.loaded_segments (0x82588 : word) = Some W_82530.
Proof. vm_refl. Qed.
Lemma D_82530 : decode_any W_82530 = Some (OpImm32 22 22 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82534 : bv 32 := 0x00a12a23.
Lemma F_82534 : fetch_word Ubsan.M.loaded_segments (0x8258c : word) = Some W_82534.
Proof. vm_refl. Qed.
Lemma D_82534 : decode_any W_82534 = Some (Store SZ4 2 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82538 : bv 32 := 0x136a8e63.
Lemma F_82538 : fetch_word Ubsan.M.loaded_segments (0x82590 : word) = Some W_82538.
Proof. vm_refl. Qed.
Lemma D_82538 : decode_any W_82538 = Some (Branch BC_EQ 21 22 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8253c : bv 32 := 0x00813503.
Lemma F_8253c : fetch_word Ubsan.M.loaded_segments (0x82594 : word) = Some W_8253c.
Proof. vm_refl. Qed.
Lemma D_8253c : decode_any W_8253c = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82540 : bv 32 := 0x01010613.
Lemma F_82540 : fetch_word Ubsan.M.loaded_segments (0x82598 : word) = Some W_82540.
Proof. vm_refl. Qed.
Lemma D_82540 : decode_any W_82540 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82544 : bv 32 := 0x000b0593.
Lemma F_82544 : fetch_word Ubsan.M.loaded_segments (0x8259c : word) = Some W_82544.
Proof. vm_refl. Qed.
Lemma D_82544 : decode_any W_82544 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82548 : bv 32 := 0xe20df0ef.
Lemma F_82548 : fetch_word Ubsan.M.loaded_segments (0x825a0 : word) = Some W_82548.
Proof. vm_refl. Qed.
Lemma D_82548 : decode_any W_82548 = Some (Jal 1 1963552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8254c : bv 32 := 0x01012503.
Lemma F_8254c : fetch_word Ubsan.M.loaded_segments (0x825a4 : word) = Some W_8254c.
Proof. vm_refl. Qed.
Lemma D_8254c : decode_any W_8254c = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82550 : bv 32 := 0x01412603.
Lemma F_82550 : fetch_word Ubsan.M.loaded_segments (0x825a8 : word) = Some W_82550.
Proof. vm_refl. Qed.
Lemma D_82550 : decode_any W_82550 = Some (Load SZ4 true 12 2 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82554 : bv 32 := 0x40c505bb.
Lemma F_82554 : fetch_word Ubsan.M.loaded_segments (0x825ac : word) = Some W_82554.
Proof. vm_refl. Qed.
Lemma D_82554 : decode_any W_82554 = Some (Op32 ALU_SUB 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82558 : bv 32 := 0x40c50633.
Lemma F_82558 : fetch_word Ubsan.M.loaded_segments (0x825b0 : word) = Some W_82558.
Proof. vm_refl. Qed.
Lemma D_82558 : decode_any W_82558 = Some (Op ALU_SUB 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8255c : bv 32 := 0x1ac59863.
Lemma F_8255c : fetch_word Ubsan.M.loaded_segments (0x825b4 : word) = Some W_8255c.
Proof. vm_refl. Qed.
Lemma D_8255c : decode_any W_8255c = Some (Branch BC_NE 11 12 432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82560 : bv 32 := 0x0005d663.
Lemma F_82560 : fetch_word Ubsan.M.loaded_segments (0x825b8 : word) = Some W_82560.
Proof. vm_refl. Qed.
Lemma D_82560 : decode_any W_82560 = Some (Branch BC_GE 11 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82564 : bv 32 := 0x1b958463.
Lemma F_82564 : fetch_word Ubsan.M.loaded_segments (0x825bc : word) = Some W_82564.
Proof. vm_refl. Qed.
Lemma D_82564 : decode_any W_82564 = Some (Branch BC_EQ 11 25 424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82568 : bv 32 := 0x40b005bb.
Lemma F_82568 : fetch_word Ubsan.M.loaded_segments (0x825c0 : word) = Some W_82568.
Proof. vm_refl. Qed.
Lemma D_82568 : decode_any W_82568 = Some (Op32 ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8256c : bv 32 := 0xfd45c2e3.
Lemma F_8256c : fetch_word Ubsan.M.loaded_segments (0x825c4 : word) = Some W_8256c.
Proof. vm_refl. Qed.
Lemma D_8256c : decode_any W_8256c = Some (Branch BC_LT 11 20 8132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82570 : bv 32 := 0x001c061b.
Lemma F_82570 : fetch_word Ubsan.M.loaded_segments (0x825c8 : word) = Some W_82570.
Proof. vm_refl. Qed.
Lemma D_82570 : decode_any W_82570 = Some (OpImm32 12 24 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82574 : bv 32 := 0x19864c63.
Lemma F_82574 : fetch_word Ubsan.M.loaded_segments (0x825cc : word) = Some W_82574.
Proof. vm_refl. Qed.
Lemma D_82574 : decode_any W_82574 = Some (Branch BC_LT 12 24 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82578 : bv 32 := 0x000b869b.
Lemma F_82578 : fetch_word Ubsan.M.loaded_segments (0x825d0 : word) = Some W_82578.
Proof. vm_refl. Qed.
Lemma D_82578 : decode_any W_82578 = Some (OpImm32 13 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8257c : bv 32 := 0x00b68bb3.
Lemma F_8257c : fetch_word Ubsan.M.loaded_segments (0x825d4 : word) = Some W_8257c.
Proof. vm_refl. Qed.
Lemma D_8257c : decode_any W_8257c = Some (Op ALU_ADD 23 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82580 : bv 32 := 0x00b685bb.
Lemma F_82580 : fetch_word Ubsan.M.loaded_segments (0x825d8 : word) = Some W_82580.
Proof. vm_refl. Qed.
Lemma D_82580 : decode_any W_82580 = Some (Op32 ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82584 : bv 32 := 0x19759463.
Lemma F_82584 : fetch_word Ubsan.M.loaded_segments (0x825dc : word) = Some W_82584.
Proof. vm_refl. Qed.
Lemma D_82584 : decode_any W_82584 = Some (Branch BC_NE 11 23 392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82588 : bv 32 := 0x00060c13.
Lemma F_82588 : fetch_word Ubsan.M.loaded_segments (0x825e0 : word) = Some W_82588.
Proof. vm_refl. Qed.
Lemma D_82588 : decode_any W_82588 = Some (OpImm ALU_ADD 24 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8258c : bv 32 := 0xfa5ff06f.
Lemma F_8258c : fetch_word Ubsan.M.loaded_segments (0x825e4 : word) = Some W_8258c.
Proof. vm_refl. Qed.
Lemma D_8258c : decode_any W_8258c = Some (Jal 0 2097060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82604 : bv 32 := 0x00100613.
Lemma F_82604 : fetch_word Ubsan.M.loaded_segments (0x8265c : word) = Some W_82604.
Proof. vm_refl. Qed.
Lemma D_82604 : decode_any W_82604 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82608 : bv 32 := 0x06813083.
Lemma F_82608 : fetch_word Ubsan.M.loaded_segments (0x82660 : word) = Some W_82608.
Proof. vm_refl. Qed.
Lemma D_82608 : decode_any W_82608 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8260c : bv 32 := 0x06013403.
Lemma F_8260c : fetch_word Ubsan.M.loaded_segments (0x82664 : word) = Some W_8260c.
Proof. vm_refl. Qed.
Lemma D_8260c : decode_any W_8260c = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82610 : bv 32 := 0x05813483.
Lemma F_82610 : fetch_word Ubsan.M.loaded_segments (0x82668 : word) = Some W_82610.
Proof. vm_refl. Qed.
Lemma D_82610 : decode_any W_82610 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82614 : bv 32 := 0x05013903.
Lemma F_82614 : fetch_word Ubsan.M.loaded_segments (0x8266c : word) = Some W_82614.
Proof. vm_refl. Qed.
Lemma D_82614 : decode_any W_82614 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82618 : bv 32 := 0x04813983.
Lemma F_82618 : fetch_word Ubsan.M.loaded_segments (0x82670 : word) = Some W_82618.
Proof. vm_refl. Qed.
Lemma D_82618 : decode_any W_82618 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8261c : bv 32 := 0x04013a03.
Lemma F_8261c : fetch_word Ubsan.M.loaded_segments (0x82674 : word) = Some W_8261c.
Proof. vm_refl. Qed.
Lemma D_8261c : decode_any W_8261c = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82620 : bv 32 := 0x03813a83.
Lemma F_82620 : fetch_word Ubsan.M.loaded_segments (0x82678 : word) = Some W_82620.
Proof. vm_refl. Qed.
Lemma D_82620 : decode_any W_82620 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82624 : bv 32 := 0x03013b03.
Lemma F_82624 : fetch_word Ubsan.M.loaded_segments (0x8267c : word) = Some W_82624.
Proof. vm_refl. Qed.
Lemma D_82624 : decode_any W_82624 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82628 : bv 32 := 0x02813b83.
Lemma F_82628 : fetch_word Ubsan.M.loaded_segments (0x82680 : word) = Some W_82628.
Proof. vm_refl. Qed.
Lemma D_82628 : decode_any W_82628 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8262c : bv 32 := 0x02013c03.
Lemma F_8262c : fetch_word Ubsan.M.loaded_segments (0x82684 : word) = Some W_8262c.
Proof. vm_refl. Qed.
Lemma D_8262c : decode_any W_8262c = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82630 : bv 32 := 0x01813c83.
Lemma F_82630 : fetch_word Ubsan.M.loaded_segments (0x82688 : word) = Some W_82630.
Proof. vm_refl. Qed.
Lemma D_82630 : decode_any W_82630 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82634 : bv 32 := 0x07010113.
Lemma F_82634 : fetch_word Ubsan.M.loaded_segments (0x8268c : word) = Some W_82634.
Proof. vm_refl. Qed.
Lemma D_82634 : decode_any W_82634 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82638 : bv 32 := 0xb35da06f.
Lemma F_82638 : fetch_word Ubsan.M.loaded_segments (0x82690 : word) = Some W_82638.
Proof. vm_refl. Qed.
Lemma D_82638 : decode_any W_82638 = Some (Jal 0 1944372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82640 : bv 32 := 0x06813083.
Lemma F_82640 : fetch_word Ubsan.M.loaded_segments (0x82698 : word) = Some W_82640.
Proof. vm_refl. Qed.
Lemma D_82640 : decode_any W_82640 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82644 : bv 32 := 0x06013403.
Lemma F_82644 : fetch_word Ubsan.M.loaded_segments (0x8269c : word) = Some W_82644.
Proof. vm_refl. Qed.
Lemma D_82644 : decode_any W_82644 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82648 : bv 32 := 0x05813483.
Lemma F_82648 : fetch_word Ubsan.M.loaded_segments (0x826a0 : word) = Some W_82648.
Proof. vm_refl. Qed.
Lemma D_82648 : decode_any W_82648 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8264c : bv 32 := 0x05013903.
Lemma F_8264c : fetch_word Ubsan.M.loaded_segments (0x826a4 : word) = Some W_8264c.
Proof. vm_refl. Qed.
Lemma D_8264c : decode_any W_8264c = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82650 : bv 32 := 0x04813983.
Lemma F_82650 : fetch_word Ubsan.M.loaded_segments (0x826a8 : word) = Some W_82650.
Proof. vm_refl. Qed.
Lemma D_82650 : decode_any W_82650 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82654 : bv 32 := 0x04013a03.
Lemma F_82654 : fetch_word Ubsan.M.loaded_segments (0x826ac : word) = Some W_82654.
Proof. vm_refl. Qed.
Lemma D_82654 : decode_any W_82654 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82658 : bv 32 := 0x03813a83.
Lemma F_82658 : fetch_word Ubsan.M.loaded_segments (0x826b0 : word) = Some W_82658.
Proof. vm_refl. Qed.
Lemma D_82658 : decode_any W_82658 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8265c : bv 32 := 0x03013b03.
Lemma F_8265c : fetch_word Ubsan.M.loaded_segments (0x826b4 : word) = Some W_8265c.
Proof. vm_refl. Qed.
Lemma D_8265c : decode_any W_8265c = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82660 : bv 32 := 0x02813b83.
Lemma F_82660 : fetch_word Ubsan.M.loaded_segments (0x826b8 : word) = Some W_82660.
Proof. vm_refl. Qed.
Lemma D_82660 : decode_any W_82660 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82664 : bv 32 := 0x02013c03.
Lemma F_82664 : fetch_word Ubsan.M.loaded_segments (0x826bc : word) = Some W_82664.
Proof. vm_refl. Qed.
Lemma D_82664 : decode_any W_82664 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82668 : bv 32 := 0x01813c83.
Lemma F_82668 : fetch_word Ubsan.M.loaded_segments (0x826c0 : word) = Some W_82668.
Proof. vm_refl. Qed.
Lemma D_82668 : decode_any W_82668 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8266c : bv 32 := 0x07010113.
Lemma F_8266c : fetch_word Ubsan.M.loaded_segments (0x826c4 : word) = Some W_8266c.
Proof. vm_refl. Qed.
Lemma D_8266c : decode_any W_8266c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82670 : bv 32 := 0x00008067.
Lemma F_82670 : fetch_word Ubsan.M.loaded_segments (0x826c8 : word) = Some W_82670.
Proof. vm_refl. Qed.
Lemma D_82670 : decode_any W_82670 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82674 : bv 32 := 0x02098063.
Lemma F_82674 : fetch_word Ubsan.M.loaded_segments (0x826cc : word) = Some W_82674.
Proof. vm_refl. Qed.
Lemma D_82674 : decode_any W_82674 = Some (Branch BC_EQ 19 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82678 : bv 32 := 0x0039f513.
Lemma F_82678 : fetch_word Ubsan.M.loaded_segments (0x826d0 : word) = Some W_82678.
Proof. vm_refl. Qed.
Lemma D_82678 : decode_any W_82678 = Some (OpImm ALU_AND 10 19 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8267c : bv 32 := 0x08051863.
Lemma F_8267c : fetch_word Ubsan.M.loaded_segments (0x826d4 : word) = Some W_8267c.
Proof. vm_refl. Qed.
Lemma D_8267c : decode_any W_8267c = Some (Branch BC_NE 10 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82680 : bv 32 := 0xd00c77d3.
Lemma F_82680 : fetch_word Ubsan.M.loaded_segments (0x826d8 : word) = Some W_82680.
Proof. vm_refl. Qed.
Lemma D_82680 : decode_any W_82680 = Some (Fcvt FC_S FC_W 15 24 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82684 : bv 32 := 0xfffa8513.
Lemma F_82684 : fetch_word Ubsan.M.loaded_segments (0x826dc : word) = Some W_82684.
Proof. vm_refl. Qed.
Lemma D_82684 : decode_any W_82684 = Some (OpImm ALU_ADD 10 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82688 : bv 32 := 0xd0157753.
Lemma F_82688 : fetch_word Ubsan.M.loaded_segments (0x826e0 : word) = Some W_82688.
Proof. vm_refl. Qed.
Lemma D_82688 : decode_any W_82688 = Some (Fcvt FC_S FC_WU 14 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8268c : bv 32 := 0x18e7f7d3.
Lemma F_8268c : fetch_word Ubsan.M.loaded_segments (0x826e4 : word) = Some W_8268c.
Proof. vm_refl. Qed.
Lemma D_8268c : decode_any W_8268c = Some (Fari F_DIV FMT_S 15 15 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82690 : bv 32 := 0x00f9a027.
Lemma F_82690 : fetch_word Ubsan.M.loaded_segments (0x826e8 : word) = Some W_82690.
Proof. vm_refl. Qed.
Lemma D_82690 : decode_any W_82690 = Some (FStore FMT_S 19 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82694 : bv 32 := 0x02090063.
Lemma F_82694 : fetch_word Ubsan.M.loaded_segments (0x826ec : word) = Some W_82694.
Proof. vm_refl. Qed.
Lemma D_82694 : decode_any W_82694 = Some (Branch BC_EQ 18 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82698 : bv 32 := 0x00397513.
Lemma F_82698 : fetch_word Ubsan.M.loaded_segments (0x826f0 : word) = Some W_82698.
Proof. vm_refl. Qed.
Lemma D_82698 : decode_any W_82698 = Some (OpImm ALU_AND 10 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8269c : bv 32 := 0x06051863.
Lemma F_8269c : fetch_word Ubsan.M.loaded_segments (0x826f4 : word) = Some W_8269c.
Proof. vm_refl. Qed.
Lemma D_8269c : decode_any W_8269c = Some (Branch BC_NE 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826a0 : bv 32 := 0xd00bf7d3.
Lemma F_826a0 : fetch_word Ubsan.M.loaded_segments (0x826f8 : word) = Some W_826a0.
Proof. vm_refl. Qed.
Lemma D_826a0 : decode_any W_826a0 = Some (Fcvt FC_S FC_W 15 23 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826a4 : bv 32 := 0xfffa8513.
Lemma F_826a4 : fetch_word Ubsan.M.loaded_segments (0x826fc : word) = Some W_826a4.
Proof. vm_refl. Qed.
Lemma D_826a4 : decode_any W_826a4 = Some (OpImm ALU_ADD 10 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826a8 : bv 32 := 0xd0157753.
Lemma F_826a8 : fetch_word Ubsan.M.loaded_segments (0x82700 : word) = Some W_826a8.
Proof. vm_refl. Qed.
Lemma D_826a8 : decode_any W_826a8 = Some (Fcvt FC_S FC_WU 14 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826ac : bv 32 := 0x18e7f7d3.
Lemma F_826ac : fetch_word Ubsan.M.loaded_segments (0x82704 : word) = Some W_826ac.
Proof. vm_refl. Qed.
Lemma D_826ac : decode_any W_826ac = Some (Fari F_DIV FMT_S 15 15 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826b0 : bv 32 := 0x00f92027.
Lemma F_826b0 : fetch_word Ubsan.M.loaded_segments (0x82708 : word) = Some W_826b0.
Proof. vm_refl. Qed.
Lemma D_826b0 : decode_any W_826b0 = Some (FStore FMT_S 18 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826b4 : bv 32 := 0x04040463.
Lemma F_826b4 : fetch_word Ubsan.M.loaded_segments (0x8270c : word) = Some W_826b4.
Proof. vm_refl. Qed.
Lemma D_826b4 : decode_any W_826b4 = Some (Branch BC_EQ 8 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826b8 : bv 32 := 0x00813503.
Lemma F_826b8 : fetch_word Ubsan.M.loaded_segments (0x82710 : word) = Some W_826b8.
Proof. vm_refl. Qed.
Lemma D_826b8 : decode_any W_826b8 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826bc : bv 32 := 0xd014f553.
Lemma F_826bc : fetch_word Ubsan.M.loaded_segments (0x82714 : word) = Some W_826bc.
Proof. vm_refl. Qed.
Lemma D_826bc : decode_any W_826bc = Some (Fcvt FC_S FC_WU 10 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826c0 : bv 32 := 0x00000593.
Lemma F_826c0 : fetch_word Ubsan.M.loaded_segments (0x82718 : word) = Some W_826c0.
Proof. vm_refl. Qed.
Lemma D_826c0 : decode_any W_826c0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826c4 : bv 32 := 0xca5de0ef.
Lemma F_826c4 : fetch_word Ubsan.M.loaded_segments (0x8271c : word) = Some W_826c4.
Proof. vm_refl. Qed.
Lemma D_826c4 : decode_any W_826c4 = Some (Jal 1 1961124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826c8 : bv 32 := 0x00a13023.
Lemma F_826c8 : fetch_word Ubsan.M.loaded_segments (0x82720 : word) = Some W_826c8.
Proof. vm_refl. Qed.
Lemma D_826c8 : decode_any W_826c8 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826cc : bv 32 := 0xa4cdf0ef.
Lemma F_826cc : fetch_word Ubsan.M.loaded_segments (0x82724 : word) = Some W_826cc.
Proof. vm_refl. Qed.
Lemma D_826cc : decode_any W_826cc = Some (Jal 1 1962572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826d0 : bv 32 := 0xfff5059b.
Lemma F_826d0 : fetch_word Ubsan.M.loaded_segments (0x82728 : word) = Some W_826d0.
Proof. vm_refl. Qed.
Lemma D_826d0 : decode_any W_826d0 = Some (OpImm32 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826d4 : bv 32 := 0x02a5dc63.
Lemma F_826d4 : fetch_word Ubsan.M.loaded_segments (0x8272c : word) = Some W_826d4.
Proof. vm_refl. Qed.
Lemma D_826d4 : decode_any W_826d4 = Some (Branch BC_GE 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826d8 : bv 32 := 0x00347513.
Lemma F_826d8 : fetch_word Ubsan.M.loaded_segments (0x82730 : word) = Some W_826d8.
Proof. vm_refl. Qed.
Lemma D_826d8 : decode_any W_826d8 = Some (OpImm ALU_AND 10 8 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826dc : bv 32 := 0x02051863.
Lemma F_826dc : fetch_word Ubsan.M.loaded_segments (0x82734 : word) = Some W_826dc.
Proof. vm_refl. Qed.
Lemma D_826dc : decode_any W_826dc = Some (Branch BC_NE 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826e0 : bv 32 := 0xd005f7d3.
Lemma F_826e0 : fetch_word Ubsan.M.loaded_segments (0x82738 : word) = Some W_826e0.
Proof. vm_refl. Qed.
Lemma D_826e0 : decode_any W_826e0 = Some (Fcvt FC_S FC_W 15 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826e4 : bv 32 := 0xfffa8a93.
Lemma F_826e4 : fetch_word Ubsan.M.loaded_segments (0x8273c : word) = Some W_826e4.
Proof. vm_refl. Qed.
Lemma D_826e4 : decode_any W_826e4 = Some (OpImm ALU_ADD 21 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826e8 : bv 32 := 0xd01af753.
Lemma F_826e8 : fetch_word Ubsan.M.loaded_segments (0x82740 : word) = Some W_826e8.
Proof. vm_refl. Qed.
Lemma D_826e8 : decode_any W_826e8 = Some (Fcvt FC_S FC_WU 14 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826ec : bv 32 := 0x18e7f7d3.
Lemma F_826ec : fetch_word Ubsan.M.loaded_segments (0x82744 : word) = Some W_826ec.
Proof. vm_refl. Qed.
Lemma D_826ec : decode_any W_826ec = Some (Fari F_DIV FMT_S 15 15 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826f0 : bv 32 := 0x00f42027.
Lemma F_826f0 : fetch_word Ubsan.M.loaded_segments (0x82748 : word) = Some W_826f0.
Proof. vm_refl. Qed.
Lemma D_826f0 : decode_any W_826f0 = Some (FStore FMT_S 8 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826f4 : bv 32 := 0x00010513.
Lemma F_826f4 : fetch_word Ubsan.M.loaded_segments (0x8274c : word) = Some W_826f4.
Proof. vm_refl. Qed.
Lemma D_826f4 : decode_any W_826f4 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826f8 : bv 32 := 0x844df0ef.
Lemma F_826f8 : fetch_word Ubsan.M.loaded_segments (0x82750 : word) = Some W_826f8.
Proof. vm_refl. Qed.
Lemma D_826f8 : decode_any W_826f8 = Some (Jal 1 1962052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_826fc : bv 32 := 0x00810513.
Lemma F_826fc : fetch_word Ubsan.M.loaded_segments (0x82754 : word) = Some W_826fc.
Proof. vm_refl. Qed.
Lemma D_826fc : decode_any W_826fc = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82700 : bv 32 := 0x83cdf0ef.
Lemma F_82700 : fetch_word Ubsan.M.loaded_segments (0x82758 : word) = Some W_82700.
Proof. vm_refl. Qed.
Lemma D_82700 : decode_any W_82700 = Some (Jal 1 1962044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82704 : bv 32 := 0x00000513.
Lemma F_82704 : fetch_word Ubsan.M.loaded_segments (0x8275c : word) = Some W_82704.
Proof. vm_refl. Qed.
Lemma D_82704 : decode_any W_82704 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_82708 : bv 32 := 0xf39ff06f.
Lemma F_82708 : fetch_word Ubsan.M.loaded_segments (0x82760 : word) = Some W_82708.
Proof. vm_refl. Qed.
Lemma D_82708 : decode_any W_82708 = Some (Jal 0 2096952, 4%Z).
Proof. vm_refl. Qed.

