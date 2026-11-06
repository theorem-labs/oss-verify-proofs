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
Definition Wx_67f3c : bv 32 := 0xfa010113.
Lemma Fx_67f3c : fetch_word Asan.M.loaded_segments (0x67f8c : word) = Some Wx_67f3c.
Proof. vm_refl. Qed.
Lemma Dx_67f3c : decode_any Wx_67f3c = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f40 : bv 32 := 0x04113c23.
Lemma Fx_67f40 : fetch_word Asan.M.loaded_segments (0x67f90 : word) = Some Wx_67f40.
Proof. vm_refl. Qed.
Lemma Dx_67f40 : decode_any Wx_67f40 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f44 : bv 32 := 0x04813823.
Lemma Fx_67f44 : fetch_word Asan.M.loaded_segments (0x67f94 : word) = Some Wx_67f44.
Proof. vm_refl. Qed.
Lemma Dx_67f44 : decode_any Wx_67f44 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f48 : bv 32 := 0x04913423.
Lemma Fx_67f48 : fetch_word Asan.M.loaded_segments (0x67f98 : word) = Some Wx_67f48.
Proof. vm_refl. Qed.
Lemma Dx_67f48 : decode_any Wx_67f48 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f4c : bv 32 := 0x05213023.
Lemma Fx_67f4c : fetch_word Asan.M.loaded_segments (0x67f9c : word) = Some Wx_67f4c.
Proof. vm_refl. Qed.
Lemma Dx_67f4c : decode_any Wx_67f4c = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f50 : bv 32 := 0x03313c23.
Lemma Fx_67f50 : fetch_word Asan.M.loaded_segments (0x67fa0 : word) = Some Wx_67f50.
Proof. vm_refl. Qed.
Lemma Dx_67f50 : decode_any Wx_67f50 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f54 : bv 32 := 0x03413823.
Lemma Fx_67f54 : fetch_word Asan.M.loaded_segments (0x67fa4 : word) = Some Wx_67f54.
Proof. vm_refl. Qed.
Lemma Dx_67f54 : decode_any Wx_67f54 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f58 : bv 32 := 0x03513423.
Lemma Fx_67f58 : fetch_word Asan.M.loaded_segments (0x67fa8 : word) = Some Wx_67f58.
Proof. vm_refl. Qed.
Lemma Dx_67f58 : decode_any Wx_67f58 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f5c : bv 32 := 0x03613023.
Lemma Fx_67f5c : fetch_word Asan.M.loaded_segments (0x67fac : word) = Some Wx_67f5c.
Proof. vm_refl. Qed.
Lemma Dx_67f5c : decode_any Wx_67f5c = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f60 : bv 32 := 0x01713c23.
Lemma Fx_67f60 : fetch_word Asan.M.loaded_segments (0x67fb0 : word) = Some Wx_67f60.
Proof. vm_refl. Qed.
Lemma Dx_67f60 : decode_any Wx_67f60 = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f64 : bv 32 := 0x01813823.
Lemma Fx_67f64 : fetch_word Asan.M.loaded_segments (0x67fb4 : word) = Some Wx_67f64.
Proof. vm_refl. Qed.
Lemma Dx_67f64 : decode_any Wx_67f64 = Some (Store SZ8 2 24 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f68 : bv 32 := 0x01913423.
Lemma Fx_67f68 : fetch_word Asan.M.loaded_segments (0x67fb8 : word) = Some Wx_67f68.
Proof. vm_refl. Qed.
Lemma Dx_67f68 : decode_any Wx_67f68 = Some (Store SZ8 2 25 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f6c : bv 32 := 0x000f9517.
Lemma Fx_67f6c : fetch_word Asan.M.loaded_segments (0x67fbc : word) = Some Wx_67f6c.
Proof. vm_refl. Qed.
Lemma Dx_67f6c : decode_any Wx_67f6c = Some (Auipc 10 249, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f70 : bv 32 := 0xc5453a03.
Lemma Fx_67f70 : fetch_word Asan.M.loaded_segments (0x67fc0 : word) = Some Wx_67f70.
Proof. vm_refl. Qed.
Lemma Dx_67f70 : decode_any Wx_67f70 = Some (Load SZ8 true 20 10 3156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f74 : bv 32 := 0x01ca4503.
Lemma Fx_67f74 : fetch_word Asan.M.loaded_segments (0x67fc4 : word) = Some Wx_67f74.
Proof. vm_refl. Qed.
Lemma Dx_67f74 : decode_any Wx_67f74 = Some (Load SZ1 false 10 20 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_67f78 : bv 32 := 0x1e050e63.
Lemma Fx_67f78 : fetch_word Asan.M.loaded_segments (0x67fc8 : word) = Some Wx_67f78.
Proof. vm_refl. Qed.
Lemma Dx_67f78 : decode_any Wx_67f78 = Some (Branch BC_EQ 10 0 508, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_68174 : bv 32 := 0x05813083.
Lemma Fx_68174 : fetch_word Asan.M.loaded_segments (0x681c4 : word) = Some Wx_68174.
Proof. vm_refl. Qed.
Lemma Dx_68174 : decode_any Wx_68174 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68178 : bv 32 := 0x05013403.
Lemma Fx_68178 : fetch_word Asan.M.loaded_segments (0x681c8 : word) = Some Wx_68178.
Proof. vm_refl. Qed.
Lemma Dx_68178 : decode_any Wx_68178 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6817c : bv 32 := 0x04813483.
Lemma Fx_6817c : fetch_word Asan.M.loaded_segments (0x681cc : word) = Some Wx_6817c.
Proof. vm_refl. Qed.
Lemma Dx_6817c : decode_any Wx_6817c = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68180 : bv 32 := 0x04013903.
Lemma Fx_68180 : fetch_word Asan.M.loaded_segments (0x681d0 : word) = Some Wx_68180.
Proof. vm_refl. Qed.
Lemma Dx_68180 : decode_any Wx_68180 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68184 : bv 32 := 0x03813983.
Lemma Fx_68184 : fetch_word Asan.M.loaded_segments (0x681d4 : word) = Some Wx_68184.
Proof. vm_refl. Qed.
Lemma Dx_68184 : decode_any Wx_68184 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68188 : bv 32 := 0x03013a03.
Lemma Fx_68188 : fetch_word Asan.M.loaded_segments (0x681d8 : word) = Some Wx_68188.
Proof. vm_refl. Qed.
Lemma Dx_68188 : decode_any Wx_68188 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6818c : bv 32 := 0x02813a83.
Lemma Fx_6818c : fetch_word Asan.M.loaded_segments (0x681dc : word) = Some Wx_6818c.
Proof. vm_refl. Qed.
Lemma Dx_6818c : decode_any Wx_6818c = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68190 : bv 32 := 0x02013b03.
Lemma Fx_68190 : fetch_word Asan.M.loaded_segments (0x681e0 : word) = Some Wx_68190.
Proof. vm_refl. Qed.
Lemma Dx_68190 : decode_any Wx_68190 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68194 : bv 32 := 0x01813b83.
Lemma Fx_68194 : fetch_word Asan.M.loaded_segments (0x681e4 : word) = Some Wx_68194.
Proof. vm_refl. Qed.
Lemma Dx_68194 : decode_any Wx_68194 = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68198 : bv 32 := 0x01013c03.
Lemma Fx_68198 : fetch_word Asan.M.loaded_segments (0x681e8 : word) = Some Wx_68198.
Proof. vm_refl. Qed.
Lemma Dx_68198 : decode_any Wx_68198 = Some (Load SZ8 true 24 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6819c : bv 32 := 0x00813c83.
Lemma Fx_6819c : fetch_word Asan.M.loaded_segments (0x681ec : word) = Some Wx_6819c.
Proof. vm_refl. Qed.
Lemma Dx_6819c : decode_any Wx_6819c = Some (Load SZ8 true 25 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_681a0 : bv 32 := 0x06010113.
Lemma Fx_681a0 : fetch_word Asan.M.loaded_segments (0x681f0 : word) = Some Wx_681a0.
Proof. vm_refl. Qed.
Lemma Dx_681a0 : decode_any Wx_681a0 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_681a4 : bv 32 := 0x00008067.
Lemma Fx_681a4 : fetch_word Asan.M.loaded_segments (0x681f4 : word) = Some Wx_681a4.
Proof. vm_refl. Qed.
Lemma Dx_681a4 : decode_any Wx_681a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_6b9a8 : bv 32 := 0x5cc0a06f.
Lemma Fx_6b9a8 : fetch_word Asan.M.loaded_segments (0x6b9f8 : word) = Some Wx_6b9a8.
Proof. vm_refl. Qed.
Lemma Dx_6b9a8 : decode_any Wx_6b9a8 = Some (Jal 0 42444, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_75f74 : bv 32 := 0xfd010113.
Lemma Fx_75f74 : fetch_word Asan.M.loaded_segments (0x75fc4 : word) = Some Wx_75f74.
Proof. vm_refl. Qed.
Lemma Dx_75f74 : decode_any Wx_75f74 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75f78 : bv 32 := 0x02113423.
Lemma Fx_75f78 : fetch_word Asan.M.loaded_segments (0x75fc8 : word) = Some Wx_75f78.
Proof. vm_refl. Qed.
Lemma Dx_75f78 : decode_any Wx_75f78 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75f7c : bv 32 := 0x02813023.
Lemma Fx_75f7c : fetch_word Asan.M.loaded_segments (0x75fcc : word) = Some Wx_75f7c.
Proof. vm_refl. Qed.
Lemma Dx_75f7c : decode_any Wx_75f7c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75f80 : bv 32 := 0x00913c23.
Lemma Fx_75f80 : fetch_word Asan.M.loaded_segments (0x75fd0 : word) = Some Wx_75f80.
Proof. vm_refl. Qed.
Lemma Dx_75f80 : decode_any Wx_75f80 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75f84 : bv 32 := 0x01213823.
Lemma Fx_75f84 : fetch_word Asan.M.loaded_segments (0x75fd4 : word) = Some Wx_75f84.
Proof. vm_refl. Qed.
Lemma Dx_75f84 : decode_any Wx_75f84 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75f88 : bv 32 := 0x01313423.
Lemma Fx_75f88 : fetch_word Asan.M.loaded_segments (0x75fd8 : word) = Some Wx_75f88.
Proof. vm_refl. Qed.
Lemma Dx_75f88 : decode_any Wx_75f88 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75f8c : bv 32 := 0x00060413.
Lemma Fx_75f8c : fetch_word Asan.M.loaded_segments (0x75fdc : word) = Some Wx_75f8c.
Proof. vm_refl. Qed.
Lemma Dx_75f8c : decode_any Wx_75f8c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75f90 : bv 32 := 0x00058493.
Lemma Fx_75f90 : fetch_word Asan.M.loaded_segments (0x75fe0 : word) = Some Wx_75f90.
Proof. vm_refl. Qed.
Lemma Dx_75f90 : decode_any Wx_75f90 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75f94 : bv 32 := 0x00050913.
Lemma Fx_75f94 : fetch_word Asan.M.loaded_segments (0x75fe4 : word) = Some Wx_75f94.
Proof. vm_refl. Qed.
Lemma Dx_75f94 : decode_any Wx_75f94 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75f98 : bv 32 := 0x364130ef.
Lemma Fx_75f98 : fetch_word Asan.M.loaded_segments (0x75fe8 : word) = Some Wx_75f98.
Proof. vm_refl. Qed.
Lemma Dx_75f98 : decode_any Wx_75f98 = Some (Jal 1 78692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75f9c : bv 32 := 0x29d390ef.
Lemma Fx_75f9c : fetch_word Asan.M.loaded_segments (0x75fec : word) = Some Wx_75f9c.
Proof. vm_refl. Qed.
Lemma Dx_75f9c : decode_any Wx_75f9c = Some (Jal 1 236188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fa0 : bv 32 := 0x000ed997.
Lemma Fx_75fa0 : fetch_word Asan.M.loaded_segments (0x75ff0 : word) = Some Wx_75fa0.
Proof. vm_refl. Qed.
Lemma Dx_75fa0 : decode_any Wx_75fa0 = Some (Auipc 19 237, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fa4 : bv 32 := 0xc009b683.
Lemma Fx_75fa4 : fetch_word Asan.M.loaded_segments (0x75ff4 : word) = Some Wx_75fa4.
Proof. vm_refl. Qed.
Lemma Dx_75fa4 : decode_any Wx_75fa4 = Some (Load SZ8 true 13 19 3072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fa8 : bv 32 := 0x00090513.
Lemma Fx_75fa8 : fetch_word Asan.M.loaded_segments (0x75ff8 : word) = Some Wx_75fa8.
Proof. vm_refl. Qed.
Lemma Dx_75fa8 : decode_any Wx_75fa8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fac : bv 32 := 0x00048593.
Lemma Fx_75fac : fetch_word Asan.M.loaded_segments (0x75ffc : word) = Some Wx_75fac.
Proof. vm_refl. Qed.
Lemma Dx_75fac : decode_any Wx_75fac = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fb0 : bv 32 := 0x00040613.
Lemma Fx_75fb0 : fetch_word Asan.M.loaded_segments (0x76000 : word) = Some Wx_75fb0.
Proof. vm_refl. Qed.
Lemma Dx_75fb0 : decode_any Wx_75fb0 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fb4 : bv 32 := 0x000680e7.
Lemma Fx_75fb4 : fetch_word Asan.M.loaded_segments (0x76004 : word) = Some Wx_75fb4.
Proof. vm_refl. Qed.
Lemma Dx_75fb4 : decode_any Wx_75fb4 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fb8 : bv 32 := 0xc009b683.
Lemma Fx_75fb8 : fetch_word Asan.M.loaded_segments (0x76008 : word) = Some Wx_75fb8.
Proof. vm_refl. Qed.
Lemma Dx_75fb8 : decode_any Wx_75fb8 = Some (Load SZ8 true 13 19 3072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fbc : bv 32 := 0x00050413.
Lemma Fx_75fbc : fetch_word Asan.M.loaded_segments (0x7600c : word) = Some Wx_75fbc.
Proof. vm_refl. Qed.
Lemma Dx_75fbc : decode_any Wx_75fbc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fc0 : bv 32 := 0x00000517.
Lemma Fx_75fc0 : fetch_word Asan.M.loaded_segments (0x76010 : word) = Some Wx_75fc0.
Proof. vm_refl. Qed.
Lemma Dx_75fc0 : decode_any Wx_75fc0 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fc4 : bv 32 := 0x03850513.
Lemma Fx_75fc4 : fetch_word Asan.M.loaded_segments (0x76014 : word) = Some Wx_75fc4.
Proof. vm_refl. Qed.
Lemma Dx_75fc4 : decode_any Wx_75fc4 = Some (OpImm ALU_ADD 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fc8 : bv 32 := 0x00000593.
Lemma Fx_75fc8 : fetch_word Asan.M.loaded_segments (0x76018 : word) = Some Wx_75fc8.
Proof. vm_refl. Qed.
Lemma Dx_75fc8 : decode_any Wx_75fc8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fcc : bv 32 := 0x00000613.
Lemma Fx_75fcc : fetch_word Asan.M.loaded_segments (0x7601c : word) = Some Wx_75fcc.
Proof. vm_refl. Qed.
Lemma Dx_75fcc : decode_any Wx_75fcc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fd0 : bv 32 := 0x000680e7.
Lemma Fx_75fd0 : fetch_word Asan.M.loaded_segments (0x76020 : word) = Some Wx_75fd0.
Proof. vm_refl. Qed.
Lemma Dx_75fd0 : decode_any Wx_75fd0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fd4 : bv 32 := 0x281390ef.
Lemma Fx_75fd4 : fetch_word Asan.M.loaded_segments (0x76024 : word) = Some Wx_75fd4.
Proof. vm_refl. Qed.
Lemma Dx_75fd4 : decode_any Wx_75fd4 = Some (Jal 1 236160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fd8 : bv 32 := 0x00040513.
Lemma Fx_75fd8 : fetch_word Asan.M.loaded_segments (0x76028 : word) = Some Wx_75fd8.
Proof. vm_refl. Qed.
Lemma Dx_75fd8 : decode_any Wx_75fd8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fdc : bv 32 := 0x02813083.
Lemma Fx_75fdc : fetch_word Asan.M.loaded_segments (0x7602c : word) = Some Wx_75fdc.
Proof. vm_refl. Qed.
Lemma Dx_75fdc : decode_any Wx_75fdc = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fe0 : bv 32 := 0x02013403.
Lemma Fx_75fe0 : fetch_word Asan.M.loaded_segments (0x76030 : word) = Some Wx_75fe0.
Proof. vm_refl. Qed.
Lemma Dx_75fe0 : decode_any Wx_75fe0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fe4 : bv 32 := 0x01813483.
Lemma Fx_75fe4 : fetch_word Asan.M.loaded_segments (0x76034 : word) = Some Wx_75fe4.
Proof. vm_refl. Qed.
Lemma Dx_75fe4 : decode_any Wx_75fe4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fe8 : bv 32 := 0x01013903.
Lemma Fx_75fe8 : fetch_word Asan.M.loaded_segments (0x76038 : word) = Some Wx_75fe8.
Proof. vm_refl. Qed.
Lemma Dx_75fe8 : decode_any Wx_75fe8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75fec : bv 32 := 0x00813983.
Lemma Fx_75fec : fetch_word Asan.M.loaded_segments (0x7603c : word) = Some Wx_75fec.
Proof. vm_refl. Qed.
Lemma Dx_75fec : decode_any Wx_75fec = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75ff0 : bv 32 := 0x03010113.
Lemma Fx_75ff0 : fetch_word Asan.M.loaded_segments (0x76040 : word) = Some Wx_75ff0.
Proof. vm_refl. Qed.
Lemma Dx_75ff0 : decode_any Wx_75ff0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75ff4 : bv 32 := 0x00008067.
Lemma Fx_75ff4 : fetch_word Asan.M.loaded_segments (0x76044 : word) = Some Wx_75ff4.
Proof. vm_refl. Qed.
Lemma Dx_75ff4 : decode_any Wx_75ff4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_75ff8 : bv 32 := 0xf45f106f.
Lemma Fx_75ff8 : fetch_word Asan.M.loaded_segments (0x76048 : word) = Some Wx_75ff8.
Proof. vm_refl. Qed.
Lemma Dx_75ff8 : decode_any Wx_75ff8 = Some (Jal 0 2039620, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_892fc : bv 32 := 0xff010113.
Lemma Fx_892fc : fetch_word Asan.M.loaded_segments (0x8934c : word) = Some Wx_892fc.
Proof. vm_refl. Qed.
Lemma Dx_892fc : decode_any Wx_892fc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89300 : bv 32 := 0x00113423.
Lemma Fx_89300 : fetch_word Asan.M.loaded_segments (0x89350 : word) = Some Wx_89300.
Proof. vm_refl. Qed.
Lemma Dx_89300 : decode_any Wx_89300 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89304 : bv 32 := 0x00813023.
Lemma Fx_89304 : fetch_word Asan.M.loaded_segments (0x89354 : word) = Some Wx_89304.
Proof. vm_refl. Qed.
Lemma Dx_89304 : decode_any Wx_89304 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89308 : bv 32 := 0x000e2517.
Lemma Fx_89308 : fetch_word Asan.M.loaded_segments (0x89358 : word) = Some Wx_89308.
Proof. vm_refl. Qed.
Lemma Dx_89308 : decode_any Wx_89308 = Some (Auipc 10 226, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8930c : bv 32 := 0x88050413.
Lemma Fx_8930c : fetch_word Asan.M.loaded_segments (0x8935c : word) = Some Wx_8930c.
Proof. vm_refl. Qed.
Lemma Dx_8930c : decode_any Wx_8930c = Some (OpImm ALU_ADD 8 10 2176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89310 : bv 32 := 0x00040503.
Lemma Fx_89310 : fetch_word Asan.M.loaded_segments (0x89360 : word) = Some Wx_89310.
Proof. vm_refl. Qed.
Lemma Dx_89310 : decode_any Wx_89310 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89314 : bv 32 := 0x00100593.
Lemma Fx_89314 : fetch_word Asan.M.loaded_segments (0x89364 : word) = Some Wx_89314.
Proof. vm_refl. Qed.
Lemma Dx_89314 : decode_any Wx_89314 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89318 : bv 32 := 0x0230000f.
Lemma Fx_89318 : fetch_word Asan.M.loaded_segments (0x89368 : word) = Some Wx_89318.
Proof. vm_refl. Qed.
Lemma Dx_89318 : decode_any Wx_89318 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8931c : bv 32 := 0x00b51a63.
Lemma Fx_8931c : fetch_word Asan.M.loaded_segments (0x8936c : word) = Some Wx_8931c.
Proof. vm_refl. Qed.
Lemma Dx_8931c : decode_any Wx_8931c = Some (Branch BC_NE 10 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89320 : bv 32 := 0x00813083.
Lemma Fx_89320 : fetch_word Asan.M.loaded_segments (0x89370 : word) = Some Wx_89320.
Proof. vm_refl. Qed.
Lemma Dx_89320 : decode_any Wx_89320 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89324 : bv 32 := 0x00013403.
Lemma Fx_89324 : fetch_word Asan.M.loaded_segments (0x89374 : word) = Some Wx_89324.
Proof. vm_refl. Qed.
Lemma Dx_89324 : decode_any Wx_89324 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89328 : bv 32 := 0x01010113.
Lemma Fx_89328 : fetch_word Asan.M.loaded_segments (0x89378 : word) = Some Wx_89328.
Proof. vm_refl. Qed.
Lemma Dx_89328 : decode_any Wx_89328 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8932c : bv 32 := 0x00008067.
Lemma Fx_8932c : fetch_word Asan.M.loaded_segments (0x8937c : word) = Some Wx_8932c.
Proof. vm_refl. Qed.
Lemma Dx_8932c : decode_any Wx_8932c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_afa38 : bv 32 := 0x000b2517.
Lemma Fx_afa38 : fetch_word Asan.M.loaded_segments (0xafa88 : word) = Some Wx_afa38.
Proof. vm_refl. Qed.
Lemma Dx_afa38 : decode_any Wx_afa38 = Some (Auipc 10 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa3c : bv 32 := 0xdf053503.
Lemma Fx_afa3c : fetch_word Asan.M.loaded_segments (0xafa8c : word) = Some Wx_afa3c.
Proof. vm_refl. Qed.
Lemma Dx_afa3c : decode_any Wx_afa3c = Some (Load SZ8 true 10 10 3568, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa40 : bv 32 := 0x00450533.
Lemma Fx_afa40 : fetch_word Asan.M.loaded_segments (0xafa90 : word) = Some Wx_afa40.
Proof. vm_refl. Qed.
Lemma Dx_afa40 : decode_any Wx_afa40 = Some (Op ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa44 : bv 32 := 0x00052583.
Lemma Fx_afa44 : fetch_word Asan.M.loaded_segments (0xafa94 : word) = Some Wx_afa44.
Proof. vm_refl. Qed.
Lemma Dx_afa44 : decode_any Wx_afa44 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa48 : bv 32 := 0x00158593.
Lemma Fx_afa48 : fetch_word Asan.M.loaded_segments (0xafa98 : word) = Some Wx_afa48.
Proof. vm_refl. Qed.
Lemma Dx_afa48 : decode_any Wx_afa48 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa4c : bv 32 := 0x00b52023.
Lemma Fx_afa4c : fetch_word Asan.M.loaded_segments (0xafa9c : word) = Some Wx_afa4c.
Proof. vm_refl. Qed.
Lemma Dx_afa4c : decode_any Wx_afa4c = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa50 : bv 32 := 0x00008067.
Lemma Fx_afa50 : fetch_word Asan.M.loaded_segments (0xafaa0 : word) = Some Wx_afa50.
Proof. vm_refl. Qed.
Lemma Dx_afa50 : decode_any Wx_afa50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa54 : bv 32 := 0xff010113.
Lemma Fx_afa54 : fetch_word Asan.M.loaded_segments (0xafaa4 : word) = Some Wx_afa54.
Proof. vm_refl. Qed.
Lemma Dx_afa54 : decode_any Wx_afa54 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa58 : bv 32 := 0x00113423.
Lemma Fx_afa58 : fetch_word Asan.M.loaded_segments (0xafaa8 : word) = Some Wx_afa58.
Proof. vm_refl. Qed.
Lemma Dx_afa58 : decode_any Wx_afa58 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa5c : bv 32 := 0x00813023.
Lemma Fx_afa5c : fetch_word Asan.M.loaded_segments (0xafaac : word) = Some Wx_afa5c.
Proof. vm_refl. Qed.
Lemma Dx_afa5c : decode_any Wx_afa5c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa60 : bv 32 := 0x000b2517.
Lemma Fx_afa60 : fetch_word Asan.M.loaded_segments (0xafab0 : word) = Some Wx_afa60.
Proof. vm_refl. Qed.
Lemma Dx_afa60 : decode_any Wx_afa60 = Some (Auipc 10 178, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa64 : bv 32 := 0xdc853403.
Lemma Fx_afa64 : fetch_word Asan.M.loaded_segments (0xafab4 : word) = Some Wx_afa64.
Proof. vm_refl. Qed.
Lemma Dx_afa64 : decode_any Wx_afa64 = Some (Load SZ8 true 8 10 3528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa68 : bv 32 := 0x00440433.
Lemma Fx_afa68 : fetch_word Asan.M.loaded_segments (0xafab8 : word) = Some Wx_afa68.
Proof. vm_refl. Qed.
Lemma Dx_afa68 : decode_any Wx_afa68 = Some (Op ALU_ADD 8 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa6c : bv 32 := 0x00042503.
Lemma Fx_afa6c : fetch_word Asan.M.loaded_segments (0xafabc : word) = Some Wx_afa6c.
Proof. vm_refl. Qed.
Lemma Dx_afa6c : decode_any Wx_afa6c = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa70 : bv 32 := 0x00050e63.
Lemma Fx_afa70 : fetch_word Asan.M.loaded_segments (0xafac0 : word) = Some Wx_afa70.
Proof. vm_refl. Qed.
Lemma Dx_afa70 : decode_any Wx_afa70 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa74 : bv 32 := 0xfff50513.
Lemma Fx_afa74 : fetch_word Asan.M.loaded_segments (0xafac4 : word) = Some Wx_afa74.
Proof. vm_refl. Qed.
Lemma Dx_afa74 : decode_any Wx_afa74 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa78 : bv 32 := 0x00a42023.
Lemma Fx_afa78 : fetch_word Asan.M.loaded_segments (0xafac8 : word) = Some Wx_afa78.
Proof. vm_refl. Qed.
Lemma Dx_afa78 : decode_any Wx_afa78 = Some (Store SZ4 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa7c : bv 32 := 0x00813083.
Lemma Fx_afa7c : fetch_word Asan.M.loaded_segments (0xafacc : word) = Some Wx_afa7c.
Proof. vm_refl. Qed.
Lemma Dx_afa7c : decode_any Wx_afa7c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa80 : bv 32 := 0x00013403.
Lemma Fx_afa80 : fetch_word Asan.M.loaded_segments (0xafad0 : word) = Some Wx_afa80.
Proof. vm_refl. Qed.
Lemma Dx_afa80 : decode_any Wx_afa80 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa84 : bv 32 := 0x01010113.
Lemma Fx_afa84 : fetch_word Asan.M.loaded_segments (0xafad4 : word) = Some Wx_afa84.
Proof. vm_refl. Qed.
Lemma Dx_afa84 : decode_any Wx_afa84 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_afa88 : bv 32 := 0x00008067.
Lemma Fx_afa88 : fetch_word Asan.M.loaded_segments (0xafad8 : word) = Some Wx_afa88.
Proof. vm_refl. Qed.
Lemma Dx_afa88 : decode_any Wx_afa88 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

