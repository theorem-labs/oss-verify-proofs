(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_89214 : bv 32 := 0xfe010113.
Lemma F_89214 : fetch_word AsanUbsan.M.loaded_segments (0x89264 : word) = Some W_89214.
Proof. vm_refl. Qed.
Lemma D_89214 : decode_any W_89214 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_89218 : bv 32 := 0x00113c23.
Lemma F_89218 : fetch_word AsanUbsan.M.loaded_segments (0x89268 : word) = Some W_89218.
Proof. vm_refl. Qed.
Lemma D_89218 : decode_any W_89218 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8921c : bv 32 := 0x00813823.
Lemma F_8921c : fetch_word AsanUbsan.M.loaded_segments (0x8926c : word) = Some W_8921c.
Proof. vm_refl. Qed.
Lemma D_8921c : decode_any W_8921c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_89220 : bv 32 := 0x00913423.
Lemma F_89220 : fetch_word AsanUbsan.M.loaded_segments (0x89270 : word) = Some W_89220.
Proof. vm_refl. Qed.
Lemma D_89220 : decode_any W_89220 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_89224 : bv 32 := 0x01213023.
Lemma F_89224 : fetch_word AsanUbsan.M.loaded_segments (0x89274 : word) = Some W_89224.
Proof. vm_refl. Qed.
Lemma D_89224 : decode_any W_89224 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89228 : bv 32 := 0x00058413.
Lemma F_89228 : fetch_word AsanUbsan.M.loaded_segments (0x89278 : word) = Some W_89228.
Proof. vm_refl. Qed.
Lemma D_89228 : decode_any W_89228 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8922c : bv 32 := 0x00050493.
Lemma F_8922c : fetch_word AsanUbsan.M.loaded_segments (0x8927c : word) = Some W_8922c.
Proof. vm_refl. Qed.
Lemma D_8922c : decode_any W_8922c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89230 : bv 32 := 0x09c000ef.
Lemma F_89230 : fetch_word AsanUbsan.M.loaded_segments (0x89280 : word) = Some W_89230.
Proof. vm_refl. Qed.
Lemma D_89230 : decode_any W_89230 = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_89234 : bv 32 := 0x0014f517.
Lemma F_89234 : fetch_word AsanUbsan.M.loaded_segments (0x89284 : word) = Some W_89234.
Proof. vm_refl. Qed.
Lemma D_89234 : decode_any W_89234 = Some (Auipc 10 335, 4%Z).
Proof. vm_refl. Qed.

Definition W_89238 : bv 32 := 0x93c50913.
Lemma F_89238 : fetch_word AsanUbsan.M.loaded_segments (0x89288 : word) = Some W_89238.
Proof. vm_refl. Qed.
Lemma D_89238 : decode_any W_89238 = Some (OpImm ALU_ADD 18 10 2364, 4%Z).
Proof. vm_refl. Qed.

Definition W_8923c : bv 32 := 0x00093603.
Lemma F_8923c : fetch_word AsanUbsan.M.loaded_segments (0x8928c : word) = Some W_8923c.
Proof. vm_refl. Qed.
Lemma D_8923c : decode_any W_8923c = Some (Load SZ8 true 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89240 : bv 32 := 0x06060a63.
Lemma F_89240 : fetch_word AsanUbsan.M.loaded_segments (0x89290 : word) = Some W_89240.
Proof. vm_refl. Qed.
Lemma D_89240 : decode_any W_89240 = Some (Branch BC_EQ 12 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_892b4 : bv 32 := 0x01813083.
Lemma F_892b4 : fetch_word AsanUbsan.M.loaded_segments (0x89304 : word) = Some W_892b4.
Proof. vm_refl. Qed.
Lemma D_892b4 : decode_any W_892b4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_892b8 : bv 32 := 0x01013403.
Lemma F_892b8 : fetch_word AsanUbsan.M.loaded_segments (0x89308 : word) = Some W_892b8.
Proof. vm_refl. Qed.
Lemma D_892b8 : decode_any W_892b8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_892bc : bv 32 := 0x00813483.
Lemma F_892bc : fetch_word AsanUbsan.M.loaded_segments (0x8930c : word) = Some W_892bc.
Proof. vm_refl. Qed.
Lemma D_892bc : decode_any W_892bc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_892c0 : bv 32 := 0x00013903.
Lemma F_892c0 : fetch_word AsanUbsan.M.loaded_segments (0x89310 : word) = Some W_892c0.
Proof. vm_refl. Qed.
Lemma D_892c0 : decode_any W_892c0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_892c4 : bv 32 := 0x02010113.
Lemma F_892c4 : fetch_word AsanUbsan.M.loaded_segments (0x89314 : word) = Some W_892c4.
Proof. vm_refl. Qed.
Lemma D_892c4 : decode_any W_892c4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_892c8 : bv 32 := 0x00008067.
Lemma F_892c8 : fetch_word AsanUbsan.M.loaded_segments (0x89318 : word) = Some W_892c8.
Proof. vm_refl. Qed.
Lemma D_892c8 : decode_any W_892c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_892cc : bv 32 := 0x00008067.
Lemma F_892cc : fetch_word AsanUbsan.M.loaded_segments (0x8931c : word) = Some W_892cc.
Proof. vm_refl. Qed.
Lemma D_892cc : decode_any W_892cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_892d0 : bv 32 := 0xfe010113.
Lemma F_892d0 : fetch_word AsanUbsan.M.loaded_segments (0x89320 : word) = Some W_892d0.
Proof. vm_refl. Qed.
Lemma D_892d0 : decode_any W_892d0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_892d4 : bv 32 := 0x00113c23.
Lemma F_892d4 : fetch_word AsanUbsan.M.loaded_segments (0x89324 : word) = Some W_892d4.
Proof. vm_refl. Qed.
Lemma D_892d4 : decode_any W_892d4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_892d8 : bv 32 := 0x00813823.
Lemma F_892d8 : fetch_word AsanUbsan.M.loaded_segments (0x89328 : word) = Some W_892d8.
Proof. vm_refl. Qed.
Lemma D_892d8 : decode_any W_892d8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_892dc : bv 32 := 0x00913423.
Lemma F_892dc : fetch_word AsanUbsan.M.loaded_segments (0x8932c : word) = Some W_892dc.
Proof. vm_refl. Qed.
Lemma D_892dc : decode_any W_892dc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_892e0 : bv 32 := 0x00050413.
Lemma F_892e0 : fetch_word AsanUbsan.M.loaded_segments (0x89330 : word) = Some W_892e0.
Proof. vm_refl. Qed.
Lemma D_892e0 : decode_any W_892e0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_892e4 : bv 32 := 0x098000ef.
Lemma F_892e4 : fetch_word AsanUbsan.M.loaded_segments (0x89334 : word) = Some W_892e4.
Proof. vm_refl. Qed.
Lemma D_892e4 : decode_any W_892e4 = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_892e8 : bv 32 := 0x00050e63.
Lemma F_892e8 : fetch_word AsanUbsan.M.loaded_segments (0x89338 : word) = Some W_892e8.
Proof. vm_refl. Qed.
Lemma D_892e8 : decode_any W_892e8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_89304 : bv 32 := 0x00040513.
Lemma F_89304 : fetch_word AsanUbsan.M.loaded_segments (0x89354 : word) = Some W_89304.
Proof. vm_refl. Qed.
Lemma D_89304 : decode_any W_89304 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89308 : bv 32 := 0x07c000ef.
Lemma F_89308 : fetch_word AsanUbsan.M.loaded_segments (0x89358 : word) = Some W_89308.
Proof. vm_refl. Qed.
Lemma D_89308 : decode_any W_89308 = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_8930c : bv 32 := 0x0014f517.
Lemma F_8930c : fetch_word AsanUbsan.M.loaded_segments (0x8935c : word) = Some W_8930c.
Proof. vm_refl. Qed.
Lemma D_8930c : decode_any W_8930c = Some (Auipc 10 335, 4%Z).
Proof. vm_refl. Qed.

Definition W_89310 : bv 32 := 0x86450493.
Lemma F_89310 : fetch_word AsanUbsan.M.loaded_segments (0x89360 : word) = Some W_89310.
Proof. vm_refl. Qed.
Lemma D_89310 : decode_any W_89310 = Some (OpImm ALU_ADD 9 10 2148, 4%Z).
Proof. vm_refl. Qed.

Definition W_89314 : bv 32 := 0x0084b583.
Lemma F_89314 : fetch_word AsanUbsan.M.loaded_segments (0x89364 : word) = Some W_89314.
Proof. vm_refl. Qed.
Lemma D_89314 : decode_any W_89314 = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_89318 : bv 32 := 0x04058663.
Lemma F_89318 : fetch_word AsanUbsan.M.loaded_segments (0x89368 : word) = Some W_89318.
Proof. vm_refl. Qed.
Lemma D_89318 : decode_any W_89318 = Some (Branch BC_EQ 11 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_89364 : bv 32 := 0x00000513.
Lemma F_89364 : fetch_word AsanUbsan.M.loaded_segments (0x893b4 : word) = Some W_89364.
Proof. vm_refl. Qed.
Lemma D_89364 : decode_any W_89364 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89368 : bv 32 := 0x01813083.
Lemma F_89368 : fetch_word AsanUbsan.M.loaded_segments (0x893b8 : word) = Some W_89368.
Proof. vm_refl. Qed.
Lemma D_89368 : decode_any W_89368 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8936c : bv 32 := 0x01013403.
Lemma F_8936c : fetch_word AsanUbsan.M.loaded_segments (0x893bc : word) = Some W_8936c.
Proof. vm_refl. Qed.
Lemma D_8936c : decode_any W_8936c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_89370 : bv 32 := 0x00813483.
Lemma F_89370 : fetch_word AsanUbsan.M.loaded_segments (0x893c0 : word) = Some W_89370.
Proof. vm_refl. Qed.
Lemma D_89370 : decode_any W_89370 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_89374 : bv 32 := 0x02010113.
Lemma F_89374 : fetch_word AsanUbsan.M.loaded_segments (0x893c4 : word) = Some W_89374.
Proof. vm_refl. Qed.
Lemma D_89374 : decode_any W_89374 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_89378 : bv 32 := 0x00008067.
Lemma F_89378 : fetch_word AsanUbsan.M.loaded_segments (0x893c8 : word) = Some W_89378.
Proof. vm_refl. Qed.
Lemma D_89378 : decode_any W_89378 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8937c : bv 32 := 0x00000513.
Lemma F_8937c : fetch_word AsanUbsan.M.loaded_segments (0x893cc : word) = Some W_8937c.
Proof. vm_refl. Qed.
Lemma D_8937c : decode_any W_8937c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89380 : bv 32 := 0x00008067.
Lemma F_89380 : fetch_word AsanUbsan.M.loaded_segments (0x893d0 : word) = Some W_89380.
Proof. vm_refl. Qed.
Lemma D_89380 : decode_any W_89380 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_89384 : bv 32 := 0x00008067.
Lemma F_89384 : fetch_word AsanUbsan.M.loaded_segments (0x893d4 : word) = Some W_89384.
Proof. vm_refl. Qed.
Lemma D_89384 : decode_any W_89384 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
