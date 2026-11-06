(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_662ac : bv 32 := 0xf7010113.
Lemma F_662ac : fetch_word AsanUbsan.M.loaded_segments (0x662f4 : word) = Some W_662ac.
Proof. vm_refl. Qed.
Lemma D_662ac : decode_any W_662ac = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662b0 : bv 32 := 0x08113423.
Lemma F_662b0 : fetch_word AsanUbsan.M.loaded_segments (0x662f8 : word) = Some W_662b0.
Proof. vm_refl. Qed.
Lemma D_662b0 : decode_any W_662b0 = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662b4 : bv 32 := 0x08813023.
Lemma F_662b4 : fetch_word AsanUbsan.M.loaded_segments (0x662fc : word) = Some W_662b4.
Proof. vm_refl. Qed.
Lemma D_662b4 : decode_any W_662b4 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662b8 : bv 32 := 0x06913c23.
Lemma F_662b8 : fetch_word AsanUbsan.M.loaded_segments (0x66300 : word) = Some W_662b8.
Proof. vm_refl. Qed.
Lemma D_662b8 : decode_any W_662b8 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662bc : bv 32 := 0x07213823.
Lemma F_662bc : fetch_word AsanUbsan.M.loaded_segments (0x66304 : word) = Some W_662bc.
Proof. vm_refl. Qed.
Lemma D_662bc : decode_any W_662bc = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662c0 : bv 32 := 0x07313423.
Lemma F_662c0 : fetch_word AsanUbsan.M.loaded_segments (0x66308 : word) = Some W_662c0.
Proof. vm_refl. Qed.
Lemma D_662c0 : decode_any W_662c0 = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662c4 : bv 32 := 0x07413023.
Lemma F_662c4 : fetch_word AsanUbsan.M.loaded_segments (0x6630c : word) = Some W_662c4.
Proof. vm_refl. Qed.
Lemma D_662c4 : decode_any W_662c4 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662c8 : bv 32 := 0x05513c23.
Lemma F_662c8 : fetch_word AsanUbsan.M.loaded_segments (0x66310 : word) = Some W_662c8.
Proof. vm_refl. Qed.
Lemma D_662c8 : decode_any W_662c8 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662cc : bv 32 := 0x05613823.
Lemma F_662cc : fetch_word AsanUbsan.M.loaded_segments (0x66314 : word) = Some W_662cc.
Proof. vm_refl. Qed.
Lemma D_662cc : decode_any W_662cc = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662d0 : bv 32 := 0x05713423.
Lemma F_662d0 : fetch_word AsanUbsan.M.loaded_segments (0x66318 : word) = Some W_662d0.
Proof. vm_refl. Qed.
Lemma D_662d0 : decode_any W_662d0 = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662d4 : bv 32 := 0x05813023.
Lemma F_662d4 : fetch_word AsanUbsan.M.loaded_segments (0x6631c : word) = Some W_662d4.
Proof. vm_refl. Qed.
Lemma D_662d4 : decode_any W_662d4 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662d8 : bv 32 := 0x03913c23.
Lemma F_662d8 : fetch_word AsanUbsan.M.loaded_segments (0x66320 : word) = Some W_662d8.
Proof. vm_refl. Qed.
Lemma D_662d8 : decode_any W_662d8 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662dc : bv 32 := 0x03a13823.
Lemma F_662dc : fetch_word AsanUbsan.M.loaded_segments (0x66324 : word) = Some W_662dc.
Proof. vm_refl. Qed.
Lemma D_662dc : decode_any W_662dc = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662e0 : bv 32 := 0x03b13423.
Lemma F_662e0 : fetch_word AsanUbsan.M.loaded_segments (0x66328 : word) = Some W_662e0.
Proof. vm_refl. Qed.
Lemma D_662e0 : decode_any W_662e0 = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662e4 : bv 32 := 0x00058493.
Lemma F_662e4 : fetch_word AsanUbsan.M.loaded_segments (0x6632c : word) = Some W_662e4.
Proof. vm_refl. Qed.
Lemma D_662e4 : decode_any W_662e4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662e8 : bv 32 := 0x00050c93.
Lemma F_662e8 : fetch_word AsanUbsan.M.loaded_segments (0x66330 : word) = Some W_662e8.
Proof. vm_refl. Qed.
Lemma D_662e8 : decode_any W_662e8 = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662ec : bv 32 := 0x42c260ef.
Lemma F_662ec : fetch_word AsanUbsan.M.loaded_segments (0x66334 : word) = Some W_662ec.
Proof. vm_refl. Qed.
Lemma D_662ec : decode_any W_662ec = Some (Jal 1 156716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662f0 : bv 32 := 0x26050463.
Lemma F_662f0 : fetch_word AsanUbsan.M.loaded_segments (0x66338 : word) = Some W_662f0.
Proof. vm_refl. Qed.
Lemma D_662f0 : decode_any W_662f0 = Some (Branch BC_EQ 10 0 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662f4 : bv 32 := 0x00050913.
Lemma F_662f4 : fetch_word AsanUbsan.M.loaded_segments (0x6633c : word) = Some W_662f4.
Proof. vm_refl. Qed.
Lemma D_662f4 : decode_any W_662f4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662f8 : bv 32 := 0x5e4260ef.
Lemma F_662f8 : fetch_word AsanUbsan.M.loaded_segments (0x66340 : word) = Some W_662f8.
Proof. vm_refl. Qed.
Lemma D_662f8 : decode_any W_662f8 = Some (Jal 1 157156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662fc : bv 32 := 0x00050993.
Lemma F_662fc : fetch_word AsanUbsan.M.loaded_segments (0x66344 : word) = Some W_662fc.
Proof. vm_refl. Qed.
Lemma D_662fc : decode_any W_662fc = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66300 : bv 32 := 0x00090513.
Lemma F_66300 : fetch_word AsanUbsan.M.loaded_segments (0x66348 : word) = Some W_66300.
Proof. vm_refl. Qed.
Lemma D_66300 : decode_any W_66300 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66304 : bv 32 := 0x630260ef.
Lemma F_66304 : fetch_word AsanUbsan.M.loaded_segments (0x6634c : word) = Some W_66304.
Proof. vm_refl. Qed.
Lemma D_66304 : decode_any W_66304 = Some (Jal 1 157232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66308 : bv 32 := 0x2499e863.
Lemma F_66308 : fetch_word AsanUbsan.M.loaded_segments (0x66350 : word) = Some W_66308.
Proof. vm_refl. Qed.
Lemma D_66308 : decode_any W_66308 = Some (Branch BC_LTU 19 9 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6630c : bv 32 := 0x00050913.
Lemma F_6630c : fetch_word AsanUbsan.M.loaded_segments (0x66354 : word) = Some W_6630c.
Proof. vm_refl. Qed.
Lemma D_6630c : decode_any W_6630c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66310 : bv 32 := 0x24a4e463.
Lemma F_66310 : fetch_word AsanUbsan.M.loaded_segments (0x66358 : word) = Some W_66310.
Proof. vm_refl. Qed.
Lemma D_66310 : decode_any W_66310 = Some (Branch BC_LTU 9 10 584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66314 : bv 32 := 0x00000d13.
Lemma F_66314 : fetch_word AsanUbsan.M.loaded_segments (0x6635c : word) = Some W_66314.
Proof. vm_refl. Qed.
Lemma D_66314 : decode_any W_66314 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66318 : bv 32 := 0x00001437.
Lemma F_66318 : fetch_word AsanUbsan.M.loaded_segments (0x66360 : word) = Some W_66318.
Proof. vm_refl. Qed.
Lemma D_66318 : decode_any W_66318 = Some (Lui 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6631c : bv 32 := 0x000fe517.
Lemma F_6631c : fetch_word AsanUbsan.M.loaded_segments (0x66364 : word) = Some W_6631c.
Proof. vm_refl. Qed.
Lemma D_6631c : decode_any W_6631c = Some (Auipc 10 254, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66320 : bv 32 := 0x000fe597.
Lemma F_66320 : fetch_word AsanUbsan.M.loaded_segments (0x66368 : word) = Some W_66320.
Proof. vm_refl. Qed.
Lemma D_66320 : decode_any W_66320 = Some (Auipc 11 254, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66324 : bv 32 := 0x000fe617.
Lemma F_66324 : fetch_word AsanUbsan.M.loaded_segments (0x6636c : word) = Some W_66324.
Proof. vm_refl. Qed.
Lemma D_66324 : decode_any W_66324 = Some (Auipc 12 254, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66328 : bv 32 := 0x000fe697.
Lemma F_66328 : fetch_word AsanUbsan.M.loaded_segments (0x66370 : word) = Some W_66328.
Proof. vm_refl. Qed.
Lemma D_66328 : decode_any W_66328 = Some (Auipc 13 254, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6632c : bv 32 := 0x000fe717.
Lemma F_6632c : fetch_word AsanUbsan.M.loaded_segments (0x66374 : word) = Some W_6632c.
Proof. vm_refl. Qed.
Lemma D_6632c : decode_any W_6632c = Some (Auipc 14 254, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66330 : bv 32 := 0xfffaa797.
Lemma F_66330 : fetch_word AsanUbsan.M.loaded_segments (0x66378 : word) = Some W_66330.
Proof. vm_refl. Qed.
Lemma D_66330 : decode_any W_66330 = Some (Auipc 15 1048490, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66334 : bv 32 := 0x008c8433.
Lemma F_66334 : fetch_word AsanUbsan.M.loaded_segments (0x6637c : word) = Some W_66334.
Proof. vm_refl. Qed.
Lemma D_66334 : decode_any W_66334 = Some (Op ALU_ADD 8 25 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66338 : bv 32 := 0x1b453b03.
Lemma F_66338 : fetch_word AsanUbsan.M.loaded_segments (0x66380 : word) = Some W_66338.
Proof. vm_refl. Qed.
Lemma D_66338 : decode_any W_66338 = Some (Load SZ8 true 22 10 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6633c : bv 32 := 0x1b85b503.
Lemma F_6633c : fetch_word AsanUbsan.M.loaded_segments (0x66384 : word) = Some W_6633c.
Proof. vm_refl. Qed.
Lemma D_6633c : decode_any W_6633c = Some (Load SZ8 true 10 11 440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66340 : bv 32 := 0x00a13c23.
Lemma F_66340 : fetch_word AsanUbsan.M.loaded_segments (0x66388 : word) = Some W_66340.
Proof. vm_refl. Qed.
Lemma D_66340 : decode_any W_66340 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66344 : bv 32 := 0x1bc63503.
Lemma F_66344 : fetch_word AsanUbsan.M.loaded_segments (0x6638c : word) = Some W_66344.
Proof. vm_refl. Qed.
Lemma D_66344 : decode_any W_66344 = Some (Load SZ8 true 10 12 444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66348 : bv 32 := 0x00a13823.
Lemma F_66348 : fetch_word AsanUbsan.M.loaded_segments (0x66390 : word) = Some W_66348.
Proof. vm_refl. Qed.
Lemma D_66348 : decode_any W_66348 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6634c : bv 32 := 0x1c06b503.
Lemma F_6634c : fetch_word AsanUbsan.M.loaded_segments (0x66394 : word) = Some W_6634c.
Proof. vm_refl. Qed.
Lemma D_6634c : decode_any W_6634c = Some (Load SZ8 true 10 13 448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66350 : bv 32 := 0x00a13423.
Lemma F_66350 : fetch_word AsanUbsan.M.loaded_segments (0x66398 : word) = Some W_66350.
Proof. vm_refl. Qed.
Lemma D_66350 : decode_any W_66350 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66354 : bv 32 := 0x19c73503.
Lemma F_66354 : fetch_word AsanUbsan.M.loaded_segments (0x6639c : word) = Some W_66354.
Proof. vm_refl. Qed.
Lemma D_66354 : decode_any W_66354 = Some (Load SZ8 true 10 14 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66358 : bv 32 := 0x00a13023.
Lemma F_66358 : fetch_word AsanUbsan.M.loaded_segments (0x663a0 : word) = Some W_66358.
Proof. vm_refl. Qed.
Lemma D_66358 : decode_any W_66358 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6635c : bv 32 := 0x0307bb83.
Lemma F_6635c : fetch_word AsanUbsan.M.loaded_segments (0x663a4 : word) = Some W_6635c.
Proof. vm_refl. Qed.
Lemma D_6635c : decode_any W_6635c = Some (Load SZ8 true 23 15 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66360 : bv 32 := 0x00100393.
Lemma F_66360 : fetch_word AsanUbsan.M.loaded_segments (0x663a8 : word) = Some W_66360.
Proof. vm_refl. Qed.
Lemma D_66360 : decode_any W_66360 = Some (OpImm ALU_ADD 7 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66364 : bv 32 := 0x00600e13.
Lemma F_66364 : fetch_word AsanUbsan.M.loaded_segments (0x663ac : word) = Some W_66364.
Proof. vm_refl. Qed.
Lemma D_66364 : decode_any W_66364 = Some (OpImm ALU_ADD 28 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66368 : bv 32 := 0x00000a13.
Lemma F_66368 : fetch_word AsanUbsan.M.loaded_segments (0x663b0 : word) = Some W_66368.
Proof. vm_refl. Qed.
Lemma D_66368 : decode_any W_66368 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6636c : bv 32 := 0x0100006f.
Lemma F_6636c : fetch_word AsanUbsan.M.loaded_segments (0x663b4 : word) = Some W_6636c.
Proof. vm_refl. Qed.
Lemma D_6636c : decode_any W_6636c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66370 : bv 32 := 0x001a0a13.
Lemma F_66370 : fetch_word AsanUbsan.M.loaded_segments (0x663b8 : word) = Some W_66370.
Proof. vm_refl. Qed.
Lemma D_66370 : decode_any W_66370 = Some (OpImm ALU_ADD 20 20 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66374 : bv 32 := 0x00b00513.
Lemma F_66374 : fetch_word AsanUbsan.M.loaded_segments (0x663bc : word) = Some W_66374.
Proof. vm_refl. Qed.
Lemma D_66374 : decode_any W_66374 = Some (OpImm ALU_ADD 10 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66378 : bv 32 := 0x1caa0e63.
Lemma F_66378 : fetch_word AsanUbsan.M.loaded_segments (0x663c0 : word) = Some W_66378.
Proof. vm_refl. Qed.
Lemma D_66378 : decode_any W_66378 = Some (Branch BC_EQ 20 10 476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6637c : bv 32 := 0x00000d93.
Lemma F_6637c : fetch_word AsanUbsan.M.loaded_segments (0x663c4 : word) = Some W_6637c.
Proof. vm_refl. Qed.
Lemma D_6637c : decode_any W_6637c = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66380 : bv 32 := 0x058cb503.
Lemma F_66380 : fetch_word AsanUbsan.M.loaded_segments (0x663c8 : word) = Some W_66380.
Proof. vm_refl. Qed.
Lemma D_66380 : decode_any W_66380 = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66384 : bv 32 := 0x00a00593.
Lemma F_66384 : fetch_word AsanUbsan.M.loaded_segments (0x663cc : word) = Some W_66384.
Proof. vm_refl. Qed.
Lemma D_66384 : decode_any W_66384 = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66388 : bv 32 := 0x414585bb.
Lemma F_66388 : fetch_word AsanUbsan.M.loaded_segments (0x663d0 : word) = Some W_66388.
Proof. vm_refl. Qed.
Lemma D_66388 : decode_any W_66388 = Some (Op32 ALU_SUB 11 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6638c : bv 32 := 0x006a0a93.
Lemma F_6638c : fetch_word AsanUbsan.M.loaded_segments (0x663d4 : word) = Some W_6638c.
Proof. vm_refl. Qed.
Lemma D_6638c : decode_any W_6638c = Some (OpImm ALU_ADD 21 20 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66390 : bv 32 := 0xfff00613.
Lemma F_66390 : fetch_word AsanUbsan.M.loaded_segments (0x663d8 : word) = Some W_66390.
Proof. vm_refl. Qed.
Lemma D_66390 : decode_any W_66390 = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66394 : bv 32 := 0x00b615b3.
Lemma F_66394 : fetch_word AsanUbsan.M.loaded_segments (0x663dc : word) = Some W_66394.
Proof. vm_refl. Qed.
Lemma D_66394 : decode_any W_66394 = Some (Op ALU_SLL 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66398 : bv 32 := 0x3ff5f593.
Lemma F_66398 : fetch_word AsanUbsan.M.loaded_segments (0x663e0 : word) = Some W_66398.
Proof. vm_refl. Qed.
Lemma D_66398 : decode_any W_66398 = Some (OpImm ALU_AND 11 11 1023, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6639c : bv 32 := 0xff150613.
Lemma F_6639c : fetch_word AsanUbsan.M.loaded_segments (0x663e4 : word) = Some W_6639c.
Proof. vm_refl. Qed.
Lemma D_6639c : decode_any W_6639c = Some (OpImm ALU_ADD 12 10 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663a0 : bv 32 := 0x414509b3.
Lemma F_663a0 : fetch_word AsanUbsan.M.loaded_segments (0x663e8 : word) = Some W_663a0.
Proof. vm_refl. Qed.
Lemma D_663a0 : decode_any W_663a0 = Some (Op ALU_SUB 19 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663a4 : bv 32 := 0x00c59c33.
Lemma F_663a4 : fetch_word AsanUbsan.M.loaded_segments (0x663ec : word) = Some W_663a4.
Proof. vm_refl. Qed.
Lemma D_663a4 : decode_any W_663a4 = Some (Op ALU_SLL 24 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663a8 : bv 32 := 0xffa98993.
Lemma F_663a8 : fetch_word AsanUbsan.M.loaded_segments (0x663f0 : word) = Some W_663a8.
Proof. vm_refl. Qed.
Lemma D_663a8 : decode_any W_663a8 = Some (OpImm ALU_ADD 19 19 4090, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663ac : bv 32 := 0x01840c33.
Lemma F_663ac : fetch_word AsanUbsan.M.loaded_segments (0x663f4 : word) = Some W_663ac.
Proof. vm_refl. Qed.
Lemma D_663ac : decode_any W_663ac = Some (Op ALU_ADD 24 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663b0 : bv 32 := 0x04000513.
Lemma F_663b0 : fetch_word AsanUbsan.M.loaded_segments (0x663f8 : word) = Some W_663b0.
Proof. vm_refl. Qed.
Lemma D_663b0 : decode_any W_663b0 = Some (OpImm ALU_ADD 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663b4 : bv 32 := 0x01451533.
Lemma F_663b4 : fetch_word AsanUbsan.M.loaded_segments (0x663fc : word) = Some W_663b4.
Proof. vm_refl. Qed.
Lemma D_663b4 : decode_any W_663b4 = Some (Op ALU_SLL 10 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663b8 : bv 32 := 0x02a13023.
Lemma F_663b8 : fetch_word AsanUbsan.M.loaded_segments (0x66400 : word) = Some W_663b8.
Proof. vm_refl. Qed.
Lemma D_663b8 : decode_any W_663b8 = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663bc : bv 32 := 0x0240006f.
Lemma F_663bc : fetch_word AsanUbsan.M.loaded_segments (0x66404 : word) = Some W_663bc.
Proof. vm_refl. Qed.
Lemma D_663bc : decode_any W_663bc = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663d4 : bv 32 := 0x001d8d93.
Lemma F_663d4 : fetch_word AsanUbsan.M.loaded_segments (0x6641c : word) = Some W_663d4.
Proof. vm_refl. Qed.
Lemma D_663d4 : decode_any W_663d4 = Some (OpImm ALU_ADD 27 27 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663d8 : bv 32 := 0x013dd533.
Lemma F_663d8 : fetch_word AsanUbsan.M.loaded_segments (0x66420 : word) = Some W_663d8.
Proof. vm_refl. Qed.
Lemma D_663d8 : decode_any W_663d8 = Some (Op ALU_SRL 10 27 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663dc : bv 32 := 0xf8051ae3.
Lemma F_663dc : fetch_word AsanUbsan.M.loaded_segments (0x66424 : word) = Some W_663dc.
Proof. vm_refl. Qed.
Lemma D_663dc : decode_any W_663dc = Some (Branch BC_NE 10 0 8084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663e0 : bv 32 := 0x01bc05b3.
Lemma F_663e0 : fetch_word AsanUbsan.M.loaded_segments (0x66428 : word) = Some W_663e0.
Proof. vm_refl. Qed.
Lemma D_663e0 : decode_any W_663e0 = Some (Op ALU_ADD 11 24 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663e4 : bv 32 := 0x0005c503.
Lemma F_663e4 : fetch_word AsanUbsan.M.loaded_segments (0x6642c : word) = Some W_663e4.
Proof. vm_refl. Qed.
Lemma D_663e4 : decode_any W_663e4 = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663e8 : bv 32 := 0xfe0506e3.
Lemma F_663e8 : fetch_word AsanUbsan.M.loaded_segments (0x66430 : word) = Some W_663e8.
Proof. vm_refl. Qed.
Lemma D_663e8 : decode_any W_663e8 = Some (Branch BC_EQ 10 0 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663ec : bv 32 := 0x058cb503.
Lemma F_663ec : fetch_word AsanUbsan.M.loaded_segments (0x66434 : word) = Some W_663ec.
Proof. vm_refl. Qed.
Lemma D_663ec : decode_any W_663ec = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663f0 : bv 32 := 0xffb50613.
Lemma F_663f0 : fetch_word AsanUbsan.M.loaded_segments (0x66438 : word) = Some W_663f0.
Proof. vm_refl. Qed.
Lemma D_663f0 : decode_any W_663f0 = Some (OpImm ALU_ADD 12 10 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663f4 : bv 32 := 0x00aa1533.
Lemma F_663f4 : fetch_word AsanUbsan.M.loaded_segments (0x6643c : word) = Some W_663f4.
Proof. vm_refl. Qed.
Lemma D_663f4 : decode_any W_663f4 = Some (Op ALU_SLL 10 20 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663f8 : bv 32 := 0x00c39633.
Lemma F_663f8 : fetch_word AsanUbsan.M.loaded_segments (0x66440 : word) = Some W_663f8.
Proof. vm_refl. Qed.
Lemma D_663f8 : decode_any W_663f8 = Some (Op ALU_SLL 12 7 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663fc : bv 32 := 0x00a40533.
Lemma F_663fc : fetch_word AsanUbsan.M.loaded_segments (0x66444 : word) = Some W_663fc.
Proof. vm_refl. Qed.
Lemma D_663fc : decode_any W_663fc = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66400 : bv 32 := 0x00c50533.
Lemma F_66400 : fetch_word AsanUbsan.M.loaded_segments (0x66448 : word) = Some W_66400.
Proof. vm_refl. Qed.
Lemma D_66400 : decode_any W_66400 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66404 : bv 32 := 0x015d9633.
Lemma F_66404 : fetch_word AsanUbsan.M.loaded_segments (0x6644c : word) = Some W_66404.
Proof. vm_refl. Qed.
Lemma D_66404 : decode_any W_66404 = Some (Op ALU_SLL 12 27 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66408 : bv 32 := 0x00c50533.
Lemma F_66408 : fetch_word AsanUbsan.M.loaded_segments (0x66450 : word) = Some W_66408.
Proof. vm_refl. Qed.
Lemma D_66408 : decode_any W_66408 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6640c : bv 32 := 0x01853603.
Lemma F_6640c : fetch_word AsanUbsan.M.loaded_segments (0x66454 : word) = Some W_6640c.
Proof. vm_refl. Qed.
Lemma D_6640c : decode_any W_6640c = Some (Load SZ8 true 12 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66410 : bv 32 := 0xfcc972e3.
Lemma F_66410 : fetch_word AsanUbsan.M.loaded_segments (0x66458 : word) = Some W_66410.
Proof. vm_refl. Qed.
Lemma D_66410 : decode_any W_66410 = Some (Branch BC_GEU 18 12 8132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66414 : bv 32 := 0xfc9670e3.
Lemma F_66414 : fetch_word AsanUbsan.M.loaded_segments (0x6645c : word) = Some W_66414.
Proof. vm_refl. Qed.
Lemma D_66414 : decode_any W_66414 = Some (Branch BC_GEU 12 9 8128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66418 : bv 32 := 0x01a58023.
Lemma F_66418 : fetch_word AsanUbsan.M.loaded_segments (0x66460 : word) = Some W_66418.
Proof. vm_refl. Qed.
Lemma D_66418 : decode_any W_66418 = Some (Store SZ1 11 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6641c : bv 32 := 0x000b3583.
Lemma F_6641c : fetch_word AsanUbsan.M.loaded_segments (0x66464 : word) = Some W_6641c.
Proof. vm_refl. Qed.
Lemma D_6641c : decode_any W_6641c = Some (Load SZ8 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66420 : bv 32 := 0xfff58613.
Lemma F_66420 : fetch_word AsanUbsan.M.loaded_segments (0x66468 : word) = Some W_66420.
Proof. vm_refl. Qed.
Lemma D_66420 : decode_any W_66420 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66424 : bv 32 := 0x00c5b6b3.
Lemma F_66424 : fetch_word AsanUbsan.M.loaded_segments (0x6646c : word) = Some W_66424.
Proof. vm_refl. Qed.
Lemma D_66424 : decode_any W_66424 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66428 : bv 32 := 0xfff68693.
Lemma F_66428 : fetch_word AsanUbsan.M.loaded_segments (0x66470 : word) = Some W_66428.
Proof. vm_refl. Qed.
Lemma D_66428 : decode_any W_66428 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6642c : bv 32 := 0x00c6f6b3.
Lemma F_6642c : fetch_word AsanUbsan.M.loaded_segments (0x66474 : word) = Some W_6642c.
Proof. vm_refl. Qed.
Lemma D_6642c : decode_any W_6642c = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66430 : bv 32 := 0x02a6fc63.
Lemma F_66430 : fetch_word AsanUbsan.M.loaded_segments (0x66478 : word) = Some W_66430.
Proof. vm_refl. Qed.
Lemma D_66430 : decode_any W_66430 = Some (Branch BC_GEU 13 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66434 : bv 32 := 0x01813683.
Lemma F_66434 : fetch_word AsanUbsan.M.loaded_segments (0x6647c : word) = Some W_66434.
Proof. vm_refl. Qed.
Lemma D_66434 : decode_any W_66434 = Some (Load SZ8 true 13 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66438 : bv 32 := 0x0006b803.
Lemma F_66438 : fetch_word AsanUbsan.M.loaded_segments (0x66480 : word) = Some W_66438.
Proof. vm_refl. Qed.
Lemma D_66438 : decode_any W_66438 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6643c : bv 32 := 0x01013683.
Lemma F_6643c : fetch_word AsanUbsan.M.loaded_segments (0x66484 : word) = Some W_6643c.
Proof. vm_refl. Qed.
Lemma D_6643c : decode_any W_6643c = Some (Load SZ8 true 13 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66440 : bv 32 := 0x0006b683.
Lemma F_66440 : fetch_word AsanUbsan.M.loaded_segments (0x66488 : word) = Some W_66440.
Proof. vm_refl. Qed.
Lemma D_66440 : decode_any W_66440 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66444 : bv 32 := 0xfff80793.
Lemma F_66444 : fetch_word AsanUbsan.M.loaded_segments (0x6648c : word) = Some W_66444.
Proof. vm_refl. Qed.
Lemma D_66444 : decode_any W_66444 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66448 : bv 32 := 0x00a7f463.
Lemma F_66448 : fetch_word AsanUbsan.M.loaded_segments (0x66490 : word) = Some W_66448.
Proof. vm_refl. Qed.
Lemma D_66448 : decode_any W_66448 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66450 : bv 32 := 0x00813703.
Lemma F_66450 : fetch_word AsanUbsan.M.loaded_segments (0x66498 : word) = Some W_66450.
Proof. vm_refl. Qed.
Lemma D_66450 : decode_any W_66450 = Some (Load SZ8 true 14 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66454 : bv 32 := 0x00073283.
Lemma F_66454 : fetch_word AsanUbsan.M.loaded_segments (0x6649c : word) = Some W_66454.
Proof. vm_refl. Qed.
Lemma D_66454 : decode_any W_66454 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66458 : bv 32 := 0x0032d713.
Lemma F_66458 : fetch_word AsanUbsan.M.loaded_segments (0x664a0 : word) = Some W_66458.
Proof. vm_refl. Qed.
Lemma D_66458 : decode_any W_66458 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6645c : bv 32 := 0x00b708b3.
Lemma F_6645c : fetch_word AsanUbsan.M.loaded_segments (0x664a4 : word) = Some W_6645c.
Proof. vm_refl. Qed.
Lemma D_6645c : decode_any W_6645c = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66460 : bv 32 := 0x02a2e863.
Lemma F_66460 : fetch_word AsanUbsan.M.loaded_segments (0x664a8 : word) = Some W_66460.
Proof. vm_refl. Qed.
Lemma D_66460 : decode_any W_66460 = Some (Branch BC_LTU 5 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66464 : bv 32 := 0x02a8f663.
Lemma F_66464 : fetch_word AsanUbsan.M.loaded_segments (0x664ac : word) = Some W_66464.
Proof. vm_refl. Qed.
Lemma D_66464 : decode_any W_66464 = Some (Branch BC_GEU 17 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66468 : bv 32 := 0xf54e6ce3.
Lemma F_66468 : fetch_word AsanUbsan.M.loaded_segments (0x664b0 : word) = Some W_66468.
Proof. vm_refl. Qed.
Lemma D_66468 : decode_any W_66468 = Some (Branch BC_LTU 28 20 8024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6646c : bv 32 := 0x00355513.
Lemma F_6646c : fetch_word AsanUbsan.M.loaded_segments (0x664b4 : word) = Some W_6646c.
Proof. vm_refl. Qed.
Lemma D_6646c : decode_any W_6646c = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66470 : bv 32 := 0x00a585b3.
Lemma F_66470 : fetch_word AsanUbsan.M.loaded_segments (0x664b8 : word) = Some W_66470.
Proof. vm_refl. Qed.
Lemma D_66470 : decode_any W_66470 = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66474 : bv 32 := 0x00100513.
Lemma F_66474 : fetch_word AsanUbsan.M.loaded_segments (0x664bc : word) = Some W_66474.
Proof. vm_refl. Qed.
Lemma D_66474 : decode_any W_66474 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66478 : bv 32 := 0x0175b023.
Lemma F_66478 : fetch_word AsanUbsan.M.loaded_segments (0x664c0 : word) = Some W_66478.
Proof. vm_refl. Qed.
Lemma D_66478 : decode_any W_66478 = Some (Store SZ8 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6647c : bv 32 := 0x01455633.
Lemma F_6647c : fetch_word AsanUbsan.M.loaded_segments (0x664c4 : word) = Some W_6647c.
Proof. vm_refl. Qed.
Lemma D_6647c : decode_any W_6647c = Some (Op ALU_SRL 12 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66480 : bv 32 := 0x00858593.
Lemma F_66480 : fetch_word AsanUbsan.M.loaded_segments (0x664c8 : word) = Some W_66480.
Proof. vm_refl. Qed.
Lemma D_66480 : decode_any W_66480 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66484 : bv 32 := 0x00150513.
Lemma F_66484 : fetch_word AsanUbsan.M.loaded_segments (0x664cc : word) = Some W_66484.
Proof. vm_refl. Qed.
Lemma D_66484 : decode_any W_66484 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66488 : bv 32 := 0xfe0608e3.
Lemma F_66488 : fetch_word AsanUbsan.M.loaded_segments (0x664d0 : word) = Some W_66488.
Proof. vm_refl. Qed.
Lemma D_66488 : decode_any W_66488 = Some (Branch BC_EQ 12 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6648c : bv 32 := 0xf49ff06f.
Lemma F_6648c : fetch_word AsanUbsan.M.loaded_segments (0x664d4 : word) = Some W_6648c.
Proof. vm_refl. Qed.
Lemma D_6648c : decode_any W_6648c = Some (Jal 0 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66554 : bv 32 := 0x060c8023.
Lemma F_66554 : fetch_word AsanUbsan.M.loaded_segments (0x6659c : word) = Some W_66554.
Proof. vm_refl. Qed.
Lemma D_66554 : decode_any W_66554 = Some (Store SZ1 25 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66558 : bv 32 := 0x08813083.
Lemma F_66558 : fetch_word AsanUbsan.M.loaded_segments (0x665a0 : word) = Some W_66558.
Proof. vm_refl. Qed.
Lemma D_66558 : decode_any W_66558 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6655c : bv 32 := 0x08013403.
Lemma F_6655c : fetch_word AsanUbsan.M.loaded_segments (0x665a4 : word) = Some W_6655c.
Proof. vm_refl. Qed.
Lemma D_6655c : decode_any W_6655c = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66560 : bv 32 := 0x07813483.
Lemma F_66560 : fetch_word AsanUbsan.M.loaded_segments (0x665a8 : word) = Some W_66560.
Proof. vm_refl. Qed.
Lemma D_66560 : decode_any W_66560 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66564 : bv 32 := 0x07013903.
Lemma F_66564 : fetch_word AsanUbsan.M.loaded_segments (0x665ac : word) = Some W_66564.
Proof. vm_refl. Qed.
Lemma D_66564 : decode_any W_66564 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66568 : bv 32 := 0x06813983.
Lemma F_66568 : fetch_word AsanUbsan.M.loaded_segments (0x665b0 : word) = Some W_66568.
Proof. vm_refl. Qed.
Lemma D_66568 : decode_any W_66568 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6656c : bv 32 := 0x06013a03.
Lemma F_6656c : fetch_word AsanUbsan.M.loaded_segments (0x665b4 : word) = Some W_6656c.
Proof. vm_refl. Qed.
Lemma D_6656c : decode_any W_6656c = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66570 : bv 32 := 0x05813a83.
Lemma F_66570 : fetch_word AsanUbsan.M.loaded_segments (0x665b8 : word) = Some W_66570.
Proof. vm_refl. Qed.
Lemma D_66570 : decode_any W_66570 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66574 : bv 32 := 0x05013b03.
Lemma F_66574 : fetch_word AsanUbsan.M.loaded_segments (0x665bc : word) = Some W_66574.
Proof. vm_refl. Qed.
Lemma D_66574 : decode_any W_66574 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66578 : bv 32 := 0x04813b83.
Lemma F_66578 : fetch_word AsanUbsan.M.loaded_segments (0x665c0 : word) = Some W_66578.
Proof. vm_refl. Qed.
Lemma D_66578 : decode_any W_66578 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6657c : bv 32 := 0x04013c03.
Lemma F_6657c : fetch_word AsanUbsan.M.loaded_segments (0x665c4 : word) = Some W_6657c.
Proof. vm_refl. Qed.
Lemma D_6657c : decode_any W_6657c = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66580 : bv 32 := 0x03813c83.
Lemma F_66580 : fetch_word AsanUbsan.M.loaded_segments (0x665c8 : word) = Some W_66580.
Proof. vm_refl. Qed.
Lemma D_66580 : decode_any W_66580 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66584 : bv 32 := 0x03013d03.
Lemma F_66584 : fetch_word AsanUbsan.M.loaded_segments (0x665cc : word) = Some W_66584.
Proof. vm_refl. Qed.
Lemma D_66584 : decode_any W_66584 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66588 : bv 32 := 0x02813d83.
Lemma F_66588 : fetch_word AsanUbsan.M.loaded_segments (0x665d0 : word) = Some W_66588.
Proof. vm_refl. Qed.
Lemma D_66588 : decode_any W_66588 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6658c : bv 32 := 0x09010113.
Lemma F_6658c : fetch_word AsanUbsan.M.loaded_segments (0x665d4 : word) = Some W_6658c.
Proof. vm_refl. Qed.
Lemma D_6658c : decode_any W_6658c = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66590 : bv 32 := 0x00008067.
Lemma F_66590 : fetch_word AsanUbsan.M.loaded_segments (0x665d8 : word) = Some W_66590.
Proof. vm_refl. Qed.
Lemma D_66590 : decode_any W_66590 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66594 : bv 32 := 0x00100593.
Lemma F_66594 : fetch_word AsanUbsan.M.loaded_segments (0x665dc : word) = Some W_66594.
Proof. vm_refl. Qed.
Lemma D_66594 : decode_any W_66594 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66598 : bv 32 := 0x06b50023.
Lemma F_66598 : fetch_word AsanUbsan.M.loaded_segments (0x665e0 : word) = Some W_66598.
Proof. vm_refl. Qed.
Lemma D_66598 : decode_any W_66598 = Some (Store SZ1 10 11 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6659c : bv 32 := 0x00008067.
Lemma F_6659c : fetch_word AsanUbsan.M.loaded_segments (0x665e4 : word) = Some W_6659c.
Proof. vm_refl. Qed.
Lemma D_6659c : decode_any W_6659c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666f8 : bv 32 := 0xfe010113.
Lemma F_666f8 : fetch_word AsanUbsan.M.loaded_segments (0x66740 : word) = Some W_666f8.
Proof. vm_refl. Qed.
Lemma D_666f8 : decode_any W_666f8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666fc : bv 32 := 0x00113c23.
Lemma F_666fc : fetch_word AsanUbsan.M.loaded_segments (0x66744 : word) = Some W_666fc.
Proof. vm_refl. Qed.
Lemma D_666fc : decode_any W_666fc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66700 : bv 32 := 0x00813823.
Lemma F_66700 : fetch_word AsanUbsan.M.loaded_segments (0x66748 : word) = Some W_66700.
Proof. vm_refl. Qed.
Lemma D_66700 : decode_any W_66700 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66704 : bv 32 := 0x00913423.
Lemma F_66704 : fetch_word AsanUbsan.M.loaded_segments (0x6674c : word) = Some W_66704.
Proof. vm_refl. Qed.
Lemma D_66704 : decode_any W_66704 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66708 : bv 32 := 0x01213023.
Lemma F_66708 : fetch_word AsanUbsan.M.loaded_segments (0x66750 : word) = Some W_66708.
Proof. vm_refl. Qed.
Lemma D_66708 : decode_any W_66708 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6670c : bv 32 := 0x02010413.
Lemma F_6670c : fetch_word AsanUbsan.M.loaded_segments (0x66754 : word) = Some W_6670c.
Proof. vm_refl. Qed.
Lemma D_6670c : decode_any W_6670c = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66710 : bv 32 := 0x000ff517.
Lemma F_66710 : fetch_word AsanUbsan.M.loaded_segments (0x66758 : word) = Some W_66710.
Proof. vm_refl. Qed.
Lemma D_66710 : decode_any W_66710 = Some (Auipc 10 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66714 : bv 32 := 0xbe050513.
Lemma F_66714 : fetch_word AsanUbsan.M.loaded_segments (0x6675c : word) = Some W_66714.
Proof. vm_refl. Qed.
Lemma D_66714 : decode_any W_66714 = Some (OpImm ALU_ADD 10 10 3040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66718 : bv 32 := 0x30d050ef.
Lemma F_66718 : fetch_word AsanUbsan.M.loaded_segments (0x66760 : word) = Some W_66718.
Proof. vm_refl. Qed.
Lemma D_66718 : decode_any W_66718 = Some (Jal 1 23308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6671c : bv 32 := 0x00053483.
Lemma F_6671c : fetch_word AsanUbsan.M.loaded_segments (0x66764 : word) = Some W_6671c.
Proof. vm_refl. Qed.
Lemma D_6671c : decode_any W_6671c = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66720 : bv 32 := 0x08048063.
Lemma F_66720 : fetch_word AsanUbsan.M.loaded_segments (0x66768 : word) = Some W_66720.
Proof. vm_refl. Qed.
Lemma D_66720 : decode_any W_66720 = Some (Branch BC_EQ 9 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66724 : bv 32 := 0x0604c503.
Lemma F_66724 : fetch_word AsanUbsan.M.loaded_segments (0x6676c : word) = Some W_66724.
Proof. vm_refl. Qed.
Lemma D_66724 : decode_any W_66724 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66728 : bv 32 := 0x0584b903.
Lemma F_66728 : fetch_word AsanUbsan.M.loaded_segments (0x66770 : word) = Some W_66728.
Proof. vm_refl. Qed.
Lemma D_66728 : decode_any W_66728 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6672c : bv 32 := 0x00050863.
Lemma F_6672c : fetch_word AsanUbsan.M.loaded_segments (0x66774 : word) = Some W_6672c.
Proof. vm_refl. Qed.
Lemma D_6672c : decode_any W_6672c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66730 : bv 32 := 0x00048513.
Lemma F_66730 : fetch_word AsanUbsan.M.loaded_segments (0x66778 : word) = Some W_66730.
Proof. vm_refl. Qed.
Lemma D_66730 : decode_any W_66730 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66734 : bv 32 := 0x00040593.
Lemma F_66734 : fetch_word AsanUbsan.M.loaded_segments (0x6677c : word) = Some W_66734.
Proof. vm_refl. Qed.
Lemma D_66734 : decode_any W_66734 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66738 : bv 32 := 0xb75ff0ef.
Lemma F_66738 : fetch_word AsanUbsan.M.loaded_segments (0x66780 : word) = Some W_66738.
Proof. vm_refl. Qed.
Lemma D_66738 : decode_any W_66738 = Some (Jal 1 2095988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6673c : bv 32 := 0xffa90593.
Lemma F_6673c : fetch_word AsanUbsan.M.loaded_segments (0x66784 : word) = Some W_6673c.
Proof. vm_refl. Qed.
Lemma D_6673c : decode_any W_6673c = Some (OpImm ALU_ADD 11 18 4090, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66740 : bv 32 := 0x00100513.
Lemma F_66740 : fetch_word AsanUbsan.M.loaded_segments (0x66788 : word) = Some W_66740.
Proof. vm_refl. Qed.
Lemma D_66740 : decode_any W_66740 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66744 : bv 32 := 0x00b51533.
Lemma F_66744 : fetch_word AsanUbsan.M.loaded_segments (0x6678c : word) = Some W_66744.
Proof. vm_refl. Qed.
Lemma D_66744 : decode_any W_66744 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66748 : bv 32 := 0x0005061b.
Lemma F_66748 : fetch_word AsanUbsan.M.loaded_segments (0x66790 : word) = Some W_66748.
Proof. vm_refl. Qed.
Lemma D_66748 : decode_any W_66748 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6674c : bv 32 := 0x06c05a63.
Lemma F_6674c : fetch_word AsanUbsan.M.loaded_segments (0x66794 : word) = Some W_6674c.
Proof. vm_refl. Qed.
Lemma D_6674c : decode_any W_6674c = Some (Branch BC_GE 0 12 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66750 : bv 32 := 0x000016b7.
Lemma F_66750 : fetch_word AsanUbsan.M.loaded_segments (0x66798 : word) = Some W_66750.
Proof. vm_refl. Qed.
Lemma D_66750 : decode_any W_66750 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66754 : bv 32 := 0xfff00713.
Lemma F_66754 : fetch_word AsanUbsan.M.loaded_segments (0x6679c : word) = Some W_66754.
Proof. vm_refl. Qed.
Lemma D_66754 : decode_any W_66754 = Some (OpImm ALU_ADD 14 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66758 : bv 32 := 0x0004b603.
Lemma F_66758 : fetch_word AsanUbsan.M.loaded_segments (0x667a0 : word) = Some W_66758.
Proof. vm_refl. Qed.
Lemma D_66758 : decode_any W_66758 = Some (Load SZ8 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6675c : bv 32 := 0x00b71733.
Lemma F_6675c : fetch_word AsanUbsan.M.loaded_segments (0x667a4 : word) = Some W_6675c.
Proof. vm_refl. Qed.
Lemma D_6675c : decode_any W_6675c = Some (Op ALU_SLL 14 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66760 : bv 32 := 0xfff50793.
Lemma F_66760 : fetch_word AsanUbsan.M.loaded_segments (0x667a8 : word) = Some W_66760.
Proof. vm_refl. Qed.
Lemma D_66760 : decode_any W_66760 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66764 : bv 32 := 0x00d485b3.
Lemma F_66764 : fetch_word AsanUbsan.M.loaded_segments (0x667ac : word) = Some W_66764.
Proof. vm_refl. Qed.
Lemma D_66764 : decode_any W_66764 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66768 : bv 32 := 0xfff74693.
Lemma F_66768 : fetch_word AsanUbsan.M.loaded_segments (0x667b0 : word) = Some W_66768.
Proof. vm_refl. Qed.
Lemma D_66768 : decode_any W_66768 = Some (OpImm ALU_XOR 13 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6676c : bv 32 := 0x02079793.
Lemma F_6676c : fetch_word AsanUbsan.M.loaded_segments (0x667b4 : word) = Some W_6676c.
Proof. vm_refl. Qed.
Lemma D_6676c : decode_any W_6676c = Some (ShiftImm ALU_SLL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66770 : bv 32 := 0x0207d793.
Lemma F_66770 : fetch_word AsanUbsan.M.loaded_segments (0x667b8 : word) = Some W_66770.
Proof. vm_refl. Qed.
Lemma D_66770 : decode_any W_66770 = Some (ShiftImm ALU_SRL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66774 : bv 32 := 0x00f60733.
Lemma F_66774 : fetch_word AsanUbsan.M.loaded_segments (0x667bc : word) = Some W_66774.
Proof. vm_refl. Qed.
Lemma D_66774 : decode_any W_66774 = Some (Op ALU_ADD 14 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66778 : bv 32 := 0x00170713.
Lemma F_66778 : fetch_word AsanUbsan.M.loaded_segments (0x667c0 : word) = Some W_66778.
Proof. vm_refl. Qed.
Lemma D_66778 : decode_any W_66778 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6677c : bv 32 := 0x00d67833.
Lemma F_6677c : fetch_word AsanUbsan.M.loaded_segments (0x667c4 : word) = Some W_6677c.
Proof. vm_refl. Qed.
Lemma D_6677c : decode_any W_6677c = Some (Op ALU_AND 16 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66780 : bv 32 := 0x010587b3.
Lemma F_66780 : fetch_word AsanUbsan.M.loaded_segments (0x667c8 : word) = Some W_66780.
Proof. vm_refl. Qed.
Lemma D_66780 : decode_any W_66780 = Some (Op ALU_ADD 15 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66784 : bv 32 := 0x0007c883.
Lemma F_66784 : fetch_word AsanUbsan.M.loaded_segments (0x667cc : word) = Some W_66784.
Proof. vm_refl. Qed.
Lemma D_66784 : decode_any W_66784 = Some (Load SZ1 false 17 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66788 : bv 32 := 0x06088663.
Lemma F_66788 : fetch_word AsanUbsan.M.loaded_segments (0x667d0 : word) = Some W_66788.
Proof. vm_refl. Qed.
Lemma D_66788 : decode_any W_66788 = Some (Branch BC_EQ 17 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6678c : bv 32 := 0xfff5051b.
Lemma F_6678c : fetch_word AsanUbsan.M.loaded_segments (0x667d4 : word) = Some W_6678c.
Proof. vm_refl. Qed.
Lemma D_6678c : decode_any W_6678c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66790 : bv 32 := 0x00160613.
Lemma F_66790 : fetch_word AsanUbsan.M.loaded_segments (0x667d8 : word) = Some W_66790.
Proof. vm_refl. Qed.
Lemma D_66790 : decode_any W_66790 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66794 : bv 32 := 0xfe0514e3.
Lemma F_66794 : fetch_word AsanUbsan.M.loaded_segments (0x667dc : word) = Some W_66794.
Proof. vm_refl. Qed.
Lemma D_66794 : decode_any W_66794 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667f4 : bv 32 := 0x00160613.
Lemma F_667f4 : fetch_word AsanUbsan.M.loaded_segments (0x6683c : word) = Some W_667f4.
Proof. vm_refl. Qed.
Lemma D_667f4 : decode_any W_667f4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667f8 : bv 32 := 0x00100513.
Lemma F_667f8 : fetch_word AsanUbsan.M.loaded_segments (0x66840 : word) = Some W_667f8.
Proof. vm_refl. Qed.
Lemma D_667f8 : decode_any W_667f8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667fc : bv 32 := 0xffb90913.
Lemma F_667fc : fetch_word AsanUbsan.M.loaded_segments (0x66844 : word) = Some W_667fc.
Proof. vm_refl. Qed.
Lemma D_667fc : decode_any W_667fc = Some (OpImm ALU_ADD 18 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66800 : bv 32 := 0x00681813.
Lemma F_66800 : fetch_word AsanUbsan.M.loaded_segments (0x66848 : word) = Some W_66800.
Proof. vm_refl. Qed.
Lemma D_66800 : decode_any W_66800 = Some (ShiftImm ALU_SLL 16 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66804 : bv 32 := 0x00c4b023.
Lemma F_66804 : fetch_word AsanUbsan.M.loaded_segments (0x6684c : word) = Some W_66804.
Proof. vm_refl. Qed.
Lemma D_66804 : decode_any W_66804 = Some (Store SZ8 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66808 : bv 32 := 0x00a78023.
Lemma F_66808 : fetch_word AsanUbsan.M.loaded_segments (0x66850 : word) = Some W_66808.
Proof. vm_refl. Qed.
Lemma D_66808 : decode_any W_66808 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6680c : bv 32 := 0x01251533.
Lemma F_6680c : fetch_word AsanUbsan.M.loaded_segments (0x66854 : word) = Some W_6680c.
Proof. vm_refl. Qed.
Lemma D_6680c : decode_any W_6680c = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66810 : bv 32 := 0x00a58533.
Lemma F_66810 : fetch_word AsanUbsan.M.loaded_segments (0x66858 : word) = Some W_66810.
Proof. vm_refl. Qed.
Lemma D_66810 : decode_any W_66810 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66814 : bv 32 := 0x010504b3.
Lemma F_66814 : fetch_word AsanUbsan.M.loaded_segments (0x6685c : word) = Some W_66814.
Proof. vm_refl. Qed.
Lemma D_66814 : decode_any W_66814 = Some (Op ALU_ADD 9 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66818 : bv 32 := 0x0084bc23.
Lemma F_66818 : fetch_word AsanUbsan.M.loaded_segments (0x66860 : word) = Some W_66818.
Proof. vm_refl. Qed.
Lemma D_66818 : decode_any W_66818 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6681c : bv 32 := 0x02f4bc23.
Lemma F_6681c : fetch_word AsanUbsan.M.loaded_segments (0x66864 : word) = Some W_6681c.
Proof. vm_refl. Qed.
Lemma D_6681c : decode_any W_6681c = Some (Store SZ8 9 15 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66820 : bv 32 := 0x00048513.
Lemma F_66820 : fetch_word AsanUbsan.M.loaded_segments (0x66868 : word) = Some W_66820.
Proof. vm_refl. Qed.
Lemma D_66820 : decode_any W_66820 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66824 : bv 32 := 0x1ad000ef.
Lemma F_66824 : fetch_word AsanUbsan.M.loaded_segments (0x6686c : word) = Some W_66824.
Proof. vm_refl. Qed.
Lemma D_66824 : decode_any W_66824 = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66828 : bv 32 := 0x00050593.
Lemma F_66828 : fetch_word AsanUbsan.M.loaded_segments (0x66870 : word) = Some W_66828.
Proof. vm_refl. Qed.
Lemma D_66828 : decode_any W_66828 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6682c : bv 32 := 0x00048513.
Lemma F_6682c : fetch_word AsanUbsan.M.loaded_segments (0x66874 : word) = Some W_6682c.
Proof. vm_refl. Qed.
Lemma D_6682c : decode_any W_6682c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66830 : bv 32 := 0x00000613.
Lemma F_66830 : fetch_word AsanUbsan.M.loaded_segments (0x66878 : word) = Some W_66830.
Proof. vm_refl. Qed.
Lemma D_66830 : decode_any W_66830 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66834 : bv 32 := 0x0005b023.
Lemma F_66834 : fetch_word AsanUbsan.M.loaded_segments (0x6687c : word) = Some W_66834.
Proof. vm_refl. Qed.
Lemma D_66834 : decode_any W_66834 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66838 : bv 32 := 0x01813083.
Lemma F_66838 : fetch_word AsanUbsan.M.loaded_segments (0x66880 : word) = Some W_66838.
Proof. vm_refl. Qed.
Lemma D_66838 : decode_any W_66838 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6683c : bv 32 := 0x01013403.
Lemma F_6683c : fetch_word AsanUbsan.M.loaded_segments (0x66884 : word) = Some W_6683c.
Proof. vm_refl. Qed.
Lemma D_6683c : decode_any W_6683c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66840 : bv 32 := 0x00813483.
Lemma F_66840 : fetch_word AsanUbsan.M.loaded_segments (0x66888 : word) = Some W_66840.
Proof. vm_refl. Qed.
Lemma D_66840 : decode_any W_66840 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66844 : bv 32 := 0x00013903.
Lemma F_66844 : fetch_word AsanUbsan.M.loaded_segments (0x6688c : word) = Some W_66844.
Proof. vm_refl. Qed.
Lemma D_66844 : decode_any W_66844 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66848 : bv 32 := 0x02010113.
Lemma F_66848 : fetch_word AsanUbsan.M.loaded_segments (0x66890 : word) = Some W_66848.
Proof. vm_refl. Qed.
Lemma D_66848 : decode_any W_66848 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6684c : bv 32 := 0x00008067.
Lemma F_6684c : fetch_word AsanUbsan.M.loaded_segments (0x66894 : word) = Some W_6684c.
Proof. vm_refl. Qed.
Lemma D_6684c : decode_any W_6684c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6686c : bv 32 := 0xfe010113.
Lemma F_6686c : fetch_word AsanUbsan.M.loaded_segments (0x668b4 : word) = Some W_6686c.
Proof. vm_refl. Qed.
Lemma D_6686c : decode_any W_6686c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66870 : bv 32 := 0x00113c23.
Lemma F_66870 : fetch_word AsanUbsan.M.loaded_segments (0x668b8 : word) = Some W_66870.
Proof. vm_refl. Qed.
Lemma D_66870 : decode_any W_66870 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66874 : bv 32 := 0x00813823.
Lemma F_66874 : fetch_word AsanUbsan.M.loaded_segments (0x668bc : word) = Some W_66874.
Proof. vm_refl. Qed.
Lemma D_66874 : decode_any W_66874 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66878 : bv 32 := 0x00913423.
Lemma F_66878 : fetch_word AsanUbsan.M.loaded_segments (0x668c0 : word) = Some W_66878.
Proof. vm_refl. Qed.
Lemma D_66878 : decode_any W_66878 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6687c : bv 32 := 0x01213023.
Lemma F_6687c : fetch_word AsanUbsan.M.loaded_segments (0x668c4 : word) = Some W_6687c.
Proof. vm_refl. Qed.
Lemma D_6687c : decode_any W_6687c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66880 : bv 32 := 0x02010413.
Lemma F_66880 : fetch_word AsanUbsan.M.loaded_segments (0x668c8 : word) = Some W_66880.
Proof. vm_refl. Qed.
Lemma D_66880 : decode_any W_66880 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66884 : bv 32 := 0x000ff517.
Lemma F_66884 : fetch_word AsanUbsan.M.loaded_segments (0x668cc : word) = Some W_66884.
Proof. vm_refl. Qed.
Lemma D_66884 : decode_any W_66884 = Some (Auipc 10 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66888 : bv 32 := 0xa6c50513.
Lemma F_66888 : fetch_word AsanUbsan.M.loaded_segments (0x668d0 : word) = Some W_66888.
Proof. vm_refl. Qed.
Lemma D_66888 : decode_any W_66888 = Some (OpImm ALU_ADD 10 10 2668, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6688c : bv 32 := 0x199050ef.
Lemma F_6688c : fetch_word AsanUbsan.M.loaded_segments (0x668d4 : word) = Some W_6688c.
Proof. vm_refl. Qed.
Lemma D_6688c : decode_any W_6688c = Some (Jal 1 22936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66890 : bv 32 := 0x00053483.
Lemma F_66890 : fetch_word AsanUbsan.M.loaded_segments (0x668d8 : word) = Some W_66890.
Proof. vm_refl. Qed.
Lemma D_66890 : decode_any W_66890 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66894 : bv 32 := 0x08048863.
Lemma F_66894 : fetch_word AsanUbsan.M.loaded_segments (0x668dc : word) = Some W_66894.
Proof. vm_refl. Qed.
Lemma D_66894 : decode_any W_66894 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66898 : bv 32 := 0x0604c503.
Lemma F_66898 : fetch_word AsanUbsan.M.loaded_segments (0x668e0 : word) = Some W_66898.
Proof. vm_refl. Qed.
Lemma D_66898 : decode_any W_66898 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6689c : bv 32 := 0x0584b903.
Lemma F_6689c : fetch_word AsanUbsan.M.loaded_segments (0x668e4 : word) = Some W_6689c.
Proof. vm_refl. Qed.
Lemma D_6689c : decode_any W_6689c = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668a0 : bv 32 := 0x00050863.
Lemma F_668a0 : fetch_word AsanUbsan.M.loaded_segments (0x668e8 : word) = Some W_668a0.
Proof. vm_refl. Qed.
Lemma D_668a0 : decode_any W_668a0 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668a4 : bv 32 := 0x00048513.
Lemma F_668a4 : fetch_word AsanUbsan.M.loaded_segments (0x668ec : word) = Some W_668a4.
Proof. vm_refl. Qed.
Lemma D_668a4 : decode_any W_668a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668a8 : bv 32 := 0x00040593.
Lemma F_668a8 : fetch_word AsanUbsan.M.loaded_segments (0x668f0 : word) = Some W_668a8.
Proof. vm_refl. Qed.
Lemma D_668a8 : decode_any W_668a8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668ac : bv 32 := 0xa01ff0ef.
Lemma F_668ac : fetch_word AsanUbsan.M.loaded_segments (0x668f4 : word) = Some W_668ac.
Proof. vm_refl. Qed.
Lemma D_668ac : decode_any W_668ac = Some (Jal 1 2095616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668b0 : bv 32 := 0xff990593.
Lemma F_668b0 : fetch_word AsanUbsan.M.loaded_segments (0x668f8 : word) = Some W_668b0.
Proof. vm_refl. Qed.
Lemma D_668b0 : decode_any W_668b0 = Some (OpImm ALU_ADD 11 18 4089, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668b4 : bv 32 := 0x00100513.
Lemma F_668b4 : fetch_word AsanUbsan.M.loaded_segments (0x668fc : word) = Some W_668b4.
Proof. vm_refl. Qed.
Lemma D_668b4 : decode_any W_668b4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668b8 : bv 32 := 0x00b51533.
Lemma F_668b8 : fetch_word AsanUbsan.M.loaded_segments (0x66900 : word) = Some W_668b8.
Proof. vm_refl. Qed.
Lemma D_668b8 : decode_any W_668b8 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668bc : bv 32 := 0x0005061b.
Lemma F_668bc : fetch_word AsanUbsan.M.loaded_segments (0x66904 : word) = Some W_668bc.
Proof. vm_refl. Qed.
Lemma D_668bc : decode_any W_668bc = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668c0 : bv 32 := 0x08c05263.
Lemma F_668c0 : fetch_word AsanUbsan.M.loaded_segments (0x66908 : word) = Some W_668c0.
Proof. vm_refl. Qed.
Lemma D_668c0 : decode_any W_668c0 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668c4 : bv 32 := 0x000016b7.
Lemma F_668c4 : fetch_word AsanUbsan.M.loaded_segments (0x6690c : word) = Some W_668c4.
Proof. vm_refl. Qed.
Lemma D_668c4 : decode_any W_668c4 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668c8 : bv 32 := 0xff190613.
Lemma F_668c8 : fetch_word AsanUbsan.M.loaded_segments (0x66910 : word) = Some W_668c8.
Proof. vm_refl. Qed.
Lemma D_668c8 : decode_any W_668c8 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668cc : bv 32 := 0x20000713.
Lemma F_668cc : fetch_word AsanUbsan.M.loaded_segments (0x66914 : word) = Some W_668cc.
Proof. vm_refl. Qed.
Lemma D_668cc : decode_any W_668cc = Some (OpImm ALU_ADD 14 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668d0 : bv 32 := 0xfff00793.
Lemma F_668d0 : fetch_word AsanUbsan.M.loaded_segments (0x66918 : word) = Some W_668d0.
Proof. vm_refl. Qed.
Lemma D_668d0 : decode_any W_668d0 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668d4 : bv 32 := 0x00c71733.
Lemma F_668d4 : fetch_word AsanUbsan.M.loaded_segments (0x6691c : word) = Some W_668d4.
Proof. vm_refl. Qed.
Lemma D_668d4 : decode_any W_668d4 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668d8 : bv 32 := 0x0084b603.
Lemma F_668d8 : fetch_word AsanUbsan.M.loaded_segments (0x66920 : word) = Some W_668d8.
Proof. vm_refl. Qed.
Lemma D_668d8 : decode_any W_668d8 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668dc : bv 32 := 0x00b797b3.
Lemma F_668dc : fetch_word AsanUbsan.M.loaded_segments (0x66924 : word) = Some W_668dc.
Proof. vm_refl. Qed.
Lemma D_668dc : decode_any W_668dc = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668e0 : bv 32 := 0xfff50813.
Lemma F_668e0 : fetch_word AsanUbsan.M.loaded_segments (0x66928 : word) = Some W_668e0.
Proof. vm_refl. Qed.
Lemma D_668e0 : decode_any W_668e0 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668e4 : bv 32 := 0x00d485b3.
Lemma F_668e4 : fetch_word AsanUbsan.M.loaded_segments (0x6692c : word) = Some W_668e4.
Proof. vm_refl. Qed.
Lemma D_668e4 : decode_any W_668e4 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668e8 : bv 32 := 0x00e586b3.
Lemma F_668e8 : fetch_word AsanUbsan.M.loaded_segments (0x66930 : word) = Some W_668e8.
Proof. vm_refl. Qed.
Lemma D_668e8 : decode_any W_668e8 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668ec : bv 32 := 0xfff7c713.
Lemma F_668ec : fetch_word AsanUbsan.M.loaded_segments (0x66934 : word) = Some W_668ec.
Proof. vm_refl. Qed.
Lemma D_668ec : decode_any W_668ec = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668f0 : bv 32 := 0x02081813.
Lemma F_668f0 : fetch_word AsanUbsan.M.loaded_segments (0x66938 : word) = Some W_668f0.
Proof. vm_refl. Qed.
Lemma D_668f0 : decode_any W_668f0 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668f4 : bv 32 := 0x02085793.
Lemma F_668f4 : fetch_word AsanUbsan.M.loaded_segments (0x6693c : word) = Some W_668f4.
Proof. vm_refl. Qed.
Lemma D_668f4 : decode_any W_668f4 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668f8 : bv 32 := 0x00f607b3.
Lemma F_668f8 : fetch_word AsanUbsan.M.loaded_segments (0x66940 : word) = Some W_668f8.
Proof. vm_refl. Qed.
Lemma D_668f8 : decode_any W_668f8 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668fc : bv 32 := 0x00178813.
Lemma F_668fc : fetch_word AsanUbsan.M.loaded_segments (0x66944 : word) = Some W_668fc.
Proof. vm_refl. Qed.
Lemma D_668fc : decode_any W_668fc = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66900 : bv 32 := 0x00e678b3.
Lemma F_66900 : fetch_word AsanUbsan.M.loaded_segments (0x66948 : word) = Some W_66900.
Proof. vm_refl. Qed.
Lemma D_66900 : decode_any W_66900 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66904 : bv 32 := 0x011687b3.
Lemma F_66904 : fetch_word AsanUbsan.M.loaded_segments (0x6694c : word) = Some W_66904.
Proof. vm_refl. Qed.
Lemma D_66904 : decode_any W_66904 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66908 : bv 32 := 0x0007c283.
Lemma F_66908 : fetch_word AsanUbsan.M.loaded_segments (0x66950 : word) = Some W_66908.
Proof. vm_refl. Qed.
Lemma D_66908 : decode_any W_66908 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6690c : bv 32 := 0x06028663.
Lemma F_6690c : fetch_word AsanUbsan.M.loaded_segments (0x66954 : word) = Some W_6690c.
Proof. vm_refl. Qed.
Lemma D_6690c : decode_any W_6690c = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66910 : bv 32 := 0xfff5051b.
Lemma F_66910 : fetch_word AsanUbsan.M.loaded_segments (0x66958 : word) = Some W_66910.
Proof. vm_refl. Qed.
Lemma D_66910 : decode_any W_66910 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66914 : bv 32 := 0x00160613.
Lemma F_66914 : fetch_word AsanUbsan.M.loaded_segments (0x6695c : word) = Some W_66914.
Proof. vm_refl. Qed.
Lemma D_66914 : decode_any W_66914 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66918 : bv 32 := 0xfe0514e3.
Lemma F_66918 : fetch_word AsanUbsan.M.loaded_segments (0x66960 : word) = Some W_66918.
Proof. vm_refl. Qed.
Lemma D_66918 : decode_any W_66918 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66978 : bv 32 := 0x00160613.
Lemma F_66978 : fetch_word AsanUbsan.M.loaded_segments (0x669c0 : word) = Some W_66978.
Proof. vm_refl. Qed.
Lemma D_66978 : decode_any W_66978 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6697c : bv 32 := 0x00100513.
Lemma F_6697c : fetch_word AsanUbsan.M.loaded_segments (0x669c4 : word) = Some W_6697c.
Proof. vm_refl. Qed.
Lemma D_6697c : decode_any W_6697c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66980 : bv 32 := 0xffb90693.
Lemma F_66980 : fetch_word AsanUbsan.M.loaded_segments (0x669c8 : word) = Some W_66980.
Proof. vm_refl. Qed.
Lemma D_66980 : decode_any W_66980 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66984 : bv 32 := 0x00789893.
Lemma F_66984 : fetch_word AsanUbsan.M.loaded_segments (0x669cc : word) = Some W_66984.
Proof. vm_refl. Qed.
Lemma D_66984 : decode_any W_66984 = Some (ShiftImm ALU_SLL 17 17 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66988 : bv 32 := 0x00c4b423.
Lemma F_66988 : fetch_word AsanUbsan.M.loaded_segments (0x669d0 : word) = Some W_66988.
Proof. vm_refl. Qed.
Lemma D_66988 : decode_any W_66988 = Some (Store SZ8 9 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6698c : bv 32 := 0x00a78023.
Lemma F_6698c : fetch_word AsanUbsan.M.loaded_segments (0x669d4 : word) = Some W_6698c.
Proof. vm_refl. Qed.
Lemma D_6698c : decode_any W_6698c = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66990 : bv 32 := 0x00d51633.
Lemma F_66990 : fetch_word AsanUbsan.M.loaded_segments (0x669d8 : word) = Some W_66990.
Proof. vm_refl. Qed.
Lemma D_66990 : decode_any W_66990 = Some (Op ALU_SLL 12 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66994 : bv 32 := 0x01251533.
Lemma F_66994 : fetch_word AsanUbsan.M.loaded_segments (0x669dc : word) = Some W_66994.
Proof. vm_refl. Qed.
Lemma D_66994 : decode_any W_66994 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66998 : bv 32 := 0x00c585b3.
Lemma F_66998 : fetch_word AsanUbsan.M.loaded_segments (0x669e0 : word) = Some W_66998.
Proof. vm_refl. Qed.
Lemma D_66998 : decode_any W_66998 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6699c : bv 32 := 0x01150533.
Lemma F_6699c : fetch_word AsanUbsan.M.loaded_segments (0x669e4 : word) = Some W_6699c.
Proof. vm_refl. Qed.
Lemma D_6699c : decode_any W_6699c = Some (Op ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669a0 : bv 32 := 0x00a584b3.
Lemma F_669a0 : fetch_word AsanUbsan.M.loaded_segments (0x669e8 : word) = Some W_669a0.
Proof. vm_refl. Qed.
Lemma D_669a0 : decode_any W_669a0 = Some (Op ALU_ADD 9 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669a4 : bv 32 := 0x0084bc23.
Lemma F_669a4 : fetch_word AsanUbsan.M.loaded_segments (0x669ec : word) = Some W_669a4.
Proof. vm_refl. Qed.
Lemma D_669a4 : decode_any W_669a4 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669a8 : bv 32 := 0x06f4bc23.
Lemma F_669a8 : fetch_word AsanUbsan.M.loaded_segments (0x669f0 : word) = Some W_669a8.
Proof. vm_refl. Qed.
Lemma D_669a8 : decode_any W_669a8 = Some (Store SZ8 9 15 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669ac : bv 32 := 0x00048513.
Lemma F_669ac : fetch_word AsanUbsan.M.loaded_segments (0x669f4 : word) = Some W_669ac.
Proof. vm_refl. Qed.
Lemma D_669ac : decode_any W_669ac = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669b0 : bv 32 := 0x021000ef.
Lemma F_669b0 : fetch_word AsanUbsan.M.loaded_segments (0x669f8 : word) = Some W_669b0.
Proof. vm_refl. Qed.
Lemma D_669b0 : decode_any W_669b0 = Some (Jal 1 2080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669b4 : bv 32 := 0x00050593.
Lemma F_669b4 : fetch_word AsanUbsan.M.loaded_segments (0x669fc : word) = Some W_669b4.
Proof. vm_refl. Qed.
Lemma D_669b4 : decode_any W_669b4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669b8 : bv 32 := 0x00048513.
Lemma F_669b8 : fetch_word AsanUbsan.M.loaded_segments (0x66a00 : word) = Some W_669b8.
Proof. vm_refl. Qed.
Lemma D_669b8 : decode_any W_669b8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669bc : bv 32 := 0x00000613.
Lemma F_669bc : fetch_word AsanUbsan.M.loaded_segments (0x66a04 : word) = Some W_669bc.
Proof. vm_refl. Qed.
Lemma D_669bc : decode_any W_669bc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669c0 : bv 32 := 0x0005b023.
Lemma F_669c0 : fetch_word AsanUbsan.M.loaded_segments (0x66a08 : word) = Some W_669c0.
Proof. vm_refl. Qed.
Lemma D_669c0 : decode_any W_669c0 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669c4 : bv 32 := 0x0005b423.
Lemma F_669c4 : fetch_word AsanUbsan.M.loaded_segments (0x66a0c : word) = Some W_669c4.
Proof. vm_refl. Qed.
Lemma D_669c4 : decode_any W_669c4 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669c8 : bv 32 := 0x01813083.
Lemma F_669c8 : fetch_word AsanUbsan.M.loaded_segments (0x66a10 : word) = Some W_669c8.
Proof. vm_refl. Qed.
Lemma D_669c8 : decode_any W_669c8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669cc : bv 32 := 0x01013403.
Lemma F_669cc : fetch_word AsanUbsan.M.loaded_segments (0x66a14 : word) = Some W_669cc.
Proof. vm_refl. Qed.
Lemma D_669cc : decode_any W_669cc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669d0 : bv 32 := 0x00813483.
Lemma F_669d0 : fetch_word AsanUbsan.M.loaded_segments (0x66a18 : word) = Some W_669d0.
Proof. vm_refl. Qed.
Lemma D_669d0 : decode_any W_669d0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669d4 : bv 32 := 0x00013903.
Lemma F_669d4 : fetch_word AsanUbsan.M.loaded_segments (0x66a1c : word) = Some W_669d4.
Proof. vm_refl. Qed.
Lemma D_669d4 : decode_any W_669d4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669d8 : bv 32 := 0x02010113.
Lemma F_669d8 : fetch_word AsanUbsan.M.loaded_segments (0x66a20 : word) = Some W_669d8.
Proof. vm_refl. Qed.
Lemma D_669d8 : decode_any W_669d8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669dc : bv 32 := 0x00008067.
Lemma F_669dc : fetch_word AsanUbsan.M.loaded_segments (0x66a24 : word) = Some W_669dc.
Proof. vm_refl. Qed.
Lemma D_669dc : decode_any W_669dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_669fc : bv 32 := 0xfe010113.
Lemma F_669fc : fetch_word AsanUbsan.M.loaded_segments (0x66a44 : word) = Some W_669fc.
Proof. vm_refl. Qed.
Lemma D_669fc : decode_any W_669fc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a00 : bv 32 := 0x00113c23.
Lemma F_66a00 : fetch_word AsanUbsan.M.loaded_segments (0x66a48 : word) = Some W_66a00.
Proof. vm_refl. Qed.
Lemma D_66a00 : decode_any W_66a00 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a04 : bv 32 := 0x00813823.
Lemma F_66a04 : fetch_word AsanUbsan.M.loaded_segments (0x66a4c : word) = Some W_66a04.
Proof. vm_refl. Qed.
Lemma D_66a04 : decode_any W_66a04 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a08 : bv 32 := 0x00913423.
Lemma F_66a08 : fetch_word AsanUbsan.M.loaded_segments (0x66a50 : word) = Some W_66a08.
Proof. vm_refl. Qed.
Lemma D_66a08 : decode_any W_66a08 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a0c : bv 32 := 0x01213023.
Lemma F_66a0c : fetch_word AsanUbsan.M.loaded_segments (0x66a54 : word) = Some W_66a0c.
Proof. vm_refl. Qed.
Lemma D_66a0c : decode_any W_66a0c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a10 : bv 32 := 0x02010413.
Lemma F_66a10 : fetch_word AsanUbsan.M.loaded_segments (0x66a58 : word) = Some W_66a10.
Proof. vm_refl. Qed.
Lemma D_66a10 : decode_any W_66a10 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a14 : bv 32 := 0x000ff517.
Lemma F_66a14 : fetch_word AsanUbsan.M.loaded_segments (0x66a5c : word) = Some W_66a14.
Proof. vm_refl. Qed.
Lemma D_66a14 : decode_any W_66a14 = Some (Auipc 10 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a18 : bv 32 := 0x8dc50513.
Lemma F_66a18 : fetch_word AsanUbsan.M.loaded_segments (0x66a60 : word) = Some W_66a18.
Proof. vm_refl. Qed.
Lemma D_66a18 : decode_any W_66a18 = Some (OpImm ALU_ADD 10 10 2268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a1c : bv 32 := 0x009050ef.
Lemma F_66a1c : fetch_word AsanUbsan.M.loaded_segments (0x66a64 : word) = Some W_66a1c.
Proof. vm_refl. Qed.
Lemma D_66a1c : decode_any W_66a1c = Some (Jal 1 22536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a20 : bv 32 := 0x00053483.
Lemma F_66a20 : fetch_word AsanUbsan.M.loaded_segments (0x66a68 : word) = Some W_66a20.
Proof. vm_refl. Qed.
Lemma D_66a20 : decode_any W_66a20 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a24 : bv 32 := 0x08048863.
Lemma F_66a24 : fetch_word AsanUbsan.M.loaded_segments (0x66a6c : word) = Some W_66a24.
Proof. vm_refl. Qed.
Lemma D_66a24 : decode_any W_66a24 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a28 : bv 32 := 0x0604c503.
Lemma F_66a28 : fetch_word AsanUbsan.M.loaded_segments (0x66a70 : word) = Some W_66a28.
Proof. vm_refl. Qed.
Lemma D_66a28 : decode_any W_66a28 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a2c : bv 32 := 0x0584b903.
Lemma F_66a2c : fetch_word AsanUbsan.M.loaded_segments (0x66a74 : word) = Some W_66a2c.
Proof. vm_refl. Qed.
Lemma D_66a2c : decode_any W_66a2c = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a30 : bv 32 := 0x00050863.
Lemma F_66a30 : fetch_word AsanUbsan.M.loaded_segments (0x66a78 : word) = Some W_66a30.
Proof. vm_refl. Qed.
Lemma D_66a30 : decode_any W_66a30 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a34 : bv 32 := 0x00048513.
Lemma F_66a34 : fetch_word AsanUbsan.M.loaded_segments (0x66a7c : word) = Some W_66a34.
Proof. vm_refl. Qed.
Lemma D_66a34 : decode_any W_66a34 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a38 : bv 32 := 0x00040593.
Lemma F_66a38 : fetch_word AsanUbsan.M.loaded_segments (0x66a80 : word) = Some W_66a38.
Proof. vm_refl. Qed.
Lemma D_66a38 : decode_any W_66a38 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a3c : bv 32 := 0x871ff0ef.
Lemma F_66a3c : fetch_word AsanUbsan.M.loaded_segments (0x66a84 : word) = Some W_66a3c.
Proof. vm_refl. Qed.
Lemma D_66a3c : decode_any W_66a3c = Some (Jal 1 2095216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a40 : bv 32 := 0xff890593.
Lemma F_66a40 : fetch_word AsanUbsan.M.loaded_segments (0x66a88 : word) = Some W_66a40.
Proof. vm_refl. Qed.
Lemma D_66a40 : decode_any W_66a40 = Some (OpImm ALU_ADD 11 18 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a44 : bv 32 := 0x00100513.
Lemma F_66a44 : fetch_word AsanUbsan.M.loaded_segments (0x66a8c : word) = Some W_66a44.
Proof. vm_refl. Qed.
Lemma D_66a44 : decode_any W_66a44 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a48 : bv 32 := 0x00b51533.
Lemma F_66a48 : fetch_word AsanUbsan.M.loaded_segments (0x66a90 : word) = Some W_66a48.
Proof. vm_refl. Qed.
Lemma D_66a48 : decode_any W_66a48 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a4c : bv 32 := 0x0005061b.
Lemma F_66a4c : fetch_word AsanUbsan.M.loaded_segments (0x66a94 : word) = Some W_66a4c.
Proof. vm_refl. Qed.
Lemma D_66a4c : decode_any W_66a4c = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a50 : bv 32 := 0x08c05263.
Lemma F_66a50 : fetch_word AsanUbsan.M.loaded_segments (0x66a98 : word) = Some W_66a50.
Proof. vm_refl. Qed.
Lemma D_66a50 : decode_any W_66a50 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a54 : bv 32 := 0x000016b7.
Lemma F_66a54 : fetch_word AsanUbsan.M.loaded_segments (0x66a9c : word) = Some W_66a54.
Proof. vm_refl. Qed.
Lemma D_66a54 : decode_any W_66a54 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a58 : bv 32 := 0xff190613.
Lemma F_66a58 : fetch_word AsanUbsan.M.loaded_segments (0x66aa0 : word) = Some W_66a58.
Proof. vm_refl. Qed.
Lemma D_66a58 : decode_any W_66a58 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a5c : bv 32 := 0x30000713.
Lemma F_66a5c : fetch_word AsanUbsan.M.loaded_segments (0x66aa4 : word) = Some W_66a5c.
Proof. vm_refl. Qed.
Lemma D_66a5c : decode_any W_66a5c = Some (OpImm ALU_ADD 14 0 768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a60 : bv 32 := 0xfff00793.
Lemma F_66a60 : fetch_word AsanUbsan.M.loaded_segments (0x66aa8 : word) = Some W_66a60.
Proof. vm_refl. Qed.
Lemma D_66a60 : decode_any W_66a60 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a64 : bv 32 := 0x00c71733.
Lemma F_66a64 : fetch_word AsanUbsan.M.loaded_segments (0x66aac : word) = Some W_66a64.
Proof. vm_refl. Qed.
Lemma D_66a64 : decode_any W_66a64 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a68 : bv 32 := 0x0104b603.
Lemma F_66a68 : fetch_word AsanUbsan.M.loaded_segments (0x66ab0 : word) = Some W_66a68.
Proof. vm_refl. Qed.
Lemma D_66a68 : decode_any W_66a68 = Some (Load SZ8 true 12 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a6c : bv 32 := 0x00b797b3.
Lemma F_66a6c : fetch_word AsanUbsan.M.loaded_segments (0x66ab4 : word) = Some W_66a6c.
Proof. vm_refl. Qed.
Lemma D_66a6c : decode_any W_66a6c = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a70 : bv 32 := 0xfff50813.
Lemma F_66a70 : fetch_word AsanUbsan.M.loaded_segments (0x66ab8 : word) = Some W_66a70.
Proof. vm_refl. Qed.
Lemma D_66a70 : decode_any W_66a70 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a74 : bv 32 := 0x00d485b3.
Lemma F_66a74 : fetch_word AsanUbsan.M.loaded_segments (0x66abc : word) = Some W_66a74.
Proof. vm_refl. Qed.
Lemma D_66a74 : decode_any W_66a74 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a78 : bv 32 := 0x00e586b3.
Lemma F_66a78 : fetch_word AsanUbsan.M.loaded_segments (0x66ac0 : word) = Some W_66a78.
Proof. vm_refl. Qed.
Lemma D_66a78 : decode_any W_66a78 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a7c : bv 32 := 0xfff7c713.
Lemma F_66a7c : fetch_word AsanUbsan.M.loaded_segments (0x66ac4 : word) = Some W_66a7c.
Proof. vm_refl. Qed.
Lemma D_66a7c : decode_any W_66a7c = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a80 : bv 32 := 0x02081813.
Lemma F_66a80 : fetch_word AsanUbsan.M.loaded_segments (0x66ac8 : word) = Some W_66a80.
Proof. vm_refl. Qed.
Lemma D_66a80 : decode_any W_66a80 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a84 : bv 32 := 0x02085793.
Lemma F_66a84 : fetch_word AsanUbsan.M.loaded_segments (0x66acc : word) = Some W_66a84.
Proof. vm_refl. Qed.
Lemma D_66a84 : decode_any W_66a84 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a88 : bv 32 := 0x00f607b3.
Lemma F_66a88 : fetch_word AsanUbsan.M.loaded_segments (0x66ad0 : word) = Some W_66a88.
Proof. vm_refl. Qed.
Lemma D_66a88 : decode_any W_66a88 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a8c : bv 32 := 0x00178813.
Lemma F_66a8c : fetch_word AsanUbsan.M.loaded_segments (0x66ad4 : word) = Some W_66a8c.
Proof. vm_refl. Qed.
Lemma D_66a8c : decode_any W_66a8c = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a90 : bv 32 := 0x00e678b3.
Lemma F_66a90 : fetch_word AsanUbsan.M.loaded_segments (0x66ad8 : word) = Some W_66a90.
Proof. vm_refl. Qed.
Lemma D_66a90 : decode_any W_66a90 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a94 : bv 32 := 0x011687b3.
Lemma F_66a94 : fetch_word AsanUbsan.M.loaded_segments (0x66adc : word) = Some W_66a94.
Proof. vm_refl. Qed.
Lemma D_66a94 : decode_any W_66a94 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a98 : bv 32 := 0x0007c283.
Lemma F_66a98 : fetch_word AsanUbsan.M.loaded_segments (0x66ae0 : word) = Some W_66a98.
Proof. vm_refl. Qed.
Lemma D_66a98 : decode_any W_66a98 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66a9c : bv 32 := 0x06028663.
Lemma F_66a9c : fetch_word AsanUbsan.M.loaded_segments (0x66ae4 : word) = Some W_66a9c.
Proof. vm_refl. Qed.
Lemma D_66a9c : decode_any W_66a9c = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66aa0 : bv 32 := 0xfff5051b.
Lemma F_66aa0 : fetch_word AsanUbsan.M.loaded_segments (0x66ae8 : word) = Some W_66aa0.
Proof. vm_refl. Qed.
Lemma D_66aa0 : decode_any W_66aa0 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66aa4 : bv 32 := 0x00160613.
Lemma F_66aa4 : fetch_word AsanUbsan.M.loaded_segments (0x66aec : word) = Some W_66aa4.
Proof. vm_refl. Qed.
Lemma D_66aa4 : decode_any W_66aa4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66aa8 : bv 32 := 0xfe0514e3.
Lemma F_66aa8 : fetch_word AsanUbsan.M.loaded_segments (0x66af0 : word) = Some W_66aa8.
Proof. vm_refl. Qed.
Lemma D_66aa8 : decode_any W_66aa8 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b08 : bv 32 := 0x00160613.
Lemma F_66b08 : fetch_word AsanUbsan.M.loaded_segments (0x66b50 : word) = Some W_66b08.
Proof. vm_refl. Qed.
Lemma D_66b08 : decode_any W_66b08 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b0c : bv 32 := 0x00100513.
Lemma F_66b0c : fetch_word AsanUbsan.M.loaded_segments (0x66b54 : word) = Some W_66b0c.
Proof. vm_refl. Qed.
Lemma D_66b0c : decode_any W_66b0c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b10 : bv 32 := 0xffb90693.
Lemma F_66b10 : fetch_word AsanUbsan.M.loaded_segments (0x66b58 : word) = Some W_66b10.
Proof. vm_refl. Qed.
Lemma D_66b10 : decode_any W_66b10 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b14 : bv 32 := 0x00c4b823.
Lemma F_66b14 : fetch_word AsanUbsan.M.loaded_segments (0x66b5c : word) = Some W_66b14.
Proof. vm_refl. Qed.
Lemma D_66b14 : decode_any W_66b14 = Some (Store SZ8 9 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b18 : bv 32 := 0x00a78023.
Lemma F_66b18 : fetch_word AsanUbsan.M.loaded_segments (0x66b60 : word) = Some W_66b18.
Proof. vm_refl. Qed.
Lemma D_66b18 : decode_any W_66b18 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b1c : bv 32 := 0x00d51533.
Lemma F_66b1c : fetch_word AsanUbsan.M.loaded_segments (0x66b64 : word) = Some W_66b1c.
Proof. vm_refl. Qed.
Lemma D_66b1c : decode_any W_66b1c = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b20 : bv 32 := 0x00200613.
Lemma F_66b20 : fetch_word AsanUbsan.M.loaded_segments (0x66b68 : word) = Some W_66b20.
Proof. vm_refl. Qed.
Lemma D_66b20 : decode_any W_66b20 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b24 : bv 32 := 0x00889893.
Lemma F_66b24 : fetch_word AsanUbsan.M.loaded_segments (0x66b6c : word) = Some W_66b24.
Proof. vm_refl. Qed.
Lemma D_66b24 : decode_any W_66b24 = Some (ShiftImm ALU_SLL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b28 : bv 32 := 0x01261633.
Lemma F_66b28 : fetch_word AsanUbsan.M.loaded_segments (0x66b70 : word) = Some W_66b28.
Proof. vm_refl. Qed.
Lemma D_66b28 : decode_any W_66b28 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b2c : bv 32 := 0x00a58533.
Lemma F_66b2c : fetch_word AsanUbsan.M.loaded_segments (0x66b74 : word) = Some W_66b2c.
Proof. vm_refl. Qed.
Lemma D_66b2c : decode_any W_66b2c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b30 : bv 32 := 0x01160633.
Lemma F_66b30 : fetch_word AsanUbsan.M.loaded_segments (0x66b78 : word) = Some W_66b30.
Proof. vm_refl. Qed.
Lemma D_66b30 : decode_any W_66b30 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b34 : bv 32 := 0x00c504b3.
Lemma F_66b34 : fetch_word AsanUbsan.M.loaded_segments (0x66b7c : word) = Some W_66b34.
Proof. vm_refl. Qed.
Lemma D_66b34 : decode_any W_66b34 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b38 : bv 32 := 0x0084bc23.
Lemma F_66b38 : fetch_word AsanUbsan.M.loaded_segments (0x66b80 : word) = Some W_66b38.
Proof. vm_refl. Qed.
Lemma D_66b38 : decode_any W_66b38 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b3c : bv 32 := 0x0ef4bc23.
Lemma F_66b3c : fetch_word AsanUbsan.M.loaded_segments (0x66b84 : word) = Some W_66b3c.
Proof. vm_refl. Qed.
Lemma D_66b3c : decode_any W_66b3c = Some (Store SZ8 9 15 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b40 : bv 32 := 0x00048513.
Lemma F_66b40 : fetch_word AsanUbsan.M.loaded_segments (0x66b88 : word) = Some W_66b40.
Proof. vm_refl. Qed.
Lemma D_66b40 : decode_any W_66b40 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b44 : bv 32 := 0x68c000ef.
Lemma F_66b44 : fetch_word AsanUbsan.M.loaded_segments (0x66b8c : word) = Some W_66b44.
Proof. vm_refl. Qed.
Lemma D_66b44 : decode_any W_66b44 = Some (Jal 1 1676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b48 : bv 32 := 0x00050593.
Lemma F_66b48 : fetch_word AsanUbsan.M.loaded_segments (0x66b90 : word) = Some W_66b48.
Proof. vm_refl. Qed.
Lemma D_66b48 : decode_any W_66b48 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b4c : bv 32 := 0x00048513.
Lemma F_66b4c : fetch_word AsanUbsan.M.loaded_segments (0x66b94 : word) = Some W_66b4c.
Proof. vm_refl. Qed.
Lemma D_66b4c : decode_any W_66b4c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b50 : bv 32 := 0x00000613.
Lemma F_66b50 : fetch_word AsanUbsan.M.loaded_segments (0x66b98 : word) = Some W_66b50.
Proof. vm_refl. Qed.
Lemma D_66b50 : decode_any W_66b50 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b54 : bv 32 := 0x0005b023.
Lemma F_66b54 : fetch_word AsanUbsan.M.loaded_segments (0x66b9c : word) = Some W_66b54.
Proof. vm_refl. Qed.
Lemma D_66b54 : decode_any W_66b54 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b58 : bv 32 := 0x0005b423.
Lemma F_66b58 : fetch_word AsanUbsan.M.loaded_segments (0x66ba0 : word) = Some W_66b58.
Proof. vm_refl. Qed.
Lemma D_66b58 : decode_any W_66b58 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b5c : bv 32 := 0x0005b823.
Lemma F_66b5c : fetch_word AsanUbsan.M.loaded_segments (0x66ba4 : word) = Some W_66b5c.
Proof. vm_refl. Qed.
Lemma D_66b5c : decode_any W_66b5c = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b60 : bv 32 := 0x0005bc23.
Lemma F_66b60 : fetch_word AsanUbsan.M.loaded_segments (0x66ba8 : word) = Some W_66b60.
Proof. vm_refl. Qed.
Lemma D_66b60 : decode_any W_66b60 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b64 : bv 32 := 0x01813083.
Lemma F_66b64 : fetch_word AsanUbsan.M.loaded_segments (0x66bac : word) = Some W_66b64.
Proof. vm_refl. Qed.
Lemma D_66b64 : decode_any W_66b64 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b68 : bv 32 := 0x01013403.
Lemma F_66b68 : fetch_word AsanUbsan.M.loaded_segments (0x66bb0 : word) = Some W_66b68.
Proof. vm_refl. Qed.
Lemma D_66b68 : decode_any W_66b68 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b6c : bv 32 := 0x00813483.
Lemma F_66b6c : fetch_word AsanUbsan.M.loaded_segments (0x66bb4 : word) = Some W_66b6c.
Proof. vm_refl. Qed.
Lemma D_66b6c : decode_any W_66b6c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b70 : bv 32 := 0x00013903.
Lemma F_66b70 : fetch_word AsanUbsan.M.loaded_segments (0x66bb8 : word) = Some W_66b70.
Proof. vm_refl. Qed.
Lemma D_66b70 : decode_any W_66b70 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b74 : bv 32 := 0x02010113.
Lemma F_66b74 : fetch_word AsanUbsan.M.loaded_segments (0x66bbc : word) = Some W_66b74.
Proof. vm_refl. Qed.
Lemma D_66b74 : decode_any W_66b74 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b78 : bv 32 := 0x00008067.
Lemma F_66b78 : fetch_word AsanUbsan.M.loaded_segments (0x66bc0 : word) = Some W_66b78.
Proof. vm_refl. Qed.
Lemma D_66b78 : decode_any W_66b78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b98 : bv 32 := 0xfe010113.
Lemma F_66b98 : fetch_word AsanUbsan.M.loaded_segments (0x66be0 : word) = Some W_66b98.
Proof. vm_refl. Qed.
Lemma D_66b98 : decode_any W_66b98 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66b9c : bv 32 := 0x00113c23.
Lemma F_66b9c : fetch_word AsanUbsan.M.loaded_segments (0x66be4 : word) = Some W_66b9c.
Proof. vm_refl. Qed.
Lemma D_66b9c : decode_any W_66b9c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ba0 : bv 32 := 0x00813823.
Lemma F_66ba0 : fetch_word AsanUbsan.M.loaded_segments (0x66be8 : word) = Some W_66ba0.
Proof. vm_refl. Qed.
Lemma D_66ba0 : decode_any W_66ba0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ba4 : bv 32 := 0x00913423.
Lemma F_66ba4 : fetch_word AsanUbsan.M.loaded_segments (0x66bec : word) = Some W_66ba4.
Proof. vm_refl. Qed.
Lemma D_66ba4 : decode_any W_66ba4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ba8 : bv 32 := 0x01213023.
Lemma F_66ba8 : fetch_word AsanUbsan.M.loaded_segments (0x66bf0 : word) = Some W_66ba8.
Proof. vm_refl. Qed.
Lemma D_66ba8 : decode_any W_66ba8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bac : bv 32 := 0x02010413.
Lemma F_66bac : fetch_word AsanUbsan.M.loaded_segments (0x66bf4 : word) = Some W_66bac.
Proof. vm_refl. Qed.
Lemma D_66bac : decode_any W_66bac = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bb0 : bv 32 := 0x000fe517.
Lemma F_66bb0 : fetch_word AsanUbsan.M.loaded_segments (0x66bf8 : word) = Some W_66bb0.
Proof. vm_refl. Qed.
Lemma D_66bb0 : decode_any W_66bb0 = Some (Auipc 10 254, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bb4 : bv 32 := 0x74050513.
Lemma F_66bb4 : fetch_word AsanUbsan.M.loaded_segments (0x66bfc : word) = Some W_66bb4.
Proof. vm_refl. Qed.
Lemma D_66bb4 : decode_any W_66bb4 = Some (OpImm ALU_ADD 10 10 1856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bb8 : bv 32 := 0x66c050ef.
Lemma F_66bb8 : fetch_word AsanUbsan.M.loaded_segments (0x66c00 : word) = Some W_66bb8.
Proof. vm_refl. Qed.
Lemma D_66bb8 : decode_any W_66bb8 = Some (Jal 1 22124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bbc : bv 32 := 0x00053483.
Lemma F_66bbc : fetch_word AsanUbsan.M.loaded_segments (0x66c04 : word) = Some W_66bbc.
Proof. vm_refl. Qed.
Lemma D_66bbc : decode_any W_66bbc = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bc0 : bv 32 := 0x08048863.
Lemma F_66bc0 : fetch_word AsanUbsan.M.loaded_segments (0x66c08 : word) = Some W_66bc0.
Proof. vm_refl. Qed.
Lemma D_66bc0 : decode_any W_66bc0 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bc4 : bv 32 := 0x0604c503.
Lemma F_66bc4 : fetch_word AsanUbsan.M.loaded_segments (0x66c0c : word) = Some W_66bc4.
Proof. vm_refl. Qed.
Lemma D_66bc4 : decode_any W_66bc4 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bc8 : bv 32 := 0x0584b903.
Lemma F_66bc8 : fetch_word AsanUbsan.M.loaded_segments (0x66c10 : word) = Some W_66bc8.
Proof. vm_refl. Qed.
Lemma D_66bc8 : decode_any W_66bc8 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bcc : bv 32 := 0x00050863.
Lemma F_66bcc : fetch_word AsanUbsan.M.loaded_segments (0x66c14 : word) = Some W_66bcc.
Proof. vm_refl. Qed.
Lemma D_66bcc : decode_any W_66bcc = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bd0 : bv 32 := 0x00048513.
Lemma F_66bd0 : fetch_word AsanUbsan.M.loaded_segments (0x66c18 : word) = Some W_66bd0.
Proof. vm_refl. Qed.
Lemma D_66bd0 : decode_any W_66bd0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bd4 : bv 32 := 0x00040593.
Lemma F_66bd4 : fetch_word AsanUbsan.M.loaded_segments (0x66c1c : word) = Some W_66bd4.
Proof. vm_refl. Qed.
Lemma D_66bd4 : decode_any W_66bd4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bd8 : bv 32 := 0xed4ff0ef.
Lemma F_66bd8 : fetch_word AsanUbsan.M.loaded_segments (0x66c20 : word) = Some W_66bd8.
Proof. vm_refl. Qed.
Lemma D_66bd8 : decode_any W_66bd8 = Some (Jal 1 2094804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bdc : bv 32 := 0xff790593.
Lemma F_66bdc : fetch_word AsanUbsan.M.loaded_segments (0x66c24 : word) = Some W_66bdc.
Proof. vm_refl. Qed.
Lemma D_66bdc : decode_any W_66bdc = Some (OpImm ALU_ADD 11 18 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66be0 : bv 32 := 0x00100513.
Lemma F_66be0 : fetch_word AsanUbsan.M.loaded_segments (0x66c28 : word) = Some W_66be0.
Proof. vm_refl. Qed.
Lemma D_66be0 : decode_any W_66be0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66be4 : bv 32 := 0x00b51533.
Lemma F_66be4 : fetch_word AsanUbsan.M.loaded_segments (0x66c2c : word) = Some W_66be4.
Proof. vm_refl. Qed.
Lemma D_66be4 : decode_any W_66be4 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66be8 : bv 32 := 0x0005061b.
Lemma F_66be8 : fetch_word AsanUbsan.M.loaded_segments (0x66c30 : word) = Some W_66be8.
Proof. vm_refl. Qed.
Lemma D_66be8 : decode_any W_66be8 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bec : bv 32 := 0x08c05263.
Lemma F_66bec : fetch_word AsanUbsan.M.loaded_segments (0x66c34 : word) = Some W_66bec.
Proof. vm_refl. Qed.
Lemma D_66bec : decode_any W_66bec = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bf0 : bv 32 := 0x000016b7.
Lemma F_66bf0 : fetch_word AsanUbsan.M.loaded_segments (0x66c38 : word) = Some W_66bf0.
Proof. vm_refl. Qed.
Lemma D_66bf0 : decode_any W_66bf0 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bf4 : bv 32 := 0xff190613.
Lemma F_66bf4 : fetch_word AsanUbsan.M.loaded_segments (0x66c3c : word) = Some W_66bf4.
Proof. vm_refl. Qed.
Lemma D_66bf4 : decode_any W_66bf4 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bf8 : bv 32 := 0x38000713.
Lemma F_66bf8 : fetch_word AsanUbsan.M.loaded_segments (0x66c40 : word) = Some W_66bf8.
Proof. vm_refl. Qed.
Lemma D_66bf8 : decode_any W_66bf8 = Some (OpImm ALU_ADD 14 0 896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66bfc : bv 32 := 0xfff00793.
Lemma F_66bfc : fetch_word AsanUbsan.M.loaded_segments (0x66c44 : word) = Some W_66bfc.
Proof. vm_refl. Qed.
Lemma D_66bfc : decode_any W_66bfc = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c00 : bv 32 := 0x00c71733.
Lemma F_66c00 : fetch_word AsanUbsan.M.loaded_segments (0x66c48 : word) = Some W_66c00.
Proof. vm_refl. Qed.
Lemma D_66c00 : decode_any W_66c00 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c04 : bv 32 := 0x0184b603.
Lemma F_66c04 : fetch_word AsanUbsan.M.loaded_segments (0x66c4c : word) = Some W_66c04.
Proof. vm_refl. Qed.
Lemma D_66c04 : decode_any W_66c04 = Some (Load SZ8 true 12 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c08 : bv 32 := 0x00b797b3.
Lemma F_66c08 : fetch_word AsanUbsan.M.loaded_segments (0x66c50 : word) = Some W_66c08.
Proof. vm_refl. Qed.
Lemma D_66c08 : decode_any W_66c08 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c0c : bv 32 := 0xfff50813.
Lemma F_66c0c : fetch_word AsanUbsan.M.loaded_segments (0x66c54 : word) = Some W_66c0c.
Proof. vm_refl. Qed.
Lemma D_66c0c : decode_any W_66c0c = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c10 : bv 32 := 0x00d485b3.
Lemma F_66c10 : fetch_word AsanUbsan.M.loaded_segments (0x66c58 : word) = Some W_66c10.
Proof. vm_refl. Qed.
Lemma D_66c10 : decode_any W_66c10 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c14 : bv 32 := 0x00e586b3.
Lemma F_66c14 : fetch_word AsanUbsan.M.loaded_segments (0x66c5c : word) = Some W_66c14.
Proof. vm_refl. Qed.
Lemma D_66c14 : decode_any W_66c14 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c18 : bv 32 := 0xfff7c713.
Lemma F_66c18 : fetch_word AsanUbsan.M.loaded_segments (0x66c60 : word) = Some W_66c18.
Proof. vm_refl. Qed.
Lemma D_66c18 : decode_any W_66c18 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c1c : bv 32 := 0x02081813.
Lemma F_66c1c : fetch_word AsanUbsan.M.loaded_segments (0x66c64 : word) = Some W_66c1c.
Proof. vm_refl. Qed.
Lemma D_66c1c : decode_any W_66c1c = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c20 : bv 32 := 0x02085793.
Lemma F_66c20 : fetch_word AsanUbsan.M.loaded_segments (0x66c68 : word) = Some W_66c20.
Proof. vm_refl. Qed.
Lemma D_66c20 : decode_any W_66c20 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c24 : bv 32 := 0x00f607b3.
Lemma F_66c24 : fetch_word AsanUbsan.M.loaded_segments (0x66c6c : word) = Some W_66c24.
Proof. vm_refl. Qed.
Lemma D_66c24 : decode_any W_66c24 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c28 : bv 32 := 0x00178813.
Lemma F_66c28 : fetch_word AsanUbsan.M.loaded_segments (0x66c70 : word) = Some W_66c28.
Proof. vm_refl. Qed.
Lemma D_66c28 : decode_any W_66c28 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c2c : bv 32 := 0x00e678b3.
Lemma F_66c2c : fetch_word AsanUbsan.M.loaded_segments (0x66c74 : word) = Some W_66c2c.
Proof. vm_refl. Qed.
Lemma D_66c2c : decode_any W_66c2c = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c30 : bv 32 := 0x011687b3.
Lemma F_66c30 : fetch_word AsanUbsan.M.loaded_segments (0x66c78 : word) = Some W_66c30.
Proof. vm_refl. Qed.
Lemma D_66c30 : decode_any W_66c30 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c34 : bv 32 := 0x0007c283.
Lemma F_66c34 : fetch_word AsanUbsan.M.loaded_segments (0x66c7c : word) = Some W_66c34.
Proof. vm_refl. Qed.
Lemma D_66c34 : decode_any W_66c34 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c38 : bv 32 := 0x06028663.
Lemma F_66c38 : fetch_word AsanUbsan.M.loaded_segments (0x66c80 : word) = Some W_66c38.
Proof. vm_refl. Qed.
Lemma D_66c38 : decode_any W_66c38 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c3c : bv 32 := 0xfff5051b.
Lemma F_66c3c : fetch_word AsanUbsan.M.loaded_segments (0x66c84 : word) = Some W_66c3c.
Proof. vm_refl. Qed.
Lemma D_66c3c : decode_any W_66c3c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c40 : bv 32 := 0x00160613.
Lemma F_66c40 : fetch_word AsanUbsan.M.loaded_segments (0x66c88 : word) = Some W_66c40.
Proof. vm_refl. Qed.
Lemma D_66c40 : decode_any W_66c40 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66c44 : bv 32 := 0xfe0514e3.
Lemma F_66c44 : fetch_word AsanUbsan.M.loaded_segments (0x66c8c : word) = Some W_66c44.
Proof. vm_refl. Qed.
Lemma D_66c44 : decode_any W_66c44 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ca4 : bv 32 := 0x00160613.
Lemma F_66ca4 : fetch_word AsanUbsan.M.loaded_segments (0x66cec : word) = Some W_66ca4.
Proof. vm_refl. Qed.
Lemma D_66ca4 : decode_any W_66ca4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ca8 : bv 32 := 0x00100513.
Lemma F_66ca8 : fetch_word AsanUbsan.M.loaded_segments (0x66cf0 : word) = Some W_66ca8.
Proof. vm_refl. Qed.
Lemma D_66ca8 : decode_any W_66ca8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cac : bv 32 := 0xffb90693.
Lemma F_66cac : fetch_word AsanUbsan.M.loaded_segments (0x66cf4 : word) = Some W_66cac.
Proof. vm_refl. Qed.
Lemma D_66cac : decode_any W_66cac = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cb0 : bv 32 := 0x00c4bc23.
Lemma F_66cb0 : fetch_word AsanUbsan.M.loaded_segments (0x66cf8 : word) = Some W_66cb0.
Proof. vm_refl. Qed.
Lemma D_66cb0 : decode_any W_66cb0 = Some (Store SZ8 9 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cb4 : bv 32 := 0x00a78023.
Lemma F_66cb4 : fetch_word AsanUbsan.M.loaded_segments (0x66cfc : word) = Some W_66cb4.
Proof. vm_refl. Qed.
Lemma D_66cb4 : decode_any W_66cb4 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cb8 : bv 32 := 0x00d51533.
Lemma F_66cb8 : fetch_word AsanUbsan.M.loaded_segments (0x66d00 : word) = Some W_66cb8.
Proof. vm_refl. Qed.
Lemma D_66cb8 : decode_any W_66cb8 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cbc : bv 32 := 0x00300613.
Lemma F_66cbc : fetch_word AsanUbsan.M.loaded_segments (0x66d04 : word) = Some W_66cbc.
Proof. vm_refl. Qed.
Lemma D_66cbc : decode_any W_66cbc = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cc0 : bv 32 := 0x00989893.
Lemma F_66cc0 : fetch_word AsanUbsan.M.loaded_segments (0x66d08 : word) = Some W_66cc0.
Proof. vm_refl. Qed.
Lemma D_66cc0 : decode_any W_66cc0 = Some (ShiftImm ALU_SLL 17 17 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cc4 : bv 32 := 0x01261633.
Lemma F_66cc4 : fetch_word AsanUbsan.M.loaded_segments (0x66d0c : word) = Some W_66cc4.
Proof. vm_refl. Qed.
Lemma D_66cc4 : decode_any W_66cc4 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cc8 : bv 32 := 0x00a58533.
Lemma F_66cc8 : fetch_word AsanUbsan.M.loaded_segments (0x66d10 : word) = Some W_66cc8.
Proof. vm_refl. Qed.
Lemma D_66cc8 : decode_any W_66cc8 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ccc : bv 32 := 0x01160633.
Lemma F_66ccc : fetch_word AsanUbsan.M.loaded_segments (0x66d14 : word) = Some W_66ccc.
Proof. vm_refl. Qed.
Lemma D_66ccc : decode_any W_66ccc = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cd0 : bv 32 := 0x00c504b3.
Lemma F_66cd0 : fetch_word AsanUbsan.M.loaded_segments (0x66d18 : word) = Some W_66cd0.
Proof. vm_refl. Qed.
Lemma D_66cd0 : decode_any W_66cd0 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cd4 : bv 32 := 0x0084bc23.
Lemma F_66cd4 : fetch_word AsanUbsan.M.loaded_segments (0x66d1c : word) = Some W_66cd4.
Proof. vm_refl. Qed.
Lemma D_66cd4 : decode_any W_66cd4 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cd8 : bv 32 := 0x1ef4bc23.
Lemma F_66cd8 : fetch_word AsanUbsan.M.loaded_segments (0x66d20 : word) = Some W_66cd8.
Proof. vm_refl. Qed.
Lemma D_66cd8 : decode_any W_66cd8 = Some (Store SZ8 9 15 504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cdc : bv 32 := 0x00048513.
Lemma F_66cdc : fetch_word AsanUbsan.M.loaded_segments (0x66d24 : word) = Some W_66cdc.
Proof. vm_refl. Qed.
Lemma D_66cdc : decode_any W_66cdc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ce0 : bv 32 := 0x4f0000ef.
Lemma F_66ce0 : fetch_word AsanUbsan.M.loaded_segments (0x66d28 : word) = Some W_66ce0.
Proof. vm_refl. Qed.
Lemma D_66ce0 : decode_any W_66ce0 = Some (Jal 1 1264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ce4 : bv 32 := 0x00050593.
Lemma F_66ce4 : fetch_word AsanUbsan.M.loaded_segments (0x66d2c : word) = Some W_66ce4.
Proof. vm_refl. Qed.
Lemma D_66ce4 : decode_any W_66ce4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ce8 : bv 32 := 0x00048513.
Lemma F_66ce8 : fetch_word AsanUbsan.M.loaded_segments (0x66d30 : word) = Some W_66ce8.
Proof. vm_refl. Qed.
Lemma D_66ce8 : decode_any W_66ce8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cec : bv 32 := 0x00000613.
Lemma F_66cec : fetch_word AsanUbsan.M.loaded_segments (0x66d34 : word) = Some W_66cec.
Proof. vm_refl. Qed.
Lemma D_66cec : decode_any W_66cec = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cf0 : bv 32 := 0x0005b023.
Lemma F_66cf0 : fetch_word AsanUbsan.M.loaded_segments (0x66d38 : word) = Some W_66cf0.
Proof. vm_refl. Qed.
Lemma D_66cf0 : decode_any W_66cf0 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cf4 : bv 32 := 0x0005b423.
Lemma F_66cf4 : fetch_word AsanUbsan.M.loaded_segments (0x66d3c : word) = Some W_66cf4.
Proof. vm_refl. Qed.
Lemma D_66cf4 : decode_any W_66cf4 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cf8 : bv 32 := 0x0005b823.
Lemma F_66cf8 : fetch_word AsanUbsan.M.loaded_segments (0x66d40 : word) = Some W_66cf8.
Proof. vm_refl. Qed.
Lemma D_66cf8 : decode_any W_66cf8 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66cfc : bv 32 := 0x0005bc23.
Lemma F_66cfc : fetch_word AsanUbsan.M.loaded_segments (0x66d44 : word) = Some W_66cfc.
Proof. vm_refl. Qed.
Lemma D_66cfc : decode_any W_66cfc = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d00 : bv 32 := 0x0205b023.
Lemma F_66d00 : fetch_word AsanUbsan.M.loaded_segments (0x66d48 : word) = Some W_66d00.
Proof. vm_refl. Qed.
Lemma D_66d00 : decode_any W_66d00 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d04 : bv 32 := 0x0205b423.
Lemma F_66d04 : fetch_word AsanUbsan.M.loaded_segments (0x66d4c : word) = Some W_66d04.
Proof. vm_refl. Qed.
Lemma D_66d04 : decode_any W_66d04 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d08 : bv 32 := 0x0205b823.
Lemma F_66d08 : fetch_word AsanUbsan.M.loaded_segments (0x66d50 : word) = Some W_66d08.
Proof. vm_refl. Qed.
Lemma D_66d08 : decode_any W_66d08 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d0c : bv 32 := 0x0205bc23.
Lemma F_66d0c : fetch_word AsanUbsan.M.loaded_segments (0x66d54 : word) = Some W_66d0c.
Proof. vm_refl. Qed.
Lemma D_66d0c : decode_any W_66d0c = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d10 : bv 32 := 0x01813083.
Lemma F_66d10 : fetch_word AsanUbsan.M.loaded_segments (0x66d58 : word) = Some W_66d10.
Proof. vm_refl. Qed.
Lemma D_66d10 : decode_any W_66d10 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d14 : bv 32 := 0x01013403.
Lemma F_66d14 : fetch_word AsanUbsan.M.loaded_segments (0x66d5c : word) = Some W_66d14.
Proof. vm_refl. Qed.
Lemma D_66d14 : decode_any W_66d14 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d18 : bv 32 := 0x00813483.
Lemma F_66d18 : fetch_word AsanUbsan.M.loaded_segments (0x66d60 : word) = Some W_66d18.
Proof. vm_refl. Qed.
Lemma D_66d18 : decode_any W_66d18 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d1c : bv 32 := 0x00013903.
Lemma F_66d1c : fetch_word AsanUbsan.M.loaded_segments (0x66d64 : word) = Some W_66d1c.
Proof. vm_refl. Qed.
Lemma D_66d1c : decode_any W_66d1c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d20 : bv 32 := 0x02010113.
Lemma F_66d20 : fetch_word AsanUbsan.M.loaded_segments (0x66d68 : word) = Some W_66d20.
Proof. vm_refl. Qed.
Lemma D_66d20 : decode_any W_66d20 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d24 : bv 32 := 0x00008067.
Lemma F_66d24 : fetch_word AsanUbsan.M.loaded_segments (0x66d6c : word) = Some W_66d24.
Proof. vm_refl. Qed.
Lemma D_66d24 : decode_any W_66d24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d44 : bv 32 := 0xfe010113.
Lemma F_66d44 : fetch_word AsanUbsan.M.loaded_segments (0x66d8c : word) = Some W_66d44.
Proof. vm_refl. Qed.
Lemma D_66d44 : decode_any W_66d44 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d48 : bv 32 := 0x00113c23.
Lemma F_66d48 : fetch_word AsanUbsan.M.loaded_segments (0x66d90 : word) = Some W_66d48.
Proof. vm_refl. Qed.
Lemma D_66d48 : decode_any W_66d48 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d4c : bv 32 := 0x00813823.
Lemma F_66d4c : fetch_word AsanUbsan.M.loaded_segments (0x66d94 : word) = Some W_66d4c.
Proof. vm_refl. Qed.
Lemma D_66d4c : decode_any W_66d4c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d50 : bv 32 := 0x00913423.
Lemma F_66d50 : fetch_word AsanUbsan.M.loaded_segments (0x66d98 : word) = Some W_66d50.
Proof. vm_refl. Qed.
Lemma D_66d50 : decode_any W_66d50 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d54 : bv 32 := 0x01213023.
Lemma F_66d54 : fetch_word AsanUbsan.M.loaded_segments (0x66d9c : word) = Some W_66d54.
Proof. vm_refl. Qed.
Lemma D_66d54 : decode_any W_66d54 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d58 : bv 32 := 0x02010413.
Lemma F_66d58 : fetch_word AsanUbsan.M.loaded_segments (0x66da0 : word) = Some W_66d58.
Proof. vm_refl. Qed.
Lemma D_66d58 : decode_any W_66d58 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d5c : bv 32 := 0x000fe517.
Lemma F_66d5c : fetch_word AsanUbsan.M.loaded_segments (0x66da4 : word) = Some W_66d5c.
Proof. vm_refl. Qed.
Lemma D_66d5c : decode_any W_66d5c = Some (Auipc 10 254, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d60 : bv 32 := 0x59450513.
Lemma F_66d60 : fetch_word AsanUbsan.M.loaded_segments (0x66da8 : word) = Some W_66d60.
Proof. vm_refl. Qed.
Lemma D_66d60 : decode_any W_66d60 = Some (OpImm ALU_ADD 10 10 1428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d64 : bv 32 := 0x4c0050ef.
Lemma F_66d64 : fetch_word AsanUbsan.M.loaded_segments (0x66dac : word) = Some W_66d64.
Proof. vm_refl. Qed.
Lemma D_66d64 : decode_any W_66d64 = Some (Jal 1 21696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d68 : bv 32 := 0x00053483.
Lemma F_66d68 : fetch_word AsanUbsan.M.loaded_segments (0x66db0 : word) = Some W_66d68.
Proof. vm_refl. Qed.
Lemma D_66d68 : decode_any W_66d68 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d6c : bv 32 := 0x08048863.
Lemma F_66d6c : fetch_word AsanUbsan.M.loaded_segments (0x66db4 : word) = Some W_66d6c.
Proof. vm_refl. Qed.
Lemma D_66d6c : decode_any W_66d6c = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d70 : bv 32 := 0x0604c503.
Lemma F_66d70 : fetch_word AsanUbsan.M.loaded_segments (0x66db8 : word) = Some W_66d70.
Proof. vm_refl. Qed.
Lemma D_66d70 : decode_any W_66d70 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d74 : bv 32 := 0x0584b903.
Lemma F_66d74 : fetch_word AsanUbsan.M.loaded_segments (0x66dbc : word) = Some W_66d74.
Proof. vm_refl. Qed.
Lemma D_66d74 : decode_any W_66d74 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d78 : bv 32 := 0x00050863.
Lemma F_66d78 : fetch_word AsanUbsan.M.loaded_segments (0x66dc0 : word) = Some W_66d78.
Proof. vm_refl. Qed.
Lemma D_66d78 : decode_any W_66d78 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d7c : bv 32 := 0x00048513.
Lemma F_66d7c : fetch_word AsanUbsan.M.loaded_segments (0x66dc4 : word) = Some W_66d7c.
Proof. vm_refl. Qed.
Lemma D_66d7c : decode_any W_66d7c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d80 : bv 32 := 0x00040593.
Lemma F_66d80 : fetch_word AsanUbsan.M.loaded_segments (0x66dc8 : word) = Some W_66d80.
Proof. vm_refl. Qed.
Lemma D_66d80 : decode_any W_66d80 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d84 : bv 32 := 0xd28ff0ef.
Lemma F_66d84 : fetch_word AsanUbsan.M.loaded_segments (0x66dcc : word) = Some W_66d84.
Proof. vm_refl. Qed.
Lemma D_66d84 : decode_any W_66d84 = Some (Jal 1 2094376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d88 : bv 32 := 0xff690593.
Lemma F_66d88 : fetch_word AsanUbsan.M.loaded_segments (0x66dd0 : word) = Some W_66d88.
Proof. vm_refl. Qed.
Lemma D_66d88 : decode_any W_66d88 = Some (OpImm ALU_ADD 11 18 4086, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d8c : bv 32 := 0x00100513.
Lemma F_66d8c : fetch_word AsanUbsan.M.loaded_segments (0x66dd4 : word) = Some W_66d8c.
Proof. vm_refl. Qed.
Lemma D_66d8c : decode_any W_66d8c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d90 : bv 32 := 0x00b51533.
Lemma F_66d90 : fetch_word AsanUbsan.M.loaded_segments (0x66dd8 : word) = Some W_66d90.
Proof. vm_refl. Qed.
Lemma D_66d90 : decode_any W_66d90 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d94 : bv 32 := 0x0005061b.
Lemma F_66d94 : fetch_word AsanUbsan.M.loaded_segments (0x66ddc : word) = Some W_66d94.
Proof. vm_refl. Qed.
Lemma D_66d94 : decode_any W_66d94 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d98 : bv 32 := 0x08c05263.
Lemma F_66d98 : fetch_word AsanUbsan.M.loaded_segments (0x66de0 : word) = Some W_66d98.
Proof. vm_refl. Qed.
Lemma D_66d98 : decode_any W_66d98 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66d9c : bv 32 := 0x000016b7.
Lemma F_66d9c : fetch_word AsanUbsan.M.loaded_segments (0x66de4 : word) = Some W_66d9c.
Proof. vm_refl. Qed.
Lemma D_66d9c : decode_any W_66d9c = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66da0 : bv 32 := 0xff190613.
Lemma F_66da0 : fetch_word AsanUbsan.M.loaded_segments (0x66de8 : word) = Some W_66da0.
Proof. vm_refl. Qed.
Lemma D_66da0 : decode_any W_66da0 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66da4 : bv 32 := 0x3c000713.
Lemma F_66da4 : fetch_word AsanUbsan.M.loaded_segments (0x66dec : word) = Some W_66da4.
Proof. vm_refl. Qed.
Lemma D_66da4 : decode_any W_66da4 = Some (OpImm ALU_ADD 14 0 960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66da8 : bv 32 := 0xfff00793.
Lemma F_66da8 : fetch_word AsanUbsan.M.loaded_segments (0x66df0 : word) = Some W_66da8.
Proof. vm_refl. Qed.
Lemma D_66da8 : decode_any W_66da8 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66dac : bv 32 := 0x00c71733.
Lemma F_66dac : fetch_word AsanUbsan.M.loaded_segments (0x66df4 : word) = Some W_66dac.
Proof. vm_refl. Qed.
Lemma D_66dac : decode_any W_66dac = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66db0 : bv 32 := 0x0204b603.
Lemma F_66db0 : fetch_word AsanUbsan.M.loaded_segments (0x66df8 : word) = Some W_66db0.
Proof. vm_refl. Qed.
Lemma D_66db0 : decode_any W_66db0 = Some (Load SZ8 true 12 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66db4 : bv 32 := 0x00b797b3.
Lemma F_66db4 : fetch_word AsanUbsan.M.loaded_segments (0x66dfc : word) = Some W_66db4.
Proof. vm_refl. Qed.
Lemma D_66db4 : decode_any W_66db4 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66db8 : bv 32 := 0xfff50813.
Lemma F_66db8 : fetch_word AsanUbsan.M.loaded_segments (0x66e00 : word) = Some W_66db8.
Proof. vm_refl. Qed.
Lemma D_66db8 : decode_any W_66db8 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66dbc : bv 32 := 0x00d485b3.
Lemma F_66dbc : fetch_word AsanUbsan.M.loaded_segments (0x66e04 : word) = Some W_66dbc.
Proof. vm_refl. Qed.
Lemma D_66dbc : decode_any W_66dbc = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66dc0 : bv 32 := 0x00e586b3.
Lemma F_66dc0 : fetch_word AsanUbsan.M.loaded_segments (0x66e08 : word) = Some W_66dc0.
Proof. vm_refl. Qed.
Lemma D_66dc0 : decode_any W_66dc0 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66dc4 : bv 32 := 0xfff7c713.
Lemma F_66dc4 : fetch_word AsanUbsan.M.loaded_segments (0x66e0c : word) = Some W_66dc4.
Proof. vm_refl. Qed.
Lemma D_66dc4 : decode_any W_66dc4 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66dc8 : bv 32 := 0x02081813.
Lemma F_66dc8 : fetch_word AsanUbsan.M.loaded_segments (0x66e10 : word) = Some W_66dc8.
Proof. vm_refl. Qed.
Lemma D_66dc8 : decode_any W_66dc8 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66dcc : bv 32 := 0x02085793.
Lemma F_66dcc : fetch_word AsanUbsan.M.loaded_segments (0x66e14 : word) = Some W_66dcc.
Proof. vm_refl. Qed.
Lemma D_66dcc : decode_any W_66dcc = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66dd0 : bv 32 := 0x00f607b3.
Lemma F_66dd0 : fetch_word AsanUbsan.M.loaded_segments (0x66e18 : word) = Some W_66dd0.
Proof. vm_refl. Qed.
Lemma D_66dd0 : decode_any W_66dd0 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66dd4 : bv 32 := 0x00178813.
Lemma F_66dd4 : fetch_word AsanUbsan.M.loaded_segments (0x66e1c : word) = Some W_66dd4.
Proof. vm_refl. Qed.
Lemma D_66dd4 : decode_any W_66dd4 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66dd8 : bv 32 := 0x00e678b3.
Lemma F_66dd8 : fetch_word AsanUbsan.M.loaded_segments (0x66e20 : word) = Some W_66dd8.
Proof. vm_refl. Qed.
Lemma D_66dd8 : decode_any W_66dd8 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ddc : bv 32 := 0x011687b3.
Lemma F_66ddc : fetch_word AsanUbsan.M.loaded_segments (0x66e24 : word) = Some W_66ddc.
Proof. vm_refl. Qed.
Lemma D_66ddc : decode_any W_66ddc = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66de0 : bv 32 := 0x0007c283.
Lemma F_66de0 : fetch_word AsanUbsan.M.loaded_segments (0x66e28 : word) = Some W_66de0.
Proof. vm_refl. Qed.
Lemma D_66de0 : decode_any W_66de0 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66de4 : bv 32 := 0x06028663.
Lemma F_66de4 : fetch_word AsanUbsan.M.loaded_segments (0x66e2c : word) = Some W_66de4.
Proof. vm_refl. Qed.
Lemma D_66de4 : decode_any W_66de4 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66de8 : bv 32 := 0xfff5051b.
Lemma F_66de8 : fetch_word AsanUbsan.M.loaded_segments (0x66e30 : word) = Some W_66de8.
Proof. vm_refl. Qed.
Lemma D_66de8 : decode_any W_66de8 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66dec : bv 32 := 0x00160613.
Lemma F_66dec : fetch_word AsanUbsan.M.loaded_segments (0x66e34 : word) = Some W_66dec.
Proof. vm_refl. Qed.
Lemma D_66dec : decode_any W_66dec = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66df0 : bv 32 := 0xfe0514e3.
Lemma F_66df0 : fetch_word AsanUbsan.M.loaded_segments (0x66e38 : word) = Some W_66df0.
Proof. vm_refl. Qed.
Lemma D_66df0 : decode_any W_66df0 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e50 : bv 32 := 0x00160613.
Lemma F_66e50 : fetch_word AsanUbsan.M.loaded_segments (0x66e98 : word) = Some W_66e50.
Proof. vm_refl. Qed.
Lemma D_66e50 : decode_any W_66e50 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e54 : bv 32 := 0x00100513.
Lemma F_66e54 : fetch_word AsanUbsan.M.loaded_segments (0x66e9c : word) = Some W_66e54.
Proof. vm_refl. Qed.
Lemma D_66e54 : decode_any W_66e54 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e58 : bv 32 := 0xffb90693.
Lemma F_66e58 : fetch_word AsanUbsan.M.loaded_segments (0x66ea0 : word) = Some W_66e58.
Proof. vm_refl. Qed.
Lemma D_66e58 : decode_any W_66e58 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e5c : bv 32 := 0x02c4b023.
Lemma F_66e5c : fetch_word AsanUbsan.M.loaded_segments (0x66ea4 : word) = Some W_66e5c.
Proof. vm_refl. Qed.
Lemma D_66e5c : decode_any W_66e5c = Some (Store SZ8 9 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e60 : bv 32 := 0x00a78023.
Lemma F_66e60 : fetch_word AsanUbsan.M.loaded_segments (0x66ea8 : word) = Some W_66e60.
Proof. vm_refl. Qed.
Lemma D_66e60 : decode_any W_66e60 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e64 : bv 32 := 0x00d51533.
Lemma F_66e64 : fetch_word AsanUbsan.M.loaded_segments (0x66eac : word) = Some W_66e64.
Proof. vm_refl. Qed.
Lemma D_66e64 : decode_any W_66e64 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e68 : bv 32 := 0x00400613.
Lemma F_66e68 : fetch_word AsanUbsan.M.loaded_segments (0x66eb0 : word) = Some W_66e68.
Proof. vm_refl. Qed.
Lemma D_66e68 : decode_any W_66e68 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e6c : bv 32 := 0x00a89893.
Lemma F_66e6c : fetch_word AsanUbsan.M.loaded_segments (0x66eb4 : word) = Some W_66e6c.
Proof. vm_refl. Qed.
Lemma D_66e6c : decode_any W_66e6c = Some (ShiftImm ALU_SLL 17 17 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e70 : bv 32 := 0x01261633.
Lemma F_66e70 : fetch_word AsanUbsan.M.loaded_segments (0x66eb8 : word) = Some W_66e70.
Proof. vm_refl. Qed.
Lemma D_66e70 : decode_any W_66e70 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e74 : bv 32 := 0x00a58533.
Lemma F_66e74 : fetch_word AsanUbsan.M.loaded_segments (0x66ebc : word) = Some W_66e74.
Proof. vm_refl. Qed.
Lemma D_66e74 : decode_any W_66e74 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e78 : bv 32 := 0x01160633.
Lemma F_66e78 : fetch_word AsanUbsan.M.loaded_segments (0x66ec0 : word) = Some W_66e78.
Proof. vm_refl. Qed.
Lemma D_66e78 : decode_any W_66e78 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e7c : bv 32 := 0x00c504b3.
Lemma F_66e7c : fetch_word AsanUbsan.M.loaded_segments (0x66ec4 : word) = Some W_66e7c.
Proof. vm_refl. Qed.
Lemma D_66e7c : decode_any W_66e7c = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e80 : bv 32 := 0x0084bc23.
Lemma F_66e80 : fetch_word AsanUbsan.M.loaded_segments (0x66ec8 : word) = Some W_66e80.
Proof. vm_refl. Qed.
Lemma D_66e80 : decode_any W_66e80 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e84 : bv 32 := 0x3ef4bc23.
Lemma F_66e84 : fetch_word AsanUbsan.M.loaded_segments (0x66ecc : word) = Some W_66e84.
Proof. vm_refl. Qed.
Lemma D_66e84 : decode_any W_66e84 = Some (Store SZ8 9 15 1016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e88 : bv 32 := 0x00048513.
Lemma F_66e88 : fetch_word AsanUbsan.M.loaded_segments (0x66ed0 : word) = Some W_66e88.
Proof. vm_refl. Qed.
Lemma D_66e88 : decode_any W_66e88 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e8c : bv 32 := 0x344000ef.
Lemma F_66e8c : fetch_word AsanUbsan.M.loaded_segments (0x66ed4 : word) = Some W_66e8c.
Proof. vm_refl. Qed.
Lemma D_66e8c : decode_any W_66e8c = Some (Jal 1 836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e90 : bv 32 := 0x00050593.
Lemma F_66e90 : fetch_word AsanUbsan.M.loaded_segments (0x66ed8 : word) = Some W_66e90.
Proof. vm_refl. Qed.
Lemma D_66e90 : decode_any W_66e90 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e94 : bv 32 := 0x00048513.
Lemma F_66e94 : fetch_word AsanUbsan.M.loaded_segments (0x66edc : word) = Some W_66e94.
Proof. vm_refl. Qed.
Lemma D_66e94 : decode_any W_66e94 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e98 : bv 32 := 0x00000613.
Lemma F_66e98 : fetch_word AsanUbsan.M.loaded_segments (0x66ee0 : word) = Some W_66e98.
Proof. vm_refl. Qed.
Lemma D_66e98 : decode_any W_66e98 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66e9c : bv 32 := 0x0005b023.
Lemma F_66e9c : fetch_word AsanUbsan.M.loaded_segments (0x66ee4 : word) = Some W_66e9c.
Proof. vm_refl. Qed.
Lemma D_66e9c : decode_any W_66e9c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ea0 : bv 32 := 0x0005b423.
Lemma F_66ea0 : fetch_word AsanUbsan.M.loaded_segments (0x66ee8 : word) = Some W_66ea0.
Proof. vm_refl. Qed.
Lemma D_66ea0 : decode_any W_66ea0 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ea4 : bv 32 := 0x0005b823.
Lemma F_66ea4 : fetch_word AsanUbsan.M.loaded_segments (0x66eec : word) = Some W_66ea4.
Proof. vm_refl. Qed.
Lemma D_66ea4 : decode_any W_66ea4 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ea8 : bv 32 := 0x0005bc23.
Lemma F_66ea8 : fetch_word AsanUbsan.M.loaded_segments (0x66ef0 : word) = Some W_66ea8.
Proof. vm_refl. Qed.
Lemma D_66ea8 : decode_any W_66ea8 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66eac : bv 32 := 0x0205b023.
Lemma F_66eac : fetch_word AsanUbsan.M.loaded_segments (0x66ef4 : word) = Some W_66eac.
Proof. vm_refl. Qed.
Lemma D_66eac : decode_any W_66eac = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66eb0 : bv 32 := 0x0205b423.
Lemma F_66eb0 : fetch_word AsanUbsan.M.loaded_segments (0x66ef8 : word) = Some W_66eb0.
Proof. vm_refl. Qed.
Lemma D_66eb0 : decode_any W_66eb0 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66eb4 : bv 32 := 0x0205b823.
Lemma F_66eb4 : fetch_word AsanUbsan.M.loaded_segments (0x66efc : word) = Some W_66eb4.
Proof. vm_refl. Qed.
Lemma D_66eb4 : decode_any W_66eb4 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66eb8 : bv 32 := 0x0205bc23.
Lemma F_66eb8 : fetch_word AsanUbsan.M.loaded_segments (0x66f00 : word) = Some W_66eb8.
Proof. vm_refl. Qed.
Lemma D_66eb8 : decode_any W_66eb8 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ebc : bv 32 := 0x0405b023.
Lemma F_66ebc : fetch_word AsanUbsan.M.loaded_segments (0x66f04 : word) = Some W_66ebc.
Proof. vm_refl. Qed.
Lemma D_66ebc : decode_any W_66ebc = Some (Store SZ8 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ec0 : bv 32 := 0x0405b423.
Lemma F_66ec0 : fetch_word AsanUbsan.M.loaded_segments (0x66f08 : word) = Some W_66ec0.
Proof. vm_refl. Qed.
Lemma D_66ec0 : decode_any W_66ec0 = Some (Store SZ8 11 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ec4 : bv 32 := 0x0405b823.
Lemma F_66ec4 : fetch_word AsanUbsan.M.loaded_segments (0x66f0c : word) = Some W_66ec4.
Proof. vm_refl. Qed.
Lemma D_66ec4 : decode_any W_66ec4 = Some (Store SZ8 11 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ec8 : bv 32 := 0x0405bc23.
Lemma F_66ec8 : fetch_word AsanUbsan.M.loaded_segments (0x66f10 : word) = Some W_66ec8.
Proof. vm_refl. Qed.
Lemma D_66ec8 : decode_any W_66ec8 = Some (Store SZ8 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ecc : bv 32 := 0x0605b023.
Lemma F_66ecc : fetch_word AsanUbsan.M.loaded_segments (0x66f14 : word) = Some W_66ecc.
Proof. vm_refl. Qed.
Lemma D_66ecc : decode_any W_66ecc = Some (Store SZ8 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ed0 : bv 32 := 0x0605b423.
Lemma F_66ed0 : fetch_word AsanUbsan.M.loaded_segments (0x66f18 : word) = Some W_66ed0.
Proof. vm_refl. Qed.
Lemma D_66ed0 : decode_any W_66ed0 = Some (Store SZ8 11 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ed4 : bv 32 := 0x0605b823.
Lemma F_66ed4 : fetch_word AsanUbsan.M.loaded_segments (0x66f1c : word) = Some W_66ed4.
Proof. vm_refl. Qed.
Lemma D_66ed4 : decode_any W_66ed4 = Some (Store SZ8 11 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ed8 : bv 32 := 0x0605bc23.
Lemma F_66ed8 : fetch_word AsanUbsan.M.loaded_segments (0x66f20 : word) = Some W_66ed8.
Proof. vm_refl. Qed.
Lemma D_66ed8 : decode_any W_66ed8 = Some (Store SZ8 11 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66edc : bv 32 := 0x01813083.
Lemma F_66edc : fetch_word AsanUbsan.M.loaded_segments (0x66f24 : word) = Some W_66edc.
Proof. vm_refl. Qed.
Lemma D_66edc : decode_any W_66edc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ee0 : bv 32 := 0x01013403.
Lemma F_66ee0 : fetch_word AsanUbsan.M.loaded_segments (0x66f28 : word) = Some W_66ee0.
Proof. vm_refl. Qed.
Lemma D_66ee0 : decode_any W_66ee0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ee4 : bv 32 := 0x00813483.
Lemma F_66ee4 : fetch_word AsanUbsan.M.loaded_segments (0x66f2c : word) = Some W_66ee4.
Proof. vm_refl. Qed.
Lemma D_66ee4 : decode_any W_66ee4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ee8 : bv 32 := 0x00013903.
Lemma F_66ee8 : fetch_word AsanUbsan.M.loaded_segments (0x66f30 : word) = Some W_66ee8.
Proof. vm_refl. Qed.
Lemma D_66ee8 : decode_any W_66ee8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66eec : bv 32 := 0x02010113.
Lemma F_66eec : fetch_word AsanUbsan.M.loaded_segments (0x66f34 : word) = Some W_66eec.
Proof. vm_refl. Qed.
Lemma D_66eec : decode_any W_66eec = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66ef0 : bv 32 := 0x00008067.
Lemma F_66ef0 : fetch_word AsanUbsan.M.loaded_segments (0x66f38 : word) = Some W_66ef0.
Proof. vm_refl. Qed.
Lemma D_66ef0 : decode_any W_66ef0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f10 : bv 32 := 0xfe010113.
Lemma F_66f10 : fetch_word AsanUbsan.M.loaded_segments (0x66f58 : word) = Some W_66f10.
Proof. vm_refl. Qed.
Lemma D_66f10 : decode_any W_66f10 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f14 : bv 32 := 0x00113c23.
Lemma F_66f14 : fetch_word AsanUbsan.M.loaded_segments (0x66f5c : word) = Some W_66f14.
Proof. vm_refl. Qed.
Lemma D_66f14 : decode_any W_66f14 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f18 : bv 32 := 0x00813823.
Lemma F_66f18 : fetch_word AsanUbsan.M.loaded_segments (0x66f60 : word) = Some W_66f18.
Proof. vm_refl. Qed.
Lemma D_66f18 : decode_any W_66f18 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f1c : bv 32 := 0x00913423.
Lemma F_66f1c : fetch_word AsanUbsan.M.loaded_segments (0x66f64 : word) = Some W_66f1c.
Proof. vm_refl. Qed.
Lemma D_66f1c : decode_any W_66f1c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f20 : bv 32 := 0x01213023.
Lemma F_66f20 : fetch_word AsanUbsan.M.loaded_segments (0x66f68 : word) = Some W_66f20.
Proof. vm_refl. Qed.
Lemma D_66f20 : decode_any W_66f20 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f24 : bv 32 := 0x02010413.
Lemma F_66f24 : fetch_word AsanUbsan.M.loaded_segments (0x66f6c : word) = Some W_66f24.
Proof. vm_refl. Qed.
Lemma D_66f24 : decode_any W_66f24 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f28 : bv 32 := 0x000fe517.
Lemma F_66f28 : fetch_word AsanUbsan.M.loaded_segments (0x66f70 : word) = Some W_66f28.
Proof. vm_refl. Qed.
Lemma D_66f28 : decode_any W_66f28 = Some (Auipc 10 254, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f2c : bv 32 := 0x3c850513.
Lemma F_66f2c : fetch_word AsanUbsan.M.loaded_segments (0x66f74 : word) = Some W_66f2c.
Proof. vm_refl. Qed.
Lemma D_66f2c : decode_any W_66f2c = Some (OpImm ALU_ADD 10 10 968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f30 : bv 32 := 0x2f4050ef.
Lemma F_66f30 : fetch_word AsanUbsan.M.loaded_segments (0x66f78 : word) = Some W_66f30.
Proof. vm_refl. Qed.
Lemma D_66f30 : decode_any W_66f30 = Some (Jal 1 21236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f34 : bv 32 := 0x00053483.
Lemma F_66f34 : fetch_word AsanUbsan.M.loaded_segments (0x66f7c : word) = Some W_66f34.
Proof. vm_refl. Qed.
Lemma D_66f34 : decode_any W_66f34 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f38 : bv 32 := 0x08048863.
Lemma F_66f38 : fetch_word AsanUbsan.M.loaded_segments (0x66f80 : word) = Some W_66f38.
Proof. vm_refl. Qed.
Lemma D_66f38 : decode_any W_66f38 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f3c : bv 32 := 0x0604c503.
Lemma F_66f3c : fetch_word AsanUbsan.M.loaded_segments (0x66f84 : word) = Some W_66f3c.
Proof. vm_refl. Qed.
Lemma D_66f3c : decode_any W_66f3c = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f40 : bv 32 := 0x0584b903.
Lemma F_66f40 : fetch_word AsanUbsan.M.loaded_segments (0x66f88 : word) = Some W_66f40.
Proof. vm_refl. Qed.
Lemma D_66f40 : decode_any W_66f40 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f44 : bv 32 := 0x00050863.
Lemma F_66f44 : fetch_word AsanUbsan.M.loaded_segments (0x66f8c : word) = Some W_66f44.
Proof. vm_refl. Qed.
Lemma D_66f44 : decode_any W_66f44 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f48 : bv 32 := 0x00048513.
Lemma F_66f48 : fetch_word AsanUbsan.M.loaded_segments (0x66f90 : word) = Some W_66f48.
Proof. vm_refl. Qed.
Lemma D_66f48 : decode_any W_66f48 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f4c : bv 32 := 0x00040593.
Lemma F_66f4c : fetch_word AsanUbsan.M.loaded_segments (0x66f94 : word) = Some W_66f4c.
Proof. vm_refl. Qed.
Lemma D_66f4c : decode_any W_66f4c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f50 : bv 32 := 0xb5cff0ef.
Lemma F_66f50 : fetch_word AsanUbsan.M.loaded_segments (0x66f98 : word) = Some W_66f50.
Proof. vm_refl. Qed.
Lemma D_66f50 : decode_any W_66f50 = Some (Jal 1 2093916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f54 : bv 32 := 0xff590593.
Lemma F_66f54 : fetch_word AsanUbsan.M.loaded_segments (0x66f9c : word) = Some W_66f54.
Proof. vm_refl. Qed.
Lemma D_66f54 : decode_any W_66f54 = Some (OpImm ALU_ADD 11 18 4085, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f58 : bv 32 := 0x00100513.
Lemma F_66f58 : fetch_word AsanUbsan.M.loaded_segments (0x66fa0 : word) = Some W_66f58.
Proof. vm_refl. Qed.
Lemma D_66f58 : decode_any W_66f58 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f5c : bv 32 := 0x00b51533.
Lemma F_66f5c : fetch_word AsanUbsan.M.loaded_segments (0x66fa4 : word) = Some W_66f5c.
Proof. vm_refl. Qed.
Lemma D_66f5c : decode_any W_66f5c = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f60 : bv 32 := 0x0005061b.
Lemma F_66f60 : fetch_word AsanUbsan.M.loaded_segments (0x66fa8 : word) = Some W_66f60.
Proof. vm_refl. Qed.
Lemma D_66f60 : decode_any W_66f60 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f64 : bv 32 := 0x08c05263.
Lemma F_66f64 : fetch_word AsanUbsan.M.loaded_segments (0x66fac : word) = Some W_66f64.
Proof. vm_refl. Qed.
Lemma D_66f64 : decode_any W_66f64 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f68 : bv 32 := 0x000016b7.
Lemma F_66f68 : fetch_word AsanUbsan.M.loaded_segments (0x66fb0 : word) = Some W_66f68.
Proof. vm_refl. Qed.
Lemma D_66f68 : decode_any W_66f68 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f6c : bv 32 := 0xff190613.
Lemma F_66f6c : fetch_word AsanUbsan.M.loaded_segments (0x66fb4 : word) = Some W_66f6c.
Proof. vm_refl. Qed.
Lemma D_66f6c : decode_any W_66f6c = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f70 : bv 32 := 0x3e000713.
Lemma F_66f70 : fetch_word AsanUbsan.M.loaded_segments (0x66fb8 : word) = Some W_66f70.
Proof. vm_refl. Qed.
Lemma D_66f70 : decode_any W_66f70 = Some (OpImm ALU_ADD 14 0 992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f74 : bv 32 := 0xfff00793.
Lemma F_66f74 : fetch_word AsanUbsan.M.loaded_segments (0x66fbc : word) = Some W_66f74.
Proof. vm_refl. Qed.
Lemma D_66f74 : decode_any W_66f74 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f78 : bv 32 := 0x00c71733.
Lemma F_66f78 : fetch_word AsanUbsan.M.loaded_segments (0x66fc0 : word) = Some W_66f78.
Proof. vm_refl. Qed.
Lemma D_66f78 : decode_any W_66f78 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f7c : bv 32 := 0x0284b603.
Lemma F_66f7c : fetch_word AsanUbsan.M.loaded_segments (0x66fc4 : word) = Some W_66f7c.
Proof. vm_refl. Qed.
Lemma D_66f7c : decode_any W_66f7c = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f80 : bv 32 := 0x00b797b3.
Lemma F_66f80 : fetch_word AsanUbsan.M.loaded_segments (0x66fc8 : word) = Some W_66f80.
Proof. vm_refl. Qed.
Lemma D_66f80 : decode_any W_66f80 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f84 : bv 32 := 0xfff50813.
Lemma F_66f84 : fetch_word AsanUbsan.M.loaded_segments (0x66fcc : word) = Some W_66f84.
Proof. vm_refl. Qed.
Lemma D_66f84 : decode_any W_66f84 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f88 : bv 32 := 0x00d485b3.
Lemma F_66f88 : fetch_word AsanUbsan.M.loaded_segments (0x66fd0 : word) = Some W_66f88.
Proof. vm_refl. Qed.
Lemma D_66f88 : decode_any W_66f88 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f8c : bv 32 := 0x00e586b3.
Lemma F_66f8c : fetch_word AsanUbsan.M.loaded_segments (0x66fd4 : word) = Some W_66f8c.
Proof. vm_refl. Qed.
Lemma D_66f8c : decode_any W_66f8c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f90 : bv 32 := 0xfff7c713.
Lemma F_66f90 : fetch_word AsanUbsan.M.loaded_segments (0x66fd8 : word) = Some W_66f90.
Proof. vm_refl. Qed.
Lemma D_66f90 : decode_any W_66f90 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f94 : bv 32 := 0x02081813.
Lemma F_66f94 : fetch_word AsanUbsan.M.loaded_segments (0x66fdc : word) = Some W_66f94.
Proof. vm_refl. Qed.
Lemma D_66f94 : decode_any W_66f94 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f98 : bv 32 := 0x02085793.
Lemma F_66f98 : fetch_word AsanUbsan.M.loaded_segments (0x66fe0 : word) = Some W_66f98.
Proof. vm_refl. Qed.
Lemma D_66f98 : decode_any W_66f98 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66f9c : bv 32 := 0x00f607b3.
Lemma F_66f9c : fetch_word AsanUbsan.M.loaded_segments (0x66fe4 : word) = Some W_66f9c.
Proof. vm_refl. Qed.
Lemma D_66f9c : decode_any W_66f9c = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fa0 : bv 32 := 0x00178813.
Lemma F_66fa0 : fetch_word AsanUbsan.M.loaded_segments (0x66fe8 : word) = Some W_66fa0.
Proof. vm_refl. Qed.
Lemma D_66fa0 : decode_any W_66fa0 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fa4 : bv 32 := 0x00e678b3.
Lemma F_66fa4 : fetch_word AsanUbsan.M.loaded_segments (0x66fec : word) = Some W_66fa4.
Proof. vm_refl. Qed.
Lemma D_66fa4 : decode_any W_66fa4 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fa8 : bv 32 := 0x011687b3.
Lemma F_66fa8 : fetch_word AsanUbsan.M.loaded_segments (0x66ff0 : word) = Some W_66fa8.
Proof. vm_refl. Qed.
Lemma D_66fa8 : decode_any W_66fa8 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fac : bv 32 := 0x0007c283.
Lemma F_66fac : fetch_word AsanUbsan.M.loaded_segments (0x66ff4 : word) = Some W_66fac.
Proof. vm_refl. Qed.
Lemma D_66fac : decode_any W_66fac = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fb0 : bv 32 := 0x06028663.
Lemma F_66fb0 : fetch_word AsanUbsan.M.loaded_segments (0x66ff8 : word) = Some W_66fb0.
Proof. vm_refl. Qed.
Lemma D_66fb0 : decode_any W_66fb0 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fb4 : bv 32 := 0xfff5051b.
Lemma F_66fb4 : fetch_word AsanUbsan.M.loaded_segments (0x66ffc : word) = Some W_66fb4.
Proof. vm_refl. Qed.
Lemma D_66fb4 : decode_any W_66fb4 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fb8 : bv 32 := 0x00160613.
Lemma F_66fb8 : fetch_word AsanUbsan.M.loaded_segments (0x67000 : word) = Some W_66fb8.
Proof. vm_refl. Qed.
Lemma D_66fb8 : decode_any W_66fb8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66fbc : bv 32 := 0xfe0514e3.
Lemma F_66fbc : fetch_word AsanUbsan.M.loaded_segments (0x67004 : word) = Some W_66fbc.
Proof. vm_refl. Qed.
Lemma D_66fbc : decode_any W_66fbc = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

