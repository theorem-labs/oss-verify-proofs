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
Definition Wx_15637c : bv 32 := 0xe451506f.
Lemma Fx_15637c : fetch_word AsanUbsan.M.loaded_segments (0x1563b8 : word) = Some Wx_15637c.
Proof. vm_refl. Qed.
Lemma Dx_15637c : decode_any Wx_15637c = Some (Jal 0 1138244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_15644c : bv 32 := 0x02060063.
Lemma Fx_15644c : fetch_word AsanUbsan.M.loaded_segments (0x156488 : word) = Some Wx_15644c.
Proof. vm_refl. Qed.
Lemma Dx_15644c : decode_any Wx_15644c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_156450 : bv 32 := 0x00054683.
Lemma Fx_156450 : fetch_word AsanUbsan.M.loaded_segments (0x15648c : word) = Some Wx_156450.
Proof. vm_refl. Qed.
Lemma Dx_156450 : decode_any Wx_156450 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_156454 : bv 32 := 0x0005c703.
Lemma Fx_156454 : fetch_word AsanUbsan.M.loaded_segments (0x156490 : word) = Some Wx_156454.
Proof. vm_refl. Qed.
Lemma Dx_156454 : decode_any Wx_156454 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_156458 : bv 32 := 0x00e69e63.
Lemma Fx_156458 : fetch_word AsanUbsan.M.loaded_segments (0x156494 : word) = Some Wx_156458.
Proof. vm_refl. Qed.
Lemma Dx_156458 : decode_any Wx_156458 = Some (Branch BC_NE 13 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_15645c : bv 32 := 0xfff60613.
Lemma Fx_15645c : fetch_word AsanUbsan.M.loaded_segments (0x156498 : word) = Some Wx_15645c.
Proof. vm_refl. Qed.
Lemma Dx_15645c : decode_any Wx_15645c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_156460 : bv 32 := 0x00150513.
Lemma Fx_156460 : fetch_word AsanUbsan.M.loaded_segments (0x15649c : word) = Some Wx_156460.
Proof. vm_refl. Qed.
Lemma Dx_156460 : decode_any Wx_156460 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_156464 : bv 32 := 0x00158593.
Lemma Fx_156464 : fetch_word AsanUbsan.M.loaded_segments (0x1564a0 : word) = Some Wx_156464.
Proof. vm_refl. Qed.
Lemma Dx_156464 : decode_any Wx_156464 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_156468 : bv 32 := 0xfe0614e3.
Lemma Fx_156468 : fetch_word AsanUbsan.M.loaded_segments (0x1564a4 : word) = Some Wx_156468.
Proof. vm_refl. Qed.
Lemma Dx_156468 : decode_any Wx_156468 = Some (Branch BC_NE 12 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_15646c : bv 32 := 0x00000513.
Lemma Fx_15646c : fetch_word AsanUbsan.M.loaded_segments (0x1564a8 : word) = Some Wx_15646c.
Proof. vm_refl. Qed.
Lemma Dx_15646c : decode_any Wx_15646c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_156470 : bv 32 := 0x00008067.
Lemma Fx_156470 : fetch_word AsanUbsan.M.loaded_segments (0x1564ac : word) = Some Wx_156470.
Proof. vm_refl. Qed.
Lemma Dx_156470 : decode_any Wx_156470 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_156474 : bv 32 := 0x40e68533.
Lemma Fx_156474 : fetch_word AsanUbsan.M.loaded_segments (0x1564b0 : word) = Some Wx_156474.
Proof. vm_refl. Qed.
Lemma Dx_156474 : decode_any Wx_156474 = Some (Op ALU_SUB 10 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_156478 : bv 32 := 0x00008067.
Lemma Fx_156478 : fetch_word AsanUbsan.M.loaded_segments (0x1564b4 : word) = Some Wx_156478.
Proof. vm_refl. Qed.
Lemma Dx_156478 : decode_any Wx_156478 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_6c1b4 : bv 32 := 0x32d0106f.
Lemma Fx_6c1b4 : fetch_word AsanUbsan.M.loaded_segments (0x6c1fc : word) = Some Wx_6c1b4.
Proof. vm_refl. Qed.
Lemma Dx_6c1b4 : decode_any Wx_6c1b4 = Some (Jal 0 6956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6c1b8 : bv 32 := 0x3e50106f.
Lemma Fx_6c1b8 : fetch_word AsanUbsan.M.loaded_segments (0x6c200 : word) = Some Wx_6c1b8.
Proof. vm_refl. Qed.
Lemma Dx_6c1b8 : decode_any Wx_6c1b8 = Some (Jal 0 7140, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_6d448 : bv 32 := 0x00008067.
Lemma Fx_6d448 : fetch_word AsanUbsan.M.loaded_segments (0x6d490 : word) = Some Wx_6d448.
Proof. vm_refl. Qed.
Lemma Dx_6d448 : decode_any Wx_6d448 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d44c : bv 32 := 0x81010113.
Lemma Fx_6d44c : fetch_word AsanUbsan.M.loaded_segments (0x6d494 : word) = Some Wx_6d44c.
Proof. vm_refl. Qed.
Lemma Dx_6d44c : decode_any Wx_6d44c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d450 : bv 32 := 0x7e113423.
Lemma Fx_6d450 : fetch_word AsanUbsan.M.loaded_segments (0x6d498 : word) = Some Wx_6d450.
Proof. vm_refl. Qed.
Lemma Dx_6d450 : decode_any Wx_6d450 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d454 : bv 32 := 0x7e813023.
Lemma Fx_6d454 : fetch_word AsanUbsan.M.loaded_segments (0x6d49c : word) = Some Wx_6d454.
Proof. vm_refl. Qed.
Lemma Dx_6d454 : decode_any Wx_6d454 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d458 : bv 32 := 0x7c913c23.
Lemma Fx_6d458 : fetch_word AsanUbsan.M.loaded_segments (0x6d4a0 : word) = Some Wx_6d458.
Proof. vm_refl. Qed.
Lemma Dx_6d458 : decode_any Wx_6d458 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d45c : bv 32 := 0x7d213823.
Lemma Fx_6d45c : fetch_word AsanUbsan.M.loaded_segments (0x6d4a4 : word) = Some Wx_6d45c.
Proof. vm_refl. Qed.
Lemma Dx_6d45c : decode_any Wx_6d45c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d460 : bv 32 := 0x7d313423.
Lemma Fx_6d460 : fetch_word AsanUbsan.M.loaded_segments (0x6d4a8 : word) = Some Wx_6d460.
Proof. vm_refl. Qed.
Lemma Dx_6d460 : decode_any Wx_6d460 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d464 : bv 32 := 0x7d413023.
Lemma Fx_6d464 : fetch_word AsanUbsan.M.loaded_segments (0x6d4ac : word) = Some Wx_6d464.
Proof. vm_refl. Qed.
Lemma Dx_6d464 : decode_any Wx_6d464 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d468 : bv 32 := 0x7b513c23.
Lemma Fx_6d468 : fetch_word AsanUbsan.M.loaded_segments (0x6d4b0 : word) = Some Wx_6d468.
Proof. vm_refl. Qed.
Lemma Dx_6d468 : decode_any Wx_6d468 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d46c : bv 32 := 0x7b613823.
Lemma Fx_6d46c : fetch_word AsanUbsan.M.loaded_segments (0x6d4b4 : word) = Some Wx_6d46c.
Proof. vm_refl. Qed.
Lemma Dx_6d46c : decode_any Wx_6d46c = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d470 : bv 32 := 0x7b713423.
Lemma Fx_6d470 : fetch_word AsanUbsan.M.loaded_segments (0x6d4b8 : word) = Some Wx_6d470.
Proof. vm_refl. Qed.
Lemma Dx_6d470 : decode_any Wx_6d470 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d474 : bv 32 := 0x7b813023.
Lemma Fx_6d474 : fetch_word AsanUbsan.M.loaded_segments (0x6d4bc : word) = Some Wx_6d474.
Proof. vm_refl. Qed.
Lemma Dx_6d474 : decode_any Wx_6d474 = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d478 : bv 32 := 0x79913c23.
Lemma Fx_6d478 : fetch_word AsanUbsan.M.loaded_segments (0x6d4c0 : word) = Some Wx_6d478.
Proof. vm_refl. Qed.
Lemma Dx_6d478 : decode_any Wx_6d478 = Some (Store SZ8 2 25 1944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d47c : bv 32 := 0x79a13823.
Lemma Fx_6d47c : fetch_word AsanUbsan.M.loaded_segments (0x6d4c4 : word) = Some Wx_6d47c.
Proof. vm_refl. Qed.
Lemma Dx_6d47c : decode_any Wx_6d47c = Some (Store SZ8 2 26 1936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d480 : bv 32 := 0x79b13423.
Lemma Fx_6d480 : fetch_word AsanUbsan.M.loaded_segments (0x6d4c8 : word) = Some Wx_6d480.
Proof. vm_refl. Qed.
Lemma Dx_6d480 : decode_any Wx_6d480 = Some (Store SZ8 2 27 1928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d484 : bv 32 := 0x7f010413.
Lemma Fx_6d484 : fetch_word AsanUbsan.M.loaded_segments (0x6d4cc : word) = Some Wx_6d484.
Proof. vm_refl. Qed.
Lemma Dx_6d484 : decode_any Wx_6d484 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d488 : bv 32 := 0xf6010113.
Lemma Fx_6d488 : fetch_word AsanUbsan.M.loaded_segments (0x6d4d0 : word) = Some Wx_6d488.
Proof. vm_refl. Qed.
Lemma Dx_6d488 : decode_any Wx_6d488 = Some (OpImm ALU_ADD 2 2 3936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d48c : bv 32 := 0x00008993.
Lemma Fx_6d48c : fetch_word AsanUbsan.M.loaded_segments (0x6d4d4 : word) = Some Wx_6d48c.
Proof. vm_refl. Qed.
Lemma Dx_6d48c : decode_any Wx_6d48c = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d490 : bv 32 := 0x00070493.
Lemma Fx_6d490 : fetch_word AsanUbsan.M.loaded_segments (0x6d4d8 : word) = Some Wx_6d490.
Proof. vm_refl. Qed.
Lemma Dx_6d490 : decode_any Wx_6d490 = Some (OpImm ALU_ADD 9 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d494 : bv 32 := 0x00068913.
Lemma Fx_6d494 : fetch_word AsanUbsan.M.loaded_segments (0x6d4dc : word) = Some Wx_6d494.
Proof. vm_refl. Qed.
Lemma Dx_6d494 : decode_any Wx_6d494 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d498 : bv 32 := 0x00060a13.
Lemma Fx_6d498 : fetch_word AsanUbsan.M.loaded_segments (0x6d4e0 : word) = Some Wx_6d498.
Proof. vm_refl. Qed.
Lemma Dx_6d498 : decode_any Wx_6d498 = Some (OpImm ALU_ADD 20 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d49c : bv 32 := 0x00058a93.
Lemma Fx_6d49c : fetch_word AsanUbsan.M.loaded_segments (0x6d4e4 : word) = Some Wx_6d49c.
Proof. vm_refl. Qed.
Lemma Dx_6d49c : decode_any Wx_6d49c = Some (OpImm ALU_ADD 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4a0 : bv 32 := 0x000f7597.
Lemma Fx_6d4a0 : fetch_word AsanUbsan.M.loaded_segments (0x6d4e8 : word) = Some Wx_6d4a0.
Proof. vm_refl. Qed.
Lemma Dx_6d4a0 : decode_any Wx_6d4a0 = Some (Auipc 11 247, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4a4 : bv 32 := 0x0205bc03.
Lemma Fx_6d4a4 : fetch_word AsanUbsan.M.loaded_segments (0x6d4ec : word) = Some Wx_6d4a4.
Proof. vm_refl. Qed.
Lemma Dx_6d4a4 : decode_any Wx_6d4a4 = Some (Load SZ8 true 24 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4a8 : bv 32 := 0x0fec4583.
Lemma Fx_6d4a8 : fetch_word AsanUbsan.M.loaded_segments (0x6d4f0 : word) = Some Wx_6d4a8.
Proof. vm_refl. Qed.
Lemma Dx_6d4a8 : decode_any Wx_6d4a8 = Some (Load SZ1 false 11 24 254, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4ac : bv 32 := 0x0a058863.
Lemma Fx_6d4ac : fetch_word AsanUbsan.M.loaded_segments (0x6d4f4 : word) = Some Wx_6d4ac.
Proof. vm_refl. Qed.
Lemma Dx_6d4ac : decode_any Wx_6d4ac = Some (Branch BC_EQ 11 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4b0 : bv 32 := 0x0ffc4583.
Lemma Fx_6d4b0 : fetch_word AsanUbsan.M.loaded_segments (0x6d4f8 : word) = Some Wx_6d4b0.
Proof. vm_refl. Qed.
Lemma Dx_6d4b0 : decode_any Wx_6d4b0 = Some (Load SZ1 false 11 24 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4b4 : bv 32 := 0x80040b93.
Lemma Fx_6d4b4 : fetch_word AsanUbsan.M.loaded_segments (0x6d4fc : word) = Some Wx_6d4b4.
Proof. vm_refl. Qed.
Lemma Dx_6d4b4 : decode_any Wx_6d4b4 = Some (OpImm ALU_ADD 23 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4b8 : bv 32 := 0xf80b8b93.
Lemma Fx_6d4b8 : fetch_word AsanUbsan.M.loaded_segments (0x6d500 : word) = Some Wx_6d4b8.
Proof. vm_refl. Qed.
Lemma Dx_6d4b8 : decode_any Wx_6d4b8 = Some (OpImm ALU_ADD 23 23 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4bc : bv 32 := 0x0a058c63.
Lemma Fx_6d4bc : fetch_word AsanUbsan.M.loaded_segments (0x6d504 : word) = Some Wx_6d4bc.
Proof. vm_refl. Qed.
Lemma Dx_6d4bc : decode_any Wx_6d4bc = Some (Branch BC_EQ 11 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4c0 : bv 32 := 0xfffa4593.
Lemma Fx_6d4c0 : fetch_word AsanUbsan.M.loaded_segments (0x6d508 : word) = Some Wx_6d4c0.
Proof. vm_refl. Qed.
Lemma Dx_6d4c0 : decode_any Wx_6d4c0 = Some (OpImm ALU_XOR 11 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4c4 : bv 32 := 0x2095e063.
Lemma Fx_6d4c4 : fetch_word AsanUbsan.M.loaded_segments (0x6d50c : word) = Some Wx_6d4c4.
Proof. vm_refl. Qed.
Lemma Dx_6d4c4 : decode_any Wx_6d4c4 = Some (Branch BC_LTU 11 9 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4c8 : bv 32 := 0xfbf48c93.
Lemma Fx_6d4c8 : fetch_word AsanUbsan.M.loaded_segments (0x6d510 : word) = Some Wx_6d4c8.
Proof. vm_refl. Qed.
Lemma Dx_6d4c8 : decode_any Wx_6d4c8 = Some (OpImm ALU_ADD 25 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4cc : bv 32 := 0xfbf00593.
Lemma Fx_6d4cc : fetch_word AsanUbsan.M.loaded_segments (0x6d514 : word) = Some Wx_6d4cc.
Proof. vm_refl. Qed.
Lemma Dx_6d4cc : decode_any Wx_6d4cc = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4d0 : bv 32 := 0x2795f263.
Lemma Fx_6d4d0 : fetch_word AsanUbsan.M.loaded_segments (0x6d518 : word) = Some Wx_6d4d0.
Proof. vm_refl. Qed.
Lemma Dx_6d4d0 : decode_any Wx_6d4d0 = Some (Branch BC_GEU 11 25 612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4d4 : bv 32 := 0x000f7597.
Lemma Fx_6d4d4 : fetch_word AsanUbsan.M.loaded_segments (0x6d51c : word) = Some Wx_6d4d4.
Proof. vm_refl. Qed.
Lemma Dx_6d4d4 : decode_any Wx_6d4d4 = Some (Auipc 11 247, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4d8 : bv 32 := 0xffc5b583.
Lemma Fx_6d4d8 : fetch_word AsanUbsan.M.loaded_segments (0x6d520 : word) = Some Wx_6d4d8.
Proof. vm_refl. Qed.
Lemma Dx_6d4d8 : decode_any Wx_6d4d8 = Some (Load SZ8 true 11 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4dc : bv 32 := 0x009a06b3.
Lemma Fx_6d4dc : fetch_word AsanUbsan.M.loaded_segments (0x6d524 : word) = Some Wx_6d4dc.
Proof. vm_refl. Qed.
Lemma Dx_6d4dc : decode_any Wx_6d4dc = Some (Op ALU_ADD 13 20 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4e0 : bv 32 := 0x0005b603.
Lemma Fx_6d4e0 : fetch_word AsanUbsan.M.loaded_segments (0x6d528 : word) = Some Wx_6d4e0.
Proof. vm_refl. Qed.
Lemma Dx_6d4e0 : decode_any Wx_6d4e0 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4e4 : bv 32 := 0x003a5593.
Lemma Fx_6d4e4 : fetch_word AsanUbsan.M.loaded_segments (0x6d52c : word) = Some Wx_6d4e4.
Proof. vm_refl. Qed.
Lemma Dx_6d4e4 : decode_any Wx_6d4e4 = Some (ShiftImm ALU_SRL 11 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4e8 : bv 32 := 0xfff68693.
Lemma Fx_6d4e8 : fetch_word AsanUbsan.M.loaded_segments (0x6d530 : word) = Some Wx_6d4e8.
Proof. vm_refl. Qed.
Lemma Dx_6d4e8 : decode_any Wx_6d4e8 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4ec : bv 32 := 0x0036d713.
Lemma Fx_6d4ec : fetch_word AsanUbsan.M.loaded_segments (0x6d534 : word) = Some Wx_6d4ec.
Proof. vm_refl. Qed.
Lemma Dx_6d4ec : decode_any Wx_6d4ec = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4f0 : bv 32 := 0x00b605b3.
Lemma Fx_6d4f0 : fetch_word AsanUbsan.M.loaded_segments (0x6d538 : word) = Some Wx_6d4f0.
Proof. vm_refl. Qed.
Lemma Dx_6d4f0 : decode_any Wx_6d4f0 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4f4 : bv 32 := 0x00e60633.
Lemma Fx_6d4f4 : fetch_word AsanUbsan.M.loaded_segments (0x6d53c : word) = Some Wx_6d4f4.
Proof. vm_refl. Qed.
Lemma Dx_6d4f4 : decode_any Wx_6d4f4 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4f8 : bv 32 := 0xff85f713.
Lemma Fx_6d4f8 : fetch_word AsanUbsan.M.loaded_segments (0x6d540 : word) = Some Wx_6d4f8.
Proof. vm_refl. Qed.
Lemma Dx_6d4f8 : decode_any Wx_6d4f8 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d4fc : bv 32 := 0xff867793.
Lemma Fx_6d4fc : fetch_word AsanUbsan.M.loaded_segments (0x6d544 : word) = Some Wx_6d4fc.
Proof. vm_refl. Qed.
Lemma Dx_6d4fc : decode_any Wx_6d4fc = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d500 : bv 32 := 0x00073703.
Lemma Fx_6d500 : fetch_word AsanUbsan.M.loaded_segments (0x6d548 : word) = Some Wx_6d500.
Proof. vm_refl. Qed.
Lemma Dx_6d500 : decode_any Wx_6d500 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d504 : bv 32 := 0x0007b783.
Lemma Fx_6d504 : fetch_word AsanUbsan.M.loaded_segments (0x6d54c : word) = Some Wx_6d504.
Proof. vm_refl. Qed.
Lemma Dx_6d504 : decode_any Wx_6d504 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d508 : bv 32 := 0x00e7e733.
Lemma Fx_6d508 : fetch_word AsanUbsan.M.loaded_segments (0x6d550 : word) = Some Wx_6d508.
Proof. vm_refl. Qed.
Lemma Dx_6d508 : decode_any Wx_6d508 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d50c : bv 32 := 0x3a071063.
Lemma Fx_6d50c : fetch_word AsanUbsan.M.loaded_segments (0x6d554 : word) = Some Wx_6d50c.
Proof. vm_refl. Qed.
Lemma Dx_6d50c : decode_any Wx_6d50c = Some (Branch BC_NE 14 0 928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d510 : bv 32 := 0xfff94593.
Lemma Fx_6d510 : fetch_word AsanUbsan.M.loaded_segments (0x6d558 : word) = Some Wx_6d510.
Proof. vm_refl. Qed.
Lemma Dx_6d510 : decode_any Wx_6d510 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d514 : bv 32 := 0x2295e463.
Lemma Fx_6d514 : fetch_word AsanUbsan.M.loaded_segments (0x6d55c : word) = Some Wx_6d514.
Proof. vm_refl. Qed.
Lemma Dx_6d514 : decode_any Wx_6d514 = Some (Branch BC_LTU 11 9 552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d518 : bv 32 := 0xfbf00593.
Lemma Fx_6d518 : fetch_word AsanUbsan.M.loaded_segments (0x6d560 : word) = Some Wx_6d518.
Proof. vm_refl. Qed.
Lemma Dx_6d518 : decode_any Wx_6d518 = Some (OpImm ALU_ADD 11 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d51c : bv 32 := 0x2995f663.
Lemma Fx_6d51c : fetch_word AsanUbsan.M.loaded_segments (0x6d564 : word) = Some Wx_6d51c.
Proof. vm_refl. Qed.
Lemma Dx_6d51c : decode_any Wx_6d51c = Some (Branch BC_GEU 11 25 652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d520 : bv 32 := 0x000f7597.
Lemma Fx_6d520 : fetch_word AsanUbsan.M.loaded_segments (0x6d568 : word) = Some Wx_6d520.
Proof. vm_refl. Qed.
Lemma Dx_6d520 : decode_any Wx_6d520 = Some (Auipc 11 247, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d524 : bv 32 := 0xfb05b583.
Lemma Fx_6d524 : fetch_word AsanUbsan.M.loaded_segments (0x6d56c : word) = Some Wx_6d524.
Proof. vm_refl. Qed.
Lemma Dx_6d524 : decode_any Wx_6d524 = Some (Load SZ8 true 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d528 : bv 32 := 0x009906b3.
Lemma Fx_6d528 : fetch_word AsanUbsan.M.loaded_segments (0x6d570 : word) = Some Wx_6d528.
Proof. vm_refl. Qed.
Lemma Dx_6d528 : decode_any Wx_6d528 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d52c : bv 32 := 0x0005b603.
Lemma Fx_6d52c : fetch_word AsanUbsan.M.loaded_segments (0x6d574 : word) = Some Wx_6d52c.
Proof. vm_refl. Qed.
Lemma Dx_6d52c : decode_any Wx_6d52c = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d530 : bv 32 := 0x00395593.
Lemma Fx_6d530 : fetch_word AsanUbsan.M.loaded_segments (0x6d578 : word) = Some Wx_6d530.
Proof. vm_refl. Qed.
Lemma Dx_6d530 : decode_any Wx_6d530 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d534 : bv 32 := 0xfff68693.
Lemma Fx_6d534 : fetch_word AsanUbsan.M.loaded_segments (0x6d57c : word) = Some Wx_6d534.
Proof. vm_refl. Qed.
Lemma Dx_6d534 : decode_any Wx_6d534 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d538 : bv 32 := 0x0036d713.
Lemma Fx_6d538 : fetch_word AsanUbsan.M.loaded_segments (0x6d580 : word) = Some Wx_6d538.
Proof. vm_refl. Qed.
Lemma Dx_6d538 : decode_any Wx_6d538 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d53c : bv 32 := 0x00b605b3.
Lemma Fx_6d53c : fetch_word AsanUbsan.M.loaded_segments (0x6d584 : word) = Some Wx_6d53c.
Proof. vm_refl. Qed.
Lemma Dx_6d53c : decode_any Wx_6d53c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d540 : bv 32 := 0x00e60633.
Lemma Fx_6d540 : fetch_word AsanUbsan.M.loaded_segments (0x6d588 : word) = Some Wx_6d540.
Proof. vm_refl. Qed.
Lemma Dx_6d540 : decode_any Wx_6d540 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d544 : bv 32 := 0xff85f713.
Lemma Fx_6d544 : fetch_word AsanUbsan.M.loaded_segments (0x6d58c : word) = Some Wx_6d544.
Proof. vm_refl. Qed.
Lemma Dx_6d544 : decode_any Wx_6d544 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d548 : bv 32 := 0xff867793.
Lemma Fx_6d548 : fetch_word AsanUbsan.M.loaded_segments (0x6d590 : word) = Some Wx_6d548.
Proof. vm_refl. Qed.
Lemma Dx_6d548 : decode_any Wx_6d548 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d54c : bv 32 := 0x00073703.
Lemma Fx_6d54c : fetch_word AsanUbsan.M.loaded_segments (0x6d594 : word) = Some Wx_6d54c.
Proof. vm_refl. Qed.
Lemma Dx_6d54c : decode_any Wx_6d54c = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d550 : bv 32 := 0x0007b783.
Lemma Fx_6d550 : fetch_word AsanUbsan.M.loaded_segments (0x6d598 : word) = Some Wx_6d550.
Proof. vm_refl. Qed.
Lemma Dx_6d550 : decode_any Wx_6d550 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d554 : bv 32 := 0x00e7e733.
Lemma Fx_6d554 : fetch_word AsanUbsan.M.loaded_segments (0x6d59c : word) = Some Wx_6d554.
Proof. vm_refl. Qed.
Lemma Dx_6d554 : decode_any Wx_6d554 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d558 : bv 32 := 0x46071063.
Lemma Fx_6d558 : fetch_word AsanUbsan.M.loaded_segments (0x6d5a0 : word) = Some Wx_6d558.
Proof. vm_refl. Qed.
Lemma Dx_6d558 : decode_any Wx_6d558 = Some (Branch BC_NE 14 0 1120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d55c : bv 32 := 0x000a0513.
Lemma Fx_6d55c : fetch_word AsanUbsan.M.loaded_segments (0x6d5a4 : word) = Some Wx_6d55c.
Proof. vm_refl. Qed.
Lemma Dx_6d55c : decode_any Wx_6d55c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d560 : bv 32 := 0x00090593.
Lemma Fx_6d560 : fetch_word AsanUbsan.M.loaded_segments (0x6d5a8 : word) = Some Wx_6d560.
Proof. vm_refl. Qed.
Lemma Dx_6d560 : decode_any Wx_6d560 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d564 : bv 32 := 0x00048613.
Lemma Fx_6d564 : fetch_word AsanUbsan.M.loaded_segments (0x6d5ac : word) = Some Wx_6d564.
Proof. vm_refl. Qed.
Lemma Dx_6d564 : decode_any Wx_6d564 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d568 : bv 32 := 0x000a80e7.
Lemma Fx_6d568 : fetch_word AsanUbsan.M.loaded_segments (0x6d5b0 : word) = Some Wx_6d568.
Proof. vm_refl. Qed.
Lemma Dx_6d568 : decode_any Wx_6d568 = Some (Jalr 1 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d56c : bv 32 := 0x00050a93.
Lemma Fx_6d56c : fetch_word AsanUbsan.M.loaded_segments (0x6d5b4 : word) = Some Wx_6d56c.
Proof. vm_refl. Qed.
Lemma Dx_6d56c : decode_any Wx_6d56c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d570 : bv 32 := 0x0e40006f.
Lemma Fx_6d570 : fetch_word AsanUbsan.M.loaded_segments (0x6d5b8 : word) = Some Wx_6d570.
Proof. vm_refl. Qed.
Lemma Dx_6d570 : decode_any Wx_6d570 = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d654 : bv 32 := 0x00098513.
Lemma Fx_6d654 : fetch_word AsanUbsan.M.loaded_segments (0x6d69c : word) = Some Wx_6d654.
Proof. vm_refl. Qed.
Lemma Dx_6d654 : decode_any Wx_6d654 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d658 : bv 32 := 0x000a0593.
Lemma Fx_6d658 : fetch_word AsanUbsan.M.loaded_segments (0x6d6a0 : word) = Some Wx_6d658.
Proof. vm_refl. Qed.
Lemma Dx_6d658 : decode_any Wx_6d658 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d65c : bv 32 := 0x00090613.
Lemma Fx_6d65c : fetch_word AsanUbsan.M.loaded_segments (0x6d6a4 : word) = Some Wx_6d65c.
Proof. vm_refl. Qed.
Lemma Dx_6d65c : decode_any Wx_6d65c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d660 : bv 32 := 0x00048693.
Lemma Fx_6d660 : fetch_word AsanUbsan.M.loaded_segments (0x6d6a8 : word) = Some Wx_6d660.
Proof. vm_refl. Qed.
Lemma Dx_6d660 : decode_any Wx_6d660 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d664 : bv 32 := 0x000a8713.
Lemma Fx_6d664 : fetch_word AsanUbsan.M.loaded_segments (0x6d6ac : word) = Some Wx_6d664.
Proof. vm_refl. Qed.
Lemma Dx_6d664 : decode_any Wx_6d664 = Some (OpImm ALU_ADD 14 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d668 : bv 32 := 0xde1ff0ef.
Lemma Fx_6d668 : fetch_word AsanUbsan.M.loaded_segments (0x6d6b0 : word) = Some Wx_6d668.
Proof. vm_refl. Qed.
Lemma Dx_6d668 : decode_any Wx_6d668 = Some (Jal 1 2096608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d66c : bv 32 := 0x000a8513.
Lemma Fx_6d66c : fetch_word AsanUbsan.M.loaded_segments (0x6d6b4 : word) = Some Wx_6d66c.
Proof. vm_refl. Qed.
Lemma Dx_6d66c : decode_any Wx_6d66c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d670 : bv 32 := 0x0a010113.
Lemma Fx_6d670 : fetch_word AsanUbsan.M.loaded_segments (0x6d6b8 : word) = Some Wx_6d670.
Proof. vm_refl. Qed.
Lemma Dx_6d670 : decode_any Wx_6d670 = Some (OpImm ALU_ADD 2 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d674 : bv 32 := 0x7e813083.
Lemma Fx_6d674 : fetch_word AsanUbsan.M.loaded_segments (0x6d6bc : word) = Some Wx_6d674.
Proof. vm_refl. Qed.
Lemma Dx_6d674 : decode_any Wx_6d674 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d678 : bv 32 := 0x7e013403.
Lemma Fx_6d678 : fetch_word AsanUbsan.M.loaded_segments (0x6d6c0 : word) = Some Wx_6d678.
Proof. vm_refl. Qed.
Lemma Dx_6d678 : decode_any Wx_6d678 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d67c : bv 32 := 0x7d813483.
Lemma Fx_6d67c : fetch_word AsanUbsan.M.loaded_segments (0x6d6c4 : word) = Some Wx_6d67c.
Proof. vm_refl. Qed.
Lemma Dx_6d67c : decode_any Wx_6d67c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d680 : bv 32 := 0x7d013903.
Lemma Fx_6d680 : fetch_word AsanUbsan.M.loaded_segments (0x6d6c8 : word) = Some Wx_6d680.
Proof. vm_refl. Qed.
Lemma Dx_6d680 : decode_any Wx_6d680 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d684 : bv 32 := 0x7c813983.
Lemma Fx_6d684 : fetch_word AsanUbsan.M.loaded_segments (0x6d6cc : word) = Some Wx_6d684.
Proof. vm_refl. Qed.
Lemma Dx_6d684 : decode_any Wx_6d684 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d688 : bv 32 := 0x7c013a03.
Lemma Fx_6d688 : fetch_word AsanUbsan.M.loaded_segments (0x6d6d0 : word) = Some Wx_6d688.
Proof. vm_refl. Qed.
Lemma Dx_6d688 : decode_any Wx_6d688 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d68c : bv 32 := 0x7b813a83.
Lemma Fx_6d68c : fetch_word AsanUbsan.M.loaded_segments (0x6d6d4 : word) = Some Wx_6d68c.
Proof. vm_refl. Qed.
Lemma Dx_6d68c : decode_any Wx_6d68c = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d690 : bv 32 := 0x7b013b03.
Lemma Fx_6d690 : fetch_word AsanUbsan.M.loaded_segments (0x6d6d8 : word) = Some Wx_6d690.
Proof. vm_refl. Qed.
Lemma Dx_6d690 : decode_any Wx_6d690 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d694 : bv 32 := 0x7a813b83.
Lemma Fx_6d694 : fetch_word AsanUbsan.M.loaded_segments (0x6d6dc : word) = Some Wx_6d694.
Proof. vm_refl. Qed.
Lemma Dx_6d694 : decode_any Wx_6d694 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d698 : bv 32 := 0x7a013c03.
Lemma Fx_6d698 : fetch_word AsanUbsan.M.loaded_segments (0x6d6e0 : word) = Some Wx_6d698.
Proof. vm_refl. Qed.
Lemma Dx_6d698 : decode_any Wx_6d698 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d69c : bv 32 := 0x79813c83.
Lemma Fx_6d69c : fetch_word AsanUbsan.M.loaded_segments (0x6d6e4 : word) = Some Wx_6d69c.
Proof. vm_refl. Qed.
Lemma Dx_6d69c : decode_any Wx_6d69c = Some (Load SZ8 true 25 2 1944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d6a0 : bv 32 := 0x79013d03.
Lemma Fx_6d6a0 : fetch_word AsanUbsan.M.loaded_segments (0x6d6e8 : word) = Some Wx_6d6a0.
Proof. vm_refl. Qed.
Lemma Dx_6d6a0 : decode_any Wx_6d6a0 = Some (Load SZ8 true 26 2 1936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d6a4 : bv 32 := 0x78813d83.
Lemma Fx_6d6a4 : fetch_word AsanUbsan.M.loaded_segments (0x6d6ec : word) = Some Wx_6d6a4.
Proof. vm_refl. Qed.
Lemma Dx_6d6a4 : decode_any Wx_6d6a4 = Some (Load SZ8 true 27 2 1928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d6a8 : bv 32 := 0x7f010113.
Lemma Fx_6d6a8 : fetch_word AsanUbsan.M.loaded_segments (0x6d6f0 : word) = Some Wx_6d6a8.
Proof. vm_refl. Qed.
Lemma Dx_6d6a8 : decode_any Wx_6d6a8 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d6ac : bv 32 := 0x00008067.
Lemma Fx_6d6ac : fetch_word AsanUbsan.M.loaded_segments (0x6d6f4 : word) = Some Wx_6d6ac.
Proof. vm_refl. Qed.
Lemma Dx_6d6ac : decode_any Wx_6d6ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d734 : bv 32 := 0x1a049663.
Lemma Fx_6d734 : fetch_word AsanUbsan.M.loaded_segments (0x6d77c : word) = Some Wx_6d734.
Proof. vm_refl. Qed.
Lemma Dx_6d734 : decode_any Wx_6d734 = Some (Branch BC_NE 9 0 428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d738 : bv 32 := 0xdd9ff06f.
Lemma Fx_6d738 : fetch_word AsanUbsan.M.loaded_segments (0x6d780 : word) = Some Wx_6d738.
Proof. vm_refl. Qed.
Lemma Dx_6d738 : decode_any Wx_6d738 = Some (Jal 0 2096600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d7a8 : bv 32 := 0x24049263.
Lemma Fx_6d7a8 : fetch_word AsanUbsan.M.loaded_segments (0x6d7f0 : word) = Some Wx_6d7a8.
Proof. vm_refl. Qed.
Lemma Dx_6d7a8 : decode_any Wx_6d7a8 = Some (Branch BC_NE 9 0 580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d7ac : bv 32 := 0xdb1ff06f.
Lemma Fx_6d7ac : fetch_word AsanUbsan.M.loaded_segments (0x6d7f4 : word) = Some Wx_6d7ac.
Proof. vm_refl. Qed.
Lemma Dx_6d7ac : decode_any Wx_6d7ac = Some (Jal 0 2096560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8ac : bv 32 := 0x00060703.
Lemma Fx_6d8ac : fetch_word AsanUbsan.M.loaded_segments (0x6d8f4 : word) = Some Wx_6d8ac.
Proof. vm_refl. Qed.
Lemma Dx_6d8ac : decode_any Wx_6d8ac = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8b0 : bv 32 := 0x0076f693.
Lemma Fx_6d8b0 : fetch_word AsanUbsan.M.loaded_segments (0x6d8f8 : word) = Some Wx_6d8b0.
Proof. vm_refl. Qed.
Lemma Dx_6d8b0 : decode_any Wx_6d8b0 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8b4 : bv 32 := 0x00e037b3.
Lemma Fx_6d8b4 : fetch_word AsanUbsan.M.loaded_segments (0x6d8fc : word) = Some Wx_6d8b4.
Proof. vm_refl. Qed.
Lemma Dx_6d8b4 : decode_any Wx_6d8b4 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8b8 : bv 32 := 0x00e6a6b3.
Lemma Fx_6d8b8 : fetch_word AsanUbsan.M.loaded_segments (0x6d900 : word) = Some Wx_6d8b8.
Proof. vm_refl. Qed.
Lemma Dx_6d8b8 : decode_any Wx_6d8b8 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8bc : bv 32 := 0x0016c693.
Lemma Fx_6d8bc : fetch_word AsanUbsan.M.loaded_segments (0x6d904 : word) = Some Wx_6d8bc.
Proof. vm_refl. Qed.
Lemma Dx_6d8bc : decode_any Wx_6d8bc = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8c0 : bv 32 := 0x00d7f6b3.
Lemma Fx_6d8c0 : fetch_word AsanUbsan.M.loaded_segments (0x6d908 : word) = Some Wx_6d8c0.
Proof. vm_refl. Qed.
Lemma Dx_6d8c0 : decode_any Wx_6d8c0 = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8c4 : bv 32 := 0x00c5fa63.
Lemma Fx_6d8c4 : fetch_word AsanUbsan.M.loaded_segments (0x6d90c : word) = Some Wx_6d8c4.
Proof. vm_refl. Qed.
Lemma Dx_6d8c4 : decode_any Wx_6d8c4 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8c8 : bv 32 := 0x0005c703.
Lemma Fx_6d8c8 : fetch_word AsanUbsan.M.loaded_segments (0x6d910 : word) = Some Wx_6d8c8.
Proof. vm_refl. Qed.
Lemma Dx_6d8c8 : decode_any Wx_6d8c8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8cc : bv 32 := 0x00158593.
Lemma Fx_6d8cc : fetch_word AsanUbsan.M.loaded_segments (0x6d914 : word) = Some Wx_6d8cc.
Proof. vm_refl. Qed.
Lemma Dx_6d8cc : decode_any Wx_6d8cc = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8d0 : bv 32 := 0x00d766b3.
Lemma Fx_6d8d0 : fetch_word AsanUbsan.M.loaded_segments (0x6d918 : word) = Some Wx_6d8d0.
Proof. vm_refl. Qed.
Lemma Dx_6d8d0 : decode_any Wx_6d8d0 = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8d4 : bv 32 := 0xfec59ae3.
Lemma Fx_6d8d4 : fetch_word AsanUbsan.M.loaded_segments (0x6d91c : word) = Some Wx_6d8d4.
Proof. vm_refl. Qed.
Lemma Dx_6d8d4 : decode_any Wx_6d8d4 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8d8 : bv 32 := 0x0ff6f593.
Lemma Fx_6d8d8 : fetch_word AsanUbsan.M.loaded_segments (0x6d920 : word) = Some Wx_6d8d8.
Proof. vm_refl. Qed.
Lemma Dx_6d8d8 : decode_any Wx_6d8d8 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8dc : bv 32 := 0xc2058ae3.
Lemma Fx_6d8dc : fetch_word AsanUbsan.M.loaded_segments (0x6d924 : word) = Some Wx_6d8dc.
Proof. vm_refl. Qed.
Lemma Dx_6d8dc : decode_any Wx_6d8dc = Some (Branch BC_EQ 11 0 7220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8e0 : bv 32 := 0x00050d13.
Lemma Fx_6d8e0 : fetch_word AsanUbsan.M.loaded_segments (0x6d928 : word) = Some Wx_6d8e0.
Proof. vm_refl. Qed.
Lemma Dx_6d8e0 : decode_any Wx_6d8e0 = Some (OpImm ALU_ADD 26 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8e4 : bv 32 := 0x000a0513.
Lemma Fx_6d8e4 : fetch_word AsanUbsan.M.loaded_segments (0x6d92c : word) = Some Wx_6d8e4.
Proof. vm_refl. Qed.
Lemma Dx_6d8e4 : decode_any Wx_6d8e4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8e8 : bv 32 := 0x00048593.
Lemma Fx_6d8e8 : fetch_word AsanUbsan.M.loaded_segments (0x6d930 : word) = Some Wx_6d8e8.
Proof. vm_refl. Qed.
Lemma Dx_6d8e8 : decode_any Wx_6d8e8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8ec : bv 32 := 0x209160ef.
Lemma Fx_6d8ec : fetch_word AsanUbsan.M.loaded_segments (0x6d934 : word) = Some Wx_6d8ec.
Proof. vm_refl. Qed.
Lemma Dx_6d8ec : decode_any Wx_6d8ec = Some (Jal 1 92680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8f0 : bv 32 := 0x00050b13.
Lemma Fx_6d8f0 : fetch_word AsanUbsan.M.loaded_segments (0x6d938 : word) = Some Wx_6d8f0.
Proof. vm_refl. Qed.
Lemma Dx_6d8f0 : decode_any Wx_6d8f0 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8f4 : bv 32 := 0x000d0513.
Lemma Fx_6d8f4 : fetch_word AsanUbsan.M.loaded_segments (0x6d93c : word) = Some Wx_6d8f4.
Proof. vm_refl. Qed.
Lemma Dx_6d8f4 : decode_any Wx_6d8f4 = Some (OpImm ALU_ADD 10 26 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d8f8 : bv 32 := 0xc00b0ce3.
Lemma Fx_6d8f8 : fetch_word AsanUbsan.M.loaded_segments (0x6d940 : word) = Some Wx_6d8f8.
Proof. vm_refl. Qed.
Lemma Dx_6d8f8 : decode_any Wx_6d8f8 = Some (Branch BC_EQ 22 0 7192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9b8 : bv 32 := 0x00060703.
Lemma Fx_6d9b8 : fetch_word AsanUbsan.M.loaded_segments (0x6da00 : word) = Some Wx_6d9b8.
Proof. vm_refl. Qed.
Lemma Dx_6d9b8 : decode_any Wx_6d9b8 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9bc : bv 32 := 0x0076f693.
Lemma Fx_6d9bc : fetch_word AsanUbsan.M.loaded_segments (0x6da04 : word) = Some Wx_6d9bc.
Proof. vm_refl. Qed.
Lemma Dx_6d9bc : decode_any Wx_6d9bc = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9c0 : bv 32 := 0x00e037b3.
Lemma Fx_6d9c0 : fetch_word AsanUbsan.M.loaded_segments (0x6da08 : word) = Some Wx_6d9c0.
Proof. vm_refl. Qed.
Lemma Dx_6d9c0 : decode_any Wx_6d9c0 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9c4 : bv 32 := 0x00e6a6b3.
Lemma Fx_6d9c4 : fetch_word AsanUbsan.M.loaded_segments (0x6da0c : word) = Some Wx_6d9c4.
Proof. vm_refl. Qed.
Lemma Dx_6d9c4 : decode_any Wx_6d9c4 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9c8 : bv 32 := 0x0016c693.
Lemma Fx_6d9c8 : fetch_word AsanUbsan.M.loaded_segments (0x6da10 : word) = Some Wx_6d9c8.
Proof. vm_refl. Qed.
Lemma Dx_6d9c8 : decode_any Wx_6d9c8 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9cc : bv 32 := 0x00d7f6b3.
Lemma Fx_6d9cc : fetch_word AsanUbsan.M.loaded_segments (0x6da14 : word) = Some Wx_6d9cc.
Proof. vm_refl. Qed.
Lemma Dx_6d9cc : decode_any Wx_6d9cc = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9d0 : bv 32 := 0x00c5fa63.
Lemma Fx_6d9d0 : fetch_word AsanUbsan.M.loaded_segments (0x6da18 : word) = Some Wx_6d9d0.
Proof. vm_refl. Qed.
Lemma Dx_6d9d0 : decode_any Wx_6d9d0 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9d4 : bv 32 := 0x0005c703.
Lemma Fx_6d9d4 : fetch_word AsanUbsan.M.loaded_segments (0x6da1c : word) = Some Wx_6d9d4.
Proof. vm_refl. Qed.
Lemma Dx_6d9d4 : decode_any Wx_6d9d4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9d8 : bv 32 := 0x00158593.
Lemma Fx_6d9d8 : fetch_word AsanUbsan.M.loaded_segments (0x6da20 : word) = Some Wx_6d9d8.
Proof. vm_refl. Qed.
Lemma Dx_6d9d8 : decode_any Wx_6d9d8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9dc : bv 32 := 0x00d766b3.
Lemma Fx_6d9dc : fetch_word AsanUbsan.M.loaded_segments (0x6da24 : word) = Some Wx_6d9dc.
Proof. vm_refl. Qed.
Lemma Dx_6d9dc : decode_any Wx_6d9dc = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9e0 : bv 32 := 0xfec59ae3.
Lemma Fx_6d9e0 : fetch_word AsanUbsan.M.loaded_segments (0x6da28 : word) = Some Wx_6d9e0.
Proof. vm_refl. Qed.
Lemma Dx_6d9e0 : decode_any Wx_6d9e0 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9e4 : bv 32 := 0x0ff6f593.
Lemma Fx_6d9e4 : fetch_word AsanUbsan.M.loaded_segments (0x6da2c : word) = Some Wx_6d9e4.
Proof. vm_refl. Qed.
Lemma Dx_6d9e4 : decode_any Wx_6d9e4 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9e8 : bv 32 := 0xb6058ae3.
Lemma Fx_6d9e8 : fetch_word AsanUbsan.M.loaded_segments (0x6da30 : word) = Some Wx_6d9e8.
Proof. vm_refl. Qed.
Lemma Dx_6d9e8 : decode_any Wx_6d9e8 = Some (Branch BC_EQ 11 0 7028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9ec : bv 32 := 0x00050c93.
Lemma Fx_6d9ec : fetch_word AsanUbsan.M.loaded_segments (0x6da34 : word) = Some Wx_6d9ec.
Proof. vm_refl. Qed.
Lemma Dx_6d9ec : decode_any Wx_6d9ec = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9f0 : bv 32 := 0x00090513.
Lemma Fx_6d9f0 : fetch_word AsanUbsan.M.loaded_segments (0x6da38 : word) = Some Wx_6d9f0.
Proof. vm_refl. Qed.
Lemma Dx_6d9f0 : decode_any Wx_6d9f0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9f4 : bv 32 := 0x00048593.
Lemma Fx_6d9f4 : fetch_word AsanUbsan.M.loaded_segments (0x6da3c : word) = Some Wx_6d9f4.
Proof. vm_refl. Qed.
Lemma Dx_6d9f4 : decode_any Wx_6d9f4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9f8 : bv 32 := 0x0fd160ef.
Lemma Fx_6d9f8 : fetch_word AsanUbsan.M.loaded_segments (0x6da40 : word) = Some Wx_6d9f8.
Proof. vm_refl. Qed.
Lemma Dx_6d9f8 : decode_any Wx_6d9f8 = Some (Jal 1 92412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6d9fc : bv 32 := 0x00050b13.
Lemma Fx_6d9fc : fetch_word AsanUbsan.M.loaded_segments (0x6da44 : word) = Some Wx_6d9fc.
Proof. vm_refl. Qed.
Lemma Dx_6d9fc : decode_any Wx_6d9fc = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6da00 : bv 32 := 0xb4050ee3.
Lemma Fx_6da00 : fetch_word AsanUbsan.M.loaded_segments (0x6da48 : word) = Some Wx_6da00.
Proof. vm_refl. Qed.
Lemma Dx_6da00 : decode_any Wx_6da00 = Some (Branch BC_EQ 10 0 7004, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dce0 : bv 32 := 0xfd010113.
Lemma Fx_6dce0 : fetch_word AsanUbsan.M.loaded_segments (0x6dd28 : word) = Some Wx_6dce0.
Proof. vm_refl. Qed.
Lemma Dx_6dce0 : decode_any Wx_6dce0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dce4 : bv 32 := 0x02113423.
Lemma Fx_6dce4 : fetch_word AsanUbsan.M.loaded_segments (0x6dd2c : word) = Some Wx_6dce4.
Proof. vm_refl. Qed.
Lemma Dx_6dce4 : decode_any Wx_6dce4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dce8 : bv 32 := 0x02813023.
Lemma Fx_6dce8 : fetch_word AsanUbsan.M.loaded_segments (0x6dd30 : word) = Some Wx_6dce8.
Proof. vm_refl. Qed.
Lemma Dx_6dce8 : decode_any Wx_6dce8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dcec : bv 32 := 0x00913c23.
Lemma Fx_6dcec : fetch_word AsanUbsan.M.loaded_segments (0x6dd34 : word) = Some Wx_6dcec.
Proof. vm_refl. Qed.
Lemma Dx_6dcec : decode_any Wx_6dcec = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dcf0 : bv 32 := 0x01213823.
Lemma Fx_6dcf0 : fetch_word AsanUbsan.M.loaded_segments (0x6dd38 : word) = Some Wx_6dcf0.
Proof. vm_refl. Qed.
Lemma Dx_6dcf0 : decode_any Wx_6dcf0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dcf4 : bv 32 := 0x00060413.
Lemma Fx_6dcf4 : fetch_word AsanUbsan.M.loaded_segments (0x6dd3c : word) = Some Wx_6dcf4.
Proof. vm_refl. Qed.
Lemma Dx_6dcf4 : decode_any Wx_6dcf4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dcf8 : bv 32 := 0x00058493.
Lemma Fx_6dcf8 : fetch_word AsanUbsan.M.loaded_segments (0x6dd40 : word) = Some Wx_6dcf8.
Proof. vm_refl. Qed.
Lemma Dx_6dcf8 : decode_any Wx_6dcf8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dcfc : bv 32 := 0x00050913.
Lemma Fx_6dcfc : fetch_word AsanUbsan.M.loaded_segments (0x6dd44 : word) = Some Wx_6dcfc.
Proof. vm_refl. Qed.
Lemma Dx_6dcfc : decode_any Wx_6dcfc = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd00 : bv 32 := 0x3081b0ef.
Lemma Fx_6dd00 : fetch_word AsanUbsan.M.loaded_segments (0x6dd48 : word) = Some Wx_6dd00.
Proof. vm_refl. Qed.
Lemma Dx_6dd00 : decode_any Wx_6dd00 = Some (Jal 1 111368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd04 : bv 32 := 0x04050863.
Lemma Fx_6dd04 : fetch_word AsanUbsan.M.loaded_segments (0x6dd4c : word) = Some Wx_6dd04.
Proof. vm_refl. Qed.
Lemma Dx_6dd04 : decode_any Wx_6dd04 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd08 : bv 32 := 0xfffae517.
Lemma Fx_6dd08 : fetch_word AsanUbsan.M.loaded_segments (0x6dd50 : word) = Some Wx_6dd08.
Proof. vm_refl. Qed.
Lemma Dx_6dd08 : decode_any Wx_6dd08 = Some (Auipc 10 1048494, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd0c : bv 32 := 0xccb50513.
Lemma Fx_6dd0c : fetch_word AsanUbsan.M.loaded_segments (0x6dd54 : word) = Some Wx_6dd0c.
Proof. vm_refl. Qed.
Lemma Dx_6dd0c : decode_any Wx_6dd0c = Some (OpImm ALU_ADD 10 10 3275, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd10 : bv 32 := 0x00a13423.
Lemma Fx_6dd10 : fetch_word AsanUbsan.M.loaded_segments (0x6dd58 : word) = Some Wx_6dd10.
Proof. vm_refl. Qed.
Lemma Dx_6dd10 : decode_any Wx_6dd10 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd14 : bv 32 := 0x2041c0ef.
Lemma Fx_6dd14 : fetch_word AsanUbsan.M.loaded_segments (0x6dd5c : word) = Some Wx_6dd14.
Proof. vm_refl. Qed.
Lemma Dx_6dd14 : decode_any Wx_6dd14 = Some (Jal 1 115204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd18 : bv 32 := 0x000f8597.
Lemma Fx_6dd18 : fetch_word AsanUbsan.M.loaded_segments (0x6dd60 : word) = Some Wx_6dd18.
Proof. vm_refl. Qed.
Lemma Dx_6dd18 : decode_any Wx_6dd18 = Some (Auipc 11 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd1c : bv 32 := 0x6185b303.
Lemma Fx_6dd1c : fetch_word AsanUbsan.M.loaded_segments (0x6dd64 : word) = Some Wx_6dd1c.
Proof. vm_refl. Qed.
Lemma Dx_6dd1c : decode_any Wx_6dd1c = Some (Load SZ8 true 6 11 1560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd20 : bv 32 := 0x04050c63.
Lemma Fx_6dd20 : fetch_word AsanUbsan.M.loaded_segments (0x6dd68 : word) = Some Wx_6dd20.
Proof. vm_refl. Qed.
Lemma Dx_6dd20 : decode_any Wx_6dd20 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd24 : bv 32 := 0x00810513.
Lemma Fx_6dd24 : fetch_word AsanUbsan.M.loaded_segments (0x6dd6c : word) = Some Wx_6dd24.
Proof. vm_refl. Qed.
Lemma Dx_6dd24 : decode_any Wx_6dd24 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd28 : bv 32 := 0x00030593.
Lemma Fx_6dd28 : fetch_word AsanUbsan.M.loaded_segments (0x6dd70 : word) = Some Wx_6dd28.
Proof. vm_refl. Qed.
Lemma Dx_6dd28 : decode_any Wx_6dd28 = Some (OpImm ALU_ADD 11 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd2c : bv 32 := 0x00090613.
Lemma Fx_6dd2c : fetch_word AsanUbsan.M.loaded_segments (0x6dd74 : word) = Some Wx_6dd2c.
Proof. vm_refl. Qed.
Lemma Dx_6dd2c : decode_any Wx_6dd2c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd30 : bv 32 := 0x00048693.
Lemma Fx_6dd30 : fetch_word AsanUbsan.M.loaded_segments (0x6dd78 : word) = Some Wx_6dd30.
Proof. vm_refl. Qed.
Lemma Dx_6dd30 : decode_any Wx_6dd30 = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd34 : bv 32 := 0x00040713.
Lemma Fx_6dd34 : fetch_word AsanUbsan.M.loaded_segments (0x6dd7c : word) = Some Wx_6dd34.
Proof. vm_refl. Qed.
Lemma Dx_6dd34 : decode_any Wx_6dd34 = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd38 : bv 32 := 0xf14ff0ef.
Lemma Fx_6dd38 : fetch_word AsanUbsan.M.loaded_segments (0x6dd80 : word) = Some Wx_6dd38.
Proof. vm_refl. Qed.
Lemma Dx_6dd38 : decode_any Wx_6dd38 = Some (Jal 1 2094868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd3c : bv 32 := 0x02813083.
Lemma Fx_6dd3c : fetch_word AsanUbsan.M.loaded_segments (0x6dd84 : word) = Some Wx_6dd3c.
Proof. vm_refl. Qed.
Lemma Dx_6dd3c : decode_any Wx_6dd3c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd40 : bv 32 := 0x02013403.
Lemma Fx_6dd40 : fetch_word AsanUbsan.M.loaded_segments (0x6dd88 : word) = Some Wx_6dd40.
Proof. vm_refl. Qed.
Lemma Dx_6dd40 : decode_any Wx_6dd40 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd44 : bv 32 := 0x01813483.
Lemma Fx_6dd44 : fetch_word AsanUbsan.M.loaded_segments (0x6dd8c : word) = Some Wx_6dd44.
Proof. vm_refl. Qed.
Lemma Dx_6dd44 : decode_any Wx_6dd44 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd48 : bv 32 := 0x01013903.
Lemma Fx_6dd48 : fetch_word AsanUbsan.M.loaded_segments (0x6dd90 : word) = Some Wx_6dd48.
Proof. vm_refl. Qed.
Lemma Dx_6dd48 : decode_any Wx_6dd48 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd4c : bv 32 := 0x03010113.
Lemma Fx_6dd4c : fetch_word AsanUbsan.M.loaded_segments (0x6dd94 : word) = Some Wx_6dd4c.
Proof. vm_refl. Qed.
Lemma Dx_6dd4c : decode_any Wx_6dd4c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd50 : bv 32 := 0x00008067.
Lemma Fx_6dd50 : fetch_word AsanUbsan.M.loaded_segments (0x6dd98 : word) = Some Wx_6dd50.
Proof. vm_refl. Qed.
Lemma Dx_6dd50 : decode_any Wx_6dd50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dd9c : bv 32 := 0xfd010113.
Lemma Fx_6dd9c : fetch_word AsanUbsan.M.loaded_segments (0x6dde4 : word) = Some Wx_6dd9c.
Proof. vm_refl. Qed.
Lemma Dx_6dd9c : decode_any Wx_6dd9c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dda0 : bv 32 := 0x02113423.
Lemma Fx_6dda0 : fetch_word AsanUbsan.M.loaded_segments (0x6dde8 : word) = Some Wx_6dda0.
Proof. vm_refl. Qed.
Lemma Dx_6dda0 : decode_any Wx_6dda0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dda4 : bv 32 := 0x02813023.
Lemma Fx_6dda4 : fetch_word AsanUbsan.M.loaded_segments (0x6ddec : word) = Some Wx_6dda4.
Proof. vm_refl. Qed.
Lemma Dx_6dda4 : decode_any Wx_6dda4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dda8 : bv 32 := 0x00913c23.
Lemma Fx_6dda8 : fetch_word AsanUbsan.M.loaded_segments (0x6ddf0 : word) = Some Wx_6dda8.
Proof. vm_refl. Qed.
Lemma Dx_6dda8 : decode_any Wx_6dda8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddac : bv 32 := 0x01213823.
Lemma Fx_6ddac : fetch_word AsanUbsan.M.loaded_segments (0x6ddf4 : word) = Some Wx_6ddac.
Proof. vm_refl. Qed.
Lemma Dx_6ddac : decode_any Wx_6ddac = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddb0 : bv 32 := 0x00060413.
Lemma Fx_6ddb0 : fetch_word AsanUbsan.M.loaded_segments (0x6ddf8 : word) = Some Wx_6ddb0.
Proof. vm_refl. Qed.
Lemma Dx_6ddb0 : decode_any Wx_6ddb0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddb4 : bv 32 := 0x00058493.
Lemma Fx_6ddb4 : fetch_word AsanUbsan.M.loaded_segments (0x6ddfc : word) = Some Wx_6ddb4.
Proof. vm_refl. Qed.
Lemma Dx_6ddb4 : decode_any Wx_6ddb4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddb8 : bv 32 := 0x00050913.
Lemma Fx_6ddb8 : fetch_word AsanUbsan.M.loaded_segments (0x6de00 : word) = Some Wx_6ddb8.
Proof. vm_refl. Qed.
Lemma Dx_6ddb8 : decode_any Wx_6ddb8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddbc : bv 32 := 0x24c1b0ef.
Lemma Fx_6ddbc : fetch_word AsanUbsan.M.loaded_segments (0x6de04 : word) = Some Wx_6ddbc.
Proof. vm_refl. Qed.
Lemma Dx_6ddbc : decode_any Wx_6ddbc = Some (Jal 1 111180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddc0 : bv 32 := 0x04050863.
Lemma Fx_6ddc0 : fetch_word AsanUbsan.M.loaded_segments (0x6de08 : word) = Some Wx_6ddc0.
Proof. vm_refl. Qed.
Lemma Dx_6ddc0 : decode_any Wx_6ddc0 = Some (Branch BC_EQ 10 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddc4 : bv 32 := 0xfffa8517.
Lemma Fx_6ddc4 : fetch_word AsanUbsan.M.loaded_segments (0x6de0c : word) = Some Wx_6ddc4.
Proof. vm_refl. Qed.
Lemma Dx_6ddc4 : decode_any Wx_6ddc4 = Some (Auipc 10 1048488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddc8 : bv 32 := 0x0be50513.
Lemma Fx_6ddc8 : fetch_word AsanUbsan.M.loaded_segments (0x6de10 : word) = Some Wx_6ddc8.
Proof. vm_refl. Qed.
Lemma Dx_6ddc8 : decode_any Wx_6ddc8 = Some (OpImm ALU_ADD 10 10 190, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddcc : bv 32 := 0x00a13423.
Lemma Fx_6ddcc : fetch_word AsanUbsan.M.loaded_segments (0x6de14 : word) = Some Wx_6ddcc.
Proof. vm_refl. Qed.
Lemma Dx_6ddcc : decode_any Wx_6ddcc = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddd0 : bv 32 := 0x1481c0ef.
Lemma Fx_6ddd0 : fetch_word AsanUbsan.M.loaded_segments (0x6de18 : word) = Some Wx_6ddd0.
Proof. vm_refl. Qed.
Lemma Dx_6ddd0 : decode_any Wx_6ddd0 = Some (Jal 1 115016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddd4 : bv 32 := 0x000f8597.
Lemma Fx_6ddd4 : fetch_word AsanUbsan.M.loaded_segments (0x6de1c : word) = Some Wx_6ddd4.
Proof. vm_refl. Qed.
Lemma Dx_6ddd4 : decode_any Wx_6ddd4 = Some (Auipc 11 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddd8 : bv 32 := 0x5645b303.
Lemma Fx_6ddd8 : fetch_word AsanUbsan.M.loaded_segments (0x6de20 : word) = Some Wx_6ddd8.
Proof. vm_refl. Qed.
Lemma Dx_6ddd8 : decode_any Wx_6ddd8 = Some (Load SZ8 true 6 11 1380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dddc : bv 32 := 0x04050c63.
Lemma Fx_6dddc : fetch_word AsanUbsan.M.loaded_segments (0x6de24 : word) = Some Wx_6dddc.
Proof. vm_refl. Qed.
Lemma Dx_6dddc : decode_any Wx_6dddc = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dde0 : bv 32 := 0x00810513.
Lemma Fx_6dde0 : fetch_word AsanUbsan.M.loaded_segments (0x6de28 : word) = Some Wx_6dde0.
Proof. vm_refl. Qed.
Lemma Dx_6dde0 : decode_any Wx_6dde0 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dde4 : bv 32 := 0x00030593.
Lemma Fx_6dde4 : fetch_word AsanUbsan.M.loaded_segments (0x6de2c : word) = Some Wx_6dde4.
Proof. vm_refl. Qed.
Lemma Dx_6dde4 : decode_any Wx_6dde4 = Some (OpImm ALU_ADD 11 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6dde8 : bv 32 := 0x00090613.
Lemma Fx_6dde8 : fetch_word AsanUbsan.M.loaded_segments (0x6de30 : word) = Some Wx_6dde8.
Proof. vm_refl. Qed.
Lemma Dx_6dde8 : decode_any Wx_6dde8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddec : bv 32 := 0x00048693.
Lemma Fx_6ddec : fetch_word AsanUbsan.M.loaded_segments (0x6de34 : word) = Some Wx_6ddec.
Proof. vm_refl. Qed.
Lemma Dx_6ddec : decode_any Wx_6ddec = Some (OpImm ALU_ADD 13 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddf0 : bv 32 := 0x00040713.
Lemma Fx_6ddf0 : fetch_word AsanUbsan.M.loaded_segments (0x6de38 : word) = Some Wx_6ddf0.
Proof. vm_refl. Qed.
Lemma Dx_6ddf0 : decode_any Wx_6ddf0 = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddf4 : bv 32 := 0xe58ff0ef.
Lemma Fx_6ddf4 : fetch_word AsanUbsan.M.loaded_segments (0x6de3c : word) = Some Wx_6ddf4.
Proof. vm_refl. Qed.
Lemma Dx_6ddf4 : decode_any Wx_6ddf4 = Some (Jal 1 2094680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddf8 : bv 32 := 0x02813083.
Lemma Fx_6ddf8 : fetch_word AsanUbsan.M.loaded_segments (0x6de40 : word) = Some Wx_6ddf8.
Proof. vm_refl. Qed.
Lemma Dx_6ddf8 : decode_any Wx_6ddf8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6ddfc : bv 32 := 0x02013403.
Lemma Fx_6ddfc : fetch_word AsanUbsan.M.loaded_segments (0x6de44 : word) = Some Wx_6ddfc.
Proof. vm_refl. Qed.
Lemma Dx_6ddfc : decode_any Wx_6ddfc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6de00 : bv 32 := 0x01813483.
Lemma Fx_6de00 : fetch_word AsanUbsan.M.loaded_segments (0x6de48 : word) = Some Wx_6de00.
Proof. vm_refl. Qed.
Lemma Dx_6de00 : decode_any Wx_6de00 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6de04 : bv 32 := 0x01013903.
Lemma Fx_6de04 : fetch_word AsanUbsan.M.loaded_segments (0x6de4c : word) = Some Wx_6de04.
Proof. vm_refl. Qed.
Lemma Dx_6de04 : decode_any Wx_6de04 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6de08 : bv 32 := 0x03010113.
Lemma Fx_6de08 : fetch_word AsanUbsan.M.loaded_segments (0x6de50 : word) = Some Wx_6de08.
Proof. vm_refl. Qed.
Lemma Dx_6de08 : decode_any Wx_6de08 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6de0c : bv 32 := 0x00008067.
Lemma Fx_6de0c : fetch_word AsanUbsan.M.loaded_segments (0x6de54 : word) = Some Wx_6de0c.
Proof. vm_refl. Qed.
Lemma Dx_6de0c : decode_any Wx_6de0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_89008 : bv 32 := 0x000e5517.
Lemma Fx_89008 : fetch_word AsanUbsan.M.loaded_segments (0x89050 : word) = Some Wx_89008.
Proof. vm_refl. Qed.
Lemma Dx_89008 : decode_any Wx_89008 = Some (Auipc 10 229, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8900c : bv 32 := 0x44850503.
Lemma Fx_8900c : fetch_word AsanUbsan.M.loaded_segments (0x89054 : word) = Some Wx_8900c.
Proof. vm_refl. Qed.
Lemma Dx_8900c : decode_any Wx_8900c = Some (Load SZ1 true 10 10 1096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89010 : bv 32 := 0x0230000f.
Lemma Fx_89010 : fetch_word AsanUbsan.M.loaded_segments (0x89058 : word) = Some Wx_89010.
Proof. vm_refl. Qed.
Lemma Dx_89010 : decode_any Wx_89010 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89014 : bv 32 := 0xfff50513.
Lemma Fx_89014 : fetch_word AsanUbsan.M.loaded_segments (0x8905c : word) = Some Wx_89014.
Proof. vm_refl. Qed.
Lemma Dx_89014 : decode_any Wx_89014 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89018 : bv 32 := 0x00153513.
Lemma Fx_89018 : fetch_word AsanUbsan.M.loaded_segments (0x89060 : word) = Some Wx_89018.
Proof. vm_refl. Qed.
Lemma Dx_89018 : decode_any Wx_89018 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_8901c : bv 32 := 0x00008067.
Lemma Fx_8901c : fetch_word AsanUbsan.M.loaded_segments (0x89064 : word) = Some Wx_8901c.
Proof. vm_refl. Qed.
Lemma Dx_8901c : decode_any Wx_8901c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

