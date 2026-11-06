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
Definition W_6e000 : bv 32 := 0x02049e63.
Lemma F_6e000 : fetch_word AsanUbsan.M.loaded_segments (0x6e048 : word) = Some W_6e000.
Proof. vm_refl. Qed.
Lemma D_6e000 : decode_any W_6e000 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e03c : bv 32 := 0x00050a93.
Lemma F_6e03c : fetch_word AsanUbsan.M.loaded_segments (0x6e084 : word) = Some W_6e03c.
Proof. vm_refl. Qed.
Lemma D_6e03c : decode_any W_6e03c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e040 : bv 32 := 0x00090513.
Lemma F_6e040 : fetch_word AsanUbsan.M.loaded_segments (0x6e088 : word) = Some W_6e040.
Proof. vm_refl. Qed.
Lemma D_6e040 : decode_any W_6e040 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e044 : bv 32 := 0x00048593.
Lemma F_6e044 : fetch_word AsanUbsan.M.loaded_segments (0x6e08c : word) = Some W_6e044.
Proof. vm_refl. Qed.
Lemma D_6e044 : decode_any W_6e044 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e048 : bv 32 := 0x2ac160ef.
Lemma F_6e048 : fetch_word AsanUbsan.M.loaded_segments (0x6e090 : word) = Some W_6e048.
Proof. vm_refl. Qed.
Lemma D_6e048 : decode_any W_6e048 = Some (Jal 1 90796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e04c : bv 32 := 0x00050913.
Lemma F_6e04c : fetch_word AsanUbsan.M.loaded_segments (0x6e094 : word) = Some W_6e04c.
Proof. vm_refl. Qed.
Lemma D_6e04c : decode_any W_6e04c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e050 : bv 32 := 0x000a8513.
Lemma F_6e050 : fetch_word AsanUbsan.M.loaded_segments (0x6e098 : word) = Some W_6e050.
Proof. vm_refl. Qed.
Lemma D_6e050 : decode_any W_6e050 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e054 : bv 32 := 0xec0900e3.
Lemma F_6e054 : fetch_word AsanUbsan.M.loaded_segments (0x6e09c : word) = Some W_6e054.
Proof. vm_refl. Qed.
Lemma D_6e054 : decode_any W_6e054 = Some (Branch BC_EQ 18 0 7872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3a0 : bv 32 := 0x81010113.
Lemma F_6e3a0 : fetch_word AsanUbsan.M.loaded_segments (0x6e3e8 : word) = Some W_6e3a0.
Proof. vm_refl. Qed.
Lemma D_6e3a0 : decode_any W_6e3a0 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3a4 : bv 32 := 0x7e113423.
Lemma F_6e3a4 : fetch_word AsanUbsan.M.loaded_segments (0x6e3ec : word) = Some W_6e3a4.
Proof. vm_refl. Qed.
Lemma D_6e3a4 : decode_any W_6e3a4 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3a8 : bv 32 := 0x7e813023.
Lemma F_6e3a8 : fetch_word AsanUbsan.M.loaded_segments (0x6e3f0 : word) = Some W_6e3a8.
Proof. vm_refl. Qed.
Lemma D_6e3a8 : decode_any W_6e3a8 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3ac : bv 32 := 0x7c913c23.
Lemma F_6e3ac : fetch_word AsanUbsan.M.loaded_segments (0x6e3f4 : word) = Some W_6e3ac.
Proof. vm_refl. Qed.
Lemma D_6e3ac : decode_any W_6e3ac = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3b0 : bv 32 := 0x7d213823.
Lemma F_6e3b0 : fetch_word AsanUbsan.M.loaded_segments (0x6e3f8 : word) = Some W_6e3b0.
Proof. vm_refl. Qed.
Lemma D_6e3b0 : decode_any W_6e3b0 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3b4 : bv 32 := 0x7d313423.
Lemma F_6e3b4 : fetch_word AsanUbsan.M.loaded_segments (0x6e3fc : word) = Some W_6e3b4.
Proof. vm_refl. Qed.
Lemma D_6e3b4 : decode_any W_6e3b4 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3b8 : bv 32 := 0x7d413023.
Lemma F_6e3b8 : fetch_word AsanUbsan.M.loaded_segments (0x6e400 : word) = Some W_6e3b8.
Proof. vm_refl. Qed.
Lemma D_6e3b8 : decode_any W_6e3b8 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3bc : bv 32 := 0x7f010413.
Lemma F_6e3bc : fetch_word AsanUbsan.M.loaded_segments (0x6e404 : word) = Some W_6e3bc.
Proof. vm_refl. Qed.
Lemma D_6e3bc : decode_any W_6e3bc = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3c0 : bv 32 := 0xfa010113.
Lemma F_6e3c0 : fetch_word AsanUbsan.M.loaded_segments (0x6e408 : word) = Some W_6e3c0.
Proof. vm_refl. Qed.
Lemma D_6e3c0 : decode_any W_6e3c0 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3c4 : bv 32 := 0x00060913.
Lemma F_6e3c4 : fetch_word AsanUbsan.M.loaded_segments (0x6e40c : word) = Some W_6e3c4.
Proof. vm_refl. Qed.
Lemma D_6e3c4 : decode_any W_6e3c4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3c8 : bv 32 := 0x00058493.
Lemma F_6e3c8 : fetch_word AsanUbsan.M.loaded_segments (0x6e410 : word) = Some W_6e3c8.
Proof. vm_refl. Qed.
Lemma D_6e3c8 : decode_any W_6e3c8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3cc : bv 32 := 0x00050993.
Lemma F_6e3cc : fetch_word AsanUbsan.M.loaded_segments (0x6e414 : word) = Some W_6e3cc.
Proof. vm_refl. Qed.
Lemma D_6e3cc : decode_any W_6e3cc = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3d0 : bv 32 := 0x3491b0ef.
Lemma F_6e3d0 : fetch_word AsanUbsan.M.loaded_segments (0x6e418 : word) = Some W_6e3d0.
Proof. vm_refl. Qed.
Lemma D_6e3d0 : decode_any W_6e3d0 = Some (Jal 1 113480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3d4 : bv 32 := 0x000f8597.
Lemma F_6e3d4 : fetch_word AsanUbsan.M.loaded_segments (0x6e41c : word) = Some W_6e3d4.
Proof. vm_refl. Qed.
Lemma D_6e3d4 : decode_any W_6e3d4 = Some (Auipc 11 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3d8 : bv 32 := 0xf7c5b683.
Lemma F_6e3d8 : fetch_word AsanUbsan.M.loaded_segments (0x6e420 : word) = Some W_6e3d8.
Proof. vm_refl. Qed.
Lemma D_6e3d8 : decode_any W_6e3d8 = Some (Load SZ8 true 13 11 3964, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3dc : bv 32 := 0x00050a13.
Lemma F_6e3dc : fetch_word AsanUbsan.M.loaded_segments (0x6e424 : word) = Some W_6e3dc.
Proof. vm_refl. Qed.
Lemma D_6e3dc : decode_any W_6e3dc = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3e0 : bv 32 := 0x00098513.
Lemma F_6e3e0 : fetch_word AsanUbsan.M.loaded_segments (0x6e428 : word) = Some W_6e3e0.
Proof. vm_refl. Qed.
Lemma D_6e3e0 : decode_any W_6e3e0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3e4 : bv 32 := 0x00048593.
Lemma F_6e3e4 : fetch_word AsanUbsan.M.loaded_segments (0x6e42c : word) = Some W_6e3e4.
Proof. vm_refl. Qed.
Lemma D_6e3e4 : decode_any W_6e3e4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3e8 : bv 32 := 0x00090613.
Lemma F_6e3e8 : fetch_word AsanUbsan.M.loaded_segments (0x6e430 : word) = Some W_6e3e8.
Proof. vm_refl. Qed.
Lemma D_6e3e8 : decode_any W_6e3e8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3ec : bv 32 := 0x000680e7.
Lemma F_6e3ec : fetch_word AsanUbsan.M.loaded_segments (0x6e434 : word) = Some W_6e3ec.
Proof. vm_refl. Qed.
Lemma D_6e3ec : decode_any W_6e3ec = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3f0 : bv 32 := 0x060a0063.
Lemma F_6e3f0 : fetch_word AsanUbsan.M.loaded_segments (0x6e438 : word) = Some W_6e3f0.
Proof. vm_refl. Qed.
Lemma D_6e3f0 : decode_any W_6e3f0 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3f4 : bv 32 := 0x04a05e63.
Lemma F_6e3f4 : fetch_word AsanUbsan.M.loaded_segments (0x6e43c : word) = Some W_6e3f4.
Proof. vm_refl. Qed.
Lemma D_6e3f4 : decode_any W_6e3f4 = Some (Branch BC_GE 0 10 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3f8 : bv 32 := 0xfff4c593.
Lemma F_6e3f8 : fetch_word AsanUbsan.M.loaded_segments (0x6e440 : word) = Some W_6e3f8.
Proof. vm_refl. Qed.
Lemma D_6e3f8 : decode_any W_6e3f8 = Some (OpImm ALU_XOR 11 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e3fc : bv 32 := 0x80040a13.
Lemma F_6e3fc : fetch_word AsanUbsan.M.loaded_segments (0x6e444 : word) = Some W_6e3fc.
Proof. vm_refl. Qed.
Lemma D_6e3fc : decode_any W_6e3fc = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e400 : bv 32 := 0xfb8a0a13.
Lemma F_6e400 : fetch_word AsanUbsan.M.loaded_segments (0x6e448 : word) = Some W_6e400.
Proof. vm_refl. Qed.
Lemma D_6e400 : decode_any W_6e400 = Some (OpImm ALU_ADD 20 20 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e404 : bv 32 := 0x06a5e863.
Lemma F_6e404 : fetch_word AsanUbsan.M.loaded_segments (0x6e44c : word) = Some W_6e404.
Proof. vm_refl. Qed.
Lemma D_6e404 : decode_any W_6e404 = Some (Branch BC_LTU 11 10 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e408 : bv 32 := 0xfbf50593.
Lemma F_6e408 : fetch_word AsanUbsan.M.loaded_segments (0x6e450 : word) = Some W_6e408.
Proof. vm_refl. Qed.
Lemma D_6e408 : decode_any W_6e408 = Some (OpImm ALU_ADD 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e40c : bv 32 := 0xfc000613.
Lemma F_6e40c : fetch_word AsanUbsan.M.loaded_segments (0x6e454 : word) = Some W_6e40c.
Proof. vm_refl. Qed.
Lemma D_6e40c : decode_any W_6e40c = Some (OpImm ALU_ADD 12 0 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e410 : bv 32 := 0x0cc5ee63.
Lemma F_6e410 : fetch_word AsanUbsan.M.loaded_segments (0x6e458 : word) = Some W_6e410.
Proof. vm_refl. Qed.
Lemma D_6e410 : decode_any W_6e410 = Some (Branch BC_LTU 11 12 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e414 : bv 32 := 0x000f6597.
Lemma F_6e414 : fetch_word AsanUbsan.M.loaded_segments (0x6e45c : word) = Some W_6e414.
Proof. vm_refl. Qed.
Lemma D_6e414 : decode_any W_6e414 = Some (Auipc 11 246, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e418 : bv 32 := 0x0bc5b583.
Lemma F_6e418 : fetch_word AsanUbsan.M.loaded_segments (0x6e460 : word) = Some W_6e418.
Proof. vm_refl. Qed.
Lemma D_6e418 : decode_any W_6e418 = Some (Load SZ8 true 11 11 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e41c : bv 32 := 0x00a486b3.
Lemma F_6e41c : fetch_word AsanUbsan.M.loaded_segments (0x6e464 : word) = Some W_6e41c.
Proof. vm_refl. Qed.
Lemma D_6e41c : decode_any W_6e41c = Some (Op ALU_ADD 13 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e420 : bv 32 := 0x0005b603.
Lemma F_6e420 : fetch_word AsanUbsan.M.loaded_segments (0x6e468 : word) = Some W_6e420.
Proof. vm_refl. Qed.
Lemma D_6e420 : decode_any W_6e420 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e424 : bv 32 := 0x0034d593.
Lemma F_6e424 : fetch_word AsanUbsan.M.loaded_segments (0x6e46c : word) = Some W_6e424.
Proof. vm_refl. Qed.
Lemma D_6e424 : decode_any W_6e424 = Some (ShiftImm ALU_SRL 11 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e428 : bv 32 := 0xfff68693.
Lemma F_6e428 : fetch_word AsanUbsan.M.loaded_segments (0x6e470 : word) = Some W_6e428.
Proof. vm_refl. Qed.
Lemma D_6e428 : decode_any W_6e428 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e42c : bv 32 := 0x0036d713.
Lemma F_6e42c : fetch_word AsanUbsan.M.loaded_segments (0x6e474 : word) = Some W_6e42c.
Proof. vm_refl. Qed.
Lemma D_6e42c : decode_any W_6e42c = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e430 : bv 32 := 0x00b605b3.
Lemma F_6e430 : fetch_word AsanUbsan.M.loaded_segments (0x6e478 : word) = Some W_6e430.
Proof. vm_refl. Qed.
Lemma D_6e430 : decode_any W_6e430 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e434 : bv 32 := 0x00e60633.
Lemma F_6e434 : fetch_word AsanUbsan.M.loaded_segments (0x6e47c : word) = Some W_6e434.
Proof. vm_refl. Qed.
Lemma D_6e434 : decode_any W_6e434 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e438 : bv 32 := 0xff85f713.
Lemma F_6e438 : fetch_word AsanUbsan.M.loaded_segments (0x6e480 : word) = Some W_6e438.
Proof. vm_refl. Qed.
Lemma D_6e438 : decode_any W_6e438 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e43c : bv 32 := 0xff867793.
Lemma F_6e43c : fetch_word AsanUbsan.M.loaded_segments (0x6e484 : word) = Some W_6e43c.
Proof. vm_refl. Qed.
Lemma D_6e43c : decode_any W_6e43c = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e440 : bv 32 := 0x00073703.
Lemma F_6e440 : fetch_word AsanUbsan.M.loaded_segments (0x6e488 : word) = Some W_6e440.
Proof. vm_refl. Qed.
Lemma D_6e440 : decode_any W_6e440 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e444 : bv 32 := 0x0007b783.
Lemma F_6e444 : fetch_word AsanUbsan.M.loaded_segments (0x6e48c : word) = Some W_6e444.
Proof. vm_refl. Qed.
Lemma D_6e444 : decode_any W_6e444 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e448 : bv 32 := 0x00e7e733.
Lemma F_6e448 : fetch_word AsanUbsan.M.loaded_segments (0x6e490 : word) = Some W_6e448.
Proof. vm_refl. Qed.
Lemma D_6e448 : decode_any W_6e448 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e44c : bv 32 := 0x14071663.
Lemma F_6e44c : fetch_word AsanUbsan.M.loaded_segments (0x6e494 : word) = Some W_6e44c.
Proof. vm_refl. Qed.
Lemma D_6e44c : decode_any W_6e44c = Some (Branch BC_NE 14 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e450 : bv 32 := 0x06010113.
Lemma F_6e450 : fetch_word AsanUbsan.M.loaded_segments (0x6e498 : word) = Some W_6e450.
Proof. vm_refl. Qed.
Lemma D_6e450 : decode_any W_6e450 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e454 : bv 32 := 0x7e813083.
Lemma F_6e454 : fetch_word AsanUbsan.M.loaded_segments (0x6e49c : word) = Some W_6e454.
Proof. vm_refl. Qed.
Lemma D_6e454 : decode_any W_6e454 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e458 : bv 32 := 0x7e013403.
Lemma F_6e458 : fetch_word AsanUbsan.M.loaded_segments (0x6e4a0 : word) = Some W_6e458.
Proof. vm_refl. Qed.
Lemma D_6e458 : decode_any W_6e458 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e45c : bv 32 := 0x7d813483.
Lemma F_6e45c : fetch_word AsanUbsan.M.loaded_segments (0x6e4a4 : word) = Some W_6e45c.
Proof. vm_refl. Qed.
Lemma D_6e45c : decode_any W_6e45c = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e460 : bv 32 := 0x7d013903.
Lemma F_6e460 : fetch_word AsanUbsan.M.loaded_segments (0x6e4a8 : word) = Some W_6e460.
Proof. vm_refl. Qed.
Lemma D_6e460 : decode_any W_6e460 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e464 : bv 32 := 0x7c813983.
Lemma F_6e464 : fetch_word AsanUbsan.M.loaded_segments (0x6e4ac : word) = Some W_6e464.
Proof. vm_refl. Qed.
Lemma D_6e464 : decode_any W_6e464 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e468 : bv 32 := 0x7c013a03.
Lemma F_6e468 : fetch_word AsanUbsan.M.loaded_segments (0x6e4b0 : word) = Some W_6e468.
Proof. vm_refl. Qed.
Lemma D_6e468 : decode_any W_6e468 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e46c : bv 32 := 0x7f010113.
Lemma F_6e46c : fetch_word AsanUbsan.M.loaded_segments (0x6e4b4 : word) = Some W_6e46c.
Proof. vm_refl. Qed.
Lemma D_6e46c : decode_any W_6e46c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e470 : bv 32 := 0x00008067.
Lemma F_6e470 : fetch_word AsanUbsan.M.loaded_segments (0x6e4b8 : word) = Some W_6e470.
Proof. vm_refl. Qed.
Lemma D_6e470 : decode_any W_6e470 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4ec : bv 32 := 0x00050913.
Lemma F_6e4ec : fetch_word AsanUbsan.M.loaded_segments (0x6e534 : word) = Some W_6e4ec.
Proof. vm_refl. Qed.
Lemma D_6e4ec : decode_any W_6e4ec = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4f0 : bv 32 := 0x00048513.
Lemma F_6e4f0 : fetch_word AsanUbsan.M.loaded_segments (0x6e538 : word) = Some W_6e4f0.
Proof. vm_refl. Qed.
Lemma D_6e4f0 : decode_any W_6e4f0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4f4 : bv 32 := 0x00090593.
Lemma F_6e4f4 : fetch_word AsanUbsan.M.loaded_segments (0x6e53c : word) = Some W_6e4f4.
Proof. vm_refl. Qed.
Lemma D_6e4f4 : decode_any W_6e4f4 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4f8 : bv 32 := 0x5fd150ef.
Lemma F_6e4f8 : fetch_word AsanUbsan.M.loaded_segments (0x6e540 : word) = Some W_6e4f8.
Proof. vm_refl. Qed.
Lemma D_6e4f8 : decode_any W_6e4f8 = Some (Jal 1 89596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e4fc : bv 32 := 0x00050493.
Lemma F_6e4fc : fetch_word AsanUbsan.M.loaded_segments (0x6e544 : word) = Some W_6e4fc.
Proof. vm_refl. Qed.
Lemma D_6e4fc : decode_any W_6e4fc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e500 : bv 32 := 0x00090513.
Lemma F_6e500 : fetch_word AsanUbsan.M.loaded_segments (0x6e548 : word) = Some W_6e500.
Proof. vm_refl. Qed.
Lemma D_6e500 : decode_any W_6e500 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e504 : bv 32 := 0xf40486e3.
Lemma F_6e504 : fetch_word AsanUbsan.M.loaded_segments (0x6e54c : word) = Some W_6e504.
Proof. vm_refl. Qed.
Lemma D_6e504 : decode_any W_6e504 = Some (Branch BC_EQ 9 0 8012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e598 : bv 32 := 0x00060703.
Lemma F_6e598 : fetch_word AsanUbsan.M.loaded_segments (0x6e5e0 : word) = Some W_6e598.
Proof. vm_refl. Qed.
Lemma D_6e598 : decode_any W_6e598 = Some (Load SZ1 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e59c : bv 32 := 0x0076f693.
Lemma F_6e59c : fetch_word AsanUbsan.M.loaded_segments (0x6e5e4 : word) = Some W_6e59c.
Proof. vm_refl. Qed.
Lemma D_6e59c : decode_any W_6e59c = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e5a0 : bv 32 := 0x00e037b3.
Lemma F_6e5a0 : fetch_word AsanUbsan.M.loaded_segments (0x6e5e8 : word) = Some W_6e5a0.
Proof. vm_refl. Qed.
Lemma D_6e5a0 : decode_any W_6e5a0 = Some (Op ALU_SLTU 15 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e5a4 : bv 32 := 0x00e6a6b3.
Lemma F_6e5a4 : fetch_word AsanUbsan.M.loaded_segments (0x6e5ec : word) = Some W_6e5a4.
Proof. vm_refl. Qed.
Lemma D_6e5a4 : decode_any W_6e5a4 = Some (Op ALU_SLT 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e5a8 : bv 32 := 0x0016c693.
Lemma F_6e5a8 : fetch_word AsanUbsan.M.loaded_segments (0x6e5f0 : word) = Some W_6e5a8.
Proof. vm_refl. Qed.
Lemma D_6e5a8 : decode_any W_6e5a8 = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e5ac : bv 32 := 0x00d7f6b3.
Lemma F_6e5ac : fetch_word AsanUbsan.M.loaded_segments (0x6e5f4 : word) = Some W_6e5ac.
Proof. vm_refl. Qed.
Lemma D_6e5ac : decode_any W_6e5ac = Some (Op ALU_AND 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e5b0 : bv 32 := 0x00c5fa63.
Lemma F_6e5b0 : fetch_word AsanUbsan.M.loaded_segments (0x6e5f8 : word) = Some W_6e5b0.
Proof. vm_refl. Qed.
Lemma D_6e5b0 : decode_any W_6e5b0 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e5b4 : bv 32 := 0x0005c703.
Lemma F_6e5b4 : fetch_word AsanUbsan.M.loaded_segments (0x6e5fc : word) = Some W_6e5b4.
Proof. vm_refl. Qed.
Lemma D_6e5b4 : decode_any W_6e5b4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e5b8 : bv 32 := 0x00158593.
Lemma F_6e5b8 : fetch_word AsanUbsan.M.loaded_segments (0x6e600 : word) = Some W_6e5b8.
Proof. vm_refl. Qed.
Lemma D_6e5b8 : decode_any W_6e5b8 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e5bc : bv 32 := 0x00d766b3.
Lemma F_6e5bc : fetch_word AsanUbsan.M.loaded_segments (0x6e604 : word) = Some W_6e5bc.
Proof. vm_refl. Qed.
Lemma D_6e5bc : decode_any W_6e5bc = Some (Op ALU_OR 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e5c0 : bv 32 := 0xfec59ae3.
Lemma F_6e5c0 : fetch_word AsanUbsan.M.loaded_segments (0x6e608 : word) = Some W_6e5c0.
Proof. vm_refl. Qed.
Lemma D_6e5c0 : decode_any W_6e5c0 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e5c4 : bv 32 := 0x0ff6f593.
Lemma F_6e5c4 : fetch_word AsanUbsan.M.loaded_segments (0x6e60c : word) = Some W_6e5c4.
Proof. vm_refl. Qed.
Lemma D_6e5c4 : decode_any W_6e5c4 = Some (OpImm ALU_AND 11 13 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6e5c8 : bv 32 := 0xe80584e3.
Lemma F_6e5c8 : fetch_word AsanUbsan.M.loaded_segments (0x6e610 : word) = Some W_6e5c8.
Proof. vm_refl. Qed.
Lemma D_6e5c8 : decode_any W_6e5c8 = Some (Branch BC_EQ 11 0 7816, 4%Z).
Proof. vm_refl. Qed.

