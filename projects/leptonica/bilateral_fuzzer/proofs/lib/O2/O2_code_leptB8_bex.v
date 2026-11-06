(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1a144 : bv 32 := 0x00050663.
Lemma F_1a144 : fetch_word Plain.M.loaded_segments (0x1a19c : word) = Some W_1a144.
Proof. vm_refl. Qed.
Lemma D_1a144 : decode_any W_1a144 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a148 : bv 32 := 0x00852503.
Lemma F_1a148 : fetch_word Plain.M.loaded_segments (0x1a1a0 : word) = Some W_1a148.
Proof. vm_refl. Qed.
Lemma D_1a148 : decode_any W_1a148 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a14c : bv 32 := 0x00008067.
Lemma F_1a14c : fetch_word Plain.M.loaded_segments (0x1a1a4 : word) = Some W_1a14c.
Proof. vm_refl. Qed.
Lemma D_1a14c : decode_any W_1a14c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a244 : bv 32 := 0x00050663.
Lemma F_1a244 : fetch_word Plain.M.loaded_segments (0x1a29c : word) = Some W_1a244.
Proof. vm_refl. Qed.
Lemma D_1a244 : decode_any W_1a244 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a248 : bv 32 := 0x03053503.
Lemma F_1a248 : fetch_word Plain.M.loaded_segments (0x1a2a0 : word) = Some W_1a248.
Proof. vm_refl. Qed.
Lemma D_1a248 : decode_any W_1a248 = Some (Load SZ8 true 10 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a24c : bv 32 := 0x00008067.
Lemma F_1a24c : fetch_word Plain.M.loaded_segments (0x1a2a4 : word) = Some W_1a24c.
Proof. vm_refl. Qed.
Lemma D_1a24c : decode_any W_1a24c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e300 : bv 32 := 0xfb010113.
Lemma F_2e300 : fetch_word Plain.M.loaded_segments (0x2e358 : word) = Some W_2e300.
Proof. vm_refl. Qed.
Lemma D_2e300 : decode_any W_2e300 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e304 : bv 32 := 0x04113423.
Lemma F_2e304 : fetch_word Plain.M.loaded_segments (0x2e35c : word) = Some W_2e304.
Proof. vm_refl. Qed.
Lemma D_2e304 : decode_any W_2e304 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e308 : bv 32 := 0x04813023.
Lemma F_2e308 : fetch_word Plain.M.loaded_segments (0x2e360 : word) = Some W_2e308.
Proof. vm_refl. Qed.
Lemma D_2e308 : decode_any W_2e308 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e30c : bv 32 := 0x02913c23.
Lemma F_2e30c : fetch_word Plain.M.loaded_segments (0x2e364 : word) = Some W_2e30c.
Proof. vm_refl. Qed.
Lemma D_2e30c : decode_any W_2e30c = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e310 : bv 32 := 0x03213823.
Lemma F_2e310 : fetch_word Plain.M.loaded_segments (0x2e368 : word) = Some W_2e310.
Proof. vm_refl. Qed.
Lemma D_2e310 : decode_any W_2e310 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e314 : bv 32 := 0x03313423.
Lemma F_2e314 : fetch_word Plain.M.loaded_segments (0x2e36c : word) = Some W_2e314.
Proof. vm_refl. Qed.
Lemma D_2e314 : decode_any W_2e314 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e318 : bv 32 := 0x03413023.
Lemma F_2e318 : fetch_word Plain.M.loaded_segments (0x2e370 : word) = Some W_2e318.
Proof. vm_refl. Qed.
Lemma D_2e318 : decode_any W_2e318 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e31c : bv 32 := 0x04050063.
Lemma F_2e31c : fetch_word Plain.M.loaded_segments (0x2e374 : word) = Some W_2e31c.
Proof. vm_refl. Qed.
Lemma D_2e31c : decode_any W_2e31c = Some (Branch BC_EQ 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e320 : bv 32 := 0x00058413.
Lemma F_2e320 : fetch_word Plain.M.loaded_segments (0x2e378 : word) = Some W_2e320.
Proof. vm_refl. Qed.
Lemma D_2e320 : decode_any W_2e320 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e324 : bv 32 := 0x00050493.
Lemma F_2e324 : fetch_word Plain.M.loaded_segments (0x2e37c : word) = Some W_2e324.
Proof. vm_refl. Qed.
Lemma D_2e324 : decode_any W_2e324 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e328 : bv 32 := 0x00060913.
Lemma F_2e328 : fetch_word Plain.M.loaded_segments (0x2e380 : word) = Some W_2e328.
Proof. vm_refl. Qed.
Lemma D_2e328 : decode_any W_2e328 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e32c : bv 32 := 0xf19eb0ef.
Lemma F_2e32c : fetch_word Plain.M.loaded_segments (0x2e384 : word) = Some W_2e32c.
Proof. vm_refl. Qed.
Lemma D_2e32c : decode_any W_2e32c = Some (Jal 1 2015000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e330 : bv 32 := 0x06050a63.
Lemma F_2e330 : fetch_word Plain.M.loaded_segments (0x2e388 : word) = Some W_2e330.
Proof. vm_refl. Qed.
Lemma D_2e330 : decode_any W_2e330 = Some (Branch BC_EQ 10 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3a4 : bv 32 := 0x00048513.
Lemma F_2e3a4 : fetch_word Plain.M.loaded_segments (0x2e3fc : word) = Some W_2e3a4.
Proof. vm_refl. Qed.
Lemma D_2e3a4 : decode_any W_2e3a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3a8 : bv 32 := 0xd9deb0ef.
Lemma F_2e3a8 : fetch_word Plain.M.loaded_segments (0x2e400 : word) = Some W_2e3a8.
Proof. vm_refl. Qed.
Lemma D_2e3a8 : decode_any W_2e3a8 = Some (Jal 1 2014620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3ac : bv 32 := 0x00800593.
Lemma F_2e3ac : fetch_word Plain.M.loaded_segments (0x2e404 : word) = Some W_2e3ac.
Proof. vm_refl. Qed.
Lemma D_2e3ac : decode_any W_2e3ac = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3b0 : bv 32 := 0x00b50663.
Lemma F_2e3b0 : fetch_word Plain.M.loaded_segments (0x2e408 : word) = Some W_2e3b0.
Proof. vm_refl. Qed.
Lemma D_2e3b0 : decode_any W_2e3b0 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3b4 : bv 32 := 0x02000593.
Lemma F_2e3b4 : fetch_word Plain.M.loaded_segments (0x2e40c : word) = Some W_2e3b4.
Proof. vm_refl. Qed.
Lemma D_2e3b4 : decode_any W_2e3b4 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3b8 : bv 32 := 0x02b51e63.
Lemma F_2e3b8 : fetch_word Plain.M.loaded_segments (0x2e410 : word) = Some W_2e3b8.
Proof. vm_refl. Qed.
Lemma D_2e3b8 : decode_any W_2e3b8 = Some (Branch BC_NE 10 11 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3bc : bv 32 := 0x06040063.
Lemma F_2e3bc : fetch_word Plain.M.loaded_segments (0x2e414 : word) = Some W_2e3bc.
Proof. vm_refl. Qed.
Lemma D_2e3bc : decode_any W_2e3bc = Some (Branch BC_EQ 8 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3c0 : bv 32 := 0x00800593.
Lemma F_2e3c0 : fetch_word Plain.M.loaded_segments (0x2e418 : word) = Some W_2e3c0.
Proof. vm_refl. Qed.
Lemma D_2e3c0 : decode_any W_2e3c0 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3c4 : bv 32 := 0x0ab51263.
Lemma F_2e3c4 : fetch_word Plain.M.loaded_segments (0x2e41c : word) = Some W_2e3c4.
Proof. vm_refl. Qed.
Lemma D_2e3c4 : decode_any W_2e3c4 = Some (Branch BC_NE 10 11 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3c8 : bv 32 := 0x00048513.
Lemma F_2e3c8 : fetch_word Plain.M.loaded_segments (0x2e420 : word) = Some W_2e3c8.
Proof. vm_refl. Qed.
Lemma D_2e3c8 : decode_any W_2e3c8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3cc : bv 32 := 0x00040593.
Lemma F_2e3cc : fetch_word Plain.M.loaded_segments (0x2e424 : word) = Some W_2e3cc.
Proof. vm_refl. Qed.
Lemma D_2e3cc : decode_any W_2e3cc = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3d0 : bv 32 := 0x00090613.
Lemma F_2e3d0 : fetch_word Plain.M.loaded_segments (0x2e428 : word) = Some W_2e3d0.
Proof. vm_refl. Qed.
Lemma D_2e3d0 : decode_any W_2e3d0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3d4 : bv 32 := 0x04813083.
Lemma F_2e3d4 : fetch_word Plain.M.loaded_segments (0x2e42c : word) = Some W_2e3d4.
Proof. vm_refl. Qed.
Lemma D_2e3d4 : decode_any W_2e3d4 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3d8 : bv 32 := 0x04013403.
Lemma F_2e3d8 : fetch_word Plain.M.loaded_segments (0x2e430 : word) = Some W_2e3d8.
Proof. vm_refl. Qed.
Lemma D_2e3d8 : decode_any W_2e3d8 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3dc : bv 32 := 0x03813483.
Lemma F_2e3dc : fetch_word Plain.M.loaded_segments (0x2e434 : word) = Some W_2e3dc.
Proof. vm_refl. Qed.
Lemma D_2e3dc : decode_any W_2e3dc = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3e0 : bv 32 := 0x03013903.
Lemma F_2e3e0 : fetch_word Plain.M.loaded_segments (0x2e438 : word) = Some W_2e3e0.
Proof. vm_refl. Qed.
Lemma D_2e3e0 : decode_any W_2e3e0 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3e4 : bv 32 := 0x02813983.
Lemma F_2e3e4 : fetch_word Plain.M.loaded_segments (0x2e43c : word) = Some W_2e3e4.
Proof. vm_refl. Qed.
Lemma D_2e3e4 : decode_any W_2e3e4 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3e8 : bv 32 := 0x02013a03.
Lemma F_2e3e8 : fetch_word Plain.M.loaded_segments (0x2e440 : word) = Some W_2e3e8.
Proof. vm_refl. Qed.
Lemma D_2e3e8 : decode_any W_2e3e8 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3ec : bv 32 := 0x05010113.
Lemma F_2e3ec : fetch_word Plain.M.loaded_segments (0x2e444 : word) = Some W_2e3ec.
Proof. vm_refl. Qed.
Lemma D_2e3ec : decode_any W_2e3ec = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e3f0 : bv 32 := 0x1300006f.
Lemma F_2e3f0 : fetch_word Plain.M.loaded_segments (0x2e448 : word) = Some W_2e3f0.
Proof. vm_refl. Qed.
Lemma D_2e3f0 : decode_any W_2e3f0 = Some (Jal 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e448 : bv 32 := 0x04813083.
Lemma F_2e448 : fetch_word Plain.M.loaded_segments (0x2e4a0 : word) = Some W_2e448.
Proof. vm_refl. Qed.
Lemma D_2e448 : decode_any W_2e448 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e44c : bv 32 := 0x04013403.
Lemma F_2e44c : fetch_word Plain.M.loaded_segments (0x2e4a4 : word) = Some W_2e44c.
Proof. vm_refl. Qed.
Lemma D_2e44c : decode_any W_2e44c = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e450 : bv 32 := 0x03813483.
Lemma F_2e450 : fetch_word Plain.M.loaded_segments (0x2e4a8 : word) = Some W_2e450.
Proof. vm_refl. Qed.
Lemma D_2e450 : decode_any W_2e450 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e454 : bv 32 := 0x03013903.
Lemma F_2e454 : fetch_word Plain.M.loaded_segments (0x2e4ac : word) = Some W_2e454.
Proof. vm_refl. Qed.
Lemma D_2e454 : decode_any W_2e454 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e458 : bv 32 := 0x02813983.
Lemma F_2e458 : fetch_word Plain.M.loaded_segments (0x2e4b0 : word) = Some W_2e458.
Proof. vm_refl. Qed.
Lemma D_2e458 : decode_any W_2e458 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e45c : bv 32 := 0x02013a03.
Lemma F_2e45c : fetch_word Plain.M.loaded_segments (0x2e4b4 : word) = Some W_2e45c.
Proof. vm_refl. Qed.
Lemma D_2e45c : decode_any W_2e45c = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e460 : bv 32 := 0x05010113.
Lemma F_2e460 : fetch_word Plain.M.loaded_segments (0x2e4b8 : word) = Some W_2e460.
Proof. vm_refl. Qed.
Lemma D_2e460 : decode_any W_2e460 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e464 : bv 32 := 0x00008067.
Lemma F_2e464 : fetch_word Plain.M.loaded_segments (0x2e4bc : word) = Some W_2e464.
Proof. vm_refl. Qed.
Lemma D_2e464 : decode_any W_2e464 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e468 : bv 32 := 0x00048513.
Lemma F_2e468 : fetch_word Plain.M.loaded_segments (0x2e4c0 : word) = Some W_2e468.
Proof. vm_refl. Qed.
Lemma D_2e468 : decode_any W_2e468 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e46c : bv 32 := 0x00000593.
Lemma F_2e46c : fetch_word Plain.M.loaded_segments (0x2e4c4 : word) = Some W_2e46c.
Proof. vm_refl. Qed.
Lemma D_2e46c : decode_any W_2e46c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e470 : bv 32 := 0xed0ec0ef.
Lemma F_2e470 : fetch_word Plain.M.loaded_segments (0x2e4c8 : word) = Some W_2e470.
Proof. vm_refl. Qed.
Lemma D_2e470 : decode_any W_2e470 = Some (Jal 1 2016976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e474 : bv 32 := 0x00a13c23.
Lemma F_2e474 : fetch_word Plain.M.loaded_segments (0x2e4cc : word) = Some W_2e474.
Proof. vm_refl. Qed.
Lemma D_2e474 : decode_any W_2e474 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e478 : bv 32 := 0x00040593.
Lemma F_2e478 : fetch_word Plain.M.loaded_segments (0x2e4d0 : word) = Some W_2e478.
Proof. vm_refl. Qed.
Lemma D_2e478 : decode_any W_2e478 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e47c : bv 32 := 0x00090613.
Lemma F_2e47c : fetch_word Plain.M.loaded_segments (0x2e4d4 : word) = Some W_2e47c.
Proof. vm_refl. Qed.
Lemma D_2e47c : decode_any W_2e47c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e480 : bv 32 := 0x0a0000ef.
Lemma F_2e480 : fetch_word Plain.M.loaded_segments (0x2e4d8 : word) = Some W_2e480.
Proof. vm_refl. Qed.
Lemma D_2e480 : decode_any W_2e480 = Some (Jal 1 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e484 : bv 32 := 0x00050993.
Lemma F_2e484 : fetch_word Plain.M.loaded_segments (0x2e4dc : word) = Some W_2e484.
Proof. vm_refl. Qed.
Lemma D_2e484 : decode_any W_2e484 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e488 : bv 32 := 0x00a13823.
Lemma F_2e488 : fetch_word Plain.M.loaded_segments (0x2e4e0 : word) = Some W_2e488.
Proof. vm_refl. Qed.
Lemma D_2e488 : decode_any W_2e488 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e48c : bv 32 := 0x01810513.
Lemma F_2e48c : fetch_word Plain.M.loaded_segments (0x2e4e4 : word) = Some W_2e48c.
Proof. vm_refl. Qed.
Lemma D_2e48c : decode_any W_2e48c = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e490 : bv 32 := 0xf41ea0ef.
Lemma F_2e490 : fetch_word Plain.M.loaded_segments (0x2e4e8 : word) = Some W_2e490.
Proof. vm_refl. Qed.
Lemma D_2e490 : decode_any W_2e490 = Some (Jal 1 2010944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e494 : bv 32 := 0x00100593.
Lemma F_2e494 : fetch_word Plain.M.loaded_segments (0x2e4ec : word) = Some W_2e494.
Proof. vm_refl. Qed.
Lemma D_2e494 : decode_any W_2e494 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e498 : bv 32 := 0x00048513.
Lemma F_2e498 : fetch_word Plain.M.loaded_segments (0x2e4f0 : word) = Some W_2e498.
Proof. vm_refl. Qed.
Lemma D_2e498 : decode_any W_2e498 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e49c : bv 32 := 0xea4ec0ef.
Lemma F_2e49c : fetch_word Plain.M.loaded_segments (0x2e4f4 : word) = Some W_2e49c.
Proof. vm_refl. Qed.
Lemma D_2e49c : decode_any W_2e49c = Some (Jal 1 2016932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4a0 : bv 32 := 0x00a13c23.
Lemma F_2e4a0 : fetch_word Plain.M.loaded_segments (0x2e4f8 : word) = Some W_2e4a0.
Proof. vm_refl. Qed.
Lemma D_2e4a0 : decode_any W_2e4a0 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4a4 : bv 32 := 0x00040593.
Lemma F_2e4a4 : fetch_word Plain.M.loaded_segments (0x2e4fc : word) = Some W_2e4a4.
Proof. vm_refl. Qed.
Lemma D_2e4a4 : decode_any W_2e4a4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4a8 : bv 32 := 0x00090613.
Lemma F_2e4a8 : fetch_word Plain.M.loaded_segments (0x2e500 : word) = Some W_2e4a8.
Proof. vm_refl. Qed.
Lemma D_2e4a8 : decode_any W_2e4a8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4ac : bv 32 := 0x074000ef.
Lemma F_2e4ac : fetch_word Plain.M.loaded_segments (0x2e504 : word) = Some W_2e4ac.
Proof. vm_refl. Qed.
Lemma D_2e4ac : decode_any W_2e4ac = Some (Jal 1 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4b0 : bv 32 := 0x00050a13.
Lemma F_2e4b0 : fetch_word Plain.M.loaded_segments (0x2e508 : word) = Some W_2e4b0.
Proof. vm_refl. Qed.
Lemma D_2e4b0 : decode_any W_2e4b0 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4b4 : bv 32 := 0x00a13423.
Lemma F_2e4b4 : fetch_word Plain.M.loaded_segments (0x2e50c : word) = Some W_2e4b4.
Proof. vm_refl. Qed.
Lemma D_2e4b4 : decode_any W_2e4b4 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4b8 : bv 32 := 0x01810513.
Lemma F_2e4b8 : fetch_word Plain.M.loaded_segments (0x2e510 : word) = Some W_2e4b8.
Proof. vm_refl. Qed.
Lemma D_2e4b8 : decode_any W_2e4b8 = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4bc : bv 32 := 0xf15ea0ef.
Lemma F_2e4bc : fetch_word Plain.M.loaded_segments (0x2e514 : word) = Some W_2e4bc.
Proof. vm_refl. Qed.
Lemma D_2e4bc : decode_any W_2e4bc = Some (Jal 1 2010900, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4c0 : bv 32 := 0x00200593.
Lemma F_2e4c0 : fetch_word Plain.M.loaded_segments (0x2e518 : word) = Some W_2e4c0.
Proof. vm_refl. Qed.
Lemma D_2e4c0 : decode_any W_2e4c0 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4c4 : bv 32 := 0x00048513.
Lemma F_2e4c4 : fetch_word Plain.M.loaded_segments (0x2e51c : word) = Some W_2e4c4.
Proof. vm_refl. Qed.
Lemma D_2e4c4 : decode_any W_2e4c4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4c8 : bv 32 := 0xe78ec0ef.
Lemma F_2e4c8 : fetch_word Plain.M.loaded_segments (0x2e520 : word) = Some W_2e4c8.
Proof. vm_refl. Qed.
Lemma D_2e4c8 : decode_any W_2e4c8 = Some (Jal 1 2016888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4cc : bv 32 := 0x00a13c23.
Lemma F_2e4cc : fetch_word Plain.M.loaded_segments (0x2e524 : word) = Some W_2e4cc.
Proof. vm_refl. Qed.
Lemma D_2e4cc : decode_any W_2e4cc = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4d0 : bv 32 := 0x00040593.
Lemma F_2e4d0 : fetch_word Plain.M.loaded_segments (0x2e528 : word) = Some W_2e4d0.
Proof. vm_refl. Qed.
Lemma D_2e4d0 : decode_any W_2e4d0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4d4 : bv 32 := 0x00090613.
Lemma F_2e4d4 : fetch_word Plain.M.loaded_segments (0x2e52c : word) = Some W_2e4d4.
Proof. vm_refl. Qed.
Lemma D_2e4d4 : decode_any W_2e4d4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4d8 : bv 32 := 0x048000ef.
Lemma F_2e4d8 : fetch_word Plain.M.loaded_segments (0x2e530 : word) = Some W_2e4d8.
Proof. vm_refl. Qed.
Lemma D_2e4d8 : decode_any W_2e4d8 = Some (Jal 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4dc : bv 32 := 0x00050413.
Lemma F_2e4dc : fetch_word Plain.M.loaded_segments (0x2e534 : word) = Some W_2e4dc.
Proof. vm_refl. Qed.
Lemma D_2e4dc : decode_any W_2e4dc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4e0 : bv 32 := 0x00a13023.
Lemma F_2e4e0 : fetch_word Plain.M.loaded_segments (0x2e538 : word) = Some W_2e4e0.
Proof. vm_refl. Qed.
Lemma D_2e4e0 : decode_any W_2e4e0 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4e4 : bv 32 := 0x01810513.
Lemma F_2e4e4 : fetch_word Plain.M.loaded_segments (0x2e53c : word) = Some W_2e4e4.
Proof. vm_refl. Qed.
Lemma D_2e4e4 : decode_any W_2e4e4 = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4e8 : bv 32 := 0xee9ea0ef.
Lemma F_2e4e8 : fetch_word Plain.M.loaded_segments (0x2e540 : word) = Some W_2e4e8.
Proof. vm_refl. Qed.
Lemma D_2e4e8 : decode_any W_2e4e8 = Some (Jal 1 2010856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4ec : bv 32 := 0x00098513.
Lemma F_2e4ec : fetch_word Plain.M.loaded_segments (0x2e544 : word) = Some W_2e4ec.
Proof. vm_refl. Qed.
Lemma D_2e4ec : decode_any W_2e4ec = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4f0 : bv 32 := 0x000a0593.
Lemma F_2e4f0 : fetch_word Plain.M.loaded_segments (0x2e548 : word) = Some W_2e4f0.
Proof. vm_refl. Qed.
Lemma D_2e4f0 : decode_any W_2e4f0 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4f4 : bv 32 := 0x00040613.
Lemma F_2e4f4 : fetch_word Plain.M.loaded_segments (0x2e54c : word) = Some W_2e4f4.
Proof. vm_refl. Qed.
Lemma D_2e4f4 : decode_any W_2e4f4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4f8 : bv 32 := 0xeaced0ef.
Lemma F_2e4f8 : fetch_word Plain.M.loaded_segments (0x2e550 : word) = Some W_2e4f8.
Proof. vm_refl. Qed.
Lemma D_2e4f8 : decode_any W_2e4f8 = Some (Jal 1 2021036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e4fc : bv 32 := 0x00050413.
Lemma F_2e4fc : fetch_word Plain.M.loaded_segments (0x2e554 : word) = Some W_2e4fc.
Proof. vm_refl. Qed.
Lemma D_2e4fc : decode_any W_2e4fc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e500 : bv 32 := 0x01010513.
Lemma F_2e500 : fetch_word Plain.M.loaded_segments (0x2e558 : word) = Some W_2e500.
Proof. vm_refl. Qed.
Lemma D_2e500 : decode_any W_2e500 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e504 : bv 32 := 0xecdea0ef.
Lemma F_2e504 : fetch_word Plain.M.loaded_segments (0x2e55c : word) = Some W_2e504.
Proof. vm_refl. Qed.
Lemma D_2e504 : decode_any W_2e504 = Some (Jal 1 2010828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e508 : bv 32 := 0x00810513.
Lemma F_2e508 : fetch_word Plain.M.loaded_segments (0x2e560 : word) = Some W_2e508.
Proof. vm_refl. Qed.
Lemma D_2e508 : decode_any W_2e508 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e50c : bv 32 := 0xec5ea0ef.
Lemma F_2e50c : fetch_word Plain.M.loaded_segments (0x2e564 : word) = Some W_2e50c.
Proof. vm_refl. Qed.
Lemma D_2e50c : decode_any W_2e50c = Some (Jal 1 2010820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e510 : bv 32 := 0x00010513.
Lemma F_2e510 : fetch_word Plain.M.loaded_segments (0x2e568 : word) = Some W_2e510.
Proof. vm_refl. Qed.
Lemma D_2e510 : decode_any W_2e510 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e514 : bv 32 := 0xebdea0ef.
Lemma F_2e514 : fetch_word Plain.M.loaded_segments (0x2e56c : word) = Some W_2e514.
Proof. vm_refl. Qed.
Lemma D_2e514 : decode_any W_2e514 = Some (Jal 1 2010812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e518 : bv 32 := 0x00040513.
Lemma F_2e518 : fetch_word Plain.M.loaded_segments (0x2e570 : word) = Some W_2e518.
Proof. vm_refl. Qed.
Lemma D_2e518 : decode_any W_2e518 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e51c : bv 32 := 0xf2dff06f.
Lemma F_2e51c : fetch_word Plain.M.loaded_segments (0x2e574 : word) = Some W_2e51c.
Proof. vm_refl. Qed.
Lemma D_2e51c : decode_any W_2e51c = Some (Jal 0 2096940, 4%Z).
Proof. vm_refl. Qed.
