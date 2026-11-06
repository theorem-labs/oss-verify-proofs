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
Definition W_149368 : bv 32 := 0x0284b503.
Lemma F_149368 : fetch_word Asan.M.loaded_segments (0x1493ac : word) = Some W_149368.
Proof. vm_refl. Qed.
Lemma D_149368 : decode_any W_149368 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14936c : bv 32 := 0x0384b603.
Lemma F_14936c : fetch_word Asan.M.loaded_segments (0x1493b0 : word) = Some W_14936c.
Proof. vm_refl. Qed.
Lemma D_14936c : decode_any W_14936c = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149370 : bv 32 := 0x40c50b33.
Lemma F_149370 : fetch_word Asan.M.loaded_segments (0x1493b4 : word) = Some W_149370.
Proof. vm_refl. Qed.
Lemma D_149370 : decode_any W_149370 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149374 : bv 32 := 0x00c546b3.
Lemma F_149374 : fetch_word Asan.M.loaded_segments (0x1493b8 : word) = Some W_149374.
Proof. vm_refl. Qed.
Lemma D_149374 : decode_any W_149374 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149378 : bv 32 := 0x00c13423.
Lemma F_149378 : fetch_word Asan.M.loaded_segments (0x1493bc : word) = Some W_149378.
Proof. vm_refl. Qed.
Lemma D_149378 : decode_any W_149378 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14937c : bv 32 := 0x01613823.
Lemma F_14937c : fetch_word Asan.M.loaded_segments (0x1493c0 : word) = Some W_14937c.
Proof. vm_refl. Qed.
Lemma D_14937c : decode_any W_14937c = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149380 : bv 32 := 0x00b13c23.
Lemma F_149380 : fetch_word Asan.M.loaded_segments (0x1493c4 : word) = Some W_149380.
Proof. vm_refl. Qed.
Lemma D_149380 : decode_any W_149380 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149384 : bv 32 := 0x02813023.
Lemma F_149384 : fetch_word Asan.M.loaded_segments (0x1493c8 : word) = Some W_149384.
Proof. vm_refl. Qed.
Lemma D_149384 : decode_any W_149384 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149388 : bv 32 := 0x008b0b33.
Lemma F_149388 : fetch_word Asan.M.loaded_segments (0x1493cc : word) = Some W_149388.
Proof. vm_refl. Qed.
Lemma D_149388 : decode_any W_149388 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14938c : bv 32 := 0x00d03933.
Lemma F_14938c : fetch_word Asan.M.loaded_segments (0x1493d0 : word) = Some W_14938c.
Proof. vm_refl. Qed.
Lemma D_14938c : decode_any W_14938c = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149390 : bv 32 := 0x00c50663.
Lemma F_149390 : fetch_word Asan.M.loaded_segments (0x1493d4 : word) = Some W_149390.
Proof. vm_refl. Qed.
Lemma D_149390 : decode_any W_149390 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149394 : bv 32 := 0x00810993.
Lemma F_149394 : fetch_word Asan.M.loaded_segments (0x1493d8 : word) = Some W_149394.
Proof. vm_refl. Qed.
Lemma D_149394 : decode_any W_149394 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149398 : bv 32 := 0x0080006f.
Lemma F_149398 : fetch_word Asan.M.loaded_segments (0x1493dc : word) = Some W_149398.
Proof. vm_refl. Qed.
Lemma D_149398 : decode_any W_149398 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14939c : bv 32 := 0x01810993.
Lemma F_14939c : fetch_word Asan.M.loaded_segments (0x1493e0 : word) = Some W_14939c.
Proof. vm_refl. Qed.
Lemma D_14939c : decode_any W_14939c = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1493a0 : bv 32 := 0x0784a503.
Lemma F_1493a0 : fetch_word Asan.M.loaded_segments (0x1493e4 : word) = Some W_1493a0.
Proof. vm_refl. Qed.
Lemma D_1493a0 : decode_any W_1493a0 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1493a4 : bv 32 := 0x00190913.
Lemma F_1493a4 : fetch_word Asan.M.loaded_segments (0x1493e8 : word) = Some W_1493a4.
Proof. vm_refl. Qed.
Lemma D_1493a4 : decode_any W_1493a4 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1493a8 : bv 32 := 0x04200893.
Lemma F_1493a8 : fetch_word Asan.M.loaded_segments (0x1493ec : word) = Some W_1493a8.
Proof. vm_refl. Qed.
Lemma D_1493a8 : decode_any W_1493a8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1493ac : bv 32 := 0x00098593.
Lemma F_1493ac : fetch_word Asan.M.loaded_segments (0x1493f0 : word) = Some W_1493ac.
Proof. vm_refl. Qed.
Lemma D_1493ac : decode_any W_1493ac = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1493b0 : bv 32 := 0x00090613.
Lemma F_1493b0 : fetch_word Asan.M.loaded_segments (0x1493f4 : word) = Some W_1493b0.
Proof. vm_refl. Qed.
Lemma D_1493b0 : decode_any W_1493b0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1493b8 : bv 32 := 0x971f80ef.
Lemma F_1493b8 : fetch_word Asan.M.loaded_segments (0x1493fc : word) = Some W_1493b8.
Proof. vm_refl. Qed.
Lemma D_1493b8 : decode_any W_1493b8 = Some (Jal 1 2066800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1493bc : bv 32 := 0x09651863.
Lemma F_1493bc : fetch_word Asan.M.loaded_segments (0x149400 : word) = Some W_1493bc.
Proof. vm_refl. Qed.
Lemma D_1493bc : decode_any W_1493bc = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149410 : bv 32 := 0x00800713.
Lemma F_149410 : fetch_word Asan.M.loaded_segments (0x149454 : word) = Some W_149410.
Proof. vm_refl. Qed.
Lemma D_149410 : decode_any W_149410 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149414 : bv 32 := 0x000a0593.
Lemma F_149414 : fetch_word Asan.M.loaded_segments (0x149458 : word) = Some W_149414.
Proof. vm_refl. Qed.
Lemma D_149414 : decode_any W_149414 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149418 : bv 32 := 0x00e98733.
Lemma F_149418 : fetch_word Asan.M.loaded_segments (0x14945c : word) = Some W_149418.
Proof. vm_refl. Qed.
Lemma D_149418 : decode_any W_149418 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14941c : bv 32 := 0x00073783.
Lemma F_14941c : fetch_word Asan.M.loaded_segments (0x149460 : word) = Some W_14941c.
Proof. vm_refl. Qed.
Lemma D_14941c : decode_any W_14941c = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149420 : bv 32 := 0x40ab0b33.
Lemma F_149420 : fetch_word Asan.M.loaded_segments (0x149464 : word) = Some W_149420.
Proof. vm_refl. Qed.
Lemma D_149420 : decode_any W_149420 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149424 : bv 32 := 0x0784a503.
Lemma F_149424 : fetch_word Asan.M.loaded_segments (0x149468 : word) = Some W_149424.
Proof. vm_refl. Qed.
Lemma D_149424 : decode_any W_149424 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149428 : bv 32 := 0x40c9093b.
Lemma F_149428 : fetch_word Asan.M.loaded_segments (0x14946c : word) = Some W_149428.
Proof. vm_refl. Qed.
Lemma D_149428 : decode_any W_149428 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14942c : bv 32 := 0x40d787b3.
Lemma F_14942c : fetch_word Asan.M.loaded_segments (0x149470 : word) = Some W_14942c.
Proof. vm_refl. Qed.
Lemma D_14942c : decode_any W_14942c = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149430 : bv 32 := 0x00f73023.
Lemma F_149430 : fetch_word Asan.M.loaded_segments (0x149474 : word) = Some W_149430.
Proof. vm_refl. Qed.
Lemma D_149430 : decode_any W_149430 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149434 : bv 32 := 0x04200893.
Lemma F_149434 : fetch_word Asan.M.loaded_segments (0x149478 : word) = Some W_149434.
Proof. vm_refl. Qed.
Lemma D_149434 : decode_any W_149434 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149438 : bv 32 := 0x00090613.
Lemma F_149438 : fetch_word Asan.M.loaded_segments (0x14947c : word) = Some W_149438.
Proof. vm_refl. Qed.
Lemma D_149438 : decode_any W_149438 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149440 : bv 32 := 0x8e9f80ef.
Lemma F_149440 : fetch_word Asan.M.loaded_segments (0x149484 : word) = Some W_149440.
Proof. vm_refl. Qed.
Lemma D_149440 : decode_any W_149440 = Some (Jal 1 2066664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149444 : bv 32 := 0x000a0993.
Lemma F_149444 : fetch_word Asan.M.loaded_segments (0x149488 : word) = Some W_149444.
Proof. vm_refl. Qed.
Lemma D_149444 : decode_any W_149444 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149448 : bv 32 := 0xf7650ce3.
Lemma F_149448 : fetch_word Asan.M.loaded_segments (0x14948c : word) = Some W_149448.
Proof. vm_refl. Qed.
Lemma D_149448 : decode_any W_149448 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14944c : bv 32 := 0x02054c63.
Lemma F_14944c : fetch_word Asan.M.loaded_segments (0x149490 : word) = Some W_14944c.
Proof. vm_refl. Qed.
Lemma D_14944c : decode_any W_14944c = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149450 : bv 32 := 0x0089b583.
Lemma F_149450 : fetch_word Asan.M.loaded_segments (0x149494 : word) = Some W_149450.
Proof. vm_refl. Qed.
Lemma D_149450 : decode_any W_149450 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149454 : bv 32 := 0x00a5b633.
Lemma F_149454 : fetch_word Asan.M.loaded_segments (0x149498 : word) = Some W_149454.
Proof. vm_refl. Qed.
Lemma D_149454 : decode_any W_149454 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149458 : bv 32 := 0x00461a13.
Lemma F_149458 : fetch_word Asan.M.loaded_segments (0x14949c : word) = Some W_149458.
Proof. vm_refl. Qed.
Lemma D_149458 : decode_any W_149458 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14945c : bv 32 := 0x01498a33.
Lemma F_14945c : fetch_word Asan.M.loaded_segments (0x1494a0 : word) = Some W_14945c.
Proof. vm_refl. Qed.
Lemma D_14945c : decode_any W_14945c = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149460 : bv 32 := 0x000a3703.
Lemma F_149460 : fetch_word Asan.M.loaded_segments (0x1494a4 : word) = Some W_149460.
Proof. vm_refl. Qed.
Lemma D_149460 : decode_any W_149460 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149464 : bv 32 := 0x40c006b3.
Lemma F_149464 : fetch_word Asan.M.loaded_segments (0x1494a8 : word) = Some W_149464.
Proof. vm_refl. Qed.
Lemma D_149464 : decode_any W_149464 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149468 : bv 32 := 0x00b6f6b3.
Lemma F_149468 : fetch_word Asan.M.loaded_segments (0x1494ac : word) = Some W_149468.
Proof. vm_refl. Qed.
Lemma D_149468 : decode_any W_149468 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14946c : bv 32 := 0x40d506b3.
Lemma F_14946c : fetch_word Asan.M.loaded_segments (0x1494b0 : word) = Some W_14946c.
Proof. vm_refl. Qed.
Lemma D_14946c : decode_any W_14946c = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149470 : bv 32 := 0x00d70733.
Lemma F_149470 : fetch_word Asan.M.loaded_segments (0x1494b4 : word) = Some W_149470.
Proof. vm_refl. Qed.
Lemma D_149470 : decode_any W_149470 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149474 : bv 32 := 0x00ea3023.
Lemma F_149474 : fetch_word Asan.M.loaded_segments (0x1494b8 : word) = Some W_149474.
Proof. vm_refl. Qed.
Lemma D_149474 : decode_any W_149474 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149478 : bv 32 := 0xf8a5fce3.
Lemma F_149478 : fetch_word Asan.M.loaded_segments (0x1494bc : word) = Some W_149478.
Proof. vm_refl. Qed.
Lemma D_149478 : decode_any W_149478 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_14947c : bv 32 := 0x01800713.
Lemma F_14947c : fetch_word Asan.M.loaded_segments (0x1494c0 : word) = Some W_14947c.
Proof. vm_refl. Qed.
Lemma D_14947c : decode_any W_14947c = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_149480 : bv 32 := 0xf95ff06f.
Lemma F_149480 : fetch_word Asan.M.loaded_segments (0x1494c4 : word) = Some W_149480.
Proof. vm_refl. Qed.
Lemma D_149480 : decode_any W_149480 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

