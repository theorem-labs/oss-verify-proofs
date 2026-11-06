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
Definition W_93940 : bv 32 := 0x02060063.
Lemma F_93940 : fetch_word Asan.M.loaded_segments (0x93990 : word) = Some W_93940.
Proof. vm_refl. Qed.
Lemma D_93940 : decode_any W_93940 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93944 : bv 32 := 0x00c50633.
Lemma F_93944 : fetch_word Asan.M.loaded_segments (0x93994 : word) = Some W_93944.
Proof. vm_refl. Qed.
Lemma D_93944 : decode_any W_93944 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93948 : bv 32 := 0x00050693.
Lemma F_93948 : fetch_word Asan.M.loaded_segments (0x93998 : word) = Some W_93948.
Proof. vm_refl. Qed.
Lemma D_93948 : decode_any W_93948 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9394c : bv 32 := 0x0005c703.
Lemma F_9394c : fetch_word Asan.M.loaded_segments (0x9399c : word) = Some W_9394c.
Proof. vm_refl. Qed.
Lemma D_9394c : decode_any W_9394c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93950 : bv 32 := 0x00e68023.
Lemma F_93950 : fetch_word Asan.M.loaded_segments (0x939a0 : word) = Some W_93950.
Proof. vm_refl. Qed.
Lemma D_93950 : decode_any W_93950 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93954 : bv 32 := 0x00168693.
Lemma F_93954 : fetch_word Asan.M.loaded_segments (0x939a4 : word) = Some W_93954.
Proof. vm_refl. Qed.
Lemma D_93954 : decode_any W_93954 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93958 : bv 32 := 0x00158593.
Lemma F_93958 : fetch_word Asan.M.loaded_segments (0x939a8 : word) = Some W_93958.
Proof. vm_refl. Qed.
Lemma D_93958 : decode_any W_93958 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9395c : bv 32 := 0xfec698e3.
Lemma F_9395c : fetch_word Asan.M.loaded_segments (0x939ac : word) = Some W_9395c.
Proof. vm_refl. Qed.
Lemma D_9395c : decode_any W_9395c = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93960 : bv 32 := 0x00008067.
Lemma F_93960 : fetch_word Asan.M.loaded_segments (0x939b0 : word) = Some W_93960.
Proof. vm_refl. Qed.
Lemma D_93960 : decode_any W_93960 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93964 : bv 32 := 0x02b57463.
Lemma F_93964 : fetch_word Asan.M.loaded_segments (0x939b4 : word) = Some W_93964.
Proof. vm_refl. Qed.
Lemma D_93964 : decode_any W_93964 = Some (Branch BC_GEU 10 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93968 : bv 32 := 0x04c05863.
Lemma F_93968 : fetch_word Asan.M.loaded_segments (0x939b8 : word) = Some W_93968.
Proof. vm_refl. Qed.
Lemma D_93968 : decode_any W_93968 = Some (Branch BC_GE 0 12 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9396c : bv 32 := 0x00c50633.
Lemma F_9396c : fetch_word Asan.M.loaded_segments (0x939bc : word) = Some W_9396c.
Proof. vm_refl. Qed.
Lemma D_9396c : decode_any W_9396c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93970 : bv 32 := 0x00050693.
Lemma F_93970 : fetch_word Asan.M.loaded_segments (0x939c0 : word) = Some W_93970.
Proof. vm_refl. Qed.
Lemma D_93970 : decode_any W_93970 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93974 : bv 32 := 0x0005c703.
Lemma F_93974 : fetch_word Asan.M.loaded_segments (0x939c4 : word) = Some W_93974.
Proof. vm_refl. Qed.
Lemma D_93974 : decode_any W_93974 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93978 : bv 32 := 0x00e68023.
Lemma F_93978 : fetch_word Asan.M.loaded_segments (0x939c8 : word) = Some W_93978.
Proof. vm_refl. Qed.
Lemma D_93978 : decode_any W_93978 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9397c : bv 32 := 0x00168693.
Lemma F_9397c : fetch_word Asan.M.loaded_segments (0x939cc : word) = Some W_9397c.
Proof. vm_refl. Qed.
Lemma D_9397c : decode_any W_9397c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93980 : bv 32 := 0x00158593.
Lemma F_93980 : fetch_word Asan.M.loaded_segments (0x939d0 : word) = Some W_93980.
Proof. vm_refl. Qed.
Lemma D_93980 : decode_any W_93980 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93984 : bv 32 := 0xfec698e3.
Lemma F_93984 : fetch_word Asan.M.loaded_segments (0x939d4 : word) = Some W_93984.
Proof. vm_refl. Qed.
Lemma D_93984 : decode_any W_93984 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93988 : bv 32 := 0x0300006f.
Lemma F_93988 : fetch_word Asan.M.loaded_segments (0x939d8 : word) = Some W_93988.
Proof. vm_refl. Qed.
Lemma D_93988 : decode_any W_93988 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9398c : bv 32 := 0x02a5f663.
Lemma F_9398c : fetch_word Asan.M.loaded_segments (0x939dc : word) = Some W_9398c.
Proof. vm_refl. Qed.
Lemma D_9398c : decode_any W_9398c = Some (Branch BC_GEU 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93990 : bv 32 := 0x02c05463.
Lemma F_93990 : fetch_word Asan.M.loaded_segments (0x939e0 : word) = Some W_93990.
Proof. vm_refl. Qed.
Lemma D_93990 : decode_any W_93990 = Some (Branch BC_GE 0 12 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93994 : bv 32 := 0xfff60693.
Lemma F_93994 : fetch_word Asan.M.loaded_segments (0x939e4 : word) = Some W_93994.
Proof. vm_refl. Qed.
Lemma D_93994 : decode_any W_93994 = Some (OpImm ALU_ADD 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93998 : bv 32 := 0x00100613.
Lemma F_93998 : fetch_word Asan.M.loaded_segments (0x939e8 : word) = Some W_93998.
Proof. vm_refl. Qed.
Lemma D_93998 : decode_any W_93998 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9399c : bv 32 := 0x00d58733.
Lemma F_9399c : fetch_word Asan.M.loaded_segments (0x939ec : word) = Some W_9399c.
Proof. vm_refl. Qed.
Lemma D_9399c : decode_any W_9399c = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939a0 : bv 32 := 0x00074703.
Lemma F_939a0 : fetch_word Asan.M.loaded_segments (0x939f0 : word) = Some W_939a0.
Proof. vm_refl. Qed.
Lemma D_939a0 : decode_any W_939a0 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939a4 : bv 32 := 0x00d507b3.
Lemma F_939a4 : fetch_word Asan.M.loaded_segments (0x939f4 : word) = Some W_939a4.
Proof. vm_refl. Qed.
Lemma D_939a4 : decode_any W_939a4 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939a8 : bv 32 := 0x00168813.
Lemma F_939a8 : fetch_word Asan.M.loaded_segments (0x939f8 : word) = Some W_939a8.
Proof. vm_refl. Qed.
Lemma D_939a8 : decode_any W_939a8 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939ac : bv 32 := 0xfff68693.
Lemma F_939ac : fetch_word Asan.M.loaded_segments (0x939fc : word) = Some W_939ac.
Proof. vm_refl. Qed.
Lemma D_939ac : decode_any W_939ac = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939b0 : bv 32 := 0x00e78023.
Lemma F_939b0 : fetch_word Asan.M.loaded_segments (0x93a00 : word) = Some W_939b0.
Proof. vm_refl. Qed.
Lemma D_939b0 : decode_any W_939b0 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939b4 : bv 32 := 0xff0664e3.
Lemma F_939b4 : fetch_word Asan.M.loaded_segments (0x93a04 : word) = Some W_939b4.
Proof. vm_refl. Qed.
Lemma D_939b4 : decode_any W_939b4 = Some (Branch BC_LTU 12 16 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939b8 : bv 32 := 0x00008067.
Lemma F_939b8 : fetch_word Asan.M.loaded_segments (0x93a08 : word) = Some W_939b8.
Proof. vm_refl. Qed.
Lemma D_939b8 : decode_any W_939b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939bc : bv 32 := 0x00a666b3.
Lemma F_939bc : fetch_word Asan.M.loaded_segments (0x93a0c : word) = Some W_939bc.
Proof. vm_refl. Qed.
Lemma D_939bc : decode_any W_939bc = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939c0 : bv 32 := 0x00f6f693.
Lemma F_939c0 : fetch_word Asan.M.loaded_segments (0x93a10 : word) = Some W_939c0.
Proof. vm_refl. Qed.
Lemma D_939c0 : decode_any W_939c0 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939c4 : bv 32 := 0x02068063.
Lemma F_939c4 : fetch_word Asan.M.loaded_segments (0x93a14 : word) = Some W_939c4.
Proof. vm_refl. Qed.
Lemma D_939c4 : decode_any W_939c4 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939c8 : bv 32 := 0x04060863.
Lemma F_939c8 : fetch_word Asan.M.loaded_segments (0x93a18 : word) = Some W_939c8.
Proof. vm_refl. Qed.
Lemma D_939c8 : decode_any W_939c8 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939cc : bv 32 := 0x00c50633.
Lemma F_939cc : fetch_word Asan.M.loaded_segments (0x93a1c : word) = Some W_939cc.
Proof. vm_refl. Qed.
Lemma D_939cc : decode_any W_939cc = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939d0 : bv 32 := 0x00050693.
Lemma F_939d0 : fetch_word Asan.M.loaded_segments (0x93a20 : word) = Some W_939d0.
Proof. vm_refl. Qed.
Lemma D_939d0 : decode_any W_939d0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939d4 : bv 32 := 0x00b68023.
Lemma F_939d4 : fetch_word Asan.M.loaded_segments (0x93a24 : word) = Some W_939d4.
Proof. vm_refl. Qed.
Lemma D_939d4 : decode_any W_939d4 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939d8 : bv 32 := 0x00168693.
Lemma F_939d8 : fetch_word Asan.M.loaded_segments (0x93a28 : word) = Some W_939d8.
Proof. vm_refl. Qed.
Lemma D_939d8 : decode_any W_939d8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939dc : bv 32 := 0xfec69ce3.
Lemma F_939dc : fetch_word Asan.M.loaded_segments (0x93a2c : word) = Some W_939dc.
Proof. vm_refl. Qed.
Lemma D_939dc : decode_any W_939dc = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939e0 : bv 32 := 0x0380006f.
Lemma F_939e0 : fetch_word Asan.M.loaded_segments (0x93a30 : word) = Some W_939e0.
Proof. vm_refl. Qed.
Lemma D_939e0 : decode_any W_939e0 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939e4 : bv 32 := 0x02060a63.
Lemma F_939e4 : fetch_word Asan.M.loaded_segments (0x93a34 : word) = Some W_939e4.
Proof. vm_refl. Qed.
Lemma D_939e4 : decode_any W_939e4 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939e8 : bv 32 := 0x00c50633.
Lemma F_939e8 : fetch_word Asan.M.loaded_segments (0x93a38 : word) = Some W_939e8.
Proof. vm_refl. Qed.
Lemma D_939e8 : decode_any W_939e8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939ec : bv 32 := 0x00859693.
Lemma F_939ec : fetch_word Asan.M.loaded_segments (0x93a3c : word) = Some W_939ec.
Proof. vm_refl. Qed.
Lemma D_939ec : decode_any W_939ec = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939f0 : bv 32 := 0x00b6e5b3.
Lemma F_939f0 : fetch_word Asan.M.loaded_segments (0x93a40 : word) = Some W_939f0.
Proof. vm_refl. Qed.
Lemma D_939f0 : decode_any W_939f0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939f4 : bv 32 := 0x01059693.
Lemma F_939f4 : fetch_word Asan.M.loaded_segments (0x93a44 : word) = Some W_939f4.
Proof. vm_refl. Qed.
Lemma D_939f4 : decode_any W_939f4 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939f8 : bv 32 := 0x00b6e5b3.
Lemma F_939f8 : fetch_word Asan.M.loaded_segments (0x93a48 : word) = Some W_939f8.
Proof. vm_refl. Qed.
Lemma D_939f8 : decode_any W_939f8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_939fc : bv 32 := 0x02059693.
Lemma F_939fc : fetch_word Asan.M.loaded_segments (0x93a4c : word) = Some W_939fc.
Proof. vm_refl. Qed.
Lemma D_939fc : decode_any W_939fc = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93a00 : bv 32 := 0x00b6e5b3.
Lemma F_93a00 : fetch_word Asan.M.loaded_segments (0x93a50 : word) = Some W_93a00.
Proof. vm_refl. Qed.
Lemma D_93a00 : decode_any W_93a00 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93a04 : bv 32 := 0x00050693.
Lemma F_93a04 : fetch_word Asan.M.loaded_segments (0x93a54 : word) = Some W_93a04.
Proof. vm_refl. Qed.
Lemma D_93a04 : decode_any W_93a04 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93a08 : bv 32 := 0x00b6b023.
Lemma F_93a08 : fetch_word Asan.M.loaded_segments (0x93a58 : word) = Some W_93a08.
Proof. vm_refl. Qed.
Lemma D_93a08 : decode_any W_93a08 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93a0c : bv 32 := 0x00b6b423.
Lemma F_93a0c : fetch_word Asan.M.loaded_segments (0x93a5c : word) = Some W_93a0c.
Proof. vm_refl. Qed.
Lemma D_93a0c : decode_any W_93a0c = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93a10 : bv 32 := 0x01068693.
Lemma F_93a10 : fetch_word Asan.M.loaded_segments (0x93a60 : word) = Some W_93a10.
Proof. vm_refl. Qed.
Lemma D_93a10 : decode_any W_93a10 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93a14 : bv 32 := 0xfec6eae3.
Lemma F_93a14 : fetch_word Asan.M.loaded_segments (0x93a64 : word) = Some W_93a14.
Proof. vm_refl. Qed.
Lemma D_93a14 : decode_any W_93a14 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93a18 : bv 32 := 0x00008067.
Lemma F_93a18 : fetch_word Asan.M.loaded_segments (0x93a68 : word) = Some W_93a18.
Proof. vm_refl. Qed.
Lemma D_93a18 : decode_any W_93a18 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b10 : bv 32 := 0x00000593.
Lemma F_93b10 : fetch_word Asan.M.loaded_segments (0x93b60 : word) = Some W_93b10.
Proof. vm_refl. Qed.
Lemma D_93b10 : decode_any W_93b10 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b14 : bv 32 := 0x00b50633.
Lemma F_93b14 : fetch_word Asan.M.loaded_segments (0x93b64 : word) = Some W_93b14.
Proof. vm_refl. Qed.
Lemma D_93b14 : decode_any W_93b14 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b18 : bv 32 := 0x00064603.
Lemma F_93b18 : fetch_word Asan.M.loaded_segments (0x93b68 : word) = Some W_93b18.
Proof. vm_refl. Qed.
Lemma D_93b18 : decode_any W_93b18 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b1c : bv 32 := 0x00158593.
Lemma F_93b1c : fetch_word Asan.M.loaded_segments (0x93b6c : word) = Some W_93b1c.
Proof. vm_refl. Qed.
Lemma D_93b1c : decode_any W_93b1c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b20 : bv 32 := 0xfe061ae3.
Lemma F_93b20 : fetch_word Asan.M.loaded_segments (0x93b70 : word) = Some W_93b20.
Proof. vm_refl. Qed.
Lemma D_93b20 : decode_any W_93b20 = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b24 : bv 32 := 0xfff58513.
Lemma F_93b24 : fetch_word Asan.M.loaded_segments (0x93b74 : word) = Some W_93b24.
Proof. vm_refl. Qed.
Lemma D_93b24 : decode_any W_93b24 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93b28 : bv 32 := 0x00008067.
Lemma F_93b28 : fetch_word Asan.M.loaded_segments (0x93b78 : word) = Some W_93b28.
Proof. vm_refl. Qed.
Lemma D_93b28 : decode_any W_93b28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f08 : bv 32 := 0xff010113.
Lemma F_93f08 : fetch_word Asan.M.loaded_segments (0x93f58 : word) = Some W_93f08.
Proof. vm_refl. Qed.
Lemma D_93f08 : decode_any W_93f08 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f0c : bv 32 := 0x00113423.
Lemma F_93f0c : fetch_word Asan.M.loaded_segments (0x93f5c : word) = Some W_93f0c.
Proof. vm_refl. Qed.
Lemma D_93f0c : decode_any W_93f0c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f10 : bv 32 := 0x00058693.
Lemma F_93f10 : fetch_word Asan.M.loaded_segments (0x93f60 : word) = Some W_93f10.
Proof. vm_refl. Qed.
Lemma D_93f10 : decode_any W_93f10 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f14 : bv 32 := 0x00100713.
Lemma F_93f14 : fetch_word Asan.M.loaded_segments (0x93f64 : word) = Some W_93f14.
Proof. vm_refl. Qed.
Lemma D_93f14 : decode_any W_93f14 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f18 : bv 32 := 0x02871713.
Lemma F_93f18 : fetch_word Asan.M.loaded_segments (0x93f68 : word) = Some W_93f18.
Proof. vm_refl. Qed.
Lemma D_93f18 : decode_any W_93f18 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f1c : bv 32 := 0x00170593.
Lemma F_93f1c : fetch_word Asan.M.loaded_segments (0x93f6c : word) = Some W_93f1c.
Proof. vm_refl. Qed.
Lemma D_93f1c : decode_any W_93f1c = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f20 : bv 32 := 0x08b6f263.
Lemma F_93f20 : fetch_word Asan.M.loaded_segments (0x93f70 : word) = Some W_93f20.
Proof. vm_refl. Qed.
Lemma D_93f20 : decode_any W_93f20 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f24 : bv 32 := 0x00000593.
Lemma F_93f24 : fetch_word Asan.M.loaded_segments (0x93f74 : word) = Some W_93f24.
Proof. vm_refl. Qed.
Lemma D_93f24 : decode_any W_93f24 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f28 : bv 32 := 0x00d50733.
Lemma F_93f28 : fetch_word Asan.M.loaded_segments (0x93f78 : word) = Some W_93f28.
Proof. vm_refl. Qed.
Lemma D_93f28 : decode_any W_93f28 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f2c : bv 32 := 0x00750793.
Lemma F_93f2c : fetch_word Asan.M.loaded_segments (0x93f7c : word) = Some W_93f2c.
Proof. vm_refl. Qed.
Lemma D_93f2c : decode_any W_93f2c = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f30 : bv 32 := 0xff87f793.
Lemma F_93f30 : fetch_word Asan.M.loaded_segments (0x93f80 : word) = Some W_93f30.
Proof. vm_refl. Qed.
Lemma D_93f30 : decode_any W_93f30 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f34 : bv 32 := 0xff877613.
Lemma F_93f34 : fetch_word Asan.M.loaded_segments (0x93f84 : word) = Some W_93f34.
Proof. vm_refl. Qed.
Lemma D_93f34 : decode_any W_93f34 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f38 : bv 32 := 0x02f57463.
Lemma F_93f38 : fetch_word Asan.M.loaded_segments (0x93f88 : word) = Some W_93f38.
Proof. vm_refl. Qed.
Lemma D_93f38 : decode_any W_93f38 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f3c : bv 32 := 0x02068263.
Lemma F_93f3c : fetch_word Asan.M.loaded_segments (0x93f8c : word) = Some W_93f3c.
Proof. vm_refl. Qed.
Lemma D_93f3c : decode_any W_93f3c = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f40 : bv 32 := 0x00000593.
Lemma F_93f40 : fetch_word Asan.M.loaded_segments (0x93f90 : word) = Some W_93f40.
Proof. vm_refl. Qed.
Lemma D_93f40 : decode_any W_93f40 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f44 : bv 32 := 0x00150693.
Lemma F_93f44 : fetch_word Asan.M.loaded_segments (0x93f94 : word) = Some W_93f44.
Proof. vm_refl. Qed.
Lemma D_93f44 : decode_any W_93f44 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f48 : bv 32 := 0x00068813.
Lemma F_93f48 : fetch_word Asan.M.loaded_segments (0x93f98 : word) = Some W_93f48.
Proof. vm_refl. Qed.
Lemma D_93f48 : decode_any W_93f48 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f4c : bv 32 := 0xfff6c683.
Lemma F_93f4c : fetch_word Asan.M.loaded_segments (0x93f9c : word) = Some W_93f4c.
Proof. vm_refl. Qed.
Lemma D_93f4c : decode_any W_93f4c = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f50 : bv 32 := 0x00d5e5b3.
Lemma F_93f50 : fetch_word Asan.M.loaded_segments (0x93fa0 : word) = Some W_93f50.
Proof. vm_refl. Qed.
Lemma D_93f50 : decode_any W_93f50 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f54 : bv 32 := 0x00f87663.
Lemma F_93f54 : fetch_word Asan.M.loaded_segments (0x93fa4 : word) = Some W_93f54.
Proof. vm_refl. Qed.
Lemma D_93f54 : decode_any W_93f54 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f58 : bv 32 := 0x00180693.
Lemma F_93f58 : fetch_word Asan.M.loaded_segments (0x93fa8 : word) = Some W_93f58.
Proof. vm_refl. Qed.
Lemma D_93f58 : decode_any W_93f58 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f5c : bv 32 := 0xfee866e3.
Lemma F_93f5c : fetch_word Asan.M.loaded_segments (0x93fac : word) = Some W_93f5c.
Proof. vm_refl. Qed.
Lemma D_93f5c : decode_any W_93f5c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f60 : bv 32 := 0x00c7fa63.
Lemma F_93f60 : fetch_word Asan.M.loaded_segments (0x93fb0 : word) = Some W_93f60.
Proof. vm_refl. Qed.
Lemma D_93f60 : decode_any W_93f60 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f64 : bv 32 := 0x0007b683.
Lemma F_93f64 : fetch_word Asan.M.loaded_segments (0x93fb4 : word) = Some W_93f64.
Proof. vm_refl. Qed.
Lemma D_93f64 : decode_any W_93f64 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f68 : bv 32 := 0x00878793.
Lemma F_93f68 : fetch_word Asan.M.loaded_segments (0x93fb8 : word) = Some W_93f68.
Proof. vm_refl. Qed.
Lemma D_93f68 : decode_any W_93f68 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f6c : bv 32 := 0x00b6e5b3.
Lemma F_93f6c : fetch_word Asan.M.loaded_segments (0x93fbc : word) = Some W_93f6c.
Proof. vm_refl. Qed.
Lemma D_93f6c : decode_any W_93f6c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f70 : bv 32 := 0xfec7eae3.
Lemma F_93f70 : fetch_word Asan.M.loaded_segments (0x93fc0 : word) = Some W_93f70.
Proof. vm_refl. Qed.
Lemma D_93f70 : decode_any W_93f70 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f74 : bv 32 := 0x02a66063.
Lemma F_93f74 : fetch_word Asan.M.loaded_segments (0x93fc4 : word) = Some W_93f74.
Proof. vm_refl. Qed.
Lemma D_93f74 : decode_any W_93f74 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f78 : bv 32 := 0x00e67e63.
Lemma F_93f78 : fetch_word Asan.M.loaded_segments (0x93fc8 : word) = Some W_93f78.
Proof. vm_refl. Qed.
Lemma D_93f78 : decode_any W_93f78 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f7c : bv 32 := 0x40c70733.
Lemma F_93f7c : fetch_word Asan.M.loaded_segments (0x93fcc : word) = Some W_93f7c.
Proof. vm_refl. Qed.
Lemma D_93f7c : decode_any W_93f7c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f80 : bv 32 := 0x00064503.
Lemma F_93f80 : fetch_word Asan.M.loaded_segments (0x93fd0 : word) = Some W_93f80.
Proof. vm_refl. Qed.
Lemma D_93f80 : decode_any W_93f80 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f84 : bv 32 := 0xfff70713.
Lemma F_93f84 : fetch_word Asan.M.loaded_segments (0x93fd4 : word) = Some W_93f84.
Proof. vm_refl. Qed.
Lemma D_93f84 : decode_any W_93f84 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f88 : bv 32 := 0x00a5e5b3.
Lemma F_93f88 : fetch_word Asan.M.loaded_segments (0x93fd8 : word) = Some W_93f88.
Proof. vm_refl. Qed.
Lemma D_93f88 : decode_any W_93f88 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f8c : bv 32 := 0x00160613.
Lemma F_93f8c : fetch_word Asan.M.loaded_segments (0x93fdc : word) = Some W_93f8c.
Proof. vm_refl. Qed.
Lemma D_93f8c : decode_any W_93f8c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f90 : bv 32 := 0xfe0718e3.
Lemma F_93f90 : fetch_word Asan.M.loaded_segments (0x93fe0 : word) = Some W_93f90.
Proof. vm_refl. Qed.
Lemma D_93f90 : decode_any W_93f90 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f94 : bv 32 := 0x0015b513.
Lemma F_93f94 : fetch_word Asan.M.loaded_segments (0x93fe4 : word) = Some W_93f94.
Proof. vm_refl. Qed.
Lemma D_93f94 : decode_any W_93f94 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f98 : bv 32 := 0x00813083.
Lemma F_93f98 : fetch_word Asan.M.loaded_segments (0x93fe8 : word) = Some W_93f98.
Proof. vm_refl. Qed.
Lemma D_93f98 : decode_any W_93f98 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93f9c : bv 32 := 0x01010113.
Lemma F_93f9c : fetch_word Asan.M.loaded_segments (0x93fec : word) = Some W_93f9c.
Proof. vm_refl. Qed.
Lemma D_93f9c : decode_any W_93f9c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_93fa0 : bv 32 := 0x00008067.
Lemma F_93fa0 : fetch_word Asan.M.loaded_segments (0x93ff0 : word) = Some W_93fa0.
Proof. vm_refl. Qed.
Lemma D_93fa0 : decode_any W_93fa0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

