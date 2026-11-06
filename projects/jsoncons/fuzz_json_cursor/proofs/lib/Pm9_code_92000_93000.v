(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9293c : bv 32 := 0x02060063.
Lemma F_9293c : fetch_word AsanUbsan.M.loaded_segments (0x92984 : word) = Some W_9293c.
Proof. vm_refl. Qed.
Lemma D_9293c : decode_any W_9293c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_92940 : bv 32 := 0x00c50633.
Lemma F_92940 : fetch_word AsanUbsan.M.loaded_segments (0x92988 : word) = Some W_92940.
Proof. vm_refl. Qed.
Lemma D_92940 : decode_any W_92940 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_92944 : bv 32 := 0x00050693.
Lemma F_92944 : fetch_word AsanUbsan.M.loaded_segments (0x9298c : word) = Some W_92944.
Proof. vm_refl. Qed.
Lemma D_92944 : decode_any W_92944 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92948 : bv 32 := 0x0005c703.
Lemma F_92948 : fetch_word AsanUbsan.M.loaded_segments (0x92990 : word) = Some W_92948.
Proof. vm_refl. Qed.
Lemma D_92948 : decode_any W_92948 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9294c : bv 32 := 0x00e68023.
Lemma F_9294c : fetch_word AsanUbsan.M.loaded_segments (0x92994 : word) = Some W_9294c.
Proof. vm_refl. Qed.
Lemma D_9294c : decode_any W_9294c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92950 : bv 32 := 0x00168693.
Lemma F_92950 : fetch_word AsanUbsan.M.loaded_segments (0x92998 : word) = Some W_92950.
Proof. vm_refl. Qed.
Lemma D_92950 : decode_any W_92950 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92954 : bv 32 := 0x00158593.
Lemma F_92954 : fetch_word AsanUbsan.M.loaded_segments (0x9299c : word) = Some W_92954.
Proof. vm_refl. Qed.
Lemma D_92954 : decode_any W_92954 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92958 : bv 32 := 0xfec698e3.
Lemma F_92958 : fetch_word AsanUbsan.M.loaded_segments (0x929a0 : word) = Some W_92958.
Proof. vm_refl. Qed.
Lemma D_92958 : decode_any W_92958 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_9295c : bv 32 := 0x00008067.
Lemma F_9295c : fetch_word AsanUbsan.M.loaded_segments (0x929a4 : word) = Some W_9295c.
Proof. vm_refl. Qed.
Lemma D_9295c : decode_any W_9295c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92960 : bv 32 := 0x02b57463.
Lemma F_92960 : fetch_word AsanUbsan.M.loaded_segments (0x929a8 : word) = Some W_92960.
Proof. vm_refl. Qed.
Lemma D_92960 : decode_any W_92960 = Some (Branch BC_GEU 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_92964 : bv 32 := 0x04c05863.
Lemma F_92964 : fetch_word AsanUbsan.M.loaded_segments (0x929ac : word) = Some W_92964.
Proof. vm_refl. Qed.
Lemma D_92964 : decode_any W_92964 = Some (Branch BC_GE 0 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_92968 : bv 32 := 0x00c50633.
Lemma F_92968 : fetch_word AsanUbsan.M.loaded_segments (0x929b0 : word) = Some W_92968.
Proof. vm_refl. Qed.
Lemma D_92968 : decode_any W_92968 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9296c : bv 32 := 0x00050693.
Lemma F_9296c : fetch_word AsanUbsan.M.loaded_segments (0x929b4 : word) = Some W_9296c.
Proof. vm_refl. Qed.
Lemma D_9296c : decode_any W_9296c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92970 : bv 32 := 0x0005c703.
Lemma F_92970 : fetch_word AsanUbsan.M.loaded_segments (0x929b8 : word) = Some W_92970.
Proof. vm_refl. Qed.
Lemma D_92970 : decode_any W_92970 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92974 : bv 32 := 0x00e68023.
Lemma F_92974 : fetch_word AsanUbsan.M.loaded_segments (0x929bc : word) = Some W_92974.
Proof. vm_refl. Qed.
Lemma D_92974 : decode_any W_92974 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92978 : bv 32 := 0x00168693.
Lemma F_92978 : fetch_word AsanUbsan.M.loaded_segments (0x929c0 : word) = Some W_92978.
Proof. vm_refl. Qed.
Lemma D_92978 : decode_any W_92978 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9297c : bv 32 := 0x00158593.
Lemma F_9297c : fetch_word AsanUbsan.M.loaded_segments (0x929c4 : word) = Some W_9297c.
Proof. vm_refl. Qed.
Lemma D_9297c : decode_any W_9297c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92980 : bv 32 := 0xfec698e3.
Lemma F_92980 : fetch_word AsanUbsan.M.loaded_segments (0x929c8 : word) = Some W_92980.
Proof. vm_refl. Qed.
Lemma D_92980 : decode_any W_92980 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_92984 : bv 32 := 0x0300006f.
Lemma F_92984 : fetch_word AsanUbsan.M.loaded_segments (0x929cc : word) = Some W_92984.
Proof. vm_refl. Qed.
Lemma D_92984 : decode_any W_92984 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_92988 : bv 32 := 0x02a5f663.
Lemma F_92988 : fetch_word AsanUbsan.M.loaded_segments (0x929d0 : word) = Some W_92988.
Proof. vm_refl. Qed.
Lemma D_92988 : decode_any W_92988 = Some (Branch BC_GEU 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_9298c : bv 32 := 0x02c05463.
Lemma F_9298c : fetch_word AsanUbsan.M.loaded_segments (0x929d4 : word) = Some W_9298c.
Proof. vm_refl. Qed.
Lemma D_9298c : decode_any W_9298c = Some (Branch BC_GE 0 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_92990 : bv 32 := 0xfff60693.
Lemma F_92990 : fetch_word AsanUbsan.M.loaded_segments (0x929d8 : word) = Some W_92990.
Proof. vm_refl. Qed.
Lemma D_92990 : decode_any W_92990 = Some (OpImm ALU_ADD 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_92994 : bv 32 := 0x00100613.
Lemma F_92994 : fetch_word AsanUbsan.M.loaded_segments (0x929dc : word) = Some W_92994.
Proof. vm_refl. Qed.
Lemma D_92994 : decode_any W_92994 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92998 : bv 32 := 0x00d58733.
Lemma F_92998 : fetch_word AsanUbsan.M.loaded_segments (0x929e0 : word) = Some W_92998.
Proof. vm_refl. Qed.
Lemma D_92998 : decode_any W_92998 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_9299c : bv 32 := 0x00074703.
Lemma F_9299c : fetch_word AsanUbsan.M.loaded_segments (0x929e4 : word) = Some W_9299c.
Proof. vm_refl. Qed.
Lemma D_9299c : decode_any W_9299c = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_929a0 : bv 32 := 0x00d507b3.
Lemma F_929a0 : fetch_word AsanUbsan.M.loaded_segments (0x929e8 : word) = Some W_929a0.
Proof. vm_refl. Qed.
Lemma D_929a0 : decode_any W_929a0 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_929a4 : bv 32 := 0x00168813.
Lemma F_929a4 : fetch_word AsanUbsan.M.loaded_segments (0x929ec : word) = Some W_929a4.
Proof. vm_refl. Qed.
Lemma D_929a4 : decode_any W_929a4 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_929a8 : bv 32 := 0xfff68693.
Lemma F_929a8 : fetch_word AsanUbsan.M.loaded_segments (0x929f0 : word) = Some W_929a8.
Proof. vm_refl. Qed.
Lemma D_929a8 : decode_any W_929a8 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_929ac : bv 32 := 0x00e78023.
Lemma F_929ac : fetch_word AsanUbsan.M.loaded_segments (0x929f4 : word) = Some W_929ac.
Proof. vm_refl. Qed.
Lemma D_929ac : decode_any W_929ac = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_929b0 : bv 32 := 0xff0664e3.
Lemma F_929b0 : fetch_word AsanUbsan.M.loaded_segments (0x929f8 : word) = Some W_929b0.
Proof. vm_refl. Qed.
Lemma D_929b0 : decode_any W_929b0 = Some (Branch BC_LTU 12 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_929b4 : bv 32 := 0x00008067.
Lemma F_929b4 : fetch_word AsanUbsan.M.loaded_segments (0x929fc : word) = Some W_929b4.
Proof. vm_refl. Qed.
Lemma D_929b4 : decode_any W_929b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_929b8 : bv 32 := 0x00a666b3.
Lemma F_929b8 : fetch_word AsanUbsan.M.loaded_segments (0x92a00 : word) = Some W_929b8.
Proof. vm_refl. Qed.
Lemma D_929b8 : decode_any W_929b8 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_929bc : bv 32 := 0x00f6f693.
Lemma F_929bc : fetch_word AsanUbsan.M.loaded_segments (0x92a04 : word) = Some W_929bc.
Proof. vm_refl. Qed.
Lemma D_929bc : decode_any W_929bc = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_929c0 : bv 32 := 0x02068063.
Lemma F_929c0 : fetch_word AsanUbsan.M.loaded_segments (0x92a08 : word) = Some W_929c0.
Proof. vm_refl. Qed.
Lemma D_929c0 : decode_any W_929c0 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_929c4 : bv 32 := 0x04060863.
Lemma F_929c4 : fetch_word AsanUbsan.M.loaded_segments (0x92a0c : word) = Some W_929c4.
Proof. vm_refl. Qed.
Lemma D_929c4 : decode_any W_929c4 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_929c8 : bv 32 := 0x00c50633.
Lemma F_929c8 : fetch_word AsanUbsan.M.loaded_segments (0x92a10 : word) = Some W_929c8.
Proof. vm_refl. Qed.
Lemma D_929c8 : decode_any W_929c8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_929cc : bv 32 := 0x00050693.
Lemma F_929cc : fetch_word AsanUbsan.M.loaded_segments (0x92a14 : word) = Some W_929cc.
Proof. vm_refl. Qed.
Lemma D_929cc : decode_any W_929cc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_929d0 : bv 32 := 0x00b68023.
Lemma F_929d0 : fetch_word AsanUbsan.M.loaded_segments (0x92a18 : word) = Some W_929d0.
Proof. vm_refl. Qed.
Lemma D_929d0 : decode_any W_929d0 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_929d4 : bv 32 := 0x00168693.
Lemma F_929d4 : fetch_word AsanUbsan.M.loaded_segments (0x92a1c : word) = Some W_929d4.
Proof. vm_refl. Qed.
Lemma D_929d4 : decode_any W_929d4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_929d8 : bv 32 := 0xfec69ce3.
Lemma F_929d8 : fetch_word AsanUbsan.M.loaded_segments (0x92a20 : word) = Some W_929d8.
Proof. vm_refl. Qed.
Lemma D_929d8 : decode_any W_929d8 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_929dc : bv 32 := 0x0380006f.
Lemma F_929dc : fetch_word AsanUbsan.M.loaded_segments (0x92a24 : word) = Some W_929dc.
Proof. vm_refl. Qed.
Lemma D_929dc : decode_any W_929dc = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_929e0 : bv 32 := 0x02060a63.
Lemma F_929e0 : fetch_word AsanUbsan.M.loaded_segments (0x92a28 : word) = Some W_929e0.
Proof. vm_refl. Qed.
Lemma D_929e0 : decode_any W_929e0 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_929e4 : bv 32 := 0x00c50633.
Lemma F_929e4 : fetch_word AsanUbsan.M.loaded_segments (0x92a2c : word) = Some W_929e4.
Proof. vm_refl. Qed.
Lemma D_929e4 : decode_any W_929e4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_929e8 : bv 32 := 0x00859693.
Lemma F_929e8 : fetch_word AsanUbsan.M.loaded_segments (0x92a30 : word) = Some W_929e8.
Proof. vm_refl. Qed.
Lemma D_929e8 : decode_any W_929e8 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_929ec : bv 32 := 0x00b6e5b3.
Lemma F_929ec : fetch_word AsanUbsan.M.loaded_segments (0x92a34 : word) = Some W_929ec.
Proof. vm_refl. Qed.
Lemma D_929ec : decode_any W_929ec = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_929f0 : bv 32 := 0x01059693.
Lemma F_929f0 : fetch_word AsanUbsan.M.loaded_segments (0x92a38 : word) = Some W_929f0.
Proof. vm_refl. Qed.
Lemma D_929f0 : decode_any W_929f0 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_929f4 : bv 32 := 0x00b6e5b3.
Lemma F_929f4 : fetch_word AsanUbsan.M.loaded_segments (0x92a3c : word) = Some W_929f4.
Proof. vm_refl. Qed.
Lemma D_929f4 : decode_any W_929f4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_929f8 : bv 32 := 0x02059693.
Lemma F_929f8 : fetch_word AsanUbsan.M.loaded_segments (0x92a40 : word) = Some W_929f8.
Proof. vm_refl. Qed.
Lemma D_929f8 : decode_any W_929f8 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_929fc : bv 32 := 0x00b6e5b3.
Lemma F_929fc : fetch_word AsanUbsan.M.loaded_segments (0x92a44 : word) = Some W_929fc.
Proof. vm_refl. Qed.
Lemma D_929fc : decode_any W_929fc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_92a00 : bv 32 := 0x00050693.
Lemma F_92a00 : fetch_word AsanUbsan.M.loaded_segments (0x92a48 : word) = Some W_92a00.
Proof. vm_refl. Qed.
Lemma D_92a00 : decode_any W_92a00 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92a04 : bv 32 := 0x00b6b023.
Lemma F_92a04 : fetch_word AsanUbsan.M.loaded_segments (0x92a4c : word) = Some W_92a04.
Proof. vm_refl. Qed.
Lemma D_92a04 : decode_any W_92a04 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92a08 : bv 32 := 0x00b6b423.
Lemma F_92a08 : fetch_word AsanUbsan.M.loaded_segments (0x92a50 : word) = Some W_92a08.
Proof. vm_refl. Qed.
Lemma D_92a08 : decode_any W_92a08 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92a0c : bv 32 := 0x01068693.
Lemma F_92a0c : fetch_word AsanUbsan.M.loaded_segments (0x92a54 : word) = Some W_92a0c.
Proof. vm_refl. Qed.
Lemma D_92a0c : decode_any W_92a0c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_92a10 : bv 32 := 0xfec6eae3.
Lemma F_92a10 : fetch_word AsanUbsan.M.loaded_segments (0x92a58 : word) = Some W_92a10.
Proof. vm_refl. Qed.
Lemma D_92a10 : decode_any W_92a10 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_92a14 : bv 32 := 0x00008067.
Lemma F_92a14 : fetch_word AsanUbsan.M.loaded_segments (0x92a5c : word) = Some W_92a14.
Proof. vm_refl. Qed.
Lemma D_92a14 : decode_any W_92a14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b0c : bv 32 := 0x00000593.
Lemma F_92b0c : fetch_word AsanUbsan.M.loaded_segments (0x92b54 : word) = Some W_92b0c.
Proof. vm_refl. Qed.
Lemma D_92b0c : decode_any W_92b0c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b10 : bv 32 := 0x00b50633.
Lemma F_92b10 : fetch_word AsanUbsan.M.loaded_segments (0x92b58 : word) = Some W_92b10.
Proof. vm_refl. Qed.
Lemma D_92b10 : decode_any W_92b10 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b14 : bv 32 := 0x00064603.
Lemma F_92b14 : fetch_word AsanUbsan.M.loaded_segments (0x92b5c : word) = Some W_92b14.
Proof. vm_refl. Qed.
Lemma D_92b14 : decode_any W_92b14 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b18 : bv 32 := 0x00158593.
Lemma F_92b18 : fetch_word AsanUbsan.M.loaded_segments (0x92b60 : word) = Some W_92b18.
Proof. vm_refl. Qed.
Lemma D_92b18 : decode_any W_92b18 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b1c : bv 32 := 0xfe061ae3.
Lemma F_92b1c : fetch_word AsanUbsan.M.loaded_segments (0x92b64 : word) = Some W_92b1c.
Proof. vm_refl. Qed.
Lemma D_92b1c : decode_any W_92b1c = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b20 : bv 32 := 0xfff58513.
Lemma F_92b20 : fetch_word AsanUbsan.M.loaded_segments (0x92b68 : word) = Some W_92b20.
Proof. vm_refl. Qed.
Lemma D_92b20 : decode_any W_92b20 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b24 : bv 32 := 0x00008067.
Lemma F_92b24 : fetch_word AsanUbsan.M.loaded_segments (0x92b6c : word) = Some W_92b24.
Proof. vm_refl. Qed.
Lemma D_92b24 : decode_any W_92b24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f04 : bv 32 := 0xff010113.
Lemma F_92f04 : fetch_word AsanUbsan.M.loaded_segments (0x92f4c : word) = Some W_92f04.
Proof. vm_refl. Qed.
Lemma D_92f04 : decode_any W_92f04 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f08 : bv 32 := 0x00113423.
Lemma F_92f08 : fetch_word AsanUbsan.M.loaded_segments (0x92f50 : word) = Some W_92f08.
Proof. vm_refl. Qed.
Lemma D_92f08 : decode_any W_92f08 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f0c : bv 32 := 0x00058693.
Lemma F_92f0c : fetch_word AsanUbsan.M.loaded_segments (0x92f54 : word) = Some W_92f0c.
Proof. vm_refl. Qed.
Lemma D_92f0c : decode_any W_92f0c = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f10 : bv 32 := 0x00100713.
Lemma F_92f10 : fetch_word AsanUbsan.M.loaded_segments (0x92f58 : word) = Some W_92f10.
Proof. vm_refl. Qed.
Lemma D_92f10 : decode_any W_92f10 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f14 : bv 32 := 0x02871713.
Lemma F_92f14 : fetch_word AsanUbsan.M.loaded_segments (0x92f5c : word) = Some W_92f14.
Proof. vm_refl. Qed.
Lemma D_92f14 : decode_any W_92f14 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f18 : bv 32 := 0x00170593.
Lemma F_92f18 : fetch_word AsanUbsan.M.loaded_segments (0x92f60 : word) = Some W_92f18.
Proof. vm_refl. Qed.
Lemma D_92f18 : decode_any W_92f18 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f1c : bv 32 := 0x08b6f263.
Lemma F_92f1c : fetch_word AsanUbsan.M.loaded_segments (0x92f64 : word) = Some W_92f1c.
Proof. vm_refl. Qed.
Lemma D_92f1c : decode_any W_92f1c = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f20 : bv 32 := 0x00000593.
Lemma F_92f20 : fetch_word AsanUbsan.M.loaded_segments (0x92f68 : word) = Some W_92f20.
Proof. vm_refl. Qed.
Lemma D_92f20 : decode_any W_92f20 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f24 : bv 32 := 0x00d50733.
Lemma F_92f24 : fetch_word AsanUbsan.M.loaded_segments (0x92f6c : word) = Some W_92f24.
Proof. vm_refl. Qed.
Lemma D_92f24 : decode_any W_92f24 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f28 : bv 32 := 0x00750793.
Lemma F_92f28 : fetch_word AsanUbsan.M.loaded_segments (0x92f70 : word) = Some W_92f28.
Proof. vm_refl. Qed.
Lemma D_92f28 : decode_any W_92f28 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f2c : bv 32 := 0xff87f793.
Lemma F_92f2c : fetch_word AsanUbsan.M.loaded_segments (0x92f74 : word) = Some W_92f2c.
Proof. vm_refl. Qed.
Lemma D_92f2c : decode_any W_92f2c = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f30 : bv 32 := 0xff877613.
Lemma F_92f30 : fetch_word AsanUbsan.M.loaded_segments (0x92f78 : word) = Some W_92f30.
Proof. vm_refl. Qed.
Lemma D_92f30 : decode_any W_92f30 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f34 : bv 32 := 0x02f57463.
Lemma F_92f34 : fetch_word AsanUbsan.M.loaded_segments (0x92f7c : word) = Some W_92f34.
Proof. vm_refl. Qed.
Lemma D_92f34 : decode_any W_92f34 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f38 : bv 32 := 0x02068263.
Lemma F_92f38 : fetch_word AsanUbsan.M.loaded_segments (0x92f80 : word) = Some W_92f38.
Proof. vm_refl. Qed.
Lemma D_92f38 : decode_any W_92f38 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f3c : bv 32 := 0x00000593.
Lemma F_92f3c : fetch_word AsanUbsan.M.loaded_segments (0x92f84 : word) = Some W_92f3c.
Proof. vm_refl. Qed.
Lemma D_92f3c : decode_any W_92f3c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f40 : bv 32 := 0x00150693.
Lemma F_92f40 : fetch_word AsanUbsan.M.loaded_segments (0x92f88 : word) = Some W_92f40.
Proof. vm_refl. Qed.
Lemma D_92f40 : decode_any W_92f40 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f44 : bv 32 := 0x00068813.
Lemma F_92f44 : fetch_word AsanUbsan.M.loaded_segments (0x92f8c : word) = Some W_92f44.
Proof. vm_refl. Qed.
Lemma D_92f44 : decode_any W_92f44 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f48 : bv 32 := 0xfff6c683.
Lemma F_92f48 : fetch_word AsanUbsan.M.loaded_segments (0x92f90 : word) = Some W_92f48.
Proof. vm_refl. Qed.
Lemma D_92f48 : decode_any W_92f48 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f4c : bv 32 := 0x00d5e5b3.
Lemma F_92f4c : fetch_word AsanUbsan.M.loaded_segments (0x92f94 : word) = Some W_92f4c.
Proof. vm_refl. Qed.
Lemma D_92f4c : decode_any W_92f4c = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f50 : bv 32 := 0x00f87663.
Lemma F_92f50 : fetch_word AsanUbsan.M.loaded_segments (0x92f98 : word) = Some W_92f50.
Proof. vm_refl. Qed.
Lemma D_92f50 : decode_any W_92f50 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f54 : bv 32 := 0x00180693.
Lemma F_92f54 : fetch_word AsanUbsan.M.loaded_segments (0x92f9c : word) = Some W_92f54.
Proof. vm_refl. Qed.
Lemma D_92f54 : decode_any W_92f54 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f58 : bv 32 := 0xfee866e3.
Lemma F_92f58 : fetch_word AsanUbsan.M.loaded_segments (0x92fa0 : word) = Some W_92f58.
Proof. vm_refl. Qed.
Lemma D_92f58 : decode_any W_92f58 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f5c : bv 32 := 0x00c7fa63.
Lemma F_92f5c : fetch_word AsanUbsan.M.loaded_segments (0x92fa4 : word) = Some W_92f5c.
Proof. vm_refl. Qed.
Lemma D_92f5c : decode_any W_92f5c = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f60 : bv 32 := 0x0007b683.
Lemma F_92f60 : fetch_word AsanUbsan.M.loaded_segments (0x92fa8 : word) = Some W_92f60.
Proof. vm_refl. Qed.
Lemma D_92f60 : decode_any W_92f60 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f64 : bv 32 := 0x00878793.
Lemma F_92f64 : fetch_word AsanUbsan.M.loaded_segments (0x92fac : word) = Some W_92f64.
Proof. vm_refl. Qed.
Lemma D_92f64 : decode_any W_92f64 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f68 : bv 32 := 0x00b6e5b3.
Lemma F_92f68 : fetch_word AsanUbsan.M.loaded_segments (0x92fb0 : word) = Some W_92f68.
Proof. vm_refl. Qed.
Lemma D_92f68 : decode_any W_92f68 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f6c : bv 32 := 0xfec7eae3.
Lemma F_92f6c : fetch_word AsanUbsan.M.loaded_segments (0x92fb4 : word) = Some W_92f6c.
Proof. vm_refl. Qed.
Lemma D_92f6c : decode_any W_92f6c = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f70 : bv 32 := 0x02a66063.
Lemma F_92f70 : fetch_word AsanUbsan.M.loaded_segments (0x92fb8 : word) = Some W_92f70.
Proof. vm_refl. Qed.
Lemma D_92f70 : decode_any W_92f70 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f74 : bv 32 := 0x00e67e63.
Lemma F_92f74 : fetch_word AsanUbsan.M.loaded_segments (0x92fbc : word) = Some W_92f74.
Proof. vm_refl. Qed.
Lemma D_92f74 : decode_any W_92f74 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f78 : bv 32 := 0x40c70733.
Lemma F_92f78 : fetch_word AsanUbsan.M.loaded_segments (0x92fc0 : word) = Some W_92f78.
Proof. vm_refl. Qed.
Lemma D_92f78 : decode_any W_92f78 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f7c : bv 32 := 0x00064503.
Lemma F_92f7c : fetch_word AsanUbsan.M.loaded_segments (0x92fc4 : word) = Some W_92f7c.
Proof. vm_refl. Qed.
Lemma D_92f7c : decode_any W_92f7c = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f80 : bv 32 := 0xfff70713.
Lemma F_92f80 : fetch_word AsanUbsan.M.loaded_segments (0x92fc8 : word) = Some W_92f80.
Proof. vm_refl. Qed.
Lemma D_92f80 : decode_any W_92f80 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f84 : bv 32 := 0x00a5e5b3.
Lemma F_92f84 : fetch_word AsanUbsan.M.loaded_segments (0x92fcc : word) = Some W_92f84.
Proof. vm_refl. Qed.
Lemma D_92f84 : decode_any W_92f84 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f88 : bv 32 := 0x00160613.
Lemma F_92f88 : fetch_word AsanUbsan.M.loaded_segments (0x92fd0 : word) = Some W_92f88.
Proof. vm_refl. Qed.
Lemma D_92f88 : decode_any W_92f88 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f8c : bv 32 := 0xfe0718e3.
Lemma F_92f8c : fetch_word AsanUbsan.M.loaded_segments (0x92fd4 : word) = Some W_92f8c.
Proof. vm_refl. Qed.
Lemma D_92f8c : decode_any W_92f8c = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f90 : bv 32 := 0x0015b513.
Lemma F_92f90 : fetch_word AsanUbsan.M.loaded_segments (0x92fd8 : word) = Some W_92f90.
Proof. vm_refl. Qed.
Lemma D_92f90 : decode_any W_92f90 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f94 : bv 32 := 0x00813083.
Lemma F_92f94 : fetch_word AsanUbsan.M.loaded_segments (0x92fdc : word) = Some W_92f94.
Proof. vm_refl. Qed.
Lemma D_92f94 : decode_any W_92f94 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f98 : bv 32 := 0x01010113.
Lemma F_92f98 : fetch_word AsanUbsan.M.loaded_segments (0x92fe0 : word) = Some W_92f98.
Proof. vm_refl. Qed.
Lemma D_92f98 : decode_any W_92f98 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_92f9c : bv 32 := 0x00008067.
Lemma F_92f9c : fetch_word AsanUbsan.M.loaded_segments (0x92fe4 : word) = Some W_92f9c.
Proof. vm_refl. Qed.
Lemma D_92f9c : decode_any W_92f9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

