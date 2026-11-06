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
Definition W_94218 : bv 32 := 0x02060063.
Lemma F_94218 : fetch_word AsanUbsan.M.loaded_segments (0x94260 : word) = Some W_94218.
Proof. vm_refl. Qed.
Lemma D_94218 : decode_any W_94218 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9421c : bv 32 := 0x00c50633.
Lemma F_9421c : fetch_word AsanUbsan.M.loaded_segments (0x94264 : word) = Some W_9421c.
Proof. vm_refl. Qed.
Lemma D_9421c : decode_any W_9421c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94220 : bv 32 := 0x00050693.
Lemma F_94220 : fetch_word AsanUbsan.M.loaded_segments (0x94268 : word) = Some W_94220.
Proof. vm_refl. Qed.
Lemma D_94220 : decode_any W_94220 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94224 : bv 32 := 0x0005c703.
Lemma F_94224 : fetch_word AsanUbsan.M.loaded_segments (0x9426c : word) = Some W_94224.
Proof. vm_refl. Qed.
Lemma D_94224 : decode_any W_94224 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94228 : bv 32 := 0x00e68023.
Lemma F_94228 : fetch_word AsanUbsan.M.loaded_segments (0x94270 : word) = Some W_94228.
Proof. vm_refl. Qed.
Lemma D_94228 : decode_any W_94228 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9422c : bv 32 := 0x00168693.
Lemma F_9422c : fetch_word AsanUbsan.M.loaded_segments (0x94274 : word) = Some W_9422c.
Proof. vm_refl. Qed.
Lemma D_9422c : decode_any W_9422c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94230 : bv 32 := 0x00158593.
Lemma F_94230 : fetch_word AsanUbsan.M.loaded_segments (0x94278 : word) = Some W_94230.
Proof. vm_refl. Qed.
Lemma D_94230 : decode_any W_94230 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94234 : bv 32 := 0xfec698e3.
Lemma F_94234 : fetch_word AsanUbsan.M.loaded_segments (0x9427c : word) = Some W_94234.
Proof. vm_refl. Qed.
Lemma D_94234 : decode_any W_94234 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94238 : bv 32 := 0x00008067.
Lemma F_94238 : fetch_word AsanUbsan.M.loaded_segments (0x94280 : word) = Some W_94238.
Proof. vm_refl. Qed.
Lemma D_94238 : decode_any W_94238 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9423c : bv 32 := 0x02b57463.
Lemma F_9423c : fetch_word AsanUbsan.M.loaded_segments (0x94284 : word) = Some W_9423c.
Proof. vm_refl. Qed.
Lemma D_9423c : decode_any W_9423c = Some (Branch BC_GEU 10 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94240 : bv 32 := 0x04c05863.
Lemma F_94240 : fetch_word AsanUbsan.M.loaded_segments (0x94288 : word) = Some W_94240.
Proof. vm_refl. Qed.
Lemma D_94240 : decode_any W_94240 = Some (Branch BC_GE 0 12 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94244 : bv 32 := 0x00c50633.
Lemma F_94244 : fetch_word AsanUbsan.M.loaded_segments (0x9428c : word) = Some W_94244.
Proof. vm_refl. Qed.
Lemma D_94244 : decode_any W_94244 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94248 : bv 32 := 0x00050693.
Lemma F_94248 : fetch_word AsanUbsan.M.loaded_segments (0x94290 : word) = Some W_94248.
Proof. vm_refl. Qed.
Lemma D_94248 : decode_any W_94248 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9424c : bv 32 := 0x0005c703.
Lemma F_9424c : fetch_word AsanUbsan.M.loaded_segments (0x94294 : word) = Some W_9424c.
Proof. vm_refl. Qed.
Lemma D_9424c : decode_any W_9424c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94250 : bv 32 := 0x00e68023.
Lemma F_94250 : fetch_word AsanUbsan.M.loaded_segments (0x94298 : word) = Some W_94250.
Proof. vm_refl. Qed.
Lemma D_94250 : decode_any W_94250 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94254 : bv 32 := 0x00168693.
Lemma F_94254 : fetch_word AsanUbsan.M.loaded_segments (0x9429c : word) = Some W_94254.
Proof. vm_refl. Qed.
Lemma D_94254 : decode_any W_94254 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94258 : bv 32 := 0x00158593.
Lemma F_94258 : fetch_word AsanUbsan.M.loaded_segments (0x942a0 : word) = Some W_94258.
Proof. vm_refl. Qed.
Lemma D_94258 : decode_any W_94258 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9425c : bv 32 := 0xfec698e3.
Lemma F_9425c : fetch_word AsanUbsan.M.loaded_segments (0x942a4 : word) = Some W_9425c.
Proof. vm_refl. Qed.
Lemma D_9425c : decode_any W_9425c = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94260 : bv 32 := 0x0300006f.
Lemma F_94260 : fetch_word AsanUbsan.M.loaded_segments (0x942a8 : word) = Some W_94260.
Proof. vm_refl. Qed.
Lemma D_94260 : decode_any W_94260 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94264 : bv 32 := 0x02a5f663.
Lemma F_94264 : fetch_word AsanUbsan.M.loaded_segments (0x942ac : word) = Some W_94264.
Proof. vm_refl. Qed.
Lemma D_94264 : decode_any W_94264 = Some (Branch BC_GEU 11 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94268 : bv 32 := 0x02c05463.
Lemma F_94268 : fetch_word AsanUbsan.M.loaded_segments (0x942b0 : word) = Some W_94268.
Proof. vm_refl. Qed.
Lemma D_94268 : decode_any W_94268 = Some (Branch BC_GE 0 12 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9426c : bv 32 := 0xfff60693.
Lemma F_9426c : fetch_word AsanUbsan.M.loaded_segments (0x942b4 : word) = Some W_9426c.
Proof. vm_refl. Qed.
Lemma D_9426c : decode_any W_9426c = Some (OpImm ALU_ADD 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94270 : bv 32 := 0x00100613.
Lemma F_94270 : fetch_word AsanUbsan.M.loaded_segments (0x942b8 : word) = Some W_94270.
Proof. vm_refl. Qed.
Lemma D_94270 : decode_any W_94270 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94274 : bv 32 := 0x00d58733.
Lemma F_94274 : fetch_word AsanUbsan.M.loaded_segments (0x942bc : word) = Some W_94274.
Proof. vm_refl. Qed.
Lemma D_94274 : decode_any W_94274 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94278 : bv 32 := 0x00074703.
Lemma F_94278 : fetch_word AsanUbsan.M.loaded_segments (0x942c0 : word) = Some W_94278.
Proof. vm_refl. Qed.
Lemma D_94278 : decode_any W_94278 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9427c : bv 32 := 0x00d507b3.
Lemma F_9427c : fetch_word AsanUbsan.M.loaded_segments (0x942c4 : word) = Some W_9427c.
Proof. vm_refl. Qed.
Lemma D_9427c : decode_any W_9427c = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94280 : bv 32 := 0x00168813.
Lemma F_94280 : fetch_word AsanUbsan.M.loaded_segments (0x942c8 : word) = Some W_94280.
Proof. vm_refl. Qed.
Lemma D_94280 : decode_any W_94280 = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94284 : bv 32 := 0xfff68693.
Lemma F_94284 : fetch_word AsanUbsan.M.loaded_segments (0x942cc : word) = Some W_94284.
Proof. vm_refl. Qed.
Lemma D_94284 : decode_any W_94284 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94288 : bv 32 := 0x00e78023.
Lemma F_94288 : fetch_word AsanUbsan.M.loaded_segments (0x942d0 : word) = Some W_94288.
Proof. vm_refl. Qed.
Lemma D_94288 : decode_any W_94288 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9428c : bv 32 := 0xff0664e3.
Lemma F_9428c : fetch_word AsanUbsan.M.loaded_segments (0x942d4 : word) = Some W_9428c.
Proof. vm_refl. Qed.
Lemma D_9428c : decode_any W_9428c = Some (Branch BC_LTU 12 16 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94290 : bv 32 := 0x00008067.
Lemma F_94290 : fetch_word AsanUbsan.M.loaded_segments (0x942d8 : word) = Some W_94290.
Proof. vm_refl. Qed.
Lemma D_94290 : decode_any W_94290 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94294 : bv 32 := 0x00a666b3.
Lemma F_94294 : fetch_word AsanUbsan.M.loaded_segments (0x942dc : word) = Some W_94294.
Proof. vm_refl. Qed.
Lemma D_94294 : decode_any W_94294 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94298 : bv 32 := 0x00f6f693.
Lemma F_94298 : fetch_word AsanUbsan.M.loaded_segments (0x942e0 : word) = Some W_94298.
Proof. vm_refl. Qed.
Lemma D_94298 : decode_any W_94298 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9429c : bv 32 := 0x02068063.
Lemma F_9429c : fetch_word AsanUbsan.M.loaded_segments (0x942e4 : word) = Some W_9429c.
Proof. vm_refl. Qed.
Lemma D_9429c : decode_any W_9429c = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942a0 : bv 32 := 0x04060863.
Lemma F_942a0 : fetch_word AsanUbsan.M.loaded_segments (0x942e8 : word) = Some W_942a0.
Proof. vm_refl. Qed.
Lemma D_942a0 : decode_any W_942a0 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942a4 : bv 32 := 0x00c50633.
Lemma F_942a4 : fetch_word AsanUbsan.M.loaded_segments (0x942ec : word) = Some W_942a4.
Proof. vm_refl. Qed.
Lemma D_942a4 : decode_any W_942a4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942a8 : bv 32 := 0x00050693.
Lemma F_942a8 : fetch_word AsanUbsan.M.loaded_segments (0x942f0 : word) = Some W_942a8.
Proof. vm_refl. Qed.
Lemma D_942a8 : decode_any W_942a8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942ac : bv 32 := 0x00b68023.
Lemma F_942ac : fetch_word AsanUbsan.M.loaded_segments (0x942f4 : word) = Some W_942ac.
Proof. vm_refl. Qed.
Lemma D_942ac : decode_any W_942ac = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942b0 : bv 32 := 0x00168693.
Lemma F_942b0 : fetch_word AsanUbsan.M.loaded_segments (0x942f8 : word) = Some W_942b0.
Proof. vm_refl. Qed.
Lemma D_942b0 : decode_any W_942b0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942b4 : bv 32 := 0xfec69ce3.
Lemma F_942b4 : fetch_word AsanUbsan.M.loaded_segments (0x942fc : word) = Some W_942b4.
Proof. vm_refl. Qed.
Lemma D_942b4 : decode_any W_942b4 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942b8 : bv 32 := 0x0380006f.
Lemma F_942b8 : fetch_word AsanUbsan.M.loaded_segments (0x94300 : word) = Some W_942b8.
Proof. vm_refl. Qed.
Lemma D_942b8 : decode_any W_942b8 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942bc : bv 32 := 0x02060a63.
Lemma F_942bc : fetch_word AsanUbsan.M.loaded_segments (0x94304 : word) = Some W_942bc.
Proof. vm_refl. Qed.
Lemma D_942bc : decode_any W_942bc = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942c0 : bv 32 := 0x00c50633.
Lemma F_942c0 : fetch_word AsanUbsan.M.loaded_segments (0x94308 : word) = Some W_942c0.
Proof. vm_refl. Qed.
Lemma D_942c0 : decode_any W_942c0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942c4 : bv 32 := 0x00859693.
Lemma F_942c4 : fetch_word AsanUbsan.M.loaded_segments (0x9430c : word) = Some W_942c4.
Proof. vm_refl. Qed.
Lemma D_942c4 : decode_any W_942c4 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942c8 : bv 32 := 0x00b6e5b3.
Lemma F_942c8 : fetch_word AsanUbsan.M.loaded_segments (0x94310 : word) = Some W_942c8.
Proof. vm_refl. Qed.
Lemma D_942c8 : decode_any W_942c8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942cc : bv 32 := 0x01059693.
Lemma F_942cc : fetch_word AsanUbsan.M.loaded_segments (0x94314 : word) = Some W_942cc.
Proof. vm_refl. Qed.
Lemma D_942cc : decode_any W_942cc = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942d0 : bv 32 := 0x00b6e5b3.
Lemma F_942d0 : fetch_word AsanUbsan.M.loaded_segments (0x94318 : word) = Some W_942d0.
Proof. vm_refl. Qed.
Lemma D_942d0 : decode_any W_942d0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942d4 : bv 32 := 0x02059693.
Lemma F_942d4 : fetch_word AsanUbsan.M.loaded_segments (0x9431c : word) = Some W_942d4.
Proof. vm_refl. Qed.
Lemma D_942d4 : decode_any W_942d4 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942d8 : bv 32 := 0x00b6e5b3.
Lemma F_942d8 : fetch_word AsanUbsan.M.loaded_segments (0x94320 : word) = Some W_942d8.
Proof. vm_refl. Qed.
Lemma D_942d8 : decode_any W_942d8 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942dc : bv 32 := 0x00050693.
Lemma F_942dc : fetch_word AsanUbsan.M.loaded_segments (0x94324 : word) = Some W_942dc.
Proof. vm_refl. Qed.
Lemma D_942dc : decode_any W_942dc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942e0 : bv 32 := 0x00b6b023.
Lemma F_942e0 : fetch_word AsanUbsan.M.loaded_segments (0x94328 : word) = Some W_942e0.
Proof. vm_refl. Qed.
Lemma D_942e0 : decode_any W_942e0 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942e4 : bv 32 := 0x00b6b423.
Lemma F_942e4 : fetch_word AsanUbsan.M.loaded_segments (0x9432c : word) = Some W_942e4.
Proof. vm_refl. Qed.
Lemma D_942e4 : decode_any W_942e4 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942e8 : bv 32 := 0x01068693.
Lemma F_942e8 : fetch_word AsanUbsan.M.loaded_segments (0x94330 : word) = Some W_942e8.
Proof. vm_refl. Qed.
Lemma D_942e8 : decode_any W_942e8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942ec : bv 32 := 0xfec6eae3.
Lemma F_942ec : fetch_word AsanUbsan.M.loaded_segments (0x94334 : word) = Some W_942ec.
Proof. vm_refl. Qed.
Lemma D_942ec : decode_any W_942ec = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_942f0 : bv 32 := 0x00008067.
Lemma F_942f0 : fetch_word AsanUbsan.M.loaded_segments (0x94338 : word) = Some W_942f0.
Proof. vm_refl. Qed.
Lemma D_942f0 : decode_any W_942f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_943e8 : bv 32 := 0x00000593.
Lemma F_943e8 : fetch_word AsanUbsan.M.loaded_segments (0x94430 : word) = Some W_943e8.
Proof. vm_refl. Qed.
Lemma D_943e8 : decode_any W_943e8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_943ec : bv 32 := 0x00b50633.
Lemma F_943ec : fetch_word AsanUbsan.M.loaded_segments (0x94434 : word) = Some W_943ec.
Proof. vm_refl. Qed.
Lemma D_943ec : decode_any W_943ec = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_943f0 : bv 32 := 0x00064603.
Lemma F_943f0 : fetch_word AsanUbsan.M.loaded_segments (0x94438 : word) = Some W_943f0.
Proof. vm_refl. Qed.
Lemma D_943f0 : decode_any W_943f0 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_943f4 : bv 32 := 0x00158593.
Lemma F_943f4 : fetch_word AsanUbsan.M.loaded_segments (0x9443c : word) = Some W_943f4.
Proof. vm_refl. Qed.
Lemma D_943f4 : decode_any W_943f4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_943f8 : bv 32 := 0xfe061ae3.
Lemma F_943f8 : fetch_word AsanUbsan.M.loaded_segments (0x94440 : word) = Some W_943f8.
Proof. vm_refl. Qed.
Lemma D_943f8 : decode_any W_943f8 = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_943fc : bv 32 := 0xfff58513.
Lemma F_943fc : fetch_word AsanUbsan.M.loaded_segments (0x94444 : word) = Some W_943fc.
Proof. vm_refl. Qed.
Lemma D_943fc : decode_any W_943fc = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94400 : bv 32 := 0x00008067.
Lemma F_94400 : fetch_word AsanUbsan.M.loaded_segments (0x94448 : word) = Some W_94400.
Proof. vm_refl. Qed.
Lemma D_94400 : decode_any W_94400 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_947e0 : bv 32 := 0xff010113.
Lemma F_947e0 : fetch_word AsanUbsan.M.loaded_segments (0x94828 : word) = Some W_947e0.
Proof. vm_refl. Qed.
Lemma D_947e0 : decode_any W_947e0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_947e4 : bv 32 := 0x00113423.
Lemma F_947e4 : fetch_word AsanUbsan.M.loaded_segments (0x9482c : word) = Some W_947e4.
Proof. vm_refl. Qed.
Lemma D_947e4 : decode_any W_947e4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_947e8 : bv 32 := 0x00058693.
Lemma F_947e8 : fetch_word AsanUbsan.M.loaded_segments (0x94830 : word) = Some W_947e8.
Proof. vm_refl. Qed.
Lemma D_947e8 : decode_any W_947e8 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_947ec : bv 32 := 0x00100713.
Lemma F_947ec : fetch_word AsanUbsan.M.loaded_segments (0x94834 : word) = Some W_947ec.
Proof. vm_refl. Qed.
Lemma D_947ec : decode_any W_947ec = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_947f0 : bv 32 := 0x02871713.
Lemma F_947f0 : fetch_word AsanUbsan.M.loaded_segments (0x94838 : word) = Some W_947f0.
Proof. vm_refl. Qed.
Lemma D_947f0 : decode_any W_947f0 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_947f4 : bv 32 := 0x00170593.
Lemma F_947f4 : fetch_word AsanUbsan.M.loaded_segments (0x9483c : word) = Some W_947f4.
Proof. vm_refl. Qed.
Lemma D_947f4 : decode_any W_947f4 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_947f8 : bv 32 := 0x08b6f263.
Lemma F_947f8 : fetch_word AsanUbsan.M.loaded_segments (0x94840 : word) = Some W_947f8.
Proof. vm_refl. Qed.
Lemma D_947f8 : decode_any W_947f8 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_947fc : bv 32 := 0x00000593.
Lemma F_947fc : fetch_word AsanUbsan.M.loaded_segments (0x94844 : word) = Some W_947fc.
Proof. vm_refl. Qed.
Lemma D_947fc : decode_any W_947fc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94800 : bv 32 := 0x00d50733.
Lemma F_94800 : fetch_word AsanUbsan.M.loaded_segments (0x94848 : word) = Some W_94800.
Proof. vm_refl. Qed.
Lemma D_94800 : decode_any W_94800 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94804 : bv 32 := 0x00750793.
Lemma F_94804 : fetch_word AsanUbsan.M.loaded_segments (0x9484c : word) = Some W_94804.
Proof. vm_refl. Qed.
Lemma D_94804 : decode_any W_94804 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94808 : bv 32 := 0xff87f793.
Lemma F_94808 : fetch_word AsanUbsan.M.loaded_segments (0x94850 : word) = Some W_94808.
Proof. vm_refl. Qed.
Lemma D_94808 : decode_any W_94808 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9480c : bv 32 := 0xff877613.
Lemma F_9480c : fetch_word AsanUbsan.M.loaded_segments (0x94854 : word) = Some W_9480c.
Proof. vm_refl. Qed.
Lemma D_9480c : decode_any W_9480c = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94810 : bv 32 := 0x02f57463.
Lemma F_94810 : fetch_word AsanUbsan.M.loaded_segments (0x94858 : word) = Some W_94810.
Proof. vm_refl. Qed.
Lemma D_94810 : decode_any W_94810 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94814 : bv 32 := 0x02068263.
Lemma F_94814 : fetch_word AsanUbsan.M.loaded_segments (0x9485c : word) = Some W_94814.
Proof. vm_refl. Qed.
Lemma D_94814 : decode_any W_94814 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94818 : bv 32 := 0x00000593.
Lemma F_94818 : fetch_word AsanUbsan.M.loaded_segments (0x94860 : word) = Some W_94818.
Proof. vm_refl. Qed.
Lemma D_94818 : decode_any W_94818 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9481c : bv 32 := 0x00150693.
Lemma F_9481c : fetch_word AsanUbsan.M.loaded_segments (0x94864 : word) = Some W_9481c.
Proof. vm_refl. Qed.
Lemma D_9481c : decode_any W_9481c = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94820 : bv 32 := 0x00068813.
Lemma F_94820 : fetch_word AsanUbsan.M.loaded_segments (0x94868 : word) = Some W_94820.
Proof. vm_refl. Qed.
Lemma D_94820 : decode_any W_94820 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94824 : bv 32 := 0xfff6c683.
Lemma F_94824 : fetch_word AsanUbsan.M.loaded_segments (0x9486c : word) = Some W_94824.
Proof. vm_refl. Qed.
Lemma D_94824 : decode_any W_94824 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94828 : bv 32 := 0x00d5e5b3.
Lemma F_94828 : fetch_word AsanUbsan.M.loaded_segments (0x94870 : word) = Some W_94828.
Proof. vm_refl. Qed.
Lemma D_94828 : decode_any W_94828 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9482c : bv 32 := 0x00f87663.
Lemma F_9482c : fetch_word AsanUbsan.M.loaded_segments (0x94874 : word) = Some W_9482c.
Proof. vm_refl. Qed.
Lemma D_9482c : decode_any W_9482c = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94830 : bv 32 := 0x00180693.
Lemma F_94830 : fetch_word AsanUbsan.M.loaded_segments (0x94878 : word) = Some W_94830.
Proof. vm_refl. Qed.
Lemma D_94830 : decode_any W_94830 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94834 : bv 32 := 0xfee866e3.
Lemma F_94834 : fetch_word AsanUbsan.M.loaded_segments (0x9487c : word) = Some W_94834.
Proof. vm_refl. Qed.
Lemma D_94834 : decode_any W_94834 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94838 : bv 32 := 0x00c7fa63.
Lemma F_94838 : fetch_word AsanUbsan.M.loaded_segments (0x94880 : word) = Some W_94838.
Proof. vm_refl. Qed.
Lemma D_94838 : decode_any W_94838 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9483c : bv 32 := 0x0007b683.
Lemma F_9483c : fetch_word AsanUbsan.M.loaded_segments (0x94884 : word) = Some W_9483c.
Proof. vm_refl. Qed.
Lemma D_9483c : decode_any W_9483c = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94840 : bv 32 := 0x00878793.
Lemma F_94840 : fetch_word AsanUbsan.M.loaded_segments (0x94888 : word) = Some W_94840.
Proof. vm_refl. Qed.
Lemma D_94840 : decode_any W_94840 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94844 : bv 32 := 0x00b6e5b3.
Lemma F_94844 : fetch_word AsanUbsan.M.loaded_segments (0x9488c : word) = Some W_94844.
Proof. vm_refl. Qed.
Lemma D_94844 : decode_any W_94844 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94848 : bv 32 := 0xfec7eae3.
Lemma F_94848 : fetch_word AsanUbsan.M.loaded_segments (0x94890 : word) = Some W_94848.
Proof. vm_refl. Qed.
Lemma D_94848 : decode_any W_94848 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9484c : bv 32 := 0x02a66063.
Lemma F_9484c : fetch_word AsanUbsan.M.loaded_segments (0x94894 : word) = Some W_9484c.
Proof. vm_refl. Qed.
Lemma D_9484c : decode_any W_9484c = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94850 : bv 32 := 0x00e67e63.
Lemma F_94850 : fetch_word AsanUbsan.M.loaded_segments (0x94898 : word) = Some W_94850.
Proof. vm_refl. Qed.
Lemma D_94850 : decode_any W_94850 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94854 : bv 32 := 0x40c70733.
Lemma F_94854 : fetch_word AsanUbsan.M.loaded_segments (0x9489c : word) = Some W_94854.
Proof. vm_refl. Qed.
Lemma D_94854 : decode_any W_94854 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94858 : bv 32 := 0x00064503.
Lemma F_94858 : fetch_word AsanUbsan.M.loaded_segments (0x948a0 : word) = Some W_94858.
Proof. vm_refl. Qed.
Lemma D_94858 : decode_any W_94858 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9485c : bv 32 := 0xfff70713.
Lemma F_9485c : fetch_word AsanUbsan.M.loaded_segments (0x948a4 : word) = Some W_9485c.
Proof. vm_refl. Qed.
Lemma D_9485c : decode_any W_9485c = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94860 : bv 32 := 0x00a5e5b3.
Lemma F_94860 : fetch_word AsanUbsan.M.loaded_segments (0x948a8 : word) = Some W_94860.
Proof. vm_refl. Qed.
Lemma D_94860 : decode_any W_94860 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94864 : bv 32 := 0x00160613.
Lemma F_94864 : fetch_word AsanUbsan.M.loaded_segments (0x948ac : word) = Some W_94864.
Proof. vm_refl. Qed.
Lemma D_94864 : decode_any W_94864 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94868 : bv 32 := 0xfe0718e3.
Lemma F_94868 : fetch_word AsanUbsan.M.loaded_segments (0x948b0 : word) = Some W_94868.
Proof. vm_refl. Qed.
Lemma D_94868 : decode_any W_94868 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9486c : bv 32 := 0x0015b513.
Lemma F_9486c : fetch_word AsanUbsan.M.loaded_segments (0x948b4 : word) = Some W_9486c.
Proof. vm_refl. Qed.
Lemma D_9486c : decode_any W_9486c = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94870 : bv 32 := 0x00813083.
Lemma F_94870 : fetch_word AsanUbsan.M.loaded_segments (0x948b8 : word) = Some W_94870.
Proof. vm_refl. Qed.
Lemma D_94870 : decode_any W_94870 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94874 : bv 32 := 0x01010113.
Lemma F_94874 : fetch_word AsanUbsan.M.loaded_segments (0x948bc : word) = Some W_94874.
Proof. vm_refl. Qed.
Lemma D_94874 : decode_any W_94874 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94878 : bv 32 := 0x00008067.
Lemma F_94878 : fetch_word AsanUbsan.M.loaded_segments (0x948c0 : word) = Some W_94878.
Proof. vm_refl. Qed.
Lemma D_94878 : decode_any W_94878 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a90 : bv 32 := 0xfffff637.
Lemma F_94a90 : fetch_word AsanUbsan.M.loaded_segments (0x94ad8 : word) = Some W_94a90.
Proof. vm_refl. Qed.
Lemma D_94a90 : decode_any W_94a90 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a94 : bv 32 := 0x0016069b.
Lemma F_94a94 : fetch_word AsanUbsan.M.loaded_segments (0x94adc : word) = Some W_94a94.
Proof. vm_refl. Qed.
Lemma D_94a94 : decode_any W_94a94 = Some (OpImm32 13 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a98 : bv 32 := 0x00d56863.
Lemma F_94a98 : fetch_word AsanUbsan.M.loaded_segments (0x94ae0 : word) = Some W_94a98.
Proof. vm_refl. Qed.
Lemma D_94a98 : decode_any W_94a98 = Some (Branch BC_LTU 10 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94aa8 : bv 32 := 0x00a63533.
Lemma F_94aa8 : fetch_word AsanUbsan.M.loaded_segments (0x94af0 : word) = Some W_94aa8.
Proof. vm_refl. Qed.
Lemma D_94aa8 : decode_any W_94aa8 = Some (Op ALU_SLTU 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94aac : bv 32 := 0x00008067.
Lemma F_94aac : fetch_word AsanUbsan.M.loaded_segments (0x94af4 : word) = Some W_94aac.
Proof. vm_refl. Qed.
Lemma D_94aac : decode_any W_94aac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ab0 : bv 32 := 0x0de00893.
Lemma F_94ab0 : fetch_word AsanUbsan.M.loaded_segments (0x94af8 : word) = Some W_94ab0.
Proof. vm_refl. Qed.
Lemma D_94ab0 : decode_any W_94ab0 = Some (OpImm ALU_ADD 17 0 222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ab4 : bv 32 := 0x00000073.
Lemma F_94ab4 : fetch_word AsanUbsan.M.loaded_segments (0x94afc : word) = Some W_94ab4.
Proof. vm_refl. Qed.
Lemma D_94ab4 : decode_any W_94ab4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_94ab4 : is_ecall W_94ab4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_94ab8 : bv 32 := 0x00008067.
Lemma F_94ab8 : fetch_word AsanUbsan.M.loaded_segments (0x94b00 : word) = Some W_94ab8.
Proof. vm_refl. Qed.
Lemma D_94ab8 : decode_any W_94ab8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94abc : bv 32 := 0x0d700893.
Lemma F_94abc : fetch_word AsanUbsan.M.loaded_segments (0x94b04 : word) = Some W_94abc.
Proof. vm_refl. Qed.
Lemma D_94abc : decode_any W_94abc = Some (OpImm ALU_ADD 17 0 215, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ac0 : bv 32 := 0x00000073.
Lemma F_94ac0 : fetch_word AsanUbsan.M.loaded_segments (0x94b08 : word) = Some W_94ac0.
Proof. vm_refl. Qed.
Lemma D_94ac0 : decode_any W_94ac0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_94ac0 : is_ecall W_94ac0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_94ac4 : bv 32 := 0x00008067.
Lemma F_94ac4 : fetch_word AsanUbsan.M.loaded_segments (0x94b0c : word) = Some W_94ac4.
Proof. vm_refl. Qed.
Lemma D_94ac4 : decode_any W_94ac4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ad8 : bv 32 := 0x000d0697.
Lemma F_94ad8 : fetch_word AsanUbsan.M.loaded_segments (0x94b20 : word) = Some W_94ad8.
Proof. vm_refl. Qed.
Lemma D_94ad8 : decode_any W_94ad8 = Some (Auipc 13 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94adc : bv 32 := 0xa386b683.
Lemma F_94adc : fetch_word AsanUbsan.M.loaded_segments (0x94b24 : word) = Some W_94adc.
Proof. vm_refl. Qed.
Lemma D_94adc : decode_any W_94adc = Some (Load SZ8 true 13 13 2616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ae0 : bv 32 := 0x00068a63.
Lemma F_94ae0 : fetch_word AsanUbsan.M.loaded_segments (0x94b28 : word) = Some W_94ae0.
Proof. vm_refl. Qed.
Lemma D_94ae0 : decode_any W_94ae0 = Some (Branch BC_EQ 13 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ae4 : bv 32 := 0x00400693.
Lemma F_94ae4 : fetch_word AsanUbsan.M.loaded_segments (0x94b2c : word) = Some W_94ae4.
Proof. vm_refl. Qed.
Lemma D_94ae4 : decode_any W_94ae4 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ae8 : bv 32 := 0x00d60663.
Lemma F_94ae8 : fetch_word AsanUbsan.M.loaded_segments (0x94b30 : word) = Some W_94ae8.
Proof. vm_refl. Qed.
Lemma D_94ae8 : decode_any W_94ae8 = Some (Branch BC_EQ 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94af4 : bv 32 := 0x0e900893.
Lemma F_94af4 : fetch_word AsanUbsan.M.loaded_segments (0x94b3c : word) = Some W_94af4.
Proof. vm_refl. Qed.
Lemma D_94af4 : decode_any W_94af4 = Some (OpImm ALU_ADD 17 0 233, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94af8 : bv 32 := 0x00000073.
Lemma F_94af8 : fetch_word AsanUbsan.M.loaded_segments (0x94b40 : word) = Some W_94af8.
Proof. vm_refl. Qed.
Lemma D_94af8 : decode_any W_94af8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_94af8 : is_ecall W_94af8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_94afc : bv 32 := 0x0005051b.
Lemma F_94afc : fetch_word AsanUbsan.M.loaded_segments (0x94b44 : word) = Some W_94afc.
Proof. vm_refl. Qed.
Lemma D_94afc : decode_any W_94afc = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94b00 : bv 32 := 0x00008067.
Lemma F_94b00 : fetch_word AsanUbsan.M.loaded_segments (0x94b48 : word) = Some W_94b00.
Proof. vm_refl. Qed.
Lemma D_94b00 : decode_any W_94b00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

