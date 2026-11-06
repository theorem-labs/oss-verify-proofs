(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation PSEGS := ImgP.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_961b8 : bv 32 := 0x00000073.
Lemma F_961b8 : fetch_word PSEGS (0x961b8 : word) = Some W_961b8.
Proof. vm_refl. Qed.
Lemma D_961b8 : decode_any W_961b8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_961b8 : is_ecall W_961b8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_961bc : bv 32 := 0x0006851b.
Lemma F_961bc : fetch_word PSEGS (0x961bc : word) = Some W_961bc.
Proof. vm_refl. Qed.
Lemma D_961bc : decode_any W_961bc = Some (OpImm32 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961c0 : bv 32 := 0x094000ef.
Lemma F_961c0 : fetch_word PSEGS (0x961c0 : word) = Some W_961c0.
Proof. vm_refl. Qed.
Lemma D_961c0 : decode_any W_961c0 = Some (Jal 1 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961c4 : bv 32 := 0x0004b583.
Lemma F_961c4 : fetch_word PSEGS (0x961c4 : word) = Some W_961c4.
Proof. vm_refl. Qed.
Lemma D_961c4 : decode_any W_961c4 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961c8 : bv 32 := 0x01013603.
Lemma F_961c8 : fetch_word PSEGS (0x961c8 : word) = Some W_961c8.
Proof. vm_refl. Qed.
Lemma D_961c8 : decode_any W_961c8 = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961cc : bv 32 := 0x00c59e63.
Lemma F_961cc : fetch_word PSEGS (0x961cc : word) = Some W_961cc.
Proof. vm_refl. Qed.
Lemma D_961cc : decode_any W_961cc = Some (Branch BC_NE 11 12 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961d0 : bv 32 := 0x0005051b.
Lemma F_961d0 : fetch_word PSEGS (0x961d0 : word) = Some W_961d0.
Proof. vm_refl. Qed.
Lemma D_961d0 : decode_any W_961d0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961d4 : bv 32 := 0x02813083.
Lemma F_961d4 : fetch_word PSEGS (0x961d4 : word) = Some W_961d4.
Proof. vm_refl. Qed.
Lemma D_961d4 : decode_any W_961d4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961d8 : bv 32 := 0x02013403.
Lemma F_961d8 : fetch_word PSEGS (0x961d8 : word) = Some W_961d8.
Proof. vm_refl. Qed.
Lemma D_961d8 : decode_any W_961d8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961dc : bv 32 := 0x01813483.
Lemma F_961dc : fetch_word PSEGS (0x961dc : word) = Some W_961dc.
Proof. vm_refl. Qed.
Lemma D_961dc : decode_any W_961dc = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961e0 : bv 32 := 0x06010113.
Lemma F_961e0 : fetch_word PSEGS (0x961e0 : word) = Some W_961e0.
Proof. vm_refl. Qed.
Lemma D_961e0 : decode_any W_961e0 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961e4 : bv 32 := 0x00008067.
Lemma F_961e4 : fetch_word PSEGS (0x961e4 : word) = Some W_961e4.
Proof. vm_refl. Qed.
Lemma D_961e4 : decode_any W_961e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961e8 : bv 32 := 0x064000ef.
Lemma F_961e8 : fetch_word PSEGS (0x961e8 : word) = Some W_961e8.
Proof. vm_refl. Qed.
Lemma D_961e8 : decode_any W_961e8 = Some (Jal 1 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961ec : bv 32 := 0xff010113.
Lemma F_961ec : fetch_word PSEGS (0x961ec : word) = Some W_961ec.
Proof. vm_refl. Qed.
Lemma D_961ec : decode_any W_961ec = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961f0 : bv 32 := 0x00113423.
Lemma F_961f0 : fetch_word PSEGS (0x961f0 : word) = Some W_961f0.
Proof. vm_refl. Qed.
Lemma D_961f0 : decode_any W_961f0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961f4 : bv 32 := 0x00050e63.
Lemma F_961f4 : fetch_word PSEGS (0x961f4 : word) = Some W_961f4.
Proof. vm_refl. Qed.
Lemma D_961f4 : decode_any W_961f4 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961f8 : bv 32 := 0x00050593.
Lemma F_961f8 : fetch_word PSEGS (0x961f8 : word) = Some W_961f8.
Proof. vm_refl. Qed.
Lemma D_961f8 : decode_any W_961f8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_961fc : bv 32 := 0x0001c517.
Lemma F_961fc : fetch_word PSEGS (0x961fc : word) = Some W_961fc.
Proof. vm_refl. Qed.
Lemma D_961fc : decode_any W_961fc = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96200 : bv 32 := 0x9b453503.
Lemma F_96200 : fetch_word PSEGS (0x96200 : word) = Some W_96200.
Proof. vm_refl. Qed.
Lemma D_96200 : decode_any W_96200 = Some (Load SZ8 true 10 10 2484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96204 : bv 32 := 0x00800613.
Lemma F_96204 : fetch_word PSEGS (0x96204 : word) = Some W_96204.
Proof. vm_refl. Qed.
Lemma D_96204 : decode_any W_96204 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96208 : bv 32 := 0x520100ef.
Lemma F_96208 : fetch_word PSEGS (0x96208 : word) = Some W_96208.
Proof. vm_refl. Qed.
Lemma D_96208 : decode_any W_96208 = Some (Jal 1 66848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9620c : bv 32 := 0x01c0006f.
Lemma F_9620c : fetch_word PSEGS (0x9620c : word) = Some W_9620c.
Proof. vm_refl. Qed.
Lemma D_9620c : decode_any W_9620c = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96210 : bv 32 := 0x0001c517.
Lemma F_96210 : fetch_word PSEGS (0x96210 : word) = Some W_96210.
Proof. vm_refl. Qed.
Lemma D_96210 : decode_any W_96210 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96214 : bv 32 := 0x9a053503.
Lemma F_96214 : fetch_word PSEGS (0x96214 : word) = Some W_96214.
Proof. vm_refl. Qed.
Lemma D_96214 : decode_any W_96214 = Some (Load SZ8 true 10 10 2464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96218 : bv 32 := 0x41c655b7.
Lemma F_96218 : fetch_word PSEGS (0x96218 : word) = Some W_96218.
Proof. vm_refl. Qed.
Lemma D_96218 : decode_any W_96218 = Some (Lui 11 269413, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9621c : bv 32 := 0xe6d5859b.
Lemma F_9621c : fetch_word PSEGS (0x9621c : word) = Some W_9621c.
Proof. vm_refl. Qed.
Lemma D_9621c : decode_any W_9621c = Some (OpImm32 11 11 3693, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96220 : bv 32 := 0x02b505b3.
Lemma F_96220 : fetch_word PSEGS (0x96220 : word) = Some W_96220.
Proof. vm_refl. Qed.
Lemma D_96220 : decode_any W_96220 = Some (Mul M_MUL 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96224 : bv 32 := 0x00b53023.
Lemma F_96224 : fetch_word PSEGS (0x96224 : word) = Some W_96224.
Proof. vm_refl. Qed.
Lemma D_96224 : decode_any W_96224 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96228 : bv 32 := 0x0001c517.
Lemma F_96228 : fetch_word PSEGS (0x96228 : word) = Some W_96228.
Proof. vm_refl. Qed.
Lemma D_96228 : decode_any W_96228 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9622c : bv 32 := 0x98853503.
Lemma F_9622c : fetch_word PSEGS (0x9622c : word) = Some W_9622c.
Proof. vm_refl. Qed.
Lemma D_9622c : decode_any W_9622c = Some (Load SZ8 true 10 10 2440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96230 : bv 32 := 0x000500a3.
Lemma F_96230 : fetch_word PSEGS (0x96230 : word) = Some W_96230.
Proof. vm_refl. Qed.
Lemma D_96230 : decode_any W_96230 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96234 : bv 32 := 0x00053503.
Lemma F_96234 : fetch_word PSEGS (0x96234 : word) = Some W_96234.
Proof. vm_refl. Qed.
Lemma D_96234 : decode_any W_96234 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96238 : bv 32 := 0x00020593.
Lemma F_96238 : fetch_word PSEGS (0x96238 : word) = Some W_96238.
Proof. vm_refl. Qed.
Lemma D_96238 : decode_any W_96238 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9623c : bv 32 := 0xfea5b823.
Lemma F_9623c : fetch_word PSEGS (0x9623c : word) = Some W_9623c.
Proof. vm_refl. Qed.
Lemma D_9623c : decode_any W_9623c = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96240 : bv 32 := 0x00813083.
Lemma F_96240 : fetch_word PSEGS (0x96240 : word) = Some W_96240.
Proof. vm_refl. Qed.
Lemma D_96240 : decode_any W_96240 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96244 : bv 32 := 0x01010113.
Lemma F_96244 : fetch_word PSEGS (0x96244 : word) = Some W_96244.
Proof. vm_refl. Qed.
Lemma D_96244 : decode_any W_96244 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96248 : bv 32 := 0x00008067.
Lemma F_96248 : fetch_word PSEGS (0x96248 : word) = Some W_96248.
Proof. vm_refl. Qed.
Lemma D_96248 : decode_any W_96248 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9624c : bv 32 := 0x00000023.
Lemma F_9624c : fetch_word PSEGS (0x9624c : word) = Some W_9624c.
Proof. vm_refl. Qed.
Lemma D_9624c : decode_any W_9624c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96250 : bv 32 := 0x00008067.
Lemma F_96250 : fetch_word PSEGS (0x96250 : word) = Some W_96250.
Proof. vm_refl. Qed.
Lemma D_96250 : decode_any W_96250 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96254 : bv 32 := 0xfffff5b7.
Lemma F_96254 : fetch_word PSEGS (0x96254 : word) = Some W_96254.
Proof. vm_refl. Qed.
Lemma D_96254 : decode_any W_96254 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96258 : bv 32 := 0x0015859b.
Lemma F_96258 : fetch_word PSEGS (0x96258 : word) = Some W_96258.
Proof. vm_refl. Qed.
Lemma D_96258 : decode_any W_96258 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9625c : bv 32 := 0x02b56663.
Lemma F_9625c : fetch_word PSEGS (0x9625c : word) = Some W_9625c.
Proof. vm_refl. Qed.
Lemma D_9625c : decode_any W_9625c = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96260 : bv 32 := 0xff010113.
Lemma F_96260 : fetch_word PSEGS (0x96260 : word) = Some W_96260.
Proof. vm_refl. Qed.
Lemma D_96260 : decode_any W_96260 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96264 : bv 32 := 0x00113423.
Lemma F_96264 : fetch_word PSEGS (0x96264 : word) = Some W_96264.
Proof. vm_refl. Qed.
Lemma D_96264 : decode_any W_96264 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96268 : bv 32 := 0x00813023.
Lemma F_96268 : fetch_word PSEGS (0x96268 : word) = Some W_96268.
Proof. vm_refl. Qed.
Lemma D_96268 : decode_any W_96268 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9626c : bv 32 := 0x40a0043b.
Lemma F_9626c : fetch_word PSEGS (0x9626c : word) = Some W_9626c.
Proof. vm_refl. Qed.
Lemma D_9626c : decode_any W_9626c = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96270 : bv 32 := 0xa8dff0ef.
Lemma F_96270 : fetch_word PSEGS (0x96270 : word) = Some W_96270.
Proof. vm_refl. Qed.
Lemma D_96270 : decode_any W_96270 = Some (Jal 1 2095756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96274 : bv 32 := 0x00852023.
Lemma F_96274 : fetch_word PSEGS (0x96274 : word) = Some W_96274.
Proof. vm_refl. Qed.
Lemma D_96274 : decode_any W_96274 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96278 : bv 32 := 0xfff00513.
Lemma F_96278 : fetch_word PSEGS (0x96278 : word) = Some W_96278.
Proof. vm_refl. Qed.
Lemma D_96278 : decode_any W_96278 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9627c : bv 32 := 0x00813083.
Lemma F_9627c : fetch_word PSEGS (0x9627c : word) = Some W_9627c.
Proof. vm_refl. Qed.
Lemma D_9627c : decode_any W_9627c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96280 : bv 32 := 0x00013403.
Lemma F_96280 : fetch_word PSEGS (0x96280 : word) = Some W_96280.
Proof. vm_refl. Qed.
Lemma D_96280 : decode_any W_96280 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96284 : bv 32 := 0x01010113.
Lemma F_96284 : fetch_word PSEGS (0x96284 : word) = Some W_96284.
Proof. vm_refl. Qed.
Lemma D_96284 : decode_any W_96284 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96288 : bv 32 := 0x00008067.
Lemma F_96288 : fetch_word PSEGS (0x96288 : word) = Some W_96288.
Proof. vm_refl. Qed.
Lemma D_96288 : decode_any W_96288 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9628c : bv 32 := 0xe5010113.
Lemma F_9628c : fetch_word PSEGS (0x9628c : word) = Some W_9628c.
Proof. vm_refl. Qed.
Lemma D_9628c : decode_any W_9628c = Some (OpImm ALU_ADD 2 2 3664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96290 : bv 32 := 0x1a113423.
Lemma F_96290 : fetch_word PSEGS (0x96290 : word) = Some W_96290.
Proof. vm_refl. Qed.
Lemma D_96290 : decode_any W_96290 = Some (Store SZ8 2 1 424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_962a4 : bv 32 := 0x00058493.
Lemma F_962a4 : fetch_word PSEGS (0x962a4 : word) = Some W_962a4.
Proof. vm_refl. Qed.
Lemma D_962a4 : decode_any W_962a4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_962a8 : bv 32 := 0x00050413.
Lemma F_962a8 : fetch_word PSEGS (0x962a8 : word) = Some W_962a8.
Proof. vm_refl. Qed.
Lemma D_962a8 : decode_any W_962a8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_962ac : bv 32 := 0x0001c517.
Lemma F_962ac : fetch_word PSEGS (0x962ac : word) = Some W_962ac.
Proof. vm_refl. Qed.
Lemma D_962ac : decode_any W_962ac = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_962b0 : bv 32 := 0x90453903.
Lemma F_962b0 : fetch_word PSEGS (0x962b0 : word) = Some W_962b0.
Proof. vm_refl. Qed.
Lemma D_962b0 : decode_any W_962b0 = Some (Load SZ8 true 18 10 2308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_962b4 : bv 32 := 0x00093503.
Lemma F_962b4 : fetch_word PSEGS (0x962b4 : word) = Some W_962b4.
Proof. vm_refl. Qed.
Lemma D_962b4 : decode_any W_962b4 = Some (Load SZ8 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_962b8 : bv 32 := 0x18a13023.
Lemma F_962b8 : fetch_word PSEGS (0x962b8 : word) = Some W_962b8.
Proof. vm_refl. Qed.
Lemma D_962b8 : decode_any W_962b8 = Some (Store SZ8 2 10 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_962d0 : bv 32 := 0x0004f517.
Lemma F_962d0 : fetch_word PSEGS (0x962d0 : word) = Some W_962d0.
Proof. vm_refl. Qed.
Lemma D_962d0 : decode_any W_962d0 = Some (Auipc 10 79, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_962d4 : bv 32 := 0x8e053503.
Lemma F_962d4 : fetch_word PSEGS (0x962d4 : word) = Some W_962d4.
Proof. vm_refl. Qed.
Lemma D_962d4 : decode_any W_962d4 = Some (Load SZ8 true 10 10 2272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_962d8 : bv 32 := 0x00053603.
Lemma F_962d8 : fetch_word PSEGS (0x962d8 : word) = Some W_962d8.
Proof. vm_refl. Qed.
Lemma D_962d8 : decode_any W_962d8 = Some (Load SZ8 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96310 : bv 32 := 0x07813583.
Lemma F_96310 : fetch_word PSEGS (0x96310 : word) = Some W_96310.
Proof. vm_refl. Qed.
Lemma D_96310 : decode_any W_96310 = Some (Load SZ8 true 11 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96314 : bv 32 := 0x06813503.
Lemma F_96314 : fetch_word PSEGS (0x96314 : word) = Some W_96314.
Proof. vm_refl. Qed.
Lemma D_96314 : decode_any W_96314 = Some (Load SZ8 true 10 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96318 : bv 32 := 0x0a058a63.
Lemma F_96318 : fetch_word PSEGS (0x96318 : word) = Some W_96318.
Proof. vm_refl. Qed.
Lemma D_96318 : decode_any W_96318 = Some (Branch BC_EQ 11 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9631c : bv 32 := 0x00000613.
Lemma F_9631c : fetch_word PSEGS (0x9631c : word) = Some W_9631c.
Proof. vm_refl. Qed.
Lemma D_9631c : decode_any W_9631c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96320 : bv 32 := 0x00000713.
Lemma F_96320 : fetch_word PSEGS (0x96320 : word) = Some W_96320.
Proof. vm_refl. Qed.
Lemma D_96320 : decode_any W_96320 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96324 : bv 32 := 0x07013683.
Lemma F_96324 : fetch_word PSEGS (0x96324 : word) = Some W_96324.
Proof. vm_refl. Qed.
Lemma D_96324 : decode_any W_96324 = Some (Load SZ8 true 13 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96328 : bv 32 := 0x0001b797.
Lemma F_96328 : fetch_word PSEGS (0x96328 : word) = Some W_96328.
Proof. vm_refl. Qed.
Lemma D_96328 : decode_any W_96328 = Some (Auipc 15 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9632c : bv 32 := 0x7207b783.
Lemma F_9632c : fetch_word PSEGS (0x9632c : word) = Some W_9632c.
Proof. vm_refl. Qed.
Lemma D_9632c : decode_any W_9632c = Some (Load SZ8 true 15 15 1824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96330 : bv 32 := 0x00600813.
Lemma F_96330 : fetch_word PSEGS (0x96330 : word) = Some W_96330.
Proof. vm_refl. Qed.
Lemma D_96330 : decode_any W_96330 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96334 : bv 32 := 0x00700893.
Lemma F_96334 : fetch_word PSEGS (0x96334 : word) = Some W_96334.
Proof. vm_refl. Qed.
Lemma D_96334 : decode_any W_96334 = Some (OpImm ALU_ADD 17 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96338 : bv 32 := 0x00200293.
Lemma F_96338 : fetch_word PSEGS (0x96338 : word) = Some W_96338.
Proof. vm_refl. Qed.
Lemma D_96338 : decode_any W_96338 = Some (OpImm ALU_ADD 5 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9633c : bv 32 := 0x00058313.
Lemma F_9633c : fetch_word PSEGS (0x9633c : word) = Some W_9633c.
Proof. vm_refl. Qed.
Lemma D_9633c : decode_any W_9633c = Some (OpImm ALU_ADD 6 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96340 : bv 32 := 0x00050393.
Lemma F_96340 : fetch_word PSEGS (0x96340 : word) = Some W_96340.
Proof. vm_refl. Qed.
Lemma D_96340 : decode_any W_96340 = Some (OpImm ALU_ADD 7 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96344 : bv 32 := 0x0140006f.
Lemma F_96344 : fetch_word PSEGS (0x96344 : word) = Some W_96344.
Proof. vm_refl. Qed.
Lemma D_96344 : decode_any W_96344 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96348 : bv 32 := 0xfff30313.
Lemma F_96348 : fetch_word PSEGS (0x96348 : word) = Some W_96348.
Proof. vm_refl. Qed.
Lemma D_96348 : decode_any W_96348 = Some (OpImm ALU_ADD 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9634c : bv 32 := 0x00d383b3.
Lemma F_9634c : fetch_word PSEGS (0x9634c : word) = Some W_9634c.
Proof. vm_refl. Qed.
Lemma D_9634c : decode_any W_9634c = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96350 : bv 32 := 0x000e0713.
Lemma F_96350 : fetch_word PSEGS (0x96350 : word) = Some W_96350.
Proof. vm_refl. Qed.
Lemma D_96350 : decode_any W_96350 = Some (OpImm ALU_ADD 14 28 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96354 : bv 32 := 0x02030a63.
Lemma F_96354 : fetch_word PSEGS (0x96354 : word) = Some W_96354.
Proof. vm_refl. Qed.
Lemma D_96354 : decode_any W_96354 = Some (Branch BC_EQ 6 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96358 : bv 32 := 0x0003ae83.
Lemma F_96358 : fetch_word PSEGS (0x96358 : word) = Some W_96358.
Proof. vm_refl. Qed.
Lemma D_96358 : decode_any W_96358 = Some (Load SZ4 true 29 7 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9635c : bv 32 := 0x00050e13.
Lemma F_9635c : fetch_word PSEGS (0x9635c : word) = Some W_9635c.
Proof. vm_refl. Qed.
Lemma D_9635c : decode_any W_9635c = Some (OpImm ALU_ADD 28 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96360 : bv 32 := 0x010e8863.
Lemma F_96360 : fetch_word PSEGS (0x96360 : word) = Some W_96360.
Proof. vm_refl. Qed.
Lemma D_96360 : decode_any W_96360 = Some (Branch BC_EQ 29 16 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96364 : bv 32 := 0x00078a63.
Lemma F_96364 : fetch_word PSEGS (0x96364 : word) = Some W_96364.
Proof. vm_refl. Qed.
Lemma D_96364 : decode_any W_96364 = Some (Branch BC_EQ 15 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96368 : bv 32 := 0x00078e13.
Lemma F_96368 : fetch_word PSEGS (0x96368 : word) = Some W_96368.
Proof. vm_refl. Qed.
Lemma D_96368 : decode_any W_96368 = Some (OpImm ALU_ADD 28 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963a8 : bv 32 := 0x040e0263.
Lemma F_963a8 : fetch_word PSEGS (0x963a8 : word) = Some W_963a8.
Proof. vm_refl. Qed.
Lemma D_963a8 : decode_any W_963a8 = Some (Branch BC_EQ 28 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963ac : bv 32 := 0x00100513.
Lemma F_963ac : fetch_word PSEGS (0x963ac : word) = Some W_963ac.
Proof. vm_refl. Qed.
Lemma D_963ac : decode_any W_963ac = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963b0 : bv 32 := 0x02a13823.
Lemma F_963b0 : fetch_word PSEGS (0x963b0 : word) = Some W_963b0.
Proof. vm_refl. Qed.
Lemma D_963b0 : decode_any W_963b0 = Some (Store SZ8 2 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963b4 : bv 32 := 0x04a13023.
Lemma F_963b4 : fetch_word PSEGS (0x963b4 : word) = Some W_963b4.
Proof. vm_refl. Qed.
Lemma D_963b4 : decode_any W_963b4 = Some (Store SZ8 2 10 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963b8 : bv 32 := 0x04013423.
Lemma F_963b8 : fetch_word PSEGS (0x963b8 : word) = Some W_963b8.
Proof. vm_refl. Qed.
Lemma D_963b8 : decode_any W_963b8 = Some (Store SZ8 2 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963bc : bv 32 := 0x04010513.
Lemma F_963bc : fetch_word PSEGS (0x963bc : word) = Some W_963bc.
Proof. vm_refl. Qed.
Lemma D_963bc : decode_any W_963bc = Some (OpImm ALU_ADD 10 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963c0 : bv 32 := 0x284110ef.
Lemma F_963c0 : fetch_word PSEGS (0x963c0 : word) = Some W_963c0.
Proof. vm_refl. Qed.
Lemma D_963c0 : decode_any W_963c0 = Some (Jal 1 70276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963c4 : bv 32 := 0x0300006f.
Lemma F_963c4 : fetch_word PSEGS (0x963c4 : word) = Some W_963c4.
Proof. vm_refl. Qed.
Lemma D_963c4 : decode_any W_963c4 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963c8 : bv 32 := 0x00000513.
Lemma F_963c8 : fetch_word PSEGS (0x963c8 : word) = Some W_963c8.
Proof. vm_refl. Qed.
Lemma D_963c8 : decode_any W_963c8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963cc : bv 32 := 0xfff7a597.
Lemma F_963cc : fetch_word PSEGS (0x963cc : word) = Some W_963cc.
Proof. vm_refl. Qed.
Lemma D_963cc : decode_any W_963cc = Some (Auipc 11 1048442, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963d0 : bv 32 := 0x3e358593.
Lemma F_963d0 : fetch_word PSEGS (0x963d0 : word) = Some W_963d0.
Proof. vm_refl. Qed.
Lemma D_963d0 : decode_any W_963d0 = Some (OpImm ALU_ADD 11 11 995, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963d4 : bv 32 := 0x00013023.
Lemma F_963d4 : fetch_word PSEGS (0x963d4 : word) = Some W_963d4.
Proof. vm_refl. Qed.
Lemma D_963d4 : decode_any W_963d4 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963d8 : bv 32 := 0x00b13423.
Lemma F_963d8 : fetch_word PSEGS (0x963d8 : word) = Some W_963d8.
Proof. vm_refl. Qed.
Lemma D_963d8 : decode_any W_963d8 = Some (Store SZ8 2 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963dc : bv 32 := 0x00a13823.
Lemma F_963dc : fetch_word PSEGS (0x963dc : word) = Some W_963dc.
Proof. vm_refl. Qed.
Lemma D_963dc : decode_any W_963dc = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963e0 : bv 32 := 0x00011c23.
Lemma F_963e0 : fetch_word PSEGS (0x963e0 : word) = Some W_963e0.
Proof. vm_refl. Qed.
Lemma D_963e0 : decode_any W_963e0 = Some (Store SZ2 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_963e4 : bv 32 := 0x02013023.
Lemma F_963e4 : fetch_word PSEGS (0x963e4 : word) = Some W_963e4.
Proof. vm_refl. Qed.
Lemma D_963e4 : decode_any W_963e4 = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9642c : bv 32 := 0x00008067.
Lemma F_9642c : fetch_word PSEGS (0x9642c : word) = Some W_9642c.
Proof. vm_refl. Qed.
Lemma D_9642c : decode_any W_9642c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96430 : bv 32 := 0xe1dff0ef.
Lemma F_96430 : fetch_word PSEGS (0x96430 : word) = Some W_96430.
Proof. vm_refl. Qed.
Lemma D_96430 : decode_any W_96430 = Some (Jal 1 2096668, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96434 : bv 32 := 0x00000513.
Lemma F_96434 : fetch_word PSEGS (0x96434 : word) = Some W_96434.
Proof. vm_refl. Qed.
Lemma D_96434 : decode_any W_96434 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96438 : bv 32 := 0x00008067.
Lemma F_96438 : fetch_word PSEGS (0x96438 : word) = Some W_96438.
Proof. vm_refl. Qed.
Lemma D_96438 : decode_any W_96438 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9643c : bv 32 := 0xff010113.
Lemma F_9643c : fetch_word PSEGS (0x9643c : word) = Some W_9643c.
Proof. vm_refl. Qed.
Lemma D_9643c : decode_any W_9643c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96440 : bv 32 := 0x00113423.
Lemma F_96440 : fetch_word PSEGS (0x96440 : word) = Some W_96440.
Proof. vm_refl. Qed.
Lemma D_96440 : decode_any W_96440 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96444 : bv 32 := 0x00852583.
Lemma F_96444 : fetch_word PSEGS (0x96444 : word) = Some W_96444.
Proof. vm_refl. Qed.
Lemma D_96444 : decode_any W_96444 = Some (Load SZ4 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96448 : bv 32 := 0x00010637.
Lemma F_96448 : fetch_word PSEGS (0x96448 : word) = Some W_96448.
Proof. vm_refl. Qed.
Lemma D_96448 : decode_any W_96448 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9644c : bv 32 := 0xf0060613.
Lemma F_9644c : fetch_word PSEGS (0x9644c : word) = Some W_9644c.
Proof. vm_refl. Qed.
Lemma D_9644c : decode_any W_9644c = Some (OpImm ALU_ADD 12 12 3840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96450 : bv 32 := 0x0085d693.
Lemma F_96450 : fetch_word PSEGS (0x96450 : word) = Some W_96450.
Proof. vm_refl. Qed.
Lemma D_96450 : decode_any W_96450 = Some (ShiftImm ALU_SRL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96454 : bv 32 := 0x0185d71b.
Lemma F_96454 : fetch_word PSEGS (0x96454 : word) = Some W_96454.
Proof. vm_refl. Qed.
Lemma D_96454 : decode_any W_96454 = Some (ShiftImm32 ALU_SRL 14 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96458 : bv 32 := 0x00c6f6b3.
Lemma F_96458 : fetch_word PSEGS (0x96458 : word) = Some W_96458.
Proof. vm_refl. Qed.
Lemma D_96458 : decode_any W_96458 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9645c : bv 32 := 0x00c5f633.
Lemma F_9645c : fetch_word PSEGS (0x9645c : word) = Some W_9645c.
Proof. vm_refl. Qed.
Lemma D_9645c : decode_any W_9645c = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96460 : bv 32 := 0x01859593.
Lemma F_96460 : fetch_word PSEGS (0x96460 : word) = Some W_96460.
Proof. vm_refl. Qed.
Lemma D_96460 : decode_any W_96460 = Some (ShiftImm ALU_SLL 11 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96464 : bv 32 := 0x00861613.
Lemma F_96464 : fetch_word PSEGS (0x96464 : word) = Some W_96464.
Proof. vm_refl. Qed.
Lemma D_96464 : decode_any W_96464 = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96468 : bv 32 := 0x00e6e6b3.
Lemma F_96468 : fetch_word PSEGS (0x96468 : word) = Some W_96468.
Proof. vm_refl. Qed.
Lemma D_96468 : decode_any W_96468 = Some (Op ALU_OR 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9646c : bv 32 := 0x00c5e5b3.
Lemma F_9646c : fetch_word PSEGS (0x9646c : word) = Some W_9646c.
Proof. vm_refl. Qed.
Lemma D_9646c : decode_any W_9646c = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96470 : bv 32 := 0x00d5e5b3.
Lemma F_96470 : fetch_word PSEGS (0x96470 : word) = Some W_96470.
Proof. vm_refl. Qed.
Lemma D_96470 : decode_any W_96470 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96474 : bv 32 := 0x01458593.
Lemma F_96474 : fetch_word PSEGS (0x96474 : word) = Some W_96474.
Proof. vm_refl. Qed.
Lemma D_96474 : decode_any W_96474 = Some (OpImm ALU_ADD 11 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96478 : bv 32 := 0x02059593.
Lemma F_96478 : fetch_word PSEGS (0x96478 : word) = Some W_96478.
Proof. vm_refl. Qed.
Lemma D_96478 : decode_any W_96478 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9647c : bv 32 := 0x0205d593.
Lemma F_9647c : fetch_word PSEGS (0x9647c : word) = Some W_9647c.
Proof. vm_refl. Qed.
Lemma D_9647c : decode_any W_9647c = Some (ShiftImm ALU_SRL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96480 : bv 32 := 0x6b1030ef.
Lemma F_96480 : fetch_word PSEGS (0x96480 : word) = Some W_96480.
Proof. vm_refl. Qed.
Lemma D_96480 : decode_any W_96480 = Some (Jal 1 16048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96484 : bv 32 := 0x00000513.
Lemma F_96484 : fetch_word PSEGS (0x96484 : word) = Some W_96484.
Proof. vm_refl. Qed.
Lemma D_96484 : decode_any W_96484 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96488 : bv 32 := 0x00813083.
Lemma F_96488 : fetch_word PSEGS (0x96488 : word) = Some W_96488.
Proof. vm_refl. Qed.
Lemma D_96488 : decode_any W_96488 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9648c : bv 32 := 0x01010113.
Lemma F_9648c : fetch_word PSEGS (0x9648c : word) = Some W_9648c.
Proof. vm_refl. Qed.
Lemma D_9648c : decode_any W_9648c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96490 : bv 32 := 0x00008067.
Lemma F_96490 : fetch_word PSEGS (0x96490 : word) = Some W_96490.
Proof. vm_refl. Qed.
Lemma D_96490 : decode_any W_96490 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96498 : bv 32 := 0x04113423.
Lemma F_96498 : fetch_word PSEGS (0x96498 : word) = Some W_96498.
Proof. vm_refl. Qed.
Lemma D_96498 : decode_any W_96498 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9649c : bv 32 := 0x04813023.
Lemma F_9649c : fetch_word PSEGS (0x9649c : word) = Some W_9649c.
Proof. vm_refl. Qed.
Lemma D_9649c : decode_any W_9649c = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_964a0 : bv 32 := 0x02913c23.
Lemma F_964a0 : fetch_word PSEGS (0x964a0 : word) = Some W_964a0.
Proof. vm_refl. Qed.
Lemma D_964a0 : decode_any W_964a0 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_964a4 : bv 32 := 0x03213823.
Lemma F_964a4 : fetch_word PSEGS (0x964a4 : word) = Some W_964a4.
Proof. vm_refl. Qed.
Lemma D_964a4 : decode_any W_964a4 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_964a8 : bv 32 := 0x03313423.
Lemma F_964a8 : fetch_word PSEGS (0x964a8 : word) = Some W_964a8.
Proof. vm_refl. Qed.
Lemma D_964a8 : decode_any W_964a8 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_964ac : bv 32 := 0x03413023.
Lemma F_964ac : fetch_word PSEGS (0x964ac : word) = Some W_964ac.
Proof. vm_refl. Qed.
Lemma D_964ac : decode_any W_964ac = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_964b0 : bv 32 := 0x01513c23.
Lemma F_964b0 : fetch_word PSEGS (0x964b0 : word) = Some W_964b0.
Proof. vm_refl. Qed.
Lemma D_964b0 : decode_any W_964b0 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_964b4 : bv 32 := 0x00068413.
Lemma F_964b4 : fetch_word PSEGS (0x964b4 : word) = Some W_964b4.
Proof. vm_refl. Qed.
Lemma D_964b4 : decode_any W_964b4 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_964b8 : bv 32 := 0x0001b697.
Lemma F_964b8 : fetch_word PSEGS (0x964b8 : word) = Some W_964b8.
Proof. vm_refl. Qed.
Lemma D_964b8 : decode_any W_964b8 = Some (Auipc 13 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9655c : bv 32 := 0x00000597.
Lemma F_9655c : fetch_word PSEGS (0x9655c : word) = Some W_9655c.
Proof. vm_refl. Qed.
Lemma D_9655c : decode_any W_9655c = Some (Auipc 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96560 : bv 32 := 0x00c10513.
Lemma F_96560 : fetch_word PSEGS (0x96560 : word) = Some W_96560.
Proof. vm_refl. Qed.
Lemma D_96560 : decode_any W_96560 = Some (OpImm ALU_ADD 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96564 : bv 32 := 0x18858713.
Lemma F_96564 : fetch_word PSEGS (0x96564 : word) = Some W_96564.
Proof. vm_refl. Qed.
Lemma D_96564 : decode_any W_96564 = Some (OpImm ALU_ADD 14 11 392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965a8 : bv 32 := 0x0187569b.
Lemma F_965a8 : fetch_word PSEGS (0x965a8 : word) = Some W_965a8.
Proof. vm_refl. Qed.
Lemma D_965a8 : decode_any W_965a8 = Some (ShiftImm32 ALU_SRL 13 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965ac : bv 32 := 0x013777b3.
Lemma F_965ac : fetch_word PSEGS (0x965ac : word) = Some W_965ac.
Proof. vm_refl. Qed.
Lemma D_965ac : decode_any W_965ac = Some (Op ALU_AND 15 14 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965b0 : bv 32 := 0x01871713.
Lemma F_965b0 : fetch_word PSEGS (0x965b0 : word) = Some W_965b0.
Proof. vm_refl. Qed.
Lemma D_965b0 : decode_any W_965b0 = Some (ShiftImm ALU_SLL 14 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965b4 : bv 32 := 0x01367633.
Lemma F_965b4 : fetch_word PSEGS (0x965b4 : word) = Some W_965b4.
Proof. vm_refl. Qed.
Lemma D_965b4 : decode_any W_965b4 = Some (Op ALU_AND 12 12 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965b8 : bv 32 := 0x00d66633.
Lemma F_965b8 : fetch_word PSEGS (0x965b8 : word) = Some W_965b8.
Proof. vm_refl. Qed.
Lemma D_965b8 : decode_any W_965b8 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965bc : bv 32 := 0x00855693.
Lemma F_965bc : fetch_word PSEGS (0x965bc : word) = Some W_965bc.
Proof. vm_refl. Qed.
Lemma D_965bc : decode_any W_965bc = Some (ShiftImm ALU_SRL 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965c0 : bv 32 := 0x00879793.
Lemma F_965c0 : fetch_word PSEGS (0x965c0 : word) = Some W_965c0.
Proof. vm_refl. Qed.
Lemma D_965c0 : decode_any W_965c0 = Some (ShiftImm ALU_SLL 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965c4 : bv 32 := 0x00f76733.
Lemma F_965c4 : fetch_word PSEGS (0x965c4 : word) = Some W_965c4.
Proof. vm_refl. Qed.
Lemma D_965c4 : decode_any W_965c4 = Some (Op ALU_OR 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965c8 : bv 32 := 0x0185579b.
Lemma F_965c8 : fetch_word PSEGS (0x965c8 : word) = Some W_965c8.
Proof. vm_refl. Qed.
Lemma D_965c8 : decode_any W_965c8 = Some (ShiftImm32 ALU_SRL 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965cc : bv 32 := 0x0136f6b3.
Lemma F_965cc : fetch_word PSEGS (0x965cc : word) = Some W_965cc.
Proof. vm_refl. Qed.
Lemma D_965cc : decode_any W_965cc = Some (Op ALU_AND 13 13 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965d0 : bv 32 := 0x00f6e6b3.
Lemma F_965d0 : fetch_word PSEGS (0x965d0 : word) = Some W_965d0.
Proof. vm_refl. Qed.
Lemma D_965d0 : decode_any W_965d0 = Some (Op ALU_OR 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965d4 : bv 32 := 0x013577b3.
Lemma F_965d4 : fetch_word PSEGS (0x965d4 : word) = Some W_965d4.
Proof. vm_refl. Qed.
Lemma D_965d4 : decode_any W_965d4 = Some (Op ALU_AND 15 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_965d8 : bv 32 := 0x01851513.
Lemma F_965d8 : fetch_word PSEGS (0x965d8 : word) = Some W_965d8.
Proof. vm_refl. Qed.
Lemma D_965d8 : decode_any W_965d8 = Some (ShiftImm ALU_SLL 10 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96648 : bv 32 := 0x00c5e5b3.
Lemma F_96648 : fetch_word PSEGS (0x96648 : word) = Some W_96648.
Proof. vm_refl. Qed.
Lemma D_96648 : decode_any W_96648 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9664c : bv 32 := 0x00010637.
Lemma F_9664c : fetch_word PSEGS (0x9664c : word) = Some W_9664c.
Proof. vm_refl. Qed.
Lemma D_9664c : decode_any W_9664c = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96650 : bv 32 := 0x00869693.
Lemma F_96650 : fetch_word PSEGS (0x96650 : word) = Some W_96650.
Proof. vm_refl. Qed.
Lemma D_96650 : decode_any W_96650 = Some (ShiftImm ALU_SLL 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96654 : bv 32 := 0xf0060613.
Lemma F_96654 : fetch_word PSEGS (0x96654 : word) = Some W_96654.
Proof. vm_refl. Qed.
Lemma D_96654 : decode_any W_96654 = Some (OpImm ALU_ADD 12 12 3840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96658 : bv 32 := 0x00da66b3.
Lemma F_96658 : fetch_word PSEGS (0x96658 : word) = Some W_96658.
Proof. vm_refl. Qed.
Lemma D_96658 : decode_any W_96658 = Some (Op ALU_OR 13 20 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9665c : bv 32 := 0x00b6e5b3.
Lemma F_9665c : fetch_word PSEGS (0x9665c : word) = Some W_9665c.
Proof. vm_refl. Qed.
Lemma D_9665c : decode_any W_9665c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96660 : bv 32 := 0x02059593.
Lemma F_96660 : fetch_word PSEGS (0x96660 : word) = Some W_96660.
Proof. vm_refl. Qed.
Lemma D_96660 : decode_any W_96660 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96664 : bv 32 := 0x00855693.
Lemma F_96664 : fetch_word PSEGS (0x96664 : word) = Some W_96664.
Proof. vm_refl. Qed.
Lemma D_96664 : decode_any W_96664 = Some (ShiftImm ALU_SRL 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96668 : bv 32 := 0x0185571b.
Lemma F_96668 : fetch_word PSEGS (0x96668 : word) = Some W_96668.
Proof. vm_refl. Qed.
Lemma D_96668 : decode_any W_96668 = Some (ShiftImm32 ALU_SRL 14 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9666c : bv 32 := 0x00c6f6b3.
Lemma F_9666c : fetch_word PSEGS (0x9666c : word) = Some W_9666c.
Proof. vm_refl. Qed.
Lemma D_9666c : decode_any W_9666c = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96670 : bv 32 := 0x00c57633.
Lemma F_96670 : fetch_word PSEGS (0x96670 : word) = Some W_96670.
Proof. vm_refl. Qed.
Lemma D_96670 : decode_any W_96670 = Some (Op ALU_AND 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9673c : bv 32 := 0x00b53633.
Lemma F_9673c : fetch_word PSEGS (0x9673c : word) = Some W_9673c.
Proof. vm_refl. Qed.
Lemma D_9673c : decode_any W_9673c = Some (Op ALU_SLTU 12 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96740 : bv 32 := 0x00a5b533.
Lemma F_96740 : fetch_word PSEGS (0x96740 : word) = Some W_96740.
Proof. vm_refl. Qed.
Lemma D_96740 : decode_any W_96740 = Some (Op ALU_SLTU 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96744 : bv 32 := 0x40c50533.
Lemma F_96744 : fetch_word PSEGS (0x96744 : word) = Some W_96744.
Proof. vm_refl. Qed.
Lemma D_96744 : decode_any W_96744 = Some (Op ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96748 : bv 32 := 0x00008067.
Lemma F_96748 : fetch_word PSEGS (0x96748 : word) = Some W_96748.
Proof. vm_refl. Qed.
Lemma D_96748 : decode_any W_96748 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9674c : bv 32 := 0x81010113.
Lemma F_9674c : fetch_word PSEGS (0x9674c : word) = Some W_9674c.
Proof. vm_refl. Qed.
Lemma D_9674c : decode_any W_9674c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96750 : bv 32 := 0x7e113423.
Lemma F_96750 : fetch_word PSEGS (0x96750 : word) = Some W_96750.
Proof. vm_refl. Qed.
Lemma D_96750 : decode_any W_96750 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96754 : bv 32 := 0x7e813023.
Lemma F_96754 : fetch_word PSEGS (0x96754 : word) = Some W_96754.
Proof. vm_refl. Qed.
Lemma D_96754 : decode_any W_96754 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96758 : bv 32 := 0x7c913c23.
Lemma F_96758 : fetch_word PSEGS (0x96758 : word) = Some W_96758.
Proof. vm_refl. Qed.
Lemma D_96758 : decode_any W_96758 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9675c : bv 32 := 0x7d213823.
Lemma F_9675c : fetch_word PSEGS (0x9675c : word) = Some W_9675c.
Proof. vm_refl. Qed.
Lemma D_9675c : decode_any W_9675c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96760 : bv 32 := 0x7d313423.
Lemma F_96760 : fetch_word PSEGS (0x96760 : word) = Some W_96760.
Proof. vm_refl. Qed.
Lemma D_96760 : decode_any W_96760 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96764 : bv 32 := 0x7d413023.
Lemma F_96764 : fetch_word PSEGS (0x96764 : word) = Some W_96764.
Proof. vm_refl. Qed.
Lemma D_96764 : decode_any W_96764 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96768 : bv 32 := 0x7b513c23.
Lemma F_96768 : fetch_word PSEGS (0x96768 : word) = Some W_96768.
Proof. vm_refl. Qed.
Lemma D_96768 : decode_any W_96768 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9676c : bv 32 := 0x7b613823.
Lemma F_9676c : fetch_word PSEGS (0x9676c : word) = Some W_9676c.
Proof. vm_refl. Qed.
Lemma D_9676c : decode_any W_9676c = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96770 : bv 32 := 0x7b713423.
Lemma F_96770 : fetch_word PSEGS (0x96770 : word) = Some W_96770.
Proof. vm_refl. Qed.
Lemma D_96770 : decode_any W_96770 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96774 : bv 32 := 0x7b813023.
Lemma F_96774 : fetch_word PSEGS (0x96774 : word) = Some W_96774.
Proof. vm_refl. Qed.
Lemma D_96774 : decode_any W_96774 = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96778 : bv 32 := 0x79913c23.
Lemma F_96778 : fetch_word PSEGS (0x96778 : word) = Some W_96778.
Proof. vm_refl. Qed.
Lemma D_96778 : decode_any W_96778 = Some (Store SZ8 2 25 1944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9677c : bv 32 := 0x79a13823.
Lemma F_9677c : fetch_word PSEGS (0x9677c : word) = Some W_9677c.
Proof. vm_refl. Qed.
Lemma D_9677c : decode_any W_9677c = Some (Store SZ8 2 26 1936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96780 : bv 32 := 0x79b13423.
Lemma F_96780 : fetch_word PSEGS (0x96780 : word) = Some W_96780.
Proof. vm_refl. Qed.
Lemma D_96780 : decode_any W_96780 = Some (Store SZ8 2 27 1928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96784 : bv 32 := 0x80010113.
Lemma F_96784 : fetch_word PSEGS (0x96784 : word) = Some W_96784.
Proof. vm_refl. Qed.
Lemma D_96784 : decode_any W_96784 = Some (OpImm ALU_ADD 2 2 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96788 : bv 32 := 0xf4010113.
Lemma F_96788 : fetch_word PSEGS (0x96788 : word) = Some W_96788.
Proof. vm_refl. Qed.
Lemma D_96788 : decode_any W_96788 = Some (OpImm ALU_ADD 2 2 3904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9678c : bv 32 := 0x00058493.
Lemma F_9678c : fetch_word PSEGS (0x9678c : word) = Some W_9678c.
Proof. vm_refl. Qed.
Lemma D_9678c : decode_any W_9678c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96790 : bv 32 := 0x00050413.
Lemma F_96790 : fetch_word PSEGS (0x96790 : word) = Some W_96790.
Proof. vm_refl. Qed.
Lemma D_96790 : decode_any W_96790 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96794 : bv 32 := 0x0001b517.
Lemma F_96794 : fetch_word PSEGS (0x96794 : word) = Some W_96794.
Proof. vm_refl. Qed.
Lemma D_96794 : decode_any W_96794 = Some (Auipc 10 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96798 : bv 32 := 0x41c53903.
Lemma F_96798 : fetch_word PSEGS (0x96798 : word) = Some W_96798.
Proof. vm_refl. Qed.
Lemma D_96798 : decode_any W_96798 = Some (Load SZ8 true 18 10 1052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9679c : bv 32 := 0x00093503.
Lemma F_9679c : fetch_word PSEGS (0x9679c : word) = Some W_9679c.
Proof. vm_refl. Qed.
Lemma D_9679c : decode_any W_9679c = Some (Load SZ8 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967a0 : bv 32 := 0x000015b7.
Lemma F_967a0 : fetch_word PSEGS (0x967a0 : word) = Some W_967a0.
Proof. vm_refl. Qed.
Lemma D_967a0 : decode_any W_967a0 = Some (Lui 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967a4 : bv 32 := 0x00b105b3.
Lemma F_967a4 : fetch_word PSEGS (0x967a4 : word) = Some W_967a4.
Proof. vm_refl. Qed.
Lemma D_967a4 : decode_any W_967a4 = Some (Op ALU_ADD 11 2 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967a8 : bv 32 := 0x04a5b023.
Lemma F_967a8 : fetch_word PSEGS (0x967a8 : word) = Some W_967a8.
Proof. vm_refl. Qed.
Lemma D_967a8 : decode_any W_967a8 = Some (Store SZ8 11 10 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967ac : bv 32 := 0x02f00593.
Lemma F_967ac : fetch_word PSEGS (0x967ac : word) = Some W_967ac.
Proof. vm_refl. Qed.
Lemma D_967ac : decode_any W_967ac = Some (OpImm ALU_ADD 11 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967b0 : bv 32 := 0x00040513.
Lemma F_967b0 : fetch_word PSEGS (0x967b0 : word) = Some W_967b0.
Proof. vm_refl. Qed.
Lemma D_967b0 : decode_any W_967b0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967b4 : bv 32 := 0x5ec100ef.
Lemma F_967b4 : fetch_word PSEGS (0x967b4 : word) = Some W_967b4.
Proof. vm_refl. Qed.
Lemma D_967b4 : decode_any W_967b4 = Some (Jal 1 67052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967b8 : bv 32 := 0x08050063.
Lemma F_967b8 : fetch_word PSEGS (0x967b8 : word) = Some W_967b8.
Proof. vm_refl. Qed.
Lemma D_967b8 : decode_any W_967b8 = Some (Branch BC_EQ 10 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967bc : bv 32 := 0x04010593.
Lemma F_967bc : fetch_word PSEGS (0x967bc : word) = Some W_967bc.
Proof. vm_refl. Qed.
Lemma D_967bc : decode_any W_967bc = Some (OpImm ALU_ADD 11 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967c0 : bv 32 := 0x00040513.
Lemma F_967c0 : fetch_word PSEGS (0x967c0 : word) = Some W_967c0.
Proof. vm_refl. Qed.
Lemma D_967c0 : decode_any W_967c0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967c4 : bv 32 := 0x688120ef.
Lemma F_967c4 : fetch_word PSEGS (0x967c4 : word) = Some W_967c4.
Proof. vm_refl. Qed.
Lemma D_967c4 : decode_any W_967c4 = Some (Jal 1 75400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967e8 : bv 32 := 0xf0068693.
Lemma F_967e8 : fetch_word PSEGS (0x967e8 : word) = Some W_967e8.
Proof. vm_refl. Qed.
Lemma D_967e8 : decode_any W_967e8 = Some (OpImm ALU_ADD 13 13 3840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967ec : bv 32 := 0x00865713.
Lemma F_967ec : fetch_word PSEGS (0x967ec : word) = Some W_967ec.
Proof. vm_refl. Qed.
Lemma D_967ec : decode_any W_967ec = Some (ShiftImm ALU_SRL 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967f0 : bv 32 := 0x0186579b.
Lemma F_967f0 : fetch_word PSEGS (0x967f0 : word) = Some W_967f0.
Proof. vm_refl. Qed.
Lemma D_967f0 : decode_any W_967f0 = Some (ShiftImm32 ALU_SRL 15 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967f4 : bv 32 := 0x00d77733.
Lemma F_967f4 : fetch_word PSEGS (0x967f4 : word) = Some W_967f4.
Proof. vm_refl. Qed.
Lemma D_967f4 : decode_any W_967f4 = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967f8 : bv 32 := 0x00d676b3.
Lemma F_967f8 : fetch_word PSEGS (0x967f8 : word) = Some W_967f8.
Proof. vm_refl. Qed.
Lemma D_967f8 : decode_any W_967f8 = Some (Op ALU_AND 13 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_967fc : bv 32 := 0x01861613.
Lemma F_967fc : fetch_word PSEGS (0x967fc : word) = Some W_967fc.
Proof. vm_refl. Qed.
Lemma D_967fc : decode_any W_967fc = Some (ShiftImm ALU_SLL 12 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968e4 : bv 32 := 0x3aa50493.
Lemma F_968e4 : fetch_word PSEGS (0x968e4 : word) = Some W_968e4.
Proof. vm_refl. Qed.
Lemma D_968e4 : decode_any W_968e4 = Some (OpImm ALU_ADD 9 10 938, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968e8 : bv 32 := 0x000ac503.
Lemma F_968e8 : fetch_word PSEGS (0x968e8 : word) = Some W_968e8.
Proof. vm_refl. Qed.
Lemma D_968e8 : decode_any W_968e8 = Some (Load SZ1 false 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968ec : bv 32 := 0xf4050ee3.
Lemma F_968ec : fetch_word PSEGS (0x968ec : word) = Some W_968ec.
Proof. vm_refl. Qed.
Lemma D_968ec : decode_any W_968ec = Some (Branch BC_EQ 10 0 8028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968f0 : bv 32 := 0x02500c13.
Lemma F_968f0 : fetch_word PSEGS (0x968f0 : word) = Some W_968f0.
Proof. vm_refl. Qed.
Lemma D_968f0 : decode_any W_968f0 = Some (OpImm ALU_ADD 24 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968f4 : bv 32 := 0xfff7c517.
Lemma F_968f4 : fetch_word PSEGS (0x968f4 : word) = Some W_968f4.
Proof. vm_refl. Qed.
Lemma D_968f4 : decode_any W_968f4 = Some (Auipc 10 1048444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968f8 : bv 32 := 0x02800c93.
Lemma F_968f8 : fetch_word PSEGS (0x968f8 : word) = Some W_968f8.
Proof. vm_refl. Qed.
Lemma D_968f8 : decode_any W_968f8 = Some (OpImm ALU_ADD 25 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_968fc : bv 32 := 0xfff7a597.
Lemma F_968fc : fetch_word PSEGS (0x968fc : word) = Some W_968fc.
Proof. vm_refl. Qed.
Lemma D_968fc : decode_any W_968fc = Some (Auipc 11 1048442, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96900 : bv 32 := 0xfff84617.
Lemma F_96900 : fetch_word PSEGS (0x96900 : word) = Some W_96900.
Proof. vm_refl. Qed.
Lemma D_96900 : decode_any W_96900 = Some (Auipc 12 1048452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96904 : bv 32 := 0xfff7c697.
Lemma F_96904 : fetch_word PSEGS (0x96904 : word) = Some W_96904.
Proof. vm_refl. Qed.
Lemma D_96904 : decode_any W_96904 = Some (Auipc 13 1048444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96920 : bv 32 := 0xec258513.
Lemma F_96920 : fetch_word PSEGS (0x96920 : word) = Some W_96920.
Proof. vm_refl. Qed.
Lemma D_96920 : decode_any W_96920 = Some (OpImm ALU_ADD 10 11 3778, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96924 : bv 32 := 0x02a13023.
Lemma F_96924 : fetch_word PSEGS (0x96924 : word) = Some W_96924.
Proof. vm_refl. Qed.
Lemma D_96924 : decode_any W_96924 = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96928 : bv 32 := 0x00460993.
Lemma F_96928 : fetch_word PSEGS (0x96928 : word) = Some W_96928.
Proof. vm_refl. Qed.
Lemma D_96928 : decode_any W_96928 = Some (OpImm ALU_ADD 19 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9692c : bv 32 := 0x4c768513.
Lemma F_9692c : fetch_word PSEGS (0x9692c : word) = Some W_9692c.
Proof. vm_refl. Qed.
Lemma D_9692c : decode_any W_9692c = Some (OpImm ALU_ADD 10 13 1223, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96930 : bv 32 := 0x02a13823.
Lemma F_96930 : fetch_word PSEGS (0x96930 : word) = Some W_96930.
Proof. vm_refl. Qed.
Lemma D_96930 : decode_any W_96930 = Some (Store SZ8 2 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96934 : bv 32 := 0x81a70513.
Lemma F_96934 : fetch_word PSEGS (0x96934 : word) = Some W_96934.
Proof. vm_refl. Qed.
Lemma D_96934 : decode_any W_96934 = Some (OpImm ALU_ADD 10 14 2074, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96938 : bv 32 := 0x02a13423.
Lemma F_96938 : fetch_word PSEGS (0x96938 : word) = Some W_96938.
Proof. vm_refl. Qed.
Lemma D_96938 : decode_any W_96938 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9693c : bv 32 := 0x8ff7851b.
Lemma F_9693c : fetch_word PSEGS (0x9693c : word) = Some W_9693c.
Proof. vm_refl. Qed.
Lemma D_9693c : decode_any W_9693c = Some (OpImm32 10 15 2303, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96940 : bv 32 := 0x00a13823.
Lemma F_96940 : fetch_word PSEGS (0x96940 : word) = Some W_96940.
Proof. vm_refl. Qed.
Lemma D_96940 : decode_any W_96940 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9694c : bv 32 := 0x0200006f.
Lemma F_9694c : fetch_word PSEGS (0x9694c : word) = Some W_9694c.
Proof. vm_refl. Qed.
Lemma D_9694c : decode_any W_9694c = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96950 : bv 32 := 0x1e1030ef.
Lemma F_96950 : fetch_word PSEGS (0x96950 : word) = Some W_96950.
Proof. vm_refl. Qed.
Lemma D_96950 : decode_any W_96950 = Some (Jal 1 14816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96954 : bv 32 := 0xba8ff0ef.
Lemma F_96954 : fetch_word PSEGS (0x96954 : word) = Some W_96954.
Proof. vm_refl. Qed.
Lemma D_96954 : decode_any W_96954 = Some (Jal 1 2093992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_96980 : bv 32 := 0x0eaaf063.
Lemma F_96980 : fetch_word PSEGS (0x96980 : word) = Some W_96980.
Proof. vm_refl. Qed.
Lemma D_96980 : decode_any W_96980 = Some (Branch BC_GEU 21 10 224, 4%Z).
Proof. vm_refl. Qed.

