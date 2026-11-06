(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_af190 : bv 32 := 0xf9010113.
Lemma F_af190 : fetch_word Plain.M.loaded_segments (0xaf1cc : word) = Some W_af190.
Proof. vm_refl. Qed.
Lemma D_af190 : decode_any W_af190 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af194 : bv 32 := 0x06113423.
Lemma F_af194 : fetch_word Plain.M.loaded_segments (0xaf1d0 : word) = Some W_af194.
Proof. vm_refl. Qed.
Lemma D_af194 : decode_any W_af194 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af198 : bv 32 := 0x06813023.
Lemma F_af198 : fetch_word Plain.M.loaded_segments (0xaf1d4 : word) = Some W_af198.
Proof. vm_refl. Qed.
Lemma D_af198 : decode_any W_af198 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af19c : bv 32 := 0x04913c23.
Lemma F_af19c : fetch_word Plain.M.loaded_segments (0xaf1d8 : word) = Some W_af19c.
Proof. vm_refl. Qed.
Lemma D_af19c : decode_any W_af19c = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1a0 : bv 32 := 0x05213823.
Lemma F_af1a0 : fetch_word Plain.M.loaded_segments (0xaf1dc : word) = Some W_af1a0.
Proof. vm_refl. Qed.
Lemma D_af1a0 : decode_any W_af1a0 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1a4 : bv 32 := 0x05313423.
Lemma F_af1a4 : fetch_word Plain.M.loaded_segments (0xaf1e0 : word) = Some W_af1a4.
Proof. vm_refl. Qed.
Lemma D_af1a4 : decode_any W_af1a4 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1a8 : bv 32 := 0x05413023.
Lemma F_af1a8 : fetch_word Plain.M.loaded_segments (0xaf1e4 : word) = Some W_af1a8.
Proof. vm_refl. Qed.
Lemma D_af1a8 : decode_any W_af1a8 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1ac : bv 32 := 0x03513c23.
Lemma F_af1ac : fetch_word Plain.M.loaded_segments (0xaf1e8 : word) = Some W_af1ac.
Proof. vm_refl. Qed.
Lemma D_af1ac : decode_any W_af1ac = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1b0 : bv 32 := 0x03613823.
Lemma F_af1b0 : fetch_word Plain.M.loaded_segments (0xaf1ec : word) = Some W_af1b0.
Proof. vm_refl. Qed.
Lemma D_af1b0 : decode_any W_af1b0 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1b4 : bv 32 := 0x00060413.
Lemma F_af1b4 : fetch_word Plain.M.loaded_segments (0xaf1f0 : word) = Some W_af1b4.
Proof. vm_refl. Qed.
Lemma D_af1b4 : decode_any W_af1b4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1b8 : bv 32 := 0x00050493.
Lemma F_af1b8 : fetch_word Plain.M.loaded_segments (0xaf1f4 : word) = Some W_af1b8.
Proof. vm_refl. Qed.
Lemma D_af1b8 : decode_any W_af1b8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1bc : bv 32 := 0x00017517.
Lemma F_af1bc : fetch_word Plain.M.loaded_segments (0xaf1f8 : word) = Some W_af1bc.
Proof. vm_refl. Qed.
Lemma D_af1bc : decode_any W_af1bc = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1c0 : bv 32 := 0x63853a83.
Lemma F_af1c0 : fetch_word Plain.M.loaded_segments (0xaf1fc : word) = Some W_af1c0.
Proof. vm_refl. Qed.
Lemma D_af1c0 : decode_any W_af1c0 = Some (Load SZ8 true 21 10 1592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1c4 : bv 32 := 0x000ab503.
Lemma F_af1c4 : fetch_word Plain.M.loaded_segments (0xaf200 : word) = Some W_af1c4.
Proof. vm_refl. Qed.
Lemma D_af1c4 : decode_any W_af1c4 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1c8 : bv 32 := 0x02a13423.
Lemma F_af1c8 : fetch_word Plain.M.loaded_segments (0xaf204 : word) = Some W_af1c8.
Proof. vm_refl. Qed.
Lemma D_af1c8 : decode_any W_af1c8 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1cc : bv 32 := 0x0284b503.
Lemma F_af1cc : fetch_word Plain.M.loaded_segments (0xaf208 : word) = Some W_af1cc.
Proof. vm_refl. Qed.
Lemma D_af1cc : decode_any W_af1cc = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1d0 : bv 32 := 0x0384b603.
Lemma F_af1d0 : fetch_word Plain.M.loaded_segments (0xaf20c : word) = Some W_af1d0.
Proof. vm_refl. Qed.
Lemma D_af1d0 : decode_any W_af1d0 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1d4 : bv 32 := 0x40c50b33.
Lemma F_af1d4 : fetch_word Plain.M.loaded_segments (0xaf210 : word) = Some W_af1d4.
Proof. vm_refl. Qed.
Lemma D_af1d4 : decode_any W_af1d4 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1d8 : bv 32 := 0x00c546b3.
Lemma F_af1d8 : fetch_word Plain.M.loaded_segments (0xaf214 : word) = Some W_af1d8.
Proof. vm_refl. Qed.
Lemma D_af1d8 : decode_any W_af1d8 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1dc : bv 32 := 0x00c13423.
Lemma F_af1dc : fetch_word Plain.M.loaded_segments (0xaf218 : word) = Some W_af1dc.
Proof. vm_refl. Qed.
Lemma D_af1dc : decode_any W_af1dc = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1e0 : bv 32 := 0x01613823.
Lemma F_af1e0 : fetch_word Plain.M.loaded_segments (0xaf21c : word) = Some W_af1e0.
Proof. vm_refl. Qed.
Lemma D_af1e0 : decode_any W_af1e0 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1e4 : bv 32 := 0x00b13c23.
Lemma F_af1e4 : fetch_word Plain.M.loaded_segments (0xaf220 : word) = Some W_af1e4.
Proof. vm_refl. Qed.
Lemma D_af1e4 : decode_any W_af1e4 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1e8 : bv 32 := 0x02813023.
Lemma F_af1e8 : fetch_word Plain.M.loaded_segments (0xaf224 : word) = Some W_af1e8.
Proof. vm_refl. Qed.
Lemma D_af1e8 : decode_any W_af1e8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1ec : bv 32 := 0x008b0b33.
Lemma F_af1ec : fetch_word Plain.M.loaded_segments (0xaf228 : word) = Some W_af1ec.
Proof. vm_refl. Qed.
Lemma D_af1ec : decode_any W_af1ec = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1f0 : bv 32 := 0x00d03933.
Lemma F_af1f0 : fetch_word Plain.M.loaded_segments (0xaf22c : word) = Some W_af1f0.
Proof. vm_refl. Qed.
Lemma D_af1f0 : decode_any W_af1f0 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1f4 : bv 32 := 0x00c50663.
Lemma F_af1f4 : fetch_word Plain.M.loaded_segments (0xaf230 : word) = Some W_af1f4.
Proof. vm_refl. Qed.
Lemma D_af1f4 : decode_any W_af1f4 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1f8 : bv 32 := 0x00810993.
Lemma F_af1f8 : fetch_word Plain.M.loaded_segments (0xaf234 : word) = Some W_af1f8.
Proof. vm_refl. Qed.
Lemma D_af1f8 : decode_any W_af1f8 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af1fc : bv 32 := 0x0080006f.
Lemma F_af1fc : fetch_word Plain.M.loaded_segments (0xaf238 : word) = Some W_af1fc.
Proof. vm_refl. Qed.
Lemma D_af1fc : decode_any W_af1fc = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af200 : bv 32 := 0x01810993.
Lemma F_af200 : fetch_word Plain.M.loaded_segments (0xaf23c : word) = Some W_af200.
Proof. vm_refl. Qed.
Lemma D_af200 : decode_any W_af200 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af204 : bv 32 := 0x0784a503.
Lemma F_af204 : fetch_word Plain.M.loaded_segments (0xaf240 : word) = Some W_af204.
Proof. vm_refl. Qed.
Lemma D_af204 : decode_any W_af204 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af208 : bv 32 := 0x00190913.
Lemma F_af208 : fetch_word Plain.M.loaded_segments (0xaf244 : word) = Some W_af208.
Proof. vm_refl. Qed.
Lemma D_af208 : decode_any W_af208 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af20c : bv 32 := 0x04200893.
Lemma F_af20c : fetch_word Plain.M.loaded_segments (0xaf248 : word) = Some W_af20c.
Proof. vm_refl. Qed.
Lemma D_af20c : decode_any W_af20c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af210 : bv 32 := 0x00098593.
Lemma F_af210 : fetch_word Plain.M.loaded_segments (0xaf24c : word) = Some W_af210.
Proof. vm_refl. Qed.
Lemma D_af210 : decode_any W_af210 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af214 : bv 32 := 0x00090613.
Lemma F_af214 : fetch_word Plain.M.loaded_segments (0xaf250 : word) = Some W_af214.
Proof. vm_refl. Qed.
Lemma D_af214 : decode_any W_af214 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af218 : bv 32 := 0x00000073.
Lemma F_af218 : fetch_word Plain.M.loaded_segments (0xaf254 : word) = Some W_af218.
Proof. vm_refl. Qed.
Lemma D_af218 : decode_any W_af218 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_af218 : is_ecall W_af218 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_af21c : bv 32 := 0xf31fa0ef.
Lemma F_af21c : fetch_word Plain.M.loaded_segments (0xaf258 : word) = Some W_af21c.
Proof. vm_refl. Qed.
Lemma D_af21c : decode_any W_af21c = Some (Jal 1 2076464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af220 : bv 32 := 0x09651863.
Lemma F_af220 : fetch_word Plain.M.loaded_segments (0xaf25c : word) = Some W_af220.
Proof. vm_refl. Qed.
Lemma D_af220 : decode_any W_af220 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af224 : bv 32 := 0x0584b503.
Lemma F_af224 : fetch_word Plain.M.loaded_segments (0xaf260 : word) = Some W_af224.
Proof. vm_refl. Qed.
Lemma D_af224 : decode_any W_af224 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af228 : bv 32 := 0x0604b583.
Lemma F_af228 : fetch_word Plain.M.loaded_segments (0xaf264 : word) = Some W_af228.
Proof. vm_refl. Qed.
Lemma D_af228 : decode_any W_af228 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af22c : bv 32 := 0x00b505b3.
Lemma F_af22c : fetch_word Plain.M.loaded_segments (0xaf268 : word) = Some W_af22c.
Proof. vm_refl. Qed.
Lemma D_af22c : decode_any W_af22c = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af230 : bv 32 := 0x02b4b023.
Lemma F_af230 : fetch_word Plain.M.loaded_segments (0xaf26c : word) = Some W_af230.
Proof. vm_refl. Qed.
Lemma D_af230 : decode_any W_af230 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af234 : bv 32 := 0x02a4b423.
Lemma F_af234 : fetch_word Plain.M.loaded_segments (0xaf270 : word) = Some W_af234.
Proof. vm_refl. Qed.
Lemma D_af234 : decode_any W_af234 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af238 : bv 32 := 0x02a4bc23.
Lemma F_af238 : fetch_word Plain.M.loaded_segments (0xaf274 : word) = Some W_af238.
Proof. vm_refl. Qed.
Lemma D_af238 : decode_any W_af238 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af23c : bv 32 := 0x00040513.
Lemma F_af23c : fetch_word Plain.M.loaded_segments (0xaf278 : word) = Some W_af23c.
Proof. vm_refl. Qed.
Lemma D_af23c : decode_any W_af23c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af240 : bv 32 := 0x000ab583.
Lemma F_af240 : fetch_word Plain.M.loaded_segments (0xaf27c : word) = Some W_af240.
Proof. vm_refl. Qed.
Lemma D_af240 : decode_any W_af240 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af244 : bv 32 := 0x02813603.
Lemma F_af244 : fetch_word Plain.M.loaded_segments (0xaf280 : word) = Some W_af244.
Proof. vm_refl. Qed.
Lemma D_af244 : decode_any W_af244 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af248 : bv 32 := 0x0cc59a63.
Lemma F_af248 : fetch_word Plain.M.loaded_segments (0xaf284 : word) = Some W_af248.
Proof. vm_refl. Qed.
Lemma D_af248 : decode_any W_af248 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af24c : bv 32 := 0x06813083.
Lemma F_af24c : fetch_word Plain.M.loaded_segments (0xaf288 : word) = Some W_af24c.
Proof. vm_refl. Qed.
Lemma D_af24c : decode_any W_af24c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af250 : bv 32 := 0x06013403.
Lemma F_af250 : fetch_word Plain.M.loaded_segments (0xaf28c : word) = Some W_af250.
Proof. vm_refl. Qed.
Lemma D_af250 : decode_any W_af250 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af254 : bv 32 := 0x05813483.
Lemma F_af254 : fetch_word Plain.M.loaded_segments (0xaf290 : word) = Some W_af254.
Proof. vm_refl. Qed.
Lemma D_af254 : decode_any W_af254 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af258 : bv 32 := 0x05013903.
Lemma F_af258 : fetch_word Plain.M.loaded_segments (0xaf294 : word) = Some W_af258.
Proof. vm_refl. Qed.
Lemma D_af258 : decode_any W_af258 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af25c : bv 32 := 0x04813983.
Lemma F_af25c : fetch_word Plain.M.loaded_segments (0xaf298 : word) = Some W_af25c.
Proof. vm_refl. Qed.
Lemma D_af25c : decode_any W_af25c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af260 : bv 32 := 0x04013a03.
Lemma F_af260 : fetch_word Plain.M.loaded_segments (0xaf29c : word) = Some W_af260.
Proof. vm_refl. Qed.
Lemma D_af260 : decode_any W_af260 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af264 : bv 32 := 0x03813a83.
Lemma F_af264 : fetch_word Plain.M.loaded_segments (0xaf2a0 : word) = Some W_af264.
Proof. vm_refl. Qed.
Lemma D_af264 : decode_any W_af264 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af268 : bv 32 := 0x03013b03.
Lemma F_af268 : fetch_word Plain.M.loaded_segments (0xaf2a4 : word) = Some W_af268.
Proof. vm_refl. Qed.
Lemma D_af268 : decode_any W_af268 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af26c : bv 32 := 0x07010113.
Lemma F_af26c : fetch_word Plain.M.loaded_segments (0xaf2a8 : word) = Some W_af26c.
Proof. vm_refl. Qed.
Lemma D_af26c : decode_any W_af26c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af270 : bv 32 := 0x00008067.
Lemma F_af270 : fetch_word Plain.M.loaded_segments (0xaf2ac : word) = Some W_af270.
Proof. vm_refl. Qed.
Lemma D_af270 : decode_any W_af270 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af274 : bv 32 := 0x00800713.
Lemma F_af274 : fetch_word Plain.M.loaded_segments (0xaf2b0 : word) = Some W_af274.
Proof. vm_refl. Qed.
Lemma D_af274 : decode_any W_af274 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af278 : bv 32 := 0x000a0593.
Lemma F_af278 : fetch_word Plain.M.loaded_segments (0xaf2b4 : word) = Some W_af278.
Proof. vm_refl. Qed.
Lemma D_af278 : decode_any W_af278 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af27c : bv 32 := 0x00e98733.
Lemma F_af27c : fetch_word Plain.M.loaded_segments (0xaf2b8 : word) = Some W_af27c.
Proof. vm_refl. Qed.
Lemma D_af27c : decode_any W_af27c = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af280 : bv 32 := 0x00073783.
Lemma F_af280 : fetch_word Plain.M.loaded_segments (0xaf2bc : word) = Some W_af280.
Proof. vm_refl. Qed.
Lemma D_af280 : decode_any W_af280 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af284 : bv 32 := 0x40ab0b33.
Lemma F_af284 : fetch_word Plain.M.loaded_segments (0xaf2c0 : word) = Some W_af284.
Proof. vm_refl. Qed.
Lemma D_af284 : decode_any W_af284 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af288 : bv 32 := 0x0784a503.
Lemma F_af288 : fetch_word Plain.M.loaded_segments (0xaf2c4 : word) = Some W_af288.
Proof. vm_refl. Qed.
Lemma D_af288 : decode_any W_af288 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af28c : bv 32 := 0x40c9093b.
Lemma F_af28c : fetch_word Plain.M.loaded_segments (0xaf2c8 : word) = Some W_af28c.
Proof. vm_refl. Qed.
Lemma D_af28c : decode_any W_af28c = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af290 : bv 32 := 0x40d787b3.
Lemma F_af290 : fetch_word Plain.M.loaded_segments (0xaf2cc : word) = Some W_af290.
Proof. vm_refl. Qed.
Lemma D_af290 : decode_any W_af290 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af294 : bv 32 := 0x00f73023.
Lemma F_af294 : fetch_word Plain.M.loaded_segments (0xaf2d0 : word) = Some W_af294.
Proof. vm_refl. Qed.
Lemma D_af294 : decode_any W_af294 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af298 : bv 32 := 0x04200893.
Lemma F_af298 : fetch_word Plain.M.loaded_segments (0xaf2d4 : word) = Some W_af298.
Proof. vm_refl. Qed.
Lemma D_af298 : decode_any W_af298 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af29c : bv 32 := 0x00090613.
Lemma F_af29c : fetch_word Plain.M.loaded_segments (0xaf2d8 : word) = Some W_af29c.
Proof. vm_refl. Qed.
Lemma D_af29c : decode_any W_af29c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2a0 : bv 32 := 0x00000073.
Lemma F_af2a0 : fetch_word Plain.M.loaded_segments (0xaf2dc : word) = Some W_af2a0.
Proof. vm_refl. Qed.
Lemma D_af2a0 : decode_any W_af2a0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_af2a0 : is_ecall W_af2a0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_af2a4 : bv 32 := 0xea9fa0ef.
Lemma F_af2a4 : fetch_word Plain.M.loaded_segments (0xaf2e0 : word) = Some W_af2a4.
Proof. vm_refl. Qed.
Lemma D_af2a4 : decode_any W_af2a4 = Some (Jal 1 2076328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2a8 : bv 32 := 0x000a0993.
Lemma F_af2a8 : fetch_word Plain.M.loaded_segments (0xaf2e4 : word) = Some W_af2a8.
Proof. vm_refl. Qed.
Lemma D_af2a8 : decode_any W_af2a8 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2ac : bv 32 := 0xf7650ce3.
Lemma F_af2ac : fetch_word Plain.M.loaded_segments (0xaf2e8 : word) = Some W_af2ac.
Proof. vm_refl. Qed.
Lemma D_af2ac : decode_any W_af2ac = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2b0 : bv 32 := 0x02054c63.
Lemma F_af2b0 : fetch_word Plain.M.loaded_segments (0xaf2ec : word) = Some W_af2b0.
Proof. vm_refl. Qed.
Lemma D_af2b0 : decode_any W_af2b0 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2b4 : bv 32 := 0x0089b583.
Lemma F_af2b4 : fetch_word Plain.M.loaded_segments (0xaf2f0 : word) = Some W_af2b4.
Proof. vm_refl. Qed.
Lemma D_af2b4 : decode_any W_af2b4 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2b8 : bv 32 := 0x00a5b633.
Lemma F_af2b8 : fetch_word Plain.M.loaded_segments (0xaf2f4 : word) = Some W_af2b8.
Proof. vm_refl. Qed.
Lemma D_af2b8 : decode_any W_af2b8 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2bc : bv 32 := 0x00461a13.
Lemma F_af2bc : fetch_word Plain.M.loaded_segments (0xaf2f8 : word) = Some W_af2bc.
Proof. vm_refl. Qed.
Lemma D_af2bc : decode_any W_af2bc = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2c0 : bv 32 := 0x01498a33.
Lemma F_af2c0 : fetch_word Plain.M.loaded_segments (0xaf2fc : word) = Some W_af2c0.
Proof. vm_refl. Qed.
Lemma D_af2c0 : decode_any W_af2c0 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2c4 : bv 32 := 0x000a3703.
Lemma F_af2c4 : fetch_word Plain.M.loaded_segments (0xaf300 : word) = Some W_af2c4.
Proof. vm_refl. Qed.
Lemma D_af2c4 : decode_any W_af2c4 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2c8 : bv 32 := 0x40c006b3.
Lemma F_af2c8 : fetch_word Plain.M.loaded_segments (0xaf304 : word) = Some W_af2c8.
Proof. vm_refl. Qed.
Lemma D_af2c8 : decode_any W_af2c8 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2cc : bv 32 := 0x00b6f6b3.
Lemma F_af2cc : fetch_word Plain.M.loaded_segments (0xaf308 : word) = Some W_af2cc.
Proof. vm_refl. Qed.
Lemma D_af2cc : decode_any W_af2cc = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2d0 : bv 32 := 0x40d506b3.
Lemma F_af2d0 : fetch_word Plain.M.loaded_segments (0xaf30c : word) = Some W_af2d0.
Proof. vm_refl. Qed.
Lemma D_af2d0 : decode_any W_af2d0 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2d4 : bv 32 := 0x00d70733.
Lemma F_af2d4 : fetch_word Plain.M.loaded_segments (0xaf310 : word) = Some W_af2d4.
Proof. vm_refl. Qed.
Lemma D_af2d4 : decode_any W_af2d4 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2d8 : bv 32 := 0x00ea3023.
Lemma F_af2d8 : fetch_word Plain.M.loaded_segments (0xaf314 : word) = Some W_af2d8.
Proof. vm_refl. Qed.
Lemma D_af2d8 : decode_any W_af2d8 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2dc : bv 32 := 0xf8a5fce3.
Lemma F_af2dc : fetch_word Plain.M.loaded_segments (0xaf318 : word) = Some W_af2dc.
Proof. vm_refl. Qed.
Lemma D_af2dc : decode_any W_af2dc = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2e0 : bv 32 := 0x01800713.
Lemma F_af2e0 : fetch_word Plain.M.loaded_segments (0xaf31c : word) = Some W_af2e0.
Proof. vm_refl. Qed.
Lemma D_af2e0 : decode_any W_af2e0 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af2e4 : bv 32 := 0xf95ff06f.
Lemma F_af2e4 : fetch_word Plain.M.loaded_segments (0xaf320 : word) = Some W_af2e4.
Proof. vm_refl. Qed.
Lemma D_af2e4 : decode_any W_af2e4 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af630 : bv 32 := 0xff010113.
Lemma F_af630 : fetch_word Plain.M.loaded_segments (0xaf66c : word) = Some W_af630.
Proof. vm_refl. Qed.
Lemma D_af630 : decode_any W_af630 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af634 : bv 32 := 0x00113423.
Lemma F_af634 : fetch_word Plain.M.loaded_segments (0xaf670 : word) = Some W_af634.
Proof. vm_refl. Qed.
Lemma D_af634 : decode_any W_af634 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af638 : bv 32 := 0x00813023.
Lemma F_af638 : fetch_word Plain.M.loaded_segments (0xaf674 : word) = Some W_af638.
Proof. vm_refl. Qed.
Lemma D_af638 : decode_any W_af638 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af63c : bv 32 := 0x41c000ef.
Lemma F_af63c : fetch_word Plain.M.loaded_segments (0xaf678 : word) = Some W_af63c.
Proof. vm_refl. Qed.
Lemma D_af63c : decode_any W_af63c = Some (Jal 1 1052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af640 : bv 32 := 0x00053403.
Lemma F_af640 : fetch_word Plain.M.loaded_segments (0xaf67c : word) = Some W_af640.
Proof. vm_refl. Qed.
Lemma D_af640 : decode_any W_af640 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af644 : bv 32 := 0x12041663.
Lemma F_af644 : fetch_word Plain.M.loaded_segments (0xaf680 : word) = Some W_af644.
Proof. vm_refl. Qed.
Lemma D_af644 : decode_any W_af644 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af648 : bv 32 := 0x0004a517.
Lemma F_af648 : fetch_word Plain.M.loaded_segments (0xaf684 : word) = Some W_af648.
Proof. vm_refl. Qed.
Lemma D_af648 : decode_any W_af648 = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af64c : bv 32 := 0x76453403.
Lemma F_af64c : fetch_word Plain.M.loaded_segments (0xaf688 : word) = Some W_af64c.
Proof. vm_refl. Qed.
Lemma D_af64c : decode_any W_af64c = Some (Load SZ8 true 8 10 1892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af650 : bv 32 := 0x04040a63.
Lemma F_af650 : fetch_word Plain.M.loaded_segments (0xaf68c : word) = Some W_af650.
Proof. vm_refl. Qed.
Lemma D_af650 : decode_any W_af650 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6a4 : bv 32 := 0x00018517.
Lemma F_af6a4 : fetch_word Plain.M.loaded_segments (0xaf6e0 : word) = Some W_af6a4.
Proof. vm_refl. Qed.
Lemma D_af6a4 : decode_any W_af6a4 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6a8 : bv 32 := 0x44053403.
Lemma F_af6a8 : fetch_word Plain.M.loaded_segments (0xaf6e4 : word) = Some W_af6a8.
Proof. vm_refl. Qed.
Lemma D_af6a8 : decode_any W_af6a8 = Some (Load SZ8 true 8 10 1088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6ac : bv 32 := 0x04040a63.
Lemma F_af6ac : fetch_word Plain.M.loaded_segments (0xaf6e8 : word) = Some W_af6ac.
Proof. vm_refl. Qed.
Lemma D_af6ac : decode_any W_af6ac = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6b0 : bv 32 := 0x08c42503.
Lemma F_af6b0 : fetch_word Plain.M.loaded_segments (0xaf6ec : word) = Some W_af6b0.
Proof. vm_refl. Qed.
Lemma D_af6b0 : decode_any W_af6b0 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6b4 : bv 32 := 0x00054663.
Lemma F_af6b4 : fetch_word Plain.M.loaded_segments (0xaf6f0 : word) = Some W_af6b4.
Proof. vm_refl. Qed.
Lemma D_af6b4 : decode_any W_af6b4 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6c0 : bv 32 := 0x02843503.
Lemma F_af6c0 : fetch_word Plain.M.loaded_segments (0xaf6fc : word) = Some W_af6c0.
Proof. vm_refl. Qed.
Lemma D_af6c0 : decode_any W_af6c0 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6c4 : bv 32 := 0x03843583.
Lemma F_af6c4 : fetch_word Plain.M.loaded_segments (0xaf700 : word) = Some W_af6c4.
Proof. vm_refl. Qed.
Lemma D_af6c4 : decode_any W_af6c4 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6c8 : bv 32 := 0x00b50c63.
Lemma F_af6c8 : fetch_word Plain.M.loaded_segments (0xaf704 : word) = Some W_af6c8.
Proof. vm_refl. Qed.
Lemma D_af6c8 : decode_any W_af6c8 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6cc : bv 32 := 0x04843683.
Lemma F_af6cc : fetch_word Plain.M.loaded_segments (0xaf708 : word) = Some W_af6cc.
Proof. vm_refl. Qed.
Lemma D_af6cc : decode_any W_af6cc = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6d0 : bv 32 := 0x00040513.
Lemma F_af6d0 : fetch_word Plain.M.loaded_segments (0xaf70c : word) = Some W_af6d0.
Proof. vm_refl. Qed.
Lemma D_af6d0 : decode_any W_af6d0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6d4 : bv 32 := 0x00000593.
Lemma F_af6d4 : fetch_word Plain.M.loaded_segments (0xaf710 : word) = Some W_af6d4.
Proof. vm_refl. Qed.
Lemma D_af6d4 : decode_any W_af6d4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6d8 : bv 32 := 0x00000613.
Lemma F_af6d8 : fetch_word Plain.M.loaded_segments (0xaf714 : word) = Some W_af6d8.
Proof. vm_refl. Qed.
Lemma D_af6d8 : decode_any W_af6d8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6dc : bv 32 := 0x000680e7.
Lemma F_af6dc : fetch_word Plain.M.loaded_segments (0xaf718 : word) = Some W_af6dc.
Proof. vm_refl. Qed.
Lemma D_af6dc : decode_any W_af6dc = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6e0 : bv 32 := 0x00843503.
Lemma F_af6e0 : fetch_word Plain.M.loaded_segments (0xaf71c : word) = Some W_af6e0.
Proof. vm_refl. Qed.
Lemma D_af6e0 : decode_any W_af6e0 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6e4 : bv 32 := 0x01043583.
Lemma F_af6e4 : fetch_word Plain.M.loaded_segments (0xaf720 : word) = Some W_af6e4.
Proof. vm_refl. Qed.
Lemma D_af6e4 : decode_any W_af6e4 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af6e8 : bv 32 := 0x00b50c63.
Lemma F_af6e8 : fetch_word Plain.M.loaded_segments (0xaf724 : word) = Some W_af6e8.
Proof. vm_refl. Qed.
Lemma D_af6e8 : decode_any W_af6e8 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af700 : bv 32 := 0x00018517.
Lemma F_af700 : fetch_word Plain.M.loaded_segments (0xaf73c : word) = Some W_af700.
Proof. vm_refl. Qed.
Lemma D_af700 : decode_any W_af700 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af704 : bv 32 := 0x2f453403.
Lemma F_af704 : fetch_word Plain.M.loaded_segments (0xaf740 : word) = Some W_af704.
Proof. vm_refl. Qed.
Lemma D_af704 : decode_any W_af704 = Some (Load SZ8 true 8 10 756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af708 : bv 32 := 0x0a040e63.
Lemma F_af708 : fetch_word Plain.M.loaded_segments (0xaf744 : word) = Some W_af708.
Proof. vm_refl. Qed.
Lemma D_af708 : decode_any W_af708 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af70c : bv 32 := 0x08c42503.
Lemma F_af70c : fetch_word Plain.M.loaded_segments (0xaf748 : word) = Some W_af70c.
Proof. vm_refl. Qed.
Lemma D_af70c : decode_any W_af70c = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af710 : bv 32 := 0x00054663.
Lemma F_af710 : fetch_word Plain.M.loaded_segments (0xaf74c : word) = Some W_af710.
Proof. vm_refl. Qed.
Lemma D_af710 : decode_any W_af710 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af71c : bv 32 := 0x02843503.
Lemma F_af71c : fetch_word Plain.M.loaded_segments (0xaf758 : word) = Some W_af71c.
Proof. vm_refl. Qed.
Lemma D_af71c : decode_any W_af71c = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af720 : bv 32 := 0x03843583.
Lemma F_af720 : fetch_word Plain.M.loaded_segments (0xaf75c : word) = Some W_af720.
Proof. vm_refl. Qed.
Lemma D_af720 : decode_any W_af720 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af724 : bv 32 := 0x00b50c63.
Lemma F_af724 : fetch_word Plain.M.loaded_segments (0xaf760 : word) = Some W_af724.
Proof. vm_refl. Qed.
Lemma D_af724 : decode_any W_af724 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af73c : bv 32 := 0x00843503.
Lemma F_af73c : fetch_word Plain.M.loaded_segments (0xaf778 : word) = Some W_af73c.
Proof. vm_refl. Qed.
Lemma D_af73c : decode_any W_af73c = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af740 : bv 32 := 0x01043583.
Lemma F_af740 : fetch_word Plain.M.loaded_segments (0xaf77c : word) = Some W_af740.
Proof. vm_refl. Qed.
Lemma D_af740 : decode_any W_af740 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af744 : bv 32 := 0x08b50063.
Lemma F_af744 : fetch_word Plain.M.loaded_segments (0xaf780 : word) = Some W_af744.
Proof. vm_refl. Qed.
Lemma D_af744 : decode_any W_af744 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af7c4 : bv 32 := 0x00813083.
Lemma F_af7c4 : fetch_word Plain.M.loaded_segments (0xaf800 : word) = Some W_af7c4.
Proof. vm_refl. Qed.
Lemma D_af7c4 : decode_any W_af7c4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af7c8 : bv 32 := 0x00013403.
Lemma F_af7c8 : fetch_word Plain.M.loaded_segments (0xaf804 : word) = Some W_af7c8.
Proof. vm_refl. Qed.
Lemma D_af7c8 : decode_any W_af7c8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af7cc : bv 32 := 0x01010113.
Lemma F_af7cc : fetch_word Plain.M.loaded_segments (0xaf808 : word) = Some W_af7cc.
Proof. vm_refl. Qed.
Lemma D_af7cc : decode_any W_af7cc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_af7d0 : bv 32 := 0x00008067.
Lemma F_af7d0 : fetch_word Plain.M.loaded_segments (0xaf80c : word) = Some W_af7d0.
Proof. vm_refl. Qed.
Lemma D_af7d0 : decode_any W_af7d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa58 : bv 32 := 0xff010113.
Lemma F_afa58 : fetch_word Plain.M.loaded_segments (0xafa94 : word) = Some W_afa58.
Proof. vm_refl. Qed.
Lemma D_afa58 : decode_any W_afa58 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa5c : bv 32 := 0x00113423.
Lemma F_afa5c : fetch_word Plain.M.loaded_segments (0xafa98 : word) = Some W_afa5c.
Proof. vm_refl. Qed.
Lemma D_afa5c : decode_any W_afa5c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa60 : bv 32 := 0x00813023.
Lemma F_afa60 : fetch_word Plain.M.loaded_segments (0xafa9c : word) = Some W_afa60.
Proof. vm_refl. Qed.
Lemma D_afa60 : decode_any W_afa60 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa64 : bv 32 := 0x0004a517.
Lemma F_afa64 : fetch_word Plain.M.loaded_segments (0xafaa0 : word) = Some W_afa64.
Proof. vm_refl. Qed.
Lemma D_afa64 : decode_any W_afa64 = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa68 : bv 32 := 0x35050413.
Lemma F_afa68 : fetch_word Plain.M.loaded_segments (0xafaa4 : word) = Some W_afa68.
Proof. vm_refl. Qed.
Lemma D_afa68 : decode_any W_afa68 = Some (OpImm ALU_ADD 8 10 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa6c : bv 32 := 0x00040513.
Lemma F_afa6c : fetch_word Plain.M.loaded_segments (0xafaa8 : word) = Some W_afa6c.
Proof. vm_refl. Qed.
Lemma D_afa6c : decode_any W_afa6c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa70 : bv 32 := 0x0410b0ef.
Lemma F_afa70 : fetch_word Plain.M.loaded_segments (0xafaac : word) = Some W_afa70.
Proof. vm_refl. Qed.
Lemma D_afa70 : decode_any W_afa70 = Some (Jal 1 47168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa74 : bv 32 := 0x00840513.
Lemma F_afa74 : fetch_word Plain.M.loaded_segments (0xafab0 : word) = Some W_afa74.
Proof. vm_refl. Qed.
Lemma D_afa74 : decode_any W_afa74 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa78 : bv 32 := 0x00813083.
Lemma F_afa78 : fetch_word Plain.M.loaded_segments (0xafab4 : word) = Some W_afa78.
Proof. vm_refl. Qed.
Lemma D_afa78 : decode_any W_afa78 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa7c : bv 32 := 0x00013403.
Lemma F_afa7c : fetch_word Plain.M.loaded_segments (0xafab8 : word) = Some W_afa7c.
Proof. vm_refl. Qed.
Lemma D_afa7c : decode_any W_afa7c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa80 : bv 32 := 0x01010113.
Lemma F_afa80 : fetch_word Plain.M.loaded_segments (0xafabc : word) = Some W_afa80.
Proof. vm_refl. Qed.
Lemma D_afa80 : decode_any W_afa80 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_afa84 : bv 32 := 0x00008067.
Lemma F_afa84 : fetch_word Plain.M.loaded_segments (0xafac0 : word) = Some W_afa84.
Proof. vm_refl. Qed.
Lemma D_afa84 : decode_any W_afa84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

