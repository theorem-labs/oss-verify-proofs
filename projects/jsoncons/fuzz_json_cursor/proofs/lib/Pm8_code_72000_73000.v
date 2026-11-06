(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_72224 : bv 32 := 0xfe010113.
Lemma F_72224 : fetch_word Asan.M.loaded_segments (0x72274 : word) = Some W_72224.
Proof. vm_refl. Qed.
Lemma D_72224 : decode_any W_72224 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_72228 : bv 32 := 0x00113c23.
Lemma F_72228 : fetch_word Asan.M.loaded_segments (0x72278 : word) = Some W_72228.
Proof. vm_refl. Qed.
Lemma D_72228 : decode_any W_72228 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7222c : bv 32 := 0x00813823.
Lemma F_7222c : fetch_word Asan.M.loaded_segments (0x7227c : word) = Some W_7222c.
Proof. vm_refl. Qed.
Lemma D_7222c : decode_any W_7222c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_72230 : bv 32 := 0x00913423.
Lemma F_72230 : fetch_word Asan.M.loaded_segments (0x72280 : word) = Some W_72230.
Proof. vm_refl. Qed.
Lemma D_72230 : decode_any W_72230 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_72234 : bv 32 := 0x01213023.
Lemma F_72234 : fetch_word Asan.M.loaded_segments (0x72284 : word) = Some W_72234.
Proof. vm_refl. Qed.
Lemma D_72234 : decode_any W_72234 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72238 : bv 32 := 0x00050413.
Lemma F_72238 : fetch_word Asan.M.loaded_segments (0x72288 : word) = Some W_72238.
Proof. vm_refl. Qed.
Lemma D_72238 : decode_any W_72238 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7223c : bv 32 := 0x038160ef.
Lemma F_7223c : fetch_word Asan.M.loaded_segments (0x7228c : word) = Some W_7223c.
Proof. vm_refl. Qed.
Lemma D_7223c : decode_any W_7223c = Some (Jal 1 90168, 4%Z).
Proof. vm_refl. Qed.

Definition W_72240 : bv 32 := 0x000e3597.
Lemma F_72240 : fetch_word Asan.M.loaded_segments (0x72290 : word) = Some W_72240.
Proof. vm_refl. Qed.
Lemma D_72240 : decode_any W_72240 = Some (Auipc 11 227, 4%Z).
Proof. vm_refl. Qed.

Definition W_72244 : bv 32 := 0xdc05b583.
Lemma F_72244 : fetch_word Asan.M.loaded_segments (0x72294 : word) = Some W_72244.
Proof. vm_refl. Qed.
Lemma D_72244 : decode_any W_72244 = Some (Load SZ8 true 11 11 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_72248 : bv 32 := 0x00050913.
Lemma F_72248 : fetch_word Asan.M.loaded_segments (0x72298 : word) = Some W_72248.
Proof. vm_refl. Qed.
Lemma D_72248 : decode_any W_72248 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7224c : bv 32 := 0x00040513.
Lemma F_7224c : fetch_word Asan.M.loaded_segments (0x7229c : word) = Some W_7224c.
Proof. vm_refl. Qed.
Lemma D_7224c : decode_any W_7224c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72250 : bv 32 := 0x000580e7.
Lemma F_72250 : fetch_word Asan.M.loaded_segments (0x722a0 : word) = Some W_72250.
Proof. vm_refl. Qed.
Lemma D_72250 : decode_any W_72250 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72254 : bv 32 := 0x00050493.
Lemma F_72254 : fetch_word Asan.M.loaded_segments (0x722a4 : word) = Some W_72254.
Proof. vm_refl. Qed.
Lemma D_72254 : decode_any W_72254 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72258 : bv 32 := 0x02090663.
Lemma F_72258 : fetch_word Asan.M.loaded_segments (0x722a8 : word) = Some W_72258.
Proof. vm_refl. Qed.
Lemma D_72258 : decode_any W_72258 = Some (Branch BC_EQ 18 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_7225c : bv 32 := 0x019180ef.
Lemma F_7225c : fetch_word Asan.M.loaded_segments (0x722ac : word) = Some W_7225c.
Proof. vm_refl. Qed.
Lemma D_7225c : decode_any W_7225c = Some (Jal 1 100376, 4%Z).
Proof. vm_refl. Qed.

Definition W_72260 : bv 32 := 0x00050863.
Lemma F_72260 : fetch_word Asan.M.loaded_segments (0x722b0 : word) = Some W_72260.
Proof. vm_refl. Qed.
Lemma D_72260 : decode_any W_72260 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_72264 : bv 32 := 0x03053603.
Lemma F_72264 : fetch_word Asan.M.loaded_segments (0x722b4 : word) = Some W_72264.
Proof. vm_refl. Qed.
Lemma D_72264 : decode_any W_72264 = Some (Load SZ8 true 12 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_72268 : bv 32 := 0x03853683.
Lemma F_72268 : fetch_word Asan.M.loaded_segments (0x722b8 : word) = Some W_72268.
Proof. vm_refl. Qed.
Lemma D_72268 : decode_any W_72268 = Some (Load SZ8 true 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7226c : bv 32 := 0x00c0006f.
Lemma F_7226c : fetch_word Asan.M.loaded_segments (0x722bc : word) = Some W_7226c.
Proof. vm_refl. Qed.
Lemma D_7226c : decode_any W_7226c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_72278 : bv 32 := 0x00040513.
Lemma F_72278 : fetch_word Asan.M.loaded_segments (0x722c8 : word) = Some W_72278.
Proof. vm_refl. Qed.
Lemma D_72278 : decode_any W_72278 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7227c : bv 32 := 0x00048593.
Lemma F_7227c : fetch_word Asan.M.loaded_segments (0x722cc : word) = Some W_7227c.
Proof. vm_refl. Qed.
Lemma D_7227c : decode_any W_7227c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72280 : bv 32 := 0x725250ef.
Lemma F_72280 : fetch_word Asan.M.loaded_segments (0x722d0 : word) = Some W_72280.
Proof. vm_refl. Qed.
Lemma D_72280 : decode_any W_72280 = Some (Jal 1 155428, 4%Z).
Proof. vm_refl. Qed.

Definition W_72284 : bv 32 := 0x00048513.
Lemma F_72284 : fetch_word Asan.M.loaded_segments (0x722d4 : word) = Some W_72284.
Proof. vm_refl. Qed.
Lemma D_72284 : decode_any W_72284 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72288 : bv 32 := 0x01813083.
Lemma F_72288 : fetch_word Asan.M.loaded_segments (0x722d8 : word) = Some W_72288.
Proof. vm_refl. Qed.
Lemma D_72288 : decode_any W_72288 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7228c : bv 32 := 0x01013403.
Lemma F_7228c : fetch_word Asan.M.loaded_segments (0x722dc : word) = Some W_7228c.
Proof. vm_refl. Qed.
Lemma D_7228c : decode_any W_7228c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_72290 : bv 32 := 0x00813483.
Lemma F_72290 : fetch_word Asan.M.loaded_segments (0x722e0 : word) = Some W_72290.
Proof. vm_refl. Qed.
Lemma D_72290 : decode_any W_72290 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_72294 : bv 32 := 0x00013903.
Lemma F_72294 : fetch_word Asan.M.loaded_segments (0x722e4 : word) = Some W_72294.
Proof. vm_refl. Qed.
Lemma D_72294 : decode_any W_72294 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_72298 : bv 32 := 0x02010113.
Lemma F_72298 : fetch_word Asan.M.loaded_segments (0x722e8 : word) = Some W_72298.
Proof. vm_refl. Qed.
Lemma D_72298 : decode_any W_72298 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7229c : bv 32 := 0x00008067.
Lemma F_7229c : fetch_word Asan.M.loaded_segments (0x722ec : word) = Some W_7229c.
Proof. vm_refl. Qed.
Lemma D_7229c : decode_any W_7229c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

