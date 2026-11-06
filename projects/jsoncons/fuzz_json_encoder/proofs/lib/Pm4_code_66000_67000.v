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
Definition W_66000 : bv 32 := 0x0084b603.
Lemma F_66000 : fetch_word Asan.M.loaded_segments (0x66050 : word) = Some W_66000.
Proof. vm_refl. Qed.
Lemma D_66000 : decode_any W_66000 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66004 : bv 32 := 0x00b797b3.
Lemma F_66004 : fetch_word Asan.M.loaded_segments (0x66054 : word) = Some W_66004.
Proof. vm_refl. Qed.
Lemma D_66004 : decode_any W_66004 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66008 : bv 32 := 0xfff50813.
Lemma F_66008 : fetch_word Asan.M.loaded_segments (0x66058 : word) = Some W_66008.
Proof. vm_refl. Qed.
Lemma D_66008 : decode_any W_66008 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6600c : bv 32 := 0x00d485b3.
Lemma F_6600c : fetch_word Asan.M.loaded_segments (0x6605c : word) = Some W_6600c.
Proof. vm_refl. Qed.
Lemma D_6600c : decode_any W_6600c = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66010 : bv 32 := 0x00e586b3.
Lemma F_66010 : fetch_word Asan.M.loaded_segments (0x66060 : word) = Some W_66010.
Proof. vm_refl. Qed.
Lemma D_66010 : decode_any W_66010 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66014 : bv 32 := 0xfff7c713.
Lemma F_66014 : fetch_word Asan.M.loaded_segments (0x66064 : word) = Some W_66014.
Proof. vm_refl. Qed.
Lemma D_66014 : decode_any W_66014 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66018 : bv 32 := 0x02081813.
Lemma F_66018 : fetch_word Asan.M.loaded_segments (0x66068 : word) = Some W_66018.
Proof. vm_refl. Qed.
Lemma D_66018 : decode_any W_66018 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6601c : bv 32 := 0x02085793.
Lemma F_6601c : fetch_word Asan.M.loaded_segments (0x6606c : word) = Some W_6601c.
Proof. vm_refl. Qed.
Lemma D_6601c : decode_any W_6601c = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66020 : bv 32 := 0x00f607b3.
Lemma F_66020 : fetch_word Asan.M.loaded_segments (0x66070 : word) = Some W_66020.
Proof. vm_refl. Qed.
Lemma D_66020 : decode_any W_66020 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66024 : bv 32 := 0x00178813.
Lemma F_66024 : fetch_word Asan.M.loaded_segments (0x66074 : word) = Some W_66024.
Proof. vm_refl. Qed.
Lemma D_66024 : decode_any W_66024 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66028 : bv 32 := 0x00e678b3.
Lemma F_66028 : fetch_word Asan.M.loaded_segments (0x66078 : word) = Some W_66028.
Proof. vm_refl. Qed.
Lemma D_66028 : decode_any W_66028 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6602c : bv 32 := 0x011687b3.
Lemma F_6602c : fetch_word Asan.M.loaded_segments (0x6607c : word) = Some W_6602c.
Proof. vm_refl. Qed.
Lemma D_6602c : decode_any W_6602c = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66030 : bv 32 := 0x0007c283.
Lemma F_66030 : fetch_word Asan.M.loaded_segments (0x66080 : word) = Some W_66030.
Proof. vm_refl. Qed.
Lemma D_66030 : decode_any W_66030 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66034 : bv 32 := 0x06028663.
Lemma F_66034 : fetch_word Asan.M.loaded_segments (0x66084 : word) = Some W_66034.
Proof. vm_refl. Qed.
Lemma D_66034 : decode_any W_66034 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66038 : bv 32 := 0xfff5051b.
Lemma F_66038 : fetch_word Asan.M.loaded_segments (0x66088 : word) = Some W_66038.
Proof. vm_refl. Qed.
Lemma D_66038 : decode_any W_66038 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6603c : bv 32 := 0x00160613.
Lemma F_6603c : fetch_word Asan.M.loaded_segments (0x6608c : word) = Some W_6603c.
Proof. vm_refl. Qed.
Lemma D_6603c : decode_any W_6603c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66040 : bv 32 := 0xfe0514e3.
Lemma F_66040 : fetch_word Asan.M.loaded_segments (0x66090 : word) = Some W_66040.
Proof. vm_refl. Qed.
Lemma D_66040 : decode_any W_66040 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660a0 : bv 32 := 0x00160613.
Lemma F_660a0 : fetch_word Asan.M.loaded_segments (0x660f0 : word) = Some W_660a0.
Proof. vm_refl. Qed.
Lemma D_660a0 : decode_any W_660a0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660a4 : bv 32 := 0x00100513.
Lemma F_660a4 : fetch_word Asan.M.loaded_segments (0x660f4 : word) = Some W_660a4.
Proof. vm_refl. Qed.
Lemma D_660a4 : decode_any W_660a4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660a8 : bv 32 := 0xffb90693.
Lemma F_660a8 : fetch_word Asan.M.loaded_segments (0x660f8 : word) = Some W_660a8.
Proof. vm_refl. Qed.
Lemma D_660a8 : decode_any W_660a8 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660ac : bv 32 := 0x00789893.
Lemma F_660ac : fetch_word Asan.M.loaded_segments (0x660fc : word) = Some W_660ac.
Proof. vm_refl. Qed.
Lemma D_660ac : decode_any W_660ac = Some (ShiftImm ALU_SLL 17 17 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660b0 : bv 32 := 0x00c4b423.
Lemma F_660b0 : fetch_word Asan.M.loaded_segments (0x66100 : word) = Some W_660b0.
Proof. vm_refl. Qed.
Lemma D_660b0 : decode_any W_660b0 = Some (Store SZ8 9 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660b4 : bv 32 := 0x00a78023.
Lemma F_660b4 : fetch_word Asan.M.loaded_segments (0x66104 : word) = Some W_660b4.
Proof. vm_refl. Qed.
Lemma D_660b4 : decode_any W_660b4 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660b8 : bv 32 := 0x00d51633.
Lemma F_660b8 : fetch_word Asan.M.loaded_segments (0x66108 : word) = Some W_660b8.
Proof. vm_refl. Qed.
Lemma D_660b8 : decode_any W_660b8 = Some (Op ALU_SLL 12 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660bc : bv 32 := 0x01251533.
Lemma F_660bc : fetch_word Asan.M.loaded_segments (0x6610c : word) = Some W_660bc.
Proof. vm_refl. Qed.
Lemma D_660bc : decode_any W_660bc = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660c0 : bv 32 := 0x00c585b3.
Lemma F_660c0 : fetch_word Asan.M.loaded_segments (0x66110 : word) = Some W_660c0.
Proof. vm_refl. Qed.
Lemma D_660c0 : decode_any W_660c0 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660c4 : bv 32 := 0x01150533.
Lemma F_660c4 : fetch_word Asan.M.loaded_segments (0x66114 : word) = Some W_660c4.
Proof. vm_refl. Qed.
Lemma D_660c4 : decode_any W_660c4 = Some (Op ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660c8 : bv 32 := 0x00a584b3.
Lemma F_660c8 : fetch_word Asan.M.loaded_segments (0x66118 : word) = Some W_660c8.
Proof. vm_refl. Qed.
Lemma D_660c8 : decode_any W_660c8 = Some (Op ALU_ADD 9 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660cc : bv 32 := 0x0084bc23.
Lemma F_660cc : fetch_word Asan.M.loaded_segments (0x6611c : word) = Some W_660cc.
Proof. vm_refl. Qed.
Lemma D_660cc : decode_any W_660cc = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660d0 : bv 32 := 0x06f4bc23.
Lemma F_660d0 : fetch_word Asan.M.loaded_segments (0x66120 : word) = Some W_660d0.
Proof. vm_refl. Qed.
Lemma D_660d0 : decode_any W_660d0 = Some (Store SZ8 9 15 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660d4 : bv 32 := 0x00048513.
Lemma F_660d4 : fetch_word Asan.M.loaded_segments (0x66124 : word) = Some W_660d4.
Proof. vm_refl. Qed.
Lemma D_660d4 : decode_any W_660d4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660d8 : bv 32 := 0x021000ef.
Lemma F_660d8 : fetch_word Asan.M.loaded_segments (0x66128 : word) = Some W_660d8.
Proof. vm_refl. Qed.
Lemma D_660d8 : decode_any W_660d8 = Some (Jal 1 2080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660dc : bv 32 := 0x00050593.
Lemma F_660dc : fetch_word Asan.M.loaded_segments (0x6612c : word) = Some W_660dc.
Proof. vm_refl. Qed.
Lemma D_660dc : decode_any W_660dc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660e0 : bv 32 := 0x00048513.
Lemma F_660e0 : fetch_word Asan.M.loaded_segments (0x66130 : word) = Some W_660e0.
Proof. vm_refl. Qed.
Lemma D_660e0 : decode_any W_660e0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660e4 : bv 32 := 0x00000613.
Lemma F_660e4 : fetch_word Asan.M.loaded_segments (0x66134 : word) = Some W_660e4.
Proof. vm_refl. Qed.
Lemma D_660e4 : decode_any W_660e4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660e8 : bv 32 := 0x0005b023.
Lemma F_660e8 : fetch_word Asan.M.loaded_segments (0x66138 : word) = Some W_660e8.
Proof. vm_refl. Qed.
Lemma D_660e8 : decode_any W_660e8 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660ec : bv 32 := 0x0005b423.
Lemma F_660ec : fetch_word Asan.M.loaded_segments (0x6613c : word) = Some W_660ec.
Proof. vm_refl. Qed.
Lemma D_660ec : decode_any W_660ec = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660f0 : bv 32 := 0x01813083.
Lemma F_660f0 : fetch_word Asan.M.loaded_segments (0x66140 : word) = Some W_660f0.
Proof. vm_refl. Qed.
Lemma D_660f0 : decode_any W_660f0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660f4 : bv 32 := 0x01013403.
Lemma F_660f4 : fetch_word Asan.M.loaded_segments (0x66144 : word) = Some W_660f4.
Proof. vm_refl. Qed.
Lemma D_660f4 : decode_any W_660f4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660f8 : bv 32 := 0x00813483.
Lemma F_660f8 : fetch_word Asan.M.loaded_segments (0x66148 : word) = Some W_660f8.
Proof. vm_refl. Qed.
Lemma D_660f8 : decode_any W_660f8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_660fc : bv 32 := 0x00013903.
Lemma F_660fc : fetch_word Asan.M.loaded_segments (0x6614c : word) = Some W_660fc.
Proof. vm_refl. Qed.
Lemma D_660fc : decode_any W_660fc = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66100 : bv 32 := 0x02010113.
Lemma F_66100 : fetch_word Asan.M.loaded_segments (0x66150 : word) = Some W_66100.
Proof. vm_refl. Qed.
Lemma D_66100 : decode_any W_66100 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66104 : bv 32 := 0x00008067.
Lemma F_66104 : fetch_word Asan.M.loaded_segments (0x66154 : word) = Some W_66104.
Proof. vm_refl. Qed.
Lemma D_66104 : decode_any W_66104 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66124 : bv 32 := 0xfe010113.
Lemma F_66124 : fetch_word Asan.M.loaded_segments (0x66174 : word) = Some W_66124.
Proof. vm_refl. Qed.
Lemma D_66124 : decode_any W_66124 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66128 : bv 32 := 0x00113c23.
Lemma F_66128 : fetch_word Asan.M.loaded_segments (0x66178 : word) = Some W_66128.
Proof. vm_refl. Qed.
Lemma D_66128 : decode_any W_66128 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6612c : bv 32 := 0x00813823.
Lemma F_6612c : fetch_word Asan.M.loaded_segments (0x6617c : word) = Some W_6612c.
Proof. vm_refl. Qed.
Lemma D_6612c : decode_any W_6612c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66130 : bv 32 := 0x00913423.
Lemma F_66130 : fetch_word Asan.M.loaded_segments (0x66180 : word) = Some W_66130.
Proof. vm_refl. Qed.
Lemma D_66130 : decode_any W_66130 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66134 : bv 32 := 0x01213023.
Lemma F_66134 : fetch_word Asan.M.loaded_segments (0x66184 : word) = Some W_66134.
Proof. vm_refl. Qed.
Lemma D_66134 : decode_any W_66134 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66138 : bv 32 := 0x02010413.
Lemma F_66138 : fetch_word Asan.M.loaded_segments (0x66188 : word) = Some W_66138.
Proof. vm_refl. Qed.
Lemma D_66138 : decode_any W_66138 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6613c : bv 32 := 0x000fc517.
Lemma F_6613c : fetch_word Asan.M.loaded_segments (0x6618c : word) = Some W_6613c.
Proof. vm_refl. Qed.
Lemma D_6613c : decode_any W_6613c = Some (Auipc 10 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66140 : bv 32 := 0x8ac50513.
Lemma F_66140 : fetch_word Asan.M.loaded_segments (0x66190 : word) = Some W_66140.
Proof. vm_refl. Qed.
Lemma D_66140 : decode_any W_66140 = Some (OpImm ALU_ADD 10 10 2220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66144 : bv 32 := 0x009050ef.
Lemma F_66144 : fetch_word Asan.M.loaded_segments (0x66194 : word) = Some W_66144.
Proof. vm_refl. Qed.
Lemma D_66144 : decode_any W_66144 = Some (Jal 1 22536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66148 : bv 32 := 0x00053483.
Lemma F_66148 : fetch_word Asan.M.loaded_segments (0x66198 : word) = Some W_66148.
Proof. vm_refl. Qed.
Lemma D_66148 : decode_any W_66148 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6614c : bv 32 := 0x08048863.
Lemma F_6614c : fetch_word Asan.M.loaded_segments (0x6619c : word) = Some W_6614c.
Proof. vm_refl. Qed.
Lemma D_6614c : decode_any W_6614c = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66150 : bv 32 := 0x0604c503.
Lemma F_66150 : fetch_word Asan.M.loaded_segments (0x661a0 : word) = Some W_66150.
Proof. vm_refl. Qed.
Lemma D_66150 : decode_any W_66150 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66154 : bv 32 := 0x0584b903.
Lemma F_66154 : fetch_word Asan.M.loaded_segments (0x661a4 : word) = Some W_66154.
Proof. vm_refl. Qed.
Lemma D_66154 : decode_any W_66154 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66158 : bv 32 := 0x00050863.
Lemma F_66158 : fetch_word Asan.M.loaded_segments (0x661a8 : word) = Some W_66158.
Proof. vm_refl. Qed.
Lemma D_66158 : decode_any W_66158 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6615c : bv 32 := 0x00048513.
Lemma F_6615c : fetch_word Asan.M.loaded_segments (0x661ac : word) = Some W_6615c.
Proof. vm_refl. Qed.
Lemma D_6615c : decode_any W_6615c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66160 : bv 32 := 0x00040593.
Lemma F_66160 : fetch_word Asan.M.loaded_segments (0x661b0 : word) = Some W_66160.
Proof. vm_refl. Qed.
Lemma D_66160 : decode_any W_66160 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66164 : bv 32 := 0x871ff0ef.
Lemma F_66164 : fetch_word Asan.M.loaded_segments (0x661b4 : word) = Some W_66164.
Proof. vm_refl. Qed.
Lemma D_66164 : decode_any W_66164 = Some (Jal 1 2095216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66168 : bv 32 := 0xff890593.
Lemma F_66168 : fetch_word Asan.M.loaded_segments (0x661b8 : word) = Some W_66168.
Proof. vm_refl. Qed.
Lemma D_66168 : decode_any W_66168 = Some (OpImm ALU_ADD 11 18 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6616c : bv 32 := 0x00100513.
Lemma F_6616c : fetch_word Asan.M.loaded_segments (0x661bc : word) = Some W_6616c.
Proof. vm_refl. Qed.
Lemma D_6616c : decode_any W_6616c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66170 : bv 32 := 0x00b51533.
Lemma F_66170 : fetch_word Asan.M.loaded_segments (0x661c0 : word) = Some W_66170.
Proof. vm_refl. Qed.
Lemma D_66170 : decode_any W_66170 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66174 : bv 32 := 0x0005061b.
Lemma F_66174 : fetch_word Asan.M.loaded_segments (0x661c4 : word) = Some W_66174.
Proof. vm_refl. Qed.
Lemma D_66174 : decode_any W_66174 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66178 : bv 32 := 0x08c05263.
Lemma F_66178 : fetch_word Asan.M.loaded_segments (0x661c8 : word) = Some W_66178.
Proof. vm_refl. Qed.
Lemma D_66178 : decode_any W_66178 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6617c : bv 32 := 0x000016b7.
Lemma F_6617c : fetch_word Asan.M.loaded_segments (0x661cc : word) = Some W_6617c.
Proof. vm_refl. Qed.
Lemma D_6617c : decode_any W_6617c = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66180 : bv 32 := 0xff190613.
Lemma F_66180 : fetch_word Asan.M.loaded_segments (0x661d0 : word) = Some W_66180.
Proof. vm_refl. Qed.
Lemma D_66180 : decode_any W_66180 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66184 : bv 32 := 0x30000713.
Lemma F_66184 : fetch_word Asan.M.loaded_segments (0x661d4 : word) = Some W_66184.
Proof. vm_refl. Qed.
Lemma D_66184 : decode_any W_66184 = Some (OpImm ALU_ADD 14 0 768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66188 : bv 32 := 0xfff00793.
Lemma F_66188 : fetch_word Asan.M.loaded_segments (0x661d8 : word) = Some W_66188.
Proof. vm_refl. Qed.
Lemma D_66188 : decode_any W_66188 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6618c : bv 32 := 0x00c71733.
Lemma F_6618c : fetch_word Asan.M.loaded_segments (0x661dc : word) = Some W_6618c.
Proof. vm_refl. Qed.
Lemma D_6618c : decode_any W_6618c = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66190 : bv 32 := 0x0104b603.
Lemma F_66190 : fetch_word Asan.M.loaded_segments (0x661e0 : word) = Some W_66190.
Proof. vm_refl. Qed.
Lemma D_66190 : decode_any W_66190 = Some (Load SZ8 true 12 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66194 : bv 32 := 0x00b797b3.
Lemma F_66194 : fetch_word Asan.M.loaded_segments (0x661e4 : word) = Some W_66194.
Proof. vm_refl. Qed.
Lemma D_66194 : decode_any W_66194 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66198 : bv 32 := 0xfff50813.
Lemma F_66198 : fetch_word Asan.M.loaded_segments (0x661e8 : word) = Some W_66198.
Proof. vm_refl. Qed.
Lemma D_66198 : decode_any W_66198 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6619c : bv 32 := 0x00d485b3.
Lemma F_6619c : fetch_word Asan.M.loaded_segments (0x661ec : word) = Some W_6619c.
Proof. vm_refl. Qed.
Lemma D_6619c : decode_any W_6619c = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661a0 : bv 32 := 0x00e586b3.
Lemma F_661a0 : fetch_word Asan.M.loaded_segments (0x661f0 : word) = Some W_661a0.
Proof. vm_refl. Qed.
Lemma D_661a0 : decode_any W_661a0 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661a4 : bv 32 := 0xfff7c713.
Lemma F_661a4 : fetch_word Asan.M.loaded_segments (0x661f4 : word) = Some W_661a4.
Proof. vm_refl. Qed.
Lemma D_661a4 : decode_any W_661a4 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661a8 : bv 32 := 0x02081813.
Lemma F_661a8 : fetch_word Asan.M.loaded_segments (0x661f8 : word) = Some W_661a8.
Proof. vm_refl. Qed.
Lemma D_661a8 : decode_any W_661a8 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661ac : bv 32 := 0x02085793.
Lemma F_661ac : fetch_word Asan.M.loaded_segments (0x661fc : word) = Some W_661ac.
Proof. vm_refl. Qed.
Lemma D_661ac : decode_any W_661ac = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661b0 : bv 32 := 0x00f607b3.
Lemma F_661b0 : fetch_word Asan.M.loaded_segments (0x66200 : word) = Some W_661b0.
Proof. vm_refl. Qed.
Lemma D_661b0 : decode_any W_661b0 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661b4 : bv 32 := 0x00178813.
Lemma F_661b4 : fetch_word Asan.M.loaded_segments (0x66204 : word) = Some W_661b4.
Proof. vm_refl. Qed.
Lemma D_661b4 : decode_any W_661b4 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661b8 : bv 32 := 0x00e678b3.
Lemma F_661b8 : fetch_word Asan.M.loaded_segments (0x66208 : word) = Some W_661b8.
Proof. vm_refl. Qed.
Lemma D_661b8 : decode_any W_661b8 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661bc : bv 32 := 0x011687b3.
Lemma F_661bc : fetch_word Asan.M.loaded_segments (0x6620c : word) = Some W_661bc.
Proof. vm_refl. Qed.
Lemma D_661bc : decode_any W_661bc = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661c0 : bv 32 := 0x0007c283.
Lemma F_661c0 : fetch_word Asan.M.loaded_segments (0x66210 : word) = Some W_661c0.
Proof. vm_refl. Qed.
Lemma D_661c0 : decode_any W_661c0 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661c4 : bv 32 := 0x06028663.
Lemma F_661c4 : fetch_word Asan.M.loaded_segments (0x66214 : word) = Some W_661c4.
Proof. vm_refl. Qed.
Lemma D_661c4 : decode_any W_661c4 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661c8 : bv 32 := 0xfff5051b.
Lemma F_661c8 : fetch_word Asan.M.loaded_segments (0x66218 : word) = Some W_661c8.
Proof. vm_refl. Qed.
Lemma D_661c8 : decode_any W_661c8 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661cc : bv 32 := 0x00160613.
Lemma F_661cc : fetch_word Asan.M.loaded_segments (0x6621c : word) = Some W_661cc.
Proof. vm_refl. Qed.
Lemma D_661cc : decode_any W_661cc = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_661d0 : bv 32 := 0xfe0514e3.
Lemma F_661d0 : fetch_word Asan.M.loaded_segments (0x66220 : word) = Some W_661d0.
Proof. vm_refl. Qed.
Lemma D_661d0 : decode_any W_661d0 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66230 : bv 32 := 0x00160613.
Lemma F_66230 : fetch_word Asan.M.loaded_segments (0x66280 : word) = Some W_66230.
Proof. vm_refl. Qed.
Lemma D_66230 : decode_any W_66230 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66234 : bv 32 := 0x00100513.
Lemma F_66234 : fetch_word Asan.M.loaded_segments (0x66284 : word) = Some W_66234.
Proof. vm_refl. Qed.
Lemma D_66234 : decode_any W_66234 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66238 : bv 32 := 0xffb90693.
Lemma F_66238 : fetch_word Asan.M.loaded_segments (0x66288 : word) = Some W_66238.
Proof. vm_refl. Qed.
Lemma D_66238 : decode_any W_66238 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6623c : bv 32 := 0x00c4b823.
Lemma F_6623c : fetch_word Asan.M.loaded_segments (0x6628c : word) = Some W_6623c.
Proof. vm_refl. Qed.
Lemma D_6623c : decode_any W_6623c = Some (Store SZ8 9 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66240 : bv 32 := 0x00a78023.
Lemma F_66240 : fetch_word Asan.M.loaded_segments (0x66290 : word) = Some W_66240.
Proof. vm_refl. Qed.
Lemma D_66240 : decode_any W_66240 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66244 : bv 32 := 0x00d51533.
Lemma F_66244 : fetch_word Asan.M.loaded_segments (0x66294 : word) = Some W_66244.
Proof. vm_refl. Qed.
Lemma D_66244 : decode_any W_66244 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66248 : bv 32 := 0x00200613.
Lemma F_66248 : fetch_word Asan.M.loaded_segments (0x66298 : word) = Some W_66248.
Proof. vm_refl. Qed.
Lemma D_66248 : decode_any W_66248 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6624c : bv 32 := 0x00889893.
Lemma F_6624c : fetch_word Asan.M.loaded_segments (0x6629c : word) = Some W_6624c.
Proof. vm_refl. Qed.
Lemma D_6624c : decode_any W_6624c = Some (ShiftImm ALU_SLL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66250 : bv 32 := 0x01261633.
Lemma F_66250 : fetch_word Asan.M.loaded_segments (0x662a0 : word) = Some W_66250.
Proof. vm_refl. Qed.
Lemma D_66250 : decode_any W_66250 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66254 : bv 32 := 0x00a58533.
Lemma F_66254 : fetch_word Asan.M.loaded_segments (0x662a4 : word) = Some W_66254.
Proof. vm_refl. Qed.
Lemma D_66254 : decode_any W_66254 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66258 : bv 32 := 0x01160633.
Lemma F_66258 : fetch_word Asan.M.loaded_segments (0x662a8 : word) = Some W_66258.
Proof. vm_refl. Qed.
Lemma D_66258 : decode_any W_66258 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6625c : bv 32 := 0x00c504b3.
Lemma F_6625c : fetch_word Asan.M.loaded_segments (0x662ac : word) = Some W_6625c.
Proof. vm_refl. Qed.
Lemma D_6625c : decode_any W_6625c = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66260 : bv 32 := 0x0084bc23.
Lemma F_66260 : fetch_word Asan.M.loaded_segments (0x662b0 : word) = Some W_66260.
Proof. vm_refl. Qed.
Lemma D_66260 : decode_any W_66260 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66264 : bv 32 := 0x0ef4bc23.
Lemma F_66264 : fetch_word Asan.M.loaded_segments (0x662b4 : word) = Some W_66264.
Proof. vm_refl. Qed.
Lemma D_66264 : decode_any W_66264 = Some (Store SZ8 9 15 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66268 : bv 32 := 0x00048513.
Lemma F_66268 : fetch_word Asan.M.loaded_segments (0x662b8 : word) = Some W_66268.
Proof. vm_refl. Qed.
Lemma D_66268 : decode_any W_66268 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6626c : bv 32 := 0x68c000ef.
Lemma F_6626c : fetch_word Asan.M.loaded_segments (0x662bc : word) = Some W_6626c.
Proof. vm_refl. Qed.
Lemma D_6626c : decode_any W_6626c = Some (Jal 1 1676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66270 : bv 32 := 0x00050593.
Lemma F_66270 : fetch_word Asan.M.loaded_segments (0x662c0 : word) = Some W_66270.
Proof. vm_refl. Qed.
Lemma D_66270 : decode_any W_66270 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66274 : bv 32 := 0x00048513.
Lemma F_66274 : fetch_word Asan.M.loaded_segments (0x662c4 : word) = Some W_66274.
Proof. vm_refl. Qed.
Lemma D_66274 : decode_any W_66274 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66278 : bv 32 := 0x00000613.
Lemma F_66278 : fetch_word Asan.M.loaded_segments (0x662c8 : word) = Some W_66278.
Proof. vm_refl. Qed.
Lemma D_66278 : decode_any W_66278 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6627c : bv 32 := 0x0005b023.
Lemma F_6627c : fetch_word Asan.M.loaded_segments (0x662cc : word) = Some W_6627c.
Proof. vm_refl. Qed.
Lemma D_6627c : decode_any W_6627c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66280 : bv 32 := 0x0005b423.
Lemma F_66280 : fetch_word Asan.M.loaded_segments (0x662d0 : word) = Some W_66280.
Proof. vm_refl. Qed.
Lemma D_66280 : decode_any W_66280 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66284 : bv 32 := 0x0005b823.
Lemma F_66284 : fetch_word Asan.M.loaded_segments (0x662d4 : word) = Some W_66284.
Proof. vm_refl. Qed.
Lemma D_66284 : decode_any W_66284 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66288 : bv 32 := 0x0005bc23.
Lemma F_66288 : fetch_word Asan.M.loaded_segments (0x662d8 : word) = Some W_66288.
Proof. vm_refl. Qed.
Lemma D_66288 : decode_any W_66288 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6628c : bv 32 := 0x01813083.
Lemma F_6628c : fetch_word Asan.M.loaded_segments (0x662dc : word) = Some W_6628c.
Proof. vm_refl. Qed.
Lemma D_6628c : decode_any W_6628c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66290 : bv 32 := 0x01013403.
Lemma F_66290 : fetch_word Asan.M.loaded_segments (0x662e0 : word) = Some W_66290.
Proof. vm_refl. Qed.
Lemma D_66290 : decode_any W_66290 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66294 : bv 32 := 0x00813483.
Lemma F_66294 : fetch_word Asan.M.loaded_segments (0x662e4 : word) = Some W_66294.
Proof. vm_refl. Qed.
Lemma D_66294 : decode_any W_66294 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66298 : bv 32 := 0x00013903.
Lemma F_66298 : fetch_word Asan.M.loaded_segments (0x662e8 : word) = Some W_66298.
Proof. vm_refl. Qed.
Lemma D_66298 : decode_any W_66298 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6629c : bv 32 := 0x02010113.
Lemma F_6629c : fetch_word Asan.M.loaded_segments (0x662ec : word) = Some W_6629c.
Proof. vm_refl. Qed.
Lemma D_6629c : decode_any W_6629c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662a0 : bv 32 := 0x00008067.
Lemma F_662a0 : fetch_word Asan.M.loaded_segments (0x662f0 : word) = Some W_662a0.
Proof. vm_refl. Qed.
Lemma D_662a0 : decode_any W_662a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662c0 : bv 32 := 0xfe010113.
Lemma F_662c0 : fetch_word Asan.M.loaded_segments (0x66310 : word) = Some W_662c0.
Proof. vm_refl. Qed.
Lemma D_662c0 : decode_any W_662c0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662c4 : bv 32 := 0x00113c23.
Lemma F_662c4 : fetch_word Asan.M.loaded_segments (0x66314 : word) = Some W_662c4.
Proof. vm_refl. Qed.
Lemma D_662c4 : decode_any W_662c4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662c8 : bv 32 := 0x00813823.
Lemma F_662c8 : fetch_word Asan.M.loaded_segments (0x66318 : word) = Some W_662c8.
Proof. vm_refl. Qed.
Lemma D_662c8 : decode_any W_662c8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662cc : bv 32 := 0x00913423.
Lemma F_662cc : fetch_word Asan.M.loaded_segments (0x6631c : word) = Some W_662cc.
Proof. vm_refl. Qed.
Lemma D_662cc : decode_any W_662cc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662d0 : bv 32 := 0x01213023.
Lemma F_662d0 : fetch_word Asan.M.loaded_segments (0x66320 : word) = Some W_662d0.
Proof. vm_refl. Qed.
Lemma D_662d0 : decode_any W_662d0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662d4 : bv 32 := 0x02010413.
Lemma F_662d4 : fetch_word Asan.M.loaded_segments (0x66324 : word) = Some W_662d4.
Proof. vm_refl. Qed.
Lemma D_662d4 : decode_any W_662d4 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662d8 : bv 32 := 0x000fb517.
Lemma F_662d8 : fetch_word Asan.M.loaded_segments (0x66328 : word) = Some W_662d8.
Proof. vm_refl. Qed.
Lemma D_662d8 : decode_any W_662d8 = Some (Auipc 10 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662dc : bv 32 := 0x71050513.
Lemma F_662dc : fetch_word Asan.M.loaded_segments (0x6632c : word) = Some W_662dc.
Proof. vm_refl. Qed.
Lemma D_662dc : decode_any W_662dc = Some (OpImm ALU_ADD 10 10 1808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662e0 : bv 32 := 0x66c050ef.
Lemma F_662e0 : fetch_word Asan.M.loaded_segments (0x66330 : word) = Some W_662e0.
Proof. vm_refl. Qed.
Lemma D_662e0 : decode_any W_662e0 = Some (Jal 1 22124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662e4 : bv 32 := 0x00053483.
Lemma F_662e4 : fetch_word Asan.M.loaded_segments (0x66334 : word) = Some W_662e4.
Proof. vm_refl. Qed.
Lemma D_662e4 : decode_any W_662e4 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662e8 : bv 32 := 0x08048863.
Lemma F_662e8 : fetch_word Asan.M.loaded_segments (0x66338 : word) = Some W_662e8.
Proof. vm_refl. Qed.
Lemma D_662e8 : decode_any W_662e8 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662ec : bv 32 := 0x0604c503.
Lemma F_662ec : fetch_word Asan.M.loaded_segments (0x6633c : word) = Some W_662ec.
Proof. vm_refl. Qed.
Lemma D_662ec : decode_any W_662ec = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662f0 : bv 32 := 0x0584b903.
Lemma F_662f0 : fetch_word Asan.M.loaded_segments (0x66340 : word) = Some W_662f0.
Proof. vm_refl. Qed.
Lemma D_662f0 : decode_any W_662f0 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662f4 : bv 32 := 0x00050863.
Lemma F_662f4 : fetch_word Asan.M.loaded_segments (0x66344 : word) = Some W_662f4.
Proof. vm_refl. Qed.
Lemma D_662f4 : decode_any W_662f4 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662f8 : bv 32 := 0x00048513.
Lemma F_662f8 : fetch_word Asan.M.loaded_segments (0x66348 : word) = Some W_662f8.
Proof. vm_refl. Qed.
Lemma D_662f8 : decode_any W_662f8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_662fc : bv 32 := 0x00040593.
Lemma F_662fc : fetch_word Asan.M.loaded_segments (0x6634c : word) = Some W_662fc.
Proof. vm_refl. Qed.
Lemma D_662fc : decode_any W_662fc = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66300 : bv 32 := 0xed4ff0ef.
Lemma F_66300 : fetch_word Asan.M.loaded_segments (0x66350 : word) = Some W_66300.
Proof. vm_refl. Qed.
Lemma D_66300 : decode_any W_66300 = Some (Jal 1 2094804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66304 : bv 32 := 0xff790593.
Lemma F_66304 : fetch_word Asan.M.loaded_segments (0x66354 : word) = Some W_66304.
Proof. vm_refl. Qed.
Lemma D_66304 : decode_any W_66304 = Some (OpImm ALU_ADD 11 18 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66308 : bv 32 := 0x00100513.
Lemma F_66308 : fetch_word Asan.M.loaded_segments (0x66358 : word) = Some W_66308.
Proof. vm_refl. Qed.
Lemma D_66308 : decode_any W_66308 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6630c : bv 32 := 0x00b51533.
Lemma F_6630c : fetch_word Asan.M.loaded_segments (0x6635c : word) = Some W_6630c.
Proof. vm_refl. Qed.
Lemma D_6630c : decode_any W_6630c = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66310 : bv 32 := 0x0005061b.
Lemma F_66310 : fetch_word Asan.M.loaded_segments (0x66360 : word) = Some W_66310.
Proof. vm_refl. Qed.
Lemma D_66310 : decode_any W_66310 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66314 : bv 32 := 0x08c05263.
Lemma F_66314 : fetch_word Asan.M.loaded_segments (0x66364 : word) = Some W_66314.
Proof. vm_refl. Qed.
Lemma D_66314 : decode_any W_66314 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66318 : bv 32 := 0x000016b7.
Lemma F_66318 : fetch_word Asan.M.loaded_segments (0x66368 : word) = Some W_66318.
Proof. vm_refl. Qed.
Lemma D_66318 : decode_any W_66318 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6631c : bv 32 := 0xff190613.
Lemma F_6631c : fetch_word Asan.M.loaded_segments (0x6636c : word) = Some W_6631c.
Proof. vm_refl. Qed.
Lemma D_6631c : decode_any W_6631c = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66320 : bv 32 := 0x38000713.
Lemma F_66320 : fetch_word Asan.M.loaded_segments (0x66370 : word) = Some W_66320.
Proof. vm_refl. Qed.
Lemma D_66320 : decode_any W_66320 = Some (OpImm ALU_ADD 14 0 896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66324 : bv 32 := 0xfff00793.
Lemma F_66324 : fetch_word Asan.M.loaded_segments (0x66374 : word) = Some W_66324.
Proof. vm_refl. Qed.
Lemma D_66324 : decode_any W_66324 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66328 : bv 32 := 0x00c71733.
Lemma F_66328 : fetch_word Asan.M.loaded_segments (0x66378 : word) = Some W_66328.
Proof. vm_refl. Qed.
Lemma D_66328 : decode_any W_66328 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6632c : bv 32 := 0x0184b603.
Lemma F_6632c : fetch_word Asan.M.loaded_segments (0x6637c : word) = Some W_6632c.
Proof. vm_refl. Qed.
Lemma D_6632c : decode_any W_6632c = Some (Load SZ8 true 12 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66330 : bv 32 := 0x00b797b3.
Lemma F_66330 : fetch_word Asan.M.loaded_segments (0x66380 : word) = Some W_66330.
Proof. vm_refl. Qed.
Lemma D_66330 : decode_any W_66330 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66334 : bv 32 := 0xfff50813.
Lemma F_66334 : fetch_word Asan.M.loaded_segments (0x66384 : word) = Some W_66334.
Proof. vm_refl. Qed.
Lemma D_66334 : decode_any W_66334 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66338 : bv 32 := 0x00d485b3.
Lemma F_66338 : fetch_word Asan.M.loaded_segments (0x66388 : word) = Some W_66338.
Proof. vm_refl. Qed.
Lemma D_66338 : decode_any W_66338 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6633c : bv 32 := 0x00e586b3.
Lemma F_6633c : fetch_word Asan.M.loaded_segments (0x6638c : word) = Some W_6633c.
Proof. vm_refl. Qed.
Lemma D_6633c : decode_any W_6633c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66340 : bv 32 := 0xfff7c713.
Lemma F_66340 : fetch_word Asan.M.loaded_segments (0x66390 : word) = Some W_66340.
Proof. vm_refl. Qed.
Lemma D_66340 : decode_any W_66340 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66344 : bv 32 := 0x02081813.
Lemma F_66344 : fetch_word Asan.M.loaded_segments (0x66394 : word) = Some W_66344.
Proof. vm_refl. Qed.
Lemma D_66344 : decode_any W_66344 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66348 : bv 32 := 0x02085793.
Lemma F_66348 : fetch_word Asan.M.loaded_segments (0x66398 : word) = Some W_66348.
Proof. vm_refl. Qed.
Lemma D_66348 : decode_any W_66348 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6634c : bv 32 := 0x00f607b3.
Lemma F_6634c : fetch_word Asan.M.loaded_segments (0x6639c : word) = Some W_6634c.
Proof. vm_refl. Qed.
Lemma D_6634c : decode_any W_6634c = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66350 : bv 32 := 0x00178813.
Lemma F_66350 : fetch_word Asan.M.loaded_segments (0x663a0 : word) = Some W_66350.
Proof. vm_refl. Qed.
Lemma D_66350 : decode_any W_66350 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66354 : bv 32 := 0x00e678b3.
Lemma F_66354 : fetch_word Asan.M.loaded_segments (0x663a4 : word) = Some W_66354.
Proof. vm_refl. Qed.
Lemma D_66354 : decode_any W_66354 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66358 : bv 32 := 0x011687b3.
Lemma F_66358 : fetch_word Asan.M.loaded_segments (0x663a8 : word) = Some W_66358.
Proof. vm_refl. Qed.
Lemma D_66358 : decode_any W_66358 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6635c : bv 32 := 0x0007c283.
Lemma F_6635c : fetch_word Asan.M.loaded_segments (0x663ac : word) = Some W_6635c.
Proof. vm_refl. Qed.
Lemma D_6635c : decode_any W_6635c = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66360 : bv 32 := 0x06028663.
Lemma F_66360 : fetch_word Asan.M.loaded_segments (0x663b0 : word) = Some W_66360.
Proof. vm_refl. Qed.
Lemma D_66360 : decode_any W_66360 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66364 : bv 32 := 0xfff5051b.
Lemma F_66364 : fetch_word Asan.M.loaded_segments (0x663b4 : word) = Some W_66364.
Proof. vm_refl. Qed.
Lemma D_66364 : decode_any W_66364 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66368 : bv 32 := 0x00160613.
Lemma F_66368 : fetch_word Asan.M.loaded_segments (0x663b8 : word) = Some W_66368.
Proof. vm_refl. Qed.
Lemma D_66368 : decode_any W_66368 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6636c : bv 32 := 0xfe0514e3.
Lemma F_6636c : fetch_word Asan.M.loaded_segments (0x663bc : word) = Some W_6636c.
Proof. vm_refl. Qed.
Lemma D_6636c : decode_any W_6636c = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663cc : bv 32 := 0x00160613.
Lemma F_663cc : fetch_word Asan.M.loaded_segments (0x6641c : word) = Some W_663cc.
Proof. vm_refl. Qed.
Lemma D_663cc : decode_any W_663cc = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663d0 : bv 32 := 0x00100513.
Lemma F_663d0 : fetch_word Asan.M.loaded_segments (0x66420 : word) = Some W_663d0.
Proof. vm_refl. Qed.
Lemma D_663d0 : decode_any W_663d0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663d4 : bv 32 := 0xffb90693.
Lemma F_663d4 : fetch_word Asan.M.loaded_segments (0x66424 : word) = Some W_663d4.
Proof. vm_refl. Qed.
Lemma D_663d4 : decode_any W_663d4 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663d8 : bv 32 := 0x00c4bc23.
Lemma F_663d8 : fetch_word Asan.M.loaded_segments (0x66428 : word) = Some W_663d8.
Proof. vm_refl. Qed.
Lemma D_663d8 : decode_any W_663d8 = Some (Store SZ8 9 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663dc : bv 32 := 0x00a78023.
Lemma F_663dc : fetch_word Asan.M.loaded_segments (0x6642c : word) = Some W_663dc.
Proof. vm_refl. Qed.
Lemma D_663dc : decode_any W_663dc = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663e0 : bv 32 := 0x00d51533.
Lemma F_663e0 : fetch_word Asan.M.loaded_segments (0x66430 : word) = Some W_663e0.
Proof. vm_refl. Qed.
Lemma D_663e0 : decode_any W_663e0 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663e4 : bv 32 := 0x00300613.
Lemma F_663e4 : fetch_word Asan.M.loaded_segments (0x66434 : word) = Some W_663e4.
Proof. vm_refl. Qed.
Lemma D_663e4 : decode_any W_663e4 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663e8 : bv 32 := 0x00989893.
Lemma F_663e8 : fetch_word Asan.M.loaded_segments (0x66438 : word) = Some W_663e8.
Proof. vm_refl. Qed.
Lemma D_663e8 : decode_any W_663e8 = Some (ShiftImm ALU_SLL 17 17 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663ec : bv 32 := 0x01261633.
Lemma F_663ec : fetch_word Asan.M.loaded_segments (0x6643c : word) = Some W_663ec.
Proof. vm_refl. Qed.
Lemma D_663ec : decode_any W_663ec = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663f0 : bv 32 := 0x00a58533.
Lemma F_663f0 : fetch_word Asan.M.loaded_segments (0x66440 : word) = Some W_663f0.
Proof. vm_refl. Qed.
Lemma D_663f0 : decode_any W_663f0 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663f4 : bv 32 := 0x01160633.
Lemma F_663f4 : fetch_word Asan.M.loaded_segments (0x66444 : word) = Some W_663f4.
Proof. vm_refl. Qed.
Lemma D_663f4 : decode_any W_663f4 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663f8 : bv 32 := 0x00c504b3.
Lemma F_663f8 : fetch_word Asan.M.loaded_segments (0x66448 : word) = Some W_663f8.
Proof. vm_refl. Qed.
Lemma D_663f8 : decode_any W_663f8 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_663fc : bv 32 := 0x0084bc23.
Lemma F_663fc : fetch_word Asan.M.loaded_segments (0x6644c : word) = Some W_663fc.
Proof. vm_refl. Qed.
Lemma D_663fc : decode_any W_663fc = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66400 : bv 32 := 0x1ef4bc23.
Lemma F_66400 : fetch_word Asan.M.loaded_segments (0x66450 : word) = Some W_66400.
Proof. vm_refl. Qed.
Lemma D_66400 : decode_any W_66400 = Some (Store SZ8 9 15 504, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66404 : bv 32 := 0x00048513.
Lemma F_66404 : fetch_word Asan.M.loaded_segments (0x66454 : word) = Some W_66404.
Proof. vm_refl. Qed.
Lemma D_66404 : decode_any W_66404 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66408 : bv 32 := 0x4f0000ef.
Lemma F_66408 : fetch_word Asan.M.loaded_segments (0x66458 : word) = Some W_66408.
Proof. vm_refl. Qed.
Lemma D_66408 : decode_any W_66408 = Some (Jal 1 1264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6640c : bv 32 := 0x00050593.
Lemma F_6640c : fetch_word Asan.M.loaded_segments (0x6645c : word) = Some W_6640c.
Proof. vm_refl. Qed.
Lemma D_6640c : decode_any W_6640c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66410 : bv 32 := 0x00048513.
Lemma F_66410 : fetch_word Asan.M.loaded_segments (0x66460 : word) = Some W_66410.
Proof. vm_refl. Qed.
Lemma D_66410 : decode_any W_66410 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66414 : bv 32 := 0x00000613.
Lemma F_66414 : fetch_word Asan.M.loaded_segments (0x66464 : word) = Some W_66414.
Proof. vm_refl. Qed.
Lemma D_66414 : decode_any W_66414 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66418 : bv 32 := 0x0005b023.
Lemma F_66418 : fetch_word Asan.M.loaded_segments (0x66468 : word) = Some W_66418.
Proof. vm_refl. Qed.
Lemma D_66418 : decode_any W_66418 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6641c : bv 32 := 0x0005b423.
Lemma F_6641c : fetch_word Asan.M.loaded_segments (0x6646c : word) = Some W_6641c.
Proof. vm_refl. Qed.
Lemma D_6641c : decode_any W_6641c = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66420 : bv 32 := 0x0005b823.
Lemma F_66420 : fetch_word Asan.M.loaded_segments (0x66470 : word) = Some W_66420.
Proof. vm_refl. Qed.
Lemma D_66420 : decode_any W_66420 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66424 : bv 32 := 0x0005bc23.
Lemma F_66424 : fetch_word Asan.M.loaded_segments (0x66474 : word) = Some W_66424.
Proof. vm_refl. Qed.
Lemma D_66424 : decode_any W_66424 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66428 : bv 32 := 0x0205b023.
Lemma F_66428 : fetch_word Asan.M.loaded_segments (0x66478 : word) = Some W_66428.
Proof. vm_refl. Qed.
Lemma D_66428 : decode_any W_66428 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6642c : bv 32 := 0x0205b423.
Lemma F_6642c : fetch_word Asan.M.loaded_segments (0x6647c : word) = Some W_6642c.
Proof. vm_refl. Qed.
Lemma D_6642c : decode_any W_6642c = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66430 : bv 32 := 0x0205b823.
Lemma F_66430 : fetch_word Asan.M.loaded_segments (0x66480 : word) = Some W_66430.
Proof. vm_refl. Qed.
Lemma D_66430 : decode_any W_66430 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66434 : bv 32 := 0x0205bc23.
Lemma F_66434 : fetch_word Asan.M.loaded_segments (0x66484 : word) = Some W_66434.
Proof. vm_refl. Qed.
Lemma D_66434 : decode_any W_66434 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66438 : bv 32 := 0x01813083.
Lemma F_66438 : fetch_word Asan.M.loaded_segments (0x66488 : word) = Some W_66438.
Proof. vm_refl. Qed.
Lemma D_66438 : decode_any W_66438 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6643c : bv 32 := 0x01013403.
Lemma F_6643c : fetch_word Asan.M.loaded_segments (0x6648c : word) = Some W_6643c.
Proof. vm_refl. Qed.
Lemma D_6643c : decode_any W_6643c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66440 : bv 32 := 0x00813483.
Lemma F_66440 : fetch_word Asan.M.loaded_segments (0x66490 : word) = Some W_66440.
Proof. vm_refl. Qed.
Lemma D_66440 : decode_any W_66440 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66444 : bv 32 := 0x00013903.
Lemma F_66444 : fetch_word Asan.M.loaded_segments (0x66494 : word) = Some W_66444.
Proof. vm_refl. Qed.
Lemma D_66444 : decode_any W_66444 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66448 : bv 32 := 0x02010113.
Lemma F_66448 : fetch_word Asan.M.loaded_segments (0x66498 : word) = Some W_66448.
Proof. vm_refl. Qed.
Lemma D_66448 : decode_any W_66448 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6644c : bv 32 := 0x00008067.
Lemma F_6644c : fetch_word Asan.M.loaded_segments (0x6649c : word) = Some W_6644c.
Proof. vm_refl. Qed.
Lemma D_6644c : decode_any W_6644c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6646c : bv 32 := 0xfe010113.
Lemma F_6646c : fetch_word Asan.M.loaded_segments (0x664bc : word) = Some W_6646c.
Proof. vm_refl. Qed.
Lemma D_6646c : decode_any W_6646c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66470 : bv 32 := 0x00113c23.
Lemma F_66470 : fetch_word Asan.M.loaded_segments (0x664c0 : word) = Some W_66470.
Proof. vm_refl. Qed.
Lemma D_66470 : decode_any W_66470 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66474 : bv 32 := 0x00813823.
Lemma F_66474 : fetch_word Asan.M.loaded_segments (0x664c4 : word) = Some W_66474.
Proof. vm_refl. Qed.
Lemma D_66474 : decode_any W_66474 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66478 : bv 32 := 0x00913423.
Lemma F_66478 : fetch_word Asan.M.loaded_segments (0x664c8 : word) = Some W_66478.
Proof. vm_refl. Qed.
Lemma D_66478 : decode_any W_66478 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6647c : bv 32 := 0x01213023.
Lemma F_6647c : fetch_word Asan.M.loaded_segments (0x664cc : word) = Some W_6647c.
Proof. vm_refl. Qed.
Lemma D_6647c : decode_any W_6647c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66480 : bv 32 := 0x02010413.
Lemma F_66480 : fetch_word Asan.M.loaded_segments (0x664d0 : word) = Some W_66480.
Proof. vm_refl. Qed.
Lemma D_66480 : decode_any W_66480 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66484 : bv 32 := 0x000fb517.
Lemma F_66484 : fetch_word Asan.M.loaded_segments (0x664d4 : word) = Some W_66484.
Proof. vm_refl. Qed.
Lemma D_66484 : decode_any W_66484 = Some (Auipc 10 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66488 : bv 32 := 0x56450513.
Lemma F_66488 : fetch_word Asan.M.loaded_segments (0x664d8 : word) = Some W_66488.
Proof. vm_refl. Qed.
Lemma D_66488 : decode_any W_66488 = Some (OpImm ALU_ADD 10 10 1380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6648c : bv 32 := 0x4c0050ef.
Lemma F_6648c : fetch_word Asan.M.loaded_segments (0x664dc : word) = Some W_6648c.
Proof. vm_refl. Qed.
Lemma D_6648c : decode_any W_6648c = Some (Jal 1 21696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66490 : bv 32 := 0x00053483.
Lemma F_66490 : fetch_word Asan.M.loaded_segments (0x664e0 : word) = Some W_66490.
Proof. vm_refl. Qed.
Lemma D_66490 : decode_any W_66490 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66494 : bv 32 := 0x08048863.
Lemma F_66494 : fetch_word Asan.M.loaded_segments (0x664e4 : word) = Some W_66494.
Proof. vm_refl. Qed.
Lemma D_66494 : decode_any W_66494 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66498 : bv 32 := 0x0604c503.
Lemma F_66498 : fetch_word Asan.M.loaded_segments (0x664e8 : word) = Some W_66498.
Proof. vm_refl. Qed.
Lemma D_66498 : decode_any W_66498 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6649c : bv 32 := 0x0584b903.
Lemma F_6649c : fetch_word Asan.M.loaded_segments (0x664ec : word) = Some W_6649c.
Proof. vm_refl. Qed.
Lemma D_6649c : decode_any W_6649c = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664a0 : bv 32 := 0x00050863.
Lemma F_664a0 : fetch_word Asan.M.loaded_segments (0x664f0 : word) = Some W_664a0.
Proof. vm_refl. Qed.
Lemma D_664a0 : decode_any W_664a0 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664a4 : bv 32 := 0x00048513.
Lemma F_664a4 : fetch_word Asan.M.loaded_segments (0x664f4 : word) = Some W_664a4.
Proof. vm_refl. Qed.
Lemma D_664a4 : decode_any W_664a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664a8 : bv 32 := 0x00040593.
Lemma F_664a8 : fetch_word Asan.M.loaded_segments (0x664f8 : word) = Some W_664a8.
Proof. vm_refl. Qed.
Lemma D_664a8 : decode_any W_664a8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664ac : bv 32 := 0xd28ff0ef.
Lemma F_664ac : fetch_word Asan.M.loaded_segments (0x664fc : word) = Some W_664ac.
Proof. vm_refl. Qed.
Lemma D_664ac : decode_any W_664ac = Some (Jal 1 2094376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664b0 : bv 32 := 0xff690593.
Lemma F_664b0 : fetch_word Asan.M.loaded_segments (0x66500 : word) = Some W_664b0.
Proof. vm_refl. Qed.
Lemma D_664b0 : decode_any W_664b0 = Some (OpImm ALU_ADD 11 18 4086, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664b4 : bv 32 := 0x00100513.
Lemma F_664b4 : fetch_word Asan.M.loaded_segments (0x66504 : word) = Some W_664b4.
Proof. vm_refl. Qed.
Lemma D_664b4 : decode_any W_664b4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664b8 : bv 32 := 0x00b51533.
Lemma F_664b8 : fetch_word Asan.M.loaded_segments (0x66508 : word) = Some W_664b8.
Proof. vm_refl. Qed.
Lemma D_664b8 : decode_any W_664b8 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664bc : bv 32 := 0x0005061b.
Lemma F_664bc : fetch_word Asan.M.loaded_segments (0x6650c : word) = Some W_664bc.
Proof. vm_refl. Qed.
Lemma D_664bc : decode_any W_664bc = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664c0 : bv 32 := 0x08c05263.
Lemma F_664c0 : fetch_word Asan.M.loaded_segments (0x66510 : word) = Some W_664c0.
Proof. vm_refl. Qed.
Lemma D_664c0 : decode_any W_664c0 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664c4 : bv 32 := 0x000016b7.
Lemma F_664c4 : fetch_word Asan.M.loaded_segments (0x66514 : word) = Some W_664c4.
Proof. vm_refl. Qed.
Lemma D_664c4 : decode_any W_664c4 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664c8 : bv 32 := 0xff190613.
Lemma F_664c8 : fetch_word Asan.M.loaded_segments (0x66518 : word) = Some W_664c8.
Proof. vm_refl. Qed.
Lemma D_664c8 : decode_any W_664c8 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664cc : bv 32 := 0x3c000713.
Lemma F_664cc : fetch_word Asan.M.loaded_segments (0x6651c : word) = Some W_664cc.
Proof. vm_refl. Qed.
Lemma D_664cc : decode_any W_664cc = Some (OpImm ALU_ADD 14 0 960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664d0 : bv 32 := 0xfff00793.
Lemma F_664d0 : fetch_word Asan.M.loaded_segments (0x66520 : word) = Some W_664d0.
Proof. vm_refl. Qed.
Lemma D_664d0 : decode_any W_664d0 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664d4 : bv 32 := 0x00c71733.
Lemma F_664d4 : fetch_word Asan.M.loaded_segments (0x66524 : word) = Some W_664d4.
Proof. vm_refl. Qed.
Lemma D_664d4 : decode_any W_664d4 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664d8 : bv 32 := 0x0204b603.
Lemma F_664d8 : fetch_word Asan.M.loaded_segments (0x66528 : word) = Some W_664d8.
Proof. vm_refl. Qed.
Lemma D_664d8 : decode_any W_664d8 = Some (Load SZ8 true 12 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664dc : bv 32 := 0x00b797b3.
Lemma F_664dc : fetch_word Asan.M.loaded_segments (0x6652c : word) = Some W_664dc.
Proof. vm_refl. Qed.
Lemma D_664dc : decode_any W_664dc = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664e0 : bv 32 := 0xfff50813.
Lemma F_664e0 : fetch_word Asan.M.loaded_segments (0x66530 : word) = Some W_664e0.
Proof. vm_refl. Qed.
Lemma D_664e0 : decode_any W_664e0 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664e4 : bv 32 := 0x00d485b3.
Lemma F_664e4 : fetch_word Asan.M.loaded_segments (0x66534 : word) = Some W_664e4.
Proof. vm_refl. Qed.
Lemma D_664e4 : decode_any W_664e4 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664e8 : bv 32 := 0x00e586b3.
Lemma F_664e8 : fetch_word Asan.M.loaded_segments (0x66538 : word) = Some W_664e8.
Proof. vm_refl. Qed.
Lemma D_664e8 : decode_any W_664e8 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664ec : bv 32 := 0xfff7c713.
Lemma F_664ec : fetch_word Asan.M.loaded_segments (0x6653c : word) = Some W_664ec.
Proof. vm_refl. Qed.
Lemma D_664ec : decode_any W_664ec = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664f0 : bv 32 := 0x02081813.
Lemma F_664f0 : fetch_word Asan.M.loaded_segments (0x66540 : word) = Some W_664f0.
Proof. vm_refl. Qed.
Lemma D_664f0 : decode_any W_664f0 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664f4 : bv 32 := 0x02085793.
Lemma F_664f4 : fetch_word Asan.M.loaded_segments (0x66544 : word) = Some W_664f4.
Proof. vm_refl. Qed.
Lemma D_664f4 : decode_any W_664f4 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664f8 : bv 32 := 0x00f607b3.
Lemma F_664f8 : fetch_word Asan.M.loaded_segments (0x66548 : word) = Some W_664f8.
Proof. vm_refl. Qed.
Lemma D_664f8 : decode_any W_664f8 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_664fc : bv 32 := 0x00178813.
Lemma F_664fc : fetch_word Asan.M.loaded_segments (0x6654c : word) = Some W_664fc.
Proof. vm_refl. Qed.
Lemma D_664fc : decode_any W_664fc = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66500 : bv 32 := 0x00e678b3.
Lemma F_66500 : fetch_word Asan.M.loaded_segments (0x66550 : word) = Some W_66500.
Proof. vm_refl. Qed.
Lemma D_66500 : decode_any W_66500 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66504 : bv 32 := 0x011687b3.
Lemma F_66504 : fetch_word Asan.M.loaded_segments (0x66554 : word) = Some W_66504.
Proof. vm_refl. Qed.
Lemma D_66504 : decode_any W_66504 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66508 : bv 32 := 0x0007c283.
Lemma F_66508 : fetch_word Asan.M.loaded_segments (0x66558 : word) = Some W_66508.
Proof. vm_refl. Qed.
Lemma D_66508 : decode_any W_66508 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6650c : bv 32 := 0x06028663.
Lemma F_6650c : fetch_word Asan.M.loaded_segments (0x6655c : word) = Some W_6650c.
Proof. vm_refl. Qed.
Lemma D_6650c : decode_any W_6650c = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66510 : bv 32 := 0xfff5051b.
Lemma F_66510 : fetch_word Asan.M.loaded_segments (0x66560 : word) = Some W_66510.
Proof. vm_refl. Qed.
Lemma D_66510 : decode_any W_66510 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66514 : bv 32 := 0x00160613.
Lemma F_66514 : fetch_word Asan.M.loaded_segments (0x66564 : word) = Some W_66514.
Proof. vm_refl. Qed.
Lemma D_66514 : decode_any W_66514 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66518 : bv 32 := 0xfe0514e3.
Lemma F_66518 : fetch_word Asan.M.loaded_segments (0x66568 : word) = Some W_66518.
Proof. vm_refl. Qed.
Lemma D_66518 : decode_any W_66518 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66578 : bv 32 := 0x00160613.
Lemma F_66578 : fetch_word Asan.M.loaded_segments (0x665c8 : word) = Some W_66578.
Proof. vm_refl. Qed.
Lemma D_66578 : decode_any W_66578 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6657c : bv 32 := 0x00100513.
Lemma F_6657c : fetch_word Asan.M.loaded_segments (0x665cc : word) = Some W_6657c.
Proof. vm_refl. Qed.
Lemma D_6657c : decode_any W_6657c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66580 : bv 32 := 0xffb90693.
Lemma F_66580 : fetch_word Asan.M.loaded_segments (0x665d0 : word) = Some W_66580.
Proof. vm_refl. Qed.
Lemma D_66580 : decode_any W_66580 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66584 : bv 32 := 0x02c4b023.
Lemma F_66584 : fetch_word Asan.M.loaded_segments (0x665d4 : word) = Some W_66584.
Proof. vm_refl. Qed.
Lemma D_66584 : decode_any W_66584 = Some (Store SZ8 9 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66588 : bv 32 := 0x00a78023.
Lemma F_66588 : fetch_word Asan.M.loaded_segments (0x665d8 : word) = Some W_66588.
Proof. vm_refl. Qed.
Lemma D_66588 : decode_any W_66588 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6658c : bv 32 := 0x00d51533.
Lemma F_6658c : fetch_word Asan.M.loaded_segments (0x665dc : word) = Some W_6658c.
Proof. vm_refl. Qed.
Lemma D_6658c : decode_any W_6658c = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66590 : bv 32 := 0x00400613.
Lemma F_66590 : fetch_word Asan.M.loaded_segments (0x665e0 : word) = Some W_66590.
Proof. vm_refl. Qed.
Lemma D_66590 : decode_any W_66590 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66594 : bv 32 := 0x00a89893.
Lemma F_66594 : fetch_word Asan.M.loaded_segments (0x665e4 : word) = Some W_66594.
Proof. vm_refl. Qed.
Lemma D_66594 : decode_any W_66594 = Some (ShiftImm ALU_SLL 17 17 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66598 : bv 32 := 0x01261633.
Lemma F_66598 : fetch_word Asan.M.loaded_segments (0x665e8 : word) = Some W_66598.
Proof. vm_refl. Qed.
Lemma D_66598 : decode_any W_66598 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6659c : bv 32 := 0x00a58533.
Lemma F_6659c : fetch_word Asan.M.loaded_segments (0x665ec : word) = Some W_6659c.
Proof. vm_refl. Qed.
Lemma D_6659c : decode_any W_6659c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665a0 : bv 32 := 0x01160633.
Lemma F_665a0 : fetch_word Asan.M.loaded_segments (0x665f0 : word) = Some W_665a0.
Proof. vm_refl. Qed.
Lemma D_665a0 : decode_any W_665a0 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665a4 : bv 32 := 0x00c504b3.
Lemma F_665a4 : fetch_word Asan.M.loaded_segments (0x665f4 : word) = Some W_665a4.
Proof. vm_refl. Qed.
Lemma D_665a4 : decode_any W_665a4 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665a8 : bv 32 := 0x0084bc23.
Lemma F_665a8 : fetch_word Asan.M.loaded_segments (0x665f8 : word) = Some W_665a8.
Proof. vm_refl. Qed.
Lemma D_665a8 : decode_any W_665a8 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665ac : bv 32 := 0x3ef4bc23.
Lemma F_665ac : fetch_word Asan.M.loaded_segments (0x665fc : word) = Some W_665ac.
Proof. vm_refl. Qed.
Lemma D_665ac : decode_any W_665ac = Some (Store SZ8 9 15 1016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665b0 : bv 32 := 0x00048513.
Lemma F_665b0 : fetch_word Asan.M.loaded_segments (0x66600 : word) = Some W_665b0.
Proof. vm_refl. Qed.
Lemma D_665b0 : decode_any W_665b0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665b4 : bv 32 := 0x344000ef.
Lemma F_665b4 : fetch_word Asan.M.loaded_segments (0x66604 : word) = Some W_665b4.
Proof. vm_refl. Qed.
Lemma D_665b4 : decode_any W_665b4 = Some (Jal 1 836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665b8 : bv 32 := 0x00050593.
Lemma F_665b8 : fetch_word Asan.M.loaded_segments (0x66608 : word) = Some W_665b8.
Proof. vm_refl. Qed.
Lemma D_665b8 : decode_any W_665b8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665bc : bv 32 := 0x00048513.
Lemma F_665bc : fetch_word Asan.M.loaded_segments (0x6660c : word) = Some W_665bc.
Proof. vm_refl. Qed.
Lemma D_665bc : decode_any W_665bc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665c0 : bv 32 := 0x00000613.
Lemma F_665c0 : fetch_word Asan.M.loaded_segments (0x66610 : word) = Some W_665c0.
Proof. vm_refl. Qed.
Lemma D_665c0 : decode_any W_665c0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665c4 : bv 32 := 0x0005b023.
Lemma F_665c4 : fetch_word Asan.M.loaded_segments (0x66614 : word) = Some W_665c4.
Proof. vm_refl. Qed.
Lemma D_665c4 : decode_any W_665c4 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665c8 : bv 32 := 0x0005b423.
Lemma F_665c8 : fetch_word Asan.M.loaded_segments (0x66618 : word) = Some W_665c8.
Proof. vm_refl. Qed.
Lemma D_665c8 : decode_any W_665c8 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665cc : bv 32 := 0x0005b823.
Lemma F_665cc : fetch_word Asan.M.loaded_segments (0x6661c : word) = Some W_665cc.
Proof. vm_refl. Qed.
Lemma D_665cc : decode_any W_665cc = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665d0 : bv 32 := 0x0005bc23.
Lemma F_665d0 : fetch_word Asan.M.loaded_segments (0x66620 : word) = Some W_665d0.
Proof. vm_refl. Qed.
Lemma D_665d0 : decode_any W_665d0 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665d4 : bv 32 := 0x0205b023.
Lemma F_665d4 : fetch_word Asan.M.loaded_segments (0x66624 : word) = Some W_665d4.
Proof. vm_refl. Qed.
Lemma D_665d4 : decode_any W_665d4 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665d8 : bv 32 := 0x0205b423.
Lemma F_665d8 : fetch_word Asan.M.loaded_segments (0x66628 : word) = Some W_665d8.
Proof. vm_refl. Qed.
Lemma D_665d8 : decode_any W_665d8 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665dc : bv 32 := 0x0205b823.
Lemma F_665dc : fetch_word Asan.M.loaded_segments (0x6662c : word) = Some W_665dc.
Proof. vm_refl. Qed.
Lemma D_665dc : decode_any W_665dc = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665e0 : bv 32 := 0x0205bc23.
Lemma F_665e0 : fetch_word Asan.M.loaded_segments (0x66630 : word) = Some W_665e0.
Proof. vm_refl. Qed.
Lemma D_665e0 : decode_any W_665e0 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665e4 : bv 32 := 0x0405b023.
Lemma F_665e4 : fetch_word Asan.M.loaded_segments (0x66634 : word) = Some W_665e4.
Proof. vm_refl. Qed.
Lemma D_665e4 : decode_any W_665e4 = Some (Store SZ8 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665e8 : bv 32 := 0x0405b423.
Lemma F_665e8 : fetch_word Asan.M.loaded_segments (0x66638 : word) = Some W_665e8.
Proof. vm_refl. Qed.
Lemma D_665e8 : decode_any W_665e8 = Some (Store SZ8 11 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665ec : bv 32 := 0x0405b823.
Lemma F_665ec : fetch_word Asan.M.loaded_segments (0x6663c : word) = Some W_665ec.
Proof. vm_refl. Qed.
Lemma D_665ec : decode_any W_665ec = Some (Store SZ8 11 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665f0 : bv 32 := 0x0405bc23.
Lemma F_665f0 : fetch_word Asan.M.loaded_segments (0x66640 : word) = Some W_665f0.
Proof. vm_refl. Qed.
Lemma D_665f0 : decode_any W_665f0 = Some (Store SZ8 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665f4 : bv 32 := 0x0605b023.
Lemma F_665f4 : fetch_word Asan.M.loaded_segments (0x66644 : word) = Some W_665f4.
Proof. vm_refl. Qed.
Lemma D_665f4 : decode_any W_665f4 = Some (Store SZ8 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665f8 : bv 32 := 0x0605b423.
Lemma F_665f8 : fetch_word Asan.M.loaded_segments (0x66648 : word) = Some W_665f8.
Proof. vm_refl. Qed.
Lemma D_665f8 : decode_any W_665f8 = Some (Store SZ8 11 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_665fc : bv 32 := 0x0605b823.
Lemma F_665fc : fetch_word Asan.M.loaded_segments (0x6664c : word) = Some W_665fc.
Proof. vm_refl. Qed.
Lemma D_665fc : decode_any W_665fc = Some (Store SZ8 11 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66600 : bv 32 := 0x0605bc23.
Lemma F_66600 : fetch_word Asan.M.loaded_segments (0x66650 : word) = Some W_66600.
Proof. vm_refl. Qed.
Lemma D_66600 : decode_any W_66600 = Some (Store SZ8 11 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66604 : bv 32 := 0x01813083.
Lemma F_66604 : fetch_word Asan.M.loaded_segments (0x66654 : word) = Some W_66604.
Proof. vm_refl. Qed.
Lemma D_66604 : decode_any W_66604 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66608 : bv 32 := 0x01013403.
Lemma F_66608 : fetch_word Asan.M.loaded_segments (0x66658 : word) = Some W_66608.
Proof. vm_refl. Qed.
Lemma D_66608 : decode_any W_66608 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6660c : bv 32 := 0x00813483.
Lemma F_6660c : fetch_word Asan.M.loaded_segments (0x6665c : word) = Some W_6660c.
Proof. vm_refl. Qed.
Lemma D_6660c : decode_any W_6660c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66610 : bv 32 := 0x00013903.
Lemma F_66610 : fetch_word Asan.M.loaded_segments (0x66660 : word) = Some W_66610.
Proof. vm_refl. Qed.
Lemma D_66610 : decode_any W_66610 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66614 : bv 32 := 0x02010113.
Lemma F_66614 : fetch_word Asan.M.loaded_segments (0x66664 : word) = Some W_66614.
Proof. vm_refl. Qed.
Lemma D_66614 : decode_any W_66614 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66618 : bv 32 := 0x00008067.
Lemma F_66618 : fetch_word Asan.M.loaded_segments (0x66668 : word) = Some W_66618.
Proof. vm_refl. Qed.
Lemma D_66618 : decode_any W_66618 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66638 : bv 32 := 0xfe010113.
Lemma F_66638 : fetch_word Asan.M.loaded_segments (0x66688 : word) = Some W_66638.
Proof. vm_refl. Qed.
Lemma D_66638 : decode_any W_66638 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6663c : bv 32 := 0x00113c23.
Lemma F_6663c : fetch_word Asan.M.loaded_segments (0x6668c : word) = Some W_6663c.
Proof. vm_refl. Qed.
Lemma D_6663c : decode_any W_6663c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66640 : bv 32 := 0x00813823.
Lemma F_66640 : fetch_word Asan.M.loaded_segments (0x66690 : word) = Some W_66640.
Proof. vm_refl. Qed.
Lemma D_66640 : decode_any W_66640 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66644 : bv 32 := 0x00913423.
Lemma F_66644 : fetch_word Asan.M.loaded_segments (0x66694 : word) = Some W_66644.
Proof. vm_refl. Qed.
Lemma D_66644 : decode_any W_66644 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66648 : bv 32 := 0x01213023.
Lemma F_66648 : fetch_word Asan.M.loaded_segments (0x66698 : word) = Some W_66648.
Proof. vm_refl. Qed.
Lemma D_66648 : decode_any W_66648 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6664c : bv 32 := 0x02010413.
Lemma F_6664c : fetch_word Asan.M.loaded_segments (0x6669c : word) = Some W_6664c.
Proof. vm_refl. Qed.
Lemma D_6664c : decode_any W_6664c = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66650 : bv 32 := 0x000fb517.
Lemma F_66650 : fetch_word Asan.M.loaded_segments (0x666a0 : word) = Some W_66650.
Proof. vm_refl. Qed.
Lemma D_66650 : decode_any W_66650 = Some (Auipc 10 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66654 : bv 32 := 0x39850513.
Lemma F_66654 : fetch_word Asan.M.loaded_segments (0x666a4 : word) = Some W_66654.
Proof. vm_refl. Qed.
Lemma D_66654 : decode_any W_66654 = Some (OpImm ALU_ADD 10 10 920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66658 : bv 32 := 0x2f4050ef.
Lemma F_66658 : fetch_word Asan.M.loaded_segments (0x666a8 : word) = Some W_66658.
Proof. vm_refl. Qed.
Lemma D_66658 : decode_any W_66658 = Some (Jal 1 21236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6665c : bv 32 := 0x00053483.
Lemma F_6665c : fetch_word Asan.M.loaded_segments (0x666ac : word) = Some W_6665c.
Proof. vm_refl. Qed.
Lemma D_6665c : decode_any W_6665c = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66660 : bv 32 := 0x08048863.
Lemma F_66660 : fetch_word Asan.M.loaded_segments (0x666b0 : word) = Some W_66660.
Proof. vm_refl. Qed.
Lemma D_66660 : decode_any W_66660 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66664 : bv 32 := 0x0604c503.
Lemma F_66664 : fetch_word Asan.M.loaded_segments (0x666b4 : word) = Some W_66664.
Proof. vm_refl. Qed.
Lemma D_66664 : decode_any W_66664 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66668 : bv 32 := 0x0584b903.
Lemma F_66668 : fetch_word Asan.M.loaded_segments (0x666b8 : word) = Some W_66668.
Proof. vm_refl. Qed.
Lemma D_66668 : decode_any W_66668 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6666c : bv 32 := 0x00050863.
Lemma F_6666c : fetch_word Asan.M.loaded_segments (0x666bc : word) = Some W_6666c.
Proof. vm_refl. Qed.
Lemma D_6666c : decode_any W_6666c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66670 : bv 32 := 0x00048513.
Lemma F_66670 : fetch_word Asan.M.loaded_segments (0x666c0 : word) = Some W_66670.
Proof. vm_refl. Qed.
Lemma D_66670 : decode_any W_66670 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66674 : bv 32 := 0x00040593.
Lemma F_66674 : fetch_word Asan.M.loaded_segments (0x666c4 : word) = Some W_66674.
Proof. vm_refl. Qed.
Lemma D_66674 : decode_any W_66674 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66678 : bv 32 := 0xb5cff0ef.
Lemma F_66678 : fetch_word Asan.M.loaded_segments (0x666c8 : word) = Some W_66678.
Proof. vm_refl. Qed.
Lemma D_66678 : decode_any W_66678 = Some (Jal 1 2093916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6667c : bv 32 := 0xff590593.
Lemma F_6667c : fetch_word Asan.M.loaded_segments (0x666cc : word) = Some W_6667c.
Proof. vm_refl. Qed.
Lemma D_6667c : decode_any W_6667c = Some (OpImm ALU_ADD 11 18 4085, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66680 : bv 32 := 0x00100513.
Lemma F_66680 : fetch_word Asan.M.loaded_segments (0x666d0 : word) = Some W_66680.
Proof. vm_refl. Qed.
Lemma D_66680 : decode_any W_66680 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66684 : bv 32 := 0x00b51533.
Lemma F_66684 : fetch_word Asan.M.loaded_segments (0x666d4 : word) = Some W_66684.
Proof. vm_refl. Qed.
Lemma D_66684 : decode_any W_66684 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66688 : bv 32 := 0x0005061b.
Lemma F_66688 : fetch_word Asan.M.loaded_segments (0x666d8 : word) = Some W_66688.
Proof. vm_refl. Qed.
Lemma D_66688 : decode_any W_66688 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6668c : bv 32 := 0x08c05263.
Lemma F_6668c : fetch_word Asan.M.loaded_segments (0x666dc : word) = Some W_6668c.
Proof. vm_refl. Qed.
Lemma D_6668c : decode_any W_6668c = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66690 : bv 32 := 0x000016b7.
Lemma F_66690 : fetch_word Asan.M.loaded_segments (0x666e0 : word) = Some W_66690.
Proof. vm_refl. Qed.
Lemma D_66690 : decode_any W_66690 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66694 : bv 32 := 0xff190613.
Lemma F_66694 : fetch_word Asan.M.loaded_segments (0x666e4 : word) = Some W_66694.
Proof. vm_refl. Qed.
Lemma D_66694 : decode_any W_66694 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66698 : bv 32 := 0x3e000713.
Lemma F_66698 : fetch_word Asan.M.loaded_segments (0x666e8 : word) = Some W_66698.
Proof. vm_refl. Qed.
Lemma D_66698 : decode_any W_66698 = Some (OpImm ALU_ADD 14 0 992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6669c : bv 32 := 0xfff00793.
Lemma F_6669c : fetch_word Asan.M.loaded_segments (0x666ec : word) = Some W_6669c.
Proof. vm_refl. Qed.
Lemma D_6669c : decode_any W_6669c = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666a0 : bv 32 := 0x00c71733.
Lemma F_666a0 : fetch_word Asan.M.loaded_segments (0x666f0 : word) = Some W_666a0.
Proof. vm_refl. Qed.
Lemma D_666a0 : decode_any W_666a0 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666a4 : bv 32 := 0x0284b603.
Lemma F_666a4 : fetch_word Asan.M.loaded_segments (0x666f4 : word) = Some W_666a4.
Proof. vm_refl. Qed.
Lemma D_666a4 : decode_any W_666a4 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666a8 : bv 32 := 0x00b797b3.
Lemma F_666a8 : fetch_word Asan.M.loaded_segments (0x666f8 : word) = Some W_666a8.
Proof. vm_refl. Qed.
Lemma D_666a8 : decode_any W_666a8 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666ac : bv 32 := 0xfff50813.
Lemma F_666ac : fetch_word Asan.M.loaded_segments (0x666fc : word) = Some W_666ac.
Proof. vm_refl. Qed.
Lemma D_666ac : decode_any W_666ac = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666b0 : bv 32 := 0x00d485b3.
Lemma F_666b0 : fetch_word Asan.M.loaded_segments (0x66700 : word) = Some W_666b0.
Proof. vm_refl. Qed.
Lemma D_666b0 : decode_any W_666b0 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666b4 : bv 32 := 0x00e586b3.
Lemma F_666b4 : fetch_word Asan.M.loaded_segments (0x66704 : word) = Some W_666b4.
Proof. vm_refl. Qed.
Lemma D_666b4 : decode_any W_666b4 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666b8 : bv 32 := 0xfff7c713.
Lemma F_666b8 : fetch_word Asan.M.loaded_segments (0x66708 : word) = Some W_666b8.
Proof. vm_refl. Qed.
Lemma D_666b8 : decode_any W_666b8 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666bc : bv 32 := 0x02081813.
Lemma F_666bc : fetch_word Asan.M.loaded_segments (0x6670c : word) = Some W_666bc.
Proof. vm_refl. Qed.
Lemma D_666bc : decode_any W_666bc = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666c0 : bv 32 := 0x02085793.
Lemma F_666c0 : fetch_word Asan.M.loaded_segments (0x66710 : word) = Some W_666c0.
Proof. vm_refl. Qed.
Lemma D_666c0 : decode_any W_666c0 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666c4 : bv 32 := 0x00f607b3.
Lemma F_666c4 : fetch_word Asan.M.loaded_segments (0x66714 : word) = Some W_666c4.
Proof. vm_refl. Qed.
Lemma D_666c4 : decode_any W_666c4 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666c8 : bv 32 := 0x00178813.
Lemma F_666c8 : fetch_word Asan.M.loaded_segments (0x66718 : word) = Some W_666c8.
Proof. vm_refl. Qed.
Lemma D_666c8 : decode_any W_666c8 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666cc : bv 32 := 0x00e678b3.
Lemma F_666cc : fetch_word Asan.M.loaded_segments (0x6671c : word) = Some W_666cc.
Proof. vm_refl. Qed.
Lemma D_666cc : decode_any W_666cc = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666d0 : bv 32 := 0x011687b3.
Lemma F_666d0 : fetch_word Asan.M.loaded_segments (0x66720 : word) = Some W_666d0.
Proof. vm_refl. Qed.
Lemma D_666d0 : decode_any W_666d0 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666d4 : bv 32 := 0x0007c283.
Lemma F_666d4 : fetch_word Asan.M.loaded_segments (0x66724 : word) = Some W_666d4.
Proof. vm_refl. Qed.
Lemma D_666d4 : decode_any W_666d4 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666d8 : bv 32 := 0x06028663.
Lemma F_666d8 : fetch_word Asan.M.loaded_segments (0x66728 : word) = Some W_666d8.
Proof. vm_refl. Qed.
Lemma D_666d8 : decode_any W_666d8 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666dc : bv 32 := 0xfff5051b.
Lemma F_666dc : fetch_word Asan.M.loaded_segments (0x6672c : word) = Some W_666dc.
Proof. vm_refl. Qed.
Lemma D_666dc : decode_any W_666dc = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666e0 : bv 32 := 0x00160613.
Lemma F_666e0 : fetch_word Asan.M.loaded_segments (0x66730 : word) = Some W_666e0.
Proof. vm_refl. Qed.
Lemma D_666e0 : decode_any W_666e0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_666e4 : bv 32 := 0xfe0514e3.
Lemma F_666e4 : fetch_word Asan.M.loaded_segments (0x66734 : word) = Some W_666e4.
Proof. vm_refl. Qed.
Lemma D_666e4 : decode_any W_666e4 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66744 : bv 32 := 0x00160613.
Lemma F_66744 : fetch_word Asan.M.loaded_segments (0x66794 : word) = Some W_66744.
Proof. vm_refl. Qed.
Lemma D_66744 : decode_any W_66744 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66748 : bv 32 := 0x00100513.
Lemma F_66748 : fetch_word Asan.M.loaded_segments (0x66798 : word) = Some W_66748.
Proof. vm_refl. Qed.
Lemma D_66748 : decode_any W_66748 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6674c : bv 32 := 0xffb90693.
Lemma F_6674c : fetch_word Asan.M.loaded_segments (0x6679c : word) = Some W_6674c.
Proof. vm_refl. Qed.
Lemma D_6674c : decode_any W_6674c = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66750 : bv 32 := 0x02c4b423.
Lemma F_66750 : fetch_word Asan.M.loaded_segments (0x667a0 : word) = Some W_66750.
Proof. vm_refl. Qed.
Lemma D_66750 : decode_any W_66750 = Some (Store SZ8 9 12 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66754 : bv 32 := 0x00a78023.
Lemma F_66754 : fetch_word Asan.M.loaded_segments (0x667a4 : word) = Some W_66754.
Proof. vm_refl. Qed.
Lemma D_66754 : decode_any W_66754 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66758 : bv 32 := 0x00d51533.
Lemma F_66758 : fetch_word Asan.M.loaded_segments (0x667a8 : word) = Some W_66758.
Proof. vm_refl. Qed.
Lemma D_66758 : decode_any W_66758 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6675c : bv 32 := 0x00500613.
Lemma F_6675c : fetch_word Asan.M.loaded_segments (0x667ac : word) = Some W_6675c.
Proof. vm_refl. Qed.
Lemma D_6675c : decode_any W_6675c = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66760 : bv 32 := 0x00b89893.
Lemma F_66760 : fetch_word Asan.M.loaded_segments (0x667b0 : word) = Some W_66760.
Proof. vm_refl. Qed.
Lemma D_66760 : decode_any W_66760 = Some (ShiftImm ALU_SLL 17 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66764 : bv 32 := 0x01261633.
Lemma F_66764 : fetch_word Asan.M.loaded_segments (0x667b4 : word) = Some W_66764.
Proof. vm_refl. Qed.
Lemma D_66764 : decode_any W_66764 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66768 : bv 32 := 0x00a58533.
Lemma F_66768 : fetch_word Asan.M.loaded_segments (0x667b8 : word) = Some W_66768.
Proof. vm_refl. Qed.
Lemma D_66768 : decode_any W_66768 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6676c : bv 32 := 0x01160633.
Lemma F_6676c : fetch_word Asan.M.loaded_segments (0x667bc : word) = Some W_6676c.
Proof. vm_refl. Qed.
Lemma D_6676c : decode_any W_6676c = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66770 : bv 32 := 0x00c504b3.
Lemma F_66770 : fetch_word Asan.M.loaded_segments (0x667c0 : word) = Some W_66770.
Proof. vm_refl. Qed.
Lemma D_66770 : decode_any W_66770 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66774 : bv 32 := 0x0084bc23.
Lemma F_66774 : fetch_word Asan.M.loaded_segments (0x667c4 : word) = Some W_66774.
Proof. vm_refl. Qed.
Lemma D_66774 : decode_any W_66774 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66778 : bv 32 := 0x7ef4bc23.
Lemma F_66778 : fetch_word Asan.M.loaded_segments (0x667c8 : word) = Some W_66778.
Proof. vm_refl. Qed.
Lemma D_66778 : decode_any W_66778 = Some (Store SZ8 9 15 2040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6677c : bv 32 := 0x00048513.
Lemma F_6677c : fetch_word Asan.M.loaded_segments (0x667cc : word) = Some W_6677c.
Proof. vm_refl. Qed.
Lemma D_6677c : decode_any W_6677c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66780 : bv 32 := 0x178000ef.
Lemma F_66780 : fetch_word Asan.M.loaded_segments (0x667d0 : word) = Some W_66780.
Proof. vm_refl. Qed.
Lemma D_66780 : decode_any W_66780 = Some (Jal 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66784 : bv 32 := 0x00050593.
Lemma F_66784 : fetch_word Asan.M.loaded_segments (0x667d4 : word) = Some W_66784.
Proof. vm_refl. Qed.
Lemma D_66784 : decode_any W_66784 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66788 : bv 32 := 0x00048513.
Lemma F_66788 : fetch_word Asan.M.loaded_segments (0x667d8 : word) = Some W_66788.
Proof. vm_refl. Qed.
Lemma D_66788 : decode_any W_66788 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6678c : bv 32 := 0x00000613.
Lemma F_6678c : fetch_word Asan.M.loaded_segments (0x667dc : word) = Some W_6678c.
Proof. vm_refl. Qed.
Lemma D_6678c : decode_any W_6678c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66790 : bv 32 := 0x0005b023.
Lemma F_66790 : fetch_word Asan.M.loaded_segments (0x667e0 : word) = Some W_66790.
Proof. vm_refl. Qed.
Lemma D_66790 : decode_any W_66790 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66794 : bv 32 := 0x0005b423.
Lemma F_66794 : fetch_word Asan.M.loaded_segments (0x667e4 : word) = Some W_66794.
Proof. vm_refl. Qed.
Lemma D_66794 : decode_any W_66794 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66798 : bv 32 := 0x0005b823.
Lemma F_66798 : fetch_word Asan.M.loaded_segments (0x667e8 : word) = Some W_66798.
Proof. vm_refl. Qed.
Lemma D_66798 : decode_any W_66798 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6679c : bv 32 := 0x0005bc23.
Lemma F_6679c : fetch_word Asan.M.loaded_segments (0x667ec : word) = Some W_6679c.
Proof. vm_refl. Qed.
Lemma D_6679c : decode_any W_6679c = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667a0 : bv 32 := 0x0205b023.
Lemma F_667a0 : fetch_word Asan.M.loaded_segments (0x667f0 : word) = Some W_667a0.
Proof. vm_refl. Qed.
Lemma D_667a0 : decode_any W_667a0 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667a4 : bv 32 := 0x0205b423.
Lemma F_667a4 : fetch_word Asan.M.loaded_segments (0x667f4 : word) = Some W_667a4.
Proof. vm_refl. Qed.
Lemma D_667a4 : decode_any W_667a4 = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667a8 : bv 32 := 0x0205b823.
Lemma F_667a8 : fetch_word Asan.M.loaded_segments (0x667f8 : word) = Some W_667a8.
Proof. vm_refl. Qed.
Lemma D_667a8 : decode_any W_667a8 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667ac : bv 32 := 0x0205bc23.
Lemma F_667ac : fetch_word Asan.M.loaded_segments (0x667fc : word) = Some W_667ac.
Proof. vm_refl. Qed.
Lemma D_667ac : decode_any W_667ac = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667b0 : bv 32 := 0x0405b023.
Lemma F_667b0 : fetch_word Asan.M.loaded_segments (0x66800 : word) = Some W_667b0.
Proof. vm_refl. Qed.
Lemma D_667b0 : decode_any W_667b0 = Some (Store SZ8 11 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667b4 : bv 32 := 0x0405b423.
Lemma F_667b4 : fetch_word Asan.M.loaded_segments (0x66804 : word) = Some W_667b4.
Proof. vm_refl. Qed.
Lemma D_667b4 : decode_any W_667b4 = Some (Store SZ8 11 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667b8 : bv 32 := 0x0405b823.
Lemma F_667b8 : fetch_word Asan.M.loaded_segments (0x66808 : word) = Some W_667b8.
Proof. vm_refl. Qed.
Lemma D_667b8 : decode_any W_667b8 = Some (Store SZ8 11 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667bc : bv 32 := 0x0405bc23.
Lemma F_667bc : fetch_word Asan.M.loaded_segments (0x6680c : word) = Some W_667bc.
Proof. vm_refl. Qed.
Lemma D_667bc : decode_any W_667bc = Some (Store SZ8 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667c0 : bv 32 := 0x0605b023.
Lemma F_667c0 : fetch_word Asan.M.loaded_segments (0x66810 : word) = Some W_667c0.
Proof. vm_refl. Qed.
Lemma D_667c0 : decode_any W_667c0 = Some (Store SZ8 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667c4 : bv 32 := 0x0605b423.
Lemma F_667c4 : fetch_word Asan.M.loaded_segments (0x66814 : word) = Some W_667c4.
Proof. vm_refl. Qed.
Lemma D_667c4 : decode_any W_667c4 = Some (Store SZ8 11 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667c8 : bv 32 := 0x0605b823.
Lemma F_667c8 : fetch_word Asan.M.loaded_segments (0x66818 : word) = Some W_667c8.
Proof. vm_refl. Qed.
Lemma D_667c8 : decode_any W_667c8 = Some (Store SZ8 11 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667cc : bv 32 := 0x0605bc23.
Lemma F_667cc : fetch_word Asan.M.loaded_segments (0x6681c : word) = Some W_667cc.
Proof. vm_refl. Qed.
Lemma D_667cc : decode_any W_667cc = Some (Store SZ8 11 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667d0 : bv 32 := 0x0805b023.
Lemma F_667d0 : fetch_word Asan.M.loaded_segments (0x66820 : word) = Some W_667d0.
Proof. vm_refl. Qed.
Lemma D_667d0 : decode_any W_667d0 = Some (Store SZ8 11 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667d4 : bv 32 := 0x0805b423.
Lemma F_667d4 : fetch_word Asan.M.loaded_segments (0x66824 : word) = Some W_667d4.
Proof. vm_refl. Qed.
Lemma D_667d4 : decode_any W_667d4 = Some (Store SZ8 11 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667d8 : bv 32 := 0x0805b823.
Lemma F_667d8 : fetch_word Asan.M.loaded_segments (0x66828 : word) = Some W_667d8.
Proof. vm_refl. Qed.
Lemma D_667d8 : decode_any W_667d8 = Some (Store SZ8 11 0 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667dc : bv 32 := 0x0805bc23.
Lemma F_667dc : fetch_word Asan.M.loaded_segments (0x6682c : word) = Some W_667dc.
Proof. vm_refl. Qed.
Lemma D_667dc : decode_any W_667dc = Some (Store SZ8 11 0 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667e0 : bv 32 := 0x0a05b023.
Lemma F_667e0 : fetch_word Asan.M.loaded_segments (0x66830 : word) = Some W_667e0.
Proof. vm_refl. Qed.
Lemma D_667e0 : decode_any W_667e0 = Some (Store SZ8 11 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667e4 : bv 32 := 0x0a05b423.
Lemma F_667e4 : fetch_word Asan.M.loaded_segments (0x66834 : word) = Some W_667e4.
Proof. vm_refl. Qed.
Lemma D_667e4 : decode_any W_667e4 = Some (Store SZ8 11 0 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667e8 : bv 32 := 0x0a05b823.
Lemma F_667e8 : fetch_word Asan.M.loaded_segments (0x66838 : word) = Some W_667e8.
Proof. vm_refl. Qed.
Lemma D_667e8 : decode_any W_667e8 = Some (Store SZ8 11 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667ec : bv 32 := 0x0a05bc23.
Lemma F_667ec : fetch_word Asan.M.loaded_segments (0x6683c : word) = Some W_667ec.
Proof. vm_refl. Qed.
Lemma D_667ec : decode_any W_667ec = Some (Store SZ8 11 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667f0 : bv 32 := 0x0c05b023.
Lemma F_667f0 : fetch_word Asan.M.loaded_segments (0x66840 : word) = Some W_667f0.
Proof. vm_refl. Qed.
Lemma D_667f0 : decode_any W_667f0 = Some (Store SZ8 11 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667f4 : bv 32 := 0x0c05b423.
Lemma F_667f4 : fetch_word Asan.M.loaded_segments (0x66844 : word) = Some W_667f4.
Proof. vm_refl. Qed.
Lemma D_667f4 : decode_any W_667f4 = Some (Store SZ8 11 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667f8 : bv 32 := 0x0c05b823.
Lemma F_667f8 : fetch_word Asan.M.loaded_segments (0x66848 : word) = Some W_667f8.
Proof. vm_refl. Qed.
Lemma D_667f8 : decode_any W_667f8 = Some (Store SZ8 11 0 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_667fc : bv 32 := 0x0c05bc23.
Lemma F_667fc : fetch_word Asan.M.loaded_segments (0x6684c : word) = Some W_667fc.
Proof. vm_refl. Qed.
Lemma D_667fc : decode_any W_667fc = Some (Store SZ8 11 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66800 : bv 32 := 0x0e05b023.
Lemma F_66800 : fetch_word Asan.M.loaded_segments (0x66850 : word) = Some W_66800.
Proof. vm_refl. Qed.
Lemma D_66800 : decode_any W_66800 = Some (Store SZ8 11 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66804 : bv 32 := 0x0e05b423.
Lemma F_66804 : fetch_word Asan.M.loaded_segments (0x66854 : word) = Some W_66804.
Proof. vm_refl. Qed.
Lemma D_66804 : decode_any W_66804 = Some (Store SZ8 11 0 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66808 : bv 32 := 0x0e05b823.
Lemma F_66808 : fetch_word Asan.M.loaded_segments (0x66858 : word) = Some W_66808.
Proof. vm_refl. Qed.
Lemma D_66808 : decode_any W_66808 = Some (Store SZ8 11 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6680c : bv 32 := 0x0e05bc23.
Lemma F_6680c : fetch_word Asan.M.loaded_segments (0x6685c : word) = Some W_6680c.
Proof. vm_refl. Qed.
Lemma D_6680c : decode_any W_6680c = Some (Store SZ8 11 0 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66810 : bv 32 := 0x01813083.
Lemma F_66810 : fetch_word Asan.M.loaded_segments (0x66860 : word) = Some W_66810.
Proof. vm_refl. Qed.
Lemma D_66810 : decode_any W_66810 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66814 : bv 32 := 0x01013403.
Lemma F_66814 : fetch_word Asan.M.loaded_segments (0x66864 : word) = Some W_66814.
Proof. vm_refl. Qed.
Lemma D_66814 : decode_any W_66814 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66818 : bv 32 := 0x00813483.
Lemma F_66818 : fetch_word Asan.M.loaded_segments (0x66868 : word) = Some W_66818.
Proof. vm_refl. Qed.
Lemma D_66818 : decode_any W_66818 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6681c : bv 32 := 0x00013903.
Lemma F_6681c : fetch_word Asan.M.loaded_segments (0x6686c : word) = Some W_6681c.
Proof. vm_refl. Qed.
Lemma D_6681c : decode_any W_6681c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66820 : bv 32 := 0x02010113.
Lemma F_66820 : fetch_word Asan.M.loaded_segments (0x66870 : word) = Some W_66820.
Proof. vm_refl. Qed.
Lemma D_66820 : decode_any W_66820 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66824 : bv 32 := 0x00008067.
Lemma F_66824 : fetch_word Asan.M.loaded_segments (0x66874 : word) = Some W_66824.
Proof. vm_refl. Qed.
Lemma D_66824 : decode_any W_66824 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66844 : bv 32 := 0xff010113.
Lemma F_66844 : fetch_word Asan.M.loaded_segments (0x66894 : word) = Some W_66844.
Proof. vm_refl. Qed.
Lemma D_66844 : decode_any W_66844 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66848 : bv 32 := 0x00113423.
Lemma F_66848 : fetch_word Asan.M.loaded_segments (0x66898 : word) = Some W_66848.
Proof. vm_refl. Qed.
Lemma D_66848 : decode_any W_66848 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6684c : bv 32 := 0x00813023.
Lemma F_6684c : fetch_word Asan.M.loaded_segments (0x6689c : word) = Some W_6684c.
Proof. vm_refl. Qed.
Lemma D_6684c : decode_any W_6684c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66850 : bv 32 := 0x7f853583.
Lemma F_66850 : fetch_word Asan.M.loaded_segments (0x668a0 : word) = Some W_66850.
Proof. vm_refl. Qed.
Lemma D_66850 : decode_any W_66850 = Some (Load SZ8 true 11 10 2040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66854 : bv 32 := 0x00000413.
Lemma F_66854 : fetch_word Asan.M.loaded_segments (0x668a4 : word) = Some W_66854.
Proof. vm_refl. Qed.
Lemma D_66854 : decode_any W_66854 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66858 : bv 32 := 0x00058023.
Lemma F_66858 : fetch_word Asan.M.loaded_segments (0x668a8 : word) = Some W_66858.
Proof. vm_refl. Qed.
Lemma D_66858 : decode_any W_66858 = Some (Store SZ1 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6685c : bv 32 := 0x09c000ef.
Lemma F_6685c : fetch_word Asan.M.loaded_segments (0x668ac : word) = Some W_6685c.
Proof. vm_refl. Qed.
Lemma D_6685c : decode_any W_6685c = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66860 : bv 32 := 0xfffaa597.
Lemma F_66860 : fetch_word Asan.M.loaded_segments (0x668b0 : word) = Some W_66860.
Proof. vm_refl. Qed.
Lemma D_66860 : decode_any W_66860 = Some (Auipc 11 1048490, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66864 : bv 32 := 0xae85b583.
Lemma F_66864 : fetch_word Asan.M.loaded_segments (0x668b4 : word) = Some W_66864.
Proof. vm_refl. Qed.
Lemma D_66864 : decode_any W_66864 = Some (Load SZ8 true 11 11 2792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66868 : bv 32 := 0x00b53023.
Lemma F_66868 : fetch_word Asan.M.loaded_segments (0x668b8 : word) = Some W_66868.
Proof. vm_refl. Qed.
Lemma D_66868 : decode_any W_66868 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6686c : bv 32 := 0x00b53423.
Lemma F_6686c : fetch_word Asan.M.loaded_segments (0x668bc : word) = Some W_6686c.
Proof. vm_refl. Qed.
Lemma D_6686c : decode_any W_6686c = Some (Store SZ8 10 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66870 : bv 32 := 0x00b53823.
Lemma F_66870 : fetch_word Asan.M.loaded_segments (0x668c0 : word) = Some W_66870.
Proof. vm_refl. Qed.
Lemma D_66870 : decode_any W_66870 = Some (Store SZ8 10 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66874 : bv 32 := 0x00b53c23.
Lemma F_66874 : fetch_word Asan.M.loaded_segments (0x668c4 : word) = Some W_66874.
Proof. vm_refl. Qed.
Lemma D_66874 : decode_any W_66874 = Some (Store SZ8 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66878 : bv 32 := 0x02b53023.
Lemma F_66878 : fetch_word Asan.M.loaded_segments (0x668c8 : word) = Some W_66878.
Proof. vm_refl. Qed.
Lemma D_66878 : decode_any W_66878 = Some (Store SZ8 10 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6687c : bv 32 := 0x02b53423.
Lemma F_6687c : fetch_word Asan.M.loaded_segments (0x668cc : word) = Some W_6687c.
Proof. vm_refl. Qed.
Lemma D_6687c : decode_any W_6687c = Some (Store SZ8 10 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66880 : bv 32 := 0x02b53823.
Lemma F_66880 : fetch_word Asan.M.loaded_segments (0x668d0 : word) = Some W_66880.
Proof. vm_refl. Qed.
Lemma D_66880 : decode_any W_66880 = Some (Store SZ8 10 11 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66884 : bv 32 := 0x02b53c23.
Lemma F_66884 : fetch_word Asan.M.loaded_segments (0x668d4 : word) = Some W_66884.
Proof. vm_refl. Qed.
Lemma D_66884 : decode_any W_66884 = Some (Store SZ8 10 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66888 : bv 32 := 0x04b53023.
Lemma F_66888 : fetch_word Asan.M.loaded_segments (0x668d8 : word) = Some W_66888.
Proof. vm_refl. Qed.
Lemma D_66888 : decode_any W_66888 = Some (Store SZ8 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6688c : bv 32 := 0x04b53423.
Lemma F_6688c : fetch_word Asan.M.loaded_segments (0x668dc : word) = Some W_6688c.
Proof. vm_refl. Qed.
Lemma D_6688c : decode_any W_6688c = Some (Store SZ8 10 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66890 : bv 32 := 0x04b53823.
Lemma F_66890 : fetch_word Asan.M.loaded_segments (0x668e0 : word) = Some W_66890.
Proof. vm_refl. Qed.
Lemma D_66890 : decode_any W_66890 = Some (Store SZ8 10 11 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66894 : bv 32 := 0x04b53c23.
Lemma F_66894 : fetch_word Asan.M.loaded_segments (0x668e4 : word) = Some W_66894.
Proof. vm_refl. Qed.
Lemma D_66894 : decode_any W_66894 = Some (Store SZ8 10 11 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66898 : bv 32 := 0x06b53023.
Lemma F_66898 : fetch_word Asan.M.loaded_segments (0x668e8 : word) = Some W_66898.
Proof. vm_refl. Qed.
Lemma D_66898 : decode_any W_66898 = Some (Store SZ8 10 11 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6689c : bv 32 := 0x06b53423.
Lemma F_6689c : fetch_word Asan.M.loaded_segments (0x668ec : word) = Some W_6689c.
Proof. vm_refl. Qed.
Lemma D_6689c : decode_any W_6689c = Some (Store SZ8 10 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668a0 : bv 32 := 0x06b53823.
Lemma F_668a0 : fetch_word Asan.M.loaded_segments (0x668f0 : word) = Some W_668a0.
Proof. vm_refl. Qed.
Lemma D_668a0 : decode_any W_668a0 = Some (Store SZ8 10 11 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668a4 : bv 32 := 0x06b53c23.
Lemma F_668a4 : fetch_word Asan.M.loaded_segments (0x668f4 : word) = Some W_668a4.
Proof. vm_refl. Qed.
Lemma D_668a4 : decode_any W_668a4 = Some (Store SZ8 10 11 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668a8 : bv 32 := 0x08b53023.
Lemma F_668a8 : fetch_word Asan.M.loaded_segments (0x668f8 : word) = Some W_668a8.
Proof. vm_refl. Qed.
Lemma D_668a8 : decode_any W_668a8 = Some (Store SZ8 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668ac : bv 32 := 0x08b53423.
Lemma F_668ac : fetch_word Asan.M.loaded_segments (0x668fc : word) = Some W_668ac.
Proof. vm_refl. Qed.
Lemma D_668ac : decode_any W_668ac = Some (Store SZ8 10 11 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668b0 : bv 32 := 0x08b53823.
Lemma F_668b0 : fetch_word Asan.M.loaded_segments (0x66900 : word) = Some W_668b0.
Proof. vm_refl. Qed.
Lemma D_668b0 : decode_any W_668b0 = Some (Store SZ8 10 11 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668b4 : bv 32 := 0x08b53c23.
Lemma F_668b4 : fetch_word Asan.M.loaded_segments (0x66904 : word) = Some W_668b4.
Proof. vm_refl. Qed.
Lemma D_668b4 : decode_any W_668b4 = Some (Store SZ8 10 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668b8 : bv 32 := 0x0ab53023.
Lemma F_668b8 : fetch_word Asan.M.loaded_segments (0x66908 : word) = Some W_668b8.
Proof. vm_refl. Qed.
Lemma D_668b8 : decode_any W_668b8 = Some (Store SZ8 10 11 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668bc : bv 32 := 0x0ab53423.
Lemma F_668bc : fetch_word Asan.M.loaded_segments (0x6690c : word) = Some W_668bc.
Proof. vm_refl. Qed.
Lemma D_668bc : decode_any W_668bc = Some (Store SZ8 10 11 168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668c0 : bv 32 := 0x0ab53823.
Lemma F_668c0 : fetch_word Asan.M.loaded_segments (0x66910 : word) = Some W_668c0.
Proof. vm_refl. Qed.
Lemma D_668c0 : decode_any W_668c0 = Some (Store SZ8 10 11 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668c4 : bv 32 := 0x0ab53c23.
Lemma F_668c4 : fetch_word Asan.M.loaded_segments (0x66914 : word) = Some W_668c4.
Proof. vm_refl. Qed.
Lemma D_668c4 : decode_any W_668c4 = Some (Store SZ8 10 11 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668c8 : bv 32 := 0x0cb53023.
Lemma F_668c8 : fetch_word Asan.M.loaded_segments (0x66918 : word) = Some W_668c8.
Proof. vm_refl. Qed.
Lemma D_668c8 : decode_any W_668c8 = Some (Store SZ8 10 11 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668cc : bv 32 := 0x0cb53423.
Lemma F_668cc : fetch_word Asan.M.loaded_segments (0x6691c : word) = Some W_668cc.
Proof. vm_refl. Qed.
Lemma D_668cc : decode_any W_668cc = Some (Store SZ8 10 11 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668d0 : bv 32 := 0x0cb53823.
Lemma F_668d0 : fetch_word Asan.M.loaded_segments (0x66920 : word) = Some W_668d0.
Proof. vm_refl. Qed.
Lemma D_668d0 : decode_any W_668d0 = Some (Store SZ8 10 11 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668d4 : bv 32 := 0x0cb53c23.
Lemma F_668d4 : fetch_word Asan.M.loaded_segments (0x66924 : word) = Some W_668d4.
Proof. vm_refl. Qed.
Lemma D_668d4 : decode_any W_668d4 = Some (Store SZ8 10 11 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668d8 : bv 32 := 0x0eb53023.
Lemma F_668d8 : fetch_word Asan.M.loaded_segments (0x66928 : word) = Some W_668d8.
Proof. vm_refl. Qed.
Lemma D_668d8 : decode_any W_668d8 = Some (Store SZ8 10 11 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668dc : bv 32 := 0x0eb53423.
Lemma F_668dc : fetch_word Asan.M.loaded_segments (0x6692c : word) = Some W_668dc.
Proof. vm_refl. Qed.
Lemma D_668dc : decode_any W_668dc = Some (Store SZ8 10 11 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668e0 : bv 32 := 0x0eb53823.
Lemma F_668e0 : fetch_word Asan.M.loaded_segments (0x66930 : word) = Some W_668e0.
Proof. vm_refl. Qed.
Lemma D_668e0 : decode_any W_668e0 = Some (Store SZ8 10 11 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668e4 : bv 32 := 0x0eb53c23.
Lemma F_668e4 : fetch_word Asan.M.loaded_segments (0x66934 : word) = Some W_668e4.
Proof. vm_refl. Qed.
Lemma D_668e4 : decode_any W_668e4 = Some (Store SZ8 10 11 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668e8 : bv 32 := 0x00813083.
Lemma F_668e8 : fetch_word Asan.M.loaded_segments (0x66938 : word) = Some W_668e8.
Proof. vm_refl. Qed.
Lemma D_668e8 : decode_any W_668e8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668ec : bv 32 := 0x00013403.
Lemma F_668ec : fetch_word Asan.M.loaded_segments (0x6693c : word) = Some W_668ec.
Proof. vm_refl. Qed.
Lemma D_668ec : decode_any W_668ec = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668f0 : bv 32 := 0x01010113.
Lemma F_668f0 : fetch_word Asan.M.loaded_segments (0x66940 : word) = Some W_668f0.
Proof. vm_refl. Qed.
Lemma D_668f0 : decode_any W_668f0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668f4 : bv 32 := 0x00008067.
Lemma F_668f4 : fetch_word Asan.M.loaded_segments (0x66944 : word) = Some W_668f4.
Proof. vm_refl. Qed.
Lemma D_668f4 : decode_any W_668f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668f8 : bv 32 := 0x000fa597.
Lemma F_668f8 : fetch_word Asan.M.loaded_segments (0x66948 : word) = Some W_668f8.
Proof. vm_refl. Qed.
Lemma D_668f8 : decode_any W_668f8 = Some (Auipc 11 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_668fc : bv 32 := 0x2d05b583.
Lemma F_668fc : fetch_word Asan.M.loaded_segments (0x6694c : word) = Some W_668fc.
Proof. vm_refl. Qed.
Lemma D_668fc : decode_any W_668fc = Some (Load SZ8 true 11 11 720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66900 : bv 32 := 0x0005b583.
Lemma F_66900 : fetch_word Asan.M.loaded_segments (0x66950 : word) = Some W_66900.
Proof. vm_refl. Qed.
Lemma D_66900 : decode_any W_66900 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66904 : bv 32 := 0xfff58613.
Lemma F_66904 : fetch_word Asan.M.loaded_segments (0x66954 : word) = Some W_66904.
Proof. vm_refl. Qed.
Lemma D_66904 : decode_any W_66904 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66908 : bv 32 := 0x00c5b6b3.
Lemma F_66908 : fetch_word Asan.M.loaded_segments (0x66958 : word) = Some W_66908.
Proof. vm_refl. Qed.
Lemma D_66908 : decode_any W_66908 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6690c : bv 32 := 0xfff68693.
Lemma F_6690c : fetch_word Asan.M.loaded_segments (0x6695c : word) = Some W_6690c.
Proof. vm_refl. Qed.
Lemma D_6690c : decode_any W_6690c = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66910 : bv 32 := 0x00c6f6b3.
Lemma F_66910 : fetch_word Asan.M.loaded_segments (0x66960 : word) = Some W_66910.
Proof. vm_refl. Qed.
Lemma D_66910 : decode_any W_66910 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66914 : bv 32 := 0x04a6f263.
Lemma F_66914 : fetch_word Asan.M.loaded_segments (0x66964 : word) = Some W_66914.
Proof. vm_refl. Qed.
Lemma D_66914 : decode_any W_66914 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66918 : bv 32 := 0x000fa697.
Lemma F_66918 : fetch_word Asan.M.loaded_segments (0x66968 : word) = Some W_66918.
Proof. vm_refl. Qed.
Lemma D_66918 : decode_any W_66918 = Some (Auipc 13 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6691c : bv 32 := 0x2b86b683.
Lemma F_6691c : fetch_word Asan.M.loaded_segments (0x6696c : word) = Some W_6691c.
Proof. vm_refl. Qed.
Lemma D_6691c : decode_any W_6691c = Some (Load SZ8 true 13 13 696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66920 : bv 32 := 0x000fa717.
Lemma F_66920 : fetch_word Asan.M.loaded_segments (0x66970 : word) = Some W_66920.
Proof. vm_refl. Qed.
Lemma D_66920 : decode_any W_66920 = Some (Auipc 14 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66924 : bv 32 := 0x2b873703.
Lemma F_66924 : fetch_word Asan.M.loaded_segments (0x66974 : word) = Some W_66924.
Proof. vm_refl. Qed.
Lemma D_66924 : decode_any W_66924 = Some (Load SZ8 true 14 14 696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66928 : bv 32 := 0x0006b803.
Lemma F_66928 : fetch_word Asan.M.loaded_segments (0x66978 : word) = Some W_66928.
Proof. vm_refl. Qed.
Lemma D_66928 : decode_any W_66928 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6692c : bv 32 := 0x00073683.
Lemma F_6692c : fetch_word Asan.M.loaded_segments (0x6697c : word) = Some W_6692c.
Proof. vm_refl. Qed.
Lemma D_6692c : decode_any W_6692c = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66930 : bv 32 := 0xfff80793.
Lemma F_66930 : fetch_word Asan.M.loaded_segments (0x66980 : word) = Some W_66930.
Proof. vm_refl. Qed.
Lemma D_66930 : decode_any W_66930 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66934 : bv 32 := 0x00a7f463.
Lemma F_66934 : fetch_word Asan.M.loaded_segments (0x66984 : word) = Some W_66934.
Proof. vm_refl. Qed.
Lemma D_66934 : decode_any W_66934 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6693c : bv 32 := 0x000fa717.
Lemma F_6693c : fetch_word Asan.M.loaded_segments (0x6698c : word) = Some W_6693c.
Proof. vm_refl. Qed.
Lemma D_6693c : decode_any W_6693c = Some (Auipc 14 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66940 : bv 32 := 0x2a473703.
Lemma F_66940 : fetch_word Asan.M.loaded_segments (0x66990 : word) = Some W_66940.
Proof. vm_refl. Qed.
Lemma D_66940 : decode_any W_66940 = Some (Load SZ8 true 14 14 676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66944 : bv 32 := 0x00073283.
Lemma F_66944 : fetch_word Asan.M.loaded_segments (0x66994 : word) = Some W_66944.
Proof. vm_refl. Qed.
Lemma D_66944 : decode_any W_66944 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66948 : bv 32 := 0x0032d713.
Lemma F_66948 : fetch_word Asan.M.loaded_segments (0x66998 : word) = Some W_66948.
Proof. vm_refl. Qed.
Lemma D_66948 : decode_any W_66948 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6694c : bv 32 := 0x00b708b3.
Lemma F_6694c : fetch_word Asan.M.loaded_segments (0x6699c : word) = Some W_6694c.
Proof. vm_refl. Qed.
Lemma D_6694c : decode_any W_6694c = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66950 : bv 32 := 0x00a2ea63.
Lemma F_66950 : fetch_word Asan.M.loaded_segments (0x669a0 : word) = Some W_66950.
Proof. vm_refl. Qed.
Lemma D_66950 : decode_any W_66950 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66954 : bv 32 := 0x00a8f863.
Lemma F_66954 : fetch_word Asan.M.loaded_segments (0x669a4 : word) = Some W_66954.
Proof. vm_refl. Qed.
Lemma D_66954 : decode_any W_66954 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66958 : bv 32 := 0x00355513.
Lemma F_66958 : fetch_word Asan.M.loaded_segments (0x669a8 : word) = Some W_66958.
Proof. vm_refl. Qed.
Lemma D_66958 : decode_any W_66958 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6695c : bv 32 := 0x00a58533.
Lemma F_6695c : fetch_word Asan.M.loaded_segments (0x669ac : word) = Some W_6695c.
Proof. vm_refl. Qed.
Lemma D_6695c : decode_any W_6695c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_66960 : bv 32 := 0x00008067.
Lemma F_66960 : fetch_word Asan.M.loaded_segments (0x669b0 : word) = Some W_66960.
Proof. vm_refl. Qed.
Lemma D_66960 : decode_any W_66960 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

