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
Definition W_8debc : bv 32 := 0xfd010113.
Lemma F_8debc : fetch_word Asan.M.loaded_segments (0x8df0c : word) = Some W_8debc.
Proof. vm_refl. Qed.
Lemma D_8debc : decode_any W_8debc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dec0 : bv 32 := 0x02113423.
Lemma F_8dec0 : fetch_word Asan.M.loaded_segments (0x8df10 : word) = Some W_8dec0.
Proof. vm_refl. Qed.
Lemma D_8dec0 : decode_any W_8dec0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dec4 : bv 32 := 0x02813023.
Lemma F_8dec4 : fetch_word Asan.M.loaded_segments (0x8df14 : word) = Some W_8dec4.
Proof. vm_refl. Qed.
Lemma D_8dec4 : decode_any W_8dec4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dec8 : bv 32 := 0x00913c23.
Lemma F_8dec8 : fetch_word Asan.M.loaded_segments (0x8df18 : word) = Some W_8dec8.
Proof. vm_refl. Qed.
Lemma D_8dec8 : decode_any W_8dec8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8decc : bv 32 := 0x01213823.
Lemma F_8decc : fetch_word Asan.M.loaded_segments (0x8df1c : word) = Some W_8decc.
Proof. vm_refl. Qed.
Lemma D_8decc : decode_any W_8decc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ded0 : bv 32 := 0x01313423.
Lemma F_8ded0 : fetch_word Asan.M.loaded_segments (0x8df20 : word) = Some W_8ded0.
Proof. vm_refl. Qed.
Lemma D_8ded0 : decode_any W_8ded0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ded4 : bv 32 := 0x0016c517.
Lemma F_8ded4 : fetch_word Asan.M.loaded_segments (0x8df24 : word) = Some W_8ded4.
Proof. vm_refl. Qed.
Lemma D_8ded4 : decode_any W_8ded4 = Some (Auipc 10 364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8ded8 : bv 32 := 0xa6450413.
Lemma F_8ded8 : fetch_word Asan.M.loaded_segments (0x8df28 : word) = Some W_8ded8.
Proof. vm_refl. Qed.
Lemma D_8ded8 : decode_any W_8ded8 = Some (OpImm ALU_ADD 8 10 2660, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dedc : bv 32 := 0x00040503.
Lemma F_8dedc : fetch_word Asan.M.loaded_segments (0x8df2c : word) = Some W_8dedc.
Proof. vm_refl. Qed.
Lemma D_8dedc : decode_any W_8dedc = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dee0 : bv 32 := 0x0230000f.
Lemma F_8dee0 : fetch_word Asan.M.loaded_segments (0x8df30 : word) = Some W_8dee0.
Proof. vm_refl. Qed.
Lemma D_8dee0 : decode_any W_8dee0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dee4 : bv 32 := 0x0e051e63.
Lemma F_8dee4 : fetch_word Asan.M.loaded_segments (0x8df34 : word) = Some W_8dee4.
Proof. vm_refl. Qed.
Lemma D_8dee4 : decode_any W_8dee4 = Some (Branch BC_NE 10 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dee8 : bv 32 := 0x00140513.
Lemma F_8dee8 : fetch_word Asan.M.loaded_segments (0x8df38 : word) = Some W_8dee8.
Proof. vm_refl. Qed.
Lemma D_8dee8 : decode_any W_8dee8 = Some (OpImm ALU_ADD 10 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8deec : bv 32 := 0x0ff00593.
Lemma F_8deec : fetch_word Asan.M.loaded_segments (0x8df3c : word) = Some W_8deec.
Proof. vm_refl. Qed.
Lemma D_8deec : decode_any W_8deec = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8def0 : bv 32 := 0x00100613.
Lemma F_8def0 : fetch_word Asan.M.loaded_segments (0x8df40 : word) = Some W_8def0.
Proof. vm_refl. Qed.
Lemma D_8def0 : decode_any W_8def0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8def4 : bv 32 := 0xffc57693.
Lemma F_8def4 : fetch_word Asan.M.loaded_segments (0x8df44 : word) = Some W_8def4.
Proof. vm_refl. Qed.
Lemma D_8def4 : decode_any W_8def4 = Some (OpImm ALU_AND 13 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8def8 : bv 32 := 0x00357713.
Lemma F_8def8 : fetch_word Asan.M.loaded_segments (0x8df48 : word) = Some W_8def8.
Proof. vm_refl. Qed.
Lemma D_8def8 : decode_any W_8def8 = Some (OpImm ALU_AND 14 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8defc : bv 32 := 0x00371713.
Lemma F_8defc : fetch_word Asan.M.loaded_segments (0x8df4c : word) = Some W_8defc.
Proof. vm_refl. Qed.
Lemma D_8defc : decode_any W_8defc = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df00 : bv 32 := 0x00e595bb.
Lemma F_8df00 : fetch_word Asan.M.loaded_segments (0x8df50 : word) = Some W_8df00.
Proof. vm_refl. Qed.
Lemma D_8df00 : decode_any W_8df00 = Some (Op32 ALU_SLL 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df04 : bv 32 := 0x00e6163b.
Lemma F_8df04 : fetch_word Asan.M.loaded_segments (0x8df54 : word) = Some W_8df04.
Proof. vm_refl. Qed.
Lemma D_8df04 : decode_any W_8df04 = Some (Op32 ALU_SLL 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df08 : bv 32 := 0x1406a7af.
Lemma F_8df08 : fetch_word Asan.M.loaded_segments (0x8df58 : word) = Some W_8df08.
Proof. vm_refl. Qed.
Lemma D_8df08 : decode_any W_8df08 = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df0c : bv 32 := 0x00060813.
Lemma F_8df0c : fetch_word Asan.M.loaded_segments (0x8df5c : word) = Some W_8df0c.
Proof. vm_refl. Qed.
Lemma D_8df0c : decode_any W_8df0c = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df10 : bv 32 := 0x0107c833.
Lemma F_8df10 : fetch_word Asan.M.loaded_segments (0x8df60 : word) = Some W_8df10.
Proof. vm_refl. Qed.
Lemma D_8df10 : decode_any W_8df10 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df14 : bv 32 := 0x00b87833.
Lemma F_8df14 : fetch_word Asan.M.loaded_segments (0x8df64 : word) = Some W_8df14.
Proof. vm_refl. Qed.
Lemma D_8df14 : decode_any W_8df14 = Some (Op ALU_AND 16 16 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df18 : bv 32 := 0x0107c833.
Lemma F_8df18 : fetch_word Asan.M.loaded_segments (0x8df68 : word) = Some W_8df18.
Proof. vm_refl. Qed.
Lemma D_8df18 : decode_any W_8df18 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df1c : bv 32 := 0x1906a82f.
Lemma F_8df1c : fetch_word Asan.M.loaded_segments (0x8df6c : word) = Some W_8df1c.
Proof. vm_refl. Qed.
Lemma D_8df1c : decode_any W_8df1c = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df20 : bv 32 := 0xfe0814e3.
Lemma F_8df20 : fetch_word Asan.M.loaded_segments (0x8df70 : word) = Some W_8df20.
Proof. vm_refl. Qed.
Lemma D_8df20 : decode_any W_8df20 = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df24 : bv 32 := 0x00e7d5bb.
Lemma F_8df24 : fetch_word Asan.M.loaded_segments (0x8df74 : word) = Some W_8df24.
Proof. vm_refl. Qed.
Lemma D_8df24 : decode_any W_8df24 = Some (Op32 ALU_SRL 11 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df28 : bv 32 := 0x0ff5f593.
Lemma F_8df28 : fetch_word Asan.M.loaded_segments (0x8df78 : word) = Some W_8df28.
Proof. vm_refl. Qed.
Lemma D_8df28 : decode_any W_8df28 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df2c : bv 32 := 0x0c059c63.
Lemma F_8df2c : fetch_word Asan.M.loaded_segments (0x8df7c : word) = Some W_8df2c.
Proof. vm_refl. Qed.
Lemma D_8df2c : decode_any W_8df2c = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df30 : bv 32 := 0x00040503.
Lemma F_8df30 : fetch_word Asan.M.loaded_segments (0x8df80 : word) = Some W_8df30.
Proof. vm_refl. Qed.
Lemma D_8df30 : decode_any W_8df30 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df34 : bv 32 := 0x0a051263.
Lemma F_8df34 : fetch_word Asan.M.loaded_segments (0x8df84 : word) = Some W_8df34.
Proof. vm_refl. Qed.
Lemma D_8df34 : decode_any W_8df34 = Some (Branch BC_NE 10 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df38 : bv 32 := 0x000dd517.
Lemma F_8df38 : fetch_word Asan.M.loaded_segments (0x8df88 : word) = Some W_8df38.
Proof. vm_refl. Qed.
Lemma D_8df38 : decode_any W_8df38 = Some (Auipc 10 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df3c : bv 32 := 0x000815b7.
Lemma F_8df3c : fetch_word Asan.M.loaded_segments (0x8df8c : word) = Some W_8df3c.
Proof. vm_refl. Qed.
Lemma D_8df3c : decode_any W_8df3c = Some (Lui 11 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df40 : bv 32 := 0x17850493.
Lemma F_8df40 : fetch_word Asan.M.loaded_segments (0x8df90 : word) = Some W_8df40.
Proof. vm_refl. Qed.
Lemma D_8df40 : decode_any W_8df40 = Some (OpImm ALU_ADD 9 10 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df44 : bv 32 := 0x0085851b.
Lemma F_8df44 : fetch_word Asan.M.loaded_segments (0x8df94 : word) = Some W_8df44.
Proof. vm_refl. Qed.
Lemma D_8df44 : decode_any W_8df44 = Some (OpImm32 10 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df48 : bv 32 := 0x00a48533.
Lemma F_8df48 : fetch_word Asan.M.loaded_segments (0x8df98 : word) = Some W_8df48.
Proof. vm_refl. Qed.
Lemma D_8df48 : decode_any W_8df48 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df4c : bv 32 := 0x02800613.
Lemma F_8df4c : fetch_word Asan.M.loaded_segments (0x8df9c : word) = Some W_8df4c.
Proof. vm_refl. Qed.
Lemma D_8df4c : decode_any W_8df4c = Some (OpImm ALU_ADD 12 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df50 : bv 32 := 0x00000593.
Lemma F_8df50 : fetch_word Asan.M.loaded_segments (0x8dfa0 : word) = Some W_8df50.
Proof. vm_refl. Qed.
Lemma D_8df50 : decode_any W_8df50 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df54 : bv 32 := 0x269050ef.
Lemma F_8df54 : fetch_word Asan.M.loaded_segments (0x8dfa4 : word) = Some W_8df54.
Proof. vm_refl. Qed.
Lemma D_8df54 : decode_any W_8df54 = Some (Jal 1 23144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df58 : bv 32 := 0x00048023.
Lemma F_8df58 : fetch_word Asan.M.loaded_segments (0x8dfa8 : word) = Some W_8df58.
Proof. vm_refl. Qed.
Lemma D_8df58 : decode_any W_8df58 = Some (Store SZ1 9 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df5c : bv 32 := 0x00848513.
Lemma F_8df5c : fetch_word Asan.M.loaded_segments (0x8dfac : word) = Some W_8df5c.
Proof. vm_refl. Qed.
Lemma D_8df5c : decode_any W_8df5c = Some (OpImm ALU_ADD 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df60 : bv 32 := 0x00040637.
Lemma F_8df60 : fetch_word Asan.M.loaded_segments (0x8dfb0 : word) = Some W_8df60.
Proof. vm_refl. Qed.
Lemma D_8df60 : decode_any W_8df60 = Some (Lui 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df64 : bv 32 := 0x000409b7.
Lemma F_8df64 : fetch_word Asan.M.loaded_segments (0x8dfb4 : word) = Some W_8df64.
Proof. vm_refl. Qed.
Lemma D_8df64 : decode_any W_8df64 = Some (Lui 19 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df68 : bv 32 := 0x00000593.
Lemma F_8df68 : fetch_word Asan.M.loaded_segments (0x8dfb8 : word) = Some W_8df68.
Proof. vm_refl. Qed.
Lemma D_8df68 : decode_any W_8df68 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df6c : bv 32 := 0x251050ef.
Lemma F_8df6c : fetch_word Asan.M.loaded_segments (0x8dfbc : word) = Some W_8df6c.
Proof. vm_refl. Qed.
Lemma D_8df6c : decode_any W_8df6c = Some (Jal 1 23120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df70 : bv 32 := 0x0409851b.
Lemma F_8df70 : fetch_word Asan.M.loaded_segments (0x8dfc0 : word) = Some W_8df70.
Proof. vm_refl. Qed.
Lemma D_8df70 : decode_any W_8df70 = Some (OpImm32 10 19 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df74 : bv 32 := 0x00a48533.
Lemma F_8df74 : fetch_word Asan.M.loaded_segments (0x8dfc4 : word) = Some W_8df74.
Proof. vm_refl. Qed.
Lemma D_8df74 : decode_any W_8df74 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df78 : bv 32 := 0x01b00613.
Lemma F_8df78 : fetch_word Asan.M.loaded_segments (0x8dfc8 : word) = Some W_8df78.
Proof. vm_refl. Qed.
Lemma D_8df78 : decode_any W_8df78 = Some (OpImm ALU_ADD 12 0 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df7c : bv 32 := 0x00761613.
Lemma F_8df7c : fetch_word Asan.M.loaded_segments (0x8dfcc : word) = Some W_8df7c.
Proof. vm_refl. Qed.
Lemma D_8df7c : decode_any W_8df7c = Some (ShiftImm ALU_SLL 12 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df80 : bv 32 := 0x00000593.
Lemma F_8df80 : fetch_word Asan.M.loaded_segments (0x8dfd0 : word) = Some W_8df80.
Proof. vm_refl. Qed.
Lemma D_8df80 : decode_any W_8df80 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df84 : bv 32 := 0x239050ef.
Lemma F_8df84 : fetch_word Asan.M.loaded_segments (0x8dfd4 : word) = Some W_8df84.
Proof. vm_refl. Qed.
Lemma D_8df84 : decode_any W_8df84 = Some (Jal 1 23096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df88 : bv 32 := 0x00041937.
Lemma F_8df88 : fetch_word Asan.M.loaded_segments (0x8dfd8 : word) = Some W_8df88.
Proof. vm_refl. Qed.
Lemma D_8df88 : decode_any W_8df88 = Some (Lui 18 65, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df8c : bv 32 := 0xdc09051b.
Lemma F_8df8c : fetch_word Asan.M.loaded_segments (0x8dfdc : word) = Some W_8df8c.
Proof. vm_refl. Qed.
Lemma D_8df8c : decode_any W_8df8c = Some (OpImm32 10 18 3520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df90 : bv 32 := 0x00a48533.
Lemma F_8df90 : fetch_word Asan.M.loaded_segments (0x8dfe0 : word) = Some W_8df90.
Proof. vm_refl. Qed.
Lemma D_8df90 : decode_any W_8df90 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df94 : bv 32 := 0x2489861b.
Lemma F_8df94 : fetch_word Asan.M.loaded_segments (0x8dfe4 : word) = Some W_8df94.
Proof. vm_refl. Qed.
Lemma D_8df94 : decode_any W_8df94 = Some (OpImm32 12 19 584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df98 : bv 32 := 0x00000593.
Lemma F_8df98 : fetch_word Asan.M.loaded_segments (0x8dfe8 : word) = Some W_8df98.
Proof. vm_refl. Qed.
Lemma D_8df98 : decode_any W_8df98 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8df9c : bv 32 := 0x221050ef.
Lemma F_8df9c : fetch_word Asan.M.loaded_segments (0x8dfec : word) = Some W_8df9c.
Proof. vm_refl. Qed.
Lemma D_8df9c : decode_any W_8df9c = Some (Jal 1 23072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfa0 : bv 32 := 0x000d3517.
Lemma F_8dfa0 : fetch_word Asan.M.loaded_segments (0x8dff0 : word) = Some W_8dfa0.
Proof. vm_refl. Qed.
Lemma D_8dfa0 : decode_any W_8dfa0 = Some (Auipc 10 211, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfa4 : bv 32 := 0xc0853983.
Lemma F_8dfa4 : fetch_word Asan.M.loaded_segments (0x8dff4 : word) = Some W_8dfa4.
Proof. vm_refl. Qed.
Lemma D_8dfa4 : decode_any W_8dfa4 = Some (Load SZ8 true 19 10 3080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfa8 : bv 32 := 0x0009b503.
Lemma F_8dfa8 : fetch_word Asan.M.loaded_segments (0x8dff8 : word) = Some W_8dfa8.
Proof. vm_refl. Qed.
Lemma D_8dfa8 : decode_any W_8dfa8 = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfac : bv 32 := 0x00051663.
Lemma F_8dfac : fetch_word Asan.M.loaded_segments (0x8dffc : word) = Some W_8dfac.
Proof. vm_refl. Qed.
Lemma D_8dfac : decode_any W_8dfac = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfb8 : bv 32 := 0x012485b3.
Lemma F_8dfb8 : fetch_word Asan.M.loaded_segments (0x8e008 : word) = Some W_8dfb8.
Proof. vm_refl. Qed.
Lemma D_8dfb8 : decode_any W_8dfb8 = Some (Op ALU_ADD 11 9 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfbc : bv 32 := 0xdd09061b.
Lemma F_8dfbc : fetch_word Asan.M.loaded_segments (0x8e00c : word) = Some W_8dfbc.
Proof. vm_refl. Qed.
Lemma D_8dfbc : decode_any W_8dfbc = Some (OpImm32 12 18 3536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfc0 : bv 32 := 0x00c48633.
Lemma F_8dfc0 : fetch_word Asan.M.loaded_segments (0x8e010 : word) = Some W_8dfc0.
Proof. vm_refl. Qed.
Lemma D_8dfc0 : decode_any W_8dfc0 = Some (Op ALU_ADD 12 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfc4 : bv 32 := 0x00100693.
Lemma F_8dfc4 : fetch_word Asan.M.loaded_segments (0x8e014 : word) = Some W_8dfc4.
Proof. vm_refl. Qed.
Lemma D_8dfc4 : decode_any W_8dfc4 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfc8 : bv 32 := 0xdca5b023.
Lemma F_8dfc8 : fetch_word Asan.M.loaded_segments (0x8e018 : word) = Some W_8dfc8.
Proof. vm_refl. Qed.
Lemma D_8dfc8 : decode_any W_8dfc8 = Some (Store SZ8 11 10 3520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfcc : bv 32 := 0xdcc5b423.
Lemma F_8dfcc : fetch_word Asan.M.loaded_segments (0x8e01c : word) = Some W_8dfcc.
Proof. vm_refl. Qed.
Lemma D_8dfcc : decode_any W_8dfcc = Some (Store SZ8 11 12 3528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfd0 : bv 32 := 0x0310000f.
Lemma F_8dfd0 : fetch_word Asan.M.loaded_segments (0x8e020 : word) = Some W_8dfd0.
Proof. vm_refl. Qed.
Lemma D_8dfd0 : decode_any W_8dfd0 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfd4 : bv 32 := 0x00d40023.
Lemma F_8dfd4 : fetch_word Asan.M.loaded_segments (0x8e024 : word) = Some W_8dfd4.
Proof. vm_refl. Qed.
Lemma D_8dfd4 : decode_any W_8dfd4 = Some (Store SZ1 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfd8 : bv 32 := 0x0310000f.
Lemma F_8dfd8 : fetch_word Asan.M.loaded_segments (0x8e028 : word) = Some W_8dfd8.
Proof. vm_refl. Qed.
Lemma D_8dfd8 : decode_any W_8dfd8 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfdc : bv 32 := 0x000400a3.
Lemma F_8dfdc : fetch_word Asan.M.loaded_segments (0x8e02c : word) = Some W_8dfdc.
Proof. vm_refl. Qed.
Lemma D_8dfdc : decode_any W_8dfdc = Some (Store SZ1 8 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfe0 : bv 32 := 0x000dd517.
Lemma F_8dfe0 : fetch_word Asan.M.loaded_segments (0x8e030 : word) = Some W_8dfe0.
Proof. vm_refl. Qed.
Lemma D_8dfe0 : decode_any W_8dfe0 = Some (Auipc 10 221, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfe4 : bv 32 := 0x0d050513.
Lemma F_8dfe4 : fetch_word Asan.M.loaded_segments (0x8e034 : word) = Some W_8dfe4.
Proof. vm_refl. Qed.
Lemma D_8dfe4 : decode_any W_8dfe4 = Some (OpImm ALU_ADD 10 10 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfe8 : bv 32 := 0x02813083.
Lemma F_8dfe8 : fetch_word Asan.M.loaded_segments (0x8e038 : word) = Some W_8dfe8.
Proof. vm_refl. Qed.
Lemma D_8dfe8 : decode_any W_8dfe8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dfec : bv 32 := 0x02013403.
Lemma F_8dfec : fetch_word Asan.M.loaded_segments (0x8e03c : word) = Some W_8dfec.
Proof. vm_refl. Qed.
Lemma D_8dfec : decode_any W_8dfec = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dff0 : bv 32 := 0x01813483.
Lemma F_8dff0 : fetch_word Asan.M.loaded_segments (0x8e040 : word) = Some W_8dff0.
Proof. vm_refl. Qed.
Lemma D_8dff0 : decode_any W_8dff0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dff4 : bv 32 := 0x01013903.
Lemma F_8dff4 : fetch_word Asan.M.loaded_segments (0x8e044 : word) = Some W_8dff4.
Proof. vm_refl. Qed.
Lemma D_8dff4 : decode_any W_8dff4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dff8 : bv 32 := 0x00813983.
Lemma F_8dff8 : fetch_word Asan.M.loaded_segments (0x8e048 : word) = Some W_8dff8.
Proof. vm_refl. Qed.
Lemma D_8dff8 : decode_any W_8dff8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8dffc : bv 32 := 0x03010113.
Lemma F_8dffc : fetch_word Asan.M.loaded_segments (0x8e04c : word) = Some W_8dffc.
Proof. vm_refl. Qed.
Lemma D_8dffc : decode_any W_8dffc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

