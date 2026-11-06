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
Definition W_81000 : bv 32 := 0x00083803.
Lemma F_81000 : fetch_word Asan.M.loaded_segments (0x81050 : word) = Some W_81000.
Proof. vm_refl. Qed.
Lemma D_81000 : decode_any W_81000 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81004 : bv 32 := 0x0008b883.
Lemma F_81004 : fetch_word Asan.M.loaded_segments (0x81054 : word) = Some W_81004.
Proof. vm_refl. Qed.
Lemma D_81004 : decode_any W_81004 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81008 : bv 32 := 0x0108e833.
Lemma F_81008 : fetch_word Asan.M.loaded_segments (0x81058 : word) = Some W_81008.
Proof. vm_refl. Qed.
Lemma D_81008 : decode_any W_81008 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8100c : bv 32 := 0x24081a63.
Lemma F_8100c : fetch_word Asan.M.loaded_segments (0x8105c : word) = Some W_8100c.
Proof. vm_refl. Qed.
Lemma D_8100c : decode_any W_8100c = Some (Branch BC_NE 16 0 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81010 : bv 32 := 0x155120ef.
Lemma F_81010 : fetch_word Asan.M.loaded_segments (0x81060 : word) = Some W_81010.
Proof. vm_refl. Qed.
Lemma D_81010 : decode_any W_81010 = Some (Jal 1 76116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81014 : bv 32 := 0x07010113.
Lemma F_81014 : fetch_word Asan.M.loaded_segments (0x81064 : word) = Some W_81014.
Proof. vm_refl. Qed.
Lemma D_81014 : decode_any W_81014 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81018 : bv 32 := 0x7e813083.
Lemma F_81018 : fetch_word Asan.M.loaded_segments (0x81068 : word) = Some W_81018.
Proof. vm_refl. Qed.
Lemma D_81018 : decode_any W_81018 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8101c : bv 32 := 0x7e013403.
Lemma F_8101c : fetch_word Asan.M.loaded_segments (0x8106c : word) = Some W_8101c.
Proof. vm_refl. Qed.
Lemma D_8101c : decode_any W_8101c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81020 : bv 32 := 0x7d813483.
Lemma F_81020 : fetch_word Asan.M.loaded_segments (0x81070 : word) = Some W_81020.
Proof. vm_refl. Qed.
Lemma D_81020 : decode_any W_81020 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81024 : bv 32 := 0x7d013903.
Lemma F_81024 : fetch_word Asan.M.loaded_segments (0x81074 : word) = Some W_81024.
Proof. vm_refl. Qed.
Lemma D_81024 : decode_any W_81024 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81028 : bv 32 := 0x7c813983.
Lemma F_81028 : fetch_word Asan.M.loaded_segments (0x81078 : word) = Some W_81028.
Proof. vm_refl. Qed.
Lemma D_81028 : decode_any W_81028 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8102c : bv 32 := 0x7c013a03.
Lemma F_8102c : fetch_word Asan.M.loaded_segments (0x8107c : word) = Some W_8102c.
Proof. vm_refl. Qed.
Lemma D_8102c : decode_any W_8102c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81030 : bv 32 := 0x7b813a83.
Lemma F_81030 : fetch_word Asan.M.loaded_segments (0x81080 : word) = Some W_81030.
Proof. vm_refl. Qed.
Lemma D_81030 : decode_any W_81030 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81034 : bv 32 := 0x7b013b03.
Lemma F_81034 : fetch_word Asan.M.loaded_segments (0x81084 : word) = Some W_81034.
Proof. vm_refl. Qed.
Lemma D_81034 : decode_any W_81034 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81038 : bv 32 := 0x7a813b83.
Lemma F_81038 : fetch_word Asan.M.loaded_segments (0x81088 : word) = Some W_81038.
Proof. vm_refl. Qed.
Lemma D_81038 : decode_any W_81038 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8103c : bv 32 := 0x7f010113.
Lemma F_8103c : fetch_word Asan.M.loaded_segments (0x8108c : word) = Some W_8103c.
Proof. vm_refl. Qed.
Lemma D_8103c : decode_any W_8103c = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81040 : bv 32 := 0x00008067.
Lemma F_81040 : fetch_word Asan.M.loaded_segments (0x81090 : word) = Some W_81040.
Proof. vm_refl. Qed.
Lemma D_81040 : decode_any W_81040 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_810cc : bv 32 := 0x0c061463.
Lemma F_810cc : fetch_word Asan.M.loaded_segments (0x8111c : word) = Some W_810cc.
Proof. vm_refl. Qed.
Lemma D_810cc : decode_any W_810cc = Some (Branch BC_NE 12 0 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_810d0 : bv 32 := 0xef5ff06f.
Lemma F_810d0 : fetch_word Asan.M.loaded_segments (0x81120 : word) = Some W_810d0.
Proof. vm_refl. Qed.
Lemma D_810d0 : decode_any W_810d0 = Some (Jal 0 2096884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81158 : bv 32 := 0x12061e63.
Lemma F_81158 : fetch_word Asan.M.loaded_segments (0x811a8 : word) = Some W_81158.
Proof. vm_refl. Qed.
Lemma D_81158 : decode_any W_81158 = Some (Branch BC_NE 12 0 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8115c : bv 32 := 0xeb5ff06f.
Lemma F_8115c : fetch_word Asan.M.loaded_segments (0x811ac : word) = Some W_8115c.
Proof. vm_refl. Qed.
Lemma D_8115c : decode_any W_8115c = Some (Jal 0 2096820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81160 : bv 32 := 0x00070803.
Lemma F_81160 : fetch_word Asan.M.loaded_segments (0x811b0 : word) = Some W_81160.
Proof. vm_refl. Qed.
Lemma D_81160 : decode_any W_81160 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81164 : bv 32 := 0x0077f793.
Lemma F_81164 : fetch_word Asan.M.loaded_segments (0x811b4 : word) = Some W_81164.
Proof. vm_refl. Qed.
Lemma D_81164 : decode_any W_81164 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81168 : bv 32 := 0x010038b3.
Lemma F_81168 : fetch_word Asan.M.loaded_segments (0x811b8 : word) = Some W_81168.
Proof. vm_refl. Qed.
Lemma D_81168 : decode_any W_81168 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8116c : bv 32 := 0x0107a7b3.
Lemma F_8116c : fetch_word Asan.M.loaded_segments (0x811bc : word) = Some W_8116c.
Proof. vm_refl. Qed.
Lemma D_8116c : decode_any W_8116c = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81170 : bv 32 := 0x0017c793.
Lemma F_81170 : fetch_word Asan.M.loaded_segments (0x811c0 : word) = Some W_81170.
Proof. vm_refl. Qed.
Lemma D_81170 : decode_any W_81170 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81174 : bv 32 := 0x00f8f7b3.
Lemma F_81174 : fetch_word Asan.M.loaded_segments (0x811c4 : word) = Some W_81174.
Proof. vm_refl. Qed.
Lemma D_81174 : decode_any W_81174 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81178 : bv 32 := 0x00e6fa63.
Lemma F_81178 : fetch_word Asan.M.loaded_segments (0x811c8 : word) = Some W_81178.
Proof. vm_refl. Qed.
Lemma D_81178 : decode_any W_81178 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8117c : bv 32 := 0x0006c803.
Lemma F_8117c : fetch_word Asan.M.loaded_segments (0x811cc : word) = Some W_8117c.
Proof. vm_refl. Qed.
Lemma D_8117c : decode_any W_8117c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81180 : bv 32 := 0x00168693.
Lemma F_81180 : fetch_word Asan.M.loaded_segments (0x811d0 : word) = Some W_81180.
Proof. vm_refl. Qed.
Lemma D_81180 : decode_any W_81180 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81184 : bv 32 := 0x00f867b3.
Lemma F_81184 : fetch_word Asan.M.loaded_segments (0x811d4 : word) = Some W_81184.
Proof. vm_refl. Qed.
Lemma D_81184 : decode_any W_81184 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81188 : bv 32 := 0xfee69ae3.
Lemma F_81188 : fetch_word Asan.M.loaded_segments (0x811d8 : word) = Some W_81188.
Proof. vm_refl. Qed.
Lemma D_81188 : decode_any W_81188 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8118c : bv 32 := 0x0ff7f693.
Lemma F_8118c : fetch_word Asan.M.loaded_segments (0x811dc : word) = Some W_8118c.
Proof. vm_refl. Qed.
Lemma D_8118c : decode_any W_8118c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81190 : bv 32 := 0xe2068ae3.
Lemma F_81190 : fetch_word Asan.M.loaded_segments (0x811e0 : word) = Some W_81190.
Proof. vm_refl. Qed.
Lemma D_81190 : decode_any W_81190 = Some (Branch BC_EQ 13 0 7732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81194 : bv 32 := 0x00050b13.
Lemma F_81194 : fetch_word Asan.M.loaded_segments (0x811e4 : word) = Some W_81194.
Proof. vm_refl. Qed.
Lemma D_81194 : decode_any W_81194 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81198 : bv 32 := 0x00058513.
Lemma F_81198 : fetch_word Asan.M.loaded_segments (0x811e8 : word) = Some W_81198.
Proof. vm_refl. Qed.
Lemma D_81198 : decode_any W_81198 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8119c : bv 32 := 0x00058b93.
Lemma F_8119c : fetch_word Asan.M.loaded_segments (0x811ec : word) = Some W_8119c.
Proof. vm_refl. Qed.
Lemma D_8119c : decode_any W_8119c = Some (OpImm ALU_ADD 23 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811a0 : bv 32 := 0x00060593.
Lemma F_811a0 : fetch_word Asan.M.loaded_segments (0x811f0 : word) = Some W_811a0.
Proof. vm_refl. Qed.
Lemma D_811a0 : decode_any W_811a0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811a4 : bv 32 := 0x00060493.
Lemma F_811a4 : fetch_word Asan.M.loaded_segments (0x811f4 : word) = Some W_811a4.
Proof. vm_refl. Qed.
Lemma D_811a4 : decode_any W_811a4 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811a8 : bv 32 := 0x075020ef.
Lemma F_811a8 : fetch_word Asan.M.loaded_segments (0x811f8 : word) = Some W_811a8.
Proof. vm_refl. Qed.
Lemma D_811a8 : decode_any W_811a8 = Some (Jal 1 10356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811ac : bv 32 := 0x000b8593.
Lemma F_811ac : fetch_word Asan.M.loaded_segments (0x811fc : word) = Some W_811ac.
Proof. vm_refl. Qed.
Lemma D_811ac : decode_any W_811ac = Some (OpImm ALU_ADD 11 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811b0 : bv 32 := 0x00048613.
Lemma F_811b0 : fetch_word Asan.M.loaded_segments (0x81200 : word) = Some W_811b0.
Proof. vm_refl. Qed.
Lemma D_811b0 : decode_any W_811b0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811b4 : bv 32 := 0x00050913.
Lemma F_811b4 : fetch_word Asan.M.loaded_segments (0x81204 : word) = Some W_811b4.
Proof. vm_refl. Qed.
Lemma D_811b4 : decode_any W_811b4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811b8 : bv 32 := 0x000b0513.
Lemma F_811b8 : fetch_word Asan.M.loaded_segments (0x81208 : word) = Some W_811b8.
Proof. vm_refl. Qed.
Lemma D_811b8 : decode_any W_811b8 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_811bc : bv 32 := 0xe00904e3.
Lemma F_811bc : fetch_word Asan.M.loaded_segments (0x8120c : word) = Some W_811bc.
Proof. vm_refl. Qed.
Lemma D_811bc : decode_any W_811bc = Some (Branch BC_EQ 18 0 7688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81260 : bv 32 := 0x00070803.
Lemma F_81260 : fetch_word Asan.M.loaded_segments (0x812b0 : word) = Some W_81260.
Proof. vm_refl. Qed.
Lemma D_81260 : decode_any W_81260 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81264 : bv 32 := 0x0077f793.
Lemma F_81264 : fetch_word Asan.M.loaded_segments (0x812b4 : word) = Some W_81264.
Proof. vm_refl. Qed.
Lemma D_81264 : decode_any W_81264 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81268 : bv 32 := 0x010038b3.
Lemma F_81268 : fetch_word Asan.M.loaded_segments (0x812b8 : word) = Some W_81268.
Proof. vm_refl. Qed.
Lemma D_81268 : decode_any W_81268 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8126c : bv 32 := 0x0107a7b3.
Lemma F_8126c : fetch_word Asan.M.loaded_segments (0x812bc : word) = Some W_8126c.
Proof. vm_refl. Qed.
Lemma D_8126c : decode_any W_8126c = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81270 : bv 32 := 0x0017c793.
Lemma F_81270 : fetch_word Asan.M.loaded_segments (0x812c0 : word) = Some W_81270.
Proof. vm_refl. Qed.
Lemma D_81270 : decode_any W_81270 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81274 : bv 32 := 0x00f8f7b3.
Lemma F_81274 : fetch_word Asan.M.loaded_segments (0x812c4 : word) = Some W_81274.
Proof. vm_refl. Qed.
Lemma D_81274 : decode_any W_81274 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81278 : bv 32 := 0x00e6fa63.
Lemma F_81278 : fetch_word Asan.M.loaded_segments (0x812c8 : word) = Some W_81278.
Proof. vm_refl. Qed.
Lemma D_81278 : decode_any W_81278 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8127c : bv 32 := 0x0006c803.
Lemma F_8127c : fetch_word Asan.M.loaded_segments (0x812cc : word) = Some W_8127c.
Proof. vm_refl. Qed.
Lemma D_8127c : decode_any W_8127c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81280 : bv 32 := 0x00168693.
Lemma F_81280 : fetch_word Asan.M.loaded_segments (0x812d0 : word) = Some W_81280.
Proof. vm_refl. Qed.
Lemma D_81280 : decode_any W_81280 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81284 : bv 32 := 0x00f867b3.
Lemma F_81284 : fetch_word Asan.M.loaded_segments (0x812d4 : word) = Some W_81284.
Proof. vm_refl. Qed.
Lemma D_81284 : decode_any W_81284 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81288 : bv 32 := 0xfee69ae3.
Lemma F_81288 : fetch_word Asan.M.loaded_segments (0x812d8 : word) = Some W_81288.
Proof. vm_refl. Qed.
Lemma D_81288 : decode_any W_81288 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8128c : bv 32 := 0x0ff7f693.
Lemma F_8128c : fetch_word Asan.M.loaded_segments (0x812dc : word) = Some W_8128c.
Proof. vm_refl. Qed.
Lemma D_8128c : decode_any W_8128c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81290 : bv 32 := 0xd80680e3.
Lemma F_81290 : fetch_word Asan.M.loaded_segments (0x812e0 : word) = Some W_81290.
Proof. vm_refl. Qed.
Lemma D_81290 : decode_any W_81290 = Some (Branch BC_EQ 13 0 7552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81294 : bv 32 := 0x00050493.
Lemma F_81294 : fetch_word Asan.M.loaded_segments (0x812e4 : word) = Some W_81294.
Proof. vm_refl. Qed.
Lemma D_81294 : decode_any W_81294 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81298 : bv 32 := 0x00058b13.
Lemma F_81298 : fetch_word Asan.M.loaded_segments (0x812e8 : word) = Some W_81298.
Proof. vm_refl. Qed.
Lemma D_81298 : decode_any W_81298 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8129c : bv 32 := 0x00060593.
Lemma F_8129c : fetch_word Asan.M.loaded_segments (0x812ec : word) = Some W_8129c.
Proof. vm_refl. Qed.
Lemma D_8129c : decode_any W_8129c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_812a0 : bv 32 := 0x00060913.
Lemma F_812a0 : fetch_word Asan.M.loaded_segments (0x812f0 : word) = Some W_812a0.
Proof. vm_refl. Qed.
Lemma D_812a0 : decode_any W_812a0 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_812a4 : bv 32 := 0x778020ef.
Lemma F_812a4 : fetch_word Asan.M.loaded_segments (0x812f4 : word) = Some W_812a4.
Proof. vm_refl. Qed.
Lemma D_812a4 : decode_any W_812a4 = Some (Jal 1 10104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_812a8 : bv 32 := 0x000b0593.
Lemma F_812a8 : fetch_word Asan.M.loaded_segments (0x812f8 : word) = Some W_812a8.
Proof. vm_refl. Qed.
Lemma D_812a8 : decode_any W_812a8 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_812ac : bv 32 := 0x00090613.
Lemma F_812ac : fetch_word Asan.M.loaded_segments (0x812fc : word) = Some W_812ac.
Proof. vm_refl. Qed.
Lemma D_812ac : decode_any W_812ac = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_812b0 : bv 32 := 0x00050993.
Lemma F_812b0 : fetch_word Asan.M.loaded_segments (0x81300 : word) = Some W_812b0.
Proof. vm_refl. Qed.
Lemma D_812b0 : decode_any W_812b0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_812b4 : bv 32 := 0x00048513.
Lemma F_812b4 : fetch_word Asan.M.loaded_segments (0x81304 : word) = Some W_812b4.
Proof. vm_refl. Qed.
Lemma D_812b4 : decode_any W_812b4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_812b8 : bv 32 := 0xd4098ce3.
Lemma F_812b8 : fetch_word Asan.M.loaded_segments (0x81308 : word) = Some W_812b8.
Proof. vm_refl. Qed.
Lemma D_812b8 : decode_any W_812b8 = Some (Branch BC_EQ 19 0 7512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813ec : bv 32 := 0x81010113.
Lemma F_813ec : fetch_word Asan.M.loaded_segments (0x8143c : word) = Some W_813ec.
Proof. vm_refl. Qed.
Lemma D_813ec : decode_any W_813ec = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813f0 : bv 32 := 0x7e113423.
Lemma F_813f0 : fetch_word Asan.M.loaded_segments (0x81440 : word) = Some W_813f0.
Proof. vm_refl. Qed.
Lemma D_813f0 : decode_any W_813f0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813f4 : bv 32 := 0x7e813023.
Lemma F_813f4 : fetch_word Asan.M.loaded_segments (0x81444 : word) = Some W_813f4.
Proof. vm_refl. Qed.
Lemma D_813f4 : decode_any W_813f4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813f8 : bv 32 := 0x7c913c23.
Lemma F_813f8 : fetch_word Asan.M.loaded_segments (0x81448 : word) = Some W_813f8.
Proof. vm_refl. Qed.
Lemma D_813f8 : decode_any W_813f8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_813fc : bv 32 := 0x7d213823.
Lemma F_813fc : fetch_word Asan.M.loaded_segments (0x8144c : word) = Some W_813fc.
Proof. vm_refl. Qed.
Lemma D_813fc : decode_any W_813fc = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81400 : bv 32 := 0x7d313423.
Lemma F_81400 : fetch_word Asan.M.loaded_segments (0x81450 : word) = Some W_81400.
Proof. vm_refl. Qed.
Lemma D_81400 : decode_any W_81400 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81404 : bv 32 := 0x7d413023.
Lemma F_81404 : fetch_word Asan.M.loaded_segments (0x81454 : word) = Some W_81404.
Proof. vm_refl. Qed.
Lemma D_81404 : decode_any W_81404 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81408 : bv 32 := 0x7b513c23.
Lemma F_81408 : fetch_word Asan.M.loaded_segments (0x81458 : word) = Some W_81408.
Proof. vm_refl. Qed.
Lemma D_81408 : decode_any W_81408 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8140c : bv 32 := 0x7b613823.
Lemma F_8140c : fetch_word Asan.M.loaded_segments (0x8145c : word) = Some W_8140c.
Proof. vm_refl. Qed.
Lemma D_8140c : decode_any W_8140c = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81410 : bv 32 := 0x7b713423.
Lemma F_81410 : fetch_word Asan.M.loaded_segments (0x81460 : word) = Some W_81410.
Proof. vm_refl. Qed.
Lemma D_81410 : decode_any W_81410 = Some (Store SZ8 2 23 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81414 : bv 32 := 0x7b813023.
Lemma F_81414 : fetch_word Asan.M.loaded_segments (0x81464 : word) = Some W_81414.
Proof. vm_refl. Qed.
Lemma D_81414 : decode_any W_81414 = Some (Store SZ8 2 24 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81418 : bv 32 := 0x7f010413.
Lemma F_81418 : fetch_word Asan.M.loaded_segments (0x81468 : word) = Some W_81418.
Proof. vm_refl. Qed.
Lemma D_81418 : decode_any W_81418 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8141c : bv 32 := 0xf8010113.
Lemma F_8141c : fetch_word Asan.M.loaded_segments (0x8146c : word) = Some W_8141c.
Proof. vm_refl. Qed.
Lemma D_8141c : decode_any W_8141c = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81420 : bv 32 := 0x000e0697.
Lemma F_81420 : fetch_word Asan.M.loaded_segments (0x81470 : word) = Some W_81420.
Proof. vm_refl. Qed.
Lemma D_81420 : decode_any W_81420 = Some (Auipc 13 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81424 : bv 32 := 0x3106b683.
Lemma F_81424 : fetch_word Asan.M.loaded_segments (0x81474 : word) = Some W_81424.
Proof. vm_refl. Qed.
Lemma D_81424 : decode_any W_81424 = Some (Load SZ8 true 13 13 784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81428 : bv 32 := 0x0006c683.
Lemma F_81428 : fetch_word Asan.M.loaded_segments (0x81478 : word) = Some W_81428.
Proof. vm_refl. Qed.
Lemma D_81428 : decode_any W_81428 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8142c : bv 32 := 0x0e068a63.
Lemma F_8142c : fetch_word Asan.M.loaded_segments (0x8147c : word) = Some W_8142c.
Proof. vm_refl. Qed.
Lemma D_8142c : decode_any W_8142c = Some (Branch BC_EQ 13 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81430 : bv 32 := 0x80040a93.
Lemma F_81430 : fetch_word Asan.M.loaded_segments (0x81480 : word) = Some W_81430.
Proof. vm_refl. Qed.
Lemma D_81430 : decode_any W_81430 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81434 : bv 32 := 0xf98a8a93.
Lemma F_81434 : fetch_word Asan.M.loaded_segments (0x81484 : word) = Some W_81434.
Proof. vm_refl. Qed.
Lemma D_81434 : decode_any W_81434 = Some (OpImm ALU_ADD 21 21 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81438 : bv 32 := 0x00c589b3.
Lemma F_81438 : fetch_word Asan.M.loaded_segments (0x81488 : word) = Some W_81438.
Proof. vm_refl. Qed.
Lemma D_81438 : decode_any W_81438 = Some (Op ALU_ADD 19 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8143c : bv 32 := 0x00c50a33.
Lemma F_8143c : fetch_word Asan.M.loaded_segments (0x8148c : word) = Some W_8143c.
Proof. vm_refl. Qed.
Lemma D_8143c : decode_any W_8143c = Some (Op ALU_ADD 20 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81440 : bv 32 := 0x00b50663.
Lemma F_81440 : fetch_word Asan.M.loaded_segments (0x81490 : word) = Some W_81440.
Proof. vm_refl. Qed.
Lemma D_81440 : decode_any W_81440 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81444 : bv 32 := 0x0145f463.
Lemma F_81444 : fetch_word Asan.M.loaded_segments (0x81494 : word) = Some W_81444.
Proof. vm_refl. Qed.
Lemma D_81444 : decode_any W_81444 = Some (Branch BC_GEU 11 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81448 : bv 32 := 0x1b356e63.
Lemma F_81448 : fetch_word Asan.M.loaded_segments (0x81498 : word) = Some W_81448.
Proof. vm_refl. Qed.
Lemma D_81448 : decode_any W_81448 = Some (Branch BC_LTU 10 19 444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8144c : bv 32 := 0xfff5c693.
Lemma F_8144c : fetch_word Asan.M.loaded_segments (0x8149c : word) = Some W_8144c.
Proof. vm_refl. Qed.
Lemma D_8144c : decode_any W_8144c = Some (OpImm ALU_XOR 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81450 : bv 32 := 0x26c6e863.
Lemma F_81450 : fetch_word Asan.M.loaded_segments (0x814a0 : word) = Some W_81450.
Proof. vm_refl. Qed.
Lemma D_81450 : decode_any W_81450 = Some (Branch BC_LTU 13 12 624, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81454 : bv 32 := 0xfbf60b13.
Lemma F_81454 : fetch_word Asan.M.loaded_segments (0x814a4 : word) = Some W_81454.
Proof. vm_refl. Qed.
Lemma D_81454 : decode_any W_81454 = Some (OpImm ALU_ADD 22 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81458 : bv 32 := 0xfbf00693.
Lemma F_81458 : fetch_word Asan.M.loaded_segments (0x814a8 : word) = Some W_81458.
Proof. vm_refl. Qed.
Lemma D_81458 : decode_any W_81458 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8145c : bv 32 := 0x2f66f663.
Lemma F_8145c : fetch_word Asan.M.loaded_segments (0x814ac : word) = Some W_8145c.
Proof. vm_refl. Qed.
Lemma D_8145c : decode_any W_8145c = Some (Branch BC_GEU 13 22 748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81460 : bv 32 := 0x000df697.
Lemma F_81460 : fetch_word Asan.M.loaded_segments (0x814b0 : word) = Some W_81460.
Proof. vm_refl. Qed.
Lemma D_81460 : decode_any W_81460 = Some (Auipc 13 223, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81464 : bv 32 := 0x7686b683.
Lemma F_81464 : fetch_word Asan.M.loaded_segments (0x814b4 : word) = Some W_81464.
Proof. vm_refl. Qed.
Lemma D_81464 : decode_any W_81464 = Some (Load SZ8 true 13 13 1896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81468 : bv 32 := 0x0006b703.
Lemma F_81468 : fetch_word Asan.M.loaded_segments (0x814b8 : word) = Some W_81468.
Proof. vm_refl. Qed.
Lemma D_81468 : decode_any W_81468 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8146c : bv 32 := 0xfff98993.
Lemma F_8146c : fetch_word Asan.M.loaded_segments (0x814bc : word) = Some W_8146c.
Proof. vm_refl. Qed.
Lemma D_8146c : decode_any W_8146c = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81470 : bv 32 := 0x0035d693.
Lemma F_81470 : fetch_word Asan.M.loaded_segments (0x814c0 : word) = Some W_81470.
Proof. vm_refl. Qed.
Lemma D_81470 : decode_any W_81470 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81474 : bv 32 := 0x0039d793.
Lemma F_81474 : fetch_word Asan.M.loaded_segments (0x814c4 : word) = Some W_81474.
Proof. vm_refl. Qed.
Lemma D_81474 : decode_any W_81474 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81478 : bv 32 := 0x00d706b3.
Lemma F_81478 : fetch_word Asan.M.loaded_segments (0x814c8 : word) = Some W_81478.
Proof. vm_refl. Qed.
Lemma D_81478 : decode_any W_81478 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8147c : bv 32 := 0x00f70733.
Lemma F_8147c : fetch_word Asan.M.loaded_segments (0x814cc : word) = Some W_8147c.
Proof. vm_refl. Qed.
Lemma D_8147c : decode_any W_8147c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81480 : bv 32 := 0xff86f793.
Lemma F_81480 : fetch_word Asan.M.loaded_segments (0x814d0 : word) = Some W_81480.
Proof. vm_refl. Qed.
Lemma D_81480 : decode_any W_81480 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81484 : bv 32 := 0xff877813.
Lemma F_81484 : fetch_word Asan.M.loaded_segments (0x814d4 : word) = Some W_81484.
Proof. vm_refl. Qed.
Lemma D_81484 : decode_any W_81484 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81488 : bv 32 := 0x0007b783.
Lemma F_81488 : fetch_word Asan.M.loaded_segments (0x814d8 : word) = Some W_81488.
Proof. vm_refl. Qed.
Lemma D_81488 : decode_any W_81488 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8148c : bv 32 := 0x00083803.
Lemma F_8148c : fetch_word Asan.M.loaded_segments (0x814dc : word) = Some W_8148c.
Proof. vm_refl. Qed.
Lemma D_8148c : decode_any W_8148c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81490 : bv 32 := 0x00f867b3.
Lemma F_81490 : fetch_word Asan.M.loaded_segments (0x814e0 : word) = Some W_81490.
Proof. vm_refl. Qed.
Lemma D_81490 : decode_any W_81490 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81494 : bv 32 := 0x2a079e63.
Lemma F_81494 : fetch_word Asan.M.loaded_segments (0x814e4 : word) = Some W_81494.
Proof. vm_refl. Qed.
Lemma D_81494 : decode_any W_81494 = Some (Branch BC_NE 15 0 700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81498 : bv 32 := 0xfff54693.
Lemma F_81498 : fetch_word Asan.M.loaded_segments (0x814e8 : word) = Some W_81498.
Proof. vm_refl. Qed.
Lemma D_81498 : decode_any W_81498 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8149c : bv 32 := 0x0cc6ee63.
Lemma F_8149c : fetch_word Asan.M.loaded_segments (0x814ec : word) = Some W_8149c.
Proof. vm_refl. Qed.
Lemma D_8149c : decode_any W_8149c = Some (Branch BC_LTU 13 12 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814a0 : bv 32 := 0xfbf00693.
Lemma F_814a0 : fetch_word Asan.M.loaded_segments (0x814f0 : word) = Some W_814a0.
Proof. vm_refl. Qed.
Lemma D_814a0 : decode_any W_814a0 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814a4 : bv 32 := 0x1566fc63.
Lemma F_814a4 : fetch_word Asan.M.loaded_segments (0x814f4 : word) = Some W_814a4.
Proof. vm_refl. Qed.
Lemma D_814a4 : decode_any W_814a4 = Some (Branch BC_GEU 13 22 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814a8 : bv 32 := 0x000df697.
Lemma F_814a8 : fetch_word Asan.M.loaded_segments (0x814f8 : word) = Some W_814a8.
Proof. vm_refl. Qed.
Lemma D_814a8 : decode_any W_814a8 = Some (Auipc 13 223, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814ac : bv 32 := 0x7206b683.
Lemma F_814ac : fetch_word Asan.M.loaded_segments (0x814fc : word) = Some W_814ac.
Proof. vm_refl. Qed.
Lemma D_814ac : decode_any W_814ac = Some (Load SZ8 true 13 13 1824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814b0 : bv 32 := 0x0006b703.
Lemma F_814b0 : fetch_word Asan.M.loaded_segments (0x81500 : word) = Some W_814b0.
Proof. vm_refl. Qed.
Lemma D_814b0 : decode_any W_814b0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814b4 : bv 32 := 0xfffa0a13.
Lemma F_814b4 : fetch_word Asan.M.loaded_segments (0x81504 : word) = Some W_814b4.
Proof. vm_refl. Qed.
Lemma D_814b4 : decode_any W_814b4 = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814b8 : bv 32 := 0x00355693.
Lemma F_814b8 : fetch_word Asan.M.loaded_segments (0x81508 : word) = Some W_814b8.
Proof. vm_refl. Qed.
Lemma D_814b8 : decode_any W_814b8 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814bc : bv 32 := 0x003a5793.
Lemma F_814bc : fetch_word Asan.M.loaded_segments (0x8150c : word) = Some W_814bc.
Proof. vm_refl. Qed.
Lemma D_814bc : decode_any W_814bc = Some (ShiftImm ALU_SRL 15 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814c0 : bv 32 := 0x00d706b3.
Lemma F_814c0 : fetch_word Asan.M.loaded_segments (0x81510 : word) = Some W_814c0.
Proof. vm_refl. Qed.
Lemma D_814c0 : decode_any W_814c0 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814c4 : bv 32 := 0x00f70733.
Lemma F_814c4 : fetch_word Asan.M.loaded_segments (0x81514 : word) = Some W_814c4.
Proof. vm_refl. Qed.
Lemma D_814c4 : decode_any W_814c4 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814c8 : bv 32 := 0xff86f793.
Lemma F_814c8 : fetch_word Asan.M.loaded_segments (0x81518 : word) = Some W_814c8.
Proof. vm_refl. Qed.
Lemma D_814c8 : decode_any W_814c8 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814cc : bv 32 := 0xff877813.
Lemma F_814cc : fetch_word Asan.M.loaded_segments (0x8151c : word) = Some W_814cc.
Proof. vm_refl. Qed.
Lemma D_814cc : decode_any W_814cc = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814d0 : bv 32 := 0x0007b783.
Lemma F_814d0 : fetch_word Asan.M.loaded_segments (0x81520 : word) = Some W_814d0.
Proof. vm_refl. Qed.
Lemma D_814d0 : decode_any W_814d0 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814d4 : bv 32 := 0x00083803.
Lemma F_814d4 : fetch_word Asan.M.loaded_segments (0x81524 : word) = Some W_814d4.
Proof. vm_refl. Qed.
Lemma D_814d4 : decode_any W_814d4 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814d8 : bv 32 := 0x00f867b3.
Lemma F_814d8 : fetch_word Asan.M.loaded_segments (0x81528 : word) = Some W_814d8.
Proof. vm_refl. Qed.
Lemma D_814d8 : decode_any W_814d8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814dc : bv 32 := 0x36079a63.
Lemma F_814dc : fetch_word Asan.M.loaded_segments (0x8152c : word) = Some W_814dc.
Proof. vm_refl. Qed.
Lemma D_814dc : decode_any W_814dc = Some (Branch BC_NE 15 0 884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814e0 : bv 32 := 0x000e1697.
Lemma F_814e0 : fetch_word Asan.M.loaded_segments (0x81530 : word) = Some W_814e0.
Proof. vm_refl. Qed.
Lemma D_814e0 : decode_any W_814e0 = Some (Auipc 13 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814e4 : bv 32 := 0x7186b683.
Lemma F_814e4 : fetch_word Asan.M.loaded_segments (0x81534 : word) = Some W_814e4.
Proof. vm_refl. Qed.
Lemma D_814e4 : decode_any W_814e4 = Some (Load SZ8 true 13 13 1816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814e8 : bv 32 := 0x000680e7.
Lemma F_814e8 : fetch_word Asan.M.loaded_segments (0x81538 : word) = Some W_814e8.
Proof. vm_refl. Qed.
Lemma D_814e8 : decode_any W_814e8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814ec : bv 32 := 0x08010113.
Lemma F_814ec : fetch_word Asan.M.loaded_segments (0x8153c : word) = Some W_814ec.
Proof. vm_refl. Qed.
Lemma D_814ec : decode_any W_814ec = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814f0 : bv 32 := 0x7e813083.
Lemma F_814f0 : fetch_word Asan.M.loaded_segments (0x81540 : word) = Some W_814f0.
Proof. vm_refl. Qed.
Lemma D_814f0 : decode_any W_814f0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814f4 : bv 32 := 0x7e013403.
Lemma F_814f4 : fetch_word Asan.M.loaded_segments (0x81544 : word) = Some W_814f4.
Proof. vm_refl. Qed.
Lemma D_814f4 : decode_any W_814f4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814f8 : bv 32 := 0x7d813483.
Lemma F_814f8 : fetch_word Asan.M.loaded_segments (0x81548 : word) = Some W_814f8.
Proof. vm_refl. Qed.
Lemma D_814f8 : decode_any W_814f8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_814fc : bv 32 := 0x7d013903.
Lemma F_814fc : fetch_word Asan.M.loaded_segments (0x8154c : word) = Some W_814fc.
Proof. vm_refl. Qed.
Lemma D_814fc : decode_any W_814fc = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81500 : bv 32 := 0x7c813983.
Lemma F_81500 : fetch_word Asan.M.loaded_segments (0x81550 : word) = Some W_81500.
Proof. vm_refl. Qed.
Lemma D_81500 : decode_any W_81500 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81504 : bv 32 := 0x7c013a03.
Lemma F_81504 : fetch_word Asan.M.loaded_segments (0x81554 : word) = Some W_81504.
Proof. vm_refl. Qed.
Lemma D_81504 : decode_any W_81504 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81508 : bv 32 := 0x7b813a83.
Lemma F_81508 : fetch_word Asan.M.loaded_segments (0x81558 : word) = Some W_81508.
Proof. vm_refl. Qed.
Lemma D_81508 : decode_any W_81508 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8150c : bv 32 := 0x7b013b03.
Lemma F_8150c : fetch_word Asan.M.loaded_segments (0x8155c : word) = Some W_8150c.
Proof. vm_refl. Qed.
Lemma D_8150c : decode_any W_8150c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81510 : bv 32 := 0x7a813b83.
Lemma F_81510 : fetch_word Asan.M.loaded_segments (0x81560 : word) = Some W_81510.
Proof. vm_refl. Qed.
Lemma D_81510 : decode_any W_81510 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81514 : bv 32 := 0x7a013c03.
Lemma F_81514 : fetch_word Asan.M.loaded_segments (0x81564 : word) = Some W_81514.
Proof. vm_refl. Qed.
Lemma D_81514 : decode_any W_81514 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81518 : bv 32 := 0x7f010113.
Lemma F_81518 : fetch_word Asan.M.loaded_segments (0x81568 : word) = Some W_81518.
Proof. vm_refl. Qed.
Lemma D_81518 : decode_any W_81518 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8151c : bv 32 := 0x00008067.
Lemma F_8151c : fetch_word Asan.M.loaded_segments (0x8156c : word) = Some W_8151c.
Proof. vm_refl. Qed.
Lemma D_8151c : decode_any W_8151c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_815fc : bv 32 := 0x28061463.
Lemma F_815fc : fetch_word Asan.M.loaded_segments (0x8164c : word) = Some W_815fc.
Proof. vm_refl. Qed.
Lemma D_815fc : decode_any W_815fc = Some (Branch BC_NE 12 0 648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81600 : bv 32 := 0xee1ff06f.
Lemma F_81600 : fetch_word Asan.M.loaded_segments (0x81650 : word) = Some W_81600.
Proof. vm_refl. Qed.
Lemma D_81600 : decode_any W_81600 = Some (Jal 0 2096864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81748 : bv 32 := 0x02061e63.
Lemma F_81748 : fetch_word Asan.M.loaded_segments (0x81798 : word) = Some W_81748.
Proof. vm_refl. Qed.
Lemma D_81748 : decode_any W_81748 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8174c : bv 32 := 0xd4dff06f.
Lemma F_8174c : fetch_word Asan.M.loaded_segments (0x8179c : word) = Some W_8174c.
Proof. vm_refl. Qed.
Lemma D_8174c : decode_any W_8174c = Some (Jal 0 2096460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81750 : bv 32 := 0x00070783.
Lemma F_81750 : fetch_word Asan.M.loaded_segments (0x817a0 : word) = Some W_81750.
Proof. vm_refl. Qed.
Lemma D_81750 : decode_any W_81750 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81754 : bv 32 := 0x0079f813.
Lemma F_81754 : fetch_word Asan.M.loaded_segments (0x817a4 : word) = Some W_81754.
Proof. vm_refl. Qed.
Lemma D_81754 : decode_any W_81754 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81758 : bv 32 := 0x00f038b3.
Lemma F_81758 : fetch_word Asan.M.loaded_segments (0x817a8 : word) = Some W_81758.
Proof. vm_refl. Qed.
Lemma D_81758 : decode_any W_81758 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8175c : bv 32 := 0x00f827b3.
Lemma F_8175c : fetch_word Asan.M.loaded_segments (0x817ac : word) = Some W_8175c.
Proof. vm_refl. Qed.
Lemma D_8175c : decode_any W_8175c = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81760 : bv 32 := 0x0017c793.
Lemma F_81760 : fetch_word Asan.M.loaded_segments (0x817b0 : word) = Some W_81760.
Proof. vm_refl. Qed.
Lemma D_81760 : decode_any W_81760 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81764 : bv 32 := 0x00f8f7b3.
Lemma F_81764 : fetch_word Asan.M.loaded_segments (0x817b4 : word) = Some W_81764.
Proof. vm_refl. Qed.
Lemma D_81764 : decode_any W_81764 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81768 : bv 32 := 0x00e6fa63.
Lemma F_81768 : fetch_word Asan.M.loaded_segments (0x817b8 : word) = Some W_81768.
Proof. vm_refl. Qed.
Lemma D_81768 : decode_any W_81768 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8176c : bv 32 := 0x0006c803.
Lemma F_8176c : fetch_word Asan.M.loaded_segments (0x817bc : word) = Some W_8176c.
Proof. vm_refl. Qed.
Lemma D_8176c : decode_any W_8176c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81770 : bv 32 := 0x00168693.
Lemma F_81770 : fetch_word Asan.M.loaded_segments (0x817c0 : word) = Some W_81770.
Proof. vm_refl. Qed.
Lemma D_81770 : decode_any W_81770 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81774 : bv 32 := 0x00f867b3.
Lemma F_81774 : fetch_word Asan.M.loaded_segments (0x817c4 : word) = Some W_81774.
Proof. vm_refl. Qed.
Lemma D_81774 : decode_any W_81774 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81778 : bv 32 := 0xfee69ae3.
Lemma F_81778 : fetch_word Asan.M.loaded_segments (0x817c8 : word) = Some W_81778.
Proof. vm_refl. Qed.
Lemma D_81778 : decode_any W_81778 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8177c : bv 32 := 0x0ff7f693.
Lemma F_8177c : fetch_word Asan.M.loaded_segments (0x817cc : word) = Some W_8177c.
Proof. vm_refl. Qed.
Lemma D_8177c : decode_any W_8177c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81780 : bv 32 := 0xd0068ce3.
Lemma F_81780 : fetch_word Asan.M.loaded_segments (0x817d0 : word) = Some W_81780.
Proof. vm_refl. Qed.
Lemma D_81780 : decode_any W_81780 = Some (Branch BC_EQ 13 0 7448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81784 : bv 32 := 0x00050b93.
Lemma F_81784 : fetch_word Asan.M.loaded_segments (0x817d4 : word) = Some W_81784.
Proof. vm_refl. Qed.
Lemma D_81784 : decode_any W_81784 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81788 : bv 32 := 0x00058513.
Lemma F_81788 : fetch_word Asan.M.loaded_segments (0x817d8 : word) = Some W_81788.
Proof. vm_refl. Qed.
Lemma D_81788 : decode_any W_81788 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8178c : bv 32 := 0x00058c13.
Lemma F_8178c : fetch_word Asan.M.loaded_segments (0x817dc : word) = Some W_8178c.
Proof. vm_refl. Qed.
Lemma D_8178c : decode_any W_8178c = Some (OpImm ALU_ADD 24 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81790 : bv 32 := 0x00060593.
Lemma F_81790 : fetch_word Asan.M.loaded_segments (0x817e0 : word) = Some W_81790.
Proof. vm_refl. Qed.
Lemma D_81790 : decode_any W_81790 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81794 : bv 32 := 0x00060493.
Lemma F_81794 : fetch_word Asan.M.loaded_segments (0x817e4 : word) = Some W_81794.
Proof. vm_refl. Qed.
Lemma D_81794 : decode_any W_81794 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81798 : bv 32 := 0x284020ef.
Lemma F_81798 : fetch_word Asan.M.loaded_segments (0x817e8 : word) = Some W_81798.
Proof. vm_refl. Qed.
Lemma D_81798 : decode_any W_81798 = Some (Jal 1 8836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8179c : bv 32 := 0x000c0593.
Lemma F_8179c : fetch_word Asan.M.loaded_segments (0x817ec : word) = Some W_8179c.
Proof. vm_refl. Qed.
Lemma D_8179c : decode_any W_8179c = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_817a0 : bv 32 := 0x00048613.
Lemma F_817a0 : fetch_word Asan.M.loaded_segments (0x817f0 : word) = Some W_817a0.
Proof. vm_refl. Qed.
Lemma D_817a0 : decode_any W_817a0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_817a4 : bv 32 := 0x00050913.
Lemma F_817a4 : fetch_word Asan.M.loaded_segments (0x817f4 : word) = Some W_817a4.
Proof. vm_refl. Qed.
Lemma D_817a4 : decode_any W_817a4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_817a8 : bv 32 := 0x000b8513.
Lemma F_817a8 : fetch_word Asan.M.loaded_segments (0x817f8 : word) = Some W_817a8.
Proof. vm_refl. Qed.
Lemma D_817a8 : decode_any W_817a8 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_817ac : bv 32 := 0xce0906e3.
Lemma F_817ac : fetch_word Asan.M.loaded_segments (0x817fc : word) = Some W_817ac.
Proof. vm_refl. Qed.
Lemma D_817ac : decode_any W_817ac = Some (Branch BC_EQ 18 0 7404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81850 : bv 32 := 0x00070783.
Lemma F_81850 : fetch_word Asan.M.loaded_segments (0x818a0 : word) = Some W_81850.
Proof. vm_refl. Qed.
Lemma D_81850 : decode_any W_81850 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81854 : bv 32 := 0x007a7813.
Lemma F_81854 : fetch_word Asan.M.loaded_segments (0x818a4 : word) = Some W_81854.
Proof. vm_refl. Qed.
Lemma D_81854 : decode_any W_81854 = Some (OpImm ALU_AND 16 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81858 : bv 32 := 0x00f038b3.
Lemma F_81858 : fetch_word Asan.M.loaded_segments (0x818a8 : word) = Some W_81858.
Proof. vm_refl. Qed.
Lemma D_81858 : decode_any W_81858 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8185c : bv 32 := 0x00f827b3.
Lemma F_8185c : fetch_word Asan.M.loaded_segments (0x818ac : word) = Some W_8185c.
Proof. vm_refl. Qed.
Lemma D_8185c : decode_any W_8185c = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81860 : bv 32 := 0x0017c793.
Lemma F_81860 : fetch_word Asan.M.loaded_segments (0x818b0 : word) = Some W_81860.
Proof. vm_refl. Qed.
Lemma D_81860 : decode_any W_81860 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81864 : bv 32 := 0x00f8f7b3.
Lemma F_81864 : fetch_word Asan.M.loaded_segments (0x818b4 : word) = Some W_81864.
Proof. vm_refl. Qed.
Lemma D_81864 : decode_any W_81864 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81868 : bv 32 := 0x00e6fa63.
Lemma F_81868 : fetch_word Asan.M.loaded_segments (0x818b8 : word) = Some W_81868.
Proof. vm_refl. Qed.
Lemma D_81868 : decode_any W_81868 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8186c : bv 32 := 0x0006c803.
Lemma F_8186c : fetch_word Asan.M.loaded_segments (0x818bc : word) = Some W_8186c.
Proof. vm_refl. Qed.
Lemma D_8186c : decode_any W_8186c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81870 : bv 32 := 0x00168693.
Lemma F_81870 : fetch_word Asan.M.loaded_segments (0x818c0 : word) = Some W_81870.
Proof. vm_refl. Qed.
Lemma D_81870 : decode_any W_81870 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81874 : bv 32 := 0x00f867b3.
Lemma F_81874 : fetch_word Asan.M.loaded_segments (0x818c4 : word) = Some W_81874.
Proof. vm_refl. Qed.
Lemma D_81874 : decode_any W_81874 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81878 : bv 32 := 0xfee69ae3.
Lemma F_81878 : fetch_word Asan.M.loaded_segments (0x818c8 : word) = Some W_81878.
Proof. vm_refl. Qed.
Lemma D_81878 : decode_any W_81878 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8187c : bv 32 := 0x0ff7f693.
Lemma F_8187c : fetch_word Asan.M.loaded_segments (0x818cc : word) = Some W_8187c.
Proof. vm_refl. Qed.
Lemma D_8187c : decode_any W_8187c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81880 : bv 32 := 0xc60680e3.
Lemma F_81880 : fetch_word Asan.M.loaded_segments (0x818d0 : word) = Some W_81880.
Proof. vm_refl. Qed.
Lemma D_81880 : decode_any W_81880 = Some (Branch BC_EQ 13 0 7264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81884 : bv 32 := 0x00050493.
Lemma F_81884 : fetch_word Asan.M.loaded_segments (0x818d4 : word) = Some W_81884.
Proof. vm_refl. Qed.
Lemma D_81884 : decode_any W_81884 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81888 : bv 32 := 0x00058b13.
Lemma F_81888 : fetch_word Asan.M.loaded_segments (0x818d8 : word) = Some W_81888.
Proof. vm_refl. Qed.
Lemma D_81888 : decode_any W_81888 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8188c : bv 32 := 0x00060593.
Lemma F_8188c : fetch_word Asan.M.loaded_segments (0x818dc : word) = Some W_8188c.
Proof. vm_refl. Qed.
Lemma D_8188c : decode_any W_8188c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81890 : bv 32 := 0x00060913.
Lemma F_81890 : fetch_word Asan.M.loaded_segments (0x818e0 : word) = Some W_81890.
Proof. vm_refl. Qed.
Lemma D_81890 : decode_any W_81890 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81894 : bv 32 := 0x188020ef.
Lemma F_81894 : fetch_word Asan.M.loaded_segments (0x818e4 : word) = Some W_81894.
Proof. vm_refl. Qed.
Lemma D_81894 : decode_any W_81894 = Some (Jal 1 8584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81898 : bv 32 := 0x000b0593.
Lemma F_81898 : fetch_word Asan.M.loaded_segments (0x818e8 : word) = Some W_81898.
Proof. vm_refl. Qed.
Lemma D_81898 : decode_any W_81898 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8189c : bv 32 := 0x00090613.
Lemma F_8189c : fetch_word Asan.M.loaded_segments (0x818ec : word) = Some W_8189c.
Proof. vm_refl. Qed.
Lemma D_8189c : decode_any W_8189c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818a0 : bv 32 := 0x00050993.
Lemma F_818a0 : fetch_word Asan.M.loaded_segments (0x818f0 : word) = Some W_818a0.
Proof. vm_refl. Qed.
Lemma D_818a0 : decode_any W_818a0 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818a4 : bv 32 := 0x00048513.
Lemma F_818a4 : fetch_word Asan.M.loaded_segments (0x818f4 : word) = Some W_818a4.
Proof. vm_refl. Qed.
Lemma D_818a4 : decode_any W_818a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_818a8 : bv 32 := 0xc2098ce3.
Lemma F_818a8 : fetch_word Asan.M.loaded_segments (0x818f8 : word) = Some W_818a8.
Proof. vm_refl. Qed.
Lemma D_818a8 : decode_any W_818a8 = Some (Branch BC_EQ 19 0 7224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a7c : bv 32 := 0xfe010113.
Lemma F_81a7c : fetch_word Asan.M.loaded_segments (0x81acc : word) = Some W_81a7c.
Proof. vm_refl. Qed.
Lemma D_81a7c : decode_any W_81a7c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a80 : bv 32 := 0x00113c23.
Lemma F_81a80 : fetch_word Asan.M.loaded_segments (0x81ad0 : word) = Some W_81a80.
Proof. vm_refl. Qed.
Lemma D_81a80 : decode_any W_81a80 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a84 : bv 32 := 0x00813823.
Lemma F_81a84 : fetch_word Asan.M.loaded_segments (0x81ad4 : word) = Some W_81a84.
Proof. vm_refl. Qed.
Lemma D_81a84 : decode_any W_81a84 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a88 : bv 32 := 0x00913423.
Lemma F_81a88 : fetch_word Asan.M.loaded_segments (0x81ad8 : word) = Some W_81a88.
Proof. vm_refl. Qed.
Lemma D_81a88 : decode_any W_81a88 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a8c : bv 32 := 0x01213023.
Lemma F_81a8c : fetch_word Asan.M.loaded_segments (0x81adc : word) = Some W_81a8c.
Proof. vm_refl. Qed.
Lemma D_81a8c : decode_any W_81a8c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a90 : bv 32 := 0x00058413.
Lemma F_81a90 : fetch_word Asan.M.loaded_segments (0x81ae0 : word) = Some W_81a90.
Proof. vm_refl. Qed.
Lemma D_81a90 : decode_any W_81a90 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a94 : bv 32 := 0x00050493.
Lemma F_81a94 : fetch_word Asan.M.loaded_segments (0x81ae4 : word) = Some W_81a94.
Proof. vm_refl. Qed.
Lemma D_81a94 : decode_any W_81a94 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a98 : bv 32 := 0x030000ef.
Lemma F_81a98 : fetch_word Asan.M.loaded_segments (0x81ae8 : word) = Some W_81a98.
Proof. vm_refl. Qed.
Lemma D_81a98 : decode_any W_81a98 = Some (Jal 1 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a9c : bv 32 := 0x00050913.
Lemma F_81a9c : fetch_word Asan.M.loaded_segments (0x81aec : word) = Some W_81a9c.
Proof. vm_refl. Qed.
Lemma D_81a9c : decode_any W_81a9c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81aa0 : bv 32 := 0x00940533.
Lemma F_81aa0 : fetch_word Asan.M.loaded_segments (0x81af0 : word) = Some W_81aa0.
Proof. vm_refl. Qed.
Lemma D_81aa0 : decode_any W_81aa0 = Some (Op ALU_ADD 10 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81aa4 : bv 32 := 0x024000ef.
Lemma F_81aa4 : fetch_word Asan.M.loaded_segments (0x81af4 : word) = Some W_81aa4.
Proof. vm_refl. Qed.
Lemma D_81aa4 : decode_any W_81aa4 = Some (Jal 1 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81aa8 : bv 32 := 0x00050593.
Lemma F_81aa8 : fetch_word Asan.M.loaded_segments (0x81af8 : word) = Some W_81aa8.
Proof. vm_refl. Qed.
Lemma D_81aa8 : decode_any W_81aa8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81aac : bv 32 := 0x00090513.
Lemma F_81aac : fetch_word Asan.M.loaded_segments (0x81afc : word) = Some W_81aac.
Proof. vm_refl. Qed.
Lemma D_81aac : decode_any W_81aac = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ab0 : bv 32 := 0x01813083.
Lemma F_81ab0 : fetch_word Asan.M.loaded_segments (0x81b00 : word) = Some W_81ab0.
Proof. vm_refl. Qed.
Lemma D_81ab0 : decode_any W_81ab0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ab4 : bv 32 := 0x01013403.
Lemma F_81ab4 : fetch_word Asan.M.loaded_segments (0x81b04 : word) = Some W_81ab4.
Proof. vm_refl. Qed.
Lemma D_81ab4 : decode_any W_81ab4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ab8 : bv 32 := 0x00813483.
Lemma F_81ab8 : fetch_word Asan.M.loaded_segments (0x81b08 : word) = Some W_81ab8.
Proof. vm_refl. Qed.
Lemma D_81ab8 : decode_any W_81ab8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81abc : bv 32 := 0x00013903.
Lemma F_81abc : fetch_word Asan.M.loaded_segments (0x81b0c : word) = Some W_81abc.
Proof. vm_refl. Qed.
Lemma D_81abc : decode_any W_81abc = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ac0 : bv 32 := 0x02010113.
Lemma F_81ac0 : fetch_word Asan.M.loaded_segments (0x81b10 : word) = Some W_81ac0.
Proof. vm_refl. Qed.
Lemma D_81ac0 : decode_any W_81ac0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ac4 : bv 32 := 0x3151b06f.
Lemma F_81ac4 : fetch_word Asan.M.loaded_segments (0x81b14 : word) = Some W_81ac4.
Proof. vm_refl. Qed.
Lemma D_81ac4 : decode_any W_81ac4 = Some (Jal 0 113428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ac8 : bv 32 := 0x000df597.
Lemma F_81ac8 : fetch_word Asan.M.loaded_segments (0x81b18 : word) = Some W_81ac8.
Proof. vm_refl. Qed.
Lemma D_81ac8 : decode_any W_81ac8 = Some (Auipc 11 223, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81acc : bv 32 := 0x1005b583.
Lemma F_81acc : fetch_word Asan.M.loaded_segments (0x81b1c : word) = Some W_81acc.
Proof. vm_refl. Qed.
Lemma D_81acc : decode_any W_81acc = Some (Load SZ8 true 11 11 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ad0 : bv 32 := 0x0005b583.
Lemma F_81ad0 : fetch_word Asan.M.loaded_segments (0x81b20 : word) = Some W_81ad0.
Proof. vm_refl. Qed.
Lemma D_81ad0 : decode_any W_81ad0 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ad4 : bv 32 := 0xfff58613.
Lemma F_81ad4 : fetch_word Asan.M.loaded_segments (0x81b24 : word) = Some W_81ad4.
Proof. vm_refl. Qed.
Lemma D_81ad4 : decode_any W_81ad4 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ad8 : bv 32 := 0x00c5b6b3.
Lemma F_81ad8 : fetch_word Asan.M.loaded_segments (0x81b28 : word) = Some W_81ad8.
Proof. vm_refl. Qed.
Lemma D_81ad8 : decode_any W_81ad8 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81adc : bv 32 := 0xfff68693.
Lemma F_81adc : fetch_word Asan.M.loaded_segments (0x81b2c : word) = Some W_81adc.
Proof. vm_refl. Qed.
Lemma D_81adc : decode_any W_81adc = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ae0 : bv 32 := 0x00c6f6b3.
Lemma F_81ae0 : fetch_word Asan.M.loaded_segments (0x81b30 : word) = Some W_81ae0.
Proof. vm_refl. Qed.
Lemma D_81ae0 : decode_any W_81ae0 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ae4 : bv 32 := 0x04a6f263.
Lemma F_81ae4 : fetch_word Asan.M.loaded_segments (0x81b34 : word) = Some W_81ae4.
Proof. vm_refl. Qed.
Lemma D_81ae4 : decode_any W_81ae4 = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ae8 : bv 32 := 0x000df697.
Lemma F_81ae8 : fetch_word Asan.M.loaded_segments (0x81b38 : word) = Some W_81ae8.
Proof. vm_refl. Qed.
Lemma D_81ae8 : decode_any W_81ae8 = Some (Auipc 13 223, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81aec : bv 32 := 0x0e86b683.
Lemma F_81aec : fetch_word Asan.M.loaded_segments (0x81b3c : word) = Some W_81aec.
Proof. vm_refl. Qed.
Lemma D_81aec : decode_any W_81aec = Some (Load SZ8 true 13 13 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81af0 : bv 32 := 0x000df717.
Lemma F_81af0 : fetch_word Asan.M.loaded_segments (0x81b40 : word) = Some W_81af0.
Proof. vm_refl. Qed.
Lemma D_81af0 : decode_any W_81af0 = Some (Auipc 14 223, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81af4 : bv 32 := 0x0e873703.
Lemma F_81af4 : fetch_word Asan.M.loaded_segments (0x81b44 : word) = Some W_81af4.
Proof. vm_refl. Qed.
Lemma D_81af4 : decode_any W_81af4 = Some (Load SZ8 true 14 14 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81af8 : bv 32 := 0x0006b803.
Lemma F_81af8 : fetch_word Asan.M.loaded_segments (0x81b48 : word) = Some W_81af8.
Proof. vm_refl. Qed.
Lemma D_81af8 : decode_any W_81af8 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81afc : bv 32 := 0x00073683.
Lemma F_81afc : fetch_word Asan.M.loaded_segments (0x81b4c : word) = Some W_81afc.
Proof. vm_refl. Qed.
Lemma D_81afc : decode_any W_81afc = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b00 : bv 32 := 0xfff80793.
Lemma F_81b00 : fetch_word Asan.M.loaded_segments (0x81b50 : word) = Some W_81b00.
Proof. vm_refl. Qed.
Lemma D_81b00 : decode_any W_81b00 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b04 : bv 32 := 0x00a7f463.
Lemma F_81b04 : fetch_word Asan.M.loaded_segments (0x81b54 : word) = Some W_81b04.
Proof. vm_refl. Qed.
Lemma D_81b04 : decode_any W_81b04 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b0c : bv 32 := 0x000df717.
Lemma F_81b0c : fetch_word Asan.M.loaded_segments (0x81b5c : word) = Some W_81b0c.
Proof. vm_refl. Qed.
Lemma D_81b0c : decode_any W_81b0c = Some (Auipc 14 223, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b10 : bv 32 := 0x0d473703.
Lemma F_81b10 : fetch_word Asan.M.loaded_segments (0x81b60 : word) = Some W_81b10.
Proof. vm_refl. Qed.
Lemma D_81b10 : decode_any W_81b10 = Some (Load SZ8 true 14 14 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b14 : bv 32 := 0x00073283.
Lemma F_81b14 : fetch_word Asan.M.loaded_segments (0x81b64 : word) = Some W_81b14.
Proof. vm_refl. Qed.
Lemma D_81b14 : decode_any W_81b14 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b18 : bv 32 := 0x0032d713.
Lemma F_81b18 : fetch_word Asan.M.loaded_segments (0x81b68 : word) = Some W_81b18.
Proof. vm_refl. Qed.
Lemma D_81b18 : decode_any W_81b18 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b1c : bv 32 := 0x00b708b3.
Lemma F_81b1c : fetch_word Asan.M.loaded_segments (0x81b6c : word) = Some W_81b1c.
Proof. vm_refl. Qed.
Lemma D_81b1c : decode_any W_81b1c = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b20 : bv 32 := 0x00a2ea63.
Lemma F_81b20 : fetch_word Asan.M.loaded_segments (0x81b70 : word) = Some W_81b20.
Proof. vm_refl. Qed.
Lemma D_81b20 : decode_any W_81b20 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b24 : bv 32 := 0x00a8f863.
Lemma F_81b24 : fetch_word Asan.M.loaded_segments (0x81b74 : word) = Some W_81b24.
Proof. vm_refl. Qed.
Lemma D_81b24 : decode_any W_81b24 = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b28 : bv 32 := 0x00355513.
Lemma F_81b28 : fetch_word Asan.M.loaded_segments (0x81b78 : word) = Some W_81b28.
Proof. vm_refl. Qed.
Lemma D_81b28 : decode_any W_81b28 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b2c : bv 32 := 0x00a58533.
Lemma F_81b2c : fetch_word Asan.M.loaded_segments (0x81b7c : word) = Some W_81b2c.
Proof. vm_refl. Qed.
Lemma D_81b2c : decode_any W_81b2c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b30 : bv 32 := 0x00008067.
Lemma F_81b30 : fetch_word Asan.M.loaded_segments (0x81b80 : word) = Some W_81b30.
Proof. vm_refl. Qed.
Lemma D_81b30 : decode_any W_81b30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d70 : bv 32 := 0x0100006f.
Lemma F_81d70 : fetch_word Asan.M.loaded_segments (0x81dc0 : word) = Some W_81d70.
Proof. vm_refl. Qed.
Lemma D_81d70 : decode_any W_81d70 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d74 : bv 32 := 0x1dc0006f.
Lemma F_81d74 : fetch_word Asan.M.loaded_segments (0x81dc4 : word) = Some W_81d74.
Proof. vm_refl. Qed.
Lemma D_81d74 : decode_any W_81d74 = Some (Jal 0 476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d7c : bv 32 := 0x7400006f.
Lemma F_81d7c : fetch_word Asan.M.loaded_segments (0x81dcc : word) = Some W_81d7c.
Proof. vm_refl. Qed.
Lemma D_81d7c : decode_any W_81d7c = Some (Jal 0 1856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d80 : bv 32 := 0x81010113.
Lemma F_81d80 : fetch_word Asan.M.loaded_segments (0x81dd0 : word) = Some W_81d80.
Proof. vm_refl. Qed.
Lemma D_81d80 : decode_any W_81d80 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d84 : bv 32 := 0x7e113423.
Lemma F_81d84 : fetch_word Asan.M.loaded_segments (0x81dd4 : word) = Some W_81d84.
Proof. vm_refl. Qed.
Lemma D_81d84 : decode_any W_81d84 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d88 : bv 32 := 0x7e813023.
Lemma F_81d88 : fetch_word Asan.M.loaded_segments (0x81dd8 : word) = Some W_81d88.
Proof. vm_refl. Qed.
Lemma D_81d88 : decode_any W_81d88 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d8c : bv 32 := 0x7c913c23.
Lemma F_81d8c : fetch_word Asan.M.loaded_segments (0x81ddc : word) = Some W_81d8c.
Proof. vm_refl. Qed.
Lemma D_81d8c : decode_any W_81d8c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d90 : bv 32 := 0x7d213823.
Lemma F_81d90 : fetch_word Asan.M.loaded_segments (0x81de0 : word) = Some W_81d90.
Proof. vm_refl. Qed.
Lemma D_81d90 : decode_any W_81d90 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d94 : bv 32 := 0x7d313423.
Lemma F_81d94 : fetch_word Asan.M.loaded_segments (0x81de4 : word) = Some W_81d94.
Proof. vm_refl. Qed.
Lemma D_81d94 : decode_any W_81d94 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d98 : bv 32 := 0x7d413023.
Lemma F_81d98 : fetch_word Asan.M.loaded_segments (0x81de8 : word) = Some W_81d98.
Proof. vm_refl. Qed.
Lemma D_81d98 : decode_any W_81d98 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81d9c : bv 32 := 0x7b513c23.
Lemma F_81d9c : fetch_word Asan.M.loaded_segments (0x81dec : word) = Some W_81d9c.
Proof. vm_refl. Qed.
Lemma D_81d9c : decode_any W_81d9c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81da0 : bv 32 := 0x7f010413.
Lemma F_81da0 : fetch_word Asan.M.loaded_segments (0x81df0 : word) = Some W_81da0.
Proof. vm_refl. Qed.
Lemma D_81da0 : decode_any W_81da0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81da4 : bv 32 := 0xfa010113.
Lemma F_81da4 : fetch_word Asan.M.loaded_segments (0x81df4 : word) = Some W_81da4.
Proof. vm_refl. Qed.
Lemma D_81da4 : decode_any W_81da4 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81da8 : bv 32 := 0x00008913.
Lemma F_81da8 : fetch_word Asan.M.loaded_segments (0x81df8 : word) = Some W_81da8.
Proof. vm_refl. Qed.
Lemma D_81da8 : decode_any W_81da8 = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dac : bv 32 := 0x00050493.
Lemma F_81dac : fetch_word Asan.M.loaded_segments (0x81dfc : word) = Some W_81dac.
Proof. vm_refl. Qed.
Lemma D_81dac : decode_any W_81dac = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81db0 : bv 32 := 0x10c0c0ef.
Lemma F_81db0 : fetch_word Asan.M.loaded_segments (0x81e00 : word) = Some W_81db0.
Proof. vm_refl. Qed.
Lemma D_81db0 : decode_any W_81db0 = Some (Jal 1 49420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81db4 : bv 32 := 0x02f4d593.
Lemma F_81db4 : fetch_word Asan.M.loaded_segments (0x81e04 : word) = Some W_81db4.
Proof. vm_refl. Qed.
Lemma D_81db4 : decode_any W_81db4 = Some (ShiftImm ALU_SRL 11 9 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81db8 : bv 32 := 0x0a059063.
Lemma F_81db8 : fetch_word Asan.M.loaded_segments (0x81e08 : word) = Some W_81db8.
Proof. vm_refl. Qed.
Lemma D_81db8 : decode_any W_81db8 = Some (Branch BC_NE 11 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dbc : bv 32 := 0x0204d593.
Lemma F_81dbc : fetch_word Asan.M.loaded_segments (0x81e0c : word) = Some W_81dbc.
Proof. vm_refl. Qed.
Lemma D_81dbc : decode_any W_81dbc = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dc0 : bv 32 := 0x00359613.
Lemma F_81dc0 : fetch_word Asan.M.loaded_segments (0x81e10 : word) = Some W_81dc0.
Proof. vm_refl. Qed.
Lemma D_81dc0 : decode_any W_81dc0 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dc4 : bv 32 := 0x00c50633.
Lemma F_81dc4 : fetch_word Asan.M.loaded_segments (0x81e14 : word) = Some W_81dc4.
Proof. vm_refl. Qed.
Lemma D_81dc4 : decode_any W_81dc4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dc8 : bv 32 := 0x00863683.
Lemma F_81dc8 : fetch_word Asan.M.loaded_segments (0x81e18 : word) = Some W_81dc8.
Proof. vm_refl. Qed.
Lemma D_81dc8 : decode_any W_81dc8 = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dcc : bv 32 := 0x0230000f.
Lemma F_81dcc : fetch_word Asan.M.loaded_segments (0x81e1c : word) = Some W_81dcc.
Proof. vm_refl. Qed.
Lemma D_81dcc : decode_any W_81dcc = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81dd0 : bv 32 := 0x08068463.
Lemma F_81dd0 : fetch_word Asan.M.loaded_segments (0x81e20 : word) = Some W_81dd0.
Proof. vm_refl. Qed.
Lemma D_81dd0 : decode_any W_81dd0 = Some (Branch BC_EQ 13 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e58 : bv 32 := 0x80040a13.
Lemma F_81e58 : fetch_word Asan.M.loaded_segments (0x81ea8 : word) = Some W_81e58.
Proof. vm_refl. Qed.
Lemma D_81e58 : decode_any W_81e58 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e5c : bv 32 := 0xfb0a0a13.
Lemma F_81e5c : fetch_word Asan.M.loaded_segments (0x81eac : word) = Some W_81e5c.
Proof. vm_refl. Qed.
Lemma D_81e5c : decode_any W_81e5c = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e60 : bv 32 := 0x80040513.
Lemma F_81e60 : fetch_word Asan.M.loaded_segments (0x81eb0 : word) = Some W_81e60.
Proof. vm_refl. Qed.
Lemma D_81e60 : decode_any W_81e60 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e64 : bv 32 := 0xfc050513.
Lemma F_81e64 : fetch_word Asan.M.loaded_segments (0x81eb4 : word) = Some W_81e64.
Proof. vm_refl. Qed.
Lemma D_81e64 : decode_any W_81e64 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e68 : bv 32 := 0x7ffa0a93.
Lemma F_81e68 : fetch_word Asan.M.loaded_segments (0x81eb8 : word) = Some W_81e68.
Proof. vm_refl. Qed.
Lemma D_81e68 : decode_any W_81e68 = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e6c : bv 32 := 0x000ab4a3.
Lemma F_81e6c : fetch_word Asan.M.loaded_segments (0x81ebc : word) = Some W_81e6c.
Proof. vm_refl. Qed.
Lemma D_81e6c : decode_any W_81e6c = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e70 : bv 32 := 0x00aa3023.
Lemma F_81e70 : fetch_word Asan.M.loaded_segments (0x81ec0 : word) = Some W_81e70.
Proof. vm_refl. Qed.
Lemma D_81e70 : decode_any W_81e70 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e74 : bv 32 := 0x000a3423.
Lemma F_81e74 : fetch_word Asan.M.loaded_segments (0x81ec4 : word) = Some W_81e74.
Proof. vm_refl. Qed.
Lemma D_81e74 : decode_any W_81e74 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e78 : bv 32 := 0x550080ef.
Lemma F_81e78 : fetch_word Asan.M.loaded_segments (0x81ec8 : word) = Some W_81e78.
Proof. vm_refl. Qed.
Lemma D_81e78 : decode_any W_81e78 = Some (Jal 1 34128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e7c : bv 32 := 0x00200593.
Lemma F_81e7c : fetch_word Asan.M.loaded_segments (0x81ecc : word) = Some W_81e7c.
Proof. vm_refl. Qed.
Lemma D_81e7c : decode_any W_81e7c = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81e80 : bv 32 := 0x02a5ea63.
Lemma F_81e80 : fetch_word Asan.M.loaded_segments (0x81ed0 : word) = Some W_81e80.
Proof. vm_refl. Qed.
Lemma D_81e80 : decode_any W_81e80 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81eb4 : bv 32 := 0x7f1200ef.
Lemma F_81eb4 : fetch_word Asan.M.loaded_segments (0x81f04 : word) = Some W_81eb4.
Proof. vm_refl. Qed.
Lemma D_81eb4 : decode_any W_81eb4 = Some (Jal 1 135152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81eb8 : bv 32 := 0x000df597.
Lemma F_81eb8 : fetch_word Asan.M.loaded_segments (0x81f08 : word) = Some W_81eb8.
Proof. vm_refl. Qed.
Lemma D_81eb8 : decode_any W_81eb8 = Some (Auipc 11 223, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ebc : bv 32 := 0xd005b583.
Lemma F_81ebc : fetch_word Asan.M.loaded_segments (0x81f0c : word) = Some W_81ebc.
Proof. vm_refl. Qed.
Lemma D_81ebc : decode_any W_81ebc = Some (Load SZ8 true 11 11 3328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ec0 : bv 32 := 0x0225c983.
Lemma F_81ec0 : fetch_word Asan.M.loaded_segments (0x81f10 : word) = Some W_81ec0.
Proof. vm_refl. Qed.
Lemma D_81ec0 : decode_any W_81ec0 = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ec4 : bv 32 := 0x00050913.
Lemma F_81ec4 : fetch_word Asan.M.loaded_segments (0x81f14 : word) = Some W_81ec4.
Proof. vm_refl. Qed.
Lemma D_81ec4 : decode_any W_81ec4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ec8 : bv 32 := 0x500080ef.
Lemma F_81ec8 : fetch_word Asan.M.loaded_segments (0x81f18 : word) = Some W_81ec8.
Proof. vm_refl. Qed.
Lemma D_81ec8 : decode_any W_81ec8 = Some (Jal 1 34048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ecc : bv 32 := 0x00050793.
Lemma F_81ecc : fetch_word Asan.M.loaded_segments (0x81f1c : word) = Some W_81ecc.
Proof. vm_refl. Qed.
Lemma D_81ecc : decode_any W_81ecc = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ed0 : bv 32 := 0x00153513.
Lemma F_81ed0 : fetch_word Asan.M.loaded_segments (0x81f20 : word) = Some W_81ed0.
Proof. vm_refl. Qed.
Lemma D_81ed0 : decode_any W_81ed0 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ed4 : bv 32 := 0xfff50513.
Lemma F_81ed4 : fetch_word Asan.M.loaded_segments (0x81f24 : word) = Some W_81ed4.
Proof. vm_refl. Qed.
Lemma D_81ed4 : decode_any W_81ed4 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ed8 : bv 32 := 0x008575b3.
Lemma F_81ed8 : fetch_word Asan.M.loaded_segments (0x81f28 : word) = Some W_81ed8.
Proof. vm_refl. Qed.
Lemma D_81ed8 : decode_any W_81ed8 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81edc : bv 32 := 0x00100513.
Lemma F_81edc : fetch_word Asan.M.loaded_segments (0x81f2c : word) = Some W_81edc.
Proof. vm_refl. Qed.
Lemma D_81edc : decode_any W_81edc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ee0 : bv 32 := 0x00bab4a3.
Lemma F_81ee0 : fetch_word Asan.M.loaded_segments (0x81f30 : word) = Some W_81ee0.
Proof. vm_refl. Qed.
Lemma D_81ee0 : decode_any W_81ee0 = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ee4 : bv 32 := 0x00f56a63.
Lemma F_81ee4 : fetch_word Asan.M.loaded_segments (0x81f34 : word) = Some W_81ee4.
Proof. vm_refl. Qed.
Lemma D_81ee4 : decode_any W_81ee4 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ef8 : bv 32 := 0x80040513.
Lemma F_81ef8 : fetch_word Asan.M.loaded_segments (0x81f48 : word) = Some W_81ef8.
Proof. vm_refl. Qed.
Lemma D_81ef8 : decode_any W_81ef8 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81efc : bv 32 := 0xfb050513.
Lemma F_81efc : fetch_word Asan.M.loaded_segments (0x81f4c : word) = Some W_81efc.
Proof. vm_refl. Qed.
Lemma D_81efc : decode_any W_81efc = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f00 : bv 32 := 0x00090593.
Lemma F_81f00 : fetch_word Asan.M.loaded_segments (0x81f50 : word) = Some W_81f00.
Proof. vm_refl. Qed.
Lemma D_81f00 : decode_any W_81f00 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f04 : bv 32 := 0x00040613.
Lemma F_81f04 : fetch_word Asan.M.loaded_segments (0x81f54 : word) = Some W_81f04.
Proof. vm_refl. Qed.
Lemma D_81f04 : decode_any W_81f04 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f08 : bv 32 := 0x00000693.
Lemma F_81f08 : fetch_word Asan.M.loaded_segments (0x81f58 : word) = Some W_81f08.
Proof. vm_refl. Qed.
Lemma D_81f08 : decode_any W_81f08 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f0c : bv 32 := 0x00098713.
Lemma F_81f0c : fetch_word Asan.M.loaded_segments (0x81f5c : word) = Some W_81f0c.
Proof. vm_refl. Qed.
Lemma D_81f0c : decode_any W_81f0c = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f10 : bv 32 := 0x4c8080ef.
Lemma F_81f10 : fetch_word Asan.M.loaded_segments (0x81f60 : word) = Some W_81f10.
Proof. vm_refl. Qed.
Lemma D_81f10 : decode_any W_81f10 = Some (Jal 1 33992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f14 : bv 32 := 0x80040593.
Lemma F_81f14 : fetch_word Asan.M.loaded_segments (0x81f64 : word) = Some W_81f14.
Proof. vm_refl. Qed.
Lemma D_81f14 : decode_any W_81f14 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f18 : bv 32 := 0xfb058593.
Lemma F_81f18 : fetch_word Asan.M.loaded_segments (0x81f68 : word) = Some W_81f18.
Proof. vm_refl. Qed.
Lemma D_81f18 : decode_any W_81f18 = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f1c : bv 32 := 0x00100613.
Lemma F_81f1c : fetch_word Asan.M.loaded_segments (0x81f6c : word) = Some W_81f1c.
Proof. vm_refl. Qed.
Lemma D_81f1c : decode_any W_81f1c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f20 : bv 32 := 0x00048513.
Lemma F_81f20 : fetch_word Asan.M.loaded_segments (0x81f70 : word) = Some W_81f20.
Proof. vm_refl. Qed.
Lemma D_81f20 : decode_any W_81f20 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f24 : bv 32 := 0xd78d80ef.
Lemma F_81f24 : fetch_word Asan.M.loaded_segments (0x81f74 : word) = Some W_81f24.
Proof. vm_refl. Qed.
Lemma D_81f24 : decode_any W_81f24 = Some (Jal 1 1934712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f28 : bv 32 := 0x06010113.
Lemma F_81f28 : fetch_word Asan.M.loaded_segments (0x81f78 : word) = Some W_81f28.
Proof. vm_refl. Qed.
Lemma D_81f28 : decode_any W_81f28 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f2c : bv 32 := 0x7e813083.
Lemma F_81f2c : fetch_word Asan.M.loaded_segments (0x81f7c : word) = Some W_81f2c.
Proof. vm_refl. Qed.
Lemma D_81f2c : decode_any W_81f2c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f30 : bv 32 := 0x7e013403.
Lemma F_81f30 : fetch_word Asan.M.loaded_segments (0x81f80 : word) = Some W_81f30.
Proof. vm_refl. Qed.
Lemma D_81f30 : decode_any W_81f30 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f34 : bv 32 := 0x7d813483.
Lemma F_81f34 : fetch_word Asan.M.loaded_segments (0x81f84 : word) = Some W_81f34.
Proof. vm_refl. Qed.
Lemma D_81f34 : decode_any W_81f34 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f38 : bv 32 := 0x7d013903.
Lemma F_81f38 : fetch_word Asan.M.loaded_segments (0x81f88 : word) = Some W_81f38.
Proof. vm_refl. Qed.
Lemma D_81f38 : decode_any W_81f38 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f3c : bv 32 := 0x7c813983.
Lemma F_81f3c : fetch_word Asan.M.loaded_segments (0x81f8c : word) = Some W_81f3c.
Proof. vm_refl. Qed.
Lemma D_81f3c : decode_any W_81f3c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f40 : bv 32 := 0x7c013a03.
Lemma F_81f40 : fetch_word Asan.M.loaded_segments (0x81f90 : word) = Some W_81f40.
Proof. vm_refl. Qed.
Lemma D_81f40 : decode_any W_81f40 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f44 : bv 32 := 0x7b813a83.
Lemma F_81f44 : fetch_word Asan.M.loaded_segments (0x81f94 : word) = Some W_81f44.
Proof. vm_refl. Qed.
Lemma D_81f44 : decode_any W_81f44 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f48 : bv 32 := 0x7f010113.
Lemma F_81f48 : fetch_word Asan.M.loaded_segments (0x81f98 : word) = Some W_81f48.
Proof. vm_refl. Qed.
Lemma D_81f48 : decode_any W_81f48 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f4c : bv 32 := 0x00008067.
Lemma F_81f4c : fetch_word Asan.M.loaded_segments (0x81f9c : word) = Some W_81f4c.
Proof. vm_refl. Qed.
Lemma D_81f4c : decode_any W_81f4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f50 : bv 32 := 0x81010113.
Lemma F_81f50 : fetch_word Asan.M.loaded_segments (0x81fa0 : word) = Some W_81f50.
Proof. vm_refl. Qed.
Lemma D_81f50 : decode_any W_81f50 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f54 : bv 32 := 0x7e113423.
Lemma F_81f54 : fetch_word Asan.M.loaded_segments (0x81fa4 : word) = Some W_81f54.
Proof. vm_refl. Qed.
Lemma D_81f54 : decode_any W_81f54 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f58 : bv 32 := 0x7e813023.
Lemma F_81f58 : fetch_word Asan.M.loaded_segments (0x81fa8 : word) = Some W_81f58.
Proof. vm_refl. Qed.
Lemma D_81f58 : decode_any W_81f58 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f5c : bv 32 := 0x7c913c23.
Lemma F_81f5c : fetch_word Asan.M.loaded_segments (0x81fac : word) = Some W_81f5c.
Proof. vm_refl. Qed.
Lemma D_81f5c : decode_any W_81f5c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f60 : bv 32 := 0x7d213823.
Lemma F_81f60 : fetch_word Asan.M.loaded_segments (0x81fb0 : word) = Some W_81f60.
Proof. vm_refl. Qed.
Lemma D_81f60 : decode_any W_81f60 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f64 : bv 32 := 0x7d313423.
Lemma F_81f64 : fetch_word Asan.M.loaded_segments (0x81fb4 : word) = Some W_81f64.
Proof. vm_refl. Qed.
Lemma D_81f64 : decode_any W_81f64 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f68 : bv 32 := 0x7d413023.
Lemma F_81f68 : fetch_word Asan.M.loaded_segments (0x81fb8 : word) = Some W_81f68.
Proof. vm_refl. Qed.
Lemma D_81f68 : decode_any W_81f68 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f6c : bv 32 := 0x7b513c23.
Lemma F_81f6c : fetch_word Asan.M.loaded_segments (0x81fbc : word) = Some W_81f6c.
Proof. vm_refl. Qed.
Lemma D_81f6c : decode_any W_81f6c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f70 : bv 32 := 0x7f010413.
Lemma F_81f70 : fetch_word Asan.M.loaded_segments (0x81fc0 : word) = Some W_81f70.
Proof. vm_refl. Qed.
Lemma D_81f70 : decode_any W_81f70 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f74 : bv 32 := 0xfa010113.
Lemma F_81f74 : fetch_word Asan.M.loaded_segments (0x81fc4 : word) = Some W_81f74.
Proof. vm_refl. Qed.
Lemma D_81f74 : decode_any W_81f74 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f78 : bv 32 := 0x00008913.
Lemma F_81f78 : fetch_word Asan.M.loaded_segments (0x81fc8 : word) = Some W_81f78.
Proof. vm_refl. Qed.
Lemma D_81f78 : decode_any W_81f78 = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f7c : bv 32 := 0x00050493.
Lemma F_81f7c : fetch_word Asan.M.loaded_segments (0x81fcc : word) = Some W_81f7c.
Proof. vm_refl. Qed.
Lemma D_81f7c : decode_any W_81f7c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f80 : bv 32 := 0x6c0070ef.
Lemma F_81f80 : fetch_word Asan.M.loaded_segments (0x81fd0 : word) = Some W_81f80.
Proof. vm_refl. Qed.
Lemma D_81f80 : decode_any W_81f80 = Some (Jal 1 30400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f84 : bv 32 := 0x06050063.
Lemma F_81f84 : fetch_word Asan.M.loaded_segments (0x81fd4 : word) = Some W_81f84.
Proof. vm_refl. Qed.
Lemma D_81f84 : decode_any W_81f84 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f88 : bv 32 := 0x80040a13.
Lemma F_81f88 : fetch_word Asan.M.loaded_segments (0x81fd8 : word) = Some W_81f88.
Proof. vm_refl. Qed.
Lemma D_81f88 : decode_any W_81f88 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f8c : bv 32 := 0xfb0a0a13.
Lemma F_81f8c : fetch_word Asan.M.loaded_segments (0x81fdc : word) = Some W_81f8c.
Proof. vm_refl. Qed.
Lemma D_81f8c : decode_any W_81f8c = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f90 : bv 32 := 0x80040513.
Lemma F_81f90 : fetch_word Asan.M.loaded_segments (0x81fe0 : word) = Some W_81f90.
Proof. vm_refl. Qed.
Lemma D_81f90 : decode_any W_81f90 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f94 : bv 32 := 0xfc050513.
Lemma F_81f94 : fetch_word Asan.M.loaded_segments (0x81fe4 : word) = Some W_81f94.
Proof. vm_refl. Qed.
Lemma D_81f94 : decode_any W_81f94 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f98 : bv 32 := 0x7ffa0a93.
Lemma F_81f98 : fetch_word Asan.M.loaded_segments (0x81fe8 : word) = Some W_81f98.
Proof. vm_refl. Qed.
Lemma D_81f98 : decode_any W_81f98 = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81f9c : bv 32 := 0x000ab4a3.
Lemma F_81f9c : fetch_word Asan.M.loaded_segments (0x81fec : word) = Some W_81f9c.
Proof. vm_refl. Qed.
Lemma D_81f9c : decode_any W_81f9c = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fa0 : bv 32 := 0x00aa3023.
Lemma F_81fa0 : fetch_word Asan.M.loaded_segments (0x81ff0 : word) = Some W_81fa0.
Proof. vm_refl. Qed.
Lemma D_81fa0 : decode_any W_81fa0 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fa4 : bv 32 := 0x000a3423.
Lemma F_81fa4 : fetch_word Asan.M.loaded_segments (0x81ff4 : word) = Some W_81fa4.
Proof. vm_refl. Qed.
Lemma D_81fa4 : decode_any W_81fa4 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fa8 : bv 32 := 0x420080ef.
Lemma F_81fa8 : fetch_word Asan.M.loaded_segments (0x81ff8 : word) = Some W_81fa8.
Proof. vm_refl. Qed.
Lemma D_81fa8 : decode_any W_81fa8 = Some (Jal 1 33824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fac : bv 32 := 0x00200593.
Lemma F_81fac : fetch_word Asan.M.loaded_segments (0x81ffc : word) = Some W_81fac.
Proof. vm_refl. Qed.
Lemma D_81fac : decode_any W_81fac = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81fb0 : bv 32 := 0x06a5e263.
Lemma F_81fb0 : fetch_word Asan.M.loaded_segments (0x82000 : word) = Some W_81fb0.
Proof. vm_refl. Qed.
Lemma D_81fb0 : decode_any W_81fb0 = Some (Branch BC_LTU 11 10 100, 4%Z).
Proof. vm_refl. Qed.

