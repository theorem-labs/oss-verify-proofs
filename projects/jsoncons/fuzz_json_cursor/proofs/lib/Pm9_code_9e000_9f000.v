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

Definition W_9ef20 : bv 32 := 0xfc010113.
Lemma F_9ef20 : fetch_word AsanUbsan.M.loaded_segments (0x9ef68 : word) = Some W_9ef20.
Proof. vm_refl. Qed.
Lemma D_9ef20 : decode_any W_9ef20 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef24 : bv 32 := 0x02113c23.
Lemma F_9ef24 : fetch_word AsanUbsan.M.loaded_segments (0x9ef6c : word) = Some W_9ef24.
Proof. vm_refl. Qed.
Lemma D_9ef24 : decode_any W_9ef24 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef28 : bv 32 := 0x02813823.
Lemma F_9ef28 : fetch_word AsanUbsan.M.loaded_segments (0x9ef70 : word) = Some W_9ef28.
Proof. vm_refl. Qed.
Lemma D_9ef28 : decode_any W_9ef28 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef2c : bv 32 := 0x02913423.
Lemma F_9ef2c : fetch_word AsanUbsan.M.loaded_segments (0x9ef74 : word) = Some W_9ef2c.
Proof. vm_refl. Qed.
Lemma D_9ef2c : decode_any W_9ef2c = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef30 : bv 32 := 0x03213023.
Lemma F_9ef30 : fetch_word AsanUbsan.M.loaded_segments (0x9ef78 : word) = Some W_9ef30.
Proof. vm_refl. Qed.
Lemma D_9ef30 : decode_any W_9ef30 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef34 : bv 32 := 0x01313c23.
Lemma F_9ef34 : fetch_word AsanUbsan.M.loaded_segments (0x9ef7c : word) = Some W_9ef34.
Proof. vm_refl. Qed.
Lemma D_9ef34 : decode_any W_9ef34 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef38 : bv 32 := 0x01413823.
Lemma F_9ef38 : fetch_word AsanUbsan.M.loaded_segments (0x9ef80 : word) = Some W_9ef38.
Proof. vm_refl. Qed.
Lemma D_9ef38 : decode_any W_9ef38 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef3c : bv 32 := 0x01513423.
Lemma F_9ef3c : fetch_word AsanUbsan.M.loaded_segments (0x9ef84 : word) = Some W_9ef3c.
Proof. vm_refl. Qed.
Lemma D_9ef3c : decode_any W_9ef3c = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef40 : bv 32 := 0x00058993.
Lemma F_9ef40 : fetch_word AsanUbsan.M.loaded_segments (0x9ef88 : word) = Some W_9ef40.
Proof. vm_refl. Qed.
Lemma D_9ef40 : decode_any W_9ef40 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef44 : bv 32 := 0x0085aa03.
Lemma F_9ef44 : fetch_word AsanUbsan.M.loaded_segments (0x9ef8c : word) = Some W_9ef44.
Proof. vm_refl. Qed.
Lemma D_9ef44 : decode_any W_9ef44 = Some (Load SZ4 true 20 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef48 : bv 32 := 0x00c5aa83.
Lemma F_9ef48 : fetch_word AsanUbsan.M.loaded_segments (0x9ef90 : word) = Some W_9ef48.
Proof. vm_refl. Qed.
Lemma D_9ef48 : decode_any W_9ef48 = Some (Load SZ4 true 21 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef4c : bv 32 := 0x015a65b3.
Lemma F_9ef4c : fetch_word AsanUbsan.M.loaded_segments (0x9ef94 : word) = Some W_9ef4c.
Proof. vm_refl. Qed.
Lemma D_9ef4c : decode_any W_9ef4c = Some (Op ALU_OR 11 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef50 : bv 32 := 0x00059663.
Lemma F_9ef50 : fetch_word AsanUbsan.M.loaded_segments (0x9ef98 : word) = Some W_9ef50.
Proof. vm_refl. Qed.
Lemma D_9ef50 : decode_any W_9ef50 = Some (Branch BC_NE 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef5c : bv 32 := 0x00050493.
Lemma F_9ef5c : fetch_word AsanUbsan.M.loaded_segments (0x9efa4 : word) = Some W_9ef5c.
Proof. vm_refl. Qed.
Lemma D_9ef5c : decode_any W_9ef5c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef60 : bv 32 := 0x10000513.
Lemma F_9ef60 : fetch_word AsanUbsan.M.loaded_segments (0x9efa8 : word) = Some W_9ef60.
Proof. vm_refl. Qed.
Lemma D_9ef60 : decode_any W_9ef60 = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef64 : bv 32 := 0x0aaafe63.
Lemma F_9ef64 : fetch_word AsanUbsan.M.loaded_segments (0x9efac : word) = Some W_9ef64.
Proof. vm_refl. Qed.
Lemma D_9ef64 : decode_any W_9ef64 = Some (Branch BC_GEU 21 10 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef68 : bv 32 := 0x00060413.
Lemma F_9ef68 : fetch_word AsanUbsan.M.loaded_segments (0x9efb0 : word) = Some W_9ef68.
Proof. vm_refl. Qed.
Lemma D_9ef68 : decode_any W_9ef68 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef6c : bv 32 := 0x0ff00513.
Lemma F_9ef6c : fetch_word AsanUbsan.M.loaded_segments (0x9efb4 : word) = Some W_9ef6c.
Proof. vm_refl. Qed.
Lemma D_9ef6c : decode_any W_9ef6c = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef70 : bv 32 := 0x00aa6463.
Lemma F_9ef70 : fetch_word AsanUbsan.M.loaded_segments (0x9efb8 : word) = Some W_9ef70.
Proof. vm_refl. Qed.
Lemma D_9ef70 : decode_any W_9ef70 = Some (Branch BC_LTU 20 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef78 : bv 32 := 0x00013023.
Lemma F_9ef78 : fetch_word AsanUbsan.M.loaded_segments (0x9efc0 : word) = Some W_9ef78.
Proof. vm_refl. Qed.
Lemma D_9ef78 : decode_any W_9ef78 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef7c : bv 32 := 0x00043023.
Lemma F_9ef7c : fetch_word AsanUbsan.M.loaded_segments (0x9efc4 : word) = Some W_9ef7c.
Proof. vm_refl. Qed.
Lemma D_9ef7c : decode_any W_9ef7c = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef80 : bv 32 := 0x001a0913.
Lemma F_9ef80 : fetch_word AsanUbsan.M.loaded_segments (0x9efc8 : word) = Some W_9ef80.
Proof. vm_refl. Qed.
Lemma D_9ef80 : decode_any W_9ef80 = Some (OpImm ALU_ADD 18 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef84 : bv 32 := 0x00010613.
Lemma F_9ef84 : fetch_word AsanUbsan.M.loaded_segments (0x9efcc : word) = Some W_9ef84.
Proof. vm_refl. Qed.
Lemma D_9ef84 : decode_any W_9ef84 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef88 : bv 32 := 0x00048513.
Lemma F_9ef88 : fetch_word AsanUbsan.M.loaded_segments (0x9efd0 : word) = Some W_9ef88.
Proof. vm_refl. Qed.
Lemma D_9ef88 : decode_any W_9ef88 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef8c : bv 32 := 0x00090593.
Lemma F_9ef8c : fetch_word AsanUbsan.M.loaded_segments (0x9efd4 : word) = Some W_9ef8c.
Proof. vm_refl. Qed.
Lemma D_9ef8c : decode_any W_9ef8c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef90 : bv 32 := 0x00040693.
Lemma F_9ef90 : fetch_word AsanUbsan.M.loaded_segments (0x9efd8 : word) = Some W_9ef90.
Proof. vm_refl. Qed.
Lemma D_9ef90 : decode_any W_9ef90 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef94 : bv 32 := 0x0b0000ef.
Lemma F_9ef94 : fetch_word AsanUbsan.M.loaded_segments (0x9efdc : word) = Some W_9ef94.
Proof. vm_refl. Qed.
Lemma D_9ef94 : decode_any W_9ef94 = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef98 : bv 32 := 0x06050263.
Lemma F_9ef98 : fetch_word AsanUbsan.M.loaded_segments (0x9efe0 : word) = Some W_9ef98.
Proof. vm_refl. Qed.
Lemma D_9ef98 : decode_any W_9ef98 = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ef9c : bv 32 := 0x008a961b.
Lemma F_9ef9c : fetch_word AsanUbsan.M.loaded_segments (0x9efe4 : word) = Some W_9ef9c.
Proof. vm_refl. Qed.
Lemma D_9ef9c : decode_any W_9ef9c = Some (ShiftImm32 ALU_SLL 12 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efa0 : bv 32 := 0x0009b583.
Lemma F_9efa0 : fetch_word AsanUbsan.M.loaded_segments (0x9efe8 : word) = Some W_9efa0.
Proof. vm_refl. Qed.
Lemma D_9efa0 : decode_any W_9efa0 = Some (Load SZ8 true 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efa4 : bv 32 := 0x01466633.
Lemma F_9efa4 : fetch_word AsanUbsan.M.loaded_segments (0x9efec : word) = Some W_9efa4.
Proof. vm_refl. Qed.
Lemma D_9efa4 : decode_any W_9efa4 = Some (Op ALU_OR 12 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efa8 : bv 32 := 0x00c53023.
Lemma F_9efa8 : fetch_word AsanUbsan.M.loaded_segments (0x9eff0 : word) = Some W_9efa8.
Proof. vm_refl. Qed.
Lemma D_9efa8 : decode_any W_9efa8 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efac : bv 32 := 0x00850513.
Lemma F_9efac : fetch_word AsanUbsan.M.loaded_segments (0x9eff4 : word) = Some W_9efac.
Proof. vm_refl. Qed.
Lemma D_9efac : decode_any W_9efac = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efb0 : bv 32 := 0x003a1613.
Lemma F_9efb0 : fetch_word AsanUbsan.M.loaded_segments (0x9eff8 : word) = Some W_9efb0.
Proof. vm_refl. Qed.
Lemma D_9efb0 : decode_any W_9efb0 = Some (ShiftImm ALU_SLL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efb4 : bv 32 := 0x989f30ef.
Lemma F_9efb4 : fetch_word AsanUbsan.M.loaded_segments (0x9effc : word) = Some W_9efb4.
Proof. vm_refl. Qed.
Lemma D_9efb4 : decode_any W_9efb4 = Some (Jal 1 2046344, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efb8 : bv 32 := 0x00013503.
Lemma F_9efb8 : fetch_word AsanUbsan.M.loaded_segments (0x9f000 : word) = Some W_9efb8.
Proof. vm_refl. Qed.
Lemma D_9efb8 : decode_any W_9efb8 = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efbc : bv 32 := 0x01055513.
Lemma F_9efbc : fetch_word AsanUbsan.M.loaded_segments (0x9f004 : word) = Some W_9efbc.
Proof. vm_refl. Qed.
Lemma D_9efbc : decode_any W_9efbc = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efc0 : bv 32 := 0xff057513.
Lemma F_9efc0 : fetch_word AsanUbsan.M.loaded_segments (0x9f008 : word) = Some W_9efc0.
Proof. vm_refl. Qed.
Lemma D_9efc0 : decode_any W_9efc0 = Some (OpImm ALU_AND 10 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efc4 : bv 32 := 0x00a48533.
Lemma F_9efc4 : fetch_word AsanUbsan.M.loaded_segments (0x9f00c : word) = Some W_9efc4.
Proof. vm_refl. Qed.
Lemma D_9efc4 : decode_any W_9efc4 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efc8 : bv 32 := 0x01850513.
Lemma F_9efc8 : fetch_word AsanUbsan.M.loaded_segments (0x9f010 : word) = Some W_9efc8.
Proof. vm_refl. Qed.
Lemma D_9efc8 : decode_any W_9efc8 = Some (OpImm ALU_ADD 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efcc : bv 32 := 0x0325252f.
Lemma F_9efcc : fetch_word AsanUbsan.M.loaded_segments (0x9f014 : word) = Some W_9efcc.
Proof. vm_refl. Qed.
Lemma D_9efcc : decode_any W_9efcc = Some (Amo AMO_ADD AW false true 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efd0 : bv 32 := 0x001005b7.
Lemma F_9efd0 : fetch_word AsanUbsan.M.loaded_segments (0x9f018 : word) = Some W_9efd0.
Proof. vm_refl. Qed.
Lemma D_9efd0 : decode_any W_9efd0 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efd4 : bv 32 := 0x02051513.
Lemma F_9efd4 : fetch_word AsanUbsan.M.loaded_segments (0x9f01c : word) = Some W_9efd4.
Proof. vm_refl. Qed.
Lemma D_9efd4 : decode_any W_9efd4 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efd8 : bv 32 := 0x02055513.
Lemma F_9efd8 : fetch_word AsanUbsan.M.loaded_segments (0x9f020 : word) = Some W_9efd8.
Proof. vm_refl. Qed.
Lemma D_9efd8 : decode_any W_9efd8 = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efdc : bv 32 := 0x00a90533.
Lemma F_9efdc : fetch_word AsanUbsan.M.loaded_segments (0x9f024 : word) = Some W_9efdc.
Proof. vm_refl. Qed.
Lemma D_9efdc : decode_any W_9efdc = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efe0 : bv 32 := 0x00043603.
Lemma F_9efe0 : fetch_word AsanUbsan.M.loaded_segments (0x9f028 : word) = Some W_9efe0.
Proof. vm_refl. Qed.
Lemma D_9efe0 : decode_any W_9efe0 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efe4 : bv 32 := 0x00b54533.
Lemma F_9efe4 : fetch_word AsanUbsan.M.loaded_segments (0x9f02c : word) = Some W_9efe4.
Proof. vm_refl. Qed.
Lemma D_9efe4 : decode_any W_9efe4 = Some (Op ALU_XOR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efe8 : bv 32 := 0x00012583.
Lemma F_9efe8 : fetch_word AsanUbsan.M.loaded_segments (0x9f030 : word) = Some W_9efe8.
Proof. vm_refl. Qed.
Lemma D_9efe8 : decode_any W_9efe8 = Some (Load SZ4 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9efec : bv 32 := 0x00153513.
Lemma F_9efec : fetch_word AsanUbsan.M.loaded_segments (0x9f034 : word) = Some W_9efec.
Proof. vm_refl. Qed.
Lemma D_9efec : decode_any W_9efec = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eff0 : bv 32 := 0x00a60533.
Lemma F_9eff0 : fetch_word AsanUbsan.M.loaded_segments (0x9f038 : word) = Some W_9eff0.
Proof. vm_refl. Qed.
Lemma D_9eff0 : decode_any W_9eff0 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eff4 : bv 32 := 0x00a43023.
Lemma F_9eff4 : fetch_word AsanUbsan.M.loaded_segments (0x9f03c : word) = Some W_9eff4.
Proof. vm_refl. Qed.
Lemma D_9eff4 : decode_any W_9eff4 = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9eff8 : bv 32 := 0x0015851b.
Lemma F_9eff8 : fetch_word AsanUbsan.M.loaded_segments (0x9f040 : word) = Some W_9eff8.
Proof. vm_refl. Qed.
Lemma D_9eff8 : decode_any W_9eff8 = Some (OpImm32 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9effc : bv 32 := 0x03813083.
Lemma F_9effc : fetch_word AsanUbsan.M.loaded_segments (0x9f044 : word) = Some W_9effc.
Proof. vm_refl. Qed.
Lemma D_9effc : decode_any W_9effc = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

