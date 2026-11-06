(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_98b24 : bv 32 := 0xfc010113.
Lemma F_98b24 : fetch_word AsanUbsan.M.loaded_segments (0x98b74 : word) = Some W_98b24.
Proof. vm_refl. Qed.
Lemma D_98b24 : decode_any W_98b24 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b28 : bv 32 := 0x02113c23.
Lemma F_98b28 : fetch_word AsanUbsan.M.loaded_segments (0x98b78 : word) = Some W_98b28.
Proof. vm_refl. Qed.
Lemma D_98b28 : decode_any W_98b28 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b2c : bv 32 := 0x02813823.
Lemma F_98b2c : fetch_word AsanUbsan.M.loaded_segments (0x98b7c : word) = Some W_98b2c.
Proof. vm_refl. Qed.
Lemma D_98b2c : decode_any W_98b2c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b30 : bv 32 := 0x02913423.
Lemma F_98b30 : fetch_word AsanUbsan.M.loaded_segments (0x98b80 : word) = Some W_98b30.
Proof. vm_refl. Qed.
Lemma D_98b30 : decode_any W_98b30 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b34 : bv 32 := 0x03213023.
Lemma F_98b34 : fetch_word AsanUbsan.M.loaded_segments (0x98b84 : word) = Some W_98b34.
Proof. vm_refl. Qed.
Lemma D_98b34 : decode_any W_98b34 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b38 : bv 32 := 0x01313c23.
Lemma F_98b38 : fetch_word AsanUbsan.M.loaded_segments (0x98b88 : word) = Some W_98b38.
Proof. vm_refl. Qed.
Lemma D_98b38 : decode_any W_98b38 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b3c : bv 32 := 0x01413823.
Lemma F_98b3c : fetch_word AsanUbsan.M.loaded_segments (0x98b8c : word) = Some W_98b3c.
Proof. vm_refl. Qed.
Lemma D_98b3c : decode_any W_98b3c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b40 : bv 32 := 0x01513423.
Lemma F_98b40 : fetch_word AsanUbsan.M.loaded_segments (0x98b90 : word) = Some W_98b40.
Proof. vm_refl. Qed.
Lemma D_98b40 : decode_any W_98b40 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b44 : bv 32 := 0x00058993.
Lemma F_98b44 : fetch_word AsanUbsan.M.loaded_segments (0x98b94 : word) = Some W_98b44.
Proof. vm_refl. Qed.
Lemma D_98b44 : decode_any W_98b44 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b48 : bv 32 := 0x0085aa03.
Lemma F_98b48 : fetch_word AsanUbsan.M.loaded_segments (0x98b98 : word) = Some W_98b48.
Proof. vm_refl. Qed.
Lemma D_98b48 : decode_any W_98b48 = Some (Load SZ4 true 20 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b4c : bv 32 := 0x00c5aa83.
Lemma F_98b4c : fetch_word AsanUbsan.M.loaded_segments (0x98b9c : word) = Some W_98b4c.
Proof. vm_refl. Qed.
Lemma D_98b4c : decode_any W_98b4c = Some (Load SZ4 true 21 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b50 : bv 32 := 0x015a65b3.
Lemma F_98b50 : fetch_word AsanUbsan.M.loaded_segments (0x98ba0 : word) = Some W_98b50.
Proof. vm_refl. Qed.
Lemma D_98b50 : decode_any W_98b50 = Some (Op ALU_OR 11 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b54 : bv 32 := 0x00059663.
Lemma F_98b54 : fetch_word AsanUbsan.M.loaded_segments (0x98ba4 : word) = Some W_98b54.
Proof. vm_refl. Qed.
Lemma D_98b54 : decode_any W_98b54 = Some (Branch BC_NE 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b60 : bv 32 := 0x00050493.
Lemma F_98b60 : fetch_word AsanUbsan.M.loaded_segments (0x98bb0 : word) = Some W_98b60.
Proof. vm_refl. Qed.
Lemma D_98b60 : decode_any W_98b60 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b64 : bv 32 := 0x10000513.
Lemma F_98b64 : fetch_word AsanUbsan.M.loaded_segments (0x98bb4 : word) = Some W_98b64.
Proof. vm_refl. Qed.
Lemma D_98b64 : decode_any W_98b64 = Some (OpImm ALU_ADD 10 0 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b68 : bv 32 := 0x0aaafe63.
Lemma F_98b68 : fetch_word AsanUbsan.M.loaded_segments (0x98bb8 : word) = Some W_98b68.
Proof. vm_refl. Qed.
Lemma D_98b68 : decode_any W_98b68 = Some (Branch BC_GEU 21 10 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b6c : bv 32 := 0x00060413.
Lemma F_98b6c : fetch_word AsanUbsan.M.loaded_segments (0x98bbc : word) = Some W_98b6c.
Proof. vm_refl. Qed.
Lemma D_98b6c : decode_any W_98b6c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b70 : bv 32 := 0x0ff00513.
Lemma F_98b70 : fetch_word AsanUbsan.M.loaded_segments (0x98bc0 : word) = Some W_98b70.
Proof. vm_refl. Qed.
Lemma D_98b70 : decode_any W_98b70 = Some (OpImm ALU_ADD 10 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b74 : bv 32 := 0x00aa6463.
Lemma F_98b74 : fetch_word AsanUbsan.M.loaded_segments (0x98bc4 : word) = Some W_98b74.
Proof. vm_refl. Qed.
Lemma D_98b74 : decode_any W_98b74 = Some (Branch BC_LTU 20 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b7c : bv 32 := 0x00013023.
Lemma F_98b7c : fetch_word AsanUbsan.M.loaded_segments (0x98bcc : word) = Some W_98b7c.
Proof. vm_refl. Qed.
Lemma D_98b7c : decode_any W_98b7c = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b80 : bv 32 := 0x00043023.
Lemma F_98b80 : fetch_word AsanUbsan.M.loaded_segments (0x98bd0 : word) = Some W_98b80.
Proof. vm_refl. Qed.
Lemma D_98b80 : decode_any W_98b80 = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b84 : bv 32 := 0x001a0913.
Lemma F_98b84 : fetch_word AsanUbsan.M.loaded_segments (0x98bd4 : word) = Some W_98b84.
Proof. vm_refl. Qed.
Lemma D_98b84 : decode_any W_98b84 = Some (OpImm ALU_ADD 18 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b88 : bv 32 := 0x00010613.
Lemma F_98b88 : fetch_word AsanUbsan.M.loaded_segments (0x98bd8 : word) = Some W_98b88.
Proof. vm_refl. Qed.
Lemma D_98b88 : decode_any W_98b88 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b8c : bv 32 := 0x00048513.
Lemma F_98b8c : fetch_word AsanUbsan.M.loaded_segments (0x98bdc : word) = Some W_98b8c.
Proof. vm_refl. Qed.
Lemma D_98b8c : decode_any W_98b8c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b90 : bv 32 := 0x00090593.
Lemma F_98b90 : fetch_word AsanUbsan.M.loaded_segments (0x98be0 : word) = Some W_98b90.
Proof. vm_refl. Qed.
Lemma D_98b90 : decode_any W_98b90 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b94 : bv 32 := 0x00040693.
Lemma F_98b94 : fetch_word AsanUbsan.M.loaded_segments (0x98be4 : word) = Some W_98b94.
Proof. vm_refl. Qed.
Lemma D_98b94 : decode_any W_98b94 = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b98 : bv 32 := 0x0b0000ef.
Lemma F_98b98 : fetch_word AsanUbsan.M.loaded_segments (0x98be8 : word) = Some W_98b98.
Proof. vm_refl. Qed.
Lemma D_98b98 : decode_any W_98b98 = Some (Jal 1 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_98b9c : bv 32 := 0x06050263.
Lemma F_98b9c : fetch_word AsanUbsan.M.loaded_segments (0x98bec : word) = Some W_98b9c.
Proof. vm_refl. Qed.
Lemma D_98b9c : decode_any W_98b9c = Some (Branch BC_EQ 10 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ba0 : bv 32 := 0x008a961b.
Lemma F_98ba0 : fetch_word AsanUbsan.M.loaded_segments (0x98bf0 : word) = Some W_98ba0.
Proof. vm_refl. Qed.
Lemma D_98ba0 : decode_any W_98ba0 = Some (ShiftImm32 ALU_SLL 12 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ba4 : bv 32 := 0x0009b583.
Lemma F_98ba4 : fetch_word AsanUbsan.M.loaded_segments (0x98bf4 : word) = Some W_98ba4.
Proof. vm_refl. Qed.
Lemma D_98ba4 : decode_any W_98ba4 = Some (Load SZ8 true 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ba8 : bv 32 := 0x01466633.
Lemma F_98ba8 : fetch_word AsanUbsan.M.loaded_segments (0x98bf8 : word) = Some W_98ba8.
Proof. vm_refl. Qed.
Lemma D_98ba8 : decode_any W_98ba8 = Some (Op ALU_OR 12 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bac : bv 32 := 0x00c53023.
Lemma F_98bac : fetch_word AsanUbsan.M.loaded_segments (0x98bfc : word) = Some W_98bac.
Proof. vm_refl. Qed.
Lemma D_98bac : decode_any W_98bac = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bb0 : bv 32 := 0x00850513.
Lemma F_98bb0 : fetch_word AsanUbsan.M.loaded_segments (0x98c00 : word) = Some W_98bb0.
Proof. vm_refl. Qed.
Lemma D_98bb0 : decode_any W_98bb0 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bb4 : bv 32 := 0x003a1613.
Lemma F_98bb4 : fetch_word AsanUbsan.M.loaded_segments (0x98c04 : word) = Some W_98bb4.
Proof. vm_refl. Qed.
Lemma D_98bb4 : decode_any W_98bb4 = Some (ShiftImm ALU_SLL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bb8 : bv 32 := 0x989f30ef.
Lemma F_98bb8 : fetch_word AsanUbsan.M.loaded_segments (0x98c08 : word) = Some W_98bb8.
Proof. vm_refl. Qed.
Lemma D_98bb8 : decode_any W_98bb8 = Some (Jal 1 2046344, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bbc : bv 32 := 0x00013503.
Lemma F_98bbc : fetch_word AsanUbsan.M.loaded_segments (0x98c0c : word) = Some W_98bbc.
Proof. vm_refl. Qed.
Lemma D_98bbc : decode_any W_98bbc = Some (Load SZ8 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bc0 : bv 32 := 0x01055513.
Lemma F_98bc0 : fetch_word AsanUbsan.M.loaded_segments (0x98c10 : word) = Some W_98bc0.
Proof. vm_refl. Qed.
Lemma D_98bc0 : decode_any W_98bc0 = Some (ShiftImm ALU_SRL 10 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bc4 : bv 32 := 0xff057513.
Lemma F_98bc4 : fetch_word AsanUbsan.M.loaded_segments (0x98c14 : word) = Some W_98bc4.
Proof. vm_refl. Qed.
Lemma D_98bc4 : decode_any W_98bc4 = Some (OpImm ALU_AND 10 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bc8 : bv 32 := 0x00a48533.
Lemma F_98bc8 : fetch_word AsanUbsan.M.loaded_segments (0x98c18 : word) = Some W_98bc8.
Proof. vm_refl. Qed.
Lemma D_98bc8 : decode_any W_98bc8 = Some (Op ALU_ADD 10 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bcc : bv 32 := 0x01850513.
Lemma F_98bcc : fetch_word AsanUbsan.M.loaded_segments (0x98c1c : word) = Some W_98bcc.
Proof. vm_refl. Qed.
Lemma D_98bcc : decode_any W_98bcc = Some (OpImm ALU_ADD 10 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bd0 : bv 32 := 0x0325252f.
Lemma F_98bd0 : fetch_word AsanUbsan.M.loaded_segments (0x98c20 : word) = Some W_98bd0.
Proof. vm_refl. Qed.
Lemma D_98bd0 : decode_any W_98bd0 = Some (Amo AMO_ADD AW false true 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bd4 : bv 32 := 0x001005b7.
Lemma F_98bd4 : fetch_word AsanUbsan.M.loaded_segments (0x98c24 : word) = Some W_98bd4.
Proof. vm_refl. Qed.
Lemma D_98bd4 : decode_any W_98bd4 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bd8 : bv 32 := 0x02051513.
Lemma F_98bd8 : fetch_word AsanUbsan.M.loaded_segments (0x98c28 : word) = Some W_98bd8.
Proof. vm_refl. Qed.
Lemma D_98bd8 : decode_any W_98bd8 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bdc : bv 32 := 0x02055513.
Lemma F_98bdc : fetch_word AsanUbsan.M.loaded_segments (0x98c2c : word) = Some W_98bdc.
Proof. vm_refl. Qed.
Lemma D_98bdc : decode_any W_98bdc = Some (ShiftImm ALU_SRL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_98be0 : bv 32 := 0x00a90533.
Lemma F_98be0 : fetch_word AsanUbsan.M.loaded_segments (0x98c30 : word) = Some W_98be0.
Proof. vm_refl. Qed.
Lemma D_98be0 : decode_any W_98be0 = Some (Op ALU_ADD 10 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_98be4 : bv 32 := 0x00043603.
Lemma F_98be4 : fetch_word AsanUbsan.M.loaded_segments (0x98c34 : word) = Some W_98be4.
Proof. vm_refl. Qed.
Lemma D_98be4 : decode_any W_98be4 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98be8 : bv 32 := 0x00b54533.
Lemma F_98be8 : fetch_word AsanUbsan.M.loaded_segments (0x98c38 : word) = Some W_98be8.
Proof. vm_refl. Qed.
Lemma D_98be8 : decode_any W_98be8 = Some (Op ALU_XOR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bec : bv 32 := 0x00012583.
Lemma F_98bec : fetch_word AsanUbsan.M.loaded_segments (0x98c3c : word) = Some W_98bec.
Proof. vm_refl. Qed.
Lemma D_98bec : decode_any W_98bec = Some (Load SZ4 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bf0 : bv 32 := 0x00153513.
Lemma F_98bf0 : fetch_word AsanUbsan.M.loaded_segments (0x98c40 : word) = Some W_98bf0.
Proof. vm_refl. Qed.
Lemma D_98bf0 : decode_any W_98bf0 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bf4 : bv 32 := 0x00a60533.
Lemma F_98bf4 : fetch_word AsanUbsan.M.loaded_segments (0x98c44 : word) = Some W_98bf4.
Proof. vm_refl. Qed.
Lemma D_98bf4 : decode_any W_98bf4 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bf8 : bv 32 := 0x00a43023.
Lemma F_98bf8 : fetch_word AsanUbsan.M.loaded_segments (0x98c48 : word) = Some W_98bf8.
Proof. vm_refl. Qed.
Lemma D_98bf8 : decode_any W_98bf8 = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98bfc : bv 32 := 0x0015851b.
Lemma F_98bfc : fetch_word AsanUbsan.M.loaded_segments (0x98c4c : word) = Some W_98bfc.
Proof. vm_refl. Qed.
Lemma D_98bfc : decode_any W_98bfc = Some (OpImm32 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c00 : bv 32 := 0x03813083.
Lemma F_98c00 : fetch_word AsanUbsan.M.loaded_segments (0x98c50 : word) = Some W_98c00.
Proof. vm_refl. Qed.
Lemma D_98c00 : decode_any W_98c00 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c04 : bv 32 := 0x03013403.
Lemma F_98c04 : fetch_word AsanUbsan.M.loaded_segments (0x98c54 : word) = Some W_98c04.
Proof. vm_refl. Qed.
Lemma D_98c04 : decode_any W_98c04 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c08 : bv 32 := 0x02813483.
Lemma F_98c08 : fetch_word AsanUbsan.M.loaded_segments (0x98c58 : word) = Some W_98c08.
Proof. vm_refl. Qed.
Lemma D_98c08 : decode_any W_98c08 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c0c : bv 32 := 0x02013903.
Lemma F_98c0c : fetch_word AsanUbsan.M.loaded_segments (0x98c5c : word) = Some W_98c0c.
Proof. vm_refl. Qed.
Lemma D_98c0c : decode_any W_98c0c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c10 : bv 32 := 0x01813983.
Lemma F_98c10 : fetch_word AsanUbsan.M.loaded_segments (0x98c60 : word) = Some W_98c10.
Proof. vm_refl. Qed.
Lemma D_98c10 : decode_any W_98c10 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c14 : bv 32 := 0x01013a03.
Lemma F_98c14 : fetch_word AsanUbsan.M.loaded_segments (0x98c64 : word) = Some W_98c14.
Proof. vm_refl. Qed.
Lemma D_98c14 : decode_any W_98c14 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c18 : bv 32 := 0x00813a83.
Lemma F_98c18 : fetch_word AsanUbsan.M.loaded_segments (0x98c68 : word) = Some W_98c18.
Proof. vm_refl. Qed.
Lemma D_98c18 : decode_any W_98c18 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c1c : bv 32 := 0x04010113.
Lemma F_98c1c : fetch_word AsanUbsan.M.loaded_segments (0x98c6c : word) = Some W_98c1c.
Proof. vm_refl. Qed.
Lemma D_98c1c : decode_any W_98c1c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c20 : bv 32 := 0x00008067.
Lemma F_98c20 : fetch_word AsanUbsan.M.loaded_segments (0x98c70 : word) = Some W_98c20.
Proof. vm_refl. Qed.
Lemma D_98c20 : decode_any W_98c20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c48 : bv 32 := 0xff010113.
Lemma F_98c48 : fetch_word AsanUbsan.M.loaded_segments (0x98c98 : word) = Some W_98c48.
Proof. vm_refl. Qed.
Lemma D_98c48 : decode_any W_98c48 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c4c : bv 32 := 0x00113423.
Lemma F_98c4c : fetch_word AsanUbsan.M.loaded_segments (0x98c9c : word) = Some W_98c4c.
Proof. vm_refl. Qed.
Lemma D_98c4c : decode_any W_98c4c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c50 : bv 32 := 0x00813023.
Lemma F_98c50 : fetch_word AsanUbsan.M.loaded_segments (0x98ca0 : word) = Some W_98c50.
Proof. vm_refl. Qed.
Lemma D_98c50 : decode_any W_98c50 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c54 : bv 32 := 0x00058793.
Lemma F_98c54 : fetch_word AsanUbsan.M.loaded_segments (0x98ca4 : word) = Some W_98c54.
Proof. vm_refl. Qed.
Lemma D_98c54 : decode_any W_98c54 = Some (OpImm ALU_ADD 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c58 : bv 32 := 0x00050593.
Lemma F_98c58 : fetch_word AsanUbsan.M.loaded_segments (0x98ca8 : word) = Some W_98c58.
Proof. vm_refl. Qed.
Lemma D_98c58 : decode_any W_98c58 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c5c : bv 32 := 0x00f5342f.
Lemma F_98c5c : fetch_word AsanUbsan.M.loaded_segments (0x98cac : word) = Some W_98c5c.
Proof. vm_refl. Qed.
Lemma D_98c5c : decode_any W_98c5c = Some (Amo AMO_ADD AD false false 8 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c60 : bv 32 := 0xfff78513.
Lemma F_98c60 : fetch_word AsanUbsan.M.loaded_segments (0x98cb0 : word) = Some W_98c60.
Proof. vm_refl. Qed.
Lemma D_98c60 : decode_any W_98c60 = Some (OpImm ALU_ADD 10 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c64 : bv 32 := 0x01445293.
Lemma F_98c64 : fetch_word AsanUbsan.M.loaded_segments (0x98cb4 : word) = Some W_98c64.
Proof. vm_refl. Qed.
Lemma D_98c64 : decode_any W_98c64 = Some (ShiftImm ALU_SRL 5 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c68 : bv 32 := 0x00850733.
Lemma F_98c68 : fetch_word AsanUbsan.M.loaded_segments (0x98cb8 : word) = Some W_98c68.
Proof. vm_refl. Qed.
Lemma D_98c68 : decode_any W_98c68 = Some (Op ALU_ADD 14 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c6c : bv 32 := 0x01475313.
Lemma F_98c6c : fetch_word AsanUbsan.M.loaded_segments (0x98cbc : word) = Some W_98c6c.
Proof. vm_refl. Qed.
Lemma D_98c6c : decode_any W_98c6c = Some (ShiftImm ALU_SRL 6 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c70 : bv 32 := 0x04629863.
Lemma F_98c70 : fetch_word AsanUbsan.M.loaded_segments (0x98cc0 : word) = Some W_98c70.
Proof. vm_refl. Qed.
Lemma D_98c70 : decode_any W_98c70 = Some (Branch BC_NE 5 6 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c74 : bv 32 := 0x02045513.
Lemma F_98c74 : fetch_word AsanUbsan.M.loaded_segments (0x98cc4 : word) = Some W_98c74.
Proof. vm_refl. Qed.
Lemma D_98c74 : decode_any W_98c74 = Some (ShiftImm ALU_SRL 10 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c78 : bv 32 := 0x00050c63.
Lemma F_98c78 : fetch_word AsanUbsan.M.loaded_segments (0x98cc8 : word) = Some W_98c78.
Proof. vm_refl. Qed.
Lemma D_98c78 : decode_any W_98c78 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c90 : bv 32 := 0x00863023.
Lemma F_98c90 : fetch_word AsanUbsan.M.loaded_segments (0x98ce0 : word) = Some W_98c90.
Proof. vm_refl. Qed.
Lemma D_98c90 : decode_any W_98c90 = Some (Store SZ8 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c94 : bv 32 := 0x00429613.
Lemma F_98c94 : fetch_word AsanUbsan.M.loaded_segments (0x98ce4 : word) = Some W_98c94.
Proof. vm_refl. Qed.
Lemma D_98c94 : decode_any W_98c94 = Some (ShiftImm ALU_SLL 12 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c98 : bv 32 := 0x00c58633.
Lemma F_98c98 : fetch_word AsanUbsan.M.loaded_segments (0x98ce8 : word) = Some W_98c98.
Proof. vm_refl. Qed.
Lemma D_98c98 : decode_any W_98c98 = Some (Op ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_98c9c : bv 32 := 0x01063503.
Lemma F_98c9c : fetch_word AsanUbsan.M.loaded_segments (0x98cec : word) = Some W_98c9c.
Proof. vm_refl. Qed.
Lemma D_98c9c : decode_any W_98c9c = Some (Load SZ8 true 10 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ca0 : bv 32 := 0x0a050a63.
Lemma F_98ca0 : fetch_word AsanUbsan.M.loaded_segments (0x98cf0 : word) = Some W_98ca0.
Proof. vm_refl. Qed.
Lemma D_98ca0 : decode_any W_98ca0 = Some (Branch BC_EQ 10 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ca4 : bv 32 := 0x02c41413.
Lemma F_98ca4 : fetch_word AsanUbsan.M.loaded_segments (0x98cf4 : word) = Some W_98ca4.
Proof. vm_refl. Qed.
Lemma D_98ca4 : decode_any W_98ca4 = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_98ca8 : bv 32 := 0x02945413.
Lemma F_98ca8 : fetch_word AsanUbsan.M.loaded_segments (0x98cf8 : word) = Some W_98ca8.
Proof. vm_refl. Qed.
Lemma D_98ca8 : decode_any W_98ca8 = Some (ShiftImm ALU_SRL 8 8 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_98cac : bv 32 := 0x00850533.
Lemma F_98cac : fetch_word AsanUbsan.M.loaded_segments (0x98cfc : word) = Some W_98cac.
Proof. vm_refl. Qed.
Lemma D_98cac : decode_any W_98cac = Some (Op ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98cb0 : bv 32 := 0x00813083.
Lemma F_98cb0 : fetch_word AsanUbsan.M.loaded_segments (0x98d00 : word) = Some W_98cb0.
Proof. vm_refl. Qed.
Lemma D_98cb0 : decode_any W_98cb0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_98cb4 : bv 32 := 0x00013403.
Lemma F_98cb4 : fetch_word AsanUbsan.M.loaded_segments (0x98d04 : word) = Some W_98cb4.
Proof. vm_refl. Qed.
Lemma D_98cb4 : decode_any W_98cb4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_98cb8 : bv 32 := 0x01010113.
Lemma F_98cb8 : fetch_word AsanUbsan.M.loaded_segments (0x98d08 : word) = Some W_98cb8.
Proof. vm_refl. Qed.
Lemma D_98cb8 : decode_any W_98cb8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_98cbc : bv 32 := 0x00008067.
Lemma F_98cbc : fetch_word AsanUbsan.M.loaded_segments (0x98d0c : word) = Some W_98cbc.
Proof. vm_refl. Qed.
Lemma D_98cbc : decode_any W_98cbc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
