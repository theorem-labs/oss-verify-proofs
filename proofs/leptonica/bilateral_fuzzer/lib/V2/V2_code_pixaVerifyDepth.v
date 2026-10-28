(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_18b18 : bv 32 := 0xfc010113.
Lemma F_18b18 : fetch_word Ubsan.M.loaded_segments (0x18b18 : word) = Some W_18b18.
Proof. vm_refl. Qed.
Lemma D_18b18 : decode_any W_18b18 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b1c : bv 32 := 0x02113c23.
Lemma F_18b1c : fetch_word Ubsan.M.loaded_segments (0x18b1c : word) = Some W_18b1c.
Proof. vm_refl. Qed.
Lemma D_18b1c : decode_any W_18b1c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b20 : bv 32 := 0x02813823.
Lemma F_18b20 : fetch_word Ubsan.M.loaded_segments (0x18b20 : word) = Some W_18b20.
Proof. vm_refl. Qed.
Lemma D_18b20 : decode_any W_18b20 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b24 : bv 32 := 0x02913423.
Lemma F_18b24 : fetch_word Ubsan.M.loaded_segments (0x18b24 : word) = Some W_18b24.
Proof. vm_refl. Qed.
Lemma D_18b24 : decode_any W_18b24 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b28 : bv 32 := 0x03213023.
Lemma F_18b28 : fetch_word Ubsan.M.loaded_segments (0x18b28 : word) = Some W_18b28.
Proof. vm_refl. Qed.
Lemma D_18b28 : decode_any W_18b28 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b2c : bv 32 := 0x01313c23.
Lemma F_18b2c : fetch_word Ubsan.M.loaded_segments (0x18b2c : word) = Some W_18b2c.
Proof. vm_refl. Qed.
Lemma D_18b2c : decode_any W_18b2c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b30 : bv 32 := 0x01413823.
Lemma F_18b30 : fetch_word Ubsan.M.loaded_segments (0x18b30 : word) = Some W_18b30.
Proof. vm_refl. Qed.
Lemma D_18b30 : decode_any W_18b30 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b34 : bv 32 := 0x01513423.
Lemma F_18b34 : fetch_word Ubsan.M.loaded_segments (0x18b34 : word) = Some W_18b34.
Proof. vm_refl. Qed.
Lemma D_18b34 : decode_any W_18b34 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b38 : bv 32 := 0x00050413.
Lemma F_18b38 : fetch_word Ubsan.M.loaded_segments (0x18b38 : word) = Some W_18b38.
Proof. vm_refl. Qed.
Lemma D_18b38 : decode_any W_18b38 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b3c : bv 32 := 0x00060863.
Lemma F_18b3c : fetch_word Ubsan.M.loaded_segments (0x18b3c : word) = Some W_18b3c.
Proof. vm_refl. Qed.
Lemma D_18b3c : decode_any W_18b3c = Some (Branch BC_EQ 12 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b40 : bv 32 := 0x00367513.
Lemma F_18b40 : fetch_word Ubsan.M.loaded_segments (0x18b40 : word) = Some W_18b40.
Proof. vm_refl. Qed.
Lemma D_18b40 : decode_any W_18b40 = Some (OpImm ALU_AND 10 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b44 : bv 32 := 0x1c051063.
Lemma F_18b44 : fetch_word Ubsan.M.loaded_segments (0x18b44 : word) = Some W_18b44.
Proof. vm_refl. Qed.
Lemma D_18b44 : decode_any W_18b44 = Some (Branch BC_NE 10 0 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b48 : bv 32 := 0x00062023.
Lemma F_18b48 : fetch_word Ubsan.M.loaded_segments (0x18b48 : word) = Some W_18b48.
Proof. vm_refl. Qed.
Lemma D_18b48 : decode_any W_18b48 = Some (Store SZ4 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b4c : bv 32 := 0x08058c63.
Lemma F_18b4c : fetch_word Ubsan.M.loaded_segments (0x18b4c : word) = Some W_18b4c.
Proof. vm_refl. Qed.
Lemma D_18b4c : decode_any W_18b4c = Some (Branch BC_EQ 11 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b50 : bv 32 := 0x0a040e63.
Lemma F_18b50 : fetch_word Ubsan.M.loaded_segments (0x18b50 : word) = Some W_18b50.
Proof. vm_refl. Qed.
Lemma D_18b50 : decode_any W_18b50 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b54 : bv 32 := 0x00747513.
Lemma F_18b54 : fetch_word Ubsan.M.loaded_segments (0x18b54 : word) = Some W_18b54.
Proof. vm_refl. Qed.
Lemma D_18b54 : decode_any W_18b54 = Some (OpImm ALU_AND 10 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b58 : bv 32 := 0x1a051663.
Lemma F_18b58 : fetch_word Ubsan.M.loaded_segments (0x18b58 : word) = Some W_18b58.
Proof. vm_refl. Qed.
Lemma D_18b58 : decode_any W_18b58 = Some (Branch BC_NE 10 0 428, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b5c : bv 32 := 0x00042a03.
Lemma F_18b5c : fetch_word Ubsan.M.loaded_segments (0x18b5c : word) = Some W_18b5c.
Proof. vm_refl. Qed.
Lemma D_18b5c : decode_any W_18b5c = Some (Load SZ4 true 20 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b60 : bv 32 := 0x0e0a0c63.
Lemma F_18b60 : fetch_word Ubsan.M.loaded_segments (0x18b60 : word) = Some W_18b60.
Proof. vm_refl. Qed.
Lemma D_18b60 : decode_any W_18b60 = Some (Branch BC_EQ 20 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b64 : bv 32 := 0x00058993.
Lemma F_18b64 : fetch_word Ubsan.M.loaded_segments (0x18b64 : word) = Some W_18b64.
Proof. vm_refl. Qed.
Lemma D_18b64 : decode_any W_18b64 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b68 : bv 32 := 0x00060913.
Lemma F_18b68 : fetch_word Ubsan.M.loaded_segments (0x18b68 : word) = Some W_18b68.
Proof. vm_refl. Qed.
Lemma D_18b68 : decode_any W_18b68 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b6c : bv 32 := 0x00010713.
Lemma F_18b6c : fetch_word Ubsan.M.loaded_segments (0x18b6c : word) = Some W_18b6c.
Proof. vm_refl. Qed.
Lemma D_18b6c : decode_any W_18b6c = Some (OpImm ALU_ADD 14 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b70 : bv 32 := 0x00040513.
Lemma F_18b70 : fetch_word Ubsan.M.loaded_segments (0x18b70 : word) = Some W_18b70.
Proof. vm_refl. Qed.
Lemma D_18b70 : decode_any W_18b70 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b74 : bv 32 := 0x00000593.
Lemma F_18b74 : fetch_word Ubsan.M.loaded_segments (0x18b74 : word) = Some W_18b74.
Proof. vm_refl. Qed.
Lemma D_18b74 : decode_any W_18b74 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b78 : bv 32 := 0x00000613.
Lemma F_18b78 : fetch_word Ubsan.M.loaded_segments (0x18b78 : word) = Some W_18b78.
Proof. vm_refl. Qed.
Lemma D_18b78 : decode_any W_18b78 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b7c : bv 32 := 0x00000693.
Lemma F_18b7c : fetch_word Ubsan.M.loaded_segments (0x18b7c : word) = Some W_18b7c.
Proof. vm_refl. Qed.
Lemma D_18b7c : decode_any W_18b7c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b80 : bv 32 := 0xe51ff0ef.
Lemma F_18b80 : fetch_word Ubsan.M.loaded_segments (0x18b80 : word) = Some W_18b80.
Proof. vm_refl. Qed.
Lemma D_18b80 : decode_any W_18b80 = Some (Jal 1 2096720, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b84 : bv 32 := 0x00100a93.
Lemma F_18b84 : fetch_word Ubsan.M.loaded_segments (0x18b84 : word) = Some W_18b84.
Proof. vm_refl. Qed.
Lemma D_18b84 : decode_any W_18b84 = Some (OpImm ALU_ADD 21 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b88 : bv 32 := 0x00200513.
Lemma F_18b88 : fetch_word Ubsan.M.loaded_segments (0x18b88 : word) = Some W_18b88.
Proof. vm_refl. Qed.
Lemma D_18b88 : decode_any W_18b88 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b8c : bv 32 := 0x0aaa4463.
Lemma F_18b8c : fetch_word Ubsan.M.loaded_segments (0x18b8c : word) = Some W_18b8c.
Proof. vm_refl. Qed.
Lemma D_18b8c : decode_any W_18b8c = Some (Branch BC_LT 20 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b90 : bv 32 := 0x00100493.
Lemma F_18b90 : fetch_word Ubsan.M.loaded_segments (0x18b90 : word) = Some W_18b90.
Proof. vm_refl. Qed.
Lemma D_18b90 : decode_any W_18b90 = Some (OpImm ALU_ADD 9 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b94 : bv 32 := 0x01c0006f.
Lemma F_18b94 : fetch_word Ubsan.M.loaded_segments (0x18b94 : word) = Some W_18b94.
Proof. vm_refl. Qed.
Lemma D_18b94 : decode_any W_18b94 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b98 : bv 32 := 0x00c12023.
Lemma F_18b98 : fetch_word Ubsan.M.loaded_segments (0x18b98 : word) = Some W_18b98.
Proof. vm_refl. Qed.
Lemma D_18b98 : decode_any W_18b98 = Some (Store SZ4 2 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18b9c : bv 32 := 0x00a5a533.
Lemma F_18b9c : fetch_word Ubsan.M.loaded_segments (0x18b9c : word) = Some W_18b9c.
Proof. vm_refl. Qed.
Lemma D_18b9c : decode_any W_18b9c = Some (Op ALU_SLT 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ba0 : bv 32 := 0xfff50513.
Lemma F_18ba0 : fetch_word Ubsan.M.loaded_segments (0x18ba0 : word) = Some W_18ba0.
Proof. vm_refl. Qed.
Lemma D_18ba0 : decode_any W_18ba0 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ba4 : bv 32 := 0x0014849b.
Lemma F_18ba4 : fetch_word Ubsan.M.loaded_segments (0x18ba4 : word) = Some W_18ba4.
Proof. vm_refl. Qed.
Lemma D_18ba4 : decode_any W_18ba4 = Some (OpImm32 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ba8 : bv 32 := 0x01557ab3.
Lemma F_18ba8 : fetch_word Ubsan.M.loaded_segments (0x18ba8 : word) = Some W_18ba8.
Proof. vm_refl. Qed.
Lemma D_18ba8 : decode_any W_18ba8 = Some (Op ALU_AND 21 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bac : bv 32 := 0x089a0463.
Lemma F_18bac : fetch_word Ubsan.M.loaded_segments (0x18bac : word) = Some W_18bac.
Proof. vm_refl. Qed.
Lemma D_18bac : decode_any W_18bac = Some (Branch BC_EQ 20 9 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bb0 : bv 32 := 0x00410713.
Lemma F_18bb0 : fetch_word Ubsan.M.loaded_segments (0x18bb0 : word) = Some W_18bb0.
Proof. vm_refl. Qed.
Lemma D_18bb0 : decode_any W_18bb0 = Some (OpImm ALU_ADD 14 2 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bb4 : bv 32 := 0x00040513.
Lemma F_18bb4 : fetch_word Ubsan.M.loaded_segments (0x18bb4 : word) = Some W_18bb4.
Proof. vm_refl. Qed.
Lemma D_18bb4 : decode_any W_18bb4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bb8 : bv 32 := 0x00048593.
Lemma F_18bb8 : fetch_word Ubsan.M.loaded_segments (0x18bb8 : word) = Some W_18bb8.
Proof. vm_refl. Qed.
Lemma D_18bb8 : decode_any W_18bb8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bbc : bv 32 := 0x00000613.
Lemma F_18bbc : fetch_word Ubsan.M.loaded_segments (0x18bbc : word) = Some W_18bbc.
Proof. vm_refl. Qed.
Lemma D_18bbc : decode_any W_18bbc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bc0 : bv 32 := 0x00000693.
Lemma F_18bc0 : fetch_word Ubsan.M.loaded_segments (0x18bc0 : word) = Some W_18bc0.
Proof. vm_refl. Qed.
Lemma D_18bc0 : decode_any W_18bc0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bc4 : bv 32 := 0xe0dff0ef.
Lemma F_18bc4 : fetch_word Ubsan.M.loaded_segments (0x18bc4 : word) = Some W_18bc4.
Proof. vm_refl. Qed.
Lemma D_18bc4 : decode_any W_18bc4 = Some (Jal 1 2096652, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bc8 : bv 32 := 0x0e051263.
Lemma F_18bc8 : fetch_word Ubsan.M.loaded_segments (0x18bc8 : word) = Some W_18bc8.
Proof. vm_refl. Qed.
Lemma D_18bc8 : decode_any W_18bc8 = Some (Branch BC_NE 10 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bcc : bv 32 := 0x00012503.
Lemma F_18bcc : fetch_word Ubsan.M.loaded_segments (0x18bcc : word) = Some W_18bcc.
Proof. vm_refl. Qed.
Lemma D_18bcc : decode_any W_18bcc = Some (Load SZ4 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bd0 : bv 32 := 0x00412583.
Lemma F_18bd0 : fetch_word Ubsan.M.loaded_segments (0x18bd0 : word) = Some W_18bd0.
Proof. vm_refl. Qed.
Lemma D_18bd0 : decode_any W_18bd0 = Some (Load SZ4 true 11 2 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bd4 : bv 32 := 0x00050613.
Lemma F_18bd4 : fetch_word Ubsan.M.loaded_segments (0x18bd4 : word) = Some W_18bd4.
Proof. vm_refl. Qed.
Lemma D_18bd4 : decode_any W_18bd4 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bd8 : bv 32 := 0xfca5c0e3.
Lemma F_18bd8 : fetch_word Ubsan.M.loaded_segments (0x18bd8 : word) = Some W_18bd8.
Proof. vm_refl. Qed.
Lemma D_18bd8 : decode_any W_18bd8 = Some (Branch BC_LT 11 10 8128, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bdc : bv 32 := 0x00058613.
Lemma F_18bdc : fetch_word Ubsan.M.loaded_segments (0x18bdc : word) = Some W_18bdc.
Proof. vm_refl. Qed.
Lemma D_18bdc : decode_any W_18bdc = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18be0 : bv 32 := 0xfb9ff06f.
Lemma F_18be0 : fetch_word Ubsan.M.loaded_segments (0x18be0 : word) = Some W_18be0.
Proof. vm_refl. Qed.
Lemma D_18be0 : decode_any W_18be0 = Some (Jal 0 2097080, 4%Z).
Proof. vm_refl. Qed.

Definition W_18be4 : bv 32 := 0x0002c517.
Lemma F_18be4 : fetch_word Ubsan.M.loaded_segments (0x18be4 : word) = Some W_18be4.
Proof. vm_refl. Qed.
Lemma D_18be4 : decode_any W_18be4 = Some (Auipc 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_18be8 : bv 32 := 0x2b453503.
Lemma F_18be8 : fetch_word Ubsan.M.loaded_segments (0x18be8 : word) = Some W_18be8.
Proof. vm_refl. Qed.
Lemma D_18be8 : decode_any W_18be8 = Some (Load SZ8 true 10 10 692, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bec : bv 32 := 0x00052503.
Lemma F_18bec : fetch_word Ubsan.M.loaded_segments (0x18bec : word) = Some W_18bec.
Proof. vm_refl. Qed.
Lemma D_18bec : decode_any W_18bec = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bf0 : bv 32 := 0x00500593.
Lemma F_18bf0 : fetch_word Ubsan.M.loaded_segments (0x18bf0 : word) = Some W_18bf0.
Proof. vm_refl. Qed.
Lemma D_18bf0 : decode_any W_18bf0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bf4 : bv 32 := 0x0ea5c463.
Lemma F_18bf4 : fetch_word Ubsan.M.loaded_segments (0x18bf4 : word) = Some W_18bf4.
Proof. vm_refl. Qed.
Lemma D_18bf4 : decode_any W_18bf4 = Some (Branch BC_LT 11 10 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bf8 : bv 32 := 0xffff9517.
Lemma F_18bf8 : fetch_word Ubsan.M.loaded_segments (0x18bf8 : word) = Some W_18bf8.
Proof. vm_refl. Qed.
Lemma D_18bf8 : decode_any W_18bf8 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_18bfc : bv 32 := 0xffff9597.
Lemma F_18bfc : fetch_word Ubsan.M.loaded_segments (0x18bfc : word) = Some W_18bfc.
Proof. vm_refl. Qed.
Lemma D_18bfc : decode_any W_18bfc = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c00 : bv 32 := 0x02d50513.
Lemma F_18c00 : fetch_word Ubsan.M.loaded_segments (0x18c00 : word) = Some W_18c00.
Proof. vm_refl. Qed.
Lemma D_18c00 : decode_any W_18c00 = Some (OpImm ALU_ADD 10 10 45, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c04 : bv 32 := 0x63c58593.
Lemma F_18c04 : fetch_word Ubsan.M.loaded_segments (0x18c04 : word) = Some W_18c04.
Proof. vm_refl. Qed.
Lemma D_18c04 : decode_any W_18c04 = Some (OpImm ALU_ADD 11 11 1596, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c08 : bv 32 := 0x0740006f.
Lemma F_18c08 : fetch_word Ubsan.M.loaded_segments (0x18c08 : word) = Some W_18c08.
Proof. vm_refl. Qed.
Lemma D_18c08 : decode_any W_18c08 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c0c : bv 32 := 0x0002c517.
Lemma F_18c0c : fetch_word Ubsan.M.loaded_segments (0x18c0c : word) = Some W_18c0c.
Proof. vm_refl. Qed.
Lemma D_18c0c : decode_any W_18c0c = Some (Auipc 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c10 : bv 32 := 0x28c53503.
Lemma F_18c10 : fetch_word Ubsan.M.loaded_segments (0x18c10 : word) = Some W_18c10.
Proof. vm_refl. Qed.
Lemma D_18c10 : decode_any W_18c10 = Some (Load SZ8 true 10 10 652, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c14 : bv 32 := 0x00052503.
Lemma F_18c14 : fetch_word Ubsan.M.loaded_segments (0x18c14 : word) = Some W_18c14.
Proof. vm_refl. Qed.
Lemma D_18c14 : decode_any W_18c14 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c18 : bv 32 := 0x00500593.
Lemma F_18c18 : fetch_word Ubsan.M.loaded_segments (0x18c18 : word) = Some W_18c18.
Proof. vm_refl. Qed.
Lemma D_18c18 : decode_any W_18c18 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c1c : bv 32 := 0x0ca5c063.
Lemma F_18c1c : fetch_word Ubsan.M.loaded_segments (0x18c1c : word) = Some W_18c1c.
Proof. vm_refl. Qed.
Lemma D_18c1c : decode_any W_18c1c = Some (Branch BC_LT 11 10 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c20 : bv 32 := 0xffff9517.
Lemma F_18c20 : fetch_word Ubsan.M.loaded_segments (0x18c20 : word) = Some W_18c20.
Proof. vm_refl. Qed.
Lemma D_18c20 : decode_any W_18c20 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c24 : bv 32 := 0xffff9597.
Lemma F_18c24 : fetch_word Ubsan.M.loaded_segments (0x18c24 : word) = Some W_18c24.
Proof. vm_refl. Qed.
Lemma D_18c24 : decode_any W_18c24 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c28 : bv 32 := 0x60750513.
Lemma F_18c28 : fetch_word Ubsan.M.loaded_segments (0x18c28 : word) = Some W_18c28.
Proof. vm_refl. Qed.
Lemma D_18c28 : decode_any W_18c28 = Some (OpImm ALU_ADD 10 10 1543, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c2c : bv 32 := 0x61458593.
Lemma F_18c2c : fetch_word Ubsan.M.loaded_segments (0x18c2c : word) = Some W_18c2c.
Proof. vm_refl. Qed.
Lemma D_18c2c : decode_any W_18c2c = Some (OpImm ALU_ADD 11 11 1556, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c30 : bv 32 := 0x04c0006f.
Lemma F_18c30 : fetch_word Ubsan.M.loaded_segments (0x18c30 : word) = Some W_18c30.
Proof. vm_refl. Qed.
Lemma D_18c30 : decode_any W_18c30 = Some (Jal 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c34 : bv 32 := 0x0039f513.
Lemma F_18c34 : fetch_word Ubsan.M.loaded_segments (0x18c34 : word) = Some W_18c34.
Proof. vm_refl. Qed.
Lemma D_18c34 : decode_any W_18c34 = Some (OpImm ALU_AND 10 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c38 : bv 32 := 0x0c051663.
Lemma F_18c38 : fetch_word Ubsan.M.loaded_segments (0x18c38 : word) = Some W_18c38.
Proof. vm_refl. Qed.
Lemma D_18c38 : decode_any W_18c38 = Some (Branch BC_NE 10 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c3c : bv 32 := 0x0159a023.
Lemma F_18c3c : fetch_word Ubsan.M.loaded_segments (0x18c3c : word) = Some W_18c3c.
Proof. vm_refl. Qed.
Lemma D_18c3c : decode_any W_18c3c = Some (Store SZ4 19 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c40 : bv 32 := 0x06090263.
Lemma F_18c40 : fetch_word Ubsan.M.loaded_segments (0x18c40 : word) = Some W_18c40.
Proof. vm_refl. Qed.
Lemma D_18c40 : decode_any W_18c40 = Some (Branch BC_EQ 18 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c44 : bv 32 := 0x00397513.
Lemma F_18c44 : fetch_word Ubsan.M.loaded_segments (0x18c44 : word) = Some W_18c44.
Proof. vm_refl. Qed.
Lemma D_18c44 : decode_any W_18c44 = Some (OpImm ALU_AND 10 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c48 : bv 32 := 0x0a051e63.
Lemma F_18c48 : fetch_word Ubsan.M.loaded_segments (0x18c48 : word) = Some W_18c48.
Proof. vm_refl. Qed.
Lemma D_18c48 : decode_any W_18c48 = Some (Branch BC_NE 10 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c4c : bv 32 := 0x00012583.
Lemma F_18c4c : fetch_word Ubsan.M.loaded_segments (0x18c4c : word) = Some W_18c4c.
Proof. vm_refl. Qed.
Lemma D_18c4c : decode_any W_18c4c = Some (Load SZ4 true 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c50 : bv 32 := 0x00b92023.
Lemma F_18c50 : fetch_word Ubsan.M.loaded_segments (0x18c50 : word) = Some W_18c50.
Proof. vm_refl. Qed.
Lemma D_18c50 : decode_any W_18c50 = Some (Store SZ4 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c54 : bv 32 := 0x08c0006f.
Lemma F_18c54 : fetch_word Ubsan.M.loaded_segments (0x18c54 : word) = Some W_18c54.
Proof. vm_refl. Qed.
Lemma D_18c54 : decode_any W_18c54 = Some (Jal 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c58 : bv 32 := 0x0002c517.
Lemma F_18c58 : fetch_word Ubsan.M.loaded_segments (0x18c58 : word) = Some W_18c58.
Proof. vm_refl. Qed.
Lemma D_18c58 : decode_any W_18c58 = Some (Auipc 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c5c : bv 32 := 0x24053503.
Lemma F_18c5c : fetch_word Ubsan.M.loaded_segments (0x18c5c : word) = Some W_18c5c.
Proof. vm_refl. Qed.
Lemma D_18c5c : decode_any W_18c5c = Some (Load SZ8 true 10 10 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c60 : bv 32 := 0x00052503.
Lemma F_18c60 : fetch_word Ubsan.M.loaded_segments (0x18c60 : word) = Some W_18c60.
Proof. vm_refl. Qed.
Lemma D_18c60 : decode_any W_18c60 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c64 : bv 32 := 0x00500593.
Lemma F_18c64 : fetch_word Ubsan.M.loaded_segments (0x18c64 : word) = Some W_18c64.
Proof. vm_refl. Qed.
Lemma D_18c64 : decode_any W_18c64 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c68 : bv 32 := 0x06a5ca63.
Lemma F_18c68 : fetch_word Ubsan.M.loaded_segments (0x18c68 : word) = Some W_18c68.
Proof. vm_refl. Qed.
Lemma D_18c68 : decode_any W_18c68 = Some (Branch BC_LT 11 10 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c6c : bv 32 := 0xffff7517.
Lemma F_18c6c : fetch_word Ubsan.M.loaded_segments (0x18c6c : word) = Some W_18c6c.
Proof. vm_refl. Qed.
Lemma D_18c6c : decode_any W_18c6c = Some (Auipc 10 1048567, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c70 : bv 32 := 0xffff9597.
Lemma F_18c70 : fetch_word Ubsan.M.loaded_segments (0x18c70 : word) = Some W_18c70.
Proof. vm_refl. Qed.
Lemma D_18c70 : decode_any W_18c70 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c74 : bv 32 := 0x72350513.
Lemma F_18c74 : fetch_word Ubsan.M.loaded_segments (0x18c74 : word) = Some W_18c74.
Proof. vm_refl. Qed.
Lemma D_18c74 : decode_any W_18c74 = Some (OpImm ALU_ADD 10 10 1827, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c78 : bv 32 := 0x5c858593.
Lemma F_18c78 : fetch_word Ubsan.M.loaded_segments (0x18c78 : word) = Some W_18c78.
Proof. vm_refl. Qed.
Lemma D_18c78 : decode_any W_18c78 = Some (OpImm ALU_ADD 11 11 1480, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c7c : bv 32 := 0x00100613.
Lemma F_18c7c : fetch_word Ubsan.M.loaded_segments (0x18c7c : word) = Some W_18c7c.
Proof. vm_refl. Qed.
Lemma D_18c7c : decode_any W_18c7c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c80 : bv 32 := 0x03813083.
Lemma F_18c80 : fetch_word Ubsan.M.loaded_segments (0x18c80 : word) = Some W_18c80.
Proof. vm_refl. Qed.
Lemma D_18c80 : decode_any W_18c80 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c84 : bv 32 := 0x03013403.
Lemma F_18c84 : fetch_word Ubsan.M.loaded_segments (0x18c84 : word) = Some W_18c84.
Proof. vm_refl. Qed.
Lemma D_18c84 : decode_any W_18c84 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c88 : bv 32 := 0x02813483.
Lemma F_18c88 : fetch_word Ubsan.M.loaded_segments (0x18c88 : word) = Some W_18c88.
Proof. vm_refl. Qed.
Lemma D_18c88 : decode_any W_18c88 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c8c : bv 32 := 0x02013903.
Lemma F_18c8c : fetch_word Ubsan.M.loaded_segments (0x18c8c : word) = Some W_18c8c.
Proof. vm_refl. Qed.
Lemma D_18c8c : decode_any W_18c8c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c90 : bv 32 := 0x01813983.
Lemma F_18c90 : fetch_word Ubsan.M.loaded_segments (0x18c90 : word) = Some W_18c90.
Proof. vm_refl. Qed.
Lemma D_18c90 : decode_any W_18c90 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c94 : bv 32 := 0x01013a03.
Lemma F_18c94 : fetch_word Ubsan.M.loaded_segments (0x18c94 : word) = Some W_18c94.
Proof. vm_refl. Qed.
Lemma D_18c94 : decode_any W_18c94 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c98 : bv 32 := 0x00813a83.
Lemma F_18c98 : fetch_word Ubsan.M.loaded_segments (0x18c98 : word) = Some W_18c98.
Proof. vm_refl. Qed.
Lemma D_18c98 : decode_any W_18c98 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18c9c : bv 32 := 0x04010113.
Lemma F_18c9c : fetch_word Ubsan.M.loaded_segments (0x18c9c : word) = Some W_18c9c.
Proof. vm_refl. Qed.
Lemma D_18c9c : decode_any W_18c9c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ca0 : bv 32 := 0x954ff06f.
Lemma F_18ca0 : fetch_word Ubsan.M.loaded_segments (0x18ca0 : word) = Some W_18ca0.
Proof. vm_refl. Qed.
Lemma D_18ca0 : decode_any W_18ca0 = Some (Jal 0 2093396, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ca4 : bv 32 := 0x00000513.
Lemma F_18ca4 : fetch_word Ubsan.M.loaded_segments (0x18ca4 : word) = Some W_18ca4.
Proof. vm_refl. Qed.
Lemma D_18ca4 : decode_any W_18ca4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ca8 : bv 32 := 0x0380006f.
Lemma F_18ca8 : fetch_word Ubsan.M.loaded_segments (0x18ca8 : word) = Some W_18ca8.
Proof. vm_refl. Qed.
Lemma D_18ca8 : decode_any W_18ca8 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cac : bv 32 := 0x0002c517.
Lemma F_18cac : fetch_word Ubsan.M.loaded_segments (0x18cac : word) = Some W_18cac.
Proof. vm_refl. Qed.
Lemma D_18cac : decode_any W_18cac = Some (Auipc 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cb0 : bv 32 := 0x1ec53503.
Lemma F_18cb0 : fetch_word Ubsan.M.loaded_segments (0x18cb0 : word) = Some W_18cb0.
Proof. vm_refl. Qed.
Lemma D_18cb0 : decode_any W_18cb0 = Some (Load SZ8 true 10 10 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cb4 : bv 32 := 0x00052503.
Lemma F_18cb4 : fetch_word Ubsan.M.loaded_segments (0x18cb4 : word) = Some W_18cb4.
Proof. vm_refl. Qed.
Lemma D_18cb4 : decode_any W_18cb4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cb8 : bv 32 := 0x00500593.
Lemma F_18cb8 : fetch_word Ubsan.M.loaded_segments (0x18cb8 : word) = Some W_18cb8.
Proof. vm_refl. Qed.
Lemma D_18cb8 : decode_any W_18cb8 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cbc : bv 32 := 0x02a5c063.
Lemma F_18cbc : fetch_word Ubsan.M.loaded_segments (0x18cbc : word) = Some W_18cbc.
Proof. vm_refl. Qed.
Lemma D_18cbc : decode_any W_18cbc = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cc0 : bv 32 := 0xffff9517.
Lemma F_18cc0 : fetch_word Ubsan.M.loaded_segments (0x18cc0 : word) = Some W_18cc0.
Proof. vm_refl. Qed.
Lemma D_18cc0 : decode_any W_18cc0 = Some (Auipc 10 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cc4 : bv 32 := 0xffff9597.
Lemma F_18cc4 : fetch_word Ubsan.M.loaded_segments (0x18cc4 : word) = Some W_18cc4.
Proof. vm_refl. Qed.
Lemma D_18cc4 : decode_any W_18cc4 = Some (Auipc 11 1048569, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cc8 : bv 32 := 0x33350513.
Lemma F_18cc8 : fetch_word Ubsan.M.loaded_segments (0x18cc8 : word) = Some W_18cc8.
Proof. vm_refl. Qed.
Lemma D_18cc8 : decode_any W_18cc8 = Some (OpImm ALU_ADD 10 10 819, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ccc : bv 32 := 0x57458593.
Lemma F_18ccc : fetch_word Ubsan.M.loaded_segments (0x18ccc : word) = Some W_18ccc.
Proof. vm_refl. Qed.
Lemma D_18ccc : decode_any W_18ccc = Some (OpImm ALU_ADD 11 11 1396, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cd0 : bv 32 := 0x00100613.
Lemma F_18cd0 : fetch_word Ubsan.M.loaded_segments (0x18cd0 : word) = Some W_18cd0.
Proof. vm_refl. Qed.
Lemma D_18cd0 : decode_any W_18cd0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cd4 : bv 32 := 0x920ff0ef.
Lemma F_18cd4 : fetch_word Ubsan.M.loaded_segments (0x18cd4 : word) = Some W_18cd4.
Proof. vm_refl. Qed.
Lemma D_18cd4 : decode_any W_18cd4 = Some (Jal 1 2093344, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cd8 : bv 32 := 0x0080006f.
Lemma F_18cd8 : fetch_word Ubsan.M.loaded_segments (0x18cd8 : word) = Some W_18cd8.
Proof. vm_refl. Qed.
Lemma D_18cd8 : decode_any W_18cd8 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cdc : bv 32 := 0x00100513.
Lemma F_18cdc : fetch_word Ubsan.M.loaded_segments (0x18cdc : word) = Some W_18cdc.
Proof. vm_refl. Qed.
Lemma D_18cdc : decode_any W_18cdc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ce0 : bv 32 := 0x03813083.
Lemma F_18ce0 : fetch_word Ubsan.M.loaded_segments (0x18ce0 : word) = Some W_18ce0.
Proof. vm_refl. Qed.
Lemma D_18ce0 : decode_any W_18ce0 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ce4 : bv 32 := 0x03013403.
Lemma F_18ce4 : fetch_word Ubsan.M.loaded_segments (0x18ce4 : word) = Some W_18ce4.
Proof. vm_refl. Qed.
Lemma D_18ce4 : decode_any W_18ce4 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_18ce8 : bv 32 := 0x02813483.
Lemma F_18ce8 : fetch_word Ubsan.M.loaded_segments (0x18ce8 : word) = Some W_18ce8.
Proof. vm_refl. Qed.
Lemma D_18ce8 : decode_any W_18ce8 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cec : bv 32 := 0x02013903.
Lemma F_18cec : fetch_word Ubsan.M.loaded_segments (0x18cec : word) = Some W_18cec.
Proof. vm_refl. Qed.
Lemma D_18cec : decode_any W_18cec = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cf0 : bv 32 := 0x01813983.
Lemma F_18cf0 : fetch_word Ubsan.M.loaded_segments (0x18cf0 : word) = Some W_18cf0.
Proof. vm_refl. Qed.
Lemma D_18cf0 : decode_any W_18cf0 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cf4 : bv 32 := 0x01013a03.
Lemma F_18cf4 : fetch_word Ubsan.M.loaded_segments (0x18cf4 : word) = Some W_18cf4.
Proof. vm_refl. Qed.
Lemma D_18cf4 : decode_any W_18cf4 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cf8 : bv 32 := 0x00813a83.
Lemma F_18cf8 : fetch_word Ubsan.M.loaded_segments (0x18cf8 : word) = Some W_18cf8.
Proof. vm_refl. Qed.
Lemma D_18cf8 : decode_any W_18cf8 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_18cfc : bv 32 := 0x04010113.
Lemma F_18cfc : fetch_word Ubsan.M.loaded_segments (0x18cfc : word) = Some W_18cfc.
Proof. vm_refl. Qed.
Lemma D_18cfc : decode_any W_18cfc = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d00 : bv 32 := 0x00008067.
Lemma F_18d00 : fetch_word Ubsan.M.loaded_segments (0x18d00 : word) = Some W_18d00.
Proof. vm_refl. Qed.
Lemma D_18d00 : decode_any W_18d00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_18d04 : bv 32 := 0xc0001073.
Lemma F_18d04 : fetch_word Ubsan.M.loaded_segments (0x18d04 : word) = Some W_18d04.
Proof. vm_refl. Qed.
Lemma D_18d04 : decode_any W_18d04 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
