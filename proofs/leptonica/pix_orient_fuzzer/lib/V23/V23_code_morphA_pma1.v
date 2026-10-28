(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6f114 : bv 32 := 0x00050a63.
Lemma F_6f114 : fetch_word Ubsan.M.loaded_segments (0x6f114 : word) = Some W_6f114.
Proof. vm_refl. Qed.
Lemma D_6f114 : decode_any W_6f114 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f118 : bv 32 := 0x00757593.
Lemma F_6f118 : fetch_word Ubsan.M.loaded_segments (0x6f118 : word) = Some W_6f118.
Proof. vm_refl. Qed.
Lemma D_6f118 : decode_any W_6f118 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f11c : bv 32 := 0x04059063.
Lemma F_6f11c : fetch_word Ubsan.M.loaded_segments (0x6f11c : word) = Some W_6f11c.
Proof. vm_refl. Qed.
Lemma D_6f11c : decode_any W_6f11c = Some (Branch BC_NE 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f120 : bv 32 := 0x00852503.
Lemma F_6f120 : fetch_word Ubsan.M.loaded_segments (0x6f120 : word) = Some W_6f120.
Proof. vm_refl. Qed.
Lemma D_6f120 : decode_any W_6f120 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f124 : bv 32 := 0x00008067.
Lemma F_6f124 : fetch_word Ubsan.M.loaded_segments (0x6f124 : word) = Some W_6f124.
Proof. vm_refl. Qed.
Lemma D_6f124 : decode_any W_6f124 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f128 : bv 32 := 0x000b8517.
Lemma F_6f128 : fetch_word Ubsan.M.loaded_segments (0x6f128 : word) = Some W_6f128.
Proof. vm_refl. Qed.
Lemma D_6f128 : decode_any W_6f128 = Some (Auipc 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f12c : bv 32 := 0x94853503.
Lemma F_6f12c : fetch_word Ubsan.M.loaded_segments (0x6f12c : word) = Some W_6f12c.
Proof. vm_refl. Qed.
Lemma D_6f12c : decode_any W_6f12c = Some (Load SZ8 true 10 10 2376, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f130 : bv 32 := 0x00052503.
Lemma F_6f130 : fetch_word Ubsan.M.loaded_segments (0x6f130 : word) = Some W_6f130.
Proof. vm_refl. Qed.
Lemma D_6f130 : decode_any W_6f130 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f134 : bv 32 := 0x00500593.
Lemma F_6f134 : fetch_word Ubsan.M.loaded_segments (0x6f134 : word) = Some W_6f134.
Proof. vm_refl. Qed.
Lemma D_6f134 : decode_any W_6f134 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f138 : bv 32 := 0x00a5ce63.
Lemma F_6f138 : fetch_word Ubsan.M.loaded_segments (0x6f138 : word) = Some W_6f138.
Proof. vm_refl. Qed.
Lemma D_6f138 : decode_any W_6f138 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f13c : bv 32 := 0xfffa2517.
Lemma F_6f13c : fetch_word Ubsan.M.loaded_segments (0x6f13c : word) = Some W_6f13c.
Proof. vm_refl. Qed.
Lemma D_6f13c : decode_any W_6f13c = Some (Auipc 10 1048482, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f140 : bv 32 := 0xfffa1597.
Lemma F_6f140 : fetch_word Ubsan.M.loaded_segments (0x6f140 : word) = Some W_6f140.
Proof. vm_refl. Qed.
Lemma D_6f140 : decode_any W_6f140 = Some (Auipc 11 1048481, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f144 : bv 32 := 0xf0f50513.
Lemma F_6f144 : fetch_word Ubsan.M.loaded_segments (0x6f144 : word) = Some W_6f144.
Proof. vm_refl. Qed.
Lemma D_6f144 : decode_any W_6f144 = Some (OpImm ALU_ADD 10 10 3855, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f148 : bv 32 := 0x29158593.
Lemma F_6f148 : fetch_word Ubsan.M.loaded_segments (0x6f148 : word) = Some W_6f148.
Proof. vm_refl. Qed.
Lemma D_6f148 : decode_any W_6f148 = Some (OpImm ALU_ADD 11 11 657, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f14c : bv 32 := 0x00000613.
Lemma F_6f14c : fetch_word Ubsan.M.loaded_segments (0x6f14c : word) = Some W_6f14c.
Proof. vm_refl. Qed.
Lemma D_6f14c : decode_any W_6f14c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f150 : bv 32 := 0xd20f406f.
Lemma F_6f150 : fetch_word Ubsan.M.loaded_segments (0x6f150 : word) = Some W_6f150.
Proof. vm_refl. Qed.
Lemma D_6f150 : decode_any W_6f150 = Some (Jal 0 2049312, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f154 : bv 32 := 0x00000513.
Lemma F_6f154 : fetch_word Ubsan.M.loaded_segments (0x6f154 : word) = Some W_6f154.
Proof. vm_refl. Qed.
Lemma D_6f154 : decode_any W_6f154 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6f158 : bv 32 := 0x00008067.
Lemma F_6f158 : fetch_word Ubsan.M.loaded_segments (0x6f158 : word) = Some W_6f158.
Proof. vm_refl. Qed.
Lemma D_6f158 : decode_any W_6f158 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b7c : bv 32 := 0xfd010113.
Lemma F_a1b7c : fetch_word Ubsan.M.loaded_segments (0xa1b7c : word) = Some W_a1b7c.
Proof. vm_refl. Qed.
Lemma D_a1b7c : decode_any W_a1b7c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b80 : bv 32 := 0x02113423.
Lemma F_a1b80 : fetch_word Ubsan.M.loaded_segments (0xa1b80 : word) = Some W_a1b80.
Proof. vm_refl. Qed.
Lemma D_a1b80 : decode_any W_a1b80 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b84 : bv 32 := 0x02813023.
Lemma F_a1b84 : fetch_word Ubsan.M.loaded_segments (0xa1b84 : word) = Some W_a1b84.
Proof. vm_refl. Qed.
Lemma D_a1b84 : decode_any W_a1b84 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b88 : bv 32 := 0x00913c23.
Lemma F_a1b88 : fetch_word Ubsan.M.loaded_segments (0xa1b88 : word) = Some W_a1b88.
Proof. vm_refl. Qed.
Lemma D_a1b88 : decode_any W_a1b88 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b8c : bv 32 := 0x01213823.
Lemma F_a1b8c : fetch_word Ubsan.M.loaded_segments (0xa1b8c : word) = Some W_a1b8c.
Proof. vm_refl. Qed.
Lemma D_a1b8c : decode_any W_a1b8c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b90 : bv 32 := 0x01313423.
Lemma F_a1b90 : fetch_word Ubsan.M.loaded_segments (0xa1b90 : word) = Some W_a1b90.
Proof. vm_refl. Qed.
Lemma D_a1b90 : decode_any W_a1b90 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b94 : bv 32 := 0x0076f713.
Lemma F_a1b94 : fetch_word Ubsan.M.loaded_segments (0xa1b94 : word) = Some W_a1b94.
Proof. vm_refl. Qed.
Lemma D_a1b94 : decode_any W_a1b94 = Some (OpImm ALU_AND 14 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b98 : bv 32 := 0x1e071063.
Lemma F_a1b98 : fetch_word Ubsan.M.loaded_segments (0xa1b98 : word) = Some W_a1b98.
Proof. vm_refl. Qed.
Lemma D_a1b98 : decode_any W_a1b98 = Some (Branch BC_NE 14 0 480, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1b9c : bv 32 := 0x00050413.
Lemma F_a1b9c : fetch_word Ubsan.M.loaded_segments (0xa1b9c : word) = Some W_a1b9c.
Proof. vm_refl. Qed.
Lemma D_a1b9c : decode_any W_a1b9c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ba0 : bv 32 := 0x0006b023.
Lemma F_a1ba0 : fetch_word Ubsan.M.loaded_segments (0xa1ba0 : word) = Some W_a1ba0.
Proof. vm_refl. Qed.
Lemma D_a1ba0 : decode_any W_a1ba0 = Some (Store SZ8 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ba4 : bv 32 := 0x08058e63.
Lemma F_a1ba4 : fetch_word Ubsan.M.loaded_segments (0xa1ba4 : word) = Some W_a1ba4.
Proof. vm_refl. Qed.
Lemma D_a1ba4 : decode_any W_a1ba4 = Some (Branch BC_EQ 11 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ba8 : bv 32 := 0x0c060063.
Lemma F_a1ba8 : fetch_word Ubsan.M.loaded_segments (0xa1ba8 : word) = Some W_a1ba8.
Proof. vm_refl. Qed.
Lemma D_a1ba8 : decode_any W_a1ba8 = Some (Branch BC_EQ 12 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bac : bv 32 := 0x00060913.
Lemma F_a1bac : fetch_word Ubsan.M.loaded_segments (0xa1bac : word) = Some W_a1bac.
Proof. vm_refl. Qed.
Lemma D_a1bac : decode_any W_a1bac = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bb0 : bv 32 := 0x00068993.
Lemma F_a1bb0 : fetch_word Ubsan.M.loaded_segments (0xa1bb0 : word) = Some W_a1bb0.
Proof. vm_refl. Qed.
Lemma D_a1bb0 : decode_any W_a1bb0 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bb4 : bv 32 := 0x00058493.
Lemma F_a1bb4 : fetch_word Ubsan.M.loaded_segments (0xa1bb4 : word) = Some W_a1bb4.
Proof. vm_refl. Qed.
Lemma D_a1bb4 : decode_any W_a1bb4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bb8 : bv 32 := 0x00058513.
Lemma F_a1bb8 : fetch_word Ubsan.M.loaded_segments (0xa1bb8 : word) = Some W_a1bb8.
Proof. vm_refl. Qed.
Lemma D_a1bb8 : decode_any W_a1bb8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bbc : bv 32 := 0xd58cd0ef.
Lemma F_a1bbc : fetch_word Ubsan.M.loaded_segments (0xa1bbc : word) = Some W_a1bbc.
Proof. vm_refl. Qed.
Lemma D_a1bbc : decode_any W_a1bbc = Some (Jal 1 1889624, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bc0 : bv 32 := 0x00100593.
Lemma F_a1bc0 : fetch_word Ubsan.M.loaded_segments (0xa1bc0 : word) = Some W_a1bc0.
Proof. vm_refl. Qed.
Lemma D_a1bc0 : decode_any W_a1bc0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bc4 : bv 32 := 0x0cb51663.
Lemma F_a1bc4 : fetch_word Ubsan.M.loaded_segments (0xa1bc4 : word) = Some W_a1bc4.
Proof. vm_refl. Qed.
Lemma D_a1bc4 : decode_any W_a1bc4 = Some (Branch BC_NE 10 11 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bc8 : bv 32 := 0x00410593.
Lemma F_a1bc8 : fetch_word Ubsan.M.loaded_segments (0xa1bc8 : word) = Some W_a1bc8.
Proof. vm_refl. Qed.
Lemma D_a1bc8 : decode_any W_a1bc8 = Some (OpImm ALU_ADD 11 2 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bcc : bv 32 := 0x00010613.
Lemma F_a1bcc : fetch_word Ubsan.M.loaded_segments (0xa1bcc : word) = Some W_a1bcc.
Proof. vm_refl. Qed.
Lemma D_a1bcc : decode_any W_a1bcc = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bd0 : bv 32 := 0x00090513.
Lemma F_a1bd0 : fetch_word Ubsan.M.loaded_segments (0xa1bd0 : word) = Some W_a1bd0.
Proof. vm_refl. Qed.
Lemma D_a1bd0 : decode_any W_a1bd0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bd4 : bv 32 := 0x00000693.
Lemma F_a1bd4 : fetch_word Ubsan.M.loaded_segments (0xa1bd4 : word) = Some W_a1bd4.
Proof. vm_refl. Qed.
Lemma D_a1bd4 : decode_any W_a1bd4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bd8 : bv 32 := 0x00000713.
Lemma F_a1bd8 : fetch_word Ubsan.M.loaded_segments (0xa1bd8 : word) = Some W_a1bd8.
Proof. vm_refl. Qed.
Lemma D_a1bd8 : decode_any W_a1bd8 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bdc : bv 32 := 0x3f4030ef.
Lemma F_a1bdc : fetch_word Ubsan.M.loaded_segments (0xa1bdc : word) = Some W_a1bdc.
Proof. vm_refl. Qed.
Lemma D_a1bdc : decode_any W_a1bdc = Some (Jal 1 13300, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1be0 : bv 32 := 0x00412503.
Lemma F_a1be0 : fetch_word Ubsan.M.loaded_segments (0xa1be0 : word) = Some W_a1be0.
Proof. vm_refl. Qed.
Lemma D_a1be0 : decode_any W_a1be0 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1be4 : bv 32 := 0x0e050863.
Lemma F_a1be4 : fetch_word Ubsan.M.loaded_segments (0xa1be4 : word) = Some W_a1be4.
Proof. vm_refl. Qed.
Lemma D_a1be4 : decode_any W_a1be4 = Some (Branch BC_EQ 10 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1be8 : bv 32 := 0x00012503.
Lemma F_a1be8 : fetch_word Ubsan.M.loaded_segments (0xa1be8 : word) = Some W_a1be8.
Proof. vm_refl. Qed.
Lemma D_a1be8 : decode_any W_a1be8 = Some (Load SZ4 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bec : bv 32 := 0x0e050463.
Lemma F_a1bec : fetch_word Ubsan.M.loaded_segments (0xa1bec : word) = Some W_a1bec.
Proof. vm_refl. Qed.
Lemma D_a1bec : decode_any W_a1bec = Some (Branch BC_EQ 10 0 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bf0 : bv 32 := 0x10040c63.
Lemma F_a1bf0 : fetch_word Ubsan.M.loaded_segments (0xa1bf0 : word) = Some W_a1bf0.
Proof. vm_refl. Qed.
Lemma D_a1bf0 : decode_any W_a1bf0 = Some (Branch BC_EQ 8 0 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bf4 : bv 32 := 0x00040513.
Lemma F_a1bf4 : fetch_word Ubsan.M.loaded_segments (0xa1bf4 : word) = Some W_a1bf4.
Proof. vm_refl. Qed.
Lemma D_a1bf4 : decode_any W_a1bf4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bf8 : bv 32 := 0x00048593.
Lemma F_a1bf8 : fetch_word Ubsan.M.loaded_segments (0xa1bf8 : word) = Some W_a1bf8.
Proof. vm_refl. Qed.
Lemma D_a1bf8 : decode_any W_a1bf8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1bfc : bv 32 := 0x9f0cd0ef.
Lemma F_a1bfc : fetch_word Ubsan.M.loaded_segments (0xa1bfc : word) = Some W_a1bfc.
Proof. vm_refl. Qed.
Lemma D_a1bfc : decode_any W_a1bfc = Some (Jal 1 1888752, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c00 : bv 32 := 0x10941c63.
Lemma F_a1c00 : fetch_word Ubsan.M.loaded_segments (0xa1c00 : word) = Some W_a1c00.
Proof. vm_refl. Qed.
Lemma D_a1c00 : decode_any W_a1c00 = Some (Branch BC_NE 8 9 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c04 : bv 32 := 0x00000513.
Lemma F_a1c04 : fetch_word Ubsan.M.loaded_segments (0xa1c04 : word) = Some W_a1c04.
Proof. vm_refl. Qed.
Lemma D_a1c04 : decode_any W_a1c04 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c08 : bv 32 := 0x00048593.
Lemma F_a1c08 : fetch_word Ubsan.M.loaded_segments (0xa1c08 : word) = Some W_a1c08.
Proof. vm_refl. Qed.
Lemma D_a1c08 : decode_any W_a1c08 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c0c : bv 32 := 0xf51cc0ef.
Lemma F_a1c0c : fetch_word Ubsan.M.loaded_segments (0xa1c0c : word) = Some W_a1c0c.
Proof. vm_refl. Qed.
Lemma D_a1c0c : decode_any W_a1c0c = Some (Jal 1 1888080, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c10 : bv 32 := 0x00a9b023.
Lemma F_a1c10 : fetch_word Ubsan.M.loaded_segments (0xa1c10 : word) = Some W_a1c10.
Proof. vm_refl. Qed.
Lemma D_a1c10 : decode_any W_a1c10 = Some (Store SZ8 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c14 : bv 32 := 0x10051863.
Lemma F_a1c14 : fetch_word Ubsan.M.loaded_segments (0xa1c14 : word) = Some W_a1c14.
Proof. vm_refl. Qed.
Lemma D_a1c14 : decode_any W_a1c14 = Some (Branch BC_NE 10 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c18 : bv 32 := 0x00085517.
Lemma F_a1c18 : fetch_word Ubsan.M.loaded_segments (0xa1c18 : word) = Some W_a1c18.
Proof. vm_refl. Qed.
Lemma D_a1c18 : decode_any W_a1c18 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c1c : bv 32 := 0xe5853503.
Lemma F_a1c1c : fetch_word Ubsan.M.loaded_segments (0xa1c1c : word) = Some W_a1c1c.
Proof. vm_refl. Qed.
Lemma D_a1c1c : decode_any W_a1c1c = Some (Load SZ8 true 10 10 3672, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c20 : bv 32 := 0x00052503.
Lemma F_a1c20 : fetch_word Ubsan.M.loaded_segments (0xa1c20 : word) = Some W_a1c20.
Proof. vm_refl. Qed.
Lemma D_a1c20 : decode_any W_a1c20 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c24 : bv 32 := 0x00500593.
Lemma F_a1c24 : fetch_word Ubsan.M.loaded_segments (0xa1c24 : word) = Some W_a1c24.
Proof. vm_refl. Qed.
Lemma D_a1c24 : decode_any W_a1c24 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c28 : bv 32 := 0x0ea5ce63.
Lemma F_a1c28 : fetch_word Ubsan.M.loaded_segments (0xa1c28 : word) = Some W_a1c28.
Proof. vm_refl. Qed.
Lemma D_a1c28 : decode_any W_a1c28 = Some (Branch BC_LT 11 10 252, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c2c : bv 32 := 0xfff78517.
Lemma F_a1c2c : fetch_word Ubsan.M.loaded_segments (0xa1c2c : word) = Some W_a1c2c.
Proof. vm_refl. Qed.
Lemma D_a1c2c : decode_any W_a1c2c = Some (Auipc 10 1048440, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c30 : bv 32 := 0xfff7a597.
Lemma F_a1c30 : fetch_word Ubsan.M.loaded_segments (0xa1c30 : word) = Some W_a1c30.
Proof. vm_refl. Qed.
Lemma D_a1c30 : decode_any W_a1c30 = Some (Auipc 11 1048442, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c34 : bv 32 := 0x7e750513.
Lemma F_a1c34 : fetch_word Ubsan.M.loaded_segments (0xa1c34 : word) = Some W_a1c34.
Proof. vm_refl. Qed.
Lemma D_a1c34 : decode_any W_a1c34 = Some (OpImm ALU_ADD 10 10 2023, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c38 : bv 32 := 0x91a58593.
Lemma F_a1c38 : fetch_word Ubsan.M.loaded_segments (0xa1c38 : word) = Some W_a1c38.
Proof. vm_refl. Qed.
Lemma D_a1c38 : decode_any W_a1c38 = Some (OpImm ALU_ADD 11 11 2330, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c3c : bv 32 := 0x0bc0006f.
Lemma F_a1c3c : fetch_word Ubsan.M.loaded_segments (0xa1c3c : word) = Some W_a1c3c.
Proof. vm_refl. Qed.
Lemma D_a1c3c : decode_any W_a1c3c = Some (Jal 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c40 : bv 32 := 0x00085517.
Lemma F_a1c40 : fetch_word Ubsan.M.loaded_segments (0xa1c40 : word) = Some W_a1c40.
Proof. vm_refl. Qed.
Lemma D_a1c40 : decode_any W_a1c40 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c44 : bv 32 := 0xe3053503.
Lemma F_a1c44 : fetch_word Ubsan.M.loaded_segments (0xa1c44 : word) = Some W_a1c44.
Proof. vm_refl. Qed.
Lemma D_a1c44 : decode_any W_a1c44 = Some (Load SZ8 true 10 10 3632, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c48 : bv 32 := 0x00052503.
Lemma F_a1c48 : fetch_word Ubsan.M.loaded_segments (0xa1c48 : word) = Some W_a1c48.
Proof. vm_refl. Qed.
Lemma D_a1c48 : decode_any W_a1c48 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c4c : bv 32 := 0x00500593.
Lemma F_a1c4c : fetch_word Ubsan.M.loaded_segments (0xa1c4c : word) = Some W_a1c4c.
Proof. vm_refl. Qed.
Lemma D_a1c4c : decode_any W_a1c4c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c50 : bv 32 := 0x0ca5ca63.
Lemma F_a1c50 : fetch_word Ubsan.M.loaded_segments (0xa1c50 : word) = Some W_a1c50.
Proof. vm_refl. Qed.
Lemma D_a1c50 : decode_any W_a1c50 = Some (Branch BC_LT 11 10 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c54 : bv 32 := 0xfff6e517.
Lemma F_a1c54 : fetch_word Ubsan.M.loaded_segments (0xa1c54 : word) = Some W_a1c54.
Proof. vm_refl. Qed.
Lemma D_a1c54 : decode_any W_a1c54 = Some (Auipc 10 1048430, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c58 : bv 32 := 0xfff7a597.
Lemma F_a1c58 : fetch_word Ubsan.M.loaded_segments (0xa1c58 : word) = Some W_a1c58.
Proof. vm_refl. Qed.
Lemma D_a1c58 : decode_any W_a1c58 = Some (Auipc 11 1048442, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c5c : bv 32 := 0x70150513.
Lemma F_a1c5c : fetch_word Ubsan.M.loaded_segments (0xa1c5c : word) = Some W_a1c5c.
Proof. vm_refl. Qed.
Lemma D_a1c5c : decode_any W_a1c5c = Some (OpImm ALU_ADD 10 10 1793, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c60 : bv 32 := 0x8f258593.
Lemma F_a1c60 : fetch_word Ubsan.M.loaded_segments (0xa1c60 : word) = Some W_a1c60.
Proof. vm_refl. Qed.
Lemma D_a1c60 : decode_any W_a1c60 = Some (OpImm ALU_ADD 11 11 2290, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c64 : bv 32 := 0x0500006f.
Lemma F_a1c64 : fetch_word Ubsan.M.loaded_segments (0xa1c64 : word) = Some W_a1c64.
Proof. vm_refl. Qed.
Lemma D_a1c64 : decode_any W_a1c64 = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c68 : bv 32 := 0x00085517.
Lemma F_a1c68 : fetch_word Ubsan.M.loaded_segments (0xa1c68 : word) = Some W_a1c68.
Proof. vm_refl. Qed.
Lemma D_a1c68 : decode_any W_a1c68 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c6c : bv 32 := 0xe0853503.
Lemma F_a1c6c : fetch_word Ubsan.M.loaded_segments (0xa1c6c : word) = Some W_a1c6c.
Proof. vm_refl. Qed.
Lemma D_a1c6c : decode_any W_a1c6c = Some (Load SZ8 true 10 10 3592, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c70 : bv 32 := 0x00052503.
Lemma F_a1c70 : fetch_word Ubsan.M.loaded_segments (0xa1c70 : word) = Some W_a1c70.
Proof. vm_refl. Qed.
Lemma D_a1c70 : decode_any W_a1c70 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c74 : bv 32 := 0x00500593.
Lemma F_a1c74 : fetch_word Ubsan.M.loaded_segments (0xa1c74 : word) = Some W_a1c74.
Proof. vm_refl. Qed.
Lemma D_a1c74 : decode_any W_a1c74 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c78 : bv 32 := 0x0aa5c663.
Lemma F_a1c78 : fetch_word Ubsan.M.loaded_segments (0xa1c78 : word) = Some W_a1c78.
Proof. vm_refl. Qed.
Lemma D_a1c78 : decode_any W_a1c78 = Some (Branch BC_LT 11 10 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c7c : bv 32 := 0xfff75517.
Lemma F_a1c7c : fetch_word Ubsan.M.loaded_segments (0xa1c7c : word) = Some W_a1c7c.
Proof. vm_refl. Qed.
Lemma D_a1c7c : decode_any W_a1c7c = Some (Auipc 10 1048437, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c80 : bv 32 := 0xfff7a597.
Lemma F_a1c80 : fetch_word Ubsan.M.loaded_segments (0xa1c80 : word) = Some W_a1c80.
Proof. vm_refl. Qed.
Lemma D_a1c80 : decode_any W_a1c80 = Some (Auipc 11 1048442, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c84 : bv 32 := 0x58950513.
Lemma F_a1c84 : fetch_word Ubsan.M.loaded_segments (0xa1c84 : word) = Some W_a1c84.
Proof. vm_refl. Qed.
Lemma D_a1c84 : decode_any W_a1c84 = Some (OpImm ALU_ADD 10 10 1417, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c88 : bv 32 := 0x8ca58593.
Lemma F_a1c88 : fetch_word Ubsan.M.loaded_segments (0xa1c88 : word) = Some W_a1c88.
Proof. vm_refl. Qed.
Lemma D_a1c88 : decode_any W_a1c88 = Some (OpImm ALU_ADD 11 11 2250, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c8c : bv 32 := 0x0280006f.
Lemma F_a1c8c : fetch_word Ubsan.M.loaded_segments (0xa1c8c : word) = Some W_a1c8c.
Proof. vm_refl. Qed.
Lemma D_a1c8c : decode_any W_a1c8c = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c90 : bv 32 := 0x00085517.
Lemma F_a1c90 : fetch_word Ubsan.M.loaded_segments (0xa1c90 : word) = Some W_a1c90.
Proof. vm_refl. Qed.
Lemma D_a1c90 : decode_any W_a1c90 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c94 : bv 32 := 0xde053503.
Lemma F_a1c94 : fetch_word Ubsan.M.loaded_segments (0xa1c94 : word) = Some W_a1c94.
Proof. vm_refl. Qed.
Lemma D_a1c94 : decode_any W_a1c94 = Some (Load SZ8 true 10 10 3552, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c98 : bv 32 := 0x00052503.
Lemma F_a1c98 : fetch_word Ubsan.M.loaded_segments (0xa1c98 : word) = Some W_a1c98.
Proof. vm_refl. Qed.
Lemma D_a1c98 : decode_any W_a1c98 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1c9c : bv 32 := 0x00500593.
Lemma F_a1c9c : fetch_word Ubsan.M.loaded_segments (0xa1c9c : word) = Some W_a1c9c.
Proof. vm_refl. Qed.
Lemma D_a1c9c : decode_any W_a1c9c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ca0 : bv 32 := 0x08a5c263.
Lemma F_a1ca0 : fetch_word Ubsan.M.loaded_segments (0xa1ca0 : word) = Some W_a1ca0.
Proof. vm_refl. Qed.
Lemma D_a1ca0 : decode_any W_a1ca0 = Some (Branch BC_LT 11 10 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ca4 : bv 32 := 0xfff71517.
Lemma F_a1ca4 : fetch_word Ubsan.M.loaded_segments (0xa1ca4 : word) = Some W_a1ca4.
Proof. vm_refl. Qed.
Lemma D_a1ca4 : decode_any W_a1ca4 = Some (Auipc 10 1048433, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ca8 : bv 32 := 0xfff7a597.
Lemma F_a1ca8 : fetch_word Ubsan.M.loaded_segments (0xa1ca8 : word) = Some W_a1ca8.
Proof. vm_refl. Qed.
Lemma D_a1ca8 : decode_any W_a1ca8 = Some (Auipc 11 1048442, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cac : bv 32 := 0xa8450513.
Lemma F_a1cac : fetch_word Ubsan.M.loaded_segments (0xa1cac : word) = Some W_a1cac.
Proof. vm_refl. Qed.
Lemma D_a1cac : decode_any W_a1cac = Some (OpImm ALU_ADD 10 10 2692, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cb0 : bv 32 := 0x8a258593.
Lemma F_a1cb0 : fetch_word Ubsan.M.loaded_segments (0xa1cb0 : word) = Some W_a1cb0.
Proof. vm_refl. Qed.
Lemma D_a1cb0 : decode_any W_a1cb0 = Some (OpImm ALU_ADD 11 11 2210, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cb4 : bv 32 := 0x00040613.
Lemma F_a1cb4 : fetch_word Ubsan.M.loaded_segments (0xa1cb4 : word) = Some W_a1cb4.
Proof. vm_refl. Qed.
Lemma D_a1cb4 : decode_any W_a1cb4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cb8 : bv 32 := 0x02813083.
Lemma F_a1cb8 : fetch_word Ubsan.M.loaded_segments (0xa1cb8 : word) = Some W_a1cb8.
Proof. vm_refl. Qed.
Lemma D_a1cb8 : decode_any W_a1cb8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cbc : bv 32 := 0x02013403.
Lemma F_a1cbc : fetch_word Ubsan.M.loaded_segments (0xa1cbc : word) = Some W_a1cbc.
Proof. vm_refl. Qed.
Lemma D_a1cbc : decode_any W_a1cbc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cc0 : bv 32 := 0x01813483.
Lemma F_a1cc0 : fetch_word Ubsan.M.loaded_segments (0xa1cc0 : word) = Some W_a1cc0.
Proof. vm_refl. Qed.
Lemma D_a1cc0 : decode_any W_a1cc0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cc4 : bv 32 := 0x01013903.
Lemma F_a1cc4 : fetch_word Ubsan.M.loaded_segments (0xa1cc4 : word) = Some W_a1cc4.
Proof. vm_refl. Qed.
Lemma D_a1cc4 : decode_any W_a1cc4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cc8 : bv 32 := 0x00813983.
Lemma F_a1cc8 : fetch_word Ubsan.M.loaded_segments (0xa1cc8 : word) = Some W_a1cc8.
Proof. vm_refl. Qed.
Lemma D_a1cc8 : decode_any W_a1cc8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ccc : bv 32 := 0x03010113.
Lemma F_a1ccc : fetch_word Ubsan.M.loaded_segments (0xa1ccc : word) = Some W_a1ccc.
Proof. vm_refl. Qed.
Lemma D_a1ccc : decode_any W_a1ccc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cd0 : bv 32 := 0xa71c106f.
Lemma F_a1cd0 : fetch_word Ubsan.M.loaded_segments (0xa1cd0 : word) = Some W_a1cd0.
Proof. vm_refl. Qed.
Lemma D_a1cd0 : decode_any W_a1cd0 = Some (Jal 0 1841776, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cd4 : bv 32 := 0x00085517.
Lemma F_a1cd4 : fetch_word Ubsan.M.loaded_segments (0xa1cd4 : word) = Some W_a1cd4.
Proof. vm_refl. Qed.
Lemma D_a1cd4 : decode_any W_a1cd4 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cd8 : bv 32 := 0xd9c53503.
Lemma F_a1cd8 : fetch_word Ubsan.M.loaded_segments (0xa1cd8 : word) = Some W_a1cd8.
Proof. vm_refl. Qed.
Lemma D_a1cd8 : decode_any W_a1cd8 = Some (Load SZ8 true 10 10 3484, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cdc : bv 32 := 0x00052503.
Lemma F_a1cdc : fetch_word Ubsan.M.loaded_segments (0xa1cdc : word) = Some W_a1cdc.
Proof. vm_refl. Qed.
Lemma D_a1cdc : decode_any W_a1cdc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ce0 : bv 32 := 0x00500593.
Lemma F_a1ce0 : fetch_word Ubsan.M.loaded_segments (0xa1ce0 : word) = Some W_a1ce0.
Proof. vm_refl. Qed.
Lemma D_a1ce0 : decode_any W_a1ce0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ce4 : bv 32 := 0x04a5c063.
Lemma F_a1ce4 : fetch_word Ubsan.M.loaded_segments (0xa1ce4 : word) = Some W_a1ce4.
Proof. vm_refl. Qed.
Lemma D_a1ce4 : decode_any W_a1ce4 = Some (Branch BC_LT 11 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1ce8 : bv 32 := 0xfff73517.
Lemma F_a1ce8 : fetch_word Ubsan.M.loaded_segments (0xa1ce8 : word) = Some W_a1ce8.
Proof. vm_refl. Qed.
Lemma D_a1ce8 : decode_any W_a1ce8 = Some (Auipc 10 1048435, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cec : bv 32 := 0xfff7a597.
Lemma F_a1cec : fetch_word Ubsan.M.loaded_segments (0xa1cec : word) = Some W_a1cec.
Proof. vm_refl. Qed.
Lemma D_a1cec : decode_any W_a1cec = Some (Auipc 11 1048442, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cf0 : bv 32 := 0xf8250513.
Lemma F_a1cf0 : fetch_word Ubsan.M.loaded_segments (0xa1cf0 : word) = Some W_a1cf0.
Proof. vm_refl. Qed.
Lemma D_a1cf0 : decode_any W_a1cf0 = Some (OpImm ALU_ADD 10 10 3970, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cf4 : bv 32 := 0x85e58593.
Lemma F_a1cf4 : fetch_word Ubsan.M.loaded_segments (0xa1cf4 : word) = Some W_a1cf4.
Proof. vm_refl. Qed.
Lemma D_a1cf4 : decode_any W_a1cf4 = Some (OpImm ALU_ADD 11 11 2142, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cf8 : bv 32 := 0x00040613.
Lemma F_a1cf8 : fetch_word Ubsan.M.loaded_segments (0xa1cf8 : word) = Some W_a1cf8.
Proof. vm_refl. Qed.
Lemma D_a1cf8 : decode_any W_a1cf8 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1cfc : bv 32 := 0xa45c10ef.
Lemma F_a1cfc : fetch_word Ubsan.M.loaded_segments (0xa1cfc : word) = Some W_a1cfc.
Proof. vm_refl. Qed.
Lemma D_a1cfc : decode_any W_a1cfc = Some (Jal 1 1841732, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d00 : bv 32 := 0x00050413.
Lemma F_a1d00 : fetch_word Ubsan.M.loaded_segments (0xa1d00 : word) = Some W_a1d00.
Proof. vm_refl. Qed.
Lemma D_a1d00 : decode_any W_a1d00 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d04 : bv 32 := 0x0200006f.
Lemma F_a1d04 : fetch_word Ubsan.M.loaded_segments (0xa1d04 : word) = Some W_a1d04.
Proof. vm_refl. Qed.
Lemma D_a1d04 : decode_any W_a1d04 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d08 : bv 32 := 0x00048513.
Lemma F_a1d08 : fetch_word Ubsan.M.loaded_segments (0xa1d08 : word) = Some W_a1d08.
Proof. vm_refl. Qed.
Lemma D_a1d08 : decode_any W_a1d08 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d0c : bv 32 := 0xb6ccc0ef.
Lemma F_a1d0c : fetch_word Ubsan.M.loaded_segments (0xa1d0c : word) = Some W_a1d0c.
Proof. vm_refl. Qed.
Lemma D_a1d0c : decode_any W_a1d0c = Some (Jal 1 1885036, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d10 : bv 32 := 0x02050a63.
Lemma F_a1d10 : fetch_word Ubsan.M.loaded_segments (0xa1d10 : word) = Some W_a1d10.
Proof. vm_refl. Qed.
Lemma D_a1d10 : decode_any W_a1d10 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d14 : bv 32 := 0x00050413.
Lemma F_a1d14 : fetch_word Ubsan.M.loaded_segments (0xa1d14 : word) = Some W_a1d14.
Proof. vm_refl. Qed.
Lemma D_a1d14 : decode_any W_a1d14 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d18 : bv 32 := 0x00048513.
Lemma F_a1d18 : fetch_word Ubsan.M.loaded_segments (0xa1d18 : word) = Some W_a1d18.
Proof. vm_refl. Qed.
Lemma D_a1d18 : decode_any W_a1d18 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d1c : bv 32 := 0xdedcc0ef.
Lemma F_a1d1c : fetch_word Ubsan.M.loaded_segments (0xa1d1c : word) = Some W_a1d1c.
Proof. vm_refl. Qed.
Lemma D_a1d1c : decode_any W_a1d1c = Some (Jal 1 1887724, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d20 : bv 32 := 0x00a9b023.
Lemma F_a1d20 : fetch_word Ubsan.M.loaded_segments (0xa1d20 : word) = Some W_a1d20.
Proof. vm_refl. Qed.
Lemma D_a1d20 : decode_any W_a1d20 = Some (Store SZ8 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d24 : bv 32 := 0x00040513.
Lemma F_a1d24 : fetch_word Ubsan.M.loaded_segments (0xa1d24 : word) = Some W_a1d24.
Proof. vm_refl. Qed.
Lemma D_a1d24 : decode_any W_a1d24 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d28 : bv 32 := 0x02813083.
Lemma F_a1d28 : fetch_word Ubsan.M.loaded_segments (0xa1d28 : word) = Some W_a1d28.
Proof. vm_refl. Qed.
Lemma D_a1d28 : decode_any W_a1d28 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d2c : bv 32 := 0x02013403.
Lemma F_a1d2c : fetch_word Ubsan.M.loaded_segments (0xa1d2c : word) = Some W_a1d2c.
Proof. vm_refl. Qed.
Lemma D_a1d2c : decode_any W_a1d2c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d30 : bv 32 := 0x01813483.
Lemma F_a1d30 : fetch_word Ubsan.M.loaded_segments (0xa1d30 : word) = Some W_a1d30.
Proof. vm_refl. Qed.
Lemma D_a1d30 : decode_any W_a1d30 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d34 : bv 32 := 0x01013903.
Lemma F_a1d34 : fetch_word Ubsan.M.loaded_segments (0xa1d34 : word) = Some W_a1d34.
Proof. vm_refl. Qed.
Lemma D_a1d34 : decode_any W_a1d34 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d38 : bv 32 := 0x00813983.
Lemma F_a1d38 : fetch_word Ubsan.M.loaded_segments (0xa1d38 : word) = Some W_a1d38.
Proof. vm_refl. Qed.
Lemma D_a1d38 : decode_any W_a1d38 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d3c : bv 32 := 0x03010113.
Lemma F_a1d3c : fetch_word Ubsan.M.loaded_segments (0xa1d3c : word) = Some W_a1d3c.
Proof. vm_refl. Qed.
Lemma D_a1d3c : decode_any W_a1d3c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d40 : bv 32 := 0x00008067.
Lemma F_a1d40 : fetch_word Ubsan.M.loaded_segments (0xa1d40 : word) = Some W_a1d40.
Proof. vm_refl. Qed.
Lemma D_a1d40 : decode_any W_a1d40 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d44 : bv 32 := 0x00085517.
Lemma F_a1d44 : fetch_word Ubsan.M.loaded_segments (0xa1d44 : word) = Some W_a1d44.
Proof. vm_refl. Qed.
Lemma D_a1d44 : decode_any W_a1d44 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d48 : bv 32 := 0xd2c53503.
Lemma F_a1d48 : fetch_word Ubsan.M.loaded_segments (0xa1d48 : word) = Some W_a1d48.
Proof. vm_refl. Qed.
Lemma D_a1d48 : decode_any W_a1d48 = Some (Load SZ8 true 10 10 3372, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d4c : bv 32 := 0x00052503.
Lemma F_a1d4c : fetch_word Ubsan.M.loaded_segments (0xa1d4c : word) = Some W_a1d4c.
Proof. vm_refl. Qed.
Lemma D_a1d4c : decode_any W_a1d4c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d50 : bv 32 := 0x00500593.
Lemma F_a1d50 : fetch_word Ubsan.M.loaded_segments (0xa1d50 : word) = Some W_a1d50.
Proof. vm_refl. Qed.
Lemma D_a1d50 : decode_any W_a1d50 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d54 : bv 32 := 0x00a5ce63.
Lemma F_a1d54 : fetch_word Ubsan.M.loaded_segments (0xa1d54 : word) = Some W_a1d54.
Proof. vm_refl. Qed.
Lemma D_a1d54 : decode_any W_a1d54 = Some (Branch BC_LT 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d58 : bv 32 := 0xfff71517.
Lemma F_a1d58 : fetch_word Ubsan.M.loaded_segments (0xa1d58 : word) = Some W_a1d58.
Proof. vm_refl. Qed.
Lemma D_a1d58 : decode_any W_a1d58 = Some (Auipc 10 1048433, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d5c : bv 32 := 0xfff79597.
Lemma F_a1d5c : fetch_word Ubsan.M.loaded_segments (0xa1d5c : word) = Some W_a1d5c.
Proof. vm_refl. Qed.
Lemma D_a1d5c : decode_any W_a1d5c = Some (Auipc 11 1048441, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d60 : bv 32 := 0x98250513.
Lemma F_a1d60 : fetch_word Ubsan.M.loaded_segments (0xa1d60 : word) = Some W_a1d60.
Proof. vm_refl. Qed.
Lemma D_a1d60 : decode_any W_a1d60 = Some (OpImm ALU_ADD 10 10 2434, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d64 : bv 32 := 0x7ee58593.
Lemma F_a1d64 : fetch_word Ubsan.M.loaded_segments (0xa1d64 : word) = Some W_a1d64.
Proof. vm_refl. Qed.
Lemma D_a1d64 : decode_any W_a1d64 = Some (OpImm ALU_ADD 11 11 2030, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d68 : bv 32 := 0x00000613.
Lemma F_a1d68 : fetch_word Ubsan.M.loaded_segments (0xa1d68 : word) = Some W_a1d68.
Proof. vm_refl. Qed.
Lemma D_a1d68 : decode_any W_a1d68 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d6c : bv 32 := 0xf91ff06f.
Lemma F_a1d6c : fetch_word Ubsan.M.loaded_segments (0xa1d6c : word) = Some W_a1d6c.
Proof. vm_refl. Qed.
Lemma D_a1d6c : decode_any W_a1d6c = Some (Jal 0 2097040, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d70 : bv 32 := 0x00000413.
Lemma F_a1d70 : fetch_word Ubsan.M.loaded_segments (0xa1d70 : word) = Some W_a1d70.
Proof. vm_refl. Qed.
Lemma D_a1d70 : decode_any W_a1d70 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_a1d74 : bv 32 := 0xfb1ff06f.
Lemma F_a1d74 : fetch_word Ubsan.M.loaded_segments (0xa1d74 : word) = Some W_a1d74.
Proof. vm_refl. Qed.
Lemma D_a1d74 : decode_any W_a1d74 = Some (Jal 0 2097072, 4%Z).
Proof. vm_refl. Qed.
