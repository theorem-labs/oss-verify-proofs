(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1d6b98 : bv 32 := 0xff010113.
Lemma F_1d6b98 : fetch_word AsanUbsan.M.loaded_segments (0x1d1b68 : word) = Some W_1d6b98.
Proof. vm_refl. Qed.
Lemma D_1d6b98 : decode_any W_1d6b98 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6b9c : bv 32 := 0x00113423.
Lemma F_1d6b9c : fetch_word AsanUbsan.M.loaded_segments (0x1d1b6c : word) = Some W_1d6b9c.
Proof. vm_refl. Qed.
Lemma D_1d6b9c : decode_any W_1d6b9c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6ba0 : bv 32 := 0x00813023.
Lemma F_1d6ba0 : fetch_word AsanUbsan.M.loaded_segments (0x1d1b70 : word) = Some W_1d6ba0.
Proof. vm_refl. Qed.
Lemma D_1d6ba0 : decode_any W_1d6ba0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6ba4 : bv 32 := 0x01010413.
Lemma F_1d6ba4 : fetch_word AsanUbsan.M.loaded_segments (0x1d1b74 : word) = Some W_1d6ba4.
Proof. vm_refl. Qed.
Lemma D_1d6ba4 : decode_any W_1d6ba4 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6ba8 : bv 32 := 0x0040d517.
Lemma F_1d6ba8 : fetch_word AsanUbsan.M.loaded_segments (0x1d1b78 : word) = Some W_1d6ba8.
Proof. vm_refl. Qed.
Lemma D_1d6ba8 : decode_any W_1d6ba8 = Some (Auipc 10 1037, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bac : bv 32 := 0xfa053503.
Lemma F_1d6bac : fetch_word AsanUbsan.M.loaded_segments (0x1d1b7c : word) = Some W_1d6bac.
Proof. vm_refl. Qed.
Lemma D_1d6bac : decode_any W_1d6bac = Some (Load SZ8 true 10 10 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bb0 : bv 32 := 0x00050a63.
Lemma F_1d6bb0 : fetch_word AsanUbsan.M.loaded_segments (0x1d1b80 : word) = Some W_1d6bb0.
Proof. vm_refl. Qed.
Lemma D_1d6bb0 : decode_any W_1d6bb0 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bb4 : bv 32 := 0x0040e517.
Lemma F_1d6bb4 : fetch_word AsanUbsan.M.loaded_segments (0x1d1b84 : word) = Some W_1d6bb4.
Proof. vm_refl. Qed.
Lemma D_1d6bb4 : decode_any W_1d6bb4 = Some (Auipc 10 1038, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bb8 : bv 32 := 0xb2453503.
Lemma F_1d6bb8 : fetch_word AsanUbsan.M.loaded_segments (0x1d1b88 : word) = Some W_1d6bb8.
Proof. vm_refl. Qed.
Lemma D_1d6bb8 : decode_any W_1d6bb8 = Some (Load SZ8 true 10 10 2852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bbc : bv 32 := 0x00053503.
Lemma F_1d6bbc : fetch_word AsanUbsan.M.loaded_segments (0x1d1b8c : word) = Some W_1d6bbc.
Proof. vm_refl. Qed.
Lemma D_1d6bbc : decode_any W_1d6bbc = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bc0 : bv 32 := 0x00c0006f.
Lemma F_1d6bc0 : fetch_word AsanUbsan.M.loaded_segments (0x1d1b90 : word) = Some W_1d6bc0.
Proof. vm_refl. Qed.
Lemma D_1d6bc0 : decode_any W_1d6bc0 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bc4 : bv 32 := 0x0c040663.
Lemma F_1d6bc4 : fetch_word AsanUbsan.M.loaded_segments (0x1d1b94 : word) = Some W_1d6bc4.
Proof. vm_refl. Qed.
Lemma D_1d6bc4 : decode_any W_1d6bc4 = Some (Branch BC_EQ 8 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bc8 : bv 32 := 0x00040513.
Lemma F_1d6bc8 : fetch_word AsanUbsan.M.loaded_segments (0x1d1b98 : word) = Some W_1d6bc8.
Proof. vm_refl. Qed.
Lemma D_1d6bc8 : decode_any W_1d6bc8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bcc : bv 32 := 0x00155593.
Lemma F_1d6bcc : fetch_word AsanUbsan.M.loaded_segments (0x1d1b9c : word) = Some W_1d6bcc.
Proof. vm_refl. Qed.
Lemma D_1d6bcc : decode_any W_1d6bcc = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bd0 : bv 32 := 0x55555637.
Lemma F_1d6bd0 : fetch_word AsanUbsan.M.loaded_segments (0x1d1ba0 : word) = Some W_1d6bd0.
Proof. vm_refl. Qed.
Lemma D_1d6bd0 : decode_any W_1d6bd0 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bd4 : bv 32 := 0x333336b7.
Lemma F_1d6bd4 : fetch_word AsanUbsan.M.loaded_segments (0x1d1ba4 : word) = Some W_1d6bd4.
Proof. vm_refl. Qed.
Lemma D_1d6bd4 : decode_any W_1d6bd4 = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bd8 : bv 32 := 0x0f0f1737.
Lemma F_1d6bd8 : fetch_word AsanUbsan.M.loaded_segments (0x1d1ba8 : word) = Some W_1d6bd8.
Proof. vm_refl. Qed.
Lemma D_1d6bd8 : decode_any W_1d6bd8 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bdc : bv 32 := 0x010107b7.
Lemma F_1d6bdc : fetch_word AsanUbsan.M.loaded_segments (0x1d1bac : word) = Some W_1d6bdc.
Proof. vm_refl. Qed.
Lemma D_1d6bdc : decode_any W_1d6bdc = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6be0 : bv 32 := 0x00b56533.
Lemma F_1d6be0 : fetch_word AsanUbsan.M.loaded_segments (0x1d1bb0 : word) = Some W_1d6be0.
Proof. vm_refl. Qed.
Lemma D_1d6be0 : decode_any W_1d6be0 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6be4 : bv 32 := 0x5556059b.
Lemma F_1d6be4 : fetch_word AsanUbsan.M.loaded_segments (0x1d1bb4 : word) = Some W_1d6be4.
Proof. vm_refl. Qed.
Lemma D_1d6be4 : decode_any W_1d6be4 = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6be8 : bv 32 := 0x3336861b.
Lemma F_1d6be8 : fetch_word AsanUbsan.M.loaded_segments (0x1d1bb8 : word) = Some W_1d6be8.
Proof. vm_refl. Qed.
Lemma D_1d6be8 : decode_any W_1d6be8 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bec : bv 32 := 0xf0f7069b.
Lemma F_1d6bec : fetch_word AsanUbsan.M.loaded_segments (0x1d1bbc : word) = Some W_1d6bec.
Proof. vm_refl. Qed.
Lemma D_1d6bec : decode_any W_1d6bec = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bf0 : bv 32 := 0x1017871b.
Lemma F_1d6bf0 : fetch_word AsanUbsan.M.loaded_segments (0x1d1bc0 : word) = Some W_1d6bf0.
Proof. vm_refl. Qed.
Lemma D_1d6bf0 : decode_any W_1d6bf0 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bf4 : bv 32 := 0x00255793.
Lemma F_1d6bf4 : fetch_word AsanUbsan.M.loaded_segments (0x1d1bc4 : word) = Some W_1d6bf4.
Proof. vm_refl. Qed.
Lemma D_1d6bf4 : decode_any W_1d6bf4 = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bf8 : bv 32 := 0x00f56533.
Lemma F_1d6bf8 : fetch_word AsanUbsan.M.loaded_segments (0x1d1bc8 : word) = Some W_1d6bf8.
Proof. vm_refl. Qed.
Lemma D_1d6bf8 : decode_any W_1d6bf8 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6bfc : bv 32 := 0x02059793.
Lemma F_1d6bfc : fetch_word AsanUbsan.M.loaded_segments (0x1d1bcc : word) = Some W_1d6bfc.
Proof. vm_refl. Qed.
Lemma D_1d6bfc : decode_any W_1d6bfc = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c00 : bv 32 := 0x00f585b3.
Lemma F_1d6c00 : fetch_word AsanUbsan.M.loaded_segments (0x1d1bd0 : word) = Some W_1d6c00.
Proof. vm_refl. Qed.
Lemma D_1d6c00 : decode_any W_1d6c00 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c04 : bv 32 := 0x02061793.
Lemma F_1d6c04 : fetch_word AsanUbsan.M.loaded_segments (0x1d1bd4 : word) = Some W_1d6c04.
Proof. vm_refl. Qed.
Lemma D_1d6c04 : decode_any W_1d6c04 = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c08 : bv 32 := 0x00f60633.
Lemma F_1d6c08 : fetch_word AsanUbsan.M.loaded_segments (0x1d1bd8 : word) = Some W_1d6c08.
Proof. vm_refl. Qed.
Lemma D_1d6c08 : decode_any W_1d6c08 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c0c : bv 32 := 0x02069793.
Lemma F_1d6c0c : fetch_word AsanUbsan.M.loaded_segments (0x1d1bdc : word) = Some W_1d6c0c.
Proof. vm_refl. Qed.
Lemma D_1d6c0c : decode_any W_1d6c0c = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c10 : bv 32 := 0x00f686b3.
Lemma F_1d6c10 : fetch_word AsanUbsan.M.loaded_segments (0x1d1be0 : word) = Some W_1d6c10.
Proof. vm_refl. Qed.
Lemma D_1d6c10 : decode_any W_1d6c10 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c14 : bv 32 := 0x02071793.
Lemma F_1d6c14 : fetch_word AsanUbsan.M.loaded_segments (0x1d1be4 : word) = Some W_1d6c14.
Proof. vm_refl. Qed.
Lemma D_1d6c14 : decode_any W_1d6c14 = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c18 : bv 32 := 0x00f70733.
Lemma F_1d6c18 : fetch_word AsanUbsan.M.loaded_segments (0x1d1be8 : word) = Some W_1d6c18.
Proof. vm_refl. Qed.
Lemma D_1d6c18 : decode_any W_1d6c18 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c1c : bv 32 := 0x00455793.
Lemma F_1d6c1c : fetch_word AsanUbsan.M.loaded_segments (0x1d1bec : word) = Some W_1d6c1c.
Proof. vm_refl. Qed.
Lemma D_1d6c1c : decode_any W_1d6c1c = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c20 : bv 32 := 0x00f56533.
Lemma F_1d6c20 : fetch_word AsanUbsan.M.loaded_segments (0x1d1bf0 : word) = Some W_1d6c20.
Proof. vm_refl. Qed.
Lemma D_1d6c20 : decode_any W_1d6c20 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c24 : bv 32 := 0x00855793.
Lemma F_1d6c24 : fetch_word AsanUbsan.M.loaded_segments (0x1d1bf4 : word) = Some W_1d6c24.
Proof. vm_refl. Qed.
Lemma D_1d6c24 : decode_any W_1d6c24 = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c28 : bv 32 := 0x00f56533.
Lemma F_1d6c28 : fetch_word AsanUbsan.M.loaded_segments (0x1d1bf8 : word) = Some W_1d6c28.
Proof. vm_refl. Qed.
Lemma D_1d6c28 : decode_any W_1d6c28 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c2c : bv 32 := 0x01055793.
Lemma F_1d6c2c : fetch_word AsanUbsan.M.loaded_segments (0x1d1bfc : word) = Some W_1d6c2c.
Proof. vm_refl. Qed.
Lemma D_1d6c2c : decode_any W_1d6c2c = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c30 : bv 32 := 0x00f56533.
Lemma F_1d6c30 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c00 : word) = Some W_1d6c30.
Proof. vm_refl. Qed.
Lemma D_1d6c30 : decode_any W_1d6c30 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c34 : bv 32 := 0x02055793.
Lemma F_1d6c34 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c04 : word) = Some W_1d6c34.
Proof. vm_refl. Qed.
Lemma D_1d6c34 : decode_any W_1d6c34 = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c38 : bv 32 := 0x00f56533.
Lemma F_1d6c38 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c08 : word) = Some W_1d6c38.
Proof. vm_refl. Qed.
Lemma D_1d6c38 : decode_any W_1d6c38 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c3c : bv 32 := 0xfff54513.
Lemma F_1d6c3c : fetch_word AsanUbsan.M.loaded_segments (0x1d1c0c : word) = Some W_1d6c3c.
Proof. vm_refl. Qed.
Lemma D_1d6c3c : decode_any W_1d6c3c = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c40 : bv 32 := 0x00155793.
Lemma F_1d6c40 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c10 : word) = Some W_1d6c40.
Proof. vm_refl. Qed.
Lemma D_1d6c40 : decode_any W_1d6c40 = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c44 : bv 32 := 0x00b7f5b3.
Lemma F_1d6c44 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c14 : word) = Some W_1d6c44.
Proof. vm_refl. Qed.
Lemma D_1d6c44 : decode_any W_1d6c44 = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c48 : bv 32 := 0x40b50533.
Lemma F_1d6c48 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c18 : word) = Some W_1d6c48.
Proof. vm_refl. Qed.
Lemma D_1d6c48 : decode_any W_1d6c48 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c4c : bv 32 := 0x00c575b3.
Lemma F_1d6c4c : fetch_word AsanUbsan.M.loaded_segments (0x1d1c1c : word) = Some W_1d6c4c.
Proof. vm_refl. Qed.
Lemma D_1d6c4c : decode_any W_1d6c4c = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c50 : bv 32 := 0x00255513.
Lemma F_1d6c50 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c20 : word) = Some W_1d6c50.
Proof. vm_refl. Qed.
Lemma D_1d6c50 : decode_any W_1d6c50 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c54 : bv 32 := 0x00c57533.
Lemma F_1d6c54 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c24 : word) = Some W_1d6c54.
Proof. vm_refl. Qed.
Lemma D_1d6c54 : decode_any W_1d6c54 = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c58 : bv 32 := 0x00a58533.
Lemma F_1d6c58 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c28 : word) = Some W_1d6c58.
Proof. vm_refl. Qed.
Lemma D_1d6c58 : decode_any W_1d6c58 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c5c : bv 32 := 0x00455593.
Lemma F_1d6c5c : fetch_word AsanUbsan.M.loaded_segments (0x1d1c2c : word) = Some W_1d6c5c.
Proof. vm_refl. Qed.
Lemma D_1d6c5c : decode_any W_1d6c5c = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c60 : bv 32 := 0x00b50533.
Lemma F_1d6c60 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c30 : word) = Some W_1d6c60.
Proof. vm_refl. Qed.
Lemma D_1d6c60 : decode_any W_1d6c60 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c64 : bv 32 := 0x00d57533.
Lemma F_1d6c64 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c34 : word) = Some W_1d6c64.
Proof. vm_refl. Qed.
Lemma D_1d6c64 : decode_any W_1d6c64 = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c68 : bv 32 := 0x02e50533.
Lemma F_1d6c68 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c38 : word) = Some W_1d6c68.
Proof. vm_refl. Qed.
Lemma D_1d6c68 : decode_any W_1d6c68 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c6c : bv 32 := 0x03855513.
Lemma F_1d6c6c : fetch_word AsanUbsan.M.loaded_segments (0x1d1c3c : word) = Some W_1d6c6c.
Proof. vm_refl. Qed.
Lemma D_1d6c6c : decode_any W_1d6c6c = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c70 : bv 32 := 0x40a0053b.
Lemma F_1d6c70 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c40 : word) = Some W_1d6c70.
Proof. vm_refl. Qed.
Lemma D_1d6c70 : decode_any W_1d6c70 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c74 : bv 32 := 0xfff00593.
Lemma F_1d6c74 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c44 : word) = Some W_1d6c74.
Proof. vm_refl. Qed.
Lemma D_1d6c74 : decode_any W_1d6c74 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c78 : bv 32 := 0x00a59533.
Lemma F_1d6c78 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c48 : word) = Some W_1d6c78.
Proof. vm_refl. Qed.
Lemma D_1d6c78 : decode_any W_1d6c78 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c7c : bv 32 := 0xfff54513.
Lemma F_1d6c7c : fetch_word AsanUbsan.M.loaded_segments (0x1d1c4c : word) = Some W_1d6c7c.
Proof. vm_refl. Qed.
Lemma D_1d6c7c : decode_any W_1d6c7c = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c80 : bv 32 := 0x00813083.
Lemma F_1d6c80 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c50 : word) = Some W_1d6c80.
Proof. vm_refl. Qed.
Lemma D_1d6c80 : decode_any W_1d6c80 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c84 : bv 32 := 0x00013403.
Lemma F_1d6c84 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c54 : word) = Some W_1d6c84.
Proof. vm_refl. Qed.
Lemma D_1d6c84 : decode_any W_1d6c84 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c88 : bv 32 := 0x01010113.
Lemma F_1d6c88 : fetch_word AsanUbsan.M.loaded_segments (0x1d1c58 : word) = Some W_1d6c88.
Proof. vm_refl. Qed.
Lemma D_1d6c88 : decode_any W_1d6c88 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6c8c : bv 32 := 0x00008067.
Lemma F_1d6c8c : fetch_word AsanUbsan.M.loaded_segments (0x1d1c5c : word) = Some W_1d6c8c.
Proof. vm_refl. Qed.
Lemma D_1d6c8c : decode_any W_1d6c8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
