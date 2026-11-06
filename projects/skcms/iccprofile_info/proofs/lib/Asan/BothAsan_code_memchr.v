(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_98b50 : bv 32 := 0x0ff5f593.
Lemma F_98b50 : fetch_word AsanUbsan.M.loaded_segments (0x98b50 : word) = Some W_98b50.
Proof. vm_refl. Qed.
Lemma D_98b50 : decode_any W_98b50 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b54 : bv 32 := 0x00757693.
Lemma F_98b54 : fetch_word AsanUbsan.M.loaded_segments (0x98b54 : word) = Some W_98b54.
Proof. vm_refl. Qed.
Lemma D_98b54 : decode_any W_98b54 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b58 : bv 32 := 0x00c03733.
Lemma F_98b58 : fetch_word AsanUbsan.M.loaded_segments (0x98b58 : word) = Some W_98b58.
Proof. vm_refl. Qed.
Lemma D_98b58 : decode_any W_98b58 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b5c : bv 32 := 0x02068c63.
Lemma F_98b5c : fetch_word AsanUbsan.M.loaded_segments (0x98b5c : word) = Some W_98b5c.
Proof. vm_refl. Qed.
Lemma D_98b5c : decode_any W_98b5c = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b60 : bv 32 := 0x02060a63.
Lemma F_98b60 : fetch_word AsanUbsan.M.loaded_segments (0x98b60 : word) = Some W_98b60.
Proof. vm_refl. Qed.
Lemma D_98b60 : decode_any W_98b60 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b64 : bv 32 := 0x00150793.
Lemma F_98b64 : fetch_word AsanUbsan.M.loaded_segments (0x98b64 : word) = Some W_98b64.
Proof. vm_refl. Qed.
Lemma D_98b64 : decode_any W_98b64 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b68 : bv 32 := 0x00100813.
Lemma F_98b68 : fetch_word AsanUbsan.M.loaded_segments (0x98b68 : word) = Some W_98b68.
Proof. vm_refl. Qed.
Lemma D_98b68 : decode_any W_98b68 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b6c : bv 32 := 0x00054703.
Lemma F_98b6c : fetch_word AsanUbsan.M.loaded_segments (0x98b6c : word) = Some W_98b6c.
Proof. vm_refl. Qed.
Lemma D_98b6c : decode_any W_98b6c = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b70 : bv 32 := 0x00060693.
Lemma F_98b70 : fetch_word AsanUbsan.M.loaded_segments (0x98b70 : word) = Some W_98b70.
Proof. vm_refl. Qed.
Lemma D_98b70 : decode_any W_98b70 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b74 : bv 32 := 0x06b70e63.
Lemma F_98b74 : fetch_word AsanUbsan.M.loaded_segments (0x98b74 : word) = Some W_98b74.
Proof. vm_refl. Qed.
Lemma D_98b74 : decode_any W_98b74 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b78 : bv 32 := 0x00150513.
Lemma F_98b78 : fetch_word AsanUbsan.M.loaded_segments (0x98b78 : word) = Some W_98b78.
Proof. vm_refl. Qed.
Lemma D_98b78 : decode_any W_98b78 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b7c : bv 32 := 0xfff68613.
Lemma F_98b7c : fetch_word AsanUbsan.M.loaded_segments (0x98b7c : word) = Some W_98b7c.
Proof. vm_refl. Qed.
Lemma D_98b7c : decode_any W_98b7c = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b80 : bv 32 := 0x0077f893.
Lemma F_98b80 : fetch_word AsanUbsan.M.loaded_segments (0x98b80 : word) = Some W_98b80.
Proof. vm_refl. Qed.
Lemma D_98b80 : decode_any W_98b80 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b84 : bv 32 := 0x00c03733.
Lemma F_98b84 : fetch_word AsanUbsan.M.loaded_segments (0x98b84 : word) = Some W_98b84.
Proof. vm_refl. Qed.
Lemma D_98b84 : decode_any W_98b84 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b88 : bv 32 := 0x00088663.
Lemma F_98b88 : fetch_word AsanUbsan.M.loaded_segments (0x98b88 : word) = Some W_98b88.
Proof. vm_refl. Qed.
Lemma D_98b88 : decode_any W_98b88 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b8c : bv 32 := 0x00178793.
Lemma F_98b8c : fetch_word AsanUbsan.M.loaded_segments (0x98b8c : word) = Some W_98b8c.
Proof. vm_refl. Qed.
Lemma D_98b8c : decode_any W_98b8c = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b90 : bv 32 := 0xfd069ee3.
Lemma F_98b90 : fetch_word AsanUbsan.M.loaded_segments (0x98b90 : word) = Some W_98b90.
Proof. vm_refl. Qed.
Lemma D_98b90 : decode_any W_98b90 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b94 : bv 32 := 0x06070863.
Lemma F_98b94 : fetch_word AsanUbsan.M.loaded_segments (0x98b94 : word) = Some W_98b94.
Proof. vm_refl. Qed.
Lemma D_98b94 : decode_any W_98b94 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b98 : bv 32 := 0x00054683.
Lemma F_98b98 : fetch_word AsanUbsan.M.loaded_segments (0x98b98 : word) = Some W_98b98.
Proof. vm_refl. Qed.
Lemma D_98b98 : decode_any W_98b98 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98b9c : bv 32 := 0x04b68663.
Lemma F_98b9c : fetch_word AsanUbsan.M.loaded_segments (0x98b9c : word) = Some W_98b9c.
Proof. vm_refl. Qed.
Lemma D_98b9c : decode_any W_98b9c = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ba0 : bv 32 := 0x00800693.
Lemma F_98ba0 : fetch_word AsanUbsan.M.loaded_segments (0x98ba0 : word) = Some W_98ba0.
Proof. vm_refl. Qed.
Lemma D_98ba0 : decode_any W_98ba0 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ba4 : bv 32 := 0x04d66263.
Lemma F_98ba4 : fetch_word AsanUbsan.M.loaded_segments (0x98ba4 : word) = Some W_98ba4.
Proof. vm_refl. Qed.
Lemma D_98ba4 : decode_any W_98ba4 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98ba8 : bv 32 := 0xfff77697.
Lemma F_98ba8 : fetch_word AsanUbsan.M.loaded_segments (0x98ba8 : word) = Some W_98ba8.
Proof. vm_refl. Qed.
Lemma D_98ba8 : decode_any W_98ba8 = Some (Auipc 13 1048439, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bac : bv 32 := 0x7c06b683.
Lemma F_98bac : fetch_word AsanUbsan.M.loaded_segments (0x98bac : word) = Some W_98bac.
Proof. vm_refl. Qed.
Lemma D_98bac : decode_any W_98bac = Some (Load SZ8 true 13 13 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bb0 : bv 32 := 0xfff77717.
Lemma F_98bb0 : fetch_word AsanUbsan.M.loaded_segments (0x98bb0 : word) = Some W_98bb0.
Proof. vm_refl. Qed.
Lemma D_98bb0 : decode_any W_98bb0 = Some (Auipc 14 1048439, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bb4 : bv 32 := 0x7a073703.
Lemma F_98bb4 : fetch_word AsanUbsan.M.loaded_segments (0x98bb4 : word) = Some W_98bb4.
Proof. vm_refl. Qed.
Lemma D_98bb4 : decode_any W_98bb4 = Some (Load SZ8 true 14 14 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bb8 : bv 32 := 0x00168793.
Lemma F_98bb8 : fetch_word AsanUbsan.M.loaded_segments (0x98bb8 : word) = Some W_98bb8.
Proof. vm_refl. Qed.
Lemma D_98bb8 : decode_any W_98bb8 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bbc : bv 32 := 0x02f587b3.
Lemma F_98bbc : fetch_word AsanUbsan.M.loaded_segments (0x98bbc : word) = Some W_98bbc.
Proof. vm_refl. Qed.
Lemma D_98bbc : decode_any W_98bbc = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bc0 : bv 32 := 0x00700813.
Lemma F_98bc0 : fetch_word AsanUbsan.M.loaded_segments (0x98bc0 : word) = Some W_98bc0.
Proof. vm_refl. Qed.
Lemma D_98bc0 : decode_any W_98bc0 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bc4 : bv 32 := 0x00053883.
Lemma F_98bc4 : fetch_word AsanUbsan.M.loaded_segments (0x98bc4 : word) = Some W_98bc4.
Proof. vm_refl. Qed.
Lemma D_98bc4 : decode_any W_98bc4 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bc8 : bv 32 := 0x00f8c8b3.
Lemma F_98bc8 : fetch_word AsanUbsan.M.loaded_segments (0x98bc8 : word) = Some W_98bc8.
Proof. vm_refl. Qed.
Lemma D_98bc8 : decode_any W_98bc8 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bcc : bv 32 := 0x411682b3.
Lemma F_98bcc : fetch_word AsanUbsan.M.loaded_segments (0x98bcc : word) = Some W_98bcc.
Proof. vm_refl. Qed.
Lemma D_98bcc : decode_any W_98bcc = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bd0 : bv 32 := 0x0112e8b3.
Lemma F_98bd0 : fetch_word AsanUbsan.M.loaded_segments (0x98bd0 : word) = Some W_98bd0.
Proof. vm_refl. Qed.
Lemma D_98bd0 : decode_any W_98bd0 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bd4 : bv 32 := 0x00e8f8b3.
Lemma F_98bd4 : fetch_word AsanUbsan.M.loaded_segments (0x98bd4 : word) = Some W_98bd4.
Proof. vm_refl. Qed.
Lemma D_98bd4 : decode_any W_98bd4 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bd8 : bv 32 := 0x02e89a63.
Lemma F_98bd8 : fetch_word AsanUbsan.M.loaded_segments (0x98bd8 : word) = Some W_98bd8.
Proof. vm_refl. Qed.
Lemma D_98bd8 : decode_any W_98bd8 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bdc : bv 32 := 0xff860613.
Lemma F_98bdc : fetch_word AsanUbsan.M.loaded_segments (0x98bdc : word) = Some W_98bdc.
Proof. vm_refl. Qed.
Lemma D_98bdc : decode_any W_98bdc = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98be0 : bv 32 := 0x00850513.
Lemma F_98be0 : fetch_word AsanUbsan.M.loaded_segments (0x98be0 : word) = Some W_98be0.
Proof. vm_refl. Qed.
Lemma D_98be0 : decode_any W_98be0 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98be4 : bv 32 := 0xfec860e3.
Lemma F_98be4 : fetch_word AsanUbsan.M.loaded_segments (0x98be4 : word) = Some W_98be4.
Proof. vm_refl. Qed.
Lemma D_98be4 : decode_any W_98be4 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98be8 : bv 32 := 0x00060693.
Lemma F_98be8 : fetch_word AsanUbsan.M.loaded_segments (0x98be8 : word) = Some W_98be8.
Proof. vm_refl. Qed.
Lemma D_98be8 : decode_any W_98be8 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bec : bv 32 := 0x00060c63.
Lemma F_98bec : fetch_word AsanUbsan.M.loaded_segments (0x98bec : word) = Some W_98bec.
Proof. vm_refl. Qed.
Lemma D_98bec : decode_any W_98bec = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bf0 : bv 32 := 0x00054603.
Lemma F_98bf0 : fetch_word AsanUbsan.M.loaded_segments (0x98bf0 : word) = Some W_98bf0.
Proof. vm_refl. Qed.
Lemma D_98bf0 : decode_any W_98bf0 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bf4 : bv 32 := 0x00b60a63.
Lemma F_98bf4 : fetch_word AsanUbsan.M.loaded_segments (0x98bf4 : word) = Some W_98bf4.
Proof. vm_refl. Qed.
Lemma D_98bf4 : decode_any W_98bf4 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bf8 : bv 32 := 0xfff68693.
Lemma F_98bf8 : fetch_word AsanUbsan.M.loaded_segments (0x98bf8 : word) = Some W_98bf8.
Proof. vm_refl. Qed.
Lemma D_98bf8 : decode_any W_98bf8 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98bfc : bv 32 := 0x00150513.
Lemma F_98bfc : fetch_word AsanUbsan.M.loaded_segments (0x98bfc : word) = Some W_98bfc.
Proof. vm_refl. Qed.
Lemma D_98bfc : decode_any W_98bfc = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c00 : bv 32 := 0xfe0698e3.
Lemma F_98c00 : fetch_word AsanUbsan.M.loaded_segments (0x98c00 : word) = Some W_98c00.
Proof. vm_refl. Qed.
Lemma D_98c00 : decode_any W_98c00 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c04 : bv 32 := 0x00000513.
Lemma F_98c04 : fetch_word AsanUbsan.M.loaded_segments (0x98c04 : word) = Some W_98c04.
Proof. vm_refl. Qed.
Lemma D_98c04 : decode_any W_98c04 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c08 : bv 32 := 0x00008067.
Lemma F_98c08 : fetch_word AsanUbsan.M.loaded_segments (0x98c08 : word) = Some W_98c08.
Proof. vm_refl. Qed.
Lemma D_98c08 : decode_any W_98c08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c0c : bv 32 := 0x00060693.
Lemma F_98c0c : fetch_word AsanUbsan.M.loaded_segments (0x98c0c : word) = Some W_98c0c.
Proof. vm_refl. Qed.
Lemma D_98c0c : decode_any W_98c0c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c10 : bv 32 := 0x00054603.
Lemma F_98c10 : fetch_word AsanUbsan.M.loaded_segments (0x98c10 : word) = Some W_98c10.
Proof. vm_refl. Qed.
Lemma D_98c10 : decode_any W_98c10 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c14 : bv 32 := 0xfeb612e3.
Lemma F_98c14 : fetch_word AsanUbsan.M.loaded_segments (0x98c14 : word) = Some W_98c14.
Proof. vm_refl. Qed.
Lemma D_98c14 : decode_any W_98c14 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98c18 : bv 32 := 0xff1ff06f.
Lemma F_98c18 : fetch_word AsanUbsan.M.loaded_segments (0x98c18 : word) = Some W_98c18.
Proof. vm_refl. Qed.
Lemma D_98c18 : decode_any W_98c18 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_994d8 : bv 32 := 0xfe010113.
Lemma F_994d8 : fetch_word AsanUbsan.M.loaded_segments (0x994d8 : word) = Some W_994d8.
Proof. vm_refl. Qed.
Lemma D_994d8 : decode_any W_994d8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_994dc : bv 32 := 0x00113c23.
Lemma F_994dc : fetch_word AsanUbsan.M.loaded_segments (0x994dc : word) = Some W_994dc.
Proof. vm_refl. Qed.
Lemma D_994dc : decode_any W_994dc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_994e0 : bv 32 := 0x00813823.
Lemma F_994e0 : fetch_word AsanUbsan.M.loaded_segments (0x994e0 : word) = Some W_994e0.
Proof. vm_refl. Qed.
Lemma D_994e0 : decode_any W_994e0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_994e4 : bv 32 := 0x00913423.
Lemma F_994e4 : fetch_word AsanUbsan.M.loaded_segments (0x994e4 : word) = Some W_994e4.
Proof. vm_refl. Qed.
Lemma D_994e4 : decode_any W_994e4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_994e8 : bv 32 := 0x00058413.
Lemma F_994e8 : fetch_word AsanUbsan.M.loaded_segments (0x994e8 : word) = Some W_994e8.
Proof. vm_refl. Qed.
Lemma D_994e8 : decode_any W_994e8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_994ec : bv 32 := 0x00050493.
Lemma F_994ec : fetch_word AsanUbsan.M.loaded_segments (0x994ec : word) = Some W_994ec.
Proof. vm_refl. Qed.
Lemma D_994ec : decode_any W_994ec = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_994f0 : bv 32 := 0x00000593.
Lemma F_994f0 : fetch_word AsanUbsan.M.loaded_segments (0x994f0 : word) = Some W_994f0.
Proof. vm_refl. Qed.
Lemma D_994f0 : decode_any W_994f0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_994f4 : bv 32 := 0x00040613.
Lemma F_994f4 : fetch_word AsanUbsan.M.loaded_segments (0x994f4 : word) = Some W_994f4.
Proof. vm_refl. Qed.
Lemma D_994f4 : decode_any W_994f4 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_994f8 : bv 32 := 0xd70a80ef.
Lemma F_994f8 : fetch_word AsanUbsan.M.loaded_segments (0x994f8 : word) = Some W_994f8.
Proof. vm_refl. Qed.
Lemma D_994f8 : decode_any W_994f8 = Some (Jal 1 1738096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_994fc : bv 32 := 0x00050463.
Lemma F_994fc : fetch_word AsanUbsan.M.loaded_segments (0x994fc : word) = Some W_994fc.
Proof. vm_refl. Qed.
Lemma D_994fc : decode_any W_994fc = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99500 : bv 32 := 0x40950433.
Lemma F_99500 : fetch_word AsanUbsan.M.loaded_segments (0x99500 : word) = Some W_99500.
Proof. vm_refl. Qed.
Lemma D_99500 : decode_any W_99500 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99504 : bv 32 := 0x00040513.
Lemma F_99504 : fetch_word AsanUbsan.M.loaded_segments (0x99504 : word) = Some W_99504.
Proof. vm_refl. Qed.
Lemma D_99504 : decode_any W_99504 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99508 : bv 32 := 0x01813083.
Lemma F_99508 : fetch_word AsanUbsan.M.loaded_segments (0x99508 : word) = Some W_99508.
Proof. vm_refl. Qed.
Lemma D_99508 : decode_any W_99508 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9950c : bv 32 := 0x01013403.
Lemma F_9950c : fetch_word AsanUbsan.M.loaded_segments (0x9950c : word) = Some W_9950c.
Proof. vm_refl. Qed.
Lemma D_9950c : decode_any W_9950c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99510 : bv 32 := 0x00813483.
Lemma F_99510 : fetch_word AsanUbsan.M.loaded_segments (0x99510 : word) = Some W_99510.
Proof. vm_refl. Qed.
Lemma D_99510 : decode_any W_99510 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99514 : bv 32 := 0x02010113.
Lemma F_99514 : fetch_word AsanUbsan.M.loaded_segments (0x99514 : word) = Some W_99514.
Proof. vm_refl. Qed.
Lemma D_99514 : decode_any W_99514 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_99518 : bv 32 := 0x00008067.
Lemma F_99518 : fetch_word AsanUbsan.M.loaded_segments (0x99518 : word) = Some W_99518.
Proof. vm_refl. Qed.
Lemma D_99518 : decode_any W_99518 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
