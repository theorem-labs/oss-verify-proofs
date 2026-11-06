(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_102bcc : bv 32 := 0xe8010113.
Lemma F_102bcc : fetch_word AsanUbsan.M.loaded_segments (0x102bcc : word) = Some W_102bcc.
Proof. vm_refl. Qed.
Lemma D_102bcc : decode_any W_102bcc = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102bd0 : bv 32 := 0x16113c23.
Lemma F_102bd0 : fetch_word AsanUbsan.M.loaded_segments (0x102bd0 : word) = Some W_102bd0.
Proof. vm_refl. Qed.
Lemma D_102bd0 : decode_any W_102bd0 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102bd4 : bv 32 := 0x16813823.
Lemma F_102bd4 : fetch_word AsanUbsan.M.loaded_segments (0x102bd4 : word) = Some W_102bd4.
Proof. vm_refl. Qed.
Lemma D_102bd4 : decode_any W_102bd4 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102bd8 : bv 32 := 0x16913423.
Lemma F_102bd8 : fetch_word AsanUbsan.M.loaded_segments (0x102bd8 : word) = Some W_102bd8.
Proof. vm_refl. Qed.
Lemma D_102bd8 : decode_any W_102bd8 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102bdc : bv 32 := 0x17213023.
Lemma F_102bdc : fetch_word AsanUbsan.M.loaded_segments (0x102bdc : word) = Some W_102bdc.
Proof. vm_refl. Qed.
Lemma D_102bdc : decode_any W_102bdc = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102be0 : bv 32 := 0x00058413.
Lemma F_102be0 : fetch_word AsanUbsan.M.loaded_segments (0x102be0 : word) = Some W_102be0.
Proof. vm_refl. Qed.
Lemma D_102be0 : decode_any W_102be0 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102be4 : bv 32 := 0x00050493.
Lemma F_102be4 : fetch_word AsanUbsan.M.loaded_segments (0x102be4 : word) = Some W_102be4.
Proof. vm_refl. Qed.
Lemma D_102be4 : decode_any W_102be4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102be8 : bv 32 := 0x03010513.
Lemma F_102be8 : fetch_word AsanUbsan.M.loaded_segments (0x102be8 : word) = Some W_102be8.
Proof. vm_refl. Qed.
Lemma D_102be8 : decode_any W_102be8 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102bec : bv 32 := 0x13000613.
Lemma F_102bec : fetch_word AsanUbsan.M.loaded_segments (0x102bec : word) = Some W_102bec.
Proof. vm_refl. Qed.
Lemma D_102bec : decode_any W_102bec = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102bf0 : bv 32 := 0x00000593.
Lemma F_102bf0 : fetch_word AsanUbsan.M.loaded_segments (0x102bf0 : word) = Some W_102bf0.
Proof. vm_refl. Qed.
Lemma D_102bf0 : decode_any W_102bf0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102bf4 : bv 32 := 0xdc16f0ef.
Lemma F_102bf4 : fetch_word AsanUbsan.M.loaded_segments (0x102bf4 : word) = Some W_102bf4.
Proof. vm_refl. Qed.
Lemma D_102bf4 : decode_any W_102bf4 = Some (Jal 1 1506752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102bf8 : bv 32 := 0x0001e517.
Lemma F_102bf8 : fetch_word AsanUbsan.M.loaded_segments (0x102bf8 : word) = Some W_102bf8.
Proof. vm_refl. Qed.
Lemma D_102bf8 : decode_any W_102bf8 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102bfc : bv 32 := 0x80053503.
Lemma F_102bfc : fetch_word AsanUbsan.M.loaded_segments (0x102bfc : word) = Some W_102bfc.
Proof. vm_refl. Qed.
Lemma D_102bfc : decode_any W_102bfc = Some (Load SZ8 true 10 10 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c00 : bv 32 := 0x00953023.
Lemma F_102c00 : fetch_word AsanUbsan.M.loaded_segments (0x102c00 : word) = Some W_102c00.
Proof. vm_refl. Qed.
Lemma D_102c00 : decode_any W_102c00 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c04 : bv 32 := 0x0004b503.
Lemma F_102c04 : fetch_word AsanUbsan.M.loaded_segments (0x102c04 : word) = Some W_102c04.
Proof. vm_refl. Qed.
Lemma D_102c04 : decode_any W_102c04 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c08 : bv 32 := 0x00848493.
Lemma F_102c08 : fetch_word AsanUbsan.M.loaded_segments (0x102c08 : word) = Some W_102c08.
Proof. vm_refl. Qed.
Lemma D_102c08 : decode_any W_102c08 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c0c : bv 32 := 0xfe051ce3.
Lemma F_102c0c : fetch_word AsanUbsan.M.loaded_segments (0x102c0c : word) = Some W_102c0c.
Proof. vm_refl. Qed.
Lemma D_102c0c : decode_any W_102c0c = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c10 : bv 32 := 0x0057f517.
Lemma F_102c10 : fetch_word AsanUbsan.M.loaded_segments (0x102c10 : word) = Some W_102c10.
Proof. vm_refl. Qed.
Lemma D_102c10 : decode_any W_102c10 = Some (Auipc 10 1407, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c14 : bv 32 := 0xe7050913.
Lemma F_102c14 : fetch_word AsanUbsan.M.loaded_segments (0x102c14 : word) = Some W_102c14.
Proof. vm_refl. Qed.
Lemma D_102c14 : decode_any W_102c14 = Some (OpImm ALU_ADD 18 10 3696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c18 : bv 32 := 0x00993423.
Lemma F_102c18 : fetch_word AsanUbsan.M.loaded_segments (0x102c18 : word) = Some W_102c18.
Proof. vm_refl. Qed.
Lemma D_102c18 : decode_any W_102c18 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c1c : bv 32 := 0x0004b583.
Lemma F_102c1c : fetch_word AsanUbsan.M.loaded_segments (0x102c1c : word) = Some W_102c1c.
Proof. vm_refl. Qed.
Lemma D_102c1c : decode_any W_102c1c = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c20 : bv 32 := 0x04058c63.
Lemma F_102c20 : fetch_word AsanUbsan.M.loaded_segments (0x102c20 : word) = Some W_102c20.
Proof. vm_refl. Qed.
Lemma D_102c20 : decode_any W_102c20 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c24 : bv 32 := 0x01048493.
Lemma F_102c24 : fetch_word AsanUbsan.M.loaded_segments (0x102c24 : word) = Some W_102c24.
Proof. vm_refl. Qed.
Lemma D_102c24 : decode_any W_102c24 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c28 : bv 32 := 0x02500513.
Lemma F_102c28 : fetch_word AsanUbsan.M.loaded_segments (0x102c28 : word) = Some W_102c28.
Proof. vm_refl. Qed.
Lemma D_102c28 : decode_any W_102c28 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c2c : bv 32 := 0x03010613.
Lemma F_102c2c : fetch_word AsanUbsan.M.loaded_segments (0x102c2c : word) = Some W_102c2c.
Proof. vm_refl. Qed.
Lemma D_102c2c : decode_any W_102c2c = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c30 : bv 32 := 0x0100006f.
Lemma F_102c30 : fetch_word AsanUbsan.M.loaded_segments (0x102c30 : word) = Some W_102c30.
Proof. vm_refl. Qed.
Lemma D_102c30 : decode_any W_102c30 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c34 : bv 32 := 0x0004b583.
Lemma F_102c34 : fetch_word AsanUbsan.M.loaded_segments (0x102c34 : word) = Some W_102c34.
Proof. vm_refl. Qed.
Lemma D_102c34 : decode_any W_102c34 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c38 : bv 32 := 0x01048493.
Lemma F_102c38 : fetch_word AsanUbsan.M.loaded_segments (0x102c38 : word) = Some W_102c38.
Proof. vm_refl. Qed.
Lemma D_102c38 : decode_any W_102c38 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c3c : bv 32 := 0x00058e63.
Lemma F_102c3c : fetch_word AsanUbsan.M.loaded_segments (0x102c3c : word) = Some W_102c3c.
Proof. vm_refl. Qed.
Lemma D_102c3c : decode_any W_102c3c = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c40 : bv 32 := 0xfeb56ae3.
Lemma F_102c40 : fetch_word AsanUbsan.M.loaded_segments (0x102c40 : word) = Some W_102c40.
Proof. vm_refl. Qed.
Lemma D_102c40 : decode_any W_102c40 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c44 : bv 32 := 0xff84b683.
Lemma F_102c44 : fetch_word AsanUbsan.M.loaded_segments (0x102c44 : word) = Some W_102c44.
Proof. vm_refl. Qed.
Lemma D_102c44 : decode_any W_102c44 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c48 : bv 32 := 0x00359593.
Lemma F_102c48 : fetch_word AsanUbsan.M.loaded_segments (0x102c48 : word) = Some W_102c48.
Proof. vm_refl. Qed.
Lemma D_102c48 : decode_any W_102c48 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c4c : bv 32 := 0x00b605b3.
Lemma F_102c4c : fetch_word AsanUbsan.M.loaded_segments (0x102c4c : word) = Some W_102c4c.
Proof. vm_refl. Qed.
Lemma D_102c4c : decode_any W_102c4c = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c50 : bv 32 := 0x00d5b023.
Lemma F_102c50 : fetch_word AsanUbsan.M.loaded_segments (0x102c50 : word) = Some W_102c50.
Proof. vm_refl. Qed.
Lemma D_102c50 : decode_any W_102c50 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c54 : bv 32 := 0xfe1ff06f.
Lemma F_102c54 : fetch_word AsanUbsan.M.loaded_segments (0x102c54 : word) = Some W_102c54.
Proof. vm_refl. Qed.
Lemma D_102c54 : decode_any W_102c54 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c58 : bv 32 := 0x0b013583.
Lemma F_102c58 : fetch_word AsanUbsan.M.loaded_segments (0x102c58 : word) = Some W_102c58.
Proof. vm_refl. Qed.
Lemma D_102c58 : decode_any W_102c58 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c5c : bv 32 := 0x13013503.
Lemma F_102c5c : fetch_word AsanUbsan.M.loaded_segments (0x102c5c : word) = Some W_102c5c.
Proof. vm_refl. Qed.
Lemma D_102c5c : decode_any W_102c5c = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c60 : bv 32 := 0x0057f617.
Lemma F_102c60 : fetch_word AsanUbsan.M.loaded_segments (0x102c60 : word) = Some W_102c60.
Proof. vm_refl. Qed.
Lemma D_102c60 : decode_any W_102c60 = Some (Auipc 12 1407, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c64 : bv 32 := 0xe8b63423.
Lemma F_102c64 : fetch_word AsanUbsan.M.loaded_segments (0x102c64 : word) = Some W_102c64.
Proof. vm_refl. Qed.
Lemma D_102c64 : decode_any W_102c64 = Some (Store SZ8 12 11 3720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c68 : bv 32 := 0x00050c63.
Lemma F_102c68 : fetch_word AsanUbsan.M.loaded_segments (0x102c68 : word) = Some W_102c68.
Proof. vm_refl. Qed.
Lemma D_102c68 : decode_any W_102c68 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c6c : bv 32 := 0x0057f597.
Lemma F_102c6c : fetch_word AsanUbsan.M.loaded_segments (0x102c6c : word) = Some W_102c6c.
Proof. vm_refl. Qed.
Lemma D_102c6c : decode_any W_102c6c = Some (Auipc 11 1407, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c70 : bv 32 := 0xdea5be23.
Lemma F_102c70 : fetch_word AsanUbsan.M.loaded_segments (0x102c70 : word) = Some W_102c70.
Proof. vm_refl. Qed.
Lemma D_102c70 : decode_any W_102c70 = Some (Store SZ8 11 10 3580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c74 : bv 32 := 0x00c0006f.
Lemma F_102c74 : fetch_word AsanUbsan.M.loaded_segments (0x102c74 : word) = Some W_102c74.
Proof. vm_refl. Qed.
Lemma D_102c74 : decode_any W_102c74 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c78 : bv 32 := 0x0057f517.
Lemma F_102c78 : fetch_word AsanUbsan.M.loaded_segments (0x102c78 : word) = Some W_102c78.
Proof. vm_refl. Qed.
Lemma D_102c78 : decode_any W_102c78 = Some (Auipc 10 1407, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c7c : bv 32 := 0xe6053823.
Lemma F_102c7c : fetch_word AsanUbsan.M.loaded_segments (0x102c7c : word) = Some W_102c7c.
Proof. vm_refl. Qed.
Lemma D_102c7c : decode_any W_102c7c = Some (Store SZ8 10 0 3696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c80 : bv 32 := 0x06013503.
Lemma F_102c80 : fetch_word AsanUbsan.M.loaded_segments (0x102c80 : word) = Some W_102c80.
Proof. vm_refl. Qed.
Lemma D_102c80 : decode_any W_102c80 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c84 : bv 32 := 0x02a93823.
Lemma F_102c84 : fetch_word AsanUbsan.M.loaded_segments (0x102c84 : word) = Some W_102c84.
Proof. vm_refl. Qed.
Lemma D_102c84 : decode_any W_102c84 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c88 : bv 32 := 0x00041463.
Lemma F_102c88 : fetch_word AsanUbsan.M.loaded_segments (0x102c88 : word) = Some W_102c88.
Proof. vm_refl. Qed.
Lemma D_102c88 : decode_any W_102c88 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c8c : bv 32 := 0x12813403.
Lemma F_102c8c : fetch_word AsanUbsan.M.loaded_segments (0x102c8c : word) = Some W_102c8c.
Proof. vm_refl. Qed.
Lemma D_102c8c : decode_any W_102c8c = Some (Load SZ8 true 8 2 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c90 : bv 32 := 0x00041663.
Lemma F_102c90 : fetch_word AsanUbsan.M.loaded_segments (0x102c90 : word) = Some W_102c90.
Proof. vm_refl. Qed.
Lemma D_102c90 : decode_any W_102c90 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c94 : bv 32 := 0xfff12517.
Lemma F_102c94 : fetch_word AsanUbsan.M.loaded_segments (0x102c94 : word) = Some W_102c94.
Proof. vm_refl. Qed.
Lemma D_102c94 : decode_any W_102c94 = Some (Auipc 10 1048338, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c98 : bv 32 := 0xd3050413.
Lemma F_102c98 : fetch_word AsanUbsan.M.loaded_segments (0x102c98 : word) = Some W_102c98.
Proof. vm_refl. Qed.
Lemma D_102c98 : decode_any W_102c98 = Some (OpImm ALU_ADD 8 10 3376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102c9c : bv 32 := 0x0001d517.
Lemma F_102c9c : fetch_word AsanUbsan.M.loaded_segments (0x102c9c : word) = Some W_102c9c.
Proof. vm_refl. Qed.
Lemma D_102c9c : decode_any W_102c9c = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102ca0 : bv 32 := 0x76453583.
Lemma F_102ca0 : fetch_word AsanUbsan.M.loaded_segments (0x102ca0 : word) = Some W_102ca0.
Proof. vm_refl. Qed.
Lemma D_102ca0 : decode_any W_102ca0 = Some (Load SZ8 true 11 10 1892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102ca4 : bv 32 := 0x0001d517.
Lemma F_102ca4 : fetch_word AsanUbsan.M.loaded_segments (0x102ca4 : word) = Some W_102ca4.
Proof. vm_refl. Qed.
Lemma D_102ca4 : decode_any W_102ca4 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102ca8 : bv 32 := 0x76453503.
Lemma F_102ca8 : fetch_word AsanUbsan.M.loaded_segments (0x102ca8 : word) = Some W_102ca8.
Proof. vm_refl. Qed.
Lemma D_102ca8 : decode_any W_102ca8 = Some (Load SZ8 true 10 10 1892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cac : bv 32 := 0x0085b023.
Lemma F_102cac : fetch_word AsanUbsan.M.loaded_segments (0x102cac : word) = Some W_102cac.
Proof. vm_refl. Qed.
Lemma D_102cac : decode_any W_102cac = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cb0 : bv 32 := 0x00140593.
Lemma F_102cb0 : fetch_word AsanUbsan.M.loaded_segments (0x102cb0 : word) = Some W_102cb0.
Proof. vm_refl. Qed.
Lemma D_102cb0 : decode_any W_102cb0 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cb4 : bv 32 := 0x00853023.
Lemma F_102cb4 : fetch_word AsanUbsan.M.loaded_segments (0x102cb4 : word) = Some W_102cb4.
Proof. vm_refl. Qed.
Lemma D_102cb4 : decode_any W_102cb4 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cb8 : bv 32 := 0x02f00613.
Lemma F_102cb8 : fetch_word AsanUbsan.M.loaded_segments (0x102cb8 : word) = Some W_102cb8.
Proof. vm_refl. Qed.
Lemma D_102cb8 : decode_any W_102cb8 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cbc : bv 32 := 0x00c0006f.
Lemma F_102cbc : fetch_word AsanUbsan.M.loaded_segments (0x102cbc : word) = Some W_102cbc.
Proof. vm_refl. Qed.
Lemma D_102cbc : decode_any W_102cbc = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cc0 : bv 32 := 0x00b53023.
Lemma F_102cc0 : fetch_word AsanUbsan.M.loaded_segments (0x102cc0 : word) = Some W_102cc0.
Proof. vm_refl. Qed.
Lemma D_102cc0 : decode_any W_102cc0 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cc4 : bv 32 := 0x00158593.
Lemma F_102cc4 : fetch_word AsanUbsan.M.loaded_segments (0x102cc4 : word) = Some W_102cc4.
Proof. vm_refl. Qed.
Lemma D_102cc4 : decode_any W_102cc4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cc8 : bv 32 := 0xfff5c683.
Lemma F_102cc8 : fetch_word AsanUbsan.M.loaded_segments (0x102cc8 : word) = Some W_102cc8.
Proof. vm_refl. Qed.
Lemma D_102cc8 : decode_any W_102cc8 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102ccc : bv 32 := 0xfec68ae3.
Lemma F_102ccc : fetch_word AsanUbsan.M.loaded_segments (0x102ccc : word) = Some W_102ccc.
Proof. vm_refl. Qed.
Lemma D_102ccc : decode_any W_102ccc = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cd0 : bv 32 := 0xfe069ae3.
Lemma F_102cd0 : fetch_word AsanUbsan.M.loaded_segments (0x102cd0 : word) = Some W_102cd0.
Proof. vm_refl. Qed.
Lemma D_102cd0 : decode_any W_102cd0 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cd4 : bv 32 := 0x03010513.
Lemma F_102cd4 : fetch_word AsanUbsan.M.loaded_segments (0x102cd4 : word) = Some W_102cd4.
Proof. vm_refl. Qed.
Lemma D_102cd4 : decode_any W_102cd4 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cd8 : bv 32 := 0x2ec000ef.
Lemma F_102cd8 : fetch_word AsanUbsan.M.loaded_segments (0x102cd8 : word) = Some W_102cd8.
Proof. vm_refl. Qed.
Lemma D_102cd8 : decode_any W_102cd8 = Some (Jal 1 748, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cdc : bv 32 := 0x0f813503.
Lemma F_102cdc : fetch_word AsanUbsan.M.loaded_segments (0x102cdc : word) = Some W_102cdc.
Proof. vm_refl. Qed.
Lemma D_102cdc : decode_any W_102cdc = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102ce0 : bv 32 := 0x594000ef.
Lemma F_102ce0 : fetch_word AsanUbsan.M.loaded_segments (0x102ce0 : word) = Some W_102ce0.
Proof. vm_refl. Qed.
Lemma D_102ce0 : decode_any W_102ce0 = Some (Jal 1 1428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102ce4 : bv 32 := 0x08813503.
Lemma F_102ce4 : fetch_word AsanUbsan.M.loaded_segments (0x102ce4 : word) = Some W_102ce4.
Proof. vm_refl. Qed.
Lemma D_102ce4 : decode_any W_102ce4 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102ce8 : bv 32 := 0x09013583.
Lemma F_102ce8 : fetch_word AsanUbsan.M.loaded_segments (0x102ce8 : word) = Some W_102ce8.
Proof. vm_refl. Qed.
Lemma D_102ce8 : decode_any W_102ce8 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cec : bv 32 := 0x00b51c63.
Lemma F_102cec : fetch_word AsanUbsan.M.loaded_segments (0x102cec : word) = Some W_102cec.
Proof. vm_refl. Qed.
Lemma D_102cec : decode_any W_102cec = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cf0 : bv 32 := 0x09813503.
Lemma F_102cf0 : fetch_word AsanUbsan.M.loaded_segments (0x102cf0 : word) = Some W_102cf0.
Proof. vm_refl. Qed.
Lemma D_102cf0 : decode_any W_102cf0 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cf4 : bv 32 := 0x0a013583.
Lemma F_102cf4 : fetch_word AsanUbsan.M.loaded_segments (0x102cf4 : word) = Some W_102cf4.
Proof. vm_refl. Qed.
Lemma D_102cf4 : decode_any W_102cf4 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cf8 : bv 32 := 0x00b51663.
Lemma F_102cf8 : fetch_word AsanUbsan.M.loaded_segments (0x102cf8 : word) = Some W_102cf8.
Proof. vm_refl. Qed.
Lemma D_102cf8 : decode_any W_102cf8 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102cfc : bv 32 := 0x0e813503.
Lemma F_102cfc : fetch_word AsanUbsan.M.loaded_segments (0x102cfc : word) = Some W_102cfc.
Proof. vm_refl. Qed.
Lemma D_102cfc : decode_any W_102cfc = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d00 : bv 32 := 0x0e050063.
Lemma F_102d00 : fetch_word AsanUbsan.M.loaded_segments (0x102d00 : word) = Some W_102d00.
Proof. vm_refl. Qed.
Lemma D_102d00 : decode_any W_102d00 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d04 : bv 32 := 0x00200693.
Lemma F_102d04 : fetch_word AsanUbsan.M.loaded_segments (0x102d04 : word) = Some W_102d04.
Proof. vm_refl. Qed.
Lemma D_102d04 : decode_any W_102d04 = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d08 : bv 32 := 0x00100793.
Lemma F_102d08 : fetch_word AsanUbsan.M.loaded_segments (0x102d08 : word) = Some W_102d08.
Proof. vm_refl. Qed.
Lemma D_102d08 : decode_any W_102d08 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d0c : bv 32 := 0x00013423.
Lemma F_102d0c : fetch_word AsanUbsan.M.loaded_segments (0x102d0c : word) = Some W_102d0c.
Proof. vm_refl. Qed.
Lemma D_102d0c : decode_any W_102d0c = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d10 : bv 32 := 0x00013823.
Lemma F_102d10 : fetch_word AsanUbsan.M.loaded_segments (0x102d10 : word) = Some W_102d10.
Proof. vm_refl. Qed.
Lemma D_102d10 : decode_any W_102d10 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d14 : bv 32 := 0x04900893.
Lemma F_102d14 : fetch_word AsanUbsan.M.loaded_segments (0x102d14 : word) = Some W_102d14.
Proof. vm_refl. Qed.
Lemma D_102d14 : decode_any W_102d14 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d18 : bv 32 := 0x01810513.
Lemma F_102d18 : fetch_word AsanUbsan.M.loaded_segments (0x102d18 : word) = Some W_102d18.
Proof. vm_refl. Qed.
Lemma D_102d18 : decode_any W_102d18 = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d1c : bv 32 := 0x00300593.
Lemma F_102d1c : fetch_word AsanUbsan.M.loaded_segments (0x102d1c : word) = Some W_102d1c.
Proof. vm_refl. Qed.
Lemma D_102d1c : decode_any W_102d1c = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d20 : bv 32 := 0x00810613.
Lemma F_102d20 : fetch_word AsanUbsan.M.loaded_segments (0x102d20 : word) = Some W_102d20.
Proof. vm_refl. Qed.
Lemma D_102d20 : decode_any W_102d20 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d24 : bv 32 := 0x00800713.
Lemma F_102d24 : fetch_word AsanUbsan.M.loaded_segments (0x102d24 : word) = Some W_102d24.
Proof. vm_refl. Qed.
Lemma D_102d24 : decode_any W_102d24 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d28 : bv 32 := 0x00013c23.
Lemma F_102d28 : fetch_word AsanUbsan.M.loaded_segments (0x102d28 : word) = Some W_102d28.
Proof. vm_refl. Qed.
Lemma D_102d28 : decode_any W_102d28 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d2c : bv 32 := 0x02f13023.
Lemma F_102d2c : fetch_word AsanUbsan.M.loaded_segments (0x102d2c : word) = Some W_102d2c.
Proof. vm_refl. Qed.
Lemma D_102d2c : decode_any W_102d2c = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d30 : bv 32 := 0x02d13423.
Lemma F_102d30 : fetch_word AsanUbsan.M.loaded_segments (0x102d30 : word) = Some W_102d30.
Proof. vm_refl. Qed.
Lemma D_102d30 : decode_any W_102d30 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d34 : bv 32 := 0x00000693.
Lemma F_102d34 : fetch_word AsanUbsan.M.loaded_segments (0x102d34 : word) = Some W_102d34.
Proof. vm_refl. Qed.
Lemma D_102d34 : decode_any W_102d34 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d38 : bv 32 := 0x00000073.
Lemma F_102d38 : fetch_word AsanUbsan.M.loaded_segments (0x102d38 : word) = Some W_102d38.
Proof. vm_refl. Qed.
Lemma D_102d38 : decode_any W_102d38 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_102d38 : is_ecall W_102d38 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_102d3c : bv 32 := 0x02051513.
Lemma F_102d3c : fetch_word AsanUbsan.M.loaded_segments (0x102d3c : word) = Some W_102d3c.
Proof. vm_refl. Qed.
Lemma D_102d3c : decode_any W_102d3c = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d40 : bv 32 := 0x00055463.
Lemma F_102d40 : fetch_word AsanUbsan.M.loaded_segments (0x102d40 : word) = Some W_102d40.
Proof. vm_refl. Qed.
Lemma D_102d40 : decode_any W_102d40 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d44 : bv 32 := 0x00000023.
Lemma F_102d44 : fetch_word AsanUbsan.M.loaded_segments (0x102d44 : word) = Some W_102d44.
Proof. vm_refl. Qed.
Lemma D_102d44 : decode_any W_102d44 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d48 : bv 32 := 0x01e15503.
Lemma F_102d48 : fetch_word AsanUbsan.M.loaded_segments (0x102d48 : word) = Some W_102d48.
Proof. vm_refl. Qed.
Lemma D_102d48 : decode_any W_102d48 = Some (Load SZ2 false 10 2 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d4c : bv 32 := 0x02057513.
Lemma F_102d4c : fetch_word AsanUbsan.M.loaded_segments (0x102d4c : word) = Some W_102d4c.
Proof. vm_refl. Qed.
Lemma D_102d4c : decode_any W_102d4c = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d50 : bv 32 := 0x02050463.
Lemma F_102d50 : fetch_word AsanUbsan.M.loaded_segments (0x102d50 : word) = Some W_102d50.
Proof. vm_refl. Qed.
Lemma D_102d50 : decode_any W_102d50 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d54 : bv 32 := 0xfff21517.
Lemma F_102d54 : fetch_word AsanUbsan.M.loaded_segments (0x102d54 : word) = Some W_102d54.
Proof. vm_refl. Qed.
Lemma D_102d54 : decode_any W_102d54 = Some (Auipc 10 1048353, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d58 : bv 32 := 0x00008637.
Lemma F_102d58 : fetch_word AsanUbsan.M.loaded_segments (0x102d58 : word) = Some W_102d58.
Proof. vm_refl. Qed.
Lemma D_102d58 : decode_any W_102d58 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d5c : bv 32 := 0x03800893.
Lemma F_102d5c : fetch_word AsanUbsan.M.loaded_segments (0x102d5c : word) = Some W_102d5c.
Proof. vm_refl. Qed.
Lemma D_102d5c : decode_any W_102d5c = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d60 : bv 32 := 0x5bc50593.
Lemma F_102d60 : fetch_word AsanUbsan.M.loaded_segments (0x102d60 : word) = Some W_102d60.
Proof. vm_refl. Qed.
Lemma D_102d60 : decode_any W_102d60 = Some (OpImm ALU_ADD 11 10 1468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d64 : bv 32 := 0x0026061b.
Lemma F_102d64 : fetch_word AsanUbsan.M.loaded_segments (0x102d64 : word) = Some W_102d64.
Proof. vm_refl. Qed.
Lemma D_102d64 : decode_any W_102d64 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d68 : bv 32 := 0xf9c00513.
Lemma F_102d68 : fetch_word AsanUbsan.M.loaded_segments (0x102d68 : word) = Some W_102d68.
Proof. vm_refl. Qed.
Lemma D_102d68 : decode_any W_102d68 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d6c : bv 32 := 0x00000073.
Lemma F_102d6c : fetch_word AsanUbsan.M.loaded_segments (0x102d6c : word) = Some W_102d6c.
Proof. vm_refl. Qed.
Lemma D_102d6c : decode_any W_102d6c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_102d6c : is_ecall W_102d6c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_102d70 : bv 32 := 0x00055463.
Lemma F_102d70 : fetch_word AsanUbsan.M.loaded_segments (0x102d70 : word) = Some W_102d70.
Proof. vm_refl. Qed.
Lemma D_102d70 : decode_any W_102d70 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d74 : bv 32 := 0x00000023.
Lemma F_102d74 : fetch_word AsanUbsan.M.loaded_segments (0x102d74 : word) = Some W_102d74.
Proof. vm_refl. Qed.
Lemma D_102d74 : decode_any W_102d74 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d78 : bv 32 := 0x02615503.
Lemma F_102d78 : fetch_word AsanUbsan.M.loaded_segments (0x102d78 : word) = Some W_102d78.
Proof. vm_refl. Qed.
Lemma D_102d78 : decode_any W_102d78 = Some (Load SZ2 false 10 2 38, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d7c : bv 32 := 0x02057513.
Lemma F_102d7c : fetch_word AsanUbsan.M.loaded_segments (0x102d7c : word) = Some W_102d7c.
Proof. vm_refl. Qed.
Lemma D_102d7c : decode_any W_102d7c = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d80 : bv 32 := 0x02050463.
Lemma F_102d80 : fetch_word AsanUbsan.M.loaded_segments (0x102d80 : word) = Some W_102d80.
Proof. vm_refl. Qed.
Lemma D_102d80 : decode_any W_102d80 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d84 : bv 32 := 0xfff21517.
Lemma F_102d84 : fetch_word AsanUbsan.M.loaded_segments (0x102d84 : word) = Some W_102d84.
Proof. vm_refl. Qed.
Lemma D_102d84 : decode_any W_102d84 = Some (Auipc 10 1048353, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d88 : bv 32 := 0x00008637.
Lemma F_102d88 : fetch_word AsanUbsan.M.loaded_segments (0x102d88 : word) = Some W_102d88.
Proof. vm_refl. Qed.
Lemma D_102d88 : decode_any W_102d88 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d8c : bv 32 := 0x03800893.
Lemma F_102d8c : fetch_word AsanUbsan.M.loaded_segments (0x102d8c : word) = Some W_102d8c.
Proof. vm_refl. Qed.
Lemma D_102d8c : decode_any W_102d8c = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d90 : bv 32 := 0x58c50593.
Lemma F_102d90 : fetch_word AsanUbsan.M.loaded_segments (0x102d90 : word) = Some W_102d90.
Proof. vm_refl. Qed.
Lemma D_102d90 : decode_any W_102d90 = Some (OpImm ALU_ADD 11 10 1420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d94 : bv 32 := 0x0026061b.
Lemma F_102d94 : fetch_word AsanUbsan.M.loaded_segments (0x102d94 : word) = Some W_102d94.
Proof. vm_refl. Qed.
Lemma D_102d94 : decode_any W_102d94 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d98 : bv 32 := 0xf9c00513.
Lemma F_102d98 : fetch_word AsanUbsan.M.loaded_segments (0x102d98 : word) = Some W_102d98.
Proof. vm_refl. Qed.
Lemma D_102d98 : decode_any W_102d98 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102d9c : bv 32 := 0x00000073.
Lemma F_102d9c : fetch_word AsanUbsan.M.loaded_segments (0x102d9c : word) = Some W_102d9c.
Proof. vm_refl. Qed.
Lemma D_102d9c : decode_any W_102d9c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_102d9c : is_ecall W_102d9c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_102da0 : bv 32 := 0x00055463.
Lemma F_102da0 : fetch_word AsanUbsan.M.loaded_segments (0x102da0 : word) = Some W_102da0.
Proof. vm_refl. Qed.
Lemma D_102da0 : decode_any W_102da0 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102da4 : bv 32 := 0x00000023.
Lemma F_102da4 : fetch_word AsanUbsan.M.loaded_segments (0x102da4 : word) = Some W_102da4.
Proof. vm_refl. Qed.
Lemma D_102da4 : decode_any W_102da4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102da8 : bv 32 := 0x02e15503.
Lemma F_102da8 : fetch_word AsanUbsan.M.loaded_segments (0x102da8 : word) = Some W_102da8.
Proof. vm_refl. Qed.
Lemma D_102da8 : decode_any W_102da8 = Some (Load SZ2 false 10 2 46, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102dac : bv 32 := 0x02057513.
Lemma F_102dac : fetch_word AsanUbsan.M.loaded_segments (0x102dac : word) = Some W_102dac.
Proof. vm_refl. Qed.
Lemma D_102dac : decode_any W_102dac = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102db0 : bv 32 := 0x02050463.
Lemma F_102db0 : fetch_word AsanUbsan.M.loaded_segments (0x102db0 : word) = Some W_102db0.
Proof. vm_refl. Qed.
Lemma D_102db0 : decode_any W_102db0 = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102db4 : bv 32 := 0xfff21517.
Lemma F_102db4 : fetch_word AsanUbsan.M.loaded_segments (0x102db4 : word) = Some W_102db4.
Proof. vm_refl. Qed.
Lemma D_102db4 : decode_any W_102db4 = Some (Auipc 10 1048353, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102db8 : bv 32 := 0x00008637.
Lemma F_102db8 : fetch_word AsanUbsan.M.loaded_segments (0x102db8 : word) = Some W_102db8.
Proof. vm_refl. Qed.
Lemma D_102db8 : decode_any W_102db8 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102dbc : bv 32 := 0x03800893.
Lemma F_102dbc : fetch_word AsanUbsan.M.loaded_segments (0x102dbc : word) = Some W_102dbc.
Proof. vm_refl. Qed.
Lemma D_102dbc : decode_any W_102dbc = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102dc0 : bv 32 := 0x55c50593.
Lemma F_102dc0 : fetch_word AsanUbsan.M.loaded_segments (0x102dc0 : word) = Some W_102dc0.
Proof. vm_refl. Qed.
Lemma D_102dc0 : decode_any W_102dc0 = Some (OpImm ALU_ADD 11 10 1372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102dc4 : bv 32 := 0x0026061b.
Lemma F_102dc4 : fetch_word AsanUbsan.M.loaded_segments (0x102dc4 : word) = Some W_102dc4.
Proof. vm_refl. Qed.
Lemma D_102dc4 : decode_any W_102dc4 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102dc8 : bv 32 := 0xf9c00513.
Lemma F_102dc8 : fetch_word AsanUbsan.M.loaded_segments (0x102dc8 : word) = Some W_102dc8.
Proof. vm_refl. Qed.
Lemma D_102dc8 : decode_any W_102dc8 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102dcc : bv 32 := 0x00000073.
Lemma F_102dcc : fetch_word AsanUbsan.M.loaded_segments (0x102dcc : word) = Some W_102dcc.
Proof. vm_refl. Qed.
Lemma D_102dcc : decode_any W_102dcc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_102dcc : is_ecall W_102dcc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_102dd0 : bv 32 := 0x00055463.
Lemma F_102dd0 : fetch_word AsanUbsan.M.loaded_segments (0x102dd0 : word) = Some W_102dd0.
Proof. vm_refl. Qed.
Lemma D_102dd0 : decode_any W_102dd0 = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102dd4 : bv 32 := 0x00000023.
Lemma F_102dd4 : fetch_word AsanUbsan.M.loaded_segments (0x102dd4 : word) = Some W_102dd4.
Proof. vm_refl. Qed.
Lemma D_102dd4 : decode_any W_102dd4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102dd8 : bv 32 := 0x00100513.
Lemma F_102dd8 : fetch_word AsanUbsan.M.loaded_segments (0x102dd8 : word) = Some W_102dd8.
Proof. vm_refl. Qed.
Lemma D_102dd8 : decode_any W_102dd8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102ddc : bv 32 := 0x00a90123.
Lemma F_102ddc : fetch_word AsanUbsan.M.loaded_segments (0x102ddc : word) = Some W_102ddc.
Proof. vm_refl. Qed.
Lemma D_102ddc : decode_any W_102ddc = Some (Store SZ1 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102de0 : bv 32 := 0x17813083.
Lemma F_102de0 : fetch_word AsanUbsan.M.loaded_segments (0x102de0 : word) = Some W_102de0.
Proof. vm_refl. Qed.
Lemma D_102de0 : decode_any W_102de0 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102de4 : bv 32 := 0x17013403.
Lemma F_102de4 : fetch_word AsanUbsan.M.loaded_segments (0x102de4 : word) = Some W_102de4.
Proof. vm_refl. Qed.
Lemma D_102de4 : decode_any W_102de4 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102de8 : bv 32 := 0x16813483.
Lemma F_102de8 : fetch_word AsanUbsan.M.loaded_segments (0x102de8 : word) = Some W_102de8.
Proof. vm_refl. Qed.
Lemma D_102de8 : decode_any W_102de8 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102dec : bv 32 := 0x16013903.
Lemma F_102dec : fetch_word AsanUbsan.M.loaded_segments (0x102dec : word) = Some W_102dec.
Proof. vm_refl. Qed.
Lemma D_102dec : decode_any W_102dec = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102df0 : bv 32 := 0x18010113.
Lemma F_102df0 : fetch_word AsanUbsan.M.loaded_segments (0x102df0 : word) = Some W_102df0.
Proof. vm_refl. Qed.
Lemma D_102df0 : decode_any W_102df0 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_102df4 : bv 32 := 0x00008067.
Lemma F_102df4 : fetch_word AsanUbsan.M.loaded_segments (0x102df4 : word) = Some W_102df4.
Proof. vm_refl. Qed.
Lemma D_102df4 : decode_any W_102df4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
