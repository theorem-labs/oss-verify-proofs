(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_34964 : bv 32 := 0xff010113.
Lemma F_34964 : fetch_word Ubsan.M.loaded_segments (0x349bc : word) = Some W_34964.
Proof. vm_refl. Qed.
Lemma D_34964 : decode_any W_34964 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_34968 : bv 32 := 0x00113423.
Lemma F_34968 : fetch_word Ubsan.M.loaded_segments (0x349c0 : word) = Some W_34968.
Proof. vm_refl. Qed.
Lemma D_34968 : decode_any W_34968 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_3496c : bv 32 := 0x00813023.
Lemma F_3496c : fetch_word Ubsan.M.loaded_segments (0x349c4 : word) = Some W_3496c.
Proof. vm_refl. Qed.
Lemma D_3496c : decode_any W_3496c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34970 : bv 32 := 0x01010413.
Lemma F_34970 : fetch_word Ubsan.M.loaded_segments (0x349c8 : word) = Some W_34970.
Proof. vm_refl. Qed.
Lemma D_34970 : decode_any W_34970 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_34974 : bv 32 := 0x00086517.
Lemma F_34974 : fetch_word Ubsan.M.loaded_segments (0x349cc : word) = Some W_34974.
Proof. vm_refl. Qed.
Lemma D_34974 : decode_any W_34974 = Some (Auipc 10 134, 4%Z).
Proof. vm_refl. Qed.

Definition W_34978 : bv 32 := 0x7bc50513.
Lemma F_34978 : fetch_word Ubsan.M.loaded_segments (0x349d0 : word) = Some W_34978.
Proof. vm_refl. Qed.
Lemma D_34978 : decode_any W_34978 = Some (OpImm ALU_ADD 10 10 1980, 4%Z).
Proof. vm_refl. Qed.

Definition W_3497c : bv 32 := 0x00054503.
Lemma F_3497c : fetch_word Ubsan.M.loaded_segments (0x349d4 : word) = Some W_3497c.
Proof. vm_refl. Qed.
Lemma D_3497c : decode_any W_3497c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_34980 : bv 32 := 0x00157513.
Lemma F_34980 : fetch_word Ubsan.M.loaded_segments (0x349d8 : word) = Some W_34980.
Proof. vm_refl. Qed.
Lemma D_34980 : decode_any W_34980 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_34984 : bv 32 := 0x00050663.
Lemma F_34984 : fetch_word Ubsan.M.loaded_segments (0x349dc : word) = Some W_34984.
Proof. vm_refl. Qed.
Lemma D_34984 : decode_any W_34984 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_34988 : bv 32 := 0x0040006f.
Lemma F_34988 : fetch_word Ubsan.M.loaded_segments (0x349e0 : word) = Some W_34988.
Proof. vm_refl. Qed.
Lemma D_34988 : decode_any W_34988 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_3498c : bv 32 := 0x0580006f.
Lemma F_3498c : fetch_word Ubsan.M.loaded_segments (0x349e4 : word) = Some W_3498c.
Proof. vm_refl. Qed.
Lemma D_3498c : decode_any W_3498c = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_34990 : bv 32 := 0x00086517.
Lemma F_34990 : fetch_word Ubsan.M.loaded_segments (0x349e8 : word) = Some W_34990.
Proof. vm_refl. Qed.
Lemma D_34990 : decode_any W_34990 = Some (Auipc 10 134, 4%Z).
Proof. vm_refl. Qed.

Definition W_34994 : bv 32 := 0x7a050593.
Lemma F_34994 : fetch_word Ubsan.M.loaded_segments (0x349ec : word) = Some W_34994.
Proof. vm_refl. Qed.
Lemma D_34994 : decode_any W_34994 = Some (OpImm ALU_ADD 11 10 1952, 4%Z).
Proof. vm_refl. Qed.

Definition W_34998 : bv 32 := 0x00100513.
Lemma F_34998 : fetch_word Ubsan.M.loaded_segments (0x349f0 : word) = Some W_34998.
Proof. vm_refl. Qed.
Lemma D_34998 : decode_any W_34998 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3499c : bv 32 := 0x00a58023.
Lemma F_3499c : fetch_word Ubsan.M.loaded_segments (0x349f4 : word) = Some W_3499c.
Proof. vm_refl. Qed.
Lemma D_3499c : decode_any W_3499c = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_349a0 : bv 32 := 0x00085517.
Lemma F_349a0 : fetch_word Ubsan.M.loaded_segments (0x349f8 : word) = Some W_349a0.
Proof. vm_refl. Qed.
Lemma D_349a0 : decode_any W_349a0 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_349a4 : bv 32 := 0x2c053503.
Lemma F_349a4 : fetch_word Ubsan.M.loaded_segments (0x349fc : word) = Some W_349a4.
Proof. vm_refl. Qed.
Lemma D_349a4 : decode_any W_349a4 = Some (Load SZ8 true 10 10 704, 4%Z).
Proof. vm_refl. Qed.

Definition W_349a8 : bv 32 := 0x00050e63.
Lemma F_349a8 : fetch_word Ubsan.M.loaded_segments (0x34a00 : word) = Some W_349a8.
Proof. vm_refl. Qed.
Lemma D_349a8 : decode_any W_349a8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_349ac : bv 32 := 0x0040006f.
Lemma F_349ac : fetch_word Ubsan.M.loaded_segments (0x34a04 : word) = Some W_349ac.
Proof. vm_refl. Qed.
Lemma D_349ac : decode_any W_349ac = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_349b0 : bv 32 := 0x00086517.
Lemma F_349b0 : fetch_word Ubsan.M.loaded_segments (0x34a08 : word) = Some W_349b0.
Proof. vm_refl. Qed.
Lemma D_349b0 : decode_any W_349b0 = Some (Auipc 10 134, 4%Z).
Proof. vm_refl. Qed.

Definition W_349b4 : bv 32 := 0x44850513.
Lemma F_349b4 : fetch_word Ubsan.M.loaded_segments (0x34a0c : word) = Some W_349b4.
Proof. vm_refl. Qed.
Lemma D_349b4 : decode_any W_349b4 = Some (OpImm ALU_ADD 10 10 1096, 4%Z).
Proof. vm_refl. Qed.

Definition W_349b8 : bv 32 := 0x00053503.
Lemma F_349b8 : fetch_word Ubsan.M.loaded_segments (0x34a10 : word) = Some W_349b8.
Proof. vm_refl. Qed.
Lemma D_349b8 : decode_any W_349b8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_349bc : bv 32 := 0x57d680ef.
Lemma F_349bc : fetch_word Ubsan.M.loaded_segments (0x34a14 : word) = Some W_349bc.
Proof. vm_refl. Qed.
Lemma D_349bc : decode_any W_349bc = Some (Jal 1 429436, 4%Z).
Proof. vm_refl. Qed.

Definition W_349c0 : bv 32 := 0x0040006f.
Lemma F_349c0 : fetch_word Ubsan.M.loaded_segments (0x34a18 : word) = Some W_349c0.
Proof. vm_refl. Qed.
Lemma D_349c0 : decode_any W_349c0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_349c4 : bv 32 := 0x00085517.
Lemma F_349c4 : fetch_word Ubsan.M.loaded_segments (0x34a1c : word) = Some W_349c4.
Proof. vm_refl. Qed.
Lemma D_349c4 : decode_any W_349c4 = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

Definition W_349c8 : bv 32 := 0x2a453503.
Lemma F_349c8 : fetch_word Ubsan.M.loaded_segments (0x34a20 : word) = Some W_349c8.
Proof. vm_refl. Qed.
Lemma D_349c8 : decode_any W_349c8 = Some (Load SZ8 true 10 10 676, 4%Z).
Proof. vm_refl. Qed.

Definition W_349cc : bv 32 := 0x00050c63.
Lemma F_349cc : fetch_word Ubsan.M.loaded_segments (0x34a24 : word) = Some W_349cc.
Proof. vm_refl. Qed.
Lemma D_349cc : decode_any W_349cc = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_349d0 : bv 32 := 0x0040006f.
Lemma F_349d0 : fetch_word Ubsan.M.loaded_segments (0x34a28 : word) = Some W_349d0.
Proof. vm_refl. Qed.
Lemma D_349d0 : decode_any W_349d0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_349d4 : bv 32 := 0xffff1517.
Lemma F_349d4 : fetch_word Ubsan.M.loaded_segments (0x34a2c : word) = Some W_349d4.
Proof. vm_refl. Qed.
Lemma D_349d4 : decode_any W_349d4 = Some (Auipc 10 1048561, 4%Z).
Proof. vm_refl. Qed.

Definition W_349d8 : bv 32 := 0xf3c50513.
Lemma F_349d8 : fetch_word Ubsan.M.loaded_segments (0x34a30 : word) = Some W_349d8.
Proof. vm_refl. Qed.
Lemma D_349d8 : decode_any W_349d8 = Some (OpImm ALU_ADD 10 10 3900, 4%Z).
Proof. vm_refl. Qed.

Definition W_349dc : bv 32 := 0x000000ef.
Lemma F_349dc : fetch_word Ubsan.M.loaded_segments (0x34a34 : word) = Some W_349dc.
Proof. vm_refl. Qed.
Lemma D_349dc : decode_any W_349dc = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_349e0 : bv 32 := 0x0040006f.
Lemma F_349e0 : fetch_word Ubsan.M.loaded_segments (0x34a38 : word) = Some W_349e0.
Proof. vm_refl. Qed.
Lemma D_349e0 : decode_any W_349e0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_349e4 : bv 32 := 0x00813083.
Lemma F_349e4 : fetch_word Ubsan.M.loaded_segments (0x34a3c : word) = Some W_349e4.
Proof. vm_refl. Qed.
Lemma D_349e4 : decode_any W_349e4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_349e8 : bv 32 := 0x00013403.
Lemma F_349e8 : fetch_word Ubsan.M.loaded_segments (0x34a40 : word) = Some W_349e8.
Proof. vm_refl. Qed.
Lemma D_349e8 : decode_any W_349e8 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_349ec : bv 32 := 0x01010113.
Lemma F_349ec : fetch_word Ubsan.M.loaded_segments (0x34a44 : word) = Some W_349ec.
Proof. vm_refl. Qed.
Lemma D_349ec : decode_any W_349ec = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_349f0 : bv 32 := 0x00008067.
Lemma F_349f0 : fetch_word Ubsan.M.loaded_segments (0x34a48 : word) = Some W_349f0.
Proof. vm_refl. Qed.
Lemma D_349f0 : decode_any W_349f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
