(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_63db4 : bv 32 := 0xfe010113.
Lemma F_63db4 : fetch_word Ubsan.M.loaded_segments (0x63db4 : word) = Some W_63db4.
Proof. vm_refl. Qed.
Lemma D_63db4 : decode_any W_63db4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_63db8 : bv 32 := 0x00113c23.
Lemma F_63db8 : fetch_word Ubsan.M.loaded_segments (0x63db8 : word) = Some W_63db8.
Proof. vm_refl. Qed.
Lemma D_63db8 : decode_any W_63db8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dbc : bv 32 := 0x00813823.
Lemma F_63dbc : fetch_word Ubsan.M.loaded_segments (0x63dbc : word) = Some W_63dbc.
Proof. vm_refl. Qed.
Lemma D_63dbc : decode_any W_63dbc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dc0 : bv 32 := 0x00913423.
Lemma F_63dc0 : fetch_word Ubsan.M.loaded_segments (0x63dc0 : word) = Some W_63dc0.
Proof. vm_refl. Qed.
Lemma D_63dc0 : decode_any W_63dc0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dc4 : bv 32 := 0x02050a63.
Lemma F_63dc4 : fetch_word Ubsan.M.loaded_segments (0x63dc4 : word) = Some W_63dc4.
Proof. vm_refl. Qed.
Lemma D_63dc4 : decode_any W_63dc4 = Some (Branch BC_EQ 10 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dc8 : bv 32 := 0x00050413.
Lemma F_63dc8 : fetch_word Ubsan.M.loaded_segments (0x63dc8 : word) = Some W_63dc8.
Proof. vm_refl. Qed.
Lemma D_63dc8 : decode_any W_63dc8 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dcc : bv 32 := 0x00757513.
Lemma F_63dcc : fetch_word Ubsan.M.loaded_segments (0x63dcc : word) = Some W_63dcc.
Proof. vm_refl. Qed.
Lemma D_63dcc : decode_any W_63dcc = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dd0 : bv 32 := 0x08051663.
Lemma F_63dd0 : fetch_word Ubsan.M.loaded_segments (0x63dd0 : word) = Some W_63dd0.
Proof. vm_refl. Qed.
Lemma D_63dd0 : decode_any W_63dd0 = Some (Branch BC_NE 10 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dd4 : bv 32 := 0x00058493.
Lemma F_63dd4 : fetch_word Ubsan.M.loaded_segments (0x63dd4 : word) = Some W_63dd4.
Proof. vm_refl. Qed.
Lemma D_63dd4 : decode_any W_63dd4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dd8 : bv 32 := 0x00043503.
Lemma F_63dd8 : fetch_word Ubsan.M.loaded_segments (0x63dd8 : word) = Some W_63dd8.
Proof. vm_refl. Qed.
Lemma D_63dd8 : decode_any W_63dd8 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63ddc : bv 32 := 0x00050463.
Lemma F_63ddc : fetch_word Ubsan.M.loaded_segments (0x63ddc : word) = Some W_63ddc.
Proof. vm_refl. Qed.
Lemma D_63ddc : decode_any W_63ddc = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_63de0 : bv 32 := 0x239aa0ef.
Lemma F_63de0 : fetch_word Ubsan.M.loaded_segments (0x63de0 : word) = Some W_63de0.
Proof. vm_refl. Qed.
Lemma D_63de0 : decode_any W_63de0 = Some (Jal 1 698936, 4%Z).
Proof. vm_refl. Qed.

Definition W_63de4 : bv 32 := 0x04048863.
Lemma F_63de4 : fetch_word Ubsan.M.loaded_segments (0x63de4 : word) = Some W_63de4.
Proof. vm_refl. Qed.
Lemma D_63de4 : decode_any W_63de4 = Some (Branch BC_EQ 9 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_63de8 : bv 32 := 0x00048513.
Lemma F_63de8 : fetch_word Ubsan.M.loaded_segments (0x63de8 : word) = Some W_63de8.
Proof. vm_refl. Qed.
Lemma D_63de8 : decode_any W_63de8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dec : bv 32 := 0xe8dff0ef.
Lemma F_63dec : fetch_word Ubsan.M.loaded_segments (0x63dec : word) = Some W_63dec.
Proof. vm_refl. Qed.
Lemma D_63dec : decode_any W_63dec = Some (Jal 1 2096780, 4%Z).
Proof. vm_refl. Qed.

Definition W_63df0 : bv 32 := 0x00050593.
Lemma F_63df0 : fetch_word Ubsan.M.loaded_segments (0x63df0 : word) = Some W_63df0.
Proof. vm_refl. Qed.
Lemma D_63df0 : decode_any W_63df0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63df4 : bv 32 := 0x0440006f.
Lemma F_63df4 : fetch_word Ubsan.M.loaded_segments (0x63df4 : word) = Some W_63df4.
Proof. vm_refl. Qed.
Lemma D_63df4 : decode_any W_63df4 = Some (Jal 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_63df8 : bv 32 := 0x000c3517.
Lemma F_63df8 : fetch_word Ubsan.M.loaded_segments (0x63df8 : word) = Some W_63df8.
Proof. vm_refl. Qed.
Lemma D_63df8 : decode_any W_63df8 = Some (Auipc 10 195, 4%Z).
Proof. vm_refl. Qed.

Definition W_63dfc : bv 32 := 0xc7853503.
Lemma F_63dfc : fetch_word Ubsan.M.loaded_segments (0x63dfc : word) = Some W_63dfc.
Proof. vm_refl. Qed.
Lemma D_63dfc : decode_any W_63dfc = Some (Load SZ8 true 10 10 3192, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e00 : bv 32 := 0x00052503.
Lemma F_63e00 : fetch_word Ubsan.M.loaded_segments (0x63e00 : word) = Some W_63e00.
Proof. vm_refl. Qed.
Lemma D_63e00 : decode_any W_63e00 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e04 : bv 32 := 0x00500593.
Lemma F_63e04 : fetch_word Ubsan.M.loaded_segments (0x63e04 : word) = Some W_63e04.
Proof. vm_refl. Qed.
Lemma D_63e04 : decode_any W_63e04 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e08 : bv 32 := 0x02a5ce63.
Lemma F_63e08 : fetch_word Ubsan.M.loaded_segments (0x63e08 : word) = Some W_63e08.
Proof. vm_refl. Qed.
Lemma D_63e08 : decode_any W_63e08 = Some (Branch BC_LT 11 10 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e0c : bv 32 := 0xfffb5517.
Lemma F_63e0c : fetch_word Ubsan.M.loaded_segments (0x63e0c : word) = Some W_63e0c.
Proof. vm_refl. Qed.
Lemma D_63e0c : decode_any W_63e0c = Some (Auipc 10 1048501, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e10 : bv 32 := 0xfffb0597.
Lemma F_63e10 : fetch_word Ubsan.M.loaded_segments (0x63e10 : word) = Some W_63e10.
Proof. vm_refl. Qed.
Lemma D_63e10 : decode_any W_63e10 = Some (Auipc 11 1048496, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e14 : bv 32 := 0xc8150513.
Lemma F_63e14 : fetch_word Ubsan.M.loaded_segments (0x63e14 : word) = Some W_63e14.
Proof. vm_refl. Qed.
Lemma D_63e14 : decode_any W_63e14 = Some (OpImm ALU_ADD 10 10 3201, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e18 : bv 32 := 0x5aa58593.
Lemma F_63e18 : fetch_word Ubsan.M.loaded_segments (0x63e18 : word) = Some W_63e18.
Proof. vm_refl. Qed.
Lemma D_63e18 : decode_any W_63e18 = Some (OpImm ALU_ADD 11 11 1450, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e1c : bv 32 := 0x00100613.
Lemma F_63e1c : fetch_word Ubsan.M.loaded_segments (0x63e1c : word) = Some W_63e1c.
Proof. vm_refl. Qed.
Lemma D_63e1c : decode_any W_63e1c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e20 : bv 32 := 0x01813083.
Lemma F_63e20 : fetch_word Ubsan.M.loaded_segments (0x63e20 : word) = Some W_63e20.
Proof. vm_refl. Qed.
Lemma D_63e20 : decode_any W_63e20 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e24 : bv 32 := 0x01013403.
Lemma F_63e24 : fetch_word Ubsan.M.loaded_segments (0x63e24 : word) = Some W_63e24.
Proof. vm_refl. Qed.
Lemma D_63e24 : decode_any W_63e24 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e28 : bv 32 := 0x00813483.
Lemma F_63e28 : fetch_word Ubsan.M.loaded_segments (0x63e28 : word) = Some W_63e28.
Proof. vm_refl. Qed.
Lemma D_63e28 : decode_any W_63e28 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e2c : bv 32 := 0x02010113.
Lemma F_63e2c : fetch_word Ubsan.M.loaded_segments (0x63e2c : word) = Some W_63e2c.
Proof. vm_refl. Qed.
Lemma D_63e2c : decode_any W_63e2c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e30 : bv 32 := 0x841ff06f.
Lemma F_63e30 : fetch_word Ubsan.M.loaded_segments (0x63e30 : word) = Some W_63e30.
Proof. vm_refl. Qed.
Lemma D_63e30 : decode_any W_63e30 = Some (Jal 0 2095168, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e34 : bv 32 := 0x00000593.
Lemma F_63e34 : fetch_word Ubsan.M.loaded_segments (0x63e34 : word) = Some W_63e34.
Proof. vm_refl. Qed.
Lemma D_63e34 : decode_any W_63e34 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e38 : bv 32 := 0x00000513.
Lemma F_63e38 : fetch_word Ubsan.M.loaded_segments (0x63e38 : word) = Some W_63e38.
Proof. vm_refl. Qed.
Lemma D_63e38 : decode_any W_63e38 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e3c : bv 32 := 0x00b43023.
Lemma F_63e3c : fetch_word Ubsan.M.loaded_segments (0x63e3c : word) = Some W_63e3c.
Proof. vm_refl. Qed.
Lemma D_63e3c : decode_any W_63e3c = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e40 : bv 32 := 0x0080006f.
Lemma F_63e40 : fetch_word Ubsan.M.loaded_segments (0x63e40 : word) = Some W_63e40.
Proof. vm_refl. Qed.
Lemma D_63e40 : decode_any W_63e40 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e44 : bv 32 := 0x00100513.
Lemma F_63e44 : fetch_word Ubsan.M.loaded_segments (0x63e44 : word) = Some W_63e44.
Proof. vm_refl. Qed.
Lemma D_63e44 : decode_any W_63e44 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e48 : bv 32 := 0x01813083.
Lemma F_63e48 : fetch_word Ubsan.M.loaded_segments (0x63e48 : word) = Some W_63e48.
Proof. vm_refl. Qed.
Lemma D_63e48 : decode_any W_63e48 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e4c : bv 32 := 0x01013403.
Lemma F_63e4c : fetch_word Ubsan.M.loaded_segments (0x63e4c : word) = Some W_63e4c.
Proof. vm_refl. Qed.
Lemma D_63e4c : decode_any W_63e4c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e50 : bv 32 := 0x00813483.
Lemma F_63e50 : fetch_word Ubsan.M.loaded_segments (0x63e50 : word) = Some W_63e50.
Proof. vm_refl. Qed.
Lemma D_63e50 : decode_any W_63e50 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e54 : bv 32 := 0x02010113.
Lemma F_63e54 : fetch_word Ubsan.M.loaded_segments (0x63e54 : word) = Some W_63e54.
Proof. vm_refl. Qed.
Lemma D_63e54 : decode_any W_63e54 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e58 : bv 32 := 0x00008067.
Lemma F_63e58 : fetch_word Ubsan.M.loaded_segments (0x63e58 : word) = Some W_63e58.
Proof. vm_refl. Qed.
Lemma D_63e58 : decode_any W_63e58 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_63e5c : bv 32 := 0xc0001073.
Lemma F_63e5c : fetch_word Ubsan.M.loaded_segments (0x63e5c : word) = Some W_63e5c.
Proof. vm_refl. Qed.
Lemma D_63e5c : decode_any W_63e5c = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
