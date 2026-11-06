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
Definition W_89640 : bv 32 := 0xff010113.
Lemma F_89640 : fetch_word Asan.M.loaded_segments (0x89690 : word) = Some W_89640.
Proof. vm_refl. Qed.
Lemma D_89640 : decode_any W_89640 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89644 : bv 32 := 0x00113423.
Lemma F_89644 : fetch_word Asan.M.loaded_segments (0x89694 : word) = Some W_89644.
Proof. vm_refl. Qed.
Lemma D_89644 : decode_any W_89644 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89648 : bv 32 := 0x00813023.
Lemma F_89648 : fetch_word Asan.M.loaded_segments (0x89698 : word) = Some W_89648.
Proof. vm_refl. Qed.
Lemma D_89648 : decode_any W_89648 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8964c : bv 32 := 0x000e1517.
Lemma F_8964c : fetch_word Asan.M.loaded_segments (0x8969c : word) = Some W_8964c.
Proof. vm_refl. Qed.
Lemma D_8964c : decode_any W_8964c = Some (Auipc 10 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89650 : bv 32 := 0x53c50413.
Lemma F_89650 : fetch_word Asan.M.loaded_segments (0x896a0 : word) = Some W_89650.
Proof. vm_refl. Qed.
Lemma D_89650 : decode_any W_89650 = Some (OpImm ALU_ADD 8 10 1340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89654 : bv 32 := 0x00040583.
Lemma F_89654 : fetch_word Asan.M.loaded_segments (0x896a4 : word) = Some W_89654.
Proof. vm_refl. Qed.
Lemma D_89654 : decode_any W_89654 = Some (Load SZ1 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89658 : bv 32 := 0x00100513.
Lemma F_89658 : fetch_word Asan.M.loaded_segments (0x896a8 : word) = Some W_89658.
Proof. vm_refl. Qed.
Lemma D_89658 : decode_any W_89658 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8965c : bv 32 := 0x0230000f.
Lemma F_8965c : fetch_word Asan.M.loaded_segments (0x896ac : word) = Some W_8965c.
Proof. vm_refl. Qed.
Lemma D_8965c : decode_any W_8965c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89660 : bv 32 := 0x00a59a63.
Lemma F_89660 : fetch_word Asan.M.loaded_segments (0x896b0 : word) = Some W_89660.
Proof. vm_refl. Qed.
Lemma D_89660 : decode_any W_89660 = Some (Branch BC_NE 11 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89664 : bv 32 := 0x00813083.
Lemma F_89664 : fetch_word Asan.M.loaded_segments (0x896b4 : word) = Some W_89664.
Proof. vm_refl. Qed.
Lemma D_89664 : decode_any W_89664 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89668 : bv 32 := 0x00013403.
Lemma F_89668 : fetch_word Asan.M.loaded_segments (0x896b8 : word) = Some W_89668.
Proof. vm_refl. Qed.
Lemma D_89668 : decode_any W_89668 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8966c : bv 32 := 0x01010113.
Lemma F_8966c : fetch_word Asan.M.loaded_segments (0x896bc : word) = Some W_8966c.
Proof. vm_refl. Qed.
Lemma D_8966c : decode_any W_8966c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89670 : bv 32 := 0x00008067.
Lemma F_89670 : fetch_word Asan.M.loaded_segments (0x896c0 : word) = Some W_89670.
Proof. vm_refl. Qed.
Lemma D_89670 : decode_any W_89670 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89744 : bv 32 := 0xfb010113.
Lemma F_89744 : fetch_word Asan.M.loaded_segments (0x89794 : word) = Some W_89744.
Proof. vm_refl. Qed.
Lemma D_89744 : decode_any W_89744 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89748 : bv 32 := 0x04113423.
Lemma F_89748 : fetch_word Asan.M.loaded_segments (0x89798 : word) = Some W_89748.
Proof. vm_refl. Qed.
Lemma D_89748 : decode_any W_89748 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8974c : bv 32 := 0x04813023.
Lemma F_8974c : fetch_word Asan.M.loaded_segments (0x8979c : word) = Some W_8974c.
Proof. vm_refl. Qed.
Lemma D_8974c : decode_any W_8974c = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89750 : bv 32 := 0x02913c23.
Lemma F_89750 : fetch_word Asan.M.loaded_segments (0x897a0 : word) = Some W_89750.
Proof. vm_refl. Qed.
Lemma D_89750 : decode_any W_89750 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89754 : bv 32 := 0x03213823.
Lemma F_89754 : fetch_word Asan.M.loaded_segments (0x897a4 : word) = Some W_89754.
Proof. vm_refl. Qed.
Lemma D_89754 : decode_any W_89754 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89758 : bv 32 := 0x03313423.
Lemma F_89758 : fetch_word Asan.M.loaded_segments (0x897a8 : word) = Some W_89758.
Proof. vm_refl. Qed.
Lemma D_89758 : decode_any W_89758 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8975c : bv 32 := 0x000e1517.
Lemma F_8975c : fetch_word Asan.M.loaded_segments (0x897ac : word) = Some W_8975c.
Proof. vm_refl. Qed.
Lemma D_8975c : decode_any W_8975c = Some (Auipc 10 225, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89760 : bv 32 := 0x42c50493.
Lemma F_89760 : fetch_word Asan.M.loaded_segments (0x897b0 : word) = Some W_89760.
Proof. vm_refl. Qed.
Lemma D_89760 : decode_any W_89760 = Some (OpImm ALU_ADD 9 10 1068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89764 : bv 32 := 0x00048503.
Lemma F_89764 : fetch_word Asan.M.loaded_segments (0x897b4 : word) = Some W_89764.
Proof. vm_refl. Qed.
Lemma D_89764 : decode_any W_89764 = Some (Load SZ1 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89768 : bv 32 := 0x00100593.
Lemma F_89768 : fetch_word Asan.M.loaded_segments (0x897b8 : word) = Some W_89768.
Proof. vm_refl. Qed.
Lemma D_89768 : decode_any W_89768 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8976c : bv 32 := 0x0230000f.
Lemma F_8976c : fetch_word Asan.M.loaded_segments (0x897bc : word) = Some W_8976c.
Proof. vm_refl. Qed.
Lemma D_8976c : decode_any W_8976c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89770 : bv 32 := 0x10b51e63.
Lemma F_89770 : fetch_word Asan.M.loaded_segments (0x897c0 : word) = Some W_89770.
Proof. vm_refl. Qed.
Lemma D_89770 : decode_any W_89770 = Some (Branch BC_NE 10 11 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89774 : bv 32 := 0xbe1fa0ef.
Lemma F_89774 : fetch_word Asan.M.loaded_segments (0x897c4 : word) = Some W_89774.
Proof. vm_refl. Qed.
Lemma D_89774 : decode_any W_89774 = Some (Jal 1 2075616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89778 : bv 32 := 0x0e051663.
Lemma F_89778 : fetch_word Asan.M.loaded_segments (0x897c8 : word) = Some W_89778.
Proof. vm_refl. Qed.
Lemma D_89778 : decode_any W_89778 = Some (Branch BC_NE 10 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8977c : bv 32 := 0xfff87517.
Lemma F_8977c : fetch_word Asan.M.loaded_segments (0x897cc : word) = Some W_8977c.
Proof. vm_refl. Qed.
Lemma D_8977c : decode_any W_8977c = Some (Auipc 10 1048455, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89780 : bv 32 := 0xcb453403.
Lemma F_89780 : fetch_word Asan.M.loaded_segments (0x897d0 : word) = Some W_89780.
Proof. vm_refl. Qed.
Lemma D_89780 : decode_any W_89780 = Some (Load SZ8 true 8 10 3252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89784 : bv 32 := 0x02813023.
Lemma F_89784 : fetch_word Asan.M.loaded_segments (0x897d4 : word) = Some W_89784.
Proof. vm_refl. Qed.
Lemma D_89784 : decode_any W_89784 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89788 : bv 32 := 0x00813c23.
Lemma F_89788 : fetch_word Asan.M.loaded_segments (0x897d8 : word) = Some W_89788.
Proof. vm_refl. Qed.
Lemma D_89788 : decode_any W_89788 = Some (Store SZ8 2 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8978c : bv 32 := 0x6b4020ef.
Lemma F_8978c : fetch_word Asan.M.loaded_segments (0x897dc : word) = Some W_8978c.
Proof. vm_refl. Qed.
Lemma D_8978c : decode_any W_8978c = Some (Jal 1 9908, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89790 : bv 32 := 0x08050263.
Lemma F_89790 : fetch_word Asan.M.loaded_segments (0x897e0 : word) = Some W_89790.
Proof. vm_refl. Qed.
Lemma D_89790 : decode_any W_89790 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89794 : bv 32 := 0x000d7597.
Lemma F_89794 : fetch_word Asan.M.loaded_segments (0x897e4 : word) = Some W_89794.
Proof. vm_refl. Qed.
Lemma D_89794 : decode_any W_89794 = Some (Auipc 11 215, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89798 : bv 32 := 0x4145b903.
Lemma F_89798 : fetch_word Asan.M.loaded_segments (0x897e8 : word) = Some W_89798.
Proof. vm_refl. Qed.
Lemma D_89798 : decode_any W_89798 = Some (Load SZ8 true 18 11 1044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8979c : bv 32 := 0x00093403.
Lemma F_8979c : fetch_word Asan.M.loaded_segments (0x897ec : word) = Some W_8979c.
Proof. vm_refl. Qed.
Lemma D_8979c : decode_any W_8979c = Some (Load SZ8 true 8 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_897a0 : bv 32 := 0x00041c63.
Lemma F_897a0 : fetch_word Asan.M.loaded_segments (0x897f0 : word) = Some W_897a0.
Proof. vm_refl. Qed.
Lemma D_897a0 : decode_any W_897a0 = Some (Branch BC_NE 8 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_897b8 : bv 32 := 0x04d020ef.
Lemma F_897b8 : fetch_word Asan.M.loaded_segments (0x89808 : word) = Some W_897b8.
Proof. vm_refl. Qed.
Lemma D_897b8 : decode_any W_897b8 = Some (Jal 1 10316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_897bc : bv 32 := 0x00050613.
Lemma F_897bc : fetch_word Asan.M.loaded_segments (0x8980c : word) = Some W_897bc.
Proof. vm_refl. Qed.
Lemma D_897bc : decode_any W_897bc = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_897c0 : bv 32 := 0x00a13c23.
Lemma F_897c0 : fetch_word Asan.M.loaded_segments (0x89810 : word) = Some W_897c0.
Proof. vm_refl. Qed.
Lemma D_897c0 : decode_any W_897c0 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_897c4 : bv 32 := 0x01010513.
Lemma F_897c4 : fetch_word Asan.M.loaded_segments (0x89814 : word) = Some W_897c4.
Proof. vm_refl. Qed.
Lemma D_897c4 : decode_any W_897c4 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_897c8 : bv 32 := 0x40850533.
Lemma F_897c8 : fetch_word Asan.M.loaded_segments (0x89818 : word) = Some W_897c8.
Proof. vm_refl. Qed.
Lemma D_897c8 : decode_any W_897c8 = Some (Op ALU_SUB 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_897cc : bv 32 := 0x408006b3.
Lemma F_897cc : fetch_word Asan.M.loaded_segments (0x8981c : word) = Some W_897cc.
Proof. vm_refl. Qed.
Lemma D_897cc : decode_any W_897cc = Some (Op ALU_SUB 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_897d0 : bv 32 := 0x00d576b3.
Lemma F_897d0 : fetch_word Asan.M.loaded_segments (0x89820 : word) = Some W_897d0.
Proof. vm_refl. Qed.
Lemma D_897d0 : decode_any W_897d0 = Some (Op ALU_AND 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_897d4 : bv 32 := 0x02d13023.
Lemma F_897d4 : fetch_word Asan.M.loaded_segments (0x89824 : word) = Some W_897d4.
Proof. vm_refl. Qed.
Lemma D_897d4 : decode_any W_897d4 = Some (Store SZ8 2 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_897d8 : bv 32 := 0x40d60733.
Lemma F_897d8 : fetch_word Asan.M.loaded_segments (0x89828 : word) = Some W_897d8.
Proof. vm_refl. Qed.
Lemma D_897d8 : decode_any W_897d8 = Some (Op ALU_SUB 14 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_897dc : bv 32 := 0x04000537.
Lemma F_897dc : fetch_word Asan.M.loaded_segments (0x8982c : word) = Some W_897dc.
Proof. vm_refl. Qed.
Lemma D_897dc : decode_any W_897dc = Some (Lui 10 16384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_897e0 : bv 32 := 0x0015051b.
Lemma F_897e0 : fetch_word Asan.M.loaded_segments (0x89830 : word) = Some W_897e0.
Proof. vm_refl. Qed.
Lemma D_897e0 : decode_any W_897e0 = Some (OpImm32 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_897e4 : bv 32 := 0x06a76263.
Lemma F_897e4 : fetch_word Asan.M.loaded_segments (0x89834 : word) = Some W_897e4.
Proof. vm_refl. Qed.
Lemma D_897e4 : decode_any W_897e4 = Some (Branch BC_LTU 14 10 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89848 : bv 32 := 0x00770713.
Lemma F_89848 : fetch_word Asan.M.loaded_segments (0x89898 : word) = Some W_89848.
Proof. vm_refl. Qed.
Lemma D_89848 : decode_any W_89848 = Some (OpImm ALU_ADD 14 14 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8984c : bv 32 := 0x10000537.
Lemma F_8984c : fetch_word Asan.M.loaded_segments (0x8989c : word) = Some W_8984c.
Proof. vm_refl. Qed.
Lemma D_8984c : decode_any W_8984c = Some (Lui 10 65536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89850 : bv 32 := 0xff85051b.
Lemma F_89850 : fetch_word Asan.M.loaded_segments (0x898a0 : word) = Some W_89850.
Proof. vm_refl. Qed.
Lemma D_89850 : decode_any W_89850 = Some (OpImm32 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89854 : bv 32 := 0x00a775b3.
Lemma F_89854 : fetch_word Asan.M.loaded_segments (0x898a4 : word) = Some W_89854.
Proof. vm_refl. Qed.
Lemma D_89854 : decode_any W_89854 = Some (Op ALU_AND 11 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89858 : bv 32 := 0x00068513.
Lemma F_89858 : fetch_word Asan.M.loaded_segments (0x898a8 : word) = Some W_89858.
Proof. vm_refl. Qed.
Lemma D_89858 : decode_any W_89858 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8985c : bv 32 := 0x00000613.
Lemma F_8985c : fetch_word Asan.M.loaded_segments (0x898ac : word) = Some W_8985c.
Proof. vm_refl. Qed.
Lemma D_8985c : decode_any W_8985c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89860 : bv 32 := 0x835f90ef.
Lemma F_89860 : fetch_word Asan.M.loaded_segments (0x898b0 : word) = Some W_89860.
Proof. vm_refl. Qed.
Lemma D_89860 : decode_any W_89860 = Some (Jal 1 2070580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89864 : bv 32 := 0x5dc020ef.
Lemma F_89864 : fetch_word Asan.M.loaded_segments (0x898b4 : word) = Some W_89864.
Proof. vm_refl. Qed.
Lemma D_89864 : decode_any W_89864 = Some (Jal 1 9692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89868 : bv 32 := 0x02050263.
Lemma F_89868 : fetch_word Asan.M.loaded_segments (0x898b8 : word) = Some W_89868.
Proof. vm_refl. Qed.
Lemma D_89868 : decode_any W_89868 = Some (Branch BC_EQ 10 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8986c : bv 32 := 0x02850583.
Lemma F_8986c : fetch_word Asan.M.loaded_segments (0x898bc : word) = Some W_8986c.
Proof. vm_refl. Qed.
Lemma D_8986c : decode_any W_8986c = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89870 : bv 32 := 0x00059e63.
Lemma F_89870 : fetch_word Asan.M.loaded_segments (0x898c0 : word) = Some W_89870.
Proof. vm_refl. Qed.
Lemma D_89870 : decode_any W_89870 = Some (Branch BC_NE 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89874 : bv 32 := 0x04853503.
Lemma F_89874 : fetch_word Asan.M.loaded_segments (0x898c4 : word) = Some W_89874.
Proof. vm_refl. Qed.
Lemma D_89874 : decode_any W_89874 = Some (Load SZ8 true 10 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89878 : bv 32 := 0x00253593.
Lemma F_89878 : fetch_word Asan.M.loaded_segments (0x898c8 : word) = Some W_89878.
Proof. vm_refl. Qed.
Lemma D_89878 : decode_any W_89878 = Some (OpImm ALU_SLTU 11 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8987c : bv 32 := 0xfff58593.
Lemma F_8987c : fetch_word Asan.M.loaded_segments (0x898cc : word) = Some W_8987c.
Proof. vm_refl. Qed.
Lemma D_8987c : decode_any W_8987c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89880 : bv 32 := 0x00a5f533.
Lemma F_89880 : fetch_word Asan.M.loaded_segments (0x898d0 : word) = Some W_89880.
Proof. vm_refl. Qed.
Lemma D_89880 : decode_any W_89880 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89884 : bv 32 := 0x00050463.
Lemma F_89884 : fetch_word Asan.M.loaded_segments (0x898d4 : word) = Some W_89884.
Proof. vm_refl. Qed.
Lemma D_89884 : decode_any W_89884 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89888 : bv 32 := 0xc34dc0ef.
Lemma F_89888 : fetch_word Asan.M.loaded_segments (0x898d8 : word) = Some W_89888.
Proof. vm_refl. Qed.
Lemma D_89888 : decode_any W_89888 = Some (Jal 1 1950772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8988c : bv 32 := 0x04813083.
Lemma F_8988c : fetch_word Asan.M.loaded_segments (0x898dc : word) = Some W_8988c.
Proof. vm_refl. Qed.
Lemma D_8988c : decode_any W_8988c = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89890 : bv 32 := 0x04013403.
Lemma F_89890 : fetch_word Asan.M.loaded_segments (0x898e0 : word) = Some W_89890.
Proof. vm_refl. Qed.
Lemma D_89890 : decode_any W_89890 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89894 : bv 32 := 0x03813483.
Lemma F_89894 : fetch_word Asan.M.loaded_segments (0x898e4 : word) = Some W_89894.
Proof. vm_refl. Qed.
Lemma D_89894 : decode_any W_89894 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_89898 : bv 32 := 0x03013903.
Lemma F_89898 : fetch_word Asan.M.loaded_segments (0x898e8 : word) = Some W_89898.
Proof. vm_refl. Qed.
Lemma D_89898 : decode_any W_89898 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8989c : bv 32 := 0x02813983.
Lemma F_8989c : fetch_word Asan.M.loaded_segments (0x898ec : word) = Some W_8989c.
Proof. vm_refl. Qed.
Lemma D_8989c : decode_any W_8989c = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_898a0 : bv 32 := 0x05010113.
Lemma F_898a0 : fetch_word Asan.M.loaded_segments (0x898f0 : word) = Some W_898a0.
Proof. vm_refl. Qed.
Lemma D_898a0 : decode_any W_898a0 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_898a4 : bv 32 := 0x00008067.
Lemma F_898a4 : fetch_word Asan.M.loaded_segments (0x898f4 : word) = Some W_898a4.
Proof. vm_refl. Qed.
Lemma D_898a4 : decode_any W_898a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

