(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_50584 : bv 32 := 0x00008067.
Lemma F_50584 : fetch_word Plain.M.loaded_segments (0x50584 : word) = Some W_50584.
Proof. vm_refl. Qed.
Lemma D_50584 : decode_any W_50584 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50588 : bv 32 := 0xe8010113.
Lemma F_50588 : fetch_word Plain.M.loaded_segments (0x50588 : word) = Some W_50588.
Proof. vm_refl. Qed.
Lemma D_50588 : decode_any W_50588 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5058c : bv 32 := 0x16113c23.
Lemma F_5058c : fetch_word Plain.M.loaded_segments (0x5058c : word) = Some W_5058c.
Proof. vm_refl. Qed.
Lemma D_5058c : decode_any W_5058c = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50590 : bv 32 := 0x16813823.
Lemma F_50590 : fetch_word Plain.M.loaded_segments (0x50590 : word) = Some W_50590.
Proof. vm_refl. Qed.
Lemma D_50590 : decode_any W_50590 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50594 : bv 32 := 0x16913423.
Lemma F_50594 : fetch_word Plain.M.loaded_segments (0x50594 : word) = Some W_50594.
Proof. vm_refl. Qed.
Lemma D_50594 : decode_any W_50594 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50598 : bv 32 := 0x17213023.
Lemma F_50598 : fetch_word Plain.M.loaded_segments (0x50598 : word) = Some W_50598.
Proof. vm_refl. Qed.
Lemma D_50598 : decode_any W_50598 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5059c : bv 32 := 0x00058413.
Lemma F_5059c : fetch_word Plain.M.loaded_segments (0x5059c : word) = Some W_5059c.
Proof. vm_refl. Qed.
Lemma D_5059c : decode_any W_5059c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505a0 : bv 32 := 0x00050493.
Lemma F_505a0 : fetch_word Plain.M.loaded_segments (0x505a0 : word) = Some W_505a0.
Proof. vm_refl. Qed.
Lemma D_505a0 : decode_any W_505a0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505a4 : bv 32 := 0x03010513.
Lemma F_505a4 : fetch_word Plain.M.loaded_segments (0x505a4 : word) = Some W_505a4.
Proof. vm_refl. Qed.
Lemma D_505a4 : decode_any W_505a4 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505a8 : bv 32 := 0x13000613.
Lemma F_505a8 : fetch_word Plain.M.loaded_segments (0x505a8 : word) = Some W_505a8.
Proof. vm_refl. Qed.
Lemma D_505a8 : decode_any W_505a8 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505ac : bv 32 := 0x00000593.
Lemma F_505ac : fetch_word Plain.M.loaded_segments (0x505ac : word) = Some W_505ac.
Proof. vm_refl. Qed.
Lemma D_505ac : decode_any W_505ac = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505b0 : bv 32 := 0x2c00e0ef.
Lemma F_505b0 : fetch_word Plain.M.loaded_segments (0x505b0 : word) = Some W_505b0.
Proof. vm_refl. Qed.
Lemma D_505b0 : decode_any W_505b0 = Some (Jal 1 58048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505b4 : bv 32 := 0x00013517.
Lemma F_505b4 : fetch_word Plain.M.loaded_segments (0x505b4 : word) = Some W_505b4.
Proof. vm_refl. Qed.
Lemma D_505b4 : decode_any W_505b4 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505b8 : bv 32 := 0x7c453503.
Lemma F_505b8 : fetch_word Plain.M.loaded_segments (0x505b8 : word) = Some W_505b8.
Proof. vm_refl. Qed.
Lemma D_505b8 : decode_any W_505b8 = Some (Load SZ8 true 10 10 1988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505bc : bv 32 := 0x00953023.
Lemma F_505bc : fetch_word Plain.M.loaded_segments (0x505bc : word) = Some W_505bc.
Proof. vm_refl. Qed.
Lemma D_505bc : decode_any W_505bc = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505c0 : bv 32 := 0x0004b503.
Lemma F_505c0 : fetch_word Plain.M.loaded_segments (0x505c0 : word) = Some W_505c0.
Proof. vm_refl. Qed.
Lemma D_505c0 : decode_any W_505c0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505c4 : bv 32 := 0x00848493.
Lemma F_505c4 : fetch_word Plain.M.loaded_segments (0x505c4 : word) = Some W_505c4.
Proof. vm_refl. Qed.
Lemma D_505c4 : decode_any W_505c4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505c8 : bv 32 := 0xfe051ce3.
Lemma F_505c8 : fetch_word Plain.M.loaded_segments (0x505c8 : word) = Some W_505c8.
Proof. vm_refl. Qed.
Lemma D_505c8 : decode_any W_505c8 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505cc : bv 32 := 0x00046517.
Lemma F_505cc : fetch_word Plain.M.loaded_segments (0x505cc : word) = Some W_505cc.
Proof. vm_refl. Qed.
Lemma D_505cc : decode_any W_505cc = Some (Auipc 10 70, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505d0 : bv 32 := 0x89450913.
Lemma F_505d0 : fetch_word Plain.M.loaded_segments (0x505d0 : word) = Some W_505d0.
Proof. vm_refl. Qed.
Lemma D_505d0 : decode_any W_505d0 = Some (OpImm ALU_ADD 18 10 2196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505d4 : bv 32 := 0x00993423.
Lemma F_505d4 : fetch_word Plain.M.loaded_segments (0x505d4 : word) = Some W_505d4.
Proof. vm_refl. Qed.
Lemma D_505d4 : decode_any W_505d4 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505d8 : bv 32 := 0x0004b583.
Lemma F_505d8 : fetch_word Plain.M.loaded_segments (0x505d8 : word) = Some W_505d8.
Proof. vm_refl. Qed.
Lemma D_505d8 : decode_any W_505d8 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505dc : bv 32 := 0x04058c63.
Lemma F_505dc : fetch_word Plain.M.loaded_segments (0x505dc : word) = Some W_505dc.
Proof. vm_refl. Qed.
Lemma D_505dc : decode_any W_505dc = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505e0 : bv 32 := 0x01048493.
Lemma F_505e0 : fetch_word Plain.M.loaded_segments (0x505e0 : word) = Some W_505e0.
Proof. vm_refl. Qed.
Lemma D_505e0 : decode_any W_505e0 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505e4 : bv 32 := 0x02500513.
Lemma F_505e4 : fetch_word Plain.M.loaded_segments (0x505e4 : word) = Some W_505e4.
Proof. vm_refl. Qed.
Lemma D_505e4 : decode_any W_505e4 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505e8 : bv 32 := 0x03010613.
Lemma F_505e8 : fetch_word Plain.M.loaded_segments (0x505e8 : word) = Some W_505e8.
Proof. vm_refl. Qed.
Lemma D_505e8 : decode_any W_505e8 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505ec : bv 32 := 0x0100006f.
Lemma F_505ec : fetch_word Plain.M.loaded_segments (0x505ec : word) = Some W_505ec.
Proof. vm_refl. Qed.
Lemma D_505ec : decode_any W_505ec = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505f0 : bv 32 := 0x0004b583.
Lemma F_505f0 : fetch_word Plain.M.loaded_segments (0x505f0 : word) = Some W_505f0.
Proof. vm_refl. Qed.
Lemma D_505f0 : decode_any W_505f0 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505f4 : bv 32 := 0x01048493.
Lemma F_505f4 : fetch_word Plain.M.loaded_segments (0x505f4 : word) = Some W_505f4.
Proof. vm_refl. Qed.
Lemma D_505f4 : decode_any W_505f4 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505f8 : bv 32 := 0x00058e63.
Lemma F_505f8 : fetch_word Plain.M.loaded_segments (0x505f8 : word) = Some W_505f8.
Proof. vm_refl. Qed.
Lemma D_505f8 : decode_any W_505f8 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_505fc : bv 32 := 0xfeb56ae3.
Lemma F_505fc : fetch_word Plain.M.loaded_segments (0x505fc : word) = Some W_505fc.
Proof. vm_refl. Qed.
Lemma D_505fc : decode_any W_505fc = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50600 : bv 32 := 0xff84b683.
Lemma F_50600 : fetch_word Plain.M.loaded_segments (0x50600 : word) = Some W_50600.
Proof. vm_refl. Qed.
Lemma D_50600 : decode_any W_50600 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50604 : bv 32 := 0x00359593.
Lemma F_50604 : fetch_word Plain.M.loaded_segments (0x50604 : word) = Some W_50604.
Proof. vm_refl. Qed.
Lemma D_50604 : decode_any W_50604 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50608 : bv 32 := 0x00b605b3.
Lemma F_50608 : fetch_word Plain.M.loaded_segments (0x50608 : word) = Some W_50608.
Proof. vm_refl. Qed.
Lemma D_50608 : decode_any W_50608 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5060c : bv 32 := 0x00d5b023.
Lemma F_5060c : fetch_word Plain.M.loaded_segments (0x5060c : word) = Some W_5060c.
Proof. vm_refl. Qed.
Lemma D_5060c : decode_any W_5060c = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50610 : bv 32 := 0xfe1ff06f.
Lemma F_50610 : fetch_word Plain.M.loaded_segments (0x50610 : word) = Some W_50610.
Proof. vm_refl. Qed.
Lemma D_50610 : decode_any W_50610 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50614 : bv 32 := 0x0b013583.
Lemma F_50614 : fetch_word Plain.M.loaded_segments (0x50614 : word) = Some W_50614.
Proof. vm_refl. Qed.
Lemma D_50614 : decode_any W_50614 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50618 : bv 32 := 0x13013503.
Lemma F_50618 : fetch_word Plain.M.loaded_segments (0x50618 : word) = Some W_50618.
Proof. vm_refl. Qed.
Lemma D_50618 : decode_any W_50618 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5061c : bv 32 := 0x00046617.
Lemma F_5061c : fetch_word Plain.M.loaded_segments (0x5061c : word) = Some W_5061c.
Proof. vm_refl. Qed.
Lemma D_5061c : decode_any W_5061c = Some (Auipc 12 70, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50620 : bv 32 := 0x8ab63623.
Lemma F_50620 : fetch_word Plain.M.loaded_segments (0x50620 : word) = Some W_50620.
Proof. vm_refl. Qed.
Lemma D_50620 : decode_any W_50620 = Some (Store SZ8 12 11 2220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50624 : bv 32 := 0x00050c63.
Lemma F_50624 : fetch_word Plain.M.loaded_segments (0x50624 : word) = Some W_50624.
Proof. vm_refl. Qed.
Lemma D_50624 : decode_any W_50624 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50628 : bv 32 := 0x00046597.
Lemma F_50628 : fetch_word Plain.M.loaded_segments (0x50628 : word) = Some W_50628.
Proof. vm_refl. Qed.
Lemma D_50628 : decode_any W_50628 = Some (Auipc 11 70, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5062c : bv 32 := 0x82a5b023.
Lemma F_5062c : fetch_word Plain.M.loaded_segments (0x5062c : word) = Some W_5062c.
Proof. vm_refl. Qed.
Lemma D_5062c : decode_any W_5062c = Some (Store SZ8 11 10 2080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50630 : bv 32 := 0x00c0006f.
Lemma F_50630 : fetch_word Plain.M.loaded_segments (0x50630 : word) = Some W_50630.
Proof. vm_refl. Qed.
Lemma D_50630 : decode_any W_50630 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50634 : bv 32 := 0x00046517.
Lemma F_50634 : fetch_word Plain.M.loaded_segments (0x50634 : word) = Some W_50634.
Proof. vm_refl. Qed.
Lemma D_50634 : decode_any W_50634 = Some (Auipc 10 70, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50638 : bv 32 := 0x88053a23.
Lemma F_50638 : fetch_word Plain.M.loaded_segments (0x50638 : word) = Some W_50638.
Proof. vm_refl. Qed.
Lemma D_50638 : decode_any W_50638 = Some (Store SZ8 10 0 2196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5063c : bv 32 := 0x06013503.
Lemma F_5063c : fetch_word Plain.M.loaded_segments (0x5063c : word) = Some W_5063c.
Proof. vm_refl. Qed.
Lemma D_5063c : decode_any W_5063c = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50640 : bv 32 := 0x02a93823.
Lemma F_50640 : fetch_word Plain.M.loaded_segments (0x50640 : word) = Some W_50640.
Proof. vm_refl. Qed.
Lemma D_50640 : decode_any W_50640 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50644 : bv 32 := 0x00041463.
Lemma F_50644 : fetch_word Plain.M.loaded_segments (0x50644 : word) = Some W_50644.
Proof. vm_refl. Qed.
Lemma D_50644 : decode_any W_50644 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50648 : bv 32 := 0x12813403.
Lemma F_50648 : fetch_word Plain.M.loaded_segments (0x50648 : word) = Some W_50648.
Proof. vm_refl. Qed.
Lemma D_50648 : decode_any W_50648 = Some (Load SZ8 true 8 2 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5064c : bv 32 := 0x00041663.
Lemma F_5064c : fetch_word Plain.M.loaded_segments (0x5064c : word) = Some W_5064c.
Proof. vm_refl. Qed.
Lemma D_5064c : decode_any W_5064c = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50650 : bv 32 := 0xfffc0517.
Lemma F_50650 : fetch_word Plain.M.loaded_segments (0x50650 : word) = Some W_50650.
Proof. vm_refl. Qed.
Lemma D_50650 : decode_any W_50650 = Some (Auipc 10 1048512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50654 : bv 32 := 0x5a150413.
Lemma F_50654 : fetch_word Plain.M.loaded_segments (0x50654 : word) = Some W_50654.
Proof. vm_refl. Qed.
Lemma D_50654 : decode_any W_50654 = Some (OpImm ALU_ADD 8 10 1441, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50658 : bv 32 := 0x00013517.
Lemma F_50658 : fetch_word Plain.M.loaded_segments (0x50658 : word) = Some W_50658.
Proof. vm_refl. Qed.
Lemma D_50658 : decode_any W_50658 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5065c : bv 32 := 0x72853583.
Lemma F_5065c : fetch_word Plain.M.loaded_segments (0x5065c : word) = Some W_5065c.
Proof. vm_refl. Qed.
Lemma D_5065c : decode_any W_5065c = Some (Load SZ8 true 11 10 1832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50660 : bv 32 := 0x00013517.
Lemma F_50660 : fetch_word Plain.M.loaded_segments (0x50660 : word) = Some W_50660.
Proof. vm_refl. Qed.
Lemma D_50660 : decode_any W_50660 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50664 : bv 32 := 0x72853503.
Lemma F_50664 : fetch_word Plain.M.loaded_segments (0x50664 : word) = Some W_50664.
Proof. vm_refl. Qed.
Lemma D_50664 : decode_any W_50664 = Some (Load SZ8 true 10 10 1832, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50668 : bv 32 := 0x0085b023.
Lemma F_50668 : fetch_word Plain.M.loaded_segments (0x50668 : word) = Some W_50668.
Proof. vm_refl. Qed.
Lemma D_50668 : decode_any W_50668 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5066c : bv 32 := 0x00140593.
Lemma F_5066c : fetch_word Plain.M.loaded_segments (0x5066c : word) = Some W_5066c.
Proof. vm_refl. Qed.
Lemma D_5066c : decode_any W_5066c = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50670 : bv 32 := 0x00853023.
Lemma F_50670 : fetch_word Plain.M.loaded_segments (0x50670 : word) = Some W_50670.
Proof. vm_refl. Qed.
Lemma D_50670 : decode_any W_50670 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50674 : bv 32 := 0x02f00613.
Lemma F_50674 : fetch_word Plain.M.loaded_segments (0x50674 : word) = Some W_50674.
Proof. vm_refl. Qed.
Lemma D_50674 : decode_any W_50674 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50678 : bv 32 := 0x00c0006f.
Lemma F_50678 : fetch_word Plain.M.loaded_segments (0x50678 : word) = Some W_50678.
Proof. vm_refl. Qed.
Lemma D_50678 : decode_any W_50678 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5067c : bv 32 := 0x00b53023.
Lemma F_5067c : fetch_word Plain.M.loaded_segments (0x5067c : word) = Some W_5067c.
Proof. vm_refl. Qed.
Lemma D_5067c : decode_any W_5067c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50680 : bv 32 := 0x00158593.
Lemma F_50680 : fetch_word Plain.M.loaded_segments (0x50680 : word) = Some W_50680.
Proof. vm_refl. Qed.
Lemma D_50680 : decode_any W_50680 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50684 : bv 32 := 0xfff5c683.
Lemma F_50684 : fetch_word Plain.M.loaded_segments (0x50684 : word) = Some W_50684.
Proof. vm_refl. Qed.
Lemma D_50684 : decode_any W_50684 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50688 : bv 32 := 0xfec68ae3.
Lemma F_50688 : fetch_word Plain.M.loaded_segments (0x50688 : word) = Some W_50688.
Proof. vm_refl. Qed.
Lemma D_50688 : decode_any W_50688 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5068c : bv 32 := 0xfe069ae3.
Lemma F_5068c : fetch_word Plain.M.loaded_segments (0x5068c : word) = Some W_5068c.
Proof. vm_refl. Qed.
Lemma D_5068c : decode_any W_5068c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50690 : bv 32 := 0x03010513.
Lemma F_50690 : fetch_word Plain.M.loaded_segments (0x50690 : word) = Some W_50690.
Proof. vm_refl. Qed.
Lemma D_50690 : decode_any W_50690 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50694 : bv 32 := 0x214000ef.
Lemma F_50694 : fetch_word Plain.M.loaded_segments (0x50694 : word) = Some W_50694.
Proof. vm_refl. Qed.
Lemma D_50694 : decode_any W_50694 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50698 : bv 32 := 0x0f813503.
Lemma F_50698 : fetch_word Plain.M.loaded_segments (0x50698 : word) = Some W_50698.
Proof. vm_refl. Qed.
Lemma D_50698 : decode_any W_50698 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5069c : bv 32 := 0x0e5000ef.
Lemma F_5069c : fetch_word Plain.M.loaded_segments (0x5069c : word) = Some W_5069c.
Proof. vm_refl. Qed.
Lemma D_5069c : decode_any W_5069c = Some (Jal 1 2276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506a0 : bv 32 := 0x08813503.
Lemma F_506a0 : fetch_word Plain.M.loaded_segments (0x506a0 : word) = Some W_506a0.
Proof. vm_refl. Qed.
Lemma D_506a0 : decode_any W_506a0 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506a4 : bv 32 := 0x09013583.
Lemma F_506a4 : fetch_word Plain.M.loaded_segments (0x506a4 : word) = Some W_506a4.
Proof. vm_refl. Qed.
Lemma D_506a4 : decode_any W_506a4 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506a8 : bv 32 := 0x00b51c63.
Lemma F_506a8 : fetch_word Plain.M.loaded_segments (0x506a8 : word) = Some W_506a8.
Proof. vm_refl. Qed.
Lemma D_506a8 : decode_any W_506a8 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506ac : bv 32 := 0x09813503.
Lemma F_506ac : fetch_word Plain.M.loaded_segments (0x506ac : word) = Some W_506ac.
Proof. vm_refl. Qed.
Lemma D_506ac : decode_any W_506ac = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506b0 : bv 32 := 0x0a013583.
Lemma F_506b0 : fetch_word Plain.M.loaded_segments (0x506b0 : word) = Some W_506b0.
Proof. vm_refl. Qed.
Lemma D_506b0 : decode_any W_506b0 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506b4 : bv 32 := 0x00b51663.
Lemma F_506b4 : fetch_word Plain.M.loaded_segments (0x506b4 : word) = Some W_506b4.
Proof. vm_refl. Qed.
Lemma D_506b4 : decode_any W_506b4 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506b8 : bv 32 := 0x0e813503.
Lemma F_506b8 : fetch_word Plain.M.loaded_segments (0x506b8 : word) = Some W_506b8.
Proof. vm_refl. Qed.
Lemma D_506b8 : decode_any W_506b8 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506bc : bv 32 := 0x0e050063.
Lemma F_506bc : fetch_word Plain.M.loaded_segments (0x506bc : word) = Some W_506bc.
Proof. vm_refl. Qed.
Lemma D_506bc : decode_any W_506bc = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506c0 : bv 32 := 0x00200693.
Lemma F_506c0 : fetch_word Plain.M.loaded_segments (0x506c0 : word) = Some W_506c0.
Proof. vm_refl. Qed.
Lemma D_506c0 : decode_any W_506c0 = Some (OpImm ALU_ADD 13 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506c4 : bv 32 := 0x00100793.
Lemma F_506c4 : fetch_word Plain.M.loaded_segments (0x506c4 : word) = Some W_506c4.
Proof. vm_refl. Qed.
Lemma D_506c4 : decode_any W_506c4 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506c8 : bv 32 := 0x00013423.
Lemma F_506c8 : fetch_word Plain.M.loaded_segments (0x506c8 : word) = Some W_506c8.
Proof. vm_refl. Qed.
Lemma D_506c8 : decode_any W_506c8 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506cc : bv 32 := 0x00013823.
Lemma F_506cc : fetch_word Plain.M.loaded_segments (0x506cc : word) = Some W_506cc.
Proof. vm_refl. Qed.
Lemma D_506cc : decode_any W_506cc = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506d0 : bv 32 := 0x04900893.
Lemma F_506d0 : fetch_word Plain.M.loaded_segments (0x506d0 : word) = Some W_506d0.
Proof. vm_refl. Qed.
Lemma D_506d0 : decode_any W_506d0 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506d4 : bv 32 := 0x01810513.
Lemma F_506d4 : fetch_word Plain.M.loaded_segments (0x506d4 : word) = Some W_506d4.
Proof. vm_refl. Qed.
Lemma D_506d4 : decode_any W_506d4 = Some (OpImm ALU_ADD 10 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506d8 : bv 32 := 0x00300593.
Lemma F_506d8 : fetch_word Plain.M.loaded_segments (0x506d8 : word) = Some W_506d8.
Proof. vm_refl. Qed.
Lemma D_506d8 : decode_any W_506d8 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506dc : bv 32 := 0x00810613.
Lemma F_506dc : fetch_word Plain.M.loaded_segments (0x506dc : word) = Some W_506dc.
Proof. vm_refl. Qed.
Lemma D_506dc : decode_any W_506dc = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506e0 : bv 32 := 0x00800713.
Lemma F_506e0 : fetch_word Plain.M.loaded_segments (0x506e0 : word) = Some W_506e0.
Proof. vm_refl. Qed.
Lemma D_506e0 : decode_any W_506e0 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506e4 : bv 32 := 0x00013c23.
Lemma F_506e4 : fetch_word Plain.M.loaded_segments (0x506e4 : word) = Some W_506e4.
Proof. vm_refl. Qed.
Lemma D_506e4 : decode_any W_506e4 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506e8 : bv 32 := 0x02f13023.
Lemma F_506e8 : fetch_word Plain.M.loaded_segments (0x506e8 : word) = Some W_506e8.
Proof. vm_refl. Qed.
Lemma D_506e8 : decode_any W_506e8 = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506ec : bv 32 := 0x02d13423.
Lemma F_506ec : fetch_word Plain.M.loaded_segments (0x506ec : word) = Some W_506ec.
Proof. vm_refl. Qed.
Lemma D_506ec : decode_any W_506ec = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506f0 : bv 32 := 0x00000693.
Lemma F_506f0 : fetch_word Plain.M.loaded_segments (0x506f0 : word) = Some W_506f0.
Proof. vm_refl. Qed.
Lemma D_506f0 : decode_any W_506f0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506f4 : bv 32 := 0x00000073.
Lemma F_506f4 : fetch_word Plain.M.loaded_segments (0x506f4 : word) = Some W_506f4.
Proof. vm_refl. Qed.
Lemma D_506f4 : decode_any W_506f4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_506f4 : is_ecall W_506f4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_506f8 : bv 32 := 0x02051513.
Lemma F_506f8 : fetch_word Plain.M.loaded_segments (0x506f8 : word) = Some W_506f8.
Proof. vm_refl. Qed.
Lemma D_506f8 : decode_any W_506f8 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_506fc : bv 32 := 0x00055463.
Lemma F_506fc : fetch_word Plain.M.loaded_segments (0x506fc : word) = Some W_506fc.
Proof. vm_refl. Qed.
Lemma D_506fc : decode_any W_506fc = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50700 : bv 32 := 0x00000023.
Lemma F_50700 : fetch_word Plain.M.loaded_segments (0x50700 : word) = Some W_50700.
Proof. vm_refl. Qed.
Lemma D_50700 : decode_any W_50700 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50704 : bv 32 := 0x01e15503.
Lemma F_50704 : fetch_word Plain.M.loaded_segments (0x50704 : word) = Some W_50704.
Proof. vm_refl. Qed.
Lemma D_50704 : decode_any W_50704 = Some (Load SZ2 false 10 2 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50708 : bv 32 := 0x02057513.
Lemma F_50708 : fetch_word Plain.M.loaded_segments (0x50708 : word) = Some W_50708.
Proof. vm_refl. Qed.
Lemma D_50708 : decode_any W_50708 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5070c : bv 32 := 0x02050463.
Lemma F_5070c : fetch_word Plain.M.loaded_segments (0x5070c : word) = Some W_5070c.
Proof. vm_refl. Qed.
Lemma D_5070c : decode_any W_5070c = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50710 : bv 32 := 0xfffc3517.
Lemma F_50710 : fetch_word Plain.M.loaded_segments (0x50710 : word) = Some W_50710.
Proof. vm_refl. Qed.
Lemma D_50710 : decode_any W_50710 = Some (Auipc 10 1048515, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50714 : bv 32 := 0x00008637.
Lemma F_50714 : fetch_word Plain.M.loaded_segments (0x50714 : word) = Some W_50714.
Proof. vm_refl. Qed.
Lemma D_50714 : decode_any W_50714 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50718 : bv 32 := 0x03800893.
Lemma F_50718 : fetch_word Plain.M.loaded_segments (0x50718 : word) = Some W_50718.
Proof. vm_refl. Qed.
Lemma D_50718 : decode_any W_50718 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5071c : bv 32 := 0x80d50593.
Lemma F_5071c : fetch_word Plain.M.loaded_segments (0x5071c : word) = Some W_5071c.
Proof. vm_refl. Qed.
Lemma D_5071c : decode_any W_5071c = Some (OpImm ALU_ADD 11 10 2061, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50720 : bv 32 := 0x0026061b.
Lemma F_50720 : fetch_word Plain.M.loaded_segments (0x50720 : word) = Some W_50720.
Proof. vm_refl. Qed.
Lemma D_50720 : decode_any W_50720 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50724 : bv 32 := 0xf9c00513.
Lemma F_50724 : fetch_word Plain.M.loaded_segments (0x50724 : word) = Some W_50724.
Proof. vm_refl. Qed.
Lemma D_50724 : decode_any W_50724 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50728 : bv 32 := 0x00000073.
Lemma F_50728 : fetch_word Plain.M.loaded_segments (0x50728 : word) = Some W_50728.
Proof. vm_refl. Qed.
Lemma D_50728 : decode_any W_50728 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_50728 : is_ecall W_50728 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_5072c : bv 32 := 0x00055463.
Lemma F_5072c : fetch_word Plain.M.loaded_segments (0x5072c : word) = Some W_5072c.
Proof. vm_refl. Qed.
Lemma D_5072c : decode_any W_5072c = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50730 : bv 32 := 0x00000023.
Lemma F_50730 : fetch_word Plain.M.loaded_segments (0x50730 : word) = Some W_50730.
Proof. vm_refl. Qed.
Lemma D_50730 : decode_any W_50730 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50734 : bv 32 := 0x02615503.
Lemma F_50734 : fetch_word Plain.M.loaded_segments (0x50734 : word) = Some W_50734.
Proof. vm_refl. Qed.
Lemma D_50734 : decode_any W_50734 = Some (Load SZ2 false 10 2 38, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50738 : bv 32 := 0x02057513.
Lemma F_50738 : fetch_word Plain.M.loaded_segments (0x50738 : word) = Some W_50738.
Proof. vm_refl. Qed.
Lemma D_50738 : decode_any W_50738 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5073c : bv 32 := 0x02050463.
Lemma F_5073c : fetch_word Plain.M.loaded_segments (0x5073c : word) = Some W_5073c.
Proof. vm_refl. Qed.
Lemma D_5073c : decode_any W_5073c = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50740 : bv 32 := 0xfffc2517.
Lemma F_50740 : fetch_word Plain.M.loaded_segments (0x50740 : word) = Some W_50740.
Proof. vm_refl. Qed.
Lemma D_50740 : decode_any W_50740 = Some (Auipc 10 1048514, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50744 : bv 32 := 0x00008637.
Lemma F_50744 : fetch_word Plain.M.loaded_segments (0x50744 : word) = Some W_50744.
Proof. vm_refl. Qed.
Lemma D_50744 : decode_any W_50744 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50748 : bv 32 := 0x03800893.
Lemma F_50748 : fetch_word Plain.M.loaded_segments (0x50748 : word) = Some W_50748.
Proof. vm_refl. Qed.
Lemma D_50748 : decode_any W_50748 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5074c : bv 32 := 0x7dd50593.
Lemma F_5074c : fetch_word Plain.M.loaded_segments (0x5074c : word) = Some W_5074c.
Proof. vm_refl. Qed.
Lemma D_5074c : decode_any W_5074c = Some (OpImm ALU_ADD 11 10 2013, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50750 : bv 32 := 0x0026061b.
Lemma F_50750 : fetch_word Plain.M.loaded_segments (0x50750 : word) = Some W_50750.
Proof. vm_refl. Qed.
Lemma D_50750 : decode_any W_50750 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50754 : bv 32 := 0xf9c00513.
Lemma F_50754 : fetch_word Plain.M.loaded_segments (0x50754 : word) = Some W_50754.
Proof. vm_refl. Qed.
Lemma D_50754 : decode_any W_50754 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50758 : bv 32 := 0x00000073.
Lemma F_50758 : fetch_word Plain.M.loaded_segments (0x50758 : word) = Some W_50758.
Proof. vm_refl. Qed.
Lemma D_50758 : decode_any W_50758 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_50758 : is_ecall W_50758 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_5075c : bv 32 := 0x00055463.
Lemma F_5075c : fetch_word Plain.M.loaded_segments (0x5075c : word) = Some W_5075c.
Proof. vm_refl. Qed.
Lemma D_5075c : decode_any W_5075c = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50760 : bv 32 := 0x00000023.
Lemma F_50760 : fetch_word Plain.M.loaded_segments (0x50760 : word) = Some W_50760.
Proof. vm_refl. Qed.
Lemma D_50760 : decode_any W_50760 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50764 : bv 32 := 0x02e15503.
Lemma F_50764 : fetch_word Plain.M.loaded_segments (0x50764 : word) = Some W_50764.
Proof. vm_refl. Qed.
Lemma D_50764 : decode_any W_50764 = Some (Load SZ2 false 10 2 46, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50768 : bv 32 := 0x02057513.
Lemma F_50768 : fetch_word Plain.M.loaded_segments (0x50768 : word) = Some W_50768.
Proof. vm_refl. Qed.
Lemma D_50768 : decode_any W_50768 = Some (OpImm ALU_AND 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5076c : bv 32 := 0x02050463.
Lemma F_5076c : fetch_word Plain.M.loaded_segments (0x5076c : word) = Some W_5076c.
Proof. vm_refl. Qed.
Lemma D_5076c : decode_any W_5076c = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50770 : bv 32 := 0xfffc2517.
Lemma F_50770 : fetch_word Plain.M.loaded_segments (0x50770 : word) = Some W_50770.
Proof. vm_refl. Qed.
Lemma D_50770 : decode_any W_50770 = Some (Auipc 10 1048514, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50774 : bv 32 := 0x00008637.
Lemma F_50774 : fetch_word Plain.M.loaded_segments (0x50774 : word) = Some W_50774.
Proof. vm_refl. Qed.
Lemma D_50774 : decode_any W_50774 = Some (Lui 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50778 : bv 32 := 0x03800893.
Lemma F_50778 : fetch_word Plain.M.loaded_segments (0x50778 : word) = Some W_50778.
Proof. vm_refl. Qed.
Lemma D_50778 : decode_any W_50778 = Some (OpImm ALU_ADD 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5077c : bv 32 := 0x7ad50593.
Lemma F_5077c : fetch_word Plain.M.loaded_segments (0x5077c : word) = Some W_5077c.
Proof. vm_refl. Qed.
Lemma D_5077c : decode_any W_5077c = Some (OpImm ALU_ADD 11 10 1965, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50780 : bv 32 := 0x0026061b.
Lemma F_50780 : fetch_word Plain.M.loaded_segments (0x50780 : word) = Some W_50780.
Proof. vm_refl. Qed.
Lemma D_50780 : decode_any W_50780 = Some (OpImm32 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50784 : bv 32 := 0xf9c00513.
Lemma F_50784 : fetch_word Plain.M.loaded_segments (0x50784 : word) = Some W_50784.
Proof. vm_refl. Qed.
Lemma D_50784 : decode_any W_50784 = Some (OpImm ALU_ADD 10 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50788 : bv 32 := 0x00000073.
Lemma F_50788 : fetch_word Plain.M.loaded_segments (0x50788 : word) = Some W_50788.
Proof. vm_refl. Qed.
Lemma D_50788 : decode_any W_50788 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_50788 : is_ecall W_50788 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_5078c : bv 32 := 0x00055463.
Lemma F_5078c : fetch_word Plain.M.loaded_segments (0x5078c : word) = Some W_5078c.
Proof. vm_refl. Qed.
Lemma D_5078c : decode_any W_5078c = Some (Branch BC_GE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50790 : bv 32 := 0x00000023.
Lemma F_50790 : fetch_word Plain.M.loaded_segments (0x50790 : word) = Some W_50790.
Proof. vm_refl. Qed.
Lemma D_50790 : decode_any W_50790 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50794 : bv 32 := 0x00100513.
Lemma F_50794 : fetch_word Plain.M.loaded_segments (0x50794 : word) = Some W_50794.
Proof. vm_refl. Qed.
Lemma D_50794 : decode_any W_50794 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50798 : bv 32 := 0x00a90123.
Lemma F_50798 : fetch_word Plain.M.loaded_segments (0x50798 : word) = Some W_50798.
Proof. vm_refl. Qed.
Lemma D_50798 : decode_any W_50798 = Some (Store SZ1 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5079c : bv 32 := 0x17813083.
Lemma F_5079c : fetch_word Plain.M.loaded_segments (0x5079c : word) = Some W_5079c.
Proof. vm_refl. Qed.
Lemma D_5079c : decode_any W_5079c = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507a0 : bv 32 := 0x17013403.
Lemma F_507a0 : fetch_word Plain.M.loaded_segments (0x507a0 : word) = Some W_507a0.
Proof. vm_refl. Qed.
Lemma D_507a0 : decode_any W_507a0 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507a4 : bv 32 := 0x16813483.
Lemma F_507a4 : fetch_word Plain.M.loaded_segments (0x507a4 : word) = Some W_507a4.
Proof. vm_refl. Qed.
Lemma D_507a4 : decode_any W_507a4 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507a8 : bv 32 := 0x16013903.
Lemma F_507a8 : fetch_word Plain.M.loaded_segments (0x507a8 : word) = Some W_507a8.
Proof. vm_refl. Qed.
Lemma D_507a8 : decode_any W_507a8 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507ac : bv 32 := 0x18010113.
Lemma F_507ac : fetch_word Plain.M.loaded_segments (0x507ac : word) = Some W_507ac.
Proof. vm_refl. Qed.
Lemma D_507ac : decode_any W_507ac = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507b0 : bv 32 := 0x00008067.
Lemma F_507b0 : fetch_word Plain.M.loaded_segments (0x507b0 : word) = Some W_507b0.
Proof. vm_refl. Qed.
Lemma D_507b0 : decode_any W_507b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507b4 : bv 32 := 0xfe010113.
Lemma F_507b4 : fetch_word Plain.M.loaded_segments (0x507b4 : word) = Some W_507b4.
Proof. vm_refl. Qed.
Lemma D_507b4 : decode_any W_507b4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507b8 : bv 32 := 0x00113c23.
Lemma F_507b8 : fetch_word Plain.M.loaded_segments (0x507b8 : word) = Some W_507b8.
Proof. vm_refl. Qed.
Lemma D_507b8 : decode_any W_507b8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507bc : bv 32 := 0x00813823.
Lemma F_507bc : fetch_word Plain.M.loaded_segments (0x507bc : word) = Some W_507bc.
Proof. vm_refl. Qed.
Lemma D_507bc : decode_any W_507bc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507c0 : bv 32 := 0x00913423.
Lemma F_507c0 : fetch_word Plain.M.loaded_segments (0x507c0 : word) = Some W_507c0.
Proof. vm_refl. Qed.
Lemma D_507c0 : decode_any W_507c0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507c4 : bv 32 := 0xdc1ff0ef.
Lemma F_507c4 : fetch_word Plain.M.loaded_segments (0x507c4 : word) = Some W_507c4.
Proof. vm_refl. Qed.
Lemma D_507c4 : decode_any W_507c4 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507c8 : bv 32 := 0x00013517.
Lemma F_507c8 : fetch_word Plain.M.loaded_segments (0x507c8 : word) = Some W_507c8.
Proof. vm_refl. Qed.
Lemma D_507c8 : decode_any W_507c8 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507cc : bv 32 := 0x00013597.
Lemma F_507cc : fetch_word Plain.M.loaded_segments (0x507cc : word) = Some W_507cc.
Proof. vm_refl. Qed.
Lemma D_507cc : decode_any W_507cc = Some (Auipc 11 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507d0 : bv 32 := 0x5c853403.
Lemma F_507d0 : fetch_word Plain.M.loaded_segments (0x507d0 : word) = Some W_507d0.
Proof. vm_refl. Qed.
Lemma D_507d0 : decode_any W_507d0 = Some (Load SZ8 true 8 10 1480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507d4 : bv 32 := 0x5cc5b483.
Lemma F_507d4 : fetch_word Plain.M.loaded_segments (0x507d4 : word) = Some W_507d4.
Proof. vm_refl. Qed.
Lemma D_507d4 : decode_any W_507d4 = Some (Load SZ8 true 9 11 1484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507d8 : bv 32 := 0x0084fa63.
Lemma F_507d8 : fetch_word Plain.M.loaded_segments (0x507d8 : word) = Some W_507d8.
Proof. vm_refl. Qed.
Lemma D_507d8 : decode_any W_507d8 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507dc : bv 32 := 0x0004b503.
Lemma F_507dc : fetch_word Plain.M.loaded_segments (0x507dc : word) = Some W_507dc.
Proof. vm_refl. Qed.
Lemma D_507dc : decode_any W_507dc = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507e0 : bv 32 := 0x000500e7.
Lemma F_507e0 : fetch_word Plain.M.loaded_segments (0x507e0 : word) = Some W_507e0.
Proof. vm_refl. Qed.
Lemma D_507e0 : decode_any W_507e0 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507e4 : bv 32 := 0x00848493.
Lemma F_507e4 : fetch_word Plain.M.loaded_segments (0x507e4 : word) = Some W_507e4.
Proof. vm_refl. Qed.
Lemma D_507e4 : decode_any W_507e4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507e8 : bv 32 := 0xfe84eae3.
Lemma F_507e8 : fetch_word Plain.M.loaded_segments (0x507e8 : word) = Some W_507e8.
Proof. vm_refl. Qed.
Lemma D_507e8 : decode_any W_507e8 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507ec : bv 32 := 0x01813083.
Lemma F_507ec : fetch_word Plain.M.loaded_segments (0x507ec : word) = Some W_507ec.
Proof. vm_refl. Qed.
Lemma D_507ec : decode_any W_507ec = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507f0 : bv 32 := 0x01013403.
Lemma F_507f0 : fetch_word Plain.M.loaded_segments (0x507f0 : word) = Some W_507f0.
Proof. vm_refl. Qed.
Lemma D_507f0 : decode_any W_507f0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507f4 : bv 32 := 0x00813483.
Lemma F_507f4 : fetch_word Plain.M.loaded_segments (0x507f4 : word) = Some W_507f4.
Proof. vm_refl. Qed.
Lemma D_507f4 : decode_any W_507f4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507f8 : bv 32 := 0x02010113.
Lemma F_507f8 : fetch_word Plain.M.loaded_segments (0x507f8 : word) = Some W_507f8.
Proof. vm_refl. Qed.
Lemma D_507f8 : decode_any W_507f8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_507fc : bv 32 := 0x00008067.
Lemma F_507fc : fetch_word Plain.M.loaded_segments (0x507fc : word) = Some W_507fc.
Proof. vm_refl. Qed.
Lemma D_507fc : decode_any W_507fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50800 : bv 32 := 0xfe010113.
Lemma F_50800 : fetch_word Plain.M.loaded_segments (0x50800 : word) = Some W_50800.
Proof. vm_refl. Qed.
Lemma D_50800 : decode_any W_50800 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50804 : bv 32 := 0x00113c23.
Lemma F_50804 : fetch_word Plain.M.loaded_segments (0x50804 : word) = Some W_50804.
Proof. vm_refl. Qed.
Lemma D_50804 : decode_any W_50804 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50808 : bv 32 := 0x00813823.
Lemma F_50808 : fetch_word Plain.M.loaded_segments (0x50808 : word) = Some W_50808.
Proof. vm_refl. Qed.
Lemma D_50808 : decode_any W_50808 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5080c : bv 32 := 0x00913423.
Lemma F_5080c : fetch_word Plain.M.loaded_segments (0x5080c : word) = Some W_5080c.
Proof. vm_refl. Qed.
Lemma D_5080c : decode_any W_5080c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50810 : bv 32 := 0x01213023.
Lemma F_50810 : fetch_word Plain.M.loaded_segments (0x50810 : word) = Some W_50810.
Proof. vm_refl. Qed.
Lemma D_50810 : decode_any W_50810 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50814 : bv 32 := 0x00060413.
Lemma F_50814 : fetch_word Plain.M.loaded_segments (0x50814 : word) = Some W_50814.
Proof. vm_refl. Qed.
Lemma D_50814 : decode_any W_50814 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50818 : bv 32 := 0x00058493.
Lemma F_50818 : fetch_word Plain.M.loaded_segments (0x50818 : word) = Some W_50818.
Proof. vm_refl. Qed.
Lemma D_50818 : decode_any W_50818 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5081c : bv 32 := 0x00050913.
Lemma F_5081c : fetch_word Plain.M.loaded_segments (0x5081c : word) = Some W_5081c.
Proof. vm_refl. Qed.
Lemma D_5081c : decode_any W_5081c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50820 : bv 32 := 0x00063583.
Lemma F_50820 : fetch_word Plain.M.loaded_segments (0x50820 : word) = Some W_50820.
Proof. vm_refl. Qed.
Lemma D_50820 : decode_any W_50820 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50824 : bv 32 := 0x00349513.
Lemma F_50824 : fetch_word Plain.M.loaded_segments (0x50824 : word) = Some W_50824.
Proof. vm_refl. Qed.
Lemma D_50824 : decode_any W_50824 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50828 : bv 32 := 0x00a60533.
Lemma F_50828 : fetch_word Plain.M.loaded_segments (0x50828 : word) = Some W_50828.
Proof. vm_refl. Qed.
Lemma D_50828 : decode_any W_50828 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5082c : bv 32 := 0x00850513.
Lemma F_5082c : fetch_word Plain.M.loaded_segments (0x5082c : word) = Some W_5082c.
Proof. vm_refl. Qed.
Lemma D_5082c : decode_any W_5082c = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50830 : bv 32 := 0xd59ff0ef.
Lemma F_50830 : fetch_word Plain.M.loaded_segments (0x50830 : word) = Some W_50830.
Proof. vm_refl. Qed.
Lemma D_50830 : decode_any W_50830 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50834 : bv 32 := 0x00000517.
Lemma F_50834 : fetch_word Plain.M.loaded_segments (0x50834 : word) = Some W_50834.
Proof. vm_refl. Qed.
Lemma D_50834 : decode_any W_50834 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50838 : bv 32 := 0x02c50313.
Lemma F_50838 : fetch_word Plain.M.loaded_segments (0x50838 : word) = Some W_50838.
Proof. vm_refl. Qed.
Lemma D_50838 : decode_any W_50838 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5083c : bv 32 := 0x00090513.
Lemma F_5083c : fetch_word Plain.M.loaded_segments (0x5083c : word) = Some W_5083c.
Proof. vm_refl. Qed.
Lemma D_5083c : decode_any W_5083c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50840 : bv 32 := 0x00048593.
Lemma F_50840 : fetch_word Plain.M.loaded_segments (0x50840 : word) = Some W_50840.
Proof. vm_refl. Qed.
Lemma D_50840 : decode_any W_50840 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50844 : bv 32 := 0x00040613.
Lemma F_50844 : fetch_word Plain.M.loaded_segments (0x50844 : word) = Some W_50844.
Proof. vm_refl. Qed.
Lemma D_50844 : decode_any W_50844 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50848 : bv 32 := 0x01813083.
Lemma F_50848 : fetch_word Plain.M.loaded_segments (0x50848 : word) = Some W_50848.
Proof. vm_refl. Qed.
Lemma D_50848 : decode_any W_50848 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5084c : bv 32 := 0x01013403.
Lemma F_5084c : fetch_word Plain.M.loaded_segments (0x5084c : word) = Some W_5084c.
Proof. vm_refl. Qed.
Lemma D_5084c : decode_any W_5084c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50850 : bv 32 := 0x00813483.
Lemma F_50850 : fetch_word Plain.M.loaded_segments (0x50850 : word) = Some W_50850.
Proof. vm_refl. Qed.
Lemma D_50850 : decode_any W_50850 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50854 : bv 32 := 0x00013903.
Lemma F_50854 : fetch_word Plain.M.loaded_segments (0x50854 : word) = Some W_50854.
Proof. vm_refl. Qed.
Lemma D_50854 : decode_any W_50854 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50858 : bv 32 := 0x02010113.
Lemma F_50858 : fetch_word Plain.M.loaded_segments (0x50858 : word) = Some W_50858.
Proof. vm_refl. Qed.
Lemma D_50858 : decode_any W_50858 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5085c : bv 32 := 0x00030067.
Lemma F_5085c : fetch_word Plain.M.loaded_segments (0x5085c : word) = Some W_5085c.
Proof. vm_refl. Qed.
Lemma D_5085c : decode_any W_5085c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50860 : bv 32 := 0xfd010113.
Lemma F_50860 : fetch_word Plain.M.loaded_segments (0x50860 : word) = Some W_50860.
Proof. vm_refl. Qed.
Lemma D_50860 : decode_any W_50860 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50864 : bv 32 := 0x02113423.
Lemma F_50864 : fetch_word Plain.M.loaded_segments (0x50864 : word) = Some W_50864.
Proof. vm_refl. Qed.
Lemma D_50864 : decode_any W_50864 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50868 : bv 32 := 0x02813023.
Lemma F_50868 : fetch_word Plain.M.loaded_segments (0x50868 : word) = Some W_50868.
Proof. vm_refl. Qed.
Lemma D_50868 : decode_any W_50868 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5086c : bv 32 := 0x00913c23.
Lemma F_5086c : fetch_word Plain.M.loaded_segments (0x5086c : word) = Some W_5086c.
Proof. vm_refl. Qed.
Lemma D_5086c : decode_any W_5086c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50870 : bv 32 := 0x01213823.
Lemma F_50870 : fetch_word Plain.M.loaded_segments (0x50870 : word) = Some W_50870.
Proof. vm_refl. Qed.
Lemma D_50870 : decode_any W_50870 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50874 : bv 32 := 0x01313423.
Lemma F_50874 : fetch_word Plain.M.loaded_segments (0x50874 : word) = Some W_50874.
Proof. vm_refl. Qed.
Lemma D_50874 : decode_any W_50874 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50878 : bv 32 := 0x00060413.
Lemma F_50878 : fetch_word Plain.M.loaded_segments (0x50878 : word) = Some W_50878.
Proof. vm_refl. Qed.
Lemma D_50878 : decode_any W_50878 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5087c : bv 32 := 0x00058493.
Lemma F_5087c : fetch_word Plain.M.loaded_segments (0x5087c : word) = Some W_5087c.
Proof. vm_refl. Qed.
Lemma D_5087c : decode_any W_5087c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50880 : bv 32 := 0x00050913.
Lemma F_50880 : fetch_word Plain.M.loaded_segments (0x50880 : word) = Some W_50880.
Proof. vm_refl. Qed.
Lemma D_50880 : decode_any W_50880 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50884 : bv 32 := 0x00359513.
Lemma F_50884 : fetch_word Plain.M.loaded_segments (0x50884 : word) = Some W_50884.
Proof. vm_refl. Qed.
Lemma D_50884 : decode_any W_50884 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50888 : bv 32 := 0x00a60533.
Lemma F_50888 : fetch_word Plain.M.loaded_segments (0x50888 : word) = Some W_50888.
Proof. vm_refl. Qed.
Lemma D_50888 : decode_any W_50888 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5088c : bv 32 := 0x00850993.
Lemma F_5088c : fetch_word Plain.M.loaded_segments (0x5088c : word) = Some W_5088c.
Proof. vm_refl. Qed.
Lemma D_5088c : decode_any W_5088c = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50890 : bv 32 := 0xf25ff0ef.
Lemma F_50890 : fetch_word Plain.M.loaded_segments (0x50890 : word) = Some W_50890.
Proof. vm_refl. Qed.
Lemma D_50890 : decode_any W_50890 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50894 : bv 32 := 0x00048513.
Lemma F_50894 : fetch_word Plain.M.loaded_segments (0x50894 : word) = Some W_50894.
Proof. vm_refl. Qed.
Lemma D_50894 : decode_any W_50894 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50898 : bv 32 := 0x00040593.
Lemma F_50898 : fetch_word Plain.M.loaded_segments (0x50898 : word) = Some W_50898.
Proof. vm_refl. Qed.
Lemma D_50898 : decode_any W_50898 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5089c : bv 32 := 0x00098613.
Lemma F_5089c : fetch_word Plain.M.loaded_segments (0x5089c : word) = Some W_5089c.
Proof. vm_refl. Qed.
Lemma D_5089c : decode_any W_5089c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_508a0 : bv 32 := 0x000900e7.
Lemma F_508a0 : fetch_word Plain.M.loaded_segments (0x508a0 : word) = Some W_508a0.
Proof. vm_refl. Qed.
Lemma D_508a0 : decode_any W_508a0 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_508a4 : bv 32 := 0x584000ef.
Lemma F_508a4 : fetch_word Plain.M.loaded_segments (0x508a4 : word) = Some W_508a4.
Proof. vm_refl. Qed.
Lemma D_508a4 : decode_any W_508a4 = Some (Jal 1 1412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b58 : bv 32 := 0x00020513.
Lemma F_50b58 : fetch_word Plain.M.loaded_segments (0x50b58 : word) = Some W_50b58.
Proof. vm_refl. Qed.
Lemma D_50b58 : decode_any W_50b58 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b5c : bv 32 := 0xf5c50513.
Lemma F_50b5c : fetch_word Plain.M.loaded_segments (0x50b5c : word) = Some W_50b5c.
Proof. vm_refl. Qed.
Lemma D_50b5c : decode_any W_50b5c = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b60 : bv 32 := 0x00008067.
Lemma F_50b60 : fetch_word Plain.M.loaded_segments (0x50b60 : word) = Some W_50b60.
Proof. vm_refl. Qed.
Lemma D_50b60 : decode_any W_50b60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b64 : bv 32 := 0xfd010113.
Lemma F_50b64 : fetch_word Plain.M.loaded_segments (0x50b64 : word) = Some W_50b64.
Proof. vm_refl. Qed.
Lemma D_50b64 : decode_any W_50b64 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b68 : bv 32 := 0x02113423.
Lemma F_50b68 : fetch_word Plain.M.loaded_segments (0x50b68 : word) = Some W_50b68.
Proof. vm_refl. Qed.
Lemma D_50b68 : decode_any W_50b68 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b6c : bv 32 := 0x00600513.
Lemma F_50b6c : fetch_word Plain.M.loaded_segments (0x50b6c : word) = Some W_50b6c.
Proof. vm_refl. Qed.
Lemma D_50b6c : decode_any W_50b6c = Some (OpImm ALU_ADD 10 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b70 : bv 32 := 0x265020ef.
Lemma F_50b70 : fetch_word Plain.M.loaded_segments (0x50b70 : word) = Some W_50b70.
Proof. vm_refl. Qed.
Lemma D_50b70 : decode_any W_50b70 = Some (Jal 1 10852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b74 : bv 32 := 0x00000513.
Lemma F_50b74 : fetch_word Plain.M.loaded_segments (0x50b74 : word) = Some W_50b74.
Proof. vm_refl. Qed.
Lemma D_50b74 : decode_any W_50b74 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b78 : bv 32 := 0x201020ef.
Lemma F_50b78 : fetch_word Plain.M.loaded_segments (0x50b78 : word) = Some W_50b78.
Proof. vm_refl. Qed.
Lemma D_50b78 : decode_any W_50b78 = Some (Jal 1 10752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b7c : bv 32 := 0x00045517.
Lemma F_50b7c : fetch_word Plain.M.loaded_segments (0x50b7c : word) = Some W_50b7c.
Proof. vm_refl. Qed.
Lemma D_50b7c : decode_any W_50b7c = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b80 : bv 32 := 0x09450513.
Lemma F_50b80 : fetch_word Plain.M.loaded_segments (0x50b80 : word) = Some W_50b80.
Proof. vm_refl. Qed.
Lemma D_50b80 : decode_any W_50b80 = Some (OpImm ALU_ADD 10 10 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b84 : bv 32 := 0x7d90d0ef.
Lemma F_50b84 : fetch_word Plain.M.loaded_segments (0x50b84 : word) = Some W_50b84.
Proof. vm_refl. Qed.
Lemma D_50b84 : decode_any W_50b84 = Some (Jal 1 57304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b88 : bv 32 := 0x00000613.
Lemma F_50b88 : fetch_word Plain.M.loaded_segments (0x50b88 : word) = Some W_50b88.
Proof. vm_refl. Qed.
Lemma D_50b88 : decode_any W_50b88 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b8c : bv 32 := 0x00013423.
Lemma F_50b8c : fetch_word Plain.M.loaded_segments (0x50b8c : word) = Some W_50b8c.
Proof. vm_refl. Qed.
Lemma D_50b8c : decode_any W_50b8c = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b90 : bv 32 := 0x00013823.
Lemma F_50b90 : fetch_word Plain.M.loaded_segments (0x50b90 : word) = Some W_50b90.
Proof. vm_refl. Qed.
Lemma D_50b90 : decode_any W_50b90 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b94 : bv 32 := 0x00013c23.
Lemma F_50b94 : fetch_word Plain.M.loaded_segments (0x50b94 : word) = Some W_50b94.
Proof. vm_refl. Qed.
Lemma D_50b94 : decode_any W_50b94 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b98 : bv 32 := 0x02013023.
Lemma F_50b98 : fetch_word Plain.M.loaded_segments (0x50b98 : word) = Some W_50b98.
Proof. vm_refl. Qed.
Lemma D_50b98 : decode_any W_50b98 = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50b9c : bv 32 := 0x08600893.
Lemma F_50b9c : fetch_word Plain.M.loaded_segments (0x50b9c : word) = Some W_50b9c.
Proof. vm_refl. Qed.
Lemma D_50b9c : decode_any W_50b9c = Some (OpImm ALU_ADD 17 0 134, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ba0 : bv 32 := 0x00600513.
Lemma F_50ba0 : fetch_word Plain.M.loaded_segments (0x50ba0 : word) = Some W_50ba0.
Proof. vm_refl. Qed.
Lemma D_50ba0 : decode_any W_50ba0 = Some (OpImm ALU_ADD 10 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ba4 : bv 32 := 0x00810593.
Lemma F_50ba4 : fetch_word Plain.M.loaded_segments (0x50ba4 : word) = Some W_50ba4.
Proof. vm_refl. Qed.
Lemma D_50ba4 : decode_any W_50ba4 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ba8 : bv 32 := 0x00800693.
Lemma F_50ba8 : fetch_word Plain.M.loaded_segments (0x50ba8 : word) = Some W_50ba8.
Proof. vm_refl. Qed.
Lemma D_50ba8 : decode_any W_50ba8 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bac : bv 32 := 0x00000073.
Lemma F_50bac : fetch_word Plain.M.loaded_segments (0x50bac : word) = Some W_50bac.
Proof. vm_refl. Qed.
Lemma D_50bac : decode_any W_50bac = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_50bac : is_ecall W_50bac = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_50bb0 : bv 32 := 0x00020513.
Lemma F_50bb0 : fetch_word Plain.M.loaded_segments (0x50bb0 : word) = Some W_50bb0.
Proof. vm_refl. Qed.
Lemma D_50bb0 : decode_any W_50bb0 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bb4 : bv 32 := 0xf5852503.
Lemma F_50bb4 : fetch_word Plain.M.loaded_segments (0x50bb4 : word) = Some W_50bb4.
Proof. vm_refl. Qed.
Lemma D_50bb4 : decode_any W_50bb4 = Some (Load SZ4 true 10 10 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bb8 : bv 32 := 0x02000613.
Lemma F_50bb8 : fetch_word Plain.M.loaded_segments (0x50bb8 : word) = Some W_50bb8.
Proof. vm_refl. Qed.
Lemma D_50bb8 : decode_any W_50bb8 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bbc : bv 32 := 0x08200893.
Lemma F_50bbc : fetch_word Plain.M.loaded_segments (0x50bbc : word) = Some W_50bbc.
Proof. vm_refl. Qed.
Lemma D_50bbc : decode_any W_50bbc = Some (OpImm ALU_ADD 17 0 130, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bc0 : bv 32 := 0x00600593.
Lemma F_50bc0 : fetch_word Plain.M.loaded_segments (0x50bc0 : word) = Some W_50bc0.
Proof. vm_refl. Qed.
Lemma D_50bc0 : decode_any W_50bc0 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bc4 : bv 32 := 0x00000073.
Lemma F_50bc4 : fetch_word Plain.M.loaded_segments (0x50bc4 : word) = Some W_50bc4.
Proof. vm_refl. Qed.
Lemma D_50bc4 : decode_any W_50bc4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_50bc4 : is_ecall W_50bc4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_50bc8 : bv 32 := 0x00c13023.
Lemma F_50bc8 : fetch_word Plain.M.loaded_segments (0x50bc8 : word) = Some W_50bc8.
Proof. vm_refl. Qed.
Lemma D_50bc8 : decode_any W_50bc8 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bcc : bv 32 := 0x08700893.
Lemma F_50bcc : fetch_word Plain.M.loaded_segments (0x50bcc : word) = Some W_50bcc.
Proof. vm_refl. Qed.
Lemma D_50bcc : decode_any W_50bcc = Some (OpImm ALU_ADD 17 0 135, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bd0 : bv 32 := 0x00010593.
Lemma F_50bd0 : fetch_word Plain.M.loaded_segments (0x50bd0 : word) = Some W_50bd0.
Proof. vm_refl. Qed.
Lemma D_50bd0 : decode_any W_50bd0 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bd4 : bv 32 := 0x00100513.
Lemma F_50bd4 : fetch_word Plain.M.loaded_segments (0x50bd4 : word) = Some W_50bd4.
Proof. vm_refl. Qed.
Lemma D_50bd4 : decode_any W_50bd4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bd8 : bv 32 := 0x00800693.
Lemma F_50bd8 : fetch_word Plain.M.loaded_segments (0x50bd8 : word) = Some W_50bd8.
Proof. vm_refl. Qed.
Lemma D_50bd8 : decode_any W_50bd8 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bdc : bv 32 := 0x00000613.
Lemma F_50bdc : fetch_word Plain.M.loaded_segments (0x50bdc : word) = Some W_50bdc.
Proof. vm_refl. Qed.
Lemma D_50bdc : decode_any W_50bdc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50be0 : bv 32 := 0x00000073.
Lemma F_50be0 : fetch_word Plain.M.loaded_segments (0x50be0 : word) = Some W_50be0.
Proof. vm_refl. Qed.
Lemma D_50be0 : decode_any W_50be0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_50be0 : is_ecall W_50be0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_50be4 : bv 32 := 0x00000023.
Lemma F_50be4 : fetch_word Plain.M.loaded_segments (0x50be4 : word) = Some W_50be4.
Proof. vm_refl. Qed.
Lemma D_50be4 : decode_any W_50be4 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50be8 : bv 32 := 0x00900513.
Lemma F_50be8 : fetch_word Plain.M.loaded_segments (0x50be8 : word) = Some W_50be8.
Proof. vm_refl. Qed.
Lemma D_50be8 : decode_any W_50be8 = Some (OpImm ALU_ADD 10 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bec : bv 32 := 0x1e9020ef.
Lemma F_50bec : fetch_word Plain.M.loaded_segments (0x50bec : word) = Some W_50bec.
Proof. vm_refl. Qed.
Lemma D_50bec : decode_any W_50bec = Some (Jal 1 10728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bf0 : bv 32 := 0x07f00513.
Lemma F_50bf0 : fetch_word Plain.M.loaded_segments (0x50bf0 : word) = Some W_50bf0.
Proof. vm_refl. Qed.
Lemma D_50bf0 : decode_any W_50bf0 = Some (OpImm ALU_ADD 10 0 127, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bf4 : bv 32 := 0x004000ef.
Lemma F_50bf4 : fetch_word Plain.M.loaded_segments (0x50bf4 : word) = Some W_50bf4.
Proof. vm_refl. Qed.
Lemma D_50bf4 : decode_any W_50bf4 = Some (Jal 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bf8 : bv 32 := 0x00050593.
Lemma F_50bf8 : fetch_word Plain.M.loaded_segments (0x50bf8 : word) = Some W_50bf8.
Proof. vm_refl. Qed.
Lemma D_50bf8 : decode_any W_50bf8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50bfc : bv 32 := 0x05e00893.
Lemma F_50bfc : fetch_word Plain.M.loaded_segments (0x50bfc : word) = Some W_50bfc.
Proof. vm_refl. Qed.
Lemma D_50bfc : decode_any W_50bfc = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c00 : bv 32 := 0x00000073.
Lemma F_50c00 : fetch_word Plain.M.loaded_segments (0x50c00 : word) = Some W_50c00.
Proof. vm_refl. Qed.
Lemma D_50c00 : decode_any W_50c00 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_50c00 : is_ecall W_50c00 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_50c04 : bv 32 := 0x05d00893.
Lemma F_50c04 : fetch_word Plain.M.loaded_segments (0x50c04 : word) = Some W_50c04.
Proof. vm_refl. Qed.
Lemma D_50c04 : decode_any W_50c04 = Some (OpImm ALU_ADD 17 0 93, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c08 : bv 32 := 0x00058513.
Lemma F_50c08 : fetch_word Plain.M.loaded_segments (0x50c08 : word) = Some W_50c08.
Proof. vm_refl. Qed.
Lemma D_50c08 : decode_any W_50c08 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c0c : bv 32 := 0x00000073.
Lemma F_50c0c : fetch_word Plain.M.loaded_segments (0x50c0c : word) = Some W_50c0c.
Proof. vm_refl. Qed.
Lemma D_50c0c : decode_any W_50c0c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_50c0c : is_ecall W_50c0c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_50c10 : bv 32 := 0xff9ff06f.
Lemma F_50c10 : fetch_word Plain.M.loaded_segments (0x50c10 : word) = Some W_50c10.
Proof. vm_refl. Qed.
Lemma D_50c10 : decode_any W_50c10 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c14 : bv 32 := 0xff010113.
Lemma F_50c14 : fetch_word Plain.M.loaded_segments (0x50c14 : word) = Some W_50c14.
Proof. vm_refl. Qed.
Lemma D_50c14 : decode_any W_50c14 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c18 : bv 32 := 0x00113423.
Lemma F_50c18 : fetch_word Plain.M.loaded_segments (0x50c18 : word) = Some W_50c18.
Proof. vm_refl. Qed.
Lemma D_50c18 : decode_any W_50c18 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c1c : bv 32 := 0x00068713.
Lemma F_50c1c : fetch_word Plain.M.loaded_segments (0x50c1c : word) = Some W_50c1c.
Proof. vm_refl. Qed.
Lemma D_50c1c : decode_any W_50c1c = Some (OpImm ALU_ADD 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c20 : bv 32 := 0x00060793.
Lemma F_50c20 : fetch_word Plain.M.loaded_segments (0x50c20 : word) = Some W_50c20.
Proof. vm_refl. Qed.
Lemma D_50c20 : decode_any W_50c20 = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c24 : bv 32 := 0x00058693.
Lemma F_50c24 : fetch_word Plain.M.loaded_segments (0x50c24 : word) = Some W_50c24.
Proof. vm_refl. Qed.
Lemma D_50c24 : decode_any W_50c24 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c28 : bv 32 := 0x00050613.
Lemma F_50c28 : fetch_word Plain.M.loaded_segments (0x50c28 : word) = Some W_50c28.
Proof. vm_refl. Qed.
Lemma D_50c28 : decode_any W_50c28 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c2c : bv 32 := 0x00014517.
Lemma F_50c2c : fetch_word Plain.M.loaded_segments (0x50c2c : word) = Some W_50c2c.
Proof. vm_refl. Qed.
Lemma D_50c2c : decode_any W_50c2c = Some (Auipc 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c30 : bv 32 := 0xfffc0597.
Lemma F_50c30 : fetch_word Plain.M.loaded_segments (0x50c30 : word) = Some W_50c30.
Proof. vm_refl. Qed.
Lemma D_50c30 : decode_any W_50c30 = Some (Auipc 11 1048512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c34 : bv 32 := 0x1f450513.
Lemma F_50c34 : fetch_word Plain.M.loaded_segments (0x50c34 : word) = Some W_50c34.
Proof. vm_refl. Qed.
Lemma D_50c34 : decode_any W_50c34 = Some (OpImm ALU_ADD 10 10 500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c38 : bv 32 := 0x5f358593.
Lemma F_50c38 : fetch_word Plain.M.loaded_segments (0x50c38 : word) = Some W_50c38.
Proof. vm_refl. Qed.
Lemma D_50c38 : decode_any W_50c38 = Some (OpImm ALU_ADD 11 11 1523, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c3c : bv 32 := 0x4dd020ef.
Lemma F_50c3c : fetch_word Plain.M.loaded_segments (0x50c3c : word) = Some W_50c3c.
Proof. vm_refl. Qed.
Lemma D_50c3c : decode_any W_50c3c = Some (Jal 1 11484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c40 : bv 32 := 0xf25ff0ef.
Lemma F_50c40 : fetch_word Plain.M.loaded_segments (0x50c40 : word) = Some W_50c40.
Proof. vm_refl. Qed.
Lemma D_50c40 : decode_any W_50c40 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c44 : bv 32 := 0xfd010113.
Lemma F_50c44 : fetch_word Plain.M.loaded_segments (0x50c44 : word) = Some W_50c44.
Proof. vm_refl. Qed.
Lemma D_50c44 : decode_any W_50c44 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c48 : bv 32 := 0x02113423.
Lemma F_50c48 : fetch_word Plain.M.loaded_segments (0x50c48 : word) = Some W_50c48.
Proof. vm_refl. Qed.
Lemma D_50c48 : decode_any W_50c48 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c4c : bv 32 := 0x02813023.
Lemma F_50c4c : fetch_word Plain.M.loaded_segments (0x50c4c : word) = Some W_50c4c.
Proof. vm_refl. Qed.
Lemma D_50c4c : decode_any W_50c4c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c50 : bv 32 := 0x00913c23.
Lemma F_50c50 : fetch_word Plain.M.loaded_segments (0x50c50 : word) = Some W_50c50.
Proof. vm_refl. Qed.
Lemma D_50c50 : decode_any W_50c50 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c54 : bv 32 := 0x01213823.
Lemma F_50c54 : fetch_word Plain.M.loaded_segments (0x50c54 : word) = Some W_50c54.
Proof. vm_refl. Qed.
Lemma D_50c54 : decode_any W_50c54 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c58 : bv 32 := 0x01313423.
Lemma F_50c58 : fetch_word Plain.M.loaded_segments (0x50c58 : word) = Some W_50c58.
Proof. vm_refl. Qed.
Lemma D_50c58 : decode_any W_50c58 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c5c : bv 32 := 0x00045517.
Lemma F_50c5c : fetch_word Plain.M.loaded_segments (0x50c5c : word) = Some W_50c5c.
Proof. vm_refl. Qed.
Lemma D_50c5c : decode_any W_50c5c = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c60 : bv 32 := 0xfbc50913.
Lemma F_50c60 : fetch_word Plain.M.loaded_segments (0x50c60 : word) = Some W_50c60.
Proof. vm_refl. Qed.
Lemma D_50c60 : decode_any W_50c60 = Some (OpImm ALU_ADD 18 10 4028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c64 : bv 32 := 0x00490413.
Lemma F_50c64 : fetch_word Plain.M.loaded_segments (0x50c64 : word) = Some W_50c64.
Proof. vm_refl. Qed.
Lemma D_50c64 : decode_any W_50c64 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c68 : bv 32 := 0x00040513.
Lemma F_50c68 : fetch_word Plain.M.loaded_segments (0x50c68 : word) = Some W_50c68.
Proof. vm_refl. Qed.
Lemma D_50c68 : decode_any W_50c68 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c6c : bv 32 := 0x6f10d0ef.
Lemma F_50c6c : fetch_word Plain.M.loaded_segments (0x50c6c : word) = Some W_50c6c.
Proof. vm_refl. Qed.
Lemma D_50c6c : decode_any W_50c6c = Some (Jal 1 57072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c70 : bv 32 := 0x01093503.
Lemma F_50c70 : fetch_word Plain.M.loaded_segments (0x50c70 : word) = Some W_50c70.
Proof. vm_refl. Qed.
Lemma D_50c70 : decode_any W_50c70 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c74 : bv 32 := 0x06050863.
Lemma F_50c74 : fetch_word Plain.M.loaded_segments (0x50c74 : word) = Some W_50c74.
Proof. vm_refl. Qed.
Lemma D_50c74 : decode_any W_50c74 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c78 : bv 32 := 0x00892583.
Lemma F_50c78 : fetch_word Plain.M.loaded_segments (0x50c78 : word) = Some W_50c78.
Proof. vm_refl. Qed.
Lemma D_50c78 : decode_any W_50c78 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c7c : bv 32 := 0x0180006f.
Lemma F_50c7c : fetch_word Plain.M.loaded_segments (0x50c7c : word) = Some W_50c7c.
Proof. vm_refl. Qed.
Lemma D_50c7c : decode_any W_50c7c = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c80 : bv 32 := 0x00053503.
Lemma F_50c80 : fetch_word Plain.M.loaded_segments (0x50c80 : word) = Some W_50c80.
Proof. vm_refl. Qed.
Lemma D_50c80 : decode_any W_50c80 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c84 : bv 32 := 0x02000593.
Lemma F_50c84 : fetch_word Plain.M.loaded_segments (0x50c84 : word) = Some W_50c84.
Proof. vm_refl. Qed.
Lemma D_50c84 : decode_any W_50c84 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c88 : bv 32 := 0x00b92423.
Lemma F_50c88 : fetch_word Plain.M.loaded_segments (0x50c88 : word) = Some W_50c88.
Proof. vm_refl. Qed.
Lemma D_50c88 : decode_any W_50c88 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c8c : bv 32 := 0x00a93823.
Lemma F_50c8c : fetch_word Plain.M.loaded_segments (0x50c8c : word) = Some W_50c8c.
Proof. vm_refl. Qed.
Lemma D_50c8c : decode_any W_50c8c = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c90 : bv 32 := 0x04050a63.
Lemma F_50c90 : fetch_word Plain.M.loaded_segments (0x50c90 : word) = Some W_50c90.
Proof. vm_refl. Qed.
Lemma D_50c90 : decode_any W_50c90 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c94 : bv 32 := 0xfff5861b.
Lemma F_50c94 : fetch_word Plain.M.loaded_segments (0x50c94 : word) = Some W_50c94.
Proof. vm_refl. Qed.
Lemma D_50c94 : decode_any W_50c94 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c98 : bv 32 := 0x00c92423.
Lemma F_50c98 : fetch_word Plain.M.loaded_segments (0x50c98 : word) = Some W_50c98.
Proof. vm_refl. Qed.
Lemma D_50c98 : decode_any W_50c98 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50c9c : bv 32 := 0xfeb052e3.
Lemma F_50c9c : fetch_word Plain.M.loaded_segments (0x50c9c : word) = Some W_50c9c.
Proof. vm_refl. Qed.
Lemma D_50c9c : decode_any W_50c9c = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ca0 : bv 32 := 0x01093503.
Lemma F_50ca0 : fetch_word Plain.M.loaded_segments (0x50ca0 : word) = Some W_50ca0.
Proof. vm_refl. Qed.
Lemma D_50ca0 : decode_any W_50ca0 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ca4 : bv 32 := 0x00361613.
Lemma F_50ca4 : fetch_word Plain.M.loaded_segments (0x50ca4 : word) = Some W_50ca4.
Proof. vm_refl. Qed.
Lemma D_50ca4 : decode_any W_50ca4 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ca8 : bv 32 := 0x00c50533.
Lemma F_50ca8 : fetch_word Plain.M.loaded_segments (0x50ca8 : word) = Some W_50ca8.
Proof. vm_refl. Qed.
Lemma D_50ca8 : decode_any W_50ca8 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cac : bv 32 := 0x00853983.
Lemma F_50cac : fetch_word Plain.M.loaded_segments (0x50cac : word) = Some W_50cac.
Proof. vm_refl. Qed.
Lemma D_50cac : decode_any W_50cac = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cb0 : bv 32 := 0x10853483.
Lemma F_50cb0 : fetch_word Plain.M.loaded_segments (0x50cb0 : word) = Some W_50cb0.
Proof. vm_refl. Qed.
Lemma D_50cb0 : decode_any W_50cb0 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cb4 : bv 32 := 0x00040513.
Lemma F_50cb4 : fetch_word Plain.M.loaded_segments (0x50cb4 : word) = Some W_50cb4.
Proof. vm_refl. Qed.
Lemma D_50cb4 : decode_any W_50cb4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cb8 : bv 32 := 0x12c0e0ef.
Lemma F_50cb8 : fetch_word Plain.M.loaded_segments (0x50cb8 : word) = Some W_50cb8.
Proof. vm_refl. Qed.
Lemma D_50cb8 : decode_any W_50cb8 = Some (Jal 1 57644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cbc : bv 32 := 0x00048513.
Lemma F_50cbc : fetch_word Plain.M.loaded_segments (0x50cbc : word) = Some W_50cbc.
Proof. vm_refl. Qed.
Lemma D_50cbc : decode_any W_50cbc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cc0 : bv 32 := 0x000980e7.
Lemma F_50cc0 : fetch_word Plain.M.loaded_segments (0x50cc0 : word) = Some W_50cc0.
Proof. vm_refl. Qed.
Lemma D_50cc0 : decode_any W_50cc0 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cc4 : bv 32 := 0x00040513.
Lemma F_50cc4 : fetch_word Plain.M.loaded_segments (0x50cc4 : word) = Some W_50cc4.
Proof. vm_refl. Qed.
Lemma D_50cc4 : decode_any W_50cc4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cc8 : bv 32 := 0x6950d0ef.
Lemma F_50cc8 : fetch_word Plain.M.loaded_segments (0x50cc8 : word) = Some W_50cc8.
Proof. vm_refl. Qed.
Lemma D_50cc8 : decode_any W_50cc8 = Some (Jal 1 56980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ccc : bv 32 := 0x00892503.
Lemma F_50ccc : fetch_word Plain.M.loaded_segments (0x50ccc : word) = Some W_50ccc.
Proof. vm_refl. Qed.
Lemma D_50ccc : decode_any W_50ccc = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cd0 : bv 32 := 0xfff5061b.
Lemma F_50cd0 : fetch_word Plain.M.loaded_segments (0x50cd0 : word) = Some W_50cd0.
Proof. vm_refl. Qed.
Lemma D_50cd0 : decode_any W_50cd0 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cd4 : bv 32 := 0x00c92423.
Lemma F_50cd4 : fetch_word Plain.M.loaded_segments (0x50cd4 : word) = Some W_50cd4.
Proof. vm_refl. Qed.
Lemma D_50cd4 : decode_any W_50cd4 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cd8 : bv 32 := 0xfca044e3.
Lemma F_50cd8 : fetch_word Plain.M.loaded_segments (0x50cd8 : word) = Some W_50cd8.
Proof. vm_refl. Qed.
Lemma D_50cd8 : decode_any W_50cd8 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cdc : bv 32 := 0x01093503.
Lemma F_50cdc : fetch_word Plain.M.loaded_segments (0x50cdc : word) = Some W_50cdc.
Proof. vm_refl. Qed.
Lemma D_50cdc : decode_any W_50cdc = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ce0 : bv 32 := 0xfa1ff06f.
Lemma F_50ce0 : fetch_word Plain.M.loaded_segments (0x50ce0 : word) = Some W_50ce0.
Proof. vm_refl. Qed.
Lemma D_50ce0 : decode_any W_50ce0 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ce4 : bv 32 := 0x00100513.
Lemma F_50ce4 : fetch_word Plain.M.loaded_segments (0x50ce4 : word) = Some W_50ce4.
Proof. vm_refl. Qed.
Lemma D_50ce4 : decode_any W_50ce4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ce8 : bv 32 := 0x00a90023.
Lemma F_50ce8 : fetch_word Plain.M.loaded_segments (0x50ce8 : word) = Some W_50ce8.
Proof. vm_refl. Qed.
Lemma D_50ce8 : decode_any W_50ce8 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cec : bv 32 := 0x00040513.
Lemma F_50cec : fetch_word Plain.M.loaded_segments (0x50cec : word) = Some W_50cec.
Proof. vm_refl. Qed.
Lemma D_50cec : decode_any W_50cec = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cf0 : bv 32 := 0x02813083.
Lemma F_50cf0 : fetch_word Plain.M.loaded_segments (0x50cf0 : word) = Some W_50cf0.
Proof. vm_refl. Qed.
Lemma D_50cf0 : decode_any W_50cf0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cf4 : bv 32 := 0x02013403.
Lemma F_50cf4 : fetch_word Plain.M.loaded_segments (0x50cf4 : word) = Some W_50cf4.
Proof. vm_refl. Qed.
Lemma D_50cf4 : decode_any W_50cf4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cf8 : bv 32 := 0x01813483.
Lemma F_50cf8 : fetch_word Plain.M.loaded_segments (0x50cf8 : word) = Some W_50cf8.
Proof. vm_refl. Qed.
Lemma D_50cf8 : decode_any W_50cf8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50cfc : bv 32 := 0x01013903.
Lemma F_50cfc : fetch_word Plain.M.loaded_segments (0x50cfc : word) = Some W_50cfc.
Proof. vm_refl. Qed.
Lemma D_50cfc : decode_any W_50cfc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d00 : bv 32 := 0x00813983.
Lemma F_50d00 : fetch_word Plain.M.loaded_segments (0x50d00 : word) = Some W_50d00.
Proof. vm_refl. Qed.
Lemma D_50d00 : decode_any W_50d00 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d04 : bv 32 := 0x03010113.
Lemma F_50d04 : fetch_word Plain.M.loaded_segments (0x50d04 : word) = Some W_50d04.
Proof. vm_refl. Qed.
Lemma D_50d04 : decode_any W_50d04 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d08 : bv 32 := 0x0dc0e06f.
Lemma F_50d08 : fetch_word Plain.M.loaded_segments (0x50d08 : word) = Some W_50d08.
Proof. vm_refl. Qed.
Lemma D_50d08 : decode_any W_50d08 = Some (Jal 0 57564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d0c : bv 32 := 0x00008067.
Lemma F_50d0c : fetch_word Plain.M.loaded_segments (0x50d0c : word) = Some W_50d0c.
Proof. vm_refl. Qed.
Lemma D_50d0c : decode_any W_50d0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d10 : bv 32 := 0xfd010113.
Lemma F_50d10 : fetch_word Plain.M.loaded_segments (0x50d10 : word) = Some W_50d10.
Proof. vm_refl. Qed.
Lemma D_50d10 : decode_any W_50d10 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d14 : bv 32 := 0x02113423.
Lemma F_50d14 : fetch_word Plain.M.loaded_segments (0x50d14 : word) = Some W_50d14.
Proof. vm_refl. Qed.
Lemma D_50d14 : decode_any W_50d14 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d18 : bv 32 := 0x02813023.
Lemma F_50d18 : fetch_word Plain.M.loaded_segments (0x50d18 : word) = Some W_50d18.
Proof. vm_refl. Qed.
Lemma D_50d18 : decode_any W_50d18 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d1c : bv 32 := 0x00913c23.
Lemma F_50d1c : fetch_word Plain.M.loaded_segments (0x50d1c : word) = Some W_50d1c.
Proof. vm_refl. Qed.
Lemma D_50d1c : decode_any W_50d1c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d20 : bv 32 := 0x01213823.
Lemma F_50d20 : fetch_word Plain.M.loaded_segments (0x50d20 : word) = Some W_50d20.
Proof. vm_refl. Qed.
Lemma D_50d20 : decode_any W_50d20 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d24 : bv 32 := 0x01313423.
Lemma F_50d24 : fetch_word Plain.M.loaded_segments (0x50d24 : word) = Some W_50d24.
Proof. vm_refl. Qed.
Lemma D_50d24 : decode_any W_50d24 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d28 : bv 32 := 0x00050493.
Lemma F_50d28 : fetch_word Plain.M.loaded_segments (0x50d28 : word) = Some W_50d28.
Proof. vm_refl. Qed.
Lemma D_50d28 : decode_any W_50d28 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d2c : bv 32 := 0x00045517.
Lemma F_50d2c : fetch_word Plain.M.loaded_segments (0x50d2c : word) = Some W_50d2c.
Proof. vm_refl. Qed.
Lemma D_50d2c : decode_any W_50d2c = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d30 : bv 32 := 0xeec50993.
Lemma F_50d30 : fetch_word Plain.M.loaded_segments (0x50d30 : word) = Some W_50d30.
Proof. vm_refl. Qed.
Lemma D_50d30 : decode_any W_50d30 = Some (OpImm ALU_ADD 19 10 3820, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d34 : bv 32 := 0x00498413.
Lemma F_50d34 : fetch_word Plain.M.loaded_segments (0x50d34 : word) = Some W_50d34.
Proof. vm_refl. Qed.
Lemma D_50d34 : decode_any W_50d34 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d38 : bv 32 := 0x00040513.
Lemma F_50d38 : fetch_word Plain.M.loaded_segments (0x50d38 : word) = Some W_50d38.
Proof. vm_refl. Qed.
Lemma D_50d38 : decode_any W_50d38 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d3c : bv 32 := 0x6210d0ef.
Lemma F_50d3c : fetch_word Plain.M.loaded_segments (0x50d3c : word) = Some W_50d3c.
Proof. vm_refl. Qed.
Lemma D_50d3c : decode_any W_50d3c = Some (Jal 1 56864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d40 : bv 32 := 0x0009c503.
Lemma F_50d40 : fetch_word Plain.M.loaded_segments (0x50d40 : word) = Some W_50d40.
Proof. vm_refl. Qed.
Lemma D_50d40 : decode_any W_50d40 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d44 : bv 32 := 0xfff00913.
Lemma F_50d44 : fetch_word Plain.M.loaded_segments (0x50d44 : word) = Some W_50d44.
Proof. vm_refl. Qed.
Lemma D_50d44 : decode_any W_50d44 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d48 : bv 32 := 0x06051263.
Lemma F_50d48 : fetch_word Plain.M.loaded_segments (0x50d48 : word) = Some W_50d48.
Proof. vm_refl. Qed.
Lemma D_50d48 : decode_any W_50d48 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d4c : bv 32 := 0x0109b503.
Lemma F_50d4c : fetch_word Plain.M.loaded_segments (0x50d4c : word) = Some W_50d4c.
Proof. vm_refl. Qed.
Lemma D_50d4c : decode_any W_50d4c = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d50 : bv 32 := 0x00051663.
Lemma F_50d50 : fetch_word Plain.M.loaded_segments (0x50d50 : word) = Some W_50d50.
Proof. vm_refl. Qed.
Lemma D_50d50 : decode_any W_50d50 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d54 : bv 32 := 0x01898513.
Lemma F_50d54 : fetch_word Plain.M.loaded_segments (0x50d54 : word) = Some W_50d54.
Proof. vm_refl. Qed.
Lemma D_50d54 : decode_any W_50d54 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d58 : bv 32 := 0x00a9b823.
Lemma F_50d58 : fetch_word Plain.M.loaded_segments (0x50d58 : word) = Some W_50d58.
Proof. vm_refl. Qed.
Lemma D_50d58 : decode_any W_50d58 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d5c : bv 32 := 0x0089a583.
Lemma F_50d5c : fetch_word Plain.M.loaded_segments (0x50d5c : word) = Some W_50d5c.
Proof. vm_refl. Qed.
Lemma D_50d5c : decode_any W_50d5c = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d60 : bv 32 := 0x02000613.
Lemma F_50d60 : fetch_word Plain.M.loaded_segments (0x50d60 : word) = Some W_50d60.
Proof. vm_refl. Qed.
Lemma D_50d60 : decode_any W_50d60 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d64 : bv 32 := 0x02c59263.
Lemma F_50d64 : fetch_word Plain.M.loaded_segments (0x50d64 : word) = Some W_50d64.
Proof. vm_refl. Qed.
Lemma D_50d64 : decode_any W_50d64 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d68 : bv 32 := 0x20800513.
Lemma F_50d68 : fetch_word Plain.M.loaded_segments (0x50d68 : word) = Some W_50d68.
Proof. vm_refl. Qed.
Lemma D_50d68 : decode_any W_50d68 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d6c : bv 32 := 0x00100593.
Lemma F_50d6c : fetch_word Plain.M.loaded_segments (0x50d6c : word) = Some W_50d6c.
Proof. vm_refl. Qed.
Lemma D_50d6c : decode_any W_50d6c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d70 : bv 32 := 0x464000ef.
Lemma F_50d70 : fetch_word Plain.M.loaded_segments (0x50d70 : word) = Some W_50d70.
Proof. vm_refl. Qed.
Lemma D_50d70 : decode_any W_50d70 = Some (Jal 1 1124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d74 : bv 32 := 0x02050c63.
Lemma F_50d74 : fetch_word Plain.M.loaded_segments (0x50d74 : word) = Some W_50d74.
Proof. vm_refl. Qed.
Lemma D_50d74 : decode_any W_50d74 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d78 : bv 32 := 0x00000593.
Lemma F_50d78 : fetch_word Plain.M.loaded_segments (0x50d78 : word) = Some W_50d78.
Proof. vm_refl. Qed.
Lemma D_50d78 : decode_any W_50d78 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d7c : bv 32 := 0x0109b603.
Lemma F_50d7c : fetch_word Plain.M.loaded_segments (0x50d7c : word) = Some W_50d7c.
Proof. vm_refl. Qed.
Lemma D_50d7c : decode_any W_50d7c = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d80 : bv 32 := 0x00c53023.
Lemma F_50d80 : fetch_word Plain.M.loaded_segments (0x50d80 : word) = Some W_50d80.
Proof. vm_refl. Qed.
Lemma D_50d80 : decode_any W_50d80 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d84 : bv 32 := 0x00a9b823.
Lemma F_50d84 : fetch_word Plain.M.loaded_segments (0x50d84 : word) = Some W_50d84.
Proof. vm_refl. Qed.
Lemma D_50d84 : decode_any W_50d84 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d88 : bv 32 := 0x00000913.
Lemma F_50d88 : fetch_word Plain.M.loaded_segments (0x50d88 : word) = Some W_50d88.
Proof. vm_refl. Qed.
Lemma D_50d88 : decode_any W_50d88 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d8c : bv 32 := 0x00359613.
Lemma F_50d8c : fetch_word Plain.M.loaded_segments (0x50d8c : word) = Some W_50d8c.
Proof. vm_refl. Qed.
Lemma D_50d8c : decode_any W_50d8c = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d90 : bv 32 := 0x00c50533.
Lemma F_50d90 : fetch_word Plain.M.loaded_segments (0x50d90 : word) = Some W_50d90.
Proof. vm_refl. Qed.
Lemma D_50d90 : decode_any W_50d90 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d94 : bv 32 := 0x00000617.
Lemma F_50d94 : fetch_word Plain.M.loaded_segments (0x50d94 : word) = Some W_50d94.
Proof. vm_refl. Qed.
Lemma D_50d94 : decode_any W_50d94 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d98 : bv 32 := 0x00158593.
Lemma F_50d98 : fetch_word Plain.M.loaded_segments (0x50d98 : word) = Some W_50d98.
Proof. vm_refl. Qed.
Lemma D_50d98 : decode_any W_50d98 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50d9c : bv 32 := 0x04060613.
Lemma F_50d9c : fetch_word Plain.M.loaded_segments (0x50d9c : word) = Some W_50d9c.
Proof. vm_refl. Qed.
Lemma D_50d9c : decode_any W_50d9c = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50da0 : bv 32 := 0x00c53423.
Lemma F_50da0 : fetch_word Plain.M.loaded_segments (0x50da0 : word) = Some W_50da0.
Proof. vm_refl. Qed.
Lemma D_50da0 : decode_any W_50da0 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50da4 : bv 32 := 0x10953423.
Lemma F_50da4 : fetch_word Plain.M.loaded_segments (0x50da4 : word) = Some W_50da4.
Proof. vm_refl. Qed.
Lemma D_50da4 : decode_any W_50da4 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50da8 : bv 32 := 0x00b9a423.
Lemma F_50da8 : fetch_word Plain.M.loaded_segments (0x50da8 : word) = Some W_50da8.
Proof. vm_refl. Qed.
Lemma D_50da8 : decode_any W_50da8 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50dac : bv 32 := 0x00040513.
Lemma F_50dac : fetch_word Plain.M.loaded_segments (0x50dac : word) = Some W_50dac.
Proof. vm_refl. Qed.
Lemma D_50dac : decode_any W_50dac = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50db0 : bv 32 := 0x0340e0ef.
Lemma F_50db0 : fetch_word Plain.M.loaded_segments (0x50db0 : word) = Some W_50db0.
Proof. vm_refl. Qed.
Lemma D_50db0 : decode_any W_50db0 = Some (Jal 1 57396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50db4 : bv 32 := 0x00090513.
Lemma F_50db4 : fetch_word Plain.M.loaded_segments (0x50db4 : word) = Some W_50db4.
Proof. vm_refl. Qed.
Lemma D_50db4 : decode_any W_50db4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50db8 : bv 32 := 0x02813083.
Lemma F_50db8 : fetch_word Plain.M.loaded_segments (0x50db8 : word) = Some W_50db8.
Proof. vm_refl. Qed.
Lemma D_50db8 : decode_any W_50db8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50dbc : bv 32 := 0x02013403.
Lemma F_50dbc : fetch_word Plain.M.loaded_segments (0x50dbc : word) = Some W_50dbc.
Proof. vm_refl. Qed.
Lemma D_50dbc : decode_any W_50dbc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50dc0 : bv 32 := 0x01813483.
Lemma F_50dc0 : fetch_word Plain.M.loaded_segments (0x50dc0 : word) = Some W_50dc0.
Proof. vm_refl. Qed.
Lemma D_50dc0 : decode_any W_50dc0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50dc4 : bv 32 := 0x01013903.
Lemma F_50dc4 : fetch_word Plain.M.loaded_segments (0x50dc4 : word) = Some W_50dc4.
Proof. vm_refl. Qed.
Lemma D_50dc4 : decode_any W_50dc4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50dc8 : bv 32 := 0x00813983.
Lemma F_50dc8 : fetch_word Plain.M.loaded_segments (0x50dc8 : word) = Some W_50dc8.
Proof. vm_refl. Qed.
Lemma D_50dc8 : decode_any W_50dc8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50dcc : bv 32 := 0x03010113.
Lemma F_50dcc : fetch_word Plain.M.loaded_segments (0x50dcc : word) = Some W_50dcc.
Proof. vm_refl. Qed.
Lemma D_50dcc : decode_any W_50dcc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50dd0 : bv 32 := 0x00008067.
Lemma F_50dd0 : fetch_word Plain.M.loaded_segments (0x50dd0 : word) = Some W_50dd0.
Proof. vm_refl. Qed.
Lemma D_50dd0 : decode_any W_50dd0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50dd4 : bv 32 := 0x00050067.
Lemma F_50dd4 : fetch_word Plain.M.loaded_segments (0x50dd4 : word) = Some W_50dd4.
Proof. vm_refl. Qed.
Lemma D_50dd4 : decode_any W_50dd4 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50dd8 : bv 32 := 0x00008067.
Lemma F_50dd8 : fetch_word Plain.M.loaded_segments (0x50dd8 : word) = Some W_50dd8.
Proof. vm_refl. Qed.
Lemma D_50dd8 : decode_any W_50dd8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ddc : bv 32 := 0xfe010113.
Lemma F_50ddc : fetch_word Plain.M.loaded_segments (0x50ddc : word) = Some W_50ddc.
Proof. vm_refl. Qed.
Lemma D_50ddc : decode_any W_50ddc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50de0 : bv 32 := 0x00113c23.
Lemma F_50de0 : fetch_word Plain.M.loaded_segments (0x50de0 : word) = Some W_50de0.
Proof. vm_refl. Qed.
Lemma D_50de0 : decode_any W_50de0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50de4 : bv 32 := 0x00813823.
Lemma F_50de4 : fetch_word Plain.M.loaded_segments (0x50de4 : word) = Some W_50de4.
Proof. vm_refl. Qed.
Lemma D_50de4 : decode_any W_50de4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50de8 : bv 32 := 0x00913423.
Lemma F_50de8 : fetch_word Plain.M.loaded_segments (0x50de8 : word) = Some W_50de8.
Proof. vm_refl. Qed.
Lemma D_50de8 : decode_any W_50de8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50dec : bv 32 := 0x00013517.
Lemma F_50dec : fetch_word Plain.M.loaded_segments (0x50dec : word) = Some W_50dec.
Proof. vm_refl. Qed.
Lemma D_50dec : decode_any W_50dec = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50df0 : bv 32 := 0x00013597.
Lemma F_50df0 : fetch_word Plain.M.loaded_segments (0x50df0 : word) = Some W_50df0.
Proof. vm_refl. Qed.
Lemma D_50df0 : decode_any W_50df0 = Some (Auipc 11 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50df4 : bv 32 := 0xfbc53503.
Lemma F_50df4 : fetch_word Plain.M.loaded_segments (0x50df4 : word) = Some W_50df4.
Proof. vm_refl. Qed.
Lemma D_50df4 : decode_any W_50df4 = Some (Load SZ8 true 10 10 4028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50df8 : bv 32 := 0xfc05b403.
Lemma F_50df8 : fetch_word Plain.M.loaded_segments (0x50df8 : word) = Some W_50df8.
Proof. vm_refl. Qed.
Lemma D_50df8 : decode_any W_50df8 = Some (Load SZ8 true 8 11 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50dfc : bv 32 := 0x00a47c63.
Lemma F_50dfc : fetch_word Plain.M.loaded_segments (0x50dfc : word) = Some W_50dfc.
Proof. vm_refl. Qed.
Lemma D_50dfc : decode_any W_50dfc = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e00 : bv 32 := 0xff853583.
Lemma F_50e00 : fetch_word Plain.M.loaded_segments (0x50e00 : word) = Some W_50e00.
Proof. vm_refl. Qed.
Lemma D_50e00 : decode_any W_50e00 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e04 : bv 32 := 0xff850493.
Lemma F_50e04 : fetch_word Plain.M.loaded_segments (0x50e04 : word) = Some W_50e04.
Proof. vm_refl. Qed.
Lemma D_50e04 : decode_any W_50e04 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e08 : bv 32 := 0x000580e7.
Lemma F_50e08 : fetch_word Plain.M.loaded_segments (0x50e08 : word) = Some W_50e08.
Proof. vm_refl. Qed.
Lemma D_50e08 : decode_any W_50e08 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e0c : bv 32 := 0x00048513.
Lemma F_50e0c : fetch_word Plain.M.loaded_segments (0x50e0c : word) = Some W_50e0c.
Proof. vm_refl. Qed.
Lemma D_50e0c : decode_any W_50e0c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e10 : bv 32 := 0xfe9468e3.
Lemma F_50e10 : fetch_word Plain.M.loaded_segments (0x50e10 : word) = Some W_50e10.
Proof. vm_refl. Qed.
Lemma D_50e10 : decode_any W_50e10 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e14 : bv 32 := 0x01813083.
Lemma F_50e14 : fetch_word Plain.M.loaded_segments (0x50e14 : word) = Some W_50e14.
Proof. vm_refl. Qed.
Lemma D_50e14 : decode_any W_50e14 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e18 : bv 32 := 0x01013403.
Lemma F_50e18 : fetch_word Plain.M.loaded_segments (0x50e18 : word) = Some W_50e18.
Proof. vm_refl. Qed.
Lemma D_50e18 : decode_any W_50e18 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e1c : bv 32 := 0x00813483.
Lemma F_50e1c : fetch_word Plain.M.loaded_segments (0x50e1c : word) = Some W_50e1c.
Proof. vm_refl. Qed.
Lemma D_50e1c : decode_any W_50e1c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e20 : bv 32 := 0x02010113.
Lemma F_50e20 : fetch_word Plain.M.loaded_segments (0x50e20 : word) = Some W_50e20.
Proof. vm_refl. Qed.
Lemma D_50e20 : decode_any W_50e20 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e24 : bv 32 := 0xfb5ff06f.
Lemma F_50e24 : fetch_word Plain.M.loaded_segments (0x50e24 : word) = Some W_50e24.
Proof. vm_refl. Qed.
Lemma D_50e24 : decode_any W_50e24 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e28 : bv 32 := 0xff010113.
Lemma F_50e28 : fetch_word Plain.M.loaded_segments (0x50e28 : word) = Some W_50e28.
Proof. vm_refl. Qed.
Lemma D_50e28 : decode_any W_50e28 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e2c : bv 32 := 0x00113423.
Lemma F_50e2c : fetch_word Plain.M.loaded_segments (0x50e2c : word) = Some W_50e2c.
Proof. vm_refl. Qed.
Lemma D_50e2c : decode_any W_50e2c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e30 : bv 32 := 0x00813023.
Lemma F_50e30 : fetch_word Plain.M.loaded_segments (0x50e30 : word) = Some W_50e30.
Proof. vm_refl. Qed.
Lemma D_50e30 : decode_any W_50e30 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e34 : bv 32 := 0x00000593.
Lemma F_50e34 : fetch_word Plain.M.loaded_segments (0x50e34 : word) = Some W_50e34.
Proof. vm_refl. Qed.
Lemma D_50e34 : decode_any W_50e34 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e38 : bv 32 := 0x00020613.
Lemma F_50e38 : fetch_word Plain.M.loaded_segments (0x50e38 : word) = Some W_50e38.
Proof. vm_refl. Qed.
Lemma D_50e38 : decode_any W_50e38 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e3c : bv 32 := 0xf5862603.
Lemma F_50e3c : fetch_word Plain.M.loaded_segments (0x50e3c : word) = Some W_50e3c.
Proof. vm_refl. Qed.
Lemma D_50e3c : decode_any W_50e3c = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e40 : bv 32 := 0x00045697.
Lemma F_50e40 : fetch_word Plain.M.loaded_segments (0x50e40 : word) = Some W_50e40.
Proof. vm_refl. Qed.
Lemma D_50e40 : decode_any W_50e40 = Some (Auipc 13 69, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e44 : bv 32 := 0xff868693.
Lemma F_50e44 : fetch_word Plain.M.loaded_segments (0x50e44 : word) = Some W_50e44.
Proof. vm_refl. Qed.
Lemma D_50e44 : decode_any W_50e44 = Some (OpImm ALU_ADD 13 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e48 : bv 32 := 0x1606a72f.
Lemma F_50e48 : fetch_word Plain.M.loaded_segments (0x50e48 : word) = Some W_50e48.
Proof. vm_refl. Qed.
Lemma D_50e48 : decode_any W_50e48 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e4c : bv 32 := 0x00b71663.
Lemma F_50e4c : fetch_word Plain.M.loaded_segments (0x50e4c : word) = Some W_50e4c.
Proof. vm_refl. Qed.
Lemma D_50e4c : decode_any W_50e4c = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e50 : bv 32 := 0x1ec6a7af.
Lemma F_50e50 : fetch_word Plain.M.loaded_segments (0x50e50 : word) = Some W_50e50.
Proof. vm_refl. Qed.
Lemma D_50e50 : decode_any W_50e50 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e54 : bv 32 := 0xfe079ae3.
Lemma F_50e54 : fetch_word Plain.M.loaded_segments (0x50e54 : word) = Some W_50e54.
Proof. vm_refl. Qed.
Lemma D_50e54 : decode_any W_50e54 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e58 : bv 32 := 0x0007059b.
Lemma F_50e58 : fetch_word Plain.M.loaded_segments (0x50e58 : word) = Some W_50e58.
Proof. vm_refl. Qed.
Lemma D_50e58 : decode_any W_50e58 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e5c : bv 32 := 0x02c58263.
Lemma F_50e5c : fetch_word Plain.M.loaded_segments (0x50e5c : word) = Some W_50e5c.
Proof. vm_refl. Qed.
Lemma D_50e5c : decode_any W_50e5c = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e60 : bv 32 := 0x02058263.
Lemma F_50e60 : fetch_word Plain.M.loaded_segments (0x50e60 : word) = Some W_50e60.
Proof. vm_refl. Qed.
Lemma D_50e60 : decode_any W_50e60 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e64 : bv 32 := 0x04900893.
Lemma F_50e64 : fetch_word Plain.M.loaded_segments (0x50e64 : word) = Some W_50e64.
Proof. vm_refl. Qed.
Lemma D_50e64 : decode_any W_50e64 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e68 : bv 32 := 0x00000593.
Lemma F_50e68 : fetch_word Plain.M.loaded_segments (0x50e68 : word) = Some W_50e68.
Proof. vm_refl. Qed.
Lemma D_50e68 : decode_any W_50e68 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e6c : bv 32 := 0x00000613.
Lemma F_50e6c : fetch_word Plain.M.loaded_segments (0x50e6c : word) = Some W_50e6c.
Proof. vm_refl. Qed.
Lemma D_50e6c : decode_any W_50e6c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e70 : bv 32 := 0x00000693.
Lemma F_50e70 : fetch_word Plain.M.loaded_segments (0x50e70 : word) = Some W_50e70.
Proof. vm_refl. Qed.
Lemma D_50e70 : decode_any W_50e70 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e74 : bv 32 := 0x00000513.
Lemma F_50e74 : fetch_word Plain.M.loaded_segments (0x50e74 : word) = Some W_50e74.
Proof. vm_refl. Qed.
Lemma D_50e74 : decode_any W_50e74 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e78 : bv 32 := 0x00000073.
Lemma F_50e78 : fetch_word Plain.M.loaded_segments (0x50e78 : word) = Some W_50e78.
Proof. vm_refl. Qed.
Lemma D_50e78 : decode_any W_50e78 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_50e78 : is_ecall W_50e78 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_50e7c : bv 32 := 0xff9ff06f.
Lemma F_50e7c : fetch_word Plain.M.loaded_segments (0x50e7c : word) = Some W_50e7c.
Proof. vm_refl. Qed.
Lemma D_50e7c : decode_any W_50e7c = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e80 : bv 32 := 0x00000023.
Lemma F_50e80 : fetch_word Plain.M.loaded_segments (0x50e80 : word) = Some W_50e80.
Proof. vm_refl. Qed.
Lemma D_50e80 : decode_any W_50e80 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e84 : bv 32 := 0x00050413.
Lemma F_50e84 : fetch_word Plain.M.loaded_segments (0x50e84 : word) = Some W_50e84.
Proof. vm_refl. Qed.
Lemma D_50e84 : decode_any W_50e84 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e88 : bv 32 := 0xdbdff0ef.
Lemma F_50e88 : fetch_word Plain.M.loaded_segments (0x50e88 : word) = Some W_50e88.
Proof. vm_refl. Qed.
Lemma D_50e88 : decode_any W_50e88 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e8c : bv 32 := 0xf51ff0ef.
Lemma F_50e8c : fetch_word Plain.M.loaded_segments (0x50e8c : word) = Some W_50e8c.
Proof. vm_refl. Qed.
Lemma D_50e8c : decode_any W_50e8c = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e90 : bv 32 := 0x561020ef.
Lemma F_50e90 : fetch_word Plain.M.loaded_segments (0x50e90 : word) = Some W_50e90.
Proof. vm_refl. Qed.
Lemma D_50e90 : decode_any W_50e90 = Some (Jal 1 11616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e94 : bv 32 := 0x00040513.
Lemma F_50e94 : fetch_word Plain.M.loaded_segments (0x50e94 : word) = Some W_50e94.
Proof. vm_refl. Qed.
Lemma D_50e94 : decode_any W_50e94 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e98 : bv 32 := 0xd61ff0ef.
Lemma F_50e98 : fetch_word Plain.M.loaded_segments (0x50e98 : word) = Some W_50e98.
Proof. vm_refl. Qed.
Lemma D_50e98 : decode_any W_50e98 = Some (Jal 1 2096480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50e9c : bv 32 := 0xfa010113.
Lemma F_50e9c : fetch_word Plain.M.loaded_segments (0x50e9c : word) = Some W_50e9c.
Proof. vm_refl. Qed.
Lemma D_50e9c : decode_any W_50e9c = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ea0 : bv 32 := 0x02113423.
Lemma F_50ea0 : fetch_word Plain.M.loaded_segments (0x50ea0 : word) = Some W_50ea0.
Proof. vm_refl. Qed.
Lemma D_50ea0 : decode_any W_50ea0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ea4 : bv 32 := 0x02813023.
Lemma F_50ea4 : fetch_word Plain.M.loaded_segments (0x50ea4 : word) = Some W_50ea4.
Proof. vm_refl. Qed.
Lemma D_50ea4 : decode_any W_50ea4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ea8 : bv 32 := 0x00913c23.
Lemma F_50ea8 : fetch_word Plain.M.loaded_segments (0x50ea8 : word) = Some W_50ea8.
Proof. vm_refl. Qed.
Lemma D_50ea8 : decode_any W_50ea8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50eac : bv 32 := 0x00058413.
Lemma F_50eac : fetch_word Plain.M.loaded_segments (0x50eac : word) = Some W_50eac.
Proof. vm_refl. Qed.
Lemma D_50eac : decode_any W_50eac = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50eb0 : bv 32 := 0x00050293.
Lemma F_50eb0 : fetch_word Plain.M.loaded_segments (0x50eb0 : word) = Some W_50eb0.
Proof. vm_refl. Qed.
Lemma D_50eb0 : decode_any W_50eb0 = Some (OpImm ALU_ADD 5 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50eb4 : bv 32 := 0x05013823.
Lemma F_50eb4 : fetch_word Plain.M.loaded_segments (0x50eb4 : word) = Some W_50eb4.
Proof. vm_refl. Qed.
Lemma D_50eb4 : decode_any W_50eb4 = Some (Store SZ8 2 16 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50eb8 : bv 32 := 0x05113c23.
Lemma F_50eb8 : fetch_word Plain.M.loaded_segments (0x50eb8 : word) = Some W_50eb8.
Proof. vm_refl. Qed.
Lemma D_50eb8 : decode_any W_50eb8 = Some (Store SZ8 2 17 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ebc : bv 32 := 0x00013517.
Lemma F_50ebc : fetch_word Plain.M.loaded_segments (0x50ebc : word) = Some W_50ebc.
Proof. vm_refl. Qed.
Lemma D_50ebc : decode_any W_50ebc = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ec0 : bv 32 := 0xee453483.
Lemma F_50ec0 : fetch_word Plain.M.loaded_segments (0x50ec0 : word) = Some W_50ec0.
Proof. vm_refl. Qed.
Lemma D_50ec0 : decode_any W_50ec0 = Some (Load SZ8 true 9 10 3812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ec4 : bv 32 := 0x02c13823.
Lemma F_50ec4 : fetch_word Plain.M.loaded_segments (0x50ec4 : word) = Some W_50ec4.
Proof. vm_refl. Qed.
Lemma D_50ec4 : decode_any W_50ec4 = Some (Store SZ8 2 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ec8 : bv 32 := 0x02d13c23.
Lemma F_50ec8 : fetch_word Plain.M.loaded_segments (0x50ec8 : word) = Some W_50ec8.
Proof. vm_refl. Qed.
Lemma D_50ec8 : decode_any W_50ec8 = Some (Store SZ8 2 13 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ecc : bv 32 := 0x04e13023.
Lemma F_50ecc : fetch_word Plain.M.loaded_segments (0x50ecc : word) = Some W_50ecc.
Proof. vm_refl. Qed.
Lemma D_50ecc : decode_any W_50ecc = Some (Store SZ8 2 14 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ed0 : bv 32 := 0x04f13423.
Lemma F_50ed0 : fetch_word Plain.M.loaded_segments (0x50ed0 : word) = Some W_50ed0.
Proof. vm_refl. Qed.
Lemma D_50ed0 : decode_any W_50ed0 = Some (Store SZ8 2 15 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ed4 : bv 32 := 0x0004b503.
Lemma F_50ed4 : fetch_word Plain.M.loaded_segments (0x50ed4 : word) = Some W_50ed4.
Proof. vm_refl. Qed.
Lemma D_50ed4 : decode_any W_50ed4 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ed8 : bv 32 := 0x0405f593.
Lemma F_50ed8 : fetch_word Plain.M.loaded_segments (0x50ed8 : word) = Some W_50ed8.
Proof. vm_refl. Qed.
Lemma D_50ed8 : decode_any W_50ed8 = Some (OpImm ALU_AND 11 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50edc : bv 32 := 0x00a13823.
Lemma F_50edc : fetch_word Plain.M.loaded_segments (0x50edc : word) = Some W_50edc.
Proof. vm_refl. Qed.
Lemma D_50edc : decode_any W_50edc = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ee0 : bv 32 := 0x00059c63.
Lemma F_50ee0 : fetch_word Plain.M.loaded_segments (0x50ee0 : word) = Some W_50ee0.
Proof. vm_refl. Qed.
Lemma D_50ee0 : decode_any W_50ee0 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ee4 : bv 32 := 0x00410537.
Lemma F_50ee4 : fetch_word Plain.M.loaded_segments (0x50ee4 : word) = Some W_50ee4.
Proof. vm_refl. Qed.
Lemma D_50ee4 : decode_any W_50ee4 = Some (Lui 10 1040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ee8 : bv 32 := 0x00a475b3.
Lemma F_50ee8 : fetch_word Plain.M.loaded_segments (0x50ee8 : word) = Some W_50ee8.
Proof. vm_refl. Qed.
Lemma D_50ee8 : decode_any W_50ee8 = Some (Op ALU_AND 11 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50eec : bv 32 := 0x00a58663.
Lemma F_50eec : fetch_word Plain.M.loaded_segments (0x50eec : word) = Some W_50eec.
Proof. vm_refl. Qed.
Lemma D_50eec : decode_any W_50eec = Some (Branch BC_EQ 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ef0 : bv 32 := 0x00000713.
Lemma F_50ef0 : fetch_word Plain.M.loaded_segments (0x50ef0 : word) = Some W_50ef0.
Proof. vm_refl. Qed.
Lemma D_50ef0 : decode_any W_50ef0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ef4 : bv 32 := 0x0080006f.
Lemma F_50ef4 : fetch_word Plain.M.loaded_segments (0x50ef4 : word) = Some W_50ef4.
Proof. vm_refl. Qed.
Lemma D_50ef4 : decode_any W_50ef4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ef8 : bv 32 := 0x03016703.
Lemma F_50ef8 : fetch_word Plain.M.loaded_segments (0x50ef8 : word) = Some W_50ef8.
Proof. vm_refl. Qed.
Lemma D_50ef8 : decode_any W_50ef8 = Some (Load SZ4 false 14 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50efc : bv 32 := 0x000086b7.
Lemma F_50efc : fetch_word Plain.M.loaded_segments (0x50efc : word) = Some W_50efc.
Proof. vm_refl. Qed.
Lemma D_50efc : decode_any W_50efc = Some (Lui 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f00 : bv 32 := 0x00d466b3.
Lemma F_50f00 : fetch_word Plain.M.loaded_segments (0x50f00 : word) = Some W_50f00.
Proof. vm_refl. Qed.
Lemma D_50f00 : decode_any W_50f00 = Some (Op ALU_OR 13 8 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f04 : bv 32 := 0x03800513.
Lemma F_50f04 : fetch_word Plain.M.loaded_segments (0x50f04 : word) = Some W_50f04.
Proof. vm_refl. Qed.
Lemma D_50f04 : decode_any W_50f04 = Some (OpImm ALU_ADD 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f08 : bv 32 := 0xf9c00593.
Lemma F_50f08 : fetch_word Plain.M.loaded_segments (0x50f08 : word) = Some W_50f08.
Proof. vm_refl. Qed.
Lemma D_50f08 : decode_any W_50f08 = Some (OpImm ALU_ADD 11 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f0c : bv 32 := 0x00028613.
Lemma F_50f0c : fetch_word Plain.M.loaded_segments (0x50f0c : word) = Some W_50f0c.
Proof. vm_refl. Qed.
Lemma D_50f0c : decode_any W_50f0c = Some (OpImm ALU_ADD 12 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f10 : bv 32 := 0x00000793.
Lemma F_50f10 : fetch_word Plain.M.loaded_segments (0x50f10 : word) = Some W_50f10.
Proof. vm_refl. Qed.
Lemma D_50f10 : decode_any W_50f10 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f14 : bv 32 := 0x00000813.
Lemma F_50f14 : fetch_word Plain.M.loaded_segments (0x50f14 : word) = Some W_50f14.
Proof. vm_refl. Qed.
Lemma D_50f14 : decode_any W_50f14 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f18 : bv 32 := 0x7650d0ef.
Lemma F_50f18 : fetch_word Plain.M.loaded_segments (0x50f18 : word) = Some W_50f18.
Proof. vm_refl. Qed.
Lemma D_50f18 : decode_any W_50f18 = Some (Jal 1 57188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f1c : bv 32 := 0x02c41413.
Lemma F_50f1c : fetch_word Plain.M.loaded_segments (0x50f1c : word) = Some W_50f1c.
Proof. vm_refl. Qed.
Lemma D_50f1c : decode_any W_50f1c = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f20 : bv 32 := 0x00050693.
Lemma F_50f20 : fetch_word Plain.M.loaded_segments (0x50f20 : word) = Some W_50f20.
Proof. vm_refl. Qed.
Lemma D_50f20 : decode_any W_50f20 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f24 : bv 32 := 0x02045663.
Lemma F_50f24 : fetch_word Plain.M.loaded_segments (0x50f24 : word) = Some W_50f24.
Proof. vm_refl. Qed.
Lemma D_50f24 : decode_any W_50f24 = Some (Branch BC_GE 8 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f28 : bv 32 := 0x80000537.
Lemma F_50f28 : fetch_word Plain.M.loaded_segments (0x50f28 : word) = Some W_50f28.
Proof. vm_refl. Qed.
Lemma D_50f28 : decode_any W_50f28 = Some (Lui 10 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f2c : bv 32 := 0xfff5051b.
Lemma F_50f2c : fetch_word Plain.M.loaded_segments (0x50f2c : word) = Some W_50f2c.
Proof. vm_refl. Qed.
Lemma D_50f2c : decode_any W_50f2c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f30 : bv 32 := 0x00150593.
Lemma F_50f30 : fetch_word Plain.M.loaded_segments (0x50f30 : word) = Some W_50f30.
Proof. vm_refl. Qed.
Lemma D_50f30 : decode_any W_50f30 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f34 : bv 32 := 0x00b6f5b3.
Lemma F_50f34 : fetch_word Plain.M.loaded_segments (0x50f34 : word) = Some W_50f34.
Proof. vm_refl. Qed.
Lemma D_50f34 : decode_any W_50f34 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f38 : bv 32 := 0x00059c63.
Lemma F_50f38 : fetch_word Plain.M.loaded_segments (0x50f38 : word) = Some W_50f38.
Proof. vm_refl. Qed.
Lemma D_50f38 : decode_any W_50f38 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f3c : bv 32 := 0x00a6f533.
Lemma F_50f3c : fetch_word Plain.M.loaded_segments (0x50f3c : word) = Some W_50f3c.
Proof. vm_refl. Qed.
Lemma D_50f3c : decode_any W_50f3c = Some (Op ALU_AND 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f40 : bv 32 := 0x01900893.
Lemma F_50f40 : fetch_word Plain.M.loaded_segments (0x50f40 : word) = Some W_50f40.
Proof. vm_refl. Qed.
Lemma D_50f40 : decode_any W_50f40 = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f44 : bv 32 := 0x00200593.
Lemma F_50f44 : fetch_word Plain.M.loaded_segments (0x50f44 : word) = Some W_50f44.
Proof. vm_refl. Qed.
Lemma D_50f44 : decode_any W_50f44 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f48 : bv 32 := 0x00100613.
Lemma F_50f48 : fetch_word Plain.M.loaded_segments (0x50f48 : word) = Some W_50f48.
Proof. vm_refl. Qed.
Lemma D_50f48 : decode_any W_50f48 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f4c : bv 32 := 0x00000073.
Lemma F_50f4c : fetch_word Plain.M.loaded_segments (0x50f4c : word) = Some W_50f4c.
Proof. vm_refl. Qed.
Lemma D_50f4c : decode_any W_50f4c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_50f4c : is_ecall W_50f4c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_50f50 : bv 32 := 0x0006851b.
Lemma F_50f50 : fetch_word Plain.M.loaded_segments (0x50f50 : word) = Some W_50f50.
Proof. vm_refl. Qed.
Lemma D_50f50 : decode_any W_50f50 = Some (OpImm32 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f54 : bv 32 := 0x094000ef.
Lemma F_50f54 : fetch_word Plain.M.loaded_segments (0x50f54 : word) = Some W_50f54.
Proof. vm_refl. Qed.
Lemma D_50f54 : decode_any W_50f54 = Some (Jal 1 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f58 : bv 32 := 0x0004b583.
Lemma F_50f58 : fetch_word Plain.M.loaded_segments (0x50f58 : word) = Some W_50f58.
Proof. vm_refl. Qed.
Lemma D_50f58 : decode_any W_50f58 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f5c : bv 32 := 0x01013603.
Lemma F_50f5c : fetch_word Plain.M.loaded_segments (0x50f5c : word) = Some W_50f5c.
Proof. vm_refl. Qed.
Lemma D_50f5c : decode_any W_50f5c = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f60 : bv 32 := 0x00c59e63.
Lemma F_50f60 : fetch_word Plain.M.loaded_segments (0x50f60 : word) = Some W_50f60.
Proof. vm_refl. Qed.
Lemma D_50f60 : decode_any W_50f60 = Some (Branch BC_NE 11 12 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f64 : bv 32 := 0x0005051b.
Lemma F_50f64 : fetch_word Plain.M.loaded_segments (0x50f64 : word) = Some W_50f64.
Proof. vm_refl. Qed.
Lemma D_50f64 : decode_any W_50f64 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f68 : bv 32 := 0x02813083.
Lemma F_50f68 : fetch_word Plain.M.loaded_segments (0x50f68 : word) = Some W_50f68.
Proof. vm_refl. Qed.
Lemma D_50f68 : decode_any W_50f68 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f6c : bv 32 := 0x02013403.
Lemma F_50f6c : fetch_word Plain.M.loaded_segments (0x50f6c : word) = Some W_50f6c.
Proof. vm_refl. Qed.
Lemma D_50f6c : decode_any W_50f6c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f70 : bv 32 := 0x01813483.
Lemma F_50f70 : fetch_word Plain.M.loaded_segments (0x50f70 : word) = Some W_50f70.
Proof. vm_refl. Qed.
Lemma D_50f70 : decode_any W_50f70 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f74 : bv 32 := 0x06010113.
Lemma F_50f74 : fetch_word Plain.M.loaded_segments (0x50f74 : word) = Some W_50f74.
Proof. vm_refl. Qed.
Lemma D_50f74 : decode_any W_50f74 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f78 : bv 32 := 0x00008067.
Lemma F_50f78 : fetch_word Plain.M.loaded_segments (0x50f78 : word) = Some W_50f78.
Proof. vm_refl. Qed.
Lemma D_50f78 : decode_any W_50f78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f7c : bv 32 := 0x064000ef.
Lemma F_50f7c : fetch_word Plain.M.loaded_segments (0x50f7c : word) = Some W_50f7c.
Proof. vm_refl. Qed.
Lemma D_50f7c : decode_any W_50f7c = Some (Jal 1 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f80 : bv 32 := 0xff010113.
Lemma F_50f80 : fetch_word Plain.M.loaded_segments (0x50f80 : word) = Some W_50f80.
Proof. vm_refl. Qed.
Lemma D_50f80 : decode_any W_50f80 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f84 : bv 32 := 0x00113423.
Lemma F_50f84 : fetch_word Plain.M.loaded_segments (0x50f84 : word) = Some W_50f84.
Proof. vm_refl. Qed.
Lemma D_50f84 : decode_any W_50f84 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f88 : bv 32 := 0x00050e63.
Lemma F_50f88 : fetch_word Plain.M.loaded_segments (0x50f88 : word) = Some W_50f88.
Proof. vm_refl. Qed.
Lemma D_50f88 : decode_any W_50f88 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f8c : bv 32 := 0x00050593.
Lemma F_50f8c : fetch_word Plain.M.loaded_segments (0x50f8c : word) = Some W_50f8c.
Proof. vm_refl. Qed.
Lemma D_50f8c : decode_any W_50f8c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f90 : bv 32 := 0x00013517.
Lemma F_50f90 : fetch_word Plain.M.loaded_segments (0x50f90 : word) = Some W_50f90.
Proof. vm_refl. Qed.
Lemma D_50f90 : decode_any W_50f90 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f94 : bv 32 := 0xe1053503.
Lemma F_50f94 : fetch_word Plain.M.loaded_segments (0x50f94 : word) = Some W_50f94.
Proof. vm_refl. Qed.
Lemma D_50f94 : decode_any W_50f94 = Some (Load SZ8 true 10 10 3600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f98 : bv 32 := 0x00800613.
Lemma F_50f98 : fetch_word Plain.M.loaded_segments (0x50f98 : word) = Some W_50f98.
Proof. vm_refl. Qed.
Lemma D_50f98 : decode_any W_50f98 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50f9c : bv 32 := 0x3540d0ef.
Lemma F_50f9c : fetch_word Plain.M.loaded_segments (0x50f9c : word) = Some W_50f9c.
Proof. vm_refl. Qed.
Lemma D_50f9c : decode_any W_50f9c = Some (Jal 1 54100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fa0 : bv 32 := 0x01c0006f.
Lemma F_50fa0 : fetch_word Plain.M.loaded_segments (0x50fa0 : word) = Some W_50fa0.
Proof. vm_refl. Qed.
Lemma D_50fa0 : decode_any W_50fa0 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fa4 : bv 32 := 0x00013517.
Lemma F_50fa4 : fetch_word Plain.M.loaded_segments (0x50fa4 : word) = Some W_50fa4.
Proof. vm_refl. Qed.
Lemma D_50fa4 : decode_any W_50fa4 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fa8 : bv 32 := 0xdfc53503.
Lemma F_50fa8 : fetch_word Plain.M.loaded_segments (0x50fa8 : word) = Some W_50fa8.
Proof. vm_refl. Qed.
Lemma D_50fa8 : decode_any W_50fa8 = Some (Load SZ8 true 10 10 3580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fac : bv 32 := 0x41c655b7.
Lemma F_50fac : fetch_word Plain.M.loaded_segments (0x50fac : word) = Some W_50fac.
Proof. vm_refl. Qed.
Lemma D_50fac : decode_any W_50fac = Some (Lui 11 269413, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fb0 : bv 32 := 0xe6d5859b.
Lemma F_50fb0 : fetch_word Plain.M.loaded_segments (0x50fb0 : word) = Some W_50fb0.
Proof. vm_refl. Qed.
Lemma D_50fb0 : decode_any W_50fb0 = Some (OpImm32 11 11 3693, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fb4 : bv 32 := 0x02b505b3.
Lemma F_50fb4 : fetch_word Plain.M.loaded_segments (0x50fb4 : word) = Some W_50fb4.
Proof. vm_refl. Qed.
Lemma D_50fb4 : decode_any W_50fb4 = Some (Mul M_MUL 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fb8 : bv 32 := 0x00b53023.
Lemma F_50fb8 : fetch_word Plain.M.loaded_segments (0x50fb8 : word) = Some W_50fb8.
Proof. vm_refl. Qed.
Lemma D_50fb8 : decode_any W_50fb8 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fbc : bv 32 := 0x00013517.
Lemma F_50fbc : fetch_word Plain.M.loaded_segments (0x50fbc : word) = Some W_50fbc.
Proof. vm_refl. Qed.
Lemma D_50fbc : decode_any W_50fbc = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fc0 : bv 32 := 0xde453503.
Lemma F_50fc0 : fetch_word Plain.M.loaded_segments (0x50fc0 : word) = Some W_50fc0.
Proof. vm_refl. Qed.
Lemma D_50fc0 : decode_any W_50fc0 = Some (Load SZ8 true 10 10 3556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fc4 : bv 32 := 0x000500a3.
Lemma F_50fc4 : fetch_word Plain.M.loaded_segments (0x50fc4 : word) = Some W_50fc4.
Proof. vm_refl. Qed.
Lemma D_50fc4 : decode_any W_50fc4 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fc8 : bv 32 := 0x00053503.
Lemma F_50fc8 : fetch_word Plain.M.loaded_segments (0x50fc8 : word) = Some W_50fc8.
Proof. vm_refl. Qed.
Lemma D_50fc8 : decode_any W_50fc8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fcc : bv 32 := 0x00020593.
Lemma F_50fcc : fetch_word Plain.M.loaded_segments (0x50fcc : word) = Some W_50fcc.
Proof. vm_refl. Qed.
Lemma D_50fcc : decode_any W_50fcc = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fd0 : bv 32 := 0xfea5b823.
Lemma F_50fd0 : fetch_word Plain.M.loaded_segments (0x50fd0 : word) = Some W_50fd0.
Proof. vm_refl. Qed.
Lemma D_50fd0 : decode_any W_50fd0 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fd4 : bv 32 := 0x00813083.
Lemma F_50fd4 : fetch_word Plain.M.loaded_segments (0x50fd4 : word) = Some W_50fd4.
Proof. vm_refl. Qed.
Lemma D_50fd4 : decode_any W_50fd4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fd8 : bv 32 := 0x01010113.
Lemma F_50fd8 : fetch_word Plain.M.loaded_segments (0x50fd8 : word) = Some W_50fd8.
Proof. vm_refl. Qed.
Lemma D_50fd8 : decode_any W_50fd8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fdc : bv 32 := 0x00008067.
Lemma F_50fdc : fetch_word Plain.M.loaded_segments (0x50fdc : word) = Some W_50fdc.
Proof. vm_refl. Qed.
Lemma D_50fdc : decode_any W_50fdc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fe0 : bv 32 := 0x00000023.
Lemma F_50fe0 : fetch_word Plain.M.loaded_segments (0x50fe0 : word) = Some W_50fe0.
Proof. vm_refl. Qed.
Lemma D_50fe0 : decode_any W_50fe0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fe4 : bv 32 := 0x00008067.
Lemma F_50fe4 : fetch_word Plain.M.loaded_segments (0x50fe4 : word) = Some W_50fe4.
Proof. vm_refl. Qed.
Lemma D_50fe4 : decode_any W_50fe4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fe8 : bv 32 := 0xfffff5b7.
Lemma F_50fe8 : fetch_word Plain.M.loaded_segments (0x50fe8 : word) = Some W_50fe8.
Proof. vm_refl. Qed.
Lemma D_50fe8 : decode_any W_50fe8 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50fec : bv 32 := 0x0015859b.
Lemma F_50fec : fetch_word Plain.M.loaded_segments (0x50fec : word) = Some W_50fec.
Proof. vm_refl. Qed.
Lemma D_50fec : decode_any W_50fec = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ff0 : bv 32 := 0x02b56663.
Lemma F_50ff0 : fetch_word Plain.M.loaded_segments (0x50ff0 : word) = Some W_50ff0.
Proof. vm_refl. Qed.
Lemma D_50ff0 : decode_any W_50ff0 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ff4 : bv 32 := 0xff010113.
Lemma F_50ff4 : fetch_word Plain.M.loaded_segments (0x50ff4 : word) = Some W_50ff4.
Proof. vm_refl. Qed.
Lemma D_50ff4 : decode_any W_50ff4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ff8 : bv 32 := 0x00113423.
Lemma F_50ff8 : fetch_word Plain.M.loaded_segments (0x50ff8 : word) = Some W_50ff8.
Proof. vm_refl. Qed.
Lemma D_50ff8 : decode_any W_50ff8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_50ffc : bv 32 := 0x00813023.
Lemma F_50ffc : fetch_word Plain.M.loaded_segments (0x50ffc : word) = Some W_50ffc.
Proof. vm_refl. Qed.
Lemma D_50ffc : decode_any W_50ffc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51000 : bv 32 := 0x40a0043b.
Lemma F_51000 : fetch_word Plain.M.loaded_segments (0x51000 : word) = Some W_51000.
Proof. vm_refl. Qed.
Lemma D_51000 : decode_any W_51000 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51004 : bv 32 := 0xb55ff0ef.
Lemma F_51004 : fetch_word Plain.M.loaded_segments (0x51004 : word) = Some W_51004.
Proof. vm_refl. Qed.
Lemma D_51004 : decode_any W_51004 = Some (Jal 1 2095956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51008 : bv 32 := 0x00852023.
Lemma F_51008 : fetch_word Plain.M.loaded_segments (0x51008 : word) = Some W_51008.
Proof. vm_refl. Qed.
Lemma D_51008 : decode_any W_51008 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5100c : bv 32 := 0xfff00513.
Lemma F_5100c : fetch_word Plain.M.loaded_segments (0x5100c : word) = Some W_5100c.
Proof. vm_refl. Qed.
Lemma D_5100c : decode_any W_5100c = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51010 : bv 32 := 0x00813083.
Lemma F_51010 : fetch_word Plain.M.loaded_segments (0x51010 : word) = Some W_51010.
Proof. vm_refl. Qed.
Lemma D_51010 : decode_any W_51010 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51014 : bv 32 := 0x00013403.
Lemma F_51014 : fetch_word Plain.M.loaded_segments (0x51014 : word) = Some W_51014.
Proof. vm_refl. Qed.
Lemma D_51014 : decode_any W_51014 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51018 : bv 32 := 0x01010113.
Lemma F_51018 : fetch_word Plain.M.loaded_segments (0x51018 : word) = Some W_51018.
Proof. vm_refl. Qed.
Lemma D_51018 : decode_any W_51018 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5101c : bv 32 := 0x00008067.
Lemma F_5101c : fetch_word Plain.M.loaded_segments (0x5101c : word) = Some W_5101c.
Proof. vm_refl. Qed.
Lemma D_5101c : decode_any W_5101c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
