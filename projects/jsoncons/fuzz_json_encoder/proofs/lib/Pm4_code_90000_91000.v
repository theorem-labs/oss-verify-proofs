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
Definition W_900a0 : bv 32 := 0x000d1597.
Lemma F_900a0 : fetch_word Asan.M.loaded_segments (0x900f0 : word) = Some W_900a0.
Proof. vm_refl. Qed.
Lemma D_900a0 : decode_any W_900a0 = Some (Auipc 11 209, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_900a4 : bv 32 := 0xb185b583.
Lemma F_900a4 : fetch_word Asan.M.loaded_segments (0x900f4 : word) = Some W_900a4.
Proof. vm_refl. Qed.
Lemma D_900a4 : decode_any W_900a4 = Some (Load SZ8 true 11 11 2840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_900a8 : bv 32 := 0x0905b583.
Lemma F_900a8 : fetch_word Asan.M.loaded_segments (0x900f8 : word) = Some W_900a8.
Proof. vm_refl. Qed.
Lemma D_900a8 : decode_any W_900a8 = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_900ac : bv 32 := 0x00058e63.
Lemma F_900ac : fetch_word Asan.M.loaded_segments (0x900fc : word) = Some W_900ac.
Proof. vm_refl. Qed.
Lemma D_900ac : decode_any W_900ac = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_900c8 : bv 32 := 0x00008067.
Lemma F_900c8 : fetch_word Asan.M.loaded_segments (0x90118 : word) = Some W_900c8.
Proof. vm_refl. Qed.
Lemma D_900c8 : decode_any W_900c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_900e4 : bv 32 := 0x000d1597.
Lemma F_900e4 : fetch_word Asan.M.loaded_segments (0x90134 : word) = Some W_900e4.
Proof. vm_refl. Qed.
Lemma D_900e4 : decode_any W_900e4 = Some (Auipc 11 209, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_900e8 : bv 32 := 0xad45b583.
Lemma F_900e8 : fetch_word Asan.M.loaded_segments (0x90138 : word) = Some W_900e8.
Proof. vm_refl. Qed.
Lemma D_900e8 : decode_any W_900e8 = Some (Load SZ8 true 11 11 2772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_900ec : bv 32 := 0x0905b583.
Lemma F_900ec : fetch_word Asan.M.loaded_segments (0x9013c : word) = Some W_900ec.
Proof. vm_refl. Qed.
Lemma D_900ec : decode_any W_900ec = Some (Load SZ8 true 11 11 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_900f0 : bv 32 := 0x00058a63.
Lemma F_900f0 : fetch_word Asan.M.loaded_segments (0x90140 : word) = Some W_900f0.
Proof. vm_refl. Qed.
Lemma D_900f0 : decode_any W_900f0 = Some (Branch BC_EQ 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90104 : bv 32 := 0x00008067.
Lemma F_90104 : fetch_word Asan.M.loaded_segments (0x90154 : word) = Some W_90104.
Proof. vm_refl. Qed.
Lemma D_90104 : decode_any W_90104 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90614 : bv 32 := 0xfe010113.
Lemma F_90614 : fetch_word Asan.M.loaded_segments (0x90664 : word) = Some W_90614.
Proof. vm_refl. Qed.
Lemma D_90614 : decode_any W_90614 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90618 : bv 32 := 0x00113c23.
Lemma F_90618 : fetch_word Asan.M.loaded_segments (0x90668 : word) = Some W_90618.
Proof. vm_refl. Qed.
Lemma D_90618 : decode_any W_90618 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9061c : bv 32 := 0x00813823.
Lemma F_9061c : fetch_word Asan.M.loaded_segments (0x9066c : word) = Some W_9061c.
Proof. vm_refl. Qed.
Lemma D_9061c : decode_any W_9061c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90620 : bv 32 := 0x00913423.
Lemma F_90620 : fetch_word Asan.M.loaded_segments (0x90670 : word) = Some W_90620.
Proof. vm_refl. Qed.
Lemma D_90620 : decode_any W_90620 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90624 : bv 32 := 0x01213023.
Lemma F_90624 : fetch_word Asan.M.loaded_segments (0x90674 : word) = Some W_90624.
Proof. vm_refl. Qed.
Lemma D_90624 : decode_any W_90624 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90628 : bv 32 := 0x00058413.
Lemma F_90628 : fetch_word Asan.M.loaded_segments (0x90678 : word) = Some W_90628.
Proof. vm_refl. Qed.
Lemma D_90628 : decode_any W_90628 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9062c : bv 32 := 0x00050493.
Lemma F_9062c : fetch_word Asan.M.loaded_segments (0x9067c : word) = Some W_9062c.
Proof. vm_refl. Qed.
Lemma D_9062c : decode_any W_9062c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90630 : bv 32 := 0x09c000ef.
Lemma F_90630 : fetch_word Asan.M.loaded_segments (0x90680 : word) = Some W_90630.
Proof. vm_refl. Qed.
Lemma D_90630 : decode_any W_90630 = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90634 : bv 32 := 0x0016b517.
Lemma F_90634 : fetch_word Asan.M.loaded_segments (0x90684 : word) = Some W_90634.
Proof. vm_refl. Qed.
Lemma D_90634 : decode_any W_90634 = Some (Auipc 10 363, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90638 : bv 32 := 0x33c50913.
Lemma F_90638 : fetch_word Asan.M.loaded_segments (0x90688 : word) = Some W_90638.
Proof. vm_refl. Qed.
Lemma D_90638 : decode_any W_90638 = Some (OpImm ALU_ADD 18 10 828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9063c : bv 32 := 0x00093603.
Lemma F_9063c : fetch_word Asan.M.loaded_segments (0x9068c : word) = Some W_9063c.
Proof. vm_refl. Qed.
Lemma D_9063c : decode_any W_9063c = Some (Load SZ8 true 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90640 : bv 32 := 0x06060a63.
Lemma F_90640 : fetch_word Asan.M.loaded_segments (0x90690 : word) = Some W_90640.
Proof. vm_refl. Qed.
Lemma D_90640 : decode_any W_90640 = Some (Branch BC_EQ 12 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_906b4 : bv 32 := 0x01813083.
Lemma F_906b4 : fetch_word Asan.M.loaded_segments (0x90704 : word) = Some W_906b4.
Proof. vm_refl. Qed.
Lemma D_906b4 : decode_any W_906b4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_906b8 : bv 32 := 0x01013403.
Lemma F_906b8 : fetch_word Asan.M.loaded_segments (0x90708 : word) = Some W_906b8.
Proof. vm_refl. Qed.
Lemma D_906b8 : decode_any W_906b8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_906bc : bv 32 := 0x00813483.
Lemma F_906bc : fetch_word Asan.M.loaded_segments (0x9070c : word) = Some W_906bc.
Proof. vm_refl. Qed.
Lemma D_906bc : decode_any W_906bc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_906c0 : bv 32 := 0x00013903.
Lemma F_906c0 : fetch_word Asan.M.loaded_segments (0x90710 : word) = Some W_906c0.
Proof. vm_refl. Qed.
Lemma D_906c0 : decode_any W_906c0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_906c4 : bv 32 := 0x02010113.
Lemma F_906c4 : fetch_word Asan.M.loaded_segments (0x90714 : word) = Some W_906c4.
Proof. vm_refl. Qed.
Lemma D_906c4 : decode_any W_906c4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_906c8 : bv 32 := 0x00008067.
Lemma F_906c8 : fetch_word Asan.M.loaded_segments (0x90718 : word) = Some W_906c8.
Proof. vm_refl. Qed.
Lemma D_906c8 : decode_any W_906c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_906cc : bv 32 := 0x00008067.
Lemma F_906cc : fetch_word Asan.M.loaded_segments (0x9071c : word) = Some W_906cc.
Proof. vm_refl. Qed.
Lemma D_906cc : decode_any W_906cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_906d0 : bv 32 := 0xfe010113.
Lemma F_906d0 : fetch_word Asan.M.loaded_segments (0x90720 : word) = Some W_906d0.
Proof. vm_refl. Qed.
Lemma D_906d0 : decode_any W_906d0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_906d4 : bv 32 := 0x00113c23.
Lemma F_906d4 : fetch_word Asan.M.loaded_segments (0x90724 : word) = Some W_906d4.
Proof. vm_refl. Qed.
Lemma D_906d4 : decode_any W_906d4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_906d8 : bv 32 := 0x00813823.
Lemma F_906d8 : fetch_word Asan.M.loaded_segments (0x90728 : word) = Some W_906d8.
Proof. vm_refl. Qed.
Lemma D_906d8 : decode_any W_906d8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_906dc : bv 32 := 0x00913423.
Lemma F_906dc : fetch_word Asan.M.loaded_segments (0x9072c : word) = Some W_906dc.
Proof. vm_refl. Qed.
Lemma D_906dc : decode_any W_906dc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_906e0 : bv 32 := 0x00050413.
Lemma F_906e0 : fetch_word Asan.M.loaded_segments (0x90730 : word) = Some W_906e0.
Proof. vm_refl. Qed.
Lemma D_906e0 : decode_any W_906e0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_906e4 : bv 32 := 0x098000ef.
Lemma F_906e4 : fetch_word Asan.M.loaded_segments (0x90734 : word) = Some W_906e4.
Proof. vm_refl. Qed.
Lemma D_906e4 : decode_any W_906e4 = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_906e8 : bv 32 := 0x00050e63.
Lemma F_906e8 : fetch_word Asan.M.loaded_segments (0x90738 : word) = Some W_906e8.
Proof. vm_refl. Qed.
Lemma D_906e8 : decode_any W_906e8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90704 : bv 32 := 0x00040513.
Lemma F_90704 : fetch_word Asan.M.loaded_segments (0x90754 : word) = Some W_90704.
Proof. vm_refl. Qed.
Lemma D_90704 : decode_any W_90704 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90708 : bv 32 := 0x07c000ef.
Lemma F_90708 : fetch_word Asan.M.loaded_segments (0x90758 : word) = Some W_90708.
Proof. vm_refl. Qed.
Lemma D_90708 : decode_any W_90708 = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9070c : bv 32 := 0x0016b517.
Lemma F_9070c : fetch_word Asan.M.loaded_segments (0x9075c : word) = Some W_9070c.
Proof. vm_refl. Qed.
Lemma D_9070c : decode_any W_9070c = Some (Auipc 10 363, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90710 : bv 32 := 0x26450493.
Lemma F_90710 : fetch_word Asan.M.loaded_segments (0x90760 : word) = Some W_90710.
Proof. vm_refl. Qed.
Lemma D_90710 : decode_any W_90710 = Some (OpImm ALU_ADD 9 10 612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90714 : bv 32 := 0x0084b583.
Lemma F_90714 : fetch_word Asan.M.loaded_segments (0x90764 : word) = Some W_90714.
Proof. vm_refl. Qed.
Lemma D_90714 : decode_any W_90714 = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90718 : bv 32 := 0x04058663.
Lemma F_90718 : fetch_word Asan.M.loaded_segments (0x90768 : word) = Some W_90718.
Proof. vm_refl. Qed.
Lemma D_90718 : decode_any W_90718 = Some (Branch BC_EQ 11 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90764 : bv 32 := 0x00000513.
Lemma F_90764 : fetch_word Asan.M.loaded_segments (0x907b4 : word) = Some W_90764.
Proof. vm_refl. Qed.
Lemma D_90764 : decode_any W_90764 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90768 : bv 32 := 0x01813083.
Lemma F_90768 : fetch_word Asan.M.loaded_segments (0x907b8 : word) = Some W_90768.
Proof. vm_refl. Qed.
Lemma D_90768 : decode_any W_90768 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9076c : bv 32 := 0x01013403.
Lemma F_9076c : fetch_word Asan.M.loaded_segments (0x907bc : word) = Some W_9076c.
Proof. vm_refl. Qed.
Lemma D_9076c : decode_any W_9076c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90770 : bv 32 := 0x00813483.
Lemma F_90770 : fetch_word Asan.M.loaded_segments (0x907c0 : word) = Some W_90770.
Proof. vm_refl. Qed.
Lemma D_90770 : decode_any W_90770 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90774 : bv 32 := 0x02010113.
Lemma F_90774 : fetch_word Asan.M.loaded_segments (0x907c4 : word) = Some W_90774.
Proof. vm_refl. Qed.
Lemma D_90774 : decode_any W_90774 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90778 : bv 32 := 0x00008067.
Lemma F_90778 : fetch_word Asan.M.loaded_segments (0x907c8 : word) = Some W_90778.
Proof. vm_refl. Qed.
Lemma D_90778 : decode_any W_90778 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9077c : bv 32 := 0x00000513.
Lemma F_9077c : fetch_word Asan.M.loaded_segments (0x907cc : word) = Some W_9077c.
Proof. vm_refl. Qed.
Lemma D_9077c : decode_any W_9077c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90780 : bv 32 := 0x00008067.
Lemma F_90780 : fetch_word Asan.M.loaded_segments (0x907d0 : word) = Some W_90780.
Proof. vm_refl. Qed.
Lemma D_90780 : decode_any W_90780 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_90784 : bv 32 := 0x00008067.
Lemma F_90784 : fetch_word Asan.M.loaded_segments (0x907d4 : word) = Some W_90784.
Proof. vm_refl. Qed.
Lemma D_90784 : decode_any W_90784 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

