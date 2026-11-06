(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Plain.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_3975c : bv 32 := 0xfffd7197.
Lemma F_3975c : fetch_word Plain.M.loaded_segments (0x397a4 : word) = Some W_3975c.
Proof. vm_refl. Qed.
Lemma D_3975c : decode_any W_3975c = Some (Auipc 3 1048535, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39760 : bv 32 := 0x05c18193.
Lemma F_39760 : fetch_word Plain.M.loaded_segments (0x397a8 : word) = Some W_39760.
Proof. vm_refl. Qed.
Lemma D_39760 : decode_any W_39760 = Some (OpImm ALU_ADD 3 3 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39764 : bv 32 := 0x00010513.
Lemma F_39764 : fetch_word Plain.M.loaded_segments (0x397ac : word) = Some W_39764.
Proof. vm_refl. Qed.
Lemma D_39764 : decode_any W_39764 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39768 : bv 32 := 0xfffc7597.
Lemma F_39768 : fetch_word Plain.M.loaded_segments (0x397b0 : word) = Some W_39768.
Proof. vm_refl. Qed.
Lemma D_39768 : decode_any W_39768 = Some (Auipc 11 1048519, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3976c : bv 32 := 0x85058593.
Lemma F_3976c : fetch_word Plain.M.loaded_segments (0x397b4 : word) = Some W_3976c.
Proof. vm_refl. Qed.
Lemma D_3976c : decode_any W_3976c = Some (OpImm ALU_ADD 11 11 2128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39770 : bv 32 := 0xff017113.
Lemma F_39770 : fetch_word Plain.M.loaded_segments (0x397b8 : word) = Some W_39770.
Proof. vm_refl. Qed.
Lemma D_39770 : decode_any W_39770 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39774 : bv 32 := 0x0040006f.
Lemma F_39774 : fetch_word Plain.M.loaded_segments (0x397bc : word) = Some W_39774.
Proof. vm_refl. Qed.
Lemma D_39774 : decode_any W_39774 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39778 : bv 32 := 0x00052583.
Lemma F_39778 : fetch_word Plain.M.loaded_segments (0x397c0 : word) = Some W_39778.
Proof. vm_refl. Qed.
Lemma D_39778 : decode_any W_39778 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3977c : bv 32 := 0x0008d617.
Lemma F_3977c : fetch_word Plain.M.loaded_segments (0x397c4 : word) = Some W_3977c.
Proof. vm_refl. Qed.
Lemma D_3977c : decode_any W_3977c = Some (Auipc 12 141, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39780 : bv 32 := 0x0008d697.
Lemma F_39780 : fetch_word Plain.M.loaded_segments (0x397c8 : word) = Some W_39780.
Proof. vm_refl. Qed.
Lemma D_39780 : decode_any W_39780 = Some (Auipc 13 141, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39784 : bv 32 := 0x0008d717.
Lemma F_39784 : fetch_word Plain.M.loaded_segments (0x397cc : word) = Some W_39784.
Proof. vm_refl. Qed.
Lemma D_39784 : decode_any W_39784 = Some (Auipc 14 141, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39788 : bv 32 := 0xebc63783.
Lemma F_39788 : fetch_word Plain.M.loaded_segments (0x397d0 : word) = Some W_39788.
Proof. vm_refl. Qed.
Lemma D_39788 : decode_any W_39788 = Some (Load SZ8 true 15 12 3772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3978c : bv 32 := 0xec06b683.
Lemma F_3978c : fetch_word Plain.M.loaded_segments (0x397d4 : word) = Some W_3978c.
Proof. vm_refl. Qed.
Lemma D_3978c : decode_any W_3978c = Some (Load SZ8 true 13 13 3776, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39790 : bv 32 := 0xec473703.
Lemma F_39790 : fetch_word Plain.M.loaded_segments (0x397d8 : word) = Some W_39790.
Proof. vm_refl. Qed.
Lemma D_39790 : decode_any W_39790 = Some (Load SZ8 true 14 14 3780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39794 : bv 32 := 0x00850613.
Lemma F_39794 : fetch_word Plain.M.loaded_segments (0x397dc : word) = Some W_39794.
Proof. vm_refl. Qed.
Lemma D_39794 : decode_any W_39794 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39798 : bv 32 := 0x00078513.
Lemma F_39798 : fetch_word Plain.M.loaded_segments (0x397e0 : word) = Some W_39798.
Proof. vm_refl. Qed.
Lemma D_39798 : decode_any W_39798 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3979c : bv 32 := 0x00000793.
Lemma F_3979c : fetch_word Plain.M.loaded_segments (0x397e4 : word) = Some W_3979c.
Proof. vm_refl. Qed.
Lemma D_3979c : decode_any W_3979c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397a0 : bv 32 := 0x0f07006f.
Lemma F_397a0 : fetch_word Plain.M.loaded_segments (0x397e8 : word) = Some W_397a0.
Proof. vm_refl. Qed.
Lemma D_397a0 : decode_any W_397a0 = Some (Jal 0 458992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397a4 : bv 32 := 0xff010113.
Lemma F_397a4 : fetch_word Plain.M.loaded_segments (0x397ec : word) = Some W_397a4.
Proof. vm_refl. Qed.
Lemma D_397a4 : decode_any W_397a4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397a8 : bv 32 := 0x00113423.
Lemma F_397a8 : fetch_word Plain.M.loaded_segments (0x397f0 : word) = Some W_397a8.
Proof. vm_refl. Qed.
Lemma D_397a8 : decode_any W_397a8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397ac : bv 32 := 0x00813023.
Lemma F_397ac : fetch_word Plain.M.loaded_segments (0x397f4 : word) = Some W_397ac.
Proof. vm_refl. Qed.
Lemma D_397ac : decode_any W_397ac = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397b0 : bv 32 := 0x01010413.
Lemma F_397b0 : fetch_word Plain.M.loaded_segments (0x397f8 : word) = Some W_397b0.
Proof. vm_refl. Qed.
Lemma D_397b0 : decode_any W_397b0 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397b4 : bv 32 := 0x0008e517.
Lemma F_397b4 : fetch_word Plain.M.loaded_segments (0x397fc : word) = Some W_397b4.
Proof. vm_refl. Qed.
Lemma D_397b4 : decode_any W_397b4 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397b8 : bv 32 := 0x35450513.
Lemma F_397b8 : fetch_word Plain.M.loaded_segments (0x39800 : word) = Some W_397b8.
Proof. vm_refl. Qed.
Lemma D_397b8 : decode_any W_397b8 = Some (OpImm ALU_ADD 10 10 852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397bc : bv 32 := 0x00054503.
Lemma F_397bc : fetch_word Plain.M.loaded_segments (0x39804 : word) = Some W_397bc.
Proof. vm_refl. Qed.
Lemma D_397bc : decode_any W_397bc = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397c0 : bv 32 := 0x00157513.
Lemma F_397c0 : fetch_word Plain.M.loaded_segments (0x39808 : word) = Some W_397c0.
Proof. vm_refl. Qed.
Lemma D_397c0 : decode_any W_397c0 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397c4 : bv 32 := 0x00050663.
Lemma F_397c4 : fetch_word Plain.M.loaded_segments (0x3980c : word) = Some W_397c4.
Proof. vm_refl. Qed.
Lemma D_397c4 : decode_any W_397c4 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397d0 : bv 32 := 0x0008e517.
Lemma F_397d0 : fetch_word Plain.M.loaded_segments (0x39818 : word) = Some W_397d0.
Proof. vm_refl. Qed.
Lemma D_397d0 : decode_any W_397d0 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397d4 : bv 32 := 0x33850593.
Lemma F_397d4 : fetch_word Plain.M.loaded_segments (0x3981c : word) = Some W_397d4.
Proof. vm_refl. Qed.
Lemma D_397d4 : decode_any W_397d4 = Some (OpImm ALU_ADD 11 10 824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397d8 : bv 32 := 0x00100513.
Lemma F_397d8 : fetch_word Plain.M.loaded_segments (0x39820 : word) = Some W_397d8.
Proof. vm_refl. Qed.
Lemma D_397d8 : decode_any W_397d8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397dc : bv 32 := 0x00a58023.
Lemma F_397dc : fetch_word Plain.M.loaded_segments (0x39824 : word) = Some W_397dc.
Proof. vm_refl. Qed.
Lemma D_397dc : decode_any W_397dc = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397e0 : bv 32 := 0x0008d517.
Lemma F_397e0 : fetch_word Plain.M.loaded_segments (0x39828 : word) = Some W_397e0.
Proof. vm_refl. Qed.
Lemma D_397e0 : decode_any W_397e0 = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397e4 : bv 32 := 0xe7053503.
Lemma F_397e4 : fetch_word Plain.M.loaded_segments (0x3982c : word) = Some W_397e4.
Proof. vm_refl. Qed.
Lemma D_397e4 : decode_any W_397e4 = Some (Load SZ8 true 10 10 3696, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_397e8 : bv 32 := 0x02050063.
Lemma F_397e8 : fetch_word Plain.M.loaded_segments (0x39830 : word) = Some W_397e8.
Proof. vm_refl. Qed.
Lemma D_397e8 : decode_any W_397e8 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39808 : bv 32 := 0x00813083.
Lemma F_39808 : fetch_word Plain.M.loaded_segments (0x39850 : word) = Some W_39808.
Proof. vm_refl. Qed.
Lemma D_39808 : decode_any W_39808 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3980c : bv 32 := 0x00013403.
Lemma F_3980c : fetch_word Plain.M.loaded_segments (0x39854 : word) = Some W_3980c.
Proof. vm_refl. Qed.
Lemma D_3980c : decode_any W_3980c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39810 : bv 32 := 0x01010113.
Lemma F_39810 : fetch_word Plain.M.loaded_segments (0x39858 : word) = Some W_39810.
Proof. vm_refl. Qed.
Lemma D_39810 : decode_any W_39810 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39814 : bv 32 := 0x00008067.
Lemma F_39814 : fetch_word Plain.M.loaded_segments (0x3985c : word) = Some W_39814.
Proof. vm_refl. Qed.
Lemma D_39814 : decode_any W_39814 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39818 : bv 32 := 0xff010113.
Lemma F_39818 : fetch_word Plain.M.loaded_segments (0x39860 : word) = Some W_39818.
Proof. vm_refl. Qed.
Lemma D_39818 : decode_any W_39818 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3981c : bv 32 := 0x00113423.
Lemma F_3981c : fetch_word Plain.M.loaded_segments (0x39864 : word) = Some W_3981c.
Proof. vm_refl. Qed.
Lemma D_3981c : decode_any W_3981c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39820 : bv 32 := 0x00813023.
Lemma F_39820 : fetch_word Plain.M.loaded_segments (0x39868 : word) = Some W_39820.
Proof. vm_refl. Qed.
Lemma D_39820 : decode_any W_39820 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39824 : bv 32 := 0x01010413.
Lemma F_39824 : fetch_word Plain.M.loaded_segments (0x3986c : word) = Some W_39824.
Proof. vm_refl. Qed.
Lemma D_39824 : decode_any W_39824 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39828 : bv 32 := 0x0008e517.
Lemma F_39828 : fetch_word Plain.M.loaded_segments (0x39870 : word) = Some W_39828.
Proof. vm_refl. Qed.
Lemma D_39828 : decode_any W_39828 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3982c : bv 32 := 0x32850513.
Lemma F_3982c : fetch_word Plain.M.loaded_segments (0x39874 : word) = Some W_3982c.
Proof. vm_refl. Qed.
Lemma D_3982c : decode_any W_3982c = Some (OpImm ALU_ADD 10 10 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39830 : bv 32 := 0x00054503.
Lemma F_39830 : fetch_word Plain.M.loaded_segments (0x39878 : word) = Some W_39830.
Proof. vm_refl. Qed.
Lemma D_39830 : decode_any W_39830 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39834 : bv 32 := 0x00157513.
Lemma F_39834 : fetch_word Plain.M.loaded_segments (0x3987c : word) = Some W_39834.
Proof. vm_refl. Qed.
Lemma D_39834 : decode_any W_39834 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39838 : bv 32 := 0x00050663.
Lemma F_39838 : fetch_word Plain.M.loaded_segments (0x39880 : word) = Some W_39838.
Proof. vm_refl. Qed.
Lemma D_39838 : decode_any W_39838 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39844 : bv 32 := 0x0008e517.
Lemma F_39844 : fetch_word Plain.M.loaded_segments (0x3988c : word) = Some W_39844.
Proof. vm_refl. Qed.
Lemma D_39844 : decode_any W_39844 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39848 : bv 32 := 0x30c50593.
Lemma F_39848 : fetch_word Plain.M.loaded_segments (0x39890 : word) = Some W_39848.
Proof. vm_refl. Qed.
Lemma D_39848 : decode_any W_39848 = Some (OpImm ALU_ADD 11 10 780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3984c : bv 32 := 0x00100513.
Lemma F_3984c : fetch_word Plain.M.loaded_segments (0x39894 : word) = Some W_3984c.
Proof. vm_refl. Qed.
Lemma D_3984c : decode_any W_3984c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39850 : bv 32 := 0x00a58023.
Lemma F_39850 : fetch_word Plain.M.loaded_segments (0x39898 : word) = Some W_39850.
Proof. vm_refl. Qed.
Lemma D_39850 : decode_any W_39850 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39854 : bv 32 := 0x0008d517.
Lemma F_39854 : fetch_word Plain.M.loaded_segments (0x3989c : word) = Some W_39854.
Proof. vm_refl. Qed.
Lemma D_39854 : decode_any W_39854 = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39858 : bv 32 := 0xe0453503.
Lemma F_39858 : fetch_word Plain.M.loaded_segments (0x398a0 : word) = Some W_39858.
Proof. vm_refl. Qed.
Lemma D_39858 : decode_any W_39858 = Some (Load SZ8 true 10 10 3588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3985c : bv 32 := 0x00050e63.
Lemma F_3985c : fetch_word Plain.M.loaded_segments (0x398a4 : word) = Some W_3985c.
Proof. vm_refl. Qed.
Lemma D_3985c : decode_any W_3985c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39860 : bv 32 := 0x0040006f.
Lemma F_39860 : fetch_word Plain.M.loaded_segments (0x398a8 : word) = Some W_39860.
Proof. vm_refl. Qed.
Lemma D_39860 : decode_any W_39860 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39864 : bv 32 := 0x0008e517.
Lemma F_39864 : fetch_word Plain.M.loaded_segments (0x398ac : word) = Some W_39864.
Proof. vm_refl. Qed.
Lemma D_39864 : decode_any W_39864 = Some (Auipc 10 142, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39868 : bv 32 := 0xfb450513.
Lemma F_39868 : fetch_word Plain.M.loaded_segments (0x398b0 : word) = Some W_39868.
Proof. vm_refl. Qed.
Lemma D_39868 : decode_any W_39868 = Some (OpImm ALU_ADD 10 10 4020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3986c : bv 32 := 0x00053503.
Lemma F_3986c : fetch_word Plain.M.loaded_segments (0x398b4 : word) = Some W_3986c.
Proof. vm_refl. Qed.
Lemma D_3986c : decode_any W_3986c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39870 : bv 32 := 0x52c700ef.
Lemma F_39870 : fetch_word Plain.M.loaded_segments (0x398b8 : word) = Some W_39870.
Proof. vm_refl. Qed.
Lemma D_39870 : decode_any W_39870 = Some (Jal 1 460076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39874 : bv 32 := 0x0040006f.
Lemma F_39874 : fetch_word Plain.M.loaded_segments (0x398bc : word) = Some W_39874.
Proof. vm_refl. Qed.
Lemma D_39874 : decode_any W_39874 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39878 : bv 32 := 0x0008d517.
Lemma F_39878 : fetch_word Plain.M.loaded_segments (0x398c0 : word) = Some W_39878.
Proof. vm_refl. Qed.
Lemma D_39878 : decode_any W_39878 = Some (Auipc 10 141, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3987c : bv 32 := 0xde853503.
Lemma F_3987c : fetch_word Plain.M.loaded_segments (0x398c4 : word) = Some W_3987c.
Proof. vm_refl. Qed.
Lemma D_3987c : decode_any W_3987c = Some (Load SZ8 true 10 10 3560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39880 : bv 32 := 0x00050c63.
Lemma F_39880 : fetch_word Plain.M.loaded_segments (0x398c8 : word) = Some W_39880.
Proof. vm_refl. Qed.
Lemma D_39880 : decode_any W_39880 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39898 : bv 32 := 0x00813083.
Lemma F_39898 : fetch_word Plain.M.loaded_segments (0x398e0 : word) = Some W_39898.
Proof. vm_refl. Qed.
Lemma D_39898 : decode_any W_39898 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3989c : bv 32 := 0x00013403.
Lemma F_3989c : fetch_word Plain.M.loaded_segments (0x398e4 : word) = Some W_3989c.
Proof. vm_refl. Qed.
Lemma D_3989c : decode_any W_3989c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_398a0 : bv 32 := 0x01010113.
Lemma F_398a0 : fetch_word Plain.M.loaded_segments (0x398e8 : word) = Some W_398a0.
Proof. vm_refl. Qed.
Lemma D_398a0 : decode_any W_398a0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_398a4 : bv 32 := 0x00008067.
Lemma F_398a4 : fetch_word Plain.M.loaded_segments (0x398ec : word) = Some W_398a4.
Proof. vm_refl. Qed.
Lemma D_398a4 : decode_any W_398a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39a1c : bv 32 := 0x000ac663.
Lemma F_39a1c : fetch_word Plain.M.loaded_segments (0x39a64 : word) = Some W_39a1c.
Proof. vm_refl. Qed.
Lemma D_39a1c : decode_any W_39a1c = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39a20 : bv 32 := 0x00050413.
Lemma F_39a20 : fetch_word Plain.M.loaded_segments (0x39a68 : word) = Some W_39a20.
Proof. vm_refl. Qed.
Lemma D_39a20 : decode_any W_39a20 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39a24 : bv 32 := 0x0780006f.
Lemma F_39a24 : fetch_word Plain.M.loaded_segments (0x39a6c : word) = Some W_39a24.
Proof. vm_refl. Qed.
Lemma D_39a24 : decode_any W_39a24 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39a28 : bv 32 := 0x148000ef.
Lemma F_39a28 : fetch_word Plain.M.loaded_segments (0x39a70 : word) = Some W_39a28.
Proof. vm_refl. Qed.
Lemma D_39a28 : decode_any W_39a28 = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39a2c : bv 32 := 0x0fb00593.
Lemma F_39a2c : fetch_word Plain.M.loaded_segments (0x39a74 : word) = Some W_39a2c.
Proof. vm_refl. Qed.
Lemma D_39a2c : decode_any W_39a2c = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39a30 : bv 32 := 0x00050413.
Lemma F_39a30 : fetch_word Plain.M.loaded_segments (0x39a78 : word) = Some W_39a30.
Proof. vm_refl. Qed.
Lemma D_39a30 : decode_any W_39a30 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39a34 : bv 32 := 0x06b56463.
Lemma F_39a34 : fetch_word Plain.M.loaded_segments (0x39a7c : word) = Some W_39a34.
Proof. vm_refl. Qed.
Lemma D_39a34 : decode_any W_39a34 = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39b70 : bv 32 := 0x00000513.
Lemma F_39b70 : fetch_word Plain.M.loaded_segments (0x39bb8 : word) = Some W_39b70.
Proof. vm_refl. Qed.
Lemma D_39b70 : decode_any W_39b70 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39b74 : bv 32 := 0x00008067.
Lemma F_39b74 : fetch_word Plain.M.loaded_segments (0x39bbc : word) = Some W_39b74.
Proof. vm_refl. Qed.
Lemma D_39b74 : decode_any W_39b74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39cd0 : bv 32 := 0x0009e517.
Lemma F_39cd0 : fetch_word Plain.M.loaded_segments (0x39d18 : word) = Some W_39cd0.
Proof. vm_refl. Qed.
Lemma D_39cd0 : decode_any W_39cd0 = Some (Auipc 10 158, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39cd4 : bv 32 := 0xe8c54503.
Lemma F_39cd4 : fetch_word Plain.M.loaded_segments (0x39d1c : word) = Some W_39cd4.
Proof. vm_refl. Qed.
Lemma D_39cd4 : decode_any W_39cd4 = Some (Load SZ1 false 10 10 3724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39cd8 : bv 32 := 0x00051463.
Lemma F_39cd8 : fetch_word Plain.M.loaded_segments (0x39d20 : word) = Some W_39cd8.
Proof. vm_refl. Qed.
Lemma D_39cd8 : decode_any W_39cd8 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_39cdc : bv 32 := 0x00008067.
Lemma F_39cdc : fetch_word Plain.M.loaded_segments (0x39d24 : word) = Some W_39cdc.
Proof. vm_refl. Qed.
Lemma D_39cdc : decode_any W_39cdc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

