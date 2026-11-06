(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition Wx_68814 : bv 32 := 0xfa010113.
Lemma Fx_68814 : fetch_word AsanUbsan.M.loaded_segments (0x6885c : word) = Some Wx_68814.
Proof. vm_refl. Qed.
Lemma Dx_68814 : decode_any Wx_68814 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68818 : bv 32 := 0x04113c23.
Lemma Fx_68818 : fetch_word AsanUbsan.M.loaded_segments (0x68860 : word) = Some Wx_68818.
Proof. vm_refl. Qed.
Lemma Dx_68818 : decode_any Wx_68818 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6881c : bv 32 := 0x04813823.
Lemma Fx_6881c : fetch_word AsanUbsan.M.loaded_segments (0x68864 : word) = Some Wx_6881c.
Proof. vm_refl. Qed.
Lemma Dx_6881c : decode_any Wx_6881c = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68820 : bv 32 := 0x04913423.
Lemma Fx_68820 : fetch_word AsanUbsan.M.loaded_segments (0x68868 : word) = Some Wx_68820.
Proof. vm_refl. Qed.
Lemma Dx_68820 : decode_any Wx_68820 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68824 : bv 32 := 0x05213023.
Lemma Fx_68824 : fetch_word AsanUbsan.M.loaded_segments (0x6886c : word) = Some Wx_68824.
Proof. vm_refl. Qed.
Lemma Dx_68824 : decode_any Wx_68824 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68828 : bv 32 := 0x03313c23.
Lemma Fx_68828 : fetch_word AsanUbsan.M.loaded_segments (0x68870 : word) = Some Wx_68828.
Proof. vm_refl. Qed.
Lemma Dx_68828 : decode_any Wx_68828 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6882c : bv 32 := 0x03413823.
Lemma Fx_6882c : fetch_word AsanUbsan.M.loaded_segments (0x68874 : word) = Some Wx_6882c.
Proof. vm_refl. Qed.
Lemma Dx_6882c : decode_any Wx_6882c = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68830 : bv 32 := 0x03513423.
Lemma Fx_68830 : fetch_word AsanUbsan.M.loaded_segments (0x68878 : word) = Some Wx_68830.
Proof. vm_refl. Qed.
Lemma Dx_68830 : decode_any Wx_68830 = Some (Store SZ8 2 21 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68834 : bv 32 := 0x03613023.
Lemma Fx_68834 : fetch_word AsanUbsan.M.loaded_segments (0x6887c : word) = Some Wx_68834.
Proof. vm_refl. Qed.
Lemma Dx_68834 : decode_any Wx_68834 = Some (Store SZ8 2 22 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68838 : bv 32 := 0x01713c23.
Lemma Fx_68838 : fetch_word AsanUbsan.M.loaded_segments (0x68880 : word) = Some Wx_68838.
Proof. vm_refl. Qed.
Lemma Dx_68838 : decode_any Wx_68838 = Some (Store SZ8 2 23 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6883c : bv 32 := 0x01813823.
Lemma Fx_6883c : fetch_word AsanUbsan.M.loaded_segments (0x68884 : word) = Some Wx_6883c.
Proof. vm_refl. Qed.
Lemma Dx_6883c : decode_any Wx_6883c = Some (Store SZ8 2 24 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68840 : bv 32 := 0x01913423.
Lemma Fx_68840 : fetch_word AsanUbsan.M.loaded_segments (0x68888 : word) = Some Wx_68840.
Proof. vm_refl. Qed.
Lemma Dx_68840 : decode_any Wx_68840 = Some (Store SZ8 2 25 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68844 : bv 32 := 0x000fc517.
Lemma Fx_68844 : fetch_word AsanUbsan.M.loaded_segments (0x6888c : word) = Some Wx_68844.
Proof. vm_refl. Qed.
Lemma Dx_68844 : decode_any Wx_68844 = Some (Auipc 10 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68848 : bv 32 := 0xc8453a03.
Lemma Fx_68848 : fetch_word AsanUbsan.M.loaded_segments (0x68890 : word) = Some Wx_68848.
Proof. vm_refl. Qed.
Lemma Dx_68848 : decode_any Wx_68848 = Some (Load SZ8 true 20 10 3204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_6884c : bv 32 := 0x01ca4503.
Lemma Fx_6884c : fetch_word AsanUbsan.M.loaded_segments (0x68894 : word) = Some Wx_6884c.
Proof. vm_refl. Qed.
Lemma Dx_6884c : decode_any Wx_6884c = Some (Load SZ1 false 10 20 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68850 : bv 32 := 0x1e050e63.
Lemma Fx_68850 : fetch_word AsanUbsan.M.loaded_segments (0x68898 : word) = Some Wx_68850.
Proof. vm_refl. Qed.
Lemma Dx_68850 : decode_any Wx_68850 = Some (Branch BC_EQ 10 0 508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68a4c : bv 32 := 0x05813083.
Lemma Fx_68a4c : fetch_word AsanUbsan.M.loaded_segments (0x68a94 : word) = Some Wx_68a4c.
Proof. vm_refl. Qed.
Lemma Dx_68a4c : decode_any Wx_68a4c = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68a50 : bv 32 := 0x05013403.
Lemma Fx_68a50 : fetch_word AsanUbsan.M.loaded_segments (0x68a98 : word) = Some Wx_68a50.
Proof. vm_refl. Qed.
Lemma Dx_68a50 : decode_any Wx_68a50 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68a54 : bv 32 := 0x04813483.
Lemma Fx_68a54 : fetch_word AsanUbsan.M.loaded_segments (0x68a9c : word) = Some Wx_68a54.
Proof. vm_refl. Qed.
Lemma Dx_68a54 : decode_any Wx_68a54 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68a58 : bv 32 := 0x04013903.
Lemma Fx_68a58 : fetch_word AsanUbsan.M.loaded_segments (0x68aa0 : word) = Some Wx_68a58.
Proof. vm_refl. Qed.
Lemma Dx_68a58 : decode_any Wx_68a58 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68a5c : bv 32 := 0x03813983.
Lemma Fx_68a5c : fetch_word AsanUbsan.M.loaded_segments (0x68aa4 : word) = Some Wx_68a5c.
Proof. vm_refl. Qed.
Lemma Dx_68a5c : decode_any Wx_68a5c = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68a60 : bv 32 := 0x03013a03.
Lemma Fx_68a60 : fetch_word AsanUbsan.M.loaded_segments (0x68aa8 : word) = Some Wx_68a60.
Proof. vm_refl. Qed.
Lemma Dx_68a60 : decode_any Wx_68a60 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68a64 : bv 32 := 0x02813a83.
Lemma Fx_68a64 : fetch_word AsanUbsan.M.loaded_segments (0x68aac : word) = Some Wx_68a64.
Proof. vm_refl. Qed.
Lemma Dx_68a64 : decode_any Wx_68a64 = Some (Load SZ8 true 21 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68a68 : bv 32 := 0x02013b03.
Lemma Fx_68a68 : fetch_word AsanUbsan.M.loaded_segments (0x68ab0 : word) = Some Wx_68a68.
Proof. vm_refl. Qed.
Lemma Dx_68a68 : decode_any Wx_68a68 = Some (Load SZ8 true 22 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68a6c : bv 32 := 0x01813b83.
Lemma Fx_68a6c : fetch_word AsanUbsan.M.loaded_segments (0x68ab4 : word) = Some Wx_68a6c.
Proof. vm_refl. Qed.
Lemma Dx_68a6c : decode_any Wx_68a6c = Some (Load SZ8 true 23 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68a70 : bv 32 := 0x01013c03.
Lemma Fx_68a70 : fetch_word AsanUbsan.M.loaded_segments (0x68ab8 : word) = Some Wx_68a70.
Proof. vm_refl. Qed.
Lemma Dx_68a70 : decode_any Wx_68a70 = Some (Load SZ8 true 24 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68a74 : bv 32 := 0x00813c83.
Lemma Fx_68a74 : fetch_word AsanUbsan.M.loaded_segments (0x68abc : word) = Some Wx_68a74.
Proof. vm_refl. Qed.
Lemma Dx_68a74 : decode_any Wx_68a74 = Some (Load SZ8 true 25 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68a78 : bv 32 := 0x06010113.
Lemma Fx_68a78 : fetch_word AsanUbsan.M.loaded_segments (0x68ac0 : word) = Some Wx_68a78.
Proof. vm_refl. Qed.
Lemma Dx_68a78 : decode_any Wx_68a78 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_68a7c : bv 32 := 0x00008067.
Lemma Fx_68a7c : fetch_word AsanUbsan.M.loaded_segments (0x68ac4 : word) = Some Wx_68a7c.
Proof. vm_refl. Qed.
Lemma Dx_68a7c : decode_any Wx_68a7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_6c280 : bv 32 := 0x5cc0a06f.
Lemma Fx_6c280 : fetch_word AsanUbsan.M.loaded_segments (0x6c2c8 : word) = Some Wx_6c280.
Proof. vm_refl. Qed.
Lemma Dx_6c280 : decode_any Wx_6c280 = Some (Jal 0 42444, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_7684c : bv 32 := 0xfd010113.
Lemma Fx_7684c : fetch_word AsanUbsan.M.loaded_segments (0x76894 : word) = Some Wx_7684c.
Proof. vm_refl. Qed.
Lemma Dx_7684c : decode_any Wx_7684c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76850 : bv 32 := 0x02113423.
Lemma Fx_76850 : fetch_word AsanUbsan.M.loaded_segments (0x76898 : word) = Some Wx_76850.
Proof. vm_refl. Qed.
Lemma Dx_76850 : decode_any Wx_76850 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76854 : bv 32 := 0x02813023.
Lemma Fx_76854 : fetch_word AsanUbsan.M.loaded_segments (0x7689c : word) = Some Wx_76854.
Proof. vm_refl. Qed.
Lemma Dx_76854 : decode_any Wx_76854 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76858 : bv 32 := 0x00913c23.
Lemma Fx_76858 : fetch_word AsanUbsan.M.loaded_segments (0x768a0 : word) = Some Wx_76858.
Proof. vm_refl. Qed.
Lemma Dx_76858 : decode_any Wx_76858 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_7685c : bv 32 := 0x01213823.
Lemma Fx_7685c : fetch_word AsanUbsan.M.loaded_segments (0x768a4 : word) = Some Wx_7685c.
Proof. vm_refl. Qed.
Lemma Dx_7685c : decode_any Wx_7685c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76860 : bv 32 := 0x01313423.
Lemma Fx_76860 : fetch_word AsanUbsan.M.loaded_segments (0x768a8 : word) = Some Wx_76860.
Proof. vm_refl. Qed.
Lemma Dx_76860 : decode_any Wx_76860 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76864 : bv 32 := 0x00060413.
Lemma Fx_76864 : fetch_word AsanUbsan.M.loaded_segments (0x768ac : word) = Some Wx_76864.
Proof. vm_refl. Qed.
Lemma Dx_76864 : decode_any Wx_76864 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76868 : bv 32 := 0x00058493.
Lemma Fx_76868 : fetch_word AsanUbsan.M.loaded_segments (0x768b0 : word) = Some Wx_76868.
Proof. vm_refl. Qed.
Lemma Dx_76868 : decode_any Wx_76868 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_7686c : bv 32 := 0x00050913.
Lemma Fx_7686c : fetch_word AsanUbsan.M.loaded_segments (0x768b4 : word) = Some Wx_7686c.
Proof. vm_refl. Qed.
Lemma Dx_7686c : decode_any Wx_7686c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76870 : bv 32 := 0x364130ef.
Lemma Fx_76870 : fetch_word AsanUbsan.M.loaded_segments (0x768b8 : word) = Some Wx_76870.
Proof. vm_refl. Qed.
Lemma Dx_76870 : decode_any Wx_76870 = Some (Jal 1 78692, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76874 : bv 32 := 0x29d390ef.
Lemma Fx_76874 : fetch_word AsanUbsan.M.loaded_segments (0x768bc : word) = Some Wx_76874.
Proof. vm_refl. Qed.
Lemma Dx_76874 : decode_any Wx_76874 = Some (Jal 1 236188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76878 : bv 32 := 0x000f0997.
Lemma Fx_76878 : fetch_word AsanUbsan.M.loaded_segments (0x768c0 : word) = Some Wx_76878.
Proof. vm_refl. Qed.
Lemma Dx_76878 : decode_any Wx_76878 = Some (Auipc 19 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_7687c : bv 32 := 0xc309b683.
Lemma Fx_7687c : fetch_word AsanUbsan.M.loaded_segments (0x768c4 : word) = Some Wx_7687c.
Proof. vm_refl. Qed.
Lemma Dx_7687c : decode_any Wx_7687c = Some (Load SZ8 true 13 19 3120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76880 : bv 32 := 0x00090513.
Lemma Fx_76880 : fetch_word AsanUbsan.M.loaded_segments (0x768c8 : word) = Some Wx_76880.
Proof. vm_refl. Qed.
Lemma Dx_76880 : decode_any Wx_76880 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76884 : bv 32 := 0x00048593.
Lemma Fx_76884 : fetch_word AsanUbsan.M.loaded_segments (0x768cc : word) = Some Wx_76884.
Proof. vm_refl. Qed.
Lemma Dx_76884 : decode_any Wx_76884 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76888 : bv 32 := 0x00040613.
Lemma Fx_76888 : fetch_word AsanUbsan.M.loaded_segments (0x768d0 : word) = Some Wx_76888.
Proof. vm_refl. Qed.
Lemma Dx_76888 : decode_any Wx_76888 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_7688c : bv 32 := 0x000680e7.
Lemma Fx_7688c : fetch_word AsanUbsan.M.loaded_segments (0x768d4 : word) = Some Wx_7688c.
Proof. vm_refl. Qed.
Lemma Dx_7688c : decode_any Wx_7688c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76890 : bv 32 := 0xc309b683.
Lemma Fx_76890 : fetch_word AsanUbsan.M.loaded_segments (0x768d8 : word) = Some Wx_76890.
Proof. vm_refl. Qed.
Lemma Dx_76890 : decode_any Wx_76890 = Some (Load SZ8 true 13 19 3120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76894 : bv 32 := 0x00050413.
Lemma Fx_76894 : fetch_word AsanUbsan.M.loaded_segments (0x768dc : word) = Some Wx_76894.
Proof. vm_refl. Qed.
Lemma Dx_76894 : decode_any Wx_76894 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_76898 : bv 32 := 0x00000517.
Lemma Fx_76898 : fetch_word AsanUbsan.M.loaded_segments (0x768e0 : word) = Some Wx_76898.
Proof. vm_refl. Qed.
Lemma Dx_76898 : decode_any Wx_76898 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_7689c : bv 32 := 0x03850513.
Lemma Fx_7689c : fetch_word AsanUbsan.M.loaded_segments (0x768e4 : word) = Some Wx_7689c.
Proof. vm_refl. Qed.
Lemma Dx_7689c : decode_any Wx_7689c = Some (OpImm ALU_ADD 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_768a0 : bv 32 := 0x00000593.
Lemma Fx_768a0 : fetch_word AsanUbsan.M.loaded_segments (0x768e8 : word) = Some Wx_768a0.
Proof. vm_refl. Qed.
Lemma Dx_768a0 : decode_any Wx_768a0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_768a4 : bv 32 := 0x00000613.
Lemma Fx_768a4 : fetch_word AsanUbsan.M.loaded_segments (0x768ec : word) = Some Wx_768a4.
Proof. vm_refl. Qed.
Lemma Dx_768a4 : decode_any Wx_768a4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_768a8 : bv 32 := 0x000680e7.
Lemma Fx_768a8 : fetch_word AsanUbsan.M.loaded_segments (0x768f0 : word) = Some Wx_768a8.
Proof. vm_refl. Qed.
Lemma Dx_768a8 : decode_any Wx_768a8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_768ac : bv 32 := 0x281390ef.
Lemma Fx_768ac : fetch_word AsanUbsan.M.loaded_segments (0x768f4 : word) = Some Wx_768ac.
Proof. vm_refl. Qed.
Lemma Dx_768ac : decode_any Wx_768ac = Some (Jal 1 236160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_768b0 : bv 32 := 0x00040513.
Lemma Fx_768b0 : fetch_word AsanUbsan.M.loaded_segments (0x768f8 : word) = Some Wx_768b0.
Proof. vm_refl. Qed.
Lemma Dx_768b0 : decode_any Wx_768b0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_768b4 : bv 32 := 0x02813083.
Lemma Fx_768b4 : fetch_word AsanUbsan.M.loaded_segments (0x768fc : word) = Some Wx_768b4.
Proof. vm_refl. Qed.
Lemma Dx_768b4 : decode_any Wx_768b4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_768b8 : bv 32 := 0x02013403.
Lemma Fx_768b8 : fetch_word AsanUbsan.M.loaded_segments (0x76900 : word) = Some Wx_768b8.
Proof. vm_refl. Qed.
Lemma Dx_768b8 : decode_any Wx_768b8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_768bc : bv 32 := 0x01813483.
Lemma Fx_768bc : fetch_word AsanUbsan.M.loaded_segments (0x76904 : word) = Some Wx_768bc.
Proof. vm_refl. Qed.
Lemma Dx_768bc : decode_any Wx_768bc = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_768c0 : bv 32 := 0x01013903.
Lemma Fx_768c0 : fetch_word AsanUbsan.M.loaded_segments (0x76908 : word) = Some Wx_768c0.
Proof. vm_refl. Qed.
Lemma Dx_768c0 : decode_any Wx_768c0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_768c4 : bv 32 := 0x00813983.
Lemma Fx_768c4 : fetch_word AsanUbsan.M.loaded_segments (0x7690c : word) = Some Wx_768c4.
Proof. vm_refl. Qed.
Lemma Dx_768c4 : decode_any Wx_768c4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_768c8 : bv 32 := 0x03010113.
Lemma Fx_768c8 : fetch_word AsanUbsan.M.loaded_segments (0x76910 : word) = Some Wx_768c8.
Proof. vm_refl. Qed.
Lemma Dx_768c8 : decode_any Wx_768c8 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_768cc : bv 32 := 0x00008067.
Lemma Fx_768cc : fetch_word AsanUbsan.M.loaded_segments (0x76914 : word) = Some Wx_768cc.
Proof. vm_refl. Qed.
Lemma Dx_768cc : decode_any Wx_768cc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_768d0 : bv 32 := 0xf45f106f.
Lemma Fx_768d0 : fetch_word AsanUbsan.M.loaded_segments (0x76918 : word) = Some Wx_768d0.
Proof. vm_refl. Qed.
Lemma Dx_768d0 : decode_any Wx_768d0 = Some (Jal 0 2039620, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_89bd4 : bv 32 := 0xff010113.
Lemma Fx_89bd4 : fetch_word AsanUbsan.M.loaded_segments (0x89c1c : word) = Some Wx_89bd4.
Proof. vm_refl. Qed.
Lemma Dx_89bd4 : decode_any Wx_89bd4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89bd8 : bv 32 := 0x00113423.
Lemma Fx_89bd8 : fetch_word AsanUbsan.M.loaded_segments (0x89c20 : word) = Some Wx_89bd8.
Proof. vm_refl. Qed.
Lemma Dx_89bd8 : decode_any Wx_89bd8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89bdc : bv 32 := 0x00813023.
Lemma Fx_89bdc : fetch_word AsanUbsan.M.loaded_segments (0x89c24 : word) = Some Wx_89bdc.
Proof. vm_refl. Qed.
Lemma Dx_89bdc : decode_any Wx_89bdc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89be0 : bv 32 := 0x000e5517.
Lemma Fx_89be0 : fetch_word AsanUbsan.M.loaded_segments (0x89c28 : word) = Some Wx_89be0.
Proof. vm_refl. Qed.
Lemma Dx_89be0 : decode_any Wx_89be0 = Some (Auipc 10 229, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89be4 : bv 32 := 0x87050413.
Lemma Fx_89be4 : fetch_word AsanUbsan.M.loaded_segments (0x89c2c : word) = Some Wx_89be4.
Proof. vm_refl. Qed.
Lemma Dx_89be4 : decode_any Wx_89be4 = Some (OpImm ALU_ADD 8 10 2160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89be8 : bv 32 := 0x00040503.
Lemma Fx_89be8 : fetch_word AsanUbsan.M.loaded_segments (0x89c30 : word) = Some Wx_89be8.
Proof. vm_refl. Qed.
Lemma Dx_89be8 : decode_any Wx_89be8 = Some (Load SZ1 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89bec : bv 32 := 0x00100593.
Lemma Fx_89bec : fetch_word AsanUbsan.M.loaded_segments (0x89c34 : word) = Some Wx_89bec.
Proof. vm_refl. Qed.
Lemma Dx_89bec : decode_any Wx_89bec = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89bf0 : bv 32 := 0x0230000f.
Lemma Fx_89bf0 : fetch_word AsanUbsan.M.loaded_segments (0x89c38 : word) = Some Wx_89bf0.
Proof. vm_refl. Qed.
Lemma Dx_89bf0 : decode_any Wx_89bf0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89bf4 : bv 32 := 0x00b51a63.
Lemma Fx_89bf4 : fetch_word AsanUbsan.M.loaded_segments (0x89c3c : word) = Some Wx_89bf4.
Proof. vm_refl. Qed.
Lemma Dx_89bf4 : decode_any Wx_89bf4 = Some (Branch BC_NE 10 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89bf8 : bv 32 := 0x00813083.
Lemma Fx_89bf8 : fetch_word AsanUbsan.M.loaded_segments (0x89c40 : word) = Some Wx_89bf8.
Proof. vm_refl. Qed.
Lemma Dx_89bf8 : decode_any Wx_89bf8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89bfc : bv 32 := 0x00013403.
Lemma Fx_89bfc : fetch_word AsanUbsan.M.loaded_segments (0x89c44 : word) = Some Wx_89bfc.
Proof. vm_refl. Qed.
Lemma Dx_89bfc : decode_any Wx_89bfc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89c00 : bv 32 := 0x01010113.
Lemma Fx_89c00 : fetch_word AsanUbsan.M.loaded_segments (0x89c48 : word) = Some Wx_89c00.
Proof. vm_refl. Qed.
Lemma Dx_89c00 : decode_any Wx_89c00 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_89c04 : bv 32 := 0x00008067.
Lemma Fx_89c04 : fetch_word AsanUbsan.M.loaded_segments (0x89c4c : word) = Some Wx_89c04.
Proof. vm_refl. Qed.
Lemma Dx_89c04 : decode_any Wx_89c04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)
Definition Wx_b0310 : bv 32 := 0x000b5517.
Lemma Fx_b0310 : fetch_word AsanUbsan.M.loaded_segments (0xb0358 : word) = Some Wx_b0310.
Proof. vm_refl. Qed.
Lemma Dx_b0310 : decode_any Wx_b0310 = Some (Auipc 10 181, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0314 : bv 32 := 0xe2053503.
Lemma Fx_b0314 : fetch_word AsanUbsan.M.loaded_segments (0xb035c : word) = Some Wx_b0314.
Proof. vm_refl. Qed.
Lemma Dx_b0314 : decode_any Wx_b0314 = Some (Load SZ8 true 10 10 3616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0318 : bv 32 := 0x00450533.
Lemma Fx_b0318 : fetch_word AsanUbsan.M.loaded_segments (0xb0360 : word) = Some Wx_b0318.
Proof. vm_refl. Qed.
Lemma Dx_b0318 : decode_any Wx_b0318 = Some (Op ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b031c : bv 32 := 0x00052583.
Lemma Fx_b031c : fetch_word AsanUbsan.M.loaded_segments (0xb0364 : word) = Some Wx_b031c.
Proof. vm_refl. Qed.
Lemma Dx_b031c : decode_any Wx_b031c = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0320 : bv 32 := 0x00158593.
Lemma Fx_b0320 : fetch_word AsanUbsan.M.loaded_segments (0xb0368 : word) = Some Wx_b0320.
Proof. vm_refl. Qed.
Lemma Dx_b0320 : decode_any Wx_b0320 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0324 : bv 32 := 0x00b52023.
Lemma Fx_b0324 : fetch_word AsanUbsan.M.loaded_segments (0xb036c : word) = Some Wx_b0324.
Proof. vm_refl. Qed.
Lemma Dx_b0324 : decode_any Wx_b0324 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0328 : bv 32 := 0x00008067.
Lemma Fx_b0328 : fetch_word AsanUbsan.M.loaded_segments (0xb0370 : word) = Some Wx_b0328.
Proof. vm_refl. Qed.
Lemma Dx_b0328 : decode_any Wx_b0328 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b032c : bv 32 := 0xff010113.
Lemma Fx_b032c : fetch_word AsanUbsan.M.loaded_segments (0xb0374 : word) = Some Wx_b032c.
Proof. vm_refl. Qed.
Lemma Dx_b032c : decode_any Wx_b032c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0330 : bv 32 := 0x00113423.
Lemma Fx_b0330 : fetch_word AsanUbsan.M.loaded_segments (0xb0378 : word) = Some Wx_b0330.
Proof. vm_refl. Qed.
Lemma Dx_b0330 : decode_any Wx_b0330 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0334 : bv 32 := 0x00813023.
Lemma Fx_b0334 : fetch_word AsanUbsan.M.loaded_segments (0xb037c : word) = Some Wx_b0334.
Proof. vm_refl. Qed.
Lemma Dx_b0334 : decode_any Wx_b0334 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0338 : bv 32 := 0x000b5517.
Lemma Fx_b0338 : fetch_word AsanUbsan.M.loaded_segments (0xb0380 : word) = Some Wx_b0338.
Proof. vm_refl. Qed.
Lemma Dx_b0338 : decode_any Wx_b0338 = Some (Auipc 10 181, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b033c : bv 32 := 0xdf853403.
Lemma Fx_b033c : fetch_word AsanUbsan.M.loaded_segments (0xb0384 : word) = Some Wx_b033c.
Proof. vm_refl. Qed.
Lemma Dx_b033c : decode_any Wx_b033c = Some (Load SZ8 true 8 10 3576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0340 : bv 32 := 0x00440433.
Lemma Fx_b0340 : fetch_word AsanUbsan.M.loaded_segments (0xb0388 : word) = Some Wx_b0340.
Proof. vm_refl. Qed.
Lemma Dx_b0340 : decode_any Wx_b0340 = Some (Op ALU_ADD 8 8 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0344 : bv 32 := 0x00042503.
Lemma Fx_b0344 : fetch_word AsanUbsan.M.loaded_segments (0xb038c : word) = Some Wx_b0344.
Proof. vm_refl. Qed.
Lemma Dx_b0344 : decode_any Wx_b0344 = Some (Load SZ4 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0348 : bv 32 := 0x00050e63.
Lemma Fx_b0348 : fetch_word AsanUbsan.M.loaded_segments (0xb0390 : word) = Some Wx_b0348.
Proof. vm_refl. Qed.
Lemma Dx_b0348 : decode_any Wx_b0348 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b034c : bv 32 := 0xfff50513.
Lemma Fx_b034c : fetch_word AsanUbsan.M.loaded_segments (0xb0394 : word) = Some Wx_b034c.
Proof. vm_refl. Qed.
Lemma Dx_b034c : decode_any Wx_b034c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0350 : bv 32 := 0x00a42023.
Lemma Fx_b0350 : fetch_word AsanUbsan.M.loaded_segments (0xb0398 : word) = Some Wx_b0350.
Proof. vm_refl. Qed.
Lemma Dx_b0350 : decode_any Wx_b0350 = Some (Store SZ4 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0354 : bv 32 := 0x00813083.
Lemma Fx_b0354 : fetch_word AsanUbsan.M.loaded_segments (0xb039c : word) = Some Wx_b0354.
Proof. vm_refl. Qed.
Lemma Dx_b0354 : decode_any Wx_b0354 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0358 : bv 32 := 0x00013403.
Lemma Fx_b0358 : fetch_word AsanUbsan.M.loaded_segments (0xb03a0 : word) = Some Wx_b0358.
Proof. vm_refl. Qed.
Lemma Dx_b0358 : decode_any Wx_b0358 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b035c : bv 32 := 0x01010113.
Lemma Fx_b035c : fetch_word AsanUbsan.M.loaded_segments (0xb03a4 : word) = Some Wx_b035c.
Proof. vm_refl. Qed.
Lemma Dx_b035c : decode_any Wx_b035c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition Wx_b0360 : bv 32 := 0x00008067.
Lemma Fx_b0360 : fetch_word AsanUbsan.M.loaded_segments (0xb03a8 : word) = Some Wx_b0360.
Proof. vm_refl. Qed.
Lemma Dx_b0360 : decode_any Wx_b0360 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

