(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.boost_beast.http_request.lib.Common Require KReplay.
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_fefe8 : bv 32 := 0xfd010113.
Lemma F_fefe8 : fetch_word Asan.M.loaded_segments (0xfefe8 : word) = Some W_fefe8.
Proof. vm_refl. Qed.
Lemma D_fefe8 : decode_any W_fefe8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_fefec : bv 32 := 0x02113423.
Lemma F_fefec : fetch_word Asan.M.loaded_segments (0xfefec : word) = Some W_fefec.
Proof. vm_refl. Qed.
Lemma D_fefec : decode_any W_fefec = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_feff0 : bv 32 := 0x00600513.
Lemma F_feff0 : fetch_word Asan.M.loaded_segments (0xfeff0 : word) = Some W_feff0.
Proof. vm_refl. Qed.
Lemma D_feff0 : decode_any W_feff0 = Some (OpImm ALU_ADD 10 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_feff4 : bv 32 := 0x5d4050ef.
Lemma F_feff4 : fetch_word Asan.M.loaded_segments (0xfeff4 : word) = Some W_feff4.
Proof. vm_refl. Qed.
Lemma D_feff4 : decode_any W_feff4 = Some (Jal 1 21972, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_feff8 : bv 32 := 0x00000513.
Lemma F_feff8 : fetch_word Asan.M.loaded_segments (0xfeff8 : word) = Some W_feff8.
Proof. vm_refl. Qed.
Lemma D_feff8 : decode_any W_feff8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_feffc : bv 32 := 0x570050ef.
Lemma F_feffc : fetch_word Asan.M.loaded_segments (0xfeffc : word) = Some W_feffc.
Proof. vm_refl. Qed.
Lemma D_feffc : decode_any W_feffc = Some (Jal 1 21872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff000 : bv 32 := 0x0057e517.
Lemma F_ff000 : fetch_word Asan.M.loaded_segments (0xff000 : word) = Some W_ff000.
Proof. vm_refl. Qed.
Lemma D_ff000 : decode_any W_ff000 = Some (Auipc 10 1406, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff004 : bv 32 := 0x4f850513.
Lemma F_ff004 : fetch_word Asan.M.loaded_segments (0xff004 : word) = Some W_ff004.
Proof. vm_refl. Qed.
Lemma D_ff004 : decode_any W_ff004 = Some (OpImm ALU_ADD 10 10 1272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff008 : bv 32 := 0x1c00f0ef.
Lemma F_ff008 : fetch_word Asan.M.loaded_segments (0xff008 : word) = Some W_ff008.
Proof. vm_refl. Qed.
Lemma D_ff008 : decode_any W_ff008 = Some (Jal 1 61888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff00c : bv 32 := 0x00000613.
Lemma F_ff00c : fetch_word Asan.M.loaded_segments (0xff00c : word) = Some W_ff00c.
Proof. vm_refl. Qed.
Lemma D_ff00c : decode_any W_ff00c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff010 : bv 32 := 0x00013423.
Lemma F_ff010 : fetch_word Asan.M.loaded_segments (0xff010 : word) = Some W_ff010.
Proof. vm_refl. Qed.
Lemma D_ff010 : decode_any W_ff010 = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff014 : bv 32 := 0x00013823.
Lemma F_ff014 : fetch_word Asan.M.loaded_segments (0xff014 : word) = Some W_ff014.
Proof. vm_refl. Qed.
Lemma D_ff014 : decode_any W_ff014 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff018 : bv 32 := 0x00013c23.
Lemma F_ff018 : fetch_word Asan.M.loaded_segments (0xff018 : word) = Some W_ff018.
Proof. vm_refl. Qed.
Lemma D_ff018 : decode_any W_ff018 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff01c : bv 32 := 0x02013023.
Lemma F_ff01c : fetch_word Asan.M.loaded_segments (0xff01c : word) = Some W_ff01c.
Proof. vm_refl. Qed.
Lemma D_ff01c : decode_any W_ff01c = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff020 : bv 32 := 0x08600893.
Lemma F_ff020 : fetch_word Asan.M.loaded_segments (0xff020 : word) = Some W_ff020.
Proof. vm_refl. Qed.
Lemma D_ff020 : decode_any W_ff020 = Some (OpImm ALU_ADD 17 0 134, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff024 : bv 32 := 0x00600513.
Lemma F_ff024 : fetch_word Asan.M.loaded_segments (0xff024 : word) = Some W_ff024.
Proof. vm_refl. Qed.
Lemma D_ff024 : decode_any W_ff024 = Some (OpImm ALU_ADD 10 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff028 : bv 32 := 0x00810593.
Lemma F_ff028 : fetch_word Asan.M.loaded_segments (0xff028 : word) = Some W_ff028.
Proof. vm_refl. Qed.
Lemma D_ff028 : decode_any W_ff028 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff02c : bv 32 := 0x00800693.
Lemma F_ff02c : fetch_word Asan.M.loaded_segments (0xff02c : word) = Some W_ff02c.
Proof. vm_refl. Qed.
Lemma D_ff02c : decode_any W_ff02c = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff030 : bv 32 := 0x00000073.
Lemma F_ff030 : fetch_word Asan.M.loaded_segments (0xff030 : word) = Some W_ff030.
Proof. vm_refl. Qed.
Lemma D_ff030 : decode_any W_ff030 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff030 : is_ecall W_ff030 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff034 : bv 32 := 0x00020513.
Lemma F_ff034 : fetch_word Asan.M.loaded_segments (0xff034 : word) = Some W_ff034.
Proof. vm_refl. Qed.
Lemma D_ff034 : decode_any W_ff034 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff038 : bv 32 := 0xf5852503.
Lemma F_ff038 : fetch_word Asan.M.loaded_segments (0xff038 : word) = Some W_ff038.
Proof. vm_refl. Qed.
Lemma D_ff038 : decode_any W_ff038 = Some (Load SZ4 true 10 10 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff03c : bv 32 := 0x02000613.
Lemma F_ff03c : fetch_word Asan.M.loaded_segments (0xff03c : word) = Some W_ff03c.
Proof. vm_refl. Qed.
Lemma D_ff03c : decode_any W_ff03c = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff040 : bv 32 := 0x08200893.
Lemma F_ff040 : fetch_word Asan.M.loaded_segments (0xff040 : word) = Some W_ff040.
Proof. vm_refl. Qed.
Lemma D_ff040 : decode_any W_ff040 = Some (OpImm ALU_ADD 17 0 130, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff044 : bv 32 := 0x00600593.
Lemma F_ff044 : fetch_word Asan.M.loaded_segments (0xff044 : word) = Some W_ff044.
Proof. vm_refl. Qed.
Lemma D_ff044 : decode_any W_ff044 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff048 : bv 32 := 0x00000073.
Lemma F_ff048 : fetch_word Asan.M.loaded_segments (0xff048 : word) = Some W_ff048.
Proof. vm_refl. Qed.
Lemma D_ff048 : decode_any W_ff048 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff048 : is_ecall W_ff048 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff04c : bv 32 := 0x00c13023.
Lemma F_ff04c : fetch_word Asan.M.loaded_segments (0xff04c : word) = Some W_ff04c.
Proof. vm_refl. Qed.
Lemma D_ff04c : decode_any W_ff04c = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff050 : bv 32 := 0x08700893.
Lemma F_ff050 : fetch_word Asan.M.loaded_segments (0xff050 : word) = Some W_ff050.
Proof. vm_refl. Qed.
Lemma D_ff050 : decode_any W_ff050 = Some (OpImm ALU_ADD 17 0 135, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff054 : bv 32 := 0x00010593.
Lemma F_ff054 : fetch_word Asan.M.loaded_segments (0xff054 : word) = Some W_ff054.
Proof. vm_refl. Qed.
Lemma D_ff054 : decode_any W_ff054 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff058 : bv 32 := 0x00100513.
Lemma F_ff058 : fetch_word Asan.M.loaded_segments (0xff058 : word) = Some W_ff058.
Proof. vm_refl. Qed.
Lemma D_ff058 : decode_any W_ff058 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff05c : bv 32 := 0x00800693.
Lemma F_ff05c : fetch_word Asan.M.loaded_segments (0xff05c : word) = Some W_ff05c.
Proof. vm_refl. Qed.
Lemma D_ff05c : decode_any W_ff05c = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff060 : bv 32 := 0x00000613.
Lemma F_ff060 : fetch_word Asan.M.loaded_segments (0xff060 : word) = Some W_ff060.
Proof. vm_refl. Qed.
Lemma D_ff060 : decode_any W_ff060 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff064 : bv 32 := 0x00000073.
Lemma F_ff064 : fetch_word Asan.M.loaded_segments (0xff064 : word) = Some W_ff064.
Proof. vm_refl. Qed.
Lemma D_ff064 : decode_any W_ff064 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff064 : is_ecall W_ff064 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff068 : bv 32 := 0x00000023.
Lemma F_ff068 : fetch_word Asan.M.loaded_segments (0xff068 : word) = Some W_ff068.
Proof. vm_refl. Qed.
Lemma D_ff068 : decode_any W_ff068 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff06c : bv 32 := 0x00900513.
Lemma F_ff06c : fetch_word Asan.M.loaded_segments (0xff06c : word) = Some W_ff06c.
Proof. vm_refl. Qed.
Lemma D_ff06c : decode_any W_ff06c = Some (OpImm ALU_ADD 10 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff070 : bv 32 := 0x558050ef.
Lemma F_ff070 : fetch_word Asan.M.loaded_segments (0xff070 : word) = Some W_ff070.
Proof. vm_refl. Qed.
Lemma D_ff070 : decode_any W_ff070 = Some (Jal 1 21848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff074 : bv 32 := 0x07f00513.
Lemma F_ff074 : fetch_word Asan.M.loaded_segments (0xff074 : word) = Some W_ff074.
Proof. vm_refl. Qed.
Lemma D_ff074 : decode_any W_ff074 = Some (OpImm ALU_ADD 10 0 127, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff078 : bv 32 := 0x004000ef.
Lemma F_ff078 : fetch_word Asan.M.loaded_segments (0xff078 : word) = Some W_ff078.
Proof. vm_refl. Qed.
Lemma D_ff078 : decode_any W_ff078 = Some (Jal 1 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff07c : bv 32 := 0x00050593.
Lemma F_ff07c : fetch_word Asan.M.loaded_segments (0xff07c : word) = Some W_ff07c.
Proof. vm_refl. Qed.
Lemma D_ff07c : decode_any W_ff07c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff080 : bv 32 := 0x05e00893.
Lemma F_ff080 : fetch_word Asan.M.loaded_segments (0xff080 : word) = Some W_ff080.
Proof. vm_refl. Qed.
Lemma D_ff080 : decode_any W_ff080 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff084 : bv 32 := 0x00000073.
Lemma F_ff084 : fetch_word Asan.M.loaded_segments (0xff084 : word) = Some W_ff084.
Proof. vm_refl. Qed.
Lemma D_ff084 : decode_any W_ff084 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff084 : is_ecall W_ff084 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff088 : bv 32 := 0x05d00893.
Lemma F_ff088 : fetch_word Asan.M.loaded_segments (0xff088 : word) = Some W_ff088.
Proof. vm_refl. Qed.
Lemma D_ff088 : decode_any W_ff088 = Some (OpImm ALU_ADD 17 0 93, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff08c : bv 32 := 0x00058513.
Lemma F_ff08c : fetch_word Asan.M.loaded_segments (0xff08c : word) = Some W_ff08c.
Proof. vm_refl. Qed.
Lemma D_ff08c : decode_any W_ff08c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff090 : bv 32 := 0x00000073.
Lemma F_ff090 : fetch_word Asan.M.loaded_segments (0xff090 : word) = Some W_ff090.
Proof. vm_refl. Qed.
Lemma D_ff090 : decode_any W_ff090 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff090 : is_ecall W_ff090 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff094 : bv 32 := 0xff9ff06f.
Lemma F_ff094 : fetch_word Asan.M.loaded_segments (0xff094 : word) = Some W_ff094.
Proof. vm_refl. Qed.
Lemma D_ff094 : decode_any W_ff094 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff098 : bv 32 := 0xff010113.
Lemma F_ff098 : fetch_word Asan.M.loaded_segments (0xff098 : word) = Some W_ff098.
Proof. vm_refl. Qed.
Lemma D_ff098 : decode_any W_ff098 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff09c : bv 32 := 0x00113423.
Lemma F_ff09c : fetch_word Asan.M.loaded_segments (0xff09c : word) = Some W_ff09c.
Proof. vm_refl. Qed.
Lemma D_ff09c : decode_any W_ff09c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0a0 : bv 32 := 0x00068713.
Lemma F_ff0a0 : fetch_word Asan.M.loaded_segments (0xff0a0 : word) = Some W_ff0a0.
Proof. vm_refl. Qed.
Lemma D_ff0a0 : decode_any W_ff0a0 = Some (OpImm ALU_ADD 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0a4 : bv 32 := 0x00060793.
Lemma F_ff0a4 : fetch_word Asan.M.loaded_segments (0xff0a4 : word) = Some W_ff0a4.
Proof. vm_refl. Qed.
Lemma D_ff0a4 : decode_any W_ff0a4 = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0a8 : bv 32 := 0x00058693.
Lemma F_ff0a8 : fetch_word Asan.M.loaded_segments (0xff0a8 : word) = Some W_ff0a8.
Proof. vm_refl. Qed.
Lemma D_ff0a8 : decode_any W_ff0a8 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0ac : bv 32 := 0x00050613.
Lemma F_ff0ac : fetch_word Asan.M.loaded_segments (0xff0ac : word) = Some W_ff0ac.
Proof. vm_refl. Qed.
Lemma D_ff0ac : decode_any W_ff0ac = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0b0 : bv 32 := 0x00021517.
Lemma F_ff0b0 : fetch_word Asan.M.loaded_segments (0xff0b0 : word) = Some W_ff0b0.
Proof. vm_refl. Qed.
Lemma D_ff0b0 : decode_any W_ff0b0 = Some (Auipc 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0b4 : bv 32 := 0xfff19597.
Lemma F_ff0b4 : fetch_word Asan.M.loaded_segments (0xff0b4 : word) = Some W_ff0b4.
Proof. vm_refl. Qed.
Lemma D_ff0b4 : decode_any W_ff0b4 = Some (Auipc 11 1048345, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0b8 : bv 32 := 0xb8050513.
Lemma F_ff0b8 : fetch_word Asan.M.loaded_segments (0xff0b8 : word) = Some W_ff0b8.
Proof. vm_refl. Qed.
Lemma D_ff0b8 : decode_any W_ff0b8 = Some (OpImm ALU_ADD 10 10 2944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0bc : bv 32 := 0xa6758593.
Lemma F_ff0bc : fetch_word Asan.M.loaded_segments (0xff0bc : word) = Some W_ff0bc.
Proof. vm_refl. Qed.
Lemma D_ff0bc : decode_any W_ff0bc = Some (OpImm ALU_ADD 11 11 2663, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0c0 : bv 32 := 0xf51600ef.
Lemma F_ff0c0 : fetch_word Asan.M.loaded_segments (0xff0c0 : word) = Some W_ff0c0.
Proof. vm_refl. Qed.
Lemma D_ff0c0 : decode_any W_ff0c0 = Some (Jal 1 1445712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0c4 : bv 32 := 0xf25ff0ef.
Lemma F_ff0c4 : fetch_word Asan.M.loaded_segments (0xff0c4 : word) = Some W_ff0c4.
Proof. vm_refl. Qed.
Lemma D_ff0c4 : decode_any W_ff0c4 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0c8 : bv 32 := 0xfd010113.
Lemma F_ff0c8 : fetch_word Asan.M.loaded_segments (0xff0c8 : word) = Some W_ff0c8.
Proof. vm_refl. Qed.
Lemma D_ff0c8 : decode_any W_ff0c8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0cc : bv 32 := 0x02113423.
Lemma F_ff0cc : fetch_word Asan.M.loaded_segments (0xff0cc : word) = Some W_ff0cc.
Proof. vm_refl. Qed.
Lemma D_ff0cc : decode_any W_ff0cc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0d0 : bv 32 := 0x02813023.
Lemma F_ff0d0 : fetch_word Asan.M.loaded_segments (0xff0d0 : word) = Some W_ff0d0.
Proof. vm_refl. Qed.
Lemma D_ff0d0 : decode_any W_ff0d0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0d4 : bv 32 := 0x00913c23.
Lemma F_ff0d4 : fetch_word Asan.M.loaded_segments (0xff0d4 : word) = Some W_ff0d4.
Proof. vm_refl. Qed.
Lemma D_ff0d4 : decode_any W_ff0d4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0d8 : bv 32 := 0x01213823.
Lemma F_ff0d8 : fetch_word Asan.M.loaded_segments (0xff0d8 : word) = Some W_ff0d8.
Proof. vm_refl. Qed.
Lemma D_ff0d8 : decode_any W_ff0d8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0dc : bv 32 := 0x01313423.
Lemma F_ff0dc : fetch_word Asan.M.loaded_segments (0xff0dc : word) = Some W_ff0dc.
Proof. vm_refl. Qed.
Lemma D_ff0dc : decode_any W_ff0dc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0e0 : bv 32 := 0x0057e517.
Lemma F_ff0e0 : fetch_word Asan.M.loaded_segments (0xff0e0 : word) = Some W_ff0e0.
Proof. vm_refl. Qed.
Lemma D_ff0e0 : decode_any W_ff0e0 = Some (Auipc 10 1406, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0e4 : bv 32 := 0x42050913.
Lemma F_ff0e4 : fetch_word Asan.M.loaded_segments (0xff0e4 : word) = Some W_ff0e4.
Proof. vm_refl. Qed.
Lemma D_ff0e4 : decode_any W_ff0e4 = Some (OpImm ALU_ADD 18 10 1056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0e8 : bv 32 := 0x00490413.
Lemma F_ff0e8 : fetch_word Asan.M.loaded_segments (0xff0e8 : word) = Some W_ff0e8.
Proof. vm_refl. Qed.
Lemma D_ff0e8 : decode_any W_ff0e8 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0ec : bv 32 := 0x00040513.
Lemma F_ff0ec : fetch_word Asan.M.loaded_segments (0xff0ec : word) = Some W_ff0ec.
Proof. vm_refl. Qed.
Lemma D_ff0ec : decode_any W_ff0ec = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0f0 : bv 32 := 0x0d80f0ef.
Lemma F_ff0f0 : fetch_word Asan.M.loaded_segments (0xff0f0 : word) = Some W_ff0f0.
Proof. vm_refl. Qed.
Lemma D_ff0f0 : decode_any W_ff0f0 = Some (Jal 1 61656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0f4 : bv 32 := 0x01093503.
Lemma F_ff0f4 : fetch_word Asan.M.loaded_segments (0xff0f4 : word) = Some W_ff0f4.
Proof. vm_refl. Qed.
Lemma D_ff0f4 : decode_any W_ff0f4 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0f8 : bv 32 := 0x06050863.
Lemma F_ff0f8 : fetch_word Asan.M.loaded_segments (0xff0f8 : word) = Some W_ff0f8.
Proof. vm_refl. Qed.
Lemma D_ff0f8 : decode_any W_ff0f8 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff0fc : bv 32 := 0x00892583.
Lemma F_ff0fc : fetch_word Asan.M.loaded_segments (0xff0fc : word) = Some W_ff0fc.
Proof. vm_refl. Qed.
Lemma D_ff0fc : decode_any W_ff0fc = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff100 : bv 32 := 0x0180006f.
Lemma F_ff100 : fetch_word Asan.M.loaded_segments (0xff100 : word) = Some W_ff100.
Proof. vm_refl. Qed.
Lemma D_ff100 : decode_any W_ff100 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff104 : bv 32 := 0x00053503.
Lemma F_ff104 : fetch_word Asan.M.loaded_segments (0xff104 : word) = Some W_ff104.
Proof. vm_refl. Qed.
Lemma D_ff104 : decode_any W_ff104 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff108 : bv 32 := 0x02000593.
Lemma F_ff108 : fetch_word Asan.M.loaded_segments (0xff108 : word) = Some W_ff108.
Proof. vm_refl. Qed.
Lemma D_ff108 : decode_any W_ff108 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff10c : bv 32 := 0x00b92423.
Lemma F_ff10c : fetch_word Asan.M.loaded_segments (0xff10c : word) = Some W_ff10c.
Proof. vm_refl. Qed.
Lemma D_ff10c : decode_any W_ff10c = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff110 : bv 32 := 0x00a93823.
Lemma F_ff110 : fetch_word Asan.M.loaded_segments (0xff110 : word) = Some W_ff110.
Proof. vm_refl. Qed.
Lemma D_ff110 : decode_any W_ff110 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff114 : bv 32 := 0x04050a63.
Lemma F_ff114 : fetch_word Asan.M.loaded_segments (0xff114 : word) = Some W_ff114.
Proof. vm_refl. Qed.
Lemma D_ff114 : decode_any W_ff114 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff118 : bv 32 := 0xfff5861b.
Lemma F_ff118 : fetch_word Asan.M.loaded_segments (0xff118 : word) = Some W_ff118.
Proof. vm_refl. Qed.
Lemma D_ff118 : decode_any W_ff118 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff11c : bv 32 := 0x00c92423.
Lemma F_ff11c : fetch_word Asan.M.loaded_segments (0xff11c : word) = Some W_ff11c.
Proof. vm_refl. Qed.
Lemma D_ff11c : decode_any W_ff11c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff120 : bv 32 := 0xfeb052e3.
Lemma F_ff120 : fetch_word Asan.M.loaded_segments (0xff120 : word) = Some W_ff120.
Proof. vm_refl. Qed.
Lemma D_ff120 : decode_any W_ff120 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff124 : bv 32 := 0x01093503.
Lemma F_ff124 : fetch_word Asan.M.loaded_segments (0xff124 : word) = Some W_ff124.
Proof. vm_refl. Qed.
Lemma D_ff124 : decode_any W_ff124 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff128 : bv 32 := 0x00361613.
Lemma F_ff128 : fetch_word Asan.M.loaded_segments (0xff128 : word) = Some W_ff128.
Proof. vm_refl. Qed.
Lemma D_ff128 : decode_any W_ff128 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff12c : bv 32 := 0x00c50533.
Lemma F_ff12c : fetch_word Asan.M.loaded_segments (0xff12c : word) = Some W_ff12c.
Proof. vm_refl. Qed.
Lemma D_ff12c : decode_any W_ff12c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff130 : bv 32 := 0x00853983.
Lemma F_ff130 : fetch_word Asan.M.loaded_segments (0xff130 : word) = Some W_ff130.
Proof. vm_refl. Qed.
Lemma D_ff130 : decode_any W_ff130 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff134 : bv 32 := 0x10853483.
Lemma F_ff134 : fetch_word Asan.M.loaded_segments (0xff134 : word) = Some W_ff134.
Proof. vm_refl. Qed.
Lemma D_ff134 : decode_any W_ff134 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff138 : bv 32 := 0x00040513.
Lemma F_ff138 : fetch_word Asan.M.loaded_segments (0xff138 : word) = Some W_ff138.
Proof. vm_refl. Qed.
Lemma D_ff138 : decode_any W_ff138 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff13c : bv 32 := 0x3140f0ef.
Lemma F_ff13c : fetch_word Asan.M.loaded_segments (0xff13c : word) = Some W_ff13c.
Proof. vm_refl. Qed.
Lemma D_ff13c : decode_any W_ff13c = Some (Jal 1 62228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff140 : bv 32 := 0x00048513.
Lemma F_ff140 : fetch_word Asan.M.loaded_segments (0xff140 : word) = Some W_ff140.
Proof. vm_refl. Qed.
Lemma D_ff140 : decode_any W_ff140 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff144 : bv 32 := 0x000980e7.
Lemma F_ff144 : fetch_word Asan.M.loaded_segments (0xff144 : word) = Some W_ff144.
Proof. vm_refl. Qed.
Lemma D_ff144 : decode_any W_ff144 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff148 : bv 32 := 0x00040513.
Lemma F_ff148 : fetch_word Asan.M.loaded_segments (0xff148 : word) = Some W_ff148.
Proof. vm_refl. Qed.
Lemma D_ff148 : decode_any W_ff148 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff14c : bv 32 := 0x07c0f0ef.
Lemma F_ff14c : fetch_word Asan.M.loaded_segments (0xff14c : word) = Some W_ff14c.
Proof. vm_refl. Qed.
Lemma D_ff14c : decode_any W_ff14c = Some (Jal 1 61564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff150 : bv 32 := 0x00892503.
Lemma F_ff150 : fetch_word Asan.M.loaded_segments (0xff150 : word) = Some W_ff150.
Proof. vm_refl. Qed.
Lemma D_ff150 : decode_any W_ff150 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff154 : bv 32 := 0xfff5061b.
Lemma F_ff154 : fetch_word Asan.M.loaded_segments (0xff154 : word) = Some W_ff154.
Proof. vm_refl. Qed.
Lemma D_ff154 : decode_any W_ff154 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff158 : bv 32 := 0x00c92423.
Lemma F_ff158 : fetch_word Asan.M.loaded_segments (0xff158 : word) = Some W_ff158.
Proof. vm_refl. Qed.
Lemma D_ff158 : decode_any W_ff158 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff15c : bv 32 := 0xfca044e3.
Lemma F_ff15c : fetch_word Asan.M.loaded_segments (0xff15c : word) = Some W_ff15c.
Proof. vm_refl. Qed.
Lemma D_ff15c : decode_any W_ff15c = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff160 : bv 32 := 0x01093503.
Lemma F_ff160 : fetch_word Asan.M.loaded_segments (0xff160 : word) = Some W_ff160.
Proof. vm_refl. Qed.
Lemma D_ff160 : decode_any W_ff160 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff164 : bv 32 := 0xfa1ff06f.
Lemma F_ff164 : fetch_word Asan.M.loaded_segments (0xff164 : word) = Some W_ff164.
Proof. vm_refl. Qed.
Lemma D_ff164 : decode_any W_ff164 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff168 : bv 32 := 0x00100513.
Lemma F_ff168 : fetch_word Asan.M.loaded_segments (0xff168 : word) = Some W_ff168.
Proof. vm_refl. Qed.
Lemma D_ff168 : decode_any W_ff168 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff16c : bv 32 := 0x00a90023.
Lemma F_ff16c : fetch_word Asan.M.loaded_segments (0xff16c : word) = Some W_ff16c.
Proof. vm_refl. Qed.
Lemma D_ff16c : decode_any W_ff16c = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff170 : bv 32 := 0x00040513.
Lemma F_ff170 : fetch_word Asan.M.loaded_segments (0xff170 : word) = Some W_ff170.
Proof. vm_refl. Qed.
Lemma D_ff170 : decode_any W_ff170 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff174 : bv 32 := 0x02813083.
Lemma F_ff174 : fetch_word Asan.M.loaded_segments (0xff174 : word) = Some W_ff174.
Proof. vm_refl. Qed.
Lemma D_ff174 : decode_any W_ff174 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff178 : bv 32 := 0x02013403.
Lemma F_ff178 : fetch_word Asan.M.loaded_segments (0xff178 : word) = Some W_ff178.
Proof. vm_refl. Qed.
Lemma D_ff178 : decode_any W_ff178 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff17c : bv 32 := 0x01813483.
Lemma F_ff17c : fetch_word Asan.M.loaded_segments (0xff17c : word) = Some W_ff17c.
Proof. vm_refl. Qed.
Lemma D_ff17c : decode_any W_ff17c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff180 : bv 32 := 0x01013903.
Lemma F_ff180 : fetch_word Asan.M.loaded_segments (0xff180 : word) = Some W_ff180.
Proof. vm_refl. Qed.
Lemma D_ff180 : decode_any W_ff180 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff184 : bv 32 := 0x00813983.
Lemma F_ff184 : fetch_word Asan.M.loaded_segments (0xff184 : word) = Some W_ff184.
Proof. vm_refl. Qed.
Lemma D_ff184 : decode_any W_ff184 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff188 : bv 32 := 0x03010113.
Lemma F_ff188 : fetch_word Asan.M.loaded_segments (0xff188 : word) = Some W_ff188.
Proof. vm_refl. Qed.
Lemma D_ff188 : decode_any W_ff188 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff18c : bv 32 := 0x2c40f06f.
Lemma F_ff18c : fetch_word Asan.M.loaded_segments (0xff18c : word) = Some W_ff18c.
Proof. vm_refl. Qed.
Lemma D_ff18c : decode_any W_ff18c = Some (Jal 0 62148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff190 : bv 32 := 0x00008067.
Lemma F_ff190 : fetch_word Asan.M.loaded_segments (0xff190 : word) = Some W_ff190.
Proof. vm_refl. Qed.
Lemma D_ff190 : decode_any W_ff190 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff194 : bv 32 := 0xfd010113.
Lemma F_ff194 : fetch_word Asan.M.loaded_segments (0xff194 : word) = Some W_ff194.
Proof. vm_refl. Qed.
Lemma D_ff194 : decode_any W_ff194 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff198 : bv 32 := 0x02113423.
Lemma F_ff198 : fetch_word Asan.M.loaded_segments (0xff198 : word) = Some W_ff198.
Proof. vm_refl. Qed.
Lemma D_ff198 : decode_any W_ff198 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff19c : bv 32 := 0x02813023.
Lemma F_ff19c : fetch_word Asan.M.loaded_segments (0xff19c : word) = Some W_ff19c.
Proof. vm_refl. Qed.
Lemma D_ff19c : decode_any W_ff19c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1a0 : bv 32 := 0x00913c23.
Lemma F_ff1a0 : fetch_word Asan.M.loaded_segments (0xff1a0 : word) = Some W_ff1a0.
Proof. vm_refl. Qed.
Lemma D_ff1a0 : decode_any W_ff1a0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1a4 : bv 32 := 0x01213823.
Lemma F_ff1a4 : fetch_word Asan.M.loaded_segments (0xff1a4 : word) = Some W_ff1a4.
Proof. vm_refl. Qed.
Lemma D_ff1a4 : decode_any W_ff1a4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1a8 : bv 32 := 0x01313423.
Lemma F_ff1a8 : fetch_word Asan.M.loaded_segments (0xff1a8 : word) = Some W_ff1a8.
Proof. vm_refl. Qed.
Lemma D_ff1a8 : decode_any W_ff1a8 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1ac : bv 32 := 0x00050493.
Lemma F_ff1ac : fetch_word Asan.M.loaded_segments (0xff1ac : word) = Some W_ff1ac.
Proof. vm_refl. Qed.
Lemma D_ff1ac : decode_any W_ff1ac = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1b0 : bv 32 := 0x0057e517.
Lemma F_ff1b0 : fetch_word Asan.M.loaded_segments (0xff1b0 : word) = Some W_ff1b0.
Proof. vm_refl. Qed.
Lemma D_ff1b0 : decode_any W_ff1b0 = Some (Auipc 10 1406, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1b4 : bv 32 := 0x35050993.
Lemma F_ff1b4 : fetch_word Asan.M.loaded_segments (0xff1b4 : word) = Some W_ff1b4.
Proof. vm_refl. Qed.
Lemma D_ff1b4 : decode_any W_ff1b4 = Some (OpImm ALU_ADD 19 10 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1b8 : bv 32 := 0x00498413.
Lemma F_ff1b8 : fetch_word Asan.M.loaded_segments (0xff1b8 : word) = Some W_ff1b8.
Proof. vm_refl. Qed.
Lemma D_ff1b8 : decode_any W_ff1b8 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1bc : bv 32 := 0x00040513.
Lemma F_ff1bc : fetch_word Asan.M.loaded_segments (0xff1bc : word) = Some W_ff1bc.
Proof. vm_refl. Qed.
Lemma D_ff1bc : decode_any W_ff1bc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1c0 : bv 32 := 0x0080f0ef.
Lemma F_ff1c0 : fetch_word Asan.M.loaded_segments (0xff1c0 : word) = Some W_ff1c0.
Proof. vm_refl. Qed.
Lemma D_ff1c0 : decode_any W_ff1c0 = Some (Jal 1 61448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1c4 : bv 32 := 0x0009c503.
Lemma F_ff1c4 : fetch_word Asan.M.loaded_segments (0xff1c4 : word) = Some W_ff1c4.
Proof. vm_refl. Qed.
Lemma D_ff1c4 : decode_any W_ff1c4 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1c8 : bv 32 := 0xfff00913.
Lemma F_ff1c8 : fetch_word Asan.M.loaded_segments (0xff1c8 : word) = Some W_ff1c8.
Proof. vm_refl. Qed.
Lemma D_ff1c8 : decode_any W_ff1c8 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1cc : bv 32 := 0x06051263.
Lemma F_ff1cc : fetch_word Asan.M.loaded_segments (0xff1cc : word) = Some W_ff1cc.
Proof. vm_refl. Qed.
Lemma D_ff1cc : decode_any W_ff1cc = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1d0 : bv 32 := 0x0109b503.
Lemma F_ff1d0 : fetch_word Asan.M.loaded_segments (0xff1d0 : word) = Some W_ff1d0.
Proof. vm_refl. Qed.
Lemma D_ff1d0 : decode_any W_ff1d0 = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1d4 : bv 32 := 0x00051663.
Lemma F_ff1d4 : fetch_word Asan.M.loaded_segments (0xff1d4 : word) = Some W_ff1d4.
Proof. vm_refl. Qed.
Lemma D_ff1d4 : decode_any W_ff1d4 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1d8 : bv 32 := 0x01898513.
Lemma F_ff1d8 : fetch_word Asan.M.loaded_segments (0xff1d8 : word) = Some W_ff1d8.
Proof. vm_refl. Qed.
Lemma D_ff1d8 : decode_any W_ff1d8 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1dc : bv 32 := 0x00a9b823.
Lemma F_ff1dc : fetch_word Asan.M.loaded_segments (0xff1dc : word) = Some W_ff1dc.
Proof. vm_refl. Qed.
Lemma D_ff1dc : decode_any W_ff1dc = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1e0 : bv 32 := 0x0089a583.
Lemma F_ff1e0 : fetch_word Asan.M.loaded_segments (0xff1e0 : word) = Some W_ff1e0.
Proof. vm_refl. Qed.
Lemma D_ff1e0 : decode_any W_ff1e0 = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1e4 : bv 32 := 0x02000613.
Lemma F_ff1e4 : fetch_word Asan.M.loaded_segments (0xff1e4 : word) = Some W_ff1e4.
Proof. vm_refl. Qed.
Lemma D_ff1e4 : decode_any W_ff1e4 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1e8 : bv 32 := 0x02c59263.
Lemma F_ff1e8 : fetch_word Asan.M.loaded_segments (0xff1e8 : word) = Some W_ff1e8.
Proof. vm_refl. Qed.
Lemma D_ff1e8 : decode_any W_ff1e8 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1ec : bv 32 := 0x20800513.
Lemma F_ff1ec : fetch_word Asan.M.loaded_segments (0xff1ec : word) = Some W_ff1ec.
Proof. vm_refl. Qed.
Lemma D_ff1ec : decode_any W_ff1ec = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1f0 : bv 32 := 0x00100593.
Lemma F_ff1f0 : fetch_word Asan.M.loaded_segments (0xff1f0 : word) = Some W_ff1f0.
Proof. vm_refl. Qed.
Lemma D_ff1f0 : decode_any W_ff1f0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1f4 : bv 32 := 0x4a9000ef.
Lemma F_ff1f4 : fetch_word Asan.M.loaded_segments (0xff1f4 : word) = Some W_ff1f4.
Proof. vm_refl. Qed.
Lemma D_ff1f4 : decode_any W_ff1f4 = Some (Jal 1 3240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1f8 : bv 32 := 0x02050c63.
Lemma F_ff1f8 : fetch_word Asan.M.loaded_segments (0xff1f8 : word) = Some W_ff1f8.
Proof. vm_refl. Qed.
Lemma D_ff1f8 : decode_any W_ff1f8 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff1fc : bv 32 := 0x00000593.
Lemma F_ff1fc : fetch_word Asan.M.loaded_segments (0xff1fc : word) = Some W_ff1fc.
Proof. vm_refl. Qed.
Lemma D_ff1fc : decode_any W_ff1fc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff200 : bv 32 := 0x0109b603.
Lemma F_ff200 : fetch_word Asan.M.loaded_segments (0xff200 : word) = Some W_ff200.
Proof. vm_refl. Qed.
Lemma D_ff200 : decode_any W_ff200 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff204 : bv 32 := 0x00c53023.
Lemma F_ff204 : fetch_word Asan.M.loaded_segments (0xff204 : word) = Some W_ff204.
Proof. vm_refl. Qed.
Lemma D_ff204 : decode_any W_ff204 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff208 : bv 32 := 0x00a9b823.
Lemma F_ff208 : fetch_word Asan.M.loaded_segments (0xff208 : word) = Some W_ff208.
Proof. vm_refl. Qed.
Lemma D_ff208 : decode_any W_ff208 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff20c : bv 32 := 0x00000913.
Lemma F_ff20c : fetch_word Asan.M.loaded_segments (0xff20c : word) = Some W_ff20c.
Proof. vm_refl. Qed.
Lemma D_ff20c : decode_any W_ff20c = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff210 : bv 32 := 0x00359613.
Lemma F_ff210 : fetch_word Asan.M.loaded_segments (0xff210 : word) = Some W_ff210.
Proof. vm_refl. Qed.
Lemma D_ff210 : decode_any W_ff210 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff214 : bv 32 := 0x00c50533.
Lemma F_ff214 : fetch_word Asan.M.loaded_segments (0xff214 : word) = Some W_ff214.
Proof. vm_refl. Qed.
Lemma D_ff214 : decode_any W_ff214 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff218 : bv 32 := 0x00000617.
Lemma F_ff218 : fetch_word Asan.M.loaded_segments (0xff218 : word) = Some W_ff218.
Proof. vm_refl. Qed.
Lemma D_ff218 : decode_any W_ff218 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff21c : bv 32 := 0x00158593.
Lemma F_ff21c : fetch_word Asan.M.loaded_segments (0xff21c : word) = Some W_ff21c.
Proof. vm_refl. Qed.
Lemma D_ff21c : decode_any W_ff21c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff220 : bv 32 := 0x04060613.
Lemma F_ff220 : fetch_word Asan.M.loaded_segments (0xff220 : word) = Some W_ff220.
Proof. vm_refl. Qed.
Lemma D_ff220 : decode_any W_ff220 = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff224 : bv 32 := 0x00c53423.
Lemma F_ff224 : fetch_word Asan.M.loaded_segments (0xff224 : word) = Some W_ff224.
Proof. vm_refl. Qed.
Lemma D_ff224 : decode_any W_ff224 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff228 : bv 32 := 0x10953423.
Lemma F_ff228 : fetch_word Asan.M.loaded_segments (0xff228 : word) = Some W_ff228.
Proof. vm_refl. Qed.
Lemma D_ff228 : decode_any W_ff228 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff22c : bv 32 := 0x00b9a423.
Lemma F_ff22c : fetch_word Asan.M.loaded_segments (0xff22c : word) = Some W_ff22c.
Proof. vm_refl. Qed.
Lemma D_ff22c : decode_any W_ff22c = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff230 : bv 32 := 0x00040513.
Lemma F_ff230 : fetch_word Asan.M.loaded_segments (0xff230 : word) = Some W_ff230.
Proof. vm_refl. Qed.
Lemma D_ff230 : decode_any W_ff230 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff234 : bv 32 := 0x21c0f0ef.
Lemma F_ff234 : fetch_word Asan.M.loaded_segments (0xff234 : word) = Some W_ff234.
Proof. vm_refl. Qed.
Lemma D_ff234 : decode_any W_ff234 = Some (Jal 1 61980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff238 : bv 32 := 0x00090513.
Lemma F_ff238 : fetch_word Asan.M.loaded_segments (0xff238 : word) = Some W_ff238.
Proof. vm_refl. Qed.
Lemma D_ff238 : decode_any W_ff238 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff23c : bv 32 := 0x02813083.
Lemma F_ff23c : fetch_word Asan.M.loaded_segments (0xff23c : word) = Some W_ff23c.
Proof. vm_refl. Qed.
Lemma D_ff23c : decode_any W_ff23c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff240 : bv 32 := 0x02013403.
Lemma F_ff240 : fetch_word Asan.M.loaded_segments (0xff240 : word) = Some W_ff240.
Proof. vm_refl. Qed.
Lemma D_ff240 : decode_any W_ff240 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff244 : bv 32 := 0x01813483.
Lemma F_ff244 : fetch_word Asan.M.loaded_segments (0xff244 : word) = Some W_ff244.
Proof. vm_refl. Qed.
Lemma D_ff244 : decode_any W_ff244 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff248 : bv 32 := 0x01013903.
Lemma F_ff248 : fetch_word Asan.M.loaded_segments (0xff248 : word) = Some W_ff248.
Proof. vm_refl. Qed.
Lemma D_ff248 : decode_any W_ff248 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff24c : bv 32 := 0x00813983.
Lemma F_ff24c : fetch_word Asan.M.loaded_segments (0xff24c : word) = Some W_ff24c.
Proof. vm_refl. Qed.
Lemma D_ff24c : decode_any W_ff24c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff250 : bv 32 := 0x03010113.
Lemma F_ff250 : fetch_word Asan.M.loaded_segments (0xff250 : word) = Some W_ff250.
Proof. vm_refl. Qed.
Lemma D_ff250 : decode_any W_ff250 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff254 : bv 32 := 0x00008067.
Lemma F_ff254 : fetch_word Asan.M.loaded_segments (0xff254 : word) = Some W_ff254.
Proof. vm_refl. Qed.
Lemma D_ff254 : decode_any W_ff254 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff258 : bv 32 := 0x00050067.
Lemma F_ff258 : fetch_word Asan.M.loaded_segments (0xff258 : word) = Some W_ff258.
Proof. vm_refl. Qed.
Lemma D_ff258 : decode_any W_ff258 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff25c : bv 32 := 0x00008067.
Lemma F_ff25c : fetch_word Asan.M.loaded_segments (0xff25c : word) = Some W_ff25c.
Proof. vm_refl. Qed.
Lemma D_ff25c : decode_any W_ff25c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff260 : bv 32 := 0xfe010113.
Lemma F_ff260 : fetch_word Asan.M.loaded_segments (0xff260 : word) = Some W_ff260.
Proof. vm_refl. Qed.
Lemma D_ff260 : decode_any W_ff260 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff264 : bv 32 := 0x00113c23.
Lemma F_ff264 : fetch_word Asan.M.loaded_segments (0xff264 : word) = Some W_ff264.
Proof. vm_refl. Qed.
Lemma D_ff264 : decode_any W_ff264 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff268 : bv 32 := 0x00813823.
Lemma F_ff268 : fetch_word Asan.M.loaded_segments (0xff268 : word) = Some W_ff268.
Proof. vm_refl. Qed.
Lemma D_ff268 : decode_any W_ff268 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff26c : bv 32 := 0x00913423.
Lemma F_ff26c : fetch_word Asan.M.loaded_segments (0xff26c : word) = Some W_ff26c.
Proof. vm_refl. Qed.
Lemma D_ff26c : decode_any W_ff26c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff270 : bv 32 := 0x0001d517.
Lemma F_ff270 : fetch_word Asan.M.loaded_segments (0xff270 : word) = Some W_ff270.
Proof. vm_refl. Qed.
Lemma D_ff270 : decode_any W_ff270 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff274 : bv 32 := 0x0001d597.
Lemma F_ff274 : fetch_word Asan.M.loaded_segments (0xff274 : word) = Some W_ff274.
Proof. vm_refl. Qed.
Lemma D_ff274 : decode_any W_ff274 = Some (Auipc 11 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff278 : bv 32 := 0xef053503.
Lemma F_ff278 : fetch_word Asan.M.loaded_segments (0xff278 : word) = Some W_ff278.
Proof. vm_refl. Qed.
Lemma D_ff278 : decode_any W_ff278 = Some (Load SZ8 true 10 10 3824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff27c : bv 32 := 0xef45b403.
Lemma F_ff27c : fetch_word Asan.M.loaded_segments (0xff27c : word) = Some W_ff27c.
Proof. vm_refl. Qed.
Lemma D_ff27c : decode_any W_ff27c = Some (Load SZ8 true 8 11 3828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff280 : bv 32 := 0x00a47c63.
Lemma F_ff280 : fetch_word Asan.M.loaded_segments (0xff280 : word) = Some W_ff280.
Proof. vm_refl. Qed.
Lemma D_ff280 : decode_any W_ff280 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff284 : bv 32 := 0xff853583.
Lemma F_ff284 : fetch_word Asan.M.loaded_segments (0xff284 : word) = Some W_ff284.
Proof. vm_refl. Qed.
Lemma D_ff284 : decode_any W_ff284 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff288 : bv 32 := 0xff850493.
Lemma F_ff288 : fetch_word Asan.M.loaded_segments (0xff288 : word) = Some W_ff288.
Proof. vm_refl. Qed.
Lemma D_ff288 : decode_any W_ff288 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff28c : bv 32 := 0x000580e7.
Lemma F_ff28c : fetch_word Asan.M.loaded_segments (0xff28c : word) = Some W_ff28c.
Proof. vm_refl. Qed.
Lemma D_ff28c : decode_any W_ff28c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff290 : bv 32 := 0x00048513.
Lemma F_ff290 : fetch_word Asan.M.loaded_segments (0xff290 : word) = Some W_ff290.
Proof. vm_refl. Qed.
Lemma D_ff290 : decode_any W_ff290 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff294 : bv 32 := 0xfe9468e3.
Lemma F_ff294 : fetch_word Asan.M.loaded_segments (0xff294 : word) = Some W_ff294.
Proof. vm_refl. Qed.
Lemma D_ff294 : decode_any W_ff294 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff298 : bv 32 := 0x01813083.
Lemma F_ff298 : fetch_word Asan.M.loaded_segments (0xff298 : word) = Some W_ff298.
Proof. vm_refl. Qed.
Lemma D_ff298 : decode_any W_ff298 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff29c : bv 32 := 0x01013403.
Lemma F_ff29c : fetch_word Asan.M.loaded_segments (0xff29c : word) = Some W_ff29c.
Proof. vm_refl. Qed.
Lemma D_ff29c : decode_any W_ff29c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2a0 : bv 32 := 0x00813483.
Lemma F_ff2a0 : fetch_word Asan.M.loaded_segments (0xff2a0 : word) = Some W_ff2a0.
Proof. vm_refl. Qed.
Lemma D_ff2a0 : decode_any W_ff2a0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2a4 : bv 32 := 0x02010113.
Lemma F_ff2a4 : fetch_word Asan.M.loaded_segments (0xff2a4 : word) = Some W_ff2a4.
Proof. vm_refl. Qed.
Lemma D_ff2a4 : decode_any W_ff2a4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2a8 : bv 32 := 0xfb5ff06f.
Lemma F_ff2a8 : fetch_word Asan.M.loaded_segments (0xff2a8 : word) = Some W_ff2a8.
Proof. vm_refl. Qed.
Lemma D_ff2a8 : decode_any W_ff2a8 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2ac : bv 32 := 0xff010113.
Lemma F_ff2ac : fetch_word Asan.M.loaded_segments (0xff2ac : word) = Some W_ff2ac.
Proof. vm_refl. Qed.
Lemma D_ff2ac : decode_any W_ff2ac = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2b0 : bv 32 := 0x00113423.
Lemma F_ff2b0 : fetch_word Asan.M.loaded_segments (0xff2b0 : word) = Some W_ff2b0.
Proof. vm_refl. Qed.
Lemma D_ff2b0 : decode_any W_ff2b0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2b4 : bv 32 := 0x00813023.
Lemma F_ff2b4 : fetch_word Asan.M.loaded_segments (0xff2b4 : word) = Some W_ff2b4.
Proof. vm_refl. Qed.
Lemma D_ff2b4 : decode_any W_ff2b4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2b8 : bv 32 := 0x00000593.
Lemma F_ff2b8 : fetch_word Asan.M.loaded_segments (0xff2b8 : word) = Some W_ff2b8.
Proof. vm_refl. Qed.
Lemma D_ff2b8 : decode_any W_ff2b8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2bc : bv 32 := 0x00020613.
Lemma F_ff2bc : fetch_word Asan.M.loaded_segments (0xff2bc : word) = Some W_ff2bc.
Proof. vm_refl. Qed.
Lemma D_ff2bc : decode_any W_ff2bc = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2c0 : bv 32 := 0xf5862603.
Lemma F_ff2c0 : fetch_word Asan.M.loaded_segments (0xff2c0 : word) = Some W_ff2c0.
Proof. vm_refl. Qed.
Lemma D_ff2c0 : decode_any W_ff2c0 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2c4 : bv 32 := 0x0057e697.
Lemma F_ff2c4 : fetch_word Asan.M.loaded_segments (0xff2c4 : word) = Some W_ff2c4.
Proof. vm_refl. Qed.
Lemma D_ff2c4 : decode_any W_ff2c4 = Some (Auipc 13 1406, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2c8 : bv 32 := 0x45c68693.
Lemma F_ff2c8 : fetch_word Asan.M.loaded_segments (0xff2c8 : word) = Some W_ff2c8.
Proof. vm_refl. Qed.
Lemma D_ff2c8 : decode_any W_ff2c8 = Some (OpImm ALU_ADD 13 13 1116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2cc : bv 32 := 0x1606a72f.
Lemma F_ff2cc : fetch_word Asan.M.loaded_segments (0xff2cc : word) = Some W_ff2cc.
Proof. vm_refl. Qed.
Lemma D_ff2cc : decode_any W_ff2cc = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2d0 : bv 32 := 0x00b71663.
Lemma F_ff2d0 : fetch_word Asan.M.loaded_segments (0xff2d0 : word) = Some W_ff2d0.
Proof. vm_refl. Qed.
Lemma D_ff2d0 : decode_any W_ff2d0 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2d4 : bv 32 := 0x1ec6a7af.
Lemma F_ff2d4 : fetch_word Asan.M.loaded_segments (0xff2d4 : word) = Some W_ff2d4.
Proof. vm_refl. Qed.
Lemma D_ff2d4 : decode_any W_ff2d4 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2d8 : bv 32 := 0xfe079ae3.
Lemma F_ff2d8 : fetch_word Asan.M.loaded_segments (0xff2d8 : word) = Some W_ff2d8.
Proof. vm_refl. Qed.
Lemma D_ff2d8 : decode_any W_ff2d8 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2dc : bv 32 := 0x0007059b.
Lemma F_ff2dc : fetch_word Asan.M.loaded_segments (0xff2dc : word) = Some W_ff2dc.
Proof. vm_refl. Qed.
Lemma D_ff2dc : decode_any W_ff2dc = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2e0 : bv 32 := 0x02c58263.
Lemma F_ff2e0 : fetch_word Asan.M.loaded_segments (0xff2e0 : word) = Some W_ff2e0.
Proof. vm_refl. Qed.
Lemma D_ff2e0 : decode_any W_ff2e0 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2e4 : bv 32 := 0x02058263.
Lemma F_ff2e4 : fetch_word Asan.M.loaded_segments (0xff2e4 : word) = Some W_ff2e4.
Proof. vm_refl. Qed.
Lemma D_ff2e4 : decode_any W_ff2e4 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2e8 : bv 32 := 0x04900893.
Lemma F_ff2e8 : fetch_word Asan.M.loaded_segments (0xff2e8 : word) = Some W_ff2e8.
Proof. vm_refl. Qed.
Lemma D_ff2e8 : decode_any W_ff2e8 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2ec : bv 32 := 0x00000593.
Lemma F_ff2ec : fetch_word Asan.M.loaded_segments (0xff2ec : word) = Some W_ff2ec.
Proof. vm_refl. Qed.
Lemma D_ff2ec : decode_any W_ff2ec = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2f0 : bv 32 := 0x00000613.
Lemma F_ff2f0 : fetch_word Asan.M.loaded_segments (0xff2f0 : word) = Some W_ff2f0.
Proof. vm_refl. Qed.
Lemma D_ff2f0 : decode_any W_ff2f0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2f4 : bv 32 := 0x00000693.
Lemma F_ff2f4 : fetch_word Asan.M.loaded_segments (0xff2f4 : word) = Some W_ff2f4.
Proof. vm_refl. Qed.
Lemma D_ff2f4 : decode_any W_ff2f4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2f8 : bv 32 := 0x00000513.
Lemma F_ff2f8 : fetch_word Asan.M.loaded_segments (0xff2f8 : word) = Some W_ff2f8.
Proof. vm_refl. Qed.
Lemma D_ff2f8 : decode_any W_ff2f8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff2fc : bv 32 := 0x00000073.
Lemma F_ff2fc : fetch_word Asan.M.loaded_segments (0xff2fc : word) = Some W_ff2fc.
Proof. vm_refl. Qed.
Lemma D_ff2fc : decode_any W_ff2fc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff2fc : is_ecall W_ff2fc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff300 : bv 32 := 0xff9ff06f.
Lemma F_ff300 : fetch_word Asan.M.loaded_segments (0xff300 : word) = Some W_ff300.
Proof. vm_refl. Qed.
Lemma D_ff300 : decode_any W_ff300 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff304 : bv 32 := 0x00000023.
Lemma F_ff304 : fetch_word Asan.M.loaded_segments (0xff304 : word) = Some W_ff304.
Proof. vm_refl. Qed.
Lemma D_ff304 : decode_any W_ff304 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff308 : bv 32 := 0x00050413.
Lemma F_ff308 : fetch_word Asan.M.loaded_segments (0xff308 : word) = Some W_ff308.
Proof. vm_refl. Qed.
Lemma D_ff308 : decode_any W_ff308 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff30c : bv 32 := 0xdbdff0ef.
Lemma F_ff30c : fetch_word Asan.M.loaded_segments (0xff30c : word) = Some W_ff30c.
Proof. vm_refl. Qed.
Lemma D_ff30c : decode_any W_ff30c = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff310 : bv 32 := 0xf51ff0ef.
Lemma F_ff310 : fetch_word Asan.M.loaded_segments (0xff310 : word) = Some W_ff310.
Proof. vm_refl. Qed.
Lemma D_ff310 : decode_any W_ff310 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff314 : bv 32 := 0x0c8060ef.
Lemma F_ff314 : fetch_word Asan.M.loaded_segments (0xff314 : word) = Some W_ff314.
Proof. vm_refl. Qed.
Lemma D_ff314 : decode_any W_ff314 = Some (Jal 1 24776, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff318 : bv 32 := 0x00040513.
Lemma F_ff318 : fetch_word Asan.M.loaded_segments (0xff318 : word) = Some W_ff318.
Proof. vm_refl. Qed.
Lemma D_ff318 : decode_any W_ff318 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff31c : bv 32 := 0xd61ff0ef.
Lemma F_ff31c : fetch_word Asan.M.loaded_segments (0xff31c : word) = Some W_ff31c.
Proof. vm_refl. Qed.
Lemma D_ff31c : decode_any W_ff31c = Some (Jal 1 2096480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff320 : bv 32 := 0xfa010113.
Lemma F_ff320 : fetch_word Asan.M.loaded_segments (0xff320 : word) = Some W_ff320.
Proof. vm_refl. Qed.
Lemma D_ff320 : decode_any W_ff320 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff324 : bv 32 := 0x02113423.
Lemma F_ff324 : fetch_word Asan.M.loaded_segments (0xff324 : word) = Some W_ff324.
Proof. vm_refl. Qed.
Lemma D_ff324 : decode_any W_ff324 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff328 : bv 32 := 0x02813023.
Lemma F_ff328 : fetch_word Asan.M.loaded_segments (0xff328 : word) = Some W_ff328.
Proof. vm_refl. Qed.
Lemma D_ff328 : decode_any W_ff328 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff32c : bv 32 := 0x05013823.
Lemma F_ff32c : fetch_word Asan.M.loaded_segments (0xff32c : word) = Some W_ff32c.
Proof. vm_refl. Qed.
Lemma D_ff32c : decode_any W_ff32c = Some (Store SZ8 2 16 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff330 : bv 32 := 0x05113c23.
Lemma F_ff330 : fetch_word Asan.M.loaded_segments (0xff330 : word) = Some W_ff330.
Proof. vm_refl. Qed.
Lemma D_ff330 : decode_any W_ff330 = Some (Store SZ8 2 17 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff334 : bv 32 := 0x0001d817.
Lemma F_ff334 : fetch_word Asan.M.loaded_segments (0xff334 : word) = Some W_ff334.
Proof. vm_refl. Qed.
Lemma D_ff334 : decode_any W_ff334 = Some (Auipc 16 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff338 : bv 32 := 0xdfc83403.
Lemma F_ff338 : fetch_word Asan.M.loaded_segments (0xff338 : word) = Some W_ff338.
Proof. vm_refl. Qed.
Lemma D_ff338 : decode_any W_ff338 = Some (Load SZ8 true 8 16 3580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff33c : bv 32 := 0x02c13823.
Lemma F_ff33c : fetch_word Asan.M.loaded_segments (0xff33c : word) = Some W_ff33c.
Proof. vm_refl. Qed.
Lemma D_ff33c : decode_any W_ff33c = Some (Store SZ8 2 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff340 : bv 32 := 0x02d13c23.
Lemma F_ff340 : fetch_word Asan.M.loaded_segments (0xff340 : word) = Some W_ff340.
Proof. vm_refl. Qed.
Lemma D_ff340 : decode_any W_ff340 = Some (Store SZ8 2 13 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff344 : bv 32 := 0x04e13023.
Lemma F_ff344 : fetch_word Asan.M.loaded_segments (0xff344 : word) = Some W_ff344.
Proof. vm_refl. Qed.
Lemma D_ff344 : decode_any W_ff344 = Some (Store SZ8 2 14 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff348 : bv 32 := 0x04f13423.
Lemma F_ff348 : fetch_word Asan.M.loaded_segments (0xff348 : word) = Some W_ff348.
Proof. vm_refl. Qed.
Lemma D_ff348 : decode_any W_ff348 = Some (Store SZ8 2 15 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff34c : bv 32 := 0x00043683.
Lemma F_ff34c : fetch_word Asan.M.loaded_segments (0xff34c : word) = Some W_ff34c.
Proof. vm_refl. Qed.
Lemma D_ff34c : decode_any W_ff34c = Some (Load SZ8 true 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff350 : bv 32 := 0x03810713.
Lemma F_ff350 : fetch_word Asan.M.loaded_segments (0xff350 : word) = Some W_ff350.
Proof. vm_refl. Qed.
Lemma D_ff350 : decode_any W_ff350 = Some (OpImm ALU_ADD 14 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff354 : bv 32 := 0x01000793.
Lemma F_ff354 : fetch_word Asan.M.loaded_segments (0xff354 : word) = Some W_ff354.
Proof. vm_refl. Qed.
Lemma D_ff354 : decode_any W_ff354 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff358 : bv 32 := 0x00d13c23.
Lemma F_ff358 : fetch_word Asan.M.loaded_segments (0xff358 : word) = Some W_ff358.
Proof. vm_refl. Qed.
Lemma D_ff358 : decode_any W_ff358 = Some (Store SZ8 2 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff35c : bv 32 := 0x00e13823.
Lemma F_ff35c : fetch_word Asan.M.loaded_segments (0xff35c : word) = Some W_ff35c.
Proof. vm_refl. Qed.
Lemma D_ff35c : decode_any W_ff35c = Some (Store SZ8 2 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff360 : bv 32 := 0x08b7ea63.
Lemma F_ff360 : fetch_word Asan.M.loaded_segments (0xff360 : word) = Some W_ff360.
Proof. vm_refl. Qed.
Lemma D_ff360 : decode_any W_ff360 = Some (Branch BC_LTU 15 11 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff364 : bv 32 := 0x000186b7.
Lemma F_ff364 : fetch_word Asan.M.loaded_segments (0xff364 : word) = Some W_ff364.
Proof. vm_refl. Qed.
Lemma D_ff364 : decode_any W_ff364 = Some (Lui 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff368 : bv 32 := 0x0606869b.
Lemma F_ff368 : fetch_word Asan.M.loaded_segments (0xff368 : word) = Some W_ff368.
Proof. vm_refl. Qed.
Lemma D_ff368 : decode_any W_ff368 = Some (OpImm32 13 13 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff36c : bv 32 := 0x00b6d6b3.
Lemma F_ff36c : fetch_word Asan.M.loaded_segments (0xff36c : word) = Some W_ff36c.
Proof. vm_refl. Qed.
Lemma D_ff36c : decode_any W_ff36c = Some (Op ALU_SRL 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff370 : bv 32 := 0x0016f693.
Lemma F_ff370 : fetch_word Asan.M.loaded_segments (0xff370 : word) = Some W_ff370.
Proof. vm_refl. Qed.
Lemma D_ff370 : decode_any W_ff370 = Some (OpImm ALU_AND 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff374 : bv 32 := 0x02068863.
Lemma F_ff374 : fetch_word Asan.M.loaded_segments (0xff374 : word) = Some W_ff374.
Proof. vm_refl. Qed.
Lemma D_ff374 : decode_any W_ff374 = Some (Branch BC_EQ 13 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff378 : bv 32 := 0x01900893.
Lemma F_ff378 : fetch_word Asan.M.loaded_segments (0xff378 : word) = Some W_ff378.
Proof. vm_refl. Qed.
Lemma D_ff378 : decode_any W_ff378 = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff37c : bv 32 := 0x00000073.
Lemma F_ff37c : fetch_word Asan.M.loaded_segments (0xff37c : word) = Some W_ff37c.
Proof. vm_refl. Qed.
Lemma D_ff37c : decode_any W_ff37c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff37c : is_ecall W_ff37c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff380 : bv 32 := 0x284000ef.
Lemma F_ff380 : fetch_word Asan.M.loaded_segments (0xff380 : word) = Some W_ff380.
Proof. vm_refl. Qed.
Lemma D_ff380 : decode_any W_ff380 = Some (Jal 1 644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff384 : bv 32 := 0x00043583.
Lemma F_ff384 : fetch_word Asan.M.loaded_segments (0xff384 : word) = Some W_ff384.
Proof. vm_refl. Qed.
Lemma D_ff384 : decode_any W_ff384 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff388 : bv 32 := 0x01813603.
Lemma F_ff388 : fetch_word Asan.M.loaded_segments (0xff388 : word) = Some W_ff388.
Proof. vm_refl. Qed.
Lemma D_ff388 : decode_any W_ff388 = Some (Load SZ8 true 12 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff38c : bv 32 := 0x18c59863.
Lemma F_ff38c : fetch_word Asan.M.loaded_segments (0xff38c : word) = Some W_ff38c.
Proof. vm_refl. Qed.
Lemma D_ff38c : decode_any W_ff38c = Some (Branch BC_NE 11 12 400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff390 : bv 32 := 0x0005051b.
Lemma F_ff390 : fetch_word Asan.M.loaded_segments (0xff390 : word) = Some W_ff390.
Proof. vm_refl. Qed.
Lemma D_ff390 : decode_any W_ff390 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff394 : bv 32 := 0x02813083.
Lemma F_ff394 : fetch_word Asan.M.loaded_segments (0xff394 : word) = Some W_ff394.
Proof. vm_refl. Qed.
Lemma D_ff394 : decode_any W_ff394 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff398 : bv 32 := 0x02013403.
Lemma F_ff398 : fetch_word Asan.M.loaded_segments (0xff398 : word) = Some W_ff398.
Proof. vm_refl. Qed.
Lemma D_ff398 : decode_any W_ff398 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff39c : bv 32 := 0x06010113.
Lemma F_ff39c : fetch_word Asan.M.loaded_segments (0xff39c : word) = Some W_ff39c.
Proof. vm_refl. Qed.
Lemma D_ff39c : decode_any W_ff39c = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3a0 : bv 32 := 0x00008067.
Lemma F_ff3a0 : fetch_word Asan.M.loaded_segments (0xff3a0 : word) = Some W_ff3a0.
Proof. vm_refl. Qed.
Lemma D_ff3a0 : decode_any W_ff3a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3a4 : bv 32 := 0x00700693.
Lemma F_ff3a4 : fetch_word Asan.M.loaded_segments (0xff3a4 : word) = Some W_ff3a4.
Proof. vm_refl. Qed.
Lemma D_ff3a4 : decode_any W_ff3a4 = Some (OpImm ALU_ADD 13 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3a8 : bv 32 := 0x0ed58a63.
Lemma F_ff3a8 : fetch_word Asan.M.loaded_segments (0xff3a8 : word) = Some W_ff3a8.
Proof. vm_refl. Qed.
Lemma D_ff3a8 : decode_any W_ff3a8 = Some (Branch BC_EQ 11 13 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3ac : bv 32 := 0x00900693.
Lemma F_ff3ac : fetch_word Asan.M.loaded_segments (0xff3ac : word) = Some W_ff3ac.
Proof. vm_refl. Qed.
Lemma D_ff3ac : decode_any W_ff3ac = Some (OpImm ALU_ADD 13 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3b0 : bv 32 := 0x04d59263.
Lemma F_ff3b0 : fetch_word Asan.M.loaded_segments (0xff3b0 : word) = Some W_ff3b0.
Proof. vm_refl. Qed.
Lemma D_ff3b0 : decode_any W_ff3b0 = Some (Branch BC_NE 11 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3b4 : bv 32 := 0x00060693.
Lemma F_ff3b4 : fetch_word Asan.M.loaded_segments (0xff3b4 : word) = Some W_ff3b4.
Proof. vm_refl. Qed.
Lemma D_ff3b4 : decode_any W_ff3b4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3b8 : bv 32 := 0x01900893.
Lemma F_ff3b8 : fetch_word Asan.M.loaded_segments (0xff3b8 : word) = Some W_ff3b8.
Proof. vm_refl. Qed.
Lemma D_ff3b8 : decode_any W_ff3b8 = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3bc : bv 32 := 0x01000593.
Lemma F_ff3bc : fetch_word Asan.M.loaded_segments (0xff3bc : word) = Some W_ff3bc.
Proof. vm_refl. Qed.
Lemma D_ff3bc : decode_any W_ff3bc = Some (OpImm ALU_ADD 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3c0 : bv 32 := 0x00810613.
Lemma F_ff3c0 : fetch_word Asan.M.loaded_segments (0xff3c0 : word) = Some W_ff3c0.
Proof. vm_refl. Qed.
Lemma D_ff3c0 : decode_any W_ff3c0 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3c4 : bv 32 := 0x00050713.
Lemma F_ff3c4 : fetch_word Asan.M.loaded_segments (0xff3c4 : word) = Some W_ff3c4.
Proof. vm_refl. Qed.
Lemma D_ff3c4 : decode_any W_ff3c4 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3c8 : bv 32 := 0x00000073.
Lemma F_ff3c8 : fetch_word Asan.M.loaded_segments (0xff3c8 : word) = Some W_ff3c8.
Proof. vm_refl. Qed.
Lemma D_ff3c8 : decode_any W_ff3c8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff3c8 : is_ecall W_ff3c8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff3cc : bv 32 := 0x0005051b.
Lemma F_ff3cc : fetch_word Asan.M.loaded_segments (0xff3cc : word) = Some W_ff3cc.
Proof. vm_refl. Qed.
Lemma D_ff3cc : decode_any W_ff3cc = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3d0 : bv 32 := 0x10050a63.
Lemma F_ff3d0 : fetch_word Asan.M.loaded_segments (0xff3d0 : word) = Some W_ff3d0.
Proof. vm_refl. Qed.
Lemma D_ff3d0 : decode_any W_ff3d0 = Some (Branch BC_EQ 10 0 276, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3d4 : bv 32 := 0xfea00593.
Lemma F_ff3d4 : fetch_word Asan.M.loaded_segments (0xff3d4 : word) = Some W_ff3d4.
Proof. vm_refl. Qed.
Lemma D_ff3d4 : decode_any W_ff3d4 = Some (OpImm ALU_ADD 11 0 4074, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3d8 : bv 32 := 0xfab514e3.
Lemma F_ff3d8 : fetch_word Asan.M.loaded_segments (0xff3d8 : word) = Some W_ff3d8.
Proof. vm_refl. Qed.
Lemma D_ff3d8 : decode_any W_ff3d8 = Some (Branch BC_NE 10 11 8104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3dc : bv 32 := 0x01900893.
Lemma F_ff3dc : fetch_word Asan.M.loaded_segments (0xff3dc : word) = Some W_ff3dc.
Proof. vm_refl. Qed.
Lemma D_ff3dc : decode_any W_ff3dc = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3e0 : bv 32 := 0x00900593.
Lemma F_ff3e0 : fetch_word Asan.M.loaded_segments (0xff3e0 : word) = Some W_ff3e0.
Proof. vm_refl. Qed.
Lemma D_ff3e0 : decode_any W_ff3e0 = Some (OpImm ALU_ADD 11 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3e4 : bv 32 := 0x00070513.
Lemma F_ff3e4 : fetch_word Asan.M.loaded_segments (0xff3e4 : word) = Some W_ff3e4.
Proof. vm_refl. Qed.
Lemma D_ff3e4 : decode_any W_ff3e4 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3e8 : bv 32 := 0x00068613.
Lemma F_ff3e8 : fetch_word Asan.M.loaded_segments (0xff3e8 : word) = Some W_ff3e8.
Proof. vm_refl. Qed.
Lemma D_ff3e8 : decode_any W_ff3e8 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3ec : bv 32 := 0x00000073.
Lemma F_ff3ec : fetch_word Asan.M.loaded_segments (0xff3ec : word) = Some W_ff3ec.
Proof. vm_refl. Qed.
Lemma D_ff3ec : decode_any W_ff3ec = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff3ec : is_ecall W_ff3ec = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff3f0 : bv 32 := 0xf95ff06f.
Lemma F_ff3f0 : fetch_word Asan.M.loaded_segments (0xff3f0 : word) = Some W_ff3f0.
Proof. vm_refl. Qed.
Lemma D_ff3f0 : decode_any W_ff3f0 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3f4 : bv 32 := 0x40600693.
Lemma F_ff3f4 : fetch_word Asan.M.loaded_segments (0xff3f4 : word) = Some W_ff3f4.
Proof. vm_refl. Qed.
Lemma D_ff3f4 : decode_any W_ff3f4 = Some (OpImm ALU_ADD 13 0 1030, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3f8 : bv 32 := 0x08d59463.
Lemma F_ff3f8 : fetch_word Asan.M.loaded_segments (0xff3f8 : word) = Some W_ff3f8.
Proof. vm_refl. Qed.
Lemma D_ff3f8 : decode_any W_ff3f8 = Some (Branch BC_NE 11 13 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff3fc : bv 32 := 0x00050793.
Lemma F_ff3fc : fetch_word Asan.M.loaded_segments (0xff3fc : word) = Some W_ff3fc.
Proof. vm_refl. Qed.
Lemma D_ff3fc : decode_any W_ff3fc = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff400 : bv 32 := 0x01900893.
Lemma F_ff400 : fetch_word Asan.M.loaded_segments (0xff400 : word) = Some W_ff400.
Proof. vm_refl. Qed.
Lemma D_ff400 : decode_any W_ff400 = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff404 : bv 32 := 0x40600593.
Lemma F_ff404 : fetch_word Asan.M.loaded_segments (0xff404 : word) = Some W_ff404.
Proof. vm_refl. Qed.
Lemma D_ff404 : decode_any W_ff404 = Some (OpImm ALU_ADD 11 0 1030, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff408 : bv 32 := 0x00000073.
Lemma F_ff408 : fetch_word Asan.M.loaded_segments (0xff408 : word) = Some W_ff408.
Proof. vm_refl. Qed.
Lemma D_ff408 : decode_any W_ff408 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff408 : is_ecall W_ff408 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff40c : bv 32 := 0x0005071b.
Lemma F_ff40c : fetch_word Asan.M.loaded_segments (0xff40c : word) = Some W_ff40c.
Proof. vm_refl. Qed.
Lemma D_ff40c : decode_any W_ff40c = Some (OpImm32 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff410 : bv 32 := 0xfea00813.
Lemma F_ff410 : fetch_word Asan.M.loaded_segments (0xff410 : word) = Some W_ff410.
Proof. vm_refl. Qed.
Lemma D_ff410 : decode_any W_ff410 = Some (OpImm ALU_ADD 16 0 4074, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff414 : bv 32 := 0x0b071663.
Lemma F_ff414 : fetch_word Asan.M.loaded_segments (0xff414 : word) = Some W_ff414.
Proof. vm_refl. Qed.
Lemma D_ff414 : decode_any W_ff414 = Some (Branch BC_NE 14 16 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff418 : bv 32 := 0x00060693.
Lemma F_ff418 : fetch_word Asan.M.loaded_segments (0xff418 : word) = Some W_ff418.
Proof. vm_refl. Qed.
Lemma D_ff418 : decode_any W_ff418 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff41c : bv 32 := 0x01900893.
Lemma F_ff41c : fetch_word Asan.M.loaded_segments (0xff41c : word) = Some W_ff41c.
Proof. vm_refl. Qed.
Lemma D_ff41c : decode_any W_ff41c = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff420 : bv 32 := 0x40600593.
Lemma F_ff420 : fetch_word Asan.M.loaded_segments (0xff420 : word) = Some W_ff420.
Proof. vm_refl. Qed.
Lemma D_ff420 : decode_any W_ff420 = Some (OpImm ALU_ADD 11 0 1030, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff424 : bv 32 := 0x00078513.
Lemma F_ff424 : fetch_word Asan.M.loaded_segments (0xff424 : word) = Some W_ff424.
Proof. vm_refl. Qed.
Lemma D_ff424 : decode_any W_ff424 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff428 : bv 32 := 0x00000613.
Lemma F_ff428 : fetch_word Asan.M.loaded_segments (0xff428 : word) = Some W_ff428.
Proof. vm_refl. Qed.
Lemma D_ff428 : decode_any W_ff428 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff42c : bv 32 := 0x00000073.
Lemma F_ff42c : fetch_word Asan.M.loaded_segments (0xff42c : word) = Some W_ff42c.
Proof. vm_refl. Qed.
Lemma D_ff42c : decode_any W_ff42c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff42c : is_ecall W_ff42c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff430 : bv 32 := 0x0005059b.
Lemma F_ff430 : fetch_word Asan.M.loaded_segments (0xff430 : word) = Some W_ff430.
Proof. vm_refl. Qed.
Lemma D_ff430 : decode_any W_ff430 = Some (OpImm32 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff434 : bv 32 := 0x0d059463.
Lemma F_ff434 : fetch_word Asan.M.loaded_segments (0xff434 : word) = Some W_ff434.
Proof. vm_refl. Qed.
Lemma D_ff434 : decode_any W_ff434 = Some (Branch BC_NE 11 16 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff438 : bv 32 := 0x00078513.
Lemma F_ff438 : fetch_word Asan.M.loaded_segments (0xff438 : word) = Some W_ff438.
Proof. vm_refl. Qed.
Lemma D_ff438 : decode_any W_ff438 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff43c : bv 32 := 0x00000593.
Lemma F_ff43c : fetch_word Asan.M.loaded_segments (0xff43c : word) = Some W_ff43c.
Proof. vm_refl. Qed.
Lemma D_ff43c : decode_any W_ff43c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff440 : bv 32 := 0x00068613.
Lemma F_ff440 : fetch_word Asan.M.loaded_segments (0xff440 : word) = Some W_ff440.
Proof. vm_refl. Qed.
Lemma D_ff440 : decode_any W_ff440 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff444 : bv 32 := 0x800006b7.
Lemma F_ff444 : fetch_word Asan.M.loaded_segments (0xff444 : word) = Some W_ff444.
Proof. vm_refl. Qed.
Lemma D_ff444 : decode_any W_ff444 = Some (Lui 13 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff448 : bv 32 := 0x01900893.
Lemma F_ff448 : fetch_word Asan.M.loaded_segments (0xff448 : word) = Some W_ff448.
Proof. vm_refl. Qed.
Lemma D_ff448 : decode_any W_ff448 = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff44c : bv 32 := 0xfff6869b.
Lemma F_ff44c : fetch_word Asan.M.loaded_segments (0xff44c : word) = Some W_ff44c.
Proof. vm_refl. Qed.
Lemma D_ff44c : decode_any W_ff44c = Some (OpImm32 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff450 : bv 32 := 0x00000073.
Lemma F_ff450 : fetch_word Asan.M.loaded_segments (0xff450 : word) = Some W_ff450.
Proof. vm_refl. Qed.
Lemma D_ff450 : decode_any W_ff450 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff450 : is_ecall W_ff450 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff454 : bv 32 := 0x00050713.
Lemma F_ff454 : fetch_word Asan.M.loaded_segments (0xff454 : word) = Some W_ff454.
Proof. vm_refl. Qed.
Lemma D_ff454 : decode_any W_ff454 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff458 : bv 32 := 0x00168513.
Lemma F_ff458 : fetch_word Asan.M.loaded_segments (0xff458 : word) = Some W_ff458.
Proof. vm_refl. Qed.
Lemma D_ff458 : decode_any W_ff458 = Some (OpImm ALU_ADD 10 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff45c : bv 32 := 0x00a77533.
Lemma F_ff45c : fetch_word Asan.M.loaded_segments (0xff45c : word) = Some W_ff45c.
Proof. vm_refl. Qed.
Lemma D_ff45c : decode_any W_ff45c = Some (Op ALU_AND 10 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff460 : bv 32 := 0x00051c63.
Lemma F_ff460 : fetch_word Asan.M.loaded_segments (0xff460 : word) = Some W_ff460.
Proof. vm_refl. Qed.
Lemma D_ff460 : decode_any W_ff460 = Some (Branch BC_NE 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff464 : bv 32 := 0x00d77533.
Lemma F_ff464 : fetch_word Asan.M.loaded_segments (0xff464 : word) = Some W_ff464.
Proof. vm_refl. Qed.
Lemma D_ff464 : decode_any W_ff464 = Some (Op ALU_AND 10 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff468 : bv 32 := 0x01900893.
Lemma F_ff468 : fetch_word Asan.M.loaded_segments (0xff468 : word) = Some W_ff468.
Proof. vm_refl. Qed.
Lemma D_ff468 : decode_any W_ff468 = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff46c : bv 32 := 0x00200593.
Lemma F_ff46c : fetch_word Asan.M.loaded_segments (0xff46c : word) = Some W_ff46c.
Proof. vm_refl. Qed.
Lemma D_ff46c : decode_any W_ff46c = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff470 : bv 32 := 0x00100613.
Lemma F_ff470 : fetch_word Asan.M.loaded_segments (0xff470 : word) = Some W_ff470.
Proof. vm_refl. Qed.
Lemma D_ff470 : decode_any W_ff470 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff474 : bv 32 := 0x00000073.
Lemma F_ff474 : fetch_word Asan.M.loaded_segments (0xff474 : word) = Some W_ff474.
Proof. vm_refl. Qed.
Lemma D_ff474 : decode_any W_ff474 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff474 : is_ecall W_ff474 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff478 : bv 32 := 0x0007071b.
Lemma F_ff478 : fetch_word Asan.M.loaded_segments (0xff478 : word) = Some W_ff478.
Proof. vm_refl. Qed.
Lemma D_ff478 : decode_any W_ff478 = Some (OpImm32 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff47c : bv 32 := 0x0980006f.
Lemma F_ff47c : fetch_word Asan.M.loaded_segments (0xff47c : word) = Some W_ff47c.
Proof. vm_refl. Qed.
Lemma D_ff47c : decode_any W_ff47c = Some (Jal 0 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff480 : bv 32 := 0xffc58693.
Lemma F_ff480 : fetch_word Asan.M.loaded_segments (0xff480 : word) = Some W_ff480.
Proof. vm_refl. Qed.
Lemma D_ff480 : decode_any W_ff480 = Some (OpImm ALU_ADD 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff484 : bv 32 := 0x0016b693.
Lemma F_ff484 : fetch_word Asan.M.loaded_segments (0xff484 : word) = Some W_ff484.
Proof. vm_refl. Qed.
Lemma D_ff484 : decode_any W_ff484 = Some (OpImm ALU_SLTU 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff488 : bv 32 := 0x00f69693.
Lemma F_ff488 : fetch_word Asan.M.loaded_segments (0xff488 : word) = Some W_ff488.
Proof. vm_refl. Qed.
Lemma D_ff488 : decode_any W_ff488 = Some (ShiftImm ALU_SLL 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff48c : bv 32 := 0x00d66633.
Lemma F_ff48c : fetch_word Asan.M.loaded_segments (0xff48c : word) = Some W_ff48c.
Proof. vm_refl. Qed.
Lemma D_ff48c : decode_any W_ff48c = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff490 : bv 32 := 0x01900893.
Lemma F_ff490 : fetch_word Asan.M.loaded_segments (0xff490 : word) = Some W_ff490.
Proof. vm_refl. Qed.
Lemma D_ff490 : decode_any W_ff490 = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff494 : bv 32 := 0x00000073.
Lemma F_ff494 : fetch_word Asan.M.loaded_segments (0xff494 : word) = Some W_ff494.
Proof. vm_refl. Qed.
Lemma D_ff494 : decode_any W_ff494 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff494 : is_ecall W_ff494 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff498 : bv 32 := 0xee9ff06f.
Lemma F_ff498 : fetch_word Asan.M.loaded_segments (0xff498 : word) = Some W_ff498.
Proof. vm_refl. Qed.
Lemma D_ff498 : decode_any W_ff498 = Some (Jal 0 2096872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff49c : bv 32 := 0x00050593.
Lemma F_ff49c : fetch_word Asan.M.loaded_segments (0xff49c : word) = Some W_ff49c.
Proof. vm_refl. Qed.
Lemma D_ff49c : decode_any W_ff49c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4a0 : bv 32 := 0x01900513.
Lemma F_ff4a0 : fetch_word Asan.M.loaded_segments (0xff4a0 : word) = Some W_ff4a0.
Proof. vm_refl. Qed.
Lemma D_ff4a0 : decode_any W_ff4a0 = Some (OpImm ALU_ADD 10 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4a4 : bv 32 := 0x00060693.
Lemma F_ff4a4 : fetch_word Asan.M.loaded_segments (0xff4a4 : word) = Some W_ff4a4.
Proof. vm_refl. Qed.
Lemma D_ff4a4 : decode_any W_ff4a4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4a8 : bv 32 := 0x00700613.
Lemma F_ff4a8 : fetch_word Asan.M.loaded_segments (0xff4a8 : word) = Some W_ff4a8.
Proof. vm_refl. Qed.
Lemma D_ff4a8 : decode_any W_ff4a8 = Some (OpImm ALU_ADD 12 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4ac : bv 32 := 0x00000713.
Lemma F_ff4ac : fetch_word Asan.M.loaded_segments (0xff4ac : word) = Some W_ff4ac.
Proof. vm_refl. Qed.
Lemma D_ff4ac : decode_any W_ff4ac = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4b0 : bv 32 := 0x00000793.
Lemma F_ff4b0 : fetch_word Asan.M.loaded_segments (0xff4b0 : word) = Some W_ff4b0.
Proof. vm_refl. Qed.
Lemma D_ff4b0 : decode_any W_ff4b0 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4b4 : bv 32 := 0x00000813.
Lemma F_ff4b4 : fetch_word Asan.M.loaded_segments (0xff4b4 : word) = Some W_ff4b4.
Proof. vm_refl. Qed.
Lemma D_ff4b4 : decode_any W_ff4b4 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4b8 : bv 32 := 0x0300f0ef.
Lemma F_ff4b8 : fetch_word Asan.M.loaded_segments (0xff4b8 : word) = Some W_ff4b8.
Proof. vm_refl. Qed.
Lemma D_ff4b8 : decode_any W_ff4b8 = Some (Jal 1 61488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4bc : bv 32 := 0xec5ff06f.
Lemma F_ff4bc : fetch_word Asan.M.loaded_segments (0xff4bc : word) = Some W_ff4bc.
Proof. vm_refl. Qed.
Lemma D_ff4bc : decode_any W_ff4bc = Some (Jal 0 2096836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4c0 : bv 32 := 0x04074a63.
Lemma F_ff4c0 : fetch_word Asan.M.loaded_segments (0xff4c0 : word) = Some W_ff4c0.
Proof. vm_refl. Qed.
Lemma D_ff4c0 : decode_any W_ff4c0 = Some (Branch BC_LT 14 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4c4 : bv 32 := 0x02151513.
Lemma F_ff4c4 : fetch_word Asan.M.loaded_segments (0xff4c4 : word) = Some W_ff4c4.
Proof. vm_refl. Qed.
Lemma D_ff4c4 : decode_any W_ff4c4 = Some (ShiftImm ALU_SLL 10 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4c8 : bv 32 := 0x01900893.
Lemma F_ff4c8 : fetch_word Asan.M.loaded_segments (0xff4c8 : word) = Some W_ff4c8.
Proof. vm_refl. Qed.
Lemma D_ff4c8 : decode_any W_ff4c8 = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4cc : bv 32 := 0x02155513.
Lemma F_ff4cc : fetch_word Asan.M.loaded_segments (0xff4cc : word) = Some W_ff4cc.
Proof. vm_refl. Qed.
Lemma D_ff4cc : decode_any W_ff4cc = Some (ShiftImm ALU_SRL 10 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4d0 : bv 32 := 0x00200593.
Lemma F_ff4d0 : fetch_word Asan.M.loaded_segments (0xff4d0 : word) = Some W_ff4d0.
Proof. vm_refl. Qed.
Lemma D_ff4d0 : decode_any W_ff4d0 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4d4 : bv 32 := 0x00100613.
Lemma F_ff4d4 : fetch_word Asan.M.loaded_segments (0xff4d4 : word) = Some W_ff4d4.
Proof. vm_refl. Qed.
Lemma D_ff4d4 : decode_any W_ff4d4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4d8 : bv 32 := 0x00000073.
Lemma F_ff4d8 : fetch_word Asan.M.loaded_segments (0xff4d8 : word) = Some W_ff4d8.
Proof. vm_refl. Qed.
Lemma D_ff4d8 : decode_any W_ff4d8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff4d8 : is_ecall W_ff4d8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff4dc : bv 32 := 0x00070513.
Lemma F_ff4dc : fetch_word Asan.M.loaded_segments (0xff4dc : word) = Some W_ff4dc.
Proof. vm_refl. Qed.
Lemma D_ff4dc : decode_any W_ff4dc = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4e0 : bv 32 := 0xea1ff06f.
Lemma F_ff4e0 : fetch_word Asan.M.loaded_segments (0xff4e0 : word) = Some W_ff4e0.
Proof. vm_refl. Qed.
Lemma D_ff4e0 : decode_any W_ff4e0 = Some (Jal 0 2096800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4e4 : bv 32 := 0x00812583.
Lemma F_ff4e4 : fetch_word Asan.M.loaded_segments (0xff4e4 : word) = Some W_ff4e4.
Proof. vm_refl. Qed.
Lemma D_ff4e4 : decode_any W_ff4e4 = Some (Load SZ4 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4e8 : bv 32 := 0x00c12503.
Lemma F_ff4e8 : fetch_word Asan.M.loaded_segments (0xff4e8 : word) = Some W_ff4e8.
Proof. vm_refl. Qed.
Lemma D_ff4e8 : decode_any W_ff4e8 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4ec : bv 32 := 0x00200613.
Lemma F_ff4ec : fetch_word Asan.M.loaded_segments (0xff4ec : word) = Some W_ff4ec.
Proof. vm_refl. Qed.
Lemma D_ff4ec : decode_any W_ff4ec = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4f0 : bv 32 := 0xe8c59ae3.
Lemma F_ff4f0 : fetch_word Asan.M.loaded_segments (0xff4f0 : word) = Some W_ff4f0.
Proof. vm_refl. Qed.
Lemma D_ff4f0 : decode_any W_ff4f0 = Some (Branch BC_NE 11 12 7828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4f4 : bv 32 := 0x40a0053b.
Lemma F_ff4f4 : fetch_word Asan.M.loaded_segments (0xff4f4 : word) = Some W_ff4f4.
Proof. vm_refl. Qed.
Lemma D_ff4f4 : decode_any W_ff4f4 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4f8 : bv 32 := 0xe8dff06f.
Lemma F_ff4f8 : fetch_word Asan.M.loaded_segments (0xff4f8 : word) = Some W_ff4f8.
Proof. vm_refl. Qed.
Lemma D_ff4f8 : decode_any W_ff4f8 = Some (Jal 0 2096780, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff4fc : bv 32 := 0xfea00713.
Lemma F_ff4fc : fetch_word Asan.M.loaded_segments (0xff4fc : word) = Some W_ff4fc.
Proof. vm_refl. Qed.
Lemma D_ff4fc : decode_any W_ff4fc = Some (OpImm ALU_ADD 14 0 4074, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff500 : bv 32 := 0x0005ca63.
Lemma F_ff500 : fetch_word Asan.M.loaded_segments (0xff500 : word) = Some W_ff500.
Proof. vm_refl. Qed.
Lemma D_ff500 : decode_any W_ff500 = Some (Branch BC_LT 11 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff504 : bv 32 := 0x02151513.
Lemma F_ff504 : fetch_word Asan.M.loaded_segments (0xff504 : word) = Some W_ff504.
Proof. vm_refl. Qed.
Lemma D_ff504 : decode_any W_ff504 = Some (ShiftImm ALU_SLL 10 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff508 : bv 32 := 0x02155513.
Lemma F_ff508 : fetch_word Asan.M.loaded_segments (0xff508 : word) = Some W_ff508.
Proof. vm_refl. Qed.
Lemma D_ff508 : decode_any W_ff508 = Some (ShiftImm ALU_SRL 10 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff50c : bv 32 := 0x03900893.
Lemma F_ff50c : fetch_word Asan.M.loaded_segments (0xff50c : word) = Some W_ff50c.
Proof. vm_refl. Qed.
Lemma D_ff50c : decode_any W_ff50c = Some (OpImm ALU_ADD 17 0 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff510 : bv 32 := 0x00000073.
Lemma F_ff510 : fetch_word Asan.M.loaded_segments (0xff510 : word) = Some W_ff510.
Proof. vm_refl. Qed.
Lemma D_ff510 : decode_any W_ff510 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff510 : is_ecall W_ff510 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff514 : bv 32 := 0x00070513.
Lemma F_ff514 : fetch_word Asan.M.loaded_segments (0xff514 : word) = Some W_ff514.
Proof. vm_refl. Qed.
Lemma D_ff514 : decode_any W_ff514 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff518 : bv 32 := 0xe69ff06f.
Lemma F_ff518 : fetch_word Asan.M.loaded_segments (0xff518 : word) = Some W_ff518.
Proof. vm_refl. Qed.
Lemma D_ff518 : decode_any W_ff518 = Some (Jal 0 2096744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff51c : bv 32 := 0xa7dff0ef.
Lemma F_ff51c : fetch_word Asan.M.loaded_segments (0xff51c : word) = Some W_ff51c.
Proof. vm_refl. Qed.
Lemma D_ff51c : decode_any W_ff51c = Some (Jal 1 2095740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff520 : bv 32 := 0xfa010113.
Lemma F_ff520 : fetch_word Asan.M.loaded_segments (0xff520 : word) = Some W_ff520.
Proof. vm_refl. Qed.
Lemma D_ff520 : decode_any W_ff520 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff524 : bv 32 := 0x02113423.
Lemma F_ff524 : fetch_word Asan.M.loaded_segments (0xff524 : word) = Some W_ff524.
Proof. vm_refl. Qed.
Lemma D_ff524 : decode_any W_ff524 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff528 : bv 32 := 0x02813023.
Lemma F_ff528 : fetch_word Asan.M.loaded_segments (0xff528 : word) = Some W_ff528.
Proof. vm_refl. Qed.
Lemma D_ff528 : decode_any W_ff528 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff52c : bv 32 := 0x00913c23.
Lemma F_ff52c : fetch_word Asan.M.loaded_segments (0xff52c : word) = Some W_ff52c.
Proof. vm_refl. Qed.
Lemma D_ff52c : decode_any W_ff52c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff530 : bv 32 := 0x00058413.
Lemma F_ff530 : fetch_word Asan.M.loaded_segments (0xff530 : word) = Some W_ff530.
Proof. vm_refl. Qed.
Lemma D_ff530 : decode_any W_ff530 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff534 : bv 32 := 0x00050293.
Lemma F_ff534 : fetch_word Asan.M.loaded_segments (0xff534 : word) = Some W_ff534.
Proof. vm_refl. Qed.
Lemma D_ff534 : decode_any W_ff534 = Some (OpImm ALU_ADD 5 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff538 : bv 32 := 0x05013823.
Lemma F_ff538 : fetch_word Asan.M.loaded_segments (0xff538 : word) = Some W_ff538.
Proof. vm_refl. Qed.
Lemma D_ff538 : decode_any W_ff538 = Some (Store SZ8 2 16 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff53c : bv 32 := 0x05113c23.
Lemma F_ff53c : fetch_word Asan.M.loaded_segments (0xff53c : word) = Some W_ff53c.
Proof. vm_refl. Qed.
Lemma D_ff53c : decode_any W_ff53c = Some (Store SZ8 2 17 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff540 : bv 32 := 0x0001d517.
Lemma F_ff540 : fetch_word Asan.M.loaded_segments (0xff540 : word) = Some W_ff540.
Proof. vm_refl. Qed.
Lemma D_ff540 : decode_any W_ff540 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff544 : bv 32 := 0xbf053483.
Lemma F_ff544 : fetch_word Asan.M.loaded_segments (0xff544 : word) = Some W_ff544.
Proof. vm_refl. Qed.
Lemma D_ff544 : decode_any W_ff544 = Some (Load SZ8 true 9 10 3056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff548 : bv 32 := 0x02c13823.
Lemma F_ff548 : fetch_word Asan.M.loaded_segments (0xff548 : word) = Some W_ff548.
Proof. vm_refl. Qed.
Lemma D_ff548 : decode_any W_ff548 = Some (Store SZ8 2 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff54c : bv 32 := 0x02d13c23.
Lemma F_ff54c : fetch_word Asan.M.loaded_segments (0xff54c : word) = Some W_ff54c.
Proof. vm_refl. Qed.
Lemma D_ff54c : decode_any W_ff54c = Some (Store SZ8 2 13 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff550 : bv 32 := 0x04e13023.
Lemma F_ff550 : fetch_word Asan.M.loaded_segments (0xff550 : word) = Some W_ff550.
Proof. vm_refl. Qed.
Lemma D_ff550 : decode_any W_ff550 = Some (Store SZ8 2 14 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff554 : bv 32 := 0x04f13423.
Lemma F_ff554 : fetch_word Asan.M.loaded_segments (0xff554 : word) = Some W_ff554.
Proof. vm_refl. Qed.
Lemma D_ff554 : decode_any W_ff554 = Some (Store SZ8 2 15 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff558 : bv 32 := 0x0004b503.
Lemma F_ff558 : fetch_word Asan.M.loaded_segments (0xff558 : word) = Some W_ff558.
Proof. vm_refl. Qed.
Lemma D_ff558 : decode_any W_ff558 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff55c : bv 32 := 0x0405f593.
Lemma F_ff55c : fetch_word Asan.M.loaded_segments (0xff55c : word) = Some W_ff55c.
Proof. vm_refl. Qed.
Lemma D_ff55c : decode_any W_ff55c = Some (OpImm ALU_AND 11 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff560 : bv 32 := 0x00a13823.
Lemma F_ff560 : fetch_word Asan.M.loaded_segments (0xff560 : word) = Some W_ff560.
Proof. vm_refl. Qed.
Lemma D_ff560 : decode_any W_ff560 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff564 : bv 32 := 0x00059c63.
Lemma F_ff564 : fetch_word Asan.M.loaded_segments (0xff564 : word) = Some W_ff564.
Proof. vm_refl. Qed.
Lemma D_ff564 : decode_any W_ff564 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff568 : bv 32 := 0x00410537.
Lemma F_ff568 : fetch_word Asan.M.loaded_segments (0xff568 : word) = Some W_ff568.
Proof. vm_refl. Qed.
Lemma D_ff568 : decode_any W_ff568 = Some (Lui 10 1040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff56c : bv 32 := 0x00a475b3.
Lemma F_ff56c : fetch_word Asan.M.loaded_segments (0xff56c : word) = Some W_ff56c.
Proof. vm_refl. Qed.
Lemma D_ff56c : decode_any W_ff56c = Some (Op ALU_AND 11 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff570 : bv 32 := 0x00a58663.
Lemma F_ff570 : fetch_word Asan.M.loaded_segments (0xff570 : word) = Some W_ff570.
Proof. vm_refl. Qed.
Lemma D_ff570 : decode_any W_ff570 = Some (Branch BC_EQ 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff574 : bv 32 := 0x00000713.
Lemma F_ff574 : fetch_word Asan.M.loaded_segments (0xff574 : word) = Some W_ff574.
Proof. vm_refl. Qed.
Lemma D_ff574 : decode_any W_ff574 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff578 : bv 32 := 0x0080006f.
Lemma F_ff578 : fetch_word Asan.M.loaded_segments (0xff578 : word) = Some W_ff578.
Proof. vm_refl. Qed.
Lemma D_ff578 : decode_any W_ff578 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff57c : bv 32 := 0x03016703.
Lemma F_ff57c : fetch_word Asan.M.loaded_segments (0xff57c : word) = Some W_ff57c.
Proof. vm_refl. Qed.
Lemma D_ff57c : decode_any W_ff57c = Some (Load SZ4 false 14 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff580 : bv 32 := 0x000086b7.
Lemma F_ff580 : fetch_word Asan.M.loaded_segments (0xff580 : word) = Some W_ff580.
Proof. vm_refl. Qed.
Lemma D_ff580 : decode_any W_ff580 = Some (Lui 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff584 : bv 32 := 0x00d466b3.
Lemma F_ff584 : fetch_word Asan.M.loaded_segments (0xff584 : word) = Some W_ff584.
Proof. vm_refl. Qed.
Lemma D_ff584 : decode_any W_ff584 = Some (Op ALU_OR 13 8 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff588 : bv 32 := 0x03800513.
Lemma F_ff588 : fetch_word Asan.M.loaded_segments (0xff588 : word) = Some W_ff588.
Proof. vm_refl. Qed.
Lemma D_ff588 : decode_any W_ff588 = Some (OpImm ALU_ADD 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff58c : bv 32 := 0xf9c00593.
Lemma F_ff58c : fetch_word Asan.M.loaded_segments (0xff58c : word) = Some W_ff58c.
Proof. vm_refl. Qed.
Lemma D_ff58c : decode_any W_ff58c = Some (OpImm ALU_ADD 11 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff590 : bv 32 := 0x00028613.
Lemma F_ff590 : fetch_word Asan.M.loaded_segments (0xff590 : word) = Some W_ff590.
Proof. vm_refl. Qed.
Lemma D_ff590 : decode_any W_ff590 = Some (OpImm ALU_ADD 12 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff594 : bv 32 := 0x00000793.
Lemma F_ff594 : fetch_word Asan.M.loaded_segments (0xff594 : word) = Some W_ff594.
Proof. vm_refl. Qed.
Lemma D_ff594 : decode_any W_ff594 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff598 : bv 32 := 0x00000813.
Lemma F_ff598 : fetch_word Asan.M.loaded_segments (0xff598 : word) = Some W_ff598.
Proof. vm_refl. Qed.
Lemma D_ff598 : decode_any W_ff598 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff59c : bv 32 := 0x74d0e0ef.
Lemma F_ff59c : fetch_word Asan.M.loaded_segments (0xff59c : word) = Some W_ff59c.
Proof. vm_refl. Qed.
Lemma D_ff59c : decode_any W_ff59c = Some (Jal 1 61260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5a0 : bv 32 := 0x02c41413.
Lemma F_ff5a0 : fetch_word Asan.M.loaded_segments (0xff5a0 : word) = Some W_ff5a0.
Proof. vm_refl. Qed.
Lemma D_ff5a0 : decode_any W_ff5a0 = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5a4 : bv 32 := 0x00050693.
Lemma F_ff5a4 : fetch_word Asan.M.loaded_segments (0xff5a4 : word) = Some W_ff5a4.
Proof. vm_refl. Qed.
Lemma D_ff5a4 : decode_any W_ff5a4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5a8 : bv 32 := 0x02045663.
Lemma F_ff5a8 : fetch_word Asan.M.loaded_segments (0xff5a8 : word) = Some W_ff5a8.
Proof. vm_refl. Qed.
Lemma D_ff5a8 : decode_any W_ff5a8 = Some (Branch BC_GE 8 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5ac : bv 32 := 0x80000537.
Lemma F_ff5ac : fetch_word Asan.M.loaded_segments (0xff5ac : word) = Some W_ff5ac.
Proof. vm_refl. Qed.
Lemma D_ff5ac : decode_any W_ff5ac = Some (Lui 10 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5b0 : bv 32 := 0xfff5051b.
Lemma F_ff5b0 : fetch_word Asan.M.loaded_segments (0xff5b0 : word) = Some W_ff5b0.
Proof. vm_refl. Qed.
Lemma D_ff5b0 : decode_any W_ff5b0 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5b4 : bv 32 := 0x00150593.
Lemma F_ff5b4 : fetch_word Asan.M.loaded_segments (0xff5b4 : word) = Some W_ff5b4.
Proof. vm_refl. Qed.
Lemma D_ff5b4 : decode_any W_ff5b4 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5b8 : bv 32 := 0x00b6f5b3.
Lemma F_ff5b8 : fetch_word Asan.M.loaded_segments (0xff5b8 : word) = Some W_ff5b8.
Proof. vm_refl. Qed.
Lemma D_ff5b8 : decode_any W_ff5b8 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5bc : bv 32 := 0x00059c63.
Lemma F_ff5bc : fetch_word Asan.M.loaded_segments (0xff5bc : word) = Some W_ff5bc.
Proof. vm_refl. Qed.
Lemma D_ff5bc : decode_any W_ff5bc = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5c0 : bv 32 := 0x00a6f533.
Lemma F_ff5c0 : fetch_word Asan.M.loaded_segments (0xff5c0 : word) = Some W_ff5c0.
Proof. vm_refl. Qed.
Lemma D_ff5c0 : decode_any W_ff5c0 = Some (Op ALU_AND 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5c4 : bv 32 := 0x01900893.
Lemma F_ff5c4 : fetch_word Asan.M.loaded_segments (0xff5c4 : word) = Some W_ff5c4.
Proof. vm_refl. Qed.
Lemma D_ff5c4 : decode_any W_ff5c4 = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5c8 : bv 32 := 0x00200593.
Lemma F_ff5c8 : fetch_word Asan.M.loaded_segments (0xff5c8 : word) = Some W_ff5c8.
Proof. vm_refl. Qed.
Lemma D_ff5c8 : decode_any W_ff5c8 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5cc : bv 32 := 0x00100613.
Lemma F_ff5cc : fetch_word Asan.M.loaded_segments (0xff5cc : word) = Some W_ff5cc.
Proof. vm_refl. Qed.
Lemma D_ff5cc : decode_any W_ff5cc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5d0 : bv 32 := 0x00000073.
Lemma F_ff5d0 : fetch_word Asan.M.loaded_segments (0xff5d0 : word) = Some W_ff5d0.
Proof. vm_refl. Qed.
Lemma D_ff5d0 : decode_any W_ff5d0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_ff5d0 : is_ecall W_ff5d0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_ff5d4 : bv 32 := 0x0006851b.
Lemma F_ff5d4 : fetch_word Asan.M.loaded_segments (0xff5d4 : word) = Some W_ff5d4.
Proof. vm_refl. Qed.
Lemma D_ff5d4 : decode_any W_ff5d4 = Some (OpImm32 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5d8 : bv 32 := 0x02c000ef.
Lemma F_ff5d8 : fetch_word Asan.M.loaded_segments (0xff5d8 : word) = Some W_ff5d8.
Proof. vm_refl. Qed.
Lemma D_ff5d8 : decode_any W_ff5d8 = Some (Jal 1 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5dc : bv 32 := 0x0004b583.
Lemma F_ff5dc : fetch_word Asan.M.loaded_segments (0xff5dc : word) = Some W_ff5dc.
Proof. vm_refl. Qed.
Lemma D_ff5dc : decode_any W_ff5dc = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5e0 : bv 32 := 0x01013603.
Lemma F_ff5e0 : fetch_word Asan.M.loaded_segments (0xff5e0 : word) = Some W_ff5e0.
Proof. vm_refl. Qed.
Lemma D_ff5e0 : decode_any W_ff5e0 = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5e4 : bv 32 := 0x00c59e63.
Lemma F_ff5e4 : fetch_word Asan.M.loaded_segments (0xff5e4 : word) = Some W_ff5e4.
Proof. vm_refl. Qed.
Lemma D_ff5e4 : decode_any W_ff5e4 = Some (Branch BC_NE 11 12 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5e8 : bv 32 := 0x0005051b.
Lemma F_ff5e8 : fetch_word Asan.M.loaded_segments (0xff5e8 : word) = Some W_ff5e8.
Proof. vm_refl. Qed.
Lemma D_ff5e8 : decode_any W_ff5e8 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5ec : bv 32 := 0x02813083.
Lemma F_ff5ec : fetch_word Asan.M.loaded_segments (0xff5ec : word) = Some W_ff5ec.
Proof. vm_refl. Qed.
Lemma D_ff5ec : decode_any W_ff5ec = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5f0 : bv 32 := 0x02013403.
Lemma F_ff5f0 : fetch_word Asan.M.loaded_segments (0xff5f0 : word) = Some W_ff5f0.
Proof. vm_refl. Qed.
Lemma D_ff5f0 : decode_any W_ff5f0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5f4 : bv 32 := 0x01813483.
Lemma F_ff5f4 : fetch_word Asan.M.loaded_segments (0xff5f4 : word) = Some W_ff5f4.
Proof. vm_refl. Qed.
Lemma D_ff5f4 : decode_any W_ff5f4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5f8 : bv 32 := 0x06010113.
Lemma F_ff5f8 : fetch_word Asan.M.loaded_segments (0xff5f8 : word) = Some W_ff5f8.
Proof. vm_refl. Qed.
Lemma D_ff5f8 : decode_any W_ff5f8 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff5fc : bv 32 := 0x00008067.
Lemma F_ff5fc : fetch_word Asan.M.loaded_segments (0xff5fc : word) = Some W_ff5fc.
Proof. vm_refl. Qed.
Lemma D_ff5fc : decode_any W_ff5fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff600 : bv 32 := 0x999ff0ef.
Lemma F_ff600 : fetch_word Asan.M.loaded_segments (0xff600 : word) = Some W_ff600.
Proof. vm_refl. Qed.
Lemma D_ff600 : decode_any W_ff600 = Some (Jal 1 2095512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff604 : bv 32 := 0xfffff5b7.
Lemma F_ff604 : fetch_word Asan.M.loaded_segments (0xff604 : word) = Some W_ff604.
Proof. vm_refl. Qed.
Lemma D_ff604 : decode_any W_ff604 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff608 : bv 32 := 0x0015859b.
Lemma F_ff608 : fetch_word Asan.M.loaded_segments (0xff608 : word) = Some W_ff608.
Proof. vm_refl. Qed.
Lemma D_ff608 : decode_any W_ff608 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff60c : bv 32 := 0x02b56663.
Lemma F_ff60c : fetch_word Asan.M.loaded_segments (0xff60c : word) = Some W_ff60c.
Proof. vm_refl. Qed.
Lemma D_ff60c : decode_any W_ff60c = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff610 : bv 32 := 0xff010113.
Lemma F_ff610 : fetch_word Asan.M.loaded_segments (0xff610 : word) = Some W_ff610.
Proof. vm_refl. Qed.
Lemma D_ff610 : decode_any W_ff610 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff614 : bv 32 := 0x00113423.
Lemma F_ff614 : fetch_word Asan.M.loaded_segments (0xff614 : word) = Some W_ff614.
Proof. vm_refl. Qed.
Lemma D_ff614 : decode_any W_ff614 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff618 : bv 32 := 0x00813023.
Lemma F_ff618 : fetch_word Asan.M.loaded_segments (0xff618 : word) = Some W_ff618.
Proof. vm_refl. Qed.
Lemma D_ff618 : decode_any W_ff618 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff61c : bv 32 := 0x40a0043b.
Lemma F_ff61c : fetch_word Asan.M.loaded_segments (0xff61c : word) = Some W_ff61c.
Proof. vm_refl. Qed.
Lemma D_ff61c : decode_any W_ff61c = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff620 : bv 32 := 0x981ff0ef.
Lemma F_ff620 : fetch_word Asan.M.loaded_segments (0xff620 : word) = Some W_ff620.
Proof. vm_refl. Qed.
Lemma D_ff620 : decode_any W_ff620 = Some (Jal 1 2095488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff624 : bv 32 := 0x00852023.
Lemma F_ff624 : fetch_word Asan.M.loaded_segments (0xff624 : word) = Some W_ff624.
Proof. vm_refl. Qed.
Lemma D_ff624 : decode_any W_ff624 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff628 : bv 32 := 0xfff00513.
Lemma F_ff628 : fetch_word Asan.M.loaded_segments (0xff628 : word) = Some W_ff628.
Proof. vm_refl. Qed.
Lemma D_ff628 : decode_any W_ff628 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff62c : bv 32 := 0x00813083.
Lemma F_ff62c : fetch_word Asan.M.loaded_segments (0xff62c : word) = Some W_ff62c.
Proof. vm_refl. Qed.
Lemma D_ff62c : decode_any W_ff62c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff630 : bv 32 := 0x00013403.
Lemma F_ff630 : fetch_word Asan.M.loaded_segments (0xff630 : word) = Some W_ff630.
Proof. vm_refl. Qed.
Lemma D_ff630 : decode_any W_ff630 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff634 : bv 32 := 0x01010113.
Lemma F_ff634 : fetch_word Asan.M.loaded_segments (0xff634 : word) = Some W_ff634.
Proof. vm_refl. Qed.
Lemma D_ff634 : decode_any W_ff634 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ff638 : bv 32 := 0x00008067.
Lemma F_ff638 : fetch_word Asan.M.loaded_segments (0xff638 : word) = Some W_ff638.
Proof. vm_refl. Qed.
Lemma D_ff638 : decode_any W_ff638 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
