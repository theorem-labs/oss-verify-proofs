(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.


(* [comment removed for export] *)
Definition W_13974 : bv 32 := 0xffffd197.
Lemma F_13974 : fetch_word Ubsan.M.loaded_segments (0x13974 : word) = Some W_13974.
Proof. vm_refl. Qed.
Lemma D_13974 : decode_any W_13974 = Some (Auipc 3 1048573, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13978 : bv 32 := 0xe8c18193.
Lemma F_13978 : fetch_word Ubsan.M.loaded_segments (0x13978 : word) = Some W_13978.
Proof. vm_refl. Qed.
Lemma D_13978 : decode_any W_13978 = Some (OpImm ALU_ADD 3 3 3724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1397c : bv 32 := 0x00010513.
Lemma F_1397c : fetch_word Ubsan.M.loaded_segments (0x1397c : word) = Some W_1397c.
Proof. vm_refl. Qed.
Lemma D_1397c : decode_any W_1397c = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13980 : bv 32 := 0xfffec597.
Lemma F_13980 : fetch_word Ubsan.M.loaded_segments (0x13980 : word) = Some W_13980.
Proof. vm_refl. Qed.
Lemma D_13980 : decode_any W_13980 = Some (Auipc 11 1048556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13984 : bv 32 := 0x68058593.
Lemma F_13984 : fetch_word Ubsan.M.loaded_segments (0x13984 : word) = Some W_13984.
Proof. vm_refl. Qed.
Lemma D_13984 : decode_any W_13984 = Some (OpImm ALU_ADD 11 11 1664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13988 : bv 32 := 0xff017113.
Lemma F_13988 : fetch_word Ubsan.M.loaded_segments (0x13988 : word) = Some W_13988.
Proof. vm_refl. Qed.
Lemma D_13988 : decode_any W_13988 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1398c : bv 32 := 0x0040006f.
Lemma F_1398c : fetch_word Ubsan.M.loaded_segments (0x1398c : word) = Some W_1398c.
Proof. vm_refl. Qed.
Lemma D_1398c : decode_any W_1398c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13990 : bv 32 := 0x00052583.
Lemma F_13990 : fetch_word Ubsan.M.loaded_segments (0x13990 : word) = Some W_13990.
Proof. vm_refl. Qed.
Lemma D_13990 : decode_any W_13990 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13994 : bv 32 := 0x00012617.
Lemma F_13994 : fetch_word Ubsan.M.loaded_segments (0x13994 : word) = Some W_13994.
Proof. vm_refl. Qed.
Lemma D_13994 : decode_any W_13994 = Some (Auipc 12 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13998 : bv 32 := 0x00012697.
Lemma F_13998 : fetch_word Ubsan.M.loaded_segments (0x13998 : word) = Some W_13998.
Proof. vm_refl. Qed.
Lemma D_13998 : decode_any W_13998 = Some (Auipc 13 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1399c : bv 32 := 0x00012717.
Lemma F_1399c : fetch_word Ubsan.M.loaded_segments (0x1399c : word) = Some W_1399c.
Proof. vm_refl. Qed.
Lemma D_1399c : decode_any W_1399c = Some (Auipc 14 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139a0 : bv 32 := 0xdc463783.
Lemma F_139a0 : fetch_word Ubsan.M.loaded_segments (0x139a0 : word) = Some W_139a0.
Proof. vm_refl. Qed.
Lemma D_139a0 : decode_any W_139a0 = Some (Load SZ8 true 15 12 3524, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139a4 : bv 32 := 0xdc86b683.
Lemma F_139a4 : fetch_word Ubsan.M.loaded_segments (0x139a4 : word) = Some W_139a4.
Proof. vm_refl. Qed.
Lemma D_139a4 : decode_any W_139a4 = Some (Load SZ8 true 13 13 3528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139a8 : bv 32 := 0xdcc73703.
Lemma F_139a8 : fetch_word Ubsan.M.loaded_segments (0x139a8 : word) = Some W_139a8.
Proof. vm_refl. Qed.
Lemma D_139a8 : decode_any W_139a8 = Some (Load SZ8 true 14 14 3532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139ac : bv 32 := 0x00850613.
Lemma F_139ac : fetch_word Ubsan.M.loaded_segments (0x139ac : word) = Some W_139ac.
Proof. vm_refl. Qed.
Lemma D_139ac : decode_any W_139ac = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139b0 : bv 32 := 0x00078513.
Lemma F_139b0 : fetch_word Ubsan.M.loaded_segments (0x139b0 : word) = Some W_139b0.
Proof. vm_refl. Qed.
Lemma D_139b0 : decode_any W_139b0 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139b4 : bv 32 := 0x00000793.
Lemma F_139b4 : fetch_word Ubsan.M.loaded_segments (0x139b4 : word) = Some W_139b4.
Proof. vm_refl. Qed.
Lemma D_139b4 : decode_any W_139b4 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139b8 : bv 32 := 0x7e10706f.
Lemma F_139b8 : fetch_word Ubsan.M.loaded_segments (0x139b8 : word) = Some W_139b8.
Proof. vm_refl. Qed.
Lemma D_139b8 : decode_any W_139b8 = Some (Jal 0 32736, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139bc : bv 32 := 0xff010113.
Lemma F_139bc : fetch_word Ubsan.M.loaded_segments (0x139bc : word) = Some W_139bc.
Proof. vm_refl. Qed.
Lemma D_139bc : decode_any W_139bc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139c0 : bv 32 := 0x00113423.
Lemma F_139c0 : fetch_word Ubsan.M.loaded_segments (0x139c0 : word) = Some W_139c0.
Proof. vm_refl. Qed.
Lemma D_139c0 : decode_any W_139c0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139c4 : bv 32 := 0x00813023.
Lemma F_139c4 : fetch_word Ubsan.M.loaded_segments (0x139c4 : word) = Some W_139c4.
Proof. vm_refl. Qed.
Lemma D_139c4 : decode_any W_139c4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139c8 : bv 32 := 0x01010413.
Lemma F_139c8 : fetch_word Ubsan.M.loaded_segments (0x139c8 : word) = Some W_139c8.
Proof. vm_refl. Qed.
Lemma D_139c8 : decode_any W_139c8 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139cc : bv 32 := 0x00013517.
Lemma F_139cc : fetch_word Ubsan.M.loaded_segments (0x139cc : word) = Some W_139cc.
Proof. vm_refl. Qed.
Lemma D_139cc : decode_any W_139cc = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139d0 : bv 32 := 0x12450513.
Lemma F_139d0 : fetch_word Ubsan.M.loaded_segments (0x139d0 : word) = Some W_139d0.
Proof. vm_refl. Qed.
Lemma D_139d0 : decode_any W_139d0 = Some (OpImm ALU_ADD 10 10 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139d4 : bv 32 := 0x00054503.
Lemma F_139d4 : fetch_word Ubsan.M.loaded_segments (0x139d4 : word) = Some W_139d4.
Proof. vm_refl. Qed.
Lemma D_139d4 : decode_any W_139d4 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139d8 : bv 32 := 0x00157513.
Lemma F_139d8 : fetch_word Ubsan.M.loaded_segments (0x139d8 : word) = Some W_139d8.
Proof. vm_refl. Qed.
Lemma D_139d8 : decode_any W_139d8 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139dc : bv 32 := 0x00050663.
Lemma F_139dc : fetch_word Ubsan.M.loaded_segments (0x139dc : word) = Some W_139dc.
Proof. vm_refl. Qed.
Lemma D_139dc : decode_any W_139dc = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139e8 : bv 32 := 0x00013517.
Lemma F_139e8 : fetch_word Ubsan.M.loaded_segments (0x139e8 : word) = Some W_139e8.
Proof. vm_refl. Qed.
Lemma D_139e8 : decode_any W_139e8 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139ec : bv 32 := 0x10850593.
Lemma F_139ec : fetch_word Ubsan.M.loaded_segments (0x139ec : word) = Some W_139ec.
Proof. vm_refl. Qed.
Lemma D_139ec : decode_any W_139ec = Some (OpImm ALU_ADD 11 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139f0 : bv 32 := 0x00100513.
Lemma F_139f0 : fetch_word Ubsan.M.loaded_segments (0x139f0 : word) = Some W_139f0.
Proof. vm_refl. Qed.
Lemma D_139f0 : decode_any W_139f0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139f4 : bv 32 := 0x00a58023.
Lemma F_139f4 : fetch_word Ubsan.M.loaded_segments (0x139f4 : word) = Some W_139f4.
Proof. vm_refl. Qed.
Lemma D_139f4 : decode_any W_139f4 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139f8 : bv 32 := 0x00012517.
Lemma F_139f8 : fetch_word Ubsan.M.loaded_segments (0x139f8 : word) = Some W_139f8.
Proof. vm_refl. Qed.
Lemma D_139f8 : decode_any W_139f8 = Some (Auipc 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_139fc : bv 32 := 0xd7853503.
Lemma F_139fc : fetch_word Ubsan.M.loaded_segments (0x139fc : word) = Some W_139fc.
Proof. vm_refl. Qed.
Lemma D_139fc : decode_any W_139fc = Some (Load SZ8 true 10 10 3448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a00 : bv 32 := 0x02050063.
Lemma F_13a00 : fetch_word Ubsan.M.loaded_segments (0x13a00 : word) = Some W_13a00.
Proof. vm_refl. Qed.
Lemma D_13a00 : decode_any W_13a00 = Some (Branch BC_EQ 10 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a20 : bv 32 := 0x00813083.
Lemma F_13a20 : fetch_word Ubsan.M.loaded_segments (0x13a20 : word) = Some W_13a20.
Proof. vm_refl. Qed.
Lemma D_13a20 : decode_any W_13a20 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a24 : bv 32 := 0x00013403.
Lemma F_13a24 : fetch_word Ubsan.M.loaded_segments (0x13a24 : word) = Some W_13a24.
Proof. vm_refl. Qed.
Lemma D_13a24 : decode_any W_13a24 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a28 : bv 32 := 0x01010113.
Lemma F_13a28 : fetch_word Ubsan.M.loaded_segments (0x13a28 : word) = Some W_13a28.
Proof. vm_refl. Qed.
Lemma D_13a28 : decode_any W_13a28 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a2c : bv 32 := 0x00008067.
Lemma F_13a2c : fetch_word Ubsan.M.loaded_segments (0x13a2c : word) = Some W_13a2c.
Proof. vm_refl. Qed.
Lemma D_13a2c : decode_any W_13a2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a30 : bv 32 := 0xff010113.
Lemma F_13a30 : fetch_word Ubsan.M.loaded_segments (0x13a30 : word) = Some W_13a30.
Proof. vm_refl. Qed.
Lemma D_13a30 : decode_any W_13a30 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a34 : bv 32 := 0x00113423.
Lemma F_13a34 : fetch_word Ubsan.M.loaded_segments (0x13a34 : word) = Some W_13a34.
Proof. vm_refl. Qed.
Lemma D_13a34 : decode_any W_13a34 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a38 : bv 32 := 0x00813023.
Lemma F_13a38 : fetch_word Ubsan.M.loaded_segments (0x13a38 : word) = Some W_13a38.
Proof. vm_refl. Qed.
Lemma D_13a38 : decode_any W_13a38 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a3c : bv 32 := 0x01010413.
Lemma F_13a3c : fetch_word Ubsan.M.loaded_segments (0x13a3c : word) = Some W_13a3c.
Proof. vm_refl. Qed.
Lemma D_13a3c : decode_any W_13a3c = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a40 : bv 32 := 0x00013517.
Lemma F_13a40 : fetch_word Ubsan.M.loaded_segments (0x13a40 : word) = Some W_13a40.
Proof. vm_refl. Qed.
Lemma D_13a40 : decode_any W_13a40 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a44 : bv 32 := 0x0f850513.
Lemma F_13a44 : fetch_word Ubsan.M.loaded_segments (0x13a44 : word) = Some W_13a44.
Proof. vm_refl. Qed.
Lemma D_13a44 : decode_any W_13a44 = Some (OpImm ALU_ADD 10 10 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a48 : bv 32 := 0x00054503.
Lemma F_13a48 : fetch_word Ubsan.M.loaded_segments (0x13a48 : word) = Some W_13a48.
Proof. vm_refl. Qed.
Lemma D_13a48 : decode_any W_13a48 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a4c : bv 32 := 0x00157513.
Lemma F_13a4c : fetch_word Ubsan.M.loaded_segments (0x13a4c : word) = Some W_13a4c.
Proof. vm_refl. Qed.
Lemma D_13a4c : decode_any W_13a4c = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a50 : bv 32 := 0x00050663.
Lemma F_13a50 : fetch_word Ubsan.M.loaded_segments (0x13a50 : word) = Some W_13a50.
Proof. vm_refl. Qed.
Lemma D_13a50 : decode_any W_13a50 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a5c : bv 32 := 0x00013517.
Lemma F_13a5c : fetch_word Ubsan.M.loaded_segments (0x13a5c : word) = Some W_13a5c.
Proof. vm_refl. Qed.
Lemma D_13a5c : decode_any W_13a5c = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a60 : bv 32 := 0x0dc50593.
Lemma F_13a60 : fetch_word Ubsan.M.loaded_segments (0x13a60 : word) = Some W_13a60.
Proof. vm_refl. Qed.
Lemma D_13a60 : decode_any W_13a60 = Some (OpImm ALU_ADD 11 10 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a64 : bv 32 := 0x00100513.
Lemma F_13a64 : fetch_word Ubsan.M.loaded_segments (0x13a64 : word) = Some W_13a64.
Proof. vm_refl. Qed.
Lemma D_13a64 : decode_any W_13a64 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a68 : bv 32 := 0x00a58023.
Lemma F_13a68 : fetch_word Ubsan.M.loaded_segments (0x13a68 : word) = Some W_13a68.
Proof. vm_refl. Qed.
Lemma D_13a68 : decode_any W_13a68 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a6c : bv 32 := 0x00012517.
Lemma F_13a6c : fetch_word Ubsan.M.loaded_segments (0x13a6c : word) = Some W_13a6c.
Proof. vm_refl. Qed.
Lemma D_13a6c : decode_any W_13a6c = Some (Auipc 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a70 : bv 32 := 0xd0c53503.
Lemma F_13a70 : fetch_word Ubsan.M.loaded_segments (0x13a70 : word) = Some W_13a70.
Proof. vm_refl. Qed.
Lemma D_13a70 : decode_any W_13a70 = Some (Load SZ8 true 10 10 3340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a74 : bv 32 := 0x00050e63.
Lemma F_13a74 : fetch_word Ubsan.M.loaded_segments (0x13a74 : word) = Some W_13a74.
Proof. vm_refl. Qed.
Lemma D_13a74 : decode_any W_13a74 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a78 : bv 32 := 0x0040006f.
Lemma F_13a78 : fetch_word Ubsan.M.loaded_segments (0x13a78 : word) = Some W_13a78.
Proof. vm_refl. Qed.
Lemma D_13a78 : decode_any W_13a78 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a7c : bv 32 := 0x00013517.
Lemma F_13a7c : fetch_word Ubsan.M.loaded_segments (0x13a7c : word) = Some W_13a7c.
Proof. vm_refl. Qed.
Lemma D_13a7c : decode_any W_13a7c = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a80 : bv 32 := 0xd6450513.
Lemma F_13a80 : fetch_word Ubsan.M.loaded_segments (0x13a80 : word) = Some W_13a80.
Proof. vm_refl. Qed.
Lemma D_13a80 : decode_any W_13a80 = Some (OpImm ALU_ADD 10 10 3428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a84 : bv 32 := 0x00053503.
Lemma F_13a84 : fetch_word Ubsan.M.loaded_segments (0x13a84 : word) = Some W_13a84.
Proof. vm_refl. Qed.
Lemma D_13a84 : decode_any W_13a84 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a88 : bv 32 := 0x3fc080ef.
Lemma F_13a88 : fetch_word Ubsan.M.loaded_segments (0x13a88 : word) = Some W_13a88.
Proof. vm_refl. Qed.
Lemma D_13a88 : decode_any W_13a88 = Some (Jal 1 33788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a8c : bv 32 := 0x0040006f.
Lemma F_13a8c : fetch_word Ubsan.M.loaded_segments (0x13a8c : word) = Some W_13a8c.
Proof. vm_refl. Qed.
Lemma D_13a8c : decode_any W_13a8c = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a90 : bv 32 := 0x00012517.
Lemma F_13a90 : fetch_word Ubsan.M.loaded_segments (0x13a90 : word) = Some W_13a90.
Proof. vm_refl. Qed.
Lemma D_13a90 : decode_any W_13a90 = Some (Auipc 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a94 : bv 32 := 0xcf053503.
Lemma F_13a94 : fetch_word Ubsan.M.loaded_segments (0x13a94 : word) = Some W_13a94.
Proof. vm_refl. Qed.
Lemma D_13a94 : decode_any W_13a94 = Some (Load SZ8 true 10 10 3312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13a98 : bv 32 := 0x00050c63.
Lemma F_13a98 : fetch_word Ubsan.M.loaded_segments (0x13a98 : word) = Some W_13a98.
Proof. vm_refl. Qed.
Lemma D_13a98 : decode_any W_13a98 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ab0 : bv 32 := 0x00813083.
Lemma F_13ab0 : fetch_word Ubsan.M.loaded_segments (0x13ab0 : word) = Some W_13ab0.
Proof. vm_refl. Qed.
Lemma D_13ab0 : decode_any W_13ab0 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ab4 : bv 32 := 0x00013403.
Lemma F_13ab4 : fetch_word Ubsan.M.loaded_segments (0x13ab4 : word) = Some W_13ab4.
Proof. vm_refl. Qed.
Lemma D_13ab4 : decode_any W_13ab4 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ab8 : bv 32 := 0x01010113.
Lemma F_13ab8 : fetch_word Ubsan.M.loaded_segments (0x13ab8 : word) = Some W_13ab8.
Proof. vm_refl. Qed.
Lemma D_13ab8 : decode_any W_13ab8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13abc : bv 32 := 0x00008067.
Lemma F_13abc : fetch_word Ubsan.M.loaded_segments (0x13abc : word) = Some W_13abc.
Proof. vm_refl. Qed.
Lemma D_13abc : decode_any W_13abc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b14 : bv 32 := 0x24050a63.
Lemma F_13b14 : fetch_word Ubsan.M.loaded_segments (0x13b14 : word) = Some W_13b14.
Proof. vm_refl. Qed.
Lemma D_13b14 : decode_any W_13b14 = Some (Branch BC_EQ 10 0 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b18 : bv 32 := 0x00050b93.
Lemma F_13b18 : fetch_word Ubsan.M.loaded_segments (0x13b18 : word) = Some W_13b18.
Proof. vm_refl. Qed.
Lemma D_13b18 : decode_any W_13b18 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b1c : bv 32 := 0x00000993.
Lemma F_13b1c : fetch_word Ubsan.M.loaded_segments (0x13b1c : word) = Some W_13b1c.
Proof. vm_refl. Qed.
Lemma D_13b1c : decode_any W_13b1c = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b20 : bv 32 := 0x00013517.
Lemma F_13b20 : fetch_word Ubsan.M.loaded_segments (0x13b20 : word) = Some W_13b20.
Proof. vm_refl. Qed.
Lemma D_13b20 : decode_any W_13b20 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b24 : bv 32 := 0x01950b13.
Lemma F_13b24 : fetch_word Ubsan.M.loaded_segments (0x13b24 : word) = Some W_13b24.
Proof. vm_refl. Qed.
Lemma D_13b24 : decode_any W_13b24 = Some (OpImm ALU_ADD 22 10 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b28 : bv 32 := 0x03501263.
Lemma F_13b28 : fetch_word Ubsan.M.loaded_segments (0x13b28 : word) = Some W_13b28.
Proof. vm_refl. Qed.
Lemma D_13b28 : decode_any W_13b28 = Some (Branch BC_NE 0 21 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b30 : bv 32 := 0x01348533.
Lemma F_13b30 : fetch_word Ubsan.M.loaded_segments (0x13b30 : word) = Some W_13b30.
Proof. vm_refl. Qed.
Lemma D_13b30 : decode_any W_13b30 = Some (Op ALU_ADD 10 9 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b34 : bv 32 := 0x000b0593.
Lemma F_13b34 : fetch_word Ubsan.M.loaded_segments (0x13b34 : word) = Some W_13b34.
Proof. vm_refl. Qed.
Lemma D_13b34 : decode_any W_13b34 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b38 : bv 32 := 0x000b8613.
Lemma F_13b38 : fetch_word Ubsan.M.loaded_segments (0x13b38 : word) = Some W_13b38.
Proof. vm_refl. Qed.
Lemma D_13b38 : decode_any W_13b38 = Some (OpImm ALU_ADD 12 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b3c : bv 32 := 0x7ad0f0ef.
Lemma F_13b3c : fetch_word Ubsan.M.loaded_segments (0x13b3c : word) = Some W_13b3c.
Proof. vm_refl. Qed.
Lemma D_13b3c : decode_any W_13b3c = Some (Jal 1 65452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b40 : bv 32 := 0x013b89b3.
Lemma F_13b40 : fetch_word Ubsan.M.loaded_segments (0x13b40 : word) = Some W_13b40.
Proof. vm_refl. Qed.
Lemma D_13b40 : decode_any W_13b40 = Some (Op ALU_ADD 19 23 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b44 : bv 32 := 0x00048b93.
Lemma F_13b44 : fetch_word Ubsan.M.loaded_segments (0x13b44 : word) = Some W_13b44.
Proof. vm_refl. Qed.
Lemma D_13b44 : decode_any W_13b44 = Some (OpImm ALU_ADD 23 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b48 : bv 32 := 0x01598663.
Lemma F_13b48 : fetch_word Ubsan.M.loaded_segments (0x13b48 : word) = Some W_13b48.
Proof. vm_refl. Qed.
Lemma D_13b48 : decode_any W_13b48 = Some (Branch BC_EQ 19 21 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b4c : bv 32 := 0x000b8493.
Lemma F_13b4c : fetch_word Ubsan.M.loaded_segments (0x13b4c : word) = Some W_13b4c.
Proof. vm_refl. Qed.
Lemma D_13b4c : decode_any W_13b4c = Some (OpImm ALU_ADD 9 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b50 : bv 32 := 0x03c0006f.
Lemma F_13b50 : fetch_word Ubsan.M.loaded_segments (0x13b50 : word) = Some W_13b50.
Proof. vm_refl. Qed.
Lemma D_13b50 : decode_any W_13b50 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b54 : bv 32 := 0x01a9d513.
Lemma F_13b54 : fetch_word Ubsan.M.loaded_segments (0x13b54 : word) = Some W_13b54.
Proof. vm_refl. Qed.
Lemma D_13b54 : decode_any W_13b54 = Some (ShiftImm ALU_SRL 10 19 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b58 : bv 32 := 0x1a051863.
Lemma F_13b58 : fetch_word Ubsan.M.loaded_segments (0x13b58 : word) = Some W_13b58.
Proof. vm_refl. Qed.
Lemma D_13b58 : decode_any W_13b58 = Some (Branch BC_NE 10 0 432, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b5c : bv 32 := 0x00199a93.
Lemma F_13b5c : fetch_word Ubsan.M.loaded_segments (0x13b5c : word) = Some W_13b5c.
Proof. vm_refl. Qed.
Lemma D_13b5c : decode_any W_13b5c = Some (ShiftImm ALU_SLL 21 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b60 : bv 32 := 0x000a8513.
Lemma F_13b60 : fetch_word Ubsan.M.loaded_segments (0x13b60 : word) = Some W_13b60.
Proof. vm_refl. Qed.
Lemma D_13b60 : decode_any W_13b60 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b64 : bv 32 := 0x714080ef.
Lemma F_13b64 : fetch_word Ubsan.M.loaded_segments (0x13b64 : word) = Some W_13b64.
Proof. vm_refl. Qed.
Lemma D_13b64 : decode_any W_13b64 = Some (Jal 1 34580, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b68 : bv 32 := 0x1c050063.
Lemma F_13b68 : fetch_word Ubsan.M.loaded_segments (0x13b68 : word) = Some W_13b68.
Proof. vm_refl. Qed.
Lemma D_13b68 : decode_any W_13b68 = Some (Branch BC_EQ 10 0 448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b6c : bv 32 := 0x00050493.
Lemma F_13b6c : fetch_word Ubsan.M.loaded_segments (0x13b6c : word) = Some W_13b6c.
Proof. vm_refl. Qed.
Lemma D_13b6c : decode_any W_13b6c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b8c : bv 32 := 0x413a8633.
Lemma F_13b8c : fetch_word Ubsan.M.loaded_segments (0x13b8c : word) = Some W_13b8c.
Proof. vm_refl. Qed.
Lemma D_13b8c : decode_any W_13b8c = Some (Op ALU_SUB 12 21 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b90 : bv 32 := 0x00010537.
Lemma F_13b90 : fetch_word Ubsan.M.loaded_segments (0x13b90 : word) = Some W_13b90.
Proof. vm_refl. Qed.
Lemma D_13b90 : decode_any W_13b90 = Some (Lui 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b94 : bv 32 := 0x00a66463.
Lemma F_13b94 : fetch_word Ubsan.M.loaded_segments (0x13b94 : word) = Some W_13b94.
Proof. vm_refl. Qed.
Lemma D_13b94 : decode_any W_13b94 = Some (Branch BC_LTU 12 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b98 : bv 32 := 0x00010637.
Lemma F_13b98 : fetch_word Ubsan.M.loaded_segments (0x13b98 : word) = Some W_13b98.
Proof. vm_refl. Qed.
Lemma D_13b98 : decode_any W_13b98 = Some (Lui 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13b9c : bv 32 := 0x000a0513.
Lemma F_13b9c : fetch_word Ubsan.M.loaded_segments (0x13b9c : word) = Some W_13b9c.
Proof. vm_refl. Qed.
Lemma D_13b9c : decode_any W_13b9c = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ba0 : bv 32 := 0x000b0593.
Lemma F_13ba0 : fetch_word Ubsan.M.loaded_segments (0x13ba0 : word) = Some W_13ba0.
Proof. vm_refl. Qed.
Lemma D_13ba0 : decode_any W_13ba0 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ba4 : bv 32 := 0x34d100ef.
Lemma F_13ba4 : fetch_word Ubsan.M.loaded_segments (0x13ba4 : word) = Some W_13ba4.
Proof. vm_refl. Qed.
Lemma D_13ba4 : decode_any W_13ba4 = Some (Jal 1 68428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ba8 : bv 32 := 0x14054263.
Lemma F_13ba8 : fetch_word Ubsan.M.loaded_segments (0x13ba8 : word) = Some W_13ba8.
Proof. vm_refl. Qed.
Lemma D_13ba8 : decode_any W_13ba8 = Some (Branch BC_LT 10 0 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bac : bv 32 := 0x00050b93.
Lemma F_13bac : fetch_word Ubsan.M.loaded_segments (0x13bac : word) = Some W_13bac.
Proof. vm_refl. Qed.
Lemma D_13bac : decode_any W_13bac = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bb0 : bv 32 := 0xf80510e3.
Lemma F_13bb0 : fetch_word Ubsan.M.loaded_segments (0x13bb0 : word) = Some W_13bb0.
Proof. vm_refl. Qed.
Lemma D_13bb0 : decode_any W_13bb0 = Some (Branch BC_NE 10 0 8064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bb4 : bv 32 := 0x000a0513.
Lemma F_13bb4 : fetch_word Ubsan.M.loaded_segments (0x13bb4 : word) = Some W_13bb4.
Proof. vm_refl. Qed.
Lemma D_13bb4 : decode_any W_13bb4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13bb8 : bv 32 := 0x2d9100ef.
Lemma F_13bb8 : fetch_word Ubsan.M.loaded_segments (0x13bb8 : word) = Some W_13bb8.
Proof. vm_refl. Qed.
Lemma D_13bb8 : decode_any W_13bb8 = Some (Jal 1 68312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c34 : bv 32 := 0x000ac663.
Lemma F_13c34 : fetch_word Ubsan.M.loaded_segments (0x13c34 : word) = Some W_13c34.
Proof. vm_refl. Qed.
Lemma D_13c34 : decode_any W_13c34 = Some (Branch BC_LT 21 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c38 : bv 32 := 0x00050413.
Lemma F_13c38 : fetch_word Ubsan.M.loaded_segments (0x13c38 : word) = Some W_13c38.
Proof. vm_refl. Qed.
Lemma D_13c38 : decode_any W_13c38 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c3c : bv 32 := 0x0780006f.
Lemma F_13c3c : fetch_word Ubsan.M.loaded_segments (0x13c3c : word) = Some W_13c3c.
Proof. vm_refl. Qed.
Lemma D_13c3c : decode_any W_13c3c = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c40 : bv 32 := 0x148000ef.
Lemma F_13c40 : fetch_word Ubsan.M.loaded_segments (0x13c40 : word) = Some W_13c40.
Proof. vm_refl. Qed.
Lemma D_13c40 : decode_any W_13c40 = Some (Jal 1 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c44 : bv 32 := 0x0fb00593.
Lemma F_13c44 : fetch_word Ubsan.M.loaded_segments (0x13c44 : word) = Some W_13c44.
Proof. vm_refl. Qed.
Lemma D_13c44 : decode_any W_13c44 = Some (OpImm ALU_ADD 11 0 251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c48 : bv 32 := 0x00050413.
Lemma F_13c48 : fetch_word Ubsan.M.loaded_segments (0x13c48 : word) = Some W_13c48.
Proof. vm_refl. Qed.
Lemma D_13c48 : decode_any W_13c48 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13c4c : bv 32 := 0x06b56463.
Lemma F_13c4c : fetch_word Ubsan.M.loaded_segments (0x13c4c : word) = Some W_13c4c.
Proof. vm_refl. Qed.
Lemma D_13c4c : decode_any W_13c4c = Some (Branch BC_LTU 10 11 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13ca8 : bv 32 := 0x6b950513.
Lemma F_13ca8 : fetch_word Ubsan.M.loaded_segments (0x13ca8 : word) = Some W_13ca8.
Proof. vm_refl. Qed.
Lemma D_13ca8 : decode_any W_13ca8 = Some (OpImm ALU_ADD 10 10 1721, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13cac : bv 32 := 0x00100613.
Lemma F_13cac : fetch_word Ubsan.M.loaded_segments (0x13cac : word) = Some W_13cac.
Proof. vm_refl. Qed.
Lemma D_13cac : decode_any W_13cac = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d88 : bv 32 := 0x00000513.
Lemma F_13d88 : fetch_word Ubsan.M.loaded_segments (0x13d88 : word) = Some W_13d88.
Proof. vm_refl. Qed.
Lemma D_13d88 : decode_any W_13d88 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_13d8c : bv 32 := 0x00008067.
Lemma F_13d8c : fetch_word Ubsan.M.loaded_segments (0x13d8c : word) = Some W_13d8c.
Proof. vm_refl. Qed.
Lemma D_13d8c : decode_any W_13d8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
