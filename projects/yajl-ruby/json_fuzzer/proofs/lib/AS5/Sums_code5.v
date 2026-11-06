(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.yajl_ruby.json_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)


(* [comment removed for export] *)
Definition W_6532c : bv 32 := 0x02060063.
Lemma F_6532c : fetch_word Asan.M.loaded_segments (0x653a0 : word) = Some W_6532c.
Proof. vm_refl. Qed.
Lemma D_6532c : decode_any W_6532c = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65330 : bv 32 := 0x00c50633.
Lemma F_65330 : fetch_word Asan.M.loaded_segments (0x653a4 : word) = Some W_65330.
Proof. vm_refl. Qed.
Lemma D_65330 : decode_any W_65330 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65334 : bv 32 := 0x00050693.
Lemma F_65334 : fetch_word Asan.M.loaded_segments (0x653a8 : word) = Some W_65334.
Proof. vm_refl. Qed.
Lemma D_65334 : decode_any W_65334 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65338 : bv 32 := 0x0005c703.
Lemma F_65338 : fetch_word Asan.M.loaded_segments (0x653ac : word) = Some W_65338.
Proof. vm_refl. Qed.
Lemma D_65338 : decode_any W_65338 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6533c : bv 32 := 0x00e68023.
Lemma F_6533c : fetch_word Asan.M.loaded_segments (0x653b0 : word) = Some W_6533c.
Proof. vm_refl. Qed.
Lemma D_6533c : decode_any W_6533c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65340 : bv 32 := 0x00168693.
Lemma F_65340 : fetch_word Asan.M.loaded_segments (0x653b4 : word) = Some W_65340.
Proof. vm_refl. Qed.
Lemma D_65340 : decode_any W_65340 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65344 : bv 32 := 0x00158593.
Lemma F_65344 : fetch_word Asan.M.loaded_segments (0x653b8 : word) = Some W_65344.
Proof. vm_refl. Qed.
Lemma D_65344 : decode_any W_65344 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65348 : bv 32 := 0xfec698e3.
Lemma F_65348 : fetch_word Asan.M.loaded_segments (0x653bc : word) = Some W_65348.
Proof. vm_refl. Qed.
Lemma D_65348 : decode_any W_65348 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6534c : bv 32 := 0x00008067.
Lemma F_6534c : fetch_word Asan.M.loaded_segments (0x653c0 : word) = Some W_6534c.
Proof. vm_refl. Qed.
Lemma D_6534c : decode_any W_6534c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition W_653a8 : bv 32 := 0x00a666b3.
Lemma F_653a8 : fetch_word Asan.M.loaded_segments (0x6541c : word) = Some W_653a8.
Proof. vm_refl. Qed.
Lemma D_653a8 : decode_any W_653a8 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653ac : bv 32 := 0x00f6f693.
Lemma F_653ac : fetch_word Asan.M.loaded_segments (0x65420 : word) = Some W_653ac.
Proof. vm_refl. Qed.
Lemma D_653ac : decode_any W_653ac = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653b0 : bv 32 := 0x02068063.
Lemma F_653b0 : fetch_word Asan.M.loaded_segments (0x65424 : word) = Some W_653b0.
Proof. vm_refl. Qed.
Lemma D_653b0 : decode_any W_653b0 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653b4 : bv 32 := 0x04060863.
Lemma F_653b4 : fetch_word Asan.M.loaded_segments (0x65428 : word) = Some W_653b4.
Proof. vm_refl. Qed.
Lemma D_653b4 : decode_any W_653b4 = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653b8 : bv 32 := 0x00c50633.
Lemma F_653b8 : fetch_word Asan.M.loaded_segments (0x6542c : word) = Some W_653b8.
Proof. vm_refl. Qed.
Lemma D_653b8 : decode_any W_653b8 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653bc : bv 32 := 0x00050693.
Lemma F_653bc : fetch_word Asan.M.loaded_segments (0x65430 : word) = Some W_653bc.
Proof. vm_refl. Qed.
Lemma D_653bc : decode_any W_653bc = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653c0 : bv 32 := 0x00b68023.
Lemma F_653c0 : fetch_word Asan.M.loaded_segments (0x65434 : word) = Some W_653c0.
Proof. vm_refl. Qed.
Lemma D_653c0 : decode_any W_653c0 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653c4 : bv 32 := 0x00168693.
Lemma F_653c4 : fetch_word Asan.M.loaded_segments (0x65438 : word) = Some W_653c4.
Proof. vm_refl. Qed.
Lemma D_653c4 : decode_any W_653c4 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653c8 : bv 32 := 0xfec69ce3.
Lemma F_653c8 : fetch_word Asan.M.loaded_segments (0x6543c : word) = Some W_653c8.
Proof. vm_refl. Qed.
Lemma D_653c8 : decode_any W_653c8 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653cc : bv 32 := 0x0380006f.
Lemma F_653cc : fetch_word Asan.M.loaded_segments (0x65440 : word) = Some W_653cc.
Proof. vm_refl. Qed.
Lemma D_653cc : decode_any W_653cc = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653d0 : bv 32 := 0x02060a63.
Lemma F_653d0 : fetch_word Asan.M.loaded_segments (0x65444 : word) = Some W_653d0.
Proof. vm_refl. Qed.
Lemma D_653d0 : decode_any W_653d0 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653d4 : bv 32 := 0x00c50633.
Lemma F_653d4 : fetch_word Asan.M.loaded_segments (0x65448 : word) = Some W_653d4.
Proof. vm_refl. Qed.
Lemma D_653d4 : decode_any W_653d4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653d8 : bv 32 := 0x00859693.
Lemma F_653d8 : fetch_word Asan.M.loaded_segments (0x6544c : word) = Some W_653d8.
Proof. vm_refl. Qed.
Lemma D_653d8 : decode_any W_653d8 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653dc : bv 32 := 0x00b6e5b3.
Lemma F_653dc : fetch_word Asan.M.loaded_segments (0x65450 : word) = Some W_653dc.
Proof. vm_refl. Qed.
Lemma D_653dc : decode_any W_653dc = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653e0 : bv 32 := 0x01059693.
Lemma F_653e0 : fetch_word Asan.M.loaded_segments (0x65454 : word) = Some W_653e0.
Proof. vm_refl. Qed.
Lemma D_653e0 : decode_any W_653e0 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653e4 : bv 32 := 0x00b6e5b3.
Lemma F_653e4 : fetch_word Asan.M.loaded_segments (0x65458 : word) = Some W_653e4.
Proof. vm_refl. Qed.
Lemma D_653e4 : decode_any W_653e4 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653e8 : bv 32 := 0x02059693.
Lemma F_653e8 : fetch_word Asan.M.loaded_segments (0x6545c : word) = Some W_653e8.
Proof. vm_refl. Qed.
Lemma D_653e8 : decode_any W_653e8 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653ec : bv 32 := 0x00b6e5b3.
Lemma F_653ec : fetch_word Asan.M.loaded_segments (0x65460 : word) = Some W_653ec.
Proof. vm_refl. Qed.
Lemma D_653ec : decode_any W_653ec = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653f0 : bv 32 := 0x00050693.
Lemma F_653f0 : fetch_word Asan.M.loaded_segments (0x65464 : word) = Some W_653f0.
Proof. vm_refl. Qed.
Lemma D_653f0 : decode_any W_653f0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653f4 : bv 32 := 0x00b6b023.
Lemma F_653f4 : fetch_word Asan.M.loaded_segments (0x65468 : word) = Some W_653f4.
Proof. vm_refl. Qed.
Lemma D_653f4 : decode_any W_653f4 = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653f8 : bv 32 := 0x00b6b423.
Lemma F_653f8 : fetch_word Asan.M.loaded_segments (0x6546c : word) = Some W_653f8.
Proof. vm_refl. Qed.
Lemma D_653f8 : decode_any W_653f8 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_653fc : bv 32 := 0x01068693.
Lemma F_653fc : fetch_word Asan.M.loaded_segments (0x65470 : word) = Some W_653fc.
Proof. vm_refl. Qed.
Lemma D_653fc : decode_any W_653fc = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65400 : bv 32 := 0xfec6eae3.
Lemma F_65400 : fetch_word Asan.M.loaded_segments (0x65474 : word) = Some W_65400.
Proof. vm_refl. Qed.
Lemma D_65400 : decode_any W_65400 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65404 : bv 32 := 0x00008067.
Lemma F_65404 : fetch_word Asan.M.loaded_segments (0x65478 : word) = Some W_65404.
Proof. vm_refl. Qed.
Lemma D_65404 : decode_any W_65404 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition W_658d8 : bv 32 := 0xff010113.
Lemma F_658d8 : fetch_word Asan.M.loaded_segments (0x6594c : word) = Some W_658d8.
Proof. vm_refl. Qed.
Lemma D_658d8 : decode_any W_658d8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_658dc : bv 32 := 0x00113423.
Lemma F_658dc : fetch_word Asan.M.loaded_segments (0x65950 : word) = Some W_658dc.
Proof. vm_refl. Qed.
Lemma D_658dc : decode_any W_658dc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_658e0 : bv 32 := 0x00058693.
Lemma F_658e0 : fetch_word Asan.M.loaded_segments (0x65954 : word) = Some W_658e0.
Proof. vm_refl. Qed.
Lemma D_658e0 : decode_any W_658e0 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_658e4 : bv 32 := 0x00100713.
Lemma F_658e4 : fetch_word Asan.M.loaded_segments (0x65958 : word) = Some W_658e4.
Proof. vm_refl. Qed.
Lemma D_658e4 : decode_any W_658e4 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_658e8 : bv 32 := 0x02871713.
Lemma F_658e8 : fetch_word Asan.M.loaded_segments (0x6595c : word) = Some W_658e8.
Proof. vm_refl. Qed.
Lemma D_658e8 : decode_any W_658e8 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_658ec : bv 32 := 0x00170593.
Lemma F_658ec : fetch_word Asan.M.loaded_segments (0x65960 : word) = Some W_658ec.
Proof. vm_refl. Qed.
Lemma D_658ec : decode_any W_658ec = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_658f0 : bv 32 := 0x08b6f263.
Lemma F_658f0 : fetch_word Asan.M.loaded_segments (0x65964 : word) = Some W_658f0.
Proof. vm_refl. Qed.
Lemma D_658f0 : decode_any W_658f0 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_658f4 : bv 32 := 0x00000593.
Lemma F_658f4 : fetch_word Asan.M.loaded_segments (0x65968 : word) = Some W_658f4.
Proof. vm_refl. Qed.
Lemma D_658f4 : decode_any W_658f4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_658f8 : bv 32 := 0x00d50733.
Lemma F_658f8 : fetch_word Asan.M.loaded_segments (0x6596c : word) = Some W_658f8.
Proof. vm_refl. Qed.
Lemma D_658f8 : decode_any W_658f8 = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_658fc : bv 32 := 0x00750793.
Lemma F_658fc : fetch_word Asan.M.loaded_segments (0x65970 : word) = Some W_658fc.
Proof. vm_refl. Qed.
Lemma D_658fc : decode_any W_658fc = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65900 : bv 32 := 0xff87f793.
Lemma F_65900 : fetch_word Asan.M.loaded_segments (0x65974 : word) = Some W_65900.
Proof. vm_refl. Qed.
Lemma D_65900 : decode_any W_65900 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65904 : bv 32 := 0xff877613.
Lemma F_65904 : fetch_word Asan.M.loaded_segments (0x65978 : word) = Some W_65904.
Proof. vm_refl. Qed.
Lemma D_65904 : decode_any W_65904 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65908 : bv 32 := 0x02f57463.
Lemma F_65908 : fetch_word Asan.M.loaded_segments (0x6597c : word) = Some W_65908.
Proof. vm_refl. Qed.
Lemma D_65908 : decode_any W_65908 = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6590c : bv 32 := 0x02068263.
Lemma F_6590c : fetch_word Asan.M.loaded_segments (0x65980 : word) = Some W_6590c.
Proof. vm_refl. Qed.
Lemma D_6590c : decode_any W_6590c = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65910 : bv 32 := 0x00000593.
Lemma F_65910 : fetch_word Asan.M.loaded_segments (0x65984 : word) = Some W_65910.
Proof. vm_refl. Qed.
Lemma D_65910 : decode_any W_65910 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65914 : bv 32 := 0x00150693.
Lemma F_65914 : fetch_word Asan.M.loaded_segments (0x65988 : word) = Some W_65914.
Proof. vm_refl. Qed.
Lemma D_65914 : decode_any W_65914 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65918 : bv 32 := 0x00068813.
Lemma F_65918 : fetch_word Asan.M.loaded_segments (0x6598c : word) = Some W_65918.
Proof. vm_refl. Qed.
Lemma D_65918 : decode_any W_65918 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6591c : bv 32 := 0xfff6c683.
Lemma F_6591c : fetch_word Asan.M.loaded_segments (0x65990 : word) = Some W_6591c.
Proof. vm_refl. Qed.
Lemma D_6591c : decode_any W_6591c = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65920 : bv 32 := 0x00d5e5b3.
Lemma F_65920 : fetch_word Asan.M.loaded_segments (0x65994 : word) = Some W_65920.
Proof. vm_refl. Qed.
Lemma D_65920 : decode_any W_65920 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65924 : bv 32 := 0x00f87663.
Lemma F_65924 : fetch_word Asan.M.loaded_segments (0x65998 : word) = Some W_65924.
Proof. vm_refl. Qed.
Lemma D_65924 : decode_any W_65924 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65928 : bv 32 := 0x00180693.
Lemma F_65928 : fetch_word Asan.M.loaded_segments (0x6599c : word) = Some W_65928.
Proof. vm_refl. Qed.
Lemma D_65928 : decode_any W_65928 = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6592c : bv 32 := 0xfee866e3.
Lemma F_6592c : fetch_word Asan.M.loaded_segments (0x659a0 : word) = Some W_6592c.
Proof. vm_refl. Qed.
Lemma D_6592c : decode_any W_6592c = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65930 : bv 32 := 0x00c7fa63.
Lemma F_65930 : fetch_word Asan.M.loaded_segments (0x659a4 : word) = Some W_65930.
Proof. vm_refl. Qed.
Lemma D_65930 : decode_any W_65930 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65934 : bv 32 := 0x0007b683.
Lemma F_65934 : fetch_word Asan.M.loaded_segments (0x659a8 : word) = Some W_65934.
Proof. vm_refl. Qed.
Lemma D_65934 : decode_any W_65934 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65938 : bv 32 := 0x00878793.
Lemma F_65938 : fetch_word Asan.M.loaded_segments (0x659ac : word) = Some W_65938.
Proof. vm_refl. Qed.
Lemma D_65938 : decode_any W_65938 = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6593c : bv 32 := 0x00b6e5b3.
Lemma F_6593c : fetch_word Asan.M.loaded_segments (0x659b0 : word) = Some W_6593c.
Proof. vm_refl. Qed.
Lemma D_6593c : decode_any W_6593c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65940 : bv 32 := 0xfec7eae3.
Lemma F_65940 : fetch_word Asan.M.loaded_segments (0x659b4 : word) = Some W_65940.
Proof. vm_refl. Qed.
Lemma D_65940 : decode_any W_65940 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65944 : bv 32 := 0x02a66063.
Lemma F_65944 : fetch_word Asan.M.loaded_segments (0x659b8 : word) = Some W_65944.
Proof. vm_refl. Qed.
Lemma D_65944 : decode_any W_65944 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65948 : bv 32 := 0x00e67e63.
Lemma F_65948 : fetch_word Asan.M.loaded_segments (0x659bc : word) = Some W_65948.
Proof. vm_refl. Qed.
Lemma D_65948 : decode_any W_65948 = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6594c : bv 32 := 0x40c70733.
Lemma F_6594c : fetch_word Asan.M.loaded_segments (0x659c0 : word) = Some W_6594c.
Proof. vm_refl. Qed.
Lemma D_6594c : decode_any W_6594c = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65950 : bv 32 := 0x00064503.
Lemma F_65950 : fetch_word Asan.M.loaded_segments (0x659c4 : word) = Some W_65950.
Proof. vm_refl. Qed.
Lemma D_65950 : decode_any W_65950 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65954 : bv 32 := 0xfff70713.
Lemma F_65954 : fetch_word Asan.M.loaded_segments (0x659c8 : word) = Some W_65954.
Proof. vm_refl. Qed.
Lemma D_65954 : decode_any W_65954 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65958 : bv 32 := 0x00a5e5b3.
Lemma F_65958 : fetch_word Asan.M.loaded_segments (0x659cc : word) = Some W_65958.
Proof. vm_refl. Qed.
Lemma D_65958 : decode_any W_65958 = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6595c : bv 32 := 0x00160613.
Lemma F_6595c : fetch_word Asan.M.loaded_segments (0x659d0 : word) = Some W_6595c.
Proof. vm_refl. Qed.
Lemma D_6595c : decode_any W_6595c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65960 : bv 32 := 0xfe0718e3.
Lemma F_65960 : fetch_word Asan.M.loaded_segments (0x659d4 : word) = Some W_65960.
Proof. vm_refl. Qed.
Lemma D_65960 : decode_any W_65960 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65964 : bv 32 := 0x0015b513.
Lemma F_65964 : fetch_word Asan.M.loaded_segments (0x659d8 : word) = Some W_65964.
Proof. vm_refl. Qed.
Lemma D_65964 : decode_any W_65964 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65968 : bv 32 := 0x00813083.
Lemma F_65968 : fetch_word Asan.M.loaded_segments (0x659dc : word) = Some W_65968.
Proof. vm_refl. Qed.
Lemma D_65968 : decode_any W_65968 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6596c : bv 32 := 0x01010113.
Lemma F_6596c : fetch_word Asan.M.loaded_segments (0x659e0 : word) = Some W_6596c.
Proof. vm_refl. Qed.
Lemma D_6596c : decode_any W_6596c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_65970 : bv 32 := 0x00008067.
Lemma F_65970 : fetch_word Asan.M.loaded_segments (0x659e4 : word) = Some W_65970.
Proof. vm_refl. Qed.
Lemma D_65970 : decode_any W_65970 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

