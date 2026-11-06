(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition Wx_82c0c : bv 32 := 0x81010113.
Lemma Fx_82c0c : fetch_word Asan.M.loaded_segments (0x82c5c : word) = Some Wx_82c0c.
Proof. vm_refl. Qed.
Lemma Dx_82c0c : decode_any Wx_82c0c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c10 : bv 32 := 0x7e113423.
Lemma Fx_82c10 : fetch_word Asan.M.loaded_segments (0x82c60 : word) = Some Wx_82c10.
Proof. vm_refl. Qed.
Lemma Dx_82c10 : decode_any Wx_82c10 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c14 : bv 32 := 0x7e813023.
Lemma Fx_82c14 : fetch_word Asan.M.loaded_segments (0x82c64 : word) = Some Wx_82c14.
Proof. vm_refl. Qed.
Lemma Dx_82c14 : decode_any Wx_82c14 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c18 : bv 32 := 0x7c913c23.
Lemma Fx_82c18 : fetch_word Asan.M.loaded_segments (0x82c68 : word) = Some Wx_82c18.
Proof. vm_refl. Qed.
Lemma Dx_82c18 : decode_any Wx_82c18 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c1c : bv 32 := 0x7d213823.
Lemma Fx_82c1c : fetch_word Asan.M.loaded_segments (0x82c6c : word) = Some Wx_82c1c.
Proof. vm_refl. Qed.
Lemma Dx_82c1c : decode_any Wx_82c1c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c20 : bv 32 := 0x7d313423.
Lemma Fx_82c20 : fetch_word Asan.M.loaded_segments (0x82c70 : word) = Some Wx_82c20.
Proof. vm_refl. Qed.
Lemma Dx_82c20 : decode_any Wx_82c20 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c24 : bv 32 := 0x7d413023.
Lemma Fx_82c24 : fetch_word Asan.M.loaded_segments (0x82c74 : word) = Some Wx_82c24.
Proof. vm_refl. Qed.
Lemma Dx_82c24 : decode_any Wx_82c24 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c28 : bv 32 := 0x7b513c23.
Lemma Fx_82c28 : fetch_word Asan.M.loaded_segments (0x82c78 : word) = Some Wx_82c28.
Proof. vm_refl. Qed.
Lemma Dx_82c28 : decode_any Wx_82c28 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c2c : bv 32 := 0x7f010413.
Lemma Fx_82c2c : fetch_word Asan.M.loaded_segments (0x82c7c : word) = Some Wx_82c2c.
Proof. vm_refl. Qed.
Lemma Dx_82c2c : decode_any Wx_82c2c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c30 : bv 32 := 0xfa010113.
Lemma Fx_82c30 : fetch_word Asan.M.loaded_segments (0x82c80 : word) = Some Wx_82c30.
Proof. vm_refl. Qed.
Lemma Dx_82c30 : decode_any Wx_82c30 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c34 : bv 32 := 0x00058a13.
Lemma Fx_82c34 : fetch_word Asan.M.loaded_segments (0x82c84 : word) = Some Wx_82c34.
Proof. vm_refl. Qed.
Lemma Dx_82c34 : decode_any Wx_82c34 = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c38 : bv 32 := 0x000d0597.
Lemma Fx_82c38 : fetch_word Asan.M.loaded_segments (0x82c88 : word) = Some Wx_82c38.
Proof. vm_refl. Qed.
Lemma Dx_82c38 : decode_any Wx_82c38 = Some (Auipc 11 208, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c3c : bv 32 := 0x4a85b583.
Lemma Fx_82c3c : fetch_word Asan.M.loaded_segments (0x82c8c : word) = Some Wx_82c3c.
Proof. vm_refl. Qed.
Lemma Dx_82c3c : decode_any Wx_82c3c = Some (Load SZ8 true 11 11 1192, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c40 : bv 32 := 0x0605c583.
Lemma Fx_82c40 : fetch_word Asan.M.loaded_segments (0x82c90 : word) = Some Wx_82c40.
Proof. vm_refl. Qed.
Lemma Dx_82c40 : decode_any Wx_82c40 = Some (Load SZ1 false 11 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c44 : bv 32 := 0x22058863.
Lemma Fx_82c44 : fetch_word Asan.M.loaded_segments (0x82c94 : word) = Some Wx_82c44.
Proof. vm_refl. Qed.
Lemma Dx_82c44 : decode_any Wx_82c44 = Some (Branch BC_EQ 11 0 560, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c48 : bv 32 := 0x00068913.
Lemma Fx_82c48 : fetch_word Asan.M.loaded_segments (0x82c98 : word) = Some Wx_82c48.
Proof. vm_refl. Qed.
Lemma Dx_82c48 : decode_any Wx_82c48 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c4c : bv 32 := 0x00060993.
Lemma Fx_82c4c : fetch_word Asan.M.loaded_segments (0x82c9c : word) = Some Wx_82c4c.
Proof. vm_refl. Qed.
Lemma Dx_82c4c : decode_any Wx_82c4c = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c50 : bv 32 := 0x00050493.
Lemma Fx_82c50 : fetch_word Asan.M.loaded_segments (0x82ca0 : word) = Some Wx_82c50.
Proof. vm_refl. Qed.
Lemma Dx_82c50 : decode_any Wx_82c50 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c54 : bv 32 := 0x000d0517.
Lemma Fx_82c54 : fetch_word Asan.M.loaded_segments (0x82ca4 : word) = Some Wx_82c54.
Proof. vm_refl. Qed.
Lemma Dx_82c54 : decode_any Wx_82c54 = Some (Auipc 10 208, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c58 : bv 32 := 0x4e453503.
Lemma Fx_82c58 : fetch_word Asan.M.loaded_segments (0x82ca8 : word) = Some Wx_82c58.
Proof. vm_refl. Qed.
Lemma Dx_82c58 : decode_any Wx_82c58 = Some (Load SZ8 true 10 10 1252, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c5c : bv 32 := 0x00052503.
Lemma Fx_82c5c : fetch_word Asan.M.loaded_segments (0x82cac : word) = Some Wx_82c5c.
Proof. vm_refl. Qed.
Lemma Dx_82c5c : decode_any Wx_82c5c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c60 : bv 32 := 0x00300593.
Lemma Fx_82c60 : fetch_word Asan.M.loaded_segments (0x82cb0 : word) = Some Wx_82c60.
Proof. vm_refl. Qed.
Lemma Dx_82c60 : decode_any Wx_82c60 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c64 : bv 32 := 0x08b57063.
Lemma Fx_82c64 : fetch_word Asan.M.loaded_segments (0x82cb4 : word) = Some Wx_82c64.
Proof. vm_refl. Qed.
Lemma Dx_82c64 : decode_any Wx_82c64 = Some (Branch BC_GEU 10 11 128, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c68 : bv 32 := 0x0899fe63.
Lemma Fx_82c68 : fetch_word Asan.M.loaded_segments (0x82cb8 : word) = Some Wx_82c68.
Proof. vm_refl. Qed.
Lemma Dx_82c68 : decode_any Wx_82c68 = Some (Branch BC_GEU 19 9 156, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c6c : bv 32 := 0x80040513.
Lemma Fx_82c6c : fetch_word Asan.M.loaded_segments (0x82cbc : word) = Some Wx_82c6c.
Proof. vm_refl. Qed.
Lemma Dx_82c6c : decode_any Wx_82c6c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c70 : bv 32 := 0xfb050513.
Lemma Fx_82c70 : fetch_word Asan.M.loaded_segments (0x82cc0 : word) = Some Wx_82c70.
Proof. vm_refl. Qed.
Lemma Dx_82c70 : decode_any Wx_82c70 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c74 : bv 32 := 0x80040593.
Lemma Fx_82c74 : fetch_word Asan.M.loaded_segments (0x82cc4 : word) = Some Wx_82c74.
Proof. vm_refl. Qed.
Lemma Dx_82c74 : decode_any Wx_82c74 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c78 : bv 32 := 0xfc058593.
Lemma Fx_82c78 : fetch_word Asan.M.loaded_segments (0x82cc8 : word) = Some Wx_82c78.
Proof. vm_refl. Qed.
Lemma Dx_82c78 : decode_any Wx_82c78 = Some (OpImm ALU_ADD 11 11 4032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c7c : bv 32 := 0x80040613.
Lemma Fx_82c7c : fetch_word Asan.M.loaded_segments (0x82ccc : word) = Some Wx_82c7c.
Proof. vm_refl. Qed.
Lemma Dx_82c7c : decode_any Wx_82c7c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c80 : bv 32 := 0xfb060613.
Lemma Fx_82c80 : fetch_word Asan.M.loaded_segments (0x82cd0 : word) = Some Wx_82c80.
Proof. vm_refl. Qed.
Lemma Dx_82c80 : decode_any Wx_82c80 = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c84 : bv 32 := 0x7ff60a93.
Lemma Fx_82c84 : fetch_word Asan.M.loaded_segments (0x82cd4 : word) = Some Wx_82c84.
Proof. vm_refl. Qed.
Lemma Dx_82c84 : decode_any Wx_82c84 = Some (OpImm ALU_ADD 21 12 2047, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c88 : bv 32 := 0x000ab4a3.
Lemma Fx_82c88 : fetch_word Asan.M.loaded_segments (0x82cd8 : word) = Some Wx_82c88.
Proof. vm_refl. Qed.
Lemma Dx_82c88 : decode_any Wx_82c88 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c8c : bv 32 := 0x00b53023.
Lemma Fx_82c8c : fetch_word Asan.M.loaded_segments (0x82cdc : word) = Some Wx_82c8c.
Proof. vm_refl. Qed.
Lemma Dx_82c8c : decode_any Wx_82c8c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c90 : bv 32 := 0x00053423.
Lemma Fx_82c90 : fetch_word Asan.M.loaded_segments (0x82ce0 : word) = Some Wx_82c90.
Proof. vm_refl. Qed.
Lemma Dx_82c90 : decode_any Wx_82c90 = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c94 : bv 32 := 0x6451e0ef.
Lemma Fx_82c94 : fetch_word Asan.M.loaded_segments (0x82ce4 : word) = Some Wx_82c94.
Proof. vm_refl. Qed.
Lemma Dx_82c94 : decode_any Wx_82c94 = Some (Jal 1 126532, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c98 : bv 32 := 0x00050593.
Lemma Fx_82c98 : fetch_word Asan.M.loaded_segments (0x82ce8 : word) = Some Wx_82c98.
Proof. vm_refl. Qed.
Lemma Dx_82c98 : decode_any Wx_82c98 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82c9c : bv 32 := 0x000d0517.
Lemma Fx_82c9c : fetch_word Asan.M.loaded_segments (0x82cec : word) = Some Wx_82c9c.
Proof. vm_refl. Qed.
Lemma Dx_82c9c : decode_any Wx_82c9c = Some (Auipc 10 208, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ca0 : bv 32 := 0x43c53503.
Lemma Fx_82ca0 : fetch_word Asan.M.loaded_segments (0x82cf0 : word) = Some Wx_82ca0.
Proof. vm_refl. Qed.
Lemma Dx_82ca0 : decode_any Wx_82ca0 = Some (Load SZ8 true 10 10 1084, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ca4 : bv 32 := 0x02154703.
Lemma Fx_82ca4 : fetch_word Asan.M.loaded_segments (0x82cf4 : word) = Some Wx_82ca4.
Proof. vm_refl. Qed.
Lemma Dx_82ca4 : decode_any Wx_82ca4 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ca8 : bv 32 := 0x008ab4a3.
Lemma Fx_82ca8 : fetch_word Asan.M.loaded_segments (0x82cf8 : word) = Some Wx_82ca8.
Proof. vm_refl. Qed.
Lemma Dx_82ca8 : decode_any Wx_82ca8 = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cac : bv 32 := 0x80040513.
Lemma Fx_82cac : fetch_word Asan.M.loaded_segments (0x82cfc : word) = Some Wx_82cac.
Proof. vm_refl. Qed.
Lemma Dx_82cac : decode_any Wx_82cac = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cb0 : bv 32 := 0xfb050513.
Lemma Fx_82cb0 : fetch_word Asan.M.loaded_segments (0x82d00 : word) = Some Wx_82cb0.
Proof. vm_refl. Qed.
Lemma Dx_82cb0 : decode_any Wx_82cb0 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cb4 : bv 32 := 0x0ff00793.
Lemma Fx_82cb4 : fetch_word Asan.M.loaded_segments (0x82d04 : word) = Some Wx_82cb4.
Proof. vm_refl. Qed.
Lemma Dx_82cb4 : decode_any Wx_82cb4 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cb8 : bv 32 := 0x00040613.
Lemma Fx_82cb8 : fetch_word Asan.M.loaded_segments (0x82d08 : word) = Some Wx_82cb8.
Proof. vm_refl. Qed.
Lemma Dx_82cb8 : decode_any Wx_82cb8 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cbc : bv 32 := 0x00000693.
Lemma Fx_82cbc : fetch_word Asan.M.loaded_segments (0x82d0c : word) = Some Wx_82cbc.
Proof. vm_refl. Qed.
Lemma Dx_82cbc : decode_any Wx_82cbc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cc0 : bv 32 := 0x34c060ef.
Lemma Fx_82cc0 : fetch_word Asan.M.loaded_segments (0x82d10 : word) = Some Wx_82cc0.
Proof. vm_refl. Qed.
Lemma Dx_82cc0 : decode_any Wx_82cc0 = Some (Jal 1 25420, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cc4 : bv 32 := 0x80040713.
Lemma Fx_82cc4 : fetch_word Asan.M.loaded_segments (0x82d14 : word) = Some Wx_82cc4.
Proof. vm_refl. Qed.
Lemma Dx_82cc4 : decode_any Wx_82cc4 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cc8 : bv 32 := 0xfb070713.
Lemma Fx_82cc8 : fetch_word Asan.M.loaded_segments (0x82d18 : word) = Some Wx_82cc8.
Proof. vm_refl. Qed.
Lemma Dx_82cc8 : decode_any Wx_82cc8 = Some (OpImm ALU_ADD 14 14 4016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ccc : bv 32 := 0x00048513.
Lemma Fx_82ccc : fetch_word Asan.M.loaded_segments (0x82d1c : word) = Some Wx_82ccc.
Proof. vm_refl. Qed.
Lemma Dx_82ccc : decode_any Wx_82ccc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cd0 : bv 32 := 0x000a0593.
Lemma Fx_82cd0 : fetch_word Asan.M.loaded_segments (0x82d20 : word) = Some Wx_82cd0.
Proof. vm_refl. Qed.
Lemma Dx_82cd0 : decode_any Wx_82cd0 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cd4 : bv 32 := 0x00098613.
Lemma Fx_82cd4 : fetch_word Asan.M.loaded_segments (0x82d24 : word) = Some Wx_82cd4.
Proof. vm_refl. Qed.
Lemma Dx_82cd4 : decode_any Wx_82cd4 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cd8 : bv 32 := 0x00090693.
Lemma Fx_82cd8 : fetch_word Asan.M.loaded_segments (0x82d28 : word) = Some Wx_82cd8.
Proof. vm_refl. Qed.
Lemma Dx_82cd8 : decode_any Wx_82cd8 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cdc : bv 32 := 0x0e0030ef.
Lemma Fx_82cdc : fetch_word Asan.M.loaded_segments (0x82d2c : word) = Some Wx_82cdc.
Proof. vm_refl. Qed.
Lemma Dx_82cdc : decode_any Wx_82cdc = Some (Jal 1 12512, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ce0 : bv 32 := 0x0300006f.
Lemma Fx_82ce0 : fetch_word Asan.M.loaded_segments (0x82d30 : word) = Some Wx_82ce0.
Proof. vm_refl. Qed.
Lemma Dx_82ce0 : decode_any Wx_82ce0 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ce4 : bv 32 := 0xfff97517.
Lemma Fx_82ce4 : fetch_word Asan.M.loaded_segments (0x82d34 : word) = Some Wx_82ce4.
Proof. vm_refl. Qed.
Lemma Dx_82ce4 : decode_any Wx_82ce4 = Some (Auipc 10 1048471, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ce8 : bv 32 := 0x97a50513.
Lemma Fx_82ce8 : fetch_word Asan.M.loaded_segments (0x82d38 : word) = Some Wx_82ce8.
Proof. vm_refl. Qed.
Lemma Dx_82ce8 : decode_any Wx_82ce8 = Some (OpImm ALU_ADD 10 10 2426, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cec : bv 32 := 0x00048593.
Lemma Fx_82cec : fetch_word Asan.M.loaded_segments (0x82d3c : word) = Some Wx_82cec.
Proof. vm_refl. Qed.
Lemma Dx_82cec : decode_any Wx_82cec = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cf0 : bv 32 := 0x000a0613.
Lemma Fx_82cf0 : fetch_word Asan.M.loaded_segments (0x82d40 : word) = Some Wx_82cf0.
Proof. vm_refl. Qed.
Lemma Dx_82cf0 : decode_any Wx_82cf0 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cf4 : bv 32 := 0x00098693.
Lemma Fx_82cf4 : fetch_word Asan.M.loaded_segments (0x82d44 : word) = Some Wx_82cf4.
Proof. vm_refl. Qed.
Lemma Dx_82cf4 : decode_any Wx_82cf4 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cf8 : bv 32 := 0x00090713.
Lemma Fx_82cf8 : fetch_word Asan.M.loaded_segments (0x82d48 : word) = Some Wx_82cf8.
Proof. vm_refl. Qed.
Lemma Dx_82cf8 : decode_any Wx_82cf8 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82cfc : bv 32 := 0x491120ef.
Lemma Fx_82cfc : fetch_word Asan.M.loaded_segments (0x82d4c : word) = Some Wx_82cfc.
Proof. vm_refl. Qed.
Lemma Dx_82cfc : decode_any Wx_82cfc = Some (Jal 1 76944, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d00 : bv 32 := 0xf699e6e3.
Lemma Fx_82d00 : fetch_word Asan.M.loaded_segments (0x82d50 : word) = Some Wx_82d00.
Proof. vm_refl. Qed.
Lemma Dx_82d00 : decode_any Wx_82d00 = Some (Branch BC_LTU 19 9 8044, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d04 : bv 32 := 0xf72a64e3.
Lemma Fx_82d04 : fetch_word Asan.M.loaded_segments (0x82d54 : word) = Some Wx_82d04.
Proof. vm_refl. Qed.
Lemma Dx_82d04 : decode_any Wx_82d04 = Some (Branch BC_LTU 20 18 8040, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d08 : bv 32 := 0xf73a62e3.
Lemma Fx_82d08 : fetch_word Asan.M.loaded_segments (0x82d58 : word) = Some Wx_82d08.
Proof. vm_refl. Qed.
Lemma Dx_82d08 : decode_any Wx_82d08 = Some (Branch BC_LTU 20 19 8036, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d0c : bv 32 := 0xf69960e3.
Lemma Fx_82d0c : fetch_word Asan.M.loaded_segments (0x82d5c : word) = Some Wx_82d0c.
Proof. vm_refl. Qed.
Lemma Dx_82d0c : decode_any Wx_82d0c = Some (Branch BC_LTU 18 9 8032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d10 : bv 32 := 0x409a06b3.
Lemma Fx_82d10 : fetch_word Asan.M.loaded_segments (0x82d60 : word) = Some Wx_82d10.
Proof. vm_refl. Qed.
Lemma Dx_82d10 : decode_any Wx_82d10 = Some (Op ALU_SUB 13 20 9, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d14 : bv 32 := 0x00100713.
Lemma Fx_82d14 : fetch_word Asan.M.loaded_segments (0x82d64 : word) = Some Wx_82d14.
Proof. vm_refl. Qed.
Lemma Dx_82d14 : decode_any Wx_82d14 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d18 : bv 32 := 0x02871713.
Lemma Fx_82d18 : fetch_word Asan.M.loaded_segments (0x82d68 : word) = Some Wx_82d18.
Proof. vm_refl. Qed.
Lemma Dx_82d18 : decode_any Wx_82d18 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d1c : bv 32 := 0x00170513.
Lemma Fx_82d1c : fetch_word Asan.M.loaded_segments (0x82d6c : word) = Some Wx_82d1c.
Proof. vm_refl. Qed.
Lemma Dx_82d1c : decode_any Wx_82d1c = Some (OpImm ALU_ADD 10 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d20 : bv 32 := 0x04a6fa63.
Lemma Fx_82d20 : fetch_word Asan.M.loaded_segments (0x82d70 : word) = Some Wx_82d20.
Proof. vm_refl. Qed.
Lemma Dx_82d20 : decode_any Wx_82d20 = Some (Branch BC_GEU 13 10 84, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d24 : bv 32 := 0x15298863.
Lemma Fx_82d24 : fetch_word Asan.M.loaded_segments (0x82d74 : word) = Some Wx_82d24.
Proof. vm_refl. Qed.
Lemma Dx_82d24 : decode_any Wx_82d24 = Some (Branch BC_EQ 19 18 336, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d28 : bv 32 := 0x007a7513.
Lemma Fx_82d28 : fetch_word Asan.M.loaded_segments (0x82d78 : word) = Some Wx_82d28.
Proof. vm_refl. Qed.
Lemma Dx_82d28 : decode_any Wx_82d28 = Some (OpImm ALU_AND 10 20 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d2c : bv 32 := 0x06051063.
Lemma Fx_82d2c : fetch_word Asan.M.loaded_segments (0x82d7c : word) = Some Wx_82d2c.
Proof. vm_refl. Qed.
Lemma Dx_82d2c : decode_any Wx_82d2c = Some (Branch BC_NE 10 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d30 : bv 32 := 0x00098a13.
Lemma Fx_82d30 : fetch_word Asan.M.loaded_segments (0x82d80 : word) = Some Wx_82d30.
Proof. vm_refl. Qed.
Lemma Dx_82d30 : decode_any Wx_82d30 = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d34 : bv 32 := 0x00090a93.
Lemma Fx_82d34 : fetch_word Asan.M.loaded_segments (0x82d84 : word) = Some Wx_82d34.
Proof. vm_refl. Qed.
Lemma Dx_82d34 : decode_any Wx_82d34 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d38 : bv 32 := 0x00048513.
Lemma Fx_82d38 : fetch_word Asan.M.loaded_segments (0x82d88 : word) = Some Wx_82d38.
Proof. vm_refl. Qed.
Lemma Dx_82d38 : decode_any Wx_82d38 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d3c : bv 32 := 0x0074f993.
Lemma Fx_82d3c : fetch_word Asan.M.loaded_segments (0x82d8c : word) = Some Wx_82d3c.
Proof. vm_refl. Qed.
Lemma Dx_82d3c : decode_any Wx_82d3c = Some (OpImm ALU_AND 19 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d40 : bv 32 := 0x08099e63.
Lemma Fx_82d40 : fetch_word Asan.M.loaded_segments (0x82d90 : word) = Some Wx_82d40.
Proof. vm_refl. Qed.
Lemma Dx_82d40 : decode_any Wx_82d40 = Some (Branch BC_NE 19 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d44 : bv 32 := 0x000a0593.
Lemma Fx_82d44 : fetch_word Asan.M.loaded_segments (0x82d94 : word) = Some Wx_82d44.
Proof. vm_refl. Qed.
Lemma Dx_82d44 : decode_any Wx_82d44 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d48 : bv 32 := 0x000a0513.
Lemma Fx_82d48 : fetch_word Asan.M.loaded_segments (0x82d98 : word) = Some Wx_82d48.
Proof. vm_refl. Qed.
Lemma Dx_82d48 : decode_any Wx_82d48 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d4c : bv 32 := 0x0d5a6863.
Lemma Fx_82d4c : fetch_word Asan.M.loaded_segments (0x82d9c : word) = Some Wx_82d4c.
Proof. vm_refl. Qed.
Lemma Dx_82d4c : decode_any Wx_82d4c = Some (Branch BC_LTU 20 21 208, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d50 : bv 32 := 0xff8af513.
Lemma Fx_82d50 : fetch_word Asan.M.loaded_segments (0x82da0 : word) = Some Wx_82d50.
Proof. vm_refl. Qed.
Lemma Dx_82d50 : decode_any Wx_82d50 = Some (OpImm ALU_AND 10 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d54 : bv 32 := 0x0cbaf863.
Lemma Fx_82d54 : fetch_word Asan.M.loaded_segments (0x82da4 : word) = Some Wx_82d54.
Proof. vm_refl. Qed.
Lemma Dx_82d54 : decode_any Wx_82d54 = Some (Branch BC_GEU 21 11 208, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d58 : bv 32 := 0xff8af493.
Lemma Fx_82d58 : fetch_word Asan.M.loaded_segments (0x82da8 : word) = Some Wx_82d58.
Proof. vm_refl. Qed.
Lemma Dx_82d58 : decode_any Wx_82d58 = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d5c : bv 32 := 0x007a8613.
Lemma Fx_82d5c : fetch_word Asan.M.loaded_segments (0x82dac : word) = Some Wx_82d5c.
Proof. vm_refl. Qed.
Lemma Dx_82d5c : decode_any Wx_82d5c = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d60 : bv 32 := 0xff867913.
Lemma Fx_82d60 : fetch_word Asan.M.loaded_segments (0x82db0 : word) = Some Wx_82d60.
Proof. vm_refl. Qed.
Lemma Dx_82d60 : decode_any Wx_82d60 = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d64 : bv 32 := 0x0c957a63.
Lemma Fx_82d64 : fetch_word Asan.M.loaded_segments (0x82db4 : word) = Some Wx_82d64.
Proof. vm_refl. Qed.
Lemma Dx_82d64 : decode_any Wx_82d64 = Some (Branch BC_GEU 10 9 212, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d68 : bv 32 := 0x40a485b3.
Lemma Fx_82d68 : fetch_word Asan.M.loaded_segments (0x82db8 : word) = Some Wx_82d68.
Proof. vm_refl. Qed.
Lemma Dx_82d68 : decode_any Wx_82d68 = Some (Op ALU_SUB 11 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d6c : bv 32 := 0x00000613.
Lemma Fx_82d6c : fetch_word Asan.M.loaded_segments (0x82dbc : word) = Some Wx_82d6c.
Proof. vm_refl. Qed.
Lemma Dx_82d6c : decode_any Wx_82d6c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d70 : bv 32 := 0x0e00006f.
Lemma Fx_82d70 : fetch_word Asan.M.loaded_segments (0x82dc0 : word) = Some Wx_82d70.
Proof. vm_refl. Qed.
Lemma Dx_82d70 : decode_any Wx_82d70 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d74 : bv 32 := 0xfff9f517.
Lemma Fx_82d74 : fetch_word Asan.M.loaded_segments (0x82dc4 : word) = Some Wx_82d74.
Proof. vm_refl. Qed.
Lemma Dx_82d74 : decode_any Wx_82d74 = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d78 : bv 32 := 0xfffa0597.
Lemma Fx_82d78 : fetch_word Asan.M.loaded_segments (0x82dc8 : word) = Some Wx_82d78.
Proof. vm_refl. Qed.
Lemma Dx_82d78 : decode_any Wx_82d78 = Some (Auipc 11 1048480, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d7c : bv 32 := 0xef750513.
Lemma Fx_82d7c : fetch_word Asan.M.loaded_segments (0x82dcc : word) = Some Wx_82d7c.
Proof. vm_refl. Qed.
Lemma Dx_82d7c : decode_any Wx_82d7c = Some (OpImm ALU_ADD 10 10 3831, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d80 : bv 32 := 0x0f858613.
Lemma Fx_82d80 : fetch_word Asan.M.loaded_segments (0x82dd0 : word) = Some Wx_82d80.
Proof. vm_refl. Qed.
Lemma Dx_82d80 : decode_any Wx_82d80 = Some (OpImm ALU_ADD 12 11 248, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d84 : bv 32 := 0x1b600593.
Lemma Fx_82d84 : fetch_word Asan.M.loaded_segments (0x82dd4 : word) = Some Wx_82d84.
Proof. vm_refl. Qed.
Lemma Dx_82d84 : decode_any Wx_82d84 = Some (OpImm ALU_ADD 11 0 438, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d88 : bv 32 := 0x58c170ef.
Lemma Fx_82d88 : fetch_word Asan.M.loaded_segments (0x82dd8 : word) = Some Wx_82d88.
Proof. vm_refl. Qed.
Lemma Dx_82d88 : decode_any Wx_82d88 = Some (Jal 1 95628, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d8c : bv 32 := 0xff8a7a93.
Lemma Fx_82d8c : fetch_word Asan.M.loaded_segments (0x82ddc : word) = Some Wx_82d8c.
Proof. vm_refl. Qed.
Lemma Dx_82d8c : decode_any Wx_82d8c = Some (OpImm ALU_AND 21 20 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d90 : bv 32 := 0x00098593.
Lemma Fx_82d90 : fetch_word Asan.M.loaded_segments (0x82de0 : word) = Some Wx_82d90.
Proof. vm_refl. Qed.
Lemma Dx_82d90 : decode_any Wx_82d90 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d94 : bv 32 := 0x01396463.
Lemma Fx_82d94 : fetch_word Asan.M.loaded_segments (0x82de4 : word) = Some Wx_82d94.
Proof. vm_refl. Qed.
Lemma Dx_82d94 : decode_any Wx_82d94 = Some (Branch BC_LTU 18 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d98 : bv 32 := 0x00090593.
Lemma Fx_82d98 : fetch_word Asan.M.loaded_segments (0x82de8 : word) = Some Wx_82d98.
Proof. vm_refl. Qed.
Lemma Dx_82d98 : decode_any Wx_82d98 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82d9c : bv 32 := 0xf8bafae3.
Lemma Fx_82d9c : fetch_word Asan.M.loaded_segments (0x82dec : word) = Some Wx_82d9c.
Proof. vm_refl. Qed.
Lemma Dx_82d9c : decode_any Wx_82d9c = Some (Branch BC_GEU 21 11 8084, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82da0 : bv 32 := 0x000d0597.
Lemma Fx_82da0 : fetch_word Asan.M.loaded_segments (0x82df0 : word) = Some Wx_82da0.
Proof. vm_refl. Qed.
Lemma Dx_82da0 : decode_any Wx_82da0 = Some (Auipc 11 208, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82da4 : bv 32 := 0x3485b583.
Lemma Fx_82da4 : fetch_word Asan.M.loaded_segments (0x82df4 : word) = Some Wx_82da4.
Proof. vm_refl. Qed.
Lemma Dx_82da4 : decode_any Wx_82da4 = Some (Load SZ8 true 11 11 840, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82da8 : bv 32 := 0x0005b583.
Lemma Fx_82da8 : fetch_word Asan.M.loaded_segments (0x82df8 : word) = Some Wx_82da8.
Proof. vm_refl. Qed.
Lemma Dx_82da8 : decode_any Wx_82da8 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82dac : bv 32 := 0x003a5613.
Lemma Fx_82dac : fetch_word Asan.M.loaded_segments (0x82dfc : word) = Some Wx_82dac.
Proof. vm_refl. Qed.
Lemma Dx_82dac : decode_any Wx_82dac = Some (ShiftImm ALU_SRL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82db0 : bv 32 := 0x00c585b3.
Lemma Fx_82db0 : fetch_word Asan.M.loaded_segments (0x82e00 : word) = Some Wx_82db0.
Proof. vm_refl. Qed.
Lemma Dx_82db0 : decode_any Wx_82db0 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82db4 : bv 32 := 0x00058583.
Lemma Fx_82db4 : fetch_word Asan.M.loaded_segments (0x82e04 : word) = Some Wx_82db4.
Proof. vm_refl. Qed.
Lemma Dx_82db4 : decode_any Wx_82db4 = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82db8 : bv 32 := 0x00058463.
Lemma Fx_82db8 : fetch_word Asan.M.loaded_segments (0x82e08 : word) = Some Wx_82db8.
Proof. vm_refl. Qed.
Lemma Dx_82db8 : decode_any Wx_82db8 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82dbc : bv 32 := 0xf6b55ae3.
Lemma Fx_82dbc : fetch_word Asan.M.loaded_segments (0x82e0c : word) = Some Wx_82dbc.
Proof. vm_refl. Qed.
Lemma Dx_82dbc : decode_any Wx_82dbc = Some (Branch BC_GE 10 11 8052, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82dc0 : bv 32 := 0x000a8513.
Lemma Fx_82dc0 : fetch_word Asan.M.loaded_segments (0x82e10 : word) = Some Wx_82dc0.
Proof. vm_refl. Qed.
Lemma Dx_82dc0 : decode_any Wx_82dc0 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82dc4 : bv 32 := 0x0e9aea63.
Lemma Fx_82dc4 : fetch_word Asan.M.loaded_segments (0x82e14 : word) = Some Wx_82dc4.
Proof. vm_refl. Qed.
Lemma Dx_82dc4 : decode_any Wx_82dc4 = Some (Branch BC_LTU 21 9 244, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82dc8 : bv 32 := 0x00048513.
Lemma Fx_82dc8 : fetch_word Asan.M.loaded_segments (0x82e18 : word) = Some Wx_82dc8.
Proof. vm_refl. Qed.
Lemma Dx_82dc8 : decode_any Wx_82dc8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82dcc : bv 32 := 0x000a8a13.
Lemma Fx_82dcc : fetch_word Asan.M.loaded_segments (0x82e1c : word) = Some Wx_82dcc.
Proof. vm_refl. Qed.
Lemma Dx_82dcc : decode_any Wx_82dcc = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82dd0 : bv 32 := 0x0f3af863.
Lemma Fx_82dd0 : fetch_word Asan.M.loaded_segments (0x82e20 : word) = Some Wx_82dd0.
Proof. vm_refl. Qed.
Lemma Dx_82dd0 : decode_any Wx_82dd0 = Some (Branch BC_GEU 21 19 240, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82dd4 : bv 32 := 0xf72ae4e3.
Lemma Fx_82dd4 : fetch_word Asan.M.loaded_segments (0x82e24 : word) = Some Wx_82dd4.
Proof. vm_refl. Qed.
Lemma Dx_82dd4 : decode_any Wx_82dd4 = Some (Branch BC_LTU 21 18 8040, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82dd8 : bv 32 := 0x0f00006f.
Lemma Fx_82dd8 : fetch_word Asan.M.loaded_segments (0x82e28 : word) = Some Wx_82dd8.
Proof. vm_refl. Qed.
Lemma Dx_82dd8 : decode_any Wx_82dd8 = Some (Jal 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ddc : bv 32 := 0xf74504e3.
Lemma Fx_82ddc : fetch_word Asan.M.loaded_segments (0x82e2c : word) = Some Wx_82ddc.
Proof. vm_refl. Qed.
Lemma Dx_82ddc : decode_any Wx_82ddc = Some (Branch BC_EQ 10 20 8040, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82de0 : bv 32 := 0xf75512e3.
Lemma Fx_82de0 : fetch_word Asan.M.loaded_segments (0x82e30 : word) = Some Wx_82de0.
Proof. vm_refl. Qed.
Lemma Dx_82de0 : decode_any Wx_82de0 = Some (Branch BC_NE 10 21 8036, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82de4 : bv 32 := 0x00748593.
Lemma Fx_82de4 : fetch_word Asan.M.loaded_segments (0x82e34 : word) = Some Wx_82de4.
Proof. vm_refl. Qed.
Lemma Dx_82de4 : decode_any Wx_82de4 = Some (OpImm ALU_ADD 11 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82de8 : bv 32 := 0xff85f913.
Lemma Fx_82de8 : fetch_word Asan.M.loaded_segments (0x82e38 : word) = Some Wx_82de8.
Proof. vm_refl. Qed.
Lemma Dx_82de8 : decode_any Wx_82de8 = Some (OpImm ALU_AND 18 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82dec : bv 32 := 0xf5257ce3.
Lemma Fx_82dec : fetch_word Asan.M.loaded_segments (0x82e3c : word) = Some Wx_82dec.
Proof. vm_refl. Qed.
Lemma Dx_82dec : decode_any Wx_82dec = Some (Branch BC_GEU 10 18 8024, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82df0 : bv 32 := 0xff84f513.
Lemma Fx_82df0 : fetch_word Asan.M.loaded_segments (0x82e40 : word) = Some Wx_82df0.
Proof. vm_refl. Qed.
Lemma Dx_82df0 : decode_any Wx_82df0 = Some (OpImm ALU_AND 10 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82df4 : bv 32 := 0xbd0ff0ef.
Lemma Fx_82df4 : fetch_word Asan.M.loaded_segments (0x82e44 : word) = Some Wx_82df4.
Proof. vm_refl. Qed.
Lemma Dx_82df4 : decode_any Wx_82df4 = Some (Jal 1 2094032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82df8 : bv 32 := 0x01350023.
Lemma Fx_82df8 : fetch_word Asan.M.loaded_segments (0x82e48 : word) = Some Wx_82df8.
Proof. vm_refl. Qed.
Lemma Dx_82df8 : decode_any Wx_82df8 = Some (Store SZ1 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82dfc : bv 32 := 0x00090593.
Lemma Fx_82dfc : fetch_word Asan.M.loaded_segments (0x82e4c : word) = Some Wx_82dfc.
Proof. vm_refl. Qed.
Lemma Dx_82dfc : decode_any Wx_82dfc = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e00 : bv 32 := 0x012a6463.
Lemma Fx_82e00 : fetch_word Asan.M.loaded_segments (0x82e50 : word) = Some Wx_82e00.
Proof. vm_refl. Qed.
Lemma Dx_82e00 : decode_any Wx_82e00 = Some (Branch BC_LTU 20 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e04 : bv 32 := 0x000a0593.
Lemma Fx_82e04 : fetch_word Asan.M.loaded_segments (0x82e54 : word) = Some Wx_82e04.
Proof. vm_refl. Qed.
Lemma Dx_82e04 : decode_any Wx_82e04 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e08 : bv 32 := 0x012ae463.
Lemma Fx_82e08 : fetch_word Asan.M.loaded_segments (0x82e58 : word) = Some Wx_82e08.
Proof. vm_refl. Qed.
Lemma Dx_82e08 : decode_any Wx_82e08 = Some (Branch BC_LTU 21 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e0c : bv 32 := 0x000a8913.
Lemma Fx_82e0c : fetch_word Asan.M.loaded_segments (0x82e5c : word) = Some Wx_82e0c.
Proof. vm_refl. Qed.
Lemma Dx_82e0c : decode_any Wx_82e0c = Some (OpImm ALU_ADD 18 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e10 : bv 32 := 0x00090a93.
Lemma Fx_82e10 : fetch_word Asan.M.loaded_segments (0x82e60 : word) = Some Wx_82e10.
Proof. vm_refl. Qed.
Lemma Dx_82e10 : decode_any Wx_82e10 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e14 : bv 32 := 0x00058513.
Lemma Fx_82e14 : fetch_word Asan.M.loaded_segments (0x82e64 : word) = Some Wx_82e14.
Proof. vm_refl. Qed.
Lemma Dx_82e14 : decode_any Wx_82e14 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e18 : bv 32 := 0xf325fce3.
Lemma Fx_82e18 : fetch_word Asan.M.loaded_segments (0x82e68 : word) = Some Wx_82e18.
Proof. vm_refl. Qed.
Lemma Dx_82e18 : decode_any Wx_82e18 = Some (Branch BC_GEU 11 18 7992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e1c : bv 32 := 0xff857513.
Lemma Fx_82e1c : fetch_word Asan.M.loaded_segments (0x82e6c : word) = Some Wx_82e1c.
Proof. vm_refl. Qed.
Lemma Dx_82e1c : decode_any Wx_82e1c = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e20 : bv 32 := 0xf2baece3.
Lemma Fx_82e20 : fetch_word Asan.M.loaded_segments (0x82e70 : word) = Some Wx_82e20.
Proof. vm_refl. Qed.
Lemma Dx_82e20 : decode_any Wx_82e20 = Some (Branch BC_LTU 21 11 7992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e24 : bv 32 := 0x000a8593.
Lemma Fx_82e24 : fetch_word Asan.M.loaded_segments (0x82e74 : word) = Some Wx_82e24.
Proof. vm_refl. Qed.
Lemma Dx_82e24 : decode_any Wx_82e24 = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e28 : bv 32 := 0xff8af493.
Lemma Fx_82e28 : fetch_word Asan.M.loaded_segments (0x82e78 : word) = Some Wx_82e28.
Proof. vm_refl. Qed.
Lemma Dx_82e28 : decode_any Wx_82e28 = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e2c : bv 32 := 0x007a8613.
Lemma Fx_82e2c : fetch_word Asan.M.loaded_segments (0x82e7c : word) = Some Wx_82e2c.
Proof. vm_refl. Qed.
Lemma Dx_82e2c : decode_any Wx_82e2c = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e30 : bv 32 := 0xff867913.
Lemma Fx_82e30 : fetch_word Asan.M.loaded_segments (0x82e80 : word) = Some Wx_82e30.
Proof. vm_refl. Qed.
Lemma Dx_82e30 : decode_any Wx_82e30 = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e34 : bv 32 := 0xf2956ae3.
Lemma Fx_82e34 : fetch_word Asan.M.loaded_segments (0x82e84 : word) = Some Wx_82e34.
Proof. vm_refl. Qed.
Lemma Dx_82e34 : decode_any Wx_82e34 = Some (Branch BC_LTU 10 9 7988, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e38 : bv 32 := 0x00758513.
Lemma Fx_82e38 : fetch_word Asan.M.loaded_segments (0x82e88 : word) = Some Wx_82e38.
Proof. vm_refl. Qed.
Lemma Dx_82e38 : decode_any Wx_82e38 = Some (OpImm ALU_ADD 10 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e3c : bv 32 := 0xff857513.
Lemma Fx_82e3c : fetch_word Asan.M.loaded_segments (0x82e8c : word) = Some Wx_82e3c.
Proof. vm_refl. Qed.
Lemma Dx_82e3c : decode_any Wx_82e3c = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e40 : bv 32 := 0x00a97a63.
Lemma Fx_82e40 : fetch_word Asan.M.loaded_segments (0x82e90 : word) = Some Wx_82e40.
Proof. vm_refl. Qed.
Lemma Dx_82e40 : decode_any Wx_82e40 = Some (Branch BC_GEU 18 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e44 : bv 32 := 0x412505b3.
Lemma Fx_82e44 : fetch_word Asan.M.loaded_segments (0x82e94 : word) = Some Wx_82e44.
Proof. vm_refl. Qed.
Lemma Dx_82e44 : decode_any Wx_82e44 = Some (Op ALU_SUB 11 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e48 : bv 32 := 0x0fc00613.
Lemma Fx_82e48 : fetch_word Asan.M.loaded_segments (0x82e98 : word) = Some Wx_82e48.
Proof. vm_refl. Qed.
Lemma Dx_82e48 : decode_any Wx_82e48 = Some (OpImm ALU_ADD 12 0 252, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e4c : bv 32 := 0x00090513.
Lemma Fx_82e4c : fetch_word Asan.M.loaded_segments (0x82e9c : word) = Some Wx_82e4c.
Proof. vm_refl. Qed.
Lemma Dx_82e4c : decode_any Wx_82e4c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e50 : bv 32 := 0xe79fe0ef.
Lemma Fx_82e50 : fetch_word Asan.M.loaded_segments (0x82ea0 : word) = Some Wx_82e50.
Proof. vm_refl. Qed.
Lemma Dx_82e50 : decode_any Wx_82e50 = Some (Jal 1 2092664, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e54 : bv 32 := 0x02990063.
Lemma Fx_82e54 : fetch_word Asan.M.loaded_segments (0x82ea4 : word) = Some Wx_82e54.
Proof. vm_refl. Qed.
Lemma Dx_82e54 : decode_any Wx_82e54 = Some (Branch BC_EQ 18 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e58 : bv 32 := 0x409906b3.
Lemma Fx_82e58 : fetch_word Asan.M.loaded_segments (0x82ea8 : word) = Some Wx_82e58.
Proof. vm_refl. Qed.
Lemma Dx_82e58 : decode_any Wx_82e58 = Some (Op ALU_SUB 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e5c : bv 32 := 0x00800513.
Lemma Fx_82e5c : fetch_word Asan.M.loaded_segments (0x82eac : word) = Some Wx_82e5c.
Proof. vm_refl. Qed.
Lemma Dx_82e5c : decode_any Wx_82e5c = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e60 : bv 32 := 0x02a69e63.
Lemma Fx_82e60 : fetch_word Asan.M.loaded_segments (0x82eb0 : word) = Some Wx_82e60.
Proof. vm_refl. Qed.
Lemma Dx_82e60 : decode_any Wx_82e60 = Some (Branch BC_NE 13 10 60, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e64 : bv 32 := 0x007af913.
Lemma Fx_82e64 : fetch_word Asan.M.loaded_segments (0x82eb4 : word) = Some Wx_82e64.
Proof. vm_refl. Qed.
Lemma Dx_82e64 : decode_any Wx_82e64 = Some (OpImm ALU_AND 18 21 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e68 : bv 32 := 0x00048513.
Lemma Fx_82e68 : fetch_word Asan.M.loaded_segments (0x82eb8 : word) = Some Wx_82e68.
Proof. vm_refl. Qed.
Lemma Dx_82e68 : decode_any Wx_82e68 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e6c : bv 32 := 0xb58ff0ef.
Lemma Fx_82e6c : fetch_word Asan.M.loaded_segments (0x82ebc : word) = Some Wx_82e6c.
Proof. vm_refl. Qed.
Lemma Dx_82e6c : decode_any Wx_82e6c = Some (Jal 1 2093912, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e70 : bv 32 := 0x01250023.
Lemma Fx_82e70 : fetch_word Asan.M.loaded_segments (0x82ec0 : word) = Some Wx_82e70.
Proof. vm_refl. Qed.
Lemma Dx_82e70 : decode_any Wx_82e70 = Some (Store SZ1 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e74 : bv 32 := 0x06010113.
Lemma Fx_82e74 : fetch_word Asan.M.loaded_segments (0x82ec4 : word) = Some Wx_82e74.
Proof. vm_refl. Qed.
Lemma Dx_82e74 : decode_any Wx_82e74 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e78 : bv 32 := 0x7e813083.
Lemma Fx_82e78 : fetch_word Asan.M.loaded_segments (0x82ec8 : word) = Some Wx_82e78.
Proof. vm_refl. Qed.
Lemma Dx_82e78 : decode_any Wx_82e78 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e7c : bv 32 := 0x7e013403.
Lemma Fx_82e7c : fetch_word Asan.M.loaded_segments (0x82ecc : word) = Some Wx_82e7c.
Proof. vm_refl. Qed.
Lemma Dx_82e7c : decode_any Wx_82e7c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e80 : bv 32 := 0x7d813483.
Lemma Fx_82e80 : fetch_word Asan.M.loaded_segments (0x82ed0 : word) = Some Wx_82e80.
Proof. vm_refl. Qed.
Lemma Dx_82e80 : decode_any Wx_82e80 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e84 : bv 32 := 0x7d013903.
Lemma Fx_82e84 : fetch_word Asan.M.loaded_segments (0x82ed4 : word) = Some Wx_82e84.
Proof. vm_refl. Qed.
Lemma Dx_82e84 : decode_any Wx_82e84 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e88 : bv 32 := 0x7c813983.
Lemma Fx_82e88 : fetch_word Asan.M.loaded_segments (0x82ed8 : word) = Some Wx_82e88.
Proof. vm_refl. Qed.
Lemma Dx_82e88 : decode_any Wx_82e88 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e8c : bv 32 := 0x7c013a03.
Lemma Fx_82e8c : fetch_word Asan.M.loaded_segments (0x82edc : word) = Some Wx_82e8c.
Proof. vm_refl. Qed.
Lemma Dx_82e8c : decode_any Wx_82e8c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e90 : bv 32 := 0x7b813a83.
Lemma Fx_82e90 : fetch_word Asan.M.loaded_segments (0x82ee0 : word) = Some Wx_82e90.
Proof. vm_refl. Qed.
Lemma Dx_82e90 : decode_any Wx_82e90 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e94 : bv 32 := 0x7f010113.
Lemma Fx_82e94 : fetch_word Asan.M.loaded_segments (0x82ee4 : word) = Some Wx_82e94.
Proof. vm_refl. Qed.
Lemma Dx_82e94 : decode_any Wx_82e94 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e98 : bv 32 := 0x00008067.
Lemma Fx_82e98 : fetch_word Asan.M.loaded_segments (0x82ee8 : word) = Some Wx_82e98.
Proof. vm_refl. Qed.
Lemma Dx_82e98 : decode_any Wx_82e98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82e9c : bv 32 := 0xfff9f517.
Lemma Fx_82e9c : fetch_word Asan.M.loaded_segments (0x82eec : word) = Some Wx_82e9c.
Proof. vm_refl. Qed.
Lemma Dx_82e9c : decode_any Wx_82e9c = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ea0 : bv 32 := 0xfff96617.
Lemma Fx_82ea0 : fetch_word Asan.M.loaded_segments (0x82ef0 : word) = Some Wx_82ea0.
Proof. vm_refl. Qed.
Lemma Dx_82ea0 : decode_any Wx_82ea0 = Some (Auipc 12 1048470, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ea4 : bv 32 := 0x1dc00593.
Lemma Fx_82ea4 : fetch_word Asan.M.loaded_segments (0x82ef4 : word) = Some Wx_82ea4.
Proof. vm_refl. Qed.
Lemma Dx_82ea4 : decode_any Wx_82ea4 = Some (OpImm ALU_ADD 11 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ea8 : bv 32 := 0xdcf50513.
Lemma Fx_82ea8 : fetch_word Asan.M.loaded_segments (0x82ef8 : word) = Some Wx_82ea8.
Proof. vm_refl. Qed.
Lemma Dx_82ea8 : decode_any Wx_82ea8 = Some (OpImm ALU_ADD 10 10 3535, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82eac : bv 32 := 0xd7460613.
Lemma Fx_82eac : fetch_word Asan.M.loaded_segments (0x82efc : word) = Some Wx_82eac.
Proof. vm_refl. Qed.
Lemma Dx_82eac : decode_any Wx_82eac = Some (OpImm ALU_ADD 12 12 3444, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82eb0 : bv 32 := 0x00800713.
Lemma Fx_82eb0 : fetch_word Asan.M.loaded_segments (0x82f00 : word) = Some Wx_82eb0.
Proof. vm_refl. Qed.
Lemma Dx_82eb0 : decode_any Wx_82eb0 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82eb4 : bv 32 := 0x460170ef.
Lemma Fx_82eb4 : fetch_word Asan.M.loaded_segments (0x82f04 : word) = Some Wx_82eb4.
Proof. vm_refl. Qed.
Lemma Dx_82eb4 : decode_any Wx_82eb4 = Some (Jal 1 95328, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82eb8 : bv 32 := 0x000a8a13.
Lemma Fx_82eb8 : fetch_word Asan.M.loaded_segments (0x82f08 : word) = Some Wx_82eb8.
Proof. vm_refl. Qed.
Lemma Dx_82eb8 : decode_any Wx_82eb8 = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ebc : bv 32 := 0xf13aece3.
Lemma Fx_82ebc : fetch_word Asan.M.loaded_segments (0x82f0c : word) = Some Wx_82ebc.
Proof. vm_refl. Qed.
Lemma Dx_82ebc : decode_any Wx_82ebc = Some (Branch BC_LTU 21 19 7960, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ec0 : bv 32 := 0x00098a13.
Lemma Fx_82ec0 : fetch_word Asan.M.loaded_segments (0x82f10 : word) = Some Wx_82ec0.
Proof. vm_refl. Qed.
Lemma Dx_82ec0 : decode_any Wx_82ec0 = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ec4 : bv 32 := 0xe72aece3.
Lemma Fx_82ec4 : fetch_word Asan.M.loaded_segments (0x82f14 : word) = Some Wx_82ec4.
Proof. vm_refl. Qed.
Lemma Dx_82ec4 : decode_any Wx_82ec4 = Some (Branch BC_LTU 21 18 7800, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ec8 : bv 32 := 0x00090a93.
Lemma Fx_82ec8 : fetch_word Asan.M.loaded_segments (0x82f18 : word) = Some Wx_82ec8.
Proof. vm_refl. Qed.
Lemma Dx_82ec8 : decode_any Wx_82ec8 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_82ecc : bv 32 := 0xe71ff06f.
Lemma Fx_82ecc : fetch_word Asan.M.loaded_segments (0x82f1c : word) = Some Wx_82ecc.
Proof. vm_refl. Qed.
Lemma Dx_82ecc : decode_any Wx_82ecc = Some (Jal 0 2096752, 4%Z).
Proof. vm_refl. Qed.

