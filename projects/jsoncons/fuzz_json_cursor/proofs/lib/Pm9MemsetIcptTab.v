(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition Wx_7f1e0 : bv 32 := 0x2590006f.
Lemma Fx_7f1e0 : fetch_word AsanUbsan.M.loaded_segments (0x7f228 : word) = Some Wx_7f1e0.
Proof. vm_refl. Qed.
Lemma Dx_7f1e0 : decode_any Wx_7f1e0 = Some (Jal 0 2648, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc38 : bv 32 := 0x81010113.
Lemma Fx_7fc38 : fetch_word AsanUbsan.M.loaded_segments (0x7fc80 : word) = Some Wx_7fc38.
Proof. vm_refl. Qed.
Lemma Dx_7fc38 : decode_any Wx_7fc38 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc3c : bv 32 := 0x7e113423.
Lemma Fx_7fc3c : fetch_word AsanUbsan.M.loaded_segments (0x7fc84 : word) = Some Wx_7fc3c.
Proof. vm_refl. Qed.
Lemma Dx_7fc3c : decode_any Wx_7fc3c = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc40 : bv 32 := 0x7e813023.
Lemma Fx_7fc40 : fetch_word AsanUbsan.M.loaded_segments (0x7fc88 : word) = Some Wx_7fc40.
Proof. vm_refl. Qed.
Lemma Dx_7fc40 : decode_any Wx_7fc40 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc44 : bv 32 := 0x7c913c23.
Lemma Fx_7fc44 : fetch_word AsanUbsan.M.loaded_segments (0x7fc8c : word) = Some Wx_7fc44.
Proof. vm_refl. Qed.
Lemma Dx_7fc44 : decode_any Wx_7fc44 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc48 : bv 32 := 0x7d213823.
Lemma Fx_7fc48 : fetch_word AsanUbsan.M.loaded_segments (0x7fc90 : word) = Some Wx_7fc48.
Proof. vm_refl. Qed.
Lemma Dx_7fc48 : decode_any Wx_7fc48 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc4c : bv 32 := 0x7d313423.
Lemma Fx_7fc4c : fetch_word AsanUbsan.M.loaded_segments (0x7fc94 : word) = Some Wx_7fc4c.
Proof. vm_refl. Qed.
Lemma Dx_7fc4c : decode_any Wx_7fc4c = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc50 : bv 32 := 0x7d413023.
Lemma Fx_7fc50 : fetch_word AsanUbsan.M.loaded_segments (0x7fc98 : word) = Some Wx_7fc50.
Proof. vm_refl. Qed.
Lemma Dx_7fc50 : decode_any Wx_7fc50 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc54 : bv 32 := 0x7b513c23.
Lemma Fx_7fc54 : fetch_word AsanUbsan.M.loaded_segments (0x7fc9c : word) = Some Wx_7fc54.
Proof. vm_refl. Qed.
Lemma Dx_7fc54 : decode_any Wx_7fc54 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc58 : bv 32 := 0x7b613823.
Lemma Fx_7fc58 : fetch_word AsanUbsan.M.loaded_segments (0x7fca0 : word) = Some Wx_7fc58.
Proof. vm_refl. Qed.
Lemma Dx_7fc58 : decode_any Wx_7fc58 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc5c : bv 32 := 0x7f010413.
Lemma Fx_7fc5c : fetch_word AsanUbsan.M.loaded_segments (0x7fca4 : word) = Some Wx_7fc5c.
Proof. vm_refl. Qed.
Lemma Dx_7fc5c : decode_any Wx_7fc5c = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc60 : bv 32 := 0xf9010113.
Lemma Fx_7fc60 : fetch_word AsanUbsan.M.loaded_segments (0x7fca8 : word) = Some Wx_7fc60.
Proof. vm_refl. Qed.
Lemma Dx_7fc60 : decode_any Wx_7fc60 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc64 : bv 32 := 0x000d5697.
Lemma Fx_7fc64 : fetch_word AsanUbsan.M.loaded_segments (0x7fcac : word) = Some Wx_7fc64.
Proof. vm_refl. Qed.
Lemma Dx_7fc64 : decode_any Wx_7fc64 = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc68 : bv 32 := 0x3bc6b683.
Lemma Fx_7fc68 : fetch_word AsanUbsan.M.loaded_segments (0x7fcb0 : word) = Some Wx_7fc68.
Proof. vm_refl. Qed.
Lemma Dx_7fc68 : decode_any Wx_7fc68 = Some (Load SZ8 true 13 13 956, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc6c : bv 32 := 0x0006c683.
Lemma Fx_7fc6c : fetch_word AsanUbsan.M.loaded_segments (0x7fcb4 : word) = Some Wx_7fc6c.
Proof. vm_refl. Qed.
Lemma Dx_7fc6c : decode_any Wx_7fc6c = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc70 : bv 32 := 0x08068a63.
Lemma Fx_7fc70 : fetch_word AsanUbsan.M.loaded_segments (0x7fcb8 : word) = Some Wx_7fc70.
Proof. vm_refl. Qed.
Lemma Dx_7fc70 : decode_any Wx_7fc70 = Some (Branch BC_EQ 13 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc74 : bv 32 := 0xfff54693.
Lemma Fx_7fc74 : fetch_word AsanUbsan.M.loaded_segments (0x7fcbc : word) = Some Wx_7fc74.
Proof. vm_refl. Qed.
Lemma Dx_7fc74 : decode_any Wx_7fc74 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc78 : bv 32 := 0x80040a93.
Lemma Fx_7fc78 : fetch_word AsanUbsan.M.loaded_segments (0x7fcc0 : word) = Some Wx_7fc78.
Proof. vm_refl. Qed.
Lemma Dx_7fc78 : decode_any Wx_7fc78 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc7c : bv 32 := 0xfa8a8a93.
Lemma Fx_7fc7c : fetch_word AsanUbsan.M.loaded_segments (0x7fcc4 : word) = Some Wx_7fc7c.
Proof. vm_refl. Qed.
Lemma Dx_7fc7c : decode_any Wx_7fc7c = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc80 : bv 32 := 0x0cc6ea63.
Lemma Fx_7fc80 : fetch_word AsanUbsan.M.loaded_segments (0x7fcc8 : word) = Some Wx_7fc80.
Proof. vm_refl. Qed.
Lemma Dx_7fc80 : decode_any Wx_7fc80 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc84 : bv 32 := 0xfbf60693.
Lemma Fx_7fc84 : fetch_word AsanUbsan.M.loaded_segments (0x7fccc : word) = Some Wx_7fc84.
Proof. vm_refl. Qed.
Lemma Dx_7fc84 : decode_any Wx_7fc84 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc88 : bv 32 := 0xfbf00713.
Lemma Fx_7fc88 : fetch_word AsanUbsan.M.loaded_segments (0x7fcd0 : word) = Some Wx_7fc88.
Proof. vm_refl. Qed.
Lemma Dx_7fc88 : decode_any Wx_7fc88 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc8c : bv 32 := 0x14d77863.
Lemma Fx_7fc8c : fetch_word AsanUbsan.M.loaded_segments (0x7fcd4 : word) = Some Wx_7fc8c.
Proof. vm_refl. Qed.
Lemma Dx_7fc8c : decode_any Wx_7fc8c = Some (Branch BC_GEU 14 13 336, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc90 : bv 32 := 0x000d5697.
Lemma Fx_7fc90 : fetch_word AsanUbsan.M.loaded_segments (0x7fcd8 : word) = Some Wx_7fc90.
Proof. vm_refl. Qed.
Lemma Dx_7fc90 : decode_any Wx_7fc90 = Some (Auipc 13 213, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc94 : bv 32 := 0x8286b683.
Lemma Fx_7fc94 : fetch_word AsanUbsan.M.loaded_segments (0x7fcdc : word) = Some Wx_7fc94.
Proof. vm_refl. Qed.
Lemma Dx_7fc94 : decode_any Wx_7fc94 = Some (Load SZ8 true 13 13 2088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc98 : bv 32 := 0x00c507b3.
Lemma Fx_7fc98 : fetch_word AsanUbsan.M.loaded_segments (0x7fce0 : word) = Some Wx_7fc98.
Proof. vm_refl. Qed.
Lemma Dx_7fc98 : decode_any Wx_7fc98 = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fc9c : bv 32 := 0x0006b703.
Lemma Fx_7fc9c : fetch_word AsanUbsan.M.loaded_segments (0x7fce4 : word) = Some Wx_7fc9c.
Proof. vm_refl. Qed.
Lemma Dx_7fc9c : decode_any Wx_7fc9c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fca0 : bv 32 := 0x00355693.
Lemma Fx_7fca0 : fetch_word AsanUbsan.M.loaded_segments (0x7fce8 : word) = Some Wx_7fca0.
Proof. vm_refl. Qed.
Lemma Dx_7fca0 : decode_any Wx_7fca0 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fca4 : bv 32 := 0xfff78793.
Lemma Fx_7fca4 : fetch_word AsanUbsan.M.loaded_segments (0x7fcec : word) = Some Wx_7fca4.
Proof. vm_refl. Qed.
Lemma Dx_7fca4 : decode_any Wx_7fca4 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fca8 : bv 32 := 0x0037d813.
Lemma Fx_7fca8 : fetch_word AsanUbsan.M.loaded_segments (0x7fcf0 : word) = Some Wx_7fca8.
Proof. vm_refl. Qed.
Lemma Dx_7fca8 : decode_any Wx_7fca8 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcac : bv 32 := 0x00d706b3.
Lemma Fx_7fcac : fetch_word AsanUbsan.M.loaded_segments (0x7fcf4 : word) = Some Wx_7fcac.
Proof. vm_refl. Qed.
Lemma Dx_7fcac : decode_any Wx_7fcac = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcb0 : bv 32 := 0x01070733.
Lemma Fx_7fcb0 : fetch_word AsanUbsan.M.loaded_segments (0x7fcf8 : word) = Some Wx_7fcb0.
Proof. vm_refl. Qed.
Lemma Dx_7fcb0 : decode_any Wx_7fcb0 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcb4 : bv 32 := 0xff86f813.
Lemma Fx_7fcb4 : fetch_word AsanUbsan.M.loaded_segments (0x7fcfc : word) = Some Wx_7fcb4.
Proof. vm_refl. Qed.
Lemma Dx_7fcb4 : decode_any Wx_7fcb4 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcb8 : bv 32 := 0xff877893.
Lemma Fx_7fcb8 : fetch_word AsanUbsan.M.loaded_segments (0x7fd00 : word) = Some Wx_7fcb8.
Proof. vm_refl. Qed.
Lemma Dx_7fcb8 : decode_any Wx_7fcb8 = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcbc : bv 32 := 0x00083803.
Lemma Fx_7fcbc : fetch_word AsanUbsan.M.loaded_segments (0x7fd04 : word) = Some Wx_7fcbc.
Proof. vm_refl. Qed.
Lemma Dx_7fcbc : decode_any Wx_7fcbc = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcc0 : bv 32 := 0x0008b883.
Lemma Fx_7fcc0 : fetch_word AsanUbsan.M.loaded_segments (0x7fd08 : word) = Some Wx_7fcc0.
Proof. vm_refl. Qed.
Lemma Dx_7fcc0 : decode_any Wx_7fcc0 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcc4 : bv 32 := 0x0108e833.
Lemma Fx_7fcc4 : fetch_word AsanUbsan.M.loaded_segments (0x7fd0c : word) = Some Wx_7fcc4.
Proof. vm_refl. Qed.
Lemma Dx_7fcc4 : decode_any Wx_7fcc4 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcc8 : bv 32 := 0x10081e63.
Lemma Fx_7fcc8 : fetch_word AsanUbsan.M.loaded_segments (0x7fd10 : word) = Some Wx_7fcc8.
Proof. vm_refl. Qed.
Lemma Dx_7fcc8 : decode_any Wx_7fcc8 = Some (Branch BC_NE 16 0 284, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fccc : bv 32 := 0x000d7697.
Lemma Fx_7fccc : fetch_word AsanUbsan.M.loaded_segments (0x7fd14 : word) = Some Wx_7fccc.
Proof. vm_refl. Qed.
Lemma Dx_7fccc : decode_any Wx_7fccc = Some (Auipc 13 215, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcd0 : bv 32 := 0x8146b683.
Lemma Fx_7fcd0 : fetch_word AsanUbsan.M.loaded_segments (0x7fd18 : word) = Some Wx_7fcd0.
Proof. vm_refl. Qed.
Lemma Dx_7fcd0 : decode_any Wx_7fcd0 = Some (Load SZ8 true 13 13 2068, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcd4 : bv 32 := 0x000680e7.
Lemma Fx_7fcd4 : fetch_word AsanUbsan.M.loaded_segments (0x7fd1c : word) = Some Wx_7fcd4.
Proof. vm_refl. Qed.
Lemma Dx_7fcd4 : decode_any Wx_7fcd4 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcd8 : bv 32 := 0x07010113.
Lemma Fx_7fcd8 : fetch_word AsanUbsan.M.loaded_segments (0x7fd20 : word) = Some Wx_7fcd8.
Proof. vm_refl. Qed.
Lemma Dx_7fcd8 : decode_any Wx_7fcd8 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcdc : bv 32 := 0x7e813083.
Lemma Fx_7fcdc : fetch_word AsanUbsan.M.loaded_segments (0x7fd24 : word) = Some Wx_7fcdc.
Proof. vm_refl. Qed.
Lemma Dx_7fcdc : decode_any Wx_7fcdc = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fce0 : bv 32 := 0x7e013403.
Lemma Fx_7fce0 : fetch_word AsanUbsan.M.loaded_segments (0x7fd28 : word) = Some Wx_7fce0.
Proof. vm_refl. Qed.
Lemma Dx_7fce0 : decode_any Wx_7fce0 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fce4 : bv 32 := 0x7d813483.
Lemma Fx_7fce4 : fetch_word AsanUbsan.M.loaded_segments (0x7fd2c : word) = Some Wx_7fce4.
Proof. vm_refl. Qed.
Lemma Dx_7fce4 : decode_any Wx_7fce4 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fce8 : bv 32 := 0x7d013903.
Lemma Fx_7fce8 : fetch_word AsanUbsan.M.loaded_segments (0x7fd30 : word) = Some Wx_7fce8.
Proof. vm_refl. Qed.
Lemma Dx_7fce8 : decode_any Wx_7fce8 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcec : bv 32 := 0x7c813983.
Lemma Fx_7fcec : fetch_word AsanUbsan.M.loaded_segments (0x7fd34 : word) = Some Wx_7fcec.
Proof. vm_refl. Qed.
Lemma Dx_7fcec : decode_any Wx_7fcec = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcf0 : bv 32 := 0x7c013a03.
Lemma Fx_7fcf0 : fetch_word AsanUbsan.M.loaded_segments (0x7fd38 : word) = Some Wx_7fcf0.
Proof. vm_refl. Qed.
Lemma Dx_7fcf0 : decode_any Wx_7fcf0 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcf4 : bv 32 := 0x7b813a83.
Lemma Fx_7fcf4 : fetch_word AsanUbsan.M.loaded_segments (0x7fd3c : word) = Some Wx_7fcf4.
Proof. vm_refl. Qed.
Lemma Dx_7fcf4 : decode_any Wx_7fcf4 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcf8 : bv 32 := 0x7b013b03.
Lemma Fx_7fcf8 : fetch_word AsanUbsan.M.loaded_segments (0x7fd40 : word) = Some Wx_7fcf8.
Proof. vm_refl. Qed.
Lemma Dx_7fcf8 : decode_any Wx_7fcf8 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fcfc : bv 32 := 0x7f010113.
Lemma Fx_7fcfc : fetch_word AsanUbsan.M.loaded_segments (0x7fd44 : word) = Some Wx_7fcfc.
Proof. vm_refl. Qed.
Lemma Dx_7fcfc : decode_any Wx_7fcfc = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fd00 : bv 32 := 0x00008067.
Lemma Fx_7fd00 : fetch_word AsanUbsan.M.loaded_segments (0x7fd48 : word) = Some Wx_7fd00.
Proof. vm_refl. Qed.
Lemma Dx_7fd00 : decode_any Wx_7fd00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fddc : bv 32 := 0x02061e63.
Lemma Fx_7fddc : fetch_word AsanUbsan.M.loaded_segments (0x7fe24 : word) = Some Wx_7fddc.
Proof. vm_refl. Qed.
Lemma Dx_7fddc : decode_any Wx_7fddc = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fde0 : bv 32 := 0xeedff06f.
Lemma Fx_7fde0 : fetch_word AsanUbsan.M.loaded_segments (0x7fe28 : word) = Some Wx_7fde0.
Proof. vm_refl. Qed.
Lemma Dx_7fde0 : decode_any Wx_7fde0 = Some (Jal 0 2096876, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fde4 : bv 32 := 0x00070803.
Lemma Fx_7fde4 : fetch_word AsanUbsan.M.loaded_segments (0x7fe2c : word) = Some Wx_7fde4.
Proof. vm_refl. Qed.
Lemma Dx_7fde4 : decode_any Wx_7fde4 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fde8 : bv 32 := 0x0077f793.
Lemma Fx_7fde8 : fetch_word AsanUbsan.M.loaded_segments (0x7fe30 : word) = Some Wx_7fde8.
Proof. vm_refl. Qed.
Lemma Dx_7fde8 : decode_any Wx_7fde8 = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fdec : bv 32 := 0x010038b3.
Lemma Fx_7fdec : fetch_word AsanUbsan.M.loaded_segments (0x7fe34 : word) = Some Wx_7fdec.
Proof. vm_refl. Qed.
Lemma Dx_7fdec : decode_any Wx_7fdec = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fdf0 : bv 32 := 0x0107a7b3.
Lemma Fx_7fdf0 : fetch_word AsanUbsan.M.loaded_segments (0x7fe38 : word) = Some Wx_7fdf0.
Proof. vm_refl. Qed.
Lemma Dx_7fdf0 : decode_any Wx_7fdf0 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fdf4 : bv 32 := 0x0017c793.
Lemma Fx_7fdf4 : fetch_word AsanUbsan.M.loaded_segments (0x7fe3c : word) = Some Wx_7fdf4.
Proof. vm_refl. Qed.
Lemma Dx_7fdf4 : decode_any Wx_7fdf4 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fdf8 : bv 32 := 0x00f8f7b3.
Lemma Fx_7fdf8 : fetch_word AsanUbsan.M.loaded_segments (0x7fe40 : word) = Some Wx_7fdf8.
Proof. vm_refl. Qed.
Lemma Dx_7fdf8 : decode_any Wx_7fdf8 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fdfc : bv 32 := 0x00e6fa63.
Lemma Fx_7fdfc : fetch_word AsanUbsan.M.loaded_segments (0x7fe44 : word) = Some Wx_7fdfc.
Proof. vm_refl. Qed.
Lemma Dx_7fdfc : decode_any Wx_7fdfc = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe00 : bv 32 := 0x0006c803.
Lemma Fx_7fe00 : fetch_word AsanUbsan.M.loaded_segments (0x7fe48 : word) = Some Wx_7fe00.
Proof. vm_refl. Qed.
Lemma Dx_7fe00 : decode_any Wx_7fe00 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe04 : bv 32 := 0x00168693.
Lemma Fx_7fe04 : fetch_word AsanUbsan.M.loaded_segments (0x7fe4c : word) = Some Wx_7fe04.
Proof. vm_refl. Qed.
Lemma Dx_7fe04 : decode_any Wx_7fe04 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe08 : bv 32 := 0x00f867b3.
Lemma Fx_7fe08 : fetch_word AsanUbsan.M.loaded_segments (0x7fe50 : word) = Some Wx_7fe08.
Proof. vm_refl. Qed.
Lemma Dx_7fe08 : decode_any Wx_7fe08 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe0c : bv 32 := 0xfee69ae3.
Lemma Fx_7fe0c : fetch_word AsanUbsan.M.loaded_segments (0x7fe54 : word) = Some Wx_7fe0c.
Proof. vm_refl. Qed.
Lemma Dx_7fe0c : decode_any Wx_7fe0c = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe10 : bv 32 := 0x0ff7f693.
Lemma Fx_7fe10 : fetch_word AsanUbsan.M.loaded_segments (0x7fe58 : word) = Some Wx_7fe10.
Proof. vm_refl. Qed.
Lemma Dx_7fe10 : decode_any Wx_7fe10 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe14 : bv 32 := 0xea068ce3.
Lemma Fx_7fe14 : fetch_word AsanUbsan.M.loaded_segments (0x7fe5c : word) = Some Wx_7fe14.
Proof. vm_refl. Qed.
Lemma Dx_7fe14 : decode_any Wx_7fe14 = Some (Branch BC_EQ 13 0 7864, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe18 : bv 32 := 0x00050493.
Lemma Fx_7fe18 : fetch_word AsanUbsan.M.loaded_segments (0x7fe60 : word) = Some Wx_7fe18.
Proof. vm_refl. Qed.
Lemma Dx_7fe18 : decode_any Wx_7fe18 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe1c : bv 32 := 0x00058b13.
Lemma Fx_7fe1c : fetch_word AsanUbsan.M.loaded_segments (0x7fe64 : word) = Some Wx_7fe1c.
Proof. vm_refl. Qed.
Lemma Dx_7fe1c : decode_any Wx_7fe1c = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe20 : bv 32 := 0x00060593.
Lemma Fx_7fe20 : fetch_word AsanUbsan.M.loaded_segments (0x7fe68 : word) = Some Wx_7fe20.
Proof. vm_refl. Qed.
Lemma Dx_7fe20 : decode_any Wx_7fe20 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe24 : bv 32 := 0x00060913.
Lemma Fx_7fe24 : fetch_word AsanUbsan.M.loaded_segments (0x7fe6c : word) = Some Wx_7fe24.
Proof. vm_refl. Qed.
Lemma Dx_7fe24 : decode_any Wx_7fe24 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe28 : bv 32 := 0x3f1020ef.
Lemma Fx_7fe28 : fetch_word AsanUbsan.M.loaded_segments (0x7fe70 : word) = Some Wx_7fe28.
Proof. vm_refl. Qed.
Lemma Dx_7fe28 : decode_any Wx_7fe28 = Some (Jal 1 11248, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe2c : bv 32 := 0x000b0593.
Lemma Fx_7fe2c : fetch_word AsanUbsan.M.loaded_segments (0x7fe74 : word) = Some Wx_7fe2c.
Proof. vm_refl. Qed.
Lemma Dx_7fe2c : decode_any Wx_7fe2c = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe30 : bv 32 := 0x00090613.
Lemma Fx_7fe30 : fetch_word AsanUbsan.M.loaded_segments (0x7fe78 : word) = Some Wx_7fe30.
Proof. vm_refl. Qed.
Lemma Dx_7fe30 : decode_any Wx_7fe30 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe34 : bv 32 := 0x00050993.
Lemma Fx_7fe34 : fetch_word AsanUbsan.M.loaded_segments (0x7fe7c : word) = Some Wx_7fe34.
Proof. vm_refl. Qed.
Lemma Dx_7fe34 : decode_any Wx_7fe34 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe38 : bv 32 := 0x00048513.
Lemma Fx_7fe38 : fetch_word AsanUbsan.M.loaded_segments (0x7fe80 : word) = Some Wx_7fe38.
Proof. vm_refl. Qed.
Lemma Dx_7fe38 : decode_any Wx_7fe38 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition Wx_7fe3c : bv 32 := 0xe80988e3.
Lemma Fx_7fe3c : fetch_word AsanUbsan.M.loaded_segments (0x7fe84 : word) = Some Wx_7fe3c.
Proof. vm_refl. Qed.
Lemma Dx_7fe3c : decode_any Wx_7fe3c = Some (Branch BC_EQ 19 0 7824, 4%Z).
Proof. vm_refl. Qed.

