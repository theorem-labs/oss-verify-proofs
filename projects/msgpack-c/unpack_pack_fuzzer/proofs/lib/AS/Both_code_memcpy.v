(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_c95c0 : bv 32 := 0x0035f693.
Lemma F_c95c0 : fetch_word AsanUbsan.M.loaded_segments (0xc95bc : word) = Some W_c95c0.
Proof. vm_refl. Qed.
Lemma D_c95c0 : decode_any W_c95c0 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95c4 : bv 32 := 0x10068863.
Lemma F_c95c4 : fetch_word AsanUbsan.M.loaded_segments (0xc95c0 : word) = Some W_c95c4.
Proof. vm_refl. Qed.
Lemma D_c95c4 : decode_any W_c95c4 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95c8 : bv 32 := 0x02060e63.
Lemma F_c95c8 : fetch_word AsanUbsan.M.loaded_segments (0xc95c4 : word) = Some W_c95c8.
Proof. vm_refl. Qed.
Lemma D_c95c8 : decode_any W_c95c8 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95cc : bv 32 := 0x00158713.
Lemma F_c95cc : fetch_word AsanUbsan.M.loaded_segments (0xc95c8 : word) = Some W_c95cc.
Proof. vm_refl. Qed.
Lemma D_c95cc : decode_any W_c95cc = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95d0 : bv 32 := 0x00100793.
Lemma F_c95d0 : fetch_word AsanUbsan.M.loaded_segments (0xc95cc : word) = Some W_c95d0.
Proof. vm_refl. Qed.
Lemma D_c95d0 : decode_any W_c95d0 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95d4 : bv 32 := 0x00050693.
Lemma F_c95d4 : fetch_word AsanUbsan.M.loaded_segments (0xc95d0 : word) = Some W_c95d4.
Proof. vm_refl. Qed.
Lemma D_c95d4 : decode_any W_c95d4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95d8 : bv 32 := 0x0005c883.
Lemma F_c95d8 : fetch_word AsanUbsan.M.loaded_segments (0xc95d4 : word) = Some W_c95d8.
Proof. vm_refl. Qed.
Lemma D_c95d8 : decode_any W_c95d8 = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95dc : bv 32 := 0x00060813.
Lemma F_c95dc : fetch_word AsanUbsan.M.loaded_segments (0xc95d8 : word) = Some W_c95dc.
Proof. vm_refl. Qed.
Lemma D_c95dc : decode_any W_c95dc = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95e0 : bv 32 := 0x00158593.
Lemma F_c95e0 : fetch_word AsanUbsan.M.loaded_segments (0xc95dc : word) = Some W_c95e0.
Proof. vm_refl. Qed.
Lemma D_c95e0 : decode_any W_c95e0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95e4 : bv 32 := 0x00377293.
Lemma F_c95e4 : fetch_word AsanUbsan.M.loaded_segments (0xc95e0 : word) = Some W_c95e4.
Proof. vm_refl. Qed.
Lemma D_c95e4 : decode_any W_c95e4 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95e8 : bv 32 := 0x01168023.
Lemma F_c95e8 : fetch_word AsanUbsan.M.loaded_segments (0xc95e4 : word) = Some W_c95e8.
Proof. vm_refl. Qed.
Lemma D_c95e8 : decode_any W_c95e8 = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95ec : bv 32 := 0x00168693.
Lemma F_c95ec : fetch_word AsanUbsan.M.loaded_segments (0xc95e8 : word) = Some W_c95ec.
Proof. vm_refl. Qed.
Lemma D_c95ec : decode_any W_c95ec = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95f0 : bv 32 := 0xfff60613.
Lemma F_c95f0 : fetch_word AsanUbsan.M.loaded_segments (0xc95ec : word) = Some W_c95f0.
Proof. vm_refl. Qed.
Lemma D_c95f0 : decode_any W_c95f0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95f4 : bv 32 := 0x00028a63.
Lemma F_c95f4 : fetch_word AsanUbsan.M.loaded_segments (0xc95f0 : word) = Some W_c95f4.
Proof. vm_refl. Qed.
Lemma D_c95f4 : decode_any W_c95f4 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95f8 : bv 32 := 0x00170713.
Lemma F_c95f8 : fetch_word AsanUbsan.M.loaded_segments (0xc95f4 : word) = Some W_c95f8.
Proof. vm_refl. Qed.
Lemma D_c95f8 : decode_any W_c95f8 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c95fc : bv 32 := 0xfcf81ee3.
Lemma F_c95fc : fetch_word AsanUbsan.M.loaded_segments (0xc95f8 : word) = Some W_c95fc.
Proof. vm_refl. Qed.
Lemma D_c95fc : decode_any W_c95fc = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9600 : bv 32 := 0x0080006f.
Lemma F_c9600 : fetch_word AsanUbsan.M.loaded_segments (0xc95fc : word) = Some W_c9600.
Proof. vm_refl. Qed.
Lemma D_c9600 : decode_any W_c9600 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9604 : bv 32 := 0x00050693.
Lemma F_c9604 : fetch_word AsanUbsan.M.loaded_segments (0xc9600 : word) = Some W_c9604.
Proof. vm_refl. Qed.
Lemma D_c9604 : decode_any W_c9604 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9608 : bv 32 := 0x0036f793.
Lemma F_c9608 : fetch_word AsanUbsan.M.loaded_segments (0xc9604 : word) = Some W_c9608.
Proof. vm_refl. Qed.
Lemma D_c9608 : decode_any W_c9608 = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c960c : bv 32 := 0x0c078a63.
Lemma F_c960c : fetch_word AsanUbsan.M.loaded_segments (0xc9608 : word) = Some W_c960c.
Proof. vm_refl. Qed.
Lemma D_c960c : decode_any W_c960c = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9610 : bv 32 := 0x02000713.
Lemma F_c9610 : fetch_word AsanUbsan.M.loaded_segments (0xc960c : word) = Some W_c9610.
Proof. vm_refl. Qed.
Lemma D_c9610 : decode_any W_c9610 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9614 : bv 32 := 0x02e67063.
Lemma F_c9614 : fetch_word AsanUbsan.M.loaded_segments (0xc9610 : word) = Some W_c9614.
Proof. vm_refl. Qed.
Lemma D_c9614 : decode_any W_c9614 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9618 : bv 32 := 0x01000713.
Lemma F_c9618 : fetch_word AsanUbsan.M.loaded_segments (0xc9614 : word) = Some W_c9618.
Proof. vm_refl. Qed.
Lemma D_c9618 : decode_any W_c9618 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c961c : bv 32 := 0x24e67863.
Lemma F_c961c : fetch_word AsanUbsan.M.loaded_segments (0xc9618 : word) = Some W_c961c.
Proof. vm_refl. Qed.
Lemma D_c961c : decode_any W_c961c = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9620 : bv 32 := 0x00867713.
Lemma F_c9620 : fetch_word AsanUbsan.M.loaded_segments (0xc961c : word) = Some W_c9620.
Proof. vm_refl. Qed.
Lemma D_c9620 : decode_any W_c9620 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9624 : bv 32 := 0x2c071e63.
Lemma F_c9624 : fetch_word AsanUbsan.M.loaded_segments (0xc9620 : word) = Some W_c9624.
Proof. vm_refl. Qed.
Lemma D_c9624 : decode_any W_c9624 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9628 : bv 32 := 0x00467713.
Lemma F_c9628 : fetch_word AsanUbsan.M.loaded_segments (0xc9624 : word) = Some W_c9628.
Proof. vm_refl. Qed.
Lemma D_c9628 : decode_any W_c9628 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c962c : bv 32 := 0x32071463.
Lemma F_c962c : fetch_word AsanUbsan.M.loaded_segments (0xc9628 : word) = Some W_c962c.
Proof. vm_refl. Qed.
Lemma D_c962c : decode_any W_c962c = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9630 : bv 32 := 0x3500006f.
Lemma F_c9630 : fetch_word AsanUbsan.M.loaded_segments (0xc962c : word) = Some W_c9630.
Proof. vm_refl. Qed.
Lemma D_c9630 : decode_any W_c9630 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9634 : bv 32 := 0x0005a703.
Lemma F_c9634 : fetch_word AsanUbsan.M.loaded_segments (0xc9630 : word) = Some W_c9634.
Proof. vm_refl. Qed.
Lemma D_c9634 : decode_any W_c9634 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9638 : bv 32 := 0x00300813.
Lemma F_c9638 : fetch_word AsanUbsan.M.loaded_segments (0xc9634 : word) = Some W_c9638.
Proof. vm_refl. Qed.
Lemma D_c9638 : decode_any W_c9638 = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c963c : bv 32 := 0x11078e63.
Lemma F_c963c : fetch_word AsanUbsan.M.loaded_segments (0xc9638 : word) = Some W_c963c.
Proof. vm_refl. Qed.
Lemma D_c963c : decode_any W_c963c = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9640 : bv 32 := 0x00200813.
Lemma F_c9640 : fetch_word AsanUbsan.M.loaded_segments (0xc963c : word) = Some W_c9640.
Proof. vm_refl. Qed.
Lemma D_c9640 : decode_any W_c9640 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9644 : bv 32 := 0x19079c63.
Lemma F_c9644 : fetch_word AsanUbsan.M.loaded_segments (0xc9640 : word) = Some W_c9644.
Proof. vm_refl. Qed.
Lemma D_c9644 : decode_any W_c9644 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9648 : bv 32 := 0x00875793.
Lemma F_c9648 : fetch_word AsanUbsan.M.loaded_segments (0xc9644 : word) = Some W_c9648.
Proof. vm_refl. Qed.
Lemma D_c9648 : decode_any W_c9648 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c964c : bv 32 := 0xffe60613.
Lemma F_c964c : fetch_word AsanUbsan.M.loaded_segments (0xc9648 : word) = Some W_c964c.
Proof. vm_refl. Qed.
Lemma D_c964c : decode_any W_c964c = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9650 : bv 32 := 0x00e68023.
Lemma F_c9650 : fetch_word AsanUbsan.M.loaded_segments (0xc964c : word) = Some W_c9650.
Proof. vm_refl. Qed.
Lemma D_c9650 : decode_any W_c9650 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9654 : bv 32 := 0x00f680a3.
Lemma F_c9654 : fetch_word AsanUbsan.M.loaded_segments (0xc9650 : word) = Some W_c9654.
Proof. vm_refl. Qed.
Lemma D_c9654 : decode_any W_c9654 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9658 : bv 32 := 0x00268693.
Lemma F_c9658 : fetch_word AsanUbsan.M.loaded_segments (0xc9654 : word) = Some W_c9658.
Proof. vm_refl. Qed.
Lemma D_c9658 : decode_any W_c9658 = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c965c : bv 32 := 0x01058593.
Lemma F_c965c : fetch_word AsanUbsan.M.loaded_segments (0xc9658 : word) = Some W_c965c.
Proof. vm_refl. Qed.
Lemma D_c965c : decode_any W_c965c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9660 : bv 32 := 0x01100793.
Lemma F_c9660 : fetch_word AsanUbsan.M.loaded_segments (0xc965c : word) = Some W_c9660.
Proof. vm_refl. Qed.
Lemma D_c9660 : decode_any W_c9660 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9664 : bv 32 := 0x0107581b.
Lemma F_c9664 : fetch_word AsanUbsan.M.loaded_segments (0xc9660 : word) = Some W_c9664.
Proof. vm_refl. Qed.
Lemma D_c9664 : decode_any W_c9664 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9668 : bv 32 := 0xff45a883.
Lemma F_c9668 : fetch_word AsanUbsan.M.loaded_segments (0xc9664 : word) = Some W_c9668.
Proof. vm_refl. Qed.
Lemma D_c9668 : decode_any W_c9668 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c966c : bv 32 := 0xff85a283.
Lemma F_c966c : fetch_word AsanUbsan.M.loaded_segments (0xc9668 : word) = Some W_c966c.
Proof. vm_refl. Qed.
Lemma D_c966c : decode_any W_c966c = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9670 : bv 32 := 0xffc5a303.
Lemma F_c9670 : fetch_word AsanUbsan.M.loaded_segments (0xc966c : word) = Some W_c9670.
Proof. vm_refl. Qed.
Lemma D_c9670 : decode_any W_c9670 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9674 : bv 32 := 0x0005a703.
Lemma F_c9674 : fetch_word AsanUbsan.M.loaded_segments (0xc9670 : word) = Some W_c9674.
Proof. vm_refl. Qed.
Lemma D_c9674 : decode_any W_c9674 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9678 : bv 32 := 0x01089393.
Lemma F_c9678 : fetch_word AsanUbsan.M.loaded_segments (0xc9674 : word) = Some W_c9678.
Proof. vm_refl. Qed.
Lemma D_c9678 : decode_any W_c9678 = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c967c : bv 32 := 0x0108d89b.
Lemma F_c967c : fetch_word AsanUbsan.M.loaded_segments (0xc9678 : word) = Some W_c967c.
Proof. vm_refl. Qed.
Lemma D_c967c : decode_any W_c967c = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9680 : bv 32 := 0x0103e833.
Lemma F_c9680 : fetch_word AsanUbsan.M.loaded_segments (0xc967c : word) = Some W_c9680.
Proof. vm_refl. Qed.
Lemma D_c9680 : decode_any W_c9680 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9684 : bv 32 := 0x01029393.
Lemma F_c9684 : fetch_word AsanUbsan.M.loaded_segments (0xc9680 : word) = Some W_c9684.
Proof. vm_refl. Qed.
Lemma D_c9684 : decode_any W_c9684 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9688 : bv 32 := 0x0102d29b.
Lemma F_c9688 : fetch_word AsanUbsan.M.loaded_segments (0xc9684 : word) = Some W_c9688.
Proof. vm_refl. Qed.
Lemma D_c9688 : decode_any W_c9688 = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c968c : bv 32 := 0x0113e8b3.
Lemma F_c968c : fetch_word AsanUbsan.M.loaded_segments (0xc9688 : word) = Some W_c968c.
Proof. vm_refl. Qed.
Lemma D_c968c : decode_any W_c968c = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9690 : bv 32 := 0x01031393.
Lemma F_c9690 : fetch_word AsanUbsan.M.loaded_segments (0xc968c : word) = Some W_c9690.
Proof. vm_refl. Qed.
Lemma D_c9690 : decode_any W_c9690 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9694 : bv 32 := 0x0103531b.
Lemma F_c9694 : fetch_word AsanUbsan.M.loaded_segments (0xc9690 : word) = Some W_c9694.
Proof. vm_refl. Qed.
Lemma D_c9694 : decode_any W_c9694 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9698 : bv 32 := 0x0053e2b3.
Lemma F_c9698 : fetch_word AsanUbsan.M.loaded_segments (0xc9694 : word) = Some W_c9698.
Proof. vm_refl. Qed.
Lemma D_c9698 : decode_any W_c9698 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c969c : bv 32 := 0x01071393.
Lemma F_c969c : fetch_word AsanUbsan.M.loaded_segments (0xc9698 : word) = Some W_c969c.
Proof. vm_refl. Qed.
Lemma D_c969c : decode_any W_c969c = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96a0 : bv 32 := 0x0063e333.
Lemma F_c96a0 : fetch_word AsanUbsan.M.loaded_segments (0xc969c : word) = Some W_c96a0.
Proof. vm_refl. Qed.
Lemma D_c96a0 : decode_any W_c96a0 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96a4 : bv 32 := 0xff060613.
Lemma F_c96a4 : fetch_word AsanUbsan.M.loaded_segments (0xc96a0 : word) = Some W_c96a4.
Proof. vm_refl. Qed.
Lemma D_c96a4 : decode_any W_c96a4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96a8 : bv 32 := 0x0106a023.
Lemma F_c96a8 : fetch_word AsanUbsan.M.loaded_segments (0xc96a4 : word) = Some W_c96a8.
Proof. vm_refl. Qed.
Lemma D_c96a8 : decode_any W_c96a8 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96ac : bv 32 := 0x0116a223.
Lemma F_c96ac : fetch_word AsanUbsan.M.loaded_segments (0xc96a8 : word) = Some W_c96ac.
Proof. vm_refl. Qed.
Lemma D_c96ac : decode_any W_c96ac = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96b0 : bv 32 := 0x0056a423.
Lemma F_c96b0 : fetch_word AsanUbsan.M.loaded_segments (0xc96ac : word) = Some W_c96b0.
Proof. vm_refl. Qed.
Lemma D_c96b0 : decode_any W_c96b0 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96b4 : bv 32 := 0x0066a623.
Lemma F_c96b4 : fetch_word AsanUbsan.M.loaded_segments (0xc96b0 : word) = Some W_c96b4.
Proof. vm_refl. Qed.
Lemma D_c96b4 : decode_any W_c96b4 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96b8 : bv 32 := 0x01068693.
Lemma F_c96b8 : fetch_word AsanUbsan.M.loaded_segments (0xc96b4 : word) = Some W_c96b8.
Proof. vm_refl. Qed.
Lemma D_c96b8 : decode_any W_c96b8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96bc : bv 32 := 0x01058593.
Lemma F_c96bc : fetch_word AsanUbsan.M.loaded_segments (0xc96b8 : word) = Some W_c96bc.
Proof. vm_refl. Qed.
Lemma D_c96bc : decode_any W_c96bc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96c0 : bv 32 := 0xfac7e2e3.
Lemma F_c96c0 : fetch_word AsanUbsan.M.loaded_segments (0xc96bc : word) = Some W_c96c0.
Proof. vm_refl. Qed.
Lemma D_c96c0 : decode_any W_c96c0 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96c4 : bv 32 := 0xff258593.
Lemma F_c96c4 : fetch_word AsanUbsan.M.loaded_segments (0xc96c0 : word) = Some W_c96c4.
Proof. vm_refl. Qed.
Lemma D_c96c4 : decode_any W_c96c4 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96c8 : bv 32 := 0x01000713.
Lemma F_c96c8 : fetch_word AsanUbsan.M.loaded_segments (0xc96c4 : word) = Some W_c96c8.
Proof. vm_refl. Qed.
Lemma D_c96c8 : decode_any W_c96c8 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96cc : bv 32 := 0xf4e66ae3.
Lemma F_c96cc : fetch_word AsanUbsan.M.loaded_segments (0xc96c8 : word) = Some W_c96cc.
Proof. vm_refl. Qed.
Lemma D_c96cc : decode_any W_c96cc = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96d0 : bv 32 := 0x19c0006f.
Lemma F_c96d0 : fetch_word AsanUbsan.M.loaded_segments (0xc96cc : word) = Some W_c96d0.
Proof. vm_refl. Qed.
Lemma D_c96d0 : decode_any W_c96d0 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96d4 : bv 32 := 0x00050693.
Lemma F_c96d4 : fetch_word AsanUbsan.M.loaded_segments (0xc96d0 : word) = Some W_c96d4.
Proof. vm_refl. Qed.
Lemma D_c96d4 : decode_any W_c96d4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96d8 : bv 32 := 0x00357793.
Lemma F_c96d8 : fetch_word AsanUbsan.M.loaded_segments (0xc96d4 : word) = Some W_c96d8.
Proof. vm_refl. Qed.
Lemma D_c96d8 : decode_any W_c96d8 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96dc : bv 32 := 0xf2079ae3.
Lemma F_c96dc : fetch_word AsanUbsan.M.loaded_segments (0xc96d8 : word) = Some W_c96dc.
Proof. vm_refl. Qed.
Lemma D_c96dc : decode_any W_c96dc = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96e0 : bv 32 := 0x01000713.
Lemma F_c96e0 : fetch_word AsanUbsan.M.loaded_segments (0xc96dc : word) = Some W_c96e0.
Proof. vm_refl. Qed.
Lemma D_c96e0 : decode_any W_c96e0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96e4 : bv 32 := 0x02e66c63.
Lemma F_c96e4 : fetch_word AsanUbsan.M.loaded_segments (0xc96e0 : word) = Some W_c96e4.
Proof. vm_refl. Qed.
Lemma D_c96e4 : decode_any W_c96e4 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96e8 : bv 32 := 0x00f00713.
Lemma F_c96e8 : fetch_word AsanUbsan.M.loaded_segments (0xc96e4 : word) = Some W_c96e8.
Proof. vm_refl. Qed.
Lemma D_c96e8 : decode_any W_c96e8 = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96ec : bv 32 := 0x0005a783.
Lemma F_c96ec : fetch_word AsanUbsan.M.loaded_segments (0xc96e8 : word) = Some W_c96ec.
Proof. vm_refl. Qed.
Lemma D_c96ec : decode_any W_c96ec = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96f0 : bv 32 := 0x0045a803.
Lemma F_c96f0 : fetch_word AsanUbsan.M.loaded_segments (0xc96ec : word) = Some W_c96f0.
Proof. vm_refl. Qed.
Lemma D_c96f0 : decode_any W_c96f0 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96f4 : bv 32 := 0x0085a883.
Lemma F_c96f4 : fetch_word AsanUbsan.M.loaded_segments (0xc96f0 : word) = Some W_c96f4.
Proof. vm_refl. Qed.
Lemma D_c96f4 : decode_any W_c96f4 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96f8 : bv 32 := 0x00c5a283.
Lemma F_c96f8 : fetch_word AsanUbsan.M.loaded_segments (0xc96f4 : word) = Some W_c96f8.
Proof. vm_refl. Qed.
Lemma D_c96f8 : decode_any W_c96f8 = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c96fc : bv 32 := 0x01058593.
Lemma F_c96fc : fetch_word AsanUbsan.M.loaded_segments (0xc96f8 : word) = Some W_c96fc.
Proof. vm_refl. Qed.
Lemma D_c96fc : decode_any W_c96fc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9700 : bv 32 := 0xff060613.
Lemma F_c9700 : fetch_word AsanUbsan.M.loaded_segments (0xc96fc : word) = Some W_c9700.
Proof. vm_refl. Qed.
Lemma D_c9700 : decode_any W_c9700 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9704 : bv 32 := 0x00f6a023.
Lemma F_c9704 : fetch_word AsanUbsan.M.loaded_segments (0xc9700 : word) = Some W_c9704.
Proof. vm_refl. Qed.
Lemma D_c9704 : decode_any W_c9704 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9708 : bv 32 := 0x0106a223.
Lemma F_c9708 : fetch_word AsanUbsan.M.loaded_segments (0xc9704 : word) = Some W_c9708.
Proof. vm_refl. Qed.
Lemma D_c9708 : decode_any W_c9708 = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c970c : bv 32 := 0x0116a423.
Lemma F_c970c : fetch_word AsanUbsan.M.loaded_segments (0xc9708 : word) = Some W_c970c.
Proof. vm_refl. Qed.
Lemma D_c970c : decode_any W_c970c = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9710 : bv 32 := 0x0056a623.
Lemma F_c9710 : fetch_word AsanUbsan.M.loaded_segments (0xc970c : word) = Some W_c9710.
Proof. vm_refl. Qed.
Lemma D_c9710 : decode_any W_c9710 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9714 : bv 32 := 0x01068693.
Lemma F_c9714 : fetch_word AsanUbsan.M.loaded_segments (0xc9710 : word) = Some W_c9714.
Proof. vm_refl. Qed.
Lemma D_c9714 : decode_any W_c9714 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9718 : bv 32 := 0xfcc76ae3.
Lemma F_c9718 : fetch_word AsanUbsan.M.loaded_segments (0xc9714 : word) = Some W_c9718.
Proof. vm_refl. Qed.
Lemma D_c9718 : decode_any W_c9718 = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_c971c : bv 32 := 0x00800713.
Lemma F_c971c : fetch_word AsanUbsan.M.loaded_segments (0xc9718 : word) = Some W_c971c.
Proof. vm_refl. Qed.
Lemma D_c971c : decode_any W_c971c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9720 : bv 32 := 0x00e66e63.
Lemma F_c9720 : fetch_word AsanUbsan.M.loaded_segments (0xc971c : word) = Some W_c9720.
Proof. vm_refl. Qed.
Lemma D_c9720 : decode_any W_c9720 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9724 : bv 32 := 0x0005a703.
Lemma F_c9724 : fetch_word AsanUbsan.M.loaded_segments (0xc9720 : word) = Some W_c9724.
Proof. vm_refl. Qed.
Lemma D_c9724 : decode_any W_c9724 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9728 : bv 32 := 0x0045a783.
Lemma F_c9728 : fetch_word AsanUbsan.M.loaded_segments (0xc9724 : word) = Some W_c9728.
Proof. vm_refl. Qed.
Lemma D_c9728 : decode_any W_c9728 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c972c : bv 32 := 0x00e6a023.
Lemma F_c972c : fetch_word AsanUbsan.M.loaded_segments (0xc9728 : word) = Some W_c972c.
Proof. vm_refl. Qed.
Lemma D_c972c : decode_any W_c972c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9730 : bv 32 := 0x00f6a223.
Lemma F_c9730 : fetch_word AsanUbsan.M.loaded_segments (0xc972c : word) = Some W_c9730.
Proof. vm_refl. Qed.
Lemma D_c9730 : decode_any W_c9730 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9734 : bv 32 := 0x00868693.
Lemma F_c9734 : fetch_word AsanUbsan.M.loaded_segments (0xc9730 : word) = Some W_c9734.
Proof. vm_refl. Qed.
Lemma D_c9734 : decode_any W_c9734 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9738 : bv 32 := 0x00858593.
Lemma F_c9738 : fetch_word AsanUbsan.M.loaded_segments (0xc9734 : word) = Some W_c9738.
Proof. vm_refl. Qed.
Lemma D_c9738 : decode_any W_c9738 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c973c : bv 32 := 0x00467713.
Lemma F_c973c : fetch_word AsanUbsan.M.loaded_segments (0xc9738 : word) = Some W_c973c.
Proof. vm_refl. Qed.
Lemma D_c973c : decode_any W_c973c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9740 : bv 32 := 0x24070063.
Lemma F_c9740 : fetch_word AsanUbsan.M.loaded_segments (0xc973c : word) = Some W_c9740.
Proof. vm_refl. Qed.
Lemma D_c9740 : decode_any W_c9740 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9744 : bv 32 := 0x0005a703.
Lemma F_c9744 : fetch_word AsanUbsan.M.loaded_segments (0xc9740 : word) = Some W_c9744.
Proof. vm_refl. Qed.
Lemma D_c9744 : decode_any W_c9744 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9748 : bv 32 := 0x00458593.
Lemma F_c9748 : fetch_word AsanUbsan.M.loaded_segments (0xc9744 : word) = Some W_c9748.
Proof. vm_refl. Qed.
Lemma D_c9748 : decode_any W_c9748 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c974c : bv 32 := 0x00e6a023.
Lemma F_c974c : fetch_word AsanUbsan.M.loaded_segments (0xc9748 : word) = Some W_c974c.
Proof. vm_refl. Qed.
Lemma D_c974c : decode_any W_c974c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9750 : bv 32 := 0x00468693.
Lemma F_c9750 : fetch_word AsanUbsan.M.loaded_segments (0xc974c : word) = Some W_c9750.
Proof. vm_refl. Qed.
Lemma D_c9750 : decode_any W_c9750 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9754 : bv 32 := 0x22c0006f.
Lemma F_c9754 : fetch_word AsanUbsan.M.loaded_segments (0xc9750 : word) = Some W_c9754.
Proof. vm_refl. Qed.
Lemma D_c9754 : decode_any W_c9754 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9758 : bv 32 := 0x00e68023.
Lemma F_c9758 : fetch_word AsanUbsan.M.loaded_segments (0xc9754 : word) = Some W_c9758.
Proof. vm_refl. Qed.
Lemma D_c9758 : decode_any W_c9758 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c975c : bv 32 := 0x00168693.
Lemma F_c975c : fetch_word AsanUbsan.M.loaded_segments (0xc9758 : word) = Some W_c975c.
Proof. vm_refl. Qed.
Lemma D_c975c : decode_any W_c975c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9760 : bv 32 := 0xfff60613.
Lemma F_c9760 : fetch_word AsanUbsan.M.loaded_segments (0xc975c : word) = Some W_c9760.
Proof. vm_refl. Qed.
Lemma D_c9760 : decode_any W_c9760 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9764 : bv 32 := 0x01058593.
Lemma F_c9764 : fetch_word AsanUbsan.M.loaded_segments (0xc9760 : word) = Some W_c9764.
Proof. vm_refl. Qed.
Lemma D_c9764 : decode_any W_c9764 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9768 : bv 32 := 0x01200793.
Lemma F_c9768 : fetch_word AsanUbsan.M.loaded_segments (0xc9764 : word) = Some W_c9768.
Proof. vm_refl. Qed.
Lemma D_c9768 : decode_any W_c9768 = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_c976c : bv 32 := 0x0087581b.
Lemma F_c976c : fetch_word AsanUbsan.M.loaded_segments (0xc9768 : word) = Some W_c976c.
Proof. vm_refl. Qed.
Lemma D_c976c : decode_any W_c976c = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9770 : bv 32 := 0xff45a883.
Lemma F_c9770 : fetch_word AsanUbsan.M.loaded_segments (0xc976c : word) = Some W_c9770.
Proof. vm_refl. Qed.
Lemma D_c9770 : decode_any W_c9770 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9774 : bv 32 := 0xff85a283.
Lemma F_c9774 : fetch_word AsanUbsan.M.loaded_segments (0xc9770 : word) = Some W_c9774.
Proof. vm_refl. Qed.
Lemma D_c9774 : decode_any W_c9774 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9778 : bv 32 := 0xffc5a303.
Lemma F_c9778 : fetch_word AsanUbsan.M.loaded_segments (0xc9774 : word) = Some W_c9778.
Proof. vm_refl. Qed.
Lemma D_c9778 : decode_any W_c9778 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c977c : bv 32 := 0x0005a703.
Lemma F_c977c : fetch_word AsanUbsan.M.loaded_segments (0xc9778 : word) = Some W_c977c.
Proof. vm_refl. Qed.
Lemma D_c977c : decode_any W_c977c = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9780 : bv 32 := 0x01889393.
Lemma F_c9780 : fetch_word AsanUbsan.M.loaded_segments (0xc977c : word) = Some W_c9780.
Proof. vm_refl. Qed.
Lemma D_c9780 : decode_any W_c9780 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9784 : bv 32 := 0x0088d89b.
Lemma F_c9784 : fetch_word AsanUbsan.M.loaded_segments (0xc9780 : word) = Some W_c9784.
Proof. vm_refl. Qed.
Lemma D_c9784 : decode_any W_c9784 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9788 : bv 32 := 0x0103e833.
Lemma F_c9788 : fetch_word AsanUbsan.M.loaded_segments (0xc9784 : word) = Some W_c9788.
Proof. vm_refl. Qed.
Lemma D_c9788 : decode_any W_c9788 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c978c : bv 32 := 0x01829393.
Lemma F_c978c : fetch_word AsanUbsan.M.loaded_segments (0xc9788 : word) = Some W_c978c.
Proof. vm_refl. Qed.
Lemma D_c978c : decode_any W_c978c = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9790 : bv 32 := 0x0082d29b.
Lemma F_c9790 : fetch_word AsanUbsan.M.loaded_segments (0xc978c : word) = Some W_c9790.
Proof. vm_refl. Qed.
Lemma D_c9790 : decode_any W_c9790 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9794 : bv 32 := 0x0113e8b3.
Lemma F_c9794 : fetch_word AsanUbsan.M.loaded_segments (0xc9790 : word) = Some W_c9794.
Proof. vm_refl. Qed.
Lemma D_c9794 : decode_any W_c9794 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9798 : bv 32 := 0x01831393.
Lemma F_c9798 : fetch_word AsanUbsan.M.loaded_segments (0xc9794 : word) = Some W_c9798.
Proof. vm_refl. Qed.
Lemma D_c9798 : decode_any W_c9798 = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c979c : bv 32 := 0x0083531b.
Lemma F_c979c : fetch_word AsanUbsan.M.loaded_segments (0xc9798 : word) = Some W_c979c.
Proof. vm_refl. Qed.
Lemma D_c979c : decode_any W_c979c = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97a0 : bv 32 := 0x0053e2b3.
Lemma F_c97a0 : fetch_word AsanUbsan.M.loaded_segments (0xc979c : word) = Some W_c97a0.
Proof. vm_refl. Qed.
Lemma D_c97a0 : decode_any W_c97a0 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97a4 : bv 32 := 0x01871393.
Lemma F_c97a4 : fetch_word AsanUbsan.M.loaded_segments (0xc97a0 : word) = Some W_c97a4.
Proof. vm_refl. Qed.
Lemma D_c97a4 : decode_any W_c97a4 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97a8 : bv 32 := 0x0063e333.
Lemma F_c97a8 : fetch_word AsanUbsan.M.loaded_segments (0xc97a4 : word) = Some W_c97a8.
Proof. vm_refl. Qed.
Lemma D_c97a8 : decode_any W_c97a8 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97ac : bv 32 := 0xff060613.
Lemma F_c97ac : fetch_word AsanUbsan.M.loaded_segments (0xc97a8 : word) = Some W_c97ac.
Proof. vm_refl. Qed.
Lemma D_c97ac : decode_any W_c97ac = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97b0 : bv 32 := 0x0106a023.
Lemma F_c97b0 : fetch_word AsanUbsan.M.loaded_segments (0xc97ac : word) = Some W_c97b0.
Proof. vm_refl. Qed.
Lemma D_c97b0 : decode_any W_c97b0 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97b4 : bv 32 := 0x0116a223.
Lemma F_c97b4 : fetch_word AsanUbsan.M.loaded_segments (0xc97b0 : word) = Some W_c97b4.
Proof. vm_refl. Qed.
Lemma D_c97b4 : decode_any W_c97b4 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97b8 : bv 32 := 0x0056a423.
Lemma F_c97b8 : fetch_word AsanUbsan.M.loaded_segments (0xc97b4 : word) = Some W_c97b8.
Proof. vm_refl. Qed.
Lemma D_c97b8 : decode_any W_c97b8 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97bc : bv 32 := 0x0066a623.
Lemma F_c97bc : fetch_word AsanUbsan.M.loaded_segments (0xc97b8 : word) = Some W_c97bc.
Proof. vm_refl. Qed.
Lemma D_c97bc : decode_any W_c97bc = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97c0 : bv 32 := 0x01068693.
Lemma F_c97c0 : fetch_word AsanUbsan.M.loaded_segments (0xc97bc : word) = Some W_c97c0.
Proof. vm_refl. Qed.
Lemma D_c97c0 : decode_any W_c97c0 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97c4 : bv 32 := 0x01058593.
Lemma F_c97c4 : fetch_word AsanUbsan.M.loaded_segments (0xc97c0 : word) = Some W_c97c4.
Proof. vm_refl. Qed.
Lemma D_c97c4 : decode_any W_c97c4 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97c8 : bv 32 := 0xfac7e2e3.
Lemma F_c97c8 : fetch_word AsanUbsan.M.loaded_segments (0xc97c4 : word) = Some W_c97c8.
Proof. vm_refl. Qed.
Lemma D_c97c8 : decode_any W_c97c8 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97cc : bv 32 := 0xff158593.
Lemma F_c97cc : fetch_word AsanUbsan.M.loaded_segments (0xc97c8 : word) = Some W_c97cc.
Proof. vm_refl. Qed.
Lemma D_c97cc : decode_any W_c97cc = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97d0 : bv 32 := 0x01000713.
Lemma F_c97d0 : fetch_word AsanUbsan.M.loaded_segments (0xc97cc : word) = Some W_c97d0.
Proof. vm_refl. Qed.
Lemma D_c97d0 : decode_any W_c97d0 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97d4 : bv 32 := 0xe4e666e3.
Lemma F_c97d4 : fetch_word AsanUbsan.M.loaded_segments (0xc97d0 : word) = Some W_c97d4.
Proof. vm_refl. Qed.
Lemma D_c97d4 : decode_any W_c97d4 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97d8 : bv 32 := 0x0940006f.
Lemma F_c97d8 : fetch_word AsanUbsan.M.loaded_segments (0xc97d4 : word) = Some W_c97d8.
Proof. vm_refl. Qed.
Lemma D_c97d8 : decode_any W_c97d8 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97dc : bv 32 := 0x00875793.
Lemma F_c97dc : fetch_word AsanUbsan.M.loaded_segments (0xc97d8 : word) = Some W_c97dc.
Proof. vm_refl. Qed.
Lemma D_c97dc : decode_any W_c97dc = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97e0 : bv 32 := 0x01075813.
Lemma F_c97e0 : fetch_word AsanUbsan.M.loaded_segments (0xc97dc : word) = Some W_c97e0.
Proof. vm_refl. Qed.
Lemma D_c97e0 : decode_any W_c97e0 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97e4 : bv 32 := 0xffd60613.
Lemma F_c97e4 : fetch_word AsanUbsan.M.loaded_segments (0xc97e0 : word) = Some W_c97e4.
Proof. vm_refl. Qed.
Lemma D_c97e4 : decode_any W_c97e4 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97e8 : bv 32 := 0x00e68023.
Lemma F_c97e8 : fetch_word AsanUbsan.M.loaded_segments (0xc97e4 : word) = Some W_c97e8.
Proof. vm_refl. Qed.
Lemma D_c97e8 : decode_any W_c97e8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97ec : bv 32 := 0x00f680a3.
Lemma F_c97ec : fetch_word AsanUbsan.M.loaded_segments (0xc97e8 : word) = Some W_c97ec.
Proof. vm_refl. Qed.
Lemma D_c97ec : decode_any W_c97ec = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97f0 : bv 32 := 0x01068123.
Lemma F_c97f0 : fetch_word AsanUbsan.M.loaded_segments (0xc97ec : word) = Some W_c97f0.
Proof. vm_refl. Qed.
Lemma D_c97f0 : decode_any W_c97f0 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97f4 : bv 32 := 0x00368693.
Lemma F_c97f4 : fetch_word AsanUbsan.M.loaded_segments (0xc97f0 : word) = Some W_c97f4.
Proof. vm_refl. Qed.
Lemma D_c97f4 : decode_any W_c97f4 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97f8 : bv 32 := 0x01058593.
Lemma F_c97f8 : fetch_word AsanUbsan.M.loaded_segments (0xc97f4 : word) = Some W_c97f8.
Proof. vm_refl. Qed.
Lemma D_c97f8 : decode_any W_c97f8 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c97fc : bv 32 := 0x01000793.
Lemma F_c97fc : fetch_word AsanUbsan.M.loaded_segments (0xc97f8 : word) = Some W_c97fc.
Proof. vm_refl. Qed.
Lemma D_c97fc : decode_any W_c97fc = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9800 : bv 32 := 0x0187581b.
Lemma F_c9800 : fetch_word AsanUbsan.M.loaded_segments (0xc97fc : word) = Some W_c9800.
Proof. vm_refl. Qed.
Lemma D_c9800 : decode_any W_c9800 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9804 : bv 32 := 0xff45a883.
Lemma F_c9804 : fetch_word AsanUbsan.M.loaded_segments (0xc9800 : word) = Some W_c9804.
Proof. vm_refl. Qed.
Lemma D_c9804 : decode_any W_c9804 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9808 : bv 32 := 0xff85a283.
Lemma F_c9808 : fetch_word AsanUbsan.M.loaded_segments (0xc9804 : word) = Some W_c9808.
Proof. vm_refl. Qed.
Lemma D_c9808 : decode_any W_c9808 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_c980c : bv 32 := 0xffc5a303.
Lemma F_c980c : fetch_word AsanUbsan.M.loaded_segments (0xc9808 : word) = Some W_c980c.
Proof. vm_refl. Qed.
Lemma D_c980c : decode_any W_c980c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9810 : bv 32 := 0x0005a703.
Lemma F_c9810 : fetch_word AsanUbsan.M.loaded_segments (0xc980c : word) = Some W_c9810.
Proof. vm_refl. Qed.
Lemma D_c9810 : decode_any W_c9810 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9814 : bv 32 := 0x00889393.
Lemma F_c9814 : fetch_word AsanUbsan.M.loaded_segments (0xc9810 : word) = Some W_c9814.
Proof. vm_refl. Qed.
Lemma D_c9814 : decode_any W_c9814 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9818 : bv 32 := 0x0188d89b.
Lemma F_c9818 : fetch_word AsanUbsan.M.loaded_segments (0xc9814 : word) = Some W_c9818.
Proof. vm_refl. Qed.
Lemma D_c9818 : decode_any W_c9818 = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c981c : bv 32 := 0x0103e833.
Lemma F_c981c : fetch_word AsanUbsan.M.loaded_segments (0xc9818 : word) = Some W_c981c.
Proof. vm_refl. Qed.
Lemma D_c981c : decode_any W_c981c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9820 : bv 32 := 0x00829393.
Lemma F_c9820 : fetch_word AsanUbsan.M.loaded_segments (0xc981c : word) = Some W_c9820.
Proof. vm_refl. Qed.
Lemma D_c9820 : decode_any W_c9820 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9824 : bv 32 := 0x0182d29b.
Lemma F_c9824 : fetch_word AsanUbsan.M.loaded_segments (0xc9820 : word) = Some W_c9824.
Proof. vm_refl. Qed.
Lemma D_c9824 : decode_any W_c9824 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9828 : bv 32 := 0x0113e8b3.
Lemma F_c9828 : fetch_word AsanUbsan.M.loaded_segments (0xc9824 : word) = Some W_c9828.
Proof. vm_refl. Qed.
Lemma D_c9828 : decode_any W_c9828 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_c982c : bv 32 := 0x00831393.
Lemma F_c982c : fetch_word AsanUbsan.M.loaded_segments (0xc9828 : word) = Some W_c982c.
Proof. vm_refl. Qed.
Lemma D_c982c : decode_any W_c982c = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9830 : bv 32 := 0x0183531b.
Lemma F_c9830 : fetch_word AsanUbsan.M.loaded_segments (0xc982c : word) = Some W_c9830.
Proof. vm_refl. Qed.
Lemma D_c9830 : decode_any W_c9830 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9834 : bv 32 := 0x0053e2b3.
Lemma F_c9834 : fetch_word AsanUbsan.M.loaded_segments (0xc9830 : word) = Some W_c9834.
Proof. vm_refl. Qed.
Lemma D_c9834 : decode_any W_c9834 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9838 : bv 32 := 0x00871393.
Lemma F_c9838 : fetch_word AsanUbsan.M.loaded_segments (0xc9834 : word) = Some W_c9838.
Proof. vm_refl. Qed.
Lemma D_c9838 : decode_any W_c9838 = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c983c : bv 32 := 0x0063e333.
Lemma F_c983c : fetch_word AsanUbsan.M.loaded_segments (0xc9838 : word) = Some W_c983c.
Proof. vm_refl. Qed.
Lemma D_c983c : decode_any W_c983c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9840 : bv 32 := 0xff060613.
Lemma F_c9840 : fetch_word AsanUbsan.M.loaded_segments (0xc983c : word) = Some W_c9840.
Proof. vm_refl. Qed.
Lemma D_c9840 : decode_any W_c9840 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9844 : bv 32 := 0x0106a023.
Lemma F_c9844 : fetch_word AsanUbsan.M.loaded_segments (0xc9840 : word) = Some W_c9844.
Proof. vm_refl. Qed.
Lemma D_c9844 : decode_any W_c9844 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9848 : bv 32 := 0x0116a223.
Lemma F_c9848 : fetch_word AsanUbsan.M.loaded_segments (0xc9844 : word) = Some W_c9848.
Proof. vm_refl. Qed.
Lemma D_c9848 : decode_any W_c9848 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c984c : bv 32 := 0x0056a423.
Lemma F_c984c : fetch_word AsanUbsan.M.loaded_segments (0xc9848 : word) = Some W_c984c.
Proof. vm_refl. Qed.
Lemma D_c984c : decode_any W_c984c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9850 : bv 32 := 0x0066a623.
Lemma F_c9850 : fetch_word AsanUbsan.M.loaded_segments (0xc984c : word) = Some W_c9850.
Proof. vm_refl. Qed.
Lemma D_c9850 : decode_any W_c9850 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9854 : bv 32 := 0x01068693.
Lemma F_c9854 : fetch_word AsanUbsan.M.loaded_segments (0xc9850 : word) = Some W_c9854.
Proof. vm_refl. Qed.
Lemma D_c9854 : decode_any W_c9854 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9858 : bv 32 := 0x01058593.
Lemma F_c9858 : fetch_word AsanUbsan.M.loaded_segments (0xc9854 : word) = Some W_c9858.
Proof. vm_refl. Qed.
Lemma D_c9858 : decode_any W_c9858 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c985c : bv 32 := 0xfac7e2e3.
Lemma F_c985c : fetch_word AsanUbsan.M.loaded_segments (0xc9858 : word) = Some W_c985c.
Proof. vm_refl. Qed.
Lemma D_c985c : decode_any W_c985c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9860 : bv 32 := 0xff358593.
Lemma F_c9860 : fetch_word AsanUbsan.M.loaded_segments (0xc985c : word) = Some W_c9860.
Proof. vm_refl. Qed.
Lemma D_c9860 : decode_any W_c9860 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9864 : bv 32 := 0x01000713.
Lemma F_c9864 : fetch_word AsanUbsan.M.loaded_segments (0xc9860 : word) = Some W_c9864.
Proof. vm_refl. Qed.
Lemma D_c9864 : decode_any W_c9864 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9868 : bv 32 := 0xdae66ce3.
Lemma F_c9868 : fetch_word AsanUbsan.M.loaded_segments (0xc9864 : word) = Some W_c9868.
Proof. vm_refl. Qed.
Lemma D_c9868 : decode_any W_c9868 = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

Definition W_c986c : bv 32 := 0x0005c703.
Lemma F_c986c : fetch_word AsanUbsan.M.loaded_segments (0xc9868 : word) = Some W_c986c.
Proof. vm_refl. Qed.
Lemma D_c986c : decode_any W_c986c = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9870 : bv 32 := 0x0015c783.
Lemma F_c9870 : fetch_word AsanUbsan.M.loaded_segments (0xc986c : word) = Some W_c9870.
Proof. vm_refl. Qed.
Lemma D_c9870 : decode_any W_c9870 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9874 : bv 32 := 0x0025c803.
Lemma F_c9874 : fetch_word AsanUbsan.M.loaded_segments (0xc9870 : word) = Some W_c9874.
Proof. vm_refl. Qed.
Lemma D_c9874 : decode_any W_c9874 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9878 : bv 32 := 0x0035c883.
Lemma F_c9878 : fetch_word AsanUbsan.M.loaded_segments (0xc9874 : word) = Some W_c9878.
Proof. vm_refl. Qed.
Lemma D_c9878 : decode_any W_c9878 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c987c : bv 32 := 0x0045c283.
Lemma F_c987c : fetch_word AsanUbsan.M.loaded_segments (0xc9878 : word) = Some W_c987c.
Proof. vm_refl. Qed.
Lemma D_c987c : decode_any W_c987c = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9880 : bv 32 := 0x0055c303.
Lemma F_c9880 : fetch_word AsanUbsan.M.loaded_segments (0xc987c : word) = Some W_c9880.
Proof. vm_refl. Qed.
Lemma D_c9880 : decode_any W_c9880 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9884 : bv 32 := 0x0065c383.
Lemma F_c9884 : fetch_word AsanUbsan.M.loaded_segments (0xc9880 : word) = Some W_c9884.
Proof. vm_refl. Qed.
Lemma D_c9884 : decode_any W_c9884 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9888 : bv 32 := 0x0075ce03.
Lemma F_c9888 : fetch_word AsanUbsan.M.loaded_segments (0xc9884 : word) = Some W_c9888.
Proof. vm_refl. Qed.
Lemma D_c9888 : decode_any W_c9888 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c988c : bv 32 := 0x00e68023.
Lemma F_c988c : fetch_word AsanUbsan.M.loaded_segments (0xc9888 : word) = Some W_c988c.
Proof. vm_refl. Qed.
Lemma D_c988c : decode_any W_c988c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9890 : bv 32 := 0x00f680a3.
Lemma F_c9890 : fetch_word AsanUbsan.M.loaded_segments (0xc988c : word) = Some W_c9890.
Proof. vm_refl. Qed.
Lemma D_c9890 : decode_any W_c9890 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9894 : bv 32 := 0x01068123.
Lemma F_c9894 : fetch_word AsanUbsan.M.loaded_segments (0xc9890 : word) = Some W_c9894.
Proof. vm_refl. Qed.
Lemma D_c9894 : decode_any W_c9894 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9898 : bv 32 := 0x011681a3.
Lemma F_c9898 : fetch_word AsanUbsan.M.loaded_segments (0xc9894 : word) = Some W_c9898.
Proof. vm_refl. Qed.
Lemma D_c9898 : decode_any W_c9898 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c989c : bv 32 := 0x0085c703.
Lemma F_c989c : fetch_word AsanUbsan.M.loaded_segments (0xc9898 : word) = Some W_c989c.
Proof. vm_refl. Qed.
Lemma D_c989c : decode_any W_c989c = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98a0 : bv 32 := 0x0095c783.
Lemma F_c98a0 : fetch_word AsanUbsan.M.loaded_segments (0xc989c : word) = Some W_c98a0.
Proof. vm_refl. Qed.
Lemma D_c98a0 : decode_any W_c98a0 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98a4 : bv 32 := 0x00a5c803.
Lemma F_c98a4 : fetch_word AsanUbsan.M.loaded_segments (0xc98a0 : word) = Some W_c98a4.
Proof. vm_refl. Qed.
Lemma D_c98a4 : decode_any W_c98a4 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98a8 : bv 32 := 0x00b5c883.
Lemma F_c98a8 : fetch_word AsanUbsan.M.loaded_segments (0xc98a4 : word) = Some W_c98a8.
Proof. vm_refl. Qed.
Lemma D_c98a8 : decode_any W_c98a8 = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98ac : bv 32 := 0x00568223.
Lemma F_c98ac : fetch_word AsanUbsan.M.loaded_segments (0xc98a8 : word) = Some W_c98ac.
Proof. vm_refl. Qed.
Lemma D_c98ac : decode_any W_c98ac = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98b0 : bv 32 := 0x006682a3.
Lemma F_c98b0 : fetch_word AsanUbsan.M.loaded_segments (0xc98ac : word) = Some W_c98b0.
Proof. vm_refl. Qed.
Lemma D_c98b0 : decode_any W_c98b0 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98b4 : bv 32 := 0x00768323.
Lemma F_c98b4 : fetch_word AsanUbsan.M.loaded_segments (0xc98b0 : word) = Some W_c98b4.
Proof. vm_refl. Qed.
Lemma D_c98b4 : decode_any W_c98b4 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98b8 : bv 32 := 0x01c683a3.
Lemma F_c98b8 : fetch_word AsanUbsan.M.loaded_segments (0xc98b4 : word) = Some W_c98b8.
Proof. vm_refl. Qed.
Lemma D_c98b8 : decode_any W_c98b8 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98bc : bv 32 := 0x00c5c283.
Lemma F_c98bc : fetch_word AsanUbsan.M.loaded_segments (0xc98b8 : word) = Some W_c98bc.
Proof. vm_refl. Qed.
Lemma D_c98bc : decode_any W_c98bc = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98c0 : bv 32 := 0x00d5c303.
Lemma F_c98c0 : fetch_word AsanUbsan.M.loaded_segments (0xc98bc : word) = Some W_c98c0.
Proof. vm_refl. Qed.
Lemma D_c98c0 : decode_any W_c98c0 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98c4 : bv 32 := 0x00e5c383.
Lemma F_c98c4 : fetch_word AsanUbsan.M.loaded_segments (0xc98c0 : word) = Some W_c98c4.
Proof. vm_refl. Qed.
Lemma D_c98c4 : decode_any W_c98c4 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98c8 : bv 32 := 0x00f5ce03.
Lemma F_c98c8 : fetch_word AsanUbsan.M.loaded_segments (0xc98c4 : word) = Some W_c98c8.
Proof. vm_refl. Qed.
Lemma D_c98c8 : decode_any W_c98c8 = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98cc : bv 32 := 0x01058593.
Lemma F_c98cc : fetch_word AsanUbsan.M.loaded_segments (0xc98c8 : word) = Some W_c98cc.
Proof. vm_refl. Qed.
Lemma D_c98cc : decode_any W_c98cc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98d0 : bv 32 := 0x00e68423.
Lemma F_c98d0 : fetch_word AsanUbsan.M.loaded_segments (0xc98cc : word) = Some W_c98d0.
Proof. vm_refl. Qed.
Lemma D_c98d0 : decode_any W_c98d0 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98d4 : bv 32 := 0x00f684a3.
Lemma F_c98d4 : fetch_word AsanUbsan.M.loaded_segments (0xc98d0 : word) = Some W_c98d4.
Proof. vm_refl. Qed.
Lemma D_c98d4 : decode_any W_c98d4 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98d8 : bv 32 := 0x01068523.
Lemma F_c98d8 : fetch_word AsanUbsan.M.loaded_segments (0xc98d4 : word) = Some W_c98d8.
Proof. vm_refl. Qed.
Lemma D_c98d8 : decode_any W_c98d8 = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98dc : bv 32 := 0x011685a3.
Lemma F_c98dc : fetch_word AsanUbsan.M.loaded_segments (0xc98d8 : word) = Some W_c98dc.
Proof. vm_refl. Qed.
Lemma D_c98dc : decode_any W_c98dc = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98e0 : bv 32 := 0x01068713.
Lemma F_c98e0 : fetch_word AsanUbsan.M.loaded_segments (0xc98dc : word) = Some W_c98e0.
Proof. vm_refl. Qed.
Lemma D_c98e0 : decode_any W_c98e0 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98e4 : bv 32 := 0x00568623.
Lemma F_c98e4 : fetch_word AsanUbsan.M.loaded_segments (0xc98e0 : word) = Some W_c98e4.
Proof. vm_refl. Qed.
Lemma D_c98e4 : decode_any W_c98e4 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98e8 : bv 32 := 0x006686a3.
Lemma F_c98e8 : fetch_word AsanUbsan.M.loaded_segments (0xc98e4 : word) = Some W_c98e8.
Proof. vm_refl. Qed.
Lemma D_c98e8 : decode_any W_c98e8 = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98ec : bv 32 := 0x00768723.
Lemma F_c98ec : fetch_word AsanUbsan.M.loaded_segments (0xc98e8 : word) = Some W_c98ec.
Proof. vm_refl. Qed.
Lemma D_c98ec : decode_any W_c98ec = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98f0 : bv 32 := 0x01c687a3.
Lemma F_c98f0 : fetch_word AsanUbsan.M.loaded_segments (0xc98ec : word) = Some W_c98f0.
Proof. vm_refl. Qed.
Lemma D_c98f0 : decode_any W_c98f0 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98f4 : bv 32 := 0x00070693.
Lemma F_c98f4 : fetch_word AsanUbsan.M.loaded_segments (0xc98f0 : word) = Some W_c98f4.
Proof. vm_refl. Qed.
Lemma D_c98f4 : decode_any W_c98f4 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98f8 : bv 32 := 0x00867713.
Lemma F_c98f8 : fetch_word AsanUbsan.M.loaded_segments (0xc98f4 : word) = Some W_c98f8.
Proof. vm_refl. Qed.
Lemma D_c98f8 : decode_any W_c98f8 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c98fc : bv 32 := 0xd20706e3.
Lemma F_c98fc : fetch_word AsanUbsan.M.loaded_segments (0xc98f8 : word) = Some W_c98fc.
Proof. vm_refl. Qed.
Lemma D_c98fc : decode_any W_c98fc = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9900 : bv 32 := 0x0005c703.
Lemma F_c9900 : fetch_word AsanUbsan.M.loaded_segments (0xc98fc : word) = Some W_c9900.
Proof. vm_refl. Qed.
Lemma D_c9900 : decode_any W_c9900 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9904 : bv 32 := 0x0015c783.
Lemma F_c9904 : fetch_word AsanUbsan.M.loaded_segments (0xc9900 : word) = Some W_c9904.
Proof. vm_refl. Qed.
Lemma D_c9904 : decode_any W_c9904 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9908 : bv 32 := 0x0025c803.
Lemma F_c9908 : fetch_word AsanUbsan.M.loaded_segments (0xc9904 : word) = Some W_c9908.
Proof. vm_refl. Qed.
Lemma D_c9908 : decode_any W_c9908 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c990c : bv 32 := 0x0035c883.
Lemma F_c990c : fetch_word AsanUbsan.M.loaded_segments (0xc9908 : word) = Some W_c990c.
Proof. vm_refl. Qed.
Lemma D_c990c : decode_any W_c990c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9910 : bv 32 := 0x0045c283.
Lemma F_c9910 : fetch_word AsanUbsan.M.loaded_segments (0xc990c : word) = Some W_c9910.
Proof. vm_refl. Qed.
Lemma D_c9910 : decode_any W_c9910 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9914 : bv 32 := 0x0055c303.
Lemma F_c9914 : fetch_word AsanUbsan.M.loaded_segments (0xc9910 : word) = Some W_c9914.
Proof. vm_refl. Qed.
Lemma D_c9914 : decode_any W_c9914 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9918 : bv 32 := 0x0065c383.
Lemma F_c9918 : fetch_word AsanUbsan.M.loaded_segments (0xc9914 : word) = Some W_c9918.
Proof. vm_refl. Qed.
Lemma D_c9918 : decode_any W_c9918 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c991c : bv 32 := 0x0075ce03.
Lemma F_c991c : fetch_word AsanUbsan.M.loaded_segments (0xc9918 : word) = Some W_c991c.
Proof. vm_refl. Qed.
Lemma D_c991c : decode_any W_c991c = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9920 : bv 32 := 0x00858593.
Lemma F_c9920 : fetch_word AsanUbsan.M.loaded_segments (0xc991c : word) = Some W_c9920.
Proof. vm_refl. Qed.
Lemma D_c9920 : decode_any W_c9920 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9924 : bv 32 := 0x00e68023.
Lemma F_c9924 : fetch_word AsanUbsan.M.loaded_segments (0xc9920 : word) = Some W_c9924.
Proof. vm_refl. Qed.
Lemma D_c9924 : decode_any W_c9924 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9928 : bv 32 := 0x00f680a3.
Lemma F_c9928 : fetch_word AsanUbsan.M.loaded_segments (0xc9924 : word) = Some W_c9928.
Proof. vm_refl. Qed.
Lemma D_c9928 : decode_any W_c9928 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c992c : bv 32 := 0x01068123.
Lemma F_c992c : fetch_word AsanUbsan.M.loaded_segments (0xc9928 : word) = Some W_c992c.
Proof. vm_refl. Qed.
Lemma D_c992c : decode_any W_c992c = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9930 : bv 32 := 0x011681a3.
Lemma F_c9930 : fetch_word AsanUbsan.M.loaded_segments (0xc992c : word) = Some W_c9930.
Proof. vm_refl. Qed.
Lemma D_c9930 : decode_any W_c9930 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9934 : bv 32 := 0x00868713.
Lemma F_c9934 : fetch_word AsanUbsan.M.loaded_segments (0xc9930 : word) = Some W_c9934.
Proof. vm_refl. Qed.
Lemma D_c9934 : decode_any W_c9934 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9938 : bv 32 := 0x00568223.
Lemma F_c9938 : fetch_word AsanUbsan.M.loaded_segments (0xc9934 : word) = Some W_c9938.
Proof. vm_refl. Qed.
Lemma D_c9938 : decode_any W_c9938 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c993c : bv 32 := 0x006682a3.
Lemma F_c993c : fetch_word AsanUbsan.M.loaded_segments (0xc9938 : word) = Some W_c993c.
Proof. vm_refl. Qed.
Lemma D_c993c : decode_any W_c993c = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9940 : bv 32 := 0x00768323.
Lemma F_c9940 : fetch_word AsanUbsan.M.loaded_segments (0xc993c : word) = Some W_c9940.
Proof. vm_refl. Qed.
Lemma D_c9940 : decode_any W_c9940 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9944 : bv 32 := 0x01c683a3.
Lemma F_c9944 : fetch_word AsanUbsan.M.loaded_segments (0xc9940 : word) = Some W_c9944.
Proof. vm_refl. Qed.
Lemma D_c9944 : decode_any W_c9944 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9948 : bv 32 := 0x00070693.
Lemma F_c9948 : fetch_word AsanUbsan.M.loaded_segments (0xc9944 : word) = Some W_c9948.
Proof. vm_refl. Qed.
Lemma D_c9948 : decode_any W_c9948 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c994c : bv 32 := 0x00467713.
Lemma F_c994c : fetch_word AsanUbsan.M.loaded_segments (0xc9948 : word) = Some W_c994c.
Proof. vm_refl. Qed.
Lemma D_c994c : decode_any W_c994c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9950 : bv 32 := 0x02070863.
Lemma F_c9950 : fetch_word AsanUbsan.M.loaded_segments (0xc994c : word) = Some W_c9950.
Proof. vm_refl. Qed.
Lemma D_c9950 : decode_any W_c9950 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9954 : bv 32 := 0x0005c703.
Lemma F_c9954 : fetch_word AsanUbsan.M.loaded_segments (0xc9950 : word) = Some W_c9954.
Proof. vm_refl. Qed.
Lemma D_c9954 : decode_any W_c9954 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9958 : bv 32 := 0x0015c783.
Lemma F_c9958 : fetch_word AsanUbsan.M.loaded_segments (0xc9954 : word) = Some W_c9958.
Proof. vm_refl. Qed.
Lemma D_c9958 : decode_any W_c9958 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c995c : bv 32 := 0x0025c803.
Lemma F_c995c : fetch_word AsanUbsan.M.loaded_segments (0xc9958 : word) = Some W_c995c.
Proof. vm_refl. Qed.
Lemma D_c995c : decode_any W_c995c = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9960 : bv 32 := 0x0035c883.
Lemma F_c9960 : fetch_word AsanUbsan.M.loaded_segments (0xc995c : word) = Some W_c9960.
Proof. vm_refl. Qed.
Lemma D_c9960 : decode_any W_c9960 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9964 : bv 32 := 0x00458593.
Lemma F_c9964 : fetch_word AsanUbsan.M.loaded_segments (0xc9960 : word) = Some W_c9964.
Proof. vm_refl. Qed.
Lemma D_c9964 : decode_any W_c9964 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9968 : bv 32 := 0x00468293.
Lemma F_c9968 : fetch_word AsanUbsan.M.loaded_segments (0xc9964 : word) = Some W_c9968.
Proof. vm_refl. Qed.
Lemma D_c9968 : decode_any W_c9968 = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_c996c : bv 32 := 0x00e68023.
Lemma F_c996c : fetch_word AsanUbsan.M.loaded_segments (0xc9968 : word) = Some W_c996c.
Proof. vm_refl. Qed.
Lemma D_c996c : decode_any W_c996c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9970 : bv 32 := 0x00f680a3.
Lemma F_c9970 : fetch_word AsanUbsan.M.loaded_segments (0xc996c : word) = Some W_c9970.
Proof. vm_refl. Qed.
Lemma D_c9970 : decode_any W_c9970 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9974 : bv 32 := 0x01068123.
Lemma F_c9974 : fetch_word AsanUbsan.M.loaded_segments (0xc9970 : word) = Some W_c9974.
Proof. vm_refl. Qed.
Lemma D_c9974 : decode_any W_c9974 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9978 : bv 32 := 0x011681a3.
Lemma F_c9978 : fetch_word AsanUbsan.M.loaded_segments (0xc9974 : word) = Some W_c9978.
Proof. vm_refl. Qed.
Lemma D_c9978 : decode_any W_c9978 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_c997c : bv 32 := 0x00028693.
Lemma F_c997c : fetch_word AsanUbsan.M.loaded_segments (0xc9978 : word) = Some W_c997c.
Proof. vm_refl. Qed.
Lemma D_c997c : decode_any W_c997c = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9980 : bv 32 := 0x00267713.
Lemma F_c9980 : fetch_word AsanUbsan.M.loaded_segments (0xc997c : word) = Some W_c9980.
Proof. vm_refl. Qed.
Lemma D_c9980 : decode_any W_c9980 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9984 : bv 32 := 0x00071863.
Lemma F_c9984 : fetch_word AsanUbsan.M.loaded_segments (0xc9980 : word) = Some W_c9984.
Proof. vm_refl. Qed.
Lemma D_c9984 : decode_any W_c9984 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9988 : bv 32 := 0x00167613.
Lemma F_c9988 : fetch_word AsanUbsan.M.loaded_segments (0xc9984 : word) = Some W_c9988.
Proof. vm_refl. Qed.
Lemma D_c9988 : decode_any W_c9988 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c998c : bv 32 := 0x02061663.
Lemma F_c998c : fetch_word AsanUbsan.M.loaded_segments (0xc9988 : word) = Some W_c998c.
Proof. vm_refl. Qed.
Lemma D_c998c : decode_any W_c998c = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9990 : bv 32 := 0x00008067.
Lemma F_c9990 : fetch_word AsanUbsan.M.loaded_segments (0xc998c : word) = Some W_c9990.
Proof. vm_refl. Qed.
Lemma D_c9990 : decode_any W_c9990 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9994 : bv 32 := 0x0005c703.
Lemma F_c9994 : fetch_word AsanUbsan.M.loaded_segments (0xc9990 : word) = Some W_c9994.
Proof. vm_refl. Qed.
Lemma D_c9994 : decode_any W_c9994 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c9998 : bv 32 := 0x0015c783.
Lemma F_c9998 : fetch_word AsanUbsan.M.loaded_segments (0xc9994 : word) = Some W_c9998.
Proof. vm_refl. Qed.
Lemma D_c9998 : decode_any W_c9998 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c999c : bv 32 := 0x00258593.
Lemma F_c999c : fetch_word AsanUbsan.M.loaded_segments (0xc9998 : word) = Some W_c999c.
Proof. vm_refl. Qed.
Lemma D_c999c : decode_any W_c999c = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99a0 : bv 32 := 0x00268813.
Lemma F_c99a0 : fetch_word AsanUbsan.M.loaded_segments (0xc999c : word) = Some W_c99a0.
Proof. vm_refl. Qed.
Lemma D_c99a0 : decode_any W_c99a0 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99a4 : bv 32 := 0x00e68023.
Lemma F_c99a4 : fetch_word AsanUbsan.M.loaded_segments (0xc99a0 : word) = Some W_c99a4.
Proof. vm_refl. Qed.
Lemma D_c99a4 : decode_any W_c99a4 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99a8 : bv 32 := 0x00f680a3.
Lemma F_c99a8 : fetch_word AsanUbsan.M.loaded_segments (0xc99a4 : word) = Some W_c99a8.
Proof. vm_refl. Qed.
Lemma D_c99a8 : decode_any W_c99a8 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99ac : bv 32 := 0x00080693.
Lemma F_c99ac : fetch_word AsanUbsan.M.loaded_segments (0xc99a8 : word) = Some W_c99ac.
Proof. vm_refl. Qed.
Lemma D_c99ac : decode_any W_c99ac = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99b0 : bv 32 := 0x00167613.
Lemma F_c99b0 : fetch_word AsanUbsan.M.loaded_segments (0xc99ac : word) = Some W_c99b0.
Proof. vm_refl. Qed.
Lemma D_c99b0 : decode_any W_c99b0 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99b4 : bv 32 := 0xfc060ee3.
Lemma F_c99b4 : fetch_word AsanUbsan.M.loaded_segments (0xc99b0 : word) = Some W_c99b4.
Proof. vm_refl. Qed.
Lemma D_c99b4 : decode_any W_c99b4 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99b8 : bv 32 := 0x0005c583.
Lemma F_c99b8 : fetch_word AsanUbsan.M.loaded_segments (0xc99b4 : word) = Some W_c99b8.
Proof. vm_refl. Qed.
Lemma D_c99b8 : decode_any W_c99b8 = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99bc : bv 32 := 0x00b68023.
Lemma F_c99bc : fetch_word AsanUbsan.M.loaded_segments (0xc99b8 : word) = Some W_c99bc.
Proof. vm_refl. Qed.
Lemma D_c99bc : decode_any W_c99bc = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_c99c0 : bv 32 := 0x00008067.
Lemma F_c99c0 : fetch_word AsanUbsan.M.loaded_segments (0xc99bc : word) = Some W_c99c0.
Proof. vm_refl. Qed.
Lemma D_c99c0 : decode_any W_c99c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
