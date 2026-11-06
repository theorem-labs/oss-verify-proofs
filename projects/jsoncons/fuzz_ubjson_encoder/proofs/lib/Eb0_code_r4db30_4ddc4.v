(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_645ac : bv 32 := 0x81010113.
Lemma F_645ac : fetch_word AsanUbsan.M.loaded_segments (0x645fc : word) = Some W_645ac.
Proof. vm_refl. Qed.
Lemma D_645ac : decode_any W_645ac = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_645b0 : bv 32 := 0x7e113423.
Lemma F_645b0 : fetch_word AsanUbsan.M.loaded_segments (0x64600 : word) = Some W_645b0.
Proof. vm_refl. Qed.
Lemma D_645b0 : decode_any W_645b0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_645b4 : bv 32 := 0x7e813023.
Lemma F_645b4 : fetch_word AsanUbsan.M.loaded_segments (0x64604 : word) = Some W_645b4.
Proof. vm_refl. Qed.
Lemma D_645b4 : decode_any W_645b4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_645b8 : bv 32 := 0x7c913c23.
Lemma F_645b8 : fetch_word AsanUbsan.M.loaded_segments (0x64608 : word) = Some W_645b8.
Proof. vm_refl. Qed.
Lemma D_645b8 : decode_any W_645b8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_645bc : bv 32 := 0x7d213823.
Lemma F_645bc : fetch_word AsanUbsan.M.loaded_segments (0x6460c : word) = Some W_645bc.
Proof. vm_refl. Qed.
Lemma D_645bc : decode_any W_645bc = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_645c0 : bv 32 := 0x7d313423.
Lemma F_645c0 : fetch_word AsanUbsan.M.loaded_segments (0x64610 : word) = Some W_645c0.
Proof. vm_refl. Qed.
Lemma D_645c0 : decode_any W_645c0 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_645c4 : bv 32 := 0x7d413023.
Lemma F_645c4 : fetch_word AsanUbsan.M.loaded_segments (0x64614 : word) = Some W_645c4.
Proof. vm_refl. Qed.
Lemma D_645c4 : decode_any W_645c4 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_645c8 : bv 32 := 0x7b513c23.
Lemma F_645c8 : fetch_word AsanUbsan.M.loaded_segments (0x64618 : word) = Some W_645c8.
Proof. vm_refl. Qed.
Lemma D_645c8 : decode_any W_645c8 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_645cc : bv 32 := 0x7b613823.
Lemma F_645cc : fetch_word AsanUbsan.M.loaded_segments (0x6461c : word) = Some W_645cc.
Proof. vm_refl. Qed.
Lemma D_645cc : decode_any W_645cc = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_645d0 : bv 32 := 0x7f010413.
Lemma F_645d0 : fetch_word AsanUbsan.M.loaded_segments (0x64620 : word) = Some W_645d0.
Proof. vm_refl. Qed.
Lemma D_645d0 : decode_any W_645d0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_645d4 : bv 32 := 0xf9010113.
Lemma F_645d4 : fetch_word AsanUbsan.M.loaded_segments (0x64624 : word) = Some W_645d4.
Proof. vm_refl. Qed.
Lemma D_645d4 : decode_any W_645d4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_645d8 : bv 32 := 0x00050913.
Lemma F_645d8 : fetch_word AsanUbsan.M.loaded_segments (0x64628 : word) = Some W_645d8.
Proof. vm_refl. Qed.
Lemma D_645d8 : decode_any W_645d8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_645dc : bv 32 := 0x5551c0ef.
Lemma F_645dc : fetch_word AsanUbsan.M.loaded_segments (0x6462c : word) = Some W_645dc.
Proof. vm_refl. Qed.
Lemma D_645dc : decode_any W_645dc = Some (Jal 1 118100, 4%Z).
Proof. vm_refl. Qed.

Definition W_645e0 : bv 32 := 0x0a050863.
Lemma F_645e0 : fetch_word AsanUbsan.M.loaded_segments (0x64630 : word) = Some W_645e0.
Proof. vm_refl. Qed.
Lemma D_645e0 : decode_any W_645e0 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_645e4 : bv 32 := 0x45d1d0ef.
Lemma F_645e4 : fetch_word AsanUbsan.M.loaded_segments (0x64634 : word) = Some W_645e4.
Proof. vm_refl. Qed.
Lemma D_645e4 : decode_any W_645e4 = Some (Jal 1 121948, 4%Z).
Proof. vm_refl. Qed.

Definition W_645e8 : bv 32 := 0x000db597.
Lemma F_645e8 : fetch_word AsanUbsan.M.loaded_segments (0x64638 : word) = Some W_645e8.
Proof. vm_refl. Qed.
Lemma D_645e8 : decode_any W_645e8 = Some (Auipc 11 219, 4%Z).
Proof. vm_refl. Qed.

Definition W_645ec : bv 32 := 0x0a85b583.
Lemma F_645ec : fetch_word AsanUbsan.M.loaded_segments (0x6463c : word) = Some W_645ec.
Proof. vm_refl. Qed.
Lemma D_645ec : decode_any W_645ec = Some (Load SZ8 true 11 11 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_645f0 : bv 32 := 0x00050493.
Lemma F_645f0 : fetch_word AsanUbsan.M.loaded_segments (0x64640 : word) = Some W_645f0.
Proof. vm_refl. Qed.
Lemma D_645f0 : decode_any W_645f0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_645f4 : bv 32 := 0x00090513.
Lemma F_645f4 : fetch_word AsanUbsan.M.loaded_segments (0x64644 : word) = Some W_645f4.
Proof. vm_refl. Qed.
Lemma D_645f4 : decode_any W_645f4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_645f8 : bv 32 := 0x000580e7.
Lemma F_645f8 : fetch_word AsanUbsan.M.loaded_segments (0x64648 : word) = Some W_645f8.
Proof. vm_refl. Qed.
Lemma D_645f8 : decode_any W_645f8 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_645fc : bv 32 := 0x06048463.
Lemma F_645fc : fetch_word AsanUbsan.M.loaded_segments (0x6464c : word) = Some W_645fc.
Proof. vm_refl. Qed.
Lemma D_645fc : decode_any W_645fc = Some (Branch BC_EQ 9 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_64600 : bv 32 := 0x000d9597.
Lemma F_64600 : fetch_word AsanUbsan.M.loaded_segments (0x64650 : word) = Some W_64600.
Proof. vm_refl. Qed.
Lemma D_64600 : decode_any W_64600 = Some (Auipc 11 217, 4%Z).
Proof. vm_refl. Qed.

Definition W_64604 : bv 32 := 0x2685b983.
Lemma F_64604 : fetch_word AsanUbsan.M.loaded_segments (0x64654 : word) = Some W_64604.
Proof. vm_refl. Qed.
Lemma D_64604 : decode_any W_64604 = Some (Load SZ8 true 19 11 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_64608 : bv 32 := 0x0fb9c583.
Lemma F_64608 : fetch_word AsanUbsan.M.loaded_segments (0x64658 : word) = Some W_64608.
Proof. vm_refl. Qed.
Lemma D_64608 : decode_any W_64608 = Some (Load SZ1 false 11 19 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_6460c : bv 32 := 0x04058c63.
Lemma F_6460c : fetch_word AsanUbsan.M.loaded_segments (0x6465c : word) = Some W_6460c.
Proof. vm_refl. Qed.
Lemma D_6460c : decode_any W_6460c = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64610 : bv 32 := 0x00150493.
Lemma F_64610 : fetch_word AsanUbsan.M.loaded_segments (0x64660 : word) = Some W_64610.
Proof. vm_refl. Qed.
Lemma D_64610 : decode_any W_64610 = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64614 : bv 32 := 0xfff94593.
Lemma F_64614 : fetch_word AsanUbsan.M.loaded_segments (0x64664 : word) = Some W_64614.
Proof. vm_refl. Qed.
Lemma D_64614 : decode_any W_64614 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64618 : bv 32 := 0x80040a13.
Lemma F_64618 : fetch_word AsanUbsan.M.loaded_segments (0x64668 : word) = Some W_64618.
Proof. vm_refl. Qed.
Lemma D_64618 : decode_any W_64618 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6461c : bv 32 := 0xfa8a0a13.
Lemma F_6461c : fetch_word AsanUbsan.M.loaded_segments (0x6466c : word) = Some W_6461c.
Proof. vm_refl. Qed.
Lemma D_6461c : decode_any W_6461c = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_64620 : bv 32 := 0x0a95e063.
Lemma F_64620 : fetch_word AsanUbsan.M.loaded_segments (0x64670 : word) = Some W_64620.
Proof. vm_refl. Qed.
Lemma D_64620 : decode_any W_64620 = Some (Branch BC_LTU 11 9 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_64624 : bv 32 := 0x04000593.
Lemma F_64624 : fetch_word AsanUbsan.M.loaded_segments (0x64674 : word) = Some W_64624.
Proof. vm_refl. Qed.
Lemma D_64624 : decode_any W_64624 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_64628 : bv 32 := 0x10b57263.
Lemma F_64628 : fetch_word AsanUbsan.M.loaded_segments (0x64678 : word) = Some W_64628.
Proof. vm_refl. Qed.
Lemma D_64628 : decode_any W_64628 = Some (Branch BC_GEU 10 11 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_6462c : bv 32 := 0x000d9597.
Lemma F_6462c : fetch_word AsanUbsan.M.loaded_segments (0x6467c : word) = Some W_6462c.
Proof. vm_refl. Qed.
Lemma D_6462c : decode_any W_6462c = Some (Auipc 11 217, 4%Z).
Proof. vm_refl. Qed.

Definition W_64630 : bv 32 := 0x24c5b583.
Lemma F_64630 : fetch_word AsanUbsan.M.loaded_segments (0x64680 : word) = Some W_64630.
Proof. vm_refl. Qed.
Lemma D_64630 : decode_any W_64630 = Some (Load SZ8 true 11 11 588, 4%Z).
Proof. vm_refl. Qed.

Definition W_64634 : bv 32 := 0x0005b603.
Lemma F_64634 : fetch_word AsanUbsan.M.loaded_segments (0x64684 : word) = Some W_64634.
Proof. vm_refl. Qed.
Lemma D_64634 : decode_any W_64634 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64638 : bv 32 := 0x012506b3.
Lemma F_64638 : fetch_word AsanUbsan.M.loaded_segments (0x64688 : word) = Some W_64638.
Proof. vm_refl. Qed.
Lemma D_64638 : decode_any W_64638 = Some (Op ALU_ADD 13 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_6463c : bv 32 := 0x00395593.
Lemma F_6463c : fetch_word AsanUbsan.M.loaded_segments (0x6468c : word) = Some W_6463c.
Proof. vm_refl. Qed.
Lemma D_6463c : decode_any W_6463c = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_64640 : bv 32 := 0x0036d713.
Lemma F_64640 : fetch_word AsanUbsan.M.loaded_segments (0x64690 : word) = Some W_64640.
Proof. vm_refl. Qed.
Lemma D_64640 : decode_any W_64640 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_64644 : bv 32 := 0x00b605b3.
Lemma F_64644 : fetch_word AsanUbsan.M.loaded_segments (0x64694 : word) = Some W_64644.
Proof. vm_refl. Qed.
Lemma D_64644 : decode_any W_64644 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64648 : bv 32 := 0x00e60633.
Lemma F_64648 : fetch_word AsanUbsan.M.loaded_segments (0x64698 : word) = Some W_64648.
Proof. vm_refl. Qed.
Lemma D_64648 : decode_any W_64648 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6464c : bv 32 := 0xff85f713.
Lemma F_6464c : fetch_word AsanUbsan.M.loaded_segments (0x6469c : word) = Some W_6464c.
Proof. vm_refl. Qed.
Lemma D_6464c : decode_any W_6464c = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_64650 : bv 32 := 0xff867793.
Lemma F_64650 : fetch_word AsanUbsan.M.loaded_segments (0x646a0 : word) = Some W_64650.
Proof. vm_refl. Qed.
Lemma D_64650 : decode_any W_64650 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_64654 : bv 32 := 0x00073703.
Lemma F_64654 : fetch_word AsanUbsan.M.loaded_segments (0x646a4 : word) = Some W_64654.
Proof. vm_refl. Qed.
Lemma D_64654 : decode_any W_64654 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64658 : bv 32 := 0x0007b783.
Lemma F_64658 : fetch_word AsanUbsan.M.loaded_segments (0x646a8 : word) = Some W_64658.
Proof. vm_refl. Qed.
Lemma D_64658 : decode_any W_64658 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6465c : bv 32 := 0x00e7e733.
Lemma F_6465c : fetch_word AsanUbsan.M.loaded_segments (0x646ac : word) = Some W_6465c.
Proof. vm_refl. Qed.
Lemma D_6465c : decode_any W_6465c = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64660 : bv 32 := 0x0c071e63.
Lemma F_64660 : fetch_word AsanUbsan.M.loaded_segments (0x646b0 : word) = Some W_64660.
Proof. vm_refl. Qed.
Lemma D_64660 : decode_any W_64660 = Some (Branch BC_NE 14 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_64664 : bv 32 := 0x07010113.
Lemma F_64664 : fetch_word AsanUbsan.M.loaded_segments (0x646b4 : word) = Some W_64664.
Proof. vm_refl. Qed.
Lemma D_64664 : decode_any W_64664 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_64668 : bv 32 := 0x7e813083.
Lemma F_64668 : fetch_word AsanUbsan.M.loaded_segments (0x646b8 : word) = Some W_64668.
Proof. vm_refl. Qed.
Lemma D_64668 : decode_any W_64668 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6466c : bv 32 := 0x7e013403.
Lemma F_6466c : fetch_word AsanUbsan.M.loaded_segments (0x646bc : word) = Some W_6466c.
Proof. vm_refl. Qed.
Lemma D_6466c : decode_any W_6466c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_64670 : bv 32 := 0x7d813483.
Lemma F_64670 : fetch_word AsanUbsan.M.loaded_segments (0x646c0 : word) = Some W_64670.
Proof. vm_refl. Qed.
Lemma D_64670 : decode_any W_64670 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_64674 : bv 32 := 0x7d013903.
Lemma F_64674 : fetch_word AsanUbsan.M.loaded_segments (0x646c4 : word) = Some W_64674.
Proof. vm_refl. Qed.
Lemma D_64674 : decode_any W_64674 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_64678 : bv 32 := 0x7c813983.
Lemma F_64678 : fetch_word AsanUbsan.M.loaded_segments (0x646c8 : word) = Some W_64678.
Proof. vm_refl. Qed.
Lemma D_64678 : decode_any W_64678 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_6467c : bv 32 := 0x7c013a03.
Lemma F_6467c : fetch_word AsanUbsan.M.loaded_segments (0x646cc : word) = Some W_6467c.
Proof. vm_refl. Qed.
Lemma D_6467c : decode_any W_6467c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_64680 : bv 32 := 0x7b813a83.
Lemma F_64680 : fetch_word AsanUbsan.M.loaded_segments (0x646d0 : word) = Some W_64680.
Proof. vm_refl. Qed.
Lemma D_64680 : decode_any W_64680 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_64684 : bv 32 := 0x7b013b03.
Lemma F_64684 : fetch_word AsanUbsan.M.loaded_segments (0x646d4 : word) = Some W_64684.
Proof. vm_refl. Qed.
Lemma D_64684 : decode_any W_64684 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_64688 : bv 32 := 0x7f010113.
Lemma F_64688 : fetch_word AsanUbsan.M.loaded_segments (0x646d8 : word) = Some W_64688.
Proof. vm_refl. Qed.
Lemma D_64688 : decode_any W_64688 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6468c : bv 32 := 0x00008067.
Lemma F_6468c : fetch_word AsanUbsan.M.loaded_segments (0x646dc : word) = Some W_6468c.
Proof. vm_refl. Qed.
Lemma D_6468c : decode_any W_6468c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6472c : bv 32 := 0x00050a93.
Lemma F_6472c : fetch_word AsanUbsan.M.loaded_segments (0x6477c : word) = Some W_6472c.
Proof. vm_refl. Qed.
Lemma D_6472c : decode_any W_6472c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64730 : bv 32 := 0x04049263.
Lemma F_64730 : fetch_word AsanUbsan.M.loaded_segments (0x64780 : word) = Some W_64730.
Proof. vm_refl. Qed.
Lemma D_64730 : decode_any W_64730 = Some (Branch BC_NE 9 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_6473c : bv 32 := 0x00050a93.
Lemma F_6473c : fetch_word AsanUbsan.M.loaded_segments (0x6478c : word) = Some W_6473c.
Proof. vm_refl. Qed.
Lemma D_6473c : decode_any W_6473c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64740 : bv 32 := 0x00060503.
Lemma F_64740 : fetch_word AsanUbsan.M.loaded_segments (0x64790 : word) = Some W_64740.
Proof. vm_refl. Qed.
Lemma D_64740 : decode_any W_64740 = Some (Load SZ1 true 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64744 : bv 32 := 0x0076f693.
Lemma F_64744 : fetch_word AsanUbsan.M.loaded_segments (0x64794 : word) = Some W_64744.
Proof. vm_refl. Qed.
Lemma D_64744 : decode_any W_64744 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_64748 : bv 32 := 0x00a03733.
Lemma F_64748 : fetch_word AsanUbsan.M.loaded_segments (0x64798 : word) = Some W_64748.
Proof. vm_refl. Qed.
Lemma D_64748 : decode_any W_64748 = Some (Op ALU_SLTU 14 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6474c : bv 32 := 0x00a6a533.
Lemma F_6474c : fetch_word AsanUbsan.M.loaded_segments (0x6479c : word) = Some W_6474c.
Proof. vm_refl. Qed.
Lemma D_6474c : decode_any W_6474c = Some (Op ALU_SLT 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64750 : bv 32 := 0x00154513.
Lemma F_64750 : fetch_word AsanUbsan.M.loaded_segments (0x647a0 : word) = Some W_64750.
Proof. vm_refl. Qed.
Lemma D_64750 : decode_any W_64750 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64754 : bv 32 := 0x00a77533.
Lemma F_64754 : fetch_word AsanUbsan.M.loaded_segments (0x647a4 : word) = Some W_64754.
Proof. vm_refl. Qed.
Lemma D_64754 : decode_any W_64754 = Some (Op ALU_AND 10 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64758 : bv 32 := 0x00c5fa63.
Lemma F_64758 : fetch_word AsanUbsan.M.loaded_segments (0x647a8 : word) = Some W_64758.
Proof. vm_refl. Qed.
Lemma D_64758 : decode_any W_64758 = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6475c : bv 32 := 0x0005c683.
Lemma F_6475c : fetch_word AsanUbsan.M.loaded_segments (0x647ac : word) = Some W_6475c.
Proof. vm_refl. Qed.
Lemma D_6475c : decode_any W_6475c = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64760 : bv 32 := 0x00158593.
Lemma F_64760 : fetch_word AsanUbsan.M.loaded_segments (0x647b0 : word) = Some W_64760.
Proof. vm_refl. Qed.
Lemma D_64760 : decode_any W_64760 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64764 : bv 32 := 0x00a6e533.
Lemma F_64764 : fetch_word AsanUbsan.M.loaded_segments (0x647b4 : word) = Some W_64764.
Proof. vm_refl. Qed.
Lemma D_64764 : decode_any W_64764 = Some (Op ALU_OR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64768 : bv 32 := 0xfec59ae3.
Lemma F_64768 : fetch_word AsanUbsan.M.loaded_segments (0x647b8 : word) = Some W_64768.
Proof. vm_refl. Qed.
Lemma D_64768 : decode_any W_64768 = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_6476c : bv 32 := 0x0ff57513.
Lemma F_6476c : fetch_word AsanUbsan.M.loaded_segments (0x647bc : word) = Some W_6476c.
Proof. vm_refl. Qed.
Lemma D_6476c : decode_any W_6476c = Some (OpImm ALU_AND 10 10 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_64770 : bv 32 := 0x0c050463.
Lemma F_64770 : fetch_word AsanUbsan.M.loaded_segments (0x647c0 : word) = Some W_64770.
Proof. vm_refl. Qed.
Lemma D_64770 : decode_any W_64770 = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_64774 : bv 32 := 0x00090513.
Lemma F_64774 : fetch_word AsanUbsan.M.loaded_segments (0x647c4 : word) = Some W_64774.
Proof. vm_refl. Qed.
Lemma D_64774 : decode_any W_64774 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64778 : bv 32 := 0x00048593.
Lemma F_64778 : fetch_word AsanUbsan.M.loaded_segments (0x647c8 : word) = Some W_64778.
Proof. vm_refl. Qed.
Lemma D_64778 : decode_any W_64778 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6477c : bv 32 := 0x6a1170ef.
Lemma F_6477c : fetch_word AsanUbsan.M.loaded_segments (0x647cc : word) = Some W_6477c.
Proof. vm_refl. Qed.
Lemma D_6477c : decode_any W_6477c = Some (Jal 1 97952, 4%Z).
Proof. vm_refl. Qed.

Definition W_64780 : bv 32 := 0x0a050c63.
Lemma F_64780 : fetch_word AsanUbsan.M.loaded_segments (0x647d0 : word) = Some W_64780.
Proof. vm_refl. Qed.
Lemma D_64780 : decode_any W_64780 = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_64838 : bv 32 := 0x000a8513.
Lemma F_64838 : fetch_word AsanUbsan.M.loaded_segments (0x64888 : word) = Some W_64838.
Proof. vm_refl. Qed.
Lemma D_64838 : decode_any W_64838 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6483c : bv 32 := 0xe29ff06f.
Lemma F_6483c : fetch_word AsanUbsan.M.loaded_segments (0x6488c : word) = Some W_6483c.
Proof. vm_refl. Qed.
Lemma D_6483c : decode_any W_6483c = Some (Jal 0 2096680, 4%Z).
Proof. vm_refl. Qed.
