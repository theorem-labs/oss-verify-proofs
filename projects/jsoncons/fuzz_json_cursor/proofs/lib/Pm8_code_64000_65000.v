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

Definition W_64608 : bv 32 := 0xf7010113.
Lemma F_64608 : fetch_word Asan.M.loaded_segments (0x64658 : word) = Some W_64608.
Proof. vm_refl. Qed.
Lemma D_64608 : decode_any W_64608 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_6460c : bv 32 := 0x08113423.
Lemma F_6460c : fetch_word Asan.M.loaded_segments (0x6465c : word) = Some W_6460c.
Proof. vm_refl. Qed.
Lemma D_6460c : decode_any W_6460c = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_64610 : bv 32 := 0x08813023.
Lemma F_64610 : fetch_word Asan.M.loaded_segments (0x64660 : word) = Some W_64610.
Proof. vm_refl. Qed.
Lemma D_64610 : decode_any W_64610 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_64614 : bv 32 := 0x06913c23.
Lemma F_64614 : fetch_word Asan.M.loaded_segments (0x64664 : word) = Some W_64614.
Proof. vm_refl. Qed.
Lemma D_64614 : decode_any W_64614 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_64618 : bv 32 := 0x07213823.
Lemma F_64618 : fetch_word Asan.M.loaded_segments (0x64668 : word) = Some W_64618.
Proof. vm_refl. Qed.
Lemma D_64618 : decode_any W_64618 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6461c : bv 32 := 0x07313423.
Lemma F_6461c : fetch_word Asan.M.loaded_segments (0x6466c : word) = Some W_6461c.
Proof. vm_refl. Qed.
Lemma D_6461c : decode_any W_6461c = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_64620 : bv 32 := 0x07413023.
Lemma F_64620 : fetch_word Asan.M.loaded_segments (0x64670 : word) = Some W_64620.
Proof. vm_refl. Qed.
Lemma D_64620 : decode_any W_64620 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64624 : bv 32 := 0x05513c23.
Lemma F_64624 : fetch_word Asan.M.loaded_segments (0x64674 : word) = Some W_64624.
Proof. vm_refl. Qed.
Lemma D_64624 : decode_any W_64624 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64628 : bv 32 := 0x05613823.
Lemma F_64628 : fetch_word Asan.M.loaded_segments (0x64678 : word) = Some W_64628.
Proof. vm_refl. Qed.
Lemma D_64628 : decode_any W_64628 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_6462c : bv 32 := 0x05713423.
Lemma F_6462c : fetch_word Asan.M.loaded_segments (0x6467c : word) = Some W_6462c.
Proof. vm_refl. Qed.
Lemma D_6462c : decode_any W_6462c = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_64630 : bv 32 := 0x05813023.
Lemma F_64630 : fetch_word Asan.M.loaded_segments (0x64680 : word) = Some W_64630.
Proof. vm_refl. Qed.
Lemma D_64630 : decode_any W_64630 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_64634 : bv 32 := 0x03913c23.
Lemma F_64634 : fetch_word Asan.M.loaded_segments (0x64684 : word) = Some W_64634.
Proof. vm_refl. Qed.
Lemma D_64634 : decode_any W_64634 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_64638 : bv 32 := 0x03a13823.
Lemma F_64638 : fetch_word Asan.M.loaded_segments (0x64688 : word) = Some W_64638.
Proof. vm_refl. Qed.
Lemma D_64638 : decode_any W_64638 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_6463c : bv 32 := 0x03b13423.
Lemma F_6463c : fetch_word Asan.M.loaded_segments (0x6468c : word) = Some W_6463c.
Proof. vm_refl. Qed.
Lemma D_6463c : decode_any W_6463c = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_64640 : bv 32 := 0x00058493.
Lemma F_64640 : fetch_word Asan.M.loaded_segments (0x64690 : word) = Some W_64640.
Proof. vm_refl. Qed.
Lemma D_64640 : decode_any W_64640 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64644 : bv 32 := 0x00050c93.
Lemma F_64644 : fetch_word Asan.M.loaded_segments (0x64694 : word) = Some W_64644.
Proof. vm_refl. Qed.
Lemma D_64644 : decode_any W_64644 = Some (OpImm ALU_ADD 25 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64648 : bv 32 := 0x42c260ef.
Lemma F_64648 : fetch_word Asan.M.loaded_segments (0x64698 : word) = Some W_64648.
Proof. vm_refl. Qed.
Lemma D_64648 : decode_any W_64648 = Some (Jal 1 156716, 4%Z).
Proof. vm_refl. Qed.

Definition W_6464c : bv 32 := 0x26050463.
Lemma F_6464c : fetch_word Asan.M.loaded_segments (0x6469c : word) = Some W_6464c.
Proof. vm_refl. Qed.
Lemma D_6464c : decode_any W_6464c = Some (Branch BC_EQ 10 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_64650 : bv 32 := 0x00050913.
Lemma F_64650 : fetch_word Asan.M.loaded_segments (0x646a0 : word) = Some W_64650.
Proof. vm_refl. Qed.
Lemma D_64650 : decode_any W_64650 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64654 : bv 32 := 0x5e4260ef.
Lemma F_64654 : fetch_word Asan.M.loaded_segments (0x646a4 : word) = Some W_64654.
Proof. vm_refl. Qed.
Lemma D_64654 : decode_any W_64654 = Some (Jal 1 157156, 4%Z).
Proof. vm_refl. Qed.

Definition W_64658 : bv 32 := 0x00050993.
Lemma F_64658 : fetch_word Asan.M.loaded_segments (0x646a8 : word) = Some W_64658.
Proof. vm_refl. Qed.
Lemma D_64658 : decode_any W_64658 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6465c : bv 32 := 0x00090513.
Lemma F_6465c : fetch_word Asan.M.loaded_segments (0x646ac : word) = Some W_6465c.
Proof. vm_refl. Qed.
Lemma D_6465c : decode_any W_6465c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64660 : bv 32 := 0x630260ef.
Lemma F_64660 : fetch_word Asan.M.loaded_segments (0x646b0 : word) = Some W_64660.
Proof. vm_refl. Qed.
Lemma D_64660 : decode_any W_64660 = Some (Jal 1 157232, 4%Z).
Proof. vm_refl. Qed.

Definition W_64664 : bv 32 := 0x2499e863.
Lemma F_64664 : fetch_word Asan.M.loaded_segments (0x646b4 : word) = Some W_64664.
Proof. vm_refl. Qed.
Lemma D_64664 : decode_any W_64664 = Some (Branch BC_LTU 19 9 592, 4%Z).
Proof. vm_refl. Qed.

Definition W_64668 : bv 32 := 0x00050913.
Lemma F_64668 : fetch_word Asan.M.loaded_segments (0x646b8 : word) = Some W_64668.
Proof. vm_refl. Qed.
Lemma D_64668 : decode_any W_64668 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6466c : bv 32 := 0x24a4e463.
Lemma F_6466c : fetch_word Asan.M.loaded_segments (0x646bc : word) = Some W_6466c.
Proof. vm_refl. Qed.
Lemma D_6466c : decode_any W_6466c = Some (Branch BC_LTU 9 10 584, 4%Z).
Proof. vm_refl. Qed.

Definition W_64670 : bv 32 := 0x00000d13.
Lemma F_64670 : fetch_word Asan.M.loaded_segments (0x646c0 : word) = Some W_64670.
Proof. vm_refl. Qed.
Lemma D_64670 : decode_any W_64670 = Some (OpImm ALU_ADD 26 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64674 : bv 32 := 0x00001437.
Lemma F_64674 : fetch_word Asan.M.loaded_segments (0x646c4 : word) = Some W_64674.
Proof. vm_refl. Qed.
Lemma D_64674 : decode_any W_64674 = Some (Lui 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64678 : bv 32 := 0x000ef517.
Lemma F_64678 : fetch_word Asan.M.loaded_segments (0x646c8 : word) = Some W_64678.
Proof. vm_refl. Qed.
Lemma D_64678 : decode_any W_64678 = Some (Auipc 10 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_6467c : bv 32 := 0x000ef597.
Lemma F_6467c : fetch_word Asan.M.loaded_segments (0x646cc : word) = Some W_6467c.
Proof. vm_refl. Qed.
Lemma D_6467c : decode_any W_6467c = Some (Auipc 11 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_64680 : bv 32 := 0x000ef617.
Lemma F_64680 : fetch_word Asan.M.loaded_segments (0x646d0 : word) = Some W_64680.
Proof. vm_refl. Qed.
Lemma D_64680 : decode_any W_64680 = Some (Auipc 12 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_64684 : bv 32 := 0x000ef697.
Lemma F_64684 : fetch_word Asan.M.loaded_segments (0x646d4 : word) = Some W_64684.
Proof. vm_refl. Qed.
Lemma D_64684 : decode_any W_64684 = Some (Auipc 13 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_64688 : bv 32 := 0x000ef717.
Lemma F_64688 : fetch_word Asan.M.loaded_segments (0x646d8 : word) = Some W_64688.
Proof. vm_refl. Qed.
Lemma D_64688 : decode_any W_64688 = Some (Auipc 14 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_6468c : bv 32 := 0xfffac797.
Lemma F_6468c : fetch_word Asan.M.loaded_segments (0x646dc : word) = Some W_6468c.
Proof. vm_refl. Qed.
Lemma D_6468c : decode_any W_6468c = Some (Auipc 15 1048492, 4%Z).
Proof. vm_refl. Qed.

Definition W_64690 : bv 32 := 0x008c8433.
Lemma F_64690 : fetch_word Asan.M.loaded_segments (0x646e0 : word) = Some W_64690.
Proof. vm_refl. Qed.
Lemma D_64690 : decode_any W_64690 = Some (Op ALU_ADD 8 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64694 : bv 32 := 0xa7053b03.
Lemma F_64694 : fetch_word Asan.M.loaded_segments (0x646e4 : word) = Some W_64694.
Proof. vm_refl. Qed.
Lemma D_64694 : decode_any W_64694 = Some (Load SZ8 true 22 10 2672, 4%Z).
Proof. vm_refl. Qed.

Definition W_64698 : bv 32 := 0xa745b503.
Lemma F_64698 : fetch_word Asan.M.loaded_segments (0x646e8 : word) = Some W_64698.
Proof. vm_refl. Qed.
Lemma D_64698 : decode_any W_64698 = Some (Load SZ8 true 10 11 2676, 4%Z).
Proof. vm_refl. Qed.

Definition W_6469c : bv 32 := 0x00a13c23.
Lemma F_6469c : fetch_word Asan.M.loaded_segments (0x646ec : word) = Some W_6469c.
Proof. vm_refl. Qed.
Lemma D_6469c : decode_any W_6469c = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_646a0 : bv 32 := 0xa7863503.
Lemma F_646a0 : fetch_word Asan.M.loaded_segments (0x646f0 : word) = Some W_646a0.
Proof. vm_refl. Qed.
Lemma D_646a0 : decode_any W_646a0 = Some (Load SZ8 true 10 12 2680, 4%Z).
Proof. vm_refl. Qed.

Definition W_646a4 : bv 32 := 0x00a13823.
Lemma F_646a4 : fetch_word Asan.M.loaded_segments (0x646f4 : word) = Some W_646a4.
Proof. vm_refl. Qed.
Lemma D_646a4 : decode_any W_646a4 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_646a8 : bv 32 := 0xa7c6b503.
Lemma F_646a8 : fetch_word Asan.M.loaded_segments (0x646f8 : word) = Some W_646a8.
Proof. vm_refl. Qed.
Lemma D_646a8 : decode_any W_646a8 = Some (Load SZ8 true 10 13 2684, 4%Z).
Proof. vm_refl. Qed.

Definition W_646ac : bv 32 := 0x00a13423.
Lemma F_646ac : fetch_word Asan.M.loaded_segments (0x646fc : word) = Some W_646ac.
Proof. vm_refl. Qed.
Lemma D_646ac : decode_any W_646ac = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_646b0 : bv 32 := 0xa5873503.
Lemma F_646b0 : fetch_word Asan.M.loaded_segments (0x64700 : word) = Some W_646b0.
Proof. vm_refl. Qed.
Lemma D_646b0 : decode_any W_646b0 = Some (Load SZ8 true 10 14 2648, 4%Z).
Proof. vm_refl. Qed.

Definition W_646b4 : bv 32 := 0x00a13023.
Lemma F_646b4 : fetch_word Asan.M.loaded_segments (0x64704 : word) = Some W_646b4.
Proof. vm_refl. Qed.
Lemma D_646b4 : decode_any W_646b4 = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_646b8 : bv 32 := 0xcbc7bb83.
Lemma F_646b8 : fetch_word Asan.M.loaded_segments (0x64708 : word) = Some W_646b8.
Proof. vm_refl. Qed.
Lemma D_646b8 : decode_any W_646b8 = Some (Load SZ8 true 23 15 3260, 4%Z).
Proof. vm_refl. Qed.

Definition W_646bc : bv 32 := 0x00100393.
Lemma F_646bc : fetch_word Asan.M.loaded_segments (0x6470c : word) = Some W_646bc.
Proof. vm_refl. Qed.
Lemma D_646bc : decode_any W_646bc = Some (OpImm ALU_ADD 7 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_646c0 : bv 32 := 0x00600e13.
Lemma F_646c0 : fetch_word Asan.M.loaded_segments (0x64710 : word) = Some W_646c0.
Proof. vm_refl. Qed.
Lemma D_646c0 : decode_any W_646c0 = Some (OpImm ALU_ADD 28 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_646c4 : bv 32 := 0x00000a13.
Lemma F_646c4 : fetch_word Asan.M.loaded_segments (0x64714 : word) = Some W_646c4.
Proof. vm_refl. Qed.
Lemma D_646c4 : decode_any W_646c4 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_646c8 : bv 32 := 0x0100006f.
Lemma F_646c8 : fetch_word Asan.M.loaded_segments (0x64718 : word) = Some W_646c8.
Proof. vm_refl. Qed.
Lemma D_646c8 : decode_any W_646c8 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_646cc : bv 32 := 0x001a0a13.
Lemma F_646cc : fetch_word Asan.M.loaded_segments (0x6471c : word) = Some W_646cc.
Proof. vm_refl. Qed.
Lemma D_646cc : decode_any W_646cc = Some (OpImm ALU_ADD 20 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_646d0 : bv 32 := 0x00b00513.
Lemma F_646d0 : fetch_word Asan.M.loaded_segments (0x64720 : word) = Some W_646d0.
Proof. vm_refl. Qed.
Lemma D_646d0 : decode_any W_646d0 = Some (OpImm ALU_ADD 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_646d4 : bv 32 := 0x1caa0e63.
Lemma F_646d4 : fetch_word Asan.M.loaded_segments (0x64724 : word) = Some W_646d4.
Proof. vm_refl. Qed.
Lemma D_646d4 : decode_any W_646d4 = Some (Branch BC_EQ 20 10 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_646d8 : bv 32 := 0x00000d93.
Lemma F_646d8 : fetch_word Asan.M.loaded_segments (0x64728 : word) = Some W_646d8.
Proof. vm_refl. Qed.
Lemma D_646d8 : decode_any W_646d8 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_646dc : bv 32 := 0x058cb503.
Lemma F_646dc : fetch_word Asan.M.loaded_segments (0x6472c : word) = Some W_646dc.
Proof. vm_refl. Qed.
Lemma D_646dc : decode_any W_646dc = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_646e0 : bv 32 := 0x00a00593.
Lemma F_646e0 : fetch_word Asan.M.loaded_segments (0x64730 : word) = Some W_646e0.
Proof. vm_refl. Qed.
Lemma D_646e0 : decode_any W_646e0 = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_646e4 : bv 32 := 0x414585bb.
Lemma F_646e4 : fetch_word Asan.M.loaded_segments (0x64734 : word) = Some W_646e4.
Proof. vm_refl. Qed.
Lemma D_646e4 : decode_any W_646e4 = Some (Op32 ALU_SUB 11 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_646e8 : bv 32 := 0x006a0a93.
Lemma F_646e8 : fetch_word Asan.M.loaded_segments (0x64738 : word) = Some W_646e8.
Proof. vm_refl. Qed.
Lemma D_646e8 : decode_any W_646e8 = Some (OpImm ALU_ADD 21 20 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_646ec : bv 32 := 0xfff00613.
Lemma F_646ec : fetch_word Asan.M.loaded_segments (0x6473c : word) = Some W_646ec.
Proof. vm_refl. Qed.
Lemma D_646ec : decode_any W_646ec = Some (OpImm ALU_ADD 12 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_646f0 : bv 32 := 0x00b615b3.
Lemma F_646f0 : fetch_word Asan.M.loaded_segments (0x64740 : word) = Some W_646f0.
Proof. vm_refl. Qed.
Lemma D_646f0 : decode_any W_646f0 = Some (Op ALU_SLL 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_646f4 : bv 32 := 0x3ff5f593.
Lemma F_646f4 : fetch_word Asan.M.loaded_segments (0x64744 : word) = Some W_646f4.
Proof. vm_refl. Qed.
Lemma D_646f4 : decode_any W_646f4 = Some (OpImm ALU_AND 11 11 1023, 4%Z).
Proof. vm_refl. Qed.

Definition W_646f8 : bv 32 := 0xff150613.
Lemma F_646f8 : fetch_word Asan.M.loaded_segments (0x64748 : word) = Some W_646f8.
Proof. vm_refl. Qed.
Lemma D_646f8 : decode_any W_646f8 = Some (OpImm ALU_ADD 12 10 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_646fc : bv 32 := 0x414509b3.
Lemma F_646fc : fetch_word Asan.M.loaded_segments (0x6474c : word) = Some W_646fc.
Proof. vm_refl. Qed.
Lemma D_646fc : decode_any W_646fc = Some (Op ALU_SUB 19 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_64700 : bv 32 := 0x00c59c33.
Lemma F_64700 : fetch_word Asan.M.loaded_segments (0x64750 : word) = Some W_64700.
Proof. vm_refl. Qed.
Lemma D_64700 : decode_any W_64700 = Some (Op ALU_SLL 24 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64704 : bv 32 := 0xffa98993.
Lemma F_64704 : fetch_word Asan.M.loaded_segments (0x64754 : word) = Some W_64704.
Proof. vm_refl. Qed.
Lemma D_64704 : decode_any W_64704 = Some (OpImm ALU_ADD 19 19 4090, 4%Z).
Proof. vm_refl. Qed.

Definition W_64708 : bv 32 := 0x01840c33.
Lemma F_64708 : fetch_word Asan.M.loaded_segments (0x64758 : word) = Some W_64708.
Proof. vm_refl. Qed.
Lemma D_64708 : decode_any W_64708 = Some (Op ALU_ADD 24 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6470c : bv 32 := 0x04000513.
Lemma F_6470c : fetch_word Asan.M.loaded_segments (0x6475c : word) = Some W_6470c.
Proof. vm_refl. Qed.
Lemma D_6470c : decode_any W_6470c = Some (OpImm ALU_ADD 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_64710 : bv 32 := 0x01451533.
Lemma F_64710 : fetch_word Asan.M.loaded_segments (0x64760 : word) = Some W_64710.
Proof. vm_refl. Qed.
Lemma D_64710 : decode_any W_64710 = Some (Op ALU_SLL 10 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_64714 : bv 32 := 0x02a13023.
Lemma F_64714 : fetch_word Asan.M.loaded_segments (0x64764 : word) = Some W_64714.
Proof. vm_refl. Qed.
Lemma D_64714 : decode_any W_64714 = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64718 : bv 32 := 0x0240006f.
Lemma F_64718 : fetch_word Asan.M.loaded_segments (0x64768 : word) = Some W_64718.
Proof. vm_refl. Qed.
Lemma D_64718 : decode_any W_64718 = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_64730 : bv 32 := 0x001d8d93.
Lemma F_64730 : fetch_word Asan.M.loaded_segments (0x64780 : word) = Some W_64730.
Proof. vm_refl. Qed.
Lemma D_64730 : decode_any W_64730 = Some (OpImm ALU_ADD 27 27 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64734 : bv 32 := 0x013dd533.
Lemma F_64734 : fetch_word Asan.M.loaded_segments (0x64784 : word) = Some W_64734.
Proof. vm_refl. Qed.
Lemma D_64734 : decode_any W_64734 = Some (Op ALU_SRL 10 27 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_64738 : bv 32 := 0xf8051ae3.
Lemma F_64738 : fetch_word Asan.M.loaded_segments (0x64788 : word) = Some W_64738.
Proof. vm_refl. Qed.
Lemma D_64738 : decode_any W_64738 = Some (Branch BC_NE 10 0 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_6473c : bv 32 := 0x01bc05b3.
Lemma F_6473c : fetch_word Asan.M.loaded_segments (0x6478c : word) = Some W_6473c.
Proof. vm_refl. Qed.
Lemma D_6473c : decode_any W_6473c = Some (Op ALU_ADD 11 24 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_64740 : bv 32 := 0x0005c503.
Lemma F_64740 : fetch_word Asan.M.loaded_segments (0x64790 : word) = Some W_64740.
Proof. vm_refl. Qed.
Lemma D_64740 : decode_any W_64740 = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64744 : bv 32 := 0xfe0506e3.
Lemma F_64744 : fetch_word Asan.M.loaded_segments (0x64794 : word) = Some W_64744.
Proof. vm_refl. Qed.
Lemma D_64744 : decode_any W_64744 = Some (Branch BC_EQ 10 0 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_64748 : bv 32 := 0x058cb503.
Lemma F_64748 : fetch_word Asan.M.loaded_segments (0x64798 : word) = Some W_64748.
Proof. vm_refl. Qed.
Lemma D_64748 : decode_any W_64748 = Some (Load SZ8 true 10 25 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_6474c : bv 32 := 0xffb50613.
Lemma F_6474c : fetch_word Asan.M.loaded_segments (0x6479c : word) = Some W_6474c.
Proof. vm_refl. Qed.
Lemma D_6474c : decode_any W_6474c = Some (OpImm ALU_ADD 12 10 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_64750 : bv 32 := 0x00aa1533.
Lemma F_64750 : fetch_word Asan.M.loaded_segments (0x647a0 : word) = Some W_64750.
Proof. vm_refl. Qed.
Lemma D_64750 : decode_any W_64750 = Some (Op ALU_SLL 10 20 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64754 : bv 32 := 0x00c39633.
Lemma F_64754 : fetch_word Asan.M.loaded_segments (0x647a4 : word) = Some W_64754.
Proof. vm_refl. Qed.
Lemma D_64754 : decode_any W_64754 = Some (Op ALU_SLL 12 7 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64758 : bv 32 := 0x00a40533.
Lemma F_64758 : fetch_word Asan.M.loaded_segments (0x647a8 : word) = Some W_64758.
Proof. vm_refl. Qed.
Lemma D_64758 : decode_any W_64758 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6475c : bv 32 := 0x00c50533.
Lemma F_6475c : fetch_word Asan.M.loaded_segments (0x647ac : word) = Some W_6475c.
Proof. vm_refl. Qed.
Lemma D_6475c : decode_any W_6475c = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64760 : bv 32 := 0x015d9633.
Lemma F_64760 : fetch_word Asan.M.loaded_segments (0x647b0 : word) = Some W_64760.
Proof. vm_refl. Qed.
Lemma D_64760 : decode_any W_64760 = Some (Op ALU_SLL 12 27 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_64764 : bv 32 := 0x00c50533.
Lemma F_64764 : fetch_word Asan.M.loaded_segments (0x647b4 : word) = Some W_64764.
Proof. vm_refl. Qed.
Lemma D_64764 : decode_any W_64764 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64768 : bv 32 := 0x01853603.
Lemma F_64768 : fetch_word Asan.M.loaded_segments (0x647b8 : word) = Some W_64768.
Proof. vm_refl. Qed.
Lemma D_64768 : decode_any W_64768 = Some (Load SZ8 true 12 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_6476c : bv 32 := 0xfcc972e3.
Lemma F_6476c : fetch_word Asan.M.loaded_segments (0x647bc : word) = Some W_6476c.
Proof. vm_refl. Qed.
Lemma D_6476c : decode_any W_6476c = Some (Branch BC_GEU 18 12 8132, 4%Z).
Proof. vm_refl. Qed.

Definition W_64770 : bv 32 := 0xfc9670e3.
Lemma F_64770 : fetch_word Asan.M.loaded_segments (0x647c0 : word) = Some W_64770.
Proof. vm_refl. Qed.
Lemma D_64770 : decode_any W_64770 = Some (Branch BC_GEU 12 9 8128, 4%Z).
Proof. vm_refl. Qed.

Definition W_64774 : bv 32 := 0x01a58023.
Lemma F_64774 : fetch_word Asan.M.loaded_segments (0x647c4 : word) = Some W_64774.
Proof. vm_refl. Qed.
Lemma D_64774 : decode_any W_64774 = Some (Store SZ1 11 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64778 : bv 32 := 0x000b3583.
Lemma F_64778 : fetch_word Asan.M.loaded_segments (0x647c8 : word) = Some W_64778.
Proof. vm_refl. Qed.
Lemma D_64778 : decode_any W_64778 = Some (Load SZ8 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6477c : bv 32 := 0xfff58613.
Lemma F_6477c : fetch_word Asan.M.loaded_segments (0x647cc : word) = Some W_6477c.
Proof. vm_refl. Qed.
Lemma D_6477c : decode_any W_6477c = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64780 : bv 32 := 0x00c5b6b3.
Lemma F_64780 : fetch_word Asan.M.loaded_segments (0x647d0 : word) = Some W_64780.
Proof. vm_refl. Qed.
Lemma D_64780 : decode_any W_64780 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64784 : bv 32 := 0xfff68693.
Lemma F_64784 : fetch_word Asan.M.loaded_segments (0x647d4 : word) = Some W_64784.
Proof. vm_refl. Qed.
Lemma D_64784 : decode_any W_64784 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64788 : bv 32 := 0x00c6f6b3.
Lemma F_64788 : fetch_word Asan.M.loaded_segments (0x647d8 : word) = Some W_64788.
Proof. vm_refl. Qed.
Lemma D_64788 : decode_any W_64788 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_6478c : bv 32 := 0x02a6fc63.
Lemma F_6478c : fetch_word Asan.M.loaded_segments (0x647dc : word) = Some W_6478c.
Proof. vm_refl. Qed.
Lemma D_6478c : decode_any W_6478c = Some (Branch BC_GEU 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_64790 : bv 32 := 0x01813683.
Lemma F_64790 : fetch_word Asan.M.loaded_segments (0x647e0 : word) = Some W_64790.
Proof. vm_refl. Qed.
Lemma D_64790 : decode_any W_64790 = Some (Load SZ8 true 13 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64794 : bv 32 := 0x0006b803.
Lemma F_64794 : fetch_word Asan.M.loaded_segments (0x647e4 : word) = Some W_64794.
Proof. vm_refl. Qed.
Lemma D_64794 : decode_any W_64794 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64798 : bv 32 := 0x01013683.
Lemma F_64798 : fetch_word Asan.M.loaded_segments (0x647e8 : word) = Some W_64798.
Proof. vm_refl. Qed.
Lemma D_64798 : decode_any W_64798 = Some (Load SZ8 true 13 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_6479c : bv 32 := 0x0006b683.
Lemma F_6479c : fetch_word Asan.M.loaded_segments (0x647ec : word) = Some W_6479c.
Proof. vm_refl. Qed.
Lemma D_6479c : decode_any W_6479c = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_647a0 : bv 32 := 0xfff80793.
Lemma F_647a0 : fetch_word Asan.M.loaded_segments (0x647f0 : word) = Some W_647a0.
Proof. vm_refl. Qed.
Lemma D_647a0 : decode_any W_647a0 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_647a4 : bv 32 := 0x00a7f463.
Lemma F_647a4 : fetch_word Asan.M.loaded_segments (0x647f4 : word) = Some W_647a4.
Proof. vm_refl. Qed.
Lemma D_647a4 : decode_any W_647a4 = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_647ac : bv 32 := 0x00813703.
Lemma F_647ac : fetch_word Asan.M.loaded_segments (0x647fc : word) = Some W_647ac.
Proof. vm_refl. Qed.
Lemma D_647ac : decode_any W_647ac = Some (Load SZ8 true 14 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_647b0 : bv 32 := 0x00073283.
Lemma F_647b0 : fetch_word Asan.M.loaded_segments (0x64800 : word) = Some W_647b0.
Proof. vm_refl. Qed.
Lemma D_647b0 : decode_any W_647b0 = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_647b4 : bv 32 := 0x0032d713.
Lemma F_647b4 : fetch_word Asan.M.loaded_segments (0x64804 : word) = Some W_647b4.
Proof. vm_refl. Qed.
Lemma D_647b4 : decode_any W_647b4 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_647b8 : bv 32 := 0x00b708b3.
Lemma F_647b8 : fetch_word Asan.M.loaded_segments (0x64808 : word) = Some W_647b8.
Proof. vm_refl. Qed.
Lemma D_647b8 : decode_any W_647b8 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_647bc : bv 32 := 0x02a2e863.
Lemma F_647bc : fetch_word Asan.M.loaded_segments (0x6480c : word) = Some W_647bc.
Proof. vm_refl. Qed.
Lemma D_647bc : decode_any W_647bc = Some (Branch BC_LTU 5 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_647c0 : bv 32 := 0x02a8f663.
Lemma F_647c0 : fetch_word Asan.M.loaded_segments (0x64810 : word) = Some W_647c0.
Proof. vm_refl. Qed.
Lemma D_647c0 : decode_any W_647c0 = Some (Branch BC_GEU 17 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_647c4 : bv 32 := 0xf54e6ce3.
Lemma F_647c4 : fetch_word Asan.M.loaded_segments (0x64814 : word) = Some W_647c4.
Proof. vm_refl. Qed.
Lemma D_647c4 : decode_any W_647c4 = Some (Branch BC_LTU 28 20 8024, 4%Z).
Proof. vm_refl. Qed.

Definition W_647c8 : bv 32 := 0x00355513.
Lemma F_647c8 : fetch_word Asan.M.loaded_segments (0x64818 : word) = Some W_647c8.
Proof. vm_refl. Qed.
Lemma D_647c8 : decode_any W_647c8 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_647cc : bv 32 := 0x00a585b3.
Lemma F_647cc : fetch_word Asan.M.loaded_segments (0x6481c : word) = Some W_647cc.
Proof. vm_refl. Qed.
Lemma D_647cc : decode_any W_647cc = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_647d0 : bv 32 := 0x00100513.
Lemma F_647d0 : fetch_word Asan.M.loaded_segments (0x64820 : word) = Some W_647d0.
Proof. vm_refl. Qed.
Lemma D_647d0 : decode_any W_647d0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_647d4 : bv 32 := 0x0175b023.
Lemma F_647d4 : fetch_word Asan.M.loaded_segments (0x64824 : word) = Some W_647d4.
Proof. vm_refl. Qed.
Lemma D_647d4 : decode_any W_647d4 = Some (Store SZ8 11 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_647d8 : bv 32 := 0x01455633.
Lemma F_647d8 : fetch_word Asan.M.loaded_segments (0x64828 : word) = Some W_647d8.
Proof. vm_refl. Qed.
Lemma D_647d8 : decode_any W_647d8 = Some (Op ALU_SRL 12 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_647dc : bv 32 := 0x00858593.
Lemma F_647dc : fetch_word Asan.M.loaded_segments (0x6482c : word) = Some W_647dc.
Proof. vm_refl. Qed.
Lemma D_647dc : decode_any W_647dc = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_647e0 : bv 32 := 0x00150513.
Lemma F_647e0 : fetch_word Asan.M.loaded_segments (0x64830 : word) = Some W_647e0.
Proof. vm_refl. Qed.
Lemma D_647e0 : decode_any W_647e0 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_647e4 : bv 32 := 0xfe0608e3.
Lemma F_647e4 : fetch_word Asan.M.loaded_segments (0x64834 : word) = Some W_647e4.
Proof. vm_refl. Qed.
Lemma D_647e4 : decode_any W_647e4 = Some (Branch BC_EQ 12 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_647e8 : bv 32 := 0xf49ff06f.
Lemma F_647e8 : fetch_word Asan.M.loaded_segments (0x64838 : word) = Some W_647e8.
Proof. vm_refl. Qed.
Lemma D_647e8 : decode_any W_647e8 = Some (Jal 0 2096968, 4%Z).
Proof. vm_refl. Qed.

Definition W_648b0 : bv 32 := 0x060c8023.
Lemma F_648b0 : fetch_word Asan.M.loaded_segments (0x64900 : word) = Some W_648b0.
Proof. vm_refl. Qed.
Lemma D_648b0 : decode_any W_648b0 = Some (Store SZ1 25 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_648b4 : bv 32 := 0x08813083.
Lemma F_648b4 : fetch_word Asan.M.loaded_segments (0x64904 : word) = Some W_648b4.
Proof. vm_refl. Qed.
Lemma D_648b4 : decode_any W_648b4 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_648b8 : bv 32 := 0x08013403.
Lemma F_648b8 : fetch_word Asan.M.loaded_segments (0x64908 : word) = Some W_648b8.
Proof. vm_refl. Qed.
Lemma D_648b8 : decode_any W_648b8 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_648bc : bv 32 := 0x07813483.
Lemma F_648bc : fetch_word Asan.M.loaded_segments (0x6490c : word) = Some W_648bc.
Proof. vm_refl. Qed.
Lemma D_648bc : decode_any W_648bc = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_648c0 : bv 32 := 0x07013903.
Lemma F_648c0 : fetch_word Asan.M.loaded_segments (0x64910 : word) = Some W_648c0.
Proof. vm_refl. Qed.
Lemma D_648c0 : decode_any W_648c0 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_648c4 : bv 32 := 0x06813983.
Lemma F_648c4 : fetch_word Asan.M.loaded_segments (0x64914 : word) = Some W_648c4.
Proof. vm_refl. Qed.
Lemma D_648c4 : decode_any W_648c4 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_648c8 : bv 32 := 0x06013a03.
Lemma F_648c8 : fetch_word Asan.M.loaded_segments (0x64918 : word) = Some W_648c8.
Proof. vm_refl. Qed.
Lemma D_648c8 : decode_any W_648c8 = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_648cc : bv 32 := 0x05813a83.
Lemma F_648cc : fetch_word Asan.M.loaded_segments (0x6491c : word) = Some W_648cc.
Proof. vm_refl. Qed.
Lemma D_648cc : decode_any W_648cc = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_648d0 : bv 32 := 0x05013b03.
Lemma F_648d0 : fetch_word Asan.M.loaded_segments (0x64920 : word) = Some W_648d0.
Proof. vm_refl. Qed.
Lemma D_648d0 : decode_any W_648d0 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_648d4 : bv 32 := 0x04813b83.
Lemma F_648d4 : fetch_word Asan.M.loaded_segments (0x64924 : word) = Some W_648d4.
Proof. vm_refl. Qed.
Lemma D_648d4 : decode_any W_648d4 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_648d8 : bv 32 := 0x04013c03.
Lemma F_648d8 : fetch_word Asan.M.loaded_segments (0x64928 : word) = Some W_648d8.
Proof. vm_refl. Qed.
Lemma D_648d8 : decode_any W_648d8 = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_648dc : bv 32 := 0x03813c83.
Lemma F_648dc : fetch_word Asan.M.loaded_segments (0x6492c : word) = Some W_648dc.
Proof. vm_refl. Qed.
Lemma D_648dc : decode_any W_648dc = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_648e0 : bv 32 := 0x03013d03.
Lemma F_648e0 : fetch_word Asan.M.loaded_segments (0x64930 : word) = Some W_648e0.
Proof. vm_refl. Qed.
Lemma D_648e0 : decode_any W_648e0 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_648e4 : bv 32 := 0x02813d83.
Lemma F_648e4 : fetch_word Asan.M.loaded_segments (0x64934 : word) = Some W_648e4.
Proof. vm_refl. Qed.
Lemma D_648e4 : decode_any W_648e4 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_648e8 : bv 32 := 0x09010113.
Lemma F_648e8 : fetch_word Asan.M.loaded_segments (0x64938 : word) = Some W_648e8.
Proof. vm_refl. Qed.
Lemma D_648e8 : decode_any W_648e8 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_648ec : bv 32 := 0x00008067.
Lemma F_648ec : fetch_word Asan.M.loaded_segments (0x6493c : word) = Some W_648ec.
Proof. vm_refl. Qed.
Lemma D_648ec : decode_any W_648ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_648f0 : bv 32 := 0x00100593.
Lemma F_648f0 : fetch_word Asan.M.loaded_segments (0x64940 : word) = Some W_648f0.
Proof. vm_refl. Qed.
Lemma D_648f0 : decode_any W_648f0 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_648f4 : bv 32 := 0x06b50023.
Lemma F_648f4 : fetch_word Asan.M.loaded_segments (0x64944 : word) = Some W_648f4.
Proof. vm_refl. Qed.
Lemma D_648f4 : decode_any W_648f4 = Some (Store SZ1 10 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_648f8 : bv 32 := 0x00008067.
Lemma F_648f8 : fetch_word Asan.M.loaded_segments (0x64948 : word) = Some W_648f8.
Proof. vm_refl. Qed.
Lemma D_648f8 : decode_any W_648f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a54 : bv 32 := 0xfe010113.
Lemma F_64a54 : fetch_word Asan.M.loaded_segments (0x64aa4 : word) = Some W_64a54.
Proof. vm_refl. Qed.
Lemma D_64a54 : decode_any W_64a54 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a58 : bv 32 := 0x00113c23.
Lemma F_64a58 : fetch_word Asan.M.loaded_segments (0x64aa8 : word) = Some W_64a58.
Proof. vm_refl. Qed.
Lemma D_64a58 : decode_any W_64a58 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a5c : bv 32 := 0x00813823.
Lemma F_64a5c : fetch_word Asan.M.loaded_segments (0x64aac : word) = Some W_64a5c.
Proof. vm_refl. Qed.
Lemma D_64a5c : decode_any W_64a5c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a60 : bv 32 := 0x00913423.
Lemma F_64a60 : fetch_word Asan.M.loaded_segments (0x64ab0 : word) = Some W_64a60.
Proof. vm_refl. Qed.
Lemma D_64a60 : decode_any W_64a60 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a64 : bv 32 := 0x01213023.
Lemma F_64a64 : fetch_word Asan.M.loaded_segments (0x64ab4 : word) = Some W_64a64.
Proof. vm_refl. Qed.
Lemma D_64a64 : decode_any W_64a64 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a68 : bv 32 := 0x02010413.
Lemma F_64a68 : fetch_word Asan.M.loaded_segments (0x64ab8 : word) = Some W_64a68.
Proof. vm_refl. Qed.
Lemma D_64a68 : decode_any W_64a68 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a6c : bv 32 := 0x000ef517.
Lemma F_64a6c : fetch_word Asan.M.loaded_segments (0x64abc : word) = Some W_64a6c.
Proof. vm_refl. Qed.
Lemma D_64a6c : decode_any W_64a6c = Some (Auipc 10 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a70 : bv 32 := 0x48c50513.
Lemma F_64a70 : fetch_word Asan.M.loaded_segments (0x64ac0 : word) = Some W_64a70.
Proof. vm_refl. Qed.
Lemma D_64a70 : decode_any W_64a70 = Some (OpImm ALU_ADD 10 10 1164, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a74 : bv 32 := 0x30d050ef.
Lemma F_64a74 : fetch_word Asan.M.loaded_segments (0x64ac4 : word) = Some W_64a74.
Proof. vm_refl. Qed.
Lemma D_64a74 : decode_any W_64a74 = Some (Jal 1 23308, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a78 : bv 32 := 0x00053483.
Lemma F_64a78 : fetch_word Asan.M.loaded_segments (0x64ac8 : word) = Some W_64a78.
Proof. vm_refl. Qed.
Lemma D_64a78 : decode_any W_64a78 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a7c : bv 32 := 0x08048063.
Lemma F_64a7c : fetch_word Asan.M.loaded_segments (0x64acc : word) = Some W_64a7c.
Proof. vm_refl. Qed.
Lemma D_64a7c : decode_any W_64a7c = Some (Branch BC_EQ 9 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a80 : bv 32 := 0x0604c503.
Lemma F_64a80 : fetch_word Asan.M.loaded_segments (0x64ad0 : word) = Some W_64a80.
Proof. vm_refl. Qed.
Lemma D_64a80 : decode_any W_64a80 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a84 : bv 32 := 0x0584b903.
Lemma F_64a84 : fetch_word Asan.M.loaded_segments (0x64ad4 : word) = Some W_64a84.
Proof. vm_refl. Qed.
Lemma D_64a84 : decode_any W_64a84 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a88 : bv 32 := 0x00050863.
Lemma F_64a88 : fetch_word Asan.M.loaded_segments (0x64ad8 : word) = Some W_64a88.
Proof. vm_refl. Qed.
Lemma D_64a88 : decode_any W_64a88 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a8c : bv 32 := 0x00048513.
Lemma F_64a8c : fetch_word Asan.M.loaded_segments (0x64adc : word) = Some W_64a8c.
Proof. vm_refl. Qed.
Lemma D_64a8c : decode_any W_64a8c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a90 : bv 32 := 0x00040593.
Lemma F_64a90 : fetch_word Asan.M.loaded_segments (0x64ae0 : word) = Some W_64a90.
Proof. vm_refl. Qed.
Lemma D_64a90 : decode_any W_64a90 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a94 : bv 32 := 0xb75ff0ef.
Lemma F_64a94 : fetch_word Asan.M.loaded_segments (0x64ae4 : word) = Some W_64a94.
Proof. vm_refl. Qed.
Lemma D_64a94 : decode_any W_64a94 = Some (Jal 1 2095988, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a98 : bv 32 := 0xffa90593.
Lemma F_64a98 : fetch_word Asan.M.loaded_segments (0x64ae8 : word) = Some W_64a98.
Proof. vm_refl. Qed.
Lemma D_64a98 : decode_any W_64a98 = Some (OpImm ALU_ADD 11 18 4090, 4%Z).
Proof. vm_refl. Qed.

Definition W_64a9c : bv 32 := 0x00100513.
Lemma F_64a9c : fetch_word Asan.M.loaded_segments (0x64aec : word) = Some W_64a9c.
Proof. vm_refl. Qed.
Lemma D_64a9c : decode_any W_64a9c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64aa0 : bv 32 := 0x00b51533.
Lemma F_64aa0 : fetch_word Asan.M.loaded_segments (0x64af0 : word) = Some W_64aa0.
Proof. vm_refl. Qed.
Lemma D_64aa0 : decode_any W_64aa0 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64aa4 : bv 32 := 0x0005061b.
Lemma F_64aa4 : fetch_word Asan.M.loaded_segments (0x64af4 : word) = Some W_64aa4.
Proof. vm_refl. Qed.
Lemma D_64aa4 : decode_any W_64aa4 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64aa8 : bv 32 := 0x06c05a63.
Lemma F_64aa8 : fetch_word Asan.M.loaded_segments (0x64af8 : word) = Some W_64aa8.
Proof. vm_refl. Qed.
Lemma D_64aa8 : decode_any W_64aa8 = Some (Branch BC_GE 0 12 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_64aac : bv 32 := 0x000016b7.
Lemma F_64aac : fetch_word Asan.M.loaded_segments (0x64afc : word) = Some W_64aac.
Proof. vm_refl. Qed.
Lemma D_64aac : decode_any W_64aac = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ab0 : bv 32 := 0xfff00713.
Lemma F_64ab0 : fetch_word Asan.M.loaded_segments (0x64b00 : word) = Some W_64ab0.
Proof. vm_refl. Qed.
Lemma D_64ab0 : decode_any W_64ab0 = Some (OpImm ALU_ADD 14 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ab4 : bv 32 := 0x0004b603.
Lemma F_64ab4 : fetch_word Asan.M.loaded_segments (0x64b04 : word) = Some W_64ab4.
Proof. vm_refl. Qed.
Lemma D_64ab4 : decode_any W_64ab4 = Some (Load SZ8 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ab8 : bv 32 := 0x00b71733.
Lemma F_64ab8 : fetch_word Asan.M.loaded_segments (0x64b08 : word) = Some W_64ab8.
Proof. vm_refl. Qed.
Lemma D_64ab8 : decode_any W_64ab8 = Some (Op ALU_SLL 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64abc : bv 32 := 0xfff50793.
Lemma F_64abc : fetch_word Asan.M.loaded_segments (0x64b0c : word) = Some W_64abc.
Proof. vm_refl. Qed.
Lemma D_64abc : decode_any W_64abc = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ac0 : bv 32 := 0x00d485b3.
Lemma F_64ac0 : fetch_word Asan.M.loaded_segments (0x64b10 : word) = Some W_64ac0.
Proof. vm_refl. Qed.
Lemma D_64ac0 : decode_any W_64ac0 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ac4 : bv 32 := 0xfff74693.
Lemma F_64ac4 : fetch_word Asan.M.loaded_segments (0x64b14 : word) = Some W_64ac4.
Proof. vm_refl. Qed.
Lemma D_64ac4 : decode_any W_64ac4 = Some (OpImm ALU_XOR 13 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ac8 : bv 32 := 0x02079793.
Lemma F_64ac8 : fetch_word Asan.M.loaded_segments (0x64b18 : word) = Some W_64ac8.
Proof. vm_refl. Qed.
Lemma D_64ac8 : decode_any W_64ac8 = Some (ShiftImm ALU_SLL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64acc : bv 32 := 0x0207d793.
Lemma F_64acc : fetch_word Asan.M.loaded_segments (0x64b1c : word) = Some W_64acc.
Proof. vm_refl. Qed.
Lemma D_64acc : decode_any W_64acc = Some (ShiftImm ALU_SRL 15 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ad0 : bv 32 := 0x00f60733.
Lemma F_64ad0 : fetch_word Asan.M.loaded_segments (0x64b20 : word) = Some W_64ad0.
Proof. vm_refl. Qed.
Lemma D_64ad0 : decode_any W_64ad0 = Some (Op ALU_ADD 14 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ad4 : bv 32 := 0x00170713.
Lemma F_64ad4 : fetch_word Asan.M.loaded_segments (0x64b24 : word) = Some W_64ad4.
Proof. vm_refl. Qed.
Lemma D_64ad4 : decode_any W_64ad4 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ad8 : bv 32 := 0x00d67833.
Lemma F_64ad8 : fetch_word Asan.M.loaded_segments (0x64b28 : word) = Some W_64ad8.
Proof. vm_refl. Qed.
Lemma D_64ad8 : decode_any W_64ad8 = Some (Op ALU_AND 16 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64adc : bv 32 := 0x010587b3.
Lemma F_64adc : fetch_word Asan.M.loaded_segments (0x64b2c : word) = Some W_64adc.
Proof. vm_refl. Qed.
Lemma D_64adc : decode_any W_64adc = Some (Op ALU_ADD 15 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ae0 : bv 32 := 0x0007c883.
Lemma F_64ae0 : fetch_word Asan.M.loaded_segments (0x64b30 : word) = Some W_64ae0.
Proof. vm_refl. Qed.
Lemma D_64ae0 : decode_any W_64ae0 = Some (Load SZ1 false 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ae4 : bv 32 := 0x06088663.
Lemma F_64ae4 : fetch_word Asan.M.loaded_segments (0x64b34 : word) = Some W_64ae4.
Proof. vm_refl. Qed.
Lemma D_64ae4 : decode_any W_64ae4 = Some (Branch BC_EQ 17 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ae8 : bv 32 := 0xfff5051b.
Lemma F_64ae8 : fetch_word Asan.M.loaded_segments (0x64b38 : word) = Some W_64ae8.
Proof. vm_refl. Qed.
Lemma D_64ae8 : decode_any W_64ae8 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64aec : bv 32 := 0x00160613.
Lemma F_64aec : fetch_word Asan.M.loaded_segments (0x64b3c : word) = Some W_64aec.
Proof. vm_refl. Qed.
Lemma D_64aec : decode_any W_64aec = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64af0 : bv 32 := 0xfe0514e3.
Lemma F_64af0 : fetch_word Asan.M.loaded_segments (0x64b40 : word) = Some W_64af0.
Proof. vm_refl. Qed.
Lemma D_64af0 : decode_any W_64af0 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b50 : bv 32 := 0x00160613.
Lemma F_64b50 : fetch_word Asan.M.loaded_segments (0x64ba0 : word) = Some W_64b50.
Proof. vm_refl. Qed.
Lemma D_64b50 : decode_any W_64b50 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b54 : bv 32 := 0x00100513.
Lemma F_64b54 : fetch_word Asan.M.loaded_segments (0x64ba4 : word) = Some W_64b54.
Proof. vm_refl. Qed.
Lemma D_64b54 : decode_any W_64b54 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b58 : bv 32 := 0xffb90913.
Lemma F_64b58 : fetch_word Asan.M.loaded_segments (0x64ba8 : word) = Some W_64b58.
Proof. vm_refl. Qed.
Lemma D_64b58 : decode_any W_64b58 = Some (OpImm ALU_ADD 18 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b5c : bv 32 := 0x00681813.
Lemma F_64b5c : fetch_word Asan.M.loaded_segments (0x64bac : word) = Some W_64b5c.
Proof. vm_refl. Qed.
Lemma D_64b5c : decode_any W_64b5c = Some (ShiftImm ALU_SLL 16 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b60 : bv 32 := 0x00c4b023.
Lemma F_64b60 : fetch_word Asan.M.loaded_segments (0x64bb0 : word) = Some W_64b60.
Proof. vm_refl. Qed.
Lemma D_64b60 : decode_any W_64b60 = Some (Store SZ8 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b64 : bv 32 := 0x00a78023.
Lemma F_64b64 : fetch_word Asan.M.loaded_segments (0x64bb4 : word) = Some W_64b64.
Proof. vm_refl. Qed.
Lemma D_64b64 : decode_any W_64b64 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b68 : bv 32 := 0x01251533.
Lemma F_64b68 : fetch_word Asan.M.loaded_segments (0x64bb8 : word) = Some W_64b68.
Proof. vm_refl. Qed.
Lemma D_64b68 : decode_any W_64b68 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b6c : bv 32 := 0x00a58533.
Lemma F_64b6c : fetch_word Asan.M.loaded_segments (0x64bbc : word) = Some W_64b6c.
Proof. vm_refl. Qed.
Lemma D_64b6c : decode_any W_64b6c = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b70 : bv 32 := 0x010504b3.
Lemma F_64b70 : fetch_word Asan.M.loaded_segments (0x64bc0 : word) = Some W_64b70.
Proof. vm_refl. Qed.
Lemma D_64b70 : decode_any W_64b70 = Some (Op ALU_ADD 9 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b74 : bv 32 := 0x0084bc23.
Lemma F_64b74 : fetch_word Asan.M.loaded_segments (0x64bc4 : word) = Some W_64b74.
Proof. vm_refl. Qed.
Lemma D_64b74 : decode_any W_64b74 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b78 : bv 32 := 0x02f4bc23.
Lemma F_64b78 : fetch_word Asan.M.loaded_segments (0x64bc8 : word) = Some W_64b78.
Proof. vm_refl. Qed.
Lemma D_64b78 : decode_any W_64b78 = Some (Store SZ8 9 15 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b7c : bv 32 := 0x00048513.
Lemma F_64b7c : fetch_word Asan.M.loaded_segments (0x64bcc : word) = Some W_64b7c.
Proof. vm_refl. Qed.
Lemma D_64b7c : decode_any W_64b7c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b80 : bv 32 := 0x1ad000ef.
Lemma F_64b80 : fetch_word Asan.M.loaded_segments (0x64bd0 : word) = Some W_64b80.
Proof. vm_refl. Qed.
Lemma D_64b80 : decode_any W_64b80 = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b84 : bv 32 := 0x00050593.
Lemma F_64b84 : fetch_word Asan.M.loaded_segments (0x64bd4 : word) = Some W_64b84.
Proof. vm_refl. Qed.
Lemma D_64b84 : decode_any W_64b84 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b88 : bv 32 := 0x00048513.
Lemma F_64b88 : fetch_word Asan.M.loaded_segments (0x64bd8 : word) = Some W_64b88.
Proof. vm_refl. Qed.
Lemma D_64b88 : decode_any W_64b88 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b8c : bv 32 := 0x00000613.
Lemma F_64b8c : fetch_word Asan.M.loaded_segments (0x64bdc : word) = Some W_64b8c.
Proof. vm_refl. Qed.
Lemma D_64b8c : decode_any W_64b8c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b90 : bv 32 := 0x0005b023.
Lemma F_64b90 : fetch_word Asan.M.loaded_segments (0x64be0 : word) = Some W_64b90.
Proof. vm_refl. Qed.
Lemma D_64b90 : decode_any W_64b90 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b94 : bv 32 := 0x01813083.
Lemma F_64b94 : fetch_word Asan.M.loaded_segments (0x64be4 : word) = Some W_64b94.
Proof. vm_refl. Qed.
Lemma D_64b94 : decode_any W_64b94 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b98 : bv 32 := 0x01013403.
Lemma F_64b98 : fetch_word Asan.M.loaded_segments (0x64be8 : word) = Some W_64b98.
Proof. vm_refl. Qed.
Lemma D_64b98 : decode_any W_64b98 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64b9c : bv 32 := 0x00813483.
Lemma F_64b9c : fetch_word Asan.M.loaded_segments (0x64bec : word) = Some W_64b9c.
Proof. vm_refl. Qed.
Lemma D_64b9c : decode_any W_64b9c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ba0 : bv 32 := 0x00013903.
Lemma F_64ba0 : fetch_word Asan.M.loaded_segments (0x64bf0 : word) = Some W_64ba0.
Proof. vm_refl. Qed.
Lemma D_64ba0 : decode_any W_64ba0 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ba4 : bv 32 := 0x02010113.
Lemma F_64ba4 : fetch_word Asan.M.loaded_segments (0x64bf4 : word) = Some W_64ba4.
Proof. vm_refl. Qed.
Lemma D_64ba4 : decode_any W_64ba4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ba8 : bv 32 := 0x00008067.
Lemma F_64ba8 : fetch_word Asan.M.loaded_segments (0x64bf8 : word) = Some W_64ba8.
Proof. vm_refl. Qed.
Lemma D_64ba8 : decode_any W_64ba8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bc8 : bv 32 := 0xfe010113.
Lemma F_64bc8 : fetch_word Asan.M.loaded_segments (0x64c18 : word) = Some W_64bc8.
Proof. vm_refl. Qed.
Lemma D_64bc8 : decode_any W_64bc8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bcc : bv 32 := 0x00113c23.
Lemma F_64bcc : fetch_word Asan.M.loaded_segments (0x64c1c : word) = Some W_64bcc.
Proof. vm_refl. Qed.
Lemma D_64bcc : decode_any W_64bcc = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bd0 : bv 32 := 0x00813823.
Lemma F_64bd0 : fetch_word Asan.M.loaded_segments (0x64c20 : word) = Some W_64bd0.
Proof. vm_refl. Qed.
Lemma D_64bd0 : decode_any W_64bd0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bd4 : bv 32 := 0x00913423.
Lemma F_64bd4 : fetch_word Asan.M.loaded_segments (0x64c24 : word) = Some W_64bd4.
Proof. vm_refl. Qed.
Lemma D_64bd4 : decode_any W_64bd4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bd8 : bv 32 := 0x01213023.
Lemma F_64bd8 : fetch_word Asan.M.loaded_segments (0x64c28 : word) = Some W_64bd8.
Proof. vm_refl. Qed.
Lemma D_64bd8 : decode_any W_64bd8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bdc : bv 32 := 0x02010413.
Lemma F_64bdc : fetch_word Asan.M.loaded_segments (0x64c2c : word) = Some W_64bdc.
Proof. vm_refl. Qed.
Lemma D_64bdc : decode_any W_64bdc = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64be0 : bv 32 := 0x000ef517.
Lemma F_64be0 : fetch_word Asan.M.loaded_segments (0x64c30 : word) = Some W_64be0.
Proof. vm_refl. Qed.
Lemma D_64be0 : decode_any W_64be0 = Some (Auipc 10 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_64be4 : bv 32 := 0x31850513.
Lemma F_64be4 : fetch_word Asan.M.loaded_segments (0x64c34 : word) = Some W_64be4.
Proof. vm_refl. Qed.
Lemma D_64be4 : decode_any W_64be4 = Some (OpImm ALU_ADD 10 10 792, 4%Z).
Proof. vm_refl. Qed.

Definition W_64be8 : bv 32 := 0x199050ef.
Lemma F_64be8 : fetch_word Asan.M.loaded_segments (0x64c38 : word) = Some W_64be8.
Proof. vm_refl. Qed.
Lemma D_64be8 : decode_any W_64be8 = Some (Jal 1 22936, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bec : bv 32 := 0x00053483.
Lemma F_64bec : fetch_word Asan.M.loaded_segments (0x64c3c : word) = Some W_64bec.
Proof. vm_refl. Qed.
Lemma D_64bec : decode_any W_64bec = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bf0 : bv 32 := 0x08048863.
Lemma F_64bf0 : fetch_word Asan.M.loaded_segments (0x64c40 : word) = Some W_64bf0.
Proof. vm_refl. Qed.
Lemma D_64bf0 : decode_any W_64bf0 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bf4 : bv 32 := 0x0604c503.
Lemma F_64bf4 : fetch_word Asan.M.loaded_segments (0x64c44 : word) = Some W_64bf4.
Proof. vm_refl. Qed.
Lemma D_64bf4 : decode_any W_64bf4 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bf8 : bv 32 := 0x0584b903.
Lemma F_64bf8 : fetch_word Asan.M.loaded_segments (0x64c48 : word) = Some W_64bf8.
Proof. vm_refl. Qed.
Lemma D_64bf8 : decode_any W_64bf8 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64bfc : bv 32 := 0x00050863.
Lemma F_64bfc : fetch_word Asan.M.loaded_segments (0x64c4c : word) = Some W_64bfc.
Proof. vm_refl. Qed.
Lemma D_64bfc : decode_any W_64bfc = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c00 : bv 32 := 0x00048513.
Lemma F_64c00 : fetch_word Asan.M.loaded_segments (0x64c50 : word) = Some W_64c00.
Proof. vm_refl. Qed.
Lemma D_64c00 : decode_any W_64c00 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c04 : bv 32 := 0x00040593.
Lemma F_64c04 : fetch_word Asan.M.loaded_segments (0x64c54 : word) = Some W_64c04.
Proof. vm_refl. Qed.
Lemma D_64c04 : decode_any W_64c04 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c08 : bv 32 := 0xa01ff0ef.
Lemma F_64c08 : fetch_word Asan.M.loaded_segments (0x64c58 : word) = Some W_64c08.
Proof. vm_refl. Qed.
Lemma D_64c08 : decode_any W_64c08 = Some (Jal 1 2095616, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c0c : bv 32 := 0xff990593.
Lemma F_64c0c : fetch_word Asan.M.loaded_segments (0x64c5c : word) = Some W_64c0c.
Proof. vm_refl. Qed.
Lemma D_64c0c : decode_any W_64c0c = Some (OpImm ALU_ADD 11 18 4089, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c10 : bv 32 := 0x00100513.
Lemma F_64c10 : fetch_word Asan.M.loaded_segments (0x64c60 : word) = Some W_64c10.
Proof. vm_refl. Qed.
Lemma D_64c10 : decode_any W_64c10 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c14 : bv 32 := 0x00b51533.
Lemma F_64c14 : fetch_word Asan.M.loaded_segments (0x64c64 : word) = Some W_64c14.
Proof. vm_refl. Qed.
Lemma D_64c14 : decode_any W_64c14 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c18 : bv 32 := 0x0005061b.
Lemma F_64c18 : fetch_word Asan.M.loaded_segments (0x64c68 : word) = Some W_64c18.
Proof. vm_refl. Qed.
Lemma D_64c18 : decode_any W_64c18 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c1c : bv 32 := 0x08c05263.
Lemma F_64c1c : fetch_word Asan.M.loaded_segments (0x64c6c : word) = Some W_64c1c.
Proof. vm_refl. Qed.
Lemma D_64c1c : decode_any W_64c1c = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c20 : bv 32 := 0x000016b7.
Lemma F_64c20 : fetch_word Asan.M.loaded_segments (0x64c70 : word) = Some W_64c20.
Proof. vm_refl. Qed.
Lemma D_64c20 : decode_any W_64c20 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c24 : bv 32 := 0xff190613.
Lemma F_64c24 : fetch_word Asan.M.loaded_segments (0x64c74 : word) = Some W_64c24.
Proof. vm_refl. Qed.
Lemma D_64c24 : decode_any W_64c24 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c28 : bv 32 := 0x20000713.
Lemma F_64c28 : fetch_word Asan.M.loaded_segments (0x64c78 : word) = Some W_64c28.
Proof. vm_refl. Qed.
Lemma D_64c28 : decode_any W_64c28 = Some (OpImm ALU_ADD 14 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c2c : bv 32 := 0xfff00793.
Lemma F_64c2c : fetch_word Asan.M.loaded_segments (0x64c7c : word) = Some W_64c2c.
Proof. vm_refl. Qed.
Lemma D_64c2c : decode_any W_64c2c = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c30 : bv 32 := 0x00c71733.
Lemma F_64c30 : fetch_word Asan.M.loaded_segments (0x64c80 : word) = Some W_64c30.
Proof. vm_refl. Qed.
Lemma D_64c30 : decode_any W_64c30 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c34 : bv 32 := 0x0084b603.
Lemma F_64c34 : fetch_word Asan.M.loaded_segments (0x64c84 : word) = Some W_64c34.
Proof. vm_refl. Qed.
Lemma D_64c34 : decode_any W_64c34 = Some (Load SZ8 true 12 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c38 : bv 32 := 0x00b797b3.
Lemma F_64c38 : fetch_word Asan.M.loaded_segments (0x64c88 : word) = Some W_64c38.
Proof. vm_refl. Qed.
Lemma D_64c38 : decode_any W_64c38 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c3c : bv 32 := 0xfff50813.
Lemma F_64c3c : fetch_word Asan.M.loaded_segments (0x64c8c : word) = Some W_64c3c.
Proof. vm_refl. Qed.
Lemma D_64c3c : decode_any W_64c3c = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c40 : bv 32 := 0x00d485b3.
Lemma F_64c40 : fetch_word Asan.M.loaded_segments (0x64c90 : word) = Some W_64c40.
Proof. vm_refl. Qed.
Lemma D_64c40 : decode_any W_64c40 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c44 : bv 32 := 0x00e586b3.
Lemma F_64c44 : fetch_word Asan.M.loaded_segments (0x64c94 : word) = Some W_64c44.
Proof. vm_refl. Qed.
Lemma D_64c44 : decode_any W_64c44 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c48 : bv 32 := 0xfff7c713.
Lemma F_64c48 : fetch_word Asan.M.loaded_segments (0x64c98 : word) = Some W_64c48.
Proof. vm_refl. Qed.
Lemma D_64c48 : decode_any W_64c48 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c4c : bv 32 := 0x02081813.
Lemma F_64c4c : fetch_word Asan.M.loaded_segments (0x64c9c : word) = Some W_64c4c.
Proof. vm_refl. Qed.
Lemma D_64c4c : decode_any W_64c4c = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c50 : bv 32 := 0x02085793.
Lemma F_64c50 : fetch_word Asan.M.loaded_segments (0x64ca0 : word) = Some W_64c50.
Proof. vm_refl. Qed.
Lemma D_64c50 : decode_any W_64c50 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c54 : bv 32 := 0x00f607b3.
Lemma F_64c54 : fetch_word Asan.M.loaded_segments (0x64ca4 : word) = Some W_64c54.
Proof. vm_refl. Qed.
Lemma D_64c54 : decode_any W_64c54 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c58 : bv 32 := 0x00178813.
Lemma F_64c58 : fetch_word Asan.M.loaded_segments (0x64ca8 : word) = Some W_64c58.
Proof. vm_refl. Qed.
Lemma D_64c58 : decode_any W_64c58 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c5c : bv 32 := 0x00e678b3.
Lemma F_64c5c : fetch_word Asan.M.loaded_segments (0x64cac : word) = Some W_64c5c.
Proof. vm_refl. Qed.
Lemma D_64c5c : decode_any W_64c5c = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c60 : bv 32 := 0x011687b3.
Lemma F_64c60 : fetch_word Asan.M.loaded_segments (0x64cb0 : word) = Some W_64c60.
Proof. vm_refl. Qed.
Lemma D_64c60 : decode_any W_64c60 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c64 : bv 32 := 0x0007c283.
Lemma F_64c64 : fetch_word Asan.M.loaded_segments (0x64cb4 : word) = Some W_64c64.
Proof. vm_refl. Qed.
Lemma D_64c64 : decode_any W_64c64 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c68 : bv 32 := 0x06028663.
Lemma F_64c68 : fetch_word Asan.M.loaded_segments (0x64cb8 : word) = Some W_64c68.
Proof. vm_refl. Qed.
Lemma D_64c68 : decode_any W_64c68 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c6c : bv 32 := 0xfff5051b.
Lemma F_64c6c : fetch_word Asan.M.loaded_segments (0x64cbc : word) = Some W_64c6c.
Proof. vm_refl. Qed.
Lemma D_64c6c : decode_any W_64c6c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c70 : bv 32 := 0x00160613.
Lemma F_64c70 : fetch_word Asan.M.loaded_segments (0x64cc0 : word) = Some W_64c70.
Proof. vm_refl. Qed.
Lemma D_64c70 : decode_any W_64c70 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64c74 : bv 32 := 0xfe0514e3.
Lemma F_64c74 : fetch_word Asan.M.loaded_segments (0x64cc4 : word) = Some W_64c74.
Proof. vm_refl. Qed.
Lemma D_64c74 : decode_any W_64c74 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cd4 : bv 32 := 0x00160613.
Lemma F_64cd4 : fetch_word Asan.M.loaded_segments (0x64d24 : word) = Some W_64cd4.
Proof. vm_refl. Qed.
Lemma D_64cd4 : decode_any W_64cd4 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cd8 : bv 32 := 0x00100513.
Lemma F_64cd8 : fetch_word Asan.M.loaded_segments (0x64d28 : word) = Some W_64cd8.
Proof. vm_refl. Qed.
Lemma D_64cd8 : decode_any W_64cd8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cdc : bv 32 := 0xffb90693.
Lemma F_64cdc : fetch_word Asan.M.loaded_segments (0x64d2c : word) = Some W_64cdc.
Proof. vm_refl. Qed.
Lemma D_64cdc : decode_any W_64cdc = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ce0 : bv 32 := 0x00789893.
Lemma F_64ce0 : fetch_word Asan.M.loaded_segments (0x64d30 : word) = Some W_64ce0.
Proof. vm_refl. Qed.
Lemma D_64ce0 : decode_any W_64ce0 = Some (ShiftImm ALU_SLL 17 17 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ce4 : bv 32 := 0x00c4b423.
Lemma F_64ce4 : fetch_word Asan.M.loaded_segments (0x64d34 : word) = Some W_64ce4.
Proof. vm_refl. Qed.
Lemma D_64ce4 : decode_any W_64ce4 = Some (Store SZ8 9 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ce8 : bv 32 := 0x00a78023.
Lemma F_64ce8 : fetch_word Asan.M.loaded_segments (0x64d38 : word) = Some W_64ce8.
Proof. vm_refl. Qed.
Lemma D_64ce8 : decode_any W_64ce8 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cec : bv 32 := 0x00d51633.
Lemma F_64cec : fetch_word Asan.M.loaded_segments (0x64d3c : word) = Some W_64cec.
Proof. vm_refl. Qed.
Lemma D_64cec : decode_any W_64cec = Some (Op ALU_SLL 12 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cf0 : bv 32 := 0x01251533.
Lemma F_64cf0 : fetch_word Asan.M.loaded_segments (0x64d40 : word) = Some W_64cf0.
Proof. vm_refl. Qed.
Lemma D_64cf0 : decode_any W_64cf0 = Some (Op ALU_SLL 10 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cf4 : bv 32 := 0x00c585b3.
Lemma F_64cf4 : fetch_word Asan.M.loaded_segments (0x64d44 : word) = Some W_64cf4.
Proof. vm_refl. Qed.
Lemma D_64cf4 : decode_any W_64cf4 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cf8 : bv 32 := 0x01150533.
Lemma F_64cf8 : fetch_word Asan.M.loaded_segments (0x64d48 : word) = Some W_64cf8.
Proof. vm_refl. Qed.
Lemma D_64cf8 : decode_any W_64cf8 = Some (Op ALU_ADD 10 10 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_64cfc : bv 32 := 0x00a584b3.
Lemma F_64cfc : fetch_word Asan.M.loaded_segments (0x64d4c : word) = Some W_64cfc.
Proof. vm_refl. Qed.
Lemma D_64cfc : decode_any W_64cfc = Some (Op ALU_ADD 9 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d00 : bv 32 := 0x0084bc23.
Lemma F_64d00 : fetch_word Asan.M.loaded_segments (0x64d50 : word) = Some W_64d00.
Proof. vm_refl. Qed.
Lemma D_64d00 : decode_any W_64d00 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d04 : bv 32 := 0x06f4bc23.
Lemma F_64d04 : fetch_word Asan.M.loaded_segments (0x64d54 : word) = Some W_64d04.
Proof. vm_refl. Qed.
Lemma D_64d04 : decode_any W_64d04 = Some (Store SZ8 9 15 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d08 : bv 32 := 0x00048513.
Lemma F_64d08 : fetch_word Asan.M.loaded_segments (0x64d58 : word) = Some W_64d08.
Proof. vm_refl. Qed.
Lemma D_64d08 : decode_any W_64d08 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d0c : bv 32 := 0x021000ef.
Lemma F_64d0c : fetch_word Asan.M.loaded_segments (0x64d5c : word) = Some W_64d0c.
Proof. vm_refl. Qed.
Lemma D_64d0c : decode_any W_64d0c = Some (Jal 1 2080, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d10 : bv 32 := 0x00050593.
Lemma F_64d10 : fetch_word Asan.M.loaded_segments (0x64d60 : word) = Some W_64d10.
Proof. vm_refl. Qed.
Lemma D_64d10 : decode_any W_64d10 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d14 : bv 32 := 0x00048513.
Lemma F_64d14 : fetch_word Asan.M.loaded_segments (0x64d64 : word) = Some W_64d14.
Proof. vm_refl. Qed.
Lemma D_64d14 : decode_any W_64d14 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d18 : bv 32 := 0x00000613.
Lemma F_64d18 : fetch_word Asan.M.loaded_segments (0x64d68 : word) = Some W_64d18.
Proof. vm_refl. Qed.
Lemma D_64d18 : decode_any W_64d18 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d1c : bv 32 := 0x0005b023.
Lemma F_64d1c : fetch_word Asan.M.loaded_segments (0x64d6c : word) = Some W_64d1c.
Proof. vm_refl. Qed.
Lemma D_64d1c : decode_any W_64d1c = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d20 : bv 32 := 0x0005b423.
Lemma F_64d20 : fetch_word Asan.M.loaded_segments (0x64d70 : word) = Some W_64d20.
Proof. vm_refl. Qed.
Lemma D_64d20 : decode_any W_64d20 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d24 : bv 32 := 0x01813083.
Lemma F_64d24 : fetch_word Asan.M.loaded_segments (0x64d74 : word) = Some W_64d24.
Proof. vm_refl. Qed.
Lemma D_64d24 : decode_any W_64d24 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d28 : bv 32 := 0x01013403.
Lemma F_64d28 : fetch_word Asan.M.loaded_segments (0x64d78 : word) = Some W_64d28.
Proof. vm_refl. Qed.
Lemma D_64d28 : decode_any W_64d28 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d2c : bv 32 := 0x00813483.
Lemma F_64d2c : fetch_word Asan.M.loaded_segments (0x64d7c : word) = Some W_64d2c.
Proof. vm_refl. Qed.
Lemma D_64d2c : decode_any W_64d2c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d30 : bv 32 := 0x00013903.
Lemma F_64d30 : fetch_word Asan.M.loaded_segments (0x64d80 : word) = Some W_64d30.
Proof. vm_refl. Qed.
Lemma D_64d30 : decode_any W_64d30 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d34 : bv 32 := 0x02010113.
Lemma F_64d34 : fetch_word Asan.M.loaded_segments (0x64d84 : word) = Some W_64d34.
Proof. vm_refl. Qed.
Lemma D_64d34 : decode_any W_64d34 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d38 : bv 32 := 0x00008067.
Lemma F_64d38 : fetch_word Asan.M.loaded_segments (0x64d88 : word) = Some W_64d38.
Proof. vm_refl. Qed.
Lemma D_64d38 : decode_any W_64d38 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d58 : bv 32 := 0xfe010113.
Lemma F_64d58 : fetch_word Asan.M.loaded_segments (0x64da8 : word) = Some W_64d58.
Proof. vm_refl. Qed.
Lemma D_64d58 : decode_any W_64d58 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d5c : bv 32 := 0x00113c23.
Lemma F_64d5c : fetch_word Asan.M.loaded_segments (0x64dac : word) = Some W_64d5c.
Proof. vm_refl. Qed.
Lemma D_64d5c : decode_any W_64d5c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d60 : bv 32 := 0x00813823.
Lemma F_64d60 : fetch_word Asan.M.loaded_segments (0x64db0 : word) = Some W_64d60.
Proof. vm_refl. Qed.
Lemma D_64d60 : decode_any W_64d60 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d64 : bv 32 := 0x00913423.
Lemma F_64d64 : fetch_word Asan.M.loaded_segments (0x64db4 : word) = Some W_64d64.
Proof. vm_refl. Qed.
Lemma D_64d64 : decode_any W_64d64 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d68 : bv 32 := 0x01213023.
Lemma F_64d68 : fetch_word Asan.M.loaded_segments (0x64db8 : word) = Some W_64d68.
Proof. vm_refl. Qed.
Lemma D_64d68 : decode_any W_64d68 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d6c : bv 32 := 0x02010413.
Lemma F_64d6c : fetch_word Asan.M.loaded_segments (0x64dbc : word) = Some W_64d6c.
Proof. vm_refl. Qed.
Lemma D_64d6c : decode_any W_64d6c = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d70 : bv 32 := 0x000ef517.
Lemma F_64d70 : fetch_word Asan.M.loaded_segments (0x64dc0 : word) = Some W_64d70.
Proof. vm_refl. Qed.
Lemma D_64d70 : decode_any W_64d70 = Some (Auipc 10 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d74 : bv 32 := 0x18850513.
Lemma F_64d74 : fetch_word Asan.M.loaded_segments (0x64dc4 : word) = Some W_64d74.
Proof. vm_refl. Qed.
Lemma D_64d74 : decode_any W_64d74 = Some (OpImm ALU_ADD 10 10 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d78 : bv 32 := 0x009050ef.
Lemma F_64d78 : fetch_word Asan.M.loaded_segments (0x64dc8 : word) = Some W_64d78.
Proof. vm_refl. Qed.
Lemma D_64d78 : decode_any W_64d78 = Some (Jal 1 22536, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d7c : bv 32 := 0x00053483.
Lemma F_64d7c : fetch_word Asan.M.loaded_segments (0x64dcc : word) = Some W_64d7c.
Proof. vm_refl. Qed.
Lemma D_64d7c : decode_any W_64d7c = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d80 : bv 32 := 0x08048863.
Lemma F_64d80 : fetch_word Asan.M.loaded_segments (0x64dd0 : word) = Some W_64d80.
Proof. vm_refl. Qed.
Lemma D_64d80 : decode_any W_64d80 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d84 : bv 32 := 0x0604c503.
Lemma F_64d84 : fetch_word Asan.M.loaded_segments (0x64dd4 : word) = Some W_64d84.
Proof. vm_refl. Qed.
Lemma D_64d84 : decode_any W_64d84 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d88 : bv 32 := 0x0584b903.
Lemma F_64d88 : fetch_word Asan.M.loaded_segments (0x64dd8 : word) = Some W_64d88.
Proof. vm_refl. Qed.
Lemma D_64d88 : decode_any W_64d88 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d8c : bv 32 := 0x00050863.
Lemma F_64d8c : fetch_word Asan.M.loaded_segments (0x64ddc : word) = Some W_64d8c.
Proof. vm_refl. Qed.
Lemma D_64d8c : decode_any W_64d8c = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d90 : bv 32 := 0x00048513.
Lemma F_64d90 : fetch_word Asan.M.loaded_segments (0x64de0 : word) = Some W_64d90.
Proof. vm_refl. Qed.
Lemma D_64d90 : decode_any W_64d90 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d94 : bv 32 := 0x00040593.
Lemma F_64d94 : fetch_word Asan.M.loaded_segments (0x64de4 : word) = Some W_64d94.
Proof. vm_refl. Qed.
Lemma D_64d94 : decode_any W_64d94 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d98 : bv 32 := 0x871ff0ef.
Lemma F_64d98 : fetch_word Asan.M.loaded_segments (0x64de8 : word) = Some W_64d98.
Proof. vm_refl. Qed.
Lemma D_64d98 : decode_any W_64d98 = Some (Jal 1 2095216, 4%Z).
Proof. vm_refl. Qed.

Definition W_64d9c : bv 32 := 0xff890593.
Lemma F_64d9c : fetch_word Asan.M.loaded_segments (0x64dec : word) = Some W_64d9c.
Proof. vm_refl. Qed.
Lemma D_64d9c : decode_any W_64d9c = Some (OpImm ALU_ADD 11 18 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_64da0 : bv 32 := 0x00100513.
Lemma F_64da0 : fetch_word Asan.M.loaded_segments (0x64df0 : word) = Some W_64da0.
Proof. vm_refl. Qed.
Lemma D_64da0 : decode_any W_64da0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64da4 : bv 32 := 0x00b51533.
Lemma F_64da4 : fetch_word Asan.M.loaded_segments (0x64df4 : word) = Some W_64da4.
Proof. vm_refl. Qed.
Lemma D_64da4 : decode_any W_64da4 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64da8 : bv 32 := 0x0005061b.
Lemma F_64da8 : fetch_word Asan.M.loaded_segments (0x64df8 : word) = Some W_64da8.
Proof. vm_refl. Qed.
Lemma D_64da8 : decode_any W_64da8 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dac : bv 32 := 0x08c05263.
Lemma F_64dac : fetch_word Asan.M.loaded_segments (0x64dfc : word) = Some W_64dac.
Proof. vm_refl. Qed.
Lemma D_64dac : decode_any W_64dac = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_64db0 : bv 32 := 0x000016b7.
Lemma F_64db0 : fetch_word Asan.M.loaded_segments (0x64e00 : word) = Some W_64db0.
Proof. vm_refl. Qed.
Lemma D_64db0 : decode_any W_64db0 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64db4 : bv 32 := 0xff190613.
Lemma F_64db4 : fetch_word Asan.M.loaded_segments (0x64e04 : word) = Some W_64db4.
Proof. vm_refl. Qed.
Lemma D_64db4 : decode_any W_64db4 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_64db8 : bv 32 := 0x30000713.
Lemma F_64db8 : fetch_word Asan.M.loaded_segments (0x64e08 : word) = Some W_64db8.
Proof. vm_refl. Qed.
Lemma D_64db8 : decode_any W_64db8 = Some (OpImm ALU_ADD 14 0 768, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dbc : bv 32 := 0xfff00793.
Lemma F_64dbc : fetch_word Asan.M.loaded_segments (0x64e0c : word) = Some W_64dbc.
Proof. vm_refl. Qed.
Lemma D_64dbc : decode_any W_64dbc = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dc0 : bv 32 := 0x00c71733.
Lemma F_64dc0 : fetch_word Asan.M.loaded_segments (0x64e10 : word) = Some W_64dc0.
Proof. vm_refl. Qed.
Lemma D_64dc0 : decode_any W_64dc0 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dc4 : bv 32 := 0x0104b603.
Lemma F_64dc4 : fetch_word Asan.M.loaded_segments (0x64e14 : word) = Some W_64dc4.
Proof. vm_refl. Qed.
Lemma D_64dc4 : decode_any W_64dc4 = Some (Load SZ8 true 12 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dc8 : bv 32 := 0x00b797b3.
Lemma F_64dc8 : fetch_word Asan.M.loaded_segments (0x64e18 : word) = Some W_64dc8.
Proof. vm_refl. Qed.
Lemma D_64dc8 : decode_any W_64dc8 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dcc : bv 32 := 0xfff50813.
Lemma F_64dcc : fetch_word Asan.M.loaded_segments (0x64e1c : word) = Some W_64dcc.
Proof. vm_refl. Qed.
Lemma D_64dcc : decode_any W_64dcc = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dd0 : bv 32 := 0x00d485b3.
Lemma F_64dd0 : fetch_word Asan.M.loaded_segments (0x64e20 : word) = Some W_64dd0.
Proof. vm_refl. Qed.
Lemma D_64dd0 : decode_any W_64dd0 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dd4 : bv 32 := 0x00e586b3.
Lemma F_64dd4 : fetch_word Asan.M.loaded_segments (0x64e24 : word) = Some W_64dd4.
Proof. vm_refl. Qed.
Lemma D_64dd4 : decode_any W_64dd4 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dd8 : bv 32 := 0xfff7c713.
Lemma F_64dd8 : fetch_word Asan.M.loaded_segments (0x64e28 : word) = Some W_64dd8.
Proof. vm_refl. Qed.
Lemma D_64dd8 : decode_any W_64dd8 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ddc : bv 32 := 0x02081813.
Lemma F_64ddc : fetch_word Asan.M.loaded_segments (0x64e2c : word) = Some W_64ddc.
Proof. vm_refl. Qed.
Lemma D_64ddc : decode_any W_64ddc = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64de0 : bv 32 := 0x02085793.
Lemma F_64de0 : fetch_word Asan.M.loaded_segments (0x64e30 : word) = Some W_64de0.
Proof. vm_refl. Qed.
Lemma D_64de0 : decode_any W_64de0 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64de4 : bv 32 := 0x00f607b3.
Lemma F_64de4 : fetch_word Asan.M.loaded_segments (0x64e34 : word) = Some W_64de4.
Proof. vm_refl. Qed.
Lemma D_64de4 : decode_any W_64de4 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_64de8 : bv 32 := 0x00178813.
Lemma F_64de8 : fetch_word Asan.M.loaded_segments (0x64e38 : word) = Some W_64de8.
Proof. vm_refl. Qed.
Lemma D_64de8 : decode_any W_64de8 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dec : bv 32 := 0x00e678b3.
Lemma F_64dec : fetch_word Asan.M.loaded_segments (0x64e3c : word) = Some W_64dec.
Proof. vm_refl. Qed.
Lemma D_64dec : decode_any W_64dec = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64df0 : bv 32 := 0x011687b3.
Lemma F_64df0 : fetch_word Asan.M.loaded_segments (0x64e40 : word) = Some W_64df0.
Proof. vm_refl. Qed.
Lemma D_64df0 : decode_any W_64df0 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_64df4 : bv 32 := 0x0007c283.
Lemma F_64df4 : fetch_word Asan.M.loaded_segments (0x64e44 : word) = Some W_64df4.
Proof. vm_refl. Qed.
Lemma D_64df4 : decode_any W_64df4 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64df8 : bv 32 := 0x06028663.
Lemma F_64df8 : fetch_word Asan.M.loaded_segments (0x64e48 : word) = Some W_64df8.
Proof. vm_refl. Qed.
Lemma D_64df8 : decode_any W_64df8 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_64dfc : bv 32 := 0xfff5051b.
Lemma F_64dfc : fetch_word Asan.M.loaded_segments (0x64e4c : word) = Some W_64dfc.
Proof. vm_refl. Qed.
Lemma D_64dfc : decode_any W_64dfc = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e00 : bv 32 := 0x00160613.
Lemma F_64e00 : fetch_word Asan.M.loaded_segments (0x64e50 : word) = Some W_64e00.
Proof. vm_refl. Qed.
Lemma D_64e00 : decode_any W_64e00 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e04 : bv 32 := 0xfe0514e3.
Lemma F_64e04 : fetch_word Asan.M.loaded_segments (0x64e54 : word) = Some W_64e04.
Proof. vm_refl. Qed.
Lemma D_64e04 : decode_any W_64e04 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e64 : bv 32 := 0x00160613.
Lemma F_64e64 : fetch_word Asan.M.loaded_segments (0x64eb4 : word) = Some W_64e64.
Proof. vm_refl. Qed.
Lemma D_64e64 : decode_any W_64e64 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e68 : bv 32 := 0x00100513.
Lemma F_64e68 : fetch_word Asan.M.loaded_segments (0x64eb8 : word) = Some W_64e68.
Proof. vm_refl. Qed.
Lemma D_64e68 : decode_any W_64e68 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e6c : bv 32 := 0xffb90693.
Lemma F_64e6c : fetch_word Asan.M.loaded_segments (0x64ebc : word) = Some W_64e6c.
Proof. vm_refl. Qed.
Lemma D_64e6c : decode_any W_64e6c = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e70 : bv 32 := 0x00c4b823.
Lemma F_64e70 : fetch_word Asan.M.loaded_segments (0x64ec0 : word) = Some W_64e70.
Proof. vm_refl. Qed.
Lemma D_64e70 : decode_any W_64e70 = Some (Store SZ8 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e74 : bv 32 := 0x00a78023.
Lemma F_64e74 : fetch_word Asan.M.loaded_segments (0x64ec4 : word) = Some W_64e74.
Proof. vm_refl. Qed.
Lemma D_64e74 : decode_any W_64e74 = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e78 : bv 32 := 0x00d51533.
Lemma F_64e78 : fetch_word Asan.M.loaded_segments (0x64ec8 : word) = Some W_64e78.
Proof. vm_refl. Qed.
Lemma D_64e78 : decode_any W_64e78 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e7c : bv 32 := 0x00200613.
Lemma F_64e7c : fetch_word Asan.M.loaded_segments (0x64ecc : word) = Some W_64e7c.
Proof. vm_refl. Qed.
Lemma D_64e7c : decode_any W_64e7c = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e80 : bv 32 := 0x00889893.
Lemma F_64e80 : fetch_word Asan.M.loaded_segments (0x64ed0 : word) = Some W_64e80.
Proof. vm_refl. Qed.
Lemma D_64e80 : decode_any W_64e80 = Some (ShiftImm ALU_SLL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e84 : bv 32 := 0x01261633.
Lemma F_64e84 : fetch_word Asan.M.loaded_segments (0x64ed4 : word) = Some W_64e84.
Proof. vm_refl. Qed.
Lemma D_64e84 : decode_any W_64e84 = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e88 : bv 32 := 0x00a58533.
Lemma F_64e88 : fetch_word Asan.M.loaded_segments (0x64ed8 : word) = Some W_64e88.
Proof. vm_refl. Qed.
Lemma D_64e88 : decode_any W_64e88 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e8c : bv 32 := 0x01160633.
Lemma F_64e8c : fetch_word Asan.M.loaded_segments (0x64edc : word) = Some W_64e8c.
Proof. vm_refl. Qed.
Lemma D_64e8c : decode_any W_64e8c = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e90 : bv 32 := 0x00c504b3.
Lemma F_64e90 : fetch_word Asan.M.loaded_segments (0x64ee0 : word) = Some W_64e90.
Proof. vm_refl. Qed.
Lemma D_64e90 : decode_any W_64e90 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e94 : bv 32 := 0x0084bc23.
Lemma F_64e94 : fetch_word Asan.M.loaded_segments (0x64ee4 : word) = Some W_64e94.
Proof. vm_refl. Qed.
Lemma D_64e94 : decode_any W_64e94 = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e98 : bv 32 := 0x0ef4bc23.
Lemma F_64e98 : fetch_word Asan.M.loaded_segments (0x64ee8 : word) = Some W_64e98.
Proof. vm_refl. Qed.
Lemma D_64e98 : decode_any W_64e98 = Some (Store SZ8 9 15 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_64e9c : bv 32 := 0x00048513.
Lemma F_64e9c : fetch_word Asan.M.loaded_segments (0x64eec : word) = Some W_64e9c.
Proof. vm_refl. Qed.
Lemma D_64e9c : decode_any W_64e9c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ea0 : bv 32 := 0x68c000ef.
Lemma F_64ea0 : fetch_word Asan.M.loaded_segments (0x64ef0 : word) = Some W_64ea0.
Proof. vm_refl. Qed.
Lemma D_64ea0 : decode_any W_64ea0 = Some (Jal 1 1676, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ea4 : bv 32 := 0x00050593.
Lemma F_64ea4 : fetch_word Asan.M.loaded_segments (0x64ef4 : word) = Some W_64ea4.
Proof. vm_refl. Qed.
Lemma D_64ea4 : decode_any W_64ea4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ea8 : bv 32 := 0x00048513.
Lemma F_64ea8 : fetch_word Asan.M.loaded_segments (0x64ef8 : word) = Some W_64ea8.
Proof. vm_refl. Qed.
Lemma D_64ea8 : decode_any W_64ea8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64eac : bv 32 := 0x00000613.
Lemma F_64eac : fetch_word Asan.M.loaded_segments (0x64efc : word) = Some W_64eac.
Proof. vm_refl. Qed.
Lemma D_64eac : decode_any W_64eac = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64eb0 : bv 32 := 0x0005b023.
Lemma F_64eb0 : fetch_word Asan.M.loaded_segments (0x64f00 : word) = Some W_64eb0.
Proof. vm_refl. Qed.
Lemma D_64eb0 : decode_any W_64eb0 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64eb4 : bv 32 := 0x0005b423.
Lemma F_64eb4 : fetch_word Asan.M.loaded_segments (0x64f04 : word) = Some W_64eb4.
Proof. vm_refl. Qed.
Lemma D_64eb4 : decode_any W_64eb4 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64eb8 : bv 32 := 0x0005b823.
Lemma F_64eb8 : fetch_word Asan.M.loaded_segments (0x64f08 : word) = Some W_64eb8.
Proof. vm_refl. Qed.
Lemma D_64eb8 : decode_any W_64eb8 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ebc : bv 32 := 0x0005bc23.
Lemma F_64ebc : fetch_word Asan.M.loaded_segments (0x64f0c : word) = Some W_64ebc.
Proof. vm_refl. Qed.
Lemma D_64ebc : decode_any W_64ebc = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ec0 : bv 32 := 0x01813083.
Lemma F_64ec0 : fetch_word Asan.M.loaded_segments (0x64f10 : word) = Some W_64ec0.
Proof. vm_refl. Qed.
Lemma D_64ec0 : decode_any W_64ec0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ec4 : bv 32 := 0x01013403.
Lemma F_64ec4 : fetch_word Asan.M.loaded_segments (0x64f14 : word) = Some W_64ec4.
Proof. vm_refl. Qed.
Lemma D_64ec4 : decode_any W_64ec4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ec8 : bv 32 := 0x00813483.
Lemma F_64ec8 : fetch_word Asan.M.loaded_segments (0x64f18 : word) = Some W_64ec8.
Proof. vm_refl. Qed.
Lemma D_64ec8 : decode_any W_64ec8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ecc : bv 32 := 0x00013903.
Lemma F_64ecc : fetch_word Asan.M.loaded_segments (0x64f1c : word) = Some W_64ecc.
Proof. vm_refl. Qed.
Lemma D_64ecc : decode_any W_64ecc = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ed0 : bv 32 := 0x02010113.
Lemma F_64ed0 : fetch_word Asan.M.loaded_segments (0x64f20 : word) = Some W_64ed0.
Proof. vm_refl. Qed.
Lemma D_64ed0 : decode_any W_64ed0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ed4 : bv 32 := 0x00008067.
Lemma F_64ed4 : fetch_word Asan.M.loaded_segments (0x64f24 : word) = Some W_64ed4.
Proof. vm_refl. Qed.
Lemma D_64ed4 : decode_any W_64ed4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ef4 : bv 32 := 0xfe010113.
Lemma F_64ef4 : fetch_word Asan.M.loaded_segments (0x64f44 : word) = Some W_64ef4.
Proof. vm_refl. Qed.
Lemma D_64ef4 : decode_any W_64ef4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_64ef8 : bv 32 := 0x00113c23.
Lemma F_64ef8 : fetch_word Asan.M.loaded_segments (0x64f48 : word) = Some W_64ef8.
Proof. vm_refl. Qed.
Lemma D_64ef8 : decode_any W_64ef8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64efc : bv 32 := 0x00813823.
Lemma F_64efc : fetch_word Asan.M.loaded_segments (0x64f4c : word) = Some W_64efc.
Proof. vm_refl. Qed.
Lemma D_64efc : decode_any W_64efc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f00 : bv 32 := 0x00913423.
Lemma F_64f00 : fetch_word Asan.M.loaded_segments (0x64f50 : word) = Some W_64f00.
Proof. vm_refl. Qed.
Lemma D_64f00 : decode_any W_64f00 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f04 : bv 32 := 0x01213023.
Lemma F_64f04 : fetch_word Asan.M.loaded_segments (0x64f54 : word) = Some W_64f04.
Proof. vm_refl. Qed.
Lemma D_64f04 : decode_any W_64f04 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f08 : bv 32 := 0x02010413.
Lemma F_64f08 : fetch_word Asan.M.loaded_segments (0x64f58 : word) = Some W_64f08.
Proof. vm_refl. Qed.
Lemma D_64f08 : decode_any W_64f08 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f0c : bv 32 := 0x000ef517.
Lemma F_64f0c : fetch_word Asan.M.loaded_segments (0x64f5c : word) = Some W_64f0c.
Proof. vm_refl. Qed.
Lemma D_64f0c : decode_any W_64f0c = Some (Auipc 10 239, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f10 : bv 32 := 0xfec50513.
Lemma F_64f10 : fetch_word Asan.M.loaded_segments (0x64f60 : word) = Some W_64f10.
Proof. vm_refl. Qed.
Lemma D_64f10 : decode_any W_64f10 = Some (OpImm ALU_ADD 10 10 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f14 : bv 32 := 0x66c050ef.
Lemma F_64f14 : fetch_word Asan.M.loaded_segments (0x64f64 : word) = Some W_64f14.
Proof. vm_refl. Qed.
Lemma D_64f14 : decode_any W_64f14 = Some (Jal 1 22124, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f18 : bv 32 := 0x00053483.
Lemma F_64f18 : fetch_word Asan.M.loaded_segments (0x64f68 : word) = Some W_64f18.
Proof. vm_refl. Qed.
Lemma D_64f18 : decode_any W_64f18 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f1c : bv 32 := 0x08048863.
Lemma F_64f1c : fetch_word Asan.M.loaded_segments (0x64f6c : word) = Some W_64f1c.
Proof. vm_refl. Qed.
Lemma D_64f1c : decode_any W_64f1c = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f20 : bv 32 := 0x0604c503.
Lemma F_64f20 : fetch_word Asan.M.loaded_segments (0x64f70 : word) = Some W_64f20.
Proof. vm_refl. Qed.
Lemma D_64f20 : decode_any W_64f20 = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f24 : bv 32 := 0x0584b903.
Lemma F_64f24 : fetch_word Asan.M.loaded_segments (0x64f74 : word) = Some W_64f24.
Proof. vm_refl. Qed.
Lemma D_64f24 : decode_any W_64f24 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f28 : bv 32 := 0x00050863.
Lemma F_64f28 : fetch_word Asan.M.loaded_segments (0x64f78 : word) = Some W_64f28.
Proof. vm_refl. Qed.
Lemma D_64f28 : decode_any W_64f28 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f2c : bv 32 := 0x00048513.
Lemma F_64f2c : fetch_word Asan.M.loaded_segments (0x64f7c : word) = Some W_64f2c.
Proof. vm_refl. Qed.
Lemma D_64f2c : decode_any W_64f2c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f30 : bv 32 := 0x00040593.
Lemma F_64f30 : fetch_word Asan.M.loaded_segments (0x64f80 : word) = Some W_64f30.
Proof. vm_refl. Qed.
Lemma D_64f30 : decode_any W_64f30 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f34 : bv 32 := 0xed4ff0ef.
Lemma F_64f34 : fetch_word Asan.M.loaded_segments (0x64f84 : word) = Some W_64f34.
Proof. vm_refl. Qed.
Lemma D_64f34 : decode_any W_64f34 = Some (Jal 1 2094804, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f38 : bv 32 := 0xff790593.
Lemma F_64f38 : fetch_word Asan.M.loaded_segments (0x64f88 : word) = Some W_64f38.
Proof. vm_refl. Qed.
Lemma D_64f38 : decode_any W_64f38 = Some (OpImm ALU_ADD 11 18 4087, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f3c : bv 32 := 0x00100513.
Lemma F_64f3c : fetch_word Asan.M.loaded_segments (0x64f8c : word) = Some W_64f3c.
Proof. vm_refl. Qed.
Lemma D_64f3c : decode_any W_64f3c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f40 : bv 32 := 0x00b51533.
Lemma F_64f40 : fetch_word Asan.M.loaded_segments (0x64f90 : word) = Some W_64f40.
Proof. vm_refl. Qed.
Lemma D_64f40 : decode_any W_64f40 = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f44 : bv 32 := 0x0005061b.
Lemma F_64f44 : fetch_word Asan.M.loaded_segments (0x64f94 : word) = Some W_64f44.
Proof. vm_refl. Qed.
Lemma D_64f44 : decode_any W_64f44 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f48 : bv 32 := 0x08c05263.
Lemma F_64f48 : fetch_word Asan.M.loaded_segments (0x64f98 : word) = Some W_64f48.
Proof. vm_refl. Qed.
Lemma D_64f48 : decode_any W_64f48 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f4c : bv 32 := 0x000016b7.
Lemma F_64f4c : fetch_word Asan.M.loaded_segments (0x64f9c : word) = Some W_64f4c.
Proof. vm_refl. Qed.
Lemma D_64f4c : decode_any W_64f4c = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f50 : bv 32 := 0xff190613.
Lemma F_64f50 : fetch_word Asan.M.loaded_segments (0x64fa0 : word) = Some W_64f50.
Proof. vm_refl. Qed.
Lemma D_64f50 : decode_any W_64f50 = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f54 : bv 32 := 0x38000713.
Lemma F_64f54 : fetch_word Asan.M.loaded_segments (0x64fa4 : word) = Some W_64f54.
Proof. vm_refl. Qed.
Lemma D_64f54 : decode_any W_64f54 = Some (OpImm ALU_ADD 14 0 896, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f58 : bv 32 := 0xfff00793.
Lemma F_64f58 : fetch_word Asan.M.loaded_segments (0x64fa8 : word) = Some W_64f58.
Proof. vm_refl. Qed.
Lemma D_64f58 : decode_any W_64f58 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f5c : bv 32 := 0x00c71733.
Lemma F_64f5c : fetch_word Asan.M.loaded_segments (0x64fac : word) = Some W_64f5c.
Proof. vm_refl. Qed.
Lemma D_64f5c : decode_any W_64f5c = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f60 : bv 32 := 0x0184b603.
Lemma F_64f60 : fetch_word Asan.M.loaded_segments (0x64fb0 : word) = Some W_64f60.
Proof. vm_refl. Qed.
Lemma D_64f60 : decode_any W_64f60 = Some (Load SZ8 true 12 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f64 : bv 32 := 0x00b797b3.
Lemma F_64f64 : fetch_word Asan.M.loaded_segments (0x64fb4 : word) = Some W_64f64.
Proof. vm_refl. Qed.
Lemma D_64f64 : decode_any W_64f64 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f68 : bv 32 := 0xfff50813.
Lemma F_64f68 : fetch_word Asan.M.loaded_segments (0x64fb8 : word) = Some W_64f68.
Proof. vm_refl. Qed.
Lemma D_64f68 : decode_any W_64f68 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f6c : bv 32 := 0x00d485b3.
Lemma F_64f6c : fetch_word Asan.M.loaded_segments (0x64fbc : word) = Some W_64f6c.
Proof. vm_refl. Qed.
Lemma D_64f6c : decode_any W_64f6c = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f70 : bv 32 := 0x00e586b3.
Lemma F_64f70 : fetch_word Asan.M.loaded_segments (0x64fc0 : word) = Some W_64f70.
Proof. vm_refl. Qed.
Lemma D_64f70 : decode_any W_64f70 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f74 : bv 32 := 0xfff7c713.
Lemma F_64f74 : fetch_word Asan.M.loaded_segments (0x64fc4 : word) = Some W_64f74.
Proof. vm_refl. Qed.
Lemma D_64f74 : decode_any W_64f74 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f78 : bv 32 := 0x02081813.
Lemma F_64f78 : fetch_word Asan.M.loaded_segments (0x64fc8 : word) = Some W_64f78.
Proof. vm_refl. Qed.
Lemma D_64f78 : decode_any W_64f78 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f7c : bv 32 := 0x02085793.
Lemma F_64f7c : fetch_word Asan.M.loaded_segments (0x64fcc : word) = Some W_64f7c.
Proof. vm_refl. Qed.
Lemma D_64f7c : decode_any W_64f7c = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f80 : bv 32 := 0x00f607b3.
Lemma F_64f80 : fetch_word Asan.M.loaded_segments (0x64fd0 : word) = Some W_64f80.
Proof. vm_refl. Qed.
Lemma D_64f80 : decode_any W_64f80 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f84 : bv 32 := 0x00178813.
Lemma F_64f84 : fetch_word Asan.M.loaded_segments (0x64fd4 : word) = Some W_64f84.
Proof. vm_refl. Qed.
Lemma D_64f84 : decode_any W_64f84 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f88 : bv 32 := 0x00e678b3.
Lemma F_64f88 : fetch_word Asan.M.loaded_segments (0x64fd8 : word) = Some W_64f88.
Proof. vm_refl. Qed.
Lemma D_64f88 : decode_any W_64f88 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f8c : bv 32 := 0x011687b3.
Lemma F_64f8c : fetch_word Asan.M.loaded_segments (0x64fdc : word) = Some W_64f8c.
Proof. vm_refl. Qed.
Lemma D_64f8c : decode_any W_64f8c = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f90 : bv 32 := 0x0007c283.
Lemma F_64f90 : fetch_word Asan.M.loaded_segments (0x64fe0 : word) = Some W_64f90.
Proof. vm_refl. Qed.
Lemma D_64f90 : decode_any W_64f90 = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f94 : bv 32 := 0x06028663.
Lemma F_64f94 : fetch_word Asan.M.loaded_segments (0x64fe4 : word) = Some W_64f94.
Proof. vm_refl. Qed.
Lemma D_64f94 : decode_any W_64f94 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f98 : bv 32 := 0xfff5051b.
Lemma F_64f98 : fetch_word Asan.M.loaded_segments (0x64fe8 : word) = Some W_64f98.
Proof. vm_refl. Qed.
Lemma D_64f98 : decode_any W_64f98 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_64f9c : bv 32 := 0x00160613.
Lemma F_64f9c : fetch_word Asan.M.loaded_segments (0x64fec : word) = Some W_64f9c.
Proof. vm_refl. Qed.
Lemma D_64f9c : decode_any W_64f9c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_64fa0 : bv 32 := 0xfe0514e3.
Lemma F_64fa0 : fetch_word Asan.M.loaded_segments (0x64ff0 : word) = Some W_64fa0.
Proof. vm_refl. Qed.
Lemma D_64fa0 : decode_any W_64fa0 = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

