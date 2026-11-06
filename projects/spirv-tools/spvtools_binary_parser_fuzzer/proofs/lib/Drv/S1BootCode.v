(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec StreamSim StoreOk.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6545c : bv 32 := 0xfffab197.
Lemma D_6545c : decode_any W_6545c = Some (Auipc 3 1048491, 4%Z).
Proof. vm_refl. Qed.

Definition W_65460 : bv 32 := 0x36418193.
Lemma D_65460 : decode_any W_65460 = Some (OpImm ALU_ADD 3 3 868, 4%Z).
Proof. vm_refl. Qed.

Definition W_65464 : bv 32 := 0x00010513.
Lemma D_65464 : decode_any W_65464 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65468 : bv 32 := 0xfff9b597.
Lemma D_65468 : decode_any W_65468 = Some (Auipc 11 1048475, 4%Z).
Proof. vm_refl. Qed.

Definition W_6546c : bv 32 := 0xb5858593.
Lemma D_6546c : decode_any W_6546c = Some (OpImm ALU_ADD 11 11 2904, 4%Z).
Proof. vm_refl. Qed.

Definition W_65470 : bv 32 := 0xff017113.
Lemma D_65470 : decode_any W_65470 = Some (OpImm ALU_AND 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_65474 : bv 32 := 0x0040006f.
Lemma D_65474 : decode_any W_65474 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_65478 : bv 32 := 0x00052583.
Lemma D_65478 : decode_any W_65478 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6547c : bv 32 := 0x00088617.
Lemma D_6547c : decode_any W_6547c = Some (Auipc 12 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_65480 : bv 32 := 0x00088697.
Lemma D_65480 : decode_any W_65480 = Some (Auipc 13 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_65484 : bv 32 := 0x00088717.
Lemma D_65484 : decode_any W_65484 = Some (Auipc 14 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_65488 : bv 32 := 0xa1463783.
Lemma D_65488 : decode_any W_65488 = Some (Load SZ8 true 15 12 2580, 4%Z).
Proof. vm_refl. Qed.

Definition W_6548c : bv 32 := 0xa186b683.
Lemma D_6548c : decode_any W_6548c = Some (Load SZ8 true 13 13 2584, 4%Z).
Proof. vm_refl. Qed.

Definition W_65490 : bv 32 := 0xa1c73703.
Lemma D_65490 : decode_any W_65490 = Some (Load SZ8 true 14 14 2588, 4%Z).
Proof. vm_refl. Qed.

Definition W_65494 : bv 32 := 0x00850613.
Lemma D_65494 : decode_any W_65494 = Some (OpImm ALU_ADD 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_65498 : bv 32 := 0x00078513.
Lemma D_65498 : decode_any W_65498 = Some (OpImm ALU_ADD 10 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6549c : bv 32 := 0x00000793.
Lemma D_6549c : decode_any W_6549c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_654a0 : bv 32 := 0x52c6a06f.
Lemma D_654a0 : decode_any W_654a0 = Some (Jal 0 435500, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf750 : bv 32 := 0x00008067.
Lemma D_cf750 : decode_any W_cf750 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf754 : bv 32 := 0xe8010113.
Lemma D_cf754 : decode_any W_cf754 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf758 : bv 32 := 0x16113c23.
Lemma D_cf758 : decode_any W_cf758 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf75c : bv 32 := 0x16813823.
Lemma D_cf75c : decode_any W_cf75c = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf760 : bv 32 := 0x16913423.
Lemma D_cf760 : decode_any W_cf760 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf764 : bv 32 := 0x17213023.
Lemma D_cf764 : decode_any W_cf764 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf768 : bv 32 := 0x00058413.
Lemma D_cf768 : decode_any W_cf768 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf76c : bv 32 := 0x00050493.
Lemma D_cf76c : decode_any W_cf76c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf770 : bv 32 := 0x03010513.
Lemma D_cf770 : decode_any W_cf770 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf774 : bv 32 := 0x13000613.
Lemma D_cf774 : decode_any W_cf774 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf778 : bv 32 := 0x00000593.
Lemma D_cf778 : decode_any W_cf778 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf77c : bv 32 := 0x409110ef.
Lemma D_cf77c : decode_any W_cf77c = Some (Jal 1 72712, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf780 : bv 32 := 0x0001e517.
Lemma D_cf780 : decode_any W_cf780 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf784 : bv 32 := 0x8d053503.
Lemma D_cf784 : decode_any W_cf784 = Some (Load SZ8 true 10 10 2256, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf788 : bv 32 := 0x00953023.
Lemma D_cf788 : decode_any W_cf788 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf78c : bv 32 := 0x0004b503.
Lemma D_cf78c : decode_any W_cf78c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf790 : bv 32 := 0x00848493.
Lemma D_cf790 : decode_any W_cf790 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf794 : bv 32 := 0xfe051ce3.
Lemma D_cf794 : decode_any W_cf794 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf798 : bv 32 := 0x00051517.
Lemma D_cf798 : decode_any W_cf798 = Some (Auipc 10 81, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf79c : bv 32 := 0x17050913.
Lemma D_cf79c : decode_any W_cf79c = Some (OpImm ALU_ADD 18 10 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7a0 : bv 32 := 0x00993423.
Lemma D_cf7a0 : decode_any W_cf7a0 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7a4 : bv 32 := 0x0004b583.
Lemma D_cf7a4 : decode_any W_cf7a4 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7a8 : bv 32 := 0x04058c63.
Lemma D_cf7a8 : decode_any W_cf7a8 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7ac : bv 32 := 0x01048493.
Lemma D_cf7ac : decode_any W_cf7ac = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7b0 : bv 32 := 0x02500513.
Lemma D_cf7b0 : decode_any W_cf7b0 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7b4 : bv 32 := 0x03010613.
Lemma D_cf7b4 : decode_any W_cf7b4 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7b8 : bv 32 := 0x0100006f.
Lemma D_cf7b8 : decode_any W_cf7b8 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7bc : bv 32 := 0x0004b583.
Lemma D_cf7bc : decode_any W_cf7bc = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7c0 : bv 32 := 0x01048493.
Lemma D_cf7c0 : decode_any W_cf7c0 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7c4 : bv 32 := 0x00058e63.
Lemma D_cf7c4 : decode_any W_cf7c4 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7c8 : bv 32 := 0xfeb56ae3.
Lemma D_cf7c8 : decode_any W_cf7c8 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7cc : bv 32 := 0xff84b683.
Lemma D_cf7cc : decode_any W_cf7cc = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7d0 : bv 32 := 0x00359593.
Lemma D_cf7d0 : decode_any W_cf7d0 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7d4 : bv 32 := 0x00b605b3.
Lemma D_cf7d4 : decode_any W_cf7d4 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7d8 : bv 32 := 0x00d5b023.
Lemma D_cf7d8 : decode_any W_cf7d8 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7dc : bv 32 := 0xfe1ff06f.
Lemma D_cf7dc : decode_any W_cf7dc = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7e0 : bv 32 := 0x0b013583.
Lemma D_cf7e0 : decode_any W_cf7e0 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7e4 : bv 32 := 0x13013503.
Lemma D_cf7e4 : decode_any W_cf7e4 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7e8 : bv 32 := 0x00051617.
Lemma D_cf7e8 : decode_any W_cf7e8 = Some (Auipc 12 81, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7ec : bv 32 := 0x18b63423.
Lemma D_cf7ec : decode_any W_cf7ec = Some (Store SZ8 12 11 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf7f0 : bv 32 := 0x00050c63.
Lemma D_cf7f0 : decode_any W_cf7f0 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf808 : bv 32 := 0x06013503.
Lemma D_cf808 : decode_any W_cf808 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf80c : bv 32 := 0x02a93823.
Lemma D_cf80c : decode_any W_cf80c = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf810 : bv 32 := 0x00041463.
Lemma D_cf810 : decode_any W_cf810 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf818 : bv 32 := 0x00041663.
Lemma D_cf818 : decode_any W_cf818 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf824 : bv 32 := 0x0001e517.
Lemma D_cf824 : decode_any W_cf824 = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf828 : bv 32 := 0x83453583.
Lemma D_cf828 : decode_any W_cf828 = Some (Load SZ8 true 11 10 2100, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf82c : bv 32 := 0x0001e517.
Lemma D_cf82c : decode_any W_cf82c = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf830 : bv 32 := 0x83453503.
Lemma D_cf830 : decode_any W_cf830 = Some (Load SZ8 true 10 10 2100, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf834 : bv 32 := 0x0085b023.
Lemma D_cf834 : decode_any W_cf834 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf838 : bv 32 := 0x00140593.
Lemma D_cf838 : decode_any W_cf838 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf83c : bv 32 := 0x00853023.
Lemma D_cf83c : decode_any W_cf83c = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf840 : bv 32 := 0x02f00613.
Lemma D_cf840 : decode_any W_cf840 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf844 : bv 32 := 0x00c0006f.
Lemma D_cf844 : decode_any W_cf844 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf848 : bv 32 := 0x00b53023.
Lemma D_cf848 : decode_any W_cf848 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf84c : bv 32 := 0x00158593.
Lemma D_cf84c : decode_any W_cf84c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf850 : bv 32 := 0xfff5c683.
Lemma D_cf850 : decode_any W_cf850 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf854 : bv 32 := 0xfec68ae3.
Lemma D_cf854 : decode_any W_cf854 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf858 : bv 32 := 0xfe069ae3.
Lemma D_cf858 : decode_any W_cf858 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf85c : bv 32 := 0x03010513.
Lemma D_cf85c : decode_any W_cf85c = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf860 : bv 32 := 0x214000ef.
Lemma D_cf860 : decode_any W_cf860 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf864 : bv 32 := 0x0f813503.
Lemma D_cf864 : decode_any W_cf864 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf868 : bv 32 := 0x1ad000ef.
Lemma D_cf868 : decode_any W_cf868 = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf86c : bv 32 := 0x08813503.
Lemma D_cf86c : decode_any W_cf86c = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf870 : bv 32 := 0x09013583.
Lemma D_cf870 : decode_any W_cf870 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf874 : bv 32 := 0x00b51c63.
Lemma D_cf874 : decode_any W_cf874 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf878 : bv 32 := 0x09813503.
Lemma D_cf878 : decode_any W_cf878 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf87c : bv 32 := 0x0a013583.
Lemma D_cf87c : decode_any W_cf87c = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf880 : bv 32 := 0x00b51663.
Lemma D_cf880 : decode_any W_cf880 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf884 : bv 32 := 0x0e813503.
Lemma D_cf884 : decode_any W_cf884 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf888 : bv 32 := 0x0e050063.
Lemma D_cf888 : decode_any W_cf888 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf968 : bv 32 := 0x17813083.
Lemma D_cf968 : decode_any W_cf968 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf96c : bv 32 := 0x17013403.
Lemma D_cf96c : decode_any W_cf96c = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf970 : bv 32 := 0x16813483.
Lemma D_cf970 : decode_any W_cf970 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf974 : bv 32 := 0x16013903.
Lemma D_cf974 : decode_any W_cf974 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf978 : bv 32 := 0x18010113.
Lemma D_cf978 : decode_any W_cf978 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf97c : bv 32 := 0x00008067.
Lemma D_cf97c : decode_any W_cf97c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf980 : bv 32 := 0xfe010113.
Lemma D_cf980 : decode_any W_cf980 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf984 : bv 32 := 0x00113c23.
Lemma D_cf984 : decode_any W_cf984 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf988 : bv 32 := 0x00813823.
Lemma D_cf988 : decode_any W_cf988 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf98c : bv 32 := 0x00913423.
Lemma D_cf98c : decode_any W_cf98c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf990 : bv 32 := 0xdc1ff0ef.
Lemma D_cf990 : decode_any W_cf990 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf994 : bv 32 := 0x0001d517.
Lemma D_cf994 : decode_any W_cf994 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf998 : bv 32 := 0x0001d597.
Lemma D_cf998 : decode_any W_cf998 = Some (Auipc 11 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf99c : bv 32 := 0x6d453403.
Lemma D_cf99c : decode_any W_cf99c = Some (Load SZ8 true 8 10 1748, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9a0 : bv 32 := 0x6d85b483.
Lemma D_cf9a0 : decode_any W_cf9a0 = Some (Load SZ8 true 9 11 1752, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9a4 : bv 32 := 0x0084fa63.
Lemma D_cf9a4 : decode_any W_cf9a4 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9a8 : bv 32 := 0x0004b503.
Lemma D_cf9a8 : decode_any W_cf9a8 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9ac : bv 32 := 0x000500e7.
Lemma D_cf9ac : decode_any W_cf9ac = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9b0 : bv 32 := 0x00848493.

Definition W_cf9b4 : bv 32 := 0xfe84eae3.

Definition W_cf9b8 : bv 32 := 0x01813083.

Definition W_cf9bc : bv 32 := 0x01013403.

Definition W_cf9c0 : bv 32 := 0x00813483.

Definition W_cf9c4 : bv 32 := 0x02010113.

Definition W_cf9c8 : bv 32 := 0x00008067.

Definition W_cf9cc : bv 32 := 0xfe010113.
Lemma D_cf9cc : decode_any W_cf9cc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9d0 : bv 32 := 0x00113c23.
Lemma D_cf9d0 : decode_any W_cf9d0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9d4 : bv 32 := 0x00813823.
Lemma D_cf9d4 : decode_any W_cf9d4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9d8 : bv 32 := 0x00913423.
Lemma D_cf9d8 : decode_any W_cf9d8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9dc : bv 32 := 0x01213023.
Lemma D_cf9dc : decode_any W_cf9dc = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9e0 : bv 32 := 0x00060413.
Lemma D_cf9e0 : decode_any W_cf9e0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9e4 : bv 32 := 0x00058493.
Lemma D_cf9e4 : decode_any W_cf9e4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9e8 : bv 32 := 0x00050913.
Lemma D_cf9e8 : decode_any W_cf9e8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9ec : bv 32 := 0x00063583.
Lemma D_cf9ec : decode_any W_cf9ec = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9f0 : bv 32 := 0x00349513.
Lemma D_cf9f0 : decode_any W_cf9f0 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9f4 : bv 32 := 0x00a60533.
Lemma D_cf9f4 : decode_any W_cf9f4 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9f8 : bv 32 := 0x00850513.
Lemma D_cf9f8 : decode_any W_cf9f8 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cf9fc : bv 32 := 0xd59ff0ef.
Lemma D_cf9fc : decode_any W_cf9fc = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa00 : bv 32 := 0x00000517.
Lemma D_cfa00 : decode_any W_cfa00 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa04 : bv 32 := 0x02c50313.
Lemma D_cfa04 : decode_any W_cfa04 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa08 : bv 32 := 0x00090513.
Lemma D_cfa08 : decode_any W_cfa08 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa0c : bv 32 := 0x00048593.
Lemma D_cfa0c : decode_any W_cfa0c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa10 : bv 32 := 0x00040613.
Lemma D_cfa10 : decode_any W_cfa10 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa14 : bv 32 := 0x01813083.
Lemma D_cfa14 : decode_any W_cfa14 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa18 : bv 32 := 0x01013403.
Lemma D_cfa18 : decode_any W_cfa18 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa1c : bv 32 := 0x00813483.
Lemma D_cfa1c : decode_any W_cfa1c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa20 : bv 32 := 0x00013903.
Lemma D_cfa20 : decode_any W_cfa20 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa24 : bv 32 := 0x02010113.
Lemma D_cfa24 : decode_any W_cfa24 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa28 : bv 32 := 0x00030067.
Lemma D_cfa28 : decode_any W_cfa28 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa2c : bv 32 := 0xfd010113.
Lemma D_cfa2c : decode_any W_cfa2c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa30 : bv 32 := 0x02113423.
Lemma D_cfa30 : decode_any W_cfa30 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa34 : bv 32 := 0x02813023.
Lemma D_cfa34 : decode_any W_cfa34 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa38 : bv 32 := 0x00913c23.
Lemma D_cfa38 : decode_any W_cfa38 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa3c : bv 32 := 0x01213823.
Lemma D_cfa3c : decode_any W_cfa3c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa40 : bv 32 := 0x01313423.
Lemma D_cfa40 : decode_any W_cfa40 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa44 : bv 32 := 0x00060413.
Lemma D_cfa44 : decode_any W_cfa44 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa48 : bv 32 := 0x00058493.
Lemma D_cfa48 : decode_any W_cfa48 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa4c : bv 32 := 0x00050913.
Lemma D_cfa4c : decode_any W_cfa4c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa50 : bv 32 := 0x00359513.
Lemma D_cfa50 : decode_any W_cfa50 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa54 : bv 32 := 0x00a60533.
Lemma D_cfa54 : decode_any W_cfa54 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa58 : bv 32 := 0x00850993.
Lemma D_cfa58 : decode_any W_cfa58 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa5c : bv 32 := 0xf25ff0ef.
Lemma D_cfa5c : decode_any W_cfa5c = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfa60 : bv 32 := 0x00048513.

Definition W_cfa64 : bv 32 := 0x00040593.

Definition W_cfa68 : bv 32 := 0x00098613.

Definition W_cfa6c : bv 32 := 0x000900e7.

Definition W_cfab4 : bv 32 := 0xfc010113.
Lemma D_cfab4 : decode_any W_cfab4 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfab8 : bv 32 := 0x02113c23.
Lemma D_cfab8 : decode_any W_cfab8 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfabc : bv 32 := 0x02813823.
Lemma D_cfabc : decode_any W_cfabc = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfac0 : bv 32 := 0x02913423.
Lemma D_cfac0 : decode_any W_cfac0 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfac4 : bv 32 := 0x03213023.
Lemma D_cfac4 : decode_any W_cfac4 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfac8 : bv 32 := 0x01313c23.
Lemma D_cfac8 : decode_any W_cfac8 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfacc : bv 32 := 0x01413823.
Lemma D_cfacc : decode_any W_cfacc = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfad0 : bv 32 := 0x01513423.
Lemma D_cfad0 : decode_any W_cfad0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfad4 : bv 32 := 0x02853683.
Lemma D_cfad4 : decode_any W_cfad4 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfad8 : bv 32 := 0x00051597.
Lemma D_cfad8 : decode_any W_cfad8 = Some (Auipc 11 81, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfadc : bv 32 := 0xbe858593.
Lemma D_cfadc : decode_any W_cfadc = Some (OpImm ALU_ADD 11 11 3048, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfae0 : bv 32 := 0x00051617.
Lemma D_cfae0 : decode_any W_cfae0 = Some (Auipc 12 81, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfae4 : bv 32 := 0xe6860493.
Lemma D_cfae4 : decode_any W_cfae4 = Some (OpImm ALU_ADD 9 12 3688, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfae8 : bv 32 := 0x0c068e63.
Lemma D_cfae8 : decode_any W_cfae8 = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfaec : bv 32 := 0x00000613.
Lemma D_cfaec : decode_any W_cfaec = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfaf0 : bv 32 := 0x00000893.
Lemma D_cfaf0 : decode_any W_cfaf0 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfaf4 : bv 32 := 0x0001f717.
Lemma D_cfaf4 : decode_any W_cfaf4 = Some (Auipc 14 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfaf8 : bv 32 := 0x01853783.
Lemma D_cfaf8 : decode_any W_cfaf8 = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfafc : bv 32 := 0x02053503.
Lemma D_cfafc : decode_any W_cfafc = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb00 : bv 32 := 0x00600813.
Lemma D_cfb00 : decode_any W_cfb00 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb04 : bv 32 := 0x0001d297.
Lemma D_cfb04 : decode_any W_cfb04 = Some (Auipc 5 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb08 : bv 32 := 0x98c76f03.
Lemma D_cfb08 : decode_any W_cfb08 = Some (Load SZ4 false 30 14 2444, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb0c : bv 32 := 0x3c42b283.
Lemma D_cfb0c : decode_any W_cfb0c = Some (Load SZ8 true 5 5 964, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb10 : bv 32 := 0x00200313.
Lemma D_cfb10 : decode_any W_cfb10 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb14 : bv 32 := 0x00700393.
Lemma D_cfb14 : decode_any W_cfb14 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb18 : bv 32 := 0x6474ee37.
Lemma D_cfb18 : decode_any W_cfb18 = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb1c : bv 32 := 0x551e0e1b.
Lemma D_cfb1c : decode_any W_cfb1c = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb20 : bv 32 := 0x00078e93.
Lemma D_cfb20 : decode_any W_cfb20 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb24 : bv 32 := 0x0180006f.
Lemma D_cfb24 : decode_any W_cfb24 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb28 : bv 32 := 0x010eb603.
Lemma D_cfb28 : decode_any W_cfb28 = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb2c : bv 32 := 0x40c78633.
Lemma D_cfb2c : decode_any W_cfb2c = Some (Op ALU_SUB 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb30 : bv 32 := 0xfff68693.
Lemma D_cfb30 : decode_any W_cfb30 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb34 : bv 32 := 0x00ae8eb3.
Lemma D_cfb34 : decode_any W_cfb34 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb38 : bv 32 := 0x04068a63.
Lemma D_cfb38 : decode_any W_cfb38 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb3c : bv 32 := 0x000ea403.
Lemma D_cfb3c : decode_any W_cfb3c = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb40 : bv 32 := 0xff0404e3.
Lemma D_cfb40 : decode_any W_cfb40 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb44 : bv 32 := 0x00028a63.
Lemma D_cfb44 : decode_any W_cfb44 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb58 : bv 32 := 0x000e8f93.
Lemma D_cfb58 : decode_any W_cfb58 = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb5c : bv 32 := 0x00740463.
Lemma D_cfb5c : decode_any W_cfb5c = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb60 : bv 32 := 0x00088f93.
Lemma D_cfb60 : decode_any W_cfb60 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb64 : bv 32 := 0x03c41063.
Lemma D_cfb64 : decode_any W_cfb64 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb68 : bv 32 := 0x028eb883.
Lemma D_cfb68 : decode_any W_cfb68 = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb6c : bv 32 := 0x011f7c63.
Lemma D_cfb6c : decode_any W_cfb6c = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb84 : bv 32 := 0x000f8893.
Lemma D_cfb84 : decode_any W_cfb84 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb88 : bv 32 := 0xfa9ff06f.
Lemma D_cfb88 : decode_any W_cfb88 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfb8c : bv 32 := 0x02088c63.
Lemma D_cfb8c : decode_any W_cfb8c = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbc4 : bv 32 := 0x0105b603.
Lemma D_cfbc4 : decode_any W_cfbc4 = Some (Load SZ8 true 12 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbc8 : bv 32 := 0x0205b683.
Lemma D_cfbc8 : decode_any W_cfbc8 = Some (Load SZ8 true 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbcc : bv 32 := 0x0285b503.
Lemma D_cfbcc : decode_any W_cfbcc = Some (Load SZ8 true 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbd0 : bv 32 := 0x00c68733.
Lemma D_cfbd0 : decode_any W_cfbd0 = Some (Op ALU_ADD 14 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbd4 : bv 32 := 0xfff50793.
Lemma D_cfbd4 : decode_any W_cfbd4 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbd8 : bv 32 := 0x40e00733.
Lemma D_cfbd8 : decode_any W_cfbd8 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbdc : bv 32 := 0x00c7f633.
Lemma D_cfbdc : decode_any W_cfbdc = Some (Op ALU_AND 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbe0 : bv 32 := 0x00e7f733.
Lemma D_cfbe0 : decode_any W_cfbe0 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbe4 : bv 32 := 0x00700793.
Lemma D_cfbe4 : decode_any W_cfbe4 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbe8 : bv 32 := 0x00d706b3.
Lemma D_cfbe8 : decode_any W_cfbe8 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbec : bv 32 := 0x02d5b023.
Lemma D_cfbec : decode_any W_cfbec = Some (Store SZ8 11 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbf0 : bv 32 := 0x02c5b823.
Lemma D_cfbf0 : decode_any W_cfbf0 = Some (Store SZ8 11 12 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbf4 : bv 32 := 0x00a7e663.
Lemma D_cfbf4 : decode_any W_cfbf4 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbf8 : bv 32 := 0x00800513.
Lemma D_cfbf8 : decode_any W_cfbf8 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfbfc : bv 32 := 0x02a5b423.
Lemma D_cfbfc : decode_any W_cfbfc = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc00 : bv 32 := 0x00d60633.
Lemma D_cfc00 : decode_any W_cfc00 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc04 : bv 32 := 0x000205b7.
Lemma D_cfc04 : decode_any W_cfc04 = Some (Lui 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc08 : bv 32 := 0x00a60633.
Lemma D_cfc08 : decode_any W_cfc08 = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc0c : bv 32 := 0x0d15869b.
Lemma D_cfc0c : decode_any W_cfc0c = Some (OpImm32 13 11 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc10 : bv 32 := 0x0df60593.
Lemma D_cfc10 : decode_any W_cfc10 = Some (OpImm ALU_ADD 11 12 223, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc14 : bv 32 := 0xff85f593.
Lemma D_cfc14 : decode_any W_cfc14 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc18 : bv 32 := 0x00b4bc23.
Lemma D_cfc18 : decode_any W_cfc18 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc1c : bv 32 := 0x02a4b023.
Lemma D_cfc1c : decode_any W_cfc1c = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc20 : bv 32 := 0x02d5ea63.
Lemma D_cfc20 : decode_any W_cfc20 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc54 : bv 32 := 0x00031697.
Lemma D_cfc54 : decode_any W_cfc54 = Some (Auipc 13 49, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc58 : bv 32 := 0x0104b983.
Lemma D_cfc58 : decode_any W_cfc58 = Some (Load SZ8 true 19 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc5c : bv 32 := 0x0284b603.
Lemma D_cfc5c : decode_any W_cfc5c = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc60 : bv 32 := 0xfff50713.
Lemma D_cfc60 : decode_any W_cfc60 = Some (OpImm ALU_ADD 14 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc64 : bv 32 := 0xf3800793.
Lemma D_cfc64 : decode_any W_cfc64 = Some (OpImm ALU_ADD 15 0 3896, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc68 : bv 32 := 0x99c68513.
Lemma D_cfc68 : decode_any W_cfc68 = Some (OpImm ALU_ADD 10 13 2460, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc6c : bv 32 := 0x40a787b3.
Lemma D_cfc6c : decode_any W_cfc6c = Some (Op ALU_SUB 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc70 : bv 32 := 0x00f77733.
Lemma D_cfc70 : decode_any W_cfc70 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc74 : bv 32 := 0xfff64693.
Lemma D_cfc74 : decode_any W_cfc74 = Some (OpImm ALU_XOR 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc78 : bv 32 := 0x00e50933.
Lemma D_cfc78 : decode_any W_cfc78 = Some (Op ALU_ADD 18 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc7c : bv 32 := 0x00369693.
Lemma D_cfc7c : decode_any W_cfc7c = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc80 : bv 32 := 0x00d506b3.
Lemma D_cfc80 : decode_any W_cfc80 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc84 : bv 32 := 0x00b68a33.
Lemma D_cfc84 : decode_any W_cfc84 = Some (Op ALU_ADD 20 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc88 : bv 32 := 0x0c890413.
Lemma D_cfc88 : decode_any W_cfc88 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfc8c : bv 32 := 0x04098463.
Lemma D_cfc8c : decode_any W_cfc8c = Some (Branch BC_EQ 19 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfcd4 : bv 32 := 0x00ca3023.
Lemma D_cfcd4 : decode_any W_cfcd4 = Some (Store SZ8 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfcd8 : bv 32 := 0x0d493023.
Lemma D_cfcd8 : decode_any W_cfcd8 = Some (Store SZ8 18 20 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfcdc : bv 32 := 0x01293023.
Lemma D_cfcdc : decode_any W_cfcdc = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfce0 : bv 32 := 0x00040513.
Lemma D_cfce0 : decode_any W_cfce0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfce4 : bv 32 := 0x081130ef.
Lemma D_cfce4 : decode_any W_cfce4 = Some (Jal 1 80000, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfce8 : bv 32 := 0x04054a63.
Lemma D_cfce8 : decode_any W_cfce8 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfcec : bv 32 := 0x00051663.
Lemma D_cfcec : decode_any W_cfcec = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfcf0 : bv 32 := 0x00100513.
Lemma D_cfcf0 : decode_any W_cfcf0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfcf4 : bv 32 := 0x00a48023.
Lemma D_cfcf4 : decode_any W_cfcf4 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfcf8 : bv 32 := 0x00200513.
Lemma D_cfcf8 : decode_any W_cfcf8 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfcfc : bv 32 := 0x00051597.
Lemma D_cfcfc : decode_any W_cfcfc = Some (Auipc 11 81, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd00 : bv 32 := 0x02a92423.
Lemma D_cfd00 : decode_any W_cfd00 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd04 : bv 32 := 0x06000893.
Lemma D_cfd04 : decode_any W_cfd04 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd08 : bv 32 := 0x9c458513.
Lemma D_cfd08 : decode_any W_cfd08 = Some (OpImm ALU_ADD 10 11 2500, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd0c : bv 32 := 0x03848593.
Lemma D_cfd0c : decode_any W_cfd0c = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd10 : bv 32 := 0x00000073.

Lemma E_cfd10 : is_ecall W_cfd10 = true.
Proof. vm_refl. Qed.

Definition W_cfd14 : bv 32 := 0x07890613.
Lemma D_cfd14 : decode_any W_cfd14 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd18 : bv 32 := 0x02a92023.
Lemma D_cfd18 : decode_any W_cfd18 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd1c : bv 32 := 0x08b93c23.
Lemma D_cfd1c : decode_any W_cfd1c = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd20 : bv 32 := 0x06c93c23.
Lemma D_cfd20 : decode_any W_cfd20 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd24 : bv 32 := 0x00051517.
Lemma D_cfd24 : decode_any W_cfd24 = Some (Auipc 10 81, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd28 : bv 32 := 0xc0c53503.
Lemma D_cfd28 : decode_any W_cfd28 = Some (Load SZ8 true 10 10 3084, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd2c : bv 32 := 0x01293423.
Lemma D_cfd2c : decode_any W_cfd2c = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd30 : bv 32 := 0x01293823.
Lemma D_cfd30 : decode_any W_cfd30 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd34 : bv 32 := 0x00a93c23.
Lemma D_cfd34 : decode_any W_cfd34 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd38 : bv 32 := 0x0080006f.
Lemma D_cfd38 : decode_any W_cfd38 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd40 : bv 32 := 0x03813083.
Lemma D_cfd40 : decode_any W_cfd40 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd44 : bv 32 := 0x03013403.
Lemma D_cfd44 : decode_any W_cfd44 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd48 : bv 32 := 0x02813483.
Lemma D_cfd48 : decode_any W_cfd48 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd4c : bv 32 := 0x02013903.
Lemma D_cfd4c : decode_any W_cfd4c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd50 : bv 32 := 0x01813983.
Lemma D_cfd50 : decode_any W_cfd50 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd54 : bv 32 := 0x01013a03.
Lemma D_cfd54 : decode_any W_cfd54 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd58 : bv 32 := 0x00813a83.
Lemma D_cfd58 : decode_any W_cfd58 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd5c : bv 32 := 0x04010113.
Lemma D_cfd5c : decode_any W_cfd5c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_cfd60 : bv 32 := 0x00008067.
Lemma D_cfd60 : decode_any W_cfd60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0220 : bv 32 := 0xff010113.
Lemma D_d0220 : decode_any W_d0220 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0224 : bv 32 := 0x00113423.
Lemma D_d0224 : decode_any W_d0224 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0228 : bv 32 := 0x00050e63.
Lemma D_d0228 : decode_any W_d0228 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_d022c : bv 32 := 0x00050593.
Lemma D_d022c : decode_any W_d022c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0230 : bv 32 := 0x0001d517.
Lemma D_d0230 : decode_any W_d0230 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0234 : bv 32 := 0xe5453503.
Lemma D_d0234 : decode_any W_d0234 = Some (Load SZ8 true 10 10 3668, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0238 : bv 32 := 0x00800613.
Lemma D_d0238 : decode_any W_d0238 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d023c : bv 32 := 0x3d5100ef.
Lemma D_d023c : decode_any W_d023c = Some (Jal 1 68564, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0240 : bv 32 := 0x01c0006f.
Lemma D_d0240 : decode_any W_d0240 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_d025c : bv 32 := 0x0001d517.
Lemma D_d025c : decode_any W_d025c = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0260 : bv 32 := 0xe2853503.
Lemma D_d0260 : decode_any W_d0260 = Some (Load SZ8 true 10 10 3624, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0264 : bv 32 := 0x000500a3.
Lemma D_d0264 : decode_any W_d0264 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0268 : bv 32 := 0x00053503.
Lemma D_d0268 : decode_any W_d0268 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d026c : bv 32 := 0x00020593.
Lemma D_d026c : decode_any W_d026c = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0270 : bv 32 := 0xfea5b823.
Lemma D_d0270 : decode_any W_d0270 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0274 : bv 32 := 0x00813083.
Lemma D_d0274 : decode_any W_d0274 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_d0278 : bv 32 := 0x01010113.
Lemma D_d0278 : decode_any W_d0278 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_d027c : bv 32 := 0x00008067.
Lemma D_d027c : decode_any W_d027c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0e10 : bv 32 := 0x0035f693.
Lemma D_e0e10 : decode_any W_e0e10 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0e14 : bv 32 := 0x10068863.
Lemma D_e0e14 : decode_any W_e0e14 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f24 : bv 32 := 0x00050693.
Lemma D_e0f24 : decode_any W_e0f24 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f28 : bv 32 := 0x00357793.
Lemma D_e0f28 : decode_any W_e0f28 = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f2c : bv 32 := 0xf2079ae3.
Lemma D_e0f2c : decode_any W_e0f2c = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f30 : bv 32 := 0x01000713.
Lemma D_e0f30 : decode_any W_e0f30 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f34 : bv 32 := 0x02e66c63.
Lemma D_e0f34 : decode_any W_e0f34 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f6c : bv 32 := 0x00800713.
Lemma D_e0f6c : decode_any W_e0f6c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f70 : bv 32 := 0x00e66e63.
Lemma D_e0f70 : decode_any W_e0f70 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f74 : bv 32 := 0x0005a703.
Lemma D_e0f74 : decode_any W_e0f74 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f78 : bv 32 := 0x0045a783.
Lemma D_e0f78 : decode_any W_e0f78 = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f7c : bv 32 := 0x00e6a023.
Lemma D_e0f7c : decode_any W_e0f7c = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f80 : bv 32 := 0x00f6a223.
Lemma D_e0f80 : decode_any W_e0f80 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f84 : bv 32 := 0x00868693.
Lemma D_e0f84 : decode_any W_e0f84 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f88 : bv 32 := 0x00858593.
Lemma D_e0f88 : decode_any W_e0f88 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f8c : bv 32 := 0x00467713.
Lemma D_e0f8c : decode_any W_e0f8c = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_e0f90 : bv 32 := 0x24070063.
Lemma D_e0f90 : decode_any W_e0f90 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

Definition W_e11d0 : bv 32 := 0x00267713.
Lemma D_e11d0 : decode_any W_e11d0 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_e11d4 : bv 32 := 0x00071863.
Lemma D_e11d4 : decode_any W_e11d4 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e11d8 : bv 32 := 0x00167613.
Lemma D_e11d8 : decode_any W_e11d8 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e11dc : bv 32 := 0x02061663.
Lemma D_e11dc : decode_any W_e11dc = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_e11e0 : bv 32 := 0x00008067.
Lemma D_e11e0 : decode_any W_e11e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1390 : bv 32 := 0x0e060a63.
Lemma D_e1390 : decode_any W_e1390 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1394 : bv 32 := 0x00b50023.
Lemma D_e1394 : decode_any W_e1394 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1398 : bv 32 := 0x00c506b3.
Lemma D_e1398 : decode_any W_e1398 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_e139c : bv 32 := 0x00300713.
Lemma D_e139c : decode_any W_e139c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13a0 : bv 32 := 0xfeb68fa3.
Lemma D_e13a0 : decode_any W_e13a0 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13a4 : bv 32 := 0x0ee66063.
Lemma D_e13a4 : decode_any W_e13a4 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13a8 : bv 32 := 0x00b500a3.
Lemma D_e13a8 : decode_any W_e13a8 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13ac : bv 32 := 0x00b50123.
Lemma D_e13ac : decode_any W_e13ac = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13b0 : bv 32 := 0x00700713.
Lemma D_e13b0 : decode_any W_e13b0 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13b4 : bv 32 := 0xfeb68ea3.
Lemma D_e13b4 : decode_any W_e13b4 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13b8 : bv 32 := 0xfeb68f23.
Lemma D_e13b8 : decode_any W_e13b8 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13bc : bv 32 := 0x0ce66463.
Lemma D_e13bc : decode_any W_e13bc = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13c0 : bv 32 := 0x00b501a3.
Lemma D_e13c0 : decode_any W_e13c0 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13c4 : bv 32 := 0x00900793.
Lemma D_e13c4 : decode_any W_e13c4 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13c8 : bv 32 := 0xfeb68e23.
Lemma D_e13c8 : decode_any W_e13c8 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13cc : bv 32 := 0x0af66c63.
Lemma D_e13cc : decode_any W_e13cc = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13d0 : bv 32 := 0x40a006bb.
Lemma D_e13d0 : decode_any W_e13d0 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13d4 : bv 32 := 0x03859813.
Lemma D_e13d4 : decode_any W_e13d4 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13d8 : bv 32 := 0x101015b7.
Lemma D_e13d8 : decode_any W_e13d8 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13dc : bv 32 := 0x0036f693.
Lemma D_e13dc : decode_any W_e13dc = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13e0 : bv 32 := 0x00459713.
Lemma D_e13e0 : decode_any W_e13e0 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13e4 : bv 32 := 0x40d60633.
Lemma D_e13e4 : decode_any W_e13e4 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13e8 : bv 32 := 0x00d505b3.
Lemma D_e13e8 : decode_any W_e13e8 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13ec : bv 32 := 0x10070693.
Lemma D_e13ec : decode_any W_e13ec = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13f0 : bv 32 := 0xffc67713.
Lemma D_e13f0 : decode_any W_e13f0 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13f4 : bv 32 := 0x02d83633.
Lemma D_e13f4 : decode_any W_e13f4 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13f8 : bv 32 := 0x00c5a023.
Lemma D_e13f8 : decode_any W_e13f8 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e13fc : bv 32 := 0x00e586b3.
Lemma D_e13fc : decode_any W_e13fc = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1400 : bv 32 := 0xfec6ae23.
Lemma D_e1400 : decode_any W_e1400 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1404 : bv 32 := 0x08f76063.
Lemma D_e1404 : decode_any W_e1404 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1408 : bv 32 := 0x00c5a223.
Lemma D_e1408 : decode_any W_e1408 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_e140c : bv 32 := 0x00c5a423.
Lemma D_e140c : decode_any W_e140c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1410 : bv 32 := 0x01900793.
Lemma D_e1410 : decode_any W_e1410 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1414 : bv 32 := 0xfec6aa23.
Lemma D_e1414 : decode_any W_e1414 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1418 : bv 32 := 0xfec6ac23.
Lemma D_e1418 : decode_any W_e1418 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_e141c : bv 32 := 0x06f76463.
Lemma D_e141c : decode_any W_e141c = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1420 : bv 32 := 0x00c5a623.
Lemma D_e1420 : decode_any W_e1420 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1424 : bv 32 := 0x00c5a823.
Lemma D_e1424 : decode_any W_e1424 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1428 : bv 32 := 0x00c5aa23.
Lemma D_e1428 : decode_any W_e1428 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_e142c : bv 32 := 0x00c5ac23.
Lemma D_e142c : decode_any W_e142c = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1430 : bv 32 := 0x0045f793.
Lemma D_e1430 : decode_any W_e1430 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1434 : bv 32 := 0x02000813.
Lemma D_e1434 : decode_any W_e1434 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1438 : bv 32 := 0x01878793.
Lemma D_e1438 : decode_any W_e1438 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_e143c : bv 32 := 0x40f70733.
Lemma D_e143c : decode_any W_e143c = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1440 : bv 32 := 0xfec6a223.
Lemma D_e1440 : decode_any W_e1440 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1444 : bv 32 := 0xfec6a423.
Lemma D_e1444 : decode_any W_e1444 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1448 : bv 32 := 0xfec6a623.
Lemma D_e1448 : decode_any W_e1448 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

Definition W_e144c : bv 32 := 0xfec6a823.
Lemma D_e144c : decode_any W_e144c = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1450 : bv 32 := 0x03076a63.
Lemma D_e1450 : decode_any W_e1450 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1454 : bv 32 := 0x02061613.
Lemma D_e1454 : decode_any W_e1454 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1458 : bv 32 := 0x00f585b3.
Lemma D_e1458 : decode_any W_e1458 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_e145c : bv 32 := 0x02065693.
Lemma D_e145c : decode_any W_e145c = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1460 : bv 32 := 0x00d66633.
Lemma D_e1460 : decode_any W_e1460 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1464 : bv 32 := 0x01f00693.
Lemma D_e1464 : decode_any W_e1464 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1468 : bv 32 := 0x00c5b023.
Lemma D_e1468 : decode_any W_e1468 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e146c : bv 32 := 0x00c5b423.
Lemma D_e146c : decode_any W_e146c = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1470 : bv 32 := 0x00c5b823.
Lemma D_e1470 : decode_any W_e1470 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1474 : bv 32 := 0x00c5bc23.
Lemma D_e1474 : decode_any W_e1474 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1478 : bv 32 := 0xfe070713.
Lemma D_e1478 : decode_any W_e1478 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_e147c : bv 32 := 0x02058593.
Lemma D_e147c : decode_any W_e147c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1480 : bv 32 := 0xfee6e4e3.
Lemma D_e1480 : decode_any W_e1480 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1484 : bv 32 := 0x00008067.
Lemma D_e1484 : decode_any W_e1484 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3530 : bv 32 := 0x00050213.
Lemma D_e3530 : decode_any W_e3530 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3534 : bv 32 := 0x00000513.
Lemma D_e3534 : decode_any W_e3534 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e3538 : bv 32 := 0x00008067.
Lemma D_e3538 : decode_any W_e3538 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition code_tbl : list (word * bv 32) := [
  (0x6549c, W_6545c);
  (0x654a0, W_65460);
  (0x654a4, W_65464);
  (0x654a8, W_65468);
  (0x654ac, W_6546c);
  (0x654b0, W_65470);
  (0x654b4, W_65474);
  (0x654b8, W_65478);
  (0x654bc, W_6547c);
  (0x654c0, W_65480);
  (0x654c4, W_65484);
  (0x654c8, W_65488);
  (0x654cc, W_6548c);
  (0x654d0, W_65490);
  (0x654d4, W_65494);
  (0x654d8, W_65498);
  (0x654dc, W_6549c);
  (0x654e0, W_654a0);
  (0xcf790, W_cf750);
  (0xcf794, W_cf754);
  (0xcf798, W_cf758);
  (0xcf79c, W_cf75c);
  (0xcf7a0, W_cf760);
  (0xcf7a4, W_cf764);
  (0xcf7a8, W_cf768);
  (0xcf7ac, W_cf76c);
  (0xcf7b0, W_cf770);
  (0xcf7b4, W_cf774);
  (0xcf7b8, W_cf778);
  (0xcf7bc, W_cf77c);
  (0xcf7c0, W_cf780);
  (0xcf7c4, W_cf784);
  (0xcf7c8, W_cf788);
  (0xcf7cc, W_cf78c);
  (0xcf7d0, W_cf790);
  (0xcf7d4, W_cf794);
  (0xcf7d8, W_cf798);
  (0xcf7dc, W_cf79c);
  (0xcf7e0, W_cf7a0);
  (0xcf7e4, W_cf7a4);
  (0xcf7e8, W_cf7a8);
  (0xcf7ec, W_cf7ac);
  (0xcf7f0, W_cf7b0);
  (0xcf7f4, W_cf7b4);
  (0xcf7f8, W_cf7b8);
  (0xcf7fc, W_cf7bc);
  (0xcf800, W_cf7c0);
  (0xcf804, W_cf7c4);
  (0xcf808, W_cf7c8);
  (0xcf80c, W_cf7cc);
  (0xcf810, W_cf7d0);
  (0xcf814, W_cf7d4);
  (0xcf818, W_cf7d8);
  (0xcf81c, W_cf7dc);
  (0xcf820, W_cf7e0);
  (0xcf824, W_cf7e4);
  (0xcf828, W_cf7e8);
  (0xcf82c, W_cf7ec);
  (0xcf830, W_cf7f0);
  (0xcf848, W_cf808);
  (0xcf84c, W_cf80c);
  (0xcf850, W_cf810);
  (0xcf858, W_cf818);
  (0xcf864, W_cf824);
  (0xcf868, W_cf828);
  (0xcf86c, W_cf82c);
  (0xcf870, W_cf830);
  (0xcf874, W_cf834);
  (0xcf878, W_cf838);
  (0xcf87c, W_cf83c);
  (0xcf880, W_cf840);
  (0xcf884, W_cf844);
  (0xcf888, W_cf848);
  (0xcf88c, W_cf84c);
  (0xcf890, W_cf850);
  (0xcf894, W_cf854);
  (0xcf898, W_cf858);
  (0xcf89c, W_cf85c);
  (0xcf8a0, W_cf860);
  (0xcf8a4, W_cf864);
  (0xcf8a8, W_cf868);
  (0xcf8ac, W_cf86c);
  (0xcf8b0, W_cf870);
  (0xcf8b4, W_cf874);
  (0xcf8b8, W_cf878);
  (0xcf8bc, W_cf87c);
  (0xcf8c0, W_cf880);
  (0xcf8c4, W_cf884);
  (0xcf8c8, W_cf888);
  (0xcf9a8, W_cf968);
  (0xcf9ac, W_cf96c);
  (0xcf9b0, W_cf970);
  (0xcf9b4, W_cf974);
  (0xcf9b8, W_cf978);
  (0xcf9bc, W_cf97c);
  (0xcf9c0, W_cf980);
  (0xcf9c4, W_cf984);
  (0xcf9c8, W_cf988);
  (0xcf9cc, W_cf98c);
  (0xcf9d0, W_cf990);
  (0xcf9d4, W_cf994);
  (0xcf9d8, W_cf998);
  (0xcf9dc, W_cf99c);
  (0xcf9e0, W_cf9a0);
  (0xcf9e4, W_cf9a4);
  (0xcf9e8, W_cf9a8);
  (0xcf9ec, W_cf9ac);
  (0xcf9f0, W_cf9b0);
  (0xcf9f4, W_cf9b4);
  (0xcf9f8, W_cf9b8);
  (0xcf9fc, W_cf9bc);
  (0xcfa00, W_cf9c0);
  (0xcfa04, W_cf9c4);
  (0xcfa08, W_cf9c8);
  (0xcfa0c, W_cf9cc);
  (0xcfa10, W_cf9d0);
  (0xcfa14, W_cf9d4);
  (0xcfa18, W_cf9d8);
  (0xcfa1c, W_cf9dc);
  (0xcfa20, W_cf9e0);
  (0xcfa24, W_cf9e4);
  (0xcfa28, W_cf9e8);
  (0xcfa2c, W_cf9ec);
  (0xcfa30, W_cf9f0);
  (0xcfa34, W_cf9f4);
  (0xcfa38, W_cf9f8);
  (0xcfa3c, W_cf9fc);
  (0xcfa40, W_cfa00);
  (0xcfa44, W_cfa04);
  (0xcfa48, W_cfa08);
  (0xcfa4c, W_cfa0c);
  (0xcfa50, W_cfa10);
  (0xcfa54, W_cfa14);
  (0xcfa58, W_cfa18);
  (0xcfa5c, W_cfa1c);
  (0xcfa60, W_cfa20);
  (0xcfa64, W_cfa24);
  (0xcfa68, W_cfa28);
  (0xcfa6c, W_cfa2c);
  (0xcfa70, W_cfa30);
  (0xcfa74, W_cfa34);
  (0xcfa78, W_cfa38);
  (0xcfa7c, W_cfa3c);
  (0xcfa80, W_cfa40);
  (0xcfa84, W_cfa44);
  (0xcfa88, W_cfa48);
  (0xcfa8c, W_cfa4c);
  (0xcfa90, W_cfa50);
  (0xcfa94, W_cfa54);
  (0xcfa98, W_cfa58);
  (0xcfa9c, W_cfa5c);
  (0xcfaa0, W_cfa60);
  (0xcfaa4, W_cfa64);
  (0xcfaa8, W_cfa68);
  (0xcfaac, W_cfa6c);
  (0xcfab4, W_cfab4);
  (0xcfab8, W_cfab8);
  (0xcfabc, W_cfabc);
  (0xcfac0, W_cfac0);
  (0xcfac4, W_cfac4);
  (0xcfac8, W_cfac8);
  (0xcfacc, W_cfacc);
  (0xcfad0, W_cfad0);
  (0xcfad4, W_cfad4);
  (0xcfad8, W_cfad8);
  (0xcfadc, W_cfadc);
  (0xcfae0, W_cfae0);
  (0xcfae4, W_cfae4);
  (0xcfae8, W_cfae8);
  (0xcfaec, W_cfaec);
  (0xcfaf0, W_cfaf0);
  (0xcfaf4, W_cfaf4);
  (0xcfaf8, W_cfaf8);
  (0xcfafc, W_cfafc);
  (0xcfb00, W_cfb00);
  (0xcfb04, W_cfb04);
  (0xcfb08, W_cfb08);
  (0xcfb0c, W_cfb0c);
  (0xcfb10, W_cfb10);
  (0xcfb14, W_cfb14);
  (0xcfb18, W_cfb18);
  (0xcfb1c, W_cfb1c);
  (0xcfb20, W_cfb20);
  (0xcfb24, W_cfb24);
  (0xcfb28, W_cfb28);
  (0xcfb2c, W_cfb2c);
  (0xcfb30, W_cfb30);
  (0xcfb34, W_cfb34);
  (0xcfb38, W_cfb38);
  (0xcfb3c, W_cfb3c);
  (0xcfb40, W_cfb40);
  (0xcfb44, W_cfb44);
  (0xcfb58, W_cfb58);
  (0xcfb5c, W_cfb5c);
  (0xcfb60, W_cfb60);
  (0xcfb64, W_cfb64);
  (0xcfb68, W_cfb68);
  (0xcfb6c, W_cfb6c);
  (0xcfb84, W_cfb84);
  (0xcfb88, W_cfb88);
  (0xcfb8c, W_cfb8c);
  (0xcfbc4, W_cfbc4);
  (0xcfbc8, W_cfbc8);
  (0xcfbcc, W_cfbcc);
  (0xcfbd0, W_cfbd0);
  (0xcfbd4, W_cfbd4);
  (0xcfbd8, W_cfbd8);
  (0xcfbdc, W_cfbdc);
  (0xcfbe0, W_cfbe0);
  (0xcfbe4, W_cfbe4);
  (0xcfbe8, W_cfbe8);
  (0xcfbec, W_cfbec);
  (0xcfbf0, W_cfbf0);
  (0xcfbf4, W_cfbf4);
  (0xcfbf8, W_cfbf8);
  (0xcfbfc, W_cfbfc);
  (0xcfc00, W_cfc00);
  (0xcfc04, W_cfc04);
  (0xcfc08, W_cfc08);
  (0xcfc0c, W_cfc0c);
  (0xcfc10, W_cfc10);
  (0xcfc14, W_cfc14);
  (0xcfc18, W_cfc18);
  (0xcfc1c, W_cfc1c);
  (0xcfc20, W_cfc20);
  (0xcfc54, W_cfc54);
  (0xcfc58, W_cfc58);
  (0xcfc5c, W_cfc5c);
  (0xcfc60, W_cfc60);
  (0xcfc64, W_cfc64);
  (0xcfc68, W_cfc68);
  (0xcfc6c, W_cfc6c);
  (0xcfc70, W_cfc70);
  (0xcfc74, W_cfc74);
  (0xcfc78, W_cfc78);
  (0xcfc7c, W_cfc7c);
  (0xcfc80, W_cfc80);
  (0xcfc84, W_cfc84);
  (0xcfc88, W_cfc88);
  (0xcfc8c, W_cfc8c);
  (0xcfcd4, W_cfcd4);
  (0xcfcd8, W_cfcd8);
  (0xcfcdc, W_cfcdc);
  (0xcfce0, W_cfce0);
  (0xcfce4, W_cfce4);
  (0xcfce8, W_cfce8);
  (0xcfcec, W_cfcec);
  (0xcfcf0, W_cfcf0);
  (0xcfcf4, W_cfcf4);
  (0xcfcf8, W_cfcf8);
  (0xcfcfc, W_cfcfc);
  (0xcfd00, W_cfd00);
  (0xcfd04, W_cfd04);
  (0xcfd08, W_cfd08);
  (0xcfd0c, W_cfd0c);
  (0xcfd10, W_cfd10);
  (0xcfd14, W_cfd14);
  (0xcfd18, W_cfd18);
  (0xcfd1c, W_cfd1c);
  (0xcfd20, W_cfd20);
  (0xcfd24, W_cfd24);
  (0xcfd28, W_cfd28);
  (0xcfd2c, W_cfd2c);
  (0xcfd30, W_cfd30);
  (0xcfd34, W_cfd34);
  (0xcfd38, W_cfd38);
  (0xcfd40, W_cfd40);
  (0xcfd44, W_cfd44);
  (0xcfd48, W_cfd48);
  (0xcfd4c, W_cfd4c);
  (0xcfd50, W_cfd50);
  (0xcfd54, W_cfd54);
  (0xcfd58, W_cfd58);
  (0xcfd5c, W_cfd5c);
  (0xcfd60, W_cfd60);
  (0xd0254, W_d0220);
  (0xd0258, W_d0224);
  (0xd025c, W_d0228);
  (0xd0260, W_d022c);
  (0xd0264, W_d0230);
  (0xd0268, W_d0234);
  (0xd026c, W_d0238);
  (0xd0270, W_d023c);
  (0xd0274, W_d0240);
  (0xd0290, W_d025c);
  (0xd0294, W_d0260);
  (0xd0298, W_d0264);
  (0xd029c, W_d0268);
  (0xd02a0, W_d026c);
  (0xd02a4, W_d0270);
  (0xd02a8, W_d0274);
  (0xd02ac, W_d0278);
  (0xd02b0, W_d027c);
  (0xe0e44, W_e0e10);
  (0xe0e48, W_e0e14);
  (0xe0f58, W_e0f24);
  (0xe0f5c, W_e0f28);
  (0xe0f60, W_e0f2c);
  (0xe0f64, W_e0f30);
  (0xe0f68, W_e0f34);
  (0xe0fa0, W_e0f6c);
  (0xe0fa4, W_e0f70);
  (0xe0fa8, W_e0f74);
  (0xe0fac, W_e0f78);
  (0xe0fb0, W_e0f7c);
  (0xe0fb4, W_e0f80);
  (0xe0fb8, W_e0f84);
  (0xe0fbc, W_e0f88);
  (0xe0fc0, W_e0f8c);
  (0xe0fc4, W_e0f90);
  (0xe1204, W_e11d0);
  (0xe1208, W_e11d4);
  (0xe120c, W_e11d8);
  (0xe1210, W_e11dc);
  (0xe1214, W_e11e0);
  (0xe13c4, W_e1390);
  (0xe13c8, W_e1394);
  (0xe13cc, W_e1398);
  (0xe13d0, W_e139c);
  (0xe13d4, W_e13a0);
  (0xe13d8, W_e13a4);
  (0xe13dc, W_e13a8);
  (0xe13e0, W_e13ac);
  (0xe13e4, W_e13b0);
  (0xe13e8, W_e13b4);
  (0xe13ec, W_e13b8);
  (0xe13f0, W_e13bc);
  (0xe13f4, W_e13c0);
  (0xe13f8, W_e13c4);
  (0xe13fc, W_e13c8);
  (0xe1400, W_e13cc);
  (0xe1404, W_e13d0);
  (0xe1408, W_e13d4);
  (0xe140c, W_e13d8);
  (0xe1410, W_e13dc);
  (0xe1414, W_e13e0);
  (0xe1418, W_e13e4);
  (0xe141c, W_e13e8);
  (0xe1420, W_e13ec);
  (0xe1424, W_e13f0);
  (0xe1428, W_e13f4);
  (0xe142c, W_e13f8);
  (0xe1430, W_e13fc);
  (0xe1434, W_e1400);
  (0xe1438, W_e1404);
  (0xe143c, W_e1408);
  (0xe1440, W_e140c);
  (0xe1444, W_e1410);
  (0xe1448, W_e1414);
  (0xe144c, W_e1418);
  (0xe1450, W_e141c);
  (0xe1454, W_e1420);
  (0xe1458, W_e1424);
  (0xe145c, W_e1428);
  (0xe1460, W_e142c);
  (0xe1464, W_e1430);
  (0xe1468, W_e1434);
  (0xe146c, W_e1438);
  (0xe1470, W_e143c);
  (0xe1474, W_e1440);
  (0xe1478, W_e1444);
  (0xe147c, W_e1448);
  (0xe1480, W_e144c);
  (0xe1484, W_e1450);
  (0xe1488, W_e1454);
  (0xe148c, W_e1458);
  (0xe1490, W_e145c);
  (0xe1494, W_e1460);
  (0xe1498, W_e1464);
  (0xe149c, W_e1468);
  (0xe14a0, W_e146c);
  (0xe14a4, W_e1470);
  (0xe14a8, W_e1474);
  (0xe14ac, W_e1478);
  (0xe14b0, W_e147c);
  (0xe14b4, W_e1480);
  (0xe14b8, W_e1484);
  (0xe3564, W_e3530);
  (0xe3568, W_e3534);
  (0xe356c, W_e3538)
].

Definition img_tbl : list (word * nat * list byte) := [
  (Z_to_bv 64 65600, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 6));
  (Z_to_bv 64 65616, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 65600));
  (Z_to_bv 64 65656, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1));
  (Z_to_bv 64 65712, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1));
  (Z_to_bv 64 65768, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1));
  (Z_to_bv 64 65824, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1));
  (Z_to_bv 64 65880, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1685382482));
  (Z_to_bv 64 65936, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1685382480));
  (Z_to_bv 64 65992, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1685382481));
  (Z_to_bv 64 66032, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 66048, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 4));
  (Z_to_bv 64 66104, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 1879048195));
  (Z_to_bv 64 970440, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 970448, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 415208));
  (Z_to_bv 64 970456, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 849808));
  (Z_to_bv 64 970464, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 852140));
  (Z_to_bv 64 970896, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 1050088));
  (Z_to_bv 64 970904, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 1182016));
  (Z_to_bv 64 970912, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 1182008));
  (Z_to_bv 64 970920, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 945944));
  (Z_to_bv 64 970928, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 945928));
  (Z_to_bv 64 976000, 4%nat, word_to_le_bytes 4 (Z_to_bv 64 131072));
  (Z_to_bv 64 1181392, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 1181408, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 1181416, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 1182000, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 1182040, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 1182064, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 0));
  (Z_to_bv 64 970936, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 1181992));
  (Z_to_bv 64 945928, 8%nat, word_to_le_bytes 8 (Z_to_bv 64 602300))
].

Definition fetch_is (segs : list Segment) (pc : word) (w : bv 32) : bool :=
  match fetch_word segs pc with Some w' => bv_eqb w' w | None => false end.

Definition code_ok (segs : list Segment) : bool :=
  forallb (fun e => fetch_is segs (fst e) (snd e)) code_tbl.

Fixpoint bytes_eqb (l1 l2 : list byte) : bool :=
  match l1, l2 with
  | [], [] => true
  | b1 :: r1, b2 :: r2 => bv_eqb b1 b2 && bytes_eqb r1 r2
  | _, _ => false
  end.

Definition rdn_is (segs : list Segment) (a : word) (n : nat) (bs : list byte) : bool :=
  match rdn segs (fun _ => None) a n with Some bs' => bytes_eqb bs' bs | None => false end.

Definition img_ok (segs : list Segment) : bool :=
  forallb (fun e => match e with (a, n, bs) => rdn_is segs a n bs end) img_tbl.

Definition data_lo : Z := 0x1005b0.
Definition data_len : nat := 400%nat.

Definition data2_lo : Z := 0x1206c0.
Definition data2_len : nat := 880%nat.

Definition s1b_ok (segs : list Segment) : bool :=
  code_ok segs && img_ok segs && wseg_ok segs (Z_to_bv 64 data_lo) data_len
  && wseg_ok segs (Z_to_bv 64 data2_lo) data2_len.

Definition code_mem (pc : word) (w : bv 32) : bool :=
  existsb (fun e => bv_eqb (fst e) pc && bv_eqb (snd e) w) code_tbl.

Definition img_mem (a : word) (n : nat) (bs : list byte) : bool :=
  existsb (fun e => match e with (a', n', bs') => bv_eqb a' a && Nat.eqb n' n && bytes_eqb bs' bs end) img_tbl.

Lemma bv_eqb_eq : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. apply bv_eq. unfold bv_eqb in H. apply Z.eqb_eq in H. exact H. Qed.

Lemma bytes_eqb_eq : forall l1 l2, bytes_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|b1 r1 IH]; intros [|b2 r2] H; cbn [bytes_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply bv_eqb_eq in H1. apply IH in H2. subst. reflexivity.
Qed.

Lemma code_sound : forall segs, s1b_ok segs = true ->
  forall pc w, code_mem pc w = true -> fetch_word segs pc = Some w.
Proof.
  intros segs H pc w Hm. unfold s1b_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
  unfold code_ok in H. rewrite forallb_forall in H.
  unfold code_mem in Hm. apply existsb_exists in Hm as [[p x] [Hin Hx]].
  apply andb_prop in Hx as [Hp Hw]. apply bv_eqb_eq in Hp, Hw. cbn [fst snd] in *. subst p x.
  specialize (H _ Hin). cbn [fst snd] in H. unfold fetch_is in H.
  destruct (fetch_word segs pc) as [w'|]; [|discriminate]. apply bv_eqb_eq in H. subst. reflexivity.
Qed.

Lemma img_sound : forall segs, s1b_ok segs = true ->
  forall a n bs, img_mem a n bs = true -> rdn segs (fun _ => None) a n = Some bs.
Proof.
  intros segs H a n bs Hm. unfold s1b_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  unfold img_ok in H. rewrite forallb_forall in H.
  unfold img_mem in Hm. apply existsb_exists in Hm as [[[a' n'] bs'] [Hin Hx]].
  apply andb_prop in Hx as [Hx Hb]. apply andb_prop in Hx as [Ha Hn].
  apply bv_eqb_eq in Ha. apply Nat.eqb_eq in Hn. apply bytes_eqb_eq in Hb. subst a' n' bs'.
  specialize (H _ Hin). unfold rdn_is in H.
  destruct (rdn segs (fun _ => None) a n) as [bs'|]; [|discriminate]. apply bytes_eqb_eq in H. subst. reflexivity.
Qed.

Lemma wseg_data : forall segs, s1b_ok segs = true -> wseg_ok segs (Z_to_bv 64 data_lo) data_len = true.
Proof. intros segs H. unfold s1b_ok in H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H]. exact H. Qed.

Lemma wseg_data2 : forall segs, s1b_ok segs = true -> wseg_ok segs (Z_to_bv 64 data2_lo) data2_len = true.
Proof. intros segs H. unfold s1b_ok in H. apply andb_prop in H as [_ H]. exact H. Qed.

Lemma store_ok_data : forall segs m (a : Z) (n : nat), s1b_ok segs = true ->
  (0x1005b0 <= a)%Z -> (a + Z.of_nat n <= 0x100740)%Z ->
  store_ok segs m (Z_to_bv 64 a) n = true.
Proof.
  intros segs m a n H Hlo Hhi.
  assert (Ha : bv_unsigned (Z_to_bv 64 a) = a).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
    apply Z.mod_small. lia. }
  eapply (store_ok_window segs m (Z_to_bv 64 0x1005b0) (Z_to_bv 64 a) 400%nat n 0x1005b0 0x100740);
    [ reflexivity | reflexivity | lia | exact (wseg_data segs H) | rewrite Ha; lia | rewrite Ha; exact Hhi ].
Qed.

Lemma store_ok_data2 : forall segs m (a : Z) (n : nat), s1b_ok segs = true ->
  (0x1206c0 <= a)%Z -> (a + Z.of_nat n <= 0x120a30)%Z ->
  store_ok segs m (Z_to_bv 64 a) n = true.
Proof.
  intros segs m a n H Hlo Hhi.
  assert (Ha : bv_unsigned (Z_to_bv 64 a) = a).
  { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64)%Z.
    apply Z.mod_small. lia. }
  eapply (store_ok_window segs m (Z_to_bv 64 0x1206c0) (Z_to_bv 64 a) 880%nat n 0x1206c0 0x120a30);
    [ reflexivity | reflexivity | lia | exact (wseg_data2 segs H) | rewrite Ha; lia | rewrite Ha; exact Hhi ].
Qed.

Ltac ok_dat HX := first [ apply (store_ok_data _ _ _ _ HX); lia | apply (store_ok_data2 _ _ _ _ HX); lia ].

Lemma F_6545c : forall segs, s1b_ok segs = true -> fetch_word segs (0x6549c : word) = Some W_6545c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_65460 : forall segs, s1b_ok segs = true -> fetch_word segs (0x654a0 : word) = Some W_65460.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_65464 : forall segs, s1b_ok segs = true -> fetch_word segs (0x654a4 : word) = Some W_65464.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_65468 : forall segs, s1b_ok segs = true -> fetch_word segs (0x654a8 : word) = Some W_65468.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_6546c : forall segs, s1b_ok segs = true -> fetch_word segs (0x654ac : word) = Some W_6546c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_65470 : forall segs, s1b_ok segs = true -> fetch_word segs (0x654b0 : word) = Some W_65470.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_65474 : forall segs, s1b_ok segs = true -> fetch_word segs (0x654b4 : word) = Some W_65474.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_65478 : forall segs, s1b_ok segs = true -> fetch_word segs (0x654b8 : word) = Some W_65478.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_6547c : forall segs, s1b_ok segs = true -> fetch_word segs (0x654bc : word) = Some W_6547c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_65480 : forall segs, s1b_ok segs = true -> fetch_word segs (0x654c0 : word) = Some W_65480.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_65484 : forall segs, s1b_ok segs = true -> fetch_word segs (0x654c4 : word) = Some W_65484.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_65488 : forall segs, s1b_ok segs = true -> fetch_word segs (0x654c8 : word) = Some W_65488.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_6548c : forall segs, s1b_ok segs = true -> fetch_word segs (0x654cc : word) = Some W_6548c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_65490 : forall segs, s1b_ok segs = true -> fetch_word segs (0x654d0 : word) = Some W_65490.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_65494 : forall segs, s1b_ok segs = true -> fetch_word segs (0x654d4 : word) = Some W_65494.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_65498 : forall segs, s1b_ok segs = true -> fetch_word segs (0x654d8 : word) = Some W_65498.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_6549c : forall segs, s1b_ok segs = true -> fetch_word segs (0x654dc : word) = Some W_6549c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_654a0 : forall segs, s1b_ok segs = true -> fetch_word segs (0x654e0 : word) = Some W_654a0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf750 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf790 : word) = Some W_cf750.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf754 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf794 : word) = Some W_cf754.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf758 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf798 : word) = Some W_cf758.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf75c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf79c : word) = Some W_cf75c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf760 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7a0 : word) = Some W_cf760.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf764 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7a4 : word) = Some W_cf764.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf768 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7a8 : word) = Some W_cf768.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf76c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7ac : word) = Some W_cf76c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf770 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7b0 : word) = Some W_cf770.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf774 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7b4 : word) = Some W_cf774.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf778 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7b8 : word) = Some W_cf778.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf77c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7bc : word) = Some W_cf77c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf780 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7c0 : word) = Some W_cf780.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf784 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7c4 : word) = Some W_cf784.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf788 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7c8 : word) = Some W_cf788.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf78c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7cc : word) = Some W_cf78c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf790 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7d0 : word) = Some W_cf790.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf794 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7d4 : word) = Some W_cf794.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf798 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7d8 : word) = Some W_cf798.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf79c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7dc : word) = Some W_cf79c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7a0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7e0 : word) = Some W_cf7a0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7a4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7e4 : word) = Some W_cf7a4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7a8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7e8 : word) = Some W_cf7a8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7ac : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7ec : word) = Some W_cf7ac.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7b0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7f0 : word) = Some W_cf7b0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7b4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7f4 : word) = Some W_cf7b4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7b8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7f8 : word) = Some W_cf7b8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7bc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf7fc : word) = Some W_cf7bc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7c0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf800 : word) = Some W_cf7c0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7c4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf804 : word) = Some W_cf7c4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7c8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf808 : word) = Some W_cf7c8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7cc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf80c : word) = Some W_cf7cc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7d0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf810 : word) = Some W_cf7d0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7d4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf814 : word) = Some W_cf7d4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7d8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf818 : word) = Some W_cf7d8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7dc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf81c : word) = Some W_cf7dc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7e0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf820 : word) = Some W_cf7e0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7e4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf824 : word) = Some W_cf7e4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7e8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf828 : word) = Some W_cf7e8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7ec : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf82c : word) = Some W_cf7ec.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf7f0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf830 : word) = Some W_cf7f0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf808 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf848 : word) = Some W_cf808.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf80c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf84c : word) = Some W_cf80c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf810 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf850 : word) = Some W_cf810.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf818 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf858 : word) = Some W_cf818.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf824 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf864 : word) = Some W_cf824.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf828 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf868 : word) = Some W_cf828.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf82c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf86c : word) = Some W_cf82c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf830 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf870 : word) = Some W_cf830.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf834 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf874 : word) = Some W_cf834.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf838 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf878 : word) = Some W_cf838.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf83c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf87c : word) = Some W_cf83c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf840 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf880 : word) = Some W_cf840.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf844 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf884 : word) = Some W_cf844.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf848 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf888 : word) = Some W_cf848.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf84c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf88c : word) = Some W_cf84c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf850 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf890 : word) = Some W_cf850.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf854 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf894 : word) = Some W_cf854.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf858 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf898 : word) = Some W_cf858.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf85c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf89c : word) = Some W_cf85c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf860 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf8a0 : word) = Some W_cf860.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf864 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf8a4 : word) = Some W_cf864.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf868 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf8a8 : word) = Some W_cf868.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf86c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf8ac : word) = Some W_cf86c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf870 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf8b0 : word) = Some W_cf870.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf874 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf8b4 : word) = Some W_cf874.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf878 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf8b8 : word) = Some W_cf878.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf87c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf8bc : word) = Some W_cf87c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf880 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf8c0 : word) = Some W_cf880.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf884 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf8c4 : word) = Some W_cf884.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf888 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf8c8 : word) = Some W_cf888.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf968 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9a8 : word) = Some W_cf968.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf96c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9ac : word) = Some W_cf96c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf970 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9b0 : word) = Some W_cf970.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf974 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9b4 : word) = Some W_cf974.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf978 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9b8 : word) = Some W_cf978.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf97c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9bc : word) = Some W_cf97c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf980 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9c0 : word) = Some W_cf980.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf984 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9c4 : word) = Some W_cf984.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf988 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9c8 : word) = Some W_cf988.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf98c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9cc : word) = Some W_cf98c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf990 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9d0 : word) = Some W_cf990.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf994 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9d4 : word) = Some W_cf994.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf998 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9d8 : word) = Some W_cf998.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf99c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9dc : word) = Some W_cf99c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9a0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9e0 : word) = Some W_cf9a0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9a4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9e4 : word) = Some W_cf9a4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9a8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9e8 : word) = Some W_cf9a8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9ac : forall segs, s1b_ok segs = true -> fetch_word segs (0xcf9ec : word) = Some W_cf9ac.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.

Lemma F_cf9cc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa0c : word) = Some W_cf9cc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9d0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa10 : word) = Some W_cf9d0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9d4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa14 : word) = Some W_cf9d4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9d8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa18 : word) = Some W_cf9d8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9dc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa1c : word) = Some W_cf9dc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9e0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa20 : word) = Some W_cf9e0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9e4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa24 : word) = Some W_cf9e4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9e8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa28 : word) = Some W_cf9e8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9ec : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa2c : word) = Some W_cf9ec.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9f0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa30 : word) = Some W_cf9f0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9f4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa34 : word) = Some W_cf9f4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9f8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa38 : word) = Some W_cf9f8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cf9fc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa3c : word) = Some W_cf9fc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa00 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa40 : word) = Some W_cfa00.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa04 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa44 : word) = Some W_cfa04.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa08 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa48 : word) = Some W_cfa08.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa0c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa4c : word) = Some W_cfa0c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa10 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa50 : word) = Some W_cfa10.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa14 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa54 : word) = Some W_cfa14.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa18 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa58 : word) = Some W_cfa18.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa1c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa5c : word) = Some W_cfa1c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa20 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa60 : word) = Some W_cfa20.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa24 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa64 : word) = Some W_cfa24.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa28 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa68 : word) = Some W_cfa28.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa2c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa6c : word) = Some W_cfa2c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa30 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa70 : word) = Some W_cfa30.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa34 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa74 : word) = Some W_cfa34.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa38 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa78 : word) = Some W_cfa38.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa3c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa7c : word) = Some W_cfa3c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa40 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa80 : word) = Some W_cfa40.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa44 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa84 : word) = Some W_cfa44.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa48 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa88 : word) = Some W_cfa48.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa4c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa8c : word) = Some W_cfa4c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa50 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa90 : word) = Some W_cfa50.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa54 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa94 : word) = Some W_cfa54.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa58 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa98 : word) = Some W_cfa58.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfa5c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfa9c : word) = Some W_cfa5c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.

Lemma F_cfab4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfab4 : word) = Some W_cfab4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfab8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfab8 : word) = Some W_cfab8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfabc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfabc : word) = Some W_cfabc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfac0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfac0 : word) = Some W_cfac0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfac4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfac4 : word) = Some W_cfac4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfac8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfac8 : word) = Some W_cfac8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfacc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfacc : word) = Some W_cfacc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfad0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfad0 : word) = Some W_cfad0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfad4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfad4 : word) = Some W_cfad4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfad8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfad8 : word) = Some W_cfad8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfadc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfadc : word) = Some W_cfadc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfae0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfae0 : word) = Some W_cfae0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfae4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfae4 : word) = Some W_cfae4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfae8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfae8 : word) = Some W_cfae8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfaec : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfaec : word) = Some W_cfaec.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfaf0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfaf0 : word) = Some W_cfaf0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfaf4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfaf4 : word) = Some W_cfaf4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfaf8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfaf8 : word) = Some W_cfaf8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfafc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfafc : word) = Some W_cfafc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb00 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb00 : word) = Some W_cfb00.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb04 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb04 : word) = Some W_cfb04.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb08 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb08 : word) = Some W_cfb08.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb0c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb0c : word) = Some W_cfb0c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb10 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb10 : word) = Some W_cfb10.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb14 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb14 : word) = Some W_cfb14.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb18 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb18 : word) = Some W_cfb18.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb1c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb1c : word) = Some W_cfb1c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb20 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb20 : word) = Some W_cfb20.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb24 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb24 : word) = Some W_cfb24.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb28 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb28 : word) = Some W_cfb28.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb2c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb2c : word) = Some W_cfb2c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb30 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb30 : word) = Some W_cfb30.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb34 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb34 : word) = Some W_cfb34.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb38 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb38 : word) = Some W_cfb38.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb3c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb3c : word) = Some W_cfb3c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb40 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb40 : word) = Some W_cfb40.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb44 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb44 : word) = Some W_cfb44.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb58 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb58 : word) = Some W_cfb58.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb5c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb5c : word) = Some W_cfb5c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb60 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb60 : word) = Some W_cfb60.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb64 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb64 : word) = Some W_cfb64.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb68 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb68 : word) = Some W_cfb68.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb6c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb6c : word) = Some W_cfb6c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb84 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb84 : word) = Some W_cfb84.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb88 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb88 : word) = Some W_cfb88.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfb8c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfb8c : word) = Some W_cfb8c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbc4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbc4 : word) = Some W_cfbc4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbc8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbc8 : word) = Some W_cfbc8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbcc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbcc : word) = Some W_cfbcc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbd0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbd0 : word) = Some W_cfbd0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbd4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbd4 : word) = Some W_cfbd4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbd8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbd8 : word) = Some W_cfbd8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbdc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbdc : word) = Some W_cfbdc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbe0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbe0 : word) = Some W_cfbe0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbe4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbe4 : word) = Some W_cfbe4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbe8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbe8 : word) = Some W_cfbe8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbec : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbec : word) = Some W_cfbec.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbf0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbf0 : word) = Some W_cfbf0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbf4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbf4 : word) = Some W_cfbf4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbf8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbf8 : word) = Some W_cfbf8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfbfc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfbfc : word) = Some W_cfbfc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc00 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc00 : word) = Some W_cfc00.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc04 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc04 : word) = Some W_cfc04.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc08 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc08 : word) = Some W_cfc08.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc0c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc0c : word) = Some W_cfc0c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc10 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc10 : word) = Some W_cfc10.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc14 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc14 : word) = Some W_cfc14.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc18 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc18 : word) = Some W_cfc18.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc1c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc1c : word) = Some W_cfc1c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc20 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc20 : word) = Some W_cfc20.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc54 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc54 : word) = Some W_cfc54.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc58 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc58 : word) = Some W_cfc58.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc5c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc5c : word) = Some W_cfc5c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc60 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc60 : word) = Some W_cfc60.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc64 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc64 : word) = Some W_cfc64.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc68 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc68 : word) = Some W_cfc68.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc6c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc6c : word) = Some W_cfc6c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc70 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc70 : word) = Some W_cfc70.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc74 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc74 : word) = Some W_cfc74.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc78 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc78 : word) = Some W_cfc78.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc7c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc7c : word) = Some W_cfc7c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc80 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc80 : word) = Some W_cfc80.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc84 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc84 : word) = Some W_cfc84.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc88 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc88 : word) = Some W_cfc88.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfc8c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfc8c : word) = Some W_cfc8c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfcd4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfcd4 : word) = Some W_cfcd4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfcd8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfcd8 : word) = Some W_cfcd8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfcdc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfcdc : word) = Some W_cfcdc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfce0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfce0 : word) = Some W_cfce0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfce4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfce4 : word) = Some W_cfce4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfce8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfce8 : word) = Some W_cfce8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfcec : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfcec : word) = Some W_cfcec.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfcf0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfcf0 : word) = Some W_cfcf0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfcf4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfcf4 : word) = Some W_cfcf4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfcf8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfcf8 : word) = Some W_cfcf8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfcfc : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfcfc : word) = Some W_cfcfc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd00 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd00 : word) = Some W_cfd00.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd04 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd04 : word) = Some W_cfd04.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd08 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd08 : word) = Some W_cfd08.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd0c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd0c : word) = Some W_cfd0c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd10 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd10 : word) = Some W_cfd10.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd14 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd14 : word) = Some W_cfd14.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd18 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd18 : word) = Some W_cfd18.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd1c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd1c : word) = Some W_cfd1c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd20 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd20 : word) = Some W_cfd20.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd24 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd24 : word) = Some W_cfd24.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd28 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd28 : word) = Some W_cfd28.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd2c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd2c : word) = Some W_cfd2c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd30 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd30 : word) = Some W_cfd30.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd34 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd34 : word) = Some W_cfd34.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd38 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd38 : word) = Some W_cfd38.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd40 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd40 : word) = Some W_cfd40.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd44 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd44 : word) = Some W_cfd44.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd48 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd48 : word) = Some W_cfd48.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd4c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd4c : word) = Some W_cfd4c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd50 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd50 : word) = Some W_cfd50.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd54 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd54 : word) = Some W_cfd54.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd58 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd58 : word) = Some W_cfd58.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd5c : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd5c : word) = Some W_cfd5c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_cfd60 : forall segs, s1b_ok segs = true -> fetch_word segs (0xcfd60 : word) = Some W_cfd60.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d0220 : forall segs, s1b_ok segs = true -> fetch_word segs (0xd0254 : word) = Some W_d0220.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d0224 : forall segs, s1b_ok segs = true -> fetch_word segs (0xd0258 : word) = Some W_d0224.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d0228 : forall segs, s1b_ok segs = true -> fetch_word segs (0xd025c : word) = Some W_d0228.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d022c : forall segs, s1b_ok segs = true -> fetch_word segs (0xd0260 : word) = Some W_d022c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d0230 : forall segs, s1b_ok segs = true -> fetch_word segs (0xd0264 : word) = Some W_d0230.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d0234 : forall segs, s1b_ok segs = true -> fetch_word segs (0xd0268 : word) = Some W_d0234.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d0238 : forall segs, s1b_ok segs = true -> fetch_word segs (0xd026c : word) = Some W_d0238.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d023c : forall segs, s1b_ok segs = true -> fetch_word segs (0xd0270 : word) = Some W_d023c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d0240 : forall segs, s1b_ok segs = true -> fetch_word segs (0xd0274 : word) = Some W_d0240.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d025c : forall segs, s1b_ok segs = true -> fetch_word segs (0xd0290 : word) = Some W_d025c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d0260 : forall segs, s1b_ok segs = true -> fetch_word segs (0xd0294 : word) = Some W_d0260.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d0264 : forall segs, s1b_ok segs = true -> fetch_word segs (0xd0298 : word) = Some W_d0264.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d0268 : forall segs, s1b_ok segs = true -> fetch_word segs (0xd029c : word) = Some W_d0268.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d026c : forall segs, s1b_ok segs = true -> fetch_word segs (0xd02a0 : word) = Some W_d026c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d0270 : forall segs, s1b_ok segs = true -> fetch_word segs (0xd02a4 : word) = Some W_d0270.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d0274 : forall segs, s1b_ok segs = true -> fetch_word segs (0xd02a8 : word) = Some W_d0274.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d0278 : forall segs, s1b_ok segs = true -> fetch_word segs (0xd02ac : word) = Some W_d0278.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_d027c : forall segs, s1b_ok segs = true -> fetch_word segs (0xd02b0 : word) = Some W_d027c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0e10 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0e44 : word) = Some W_e0e10.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0e14 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0e48 : word) = Some W_e0e14.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f24 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0f58 : word) = Some W_e0f24.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f28 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0f5c : word) = Some W_e0f28.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f2c : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0f60 : word) = Some W_e0f2c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f30 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0f64 : word) = Some W_e0f30.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f34 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0f68 : word) = Some W_e0f34.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f6c : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0fa0 : word) = Some W_e0f6c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f70 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0fa4 : word) = Some W_e0f70.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f74 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0fa8 : word) = Some W_e0f74.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f78 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0fac : word) = Some W_e0f78.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f7c : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0fb0 : word) = Some W_e0f7c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f80 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0fb4 : word) = Some W_e0f80.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f84 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0fb8 : word) = Some W_e0f84.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f88 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0fbc : word) = Some W_e0f88.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f8c : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0fc0 : word) = Some W_e0f8c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e0f90 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe0fc4 : word) = Some W_e0f90.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e11d0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1204 : word) = Some W_e11d0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e11d4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1208 : word) = Some W_e11d4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e11d8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe120c : word) = Some W_e11d8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e11dc : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1210 : word) = Some W_e11dc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e11e0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1214 : word) = Some W_e11e0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1390 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13c4 : word) = Some W_e1390.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1394 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13c8 : word) = Some W_e1394.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1398 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13cc : word) = Some W_e1398.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e139c : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13d0 : word) = Some W_e139c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13a0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13d4 : word) = Some W_e13a0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13a4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13d8 : word) = Some W_e13a4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13a8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13dc : word) = Some W_e13a8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13ac : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13e0 : word) = Some W_e13ac.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13b0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13e4 : word) = Some W_e13b0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13b4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13e8 : word) = Some W_e13b4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13b8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13ec : word) = Some W_e13b8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13bc : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13f0 : word) = Some W_e13bc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13c0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13f4 : word) = Some W_e13c0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13c4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13f8 : word) = Some W_e13c4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13c8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe13fc : word) = Some W_e13c8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13cc : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1400 : word) = Some W_e13cc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13d0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1404 : word) = Some W_e13d0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13d4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1408 : word) = Some W_e13d4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13d8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe140c : word) = Some W_e13d8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13dc : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1410 : word) = Some W_e13dc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13e0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1414 : word) = Some W_e13e0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13e4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1418 : word) = Some W_e13e4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13e8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe141c : word) = Some W_e13e8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13ec : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1420 : word) = Some W_e13ec.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13f0 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1424 : word) = Some W_e13f0.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13f4 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1428 : word) = Some W_e13f4.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13f8 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe142c : word) = Some W_e13f8.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e13fc : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1430 : word) = Some W_e13fc.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1400 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1434 : word) = Some W_e1400.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1404 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1438 : word) = Some W_e1404.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1408 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe143c : word) = Some W_e1408.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e140c : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1440 : word) = Some W_e140c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1410 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1444 : word) = Some W_e1410.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1414 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1448 : word) = Some W_e1414.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1418 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe144c : word) = Some W_e1418.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e141c : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1450 : word) = Some W_e141c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1420 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1454 : word) = Some W_e1420.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1424 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1458 : word) = Some W_e1424.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1428 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe145c : word) = Some W_e1428.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e142c : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1460 : word) = Some W_e142c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1430 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1464 : word) = Some W_e1430.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1434 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1468 : word) = Some W_e1434.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1438 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe146c : word) = Some W_e1438.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e143c : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1470 : word) = Some W_e143c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1440 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1474 : word) = Some W_e1440.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1444 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1478 : word) = Some W_e1444.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1448 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe147c : word) = Some W_e1448.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e144c : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1480 : word) = Some W_e144c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1450 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1484 : word) = Some W_e1450.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1454 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1488 : word) = Some W_e1454.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1458 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe148c : word) = Some W_e1458.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e145c : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1490 : word) = Some W_e145c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1460 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1494 : word) = Some W_e1460.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1464 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe1498 : word) = Some W_e1464.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1468 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe149c : word) = Some W_e1468.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e146c : forall segs, s1b_ok segs = true -> fetch_word segs (0xe14a0 : word) = Some W_e146c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1470 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe14a4 : word) = Some W_e1470.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1474 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe14a8 : word) = Some W_e1474.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1478 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe14ac : word) = Some W_e1478.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e147c : forall segs, s1b_ok segs = true -> fetch_word segs (0xe14b0 : word) = Some W_e147c.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1480 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe14b4 : word) = Some W_e1480.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e1484 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe14b8 : word) = Some W_e1484.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3530 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe3564 : word) = Some W_e3530.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3534 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe3568 : word) = Some W_e3534.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.
Lemma F_e3538 : forall segs, s1b_ok segs = true -> fetch_word segs (0xe356c : word) = Some W_e3538.
Proof. intros segs H. apply (code_sound segs H). vm_refl. Qed.

Lemma img_10040_4 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65600) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 6)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_10050_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65616) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 65600)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_10078_4 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65656) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_100b0_4 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65712) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_100e8_4 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65768) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_10120_4 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65824) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_10158_4 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65880) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382482)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_10190_4 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65936) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382480)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_101c8_4 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 65992) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1685382481)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_101f0_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 66032) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_10200_4 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 66048) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_10238_4 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 66104) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1879048195)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_ece98_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 970440) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_ecea0_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 970448) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 415208)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_ecea8_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 970456) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 849808)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_eceb0_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 970464) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 852140)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_ed060_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 970896) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1050088)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_ed068_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 970904) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1182016)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_ed070_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 970912) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1182008)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_ed078_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 970920) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 945944)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_ed080_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 970928) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 945928)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_ee450_4 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 976000) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 131072)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_1005d0_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 1181392) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_1005e0_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 1181408) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_1005e8_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 1181416) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_100980_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 1182000) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_1009a8_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 1182040) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_1009c0_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 1182064) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_ed088_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 970936) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 1181992)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
Lemma img_e6ed8_8 : forall segs, s1b_ok segs = true -> rdn segs (fun _ => None) (Z_to_bv 64 945928) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 602300)).
Proof. intros segs H. apply (img_sound segs H). vm_refl. Qed.
