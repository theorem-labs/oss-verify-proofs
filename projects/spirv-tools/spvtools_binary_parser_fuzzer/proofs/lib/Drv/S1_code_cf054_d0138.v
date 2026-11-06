(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_cf750 : bv 32 := 0x00008067.

Definition W_cf754 : bv 32 := 0xe8010113.

Definition W_cf758 : bv 32 := 0x16113c23.

Definition W_cf75c : bv 32 := 0x16813823.

Definition W_cf760 : bv 32 := 0x16913423.

Definition W_cf764 : bv 32 := 0x17213023.

Definition W_cf768 : bv 32 := 0x00058413.

Definition W_cf76c : bv 32 := 0x00050493.

Definition W_cf770 : bv 32 := 0x03010513.

Definition W_cf774 : bv 32 := 0x13000613.

Definition W_cf778 : bv 32 := 0x00000593.

Definition W_cf77c : bv 32 := 0x409110ef.

Definition W_cf780 : bv 32 := 0x0001e517.

Definition W_cf784 : bv 32 := 0x8d053503.

Definition W_cf788 : bv 32 := 0x00953023.

Definition W_cf78c : bv 32 := 0x0004b503.

Definition W_cf790 : bv 32 := 0x00848493.

Definition W_cf794 : bv 32 := 0xfe051ce3.

Definition W_cf798 : bv 32 := 0x00051517.

Definition W_cf79c : bv 32 := 0x17050913.

Definition W_cf7a0 : bv 32 := 0x00993423.

Definition W_cf7a4 : bv 32 := 0x0004b583.

Definition W_cf7a8 : bv 32 := 0x04058c63.

Definition W_cf7ac : bv 32 := 0x01048493.

Definition W_cf7b0 : bv 32 := 0x02500513.

Definition W_cf7b4 : bv 32 := 0x03010613.

Definition W_cf7b8 : bv 32 := 0x0100006f.

Definition W_cf7bc : bv 32 := 0x0004b583.

Definition W_cf7c0 : bv 32 := 0x01048493.

Definition W_cf7c4 : bv 32 := 0x00058e63.

Definition W_cf7c8 : bv 32 := 0xfeb56ae3.

Definition W_cf7cc : bv 32 := 0xff84b683.

Definition W_cf7d0 : bv 32 := 0x00359593.

Definition W_cf7d4 : bv 32 := 0x00b605b3.

Definition W_cf7d8 : bv 32 := 0x00d5b023.

Definition W_cf7dc : bv 32 := 0xfe1ff06f.

Definition W_cf7e0 : bv 32 := 0x0b013583.

Definition W_cf7e4 : bv 32 := 0x13013503.

Definition W_cf7e8 : bv 32 := 0x00051617.

Definition W_cf7ec : bv 32 := 0x18b63423.

Definition W_cf7f0 : bv 32 := 0x00050c63.

Definition W_cf808 : bv 32 := 0x06013503.

Definition W_cf80c : bv 32 := 0x02a93823.

Definition W_cf810 : bv 32 := 0x00041463.

Definition W_cf818 : bv 32 := 0x00041663.

Definition W_cf824 : bv 32 := 0x0001e517.

Definition W_cf828 : bv 32 := 0x83453583.

Definition W_cf82c : bv 32 := 0x0001e517.

Definition W_cf830 : bv 32 := 0x83453503.

Definition W_cf834 : bv 32 := 0x0085b023.

Definition W_cf838 : bv 32 := 0x00140593.

Definition W_cf83c : bv 32 := 0x00853023.

Definition W_cf840 : bv 32 := 0x02f00613.

Definition W_cf844 : bv 32 := 0x00c0006f.

Definition W_cf848 : bv 32 := 0x00b53023.

Definition W_cf84c : bv 32 := 0x00158593.

Definition W_cf850 : bv 32 := 0xfff5c683.

Definition W_cf854 : bv 32 := 0xfec68ae3.

Definition W_cf858 : bv 32 := 0xfe069ae3.

Definition W_cf85c : bv 32 := 0x03010513.

Definition W_cf860 : bv 32 := 0x214000ef.

Definition W_cf864 : bv 32 := 0x0f813503.

Definition W_cf868 : bv 32 := 0x1ad000ef.

Definition W_cf86c : bv 32 := 0x08813503.

Definition W_cf870 : bv 32 := 0x09013583.

Definition W_cf874 : bv 32 := 0x00b51c63.

Definition W_cf878 : bv 32 := 0x09813503.

Definition W_cf87c : bv 32 := 0x0a013583.

Definition W_cf880 : bv 32 := 0x00b51663.

Definition W_cf884 : bv 32 := 0x0e813503.

Definition W_cf888 : bv 32 := 0x0e050063.

Definition W_cf968 : bv 32 := 0x17813083.

Definition W_cf96c : bv 32 := 0x17013403.

Definition W_cf970 : bv 32 := 0x16813483.

Definition W_cf974 : bv 32 := 0x16013903.

Definition W_cf978 : bv 32 := 0x18010113.

Definition W_cf97c : bv 32 := 0x00008067.

Definition W_cf980 : bv 32 := 0xfe010113.

Definition W_cf984 : bv 32 := 0x00113c23.

Definition W_cf988 : bv 32 := 0x00813823.

Definition W_cf98c : bv 32 := 0x00913423.

Definition W_cf990 : bv 32 := 0xdc1ff0ef.

Definition W_cf994 : bv 32 := 0x0001d517.

Definition W_cf998 : bv 32 := 0x0001d597.

Definition W_cf99c : bv 32 := 0x6d453403.

Definition W_cf9a0 : bv 32 := 0x6d85b483.

Definition W_cf9a4 : bv 32 := 0x0084fa63.

Definition W_cf9a8 : bv 32 := 0x0004b503.

Definition W_cf9ac : bv 32 := 0x000500e7.

Definition W_cf9b0 : bv 32 := 0x00848493.

Definition W_cf9b4 : bv 32 := 0xfe84eae3.

Definition W_cf9b8 : bv 32 := 0x01813083.

Definition W_cf9bc : bv 32 := 0x01013403.

Definition W_cf9c0 : bv 32 := 0x00813483.

Definition W_cf9c4 : bv 32 := 0x02010113.

Definition W_cf9c8 : bv 32 := 0x00008067.

Definition W_cf9cc : bv 32 := 0xfe010113.

Definition W_cf9d0 : bv 32 := 0x00113c23.

Definition W_cf9d4 : bv 32 := 0x00813823.

Definition W_cf9d8 : bv 32 := 0x00913423.

Definition W_cf9dc : bv 32 := 0x01213023.

Definition W_cf9e0 : bv 32 := 0x00060413.

Definition W_cf9e4 : bv 32 := 0x00058493.

Definition W_cf9e8 : bv 32 := 0x00050913.

Definition W_cf9ec : bv 32 := 0x00063583.

Definition W_cf9f0 : bv 32 := 0x00349513.

Definition W_cf9f4 : bv 32 := 0x00a60533.

Definition W_cf9f8 : bv 32 := 0x00850513.

Definition W_cf9fc : bv 32 := 0xd59ff0ef.

Definition W_cfa00 : bv 32 := 0x00000517.

Definition W_cfa04 : bv 32 := 0x02c50313.

Definition W_cfa08 : bv 32 := 0x00090513.

Definition W_cfa0c : bv 32 := 0x00048593.

Definition W_cfa10 : bv 32 := 0x00040613.

Definition W_cfa14 : bv 32 := 0x01813083.

Definition W_cfa18 : bv 32 := 0x01013403.

Definition W_cfa1c : bv 32 := 0x00813483.

Definition W_cfa20 : bv 32 := 0x00013903.

Definition W_cfa24 : bv 32 := 0x02010113.

Definition W_cfa28 : bv 32 := 0x00030067.

Definition W_cfa2c : bv 32 := 0xfd010113.

Definition W_cfa30 : bv 32 := 0x02113423.

Definition W_cfa34 : bv 32 := 0x02813023.

Definition W_cfa38 : bv 32 := 0x00913c23.

Definition W_cfa3c : bv 32 := 0x01213823.

Definition W_cfa40 : bv 32 := 0x01313423.

Definition W_cfa44 : bv 32 := 0x00060413.

Definition W_cfa48 : bv 32 := 0x00058493.

Definition W_cfa4c : bv 32 := 0x00050913.

Definition W_cfa50 : bv 32 := 0x00359513.

Definition W_cfa54 : bv 32 := 0x00a60533.

Definition W_cfa58 : bv 32 := 0x00850993.

Definition W_cfa5c : bv 32 := 0xf25ff0ef.

Definition W_cfa60 : bv 32 := 0x00048513.

Definition W_cfa64 : bv 32 := 0x00040593.

Definition W_cfa68 : bv 32 := 0x00098613.

Definition W_cfa6c : bv 32 := 0x000900e7.

























































































































Definition W_cfdd8 : bv 32 := 0x00000073.
Lemma F_cfdd8 : fetch_word Plain.M.loaded_segments (0xcfe0c : word) = Some W_cfdd8.
Proof. vm_refl. Qed.

Lemma E_cfdd8 : is_ecall W_cfdd8 = true.
Proof. reflexivity. Qed.

Definition W_cffb0 : bv 32 := 0xfd010113.

Definition W_cffb4 : bv 32 := 0x02113423.

Definition W_cffb8 : bv 32 := 0x02813023.

Definition W_cffbc : bv 32 := 0x00913c23.

Definition W_cffc0 : bv 32 := 0x01213823.

Definition W_cffc4 : bv 32 := 0x01313423.

Definition W_cffc8 : bv 32 := 0x00050493.

Definition W_cffcc : bv 32 := 0x00050517.

Definition W_cffd0 : bv 32 := 0x70050993.

Definition W_cffd4 : bv 32 := 0x00498413.

Definition W_cffd8 : bv 32 := 0x00040513.

Definition W_cffdc : bv 32 := 0x325110ef.

Definition W_cffe0 : bv 32 := 0x0009c503.

Definition W_cffe4 : bv 32 := 0xfff00913.

Definition W_cffe8 : bv 32 := 0x06051263.

Definition W_cffec : bv 32 := 0x0109b503.

Definition W_cfff0 : bv 32 := 0x00051663.

Definition W_cfff4 : bv 32 := 0x01898513.

Definition W_cfff8 : bv 32 := 0x00a9b823.

Definition W_cfffc : bv 32 := 0x0089a583.

Definition W_d0000 : bv 32 := 0x02000613.

Definition W_d0004 : bv 32 := 0x02c59263.

Definition W_d0008 : bv 32 := 0x20800513.

Definition W_d000c : bv 32 := 0x00100593.

Definition W_d0010 : bv 32 := 0x761010ef.

Definition W_d0014 : bv 32 := 0x02050c63.

Definition W_d0018 : bv 32 := 0x00000593.

Definition W_d001c : bv 32 := 0x0109b603.

Definition W_d0020 : bv 32 := 0x00c53023.

Definition W_d0024 : bv 32 := 0x00a9b823.

Definition W_d0028 : bv 32 := 0x00000913.

Definition W_d002c : bv 32 := 0x00359613.

Definition W_d0030 : bv 32 := 0x00c50533.

Definition W_d0034 : bv 32 := 0x00000617.

Definition W_d0038 : bv 32 := 0x00158593.

Definition W_d003c : bv 32 := 0x04060613.

Definition W_d0040 : bv 32 := 0x00c53423.

Definition W_d0044 : bv 32 := 0x10953423.

Definition W_d0048 : bv 32 := 0x00b9a423.

Definition W_d004c : bv 32 := 0x00040513.

Definition W_d0050 : bv 32 := 0x539110ef.

Definition W_d0054 : bv 32 := 0x00090513.

Definition W_d0058 : bv 32 := 0x02813083.

Definition W_d005c : bv 32 := 0x02013403.

Definition W_d0060 : bv 32 := 0x01813483.

Definition W_d0064 : bv 32 := 0x01013903.

Definition W_d0068 : bv 32 := 0x00813983.

Definition W_d006c : bv 32 := 0x03010113.

Definition W_d0070 : bv 32 := 0x00008067.

Definition W_d0074 : bv 32 := 0x00050067.

