(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_U1_code_d1054_d2138 () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions9bv_eq_decC35stdpp6option=option_eq_decC35stdpp4base:decide_relK47Corelib4Init5Logic2eq01C35stdpp9decidable;bool_decideC35stdpp9decidableEbool_decide_eq_true_1K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrImgWTgt_spvtools_binary_parser_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01c59OSSVerify5KrLib3DrvCU1_code_d1054_d21387W_d1b30C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib3DrvCU1_code_d1054_d21387W_d1fe0C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK4ELinuxProcessSemantics5Riscv5Instr5instr01K47Corelib4Init9Datatypes4prod01C35stdpp9decidable;prod_eq_decI4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics5Riscv5Instr<instr_eq_decC45stdpp7numbers1Z6eq_decc59OSSVerify5KrLib3DrvCU1_code_d1054_d21387W_d1fe4C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr0;c59OSSVerify5KrLib3DrvCU1_code_d1054_d21387W_d1fe8C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr05K4ELinuxProcessSemantics5Riscv5Instr;branch_cond05c59OSSVerify5KrLib3DrvCU1_code_d1054_d21387W_d2014C1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics5Riscv5Instr5instr04K47Corelib7Numbers7BinNums1Z01".
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_d14a8 : bv 32 := 0x00008067.

Definition W_d14ac : bv 32 := 0xe8010113.

Definition W_d14b0 : bv 32 := 0x16113c23.

Definition W_d14b4 : bv 32 := 0x16813823.

Definition W_d14b8 : bv 32 := 0x16913423.

Definition W_d14bc : bv 32 := 0x17213023.

Definition W_d14c0 : bv 32 := 0x00058413.

Definition W_d14c4 : bv 32 := 0x00050493.

Definition W_d14c8 : bv 32 := 0x03010513.

Definition W_d14cc : bv 32 := 0x13000613.

Definition W_d14d0 : bv 32 := 0x00000593.

Definition W_d14d4 : bv 32 := 0x409110ef.

Definition W_d14d8 : bv 32 := 0x0001e517.

Definition W_d14dc : bv 32 := 0x8d053503.

Definition W_d14e0 : bv 32 := 0x00953023.

Definition W_d14e4 : bv 32 := 0x0004b503.

Definition W_d14e8 : bv 32 := 0x00848493.

Definition W_d14ec : bv 32 := 0xfe051ce3.

Definition W_d14f0 : bv 32 := 0x00051517.

Definition W_d14f4 : bv 32 := 0x17850913.

Definition W_d14f8 : bv 32 := 0x00993423.

Definition W_d14fc : bv 32 := 0x0004b583.

Definition W_d1500 : bv 32 := 0x04058c63.

Definition W_d1504 : bv 32 := 0x01048493.

Definition W_d1508 : bv 32 := 0x02500513.

Definition W_d150c : bv 32 := 0x03010613.

Definition W_d1510 : bv 32 := 0x0100006f.

Definition W_d1514 : bv 32 := 0x0004b583.

Definition W_d1518 : bv 32 := 0x01048493.

Definition W_d151c : bv 32 := 0x00058e63.

Definition W_d1520 : bv 32 := 0xfeb56ae3.

Definition W_d1524 : bv 32 := 0xff84b683.

Definition W_d1528 : bv 32 := 0x00359593.

Definition W_d152c : bv 32 := 0x00b605b3.

Definition W_d1530 : bv 32 := 0x00d5b023.

Definition W_d1534 : bv 32 := 0xfe1ff06f.

Definition W_d1538 : bv 32 := 0x0b013583.

Definition W_d153c : bv 32 := 0x13013503.

Definition W_d1540 : bv 32 := 0x00051617.

Definition W_d1544 : bv 32 := 0x18b63823.

Definition W_d1548 : bv 32 := 0x00050c63.

Definition W_d1560 : bv 32 := 0x06013503.

Definition W_d1564 : bv 32 := 0x02a93823.

Definition W_d1568 : bv 32 := 0x00041463.

Definition W_d1570 : bv 32 := 0x00041663.

Definition W_d157c : bv 32 := 0x0001e517.

Definition W_d1580 : bv 32 := 0x83453583.

Definition W_d1584 : bv 32 := 0x0001e517.

Definition W_d1588 : bv 32 := 0x83453503.

Definition W_d158c : bv 32 := 0x0085b023.

Definition W_d1590 : bv 32 := 0x00140593.

Definition W_d1594 : bv 32 := 0x00853023.

Definition W_d1598 : bv 32 := 0x02f00613.

Definition W_d159c : bv 32 := 0x00c0006f.

Definition W_d15a0 : bv 32 := 0x00b53023.

Definition W_d15a4 : bv 32 := 0x00158593.

Definition W_d15a8 : bv 32 := 0xfff5c683.

Definition W_d15ac : bv 32 := 0xfec68ae3.

Definition W_d15b0 : bv 32 := 0xfe069ae3.

Definition W_d15b4 : bv 32 := 0x03010513.

Definition W_d15b8 : bv 32 := 0x214000ef.

Definition W_d15bc : bv 32 := 0x0f813503.

Definition W_d15c0 : bv 32 := 0x1ad000ef.

Definition W_d15c4 : bv 32 := 0x08813503.

Definition W_d15c8 : bv 32 := 0x09013583.

Definition W_d15cc : bv 32 := 0x00b51c63.

Definition W_d15d0 : bv 32 := 0x09813503.

Definition W_d15d4 : bv 32 := 0x0a013583.

Definition W_d15d8 : bv 32 := 0x00b51663.

Definition W_d15dc : bv 32 := 0x0e813503.

Definition W_d15e0 : bv 32 := 0x0e050063.

Definition W_d16c0 : bv 32 := 0x17813083.

Definition W_d16c4 : bv 32 := 0x17013403.

Definition W_d16c8 : bv 32 := 0x16813483.

Definition W_d16cc : bv 32 := 0x16013903.

Definition W_d16d0 : bv 32 := 0x18010113.

Definition W_d16d4 : bv 32 := 0x00008067.

Definition W_d16d8 : bv 32 := 0xfe010113.

Definition W_d16dc : bv 32 := 0x00113c23.

Definition W_d16e0 : bv 32 := 0x00813823.

Definition W_d16e4 : bv 32 := 0x00913423.

Definition W_d16e8 : bv 32 := 0xdc1ff0ef.

Definition W_d16ec : bv 32 := 0x0001d517.

Definition W_d16f0 : bv 32 := 0x0001d597.

Definition W_d16f4 : bv 32 := 0x6d453403.

Definition W_d16f8 : bv 32 := 0x6d85b483.

Definition W_d16fc : bv 32 := 0x0084fa63.

Definition W_d1700 : bv 32 := 0x0004b503.

Definition W_d1704 : bv 32 := 0x000500e7.

Definition W_d1708 : bv 32 := 0x00848493.

Definition W_d170c : bv 32 := 0xfe84eae3.

Definition W_d1710 : bv 32 := 0x01813083.

Definition W_d1714 : bv 32 := 0x01013403.

Definition W_d1718 : bv 32 := 0x00813483.

Definition W_d171c : bv 32 := 0x02010113.

Definition W_d1720 : bv 32 := 0x00008067.

Definition W_d1724 : bv 32 := 0xfe010113.

Definition W_d1728 : bv 32 := 0x00113c23.

Definition W_d172c : bv 32 := 0x00813823.

Definition W_d1730 : bv 32 := 0x00913423.

Definition W_d1734 : bv 32 := 0x01213023.

Definition W_d1738 : bv 32 := 0x00060413.

Definition W_d173c : bv 32 := 0x00058493.

Definition W_d1740 : bv 32 := 0x00050913.

Definition W_d1744 : bv 32 := 0x00063583.

Definition W_d1748 : bv 32 := 0x00349513.

Definition W_d174c : bv 32 := 0x00a60533.

Definition W_d1750 : bv 32 := 0x00850513.

Definition W_d1754 : bv 32 := 0xd59ff0ef.

Definition W_d1758 : bv 32 := 0x00000517.

Definition W_d175c : bv 32 := 0x02c50313.

Definition W_d1760 : bv 32 := 0x00090513.

Definition W_d1764 : bv 32 := 0x00048593.

Definition W_d1768 : bv 32 := 0x00040613.

Definition W_d176c : bv 32 := 0x01813083.

Definition W_d1770 : bv 32 := 0x01013403.

Definition W_d1774 : bv 32 := 0x00813483.

Definition W_d1778 : bv 32 := 0x00013903.

Definition W_d177c : bv 32 := 0x02010113.

Definition W_d1780 : bv 32 := 0x00030067.

Definition W_d1784 : bv 32 := 0xfd010113.

Definition W_d1788 : bv 32 := 0x02113423.

Definition W_d178c : bv 32 := 0x02813023.

Definition W_d1790 : bv 32 := 0x00913c23.

Definition W_d1794 : bv 32 := 0x01213823.

Definition W_d1798 : bv 32 := 0x01313423.

Definition W_d179c : bv 32 := 0x00060413.

Definition W_d17a0 : bv 32 := 0x00058493.

Definition W_d17a4 : bv 32 := 0x00050913.

Definition W_d17a8 : bv 32 := 0x00359513.

Definition W_d17ac : bv 32 := 0x00a60533.

Definition W_d17b0 : bv 32 := 0x00850993.

Definition W_d17b4 : bv 32 := 0xf25ff0ef.

Definition W_d17b8 : bv 32 := 0x00048513.

Definition W_d17bc : bv 32 := 0x00040593.

Definition W_d17c0 : bv 32 := 0x00098613.

Definition W_d17c4 : bv 32 := 0x000900e7.

























































































































Definition W_d1b30 : bv 32 := 0x00000073.
Lemma F_d1b30 : fetch_word Ubsan.M.loaded_segments (0xd1b64 : word) = Some W_d1b30.
Proof. vm_refl. Qed.

Lemma E_d1b30 : is_ecall W_d1b30 = true.
Proof. reflexivity. Qed.

Definition W_d1d08 : bv 32 := 0xfd010113.

Definition W_d1d0c : bv 32 := 0x02113423.

Definition W_d1d10 : bv 32 := 0x02813023.

Definition W_d1d14 : bv 32 := 0x00913c23.

Definition W_d1d18 : bv 32 := 0x01213823.

Definition W_d1d1c : bv 32 := 0x01313423.

Definition W_d1d20 : bv 32 := 0x00050493.

Definition W_d1d24 : bv 32 := 0x00050517.

Definition W_d1d28 : bv 32 := 0x70850993.

Definition W_d1d2c : bv 32 := 0x00498413.

Definition W_d1d30 : bv 32 := 0x00040513.

Definition W_d1d34 : bv 32 := 0x325110ef.

Definition W_d1d38 : bv 32 := 0x0009c503.

Definition W_d1d3c : bv 32 := 0xfff00913.

Definition W_d1d40 : bv 32 := 0x06051263.

Definition W_d1d44 : bv 32 := 0x0109b503.

Definition W_d1d48 : bv 32 := 0x00051663.

Definition W_d1d4c : bv 32 := 0x01898513.

Definition W_d1d50 : bv 32 := 0x00a9b823.

Definition W_d1d54 : bv 32 := 0x0089a583.

Definition W_d1d58 : bv 32 := 0x02000613.

Definition W_d1d5c : bv 32 := 0x02c59263.

Definition W_d1d60 : bv 32 := 0x20800513.

Definition W_d1d64 : bv 32 := 0x00100593.

Definition W_d1d68 : bv 32 := 0x761010ef.

Definition W_d1d6c : bv 32 := 0x02050c63.

Definition W_d1d70 : bv 32 := 0x00000593.

Definition W_d1d74 : bv 32 := 0x0109b603.

Definition W_d1d78 : bv 32 := 0x00c53023.

Definition W_d1d7c : bv 32 := 0x00a9b823.

Definition W_d1d80 : bv 32 := 0x00000913.

Definition W_d1d84 : bv 32 := 0x00359613.

Definition W_d1d88 : bv 32 := 0x00c50533.

Definition W_d1d8c : bv 32 := 0x00000617.

Definition W_d1d90 : bv 32 := 0x00158593.

Definition W_d1d94 : bv 32 := 0x04060613.

Definition W_d1d98 : bv 32 := 0x00c53423.

Definition W_d1d9c : bv 32 := 0x10953423.

Definition W_d1da0 : bv 32 := 0x00b9a423.

Definition W_d1da4 : bv 32 := 0x00040513.

Definition W_d1da8 : bv 32 := 0x539110ef.

Definition W_d1dac : bv 32 := 0x00090513.

Definition W_d1db0 : bv 32 := 0x02813083.

Definition W_d1db4 : bv 32 := 0x02013403.

Definition W_d1db8 : bv 32 := 0x01813483.

Definition W_d1dbc : bv 32 := 0x01013903.

Definition W_d1dc0 : bv 32 := 0x00813983.

Definition W_d1dc4 : bv 32 := 0x03010113.

Definition W_d1dc8 : bv 32 := 0x00008067.

Definition W_d1dcc : bv 32 := 0x00050067.

Definition W_d1f78 : bv 32 := 0xff010113.

Definition W_d1f7c : bv 32 := 0x00113423.

Definition W_d1f80 : bv 32 := 0x00050e63.

Definition W_d1f84 : bv 32 := 0x00050593.

Definition W_d1f88 : bv 32 := 0x0001d517.

Definition W_d1f8c : bv 32 := 0xe5453503.

Definition W_d1f90 : bv 32 := 0x00800613.

Definition W_d1f94 : bv 32 := 0x3d5100ef.

Definition W_d1f98 : bv 32 := 0x01c0006f.

Definition W_d1fb4 : bv 32 := 0x0001d517.

Definition W_d1fb8 : bv 32 := 0xe2853503.

Definition W_d1fbc : bv 32 := 0x000500a3.

Definition W_d1fc0 : bv 32 := 0x00053503.

Definition W_d1fc4 : bv 32 := 0x00020593.

Definition W_d1fc8 : bv 32 := 0xfea5b823.

Definition W_d1fcc : bv 32 := 0x00813083.

Definition W_d1fd0 : bv 32 := 0x01010113.

Definition W_d1fd4 : bv 32 := 0x00008067.

Definition W_d1fe0 : bv 32 := 0xfffff5b7.
Lemma F_d1fe0 : fetch_word Ubsan.M.loaded_segments (0xd2014 : word) = Some W_d1fe0.
Proof. vm_refl. Qed.
Lemma D_d1fe0 : decode_any W_d1fe0 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1fe4 : bv 32 := 0x0015859b.
Lemma F_d1fe4 : fetch_word Ubsan.M.loaded_segments (0xd2018 : word) = Some W_d1fe4.
Proof. vm_refl. Qed.
Lemma D_d1fe4 : decode_any W_d1fe4 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_d1fe8 : bv 32 := 0x02b56663.
Lemma F_d1fe8 : fetch_word Ubsan.M.loaded_segments (0xd201c : word) = Some W_d1fe8.
Proof. vm_refl. Qed.
Lemma D_d1fe8 : decode_any W_d1fe8 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_d2014 : bv 32 := 0x00008067.
Lemma F_d2014 : fetch_word Ubsan.M.loaded_segments (0xd2048 : word) = Some W_d2014.
Proof. vm_refl. Qed.
Lemma D_d2014 : decode_any W_d2014 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
