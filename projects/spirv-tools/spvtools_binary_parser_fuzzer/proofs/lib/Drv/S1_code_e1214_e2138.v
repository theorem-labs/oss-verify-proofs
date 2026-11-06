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

Definition W_e1214 : bv 32 := 0x08b50663.

Definition W_e1218 : bv 32 := 0x00a606b3.

Definition W_e121c : bv 32 := 0x00161713.

Definition W_e1220 : bv 32 := 0x40d586b3.

Definition W_e1224 : bv 32 := 0x40e00733.

Definition W_e1228 : bv 32 := 0x04d77063.

Definition W_e1268 : bv 32 := 0xba9ff06f.

Definition W_e1390 : bv 32 := 0x0e060a63.

Definition W_e1394 : bv 32 := 0x00b50023.

Definition W_e1398 : bv 32 := 0x00c506b3.

Definition W_e139c : bv 32 := 0x00300713.

Definition W_e13a0 : bv 32 := 0xfeb68fa3.

Definition W_e13a4 : bv 32 := 0x0ee66063.

Definition W_e13a8 : bv 32 := 0x00b500a3.

Definition W_e13ac : bv 32 := 0x00b50123.

Definition W_e13b0 : bv 32 := 0x00700713.

Definition W_e13b4 : bv 32 := 0xfeb68ea3.

Definition W_e13b8 : bv 32 := 0xfeb68f23.

Definition W_e13bc : bv 32 := 0x0ce66463.

Definition W_e13c0 : bv 32 := 0x00b501a3.

Definition W_e13c4 : bv 32 := 0x00900793.

Definition W_e13c8 : bv 32 := 0xfeb68e23.

Definition W_e13cc : bv 32 := 0x0af66c63.

Definition W_e13d0 : bv 32 := 0x40a006bb.

Definition W_e13d4 : bv 32 := 0x03859813.

Definition W_e13d8 : bv 32 := 0x101015b7.

Definition W_e13dc : bv 32 := 0x0036f693.

Definition W_e13e0 : bv 32 := 0x00459713.

Definition W_e13e4 : bv 32 := 0x40d60633.

Definition W_e13e8 : bv 32 := 0x00d505b3.

Definition W_e13ec : bv 32 := 0x10070693.

Definition W_e13f0 : bv 32 := 0xffc67713.

Definition W_e13f4 : bv 32 := 0x02d83633.

Definition W_e13f8 : bv 32 := 0x00c5a023.

Definition W_e13fc : bv 32 := 0x00e586b3.

Definition W_e1400 : bv 32 := 0xfec6ae23.

Definition W_e1404 : bv 32 := 0x08f76063.

Definition W_e1408 : bv 32 := 0x00c5a223.

Definition W_e140c : bv 32 := 0x00c5a423.

Definition W_e1410 : bv 32 := 0x01900793.

Definition W_e1414 : bv 32 := 0xfec6aa23.

Definition W_e1418 : bv 32 := 0xfec6ac23.

Definition W_e141c : bv 32 := 0x06f76463.

Definition W_e1420 : bv 32 := 0x00c5a623.

Definition W_e1424 : bv 32 := 0x00c5a823.

Definition W_e1428 : bv 32 := 0x00c5aa23.

Definition W_e142c : bv 32 := 0x00c5ac23.

Definition W_e1430 : bv 32 := 0x0045f793.

Definition W_e1434 : bv 32 := 0x02000813.

Definition W_e1438 : bv 32 := 0x01878793.

Definition W_e143c : bv 32 := 0x40f70733.

Definition W_e1440 : bv 32 := 0xfec6a223.

Definition W_e1444 : bv 32 := 0xfec6a423.

Definition W_e1448 : bv 32 := 0xfec6a623.

Definition W_e144c : bv 32 := 0xfec6a823.

Definition W_e1450 : bv 32 := 0x03076a63.

Definition W_e1454 : bv 32 := 0x02061613.

Definition W_e1458 : bv 32 := 0x00f585b3.

Definition W_e145c : bv 32 := 0x02065693.

Definition W_e1460 : bv 32 := 0x00d66633.

Definition W_e1464 : bv 32 := 0x01f00693.

Definition W_e1468 : bv 32 := 0x00c5b023.

Definition W_e146c : bv 32 := 0x00c5b423.

Definition W_e1470 : bv 32 := 0x00c5b823.

Definition W_e1474 : bv 32 := 0x00c5bc23.

Definition W_e1478 : bv 32 := 0xfe070713.

Definition W_e147c : bv 32 := 0x02058593.

Definition W_e1480 : bv 32 := 0xfee6e4e3.

Definition W_e1484 : bv 32 := 0x00008067.

Definition W_e1964 : bv 32 := 0xfe010113.
Lemma F_e1964 : fetch_word Plain.M.loaded_segments (0xe1998 : word) = Some W_e1964.
Proof. vm_refl. Qed.
Lemma D_e1964 : decode_any W_e1964 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1968 : bv 32 := 0x00113c23.
Lemma F_e1968 : fetch_word Plain.M.loaded_segments (0xe199c : word) = Some W_e1968.
Proof. vm_refl. Qed.
Lemma D_e1968 : decode_any W_e1968 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_e196c : bv 32 := 0x00813823.
Lemma F_e196c : fetch_word Plain.M.loaded_segments (0xe19a0 : word) = Some W_e196c.
Proof. vm_refl. Qed.
Lemma D_e196c : decode_any W_e196c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1970 : bv 32 := 0x00913423.
Lemma F_e1970 : fetch_word Plain.M.loaded_segments (0xe19a4 : word) = Some W_e1970.
Proof. vm_refl. Qed.
Lemma D_e1970 : decode_any W_e1970 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1974 : bv 32 := 0x00058413.
Lemma F_e1974 : fetch_word Plain.M.loaded_segments (0xe19a8 : word) = Some W_e1974.
Proof. vm_refl. Qed.
Lemma D_e1974 : decode_any W_e1974 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1978 : bv 32 := 0x00050493.
Lemma F_e1978 : fetch_word Plain.M.loaded_segments (0xe19ac : word) = Some W_e1978.
Proof. vm_refl. Qed.
Lemma D_e1978 : decode_any W_e1978 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e197c : bv 32 := 0x00000593.
Lemma F_e197c : fetch_word Plain.M.loaded_segments (0xe19b0 : word) = Some W_e197c.
Proof. vm_refl. Qed.
Lemma D_e197c : decode_any W_e197c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1980 : bv 32 := 0x00040613.
Lemma F_e1980 : fetch_word Plain.M.loaded_segments (0xe19b4 : word) = Some W_e1980.
Proof. vm_refl. Qed.
Lemma D_e1980 : decode_any W_e1980 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1984 : bv 32 := 0xb90ff0ef.
Lemma F_e1984 : fetch_word Plain.M.loaded_segments (0xe19b8 : word) = Some W_e1984.
Proof. vm_refl. Qed.
Lemma D_e1984 : decode_any W_e1984 = Some (Jal 1 2093968, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1988 : bv 32 := 0x00050463.
Lemma F_e1988 : fetch_word Plain.M.loaded_segments (0xe19bc : word) = Some W_e1988.
Proof. vm_refl. Qed.
Lemma D_e1988 : decode_any W_e1988 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e198c : bv 32 := 0x40950433.
Lemma F_e198c : fetch_word Plain.M.loaded_segments (0xe19c0 : word) = Some W_e198c.
Proof. vm_refl. Qed.
Lemma D_e198c : decode_any W_e198c = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1990 : bv 32 := 0x00040513.
Lemma F_e1990 : fetch_word Plain.M.loaded_segments (0xe19c4 : word) = Some W_e1990.
Proof. vm_refl. Qed.
Lemma D_e1990 : decode_any W_e1990 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1994 : bv 32 := 0x01813083.
Lemma F_e1994 : fetch_word Plain.M.loaded_segments (0xe19c8 : word) = Some W_e1994.
Proof. vm_refl. Qed.
Lemma D_e1994 : decode_any W_e1994 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1998 : bv 32 := 0x01013403.
Lemma F_e1998 : fetch_word Plain.M.loaded_segments (0xe19cc : word) = Some W_e1998.
Proof. vm_refl. Qed.
Lemma D_e1998 : decode_any W_e1998 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_e199c : bv 32 := 0x00813483.
Lemma F_e199c : fetch_word Plain.M.loaded_segments (0xe19d0 : word) = Some W_e199c.
Proof. vm_refl. Qed.
Lemma D_e199c : decode_any W_e199c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_e19a0 : bv 32 := 0x02010113.
Lemma F_e19a0 : fetch_word Plain.M.loaded_segments (0xe19d4 : word) = Some W_e19a0.
Proof. vm_refl. Qed.
Lemma D_e19a0 : decode_any W_e19a0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_e19a4 : bv 32 := 0x00008067.
Lemma F_e19a4 : fetch_word Plain.M.loaded_segments (0xe19d8 : word) = Some W_e19a4.
Proof. vm_refl. Qed.
Lemma D_e19a4 : decode_any W_e19a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1dfc : bv 32 := 0x00050893.
Lemma F_e1dfc : fetch_word Plain.M.loaded_segments (0xe1e30 : word) = Some W_e1dfc.
Proof. vm_refl. Qed.
Lemma D_e1dfc : decode_any W_e1dfc = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1e00 : bv 32 := 0x00058513.
Lemma F_e1e00 : fetch_word Plain.M.loaded_segments (0xe1e34 : word) = Some W_e1e00.
Proof. vm_refl. Qed.
Lemma D_e1e00 : decode_any W_e1e00 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1e04 : bv 32 := 0x00060593.
Lemma F_e1e04 : fetch_word Plain.M.loaded_segments (0xe1e38 : word) = Some W_e1e04.
Proof. vm_refl. Qed.
Lemma D_e1e04 : decode_any W_e1e04 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1e08 : bv 32 := 0x00068613.
Lemma F_e1e08 : fetch_word Plain.M.loaded_segments (0xe1e3c : word) = Some W_e1e08.
Proof. vm_refl. Qed.
Lemma D_e1e08 : decode_any W_e1e08 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1e0c : bv 32 := 0x00070693.
Lemma F_e1e0c : fetch_word Plain.M.loaded_segments (0xe1e40 : word) = Some W_e1e0c.
Proof. vm_refl. Qed.
Lemma D_e1e0c : decode_any W_e1e0c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1e10 : bv 32 := 0x00078713.
Lemma F_e1e10 : fetch_word Plain.M.loaded_segments (0xe1e44 : word) = Some W_e1e10.
Proof. vm_refl. Qed.
Lemma D_e1e10 : decode_any W_e1e10 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1e14 : bv 32 := 0x00080793.
Lemma F_e1e14 : fetch_word Plain.M.loaded_segments (0xe1e48 : word) = Some W_e1e14.
Proof. vm_refl. Qed.
Lemma D_e1e14 : decode_any W_e1e14 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1e18 : bv 32 := 0x00000073.
Lemma F_e1e18 : fetch_word Plain.M.loaded_segments (0xe1e4c : word) = Some W_e1e18.
Proof. vm_refl. Qed.

Lemma E_e1e18 : is_ecall W_e1e18 = true.
Proof. reflexivity. Qed.

Definition W_e1e1c : bv 32 := 0x00008067.
Lemma F_e1e1c : fetch_word Plain.M.loaded_segments (0xe1e50 : word) = Some W_e1e1c.
Proof. vm_refl. Qed.
Lemma D_e1e1c : decode_any W_e1e1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_e1e20 : bv 32 := 0xfddff06f.
Lemma F_e1e20 : fetch_word Plain.M.loaded_segments (0xe1e54 : word) = Some W_e1e20.
Proof. vm_refl. Qed.
Lemma D_e1e20 : decode_any W_e1e20 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.
