(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp RepRsa.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_cmp U_mpi_cmp_int U_mpi_cmp_int_z0 U_mpi_bitlen U_rsa_check_context U_rsa_check_pubkey.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0069dc2969cf13c7 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P0180821fe6137405 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P01fa347cacdbb71b 0 2 0 1 2 1P025940cbf495d11a 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P02c1fd35db700b63 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P02f81a49698da760 0 2 0 1 2 1P03958f0905d720e9 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P045723e2f1313d93 0 2 0 1 55 1P04597a00c72d46e8 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P049c2439284c9b44 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P0508aeddadfdeaa8 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P06b0006950db3f19 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P0795e0ee257cca81 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P07f16290ee3905cc 0 2 0 1 55 1P0835ccbae4deb526 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P086180eae100028a 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P089791dfaf061450 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P0a2012fb176caf32 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P0b2978ca2cb50e06 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P0bd5855dd23ec8c1 1 2 16 3 0 1 52 1 55 1 16 3 1 1 53 1 54 1 2 56 1 57 1P0bdfce4c6601ede6 0 2 0 1 32 1P0d1ca5f9bb0acc2d 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P0d939147227abdd7 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P0f74991b68b8a086 0 2 0 1 56 1P1103ef770496d530 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P11f0bb39bb31b0bf 0 2 0 1 32 1P148407ada14488b9 0 2 0 1 34 1P1669bd56376ea235 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P16a7bb47d3b347d6 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P170c1cef847e78e9 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P171492ccb1ac99a5 0 2 0 1 32 1P17f52b371580366d 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P18d63406062285d6 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P19a824cd13da2d72 0 2 0 1 33 1P19c0d46cc6ed3d8f 1 2 16 3 0 1 52 1 55 1 16 3 1 1 53 1 54 1 2 56 1 57 1P19c4503362b46ccd 0 2 0 1 29 1P19fd88ff47af8c54 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P1b76cb03606e00d5 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P1b8fc61915a19eb7 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P1c45f2436d926204 0 2 0 1 34 1P1ccf58fefce79ac8 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P1d1d9d2d05589b57 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P1d9b77d34a8539c6 1 2 16 3 0 1 54 1 57 1 16 3 1 1 55 1 56 1 2 58 1 59 1P1e32ba3e94d6ed7d 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P1e81bc6c517a9fae 0 2 0 1 31 1P1e92e781e7ea63d5 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P1ee83e49766d938f 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P1f38304570d8cb75 1 2 16 3 0 1 54 1 57 1 16 3 1 1 55 1 56 1 2 58 1 59 1P1fb24cc6b7fcaaf7 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P1fb7198fe434f4be 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P21427c80427c8a4a 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P221eaa7247efe2e1 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P222e19a28fad2dba 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P2234c6d246dad59e 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P2347b2aec26c33af 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P235dd9e887da67b5 0 2 0 1 32 1P239a198ab35d22e3 0 2 0 1 9 1P244f4f3f2796ac9d 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P24df60686387cdd2 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P253c9bd7eb403186 1 2 16 3 0 1 52 1 55 1 16 3 1 1 53 1 54 1 2 56 1 57 1P2557451cc450e7bd 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P25bc4b0b6ee0e9a0 0 2 0 1 31 1P25dc2764bfdf20fd 1 2 16 3 0 1 52 1 55 1 16 3 1 1 53 1 54 1 2 56 1 57 1P26abbb612ed2d2a1 1 2 16 3 0 1 56 1 59 1 16 3 1 1 57 1 58 1 2 60 1 61 1P2716d78701cc4700 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P27b59343524d7692 1 2 16 3 0 1 56 1 59 1 16 3 1 1 57 1 58 1 2 60 1 61 1P27be8829fddca5d8 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P281250ffef8fbbd0 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P286ea774224d8fea 0 2 0 1 55 1P2abb873667d1f0cd 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P2ae11680610a4a5d 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P2ae1fca0fff054e7 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P2b3a02f53c064504 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P2b40351c96c3d2c5 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P2c96c85b5edd4bb2 0 2 0 1 32 1P2d0671071f7a1cfa 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P2d0ebf19583deaa6 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P2d365f239c127da1 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P2d407dd0439caadd 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P2dd61a107ab8fa48 0 2 0 1 2 1P2e4dc8d642a5d5b8 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P2e5e05d7040467e2 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P2e71ad587fe803a1 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P2f0aed0c6bc86bae 0 2 0 1 33 1P2f8a6f28861d6de2 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P30f764360fbc13b8 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P318b420279bbd83b 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P3274936b1607c899 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P32c8ea8a5101ae9e 1 2 16 3 0 1 52 1 55 1 16 3 1 1 53 1 54 1 2 56 1 57 1P32d26dbe7563f6fb 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P331810976f9c415f 1 2 16 3 0 1 52 1 55 1 16 3 1 1 53 1 54 1 2 56 1 57 1P332b30f384cc932c 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P332c15df874fa299 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P3492edde02bef83c 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P34b981fc3b567cc8 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P35947c360857a69d 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P36a56a867a744dd8 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P371a47ce3ecb6b31 0 2 0 1 33 1P374d1fc44f1abc25 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P377622b8bbbf8298 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P3874b0dafafc71f7 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P3898d1784deef391 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P39d89e186fde8832 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P39f7b3c248613df3 1 2 16 3 1 1 57 1 58 1 16 5 47 1 48 1 49 1 56 1 59 1 2 60 1 61 1P3a69859498685f16 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P3b7e992113a2d06e 0 2 0 1 2 1P3c00f44be0918bdf 0 2 0 1 30 1P3c4e62dbcbc50780 1 2 16 3 1 1 55 1 56 1 16 5 45 1 46 1 47 1 54 1 57 1 2 58 1 59 1P3c66af3e8388461d 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P3c732d8f6b7c0599 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P3e52b735bc9e9901 1 2 16 3 1 1 53 1 54 1 16 5 43 1 44 1 45 1 52 1 55 1 2 56 1 57 1P3e913d4d6509435f 0 2 0 1 56 1P3f14c0ff064596b2 1 2 16 3 0 1 52 1 55 1 16 3 1 1 53 1 54 1 2 56 1 57 1N00bcc3073604e814N044eed8ac4dfd318N0ab01b5bf836566fN0f79e7b5ffd9f882N12b704c9c20e3337N15eb54713835411fN2028512f6027fe0bN202f2eb967167662N243297da3b5313e2N2f146601e268baf0N35448505b616bdb6N3b3238271b8917b7N3c567303f5d53c3e"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_rsa_complete () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "rsa_complete_post"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_st"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_head_cells"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_len"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_N"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_E"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.U.U_rsa_check_context.rsa_field_live"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.RSA_CTX_SIZE"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"].


Definition U_RSA_COMPLETE : Z := 0x2a404.
(* [comment removed for export] *)
Notation RSA_COMPLETE_STACK := 208 (only parsing).

Definition rsa_complete_post (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_rsa_complete ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O14.O13.O12.O11.R10.R?.R>.O10.O?.R=.R<.R;.R:.R9.R8.R7.R6.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R5.R4.R3.R2.)O4.(8.O14.)O3.(9.(2.&40.))R1.(:.O15.)))(4.(;.(<.(=.$>.$>.)(?.$>.$>.(10.(11.&40.O13.)+=0.)(11.&40.O13.))(12.(=.$>.$>.)))O1.R1.)(4.(13.O15.O1.R1.)(4.(14.O15.R1.)(15.O15.R1.O2.(11.&40.O13.))))))))))))))))))))))")
(* [comment removed for export] *).

Definition rsa_complete_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (LB : list blk) (C : Z) (r : rsa_st) (lo : Z),
  rsa_at segs m LB C r -> md_sg (r_N r) = 1 -> md_sg (r_E r) = 1 ->
  rsa_field_live (r_N r) -> rsa_field_live (r_E r) -> C + RSA_CTX_SIZE <= alloc_ceiling ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RSA_COMPLETE_STACK -> alloc_ceiling <= lo -> bv_unsigned sp mod 16 = 0 ->
  mem_inv segs m -> bv_unsigned ra mod 2 = 0 ->
  a0 = Z_to_bv 64 C ->
  evt segs (rsa_complete_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

(* [comment removed for export] *)
Ltac norm_lits :=
  repeat match goal with |- context [Z_to_bv 64 ?t] =>
    lazymatch t with
    | Zpos _ => fail | Z0 => fail | Zneg _ => fail
    | _ => let v := eval cbv in t in
           lazymatch v with Zpos _ => change t with v | Z0 => change t with v | Zneg _ => change t with v end
    end end.

(* [comment removed for export] *)
Ltac zcall segs Z0SPEC ENTRY ZC retpc spo lo MU WM :=
  let SP := fresh "SP" in
  pose proof Z0SPEC as SP; unfold mpi_cmp_int_z0_stmt, ENTRY in SP;
  eapply evt_cut; [ eapply SP with (lo := lo); rewrite ?(unsigned_lit spo) by lia;
    [ exact ZC | lia | lia | lia | eassumption | lia | lia | lia | lia | assumption | reflexivity | reflexivity ] | ];
  clear SP; cbv beta;
  let PO := fresh "PO" in let ms := fresh "ms" in
  intros ms PO; unfold mpi_cmp_int_post in PO; rewrite ?(unsigned_lit spo) in PO by lia;
  let mq := fresh "mq" in let MUq := fresh "MUq" in let WMq := fresh "WMq" in let MIq := fresh "MIq" in let STq := fresh "STq" in
  (flat constr:(PO) 20%nat; flclear PO; intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? mq -> MUq WMq MIq STq);
  replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]);
  after_callg segs MU WM MUq WMq.

Ltac cpl_z0 c sp lo off retpc mu wm :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with zc : rw_cells _ mx (c + off) _ |- _ =>
      zstep; zcall usegs U_mpi_cmp_int_z0_spec U_MPI_CMP_INT zc retpc (bv_unsigned sp + -176) lo mu wm
    end end.

Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L19815966384.3L24509946420.3L24926274299.3L35943095571.300000700>00?00@S1v1H1ES1v1H1ESS". (* [comment removed for export] *)
Lemma sgn01 : forall v, 0 <= v -> Z.sgn (v - 0) = 0 \/ Z.sgn (v - 0) = 1.
Proof. intros v H. destruct (Z.eq_dec v 0) as [E|E]; [left; rewrite Z.sgn_null; lia| right; rewrite Z.sgn_pos; lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L37546568455.3000006S1d2H0". (* [comment removed for export] *)
Lemma mpd_val_sg1 : forall d, md_sg d = 1 -> 0 <= mpd_val d.
Proof. intros d H. unfold mpd_val. rewrite H. pose proof (mpd_abs_nonneg d). unfold mpd_abs in *. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac cpl_run ex1 ex2 :=
  first [ lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ex1) _ _ _ _) => idtac end
        | lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ex2) _ _ _ _) => idtac end
        | zstep; norm_lits;
          try (let K := fresh "K" in if_cases K; zify_cond K; first [exfalso; cbv in K; lia | clear K]);
          cpl_run ex1 ex2 ].

Section CK.
  Context {L : heap_layout}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z).
  Hypothesis SLO : lo <= bv_unsigned sp - RSA_COMPLETE_STACK.
  Hypothesis ACL : alloc_ceiling <= lo.

  Notation POST := (rsa_complete_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).
  Notation SAVED := ([C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).

  Notation FRAME l0 l1 l2 l3 l4 l5 l6 l7 l8 := ([C8 l0; C8 l1; C8 l2; C8 l3; C8 l4; C8 l5; C8 l6; C8 l7; C8 l8;
      C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] : list cell).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L22706553362.3000009S2sp1a2Ha". (* [comment removed for export] *)
  Lemma cpl_epilogue : ltac2:(CDefT.buildp (gd_tbl_P_rsa_complete ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pl0,(2.&40.)Pl1,(2.&40.)Pl2,(2.&40.)Pl3,(2.&40.)Pl4,(2.&40.)Pl5,(2.&40.)Pl6,(2.&40.)Pl7,(2.&40.)Pl8,(2.&40.)Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Px0,(2.&40.)Px1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px2,(2.&40.)Px3,(2.&40.)Px4,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px8,(2.&40.)Px9,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(;.(<.(=.$>.$>.)(?.$>.$>.(10.(11.&40.Vsp,)+=0.)(11.&40.Vsp,))(12.(=.$>.$>.)))Vm,R26.)P,(13.$16.Vm,R27.)P,(14.$16.R28.)P,(15.$16.R29.Vlo,(17.(11.&40.Vsp,)-;0.))P,(18.$16.R2:.(17.(11.&40.Vsp,)-;0.)(<.$19.(1:.R29.)(<.$19.(1:.R28.)(<.$19.(1:.R27.)(<.$19.(1:.R26.)(<.$19.(1:.R25.)(<.$19.(1:.R24.)(<.$19.(1:.R23.)(<.$19.(1:.R22.)(<.$19.(1:.R21.)(<.$19.(1:.Vs11,)(<.$19.(1:.Vs10,)(<.$19.(1:.Vs9,)(<.$19.(1:.Vs8,)(<.$19.(1:.Vs7,)(<.$19.(1:.Vs6,)(<.$19.(1:.Vs5,)(<.$19.(1:.Vs4,)(<.$19.(1:.Vs3,)(<.$19.(1:.Vs2,)(<.$19.(1:.Vs1,)(<.$19.(1:.Vs0,)(<.$19.(1:.Vra,)(12.$19.))))))))))))))))))))))))(1;.$16.(1<.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,Vm,)(6.(7.R21.(1=.&40.(17.(11.&40.Vsp,)-;0.))Vgp,Vtp,R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)VF,(1=.&40.+2:630.)Vfc,(9.(2.&40.))R2;.(:.$16.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros MU WM MI ST FR.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    (* [comment removed for export] *)
    lx_run_tac (PLAN [] [] 40%N); lx_tree.
    all: try lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hi : mem_inv _ mx, Hs : stk _ mx lo (bv_unsigned sp) |- _ =>
           try rewrite (Z_to_bv_bv_unsigned sp);
           apply evt_done; unfold rsa_complete_post; flexi 16%nat;
           split; [reflexivity|];
           split; [eapply munch_weaken; [| exact Hm]; intros a Ha; clear -Ha; cbn in Ha |- *; lia|];
           split; [exact Hw|]; split; [exact Hi| exact Hs]
         end end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L22706553362.114L22706553362.3  L26008407122.92 L312740882.4    L64238623868.1  00000>00G00W00b00fS2ra2sp1C1a2HaS2sp1a2HaS2ra2sp2lo3SLO1CS2sp2lo3SLOS2sp". (* [comment removed for export] *)
  Lemma cpl_tail : ltac2:(CDefT.buildp (gd_tbl_P_rsa_complete ()) "Pm1,P,(2.&40.)(3.(2.&8.))Pl0,(2.&40.)Pl1,(2.&40.)Pl2,(2.&40.)Pl3,(2.&40.)Pl4,(2.&40.)Pl5,(2.&40.)Pl6,(2.&40.)Pl7,(2.&40.)Pl8,(2.&40.)PLB,(1>.$1?.)PC,$>.Pr,$20.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Px1,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px2,(2.&40.)Px4,(2.&40.)Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px8,(2.&40.)Px9,(2.&40.)Px10,(2.&40.)Px11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(;.(<.(=.$>.$>.)(?.$>.$>.(10.(11.&40.Vsp,)+=0.)(11.&40.Vsp,))(12.(=.$>.$>.)))Vm,R27.)P,(13.$16.Vm,R28.)P,(14.$16.R29.)P,(15.$16.R2:.Vlo,(17.(11.&40.Vsp,)-;0.))P,(18.$16.R2;.(17.(11.&40.Vsp,)-;0.)(<.$19.(1:.R2:.)(<.$19.(1:.R29.)(<.$19.(1:.R28.)(<.$19.(1:.R27.)(<.$19.(1:.R26.)(<.$19.(1:.R25.)(<.$19.(1:.R24.)(<.$19.(1:.R23.)(<.$19.(1:.R22.)(<.$19.(1:.Vs11,)(<.$19.(1:.Vs10,)(<.$19.(1:.Vs9,)(<.$19.(1:.Vs8,)(<.$19.(1:.Vs7,)(<.$19.(1:.Vs6,)(<.$19.(1:.Vs5,)(<.$19.(1:.Vs4,)(<.$19.(1:.Vs3,)(<.$19.(1:.Vs2,)(<.$19.(1:.Vs1,)(<.$19.(1:.Vs0,)(<.$19.(1:.Vra,)(12.$19.))))))))))))))))))))))))P,(18.$16.R2<.R21.(21.R20.))P,(4.(22.=(23.R21.))(24.(23.R21.)(25.+2.+40.)))P,(26.$16.R2>.R24.(27.R22.))P,(26.$16.R2?.R25.(28.R23.))P,(5.$>.(29.(27.R24.))(17.R25.+10.))P,(5.$>.(29.(28.R25.))(17.R26.+20.))P,(2:.VL,(27.R26.))P,(2:.VL,(28.R27.))P,(5.$>.(2;.R29.+8.)=)P,(24.=R2:.)P,(22.(17.R2;.$2<.)(2=.VL,))P,(5.$>.(2;.(11.&40.Vsp,)+10.)=)P,(5.$>.(2;.(11.&40.Vra,)+2.)=)(1;.$16.(1<.$16.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vlo,Vm,)(6.(7.R2<.(1=.&40.(17.(11.&40.Vsp,)-;0.))Vgp,Vtp,R2;.R2:.R29.(1=.&40.R2>.)R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.(1=.&40.=)R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)VF,(1=.&40.+2:66<.)Vfc,(9.(2.&40.))R39.(:.$16.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros MU WM MI ST FR HD LEN MN ME AN AE LVN LVE CAL C0 CAC SPA RA.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(MN) 2%nat. intros (CN & _) _. flat constr:(ME) 2%nat. intros (CE & _) _. rewrite AN in CN. rewrite AE in CE.
    (* [comment removed for export] *)
    lx_run_tac (PLAN [U_RSA_CHECK_CONTEXT] [] 40%N); lx_tree.
    all: try lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
    all: let xC := constr:(C) in lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hi : mem_inv _ mx, Hs : stk _ mx lo _, Hf : rw_cells _ mx (bv_unsigned sp + -176) _, Hd : rw_cells _ mx xC _ |- _ =>
           let MUW := fresh "MUW" in let STR := fresh "STR" in
           assert (MUW : munch [(bv_unsigned sp - RSA_COMPLETE_STACK, bv_unsigned sp)] m mx) by (eapply munch_weaken; [| exact Hm]; intros a Ha; clear -Ha; cbn in Ha |- *; lia);
           (* [comment removed for export] *)
           pose proof (stk_release usegs mx lo _ _ Hs Hf ltac:(clear -SLO SPB; lia)) as STR; cbn [cells_size csize Nat.add] in STR;
           lazymatch type of STR with stk _ _ _ ?h => replace h with (bv_unsigned sp) in STR by (clear; lia) end;
           try rewrite (Z_to_bv_bv_unsigned sp); pose proof Hm as MUc; pose proof Hw as WMc;
           pose proof U_rsa_check_context_spec as SP; unfold rsa_check_context_stmt, U_RSA_CHECK_CONTEXT in SP;
           eapply evt_mono; [eapply SP with (lo := lo) (LB := LB) (r := r);
             first [exact Hd| eapply mpd_at_munch_frame; [exact MN| exact Hm| exact Hw] | eassumption| reflexivity| lia| idtac] |]
         end end.
    cbv beta. intros ms' PO. unfold rsa_ctxck_post in PO.
    flat constr:(PO) 21%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m2 -> MU2 WM2 MI2 ST2.
    unfold rsa_complete_post. flexi 16%nat.
    split; [reflexivity|].
    split; [eapply munch_trans; [exact MUc| eapply munch_weaken; [| exact MU2]; intros a Ha; cbn in Ha |- *; lia]|].
    split; [eapply wmono_trans; [exact WMc| exact WM2]|]. split; [exact MI2| exact ST2].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End CK.

Local Ltac2 Set LiaOrc.tbl := fun () => "00f0@L13661581380.156L13661581380.182L14065687809.85 L17218481476.156L17218481476.182L19488074687.62 L19488304563.63 L20295814720.87 L20295814720.88 L22704459656.3  L22706553362.156L22706553362.182L23227356824.3  L23277650839.195L30520824893.136L30520824893.162L32181381248.156L32181381248.182L32473681269.156L32473681269.182L35780857345.84 L3818671721.136 L3818671721.162 L38932618820.156L38932618820.182L42491087684.156L42491087684.182L43055136010.81 L4444862769.80  L4444862769.81  L49604375876.156L49604375876.182L5090040119.154 L52271955174.83 L52840858064.136L53136536533.79 L53136536533.80 L5852950736.162 L59854489495.137L59854489495.163L59854538518.136L59854538518.162L5987430709.180 L60664827716.156L60664827716.182L61171040852.136L61171040852.162L61484595796.136L61484595796.162L64222788676.156L64222788676.182L8115517792.156 L8115517792.182 L9700704316.3   00003W07>07a0;H0>o0?E0?[0@=0@_0@j0D>0GR0G]0K70NM0Qc0UJ0Y10\@0_O0`20cJ0fb0jI0n011W15>15P15n16L1:31=Z1@i1A41DW1E61EU1I81L_1PF1Sm1WT1Zc1^J1b11e\1iG1lV1oe23L27327427527@S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C0S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S2ra2sp1C1r3SGN3SPB2C0S2ra2sp1C1r3SGE3SPB2C0S1L2ra2sp1C1r2lo3SLO3ACL3SPB2C02H1S1L2ra2sp1C1r2lo3SLO3ACL3SPB2C02H1S2sp2xw3HxwS2ra2sp1C1r1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ201a2HaS2ra2sp1C1r1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ201a2HaS1r2rN4RN01S2ra2sp1C1r3SPB3CAL2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S2ra2sp1C1r2lo3SLO1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S2ra2sp1C1r2lo3SLO1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S2ra2sp1C1r1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S2ra2sp1C1r1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C0S1L2ra2sp1C1r2lo3ACL1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3ACL1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S2ra2sp1C1r2lo3SLOS1L2ra2sp1C1r2lo3ACL3SPB2C02H0S1L2ra2sp1C1r2lo3ACL3SPB2C02H0S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S2ra2sp1C1r1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S2ra2sp1C1rS1L2ra2sp1C1r2lo3CAC3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3ACL3SPB3ACP2C0S1L2ra2sp1C1r2lo3ACL3SPB3ACP2C0S1L2ra2sp1C1r2lo3CAC3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3SLO3ACL3SPB3ACP2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3SLO3ACL3SPB3ACP2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3SLO3ACL3SPB3ACP2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3SLO3ACL3SPB3ACP2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S2ra2sp1C1r1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3SLO3ACL3SPA3SPB3ACP2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3SLO3ACL3SPA3SPB3ACP2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S2ra2sp1C1r1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S2ra2sp1C1r1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20S1L2ra2sp1C1r2lo3CAC3SLO3ACL3SPB2C01j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163j173j183j193j203LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ165LXJ175LXJ185LXJ195LXJ20FFS1r2rE4RE01". (* [comment removed for export] *)
Theorem U_rsa_complete_spec {L : heap_layout} : rsa_complete_stmt usegs U_RSA_COMPLETE.
Proof.
  unfold rsa_complete_stmt, U_RSA_COMPLETE. intros until lo.
  intros RA_ SGN SGE [NSN LVN] [NSE LVE] CAC ST SLO ACL SPA MI RA ->. unfold RSA_CTX_SIZE in CAC.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
  flat constr:(RA_) 12%nat. flclear RA_. intros HD HT AN AE _ _ LEN ALL CAL C0 CB _.
  assert (MN : mpd_at usegs m LB (r_N r)) by (split; [exact (Forall_inv ALL)| lia]).
  assert (ME : mpd_at usegs m LB (r_E r)) by (split; [exact (Forall_inv (Forall_inv_tail ALL))| lia]).
  pose proof (Forall_inv_tail (Forall_inv_tail ALL)) as ZS. clear ALL.
  unfold rsa_zero_mpds, rsa_zero_offs in ZS. cbn [map] in ZS.
  (* [comment removed for export] *)
  assert (ZP : rw_cells usegs m (C + 64) (mpi_cells 0 (Z_to_bv 64 0) 0 (Z_to_bv 64 0))) by (refine (proj1 (proj1 (Forall_forall _ _) ZS (mpd_z (C + 64)) _)); cbn [In]; tauto).
  assert (ZQ : rw_cells usegs m (C + 80) (mpi_cells 0 (Z_to_bv 64 0) 0 (Z_to_bv 64 0))) by (refine (proj1 (proj1 (Forall_forall _ _) ZS (mpd_z (C + 80)) _)); cbn [In]; tauto).
  assert (ZD : rw_cells usegs m (C + 48) (mpi_cells 0 (Z_to_bv 64 0) 0 (Z_to_bv 64 0))) by (refine (proj1 (proj1 (Forall_forall _ _) ZS (mpd_z (C + 48)) _)); cbn [In]; tauto).
  assert (ZDP : rw_cells usegs m (C + 96) (mpi_cells 0 (Z_to_bv 64 0) 0 (Z_to_bv 64 0))) by (refine (proj1 (proj1 (Forall_forall _ _) ZS (mpd_z (C + 96)) _)); cbn [In]; tauto).
  assert (ZDQ : rw_cells usegs m (C + 112) (mpi_cells 0 (Z_to_bv 64 0) 0 (Z_to_bv 64 0))) by (refine (proj1 (proj1 (Forall_forall _ _) ZS (mpd_z (C + 112)) _)); cbn [In]; tauto).
  assert (ZQP : rw_cells usegs m (C + 128) (mpi_cells 0 (Z_to_bv 64 0) 0 (Z_to_bv 64 0))) by (refine (proj1 (proj1 (Forall_forall _ _) ZS (mpd_z (C + 128)) _)); cbn [In]; tauto).
  clear ZS. unfold mpi_cells in ZP, ZQ, ZD, ZDP, ZDQ, ZQP.
  flat constr:(MN) 2%nat. intros FLt1 _. flat constr:(FLt1) 2%nat. flclear FLt1. intros _ FLt2. flat constr:(FLt2) 5%nat. flclear FLt2. intros _ _ LENN NRN OWNN. flat constr:(ME) 2%nat. intros FLt3 _. flat constr:(FLt3) 2%nat. flclear FLt3. intros _ FLt4. flat constr:(FLt4) 5%nat. flclear FLt4. intros _ _ LENE NRE OWNE. unfold MPI_MAX_LIMBS in NRN, NRE.
  assert (PN : md_own (r_N r) = LHeap -> 0 < md_p (r_N r)) by (intros H; exact (proj1 (LVN H))).
  assert (PE : md_own (r_E r) = LHeap -> 0 < md_p (r_E r)) by (intros H; exact (proj1 (LVE H))).
  assert (DN : md_p (r_N r) + 4 * md_n (r_N r) <= lo).
  { destruct (md_own (r_N r)) eqn:EO; [| destruct (LVN eq_refl); lia| exfalso; exact (NSN eq_refl)].
    flat constr:(OWNN) 2%nat. flclear OWNN. intros P0 N0. rewrite P0, N0. lia. }
  assert (DE : md_p (r_E r) + 4 * md_n (r_E r) <= lo).
  { destruct (md_own (r_E r)) eqn:EO; [| destruct (LVE eq_refl); lia| exfalso; exact (NSE eq_refl)].
    flat constr:(OWNE) 2%nat. flclear OWNE. intros P0 N0. rewrite P0, N0. lia. }
  assert (TRN : forall ma mb, mpd_at usegs ma LB (r_N r) -> munch [(bv_unsigned sp - 208, bv_unsigned sp)] ma mb -> wmono usegs ma mb -> mpd_at usegs mb LB (r_N r)).
  { intros ma mb H MUx WMx. eapply mpd_at_munch; [exact H| exact NSN| exact MUx| exact WMx| cbn; split; [rewrite AN; lia| exact I]|].
    intros EO. cbn. split; [| exact I]. destruct (LVN EO). lia. }
  assert (TRE : forall ma mb, mpd_at usegs ma LB (r_E r) -> munch [(bv_unsigned sp - 208, bv_unsigned sp)] ma mb -> wmono usegs ma mb -> mpd_at usegs mb LB (r_E r)).
  { intros ma mb H MUx WMx. eapply mpd_at_munch; [exact H| exact NSE| exact MUx| exact WMx| cbn; split; [rewrite AE; lia| exact I]|].
    intros EO. cbn. split; [| exact I]. destruct (LVE EO). lia. }
  pose proof (sgn01 _ (mpd_val_sg1 _ SGN)) as RN01. pose proof (sgn01 _ (mpd_val_sg1 _ SGE)) as RE01.
  clear OWNN OWNE.
  unfold rsa_head_cells in HD. unfold rsa_tail_cells in HT.
  carve_frame 176%nat ST.
  lxp_split_frame [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp)] mx) as MU; pose proof (wmono_refl usegs mx) as WM end.
  (* [comment removed for export] *)
  lx_run_tac (PLAN [0x2a458] [] 40%N); lx_tree.
  all: lxp_unjunk.
  try clear MU; try clear WM; try clear ST; try clear FR.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hi : mem_inv _ mx, Hs : stk _ mx lo _, Hf : rw_cells _ mx (bv_unsigned sp + -176) _,
                        Hd : rw_cells _ mx C _, Ht : rw_cells _ mx (C + 224) _ |- _ =>
      clear HD HT MI; rename Hm into MU; rename Hw into WM; rename Hi into MI; rename Hs into ST; rename Hf into FR; rename Hd into HD; rename Ht into HT;
      lxp_cells FR; rename mx into m1
    end end.
  (* [comment removed for export] *)
  zstep.
  pose proof U_mpi_cmp_int_spec as SP. unfold mpi_cmp_int_stmt, U_MPI_CMP_INT in SP.
  eapply evt_cut; [ eapply SP with (lo := lo) (LB := LB) (dX := r_N r) (z := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -176)) by lia;
    [ eapply TRN; [exact MN| exact MU| exact WM] | exact PN | lia | eassumption | lia | lia | lia | rewrite AN; lia | left; exact DN | assumption | first [reflexivity | rewrite AN; reflexivity] | reflexivity ] | ].
  clear SP. cbv beta. intros ms' PO. unfold mpi_cmp_int_post in PO. rewrite ?(unsigned_lit (bv_unsigned sp + -176)) in PO by lia.
  flat constr:(PO) 20%nat. flclear PO. intros b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 m3 -> MU3 WM3 MI3 ST3.
  replace (ret_pc (Z_to_bv 64 0x2a45c)) with (Z_to_bv 64 0x2a45c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  after_callg usegs MU WM MU3 WM3.
  set (rN := Z.sgn (mpd_val (r_N r) - 0)) in *.
  assert (RNB : 0 <= rN <= 1) by (clear -RN01; lia). clearbody rN. clear RN01.
  (* [comment removed for export] *)
  lx_run_tac (PLAN [0x2a470] [] 40%N); lx_tree.
  try clear ST; try clear FR; try clear MI.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hi : mem_inv _ mx, Hs : stk _ mx lo _, Hf : rw_cells _ mx (bv_unsigned sp + -176) _ |- _ =>
      try clear MU; try clear WM; rename Hm into MU; rename Hw into WM; rename Hi into MI; rename Hs into ST; rename Hf into FR
    end end.
  cpl_z0 C sp lo 64 0x2a474 MU WM.
  lx_run_tac (PLAN [0x2a488] [] 40%N); lx_tree.
  try clear ST; try clear FR; try clear MI.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hi : mem_inv _ mx, Hs : stk _ mx lo _, Hf : rw_cells _ mx (bv_unsigned sp + -176) _ |- _ =>
      try clear MU; try clear WM; rename Hm into MU; rename Hw into WM; rename Hi into MI; rename Hs into ST; rename Hf into FR
    end end.
  cpl_z0 C sp lo 80 0x2a48c MU WM.
  lx_run_tac (PLAN [0x2a4a0] [] 40%N); lx_tree.
  try clear ST; try clear FR; try clear MI.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hi : mem_inv _ mx, Hs : stk _ mx lo _, Hf : rw_cells _ mx (bv_unsigned sp + -176) _ |- _ =>
      try clear MU; try clear WM; rename Hm into MU; rename Hw into WM; rename Hi into MI; rename Hs into ST; rename Hf into FR
    end end.
  cpl_z0 C sp lo 48 0x2a4a4 MU WM.
  lx_run_tac (PLAN [0x2a4b8] [] 40%N); lx_tree.
  try clear ST; try clear FR; try clear MI.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hi : mem_inv _ mx, Hs : stk _ mx lo _, Hf : rw_cells _ mx (bv_unsigned sp + -176) _ |- _ =>
      try clear MU; try clear WM; rename Hm into MU; rename Hw into WM; rename Hi into MI; rename Hs into ST; rename Hf into FR; rename mx into m4
    end end.
  (* [comment removed for export] *)
  zstep.
  pose proof U_mpi_cmp_int_spec as SP. unfold mpi_cmp_int_stmt, U_MPI_CMP_INT in SP.
  eapply evt_cut; [ eapply SP with (lo := lo) (LB := LB) (dX := r_E r) (z := 0); rewrite ?(unsigned_lit (bv_unsigned sp + -176)) by lia;
    [ eapply TRE; [exact ME| exact MU| exact WM] | exact PE | lia | eassumption | lia | lia | lia | rewrite AE; lia | left; exact DE | assumption | first [reflexivity | rewrite AE; reflexivity] | reflexivity ] | ].
  clear SP. cbv beta. intros ms' PO. unfold mpi_cmp_int_post in PO. rewrite ?(unsigned_lit (bv_unsigned sp + -176)) in PO by lia.
  flat constr:(PO) 20%nat. flclear PO. intros e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 m5 -> MU5 WM5 MI5 ST5.
  replace (ret_pc (Z_to_bv 64 0x2a4bc)) with (Z_to_bv 64 0x2a4bc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  after_callg usegs MU WM MU5 WM5.
  set (rE := Z.sgn (mpd_val (r_E r) - 0)) in *.
  assert (REB : 0 <= rE <= 1) by (clear -RE01; lia). clearbody rE. clear RE01.
  (* [comment removed for export] *)
  lx_run_tac (PLAN [0x2a4cc] [] 40%N); lx_tree.
  try clear ST; try clear FR; try clear MI.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hi : mem_inv _ mx, Hs : stk _ mx lo _, Hf : rw_cells _ mx (bv_unsigned sp + -176) _ |- _ =>
      try clear MU; try clear WM; rename Hm into MU; rename Hw into WM; rename Hi into MI; rename Hs into ST; rename Hf into FR
    end end.
  cpl_z0 C sp lo 96 0x2a4d0 MU WM.
  lx_run_tac (PLAN [0x2a4e0] [] 40%N); lx_tree.
  try clear ST; try clear FR; try clear MI.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hi : mem_inv _ mx, Hs : stk _ mx lo _, Hf : rw_cells _ mx (bv_unsigned sp + -176) _ |- _ =>
      try clear MU; try clear WM; rename Hm into MU; rename Hw into WM; rename Hi into MI; rename Hs into ST; rename Hf into FR
    end end.
  cpl_z0 C sp lo 112 0x2a4e4 MU WM.
  lx_run_tac (PLAN [0x2a4f4] [] 40%N); lx_tree.
  try clear ST; try clear FR; try clear MI.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with Hm : munch _ m mx, Hw : wmono _ m mx, Hi : mem_inv _ mx, Hs : stk _ mx lo _, Hf : rw_cells _ mx (bv_unsigned sp + -176) _ |- _ =>
      try clear MU; try clear WM; rename Hm into MU; rename Hw into WM; rename Hi into MI; rename Hs into ST; rename Hf into FR
    end end.
  cpl_z0 C sp lo 128 0x2a4f8 MU WM.
  lx_run_tac (PLAN [0x2a630; 0x2a66c] [] 160%N); lx_tree.
  all: let xm := constr:(m) in let xC := constr:(C) in
       lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
       lazymatch goal with Hm : munch _ xm mx, Hw : wmono _ xm mx, Hi : mem_inv _ mx, Hs : stk _ mx _ _, Hf : rw_cells _ mx (bv_unsigned _ + -176) _, Hd : rw_cells _ mx xC _ |- _ =>
         let MUW := fresh "MUW" in
         assert (MUW : munch [(bv_unsigned sp - 208, bv_unsigned sp)] m mx) by (eapply munch_weaken; [| exact Hm]; intros xw Hxw; clear -Hxw; cbn in Hxw |- *; lia);
         lazymatch pc with
         | 173616 => eapply cpl_epilogue; first [exact SLO| exact ACL| exact MUW| exact Hw| exact Hi| exact Hs| exact Hf]
         | _ => eapply cpl_tail; first [exact SLO| exact ACL| exact MUW| exact Hw| exact Hi| exact Hs| exact Hf| exact Hd| exact (conj NSN LVN)| exact (conj NSE LVE)
                                       | eapply TRN; [exact MN| exact MUW| exact Hw] | eapply TRE; [exact ME| exact MUW| exact Hw] | eassumption| lia]
         end end end.
  all: match goal with |- ?g => idtac "LEFT" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
