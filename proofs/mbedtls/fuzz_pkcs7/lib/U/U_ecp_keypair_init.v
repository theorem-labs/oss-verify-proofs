(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_mpi_init U_ecp_group_init.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P01ba3c0de376f29a 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P027ee10f3aa8f2be 0 4 0 1 2 1 42 1 43 1P029fcb520e12d448 0 4 0 1 2 1 42 1 43 1P03db8f8c7f8704f2 1 1 8 2 35 1 39 1 3 0 1 38 1 40 8P04923c7f43b8fc1c 1 1 8 3 0 1 41 1 42 1 5 2 2 36 2 40 2 43 2 44 16P04d9c694d6e5331e 1 1 8 3 1 1 41 1 42 1 4 2 1 40 1 43 1 44 8P0565ac48efac18eb 1 1 8 3 1 1 41 1 42 1 4 2 1 40 1 43 1 44 8P06b48272e431c07e 1 1 8 2 35 1 39 1 3 0 1 38 1 40 8P07efbcfd08dcc350 1 1 8 3 0 1 41 1 42 1 5 2 2 36 2 40 2 43 2 44 16P0b4a59e7c88682a2 1 1 8 3 1 1 40 1 43 1 4 2 2 41 2 42 2 44 16P0b582dcd90683586 2 34 1 1 8 3 1 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P0b9b76e1576ef7ec 1 1 8 3 1 1 41 1 42 1 4 2 1 40 1 43 1 44 8P0bf206e6a551f0ed 0 4 0 1 2 1 42 1 43 1P0d31115a0165e55b 2 34 1 1 8 3 1 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P0d57d1aa47520bd9 1 1 8 3 1 1 40 1 43 1 4 2 2 41 2 42 2 44 16P0deab3a093db4f36 1 1 8 2 35 1 39 1 3 0 1 38 1 40 8P0e3bab08a7cff170 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P0f059059384645f6 1 1 8 2 35 1 39 1 3 0 1 38 1 40 8P106967a647f87d05 0 4 0 1 2 1 42 1 43 1P10e93b451a5eab2b 1 1 8 2 35 1 39 1 3 0 1 38 1 40 8P10ea399fec7167af 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P12fbb3dfc9a3412d 1 1 8 2 35 1 39 1 3 0 1 38 1 40 8P1314ce1f83815157 0 4 0 1 2 1 42 1 43 1P149f574eb2ac5cdb 0 4 0 1 2 1 42 1 43 1P1593b1a43a7b3edc 1 1 8 3 1 1 41 1 42 1 4 2 1 40 1 43 1 44 8P15b4e0846562d6d8 1 1 8 3 1 1 40 1 43 1 4 2 2 41 2 42 2 44 16P177da2deed377696 0 4 0 1 2 1 42 1 43 1P17e62397f6e3b87e 1 1 8 3 1 1 41 1 42 1 4 2 1 40 1 43 1 44 8P1806d2f86b55f533 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P181a6d831b712949 2 34 1 1 8 3 1 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P189d983caa51294b 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P18e2488783a51940 2 34 1 1 8 3 1 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P19fecdca7300406b 2 34 1 1 8 3 1 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P1bb46392fb6adf51 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P1cf1f16b9eebae61 1 1 8 3 0 1 41 1 42 1 5 2 2 36 2 40 2 43 2 44 16P1d09ca4dbadee2e6 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P1dcd608199f940f8 1 1 8 3 0 1 41 1 42 1 5 2 2 36 2 40 2 43 2 44 16P1df33a6963d085d6 1 1 8 3 1 1 41 1 42 1 4 2 1 40 1 43 1 44 8P1f2e0543aaada91e 1 1 8 2 35 1 39 1 3 0 1 38 1 40 8P1ff461d27bb378fd 1 1 8 2 35 1 39 1 3 0 1 38 1 40 8P20484d93ba912421 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P2093aa24256842ee 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P218ae93040b853cc 1 1 8 3 0 1 41 1 42 1 5 2 2 36 2 40 2 43 2 44 16P220c26bced597e3a 1 1 8 3 1 1 40 1 43 1 4 2 2 41 2 42 2 44 16P22ade0e613e47919 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P22d5e0346a845f2b 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P23319648842c4c2f 1 1 8 3 0 1 41 1 42 1 5 2 2 36 2 40 2 43 2 44 16P24b2aa25044e0638 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P25c3778d7ae1a53a 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P25c60a2feae62842 2 34 1 1 8 3 1 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P266175b4859188d6 1 1 8 3 1 1 40 1 43 1 4 2 2 41 2 42 2 44 16P274489b045fa8ffb 0 4 0 1 2 1 42 1 43 1P27a03cbc56d54c7a 1 1 8 3 1 1 41 1 42 1 4 2 1 40 1 43 1 44 8P27d6a9e97f081099 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P2ad04c228225b6f5 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P2afa7ab1f823fb36 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P2b1ff5fb337a8e2c 2 34 1 1 8 3 1 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P2bc620988fed5d23 1 1 8 3 0 1 41 1 42 1 5 2 2 36 2 40 2 43 2 44 16P2bfe7298d6f41b30 0 4 0 1 2 1 42 1 43 1P2deeb028545461c1 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P2eca2e7f0098567c 1 1 8 2 35 1 39 1 3 0 1 38 1 40 8P2f9d92c233f596a7 1 1 8 3 0 1 41 1 42 1 5 2 2 36 2 40 2 43 2 44 16P301392b4882aa2b4 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P3062c5865466d064 0 4 0 1 2 1 42 1 43 1P30656717609afb0f 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P328f516427214ab6 1 1 8 3 1 1 41 1 42 1 4 2 1 40 1 43 1 44 8P32dacad67ea794be 1 1 8 3 1 1 40 1 43 1 4 2 2 41 2 42 2 44 16P335126d3be5c0173 1 1 8 3 0 1 41 1 42 1 5 2 2 36 2 40 2 43 2 44 16P33608e4afa4a2857 2 34 1 1 8 3 1 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P33e6680b37583cd7 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P33ea4c3c3baa2233 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P344bb704b40b73c6 1 1 8 3 1 1 41 1 42 1 4 2 1 40 1 43 1 44 8P358bb353690fbe70 1 1 8 3 0 1 41 1 42 1 5 2 2 36 2 40 2 43 2 44 16P359e380506345960 1 1 8 3 1 1 40 1 43 1 4 2 2 41 2 42 2 44 16P35b20e13089a09f2 2 34 1 1 8 3 1 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P35e36d34f3ea7a87 0 4 0 1 2 1 42 1 43 1P3606274f37a1bacb 1 1 8 3 1 1 40 1 43 1 4 2 2 41 2 42 2 44 16P367559a671ff143f 2 34 1 1 8 3 1 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P36d049bab4d41e00 1 1 8 3 0 1 41 1 42 1 5 2 2 36 2 40 2 43 2 44 16P36e71b1ab50d56f4 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P393febe60e5acb79 1 1 8 3 1 1 40 1 43 1 4 2 2 41 2 42 2 44 16P39469ff97f2aa0cb 1 1 8 2 35 1 39 1 3 0 1 38 1 40 8P3967d2c898916130 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P3a7e5ef600d97e15 1 1 8 3 1 1 40 1 43 1 4 2 2 41 2 42 2 44 16P3acace7ed56d32f0 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P3c00d27f79689409 1 1 8 3 1 1 41 1 42 1 4 2 1 40 1 43 1 44 8P3d31730df5b6d6dd 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P3d52763b881e28db 1 1 8 3 1 1 41 1 42 1 4 2 1 40 1 43 1 44 8P3e7dd9f8f257be0f 2 34 1 1 8 3 2 1 41 1 42 1 5 0 1 36 1 40 1 43 1 44 8 1 1 8 3 1 1 40 1 43 1 4 0 2 41 2 42 2 44 16P3f0265c62848f85a 1 1 8 3 1 1 40 1 43 1 4 2 2 41 2 42 2 44 16P3fcaa5a8de53276a 1 1 8 2 35 1 39 1 3 0 1 38 1 40 8N00319529431e9d81N03a55f791852ba1aN049ec0e74336fa32N04f615c981d8b93eN08624d57c5f902f1N0879a04f0b6be8ecN0882efe9f52e0648N08a049a8fc9324a4N0906991510ae7ca9N0968b996834bac08N096bd2054dc2b0e6N0b9131ca427607f6N10a70bb84b052183N1127b841fef9ae1cN139447a4bceea935N18eaa0b132359903N1a110448e67edbe3N1a2d502f1c6ba999N1b2df22dd2f6a6e2N1bcbc18e2155d028N1ed089ec978a8b74N1ee2b97643d20f59N239cd2a6b88d93ddN29f3954c9cb63439N2a82632b4373dd8fN2b3ea99c45a96c78N2b4a8dda369ab7b3N329808e211bca80dN360d319d44f85e11N385397d62a309774N3908fdfbd736379aN3bfe7f18adb65446N3c800afdc8bd4697N3c8b6d19f4fa54d3N3e4c13a6065ed0f0N3f209f27f7b18649N3fce628b55be7100"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_ecp_keypair_init () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mkKP"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_init"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpd_init"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.pt_init"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ECP_KEYPAIR_SIZE"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_keypair_at"; "kp_init"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "ecp_keypair_init_post"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_group_at"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"].


Definition U_ECP_KEYPAIR_INIT : Z := 0x38474.
Notation ECP_KEYPAIR_INIT_STACK := 32 (only parsing).

(* [comment removed for export] *)
Definition kp_init (A : Z) (idpad pP pA pB pX pY pZ pN hpad pd qX qY qZ : word) : ecp_kp := ltac2:(CDefT.buildp (gd_tbl_P_ecp_keypair_init ()) "(0.(1.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.)(2.(3.O>.+<0.)O4.)(4.(3.O>.+=0.)O3.O2.O1.))")
(* [comment removed for export] *).

Definition ecp_keypair_init_post (segs : list Segment) (MT : list modp_ent)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (LB : list blk) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_keypair_init ()) "Lms',$5.(6.(7.&40.)Lt0,(7.&40.)(6.(7.&40.)Lt1,(7.&40.)(6.(7.&40.)Lt2,(7.&40.)(6.(7.&40.)La0,(7.&40.)(6.(7.&40.)La1,(7.&40.)(6.(7.&40.)La2,(7.&40.)(6.(7.&40.)La3,(7.&40.)(6.(7.&40.)La4,(7.&40.)(6.(7.&40.)La5,(7.&40.)(6.(7.&40.)La6,(7.&40.)(6.(7.&40.)La7,(7.&40.)(6.(7.&40.)Lt3,(7.&40.)(6.(7.&40.)Lt4,(7.&40.)(6.(7.&40.)Lt5,(7.&40.)(6.(7.&40.)Lt6,(7.&40.)(6.P,(7.&40.)(8.(7.&8.))Lm',P,(7.&40.)(8.(7.&8.))(6.(7.&40.)Lidpad,(7.&40.)(6.(7.&40.)LpP,(7.&40.)(6.(7.&40.)LpA,(7.&40.)(6.(7.&40.)LpB,(7.&40.)(6.(7.&40.)LpX,(7.&40.)(6.(7.&40.)LpY,(7.&40.)(6.(7.&40.)LpZ,(7.&40.)(6.(7.&40.)LpN,(7.&40.)(6.(7.&40.)Lhpad,(7.&40.)(6.(7.&40.)Lpd,(7.&40.)(6.(7.&40.)LqX,(7.&40.)(6.(7.&40.)LqY,(7.&40.)(6.(7.&40.)LqZ,(7.&40.)(9.(:.$5.R1>.(;.(<.O16.O15.O14.O13.R1=.R1<.R1;.O12.O11.R1:.R19.R18.R17.R16.R15.R14.R13.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R12.R11.R10.R?.)O6.(=.O16.)O5.(>.(7.&40.))R>.(?.O18.)))(9.(10.(11.(12.$13.$13.)(14.$13.$13.O4.(3.O4.$15.))(11.(12.$13.$13.)(14.$13.$13.(16.(17.&40.O15.)+20.)(17.&40.O15.))(18.(12.$13.$13.))))O1.R>.)(9.(19.O18.O1.R>.)(9.(1:.O18.R>.)(9.(1;.O18.O17.R>.O3.O4.(1<.O4.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.))(1=.O18.R>.O2.(17.&40.O15.))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition ecp_keypair_init_stmt (segs : list Segment) (MT : list modp_ent) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_ecp_keypair_init ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps0,(7.&40.)Ps1,(7.&40.)Pa0,(7.&40.)Pa1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps4,(7.&40.)Ps5,(7.&40.)Ps6,(7.&40.)Ps7,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)PF,(1>.&5.(7.&40.))Pfc,(7.&20.)Pm,P,(7.&40.)(8.(7.&8.))PA,$13.Plo,$13.PLB,(1?.$20.)Pjunk,(1?.(7.&8.))P,(21.O3.R5.R4.(11.$22.(23.#100.R1.)(18.$22.)))P,(:.$13.(24.R5.+8.)=)P,(25.=R6.)P,(1=.O3.R8.R6.(17.&40.R28.))P,(26.R7.(16.(17.&40.R29.)+20.))P,(:.$13.(24.(17.&40.R2:.)+10.)=)P,(27.(26.(3.R:.$15.)R9.)(26.(17.&40.R2;.)R:.))P,(1:.O3.R<.)P,(:.$13.(24.(17.&40.R2>.)+2.)=)P,(:.(7.&40.)R26.(28.&40.R=.))(29.O3.(2:.O3.O2.R30.R2?.R2>.R2=.R29.R28.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R11.R10.R>.R<.R=.R?.)(;.(<.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R11.(28.&40.O1.)R10.(>.(7.&40.))R?.(?.O3.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L13592035095.25L1555092503.25 L26929280295.25L39009021990.25L42601177800.25L43652582344.25L44688266440.25L4572661286.25 L45741800904.25L46202318359.25L52397760807.25L58238699799.2500000700>00A00D00N00X00b00e00o01601901@S1A3POSS1A3POSS1AS1AS1A2AL3POSS1A2AL3POSS1A2AL3POSS1AS1A2AL3POSS1A3POSS1AS1A3POS". (* [comment removed for export] *)
Lemma ecp_keypair_at_init : ltac2:(CDefT.buildp (gd_tbl_P_ecp_keypair_init ()) "Psegs,(1?.$2;.)PMT,(1?.$2<.)Pm,P,(7.&40.)(8.(7.&8.))PLB,(1?.$20.)PA,$13.Pidpad,(7.&40.)PpP,(7.&40.)PpA,(7.&40.)PpB,(7.&40.)PpX,(7.&40.)PpY,(7.&40.)PpZ,(7.&40.)PpN,(7.&40.)Phpad,(7.&40.)Ppd,(7.&40.)PqX,(7.&40.)PqY,(7.&40.)PqZ,(7.&40.)P,(2=.R12.R11.R10.R?.R>.(1.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.))P,(21.R13.R11.(3.R?.+<0.)(2>.=(28.&40.+1.)=R5.))P,(21.R14.R12.(3.R10.+=0.)(2>.=(28.&40.+1.)=R5.))P,(21.R15.R13.(3.R11.+>0.)(2>.=(28.&40.+1.)=R5.))P,(21.R16.R14.(3.R12.+?0.)(2>.=(28.&40.+1.)=R5.))(1;.R17.R16.R15.R14.R13.(1<.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.))")
(* [comment removed for export] *).
Proof.
  intros until qZ. intros HG HDd HX HY HZ. flat constr:(HG) 4%nat. intros _ AL POS _.
  unfold ecp_keypair_at, kp_init, ecp_point_at, pt_init; cbn -[ecp_group_at grp_init mpdr_at rw_cells Z.pow Z.add Z.mul Z.le Z.lt].
  split; [exact HG|]. split; [reflexivity|]. split; [apply mpdr_at_init; [exact HDd| lia| lia]|].
  split; [discriminate|].
  split. { split; [reflexivity|]. split; [cbn; lia|]. split; [cbn; lia|].
           replace (A + 208 + 16) with (A + 224) by lia. replace (A + 208 + 32) with (A + 240) by lia.
           split; [apply mpdr_at_init; [exact HX| lia| lia]|]. split; [apply mpdr_at_init; [exact HY| lia| lia]|]. apply mpdr_at_init; [exact HZ| lia| lia]. }
  unfold pt_freeable, pt_mpds; cbn. repeat constructor; cbn; discriminate.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac kp_grp_cells :=
  lazymatch goal with H : ecp_group_at _ _ _ _ _ (grp_init _ _ _ _ _ _ _ _ _ _) |- _ =>
    unfold ecp_group_at, grp_init, ecp_point_at, pt_init in H;
    cbn -[mpdr_at rw_cells Z.pow Z.add Z.mul Z.le Z.lt] in H;
    let HD := fresh "GHD" in let MP := fresh "GMP" in let MA := fresh "GMA" in let MB := fresh "GMB" in
    let MX := fresh "GMX" in let MY := fresh "GMY" in let MZ := fresh "GMZ" in let MN := fresh "GMN" in
    let HT := fresh "GHT" in
    destruct H as (HD & _ & _ & _ & _ & _ & _ & MP & MA & MB & (_ & _ & _ & MX & MY & MZ) & MN & HT & _);
    unfold mpdr_at, mpi_at in MP, MA, MB, MX, MY, MZ, MN;
    cbn -[rw_cells Z.pow Z.add Z.mul Z.le Z.lt] in MP, MA, MB, MX, MY, MZ, MN;
    destruct MP as (MP & _); destruct MA as (MA & _); destruct MB as (MB & _); destruct MX as (MX & _);
    destruct MY as (MY & _); destruct MZ as (MZ & _); destruct MN as (MN & _);
    unfold mpi_cells in MP, MA, MB, MX, MY, MZ, MN
  end.

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L20433961190.66L31398624892.1 L3831839359.64 L43059266230.6400000@00D00h01>S2ra2sp1A3SPR2GBS2spS2ra2sp1A2lo2LO3SPR2GB1j2j03LXJ4LXJ0S2ra2sp1A2lo2LO3SPR2GB". (* [comment removed for export] *)
Lemma U_ecp_keypair_init_spec : forall MT, ecp_keypair_init_stmt usegs MT U_ECP_KEYPAIR_INIT.
Proof.
  intros MT.
  unfold ecp_keypair_init_stmt, U_ECP_KEYPAIR_INIT.
  intros until junk.
  intros HK AL POS ST LO SPA SX MI RA ->.
  unfold ECP_KEYPAIR_SIZE in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  assert (LO0 : 0 <= lo) by ((flat constr:(ST) 2%nat; flclear ST; intros ? _); assumption).
  pose proof (rw_cells_bound _ _ _ _ HK) as GB.
  cbn [cells_size csize Nat.add] in GB.
  flat constr:((kp_chunks_of_bytes _ _ _ _ HK)) 5%nat. intros HG R1 R2 R3 R4.
  clear HK.
  apply mpi_cells_of_bytes in R1.
  apply mpi_cells_of_bytes in R2.
  apply mpi_cells_of_bytes in R3.
  apply mpi_cells_of_bytes in R4.
  pose proof (munch_refl [(A, A + 256); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold mpi_cells in R1, R2, R3, R4.
  carve_frame 16%nat ST.
  lxp_split_frame [8;8]%nat. lxp_seps 16.
  (* [comment removed for export] *)
  pose proof (@sums1_ok) as LXSUMS.
  lxp_run (PLANS [0x383e4] [] 64%N SUMS1).
  pose proof (U_ecp_group_init_spec MT) as SPG. unfold ecp_group_init_stmt, U_ECP_GROUP_INIT in SPG.
  lazymatch goal with |- evt ?sg _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut;
    [ eapply SPG with (A := A) (lo := lo) (LB := LB); rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by plia;
      try eassumption; try reflexivity; try plia; try (unfold ECP_GROUP_SIZE; plia); lxp_side
    | unfold ecp_group_init_post, ECP_GROUP_SIZE; rewrite ?(unsigned_lit (bv_unsigned sp + -16)) by plia;
      post_call sg mm ]
  end.
  clear SPG.
  kp_grp_cells.
  lxp_run (PLANS [] [] 64%N SUMS1).
  lxp_ret.
  all: try (eapply ecp_keypair_at_init; lxp_apply_post).
  all: try (eapply ecp_group_at_init; lxp_apply_post).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
