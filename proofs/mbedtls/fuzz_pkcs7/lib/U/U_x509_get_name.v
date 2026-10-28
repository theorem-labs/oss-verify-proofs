(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA X509Aux AStep CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_len U_asn1_free_named_data_list_shallow U_x509_get_name_A U_x509_get_name_B U_x509_get_name_C U_x509_get_name_F.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPHeap. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P016f3958a968d135 0 4 0 1 18 1 35 1 36 1P02195a54329c95ce 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P027e2e55ad4d0974 0 5 0 1 20 1 28 1 35 1 36 1P03b1e099233aad61 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P03ceaad3a69db6f3 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P05c1df2f9c0a63df 0 4 0 1 18 1 35 1 36 1P0618697cee705422 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P06a2cfe8e77019ff 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P0790b8a1803307ab 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P0b747c9292c9c8e3 0 5 0 1 20 1 28 1 35 1 36 1P0cbfdea0842e2b1d 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P0cc3607fca035dbe 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P0cfaaa9d3e936d47 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P0cffa6493a0e8de3 0 5 0 1 20 1 28 1 35 1 36 1P0d2a5a2855dec46b 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P0dd020b0c914ecc6 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P0e630f3b28563bb2 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P102c6f4f77a5daa7 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P1102b6b1460766c2 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P1205c2d57ab7faa9 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P12cba50e7401aeda 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P130286d93de9c31e 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P13a96d989c7bd3ec 0 4 0 1 18 1 35 1 36 1P13e137017debceed 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P148b79c63931f0bb 0 4 0 1 18 1 35 1 36 1P162f17c4f9dc4f6a 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P173bdf5fc355bea7 0 4 0 1 18 1 35 1 36 1P18d8c4b2870bf0b5 0 4 0 1 18 1 35 1 36 1P1a2023a3082ea133 0 5 0 1 20 1 28 1 35 1 36 1P1a9478ab13bda02c 0 4 0 1 18 1 35 1 36 1P1b7fa9f5afc91889 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P1d4267e875240e38 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P1da5be0b5298f6f1 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P1db017404f7efd3c 0 5 0 1 20 1 28 1 35 1 36 1P1db6ed754f409491 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P1dccf59cd8f9c6e0 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P1f2523829e526519 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P1f296d66058cf259 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P20125d4f3292f5ee 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P206fe92a7e082e83 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P21ad21678390093f 0 4 0 1 18 1 35 1 36 1P2226ffc27d6d8a6b 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P2238c502f55a479f 0 4 0 1 18 1 35 1 36 1P22e0f6d7e2cd6b70 0 5 0 1 20 1 28 1 35 1 36 1P2587f48e57ce1b37 0 5 0 1 20 1 28 1 35 1 36 1P2634bbf3d7c19211 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P283985ac4d6084a5 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P286b7577a02bde0d 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P28d484efe36b2b9a 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P299ff170f7e99212 0 4 0 1 18 1 35 1 36 1P29fc5d9ca406f176 0 4 0 1 18 1 35 1 36 1P2a1e03ed42d69ccd 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P2acfa03daa85c42f 0 5 0 1 20 1 28 1 35 1 36 1P2b241c55832f51a9 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P2ba31a901e254aab 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P2c1e41cc579290ba 0 5 0 1 20 1 28 1 35 1 36 1P2d3db9ed3c0fc7ec 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P310868cc31852726 0 5 0 1 20 1 28 1 35 1 36 1P32644e1f9c34b911 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P33816b62abf0f0fa 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P3398a2d08134a922 0 5 0 1 20 1 28 1 35 1 36 1P33a17a6c6c2f3eb1 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P33e49ba1ce1ce5d4 0 5 0 1 20 1 28 1 35 1 36 1P35dc31a5d325ace4 0 5 0 1 20 1 28 1 35 1 36 1P373ebfe724ebc00d 0 5 0 1 20 1 28 1 35 1 36 1P37bda25fa5ab2645 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P37c9b10534fc6e77 0 4 0 1 18 1 35 1 36 1P37d1eaa1f20809bd 2 14 0 6 0 1 3 1 23 1 31 1 38 1 39 1 0 4 0 1 2 1 38 1 39 1P3ab322b78f45e6fe 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P3ca2f5d71c1de1ae 0 4 0 1 18 1 35 1 36 1P3e45f519b7a63aa0 0 5 0 1 20 1 28 1 35 1 36 1P3f65509cf74f6693 0 4 0 1 18 1 35 1 36 1P3f7ea0e9a7f3be54 2 15 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8P3f949a0cba2ae74e 0 4 0 1 18 1 35 1 36 1P3fbfadc0a6878ad0 2 16 1 1 8 3 2 1 38 1 39 1 6 0 1 22 1 30 1 37 1 40 1 41 8 1 1 8 3 1 1 37 1 40 1 4 0 1 38 1 39 1 41 8N00a25aba15eb4cb1N042454cd2bc1d12cN04c049ca24f653aaN09efbfbb709b5b3eN0bd606c343846377N10ef0124ab385889N13859508c3773001N14888fc2c1245906N14a4fa22a4bcb29cN1690ed41fc2e7701N16b4970faf1fc7e2N16eb70ae0ebf2577N19fc76cd2198b461N1b7a48a0f1fd88caN222be23535e3a5ffN2609311e428b17f4N2a668e2d2548b0bfN2fc9fb816ab73ac4N3774b9aa52fb80fdN37830c28426849abN37dae5140f1ab5b6N37efb1dd4b452332N382a65b94fcbeae4N38ef2fbb0acbfc3fN398941120c373fe8N3a63e5dcbe754f47N3bfb6ab02a05c968N3cb2e9fecbfc6e32N3fc8bc187b895f28N3fe76e4ea04fd451"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_x509_get_name () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_iface"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_calloc"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.U_CALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_free"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_free_named_data_list_shallow.U_FREE"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.x509_get_name_stmt"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.U_X509_GET_NAME"].


Local Ltac2 Set LiaOrc.tbl := fun () => "00<0@L12775220663.116L1399768260.116 L15028858872.116L18241568998.92 L2261724442.1   L43059266230.90 L43777720960.113L46361372624.110L47200983892.110L55605031846.110L55605031846.116L6952084072.1   00000102`02a02o03403[06I09<0;h0;i0;j0;nFS2sp2PP3CUR2bs4CURB1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ16FS2sp2PP3CUR2bsS3CURS1L3HLS2sp2PP3CUR2lo2bs3NZ13NZ23SLO3SPBS2sp2PP3CUR2bs3SPB1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ16S2sp2PP3CUR1P3END2bs2B21j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ16S2sp2PP3CUR1P2bs1j2j02j12j22j32j42j52j62j72j82j93j103j113j123j133j143j153j163LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44LXJ54LXJ64LXJ74LXJ84LXJ95LXJ105LXJ115LXJ125LXJ135LXJ145LXJ155LXJ16FFS2PP". (* [comment removed for export] *)
Theorem U_x509_get_name_spec : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name ()) "PL,$0.PHI,(1.$2.R1.)P,(3.$4.(5.R2.)$6.)P,(3.$4.(7.R3.)$8.)P,(9.=(:.R4.))(;.$2.R5.R4.$<.)")
(* [comment removed for export] *).
Proof.
  (* [comment removed for export] *)
  intros L HI HCALLOC HFREE HLS.
  unfold x509_get_name_stmt, U_X509_GET_NAME.
  intros until pad7.
  intros HH HPP HCUR HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL HTOP SPA DHI DIM1 DIM2 DS1 DS2 DS3
    CWPP CWCUR CRBUF TP MI -> -> ->.
  pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (proj1 ST) as LO0.
  pose proof (bv_unsigned_in_range 64 sp) as SPB.
  try (unfold bv_modulus in SPB).
  try (cbn in SPB).
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  pose proof (rw_cells_bound _ _ _ _ HCUR) as CURB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ name_blob] in PPB, CURB.
  change (Z.of_nat 64) with 64 in CURB.
  change (Z.of_nat 8) with 8 in PPB.
  destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _].
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 144%nat ST.
  lxp_split_frame [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat.
  (* [comment removed for export] *)
  try (pose proof (heap_presx_refl usegs L LB (bv_unsigned sp) [(PP, PP + 8); (CUR, CUR + 64)] m) as HPX0).
  (* [comment removed for export] *)
  pose proof (@sums1_ok) as LXSUMS.
  lxp_run (PLANS [0x1efe0; 0x27dc0; 0x27dfc; 0x27ef4; 0x27f54; 0x27f84; 0x27ff8; 0x3f960] [] 155%N SUMS1).
  (* [comment removed for export] *)
  try (lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end).
  try (unfold name_blob in HCUR).
  try (replace (CUR + 8 + 8 + 16) with (CUR + 32) in W3 by lia).
  try (replace (CUR + 8 + 8 + 16 + 8) with (CUR + 40) in W4 by lia).
  try (eapply (outer_start L HI HCALLOC HFREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs);
    try exact INV1; try eassumption; try plia).
  lxp_apply (outer_start L HI HCALLOC HFREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs).  (* [comment removed for export] *)
  Unshelve. all: try lxp_default.   (* [comment removed for export] *)
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
