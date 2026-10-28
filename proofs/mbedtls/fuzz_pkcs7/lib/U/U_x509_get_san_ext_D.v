(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_asn1_get_tag U_asn1_get_len U_asn1_sequence_free U_asn1_free_named_data_list_shallow U_asn1_get_sequence_of_A U_x509_get_name_A U_x509_parse_san_A U_x509_parse_san U_x509_get_san_ext_A U_x509_get_san_ext_B U_x509_get_san_ext_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sum_getlen LxU_SumsHeapO.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P01993028afbeedf4 0 4 0 1 2 1 53 1 54 1P020cfafbd1e54933 0 1 1 1P020e43246015fca8 0 2 0 1 22 1P0249be3a5d0c0ccb 2 60 1 1 8 3 2 1 63 1 64 1 6 0 1 42 1 49 1 62 1 65 1 66 8 1 1 8 3 1 1 62 1 65 1 4 0 1 63 1 64 1 66 8P029554a8f8ddaca4 1 1 8 3 0 1 51 1 54 1 4 2 1 52 1 53 1 55 8P0391be0c917a2373 0 2 0 1 21 1P060c11bbf5b34f11 0 4 0 1 2 1 55 1 56 1P06bac6e8780a52f3 1 1 8 3 0 1 54 1 55 1 6 2 1 33 1 40 1 53 1 56 1 57 8P076a05ea2767ea2e 0 2 0 1 1 1P0770bcad1135a711 0 2 0 1 5 1P097b5dc77c1dae77 2 60 1 1 8 3 2 1 63 1 64 1 6 0 1 42 1 49 1 62 1 65 1 66 8 1 1 8 3 1 1 62 1 65 1 4 0 1 63 1 64 1 66 8P0c6315e5c104a276 2 26 1 1 8 3 1 1 54 1 55 1 6 0 1 33 1 40 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P0d9828c10c6c87a3 0 3 0 1 34 1 45 1P0da7ac6d5e8f041f 0 6 1 1 2 1 33 1 40 1 53 1 54 1P0daee213a7f670d0 2 33 0 6 0 1 3 1 43 1 50 1 63 1 64 1 0 4 0 1 2 1 63 1 64 1P0eaab44b94f41d49 1 1 8 3 0 1 51 1 54 1 4 2 1 52 1 53 1 55 8P0efa0375b6d36a6c 1 1 8 2 34 1 52 1 3 0 1 51 1 53 8P0f8da8155e2d3c5e 0 2 0 1 60 1P0fcb4279d036b5a3 0 2 0 1 61 1P1079b010ff118cd0 0 2 0 1 7 1P11830e03e8e729da 0 2 0 1 1 1P11bd1898660e9dd7 1 1 8 3 1 1 52 1 53 1 6 2 1 31 1 38 1 51 1 54 1 55 8P1234760c296537f0 1 1 8 3 1 1 52 1 53 1 6 2 1 31 1 38 1 51 1 54 1 55 8P126812878971c6cd 0 2 0 1 35 1P141246250a360f74 0 2 0 1 21 1P1487d97a6e5f4e02 2 26 1 1 8 3 2 1 54 1 55 1 6 0 1 33 1 40 1 53 1 56 1 57 8 1 1 8 3 1 1 53 1 56 1 4 0 1 54 1 55 1 57 8P15aa16bd381b036a 1 1 8 3 1 1 54 1 55 1 6 2 1 33 1 40 1 53 1 56 1 57 8P15d5809387144d95 2 35 1 1 8 3 2 1 63 1 64 1 6 0 1 42 1 49 1 62 1 65 1 66 8 1 1 8 3 1 1 62 1 65 1 4 0 1 63 1 64 1 66 8P171dc9a28e4c2269 0 1 1 1P1896ce072ef36a4f 2 33 0 6 0 1 3 1 43 1 50 1 63 1 64 1 0 4 0 1 2 1 63 1 64 1P1960819543e26396 2 26 1 1 8 3 1 1 54 1 55 1 6 0 1 33 1 40 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P1a276cd957604aa9 1 1 8 3 1 1 53 1 56 1 4 2 1 54 1 55 1 57 8P1afbe618ce2ef3a1 0 2 0 1 32 1P1c8ead6b4b1dfa8f 0 2 0 1 60 1P1d01ab86469eb78b 0 2 0 1 21 1P1e112bb3fd440cfe 0 4 0 1 3 1 52 1 53 1P228a13ab2e4ce1b1 0 2 0 1 6 1P23425f336332a692 0 2 0 1 36 1P237f2f1f071ca3d3 0 2 0 1 61 1P269f0496d4b3feb6 0 3 0 1 35 1 46 1P2854a5b8a2687baa 1 1 8 3 1 1 53 1 56 1 4 2 1 54 1 55 1 57 8P295110015dfb9aa7 0 2 0 1 5 1P29e851611bd02f50 0 2 0 1 47 1P2b8bd9276051a39b 0 2 0 1 5 1P2bc671edd01cd7cf 0 2 0 1 1 1P2e4d6cfb45eec3e6 0 2 0 1 22 1P2ec862bcd4d58193 1 1 8 3 1 1 54 1 55 1 4 2 1 53 1 56 1 57 8P303c2ebfa7179158 2 24 0 6 0 1 3 1 34 1 41 1 54 1 55 1 0 4 0 1 2 1 54 1 55 1P308043dca7e496c7 1 1 8 3 0 1 54 1 55 1 6 2 1 33 1 40 1 53 1 56 1 57 8P32562921f541de6a 0 2 0 1 21 1P34c97dae3d7b53ce 0 4 0 1 3 1 54 1 55 1P34e595324032548a 2 51 1 1 8 3 2 1 54 1 55 1 6 0 1 33 1 40 1 53 1 56 1 57 8 1 1 8 3 1 1 53 1 56 1 4 0 1 54 1 55 1 57 8P3507eb6213b2a7bf 0 6 1 1 3 1 32 1 39 1 52 1 53 1P36e678504313fe08 1 1 8 3 1 1 53 1 56 1 4 2 1 54 1 55 1 57 8P38281df05ca23e61 0 6 1 1 3 1 34 1 41 1 54 1 55 1P385ef94ecc136c8a 0 3 0 1 37 1 48 1P3b6114188e6fc5fb 2 35 1 1 8 3 2 1 63 1 64 1 6 0 1 42 1 49 1 62 1 65 1 66 8 1 1 8 3 1 1 62 1 65 1 4 0 1 63 1 64 1 66 8P3bd73f44efbd3a15 0 4 0 16 5 16 51 16 52 16P3c030f22225e2f28 2 26 1 1 8 3 1 1 54 1 55 1 6 0 1 33 1 40 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P3c9d1cda18876c6e 1 1 8 3 0 1 54 1 55 1 6 2 1 33 1 40 1 53 1 56 1 57 8P3dabc1a228f0875a 0 2 0 1 21 1P3e3c84af0f24acc1 1 1 8 3 0 1 53 1 56 1 4 2 1 54 1 55 1 57 8N0012947b4f049238N00ce05738e4a3b55N00d92cd57f267b11N013bd13892641abeN016471f8b61d1dfbN0294350123ce02ddN0311a42339f94794N035dec1aa8561c1cN03d28880730c5766N03eab024d2cbcd5bN03f4d58f66083883N046f7697aa5d7ff2N0478c9a2d7405d3fN053f1806a4b1ee2dN055af89328686c6dN057e67adcee7bc02N05d7ed0e2afaf361N05d8ccaf6da5a54aN0601dd3d0ba2ac54N0613d735de085f2bN06e2f1d6ec2bfffeN06e5b770b56b864bN07f1f14215a5e0e6N0825eb9f665e5d53N089174655ab557f5N0922b7f09560975eN0954eeb4d5dab15bN0956d9681941df0eN0966827e4562ab7aN09760bb21147d7bbN09cfed3d0c050579N0a4cbc66e4fd90afN0a62733a287211e0N0a9379daed6466e5N0ae16f0ccf94a3f9N0afc0fb1e642be6cN0b2b0e9238960c4eN0ba2acdb65f817c4N0bdd9a15a52907baN0beabbe77987cbbdN0c1ad4e8d5922140N0c3d2605b4e79002N0cdf60cf5399fcb9N0ce22c4f68b1bb31N0d8693901443e58aN0e05c2db47385b0cN0e23b95bfe08d803N0e55219e8c0948e9N0e86f9f4d21c7724N0e9b4a36c246288cN0ebf33b3a8b6654aN0efa77e38a0c5d85N0f304216b8029629N0f5ea52299495621N100e9644060832c3N103984f0b396b234N10436ea458f13120N10443450f02187d9N107adbcc65c32827N114e7894bc54e6ebN118a37859e88f6acN11f0f941f05962d0N1257c1047e667e10N13d172b258763b21N13e63231b99166a2N14076d1f2bb63bf6N140bf4082a4e4a1aN148c81ed06aa33cfN14ef1164f2589eabN1527c157538a82d1N1550d8fc20a44c79N156efc7d600fac0aN1587ae3c97564beeN15a1c248e5da22d5N15fe00769ec1dbafN1644a6347f1889c4N16b040dd9fdf6042N16d1fbe367de3afdN16f8e96d8ec0e76dN173c8529c48b4844N17e6ddec515ab5eaN17e9f5f97806774eN1841f1eab9c26343N1863d799ccc3b8b3N18a7cea58d8d0d71N18af359b5e7baaedN18c068a7d92e7d89N18fcf27450b8a8ebN199812b4dbbb4dd6N19e7a3f9f5fbb83eN1a22e50967171429N1a36ce006f485fdbN1a777c1a7f9e04e4N1a898be93bc0913aN1aa81cfeb9c3b03bN1ad881a34c1b289aN1bee6800bd62b800N1bf1e65761422da6N1d0876dc891af4a9N1d71c44a15b8e999N1de5eb1cd3846a1eN1ea8dc57df9aeaeaN1ead61ea57cdb94aN1f44b4f4f779a218N1fb309dcd328abd5N1fe2e1d2246e7017N202e1be04c4bc772N212d486597e755c6N218669cd393fbdc9N21c7e4d9263753b4N220097ecb064fce9N2286cdaf2beba3a1N22bb878b79722b03N22cea7b5f938ebc3N22ff1598996534c2N23cdde5c65b20981N24c92631e96cf158N24e02028c6a34ff2N2540808c72997f45N255228d52f09b8e3N2613a5921b0c14c4N266cd30fdd4718a8N268d2c629040a47aN269da09f452eedf7N277d1b2ee63bdeb9N27a5eed0ed0f8c77N27c45a4b4418d675N2821d2d35ae0cc3fN282e31c3880df4d2N29a1cf262590234eN29cbf67993c8037dN2b4f64be7baaf7f2N2b4fa6836027bc44N2b5220038b880f36N2b57614ba39f766aN2c91d30c3a9bfe16N2cbcc4a5588a2659N2cc4ac3eca0207f0N2db1ba0c8c35b6f7N2db20a1e3770129cN2de404a016f1025aN2e2504931f95a9fbN2f38d3cbef3e65a0N2f842a9631bce745N2f88de804d3571cfN2fbf1fdb96a9f498N310483d9f4c3c247N327b3b9bb56cdcb3N32e5f1717b26d614N34971311fd3f963aN350557a78e3fe1b6N35aed852a616697dN35f5be4f56e4d3c7N3605174c7fbba832N36909cbf31b1779dN3744b4700f75c89eN379c4546f91a415eN37d1381682c35054N37dcb245fe406b14N38254c004cec938cN3838f5b759ec764cN38e5c19d5e9715f1N390b881da28a6eb2N39240d2b740b1e15N3931e4467febbcc5N39be898e352df35bN3b4216d9d74109f2N3b48167da48f91abN3b644daf57cd3f0eN3bb101c928f12b54N3bdb1bbceff1591fN3be10f895ea3282dN3c14cf86aba3610fN3c16ed0f60d687faN3c76dd1f128db3bdN3cba089342e241aaN3cf260f1c676920eN3d5a9db25f49ce40N3d753140174724a9N3dc1c48521b734e5N3e27e8567bf20eeeN3e48848fa542fc13N3e5be36317ddc06aN3edae9d000d7e98bN3edb54a7e0f6f4baN3ef6c44c34324f2aN3f04ddb52da9504bN3f73e2a5b9ad4cfcN3ff2ebc05e5ec97dN3ffec3f5b324124c"%lxh.
Ltac2 gd_tbl_P_x509_get_san_ext_D () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.ninv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.x509_get_san_ext_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Walk.BodyOb"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.pair"; "Stdlib.Lists.List.rev"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.nLBof"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "Stdlib.Lists.List.NoDup"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.nfresh"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.curF"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.headrep"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_lseg"; "Stdlib.Lists.List.removelast"; "Stdlib.Lists.List.last"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Spec.RepName.name_blob"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.name_chain"; "Corelib.Init.Logic.True"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.frame_hi"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "Stdlib.ZArith.BinInt.Z.sub"].


Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model)
            (h : HST usegs L HI) (LB : list blk) (PP CUR P END BUF lo : Z) (bs : list byte).
  Notation CTX := (ext_ctx usegs L HI U_CALLOC U_FREE sp tp h LB PP CUR P END BUF lo bs).
  Hypothesis HC : CTX.

  Notation X := [(PP, PP + 8); (CUR, CUR + 32)].
  Notation POST := (x509_get_san_ext_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END BUF lo m mo).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -224)).
  Notation INV := (ninv L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo h LB PP CUR END BUF lo bs).
  Notation K4W := (Z_to_bv 64 (-9570)) (only parsing).
  Notation K7W := (Z_to_bv 64 (-9472)) (only parsing).
  Notation K8W := (Z_to_bv 64 (-8320)) (only parsing).
  Notation K9W := (Z_to_bv 64 (-9578)) (only parsing).
  Let sync_W' := sync_W L HI sp tp m h LB PP CUR P END BUF lo bs HC.
  Let presx_W' := presx_W L HI sp tp m h LB PP CUR P END BUF lo bs HC.
  Let heap_W' := heap_W L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let snoc_facts' := snoc_facts L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let others_apart' := others_apart L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let cur_wrange' := cur_wrange L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let headrep_pres' := headrep_pres L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let headrep_presx' := headrep_presx L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let presx_call' := presx_call L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let cur_cases' := cur_cases L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let in_block_below' := in_block_below L HI sp tp h LB PP CUR P END BUF lo bs HC.
  Let close_nodes' := close_nodes sp LB PP CUR END BUF lo bs.
  Let headrep_snoc' := headrep_snoc sp PP CUR END BUF lo bs.
  Let presx_munch' := presx_munch L sp LB PP CUR.

  Ltac open_ninv INV :=
    pose proof INV as INVc;
    (flat constr:(INVc) 19%nat; flclear INVc; intros HH HT HND HFR HCF HHD HLS' F0 FB SZB FS SZS FT FRH ST MI HBUF HPX MF);
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK; pose proof (conj HH I) as HHbox;
    pose proof HCF as HCFc; (flat constr:(HCFc) 7%nat; flclear HCFc; intros CAL CPOS C32 CPP CBF CSTK _);
    try unfold frame_hi in FRH.

  (* [comment removed for export] *)
  Ltac start_W cur :=
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (munch_refl (W sp PP cur) mx) as MU; unfold W in MU; pose proof (wmono_refl usegs mx) as WM end.

  (* [comment removed for export] *)
  Ltac wsync :=
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with
      | HHbox : HEAP _ _ _ ?hc ?LBx ?mm ?moc /\ True, HT : heap_top _ _ _ ?hc = _, HCF : curF _ _ _ _ _ _ ?nodes ?cur,
        HND : List.NoDup ?nodes, HFR : nfresh _ _ ?nodes,
        MU : munch _ ?mm mx, WM : wmono _ ?mm mx, HHD : headrep CUR END BUF ?mm ?nodes,
        HLS' : seq_lseg _ ?mm _ BUF END (removelast ?nodes) _, HPX : heap_presx _ _ LB _ _ m ?mm |- _ =>
          let A := fresh "HH" in let B := fresh "HHD" in let C := fresh "HLS'" in let D := fresh "HPX" in
          let HS := fresh "HS" in
          assert (HS : forall b, In b (nLBof LB nodes) -> In b LBx)
            by first [ exact (fun b Hb => Hb) | exact (fun b Hb => or_intror Hb) | solve_sub ];
          repeat match goal with H : HEAP _ _ _ _ _ _ _ |- _ => clear H end;
          repeat match goal with H : MOK _ |- _ => clear H end;
          (flat constr:((sync_W' _ _ _ _ _ _ _ _ _ (proj1 HHbox) HT HS HND HFR HCF HHD HLS' HPX MU WM)) 4%nat; intros A B C D); clear HS;
          clear HHbox HHD HLS' HPX MU WM;
          match goal with HHn : HEAP _ _ _ _ _ mx _ |- _ => pose proof (conj HHn I) as HHbox; pose proof (heap_mok _ _ HI _ _ _ _ HHn) as MK end;
          rename A into HH; rename B into HHD; rename C into HLS'; rename D into HPX;
          pose proof (munch_refl (W sp PP cur) mx) as MU; unfold W in MU; pose proof (wmono_refl usegs mx) as WM
      end
    end.

  (* [comment removed for export] *)
  Ltac rebuild_ninv INVn :=
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with
    | HH : HEAP _ _ _ ?hc (nLBof LB ?nodes) mx mox, HCF : curF _ _ _ _ _ _ ?nodes ?cur,
      F0 : rw_cells _ mx (bv_unsigned sp + -224) [CB 8 ?j0], FB : rw_cells _ mx (bv_unsigned sp + -216) ?fb,
      FS : rw_cells _ mx (bv_unsigned sp + -192) ?fs, FT : rw_cells _ mx (bv_unsigned sp + -112) [C8 ?tl] |- _ =>
        assert (INVn : INV mx mox hc nodes cur j0 fb fs tl);
        [ unfold ninv; repeat match goal with |- _ /\ _ => split end; try assumption;
          try (simpl_sizes; reflexivity);
          try (etransitivity; eassumption); try (eapply mo_frame_trans; eassumption) | ]
    end end.

  (* [comment removed for export] *)
  Definition BodyOb (p : Z) : Prop :=
    forall (nodes : list Z) (cur : Z) (ct cpad : word) (cl cp : Z) (j0 : list byte) (fb fs : list cell) (tl : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mm : mem) (moc : Model) (hc : HST usegs L HI),
    INV mm moc hc nodes cur j0 fb fs tl -> rw_cells usegs mm cur (seq_cells ct cpad cl cp 0) ->
    (cp = 0 /\ cl = 0 /\ nodes = []) \/ (BUF <= cp /\ 0 <= cl /\ cp + cl <= END) ->
    rw_cells usegs mm PP [C8 (Z_to_bv 64 p)] -> P <= p -> p < END ->
    aevtM usegs moc POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 CUR) (Z_to_bv 64 END) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (-9570)) (Z_to_bv 64 PP) (Z_to_bv 64 (-1)) (Z_to_bv 64 cur) (Z_to_bv 64 128) (Z_to_bv 64 4)
             (Z_to_bv 64 (-9472)) (Z_to_bv 64 (-8320)) (Z_to_bv 64 (-9578)) (Z_to_bv 64 p) x28 x29 x30 x31)
          F (Z_to_bv 64 0x2880c) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Let alloc_walk' := alloc_walk L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs HC.
  Let epi_inv' := epi_inv L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs HC.
  Let fatal_walk' := fatal_walk L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs HC.

  (* [comment removed for export] *)
  Lemma ok_walk : forall (p0 p1 : Z) (Lw tb pd : word) (nodes : list Z) (cur : Z) (ct cpad : word) (cl cp : Z) (j0 : list byte) (tl : word)
      (t dn : Z) (rest : list cell) (pnodes : list Z)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 : word) (m6 : mem) (mo6 : Model) (h6 : HST usegs L HI),
    (forall p' : Z, p0 < p' -> BodyOb p') ->
    HEAP usegs L HI h6 (map (fun a : Z => (a, 64)) (rev pnodes) ++ nLBof LB nodes) m6 mo6 ->
    heap_top usegs L HI h6 = heap_top usegs L HI h ->
    Stdlib.Lists.List.NoDup nodes -> nfresh L LB nodes -> curF sp PP CUR BUF lo bs nodes cur ->
    headrep CUR END BUF m6 nodes -> seq_lseg usegs m6 (nLBof LB nodes) BUF END (removelast nodes) (last nodes 0) ->
    rw_cells usegs m6 (bv_unsigned sp + -224) [CB 8 j0] ->
    rw_cells usegs m6 (bv_unsigned sp + -216) [C4 tb; C4 pd; C8 Lw; C8 (Z_to_bv 64 p1)] ->
    rw_cells usegs m6 (bv_unsigned sp + -192) (C4 (Z_to_bv 64 t) :: rest) -> Z.of_nat (cells_size rest) = 76 -> 0 <= t <= 7 ->
    (t = 4 -> exists (p4 j48 : list byte) (mg : byte) (pad7 j8 : list byte), rest = CB 4 p4 :: name_blob j48 dn mg pad7 ++ [CB 8 j8]) ->
    (t = 4 -> name_chain usegs (fun _ : list cell => True) m6 (map (fun a : Z => (a, 64)) (rev pnodes) ++ nLBof LB nodes) dn pnodes) ->
    (t <> 4 -> pnodes = []) -> Stdlib.Lists.List.NoDup pnodes ->
    rw_cells usegs m6 (bv_unsigned sp + -112) [C8 tl] ->
    rw_cells usegs m6 (bv_unsigned sp + -104) (frame_hi ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    stk usegs m6 lo (bv_unsigned sp + -224) -> mem_inv usegs m6 -> bytes_at usegs m6 BUF bs ->
    heap_presx usegs L LB (bv_unsigned sp) X m m6 -> mo_frame mo mo6 ->
    rw_cells usegs m6 cur (seq_cells ct cpad cl cp 0) ->
    (cp = 0 /\ cl = 0 /\ nodes = []) \/ (BUF <= cp /\ 0 <= cl /\ cp + cl <= END) ->
    rw_cells usegs m6 PP [C8 (Z_to_bv 64 p1)] -> P <= p0 -> p0 < p1 -> BUF <= p1 -> bv_unsigned Lw <= END - p1 ->
    aevtM usegs mo6 POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 CUR) (Z_to_bv 64 END) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 (-9570)) (Z_to_bv 64 PP) (Z_to_bv 64 (-1)) (Z_to_bv 64 cur) (Z_to_bv 64 128) (Z_to_bv 64 4)
             (Z_to_bv 64 (-9472)) (Z_to_bv 64 (-8320)) (Z_to_bv 64 (-9578)) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x28878) fc None m6 (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros p0 p1 Lw tb pd nodes cur ct cpad cl cp j0 tl t dn rest pnodes x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x27 x28 x29 x30 x31 m6 mo6 h6
      KLOOP HH HT HND HFR HCF HHD HLS' F0 FB FS SZR Ht7 Hsh Hch Ht4 HNDp FT FRH ST MI HBUF HPX MF HCUR HCB HPP Hp0 Hp01 Hp1 HL.
    open_ectx HC. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. unfold frame_hi in FRH.
    pose proof HCF as HCFc. flat constr:(HCFc) 7%nat. flclear HCFc. intros CAL CPOS C32 CPP CBF CSTK _.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn in LR.
    zstep. zstep. if_cases K4; zify_cond K4.
    - (* [comment removed for export] *)
      assert (PN : pnodes = []) by (apply Ht4; clear -K4; rewrite ?unsigned_lit in K4 by lia; intros E; apply K4; rewrite E; reflexivity).
      subst pnodes. cbn [rev map app] in HH.
      assert (INV6 : INV m6 mo6 h6 nodes cur j0 [C4 tb; C4 pd; C8 Lw; C8 (Z_to_bv 64 p1)] (C4 (Z_to_bv 64 t) :: rest) tl).
      { unfold ninv. repeat match goal with |- _ /\ _ => split end; try assumption. reflexivity. cbn [cells_size csize]. clear -SZR. lia. }
      eapply alloc_walk'; try exact INV6; try eassumption.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in K4 by (clear; lia).
      assert (T4 : t = 4).
      { revert K4. clear -Ht7. intros K4. cbv [sx32] in K4. rewrite ?Z_to_bv_unsigned in K4.
        unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in K4.
        change (Z.of_N 64) with 64 in K4. change (Z.of_N 32) with 32 in K4. change (2 ^ (32 - 1)) with 2147483648 in K4. lia. }
      subst t. clear K4 Ht4 Ht7. flat constr:((Hsh eq_refl)) 6%nat. intros p4 j48 mg pad7 j8 ->. specialize (Hch eq_refl).
      unfold name_blob in FS. cbn [app] in FS.
      pose proof (cur_wrange' nodes cur _ HFR HCF ltac:(intros b Hb; exact Hb)) as CWc0.
      pose proof CWc0 as CWc. rewrite <- HT in CWc. pose proof HTOP as HTOPc. rewrite <- HT in HTOPc.
      zstep. zstep.
      pose proof (U_asn1_free_named_data_list_shallow_spec L HI HFREE HLS) as SPF'.
      unfold asn1_free_named_data_list_shallow_stmt, U_ASN1_FREE_NAMED_DATA_LIST_SHALLOW in SPF'.
      eapply aevtM_cut; [ eapply SPF' with (a := dn) (nodes := pnodes) (lo := lo) (h := h6);
         rewrite ?(unsigned_lit (bv_unsigned sp + -224)) by dlia; try eassumption; try reflexivity | ].
      { clear -SLO HLS. lia. }
      { clear -HTOPc. lia. }
      { clear -SPA. lia. }
      clear SPF'.
      intros ms' mo' PO. unfold asn1_free_named_data_list_shallow_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
      injection E as E1 E2. subst ms' mo'.
      rewrite ?(unsigned_lit (bv_unsigned sp + -224)) in PO by dlia.
      flat constr:(PO) 6%nat. flclear PO. intros MI7 ST7 MF7 HT7 HH7 HP7.
      rewrite (lb_remove_all_new pnodes (nLBof LB nodes) HNDp) in HH7, HP7.
      lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
      lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m7; rename mox into mo7 end.
      match type of HH7 with HEAP _ _ _ ?hh _ _ _ => rename hh into h7 end.
      pose proof (headrep_pres' nodes _ _ _ HP7 (nLBof_sub LB nodes) HHD) as HHD7.
      pose proof (lseg_pres _ _ _ _ _ _ _ _ _ HP7 HLS') as HLS7.
      assert (HPX7 : heap_presx usegs L LB (bv_unsigned sp) X m m7).
      { eapply heap_presx_trans; [exact HPX|]. eapply heap_presx_of_pres_sub; [exact HP7| apply nLBof_sub| clear; lia| clear; lia]. }
      clear ST MI MK HH HHD HLS' HPX Hch Hsh. heap_transport HP7. clear HP7.
      rewrite HT in HT7.
      assert (INV7 : INV m7 mo7 h7 nodes cur j0 [C4 tb; C4 pd; C8 Lw; C8 (Z_to_bv 64 p1)]
                         [C4 (Z_to_bv 64 4); CB 4 p4; CB 48 j48; C8 (Z_to_bv 64 dn); C1 mg; CB 7 pad7; CB 8 j8] tl).
      { unfold ninv. repeat match goal with |- _ /\ _ => split end; try assumption. reflexivity. reflexivity.
        eapply mo_frame_trans; eassumption. }
      eapply alloc_walk'; try exact INV7; try eassumption.
  Qed.

  (* [comment removed for export] *)
  Ltac flia := first [clear_disj; lia | lia].
  Lemma zbv_mod64 : forall a b, (a - b) mod 18446744073709551616 = 0 -> (Z_to_bv 64 a : word) = Z_to_bv 64 b.
  Proof.
    intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    apply Z.mod_divide in H; [| lia]. flat constr:(H) 2%nat. flclear H. intros k Hk. replace a with (b + k * 18446744073709551616) by lia. apply Z.mod_add. lia.
  Qed.
  Ltac spine_firstn k cs :=
    let k := eval cbv in k in
    lazymatch k with
    | Datatypes.O => eval lazy beta iota delta [firstn] in (firstn Datatypes.O cs)
    | Datatypes.S ?k' => lazymatch cs with
               | ?c :: ?cs' => let r := spine_firstn k' cs' in constr:(c :: r)
               | _ => eval cbv beta iota delta [firstn] in (firstn k cs)
               end
    end.
  Ltac spine_skipn k cs :=
    let k := eval cbv in k in
    lazymatch k with
    | Datatypes.O => cs
    | Datatypes.S ?k' => lazymatch cs with
               | _ :: ?cs' => spine_skipn k' cs'
               | _ => eval cbv beta iota delta [skipn] in (skipn k cs)
               end
    end.
  Ltac zofnat H := cbn [cells_size csize Nat.add length] in H;
    repeat match type of H with context [Z.of_nat (Datatypes.S ?k)] => let v := eval vm_compute in (Z.of_nat (Datatypes.S k)) in change (Z.of_nat (Datatypes.S k)) with v in H end;
    repeat match type of H with context [Z.add (Z.add ?a ?b) ?c] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (Z.add b c) in replace (Z.add (Z.add a b) c) with (Z.add a v) in H by lia end.
  Ltac splitat H k H2 :=
    lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
      let l1 := spine_firstn k cs in
      let l2 := spine_skipn k cs in
      change (rw_cells sg mm A0 (l1 ++ l2)) in H;
      let H1 := fresh "SP" in
      (flat constr:((proj1 (rw_cells_app sg mm A0 l1 l2) H)) 2%nat; intros H1 H2); clear H; rename H1 into H; zofnat H2
    end.


  (* [comment removed for export] *)
  Ltac cells_upto cs n :=
    lazymatch n with
    | 0%nat => constr:(0%nat)
    | _ => lazymatch cs with ?c :: ?cs' => let k := eval cbn in (n - csize c)%nat in let r := cells_upto cs' k in constr:(S r) end
    end.
  Ltac cutsz mx A n :=
    try (lazymatch goal with H : rw_cells _ mx A ?cs |- _ =>
      let tot := eval cbn in (cells_size cs) in
      lazymatch eval compute in (Nat.ltb n tot) with
      | true => let k := cells_upto cs n in let H2 := fresh "FX" in splitat H k H2
      | false => idtac end end).
  (* [comment removed for export] *)
  Ltac cut_locals mx :=
    cutsz mx (bv_unsigned sp + -224) 8%nat; cutsz mx (bv_unsigned sp + -216) 24%nat;
    cutsz mx (bv_unsigned sp + -192) 80%nat; cutsz mx (bv_unsigned sp + -112) 8%nat.

  (* [comment removed for export] *)
  Lemma body_walk : forall p0, (forall p', p0 < p' -> BodyOb p') -> BodyOb p0.
  Proof.
    intros p0 KLOOP. unfold BodyOb.
    intros nodes cur ct cpad cl cp j0 fb fs tl x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm moc hc INV HCUR HCB HPP Hp0 HpE.
    open_ninv INV. clear INV. open_ectx HC. unfold seq_cells in HCUR.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    (* [comment removed for export] *)
    flat constr:((rw_cells_forget _ _ _ _ FB)) 2%nat. intros jb FB'. clear FB. rewrite SZB in FB'. rename FB' into FB.
    flat constr:((rw_cells_forget _ _ _ _ FS)) 2%nat. intros js FS'. clear FS. rewrite SZS in FS'. rename FS' into FS. clear SZB SZS.
    clear HHbox.
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) [SUM_memset0P 80; SUM_getlenP])
      by (intros AL; repeat constructor; apply apply_summary_sound; first [apply sum_memset0P_valid; lia | apply sum_getlenP_valid]).
    rewrite TP. apply (lxp_aevtM_of_evt usegs moc _ _ MK).
    lx_run_tac (PLANS [0x28938; 0x289b8] [] 80%N [SUM_memset0P 80; SUM_getlenP]); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    all: repeat match goal with |- context [Z_to_bv 64 (Zpos ?p)] =>
           let z := constr:(Zpos p) in
           lazymatch eval compute in (Z.leb (2^63) z) with
           | true => let z' := eval compute in (z - 2^64)%Z in replace (Z_to_bv 64 z : word) with (Z_to_bv 64 z' : word) by (apply zbv_mod64; reflexivity)
           end end.
    (* [comment removed for export] *)
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hm1 : munch ?W1 ?mA mx, Hw1 : wmono _ ?mA' mx, HCFx : curF _ _ _ _ _ _ ?nodesx ?curx |- _ =>
           let MUW := fresh "MUW" in
           assert (MUW : munch (W sp PP curx) mA mx) by (eapply munch_weaken; [| exact Hm1]; intros xw Hxw; clear - Hxw; cbn [outside W] in Hxw |- *; lia);
           let A := fresh "HH" in let B := fresh "HHD" in let C := fresh "HLS'" in let D := fresh "HPX" in
           destruct (sync_W' _ _ _ _ _ _ _ _ _ HH HT ltac:(intros bb Hbb; exact Hbb) HND HFR HCF HHD HLS' HPX MUW Hw1) as (A & B & C & D);
           clear HH HHD HLS' HPX MUW Hm1 Hw1 MK; rename A into HH; rename B into HHD; rename C into HLS'; rename D into HPX;
           pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK; pose proof (conj HH I) as HHbox;
           try clear ST MI HBUF HCUR HPP F0 FB FS FT FRH;
           (* [comment removed for export] *)
           cut_locals mx
         end end.
    (* [comment removed for export] *)
    all: lazymatch goal with
         | |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 0x28938) _ _ ?mx _) =>
             rebuild_ninv INV2;
             eapply epi_inv'; [exact INV2| eassumption| exact HCB| eassumption| flia| flia]
         | |- _ => idtac end.
    (* [comment removed for export] *)
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => set (m5 := mx) in * end.
    lazymatch goal with H : rw_cells _ m5 (bv_unsigned sp + -224) _ |- _ => rename H into F0 end.
    lazymatch goal with H : rw_cells _ m5 (bv_unsigned sp + -216) _ |- _ => rename H into FB end.
    lazymatch goal with H : rw_cells _ m5 (bv_unsigned sp + -192) _ |- _ => rename H into FS end.
    lazymatch goal with H : rw_cells _ m5 (bv_unsigned sp + -112) _ |- _ => rename H into FT end.
    lazymatch goal with H : rw_cells _ m5 (bv_unsigned sp + -104) _ |- _ => rename H into FRH end.
    lazymatch goal with H : rw_cells _ m5 PP _ |- _ => rename H into HPP end.
    lazymatch goal with H : rw_cells _ m5 cur _ |- _ => rename H into HCUR end.
    lazymatch goal with H : stk _ m5 lo _ |- _ => rename H into ST end.
    lazymatch goal with H : mem_inv _ m5 |- _ => rename H into MI end.
    lazymatch goal with H : bytes_at _ m5 BUF bs |- _ => rename H into HBUF end.
    lazymatch type of FB with rw_cells _ _ _ (?c0 :: CB 4 _ :: _) => cb4_to_c4 FB [c0] | _ => idtac end.
    lazymatch type of FB with rw_cells _ _ _ [C4 (Z_to_bv 64 ?tb0); C4 ?pdw; C8 (Z_to_bv 64 ?L0); C8 (Z_to_bv 64 ?q0)] =>
      set (tb := tb0) in *; set (Ln := L0) in *; set (p1 := q0) in * end.
    assert (HLn : 0 <= Ln < 2^64) by (subst Ln; flia).
    assert (PC : p0 + 1 <= p1 <= END) by (subst p1; flia).
    assert (PT1 : p0 + 1 + 1 <= p1) by (subst p1; flia).
    assert (PT2 : Ln <= END - p1) by (subst p1 Ln; flia).
    assert (TBR : 0 <= tb < 256) by (subst tb; flia).
    pose proof HTOP as HTOPc. rewrite <- HT in HTOPc.
    pose proof (U_x509_parse_san_spec L HI HCALLOC HFREE HLS) as SPS. unfold x509_parse_san_stmt, U_X509_PARSE_SAN in SPS.
    eapply aevtM_cut;
      [ eapply SPS with (SB := bv_unsigned sp + -216) (SAN := bv_unsigned sp + -192) (BUF := BUF) (bs := bs) (sp0 := p1)
                        (slen := Ln) (lo := lo) (LB := nLBof LB nodes) (h := hc);
        rewrite ?(unsigned_lit (bv_unsigned sp + -224)) by dlia; try eassumption; try reflexivity; try flia2 | ].
    all: lazymatch goal with
         | |- client_range _ _ _ (bv_unsigned sp + -216) _ => apply client_range_stack; clear -SLO HLS; lia
         | |- client_wrange _ _ _ _ (bv_unsigned sp + -192) _ => apply client_wrange_stack; [clear -SLO HLS; lia| clear -HTOPc; lia]
         | |- client_range _ _ _ BUF _ => eapply client_range_sep; [exact CRBUF| apply nLBof_sub| clear -DS3 ACL SLO HLS; lia]
         | |- _ => idtac end.
    clear SPS.
    intros ms' mo' PO. unfold x509_parse_san_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -224)) in PO by dlia.
    flat constr:(PO) 17%nat. flclear PO. intros MI6 ST6 MF6 HT6 Ha0 Hr6 HSAN6 SZR Ht7 Hsh Hch Ht4 Hr0 HNDp HAPp HH6 HPX6.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m6; rename mox into mo6 end.
    match type of HH6 with HEAP _ _ _ ?hh _ _ _ => rename hh into h6 end.
    match type of Ha0 with ?x = Z_to_bv 64 ?rr => subst x; rename rr into r end.
    match type of HSAN6 with rw_cells _ _ _ (C4 (Z_to_bv 64 ?tt) :: ?rr) => rename tt into t; rename rr into rest end.
    match type of Hch with _ -> name_chain _ _ _ _ ?d ?pn => rename d into dn; rename pn into pnodes end.
    pose proof (heap_mok _ _ HI _ _ _ _ HH6) as MK6.
    (* [comment removed for export] *)
    lazymatch type of HPX6 with heap_presx _ _ _ _ ?Xc ?ma m6 =>
    assert (TR : forall A cs, rw_cells usegs ma A cs -> client_range L (nLBof LB nodes) (bv_unsigned sp + -224) A (Z.of_nat (cells_size cs)) ->
                 disjoint_from Xc A (Z.of_nat (cells_size cs)) -> rw_cells usegs m6 A cs)
      by (intros A cs HR HCR HD; exact (heap_presx_rw_cells usegs L _ _ _ _ _ _ _ HPX6 HR HCR HD)) end.
    apply TR in F0; [| apply client_range_stack; clear; lia | simpl_sizes; cbn [disjoint_from]; clear; lia ].
    apply TR in FB; [| apply client_range_stack; clear; lia | simpl_sizes; cbn [disjoint_from]; clear; lia ].
    apply TR in FT; [| apply client_range_stack; clear; lia | simpl_sizes; cbn [disjoint_from]; clear; lia ].
    apply TR in FRH; [| apply client_range_stack; simpl_sizes; clear; lia | simpl_sizes; cbn [disjoint_from]; clear; lia ].
    apply TR in HPP; [| simpl_sizes; eapply client_range_wsep; [exact CWPP| apply nLBof_sub| clear -DS1; lia] | simpl_sizes; cbn [disjoint_from]; clear -DS1 SLO HLS; lia ].
    apply TR in HCUR; [| simpl_sizes; eapply client_range_wsep; [eapply cur_wrange'; [exact HFR| exact HCF| intros bb Hbb; exact Hbb] | intros bb Hbb; exact Hbb| clear -CSTK; lia]
                      | simpl_sizes; cbn [disjoint_from]; clear -CSTK SLO HLS; lia ].
    clear TR.
    pose proof (headrep_presx' nodes _ _ _ _ HPX6 (nLBof_sub LB nodes) ltac:(cbn [disjoint_from]; clear -DS2 SLO HLS; lia) HHD) as HHD6.
    assert (HLS6 : seq_lseg usegs m6 (nLBof LB nodes) BUF END (removelast nodes) (last nodes 0)).
    { eapply lseg_presx; [exact HPX6| exact HLS'|]. intros y Hy. split; [eapply seq_lseg_in; [exact HLS'| exact Hy]|].
      flat constr:((HFR y (in_removelast _ _ Hy))) 3%nat. intros Yc _ _. cbn [disjoint_from]. clear -Yc ACL SLO HLS. lia. }
    assert (HBUF6 : bytes_at usegs m6 BUF bs).
    { eapply heap_presx_bytes_at; [exact HPX6| exact HBUF| |].
      - eapply client_range_sep; [exact CRBUF| apply nLBof_sub| clear -DS3; lia].
      - cbn [disjoint_from]. clear -DS3 SLO HLS. lia. }
    pose proof (heap_presx_trans usegs L _ _ _ _ _ _ HPX (presx_call' _ _ _ _ _ HPX6 (nLBof_sub LB nodes) ltac:(clear; lia) ltac:(clear; lia))) as HPXn.
    clear HPX HPX6 HBUF HHD HLS' ST MI HH. try clear MK HHbox. rename HPXn into HPX. rename HBUF6 into HBUF. rename HHD6 into HHD. rename HLS6 into HLS'.
    rewrite HT in HT6.
    (* [comment removed for export] *)
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo6 _ _ MK6).
    lx_run_tac (PLANS [0x28878; 0x28998] [] 40%N [SUM_memset0P 80; SUM_getlenP]); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
    all: lazymatch goal with
         | |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 0x28878) _ _ _ _) =>
             eapply ok_walk; try eassumption; first [eapply mo_frame_trans; eassumption | rewrite ?unsigned_lit by flia; flia]
         | |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 0x28998) _ _ _ _) =>
             assert (PN : pnodes = []) by (apply Hr0; flia);
             subst pnodes; cbn [rev map app] in HH6;
             lazymatch type of FB with rw_cells _ _ _ ?fb =>
               assert (INV6 : INV m6 mo6 h6 nodes cur j0 fb (C4 (Z_to_bv 64 t) :: rest) (Z_to_bv 64 Ln));
               [ unfold ninv; repeat match goal with |- _ /\ _ => split end; try assumption;
                 first [reflexivity | cbn [cells_size csize]; clear -SZR; lia | eapply mo_frame_trans; eassumption]
               | eapply fatal_walk'; try exact INV6; try eassumption; flia ] end
         end.
  Qed.
End Walk.
