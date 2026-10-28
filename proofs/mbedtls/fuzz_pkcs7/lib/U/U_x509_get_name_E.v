(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_x509_get_name_B U_x509_get_name_C U_x509_get_name_D.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_len U_asn1_free_named_data_list_shallow U_x509_get_name_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPHeap. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P003cdd01bf373fdf 2 53 1 1 8 3 1 1 74 1 75 1 6 0 1 56 1 57 1 73 1 76 1 77 8 1 1 8 3 2 1 73 1 76 1 4 0 1 74 1 75 1 77 8P0059dc69fe70d927 0 2 0 1 69 1P0086b004b2d9308a 0 2 0 1 68 1P01897fba277c9d08 1 1 8 3 0 1 76 1 77 1 6 2 1 58 1 59 1 75 1 78 1 79 8P01eacdf109bc78c8 0 5 0 1 1 1 37 1 38 1 55 1P02d531533ee6d829 0 2 0 1 6 1P036836cb023d3ab3 0 9 0 1 29 1 36 1 37 1 41 1 51 1 53 1 54 1 55 1P048a718590315ae1 2 48 1 1 8 3 1 1 67 1 68 1 6 0 1 51 1 52 1 66 1 69 1 70 8 1 1 8 3 2 1 66 1 69 1 4 0 1 67 1 68 1 70 8P07571fd924401a31 0 5 0 1 5 1 41 1 42 1 59 1P08904bd6615e4e28 0 2 0 1 7 1P0898d1e3ce0aa73d 0 4 0 1 2 1 77 1 78 1P090652870f87063d 2 38 1 1 8 3 1 1 76 1 77 1 6 0 1 58 1 59 1 75 1 78 1 79 8 1 1 8 3 2 1 75 1 78 1 4 0 1 76 1 77 1 79 8P09461a9dc51a223b 0 2 0 1 1 1P0995327f3073fab7 2 31 1 1 8 3 1 1 67 1 68 1 6 0 1 51 1 52 1 66 1 69 1 70 8 1 1 8 3 2 1 66 1 69 1 4 0 1 67 1 68 1 70 8P0a49f14b98ba6af4 0 4 0 1 2 1 75 1 76 1P0b4ede9993fd3cc5 2 48 1 1 8 3 1 1 67 1 68 1 6 0 1 51 1 52 1 66 1 69 1 70 8 1 1 8 3 2 1 66 1 69 1 4 0 1 67 1 68 1 70 8P0c2f5422758fc695 0 2 0 1 1 1P0cfeab165e2c96c4 1 1 8 3 0 1 76 1 77 1 6 2 1 58 1 59 1 75 1 78 1 79 8P0d8035dd71df53a1 0 2 0 1 7 1P0dda6e1847aba799 0 2 0 1 3 1P0e4b223d6330aaff 0 2 0 1 27 1P101a7856aa87c4af 0 4 0 1 30 1 42 1 56 1P105535f7963c0c2f 2 48 1 1 8 3 1 1 67 1 68 1 6 0 1 51 1 52 1 66 1 69 1 70 8 1 1 8 3 2 1 66 1 69 1 4 0 1 67 1 68 1 70 8P10b2eebc1b093f4b 2 48 1 1 8 3 1 1 67 1 68 1 6 0 1 51 1 52 1 66 1 69 1 70 8 1 1 8 3 2 1 66 1 69 1 4 0 1 67 1 68 1 70 8P1109e5c61dbfb9c1 0 2 0 1 29 1P1141a84eb9c7a6ca 0 2 0 1 1 1P11fe8f0471c33d80 0 2 0 1 1 1P12290859c6cb757b 2 31 1 1 8 3 1 1 67 1 68 1 6 0 1 51 1 52 1 66 1 69 1 70 8 1 1 8 3 2 1 66 1 69 1 4 0 1 67 1 68 1 70 8P127f1e83affbc508 2 38 1 1 8 3 1 1 76 1 77 1 6 0 1 58 1 59 1 75 1 78 1 79 8 1 1 8 3 2 1 75 1 78 1 4 0 1 76 1 77 1 79 8P14885c8c5d5c8477 0 2 0 1 1 1P153c6d18a4337fe8 2 31 1 1 8 3 1 1 67 1 68 1 6 0 1 51 1 52 1 66 1 69 1 70 8 1 1 8 3 2 1 66 1 69 1 4 0 1 67 1 68 1 70 8P1550e1863025dc6a 0 2 0 1 1 1P1557f00fd94068c6 0 2 0 1 1 1P15d76e3b937d2856 0 2 0 1 2 1P1637c009ec08a117 0 2 0 1 68 1P1ae01066bb2c23a3 0 4 0 1 43 1 44 1 61 1P1af269c4b0f2506b 0 4 0 1 2 1 77 1 78 1P1b547dbcccd287b3 2 53 1 1 8 3 1 1 74 1 75 1 6 0 1 56 1 57 1 73 1 76 1 77 8 1 1 8 3 2 1 73 1 76 1 4 0 1 74 1 75 1 77 8P1b7d739cf63fb527 1 1 8 3 1 1 75 1 78 1 4 2 1 76 1 77 1 79 8P1c96f0873f175ed7 1 1 8 3 0 1 76 1 77 1 6 2 1 58 1 59 1 75 1 78 1 79 8P1cd5f07449b45f6c 0 2 0 1 5 1P1daa7fb31368aaae 1 1 8 3 0 1 76 1 77 1 6 2 1 58 1 59 1 75 1 78 1 79 8P1df6d3924b40a621 0 2 0 1 68 1P1f379c481575074d 0 2 0 1 29 1P1f8f9b14650924b2 0 2 0 1 27 1P2015c9fd50fd9561 0 2 0 1 28 1P2042433b2fc8c42f 2 38 1 1 8 3 1 1 76 1 77 1 6 0 1 58 1 59 1 75 1 78 1 79 8 1 1 8 3 2 1 75 1 78 1 4 0 1 76 1 77 1 79 8P2086c15735c3d944 1 1 8 3 1 1 75 1 78 1 4 2 1 76 1 77 1 79 8P22f88ce223024c8d 0 4 0 1 36 1 48 1 62 1P26e6fc1ee5c1fa43 1 1 8 3 1 1 75 1 78 1 4 2 1 76 1 77 1 79 8P27545e06f09ebbc0 2 38 1 1 8 3 1 1 76 1 77 1 6 0 1 58 1 59 1 75 1 78 1 79 8 1 1 8 3 2 1 75 1 78 1 4 0 1 76 1 77 1 79 8P28706112a3aaf76b 1 1 8 3 1 1 76 1 77 1 4 2 1 75 1 78 1 79 8P28dcc2c2f985de68 1 1 8 3 1 1 75 1 78 1 4 2 1 76 1 77 1 79 8P296e89b98b418999 0 2 0 1 60 1P2aa0ea489de36020 1 1 8 3 1 1 75 1 78 1 4 2 1 76 1 77 1 79 8P2b9df9ed3197cad4 1 1 8 2 59 1 74 1 3 0 1 73 1 75 8P2c4a989a9ff1916e 2 31 1 1 8 3 1 1 67 1 68 1 6 0 1 51 1 52 1 66 1 69 1 70 8 1 1 8 3 2 1 66 1 69 1 4 0 1 67 1 68 1 70 8P2c6ab5f749a85760 1 1 8 3 0 1 75 1 78 1 4 2 1 76 1 77 1 79 8P2cfbcc996358c8ca 1 1 8 3 0 1 76 1 77 1 6 2 1 58 1 59 1 75 1 78 1 79 8P2eea96ba778f98b2 0 4 1 1 2 1 75 1 76 1P2fb863e735ade35f 0 2 0 1 27 1P2fc133ba2f7c28d3 0 4 0 1 34 1 46 1 60 1P300c96d885ac9b8b 1 1 8 3 1 1 75 1 78 1 4 2 1 76 1 77 1 79 8P311618a0544938d0 0 2 0 1 39 1P328d186f8a2f484d 2 53 1 1 8 3 1 1 74 1 75 1 6 0 1 56 1 57 1 73 1 76 1 77 8 1 1 8 3 2 1 73 1 76 1 4 0 1 74 1 75 1 77 8P32cb4801fa7533f3 0 2 0 1 58 1P350dbcbd0fe98212 1 1 8 3 0 1 76 1 77 1 6 2 1 58 1 59 1 75 1 78 1 79 8P351ce078071342c5 2 53 1 1 8 3 1 1 74 1 75 1 6 0 1 56 1 57 1 73 1 76 1 77 8 1 1 8 3 2 1 73 1 76 1 4 0 1 74 1 75 1 77 8P355d2fe6583f94a9 1 1 8 3 0 1 76 1 77 1 6 2 1 58 1 59 1 75 1 78 1 79 8P3583fd6d23f58d9d 1 1 8 3 1 1 75 1 78 1 4 2 1 76 1 77 1 79 8P35da23f1e6f467a4 0 2 0 1 1 1P366ed9c3c2766987 0 2 0 1 69 1P369daa56fa774809 0 4 0 8 9 8 73 8 74 8P36f367b7e8e8cb59 0 2 0 1 1 1P37846d0be8173aab 0 2 0 1 7 1P38e2279ebf872dd6 1 1 8 3 1 1 76 1 77 1 4 2 1 75 1 78 1 79 8P39c9562a13922c56 1 1 8 3 0 1 76 1 77 1 6 2 1 58 1 59 1 75 1 78 1 79 8P3b0739353361853d 0 2 0 1 1 1P3bb9d6025fd11fc8 0 2 0 1 5 1P3e0faee72de516dd 1 1 8 3 1 1 75 1 78 1 4 2 1 76 1 77 1 79 8P3e240c3d5ec9063e 0 2 0 1 1 1P3edb3fa7d8da7828 1 1 8 3 1 1 76 1 77 1 4 2 1 75 1 78 1 79 8P3f58b6e0a5cdb4e5 0 2 0 1 5 1N000701cce3e60f82N0013036a88a363f7N005f952965cc7a6bN005fba70d6058ddaN0075884d07556a75N007ddd0133ae3601N009808664978e8cdN017c1ca84d4b5467N01b0e2325274c37bN01cefaa2b2ada98dN020756679eebe9c4N021eb1a98d2ce5dcN02ea741a5a189446N035ea0b7cf370da9N039861cc3b938453N03e50ca0364b737bN0452c37d84d4257bN04ad396d299ed176N04d0d36970e559bbN05baacc8d8e6d707N05bfb81cd21cd58cN05c45af123b45c08N05fa0dfc9c5c95e5N064d9691c2b14d76N067f23395f442a56N069980f47a4d1ad6N0723689aff6183ecN072a9d297a241269N075301ae297d020aN0767dfeae694e3bdN0792587343e565e0N07b44b5947621c1fN07c7320ffc491ac3N07d4db5da9ac4d9cN080c7e2ad83a2cd1N082fb5eb787123caN08b8e1c87de6f48eN08eb18091fabdc51N091d11a69950ca0aN092e1a47c8c9c0e0N095837f0732a6196N0960e76a684b2623N098bae027ad525a0N0a174448280e007aN0bbae54bf9bbdcd1N0bc522243fc549f8N0be5b21b474f3477N0c07753e74c97224N0c23c8981190b11fN0cb9167f6c66b79aN0cd5e37890478f60N0d7c8b057466e20fN0d9ca43388b532eeN0df82f41ece4afd2N0e2283ca9c12d0cdN0e2ede04ada5994aN0e35f77aa5a9a7edN0e50ae7af9abeacfN0e5125d31578beefN0e6eafe73d885bb3N0eb9a54cf882fc43N0ecc5dd8578beac6N0ee84d60ad3dc655N0f7e5f745c06a699N0f8e83289efb6dadN0f98de9c198cd636N0fa8cd4708c05475N0fc574d0af9daa91N100061dd95a77aacN108c9f562ed4ba0eN10d1d6cab77367a8N1132ecb0c6aa63beN11a11ef3aa4af15bN11a33932b4f9f564N12041e4d2e207289N126b0076fffb1805N1277f1c25ad375baN12ffbbb0c09713b7N1320454f4191a4e0N132211ae74c0e806N13ad514b9931a260N13d13fdc7c337b20N13ebd3fe8d2ec674N145fa7c9fc7164d6N146b676386c4d514N149902c021a4d979N1499edddfad28bb4N14a1070ac36d1410N14dea737ada9784eN14f48ece6fa4bb88N1508f67e6836573cN1510887cdf325f63N154e1996ae1fd58aN158b6d2ed5ca1d8dN1603ced13560c2f9N162e2288c3c423e3N1686f1178b962865N16a1024135a04169N171a2c5e6b937491N172a32d5fcaf4c21N1738c99eab2ec238N17483af27440ebc7N1850af6b981db68aN18acf924fca9b02dN18c2792da461f3c8N18dcb3db70cac214N18e8115773ae6d85N1909b971a14a3fbaN197dd26866f02ce5N1a096ad79eb520a1N1a16dd2416c8d990N1a3d222595fc44eaN1a55287ab9a2690fN1a5697e17b833850N1a76bdeaaec26389N1a7b88570c7472f5N1add3a84a8c748b1N1b597fce8baa4ae6N1c2efac3d14aee0bN1c4905a8664223f6N1c7090875410c194N1c97c6e358b43864N1cc36861b97d0b52N1ccab4a1546cc12bN1cd2cc3295eb3d63N1cdc6d76b0560724N1cf2b655610daaf1N1d0cc852f54de931N1d768ba286d1400bN1db67f7e4ada2e49N1dd00c8761281ca2N1de2be698da257faN1e14617bd389e5f8N1e6b73cef08d4f21N1fce6a24d49d4c45N1fd462e0ab4e695bN20b2be172ac1f2d3N2142df4bd405b025N214b7a204f0ef7feN2214a27d1611a2d0N2244d9e56687b4c4N227b85a20bdc7ea2N22a87c2aaa1d6fcbN22c54d12a49b08dcN22e2333734252700N2367df087a25189dN23c0dbcea1deb0b0N2466f45cc2b481a4N2498ac7f38d8b974N24b5c7564252668dN25358631fc60fd96N259032e7c8133fb2N2599287b18940487N25d8dcb2ed81f00eN25f3892943033a3eN26fb65e25a1c8997N2776603b3bd16e97N27a7f731cf6a7528N27b9a5fb946f2111N2813c1c8be3ae457N283e86abc77fe2d6N28561a205aadce5eN28724128fa821c77N29512d0f31d83eb4N2959675711e052e1N296a9531937b5bc3N2985a84321aab22bN2a1b65ad5f1ad7c3N2a3bccc2b61c9dacN2aeca3059ec8d9edN2b152341c31783d0N2b2e891eee8bee90N2b4753b75d7f57c8N2bdaeafcb8bd98b1N2c0aede857f5def0N2c2b08ce9d4bb811N2c8889e84e3a3437N2d071c13372eb3d6N2d511502c252b9a1N2dcbd75c52b7ffa3N2e6edfd1ce6840f9N2e8e176ad310ef92N2f5066286a7dad69N2f8fe48c6bd9ebcfN2f9c8af7838c4b64N2fbab7b642b35d6cN303c48c8f0ec538fN30452dce6daf9787N30537e4b5263a875N30abdb78cb15418eN31218dde8ca4c20dN32142263b9e541bcN327357ffa63895a9N32cfd633096cc67aN32f565ab64b75b1eN33578e65a69f0c47N33d75e7560055bf9N343fb3ed4d6a3497N344e9e84f243da4aN3498b39c85cbaa64N356ef64d45ddad25N3625f8421e344f34N365e4b8bf4c64f38N36aead9a6cde6c13N36b2909a2406f809N36dd658e7f4ff8ddN36df921e34682999N3727a83b487f550dN37abc512ef78d1b8N37c9a251803c0b6bN37dee656acad8da4N37e5576d95805d0aN3803b5116dde26fdN3845206f3d32e912N385bf9cb1f9b652eN389d196b4459b550N38a5d15bfe8a1b03N38c90d56488d3960N39025440ea62ed86N397a16e7bbbac63aN397b919aca7a5bc5N39b84e7b654b5064N3a4e34fc2c0ad27dN3a8735d97590a197N3aa906385e5db95dN3adddf8b0013f23cN3b1fedaebf550843N3d08588e40694cebN3d21f19d63abcecbN3d9574fa49bfefe9N3dad26d519046c20N3e0be93b6ea38596N3e0c2e781df37c70N3e53755d809697e0N3e867c81370e8366N3ef19a5d7abf755bN3efaab767e3eb9fcN3f64fe00ec0d9d20N3f656c33bc531595"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_x509_get_name_E () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.ninv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_C.InnerOb"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_C.OuterOb"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.x509_get_name_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"].


Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HFREE : hl_free L = U_FREE.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk)
            (PP CUR P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 64 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : CUR + 64 <= BUF \/ BUF + Z.of_nat (length bs) <= CUR.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis CURB : 0 <= CUR /\ CUR + 64 <= 2^64.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : CUR mod 8 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < CUR.
  Hypothesis NZ3 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - 160 - hl_stack L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : CUR + 64 <= lo \/ bv_unsigned sp <= CUR.
  Hypothesis DS3 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CWPP : client_wrange L LB lo (heap_top usegs L HI h) PP 8.
  Hypothesis CWCUR : client_wrange L LB lo (heap_top usegs L HI h) CUR 64.
  Hypothesis CRBUF : client_range L LB lo BUF (Z.of_nat (length bs)).
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPB : bv_unsigned sp < 2^64.
  Hypothesis HBR0 : Forall (fun b => block_range L (fst b) (snd b)) LB.

  Notation X := [(PP, PP + 8); (CUR, CUR + 64)].
  Notation POST := (x509_get_name_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END lo m mo).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -144)).
  Notation INV := (ninv L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo h LB PP CUR BUF lo bs K1W K2W).
  Notation WW := (W sp PP).
  Let sync_W' := sync_W L HI sp m h LB PP CUR BUF lo bs D1 SLO HLS ACL HTOP DHI DIM1 DIM2 DS2 CWPP CWCUR HBR0.
  Let snoc_facts' := snoc_facts L HI sp h LB PP CUR BUF lo bs SLO HLS ACL DIM1 DIM2 CWPP CWCUR CRBUF SPB.
  Let others_apart' := others_apart L HI sp h LB PP CUR BUF lo bs ACL DIM1 DIM2 CWPP.
  Let cur_wrange' := cur_wrange L HI sp h LB PP CUR BUF lo bs DIM1 DIM2 CWCUR.
  Let headrep_pres' := headrep_pres L HI sp h LB CUR lo DS2 CWCUR.
  Let cur_cases' := cur_cases L sp LB PP CUR BUF lo bs DIM1 DIM2.
  Let close_nodes' := close_nodes sp LB PP CUR BUF lo bs.
  Let close_fin' := close_fin sp LB PP CUR BUF lo bs.
  Let headrep_snoc' := headrep_snoc sp PP CUR BUF lo bs.
  Let in_block_below' := in_block_below L LB HBR0.
  Let presx_munch' := presx_munch L sp LB PP CUR.

  Ltac open_ninv INV :=
    pose proof INV as INVc;
    (flat constr:(INVc) 16%nat; flclear INVc; intros HH HT HND HFR HCF HHD HLS' FRA FRS FRL FRH ST MI HBUF HPX MF);
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK; pose proof (conj HH I) as HHbox;
    pose proof HCF as HCFc; (flat constr:(HCFc) 7%nat; flclear HCFc; intros CAL CPOS C64 CPP CBF CSTK _);
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
        MU : munch _ ?mm mx, WM : wmono _ ?mm mx, HHD : headrep CUR ?mm ?nodes,
        HLS' : name_lseg _ ?mm _ (removelast ?nodes) _, HPX : heap_presx _ _ LB _ _ m ?mm |- _ =>
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
      FRA : rw_cells _ mx (bv_unsigned sp + -144) [C8 _; _; _], FRS : rw_cells _ mx (bv_unsigned sp + -120) [C8 ?slen],
      FRL : rw_cells _ mx (bv_unsigned sp + -112) [C8 ?alen] |- _ =>
        assert (INVn : INV mx mox hc nodes cur slen alen (@nil byte));
        [ unfold ninv; repeat match goal with |- _ /\ _ => split end; try assumption;
          try (etransitivity; eassumption); try (eapply mo_frame_trans; eassumption) | ]
    end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
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
  Ltac mk_blob W0 W1 W2 W3 W4 HCB :=
    let H1 := fresh "J" in let H2 := fresh "J" in let H3 := fresh "J" in
    chunk_join W3 W4 H1; chunk_join W2 H1 H2; chunk_join W1 H2 H3; chunk_join W0 H3 HCB;
    lazymatch type of HCB with rw_cells ?sg ?mx ?A ?cs =>
      let n := eval cbv in (length cs - 3)%nat in
      let mid := spine_firstn n cs in
      let post := spine_skipn n cs in
      change (rw_cells sg mx A cs) with (rw_cells sg mx A ([] ++ mid ++ post)) in HCB;
      apply (rw_cells_merge sg mx A [] mid post) in HCB;
      cbn [cells_size csize Nat.add app] in HCB;
      change (CB 48 ?j :: ?rest) with (name_blob j 0) in HCB || idtac
    end.

  (* [comment removed for export] *)
  Ltac err_addw r :=
    zstep; rewrite (swrap32_errsum r) by (match goal with H : _ < r <= 0 |- _ => clear -H end; lia);
    zstep;
    let KZ := fresh "KZ" in
    if_cases KZ; zify_cond KZ; [| exfalso; match goal with H : _ < r <= 0 |- _ => clear -H KZ end; rewrite ?unsigned_lit in KZ by lia; lia ].
  Let err_walk' := err_walk L HI HFREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs.
  Notation INNEROB := (InnerOb L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs).
  Notation OUTEROB := (OuterOb L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR P END BUF lo bs).


  (* [comment removed for export] *)
  #[local] Ltac lxp_is_protected H ::= lazymatch H with HCALLOC => idtac | HFREE => idtac | B1 => idtac | B3 => idtac | B4 => idtac | D1 => idtac | D2 => idtac | D3 => idtac | PPB => idtac | CURB => idtac | AL1 => idtac | AL2 => idtac | NZ1 => idtac | NZ2 => idtac | NZ3 => idtac | SLO => idtac | HLS => idtac | ACL => idtac | ACP => idtac | HTOP => idtac | SPA => idtac | DHI => idtac | DIM1 => idtac | DIM2 => idtac | DS1 => idtac | DS2 => idtac | DS3 => idtac | CWPP => idtac | CWCUR => idtac | CRBUF => idtac | TP => idtac | SPB => idtac | HBR0 => idtac end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00b0@L13549890220.162L1848725797.169 L1848725797.172 L1848725797.177 L1848725797.180 L1848725797.209 L21143270663.116L2261724442.1   L23466391738.1  L23733440223.157L24422220979.153L25638580534.160L26443884051.170L26443884051.173L26443884051.178L26443884051.181L26443884051.210L27803406694.159L29734002620.160L31393302313.171L31393302313.174L31393302313.179L31393302313.182L31393302313.211L32836657718.153L38005468328.153L43068582243.157L49225248588.121L49225248590.124L49533686324.118L50072307020.121L50072307022.124L51043000313.162L52838428710.114L54933384500.124L54933384502.121L54933384509.116L56696518316.172L56696518316.175L56696518316.180L56696518316.183L56696518316.212L58972689219.157L65315988308.114L66149329551.114L66149329551.122L68314652998.157L68338970955.153L6952084072.1   L702623146.153  00000100V01;01`02E02j03O03T03Y04G05d06P07507Z08?08d09I0:90:i0;N0<30<X0==0=b0=c0?V0@C0@D0@E0B>0Bc0CH0CI0Dk0FU0H?0In0JS0K80K]0LB0Lg0MS0N=0Nk0Nl0O\0Q80Q<0QnFS2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S3CURS3curS2sp2PP1P3BUF2bs2B13cur2j82r02j23LXJ4LXJ04LXJ1S1L2sp2PP1P2lo2bs3PPB3SLO3HLS3ACL3ACP3cur2j82r04olen2j22q23Hq14CPOS2LR3LXJ4LXJ04LXJ14lxv23H18S2sp2PP3BUF2bs2D23cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP3CUR3BUF2bs2D33cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP3BUF2lo2bs3DS33cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1FS1L2sp2PP1P3END2lo2bs3PPB3SLO3HLS3ACL3ACP3cur2j82r04olen2j22e22es2q23Hq13He23Hes4CPOS2LR3LXJ4LXJ04LXJ14lxv23H193H20S2sp2PP3BUF2bs3NZ33cur2j82r02j23LXJ4LXJ04LXJ1FFS1L2HI2sp1h2PP3CUR1P3END3BUF2lo2bs2B12B32D12D22D33PPB3SLO3HLS3ACL3ACP3DS13DS23DS33cur2e22es2q22hc3Hq13Hq23He23Hes2HT4CPOSS2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1FS1L2sp2PP1P3END2lo2bs3PPB3SLO3HLS3ACL3ACP3cur2j82r02j22e22es2q23Hq13Hq23He23Hes4CPOS3LXJ4LXJ04LXJ1S1L2sp2PP1P3END2lo2bs3PPB3SLO3HLS3ACL3ACP3cur2j82r04olen2j22e22es2q23Hq13He23Hes4CPOS2LR3LXJ4LXJ04LXJ13H19S1L2sp2PP1P3END2lo2bs3PPB3SLO3HLS3ACL3ACP3cur2j82r04olen2j22e22es2q23Hq13He23Hes4CPOS2LR3LXJ4LXJ04LXJ13H17S1L2sp2PP1P3END2lo2bs3PPB3SLO3HLS3ACL3ACP3cur2j82r04olen2j22e22es2q23Hq13Hq23HOL3He23Hes4CPOS3LXJ4LXJ04LXJ13H12S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP3BUF2bs2B43cur2j82r02j23LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j21r2Hr3LXJ4LXJ04LXJ1S2sp2PP2bs3cur2j82r02j21r2Hr3LXJ4LXJ04LXJ13H13FS2sp2PP3END3BUF2bs2B33cur2j82r02j23LXJ4LXJ04LXJ1S1L2sp2PP2lo2bs3PPB3SLO3HLS3ACL3ACP3SPA3cur2j82r02j22e24CPOS3LXJ4LXJ04LXJ14lxv24lxv33H153H17S2PPS2sp2PP2bs3cur2j82r02j23LXJ4LXJ04LXJ14lxv13H123H22". (* [comment removed for export] *)
  Lemma l2_walk : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_E ()) "Pnodes,(0.$1.)Pcur,$1.Pslen,(2.&40.)Palen,(2.&40.)Pj8,(0.(2.&8.))Potw,(2.&40.)Pr0,(0.(2.&8.))Polen,(2.&40.)Pj1,(0.(2.&8.))Pvlen,(2.&40.)Pj2,(0.(2.&8.))Pmg,(2.&8.)Pp7,(0.(2.&8.))Pp0,$1.Pe2,$1.Pes,$1.Pq2,$1.Pr,$1.Px5,(2.&40.)Px6,(2.&40.)Px7,(2.&40.)Px11,(2.&40.)Px12,(2.&40.)Px13,(2.&40.)Px14,(2.&40.)Px15,(2.&40.)Px16,(2.&40.)Px17,(2.&40.)Px28,(2.&40.)Px29,(2.&40.)Px30,(2.&40.)Px31,(2.&40.)Pmm,P,(2.&40.)(3.(2.&8.))Pmoc,$4.Phc,(5.$6.VL,VHI,)P,(7.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,Vm,Vmo,Vh,VLB,VPP,VCUR,VBUF,Vlo,Vbs,(8.&40.+????????????=<1:.)(8.&40.+????????????=<20.)R3.R2.R1.R23.R22.R21.R20.R1?.)P,(9.$6.R4.R23.(:.$;.(<.R1?.)(:.$;.(=.#4.R1>.)(>.$;.))))P,(9.$6.R5.(?.R24.+8.)(:.$;.(10.R1>.)(>.$;.)))P,(9.$6.R6.(?.R25.+10.)(:.$;.(=.#10.R1>.)(>.$;.)))P,(9.$6.R7.(?.R26.+20.)(:.$;.(10.R1>.)(>.$;.)))P,(9.$6.R8.(?.R27.+28.)(:.$;.(=.#8.R1>.)(:.$;.(10.(8.&40.=))(:.$;.(11.R1=.)(:.$;.(=.#7.R1<.)(>.$;.))))))P,(9.$6.R9.VPP,(:.$;.(10.(8.&40.R19.))(>.$;.)))P,(12.VP,R1:.)P,(12.R1;.R1=.)P,P,(13.$1.R1;.=)(12.(14.&40.R26.)(15.R1?.R1=.))P,(16.(17.-7?.R1<.)(12.R1<.=))P,(17.R21.R20.)P,(12.R21.R20.)P,(12.R21.VEND,)P,Pp',$1.Pes',$1.P,(17.R26.R2.)(18.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vbs,R3.R2.)P,Pp',$1.P,(17.R26.R1.)(19.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vbs,R2.)(1:.$6.R12.(1;.$6.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,Vlo,Vm,Vmo,)(1<.(1=.(8.&40.+27>64.)(8.&40.(?.(14.&40.Vsp,)-90.))Vgp,Vtp,R21.R20.R1?.(8.&40.R32.)(8.&40.-2880.)(8.&40.R22.)R1>.R1=.R1<.R1;.R1:.R19.R18.(8.&40.VEND,)(8.&40.VPP,)(8.&40.R24.)(8.&40.R25.)(8.&40.+1.)(8.&40.VCUR,)(8.&40.=)(8.&40.+1.)(8.&40.+50581008.)(8.&40.-2380.)R17.R16.R15.R14.)VF,(8.&40.+27>64.)Vfc,(1>.(2.&40.))R13.(1?.$6.)))")
(* [comment removed for export] *).
  Proof.
  (* [comment removed for export] *)
  intros nodes cur slen alen j8 otw r0 olen j1 vlen j2 mg p7 p0 e2 es q2 r x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 mm moc hc
    INV W0 W1 W2 W3 W4 HPP Hq1 Hq2 HOL Hr Hp0 He2 Hes KIN KOUT.
  (* [comment removed for export] *)
  open_ninv INV.
  clear INV.
  pose proof (bv_unsigned_in_range 64 olen) as LR.
  try (unfold bv_modulus in LR).
  try (cbn in LR).
  pose proof (cur_wrange' nodes cur _ HFR HCF ltac:(intros b Hb; exact Hb)) as CWc0.
  pose proof CWc0 as CWc.
  try (rewrite <- HT in CWc).
  pose proof HTOP as HTOPc.
  try (rewrite <- HT in HTOPc).
  pose proof CWPP as CWp.
  try (rewrite <- HT in CWp).
  start_W cur.
  (* [comment removed for export] *)
  pose proof (@sums1_ok) as LXSUMS.
  lxp_run (PLANS [0x1efe0; 0x27e64; 0x27e68; 0x27ef4; 0x27f1c; 0x27f54; 0x27f84; 0x27ff8; 0x3f960] [] 155%N SUMS1).
  { (* [comment removed for export] *)
    (* [comment removed for export] *)
    try (wsync).
    try (mk_blob W0 W1 W2 W3 W4 HCB).
    try (rebuild_ninv INV2).
    lxp_apply err_walk'.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    (* [comment removed for export] *)
    try (rewrite ?unsigned_lit in Kr by plia).
    lxp_r0 r.
    subst r.
    specialize (HOL eq_refl).
    lxp_gc.
    lxp_run (PLANS [0x1efe0; 0x27e64; 0x27e68; 0x27ef4; 0x27f1c; 0x27f54; 0x27f84; 0x27ff8; 0x3f960] [(0x27f9c, DMerge 0)] 155%N SUMS1).
    (* [comment removed for export] *)
    all: first [ lxp_at 163716; first [ try (wsync); try (mk_blob W0 W1 W2 W3 W4 HCB); try (rebuild_ninv INV2); lxp_apply err_walk' | (try (replace (Z_to_bv 64 18446744073709542430) with (Z_to_bv 64 (-9186)) by (apply bv_eq; reflexivity))); try (wsync); try (mk_blob W0 W1 W2 W3 W4 HCB); try (rebuild_ninv INV2); lxp_apply err_walk' | try (pose proof U_asn1_get_len_spec as SP); try (wsync); (try (lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end)); (try (match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rv end)); try (wsync); try (rebuild_ninv INV2); lxp_apply err_walk' ] | lxp_at 163612; try (pose proof U_asn1_get_len_spec as SP); try (wsync); (try (lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end)); (try (match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into rv end)); try (wsync); (try (rewrite ?unsigned_lit in Krv by plia)); try (rebuild_ninv INV2); lxp_apply l3_walk ].
  }
  Unshelve. all: try lxp_default.   (* [comment removed for export] *)
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
