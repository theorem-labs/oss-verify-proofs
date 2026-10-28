(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_x509_get_name_B U_x509_get_name_C U_x509_get_name_D U_x509_get_name_E.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_len U_asn1_free_named_data_list_shallow U_x509_get_name_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00013a1962ed3bdc 0 4 0 1 3 1 56 1 57 1P00988ef88087f283 1 1 8 3 1 1 65 1 68 1 4 2 1 66 1 67 1 69 8P017645d0c4cf95be 0 3 0 1 33 1 47 1P0185798700a602f3 2 35 1 1 8 3 1 1 66 1 67 1 6 0 1 52 1 53 1 65 1 68 1 69 8 1 1 8 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 8P02622f1045a636c5 0 2 0 1 32 1P035b4d9bf69d6584 1 1 8 3 1 1 56 1 59 1 4 2 1 57 1 58 1 60 8P0390fc2ce2ca9dbd 0 2 0 1 1 1P03d531ebbe09c6c5 0 2 0 1 6 1P041a2719842862fb 1 1 8 3 0 1 56 1 59 1 4 2 1 57 1 58 1 60 8P042353e2c0d52fc0 1 1 8 2 43 1 54 1 3 0 1 53 1 55 8P04b3d01ca7ba8906 0 4 0 1 6 1 43 1 57 1P05782b13c4ad328a 0 2 0 1 3 1P05b193c2f091f782 0 2 0 1 42 1P0675f3297031c621 1 1 8 3 1 1 66 1 67 1 4 2 1 65 1 68 1 69 8P069d579a1e595a82 1 1 8 3 1 1 56 1 57 1 6 2 1 42 1 43 1 55 1 58 1 59 8P06e9b232614e073d 0 2 0 1 1 1P070c417b42a0928b 1 1 8 3 1 1 56 1 57 1 6 2 1 42 1 43 1 55 1 58 1 59 8P0740f4e47bdd27a5 1 1 8 3 1 1 55 1 58 1 4 2 1 56 1 57 1 59 8P07762ec9dc13a65e 1 1 8 3 1 1 57 1 58 1 6 2 1 43 1 44 1 56 1 59 1 60 8P083bd6821c347526 0 2 0 1 3 1P085fa922eb726049 0 1 1 1P090507ac58a70e3c 2 35 1 1 8 3 1 1 66 1 67 1 6 0 1 52 1 53 1 65 1 68 1 69 8 1 1 8 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 8P0b02124052e46456 1 1 8 3 1 1 57 1 58 1 6 2 1 43 1 44 1 56 1 59 1 60 8P0c26853a75b50bcc 1 1 8 3 0 1 56 1 57 1 6 2 1 42 1 43 1 55 1 58 1 59 8P0c5603e30f5190f1 1 1 8 2 53 1 64 1 3 0 1 63 1 65 8P0d25370228428e2e 0 4 0 1 2 1 58 1 59 1P0e5d70160b332dcc 1 1 8 3 1 1 65 1 68 1 4 2 1 66 1 67 1 69 8P0eacf7dcea7d4641 1 1 8 3 1 1 65 1 68 1 4 2 1 66 1 67 1 69 8P0ecb81c2485c3e06 0 4 0 1 2 1 56 1 57 1P0fe423192d05d945 1 1 8 3 1 1 66 1 67 1 4 2 1 65 1 68 1 69 8P100ed84b2307d7a4 0 4 0 1 2 1 55 1 56 1P11a97cda9b90251b 1 1 8 3 1 1 56 1 59 1 4 2 1 57 1 58 1 60 8P12e2e99f198fe5ad 0 2 0 1 1 1P135ef070445e3779 1 1 8 3 1 1 56 1 57 1 6 2 1 42 1 43 1 55 1 58 1 59 8P14bd0661f2c3f98a 0 2 0 1 5 1P153827115534f64d 1 1 8 3 0 1 55 1 58 1 4 2 1 56 1 57 1 59 8P159fd7106d7b15a4 0 5 0 1 1 1 5 1 41 1 56 1P15f6071f572ef662 0 2 0 1 6 1P16cf956fbff9e0e0 0 9 0 1 4 1 5 1 40 1 42 1 52 1 54 1 55 1 56 1P16ddb9f33bcf8fdd 1 1 8 3 1 1 55 1 58 1 4 2 1 56 1 57 1 59 8P1703c6edeab61866 1 1 8 3 0 1 65 1 68 1 4 2 1 66 1 67 1 69 8P175740a9d385a314 0 4 1 1 2 1 65 1 66 1P17f5908726cc0c3d 1 1 8 3 1 1 65 1 68 1 4 2 1 66 1 67 1 69 8P18cb5871c97f072f 0 4 0 1 2 1 67 1 68 1P195d7c21d3c1b96e 1 1 8 3 0 1 57 1 58 1 6 2 1 43 1 44 1 56 1 59 1 60 8P1999f46ad181fab6 1 1 8 3 1 1 57 1 58 1 6 2 1 43 1 44 1 56 1 59 1 60 8P1afe682b2d311dde 0 2 0 1 45 1P1bb53eacccddaf40 1 1 8 3 0 1 66 1 67 1 6 2 1 52 1 53 1 65 1 68 1 69 8P1ca48d85fc72f345 1 1 8 3 1 1 55 1 58 1 4 2 1 56 1 57 1 59 8P1decbe56dd607871 1 1 8 3 0 1 66 1 67 1 6 2 1 52 1 53 1 65 1 68 1 69 8P1e9beff398b572a6 0 2 0 1 5 1P1f548b2db6066fd4 0 2 0 1 5 1P2103f88577f2421f 1 1 8 3 1 1 57 1 58 1 6 2 1 43 1 44 1 56 1 59 1 60 8P2144e07add69a027 0 2 0 1 45 1P21fd90946d6bb424 1 1 8 3 0 1 57 1 58 1 6 2 1 43 1 44 1 56 1 59 1 60 8P22494abe8e603162 0 4 0 16 10 16 54 16 55 16P226c97f2e47b8797 1 1 8 3 0 1 66 1 67 1 6 2 1 52 1 53 1 65 1 68 1 69 8P2330624075860152 1 1 8 3 0 1 55 1 58 1 4 2 1 56 1 57 1 59 8P24869f096021172a 0 6 1 1 3 1 44 1 45 1 57 1 58 1P24c49e42e6e5acad 0 2 0 1 54 1P24df269e51f966e8 0 2 0 1 1 1P25145ceda31521a9 0 4 0 1 2 1 57 1 58 1P257e2e92a02507cf 1 1 8 3 1 1 57 1 58 1 4 2 1 56 1 59 1 60 8P25972b011256eaa6 0 3 0 1 32 1 46 1P25a35e4361134e4d 1 1 8 3 0 1 66 1 67 1 6 2 1 52 1 53 1 65 1 68 1 69 8P269f99f9bb92ea78 1 1 8 3 0 1 56 1 59 1 4 2 1 57 1 58 1 60 8P26c2cd1189619e88 0 2 0 1 31 1P27804e307852e46d 1 1 8 3 0 1 55 1 58 1 4 2 1 56 1 57 1 59 8P281054e5300d470a 0 1 1 1P281a6bc88be63bfe 0 2 0 1 5 1P2a3c75adfe62a8b2 0 2 0 1 43 1P2a8ef880e0908a58 1 1 8 3 1 1 56 1 57 1 6 2 1 42 1 43 1 55 1 58 1 59 8P2c43501fe6c2ab4d 0 4 0 1 3 1 57 1 58 1P2c8db3749dc92012 0 4 0 1 6 1 40 1 55 1P2ca59c2d824b3666 2 35 1 1 8 3 1 1 66 1 67 1 6 0 1 52 1 53 1 65 1 68 1 69 8 1 1 8 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 8P2df36e088f552068 0 4 0 1 7 1 42 1 56 1P2e06ff0403d41823 0 2 0 1 1 1P2e106ebf71884501 0 6 1 1 2 1 43 1 44 1 56 1 57 1P2e4f72cc83909f60 1 1 8 3 0 1 66 1 67 1 6 2 1 52 1 53 1 65 1 68 1 69 8P2e847e9fa938cfa5 1 1 8 3 0 1 66 1 67 1 6 2 1 52 1 53 1 65 1 68 1 69 8P2fa527802d98f1d2 1 1 8 3 1 1 65 1 68 1 4 2 1 66 1 67 1 69 8P30385002c12e9bea 0 2 0 1 5 1P304eae3adbaa747d 0 4 0 8 11 8 63 8 64 8P3051a4583bcc5cbd 1 1 8 3 1 1 65 1 68 1 4 2 1 66 1 67 1 69 8P30aee8b23b28ed12 0 3 0 1 31 1 46 1P313fc9c87bbfeee8 1 1 8 3 1 1 56 1 57 1 4 2 1 55 1 58 1 59 8P320a827d2a541907 1 1 8 3 0 1 56 1 57 1 6 2 1 42 1 43 1 55 1 58 1 59 8P3224aaf147a60634 1 1 8 3 0 1 56 1 59 1 4 2 1 57 1 58 1 60 8P323274b68e50bff2 2 35 1 1 8 3 1 1 66 1 67 1 6 0 1 52 1 53 1 65 1 68 1 69 8 1 1 8 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 8P324592b91a0fd0dd 1 1 8 3 0 1 66 1 67 1 6 2 1 52 1 53 1 65 1 68 1 69 8P32cb6e457766b59e 0 2 0 1 1 1P33295d8f300baea5 0 4 0 1 2 1 67 1 68 1P3332e93208ad41c8 1 1 8 3 1 1 56 1 59 1 4 2 1 57 1 58 1 60 8P338439332914396b 1 1 16 2 0 1 53 1 3 10 1 54 1 55 16P343d31a3ec6cf288 0 2 0 1 44 1P34eb20106c7bf18f 1 1 8 3 1 1 56 1 59 1 4 2 1 57 1 58 1 60 8P363b733a9fad9575 1 1 8 3 0 1 55 1 58 1 4 2 1 56 1 57 1 59 8P363e6f573267a5ed 1 1 8 3 0 1 56 1 57 1 6 2 1 42 1 43 1 55 1 58 1 59 8P37691f69d9a8c27a 0 2 0 1 1 1P37aa85c1d8c9d276 1 1 8 3 1 1 66 1 67 1 4 2 1 65 1 68 1 69 8P37ab63e369af0b57 1 1 8 3 1 1 65 1 68 1 4 2 1 66 1 67 1 69 8P37ccd259525f82c8 1 1 8 3 0 1 57 1 58 1 6 2 1 43 1 44 1 56 1 59 1 60 8P382b8083247bbbf7 0 2 0 1 52 1P382c750711185c3d 0 4 0 1 2 1 65 1 66 1P384d88ea0c1676cf 0 2 0 1 7 1P38b1608226c70d37 1 1 8 3 0 1 56 1 57 1 6 2 1 42 1 43 1 55 1 58 1 59 8P3975fa4e61fa3ea5 0 2 0 1 7 1P3982318d63f406b2 1 1 8 3 0 1 56 1 59 1 4 2 1 57 1 58 1 60 8P39b532fe93f5b0da 0 6 1 1 3 1 43 1 44 1 56 1 57 1P3a157a755711ec98 0 2 0 1 7 1P3a7142c67ff5eaf0 1 1 8 3 1 1 65 1 68 1 4 2 1 66 1 67 1 69 8P3a8420554623e44e 1 1 8 3 1 1 55 1 58 1 4 2 1 56 1 57 1 59 8P3baf8c212ce14573 1 1 8 3 0 1 66 1 67 1 6 2 1 52 1 53 1 65 1 68 1 69 8P3bd43009b17b87a3 1 1 8 2 44 1 55 1 3 0 1 54 1 56 8P3e20befeba68bcbc 0 6 1 1 2 1 42 1 43 1 55 1 56 1P3f924dbeb2de0acd 1 1 8 3 0 1 57 1 58 1 6 2 1 43 1 44 1 56 1 59 1 60 8P3fd5b29d114690f8 0 2 0 1 5 1N0067204c422c4c54N0079a3e6a5f2f846N017dea1e2918ecf7N020f716e63c5f4bcN0234ac1d9c9f3377N026e37b863644062N02d5d78f451ff707N03215979fc2b3a46N0340aa33c2d3c966N03a81e44a3b762d6N03ba557b795184e3N0425ba9db9e2e31cN046a347310b6ab2dN051f4b693f0fe691N053374275aa4e280N05704b7ae2947e28N065a2301a3e0a3e7N065b252585c90da3N0692b243ba64a15bN074a5151f06b6fe5N07c656682eef0dd5N07f82eb6eb259d4eN083c054423666171N08c2352991e79669N08f54392204b52e2N0940a11ac221f3d4N098101617efcd65cN0a07006882f2658fN0a1cf6cc36aec1b5N0a357091c27d61f2N0a513028586a4d43N0ac11961d8c6bf63N0af11648249edaf7N0b2a3dcf8a6b5d68N0b490e42209d2c13N0bd260b85c178822N0cf33764643fbca6N0d13bb73b2b9d812N0d3c52a2f28d12c1N0d4b1fe44f4801f8N0da55baffff2f10aN0dae3b7071e0af1eN0e12eb3e4a790be7N0f0970702572e1a6N0f7db33825e2a1caN0fb458020b49a796N104040416f00600fN1051bc6a585370e4N10a4a158f68d0098N10b448328dbdc478N117afc7cd0635bd0N11cdc9ecbb864395N12090b02e41c87e8N120a0c4f92e6c260N122783295f9e3db0N1291d9b93d942ccaN12c059fa20e5df70N12cf4634a63b1188N13810f5b840ff0efN13d96fb4aa243ed2N1478f584781eea14N14b8c5008b4bf373N14ccb17d031e89d8N1503ab30766769d8N1523768294b8e0daN1528bbcf7af748c2N153d7d879f9510e5N154a70588201c910N15c1f56a84e00a3fN16204e453dcbc1acN16303c446f150ae3N17450f2168986678N177d878192bb120cN17abb6ba8f064abfN17b17de22669397fN183611b7d713e07cN18bd954aa8040369N18c1e1f82a32e7cfN194a23adf214c077N1a37e5bd3c9ee8d2N1a8ea2ded42b3a32N1adb3d4679ba0118N1b31804003c626aeN1b6abd47060c5001N1b7d192c2f0261e2N1b9c83a3e09d0e8fN1ba5df152c5eba0bN1c8ae88c15ca1766N1cef28431219a80fN1cf14a876db997d8N1cf6a07cf9fe4419N1dfc0296fa3b4c87N1e046627a204616cN1e404760b30c726fN1e87fdba5d72c779N1f34c5081a2d0fb0N1f7de8f070f67c62N1fc0523d535660faN20518948a2e5a1baN20d52824d48917abN219d8dec96e8cd68N21c65ac107ce8a34N221917fd049b569aN22239c8fd3891f67N22391207ece25affN22884e0846b9dc5cN22c29ab89746da3fN2372e1a1e75ab5d3N23e322d33df83942N2409e624eb0d0b23N241e90c230286347N244842a087f7cba8N2475d445a8a5d95cN24848b18260fc78bN24892fd0bd726352N24ae8306ac7ad040N250adc2062fb0cceN25a647fe2cc277bdN2606255d72564d81N2646cd19380f378aN26870dfd66a507f4N26cdccfd45587b30N27562c474da041ccN27947b7bbcc2c7fbN2797bfa27be37fabN29236c196ea71e5eN29461aec86f066bbN2a02b1a843ab0493N2aa25d4024667393N2adcb66bfe2be425N2ae587aa7868ed0bN2b0860214529c330N2c09732f0437e66eN2c7c252ac4d3a055N2cc87539f5ebc5b3N2d2330b3ad07befbN2d3f8113582856dcN2d582024f79e8598N2d69a65493ba0c1cN2d9973516db87099N2da39cc85ecc852bN2da8005850da3b5dN2db66380782315efN2dcdbfd4499ae598N2deb20b4cc428c6aN2dfc730bb71f4125N2ea6846b87908d8aN2f06866e4f2d7d6dN2f3a75aacdc8f576N2fc500581015edc7N2fc900828b924b3bN2fc98e088feca228N2fff62d97f66a621N300ed286bd880387N30233a6acd17656eN30fa02a3aeff1858N317cabbbcda079fbN319c5e630c98f4e4N31d571858572fd4aN3202a79c2c779553N32a51c7c7180f680N32c02d00c6b7ef97N32ff80dbbb883121N331c0b5ee52a487cN331e8a270eae0448N337b183f5af55121N337bc1743d2b6af7N3396ebe9e4ef5543N339aa153fc308519N33b0fc7199126dd6N3407ab6936220610N342696f993c0ecf9N343ea2ab8174c038N346e84c4370fdfc2N347f9393ec46b8beN3596bc8e13526c71N35c3159db75e8e72N35e332b7d809c07fN36a41ab533fa8004N371397723693db29N37171ad46e9bc2baN37362e89df012565N376ae90b0a319eaeN378e65a274beb9ddN3799d0994677abb6N3810467585ed14e8N3839204d12b2bba7N38443cdcb43a7e0aN38c554798cfb93ccN3904a26d95e5814aN399e8551ae0bae0aN39b866523fe5e44dN3a15956d10715823N3a987cdbe409a2f0N3aac6abd76b98745N3af3ebc4cae7c619N3bb90316da14dedfN3c34d46ec32d077fN3c68b2c440eaff67N3cc18df2b351313aN3d844782cb3beb41N3e21c1f5eff87bf1N3e396a0736c46c98N3ea8d850ce7f13cfN3eefcb72d5aa181cN3ef960e223ddae91N3f494e2fc8e27c1eN3f5877a690cbc416N3f94866cb694ee09"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_x509_get_name_F () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_C.InnerOb"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_C.OuterOb"].


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
  Ltac flia := first [clear_disj; lia | lia].
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12779162959.87L18926747689.87L18926759668.8700001>01L01^S1L2sp2PP3CUR3BUF2lo2bs2D12D22D33PPB4CURB3SLO3HLS3ACL3ACP3DS13DS23DS31a1b1k2HkS2sp2PP3CUR2bsS2sp2PP3CUR2bs1a1b". (* [comment removed for export] *)
  Lemma zbv_mod64 : forall a b, (a - b) mod 18446744073709551616 = 0 -> (Z_to_bv 64 a : word) = Z_to_bv 64 b.
  Proof.
    intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    apply Z.mod_divide in H; [| lia]. flat constr:(H) 2%nat. flclear H. intros k Hk. replace a with (b + k * 18446744073709551616) by lia. apply Z.mod_add. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
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
    cutsz mx (bv_unsigned sp + -144) 24%nat; cutsz mx (bv_unsigned sp + -120) 8%nat; cutsz mx (bv_unsigned sp + -112) 8%nat.


  Local Ltac2 Set LiaOrc.tbl := fun () => "00N0@L10956075483.206L10956075483.215L1438479738.205 L1764931924.205 L1764931924.214 L1848725797.183 L1848725797.185 L19031108897.174L19031108897.178L20370545675.205L21153761159.178L21735923562.217L21735923562.226L23069862995.205L26443884051.184L26443884051.186L31393302313.185L31393302313.187L34491972695.206L38346282486.190L38346282486.194L38346282486.199L38346282486.201L4110235859.174 L44231514192.205L54133370802.205L56696944558.186L56696944558.188L57626602889.5  L8804326598.5   00000102a03b03c03d04204@05M06g07F07T07U0:70:S0:a0:o0;=0;K0;g0;h0;i0>70@I0@c0Ak0BM0B[0Bi0C;0CMFS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32D12D22D33PPB3SLO3HLS3ACL3ACP3SPA3DS13DS23DS32p02es3cur3Hp13Hp34CPOS3CPP3CBF4CSTK4lxv04lxv15lxv175lxv185lxv193H123H133H143H203H233H243H253H27S1L2sp2PP2lo2bs3PPB3SLO3HLS3ACL3ACP2p03cur4CPOS4lxv04lxv13H203H24FFS2sp2PP2bs3curS2sp2PP2bs3curS1L2sp2PP1P3END2lo2bs3PPB3SLO3HLS3ACL3ACP2p02es3cur3Hp13Hp34CPOS4lxv03H153H16S1L2sp2PP1P3END2lo2bs3PPB3SLO3HLS3ACL3ACP2p02es3cur3Hp13Hp34CPOS4lxv04lxv13H133H143H153H16S2sp2PP2bs2es3cur4lxv04lxv13H23S2sp2PP2bs3curFS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32D12D22D33PPB3SLO3HLS3ACL3ACP3SPA3DS13DS23DS32p02es3cur3Hp13Hp33CAL4CPOS3CPP3CBF4CSTK4lxv04lxv15lxv185lxv193H113H143H233H243H25S2sp2PP2bs3cur5lxv173H163H17S2sp2PP2bs3curS2sp2PP2bs3curS2sp2PP2bs3curS2sp2PP2bs3curS2sp2PP2bs3cur5lxv193H103H11FFS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32D12D22D33PPB3SLO3HLS3ACL3ACP3SPA3DS13DS23DS32p02es3cur3Hp13Hp23Hp33CAL4CPOS3CPP3CBF4CSTK4lxv04lxv13H123H15S1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32D12D22D33PPB3SLO3HLS3ACL3ACP3SPA3DS13DS23DS32p02es3cur3Hp13Hp33CAL4CPOS3CPP3CBF4CSTK4lxv04lxv13H133H143H153H16S2sp2PP2bs3cur3lxv3H103H18S1L2sp2PP1P2lo2bs3PPB3SLO3HLS3ACL3ACP2p03cur3Hp14CPOS4lxv05lxv183H153H24S2sp2PP2bs3cur4lxv04lxv15lxv183H14S2sp2PP2bs3curS2sp2PP2bs3curS2sp2PP3cur2xw3HxwS2sp2PP3cur2xw3Hxw". (* [comment removed for export] *)
  Lemma inner_walk : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_F ()) "Pp0,$0.Pes,$0.P,Pp',$0.Pes',$0.P,(1.R4.R2.)(2.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vbs,R3.R2.)P,Pp',$0.P,(1.R4.R1.)(3.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vbs,R2.)(2.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vbs,R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros p0 es KIN KOUT. unfold InnerOb.
    intros x24 nodes cur slen alen j8 j0 olen j1 vlen j2 mg p7 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 mm moc hc
      INV W0 W1 W2 W3 W4 HPP Hp1 Hp2 Hp3.
    open_ninv INV. clear INV.
    pose proof (cur_wrange' nodes cur _ HFR HCF ltac:(intros b Hb; exact Hb)) as CWc0.
    pose proof CWc0 as CWc. rewrite <- HT in CWc. pose proof HTOP as HTOPc. rewrite <- HT in HTOPc.
    pose proof CWPP as CWp. rewrite <- HT in CWp.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB. clear HHbox.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) [SUM_gettagP])
      by (intros AL; repeat constructor; apply apply_summary_sound; apply sum_gettagP_valid).
    rewrite TP. apply (lxp_aevtM_of_evt usegs moc _ _ MK).
    lx_run_tac (PLANS [0x27f84; 0x27e64] [] 80%N [SUM_gettagP]); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hm1 : munch ?W1 ?mA mx, Hw1 : wmono _ ?mA' mx, HCFx : curF _ _ _ _ _ _ ?nodesx ?curx |- _ =>
           let MUW := fresh "MUW" in
           assert (MUW : munch (W sp PP curx) mA mx) by (eapply munch_weaken; [| exact Hm1]; intros xw Hxw; clear - Hxw; cbn [outside W] in Hxw |- *; lia);
           (* [comment removed for export] *)
           first [ lazymatch goal with X4 : rw_cells _ mx (curx + 40) _ |- _ => idtac end
                 | apply (rw_cells_transport usegs W1 mA mx) in W4; [| exact Hm1| exact Hw1| cbn [cells_size csize Nat.add disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]; flia] ];
           first [ lazymatch goal with X2 : rw_cells _ mx (curx + 16) _ |- _ => idtac end
                 | apply (rw_cells_transport usegs W1 mA mx) in W2; [| exact Hm1| exact Hw1| cbn [cells_size csize Nat.add disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]; flia] ];
           let A := fresh "HH" in let B := fresh "HHD" in let C := fresh "HLS'" in let D := fresh "HPX" in
           destruct (sync_W' _ _ _ _ _ _ _ _ _ HH HT ltac:(intros bb Hbb; exact Hbb) HND HFR HCF HHD HLS' HPX MUW Hw1) as (A & B & C & D);
           clear HH HHD HLS' HPX MUW Hm1 Hw1 MK; rename A into HH; rename B into HHD; rename C into HLS'; rename D into HPX;
           pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK;
           try clear ST MI HBUF HPP FRA FRS FRL FRH; try clear W0; try clear W1; try clear W3;
           cut_locals mx
         end end.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
         lazymatch goal with HCFx : curF _ _ _ _ _ _ ?nodesx ?curx |- _ =>
         lazymatch goal with X0 : rw_cells _ mx curx _, X1 : rw_cells _ mx (curx + 8) _, X2 : rw_cells _ mx (curx + 16) _, X3 : rw_cells _ mx (curx + 32) _,
                             X4 : rw_cells _ mx (curx + 40) _, XP : rw_cells _ mx PP _ |- _ =>
           lazymatch pc with
           | 163716 => (* [comment removed for export] *)
               let HCB := fresh "HCB" in mk_blob X0 X1 X2 X3 X4 HCB; rebuild_ninv INV2;
              try (replace (Z_to_bv 64 18446744073709542432) with (Z_to_bv 64 (-9184)) by (apply bv_eq; reflexivity));
              eapply err_walk'; try exact INV2; try exact HCB; try eassumption; flia
           | _ => (* [comment removed for export] *)
               rebuild_ninv INV2;
               eapply l2_walk with (p0 := p0); try exact INV2; try eassumption; first [flia | intros; rewrite ?unsigned_lit by flia; flia]
           end end end end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0@L13543577765.180L13543577765.187L1848725797.183 L19031108897.174L26443884051.184L31393302313.185L31565460392.180L34680000318.182L34680000318.183L37649587022.180L38346282486.189L38346282486.191L38346282486.198L4110235859.174 L51045084656.180L51045084656.187L56696944558.186L57626602889.5  L68116485242.18000000100200@01F01T01b02`03_04^05>05?05@07S07m07n07o08=08O08kFFS2sp2PP2bs3curS1L2sp2PP1P3END2lo2bs3PPB3SLO3HLS3ACL3ACP2p03cur3Hp14CPOS4lxv03H153H16S2sp2PP2bs3curS2sp2PP2bs3curS1L2sp2PP1P2lo2bs3PPB3SLO3HLS3ACL3ACP2p03cur3Hp14CPOS4lxv03H14S1L2sp2PP2lo2bs3PPB3SLO3HLS3ACL3ACP2p03cur4CPOS4lxv03H142p'3Hp'S1L2sp2PP2lo2bs3PPB3SLO3HLS3ACL3ACP2p03cur4CPOS4lxv03H142p'3Hp'S2sp2PP3END2bs3cur4lxv04lxv13H13FFS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32D12D22D33PPB3SLO3HLS3ACL3ACP3SPA3DS13DS23DS32p03cur3Hp13Hp23CAL4CPOS3CPP3CBF4CSTK4lxv04lxv13H123H153H163H133H14S2sp2PP2bs3cur3lxv3H103H18FFS2sp2PP2bs3curS2sp2PP3cur2xw3HxwS2sp2PP2bs3cur4lxv04lxv13H12". (* [comment removed for export] *)
  Lemma outer_walk : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_name_F ()) "Pp0,$0.P,Pp',$0.Pes',$0.P,(1.R3.R2.)(2.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vbs,R3.R2.)P,Pp',$0.P,(1.R3.R1.)(3.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vbs,R2.)(3.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vm,Vmo,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vbs,R3.)")
(* [comment removed for export] *).
  Proof.
    intros p0 KIN KOUT. unfold OuterOb.
    intros x24 nodes cur slen alen j8 j0 olen j1 vlen j2 mg p7 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x28 x29 x30 x31 mm moc hc
      INV W0 W1 W2 W3 W4 HPP Hp1 Hp2.
    open_ninv INV. clear INV.
    pose proof (cur_wrange' nodes cur _ HFR HCF ltac:(intros b Hb; exact Hb)) as CWc0.
    pose proof CWc0 as CWc. rewrite <- HT in CWc. pose proof HTOP as HTOPc. rewrite <- HT in HTOPc.
    pose proof CWPP as CWp. rewrite <- HT in CWp.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB. clear HHbox.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) [SUM_gettagP])
      by (intros AL; repeat constructor; apply apply_summary_sound; apply sum_gettagP_valid).
    rewrite TP. apply (lxp_aevtM_of_evt usegs moc _ _ MK).
    lx_run_tac (PLANS [0x27f84; 0x27dfc] [] 60%N [SUM_gettagP]); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hm1 : munch ?W1 ?mA mx, Hw1 : wmono _ ?mA' mx, HCFx : curF _ _ _ _ _ _ ?nodesx ?curx |- _ =>
           let MUW := fresh "MUW" in
           assert (MUW : munch (W sp PP curx) mA mx) by (eapply munch_weaken; [| exact Hm1]; intros xw Hxw; clear - Hxw; cbn [outside W] in Hxw |- *; lia);
           first [ lazymatch goal with X4 : rw_cells _ mx (curx + 40) _ |- _ => idtac end
                 | apply (rw_cells_transport usegs W1 mA mx) in W4; [| exact Hm1| exact Hw1| cbn [cells_size csize Nat.add disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]; flia] ];
           first [ lazymatch goal with X2 : rw_cells _ mx (curx + 16) _ |- _ => idtac end
                 | apply (rw_cells_transport usegs W1 mA mx) in W2; [| exact Hm1| exact Hw1| cbn [cells_size csize Nat.add disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]; flia] ];
           first [ lazymatch goal with X0 : rw_cells _ mx curx _ |- _ => idtac end
                 | apply (rw_cells_transport usegs W1 mA mx) in W0; [| exact Hm1| exact Hw1| cbn [cells_size csize Nat.add disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ]; flia] ];
           let A := fresh "HH" in let B := fresh "HHD" in let C := fresh "HLS'" in let D := fresh "HPX" in
           destruct (sync_W' _ _ _ _ _ _ _ _ _ HH HT ltac:(intros bb Hbb; exact Hbb) HND HFR HCF HHD HLS' HPX MUW Hw1) as (A & B & C & D);
           clear HH HHD HLS' HPX MUW Hm1 Hw1 MK; rename A into HH; rename B into HHD; rename C into HLS'; rename D into HPX;
           pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK;
           try clear ST MI HBUF HPP FRA FRS FRL FRH; try clear W1; try clear W3;
           cut_locals mx
         end end.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
         lazymatch goal with HCFx : curF _ _ _ _ _ _ ?nodesx ?curx |- _ =>
         lazymatch goal with X0 : rw_cells _ mx curx _, X1 : rw_cells _ mx (curx + 8) _, X2 : rw_cells _ mx (curx + 16) _, X3 : rw_cells _ mx (curx + 32) _,
                             X4 : rw_cells _ mx (curx + 40) _, XP : rw_cells _ mx PP _ |- _ =>
           lazymatch pc with
           | 163716 => let HCB := fresh "HCB" in mk_blob X0 X1 X2 X3 X4 HCB; rebuild_ninv INV2;
                       eapply err_walk'; try exact INV2; try exact HCB; try eassumption; flia
           | _ => rebuild_ninv INV2;
                 lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (?q1 + ?sl)) _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
                    eapply (inner_walk q1 (q1 + sl)); try exact INV2; try eassumption;
                    first [flia | intros p' es' Hp'; apply KIN; flia | intros p' Hp'; apply KOUT; flia] end
           end end end end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030@L26728691728.90 L59308579930.127L59308580059.12800001G01a03CS1L2sp2PP3CUR3END3BUF2lo2bs2D12D22D33PPB4CURB3SLO3HLS3ACL3ACP3DS13DS23DS31k1p2Hk2p'3Hp'S2sp2PP3CUR3END2bs1p2Hk2H7S1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32D12D22D33PPB4CURB3SLO3HLS3ACL3ACP3DS13DS23DS31p2Hk2es2H62H72H8". (* [comment removed for export] *)
  Lemma loops : forall (k : nat) (p : Z), END - p < Z.of_nat k -> (forall es, INNEROB p es) /\ OUTEROB p.
  Proof.
    induction k as [|k IH]; intros p Hk.
    - split; [intros es|]; [unfold InnerOb| unfold OuterOb]; intros; exfalso; lia.
    - assert (KIN : forall p' es', p < p' -> INNEROB p' es') by (intros p' es' Hp'; apply (proj1 (IH p' ltac:(lia)))).
      assert (KOUT : forall p', p < p' -> OUTEROB p') by (intros p' Hp'; apply (proj2 (IH p' ltac:(lia)))).
      split; [intros es; apply inner_walk; assumption| apply outer_walk; assumption].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L10818113471.8400001;S1L2sp2PP3CUR3END3BUF2lo2bs2D12D22D33PPB4CURB3SLO3HLS3ACL3ACP3DS13DS23DS31p". (* [comment removed for export] *)
  Lemma outer_start : forall p, OUTEROB p.
  Proof. intros p. destruct (loops (Z.to_nat (END - p + 1)) p) as [_ H]; [lia| exact H]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

