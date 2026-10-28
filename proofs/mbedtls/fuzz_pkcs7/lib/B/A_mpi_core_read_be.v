(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_read_be.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_rt_facts AImgRT A_mpi_core_mla A_mpi_core_mul.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxAMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P000d689685239181 1 1 4 1 0 1 5 29 1 43 1 46 1 56 1 76 1P008b1fd549813651 0 5 0 1 54 1 59 1 70 1 71 1P00d6020fa2455a34 0 6 0 1 52 1 53 1 57 1 66 1 67 1P0109461465f43774 0 4 0 1 51 1 66 1 67 1P015c334761a0227a 1 2 4 2 0 1 73 1 4 2 24 1 74 1 3 28 1 75 1 76 1P01af24e5c1e73923 0 5 0 1 52 1 57 1 66 1 67 1P01b2f0fda1d7bad7 0 2 0 1 31 1P01d5e4d422326a4b 0 5 0 1 54 1 60 1 79 1 80 1P02728ace7b1d0e69 0 2 0 1 33 1P035ea3e71063bc9e 1 1 4 1 0 1 5 21 1 26 1 44 1 45 2 74 2P042040008cf668da 1 2 4 2 0 1 78 1 4 2 27 1 79 1 3 31 1 80 1 81 1P0460d43558a35f19 1 2 4 2 0 1 60 1 4 2 21 1 61 1 3 19 1 62 1 63 1P0462f47b80a2b6ca 0 2 0 1 24 1P04a96361b35651e4 0 2 0 1 23 1P04c9500a5210ec27 0 2 0 1 2 1P0556d26ff728cf5c 1 1 4 1 0 1 5 25 1 30 1 48 1 49 2 78 2P06659d60bc17faea 1 1 4 1 0 1 3 30 1 47 1 75 1P0692fc49c9f64fd5 2 54 1 1 4 3 3 1 70 1 71 1 6 0 4 55 4 60 4 69 4 72 4 73 16 1 1 4 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 4P07bf928e9d993f72 0 6 0 1 52 1 53 1 57 1 66 1 67 1P08643757f70ff716 0 2 0 1 33 1P097188a139e6a284 1 1 4 2 20 1 60 1 5 0 1 19 4 46 4 61 1 62 4P097d159f10f3ce6b 0 2 0 1 1 1P0a0cb10b7d6db49f 2 54 1 1 4 5 3 1 47 1 59 4 70 1 71 1 6 0 1 55 1 60 1 69 1 72 1 73 4 1 1 4 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 4P0a0f5d895c95bbb5 0 2 0 1 2 1P0abf23752fef62d4 2 55 1 1 4 3 1 1 81 1 82 1 9 0 1 33 4 50 4 55 1 60 4 61 1 80 1 83 1 84 4 1 1 4 3 2 1 80 1 83 1 8 0 8 32 32 33 32 50 16 51 16 81 8 82 8 84 32P0acdc67ede44d44b 1 1 4 1 0 1 4 30 2 31 2 48 2 78 2P0bc282d9e02ca69d 1 1 4 1 0 1 2 25 1 70 1P0bd01ac548610b66 1 1 4 1 0 1 4 30 2 31 2 48 2 78 2P0c4b2bc0cf56fcfc 0 5 0 1 53 1 58 1 69 1 70 1P0c4ccd2a3ccd29c4 0 2 0 1 1 1P0cdeff102e27318d 0 2 0 1 3 1P0d0b90236f5c9270 0 5 0 1 53 1 58 1 69 1 70 1P0dcb467a44f0500a 0 5 0 1 52 1 57 1 66 1 67 1P0ea630aedc43998e 0 5 0 1 54 1 60 1 79 1 80 1P0f2ded26f1c50387 1 1 4 2 20 1 70 1 7 0 2 24 8 25 8 42 8 52 8 71 2 72 8P0f2f1298882cfdd9 0 4 0 1 51 1 66 1 67 1P0f647f0c292268a8 0 2 0 1 1 1P0fd7373914ad1404 1 1 4 1 0 1 3 31 1 48 1 78 1P101eb2da80f8deff 0 5 0 1 52 1 57 1 66 1 67 1P107d7b7cd2fc557d 1 1 4 1 0 1 2 28 1 73 1P108581d8989110f8 0 4 0 1 51 1 66 1 67 1P11aa2a3ee8be233e 1 1 4 2 20 1 60 1 4 0 1 46 4 61 1 62 4P11b68e10da1ccaac 0 2 0 1 4 1P120005f149931c07 1 1 4 1 0 1 4 27 2 28 2 45 2 73 2P12c16d9f46d6c675 0 5 0 1 53 1 58 1 69 1 70 1P12d6723879c9411b 1 1 4 1 0 1 2 32 1 79 1P12dc4ddaee064960 0 4 0 2 28 8 29 8 46 8P12e719aa77c32b1a 0 2 0 1 3 1P1391e2af4fce8fc1 2 54 1 1 4 5 3 1 47 1 59 4 70 1 71 1 6 0 1 55 1 60 1 69 1 72 1 73 4 1 1 4 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 4P1489e5f12879adfb 0 6 0 1 52 1 53 1 57 1 66 1 67 1P14adaec479298454 1 1 4 1 0 1 2 29 1 76 1P14da9c4312d4f3bd 1 2 4 2 0 1 74 1 4 2 23 1 75 1 6 26 2 27 2 44 2 45 2 76 2 77 2P14f12cebad7468fd 2 54 1 1 4 5 3 1 47 1 59 4 70 1 71 1 6 0 1 55 1 60 1 69 1 72 1 73 4 1 1 4 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 4P150e1a4472ef42c5 0 5 0 1 53 1 58 1 69 1 70 1P158534f4f670ed7d 1 1 4 2 22 1 74 1 6 0 1 27 4 44 4 54 4 75 1 76 4P15c5b02f3a027546 0 2 0 1 33 1P1630844b87b25d8c 0 2 0 1 24 1P164bbcaa4cb41370 1 1 4 2 26 1 78 1 7 0 2 30 8 31 8 48 8 58 8 79 2 80 8P16a28fe5b6171145 0 4 0 2 28 8 29 8 46 8P16e070bad750bfa5 0 5 0 1 54 1 60 1 79 1 80 1P170662bcbb679113 1 1 4 1 0 1 2 31 1 78 1P1729cf3ac76e4834 1 2 4 2 0 1 78 1 4 2 27 1 79 1 6 30 2 31 2 48 2 49 2 80 2 81 2P17d51aa626c8be77 0 2 0 1 1 1P182de22987f66474 1 1 4 2 0 1 60 1 3 3 1 61 1 62 4P18493601715359dd 0 2 0 1 4 1P1945138dc15c9034 0 2 0 1 66 1P19957125044a46e5 0 5 0 1 54 1 60 1 79 1 80 1P19a6cc6d065ca570 2 55 1 1 4 3 1 1 81 1 82 1 10 0 32 32 128 33 128 50 128 55 32 60 128 61 32 80 32 83 32 84 128 1 1 4 3 2 1 80 1 83 1 5 0 1 33 4 81 1 82 1 84 4P19b0306cb5bfce4c 0 5 0 1 52 1 57 1 66 1 67 1P19f35dcabeebf738 0 5 0 1 54 1 59 1 70 1 71 1P1cb12f6555b707e2 1 1 4 1 0 1 5 25 1 30 1 48 1 49 2 78 2P1cb5307e6bbe3d3b 0 2 0 1 4 1P1cd026be70904b94 1 1 4 1 0 1 5 26 1 31 1 49 1 50 2 77 2P1d61c7e5637f6e66 0 2 0 1 1 1P1dd52979bb4b1a37 0 2 0 1 4 1P1dd986e4a37c8e6b 1 1 4 1 0 1 5 23 1 28 1 46 1 47 2 76 2P1e144626ca450f0a 0 6 0 1 52 1 53 1 57 1 66 1 67 1P1e31b20646bdd82e 1 1 4 1 0 1 4 26 2 27 2 44 2 74 2P1eeecd6a91c6af0a 0 5 0 1 52 1 57 1 66 1 67 1P1f25530252fe6e8d 0 5 0 1 53 1 58 1 69 1 70 1P1f6e8b394218287b 0 5 0 1 53 1 58 1 69 1 70 1P1f76e1fd84286da5 1 1 4 1 0 1 5 23 1 28 1 46 1 47 2 76 2P20365eb39882bfe2 1 1 4 1 0 1 2 31 1 78 1P20583dd673965e2e 0 6 0 1 52 1 53 1 57 1 66 1 67 1P20678f8f9e870230 0 4 0 4 37 1 67 4 68 1P20f46a5ae29d8004 0 5 0 1 52 1 57 1 66 1 67 1P213ae63db87a2a66 0 2 0 1 37 1P217f3451ae7d60f8 0 4 0 1 51 1 66 1 67 1P21baa141641aaf5c 1 1 4 1 0 1 2 19 1 60 1P225340b3a33aad2c 0 5 0 1 52 1 57 1 66 1 67 1P226acfaac1a81c0b 0 2 0 1 2 1P22fac51775583c36 1 1 4 1 0 1 5 25 1 30 1 48 1 49 2 78 2P234bdb56d3010480 0 3 0 1 31 4 48 4P23942f414b154479 0 4 0 4 38 1 66 4 69 1P243e7e0306102197 1 1 4 1 0 1 2 27 1 74 1P24ab81cdb7b6dadc 0 5 0 1 31 1 45 1 48 1 58 1P25815c16195a3e06 0 5 0 1 54 1 59 1 70 1 71 1P264fb98a449cfcb6 1 1 4 1 0 1 4 31 2 32 2 49 2 79 2P26ec9f542a566181 0 4 0 1 51 1 66 1 67 1P275ed2e8c425e10c 1 1 4 1 0 1 3 29 1 46 1 76 1P276b12abca7aa8de 2 54 1 1 4 5 3 1 47 1 59 4 70 1 71 1 6 0 1 55 1 60 1 69 1 72 1 73 4 1 1 4 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 4P27db87e62b8208ef 0 2 0 1 22 1P280a5325d26a22e1 1 2 4 2 0 1 79 1 4 2 28 1 80 1 3 32 1 81 1 82 1P28ddb9055a3a42e8 1 2 4 2 0 1 77 1 4 2 28 1 78 1 6 31 2 32 2 49 2 50 2 79 2 80 2P28e0ade79781e6de 0 5 0 1 54 1 60 1 79 1 80 1P2a17a9cc1141aac1 0 2 0 1 1 1P2a3fc4572df58885 2 54 1 1 4 3 3 1 70 1 71 1 6 0 4 55 4 60 4 69 4 72 4 73 16 1 1 4 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 4P2a6a4cb574e4ab0a 0 5 0 1 54 1 60 1 79 1 80 1P2a88fea084de39c0 0 2 0 1 3 1P2ac2f4c1c3816c5b 2 54 1 1 4 3 3 1 70 1 71 1 6 0 4 55 4 60 4 69 4 72 4 73 16 1 1 4 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 4P2ad17283a0db9554 0 3 0 1 27 4 44 4P2ae80bba3eb02305 1 1 4 1 0 1 5 21 1 26 1 44 1 45 2 74 2P2b217b4f29d27e58 1 1 4 1 0 1 5 24 1 29 1 47 1 48 2 75 2P2b6658120b8a6cf5 0 2 0 1 2 1P2b933ae24e6b7bc4 0 4 0 2 24 8 25 8 42 8P2bba39bba3f55a92 0 2 0 1 2 1P2bbc3a75813cc51c 0 2 0 1 67 1P2bf3ca50983a5a92 1 2 4 2 0 1 70 1 4 2 21 1 71 1 3 25 1 72 1 73 1P2c1adedaa0befa39 0 2 0 1 1 1P2c493ec784327a89 0 2 0 1 1 1P2c9d4247929625d4 0 3 0 1 31 4 48 4P2ca156bdac360f23 0 2 0 1 2 1P2d492c44f2ba0d50 0 2 0 1 24 1P2e129aff832eb2e2 2 54 1 1 4 3 3 1 70 1 71 1 6 0 4 55 4 60 4 69 4 72 4 73 16 1 1 4 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 4P3133fecc89a0c282 1 1 4 1 0 1 3 32 1 49 1 77 1P3174a10033d07bd4 0 2 0 1 23 1P31a2eb9ecbb795a9 1 1 4 2 26 1 78 1 6 0 1 31 4 48 4 58 4 79 1 80 4P31fd45936578e2b8 0 5 0 2 25 1 30 1 48 1 49 2P320074812a902350 0 5 0 1 52 1 57 1 66 1 67 1P3216f1a9fa589aa4 0 5 0 1 52 1 57 1 66 1 67 1P3248c5b29fd75bc3 0 3 0 1 27 4 44 4P329e99dcc6985a9b 0 2 0 1 4 1P32d69f9b3cf04d09 0 5 0 1 54 1 59 1 70 1 71 1P33b760844d6b5bae 0 7 0 2 8 1 30 1 44 1 45 2 48 1 58 1P34b3aefda045a4f6 0 4 0 1 51 1 66 1 67 1P34c791ad70f75cc5 0 5 0 1 52 1 57 1 66 1 67 1P3526b6e776bf22bb 1 1 4 1 0 1 7 4 1 26 1 40 1 41 2 44 1 54 1 74 2P354ca5662fa34989 1 1 4 1 0 1 2 29 1 76 1P3555437353da2050 0 5 0 1 54 1 59 1 70 1 71 1P357828acfb6b6913 0 2 0 1 38 1P35bf9c6b492798e0 1 1 4 1 0 1 3 31 1 48 1 78 1P36e4ab6c806d9260 0 2 0 1 32 1P3725f1f4ada9e847 0 5 0 1 53 1 58 1 69 1 70 1P37febbc773dd2fe2 1 1 4 1 0 1 5 25 1 30 1 48 1 49 2 78 2P3971d9e73122f959 0 5 0 1 54 1 59 1 70 1 71 1P399c90304d365a1e 2 54 1 1 4 3 3 1 70 1 71 1 6 0 4 55 4 60 4 69 4 72 4 73 16 1 1 4 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 4P39a756876466a96e 0 5 0 1 54 1 59 1 70 1 71 1P3a8c91558dd434fe 0 6 0 1 52 1 53 1 57 1 66 1 67 1P3ae74fe2af2db2f8 1 1 4 1 0 1 2 27 1 74 1P3b594df6c769a8fa 2 54 1 1 4 5 3 1 47 1 59 4 70 1 71 1 6 0 1 55 1 60 1 69 1 72 1 73 4 1 1 4 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 4P3baefde05be70640 1 1 4 1 0 1 2 25 1 70 1P3c4fde2ad757e231 0 4 0 2 24 8 25 8 42 8P3db681b86c1b7fa4 1 2 4 2 0 1 75 1 4 2 26 1 76 1 6 29 2 30 2 47 2 48 2 77 2 78 2P3dd019aa4ff73755 0 2 0 1 4 1P3de1e5c6938f8d88 0 3 0 1 17 4 40 1P3e7286cdf7f1a0cd 0 2 0 1 3 1P3eb213347d26de85 0 2 0 1 23 1P3f02c08f32a0bab8 2 54 1 1 4 5 3 1 47 1 59 4 70 1 71 1 6 0 1 55 1 60 1 69 1 72 1 73 4 1 1 4 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 4P3f2edf85124fcde6 2 54 1 1 4 3 3 1 70 1 71 1 6 0 4 55 4 60 4 69 4 72 4 73 16 1 1 4 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 4P3f576e83e687bf5a 0 5 0 1 52 1 57 1 66 1 67 1P3f83587929b979c5 0 5 0 1 52 1 57 1 66 1 67 1P3f9a985d8dc37e07 0 5 0 1 54 1 60 1 79 1 80 1N0373f19305775b42N047583f93e14bbc3N055e033000007463N0644a20d344205f3N066caebc1a2f6641N06b48e70af5381d5N06c0156ff4ff3350N07842ac2e5b55d57N07fdfad1fbe61121N0818041d52431a25N0862c9c20b5bb6a9N08c18a474fa2e7d2N094e58b7af277580N09de0942b30757ddN09e1f2082611ad83N0aeaf826520155adN0b77ff6366810fc2N0bfcb19dd5ea4ea0N0c86a761412dd93dN0caa9a0065d805adN0e6f7202e77f0b7dN0e79d4932cef0dcaN0f5eb687a8828821N0fa3725661a81cc0N0fdb7579f317267dN0ff59621d51ae2d0N10562439b970c9f4N10f419c8aba71bfbN112867bac21370d8N11fe200a8420ba49N129a1ddc0b555a84N12d6673a6e3b9f2fN12e17c498cab66d0N12f41dbcdfbf6345N13177a29ad285919N134281db2f9cd569N13ce2217d76affccN13f28af63c17616aN142349080b27f901N145c767020aa40a4N149241294df41256N14b1f7408ea54e6cN15965d11dd46bd91N16a28506a9ec4f3dN16baecb7bee76787N17056d60335c751cN1760c4884f1052dbN178280529f1c52ffN17925e0a78c1cf22N190ff452287fe01eN1938561f83da9affN19c72c0dea0eff41N19ed44c3f08a114fN1a7f51ced6dc5f91N1a95c49b4304996bN1af33bc8ebe8d8a9N1b192251c2703360N1b1a524fb0a5f4c2N1b483b9f09c303ccN1cdb62a30d9ca979N1cfc275944b8a8d6N1d0ba1733c5f52faN1d71a32851ae0a9bN1d8a68c9bbefb81cN1ef5a7edf14a5167N1f0d2fe70a963f7cN2054e0c788617062N208c6c41055e950fN20da2b203694bcccN210e99873ab3bef9N221059ba652c39f2N22a170ac4049ba2bN257fabe334bc57b7N25852e71d7c8441fN25ffa207ff92d925N2640eb97433494e8N26f56e5c0b5c5d66N272c13f922f202ceN285cdac671117166N29a5a6c5140bbf81N29a7a6ed7c6d8957N2a3a82c8d9827a84N2a494ccf2b6917bbN2baeffa38e5c5bc6N2bce886100a1214bN2bcefd90c2121398N2c1dcbe1cac1baedN2ca165fd77a80183N2cdba004f19f7225N2e9fc286bc48dd68N2f89892b5e205cb6N2fd5b49a0d94cfc8N3006fba086e2e118N30693ff58caee3b3N307bce6cb35e0befN31f6b10402b471c9N3275acd2e45e5129N334563f73226a00eN33559de6533e3d3aN335f1b25a235ad5fN34fb6f17a4b4a424N35952e48b05b6cabN36b3fc27001fc7e7N37279f20106c7b94N389eb64f6ba644cdN39b67188afed6b0aN3a83cb3200e00d7cN3b5de2ecba03feb7N3ba249642dc75c0cN3bb02326c686d14dN3bcb5f7d2762e06bN3c6a214cd6d144e6N3cb297c0d41c1442N3d039e6b7eef2f66N3d35e668dd33a945N3d35e67163dec7baN3dc99f68cc150126N3dda907f83fca7beN3f32c409723cd396N3f8d437479880715N3fb054e7ee0bfdb5"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_mpi_core_read_be () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "MPI_CORE_READ_BE_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_core_read_be_postA"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_core_read_be.read_be_ret"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_core_mul.A_ASAN_MEMSET"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemcpy"; "A_ASAN_MEMCPY"; "mpi_core_read_be_stmtA"; "A_MPI_CORE_READ_BE"].


Definition A_MPI_CORE_READ_BE : Z := 0xa3dc4.
Definition A_ASAN_MEMCPY : Z := 0x67dbc.
Definition MPI_CORE_READ_BE_STACK_A : Z := 64.

Definition mpi_core_read_be_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n r : Z) (xs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_read_be ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R11.(7.(8.O18.O17.O16.O15.R10.R?.R>.O14.O13.(9.&40.O4.)R=.R<.R;.R:.R9.R8.R7.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R6.R5.R4.R3.)O8.(:.O18.)O7.(;.(2.&40.))R2.(<.O1>.)))(5.(=.(>.(?.$10.$10.)(11.$10.$10.O6.(12.O6.(13.+4.O5.)))(>.(?.$10.$10.)(11.$10.$10.O2.(14.&40.O17.))(15.(?.$10.$10.))))O1.R2.)(5.(16.O1>.O1.R2.)(5.(17.O1>.R2.)(5.(18.O1>.R2.O6.R1.)(5.(6.$19.(1:.(2.&40.)R1.)(1:.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1;.(2.&40.)(1<.O5.)R1.)(1;.(2.&40.)(1<.O5.)O3.))(5.(1=.O1>.R2.O2.(14.&40.O17.))(1>.O1>.O1=.O1<.O1;.O1:.O19.R2.)))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_read_be_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_read_be ()) "Ph,(1?.O4.O3.O2.)PLB,(4.$20.)PLF,(4.$20.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(21.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$10.Pn,$10.PB,$10.Pblen,$10.Plo,$10.Pxs,(4.(2.&40.))Pbs,(4.(2.&8.))P,(1>.O4.O3.O2.R2<.R2;.R2:.R8.)P,(18.O4.R9.R8.R3.)P,(22.O4.R:.R7.R3.)P,(5.(23.=R9.)(23.R9.+2710.))P,(23.R:.(24.(1:.(2.&40.)R6.)))P,(5.(23.=R9.)(23.R9.(24.(1:.(2.&8.)R6.))))P,(25.(23.(12.R;.(24.(1:.(2.&8.)R7.)))R=.)(23.(12.R=.(13.+4.(24.(1:.(2.&40.)R8.))))R;.))P,(6.$10.(26.R>.+4.)=)P,(25.(6.$10.R>.=)(27.+4.R?.))P,(25.(6.$10.R=.=)(27.=R>.))P,(27.(12.R11.(13.+4.(24.(1:.(2.&40.)R<.))))(28.+2.+40.))P,(27.(12.R10.(24.(1:.(2.&8.)R<.)))(28.+2.+40.))P,(1=.O4.R14.R?.(14.&40.R34.))P,(23.(29.O3.)R10.)P,(23.R11.(2:.(2:.(14.&40.R36.)$2;.)(2<.O3.)))P,(23.(14.&40.R37.)(2=.O4.O3.O2.R3;.))P,(6.$10.(26.(14.&40.R38.)+10.)=)P,(25.(23.(12.R18.(13.+4.(24.(1:.(2.&40.)R13.))))R14.)(23.(14.&40.R39.)R18.))P,(25.(23.(12.R17.(24.(1:.(2.&8.)R13.)))R15.)(23.(14.&40.R3:.)R17.))P,(25.(6.$10.R17.=)(23.(12.(12.R18.R17.)+8.)(28.+2.+2?.)))P,(2>.(2?.O3.)(30.$20.R3?.(31.R3>.))(29.O3.)(2=.O4.O3.O2.R40.)R1;.(13.+4.R1:.))P,(17.O4.R1=.)P,(6.$10.(26.(14.&40.R3?.)+2.)=)P,(32.O4.(33.O3.)(34.O4.O3.O2.R43.)R1?.R1>.(13.+4.R1=.))P,(32.O4.(33.O3.)(34.O4.O3.O2.R44.)R20.R1=.R1<.)P,(6.(2.&40.)R39.(9.&40.R20.))P,(6.(2.&40.)R39.(9.&40.R20.))P,(6.(2.&40.)R39.(9.&40.R20.))P,(6.(2.&40.)R39.(9.&40.R20.))(35.O4.(33.O3.)(34.O4.O3.O2.R49.)(36.O4.O3.O2.R49.R48.R47.R46.R45.R44.R43.R3?.R3>.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R27.R26.R24.R23.(37.R23.R21.)R1?.R20.R25.)(7.(8.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.)R27.(9.&40.O1.)R26.(;.(2.&40.))R25.(<.O4.)))")
(* [comment removed for export] *).

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.   (* [comment removed for export] *)
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY.
  Hypothesis NEED0 : 0 <= arl_need_amem R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X n blen lx lo : Z) (xs0 : list word).
  Hypothesis Hn : 0 < n <= 10000.
  Hypothesis Ln : n <= lx.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis Hbl : 0 <= blen.
  Hypothesis XB : 4 < X /\ X + 4 * lx < 2^64.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - 64 - arl_need_amem R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis OK : chars_to_limbs4 blen <= n.
  Hypothesis CWX : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) X (4 * n).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    match goal with HH : HM _ _ _ h LB LF _ |- _ =>
      pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP;
      assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; lia);
      assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - TOP HTOP; lia])
    end.

  Notation POST := (mpi_core_read_be_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n (read_be_ret n blen) xs0 lo m).
  Notation W := [(X, X + 4 * n); (lo, bv_unsigned sp)].
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -64)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation FRAME mm junk := (rw_cells asegs mm (bv_unsigned sp + -64) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation DINV mm xs := (u32arr asegs mm X xs /\ Z.of_nat (length xs) = lx /\ same_from (Z.to_nat n) xs xs0
                          /\ munch W m mm /\ wmono asegs m mm /\ mem_inv asegs mm /\ stk asegs mm lo (bv_unsigned sp + -64)
                          /\ HM asegs R HIA h LB LF mm).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L2977899845.5000000IS2ra2sp1X1n4blen3xs02OK1E". (* [comment removed for export] *)
  Lemma ret_ok : read_be_ret n blen = 0.
  Proof. unfold read_be_ret. destruct (n <? chars_to_limbs4 blen) eqn:E; [apply Z.ltb_lt in E; lia | reflexivity]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0@D16567456097.93 D5483095183.93  D563007111.94   D62022258533.94 L14771727165.5  L19145254977.113L20489621819.5  L25421253429.5  L27502493422.81 L29428324939.5  L30534504739.113L35653441506.7  L53643024490.4  L60098763854.3  L6276468881.4   L7987122863.9   00000K00d01E01`01n02Q02_02i05J05\06?06W06c06m07707WS2ra2sp1X1n3xs01k1l1r2xs2HkS2ra2sp1X3xs01k1l1r2xs2HkS1R3HIA1h2ra2sp1X3xs01k1l1r2xs2HkS1R2ra2sp1X3xs01k1l1r2xs2HkS1n1l1r3Hlr2HsS2ra2sp1X3xs01k1l1r2xs2Hk4lxv24lxv5S1n1l1r3Hlr2HsS1k1l1r2HkS1R3HIA1h2LB2LF2ra2sp2gp2tp2s02s12s22s32s42s52s62s72s82s93s103s111F2fc1m1X1n4blen2lo3xs01l1r2xs2mm3xra3xt03xt13xt23xs13xa63xa73xs23xs43xs53xt33xt43xt53xt62Hk3HlrS1R2lo3LOS3ALO3ACPS2ra2sp1X3xs01k1l1r2xs2Hk4lxv24lxv5S1R3HIA1h2sp2lo3TOP4HTOPS1l1r3Hlr2BRS1R2lo3LOSS1n1l1r2HsS2lx3xs02L01l1r2xs4lxv24lxv53LX'". (* [comment removed for export] *)
  Lemma loop_walk : forall (k : nat) (l r : Z) (xs : list word) (mm : mem) (junk : list byte)
      (xra xt0 xt1 xt2 xs1 xa6 xa7 xs2 xs4 xs5 xt3 xt4 xt5 xt6 wl wr : word),
      r - l < 2 * Z.of_nat k -> 0 <= l <= r -> l + r = n - 1 ->
      wl = Z_to_bv 64 (X + 4 * l) -> wr = Z_to_bv 64 (X + 4 * r) ->
      DINV mm xs -> FRAME mm junk -> aobj asegs AL CS mm X (4 * n) ->
      evtA asegs AL CS POST
        (MS (mkR xra SP' gp tp xt0 xt1 xt2 wl xs1 wr wl wr (Z_to_bv 64 (-5)) (Z_to_bv 64 0xff00) (Z_to_bv 64 5)
                 xa6 xa7 xs2 SB xs4 xs5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa3eb4) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros l r xs mm junk xra xt0 xt1 xt2 xs1 xa6 xa7 xs2 xs4 xs5 xt3 xt4 xt5 xt6 wl wr Hk Hlr Hs -> ->
      (HX & LX & FX & MU & WM & MI & ST & HH) FR OX; [lia|]. rt_facts.
    lxr_pose. lx_spell. lx_pre.
    lx_run_tac (PLAN [0xa3eb4] [(0xa3ec4, DJoin); (0xa3ed8, DJoin); (0xa3ee4, DJoin); (0xa3f14, DJoin)] 90%N). lx_tree.
    all: lxr_leaf; lx_carry; lx_gc.
    all: match goal with H1 : u32arr asegs ?m2 X ?xs2 |- evtA _ _ _ _ (MS _ _ _ _ _ ?m2 _) =>
           rename H1 into HX';
           assert (LX' : Z.of_nat (length xs2) = lx) by (rewrite !upd_length; exact LX);
           assert (FX' : same_from (Z.to_nat n) xs2 xs0) by (repeat (apply same_from_upd_lt; [|clear - Hlr Hs; lia]); exact FX);
           lx_rn_munch MU'; lx_rn_wmono WM'; lx_rn_mi MI'; lx_rn_stk ST' end.
    - (* [comment removed for export] *)
      match goal with K : 0 <= -4 * l + (4 * r + -8) |- _ => rename K into BR end.
      eapply (IH (l + 1) (r - 1)); [clear - Hk Hlr; lia | clear - Hlr BR; lia | clear - Hs; lia | f_equal; lia | f_equal; lia
        | exact (conj HX' (conj LX' (conj FX' (conj MU' (conj WM' (conj MI' (conj ST' HH))))))) | exact FR | assumption ].
    - (* [comment removed for export] *)
      rewrite ret_ok. lx_post; [> exact HX' | clear - LX' L0; lia | apply same_from_skipn; [exact FX' | clear - LX' L0; lia] | .. ].
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?D16567456097.90D5483095183.90 D563007111.91  D62022258533.91L29094647515.1 L29428324939.5 L30532261533.87L35653441506.7 L57639537979.2 L60098763854.3 L60289041929.87L63720461198.2 00000B00R00j01<01?01Q01c02;02A02K02[02aS2ra2sp1X1n3xs02xsS2ra2sp1X3xs02xsS1R3HIA1h2ra2sp1X3xs02xsS1R2ra2sp1X3xs02xsS1nS1R2lo3LOS3ALO3ACPS2ra2sp1X1n3xs02xsS1R3HIA1h2sp2lo3TOP4HTOPS1n2HnS1R2lo3LOSS2ra2sp1X3xs02xsS1n2Hn". (* [comment removed for export] *)
  Lemma conv_walk : forall (xs : list word) (mm : mem) (junk : list byte)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xt3 xt4 xt5 xt6 ws1 ws4 : word),
      ws1 = Z_to_bv 64 (4 * n) -> ws4 = Z_to_bv 64 n ->
      DINV mm xs -> FRAME mm junk -> aobj asegs AL CS mm X (4 * n) ->
      evtA asegs AL CS POST
        (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 X) ws1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                 xs2 SB ws4 xs5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa3e60) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    intros until ws4. intros -> -> (HX & LX & FX & MU & WM & MI & ST & HH) FR OX. rt_facts.
    lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0xa3eb4] [] 40%N). lx_tree.
    all: lx_same_mem; lx_gc; try clear OQH.
    eapply (loop_walk (Z.to_nat n) 0 (n - 1)); [clear - Hn; lia | clear - Hn; lia | clear; lia | f_equal; lia | f_equal; lia
      | exact (conj HX (conj LX (conj FX (conj MU (conj WM (conj MI (conj ST HH))))))) | exact FR | exact OX].
    all: match goal with |- ?g => idtac "CONV-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "03H0@C17025492443.129C17025492443.136C24870685926.137C32557765051.137C45137625611.130D16565017318.98 D16569571680.132D20197639228.138D5472627854.132 D5485375240.98  D563007111.99   D60109446735.132D60109446735.138D60203142919.138D62022258533.99 D64311484648.132D64311484648.138K15588900467.129K36719207456.129K36719207456.136K38549772511.137K4325584196.138 K4325584196.140 K44973613286.132K4709732394.136 K49644543183.130K51736254456.137K54754243139.137K57898196488.137L11901686152.50 L12733936911.69 L12736964323.56 L13042993542.51 L15601019926.4  L16824139329.50 L17646078182.99 L18293330070.2  L18573586357.58 L18573586357.60 L18573893142.114L20184675091.59 L21097429411.54 L21097429411.67 L21104654755.116L21104654755.134L21861379102.55 L27993512217.56 L28136076198.57 L28136130109.51 L28137792890.69 L29428551881.79 L29429056688.44 L30986492595.49 L30986829673.48 L30987168515.114L30987168521.108L33189481538.72 L33684699757.64 L34113589981.59 L34113589981.62 L34115610467.118L35667338951.62 L35667657501.62 L35668187074.59 L36715738693.2  L37288975338.59 L37288975338.60 L37291454036.117L37291454036.118L37468808905.5  L38548947365.3  L39016714998.5  L39172636981.0  L39310718378.118L39313145876.62 L39313145876.63 L42022308307.55 L43059596331.97 L4313824549.5   L4319883708.5   L43718780418.59 L43721138830.74 L4375655833.117 L4377395239.53  L4377395239.55  L44963822876.3  L45194705697.0  L46772641698.117L46772641698.118L46774561308.64 L46774561308.65 L47053128703.50 L47053128703.51 L4705469007.5   L47055058497.114L47055058497.118L47283864467.50 L47285887187.63 L49158362917.66 L49159270507.50 L49159270507.53 L49161362620.3  L49409390644.114L49409390644.118L49409390654.108L49409390654.112L49409469534.62 L49409788292.62 L49656466606.3  L49911831958.51 L50282432488.50 L50284982870.114L51729945955.110L51730359518.53 L51730359518.54 L51731989917.5  L5262243222.85  L53763021781.2  L54741090796.116L54741090796.121L54741090796.134L54741090796.139L54741835410.66 L54743059838.53 L54754011961.4  L5483969141.48  L55315076415.116L55315076415.134L55321253183.54 L55321253183.67 L55959448093.109L55959448093.112L55959853984.50 L55959853984.51 L56784985419.2  L57017434196.46 L57519689234.84 L57628690499.134L57628691269.125L57835392626.59 L57835727784.59 L57899009906.3  L57929056743.68 L57929056743.69 L57930789977.117L57930789977.118L58430200545.46 L58710375227.5  L59310615034.127L59836247768.1  L59904363750.56 L59905141799.69 L60098234548.57 L60098571630.57 L60098763883.54 L60164579387.59 L60445797666.53 L60447751886.66 L60745729305.48 L61085994631.57 L61086071580.51 L61086206625.107L61086206625.112L61087958821.116L61087958821.121L61087958821.134L61087958821.139L61088766043.69 L6330017699.64  L6330017699.66  L6331589792.76  L6331589792.78  L63552601673.47 L63742606293.2  L65032630433.0  L68368272763.53 L8504542741.3   L8517790851.55  L8518159426.68  L9789376992.48  N22834764276.130N37104593031.130N39208714554.137N42129917801.137O17025492443.129O17025492443.136O17223163713.129O24425325148.132O24870685926.137O31132687832.136O32557765051.137O42224484491.132O44531189307.137O45137625611.130O54173095307.131O57399310481.137O57442556486.138O57442556486.140P36719207456.129P36719207456.136P38549772511.137P4325584196.138 P4325584196.140 P49644543183.130P53756888623.132P63752726063.131Q16569571680.132Q20197639228.138Q30987168515.118Q30987168521.112Q38248387216.132Q38248387216.138Q43879899724.132Q43879899724.138Q5472627854.132 Q60203142919.13800000100200300400500M00e01F01^02602V03703X04504O05605]06?06@06A06B06C06D07107\07]08G09=09_09d0:40:D0:T0:U0:^0;60;=0;>0;?0<C0<Q0<R0<S0=80=c0=f0>50>G0>Y0>k0?R0?S0?T0?U0@Q0AM0Ag0BC0BD0BE0CN0Cj0DF0Db0Dc0Dd0De0Df0Dg0E80E90EK0EL0F\0F]0F^0Fa0Ga0Gb0Gc0H50HG0I:0I;0I<0I=0I>0I?0I@0IA0IB0IC0ID0IE0IF0IG0IK0IO0IY0Ic0Im0J:0J;0J<0J=0J>0J?0J@0JA0JQ0JR0K=0Kn0Ko0L00L10M?0M@0MA0MB0MC0MD0ME0MF0MG0MJ0Mk0NR0NS0NT0NU0NV0NW0NX0N^0N_0OI0PY0Q<0QP0Qd0Qe0Qf0Qg0Qh0Qi0R50RJ0Ri0Rl0S10S60S@0SJ0ST0S^0Sh0T20T90T:0T;0T<0T=0T>0T?0T@0TA0TB0TC0U20U30Ub0V10V20V30V:0VG0VS0V_0Ve0Vf0Vg0Vh0Vi0Vj0Vk0Vl0Vm0Vn0Vo0W00W10W20W30W40W50W60W70W80W90W:0W;0W<0W=0W>0W?0WT0X20Xb0YR0Yh0Z>0ZT0Zj0[?0[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". (* [comment removed for export] *)
Lemma A_mpi_core_read_be_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_read_be ()) "PR,$3>.PHIA,(3?.$38.R1.)P,(40.(33.R2.))P,(6.$10.(41.R3.)$42.)P,(6.$10.(43.R4.)$44.)P,(23.=(2<.R5.))(45.$38.R6.R5.$46.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG AMS AMC NEED0. unfold mpi_core_read_be_stmtA, A_MPI_CORE_READ_BE.
  intros until bs. intros HH HX HB Hn LX Hbl DB ALX NZX NZB XT BT ST LOS LO TOP SPA SX SB HB47 CWX MI RA OX OB -> -> -> ->.
  unfold MPI_CORE_READ_BE_STACK_A in *.
  pose (lxi := lxA_img (arl_AL R) IMG).
  pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
  pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (bytes_at_bound _ _ _ _ HB) as BB0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (LO0 : 0 <= lo) by klia.
  assert (BLT : 0 <= blen < 2^64) by lia. assert (XLT : 0 <= X < 2^64) by lia.
  assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| klia| klia]).
  pose proof (munch_refl [(X, X + 4 * n); (lo, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (lock HB) as HB00.
  pose proof (hm_abase asegs R HIA h LB LF m HH) as ABS.
  (* [comment removed for export] *)
  pose proof (firstn_skipn (Z.to_nat n) xs) as EY. symmetry in EY.
  assert (LP : length (firstn (Z.to_nat n) xs) = Z.to_nat n) by (rewrite length_firstn; klia).
  pose proof HX as HXfull.
  rewrite EY in HX. apply u32arr_app in HX. destruct HX as [HXB HXC]. rewrite LP in HXC.
  apply u32arr_cells in HXB. rewrite LP in HXB. apply (u8arr_of_rw_cells asegs) in HXB.
  pose proof (lock HXC) as HXC0. clear HXC.
  assert (LXB8 : Z.of_nat (length (u32s (firstn (Z.to_nat n) xs))) = 4 * n) by (rewrite u32s_length, firstn_length; klia).
  assert (CR : 0 <= chars_to_limbs4 blen <= blen) by (unfold chars_to_limbs4; clear - Hbl; lia).
  carve_frame 64%nat ST.
  clear HB.
  (* [comment removed for export] *)
  lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0x68258] [] 60%N). lx_tree.
  all: lxr_leaf; lx_carry; lx_gc.
  all: match goal with
       | K : 0 <= - ?n' + (?bl ≫ 2 + _) |- _ =>
           assert (E2 : bl ≫ 2 = bl / 4) by (rewrite Z.shiftr_div_pow2 by (clear; lia); reflexivity);
           assert (LT8 : n < chars_to_limbs4 blen) by (pose proof (chars_to_limbs4_eq blen ltac:(clear - Hbl; lia)) as E; clear - K E E2; lia);
           clear K E2; assert (R8 : read_be_ret n blen = -8) by (unfold read_be_ret; rewrite (proj2 (Z.ltb_lt _ _)) by exact LT8; reflexivity)
       | K : 0 <= ?n' + (- (?bl ≫ 2) + - _) |- _ =>
           assert (E2 : bl ≫ 2 = bl / 4) by (rewrite Z.shiftr_div_pow2 by (clear; lia); reflexivity);
           assert (GE : chars_to_limbs4 blen <= n) by (pose proof (chars_to_limbs4_eq blen ltac:(clear - Hbl; lia)) as E; clear - K E E2; lia);
           clear K E2; assert (R0 : read_be_ret n blen = 0) by (unfold read_be_ret; rewrite (proj2 (Z.ltb_ge _ _)) by exact GE; reflexivity)
       end.
  (* [comment removed for export] *)
  all: try (lazymatch goal with R8' : read_be_ret _ _ = -8 |- evtA _ _ _ _ (MS _ _ (ret_pc _) _ _ _ _) =>
              rewrite R8'; lx_post; [> eassumption | reflexivity | reflexivity | .. ] end).
  all: try (lazymatch goal with R0' : read_be_ret _ _ = 0 |- evtA _ _ _ _ (MS _ _ (ret_pc _) _ _ _ _) =>
              rewrite R0'; lx_post; [> eassumption | reflexivity | reflexivity | .. ] end).
  (* [comment removed for export] *)
  assert (BL4 : blen <= 4 * n) by (clear - GE Hbl; unfold chars_to_limbs4 in GE; lia).
  clear HXfull.
  match goal with K : aobj _ _ _ _ X ?n4 |- _ => replace n4 with (4 * n) in K by (clear; lia) end.
  match goal with K : u32arr _ _ X xs |- _ => clear K end.
  clear HXB ABS. lx_rn_munch MU. lx_rn_wmono WM.
  pose proof (artA_amemset asegs R HIA A_ASAN_MEMSET) as SPM. rewrite <- AMS in SPM. unfold A_ASAN_MEMSET in AMS. rewrite AMS in SPM.
  callxA_sp (bv_unsigned sp + -64)
    (eapply SPM with (h := h) (LB := LB) (LF := LF) (DST := X) (v := 0) (n := 4 * n) (lo := lo);
     rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by klia;
     try eassumption; try reflexivity; try klia;
     first [ left; reflexivity | rewrite u32s_length, length_firstn; klia | f_equal; klia
           | eapply crange_sub; [exact SCS0| klia| klia]
           | eapply (cw_top47_in asegs R HIA h LB LF); [eassumption| exact CWX| klia| klia| klia]     (* [comment removed for export] *)
           | match goal with |- ?g => idtac "MEMSET-PRE-LEFT:" g end ]).
  clear SPM.
  lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
  match goal with H : u8arr _ m5 X _ |- _ => rename H into RW end.
  lx_rn_munch MU5. lx_rn_wmono WM5.
  assert (LRW : Z.of_nat (length (repeat (Z_to_bv 8 0) (Z.to_nat (4 * n)))) = 4 * n) by (rewrite repeat_length; clear - Hn; lia).
  all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "MEMSET-SIDE:" g end.
  (* [comment removed for export] *)
  assert (X4 : 4 < X) by (destruct NZX as [N0|N0]; [exfalso; lia | exact N0]).
  lxr_pose. lx_spell. lx_pre. lx_run_tac (PLAN [0x67dbc; 0xa3e60] [] 40%N). lx_tree.
  all: lx_same_mem; lx_gc; try clear OQH.
  - (* [comment removed for export] *)
    match goal with MU5 : munch _ m m5, WM5 : wmono _ m m5 |- _ =>
      pose proof (u32arr_transport asegs _ m m5 _ _ (unlock _ HXC0) MU5 WM5 ltac:(cbn [disjoint_from]; rewrite length_skipn; klia)) as HXC end.
    apply (rw_cells_of_u8arr asegs) in RW. rewrite repeat_length in RW.
    apply (u32arr_of_cells asegs m5 _ _ _ (repeat (Z_to_bv 64 0) (Z.to_nat n))) in RW; [| rewrite u32s_repeat0; f_equal; klia ].
    assert (HX : u32arr asegs m5 X (repeat (Z_to_bv 64 0) (Z.to_nat n) ++ skipn (Z.to_nat n) xs)).
    { apply u32arr_app. split; [exact RW|]. rewrite repeat_length.
      lazymatch type of HXC with u32arr _ _ ?a _ => replace (X + 4 * Z.of_nat (Z.to_nat n)) with a by klia end. assumption. }
    assert (LX' : Z.of_nat (length (repeat (Z_to_bv 64 0) (Z.to_nat n) ++ skipn (Z.to_nat n) xs)) = Z.of_nat (length xs))
      by (rewrite length_app, repeat_length, length_skipn; klia).
    assert (FX' : same_from (Z.to_nat n) (repeat (Z_to_bv 64 0) (Z.to_nat n) ++ skipn (Z.to_nat n) xs) xs).
    { intros q Hq. rewrite nth_error_app2 by (rewrite repeat_length; klia). rewrite repeat_length, nth_error_skipn. f_equal. klia. }
    match goal with H4 : mem_inv asegs m5, H5 : stk asegs m5 lo _, H6 : HM _ _ _ h LB LF m5, MU5 : munch _ m m5, WM5 : wmono _ m m5 |- _ =>
      pose proof (conj HX (conj LX' (conj FX' (conj MU5 (conj WM5 (conj H4 (conj H5 H6))))))) as DI end.
    eapply conv_walk with (h := h) (LB := LB) (LF := LF) (lx := Z.of_nat (length xs)); try eassumption; try klia; try (f_equal; klia).
    all: match goal with |- ?g => idtac "NOCPY-LEFT:" g end.
  - (* [comment removed for export] *)
    replace (Z.to_nat (4 * n)) with (Z.to_nat (n * 4 - blen) + Z.to_nat blen)%nat in RW by klia.
    rewrite repeat_app in RW. apply u8arr_app in RW. destruct RW as [RW1 RW2]. rewrite repeat_length in RW2.
    replace (X + Z.of_nat (Z.to_nat (n * 4 - blen))) with (X + (n * 4 - blen)) in RW2 by klia.
    apply (rw_cells_of_u8arr asegs) in RW1. rewrite repeat_length in RW1.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      match goal with MU5 : munch _ m mx |- _ =>
        pose proof (bytes_at_transport asegs _ m mx B bs (unlock _ HB00) MU5 ltac:(cbn [disjoint_from]; klia)) as HB1 end end.
    rewrite <- (firstn_skipn (Z.to_nat blen) bs) in HB1. apply bytes_at_app in HB1. destruct HB1 as [HB1 _].
    assert (OBl : aobj asegs (arl_AL R) (hcs asegs R HIA h) m5 B (Z.of_nat (length (firstn (Z.to_nat blen) bs)))).
    { rewrite length_firstn. replace (Z.of_nat (Nat.min (Z.to_nat blen) (length bs))) with blen by klia. assumption. }
    assert (OXw : aobj asegs (arl_AL R) (hcs asegs R HIA h) m5 (X + (n * 4 - blen)) blen).
    { eapply aobj_sub; [exact OX | klia | klia]. }
    pose proof (artA_amemcpy asegs R HIA A_ASAN_MEMCPY) as SPC. rewrite <- AMC in SPC. unfold A_ASAN_MEMCPY in AMC. rewrite AMC in SPC.
    callxA_sp (bv_unsigned sp + -64)
      (eapply SPC with (h := h) (LB := LB) (LF := LF) (DST := X + (n * 4 - blen)) (SRC := B) (n := blen) (lo := lo) (ss := firstn (Z.to_nat blen) bs);
       rewrite ?(unsigned_lit (bv_unsigned sp + -64)) by klia;
       try eassumption; try reflexivity; try klia;
       first [ left; reflexivity | rewrite repeat_length; klia | rewrite length_firstn; klia | f_equal; klia
             | eapply crange_sub; [exact SCS0| klia| klia]
             | eapply client_wrange_inside; [exact CWX | intros b Hb; exact Hb | klia | klia]
             | exact HB47                                                                              (* [comment removed for export] *)
             | eapply (cw_top47_in asegs R HIA h LB LF); [eassumption| exact CWX| klia| klia| klia]     (* [comment removed for export] *)
             | match goal with |- ?g => idtac "MEMCPY-PRE-LEFT:" g end ]).
    clear SPC.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with MU6 : munch _ m m6, WM6 : wmono _ m m6 |- _ =>
      pose proof (u32arr_transport asegs _ m m6 _ _ (unlock _ HXC0) MU6 WM6 ltac:(cbn [disjoint_from]; rewrite length_skipn; klia)) as HXC end.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-MEMCPY-SIDE:" g end.
    match goal with H : rw_cells _ m6 X [CB _ _] |- _ => rename H into RW1z end.
    match goal with H : u8arr _ m6 (X + (n * 4 - blen)) _ |- _ => rename H into RW2 end.
    apply (u8arr_of_rw_cells asegs) in RW1z.
    assert (U8 : u8arr asegs m6 X (repeat (Z_to_bv 8 0) (Z.to_nat (n * 4 - blen)) ++ firstn (Z.to_nat blen) bs)).
    { apply u8arr_app. split; [exact RW1z|]. rewrite repeat_length.
      replace (X + Z.of_nat (Z.to_nat (n * 4 - blen))) with (X + (n * 4 - blen)) by klia. exact RW2. }
    clear RW1z RW2.
    destruct (u32arr_of_u8arr asegs m6 X _ (Z.to_nat n) U8 ltac:(rewrite length_app, repeat_length, length_firstn; klia)) as (ws & HXB & LW).
    clear U8.
    assert (HX : u32arr asegs m6 X (ws ++ skipn (Z.to_nat n) xs)).
    { apply u32arr_app. split; [exact HXB|]. rewrite LW.
      lazymatch type of HXC with u32arr _ _ ?a _ => replace (X + 4 * Z.of_nat (Z.to_nat n)) with a by klia end. exact HXC. }
    assert (LX' : Z.of_nat (length (ws ++ skipn (Z.to_nat n) xs)) = Z.of_nat (length xs)) by (rewrite length_app, LW, length_skipn; klia).
    assert (FX' : same_from (Z.to_nat n) (ws ++ skipn (Z.to_nat n) xs) xs).
    { intros q Hq. rewrite nth_error_app2 by (rewrite LW; klia). rewrite LW, nth_error_skipn. f_equal. klia. }
    match goal with H4 : mem_inv asegs m6, H5 : stk asegs m6 lo _, H6 : HM _ _ _ h LB LF m6, MU6 : munch _ m m6, WM6 : wmono _ m m6 |- _ =>
      pose proof (conj HX (conj LX' (conj FX' (conj MU6 (conj WM6 (conj H4 (conj H5 H6))))))) as DI end.
    eapply conv_walk with (h := h) (LB := LB) (LF := LF) (lx := Z.of_nat (length xs)); try eassumption; try klia; try (f_equal; klia).
  all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
