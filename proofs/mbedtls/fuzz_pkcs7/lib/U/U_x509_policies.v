(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AEvt HeapIface CellsX Cells Mem Step Frame Tac AStep Asn1Aux Asn1AuxA X509Aux X509AuxB MState Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts CrtFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import CrtExtStmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_oid U_asn1_get_tag.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1 LxU_SumsHeapO LxU_SumsCrt2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.
Set Printing Width 200.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P002798b859ffc405 0 4 0 1 3 1 57 1 58 1P00acbdcbbeee3cd4 2 16 1 1 8 3 1 1 54 1 55 1 5 0 1 32 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P0167dabc7c1b89b4 0 2 0 1 31 1P01b47c6c672ca8c8 0 2 0 1 5 1P01bd43e3e11f71fa 0 5 0 1 1 1 6 1 40 1 46 1P01d8ddc65b852546 0 5 0 1 25 1 26 1 48 1 49 1P01d945fac955ee9d 0 4 0 16 10 16 67 16 68 16P020599328dd72db6 0 2 0 1 14 1P022a21e08bc3fe79 2 19 0 5 0 1 3 1 22 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P023e265967b24f24 0 2 0 1 2 1P0253770ab23b4571 0 2 0 1 4 1P034477e0505026cd 1 1 8 3 0 1 43 1 46 1 4 22 1 44 1 45 1 47 8P034a142e6e4e964c 1 1 8 3 1 1 44 1 45 1 4 22 1 43 1 46 1 47 8P03d6a79569c8ed04 0 4 0 1 41 1 64 1 65 1P0518d884c2add956 0 2 0 1 7 1P05807dd0373535c2 0 2 0 1 3 1P05bc42736e263b09 1 1 8 3 0 1 43 1 46 1 4 21 2 44 2 45 2 47 16P05e9d2c0de4ad5e4 2 16 1 1 8 3 1 1 54 1 55 1 5 0 1 32 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P05f42f6904da3d2a 1 1 8 3 0 1 56 1 59 1 4 32 2 57 2 58 2 60 16P060c74830c26b803 1 1 8 3 1 1 61 1 64 1 4 40 1 62 1 63 1 65 8P06469b238b0ecbea 0 5 0 1 53 1 55 1 74 1 75 1P066e8cdd762b7771 1 1 8 3 0 1 43 1 46 1 4 22 1 44 1 45 1 47 8P068944dcd33a6792 0 4 0 1 40 1 63 1 64 1P06cadfb610dbe059 1 1 8 3 1 1 52 1 55 1 4 31 1 53 1 54 1 56 8P0704b7a18108add2 0 5 0 1 31 1 33 1 52 1 53 1P07186d11fba96762 0 5 0 1 26 1 27 1 49 1 50 1P07b3bf3e7e05a875 2 16 1 1 8 3 1 1 54 1 55 1 5 0 1 32 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P07c683b0eca6a651 0 2 0 1 3 1P07dfbd69a18d71be 1 1 8 2 50 1 61 1 3 0 1 60 1 62 8P086ba67d5458015f 0 2 0 1 22 1P088387a0be2432c3 0 5 0 1 36 1 37 1 59 1 60 1P08f563d12c622bd6 0 4 0 1 2 1 44 1 45 1P08fa64c443c0eb18 1 1 8 3 0 1 43 1 46 1 4 21 2 44 2 45 2 47 16P0956465a25998f6b 0 2 0 1 6 1P096d4494a8368d76 0 2 0 1 33 1P098f3d77fc4ac1d7 0 4 0 1 3 1 63 1 64 1P0990d8676ff8bbd9 0 4 0 16 5 16 51 16 52 16P09ad55bc7d379612 2 16 1 1 8 3 1 1 54 1 55 1 5 0 1 32 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P0a0e9ccac484203f 0 5 0 1 53 1 54 1 74 1 75 1P0a77a769fd29af12 0 5 0 1 51 1 53 1 72 1 73 1P0a8f5a4d23dafde1 0 1 1 1P0c893ccedd2315ba 0 2 0 1 5 1P0ca1efe4a911b92a 1 1 8 3 1 1 43 1 46 1 4 22 1 44 1 45 1 47 8P0cbbda542f015208 0 4 0 1 3 1 54 1 55 1P0cbf4b6f7c174902 0 2 0 1 7 1P0cca922d26e892cf 1 1 8 3 1 1 52 1 55 1 4 31 1 53 1 54 1 56 8P0d82260c39f9ac00 0 5 1 1 3 1 34 1 57 1 58 1P0da43dbfd3ea8641 0 5 0 1 28 1 29 1 49 1 50 1P0e13b6081f585bfd 0 2 0 1 1 1P0e36b9d7e25ba376 0 5 0 1 36 1 38 1 59 1 60 1P0e55d8471722352d 0 4 0 1 30 1 55 1 56 1P0e5dbe00f56c83db 1 1 8 3 0 1 43 1 46 1 4 21 2 44 2 45 2 47 16P0e6e5b84a9f9f7f9 2 37 1 1 8 3 1 1 70 1 71 1 5 0 1 46 1 69 1 72 1 73 8 1 1 8 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 8P0e8c2c5ba811e421 0 2 0 1 6 1P0eca0307a5cd872c 1 1 8 3 0 1 43 1 46 1 4 21 2 44 2 45 2 47 16P0ee018feca209dbe 1 1 8 3 0 1 62 1 65 1 4 2 1 63 1 64 1 66 8P0f79ffef3d0aa905 1 1 8 3 0 1 43 1 46 1 4 21 2 44 2 45 2 47 16P0ff488740cda1ca2 0 2 0 1 1 1P10366a2b2f16df50 0 2 0 1 42 1P103a5dd3cc1e84fb 0 2 0 1 1 1P10404d7c1024ad2e 0 2 0 1 2 1P10614db22d7b1142 0 6 0 16 20 16 42 16 43 16 44 16 45 16P106d14f1004c361a 0 7 0 1 3 1 5 1 32 1 34 1 51 1 57 1P107f3978a076357a 0 5 0 1 20 1 21 1 42 1 43 1P108785f8527bc89b 2 37 1 1 8 3 1 1 70 1 71 1 5 0 1 46 1 69 1 72 1 73 8 1 1 8 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 8P10a8aec4bf21698d 0 2 0 1 28 1P10b328270baf37de 0 4 0 1 35 1 58 1 59 1P110d43b183ef0b92 1 1 8 3 1 1 53 1 54 1 4 31 1 52 1 55 1 56 8P116e861f5a4d9414 1 1 8 3 0 1 43 1 46 1 4 22 1 44 1 45 1 47 8P11ad1fd2f5e292ae 0 4 0 1 13 1 39 1 40 1P12604eb99d21d7b6 0 4 0 1 38 1 61 1 62 1P127d7e3651c9cc7c 0 5 0 1 13 1 14 1 36 1 42 1P12e29fdb291d4485 1 1 8 3 0 1 56 1 59 1 4 33 1 57 1 58 1 60 8P136ad10a2f4a38c7 1 1 8 3 0 1 56 1 59 1 4 32 2 57 2 58 2 60 16P139548f969eb9dcd 0 2 0 1 3 1P139b918647fa3a50 0 5 0 1 28 1 30 1 49 1 50 1P13f13815975915d2 0 4 0 16 8 16 42 16 43 16P13f3d378e1e50b04 1 1 8 2 44 1 55 1 3 0 1 54 1 56 8P14010564bdee2332 1 1 8 3 0 1 43 1 46 1 4 22 1 44 1 45 1 47 8P140738c5b4a9419a 1 1 8 3 1 1 55 1 58 1 4 34 1 56 1 57 1 59 8P14127d99c68712dd 0 2 0 1 5 1P1440d88ac7150983 0 4 0 1 44 1 67 1 68 1P146d68e4b3b07733 1 1 8 3 0 1 43 1 46 1 4 21 2 44 2 45 2 47 16P14ccb1632713054c 1 1 8 2 30 1 43 1 3 0 1 42 1 44 8P14e4dbd934b9f121 0 5 1 1 2 1 21 1 44 1 45 1P150e8776a38eb6b0 2 19 0 5 0 1 3 1 22 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P15765da61de26d31 1 1 8 3 0 1 42 1 45 1 4 21 1 43 1 44 1 46 8P158506531fe6a233 0 2 0 1 48 1P15b56376626eae58 1 1 8 3 0 1 43 1 46 1 4 22 1 44 1 45 1 47 8P15c63ee864e31b10 0 4 0 1 44 1 67 1 68 1P15d8b368797d5953 0 4 0 1 3 1 45 1 46 1P162487c018e292e6 0 1 1 1P164866625285ff7b 0 2 0 1 19 1P16489add50fa8e0c 0 4 0 1 5 1 43 1 44 1P1693003f3a76a3e6 0 4 0 1 26 1 51 1 52 1P169cd43cfd4e8c53 0 5 0 1 51 1 52 1 72 1 73 1P1704cb11b6599ff9 0 2 0 1 39 1P173018486133aa06 0 5 0 1 26 1 28 1 49 1 50 1P17d8e801eafeb1af 0 4 0 1 28 1 51 1 52 1P180c9c06c5610bd9 0 2 0 1 5 1P181645ba2c1bc33b 0 2 0 1 1 1P18314d9b803b6d15 0 2 0 1 34 1P186314b06b87f96a 2 19 0 5 0 1 3 1 22 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P189582e35e8d06f3 1 1 8 3 1 1 64 1 67 1 4 43 1 65 1 66 1 68 8P18faa715d05ab247 0 8 0 1 3 1 4 1 5 1 32 1 34 1 51 1 57 1P18ffc88072cf1646 1 1 8 3 0 1 43 1 46 1 4 22 1 44 1 45 1 47 8P196414f8373ec96a 1 1 8 3 1 1 61 1 64 1 4 40 1 62 1 63 1 65 8P19c564258132ccc8 2 16 1 1 8 3 1 1 54 1 55 1 5 0 1 32 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P1a01533c45e76c6e 0 4 0 1 40 1 63 1 64 1P1a3845b9281f3603 2 37 1 1 8 3 1 1 70 1 71 1 5 0 1 46 1 69 1 72 1 73 8 1 1 8 3 2 1 69 1 72 1 4 0 1 70 1 71 1 73 8P1a72559eef473a52 2 19 1 1 8 3 1 1 54 1 55 1 5 0 1 30 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P1a95f42d8e8ecf36 0 5 0 1 31 1 32 1 52 1 53 1P1b059cbd89f0a824 0 2 0 1 1 1P1b1434402a916c36 2 19 0 5 0 1 3 1 22 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P1b64c88d89a74c42 0 2 0 1 1 1P1bca165a6f7d161b 1 2 16 2 0 1 67 1 16 2 25 1 68 1 2 69 1 70 1P1be47e228cd41ab2 0 2 0 1 5 1P1c2466d6002c145c 0 1 1 1P1c9f457682fe2c95 1 1 8 3 1 1 52 1 55 1 4 33 1 53 1 54 1 56 8P1ca7400979d2b774 0 4 0 1 41 1 64 1 65 1P1cbfaf6e53468752 0 2 0 1 20 1P1cda94b2af485e9a 0 4 0 1 30 1 55 1 56 1P1d0c27ee8f73f9fc 0 2 0 1 18 1P1d4188024b34cabf 0 5 0 1 4 1 30 1 54 1 55 1P1d65741428ee7869 0 2 0 1 18 1P1d7fb62ace879ed5 2 30 0 5 0 1 3 1 33 1 58 1 59 1 0 4 0 1 2 1 58 1 59 1P1e71a8abbebfacbd 0 7 0 1 4 1 5 1 39 1 42 1 43 1 45 1P1e8fd0ac56934427 0 6 0 1 21 1 22 1 24 1 39 1 45 1P1e92ab72e696d937 0 4 0 1 30 1 54 1 55 1P1f3bc5ecbc643738 0 10 0 1 4 1 5 1 13 1 14 1 33 1 57 1 60 1 61 1 63 1P1f49a3c2becb22da 1 1 8 3 1 1 55 1 58 1 4 34 1 56 1 57 1 59 8P1f891e11e6dbd6e6 0 4 0 1 29 1 54 1 55 1P1f896abf84f59875 0 2 0 1 5 1P1fcbf04377c59c86 1 1 8 3 1 1 56 1 57 1 4 34 1 55 1 58 1 59 8P201dc58aed4eda37 0 6 0 1 1 1 5 1 6 1 40 1 46 1P20a437ba4f5c9154 0 2 0 1 5 1P20c241f9ff0945f9 0 3 0 1 43 1 44 1P20d90086c40d521d 0 4 0 1 29 1 54 1 55 1P20daaaafafdfe094 0 5 0 1 28 1 30 1 49 1 50 1P215b455b517dd233 2 19 0 5 0 1 3 1 22 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P21a526fd44d4e292 0 3 0 1 4 1 52 1P21c824cba232c076 0 2 0 1 3 1P22713fe5a6b80f63 1 1 8 3 0 1 43 1 46 1 4 21 2 44 2 45 2 47 16P227b4c5c9bb2e85c 2 19 0 5 0 1 3 1 22 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P22be418d1f0563db 2 28 1 1 8 3 1 1 66 1 67 1 5 0 1 42 1 65 1 68 1 69 8 1 1 8 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 8P233d2660dc595fde 2 19 0 5 0 1 3 1 22 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P2361fcb284590523 2 30 0 5 0 1 3 1 33 1 58 1 59 1 0 4 0 1 2 1 58 1 59 1P239c907bd73d4d11 0 3 0 1 43 1 44 1P23cf83fa9d9974e1 1 1 8 3 1 1 54 1 55 1 5 2 1 30 1 53 1 56 1 57 8P23f7034a8ece77c6 0 5 0 1 31 1 33 1 52 1 53 1P2415142a8e0936b0 2 19 0 5 0 1 3 1 22 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P24213b8eccf610c4 0 4 0 1 44 1 67 1 68 1P24924b4dc490ddbe 0 5 0 1 31 1 32 1 52 1 53 1P249ae92e75f33f99 0 4 0 1 38 1 61 1 62 1P24b71bddefcf4be0 2 16 1 1 8 3 1 1 54 1 55 1 5 0 1 32 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P24be0845535494ae 0 4 0 1 40 1 63 1 64 1P24d6d9775e5035a4 0 2 0 1 6 1P2516b43e70981ef8 0 2 0 1 18 1P253aaa8830d8769c 0 4 0 1 26 1 51 1 52 1P25445db675d1d70b 1 1 8 3 1 1 62 1 63 1 4 40 1 61 1 64 1 65 8P254dea77b9cf68c6 2 16 1 1 8 3 1 1 54 1 55 1 5 0 1 32 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P255e874f69a3e879 0 4 0 1 41 1 64 1 65 1P25654f35e6d02614 1 1 8 3 0 1 56 1 59 1 4 33 1 57 1 58 1 60 8P259d16cefc710083 0 5 1 1 3 1 40 1 63 1 64 1P25e67865d15402f1 0 4 0 1 29 1 54 1 55 1P26dd6cfba79c63cb 0 5 1 1 2 1 30 1 53 1 54 1P2798da56bc19d24d 0 2 0 1 43 1P27ac94143d0cced6 1 1 8 3 0 1 43 1 46 1 4 21 2 44 2 45 2 47 16P27cdc4bbd7cfe78e 0 2 0 1 7 1P2807868d3dfa1544 0 4 0 1 23 1 25 1 48 1P28238352d6224974 2 19 0 5 0 1 3 1 22 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P28cde7e0fac1a87a 2 16 1 1 8 3 1 1 54 1 55 1 5 0 1 32 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P28eb2c0854c35150 0 2 0 1 1 1P2963d59d0f97dd57 2 19 1 1 8 3 1 1 54 1 55 1 5 0 1 30 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P29a75605d10e6f84 0 2 0 1 5 1P29ab346e403aa4e2 1 1 8 3 0 1 43 1 46 1 4 21 2 44 2 45 2 47 16P2a2b8836d074749b 0 5 0 1 35 1 36 1 58 1 59 1P2a8b19bfe648b082 0 2 0 1 5 1P2ada121b15619b47 0 2 0 1 5 1P2af8522be00f57c3 1 1 16 2 25 1 68 1 3 0 1 67 1 69 16P2b8cafa4e80ee625 0 4 0 16 5 16 54 16 55 16P2bb80f7c60099926 1 1 8 3 0 1 43 1 46 1 4 21 2 44 2 45 2 47 16P2c02fead55df7ce9 0 2 0 1 1 1P2c1496cb2ac4d975 0 4 0 1 38 1 61 1 62 1P2c34fe5bec79435a 0 5 0 1 1 1 6 1 40 1 46 1P2c6a2f95a6e1e46f 0 5 1 1 3 1 22 1 45 1 46 1P2ccac81b6cadedc2 0 2 0 1 45 1P2cf391169cfe47d8 0 6 0 1 1 1 5 1 6 1 40 1 46 1P2d36817b3e291a8b 1 1 8 3 0 1 53 1 56 1 4 2 1 54 1 55 1 57 8P2d394c840fa3e7ff 0 2 0 1 51 1P2d890d99cd24a6eb 0 2 0 1 3 1P2daaae28142fee84 1 1 8 3 1 1 61 1 64 1 4 40 1 62 1 63 1 65 8P2e08d78180394ee2 0 2 0 1 17 1P2e5f515a349fb11d 2 19 0 5 0 1 3 1 22 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P2f273b37c916f455 0 2 0 1 4 1P2f473fed9d190ad8 0 2 0 1 32 1P2f550cce18b8ee05 0 2 0 1 1 1P2f6e9df8876c7303 0 5 1 1 3 1 31 1 54 1 55 1P2f8a7cbdcd4be251 0 2 0 1 5 1P2fa1e19d8baab615 1 1 8 3 0 1 43 1 46 1 4 21 2 44 2 45 2 47 16P2fbd423522ebef9d 2 19 0 5 0 1 3 1 22 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P300583af495a9f41 0 4 0 1 2 1 53 1 54 1P3028e7178fce3035 0 3 0 1 15 1 45 1P3059d7664ef31c7d 0 2 0 1 1 1P3072655d47629b85 0 2 0 1 1 1P30e1ab44031c99ec 0 8 0 1 3 1 4 1 5 1 32 1 34 1 51 1 57 1P30e7a44b498129fc 0 2 0 1 5 1P3135b2b831d575d6 2 28 1 1 8 3 1 1 66 1 67 1 5 0 1 42 1 65 1 68 1 69 8 1 1 8 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 8P313db376bfbaec00 0 4 0 1 5 1 43 1 44 1P316b297e39f9c0a5 1 1 8 3 1 1 55 1 58 1 4 34 1 56 1 57 1 59 8P318b503f5038c786 2 16 1 1 8 3 1 1 54 1 55 1 5 0 1 32 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P31965f8bfbd756ec 0 4 0 16 14 16 60 16 61 16P31c3a32f3d90a369 0 5 0 1 4 1 30 1 54 1 55 1P32a8037e569f3019 2 19 0 5 0 1 3 1 22 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1P32acb2459b6c8a5e 0 4 0 1 20 1 42 1 43 1P337787df5c59ec96 0 4 0 1 28 1 51 1 52 1P3395fd101c31e2ae 1 1 8 3 0 1 43 1 46 1 4 22 1 44 1 45 1 47 8P339ab2e2180ccf22 0 2 0 1 6 1P339c4e506a319b91 0 5 1 1 2 1 33 1 56 1 57 1P33fb02a5dd78b32c 1 1 8 3 0 1 43 1 46 1 4 22 1 44 1 45 1 47 8P340625e8b1d76cd0 0 3 0 1 39 1 40 1P341e8549ef5a84d0 0 1 1 1P345437fa4f5df431 0 2 0 1 17 1P3455a3545cf654bd 0 4 0 1 28 1 51 1 52 1P346497d03ccd47fb 0 5 0 1 22 1 24 1 39 1 45 1P34c5b70c266e4557 1 1 8 3 1 1 64 1 67 1 4 43 1 65 1 66 1 68 8P34f1f8cb247431e0 0 5 0 1 28 1 29 1 49 1 50 1P3539584e9d291e7b 1 1 8 3 0 1 43 1 46 1 4 21 2 44 2 45 2 47 16P360f83be5fd644c6 0 2 0 1 1 1P364c1c3b471f29b3 1 1 8 3 1 1 43 1 46 1 4 22 1 44 1 45 1 47 8P369a853253a7cf9f 0 5 0 1 35 1 37 1 58 1 59 1P36bf5102be7ca265 0 4 0 1 5 1 24 1 54 1P37822564d2749b6a 1 1 8 3 1 1 63 1 64 1 5 2 1 39 1 62 1 65 1 66 8P37b227cfe8c17c95 2 28 1 1 8 3 1 1 66 1 67 1 5 0 1 42 1 65 1 68 1 69 8 1 1 8 3 2 1 65 1 68 1 4 0 1 66 1 67 1 69 8P3815b9063372455d 1 1 8 3 0 1 43 1 46 1 4 22 1 44 1 45 1 47 8P382a48ab3b35779c 0 2 0 1 42 1P382c775604ab3fe4 1 1 8 3 0 1 56 1 59 1 4 2 1 57 1 58 1 60 8P3867d45312e0ae1c 1 1 8 3 1 1 43 1 46 1 4 22 1 44 1 45 1 47 8P38737c22517fa962 1 1 8 3 0 1 43 1 46 1 4 21 2 44 2 45 2 47 16P388bd5dce5c2daa8 0 4 0 1 35 1 58 1 59 1P38e19d6bc22f7146 1 1 8 3 0 1 43 1 46 1 4 22 1 44 1 45 1 47 8P390f60352aa4e820 0 2 0 1 5 1P3930f8dd43da84d0 0 4 0 1 30 1 54 1 55 1P399916148a304606 0 4 0 1 2 1 56 1 57 1P39d593458b2a465c 0 2 0 1 7 1P3a0d67f26a07e7ed 0 4 0 1 26 1 51 1 52 1P3b0d6a8add8bfab2 0 4 0 1 14 1 36 1 42 1P3b37955089e4009e 1 1 8 3 1 1 57 1 58 1 5 2 1 33 1 56 1 59 1 60 8P3b6bc480406b2fda 0 5 1 1 2 1 39 1 62 1 63 1P3bf2cdb7f2748ea1 0 5 0 1 25 1 27 1 48 1 49 1P3c0c0e3dbdd27778 0 4 0 1 2 1 62 1 63 1P3c366e75962f9f59 1 1 8 3 0 1 43 1 46 1 4 22 1 44 1 45 1 47 8P3c7a90e75f62db0c 0 4 0 1 30 1 55 1 56 1P3da11e75e4a6c939 0 3 0 1 21 1 46 1P3da584f652c2e2e7 1 1 8 2 41 1 52 1 3 0 1 51 1 53 8P3db5e1a65f7e5708 1 1 8 3 1 1 52 1 55 1 4 33 1 53 1 54 1 56 8P3e0546f6aee17f43 1 1 8 3 0 1 43 1 46 1 4 22 1 44 1 45 1 47 8P3e26721a1bc4dc17 1 1 8 3 0 1 43 1 46 1 4 22 1 44 1 45 1 47 8P3e6d1fef1d88073d 0 2 0 1 5 1P3ea5e3bbbba92bb2 2 19 1 1 8 3 1 1 54 1 55 1 5 0 1 30 1 53 1 56 1 57 8 1 1 8 3 2 1 53 1 56 1 4 0 1 54 1 55 1 57 8P3ea6b28b780186eb 0 2 0 1 3 1P3ea832807e50eaa0 1 1 8 3 1 1 52 1 55 1 4 33 1 53 1 54 1 56 8P3eb1d345767e9404 1 1 8 3 1 1 64 1 67 1 4 43 1 65 1 66 1 68 8P3ef48c89b96079c8 0 4 0 1 35 1 58 1 59 1P3effd87cf989e27c 1 1 8 3 1 1 52 1 55 1 4 31 1 53 1 54 1 56 8P3f17593d28a6d11b 0 7 0 1 3 1 5 1 32 1 34 1 51 1 57 1P3f586509fef7664a 1 1 8 3 0 1 43 1 46 1 4 21 2 44 2 45 2 47 16P3fdb19c6dbb4879f 2 19 0 5 0 1 3 1 22 1 45 1 46 1 0 4 0 1 2 1 45 1 46 1N00065f9b35eca788N009a0248ccfc9f13N00b044f5fa08d06dN00b851c6ae608b98N00bc167fef024918N01215d3638e91f8bN013a00f5e8e38c0cN01446b9b9e5e0e60N0169f652367cd8aeN016eaadbf896cc70N0172e8ed67f3a3d5N01a5b8932b379ff5N01bbfcbdc6610e4cN023838ae00a1ee27N0258da066509004fN0264275f53559a97N0282528684a65c61N02890387ea082673N028b2ce128836de7N02ad0a5809bb3b46N03052ffd93766828N0341065a4394cf58N0341a37fbda4f6adN034e3a51ed9f3dd5N0362df26ba0a6f76N03d873313a13caf2N04250132e4316ecaN046086f5a9b12b4cN046397312ce399edN0483137fe8144a36N04b20e42c1ac6b5fN04b337f25537cc87N04bc620231487203N04fe9fd2c8136c32N0514c31b104671b4N051e606b7d86a44aN053070109e6efbdcN057c8aea54503d42N0581127167334b8aN05d752013f3d5405N05fd499d0e019584N06060ce9870cd625N0649d558804e0af1N066bf360a67ca63eN06b401e15ae07709N06b89b1b2b5ac638N06ba0c361fcb900cN06bbd8e293dcf0baN06e08158a3394c25N06fcff95118d77dfN072ddf8c80ab7a22N0732e4eafc6515beN0735b7b1113d35e8N077a0a0e3ada3823N07a84be0c1f6229eN07ce335d14e8165cN07f3393510b40feaN07fabc394b0b4760N082842b0a19bdd06N0868cb3616b6dfdfN08887f0e2a62ce0dN08aa8db011777852N094a838181382bacN096932f45682d4a7N09796d0d878888bdN09a26df45ce4f828N09b6b9e06f5c885fN09b8b98ff204afabN09c3d73698039960N09f9d3badeef37a3N0a0503b34b29d6b0N0a5c315cf99a3ce5N0a790ef826b1ee69N0aadaa9a7a8b28d7N0ab692d25ed2798bN0ae8baaad9fa5acbN0b05a3148d1afd90N0b3b0bb32725ad60N0b41b6d686def435N0b4d3939cfe5c07aN0b71a60c2cec5862N0b8e32c6fd1de8cdN0bb8240a19de083fN0bc54205bd3cb1c5N0bed5c4a9eeb8975N0c0aaea298a1effbN0c19e540467bf625N0c283f39e7ea3751N0c5c4d36b4336a72N0c908751b6919756N0cac9cb137b9c6c7N0cb153c9b7615acaN0cc6dea00c0e2fd7N0cde1d6c3921c8ecN0ce5cc47812a55f7N0d1bafc7d71ecb0dN0d45f8cc781aa199N0d4c7cb80de07f54N0d90771f1fd1a08bN0de097249d53328aN0e66c15f96d43a5bN0e6e4990405a6b4dN0e93b937012fa21fN0eaabe208aa230b0N0eef2995062eda9fN0f1ece19bab60435N0f2572fa450a564fN0f3af8f113cf9ef3N0f4058669c9bef49N0f4e2c274dcd7871N0fb874a1f86b56c0N10223852f36a1282N102386b71a523741N10387509b148446dN103d41f80e545ae1N105add56d0c3352aN1067a74e06b9757dN10dad2e8007b4ed2N10dcc8a6b61445a6N110c608815909789N110efc911d942c05N1111e896f54a19f8N1156386a1e44ef06N117394cf917bdef2N118183efa3b02b59N11ccb0dad87fd206N11d139b0bbaca3e0N11ff5096853fed0bN12258b7a731b7d11N123287c1e7c67152N124b436a2d035ef9N12570feb304c77aaN1261ed2aed26ebc8N129d89a09df44d6aN12aa08ad0ca2c30cN12cfd09dbd613aa3N12d4d82cd27b9470N1317b4e479465495N134ce48f95e986c2N137a6161568a424eN13aa08284e41aa50N13c6d632785d27d1N13f247908208bafcN144dc80e5603b910N144df9ee3170e7dbN145bc8d62f6e86f1N149588f2b1f79ad6N151273b4782fb09cN1514b9f41f6a813cN152a1ec117363065N15667a5c0a18c570N15681697be07a255N1587725455f5c75fN1588949b6738e890N159333b42e3224e2N15a0030e327e0e5eN15c4fe75bd41ad96N15d5ce0ccb4ec9daN15d88433ced71c34N15e51c01a2585236N1616a0eeed70d67eN167cb0f96dbe41b8N16dabd23bf26d2a8N16f8c7a6652eebc7N1747627f46727e84N175d4826ce71cb7dN17725d36dbbb1ba9N17f7f335bdc919deN18506ee99d3c29f1N189b796d69de7769N18bff6612fc27494N1904a3711f2f41c4N19070b509d51fd8cN19732415073a3364N19969e70775b551fN19ec535feded6574N1a65d5b96eff60dbN1aa947fd51f92ab4N1ad03a63ef7332aaN1ada144eb0f29993N1b38e76a3e416990N1b5a86a9c64ace3fN1b6f7e0ebddfc76fN1b7c4e2cff80b7c2N1ba312ff9d800846N1baee118c36edf66N1bf73cc6dbc9a25dN1c0471118c4e1d6fN1c33245306474555N1c564c2f96e5faf7N1c5b098a328a5f72N1c6823f350c08e0eN1c998fc4e6c35785N1ca2c632159687b7N1cc0aaa86ce40c00N1cc237ae763f05cbN1d601efae364bcc3N1d8b97443cb39310N1da11834e9ba7364N1e0c419c5f809dbeN1e55738c95abf0e5N1e7c147d3695c821N1ec5baa873ba589bN1ec93e7156ef233fN1f353d23894ed25aN1f47748af9094580N1f707235b46614eaN1f7fb3450af7bb4eN1fcbdd5232813533N1fe7a00ee1103f89N1feb87117727d36cN2015d334bb9933cfN20284f673dded6c5N203a8de3731bd937N206d779ca4e30b38N20956d1cb00f68e0N20be373d3ec1a677N210a5bc6a78b3507N210fa6ae771498deN2121d7f52ef8f08bN2188c14afe65ee76N22074d4be11680f9N222d105db43f9f64N2232cc5f450c1368N2255a6cb1c6a6dabN226b8b5d1e811b8fN22c3c0a6b061c1efN22de511f55880009N2306fcaaf5a632d5N235726327010adafN23789510251e6522N23dac5e05161e934N23de48e03a2d764bN23e34303af5e83baN246c401445349774N24a6bea9d5a9418eN24da5da6d9b362b2N24f2fd435ee0e8cbN256300857a989a9cN2569d4015dd05798N256e721f3f2bea82N25ad0c751d99e4bbN25d52aaf60b9ae7fN2608b7a23d5024b8N260a0194c2863234N260e7be7a6f60353N261bfad0dea56176N262499a10b3ca01bN264df35051f67347N26b8c623f8876ac4N26ddb4f9f4134d20N26ffbb126b2aa7b8N2778880f6349ac21N27b098ece6345cfaN27de95cf2977a5c1N27fb3c13ff9e815bN281d0a04e096dd13N28236dcdb74619d6N28361fd0fdd05dc2N28788107af358974N287e2225347aee6fN28da1ffa004afae8N28e5f0c04a416361N29205b79250f0a54N292a68c7cd82becdN294bd073017fcb40N29b017a6c55f6ec4N29bda865459cbfeeN29bdb7dcb4061140N29c5bf0139ca13b8N29faba0ce1340659N2a187e40c9d58033N2a49fbb8d8afd59dN2a72f27cb4ad8e45N2a8dc14bc5e4d3faN2a8ef04bf92ce8aaN2aa34268e081990aN2acded5cf9dcf164N2ad05d9c503f0749N2b186d02d352d2adN2b212f674b770a4eN2b2ad53dbddbb551N2b41114139d2e9caN2bc717876a06fbadN2c1f00920f2192fbN2c6fda5bc25a8e80N2c9256653cebea01N2cd6e320a8c7576aN2d120f6266a9bebdN2d6d26cd6993739dN2d70005952dcbb7cN2d790b53b81d423eN2d892c5a73dcd748N2da8464307ebe251N2dc03a062e3286b9N2dc58283b69d7896N2dd2d7f4e53bbf3dN2e3faf13ca6062b0N2e678f750cf2205aN2e8337a29dd0a170N2e932ccabcce2520N2e96be7074e6825fN2ea543354140c807N2eb38954c7b48d38N2f3c73b2d2058c20N2f43429eb5e7a2a0N2f5989827a7c58c6N2fb5c41e55b883f0N2fb5fa33789f53ceN2fb9b6eb07610eabN2fbe361b553698d2N2fe48ae2c7e78b3fN30278af2bde05cd8N3116a6442b1b2433N312f7661cce55d6fN31373dff5073b9dbN314455e5411aef7aN3156682a9eafe5fbN31a7ed2acc92b520N31bcca915c1d8fd0N31e124f073defb98N3238469ed83d2bc2N32bf71cc3aeb6fb0N32cabc084c77e32bN32e51a1f0c4916d5N32e6c1e1d01c84b4N32f96b94cc23d1c9N3304a768a3593ad7N33672b6f178f0a05N3371b8bc2690af35N33d9155be15b2260N33e80f11580d54d4N33ffcbbaf97f8b86N342c18f329a183d9N3435044bd62cf75aN346e35f014eff2b0N34823856cb34ddd9N34948502f28bbe21N34b8797f19ad21f3N34bfaa976a880ec7N34e89a58a890af3eN3573c3a962ab1bc8N35a3bff11390d438N35b87b5fe485ce33N35e4018a64d79278N36bcac836da148abN36fc9ae37dd444c3N3702d081889e74c5N379184da7100d6f0N37a16577bc54cf4eN37a78fb1fc95705eN37a9884262446e4fN37f893819f5c0bfdN37fbd36099076249N383462811fca81c7N38434d5b28a21613N385d5cee7e81aa5fN387eb9b72cad7a92N38edf27e7c94cc65N38ef17e094bbc339N3926e6a5b7bdd06bN395953687795c58aN397a0d0a3d8128aeN3988a03f88083aaeN39d98467cfaa9cb8N39e5a6ad9ba419f9N3a8dc83e8cb6dd56N3aa4d953640bb53bN3abc14b0e420e6a1N3ac7a5b97bf48672N3acfaf3f47c85eb4N3b303382f308d6c3N3b436747780f5001N3b5c769a3dc64706N3b70c73258dd4fcdN3b7de938c25df39eN3bab543ff73400c3N3c3b41c3a413a8caN3cc0bd59f9521c92N3cf1353cb509ad55N3d00f859a035e2daN3d0e7c9f4ee1b984N3d3f03935bacd860N3d71c82618cc4434N3d7261dc9e53c2eaN3d9d09ae3c8eaa04N3de8cd7f8426affcN3e2c10940edbda3dN3e418eea96e8dd01N3e4281535bac070eN3e4508f523333450N3e6768ac47a57ca1N3e88d4841cc7f66bN3e8f5b27bc893771N3ed11c5793585137N3ed61a09046a033eN3ede67c7f244b9e9N3eefc57b38040c7cN3f11f0a032f49883N3f4815fa04f5bc51N3f4e50b4c3be5624N3f5dc5486aec1c6aN3f7a5072039c8d89N3f89db44841637edN3f909dd9a9c26915N3f932b2b9d7b01d2N3f9cccc61f11b78aN3fc47a67104c4d00N3fe1da3a237580e6N3ff5d38172780e86"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_x509_policies () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.bv_swrap"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.land"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.last"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "Stdlib.Lists.List.hd"; "Walk.Body.nfresh"; "Walk.Body.curF"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Walk.Body.nLBof"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Walk.Body.W"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_waddr"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.cons"; "Stdlib.Lists.List.NoDup"; "Stdlib.Lists.List.removelast"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_lseg"; "Walk.Body.headrep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Walk.Body.curR"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.USpec.CrtExtStmts.x509_policies_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Walk.Body.Loop.HREGS"].

Definition U_X509_POLICIES : Z := 0x27518.
Definition U_CALLOC : Z := 0x3f960.
Definition U_BCMP : Z := 0x46940.
Definition U_OID_ANY_POLICY : Z := 0x10b9c.

Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L11608498963.4L29012259966.4L33972362522.4L35495549846.3L59315336847.400000300;00C00D00LS1rS1r2Hr1lS1r2Hr1lSS1r2Hr1H". (* [comment removed for export] *)
Lemma land64_zero : forall r, -2^63 <= r < 2^63 -> Z.land r 18446744073709551615 = 0 -> r = 0.
Proof.
  intros r Hr H. change 18446744073709551615 with (Z.ones 64) in H. rewrite Z.land_ones in H by lia.
  destruct (Z_lt_le_dec r 0); [| rewrite Z.mod_small in H by lia; exact H].
  exfalso. rewrite <- (Z.mod_add r 1) in H by lia. rewrite Z.mod_small in H by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma land64_nonzero : forall r, -2^63 <= r < 2^63 -> Z.land r 18446744073709551615 <> 0 -> r <> 0.
Proof. intros r Hr H ->. apply H. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L13196062947.4L18932449448.4L59315336847.4L67179409831.400000800;00C00KS1r2Hr1lS1rS1r2Hr1HS1r2Hr1l". (* [comment removed for export] *)
Lemma mod64_zero : forall r, -2^63 <= r < 2^63 -> r mod 18446744073709551616 = 0 -> r = 0.
Proof.
  intros r Hr H. destruct (Z_lt_le_dec r 0); [| rewrite Z.mod_small in H by lia; exact H].
  exfalso. rewrite <- (Z.mod_add r 1) in H by lia. rewrite Z.mod_small in H by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma mod64_nonzero : forall r, -2^63 <= r < 2^63 -> r mod 18446744073709551616 <> 0 -> r <> 0.
Proof. intros r Hr H ->. apply H. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L35497643387.4L43090583504.4L58031153122.400000100700=SS1r2HrS1c2Hc". (* [comment removed for export] *)
Lemma swrap32_land_errsum : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pr,$0.Pc,$0.P,(1.(2.-10000.R2.)(3.R2.=))P,(1.(3.(4.(5.+2.+40.)+10000.)R2.)(2.R2.(5.+2.+40.)))(6.$0.(7.&20.(8.(9.R4.+????????????????.)R3.))(8.R4.(4.R3.(5.+2.+40.))))")
(* [comment removed for export] *).
Proof.
  intros r c Hr Hc. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply swrap32_errsum; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma removelast_last_app : forall (l : list Z) d, l <> [] -> removelast l ++ [last l d] = l.
Proof. intros l d H. symmetry. apply app_removelast_last. exact H. Qed.
Lemma hd_app_ne : forall (l l' : list Z) d, l <> [] -> hd d (l ++ l') = hd d l.
Proof. intros [|x l] l' d H; [exfalso; exact (H eq_refl)| reflexivity]. Qed.
Lemma in_removelast : forall (l : list Z) x, In x (removelast l) -> In x l.
Proof.
  intros l x H. destruct l as [|a r]; [exact H|].
  rewrite <- (removelast_last_app (a :: r) 0) by congruence. apply in_or_app. left. exact H.
Qed.

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.

  Section Body.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
              (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (PP CUR P END BUF lo : Z) (bs : list byte)
              (ct cpad : word).
    Hypothesis HH : HEAP usegs L HI h LB m mo.
    Hypothesis HPP : rw_cells usegs m PP [C8 (Z_to_bv 64 P)].
    Hypothesis HCR : rw_cells usegs m CUR (seq_cells ct cpad 0 0 0).
    Hypothesis BY : bytes_at usegs m BUF bs.
    Hypothesis B1 : BUF <= P.  Hypothesis B2 : P <= END.  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
    Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
    Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
    Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
    Hypothesis D3 : CUR + 32 <= BUF \/ BUF + Z.of_nat (length bs) <= CUR.
    Hypothesis AL1 : PP mod 8 = 0. Hypothesis AL2 : CUR mod 8 = 0.
    Hypothesis NZ1 : 0 < PP. Hypothesis NZ2 : 0 < CUR. Hypothesis NZ3 : 0 < BUF.
    Hypothesis ST : stk usegs m lo (bv_unsigned sp).
    Hypothesis SLO : lo <= bv_unsigned sp - X509_POLICIES_STACK - hl_stack L.
    Hypothesis CEIL : alloc_ceiling <= lo.
    Hypothesis SPTOP : bv_unsigned sp <= heap_top usegs L HI h.
    Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
    Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
    Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L. Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.
    Hypothesis SPP : bv_unsigned sp <= PP. Hypothesis SCUR : bv_unsigned sp <= CUR.
    Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
    Hypothesis DS2 : CUR + 32 <= lo \/ bv_unsigned sp <= CUR.
    Hypothesis DS3 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
    Hypothesis CW1 : client_wrange L LB lo (heap_top usegs L HI h) PP 8.
    Hypothesis CW2 : client_wrange L LB lo (heap_top usegs L HI h) CUR 32.
    Hypothesis CRB : client_range L LB lo BUF (Z.of_nat (length bs)).
    Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
    Hypothesis MI : mem_inv usegs m.
    Hypothesis SPR : 0 <= bv_unsigned sp < 2 ^ 64.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L56995406082.7000001HS1L3HLS2sp2PP3CUR1P3END3BUF2lo2bs2B12B22B32D12D22D33NZ13NZ23SLO3SPP4SCUR3DS13DS23DS33SPR". (* [comment removed for export] *)
    Let LOSP : lo <= bv_unsigned sp + -128. Proof. unfold X509_POLICIES_STACK in SLO. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L3517659205.7100000GS1L2sp2PP3CUR2lo2bs3SLO". (* [comment removed for export] *)
    Let SLO2 : lo <= bv_unsigned sp + -128 - hl_stack L. Proof. unfold X509_POLICIES_STACK in SLO. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L12990621327.7300000DS2sp2PP3CUR2bs3NZ11B". (* [comment removed for export] *)
    Let PPB : 0 <= PP /\ PP + 8 <= 2 ^ 64.
    Proof. pose proof (rw_cells_bound usegs m PP _ HPP) as B. cbn [cells_size csize Nat.add] in B. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L62948604328.7400000@S2sp2PP3CUR2bs1B". (* [comment removed for export] *)
    Let CURB : CUR + 32 <= 2 ^ 64.
    Proof. pose proof (rw_cells_bound usegs m CUR _ HCR) as B. unfold seq_cells in B. cbn [cells_size csize Nat.add app] in B. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L25157604214.7500000BS1L2sp2PP3CUR2bs1H". (* [comment removed for export] *)
    Let ACP : 4096 < alloc_ceiling. Proof. pose proof alloc_ceiling_pos. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Let BRL : Forall (fun b => block_range L (fst b) (snd b)) LB. Proof. exact (proj1 (heap_blocks usegs L HI _ _ _ _ HH)). Qed.

    Notation POST := (x509_policies_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END BUF lo m mo).
    Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -128)).
    Notation X0 := [(PP, PP + 8); (CUR, CUR + 32)].
    Notation SAVED := ([C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

    (* [comment removed for export] *)
    Definition nLBof (nodes : list Z) : list blk := map (fun a => (a, 32)) (rev nodes) ++ LB.
    Definition nfresh (nodes : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Px,$0.P,(:.$0.R1.O1.)(1.(3.(8.R2.+20.)(;.VL,))(1.(<.(3.(8.R2.+20.)(=.VL,))(3.(>.VL,)R2.))PB,$0.Pk,$0.P,(:.(?.$0.$0.)(10.$0.$0.R2.R1.)VLB,)(<.(3.(8.R5.+20.)R3.)(3.(8.R3.R2.)R5.))))")
(* [comment removed for export] *).
    Definition W (cur : Z) : list ivl := [(PP, PP + 8); (cur, cur + 32); (bv_unsigned sp - 128, bv_unsigned sp)].
    Definition curF (nodes : list Z) (cur : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "(1.(6.$0.(11.O1.+8.)=)(1.(2.=O1.)(1.(3.(8.O1.+20.)(5.+2.+40.))(1.(<.(3.(8.VPP,+8.)O1.)(3.(8.O1.+20.)VPP,))(1.(<.(3.(8.O1.+20.)VBUF,)(3.(8.VBUF,(12.(13.(14.&8.)Vbs,)))O1.))(1.(<.(3.(8.O1.+20.)Vlo,)(3.(15.&40.Vsp,)O1.))(<.(1.(6.(16.$0.)O2.(17.$0.))(6.$0.O1.VCUR,))(1.(18.(6.(16.$0.)O2.(17.$0.)))(1.(6.$0.O1.(19.$0.O2.=))(1.(6.$0.(11.O1.+10.)=)(<.(3.(8.O1.+20.)VCUR,)(3.(8.VCUR,+20.)O1.))))))))))))")
(* [comment removed for export] *).
    Definition headrep (mm : mem) (nodes : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "(<.(6.(16.$0.)O1.(17.$0.))(1:.(14.&40.)Lt,(14.&40.)(1:.(14.&40.)Lpd,(14.&40.)(1:.$0.Ll,$0.(1:.$0.Lp,$0.(1.(1;.$1<.O2.VCUR,(1=.R4.R3.R2.R1.(1>.$0.=O1.)))(1.(3.VBUF,R1.)(1.(3.=R2.)(3.(8.R1.R2.)VEND,)))))))))")
(* [comment removed for export] *).

    Lemma nLBof_snoc : forall nodes N, nLBof (nodes ++ [N]) = (N, 32) :: nLBof nodes.
    Proof. intros. unfold nLBof. rewrite rev_app_distr. reflexivity. Qed.
    Lemma nLBof_sub : forall nodes b, In b LB -> In b (nLBof nodes).
    Proof. intros. unfold nLBof. apply in_or_app. right. assumption. Qed.
    Lemma nLBof_in : forall nodes x, In x nodes -> In (x, 32) (nLBof nodes).
    Proof. intros. unfold nLBof. apply in_or_app. left. apply in_map_iff. exists x. split; [reflexivity|]. rewrite <- in_rev. exact H. Qed.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L6662040476.8200001OS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B22B32D12D22D33NZ13NZ23SPP4SCUR3DS13DS23DS33SPR4LOSP1a1b2Hr2Hc". (* [comment removed for export] *)
    Lemma in_block_below : forall a, in_block LB a -> a < alloc_ceiling.
    Proof. intros a (b & Hb & Hr). pose proof BRL as BR. rewrite Forall_forall in BR. flat constr:((BR b Hb)) 5%nat. intros _ _ _ Hc _. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L15310374719.8500001OS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B22B32D12D22D33NZ13NZ23SPP4SCUR3DS13DS23SPR4LOSP5nodes2A21H2H0". (* [comment removed for export] *)
    Lemma cur_cases : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pnodes,(16.$0.)Pcur,$0.P,(1?.R2.)P,(20.R3.R2.)(<.(6.$0.R3.VCUR,)(1.(:.$0.R3.R4.)(1.(3.(8.R3.+20.)(;.VL,))(1.(<.(3.(8.R3.+20.)(21.VL,))(3.(22.VL,)R3.))PB,$0.Pk,$0.P,(:.(?.$0.$0.)(10.$0.$0.R2.R1.)VLB,)(<.(3.(8.R6.+20.)R3.)(3.(8.R3.R2.)R6.))))))")
(* [comment removed for export] *).
    Proof.
      intros nodes cur HFR (_ & _ & _ & _ & _ & _ & [[_ ->]|(Hne & -> & _ & _)]); [left; reflexivity| right].
      assert (HIN : In (last nodes 0) nodes).
      { rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity. }
      flat constr:((HFR _ HIN)) 3%nat. intros A1 A2 A3. pose proof DIM1. pose proof DIM2. split; [exact HIN|]. split; [exact A1|]. split; [lia| exact A3].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L34477300571.91L34479285344.93L44370725769.90L54391870717.9100000N00e01802VS2sp2PP3CUR2bs3cur1a3Hin2O12O3S2sp2PP3CUR2bs3cur1a2HAS2sp2PP3CUR2bs1a2O1S1L2HI2sp1h2PP3CUR1P3END3BUF2lo2bs2B12B22B32D12D22D33NZ13NZ23SPP4SCUR3DS13DS23SPR1a1H2H02O12O3". (* [comment removed for export] *)
    Lemma W_client : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pnodes,(16.$0.)Pcur,$0.PLBx,(16.$23.)Phc,(24.$1<.VL,VHI,)Pa,$0.P,(1?.R5.)P,(20.R6.R5.)P,Pb,$23.P,(:.$23.R1.(25.R8.))(:.$23.R2.R7.)P,(6.$0.(26.$1<.VL,VHI,R5.)(26.$1<.VL,VHI,Vh,))P,(18.(27.(28.R8.)R5.))(29.VL,R8.Vlo,(26.$1<.VL,VHI,R7.)R6.)")
(* [comment removed for export] *).
    Proof.
      intros nodes cur LBx hc a HFR HCF HS HT Hin. cbn [outside W] in Hin. rewrite HT. pose proof LOSP. pose proof SPTOP.
      assert (HS' : forall b, In b LB -> In b LBx) by (intros b Hb; apply HS; apply nLBof_sub; exact Hb).
      destruct (outside_dec [(PP, PP + 8)] a) as [O1|O1]; cbn [outside] in O1.
      2:{ exact (client_wrange_mono L _ _ _ _ _ _ CW1 HS' a ltac:(lia)). }
      destruct (outside_dec [(bv_unsigned sp - 128, bv_unsigned sp)] a) as [O3|O3]; cbn [outside] in O3.
      2:{ left. lia. }
      assert (HA : cur <= a < cur + 32) by lia.
      destruct (cur_cases nodes cur HFR HCF) as [->|(HIN & _)].
      - exact (client_wrange_mono L _ _ _ _ _ _ CW2 HS' a HA).
      - right. right. exists (cur, 32). split; [apply HS; apply nLBof_in; exact HIN| cbn; lia].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Lemma heap_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pnodes,(16.$0.)Pcur,$0.Phc,(24.$1<.VL,VHI,)PLBx,(16.$23.)Pmm,P,(14.&40.)(2:.(14.&8.))Pm1,P,(14.&40.)(2:.(14.&8.))Pmoc,$2;.P,(1?.R7.)P,(20.R8.R7.)P,(2<.$1<.VL,VHI,R7.R6.R5.R3.)P,(6.$0.(26.$1<.VL,VHI,R8.)(26.$1<.VL,VHI,Vh,))P,Pb,$23.P,(:.$23.R1.(25.R<.))(:.$23.R2.R:.)P,(2=.(28.R;.)R8.R7.)P,(2>.$1<.R9.R8.)(2<.$1<.VL,VHI,R<.R;.R9.R8.)")
(* [comment removed for export] *).
    Proof.
      intros nodes cur hc LBx mm m1 moc HFR HCF HHx HT HS MU WM.
      eapply HEAP_munch; [exact HHx| exact CEIL| exact MU| exact WM|].
      intros a Ha Hin. eapply W_client; eassumption.
    Qed.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L2150165764.102 L28571787284.98 L28573882931.103L28573883312.94 L28573890933.93 00000G02103`05:06YS2sp2PP3CUR2bs1a1B1j2HrS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B22B32D12D22D33NZ13NZ23SPP4SCUR3DS13DS23SPR3cur1H2H01a2Hs2Ho3HCc2H12Hd2HDS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B22B32D12D22D33NZ13NZ23SPP4SCUR3DS13DS23DS33SPR3cur1H2H01a2Ho3HCc1B1j2Hr2H42H5S1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B22B32D12D22D33NZ13NZ23SPP4SCUR3DS13DS23DS33SPR1H2H01a2H4S2sp2PP3CUR2bs1a2Hs2Ho1L1P3END3BUF2lo2B12B22B32D12D22D33NZ13NZ23SPP4SCUR3DS13DS23SPR1H2H02H12Hd". (* [comment removed for export] *)
    Lemma presx_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pnodes,(16.$0.)Pcur,$0.Pmm,P,(14.&40.)(2:.(14.&8.))Pm1,P,(14.&40.)(2:.(14.&8.))P,(1?.R4.)P,(20.R5.R4.)P,(2=.(28.R5.)R4.R3.)P,(2>.$1<.R5.R4.)P,(2?.$1<.VL,VLB,(15.&40.Vsp,)(30.(?.$0.$0.)(10.$0.$0.VPP,(8.VPP,+8.))(30.(?.$0.$0.)(10.$0.$0.VCUR,(8.VCUR,+20.))(17.(?.$0.$0.))))Vm,R6.)(2?.$1<.VL,VLB,(15.&40.Vsp,)(30.(?.$0.$0.)(10.$0.$0.VPP,(8.VPP,+8.))(30.(?.$0.$0.)(10.$0.$0.VCUR,(8.VCUR,+20.))(17.(?.$0.$0.))))Vm,R6.)")
(* [comment removed for export] *).
    Proof.
      intros nodes cur mm m1 HFR HCF MU WM HPX. pose proof LOSP. pose proof CEIL. pose proof DHI. pose proof DIM1. pose proof DIM2.
      eapply heap_presx_trans; [exact HPX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn [outside W] in Ho |- *.
      destruct (cur_cases nodes cur HFR HCF) as [->|(HIN & HCc & HD & HAP)].
      - destruct Hc as [Hs|[Hd|Hb]]; [lia| lia| pose proof (in_block_below a Hb); lia].
      - destruct Hc as [Hs|[Hd|Hb]]; [lia| lia|].
        flat constr:(Hb) 3%nat. flclear Hb. intros b Hb Hr. destruct b as [B j]. cbn in Hr. pose proof (HAP B j Hb).
        pose proof (in_block_below a ltac:(exists (B, j); split; [exact Hb| cbn; lia])). lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L36324904500.96L44017265591.97L63370427703.9700001L01Z01hS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B22B32D12D22D33NZ13NZ23SPP4SCUR3DS13DS23SPR4LOSP1y2H02H12HDS2sp2PP3CUR2bsS2sp2PP3CUR2bs". (* [comment removed for export] *)
    Lemma others_apart : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pnodes,(16.$0.)Pcur,$0.Phc,(24.$1<.VL,VHI,)PLBx,(16.$23.)Pmm,P,(14.&40.)(2:.(14.&8.))Pmoc,$2;.Py,$0.P,(2<.$1<.VL,VHI,R5.R4.R3.R2.)P,Pb,$23.P,(:.$23.R1.(25.R9.))(:.$23.R2.R7.)P,(31.$0.R9.)P,(1?.R:.)P,(20.R;.R:.)P,(:.$0.R6.(32.$0.R<.))(1.(<.(3.(8.R7.+20.)VPP,)(3.(8.VPP,+8.)R7.))(1.(<.(3.(8.R7.+20.)R<.)(3.(8.R<.+20.)R7.))(3.(8.R7.+20.)(;.VL,))))")
(* [comment removed for export] *).
    Proof.
      intros nodes cur hc LBx mm moc y HHx HS HND HFR HCF Hy. pose proof CEIL. pose proof DIM1. pose proof DIM2.
      pose proof (in_removelast _ _ Hy) as HyN.
      flat constr:((HFR y HyN)) 3%nat. intros HCc HD HAP.
      assert (HD' : y + 32 <= hl_data_lo L \/ hl_data_hi L <= y) by lia.
      split; [| split; [| exact HCc]].
      - eapply client_wrange_apart; [exact CW1| lia| lia| exact CEIL| exact HCc| exact HD'| exact HAP].
      - destruct HCF as (_ & _ & _ & _ & _ & _ & [[-> ->]|(Hne & -> & _ & _)]); [destruct Hy|].
        flat constr:((heap_blocks _ _ HI _ _ _ _ HHx)) 2%nat. intros _ HAPc.
        assert (NE : y <> last nodes 0).
        { intros E. rewrite <- (removelast_last_app nodes 0) in HND by exact Hne.
          apply (List.NoDup_remove_2 (removelast nodes) [] (last nodes 0)) in HND. rewrite app_nil_r in HND. apply HND. rewrite <- E. exact Hy. }
        eapply blocks_apart_in2; [exact HAPc| apply HS; apply nLBof_in; exact HyN| apply HS; apply nLBof_in| exact NE].
        rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L24091369234.10300001WS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B22B32D12D22D33NZ13NZ23SPP4SCUR3DS13DS23SPR3cur1H2H01y2cs3Hsz2A12A22A3". (* [comment removed for export] *)
    Lemma lseg_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pnodes,(16.$0.)Pcur,$0.Phc,(24.$1<.VL,VHI,)PLBx,(16.$23.)PLBn,(16.$23.)Pmm,P,(14.&40.)(2:.(14.&8.))Pm1,P,(14.&40.)(2:.(14.&8.))Pmoc,$2;.Pfin,$0.P,(2<.$1<.VL,VHI,R7.R6.R4.R2.)P,Pb,$23.P,(:.$23.R1.(25.R;.))(:.$23.R2.R9.)P,(31.$0.R;.)P,(1?.R<.)P,(20.R=.R<.)P,(33.$1<.R9.R:.VBUF,VEND,(32.$0.R>.)R6.)P,(2=.(28.R>.)R:.R9.)P,(2>.$1<.R;.R:.)(33.$1<.R;.R=.VBUF,VEND,(32.$0.R11.)R9.)")
(* [comment removed for export] *).
    Proof.
      intros nodes cur hc LBx LBn mm m1 moc fin HHx HS HND HFR HCF HL MU WM. pose proof LOSP. pose proof CEIL.
      eapply seq_lseg_mem; [exact HL| intros y Hy; eapply seq_lseg_in; [exact HL| exact Hy] |].
      intros y cs Hy HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz.
      flat constr:((others_apart nodes cur hc LBx mm moc y HHx HS HND HFR HCF Hy)) 3%nat. intros A1 A2 A3.
      cbn [disjoint_from W]. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L68050706037.9300000MS2sp2PP3CUR2bs2D14SCUR3cur2AP". (* [comment removed for export] *)
    Lemma headrep_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pnodes,(16.$0.)Pcur,$0.Pmm,P,(14.&40.)(2:.(14.&8.))Pm1,P,(14.&40.)(2:.(14.&8.))P,(20.R4.R3.)P,(34.R3.R5.)P,(2=.(28.R5.)R4.R3.)P,(2>.$1<.R5.R4.)(34.R5.R8.)")
(* [comment removed for export] *).
    Proof.
      intros nodes cur mm m1 HCF [->|(t & pd & l & p & HR & HB)] MU WM; [left; reflexivity|]. pose proof D1. pose proof DS2. pose proof LOSP.
      destruct HCF as (_ & _ & _ & _ & _ & _ & [[-> _]|(Hne & _ & _ & AP)]); [left; reflexivity| right].
      exists t, pd, l, p. split; [| exact HB]. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. unfold seq_cells. cbn. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L1219900981.9600001ES2sp2PP3CUR1P3END3BUF2lo2bs2B12B22B32D22D33NZ13NZ23SPP4SCUR3DS13DS23SPR3cur2H02H13HB5". (* [comment removed for export] *)
    Lemma sync_W : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pnodes,(16.$0.)Pcur,$0.Phc,(24.$1<.VL,VHI,)Pmm,P,(14.&40.)(2:.(14.&8.))Pm1,P,(14.&40.)(2:.(14.&8.))Pmoc,$2;.P,(31.$0.R6.)P,(1?.R7.)P,(20.R8.R7.)P,(2<.$1<.VL,VHI,R7.(25.R9.)R6.R4.)P,(6.$0.(26.$1<.VL,VHI,R8.)(26.$1<.VL,VHI,Vh,))P,(34.R8.R;.)P,(33.$1<.R9.(25.R<.)VBUF,VEND,(32.$0.R<.)(19.$0.R<.=))P,(2?.$1<.VL,VLB,(15.&40.Vsp,)(30.(?.$0.$0.)(10.$0.$0.VPP,(8.VPP,+8.))(30.(?.$0.$0.)(10.$0.$0.VCUR,(8.VCUR,+20.))(17.(?.$0.$0.))))Vm,R:.)P,(35.$1<.R;.VBUF,Vbs,)P,(2=.(28.R>.)R<.R;.)P,(2>.$1<.R=.R<.)(1.(2<.$1<.VL,VHI,R?.(25.R11.)R=.R<.)(1.(34.R=.R11.)(1.(33.$1<.R=.(25.R11.)VBUF,VEND,(32.$0.R11.)(19.$0.R11.=))(1.(2?.$1<.VL,VLB,(15.&40.Vsp,)(30.(?.$0.$0.)(10.$0.$0.VPP,(8.VPP,+8.))(30.(?.$0.$0.)(10.$0.$0.VCUR,(8.VCUR,+20.))(17.(?.$0.$0.))))Vm,R=.)(35.$1<.R=.VBUF,Vbs,)))))")
(* [comment removed for export] *).
    Proof.
      intros nodes cur hc mm m1 moc HND HFR HCF HHx HT HHD HL HPX HBY MU WM.
      split; [eapply heap_W; try eassumption; intros b Hb; exact Hb|]. split; [eapply headrep_W; eassumption|].
      split; [eapply lseg_W; try eassumption; intros b Hb; exact Hb|]. split; [eapply presx_W; eassumption|].
      eapply bytes_at_transport; [exact HBY| exact MU|]. pose proof D2. pose proof DS3. pose proof LOSP.
      flat constr:(HCF) 6%nat. flclear HCF. intros _ _ _ _ HB5 _. cbn [disjoint_from W]. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Lemma close_nodes : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pnodes,(16.$0.)Pcur,$0.Pmm,P,(14.&40.)(2:.(14.&8.))Pt,(14.&40.)Ppd,(14.&40.)Pl,$0.Pq,$0.P,(20.R7.R6.)P,(34.R6.R8.)P,(33.$1<.R7.(25.R9.)VBUF,VEND,(32.$0.R9.)(19.$0.R9.=))P,(1;.$1<.R8.R9.(1=.R7.R6.R5.R4.=))P,(<.(1.(6.$0.R5.=)(1.(6.$0.R6.=)(6.(16.$0.)R;.(17.$0.))))(1.(3.VBUF,R5.)(1.(3.=R6.)(3.(8.R5.R6.)VEND,))))(1.(1:.(14.&40.)Lt',(14.&40.)(1:.(14.&40.)Lpd',(14.&40.)(1:.$0.Ll',$0.(1:.$0.Lq',$0.(1.(1;.$1<.R>.VCUR,(1=.R4.R3.R2.R1.(1>.$0.=R10.)))(<.(1.(6.$0.R1.=)(1.(6.$0.R2.=)(6.(16.$0.)R10.(17.$0.))))(1.(3.VBUF,R1.)(1.(3.=R2.)(3.(8.R1.R2.)VEND,)))))))))(33.$1<.R:.(25.R<.)VBUF,VEND,R<.=))")
(* [comment removed for export] *).
    Proof.
      intros nodes cur mm t pd l q HCF HHD HL HR HB.
      destruct HCF as (AL & POS & _ & _ & _ & _ & [[-> ->]|(Hne & -> & A16 & _)]).
      - split; [exists t, pd, l, q; split; [exact HR| exact HB]| exact I].
      - destruct HHD as [E|(t' & pd' & l' & q' & HHc & HB')]; [exfalso; exact (Hne E)|]. split; [exists t', pd', l', q'; split; [exact HHc| right; exact HB']|].
        destruct HB as [(_ & _ & E)|HB]; [exfalso; exact (Hne E)|].
        rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply seq_lseg_app. split; [exact HL|].
        cbn [seq_lseg hd]. split; [apply nLBof_in|].
        { rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity. }
        split; [exact A16|]. split; [exact POS|]. split; [| exact I]. exists t, pd, l, q. split; [exact HR| exact HB].
    Qed.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L10180489728.8700000VS2sp2PP3CUR3END3BUF2bs1l1q3HB13HB23HB3". (* [comment removed for export] *)
    Lemma headrep_snoc : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pnodes,(16.$0.)Pcur,$0.Pmm,P,(14.&40.)(2:.(14.&8.))Pt,(14.&40.)Ppd,(14.&40.)Pl,$0.Pq,$0.PN,$0.P,(20.R8.R7.)P,(34.R7.R9.)P,(1;.$1<.R8.R9.(1=.R7.R6.R5.R4.R3.))P,(3.VBUF,R5.)P,(3.=R7.)P,(3.(8.R7.R8.)VEND,)(34.R<.(36.$0.R>.(30.$0.R7.(17.$0.))))")
(* [comment removed for export] *).
    Proof.
      intros nodes cur mm t pd l q N HCF HHD HR HB1 HB2 HB3. right.
      destruct HCF as (_ & _ & _ & _ & _ & _ & [[-> ->]|(Hne & _ & _ & _)]).
      - exists t, pd, l, q. split; [exact HR| lia].
      - destruct HHD as [E|(t' & pd' & l' & q' & HHc & HB)]; [exfalso; exact (Hne E)|]. exists t', pd', l', q'. rewrite hd_app_ne by exact Hne. split; [exact HHc| exact HB].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L10182588832.9400000\S2sp2PP3CUR3END3BUF2bs1l1q5nodes3HB13HB23HB3". (* [comment removed for export] *)
    Lemma lseg_fin : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pnodes,(16.$0.)Pcur,$0.Pmm,P,(14.&40.)(2:.(14.&8.))Pt,(14.&40.)Ppd,(14.&40.)Pl,$0.Pq,$0.Pfin,$0.PLBx,(16.$23.)P,(20.R9.R8.)P,(33.$1<.R8.(25.R:.)VBUF,VEND,(32.$0.R:.)(19.$0.R:.=))P,(1;.$1<.R9.R:.(1=.R8.R7.R6.R5.R4.))P,(3.VBUF,R6.)P,(3.=R8.)P,(3.(8.R8.R9.)VEND,)P,Pb,$23.P,(:.$23.R1.(25.R10.))(:.$23.R2.R9.)(33.$1<.R>.R8.VBUF,VEND,R10.R9.)")
(* [comment removed for export] *).
    Proof.
      intros nodes cur mm t pd l q fin LBx HCF HL HR HB1 HB2 HB3 HS.
      destruct nodes as [|n0 rest0]; [exact I|]. assert (Hne : n0 :: rest0 <> []) by discriminate. revert Hne HCF HL HS. generalize (n0 :: rest0). clear n0 rest0. intros nodes Hne HCF HL HS.
      destruct HCF as (AL & POS & _ & _ & _ & _ & [[E _]|(_ & -> & A16 & _)]); [exfalso; exact (Hne E)|].
      eapply seq_lseg_mem; [| intros x Hx; apply HS; apply nLBof_in; exact Hx| intros x cs _ HRx _; exact HRx].
      rewrite <- (removelast_last_app nodes 0) at 1 by exact Hne. apply seq_lseg_app. split; [exact HL|].
      cbn [seq_lseg hd]. split; [apply nLBof_in|].
      { rewrite <- (removelast_last_app nodes 0) at 2 by exact Hne. apply in_or_app. right. left. reflexivity. }
      split; [exact A16|]. split; [exact POS|]. split; [| exact I]. exists t, pd, l, q. split; [exact HR| lia].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L23639220756.9000000FS2sp2PP3CUR2lo2bs4SCUR". (* [comment removed for export] *)
    Lemma headrep_pres : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pnodes,(16.$0.)PLBx,(16.$23.)Pmm,P,(14.&40.)(2:.(14.&8.))Pm2,P,(14.&40.)(2:.(14.&8.))P,(37.$1<.VL,R3.(8.(15.&40.Vsp,)-80.)R2.R1.)P,Pb,$23.P,(:.$23.R1.VLB,)(:.$23.R2.R6.)P,(34.R4.R6.)(34.R4.R7.)")
(* [comment removed for export] *).
    Proof.
      intros nodes LBx mm m2 HP HS [->|(t & pd & l & p & HR & HB)]; [left; reflexivity| right]. pose proof DS2. pose proof LOSP.
      exists t, pd, l, p. split; [| exact HB]. eapply heap_pres_rw_cells; [exact HP| exact HR|].
      eapply client_range_wsep; [exact CW2| exact HS| unfold seq_cells; cbn; lia].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L30491911797.89L4640499146.89 00000G00^S2sp2PP3CUR2bs1y2cs3HszS2sp2PP3CUR2bs1y2cs3Hsz". (* [comment removed for export] *)
    Lemma lseg_pres : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "PLBx,(16.$23.)Pl,(16.$0.)Pfin,$0.Pmm,P,(14.&40.)(2:.(14.&8.))Pm2,P,(14.&40.)(2:.(14.&8.))PSP,$0.P,(37.$1<.VL,R6.R1.R3.R2.)P,(33.$1<.R4.R7.VBUF,VEND,R6.R5.)(33.$1<.R4.R8.VBUF,VEND,R7.R6.)")
(* [comment removed for export] *).
    Proof.
      intros LBx l fin mm m2 SP HP HL.
      eapply seq_lseg_mem; [exact HL| intros y Hy; eapply seq_lseg_in; [exact HL| exact Hy] |].
      intros y cs Hy HR Hsz. eapply heap_pres_rw_cells; [exact HP| exact HR|]. rewrite Hsz.
      eapply client_range_block; [eapply seq_lseg_in; [exact HL| exact Hy] | lia | cbn; lia].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L32480087599.81L38383218612.83L44052166346.83L63625778705.8100000>00P00b010S2sp2PP3CUR2bsS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs3curS2sp2PP3CUR2bs". (* [comment removed for export] *)
    Lemma cur_wrange : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pnodes,(16.$0.)Pcur,$0.PLBx,(16.$23.)P,(1?.R3.)P,(20.R4.R3.)P,Pb,$23.P,(:.$23.R1.(25.R6.))(:.$23.R2.R5.)(38.VL,R4.Vlo,(26.$1<.VL,VHI,Vh,)R5.+20.)")
(* [comment removed for export] *).
    Proof.
      intros nodes cur LBx HFR HCF HS.
      destruct (cur_cases nodes cur HFR HCF) as [->|(HIN & _)].
      - eapply client_wrange_inside; [exact CW2| intros b Hb; apply HS; apply nLBof_sub; exact Hb| lia| lia].
      - eapply client_wrange_block; [apply HS; apply nLBof_in; exact HIN| lia| lia].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00>0@L20847115543.106L255731202.106  L40365031583.106L41952613207.106L44013068718.102L44017148302.104L44017148315.103L50388579215.106L59308584312.4  L63370278683.103L64012146195.104L66151427842.16 L8085386908.106 L990761365.100  00001:01N02X04204B04R04b05:05D05T05h06B07E08YS1L2sp2PP3CUR3BUF2lo2bs2D33NZ13NZ23SPP4SCUR3DS13DS23SPR1N3HN03HNC3LBS1H2H2S2sp2PP3CUR2bs1N3HN0S1L2sp2PP3CUR3BUF2lo2bs2D23NZ13NZ23SPP4SCUR3DS13DS23SPR1N3HN03HNC3LBS1H2H2S1L3HLS2sp2PP3CUR3BUF2lo2bs2D12D22D33NZ13NZ23SPP4SCUR3DS13DS23DS33SPR4SLO21N3HN03HNC3LBS1HS2sp2PP3CUR2bs1NS2sp2PP3CUR2bs1NS2sp2PP3CUR2bs1NS2sp2PP3CUR3BUF2bs1N3APBS1N1y1E2HYS2sp2PP3CUR2bs1NS2sp2PP3CUR2bs1N3LBSS1N2r04HN161q1r1H2H02q02H4S1L2sp2PP3CUR3BUF2lo2bs2B43NZ13NZ23SPP4SCUR3SPR4CURB1N3HNC3LBS1H2H2S1L2sp2PP3CUR3BUF2lo2bs2D12D22D33NZ13NZ23SPP4SCUR3DS13DS23SPR1N3HN03HNI3LBS2H02H12H2". (* [comment removed for export] *)
    Lemma snoc_facts : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pnodes,(16.$0.)Pcur,$0.PN,$0.Phc2,(24.$1<.VL,VHI,)Pmm,P,(14.&40.)(2:.(14.&8.))Pmoc,$2;.P,(2<.$1<.VL,VHI,R3.(30.(?.$0.$0.)(10.$0.$0.R4.+20.)(25.R6.))R2.R1.)P,(31.$0.R7.)P,(1?.R8.)P,(20.R9.R8.)P,(39.VL,R8.+20.)P,(2.=(12.(13.(14.&8.)Vbs,)))(1.(31.$0.(36.$0.R<.(30.$0.R:.(17.$0.))))(1.(1?.(36.$0.R<.(30.$0.R:.(17.$0.))))(1.(20.(36.$0.R<.(30.$0.R:.(17.$0.)))R:.)(1.(<.(3.(8.R:.+20.)R;.)(3.(8.R;.+20.)R:.))(1.(<.(3.(8.R:.+20.)VPP,)(3.(8.VPP,+8.)R:.))(<.(3.(8.R:.+20.)VBUF,)(3.(8.VBUF,(12.(13.(14.&8.)Vbs,)))R:.)))))))")
(* [comment removed for export] *).
    Proof.
      intros nodes cur N hc2 mm moc HHx HND HFR HCF (HN0 & HN16 & _ & HNC & HNI) LBS.
      pose proof CEIL. pose proof DIM1. pose proof DIM2. pose proof LOSP. pose proof B1. pose proof B2. pose proof B3.
      flat constr:((heap_blocks _ _ HI _ _ _ _ HHx)) 2%nat. intros _ HAP. cbn [blocks_apart] in HAP. flat constr:(HAP) 2%nat. flclear HAP. intros HAPN HAPc.
      assert (HND' : N + 32 <= hl_data_lo L \/ hl_data_hi L <= N) by lia.
      assert (HAPN0 : forall B j, In (B, j) LB -> N + 32 <= B \/ B + j <= N) by (intros B j HBj; apply HAPN; apply nLBof_sub; exact HBj).
      assert (APC : N + 32 <= CUR \/ CUR + 32 <= N)
        by (eapply client_wrange_apart; [exact CW2 | lia | lia | exact CEIL | exact HNC | exact HND' | exact HAPN0]).
      assert (APP : N + 32 <= PP \/ PP + 8 <= N)
        by (eapply client_wrange_apart; [exact CW1 | lia | lia | exact CEIL | exact HNC | exact HND' | exact HAPN0]).
      assert (APB : N + 32 <= BUF \/ BUF + Z.of_nat (length bs) <= N)
        by (eapply client_range_apart; [exact CRB | lia | lia | exact CEIL | exact HNC | exact HND' | exact HAPN0]).
      assert (APcur : N + 32 <= cur \/ cur + 32 <= N).
      { destruct (cur_cases nodes cur HFR HCF) as [->|(HIN & _)]; [exact APC|]. apply HAPN. apply nLBof_in. exact HIN. }
      split; [| split; [| split; [| split; [exact APcur| split; [exact APP| exact APB]]]]].
      - apply List.NoDup_app; [exact HND| constructor; [intros HIn; destruct HIn| constructor] |].
        intros y Hy [E|[]]. pose proof (HAPN y 32 (nLBof_in nodes y Hy)) as HY. clear - E HY. lia.
      - intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|[<-|[]]]; [exact (HFR y Hy)|].
        split; [exact HNC|]. split; [exact HNI| exact HAPN0].
      - unfold curF. split; [clear - HN16; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        right. split; [destruct nodes; discriminate|]. split; [symmetry; apply last_last|]. split; [exact HN16| lia].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Definition curR (nodes : list Z) (l q : Z) : Prop := (q = 0 /\ l = 0 /\ nodes = []) \/ (BUF <= q /\ 0 <= l /\ q + l <= END).

    Ltac zofnat H := cbn [cells_size csize Nat.add length] in H;
      repeat match type of H with context [Z.of_nat (Datatypes.S ?k)] => let v := eval vm_compute in (Z.of_nat (Datatypes.S k)) in change (Z.of_nat (Datatypes.S k)) with v in H end;
      repeat match type of H with context [Z.add (Z.add ?a ?b) ?c] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (Z.add b c) in replace (Z.add (Z.add a b) c) with (Z.add a v) in H by lia end.
    Ltac fix_ret pc := replace (ret_pc (Z_to_bv 64 pc)) with (Z_to_bv 64 pc : word) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    Ltac kz K := first [ apply land64_zero in K; [| clear_disj; lia] | apply mod64_zero in K; [| clear_disj; lia]
                       | apply land64_nonzero in K; [| clear_disj; lia] | apply mod64_nonzero in K; [| clear_disj; lia]
                       | rewrite Z.mod_small in K by (clear_disj; lia)
                       | change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by (clear_disj; lia); rewrite Z.mod_small in K by (clear_disj; lia)
                       | idtac ].
    Ltac joinr H1 H2 :=
      lazymatch type of H1 with rw_cells ?sg ?mm ?A1 ?cs1 =>
      lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
        let v := eval vm_compute in (Z.of_nat (cells_size cs1)) in
        let Hj := fresh "J" in
        pose proof (proj2 (rw_cells_app sg mm A1 cs1 cs2)) as Hj;
        let He := fresh "E" in
        assert (He : Z.of_nat (cells_size cs1) = v) by reflexivity; rewrite He in Hj; clear He;
        replace A2 with (A1 + v) in H2 by lia;
        specialize (Hj (conj H1 H2)); clear H1 H2; rename Hj into H1; cbn [app] in H1
      end end.
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
    Ltac splitat H k H2 :=
      lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
        let l1 := spine_firstn k cs in
        let l2 := spine_skipn k cs in
        change (rw_cells sg mm A0 (l1 ++ l2)) in H;
        let H1 := fresh "SP" in
        (flat constr:((proj1 (rw_cells_app sg mm A0 l1 l2) H)) 2%nat; intros H1 H2); clear H; rename H1 into H; zofnat H2
      end.
    (* [comment removed for export] *)

    Notation C_INV := (Z_to_bv 64 (-9472)).
    Notation C_FEAT := (Z_to_bv 64 (-8320)).
    Notation C_OID := (Z_to_bv 64 68508).

    Notation K9574 := (Z_to_bv 64 (-9574)).
    Notation K9578 := (Z_to_bv 64 (-9578)).


    (* [comment removed for export] *)
    Ltac flia := first [clear_disj; lia | lia].
    Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12779162959.80L18926747689.80L18926759668.8000001L01Z01lS2sp2PP3CUR1P3END3BUF2lo2bs2B12B22B32D12D22D33NZ13NZ23SPP4SCUR3DS13DS23DS33SPR4LOSP1a1b1k2HkS2sp2PP3CUR2bsS2sp2PP3CUR2bs1a1b". (* [comment removed for export] *)
    Lemma zbv_mod : forall a b, (a - b) mod 18446744073709551616 = 0 -> (Z_to_bv 64 a : word) = Z_to_bv 64 b.
    Proof.
      intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
      apply Z.mod_divide in H; [| lia]. flat constr:(H) 2%nat. flclear H. intros k Hk. replace a with (b + k * 18446744073709551616) by lia. apply Z.mod_add. lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    (* [comment removed for export] *)
    Ltac fix_lit z :=
      lazymatch z with
      | Zpos _ => lazymatch eval compute in (Z.leb (2^63) z) with
                  | true => let z' := eval compute in (z - 2^64)%Z in replace (Z_to_bv 64 z : word) with (Z_to_bv 64 z' : word) by (apply zbv_mod; reflexivity)
                  | false => idtac end
      | _ => idtac end.
    Ltac fix_regs :=
      try lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?z) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => fix_lit z end;
      try lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?z) _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => fix_lit z end;
      try lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?z) _ _ _ _ _ _ _ _) _ _ _ _ _ _) => fix_lit z end;
      try lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?z) _ _ _ _) _ _ _ _ _ _) => fix_lit z end;
      try lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?z) _ _ _ _ _) _ _ _ _ _ _) => fix_lit z end.
    (* [comment removed for export] *)
    Ltac lsync mx :=
      (* [comment removed for export] *)
      repeat match goal with H : munch [] ?a ?a |- _ => clear H | H : wmono _ ?a ?a |- _ => clear H end;
      first [ lazymatch goal with Hm : munch _ _ mx |- _ => idtac end
            | pose proof (munch_refl (@nil ivl) mx); pose proof (wmono_refl usegs mx) ];
      lazymatch goal with Hm1 : munch ?W1 ?mA mx, HCF : curF ?nodes ?cur |- _ =>
      lazymatch goal with Hw1 : wmono _ mA mx |- _ =>
        let MUW := fresh "MUW" in
        assert (MUW : munch (W cur) mA mx) by (eapply munch_weaken; [| exact Hm1]; intros xw Hxw; clear - Hxw; cbn [outside W] in Hxw |- *; lia);
        lazymatch goal with HHc : HEAP _ _ _ ?hc (nLBof nodes) mA ?moc, HTc : heap_top _ _ _ ?hc' = heap_top _ _ _ h, HPXc : heap_presx _ _ LB (bv_unsigned sp) _ m mA,
                            ND : List.NoDup nodes, HFR : nfresh nodes, HHD : headrep mA nodes, HSG : seq_lseg _ mA _ BUF END (removelast nodes) _,
                            BYc : bytes_at _ mA BUF bs |- _ =>
          let A := fresh "HHl" in let B := fresh "HHDl" in let C := fresh "HSGl" in let D := fresh "HPXl" in let E := fresh "BYl" in
          (flat constr:((sync_W nodes cur hc mA mx moc ND HFR HCF HHc HTc HHD HSG HPXc BYc MUW Hw1)) 5%nat; intros A B C D E);
          clear HHc HHD HSG HPXc MUW Hm1 Hw1; try clear BYc;
          try match goal with H : bytes_at _ mx BUF bs, H' : bytes_at _ mx BUF bs |- _ => clear H' end
        end end end.

    (* [comment removed for export] *)
    Lemma L_RET : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pmx,P,(14.&40.)(2:.(14.&8.))Pmox,$2;.Phx,(24.$1<.VL,VHI,)Pnodes,(16.$0.)Pcur,$0.Pr,$0.Pp,$0.Pt,(14.&40.)Ppd,(14.&40.)Pl,$0.Pq,$0.Pt0,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Pa1,(14.&40.)Pa2,(14.&40.)Pa3,(14.&40.)Pa4,(14.&40.)Pa5,(14.&40.)Pa6,(14.&40.)Pa7,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)P,(3:.$1<.R19.)P,(3;.$1<.R1:.Vlo,(15.&40.Vsp,))P,(3<.Vmo,R1:.)P,(6.$0.(26.$1<.VL,VHI,R1:.)(26.$1<.VL,VHI,Vh,))P,(1.(2.-3000.R18.)(3.R18.=))P,(1;.$1<.R1>.VPP,(30.$3=.(3>.(3?.&40.R18.))(17.$3=.)))P,(1.(3.VP,R19.)(3.R19.VEND,))P,(1?.R1=.)P,(31.$0.R1>.)P,(20.R1?.R1>.)P,(34.R23.R20.)P,(33.$1<.R24.(25.R21.)VBUF,VEND,(32.$0.R21.)(19.$0.R21.=))P,(1;.$1<.R25.R21.(1=.R1>.R1=.R1<.R1;.=))P,(40.R23.R1=.R1<.)P,(2<.$1<.VL,VHI,R25.(25.R24.)R27.R26.)P,(2?.$1<.VL,VLB,(15.&40.Vsp,)(30.(?.$0.$0.)(10.$0.$0.VPP,(8.VPP,+8.))(30.(?.$0.$0.)(10.$0.$0.VCUR,(8.VCUR,+20.))(17.(?.$0.$0.))))Vm,R28.)(41.$1<.R28.(42.$1<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(43.(44.Vra,Vsp,Vgp,Vtp,R1>.R1=.R1<.Vs0,Vs1,(3?.&40.R24.)R1;.R1:.R19.R18.R17.R16.R15.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R14.R13.R12.R11.)VF,(45.Vra,)Vfc,(46.(14.&40.))R29.(47.$1<.)))")
(* [comment removed for export] *).
    Proof.
      intros until t6. intros MIx STx MFx HTx Hr HP Hp HFR ND HCF HHD HSG HCUR HCB HHx HPX.
      flat constr:((close_nodes nodes cur mx t pd l q HCF HHD HSG HCUR HCB)) 2%nat. intros FLt1 HLSn. flat constr:(FLt1) 6%nat. flclear FLt1. intros t' pd' l' q' HEAD HB'.
      apply aevtM_done. unfold x509_policies_post.
      do 15 eexists. exists mx, mox, hx, r, p, t', pd', l', q', (hd 0 nodes), nodes.
      split; [reflexivity|]. split; [exact MIx|]. split; [exact STx|]. split; [exact MFx|]. split; [exact HTx|]. split; [reflexivity|]. split; [exact Hr|].
      split; [exact HP|]. split; [exact Hp|]. split; [exact HEAD|]. split; [exact HB'|]. split; [reflexivity|].
      split; [apply (seq_lseg_chain usegs) with (B := BUF) (E := END); exact HLSn|].
      split; [exact ND|]. split; [intros x Hx; exact (proj2 (proj2 (HFR x Hx)))|]. split; [exact HHx|]. exact HPX.
    Qed.
    (* [comment removed for export] *)
    Ltac leaf_ret mx :=
      fix_regs;
      lazymatch goal with HHl : HEAP _ _ _ ?hc (nLBof ?nodes) mx ?moc, HCF : curF ?nodes' ?cur |- _ =>
      lazymatch goal with HP : rw_cells _ mx PP _, HC : rw_cells _ mx cur _, STx : stk _ mx lo (bv_unsigned sp), MIx : mem_inv _ mx,
                          HHDl : headrep mx _, HSGl : seq_lseg _ mx _ BUF END _ _, HPXl : heap_presx _ _ LB (bv_unsigned sp) _ m mx |- _ =>
        eapply (L_RET mx moc hc nodes cur);
        [exact MIx| exact STx| | | | exact HP| | | | exact HCF| exact HHDl| exact HSGl| exact HC| | exact HHl| exact HPXl];
        [first [eassumption| eapply mo_frame_trans; eassumption] | eassumption | flia | flia | eassumption | eassumption | first [eassumption | right; flia | left; repeat split; flia] ]
      end end.

    Section Loop.
      (* [comment removed for export] *)
      Definition HREGS (x1 x5 x6 x7 : word) (cur : Z) (x10 x11 x12 x13 x14 x15 x16 x17 : word) (v4 : Z) (x22 x26 : word) (pr : Z) (x28 x29 x30 x31 : word) := ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "(44.O15.(3?.&40.(8.(15.&40.Vsp,)-80.))Vgp,Vtp,O14.O13.O12.(3?.&40.VEND,)(3?.&40.O11.)O10.O?.O>.O=.O<.O;.O:.O9.(3?.&40.VPP,)(3?.&40.-2500.)(3?.&40.O8.)(3?.&40.+10;9<.)O7.(3?.&40.O5.)(3?.&40.+6.)(3?.&40.+4.)(3?.&40.-2000.)O6.O4.O3.O2.O1.)")
(* [comment removed for export] *).

      (* [comment removed for export] *)
      Definition KH (nn : nat) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pmc,P,(14.&40.)(2:.(14.&8.))Pmoc,$2;.Phc,(24.$1<.VL,VHI,)Pnodes,(16.$0.)Pcur,$0.Pln,$0.Pp,$0.Pt,(14.&40.)Ppd,(14.&40.)Pl,$0.Pq,$0.Ppr,$0.Px1,(14.&40.)Px5,(14.&40.)Px6,(14.&40.)Px7,(14.&40.)Px10,(14.&40.)Px11,(14.&40.)Px12,(14.&40.)Px13,(14.&40.)Px14,(14.&40.)Px15,(14.&40.)Px16,(14.&40.)Px17,(14.&40.)Px22,(14.&40.)Px26,(14.&40.)Px28,(14.&40.)Px29,(14.&40.)Px30,(14.&40.)Px31,(14.&40.)P,(2<.$1<.VL,VHI,R1<.(25.R1;.)R1>.R1=.)P,(6.$0.(26.$1<.VL,VHI,R1=.)(26.$1<.VL,VHI,Vh,))P,(3<.Vmo,R1?.)P,(2?.$1<.VL,VLB,(15.&40.Vsp,)(30.(?.$0.$0.)(10.$0.$0.VPP,(8.VPP,+8.))(30.(?.$0.$0.)(10.$0.$0.VCUR,(8.VCUR,+20.))(17.(?.$0.$0.))))Vm,R21.)P,(3:.$1<.R22.)P,(3;.$1<.R23.Vlo,(8.(15.&40.Vsp,)-80.))P,(1;.$1<.R24.(8.(15.&40.Vsp,)-80.)(30.$3=.(3>.(3?.&40.-256:.))(30.$3=.(3>.(3?.&40.-2566.))(17.$3=.))))P,(1;.$1<.R25.(8.(15.&40.Vsp,)-70.)(30.$3=.(3>.(3?.&40.R20.))(17.$3=.)))P,(1;.$1<.R26.(8.(15.&40.Vsp,)-68.)(30.$3=.(3>.Vs11,)(30.$3=.(3>.Vs10,)(30.$3=.(3>.Vs9,)(30.$3=.(3>.Vs8,)(30.$3=.(3>.Vs7,)(30.$3=.(3>.Vs6,)(30.$3=.(3>.Vs5,)(30.$3=.(3>.Vs4,)(30.$3=.(3>.Vs3,)(30.$3=.(3>.Vs2,)(30.$3=.(3>.Vs1,)(30.$3=.(3>.Vs0,)(30.$3=.(3>.Vra,)(17.$3=.)))))))))))))))P,(1;.$1<.R27.VPP,(30.$3=.(3>.(3?.&40.R21.))(17.$3=.)))P,(1.(3.VP,R22.)(3.R22.VEND,))P,(35.$1<.R29.VBUF,Vbs,)P,(31.$0.R27.)P,(1?.R28.)P,(20.R29.R28.)P,(34.R2=.R2:.)P,(33.$1<.R2>.(25.R2;.)VBUF,VEND,(32.$0.R2;.)(19.$0.R2;.=))P,(1;.$1<.R2?.R2;.(1=.R28.R27.R26.R25.=))P,(40.R2=.R27.R26.)P,(<.(6.$0.R26.=)(6.$0.R26.-2080.))P,(3.(4.VEND,R2<.)(12.O1.))(41.$1<.R32.(42.$1<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(43.(48.R27.R26.R25.R24.R2?.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R2=.R1;.R1:.R28.R19.R18.R17.R16.)VF,(3?.&40.+27628.)Vfc,(46.(14.&40.))R33.(47.$1<.)))")
(* [comment removed for export] *).

      Section Iter.
        Variable nn : nat.
        Hypothesis IH : KH nn.

        (* [comment removed for export] *)
        Ltac leaf_head mx :=
          (* [comment removed for export] *)
          lazymatch goal with |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v4) _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
            lazymatch goal with HP : rw_cells _ mx PP [C8 (Z_to_bv 64 ?pv)] |- _ =>
              first [constr_eq pv v4 | replace pv with v4 in HP by flia] end end;
          lazymatch goal with HHl : HEAP _ _ _ ?hc (nLBof ?nodes) mx ?moc, HCF : curF ?nodes' ?cur |- _ =>
          lazymatch goal with HP : rw_cells _ mx PP _, HC : rw_cells _ mx cur _, STx : stk _ mx lo _, MIx : mem_inv _ mx,
                              HF0 : rw_cells _ mx (bv_unsigned sp + -128) _, HFL : rw_cells _ mx (bv_unsigned sp + -112) _, HSV : rw_cells _ mx (bv_unsigned sp + -104) _,
                              HB : bytes_at _ mx BUF bs, ND : List.NoDup nodes, HFR : nfresh nodes,
                              HHDl : headrep mx _, HSGl : seq_lseg _ mx _ BUF END _ _, HPXl : heap_presx _ _ LB (bv_unsigned sp) _ m mx |- _ =>
            eapply (IH mx moc hc nodes cur);
            [exact HHl| | | exact HPXl| exact MIx| exact STx| exact HF0| exact HFL| exact HSV| exact HP| | exact HB| exact ND| exact HFR| exact HCF| exact HHDl| exact HSGl| exact HC| | | ];
            [eassumption| first [eassumption| eapply mo_frame_trans; eassumption]| flia| first [eassumption | right; flia]| first [eassumption| left; reflexivity| right; reflexivity]| flia]
          end end.

        (* [comment removed for export] *)
        Local Ltac2 Set LiaOrc.tbl := fun () => "00@0@L19031124607.176L28571794941.5  L37759934627.154L37759934627.183L45202778207.154L45202778207.183L47569862681.180L52956455594.183L53843456460.154L53843456460.176L53843456460.180L53843456460.183L6404012507.154 L68030124159.180L68297731981.176L8804326598.5   00001?01Q02202S03\05505J06507@08J09c0;60;^0=50=U0=gS2sp2PP3CUR1P3END2bs3NZ13NZ23SPR2nn3cur2p24pend2L24Hp2a3HL23Hpe4CPOS4lxv02H82H9S2sp2PP3cur2xw3HxwS2sp2PP3CUR3END2bs2nn3cur4pend2HnS2sp2PP3CUR3END2bs2nn3cur4pend2HnS2sp2PP3CUR1P3END2bs3NZ13NZ23SPR2nn3cur2p24pend2L24Hp2a3HL24Hp2c3Hpe4CPOSS2sp2PP3CUR1P3END2bs3NZ13NZ23SPR2nn3cur2p24pend2L24Hp2a3HL23Hpe4CPOS4lxv04lxv12H93H103H11S2sp2PP3CUR2bs2nn3curS2sp2PP3CUR2bs2nn3cur4pend4lxv04lxv12H63H10S2sp2PP3CUR3END3BUF2bs3NZ13NZ23SPR2nn3cur2p24pend2L24Hp2b3HL24Hp2c3Hpe4CPOSS2sp2PP3CUR3END3BUF2bs3NZ13NZ23SPR2nn3cur2p24pend2L24Hp2b3HL23Hpe4CPOS3H12S2sp2PP3CUR3END3BUF2bs3NZ13NZ23SPR2nn3cur2p24pend2L24Hp2b3HL23Hpe4CPOS4lxv04lxv12H32H62H8S2sp2PP3CUR3END3BUF2bs3NZ13NZ23SPR2nn3cur2p24pend2L24Hp2b3HL23Hpe4CPOS4lxv03H113H12S2sp2PP3CUR2bs2nn3cur2p24pend2L24Hp2c2H6S2sp2PP3CUR1P3END2bs3NZ13NZ23SPR2nn3cur2p24pend2L24Hp2a3HL23Hpe4CPOS4lxv04lxv12H32H62H8S2sp2PP3CUR2bs2nn3cur3lxv2H33H11S2sp2PP3cur2xw3Hxw". (* [comment removed for export] *)
        Lemma FILL : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Px11,(14.&40.)Pmc,P,(14.&40.)(2:.(14.&8.))Pmoc,$2;.Phc,(24.$1<.VL,VHI,)Pnodes,(16.$0.)Pcur,$0.Pp2,$0.Pt,(14.&40.)Ppd,(14.&40.)Pl,$0.Pq,$0.Ppr,$0.Ppend,$0.PL2,$0.Px1,(14.&40.)Px5,(14.&40.)Px6,(14.&40.)Px7,(14.&40.)Px10,(14.&40.)Px12,(14.&40.)Px13,(14.&40.)Px14,(14.&40.)Px15,(14.&40.)Px16,(14.&40.)Px17,(14.&40.)Px28,(14.&40.)Px29,(14.&40.)Px30,(14.&40.)Px31,(14.&40.)P,(2<.$1<.VL,VHI,R1:.(25.R19.)R1<.R1;.)P,(6.$0.(26.$1<.VL,VHI,R1;.)(26.$1<.VL,VHI,Vh,))P,(3<.Vmo,R1=.)P,(2?.$1<.VL,VLB,(15.&40.Vsp,)(30.(?.$0.$0.)(10.$0.$0.VPP,(8.VPP,+8.))(30.(?.$0.$0.)(10.$0.$0.VCUR,(8.VCUR,+20.))(17.(?.$0.$0.))))Vm,R1?.)P,(3:.$1<.R20.)P,(3;.$1<.R21.Vlo,(8.(15.&40.Vsp,)-80.))P,(1;.$1<.R22.(8.(15.&40.Vsp,)-80.)(30.$3=.(3>.(3?.&40.-256:.))(30.$3=.(3>.(3?.&40.-2566.))(17.$3=.))))P,(1;.$1<.R23.(8.(15.&40.Vsp,)-70.)(30.$3=.(3>.(3?.&40.R17.))(17.$3=.)))P,(1;.$1<.R24.(8.(15.&40.Vsp,)-68.)(30.$3=.(3>.Vs11,)(30.$3=.(3>.Vs10,)(30.$3=.(3>.Vs9,)(30.$3=.(3>.Vs8,)(30.$3=.(3>.Vs7,)(30.$3=.(3>.Vs6,)(30.$3=.(3>.Vs5,)(30.$3=.(3>.Vs4,)(30.$3=.(3>.Vs3,)(30.$3=.(3>.Vs2,)(30.$3=.(3>.Vs1,)(30.$3=.(3>.Vs0,)(30.$3=.(3>.Vra,)(17.$3=.)))))))))))))))P,(1;.$1<.R25.VPP,(30.$3=.(3>.(3?.&40.R20.))(17.$3=.)))P,(35.$1<.R26.VBUF,Vbs,)P,(31.$0.R24.)P,(1?.R25.)P,(20.R26.R25.)P,(34.R2:.R27.)P,(33.$1<.R2;.(25.R28.)VBUF,VEND,(32.$0.R28.)(19.$0.R28.=))P,(1;.$1<.R2<.R28.(1=.R26.R25.R24.R23.=))P,(<.(6.$0.R23.=)(6.$0.R23.-2080.))P,(3.VP,R29.)P,(3.VBUF,R2:.)P,(3.=R24.)P,(3.(8.R2<.R25.)R26.)P,(3.R27.VEND,)P,(3.(8.(4.VEND,R28.)+1.)(12.Vnn,))(41.$1<.R33.(42.$1<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(43.(44.R27.(3?.&40.(8.(15.&40.Vsp,)-80.))Vgp,Vtp,R26.R25.R24.(3?.&40.VEND,)(3?.&40.R30.)R23.R35.R22.R21.R20.R1?.R1>.R1=.(3?.&40.VPP,)(3?.&40.-2500.)(3?.&40.R29.)(3?.&40.+10;9<.)(3?.&40.R2?.)(3?.&40.R2:.)(3?.&40.+6.)(3?.&40.+4.)(3?.&40.-2000.)(3?.&40.R28.)R1<.R1;.R1:.R19.)VF,(3?.&40.+276=8.)Vfc,(46.(14.&40.))R34.(47.$1<.)))")
(* [comment removed for export] *).
        Proof.
          intros until x31. intros HHc HTc MFc HPXc MIc STc FC FL SV PPc BYc ND HFR HCF HHD HSG HCUR PR Hp2a Hp2b HL2 Hp2c Hpe Hn.
          pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof LOSP as LOSP'. pose proof B1 as B1'. pose proof B2 as B2'. pose proof B3 as B3'. pose proof B4 as B4'. pose proof PPB as PPB'.
          pose proof AL1 as AL1'. pose proof NZ1 as NZ1'. pose proof NZ3 as NZ3'. pose proof D2 as D2'. pose proof DS1 as DS1'. pose proof DS3 as DS3'. pose proof SP16 as SP16'. pose proof SPR as SPR'.
          pose proof SPP as SPP'. pose proof CEIL as CEIL'. pose proof DHI as DHI'. pose proof DIM1 as DIM1'. pose proof DIM2 as DIM2'.
          pose proof HCF as HCF'. flat constr:(HCF') 7%nat. flclear HCF'. intros CAL CPOS C64 CPP CBF CSTK _.
          clear MI ST. lazymatch type of HPP with ?T => change (lx_hidden T) in HPP end. lazymatch type of HCR with ?T => change (lx_hidden T) in HCR end.
          lazymatch type of BY with ?T => change (lx_hidden T) in BY end.
          unfold seq_cells in HCUR.
          (* [comment removed for export] *)
          assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) [SUM_gettagP])
            by (intros AL; repeat constructor; apply apply_summary_sound; apply sum_gettagP_valid).
          rewrite TP. apply (lxp_aevtM_of_evt usegs moc _ _ MK).
          lx_run_tac (PLANS [0x27628] [] 100%N [SUM_gettagP]); lx_tree.
          all: apply evt_done; cbv beta; rewrite <- TP.
          all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => lsync mx end.
          all: lazymatch goal with
               | |- aevtM _ _ _ (MS _ _ (ret_pc _) _ _ ?mx _) => leaf_ret mx
               | |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 0x27628) _ _ ?mx _) => unfold HREGS in IH; leaf_head mx
               end.
        Qed.
        Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
        (* [comment removed for export] *)
        Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L10170007385.176L1219819012.10  L20216145785.190L2156550393.190 L22704459656.5  L27454681247.166L29606286466.166L3517592487.166 L38133883275.165L38397459865.176L39011996849.190L44010973420.166L44243963223.163L44256556378.194L45364886807.190L46881195519.176L47403886218.193L50087265159.161L51284677265.190L53308553363.193L53604122480.190L59310630150.166L64012342419.162L66024063243.161L6751723004.166 L8158759545.190 00000V01>01S01h02:02\03103P05W05l06I06^07?07b08709@09U09j0:J0:_0;80;T0=G0>B0>W0>lS2sp2PP3CUR3END3BUF2bs2nn3cur1l1q4HCBrS2sp2PP3BUF2lo2bs3cur5LOSP'3D2'4DS3'3CBFS2sp2PP3CUR2bs2nn3curS2sp2PP3CUR2bs2nn3curS2sp2PP3cur2xw3HxwS1L2HI2sp1h2PP3CUR2bs5SPTOP2nn3curS2sp2PP3CUR2bs2nn3curS1L2sp2PP3CUR2lo2bs4SLO22nn3curS1L2sp2PP3CUR3END3BUF2lo2bs2D12D22D33NZ13NZ24SCUR3DS23DS33SPR3ACP2nn3cur1l1q2Q12Q22Q35LOSP'5SLO2'4HLS'3B3'3B4'5CEIL'4NZ3'4SPP'4CPOS3LBSS2sp2PP3CUR2bs2nn3curS2sp2PP3CUR2lo2bs2nn3cur4CSTKS2sp2PP3CUR2bs2nn3curS2sp2PP3CUR3BUF2bs2nn3cur2p24Hp2bS2sp2PP3CUR3BUF2bs2nn3cur2p24Hp2b1NS2sp2PP3CUR2bs2nn3curS2sp2PP3CUR1P3END2bs3NZ13NZ23SPR2nn3cur2p24pend2L24Hp2a3HL24Hp2c3Hpe4CPOSS2sp2PP3CUR2bs2nn3curS2sp2PP3CUR2bs2nn3curS2sp2PP3CUR3BUF2lo2bs3DS32nn3curS2sp2PP3CUR2bs2nn3curS2sp2PP3CUR2bs3SPP2nn3curS2sp2PP3CUR2bs2nn3cur1q1E2H6S2sp2PP3CUR3END3BUF2lo2bs2D12D22D33NZ13NZ24SCUR3DS23DS33SPR2nn3cur2p24pend2L24Hp2b3HL24Hp2c3Hpe5LOSP'3B3'4SPP'4CPOSS1L2sp2PP3CUR2lo2bs3NZ13NZ23SPR3ACP2nn3cur5LOSP'5CEIL'4CPOSS2sp2PP3CUR2bs2nn3curS2sp2PP3CUR2bs2nn3cur". (* [comment removed for export] *)
        Lemma L_CA4 : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pmc,P,(14.&40.)(2:.(14.&8.))Pmoc,$2;.Phc,(24.$1<.VL,VHI,)Pnodes,(16.$0.)Pcur,$0.Pp2,$0.Pt,(14.&40.)Ppd,(14.&40.)Pl,$0.Pq,$0.Ppr,$0.Ppend,$0.PL2,$0.Px1,(14.&40.)Px5,(14.&40.)Px6,(14.&40.)Px7,(14.&40.)Px10,(14.&40.)Px11,(14.&40.)Px12,(14.&40.)Px13,(14.&40.)Px14,(14.&40.)Px15,(14.&40.)Px16,(14.&40.)Px17,(14.&40.)Px28,(14.&40.)Px29,(14.&40.)Px30,(14.&40.)Px31,(14.&40.)P,(2<.$1<.VL,VHI,R1;.(25.R1:.)R1=.R1<.)P,(6.$0.(26.$1<.VL,VHI,R1<.)(26.$1<.VL,VHI,Vh,))P,(3<.Vmo,R1>.)P,(2?.$1<.VL,VLB,(15.&40.Vsp,)(30.(?.$0.$0.)(10.$0.$0.VPP,(8.VPP,+8.))(30.(?.$0.$0.)(10.$0.$0.VCUR,(8.VCUR,+20.))(17.(?.$0.$0.))))Vm,R20.)P,(3:.$1<.R21.)P,(3;.$1<.R22.Vlo,(8.(15.&40.Vsp,)-80.))P,(1;.$1<.R23.(8.(15.&40.Vsp,)-80.)(30.$3=.(3>.(3?.&40.-256:.))(30.$3=.(3>.(3?.&40.-2566.))(17.$3=.))))P,(1;.$1<.R24.(8.(15.&40.Vsp,)-70.)(30.$3=.(3>.(3?.&40.R18.))(17.$3=.)))P,(1;.$1<.R25.(8.(15.&40.Vsp,)-68.)(30.$3=.(3>.Vs11,)(30.$3=.(3>.Vs10,)(30.$3=.(3>.Vs9,)(30.$3=.(3>.Vs8,)(30.$3=.(3>.Vs7,)(30.$3=.(3>.Vs6,)(30.$3=.(3>.Vs5,)(30.$3=.(3>.Vs4,)(30.$3=.(3>.Vs3,)(30.$3=.(3>.Vs2,)(30.$3=.(3>.Vs1,)(30.$3=.(3>.Vs0,)(30.$3=.(3>.Vra,)(17.$3=.)))))))))))))))P,(1;.$1<.R26.VPP,(30.$3=.(3>.(3?.&40.R21.))(17.$3=.)))P,(35.$1<.R27.VBUF,Vbs,)P,(31.$0.R25.)P,(1?.R26.)P,(20.R27.R26.)P,(34.R2;.R28.)P,(33.$1<.R2<.(25.R29.)VBUF,VEND,(32.$0.R29.)(19.$0.R29.=))P,(1;.$1<.R2=.R29.(1=.R27.R26.R25.R24.=))P,(40.R2;.R26.R25.)P,(<.(6.$0.R25.=)(6.$0.R25.-2080.))P,(3.VP,R2;.)P,(2.VBUF,R2<.)P,(3.=R26.)P,(3.(8.R2>.R27.)R28.)P,(3.R29.VEND,)P,(3.(8.(4.VEND,R2:.)+1.)(12.Vnn,))(41.$1<.R35.(42.$1<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(43.(44.R29.(3?.&40.(8.(15.&40.Vsp,)-80.))Vgp,Vtp,R28.R27.R26.(3?.&40.VEND,)(3?.&40.R32.)R25.R24.R23.R22.R21.R20.R1?.R1>.(3?.&40.VPP,)(3?.&40.-2500.)(3?.&40.R2;.)(3?.&40.+10;9<.)(3?.&40.R31.)(3?.&40.R2<.)(3?.&40.+6.)(3?.&40.+4.)(3?.&40.-2000.)(3?.&40.R2:.)R1=.R1<.R1;.R1:.)VF,(3?.&40.+276:0.)Vfc,(46.(14.&40.))R36.(47.$1<.)))")
(* [comment removed for export] *).
        Proof.
          intros until x31. intros HHc HTc MFc HPXc MIc STc FC FL SV PPc BYc ND HFR HCF HHD HSG HCUR HCB PR Hp2a Hp2b HL2 Hp2c Hpe Hn.
          pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK. pose proof LOSP as LOSP'. pose proof SLO2 as SLO2'. pose proof HLS as HLS'.
          pose proof B1 as B1'. pose proof B2 as B2'. pose proof B3 as B3'. pose proof B4 as B4'. pose proof PPB as PPB'. pose proof CEIL as CEIL'. pose proof SPTOP as SPTOP'.
          pose proof AL1 as AL1'. pose proof NZ1 as NZ1'. pose proof NZ3 as NZ3'. pose proof D2 as D2'. pose proof DS1 as DS1'. pose proof DS3 as DS3'. pose proof SP16 as SP16'. pose proof SPP as SPP'.
          pose proof SPR as SPR'. pose proof DHI as DHI'. pose proof DIM1 as DIM1'. pose proof DIM2 as DIM2'.
          pose proof HCF as HCF'. flat constr:(HCF') 7%nat. flclear HCF'. intros CAL CPOS C64 CPP CBF CSTK _.
          pose proof (unsigned_lit (bv_unsigned sp + -128) ltac:(lia)) as USP.
          assert (LBS : 0 < Z.of_nat (length bs)) by lia.
          assert (HQ : 0 <= q < 2^63) by (destruct HCB as [(-> & _)|(Q1 & Q2 & Q3)]; lia).
          clear MI ST. lazymatch type of HPP with ?T => change (lx_hidden T) in HPP end. lazymatch type of HCR with ?T => change (lx_hidden T) in HCR end.
          lazymatch type of BY with ?T => change (lx_hidden T) in BY end.
          unfold seq_cells in HCUR.
          (* [comment removed for export] *)
          assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
          rewrite TP. apply (lxp_aevtM_of_evt usegs moc _ _ MK).
          lx_run_tac (PLANS [0x276d8; 0x3f960] [] 60%N (@nil summary)); lx_tree.
          all: apply evt_done; cbv beta; rewrite <- TP.
          all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
          (* [comment removed for export] *)
          1: lazymatch goal with HC : rw_cells _ mc cur _, HP : rw_cells _ mc PP _, HF0 : rw_cells _ mc (bv_unsigned sp + -128) _, HFL : rw_cells _ mc (bv_unsigned sp + -112) _,
                                 HSV : rw_cells _ mc (bv_unsigned sp + -104) _, HB : bytes_at _ mc BUF bs, STx : stk _ mc lo _, MIx : mem_inv _ mc |- _ =>
               eapply FILL; [exact HHc| exact HTc| exact MFc| exact HPXc| exact MIx| exact STx| exact HF0| exact HFL| exact HSV| exact HP| exact HB| exact ND| exact HFR| exact HCF
                            | exact HHD| exact HSG| exact HC| exact PR| exact Hp2a| flia| exact HL2| exact Hp2c| exact Hpe| exact Hn] end.
          (* [comment removed for export] *)
          try rename HCUR into HCUR0; try rename PPc into PPc0; try rename FC into FC0; try rename FL into FL0; try rename SV into SV0;
          try rename BYc into BYc0; try rename STc into STc0; try rename MIc into MIc0.
          lazymatch goal with HC : rw_cells _ mc cur _, HP : rw_cells _ mc PP _, HF0 : rw_cells _ mc (bv_unsigned sp + -128) _, HFL : rw_cells _ mc (bv_unsigned sp + -112) _,
                              HSV : rw_cells _ mc (bv_unsigned sp + -104) _, HB : bytes_at _ mc BUF bs, STx : stk _ mc lo _, MIx : mem_inv _ mc |- _ =>
            rename HC into HCUR; rename HP into PPc; rename HF0 into FC; rename HFL into FL; rename HSV into SV; rename HB into BYc; rename STx into STc; rename MIx into MIc end.
          repeat match goal with H : munch [] mc mc |- _ => clear H | H : wmono usegs mc mc |- _ => clear H end.
          try clear HCUR0 PPc0 FC0 FL0 SV0 BYc0 STc0 MIc0.
          assert (HCBr : BUF <= q /\ 0 <= l /\ q + l <= END) by (destruct HCB as [(E & _)|H']; [exfalso; lia| exact H']). clear HCB.
          replace (Z_to_bv 64 260448 : word) with (Z_to_bv 64 (hl_calloc L) : word) by (rewrite HCALLOC; reflexivity).
          eapply aevtM_cut.
          { eapply (heap_calloc usegs L HI) with (cnt := 1) (sz := 32) (lo := lo) (h := hc) (LB := nLBof nodes);
              [ exact HHc | rewrite USP; exact STc | exact CEIL | rewrite USP; lia | exact MIc | exact TP | rewrite USP, HTc; lia
              | reflexivity | reflexivity | lia | lia | lia ]. }
          intros ms' mo'x PO. unfold call_post in PO.
          destruct PO as (w0 & w1 & w2 & wa0 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m2 & mo2
                          & E0 & MI2 & ST2 & MF2 & HP2 & h2 & HT2 & HRES).
          injection E0; clear E0; intros Emo Ems. subst ms' mo'x. rewrite USP in ST2, HP2. fix_ret 0x276c4.
          (* [comment removed for export] *)
          apply (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP2) in FC; [| apply client_range_stack; cbn; lia].
          apply (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP2) in FL; [| apply client_range_stack; cbn; lia].
          apply (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP2) in SV; [| apply client_range_stack; cbn; lia].
          apply (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP2) in PPc; [| apply client_range_stack; cbn; lia].
          apply (heap_pres_rw_cells usegs L _ _ _ _ _ _ HP2) in HCUR.
          2:{ eapply client_range_wsep; [eapply (cur_wrange nodes cur); [exact HFR| exact HCF| intros b Hb; exact Hb] | intros b Hb; exact Hb| cbn; lia]. }
          assert (BY2 : bytes_at usegs m2 BUF bs).
          { eapply heap_pres_bytes_at; [exact HP2| exact BYc|]. eapply client_range_sep; [exact CRB| intros b Hb; apply nLBof_sub; exact Hb| lia]. }
          pose proof (headrep_pres nodes _ _ _ HP2 (nLBof_sub nodes) HHD) as HHD2.
          pose proof (lseg_pres _ _ _ _ _ _ HP2 HSG) as HSG2.
          assert (HPX2 : heap_presx usegs L LB (bv_unsigned sp) X0 m m2).
          { eapply heap_presx_trans; [exact HPXc|]. eapply heap_presx_of_pres_sub; [exact HP2| apply nLBof_sub| lia| lia]. }
          assert (HTn : heap_top usegs L HI h2 = heap_top usegs L HI h) by (rewrite HT2; exact HTc).
          assert (MFn : mo_frame mo mo2) by (eapply mo_frame_trans; [exact MFc| exact MF2]).
          clear HHc HPXc BYc HHD HSG STc MIc MK HTc MFc MF2 HT2 HP2. rename BY2 into BYc. rename HHD2 into HHD. rename HSG2 into HSG. rename HPX2 into HPXc. rename HTn into HTc. rename MFn into MFc.
          rename ST2 into STc. rename MI2 into MIc.
          destruct HRES as [[-> HHc] | (N & -> & HBN & HHc & HNEW)].
          - (* [comment removed for export] *)
            pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK.
            rewrite TP. apply (lxp_aevtM_of_evt usegs mo2 _ _ MK).
            lx_run_tac (PLANS [0x276d8] [] 60%N (@nil summary)); lx_tree.
            all: apply evt_done; cbv beta; rewrite <- TP.
            all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => lsync mx; leaf_ret mx end.
          - (* [comment removed for export] *)
            change (1 * 32) with 32 in HBN, HHc, HNEW. cbn [Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in HNEW.
            flat constr:((snoc_facts nodes cur N h2 m2 mo2 HHc ND HFR HCF HBN LBS)) 6%nat. intros ND' HFR' HCF' APcur APP APB.
            pose proof HBN as HBNc. flat constr:(HBNc) 5%nat. flclear HBNc. intros HN0 HN16 _ HNC HNI.
            apply (rw_cells_zeros usegs m2 N 32 (seq_cells (Z_to_bv 64 0) (Z_to_bv 64 0) 0 0 0)) in HNEW; [| cbn; repeat split; reflexivity | reflexivity].
            unfold seq_cells in HNEW.
            pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK.
            rewrite TP. apply (lxp_aevtM_of_evt usegs mo2 _ _ MK).
            lx_run_tac (PLANS [0x276d8] [] 60%N (@nil summary)); lx_tree.
            all: apply evt_done; cbv beta; rewrite <- TP.
            lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
              lazymatch goal with Hm1 : munch ?W1 m2 mx, Hw1 : wmono _ m2 mx, HC : rw_cells _ mx cur _, HNn : rw_cells _ mx N _, STx : stk _ mx lo _, MIx : mem_inv _ mx,
                                  HP : rw_cells _ mx PP _, HF0 : rw_cells _ mx (bv_unsigned sp + -128) _, HFL : rw_cells _ mx (bv_unsigned sp + -112) _,
                                  HSV : rw_cells _ mx (bv_unsigned sp + -104) _ |- _ =>
                let MUW := fresh "MUW" in
                assert (MUW : munch (W cur) m2 mx) by (eapply munch_weaken; [| exact Hm1]; intros xw Hxw; clear - Hxw; cbn [outside W] in Hxw |- *; lia);
                pose proof (heap_W nodes cur h2 _ m2 mx mo2 HFR HCF HHc HTc ltac:(intros b Hb; right; exact Hb) MUW Hw1) as HH3;
                pose proof (presx_W nodes cur m2 mx HFR HCF MUW Hw1 HPXc) as HPX3;
                pose proof (lseg_W nodes cur h2 _ _ m2 mx mo2 _ HHc ltac:(intros b Hb; right; exact Hb) ND HFR HCF HSG MUW Hw1) as HSG3;
                pose proof (headrep_W nodes cur m2 mx HCF HHD MUW Hw1) as HHD3;
                assert (BY3 : bytes_at usegs mx BUF bs) by (eapply bytes_at_transport; [exact BYc| exact MUW| cbn [disjoint_from W]; clear - CBF D2' DS3' LOSP'; lia]);
                clear HHc HPXc HSG HHD BYc MUW Hm1 Hw1;
                lazymatch type of HC with rw_cells _ _ _ [_; _; _; _; C8 ?nv] => change nv with (Z_to_bv 64 N : word) in HC || idtac end;
                change (rw_cells usegs mx cur (seq_cells t pd l q N)) in HC;
                (flat constr:(HCBr) 3%nat; flclear HCBr; intros HB1x HB2x HB3x);
                pose proof (headrep_snoc nodes cur mx t pd l q N HCF HHD3 HC HB1x HB2x HB3x) as HHD4;
                pose proof (lseg_fin nodes cur mx t pd l q N (nLBof (nodes ++ [N])) HCF HSG3 HC HB1x HB2x HB3x ltac:(intros b Hb; rewrite nLBof_snoc; right; exact Hb)) as HSG4;
                rewrite <- nLBof_snoc in HH3;
                rewrite <- (removelast_last nodes N) in HSG4 at 2; rewrite <- (last_last nodes N 0) in HSG4 at 3;
                change (rw_cells usegs mx N (seq_cells (Z_to_bv 64 0) (Z_to_bv 64 0) 0 0 0)) in HNn;
                eapply (FILL _ mx mo2 h2 (nodes ++ [N]) N);
                [exact HH3| exact HTc| exact MFc| exact HPX3| exact MIx| exact STx| exact HF0| exact HFL| exact HSV| exact HP| exact BY3| exact ND'| exact HFR'| exact HCF'
                | exact HHD4| exact HSG4| exact HNn| exact PR| exact Hp2a| flia| exact HL2| exact Hp2c| exact Hpe| exact Hn]
              end end.
        Qed.
        Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
      End Iter.

      (* [comment removed for export] *)
      Ltac ro_const A n RO :=
        lazymatch goal with |- context [MS _ _ _ _ _ ?mx (seg_rom ?sg)] =>
          let cbs := eval vm_compute in (match image_bytes sg A n with Some cbs => cbs | None => [] end) in
          match goal with MI : mem_inv sg mx |- _ =>
            pose proof (ro_image_bytes_at sg mx A cbs MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO end
        end.

      (* [comment removed for export] *)
      Local Ltac2 Set LiaOrc.tbl := fun () => "00X0@L13443096587.207L13443096587.225L13443096587.227L14366723839.147L14366723839.149L15781037771.227L19031124607.174L19540777816.207L19540777816.225L19540777816.227L22704459656.5  L24945598354.207L24945598354.225L24945598354.227L2920218969.147 L2920218969.149 L2920218969.160 L2920218969.162 L30485595088.227L33795255170.207L33795255170.225L33795255170.227L36689020188.216L37649603600.207L37649603600.225L37649603600.227L39268637205.0  L39332496128.216L47216798497.0  L52295489675.201L55808129792.216L5645198221.201 L57626602889.5  L57684758224.212L59316904292.154L68297731981.174L7708577250.212 L7710685365.207 L7710685365.225 L7710685365.227 00001702>03E03e04H05005o07C08W09k0:=0;50;m0<e0<f0<g0=Y0>N0?60?]0@D0@k0B]0CI0D50Da0Db0EJ0EK0F]0GE0H00HB0IZ0J80Ja0L00M?0NN0O]S2sp2PP3CUR1P3END2bs3NZ13NZ23SPR2nn3cur1p2Hp2Hn4CPOS4lxv05lxv173H113H20S2sp2PP3CUR1P3END2bs3NZ13NZ23SPR2nn3cur1p2Hp2Hn4CPOS4lxv05lxv173H123H21S2sp2PP3CUR1P3END2bs3NZ13NZ23SPR2nn3cur1p2Hp2Hn4CPOS4lxv05lxv173H123H21S2sp2PP3CUR1P3END2bs3cur1p2Hp2HnS2sp2PP3CUR1P3END2bs2nn3cur1p2Hp2HnS2sp2PP3CUR3END3BUF2bs2nn3cur1p2Hn5lxv17S2sp2PP3CUR1P3END2bs3NZ13NZ23SPR2nn3cur1p2Hp2Hn4CPOS4lxv02H82H9S2sp2PP3CUR3END2bs3NZ13NZ23SPR2nn3cur1p2Hn4CPOS4lxv04lxv15lxv175lxv182H93H103H113H20S2sp2PP3CUR3END2bs3NZ13NZ23SPR2nn3cur1p2Hn4CPOS4lxv04lxv15lxv175lxv182H73H113H123H21S2sp2PP3CUR3END2bs3NZ13NZ23SPR2nn3cur1p2Hn4CPOS4lxv04lxv15lxv175lxv182H73H113H123H21S2sp2PP3cur2xw3HxwS2sp2PP3CUR3END2bs2nn3cur1p2Hn4lxv04lxv15lxv175lxv183H10S2sp2PP3CUR3END2bs2nn3cur1p2Hn4lxv04lxv15lxv175lxv183H11S2sp2PP3CUR3END2bs2nn3cur1p2Hn4lxv04lxv15lxv175lxv183H11FFS2sp2PP3CUR3END2bs3NZ13NZ23SPR3cur1p2pr2PR2Hn4CPOSS2sp2PP3CUR3END2bs3NZ13NZ23SPR2nn3cur1p2pr2PR2Hn4CPOSS2sp2PP3CUR3END3BUF2bs2nn3cur1p2Hn5lxv17S2sp2PP3CUR3END2bs2nn3cur1p2Hn5lxv182H9S2sp2PP3CUR3END2bs2nn3cur1p2Hn5lxv182H7S2sp2PP3CUR3END2bs2nn3cur1p2Hn5lxv182H7S2sp2PP3CUR1P3END3BUF2bs3NZ13NZ23SPR2nn3cur1p2Hp2Hn3B1'3B3'3B4'4NZ3'4CPOS4lxv04lxv15lxv175lxv182H73H113H123H203H21S2sp2PP3CUR3END2bs2nn3cur1p2Hn4lxv04lxv13H19S2sp2PP3CUR3END2bs2nn3cur1p2Hn4lxv04lxv13H20S2sp2PP3CUR3END2bs2nn3cur1p2Hn4lxv04lxv13H20SS2sp2PP3CUR3END3BUF2bs2nn3cur1p2Hn5lxv17SS2sp2PP3CUR1P3END2bs3NZ13NZ23SPR2nn3cur1p2Hp2Hn4CPOS4lxv04lxv15lxv172H82H93H153H16S2sp2PP3CUR3END3BUF2bs2nn3cur1p2Hn5lxv17S2sp2PP3CUR3END2bs2nn3cur1p2Hn5lxv162H33H11S2sp2PP3cur2xw3HxwS2sp2PP3CUR3END3BUF2bs3NZ13NZ23SPR2nn3cur1p2Hn3B3'4CPOS4lxv04lxv15lxv175lxv182H73H113H20S2sp2PP3CUR3END2bs3cur1p2Hn2H6S2sp2PP3CUR3END2bs2nn3cur1p2Hn3lxv2H33H11S2sp2PP3CUR1P3END3BUF2bs3NZ13NZ23SPR2nn3cur1p2Hp2Hn3B1'4CPOS4lxv05lxv173H123H21S2sp2PP3CUR1P3END3BUF2bs3NZ13NZ23SPR2nn3cur1p2Hp2Hn3B1'4CPOS4lxv05lxv173H113H20S2sp2PP3CUR1P3END3BUF2bs3NZ13NZ23SPR2nn3cur1p2Hp2Hn3B1'4CPOS4lxv05lxv173H123H21S2sp2PP3CUR1P3END3BUF2bs3NZ13NZ23SPR2nn3cur1p2Hp2Hn3B1'4CPOS4lxv05lxv173H123H21". (* [comment removed for export] *)
      Lemma LOOP : forall nn, KH nn.
      Proof.
        induction nn as [|nn IHn]; unfold KH; intros until x31; intros HHc HTc MFc HPXc MIc STc FC FL SV PPc Hp BYc ND HFR HCF HHD HSG HCUR HCB PR Hn;
          pose proof (heap_mok _ _ HI _ _ _ _ HHc) as MK; pose proof LOSP as LOSP'; pose proof B1 as B1'; pose proof B2 as B2'; pose proof B3 as B3'; pose proof B4 as B4';
          pose proof PPB as PPB'; pose proof AL1 as AL1'; pose proof NZ1 as NZ1'; pose proof NZ3 as NZ3'; pose proof D2 as D2'; pose proof DS1 as DS1'; pose proof DS3 as DS3';
          pose proof SP16 as SP16'; pose proof SPR as SPR'; pose proof SPP as SPP'; pose proof CEIL as CEIL'; pose proof DHI as DHI'; pose proof DIM1 as DIM1'; pose proof DIM2 as DIM2';
          pose proof HCF as HCF'; (flat constr:(HCF') 7%nat; flclear HCF'; intros CAL CPOS C64 CPP CBF CSTK _);
          clear MI ST; lazymatch type of HPP with ?T => change (lx_hidden T) in HPP end; lazymatch type of HCR with ?T => change (lx_hidden T) in HCR end;
          lazymatch type of BY with ?T => change (lx_hidden T) in BY end;
          unfold HREGS; unfold seq_cells in HCUR;
          assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) [SUM_gettagP; SUM_bcmpBP U_BCMP])
            by (intros AL; repeat constructor; apply apply_summary_sound; first [apply sum_gettagP_valid | apply sum_bcmpBP_valid; exact U_bcmp_spec]).
        - (* [comment removed for export] *)
          rewrite TP. apply (lxp_aevtM_of_evt usegs moc _ _ MK).
          lx_run_tac (PLANS [0x2762c] [] 60%N [SUM_gettagP; SUM_bcmpBP U_BCMP]); lx_tree.
          all: apply evt_done; cbv beta; rewrite <- TP.
          all: lazymatch goal with
               | |- aevtM _ _ _ (MS _ _ (ret_pc _) _ _ ?mx _) => lsync mx; leaf_ret mx
               | |- _ => exfalso; cbn in Hn; flia
               end.
        - rewrite TP. apply (lxp_aevtM_of_evt usegs moc _ _ MK).
          lx_run_tac (PLANS [0x276a0; 0x46940] [] 120%N [SUM_gettagP; SUM_bcmpBP U_BCMP]); lx_tree.
          all: apply evt_done; cbv beta; rewrite <- TP.
          (* [comment removed for export] *)
          all: lazymatch goal with
               | |- aevtM _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?pp2) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ (Z_to_bv 64 0x46940) _ _ ?mx _) =>
                   lazymatch goal with HB : bytes_at _ mx BUF bs, MIx : mem_inv _ mx |- _ =>
                     let QBY := fresh "QBY" in let QLEN := fresh "QLEN" in
                     destruct (bytes_at_sliceK mx BUF bs pp2 4 HB ltac:(flia) ltac:(clear; lia) ltac:(flia)) as [QBY QLEN];
                     let ROD := fresh "ROD" in ro_const 0x10b9c 4%nat ROD;
                     let SPB := fresh "SPB" in pose proof U_bcmp_spec as SPB; unfold memcmp_stmt in SPB;
                     eapply aevtM_cut_evt;
                     [ exact MK
                     | eapply SPB; rewrite ?unsigned_lit by flia; [exact ROD | exact QBY | reflexivity | apply Nat2Z.inj; rewrite QLEN; reflexivity]
                     | clear SPB; let ms' := fresh "ms" in let PO := fresh "PO" in intros ms' PO;
                       let r := fresh "rb" in let Hr := fresh "Hrb" in
                       (flat constr:(PO) 10%nat; flclear PO; intros ? ? ? ? ? r -> -> Hr _);
                       replace (ret_pc (Z_to_bv 64 0x27698)) with (Z_to_bv 64 0x27698 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]);
                       clear QBY QLEN ROD;
                       rewrite TP; apply (lxp_aevtM_of_evt usegs moc _ _ MK);
                       lx_run_tac (PLANS [0x276a0] [] 60%N [SUM_gettagP; SUM_bcmpBP U_BCMP]); lx_tree;
                       [> apply evt_done; cbv beta; rewrite <- TP ..] ]
                   end
               | |- _ => idtac
               end.
          all: try lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
          all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => lsync mx end.
          all: lazymatch goal with
               | |- aevtM _ _ _ (MS _ _ (ret_pc _) _ _ ?mx _) => leaf_ret mx
               | |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 0x276a0) _ _ ?mx _) =>
                   lazymatch goal with HHl : HEAP _ _ _ ?hc (nLBof ?nodes) mx ?moc, HCF : curF ?nodes' ?cur |- _ =>
                   lazymatch goal with HP : rw_cells _ mx PP _, HC : rw_cells _ mx cur _, STx : stk _ mx lo _, MIx : mem_inv _ mx,
                                       HF0 : rw_cells _ mx (bv_unsigned sp + -128) _, HFL : rw_cells _ mx (bv_unsigned sp + -112) _, HSV : rw_cells _ mx (bv_unsigned sp + -104) _,
                                       HB : bytes_at _ mx BUF bs, ND : List.NoDup nodes, HFR : nfresh nodes,
                                       HHDl : headrep mx _, HSGl : seq_lseg _ mx _ BUF END _ _, HPXl : heap_presx _ _ LB (bv_unsigned sp) _ m mx |- _ =>
                     eapply (L_CA4 nn IHn mx moc hc nodes cur);
                     [exact HHl| eassumption| eassumption| exact HPXl| exact MIx| exact STx| exact HF0| exact HFL| exact HSV| exact HP| exact HB| exact ND| exact HFR| exact HCF
                     | exact HHDl| exact HSGl| exact HC| eassumption| first [eassumption| right; reflexivity]| flia| flia| flia| flia| flia| cbn in Hn; flia]
                   end end
               end.
      Qed.
      Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    End Loop.

    (* [comment removed for export] *)
    Ltac fix_cell_lits H :=
      repeat match type of H with context [C8 (Z_to_bv 64 (Zpos ?p))] =>
        let z := constr:(Zpos p) in
        lazymatch eval compute in (Z.leb (2^63) z) with
        | true => let z' := eval compute in (z - 2^64)%Z in replace (Z_to_bv 64 z : word) with (Z_to_bv 64 z' : word) in H by (apply zbv_mod; reflexivity)
        end end.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@L11077385241.167L19031124607.158L19031124607.162L19031124607.164L19034877189.167L34326800225.179L35266223995.178L38996969702.136L41376807024.124L43055550123.134L47569862681.162L47569862681.164L4867664624.158 L4867664624.162 L4867664624.164 L4867664624.172 L4867664624.174 L4867664624.176 L5003221353.124 L57626602889.5  L62958990543.124L6394595208.124 L66025898159.119L67184963128.124L68297731981.15800000S01201Q02102R02`02n03<03M03c04104?04@04A04B04C04D04E04W04i05<05R06B06W070S2sp2PP3CUR3END2bs3NZ13NZ23SPR4lxv0S2sp2PP3CUR1P3END2bs4lxv02H82H9S2sp2PP3CUR1P3END2bs4lxv02H82H9S2sp2PP3CUR1P3END2bs4lxv02H93H10S2sp2PP3CUR1P3END2bs4lxv03H103H11S2sp2PP3CUR2bsS2sp2PP3CUR2bsS2sp2PP3CUR2bsS2sp2PP3CUR2bs2D1S2sp2PP3CUR2lo2bs4LOSPS2sp2PP3CUR2bsS2sp2PP3CUR2bsFFFFFFS2sp2PP3CUR2bs3NZ2S2sp2PP3CUR2xw3HxwS2sp2PP3CUR2bs4CURBS2sp2PP3CUR2lo2bs4SCURS1L2sp2PP3CUR2lo2bs3NZ13NZ23SPR5LOSP'4ACP'5CEIL'S2sp2PP3CUR3BUF2bs2D3S2sp2PP3CUR2bs3lxv2H33H11". (* [comment removed for export] *)
    Lemma ENTRY : ltac2:(CDefT.buildp (gd_tbl_P_x509_policies ()) "Pt0,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Pa3,(14.&40.)Pa4,(14.&40.)Pa5,(14.&40.)Pa6,(14.&40.)Pa7,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)(41.$1<.Vmo,(42.$1<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(43.(44.Vra,Vsp,Vgp,Vtp,R<.R;.R:.Vs0,Vs1,(3?.&40.VPP,)(3?.&40.VEND,)(3?.&40.VCUR,)R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(3?.&40.+27518.)Vfc,(46.(14.&40.))Vm,(47.$1<.)))")
(* [comment removed for export] *).
    Proof.
      intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
      pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof LOSP as LOSP'. pose proof alloc_ceiling_pos as ACP'.
      pose proof B1 as B1'. pose proof B2 as B2'. pose proof B3 as B3'. pose proof B4 as B4'. pose proof D1 as D1'. pose proof D2 as D2'. pose proof D3 as D3'. pose proof AL1 as AL1'. pose proof AL2 as AL2'.
      pose proof NZ1 as NZ1'. pose proof NZ2 as NZ2'. pose proof NZ3 as NZ3'. pose proof PPB as PPB'. pose proof CURB as CURB'. pose proof SLO2 as SLO2'. pose proof HLS as HLS'.
      pose proof DHI as DHI'. pose proof DIM1 as DIM1'. pose proof DIM2 as DIM2'. pose proof SP16 as SP16'. pose proof SPTOP as SPTOP'. pose proof DS1 as DS1'. pose proof DS2 as DS2'. pose proof DS3 as DS3'.
      pose proof SPR as SPR'. pose proof CEIL as CEIL'. pose proof SPP as SPP'. pose proof SCUR as SCUR'.
      pose proof (unsigned_lit (bv_unsigned sp + -128) ltac:(lia)) as USP.
      (* [comment removed for export] *)
      pose proof HH as HHc. change (HEAP usegs L HI h (nLBof []) m mo) in HHc.
      assert (HTc : heap_top usegs L HI h = heap_top usegs L HI h) by reflexivity. pose proof (mo_frame_refl mo) as MFc.
      pose proof (heap_presx_refl usegs L LB (bv_unsigned sp) X0 m) as HPXc.
      assert (HCF : curF [] CUR).
      { unfold curF. split; [exact AL2'|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. left. split; reflexivity. }
      assert (HFR : nfresh []) by (intros x Hx; destruct Hx).
      assert (ND : List.NoDup (@nil Z)) by constructor.
      assert (HHD : headrep m []) by (left; reflexivity).
      assert (HSG : seq_lseg usegs m (nLBof []) BUF END (removelast []) (last [] 0)) by exact I.
      pose proof BY as BYc. pose proof ST as STc. pose proof MI as MIc. pose proof HPP as PPc. pose proof HCR as HCUR. unfold seq_cells in HCUR.
      lazymatch type of HPP with ?T => change (lx_hidden T) in HPP end. lazymatch type of HCR with ?T => change (lx_hidden T) in HCR end.
      lazymatch type of BY with ?T => change (lx_hidden T) in BY end. lazymatch type of ST with ?T => change (lx_hidden T) in ST end.
      lazymatch type of MI with ?T => change (lx_hidden T) in MI end.
      (* [comment removed for export] *)
      carve_frame 128%nat STc.
      lazymatch type of FR with rw_cells usegs ?mx ?A [CB 128 ?j] =>
        set (JJ := j) in FR; clearbody JJ;
        change (rw_cells usegs mx A ([] ++ CB 128 JJ :: [])) in FR;
        apply (rw_cells_split_CB usegs mx A [] 128 JJ [] [8; 8; 8; 104]%nat) in FR; [| reflexivity]; cbn [mk_CB_cells app] in FR end.
      lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: _) => cb8_to_c8 FR [c0; c1] end.
      lazymatch type of FR with rw_cells _ _ _ [?c0; ?c1; C8 ?w; ?c3] => set (lw0 := w) in FR; clearbody lw0 end.
      (* [comment removed for export] *)
      assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) [SUM_gettagP])
        by (intros AL; repeat constructor; apply apply_summary_sound; apply sum_gettagP_valid).
      rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
      lx_run_tac (PLANS [0x27628] [] 100%N [SUM_gettagP]); lx_tree.
      all: apply evt_done; cbv beta; rewrite <- TP.
      all: try lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
      all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => lsync mx end.
      all: lazymatch goal with
           | |- aevtM _ _ _ (MS _ _ (ret_pc _) _ _ ?mx _) => leaf_ret mx
           | |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 0x27628) _ _ ?mx _) =>
               fix_regs;
               lazymatch goal with HHl : HEAP _ _ _ _ _ mx _, HP : rw_cells _ mx PP [C8 (Z_to_bv 64 ?p1)], HC : rw_cells _ mx CUR _, STx : stk _ mx lo (bv_unsigned sp + -128), MIx : mem_inv _ mx,
                                   HF : rw_cells _ mx (bv_unsigned sp + -128) _, HB : bytes_at _ mx BUF bs,
                                   HHDl : headrep mx _, HSGl : seq_lseg _ mx _ BUF END _ _, HPXl : heap_presx _ _ LB (bv_unsigned sp) _ m mx |- _ =>
                 let HFL := fresh "FL" in let HSV := fresh "SV" in
                 splitat HF 2%nat HFL; splitat HFL 1%nat HSV; fix_cell_lits HF;
                 eapply (LOOP (Z.to_nat (END - p1)) mx mo h [] CUR);
                 [exact HHl| reflexivity| apply mo_frame_refl| exact HPXl| exact MIx| exact STx| exact HF| exact HFL| exact HSV| exact HP| flia| exact HB| exact ND| exact HFR| exact HCF
                 | exact HHDl| exact HSGl| exact HC| left; repeat split; reflexivity| left; reflexivity| flia]
               end
           end.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Body.

  Theorem U_x509_policies_spec : x509_policies_stmt usegs L HI U_X509_POLICIES.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mo h LB PP CUR P END BUF lo bs ct cpad
           HH HPP HCR BY B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO CEIL SPTOP SP16 DHI DIM1 DIM2 SPP SCUR DS1 DS2 DS3 CW1 CW2 CRB TP MI -> -> ->.
    unfold U_X509_POLICIES.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2 ^ 64) in SPR.
    eapply ENTRY; try eassumption.
  Qed.
End Walk.
