(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd MpiClient.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_copy P_mpi_mul_stmt P_mpi_mul_mpi.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_opnd A_mpi_journey A_mpi_journey2
     A_mpi_zeroize_and_free A_mpi_copy A_mpi_core_mul A_mpi_client A_mpi_mul_mpi_W.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_mpi_stmtA_c24 A_mpi_copy_c24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_mpi_mul_mpi_defs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxA LxSum.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxATac LxARt LxAEcpSums.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00044ad39b4a564a 1 1 16 3 0 1 80 1 81 1 8 37 4 66 4 69 4 70 4 71 4 79 4 82 4 83 64P006e562ebb1b24e4 1 1 16 3 0 1 80 1 81 1 8 37 4 66 4 69 4 70 4 71 4 79 4 82 4 83 64P00dc94399a53b67b 0 5 0 1 34 1 36 1 44 1 45 1P00e4d0155088187f 1 1 16 3 0 1 79 1 80 1 8 36 4 65 4 68 4 69 4 70 4 78 4 81 4 82 64P015170f219d62127 1 1 16 3 0 1 80 1 81 1 4 57 1 79 1 82 1 83 16P01a23db1d6848d8a 0 6 0 1 34 1 35 1 36 1 44 1 45 1P01cc1d5f2aedc14c 1 1 32 3 0 1 78 1 81 1 9 36 1 53 1 65 1 68 1 69 1 70 1 79 1 80 1 82 32P0217a8f6e812ea66 1 1 16 3 0 1 80 1 81 1 8 37 4 66 4 69 4 70 4 71 4 79 4 82 4 83 64P0238e7e17961c19f 1 1 16 3 0 1 80 1 81 1 4 57 1 79 1 82 1 83 16P0267f3453148de5c 0 4 0 1 32 1 44 1 45 1P028460bd582721e2 0 5 0 1 53 1 67 1 79 1 80 1P030e774b136b1c84 0 7 0 1 53 1 68 1 69 1 70 1 78 1 79 1P03f1742879baa1ab 0 6 0 1 34 1 35 1 36 1 44 1 45 1P0429ac5f98c06fd1 0 5 0 1 34 1 36 1 44 1 45 1P042e8943ca4645eb 0 7 0 1 53 1 68 1 69 1 70 1 78 1 79 1P0448b87ac608fb14 0 4 0 1 32 1 44 1 45 1P045c625c95415333 1 1 16 3 0 1 80 1 81 1 4 57 1 79 1 82 1 83 16P047eb11ff78c84dd 0 5 0 1 34 1 36 1 44 1 45 1P0484a377305ed34b 1 1 32 3 0 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P04af39d08409d7e6 1 1 32 3 0 1 78 1 81 1 9 36 1 53 1 65 1 68 1 69 1 70 1 79 1 80 1 82 32P04f4079a1831f072 1 1 32 3 1 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P06ca0689413ce183 0 5 0 1 53 1 67 1 79 1 80 1P06e442a42922cc41 0 6 0 1 35 1 41 1 55 1 67 1 68 1P06fdf7545e1c1f36 0 6 0 1 69 1 70 1 71 1 79 1 80 1P07343a41d8569341 0 5 0 1 34 1 36 1 44 1 45 1P0778111f7abc84b6 0 6 0 1 69 1 70 1 71 1 79 1 80 1P079257543b6d4c72 0 5 0 1 53 1 67 1 79 1 80 1P07b33266c7b7c003 0 5 0 1 53 1 67 1 79 1 80 1P07d43ec1c228432b 1 1 32 3 1 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P0866df50dc8abf7c 0 5 0 1 34 1 36 1 44 1 45 1P086ff582ff2c2400 0 3 0 1 38 1 44 1P08accc0bcffa79ec 0 6 0 1 53 1 68 1 70 1 78 1 79 1P08b8f666feb62b17 1 2 32 3 0 1 80 1 81 1 32 3 1 1 79 1 82 1 2 83 2 84 2P09ac3c70f40cb008 0 6 0 1 57 1 58 1 59 1 67 1 68 1P09dd30d963d78af4 1 1 16 3 0 1 69 1 70 1 8 47 4 51 4 58 4 59 4 60 4 68 4 71 4 72 64P0a3b6a44c78e5931 0 5 0 1 53 1 67 1 79 1 80 1P0aceaf83cde05ff1 0 6 0 1 34 1 35 1 36 1 44 1 45 1P0b2bbc50b9ef8b22 1 2 32 3 0 1 80 1 81 1 32 3 1 1 79 1 82 1 2 83 2 84 2P0bb3d7688321c94a 0 4 0 1 32 1 44 1 45 1P0c825f91a1d0db19 1 1 32 3 1 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P0c8e1babb1a54ee7 1 1 32 3 0 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P0cc7288d00ba1f48 0 6 0 1 69 1 70 1 71 1 79 1 80 1P0d04c6108a3e6808 1 1 32 3 0 1 78 1 81 1 9 36 1 53 1 65 1 68 1 69 1 70 1 79 1 80 1 82 32P0d30bd2beccc29f7 0 6 0 1 53 1 68 1 70 1 78 1 79 1P0d8521050c628cd3 0 5 0 1 34 1 36 1 44 1 45 1P0d86670c8be8e218 0 5 0 1 53 1 67 1 79 1 80 1P0dd2fd218e0cbd74 1 1 16 3 0 1 80 1 81 1 4 47 1 79 1 82 1 83 16P0dd5b328cbaa2cea 0 6 0 1 47 1 56 1 66 1 78 1 79 1P0eb2514def80c7a2 1 2 32 3 0 1 80 1 81 1 32 3 1 1 79 1 82 1 2 83 2 84 2P0f3bd67ad051cb97 0 6 0 1 69 1 70 1 71 1 79 1 80 1P0f9c500d04ef1c0b 1 1 16 3 0 1 79 1 80 1 4 56 1 78 1 81 1 82 16P0fa0b57033cfbebb 0 5 0 1 34 1 36 1 44 1 45 1P10ded3cd80b5face 0 4 0 1 32 1 44 1 45 1P11820fb685cfd34c 0 6 0 1 34 1 35 1 36 1 44 1 45 1P11b081f991c3bd38 1 1 32 3 1 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P12e2166a00489c28 0 6 0 1 34 1 35 1 36 1 44 1 45 1P1308f330c2fc43f7 0 6 0 1 47 1 56 1 66 1 78 1 79 1P1309cc228b11112d 0 4 0 1 32 1 44 1 45 1P133c2a516086ed9d 1 1 32 3 1 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P1346d58495fe23ed 0 6 0 1 53 1 68 1 70 1 78 1 79 1P13728795e9b9b271 1 1 16 3 0 1 80 1 81 1 4 47 1 79 1 82 1 83 16P1378329fdf876704 0 7 0 1 53 1 68 1 69 1 70 1 78 1 79 1P138a67f39045f9d7 0 6 0 1 69 1 70 1 71 1 79 1 80 1P144d33206611e7b9 0 6 0 1 69 1 70 1 71 1 79 1 80 1P14e2302f18a9ddf0 1 1 64 2 0 1 67 1 3 2 1 68 1 69 64P15002a3b3bebee70 0 6 0 1 34 1 35 1 36 1 44 1 45 1P162f3fdf4aabf892 1 2 32 3 0 1 80 1 81 1 32 3 1 1 79 1 82 1 2 83 2 84 2P1692b2b33ea5e0c5 1 1 16 3 0 1 79 1 80 1 4 56 1 78 1 81 1 82 16P186cb4b087a56c22 0 6 0 1 53 1 68 1 70 1 78 1 79 1P18c500d034b87a26 1 1 32 3 0 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P18f3c542e56678cd 0 5 0 1 34 1 36 1 44 1 45 1P193376550ed0329a 0 4 0 1 32 1 44 1 45 1P194bb62cc7313a3d 0 4 0 1 32 1 44 1 45 1P194bdc4a8ec99ea1 0 6 0 1 34 1 35 1 36 1 44 1 45 1P19512b65ffc0d58d 0 6 0 1 69 1 70 1 71 1 79 1 80 1P1b1c167243588327 0 6 0 1 34 1 35 1 36 1 44 1 45 1P1b7f9ea92052dd5f 1 1 16 3 0 1 80 1 81 1 8 37 4 66 4 69 4 70 4 71 4 79 4 82 4 83 64P1bad9c205be743f2 1 1 16 3 0 1 80 1 81 1 4 47 1 79 1 82 1 83 16P1bd03e571d22c0c8 1 1 64 2 47 1 68 1 3 0 1 67 1 69 64P1becafa35f9c8197 0 6 0 1 34 1 35 1 36 1 44 1 45 1P1c27340e81086b21 1 1 16 3 0 1 79 1 80 1 4 56 1 78 1 81 1 82 16P1e882f6f38f657a4 0 5 0 1 68 1 70 1 78 1 79 1P1e9ee5ef4145e5c2 0 6 0 1 35 1 41 1 55 1 67 1 68 1P200edf89ae6b86d6 0 6 0 1 34 1 35 1 36 1 44 1 45 1P201f80ff38fe9809 0 6 0 1 47 1 56 1 66 1 78 1 79 1P20a49e200b91f11b 0 6 0 1 48 1 69 1 71 1 79 1 80 1P20f9993642f85f15 0 6 0 1 53 1 68 1 70 1 78 1 79 1P2178e93882131b79 0 6 0 1 53 1 68 1 70 1 78 1 79 1P21ac9f4a7ce747b7 1 1 16 3 0 1 80 1 81 1 4 57 1 79 1 82 1 83 16P21c95a1d6f311345 1 1 32 3 0 1 78 1 81 1 9 36 1 53 1 65 1 68 1 69 1 70 1 79 1 80 1 82 32P2230768e0af15026 1 1 16 3 0 1 80 1 81 1 8 37 4 66 4 69 4 70 4 71 4 79 4 82 4 83 64P2235c62634c9775b 1 1 32 3 0 1 78 1 81 1 9 36 1 53 1 65 1 68 1 69 1 70 1 79 1 80 1 82 32P22bd8bfaa8234721 0 5 0 1 34 1 36 1 44 1 45 1P23ef5a83340e0814 1 1 16 2 16 1 44 1 3 0 1 45 1 46 16P23f62c93f3e78739 0 4 0 1 32 1 44 1 45 1P242383155ddae77a 1 1 16 3 0 1 80 1 81 1 4 57 1 79 1 82 1 83 16P2427f6b410c27697 0 6 0 1 47 1 56 1 66 1 78 1 79 1P245a63586b8ef676 0 5 0 1 34 1 36 1 44 1 45 1P246e211fbc48a3d4 0 4 0 1 32 1 44 1 45 1P2576103408613bef 0 5 0 1 53 1 67 1 79 1 80 1P25c487bd4b07ee4e 0 6 0 1 69 1 70 1 71 1 79 1 80 1P26624bc9a34282a1 1 1 32 3 0 1 68 1 71 1 9 37 1 47 1 51 1 58 1 59 1 60 1 69 1 70 1 72 32P2671bda1e55c6ad2 1 1 64 2 0 1 78 1 3 6 1 79 1 80 64P27f2c8fc463aed4a 0 5 0 1 34 1 36 1 44 1 45 1P287e2ead77f6900a 1 1 32 3 0 1 78 1 81 1 9 36 1 53 1 65 1 68 1 69 1 70 1 79 1 80 1 82 32P28aab7d6352d2873 1 1 32 3 0 1 78 1 81 1 9 36 1 53 1 65 1 68 1 69 1 70 1 79 1 80 1 82 32P28abf79388a526a4 0 5 0 1 53 1 67 1 79 1 80 1P28ba8b127b799a4a 1 1 32 3 0 1 78 1 81 1 9 36 1 53 1 65 1 68 1 69 1 70 1 79 1 80 1 82 32P28e0beb185bb9314 0 5 0 1 53 1 67 1 79 1 80 1P2917b5f04543028f 0 6 0 1 34 1 35 1 36 1 44 1 45 1P29362a8f338c5a4b 1 1 32 3 0 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P296de7545c23735d 0 7 0 1 53 1 68 1 69 1 70 1 78 1 79 1P2a4368b887ad2c07 0 6 0 1 69 1 70 1 71 1 79 1 80 1P2a72dc42ff21cc0a 1 1 32 3 0 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P2ab69fe0decb9244 0 6 0 1 48 1 69 1 71 1 79 1 80 1P2bb1b6da6c1c25f0 0 6 0 1 34 1 35 1 36 1 44 1 45 1P2c5654867128c452 0 6 0 1 34 1 35 1 36 1 44 1 45 1P2cc9d028426e727a 1 1 16 3 0 1 80 1 81 1 8 37 4 66 4 69 4 70 4 71 4 79 4 82 4 83 64P2d81652addd86696 0 5 0 1 53 1 67 1 79 1 80 1P2efc0ce7db5a4987 0 7 0 1 53 1 68 1 69 1 70 1 78 1 79 1P2f56ec9d11d995df 1 2 32 3 0 1 80 1 81 1 32 3 1 1 79 1 82 1 2 83 2 84 2P2fa49c4d54cb9add 0 6 0 1 48 1 69 1 71 1 79 1 80 1P3005eabee949b692 0 6 0 1 69 1 70 1 71 1 79 1 80 1P305fca6ecdefadae 0 5 0 1 53 1 67 1 79 1 80 1P30890e78a93f2911 0 6 0 1 69 1 70 1 71 1 79 1 80 1P30a021c09054daee 0 6 0 1 47 1 56 1 66 1 78 1 79 1P30c99510189445d0 0 7 0 1 36 1 57 1 58 1 59 1 67 1 68 1P30f6b20e5fc08bef 1 1 32 3 0 1 78 1 81 1 9 36 1 53 1 65 1 68 1 69 1 70 1 79 1 80 1 82 32P319272e2e2d9103b 0 5 0 1 34 1 36 1 44 1 45 1P31967d8dd37de181 0 5 0 1 53 1 67 1 79 1 80 1P3197aa16ad6c575c 1 1 16 3 0 1 80 1 81 1 8 37 4 66 4 69 4 70 4 71 4 79 4 82 4 83 64P31a9f13f59d4e500 1 1 16 2 0 1 44 1 3 4 1 45 1 46 16P31b0db49d476eb49 0 4 0 1 32 1 44 1 45 1P31f4f6f36066c70e 1 2 32 3 0 1 80 1 81 1 32 3 1 1 79 1 82 1 2 83 2 84 2P31fb66e670482c5b 0 5 0 1 34 1 36 1 44 1 45 1P329e1717519d9d9a 0 5 0 1 53 1 67 1 79 1 80 1P33ac8836040da394 1 1 32 3 0 1 68 1 71 1 9 37 1 47 1 51 1 58 1 59 1 60 1 69 1 70 1 72 32P34228229c879e9bc 0 6 0 1 69 1 70 1 71 1 79 1 80 1P344378a3e352ab0a 0 4 0 1 32 1 44 1 45 1P3449e8914939f07f 1 1 16 3 0 1 79 1 80 1 4 56 1 78 1 81 1 82 16P34617538812706a3 0 5 0 1 41 1 55 1 67 1 68 1P346d48927bd8fcc4 1 1 32 3 1 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P357bd8159f04dad9 0 6 0 1 34 1 35 1 36 1 44 1 45 1P36568d88ea2c59d7 0 7 0 1 36 1 57 1 58 1 59 1 67 1 68 1P375ad41fde5ef3fb 0 3 0 1 27 1 37 1P37dd8b5fe9d4a3ac 1 1 16 3 0 1 79 1 80 1 4 56 1 78 1 81 1 82 16P3856142a85978781 0 6 0 1 69 1 70 1 71 1 79 1 80 1P385ebf2e2b1c35cb 1 1 32 3 1 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P39c50a6283fc1ba5 0 4 0 1 32 1 44 1 45 1P39e6ffdd7c1b1f56 1 1 32 3 0 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P3a4758ed505a20e2 1 1 64 2 1 1 67 1 3 0 1 68 1 69 64P3b1a06fef03f4eb1 1 1 32 3 0 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P3be3f373bc5030b7 0 4 0 1 32 1 44 1 45 1P3c6fd2154f4d2fb0 0 5 0 1 34 1 36 1 44 1 45 1P3d387710a10a334b 1 1 64 2 9 1 78 1 3 0 1 79 1 80 64P3f4596f5c766c754 1 1 32 3 1 1 79 1 82 1 9 37 1 54 1 66 1 69 1 70 1 71 1 80 1 81 1 83 32P3f910ecc835b6cf1 0 4 0 1 32 1 44 1 45 1P3fb39a6a09fc5b8f 1 1 32 3 0 1 78 1 81 1 9 36 1 53 1 65 1 68 1 69 1 70 1 79 1 80 1 82 32N0065d4f27b832dd3N00bbb3b1bf9e8a04N00fb7026d5978fb4N03eb7a432283bc25N03ec9da2120e12aaN048bde07e165a3d5N04cceeaae31fd81aN04f35f82466dfa4dN0544bf74373246f2N05f3a5e41b7c4370N091fb20445d14aa1N0972601cdd99bfadN0997a12114e73660N09e8a2ee26e4ec82N0ae59e13f7869929N0ceb93490dbcb49aN0dab813a420dc528N0de7d48c3ea5f8aaN0e159d1f42cffb1eN0e5f089b4befb9efN0e68171ce285aa2fN0f7ee8418c97449dN1083dd7b583958f0N1102d0ab8c843017N1185d594349af55aN11bf25c7c1f06dcfN11df659dea80c8dbN132f23770dcb0c39N13be198e7f916b6cN14815d9d0455906aN158764f852b8b13fN15f4831de21114b2N1610181c5b6b603dN16607ea98083e09eN168f0fbbed20de21N179daa60854be5b9N180f5cc42ee06342N18ec2f1960592399N192167874f152a80N196c817dcd0acc90N19fe71edfcb5ce81N1af865f23dd072ccN1b61a1dfde3c038dN1b63cb5322fb7c33N1bf6fe5789040c5bN1fee9e06ceb5a604N20688a94ff8d92a4N222e12c1b7dde34cN231bbb9e12c36364N234861a9a308e265N23daf62cbdda03dcN23dd1bf3c7543b7bN25d1e445294dcf5bN2623b3cafa17e5a0N2703615ff1ba4816N27857e9bdfddea65N2792c65272fe705aN279b1db87f9786f2N27bb3a01bd93f2e4N27f49c0eb6beacd1N2838cfcd3660ee2bN28b6983d1ab2854cN2900832bb5c0a5b6N29d336317a229429N2adc3af5a9a64ef8N2b8f766046834420N2ba2645d5605151aN2cb37b6f89fc3cdaN2cc653422108f826N2e57e008897b01a7N2e855f0dbe50b2dfN2e99d77c5b74ed92N2f3f364cf68ebd52N2fcc8af58cff4f3dN2fec0d781139ff09N3071741b39929d5bN31e021ad8de81066N3210780e101a9cf3N32352abc604b9cd4N327734a85f4dd4b5N3295cabe08987397N347469c55e4dbfa7N349565a437fa9891N34a38737f97965c0N34a63f158cc55731N34c23c8c8ca83938N3583379c49c4b1d1N35907a9c04e6c6b2N359116300dba0eabN36c5023b31a1c0a6N37292804c0e2bf5fN376b4a192cca4b43N37a658b424edab1cN37e8e6dab631bbf3N393e4a131f3d0756N399fd188744359f1N3adc63bd0b16fb32N3c725c9b34531926N3cfb707be57085bdN3d3482ed732e3503N3db6fa7c17d366a5N3f419acd7f5b2afeN3fd303b7b1281448"%lxh.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_mpi_mul_mpi_c24 () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibA.ARt.HST"; "OSSVerify.KrLib.A.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.LibA.ARt.HM"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.LibA.ARt.hflag"; "OSSVerify.KrLib.LibA.ARt.havol"; "OSSVerify.KrLib.LibA.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.LibA.ARt.fresh_apart"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.C2"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Lib.Cells.C1"; "WalkM.Call.SPILLL"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.LibA.ARt.presW"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "WalkM.Call.S1P"; "OSSVerify.KrLib.A.A_mpi_mul_mpi_defs.A_MPI_MUL_MPI_E"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.LibA.ALazy.crange"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "OSSVerify.KrLib.A.A_mpi_mul_mpi_W.mm_fr"; "WalkM.Call.EPOST"; "Corelib.Lists.ListDef.Forall"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.LibA.ARt.fdata"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.Rep.LNull"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.A.A_mpi_client.cstateA"; "WalkM.Call.Fr.CSF"; "OSSVerify.KrLib.P.P_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "OSSVerify.KrLib.A.A_mpi_mul_mpi_defs.mul_mpi_PHI"; "OSSVerify.KrLib.A.A_mpi_mul_mpi_defs.mul_mpi_FR"; "Stdlib.ZArith.BinInt.Z.max"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpi_binop_postA"; "OSSVerify.KrLib.A.A_mpi_mul_mpi_defs.mul_mpi_Rs"; "OSSVerify.KrLib.LibA.AUnw.uwc"; "OSSVerify.KrLib.LibA.ARt.AVOL_CALL"; "OSSVerify.KrLib.LibA.ARt.fr_charge"; "OSSVerify.KrLib.LibA.ARt.AVOL_MAX"; "OSSVerify.KrLib.LibA.ARt.FR_MAX"; "Corelib.Init.Datatypes.nat"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.A.A_mpi_journey.JBA"; "OSSVerify.KrLib.A.A_mpi_journey.BJA"; "OSSVerify.KrLib.P.P_mpi_addsub.opnd_sep"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "OSSVerify.KrLib.Lib.Mem.wa"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.A.AImgGlobals.img_norz"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.MpiVal.md_limbs"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"; "OSSVerify.KrLib.A.A_mpi_mul_mpi_W.mul_mid_PHI"; "OSSVerify.KrLib.A.A_mpi_mul_mpi_W.mul_mid_FR"; "OSSVerify.KrLib.Lib.Frame.munch"; "OSSVerify.KrLib.Lib.Frame.wmono"; "WalkM.Call.Fr.ra_src"; "OSSVerify.KrLib.A.A_mpi_copy.copy_PHI"; "OSSVerify.KrLib.A.A_mpi_copy.copy_FR"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asan_img_ok"; "OSSVerify.KrLib.LibA.ARt.arl_uar_got"; "OSSVerify.KrLib.A.A_mpi_mul_mpi_defs.A_UAR_GOT_MM"; "OSSVerify.KrLib.LibA.ARt.arl_smalloc"; "OSSVerify.KrLib.A.A_mpi_mul_mpi_defs.A_SMALLOC_1_MM"; "OSSVerify.KrLib.LibA.ARt.arl_need_smalloc"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.A.A_mpi_zeroize_and_free.zeroize_and_free_stmtA"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_ZEROIZE_AND_FREE"; "OSSVerify.KrLib.A.A_mpi_copy_c24.mpi_copy_stmtA_c"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_COPY"; "OSSVerify.KrLib.A.A_mpi_core_mul.mpi_core_mul_stmtA"; "OSSVerify.KrLib.A.A_mpi_core_mul.A_MPI_CORE_MUL"; "OSSVerify.KrLib.LibA.ARt.arl_calloc"; "OSSVerify.KrLib.A.A_mpi_mul_mpi_W.A_WRAP_CALLOC_MM"; "OSSVerify.KrLib.LibA.ARt.arl_amemcpy"; "OSSVerify.KrLib.A.A_mpi_mul_mpi_W.A_ASAN_MEMCPY_MM"; "OSSVerify.KrLib.LibA.ARt.arl_amemset"; "OSSVerify.KrLib.A.A_mpi_mul_mpi_W.A_ASAN_MEMSET_MM"; "OSSVerify.KrLib.A.A_mpi_mul_mpi_defs.mpi_mul_mpi_stmtA"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_MUL_MPI"].


(* [comment removed for export] *)

(* [comment removed for export] *)


Section WalkM.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_MM.
  Hypothesis SM1 : arl_smalloc R 1 = A_SMALLOC_1_MM.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NEEDR : 0 <= arl_need_rt R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (X A B lo : Z).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 400 - arl_need_rt R.
  Hypothesis SLOS : lo <= bv_unsigned sp - 240 - arl_need_smalloc R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF < 512)%nat.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_MM in UARG; unfold A_SMALLOC_1_MM in SM1;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation FSHXL :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
     C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
     C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Definition SPILLL (FB : Z) (j0 j8 j16 j24 j32 j40 j48 j56 j96 j104 : word) : list cell := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "(0.$1.(2.O:.)(0.$1.(2.O9.)(0.$1.(2.O8.)(0.$1.(2.O7.)(0.$1.(2.O6.)(0.$1.(2.O5.)(0.$1.(2.O4.)(0.$1.(2.O3.)(0.$1.(2.(3.&40.(4.O;.+4:.)))(0.$1.(2.(3.&40.(4.O;.+20.)))(0.$1.(2.(3.&40.O;.))(0.$1.(2.(3.&40.(4.O;.+40.)))(0.$1.(2.O2.)(0.$1.(2.O1.)(0.$1.(2.(3.&40.O;.))(5.$1.))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Lms,$6.(7.$8.LFB,$8.(7.$8.Lsp1,$8.(7.(9.$:.VR,VHIA,)Lh1,(9.$:.VR,VHIA,)(7.P,(;.&40.)(<.(;.&8.))Lm1,P,(;.&40.)(<.(;.&8.))(7.(;.&40.)Lxra,(;.&40.)(7.(;.&40.)Lt0,(;.&40.)(7.(;.&40.)Lt1,(;.&40.)(7.(;.&40.)Lt2,(;.&40.)(7.(;.&40.)La0,(;.&40.)(7.(;.&40.)La1,(;.&40.)(7.(;.&40.)La2,(;.&40.)(7.(;.&40.)La3,(;.&40.)(7.(;.&40.)La4,(;.&40.)(7.(;.&40.)La5,(;.&40.)(7.(;.&40.)La6,(;.&40.)(7.(;.&40.)La7,(;.&40.)(7.(;.&40.)Lt3,(;.&40.)(7.(;.&40.)Lt4,(;.&40.)(7.(;.&40.)Lt5,(;.&40.)(7.(;.&40.)Lt6,(;.&40.)(7.(;.&40.)Lw0,(;.&40.)(7.(;.&40.)Lw1,(;.&40.)(7.(;.&40.)Lw2,(;.&40.)(7.(;.&40.)LpadA,(;.&40.)(7.(;.&40.)LpadB,(;.&40.)(7.(;.&40.)Lj0,(;.&40.)(7.(;.&40.)Lj8,(;.&40.)(7.(;.&40.)Lj16,(;.&40.)(7.(;.&40.)Lj24,(;.&40.)(7.(;.&40.)Lj32,(;.&40.)(7.(;.&40.)Lj40,(;.&40.)(7.(;.&40.)Lj48,(;.&40.)(7.(;.&40.)Lj56,(;.&40.)(7.(;.&40.)Lj96,(;.&40.)(7.(;.&40.)Lj104,(;.&40.)(=.(>.$6.R24.(?.(10.R1?.(3.&40.R22.)Vgp,Vtp,R1>.R1=.R1<.Vsp,(3.&40.R22.)R1;.R1:.R19.R18.R17.R16.R15.R14.(3.&40.R23.)Vs3,(3.&40.(11.(12.VR,)))(3.&40.(4.R23.+2:.))(3.&40.VB,)(3.&40.VX,)(3.&40.VA,)(3.&40.(4.(13.R23.+3.)(11.(12.VR,))))(3.&40.(4.R23.+20.))(3.&40.R23.)R13.R12.R11.R10.)VF,(3.&40.+9>::8.)Vfc,(14.(;.&40.))R20.(15.$:.)))(=.(=.(16.(17.(18.&40.Vsp,)+?0.)R22.)(16.R22.(17.(18.&40.Vsp,)+>0.)))(=.(>.$8.(19.R22.+20.)=)(=.(1:.$:.VR,VHIA,R21.VLB,(0.(1;.$8.$8.)(1<.$8.$8.R23.+80.)VLF,)R20.)(=.(>.P,$8.Sp(1=.$:.VR,VHIA,R21.)(1=.$:.VR,VHIA,Vh,))(=.(>.$8.(1>.$:.VR,VHIA,R21.)(1>.$:.VR,VHIA,Vh,))(=.(>.$8.(1?.$:.VR,VHIA,R21.)(1?.$:.VR,VHIA,Vh,))(=.(>.$8.(20.$:.VR,VHIA,R21.)(20.$:.VR,VHIA,Vh,))(=.(>.$8.(21.$:.VR,VHIA,R21.)(21.$:.VR,VHIA,Vh,))(=.(>.$8.(22.$:.VR,VHIA,R21.)(22.$:.VR,VHIA,Vh,))(=.Pmo,$23.(24.(25.$:.VR,VHIA,R22.R1.)(25.$:.VR,VHIA,Vh,R1.))(=.(>.$8.(19.R23.+40.)=)(=.(26.VR,VLB,VLF,R23.+80.)(=.(27.$:.R20.R23.(0.$1.(2.R?.)(0.$1.(2.R>.)(0.$1.(2.R=.)(5.$1.)))))(=.(27.$:.R20.(4.R23.+20.)(0.$1.(2.(3.&40.=))(0.$1.(28.(3.&40.+1.))(0.$1.(28.(3.&40.=))(0.$1.(29.R<.)(5.$1.))))))(=.(27.$:.R20.(4.R23.+40.)(0.$1.(2.(3.&40.=))(0.$1.(28.(3.&40.+1.))(0.$1.(28.(3.&40.=))(0.$1.(29.R;.)(5.$1.))))))(=.(27.$:.R20.(4.(13.R23.+3.)(11.(12.VR,)))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(5.$1.))))))))))))))))))(=.(27.$:.R20.(4.(18.&40.Vsp,)-68.)(0.$1.(2.Vs11,)(0.$1.(2.Vs10,)(0.$1.(2.Vs9,)(0.$1.(2.Vs8,)(0.$1.(2.Vs7,)(0.$1.(2.Vs6,)(0.$1.(2.Vs5,)(0.$1.(2.Vs4,)(0.$1.(2.Vs3,)(0.$1.(2.Vs2,)(0.$1.(2.Vs1,)(0.$1.(2.Vs0,)(0.$1.(2.Vra,)(5.$1.)))))))))))))))(=.(27.$:.R20.R22.(2;.R23.R:.R9.R8.R7.R6.R5.R4.R3.R2.R1.))(=.(2<.$:.R20.(4.R22.+78.)(4.(18.&40.Vsp,)-68.))(=.(2<.$:.R20.Vlo,R22.)(=.(2=.$:.R20.)(2>.$:.VR,VHIA,Vh,VLB,VLF,(18.&40.Vsp,)(2?.VR,)(5.$30.)Vm,R20.))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Ltac cb8_all H :=
    repeat (lazymatch type of H with
            | rw_cells ?sg ?mx ?A ?cs =>
                let rec go pre rest :=
                  lazymatch rest with
                  | CB 8 ?bs :: ?post => apply (rw_cells_CB8_C8 sg mx A pre bs post) in H; cbn [app] in H
                  | ?c :: ?post => go (pre ++ [c]) post
                  end in go (@nil cell) cs
            end).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01;0@D18607476203.121D18607476203.123D2457697676.151 D29569067328.151D30470095146.124D32458983511.151D32604263317.152D3386269608.150 D45702641177.150D50254960491.122D50254960491.124D560335984.78   D62011770190.152D62012280210.78 D68409558507.150D6897506286.150 L10646859417.10 L13424450160.138L15629616632.10 L19546883925.138L19980016842.10 L2275137097.0   L24131365019.134L24462168006.3  L27188209011.155L28987030758.74 L29738741675.1  L30470049078.145L33485826452.1  L33485826452.11 L36278886100.7  L42402910215.1  L43061657906.72 L43495095303.1  L45298099350.1  L47230721790.134L48117620902.135L48117620911.73 L48132302231.90 L51271499937.0  L5324112511.21  L55351494680.11 L57355539152.131L58127621921.0  L58790154276.10 L59308677456.12 L62018535662.1  L68330859864.1  L68345989594.144L6912107244.134 L9356559645.11  Q10533598597.80 Q10592386206.156Q1530342990.124 Q23937998252.80 Q24131365019.157Q24137657765.155Q30223088059.156Q32440833928.155Q35653441506.67 Q40271359350.124Q47241206720.80 Q48117620904.156Q48132302231.155Q56531220660.156Q59310664043.155Q59310664043.80 Q59321150548.156Q60109315147.67 Q6192914196.120 Q62012212072.124Q62022254708.80 Q6897428434.155 Q6912107244.157 Q9356560156.105 00000100200300E00W00i01D01E01W01X01Y01l02@02M02N02`02a03B03C03_04704804C04O04f05105505J05K05L05f05j06H06L06Q06_07A07c08E08F08l09<09=09>09T09^09a09f0:80:C0:n0;;0;F0;X0<40<?0<J0<U0<V0=50=E0=S0>50>W0>X0>Y0>Z0>[0>l0?80?B0?L0?W0?b0@3FFFS2LF2sp3LFB3sp12FBS2LF2sp3LFB3sp12H7S2LF2sp3LFB3sp12FBS1R3HIA2LF2sp3LFB3sp12h12FBFS2LF2sp3LFB3sp12FBFFS1R3HIA1h2LF2sp3LFBS1R2LF2sp3LFB3sp12FBS1R2LF2sp3LFBFS2LF2sp3LFB3sp12FBSS2LF2sp3LFB3SPR3sp14SP1R2FB2F02F8SS2LF2sp3LFB3SPR3sp12FB2F02F8S1R3HIA1h2sp3TOP3sp13SP1SS2LF3LFB2FBS2sp3sp13SP1S2LF2sp3LFB3sp12FB1c2HcS2LF2sp3LFBS2FBS2LF2sp3LFB3sp12H72FBFFS1R3NS12sp2lo4SLOS3sp13SP1S2spS1R5NEEDR2LF2sp2lo3SLO3LFB3SPRS2FBS3sp1S1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOSS2sp2r03SPA3sp11r4SP1M2H62H71q1H2q02H4S1R3ACV2FB2F02F1FSS1R2sp2lo4SLOS3sp13SP1S2FB2Kb2F0S1RS3sp1S2LF2sp3LFB3sp12FBS2LF3LFB2FBS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3SPR3sp13SP1S1R2LF2sp3LFBS2LF3LFB2FBS2LF2sp3LFB3sp12H7S1R3HIA1h2LF2sp3TOP3LFB4HTOPS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBFS1R3HIA1h2LF2sp2lo3TOP3LFB4HTOPS1R3HIA1h2LF3LFBS1R2LF3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOFFFFS1R2LF2lo3LOS3LFBS2LF3LFB3sp1S1R2LF3LFBS1R2LF3LFBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB3sp14SP1R". (* [comment removed for export] *)
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)P,(1:.$:.VR,VHIA,Vh,VLB,VLF,Vm,)P,(2<.$:.Vm,Vlo,(18.&40.Vsp,))P,(2=.$:.Vm,)(31.$:.(12.VR,)(1=.$:.VR,VHIA,Vh,)$32.(?.(10.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(3.&40.VX,)(3.&40.VA,)(3.&40.VB,)R<.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(3.&40.$33.)Vfc,(14.(;.&40.))Vm,(15.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH ST MI. unfold A_MPI_MUL_MPI_E. rt_facts.
    pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
    pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) as PRES.
    flat constr:(IMG') 3%nat. flclear IMG'. intros EGOT ELO EHI.
    (* [comment removed for export] *)
    zstep. carve_frame 224%nat ST.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose (lxi := lxA_img (arl_AL R) IMG).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x9e99c] [] 60%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    lx_carry.
    lx_align32 sp1.
    match goal with Hm : sp1 mod 32 = 0 |- _ => rename Hm into SP1M end.
    assert (SP1 : bv_unsigned sp - 240 <= sp1 <= bv_unsigned sp - 224)
      by (match goal with H1 : 0 <= sp1 + _, H2 : 0 <= - sp1 + _ |- _ => clear - H1 H2 SP1M SPA SPR end; Z.div_mod_to_equations; lia).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    try match goal with H : stk _ _ lo (bv_unsigned sp + -224) |- _ => rename H into ST end.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
        pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
        pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
        (flat constr:((hm_auar asegs R HIA h LB LF mc HHc)) 2%nat; intros UGOT UFLAG);
        pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
      end end.
    rewrite EGOT in GOT. rewrite UARG in UGOT.
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x67848; 0x67ce4; 0x68f10; 0x9bcf4; 0xa5364; 0xa7c28; 0x9eef8; 0x9eaa8; 0x9eabc; 0x9eac4; 0x9ee0c; 0x9ee4c; 0x9ee68; 0x9ee90] [(0x9ead0, DJoin); (0x9eaf0, DJoin); (0x9eb14, DJoin); (0x9eb1c, DJoin); (0x9eb70, DJoin); (0x9eb8c, DJoin); (0x9ebb0, DJoin); (0x9ebb8, DJoin); (0x9ec18, DJoin); (0x9ec4c, DJoin); (0x9ec60, DJoin); (0x9ec78, DJoin); (0x9ecb0, DJoin); (0x9ecc8, DJoin); (0x9ece0, DJoin); (0x9ed04, DJoin); (0x9ed18, DJoin); (0x9ed2c, DJoin); (0x9ed3c, DJoin); (0x9ed60, DJoin); (0x9ed78, DJoin); (0x9ed90, DJoin); (0x9eda0, DJoin); (0x9edd0, DJoin); (0x9ede8, DJoin); (0x9ee40, DJoin)] 400%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : presW _ _ _ _ _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    repeat match goal with H : context [al_sb AL + Z.shiftr ?f 3] |- _ => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) in H by (clear; lia) end.
    repeat match goal with |- context [al_sb AL + Z.shiftr ?f 3] => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) by (clear; lia) end.
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
    destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -224) ST ltac:(clear - SP1 SLOS NS1; lia)) as [ST1 ST2]. clear ST.
    replace (Z_to_bv 64 338680) with (Z_to_bv 64 (arl_smalloc R 1)) by (rewrite SM1; reflexivity).
    lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
    callrt sp1 (eapply (art_smalloc asegs R HIA 1) with (lo := lo) (sz := 96); rewrite ?(unsigned_lit sp1) by exact SP1R;
                first [ exact HHc | exact LFB | reflexivity | exact TPV | exact LOS | exact ST1
                | clear - SLOS SP1 TOP NS1; lia
                | clear; lia
                | assumption | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
    end.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SMALLOC-LEFT:" g end.
    clear ST1.
    lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
    clear HH.
    presA_transport HP1. clear HP1.
    lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
      (flat constr:(H) 9%nat; flclear H; intros h1 Ehcs Ehtop Estk Eflag Evol Efr HKI SMC) end.
    flat constr:(SMC) 8%nat. flclear SMC. intros FB junkf Ea0 F64 FRSH HH1 FRM FSH. lazymatch type of Ea0 with ?x = _ => subst x end.
    cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in FRSH, HH1, FRM, FSH.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases Kb; zify_cond Kb.
    2:{ exfalso. flat constr:(FRSH) 3%nat. intros F0 F1 _.
        try (change 18446744073709551615 with (Z.ones 64) in Kb; rewrite Z.land_ones in Kb by (clear; lia)).
        rewrite ?Z.mod_small in Kb by (clear - F0 F1 ALO ACV LOS SLO SPR; lia). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
    clear Kb.
    change (64 * 2 ^ 1) with 128 in *. change (8 * 2 ^ 1) with 16 in FSH. change (Z.to_nat 128) with 128%nat in FRM. change (Z.to_nat 16) with 16%nat in FSH.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    destruct (frame_factsA R HIA CS h1 LB LF m3 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS. change (128 - 40) with 88 in IND.
    pose proof (art_stk_high asegs R HIA) as STKH.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -224) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
    replace (bv_unsigned sp + -224 + 120) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
    lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -224) |- _ => release_frame FRa STx (bv_unsigned sp + -104); rename STx into STJ end.
    destruct (stk_split asegs m3 sp1 (sp1 + 120) (bv_unsigned sp + -104) STJ ltac:(clear - SP1; lia)) as [STlo SThi]. clear STJ.
    destruct (stk_carve asegs m3 sp1 (sp1 + 120) 120 STlo ltac:(clear; lia)) as [STlo' [jslot SPILL]].
    replace (sp1 + 120 - Z.of_nat 120) with sp1 in STlo', SPILL by (clear; lia). clear STlo STlo'.
    apply (rw_cells_split_CB asegs m3 sp1 [] 120 jslot [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in SPILL; [| reflexivity].
    cbn [mk_CB_cells app] in SPILL. cb8_all SPILL.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs m3 FB [] 128 junkf [] [8; 8; 8; 8; 8; 4; 4; 16; 8; 4; 4; 48]%nat) in FRM; [| reflexivity].
    cbn [mk_CB_cells app] in FRM.
    chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 3%nat TAC FRM3. chunk_split FRM3 1%nat RZC FRM4. chunk_split FRM4 3%nat TBC FREST.
    lazymatch type of TAC with rw_cells _ _ ?a _ => replace a with (FB + 32) in TAC by (clear; lia) end.
    lazymatch type of TBC with rw_cells _ _ ?a _ => replace a with (FB + 64) in TBC by (clear; lia) end.
    clear FLNK FREST RZC.
    cb8_to_c8 FHD (@nil cell).
    cbn [zcells] in FSH.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x67848; 0x67ce4; 0x68f10; 0x9bcf4; 0xa5364; 0xa7c28; 0x9eef8; 0x9eaa8; 0x9eabc; 0x9eac4; 0x9ee0c; 0x9ee4c; 0x9ee68; 0x9ee90] [(0x9ead0, DJoin); (0x9eaf0, DJoin); (0x9eb14, DJoin); (0x9eb1c, DJoin); (0x9eb70, DJoin); (0x9eb8c, DJoin); (0x9ebb0, DJoin); (0x9ebb8, DJoin); (0x9ec18, DJoin); (0x9ec4c, DJoin); (0x9ec60, DJoin); (0x9ec78, DJoin); (0x9ecb0, DJoin); (0x9ecc8, DJoin); (0x9ece0, DJoin); (0x9ed04, DJoin); (0x9ed18, DJoin); (0x9ed2c, DJoin); (0x9ed3c, DJoin); (0x9ed60, DJoin); (0x9ed78, DJoin); (0x9ed90, DJoin); (0x9eda0, DJoin); (0x9edd0, DJoin); (0x9ede8, DJoin); (0x9ee40, DJoin)] 400%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : presW _ _ _ _ _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    repeat match goal with H : context [al_sb AL + Z.shiftr ?f 3] |- _ => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) in H by (clear; lia) end.
    repeat match goal with |- context [al_sb AL + Z.shiftr ?f 3] => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) by (clear; lia) end.
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHX end.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    match goal with H : rw_cells _ m9 (FB + 32) _ |- _ => rename H into TA9 end.
    match goal with H : rw_cells _ m9 (FB + 64) _ |- _ => rename H into TB9 end.
    (* [comment removed for export] *)
    lazymatch type of TA9 with rw_cells _ _ _ [?c0; ?c1; CB 4 ?jb] => set (jA := jb) in TA9 end.
    lazymatch type of TB9 with rw_cells _ _ _ [?c0; ?c1; CB 4 ?jb] => set (jB := jb) in TB9 end.
    pose proof (rw_cells_split_C4 asegs m9 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) _ TA9) as TA2. cbn [app] in TA2.
    pose proof (P_mpi_mul_mpi.rw_cells_CB4_C4 asegs m9 _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) / 2 ^ 16))] jA [] TA2) as TA3. cbn [app] in TA3.
    pose proof (rw_cells_split_C4 asegs m9 _ [C8 (Z_to_bv 64 0)] (Z_to_bv 64 1) _ TB9) as TB2. cbn [app] in TB2.
    pose proof (P_mpi_mul_mpi.rw_cells_CB4_C4 asegs m9 _ [C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 1); C2 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) / 2 ^ 16))] jB [] TB2) as TB3. cbn [app] in TB3.
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 1) / 2 ^ 16)) with (Z_to_bv 64 0) in TA3, TB3 by (rewrite unsigned_lit by (clear; lia); reflexivity).
    clear TA9 TA2 TB9 TB2.
    apply evtA_done. unfold S1P, SPILLL.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
    do 16 eexists. exists (Z_to_bv 64 1102416563). do 2 eexists. exists (le_bytes_to_word jA), (le_bytes_to_word jB). do 10 eexists.
    split; [reflexivity|].
    split; [exact SP1|]. split; [exact SP1M|].
    split; [exact HH1|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
    split; [exact F64|]. split; [exact FRSH|].
    split; [exact FHD|]. split; [exact TA3|]. split; [exact TB3|].
    split; [exact FSHX|].
    split; [exact SAVE|]. split; [exact SPILL|]. split; [exact SThi|].
    split; [assumption|]. split; [assumption|].
    exact PRES.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition EPOST (h3 : HST asegs R HIA) (LBa LBb : list blk) (m0 m2x : mem) (WA WB : list ivl) (r : Z)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Lms,$6.(7.P,(;.&40.)(<.(;.&8.))Lm',P,(;.&40.)(<.(;.&8.))(7.(9.$:.VR,VHIA,)Lh4,(9.$:.VR,VHIA,)(7.(;.&40.)Lt0,(;.&40.)(7.(;.&40.)Lt1,(;.&40.)(7.(;.&40.)Lt2,(;.&40.)(7.(;.&40.)La1,(;.&40.)(7.(;.&40.)La2,(;.&40.)(7.(;.&40.)La3,(;.&40.)(7.(;.&40.)La4,(;.&40.)(7.(;.&40.)La5,(;.&40.)(7.(;.&40.)La6,(;.&40.)(7.(;.&40.)La7,(;.&40.)(7.(;.&40.)Lt3,(;.&40.)(7.(;.&40.)Lt4,(;.&40.)(7.(;.&40.)Lt5,(;.&40.)(7.(;.&40.)Lt6,(;.&40.)(=.(>.$6.R11.(?.(10.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(3.&40.O1.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(34.Vra,)Vfc,(14.(;.&40.))R10.(15.$:.)))(=.(2=.$:.R10.)(=.(2<.$:.R10.Vlo,(18.&40.Vsp,))(=.(2>.$:.VR,VHIA,O8.O7.VLF,(18.&40.Vsp,)(2?.VR,)O3.O5.R10.)(=.(2>.$:.VR,VHIA,O8.O6.VLF,(18.&40.Vsp,)(2?.VR,)O2.O4.R10.)(=.(>.P,$8.Sp(1=.$:.VR,VHIA,R?.)(1=.$:.VR,VHIA,O8.))(=.(>.$8.(1>.$:.VR,VHIA,R?.)(1>.$:.VR,VHIA,O8.))(=.(>.$8.(1?.$:.VR,VHIA,R?.)(1?.$:.VR,VHIA,O8.))(=.(>.$8.(20.$:.VR,VHIA,R?.)(20.$:.VR,VHIA,O8.))(=.(>.$8.(21.$:.VR,VHIA,R?.)(21.$:.VR,VHIA,O8.))(=.(>.$8.(22.$:.VR,VHIA,R?.)(22.$:.VR,VHIA,O8.))(=.Pmo,$23.(24.(25.$:.VR,VHIA,R10.R1.)(25.$:.VR,VHIA,O8.R1.))(1:.$:.VR,VHIA,R?.O6.VLF,R10.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01L0@D10777814275.160D2459732108.187 D2459793318.160 D32452690557.160D3376374386.159 D3386269615.187 D38320100953.187D43016287773.161D45717900227.159D62011770188.161D62022316111.187D68407932977.159D6911601204.159 L13312155929.183L13424450162.144L13424450175.148L17832996913.190L19546883927.144L19546883930.148L2275137097.0   L24131365012.144L24131365017.140L24592528161.8  L27188209011.164L30443457480.6  L35655538631.9  L38564635093.0  L39540652971.1  L39844638933.0  L4022451686.1   L40228640085.0  L42411609006.0  L47798928558.160L47801036031.160L48117620903.145L48117620904.141L48132302223.161L48132302231.160L50790580594.6  L5162232212.2   L60098763854.3  L62018535662.1  L67028235242.8  L6899380056.1   L6912107235.144 L6912107246.140 L9356559676.11  P5152549648.189 Q10592386204.165Q10592386207.169Q12191695080.189Q12191695088.190Q21715049793.190Q21715049817.189Q21721340005.166Q21721340008.170Q22358563588.168Q24131365012.170Q24131365017.166Q24137657765.164Q24137657789.168Q30132769282.190Q30147450662.166Q30223088057.165Q30223088058.169Q30871588746.187Q31314676345.164Q34796740410.169Q4125667684.186 Q4279611329.188 Q48117620905.169Q48117620906.165Q48132302223.168Q48132302231.164Q52741535643.187Q5935758158.188 Q59666529497.189Q59668625896.170Q60382659730.170Q60382659743.166Q60397339043.189Q60397339067.190Q64133651577.187Q67397950268.165Q6897428426.168 Q6897428434.164 Q6912107235.170 Q6912107246.166 Q7902384038.189 Q7902384062.190 Q7917062807.170 Q7917062810.166 00000B00C00D00V00W00X01301N01`02402H02I02[03203S04404504Q04m04n05905D05c06:06Q06j06k06o07007407507607707807Z08<08^09@09W09X09b09e0:D0:H0:S0:^0;I0;J0;U0;`0;a0;b0;c0;d0;e0;f0;g0<20<=0<H0<S0<T0<U0<`0<k0=;0=<0==0=J0=W0>90>[0?=0?_0?o0@<0@=0@>0@?0@@0@A0@B0@O0@P0@[0@f0A10A<0AP0Ad0B80BLS2LF2sp3LFB2FB3sp1FFS2LF2sp3LFB2FB3sp1FFS1R3HIA2LF2sp3LFB2FB3sp12h4S1R3HIA2LF2sp3LFB2h32FB3sp1S2LF2sp3LFB2FB3sp1S1R2LF2sp3LFB2FB3sp1S1R2LF2sp3LFB2FB3sp1FS2LF2sp3LFB2FB3sp1S2LF2sp3LFB2FB3sp11p2PBS2LF2sp3LFB2FB3sp13SPR4SP1R2F82F0S2LF2sp3LFB2FB3sp13SPR4SP1R2F82F0FS2LF2sp3LFB2FB3sp13SPR2F82F0S2LF2sp3LFB2FB3sp13SPR2F82F0SS2LF3LFB2FBS2LF3LFB2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP1S2LF2sp3LFB2FB3sp11c2HcS1R5NEEDR2sp2lo3LOS3SLOS1R3HIA1h2sp2lo3TOP5HTOP3SS2FBSS2FBSSFFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2sp2lo3LOS3SLOFS1R2lo3LOSS1RS1R5NEEDR2sp2lo3LOS3SLO3sp13SP1S2FBS2LF3LFB2FBS2LF3LFB2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRFS2LF3LFB2FBS2LF3LFB2FBFFFFFFFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBFFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FB1p2PBFFS2LF3LFB1p2PBS2LF3LFB1p2PBS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALOS2LF3LFB2FB1p2PBS2LF3LFB1p2PBFFFFFFS2LF3LFB1p2PBFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS1R2LF3LFB2FB3ALO2F1S1R2LF3LFB2FB3ALO2F1S1R2LF3LFB2FB3ALO2F1S1R2LF3LFB2FB3ALO2F1". (* [comment removed for export] *)
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Ph3,(9.$:.VR,VHIA,)PLBa,(35.$36.)PLBb,(35.$36.)Pm0,P,(;.&40.)(<.(;.&8.))Pm2x,P,(;.&40.)(<.(;.&8.))Pmm,P,(;.&40.)(<.(;.&8.))PWA,(35.$30.)PWB,(35.$30.)PFB,$8.Psp1,$8.Pxra,(;.&40.)Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa0,(;.&40.)Pa1,(;.&40.)Pa2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)Ps4v,(;.&40.)Ps5v,(;.&40.)Ps6v,(;.&40.)Ps7v,(;.&40.)Ps10v,(;.&40.)Ps11v,(;.&40.)Pw0,(;.&40.)Pw1,(;.&40.)Pw2,(;.&40.)Pc0,(;.&40.)Pc8,(;.&40.)Pc16,(;.&40.)Pc24,(;.&40.)Pc32,(;.&40.)Pc40,(;.&40.)Pc48,(;.&40.)Pc56,(;.&40.)Pk64,(;.&40.)Pk72,(;.&40.)Pk80,(;.&40.)Pk88,(;.&40.)Pk96,(;.&40.)Pk104,(;.&40.)Pk112,(;.&40.)Pr,$8.P,(1:.$:.VR,VHIA,R33.R31.(0.(1;.$8.$8.)(1<.$8.$8.R2;.+80.)VLF,)R2>.)P,Px,$8.P,(1=.$:.VR,VHIA,Vh,R1.)(1=.$:.VR,VHIA,R36.R2.)P,(>.$8.(1>.$:.VR,VHIA,R35.)(1>.$:.VR,VHIA,Vh,))P,(>.$8.(1?.$:.VR,VHIA,R36.)(1?.$:.VR,VHIA,Vh,))P,(=.(16.(17.(18.&40.Vsp,)+?0.)R2>.)(16.R2>.(17.(18.&40.Vsp,)+>0.)))P,(>.$8.(19.R2?.+20.)=)P,(>.$8.(19.R31.+40.)=)P,(26.VR,R39.VLF,R32.+80.)P,(26.VR,R39.VLF,R33.+80.)P,(37.(1=.$:.VR,VHIA,Vh,)R34.+80.)P,PB,$8.Pj,$8.P,(38.(1;.$8.$8.)(1<.$8.$8.R2.R1.)VLF,)(39.(16.(4.R38.+80.)R3.)(16.(4.R3.R2.)R38.))P,Pb',$36.P,(38.$36.R1.R3>.)(38.$36.R2.R3>.)P,(27.$:.R3:.R37.(0.$1.(2.R1?.)(0.$1.(2.R1>.)(0.$1.(2.R1=.)(5.$1.)))))P,(27.$:.R3;.(4.(13.R38.+3.)(11.(12.VR,)))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(5.$1.))))))))))))))))))P,(27.$:.R3<.(4.(18.&40.Vsp,)-68.)(0.$1.(2.Vs11,)(0.$1.(2.Vs10,)(0.$1.(2.Vs9,)(0.$1.(2.Vs8,)(0.$1.(2.Vs7,)(0.$1.(2.Vs6,)(0.$1.(2.Vs5,)(0.$1.(2.Vs4,)(0.$1.(2.Vs3,)(0.$1.(2.Vs2,)(0.$1.(2.Vs1,)(0.$1.(2.Vs0,)(0.$1.(2.Vra,)(5.$1.)))))))))))))))P,(27.$:.R3=.R39.(3:.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.))P,(27.$:.R3>.(4.R3:.+40.)(0.$1.(2.R18.)(0.$1.(2.R17.)(0.$1.(2.R16.)(0.$1.(2.R15.)(0.$1.(2.R14.)(0.$1.(2.R13.)(0.$1.(2.R12.)(5.$1.)))))))))P,(2<.$:.R3?.(4.R3;.+78.)(4.(18.&40.Vsp,)-68.))P,(2<.$:.R40.Vlo,R3<.)P,(2=.$:.R41.)P,(2>.$:.VR,VHIA,R47.R46.VLF,(18.&40.Vsp,)(2?.VR,)R41.R44.R42.)P,(2>.$:.VR,VHIA,R48.R46.VLF,(18.&40.Vsp,)(2?.VR,)R41.R44.R43.)(31.$:.(12.VR,)(1=.$:.VR,VHIA,R49.)(3;.R49.R48.R47.R46.R45.R43.R42.R17.)(?.(10.R3?.(3.&40.R40.)Vgp,Vtp,R3>.R3=.R3<.Vsp,(3.&40.R40.)R3;.R3:.R39.R38.R37.R36.R35.R34.(3.&40.R41.)(3.&40.R41.)R2?.R2>.R2=.R2<.(3.&40.R17.)(3.&40.(4.(13.R41.+3.)(11.(12.VR,))))R2;.R2:.R33.R32.R31.R30.)VF,(3.&40.+9>>90.)Vfc,(14.(;.&40.))R44.(15.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP SUBK FHD FSH SAVE SPLO SPHI SThi STlo MI PRES PRES2. unfold mm_fr in SPLO.
    rt_facts.
    pose proof (hcs_ok asegs R HIA h3) as CSOK3.
    pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3. rewrite ET3, ES3 in HTOP3.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    assert (CFB3 : crange (hcs asegs R HIA h3) FB 128) by (eapply crange_mono; [exact HCS3| exact CFB]).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NEEDR TOP HTOP3; lia]).
    assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
    assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
    destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 LBb LF mm FB 128 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS.
    pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'. flat constr:(FRSH') 4%nat. flclear FRSH'. intros F0 F1 F2 F3.
    pose proof (art_stk_high asegs R HIA) as STKH.
    pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
    (* [comment removed for export] *)
    pose (lxi := lxA_img (arl_AL R) IMG).
    assert (SFF : shadow_free R LBa LF (arl_stklo R) (hstkhi asegs R HIA h3) FB 128)
      by (eapply shadow_free_fresh; [exact FRSH | exact (proj2 (proj2 (proj2 PRES))) | clear; lia | clear; lia | exact ALO | exact AP]).
    assert (SFF2 : shadow_free R LBb LF (arl_stklo R) (hstkhi asegs R HIA h3) FB 128)
      by (eapply shadow_free_fresh; [exact FRSH3 | exact (proj2 (proj2 (proj2 PRES2))) | clear; lia | clear; lia | exact ALO | exact AP]).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x67848; 0x67ce4; 0x68f10; 0x9bcf4; 0xa5364; 0xa7c28; 0x9eef8; 0x9eaa8; 0x9eabc; 0x9eac4; 0x9ee0c; 0x9ee4c; 0x9ee68; 0x9ee90] [(0x9ead0, DJoin); (0x9eaf0, DJoin); (0x9eb14, DJoin); (0x9eb1c, DJoin); (0x9eb70, DJoin); (0x9eb8c, DJoin); (0x9ebb0, DJoin); (0x9ebb8, DJoin); (0x9ec18, DJoin); (0x9ec4c, DJoin); (0x9ec60, DJoin); (0x9ec78, DJoin); (0x9ecb0, DJoin); (0x9ecc8, DJoin); (0x9ece0, DJoin); (0x9ed04, DJoin); (0x9ed18, DJoin); (0x9ed2c, DJoin); (0x9ed3c, DJoin); (0x9ed60, DJoin); (0x9ed78, DJoin); (0x9ed90, DJoin); (0x9eda0, DJoin); (0x9edd0, DJoin); (0x9ede8, DJoin); (0x9ee40, DJoin)] 400%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : presW _ _ _ _ _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    repeat match goal with H : context [al_sb AL + Z.shiftr ?f 3] |- _ => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) in H by (clear; lia) end.
    repeat match goal with |- context [al_sb AL + Z.shiftr ?f 3] => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) by (clear; lia) end.
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
    (* [comment removed for export] *)
    match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
    destruct (hm_fake_free asegs R HIA h3 LBb ((FB, 128) :: LF) me FB 128 HHe ltac:(left; reflexivity))
      as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
    replace (FB + 128 - 8) with (FB + 120) in ROp by (clear; lia).
    pose proof (rw_cells_bound _ _ _ _ Hold) as PB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
    pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp. clear Hold.
    assert (SUB1 : forall b', In b' (LBa ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 128) :: LF))).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBK; exact Hb| right].
      eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
    assert (SUB2 : forall b', In b' (LBb ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 128) :: LF))) by (intros b' Hb; apply fdata_cons_sub; exact Hb).
    assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS NEEDR; lia| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
    assert (NP6 : sp1 + 64 <= p \/ p + 1 <= sp1).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS SP1 NEEDR; lia| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
    assert (NP7 : sp1 + 64 + 56 <= p \/ p + 1 <= sp1 + 64).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS SP1 NEEDR; lia| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
    assert (WCp1 : wcover R LBa LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| clear - LOS SLO NEEDR; lia]).
    assert (WCp2 : wcover R LBb LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| clear - LOS SLO NEEDR; lia]).
    clear HHe NCp NSp FHD.
    repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H | H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
    zstep. zstep.
    fake_free_done p HSp.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x67848; 0x67ce4; 0x68f10; 0x9bcf4; 0xa5364; 0xa7c28; 0x9eef8; 0x9eaa8; 0x9eabc; 0x9eac4; 0x9ee0c; 0x9ee4c; 0x9ee68; 0x9ee90] [(0x9ead0, DJoin); (0x9eaf0, DJoin); (0x9eb14, DJoin); (0x9eb1c, DJoin); (0x9eb70, DJoin); (0x9eb8c, DJoin); (0x9ebb0, DJoin); (0x9ebb8, DJoin); (0x9ec18, DJoin); (0x9ec4c, DJoin); (0x9ec60, DJoin); (0x9ec78, DJoin); (0x9ecb0, DJoin); (0x9ecc8, DJoin); (0x9ece0, DJoin); (0x9ed04, DJoin); (0x9ed18, DJoin); (0x9ed2c, DJoin); (0x9ed3c, DJoin); (0x9ed60, DJoin); (0x9ed78, DJoin); (0x9ed90, DJoin); (0x9eda0, DJoin); (0x9edd0, DJoin); (0x9ede8, DJoin); (0x9ee40, DJoin)] 400%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : presW _ _ _ _ _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    repeat match goal with H : context [al_sb AL + Z.shiftr ?f 3] |- _ => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) in H by (clear; lia) end.
    repeat match goal with |- context [al_sb AL + Z.shiftr ?f 3] => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) by (clear; lia) end.
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
    cbn [lb_remove fst Z.eqb] in HM4. rewrite Z.eqb_refl in HM4.
    apply evtA_done. unfold EPOST.
    exists mf, h4. do 14 eexists.
    split; [reflexivity|].
    split; [assumption|].
    split; [assumption|].   (* [comment removed for export] *)
    split; [exact PRES|]. split; [exact PRES2|].
    split; [rewrite E4cs; reflexivity|]. split; [exact E4top|]. split; [exact E4stk|]. split; [exact E4flag|]. split; [exact E4vol|]. split; [exact E4fr|].
    split; [exact HKI4|]. exact HM4.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (dX dA dB : mpd) (d : Z) (es : list mpd).
  Hypothesis XE : X = md_addr dX.
  Hypothesis AE : A = md_addr dA.
  Hypothesis BE : B = md_addr dB.
  Hypothesis HNDk : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis ROIMG : forall a, ro_addr asegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis H0M : HM asegs R HIA h LB LF m.
  Hypothesis NST : md_own dX <> LStatic.
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis W0AS : md_addr dX + 16 <= lo \/ bv_unsigned sp <= md_addr dX.
  Hypothesis W0BLK : md_own dX = LHeap -> In (md_p dX, 4 * md_n dX) LB /\ 1 <= md_n dX.
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis D0 : 0 <= d.

  Local Notation POSTM := (mpi_binop_postA asegs R HIA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB LF dX
                             (mul_mpi_Rs LB dX dA dB) (mul_mpi_PHI dX dA dB) (mul_mpi_FR d) lo m mo0).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L45094400112.7400000JS2LF2ra2sp3LFB2FB1n2B01j1K". (* [comment removed for export] *)
  Lemma fresh_apart_relist_m : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Ph3,(9.$:.VR,VHIA,)PLB',(35.$36.)Pm3,P,(;.&40.)(<.(;.&8.))PFB,$8.Pn,$8.P,(26.VR,VLB,VLF,R2.R1.)P,(1:.$:.VR,VHIA,R6.R5.(0.(1;.$8.$8.)(1<.$8.$8.R3.R2.)VLF,)R4.)(26.VR,R6.VLF,R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros h3 LB' m3 FB n (F0 & F1 & F2 & F3) HH. split; [exact F0|]. split; [exact F1|]. split; [exact F2|].
    intros B0 j Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [| apply F3; apply in_app_iff; right; exact Hb].
    flat constr:((hm_apart asegs R HIA h3 _ _ _ HH)) 2%nat. intros _ BA.
    pose proof (blocks_apart_app2 LB' ((FB, n) :: LF) (B0, j) (FB, n) BA Hb ltac:(left; reflexivity)) as K. cbn [fst snd] in K. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Section Fr.
  (* [comment removed for export] *)
  Variables (FB sp1 : Z) (w0 w1 w2 : word) (gapn : nat).
  Hypothesis SP1 : bv_unsigned sp - 240 <= sp1 <= bv_unsigned sp - 224.
  Hypothesis SP1M : sp1 mod 32 = 0.
  Hypothesis GAP : Z.of_nat gapn = bv_unsigned sp + -104 - (sp1 + 120).
  Hypothesis F64 : FB mod 64 = 0.
  Hypothesis FRSH : fresh_apart R LB LF FB 128.
  Hypothesis CFB : crange CS FB 128.
  Hypothesis APF : forall B0 j, In (B0, j) LF -> FB + 128 <= B0 \/ B0 + j <= FB.
  Hypothesis ESF : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "(3<.$3=.Le,$3=.(=.(3>.(3?.VR,)(40.$36.VLB,(41.VLF,))Vlo,(42.R1.)+10.)(=.P,(>.$43.(44.R1.)$45.)(=.(38.(1;.$8.$8.)(1<.$8.$8.(46.R2.)(47.+4.(48.R2.)))VLB,)(16.+1.(48.R2.)))(=.(39.(16.(4.(42.R1.)+10.)Vlo,)(16.(18.&40.Vsp,)(42.R1.)))(=.P,(>.$43.(44.VdX,)$45.)(39.(16.(4.(42.R2.)+10.)(46.VdX,))(16.(4.(46.VdX,)(47.+4.(48.VdX,)))(42.R2.)))(=.(39.(49.(>.$43.(44.VdX,)$45.))(39.(>.$43.(44.R1.)$4:.)(39.(16.(4.(46.VdX,)(47.+4.(48.VdX,)))(46.R1.))(16.(4.(46.R1.)(47.+4.(48.R1.)))(46.VdX,)))))(=.(39.(16.(4.(42.VdX,)+10.)(42.R1.))(16.(4.(42.R1.)+10.)(42.VdX,)))P,(49.(>.$43.(44.R1.)$4:.))(39.(16.(4.(42.VdX,)+10.)(46.R2.))(16.(4.(46.R2.)(47.+4.(48.R2.)))(42.VdX,)))))))))Ves,)")
(* [comment removed for export] *).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L34979112605.700000KS1R5NEEDR2sp2lo3SLO3sp13SP1". (* [comment removed for export] *)
  Let LOC : lo <= sp1. Proof. clear - SLO SP1 NEEDR. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L1540877545.300000<S2sp3sp13SP1". (* [comment removed for export] *)
  Let CSP : sp1 <= bv_unsigned sp. Proof. clear - SP1. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L9414545578.7500000JS2LF2ra2sp3LFB2FB3sp14gapn". (* [comment removed for export] *)
  Let FN64 : 64 <= 128. Proof. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L66151427842.1600000JS2FB2r03F641q1r1H2H02q02H4". (* [comment removed for export] *)
  Let FB8 : FB mod 8 = 0. Proof. clear - F64. Z.div_mod_to_equations. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation LF1 := ((FB, 128) :: LF).
  Local Notation CSTA := (A_mpi_client.cstateA asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es).
  Definition CSF (k64 k72 k80 k88 k96 k104 k112 : word) (gb : list byte) : list (Z * list cell) := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "(0.(1;.$8.(35.$1.))(1<.$8.(35.$1.)(4.Vsp1,+40.)(0.$1.(2.O8.)(0.$1.(2.O7.)(0.$1.(2.O6.)(0.$1.(2.O5.)(0.$1.(2.O4.)(0.$1.(2.O3.)(0.$1.(2.O2.)(5.$1.)))))))))(0.(1;.$8.(35.$1.))(1<.$8.(35.$1.)(4.Vsp1,+78.)(0.$1.(4;.Vgapn,O1.)(5.$1.)))(0.(1;.$8.(35.$1.))(1<.$8.(35.$1.)(4.(18.&40.Vsp,)-68.)(0.$1.(2.Vs11,)(0.$1.(2.Vs10,)(0.$1.(2.Vs9,)(0.$1.(2.Vs8,)(0.$1.(2.Vs7,)(0.$1.(2.Vs6,)(0.$1.(2.Vs5,)(0.$1.(2.Vs4,)(0.$1.(2.Vs3,)(0.$1.(2.Vs2,)(0.$1.(2.Vs1,)(0.$1.(2.Vs0,)(0.$1.(2.Vra,)(5.$1.)))))))))))))))(0.(1;.$8.(35.$1.))(1<.$8.(35.$1.)VFB,(0.$1.(2.Vw0,)(0.$1.(2.Vw1,)(0.$1.(2.Vw2,)(5.$1.)))))(5.(1;.$8.(35.$1.)))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L18547421326.10L26892418956.1 L55798526857.1 L59972714867.8 L62018535662.1 L64376833952.2 L7007546227.2  00000N00R00V00n01101901=S1R3HIA1h2dX2dA2dB2hq1v2HV3HVqS2spS2dWS1R3HIA1h1d2hq1f2HF4HFRqS1RS2sp3sp1S2dW". (* [comment removed for export] *)
  Lemma mm_EPIK : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pmq,P,(;.&40.)(<.(;.&8.))Phq,(9.$:.VR,VHIA,)PLBq,(35.$36.)Pls,(35.$3=.)PdW,$3=.Pv,$8.Pf,$8.Pr,$8.Pc0,(;.&40.)Pc8,(;.&40.)Pc16,(;.&40.)Pc24,(;.&40.)Pc32,(;.&40.)Pc40,(;.&40.)Pc48,(;.&40.)Pc56,(;.&40.)Pk64,(;.&40.)Pk72,(;.&40.)Pk80,(;.&40.)Pk88,(;.&40.)Pk96,(;.&40.)Pk104,(;.&40.)Pk112,(;.&40.)Pgb,(35.(;.&8.))Pxra,(;.&40.)Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa0,(;.&40.)Pa1,(;.&40.)Pa2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)Ps4v,(;.&40.)Ps5v,(;.&40.)Ps6v,(;.&40.)Ps7v,(;.&40.)Ps10v,(;.&40.)Ps11v,(;.&40.)P,(4<.$:.VR,VHIA,Vh,VLB,VLF,Vm,(18.&40.Vsp,)Vlo,Vsp1,VFB,+80.VdX,Ves,R2>.R2=.R2<.R2;.R2:.(4=.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(5.$1.)))))))))))))))))R29.R28.)P,(3<.$3=.Ldl,$3=.(>.$43.(44.R1.)$4:.)R2<.)P,(27.$:.R30.Vsp1,(3:.R28.R27.R26.R25.R24.R23.R22.R21.))P,(39.(>.$8.R2:.=)(>.$8.R2:.$4>.))P,(16.R2=.(4?.VdX,VdA,VdB,))P,(16.R2=.(50.Vd,))P,(16.(48.R30.)(51.(48.VdX,)(51.(4.(48.VdA,)(48.VdB,))+1.)))(52.$:.(53.$:.VR,VHIA,R34.Vmo0,)(54.$:.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,(55.VLB,VdX,VdA,VdB,)(4?.VdX,VdA,VdB,)(50.Vd,)Vlo,Vm,Vmo0,)(?.(10.R1=.(3.&40.Vsp1,)Vgp,Vtp,R1<.R1;.R1:.Vsp,(3.&40.Vsp1,)R19.R18.R17.R16.R15.R14.R13.R12.(3.&40.VFB,)(3.&40.VFB,)R=.R<.R;.R:.(3.&40.R2>.)(3.&40.(4.(13.VFB,+3.)(11.(12.VR,))))R9.R8.R11.R10.R?.R>.)VF,(3.&40.+9>>90.)Vfc,(14.(;.&40.))R35.(15.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until s11v. intros CST NUL SPLO HR HV HF HSZ. rt_facts.
    destruct (A_mpi_client.cs_final asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST NUL)
      as (HHq & HTq & HSq & HFq & HCSq & HVq & HFRq & MWq & OUTq & BKq & FRWq & PXq & MIq & STq & CHq & SHq).
    unfold CSF in CHq.
    apply Forall_cons_iff in CHq. flat constr:(CHq) 2%nat. flclear CHq. intros SPHI CHq. apply Forall_cons_iff in CHq. flat constr:(CHq) 2%nat. flclear CHq. intros GAPC CHq.
    apply Forall_cons_iff in CHq. flat constr:(CHq) 2%nat. flclear CHq. intros SAVE CHq. apply Forall_cons_iff in CHq. flat constr:(CHq) 2%nat. flclear CHq. intros FHD _.
    cbn [fst snd] in SPHI, GAPC, SAVE, FHD.
    assert (SThi : stk asegs mq (sp1 + 120) (bv_unsigned sp + -104)).
    { pose proof (stk_of_rw_cells asegs mq _ _ GAPC) as K. cbn [cells_size csize Nat.add] in K. rewrite Nat.add_0_r, GAP in K.
      replace (sp1 + 120 + (bv_unsigned sp + -104 - (sp1 + 120))) with (bv_unsigned sp + -104) in K by (clear; lia). exact K. }
    pose proof (fresh_apart_relist_m hq LBq mq FB 128 FRSH HHq) as FRSH3.
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] H0M ltac:(clear; lia)) as PRES0.
    pose proof (presW_sub_blocks asegs R HIA h LB (mpd_keep LB dX) LF _ _ _ m m PRES0 ltac:(intros b' Hb; eapply In_mpd_keep; exact Hb)) as (_ & C1 & C2 & C3).
    assert (PRESb : presW asegs R HIA h (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) [(md_addr dX, md_addr dX + 16)] m mq)
      by (split; [exact PXq| split; [exact C1| split; [exact C2| exact C3]]]).
    pose proof (presW_hmono R HIA h hq (mpd_keep LB dX) LF _ _ _ m _ PRESb HCSq HSq) as PRESb3.
    pose proof (presW_init_at R HIA hq _ _ LBq LF mq (bv_unsigned sp) (arl_stklo R) [] h HHq
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSq HSq ltac:(clear; lia)) as PRES2.
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    eapply (aevtA_cut_evtA_KF asegs R HIA hq mo0).
    { eapply epi_walk with (h3 := hq) (LBa := mpd_keep LB dX) (LBb := LBq) (r := r) (WA := [(md_addr dX, md_addr dX + 16)]) (WB := []) (m0 := m) (m2x := mq);
        first [ exact HHq | exact HCSq | exact PRESb3 | exact PRES2 | exact FRSH3 | exact CFB | exact APF | exact SPLO | exact SPHI | exact SThi | exact SAVE | exact FHD | exact SHq
              | exact HTq | exact HSq | exact SP1 | exact SP1M | exact F64 | exact STq | exact MIq
              | lazymatch goal with
                | |- fresh_apart _ (mpd_keep LB dX) LF FB 128 => apply fresh_apart_keep; exact FRSH
                | |- forall b', In b' (mpd_keep LB dX) -> In b' LBq => intros b' Hb; eapply mpd_keep_out; [exact OUTq| exact Hb]
                end
              | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold mpi_binop_postA.
    do 14 eexists. exists m9, mo9, h4, LBq, dW, r.
    split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|]. split; [exact MF9|].
    split; [pose proof (presW_presA asegs R HIA hq _ LF _ _ _ _ _ PRES9) as HPF; rewrite HSq in HPF; exact HPF|].
    split; [rewrite E4top; exact HTq|]. split; [rewrite E4stk; exact HSq|]. split; [rewrite E4flag; exact HFq|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSq x Hx)|].
    split; [rewrite E4vol; clear - HVq HV; lia|].
    split; [rewrite E4fr; clear - HFRq HF; lia|].
    split; [exact HH4|].
    flat constr:(OUTq) 5%nat. intros OU1 OU2 OU3 OU4 OU5.
    split.
    { flat constr:(MWq) 2%nat. intros FLt1 _. flat constr:(FLt1) 6%nat. flclear FLt1. intros CX3 _ _ _ _ OWN3.
      eapply (mpd_at_heap_presx asegs L) with (LBp := LBq ++ fdata LF) (SP := bv_unsigned sp) (XI := []);
        [exact MWq| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hq _ LF _ _ _ _ _ PRES29))| exact MIq| exact MI9| | | exact I| intros _; exact I|].
      - rewrite OU1. eapply client_range_temp; [eapply client_range_of_w; eapply mpd_writableA_keep; exact XW| clear; lia|].
        intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; eapply mpd_keep_out; [exact OUTq| exact Hb]| right; exact Hb].
      - intros EO. rewrite EO in OWN3. flat constr:(OWN3) 3%nat. flclear OWN3. intros N1 XIN _. eapply client_range_block; [apply in_app_iff; left; exact XIN| clear; lia| clear - N1; lia].
      - intros b' Hb. unfold mpd_blk in Hb. destruct (md_own dW) eqn:EO; try (destruct Hb; fail). destruct Hb as [<-|[]]. flat constr:(OWN3) 3%nat. flclear OWN3. intros _ XIN _. exact XIN. }
    split; [exact OUTq|]. split; [exact FRWq|].
    split; [split; [exact HR| exact BKq]| exact HSZ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Local Notation UWCM mq := (uwc asegs mq (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) (sp1 + 64) (d + 1)).
  Local Notation CSFC k96 k104 gb := (CSF (Z_to_bv 64 (FB + 74)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 FB) (Z_to_bv 64 (FB + 64)) k96 k104 (Z_to_bv 64 FB) gb).
  Local Notation SH9 := (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01G0@D11138851872.174D1162412691.173 D67430489183.173D67430489183.174L10711524986.182L13497978411.14 L14447275964.10 L1685717371.0   L16999276204.6  L18364504529.4  L19042919733.1  L23455076668.175L23455522467.181L23467742757.2  L23622172275.11 L2405434805.3   L2406438837.30  L25204003039.167L28494452040.1  L32354394574.168L33754013180.175L33880637158.1  L34449366402.10 L34673485611.1  L3482348703.30  L3483319967.1   L35663928186.7  L37131230209.1  L372066202.168  L38327628946.30 L39172636981.0  L39261862547.30 L3947075145.1   L39797113581.5  L40889598521.3  L41663468825.167L43646346876.175L45098265576.1  L46495298509.1  L46495921149.30 L49636034987.14 L51205686798.1  L52101693566.15 L52284635941.2  L53971187802.4  L56523586534.1  L56641043079.4  L56643561799.30 L576250137.175  L58046700543.2  L59308972243.3  L59918119559.14 L60098763854.3  L62018535662.1  L62037211595.7  L6203936179.1   L65232285359.1  L66081706166.218L67337568515.3  L9050757852.14  L9356559676.11  P14461423358.173P14461423358.174P58035951928.173P58035951928.174Q10596710310.178Q1107808484.172 Q11801279589.173Q11801279589.174Q13394240522.178Q17002805393.173Q18220167180.186Q20546156061.186Q20614549399.178Q25160678704.172Q25160678704.173Q29724111287.178Q34673729958.169Q38272766294.170Q40688686592.170Q41259381015.178Q49698585326.171Q49698585326.172Q55203889079.169Q66384264721.170Q7366406794.178 Q9961343543.171 00000b01T02F03803_04M04N04O04c04d04i04j05V05`06J06K06`07C07H07k08R08V09=09A09K09L09a09e0:H0:i0:j0;M0;Q0;`0;a0<D0<k0<o0=00=B0>00>40>h0?20?=0?A0?B0?a0@H0@I0@T0@]0@g0@j0AE0AJ0AN0B50BD0Bj0CU0E@0Fk0H80IE0Ib0JJ0K20KZ0L?0Lg0MD0Ma0NI0O10OY0P60PO0Pn0QG0Qo0RQ0S30SL0Se0TJ0TiS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn2HB5Ha_st5Hl_stS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn3dTAS1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1FSS1R3dTA3ACV2P02PC2N1FS3dTAFS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn3dTA4NRTAS3dTA4NRTAS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13dTA3ALO2PCFS1R2sp2lo3SLO3sp13SP1S2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapnS3sp1S2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapnS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn3dTAS2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS2FBS3sp14SP1MFS1R3HIA1h2sp2lo3TOP1HS2FBS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapnS1R3HIA1h1d3sp12hq1f2HF4BUDF4HFRqSS1R3HIA1h2dA2dB3sp12hq1v2HV3BUD3HVqS2FBS2dX2dA2dB1v2HVFS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapnS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn3dTAS2FBFS3sp13dTA4NRTA3NT1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S2FBS1R3HIA5NEEDR1h2sp2lo3LOS3SLO2FB3sp13SP13ALO2F11a2HaS3dTA4NRTAS1d2D01f2HFS2FBFS1R3HIA1h2sp3TOP3sp13SP12hq3HTqS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn3dTAFS3dTA2KZ2P0S2FB4gapnS1R2lo3LOSS1RS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S2FBS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn3dTAS3dTA5LENTA3NT1S1R5NEEDR2sp2lo3LOS3SLO2FB4gapn3ALO2F1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2dA2dB2FB3sp14gapn3SP12c02c83c163c243c323c403c483c563ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2dA2dB2FB3sp14gapn3SP12c02c83c163c243c323c403c483c563ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2dA2dB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2dA2dB2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS2LF3LFB2dX2dA2dB2FB4gapn3dTAS2LF3LFB2dX2dA2dB2FB4gapn2HB5Ha_st5Hl_stS2LF3LFB2dX2dA2dB2FB4gapn2HB5Ha_st5Hl_stS2LF3LFB2dX2dA2dB2FB4gapn2HB5Ha_st5Hl_stS2LF2lo3LFB2dX2dA2dB3sp14gapn3LOC3dTAS2LF3LFB2dX2dA2dB2FB4gapn2HB5Ha_st5Hl_stS2LF3LFB2dX2dA2dB2FB4gapn3dTAS2LF3LFB2dX2dA2dB2FB4gapn3dTAS2LF2sp2lo3LFB2dX2dA2dB3sp14gapn3SP13dTAS2LF3LFB2dX2dA2dB2FB4gapn2HB5Ha_st5Hl_stS2LF3LFB2dX2dA2dB2FB4gapn2HB5Ha_st5Hl_stS2LF3LFB2dX2dA2dB2FB4gapn3dTAS2LF3LFB2dX2dA2dB2FB4gapnS2LF3LFB2dX2dA2dB2FB4gapn2F02HBS2LF3LFB2dX2dA2dB2FB4gapnS2LF2sp2lo3LFB2dX2dA2dB3sp14gapn3SP13dTAS2LF3LFB2dX2dA2dB2FB4gapn2HB5Ha_stS2LF3LFB2dX2dA2dB2FB4gapn2HB5Ha_stS2LF3LFB2dX2dA2dB2FB4gapnS2LF3LFB2dX2dA2dB2FB4gapnS2LF2lo3LFB2dX2dA2dB3sp14gapn3LOC3dTAS2LF3LFB2dX2dA2dB2FB4gapn2F02HB". (* [comment removed for export] *)
  Lemma mm_CLEAN_B : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pmq,P,(;.&40.)(<.(;.&8.))Phq,(9.$:.VR,VHIA,)PLBq,(35.$36.)PdTA,$3=.PdW,$3=.Pv,$8.Pf,$8.Pr,$8.Pc0,(;.&40.)Pc8,(;.&40.)Pc16,(;.&40.)Pc24,(;.&40.)Pc32,(;.&40.)Pc40,(;.&40.)Pc48,(;.&40.)Pc56,(;.&40.)Pk96,(;.&40.)Pk104,(;.&40.)Pgb,(35.(;.&8.))Ptp0,$8.Pts0,$8.Ptn0,$8.Ptpad,(;.&40.)Pxra,(;.&40.)Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa0,(;.&40.)Pa1,(;.&40.)Pa2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)Ps4v,(;.&40.)Ps6v,(;.&40.)Ps7v,(;.&40.)Ps10v,(;.&40.)Ps11v,(;.&40.)P,(4<.$:.VR,VHIA,Vh,VLB,VLF,Vm,(18.&40.Vsp,)Vlo,Vsp1,VFB,+80.VdX,Ves,R2<.R2;.R2:.(0.$3=.R29.(5.$3=.))R28.(4=.(3.&40.(4.VFB,+4:.))(3.&40.(4.VFB,+20.))(3.&40.VFB,)(3.&40.(4.VFB,+40.))R1<.R1;.(3.&40.VFB,)R1:.)(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(5.$1.)))))))))))))))))R27.R26.)P,(>.$8.(42.R2:.)(4.VFB,+20.))P,(27.$:.R2>.Vsp1,(3:.R26.R25.R24.R23.R22.R21.R20.R1?.))P,(27.$:.R2?.(4.VFB,+40.)(0.$1.(2.(3.&40.R1<.))(0.$1.(28.(3.&40.R1;.))(0.$1.(28.(3.&40.R1:.))(0.$1.(29.R19.)(5.$1.))))))P,(56.$:.R30.(2?.VR,)(1?.$:.VR,VHIA,Vh,)(18.&40.Vsp,)(4.Vsp1,+40.)(4.Vd,+1.))P,(39.(>.$8.R2:.=)(>.$8.R2:.$4>.))P,(16.(4.R2=.$57.)(4?.VdX,VdA,VdB,))P,(16.(4.R2=.(58.(4.Vd,+1.)))(50.Vd,))P,(16.(4.(21.$:.VR,VHIA,Vh,)(4?.VdX,VdA,VdB,))$59.)P,(16.(4.(22.$:.VR,VHIA,Vh,)(50.Vd,))$5:.)P,(16.(48.R32.)(51.(48.VdX,)(51.(4.(48.VdA,)(48.VdB,))+1.)))(52.$:.(53.$:.VR,VHIA,R36.Vmo0,)(54.$:.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,(55.VLB,VdX,VdA,VdB,)(4?.VdX,VdA,VdB,)(50.Vd,)Vlo,Vm,Vmo0,)(?.(10.R20.(3.&40.Vsp1,)Vgp,Vtp,R1?.R1>.R1=.Vsp,(3.&40.Vsp1,)R1<.R1;.R1:.R19.R18.R17.R16.R15.(3.&40.VFB,)(3.&40.(4.VFB,+40.))R10.(3.&40.(4.VFB,+2:.))R?.R>.(3.&40.R30.)(3.&40.(4.(13.VFB,+3.)(11.(12.VR,))))R=.R<.R14.R13.R12.R11.)VF,(3.&40.+9>>68.)Vfc,(14.(;.&40.))R37.(15.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until s11v. intros CST EAD SPLO TBC UW HR HV HF BUD BUDF HSZ. rt_facts.
    flat constr:((A_mpi_client.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST)) 5%nat. intros CHq SHq MIq STq HHq.
    flat constr:((A_mpi_client.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST)) 6%nat. intros HTq HSq HFq HCSq HVq HFRq.
    flat constr:(FRSH) 4%nat. intros F0 F1 F2 F3.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    pose proof (hm_top asegs R HIA hq _ _ _ HHq) as HTOPq.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 128) by (eapply crange_mono; [exact HCSq| exact CFB]).
    assert (IND : In (FB + 32, 88) (LBq ++ fdata LF1)) by (apply in_app_iff; right; cbn [fdata]; right; left; reflexivity).
    assert (CWT : client_wrange L (LBq ++ fdata LF1) (arl_stklo R) (htop asegs R HIA hq) (FB + 64) 16) by (eapply client_wrange_block; [exact IND| clear; lia| clear; lia]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    unfold CSF in CHq. apply Forall_cons_iff in CHq. flat constr:(CHq) 2%nat. flclear CHq. intros SPHI _. cbn [fst snd] in SPHI.
    (* [comment removed for export] *)
    assert (TBC' : rw_cells asegs mq (FB + 64) [C8 (Z_to_bv 64 tp0); CB 4 (le2 (Z_to_bv 64 ts0) ++ le2 (Z_to_bv 64 tn0)); C4 tpad]).
    { eapply rw_cells_reshape; [exact TBC| |].
      - cbn -[le2]. repeat split; try (rewrite ?length_app, !length_le2; reflexivity).
      - cbn -[le2 le4 le8]. rewrite <- ?app_assoc. reflexivity. }
    clear TBC.
    pose proof (munch_refl [(FB + 64, FB + 80)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    assert (HP2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(FB + 64, FB + 80)] mq m2).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HH2| | exact Hc]; clear; lia| exact MU| exact WM].
      unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact CFBq| clear; lia| clear; lia]| apply Forall_nil]. }
    assert (CST2 : CSTA m2 hq LBq [dTA] dW (CSFC k96 k104 gb) FSHXL v f).
    { eapply (A_mpi_client.cs_nop asegs R HIA) with (mq := mq) (WX := [(FB + 64, FB + 80)]); try eassumption.
      - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. split; [clear; lia|]. right. split; [clear; lia|]. split; [clear; lia|].
        intros d' [<-|[]]. right. rewrite EAD. clear. lia.
      - unfold CSF. repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add disjoint_from]; split; [| exact I]|]); [ | | | | apply Forall_nil].
        all: try (clear - SP1 F1 ALO LOS SLO NEEDR ACV GAP; lia). }
    assert (UW2 : UWCM m2).
    { eapply uwc_munch; [exact UW| exact MU| clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia|].
      intros a Ha. cbn [outside]. split; [clear - Ha F1 ALO LOS SLO SP1 NEEDR; lia| exact I]. }
    clear CST UW MU WM HP2. clear TBC'.
    edestruct (A_mpi_client.cs_local_facts asegs R HIA) with (i := 0%nat) (d := dTA) as (MTA & NSTA & _ & _ & _ & _ & HFTA & _); try eassumption; [reflexivity|].
    flat constr:(MTA) 2%nat. intros FLt2 SGTA. flat constr:(FLt2) 6%nat. flclear FLt2. intros CTA _ _ LENTA NRTA OWNTA. rewrite EAD in CTA. unfold mpi_cells in CTA. unfold MPI_MAX_LIMBS in NRTA.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      assert (EO : md_own dTA = LNull).
      { destruct (md_own dTA) eqn:EOT; [reflexivity| | exfalso; exact (NSTA eq_refl)]. exfalso.
        flat constr:((HFTA eq_refl)) 5%nat. intros P0 PC _ N1 _. rewrite Z.mod_small in KZ by (clear - P0 PC N1 ACV; lia). clear - KZ P0. lia. }
      eapply (mm_EPIK m2 hq LBq [dTA] dW v f r); [exact CST2| apply Forall_cons; [exact EO| apply Forall_nil]| exact SPLO| exact HR| | | exact HSZ].
      + unfold AVOL_CALL in HV. clear - HV. lia.
      + unfold fr_charge in HF. clear - HF D0. lia.
    - (* [comment removed for export] *)
      assert (EO : md_own dTA = LHeap).
      { destruct (md_own dTA) eqn:EOT; [exfalso; (flat constr:(OWNTA) 2%nat; flclear OWNTA; intros EP _); apply KZ; rewrite EP; reflexivity| reflexivity| exfalso; exact (NSTA eq_refl)]. }
      rewrite EO in OWNTA. flat constr:(OWNTA) 4%nat. flclear OWNTA. intros NT1 INT PAL ARRT.
      flat constr:((HFTA EO)) 6%nat. intros P0 PC _ _ BFT _.
      (* [comment removed for export] *)
      replace (FB + 42) with (FB + 32 + 10) by (clear; lia).
      zstep.
      replace (zx16 (Z_to_bv 64 (md_n dTA))) with (Z_to_bv 64 (md_n dTA))
        by (unfold zx16; rewrite !unsigned_lit by (clear - NRTA; lia); rewrite Z.mod_small by (clear - NRTA; lia); reflexivity).
      zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. clear MU WM.
      pose proof (u32arr_cells asegs _ _ _ ARRT) as ZCH.
      replace (4 * length (md_limbs dTA))%nat with (Z.to_nat (4 * md_n dTA)) in ZCH by (clear - LENTA NT1; lia).
      pose proof (conj SPLO I) as SPLOb. clear SPLO.
      pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
      eapply aevtA_call.
      { intros mo3 [HK3 MF3].
        eapply SPZ with (h := hq) (LB := LBq) (LF := LF1) (buf := md_p dTA) (len := 4 * md_n dTA) (lo := lo) (d := d + 1) (junk := u32s (md_limbs dTA));
          rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
        all: try (right; split; [exact INT | exact ZCH]).
        all: try (rewrite HSq; eapply uwc_floor; [exact UW2| clear; lia]).
        all: try (f_equal; clear; lia).
        all: unfold mul_mpi_PHI, mul_mpi_FR, fr_charge in *; unfold AVOL_CALL in *;
             clear - NRTA NT1 LOS SLO SP1 SP1M NEEDR TOP HTq SPR BUD BUDF HV HF HVq HFRq D0; try lia.
        all: match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end. }
      clear SPZ.
      intros ms' mo4' (mo3 & [HK3 MF3] & PO).
      destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO. injection E as E1 E2. subst ms' mo4'.
      rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
      flat constr:(PO) 12%nat. flclear PO. intros MI4 ST4 MF4 HP4 HT4 HS4 HF4 HK4 HCS4 HV4 HFR4 HH4.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
      match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
      flat constr:(SPLOb) 2%nat. flclear SPLOb. intros SPLO _.
      assert (SPLO4 : rw_cells asegs m4 sp1 (mm_fr c0 c8 c16 c24 c32 c40 c48 c56)).
      { eapply (presA_rw_cells asegs R); [exact HP4| exact SPLO| apply client_range_stack; clear; lia|].
        cbn [disjoint_from cells_size csize Nat.add mm_fr]. split; [clear - PC ALO LOS SLO SP1 NEEDR; lia| exact I]. }
      assert (CST4 : CSTA m4 h4 (lb_remove (md_p dTA) LBq) [] dW (CSFC k96 k104 gb) FSHXL (v + AVOL_CALL) (f + fr_charge (d + 1))).
      { change (@nil mpd) with (remove_nth 0 [dTA]).
        eapply (A_mpi_client.cs_drop asegs R HIA) with (i := 0%nat) (d := dTA) (mq := m2) (hq := hq); try eassumption; reflexivity. }
      apply (aevtA_enter asegs (KF asegs R HIA h4 mo0) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
      eapply (mm_EPIK m4 h4 _ [] dW _ _ r); [exact CST4| apply Forall_nil| exact SPLO4| exact HR| exact HV| exact HF| exact HSZ].
    all: match goal with |- ?g => idtac "CLEANB-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00c0@L10487653234.5  L11859751194.2  L12806812869.5  L18364504529.4  L22181430612.1  L22227626934.213L2405434805.3   L2406438837.30  L26939613102.3  L28494452040.1  L28800957839.177L34449366402.10 L3482348703.30  L3483319967.1   L35442068860.170L35663928186.7  L38327628946.30 L39172636981.0  L39261862547.30 L40889598521.3  L41663468825.170L46495298508.1  L46495921149.30 L47273608292.11 L5156091514.177 L51728739354.2  L51732702365.176L51732851458.170L52101693566.15 L55289527462.6  L55866159508.4  L56523586534.1  L56641043079.4  L56643561799.30 L59308972243.3  L60098763854.3  L61627378852.3  L62037211595.7  L6203936179.1   L64460575278.1  L67337568515.3  L8398153729.1   L9356559676.11  Q1356123914.173 Q19405263633.181Q34673729958.173Q39029445783.173Q44621047837.181Q53876795532.181Q55203889079.173Q65149597196.18100000?00I00X00Y00]01D01E01Z01f01k02R03903C03D03k04@04d04e05H05I06006106C06m07T07^08J08K09A09U09`09d09e0:D0:O0:Y0:a0;<0;A0;F0;U0;Y0<D0<i0=N0=k0>S0?00?X0@50@RS2dX2dA2dB1v2HVS3dTB4NRTBS2dX2dA2dB1v2HVFS2FBS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn3dTBFS1R2sp2lo3SLO3sp13SP1S2FB3dTB3BFTS3sp1S2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn3dTBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS3sp14SP1MFS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn3dTBS1R3HIA1h2sp2lo3TOP1HS1R3HIA1h1d2D03sp12hq1f2HF4BUDF4HFRqSS1R3HIA1h2dA2dB3sp12hq1v2HV3BUD3HVqFS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn3dTBFS3sp13dTB4NRTB3NT1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13dTB3ALO2PCS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn3dTBS3dTB4NRTBS2LF2ra2sp3LFB2dX2dA2dB2FB3sp14gapn3dTB4NRTBFS1R3HIA5NEEDR2sp2lo3LOS3SLO3sp13SP12hq3dTB3ALO2PC1a2HaS1R3dTB3ACV2P02PC2N1S1d2D01f2HFS2FBFS1R3HIA1h2sp3TOP3sp13SP12hq3HTqS3dTB2KZ2P0S1R2lo3LOSS1d1f2HFS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3dTBS3dTB5LENTB3NT1S2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS2LF2lo3LFB2dX2dA2dB3sp14gapn3LOC3dTBS2LF2lo3LFB2dX2dA2dB3sp14gapn3LOC3dTBS2LF3LFB2dX2dA2dB2FB4gapn3dTBS2LF2sp2lo3LFB2dX2dA2dB3sp14gapn3SP13dTBS2LF3LFB2dX2dA2dB2FB4gapn3dTBS2LF2sp2lo3LFB2dX2dA2dB3sp14gapn3SP13dTBS2LF3LFB2dX2dA2dB2FB4gapn3dTBS2LF3LFB2dX2dA2dB2FB4gapn3dTB". (* [comment removed for export] *)
  Lemma mm_CLEAN : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pmq,P,(;.&40.)(<.(;.&8.))Phq,(9.$:.VR,VHIA,)PLBq,(35.$36.)PdTA,$3=.PdTB,$3=.PdW,$3=.Pv,$8.Pf,$8.Pr,$8.Pc0,(;.&40.)Pc8,(;.&40.)Pc16,(;.&40.)Pc24,(;.&40.)Pc32,(;.&40.)Pc40,(;.&40.)Pc48,(;.&40.)Pc56,(;.&40.)Pk96,(;.&40.)Pk104,(;.&40.)Pgb,(35.(;.&8.))Pxra,(;.&40.)Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa0,(;.&40.)Pa1,(;.&40.)Pa2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)Ps3v,(;.&40.)Ps4v,(;.&40.)Ps6v,(;.&40.)Ps7v,(;.&40.)Ps10v,(;.&40.)Ps11v,(;.&40.)P,(4<.$:.VR,VHIA,Vh,VLB,VLF,Vm,(18.&40.Vsp,)Vlo,Vsp1,VFB,+80.VdX,Ves,R2:.R29.R28.(0.$3=.R27.(0.$3=.R26.(5.$3=.)))R25.(4=.(3.&40.(4.VFB,+4:.))(3.&40.(4.VFB,+20.))(3.&40.VFB,)(3.&40.(4.VFB,+40.))R19.R18.(3.&40.VFB,)R17.)(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(5.$1.)))))))))))))))))R24.R23.)P,(>.$8.(42.R28.)(4.VFB,+20.))P,(>.$8.(42.R28.)(4.VFB,+40.))P,(27.$:.R2=.Vsp1,(3:.R24.R23.R22.R21.R20.R1?.R1>.R1=.))P,(56.$:.R2>.(2?.VR,)(1?.$:.VR,VHIA,Vh,)(18.&40.Vsp,)(4.Vsp1,+40.)(4.Vd,+1.))P,(39.(>.$8.R27.=)(>.$8.R27.$4>.))P,(16.(4.R2:.(47.+2.$57.))(4?.VdX,VdA,VdB,))P,(16.(4.R2:.(47.+2.(58.(4.Vd,+1.))))(50.Vd,))P,(16.(4.(21.$:.VR,VHIA,Vh,)(4?.VdX,VdA,VdB,))$59.)P,(16.(4.(22.$:.VR,VHIA,Vh,)(50.Vd,))$5:.)P,(16.(48.R2?.)(51.(48.VdX,)(51.(4.(48.VdA,)(48.VdB,))+1.)))(52.$:.(53.$:.VR,VHIA,R34.Vmo0,)(54.$:.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,(55.VLB,VdX,VdA,VdB,)(4?.VdX,VdA,VdB,)(50.Vd,)Vlo,Vm,Vmo0,)(?.(10.R21.(3.&40.Vsp1,)Vgp,Vtp,R20.R1?.R1>.Vsp,(3.&40.Vsp1,)R1=.R1<.R1;.R1:.R19.R18.R17.R16.(3.&40.VFB,)R11.R10.(3.&40.(4.VFB,+2:.))R?.R>.(3.&40.R2=.)(3.&40.(4.(13.VFB,+3.)(11.(12.VR,))))R=.R<.R15.R14.R13.R12.)VF,(3.&40.+9>>4<.)Vfc,(14.(;.&40.))R35.(15.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until s11v. intros CST EAD EBD SPLO UW HR HV HF BUD BUDF HSZ. rt_facts.
    flat constr:((A_mpi_client.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST)) 5%nat. intros CHq SHq MIq STq HHq.
    flat constr:((A_mpi_client.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST)) 6%nat. intros HTq HSq HFq HCSq HVq HFRq.
    flat constr:(FRSH) 4%nat. intros F0 F1 F2 F3.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    assert (CFBq : crange (hcs asegs R HIA hq) FB 128) by (eapply crange_mono; [exact HCSq| exact CFB]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    unfold CSF in CHq. apply Forall_cons_iff in CHq. flat constr:(CHq) 2%nat. flclear CHq. intros SPHI _. cbn [fst snd] in SPHI.
    edestruct (A_mpi_client.cs_local_facts asegs R HIA) with (i := 1%nat) (d := dTB) as (MTB & NSTB & _ & _ & _ & _ & HFTB & _); try eassumption; [reflexivity|].
    flat constr:(MTB) 2%nat. intros FLt3 SGTB. flat constr:(FLt3) 6%nat. flclear FLt3. intros CTB _ _ LENTB NRTB OWNTB. rewrite EBD in CTB. unfold mpi_cells in CTB. unfold MPI_MAX_LIMBS in NRTB.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases KZ; zify_cond KZ.
    - (* [comment removed for export] *)
      assert (EO : md_own dTB = LNull).
      { destruct (md_own dTB) eqn:EOT; [reflexivity| | exfalso; exact (NSTB eq_refl)]. exfalso.
        flat constr:((HFTB eq_refl)) 5%nat. intros P0 PC _ N1 _. rewrite Z.mod_small in KZ by (clear - P0 PC N1 ACV; lia). clear - KZ P0. lia. }
      assert (CST1 : CSTA mq hq LBq [dTA] dW (CSFC k96 k104 gb) FSHXL v f).
      { change [dTA] with (remove_nth 1 [dTA; dTB]). eapply (A_mpi_client.cs_drop_null asegs R HIA) with (i := 1%nat) (d := dTB); [exact CST| reflexivity| exact EO]. }
      eapply (mm_CLEAN_B mq hq LBq dTA dW v f r); [exact CST1| exact EAD| exact SPLO| exact CTB| exact UW| exact HR| | | exact BUD| exact BUDF| exact HSZ].
      + unfold AVOL_CALL in *. clear - HV. lia.
      + unfold fr_charge in *. clear - HF D0. lia.
    - (* [comment removed for export] *)
      assert (EO : md_own dTB = LHeap).
      { destruct (md_own dTB) eqn:EOT; [exfalso; (flat constr:(OWNTB) 2%nat; flclear OWNTB; intros EP _); apply KZ; rewrite EP; reflexivity| reflexivity| exfalso; exact (NSTB eq_refl)]. }
      rewrite EO in OWNTB. flat constr:(OWNTB) 4%nat. flclear OWNTB. intros NT1 INT PAL ARRT.
      flat constr:((HFTB EO)) 6%nat. intros P0 PC _ _ BFT _.
      (* [comment removed for export] *)
      zstep. replace (FB + 74) with (FB + 64 + 10) by (clear; lia).
      zstep.
      replace (zx16 (Z_to_bv 64 (md_n dTB))) with (Z_to_bv 64 (md_n dTB))
        by (unfold zx16; rewrite !unsigned_lit by (clear - NRTB; lia); rewrite Z.mod_small by (clear - NRTB; lia); reflexivity).
      zstep. rewrite !Z.shiftl_mul_pow2 by (clear; lia). change (2 ^ 2) with 4. zstep. clear MU WM.
      pose proof (u32arr_cells asegs _ _ _ ARRT) as ZCH.
      replace (4 * length (md_limbs dTB))%nat with (Z.to_nat (4 * md_n dTB)) in ZCH by (clear - LENTB NT1; lia).
      pose proof (conj SPLO I) as SPLOb. clear SPLO. pose proof (conj CTB I) as CTBb. clear CTB.
      pose proof ZF as SPZ. unfold zeroize_and_free_stmtA, A_ZEROIZE_AND_FREE in SPZ.
      eapply aevtA_call.
      { intros mo3 [HK3 MF3].
        eapply SPZ with (h := hq) (LB := LBq) (LF := LF1) (buf := md_p dTB) (len := 4 * md_n dTB) (lo := lo) (d := d + 1) (junk := u32s (md_limbs dTB));
          rewrite ?(unsigned_lit sp1) by exact SP1R; try eassumption; try reflexivity.
        all: try (right; split; [exact INT | exact ZCH]).
        all: try (rewrite HSq; eapply uwc_floor; [exact UW| clear; lia]).
        all: try (f_equal; clear; lia).
        all: unfold mul_mpi_PHI, mul_mpi_FR, fr_charge in *; unfold AVOL_CALL in *;
             clear - NRTB NT1 LOS SLO SP1 SP1M NEEDR TOP HTq SPR BUD BUDF HV HF HVq HFRq D0; try lia.
        all: match goal with |- ?g => idtac "ZF-PRE-LEFT:" g end. }
      clear SPZ.
      intros ms' mo4' (mo3 & [HK3 MF3] & PO).
      destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO. injection E as E1 E2. subst ms' mo4'.
      rewrite ?(unsigned_lit sp1) in PO by exact SP1R.
      flat constr:(PO) 12%nat. flclear PO. intros MI4 ST4 MF4 HP4 HT4 HS4 HF4 HK4 HCS4 HV4 HFR4 HH4.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) => rename mx into m4 end.
      match type of HH4 with HM _ _ _ ?hh _ _ _ => rename hh into h4 end.
      flat constr:(SPLOb) 2%nat. flclear SPLOb. intros SPLO _. flat constr:(CTBb) 2%nat. flclear CTBb. intros CTB _.
      assert (SPLO4 : rw_cells asegs m4 sp1 (mm_fr c0 c8 c16 c24 c32 c40 c48 c56)).
      { eapply (presA_rw_cells asegs R); [exact HP4| exact SPLO| apply client_range_stack; clear; lia|].
        cbn [disjoint_from cells_size csize Nat.add mm_fr]. split; [clear - PC ALO LOS SLO SP1 NEEDR; lia| exact I]. }
      assert (CTB4 : rw_cells asegs m4 (FB + 64) [C8 (Z_to_bv 64 (md_p dTB)); C2 (Z_to_bv 64 (md_sg dTB)); C2 (Z_to_bv 64 (md_n dTB)); C4 (md_pad dTB)]).
      { eapply (presA_rw_cells asegs R); [exact HP4| exact CTB| |].
        - eapply client_range_block; [apply in_app_iff; right; cbn [fdata]; right; left; reflexivity| clear; lia| cbn [cells_size csize Nat.add]; clear; lia].
        - cbn [disjoint_from cells_size csize Nat.add]. split; [clear - BFT; lia| exact I]. }
      assert (UW4 : UWCM m4).
      { rewrite <- HSq. eapply (uwc_presA_w R); [exact HP4| rewrite HSq; exact UW| clear; lia| | clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
        intros a Ha. cbn [outside]. split; [clear - Ha PC ALO LOS SLO SP1 NEEDR; lia| exact I]. }
      assert (CST4 : CSTA m4 h4 (lb_remove (md_p dTB) LBq) [dTA] dW (CSFC k96 k104 gb) FSHXL (v + AVOL_CALL) (f + fr_charge (d + 1))).
      { change [dTA] with (remove_nth 1 [dTA; dTB]).
        eapply (A_mpi_client.cs_drop asegs R HIA) with (i := 1%nat) (d := dTB) (mq := mq) (hq := hq); try eassumption; reflexivity. }
      apply (aevtA_enter asegs (KF asegs R HIA h4 mo0) _ _ _ (conj HK4 (mo_frame_trans _ _ _ MF3 MF4))).
      eapply (mm_CLEAN_B m4 h4 _ dTA dW _ _ r); [exact CST4| exact EAD| exact SPLO4| exact CTB4| exact UW4| exact HR| | | exact BUD| exact BUDF| exact HSZ].
      + clear - HV. lia.
      + clear - HF. lia.
    all: match goal with |- ?g => idtac "CLEAN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis IMGk : asan_img_ok AL.
  Local Notation SPVW := (Z_to_bv 64 (sp1 + 64)).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L62281631034.1100000[S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13SPR3ALO3ACP". (* [comment removed for export] *)
  Lemma SPVU : bv_unsigned SPVW = sp1 + 64.
  Proof. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
         pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
         apply unsigned_lit. clear - SP1 SPR SLO LOS ALO ACP NEEDR. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L19611842351.2L56087230626.200000800@S2dW3NW1S2dl3NL1". (* [comment removed for export] *)
  Lemma cs_wl_apart : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pmq,P,(;.&40.)(<.(;.&8.))Phq,(9.$:.VR,VHIA,)PLBq,(35.$36.)Pls,(35.$3=.)PdW,$3=.PCS,(35.(1;.$8.(35.$1.)))PSHC,(35.$1.)Pv,$8.Pf,$8.Pi,$5;.Pdl,$3=.P,(4<.$:.VR,VHIA,Vh,VLB,VLF,Vm,(18.&40.Vsp,)Vlo,Vsp1,VFB,+80.VdX,Ves,R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(>.(<.$3=.)(5<.$3=.R9.R3.)(5=.$3=.R2.))P,(>.$43.(44.R9.)$45.)P,(>.$43.(44.R4.)$45.)(39.(16.(4.(46.R;.)(47.+4.(48.R;.)))(46.R5.))(16.(4.(46.R5.)(47.+4.(48.R5.)))(46.R;.)))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW CS SHC v f i dl CST Hi OW OL.
    flat constr:(CST) 11%nat. flclear CST. intros HH _ _ _ LOK _ _ MW _ WOK _.
    flat constr:(WOK) 5%nat. flclear WOK. intros _ _ _ WB _. flat constr:((WB OW)) 2%nat. intros WNL _.
    flat constr:((proj1 (Forall_forall _ _) LOK dl (nth_error_In _ _ Hi))) 2%nat. intros ML _.
    flat constr:((A_mpi_client.mpd_heap_in asegs _ _ _ MW OW)) 2%nat. intros INW NW1. flat constr:((A_mpi_client.mpd_heap_in asegs _ _ _ ML OL)) 2%nat. intros INL NL1.
    flat constr:((hm_apart asegs R HIA hq LBq LF1 mq HH)) 2%nat. intros _ BA. pose proof (blocks_apart_app_l _ _ BA) as BAq.
    assert (NE : (md_p dW, 4 * md_n dW) <> (md_p dl, 4 * md_n dl)).
    { intros E. apply WNL. rewrite E. apply in_flat_map. exists dl. split; [eapply nth_error_In; exact Hi| apply mpd_blk_in; exact OL]. }
    pose proof (blocks_apart_neq _ _ _ BAq INW INL NE ltac:(cbn; clear - NW1; lia) ltac:(cbn; clear - NL1; lia)) as K. cbn [fst snd] in K. exact K.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L10877879353.3L15756354262.4L33976102659.6L37280444511.6L38948636245.0L56089315106.2L57965015528.6L66076510722.600000:00H00\00o01001701K01_S2dX2dl2APS1R2lo3LOS3ALOS2dX2FB2dl2L12L23WFBS2dX2FB2dl2L12L22BFSS2dl2N1S2dX2FB2dl2L12L23WFBS1R2lo3LOS2dl3ALO2PC". (* [comment removed for export] *)
  Lemma rider_loc : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pmq,P,(;.&40.)(<.(;.&8.))Phq,(9.$:.VR,VHIA,)PLBq,(35.$36.)Pls,(35.$3=.)PCS,(35.(1;.$8.(35.$1.)))Pv,$8.Pf,$8.Pi,$5;.Pdl,$3=.P,(4<.$:.VR,VHIA,Vh,VLB,VLF,Vm,(18.&40.Vsp,)Vlo,Vsp1,VFB,+80.VdX,Ves,R9.R8.R7.R6.VdX,R5.(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(5.$1.)))))))))))))))))R4.R3.)P,(>.(<.$3=.)(5<.$3=.R7.R3.)(5=.$3=.R2.))(=.(5>.$:.VR,VHIA,R9.(0.(1;.$8.$8.)(1<.$8.$8.VFB,+80.)VLF,)R;.VdX,(3.&40.(4.Vsp1,+40.))Vlo,R3.)(=.(5?.$:.VR,VHIA,(0.(1;.$8.$8.)(1<.$8.$8.VFB,+80.)VLF,)(3.&40.(4.Vsp1,+40.))R3.R:.R9.R;.VdX,)(=.(49.(>.$8.(42.R3.)(42.VdX,)))(=.(16.=(48.R3.))(16.(48.R3.)+2710.)))))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls CS v f i dl CST Hi. pose proof SPVU as SPVU. rt_facts. flat constr:(FRSH) 4%nat. intros F0 F1 F2 F3.
    edestruct (A_mpi_client.cs_local_facts asegs R HIA) with (i := i) (d := dl) as (ML & NSL & _ & LLO & CRL & CRLL & HFL & L1 & L2 & L8 & LLO2 & OL); try eassumption.
    edestruct (A_mpi_client.cs_w_facts asegs R HIA) as (MWq & _ & _ & _ & _ & _ & _ & HFW & _ & WFB & _); try eassumption.
    flat constr:((A_mpi_client.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST)) 5%nat. intros _ _ _ _ HHq.
    flat constr:(ML) 2%nat. intros FLt4 _. flat constr:(FLt4) 6%nat. flclear FLt4. intros _ _ _ _ NRL _. unfold MPI_MAX_LIMBS in NRL.
    assert (SEPS : md_own dX = LHeap -> md_addr dl + 16 <= md_p dX \/ md_p dX + 4 * md_n dX <= md_addr dl).
    { intros O. flat constr:((HFW O)) 6%nat. intros _ _ _ _ BF _. clear - BF L1 L2. lia. }
    assert (SEPL : md_own dX = LHeap -> md_own dl <> LNull -> md_p dX + 4 * md_n dX <= md_p dl \/ md_p dl + 4 * md_n dl <= md_p dX).
    { intros O NN. destruct (md_own dl) eqn:EOL; [exfalso; exact (NN eq_refl)| | exfalso; exact (NSL eq_refl)].
      exact (cs_wl_apart _ _ _ _ _ _ _ _ _ i dl CST Hi O EOL). }
    assert (XLA : md_own dl <> LNull -> md_addr dX + 16 <= md_p dl \/ md_p dl + 4 * md_n dl <= md_addr dX).
    { intros NN. destruct (md_own dl) eqn:EOL; [exfalso; exact (NN eq_refl)| | exfalso; exact (NSL eq_refl)].
      flat constr:((HFL eq_refl)) 6%nat. intros _ _ _ N1 _ FRL.
      assert (W0C : client_range L (mpd_keep LB dX ++ fdata LF) lo (md_addr dX) 16) by (eapply (A_mpi_client.w0_client asegs R HIA); eassumption).
      pose proof (fresh_apart_client R (mpd_keep LB dX) LF lo (md_addr dX) 16 _ _ FRL W0C ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as AP.
      clear - AP. lia. }
    split; [| split; [| split; [clear - WFB L1 L2; lia| exact NRL]]].
    - constructor.
      + left. exact ML.
      + split; [exact XLA|]. split; [exact SEPS|]. split; [| split; [left; exact LLO2| intros NN; rewrite SPVU; destruct (LLO NN) as [K|K]; [left; exact K| left; destruct (md_own dl) eqn:EOL; [exfalso; exact (NN eq_refl)| (flat constr:((HFL eq_refl)) 3%nat; intros _ PC _); clear - PC ALO LOS; lia| exfalso; exact (NSL eq_refl)]]]].
        destruct (limb_own_eq_dec (md_own dX) LHeap) as [O|O]; [| right; left; exact O].
        destruct (limb_own_eq_dec (md_own dl) LNull) as [O2|O2]; [right; right; left; exact O2| right; right; right; exact (SEPL O O2)].
      + exact CRL.
      + exact CRLL.
      + clear - WFB L1 L2. lia.
      + intros EO. exfalso. exact (NSL EO).
    - constructor.
      + left. exact ML.
      + exact SEPS.
      + exact SEPL.
      + exact OL.
      + intros NN. destruct (md_own dl) eqn:EOL; [exfalso; exact (NN eq_refl)| | exfalso; exact (NSL eq_refl)].
        flat constr:((HFL eq_refl)) 4%nat. intros _ _ IN _. eapply hm_aobj_block; [exact HHq| exact IN].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L44709793478.5L45304130759.3L59308661717.200000@00I00OS2sp3sp13SP11e1KS2dX1e2E6S1e2E6". (* [comment removed for export] *)
  Lemma rider_ext : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pmq,P,(;.&40.)(<.(;.&8.))Phq,(9.$:.VR,VHIA,)PLBq,(35.$36.)Pls,(35.$3=.)PCS,(35.(1;.$8.(35.$1.)))Pv,$8.Pf,$8.Pe,$3=.P,(4<.$:.VR,VHIA,Vh,VLB,VLF,Vm,(18.&40.Vsp,)Vlo,Vsp1,VFB,+80.VdX,Ves,R8.R7.R6.R5.VdX,R4.(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(5.$1.)))))))))))))))))R3.R2.)P,(38.$3=.R2.Ves,)P,(60.VdX,R3.Vlo,(18.&40.Vsp,))P,P,(>.$43.(44.R4.)$61.)P,Pi,$8.P,(=.(16.=R1.)(62.R1.(47.+4.(48.R6.))))(>.$63.(64.$:.(65.(4.(46.R7.)R2.)))$66.)(>.$63.(67.(46.R6.)(47.+4.(48.R6.)))$66.)(=.(5>.$:.VR,VHIA,R:.(0.(1;.$8.$8.)(1<.$8.$8.VFB,+80.)VLF,)R<.VdX,(3.&40.(4.Vsp1,+40.))Vlo,R5.)(=.(5?.$:.VR,VHIA,(0.(1;.$8.$8.)(1<.$8.$8.VFB,+80.)VLF,)(3.&40.(4.Vsp1,+40.))R5.R;.R:.R<.VdX,)(=.(49.(>.$8.(42.R5.)(42.VdX,)))(=.(16.=(48.R5.))(16.(48.R5.)+2710.)))))")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls CS v f e CST He OE IE. pose proof SPVU as SPVU. rt_facts.
    edestruct (A_mpi_client.cs_ext_facts asegs R HIA) with (e := e) as (ME & OEs & CRE & CREL & HFE & ASE & EFB); try eassumption.
    flat constr:((A_mpi_client.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST)) 5%nat. intros _ _ _ _ HHq.
    flat constr:((proj1 (Forall_forall _ _) ESF e He)) 7%nat. intros _ _ _ _ _ E6 _.
    flat constr:(ME) 2%nat. intros FLt5 _. flat constr:(FLt5) 6%nat. flclear FLt5. intros _ _ _ _ NRE OWE. unfold MPI_MAX_LIMBS in NRE.
    flat constr:(OE) 5%nat. intros OE1 OE2 OE3 OE4 OE5.
    assert (IMGA : md_own e = LStatic -> forall hc LBc mc, HM asegs R HIA hc LBc LF1 mc -> aobj asegs AL (hcs asegs R HIA hc) mc (md_p e) (4 * md_n e)).
    { intros EO hc LBc mc HMc. rewrite EO in OWE. flat constr:(OWE) 5%nat. flclear OWE. intros _ _ _ _ RO.
      eapply (AImgGlobals.aobj_img asegs AL); [apply (hcs_img_cs_cp R HIA IMGk)| eapply (hm_img_shadow asegs R HIA); exact HMc| exact (IE EO RO)]. }
    split; [| split; [| split; [clear - E6; lia| exact NRE]]].
    - constructor.
      + left. exact ME.
      + split; [exact OE1|]. split; [exact OE2|]. split; [exact OE3|]. rewrite SPVU.
        split; [destruct OE4 as [K|K]; [left; exact K| right; clear - K SP1; lia]| intros EN; destruct (OE5 EN) as [K|K]; [left; exact K| right; clear - K SP1; lia]].
      + exact CRE.
      + exact CREL.
      + exact E6.
      + intros EO _ hc LBc mc HMc. exact (IMGA EO hc LBc mc HMc).
    - constructor.
      + left. exact ME.
      + exact OE2.
      + intros EOX EN. destruct OE3 as [C|[C|[C|C]]]; [exfalso; rewrite C in E6; clear - E6; lia| exfalso; exact (C EOX)| exfalso; exact (EN C)| exact C].
      + exact OEs.
      + intros EN. destruct (md_own e) eqn:EOE; [exfalso; exact (EN eq_refl)| |].
        * flat constr:((HFE eq_refl)) 2%nat. intros IN _. eapply hm_aobj_block; [exact HHq| exact IN].
        * exact (IMGA eq_refl hq LBq mq HHq).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis CMUL : mpi_core_mul_stmtA asegs R HIA A_MPI_CORE_MUL.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_MM.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_MM.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_MM.
  Hypothesis UWX : uw_obj R (md_addr dX) 16 d.
  Hypothesis BUD : havol asegs R HIA h + mul_mpi_PHI dX dA dB <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + mul_mpi_FR d <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_MUL_MPI <= C24MAX.

  Lemma mpd_eta : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pdq,$3=.(>.$3=.R1.(68.(42.R1.)(69.R1.)(48.R1.)(46.R1.)(6:.R1.)(6;.R1.)(44.R1.)))")
(* [comment removed for export] *).
  Proof. destruct dq; reflexivity. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0?L11867806386.8 L12945043148.3 L14127923137.1 L18359781713.10L18447870501.5 L25498419105.2 L27604546642.4 L27604546642.8 L27650499371.1 L28494972232.3 L29453456920.7 L29761862326.6 L30456950942.1 L30457471134.6 L31419296075.1 L33316636690.6 L33317165074.3 L33323121782.7 L33754188383.3 L34449366402.10L3574160920.12 L3574160920.8  L3576194526.16 L3859788583.11 L39210124298.14L39280637297.0 L40963710207.7 L42107586957.4 L4392741670.24 L44744406794.3 L45328269040.11L45329976438.7 L45330504822.3 L47214264752.3 L4781719053.2  L48439538898.10L52101693566.14L53429927394.6 L59309021520.8 L62037211595.7 L63098214383.1 L66151427842.16L8118034753.1  L9568782098.6  L960210853.1   00000O00[00`01@01O01V01W01X01\01a02;02O02P02Q02V02k02l03B03L04304404504604704f04g05?05Q05R05^05_05`05a05m06306V07G07^08708R08W09309809M09RS2dX2dA2dB3dAr3dBr3SZM3dXc4HSZ'S2dX3dAr3dBrS3sp1S1R3HIA1h1d2D04BUDF2hq1f2HF4HFRqS1d1f2HF2f'3HF'S1d3CAPFFS2FBS3sp1S2dX2dA2dB3dAr3dBr3NLA3NLBS1R2lo3LOS2dX3ALO2PCFFS3sp1S1R2sp2lo3SLO3sp13SP1FS2sp2dX3sp13SP11C1x2HxS2LB3LBq1CS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPFFFFS1R3HIA1h2dX2dA2dB3BUD2hq3dAr3dBr1v2HV3HVq4MONOSS1R3HIA1h2sp3TOP3sp13SP1S2LB4C24H3LBq4C24qFS2sp3sp13SP1FFFS2sp3sp13SP1S1d2D0S2dX2dA2dB3dAr3dBr1v2HV4MONO2v'3HV'S1R3HIA5NEEDR2sp2lo3LOS3SLO2dX3sp13SP12hq2XS1a2HaS2dA2dB3dAr3dBr3NLA3NLBS2lo2dX3sp13LOC1C1x2Hx2S1S1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S3sp12r04SP1M1q1r1H2H02q02H4S3sp1S1R2sp2lo3SLO3sp13SP1S3sp1". (* [comment removed for export] *)
  Lemma mm_MIDGO : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pmq,P,(;.&40.)(<.(;.&8.))Phq,(9.$:.VR,VHIA,)PLBq,(35.$36.)PdTA,$3=.PdTB,$3=.PdAr,$3=.PdBr,$3=.Pv,$8.Pf,$8.Pc0,(;.&40.)Pc8,(;.&40.)Pc16,(;.&40.)Pc24,(;.&40.)Pc32,(;.&40.)Pc40,(;.&40.)Pc48,(;.&40.)Pk96,(;.&40.)Pk104,(;.&40.)Pgb,(35.(;.&8.))Pxra,(;.&40.)Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa1,(;.&40.)Pa2,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)Ps10v,(;.&40.)Ps11v,(;.&40.)P,(4<.$:.VR,VHIA,Vh,VLB,VLF,Vm,(18.&40.Vsp,)Vlo,Vsp1,VFB,+80.VdX,Ves,R23.R22.R21.(0.$3=.R20.(0.$3=.R1?.(5.$3=.)))VdX,(4=.(3.&40.(4.VFB,+4:.))(3.&40.(4.VFB,+20.))(3.&40.VFB,)(3.&40.(4.VFB,+40.))R13.R12.(3.&40.VFB,)R11.)(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(5.$1.)))))))))))))))))R1<.R1;.)P,(>.$8.(42.R21.)(4.VFB,+20.))P,(>.$8.(42.R21.)(4.VFB,+40.))P,(27.$:.R26.Vsp1,(3:.R1=.R1<.R1;.R1:.R19.R18.R17.(3.&40.(4.(42.R21.)+8.))))P,(56.$:.R27.(2?.VR,)(1?.$:.VR,VHIA,Vh,)(18.&40.Vsp,)(4.Vsp1,+40.)(4.Vd,+1.))P,(=.(5>.$:.VR,VHIA,R26.(0.(1;.$8.$8.)(1<.$8.$8.VFB,+80.)VLF,)R28.VdX,(3.&40.(4.Vsp1,+40.))Vlo,R23.)(=.(5?.$:.VR,VHIA,(0.(1;.$8.$8.)(1<.$8.$8.VFB,+80.)VLF,)(3.&40.(4.Vsp1,+40.))R23.R27.R26.R28.VdX,)(=.(49.(>.$8.(42.R23.)(42.VdX,)))(=.(16.=(48.R23.))(16.(48.R23.)+2710.)))))P,(=.(5>.$:.VR,VHIA,R27.(0.(1;.$8.$8.)(1<.$8.$8.VFB,+80.)VLF,)R29.VdX,(3.&40.(4.Vsp1,+40.))Vlo,R23.)(=.(5?.$:.VR,VHIA,(0.(1;.$8.$8.)(1<.$8.$8.VFB,+80.)VLF,)(3.&40.(4.Vsp1,+40.))R23.R28.R27.R29.VdX,)(=.(49.(>.$8.(42.R23.)(42.VdX,)))(=.(16.=(48.R23.))(16.(48.R23.)+2710.)))))P,(16.(48.R25.)(48.VdA,))P,(16.(48.R25.)(48.VdB,))P,(16.(4.(4.R25.(6<.VdA,VdB,))(47.+2.$57.))(4?.VdX,VdA,VdB,))P,(16.(4.(4.R25.(6=.(4.Vd,+1.)))(47.+2.(58.(4.Vd,+1.))))(50.Vd,))(52.$:.(53.$:.VR,VHIA,R2=.Vmo0,)(54.$:.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,(55.VLB,VdX,VdA,VdB,)(4?.VdX,VdA,VdB,)(50.Vd,)Vlo,Vm,Vmo0,)(?.(10.R1;.(3.&40.Vsp1,)Vgp,Vtp,R1:.R19.R18.Vsp,(3.&40.Vsp1,)(3.&40.(4.(42.R28.)+:.))R17.R16.(3.&40.(4.(42.R28.)+8.))R15.R14.R13.R12.(3.&40.VFB,)(3.&40.(4.(42.R29.)+:.))(3.&40.(11.(12.VR,)))(3.&40.(4.VFB,+2:.))(3.&40.(42.R28.))(3.&40.(42.VdX,))(3.&40.(42.R29.))(3.&40.(4.(13.VFB,+3.)(11.(12.VR,))))R=.R<.R11.R10.R?.R>.)VF,(3.&40.+9>:<4.)Vfc,(14.(;.&40.))R2>.(15.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until s11v. intros CST EAD EBD SPLO UW (JA & BA & NXA & NRA) (JB & BB & NXB & NRB) NLA NLB HV HF. pose proof SPVU as SPVU. rt_facts.
    flat constr:(FRSH) 4%nat. intros F0 F1 F2 F3.
    flat constr:((A_mpi_client.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST)) 5%nat. intros CHq SHq MIq STq HHq.
    flat constr:((A_mpi_client.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST)) 6%nat. intros HTq HSq HFq HCSq HVq HFRq.
    edestruct (A_mpi_client.cs_w_facts asegs R HIA) as (MWq & _ & _ & (CWq & XPq) & _ & _ & _ & HFW & ASW & WFB & OWq); try eassumption.
    assert (MONO : mul_mid_PHI dAr dBr <= mul_mid_PHI dA dB) by (unfold mul_mid_PHI, grow_PHI; clear - NLA NLB; lia).
    assert (SZM : mul_mid_SZ (md_n dX) dAr dBr <= Z.max (md_n dX) (Z.max (md_n dA + md_n dB) 1)) by (unfold mul_mid_SZ; clear - NLA NLB; lia).
    assert (JCx : forall k0 k8 k16 k24 k32 k40 k48 k56, JCA asegs R HIA hq LBq LF1 mq dX SPVW lo 64 (mm_fr k0 k8 k16 k24 k32 k40 k48 k56)).
    { intros. constructor; rewrite ?SPVU; try assumption; try reflexivity; try (clear; lia); try (clear - SLO SP1; lia); try (rewrite HTq; clear - TOP SP1; lia);
        try (clear - SP1M; Z.div_mod_to_equations; lia).
      - split; [| exact XPq]. intros x Hx. destruct (CWq x Hx) as [[S1 S2]|[K|K]]; [left; destruct ASW as [C|C]; [exfalso; clear - C S1 Hx LOC; lia| split; [clear - C Hx SP1; lia| exact S2]]| right; left; exact K| right; right; exact K].
      - intros NN. left. destruct (md_own dX) eqn:EOX; [exfalso; exact (NN eq_refl)| (flat constr:((HFW eq_refl)) 3%nat; intros _ PC _); clear - PC ALO LOS; lia| exfalso; exact (NST eq_refl)]. }
    assert (C24q : cnt24 LBq <= cnt24 LB + 3).
    { pose proof (A_mpi_client.cs_cnt24 asegs R HIA HNDk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CST) as C. cbn [length] in C. clear - C. lia. }
    replace (Z_to_bv 64 sp1) with (Z_to_bv 64 (bv_unsigned SPVW + -64)) by (rewrite SPVU; f_equal; clear; lia).
    eapply (mw_MID R HIA) with (h := hq) (LB := LBq) (LF := LF1) (m := mq) (mo := mo0) (spv := SPVW) (spe := sp)
             (xs2 := Z_to_bv 64 FB) (xs5 := Z_to_bv 64 (FB + 42)) (xs9 := SH9)
             (X := md_addr dX) (sX := md_sg dX) (nX := md_n dX) (pX := md_p dX) (xs0 := md_limbs dX) (padX := md_pad dX) (ownX := md_own dX)
             (dA := dAr) (dB := dBr) (lo := lo) (d1 := d + 1) (POST := POSTM) (v := 0) (f := 0) (hc := hq) (LBc := LBq) (mc := mq)
             (dXc := mkMPD (md_addr dX) (md_sg dX) (md_n dX) (md_p dX) (md_limbs dX) (md_pad dX) (md_own dX))
             (c0 := c0) (c8 := c8) (c16 := c16) (c24 := c24) (c32 := c32) (c40 := c40) (c48 := c48);
      first [ exact IMGk | exact ZF | exact CMUL | exact CALLOC | exact AMC | exact AMS | exact TPV | exact NRA | exact NRB | exact NXA | exact NXB
            | (intros; rewrite <- (mpd_eta dX); apply JCx)
            | (rewrite <- (mpd_eta dX); right; split; [exact JA| exact BA]) | (rewrite <- (mpd_eta dX); right; split; [exact JB| exact BB])
            | lazymatch goal with
              | |- 0 <= d + 1 => clear - D0; lia
              | |- 0 <= 0 => clear; lia
              | |- _ + 16 <= _ => rewrite SPVU; clear - SP1; lia
              | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - HVq BUD HV MONO; unfold AVOL_CALL in *; lia
              | |- hfr _ _ _ _ + _ <= FR_MAX => clear - HFRq BUDF HF D0; unfold fr_charge in *; lia
              | |- lo <= _ - 64 - 144 - _ => rewrite SPVU; clear - SLO SP1; lia
              | |- uwc _ _ _ _ _ _ _ => rewrite SPVU, HSq; exact UW
              | |- md_n _ <= mul_mid_SZ _ _ _ => unfold mul_mid_SZ; cbn [md_n]; clear; lia
              | |- cnt24 _ + 2 <= C24MAX => clear - C24q C24H; unfold C24_MUL_MPI in C24H; lia
              end
            | idtac ].
    - (* [comment removed for export] *)
      unfold KCL_stmt. intros v' f' hc LBc mc dXc r k0 k8 k16 k24 k32 k40 k48 k56 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys3 ys4 ys6 ys7 ys10 ys11 yt3 yt4 yt5 yt6 J HR HV' HF' HSZ'.
      rewrite <- (mpd_eta dX) in J.
      pose proof J as [JMI1 JST1 JFR1 JHH1 JHT1 JHS1 JHF1 JHCS1 JHV1 JHFR1 JMX1 JAD1 JPD1 JNS1 JOUT1 JFRS1 JFRA1 JHPX1 JOX1 JXP1 JXLS1 JNM1]. cbn [app] in JHH1.
      rewrite SPVU in JST1, JFR1, JHPX1. replace (sp1 + 64 - 64) with sp1 in JST1, JFR1 by (clear; lia).
      assert (CSTc : CSTA mc hc LBc [dTA; dTB] dXc (CSFC k96 k104 gb) FSHXL (v + v') (f + f')).
      { eapply (A_mpi_client.cs_binop_w asegs R HIA) with (mq := mq) (hq := hq) (SPx := sp1 + 64); try eassumption; try (clear - SP1; lia).
        unfold CSF. repeat (apply Forall_cons; [cbn [fst snd]|]); [left; clear; lia| left; clear; lia| left; clear - SP1; lia| right; clear; lia| apply Forall_nil]. }
      assert (UWc : UWCM mc).
      { destruct UWX as [[XS _]|CAP]; [| apply uwc_cap; clear - CAP; lia].
        rewrite <- HSq. eapply (uwc_presA_w R); [exact JHPX1| rewrite HSq; exact UW| clear; lia| | clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
        intros a Ha. cbn [outside]. split; [clear - Ha XS LOS SLO SP1 NEEDR; lia| exact I]. }
      replace (Z_to_bv 64 (bv_unsigned SPVW + -64)) with (Z_to_bv 64 sp1) by (rewrite SPVU; f_equal; clear; lia).
      eapply (mm_CLEAN mc hc LBc dTA dTB dXc (v + v') (f + f') r); [exact CSTc| exact EAD| exact EBD| exact JFR1| exact UWc| exact HR| | | exact BUD| exact BUDF|].
      + clear - HV HV' MONO. lia.
      + clear - HF HF'. lia.
      + clear - HSZ' SZM. lia.
    - (* [comment removed for export] *)
      rewrite <- (mpd_eta dX).
      eapply (xa_start asegs R HIA hq LBq LF1 mq dX SPVW lo 64 _ (JCx c0 c8 c16 c24 c32 c40 c48 (Z_to_bv 64 (md_addr dAr + 8))));
        [exact HHq| exact MIq| rewrite SPVU; replace (sp1 + 64 - 64) with sp1 by (clear; lia); exact STq
        | rewrite SPVU; replace (sp1 + 64 - 64) with sp1 by (clear; lia); exact SPLO| exact OWq| apply munch_refl| apply wmono_refl].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis COPY : mpi_copy_stmtA_c asegs R HIA A_MPI_COPY.
  Hypothesis MBe : mpd_at asegs m LB dB.
  Hypothesis SXB : mpd_sep dX dB.
  Hypothesis OB : opnd_sep dX dB lo (bv_unsigned sp).
  Hypothesis IB2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "P,(>.$43.(44.VdB,)$61.)P,Pi,$8.P,(=.(16.=R1.)(62.R1.(47.+4.(48.VdB,))))(>.$63.(64.$:.(65.(4.(46.VdB,)R2.)))$66.)(>.$63.(67.(46.VdB,)(47.+4.(48.VdB,)))$66.)")
(* [comment removed for export] *).
  Hypothesis ESB : md_addr dB <> md_addr dX -> In dB es.
  Hypothesis NRA0 : 0 <= md_n dA.
  Hypothesis NRB0 : 0 <= md_n dB.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L16011783460.14L28494452040.1 L43737353406.3 L49756818986.8 L5142873508.14 L54361068081.14L57101828076.14L62018535662.1 L67028546396.5 00000:00?00K00e00o01@01n02102CS3sp14gapnS3sp1S2sp3sp13SP1S1R3HIA1h2sp3TOP3sp13SP11HS3sp14gapnS2sp3sp14gapn3SP1S1R5NEEDR2sp2lo3LOS3SLO2FB3sp14gapn3SP13ALO2F1S1RS1R2lo3LOS3sp13LOC". (* [comment removed for export] *)
  Lemma cs_spill : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pmq,P,(;.&40.)(<.(;.&8.))Phq,(9.$:.VR,VHIA,)PLBq,(35.$36.)Pls,(35.$3=.)PdW,$3=.Pk96,(;.&40.)Pk104,(;.&40.)Pgb,(35.(;.&8.))Pv,$8.Pf,$8.Pm2,P,(;.&40.)(<.(;.&8.))P,(4<.$:.VR,VHIA,Vh,VLB,VLF,Vm,(18.&40.Vsp,)Vlo,Vsp1,VFB,+80.VdX,Ves,R;.R:.R9.R8.R7.(4=.(3.&40.(4.VFB,+4:.))(3.&40.(4.VFB,+20.))(3.&40.VFB,)(3.&40.(4.VFB,+40.))R6.R5.(3.&40.VFB,)R4.)(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(5.$1.)))))))))))))))))R3.R2.)P,(6>.(0.(1;.$8.$8.)(1<.$8.$8.Vsp1,(4.Vsp1,+40.))(5.(1;.$8.$8.)))R<.R2.)P,(6?.$:.R=.R3.)P,(1:.$:.VR,VHIA,R=.R<.(0.(1;.$8.$8.)(1<.$8.$8.VFB,+80.)VLF,)R4.)P,(2=.$:.R5.)P,(2<.$:.R6.Vlo,Vsp1,)(4<.$:.VR,VHIA,Vh,VLB,VLF,Vm,(18.&40.Vsp,)Vlo,Vsp1,VFB,+80.VdX,Ves,R7.R10.R?.R>.R=.(4=.(3.&40.(4.VFB,+4:.))(3.&40.(4.VFB,+20.))(3.&40.VFB,)(3.&40.(4.VFB,+40.))R<.R;.(3.&40.VFB,)R:.)(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(5.$1.)))))))))))))))))R9.R8.)")
(* [comment removed for export] *).
  Proof.
    intros mq hq LBq ls dW k96 k104 gb v f m2 CST MU WM HH2 MI2 ST2. rt_facts. flat constr:(FRSH) 4%nat. intros F0 F1 F2 F3.
    flat constr:((A_mpi_client.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST)) 5%nat. intros _ _ _ _ HHq.
    flat constr:((A_mpi_client.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST)) 3%nat. intros _ HSq _.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (HP2 : presA asegs R LBq LF1 sp1 (arl_stklo R) (hstkhi asegs R HIA hq) [(sp1, sp1 + 64)] mq m2).
    { eapply (presA_of_munch asegs R LBq LF1 _ _ _ _ mq m2 (hcs asegs R HIA hq) CSOKq); [| intros c0' Hc; eapply cshd_hcs; [exact HHq| | exact Hc]; clear; lia| exact MU| exact WM].
      unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS0q| clear - LOS LOC; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP SP1; lia]| apply Forall_nil]. }
    eapply (A_mpi_client.cs_nop asegs R HIA) with (mq := mq) (WX := [(sp1, sp1 + 64)]); try eassumption.
    - apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. split; [clear; lia|]. left. clear - SP1. lia.
    - unfold CSF. repeat (apply Forall_cons; [cbn [fst snd cells_size csize Nat.add disjoint_from]; split; [| exact I]|]); [ | | | | apply Forall_nil].
      all: try (clear - SP1 F1 ALO LOS SLO NEEDR ACV GAP; lia).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ra_src (ls : list mpd) (dAr : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "(39.(=.(38.$3=.O1.Ves,)(=.(60.VdX,O1.Vlo,(18.&40.Vsp,))P,(>.$43.(44.O1.)$61.)P,Pi,$8.P,(=.(16.=R1.)(62.R1.(47.+4.(48.O1.))))(>.$63.(64.$:.(65.(4.(46.O1.)R2.)))$66.)(>.$63.(67.(46.O1.)(47.+4.(48.O1.)))$66.)))(>.(<.$3=.)(5<.$3=.O2.#0.)(5=.$3=.O1.)))")
(* [comment removed for export] *).

  Lemma ra_bundle : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pmq,P,(;.&40.)(<.(;.&8.))Phq,(9.$:.VR,VHIA,)PLBq,(35.$36.)Pls,(35.$3=.)PCS,(35.(1;.$8.(35.$1.)))Pv,$8.Pf,$8.PdAr,$3=.P,(4<.$:.VR,VHIA,Vh,VLB,VLF,Vm,(18.&40.Vsp,)Vlo,Vsp1,VFB,+80.VdX,Ves,R8.R7.R6.R5.VdX,R4.(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(5.$1.)))))))))))))))))R3.R2.)P,(70.R6.R2.)(=.(5>.$:.VR,VHIA,R8.(0.(1;.$8.$8.)(1<.$8.$8.VFB,+80.)VLF,)R:.VdX,(3.&40.(4.Vsp1,+40.))Vlo,R3.)(=.(5?.$:.VR,VHIA,(0.(1;.$8.$8.)(1<.$8.$8.VFB,+80.)VLF,)(3.&40.(4.Vsp1,+40.))R3.R9.R8.R:.VdX,)(=.(49.(>.$8.(42.R3.)(42.VdX,)))(=.(16.=(48.R3.))(16.(48.R3.)+2710.)))))")
(* [comment removed for export] *).
  Proof. intros mq hq LBq ls CS v f dAr CST [(I1 & I2 & I3)|I1]; [eapply rider_ext; eassumption| eapply rider_loc; eassumption]. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L21749751998.1000004S2dB". (* [comment removed for export] *)
  Lemma mm_BNE : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pmq,P,(;.&40.)(<.(;.&8.))Phq,(9.$:.VR,VHIA,)PLBq,(35.$36.)PdTA,$3=.PdTB,$3=.PdAr,$3=.Pv,$8.Pf,$8.Pc0,(;.&40.)Pc8,(;.&40.)Pc16,(;.&40.)Pc24,(;.&40.)Pc32,(;.&40.)Pc40,(;.&40.)Pc48,(;.&40.)Pk96,(;.&40.)Pk104,(;.&40.)Pgb,(35.(;.&8.))Pxra,(;.&40.)Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa0,(;.&40.)Pa1,(;.&40.)Pa2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)Ps10v,(;.&40.)Ps11v,(;.&40.)Ps3w,(;.&40.)P,(4<.$:.VR,VHIA,Vh,VLB,VLF,Vm,(18.&40.Vsp,)Vlo,Vsp1,VFB,+80.VdX,Ves,R25.R24.R23.(0.$3=.R22.(0.$3=.R21.(5.$3=.)))VdX,(4=.(3.&40.(4.VFB,+4:.))(3.&40.(4.VFB,+20.))(3.&40.VFB,)(3.&40.(4.VFB,+40.))R16.R15.(3.&40.VFB,)R14.)(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(5.$1.)))))))))))))))))R1?.R1>.)P,(>.$8.(42.R23.)(4.VFB,+20.))P,(>.$8.(42.R23.)(4.VFB,+40.))P,(27.$:.R28.Vsp1,(3:.R20.R1?.R1>.R1=.R1<.R1;.R1:.(3.&40.(4.(42.R23.)+8.))))P,(56.$:.R29.(2?.VR,)(1?.$:.VR,VHIA,Vh,)(18.&40.Vsp,)(4.Vsp1,+40.)(4.Vd,+1.))P,(70.(0.$3=.R27.(0.$3=.R26.(5.$3=.)))R25.)P,(16.(48.R26.)(48.VdA,))P,(>.(;.&40.)R8.(3.&40.(4.(42.R27.)+:.)))P,(49.(>.$8.(42.VdB,)(42.VdX,)))P,(16.(4.(4.R28.(6<.VdA,VdB,))(47.+2.$57.))(4?.VdX,VdA,VdB,))P,(16.(4.(4.R28.(6=.(4.Vd,+1.)))(47.+2.(58.(4.Vd,+1.))))(50.Vd,))(52.$:.(53.$:.VR,VHIA,R2?.Vmo0,)(54.$:.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,(55.VLB,VdX,VdA,VdB,)(4?.VdX,VdA,VdB,)(50.Vd,)Vlo,Vm,Vmo0,)(?.(10.R1>.(3.&40.Vsp1,)Vgp,Vtp,R1=.R1<.R1;.Vsp,(3.&40.Vsp1,)R1:.R19.R18.R17.R16.R15.R14.R13.(3.&40.VFB,)R<.(3.&40.(11.(12.VR,)))(3.&40.(4.VFB,+2:.))(3.&40.(42.VdB,))(3.&40.(42.VdX,))(3.&40.(42.R2;.))(3.&40.(4.(13.VFB,+3.)(11.(12.VR,))))R>.R=.R12.R11.R10.R?.)VF,(3.&40.+9>:;<.)Vfc,(14.(;.&40.))R30.(15.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until s3w. intros CST EAD EBD SPLO UW RAS NLA ES3 NXB HV HF. subst s3w. rt_facts.
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    zstep. zstep.
    eapply (mm_MIDGO mq hq LBq dTA dTB dAr dB v f); [exact CST| exact EAD| exact EBD| exact SPLO| exact UW| exact (ra_bundle _ _ _ _ _ _ _ _ CST RAS)
      | eapply rider_ext; [exact CST| exact (ESB NXB)| exact OB| exact IB2]| exact NLA| clear; lia| exact HV| exact HF].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00i0@D35300034347.178D60189065437.178L12462518772.1  L12562928678.1  L12947140284.3  L19980016842.7  L26983617546.4  L28287220361.4  L28494452040.1  L28800957839.240L34449366402.10 L35442068860.188L35663928186.7  L37889609311.4  L38328690359.229L39280637297.0  L39307640896.7  L40706725791.3  L44150806992.5  L48005370482.5  L48312156349.11 L49037504437.6  L52101693566.15 L52895006273.1  L54021825780.3  L5486630048.3   L56959234767.6  L58406975983.13 L60098763854.3  L60873171499.6  L62037211595.7  L6203936179.1   L65159210099.10 L66151427842.16 L67156766667.4  L8398153729.1   L9356559676.11  Q11968186855.179Q1356123914.191 Q15236711831.175Q15236711831.243Q19402954634.243Q25954107624.179Q28465177121.176Q3375676648.179 Q3421936230.178 Q39029445783.191Q44416079101.179Q45057547415.179Q5265442331.177 Q53878713367.243Q57228775306.178Q58205651829.179Q60189065437.179Q68235297648.178Q9874769418.175 Q9874769418.243 00001?02N02R02W02a03903F03S03X04904`05:05O05Z06406506N06V06g07607_08408i08m09709B09[0:G0:Q0:c0;>0;C0;c0<?0<N0<R0==0>D0>\0?70?Y0@80@90@R0@S0A@0A[0A\0A]0B70BY0CC0CD0DA0Dd0E<0E[S1R3HIA1h2LF2ra2sp3TOP3LFB2dX2FB3sp14gapn3GAP2hq3SPR2F03HTq4SP1R2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13SPR2F04SP1R2HB5Ha_st5Hl_stS2FBS3sp1S2dX2dA2dBS1R3HIA1h2sp3TOP3sp13SP1S2dX3X0q1a2HaS1R2FB3ALO2F1S3sp1S2LF2ra2sp3LFB2dX2FB3sp14gapn3dTBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS2LF2ra2sp3LFB2FB3sp14gapnS1R3HIA1h2sp2lo3TOP1HS1d2D01f2HFS2LF2ra2sp3LFB2FB3sp14gapnSS2dX2dA2dB4NRA04NRB01v2HVS1d1f2HFS2sp2dX3sp13SP11KS2dX2dA2dB1v2HVS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R2sp2lo3SLO3sp13SP1S1R3HIA5NEEDR2sp2lo3LOS3SLO2FB3sp13SP12hq3ALO2F11a2HaS2FBS2dX2FB2BFS2dX2FB3WFBS2dX3dTB4NTB04dTB33NB32K0S1R3HIA1h2dX2dA2dB3BUD4NRA04NRB02hq1v2HV3HVqS1R2lo3LOSS1R3HIA1h3sp11a2HaS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S1R3HIA1h1d2D04BUDF2hq1f2HF4HFRqS3sp12r04SP1M1q1r1H2H02q02H4S2LB4C24H3LBq1CS2FBS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOCS2LF2sp2lo3LFB3sp14gapn3SP1S2LF2sp2lo3LFB2dX3sp14gapn3SP13dTBS2LF2lo3LFB2dX3sp14gapn3LOC3dTBFS2LF3LFB3sp14gapn4SP1R2HBFS2LF2sp2lo3LFB2dX3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2sp2lo3LFB3sp14gapn3SP1FFS2LF3LFB3sp14gapn2HB5Ha_stS2LF2sp2lo3LFB2dX3sp14gapn3SP13dTBS2LF2lo3LFB2dX3sp14gapn3LOC2HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dX3sp14gapn3SP12HB5Ha_st5Hl_stS2LF3LFB2dX3sp14gapn2HB5Ha_st5Hl_stS2LF2lo3LFB3sp14gapn3LOCS2LF2lo3LFB2dX3sp14gapn3LOC3dTB". (* [comment removed for export] *)
  Lemma mm_BEQ : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pmq,P,(;.&40.)(<.(;.&8.))Phq,(9.$:.VR,VHIA,)PLBq,(35.$36.)PdTA,$3=.PdTB,$3=.PdAr,$3=.Pv,$8.Pf,$8.Pc0,(;.&40.)Pc8,(;.&40.)Pc16,(;.&40.)Pc24,(;.&40.)Pc32,(;.&40.)Pc40,(;.&40.)Pc48,(;.&40.)Pk96,(;.&40.)Pk104,(;.&40.)Pgb,(35.(;.&8.))Pxra,(;.&40.)Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa0,(;.&40.)Pa1,(;.&40.)Pa2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)Ps10v,(;.&40.)Ps11v,(;.&40.)Ps3w,(;.&40.)P,(4<.$:.VR,VHIA,Vh,VLB,VLF,Vm,(18.&40.Vsp,)Vlo,Vsp1,VFB,+80.VdX,Ves,R25.R24.R23.(0.$3=.R22.(0.$3=.R21.(5.$3=.)))VdX,(4=.(3.&40.(4.VFB,+4:.))(3.&40.(4.VFB,+20.))(3.&40.VFB,)(3.&40.(4.VFB,+40.))R16.R15.(3.&40.VFB,)R14.)(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(5.$1.)))))))))))))))))R1?.R1>.)P,(>.$8.(42.R23.)(4.VFB,+20.))P,(>.$8.(42.R23.)(4.VFB,+40.))P,(>.$43.(44.R24.)$4:.)P,(27.$:.R29.Vsp1,(3:.R21.R20.R1?.R1>.R1=.R1<.R1;.(3.&40.(4.(42.R24.)+8.))))P,(56.$:.R2:.(2?.VR,)(1?.$:.VR,VHIA,Vh,)(18.&40.Vsp,)(4.Vsp1,+40.)(4.Vd,+1.))P,(70.(0.$3=.R28.(0.$3=.R27.(5.$3=.)))R26.)P,(16.(48.R27.)(48.VdA,))P,(>.(;.&40.)R9.(3.&40.(4.(42.R28.)+:.)))P,(>.$3=.VdB,VdX,)P,(16.(4.(4.(4.R29.(71.VdX,))(6<.VdA,VdB,))(47.+2.$57.))(4?.VdX,VdA,VdB,))P,(16.(4.(4.(4.R29.(72.=))(6=.(4.Vd,+1.)))(47.+2.(58.(4.Vd,+1.))))(50.Vd,))(52.$:.(53.$:.VR,VHIA,R30.Vmo0,)(54.$:.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,(55.VLB,VdX,VdA,VdB,)(4?.VdX,VdA,VdB,)(50.Vd,)Vlo,Vm,Vmo0,)(?.(10.R1?.(3.&40.Vsp1,)Vgp,Vtp,R1>.R1=.R1<.Vsp,(3.&40.Vsp1,)R1;.R1:.R19.R18.R17.R16.R15.R14.(3.&40.VFB,)R=.(3.&40.(11.(12.VR,)))(3.&40.(4.VFB,+2:.))(3.&40.(42.VdX,))(3.&40.(42.VdX,))(3.&40.(42.R2<.))(3.&40.(4.(13.VFB,+3.)(11.(12.VR,))))R?.R>.R13.R12.R11.R10.)VF,(3.&40.+9>>0<.)Vfc,(14.(;.&40.))R31.(15.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until s3w. intros CST EAD EBD ETBN SPLO UW RAS NLA ES3 EQB HV HF. subst s3w. rt_facts. flat constr:(FRSH) 4%nat. intros F0 F1 F2 F3.
    flat constr:((A_mpi_client.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST)) 5%nat. intros CHq SHq MIq STq HHq.
    flat constr:((A_mpi_client.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST)) 6%nat. intros HTq HSq HFq HCSq HVq HFRq.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    unfold CSF in CHq. apply Forall_cons_iff in CHq. flat constr:(CHq) 2%nat. flclear CHq. intros SPHI _. cbn [fst snd] in SPHI.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    unfold mm_fr in SPLO.
    pose proof (munch_refl [(sp1, sp1 + 64)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep.
    lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
    match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
    match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
    pose proof (cs_spill _ _ _ _ _ _ _ _ _ _ m2 CST MU WM HH2 MI2 ST2) as CST2.
    assert (UW2 : UWCM m2).
    { eapply uwc_munch; [exact UW| exact MU| clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia|].
      intros a Ha. cbn [outside]. split; [clear - Ha; lia| exact I]. }
    clear CST UW MU WM.
    edestruct (A_mpi_client.cs_local_facts asegs R HIA) with (i := 1%nat) (d := dTB) as (MTB & NSTB & XWTB & _ & _ & _ & _ & _ & _ & _ & TBLO & OTB); try eassumption; [reflexivity|].
    edestruct (A_mpi_client.cs_w_facts asegs R HIA) as (MWq & _ & _ & _ & XLSq & CRWq & CRWLq & HFW & ASW & WFB & OWq); try eassumption.
    flat constr:(MWq) 2%nat. intros FLt6 _. flat constr:(FLt6) 4%nat. flclear FLt6. intros CXq _ X0q _. flat constr:(MTB) 2%nat. intros FLt7 _. flat constr:(FLt7) 6%nat. flclear FLt7. intros _ _ _ _ _ OWNTB. rewrite ETBN in OWNTB. flat constr:(OWNTB) 2%nat. flclear OWNTB. intros _ NTB0.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. clear MU WM.
    pose proof (conj SPLO I) as SPLOb. clear SPLO.
    pose proof COPY as CPY. unfold mpi_copy_stmtA_c, mpi_copy_stmtA_gen_c, A_MPI_COPY in CPY.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply CPY with (h := hq) (LB := LBq) (LF := LF1) (dX := dTB) (dY := dX) (lo := lo) (d := 0);
        rewrite ?(unsigned_lit sp1) by exact SP1R;
        first [ exact HH2 | exact HK1 | exact MTB | exact NSTB | exact MWq | exact XWTB | exact ST2 | exact LOS | exact MI2 | exact TPV | exact OTB | exact OWq | exact CRWq | exact CRWLq | reflexivity
              | lazymatch goal with
                | |- mpd_sep dTB dX => right; rewrite EBD; clear - WFB; lia
                | |- copy_sep dTB dX _ _ =>
                    split; [intros NN; rewrite EBD; destruct (md_own dX) eqn:EOX; [exfalso; exact (NN eq_refl)| (flat constr:((HFW eq_refl)) 6%nat; intros _ _ _ _ BF _); clear - BF; lia| exfalso; exact (NST eq_refl)]|];
                    split; [intros EO; rewrite ETBN in EO; discriminate EO|];
                    split; [right; left; rewrite ETBN; discriminate|];
                    split; [destruct ASW as [K|K]; [left; exact K| right; clear - K SP1; lia]|];
                    split; [exact XLSq| intros a Ha; clear - Ha X0q; lia]
                | |- lo <= sp1 - 112 - _ => clear - SLO SP1; lia
                | |- sp1 <= htop _ _ _ _ => rewrite HTq; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                | |- md_own dX = LStatic -> _ => intros EO; exfalso; exact (NST EO)
                | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold mul_mpi_PHI, mul_mid_PHI, grow_PHI in *; unfold AVOL_CALL in *; clear - HVq BUD HV NRA0 NRB0; lia
                | |- uw_obj _ _ 16 0 => left; rewrite EBD; split; [clear - F1 ALO; lia| clear; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold mul_mpi_FR, mul_mid_FR, calls_FR, fr_charge in *; clear - HFRq BUDF HF D0; lia
                | |- _ = Z_to_bv 64 (md_addr dTB) => rewrite EBD; reflexivity
                end
              | first [ (lazymatch goal with |- context [cnt24] => idtac end; let C := fresh "C" in match goal with CSx : _ |- _ => pose proof (A_mpi_client.cs_cnt24 asegs R HIA HNDk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CSx) as C end; cbn [length] in C; clear - C C24H; unfold C24_MUL_MPI, C24_COPY_c in *; lia) | match goal with |- ?g => idtac "COPY-PRE-LEFT:" g end ] ]. }
    cbv beta. intros ms4 mo4 (mo1 & [HK1 MF1] & PO).
    destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & mo3 & h3 & LB3 & dTB3 & r
                    & E4 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & FRS3 & RR3).
    injection E4 as Ems Emo. subst ms4 mo4.
    lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
      replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    rewrite (unsigned_lit sp1) in ST3, HP3 by exact SP1R.
    flat constr:(RR3) 4%nat. flclear RR3. intros RV EA3 _ FRP3.
    assert (CST3 : CSTA m3 h3 LB3 [dTA; dTB3] dX (CSFC k96 k104 gb) FSHXL (v + copy_PHI dX) (f + copy_FR 0)).
    { change [dTA; dTB3] with (set_nth 1 [dTA; dTB] dTB3).
      eapply (A_mpi_client.cs_binop_l asegs R HIA) with (i := 1%nat) (dX := dTB) (mq := m2) (hq := hq); try eassumption; reflexivity. }
    flat constr:(SPLOb) 2%nat. flclear SPLOb. intros SPLO _.
    assert (SPLO3 : rw_cells asegs m3 sp1 [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 (Z_to_bv 64 (md_addr dX)); C8 c48; C8 (Z_to_bv 64 (md_addr dAr + 8))]).
    { eapply (presA_rw_cells asegs R); [exact HP3| exact SPLO| apply client_range_stack; clear; lia|].
      cbn [disjoint_from cells_size csize Nat.add]. split; [rewrite EBD; clear - F1 ALO LOS SLO SP1 NEEDR; lia| exact I]. }
    assert (UW3 : UWCM m3).
    { rewrite <- HSq. eapply (uwc_presA_w R); [exact HP3| rewrite HSq; exact UW2| clear; lia| | clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
      intros a Ha. cbn [outside]. split; [rewrite EBD; clear - Ha F1 ALO LOS SLO SP1 NEEDR; lia| exact I]. }
    assert (RAS3 : ra_src [dTA; dTB3] dAr) by (destruct RAS as [K|K]; [left; exact K| right; exact K]).
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
    pose proof (AIh_laws asegs R HIA h3) as LAWS3. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV3. clear LAWS KINV.
    flat constr:((A_mpi_client.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST3)) 5%nat. intros CH3 _ _ _ HH3'.
    flat constr:((A_mpi_client.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST3)) 5%nat. intros _ HS3' _ HCS3' _.
    pose proof (hcs_ok asegs R HIA h3) as CSOK3. pose proof (hcs_stack asegs R HIA h3) as SCS03.
    assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS03| clear - LOS; lia| rewrite HS3'; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    unfold CSF in CH3. apply Forall_cons_iff in CH3. flat constr:(CH3) 2%nat. flclear CH3. intros SPHI3 _. cbn [fst snd] in SPHI3.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    destruct RV as [(-> & _ & NB3)|(-> & _)].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      replace (FB + 74) with (md_addr dTB3 + 10) by (rewrite EA3, EBD; clear; lia).
      replace (FB + 72) with (md_addr dTB3 + 8) by (rewrite EA3, EBD; clear; lia).
      replace (FB + 64) with (md_addr dTB3) by (rewrite EA3, EBD; clear; lia).
      eapply (mm_MIDGO m3 h3 LB3 dTA dTB3 dAr dTB3 _ _); [exact CST3| exact EAD| rewrite EA3; exact EBD| exact SPLO3| exact UW3| exact (ra_bundle _ _ _ _ _ _ _ _ CST3 RAS3)
        | eapply (rider_loc _ _ _ _ _ _ _ 1%nat dTB3); [exact CST3| reflexivity]| exact NLA| pose proof NRB0 as K0; rewrite EQB in K0 |- *; clear - NB3 NTB0 K0; lia| clear - HV; lia| clear - HF; lia].
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      eapply (mm_CLEAN m3 h3 LB3 dTA dTB3 dX _ _ MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| exact EAD| rewrite EA3; exact EBD| exact SPLO3| exact UW3| right; reflexivity| | | exact BUD| exact BUDF| clear; lia].
      + unfold mul_mid_PHI, grow_PHI in HV; unfold AVOL_CALL in *. clear - HV NRA0 NRB0. lia.
      + unfold mul_mid_FR, calls_FR, fr_charge in *. clear - HF D0. lia.
    all: match goal with |- ?g => idtac "BEQ-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis OA : opnd_sep dX dA lo (bv_unsigned sp).
  Hypothesis IA2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "P,(>.$43.(44.VdA,)$61.)P,Pi,$8.P,(=.(16.=R1.)(62.R1.(47.+4.(48.VdA,))))(>.$63.(64.$:.(65.(4.(46.VdA,)R2.)))$66.)(>.$63.(67.(46.VdA,)(47.+4.(48.VdA,)))$66.)")
(* [comment removed for export] *).
  Hypothesis ESA : md_addr dA <> md_addr dX -> In dA es.
  Hypothesis XR : 0 <= md_addr dX < 2^64.
  Hypothesis AR : 0 <= md_addr dA < 2^64.
  Hypothesis BR : 0 <= md_addr dB < 2^64.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0120@D25900232977.251D35300034347.182D60189065437.182D60189065437.251L10571287284.3  L12947140284.3  L14665545899.1  L16824638007.234L18915067017.4  L19980016842.7  L20343453395.5  L20696119022.2  L26823684373.2  L26983617546.4  L28494452040.1  L34449366402.10 L35663928186.7  L39280637297.0  L40708709545.5  L40708822953.2  L44150806992.5  L46341128227.5  L46341128227.6  L48934549152.3  L49037504437.6  L52101693566.15 L53270961206.5  L59314955108.4  L60098763854.3  L60178444865.1  L60873171499.6  L61263298563.1  L62037211595.7  L6203936179.1   L62677235295.7  L65159210099.12 L65649988650.5  L66151427842.16 L66421750305.4  L66953995364.1  L67156766667.4  L67182365775.6  L795101770.11   L7960699581.11  L9356559676.11  Q11968186855.183Q25954107624.183Q28465177121.180Q28465177121.248Q3375676648.183 Q3421936230.182 Q3421936230.250 Q37991553687.247Q37991881883.179Q44416079101.183Q45057547415.183Q5265442331.181 Q5265442331.249 Q57228775306.182Q57228775306.250Q58205651829.183Q60189065437.183Q66561630474.247Q66561959686.179Q68235297648.182Q68235297648.25100001J02Y03h05;05E05O05S05m06:06R06d06k07307@07E07l08A08B08S08Z08k09<09P09[0:00:e0;70;I0;S0;W0;i0;m0<H0<M0<g0=L0=^0>:0>K0>N0>]0?60?Z0@C0@n0B50B60BO0Bo0C00C]0DQ0E30EN0EO0EP0Ej0FK0G50Gf0Gg0Hd0IC0I[0J>0JhS1R3HIA1h2LF2ra2sp3TOP3LFB2dX2FB3sp14gapn3GAP2hq3dTA3SPR2F03HTq4SP1R2h33HT32HB5Ha_st5Hl_stS1R3HIA1h2LF2ra2sp3TOP3LFB2dA2FB3sp14gapn3GAP2hq3SPR2F03HTq4SP1R2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13SPR2F04SP1R2HB5Ha_st5Hl_stS1R5NEEDR2LF2ra2sp2lo3LOS3SLO3LFB2dX2FB3sp14gapn3SP13dTA3SPR2F04SP1R2HB5Ha_st5Hl_stS2dX2FB2BFS2dX2dA2dBS2FBS2LF2ra2sp3LFB2FB3sp14gapnS1R2FB3ALO2F1S1R3HIA1h2sp3TOP3sp13SP1S2dX2dA2dB3HV03CP0S2dA2dBS2dX3HV0S2dX3X0q1a2HaS3sp1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACPS1R3HIA1h2sp2lo3TOP1HSS2dA2dB1d3HF03CP0S1d3HF0S2sp2dX3sp13SP11KS2dA2dB1d3HF03CP0S2dA2dB1d2D03HF03CP0S2dX2FB3WFBS1R2sp2lo3SLO3sp13SP1S1R3HIA5NEEDR2sp2lo3LOS3SLO2FB3sp13SP12hq3ALO2F11a2HaS2dX2dA2dB3HV03CP0S2dX2dA2KA1E2dB2KBS1R2lo3LOSS2FBS1R3HIA1h3sp11a2HaS2dAS1R5NEEDR2sp2lo3LOS3SLO3SPRS3sp1S2dX2dA2dB4NRB03HV03CP02K0S1R3HIA1h2dA2dB1d2D04BUDF2hq3CP04HFRqS2dX2dA2dB3HV03CP0S3sp12r04SP1M1q1r1H2H02q02H4S2dA2dB4NRA04NRB0S1dS2LB4C24H3LBq1CS2dX3dTA4NTA04dTA33NA32K0S1R3HIA1h2dX2dB3BUD4NRA04NRB02hq3HVqS1R5NEEDR2sp2lo3LOS3SLO2FB3sp13SP13ALO2F1S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3SPRS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA2FB3sp14gapn3SP13ALO2F12HB5Ha_st5Hl_stFS2LF3LFB3sp14gapn4SP1R2HBS2LF3LFB2dX3sp14gapn3dTA4SP1R2HBFS2LF2sp2lo3LFB2dA3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2sp2lo3LFB2dX2FB3sp14gapn3SP13dTA2HB5Ha_st5Hl_stS2LF2sp2lo3LFB2dX3sp14gapn3SP13dTAS2LF2sp2lo3LFB3sp14gapn3SP1FFS2LF3LFB3sp14gapn2HB5Ha_stS2LF3LFB2dX3sp14gapn3dTA2HB5Ha_stS2LF2lo3LFB2dA3sp14gapn3LOC2HB5Ha_st5Hl_stS2LF2lo3LFB2dX2FB3sp14gapn3LOC3dTA2HB5Ha_st5Hl_stFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB2dA3sp14gapn3SP12HB5Ha_st5Hl_stS2LF2lo3LFB2dX3sp14gapn3LOC3dTAS2LF2lo3LFB3sp14gapn3LOCS2LF3LFB2dA3sp14gapn2HB5Ha_st5Hl_stS2LF3LFB2dX2FB3sp14gapn3dTA2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  Lemma mm_BODY : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pmq,P,(;.&40.)(<.(;.&8.))Phq,(9.$:.VR,VHIA,)PLBq,(35.$36.)PdTA,$3=.PdTB,$3=.Pc0,(;.&40.)Pc8,(;.&40.)Pc16,(;.&40.)Pc24,(;.&40.)Pc32,(;.&40.)Pc40,(;.&40.)Pc48,(;.&40.)Pc56,(;.&40.)Pk96,(;.&40.)Pk104,(;.&40.)Pgb,(35.(;.&8.))Pxra,(;.&40.)Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa0,(;.&40.)Pa1,(;.&40.)Pa2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)Ps3v,(;.&40.)P,(4<.$:.VR,VHIA,Vh,VLB,VLF,Vm,(18.&40.Vsp,)Vlo,Vsp1,VFB,+80.VdX,Ves,R21.R20.R1?.(0.$3=.R1>.(0.$3=.R1=.(5.$3=.)))VdX,(4=.(3.&40.(4.VFB,+4:.))(3.&40.(4.VFB,+20.))(3.&40.VFB,)(3.&40.(4.VFB,+40.))R14.R13.(3.&40.VFB,)R12.)(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.+?1.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.+?2.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.+?3.))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(0.$1.(2:.(3.&8.=))(5.$1.)))))))))))))))))==)P,(>.$8.(42.R1?.)(4.VFB,+20.))P,(>.$8.(42.R1?.)(4.VFB,+40.))P,(>.$43.(44.R21.)$4:.)P,(>.$43.(44.R21.)$4:.)P,(27.$:.R26.Vsp1,(3:.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.))P,(56.$:.R27.(2?.VR,)(1?.$:.VR,VHIA,Vh,)(18.&40.Vsp,)(4.Vsp1,+40.)(4.Vd,+1.))(52.$:.(53.$:.VR,VHIA,R27.Vmo0,)(54.$:.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,(55.VLB,VdX,VdA,VdB,)(4?.VdX,VdA,VdB,)(50.Vd,)Vlo,Vm,Vmo0,)(?.(10.R18.(3.&40.Vsp1,)Vgp,Vtp,R17.R16.R15.Vsp,(3.&40.Vsp1,)R14.R13.R12.R11.R10.R?.R>.R=.(3.&40.VFB,)R8.(3.&40.(11.(12.VR,)))(3.&40.(4.VFB,+2:.))(3.&40.VB,)(3.&40.VX,)(3.&40.VA,)(3.&40.(4.(13.VFB,+3.)(11.(12.VR,))))(3.&40.(4.VFB,+20.))(3.&40.VFB,)R<.R;.R:.R9.)VF,(3.&40.+9>::8.)Vfc,(14.(;.&40.))R28.(15.$:.)))")
(* [comment removed for export] *).
  Proof.
    intros until s3v. intros CST EAD EBD ETAN ETBN SPLO UW. rewrite XE, AE, BE. rt_facts. flat constr:(FRSH) 4%nat. intros F0 F1 F2 F3.
    assert (HV0 : 0 + copy_PHI dA + copy_PHI dB + mul_mid_PHI dA dB + 2 * AVOL_CALL <= mul_mpi_PHI dX dA dB) by (unfold mul_mpi_PHI; clear; lia).
    assert (HF0 : 0 + 2 * copy_FR 0 + mul_mid_FR (d + 1) + 2 * fr_charge (d + 1) <= mul_mpi_FR d) by (unfold mul_mpi_FR; clear; lia).
    assert (CP0 : 0 <= copy_PHI dA /\ 0 <= copy_PHI dB /\ 0 <= copy_FR 0) by (unfold copy_PHI, grow_PHI, copy_FR, calls_FR, fr_charge; unfold AVOL_CALL; clear - NRA0 NRB0; lia).
    flat constr:((A_mpi_client.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST)) 5%nat. intros CHq SHq MIq STq HHq.
    flat constr:((A_mpi_client.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST)) 6%nat. intros HTq HSq HFq HCSq HVq HFRq.
    pose proof (hcs_ok asegs R HIA hq) as CSOKq. pose proof (hcs_stack asegs R HIA hq) as SCS0q.
    assert (SCSq : crange (hcs asegs R HIA hq) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0q| clear - LOS; lia| rewrite HSq; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
    pose proof (AIh_laws asegs R HIA hq) as LAWS. pose proof (KF_kinv asegs R HIA hq mo0) as KINV.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    unfold mm_fr in SPLO.
    pose proof (munch_refl [(sp1, sp1 + 64)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KA; zify_cond KA; rewrite ?Z.mod_small in KA by (first [exact XR| exact AR]).
    - (* [comment removed for export] *)
      assert (EQA : dA = dX) by (destruct SXA as [E|E]; [symmetry; exact E| exfalso; clear - E KA; lia]).
      rewrite <- KA. clear MU WM.
      edestruct (A_mpi_client.cs_local_facts asegs R HIA) with (i := 0%nat) (d := dTA) as (MTA & NSTA & XWTA & _ & _ & _ & _ & _ & _ & _ & TALO & OTA); try eassumption; [reflexivity|].
      edestruct (A_mpi_client.cs_w_facts asegs R HIA) as (MWq & _ & _ & _ & XLSq & CRWq & CRWLq & HFW & ASW & WFB & OWq); try eassumption.
      flat constr:(MWq) 2%nat. intros FLt8 _. flat constr:(FLt8) 4%nat. flclear FLt8. intros CXq _ X0q _. flat constr:(MTA) 2%nat. intros FLt9 _. flat constr:(FLt9) 6%nat. flclear FLt9. intros _ _ _ _ _ OWNTA. rewrite ETAN in OWNTA. flat constr:(OWNTA) 2%nat. flclear OWNTA. intros _ NTA0.
      pose proof (munch_refl ([] : list ivl) mq) as MU. pose proof (wmono_refl asegs mq) as WM.
      (* [comment removed for export] *)
      zstep. zstep. zstep. clear MU WM.
      pose proof (conj SPLO I) as SPLOb. clear SPLO.
      pose proof COPY as CPY. unfold mpi_copy_stmtA_c, mpi_copy_stmtA_gen_c, A_MPI_COPY in CPY.
      eapply aevtA_call.
      { intros mo1 [HK1 MF1].
        eapply CPY with (h := hq) (LB := LBq) (LF := LF1) (dX := dTA) (dY := dX) (lo := lo) (d := 0);
          rewrite ?(unsigned_lit sp1) by exact SP1R;
          first [ exact HHq | exact HK1 | exact MTA | exact NSTA | exact MWq | exact XWTA | exact STq | exact LOS | exact MIq | exact TPV | exact OTA | exact OWq | exact CRWq | exact CRWLq | reflexivity
                | lazymatch goal with
                  | |- mpd_sep dTA dX => right; rewrite EAD; clear - WFB; lia
                  | |- copy_sep dTA dX _ _ =>
                      split; [intros NN; rewrite EAD; destruct (md_own dX) eqn:EOX; [exfalso; exact (NN eq_refl)| (flat constr:((HFW eq_refl)) 6%nat; intros _ _ _ _ BF _); clear - BF; lia| exfalso; exact (NST eq_refl)]|];
                      split; [intros EO; rewrite ETAN in EO; discriminate EO|];
                      split; [right; left; rewrite ETAN; discriminate|];
                      split; [destruct ASW as [K|K]; [left; exact K| right; clear - K SP1; lia]|];
                      split; [exact XLSq| intros a Ha; clear - Ha X0q; lia]
                  | |- lo <= sp1 - 112 - _ => clear - SLO SP1; lia
                  | |- sp1 <= htop _ _ _ _ => rewrite HTq; clear - SP1 TOP; lia
                  | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                  | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                  | |- md_own dX = LStatic -> _ => intros EO; exfalso; exact (NST EO)
                  | |- havol _ _ _ _ + _ <= AVOL_MAX => unfold mul_mpi_PHI, mul_mid_PHI, copy_PHI, grow_PHI in *; unfold AVOL_CALL in *; rewrite ?EQA in *; clear - HVq BUD HV0 NRA0 NRB0; lia
                  | |- uw_obj _ _ 16 0 => left; rewrite EAD; split; [clear - F1 ALO; lia| clear; lia]
                  | |- hfr _ _ _ _ + _ <= FR_MAX => unfold mul_mpi_FR, mul_mid_FR, calls_FR, fr_charge in *; clear - HFRq BUDF HF0 D0 CP0; lia
                  | |- _ = Z_to_bv 64 (md_addr dTA) => rewrite EAD; reflexivity
                  end
                | first [ (lazymatch goal with |- context [cnt24] => idtac end; let C := fresh "C" in match goal with CSx : _ |- _ => pose proof (A_mpi_client.cs_cnt24 asegs R HIA HNDk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CSx) as C end; cbn [length] in C; clear - C C24H; unfold C24_MUL_MPI, C24_COPY_c in *; lia) | match goal with |- ?g => idtac "COPY-PRE-LEFT:" g end ] ]. }
      cbv beta. intros ms4 mo4 (mo1 & [HK1 MF1] & PO).
      destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m3 & mo3 & h3 & LB3 & dTA3 & r
                      & E4 & MI3 & ST3 & MF3 & HP3 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & FRS3 & RR3).
      injection E4 as Ems Emo. subst ms4 mo4.
      lazymatch goal with |- aevtS _ _ (mkCfg (MS _ _ (ret_pc (Z_to_bv 64 ?rr)) _ _ _ _) _) =>
        replace (ret_pc (Z_to_bv 64 rr)) with (Z_to_bv 64 rr) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      rewrite (unsigned_lit sp1) in ST3, HP3 by exact SP1R.
      flat constr:(RR3) 4%nat. flclear RR3. intros RV EA3 _ FRP3.
      assert (CST3 : CSTA m3 h3 LB3 [dTA3; dTB] dX (CSFC k96 k104 gb) FSHXL (0 + copy_PHI dX) (0 + copy_FR 0)).
      { change [dTA3; dTB] with (set_nth 0 [dTA; dTB] dTA3).
        eapply (A_mpi_client.cs_binop_l asegs R HIA) with (i := 0%nat) (dX := dTA) (mq := mq) (hq := hq); try eassumption; reflexivity. }
      flat constr:(SPLOb) 2%nat. flclear SPLOb. intros SPLO _.
      assert (SPLO3 : rw_cells asegs m3 sp1 [C8 c0; C8 c8; C8 c16; C8 c24; C8 c32; C8 c40; C8 c48; C8 c56]).
      { eapply (presA_rw_cells asegs R); [exact HP3| exact SPLO| apply client_range_stack; clear; lia|].
        cbn [disjoint_from cells_size csize Nat.add]. split; [rewrite EAD; clear - F1 ALO LOS SLO SP1 NEEDR; lia| exact I]. }
      assert (UW3 : UWCM m3).
      { rewrite <- HSq. eapply (uwc_presA_w R); [exact HP3| rewrite HSq; exact UW| clear; lia| | clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia].
        intros a Ha. cbn [outside]. split; [rewrite EAD; clear - Ha F1 ALO LOS SLO SP1 NEEDR; lia| exact I]. }
      apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF3))).
      pose proof (AIh_laws asegs R HIA h3) as LAWS3. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV3. clear LAWS KINV.
      flat constr:((A_mpi_client.cs_cells asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST3)) 5%nat. intros CH3 _ _ _ HH3'.
      flat constr:((A_mpi_client.cs_budget asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es _ _ _ _ _ _ _ _ _ CST3)) 5%nat. intros _ HS3' _ HCS3' _.
      pose proof (hcs_ok asegs R HIA h3) as CSOK3. pose proof (hcs_stack asegs R HIA h3) as SCS03.
      assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS03| clear - LOS; lia| rewrite HS3'; pose proof (hm_top asegs R HIA h LB LF m H0M); clear - H TOP; lia]).
      pose proof (munch_refl [(sp1, sp1 + 64)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      destruct RV as [(-> & _ & NA3)|(-> & _)].
      + (* [comment removed for export] *)
        zstep. zstep. zstep.
        lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
        match goal with H : HM asegs R HIA h3 LB3 LF1 m4 |- _ => rename H into HH4 end.
        match goal with H : mem_inv asegs m4 |- _ => rename H into MI4 end.
        match goal with H : stk asegs m4 lo sp1 |- _ => rename H into ST4 end.
        pose proof (cs_spill _ _ _ _ _ _ _ _ _ _ m4 CST3 MU WM HH4 MI4 ST4) as CST4.
        assert (UW4 : UWCM m4).
        { eapply uwc_munch; [exact UW3| exact MU| clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia|].
          intros a Ha. cbn [outside]. split; [clear - Ha; lia| exact I]. }
        clear CST3 UW3 MU WM. pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
        zstep. zstep.
        replace (FB + 40) with (md_addr dTA3 + 8) in * by (rewrite EA3, EAD; clear; lia).
        replace (Z_to_bv 64 (FB + 32)) with (Z_to_bv 64 (md_addr dTA3)) by (rewrite EA3, EAD; reflexivity).
        assert (NLA : md_n dTA3 <= md_n dA) by (pose proof NRA0 as K0; rewrite EQA in K0 |- *; clear - NA3 NTA0 K0; lia).
        zstep. if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by (first [exact XR| exact BR]).
        * (* [comment removed for export] *)
          eapply (mm_BNE m4 h3 LB3 dTA3 dTB dTA3 _ _); [exact CST4| rewrite EA3; exact EAD| exact EBD| eassumption| exact UW4| right; reflexivity| exact NLA| rewrite EA3, EAD; f_equal; clear; lia| intros E; apply KB; symmetry; exact E| |].
          -- rewrite EQA in HV0 |- *. clear - HV0 CP0. lia.
          -- clear - HF0 CP0. lia.
        * (* [comment removed for export] *)
          assert (EQB : dB = dX) by (destruct SXB as [E|E]; [symmetry; exact E| exfalso; clear - E KB; lia]).
          rewrite <- KB.
          eapply (mm_BEQ m4 h3 LB3 dTA3 dTB dTA3 _ _); [exact CST4| rewrite EA3; exact EAD| exact EBD| exact ETBN| eassumption| exact UW4| right; reflexivity| exact NLA| rewrite EA3, EAD; f_equal; clear; lia| exact EQB| |].
          -- rewrite EQA in HV0 |- *. rewrite EQB in HV0 |- *. clear - HV0. lia.
          -- clear - HF0. lia.
      + (* [comment removed for export] *)
        clear MU WM. pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
        zstep. zstep. zstep.
        eapply (mm_CLEAN m3 h3 LB3 dTA3 dTB dX _ _ MBEDTLS_ERR_MPI_ALLOC_FAILED); [exact CST3| rewrite EA3; exact EAD| exact EBD| exact SPLO3| exact UW3| right; reflexivity| | | exact BUD| exact BUDF| clear; lia].
        * pose proof NRA0 as K0. rewrite EQA in HV0, K0 |- *. unfold mul_mid_PHI, grow_PHI in HV0; unfold AVOL_CALL in *. clear - HV0 CP0 K0 NRB0. lia.
        * unfold mul_mid_FR, calls_FR, fr_charge in *. clear - HF0 D0 CP0. lia.
    - (* [comment removed for export] *)
      zstep. zstep. zstep.
      lazymatch goal with |- aevtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      match goal with H : HM asegs R HIA hq LBq LF1 m2 |- _ => rename H into HH2 end.
      match goal with H : mem_inv asegs m2 |- _ => rename H into MI2 end.
      match goal with H : stk asegs m2 lo sp1 |- _ => rename H into ST2 end.
      pose proof (cs_spill _ _ _ _ _ _ _ _ _ _ m2 CST MU WM HH2 MI2 ST2) as CST2.
      assert (UW2 : UWCM m2).
      { eapply uwc_munch; [exact UW| exact MU| clear - SP1 SLO LOS ALO ACP NEEDR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia|].
        intros a Ha. cbn [outside]. split; [clear - Ha; lia| exact I]. }
      clear CST UW MU WM. pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      assert (RAS : ra_src [dTA; dTB] dA) by (left; split; [apply ESA; intros E; apply KA; symmetry; exact E| split; [exact OA| exact IA2]]).
      zstep. if_cases KB; zify_cond KB; rewrite ?Z.mod_small in KB by (first [exact XR| exact BR]).
      + (* [comment removed for export] *)
        assert (EQB : dB = dX) by (destruct SXB as [E|E]; [symmetry; exact E| exfalso; clear - E KB; lia]).
        rewrite <- KB.
        eapply (mm_BEQ m2 hq LBq dTA dTB dA _ _); [exact CST2| exact EAD| exact EBD| exact ETBN| eassumption| exact UW2| exact RAS| clear; lia| reflexivity| exact EQB| |].
        * rewrite EQB in HV0 |- *. clear - HV0 CP0. lia.
        * clear - HF0 CP0. lia.
      + (* [comment removed for export] *)
        eapply (mm_BNE m2 hq LBq dTA dTB dA _ _); [exact CST2| exact EAD| exact EBD| eassumption| exact UW2| exact RAS| clear; lia| reflexivity| intros E; apply KB; symmetry; exact E| |].
        * clear - HV0 CP0. lia.
        * clear - HF0 CP0. lia.
    all: match goal with |- ?g => idtac "BODY-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Fr.

  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis IMGk : asan_img_ok AL.
  Hypothesis CMUL : mpi_core_mul_stmtA asegs R HIA A_MPI_CORE_MUL.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_MM.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_MM.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_MM.
  Hypothesis UWX : uw_obj R (md_addr dX) 16 d.
  Hypothesis BUD : havol asegs R HIA h + mul_mpi_PHI dX dA dB <= AVOL_MAX.
  Hypothesis BUDF : hfr asegs R HIA h + mul_mpi_FR d <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_MUL_MPI <= C24MAX.
  Hypothesis COPY : mpi_copy_stmtA_c asegs R HIA A_MPI_COPY.
  Hypothesis MBe : mpd_at asegs m LB dB.
  Hypothesis SXB : mpd_sep dX dB.
  Hypothesis OB : opnd_sep dX dB lo (bv_unsigned sp).
  Hypothesis IB2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "P,(>.$43.(44.VdB,)$61.)P,Pi,$8.P,(=.(16.=R1.)(62.R1.(47.+4.(48.VdB,))))(>.$63.(64.$:.(65.(4.(46.VdB,)R2.)))$66.)(>.$63.(67.(46.VdB,)(47.+4.(48.VdB,)))$66.)")
(* [comment removed for export] *).
  Hypothesis ESB : md_addr dB <> md_addr dX -> In dB es.
  Hypothesis NRA0 : 0 <= md_n dA.
  Hypothesis NRB0 : 0 <= md_n dB.
  Hypothesis SXA : mpd_sep dX dA.
  Hypothesis OA : opnd_sep dX dA lo (bv_unsigned sp).
  Hypothesis IA2 : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "P,(>.$43.(44.VdA,)$61.)P,Pi,$8.P,(=.(16.=R1.)(62.R1.(47.+4.(48.VdA,))))(>.$63.(64.$:.(65.(4.(46.VdA,)R2.)))$66.)(>.$63.(67.(46.VdA,)(47.+4.(48.VdA,)))$66.)")
(* [comment removed for export] *).
  Hypothesis ESA : md_addr dA <> md_addr dX -> In dA es.
  Hypothesis XR : 0 <= md_addr dX < 2^64.
  Hypothesis AR : 0 <= md_addr dA < 2^64.
  Hypothesis BR : 0 <= md_addr dB < 2^64.
  Hypothesis ESF : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "(3<.$3=.Le,$3=.(=.(3>.(3?.VR,)(40.$36.VLB,(41.VLF,))Vlo,(42.R1.)+10.)(=.P,(>.$43.(44.R1.)$45.)(=.(38.(1;.$8.$8.)(1<.$8.$8.(46.R2.)(47.+4.(48.R2.)))VLB,)(16.+1.(48.R2.)))(=.(39.(16.(4.(42.R1.)+10.)Vlo,)(16.(18.&40.Vsp,)(42.R1.)))(=.P,(>.$43.(44.VdX,)$45.)(39.(16.(4.(42.R2.)+10.)(46.VdX,))(16.(4.(46.VdX,)(47.+4.(48.VdX,)))(42.R2.)))(=.(39.(49.(>.$43.(44.VdX,)$45.))(39.(>.$43.(44.R1.)$4:.)(39.(16.(4.(46.VdX,)(47.+4.(48.VdX,)))(46.R1.))(16.(4.(46.R1.)(47.+4.(48.R1.)))(46.VdX,)))))(=.(39.(16.(4.(42.VdX,)+10.)(42.R1.))(16.(4.(42.R1.)+10.)(42.VdX,)))P,(49.(>.$43.(44.R1.)$4:.))(39.(16.(4.(42.VdX,)+10.)(46.R2.))(16.(4.(46.R2.)(47.+4.(48.R2.)))(42.VdX,)))))))))Ves,)")
(* [comment removed for export] *).
  Hypothesis MX : mpd_at asegs m LB dX.
  Hypothesis OXs : aobj asegs AL CS m (md_addr dX) 16.
  Hypothesis ESM : Forall (fun e => mpd_at asegs m LB e /\ aobj asegs AL CS m (md_addr e) 16) es.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00^0@L14714406535.1  L15263976489.0  L1540877545.3   L16709757489.1  L17532288201.0  L17609341892.1  L1919789925.3   L19698478532.1  L19954847564.12 L19955371082.4  L2275137097.0   L26892418956.1  L27818198441.210L31102187327.1  L33958100529.1  L34979112605.7  L37336920691.5  L39616818408.1  L40281191306.3  L45223079498.4  L45223603532.12 L47373672618.4  L50790580594.6  L50794195360.5  L51822029493.3  L52946684648.1  L56523586534.1  L56658999053.1  L59308586248.2  L61970232519.6  L62018535662.1  L62037211595.7  L62280601709.3  L64500993267.5  L66151427842.16 L66925224090.211L696052593.2    L9356559645.11  Q10591678745.210Q19547491027.210Q19561562592.211Q33227107930.210Q34671242282.211Q35333705577.211Q9634015263.211 Q9643860780.210 00000300400@00D00E00F00R00S00T00U00V00Z01401701;01V01g01k02402502602G02^02o03;03?03C03G03M03]03`04;04G04X05<05V05^06I06`07D07h08?08V08m09G09aS1eSS2sp3sp13SP1S2FBSFS2sp3sp13SP1FFFSS2spS2LF2ra2sp3LFB2FB3sp14gapnS1eS2FBS1R5NEEDR2sp2lo3SLO3sp13SP1S2sp3sp14gapn3GAPS2FBS1R3HIA1hFFS2sp3sp14gapn3GAPS1R5NEEDR2sp2lo3LOS3SLOS2sp3sp13SP14gapnS2sp3sp13SP1S2FBS2FBS2spS1i2HiS2sp2FB3sp14gapnS1RS1R5NEEDR2sp2lo3LOS3SLO3SPRS2sp3sp13SP1S2sp3sp13SP14gapnS2sp2r03SPA1q1r1H2H02q02H42FB3F642F8S2LF2ra2sp3LFB2FB3sp14gapnS2sp3SPRS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3SPR3sp13SP1S2LF2sp3LFB2FB3sp14gapnS2LF2ra2sp3LFB3SPR2FB3sp12F02F84gapnS2LF2ra2sp3LFB3SPR2FB3sp12F02F84gapnS2LF2sp3LFB2FB3sp14gapnS2LF2sp3LFB2FB3sp14gapnS2LF2sp3LFB2FB3sp14gapnS2LF2sp3LFB2FB3sp12F04gapnS2LF2sp3LFB2FB3sp12F04gapn". (* [comment removed for export] *)
  Lemma mm_MAIN : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "Pt0,(;.&40.)Pt1,(;.&40.)Pt2,(;.&40.)Pa3,(;.&40.)Pa4,(;.&40.)Pa5,(;.&40.)Pa6,(;.&40.)Pa7,(;.&40.)Pt3,(;.&40.)Pt4,(;.&40.)Pt5,(;.&40.)Pt6,(;.&40.)P,(25.$:.VR,VHIA,Vh,Vmo0,)P,(2<.$:.Vm,Vlo,(18.&40.Vsp,))P,(2=.$:.Vm,)P,(56.$:.Vm,(2?.VR,)(1?.$:.VR,VHIA,Vh,)(18.&40.Vs0,)(18.&40.Vsp,)Vd,)(73.$:.(54.$:.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,(55.VLB,VdX,VdA,VdB,)(4?.VdX,VdA,VdB,)(50.Vd,)Vlo,Vm,Vmo0,)(74.(?.(10.Vra,Vsp,Vgp,Vtp,R10.R?.R>.Vs0,Vs1,(3.&40.VX,)(3.&40.VA,)(3.&40.VB,)R=.R<.R;.R:.R9.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(3.&40.$33.)Vfc,(14.(;.&40.))Vm,(15.$:.))Vmo0,))")
(* [comment removed for export] *).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HK0 ST MI UW. rt_facts.
    pose proof (hm_top asegs R HIA h LB LF m H0M) as HTOP.
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo0) as KINV.
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0). { eapply pro_walk; [exact H0M| exact ST| exact MI]. }
    cbv beta. intros ms1 S1. unfold S1P in S1.
    destruct S1 as (FB & sp1 & h1 & m1 & xra & y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & w0 & w1 & w2 & padA & padB
                    & j0 & j8 & j16 & j24 & j32 & j40 & j48 & j56 & j96 & j104
                    & -> & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & TAC & TBC & FSHX & SAVE & SPILL & SThi & STlo & MI1 & PRES0).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS.
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ _ _ PRES0) as HP01.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR; lia).
    (* [comment removed for export] *)
    assert (UW1 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply (uwc_presA R); [exact HP01| exact UW| clear; lia| intros a Ha; exact I| clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR; lia]. }
    assert (UWF : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) (sp1 + 64) (d + 1)).
    { pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UW1| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0]. }
    (* [comment removed for export] *)
    unfold SPILLL in SPILL. chunk_split SPILL 8%nat SPLO SPHI. replace (sp1 + 64) with (sp1 + 64) in SPHI by reflexivity.
    set (gapn := Z.to_nat (bv_unsigned sp + -104 - (sp1 + 120))).
    destruct (stk_carve asegs m1 (sp1 + 120) (bv_unsigned sp + -104) gapn SThi ltac:(subst gapn; clear - SP1; lia)) as [_ [gb GAPC]].
    assert (GAP : Z.of_nat gapn = bv_unsigned sp + -104 - (sp1 + 120)) by (subst gapn; clear - SP1; lia).
    replace (bv_unsigned sp + -104 - Z.of_nat gapn) with (sp1 + 120) in GAPC by (clear - GAP; lia).
    (* [comment removed for export] *)
    assert (TR : forall e, mpd_at asegs m LB e -> aobj asegs AL CS m (md_addr e) 16 -> client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_addr e) 16 ->
                 mpd_at asegs m1 LB e /\ aobj asegs AL (hcs asegs R HIA h1) m1 (md_addr e) 16).
    { intros e ME OE CRE. rewrite Ehcs. split.
      - eapply (mpd_at_heap_presx asegs L) with (LBp := LB ++ fdata LF) (SP := bv_unsigned sp) (XI := []);
          [exact ME| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP01)| exact MI| exact MI1| exact CRE| | exact I| intros _; exact I| intros b Hb; (flat constr:((mpd_blk_heap _ _ Hb)) 2%nat; intros O ->); exact (proj1 (A_mpi_client.mpd_heap_in asegs _ _ _ ME O))].
        intros O. flat constr:((A_mpi_client.mpd_heap_in asegs _ _ _ ME O)) 2%nat. intros IN N1. eapply client_range_block; [apply in_app_iff; left; exact IN| clear; lia| clear; lia].
      - eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact OE| exact CRE| clear - LOS SLO NEEDR; lia| intros x Hx; eapply hcs_below_top; exact Hx]. }
    assert (XCR : client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_addr dX) 16).
    { flat constr:(XW) 2%nat. intros CW _. intros x Hx. destruct (CW x Hx) as [K|[K|K]]; [left; exact (proj1 K)| right; left; exact K| right; right; exact K]. }
    flat constr:((TR dX MX OXs XCR)) 2%nat. intros MX1 OX1.
    assert (EXT1 : Forall (fun e => mpd_at asegs m1 LB e /\ aobj asegs AL (hcs asegs R HIA h1) m1 (md_addr e) 16) es).
    { apply Forall_forall. intros e He. flat constr:((proj1 (Forall_forall _ _) ESM e He)) 2%nat. intros ME OE.
      flat constr:((proj1 (Forall_forall _ _) ESF e He)) 4%nat. intros CRE _ ASE _.
      apply (TR e ME OE). eapply client_range_raise; [exact CRE| exact ASE]. }
    (* [comment removed for export] *)
    intros mo1 [HK1 MF1]. apply (aevtA_enter asegs (KF asegs R HIA h1 mo0) _ _ mo1 (conj (proj2 (HKI mo1) HK1) MF1)).
    assert (LOC : lo <= sp1) by (clear - SLO SP1 NEEDR; lia). assert (CSP : sp1 <= bv_unsigned sp) by (clear - SP1; lia).
    assert (FN64 : 64 <= 128) by (clear; lia). assert (FB8 : FB mod 8 = 0) by (clear - F64; Z.div_mod_to_equations; lia).
    set (dTA0 := mkMPD (FB + 32) 1 0 0 [] padA LNull). set (dTB0 := mkMPD (FB + 64) 1 0 0 [] padB LNull).
    assert (OTA : aobj asegs AL (hcs asegs R HIA h1) m1 (FB + 32) 16) by (rewrite Ehcs; frame_aobj FSHX (FB + 32) 2%nat as OBS; exact OBS).
    assert (OTB : aobj asegs AL (hcs asegs R HIA h1) m1 (FB + 64) 16) by (rewrite Ehcs; frame_aobj FSHX (FB + 64) 2%nat as OBS; exact OBS).
    assert (CST0 : A_mpi_client.cstateA asegs R HIA h LB LF m (bv_unsigned sp) lo sp1 FB 128 dX es m1 h1 LB [dTA0; dTB0] dX
                     (CSF FB sp1 w0 w1 w2 gapn (Z_to_bv 64 (FB + 74)) (Z_to_bv 64 (FB + 32)) (Z_to_bv 64 FB) (Z_to_bv 64 (FB + 64)) j96 j104 (Z_to_bv 64 FB) gb) FSHXL 0 0).
    { eapply (A_mpi_client.cs_init asegs R HIA); try eassumption.
      - rewrite Ehcs. intros x Hx. exact Hx.
      - rewrite Evol. clear. lia.
      - rewrite Efr. clear. lia.
      - eapply presA_weaken; [exact HP01| intros b Hb; eapply In_mpd_keep; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I].
      - repeat (apply Forall_cons; [unfold dTA0, dTB0; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]; unfold mpi_cells;
                  repeat (split; [first [assumption| reflexivity| clear; lia| clear - F8; Z.div_mod_to_equations; lia]|]); assumption|]). apply Forall_nil.
      - intros a b da db Ha Hb NE. destruct a as [|[|a]]; destruct b as [|[|b]]; cbn in Ha, Hb; try (destruct a; discriminate); try (destruct b; discriminate);
          try (exfalso; apply NE; reflexivity).
        all: injection Ha as <-; injection Hb as <-; unfold dTA0, dTB0; cbn [md_addr]; clear; lia.
      - unfold CSF. repeat (apply Forall_cons; [cbn [fst snd]; assumption|]). apply Forall_nil.
      - unfold CSF. repeat (apply Forall_cons; [unfold A_mpi_client.chunk_okA; cbn [fst snd cells_size csize Nat.add]|]); [left| left| left| right; left| apply Forall_nil]; clear - SP1 GAP; lia.
      - cbn [cells_size csize Nat.add]. clear. lia. }
    eapply (mm_BODY FB sp1 w0 w1 w2 gapn) with (dTA := dTA0) (dTB := dTB0); try eassumption; try reflexivity.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Call.

  Hypothesis HNDk : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis ROIMG : forall a, ro_addr asegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis ZF : zeroize_and_free_stmtA asegs R HIA A_ZEROIZE_AND_FREE.
  Hypothesis COPY : mpi_copy_stmtA_c asegs R HIA A_MPI_COPY.
  Hypothesis CMUL : mpi_core_mul_stmtA asegs R HIA A_MPI_CORE_MUL.
  Hypothesis CALLOC : arl_calloc R = A_WRAP_CALLOC_MM.
  Hypothesis AMC : arl_amemcpy R = A_ASAN_MEMCPY_MM.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_MM.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00R0?L11330378022.4 L11330378023.4 L11332112679.4 L11332227367.5 L11332276519.5 L12926298066.10L12926298066.11L13285129801.3 L23459159588.3 L23459159589.2 L23461090852.4 L23461205540.3 L31813109764.2 L32121500974.2 L32121500975.3 L3457879877.7  L3458027333.8  L3458043717.8  L3460204356.7  L3460204357.7  L38948636245.0 L47045695139.5 L47045695139.6 L54325852470.3 L54328242486.3 L54328242487.3 L66988729626.2 L66988729627.3 L66990599450.4 L66990714138.4 L66990763290.3 L774765788.5   L849490548.5   L849490548.6   00000100200300400500600700?00@00A00B00L00T00\00]00^00_00`00a00b00c00d00e00o01001101201301401501?01R01S01TFFFFFFFS2dX1e1CFFFS2dA2A02ABS2dA3NRAS2dB3NRBFFFFFFSFFS2dX2X02XBFFFFFFS2dB2B02BBS1R5NEEDR2sp2lo3SLOFF". (* [comment removed for export] *)
  Theorem A_mpi_mul_mpi_spec_s_c : mpi_mul_mpi_stmtA asegs R HIA A_MPI_MUL_MPI_E.
  Proof.
    unfold mpi_mul_mpi_stmtA. intros until d.
    intros HH HK LFB MX MA MB SXA SXB SAB NST OA OB CRA CRAL CRB CRBL XW XLS ST LOS SLO SLOS TOP SPA TPV MI RAE OXA OAA OBA IA2 IB2 BUD UW UWX BUDF C24H -> -> ->.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    flat constr:(MX) 2%nat. intros FLt10 _. flat constr:(FLt10) 6%nat. flclear FLt10. intros CX0 _ X0 _ NRX OWNX. flat constr:(MA) 2%nat. intros FLt11 _. flat constr:(FLt11) 6%nat. flclear FLt11. intros CA0 _ A0 _ NRA _. flat constr:(MB) 2%nat. intros FLt12 _. flat constr:(FLt12) 6%nat. flclear FLt12. intros CB0 _ B0 _ NRB _.
    pose proof (rw_cells_bound _ _ _ _ CX0) as XB. pose proof (rw_cells_bound _ _ _ _ CA0) as AB. pose proof (rw_cells_bound _ _ _ _ CB0) as BB.
    unfold mpi_cells in XB, AB, BB. cbn [cells_size csize Nat.add] in XB, AB, BB.
    flat constr:(XW) 2%nat. intros XCW XP.
    pose proof (client_wrange_where_A asegs R HIA h LB LF m LB (bv_unsigned sp) (md_addr dX) 16 lo HH ltac:(intros b' Hb; exact Hb) XCW ltac:(clear; lia) LOS ltac:(clear - SLO NEEDR; lia)) as XS.
    set (es := (if Z.eq_dec (md_addr dA) (md_addr dX) then [] else [dA]) ++ (if Z.eq_dec (md_addr dB) (md_addr dX) then [] else [dB])).
    assert (ESP : forall e, In e es -> (e = dA /\ md_addr dA <> md_addr dX) \/ (e = dB /\ md_addr dB <> md_addr dX)).
    { intros e He. subst es. apply in_app_iff in He. destruct He as [He|He].
      - destruct (Z.eq_dec (md_addr dA) (md_addr dX)) as [E|NE]; [destruct He| destruct He as [<-|[]]; left; split; [reflexivity| exact NE]].
      - destruct (Z.eq_dec (md_addr dB) (md_addr dX)) as [E|NE]; [destruct He| destruct He as [<-|[]]; right; split; [reflexivity| exact NE]]. }
    assert (EFACT : forall e, mpd_at asegs m LB e -> mpd_sep dX e -> opnd_sep dX e lo (bv_unsigned sp) -> client_range L (LB ++ fdata LF) lo (md_addr e) 16 -> md_addr e <> md_addr dX ->
              client_range L (LB ++ fdata LF) lo (md_addr e) 16
              /\ (md_own e = LHeap -> In (md_p e, 4 * md_n e) LB /\ 1 <= md_n e)
              /\ (md_addr e + 16 <= lo \/ bv_unsigned sp <= md_addr e)
              /\ (md_own dX = LHeap -> md_addr e + 16 <= md_p dX \/ md_p dX + 4 * md_n dX <= md_addr e)
              /\ (md_own dX <> LHeap \/ md_own e = LNull \/ md_p dX + 4 * md_n dX <= md_p e \/ md_p e + 4 * md_n e <= md_p dX)
              /\ (md_addr dX + 16 <= md_addr e \/ md_addr e + 16 <= md_addr dX)
              /\ (md_own e <> LNull -> md_addr dX + 16 <= md_p e \/ md_p e + 4 * md_n e <= md_addr dX)).
    { intros e ME SE OE CRE NE. flat constr:(OE) 5%nat. flclear OE. intros O1 O2 O3 O4 O5.
      split; [exact CRE|]. split; [intros O; exact (A_mpi_client.mpd_heap_in asegs _ _ _ ME O)|]. split; [exact O4|]. split; [exact O2|].
      split; [destruct O3 as [C|[C|[C|C]]]; [exfalso; apply NE; rewrite C; reflexivity| left; exact C| right; left; exact C| right; right; exact C]|].
      split; [destruct SE as [C|C]; [exfalso; apply NE; rewrite C; reflexivity| clear - C; lia]| exact O1]. }
    eapply (mm_MAIN h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo (md_addr dX) (md_addr dA) (md_addr dB) lo) with (dX := dX) (dA := dA) (dB := dB) (d := d) (es := es);
      try eassumption; try reflexivity.
    all: first
      [ clear - NRA; unfold MPI_MAX_LIMBS in NRA; lia | clear - NRB; unfold MPI_MAX_LIMBS in NRB; lia
      | clear - X0 XB; lia | clear - A0 AB; lia | clear - B0 BB; lia
      | exact (proj1 OXA)
      | (intros O; exact (A_mpi_client.mpd_heap_in asegs _ _ _ MX O))
      | (intros NE; subst es; apply in_app_iff; left; destruct (Z.eq_dec (md_addr dA) (md_addr dX)) as [E|_]; [exfalso; exact (NE E)| left; reflexivity])
      | (intros NE; subst es; apply in_app_iff; right; destruct (Z.eq_dec (md_addr dB) (md_addr dX)) as [E|_]; [exfalso; exact (NE E)| left; reflexivity])
      | (apply Forall_forall; intros e He; destruct (ESP e He) as [[-> NE]|[-> NE]]; [exact (EFACT dA MA SXA OA CRA NE)| exact (EFACT dB MB SXB OB CRB NE)])
      | (apply Forall_forall; intros e He; destruct (ESP e He) as [[-> NE]|[-> NE]]; [split; [exact MA| exact (proj1 OAA)]| split; [exact MB| exact (proj1 OBA)]])
      | match goal with |- ?g => idtac "THM-LEFT:" g end ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End WalkM.

Theorem A_mpi_mul_mpi_spec_c : ltac2:(CDefT.buildp (gd_tbl_A_mpi_mul_mpi_c24 ()) "PR,$75.PHIA,(76.$:.R1.)P,(77.(12.R2.))P,(>.$8.(78.R3.)$79.)P,(>.$8.(7:.R4.+1.)$7;.)P,(16.=(7<.R5.))P,(16.=(7=.R6.))P,Ph,(9.$:.R7.R6.)PLB,(35.$36.)PLF,(35.$36.)Pm,P,(;.&40.)(<.(;.&8.))P,(1:.$:.R;.R:.R4.R3.R2.R1.)(7>.$8.(7?.(1;.$8.$8.)$8.(80.$8.$8.)R4.))P,(=.(16.(81.(3?.R8.))(82.(3?.R8.)))(16.(83.(3?.R8.))(84.(3?.R8.))))P,Pa,$8.P,(>.$63.(64.$:.(65.R1.))$66.)P,(=.(16.=R2.)(62.R2.(85.+2.+40.)))(=.(16.(81.(3?.R<.))R3.)(62.R3.(84.(3?.R<.))))P,(86.$:.R:.R9.$87.)P,(88.$:.R;.R:.$89.)P,(8:.$:.R<.R;.$8;.)P,(>.$8.(8<.R=.)$8=.)P,(>.$8.(8>.R>.)$8?.)P,(>.$8.(90.R?.)$91.)(92.$:.R10.R?.$93.)")
(* [comment removed for export] *).
Proof. intros. change A_MPI_MUL_MPI with A_MPI_MUL_MPI_E. eapply A_mpi_mul_mpi_spec_s_c; eassumption. Qed.
