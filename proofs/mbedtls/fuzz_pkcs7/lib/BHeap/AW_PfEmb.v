(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_exit_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_PfLib AW_PfNum AW_PfLib2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AW_Unwind AW_MmapFixed AW_MmapDie AW_Populate.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
#[local] Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | first [tb_light_a a | lia] | first [tb_light_l a | (simpl_sizes; slia)]
                | first [ solve [cbn [inside]; tb_free] | (cbn [inside]; simpl_sizes; slia) ] ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq;
              [ | first [tb_light_a a | lia] | first [tb_light_l a | (simpl_sizes; slia)] ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00c78634fd3153b4 0 2 0 1 33 1P00c8c69faf79ca89 0 2 0 1 36 1P00d1a0e6d945832d 0 3 1 1 37 1 38 1P013103d51dd60259 0 2 0 1 36 1P0141e0fb176e8ae0 0 2 0 1 36 1P0156fbe269e90d01 0 3 0 1 25 1 27 1P0163d5e9d9efc2be 0 2 1 1 40 1P0175baec9988152a 0 3 1 1 39 1 40 1P017c67bc60d0189b 0 3 1 1 37 1 38 1P0191bfc39f88d617 0 2 0 1 33 1P01971bf17f1dccb0 0 2 0 1 33 1P0226e7ce61248cfe 0 3 0 1 39 1 40 1P02978ebce0cdfac1 0 3 1 1 39 1 40 1P02b511c3f7e6f3f2 0 3 1 1 34 1 35 1P03f08296572ed9be 0 2 1 1 40 1P04328c8d4dc47257 0 3 1 1 34 1 35 1P045fa86ce1fbfacb 0 3 1 1 37 1 38 1P046fd9e30c8c6ad7 0 2 0 1 36 1P054b27174de80372 0 3 0 1 39 1 40 1P0581ce7e0d1062ee 0 3 1 1 44 1 45 1P05862d542e3b8ed2 0 2 0 1 37 1P05cda8809ecb2b25 0 2 0 1 43 1P05daa39b62b6dbbd 0 2 0 1 36 1P05edf107a01a6de4 0 3 1 1 37 1 38 1P066658ef36c6fbaf 0 3 1 1 37 1 38 1P06c9e82def7b6679 0 3 1 1 39 1 40 1P07108fe5e3f7a7e4 0 2 1 1 40 1P0741e495f0a6255d 0 2 1 1 40 1P07b9d99134d27b58 0 2 1 1 40 1P07f558d0a7e54b5f 0 3 0 1 25 1 27 1P0813898a6656d9c6 0 2 0 1 33 1P089dd879f734a77b 0 2 0 1 38 1P08a31e764798c550 0 3 1 1 37 1 38 1P08c5de01b1407852 0 2 0 1 33 1P08d2c388ae864459 0 2 0 1 36 1P08f10eaee10d2e60 0 3 1 1 39 1 40 1P0927c251f25d5eb0 0 3 1 1 37 1 38 1P094105fa5ebfaa95 0 2 0 1 37 1P09d2e04c77e3e7cf 0 3 1 1 44 1 45 1P09d7024ad3cd84e8 0 2 0 1 36 1P09fbc56339614013 0 3 1 1 34 1 35 1P0a14523f0bbab50a 0 2 0 1 33 1P0aa06a33cba2eac4 0 3 1 1 44 1 45 1P0af32dad0490e775 0 2 1 1 51 1P0b42d51cb5ca4895 0 2 0 1 37 1P0baf8e19f1b01f19 0 2 0 1 28 1P0bb19d3218e2518c 0 2 0 1 43 1P0c5f084bf19c7681 0 3 1 1 39 1 40 1P0ca0719adf18e00d 0 3 1 1 44 1 45 1P0da62e745c5c8355 0 3 1 1 39 1 40 1P0db76c86d687ffc0 0 3 1 1 34 1 35 1P0dc8af5f309c7823 0 2 0 1 36 1P0dff4d8a58f7a916 0 3 1 1 37 1 38 1P0e48834381377714 0 5 1 1 23 1 25 1 26 1 28 1P0e5fbb6f27cc6677 0 2 1 1 40 1P0e6a671909a8263e 0 2 0 1 36 1P0e8cf44c49d073b0 0 2 0 1 38 1P0e8e0c07c7825613 0 2 0 1 43 1P0e9983559efef05d 0 2 0 1 43 1P0eba2d7280161f31 0 2 0 1 37 1P0ec9af778d885cb5 0 2 0 1 36 1P0ed2c63cd2f9d9cb 0 3 1 1 34 1 35 1P0ee9dbdab89d389d 0 2 0 1 36 1P0f51f6aa19c992ae 0 2 0 1 37 1P0f79d82f932877e6 0 3 1 1 39 1 40 1P0f8a0248e9017d02 0 2 0 1 43 1P0f945faeefdf8a3b 0 2 0 1 33 1P0ff029c7c5712667 0 3 0 1 44 1 45 1P10004495f908e81d 0 2 0 1 36 1P1028d79174e90fd6 0 3 1 1 37 1 38 1P104c03cf195cded3 0 2 0 1 37 1P104f231afdfa563a 0 2 0 1 36 1P1071875ab46e00b7 0 2 0 1 38 1P1080c345a68e7393 0 2 0 1 33 1P10d370a4e591b4d6 0 3 1 1 37 1 38 1P1110c7e6ccdb3c79 0 3 0 1 44 1 45 1P1131294a5d5d2c34 0 3 1 1 44 1 45 1P11a436faf4a5e1ab 0 2 0 1 43 1P11daff799f5ba0ca 0 2 0 1 36 1P11e9bcc7f28cfd5e 0 3 1 1 37 1 38 1P1221fb7e6488b700 0 2 0 1 37 1P1229e9b2aa758482 0 3 1 1 39 1 40 1P124465bcfe14caba 0 3 0 1 44 1 45 1P12b28d3483ed77e6 0 2 0 1 33 1P12cd58a726825b80 0 2 0 1 36 1P13c036732cf8f39e 0 3 1 1 37 1 38 1P13d14c89a5cac967 0 3 1 1 39 1 40 1P140f8a85011f57fe 0 2 0 1 33 1P14c1422899440a5a 0 3 1 1 44 1 45 1P14c9cb41241ccb1b 0 2 1 1 51 1P14d635a793e8be5d 0 3 1 1 44 1 45 1P14f50b57a4665ae6 0 3 1 1 37 1 38 1P15670414c7a608a0 0 3 1 1 37 1 38 1P15721e2362ab2632 0 3 1 1 34 1 35 1P15a9db3ef7071992 0 3 1 1 44 1 45 1P15fb174283c785e3 0 2 0 1 36 1P16150368187a483d 0 2 0 1 37 1P1644cc457b3a461f 0 3 1 1 37 1 38 1P164fc58133c6af5f 0 3 1 1 39 1 40 1P16aaf9fc961ed21c 0 3 1 1 44 1 45 1P16bd95fa51363211 0 2 0 1 33 1P16e710d0de4045fd 0 2 0 1 38 1P171d6180fff42f00 0 2 1 1 51 1P17e5ad36f80b5b9d 0 3 1 1 37 1 38 1P1802c763b7221c87 0 3 1 1 39 1 40 1P181af200d4df960a 0 3 1 1 34 1 35 1P183f5791eaab85b2 0 2 0 1 33 1P184f3834876f6070 0 3 0 1 26 1 28 1P18c978722113e04c 0 3 1 1 34 1 35 1P18dd39ad0f1580f6 0 3 1 1 37 1 38 1P18f58855f0af5eb1 0 3 1 1 37 1 38 1P19a0164b78ff2da4 0 3 0 1 39 1 40 1P19dd8c528067b862 0 2 0 1 38 1P1a0411e15f06aac0 0 3 1 1 37 1 38 1P1a3907de0f9b2aac 0 3 1 1 37 1 38 1P1a6ae5a2df28fb9c 0 2 0 1 38 1P1a91b2ca1e311e43 0 3 1 1 37 1 38 1P1aa8bddfbd74947b 0 3 1 1 44 1 45 1P1af95b72d80aa729 0 2 0 1 33 1P1b19996aa532c0d2 0 3 1 1 37 1 38 1P1b5dc4a23ac0e6bc 0 2 1 1 51 1P1b71a208c5e9610b 0 3 1 1 39 1 40 1P1bcd43dc2fe3995c 0 3 1 1 37 1 38 1P1c7fe24e841910c0 0 2 0 1 37 1P1c9133fc041d53c0 0 3 1 1 37 1 38 1P1ca96bc2b8dc6c9e 0 3 1 1 39 1 40 1P1caf00c8135172dd 0 2 0 1 36 1P1cbe7469f6b35da0 0 2 0 1 33 1P1d527e8d56fdb1d3 0 3 1 1 34 1 35 1P1d81a910f853432a 0 3 1 1 37 1 38 1P1d9b1dfed9276aef 0 3 1 1 39 1 40 1P1e1d410030f599d5 0 2 0 1 36 1P1e4b2632d5b03f03 0 3 1 1 37 1 38 1P1e632bc5c5c88d48 0 3 1 1 39 1 40 1P1ebd8a812063a13b 0 2 0 1 38 1P1ee3a1805ca8ee7c 0 2 0 1 33 1P1f0915b385907cd1 0 3 1 1 37 1 38 1P1fdb4e90ae2cfec2 0 2 0 1 33 1P1fea24996b3d7282 0 2 0 1 36 1P2079aceb2f9dc68a 0 3 1 1 39 1 40 1P2088c95fcf22ad3a 0 2 0 1 43 1P20f61dae5d0b53a2 0 3 1 1 37 1 38 1P218b1cc1ffd31182 0 2 0 1 33 1P21f3bc5f05916ad4 0 3 1 1 37 1 38 1P2210057a3e908db9 0 2 0 1 36 1P224376cfec6d6ea7 0 3 1 1 37 1 38 1P22a2f4e9b6fbfe49 0 3 1 1 34 1 35 1P22a81193fe7b7532 0 2 0 1 37 1P22bb9b30f4039031 0 3 1 1 37 1 38 1P2346a1ad6aad98cb 0 2 0 1 33 1P2376e3b88dab33af 0 2 0 1 33 1P23e4a4f20e2a7186 0 3 1 1 34 1 35 1P247ea875afbb1e13 0 3 1 1 44 1 45 1P248dee8be024c44f 0 3 1 1 37 1 38 1P248feddf9df41a7d 0 2 0 1 26 1P24cb0ad06f164487 0 2 1 1 40 1P24e6550d58f108cb 0 3 1 1 37 1 38 1P24f0a806ebb34ab7 0 2 0 1 43 1P24fe9e9cc9acefc3 0 3 1 1 37 1 38 1P25012bf569e3c3cf 0 3 1 1 44 1 45 1P252e93be555e45af 0 2 0 1 33 1P2533eddb7dedfa91 0 3 1 1 37 1 38 1P2548bd210f9233d3 0 2 0 1 43 1P2625d61a7038eba9 0 3 1 1 37 1 38 1P268149870231d2d2 0 3 1 1 34 1 35 1P2688af78ece918db 0 2 1 1 40 1P2691f937b82d9ffb 0 3 1 1 34 1 35 1P269b3c84605321f2 0 2 0 1 36 1P271f07c9bdce4120 0 3 0 1 44 1 45 1P27426b396251f3ef 0 3 1 1 44 1 45 1P27a87eb131eac1f1 0 3 1 1 44 1 45 1P289ee607d6168d7c 0 2 0 1 36 1P296beb08bb2bbd34 0 3 1 1 37 1 38 1P298baecd02b9c6f6 0 2 0 1 33 1P2a14f1a8c861e881 0 3 1 1 44 1 45 1P2b03a033c6c5533c 0 3 1 1 37 1 38 1P2b3f588ae8dd7953 0 3 1 1 37 1 38 1P2b46048a2d3afb4e 0 2 0 1 33 1P2b8d32a8614e985e 0 3 1 1 37 1 38 1P2bd61964cf6d30bc 0 3 1 1 37 1 38 1P2c3ac5e60e7de8cd 0 2 0 1 33 1P2c82527cd63f1ad8 0 3 0 1 39 1 40 1P2c8fe828c9bfeed0 0 3 1 1 39 1 40 1P2c901f176e9dd380 0 2 0 1 33 1P2ccd8ccb842a4057 0 3 1 1 34 1 35 1P2cdbc908fc49c20d 0 3 1 1 44 1 45 1P2d1fad87b464d7f6 0 2 0 1 36 1P2d30a4a6bdd0e992 0 3 1 1 37 1 38 1P2d31be252e6187a1 0 2 0 1 43 1P2d4cfdac972566a0 0 3 1 1 37 1 38 1P2d9fbb74293caa4e 0 3 1 1 37 1 38 1P2dee2f566fcb9608 0 5 1 1 45 1 47 1 49 1 51 1P2e0b151be9198beb 0 2 0 1 33 1P2e0d8ce114c8108f 0 2 0 1 37 1P2e71cb878e1255e2 0 3 1 1 37 1 38 1P2ea7db3068b6845b 0 3 1 1 34 1 35 1P2eb088a2b95c73a5 0 3 1 1 37 1 38 1P2ed19a61e2bea1cc 0 3 1 1 37 1 38 1P2ee720692af4af23 0 3 1 1 34 1 35 1P2f95491f27047fb8 0 3 1 1 34 1 35 1P2fb7fbe7caad5570 0 2 0 1 43 1P2fc9a07ec0265294 0 3 1 1 37 1 38 1P2fd96184ff5074b5 0 2 0 1 36 1P2ffa8c2eecf69531 0 2 0 1 43 1P301c4d79a32838bd 0 2 0 1 36 1P30279e6f60cd6c80 0 3 1 1 37 1 38 1P307dd38fb781250d 0 2 0 1 38 1P309d62d5764c79c1 0 3 1 1 39 1 40 1P30ecf2c98b9a2922 0 3 1 1 37 1 38 1P319bb1a7ca151cfd 0 3 1 1 34 1 35 1P31c1141cae371597 0 2 0 1 33 1P31c9c3711fbf35de 0 3 1 1 44 1 45 1P31d10de6b8ca9779 0 3 1 1 34 1 35 1P31d94ac8583babb2 0 2 0 1 33 1P323040d7611578f3 0 2 0 1 33 1P326f8867845f7694 0 3 1 1 39 1 40 1P327eeceb82bce49a 0 2 0 1 36 1P32ae1379d523e2de 0 3 1 1 34 1 35 1P32afca0984626592 0 2 0 1 43 1P32db06198438e40e 0 3 1 1 39 1 40 1P3338d4243078f613 0 3 1 1 37 1 38 1P33eca1bf6106f9e6 0 3 1 1 37 1 38 1P347aaf7f367dc55e 0 2 0 1 33 1P34852665ea18b58e 0 3 1 1 39 1 40 1P349c4f3c25cf7e1b 0 2 0 1 38 1P35085e54c4362040 0 2 0 1 43 1P357165152095dcfd 0 2 0 1 33 1P35c7c6faaeaf050b 0 3 1 1 39 1 40 1P361d55304bd825b9 0 3 1 1 37 1 38 1P3647a0999a53018e 0 2 0 1 36 1P3658292632eff3de 0 3 1 1 34 1 35 1P3676888019fcae53 0 2 0 1 36 1P372a6b9713c60d02 0 3 0 1 22 1 23 1P37458e8010dd669e 0 2 0 1 36 1P37b2fd5063c836c8 0 3 1 1 37 1 38 1P38268dfa1408ab30 0 2 0 1 27 1P386191d4c539d7c7 0 2 0 1 38 1P38e1163bc4cb5fe0 0 3 1 1 39 1 40 1P3913aa471322b48d 0 3 1 1 37 1 38 1P39841a4cf22a0c1c 0 2 0 1 36 1P39a0f5e243e44310 0 3 1 1 34 1 35 1P39ad3ba62cec8fc9 0 2 1 1 40 1P39c65246557576c8 0 5 1 1 45 1 47 1 49 1 51 1P39edcf255b452189 0 2 0 1 36 1P3a26780ce186e07c 0 3 1 1 37 1 38 1P3a286eabd0934ca2 0 2 0 1 37 1P3a4cb2270b06b614 0 3 1 1 44 1 45 1P3a8dba6066a260b9 0 2 0 1 36 1P3ac38a4984142fb5 0 2 0 1 36 1P3b94fd067dc8f6b1 0 2 0 1 43 1P3bd964a7116e1578 0 2 0 1 43 1P3c1634c968467c77 0 3 1 1 37 1 38 1P3ca6a139fd850752 0 3 1 1 39 1 40 1P3cd85de68d0abb53 0 2 0 1 33 1P3cdec8547208ed32 0 3 1 1 37 1 38 1P3cf6ce390bc01f3a 0 2 0 1 38 1P3d6885166ae4fbc1 0 3 1 1 34 1 35 1P3da1fa71490fd173 0 2 0 1 33 1P3df0968fbd5683e2 0 3 1 1 37 1 38 1P3e480410dd08a6c4 0 2 1 1 40 1P3e4ece40eb6e05a1 0 3 1 1 34 1 35 1P3e711708c080e528 0 2 1 1 40 1P3e77afa5be9a60bd 0 2 0 1 38 1P3f820e03c8c0f488 0 2 0 1 33 1N0677b5de1ed6fd05N07b354a57aa87509N0eef795027752945N1c8ab710d4490eeeN23bcde18c4a87d28N247e78bbf0e1d6eaN2e26b5e4956d3381N3ed3a6894cc825fd"%lxh.
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
Ltac2 gd_tbl_AW_PfEmb () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_EMB"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kEmbBytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.Emb.emb_cb_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MSsvc"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_ECALL"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DECORATE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "ARUN_1.Emb.emb_first_svc_post"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_LIMIT"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.md_answered"].

Section ARUN_1. Context {hAR : arun}.

Section Emb.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition emb_cb_post (ra : word) (SPc : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (W : list (Z * Z)) (lo d sz' : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_PfEmb ()) "Lms',$0.(1.(2.&40.)Lt0',(2.&40.)(1.(2.&40.)Lt1',(2.&40.)(1.(2.&40.)Lt2',(2.&40.)(1.(2.&40.)La0',(2.&40.)(1.(2.&40.)La1',(2.&40.)(1.(2.&40.)La2',(2.&40.)(1.(2.&40.)La3',(2.&40.)(1.(2.&40.)La4',(2.&40.)(1.(2.&40.)La5',(2.&40.)(1.(2.&40.)La6',(2.&40.)(1.(2.&40.)La7',(2.&40.)(1.(2.&40.)Lt3',(2.&40.)(1.(2.&40.)Lt4',(2.&40.)(1.(2.&40.)Lt5',(2.&40.)(1.(2.&40.)Lt6',(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R11.(6.(7.O17.(8.&40.O16.)O15.O14.R10.R?.R>.O13.O12.R=.R<.R;.R:.R9.R8.R7.R6.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R5.R4.R3.R2.)O7.(9.O17.)O6.(:.(2.&40.))R1.(;.$<.)))(4.(=.$<.R1.$>.(?.$10.(11.(8.&40.(12.$>.+20.)))(13.$10.)))(4.(=.$<.R1.(12.$>.+10.)(?.$10.(11.(8.&40.=))(13.$10.)))(4.(=.$<.R1.(12.$>.+20.)(?.$10.(11.(8.&40.O3.))(?.$10.(11.(8.&40.$14.))(?.$10.(11.(8.&40.O2.))(13.$10.)))))(4.(15.$<.R1.O3.$14.)(4.(16.$<.R1.O4.O16.)(4.(17.O5.O1.R1.)(4.(18.$<.O1.R1.)(19.$<.R1.)))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01F0?L10704731530.13L10704731530.16L10762970737.88L13594639780.90L14372174060.90L14391451539.6 L14393617315.6 L14776158036.6 L16710716938.75L16725820075.15L20205877484.90L24491750542.6 L24845740268.90L29397351534.16L33415184485.3 L35699775234.7 L3603427538.4  L36062169889.0 L38429153490.4 L43174654446.5 L43607788425.12L43607788425.15L44158274770.4 L4551813440.2  L46095719840.4 L46097885457.4 L46097886235.12L46097886235.15L48134333217.0 L49810120657.15L53223706740.15L5547431435.12 L5547431435.15 L55716686549.0 L5764754358.7  L5764754358.8  L59723276104.90L62420670842.5 L64038912520.89L66004556044.0 L66969711777.0 L67565208580.3 N15464071796.83N15464071796.87N42897359755.83N42897359755.87O15794444523.85O15794444524.81O34964186107.85O34964186108.81O36694325450.81O36694325453.85O60325165051.85O60325165052.81O63839502331.85O63839502332.81O66128731130.81O66128731133.85P24492253906.81P24492253909.85P3603932809.85 P3603932814.81 P38428610185.85P38428610190.81P43174111154.81P43174111157.85P44157737609.85P44157737614.81P62420127521.85P62420127526.81Q16462473515.87Q17282617483.87Q17926394621.74Q20891169579.87Q22216797879.87Q2601842492.87 Q4033576620.87 Q42484149080.74Q45406616736.74Q53534663706.74Q53534892422.87Q60087523095.74Q64151389367.74Q68415761604.87Q7769115319.74 Q9395981665.87 00000100200<00c01901K01]01o02O02k03A03B03X03Y03a03m03n03o04004104S05905:05@05M05Z05j06:06;06E06k07107707807L07M08<08=08M08N08O08Y09009G09[09o0:00:10:20:30:40:50:60:70:80:90::0:;0:Y0;70;K0;_0<30<G0=10=[0=o0>C0>e0?G0?N0?O0?Z0?i0@00@10@80@90@:0@F0@V0@W0@b0@c0@f0A5FFS1s3len2HBS1s3SPc2lo3len5LOIMG3SPL2HB5Ha_st5Hl_stS1s3len2HB5Ha_st5Hl_stS1s1d2sz2SL2W23SZBS1s1d2sz2SL3SZB2W2S1s2sz2SL3SZB1i2HiS1s3MSG3SPc2lo3len3SPM5LOIMG3SPLS1s3MSG3SPc2lo3SPM5LOIMG3SPLS1s3len2HB5Ha_st5Hl_stFS1s3len2HB5Ha_st5Hl_stFS1d2sz1iS1s3MSG1x2HxFSFFS1s3SPc2lo1d2sz2SL3DHI3SZB3SPL3SPHS1s3MSG3SPc2lo1d2sz3SPM2MH3DHI3SZB3SPLFS1d2szS1d2sz3SZB2W1S1d2sz2W13SZBS1s1d2sz3DLO3SZBS1s1d2sz3DLO3SZBSS1s3MSG2MHS1s3MSG3SPc2lo1d2sz2SL3SPM3DHI3SZB3SPLS1s2SLS1s2SLSS1s1d2sz2SL3SZB1x2HxFS1s3MSG3SPc2lo3len3SPM5LOIMG3SPL2HB5Ha_st5Hl_stFS1s3len2HB5Ha_stSSS1s2sz3lenS1s1d2sz3len2SL3SZB1x1CS1s1d2sz3len2SL3SZB1x1CS1s1d2sz3len3SZB1x1CS1s1d2sz3len3SZB1x1CFFFFFFFFFFFFS1s3SPc2lo1d2sz3len2SL3DHI3SZBS1s3SPc2lo1d2sz3len2SL3DHI3SZBS1s1d2sz3len3DLO3SZBS1s1d2sz3len3DLO3SZBS1s1d2sz3len3DLO3SZBS1s1d2sz3len3DLO3SZBS1s3MSG3SPc2lo1d2sz3len2SL3SPM3DHI3SZB3SPLS1s3MSG3SPc2lo1d2sz3len2SL3SPM3DHI3SZB3SPLS1s1d2sz3len3DLO3SZBS1s1d2sz3len3DLO3SZBS1s3SPc2lo1d2sz3len2SL3DHI3SZB3SPLS1s3SPc2lo1d2sz3len2SL3DHI3SZB3SPLS1s3lenFS2AL1s4IMG'S2AL1s3len4IMG'S1s3lenFS1s3lenFFS2AL1s5ALWF'S2AL1s3len5ALWF'FS2AL1s4IMG'FS1sS2AL1s3len4IMG'". (* [comment removed for export] *)
  Lemma emb_cb_tail : ltac2:(CDefT.buildp (gd_tbl_AW_PfEmb ()) "Ps,(1:.(2.&8.))PMSG,$1;.PSPc,$1;.Plo,$1;.Pd,$1;.Psz,$1;.Pj8,(1:.(2.&8.))Pra,(2.&40.)Pra',(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pm,P,(2.&40.)(3.(2.&8.))P,(1=.$<.R1.R29.(1>.(2.&8.)R2:.(?.(2.&8.)(8.&8.=)(13.(2.&8.)))))P,(1?.(20.(2.&8.)(8.&8.=)R2;.))P,(4.(21.+1.(22.(23.(2.&8.)R2<.)))(21.(22.(23.(2.&8.)R2<.))+190.))P,(24.VCS,R2<.(12.(22.(23.(2.&8.)R2=.))+1.))P,(21.R2<.R2=.)P,(25.(12.(12.R2>.(22.(23.(2.&8.)R2?.)))+1.)(26.+2.+3?.))P,(=.$<.R7.$>.(?.$10.(11.(8.&40.(12.$>.+20.)))(13.$10.)))P,(=.$<.R8.(12.$>.+10.)(?.$10.(11.(8.&40.+1000000000000000.))(13.$10.)))P,(=.$<.R9.(12.$>.+20.)(?.$10.(11.(8.&40.R2>.))(?.$10.(11.(8.&40.$14.))(?.$10.(11.(8.&40.R2=.))(13.$10.)))))P,(15.$<.R:.R2?.$14.)P,(24.VCS,R30.$14.)P,(21.+65?000.R31.)P,(21.(12.R32.$14.)R33.)P,(4.(21.=R32.)(21.R32.(12.(27.+3>.+80.)+80.)))P,(=.$<.R?.(12.R36.-60.)(?.$10.(28.#8.R32.)(?.$10.(11.R21.)(?.$10.(11.R22.)(?.$10.(11.R23.)(?.$10.(11.R24.)(?.$10.(11.R25.)(?.$10.(11.R26.)(?.$10.(11.R27.)(?.$10.(11.R28.)(?.$10.(11.R29.)(?.$10.(11.R2:.)(?.$10.(11.R31.)(13.$10.))))))))))))))P,(16.$<.R10.R36.(12.R37.-60.))P,(21.+65?000.R37.)P,(21.R38.(29.R39.+60.))P,(21.R3:.(26.+2.+3?.))P,(24.VCS,R3:.(29.R3;.R3:.))P,(17.(?.(2:.$1;.$1;.)(2;.$1;.$1;.R3;.R3<.)(?.(2:.$1;.$1;.)(2;.$1;.$1;.$>.(12.$>.+38.))(?.(2:.$1;.$1;.)(2;.$1;.$1;.R3:.(12.R3:.$14.))(13.(2:.$1;.$1;.)))))R16.R15.)P,(18.$<.R17.R16.)P,(19.$<.R17.)(2<.$<.VAL,VCS,(2=.R3:.R3?.R38.R37.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R1;.R1:.(?.(2:.$1;.$1;.)(2;.$1;.$1;.R3>.R3?.)(?.(2:.$1;.$1;.)(2;.$1;.$1;.$>.(12.$>.+38.))(?.(2:.$1;.$1;.)(2;.$1;.$1;.R3=.(12.R3=.$14.))(13.(2:.$1;.$1;.)))))R3>.R3=.(12.(22.(23.(2.&8.)R41.))R3<.)R19.)(6.(7.R39.(8.&40.(12.R3?.-60.))R38.R37.R36.R35.R34.(8.&40.+109280.)(8.&40.R40.)R27.R26.R25.R24.R23.R22.R21.R20.(8.&40.+109288.)(8.&40.+10000000000.)(8.&40.+109268.)(8.&40.+2000000000000000.)(8.&40.+109278.)(8.&40.+1000000000000000.)(8.&40.+10000000000?????.)(8.&40.+=???????????????.)R29.R28.R1?.R1>.R1=.R1<.)R1;.(8.&40.+6;:7<.)R1:.(:.(2.&40.))R18.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros BY NZ SL CRM SPM MH EP EMX EV WRB CRD DLO DHI SZB FR ST LOIMG SPL SPH SCS MU WM MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold emb_cb_post, A_EMB, kEmbBytes in *.
    change (1086056 + 16) with 1086072 in *. change (1086056 + 32) with 1086088 in *. change (1086056 + 56) with 1086112 in *.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    set (len := Z.of_nat (length s)) in *.
    eapply (evtA_cut asegs AL CS).
    { eapply (istrlen_spec AL IMG ALWF CS CSOK s MSG); try eassumption; try reflexivity; try (fold len; lia). }
    cbn beta. intros ms' (a1s & a2s & ->). fold len.
    ret_lit.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, SPc); (1086056, 1086112); (d, d + 65536)] m) as MU1. pose proof (wmono_refl asegs m) as WM1.
    lx_run (PLAN [0x7aa58] [] 30%N). subst lxm. try clear LXlen.
    repeat match goal with H : munch _ m m |- _ => clear H | H : wmono _ m m |- _ => clear H end. lx_dedup.
    (* [comment removed for export] *)
    replace (sz + d) with (d + sz) by (clear; lia).
    assert (WRS : wr_at asegs m (d + sz) len).
    { destruct WRB as (W1 & W2 & W3). split; [clear -W1 SZB; lia|]. split; [subst len; clear -W2 SZB SL; lia|].
      intros i Hi. replace (d + sz + i) with (d + (sz + i)) by (clear; lia). apply W3. subst len; clear -Hi SZB SL; lia. }
    eapply (evtA_cut asegs AL CS).
    { eapply (imsetw_spec AL IMG ALWF CS CSOK) with (P := d + sz) (n := len) (b := Z_to_bv 8 0);
        first [ exact WRS | assumption | reflexivity | subst len; clear -SL SZB DLO DHI SPL SPH LOIMG; lia | intros x Hx; apply CRD; subst len; clear -Hx SL SZB; lia ]. }
    cbn beta. intros ms' (a1m & a3m & m2 & -> & MUc & WMc & MI2 & ZB).
    clear WRS ZB. lx_acc_call m0 MUc WMc. ret_lit.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, SPc); (1086056, 1086112); (d, d + 65536)] m2) as MU2. pose proof (wmono_refl asegs m2) as WM2.
    lx_run (PLAN [0x7a9dc] [] 30%N). try clear LXlen.
    lazymatch goal with WMl : wmono _ m2 ?mx |- _ => pose proof (wr_at_transport _ _ _ _ _ WRB WMl) as WRB'; clear WRB; rename WRB' into WRB end.
    lx_acc_run m0 m2. lx_clear_mem m2.
    (* [comment removed for export] *)
    assert (WRS : wr_at asegs lxm (d + sz) len).
    { destruct WRB as (W1 & W2 & W3). split; [clear -W1 SZB; lia|]. split; [subst len; clear -W2 SZB SL; lia|].
      intros i Hi. replace (d + sz + i) with (d + (sz + i)) by (clear; lia). apply W3. subst len; clear -Hi SZB SL; lia. }
    lazymatch goal with BYl : bytes_at _ lxm MSG _ |- _ => pose proof (proj1 (proj1 (bytes_at_app asegs lxm MSG s [Z_to_bv 8 0]) BYl)) as BYS end.
    eapply (evtA_cut asegs AL CS).
    { eapply (imcpy_spec AL IMG ALWF CS CSOK len (d + sz) MSG s);
        first [ exact BYS | exact WRS | assumption | reflexivity
              | subst len; clear -SL SZB DLO DHI SPL SPH LOIMG SPM MH; lia
              | intros x Hx; apply CRD; subst len; clear -Hx SL SZB; lia
              | intros x Hx; apply CRM; subst len; clear -Hx SL SZB; lia ]. }
    cbn beta. intros ms' (a1c & a2c & a3c & a4c & m3 & -> & MUc & WMc & MI3 & BYS3 & WRS3).
    clear WRS BYS BYS3 WRS3. lx_acc_call m0 MUc WMc. ret_lit.
    (* [comment removed for export] *)
    assert (KMC : ro_cells asegs m3 66568 [C8 (Z_to_bv 64 12682135451164737535)]).
    { split; [cbn; repeat split; exact I|]. apply ro_bytes_at; [exact MI3| clear; lia| cbn; clear; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. }
    pose proof (munch_refl [(lo, SPc); (1086056, 1086112); (d, d + 65536)] m3) as MU3. pose proof (wmono_refl asegs m3) as WM3.
    lx_run (PLAN [0x6bb20] [] 40%N). try clear LXlen.
    subst lxm. lx_dedup.
    (* [comment removed for export] *)
    pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof WRB as WRB3. lx_hide WRB3.
    zstep. zstep. zstep. zstep.
    lx_fold_mkR.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 30%N). try clear LXlen.
    clear WRB. lx_unhide1 WRB3.
    lazymatch goal with WMl : wmono _ m3 ?mx |- _ => pose proof (wr_at_transport _ _ _ _ _ WRB3 WMl) as WRB; clear WRB3 end.
    lx_acc_run m0 m3. lx_unhide.
    lazymatch goal with EVl : rw_cells _ ?mx 1086088 _ |- _ => replace (sz + len) with (len + sz) in EVl by (clear; lia) end.
    lx_clear_mem m.
    lazymatch goal with MUf : munch _ m0 ?mx, WMf : wmono _ m0 ?mx' |- _ =>
      apply evtA_done; lx_exs; lx_ands; [ lx_mseq | assumption | assumption | assumption | exact WRB | assumption | exact MUf | exact WMf | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0?L10762970737.72L11517020883.1 L14372174060.74L20205877484.74L3192510483.73 L44662488140.54L48699411601.1 L59723276104.74L64038912520.73L67899323172.74Q16472957212.71Q17297299644.71Q18376990764.71Q20901657372.71Q21179125699.71Q22227281536.71Q2616524555.71 Q30894074982.71Q37951375404.71Q4035671707.71 Q49839969339.71Q53520214449.71Q53522094465.71Q64520892812.71Q68401079539.71Q9410659670.71 00000600;00M00_00f01401901d02002S02V02W02b02m02n03103203=03@03C03D03P03\03]03^03iS1s2HBS3SPcS1s2HB5Ha_st5Hl_stS1s2HB5Ha_st5Hl_stS1s3SPcS1s3SPc2lo3SPLS3SPcS1s3MSG3SPc2lo3SPM5LOIMG3SPL2HB5Ha_st5Hl_stS1s2HB5Ha_stS1s3SPc2lo5LOIMG3SPL2HB5Ha_st5Hl_stS1sFS2AL1s4IMG'S2AL1s4IMG'FS1sFS2AL1s4IMG'S1sS1sFS2AL1s5ALWF'S2AL1s5ALWF'FFS2AL1s4IMG'". (* [comment removed for export] *)
  Theorem emb_cb_present : ltac2:(CDefT.buildp (gd_tbl_AW_PfEmb ()) "Ps,(1:.(2.&8.))PMSG,$1;.PSPc,$1;.Plo,$1;.Pd,$1;.Psz,$1;.Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))P,(1=.$<.R1.R25.(1>.(2.&8.)R26.(?.(2.&8.)(8.&8.=)(13.(2.&8.)))))P,(1?.(20.(2.&8.)(8.&8.=)R27.))P,(4.(21.+1.(22.(23.(2.&8.)R28.)))(21.(22.(23.(2.&8.)R28.))+190.))P,(24.VCS,R28.(12.(22.(23.(2.&8.)R29.))+1.))P,(21.R28.R29.)P,(25.(12.(12.R2:.(22.(23.(2.&8.)R2;.)))+1.)(26.+2.+3?.))P,(=.$<.R7.$>.(?.$10.(11.(8.&40.(12.$>.+20.)))(13.$10.)))P,(=.$<.R8.(12.$>.+10.)(?.$10.(11.(8.&40.=))(13.$10.)))P,(=.$<.R9.(12.$>.+20.)(?.$10.(11.(8.&40.R2:.))(?.$10.(11.(8.&40.$14.))(?.$10.(11.(8.&40.R29.))(13.$10.)))))P,(15.$<.R:.R2;.$14.)P,(24.VCS,R2<.$14.)P,(21.+65?000.R2=.)P,(21.(12.R2>.$14.)R2?.)P,(4.(21.=R2>.)(21.R2>.(12.(27.+3>.+80.)+80.)))P,(16.$<.R?.R31.R32.)P,(21.+65?000.R32.)P,(21.R33.(29.R34.+60.))P,(21.R35.(26.+2.+3?.))P,(24.VCS,R35.(29.R36.R35.))P,(19.$<.R14.)(2<.$<.VAL,VCS,(2=.R34.R38.R33.R32.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R17.R16.(?.(2:.$1;.$1;.)(2;.$1;.$1;.R37.R38.)(?.(2:.$1;.$1;.)(2;.$1;.$1;.$>.(12.$>.+38.))(?.(2:.$1;.$1;.)(2;.$1;.$1;.R36.(12.R36.$14.))(13.(2:.$1;.$1;.)))))R37.R36.(12.(22.(23.(2.&8.)R3:.))R35.)R15.)(6.(7.R34.(8.&40.R38.)R33.R32.R31.R30.R2?.R2>.R2=.(8.&40.R39.)R22.R21.R20.R1?.R1>.R1=.R1<.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1;.R1:.R19.R18.)R17.(8.&40.+6;948.)R16.(:.(2.&40.))R15.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros BY NZ SL CRM SPM MH EP EMX EV WRB CRD DLO DHI SZB ST LOIMG SPL SPH SCS MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold A_EMB, kEmbBytes in *.
    pose proof (munch_refl [(lo, SPc); (0x109268, 0x109268 + 56); (d, d + 0x10000)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    change (1086056 + 16) with 1086072 in *. change (1086056 + 32) with 1086088 in *. change (1086056 + 56) with 1086112 in *.
    (* [comment removed for export] *)
    lx_run (PLAN [0x6b9d0] [] 60%N). try clear LXlen.
    (* [comment removed for export] *)
    try (pose proof ALWF as ALWF'; unfold al_wf in ALWF'). try (pose proof IMG as IMG'; unfold asan_img_ok in IMG').
    lazymatch goal with WMl : wmono _ m ?mx |- _ => pose proof (wr_at_transport _ _ _ _ _ WRB WMl) as WRB'; clear WRB; rename WRB' into WRB end.
    clear EP EMX EV ST MI BY.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lx_fold_mkR.
    (* [comment removed for export] *)
    lx_junk_under lo (SPc + -88) 8%nat j8 FR.
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m ?mx', STl : stk _ _ lo (SPc + -96), BYl : bytes_at _ _ MSG _ |- _ =>
      eapply (emb_cb_tail s MSG SPc lo d sz j8 ra) with (m0 := m);
      first [ exact BYl | exact FR | exact STl | exact MUl | exact WMl | exact WRB | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition emb_first_svc_post (ra : word) (SPc : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (MSG lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_PfEmb ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(1.(1:.(2.&8.))Lfr,(1:.(2.&8.))(1.(1:.(2.&8.))Lj8,(1:.(2.&8.))(4.(5.$0.R<.(2>.(7.(8.&40.+7<9;8.)(8.&40.(12.O14.-;0.))O13.O12.R;.R:.R9.(8.&40.+1.)(8.&40.+221:5.)(8.&40.=)(8.&40.(27.(2?.(12.+10000.+???.)+1000.)+1000.))(8.&40.+3.)(8.&40.+22.)(8.&40.-1.)(8.&40.=)R4.(8.&40.+=>.)(8.&40.(27.(2?.(12.+10000.+???.)+1000.)+1000.))(8.&40.$30.)(8.&40.+109268.)(8.&40.+2000000000000000.)(8.&40.+109278.)(8.&40.+1000000000000000.)(8.&40.+10000000000?????.)(8.&40.+=???????????????.)O7.O6.R8.R7.R6.R5.)O5.(8.&40.$31.)(8.&40.+=>.)O4.(:.(2.&40.))R3.(;.$<.)))(4.(17.(?.(2:.$1;.$1;.)(2;.$1;.$1;.O2.O14.)(?.(2:.$1;.$1;.)(2;.$1;.$1;.$>.(12.$>.+38.))(13.(2:.$1;.$1;.))))O1.R3.)(4.(18.$<.O1.R3.)(4.(19.$<.R3.)(4.(=.$<.R3.(12.O14.-;0.)(?.$10.(28.#4.R2.)(?.$10.(32.(8.&40.+22.))(?.$10.(11.(8.&40.+10000000000.))(?.$10.(11.(8.&40.+1994:0.))(?.$10.(11.(8.&40.+10000.))(?.$10.(11.(8.&40.+109288.))(?.$10.(11.(8.&40.+6?62<.))(13.$10.)))))))))(4.(=.$<.R3.(12.O14.-80.)(?.$10.(11.(8.&40.+109288.))(?.$10.(11.(8.&40.O3.))(?.$10.(11.(8.&40.+109280.))(?.$10.(11.(8.&40.+6;:7<.))(13.$10.))))))(4.(=.$<.R3.(12.O14.-60.)(?.$10.(28.#8.R1.)(?.$10.(11.O8.)(?.$10.(11.O9.)(?.$10.(11.O:.)(?.$10.(11.O;.)(?.$10.(11.O<.)(?.$10.(11.O=.)(?.$10.(11.O>.)(?.$10.(11.O?.)(?.$10.(11.O10.)(?.$10.(11.O11.)(?.$10.(11.O15.)(13.$10.))))))))))))))(4.(=.$<.R3.$>.(?.$10.(11.(8.&40.(12.$>.+20.)))(13.$10.)))(4.(=.$<.R3.(12.$>.+10.)(?.$10.(11.(8.&40.+1000000000000000.))(13.$10.)))(4.(=.$<.R3.(12.$>.+20.)(?.$10.(11.(8.&40.=))(?.$10.(11.(8.&40.=))(?.$10.(11.(8.&40.=))(13.$10.)))))(16.$<.R3.O2.(12.O14.-;0.)))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00n0?C17015022970.80L10762970737.63L11517020883.1 L14372174060.65L20205877484.65L23189778160.2 L24852388830.0 L24868018416.2 L25148210289.0 L25297719934.3 L25299206787.4 L25299206791.4 L27342692371.2 L27345793262.3 L30579370628.2 L31612660001.0 L3192510483.66 L32442839532.65L37530440176.2 L41395250160.2 L44680637166.2 L45258359720.1 L45258359745.3 L45258359749.2 L46753930220.65L48699411601.1 L59797380228.2 L62746957296.2 L6292198640.2  L64038912520.64L65918157296.2 L66566358642.5 L67606575856.1 L67899323172.65L9334266860.65 L9764768748.65 N12598536175.81N21468391759.81N21855282908.81N67106240206.81O17015022970.80O21461885008.80O37741719248.80O38077301328.80O49747279952.80O52769784400.80O57112491600.80O60391919696.80P23187700788.80P24864885300.80P37527667508.80P41397170484.80P62749755188.80P6293849652.80 P65920340788.80Q16472773038.62Q20901399470.62Q22227621426.62Q2616397753.62 Q4035741225.62 Q53519997187.62Q9410754020.62 00000100500:00J00Z00[00\00]00^00_00`00a00b00n01601701<01L01M01N01O01P01Q01Z01j01o02702802902C02D02Q02V03703G03W03i03j04604B04N04O04P04Q04R04S04T04U04c05105?05M05[05i06706806A06B06C06D06N06WFS2HBS3SPcS2HB5Ha_st5Hl_stS2HB5Ha_st5Hl_stFSFSFFFFS3SPc2lo3SPLS3SPc2loSS3SPcS2HB5Ha_st5Hl_stFFFFFS3SPc3SPHS2HB5Ha_st5Hl_stS3SPcS3SPc2loFFS2HB5Ha_stFS3SPc2lo1x2HxS3SPcS3SPc2lo5LOIMG3SPL2HB5Ha_st5Hl_stS2HB5Ha_st5Hl_stS2HB5Ha_st5Hl_stS3SPc2lo5LOIMG1x1CFS3SPc2lo1x1CS3SPc2lo1x1CS3SPc2lo3SPLFFFFFFFS3SPc2lo5LOIMGS3SPc2lo5LOIMGS3SPc2lo5LOIMGS3SPc2lo5LOIMGS3SPc2lo5LOIMGS3SPc2lo5LOIMGS3SPc2lo5LOIMGSS2AL4IMG'SFSS2AL5ALWF'S2AL4IMG'". (* [comment removed for export] *)
  Theorem emb_cb_first_pre : ltac2:(CDefT.buildp (gd_tbl_AW_PfEmb ()) "PMSG,$1;.PSPc,$1;.Plo,$1;.Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))P,(=.$<.R1.$>.(?.$10.(11.(8.&40.=))(13.$10.)))P,(=.$<.R2.(12.$>.+10.)(?.$10.(11.(8.&40.=))(13.$10.)))P,(=.$<.R3.(12.$>.+20.)(?.$10.(11.(8.&40.=))(?.$10.(11.(8.&40.=))(?.$10.(11.(8.&40.=))(13.$10.)))))P,(33.$<.R4.$34.(?.$10.(11.(8.&40.$30.))(13.$10.)))P,(33.$<.R5.$30.(?.$10.(11.(8.&40.+1000.))(13.$10.)))P,(33.$<.R6.$35.(?.$10.(11.(8.&40.$36.))(13.$10.)))P,(33.$<.R7.$37.(?.$10.(38.(8.&8.=))(13.$10.)))P,(16.$<.R8.R28.R29.)P,(21.+65?000.R29.)P,(21.R2:.(29.R2;.+1<0.))P,(21.R2<.(26.+2.+3?.))P,(24.VCS,R2<.(29.R2=.R2<.))P,(19.$<.R=.)P,(4.(25.=R30.)(25.R30.(26.+2.+3?.)))(2<.$<.VAL,VCS,(39.R2>.R30.R2=.R2<.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R11.R10.R31.R2?.R?.)(6.(7.R2>.(8.&40.R30.)R2=.R2<.R2;.R2:.R29.R28.R27.(8.&40.R31.)R1<.R1;.R1:.R19.R18.R17.R16.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R15.R14.R13.R12.)R11.(8.&40.+6;948.)R10.(:.(2.&40.))R?.(;.$<.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros EP EMX EV GOT PGS GOTF DEC ST LOIMG SPL SPH SCS MI MSGB.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold emb_first_svc_post, A_EMB, A_GOT_PAGESZ, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_DECORATE in *.
    pose proof (munch_refl [(lo, SPc); (0x109268, 0x109268 + 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    change (1086056 + 16) with 1086072 in *. change (1086056 + 32) with 1086088 in *. change (1086056 + 56) with 1086112 in *.
    (* [comment removed for export] *)
    lx_run (PLAN [0x6b9d0] [] 60%N). try clear LXlen.
    (* [comment removed for export] *)
    try (pose proof ALWF as ALWF'; unfold al_wf in ALWF'). try (pose proof IMG as IMG'; unfold asan_img_ok in IMG').
    clear EP EMX EV GOT PGS GOTF DEC ST MI.
    zstep. zstep. zstep. zstep.
    lx_fold_mkR.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7c928] [] 60%N). try clear LXlen.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) => repeat match goal with H : context [?mo] |- _ => lazymatch type of H with context [mx] => fail | _ => (constr_eq mo mx; fail 1) || (is_var mo; match type of mo with mem => clear H end) end end end.
    lx_junk_under lo (SPc + -88) 8%nat j8 FR.
    lazymatch goal with STl : stk _ ?mx lo (SPc + -128) |- _ =>
      eapply (evtA_mono asegs AL CS);
      [ eapply (mmapdie_pre AL IMG ALWF CS CSOK) with (size := 65536) (name := 139685) (raw := 1) (lo := lo);
          first [ exact STl | assumption | clear; lia | clear -SPL; lia | clear -SPH; lia | intros x Hx; apply SCS; clear -Hx SPL; lia ]
      | ] end.
    cbn beta. intros ms' (t0' & t1' & t2' & t3' & t4' & t5' & t6' & a6' & mm & fr & -> & MU3 & WM3 & MI3 & FR3 & ST3).
    lazymatch type of MU3 with munch _ ?mx _ => transport_after_call asegs mx mm MU3 WM3; clear MU3 WM3; lx_clear_mem mx end.
    replace (SPc + -128 + -48) with (SPc + -176) in * by (clear; lia).
    lazymatch goal with MUl : munch _ m mm, WMl : wmono _ m mm |- _ =>
      eexists t0', t1', t2', t3', t4', t5', t6', a6', mm, fr, _; split; [reflexivity|];
      split; [exact MUl|]; split; [exact WMl|]; split; [exact MI3|]; split; [exact FR3|];
      split; [assumption|]; split; [exact FR|]; split; [assumption|]; split; [assumption|]; split; [assumption| exact ST3] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00c0?L17217255245.1 L1872319822.1  L1958026319.1  L20713654111.72L23964203085.1 L25297404829.72L26562657487.0 L27343401456.72L28754209816.1 L30579370628.2 L32964720465.1 L34305501713.1 L34539546910.4 L34908015867.72L35476651494.67L35574332497.1 L37530440176.2 L39778167285.72L40275491312.2 L45260686047.72L48366437576.67L48368533590.2 L51764672013.1 L5423434321.1  L59797380228.2 L60407395161.72L62746957296.2 L6292198640.2  L65918157296.2 L66566358642.74L67604773767.72L8747172257.0  L8839293968.72 N12598536175.91N21468391759.91N21855282908.91N41262473690.91N67106240206.91N7198125091.91 O21107722838.89O21461885014.89O38077301334.89O52769784406.89O60391919702.89O818431772.89  P34537503708.89P37527667506.89P40277175090.89P62749755186.89P6293849650.89 P65920340786.8900000100600;00<00=00>00?00V00W00_00`00e00f01601M01N01O01P01Q01e02<02=02>02?02G02H02I02J02K02c03303403@03]03^04504P04g04h04i04j04k04l04m04n05I05b06;06T06m07FFS3SPcS3SPcFFFSS3hAR1s3SPc2lo1a2ua3SPLFS3SPc2loFS3SPcFS3hAR1s1a2ua3ALOS3hAR1s3SPc2lo1a2ua3SPLFFFFS3hAR1s3SPc1a2ua3SPHS3hAR1s3SPc2lo1a2ua3SPLFFFS3SPc2loFFFFS3hAR1s3SPc2lo1a2ua1x2HxS3hAR1s3SPc1a2uaSS3hAR1s1a2uaS3hAR1s3SPc2lo1a2ua5LOIMG1x1CFS3hAR1s3SPc2lo1a2ua1x1CS3hAR1s3SPc2lo1a2ua3AHI1x1CS3hAR1s3SPc2lo1a2ua1x1CFFFFFFFS3hAR1s3MSG3SPc2lo1a3SPM2uaS3hAR1s3SPc2lo1a2ua5LOIMGS3hAR1s3SPc2lo1a2ua5LOIMGS3hAR1s3SPc2lo1a2ua5LOIMGS3hAR1s3SPc2lo1a2ua5LOIMGS3hAR1s3SPc2lo1a2ua5LOIMG". (* [comment removed for export] *)
  Theorem emb_cb_first_post_ok : ltac2:(CDefT.buildp (gd_tbl_AW_PfEmb ()) "Ps,(1:.(2.&8.))PMSG,$1;.PSPc,$1;.Plo,$1;.Pa,(2.&40.)Pfr,(1:.(2.&8.))Pj8,(1:.(2.&8.))Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))P,(1=.$<.R1.R21.(1>.(2.&8.)R22.(?.(2.&8.)(8.&8.=)(13.(2.&8.)))))P,(1?.(20.(2.&8.)(8.&8.=)R23.))P,(4.(21.+1.(22.(23.(2.&8.)R24.)))(21.(22.(23.(2.&8.)R24.))+190.))P,(24.VCS,R24.(12.(22.(23.(2.&8.)R25.))+1.))P,(21.R24.R25.)P,(25.(12.(12.R26.(22.(23.(2.&8.)R27.)))+1.)(26.+2.+3?.))P,(21.+65?000.(3:.&40.R24.))P,(21.(12.(3:.&40.R25.)$14.)(3;.VhAR,))P,(21.(12.(3:.&40.R26.)$14.)R27.)P,(15.$<.R:.(3:.&40.R27.)$14.)P,(24.VCS,(3:.&40.R28.)$14.)P,(=.$<.R<.(12.R2;.-;0.)(?.$10.(28.#4.R28.)(?.$10.(32.(8.&40.+22.))(?.$10.(11.(8.&40.+10000000000.))(?.$10.(11.(8.&40.+1994:0.))(?.$10.(11.(8.&40.+10000.))(?.$10.(11.(8.&40.+109288.))(?.$10.(11.(8.&40.+6?62<.))(13.$10.)))))))))P,(=.$<.R=.(12.R2<.-80.)(?.$10.(11.(8.&40.+109288.))(?.$10.(11.(8.&40.R2=.))(?.$10.(11.(8.&40.+109280.))(?.$10.(11.(8.&40.+6;:7<.))(13.$10.))))))P,(=.$<.R>.(12.R2=.-60.)(?.$10.(28.#8.R29.)(?.$10.(11.R19.)(?.$10.(11.R1:.)(?.$10.(11.R1;.)(?.$10.(11.R1<.)(?.$10.(11.R1=.)(?.$10.(11.R1>.)(?.$10.(11.R1?.)(?.$10.(11.R20.)(?.$10.(11.R21.)(?.$10.(11.R22.)(?.$10.(11.R28.)(13.$10.))))))))))))))P,(=.$<.R?.$>.(?.$10.(11.(8.&40.(12.$>.+20.)))(13.$10.)))P,(=.$<.R10.(12.$>.+10.)(?.$10.(11.(8.&40.+1000000000000000.))(13.$10.)))P,(=.$<.R11.(12.$>.+20.)(?.$10.(11.(8.&40.=))(?.$10.(11.(8.&40.=))(?.$10.(11.(8.&40.=))(13.$10.)))))P,(33.$<.R12.$35.(?.$10.(11.(8.&40.$36.))(13.$10.)))P,(33.$<.R13.$3<.(?.$10.(11.(8.&40.=))(13.$10.)))P,(16.$<.R14.R32.(12.R33.-;0.))P,(21.+65?000.R33.)P,(21.R34.(29.R35.+1<0.))P,(21.R36.(26.+2.+3?.))P,(24.VCS,R36.(29.R37.R36.))P,(17.(?.(2:.$1;.$1;.)(2;.$1;.$1;.R37.R38.)(?.(2:.$1;.$1;.)(2;.$1;.$1;.$>.(12.$>.+38.))(?.(2:.$1;.$1;.)(2;.$1;.$1;.(3:.&40.R36.)(12.(3:.&40.R36.)$14.))(13.(2:.$1;.$1;.)))))R1:.R19.)P,(18.$<.R1;.R1:.)P,(19.$<.R1;.)(2<.$<.VAL,VCS,(2=.R36.R3;.R35.R34.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R1?.R1>.(?.(2:.$1;.$1;.)(2;.$1;.$1;.R3:.R3;.)(?.(2:.$1;.$1;.)(2;.$1;.$1;.$>.(12.$>.+38.))(?.(2:.$1;.$1;.)(2;.$1;.$1;.(3:.&40.R39.)(12.(3:.&40.R39.)$14.))(13.(2:.$1;.$1;.)))))R3:.(3:.&40.R39.)(12.(22.(23.(2.&8.)R3=.))=)R1=.)(3=.R39.(12.R3;.-80.)R35.R34.R33.R32.R31.(8.&40.+109268.)(8.&40.+2000000000000000.)(8.&40.+109278.)(8.&40.+1000000000000000.)(8.&40.+10000000000?????.)(8.&40.+=???????????????.)R26.R25.R24.R23.R22.R21.R20.R1?.R1>.+10000.+221:5.+1.R1<.))")
(* [comment removed for export] *).
  Proof.
    intros until mm. intros BY NZ SL CRM SPM MH ALO ACE AHI WRB CRD FRM FRR FRC EP EMX EV GOTF LIM ST LOIMG SPL SPH SCS MU WM MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 64 a) as AR. unfold bv_modulus in AR. change (2 ^ Z.of_N 64) with (2^64) in AR.
    set (ua := bv_unsigned a) in *.
    unfold emb_cb_post, kEmbBytes, A_EMB in *.
    change (1086056 + 16) with 1086072 in *. change (1086056 + 32) with 1086088 in *. change (1086056 + 56) with 1086112 in *.
    eapply (evtA_cut asegs AL CS).
    { eapply (mmapdie_post_ok AL IMG ALWF CS CSOK) with (m0 := mm) (lo := lo) (fr := fr); try eassumption; try (fold ua; lia).
      - replace (SPc + -128 + -48) with (SPc + -176) by lia. exact FRM.
      - replace (SPc + -128 + -48) with (SPc + -176) by lia. exact ST.
      - apply munch_refl.
      - apply wmono_refl.
      - intros x Hx. apply SCS. lia. }
    cbn beta. intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
    clear FRM ST. unfold A_GOT_CFLAGS, A_CFLAGS, A_MMAP_LIMIT in *. transport_after_call asegs mm m1 MU1 WM1. clear MU1 WM1 MI.
    rewrite <- (Z_to_bv_bv_unsigned a). fold ua.
    ret_lit.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM.
    pose proof (munch_refl [(lo, SPc); (1086056, 1086112); (ua, ua + 65536)] m1) as MUr. pose proof (wmono_refl asegs m1) as WMr.
    lx_aceil.
    lx_run (PLAN [0x6ba7c] [] 60%N). try clear LXlen.
    lazymatch goal with WMl : wmono _ m1 ?mx |- _ => pose proof (wr_at_transport _ _ _ _ _ WRB WMl) as WRB'; clear WRB; rename WRB' into WRB end.
    lx_acc_run m0 m1. lx_clear_mem m1. lx_unhide. lx_stk_grow_to lo (SPc + -96).
    lazymatch goal with MUl : munch _ m0 ?mx, WMl : wmono _ m0 ?mx', STl : stk _ _ lo (SPc + -96), BYl : bytes_at _ _ MSG _, FRl : rw_cells _ _ (SPc + -96) _ |- _ =>
      eapply (evtA_mono asegs AL CS);
      [ eapply (emb_cb_tail s MSG SPc lo ua 0 j8 ra) with (m0 := m0);
          first [ exact BYl | exact FRl | exact STl | exact MUl | exact WMl | exact WRB | assumption | clear; lia | lx_arith ]
      | ] end.
    cbn beta. unfold emb_cb_post, A_EMB, kEmbBytes. intros ms' Hp.
    change (1086056 + 16) with 1086072 in *. change (1086056 + 32) with 1086088 in *. change (1086056 + 56) with 1086112 in *.
    rewrite ?Z.add_0_r in Hp. rewrite ?Z.add_0_r. exact Hp.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Emb.
End ARUN_1.
