(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_asn1_get_tag U_asn1_get_int U_oid U_oid_md_alg U_asn1_get_mpi U_platform_zeroize U_asn1_get_alg_A U_asn1_get_alg U_asn1_get_alg_null U_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00ac8572b35bb041 0 2 0 1 32 1P019175276679501f 0 3 0 1 34 1 43 1P0238135bd3063d12 0 4 0 1 39 1 41 1 42 1P02ce87337201b23e 0 2 0 1 1 1P02f51881000c14aa 0 2 0 1 36 1P03211eea967a0965 0 2 0 1 1 1P06238e32e7e58e98 0 5 0 1 39 1 42 1 54 1 56 1P066836d91b6fb4b9 0 2 0 1 36 1P06f444049e8d269f 0 2 0 1 36 1P0f41896c0c9761e8 0 2 0 1 42 1P0f998f9b4423164a 0 2 0 1 39 1P1026a0a351d1fb20 0 4 0 1 39 1 41 1 42 1P127cbab235851f0a 0 2 0 1 42 1P1675284731a509fe 0 2 0 1 1 1P16910ca7c4b9fe70 0 4 0 1 30 1 43 1 44 1P1795aa5cd26e6864 0 4 0 1 30 1 43 1 44 1P19e206d5ece11fe1 0 2 0 1 32 1P1acbaf4f7a457fc7 0 4 0 1 30 1 43 1 44 1P1e3ce2150b2849dc 0 3 0 1 39 1 41 1P1e84804977980f52 0 4 0 1 30 1 43 1 44 1P1f31dd03c83d89a6 0 2 0 1 31 1P202f1ff94f83477a 0 4 0 1 30 1 43 1 44 1P203a69a4110c019a 0 3 0 1 29 1 40 1P2202a446980118ab 0 2 0 1 30 1P2301a7050a79ce65 0 2 0 1 1 1P23617b1a44cec0aa 0 3 0 1 39 1 41 1P23a51bc472e50b8b 0 4 0 1 42 1 54 1 56 1P242e08b1b37df3ae 0 3 0 1 29 1 40 1P24fdcbcaa0515498 0 5 0 1 40 1 43 1 49 1 58 1P25524120072e2aa1 0 3 0 1 34 1 43 1P270bbd71e6969693 0 2 0 1 30 1P279b8e9085617f22 0 4 0 1 30 1 43 1 44 1P28d250bd9642e12a 0 6 0 1 39 1 40 1 43 1 49 1 58 1P29678a0712933fa0 0 2 0 1 66 1P2cb5f24c77b0db8b 0 2 0 1 67 1P2f37280536da7a76 0 5 0 1 40 1 43 1 49 1 58 1P308ab34f08ad2307 0 2 0 1 39 1P327b2d8bd9bf2008 0 2 0 1 37 1P359f2c459d2b91d2 0 5 0 1 39 1 42 1 54 1 56 1P367cc8704bf85123 0 6 0 1 39 1 40 1 43 1 49 1 58 1P387663ccce2ecad7 0 2 0 1 30 1P395872f206e3174b 0 2 0 1 66 1P399814d062007844 0 2 0 1 66 1P3c190cde28b57e9e 0 4 0 1 42 1 54 1 56 1P3cbc30f344802caf 0 2 0 1 38 1N00853409934419b6N00ac00acb59f539cN00bc0a0267fbdcb2N00c058f34ee68b3cN00cc7a3e46401903N014a7c38e29a84a7N01a1b56c6def1b84N01a585a11d6e3adeN01e8ca8ef333f14dN0201eba8d9e0180cN0241a5bc432a4fffN026f7b16eb4aeb22N028121b591ddb167N02b81a738280c1ecN02c2edde2a980fb8N02e65bd6e9c3907eN0337f99977b250dbN03392b44df4b02a1N03c44c594e0079c7N03cbc8b3c1f76a5bN0403241d48a43594N040cfddcf473cfa8N0419290926140f04N0434fd934561b959N045c1449443f4cd0N0466ad69d45a333aN0474c22db4764cbfN04793d06f3cf65fdN04e9556bfc0cc282N050800e322486af8N051a3aedbe37f992N052086a3aa0a01c7N05399d01d9a3970fN054e8fcac6cf49f4N059ccadbd8ce59f3N05a809b3e6e92f26N05c6121171a89f04N0661524c3aba5236N06699753b4005a7fN066fddc7a9212a73N0693df4c1a8360c4N06989c84d4abf21eN06a1a9d8cb33eaf0N06d82f246ecd82afN06f58faf2ea2beb7N070563ea06ea0af3N0729e8805effa77aN072a28b5584fca8aN073951d5b53c0cfdN0777bb63b0e845c2N078fd088fa863df5N07c1e59342d698ddN07dabe230d46315fN08197ad192aa1d63N081dd3bdc95f7f21N082617106c9f4415N0842728b8d202e20N08511928ca353c45N087517842d1e38f6N08a69ad713b8f678N08ad98d0ce7582baN08bdd7b469147111N08be099486e430d0N08e451cf4a12cb7dN091035b6c776829bN0910d4be6bfbcdafN091108851644cbf3N0916007a316ca739N09270595c4ffb5c6N09c3a85e65f1b365N09df91c66103a362N0a53e0de5f264024N0a96971061635556N0a97f4f5e7552602N0ab2534ed0a01336N0ac5752ca67f8689N0b18d455d2997c5cN0b229fbac905bca8N0b297d8c6ac39307N0b2c17b1a9fdc0f3N0b4125f7cdc719efN0b78c82d033dc722N0b80efcf22be0acdN0b94d305e9a1176eN0ba579eb4a5bcec6N0ba72dc5bf62c607N0bbe9f3d86e73022N0bf288c9fa4163a9N0c38114b52fbbcb6N0c5667fcfb95fa59N0c817c128a4ecb08N0c9af71853273930N0ca50964fb9e39abN0cf189d157ac6511N0d11aff585b29a76N0d35eeeaf64dd65bN0d4a9399e009875aN0d6b895c9e1206b5N0d8803c48df46d18N0da28674e45e507aN0db0b2638dc1cfdeN0dc374f2b7cc74eeN0dd209a7a7c36876N0de47d38ef56a3b6N0de9b69a445aaa66N0e6127355547a7abN0e66cd7094f73fc7N0e6807f40d9acd4eN0e9d1536819721edN0f24aa5d58ce2f83N0f2e4ed33b05dba3N0f46d9357882eb12N0f93cab62e841162N0fd1abb8134a5716N0fd2d53577626569N101715fc7dc62bd3N1025619aea531a6eN102b64e1960327a5N103236c174818d41N1040e44f6f618e94N10677d231a831eedN109b43839a6d39f1N10ba03f408d42191N10c253af3716e0b8N112556972bbc4784N1137d1e96c3f2326N115736171d29edf5N118772ec72a4819cN11fda502001e2b40N11ffe62b2558ecb4N1200f38da5506d66N120bf0a2ec141aeaN123212f390b71823N127c442c84acc645N128c21f34fdfb853N12b89320c6d0533fN12f2f01743e2ef01N12f87a559e58e239N1354c2d198ee46f8N13a7428b7edfc920N13d8ab897ab88b5aN13dfad591324db30N13e6938f738eea09N140b1e49e83aedecN1419c0b198aed762N141a97d518dbeceeN1420cc01af5e5aafN14b5d8d93702c951N14ba2f453654c731N14c961de99a6a34eN14cc421f2950278eN14d3cec09c2c0521N14ef33515fe1f4ecN1506f3f76f62c98fN1592ba0060394cb3N15a41b4276af16fcN15a71f422acf9b4bN15a9218de7df88feN15d1e19e54da323fN15e3248d598ab514N1642ef5be7f3d7d8N16511f5cc1a0e304N16c9dec36b5d443cN16cb803e0c510b83N16d0308b5f5e7a00N174fc55e2c930e4cN1778b373a617959eN178addaff26993f8N178b41b0dc428f43N17b6928f24833a56N17d20441b4b7835bN1802dd83ddfc523fN18036ca2dde279e4N1835a56a91aa52e6N183a5243d6be20e2N186ae0077204e1fdN18b9c2e51886db78N1929228e5dcee960N195b737e9d7173a7N1964ead65f24b64eN19713156e03ddf6eN19bf68a74a1fc78eN19c108544e90e743N19d2c4e949c46dc0N1a06a170006e6326N1a12b631905a6d43N1a1de00b29c0aa85N1a6cb16f2480ad18N1a734c598d57225fN1a95264dcf8c4fe4N1ac237c394e05d59N1ad659d609701265N1b2dc1beca6538eeN1b7b48813677c9e7N1b9feba8a65ac623N1ba81f4d4295844fN1bb4dc02fb9c2962N1bba5b099451087eN1bd7a61233dd2bb7N1c0869f36c050d8aN1c20b2c6e598422dN1c30839fa0906441N1c86627ac9da1d0bN1cb7412a9f92a796N1cd0952453862765N1ce7c0b2191dca4eN1cf421d4be64dd5cN1cf8f20a2aaa9926N1d6aaa68c421622dN1e58a060614b6effN1e65f5ea5f1e5e61N1ed6d99be07d471bN1f301ed5e28eb6a5N1f33adaf8c3e7a58N1f3450b3abbfd459N1f826d97716928b0N1f9739110f3d4d1fN1faaed80cd88afe3N1fdc80c011f7dafcN1fe95f93cbe8cd8cN1ffd1678275b831fN202c95ecd7adb511N205c74648961a199N20604baa9dec2f84N208781a7c8b49022N20c65b16384c83eaN2146145441d5f295N214f0e2479652286N21572471842337e2N218d866a10758d43N21c003856b648cdeN21efd4b4aee244b2N21f15e466bc14a8fN21f7b5a9ae5c7728N21fe481cd6cec5bdN22ca82540a6b7751N22d53ff7566f1af4N22dd265cfe388f7cN2313e8e9e3dbef9fN2355a43cb23eb361N23658e9a0153908fN2398e38c953cc965N23adf87d2760a25bN23ae5b3450ca274dN23b1714ac36b31f8N23c3a3855c7a3c72N23e6a3fc7f89103aN2444da388c969447N2453d74adc1388e1N245aa35f4a6b720bN247876db4f381650N24bf26856aa5326aN2535c67abc420afeN253aca107adf7419N254c3252ad716de0N256af2712cdb6860N257605ec0d21b0dfN25853f800852f1adN25afb122280f7221N25e9cd2c2bf286c0N25f91c7f953574a8N25fe6c429facdcdeN2612d83c75455aa0N2621eab987e1d81fN2623af249a7f1b4bN262ec1c40cc32b80N263cca9a57c2191fN26469b99f9235c06N2668c88cafcee450N26a1fb11181f6f0aN26a3c0d762ba6d09N26aa9a8a82d3383fN26d604d3a8b952d2N26d760a6054096a7N272b4fde0cb4e056N277bc4ab85903b4aN279dd695b789a90cN27a81ccc995c335aN27abbd1395bf0b7cN27bf7a72debe8b21N27de83527ea717e0N27df537b3815ad73N2802dae5f8f2f60cN2812a2ee6d9aa159N2853fe37722dfab6N28615f7dd6997ce6N28a3bc32266bfd22N28c19e48e5969990N28c481e4e632f303N2927789379d99648N29510336429e9b14N29512b75c8c421baN29801436fd5cd7d3N29934d736eff8902N299818619e3f77fdN29e6c63921a50daaN2a5cfbc752f6592cN2a684f7b41138ff0N2a7072843d36cd80N2b0a79c3e718468eN2b490ca307ddabc2N2b577875fcb6a1ecN2b83569f7fb440f4N2bb92a3f361ef43dN2bbd54941996ea96N2bbecf8fad43785fN2bdf0cb59cfa17b7N2be2a0f91a98f0ccN2c237eb9c715c9b1N2c30518f4baf6ebeN2c6996aa79c2f16dN2d1b4db9ea8a6586N2d1d270c990fb5adN2d25656fcef19baeN2d2d9840046b875aN2d499b8977c455e3N2d7c3d3e8c84750fN2d7f219261d457daN2d830ef9cd82b38bN2d8f941eddf36ec2N2da1ee8e6bceab1cN2dbe3bcadba22be2N2dc4fe0c34b33362N2dce9d9112758872N2df585708ddb40a9N2e035c520bf1695aN2e2acbf63ca69953N2e387b59da401f22N2e6313274283b899N2e98e07b04a8eb31N2ec929c260167402N2ed2e5f7ce073edeN2ef30b6f4b2ee913N2f063c0378b90f25N2f1a8363ebf6314cN2f45b7b5026447f0N2f5c95d30281afa8N2f64a1dd3f96e415N2f76da3ecac89655N2fa8f4354deb5580N2fbb6c4c9216ed61N2fcac196851fef35N30618e1a0981bf98N30874ed6345beb23N30fcae708b9c140bN313e4380e392c313N31669c174feeb252N31b82d52250c3710N31f6586348760f4bN321836f797647726N32324402a54febc9N3272011ada26ab2dN3335b7dbae8eb704N33587af24f19dacbN338ce44fc0ca3549N33a35e36bdf058b4N33dd884a9953debaN33f40f57ca619115N34ac6b0c130d4221N34b1e2ba4036ec34N34c1d071a501e8afN34c48d10154c9e88N34eac0db153cad3aN34f8a3704e8b6cf5N3554b6936e7253d7N356f672ddf7a7112N3591f5408a6ef280N3596e2931e509fb9N35ac83d8917c8448N35b1b71569054000N35c7e9091f839c62N35d2344159cabe60N35f95a8d849fef07N3627ee199d7c5dbaN3654498741ce9013N36f2e728d7f1a194N37381768efe257e2N3758992676e466bfN376979244e1f86cdN3788a3f7e89c02edN37d2d179684da1e2N37e0671631f2ddc2N37f0f25aad87c2e1N37fed297f51b80d0N38055721d217e60bN384371bd0707a2b4N38a052bb3c1df9a5N38aa3c19019beae8N38b8f3b492c4e0a3N3909e4e7b802408fN391b8c7ec73a3346N395130ea99d887c7N395de68ebace42d5N396b43fe5fb734e4N3975d6791914f7a5N39c48eb031a3010eN39d741476fd6f4e8N39f4d458944e4a6fN3a117117ff5df4bdN3a235bde99747bf6N3a28447716d64b18N3a5979f2cd383f28N3a6c61615c29fd77N3a70e8e6b244068bN3a99df81b5a536b6N3a9eef34e9358ebcN3ac48e6329b16e19N3b58eaf5e34226c2N3ba28a7b7c57bb7aN3bdb25fa8b41c431N3c13f288a0139dcfN3c39462211e89fe6N3c6283d77954ef3fN3c6ffadaf4762938N3c7febd6d186d9fcN3c907d9909211c6dN3ce2be37296d04ecN3d101f9f404f48f4N3d227458b3fb092aN3d30878cc9001692N3d3c1572991e2293N3d7a8fc8096c0e11N3d9552255d900471N3deb8c99ac46cbe4N3e13de564d6fd996N3e28dae8a77d7241N3e3c254bb5b89168N3e818a07ca161d19N3e822df22eded288N3e847821ea24ddb3N3ea7278cc3548201N3eadcc973b8c6b32N3f1c619ffd96e609N3f54fe205dd21ed7N3f6b3237c0eeba55N3f89bcfe4926c739N3fa418c68723bc6dN3fe2e2ff3a277549"%lxh.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition U_X509_GET_RSASSA_PSS_PARAMS : Z := 0x2789c.
Notation X509_RSASSA_STACK := 240 (only parsing).

Definition x509_get_rsassa_pss_params_post (segs : list Segment) (L : heap_layout)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (MD MGF SALT lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r : Z) (v1 v2 v3 : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(MD, MD + 4); (MGF, MGF + 4); (SALT, SALT + 4); (bv_unsigned sp - X509_RSASSA_STACK, bv_unsigned sp)] m m'
    /\ wmono segs m m' /\ mem_inv segs m'
    /\ a0 = Z_to_bv 64 r /\ (-0x3000 < r <= 0)
    /\ rw_cells segs m' MD [C4 v1] /\ rw_cells segs m' MGF [C4 v2] /\ rw_cells segs m' SALT [C4 v3]
    /\ stk segs m' lo (bv_unsigned sp)
    /\ statics_ok segs L m'.

Definition x509_get_rsassa_pss_params_stmt (segs : list Segment) (L : heap_layout) (ENTRY MSF MDTBL : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PAR MD MGF SALT BUF pp lo : Z) (bs : list byte) (ptag ppad plen v1 v2 v3 : word),
  rw_cells segs m PAR [C4 ptag; C4 ppad; C8 plen; C8 (Z_to_bv 64 pp)] ->
  rw_cells segs m MD [C4 v1] -> rw_cells segs m MGF [C4 v2] -> rw_cells segs m SALT [C4 v3] ->
  bytes_at segs m BUF bs ->
  ((pp = 0 /\ bv_unsigned plen = 0) \/ (BUF <= pp /\ pp + bv_unsigned plen <= BUF + Z.of_nat (length bs))) ->
  BUF + Z.of_nat (length bs) < 2^63 ->
  (MD + 4 <= MGF \/ MGF + 4 <= MD) -> (MD + 4 <= SALT \/ SALT + 4 <= MD) -> (MGF + 4 <= SALT \/ SALT + 4 <= MGF) ->
  (MD + 4 <= PAR \/ PAR + 24 <= MD) -> (MGF + 4 <= PAR \/ PAR + 24 <= MGF) -> (SALT + 4 <= PAR \/ PAR + 24 <= SALT) ->
  (MD + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= MD) -> (MGF + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= MGF) ->
  (SALT + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= SALT) ->
  PAR mod 8 = 0 -> MD mod 4 = 0 -> MGF mod 4 = 0 -> SALT mod 4 = 0 ->
  0 < PAR -> 0 < MD -> 0 < MGF -> 0 < SALT -> 0 < BUF ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - X509_RSASSA_STACK -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PAR + 24 <= lo \/ bv_unsigned sp <= PAR) -> (MD + 4 <= lo \/ bv_unsigned sp <= MD) ->
  (MGF + 4 <= lo \/ bv_unsigned sp <= MGF) -> (SALT + 4 <= lo \/ bv_unsigned sp <= SALT) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m -> statics_ok segs L m -> const_at L MSF 8 -> const_at L MDTBL 440 -> hl_data_hi L <= alloc_ceiling ->
  (MD + 4 <= hl_data_lo L \/ hl_data_hi L <= MD) -> (MGF + 4 <= hl_data_lo L \/ hl_data_hi L <= MGF) ->
  (SALT + 4 <= hl_data_lo L \/ hl_data_hi L <= SALT) ->
  a0 = Z_to_bv 64 PAR -> a1 = Z_to_bv 64 MD -> a2 = Z_to_bv 64 MGF -> a3 = Z_to_bv 64 SALT ->
  evt segs (x509_get_rsassa_pss_params_post segs L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MD MGF SALT lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).


(* [comment removed for export] *)
Definition rsassa_ctx (segs : list Segment) (L : heap_layout) (MSF MDTBL AALGN AALG AMD AHASH : Z)
    (sp : word) (PAR MD MGF SALT BUF pp lo : Z) (bs : list byte) (plen : word) : Prop :=
  asn1_get_alg_null_stmt segs L AALGN MSF /\ asn1_get_alg_stmt segs L AALG MSF
  /\ oid_lookup1_stmt segs L AMD MDTBL 440 48 /\ x509_get_hash_alg_stmt segs L AHASH MDTBL
  /\ pp + bv_unsigned plen <= BUF + Z.of_nat (length bs) /\ 0 <= pp /\ BUF + Z.of_nat (length bs) < 2^63
  /\ (MD + 4 <= MGF \/ MGF + 4 <= MD) /\ (MD + 4 <= SALT \/ SALT + 4 <= MD) /\ (MGF + 4 <= SALT \/ SALT + 4 <= MGF)
  /\ (MD + 4 <= PAR \/ PAR + 24 <= MD) /\ (MGF + 4 <= PAR \/ PAR + 24 <= MGF) /\ (SALT + 4 <= PAR \/ PAR + 24 <= SALT)
  /\ (MD + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= MD) /\ (MGF + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= MGF)
  /\ (SALT + 4 <= BUF \/ BUF + Z.of_nat (length bs) <= SALT)
  /\ PAR mod 8 = 0 /\ MD mod 4 = 0 /\ MGF mod 4 = 0 /\ SALT mod 4 = 0
  /\ 0 < PAR /\ 0 < MD /\ 0 < MGF /\ 0 < SALT /\ 0 < BUF
  /\ lo <= bv_unsigned sp - 240 /\ alloc_ceiling <= lo /\ 4096 < alloc_ceiling /\ bv_unsigned sp mod 16 = 0
  /\ (PAR + 24 <= lo \/ bv_unsigned sp <= PAR) /\ (MD + 4 <= lo \/ bv_unsigned sp <= MD)
  /\ (MGF + 4 <= lo \/ bv_unsigned sp <= MGF) /\ (SALT + 4 <= lo \/ bv_unsigned sp <= SALT)
  /\ (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF)
  /\ const_at L MSF 8 /\ const_at L MDTBL 440 /\ hl_data_hi L <= alloc_ceiling
  /\ (MD + 4 <= hl_data_lo L \/ hl_data_hi L <= MD) /\ (MGF + 4 <= hl_data_lo L \/ hl_data_hi L <= MGF)
  /\ (SALT + 4 <= hl_data_lo L \/ hl_data_hi L <= SALT)
  /\ 0 <= bv_unsigned sp < 2^64 /\ (0 <= MD /\ MD + 4 <= 2^64) /\ (0 <= MGF /\ MGF + 4 <= 2^64)
  /\ (0 <= SALT /\ SALT + 4 <= 2^64) /\ (0 <= PAR /\ PAR + 24 <= 2^64).

Ltac open_ctx HC :=
  pose proof HC as HCc;
  destruct HCc as (HALGN & HALGS & HMDS & HHASH & HPP2 & HPP1 & B4 & D12 & D13 & D23 & D1P & D2P & D3P & D1B & D2B & D3B
                   & ALP & AL1 & AL2 & AL3 & NZP & NZ1 & NZ2 & NZ3 & NZB & SLO & ACL & ACP & SPA & DSP & DS1 & DS2 & DS3 & DSB
                   & CA & CT & DHI & OD1 & OD2 & OD3 & SPR & MDB & MGFB & SALTB & PARB).

Section Walk.
  Variable L : heap_layout.
  Variables (MSF MDTBL : Z).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PAR MD MGF SALT BUF pp lo : Z) (bs : list byte) (plen : word).

  Notation CTX := (rsassa_ctx usegs L MSF MDTBL U_ASN1_GET_ALG_NULL U_ASN1_GET_ALG U_OID_GET_MD_ALG U_X509_GET_HASH_ALG sp PAR MD MGF SALT BUF pp lo bs plen).
  Notation W := [(MD, MD + 4); (MGF, MGF + 4); (SALT, SALT + 4); (bv_unsigned sp - 240, bv_unsigned sp)].
  Notation POST := (x509_get_rsassa_pss_params_post usegs L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc MD MGF SALT lo m).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -128)).
  Notation ENDv := (pp + bv_unsigned plen).
  Hypothesis HC : CTX.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L43101658713.94L59314873579.6 00000S00TS2sp3PAR2MD3MGF4SALT2bs1r2j42Hr3LXJS". (* [comment removed for export] *)
  Lemma exit_walk : forall (r p : Z) (j4 : list byte) (tfw lw : word) (qtag qpad qlen qpw atag apad alen apw w1 w2 w3 : word)
                           (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word) mm,
    rw_cells usegs mm (bv_unsigned sp + -128) [CB 12 j4; C4 tfw] ->
    rw_cells usegs mm (bv_unsigned sp + -112) [C4 qtag; C4 qpad; C8 qlen; C8 qpw] ->
    rw_cells usegs mm (bv_unsigned sp + -88) [C4 atag; C4 apad; C8 alen; C8 apw] ->
    rw_cells usegs mm (bv_unsigned sp + -64) [C8 lw] ->
    rw_cells usegs mm (bv_unsigned sp + -56) [C8 (Z_to_bv 64 p)] ->
    rw_cells usegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs mm MD [C4 w1] -> rw_cells usegs mm MGF [C4 w2] -> rw_cells usegs mm SALT [C4 w3] ->
    stk usegs mm lo (bv_unsigned sp + -128) -> munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> statics_ok usegs L mm ->
    -0x3000 < r <= 0 ->
    evt usegs POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x27a7c) fc None mm (seg_rom usegs)).
  Proof.
  intros r p j4 tfw lw qtag qpad qlen qpw atag apad alen apw w1 w2 w3 x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 mm
    F0 FPAR FALG FL FP FS HMD HMGF HSALT ST MU WM MI SOK Hr.
  open_ctx HC.
  lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x279b4; 0x279dc; 0x27bf8; 0x46940] [] 197%N).
  lxp_ret.
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L31969705993.95L3695288089.95 L59314873579.6 00000N00l00mS2sp3PAR2MD3MGF4SALT2bs2j43LXJS2sp3PAR2MD3MGF4SALT2bs2j43LXJS". (* [comment removed for export] *)
  Lemma sel_walk : forall (p q : Z) (j4 : list byte) (tfw lw : word) (qtag qpad qlen qpw atag apad alen apw w1 w2 w3 : word)
                           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word) mm,
    rw_cells usegs mm (bv_unsigned sp + -128) [CB 12 j4; C4 tfw] ->
    rw_cells usegs mm (bv_unsigned sp + -112) [C4 qtag; C4 qpad; C8 qlen; C8 qpw] ->
    rw_cells usegs mm (bv_unsigned sp + -88) [C4 atag; C4 apad; C8 alen; C8 apw] ->
    rw_cells usegs mm (bv_unsigned sp + -64) [C8 lw] ->
    rw_cells usegs mm (bv_unsigned sp + -56) [C8 (Z_to_bv 64 q)] ->
    rw_cells usegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs mm MD [C4 w1] -> rw_cells usegs mm MGF [C4 w2] -> rw_cells usegs mm SALT [C4 w3] ->
    stk usegs mm lo (bv_unsigned sp + -128) -> munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> statics_ok usegs L mm ->
    0 <= p -> p < 2^63 ->
    evt usegs POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 ENDv) (Z_to_bv 64 p) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x279dc) fc None mm (seg_rom usegs)).
  Proof.
  intros p q j4 tfw lw qtag qpad qlen qpw atag apad alen apw w1 w2 w3 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 mm
    F0 FPAR FALG FL FP FS HMD HMGF HSALT ST MU WM MI SOK Hp0 Hp1.
  open_ctx HC.
  pose proof (bv_unsigned_in_range 64 plen) as PLR.
  unfold bv_modulus in PLR.
  cbn in PLR.
  lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x279b4; 0x27a7c; 0x27bf8; 0x46940] [] 197%N).
  lxp_apply exit_walk.  (* [comment removed for export] *)
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01f0@D12218223161.164D12428150072.190D14496695657.166D15604092089.190D16496876345.164D16496876345.190D16974982078.164D16974982078.190D17565844854.164D18465171153.190D20264044729.164D20264044729.190D20994638648.164D2274929014.164 D26291562981.190D297892561.190  D30018886457.190D30210897849.164D30228025918.164D31970719160.190D33783957689.190D35669607670.190D35692261966.190D35924880566.190D36191331830.164D36191331830.190D37224243094.190D37339824057.190D37728747582.190D3827506166.164 D3827506166.190 D40166789585.190D43550644817.190D44484923210.190D45067944057.191D45347449913.190D46029161400.164D46029161400.190D46371768398.190D4758791481.190 D48356160441.164D49981889860.190D52101704109.167D52101704109.192D54602574929.190D55677588537.164D61016641270.190D62814340926.164D62814340926.190D63042527678.164D67071090489.164D67071090489.190D873627326.190  D9195366073.164 D9195366073.190 L12428150072.174L16974982078.148L16974982078.174L17565844854.148L21800167073.0  L2274929014.148 L26291562981.174L30228025918.148L31956544213.97 L35669607670.174L35692261966.174L35924880566.174L36191331830.148L36191331830.174L3708335553.145 L37224243094.174L37728747582.174L3827506166.148 L3827506166.174 L39168452396.124L4048540727.148 L4150533378.146 L44484923210.174L44709467317.124L46371768398.174L49981889860.174L55544472403.123L55544472404.143L59314873579.6  L61016641270.174L62405989940.148L62814340926.148L62814340926.174L63042527678.148L66149329545.121L66149329548.164L66149329549.163L66149329550.161L8060680993.0   L873627326.174  R17698853560.163R19077775108.138R19079872287.163R19360852482.163R21687433375.163R2383289165.163 R26708535608.163R29946627972.138R31542961001.163R34848507727.163R36671363410.163R36673460553.138R37382337318.163R40707931087.163R42695276489.138R51273849103.163R51892457379.138R54652266242.163R62003914580.138R6443869647.163 R6445966804.138 R66030093069.163R68017836946.16300000N00O01;01^02<02_02`02a02b03E03c04F04g04h04i05L05o06M06N07407W07X07Y07Z07[07\07]08@08A08B08C08f09I09J0:;0:^0;?0;e0;f0<I0<g0<h0=o0?;0?^0@<0@=0@>0@?0@@0@^0AA0AB0A`0BC0BD0C@0DA0EA0EB0F>0F?0G;0GY0H^0Ic0Jd0Kd0Li0MG0NH0OI0PE0QF0RT0Sh0TF0TG0UU0VV0VW0W:0W]0W^0X_0Yn0Zj0[k0\g0]N0^50^\0_C0_D0`E0aK0c;0e?0ee0gi0hT0i70jg0l80mD0nL0oO10911E12H13613T14:15A16M17T18\19dS2sp3PAR2MD3MGF4SALT2bs2j43LXJFS2sp3PAR2MD3MGF4SALT2bs2j43LXJ3x353PC03x381HS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTS2sp3PAR2MD3MGF4SALT2bs2j43LXJS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTFFFS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTS2sp3PAR2MD3MGF4SALT2bs2j43LXJS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTS2sp3PAR2MD3MGF4SALT2lo2bs2j43LXJFFS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTS2sp3PAR2MD3MGF4SALT2bs2j43LXJFS2sp3PAR2MD3MGF4SALT2lo2bs2j43LXJ4LXKTS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTFFFFFFS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTFFFS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTFS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKT3x493PC03x521HS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTS2sp3PAR2MD3MGF4SALT2lo2bs2j43LXJS2sp3PAR2MD3MGF4SALT2lo2bs2j43LXJ4LXKTFS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTS2sp3PAR2MD3MGF4SALT2bs2j43LXJFS1L2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPR3LXJ1a1HS1L2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO3ACL3DHI3SPR3LXJ4LXKT1a1HS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTS2sp3PAR2MD3MGF4SALT2bs2j43LXJFFFFS2sp3PAR2MD3MGF4SALT2bs2j43LXJS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTFS2sp3PAR2MD3MGF4SALT2bs2j43LXJS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTFS2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJS2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJ4LXKTS2sp3PAR2MD3MGF4SALT3BUF2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJSS2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJFS2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJS2sp3PAR2MD3MGF4SALT2bs2j43LXJS2sp3PAR2MD3MGF4SALT3BUF2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJ4LXKTS2sp3PAR2MD3MGF4SALT3BUF2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJ4LXKTS2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJ4LXKTS2sp3PAR2MD3MGF4SALT3BUF2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJS2sp3PAR2MD3MGF4SALT3BUF2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJ4LXKTS2sp3PAR2MD3MGF4SALT2bs2j43LXJS2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJ4LXKTS2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJ4LXKTS2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJS2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJ4LXKTS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen1p2j43Hp03NZP3NZ13NZ23NZ33NZB3SPR3LXJ1q3PC3S2sp3PAR2MD3MGF4SALT3BUF2bs1p2j43Hp03NZP3NZ13NZ23NZ33NZB3SPR3LXJ1q2Lw2Hq2q23PC54POSTS2sp3PAR2MD3MGF4SALT2bs2j43LXJFS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen1p2j44HPP22B43NZP3NZ13NZ23NZ33SPR3LXJ1q3PC3S2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJ4LXKTFS2sp3PAR2MD3MGF4SALT2bs2j43LXJ1r2HrS2sp3PAR2MD3MGF4SALT2bs2j43LXJ1r2HrSS2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJ4LXKTS2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen2j44HPP22B43NZP3NZ13NZ23NZ33SPR3LXJ1q2Lw3HqLS2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJS2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJ4LXKTS2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJS2sp3PAR2MD3MGF4SALT2bs2j43LXJ1r2Hr3H11S2sp3PAR2MD3MGF4SALT2bs2j43LXJ1r2Hr3H16S2sp3PAR2MD3MGF4SALT2bs2j43LXJ1r2Hr3H15S2sp3PAR2MD3MGF4SALT2bs2j43LXJ1r2Hr3H14SS2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO2HD3SPR3LXJ4LXKTS2sp3PAR2MD3MGF4SALT3BUF2bs1p2j43Hp03NZP3NZ13NZ23NZ33SPR3LXJ1q2Hq4LXKTS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p2j43Hp04HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR3LXJ3H10S2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p2j43Hp04HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR3LXJ1q2Lw3PC32Hq3HqL2LR4LXKTS2sp3PAR2MD3MGF4SALT2lo2bs2j43LXJ4LXKTS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p2j43Hp04HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR3LXJ1q2Lw3PC32Hq3HqL2LR4LXKTS2sp3PAR2MD3MGF4SALT2bs2j43LXJ1q2Lw2LR4LXKTS2sp3PAR2MD3MGF4SALT2bs2j43LXJ4LXKTS2sp3PAR2MD3MGF4SALT3BUF2pp2lo2bs4plen1p2j43Hp04HPP23D1B3D2B3D3B3NZP3NZ13NZ23NZ33SLO3DS13DS23DS33DSB3SPR3LXJ3H10S2sp3PAR2MD3MGF4SALT3BUF2pp2bs4plen2j44HPP23NZP3NZ13NZ23NZ33SPR3LXJ1q2Lw3HqL4LXKTS1L2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPR3LXJ4LXKTS1L2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPR3LXJ4LXKTS1L2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPR3LXJS2sp3PAR2MD3MGF4SALT2lo2bs2j43SLO3LXJ4LXKTS1L2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPR3LXJ4LXKTS1L2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPR3LXJS2sp3PAR2MD3MGF4SALT3BUF2lo2bs2j43DSB3LXJ4LXKTS2sp3PAR2MD3MGF4SALT2bs2j43LXJS2sp3PAR2MD3MGF4SALT2lo2bs2j43LXJ4LXKTS1L2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPR3LXJS1L2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPR3LXJ4LXKTS1L2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPA3SPR3LXJS1L2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPR3LXJ4LXKTS1L2sp3PAR2MD3MGF4SALT2lo2bs2j43NZP3NZ13NZ23NZ33SLO3ACL3ACP3SPR3LXJ4LXKT". (* [comment removed for export] *)
  Lemma s4_walk : forall (p : Z) (j4 : list byte) (tfw lw : word) (qtag qpad qlen qpw atag apad alen apw w1 w2 w3 : word)
                         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word) mm,
    rw_cells usegs mm (bv_unsigned sp + -128) [CB 12 j4; C4 tfw] ->
    rw_cells usegs mm (bv_unsigned sp + -112) [C4 qtag; C4 qpad; C8 qlen; C8 qpw] ->
    rw_cells usegs mm (bv_unsigned sp + -88) [C4 atag; C4 apad; C8 alen; C8 apw] ->
    rw_cells usegs mm (bv_unsigned sp + -64) [C8 lw] ->
    rw_cells usegs mm (bv_unsigned sp + -56) [C8 (Z_to_bv 64 p)] ->
    rw_cells usegs mm (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells usegs mm MD [C4 w1] -> rw_cells usegs mm MGF [C4 w2] -> rw_cells usegs mm SALT [C4 w3] ->
    bytes_at usegs mm BUF bs ->
    stk usegs mm lo (bv_unsigned sp + -128) -> munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> statics_ok usegs L mm ->
    BUF <= p -> p <= ENDv ->
    evt usegs POST
      (MS (mkR x1 SPF gp tp x5 x6 x7 (Z_to_bv 64 ENDv) (Z_to_bv 64 p) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x279b4) fc None mm (seg_rom usegs)).
  Proof.
  intros p j4 tfw lw qtag qpad qlen qpw atag apad alen apw w1 w2 w3 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 mm
    F0 FPAR FALG FL FP FS HMD HMGF HSALT HBUF ST MU WM MI SOK Hp0 Hp1.
  open_ctx HC.
  pose proof (bv_unsigned_in_range 64 plen) as PLR.
  unfold bv_modulus in PLR.
  cbn in PLR.
  lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x279dc; 0x27a7c; 0x27bf8; 0x46940] [] 197%N).
  { (* [comment removed for export] *)
    lxp_apply exit_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    (* [comment removed for export] *)
    lxp_gc. try lxp_statics.
    lxp_frame_cut (bv_unsigned sp + -128) [64; 72; 80].
    pose proof U_asn1_get_tag_spec as SP.
    unfold asn1_get_tag_stmt, U_ASN1_GET_TAG in SP.
    callx_sp (bv_unsigned sp + -128)
      (eapply SP with (PP := bv_unsigned sp + -56) (LENP := bv_unsigned sp + -64) (P := p) (END := ENDv) (BUF := BUF) (bs := bs);
      rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by plia; try eassumption; try reflexivity; try plia).
    try clear SP.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -64) [C8 ?lw] |- _ => rename H into FL; rename lw into Lw end.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -56) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into FP; rename qq into q end.
    match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end.
    match goal with H : r = 0 -> _ |- _ => rename H into HL0 end.
    match goal with H : _ < r <= 0 |- _ => rename H into Hr end.
    match goal with H : stk _ _ lo _ |- _ => rename H into ST4 end.
    pose proof (bv_unsigned_in_range 64 Lw) as LR.
    unfold bv_modulus in LR.
    cbn in LR.
    lxp_gc.
    destruct (Z.eq_dec r 0) as [R0|R0].
    2: { assert (RN : r < 0) by lia. clear R0.
      lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x279dc; 0x27a7c; 0x27bf8; 0x46940] [] 197%N).
      all: first [ lxp_at 162428; lxp_apply exit_walk | lxp_at 162268; lxp_apply sel_walk ]. }
    subst r.
    specialize (HL0 eq_refl).
    destruct HL0 as [Hq HqL].
    try clear Hr.
    lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x279dc; 0x27a7c; 0x27bf8; 0x46940] [] 197%N).
    { (* [comment removed for export] *)
      (* [comment removed for export] *)
      lxp_gc. try lxp_statics.
      lxp_frame_cut (bv_unsigned sp + -128) [12; 16; 72; 80].
      pose proof U_asn1_get_int_spec as SPI.
      unfold asn1_get_int_stmt, U_ASN1_GET_INT in SPI.
      callx_sp (bv_unsigned sp + -128)
        (eapply SPI with (PP := bv_unsigned sp + -56) (VALP := bv_unsigned sp + -116) (P := q) (END := q + bv_unsigned Lw) (BUF := BUF) (bs := bs) (lo := lo);
        rewrite ?(unsigned_lit (bv_unsigned sp + -128)) by plia; try eassumption; try reflexivity; try plia).
      try clear SPI.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
      match goal with H : rw_cells _ _ (bv_unsigned sp + -116) [C4 ?tw] |- _ => rename H into F0b end.
      match goal with H : rw_cells _ _ (bv_unsigned sp + -56) [C8 (Z_to_bv 64 ?qq)] |- _ => rename H into FP; rename qq into q2 end.
      match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end.
      match goal with H : _ < r <= 0 |- _ => rename H into Hr end.
      match goal with H : stk _ _ lo _ |- _ => rename H into ST5 end.
      lxp_gc.
      lxp_run (PLAN [0x1e5b8; 0x1e6d0; 0x1edc0; 0x1ef8c; 0x2612c; 0x279dc; 0x27a7c; 0x27bf8; 0x46940] [] 197%N).
      all: first [ lxp_at 162428; lxp_apply exit_walk | lxp_at 162268; lxp_apply sel_walk ].
    }
  }
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
