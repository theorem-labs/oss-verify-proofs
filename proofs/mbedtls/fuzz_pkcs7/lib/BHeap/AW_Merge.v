(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_DepotB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_QPut AW_Enqueue AW_Drain AW_Blist.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
Import AW_Blist.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXAW Require Import LxFlat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P001cf0022b096c28 0 2 1 1 35 1P00ee1468325e971a 0 4 1 1 19 1 22 1 23 1P01416644bd2b6f4b 0 2 0 1 9 1P017e461d69c40f72 0 3 0 1 35 1 38 1P01a3058c836f61af 0 2 0 1 30 1P021495ef31422c32 0 2 0 1 38 1P0216a326c41948b6 0 2 0 1 37 1P027207d182717a20 0 3 0 1 31 1 34 1P0275e80fdd5045b9 0 2 0 1 36 1P028b940749a87ffa 0 2 0 1 38 1P033606b91c1305f4 0 2 0 1 12 1P03aebc9a8b44da09 0 2 1 1 39 1P04401cf072615df5 0 2 0 1 20 1P04b22a9dbd6a6b33 0 2 1 1 35 1P04b4cd799c4e9983 0 2 0 1 12 1P0506dcc6689210d8 0 3 0 1 19 1 21 1P0563e7ebbba06b49 0 3 0 1 31 1 34 1P0651f6aaa58b98cd 0 2 0 1 18 1P0710e0f39b7c0316 0 2 0 1 34 1P07fcae3d38631978 0 4 0 1 19 1 22 1 23 1P07fdb703e6b333ed 0 2 0 1 39 1P0856d5448d2599d8 0 2 0 1 33 1P0928e99a330137e7 0 2 0 1 20 1P0967b9798a7e9633 0 3 0 1 29 1 31 1P09a5c76cad953b83 0 2 1 1 33 1P09bd0edbc2bd5979 0 4 1 1 15 1 17 1 18 1P09ca05d00851a013 0 3 0 1 31 1 32 1P0a3a4cb822534178 0 2 0 1 39 1P0adba866f4c562ee 0 2 0 1 35 1P0afef91ff85152cd 0 3 0 1 19 1 21 1P0b2fbcd596a9f8df 0 2 0 1 19 1P0b8d0b624e288a87 0 2 1 1 33 1P0bcfe136485ac04f 0 2 0 1 3 1P0c8d9fa71957cfe9 0 2 0 1 24 1P0c963e3f88015a50 0 2 1 1 37 1P0cbf2a5b1491557d 0 2 0 1 37 1P0ccb755525a45287 0 2 0 1 34 1P0cea36fa3d92ef95 0 2 0 1 3 1P0cf308ca835aefab 0 3 0 1 32 1 35 1P0d0b8cea80e8806d 0 2 1 1 33 1P0d10801bb276a857 0 2 0 1 16 1P0d8bb31a382b8778 0 2 1 1 37 1P0e262e2bf15eaea8 0 3 0 8192 13 1 26 1P1049c73d8b367a83 0 3 0 1 31 1 34 1P1060a757fe2b64d5 0 2 0 1 5 1P106c564f3f94f00a 0 2 0 1 37 1P107bd7a67fe6f9c1 0 2 0 1 10 1P1106117c90c27e00 0 2 0 1 21 1P1198bd696d9fd78f 0 2 0 1 16 1P125bbb9ff8191106 0 3 0 8192 14 1 27 1P126596ef6389581e 0 3 0 1 35 1 36 1P12931ee5ad91130a 0 2 0 1 19 1P1306673c909e98db 0 3 0 1 35 1 36 1P1396a9976ff2bfc5 0 2 0 1 21 1P14badcbf803a12a7 0 2 0 1 21 1P14c6c84b0be04d7b 0 2 0 1 32 1P15444eea7144d4db 0 2 0 1 17 1P155cf36a4e900b4b 0 2 0 1 10 1P15c64f016f7de4b3 0 2 1 1 39 1P15d3b4dc07303c10 0 2 0 1 36 1P165cf96c3cd706a4 0 2 0 1 36 1P16e7769b2fe3df50 0 3 1 1 21 1 22 1P17b5d535434da10b 0 4 0 1 17 1 23 1 24 1P17e633762f496cd0 0 2 0 1 32 1P17f14b99f8f9e76c 0 2 0 1 30 1P180da9e9cf451d53 0 2 0 1 14 1P18d3f4e83b3daeef 0 2 0 1 34 1P1943543e1a3d41bd 0 2 0 1 19 1P19b496799ba0c7c2 0 3 0 1 35 1 38 1P1a74e13e6d1e0e04 0 3 0 1 31 1 32 1P1af609104ebadf9a 0 2 0 1 34 1P1bd27f618dd42a78 0 2 0 1 38 1P1bd60aa14a1bf135 0 3 0 1 31 1 33 1P1bea73797d71e713 0 2 0 1 22 1P1c22985564a66c8d 0 3 1 1 31 1 32 1P1ce5c48d8dbda403 0 2 0 1 39 1P1e322474b2466b17 0 2 1 1 33 1P1e73d52aaac0c74b 0 2 0 1 21 1P1e78df3395935765 0 2 0 1 16 1P1e79c22c79b70352 0 2 0 1 41 1P1f66b7aef25f5fae 0 2 0 1 22 1P2002bde84b2617c4 0 3 0 1 30 1 35 1P209c021e3d055aca 0 3 0 1 34 1 37 1P20c3d5b1087678e6 0 2 0 1 35 1P211f3d310945a214 0 2 1 1 35 1P2233b212c971de16 0 3 0 1 33 1 34 1P223a551de101fa87 0 3 0 1 35 1 36 1P2256e6e48aaf131f 0 2 0 1 38 1P22c7e0b9c7bf512d 0 2 1 1 37 1P2376b590991730c0 0 4 0 1 15 1 17 1 18 1P25276508e51da264 0 3 0 1 31 1 33 1P25c5a4c030a36c7c 0 3 0 1 37 1 38 1P25ff9dba24d7d826 0 2 0 1 20 1P26405bbaab939d26 0 2 1 1 35 1P2646c002c8f52ac7 0 2 0 1 36 1P267643974ba3fe31 0 2 0 1 32 1P26c247eb37698004 0 3 1 1 31 1 34 1P27a083598cc98811 0 2 0 1 18 1P28d3962af1abc62c 0 2 0 1 21 1P290c1d7b1c343cbc 0 2 0 1 32 1P29255721c7b7890e 0 2 0 1 35 1P2978acb344a88cc8 0 3 0 1 32 1 37 1P298748f0d9a0cea8 0 2 0 1 32 1P29b05f78b46479b3 0 2 0 1 19 1P2a369cccc4664024 0 2 1 1 35 1P2ab32c15f739c2db 0 3 0 1 31 1 32 1P2b16cdec98f0c6c0 0 4 1 1 16 1 22 1 23 1P2b3abe3cfb7e5eed 0 2 0 1 19 1P2bab71c51e42c231 0 2 0 1 13 1P2c6d19bbe4e4149e 0 2 0 1 21 1P2c716eda82dd5dff 0 2 0 1 41 1P2cbc5bbc69bfe4fb 0 2 0 1 12 1P2cc7a92737768466 0 3 0 1 28 1 30 1P2d1c5cdb3a1222c7 0 3 1 1 29 1 31 1P2d3fca962c53db55 0 2 0 1 18 1P2e9ee3bb63cd45a8 0 2 1 1 39 1P2ee7d992d45bc57f 0 2 0 1 33 1P2f6a5a9977d88f74 0 2 0 1 17 1P30625cacc836605f 0 2 0 1 35 1P30fe64985ab3ac38 0 3 1 1 21 1 22 1P3105ca797adc4ac3 0 3 0 8192 14 1 27 1P323774fe50490405 0 2 0 1 17 1P337ba911dbcddebe 0 2 1 1 39 1P3458402606e28af8 0 3 1 1 33 1 36 1P34637f93163ce891 0 2 0 1 20 1P34f33a723c304609 0 3 0 1 20 1 21 1P3568361396ef260d 0 3 0 1 32 1 37 1P356d69762b0955dd 0 2 0 1 32 1P361fd8a9d8c567f6 0 4 0 1 18 1 21 1 22 1P365827bea0ada6b4 0 2 0 1 13 1P36c99759aac37062 0 3 0 1 7 1 9 1P38740c49fc97ac58 0 2 0 1 19 1P38e5e92798c2b6c4 0 3 0 1 30 1 32 1P38ef2dfc58e5843f 0 2 0 1 13 1P39b105f58c8daa4d 0 2 0 1 34 1P39f641165b001fb5 0 3 1 1 33 1 34 1P3a5dbde8bc1fc43f 0 2 0 1 20 1P3a9636639ebdaa83 0 2 0 1 19 1P3b34ba4b86b2f6c8 0 2 0 1 17 1P3be534e8710c85a3 0 3 0 1 35 1 38 1P3c1f59979839cc5d 0 2 0 1 16 1P3c4e963d17791b77 0 2 0 1 11 1P3c6eb0bb0947bc84 0 2 0 1 10 1P3c86ad6dfb403374 0 2 0 1 26 1P3d12a838bcacfeab 0 2 0 1 32 1P3e592cc87eaced1b 0 2 0 1 35 1P3ef51fc0069a3e2c 0 2 0 1 20 1P3f70411f08b921e0 0 3 1 1 21 1 22 1P3fa7195a5dc317e7 0 3 1 1 31 1 33 1N016bff37da63b95eN01b92516abd0c187N024f9333807254edN026b90f234d2739eN037483119634a215N03aef882f0daff6eN04154cf58dd22a13N05b154c78d1e7d70N065210f7db567cc9N06a279f518f09b91N073da315fce3fa42N07cf308d52a6042eN081575369d8c7784N090b941540e250a9N095618f2dffc5310N0a74ecfc735716f6N0aab49aab6f36958N0aef7c3bd000ee3eN0b7d34fdac7c00eaN0b94f6ed17fe522dN0ba56cf70efb94f0N0cc9b084893d31a9N0cd21e9044f5ce4dN0d4d4e22b4126329N0d52fe76012da32fN0df55c6d0ce62465N0e33ff39916180bdN0ed8344dfe0efe6cN0ff373b221cbdfa9N1026c29ed3676acaN10531008e8267c7fN10801a83183b3ce8N1082bb9267433b76N10beef0e34711b08N10f2292b1b999843N1101e55f82b070baN117b59418f41e9a5N12c07193e8b6a137N12dee01458f3d09bN13ed1fc9c64faa2aN142ad4a0724944ffN158ad98aab16597fN180c6b17c30deba8N187f821c116fa338N18bad85b9507d579N18c9e75af801558dN195437b3ce419304N19571bf736164aa7N19effcb9575d7fc1N1ab2c4d89c4c378eN1b2b59d5635b8767N1b9ec55af949e5c5N1bd68980b5e4a52aN1cde716ddcd679e5N1dcf8500f6af8b9fN1e902ff815d6a5acN202aa9370338eab7N20d80941fa2d273eN2109ae6e6f11ea88N2124048887b7f695N2148e09adfaf5db7N217a525c1331ae3aN22033b7d7b2a5621N224d51cad5aebfecN229e8f6a6eda6e51N22fb57daf08a3a4eN235dd754c3fa6276N24be6baefa49644aN24c1627f5ed2d07dN24c58f237666870bN24ef3aa85a26b364N25ec6a827e54e1b2N26280c2045cff541N271974a9f0b31ca6N28bfb1a0b44dc025N28e47e53d55b1e17N2a073423f2d5b0ddN2a1fd2726e9be459N2a918fcf1f72613cN2c821267ae01ee57N2c9de524f7d99882N2db34413b1292122N2dc654538c47e765N2ddb6c9058776884N2e671579eaf48469N2ea00981d216f015N30c8932699c44765N317f66ffa367d068N32796429d60a4518N341ec57edf51c701N34252c24f78bfee6N342d0c1ea22ddd2dN3534c80eeee38baeN3545ae33f4599221N360bf35623aa57d8N37d405d078865062N3839ce43466180f2N38411366eca6a37bN385f009c5da5e33eN38f8df6f6e08bcdaN39defd4d7e179e11N3a6630d5e8531eafN3a709b56235a6a62N3bd4b769ff1231ecN3d3c86a6ae286afeN3d84255cf5441527N3dae865ccc5a5088N3db7a44877314abeN3ea0d719e5effaa2N3eeaf600a33847e1N3eeca21be9ce8feaN3f0fce7f1efbb209"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_Merge () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bnode"; "Stdlib.Sorting.Permutation.Permutation"; "Corelib.Numbers.BinNums.Z"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_addr"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "ARUN_1.xnode"; "Corelib.Init.Datatypes.nil"; "ARUN_1.mnode"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bsum"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv"; "Stdlib.Lists.List.flat_map"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_elems"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_ok"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_size"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bn_count"; "Corelib.Init.Datatypes.prod"; "ARUN_1.mloop"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Lists.ListDef.firstn"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "ARUN_1.A_MB_MID"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "ARUN_1.A_MB_COPY"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "ARUN_1.Merge.bhdr"; "Corelib.Init.Logic.not"; "ARUN_1.Merge.mb_regs"; "ARUN_1.A_MB_HEAD"; "ARUN_1.A_MB_EXIT"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "ARUN_1.A_MB_JOIN"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "ARUN_1.Merge.mb_frame"; "ARUN_1.A_MERGEB"; "ARUN_1.Merge.mb_W"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.hd_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.last_addr"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.blist"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Blist.bwf"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "ARUN_1.Merge.mb_post"; "ARUN_1.merge_out"; "ARUN_1.Merge.merge_post"].

Section ARUN_1. Context {hAR : arun}.
Definition A_MERGEB : Z := 0x49904.          (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_MB_HEAD : Z := 0x4993c.         (* [comment removed for export] *)
Definition A_MB_COPY : Z := 0x49974.         (* [comment removed for export] *)
Definition A_MB_MID : Z := 0x49988.          (* [comment removed for export] *)
Definition A_MB_EXIT : Z := 0x49a20.         (* [comment removed for export] *)

Lemma firstn_snoc : forall (ws : list word) i w, nth_error ws i = Some w -> firstn (S i) ws = firstn i ws ++ [w].
Proof.
  induction ws as [|x ws IH]; intros [|i] w H; cbn in H; try discriminate.
  - injection H. intros ->. reflexivity.
  - cbn [firstn app]. rewrite (IH i w H). reflexivity.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010;L23184456.2000003S1x". (* [comment removed for export] *)
Lemma zbv_subM8192 : forall x, Z_to_bv 64 (x + 18446744073709543424) = Z_to_bv 64 (x - 8192).
Proof.
  intros. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with 18446744073709551616%Z.
  replace (x + 18446744073709543424)%Z with ((x - 8192) + 1 * 18446744073709551616)%Z by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition A_MB_JOIN : Z := 0x49a00.         (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mnode (c x : bnode) : bnode := BN (bn_addr c) (bn_size c + bn_size x - 8192) (bn_elems c ++ bn_elems x).
Definition xnode (x : bnode) : bnode := BN (bn_addr x) 8192 [].

Lemma surg_perm : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pts,(0.$1.)Pdone,(0.$1.)Pc,$1.Px,$1.Prest,(0.$1.)(2.$3.(4.$1.$3.$5.(6.$1.R5.(6.$1.R4.(7.$1.R3.(7.$1.R2.R1.)))))(4.$1.$3.$5.(6.$1.(6.$1.R5.(7.$1.(8.R2.)(9.$1.)))(6.$1.R4.(7.$1.(:.R3.R2.)R1.)))))")
(* [comment removed for export] *).
Proof.
  intros. rewrite <- app_assoc. rewrite !map_app. cbn [map app bn_addr mnode xnode].
  apply Permutation_app_head. apply Permutation_sym.
  replace (map bn_addr done ++ bn_addr c :: map bn_addr rest) with ((map bn_addr done ++ [bn_addr c]) ++ map bn_addr rest) by (rewrite <- app_assoc; reflexivity).
  replace (map bn_addr done ++ bn_addr c :: bn_addr x :: map bn_addr rest) with ((map bn_addr done ++ [bn_addr c]) ++ bn_addr x :: map bn_addr rest) by (rewrite <- app_assoc; reflexivity).
  apply Permutation_middle.
Qed.

Lemma surg_addrs : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pts,(0.$1.)Pdone,(0.$1.)Pc,$1.Px,$1.Prest,(0.$1.)Pb',$1.P,(;.$1.R1.(6.$1.(6.$1.R6.(7.$1.(8.R3.)(9.$1.)))(6.$1.R5.(7.$1.(:.R4.R3.)R2.))))(<.$1.Lb,$1.(=.(;.$1.R1.(6.$1.R8.(6.$1.R7.(7.$1.R6.(7.$1.R5.R4.)))))(>.$3.(5.R3.)(5.R1.))))")
(* [comment removed for export] *).
Proof.
  intros ts done c x rest b' H.
  assert (M : In (bn_addr b') (map bn_addr (ts ++ done ++ c :: x :: rest))).
  { eapply Permutation_in; [apply Permutation_sym; apply surg_perm|]. apply in_map. exact H. }
  apply in_map_iff in M. flat constr:(M) 3%nat. flclear M. intros b E Hb. exists b. split; [exact Hb| symmetry; exact E].
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L40925311832.600000>S2ts4done4rest". (* [comment removed for export] *)
Lemma surg_len : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pts,(0.$1.)Pdone,(0.$1.)Pc,$1.Px,$1.Prest,(0.$1.)(>.$?.(10.$1.(6.$1.(6.$1.R5.(7.$1.(8.R2.)(9.$1.)))(6.$1.R4.(7.$1.(:.R3.R2.)R1.))))(10.$1.(6.$1.R5.(6.$1.R4.(7.$1.R3.(7.$1.R2.R1.))))))")
(* [comment removed for export] *).
Proof. intros. rewrite !app_length. cbn [length]. rewrite ?app_length. cbn [length]. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L2702247627.600000BS2ts4done1c1x4rest". (* [comment removed for export] *)
Lemma surg_bsum : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pts,(0.$1.)Pdone,(0.$1.)Pc,$1.Px,$1.Prest,(0.$1.)(=.(>.$3.(11.(6.$1.R5.(7.$1.(8.R2.)(9.$1.))))(12.(11.R5.)+2000.))(>.$3.(11.(6.$1.R4.(7.$1.(:.R3.R2.)R1.)))(13.(11.(6.$1.R4.(7.$1.R3.(7.$1.R2.R1.))))+2000.)))")
(* [comment removed for export] *).
Proof. intros. rewrite !bsum_app. cbn [bsum xnode mnode bn_size]. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma surg_flat : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pts,(0.$1.)Pdone,(0.$1.)Pc,$1.Px,$1.Prest,(0.$1.)(=.(>.(0.(14.&40.))(15.$1.(14.&40.)$16.(6.$1.R4.(7.$1.(:.R3.R2.)R1.)))(15.$1.(14.&40.)$16.(6.$1.R4.(7.$1.R3.(7.$1.R2.R1.)))))(>.(0.(14.&40.))(15.$1.(14.&40.)$16.(6.$1.R5.(7.$1.(8.R2.)(9.$1.))))(15.$1.(14.&40.)$16.R5.)))")
(* [comment removed for export] *).
Proof. intros. rewrite !flat_map_app. cbn [flat_map mnode xnode bn_elems]. rewrite app_nil_r, <- !app_assoc. split; reflexivity. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L55173687316.7L55667372535.700000F00RS3hAR1c1x2OC2OX2SZ3CNTS3hAR1c1x2OX". (* [comment removed for export] *)
Lemma surg_ok : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pc,$1.Px,$1.P,(17.VhAR,R2.)P,(17.VhAR,R2.)P,(18.(13.(12.(19.R4.)(19.R3.))+2000.)(1:.+2.+3<.))P,(1;.(12.(1<.R5.)(1<.R4.))+3?=.)(=.(17.VhAR,(:.R6.R5.))(17.VhAR,(8.R5.)))")
(* [comment removed for export] *).
Proof.
  intros c x OC OX SZ CNT. unfold bn_ok, bn_count, mnode, xnode in *. cbn [bn_addr bn_size bn_elems length] in *.
  rewrite app_length. split; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint mloop (c : bnode) (rest : list bnode) {struct rest} : list bnode * list bnode :=
  match rest with
  | [] => ([c], [])
  | x :: r => if 1021 <? bn_count c + bn_count x then (c :: fst (mloop x r), snd (mloop x r))
              else (fst (mloop (mnode c x) r), xnode x :: snd (mloop (mnode c x) r))
  end.
Definition merge_out (gs : list bnode) : list bnode * list bnode := match gs with [] => ([], []) | b :: r => mloop b r end.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L4792373173.600000<S1c1x1r1H2H0". (* [comment removed for export] *)
Lemma mloop_big : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pc,$1.Px,$1.Pr,(0.$1.)P,(18.+3?=.(12.(1<.R3.)(1<.R2.)))(>.(1=.(0.$1.)(0.$1.))(1>.R4.(7.$1.R3.R2.))(1?.(0.$1.)(0.$1.)(7.$1.R4.(20.(0.$1.)(0.$1.)(1>.R3.R2.)))(21.(0.$1.)(0.$1.)(1>.R3.R2.))))")
(* [comment removed for export] *).
Proof. intros c x r H. cbn [mloop]. destruct (Z.ltb_spec 1021 (bn_count c + bn_count x)); [reflexivity| lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L42264799957.600000<S1c1x1r1H2H0". (* [comment removed for export] *)
Lemma mloop_fit : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pc,$1.Px,$1.Pr,(0.$1.)P,(1;.(12.(1<.R3.)(1<.R2.))+3?=.)(>.(1=.(0.$1.)(0.$1.))(1>.R4.(7.$1.R3.R2.))(1?.(0.$1.)(0.$1.)(20.(0.$1.)(0.$1.)(1>.(:.R4.R3.)R2.))(7.$1.(8.R3.)(21.(0.$1.)(0.$1.)(1>.(:.R4.R3.)R2.)))))")
(* [comment removed for export] *).
Proof. intros c x r H. cbn [mloop]. destruct (Z.ltb_spec 1021 (bn_count c + bn_count x)); [lia| reflexivity]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Merge.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition mb_regs (SP : Z) (ra gp tp t1 t2 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (P ext cur nx : Z) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "(22.O1:.(23.&40.(12.O1;.-10.))O19.O18.(23.&40.O1.)O17.O16.O15.O14.(23.&40.(12.$24.+378.))(23.&40.O4.)(23.&40.O3.)O13.(23.&40.O2.)(23.&40.+3?=.)(23.&40.+????????????>000.)(23.&40.+2000.)O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L10353725385.69L14403128707.12L16901775916.69L17290936988.12L17918598832.62L19022916715.12L2395258393.70 L24463925918.3 L26079606249.72L29335386990.70L29335386990.71L29858120756.69L31254075438.69L35778571161.5 L36192008061.2 L36840904511.4 L39332637397.0 L41974174763.73L49698585326.72L49702774835.70L49768407454.3 L53022103785.68L60505815499.7 L6116201822.7  L63907500555.5 L68375765817.69L8931259039.69 L952571003.3   00000O00e01G01]03i04704`04n05^06D06j07M08008C08I08X08Y08Z09A09h0:60<H0<]0=20=A0=e0>Q0>YS3hAR1k1i1n6celems2ws2Hk2Hi3LWSS3hAR1k1i2nx1n2Hk2Hi1KS3hAR1k1i2nx1n6celems2ws2Hk2Hi3LWSS3hAR1k1i2nx1n2Hk2Hi1KS3hAR2AL2CS1i2ra2sp2gp2tp2t02t12s02s12a02a12a22a32a42a52a62a72s22s32s42s52s62s72s82s93s103s112t52t61F2fc2m01m3cur2nx1n6celems2ws1W2Hk2Hi3LWSS3hAR1k1i1n2HkS3hAR1k1i3cur1n6celems2ws1W2Hk2Hi3LWS3CAPS1i3cur6celemsS3hAR1k1i3cur2nx1n6celems2ws2Hk2Hi3LWS3CAP3SEP1wS3hAR1k1i3cur1n6celems2ws2Hk2Hi3LWS2C0S3hAR1k1i3cur1n6celems2ws2Hk2Hi3LWS2C0S3hAR1k1i3cur1n6celems2ws2Hk2Hi3LWSS3hAR1k1i2nx1n6celems2ws2Hk3LWS3CAPS1i3cur1n6celems2HiS1i2nxS1i1n6celems2HiSFS3hAR1k1i3cur1n6celems2ws2Hk3LWS3CAP2C1S3hAR1k1i3cur1n6celems2ws2Hk3LWS3CAP2C1S1i3cur6celemsS3hAR2AL2CS1k1i2ra2sp2gp2tp2t02t12s02s12a02a12a22a32a42a52a62a72s22s32s42s52s62s72s82s93s103s112t52t61F2fc2m01m3cur2nx1n6celems2ws1W2Hk2Hi3LWS3NTHS1k1i1n6celems2Hk3CAPS1k1i1n6celems2Hk3CAPS1i1n2ws2Hi3LWSS3hAR1k1i3cur1n6celems2ws2Hk3LWS3CAPS3hAR1k1i2nx1n6celems2ws2Hk2Hi3LWS3CAP2N02N1S1i1n2Hi". (* [comment removed for export] *)
  Lemma mb_copy : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pk,$?.Pi,$3.Pra,(14.&40.)Psp,(14.&40.)Pgp,(14.&40.)Ptp,(14.&40.)Pt0,(14.&40.)Pt1,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa0,(14.&40.)Pa1,(14.&40.)Pa2,(14.&40.)Pa3,(14.&40.)Pa4,(14.&40.)Pa5,(14.&40.)Pa6,(14.&40.)Pa7,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)PF,(25.&5.(14.&40.))Pfc,(14.&20.)Pm0,P,(14.&40.)(26.(14.&8.))Pm,P,(14.&40.)(26.(14.&8.))Pcur,$3.Pnx,$3.Pn,$3.Pcelems,(0.(14.&40.))Pws,(0.(14.&40.))PW,(0.(1=.$3.$3.))P,(>.$3.(12.R27.(27.R28.))R4.)P,(=.(1;.=R28.)(18.R28.R5.))P,(>.$?.(10.(14.&40.)R4.)(28.R6.))P,(1;.(12.+18.(29.+8.(12.(27.(10.(14.&40.)R6.))R7.)))+2000.)P,(1;.+65?000.R:.)P,(1;.(12.R;.+2000.)(2:.VhAR,))P,(1;.+65?000.R;.)P,(1;.(12.R<.+2000.)(2:.VhAR,))P,(2;.(1;.(12.R>.+2000.)R=.)(1;.(12.R=.+2000.)R>.))P,(2<.VCS,R?.+2000.)P,(2<.VCS,R?.+2000.)P,(2=.$2>.R12.(12.R10.+18.)R=.)P,(2=.$2>.R13.(12.R12.+18.)(6.(14.&40.)R?.(2?.(14.&40.)(28.R33.)R>.)))P,(30.$2>.R14.R13.+2000.)P,(31.(7.(1=.$3.$3.)(1?.$3.$3.(12.R14.+18.)(12.R14.+2000.))R?.)R16.R15.)P,(32.$2>.R17.R16.)P,(33.$2>.R17.)(34.$2>.VAL,VCS,Lms',$35.(<.(14.&40.)Lx30,(14.&40.)(<.P,(14.&40.)(26.(14.&8.))Lm',P,(14.&40.)(26.(14.&8.))(=.(>.$35.R3.(36.(22.R3:.R39.R38.R37.R36.R35.(23.&40.(12.(12.R19.+18.)(29.+8.R18.)))R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.(23.&40.(12.(12.R1:.+18.)(29.+8.(12.(27.(10.(14.&40.)R17.))R18.))))(23.&40.(12.(12.R19.+18.)(29.+8.R18.)))R2.R1?.)R1>.(23.&40.$37.)R1=.(38.(14.&40.))R1.(39.$2>.)))(=.(31.(7.(1=.$3.$3.)(1?.$3.$3.(12.R1:.+18.)(12.R1:.+2000.))R15.)R1<.R1.)(=.(32.$2>.R1<.R1.)(=.(33.$2>.R1.)(=.(2=.$2>.R1.(12.R19.+18.)R16.)(=.(2=.$2>.R1.(12.R1:.+18.)(6.(14.&40.)R17.R16.))(30.$2>.R1.R1:.+2000.)))))))))(36.(22.R37.R36.R35.R34.R33.R32.(23.&40.(12.(12.R16.+18.)(29.+8.R38.)))R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.(23.&40.(12.(12.R17.+18.)(29.+8.(12.(27.(10.(14.&40.)R14.))R38.))))(23.&40.(12.(12.R16.+18.)(29.+8.R15.)))R1=.R1<.)R1;.(23.&40.$3:.)R1:.(38.(14.&40.))R18.(39.$2>.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m0 m cur nx n celems ws W
      Hk Hi LWS CAP C0 C1 N0 N1 SEP CCS NCS HS HD BW MU WM MI; [lia|].
    facts. unfold A_MB_COPY, A_MB_MID in *.
    destruct (nth_error ws (Z.to_nat i)) as [w|] eqn:NTH; [| apply nth_error_None in NTH; lia].
    pose proof (u64arr_read asegs m (nx + 24) ws i w _ HS NTH ltac:(lia) eq_refl) as RD.
    (* [comment removed for export] *)
    zstep. clear RD. zstep.
    (* [comment removed for export] *)
    pose proof (wr_at_store_ok asegs _ cur 8192 (24 + 8 * (Z.of_nat (length celems) + i)) 8 BW ltac:(clear -Hi; lia) ltac:(clear -Hi Hk CAP; cbn; lia)) as SOK.
    replace (cur + (24 + 8 * (Z.of_nat (length celems) + i))) with (cur + 24 + 8 * (Z.of_nat (length celems) + i)) in SOK by (clear; lia).
    zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx ?a ?bs) _) =>
      pose proof (u64arr_append mx (cur + 24) (celems ++ firstn (Z.to_nat i) ws) w HD) as HD';
      rewrite app_length, firstn_length, (Nat.min_l (Z.to_nat i) (length ws)) in HD' by (clear -Hi LWS; lia);
      replace (cur + 24 + 8 * Z.of_nat (length celems + Z.to_nat i)) with (cur + 24 + 8 * (Z.of_nat (length celems) + i)) in HD' by (clear -Hi; lia);
      pose proof (wr_at_sub mx cur 8192 (24 + 8 * (Z.of_nat (length celems) + i)) 8 BW ltac:(clear -Hi; lia) ltac:(clear; lia) ltac:(clear -Hi Hk CAP; lia)) as W8;
      replace (cur + (24 + 8 * (Z.of_nat (length celems) + i))) with (cur + 24 + 8 * (Z.of_nat (length celems) + i)) in W8 by (clear; lia);
      specialize (HD' W8); clear W8
    end.
    store_done. try clear HD. rename HD' into HD.
    rewrite <- app_assoc, <- (firstn_snoc ws (Z.to_nat i) w NTH) in HD. replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in HD by (clear -Hi; lia).
    (* [comment removed for export] *)
    zstep. replace (cur + 24 + 8 * (Z.of_nat (length celems) + i) + 8) with (cur + 24 + 8 * (Z.of_nat (length celems) + (i + 1))) by (clear; lia).
    replace (nx + 24 + 8 * i + 8) with (nx + 24 + 8 * (i + 1)) by (clear; lia).
    zstep. if_cases K; zify_cond K.
    - eapply (IH (i + 1)); try eassumption; clear -Hk Hi K C0 N0 N1; lia.
    - assert (EN : i + 1 = n) by (clear - K Hi Hk C0 N0 N1; lia).
      rewrite EN in *. rewrite <- LWS, firstn_all in HD. apply evtA_done. do 2 eexists.
      split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition bhdr (nx sz cnt : Z) : list cell := [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 cnt)].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L13587678822.50L15168693734.5000000@00LS3hAR3nxn3NXB2H1S3hAR3nxn2H1". (* [comment removed for export] *)
  Lemma mb_nomerge : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pra,(14.&40.)Pgp,(14.&40.)Ptp,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa3,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)PSP,$3.PP,$3.Pext,$3.Pcur,$3.Pnx,$3.Pnxn,$3.Pcsz,$3.Pccnt,$3.Pnsz,$3.Pncnt,$3.PF,(25.&5.(14.&40.))Pfc,(14.&20.)Pm,P,(14.&40.)(26.(14.&8.))P,(1;.+65?000.R:.)P,(1;.(12.R;.+2000.)(2:.VhAR,))P,(1;.+65?000.R;.)P,(1;.(12.R<.+2000.)(2:.VhAR,))P,(=.(1;.=R:.)(1;.R:.+3?=.))P,(=.(1;.=R9.)(1;.R9.+3?=.))P,(18.+3?=.(12.R<.R:.))P,(=.(1;.=R?.)(18.R?.(1:.+2.+40.)))P,(3;.$2>.R9.R12.(3<.R11.R?.R>.))P,(3;.$2>.R:.R12.(3<.R11.R>.R=.))P,(2<.VCS,R14.+2000.)P,(2<.VCS,R14.+2000.)P,(33.$2>.R=.)(34.$2>.VAL,VCS,Lms',$35.(<.(14.&40.)Lx6,(14.&40.)(<.(14.&40.)Lx28,(14.&40.)(<.(14.&40.)Lx29,(14.&40.)(2;.(=.(3=.(>.$3.R19.=))(>.$35.R4.(36.(3>.R1>.R34.R33.R32.R3.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R2.R1.R20.R1?.R1=.R1<.R1:.R19.)R14.(23.&40.$3?.)R13.(38.(14.&40.))R12.(39.$2>.))))(=.(>.$3.R19.=)(>.$35.R4.(36.(3>.R1>.R34.R33.R32.R3.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R2.R1.R20.R1?.R1=.R1<.R1:.R19.)R14.(23.&40.$40.)R13.(38.(14.&40.))R12.(39.$2>.))))))))(36.(3>.R1:.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R19.R18.R17.R16.)R10.(23.&40.$3?.)R?.(38.(14.&40.))R>.(39.$2>.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t1 t2 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP P ext cur nx nxn csz ccnt nsz ncnt F fc m
      C0 C1 N0 N1 CCB NCB SUM NXB HC HN CCS NCS MI.
    unfold mb_regs, bhdr in *. unfold A_MB_HEAD, A_MB_EXIT, A_INSTANCE in *.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    lx_run (PLAN [A_MB_HEAD; A_MB_EXIT] [] 20%N).
    all: subst lxm; apply evtA_done; do 3 eexists.
    all: first [ left; split; [lx_arith| lx_mseq] | right; split; [lx_arith| lx_mseq] ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L10544317660.56L12700802836.18L20075077474.17L22212526935.17L23189023613.2 L23913305065.3 L27737344424.56L46781010622.5 L57829139081.1 L58956172214.2 L59308634630.4 L62822527476.1 L8294462878.17 L9565101882.4  00000X00Y01A01j02302?02c03<03A03L03\03`04E04ZS3hAR4ccnt4ncnt6celems2ws3NC03LCE3LWS2H3FS3hAR4ccnt4ncnt6celems2ws3NC03LCE3LWS2KcS3hAR4ccnt4ncnt6celems2ws3CC03SUM3LCE3LWSS2nx4ncntS3cur2nx3SEPS3hAR4ccnt4ncnt6celems2ws3LCE3LWS2H3S3cur4ccnt6celems3CC03LCES3curS4ccnt4ncntS4ncnt2ws3LWS2KcS2nxS3hAR4ccnt4ncnt6celems2ws3NC03LCE3LWSS4ccnt6celems3CC03LCE". (* [comment removed for export] *)
  Lemma mb_merge_A : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pra,(14.&40.)Pgp,(14.&40.)Ptp,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa3,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)PSP,$3.PP,$3.Pext,$3.Pcur,$3.Pnx,$3.Pnxn,$3.Pcsz,$3.Pccnt,$3.Pnsz,$3.Pncnt,$3.Pcelems,(0.(14.&40.))Pws,(0.(14.&40.))PF,(25.&5.(14.&40.))Pfc,(14.&20.)Pm,P,(14.&40.)(26.(14.&8.))P,(1;.+65?000.R<.)P,(1;.(12.R=.+2000.)(2:.VhAR,))P,(1;.+65?000.R=.)P,(1;.(12.R>.+2000.)(2:.VhAR,))P,(2;.(1;.(12.R10.+2000.)R?.)(1;.(12.R?.+2000.)R10.))P,(1;.=R=.)P,(1;.=R<.)P,(1;.(12.R?.R=.)+3?=.)P,(=.(1;.+2000.R11.)(18.R11.(1:.+2.+3<.)))P,(>.$?.(10.(14.&40.)R>.)(28.R11.))P,(>.$?.(10.(14.&40.)R>.)(28.R10.))P,(3;.$2>.R<.R17.(3<.R16.R14.R13.))P,(3;.$2>.R=.R17.(3<.R16.R13.R12.))P,(2<.VCS,R19.+2000.)P,(2<.VCS,R19.+2000.)P,(2=.$2>.R10.(12.R1;.+18.)R14.)P,(2=.$2>.R11.(12.R1;.+18.)R14.)P,(30.$2>.R12.R1=.+2000.)P,(33.$2>.R13.)(34.$2>.VAL,VCS,Lms',$35.(<.(14.&40.)Lx7,(14.&40.)(<.(14.&40.)Lx28,(14.&40.)(<.(14.&40.)Lx29,(14.&40.)(<.(14.&40.)Lx30,(14.&40.)(<.P,(14.&40.)(26.(14.&8.))Lm',P,(14.&40.)(26.(14.&8.))(=.(>.$35.R6.(36.(22.R3>.(23.&40.(12.R28.-10.))R3=.R3<.(23.&40.R24.)(23.&40.(12.R21.R1?.))R5.R39.R38.(23.&40.(12.$24.+378.))(23.&40.R27.)(23.&40.R26.)(23.&40.R22.)(23.&40.R25.)(23.&40.+3?=.)(23.&40.+????????????>000.)(23.&40.+2000.)R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R4.R3.R2.R29.)R1<.(23.&40.$37.)R1;.(38.(14.&40.))R1.(39.$2>.)))(=.(31.(7.(1=.$3.$3.)(1?.$3.$3.(12.R25.+18.)(12.R25.+2000.))(9.(1=.$3.$3.)))R1:.R1.)(=.(32.$2>.R1:.R1.)(=.(33.$2>.R1.)(=.(3;.$2>.R1.R25.(3<.R24.R22.R21.))(=.(3;.$2>.R1.R24.(3<.R23.R20.R1?.))(=.(2=.$2>.R1.(12.R25.+18.)(6.(14.&40.)R1>.R1=.))(=.(2=.$2>.R1.(12.R24.+18.)R1=.)(30.$2>.R1.R25.+2000.))))))))))))))(36.(3>.R22.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R21.R20.R1?.R1>.)R16.(23.&40.$3?.)R15.(38.(14.&40.))R14.(39.$2>.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t1 t2 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP P ext cur nx nxn csz ccnt nsz ncnt celems ws F fc m
      C0 C1 N0 N1 SEP CC0 NC0 SUM CSZ LCE LWS HC HN CCS NCS HD HS BW MI.
    unfold mb_regs, bhdr in *. unfold A_MB_HEAD, A_MB_MID, A_INSTANCE in *.
    pose proof (munch_refl [(cur + 24, cur + 8192)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    set (cws := celems ++ ws).
    (* [comment removed for export] *)
    lx_run (PLAN [A_MB_MID; A_MB_COPY] [] 20%N).
    all: lx_deads.
    - (* [comment removed for export] *)
      subst lxm cws.
      assert (Kc : ncnt = 0) by lx_arith.
      assert (ws = []) as -> by (destruct ws; [reflexivity| cbn in LWS; exfalso; clear -LWS Kc; lia]). rewrite app_nil_r.
      apply evtA_done. lx_exs. lx_ands; [> rewrite Kc, Z.add_0_r; lx_mseq | assumption .. ].
    - subst lxm cws.
      assert (Kc : ncnt <> 0) by lx_arith.
      replace (cur + (8 * ccnt + 24)) with (cur + 24 + 8 * (Z.of_nat (length celems) + 0)) by (clear -LCE CC0; lia).
      replace (nx + (8 * ncnt + 24)) with (nx + 24 + 8 * ncnt) by (clear; lia).
      replace (nx + 24) with (nx + 24 + 8 * 0) at 1 by (clear; lia).
      eapply evtA_mono.
      { eapply (mb_copy (Z.to_nat ncnt) 0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m m cur nx ncnt celems ws []);
          try eassumption; try (clear -Kc NC0 SUM LCE LWS C0 C1 N0 N1 CC0; lia).
        cbn [Z.to_nat firstn]. rewrite app_nil_r. exact HD. }
      cbv beta. intros ms' (x30 & m' & -> & MU' & WM' & MI' & HS' & HD' & BW').
      do 5 eexists. split; [replace (Z.of_nat (length celems)) with ccnt by (clear -LCE CC0; lia); replace (ncnt + ccnt) with (ccnt + ncnt) by (clear; lia); reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|].
      split. { eapply rw_cells_transport; [exact HC| exact MU'| exact WM'| cbn; clear; lia]. }
      split. { eapply rw_cells_transport; [exact HN| exact MU'| exact WM'| cbn; clear -SEP; lia]. }
      split; [exact HD'|]. split; [exact HS'| exact BW'].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mb_Wb (P cur nx tlen TL : Z) : list (Z * Z) :=
    (A_INSTANCE + 888, A_INSTANCE + 920) :: (P, P + 32) :: (cur, cur + 24) :: (nx, nx + 24) :: (if tlen =? 0 then [] else [(TL, TL + 8)]).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L15919221662.83L15919221662.84L15919221662.93L15919221662.94L20866702127.64L20866702127.69L34620732896.3 L45168044003.66L45168044003.71L62301138302.83L62301138302.84L62301138302.93L62301138302.9400000E00Z00o01D01[02202?02P02a02b02c02d02eS3hAR3csz3nsz3CSZ3NSZS3hAR3csz3nsz3CSZ3NSZS3hAR3csz3nsz3CSZ3NSZS3hAR3csz3nsz3CSZ3NSZS3hAR2nx2GL2N03GLL4LXKFS3hAR2nx2GL2N03GLL4LXKFS4tlen3TLB2T0S3hAR2nx2GL2H42H5S3hAR2nx2GL2H52H6FFFF". (* [comment removed for export] *)
  Lemma mb_merge_B1 : forall
      (ra gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (gf tf tlw : word)
      (SP P ext cur nx nxn csz ccnt newcnt nsz ncnt glen GL gb tlen TL tb : Z) (F : bvmap 5 word) (fc : bv 32) (m : mem) (Wb : list (Z * Z)),
      Wb = mb_Wb P cur nx tlen TL ->
      0x65f000 <= cur -> cur + 8192 <= ACEIL -> 0x65f000 <= nx -> nx + 8192 <= ACEIL ->
      (cur + 8192 <= nx \/ nx + 8192 <= cur) -> ACEIL <= P -> P + 32 <= 2^62 ->
      0 <= newcnt < 2^64 -> 8192 <= csz < 2^60 -> 8192 <= nsz < 2^60 -> 1 <= glen < 2^63 -> 0 <= GL < 2^64 -> 0 <= nxn < 2^64 ->
      0 <= tlen < 2^62 -> 0 <= TL < 2^64 ->
      rw_cells asegs m cur (bhdr nx csz ccnt) -> rw_cells asegs m nx (bhdr nxn nsz ncnt) -> crange CS cur 8192 -> crange CS nx 8192 ->
      rw_cells asegs m (A_INSTANCE + 888) [C8 (Z_to_bv 64 glen); C8 gf; C8 (Z_to_bv 64 GL); C8 (Z_to_bv 64 gb)] ->
      rw_cells asegs m P [C8 (Z_to_bv 64 tlen); C8 tf; C8 (Z_to_bv 64 TL); C8 (Z_to_bv 64 tb)] -> crange CS P 32 ->
      (tlen <> 0 -> rw_cells asegs m TL [C8 tlw] /\ crange CS TL 8 /\ 0x65f000 <= TL /\ TL + 8192 <= ACEIL
                    /\ (TL + 8192 <= cur \/ cur + 8192 <= TL) /\ (TL + 8192 <= nx \/ nx + 8192 <= TL)) ->
      mem_inv asegs m ->
      evtA asegs AL CS
        (fun ms' => exists (m' : mem) (x6 x7 : word),
           munch Wb m m' /\ wmono asegs m m' /\ mem_inv asegs m'
           /\ rw_cells asegs m' cur (bhdr nxn (csz + nsz - 8192) newcnt) /\ rw_cells asegs m' nx (bhdr 0 8192 0)
           /\ rw_cells asegs m' (A_INSTANCE + 888) [C8 (Z_to_bv 64 (glen - 1)); C8 gf; C8 (Z_to_bv 64 (if GL =? nx then cur else GL)); C8 (Z_to_bv 64 gb)]
           /\ rw_cells asegs m' P [C8 (Z_to_bv 64 tlen); C8 (if tlen =? 0 then Z_to_bv 64 nx else tf); C8 (Z_to_bv 64 TL); C8 (Z_to_bv 64 tb)]
           /\ (tlen <> 0 -> rw_cells asegs m' TL [C8 (Z_to_bv 64 nx)])
           /\ ms' = MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp (Z_to_bv 64 nx) x6 x7 s0 s1
                        (Z_to_bv 64 (A_INSTANCE + 888)) (Z_to_bv 64 P) (Z_to_bv 64 ext) (Z_to_bv 64 (tlen + 1))
                        (Z_to_bv 64 cur) (Z_to_bv 64 1021) (Z_to_bv 64 18446744073709543424) (Z_to_bv 64 8192)
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_MB_JOIN) fc None m' (seg_rom asegs))
        (MS (mkR ra (Z_to_bv 64 (SP + -16)) gp tp (Z_to_bv 64 nx) (Z_to_bv 64 newcnt) t2 s0 s1
                 (Z_to_bv 64 (A_INSTANCE + 888)) (Z_to_bv 64 P) (Z_to_bv 64 ext) (Z_to_bv 64 csz)
                 (Z_to_bv 64 cur) (Z_to_bv 64 1021) (Z_to_bv 64 18446744073709543424) (Z_to_bv 64 8192)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_MB_MID) fc None m (seg_rom asegs)).
  Proof.
    intros ra gp tp t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gf tf tlw SP P ext cur nx nxn csz ccnt newcnt nsz ncnt glen GL gb tlen TL tb F fc m Wb
      HWb C0 C1 N0 N1 SEP P0 P1 NCB CSZ NSZ GLB GLL NXB TLB TLR HC HN CCS NCS QG TMP PCS TLAST MI.
    unfold bhdr, mb_Wb in *. unfold A_MB_MID, A_MB_JOIN, A_INSTANCE in *.
    change (1074072 + 888) with 1074960 in *. change (1074072 + 920) with 1074992 in *.
    pose proof (wmono_refl asegs m) as WM. lx_aceil.
    destruct (Z.eq_dec tlen 0) as [T0|T0].
    - clear TLAST. rewrite T0 in HWb. cbn [Z.eqb] in HWb. subst Wb.
      pose proof (munch_refl [(1074960, 1074992); (P, P + 32); (cur, cur + 24); (nx, nx + 24)] m) as MU.
      subst tlen.
      (* [comment removed for export] *)
      lx_run (PLAN [A_MB_JOIN] [] 40%N).
    + (* [comment removed for export] *)
      assert (Kl : GL = nx) by lx_arith.
      apply evtA_done. cbn [Z.eqb Z.add]. rewrite (proj2 (Z.eqb_eq GL nx) Kl).
      lx_exs; lx_ands; [> | | | | | | | intros X; exfalso; exact (X eq_refl) | lx_mseq];
        [ assumption .. | | | | ]; match goal with |- rw_cells _ lxm ?a _ => match goal with K : rw_cells _ lxm a _ |- _ => lx_rwx K end end.
    + assert (Kl : GL <> nx) by lx_arith.
      apply evtA_done. cbn [Z.eqb Z.add]. replace (GL =? nx) with false by (symmetry; apply Z.eqb_neq; exact Kl).
      lx_exs; lx_ands; [> | | | | | | | intros X; exfalso; exact (X eq_refl) | lx_mseq];
        [ assumption .. | | | | ]; match goal with |- rw_cells _ lxm ?a _ => match goal with K : rw_cells _ lxm a _ |- _ => lx_rwx K end end.
    - replace (tlen =? 0) with false in HWb by (symmetry; apply Z.eqb_neq; exact T0). subst Wb.
      flat constr:((TLAST T0)) 6%nat. intros TLC TLCS TL0 TL1 TLSC TLSN. clear TLAST.
      pose proof (munch_refl [(1074960, 1074992); (P, P + 32); (cur, cur + 24); (nx, nx + 24); (TL, TL + 8)] m) as MU.
      assert (TP : 0 < tlen) by (clear -T0 TLB; lia).
      (* [comment removed for export] *)
      lx_run (PLAN [A_MB_JOIN] [] 40%N).
      + assert (Kl : GL = nx) by lx_arith.
        apply evtA_done. rewrite (proj2 (Z.eqb_eq GL nx) Kl). replace (tlen =? 0) with false by (symmetry; apply Z.eqb_neq; exact T0).
        lx_exs; lx_ands; [> | | | | | | | intros _ | lx_mseq];
          [ assumption .. | | | | | ]; match goal with |- rw_cells _ lxm ?a _ => match goal with K : rw_cells _ lxm a _ |- _ => lx_rwx K end end.
      + assert (Kl : GL <> nx) by lx_arith.
        apply evtA_done. replace (GL =? nx) with false by (symmetry; apply Z.eqb_neq; exact Kl). replace (tlen =? 0) with false by (symmetry; apply Z.eqb_neq; exact T0).
        lx_exs; lx_ands; [> | | | | | | | intros _ | lx_mseq];
          [ assumption .. | | | | | ]; match goal with |- rw_cells _ lxm ?a _ => match goal with K : rw_cells _ lxm a _ |- _ => lx_rwx K end end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L13587679205.57L15168693349.5700000@00LS3hAR3nxn3NXB2H2S3hAR3nxn2H2". (* [comment removed for export] *)
  Lemma mb_merge_B2 : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pra,(14.&40.)Pgp,(14.&40.)Ptp,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)Ptf',(14.&40.)Ptl0,(14.&40.)Ptl2,(14.&40.)PSP,$3.PP,$3.Pext,$3.Pcur,$3.Pnx,$3.Pnxn,$3.Psz,$3.Pcnt,$3.Ptlen',$3.Ptb,$3.PF,(25.&5.(14.&40.))Pfc,(14.&20.)Pm,P,(14.&40.)(26.(14.&8.))P,(1;.+65?000.R:.)P,(1;.(12.R;.+2000.)(2:.VhAR,))P,(1;.(2:.VhAR,)R>.)P,(1;.(12.R?.+20.)(1:.+2.+3>.))P,(=.(1;.=R=.)(18.R=.(1:.+2.+40.)))P,(=.(1;.=R=.)(18.R=.(1:.+2.+40.)))P,(=.(1;.=R;.)(18.R;.(1:.+2.+40.)))P,(1;.=R;.)P,(18.(12.R<.+2000.)(1:.+2.+3?.))P,(1;.=R14.)P,(18.(12.R15.+2000.)(1:.+2.+3?.))P,(3;.$2>.R<.R15.(3<.R13.R12.R11.))P,(2<.VCS,R16.+2000.)P,(3;.$2>.R>.R19.(7.$41.(42.R1<.)(7.$41.(42.R1=.)(7.$41.(42.R1;.)(7.$41.(42.(23.&40.R11.))(9.$41.))))))P,(2<.VCS,R1:.+20.)P,(33.$2>.R10.)(34.$2>.VAL,VCS,Lms',$35.(<.P,(14.&40.)(26.(14.&8.))Lm',P,(14.&40.)(26.(14.&8.))(<.(14.&40.)Lx13,(14.&40.)(=.(31.(7.(1=.$3.$3.)(1?.$3.$3.R1?.(12.R1?.+20.))(9.(1=.$3.$3.)))R14.R2.)(=.(32.$2>.R14.R2.)(=.(33.$2>.R2.)(=.(3;.$2>.R2.R1?.(7.$41.(42.(23.&40.R18.))(7.$41.(42.R23.)(7.$41.(42.(23.&40.R1<.))(7.$41.(42.(23.&40.(12.R17.+2000.)))(9.$41.))))))(2;.(=.(3=.(>.$3.R1;.=))(>.$35.R3.(36.(3>.R20.R38.R37.R36.R35.R34.R33.R32.R1.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1?.(12.R1>.+2000.)R1=.R1;.)R16.(23.&40.$3?.)R15.(38.(14.&40.))R2.(39.$2>.))))(=.(>.$3.R1;.=)(>.$35.R3.(36.(3>.R20.R38.R37.R36.R35.R34.R33.R32.R1.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1?.(12.R1>.+2000.)R1=.R1;.)R16.(23.&40.$40.)R15.(38.(14.&40.))R2.(39.$2>.)))))))))))(36.(22.R35.(23.&40.(12.R1=.-10.))R34.R33.(23.&40.R19.)R32.R31.R30.R2?.(23.&40.(12.$24.+378.))(23.&40.R1<.)(23.&40.R1;.)(23.&40.R15.)(23.&40.R1:.)(23.&40.+3?=.)(23.&40.+????????????>000.)(23.&40.+2000.)R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R13.(23.&40.$43.)R12.(38.(14.&40.))R11.(39.$2>.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 tf' tl0 tl2 SP P ext cur nx nxn sz cnt tlen' tb F fc m
      C0 C1 P0 P1 NXR NXB TLB TB0 TB1 E0 E1 HC CCS TMP PCS MI.
    unfold bhdr, mb_regs in *. unfold A_MB_JOIN, A_MB_HEAD, A_MB_EXIT, A_INSTANCE in *.
    change (1074072 + 888) with 1074960 in *.
    pose proof (munch_refl [(P, P + 32)] m) as MU. pose proof (wmono_refl asegs m) as WM. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [A_MB_HEAD; A_MB_EXIT] [] 20%N).
    all: apply evtA_done; lx_exs; lx_ands;
         [> | | | | first [ left; split; [lx_arith| lx_mseq] | right; split; [lx_arith| lx_mseq] ] ]; [assumption .. | ];
         match goal with |- rw_cells _ ?mx ?a _ => match goal with K : rw_cells _ mx a _ |- _ => lx_rwx K end end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mb_frame (m : mem) (SP : Z) (j : list byte) (ra : word) : Prop := rw_cells asegs m (SP + -16) [CB 8 j; C8 ra].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L19567670979.60L19567670979.61L20239957767.61L25083598744.1 L40522939758.1 L42122450195.76L43185854564.6000000@00A00M00Q00U00]00lS3hAR3fnx3FNB2H3FS3hAR3fnx2H4S2SPS2SPS3hAR2SPS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  Lemma mb_entry : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pra,(14.&40.)Pgp,(14.&40.)Ptp,(14.&40.)Pt0,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa2,(14.&40.)Pa3,(14.&40.)Pa4,(14.&40.)Pa5,(14.&40.)Pa6,(14.&40.)Pa7,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)Pgl,(14.&40.)PSP,$3.PP,$3.Pglen,$3.Pgfirst,$3.Pgb,$3.Pfnx,$3.Pfsz,$3.Pfcnt,$3.Plo,$3.PF,(25.&5.(14.&40.))Pfc,(14.&20.)Pm,P,(14.&40.)(26.(14.&8.))P,(=.(1;.=R9.)(18.R9.(1:.+2.+40.)))P,(=.(1;.=R9.)(18.R9.(1:.+2.+40.)))P,(=.(1;.=R=.)(18.R=.(1:.+2.+40.)))P,(3;.$2>.R4.(12.$24.+378.)(7.$41.(42.(23.&40.R=.))(7.$41.(42.(23.&40.R<.))(7.$41.(42.R10.)(7.$41.(42.(23.&40.R;.))(9.$41.))))))P,P,(3=.(>.$3.R=.=))(=.(3;.$2>.R6.R>.(3<.R<.R;.R:.))(=.(2<.VCS,R>.+2000.)(=.(1;.+65?000.R>.)(=.(1;.(12.R>.+2000.)(2:.VhAR,))(=.(1;.=R<.)(18.R<.(1:.+2.+40.)))))))P,(44.$2>.R6.R9.R11.)P,(1;.(2:.VhAR,)R:.)P,(1;.R;.(13.R13.+10.))P,(1;.R14.(1:.+2.+3>.))P,(2<.VCS,R=.(13.R15.R=.))P,(33.$2>.R;.)(34.$2>.VAL,VCS,Lms',$35.(<.P,(14.&40.)(26.(14.&8.))Lm',P,(14.&40.)(26.(14.&8.))(=.(31.(7.(1=.$3.$3.)(1?.$3.$3.R11.R19.)(7.(1=.$3.$3.)(1?.$3.$3.(12.$24.+390.)(12.$24.+398.))(9.(1=.$3.$3.))))R>.R1.)(=.(32.$2>.R>.R1.)(=.(33.$2>.R1.)(=.(3;.$2>.R1.(12.$24.+378.)(7.$41.(42.(23.&40.R17.))(7.$41.(42.(23.&40.R16.))(7.$41.(42.R1:.)(7.$41.(42.(23.&40.R15.))(9.$41.))))))(2;.(=.(2;.(>.$3.R16.=)(>.$3.R14.=))(=.(44.$2>.R1.R11.R19.)(<.(14.&40.)Lx5,(14.&40.)(<.(14.&40.)Lx11,(14.&40.)(<.(14.&40.)Lx14,(14.&40.)(>.$35.R5.(36.(22.R39.(23.&40.R1<.)R38.R37.R3.R35.R34.R33.R32.(23.&40.(12.$24.+378.))R2.R31.R30.R1.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R13.(45.R39.)R12.(38.(14.&40.))R4.(39.$2>.))))))))(=.(3=.(>.$3.R16.=))(=.(3=.(>.$3.R14.=))(=.(44.$2>.R1.R11.(12.R19.-10.))(=.(<.(0.(14.&8.))Lj,(0.(14.&8.))(46.R2.R1:.R1.R37.))(>.$35.R2.(36.(3>.R19.R36.R35.R34.R32.R31.R30.R2?.R2=.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R18.=R16.R14.)R10.(23.&40.$3?.)R?.(38.(14.&40.))R1.(39.$2>.)))))))))))))(36.(22.R34.(23.&40.R17.)R33.R32.R31.R30.R2?.R2>.R2=.(23.&40.(12.$24.+378.))(23.&40.R16.)R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R>.(23.&40.$47.)R=.(38.(14.&40.))R<.(39.$2>.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gl SP P glen gfirst gb fnx fsz fcnt lo F fc m
      GFB GBB PB QG FIRST ST LOIMG SPL SPH SCS MI.
    unfold bhdr, mb_regs, mb_frame in *. unfold A_MERGEB, A_MB_HEAD, A_INSTANCE in *.
    change (1074072 + 888) with 1074960 in *. change (1074072 + 912) with 1074984 in *. change (1074072 + 920) with 1074992 in *.
    pose proof (munch_refl [(lo, SP); (1074984, 1074992)] m) as MU. pose proof (wmono_refl asegs m) as WM. lx_aceil.
    destruct (Z.eq_dec gfirst 0) as [G0|G0].
    - clear FIRST. subst gfirst.
      (* [comment removed for export] *)
      lx_run (PLAN [A_MB_HEAD] [] 20%N).
      apply evtA_done. exists lxm. lx_ands; [ assumption .. | | left; split; [left; reflexivity| split; [assumption| do 3 eexists; lx_mseq]]];
        match goal with |- rw_cells _ lxm ?a _ => match goal with K : rw_cells _ lxm a _ |- _ => lx_rwx K end end.
    - flat constr:((FIRST G0)) 5%nat. intros HF FCS F0 F1 FNB. clear FIRST.
      (* [comment removed for export] *)
      lx_run (PLAN [A_MB_HEAD] [] 20%N).
      + try lx_junk_under lo (SP + -8) 8%nat j FRj.
        apply evtA_done; exists lxm; lx_ands;
        [ assumption ..
        |
        | first [ left; split; [right; lx_arith| split; [assumption| do 3 eexists; lx_mseq]]
                | right; split; [exact G0| split; [lx_arith| split; [assumption| split; [eexists; eassumption| lx_mseq]]]] ] ];
        match goal with |- rw_cells _ ?mx ?a _ => match goal with K : rw_cells _ mx a _ |- _ => lx_rwx K end end.
      + try lx_junk_under lo (SP + -8) 8%nat j FRj.
        apply evtA_done; exists lxm; lx_ands;
        [ assumption ..
        |
        | first [ left; split; [right; lx_arith| split; [assumption| do 3 eexists; lx_mseq]]
                | right; split; [exact G0| split; [lx_arith| split; [assumption| split; [eexists; eassumption| lx_mseq]]]] ] ];
        match goal with |- rw_cells _ ?mx ?a _ => match goal with K : rw_cells _ mx a _ |- _ => lx_rwx K end end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L11946690999.60L19516721402.60L20891441591.60L21786719899.60L21991601993.59L23585410382.61L25930419531.60L25936898221.60L31947775533.60L32796810656.60L40066591175.63L47134214024.62L47937465853.60L53534663706.60L53578222862.1 L53599432850.61L9679931634.2  00000=00H00M00`00h01001C01R01a01b02M02[02h03603:03B03JS3hAR2AL4IMG'S3hAR2SP2loS3hARS3hAR3ext2gb2EB3GBBS3hAR2SPS3hAR2SPS3hAR3ext2gb2EB3GBBS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLFS3hAR2SP3ext2gb2lo5LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2HB5Ha_stS3hAR2AL4IMG'S3hAR2AL5ALWF'S2SPS3hAR2HBS3ext2gb". (* [comment removed for export] *)
  Lemma mb_exit : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pra,(14.&40.)Pgp,(14.&40.)Ptp,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa3,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)Pgf,(14.&40.)Pgl,(14.&40.)Pqra,(14.&40.)Pj,(0.(14.&8.))PSP,$3.PP,$3.Pext,$3.Pcur,$3.Pnx,$3.Pglen,$3.Pgb,$3.Plo,$3.PF,(25.&5.(14.&40.))Pfc,(14.&20.)Pm0,P,(14.&40.)(26.(14.&8.))Pm,P,(14.&40.)(26.(14.&8.))PW,(0.(1=.$3.$3.))P,(=.(1;.=R;.)(1;.R;.R7.))P,(18.R8.(1:.+2.+40.))P,(1;.R?.(1:.+2.+3>.))P,(3;.$2>.R5.(12.$24.+378.)(7.$41.(42.(23.&40.R;.))(7.$41.(42.R14.)(7.$41.(42.R13.)(7.$41.(42.(23.&40.R:.))(9.$41.))))))P,(46.R6.R11.R12.R13.)P,(44.$2>.R7.R;.(12.R12.-10.))P,(1;.(2:.VhAR,)R<.)P,(1;.R=.(13.R14.+10.))P,(2<.VCS,R>.(13.R15.R>.))P,(31.(7.(1=.$3.$3.)(1?.$3.$3.R?.R16.)(7.(1=.$3.$3.)(1?.$3.$3.(12.$24.+378.)(12.$24.+398.))R:.))R<.R;.)P,(32.$2>.R=.R<.)P,(33.$2>.R=.)(34.$2>.VAL,VCS,Lms',$35.(<.P,(14.&40.)(26.(14.&8.))Lm',P,(14.&40.)(26.(14.&8.))(=.(31.(7.(1=.$3.$3.)(1?.$3.$3.R14.R1;.)(7.(1=.$3.$3.)(1?.$3.$3.(12.$24.+378.)(12.$24.+398.))R?.))R11.R1.)(=.(32.$2>.R11.R1.)(=.(33.$2>.R1.)(=.(3;.$2>.R1.(12.$24.+378.)(7.$41.(42.(23.&40.R16.))(7.$41.(42.R1?.)(7.$41.(42.R1>.)(7.$41.(42.(23.&40.(13.R15.R19.)))(9.$41.))))))(=.(44.$2>.R1.R14.R1;.)(>.$35.R2.(36.(22.R1=.(23.&40.R1;.)R34.R33.(23.&40.R17.)R32.R31.R30.R2?.(23.&40.(12.$24.+378.))(23.&40.(13.R15.R19.))(23.&40.R19.)R2>.(23.&40.R18.)(23.&40.+3?=.)(23.&40.+????????????>000.)(23.&40.+2000.)R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.)R13.(45.R1=.)R12.(38.(14.&40.))R1.(39.$2>.)))))))))(36.(3>.R19.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R18.R17.R16.R15.)R11.(23.&40.$40.)R10.(38.(14.&40.))R>.(39.$2>.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t1 t2 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gf gl qra j SP P ext cur nx glen gb lo F fc m0 m W
      EB GBB SPH QG FR ST LOIMG SPL SCS MU WM MI.
    facts. unfold mb_regs, mb_frame in *. unfold A_MB_EXIT, A_INSTANCE in *.
    change (1074072 + 888) with 1074960 in *. change (1074072 + 920) with 1074992 in *.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. replace (SP + -16 + 16) with SP by (clear; lia). zstep.
    release_frame FR ST SP.
    apply evtA_done. eexists. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [replace (gb - ext) with (gb + - ext) by (clear; lia); first [assumption | replace (gb + - ext) with (gb - ext) by (clear; lia); assumption]|].
    split; [exact ST| first [reflexivity | replace (gb + - ext) with (gb - ext) by (clear; lia); reflexivity]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Definition mb_W (P : Z) (W : list (Z * Z)) : list (Z * Z) := (A_INSTANCE + 888, A_INSTANCE + 920) :: (P, P + 32) :: W.

  Definition mb_post (SP : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
      (P gb : Z) (L ts Lf tsf : list bnode) (TL : Z) (tf : word) (W : list (Z * Z)) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Lms',$35.(<.P,(14.&40.)(26.(14.&8.))Lm',P,(14.&40.)(26.(14.&8.))(<.(0.$1.)LL',(0.$1.)(<.(0.$1.)Lts',(0.$1.)(<.$3.Lext',$3.(<.$3.LTL',$3.(<.$3.Lcur',$3.(<.(14.&40.)Ltf',(14.&40.)(<.(14.&40.)Lx6,(14.&40.)(<.(14.&40.)Lx7,(14.&40.)(<.(14.&40.)Lx13,(14.&40.)(<.(14.&40.)Lx28,(14.&40.)(<.(14.&40.)Lx29,(14.&40.)(<.(14.&40.)Lx30,(14.&40.)(=.(31.(48.O<.O4.)O1.R=.)(=.(32.$2>.O1.R=.)(=.(33.$2>.R=.)(=.(3;.$2>.R=.(12.$24.+378.)(7.$41.(42.(23.&40.(27.(10.$1.R<.))))(7.$41.(42.(23.&40.(49.R<.)))(7.$41.(42.(23.&40.(4:.=R<.)))(7.$41.(42.(23.&40.O;.))(9.$41.))))))(=.(>.$3.O;.(12.(11.R<.)R:.))(=.(1;.=R:.)(=.(4;.R=.R<.)(=.(4;.R=.R;.)(=.(4<.VhAR,(6.$1.R;.R<.))(=.(>.$3.(49.R<.)(49.O:.))(=.(3;.$2>.R=.O<.(7.$41.(42.(23.&40.(27.(10.$1.R;.))))(7.$41.(42.R7.)(7.$41.(42.(23.&40.R9.))(7.$41.(42.(23.&40.(11.R;.)))(9.$41.))))))(=.P,(3=.(>.(0.$1.)R;.(9.$1.)))(=.(>.$3.R:.(4:.=R<.))(>.(14.&40.)R8.(23.&40.(49.R<.))))(=.(=.(1;.=R9.)(18.R9.(1:.+2.+40.)))(=.P,(>.(0.$1.)R;.(9.$1.))(=.(>.$3.R:.O6.)(>.(14.&40.)R8.O5.))(=.(>.(0.(14.&40.))(15.$1.(14.&40.)$16.R<.)(15.$1.(14.&40.)$16.O:.))(=.(>.(0.(14.&40.))(15.$1.(14.&40.)$16.R;.)(15.$1.(14.&40.)$16.O9.))(=.Pb',$1.P,(;.$1.R1.(6.$1.R<.R=.))(<.$1.Lb,$1.(=.(;.$1.R1.(6.$1.O9.O:.))(>.$3.(5.R3.)(5.R1.))))(=.(>.$?.(10.$1.(6.$1.R;.R<.))(10.$1.(6.$1.O9.O:.)))(=.(>.$3.(12.(11.R;.)(11.R<.))(12.(11.O9.)(11.O:.)))(=.(>.(0.$1.)R<.O8.)(=.(>.(0.$1.)R;.O7.)(>.$35.R>.(36.(3>.O1=.O1<.O1;.O1:.R6.R5.O19.O18.R4.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.R3.R2.R1.O=.O<.R:.R8.=)O3.(23.&40.$40.)O2.(38.(14.&40.))R=.(39.$2>.)))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01]0?L10104637928.5 L10326617254.3 L10394150570.8 L11144228395.17L11801312500.3 L11801312500.5 L11801343032.3 L11803369861.7 L11803401972.3 L11805908770.3 L12487233674.3 L12567322865.6 L12638543609.1 L12919271948.17L13309571158.19L15667356421.21L17289902851.1 L18068229764.18L18458821775.3 L18469321238.3 L19613817787.17L19949507196.8 L20005703504.8 L20005769037.18L20005769037.6 L20009799152.17L20047152914.6 L23197694228.17L23242755669.3 L23596113294.18L24516123541.3 L25531141753.3 L2875253326.5  L31038191277.2 L31609138196.1 L32027975233.0 L39987089470.8 L39987154979.18L39987154979.6 L40037278339.3 L40039373850.3 L40132574184.3 L40147240305.3 L42046782312.4 L44711700505.7 L45040410085.1 L45732878885.8 L45732944440.18L4711547566.3  L47179840487.2 L47507344155.8 L47507409670.18L47507409670.6 L47809926588.2 L48487574113.3 L48493597916.3 L49810892654.2 L50701648849.5 L50701714037.8 L50703514961.3 L50714238792.7 L50716334024.5 L50716334408.5 L50716343624.5 L50716446536.7 L50871118831.6 L51492177656.3 L51492178021.3 L51492179561.3 L51493998613.3 L52235622253.17L52565066999.12L52577458634.11L53039478276.4 L53039478276.6 L53517156698.94L57144070772.64L58290980727.3 L5846808918.3  L58480500378.3 L59149846997.6 L59149846997.8 L59210333457.17L59222949809.8 L59223015340.18L59223015340.6 L59308841296.2 L59308841425.2 L59314873579.97L60631948163.3 L61596861341.22L64754897250.18L6487649030.8  L65745680710.96L66030178054.18L66030178054.6 L66180630099.1 L66799230352.1 L66801553502.2 L67117412189.3 L67119527005.17L67458179888.1 L67690990034.18L68586771908.7 L7500676798.16 L7824888693.3  L7834591868.1  L8163180309.7  L8927277446.18 00000A00K00^01A01L01^01j02D02N02W02e03=03B04A04B04C04F04g05305@05f06306A06b07007Q07Z08:08E08k09709?09N09V09[09\09j0:K0:Y0:f0;20;>0;K0;Y0<40<80<K0<L0<W0<\0<j0=K0=Y0=^0=g0>10>70>H0>f0?00?J0?[0?l0@>0@V0@c0@k0A30A<0AC0BC0Bo0CW0Cd0D90DU0FV0Fd0G00G90GN0Gk0HL0HZ0I;0II0IO0IU0J<0JH0JI0Jo0KK0L80LY0Lg0Lj0M00M<0MH0Mn0N20N30NM0OJ0OR0OV0On0PXS3hAR1c1P2P04OKc'S1x2bl3XblS3hAR1c1x4OKc'4OKx'S3hAR4done1c1x4rest2ts3ext2E05LENB'S1c2tl4APtcS1c2TL2tl3ETL4APtcS3hAR1c4OKc'S3hAR1c2TL2tl3ETL4APtc3CNTS1c2b03A0cS1c2b02X1S3hAR2tl5OKtl'S3hAR1c1x4OKc'4APcx4FIT'S3ts0S3hAR4done1c1x4rest2ts3ext2gb2E03BND4OKc'4OKx'2RB2DB4HGB'5LENB'FFS1cS3hAR4done1c1x4rest2ts4OKx'5LENB'S3hAR2b03OK0S3hAR2b04OK0'S3hAR4done1c1x4rest2ts4OKc'4OKx'5LENB'S3hAR1c1x3BIGS3hAR1c1x4OKc'S3hAR4done1c1x4rest2ts4OKc'5LENB'S3hAR1c1x4OKc'S3hAR4done1c1x4rest2ts4OKc'5LENB'S3hAR1c1xS3hAR4done1c1x4rest2ts3TB05LENB'S2TL2tl3ETLS3hAR4done1c1x4rest2ts4OKc'4OKx'5LENB'S3hAR1x4OKx'S1x1a2AxS3hAR1P2P01a2A1S3ext2E0S3ts_SS3hAR1c1x4OKx'S3hAR4done1c1x4rest2ts4OKx'5LENB'S3hAR1c1x4OKx'S3hAR2b04OK0'S3hAR2b03OK0S3hAR2b03OK0S3hAR2b04OK0'S3hAR1c1x4OKc'S3hAR1c1x4OKc'4FIT'2tl4APtcS2tlS3hAR1c1x4rest4HDRBFS2TL2tl3ETLS1c1xS3hAR1c1x4OKx'S3hAR4done1c1x4rest2ts4OKx'5LENB'S3hAR1c1x4OKx'S1c1xS2b02tl1HS2tl2b02X3S1a2A0S3hAR1P2P02b03OK0S3hAR1P2TL2P02tl3ETL5OKtl'3CNTS3hAR1P2P0S3hAR1P2TL2P02tl3ETL5OKtl'S3hAR1c1P2P04OKc'S3hAR1x1P2P04OKx'S3hAR1P2P02b04OK0'S3hAR1c1x1P2P04OKc'4FIT'S3hAR1c1x3FITS1c1y2YcS1x1y2YxS1y2tl2YtS1c1y1HS3hAR4done1c1x4rest2ts3ext2gb3BND4OKc'4OKx'2RB3TB02DB4HGB'5LENB'S3hAR1c1x1P2TL2P02tl3ETL4APtc4APtx5OKtl'3CNTS3hAR1c1x1P2TL2P02tl3ETL4APtc4APtx5OKtl'S4done1c1x2tsS4done1c1x1r5rest'2tsS3hAR1k4done1c1x2ts2LT5LENB'S3hAR2AL2CS4done1c1x4rest2ts2ra2gp2tp2t12t22s02s12a32s22s32s42s52s62s72s82s93s103s112t32t42t52t62tf2SP1P3ext2gb2TL1W1F2fc2m01m2LTS3hAR2tl5OKtl'S3hAR1x4OKx'S2tl2b'1HS4done1c1x3ext2gb3HGBS4done1c1x1r5rest'3ext2gb3HGBS3hAR4done1c1x4rest2ts4OKc'5LENB'S3hAR1c1x4OKc'S3hAR4done1c1x4rest2ts4OKc'5LENB'S3hAR1c1x4OKc'S1c2X1S1x2X2S3hAR1k4done1c1x2r02rr2ts2LT5LENB'2H11HS1k5rest'2LTFS3hAR4done1c1x4rest2ts4OKc'4OKx'5LENB'S4done1c1x1r5rest'2ts2gb3BNDS3hAR1k4done1c1x2r02rr2ts2LT3OKc3OKx5LENB'2H1S3hAR4done1c1x4rest2ts4OKc'5LENB'S3hAR1c1x4OKc'S1xS4doneS4done5rest'S3hAR1x4OKx'S3hAR4done1c1x4rest2ts4OKc'4OKx'5LENB'S2tlFS3hAR1P2TL2P02tl3ETL5OKtl'S3hAR4done1c1x4rest2ts3ext2gb2E03BND4OKc'4OKx'2RB3TB02DB4HGB'S1c1a2AcS2tlS3hAR1c1x1P2P04OKc'4FIT'S3hAR4done1c1x4rest2ts4OKc'4OKx'5LENB'3FIT". (* [comment removed for export] *)
  Lemma mb_loop : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pk,$?.Pdone,(0.$1.)Pc,$1.Px,$1.Prest,(0.$1.)Pts,(0.$1.)Pra,(14.&40.)Pgp,(14.&40.)Ptp,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa3,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)Ptf,(14.&40.)PSP,$3.PP,$3.Pext,$3.Pgb,$3.PTL,$3.PW,(0.(1=.$3.$3.))PF,(25.&5.(14.&40.))Pfc,(14.&20.)Pm0,P,(14.&40.)(26.(14.&8.))Pm,P,(14.&40.)(26.(14.&8.))P,(4=.(10.$1.R23.)R27.)P,(>.$3.R8.(12.(11.(6.$1.R27.(7.$1.R26.(7.$1.R25.R24.))))R9.))P,(1;.=R:.)P,(18.(12.(12.(11.R25.)R:.)(29.+2000.(27.(10.$1.(6.$1.R29.(7.$1.R28.(7.$1.R27.R26.)))))))(1:.+2.+3<.))P,(18.(27.(10.$1.(6.$1.R26.(6.$1.R2:.(7.$1.R29.(7.$1.R28.R27.))))))(1:.+2.+28.))P,(=.(1;.=R;.)(18.R;.(1:.+2.+40.)))P,(4<.VhAR,(6.$1.R28.(6.$1.R2<.(7.$1.R2;.(7.$1.R2:.R29.)))))P,Pb,$1.P,(;.$1.R1.(6.$1.R2:.(6.$1.R2>.(7.$1.R2=.(7.$1.R2<.R2;.)))))(2<.VCS,(5.R2.)+2000.)P,Pb,$1.Py,$3.P,(;.$1.R2.(6.$1.R2<.(6.$1.R30.(7.$1.R2?.(7.$1.R2>.R2=.)))))P,(4>.R10.R2.)(3=.(=.(1;.(5.R4.)R3.)(18.R3.(12.(5.R4.)+2000.))))P,(3;.$2>.R:.(12.$24.+378.)(7.$41.(42.(23.&40.(27.(10.$1.(6.$1.R2?.(7.$1.R2>.(7.$1.R2=.R2<.)))))))(7.$41.(42.(23.&40.(49.(6.$1.R2?.(7.$1.R2>.(7.$1.R2=.R2<.))))))(7.$41.(42.(23.&40.(4:.=(6.$1.R2?.(7.$1.R2>.(7.$1.R2=.R2<.))))))(7.$41.(42.(23.&40.R10.))(9.$41.))))))P,(4;.R;.(6.$1.R30.(7.$1.R2?.(7.$1.R2>.R2=.))))P,(4;.R<.R2=.)P,P,(3=.(>.(0.$1.)R2>.(9.$1.)))(=.(>.$3.R13.(4:.=R2?.))(>.(14.&40.)R18.(23.&40.(49.R2?.))))P,(3;.$2>.R>.R16.(7.$41.(42.(23.&40.(27.(10.$1.R2?.))))(7.$41.(42.R18.)(7.$41.(42.(23.&40.R13.))(7.$41.(42.(23.&40.(11.R2?.)))(9.$41.))))))P,(2<.VCS,R17.+20.)P,(1;.(2:.VhAR,)R18.)P,(1;.(12.R19.+20.)(1:.+2.+3>.))P,(31.(48.R1:.R16.)R13.R12.)P,(32.$2>.R14.R13.)P,(33.$2>.R14.)(34.$2>.VAL,VCS,(4?.R1>.R35.R34.R33.R30.R2?.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R20.R1=.R1;.(6.$1.R3:.(7.$1.R39.(7.$1.R38.R37.)))R36.(6.$1.R3:.(20.(0.$1.)(0.$1.)(1>.R39.(7.$1.R38.R37.))))(6.$1.R36.(21.(0.$1.)(0.$1.)(1>.R39.(7.$1.R38.R37.))))R1:.R1?.R19.R18.R17.R16.)(36.(3>.R1>.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1=.R1<.(5.R39.)(5.R38.))R18.(23.&40.$3?.)R17.(38.(14.&40.))R15.(39.$2>.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros done c x rest ts ra gp tp t1 t2 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 tf
      SP P ext gb TL W F fc m0 m LT HGB E0 BND LENB TLB WF CSN NW QG BL BT TLD TMP PCS P0 P1 MU WM MI; [lia|].
    (* [comment removed for export] *)
    pose proof (bwf_app_r _ _ WF) as WFL. pose proof (bwf_app_l _ _ WF) as WFts. pose proof (bwf_app_r _ _ WFL) as WFc.
    flat constr:((bwf_cons_inv _ _ WFc)) 3%nat. intros OKc WFx APc. flat constr:((bwf_cons_inv _ _ WFx)) 3%nat. intros OKx WFr APx.
    pose proof (proj1 WFr) as OKr. pose proof (proj1 WFts) as OKts. pose proof (proj1 (bwf_app_l _ _ WFL)) as OKd.
    pose proof OKc as OKc'. unfold bn_ok in OKc'. pose proof OKx as OKx'. unfold bn_ok in OKx'.
    assert (APcx : bn_addr c + 8192 <= bn_addr x \/ bn_addr x + 8192 <= bn_addr c) by (apply APc; left; reflexivity).
    assert (INc : In c (ts ++ done ++ c :: x :: rest)) by (apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    assert (INx : In x (ts ++ done ++ c :: x :: rest)) by (apply in_or_app; right; apply in_or_app; right; right; left; reflexivity).
    pose proof (bsum_nonneg _ OKr) as RB. pose proof (bsum_nonneg _ OKts) as TB0. pose proof (bsum_nonneg _ OKd) as DB.
    pose proof HGB as HGB'. rewrite bsum_app in HGB'. cbn [bsum] in HGB'.
    pose proof LENB as LENB'. rewrite !app_length in LENB'. cbn [length] in LENB'.
    (* [comment removed for export] *)
    unfold blist in BL. rewrite blistT_app in BL. flat constr:(BL) 4%nat. flclear BL. intros Bd Nc Nx Br. cbn [hd_addrT] in Bd, Nc, Nx.
    change (hd_addrT rest 0) with (hd_addr rest) in Nx.
    flat constr:(Nc) 3%nat. flclear Nc. intros HC HDc BWc. flat constr:(Nx) 3%nat. flclear Nx. intros HN HDx BWx.
    assert (HDR : (hd_addr rest = 0 <-> rest = []) /\ 0 <= hd_addr rest < 2^64).
    { destruct rest as [|r0 rr]; cbn [hd_addr hd_addrT]. { split; [tauto| lia]. }
      inversion OKr; subst. unfold bn_ok in *. split; [split; [intros; exfalso; lia| congruence]| lia]. }
    flat constr:(HDR) 2%nat. flclear HDR. intros HDR0 HDRB.
    destruct (Z_lt_le_dec 1021 (bn_count c + bn_count x)) as [BIG|FIT].
    - (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (mb_nomerge ra gp tp t1 t2 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP P ext
                  (bn_addr c) (bn_addr x) (hd_addr rest) (bn_size c) (bn_count c) (bn_size x) (bn_count x) F fc m);
          try first [exact HC | exact HN | exact MI | apply CSN; assumption].
        all: unfold bn_count in *; clear -OKc' OKx' BIG HDRB; try lia. }
      intros ms' (x6 & x28 & x29 & POST).
      destruct POST as [(Kn & ->) | (Kn & ->)].
      + (* [comment removed for export] *)
        destruct rest as [|r rest']; [exfalso; apply Kn; reflexivity|]. cbn [hd_addr hd_addrT] in *.
        rewrite (mloop_big c x (r :: rest') BIG). cbn [fst snd].
        replace (done ++ c :: fst (mloop x (r :: rest'))) with ((done ++ [c]) ++ fst (mloop x (r :: rest'))) by (rewrite <- app_assoc; reflexivity).
        replace (done ++ c :: x :: r :: rest') with ((done ++ [c]) ++ x :: r :: rest') in * by (rewrite <- app_assoc; reflexivity).
        eapply (IH (done ++ [c]) x r rest' ts) with (TL := TL) (tf := tf); try eassumption.
        * cbn in LT. clear -LT. lia.
        * unfold blist. rewrite blistT_app. cbn [hd_addrT blistT]. rewrite blistT_snoc.
          split; [split; [exact Bd| split; [exact HC| split; [exact HDc| exact BWc]]]|].
          split; [split; [exact HN| split; [exact HDx| exact BWx]]| exact Br].
      + (* [comment removed for export] *)
        assert (rest = []) as -> by (apply HDR0; exact Kn).
        apply evtA_done. unfold mb_post.
        exists m, (done ++ [c; x]), ts, ext, TL, (bn_addr x), tf, x6, t2, a3, x28, x29, t5.
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact QG|].
        split; [exact HGB|]. split; [exact E0|].
        split. { unfold blist. rewrite blistT_app. cbn [hd_addrT blistT]. split; [exact Bd|].
                 split; [split; [exact HC| split; [exact HDc| exact BWc]]|]. split; [split; [exact HN| split; [exact HDx| exact BWx]]| exact I]. }
        split; [exact BT|]. split; [exact WF|]. split; [reflexivity|]. split; [exact TMP|]. split; [exact TLD|]. split; [exact TLB|].
        split; [intros _; split; reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [intros b' Hb'; exists b'; split; [exact Hb'| reflexivity]|].
        split; [reflexivity|]. split; [reflexivity|].
        rewrite (mloop_big c x [] BIG). cbn [fst snd mloop]. split; [reflexivity|]. split; [rewrite app_nil_r; reflexivity|]. reflexivity.
    - (* [comment removed for export] *)
      assert (SZB : bn_size c + bn_size x - 8192 < 2^60) by (clear -BND HGB' OKc' OKx' RB TB0 DB E0; lia).
      flat constr:((surg_ok c x OKc OKx SZB FIT)) 2%nat. intros OKc2 OKx2. pose proof FIT as FIT'. unfold bn_count in FIT'.
      assert (LCE : length (bn_elems c) = Z.to_nat (bn_count c)) by (unfold bn_count; clear; lia).
      assert (LWS : length (bn_elems x) = Z.to_nat (bn_count x)) by (unfold bn_count; clear; lia).
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (mb_merge_A ra gp tp t1 t2 s0 s1 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP P ext
                  (bn_addr c) (bn_addr x) (hd_addr rest) (bn_size c) (bn_count c) (bn_size x) (bn_count x) (bn_elems c) (bn_elems x) F fc m);
          try first [exact HC | exact HN | exact HDc | exact HDx | exact BWc | exact MI | exact APcx | exact LCE | exact LWS | apply CSN; assumption].
        all: unfold bn_count in *; clear -OKc' OKx' FIT; lia. }
      intros ms1 (x7 & x28 & x29 & x30 & m1 & -> & MU1 & WM1 & MI1 & HC1 & HN1 & HD1 & HS1 & BW1).
      (* [comment removed for export] *)
      assert (TLAST : ts <> [] -> exists ts0 tl, ts = ts0 ++ [tl] /\ TL = bn_addr tl /\ tf = Z_to_bv 64 (hd_addr ts) /\ bn_ok tl
                 /\ blistT m ts0 (bn_addr tl) /\ rw_cells asegs m TL [C8 (Z_to_bv 64 0)]
                 /\ rw_cells asegs m (TL + 8) [C8 (Z_to_bv 64 (bn_size tl)); C8 (Z_to_bv 64 (bn_count tl))]
                 /\ u64arr asegs m (TL + 24) (bn_elems tl) /\ wr_at asegs m TL 8192
                 /\ (bn_addr tl + 8192 <= bn_addr c \/ bn_addr c + 8192 <= bn_addr tl)
                 /\ (bn_addr tl + 8192 <= bn_addr x \/ bn_addr x + 8192 <= bn_addr tl)
                 /\ (forall b', In b' (done ++ c :: x :: rest) -> bn_addr tl + 8192 <= bn_addr b' \/ bn_addr b' + 8192 <= bn_addr tl)
                 /\ (forall b', In b' ts0 -> bn_addr tl + 8192 <= bn_addr b' \/ bn_addr b' + 8192 <= bn_addr tl)).
      { intros NE. destruct (snoc_or_nil ts) as [->|(ts0 & tl & ->)]; [congruence|]. flat constr:((TLD NE)) 2%nat. intros E1 E2.
        rewrite last_addr_snoc in E1. exists ts0, tl. unfold blist in BT. rewrite blistT_snoc in BT. flat constr:(BT) 2%nat. flclear BT. intros B0 (R1 & R2 & R3).
        pose proof (proj1 (rw_cells_app asegs m (bn_addr tl) [C8 _] [C8 _; C8 _]) R1) as [R1a R1b]. cbn [cells_size csize Nat.add] in R1b.
        assert (INtl : In tl (ts0 ++ [tl])) by (apply in_or_app; right; left; reflexivity).
        subst TL. split; [reflexivity|]. split; [reflexivity|]. split; [exact E2|].
        split; [eapply bwf_ok_in; [exact WFts| exact INtl]|]. split; [exact B0|]. split; [exact R1a|].
        split; [replace (bn_addr tl + 8) with (bn_addr tl + Z.of_nat 8) by (clear; lia); exact R1b|]. split; [exact R2|]. split; [exact R3|].
        split; [eapply bwf_app_apart; [exact WF| exact INtl| apply in_or_app; right; left; reflexivity]|].
        split; [eapply bwf_app_apart; [exact WF| exact INtl| apply in_or_app; right; right; left; reflexivity]|].
        split; [intros b' Hb'; eapply bwf_app_apart; [exact WF| exact INtl| exact Hb']|].
        intros b' Hb'. pose proof (bwf_app_apart ts0 [tl] b' tl WFts Hb' ltac:(left; reflexivity)). clear -H. lia. }
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (mb_merge_B1 ra gp tp x7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6
                  (Z_to_bv 64 (hd_addr (done ++ c :: x :: rest))) tf (Z_to_bv 64 0) SP P ext
                  (bn_addr c) (bn_addr x) (hd_addr rest) (bn_size c) (bn_count c) (bn_count c + bn_count x) (bn_size x) (bn_count x)
                  (Z.of_nat (length (done ++ c :: x :: rest))) (last_addr 0 (done ++ c :: x :: rest)) gb (Z.of_nat (length ts)) TL (bsum ts) F fc m1 _ eq_refl);
          try first [exact HC1 | exact HN1 | exact MI1 | exact APcx | exact PCS | exact P0 | exact P1 | exact TLB | apply CSN; assumption].
        all: try (unfold bn_count in *; rewrite ?app_length; cbn [length]; clear -OKc' OKx' FIT LENB' HGB' RB DB E0 BND TB0; lia).
        all: try (apply last_addr_bound; [exact (proj1 WFL)| clear; lia]).
        all: try (eapply rw_cells_transport; [exact QG| exact MU1| exact WM1| unfold A_INSTANCE; cbn; clear -OKc'; lia]).
        all: try (eapply rw_cells_transport; [exact TMP| exact MU1| exact WM1| cbn; clear -OKc' P0; lia]).
        1: exact HDRB.
        intros T0. destruct (TLAST ltac:(intros E; subst ts; apply T0; reflexivity)) as (ts0 & tl & Ets & ETL & _ & OKtl & _ & R1a & _ & _ & _ & APtc & APtx & _).
          pose proof OKtl as OKtl'. unfold bn_ok in OKtl'. subst TL.
          split; [eapply rw_cells_transport; [exact R1a| exact MU1| exact WM1| cbn; clear -APtc; lia]|].
          split; [eapply crange_sub; [apply CSN; rewrite Ets; apply in_or_app; left; apply in_or_app; right; left; reflexivity| clear; lia| clear; lia]|].
          split; [clear -OKtl'; lia|]. split; [clear -OKtl'; lia|]. split; [exact APtc| exact APtx]. }
      intros ms2 (m2 & x6 & x7' & MU2 & WM2 & MI2 & HC2 & HN2 & QG2 & TMP2 & TLC2 & ->).
      (* [comment removed for export] *)
      eapply evtA_cut.
      { eapply (mb_merge_B2 ra gp tp x6 x7' s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6
                  (if Z.of_nat (length ts) =? 0 then Z_to_bv 64 (bn_addr x) else tf) (Z_to_bv 64 (Z.of_nat (length ts))) (Z_to_bv 64 TL)
                  SP P ext (bn_addr c) (bn_addr x) (hd_addr rest) (bn_size c + bn_size x - 8192) (bn_count c + bn_count x)
                  (Z.of_nat (length ts) + 1) (bsum ts) F fc m2);
          try first [exact HC2 | exact TMP2 | exact MI2 | exact PCS | exact P0 | exact P1 | exact HDRB | apply CSN; assumption].
        all: clear -OKc' OKx' LENB' HGB' RB DB E0 BND TB0; lia. }
      intros ms3 (m3 & x13 & MU3 & WM3 & MI3 & TMP3 & POST).
      (* [comment removed for export] *)
      set (c' := mnode c x). set (x' := xnode x).
      assert (WM13 : wmono asegs m m3) by (eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]).
      (* [comment removed for export] *)
      assert (HC3 : rw_cells asegs m3 (bn_addr c) (bhdr (hd_addr rest) (bn_size c + bn_size x - 8192) (bn_count c + bn_count x))).
      { eapply rw_cells_transport; [exact HC2| exact MU3| exact WM3| cbn; clear -OKc' P0; lia]. }
      assert (HN3 : rw_cells asegs m3 (bn_addr x) (bhdr 0 8192 0)).
      { eapply rw_cells_transport; [exact HN2| exact MU3| exact WM3| cbn; clear -OKx' P0; lia]. }
      assert (QG3 : rw_cells asegs m3 (A_INSTANCE + 888)
                      [C8 (Z_to_bv 64 (Z.of_nat (length (done ++ c :: x :: rest)) - 1)); C8 (Z_to_bv 64 (hd_addr (done ++ c :: x :: rest)));
                       C8 (Z_to_bv 64 (if last_addr 0 (done ++ c :: x :: rest) =? bn_addr x then bn_addr c else last_addr 0 (done ++ c :: x :: rest))); C8 (Z_to_bv 64 gb)]).
      { eapply rw_cells_transport; [exact QG2| exact MU3| exact WM3| unfold A_INSTANCE; cbn; clear -P0; lia]. }
      (* [comment removed for export] *)
      assert (DJ1 : forall a, 0x65f000 <= a -> a + 8192 <= ACEIL ->
                    (a + 8192 <= bn_addr c \/ bn_addr c + 8192 <= a) -> (a + 8192 <= bn_addr x \/ bn_addr x + 8192 <= a) ->
                    (Z.of_nat (length ts) <> 0 -> a + 8192 <= TL \/ TL + 8 <= a) ->
                    disjoint_from (mb_Wb P (bn_addr c) (bn_addr x) (Z.of_nat (length ts)) TL) a 8192).
      { intros a A0 A1 Ac Ax At. unfold mb_Wb, A_INSTANCE. cbn [disjoint_from app].
        split; [clear -A0; lia|]. split; [clear -A1 P0; lia|]. split; [clear -Ac; lia|]. split; [clear -Ax; lia|].
        destruct (Z.of_nat (length ts) =? 0) eqn:E; cbn [disjoint_from app]; [exact I|].
        split; [apply At; apply Z.eqb_neq; exact E| exact I]. }
      (* [comment removed for export] *)
      assert (NODE3 : forall b0 nx0, In b0 (done ++ c :: x :: rest) -> b0 <> c -> b0 <> x -> bnode_at m b0 nx0 -> bnode_at m3 b0 nx0).
      { intros b0 nx0 Hin NEc NEx Hat.
        pose proof (bwf_ok_in _ _ WFL Hin) as OK0. pose proof OK0 as OK0'. unfold bn_ok in OK0'.
        assert (A0c : bn_addr b0 + 8192 <= bn_addr c \/ bn_addr c + 8192 <= bn_addr b0).
        { apply (bapart_in _ _ _ WFL Hin ltac:(apply in_or_app; right; left; reflexivity)).
          intros E. flat constr:((bwf_in_split _ _ WFL Hin)) 5%nat. intros l r EL NL NR.
          flat constr:(WFL) 2%nat. intros _ (ND & _). rewrite EL, map_app in ND. cbn [map] in ND. apply NoDup_remove_2 in ND. apply ND.
          rewrite E. assert (INc' : In c (l ++ b0 :: r)) by (rewrite <- EL; apply in_or_app; right; left; reflexivity).
          apply in_or_app. apply in_app_or in INc'. destruct INc' as [H|[H|H]]; [left; apply in_map; exact H| exfalso; exact (NEc H)| right; apply in_map; exact H]. }
        assert (A0x : bn_addr b0 + 8192 <= bn_addr x \/ bn_addr x + 8192 <= bn_addr b0).
        { apply (bapart_in _ _ _ WFL Hin ltac:(apply in_or_app; right; right; left; reflexivity)).
          intros E. flat constr:((bwf_in_split _ _ WFL Hin)) 5%nat. intros l r EL NL NR.
          flat constr:(WFL) 2%nat. intros _ (ND & _). rewrite EL, map_app in ND. cbn [map] in ND. apply NoDup_remove_2 in ND. apply ND.
          rewrite E. assert (INx' : In x (l ++ b0 :: r)) by (rewrite <- EL; apply in_or_app; right; right; left; reflexivity).
          apply in_or_app. apply in_app_or in INx'. destruct INx' as [H|[H|H]]; [left; apply in_map; exact H| exfalso; exact (NEx H)| right; apply in_map; exact H]. }
        eapply bnode_at_transport; [| exact MU3| exact WM3| cbn; unfold A_INSTANCE; clear -OK0' P0; lia| clear -OK0'; lia].
        eapply bnode_at_transport; [| exact MU2| exact WM2| | clear -OK0'; lia].
        2:{ apply DJ1; [clear -OK0'; lia| clear -OK0'; lia| exact A0c| exact A0x|].
            intros T0. destruct (TLAST ltac:(intros E; subst ts; apply T0; reflexivity)) as (ts0 & tl & Ets & ETL & _ & _ & _ & _ & _ & _ & _ & _ & _ & APtL & _).
            pose proof (APtL b0 Hin). rewrite ETL. clear -H. lia. }
        eapply bnode_at_transport; [exact Hat| exact MU1| exact WM1| cbn; clear -A0c; lia| clear -OK0'; lia]. }
      assert (Br3 : blistT m3 rest 0).
      { apply (blistT_map_nodes m m3 rest 0); [| exact Br]. intros b0 nx0 H0 N0.
        pose proof (APc b0 ltac:(right; exact H0)) as X1. pose proof (APx b0 H0) as X2.
        apply NODE3; [apply in_or_app; right; right; right; exact H0| intros ->; clear -X1; lia| intros ->; clear -X2; lia| exact N0]. }
      assert (Bd3 : blistT m3 done (bn_addr c)).
      { apply (blistT_map_nodes m m3 done (bn_addr c)); [| exact Bd]. intros b0 nx0 H0 N0.
        pose proof (bwf_app_apart _ _ b0 c WFL H0 ltac:(left; reflexivity)) as X1. pose proof (bwf_app_apart _ _ b0 x WFL H0 ltac:(right; left; reflexivity)) as X2.
        apply NODE3; [apply in_or_app; left; exact H0| intros ->; clear -X1; lia| intros ->; clear -X2; lia| exact N0]. }
      assert (BL3 : blist m3 (done ++ c' :: rest)).
      { unfold blist. rewrite blistT_app. cbn [hd_addrT blistT]. split; [exact Bd3|]. split; [| exact Br3].
        change (hd_addrT rest 0) with (hd_addr rest).
        split. { replace (bn_count c') with (bn_count c + bn_count x) by (subst c'; unfold bn_count; cbn [mnode bn_elems]; rewrite app_length; clear; lia).
                 subst c'. cbn [mnode bn_addr bn_size]. exact HC3. }
        split.
        - subst c'. cbn [mnode bn_addr bn_elems].
          eapply u64arr_transport; [| exact MU3| exact WM3| cbn -[Z.of_nat Z.mul Z.add]; rewrite app_length; clear -OKc' P0 FIT'; lia].
          eapply u64arr_transport; [exact HD1| exact MU2| exact WM2|].
          rewrite app_length. unfold mb_Wb, A_INSTANCE. cbn [disjoint_from app].
          split; [clear -OKc'; lia|]. split; [clear -OKc' P0 FIT'; lia|]. split; [clear; lia|]. split; [clear -APcx FIT' OKc'; lia|].
          destruct (Z.of_nat (length ts) =? 0) eqn:E; cbn [disjoint_from app]; [exact I|]. split; [| exact I].
          destruct (TLAST ltac:(intros E'; subst ts; apply (proj1 (Z.eqb_neq _ _) E); reflexivity)) as (ts0 & tl & Ets & ETL & _ & _ & _ & _ & _ & _ & _ & APtc & _).
          rewrite ETL. clear -APtc FIT' OKc'. lia.
        - subst c'. cbn [mnode bn_addr]. eapply wr_at_transport; [exact BWc| exact WM13]. }
      assert (BT3 : blist m3 (ts ++ [x'])).
      { unfold blist. rewrite blistT_snoc. split.
        - destruct (snoc_or_nil ts) as [Ets|(ts0_ & tl_ & Ets_)]; [rewrite Ets; exact I|].
          destruct (TLAST ltac:(rewrite Ets_; destruct ts0_; discriminate)) as (ts0 & tl & Ets & ETL & _ & OKtl & B0 & R1a & R1b & R2 & R3 & APtc & APtx & APtL & APts0).
          clear ts0_ tl_ Ets_. pose proof OKtl as OKtl'. unfold bn_ok in OKtl'.
          assert (INts : forall b0, In b0 ts0 -> In b0 ts) by (intros b0 H0; rewrite Ets; apply in_or_app; left; exact H0).
          assert (LTS : Z.of_nat (length ts) =? 0 = false) by (rewrite Ets, zlen_app1; apply Z.eqb_neq; clear; lia).
          rewrite Ets. rewrite blistT_snoc. split.
          + apply (blistT_map_nodes m m3 ts0 (bn_addr tl)); [| exact B0]. intros b0 nx0 H0 N0.
            pose proof (bwf_ok_in _ _ WFts (INts b0 H0)) as OK0. unfold bn_ok in OK0.
            pose proof (bwf_app_apart ts (done ++ c :: x :: rest) b0 c WF (INts b0 H0) ltac:(apply in_or_app; right; left; reflexivity)) as X1.
            pose proof (bwf_app_apart ts (done ++ c :: x :: rest) b0 x WF (INts b0 H0) ltac:(apply in_or_app; right; right; left; reflexivity)) as X2.
            pose proof (APts0 b0 H0) as X3.
            eapply bnode_at_transport; [| exact MU3| exact WM3| cbn; unfold A_INSTANCE; clear -OK0 P0; lia| clear -OK0; lia].
            eapply bnode_at_transport; [| exact MU2| exact WM2| apply DJ1; [clear -OK0; lia| clear -OK0; lia| exact X1| exact X2| intros _; rewrite ETL; clear -X3; lia] | clear -OK0; lia].
            eapply bnode_at_transport; [exact N0| exact MU1| exact WM1| cbn; clear -X1; lia| clear -OK0; lia].
          + subst x'. cbn [xnode bn_addr]. split; [|split].
            * apply (proj2 (rw_cells_app asegs m3 (bn_addr tl) [C8 _] [C8 _; C8 _])). split.
              -- rewrite <- ETL. eapply rw_cells_transport; [apply TLC2; apply Z.eqb_neq; exact LTS| exact MU3| exact WM3| cbn; clear -OKtl' P0 ETL; lia].
              -- cbn [cells_size csize Nat.add]. replace (bn_addr tl + Z.of_nat 8) with (TL + 8) by (clear -ETL; lia).
                 eapply rw_cells_transport; [| exact MU3| exact WM3| cbn; unfold A_INSTANCE; clear -OKtl' P0 ETL; lia].
                 eapply rw_cells_transport; [| exact MU2| exact WM2| unfold mb_Wb, A_INSTANCE; rewrite LTS; cbn; clear -OKtl' P0 ETL APtc APtx; lia].
                 eapply rw_cells_transport; [exact R1b| exact MU1| exact WM1| cbn; clear -APtc ETL; lia].
            * replace (bn_addr tl + 24) with (TL + 24) by (clear -ETL; lia). pose proof OKtl as CNT. unfold bn_ok, bn_count in CNT.
              eapply u64arr_transport; [| exact MU3| exact WM3| cbn; unfold A_INSTANCE; clear -OKtl' P0 ETL CNT; lia].
              eapply u64arr_transport; [| exact MU2| exact WM2| unfold mb_Wb, A_INSTANCE; rewrite LTS; cbn; clear -OKtl' P0 ETL APtc APtx CNT; lia].
              eapply u64arr_transport; [exact R2| exact MU1| exact WM1| cbn; clear -APtc ETL CNT; lia].
            * rewrite <- ETL. eapply wr_at_transport; [exact R3| exact WM13].
        - subst x'. split; [| split].
          + cbn [xnode bn_addr bn_size bn_count bn_elems length Z.of_nat]. exact HN3.
          + cbn [xnode bn_addr bn_elems]. apply u64arr_nil; clear -OKx'; lia.
          + cbn [xnode bn_addr]. eapply wr_at_transport; [exact BWx| exact WM13]. }
      assert (WF3 : bwf ((ts ++ [x']) ++ done ++ c' :: rest)).
      { eapply bwf_of_perm; [exact WF| apply surg_perm|].
        rewrite !Forall_app. repeat split; try assumption; constructor; try assumption; constructor. }
      assert (MU03 : munch (mb_W P W) m0 m3).
      { eapply munch_trans; [exact MU|]. eapply munch_trans; [| eapply munch_trans]; (eapply munch_weaken; [| eassumption]);
          unfold sub_fp, mb_W, mb_Wb, A_INSTANCE; cbn [outside app]; intros y (O1 & O2 & O3).
        - pose proof (NW c y INc O3). split; [clear -H; lia| exact I].
        - pose proof (NW c y INc O3) as Yc. pose proof (NW x y INx O3) as Yx.
          split; [exact O1|]. split; [exact O2|]. split; [clear -Yc; lia|]. split; [clear -Yx; lia|].
          destruct (Z.of_nat (length ts) =? 0) eqn:E; cbn [outside app]; [exact I|]. split; [| exact I].
          destruct (TLAST ltac:(intros E'; subst ts; apply (proj1 (Z.eqb_neq _ _) E); reflexivity)) as (ts0 & tl & Ets & ETL & _).
          pose proof (NW tl y ltac:(rewrite Ets; apply in_or_app; left; apply in_or_app; right; left; reflexivity) O3) as Yt.
          rewrite ETL. clear -Yt. lia.
        - split; [exact O2| exact I]. }
      pose proof (wmono_trans asegs _ _ _ WM WM13) as WM03.
      assert (CSN3 : forall b, In b ((ts ++ [x']) ++ done ++ c' :: rest) -> crange CS (bn_addr b) 8192).
      { intros b' H'. flat constr:((surg_addrs _ _ _ _ _ _ H')) 3%nat. intros b Hb ->. apply CSN. exact Hb. }
      assert (NW3 : forall b y, In b ((ts ++ [x']) ++ done ++ c' :: rest) -> outside W y -> ~ (bn_addr b <= y < bn_addr b + 8192)).
      { intros b' y H'. flat constr:((surg_addrs _ _ _ _ _ _ H')) 3%nat. intros b Hb ->. apply NW. exact Hb. }
      pose proof (surg_bsum ts done c x rest) as [SB1 SB2]. pose proof (surg_flat ts done c x rest) as [SF1 SF2].
      pose proof (surg_len ts done c x rest) as SL.
      fold c' in SB2, SF1, SL. fold x' in SB1, SF2, SL.
      assert (HDA : hd_addr (done ++ c' :: rest) = hd_addr (done ++ c :: x :: rest)) by (apply hd_addr_app_same; reflexivity).
      assert (TLD3 : ts ++ [x'] <> [] -> bn_addr x = last_addr 0 (ts ++ [x'])
                     /\ (if Z.of_nat (length ts) =? 0 then Z_to_bv 64 (bn_addr x) else tf) = Z_to_bv 64 (hd_addr (ts ++ [x']))).
      { intros _. rewrite last_addr_snoc. split; [reflexivity|]. destruct ts as [|t0_ ts_]; [reflexivity|].
        cbn [length]. replace (Z.of_nat (S (length ts_)) =? 0) with false by (symmetry; apply Z.eqb_neq; clear; lia).
        rewrite (proj2 (TLD ltac:(discriminate))). reflexivity. }
      assert (TMP3' : rw_cells asegs m3 P [C8 (Z_to_bv 64 (Z.of_nat (length (ts ++ [x'])))); C8 (if Z.of_nat (length ts) =? 0 then Z_to_bv 64 (bn_addr x) else tf);
                                       C8 (Z_to_bv 64 (bn_addr x)); C8 (Z_to_bv 64 (bsum (ts ++ [x'])))]).
      { rewrite zlen_app1, SB1. exact TMP3. }
      clear DJ1 NODE3 Br3 Bd3 HC3 HN3 TMP3 MU1 MU2 MU3 WM1 WM2 WM3 HC1 HN1 HD1 HS1 BW1 HC2 HN2 QG2 TMP2 TLC2 TLAST Bd Br HC HDc BWc HN HDx BWx QG TMP MU WM MI MI1 MI2 BT.
      fold c' in BL3, WF3, CSN3, NW3, SB2, SF1, SL, HDA. fold x' in BT3, WF3, CSN3, NW3, SB1, SF2, SL, TLD3, TMP3'.
      destruct POST as [(Kn & ->) | (Kn & ->)].
      + (* [comment removed for export] *)
        destruct rest as [|r rest']; [exfalso; apply Kn; reflexivity|].
        replace (hd_addr (r :: rest')) with (bn_addr r) in * by reflexivity.
        replace (bn_addr c) with (bn_addr c') by reflexivity.
        eapply evtA_mono.
        { eapply (IH done c' r rest' (ts ++ [x'])) with (TL := bn_addr x) (tf := if Z.of_nat (length ts) =? 0 then Z_to_bv 64 (bn_addr x) else tf) (gb := gb);
            try first [exact BL3 | exact BT3 | exact WF3 | exact CSN3 | exact NW3 | exact TLD3 | exact TMP3' | exact PCS | exact P0 | exact P1 | exact MU03 | exact WM03 | exact MI3].
          * cbn in LT. clear -LT. lia.
          * rewrite SB2. exact ltac:(clear -HGB; lia).
          * clear -E0. lia.
          * rewrite SB1. replace (Z.of_nat (length (done ++ c' :: r :: rest'))) with (Z.of_nat (length (done ++ c :: x :: r :: rest')) - 1) by (rewrite !app_length; cbn [length]; clear; lia).
            clear -BND. lia.
          * rewrite SL. exact LENB.
          * clear -OKx'. lia.
          * replace (Z.of_nat (length (done ++ c' :: r :: rest'))) with (Z.of_nat (length (done ++ c :: x :: r :: rest')) - 1) by (rewrite !app_length; cbn [length]; clear; lia).
            rewrite HDA. rewrite (last_addr_mid 0 done c' (r :: rest')). rewrite (last_addr_mid 0 done c (x :: r :: rest')) in QG3. cbn [last_addr] in QG3 |- *.
            flat constr:((last_addr_in 0 (r :: rest') ltac:(discriminate))) 3%nat. intros bl Hbl Ebl. cbn [last_addr] in Ebl. rewrite Ebl in QG3 |- *.
            pose proof (APx bl Hbl) as Xbl.
            replace (bn_addr bl =? bn_addr x) with false in QG3 by (symmetry; apply Z.eqb_neq; clear -Xbl; lia). exact QG3. }
        intros ms4 PP. unfold mb_post in PP |- *.
        flat constr:(PP) 35%nat. flclear PP. intros m4 L4 ts4 ext4 TL4 cur4 tf4 y6 y7 y13 y28 y29 y30 MU4 WM4 MI4 QG4 HGB4 E4 BL4 BT4 WF4 HD4 TMP4 TLD4 TLB4 TE4 FM4 FT4 ADDR4 LEN4 SUM4 ELF4 ETS4 ->.
        exists m4, L4, ts4, ext4, TL4, cur4, tf4, y6, y7, y13, y28, y29, y30.
        split; [exact MU4|]. split; [exact WM4|]. split; [exact MI4|]. split; [exact QG4|]. split; [exact HGB4|]. split; [exact E4|].
        split; [exact BL4|]. split; [exact BT4|]. split; [exact WF4|]. split; [rewrite HD4; exact HDA|].
        split; [exact TMP4|]. split; [exact TLD4|]. split; [exact TLB4|].
        split; [intros E4'; exfalso; rewrite ETS4 in E4'; destruct ts; discriminate E4'|].
        split; [rewrite FM4; exact SF1|]. split; [rewrite FT4; exact SF2|].
        split. { intros b' H'. flat constr:((ADDR4 b' H')) 3%nat. intros b1 H1 E1. flat constr:((surg_addrs _ _ _ _ _ _ H1)) 3%nat. intros b2 H2 E2.
                 exists b2. split; [exact H2| rewrite E1; exact E2]. }
        split; [rewrite LEN4; exact SL|]. split; [rewrite SUM4, SB1, SB2; clear; lia|].
        split; [rewrite ELF4; subst c'; rewrite (mloop_fit c x (r :: rest') FIT); reflexivity|].
        split; [rewrite ETS4; subst c' x'; rewrite (mloop_fit c x (r :: rest') FIT), <- app_assoc; reflexivity| reflexivity].
      + (* [comment removed for export] *)
        assert (rest = []) as -> by (apply HDR0; exact Kn).
        apply evtA_done. unfold mb_post.
        exists m3, (done ++ [c']), (ts ++ [x']), (ext + 8192), (bn_addr x), (bn_addr c), (if Z.of_nat (length ts) =? 0 then Z_to_bv 64 (bn_addr x) else tf),
               x6, x7', x13, x28, x29, x30.
        split; [exact MU03|]. split; [exact WM03|]. split; [exact MI3|].
        split. { replace (Z.of_nat (length (done ++ [c']))) with (Z.of_nat (length (done ++ [c; x])) - 1) by (rewrite !app_length; cbn [length]; clear; lia).
                 rewrite HDA, last_addr_snoc. rewrite (last_addr_mid 0 done c [x]) in QG3. cbn [last_addr] in QG3. rewrite Z.eqb_refl in QG3. exact QG3. }
        split; [rewrite SB2; clear -HGB; lia|]. split; [clear -E0; lia|].
        split; [exact BL3|]. split; [exact BT3|]. split; [exact WF3|]. split; [exact HDA|].
        split; [exact TMP3'|]. split; [exact TLD3|]. split; [clear -OKx'; lia|].
        split; [intros E3'; exfalso; destruct ts; discriminate E3'|].
        split; [exact SF1|]. split; [exact SF2|]. split; [intros b' H'; exact (surg_addrs _ _ _ _ _ _ H')|].
        split; [exact SL|]. split; [rewrite SB1, SB2; clear; lia|].
        rewrite (mloop_fit c x [] FIT). cbn [fst snd mloop]. subst c' x'. split; [reflexivity|]. split; [reflexivity| reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition merge_post (SP : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
      (gs ts : list bnode) (TL : Z) (tf : word) (lo : Z) (W : list (Z * Z)) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Lms',$35.(<.P,(14.&40.)(26.(14.&8.))Lm',P,(14.&40.)(26.(14.&8.))(<.(0.$1.)Lgs',(0.$1.)(<.(0.$1.)Lts',(0.$1.)(<.$3.LTL',$3.(<.(14.&40.)Ltf',(14.&40.)(<.(14.&40.)Lx5,(14.&40.)(<.(14.&40.)Lx6,(14.&40.)(<.(14.&40.)Lx7,(14.&40.)(<.(14.&40.)Lx11,(14.&40.)(<.(14.&40.)Lx12,(14.&40.)(<.(14.&40.)Lx13,(14.&40.)(<.(14.&40.)Lx14,(14.&40.)(<.(14.&40.)Lx15,(14.&40.)(<.(14.&40.)Lx16,(14.&40.)(<.(14.&40.)Lx17,(14.&40.)(<.(14.&40.)Lx28,(14.&40.)(<.(14.&40.)Lx29,(14.&40.)(<.(14.&40.)Lx30,(14.&40.)(=.(31.(7.(1=.$3.$3.)(1?.$3.$3.O5.O1:.)(7.(1=.$3.$3.)(1?.$3.$3.(12.$24.+378.)(12.$24.+398.))(7.(1=.$3.$3.)(1?.$3.$3.O1:.(12.O1:.+20.))O4.)))O1.R12.)(=.(32.$2>.O1.R12.)(=.(33.$2>.R12.)(=.(3;.$2>.R12.(12.$24.+378.)(7.$41.(42.(23.&40.(27.(10.$1.R11.))))(7.$41.(42.(23.&40.(49.R11.)))(7.$41.(42.(23.&40.(4:.=R11.)))(7.$41.(42.(23.&40.(11.R11.)))(9.$41.))))))(=.(4;.R12.R11.)(=.(4;.R12.R10.)(=.(4<.VhAR,(6.$1.R10.R11.))(=.(>.$3.(49.R11.)(49.O9.))(=.(3;.$2>.R12.O1:.(7.$41.(42.(23.&40.(27.(10.$1.R10.))))(7.$41.(42.R>.)(7.$41.(42.(23.&40.R?.))(7.$41.(42.(23.&40.(11.R10.)))(9.$41.))))))(=.P,(3=.(>.(0.$1.)R10.(9.$1.)))(=.(>.$3.R10.(4:.=R11.))(>.(14.&40.)R?.(23.&40.(49.R11.))))(=.(=.(1;.=R?.)(18.R?.(1:.+2.+40.)))(=.P,(>.(0.$1.)R10.(9.$1.))(=.(>.$3.R10.O7.)(>.(14.&40.)R?.O6.))(=.(>.(0.(14.&40.))(15.$1.(14.&40.)$16.R11.)(15.$1.(14.&40.)$16.O9.))(=.(>.(0.(14.&40.))(15.$1.(14.&40.)$16.R10.)(15.$1.(14.&40.)$16.O8.))(=.Pb',$1.P,(;.$1.R1.(6.$1.R11.R12.))(<.$1.Lb,$1.(=.(;.$1.R1.(6.$1.O8.O9.))(>.$3.(5.R3.)(5.R1.))))(=.(>.$?.(10.$1.(6.$1.R10.R11.))(10.$1.(6.$1.O8.O9.)))(=.(>.$3.(12.(11.R10.)(11.R11.))(12.(11.O8.)(11.O9.)))(=.(44.$2>.R12.O5.O1:.)(=.(>.(0.$1.)R11.(20.(0.$1.)(0.$1.)(50.O9.)))(=.(>.(0.$1.)R10.(6.$1.O8.(21.(0.$1.)(0.$1.)(50.O9.))))(>.$35.R13.(36.(22.O19.(23.&40.O1:.)O18.O17.R=.R<.R;.O16.O15.(23.&40.(12.$24.+378.))R:.R9.R8.R7.R6.R5.R4.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R3.R2.R1.O:.)O3.(45.O19.)O2.(38.(14.&40.))R12.(39.$2>.)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00X0?L1322716074.8  L26137658151.7 L30035755762.10L30041936619.13L32027975233.0 L3453638010.5  L34585039509.1 L36042382352.93L38235734261.1 L38389436334.3 L38389436334.4 L38389688417.8 L38542770450.3 L38542886958.10L38549002295.13L39170601649.13L39280637297.0 L49380034775.5 L50527533039.6 L50527533039.7 L51491899878.7 L51492187689.8 L53516864658.10L53860705757.3 L5423397493.2  L5423477581.10 L5429879636.13 L57628699659.5 L58240380758.8 L58499548348.5 L59314873579.82L59315137787.4 L61031760050.2 L65636229322.5 L6619000599.5  L6701288080.6  L67092038960.2 L67113290310.81L7059421839.2  L8941806907.13 00000<00Q01101\01]02202802O02S02\02h03103<03R03n04E04F04Z05305J05d05j06606A06I06\07507C07a08608I08W08^08n09609M09U09j0:10:PS2SP2lo1y2Y1S1b1x4rest2ts3BND3TB0S3hAR2ts2SP2lo3BND5LOIMG3SPL3SPHS3hAR1b3gs12ts2SP2lo3BND5LOIMG3SPL3SPH4OKb'SS3hAR2SP2lo5LOIMG3SPLS4restS3hAR1b1x4rest2ts2bb2OKS2loS2SP1y2HyS2SP2lo1y2HyS2SP1y2Y3S2SP2lo3SPLS3hAR2ts2SP2lo3BND3SPLS3hAR1b3gs12ts2SP2lo3BND3SPLS3hAR1b3gs12ts3BND4OKb'SS3hAR1b3gs14OKb'3HDBS3hAR2SP2lo5LOIMG1b2OK2bbS3hAR2SP2lo5LOIMG2bb2OKS3hAR2SP2lo5LOIMG3SPL1y2HyS1y2Y2S3hAR2ts3BNDS2SP2lo3SPLS2SP3SPHS3hAR2ts2SP3BND3SPHS3hAR1b3gs12ts2SP3BND3SPHS2SP2lo1W1y2HyS1b1x4rest2L24ext24HGB22E23L2BS3hAR2SP2lo5LOIMG3SPLS3hAR1b1x1r2ts2H11HS3hAR1b4OKb'1XS2SP2loS2SP2lo3SPL1y2HyS3hAR2SPS1b1x4rest2L24ext24HGB2S2SP3SPHS3hAR1b1x1r2ts3OKb2H1S2SP2loS3hAR1b3gs12ts3BND3GB03TB04OKb'". (* [comment removed for export] *)
  Lemma merge_spec : ltac2:(CDefT.buildp (gd_tbl_AW_Merge ()) "Pgs,(0.$1.)Pts,(0.$1.)Pra,(14.&40.)Pgp,(14.&40.)Ptp,(14.&40.)Pt0,(14.&40.)Pt1,(14.&40.)Pt2,(14.&40.)Ps0,(14.&40.)Ps1,(14.&40.)Pa2,(14.&40.)Pa3,(14.&40.)Pa4,(14.&40.)Pa5,(14.&40.)Pa6,(14.&40.)Pa7,(14.&40.)Ps2,(14.&40.)Ps3,(14.&40.)Ps4,(14.&40.)Ps5,(14.&40.)Ps6,(14.&40.)Ps7,(14.&40.)Ps8,(14.&40.)Ps9,(14.&40.)Ps10,(14.&40.)Ps11,(14.&40.)Pt3,(14.&40.)Pt4,(14.&40.)Pt5,(14.&40.)Pt6,(14.&40.)Ptf,(14.&40.)PSP,$3.PTL,$3.Plo,$3.PW,(0.(1=.$3.$3.))PF,(25.&5.(14.&40.))Pfc,(14.&20.)Pm,P,(14.&40.)(26.(14.&8.))P,(18.(12.(12.(11.R25.)(11.R26.))(29.+2000.(27.(10.$1.R26.))))(1:.+2.+3<.))P,(18.(27.(10.$1.(6.$1.R26.R27.)))(1:.+2.+28.))P,(=.(1;.=R8.)(18.R8.(1:.+2.+40.)))P,(4<.VhAR,(6.$1.R28.R29.))P,Pb,$1.P,(;.$1.R1.(6.$1.R2:.R2;.))(2<.VCS,(5.R2.)+2000.)P,Pb,$1.Py,$3.P,(;.$1.R2.(6.$1.R2<.R2=.))P,(4>.R<.R2.)(3=.(=.(1;.(5.R4.)R3.)(18.R3.(12.(5.R4.)+2000.))))P,Py,$3.P,(=.(1;.R<.R1.)(18.R1.(12.R>.+20.)))(4>.R<.R2.)P,(3;.$2>.R8.(12.$24.+378.)(7.$41.(42.(23.&40.(27.(10.$1.R2=.))))(7.$41.(42.(23.&40.(49.R2=.)))(7.$41.(42.(23.&40.(4:.=R2=.)))(7.$41.(42.(23.&40.(11.R2=.)))(9.$41.))))))P,(4;.R9.R2>.)P,(4;.R:.R2>.)P,P,(3=.(>.(0.$1.)R2?.(9.$1.)))(=.(>.$3.R11.(4:.=R30.))(>.(14.&40.)R13.(23.&40.(49.R30.))))P,(3;.$2>.R<.R12.(7.$41.(42.(23.&40.(27.(10.$1.R30.))))(7.$41.(42.R13.)(7.$41.(42.(23.&40.R11.))(7.$41.(42.(23.&40.(11.R30.)))(9.$41.))))))P,(44.$2>.R=.R11.R13.)P,(1;.(2:.VhAR,)R12.)P,(1;.R13.(13.R15.+10.))P,(1;.(12.R16.+20.)(1:.+2.+3>.))P,(2<.VCS,R15.(13.(12.R17.+20.)R15.))P,(33.$2>.R12.)(34.$2>.VAL,VCS,(51.R19.R36.R35.R34.R30.R2?.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1;.R38.R37.R18.R1:.R17.R16.R15.R14.R13.)(36.(22.R36.(23.&40.R19.)R35.R34.R33.R32.R31.R30.R2?.(23.&40.(12.$24.+378.))(23.&40.R19.)R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R15.(23.&40.$47.)R14.(38.(14.&40.))R13.(39.$2>.)))")
(* [comment removed for export] *).
  Proof.
    intros gs ts ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 tf SP TL lo W F fc m
      BND LENB TLB WF CSN NW SW QG BG BT TLD TMP ST LOIMG SPL SPH SCS MI.
    pose proof (bwf_app_r _ _ WF) as WFg. pose proof (proj1 WFg) as OKg. pose proof (proj1 (bwf_app_l _ _ WF)) as OKts.
    pose proof (bsum_nonneg _ OKg) as GB0. pose proof (bsum_nonneg _ OKts) as TB0.
    (* [comment removed for export] *)
    assert (DONE0 : forall m' x5 x11 x14, fst (merge_out gs) = gs -> snd (merge_out gs) = [] ->
              munch [(lo, SP); (A_INSTANCE + 912, A_INSTANCE + 920)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
              rw_cells asegs m' (A_INSTANCE + 888) [C8 (Z_to_bv 64 (Z.of_nat (length gs))); C8 (Z_to_bv 64 (hd_addr gs)); C8 (Z_to_bv 64 (last_addr 0 gs)); C8 (Z_to_bv 64 (bsum gs))] ->
              stk asegs m' lo SP ->
              merge_post SP ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 gs ts TL tf lo W F fc m
                (MS (mkR ra (Z_to_bv 64 SP) gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 (A_INSTANCE + 888)) x11 a2 a3 x14 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs))).
    { intros m' x5 x11 x14 EF EX MU' WM' MI' QG' ST'. unfold merge_post.
      exists m', gs, ts, TL, tf, x5, t1, t2, x11, a2, a3, x14, a5, a6, a7, t3, t4, t5.
      split. { eapply munch_weaken; [| exact MU']. unfold sub_fp, A_INSTANCE. cbn [outside]. clear. intros y Hy. lia. }
      split; [exact WM'|]. split; [exact MI'|]. split; [exact QG'|].
      split. { unfold blist. eapply blistT_transport; [exact BG| exact OKg| exact MU'| exact WM'|].
               intros b Hb. pose proof (bwf_ok_in _ _ WFg Hb) as OK. unfold bn_ok in OK. unfold A_INSTANCE. cbn. clear -OK LOIMG. lia. }
      split. { unfold blist. eapply blistT_transport; [exact BT| exact OKts| exact MU'| exact WM'|].
               intros b Hb. pose proof (bwf_ok_in _ _ (bwf_app_l _ _ WF) Hb) as OK. unfold bn_ok in OK. unfold A_INSTANCE. cbn. clear -OK LOIMG. lia. }
      split; [exact WF|]. split; [reflexivity|].
      split. { eapply rw_cells_transport; [exact TMP| exact MU'| exact WM'| unfold A_INSTANCE; cbn; clear -SPL LOIMG; lia]. }
      split; [exact TLD|]. split; [exact TLB|]. split; [intros _; split; reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split; [intros b' H'; exists b'; split; [exact H'| reflexivity]|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact ST'|]. split; [symmetry; exact EF|]. split; [rewrite EX, app_nil_r; reflexivity| reflexivity]. }
    destruct gs as [|b gs1].
    - (* [comment removed for export] *)
      eapply evtA_mono.
      { eapply (mb_entry ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  (Z_to_bv 64 (last_addr 0 [])) SP SP (Z.of_nat (@length bnode [])) 0 (bsum []) 0 0 0 lo F fc m);
          try first [exact QG | exact ST | exact LOIMG | exact MI].
        all: try (intros X; exfalso; apply X; reflexivity).
        all: try (eapply crange_sub; [exact SCS| clear; lia| clear; lia]).
        all: clear -SPL SPH LOIMG GB0 TB0 BND; cbn in *; lia. }
      cbv beta. intros ms' (m' & MU' & WM' & MI' & QG' & [(_ & ST' & x5 & x11 & x14 & ->) | (X & _)]); [| exfalso; apply X; reflexivity].
      apply DONE0; first [assumption| reflexivity].
    - flat constr:((bwf_cons_inv _ _ WFg)) 3%nat. intros OKb WFg1 APb. pose proof OKb as OKb'. unfold bn_ok in OKb'.
      unfold blist in BG. flat constr:(BG) 2%nat. flclear BG. intros Nb BG1. flat constr:(Nb) 3%nat. intros HB HDb BWb.
      assert (HD1 : 0 <= hd_addrT gs1 0 < 2^64 /\ (hd_addrT gs1 0 = 0 <-> gs1 = [])).
      { destruct gs1 as [|x r]; cbn. { split; [clear; lia| tauto]. } pose proof (proj1 WFg1) as OK1. inversion OK1; subst. unfold bn_ok in *. split; [lia|]. split; [intros; exfalso; lia| congruence]. }
      flat constr:(HD1) 2%nat. flclear HD1. intros HDB HD0.
      eapply evtA_cut.
      { eapply (mb_entry ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                  (Z_to_bv 64 (last_addr 0 (b :: gs1))) SP SP (Z.of_nat (length (b :: gs1))) (bn_addr b) (bsum (b :: gs1))
                  (hd_addrT gs1 0) (bn_size b) (bn_count b) lo F fc m);
          try first [exact QG | exact ST | exact LOIMG | exact MI].
        all: try (intros _; split; [exact HB|]; split; [apply CSN; apply in_or_app; right; left; reflexivity|]; clear -OKb' HDB; lia).
        all: try (eapply crange_sub; [exact SCS| clear; lia| clear; lia]).
        all: clear -SPL SPH LOIMG GB0 TB0 BND OKb'; cbn [bsum length] in *; lia. }
      cbv beta. intros ms' (m' & MU' & WM' & MI' & QG' & [([X|X] & ST' & x5 & x11 & x14 & ->) | (_ & X & ST' & [j FR'] & ->)]).
      + exfalso. clear -X OKb'. lia.
      + (* [comment removed for export] *) apply evtA_done. assert (gs1 = []) as -> by (apply (proj1 HD0); exact X). apply DONE0; first [assumption| reflexivity].
      + (* [comment removed for export] *)
        destruct gs1 as [|x rest]; [exfalso; apply X; apply HD0; reflexivity|]. cbn [hd_addrT] in *.
        assert (TR : forall bb nx, bn_ok bb -> bnode_at m bb nx -> bnode_at m' bb nx).
        { intros bb nx OK N. eapply bnode_at_transport; [exact N| exact MU'| exact WM'| | unfold bn_ok in OK; lia]. unfold bn_ok in OK. unfold A_INSTANCE. cbn. clear -OK LOIMG. lia. }
        eapply evtA_cut.
        { eapply (mb_loop (S (length rest)) [] b x rest ts) with (TL := TL) (tf := tf) (gb := bsum (b :: x :: rest)) (m0 := m') (W := W);
            cbn [app]; try first [exact WF | exact CSN | exact QG' | exact TLD | exact TLB | exact LENB | exact MI' | apply wmono_refl | apply munch_refl].
          * clear. lia.
          * rewrite Z.add_0_r. reflexivity.
          * clear. lia.
          * exact BND.
          * exact NW.
          * unfold blist. eapply blistT_map_nodes; [| exact (conj Nb BG1)]. intros bb nx Hbb N. apply TR; [| exact N]. eapply bwf_ok_in; [exact WFg| exact Hbb].
          * unfold blist. eapply blistT_map_nodes; [| exact BT]. intros bb nx Hbb N. apply TR; [| exact N]. eapply bwf_ok_in; [exact (bwf_app_l _ _ WF)| exact Hbb].
          * eapply rw_cells_transport; [exact TMP| exact MU'| exact WM'| unfold A_INSTANCE; cbn; clear -SPL LOIMG; lia].
          * eapply crange_sub; [exact SCS| clear -SPL; lia| clear; lia].
          * clear -LOIMG SPL. lia.
          * clear -SPH. lia. }
        intros ms2 PP. unfold mb_post in PP.
        flat constr:(PP) 35%nat. flclear PP. intros m2 L2 ts2 ext2 TL2 cur2 tf2 y6 y7 y13 y28 y29 y30 MU2 WM2 MI2 QG2 HGB2 E2 BL2 BT2 WF2 HD2 TMP2 TLD2 TLB2 TE2 FM2 FT2 ADDR2 LEN2 SUM2 ELF2 ETS2 ->.
        pose proof (bsum_nonneg _ (proj1 (bwf_app_r _ _ WF2))) as L2B.
        assert (FR2 : mb_frame m2 SP j ra).
        { unfold mb_frame in *. eapply rw_cells_transport; [exact FR'| eapply (munch_restrict _ _ _ (SP + -16) 16); [exact MU2|]| exact WM2| cbn; clear -SPL LOIMG; lia].
          intros y Hy. unfold mb_W, A_INSTANCE. cbn [outside]. cbn in Hy. split; [clear -Hy SPL LOIMG; lia|]. split; [clear -Hy; lia|].
          apply SW. clear -Hy SPL; lia. }
        assert (ST2 : stk asegs m2 lo (SP + -16)).
        { eapply stk_transport; [exact ST'| exact MU2| exact WM2|]. intros y Hy. left. unfold mb_W, A_INSTANCE. cbn [outside].
          split; [clear -Hy SPL LOIMG; lia|]. split; [clear -Hy; lia|]. apply SW. clear -Hy SPL; lia. }
        eapply evtA_mono.
        { eapply mb_exit with (m0 := m2) (W := []) (lo := lo);
            try first [exact QG2 | exact FR2 | exact ST2 | exact LOIMG | exact MI2 | apply wmono_refl | apply munch_refl].
          * clear -HGB2 E2 L2B. lia.
          * clear -BND GB0 TB0. cbn [bsum length] in *. lia.
          * clear -SPH. lia.
          * clear -SPL. lia.
          * eapply crange_sub; [exact SCS| clear; lia| clear; lia]. }
        cbv beta. intros ms3 (m3 & MU3 & WM3 & MI3 & QG3 & ST3 & ->). unfold merge_post.
        exists m3, L2, ts2, TL2, tf2, (Z_to_bv 64 0), y6, y7, (Z_to_bv 64 (bsum (b :: x :: rest) - ext2)), (Z_to_bv 64 ext2), y13,
               (Z_to_bv 64 cur2), (Z_to_bv 64 1021), (Z_to_bv 64 18446744073709543424), (Z_to_bv 64 8192), y28, y29, y30.
        split. { eapply munch_trans; [eapply munch_weaken; [| exact MU'] | eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MU3]]];
                 unfold sub_fp, mb_W, A_INSTANCE; cbn [outside]; clear; intros y (Y1 & Y2 & Y3 & Y4); repeat split; try exact Y4; try exact I; lia. }
        split; [eapply wmono_trans; [exact WM'| eapply wmono_trans; [exact WM2| exact WM3]]|]. split; [exact MI3|].
        split; [replace (bsum L2) with (bsum (b :: x :: rest) - ext2) by (clear -HGB2; lia); exact QG3|].
        split. { unfold blist. eapply blistT_transport; [exact BL2| exact (proj1 (bwf_app_r _ _ WF2))| exact MU3| exact WM3|].
                 intros bb Hbb. pose proof (bwf_ok_in _ _ (bwf_app_r _ _ WF2) Hbb) as OK. unfold bn_ok in OK. unfold A_INSTANCE. cbn. clear -OK LOIMG SPL. lia. }
        split. { unfold blist. eapply blistT_transport; [exact BT2| exact (proj1 (bwf_app_l _ _ WF2))| exact MU3| exact WM3|].
                 intros bb Hbb. pose proof (bwf_ok_in _ _ (bwf_app_l _ _ WF2) Hbb) as OK. unfold bn_ok in OK. unfold A_INSTANCE. cbn. clear -OK LOIMG SPL. lia. }
        split; [exact WF2|]. split; [exact HD2|].
        split; [eapply rw_cells_transport; [exact TMP2| exact MU3| exact WM3| unfold A_INSTANCE; cbn; clear -SPL LOIMG; lia]|].
        split; [exact TLD2|]. split; [exact TLB2|]. split; [exact TE2|]. split; [exact FM2|]. split; [exact FT2|]. split; [exact ADDR2|].
        split; [exact LEN2|]. split; [exact SUM2|]. split; [exact ST3|]. split; [exact ELF2|]. split; [exact ETS2| reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Merge.

End ARUN_1.
