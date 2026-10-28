(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXAW Require Import LxFlat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00c9ece02f24f0bb 0 4 0 1 37 1 45 1 46 1P0110063ca423c810 2 36 1 1 8 3 2 1 49 1 50 1 4 0 2 48 2 51 2 52 16 1 1 8 3 3 1 48 1 51 1 6 0 2 37 16 40 2 49 2 50 2 52 16P016961eb5dd1a3c6 0 4 0 1 37 1 45 1 46 1P01f93c6ac1c5dbf0 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P02aa3ad38754417b 2 36 1 1 8 3 2 1 49 1 50 1 4 0 2 48 2 51 2 52 16 1 1 8 3 3 1 48 1 51 1 6 0 2 37 16 40 2 49 2 50 2 52 16P0326d1fc884db03a 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P036143cecc9f08ea 0 4 0 1 37 1 45 1 46 1P04365de0235a35fc 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P04574f75c68c79af 0 4 0 1 37 1 45 1 46 1P062a2edc152047d8 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P06af32747eed7294 2 36 1 1 8 3 2 1 49 1 50 1 4 0 2 48 2 51 2 52 16 1 1 8 3 3 1 48 1 51 1 6 0 2 37 16 40 2 49 2 50 2 52 16P0861d41df82ab038 2 36 1 1 8 3 2 1 49 1 50 1 4 0 2 48 2 51 2 52 16 1 1 8 3 3 1 48 1 51 1 6 0 2 37 16 40 2 49 2 50 2 52 16P08724b599e3f96b6 2 36 1 1 8 3 2 1 49 1 50 1 4 0 2 48 2 51 2 52 16 1 1 8 3 3 1 48 1 51 1 6 0 2 37 16 40 2 49 2 50 2 52 16P090ed625c3b19578 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P09f1a68ea5176e83 1 2 8 2 0 1 45 1 8 2 42 1 46 1 2 47 1 48 1P0e97218fbfb9c66d 0 4 0 8 41 8 45 8 46 8P105e80efe8011484 0 4 0 1 37 1 45 1 46 1P11e72e59b71c36bd 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P12c62bea05346c96 0 2 0 1 45 1P12ca74dc396f7654 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P12da7387a4f68ade 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P12e16e5bea9b8f72 0 4 0 1 37 1 45 1 46 1P1308e95d3bd8ce0a 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P1450ebef99eea48a 2 36 1 1 8 3 2 1 49 1 50 1 4 0 2 48 2 51 2 52 16 1 1 8 3 3 1 48 1 51 1 6 0 2 37 16 40 2 49 2 50 2 52 16P146d56d1278eff27 0 4 0 1 37 1 45 1 46 1P1481166e56957917 0 4 0 1 37 1 45 1 46 1P1542f68a5de23895 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P15a6a66a838e2606 0 4 0 1 37 1 45 1 46 1P162b55e85c8a0030 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P16787d3e726f1a87 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P1820f3115f92bbeb 0 4 0 1 37 1 45 1 46 1P18499176c6e47d00 0 4 0 1 37 1 45 1 46 1P1893218ef120b1fd 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P195f74a55c50db05 0 4 0 1 37 1 45 1 46 1P198996c02965c1ec 0 2 0 1 46 1P198b446d80c62094 2 36 1 1 8 3 2 1 49 1 50 1 4 0 2 48 2 51 2 52 16 1 1 8 3 3 1 48 1 51 1 6 0 2 37 16 40 2 49 2 50 2 52 16P1b22cdba7dfa24ac 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P1b3cf0daaf659a53 0 4 0 1 30 4294967296 32 1 43 1P1b9baf8deee220d0 0 4 0 1 37 1 45 1 46 1P1c8fd202a8b7efa1 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P1dbc67f4400d22a6 2 36 1 1 8 3 2 1 49 1 50 1 4 0 2 48 2 51 2 52 16 1 1 8 3 3 1 48 1 51 1 6 0 2 37 16 40 2 49 2 50 2 52 16P1e07e4ee8e987574 0 4 0 1 37 1 45 1 46 1P1e69a8e36727d865 0 2 0 1 2 1P1e75f099d7602425 0 4 0 1 37 1 45 1 46 1P20e66258a66d62c7 0 3 0 1 36 1 45 1P2123e076c87fc602 0 2 0 1 37 1P21b595862a40d733 0 4 0 1 37 1 45 1 46 1P21e90a3718df766f 0 4 0 1 37 1 45 1 46 1P21f69dddd334875e 0 4 0 1 37 1 45 1 46 1P21fed699799db296 0 4 0 1 37 1 45 1 46 1P2305a9872cd3d713 0 4 0 1 37 1 45 1 46 1P24f95a827b5cfe15 0 4 0 1 37 1 45 1 46 1P253f88d9b98f70cb 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P260e54556ecbd101 0 4 0 1 37 1 45 1 46 1P26769c912c4aa922 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P2765772bd2c4017c 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P27b9342979f3d741 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P27c55f4fbdba1217 2 36 1 1 8 3 2 1 49 1 50 1 4 0 2 48 2 51 2 52 16 1 1 8 3 3 1 48 1 51 1 6 0 2 37 16 40 2 49 2 50 2 52 16P28097473a42a3f9c 1 1 8 2 42 1 46 1 3 0 1 45 1 47 8P28f280e053fd7422 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P29979d3c9b223d41 0 4 0 1 37 1 45 1 46 1P2a8b6a41f3cfeb48 0 4 0 1 37 1 45 1 46 1P2b2b0feec504f766 0 4 0 1 31 4294967296 33 1 44 1P2b6ac7d7e0dbd225 0 4 0 1 37 1 45 1 46 1P2bae3acb981158f4 0 4 0 1 31 4294967296 33 1 44 1P2c9c5b11d81928c3 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P2d1688a0b6c9a117 0 4 0 1 37 1 45 1 46 1P2d5338c270f0f6e9 0 4 0 1 37 1 45 1 46 1P2d66d6e5d8c42f35 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P2ded814445153b11 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P2df8ae8cd78a110e 0 2 0 1 1 1P2e2ed2216228c837 0 4 0 1 37 1 45 1 46 1P2e94ea53bc612535 0 4 0 1 37 1 45 1 46 1P2ea86ae36e287f74 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P2f4cfb7f77d42a19 0 4 0 1 37 1 45 1 46 1P2f6012d8365d1819 2 36 1 1 8 3 2 1 49 1 50 1 4 0 2 48 2 51 2 52 16 1 1 8 3 3 1 48 1 51 1 6 0 2 37 16 40 2 49 2 50 2 52 16P302036d23e765a01 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P32275653e087fc99 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P324c1217ccd3736a 0 4 0 1 37 1 45 1 46 1P326cfd6c208496a8 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P3467208464528cf3 0 4 0 1 31 4294967296 33 1 44 1P3536dfc757f7eaa5 0 4 0 1 37 1 45 1 46 1P358d25950b2a6d28 2 36 1 1 8 3 2 1 49 1 50 1 4 0 2 48 2 51 2 52 16 1 1 8 3 3 1 48 1 51 1 6 0 2 37 16 40 2 49 2 50 2 52 16P359a2408b2531e8b 0 4 0 1 37 1 45 1 46 1P362b41855a09cd1d 2 36 1 1 8 3 2 1 49 1 50 1 4 0 2 48 2 51 2 52 16 1 1 8 3 3 1 48 1 51 1 6 0 2 37 16 40 2 49 2 50 2 52 16P36ad3f9ca616dd8f 0 4 0 1 37 1 45 1 46 1P379f544b9adc0be4 0 4 0 1 37 1 45 1 46 1P379fd398f922a366 0 4 0 1 37 1 45 1 46 1P37c0440a75847c9e 0 4 0 1 37 1 45 1 46 1P39461b68f887e05c 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P3952887573fb9b5e 0 4 0 1 37 1 45 1 46 1P3a5b8da97ce8e046 0 4 0 1 37 1 45 1 46 1P3a6980de44008c2a 0 2 0 1 45 1P3a882e53e0a0ca6c 2 36 1 1 8 3 2 1 49 1 50 1 4 0 2 48 2 51 2 52 16 1 1 8 3 3 1 48 1 51 1 6 0 2 37 16 40 2 49 2 50 2 52 16P3acd09d191d97050 1 2 16 2 0 1 47 1 16 2 1 1 46 1 2 48 1 49 1P3b16679c24c815ba 0 4 0 1 37 1 45 1 46 1P3b66953e5b14dc4a 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16P3b79b73f685164fe 1 1 16 2 1 1 46 1 4 38 1 39 1 47 1 48 16N0254c41c5c9668e8N02c3ea23a1f24a97N065327a1449a2963N0b3c996e6e3df74eN1657be3a135da9e9N186ddb6b455b2e5cN262e32eb7b5bc999N26dc4a5c9a777d8cN292899111d277a62N298677e8d9fb3f1bN29a21ebb7874746bN2ba15442c671fc8cN31a9cfcbd0a80a28N31acfab5570c89c2N32bc7321553e76c0N3327d0fc0b05e04aN337ce332528e791fN377d8bf44462c883N3b35722deb99d13a"%lxh.
Ltac2 gd_tbl_AW_DepotA () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.add"; "ARUN_1.A_DEP"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "ARUN_1.A_DEP_MAP1"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "ARUN_1.dmap1v"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Nat.of_num_uint"; "Corelib.Init.Number.UIntDecimal"; "Corelib.Init.Decimal.D3"; "Corelib.Init.Decimal.D2"; "Corelib.Init.Decimal.D7"; "Corelib.Init.Decimal.D6"; "Corelib.Init.Decimal.D8"; "Corelib.Init.Decimal.Nil"; "Stdlib.ZArith.BinInt.Z.of_nat"; "stdpp.bitvector.definitions.bv"; "ARUN_1.dnode"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.option"; "ARUN_1.dtab"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "ARUN_1.dmap1"; "ARUN_1.dblk"; "Stdlib.ZArith.BinInt.Z.div"; "ARUN_1.dnodes"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Peano.lt"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "ARUN_1.A_DPUT_HASH"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "ARUN_1.A_DEP_NODES"; "ARUN_1.A_DPUT_FIND"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "ARUN_1.DepotA.dput_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "ARUN_1.A_MUR1"; "ARUN_1.A_MUR2"; "ARUN_1.A_MUR3"; "Corelib.Init.Logic.or"; "ARUN_1.DepotA.dput_pro_post"; "ARUN_1.A_STACK_DEPOT_PUT"; "ARUN_1.dwf"; "ARUN_1.DepotA.dfind_post"].

Section ARUN_1. Context {hAR : arun}.
Definition A_STACK_DEPOT_PUT : Z := 0x0895a0.
Definition A_DPUT_HASH : Z := 0x089650.
Definition A_DPUT_FIND : Z := 0x0896e0.
Definition A_DEP : Z := 0x1eb8d8.                 (* [comment removed for export] *)
Definition A_DEP_N : Z := 0x5eb8d8.               (* [comment removed for export] *)
Definition A_DEP_NODES : Z := 0x5eb8e0.           (* [comment removed for export] *)
Definition A_DEP_MAP1 : Z := 0x5eb8e8.            (* [comment removed for export] *)
Definition A_MUR1 : Z := 0x10310.                 (* [comment removed for export] *)
Definition A_MUR2 : Z := 0x103e8.
Definition A_MUR3 : Z := 0x102e8.

(* [comment removed for export] *)
Definition dtab (m : mem) (N : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotA ()) "Pi,$0.P,(1.(2.=R1.)(3.R1.(4.+2.+14.)))(5.$0.Lv,$0.(1.(6.$7.O2.(8.$9.(:.+4.R3.))(;.$<.(=.(>.&40.R1.))(?.$<.)))(1.(2.=R1.)(2.R1.O1.))))")
(* [comment removed for export] *).

#[using="Type"] Lemma swrap32_low : forall a t, 0 <= a < 2^31 -> 0 <= t -> bv_swrap 32 (a + t * 4294967296) = a.
Proof.
  intros a t Ha Ht. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ (Z.of_N 32 - 1)) with 2147483648. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 / 2) with 2147483648.
  replace (a + t * 4294967296 + 2147483648) with ((a + 2147483648) + t * 4294967296) by lia.
  rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Definition dblk (nb : list Z) (k : Z) : Z := nth (Z.to_nat k) nb 0.
Definition dnode (nb : list Z) (s : Z) : Z := dblk nb (s / 65536) + 16 * (s mod 65536).
Definition dmap1v (nb : list Z) (k : Z) : Z := if k <? Z.of_nat (length nb) then dblk nb k else 0.
Definition dmap1 (m : mem) (nb : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotA ()) "(1.Pk,$0.P,(1.(2.=R1.)(3.R1.+8000.))(6.$7.O2.(8.$10.(:.+8.R2.))(;.$<.(11.(>.&40.(12.O1.R2.)))(?.$<.)))(1.(13.$0.Lb,$0.(1.(2.+65?000.R1.)(1.(2.(8.R1.(4.+2.+14.))(14.VhAR,))(15.$0.(16.R1.+1000.)=)))O1.)(17.(18.$0.O1.)(19.(1:.(1;.(1<.(1=.(1>.(1?.$20.))))))))))")
(* [comment removed for export] *).
Definition dnodes (m : mem) (nb : list Z) (N : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotA ()) "Ps,$0.P,(1.(2.=R1.)(3.R1.(:.+10000.(21.(18.$0.O2.)))))(5.(22.&40.)Lhsh,(22.&40.)(5.(22.&40.)Lsid,(22.&40.)(5.$0.Llnk,$0.(1.(6.$7.O3.(23.O2.R5.)(;.$<.(11.R3.)(;.$<.(=.(>.&40.R1.))(;.$<.(=.R2.)(?.$<.)))))(1.(2.=R1.)P,(1.(2.+1.R5.)(2.R5.O1.))(3.R2.R6.))))))")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition dwf (nb : list Z) (N : Z) : Prop := 1 <= N < 2^31 - 2^28 /\ Z.of_nat (length nb) = N / 65536 + 1.

(* [comment removed for export] *)
#[using="Type"] Lemma dtab_transport : ltac2:(CDefT.buildp (gd_tbl_AW_DepotA ()) "PW,(24.$25.)Pm,P,(22.&40.)(26.(22.&8.))Pm',P,(22.&40.)(26.(22.&8.))PN,$0.P,(27.R3.R1.)P,(28.R5.R4.R3.)P,(29.$7.R5.R4.)P,(2:.R7.$9.(:.+4.(4.+2.+14.)))(27.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros W m m' N DT MU WM DJ i Hi. flat constr:((DT i Hi)) 3%nat. intros v TC VB. exists v. split; [|exact VB].
  eapply rw_cells_transport; [exact TC| exact MU| exact WM|].
  cbn [cells_size csize Nat.add]. clear -DJ Hi. induction W as [|[lo hi] W IH]; [exact I|].
  flat constr:(DJ) 2%nat. flclear DJ. intros D1 D2. split; [lia| apply IH; exact D2].
Qed.
#[using="Type"] Lemma dtab_mono : forall m N N', dtab m N -> N <= N' -> dtab m N'.
Proof. intros m N N' DT LE i Hi. flat constr:((DT i Hi)) 3%nat. intros v TC VB. exists v. split; [exact TC| lia]. Qed.
#[using="Type"] Lemma dmap1_transport : ltac2:(CDefT.buildp (gd_tbl_AW_DepotA ()) "PW,(24.$25.)Pm,P,(22.&40.)(26.(22.&8.))Pm',P,(22.&40.)(26.(22.&8.))Pnb,(24.$0.)P,(2;.R3.R1.)P,(28.R5.R4.R3.)P,(29.$7.R5.R4.)P,(2:.R7.$10.(:.+8.+8000.))(2;.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros W m m' nb (DM & DF & DL) MU WM DJ. split; [|split; [exact DF| exact DL]].
  intros k Hk. eapply rw_cells_transport; [exact (DM k Hk)| exact MU| exact WM|].
  cbn [cells_size csize Nat.add]. clear -DJ Hk. induction W as [|[lo hi] W IH]; [exact I|].
  flat constr:(DJ) 2%nat. flclear DJ. intros D1 D2. split; [lia| apply IH; exact D2].
Qed.
#[using="Type"] Lemma dnode_range : ltac2:(CDefT.buildp (gd_tbl_AW_DepotA ()) "Pnb,(24.$0.)Ps,$0.P,(13.$0.Lb,$0.(1.(2.+65?000.R1.)(1.(2.(8.R1.(4.+2.+14.))(14.VhAR,))(15.$0.(16.R1.+1000.)=)))R2.)P,(1.(2.=R2.)(3.R2.(:.+10000.(21.(18.$0.R3.)))))(1.(2.(2<.R4.(2=.R3.+10000.))(23.R4.R3.))(1.(2.(8.(23.R4.R3.)+10.)(8.(2<.R4.(2=.R3.+10000.))(4.+2.+14.)))(1.(15.$0.(16.(23.R4.R3.)+10.)=)(1.(2.+65?000.(2<.R4.(2=.R3.+10000.)))(2.(8.(2<.R4.(2=.R3.+10000.))(4.+2.+14.))(14.VhAR,))))))")
(* [comment removed for export] *).
Proof.
  intros nb s HF Hs. unfold dnode.
  assert (KB : 0 <= s / 65536 < Z.of_nat (length nb)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  pose proof (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb) as FN.
  flat constr:((proj1 FN HF (Z.to_nat (s / 65536)) 0 ltac:(lia))) 3%nat. intros B0 B1 BA. unfold dblk.
  pose proof (Z.mod_pos_bound s 65536 ltac:(lia)). pose proof (Z.div_mod (nth (Z.to_nat (s / 65536)) nb 0) 4096 ltac:(lia)).
  repeat split; lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma dnodes_transport : ltac2:(CDefT.buildp (gd_tbl_AW_DepotA ()) "PW,(24.$25.)Pm,P,(22.&40.)(26.(22.&8.))Pm',P,(22.&40.)(26.(22.&8.))Pnb,(24.$0.)PN,$0.P,(2>.R4.R2.R1.)P,(28.R6.R5.R4.)P,(29.$7.R6.R5.)P,(13.$0.Lb,$0.(1.(2.+65?000.R1.)(1.(2.(8.R1.(4.+2.+14.))(14.VhAR,))(15.$0.(16.R1.+1000.)=)))R5.)P,Pb,$0.P,(2?.$0.R1.R7.)(2:.R;.R2.(4.+2.+14.))(2>.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros W m m' nb N DN MU WM HF DJ s Hs. flat constr:((DN s Hs)) 6%nat. intros hsh sid lnk NC L0 LS.
  exists hsh, sid, lnk. split; [| split; [exact L0| exact LS]].
  eapply rw_cells_transport; [exact NC| exact MU| exact WM|].
  cbn [cells_size csize Nat.add]. flat constr:((dnode_range nb s HF Hs)) 5%nat. intros R0 R1 _ _ _.
  assert (IN : In (dblk nb (s / 65536)) nb).
  { unfold dblk. apply nth_In. assert (0 <= s / 65536 < Z.of_nat (length nb)) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]). lia. }
  specialize (DJ _ IN). clear -DJ R0 R1. induction W as [|[lo hi] W IH]; [exact I|].
  flat constr:(DJ) 2%nat. flclear DJ. intros D1 D2. split; [lia| apply IH; exact D2].
Qed.

#[using="Type"] Lemma dblk_facts : ltac2:(CDefT.buildp (gd_tbl_AW_DepotA ()) "Pnb,(24.$0.)Pk,$0.P,(13.$0.Lb,$0.(1.(2.+65?000.R1.)(1.(2.(8.R1.(4.+2.+14.))(14.VhAR,))(15.$0.(16.R1.+1000.)=)))R2.)P,(1.(2.=R2.)(3.R2.(21.(18.$0.R3.))))(1.(2.+65?000.(2<.R4.R3.))(1.(2.(8.(2<.R4.R3.)(4.+2.+14.))(14.VhAR,))(15.$0.(16.(2<.R4.R3.)+1000.)=)))")
(* [comment removed for export] *).
Proof.
  intros nb k HF Hk. unfold dblk. apply (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb); [exact HF| lia].
Qed.

#[using="Type"] Lemma shiftr32_tag : forall a t, 0 <= a < 2^32 -> 0 <= t -> Z.shiftr (a + t * 4294967296) 32 = t.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. Qed.
#[using="Type"] Lemma land32_low : forall a t, 0 <= a < 2^32 -> 0 <= t -> Z.land (a + t * 4294967296) 4294967295 = a.
Proof. intros. change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. change (2^32) with 4294967296.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma srliw16 : forall s, 0 <= s < 2^31 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 s) 16) = s / 65536.
Proof.
  intros s Hs. unfold bv_wrap, bv_swrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296. change (2 ^ (Z.of_N 32 - 1)) with 2147483648.
  rewrite (Z.mod_small s) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^16) with 65536.
  change (4294967296 / 2) with 2147483648. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
  assert (0 <= s / 65536 <= 2147483648 / 65536) by (split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]).
  rewrite Z.mod_small; [lia|]. cbn in H. lia.
Qed.

#[using="Type"] Lemma zext32_small : forall s, 0 <= s < 2^32 -> Z.shiftr (Z.shiftl s 32 mod 18446744073709551616) 32 = s.
Proof.
  intros s Hs. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change 18446744073709551616 with (2^32 * 2^32). rewrite Zmult_mod_distr_r, Z.div_mul by lia. apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma land16_mod : forall s, 0 <= s -> Z.land s 65535 = s mod 65536.
Proof. intros. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bucket_of : forall h, 0 <= h < 2^64 -> Z.shiftr (Z.shiftl h 44 mod 18446744073709551616) 42 = 4 * (h mod 2^20).
Proof.
  intros h Hh. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change 18446744073709551616 with (2^20 * 2^44). rewrite Zmult_mod_distr_r.
  change (2^44) with (4 * 2^42). rewrite Z.mul_assoc, Z.div_mul by lia. lia.
Qed.

Section DepotA.
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
  #[using="IMG ALWF CSOK"] Lemma dhash_loop : ltac2:(CDefT.buildp (gd_tbl_AW_DepotA ()) "Pk,$30.Pcur,$0.PTR,$0.Pws,(24.(22.&40.))Psize,$0.Pra,(22.&40.)Psp,(22.&40.)Pgp,(22.&40.)Ptp,(22.&40.)Pt0,(22.&40.)Pt1,(22.&40.)Pt2,(22.&40.)Ps0,(22.&40.)Ps1,(22.&40.)Pa3,(22.&40.)Pa7,(22.&40.)Ps2,(22.&40.)Ps3,(22.&40.)Ps4,(22.&40.)Ps5,(22.&40.)Ps6,(22.&40.)Ps7,(22.&40.)Ps8,(22.&40.)Ps9,(22.&40.)Ps10,(22.&40.)Ps11,(22.&40.)Pt3,(22.&40.)Pt4,(22.&40.)Pt5,(22.&40.)Pt6,(22.&40.)Pc,(22.&40.)Pacc,(22.&40.)Px5,(22.&40.)Px6,(22.&40.)PF,(31.&5.(22.&40.))Pfc,(22.&20.)Pm,P,(22.&40.)(26.(22.&8.))P,(32.#0.R25.)P,(15.$0.R25.(33.(8.R24.(:.+8.R22.))(:.+8.(21.R26.))))P,(2.R25.R26.)P,(34.$7.R4.R26.R25.)P,(15.$30.(18.(22.&40.)R26.)#1>.)P,(1.(2.+1.R26.)(2.R26.+1>.))P,(2.=R29.)P,(2.(8.R2:.+100.)(4.+2.+3?.))P,(35.VCS,R2;.+?0.)P,(36.$7.R:.)(37.$7.VAL,VCS,Lms',$38.(5.(22.&40.)Lacc',(22.&40.)(5.(22.&40.)Lx5',(22.&40.)(5.(22.&40.)Lx6',(22.&40.)(15.$38.R4.(39.(3:.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R15.(>.&40.(8.R31.(:.+8.R2?.)))R3.R25.(>.&40.(8.R31.(:.+8.R2?.)))R2.R1.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R11.(>.&40.+89674.)R10.(3;.(22.&40.))R?.(3<.$7.))))))(39.(3:.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R11.(>.&40.R2>.)R10.R21.(>.&40.(8.R2=.(:.+8.R2;.)))R?.R>.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R=.(>.&40.$3=.)R<.(3;.(22.&40.))R;.(3<.$7.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros cur TR ws size ra sp gp tp t0 t1 t2 s0 s1 a3 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 c acc x5 x6 F fc m
      HK HC HLO HTR HL HSZ T0 T1 TCS MI; [lia|].
    facts. unfold A_DPUT_HASH.
    (* [comment removed for export] *)
    assert (HI : (Z.to_nat ((cur - TR) / 8) < length ws)%nat) by (rewrite HL; lia).
    destruct (nth_error ws (Z.to_nat ((cur - TR) / 8))) as [w|] eqn:HN; [| apply nth_error_None in HN; lia].
    pose proof (u64arr_read asegs m TR ws ((cur - TR) / 8) w (wa cur) HTR HN ltac:(lia) ltac:(f_equal; lia)) as RD.
    zstep. clear RD.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases Kne; zify_cond Kne.
    - (* [comment removed for export] *)
      destruct k as [|k']; [exfalso; lia|].
      eapply evtA_mono. { eapply (IH (cur + 8) TR ws size); try eassumption; lia. }
      cbn beta. intros ms1 (acc' & x5' & x6' & ->). do 3 eexists. reflexivity.
    - apply evtA_done. replace (cur + 8) with (TR + 8 * size) by lia. do 3 eexists. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Definition dput_frame (mm : mem) (SP : Z) (fr : list byte) (TR szt : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotA ()) "(6.$7.O10.(8.O?.-70.)(;.$<.(3>.#8.O>.)(;.$<.(11.(>.&40.O=.))(;.$<.(11.(>.&40.O<.))(;.$<.(11.O1.)(;.$<.(11.O2.)(;.$<.(11.O3.)(;.$<.(11.O4.)(;.$<.(11.O5.)(;.$<.(11.O6.)(;.$<.(11.O7.)(;.$<.(11.O8.)(;.$<.(11.O9.)(;.$<.(11.O:.)(;.$<.(11.O;.)(?.$<.))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition dput_pro_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a7 : word)
      (F : bvmap 5 word) (fc : bv 32) (TR szt size v lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotA ()) "Lms',$38.(5.$0.Lh,$0.(5.$0.Lbi,$0.(5.(22.&40.)Lx2,(22.&40.)(5.(22.&40.)Lx4,(22.&40.)(5.(22.&40.)Lx5,(22.&40.)(5.(22.&40.)Lx6,(22.&40.)(5.P,(22.&40.)(26.(22.&8.))Lmm,P,(22.&40.)(26.(22.&8.))(5.(24.(22.&8.))Lfr,(24.(22.&8.))(1.(15.$38.R9.(39.(3:.O20.(>.&40.(8.O1?.-70.))O1>.O1=.O10.O?.O>.(>.&40.=)(>.&40.$9.)(>.&40.O3.)(>.&40.O3.)R6.(>.&40.+400008.)R5.R4.R3.O9.(>.&40.(8.$9.(:.+4.R7.)))(>.&40.R8.)(>.&40.$3?.)O17.(>.&40.+????.)(>.&40.+7???????.)(>.&40.$10.)(>.&40.O3.)O12.O11.O=.O<.O;.O:.)O8.(>.&40.$40.)O7.(3;.(22.&40.))R2.(3<.$7.)))(1.(28.(;.(41.$0.$0.)(42.$0.$0.O2.O1?.)(?.(41.$0.$0.)))O1.R2.)(1.(29.$7.O1.R2.)(1.(36.$7.R2.)(1.(43.R2.O1?.R1.O6.O5.O20.O1<.O1;.O1:.O19.O18.O17.O16.O15.O14.O13.)(1.(44.$7.R2.O2.(8.O1?.-70.))(1.(6.$7.R2.(8.$9.(:.+4.R7.))(;.$<.(=.(>.&40.O3.))(?.$<.)))(1.(1.(2.=R8.)(3.R8.(4.+2.+40.)))(1.(2.=R7.)(3.R7.(4.+2.+14.)))))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma dput_pro : ltac2:(CDefT.buildp (gd_tbl_AW_DepotA ()) "Pra,(22.&40.)Pgp,(22.&40.)Ptp,(22.&40.)Pt0,(22.&40.)Pt1,(22.&40.)Pt2,(22.&40.)Ps0,(22.&40.)Ps1,(22.&40.)Ps2,(22.&40.)Ps3,(22.&40.)Ps4,(22.&40.)Ps5,(22.&40.)Ps6,(22.&40.)Ps7,(22.&40.)Ps8,(22.&40.)Ps9,(22.&40.)Ps10,(22.&40.)Ps11,(22.&40.)Pt3,(22.&40.)Pt4,(22.&40.)Pt5,(22.&40.)Pt6,(22.&40.)Pa2,(22.&40.)Pa3,(22.&40.)Pa4,(22.&40.)Pa5,(22.&40.)Pa6,(22.&40.)Pa7,(22.&40.)Pc1,(22.&40.)Pc2,(22.&40.)Pc3,(22.&40.)PSP,$0.PF,(31.&5.(22.&40.))Pfc,(22.&20.)Pm,P,(22.&40.)(26.(22.&8.))PTR,$0.Psize,$0.Ptag,$0.PN,$0.Pv,$0.Plo,$0.Pws,(24.(22.&40.))Zszt,$0.(8.R6.(:.R5.(4.+2.+20.)))P,(1.(2.+1.R7.)(2.R7.+1>.))P,(1.(2.=R7.)(3.R7.+100.))P,(3.=R:.)P,(2.(8.R;.+100.)(4.+2.+3?.))P,(15.$0.(16.R<.+8.)=)P,(34.$7.R>.R=.R7.)P,(15.$30.(18.(22.&40.)R8.)#1>.)P,(35.VCS,R?.+?0.)P,(45.$7.R11.$46.(;.$<.(11.R17.)(?.$<.)))P,(45.$7.R12.$47.(;.$<.(11.R17.)(?.$<.)))P,(45.$7.R13.$48.(;.$<.(11.R17.)(?.$<.)))P,(27.R14.R10.)P,(1.(2.=R11.)(3.R11.(33.(4.+2.+1?.)+2.)))P,(44.$7.R16.R10.R19.)P,(2.+65?000.R11.)P,(2.R12.(33.R1;.+70.))P,(2.R1<.(4.+2.+3?.))P,(15.$0.(16.R1=.+10.)=)P,(49.(2.R1>.R1:.)(2.(8.R1:.+100.)R15.))P,(35.VCS,R16.(33.R1?.R16.))P,(36.$7.R1=.)(37.$7.VAL,VCS,Lms',$38.(5.$0.Lv,$0.(1.(1.(2.=R1.)(2.R1.R1<.))(4:.R42.R23.R41.R40.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R3?.R3>.R3=.R30.R2?.R2>.R2=.R27.R22.R21.R1?.R18.R1>.R1.R1:.R20.R2.)))(39.(3:.R40.(>.&40.R21.)R3?.R3>.R3=.R3<.R3;.R3:.R39.(>.&40.R1=.)(>.&40.R16.)R2:.R29.R28.R27.R26.R25.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.)R20.(>.&40.$4;.)R1?.(3;.(22.&40.))R1>.(3<.$7.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a2 a3 a4 a5 a6 a7 c1 c2 c3 SP F fc m TR size tag N v0 lo ws
      szt SZ TG T0 T1 TAL HTR HL TCS M1 M2 M3 DT NB ST LOIMG SPL SPH SPA TRSEP SCS MI.
    facts. subst szt.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_STACK_DEPOT_PUT, A_MUR1, A_MUR2, A_MUR3, A_DPUT_HASH in *.
    assert (HLz : Z.of_nat (length ws) = 30) by (rewrite HL; reflexivity).
    rewrite <- (Z_to_bv_bv_unsigned c1) in M1. rewrite <- (Z_to_bv_bv_unsigned c2) in M2. rewrite <- (Z_to_bv_bv_unsigned c3) in M3.
    flat constr:(SZ) 2%nat. flclear SZ. intros SZa SZb. flat constr:(TG) 2%nat. flclear TG. intros TGa TGb. flat constr:(NB) 2%nat. flclear NB. intros NBa NBb. lx_mulc. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x89650; 0x897e4] [] 60%N).
    all: change (2 ^ 32) with 4294967296 in *.
    1: { exfalso. clear -LXKT SZa SZb TGa. unfold zswrap, zlow in LXKT. change (2 ^ (32 - 1)) with 2147483648 in LXKT.
         rewrite (Z_mod_plus_full size tag 4294967296) in LXKT || rewrite Z_mod_plus_full in LXKT.
         rewrite (Z.mod_small size) in LXKT by lia. replace ((size + 2147483648) mod 2 ^ 32 - 2147483648) with size in LXKT by (rewrite Z.mod_small; lia).
         lx_klin. lia. }
    rewrite (land32_low size tag) in * by lia.
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (dhash_loop (Z.to_nat size) TR TR ws size); try eassumption; try lia. }
    cbv beta. intros ms1 (acc' & x5' & x6' & ->).
    (* [comment removed for export] *)
    lx_run (PLAN [0x896b4] [] 40%N). lx_same.
    (* [comment removed for export] *)
    lazymatch goal with |- evtA _ _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?e) _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
      rewrite <- (Z_to_bv_bv_unsigned (Z_to_bv 64 e));
      pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 e)) as HR;
      set (h := bv_unsigned (Z_to_bv 64 e)) in *; clearbody h end.
    unfold bv_modulus in HR. change (2 ^ Z.of_N 64) with (2^64) in HR.
    (* [comment removed for export] *)
    zstep. zstep. rewrite (bucket_of h) by lia.
    pose proof (Z.mod_pos_bound h (2^20) ltac:(lia)) as BI. set (bi := h mod 2 ^ 20) in *. clearbody bi.
    zstep.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with MU' : munch _ m mc |- _ => lazymatch goal with WM' : wmono _ m mc |- _ =>
        assert (DJ : disjoint_from [(lo, SP)] A_DEP (4 * 2^20)) by (unfold A_DEP; cbn; lia);
        (flat constr:((dtab_transport _ m mc N DT MU' WM' DJ bi ltac:(lia))) 3%nat; intros v TC VB) end end end.
    unfold A_DEP in TC. change (2 ^ 20) with 1048576 in *. change (2 ^ 64) with 18446744073709551616 in HR. flat constr:(VB) 2%nat. flclear VB. intros VBa VBb. flat constr:(BI) 2%nat. flclear BI. intros BIa BIb. flat constr:(HR) 2%nat. flclear HR. intros HRa HRb.
    (* [comment removed for export] *)
    zstep. rewrite (sx32_small v) by lia.
    (* [comment removed for export] *)
    lx_run (PLAN [0x896e0] [] 20%N). lx_same.
    lazymatch goal with ST' : stk _ lxm lo ?top |- _ =>
      lx_carve ST' 8%nat ST2 FRj fr;
      match goal with FR13 : rw_cells _ lxm top _ |- _ => chunk_join FRj FR13 FRA end end.
    apply evtA_done. exists v. split; [clear -VBa VBb; lia|]. unfold dput_pro_post, dput_frame, A_DPUT_FIND, A_DEP, A_DEP_NODES, A_DEP_MAP1.
    exists h, bi. lx_exs. lx_ands; [> lx_mseq | ..]; first [lx_close | clear -HRa HRb BIa BIb; lia].
  Qed.

  (* [comment removed for export] *)
  Definition dfind_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (h N : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_DepotA ()) "Lms',$38.(5.$0.Lpc,$0.(5.(22.&40.)Lx0,(22.&40.)(5.(22.&40.)Lx1,(22.&40.)(5.(22.&40.)Lx2,(22.&40.)(1.(15.$38.R5.(39.(3:.O1>.O1=.O1<.O1;.O1:.O19.O18.O17.O16.R3.R2.R1.O15.O14.O13.O12.O11.O10.(>.&40.O3.)O?.O>.(>.&40.+????.)O=.(>.&40.$10.)O<.O;.O:.O9.O8.O7.O6.)O5.(>.&40.R4.)O4.(3;.(22.&40.))O1.(3<.$7.)))(49.(1.(15.$0.R4.+897>4.)(5.$0.Ls,$0.(1.(15.(22.&40.)R4.(>.&40.R1.))(1.(2.+1.R1.)(2.R1.O2.)))))(1.(15.$0.R4.+89738.)(15.(22.&40.)R2.(>.&40.=)))))))))")
(* [comment removed for export] *).                              (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma dfind_loop : ltac2:(CDefT.buildp (gd_tbl_AW_DepotA ()) "Pn,$30.Ps,$0.Pnb,(24.$0.)PN,$0.Pra,(22.&40.)Psp,(22.&40.)Pgp,(22.&40.)Ptp,(22.&40.)Pt0,(22.&40.)Pt1,(22.&40.)Pt2,(22.&40.)Ps0,(22.&40.)Ps1,(22.&40.)Pa3,(22.&40.)Pa4,(22.&40.)Pa5,(22.&40.)Pa6,(22.&40.)Pa7,(22.&40.)Ps2,(22.&40.)Ps4,(22.&40.)Ps5,(22.&40.)Ps7,(22.&40.)Ps9,(22.&40.)Ps10,(22.&40.)Ps11,(22.&40.)Pt3,(22.&40.)Pt4,(22.&40.)Pt5,(22.&40.)Pt6,(22.&40.)Px0,(22.&40.)Px2,(22.&40.)PF,(31.&5.(22.&40.))Pfc,(22.&20.)Pm,P,(22.&40.)(26.(22.&8.))Ph,$0.P,(3.R22.(21.R23.))P,(1.(2.=R23.)(2.R23.R21.))P,(1.(2.=R3.)(3.R3.(4.+2.+40.)))P,(2;.R5.R24.)P,(2>.R6.R25.R24.)P,(4<.R26.R25.)P,(36.$7.R8.)P,Pk,$0.P,(1.(2.=R1.)(3.R1.(21.(18.$0.R29.))))(35.VCS,(2<.R2:.R2.)(4.+2.+14.))(37.$7.VAL,VCS,(4=.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R<.R;.R9.R28.R:.)(39.(3:.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R>.(>.&40.R2:.)R=.R1>.R1=.R1<.R1;.R1:.R19.(>.&40.R9.)R18.R17.(>.&40.+????.)R16.(>.&40.$10.)R15.R14.R13.R12.R11.R10.R?.)R<.(>.&40.$40.)R;.(3;.(22.&40.))R:.(3<.$7.)))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros s nb N ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s10 s11 t3 t4 t5 t6 x0 x2 F fc m h
      Hn Hs Hh DM DN WF MI NBCS; [lia|].
    facts. flat constr:(DM) 3%nat. flclear DM. intros DM1 DMF DML. flat constr:(WF) 2%nat. flclear WF. intros WN WL. unfold A_DPUT_FIND, A_DEP_MAP1 in *.
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz.
    { apply evtA_done. unfold dfind_post. do 4 eexists. split; [reflexivity|]. right. split; [reflexivity|]. apply bv_eq. rewrite Kz. reflexivity. }
    (* [comment removed for export] *)
    zstep. zstep. rewrite (srliw16 s) by lia.
    assert (KB : 0 <= s / 65536 < Z.of_nat (length nb)).
    { split; [apply Z.div_pos; lia|]. rewrite WL. apply Z.le_lt_trans with (N / 65536); [apply Z.div_le_mono; lia| lia]. }
    pose proof (DM1 (s / 65536) ltac:(lia)) as MC. unfold dmap1v in MC.
    replace (s / 65536 <? Z.of_nat (length nb)) with true in MC by (symmetry; apply Z.ltb_lt; lia).
    flat constr:((dblk_facts nb (s / 65536) DMF KB)) 3%nat. intros B0 B1 BAL.
    zstep. rewrite (Z.shiftl_mul_pow2 (s / 65536) 3) by lia. change (2^3) with 8.
    zstep. replace (6207720 + s / 65536 * 8) with (6207720 + 8 * (s / 65536)) by lia.
    zstep.
    (* [comment removed for export] *)
    zstep. if_cases Kb; zify_cond Kb. { exfalso. lia. }
    (* [comment removed for export] *)
    zstep. zstep. rewrite (Z.mod_small s 4294967296) by lia.
    zstep. rewrite (land16_mod s) by lia.
    zstep. rewrite (Z.shiftl_mul_pow2 (s mod 65536) 4) by lia. change (2^4) with 16.
    zstep.
    assert (HSB : 0 <= s < 65536 * Z.of_nat (length nb)).
    { split; [lia|]. pose proof (Z.div_mod s 65536 ltac:(lia)). pose proof (Z.mod_pos_bound s 65536 ltac:(lia)). nia. }
    flat constr:((DN s HSB)) 6%nat. intros hsh sid lnk NC L0 LS. specialize (LS ltac:(lia)).
    replace (dblk nb (s / 65536) + s mod 65536 * 16) with (dnode nb s) by (unfold dnode; lia).
    flat constr:((dnode_range nb s DMF HSB)) 5%nat. intros NR0 NR1 NRA NR2 NR3.
    pose proof (NBCS (s / 65536) KB) as NCS.
    pose proof (bv_unsigned_in_range 64 hsh) as HHR.
    zstep. zstep. rewrite (sx32_small lnk) by lia.
    (* [comment removed for export] *)
    zstep. if_cases Kne; zify_cond Kne.
    - (* [comment removed for export] *)
      eapply (IH lnk nb N); try eassumption; try lia. split; [exact DM1| split; [exact DMF| exact DML]]. split; assumption.
    - (* [comment removed for export] *)
      zstep. apply evtA_done. unfold dfind_post. do 4 eexists. split; [reflexivity|]. left. split; [reflexivity|]. exists s. split; [reflexivity| lia].
  Qed.
End DepotA.

End ARUN_1.
