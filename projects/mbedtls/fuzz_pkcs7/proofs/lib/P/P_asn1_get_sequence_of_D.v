(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_asn1_get_tag P_asn1_get_sequence_of_A P_asn1_get_sequence_of_B P_asn1_get_sequence_of_C.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P065bea0a941d831e 0 2 0 1 12 1P06f805a2195dcc57 0 3 0 1 37 1 38 1P0777a2cc72775442 0 2 0 1 1 1P0817b808b1a010c6 0 3 0 1 1 1 36 1P0b079aa2e96056c1 0 3 0 1 22 1 23 1P0b9f03758d6fa7f8 2 30 0 6 0 1 1 1 37 1 38 1 51 1 52 1 0 4 0 1 2 1 51 1 52 1P0befada3bcf0c71a 0 4 0 1 24 1 37 1 38 1P0ce6da4886d2f4db 0 2 0 1 41 1P0d8f6309af16384c 0 3 0 1 11 1 32 1P0e40b3a04cd711b4 0 2 0 1 26 1P0f018764f3ed2c84 0 2 0 1 5 1P0f4f7658f800b3c9 0 3 0 1 19 1 40 1P0fa4f1bfc06c8623 2 32 0 6 0 1 1 1 39 1 40 1 57 1 58 1 0 4 0 1 2 1 57 1 58 1P0fad819189856aca 0 5 0 1 15 1 21 1 36 1 39 1P11062f9894b8e4ed 0 6 0 1 15 1 33 1 34 1 35 1 36 1P1187059b3a3c8180 2 29 0 6 0 1 1 1 36 1 37 1 50 1 51 1 0 4 0 1 2 1 50 1 51 1P15a3cb4dc67a7b44 0 2 0 1 2 1P18365fc982bd2102 0 3 0 1 4 1 39 1P19d0321ed5f6611f 0 3 0 1 22 1 23 1P19f962c76257a53b 0 5 0 1 12 1 25 1 36 1 37 1P1b289315481378e3 0 6 0 1 20 1 38 1 39 1 40 1 41 1P1c312e566cec6015 0 2 0 1 12 1P1ca4f271b0fb0721 0 2 0 1 2 1P1dcdcf8a29dd67bf 0 2 0 1 12 1P1e80c3215ef078d1 0 3 0 1 10 1 31 1P1ee1f6ac27d68cd9 2 28 0 6 0 1 1 1 35 1 36 1 47 1 48 1 0 4 0 1 2 1 47 1 48 1P1fed2108bac0bfaf 0 2 0 1 1 1P209042337aa8f399 0 4 0 1 13 1 35 1 38 1P20ae7ad9b88f7196 0 2 0 1 1 1P226a9b63e8961672 0 2 0 1 27 1P229d1e9dd363877a 0 5 0 1 12 1 25 1 36 1 37 1P2681c146a05ebd0d 0 5 0 1 12 1 13 1 35 1 38 1P28bad80a4fafdf59 0 4 0 1 25 1 36 1 37 1P290ae7420a548059 0 3 0 1 16 1 37 1P2954083228eab7ba 0 2 0 1 49 1P2b8a2e72a52b7f9d 0 2 0 1 44 1P2c3db8908eb225a1 0 2 0 1 41 1P2c92d3820caa29e2 0 2 0 1 52 1P2d71800c43bbbdbf 0 2 0 1 1 1P2ed1abb8f451e134 0 6 0 1 13 1 32 1 33 1 34 1 35 1P2eef0339e33f84b7 0 5 0 1 12 1 13 1 35 1 38 1P30ca825a24d8ce0b 0 2 0 1 2 1P30f0f60bb54a1431 0 4 0 1 13 1 35 1 38 1P32ae8291622bb47d 0 4 0 1 10 1 23 1 35 1P339e923ecb3de95d 2 30 0 6 0 1 1 1 37 1 38 1 51 1 52 1 0 4 0 1 2 1 51 1 52 1P33c186d699f432cf 2 32 0 6 0 1 1 1 39 1 40 1 57 1 58 1 0 4 0 1 2 1 57 1 58 1P354ad1949e44f63a 2 28 0 6 0 1 1 1 35 1 36 1 47 1 48 1 0 4 0 1 2 1 47 1 48 1P361cbff61fdd5c8e 0 6 0 1 15 1 21 1 24 1 36 1 39 1P361dd4828fde78cd 0 2 0 1 18 1P36828f0d540a319a 2 29 0 6 0 1 1 1 36 1 37 1 50 1 51 1 0 4 0 1 2 1 50 1 51 1P36f9532738c036b9 0 3 0 1 11 1 36 1P372163a7c7ea22db 0 4 0 1 25 1 36 1 37 1P39cc1d572c7eda3b 0 2 0 1 14 1P3b1b887381a52e8e 2 22 0 6 0 1 1 1 29 1 30 1 41 1 42 1 0 4 0 1 2 1 41 1 42 1P3c279d8f33a9d7ab 0 2 0 1 53 1P3cb1271c89ee5984 0 2 0 1 19 1P3d4c29b1dfb98d79 0 2 0 1 42 1P3efb324eb0725723 2 22 0 6 0 1 1 1 29 1 30 1 41 1 42 1 0 4 0 1 2 1 41 1 42 1N000a94eba0469a78N008535763c31771bN00a04b3b76800191N00ad7e18b3fa105cN00ccb0e498593db2N00ec5bdea0870c0dN0125ccecc2e0f86aN012e4af0e2609493N01a9731dc2079cf8N01ba19676f4ab21bN01f3db5fa3298f3aN01fde8bf466ae763N024335e5cc9945e9N02cf06b59b7032bdN02d781703772c80fN034c5db74b2f3244N03a9b06e75d3e221N03dd224e79835cd9N03e104667a4c23f4N03fc1818164405a4N040bfd0996924502N04228c4dff8bbc06N043dbc13a5f78505N0467d7cdf7be812eN047100a4c0fac0f1N04b566fe9062d889N04fe90b38b39f87fN0580a2108b0e10e0N05934fa7fb9c7f4aN05b6861adb03de2aN066431c8991113dbN067635d9ab873037N07373ee6ecea94f5N074f95f88958fb73N078bae4142c4e522N08342484a7a187c1N08eda62c29bfedd2N0984201b5ed00337N0996d01551f5c6beN09ab29de4f2f096aN09b075e780d77d40N09bc7c9479a3f6c4N09dea032467f39ffN0a2e15c87b328c05N0a8ea513ed2308adN0aca2f930338b570N0af138235f47bf0cN0b0dd659428fb3fcN0b65bf2ed5690361N0bc3df6039703c36N0be58c99a5f85831N0c043340581a8b75N0c3bb0766b172b6fN0c59d461568e3a29N0c5dc7267abae245N0cb63c29897595f9N0ce6d29ee153916eN0d34f3f048e4ddc4N0d3607ad6dbaa1ecN0d979f64025ce294N0e2e68f4cae50ca5N0e3f332419c52859N0e69d2ba5b3318faN0eb43ab2af98ad26N0ebaa31b7702d715N0ed5c01fb4e42783N0f4ead15e665f685N0f65cf991333ceb7N0f7375ce08e28750N0f9ca04d4928c629N0fe19ac8e743b9aaN0fe43d86f829aa1fN0fed04be689e7217N1002fb01def877adN1029cec836d92e5cN102abb27ccbf4bd9N1068b1e30b5cf8dcN108c594569d3322cN1092f0772eb7582bN10a05dee611b0fd6N118e2e951b68e652N11bd5f3dbe8821d8N11c051e68dcc2bf6N11ec7a5a2ca91060N11f47cba300fa34dN1218c67527f098e5N1290e3c4c7d516d5N12c9e90702ef1e44N12e6da6a82476908N1317ad43b348dd89N1363219a25bb5726N13b09c176dcf8384N13b4d6cb2343ffa0N14e1092be2df5f8aN15dbbb40beb2d390N15e99f00af145c90N16c3046f5b445759N1779a7d7eef7c3e5N177c8d85cf30d0ddN17ff076b59cd7c06N1808c09fc837dfd8N182faa6c5e920d2cN186569b0b4a8140bN188b96d8ff80d421N188d65b780e15905N18b3f8a6009581bbN1924a4377477165eN1942531d2670a517N196cf7bcfdcfb91aN19875347d19deb3cN198b701baee7a29eN1994405330e8f390N199879f0b8b51035N1a08d0f8724ab619N1a093f3b0958ecbeN1a3d2cad82dbb5aaN1a48e45c5979be1dN1abcb603dd5ac534N1b68d3e41e7fc80cN1c002b9fc7ee2d2eN1c0401a5c64a6de0N1c0f9a42455fefc0N1c662ecfe01b5607N1c6759d555619a98N1c6b5ead075b8ec0N1d6494c752030cc5N1dc42522f4af0500N1e7d7b5f3152f801N1ea696eb4057800aN1eba80667f59555dN1f3e335b733c4f76N1fe53b8ae58c3fe4N201270c524841bd5N207d0c8f6fad6b01N210eaefb2f5afbe6N2135d7a66f1b588aN2139a1c0336a93ddN214fcec7bb4324a9N21a5c84eb5e18f61N2224d4fc1689b4ebN231aa139b06a1f0fN2326e302c2e0f629N234d89c159a47544N239d6d2fc2d2a85eN239f895d6d141acdN24304ba6f4b1fc34N247bf66430794389N2491f03b6af7d958N24dee8d182c2ccc5N24fe12deef8a3b59N255c5137657692adN256a3e4ed7b5c312N263babdc5e497451N2688bc08e136e96bN273942193e32f814N27613b31698b15b7N27bb31533c64b65dN28476307d85391deN28a22a8dc9e044f3N2930c00e0f3c29f3N29d3eb95fe92e48cN29d54351fcccb50fN29e1e0d3fcd3960aN2a051faffc74b454N2b5a2520b54f0a19N2b7a5cf00eb658c3N2bfdc120c6751320N2c109f01e2ce0a20N2c17ecfa3a94ad6fN2c2cbbbe3675318cN2c6448f52fb24e27N2c9174bd00d3f62fN2ce7277d350ad02eN2d24f5fc32d823c5N2e0531b3a7d795dfN2e1468f8739b4839N2e24a5efd6b12b4bN2e4b50224dffbaf6N2ea88dbc1a2138adN2ef5a2253c5403daN2f3afccc642c28adN2f5cb3b2ff498b8bN2faa2d4c4f1ecf83N301996118591eee6N30435cb278215156N3051b1d2467f5c86N30ed5738a9f7f695N311b38fc7ae226a4N319c48ae0bce1712N31bcfcbabffc4fceN31ecc8262d0a0c18N31fd06764f867f43N320b688e6812ec47N320fab86e579c70dN3216c171be15b9eeN3295de0cc3fd99d9N32a4ccd9e57b91ecN32e85472f683d10dN3385523f76cb5a19N33c49305a3f71b46N33cf90d415fe3913N340691e72a7cfc3cN342c11b71f083d6dN343b6762da92b18eN347d700231ccf480N34b153a73ea036d0N34f124cf62b471b6N3520dcf2b647576eN35710d20472bdb96N359bae8f895f7be9N35ce1f57155df56bN35db0dcd086dee86N35e26a2aaef2e427N35ea8e74ca5751f5N3654f716208f4d95N36ccc2c54f17ac5fN36dcd0f1031bf977N36e72e41ccd52ff6N37a6a38bf4792e9aN3815f5af1eba5cebN3830ad09cf4c593aN38351a0327c59a3cN38d778d35b4a3242N38f570d53d3545d5N39330345ed1a101aN3955b38d1fa658edN399a81fbd597bf2aN3a40a2a60b56930aN3ad4191f5638d80fN3b22689ea107a496N3b243be7bcefcc50N3b6dc4b2a298807aN3b99dadeefb5bab6N3bca436b80035ea4N3bca695e8db7bb95N3c801d0ee4869dccN3c9614d727b71211N3dd43e2ccf1ca291N3e1693b72c9ab422N3e25f2a14daa1355N3e91b6feb1ebd81fN3e92c858616a73ceN3f0a3e746ab0e224N3f1d67d933139f2bN3fee8cecd0685f25"%lxh.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_asn1_get_sequence_of_D () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Lib.HeapIface.HST"; "OSSVerify.KrLib.P.PImg.psegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.HeapIface.HEAP"; "OSSVerify.KrLib.P.P_asn1_get_sequence_of_A.LBof"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.HeapIface.heap_top"; "OSSVerify.KrLib.P.P_asn1_get_sequence_of_A.fresh"; "OSSVerify.KrLib.Spec.RepFacts.seq_lseg"; "OSSVerify.KrLib.Lib.Asn1Aux.heap_presx"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Frame.munch"; "Walk.W3"; "OSSVerify.KrLib.Lib.Frame.wmono"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.KrLib.LX.LxExpr.zlow"; "OSSVerify.KrLib.P.P_asn1_get_sequence_of_A.inv"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Lib.AEvt.aevtM"; "OSSVerify.KrLib.P.P_asn1_get_sequence_of_A.asn1_get_sequence_of_post"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Walk.LoopOblig"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.of_nat"].


Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface psegs L.
  Hypothesis HCALLOC : hl_calloc L = P_CALLOC.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST psegs L HI) (LB : list blk)
            (PP CUR P END BUF lo tag : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : CUR + 32 <= BUF \/ BUF + Z.of_nat (length bs) <= CUR.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis CURB : 0 <= CUR /\ CUR + 32 <= 2^64.
  Hypothesis AL1 : PP mod 8 = 0.
  Hypothesis AL2 : CUR mod 8 = 0.
  Hypothesis NZ1 : 0 < PP.
  Hypothesis NZ2 : 0 < CUR.
  Hypothesis NZ3 : 0 < BUF.
  Hypothesis SLO : lo <= bv_unsigned sp - 176 - hl_stack L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis HTOP : bv_unsigned sp <= heap_top psegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis DIM1 : hl_img_lo L <= hl_data_lo L.
  Hypothesis DIM2 : hl_data_hi L <= hl_img_hi L.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : CUR + 32 <= lo \/ bv_unsigned sp <= CUR.
  Hypothesis DS3 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CWPP : client_wrange L LB lo (heap_top psegs L HI h) PP 8.
  Hypothesis CWCUR : client_wrange L LB lo (heap_top psegs L HI h) CUR 32.
  Hypothesis CRBUF : client_range L LB lo BUF (Z.of_nat (length bs)).
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Hypothesis SPB : bv_unsigned sp < 2^64.
  Hypothesis HBR0 : Forall (fun b => block_range L (fst b) (snd b)) LB.

  Notation X := [(PP, PP + 8); (CUR, CUR + 32)].
  Notation POST := (asn1_get_sequence_of_post psegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB PP CUR P END BUF lo m mo).
  Notation CTX := (bv_unsigned sp + -24).
  (* [comment removed for export] *)
  Notation SPG := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Notation SPT := (Z_to_bv 64 (bv_unsigned sp + -128)).

  Notation INV := (inv L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m mo h LB PP CUR END BUF lo bs).
  Notation CBPOST := (cb_post L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB PP CUR END BUF lo bs).

  (* [comment removed for export] *)
  Definition W3 : list ivl := [(PP, PP + 8); (CUR, CUR + 32); (bv_unsigned sp - 128, bv_unsigned sp)].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L1224094474.47 L24089274786.12L28573890933.50L28575982988.51L32795543516.51L36324901792.5 L44010973198.54L44017149326.55L44370725769.50L54391871354.51L63380913806.5400000Y01C02102W02j03=03H03S03_04^04iS1L2sp2PP3CUR3BUF2lo2bs2D22D33SLO3HLS3DS3S1L2sp2PP3CUR2lo3SLO3HLS3ACL1y3HXC3AXP3AXCS2sp2PP3CUR2bs1a2Hs2Ho1L2lo3SLO3HLS3ACL3DHI2HdS1L2sp2PP3CUR2lo2bs3SLO3HLS3ACL1a2Ho1HS2PP3CUR2bs1a2O12O2S1L4DIM14DIM21y3HXDS2bs2cs3HszS2bs2cs3HszS2PP2bs1a2O1S1L2HI2sp1h2PP3CUR3BUF2lo2bs2D22D33SLO3HLS4HTOP3DS31a3Hin2O12O2S2bs2cs3Hsz". (* [comment removed for export] *)
  Lemma sync_T : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_D ()) "Pnodes,(0.$1.)Phc,(2.$3.VL,VHI,)Pmm,P,(4.&40.)(5.(4.&8.))Pm1,P,(4.&40.)(5.(4.&8.))Pmoc,$6.P,(7.$3.VL,VHI,R4.(8.VLB,R5.)R3.R1.)P,(9.$1.(:.$3.VL,VHI,R5.)(:.$3.VL,VHI,Vh,))P,(;.VL,VLB,R7.)P,(<.$3.R6.(8.VLB,R8.)VBUF,VEND,R8.=)P,(=.$3.VL,VLB,(>.&40.Vsp,)(?.(10.$1.$1.)(11.$1.$1.VPP,(12.VPP,+8.))(?.(10.$1.$1.)(11.$1.$1.VCUR,(12.VCUR,+20.))(13.(10.$1.$1.))))Vm,R7.)P,(14.$3.R8.VBUF,Vbs,)P,(15.$16.R9.R8.)P,(17.$3.R:.R9.)(18.(7.$3.VL,VHI,R<.(8.VLB,R=.)R:.R9.)(18.(<.$3.R:.(8.VLB,R=.)VBUF,VEND,R=.=)(18.(=.$3.VL,VLB,(>.&40.Vsp,)(?.(10.$1.$1.)(11.$1.$1.VPP,(12.VPP,+8.))(?.(10.$1.$1.)(11.$1.$1.VCUR,(12.VCUR,+20.))(13.(10.$1.$1.))))Vm,R:.)(14.$3.R:.VBUF,Vbs,))))")
(* [comment removed for export] *).
  Proof.
    clear - ACL CWPP CWCUR CRBUF DIM1 DIM2 DHI HBR0 PPB CURB SLO HLS HTOP D2 D3 DS3 B1 B3 B4.
    intros nodes hc mm m1 moc HHx HT HFR HLS' HPX HBY MU WM.
    assert (HSUB : forall b, In b LB -> In b (LBof LB nodes)) by (intros b Hb; unfold LBof; apply in_or_app; right; exact Hb).
    split; [| split; [| split]].
    - eapply HEAP_munch; [exact HHx| exact ACL| exact MU| exact WM|].
      intros a Ha Hin. cbn [outside W3] in Hin. rewrite HT.
      destruct (outside_dec [(PP, PP + 8)] a) as [O1|O1]; cbn [outside] in O1.
      2:{ exact (client_wrange_mono L _ _ _ _ _ _ CWPP HSUB a ltac:(lia)). }
      destruct (outside_dec [(CUR, CUR + 32)] a) as [O2|O2]; cbn [outside] in O2.
      2:{ exact (client_wrange_mono L _ _ _ _ _ _ CWCUR HSUB a ltac:(lia)). }
      left. lia.
    - eapply seq_lseg_mem; [exact HLS'| intros y Hy; eapply seq_lseg_in; [exact HLS'| exact Hy] |].
      intros y cs Hy HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz.
      flat constr:((HFR y Hy)) 3%nat. intros HXC HXD HXAP.
      assert (AXP : y + 32 <= PP \/ PP + 8 <= y)
        by (eapply client_wrange_apart; [exact CWPP | lia | lia | exact ACL | exact HXC | clear -HXD DIM1 DIM2; lia | exact HXAP]).
      assert (AXC : y + 32 <= CUR \/ CUR + 32 <= y)
        by (eapply client_wrange_apart; [exact CWCUR | lia | lia | exact ACL | exact HXC | clear -HXD DIM1 DIM2; lia | exact HXAP]).
      cbn [disjoint_from W3]. clear - AXP AXC HXC ACL SLO HLS. lia.
    - eapply heap_presx_trans; [exact HPX|]. eapply presx_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn [outside W3] in Ho |- *.
      destruct Hc as [Hs|[Hd|Hb]]; [lia| lia| pose proof (in_block_below L LB HBR0 a Hb); lia].
    - eapply bytes_at_transport; [exact HBY| exact MU|]. pose proof (bytes_at_bound _ _ _ _ HBY). cbn [disjoint_from W3]. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L22706555648.4 L36324901792.5 L44010973198.33L50384872000.3 L63380913806.3300000=00P00X00b00jS2PP3CUR1a2HoS1L4DIM14DIM21y3HXDS2cs3HszS2PP1y3AXPS2cs3Hsz". (* [comment removed for export] *)
  Lemma pp_store_keep : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_D ()) "Pnodes,(0.$1.)Pmm,P,(4.&40.)(5.(4.&8.))Pmm',P,(4.&40.)(5.(4.&8.))P,(;.VL,VLB,R3.)P,(<.$3.R3.(8.VLB,R4.)VBUF,VEND,R4.=)P,(=.$3.VL,VLB,(>.&40.Vsp,)(?.(10.$1.$1.)(11.$1.$1.VPP,(12.VPP,+8.))(?.(10.$1.$1.)(11.$1.$1.VCUR,(12.VCUR,+20.))(13.(10.$1.$1.))))Vm,R4.)P,(15.(?.(10.$1.$1.)(11.$1.$1.VPP,(12.VPP,+8.))(13.(10.$1.$1.)))R5.R4.)P,(17.$3.R6.R5.)(18.(<.$3.R6.(8.VLB,R8.)VBUF,VEND,R8.=)(=.$3.VL,VLB,(>.&40.Vsp,)(?.(10.$1.$1.)(11.$1.$1.VPP,(12.VPP,+8.))(?.(10.$1.$1.)(11.$1.$1.VCUR,(12.VCUR,+20.))(13.(10.$1.$1.))))Vm,R6.))")
(* [comment removed for export] *).
  Proof.
    clear - ACL CWPP DIM1 DIM2 HBR0 PPB.
    intros nodes mm mm' HFR HLS HPX MU WM. split.
    - eapply seq_lseg_mem; [exact HLS| intros y Hy; eapply seq_lseg_in; [exact HLS| exact Hy] |].
      intros y cs Hy HR Hsz. eapply rw_cells_transport; [exact HR| exact MU| exact WM|]. rewrite Hsz.
      flat constr:((HFR y Hy)) 3%nat. intros HXC HXD HXAP.
      assert (AXP : y + 32 <= PP \/ PP + 8 <= y)
        by (eapply client_wrange_apart; [exact CWPP | lia | lia | exact ACL | exact HXC | clear -HXD DIM1 DIM2; lia | exact HXAP]).
      cbn [disjoint_from]. clear -AXP. lia.
    - eapply heap_presx_trans; [exact HPX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn [outside] in Ho |- *. clear -Ho. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac tsync mx :=
    repeat match goal with H : munch [] ?a ?a |- _ => clear H | H : wmono _ ?a ?a |- _ => clear H end;
    first [ lazymatch goal with Hm : munch _ _ mx |- _ => idtac end
          | pose proof (munch_refl (@nil ivl) mx); pose proof (wmono_refl psegs mx) ];
    lazymatch goal with Hm1 : munch ?W1 ?mA mx |- _ =>
    lazymatch goal with Hw1 : wmono _ mA mx |- _ =>
      let MUW := fresh "MUW" in
      assert (MUW : munch W3 mA mx) by (eapply munch_weaken; [| exact Hm1]; intros xw Hxw; clear - Hxw; cbn [outside W3] in Hxw |- *; lia);
      lazymatch goal with HHc : HEAP _ _ _ ?hc (LBof LB ?nodes) mA ?moc, HTc : heap_top _ _ _ ?hc' = heap_top _ _ _ h, HPXc : heap_presx _ _ LB (bv_unsigned sp) _ m mA,
                          HFR : fresh L LB ?nodes', HSG : seq_lseg _ mA _ BUF END _ 0, BYc : bytes_at _ mA BUF bs |- _ =>
        let A := fresh "HH" in let C := fresh "HLS" in let D := fresh "HPX" in let E := fresh "HBUF" in
        (flat constr:((sync_T nodes hc mA mx moc HHc HTc HFR HSG HPXc BYc MUW Hw1)) 4%nat; intros A C D E);
        clear HHc HSG HPXc MUW Hm1 Hw1; try clear BYc;
        try match goal with H : bytes_at _ mx BUF bs, H' : bytes_at _ mx BUF bs |- _ => clear H' end
      end end end.

  (* [comment removed for export] *)
  Ltac rebuild_inv INV mm' :=
    lazymatch goal with
    | HH : HEAP _ _ _ ?hc (LBof LB ?nodes) mm' ?moc, HCUR : rw_cells _ mm' CUR [C4 ?ct; C4 ?cpad; C8 (Z_to_bv 64 ?cl); C8 (Z_to_bv 64 ?cp); _],
      FRG : rw_cells _ mm' (bv_unsigned sp + -32) [CB 8 ?j0; C4 ?tagw; C4 ?zpad; _; _],
      FRT : rw_cells _ mm' (bv_unsigned sp + -128) (CB 8 ?j1 :: _) |- _ =>
        assert (INV : inv L HI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m mo h LB PP CUR END BUF lo bs mm' moc hc nodes ct cpad cl cp tagw zpad j0 j1);
        [ unfold inv; unfold seq_cells; (flsplit; repeat match goal with |- _ /\ _ => split end); try assumption; try (eapply mo_frame_trans; eassumption) | ]
    end.
  Ltac open_inv INV :=
    pose proof INV as INVc;
    (flat constr:(INVc) 14%nat; flclear INVc; intros HH HT HND HFR HLS' HCUR HBUFOK FRG FRT ST MI HBUF HPX MF);
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK; unfold seq_cells in HCUR.
  Ltac flia := first [clear_disj; lia | lia].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L53792582152.7600000DS2sp2PP3CUR2bs2nn2H6". (* [comment removed for export] *)
  Lemma longform_n' : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_D ()) "Pnn,$1.Pw,(4.&40.)P,(18.(19.=R2.)(19.R2.+7?.))P,(9.$1.(>.&40.R2.)(1:.(1;.+2.+40.)+4.))P,(19.=(12.(1<.(>.&40.R3.))(1=.+40.(12.R4.-5.))))(18.(19.+1.R5.)(19.R5.+4.))")
(* [comment removed for export] *).
  Proof.
    intros nn w NR Hw H6. apply longform_n; [exact NR|]. unfold zlow in H6. rewrite Hw in H6.
    change (2 ^ 64)%Z with 18446744073709551616%Z in H6. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L13960211560.73L18926748074.73L316163276.73  L44015173360.7300001;01I01Z01hS1L2sp2PP3CUR3BUF2lo2bs2D12D22D33PPB4CURB3SLO3HLS3ACL3ACP3DS13DS23DS32nn2HnS2sp2PP3CUR2bsS2sp2PP3CUR2bs2nnS2sp2PP3CUR2bs". (* [comment removed for export] *)
  Lemma zx32m1 : forall nn, 1 <= nn <= 4 -> Z.shiftr (zlow 64 (4294967296 * nn + -4294967296)) 32 = nn - 1.
  Proof.
    intros nn Hn. unfold zlow. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32)%Z with 4294967296%Z.
    replace (4294967296 * nn + -4294967296) with ((nn - 1) * 4294967296) by lia. rewrite Z.div_mul by lia. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Notation CBA := 124712 (only parsing).   (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L13952744466.123L19615206944.123L20944490094.123L45172164586.123L49843886394.123L61492267460.123L61543799807.123L63462019729.12300000900:00I00X00b00k00l00mS2bs1r2HrFS1P3END2bs1p2HpS1P3END2bs1p2HpS2bs5nodesS2bs1r2HrFF". (* [comment removed for export] *)
  Lemma exit_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_D ()) "Pnodes,(0.$1.)Pp,$1.Pr,$1.Pct,(4.&40.)Pcpad,(4.&40.)Ptagw,(4.&40.)Pzpad,(4.&40.)Pcl,$1.Pcp,$1.Pj0,(0.(4.&8.))Pj1,(0.(4.&8.))Px1,(4.&40.)Px6,(4.&40.)Px7,(4.&40.)Px8,(4.&40.)Px9,(4.&40.)Px10,(4.&40.)Px11,(4.&40.)Px12,(4.&40.)Px13,(4.&40.)Px14,(4.&40.)Px15,(4.&40.)Px16,(4.&40.)Px17,(4.&40.)Px18,(4.&40.)Px19,(4.&40.)Px20,(4.&40.)Px21,(4.&40.)Px22,(4.&40.)Px23,(4.&40.)Px24,(4.&40.)Px25,(4.&40.)Px28,(4.&40.)Px29,(4.&40.)Px30,(4.&40.)Px31,(4.&40.)Pmm,P,(4.&40.)(5.(4.&8.))Pmoc,$6.Phc,(2.$3.VL,VHI,)P,(1>.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vm,Vmo,Vh,VLB,VPP,VCUR,VEND,VBUF,Vlo,Vbs,R3.R2.R1.R27.R24.R23.R20.R1?.R22.R21.R1>.R1=.)P,(1?.$3.R4.VPP,(?.$20.(21.(22.&40.R27.))(13.$20.)))P,(18.(19.VP,R28.)(19.R28.VEND,))P,(18.(23.-7?.R28.)(19.R28.=))(24.$3.R6.(25.$3.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(26.(27.R20.(22.&40.(12.(>.&40.Vsp,)-80.))Vgp,Vtp,(22.&40.R29.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.Vs10,Vs11,R;.R:.R9.R8.)VF,(22.&40.+1>580.)Vfc,(28.(4.&40.))R7.(29.$3.)))")
(* [comment removed for export] *).
  Proof.
    intros nodes p r ct cpad tagw zpad cl cp j0 j1 x1 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 mm moc hc
      INV HPP Hp Hr.
    open_inv INV. pose proof ACL as ACL'. pose proof SLO as SLO'. pose proof HLS as HLS'0.
    (* [comment removed for export] *)
    clear HCALLOC B4 AL1 AL2 NZ1 NZ2 NZ3 HTOP SPA DHI DIM1 DIM2 TP SPB CWPP CWCUR CRBUF HBR0.
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG psegs AL []) (@nil summary)) by (intros AL; constructor).
    apply (lxp_aevtM_of_evt psegs moc _ _ MK).
    lx_run_tac (PLANS (@nil Z) [] 60%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta.
    all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
    lazymatch goal with STx : stk _ mm lo (bv_unsigned sp) |- _ => rename STx into STf end.
    apply aevtM_done. unfold asn1_get_sequence_of_post. flexi 15%nat.
    exists mm, moc, hc, r, p, ct, cpad, cl, cp, (hd 0 nodes), nodes.
    split; [reflexivity|].
    (flsplit; repeat match goal with |- _ /\ _ => split end); try assumption; try lia.
    - reflexivity.
    - eapply (seq_lseg_chain psegs). exact HLS'.
    - intros x Hx. exact (proj2 (proj2 (HFR x Hx))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition LoopOblig (p' : Z) (tgw s1w : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_D ()) "Pnodes,(0.$1.)Pct,(4.&40.)Pcpad,(4.&40.)Ptagw,(4.&40.)Pzpad,(4.&40.)Pcl,$1.Pcp,$1.Pj0,(0.(4.&8.))Pj1,(0.(4.&8.))Px1,(4.&40.)Px5,(4.&40.)Px6,(4.&40.)Px8,(4.&40.)Px18,(4.&40.)Px19,(4.&40.)Px20,(4.&40.)Px21,(4.&40.)Px22,(4.&40.)Px23,(4.&40.)Px24,(4.&40.)Px25,(4.&40.)Px28,(4.&40.)Px29,(4.&40.)Px30,(4.&40.)Px31,(4.&40.)Pmm,P,(4.&40.)(5.(4.&8.))Pmoc,$6.Phc,(2.$3.VL,VHI,)P,(1>.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vm,Vmo,Vh,VLB,VPP,VCUR,VEND,VBUF,Vlo,Vbs,R3.R2.R1.R1<.R1;.R1:.R17.R16.R19.R18.R15.R14.)P,(1?.$3.R4.VPP,(?.$20.(21.(22.&40.O3.))(13.$20.)))(24.$3.R4.(25.$3.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(26.(27.R15.(22.&40.(12.(>.&40.Vsp,)-80.))Vgp,Vtp,R14.R13.(22.&40.O3.)R12.O1.(22.&40.VPP,)(22.&40.VEND,)(22.&40.+??.)O2.(22.&40.=)(22.&40.=)(22.&40.+1>728.)(22.&40.(12.(>.&40.Vsp,)-18.))R11.R10.R?.R>.R=.R<.R;.R:.Vs10,Vs11,R9.R8.R7.R6.)VF,(22.&40.+1>4:0.)Vfc,(28.(4.&40.))R5.(29.$3.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0@L22704459656.5  L2397608051.175 L25223889516.175L25228112495.136L38398856704.175L42814931379.136L49334196641.175L49336294177.136L52591992819.175L52591992819.185L64000094492.17500000B00Q00e01801?01F01X01j01k03W04KS2sp2PP3CUR2xw3HxwS2sp2bs1q2Lw2LRS2sp3END2bs1q2Lw3H15S2sp3END2bs1q2Lw2H5S2sp2bsS2sp2bsS2sp1P3END2bs1q2HqS2sp1P3END2bs1q2HqFS1L2sp2PP3CUR1P3END3BUF2lo2bs2D12D22D33ACP3DS13DS23DS31q2Hq3HqB4ACL'4SLO'5HLS'04SPA'3B1'3B3'3D2'4DS1'3x402HRS1L2sp1P3END2lo2bs3ACP1q2Lw2Hq4ACL'4SLO'5HLS'02LR2H5". (* [comment removed for export] *)
  Lemma j2_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_D ()) "Pnodes,(0.$1.)Pp0,$1.Pq,$1.Ptb,$1.PLw,(4.&40.)Ptgw,(4.&40.)Ps1w,(4.&40.)Pct,(4.&40.)Pcpad,(4.&40.)Ptagw,(4.&40.)Pzpad,(4.&40.)Pcl,$1.Pcp,$1.Pj0,(0.(4.&8.))Pj1,(0.(4.&8.))Px1,(4.&40.)Px7,(4.&40.)Px18,(4.&40.)Px19,(4.&40.)Px20,(4.&40.)Px21,(4.&40.)Px22,(4.&40.)Px23,(4.&40.)Px24,(4.&40.)Px25,(4.&40.)Px28,(4.&40.)Px29,(4.&40.)Px30,(4.&40.)Px31,(4.&40.)Pmm,P,(4.&40.)(5.(4.&8.))Pmoc,$6.Phc,(2.$3.VL,VHI,)P,(1>.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vm,Vmo,Vh,VLB,VPP,VCUR,VEND,VBUF,Vlo,Vbs,R3.R2.R1.R20.R19.R18.R15.R14.R17.R16.R13.R12.)P,(1?.$3.R4.VPP,(?.$20.(21.(22.&40.R1?.))(13.$20.)))P,(18.(19.(12.VP,+2.)R20.)(19.R20.VEND,))P,(19.VBUF,R21.)P,(18.(19.=R21.)(23.R21.+100.))P,Pp',$1.P,(19.R24.R1.)P,(23.R2.VEND,)(2:.R3.R23.R22.)(24.$3.R8.(25.$3.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(26.(27.R17.(22.&40.(12.(>.&40.Vsp,)-80.))Vgp,Vtp,(22.&40.R23.)(22.&40.R24.)R16.R22.R20.(22.&40.VPP,)(22.&40.VEND,)(22.&40.+??.)R21.(22.&40.=)(22.&40.=)(22.&40.+1>728.)(22.&40.(12.(>.&40.Vsp,)-18.))R15.R14.R13.R12.R11.R10.R?.R>.Vs10,Vs11,R=.R<.R;.R:.)VF,(22.&40.+1>520.)Vfc,(28.(4.&40.))R9.(29.$3.)))")
(* [comment removed for export] *).
  Proof.
    intros nodes p0 q tb Lw tgw s1w ct cpad tagw zpad cl cp j0 j1 x1 x7 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 mm moc hc
      INV HPP Hq HqB Htb KLOOP.
    open_inv INV. pose proof ACL as ACL'. pose proof SLO as SLO'. pose proof HLS as HLS'0. pose proof SPB as SPB'. pose proof SPA as SPA'.
    pose proof B1 as B1'. pose proof B3 as B3'. pose proof B4 as B4'. pose proof PPB as PPB'. pose proof D2 as D2'. pose proof DS1 as DS1'.
    clear NZ1 NZ2 AL1 AL2.   (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn in LR.
    assert (LXSUMS : forall AL, Forall (summary_okG psegs AL []) (@nil summary)) by (intros AL; constructor).
    (* [comment removed for export] *)
    rewrite TP. apply (lxp_aevtM_of_evt psegs moc _ _ MK).
    lx_run_tac (PLANS [0x1e728; 0x1e580] [] 80%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
    (* [comment removed for export] *)
    1: eapply exit_walk; [exact INV| exact HPP| flia| flia].
    (* [comment removed for export] *)
    eapply aevtM_cut; [eapply cb_walk; try exact INV; try eassumption; flia |].
    intros ms' mo' PO. unfold cb_post in PO. destruct_exs PO.
    flat constr:(PO) 5%nat. flclear PO. intros E Hr HR INV2 HPP2. injection E as E1 E2. subst ms' mo'. subst.
    clear HH HT HND HFR HLS' HCUR HBUFOK FRG FRT ST MI HBUF HPX MF MK INV HPP.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m2; rename mox into mo2 end.
    open_inv INV2.
    (* [comment removed for export] *)
    rewrite TP. apply (lxp_aevtM_of_evt psegs mo2 _ _ MK).
    lx_run_tac (PLANS [0x1e580; 0x1e4a0] [] 80%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    all: lazymatch goal with
         | E : @eq mem ?mx ?mc0 |- _ => subst mx; eapply exit_walk; [exact INV2| exact HPP2| flia| flia]
         | |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
             tsync mx; rebuild_inv INV3 mx;
             lazymatch goal with HP : rw_cells _ mx PP _ |- _ =>
               lazymatch pc with
               | 124288 => eapply exit_walk; [exact INV3| exact HP| flia| flia]
               | _ => eapply KLOOP; [flia| flia| exact INV3| exact HP]
               end end
         end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090@L10881010543.142L19526678764.142L20624037919.145L21641375212.142L22704459656.5  L34399671065.142L59981756645.145L6284136474.142 L8512937216.142 00000L00k01L01k02=02Y03Y04Q05PS2sp3BUF2bs1k3cur4stop2Hk2HBS2sp1P2bs1k3cur4stop2Hk4Hcur2H5S2sp3END2bs1k3cur4stop2Hk2p'4Hp'2S2sp3END2bs1k3cur4stop2Hk5HstopS2sp2PP3CUR2xw3HxwS2sp2bs1k3cur4stop2tb2Hk3HtbS2sp2bs1k3cur4stop2Hk2p'4Hp'11L1P2lo3ACP4Hcur4ACL'4SLO'5HLS'02H5S1L2sp1P2lo2bs3ACP1k3cur4stop2Hk4Hcur4ACL'4SLO'5HLS'02H5S1L2sp1P3END2lo2bs3ACP1k3cur4stop2Hk4Hcur5Hstop4ACL'4SLO'5HLS'0". (* [comment removed for export] *)
  Lemma lenloop_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_D ()) "Pk,$2;.Pcur,$1.Pstop,$1.Ptb,$1.Pnodes,(0.$1.)Pct,(4.&40.)Pcpad,(4.&40.)Ptagw,(4.&40.)Pzpad,(4.&40.)PLw,(4.&40.)Ptgw,(4.&40.)Ps1w,(4.&40.)Pcl,$1.Pcp,$1.Pj0,(0.(4.&8.))Pj1,(0.(4.&8.))Px1,(4.&40.)Px18,(4.&40.)Px19,(4.&40.)Px20,(4.&40.)Px21,(4.&40.)Px22,(4.&40.)Px23,(4.&40.)Px24,(4.&40.)Px25,(4.&40.)Px28,(4.&40.)Px29,(4.&40.)Px30,(4.&40.)Px31,(4.&40.)Pmm,P,(4.&40.)(5.(4.&8.))Pmoc,$6.Phc,(2.$3.VL,VHI,)P,(9.$2;.(2<.(1:.R1>.R1?.))R20.)P,(18.(19.(12.VP,+2.)R20.)(23.R20.R1?.))P,(19.R20.VEND,)P,(19.VBUF,R22.)P,(18.(19.=R21.)(23.R21.+100.))P,(1>.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vm,Vmo,Vh,VLB,VPP,VCUR,VEND,VBUF,Vlo,Vbs,R8.R7.R6.R21.R20.R1?.R19.R18.R1>.R1=.R17.R16.)P,(1?.$3.R9.VPP,(?.$20.(21.(22.&40.R25.))(13.$20.)))P,Pp',$1.P,(19.R26.R1.)P,(23.R2.VEND,)(2:.R3.R20.R1?.)(24.$3.R:.(25.$3.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(26.(27.R18.(22.&40.(12.(>.&40.Vsp,)-80.))Vgp,Vtp,(22.&40.R25.)(22.&40.R27.)(22.&40.R26.)R1?.R1=.(22.&40.VPP,)(22.&40.VEND,)(22.&40.+??.)R1>.(22.&40.=)(22.&40.=)(22.&40.+1>728.)(22.&40.(12.(>.&40.Vsp,)-18.))R17.R16.R15.R14.R13.R12.R11.R10.Vs10,Vs11,R?.R>.R=.R<.)VF,(22.&40.+1>508.)Vfc,(28.(4.&40.))R;.(29.$3.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros cur stop tb nodes ct cpad tagw zpad Lw tgw s1w cl cp j0 j1 x1 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 mm moc hc
      Hk Hcur Hstop HB Htb INV HPP KLOOP; [lia|].
    open_inv INV. pose proof ACL as ACL'. pose proof SLO as SLO'. pose proof HLS as HLS'0. pose proof SPB as SPB'. pose proof SPA as SPA'.
    pose proof B1 as B1'. pose proof B3 as B3'. pose proof B4 as B4'. pose proof PPB as PPB'. pose proof D2 as D2'. pose proof DS1 as DS1'.
    clear NZ1 NZ2 AL1 AL2.   (* [comment removed for export] *)
    pose proof (bv_unsigned_in_range 64 Lw) as LR. unfold bv_modulus in LR. cbn in LR.
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    assert (LXSUMS : forall AL, Forall (summary_okG psegs AL []) (@nil summary)) by (intros AL; constructor).
    (* [comment removed for export] *)
    rewrite TP. apply (lxp_aevtM_of_evt psegs moc _ _ MK).
    lx_run_tac (PLANS [0x1e508; 0x1e520] [] 60%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
         tsync mx; rebuild_inv INV2 mx;
         lazymatch goal with HP : rw_cells _ mx PP _ |- _ =>
           lazymatch pc with
           | 124168 => eapply (IH (cur + 1) stop); [flia| flia| flia| flia| flia| exact INV2| exact HP| intros p' Hp'1 Hp'2; apply KLOOP; flia]
           | _ => eapply j2_walk with (p0 := 0); [exact INV2| exact HP| flia| flia| flia| intros p' Hp'1 Hp'2; apply KLOOP; flia]
           end end
         end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0@L18817887146.150L20097941744.147L20367711647.150L20624037919.150L20624037919.153L22704459656.5  L2383481069.150 L2396079313.147 L27586674021.135L27586674021.139L27586674021.146L27586674021.148L34246658149.150L34246658149.153L42802377143.139L42802377143.148L47844901431.146L60925704695.135L67044134857.147L67056698357.15000000E00[01501H01[01m02`03S03e04704I04[04l05^05e05l06306:06M06`S2sp3END2bs1p4lxv02H5S2sp1P3END2bs1p2Hp3H10S2sp1P3END2bs1p2Hp4lxv02HNS2sp3END2bs2p'4Hp'2S2sp3END2bs2p'4Hp'2S2sp2PP3CUR2xw3HxwS1L2sp1P3END3BUF2lo2bs3ACP1p2Hp4ACL'4SLO'5HLS'03B1'S1L2sp1P3END3BUF2lo2bs3ACP1p2Hp4ACL'4SLO'5HLS'03B1'S2sp1P3END2bs1p2HpS2sp1P3END2bs1p2HpS2sp1P3END2bs1p2HpS2sp1P3END2bs1p2HpS2sp2bs1p2p'4Hp'1S1L2sp2lo2bs3ACP1p4ACL'4SLO'5HLS'04lxv02HN2p'4Hp'1S2sp2bsS2sp2bsS2sp2bsS2sp2bsS2sp2bs3lxv3H133H14S2sp2bs3lxv3H133H14". (* [comment removed for export] *)
  Lemma body_walk : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_D ()) "Pp,$1.Pnodes,(0.$1.)Pct,(4.&40.)Pcpad,(4.&40.)Ptagw,(4.&40.)Pzpad,(4.&40.)Ptgw,(4.&40.)Ps1w,(4.&40.)Pcl,$1.Pcp,$1.Pj0,(0.(4.&8.))Pj1,(0.(4.&8.))Px1,(4.&40.)Px5,(4.&40.)Px6,(4.&40.)Px8,(4.&40.)Px18,(4.&40.)Px19,(4.&40.)Px20,(4.&40.)Px21,(4.&40.)Px22,(4.&40.)Px23,(4.&40.)Px24,(4.&40.)Px25,(4.&40.)Px28,(4.&40.)Px29,(4.&40.)Px30,(4.&40.)Px31,(4.&40.)Pmm,P,(4.&40.)(5.(4.&8.))Pmoc,$6.Phc,(2.$3.VL,VHI,)P,(1>.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vm,Vmo,Vh,VLB,VPP,VCUR,VEND,VBUF,Vlo,Vbs,R3.R2.R1.R1>.R1=.R1<.R17.R16.R1;.R1:.R15.R14.)P,(1?.$3.R4.VPP,(?.$20.(21.(22.&40.R20.))(13.$20.)))P,(18.(19.(12.VP,+2.)R21.)(23.R21.VEND,))P,(9.$1.(>.&40.R1;.)(1:.(1;.+2.+40.)+4.))P,Pp',$1.P,(23.R24.R1.)P,(23.R2.VEND,)(2:.R3.R20.R1?.)(24.$3.R7.(25.$3.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VPP,VCUR,VP,VEND,VBUF,Vlo,Vm,Vmo,)(26.(27.R18.(22.&40.(12.(>.&40.Vsp,)-80.))Vgp,Vtp,R17.R16.(22.&40.R24.)R15.R1=.(22.&40.VPP,)(22.&40.VEND,)(22.&40.+??.)R1>.(22.&40.=)(22.&40.=)(22.&40.+1>728.)(22.&40.(12.(>.&40.Vsp,)-18.))R14.R13.R12.R11.R10.R?.R>.R=.Vs10,Vs11,R<.R;.R:.R9.)VF,(22.&40.+1>4:0.)Vfc,(28.(4.&40.))R8.(29.$3.)))")
(* [comment removed for export] *).
  Proof.
    intros p nodes ct cpad tagw zpad tgw s1w cl cp j0 j1 x1 x5 x6 x8 x18 x19 x20 x21 x22 x23 x24 x25 x28 x29 x30 x31 mm moc hc
      INV HPP Hp Hs1 KLOOP.
    open_inv INV. pose proof ACL as ACL'. pose proof SLO as SLO'. pose proof HLS as HLS'0. pose proof SPB as SPB'. pose proof SPA as SPA'.
    pose proof B1 as B1'. pose proof B3 as B3'. pose proof B4 as B4'. pose proof PPB as PPB'. pose proof D2 as D2'. pose proof DS1 as DS1'.
    clear NZ1 NZ2 AL1 AL2.   (* [comment removed for export] *)
    pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
    assert (LXSUMS : forall AL, Forall (summary_okG psegs AL []) (@nil summary)) by (intros AL; constructor).
    (* [comment removed for export] *)
    rewrite TP. apply (lxp_aevtM_of_evt psegs moc _ _ MK).
    lx_run_tac (PLANS [0x1e508; 0x1e520; 0x1e580] [] 80%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
         tsync mx; rebuild_inv INV2 mx;
         lazymatch goal with HP : rw_cells _ mx PP _ |- _ =>
           lazymatch pc with
           | 124288 => eapply exit_walk; [exact INV2| exact HP| flia| flia]
           | 124168 => (* [comment removed for export] *)
               lazymatch goal with |- context [Z.shiftr (zlow 64 (4294967296 * ?nn + -4294967296)) 32] =>
                 lazymatch nn with Z.land (Z.land ?b 255) 127 =>
                   let NR := fresh "NR" in pose proof (land_127_range b) as NR;
                   lazymatch goal with H6 : 0 <= - bv_unsigned ?sw + zlow 64 (nn + -5), Hs : bv_unsigned ?sw' = 2 ^ 64 - 4 |- _ =>
                     let HN := fresh "HN" in pose proof (longform_n' nn sw NR Hs H6) as HN;
                     rewrite (zx32m1 nn HN)
                   end end end;
               eapply lenloop_walk; [reflexivity| flia| flia| flia| flia| exact INV2| exact HP| intros p' Hp'1 Hp'2; apply KLOOP; flia]
           | _ => eapply j2_walk with (p0 := 0); [exact INV2| exact HP| flia| flia| flia| intros p' Hp'1 Hp'2; apply KLOOP; flia]
           end end
         end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L26726586635.112L2936365656.112 L3914836636.112 L51040902898.109L51830345412.77 00001T03804d04e05IS1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32D12D22D33PPB4CURB3SLO3HLS3ACL3ACP3DS13DS23DS31k1p2Hk2Hp2p'2H12H2S1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32D12D22D33PPB4CURB3SLO3HLS3ACL3ACP3DS13DS23DS31k1p2Hk2Hp2p'2H12H2S1L2sp2PP3CUR1P3END3BUF2lo2bs2B12B32D12D22D33PPB4CURB3SLO3HLS3ACL3ACP3DS13DS23DS31k1p3s1w2Hk2Hp3Hs12p'2H12H2FS2sp2PP3CUR1P3END2bs1p3tgw3s1w2Hk2Hp". (* [comment removed for export] *)
  Lemma tloop : ltac2:(CDefT.buildp (gd_tbl_P_asn1_get_sequence_of_D ()) "Pk,$2;.Pp,$1.Ptgw,(4.&40.)Ps1w,(4.&40.)P,(19.(1:.VEND,R3.)(2=.R4.))P,(18.(19.(12.VP,+2.)R4.)(23.R4.VEND,))P,(9.$1.(>.&40.R3.)(1:.(1;.+2.+40.)+4.))(2:.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros p tgw s1w Hk Hp Hs1; [lia|].
    unfold LoopOblig. intros. eapply body_walk; try eassumption; try lia.
    intros p' H1 H2. apply IH; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.
