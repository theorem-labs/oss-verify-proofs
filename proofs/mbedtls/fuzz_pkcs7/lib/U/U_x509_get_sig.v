(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_get_bitstring_null.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P003a503133260564 0 4 0 1 19 1 29 1 30 1P02a7f0d0e5afac78 0 2 0 1 26 1P02fffff5096be445 2 27 1 1 8 3 1 1 41 1 42 1 5 0 2 30 2 40 2 43 2 44 16 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P05124ad17dde557a 0 4 0 1 2 1 33 1 34 1P054f13d692bb675c 1 1 16 2 0 1 29 1 3 10 1 30 1 31 16P0693db99426c20f0 1 1 8 3 0 1 32 1 33 1 5 2 2 21 2 31 2 34 2 35 16P06b5984780958030 0 5 1 1 2 1 21 1 31 1 32 1P07062781f2fdb5bc 0 2 0 1 3 1P0729366b460e31de 0 2 0 1 6 1P079c1062848810ef 2 27 1 1 8 3 1 1 41 1 42 1 5 0 2 30 2 40 2 43 2 44 16 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P07f6961823abbb5e 1 1 8 3 0 1 31 1 34 1 4 2 2 32 2 33 2 35 16P0adef23a74319061 0 2 0 1 20 1P0af87c5cba4e215e 2 27 1 1 8 3 1 1 41 1 42 1 5 0 2 30 2 40 2 43 2 44 16 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P0cd4fa5ddd9993d0 1 1 8 2 22 1 30 1 3 0 1 29 1 31 8P0d605c0bb5f13695 0 2 0 1 5 1P0ff84974a53d4942 0 5 1 1 3 1 22 1 32 1 33 1P10bd5ead00c61b5c 0 3 0 1 1 1 22 1P10e47fdd5ea128ba 1 1 8 3 0 1 31 1 34 1 4 2 2 32 2 33 2 35 16P10e8b57dcb47fc9a 0 2 0 1 24 1P123cf363514d0b45 1 1 8 3 1 1 32 1 33 1 5 2 2 21 2 31 2 34 2 35 16P1443bf0c1fca76da 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P14c9a07e2975215b 0 2 0 1 2 1P14d1c1c73948b521 0 4 0 1 3 1 32 1 33 1P152572d6f0be661e 1 1 8 3 1 1 31 1 34 1 4 2 2 32 2 33 2 35 16P16cd07cc6e64cc1e 0 4 0 1 26 1 36 1 37 1P16ebabd4c84b0680 1 1 16 2 11 1 29 1 3 0 1 30 1 31 16P188d093d989c5589 2 27 1 1 8 3 1 1 41 1 42 1 5 0 2 30 2 40 2 43 2 44 16 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P19212a5325f24c9a 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P19d8686ec797bcd2 0 2 0 1 1 1P1a227fadbf2832a8 0 4 0 1 26 1 36 1 37 1P1a4c913f4fb40ed7 2 27 1 1 8 3 1 1 41 1 42 1 5 0 2 30 2 40 2 43 2 44 16 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P1b3a9b9809082b21 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P1b4b3f8fc18cc66c 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P1bf204542ded4f42 0 2 0 1 7 1P1c9513cd6f0fdc1c 0 5 1 1 3 1 22 1 32 1 33 1P1e7b2fc1fe5a9c33 1 1 8 3 0 1 32 1 33 1 5 2 2 21 2 31 2 34 2 35 16P1f4abe16cb332e23 0 2 0 1 5 1P20aca0e1c26e1345 0 4 0 1 28 1 38 1 39 1P2185521e41020ab1 0 2 0 1 22 1P21f25f1e35fc2831 0 4 1 1 2 1 31 1 32 1P234c35d689b8f70b 2 28 1 1 8 3 1 1 41 1 42 1 5 0 2 30 2 40 2 43 2 44 16 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P23e55f8cd61af875 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P240f10ce51e90dc8 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P26672f5e45561282 0 2 0 1 1 1P269eaa50b58be2d6 1 1 8 3 1 1 32 1 33 1 5 2 2 21 2 31 2 34 2 35 16P2755af0d8a78f9e5 0 4 0 1 2 1 31 1 32 1P2a0654b37012dc94 2 28 1 1 8 3 1 1 41 1 42 1 5 0 2 30 2 40 2 43 2 44 16 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P2ab65fcea2f9f794 2 27 1 1 8 3 1 1 41 1 42 1 5 0 2 30 2 40 2 43 2 44 16 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P2c388ce01c3408be 1 1 16 2 0 1 29 1 3 10 1 30 1 31 16P2ce6b6d6158bf651 0 2 0 1 18 1P2d49a523bdc9c481 2 27 1 1 8 3 1 1 41 1 42 1 5 0 2 30 2 40 2 43 2 44 16 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P2eaa4bcec685b6d0 2 28 1 1 8 3 1 1 41 1 42 1 5 0 2 30 2 40 2 43 2 44 16 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P30401859d10638bf 0 4 0 1 28 1 38 1 39 1P317384dbd7f70a0d 1 1 8 3 1 1 31 1 34 1 4 2 2 32 2 33 2 35 16P31ae1b5c692dd749 0 2 0 1 24 1P326ec96b4dc717b8 2 27 1 1 8 3 1 1 41 1 42 1 5 0 2 30 2 40 2 43 2 44 16 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P3288c3db09dd84ee 0 4 0 1 17 1 27 1 28 1P3461db9c1ff47efc 0 2 0 1 5 1P356257de20a47048 1 1 8 3 1 1 31 1 34 1 4 2 2 32 2 33 2 35 16P359863197b2ceb53 0 4 0 1 19 1 29 1 30 1P35afd14fde0da9a6 2 16 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P35b4641301b8f888 1 1 8 3 1 1 32 1 33 1 4 2 2 31 2 34 2 35 16P35f518945f3d5f50 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P3843a40faf95ad3a 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P38841f837b3315a8 0 4 0 1 3 1 32 1 33 1P38c17cf3decee71f 0 4 0 1 28 1 38 1 39 1P3970b8efd224c8d4 0 2 0 1 23 1P39b8f0435877ced7 1 1 8 3 0 1 32 1 33 1 5 2 2 21 2 31 2 34 2 35 16P39d5468d7871926d 2 15 1 1 8 3 2 1 29 1 30 1 5 0 2 18 2 28 2 31 2 32 16 1 1 8 3 1 1 28 1 31 1 4 0 2 29 2 30 2 32 16P3af1c80f57f3ccb2 0 5 0 1 17 1 20 1 21 1 23 1P3d6c0e29a28eb0a5 0 1 1 1P3de2e39be058d308 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P3e66807c87ac5307 2 14 0 5 0 1 3 1 19 1 29 1 30 1 0 4 0 1 2 1 29 1 30 1P3ebbb0aa82544909 0 4 0 1 26 1 36 1 37 1N0013ac5e20edddefN02649eeb01d42a02N027311b31d881309N028a708ed2318714N02a7e9da82335037N0341649471a130cbN035231e72ed7c822N03da634fdfdfc76fN04f654ed34b01b0fN054c20b1b041e60dN055713d2c90b43d8N059c8e4e7660dfddN06142608a53e09f7N06e46ae922d72f86N0724788db3ffce25N09282a877ccc5700N09942c8c9c668363N0b5f30375f407439N0c19f6cbb7b76369N0c74924551227b6dN0cca1bb818fd4e91N0d0f74b0b5154640N0dbb7ac3a5a06080N0f64b6646d8696cdN1190c8ba0d0e5c31N11dd485027ad88b6N1325a40f2cd48563N141a2d1e9d58d334N14727419f073ef92N148dcef7a81f141aN14cbdc0343443f6fN17d9eadab5c4445aN17fa4974155ee353N19029cde5679b959N19198ba45f036596N196943f80576daf6N19f1e7a4da547d16N1a0b33c900f1a29cN1cc1a430249575fbN1cd79f23c024d8b2N1cef60a7a0243ef5N1df0e2533284e45cN209a1d5a5cb63d00N20c3c7a786515303N20dffaea02eab269N21b62b6761c7c050N2236bf3150c133e1N2339b74f51028f74N2408365c8ca11d4bN24f17d7b80b09315N252da5cbfb7b92f9N252ed6ce8f9ef896N27e9fe228b3e1d27N28656c993ad63c7dN290a38ee0732c215N29781763f0d7dd5dN299fa4679293211bN29f8c979917c0c69N2a418fe110c3a4d5N2a58471d48d497d3N2a7db726d56af9dbN2a8a7e48bcc78c5aN2ac6abfe6d3e143aN2b280f272a00460aN2d0eb7173732a5daN2e18cea6dd39edf5N2e6b95af151f0c2eN2e6bace6a78d7949N3008d2335ed5333eN3051b22d223758b2N307d3409d3a172d6N307dbb12a64af9ffN30e2cd72ac0330ddN310fb011b061a929N318f316964572ee6N3214d72bc8cd42e5N322ffce66fd9bde5N34a642cb61d96b91N359a3a72da2fbe80N35d142c6fa129eeeN38dbfa36a9b73c95N39223d5f102b6edbN39b617033977aa88N39d7a195e173e4aeN39fd32af97e17b75N3a4082a2cb2d7b98N3a8d9e2ce0c7fdb4N3ce1b1ac106ab0caN3d8d06a68aae2938N3d97429e3ebb6486N3dedab4edec3268cN3e082e9e80208fea"%lxh.
Ltac2 gd_tbl_P_x509_get_sig () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"].


Definition U_X509_GET_SIG : Z := 0x28494.
Notation X509_GET_SIG_STACK := 80 (only parsing).

Definition x509_get_sig_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP SIG P END lo : Z) (pad : word) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_sig ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.(2.&40.)Ltg,(2.&40.)(1.$4.Llen,$4.(1.$4.Lq,$4.(5.(6.$0.R16.(7.(8.O19.O18.O17.O16.R15.R14.R13.O15.O14.R12.R11.R10.R?.R>.R=.R<.R;.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.R:.R9.R8.R7.)O9.(9.O19.)O8.(:.(2.&40.))R6.(;.O1:.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O7.(10.O7.+8.))(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O18.)+50.)(12.&40.O18.))(13.(>.$4.$4.)))))O1.R6.)(5.(14.O1:.O1.R6.)(5.(15.O1:.R6.)(5.(6.(2.&40.)R12.(16.&40.R5.))(5.(5.(17.-3000.R5.)(18.R5.=))(5.(19.O1:.R6.O7.(=.$1:.(1;.(16.&40.R4.))(13.$1:.)))(5.(19.O1:.R6.O6.(1<.R3.O2.R2.R1.))(5.(1=.O1:.R6.O3.(12.&40.O18.))(5.(5.(18.O5.R4.)(18.R4.O4.))P,(6.$4.R5.=)(5.(18.(10.O5.+3.)R2.)(5.(18.=R3.)(6.$4.(10.R2.R3.)R5.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition x509_get_sig_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP SIG P END BUF lo : Z) (bs : list byte) (tg0 pad : word) (len0 q0 : Z),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m SIG (buf_cells tg0 pad len0 q0) ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= SIG \/ SIG + 24 <= PP) ->
  (PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (SIG + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= SIG) ->
  PP mod 8 = 0 -> SIG mod 8 = 0 -> 0 < PP -> 0 < SIG -> 0 < BUF ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - X509_GET_SIG_STACK -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) -> (SIG + 24 <= lo \/ bv_unsigned sp <= SIG) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 SIG ->
  evt segs (x509_get_sig_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP SIG P END lo pad m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Lemma U_x509_get_sig_spec {L : heap_layout} : x509_get_sig_stmt usegs U_X509_GET_SIG.
Proof.
  unfold x509_get_sig_stmt, U_X509_GET_SIG.
  intros until q0.
  intros HPP HSIG HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB.
  change (Z.of_nat 8) with 8 in PPB.
  pose proof (rw_cells_bound _ _ _ _ HSIG) as SIGB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ buf_cells] in SIGB.
  change (Z.of_nat 24) with 24 in SIGB.
  pose proof (munch_refl [(PP, PP + 8); (SIG, SIG + 24); (bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold buf_cells in HSIG.
  carve_frame 48%nat ST.
  lxp_split_frame [8;8;8;8;8;8]%nat. lxp_seps 48.
  (* [comment removed for export] *)
  pose proof (@sums2_ok _) as LXSUMS.
  lxp_run (PLANS [] [] 55%N SUMS2).
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
Qed.
