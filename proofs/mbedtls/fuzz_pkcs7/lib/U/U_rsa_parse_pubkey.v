(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts RepEcp EcpFacts RepRsa.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_platform_zeroize U_mpi_free U_mpi_grow U_mpi_addsub U_mpi_read_binary U_mpi_read_binary_r U_mpi_read_binary_proof U_mpi_cmp U_mpi_cmp_int U_mpi_bitlen U_asn1_get_mpi U_rsa_check_context U_rsa_check_pubkey U_rsa_complete.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00722a03b06e21a1 0 6 1 1 2 1 34 1 37 1 44 1 45 1P0076d42377c83b59 0 4 0 1 3 1 45 1 46 1P014c06d2601440d7 0 4 0 1 2 1 34 1 35 1P022afdf1f853f2a8 0 3 0 1 4 1 32 1P03505619f1a7a67c 0 1 1 1P03d3178034e02e96 0 2 0 1 33 1P07281500c264bcf4 0 4 0 1 3 1 35 1 36 1P0769e52d7917421e 1 1 16 2 0 1 32 1 3 4 1 33 1 34 16P07acda02a2397e25 0 2 0 1 5 1P0c2523125fe17fad 0 6 0 16 12 16 32 16 35 16 42 16 43 16P0d2c855fe8c9eff8 0 6 1 1 2 1 34 1 37 1 44 1 45 1P0f89f7897a4a068d 0 6 0 16 2 16 22 16 25 16 32 16 33 16P11bdf5a1693b4b58 0 4 0 1 2 1 44 1 45 1P13568d05a397411c 0 4 0 1 2 1 34 1 35 1P16135e306e7dcb17 0 2 0 1 5 1P1674d12039e86bdb 0 2 0 1 5 1P179b05515b1c4d82 0 2 0 1 6 1P1a7eb16fe2a7b220 0 1 1 1P1c6576c21e9e6648 0 6 1 1 3 1 25 1 28 1 35 1 36 1P1e0f3107186f16ef 0 4 0 1 5 1 6 1 33 1P1efe85abe88f6cd1 0 4 0 1 3 1 5 1 33 1P1f5b1ee5967e3181 0 4 0 1 3 1 5 1 33 1P1fcd27ba1e4b73a4 0 1 1 1P20645706390f4893 0 3 0 1 4 1 32 1P245788da533b7cd9 0 4 0 1 3 1 35 1 36 1P24aeb6a64d613e91 0 4 0 1 5 1 6 1 33 1P2839352031806400 0 6 1 1 3 1 35 1 38 1 45 1 46 1P28b5faae0ddd6d6a 0 2 0 1 32 1P2a17d5b51fb6b21e 0 2 0 1 34 1P2c0369e82e51e071 0 6 1 1 3 1 35 1 38 1 45 1 46 1P2c45fc720a2fbbfa 0 2 0 1 7 1P2f49454d739afec3 0 2 0 1 5 1P2f53d1b99c04eed3 0 2 0 1 6 1P330cfed43f8d3650 0 6 1 1 2 1 24 1 27 1 34 1 35 1P33ac36a78d961bf0 0 1 1 1P33eb42de9bc1e4f9 0 4 0 1 2 1 44 1 45 1P3424c8c2b4679990 0 6 1 1 3 1 25 1 28 1 35 1 36 1P34264a3d4d8dcda6 0 2 0 1 1 1P35e1f40472c0fcfb 0 6 1 1 2 1 24 1 27 1 34 1 35 1P360599d2dfeb5478 0 2 0 1 23 1P3616edda83aec44f 0 2 0 1 32 1P3686568f179b56c6 0 2 0 1 5 1P37ec18f80c2af6aa 0 2 0 1 6 1P3831ebedc1012382 0 2 0 1 24 1P385326fd87e07ea6 0 2 0 1 4 1P3b25db7524dfc9e3 0 4 0 1 3 1 45 1 46 1P3b5319b29d4428b4 0 2 0 1 6 1P3b9f9fd36d26228d 0 2 0 1 5 1P3bf077265b67bee1 1 1 16 2 0 1 42 1 3 14 1 43 1 44 16P3d79e7cc12a698e3 0 2 0 1 1 1N0167420bdc83ff74N019353f1289d68afN0202795188d9a54aN02c13a46712b652eN054a3fb3a419ec31N0618055c6c921ec9N08f97352bd8c7018N0c598395df8a348dN0d052ebab4d3e9c3N0d5aa34d2d242576N0ef36604eeff29caN0fb2d6165d8016f5N0fc9a15493b63e52N1067b8202ea4a144N108f49f6d42ff0f2N10cb677259f9352aN143474e10d69b20fN14566b520c1daa50N156c5445cb955819N157f4091475addedN159f865217228b21N15e5413f793e8f5dN163da00e42d3134dN17c783ff848392c7N187ba1605a9d5910N19505ba4a0b48411N1de03f1142bca22dN223d3ce56761acf4N22de1f0ddaa114d0N231b925e8abc8081N23503055b5f23ed9N23e6ceba2a002db0N244b7bdeb1f42a8dN24b5944beeebbb87N24e8a53b505d731aN2642b5fcae659dccN26e4c3648d4d0f1eN28110574e53eedb2N2812ce89628d0114N2999afe3426b2f3dN29e0f795c28a5f7fN2abd58003922f39cN2bf9ac7ff0491cdcN2cb54db646fe7f85N2e413359c7f746b7N2f912f74fba69872N30abda59f76c2312N316c5e8c78bdb60fN326b272ea6c96a84N33458a28255abcd4N3505c3be0eabbc43N35626396be48a9f7N3580cddee56fd9d4N36c412cdd419e1dfN375da11b2222ce5eN37f6c7b5025157d2N3829e66d3ee6b1f9N3940c1fd02c499ffN3967afaa64b19d66N3ae9fad9971d91d6N3b110ee2b026e2baN3c8373d780c7d4e6N3d2a4da552a99c2d"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_rsa_parse_pubkey () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_st"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_at"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_limb_blocks"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.RSA_CTX_SIZE"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_fresh"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "rsa_parse_pubkey_post"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.mpdr_at"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.rsa_zero_mpds"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Lists.ListDef.firstn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.skipn"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.U.U_rsa_check_context.rsa_field_live"; "RPG.pstate"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_N"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_E"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.mkRSA"; "RocqVerifyHarness.AgentSubmission.Spec.RepRsa.r_len"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "pstate"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"].


Definition U_RSA_PARSE_PUBKEY : Z := 0x2a888.
(* [comment removed for export] *)
Notation RSA_PARSE_PUBKEY_STACK := 256 (only parsing).

Definition rsa_parse_pubkey_post (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (h : HST segs L HI) (LB : list blk) (C : Z) (lo : Z) (m : mem) (mo : Model) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Lc,$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lmo',$4.(1.(5.O1;.O1:.O19.)Lh',(5.O1;.O1:.O19.)(1.(6.$7.)LLB',(6.$7.)(1.$8.Lr',$8.(9.(:.$0.R15.(;.(<.(=.O18.O17.O16.O15.R14.R13.R12.O14.O13.R11.R10.R?.R>.R=.R<.R;.R:.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R9.R8.R7.R6.)O8.(>.O18.)O7.(?.(2.&40.))R5.(10.O1;.))R4.))(9.(11.O1;.R5.)(9.(12.O1;.R5.O3.(13.&40.O17.))(9.(14.O1.R4.)(9.(:.$15.(16.O1;.O1:.O19.R3.)(16.O1;.O1:.O19.O6.))(9.(17.O1;.O1:.O19.R3.R2.R5.R4.)(9.(18.O1;.R5.R2.O4.R1.)(9.Pb,$7.P,(19.$7.R1.R3.)(1:.(19.$7.R2.O5.)(19.$7.R2.(1;.R3.)))(9.Pb,$7.P,(19.$7.R1.O5.)(19.$7.R2.R4.)(9.Pb,$7.P,(19.$7.R1.(1;.R2.))(1<.(19.$7.R2.O5.))(9.(1=.O1;.O1:.O5.(13.&40.O17.)(1>.(1?.$15.$15.)(20.$15.$15.O4.(21.O4.$22.))(23.(1?.$15.$15.)))O2.R5.)(24.O1;.O1:.R5.))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition rsa_parse_pubkey_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(25.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$4.Ph,(5.O5.O4.O3.)PLB,(6.$7.)PC,$15.PKEY,$15.Pkbs,(6.(2.&8.))Plo,$15.P,(17.O5.O4.O3.R6.R5.R8.R7.)P,(18.O5.R9.R6.R5.(26.R5.))P,(27.O5.R:.R5.R4.)P,(28.=R6.)P,(28.(21.R7.(29.(2:.(2.&8.)R6.)))(2;.+2.+3?.))P,(2<.O4.R:.R6.R8.(29.(2:.(2.&8.)R7.)))P,(1:.(2=.(21.R9.(29.(2:.(2.&8.)R8.)))R:.)(2=.(21.R:.$22.)R9.))P,(1:.(2=.(21.R:.(29.(2:.(2.&8.)R9.)))R8.)(2=.(13.&40.R2?.)R:.))P,(12.O5.R10.R9.(13.&40.R30.))P,(2=.R:.(2>.(2>.(13.&40.R31.)+100.)(2?.O4.)))P,(2=.(30.O4.)R;.)P,(2=.(13.&40.R33.)(16.O5.O4.O3.R11.))P,(:.$15.(31.(13.&40.R34.)+10.)=)P,(2=.(32.O4.)(30.O4.))P,(:.(2.&40.)R34.(33.&40.(34.O4.)))P,(11.O5.R17.)P,(24.O5.O4.R18.)P,(35.O4.O1.+8.)P,(:.$15.(31.(13.&40.R3;.)+2.)=)P,(:.(2.&40.)R33.(33.&40.R17.))P,(:.(2.&40.)R33.(33.&40.R17.))P,(:.(2.&40.)R33.(33.&40.(29.(2:.(2.&8.)R17.))))(36.O5.R1=.(37.O5.O4.O3.R3?.R3>.R3=.R3<.R38.R37.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R20.R1?.R1<.R1;.R1:.R17.R1>.R1=.)(<.(=.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R20.(33.&40.O2.)R1?.(?.(2.&40.))R1>.(10.O5.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L32224124960.18L38396006073.18L50399682931.18L66910837588.1800000800@00H00PS1C1o2HoS1C1o2HoS1C1o2HoS1C1o2Ho". (* [comment removed for export] *)
Lemma zeros_presx : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Psegs,(6.$38.)PL,$39.Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(6.$7.)PLB1,(6.$7.)PSP,$15.PX,(6.$3:.)PC,$15.P,(3;.$3<.(3=.R9.R7.R5.)(3>.R1.))P,(1=.R:.R9.R5.R4.R3.R8.R7.)P,(11.R;.R9.)P,(11.R<.R9.)P,(19.(1?.$15.$15.)(20.$15.$15.R5.+>8.)R8.)P,(3?.R7.(21.R6.+30.)+;0.)(3;.$3<.(3=.R?.R<.R:.)(3>.R7.))")
(* [comment removed for export] *).
Proof.
  intros segs L m m' LB LB1 SP X C H HP MI MI' CIN DX.
  apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) H d Hd) as Hm.
  unfold rsa_zero_mpds in Hd. apply in_map_iff in Hd. flat constr:(Hd) 3%nat. flclear Hd. intros o <- Ho. apply rsa_zero_offs_spec in Ho.
  eapply mpdr_at_presx; [exact Hm| exact HP| exact MI| exact MI'| | |].
  - cbn [md_addr mpd_z]. eapply client_range_blk; [exact CIN| lia| lia].
  - cbn [md_addr mpd_z]. eapply disjoint_from_sub; [exact DX| lia| lia].
  - cbn. intros; discriminate.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L32224124960.15L66910837588.1500000800@S1C1o2HoS1C1o2Ho". (* [comment removed for export] *)
Lemma zeros_munch : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Psegs,(6.$38.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(6.$7.)PW,(6.$3:.)PC,$15.P,(3;.$3<.(3=.R6.R5.R3.)(3>.R1.))P,(40.R3.R6.R5.)P,(41.R8.R7.R6.)P,(11.R9.R8.)P,(11.R:.R8.)P,(3?.R7.(21.R6.+30.)+;0.)(3;.$3<.(3=.R<.R:.R9.)(3>.R7.))")
(* [comment removed for export] *).
Proof.
  intros segs m m' LB W C H MU WM MI MI' DX.
  apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) H d Hd) as Hm.
  unfold rsa_zero_mpds in Hd. apply in_map_iff in Hd. flat constr:(Hd) 3%nat. flclear Hd. intros o <- Ho. apply rsa_zero_offs_spec in Ho.
  eapply EcpFacts.mpdr_at_munch; [exact Hm| exact MU| exact WM| exact MI| exact MI'| |].
  - cbn [md_addr mpd_z]. eapply disjoint_from_sub; [exact DX| lia| lia].
  - cbn. intros; discriminate.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12994750578.10L22261619173.10L25349417994.1000000A00L00ZS3KEY3kbs1p2ln2H3S3kbs2ln2H2S3KEY3kbs1p2H1". (* [comment removed for export] *)
Lemma sub_input : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Psegs,(6.$38.)Pmq,P,(2.&40.)(3.(2.&8.))PKEY,$15.Pkbs,(6.(2.&8.))Pp,$15.Pln,$15.P,(27.R6.R5.R4.R3.)P,(2=.R5.R3.)P,(2=.=R3.)P,(2=.(21.R5.R4.)(21.R7.(29.(2:.(2.&8.)R6.))))(9.(27.R:.R9.R6.(42.(2.&8.)(43.R5.)(44.(2.&8.)(43.(2>.R6.R8.))R7.)))(:.$15.(29.(2:.(2.&8.)(42.(2.&8.)(43.R5.)(44.(2.&8.)(43.(2>.R6.R8.))R7.))))R5.))")
(* [comment removed for export] *).
Proof.
  intros segs mq KEY kbs p ln KY H1 H2 H3. split; [eapply bytes_at_sub; [exact KY| lia| lia| lia]| apply bytes_at_sub_length; lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition blk_eq_dec (x y : blk) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* [comment removed for export] *)
Lemma field_munch : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Psegs,(6.$38.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PLB,(6.$7.)Pd,$3<.PW,(6.$3:.)P,(3=.R6.R5.R3.R2.)P,(1<.(:.$45.(46.R3.)$47.))P,(40.R3.R7.R6.)P,(41.R9.R8.R7.)P,(11.R:.R9.)P,(11.R;.R9.)P,(3?.R7.(48.R8.)+10.)P,P,(:.$45.(46.R9.)$49.)(3?.R9.(4:.R:.)(4;.+4.(4<.R:.)))(3=.R>.R<.R;.R:.)")
(* [comment removed for export] *).
Proof. intros. eapply mpdr_at_munch; eassumption. Qed.

Section RPG.
  Variable segs : list Segment.
  Variable L : heap_layout.
  Variable HI : heap_iface segs L.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP segs L HI h LB m mo -> List.NoDup (map fst LB).

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST segs L HI) (LB : list blk) (C KEY lo : Z) (kbs : list byte).
  Hypothesis K0 : 0 < KEY.
  Hypothesis KB : KEY + Z.of_nat (length kbs) < 2^63.
  Hypothesis CRK : client_range L LB lo KEY (Z.of_nat (length kbs)).
  Hypothesis DKC : KEY + Z.of_nat (length kbs) <= C \/ C + 232 <= KEY.
  Hypothesis DKS : KEY + Z.of_nat (length kbs) <= lo \/ bv_unsigned sp <= KEY.
  Hypothesis SLO : lo <= bv_unsigned sp - RSA_PARSE_PUBKEY_STACK - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top segs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Variable MSF : Z.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis CIN : In (C, 232) LB.
  Hypothesis CAL : C mod 16 = 0.
  Hypothesis C0 : 0 < C.
  Hypothesis CAC : C + 232 <= alloc_ceiling.
  Hypothesis CND : C + 232 <= hl_img_lo L \/ hl_img_hi L <= C.
  Hypothesis HBR : Forall (fun b => block_range L (fst b) (snd b)) LB.

  Notation END := (KEY + Z.of_nat (length kbs)).

  (* [comment removed for export] *)
  Definition pstate (mq : mem) (moq : Model) (hq : HST segs L HI) (LBq : list blk) (r : rsa_st) (lenw pw : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "(9.(17.Vsegs,VL,VHI,O5.O4.O7.O6.)(9.(:.$15.(16.Vsegs,VL,VHI,O5.)(16.Vsegs,VL,VHI,Vh,))(9.(14.Vmo,O6.)(9.(18.Vsegs,O7.O4.VC,O3.)(9.Pb,$7.P,(19.$7.R1.O4.)(1:.(19.$7.R2.VLB,)(19.$7.R2.(1;.O3.)))(9.Pb,$7.P,(19.$7.R1.VLB,)(19.$7.R2.O4.)(9.Pb,$7.P,(19.$7.R1.(1;.O3.))(1<.(19.$7.R2.VLB,))(9.(1=.Vsegs,VL,VLB,(13.&40.Vsp,)(1>.(1?.$15.$15.)(20.$15.$15.VC,(21.VC,+>8.))(23.(1?.$15.$15.)))Vm,O7.)(9.(24.Vsegs,VL,O7.)(9.(11.Vsegs,O7.)(9.(12.Vsegs,O7.Vlo,(21.(13.&40.Vsp,)-30.))(9.(4=.Vsegs,O7.(21.(13.&40.Vsp,)-30.)(1>.$4>.(4?.O2.)(1>.$4>.(4?.O1.)(1>.$4>.(4?.Vs2,)(1>.$4>.(4?.Vs1,)(1>.$4>.(4?.Vs0,)(1>.$4>.(4?.Vra,)(23.$4>.))))))))(27.Vsegs,O7.VKEY,Vkbs,)))))))))))))")
(* [comment removed for export] *).

  Lemma field_live_of : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))Pmoq,$4.Phq,(5.Vsegs,VL,VHI,)PLBq,(6.$7.)Pd,$3<.P,(17.Vsegs,VL,VHI,R3.R2.R5.R4.)P,(3=.Vsegs,R6.R3.R2.)P,(1<.(:.$45.(46.R3.)$47.))(50.VL,R4.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq d HH HM NS. split; [exact NS|]. intros HO.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BR _.
    flat constr:((mpdr_blk_facts segs L mq LBq d HM HO BR)) 5%nat. intros _ _ P0 P4 _. split; assumption.
  Qed.


  (* [comment removed for export] *)
  Lemma zeros_relb : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))PLB1,(6.$7.)PLB2,(6.$7.)P,(3;.$3<.(3=.Vsegs,R3.R2.)(3>.VC,))(3;.$3<.(3=.Vsegs,R4.R2.)(3>.VC,))")
(* [comment removed for export] *).
  Proof.
    intros mq LB1 LB2 H. apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) H d Hd) as Hm.
    unfold rsa_zero_mpds in Hd. apply in_map_iff in Hd. flat constr:(Hd) 3%nat. flclear Hd. intros o <- _. exact Hm.
  Qed.

  Lemma null_relb : forall mq LB1 LB2 d, mpdr_at segs mq LB1 d -> md_own d = LNull -> mpdr_at segs mq LB2 d.
  Proof. intros mq LB1 LB2 d (HR & HAL & HPOS & HL & HN & HO) E. rewrite E in HO. repeat (split; [assumption|]). rewrite E. exact HO. Qed.

  Lemma relb : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))PLB1,(6.$7.)PLB2,(6.(1?.$15.$15.))Pd,$3<.P,(3=.Vsegs,R4.R3.R1.)P,P,(:.$45.(46.R2.)$49.)(19.(1?.$15.$15.)(20.$15.$15.(4:.R3.)(4;.+4.(4<.R3.)))R4.)(3=.Vsegs,R6.R4.R3.)")
(* [comment removed for export] *).
  Proof.
    intros mq LB1 LB2 d (HR & HAL & HPOS & HL & HN & HO) HIN. repeat (split; [assumption|]).
    destruct (md_own d); [exact HO| | exact HO]. flat constr:(HO) 4%nat. flclear HO. intros N1 _ PAL U32. split; [exact N1|]. split; [exact (HIN eq_refl)|]. split; assumption.
  Qed.


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0@L11801272103.117L14665597417.117L19267364125.117L19646198478.120L22706553362.119L2776197978.117 L39834994973.117L41657934532.117L49642803854.117L57161175510.117L59315137787.121L63385439284.117L6456587498.117 L7329336713.117 00000e01201?02302E02R02_02l03903N04D04Q04^04kS2ra2sp1C3kbs1L3HLS3KEY2lo3DKC3DKS3SLO3ACL2C03CAC3SPBS2ra2sp1C3kbsS2ra2sp1C3kbsS1L3HLS2ra2sp1C3KEY2lo3kbs3SLO3ACL2C03CAC3SPB1a2Ha1DS2ra2sp1C3kbs1a2HaS2ra2sp1C3kbsS2ra2sp1C3kbsS2ra2sp1C3kbsS2ra2sp1C3kbsS2ra2sp1C3KEY3kbs3DKCS1L3HLS2ra2sp1C3KEY2lo3kbs3SLO3ACL2C03CAC3SPB1a2Ha1D1XS2ra2sp1C3kbsS2ra2sp1C3kbsS2ra2sp1C3kbs". (* [comment removed for export] *)
  Lemma pstate_importN : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))Pmoq,$4.Phq,(5.Vsegs,VL,VHI,)PLBq,(6.$7.)Pr,$8.Plenw,(2.&40.)Ppw,(2.&40.)Pm2,P,(2.&40.)(3.(2.&8.))Pmo2,$4.Ph2,(5.Vsegs,VL,VHI,)PLB2,(6.$7.)PdN',$3<.P,(51.R<.R;.R:.R9.R8.R7.R6.)P,(:.$45.(46.(52.R9.))$53.)P,(:.$45.(46.(54.R:.))$53.)P,(17.Vsegs,VL,VHI,R6.R5.R8.R7.)P,(:.$15.(16.Vsegs,VL,VHI,R7.)(16.Vsegs,VL,VHI,Vh,))P,(14.R10.R9.)P,(55.Vsegs,R;.R8.R7.)P,(56.R10.(52.R?.)R9.R8.)P,(1=.Vsegs,VL,R11.(21.(13.&40.Vsp,)-30.)(57.(52.R10.))R14.R=.)P,(24.Vsegs,VL,R>.)P,(11.Vsegs,R?.)P,(12.Vsegs,R10.Vlo,(21.(13.&40.Vsp,)-30.))P,Pb,$7.P,(19.$7.R1.(58.R>.))(1:.(19.$7.R2.(58.(52.R16.)))(1<.(19.$7.R2.R17.)))(51.R12.R11.R10.R?.(59.(5:.R15.)R>.(54.R15.))R14.R13.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq r lenw pw m2 mo2 h2 LB2 dN' (HH & HTc & MF & RAT & L1 & L2 & L3 & PX & SOK & MI & ST & FR & KY) ON OE HH2 HT2 MF2 MN2 OUT PX2 SOK2 MI2 ST2 FRESH.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(RAT) 15%nat. flclear RAT. intros HD HT AN AE OKN OKE LEN ALL CAL' C0' CB CINq PN PE PNE. unfold RSA_CTX_SIZE in CB, CINq.
    pose proof (Forall_inv (Forall_inv_tail ALL)) as ME. pose proof (Forall_inv_tail (Forall_inv_tail ALL)) as ZS.
    unfold mpd_ivs in PX2. rewrite ON, AN in PX2.
    assert (BLKN : mpd_blk (r_N r) = []) by (unfold mpd_blk; rewrite ON; reflexivity).
    rewrite BLKN in FRESH.
    flat constr:(OUT) 5%nat. flclear OUT. intros AN2 NST2 O1 O2 O3. rewrite BLKN in O2. rewrite AN in AN2.
    assert (SUB : forall b, In b LBq -> In b LB2) by (intros b Hb; apply O2; [exact Hb| intros []]).
    assert (CIN2 : In (C, 232) LB2) by (apply SUB; exact CINq).
    pose proof (HND _ _ _ _ HH2) as ND2.
    (* [comment removed for export] *)
    assert (CR16 : forall a, C <= a -> a + 16 <= C + 232 -> client_range L LBq (bv_unsigned sp + -48) a 16).
    { intros a H1 H2. eapply client_range_blk; [exact CINq| exact H1| exact H2]. }
    split; [exact HH2|]. split; [exact HT2|]. split; [eapply mo_frame_trans; [exact MF| exact MF2]|].
    split.
    { (* [comment removed for export] *)
      split. { eapply heap_presx_rw_cells; [exact PX2| exact HD| eapply client_range_blk; [exact CINq| lia| cbn; lia] | cbn; lia]. }
      split. { eapply heap_presx_rw_cells; [exact PX2| exact HT| eapply client_range_blk; [exact CINq| lia| cbn; lia] | cbn; lia]. }
      cbn [r_N r_E r_len].
      split; [exact AN2|]. split; [exact AE|].
      split. { split; [exact NST2|]. right. exact (proj2 MN2). }
      split; [exact OKE|]. split; [exact LEN|].
      split.
      { unfold rsa_mpds. cbn [r_N r_E]. constructor; [exact (proj1 MN2)|]. constructor.
        - eapply null_relb with (LB1 := LBq); [| exact OE].
          eapply mpdr_at_presx; [exact ME| exact PX2| exact MI| exact MI2| rewrite AE; apply CR16; lia| rewrite AE; cbn; lia| rewrite OE; intros; discriminate].
        - eapply zeros_relb. eapply (zeros_presx segs L); [exact ZS| exact PX2| exact MI| exact MI2| exact CINq| cbn; lia]. }
      split; [exact CAL'|]. split; [exact C0'|]. split; [exact CB|]. split; [exact CIN2|].
      split.
      { intros HO E. flat constr:((proj1 MN2)) 6%nat. intros _ _ _ _ _ OWN. rewrite HO in OWN. flat constr:(OWN) 3%nat. flclear OWN. intros N1 PIN _.
        rewrite E in PIN.
        destruct (FRESH _ ltac:(unfold mpd_blk; rewrite HO, E; left; reflexivity)) as [[]|NIN].
        assert (EQ : (C, 4 * md_n dN') = (C, 232)).
        { destruct (blk_eq_dec (C, 4 * md_n dN') (C, 232)) as [Q|Q]; [exact Q|]. exfalso.
          exact (nodup_fst_neq _ _ _ _ _ ND2 CIN2 PIN Q eq_refl). }
        apply NIN. rewrite EQ. exact CINq. }
      split; [rewrite OE; intros; discriminate|]. rewrite OE. intros _ X; discriminate. }
    split.
    { intros b Hb. destruct (O1 b Hb) as [Hq|Hn].
      - destruct (L1 b Hq) as [Hl|Hr]; [left; exact Hl| right]. unfold rsa_limb_blocks in Hr |- *. cbn [r_N r_E]. rewrite BLKN in Hr. cbn in Hr. apply in_or_app. right. exact Hr.
      - right. unfold rsa_limb_blocks. cbn [r_N r_E]. apply in_or_app. left. exact Hn. }
    split; [intros b Hb; apply SUB, L2, Hb|].
    split.
    { intros b Hb HbLB. unfold rsa_limb_blocks in Hb. cbn [r_N r_E] in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      - destruct (FRESH b Hb) as [[]|NIN]. apply NIN, L2, HbLB.
      - apply (L3 b); [| exact HbLB]. unfold rsa_limb_blocks. apply in_or_app. right. exact Hb. }
    split.
    { eapply heap_presx_trans; [exact PX|].
      eapply (heap_presx_weak segs L) with (SP1 := bv_unsigned sp + -48) (X1 := [(C + 16, C + 16 + 16)]); [exact PX2| exact L2| lia|].
      intros a Ha. cbn in Ha |- *. lia. }
    split; [exact SOK2|]. split; [exact MI2|]. split; [exact ST2|].
    split. { eapply heap_presx_rw_cells; [exact PX2| exact FR| cbn; apply client_range_stack; lia| cbn; lia]. }
    eapply heap_presx_bytes_at; [exact PX2| exact KY| | cbn; lia].
    intros a Ha. destruct DKS as [D|D]; [| left; lia]. destruct (CRK a Ha) as [X|[X|X]]; [exfalso; lia| right; left; exact X| right; right].
    flat constr:(X) 3%nat. flclear X. intros b Hb R. exists b. split; [apply L2, Hb| exact R].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0@L11803453185.119L11805503105.122L19269672251.119L19646198478.122L22706553362.121L23141774031.119L2778338172.119 L27805062203.119L3187454762.123 L41672694498.119L48174641043.123L49628211880.119L56981320258.124L57175779824.119L59315137787.123L63400211474.119L6445911244.119 L7319041455.119 00000e01701D02802J02W02d03103>03K04904F04W04l05b05o06<06IS2ra2sp1C3kbs1L3HLS3KEY2lo3DKC3DKS3SLO3ACL2C03CAC3SPBS2ra2sp1C3kbs1r2APS2ra2sp1C3kbsS1L3HLS2ra2sp1C3KEY2lo3kbs3SLO3ACL2C03CAC3SPB1a2Ha1DS2ra2sp1C3kbs1a2HaS2ra2sp1C3kbsS2ra2sp1C3kbsS2ra2sp1C3kbsS2ra2sp1C3kbsS2ra2sp1C3kbsS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC1r3SPB2N1S2ra2sp1C3kbsS2ra2sp1C3kbs1r1QS2ra2sp1C3KEY3kbs3DKCS1L3HLS2ra2sp1C3KEY2lo3kbs3SLO3ACL2C03CAC3SPB1a2Ha1D1XS2ra2sp1C3kbsS2ra2sp1C3kbsS2ra2sp1C3kbs". (* [comment removed for export] *)
  Lemma pstate_importE : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))Pmoq,$4.Phq,(5.Vsegs,VL,VHI,)PLBq,(6.$7.)Pr,$8.Plenw,(2.&40.)Ppw,(2.&40.)Pm2,P,(2.&40.)(3.(2.&8.))Pmo2,$4.Ph2,(5.Vsegs,VL,VHI,)PLB2,(6.$7.)PdE',$3<.P,(51.R<.R;.R:.R9.R8.R7.R6.)P,(:.$45.(46.(54.R9.))$53.)P,(17.Vsegs,VL,VHI,R5.R4.R7.R6.)P,(:.$15.(16.Vsegs,VL,VHI,R6.)(16.Vsegs,VL,VHI,Vh,))P,(14.R?.R8.)P,(55.Vsegs,R:.R7.R6.)P,(56.R?.(54.R>.)R8.R7.)P,(1=.Vsegs,VL,R10.(21.(13.&40.Vsp,)-30.)(57.(54.R?.))R13.R<.)P,(24.Vsegs,VL,R=.)P,(11.Vsegs,R>.)P,(12.Vsegs,R?.Vlo,(21.(13.&40.Vsp,)-30.))P,Pb,$7.P,(19.$7.R1.(58.R=.))(1:.(19.$7.R2.(58.(54.R15.)))(1<.(19.$7.R2.R16.)))(51.R11.R10.R?.R>.(59.(5:.R14.)(52.R14.)R=.)R13.R12.)")
(* [comment removed for export] *).
  Proof.
    intros mq moq hq LBq r lenw pw m2 mo2 h2 LB2 dE' (HH & HTc & MF & RAT & L1 & L2 & L3 & PX & SOK & MI & ST & FR & KY) OE HH2 HT2 MF2 ME2 OUT PX2 SOK2 MI2 ST2 FRESH.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(RAT) 15%nat. flclear RAT. intros HD HT AN AE OKN OKE LEN ALL CAL' C0' CB CINq PN PE PNE. unfold RSA_CTX_SIZE in CB, CINq.
    pose proof (Forall_inv ALL) as MN. pose proof (Forall_inv_tail (Forall_inv_tail ALL)) as ZS.
    unfold mpd_ivs in PX2. rewrite OE, AE in PX2.
    assert (BLKE : mpd_blk (r_E r) = []) by (unfold mpd_blk; rewrite OE; reflexivity).
    rewrite BLKE in FRESH.
    flat constr:(OUT) 5%nat. flclear OUT. intros AE2 NST2 O1 O2 O3. rewrite BLKE in O2. rewrite AE in AE2.
    assert (SUB : forall b, In b LBq -> In b LB2) by (intros b Hb; apply O2; [exact Hb| intros []]).
    assert (CIN2 : In (C, 232) LB2) by (apply SUB; exact CINq).
    pose proof (HND _ _ _ _ HH2) as ND2. pose proof (HND _ _ _ _ HH) as NDq.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BRq BAq.
    (* [comment removed for export] *)
    assert (NAP : md_own (r_N r) = LHeap -> In (md_p (r_N r), 4 * md_n (r_N r)) LBq /\ (C + 232 <= md_p (r_N r) \/ md_p (r_N r) + 4 * md_n (r_N r) <= C)).
    { intros HO. flat constr:((mpdr_blk_facts segs L mq LBq _ MN HO BRq)) 5%nat. intros PIN N1 P0 P4 _. split; [exact PIN|].
      destruct (blocks_apart_neq _ _ _ BAq PIN CINq ltac:(intros E; apply (PN HO); injection E as E1 E2; exact E1) ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia. }
    split; [exact HH2|]. split; [exact HT2|]. split; [eapply mo_frame_trans; [exact MF| exact MF2]|].
    split.
    { (* [comment removed for export] *)
      split. { eapply heap_presx_rw_cells; [exact PX2| exact HD| eapply client_range_blk; [exact CINq| lia| cbn; lia] | cbn; lia]. }
      split. { eapply heap_presx_rw_cells; [exact PX2| exact HT| eapply client_range_blk; [exact CINq| lia| cbn; lia] | cbn; lia]. }
      cbn [r_N r_E r_len].
      split; [exact AN|]. split; [exact AE2|].
      split; [exact OKN|].
      split. { split; [exact NST2|]. right. exact (proj2 ME2). }
      split; [exact LEN|].
      split.
      { unfold rsa_mpds. cbn [r_N r_E]. constructor; [| constructor; [exact (proj1 ME2)|]].
        - eapply relb with (LB1 := LBq); [| intros HO; apply SUB; exact (proj1 (NAP HO))].
          eapply mpdr_at_presx; [exact MN| exact PX2| exact MI| exact MI2| rewrite AN; eapply client_range_blk; [exact CINq| lia| lia] | rewrite AN; cbn; lia|].
          intros HO. flat constr:((NAP HO)) 2%nat. intros PIN AP. split; [exact PIN| cbn; lia].
        - eapply zeros_relb. eapply (zeros_presx segs L); [exact ZS| exact PX2| exact MI| exact MI2| exact CINq| cbn; lia]. }
      split; [exact CAL'|]. split; [exact C0'|]. split; [exact CB|]. split; [exact CIN2|].
      split; [exact PN|].
      split.
      { intros HO E. flat constr:((proj1 ME2)) 6%nat. intros _ _ _ _ _ OWN. rewrite HO in OWN. flat constr:(OWN) 3%nat. flclear OWN. intros N1 PIN _.
        rewrite E in PIN.
        destruct (FRESH _ ltac:(unfold mpd_blk; rewrite HO, E; left; reflexivity)) as [[]|NIN].
        assert (EQ : (C, 4 * md_n dE') = (C, 232)).
        { destruct (blk_eq_dec (C, 4 * md_n dE') (C, 232)) as [Q|Q]; [exact Q|]. exfalso.
          exact (nodup_fst_neq _ _ _ _ _ ND2 CIN2 PIN Q eq_refl). }
        apply NIN. rewrite EQ. exact CINq. }
      intros HON HOE E. flat constr:((NAP HON)) 2%nat. intros PINN _.
      flat constr:((proj1 ME2)) 6%nat. intros _ _ _ _ _ OWN. rewrite HOE in OWN. flat constr:(OWN) 3%nat. flclear OWN. intros N1 PINE _.
      destruct (FRESH _ ltac:(unfold mpd_blk; rewrite HOE; left; reflexivity)) as [[]|NIN].
      assert (EQ : (md_p dE', 4 * md_n dE') = (md_p (r_N r), 4 * md_n (r_N r))).
      { destruct (blk_eq_dec (md_p dE', 4 * md_n dE') (md_p (r_N r), 4 * md_n (r_N r))) as [Q|Q]; [exact Q|]. exfalso.
        exact (nodup_fst_neq _ _ _ _ _ ND2 (SUB _ PINN) PINE Q (eq_sym E)). }
      apply NIN. rewrite EQ. exact PINN. }
    split.
    { intros b Hb. destruct (O1 b Hb) as [Hq|Hn].
      - destruct (L1 b Hq) as [Hl|Hr]; [left; exact Hl| right]. unfold rsa_limb_blocks in Hr |- *. cbn [r_N r_E]. rewrite BLKE in Hr. rewrite app_nil_r in Hr. apply in_or_app. left. exact Hr.
      - right. unfold rsa_limb_blocks. cbn [r_N r_E]. apply in_or_app. right. exact Hn. }
    split; [intros b Hb; apply SUB, L2, Hb|].
    split.
    { intros b Hb HbLB. unfold rsa_limb_blocks in Hb. cbn [r_N r_E] in Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      - apply (L3 b); [| exact HbLB]. unfold rsa_limb_blocks. apply in_or_app. left. exact Hb.
      - destruct (FRESH b Hb) as [[]|NIN]. apply NIN, L2, HbLB. }
    split.
    { eapply heap_presx_trans; [exact PX|].
      eapply (heap_presx_weak segs L) with (SP1 := bv_unsigned sp + -48) (X1 := [(C + 32, C + 32 + 16)]); [exact PX2| exact L2| lia|].
      intros a Ha. cbn in Ha |- *. lia. }
    split; [exact SOK2|]. split; [exact MI2|]. split; [exact ST2|].
    split. { eapply heap_presx_rw_cells; [exact PX2| exact FR| cbn; apply client_range_stack; lia| cbn; lia]. }
    eapply heap_presx_bytes_at; [exact PX2| exact KY| | cbn; lia].
    intros a Ha. destruct DKS as [D|D]; [| left; lia]. destruct (CRK a Ha) as [X|[X|X]]; [exfalso; lia| right; left; exact X| right; right].
    flat constr:(X) 3%nat. flclear X. intros b Hb R. exists b. split; [apply L2, Hb| exact R].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0@L11803485953.102L11807744665.104L12186017261.109L22700267513.106L22706555648.106L3187454762.109 L33669255183.105L39402961632.110L44483019854.102L57175812592.10200000e01601d02\02n03;03M03^04S04hS2ra2sp1C3kbs1L3HLS3KEY2lo3DKC3DKS3SLO3ACL2C03CAC3SPBS2ra2sp1C3kbs1r1HS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC3SPB1d2N1S1L3HLS2ra2sp1C2lo3kbs3SLO3ACL3DHI2C03CAC3CND3SPB1a2Ha1HS2ra2sp1C3kbs1a2HoS2ra2sp1C3kbsS2ra2sp1C3kbs1a2NOS2ra2sp1C3kbs1d1QS1L3HLS2ra2sp1C3KEY2lo3kbs3DKC3DKS3SLO3ACL2C03CAC3SPBS2ra2sp1C3KEY3kbs3DKC". (* [comment removed for export] *)
  Lemma pstate_len : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))Pmq',P,(2.&40.)(3.(2.&8.))Pmoq,$4.Phq,(5.Vsegs,VL,VHI,)PLBq,(6.$7.)Pr,$8.Plenw,(2.&40.)Ppw,(2.&40.)Plen',$15.P,(51.R9.R7.R6.R5.R4.R3.R2.)P,(40.(1>.(1?.$15.$15.)(20.$15.$15.(21.VC,+8.)(21.VC,+10.))(23.(1?.$15.$15.)))R:.R9.)P,(41.Vsegs,R;.R:.)P,(11.Vsegs,R;.)P,(4=.Vsegs,R<.VC,(1>.$4>.(5;.(33.&40.=))(1>.$4>.(5;.(33.&40.=))(1>.$4>.(4?.(33.&40.R5.))(23.$4>.)))))P,(9.(2=.=R6.)(28.R6.(2;.+2.+40.)))(51.R>.R=.R<.R;.(59.R7.(52.R:.)(54.R:.))R9.R8.)")
(* [comment removed for export] *).
  Proof.
    intros mq mq' moq hq LBq r lenw pw len' (HH & HTc & MF & RAT & L1 & L2 & L3 & PX & SOK & MI & ST & FR & KY) MU WM MI' HD' LB'.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(RAT) 15%nat. flclear RAT. intros HD HT AN AE OKN OKE LEN ALL CAL' C0' CB CINq PN PE PNE. unfold RSA_CTX_SIZE in CB, CINq.
    pose proof (Forall_inv ALL) as MN. pose proof (Forall_inv (Forall_inv_tail ALL)) as ME. pose proof (Forall_inv_tail (Forall_inv_tail ALL)) as ZS.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BRq BAq.
    assert (LAP : forall d, mpdr_at segs mq LBq d -> (md_own d = LHeap -> md_p d <> C) -> md_own d = LHeap ->
                  C + 232 <= md_p d \/ md_p d + 4 * md_n d <= C).
    { intros d Hd HNC HO. flat constr:((mpdr_blk_facts segs L mq LBq _ Hd HO BRq)) 5%nat. intros PIN N1 P0 P4 _.
      destruct (blocks_apart_neq _ _ _ BAq PIN CINq ltac:(intros E; apply (HNC HO); injection E as E1 E2; exact E1) ltac:(cbn; lia) ltac:(cbn; lia)) as [Q|Q]; cbn in Q; lia. }
    split; [| split; [exact HTc| split; [exact MF| split; [| split; [| split; [exact L2| split; [exact L3| split; [| split; [| split; [exact MI'| split; [| split]]]]]]]]]]].
    - apply (@HEAP_munch segs L HI hq _ mq mq' moq _ lo HH MU WM ACL).
      intros a Ha NO. cbn in NO. right; right. exists (C, 232). split; [exact CINq| cbn; lia].
    - split; [exact HD'|]. split; [eapply rw_cells_transport; [exact HT| exact MU| exact WM| cbn; lia]|].
      cbn [r_N r_E r_len]. split; [exact AN|]. split; [exact AE|]. split; [exact OKN|]. split; [exact OKE|]. split; [exact LB'|].
      split; [| tauto].
      unfold rsa_mpds. cbn [r_N r_E].
      constructor; [| constructor; [| eapply zeros_munch; [exact ZS| exact MU| exact WM| exact MI| exact MI'| cbn; lia]]].
      + eapply field_munch; [exact MN| exact (proj1 OKN)| exact MU| exact WM| exact MI| exact MI'| cbn; rewrite AN; lia|].
        intros HO. pose proof (LAP _ MN PN HO). cbn. lia.
      + eapply field_munch; [exact ME| exact (proj1 OKE)| exact MU| exact WM| exact MI| exact MI'| cbn; rewrite AE; lia|].
        intros HO. pose proof (LAP _ ME PE HO). cbn. lia.
    - unfold rsa_limb_blocks. cbn [r_N r_E]. exact L1.
    - eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn in Ho |- *. lia.
    - eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha NW. cbn. pose proof DIMG. lia.
    - eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| cbn; lia].
    - eapply rw_cells_transport; [exact FR| exact MU| exact WM| cbn; lia].
    - eapply bytes_at_transport; [exact KY| exact MU| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L22706593640.102L2802212018.99  L40792424124.99 L51078758152.102L51080547407.99 L58189536024.102L58766147575.103L58766302514.10800001:02602f03[04W05[06d07_S1L3HLS4DIMG2ra2sp1C3KEY2lo3kbs3DKC3DKS3SLO3ACL3DHI2C03CAC3wlo2HW3SPB1a2HaS1L3HLS2ra2sp1C3KEY2lo3kbs3DKC3DKS3SLO3ACL2C03CAC3wlo2HW3SPBS1L2ra2sp1C3KEY2lo3kbs3DKS3ACL2C03CAC3wlo2HW3SPBS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC1r3wlo2HW3SPB2P4S1L3HLS2ra2sp1C3KEY2lo3kbs3DKC3DKS3SLO3ACL2C03CAC3wlo2HW3SPBS4segs1L2HI3HLS2ra2sp1h1C2lo3kbs3SLO3ACL4HTOP2C03CAC3wlo2HW3SPB1a2NOS2ra2sp1C3kbs3wlo1a1X1L3HLS4DIMG3KEY2lo3DKC3DKS3SLO3ACL3DHI2C03CAC2HW3SPBS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC3wlo2HW3SPB1a1b1k1X2B4". (* [comment removed for export] *)
  Lemma pstate_below : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))Pmq',P,(2.&40.)(3.(2.&8.))Pmoq,$4.Phq,(5.Vsegs,VL,VHI,)PLBq,(6.$7.)Pr,$8.Plenw,(2.&40.)Ppw,(2.&40.)Pwlo,$15.P,(51.R9.R7.R6.R5.R4.R3.R2.)P,(40.(1>.(1?.$15.$15.)(20.$15.$15.R2.(21.(13.&40.Vsp,)-30.))(23.(1?.$15.$15.)))R:.R9.)P,(41.Vsegs,R;.R:.)P,(11.Vsegs,R;.)P,(12.Vsegs,R<.Vlo,(21.(13.&40.Vsp,)-30.))P,(2=.Vlo,R6.)(51.R>.R=.R<.R;.R:.R9.R8.)")
(* [comment removed for export] *).
  Proof.
    intros mq mq' moq hq LBq r lenw pw wlo (HH & HTc & MF & RAT & L1 & L2 & L3 & PX & SOK & MI & ST & FR & KY) MU WM MI' ST' HW.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:(RAT) 15%nat. flclear RAT. intros HD HT AN AE OKN OKE LEN ALL CAL' C0' CB CINq PN PE PNE. unfold RSA_CTX_SIZE in CB, CINq.
    pose proof (Forall_inv ALL) as MN. pose proof (Forall_inv (Forall_inv_tail ALL)) as ME. pose proof (Forall_inv_tail (Forall_inv_tail ALL)) as ZS.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BRq _.
    split; [| split; [exact HTc| split; [exact MF| split; [| split; [exact L1| split; [exact L2| split; [exact L3| split; [| split; [| split; [exact MI'| split; [exact ST'| split]]]]]]]]]]].
    - apply (@HEAP_munch segs L HI hq _ mq mq' moq _ lo HH MU WM ACL).
      intros a Ha NO. left. cbn in NO. rewrite HTc. lia.
    - split; [| split; [| split; [exact AN| split; [exact AE| split; [exact OKN| split; [exact OKE| split; [exact LEN| split; [| tauto]]]]]]]].
      + eapply rw_cells_transport; [exact HD| exact MU| exact WM| cbn; lia].
      + eapply rw_cells_transport; [exact HT| exact MU| exact WM| cbn; lia].
      + constructor; [| constructor; [| eapply zeros_munch; [exact ZS| exact MU| exact WM| exact MI| exact MI'| cbn; lia]]].
        * eapply field_munch; [exact MN| exact (proj1 OKN)| exact MU| exact WM| exact MI| exact MI'| cbn; rewrite AN; lia|].
          intros HO. flat constr:((mpdr_blk_facts segs L mq LBq _ MN HO BRq)) 5%nat. intros _ _ P0 P4 _. cbn. lia.
        * eapply field_munch; [exact ME| exact (proj1 OKE)| exact MU| exact WM| exact MI| exact MI'| cbn; rewrite AE; lia|].
          intros HO. flat constr:((mpdr_blk_facts segs L mq LBq _ ME HO BRq)) 5%nat. intros _ _ P0 P4 _. cbn. lia.
    - eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn. split; [| exact I].
      destruct Hc as [X|[[X _]|([b k] & Hb & X)]]; [lia| lia|]. cbn in X.
      flat constr:((proj1 (Forall_forall _ _) HBR _ Hb)) 5%nat. intros B0 _ _ B4 _. cbn in B0, B4. lia.
    - eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha NW. cbn. lia.
    - eapply rw_cells_transport; [exact FR| exact MU| exact WM| cbn; lia].
    - eapply bytes_at_transport; [exact KY| exact MU| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090@L11803389922.100L11805777061.103L22706593640.103L41672626689.100L44483120301.100L52101695852.104L52101802921.109L57175843091.100L58189536024.10300000e01S02N03C03S04M05A06206oS1L3HLS2ra2sp1C3KEY2lo3kbs3DKC3DKS3SLO3ACL2C03CAC3SPBS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC1r3SPB2P4S1L3HLS4DIMG2ra2sp1C2lo3kbs3SLO3ACL3DHI2C03CAC3CND3SPB1a2HaS1L3HLS2ra2sp1C3KEY2lo3kbs3DKC3DKS3SLO3ACL2C03CAC3SPBS2ra2sp1C2lo3kbsS2ra2sp1C3kbs1a1X1L3HLS4DIMG2lo3SLO3ACL3DHI2C03CAC3CND3SPBS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC3SPB1a1b1k1X2B4S1L3HLS2ra2sp1C3KEY2lo3kbs3DKS3SLO3ACL2C03CAC3SPBS4segs1L2HI3HLS2ra2sp1h1C2lo3kbs3SLO3ACL4HTOP2C03CAC3SPB1a2NO". (* [comment removed for export] *)
  Lemma pstate_frame : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))Pmq',P,(2.&40.)(3.(2.&8.))Pmoq,$4.Phq,(5.Vsegs,VL,VHI,)PLBq,(6.$7.)Pr,$8.Plenw,(2.&40.)Ppw,(2.&40.)Plenw',(2.&40.)Ppw',(2.&40.)P,(51.R:.R8.R7.R6.R5.R4.R3.)P,(40.(1>.(1?.$15.$15.)(20.$15.$15.(21.(13.&40.Vsp,)-30.)(13.&40.Vsp,))(23.(1?.$15.$15.)))R;.R:.)P,(41.Vsegs,R<.R;.)P,(11.Vsegs,R<.)P,(4=.Vsegs,R=.(21.(13.&40.Vsp,)-30.)(1>.$4>.(4?.R6.)(1>.$4>.(4?.R5.)(1>.$4>.(4?.Vs2,)(1>.$4>.(4?.Vs1,)(1>.$4>.(4?.Vs0,)(1>.$4>.(4?.Vra,)(23.$4>.))))))))(51.R>.R=.R<.R;.R:.R7.R6.)")
(* [comment removed for export] *).
  Proof.
    intros mq mq' moq hq LBq r lenw pw lenw' pw' (HH & HTc & MF & RAT & L1 & L2 & L3 & PX & SOK & MI & ST & FR & KY) MU WM MI' FR'.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(RAT) 15%nat. flclear RAT. intros HD HT AN AE OKN OKE LEN ALL CAL' C0' CB CINq PN PE PNE. unfold RSA_CTX_SIZE in CB, CINq.
    pose proof (Forall_inv ALL) as MN. pose proof (Forall_inv (Forall_inv_tail ALL)) as ME. pose proof (Forall_inv_tail (Forall_inv_tail ALL)) as ZS.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BRq _.
    split; [| split; [exact HTc| split; [exact MF| split; [| split; [exact L1| split; [exact L2| split; [exact L3| split; [| split; [| split; [exact MI'| split; [| split; [exact FR'|]]]]]]]]]]]].
    - apply (@HEAP_munch segs L HI hq _ mq mq' moq _ lo HH MU WM ACL).
      intros a Ha NO. left. cbn in NO. rewrite HTc. lia.
    - split; [| split; [| split; [exact AN| split; [exact AE| split; [exact OKN| split; [exact OKE| split; [exact LEN| split; [| tauto]]]]]]]].
      + eapply rw_cells_transport; [exact HD| exact MU| exact WM| cbn; lia].
      + eapply rw_cells_transport; [exact HT| exact MU| exact WM| cbn; lia].
      + constructor; [| constructor; [| eapply zeros_munch; [exact ZS| exact MU| exact WM| exact MI| exact MI'| cbn; lia]]].
        * eapply field_munch; [exact MN| exact (proj1 OKN)| exact MU| exact WM| exact MI| exact MI'| cbn; rewrite AN; lia|].
          intros HO. flat constr:((mpdr_blk_facts segs L mq LBq _ MN HO BRq)) 5%nat. intros _ _ P0 P4 _. cbn. lia.
        * eapply field_munch; [exact ME| exact (proj1 OKE)| exact MU| exact WM| exact MI| exact MI'| cbn; rewrite AE; lia|].
          intros HO. flat constr:((mpdr_blk_facts segs L mq LBq _ ME HO BRq)) 5%nat. intros _ _ P0 P4 _. cbn. lia.
    - eapply heap_presx_trans; [exact PX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn. split; [| exact I].
      destruct Hc as [X|[[X _]|([b k] & Hb & X)]]; [lia| lia|]. cbn in X.
      flat constr:((proj1 (Forall_forall _ _) HBR _ Hb)) 5%nat. intros B0 _ _ B4 _. cbn in B0, B4. lia.
    - eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha NW. cbn. lia.
    - eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| cbn; lia].
    - eapply bytes_at_transport; [exact KY| exact MU| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L11803681174.82L11805654624.86L11805879300.83L22706593640.85L41672858741.82L52101695852.86L52101802921.91L57176141671.82L58189536024.8500000e01h02]03X04M05G06;06l07iS1L3HLS2ra2sp1C3KEY2lo3kbs3DKC3DKS3SLO3ACL2C03CAC3SPBS1L3HLS2ra2sp1C3KEY2lo3kbs3DKC3DKS3SLO3ACL3SPA2C03CAC3SPB4CAL'1o2HoS1L3HLS2ra2sp1C3KEY2lo3kbs3DKC3DKS3SLO3ACL2C03CAC3SPBS1L3HLS4DIMG2ra2sp1C2lo3kbs3SLO3ACL3DHI2C03CAC3CND3SPB1a2HaS1L3HLS2ra2sp1C3KEY2lo3kbs3DKC3DKS3SLO3ACL2C03CAC3SPBS2ra2sp1C3kbs1a1X1L3HLS4DIMG2lo3SLO3ACL3DHI2C03CAC3CND3SPBS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC3SPB1a1b1k1X2B4S1L3HLS2ra2sp1C3KEY2lo3kbs3DKS3SLO3ACL2C03CAC3SPBS4segs1L2HI3HLS2ra2sp1h1C2lo3kbs3SLO3ACL4HTOP2C03CAC3SPB1a2NO". (* [comment removed for export] *)
  Lemma pstate_init : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pm1,P,(2.&40.)(3.(2.&8.))Plenw,(2.&40.)P,(17.Vsegs,VL,VHI,Vh,VLB,Vm,Vmo,)P,(18.Vsegs,Vm,VLB,VC,(26.VC,))P,(27.Vsegs,Vm,VKEY,Vkbs,)P,(12.Vsegs,Vm,Vlo,(13.&40.Vsp,))P,(11.Vsegs,Vm,)P,(24.Vsegs,VL,Vm,)P,(40.(1>.(1?.$15.$15.)(20.$15.$15.(21.(13.&40.Vsp,)-30.)(13.&40.Vsp,))(23.(1?.$15.$15.)))Vm,R8.)P,(41.Vsegs,Vm,R9.)P,(11.Vsegs,R:.)P,(4=.Vsegs,R;.(21.(13.&40.Vsp,)-30.)(1>.$4>.(4?.R:.)(1>.$4>.(4?.(33.&40.VKEY,))(1>.$4>.(4?.Vs2,)(1>.$4>.(4?.Vs1,)(1>.$4>.(4?.Vs0,)(1>.$4>.(4?.Vra,)(23.$4>.))))))))P,(12.Vsegs,R<.Vlo,(21.(13.&40.Vsp,)-30.))(51.R=.Vmo,Vh,VLB,(26.VC,)R<.(33.&40.VKEY,))")
(* [comment removed for export] *).
  Proof.
    intros m1 lenw HH RAT KY ST MI SOK MU WM MI' FR' ST'.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB. pose proof alloc_ceiling_pos as ACP.
    flat constr:(RAT) 15%nat. flclear RAT. intros HD HT AN AE OKN OKE LEN ALL CAL' C0' CB CINq PN PE PNE. unfold RSA_CTX_SIZE in CB, CINq.
    split; [| split; [reflexivity| split; [apply mo_frame_refl| split; [| split; [intros b Hb; left; exact Hb| split; [intros b Hb; exact Hb| split; [cbn; intros b []| split; [| split; [| split; [exact MI'| split; [exact ST'| split; [exact FR'|]]]]]]]]]]]].
    - apply (@HEAP_munch segs L HI h _ m m1 mo _ lo HH MU WM ACL).
      intros a Ha NO. left. cbn in NO. lia.
    - split; [| split; [| split; [exact AN| split; [exact AE| split; [exact OKN| split; [exact OKE| split; [exact LEN| split; [| tauto]]]]]]]].
      + eapply rw_cells_transport; [exact HD| exact MU| exact WM| cbn; lia].
      + eapply rw_cells_transport; [exact HT| exact MU| exact WM| cbn; lia].
      + unfold rsa_mpds, rsa_fresh in ALL |- *. cbn [r_N r_E] in ALL |- *.
        change (mpd_z (C + 16) :: mpd_z (C + 32) :: rsa_zero_mpds C) with (map (fun o => mpd_z (C + o)) [16; 32] ++ rsa_zero_mpds C) in ALL |- *.
        apply Forall_app in ALL. flat constr:(ALL) 2%nat. flclear ALL. intros A12 ZS. apply Forall_app. split.
        * apply Forall_forall. intros d Hd. pose proof (proj1 (Forall_forall _ _) A12 d Hd) as Hm.
          apply in_map_iff in Hd. flat constr:(Hd) 3%nat. flclear Hd. intros o <- Ho. cbn in Ho.
          eapply EcpFacts.mpdr_at_munch; [exact Hm| exact MU| exact WM| exact MI| exact MI'| cbn [md_addr mpd_z]; cbn; lia| cbn; intros; discriminate].
        * eapply zeros_munch; [exact ZS| exact MU| exact WM| exact MI| exact MI'| cbn; lia].
    - eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn. split; [| exact I].
      destruct Hc as [X|[[X _]|([b k] & Hb & X)]]; [lia| lia|]. cbn in X.
      flat constr:((proj1 (Forall_forall _ _) HBR _ Hb)) 5%nat. intros B0 _ _ B4 _. cbn in B0, B4. lia.
    - eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha NW. cbn. lia.
    - eapply bytes_at_transport; [exact KY| exact MU| cbn; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RPG.

Ltac b2z_close k :=
  exfalso;
  repeat match type of k with context [Z.ltb ?a ?b] =>
    first [ let H := fresh in assert (H : a < b) by lia; apply Z.ltb_lt in H; rewrite H in k; clear H
          | let H := fresh in assert (H : b <= a) by lia; apply Z.ltb_ge in H; rewrite H in k; clear H ] end;
  cbn in k; first [discriminate k | lia].

Section RP.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (h : HST usegs L HI) (LB : list blk) (C KEY lo : Z) (kbs : list byte).
  Hypothesis K0 : 0 < KEY.
  Hypothesis KB : KEY + Z.of_nat (length kbs) < 2^63.
  Hypothesis CRK : client_range L LB lo KEY (Z.of_nat (length kbs)).
  Hypothesis DKC : KEY + Z.of_nat (length kbs) <= C \/ C + 232 <= KEY.
  Hypothesis DKS : KEY + Z.of_nat (length kbs) <= lo \/ bv_unsigned sp <= KEY.
  Hypothesis SLO : lo <= bv_unsigned sp - RSA_PARSE_PUBKEY_STACK - hl_stack L.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis HTOP : bv_unsigned sp <= heap_top usegs L HI h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis TP : tp = Z_to_bv 64 (hl_tp L).
  Variable MSF : Z.
  Hypothesis HMSF : MSF = U_MEMSET_FUNC.
  Hypothesis CA : const_at L MSF 8.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis CIN : In (C, 232) LB.
  Hypothesis CAL : C mod 16 = 0.
  Hypothesis C0 : 0 < C.
  Hypothesis CAC : C + 232 <= alloc_ceiling.
  Hypothesis CND : C + 232 <= hl_img_lo L \/ hl_img_hi L <= C.
  Hypothesis HBR : Forall (fun b => block_range L (fst b) (snd b)) LB.

  Notation POST := (rsa_parse_pubkey_post usegs L HI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc h LB C lo m mo).
  Notation SPF := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Notation END := (KEY + Z.of_nat (length kbs)).

  (* [comment removed for export] *)
  Notation PST := (pstate usegs L HI ra sp s0 s1 s2 m mo h LB C KEY lo kbs).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L11741095640.95L26924648792.95L27904922642.97L43654564952.95L51711223320.96L7510805464.95 00000=00J01301@01M01ZS2ra2sp1C3kbsS2ra2sp1C3kbsS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC3SPBS2ra2sp1C3kbsS2ra2sp1C3kbsS2ra2sp1C3kbs". (* [comment removed for export] *)
  Lemma pp_exit : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))Pmoq,$4.Phq,(5.$5<.VL,VHI,)PLBq,(6.$7.)Pr,$8.Plenw,(2.&40.)Ppw,(2.&40.)Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Px0,(2.&40.)Px1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px2,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(5=.$5<.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vm,Vmo,Vh,VLB,VC,VKEY,Vlo,Vkbs,R1:.R19.R18.R17.R16.R15.R14.)(36.$5<.R1:.(37.$5<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VC,Vlo,Vm,Vmo,)(<.(=.R14.(33.&40.(21.(13.&40.Vsp,)-30.))Vgp,Vtp,R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(33.&40.+2::4<.)Vfc,(?.(2.&40.))R1;.(10.$5<.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros (HH & HTc & MF & RAT & L1 & L2 & L3 & PX & SOK & MI & ST & FR & KY).
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    zstep. zstep. zstep. zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
    apply aevtM_done. unfold rsa_parse_pubkey_post. do 17 eexists. exists hq, LBq, r.
    split; [reflexivity|]. unfold RSA_CTX_SIZE. repeat (split; [assumption|]). exact SOK.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma pp_err : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))Pmoq,$4.Phq,(5.$5<.VL,VHI,)PLBq,(6.$7.)Pr,$8.Plenw,(2.&40.)Ppw,(2.&40.)Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Px0,(2.&40.)Px1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px2,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(5=.$5<.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vm,Vmo,Vh,VLB,VC,VKEY,Vlo,Vkbs,R1:.R19.R18.R17.R16.R15.R14.)(36.$5<.R1:.(37.$5<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VC,Vlo,Vm,Vmo,)(<.(=.R14.(33.&40.(21.(13.&40.Vsp,)-30.))Vgp,Vtp,R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(33.&40.+2:8?8.)Vfc,(?.(2.&40.))R1;.(10.$5<.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros PS. flat constr:(PS) 11%nat. intros HH _ _ _ _ _ _ _ _ MI _.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    zstep. zstep. zstep. eapply pp_exit. exact PS.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L11805467289.91 L14664302896.124L14792943382.105L14792943382.122L14792959895.106L14792959895.123L19354909044.91 L19487810221.122L20788096573.122L20790193176.141L21177519580.105L23275454494.122L25604052563.91 L31695191108.125L36344376125.105L36346472735.124L3818671721.105 L4202106291.91  L49354231446.125L49705053714.91 L52067444116.125L59499841752.126L59499841752.91 L60690064055.141L806312532.105  L806312532.122  00000@00M01601_02H03103>04104Z05C05V06C06S07C07l08U08k09809V09j09k0:80:E0:R0;C0<4S2ra2sp1C3kbs2HBS2ra2sp1C3kbsS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03ACP3SPBS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03ACP3SPBS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03ACP3SPBS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03ACP3SPBS2ra2sp1C3kbsS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC1r3SGN3SPB3SGES1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC3SPBS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC3SPBS1L2ra2sp1C3kbs3CACS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL3CAL2C03CAC3SPBS2ra2sp1C3kbs2HBS2ra2sp1C3KEY3kbs2K02KB2C04lenw4pcur3PCB3SPB3LWBS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC3SPBS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC3SPBS1L2ra2sp1C2lo3kbs3ACLS2ra2sp1C3kbsS2ra2sp1C3KEY3kbs2K02KB2C03SPBS2ra2sp1C3kbs3SPB2HBFS2ra2sp1C3kbsS2ra2sp1C3kbsS2ra2sp1C3kbsS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL3SPA2C03CAC3ACP3SPBS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL3SPA2C03CAC3ACP3SPB". (* [comment removed for export] *)
  Lemma seg_D : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))Pmoq,$4.Phq,(5.$5<.VL,VHI,)PLBq,(6.$7.)Pr,$8.Plenw,(2.&40.)Ppcur,$15.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px2,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(5=.$5<.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vm,Vmo,Vh,VLB,VC,VKEY,Vlo,Vkbs,R18.R17.R16.R15.R14.R13.(33.&40.R12.))P,(9.(2=.VKEY,R13.)(2=.(21.R13.(13.&40.R14.))(21.VKEY,(29.(2:.(2.&8.)Vkbs,)))))P,(:.$15.(5>.(52.R16.))+1.)P,(:.$15.(5>.(54.R17.))+1.)(36.$5<.R1;.(37.$5<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VC,Vlo,Vm,Vmo,)(<.(=.R15.(33.&40.(21.(13.&40.Vsp,)-30.))Vgp,Vtp,R14.R13.R12.(33.&40.(21.VKEY,(29.(2:.(2.&8.)Vkbs,))))(33.&40.VC,)R11.R10.R?.R>.R=.R<.R;.R:.R9.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R8.R7.R6.R5.)VF,(33.&40.+2:9>4.)Vfc,(?.(2.&40.))R1<.(10.$5<.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros PS PCB SGN SGE.
    flat constr:(PS) 13%nat. intros HH _ _ _ _ _ _ _ _ MI ST FR _.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (bv_unsigned_in_range 64 lenw) as LWB. change (bv_modulus 64) with (2^64) in LWB.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    pose proof (conj HH I) as HH0. clear HH.
    zstep. zstep. zstep. zstep; if_cases KW2; zify_cond KW2; [exfalso; lia|].
    zstep. zstep. zstep. zstep; if_cases KN2; zify_cond KN2; [b2z_close KN2|].
    zstep. zstep.
    replace (bv_unsigned lenw + pcur) with (pcur + bv_unsigned lenw) in * by lia.
    flat constr:(HH0) 2%nat. flclear HH0. intros HH _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    lazymatch goal with F' : rw_cells usegs m1 (bv_unsigned sp + -48) [C8 lenw; C8 ?pw'; C8 s2; C8 s1; C8 s0; C8 ra] |- _ =>
      assert (PS1 : PST m1 moq hq LBq r lenw pw') by (eapply pstate_frame; try eassumption; first [exact PS| exact F']);
      clear F' end.
    clear PS MU WM ST HH. rename m1 into m0'.
    flat constr:(PS1) 13%nat. intros HH _ _ RAT _ _ _ _ _ MI1 ST FR _.
    flat constr:(RAT) 9%nat. intros HD _ AN AE OKN OKE LEN ALL _.
    pose proof (Forall_inv ALL) as MN. pose proof (Forall_inv (Forall_inv_tail ALL)) as ME. clear ALL.
    pose proof (field_live_of _ _ _ _ _ _ _ _ HH MN (proj1 OKN)) as LVN. pose proof (field_live_of _ _ _ _ _ _ _ _ HH ME (proj1 OKE)) as LVE.
    (* [comment removed for export] *)
    zstep.
    pose proof U_rsa_complete_spec as SP. unfold rsa_complete_stmt, U_RSA_COMPLETE in SP.
    eapply aevtM_cut_evt; [exact MK| eapply SP with (lo := lo) (LB := LBq) (r := r); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
      first [exact RAT| exact SGN| exact SGE| exact LVN| exact LVE| exact ST| exact MI1| reflexivity| unfold RSA_CTX_SIZE; lia] |].
    clear SP. cbv beta. intros ms' PO. unfold rsa_complete_post in PO. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by lia.
    flat constr:(PO) 21%nat. flclear PO. intros y0 y1 y2 z0 z1 z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 m2 -> MU2 WM2 MI2 ST2.
    replace (ret_pc (Z_to_bv 64 0x2aa10)) with (Z_to_bv 64 0x2aa10) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (PS2 : PST m2 moq hq LBq r lenw (Z_to_bv 64 (pcur + bv_unsigned lenw)))
      by (eapply pstate_below; try eassumption; try lia; first [exact PS1| exact MU2]).
    clear PS1 HH RAT HD MN ME LVN LVE MU2 WM2 ST MI1 FR MI AN AE OKN OKE LEN. rename MI2 into MI.
    flat constr:(PS2) 13%nat. intros HH _ _ RAT _ _ _ _ _ _ ST FR _.
    flat constr:(RAT) 9%nat. intros HD _ AN AE OKN OKE LEN ALL _.
    pose proof (Forall_inv ALL) as MN. pose proof (Forall_inv (Forall_inv_tail ALL)) as ME. clear ALL.
    pose proof (field_live_of _ _ _ _ _ _ _ _ HH MN (proj1 OKN)) as LVN. pose proof (field_live_of _ _ _ _ _ _ _ _ HH ME (proj1 OKE)) as LVE.
    zstep. zstep. zstep. zstep; if_cases K1; zify_cond K1.
    { eapply pp_exit. exact PS2. }
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    pose proof U_rsa_check_pubkey_spec as SP. unfold rsa_check_pubkey_stmt, U_RSA_CHECK_PUBKEY in SP.
    eapply aevtM_cut_evt; [exact MK| eapply SP with (lo := lo) (LB := LBq) (r := r); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
      first [exact HD| exact LVN| exact LVE| exact ST| split; [exact MN| lia] | split; [exact ME| lia] | eassumption| reflexivity| unfold RSA_CTX_SIZE; lia] |].
    clear SP. cbv beta. intros ms' PO. unfold rsa_ckpub_post in PO. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by lia.
    flat constr:(PO) 21%nat. flclear PO. intros w0 w1 w2 v0 v1 v2 v3 v4 v5 v6 v7 w3 w4 w5 w6 m3 -> MU3 WM3 MI3 ST3.
    replace (ret_pc (Z_to_bv 64 0x2aa2c)) with (Z_to_bv 64 0x2aa2c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (PS3 : PST m3 moq hq LBq r lenw (Z_to_bv 64 (pcur + bv_unsigned lenw)))
      by (eapply pstate_below; try eassumption; try lia; first [exact PS2| exact MU3]).
    clear PS2 HH RAT HD MN ME LVN LVE MU3 WM3 ST MI FR AN AE OKN OKE LEN. rename MI3 into MI.
    flat constr:(PS3) 13%nat. intros HH _ _ _ _ _ _ _ _ _ ST FR _.
    zstep. zstep. zstep; if_cases K2; zify_cond K2.
    { eapply pp_exit. exact PS3. }
    zstep. zstep. zstep. zstep. zstep.
    eapply pp_exit. exact PS3.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00g0@L10927964476.144L11672986577.112L11805467289.91 L12415153560.133L13513474930.112L14792943382.144L14792959895.164L17266589690.137L17485166146.144L18197933908.140L19354909044.91 L23325359358.124L24660008290.112L25076072338.137L25604052563.91 L29289228653.112L29311557968.160L29311558097.159L33669351805.146L34308876966.112L3630638320.121 L39179261132.112L4202106291.126 L4202106291.91  L42306726467.112L43056167378.144L43532372228.112L45190316876.112L49705053714.91 L51173085902.147L52302674621.112L54349069600.144L54805740431.137L57628696595.136L58451400700.3  L59308628304.1  L59308633593.128L59314873579.148L59315137787.148L59499841752.125L59499841752.91 L59656867194.147L60033852178.144L60042324106.175L60835850470.139L61300841723.144L61870911213.112L62770210624.112L62973239628.140L65042670712.125L67448148992.140L67858294733.164L68282338385.112L7707712115.144 L806312532.144  00001S02\02l03M04204^05J05h07N08608C09Y0:70:U0:e0;g0;h0;i0=40=R0=S0>40>U0>b0?@0@W0A<0B60BJ0D40E:0FL0Fj0GS0G]0Ga0I70JO0L;0L\0Li0NG0Nl0OQ0Oo0P]0Q_0RE0S40T90UI0Vg0X00YO0[2S1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs3DKS3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPB2rt2p42L43RT03P4a3P4b3ibsS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs3SLO3ACL3SPA2C03CAC2lv4pcur3PCB3SPB2FBS2ra2sp1C3kbs2HBS2ra2sp2s02s12s21C2lo3kbs2lv4pcurS2ra2sp2s02s12s21C3KEY3kbs2KB2lv4pcurS2ra2sp2s02s12s21C3kbs2lv4pcur3SPB2FB2rt3ibsS2ra2sp2s02s12s21C3kbs2lv4pcur3SPB2FB2rt3ibsS2ra2sp2s02s12s21C3kbs2lv4pcurS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs2KB3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPB2rt2p42L43P4B3RT03P4a3P4b3ibsS2ra2sp2s02s12s21C3kbs2lv4pcur2rt2L43L4BS2ra2sp1C3kbsS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPB2rt2p42RT3P4B2KRS2ra2sp2s02s12s21C3kbs2lv4pcurS2ra2sp2s02s12s21C3kbs2lv4pcurS2ra2sp1C3kbs2HBS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs3DKS3SLO3ACL2C03CAC2lv4pcur3SPBFFS1L3HLS2ra2sp2s02s12s21C2lo3kbs3SLO3ACL2C03CAC1r2lv4pcur3SPB2rt2AE3ibs1a2HaS2ra2sp2s02s12s21C3kbs2lv4pcurFS2ra2sp2s02s12s21C3kbs2lv4pcur2FBS2ra2sp2s02s12s21C3kbs2lv4pcur2rtS2ra2sp1C3kbsS2ra2sp2s02s12s21C3kbs2lv4pcurS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs2K03SLO3ACL2C02lv4pcur3PCB3LVB3ACP3SPB2rt2p43P4a3ibsS2ra2sp2s02s12s21C3KEY3kbs2K02lv4pcurS1L3HLS2ra2sp2s02s12s21C2lo3kbs3SLO3ACL2C02lv4pcur3ACP3SPBS2ra2sp1C3kbs3SPB2HBS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPB2rt2p42L43P4B3RT03P4a3P4b3ibs1a2Ha1DS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPBS1L2HI3HLS2ra2sp2s02s12s21h1C2lo3kbs3SLO3ACL4HTOP2C03CAC2hq2lv4pcur3SPB2rt3HTc3ibsS2ra2sp2s02s12s21C3kbs2lv4pcurS2ra2sp2s02s12s21C3kbs2lv4pcur2rt2RT1a2HaS2rv2Hr2K2S2K1S1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs2K03SLO3ACL2C02lv4pcur3PCB3LVB3ACP3SPB2rt2p43P4a2KZS1L3HLS2ra2sp2s02s12s21C2lo3kbs3SLO3ACL3DHI2C03CAC3CND1r2lv4pcur3SPB2rt2AE3ibs1a2Ha2Hd1HS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPB2rt2p42L43P4B3RT03P4a3P4b3ibs1a2Ha1D1XS2ra2sp2s02s12s21C3kbs2lv4pcur2rtS2ra2sp1C3kbsS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPB2rt2p42L43P4a3ibs1a2Ha1DS2ra2sp2s02s12s21C3kbs2lv4pcur2rt3ibsS2ra2sp2s02s12s21C3kbs2lv4pcur2rt3ibsS2ra2sp2s02s12s21C3kbs2lv4pcurS1L2ra2sp2s02s12s21C2lo3kbs3SLO2lv4pcur2rt3ibsS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs3DKS3SLO3ACL2C03CAC2lv4pcur3SPBS2ra2sp2s02s12s21C3KEY3kbs2lv4pcur3LVBS2ra2sp2s02s12s21C3KEY3kbs2lv4pcur2rt2p42L43P4bS2ra2sp2s02s12s21C3KEY3kbs2K02KB2C02lv4pcur3PCB3LVB3SPB2rt2p43P4B3P4aS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPB2rt2p43P4aS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPB2rt2p42L43P4a3P4b3ibs2rvS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs3SLO3ACL3SPA2C03CAC2lv4pcur3PCB3SPB2FBS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs3DKC3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPB2rt2p42L43P4a3P4b3ibsS1L3HLS2ra2sp2s02s12s21C3KEY2lo3kbs3SLO3ACL3SPA2C03CAC2lv4pcur3PCB3LVB3SPB2FB2rt2p43P4B3RT03P4a3ibs". (* [comment removed for export] *)
  Lemma seg_C : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))Pmoq,$4.Phq,(5.$5<.VL,VHI,)PLBq,(6.$7.)Pr,$8.Plv,$15.Ppcur,$15.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px2,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(5=.$5<.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vm,Vmo,Vh,VLB,VC,VKEY,Vlo,Vkbs,R18.R17.R16.R15.R14.(33.&40.R13.)(33.&40.R12.))P,(9.(2=.(21.VKEY,+2.)R13.)(2=.R13.(21.VKEY,(29.(2:.(2.&8.)Vkbs,)))))P,(9.(2=.=R15.)(2=.R15.(2>.(21.VKEY,(29.(2:.(2.&8.)Vkbs,)))R14.)))P,(:.$15.(5>.(52.R17.))+1.)P,(:.$45.(46.(54.R18.))$53.)(36.$5<.R1<.(37.$5<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VC,Vlo,Vm,Vmo,)(<.(=.R16.(33.&40.(21.(13.&40.Vsp,)-30.))Vgp,Vtp,R15.R14.R13.(33.&40.(21.VKEY,(29.(2:.(2.&8.)Vkbs,))))(33.&40.VC,)R12.R11.R10.R?.R>.R=.R<.R;.R:.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(33.&40.+2:96<.)Vfc,(?.(2.&40.))R1=.(10.$5<.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros PS PCB LVB SGN OE.
    flat constr:(PS) 13%nat. intros HH _ _ _ _ _ _ _ _ MI ST FR _.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] mq) as MU. pose proof (wmono_refl usegs mq) as WM.
    pose proof (conj HH I) as HH0. clear HH.
    zstep. zstep. zstep. zstep; if_cases KW1; zify_cond KW1; [exfalso; lia|].
    zstep. zstep. zstep. zstep; if_cases KN1; zify_cond KN1; [b2z_close KN1|].
    zstep.
    try replace (lv + pcur) with (pcur + lv) in * by lia.
    flat constr:(HH0) 2%nat. flclear HH0. intros HH _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    match goal with F' : rw_cells usegs m1 (bv_unsigned sp + -48) [C8 ?lw'; C8 ?pw'; C8 s2; C8 s1; C8 s0; C8 ra] |- _ =>
      assert (PS1 : PST m1 moq hq LBq r lw' pw') by (eapply pstate_frame; try eassumption; first [exact PS| exact F']);
      clear F' end.
    clear PS MU WM ST HH MI.
    flat constr:(PS1) 13%nat. intros HH _ _ RAT L1 L2 L3 _ SOK MI ST FR KY.
    flat constr:(RAT) 13%nat. intros HD _ AN AE OKN OKE LEN ALL _ _ CB CINq _. unfold RSA_CTX_SIZE in CB, CINq.
    pose proof (rw_cells_bound _ _ _ _ FR) as FB.
    zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    pose proof U_asn1_get_tag_spec as SP. unfold asn1_get_tag_stmt, U_ASN1_GET_TAG in SP.
    match type of FR with rw_cells _ _ _ [C8 ?lw; C8 ?pw; _; _; _; _] =>
      pose proof (rw_cells_app usegs m1 (bv_unsigned sp + -48) [C8 lw] [C8 pw; C8 s2; C8 s1; C8 s0; C8 ra]) as J1 end.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in J1. flat constr:((proj1 J1 FR)) 2%nat. intros FRL FRR. clear J1.
    pose proof (rw_cells_app usegs m1 (bv_unsigned sp + -48 + 8) [C8 (Z_to_bv 64 (pcur + lv))] [C8 s2; C8 s1; C8 s0; C8 ra]) as J2.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in J2. flat constr:((proj1 J2 FRR)) 2%nat. intros FRP FRS. clear J2 FRR.
    lazymatch type of FRP with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -40) in FRP by lia end.
    lazymatch type of FRS with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -32) in FRS by lia end.
    eapply aevtM_cut_evt; [exact MK| eapply SP with (PP := bv_unsigned sp + -40) (LENP := bv_unsigned sp + -48) (P := pcur + lv) (END := KEY + Z.of_nat (length kbs)) (BUF := KEY) (bs := kbs);
      rewrite ?(unsigned_lit (bv_unsigned sp + -48)), ?(unsigned_lit (bv_unsigned sp + -40)) by lia; first [exact FRP| exact FRL| exact KY| exact MI| reflexivity| lia| match goal with |- ?g => idtac "UNS" g end] |].
    clear SP. cbv beta. intros ms' PO. unfold asn1_get_tag_post in PO.
    flat constr:(PO) 29%nat. flclear PO. intros y0 y1 y2 xa0 z1 z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 m2 rt p4 L4 -> MU2 WM2 MI2 -> RT FRP2 FRL2 P4B P4OK.
    replace (ret_pc (Z_to_bv 64 0x2a9a4)) with (Z_to_bv 64 0x2a9a4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    assert (FRS2 : rw_cells usegs m2 (bv_unsigned sp + -40 + 8) [C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_transport; [replace (bv_unsigned sp + -40 + 8) with (bv_unsigned sp + -32) by lia; exact FRS| exact MU2| exact WM2| cbn; lia]. }
    pose proof (proj2 (rw_cells_app usegs m2 (bv_unsigned sp + -40) [C8 (Z_to_bv 64 p4)] [C8 s2; C8 s1; C8 s0; C8 ra])) as J3.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in J3. specialize (J3 (conj FRP2 FRS2)).
    replace (bv_unsigned sp + -40) with (bv_unsigned sp + -48 + 8) in J3 by lia.
    pose proof (proj2 (rw_cells_app usegs m2 (bv_unsigned sp + -48) [C8 L4] [C8 (Z_to_bv 64 p4); C8 s2; C8 s1; C8 s0; C8 ra])) as J4.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in J4. specialize (J4 (conj FRL2 J3)). clear J3 FRP2 FRL2 FRS2 FRS FRP FRL.
    assert (ST2 : stk usegs m2 lo (bv_unsigned sp + -48)) by (eapply stk_transport_disjoint; [exact ST| exact MU2| exact WM2| cbn; lia]).
    assert (PS2 : PST m2 moq hq LBq r L4 (Z_to_bv 64 p4)).
    { assert (MU2' : munch [(bv_unsigned sp + -48, bv_unsigned sp)] m1 m2) by (eapply munch_weaken; [| exact MU2]; intros a Ha; cbn in Ha |- *; lia).
      eapply pstate_frame; try eassumption; first [exact PS1| exact J4]. }
    clear PS1 HH RAT HD ALL SOK MI ST FR KY MU2 WM2 AN AE OKN OKE LEN CB CINq L1 L2 L3. rename MI2 into MI.
    flat constr:(PS2) 13%nat. intros HH HTc _ RAT L1' L2' L3' _ SOK _ ST FR KY.
    zstep; if_cases KR; zify_cond KR.
    { eapply pp_exit. exact PS2. }
    assert (RT0 : rt = 0) by lia. specialize (P4OK RT0). flat constr:(P4OK) 2%nat. flclear P4OK. intros P4a P4b.
    pose proof (bv_unsigned_in_range 64 L4) as L4B. change (bv_modulus 64) with (2^64) in L4B.
    zstep. zstep; if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|].
    zstep; if_cases KC2; zify_cond KC2; [exfalso; rewrite ?unsigned_lit in KC2 by lia; lia|].
    zstep. zstep; if_cases KC3; zify_cond KC3; [exfalso; rewrite ?unsigned_lit in KC3 by lia; change 7 with (Z.ones 3) in KC3; rewrite Z.land_ones in KC3 by lia; change (2 ^ 3) with 8 in KC3; lia|].
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    flat constr:(RAT) 15%nat. intros _ _ AN AE OKN OKE LEN ALL _ _ CB CINq PN PE _. unfold RSA_CTX_SIZE in CB, CINq.
    pose proof (Forall_inv (Forall_inv_tail ALL)) as ME.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BRq _.
    flat constr:((sub_input usegs m2 KEY kbs p4 (bv_unsigned L4) KY ltac:(lia) ltac:(lia) ltac:(lia))) 2%nat. intros HIB LENI.
    set (ibs := firstn (Z.to_nat (bv_unsigned L4)) (skipn (Z.to_nat (p4 - KEY)) kbs)) in HIB, LENI.
    pose proof (U_mpi_read_binary_spec_r L HI HFREE HCALLOC HLS SW DIMG HND MSF HMSF) as SP. unfold mpi_read_binary_stmt_r, U_MPI_READ_BINARY in SP.
    eapply aevtM_cut.
    { eapply SP with (dX := r_E r) (B := p4) (ibs := ibs) (lo := lo) (LB := LBq) (h := hq);
        rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia; rewrite ?LENI, ?AE;
        first [ exact HH | exact HIB | exact ST | exact ACL | exact DHI | exact TP | exact MI | exact SOK | exact CA | exact (proj1 OKE)
              | lazymatch goal with
                | |- mpi_at _ _ _ _ _ _ _ _ _ _ => rewrite <- AE; exact ME
                | |- mpd_writable _ _ _ _ _ =>
                    split; [| split; [intros a Ha Hd; exfalso; pose proof DIMG; lia| rewrite OE; intros; discriminate]];
                    rewrite HTc; intros a Ha; right; right; exists (C, 232); split; [exact CINq| cbn; lia]
                | |- client_range _ _ _ _ _ =>
                    intros a Ha; destruct DKS as [D|D]; [| left; lia]; destruct (CRK a ltac:(lia)) as [X|[X|X]]; [exfalso; lia| right; left; exact X| right; right];
                    (flat constr:(X) 3%nat; flclear X; intros b Hb R); exists b; split; [apply L2', Hb| exact R]
                | |- md_own _ = LHeap -> _ => rewrite OE; intros; discriminate
                | |- _ = Z_to_bv 64 _ => rewrite ?Z_to_bv_bv_unsigned; reflexivity
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => rewrite unsigned_lit by lia; reflexivity
                end
              | lia ]. }
    clear SP. cbv beta. intros ms' mo' PO. unfold mpi_read_binary_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by lia. rewrite ?LENI in PO.
    flat constr:(PO) 12%nat. flclear PO. intros MI3 ST3 MF3 HT3 HH3 HX3 HOUT HPX3 SOK3 Hr Hr0 HFRESH.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    match type of HH3 with HEAP _ _ _ ?hh ?LBB ?mm ?mmo => rename hh into h3; rename LBB into LB3; rename mm into m3; rename mmo into mo3 end.
    match type of HX3 with mpd_at _ _ _ ?d => rename d into dE3 end.
    match type of Hr with ?rr = 0 \/ _ => rename rr into rv end.
    assert (PS3 : PST m3 mo3 h3 LB3 (mkRSA (r_len r) (r_N r) dE3) L4 (Z_to_bv 64 p4)).
    { eapply pstate_importE; try eassumption; first [exact PS2| rewrite HT3; exact HTc| exact HOUT| exact HFRESH]. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
    clear PS2 HH HTc RAT L1' L2' L3' SOK ST FR KY ME BRq HIB MI. rename MI3 into MI.
    zstep; if_cases KRB; zify_cond KRB.
    2: { zstep. zstep. zstep. zstep. zstep; if_cases KRA; zify_cond KRA.
         { exfalso. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr. clear -Hr KRA KRB. destruct Hr as [-> | ->]; [vm_compute in KRB; exact (KRB eq_refl) | vm_compute in KRA; exact (KRA eq_refl)]. }
         zstep; if_cases KRE; zify_cond KRE.
         { (* [comment removed for export] *) eapply pp_exit. exact PS3. }
         exfalso. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr. clear -Hr KRE KRB. destruct Hr as [-> | ->]; [vm_compute in KRB; exact (KRB eq_refl) | vm_compute in KRE; discriminate KRE]. }
    (* [comment removed for export] *)
    eapply seg_D; [exact PS3| lia| exact SGN| cbn [r_E]; apply Hr0; clear -KRB Hr; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; destruct Hr as [-> | ->]; [reflexivity | vm_compute in KRB; discriminate KRB]].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00_0@L10632953650.111L11733510587.143L11733556127.146L11805467289.154L13352081286.156L14792943382.115L14792943382.143L14792959895.135L14792959895.144L14932067865.154L1576967403.115 L16396364324.115L17101786620.115L23528662352.115L24133020925.159L24224590217.143L26609628168.108L29311557968.120L29311558097.119L29323532093.143L29325628697.161L33669351805.117L37756016778.146L37764059922.115L4202106291.109 L42166861512.2  L42168520137.146L43938117536.3  L51173085902.118L51929089710.159L54349069600.115L58451400700.3  L59208969564.144L59308628304.1  L59308633593.111L59314873579.119L59315137787.119L59499841752.108L59656867194.118L59976694070.161L61300841723.115L62768161615.111L64193412887.154L68305879490.143L806312532.115  L806312532.143  L9418349343.111 00000M00N01H01_02f03S04C05005`06:07?08D09A0:E0:i0;`0<G0<H0<I0=90=i0>`0?10?B0?O0?X0@30@@0AH0Ai0Bg0C10CU0CY0DU0EY0Fc0G00H40HH0Hb0I?0IY0IZ0J\0Kd0L>S2ra2sp1C3KEY3kbs2lv4pcur3LVBFS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC3SPB3ibs3dN32rv2R02P4S2ra2sp1C3kbs3ibs2rv2HBS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC3SPB3ibs3dN32rv3CBR2HB5Ha_st5Hl_stS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03ACP3SPB3ibsS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03ACP3SPB3ibs2rvS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03ACP3SPB3ibsS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03ACP3SPB3ibs2rvS2ra2sp1C3kbs3ibs2rv2CB2HBS1L3HLS2ra2sp1C3KEY2lo3kbs3DKC3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPB3ibsS1L3HLS2ra2sp1C3KEY2lo3kbs3DKS3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPB3ibsS1L3HLS2ra2sp1C3KEY2lo3kbs2K03SLO3ACL2C04pcur3PCB3ACP3SPB3ibsS1L3HLS2ra2sp1C3KEY2lo3kbs2KB3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPB3ibsS2ra2sp1C3KEY3kbs2lv4pcur3LVB3ibs2rvS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC3SPB3ibs3dN32rv2ANS2ra2sp1C3KEY3kbs2K02KB2C04pcur3PCB3SPBFFS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC3SPB3ibs2rvS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC3SPB3ibs2rvS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL2C03CAC1r3SPB2AN3ibs1a2HaS2ra2sp1C3kbs3ibsS2ra2sp1C3kbs3ibsS2ra2sp1C3kbsS3dN33NR3S2ra2sp1C3kbs3ibs3dN32rv2P0S3dN33NR33CBRS1L3HLS2ra2sp1C3KEY2lo3kbs3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPB3ibs1a2Ha1DS2ra2sp1C3KEY3kbs4pcur3PCB3ibs2rvS1L2HI3HLS2ra2sp1h1C2lo3kbs3SLO3ACL4HTOP2C03CAC2hq3HTc3SPB3ibsS2rv2Hr2K2S1L2ra2sp1C2lo3kbs3ACL2C03ACP3ibs2rvS2K1S1L3HLS2ra2sp1C3KEY2lo3kbs2K03SLO3ACL2C04pcur3PCB3ACP3SPB2KZS1L3HLS2ra2sp1C2lo3kbs3SLO3ACL3DHI2C03CAC3CND1r3SPB2AN3ibs1a2Ha2Hd1HS1L3HLS2ra2sp1C3KEY2lo3kbs3SLO3ACL2C03CAC2lv4pcur3PCB3LVB3SPB3ibs1a2Ha1D1XS2ra2sp1C3kbsS1L3HLS2ra2sp1C3KEY2lo3kbs3SLO3ACL2C03CAC2lv4pcur3PCB3SPB3ibs1a2Ha1DS2ra2sp1C3kbs3ibs2rvS1L2ra2sp1C2lo3kbs3SLO3ibsS2ra2sp1C3KEY3kbs2lv4pcur3LVBS2ra2sp1C3kbs2C03ibs2rv2HBFS1L3HLS2ra2sp1C3KEY2lo3kbs3SLO3ACL3SPA2C03CAC4pcur3PCB3ACP3SPB3ibsS1L3HLS2ra2sp1C3KEY2lo3kbs3SLO3ACL3SPA2C03CAC4pcur3PCB3ACP3SPB3ibs2rv2R0S2ra2sp1C3KEY3kbs4pcur3PCB". (* [comment removed for export] *)
  Lemma seg_B : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))Pmoq,$4.Phq,(5.$5<.VL,VHI,)PLBq,(6.$7.)Pr,$8.Plv,$15.Ppcur,$15.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px2,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(5=.$5<.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vm,Vmo,Vh,VLB,VC,VKEY,Vlo,Vkbs,R18.R17.R16.R15.R14.(33.&40.R13.)(33.&40.R12.))P,(9.(2=.(21.VKEY,+2.)R13.)(2=.R13.(21.VKEY,(29.(2:.(2.&8.)Vkbs,)))))P,(9.(2=.=R15.)(2=.R15.(2>.(21.VKEY,(29.(2:.(2.&8.)Vkbs,)))R14.)))P,(:.$45.(46.(52.R17.))$53.)P,(:.$45.(46.(54.R18.))$53.)(36.$5<.R1<.(37.$5<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VC,Vlo,Vm,Vmo,)(<.(=.R16.(33.&40.(21.(13.&40.Vsp,)-30.))Vgp,Vtp,R15.R14.R13.(33.&40.(21.VKEY,(29.(2:.(2.&8.)Vkbs,))))(33.&40.VC,)R12.R11.R10.R?.R>.R=.R<.R;.R:.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R9.R8.R7.R6.)VF,(33.&40.+2:91<.)Vfc,(?.(2.&40.))R1=.(10.$5<.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros PS PCB LVB ON OE.
    flat constr:(PS) 13%nat. intros HH HTc _ RAT L1' L2' L3' _ SOK MI ST FR KY.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:(RAT) 15%nat. intros _ _ AN AE OKN OKE LEN ALL _ _ CB CINq PN PE _. unfold RSA_CTX_SIZE in CB, CINq.
    pose proof (Forall_inv ALL) as MN.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BRq _.
    zstep. zstep; if_cases KZ; zify_cond KZ; [exfalso; rewrite ?unsigned_lit in KZ by lia; lia|].
    zstep; if_cases KC0; zify_cond KC0; [exfalso; rewrite ?unsigned_lit in KC0 by lia; lia|].
    zstep. zstep; if_cases KC1; zify_cond KC1; [exfalso; rewrite ?unsigned_lit in KC1 by lia; change 7 with (Z.ones 3) in KC1; rewrite Z.land_ones in KC1 by lia; change (2 ^ 3) with 8 in KC1; lia|].
    zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    flat constr:((sub_input usegs mq KEY kbs pcur lv KY ltac:(lia) ltac:(lia) ltac:(lia))) 2%nat. intros HIB LENI.
    set (ibs := firstn (Z.to_nat lv) (skipn (Z.to_nat (pcur - KEY)) kbs)) in HIB, LENI.
    pose proof (U_mpi_read_binary_spec_r L HI HFREE HCALLOC HLS SW DIMG HND MSF HMSF) as SP. unfold mpi_read_binary_stmt_r, U_MPI_READ_BINARY in SP.
    eapply aevtM_cut.
    { eapply SP with (dX := r_N r) (B := pcur) (ibs := ibs) (lo := lo) (LB := LBq) (h := hq);
        rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia; rewrite ?LENI, ?AN;
        first [ exact HH | exact HIB | exact ST | exact ACL | exact DHI | exact TP | exact MI | exact SOK | exact CA | exact (proj1 OKN)
              | lazymatch goal with
                | |- mpi_at _ _ _ _ _ _ _ _ _ _ => rewrite <- AN; exact MN
                | |- mpd_writable _ _ _ _ _ =>
                    split; [| split; [intros a Ha Hd; exfalso; pose proof DIMG; lia| rewrite ON; intros; discriminate]];
                    rewrite HTc; intros a Ha; right; right; exists (C, 232); split; [exact CINq| cbn; lia]
                | |- client_range _ _ _ _ _ =>
                    intros a Ha; destruct DKS as [D|D]; [| left; lia]; destruct (CRK a ltac:(lia)) as [X|[X|X]]; [exfalso; lia| right; left; exact X| right; right];
                    (flat constr:(X) 3%nat; flclear X; intros b Hb R); exists b; split; [apply L2', Hb| exact R]
                | |- md_own _ = LHeap -> _ => rewrite ON; intros; discriminate
                | |- _ = Z_to_bv 64 _ => rewrite ?Z_to_bv_bv_unsigned; reflexivity
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => rewrite unsigned_lit by lia; reflexivity
                end
              | lia ]. }
    clear SP. cbv beta. intros ms' mo' PO. unfold mpi_read_binary_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by lia. rewrite ?LENI in PO.
    flat constr:(PO) 12%nat. flclear PO. intros MI3 ST3 MF3 HT3 HH3 HX3 HOUT HPX3 SOK3 Hr Hr0 HFRESH.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    match type of HH3 with HEAP _ _ _ ?hh ?LBB ?mm ?mmo => rename hh into h3; rename LBB into LB3; rename mm into m3; rename mmo into mo3 end.
    match type of HX3 with mpd_at _ _ _ ?d => rename d into dN3 end.
    match type of Hr with ?rr = 0 \/ _ => rename rr into rv end.
    assert (PS3 : PST m3 mo3 h3 LB3 (mkRSA (r_len r) dN3 (r_E r)) (Z_to_bv 64 lv) (Z_to_bv 64 pcur)).
    { eapply pstate_importN; try eassumption; first [exact PS| rewrite HT3; exact HTc| exact HOUT| exact HFRESH]. }
    pose proof (heap_mok _ _ HI _ _ _ _ HH3) as MK3.
    clear PS HH HTc RAT L1' L2' L3' SOK ST FR KY MN BRq HIB MI AN AE OKN OKE LEN ALL CB CINq PN PE MK. rename MI3 into MI. rename MK3 into MK.
    zstep; if_cases KRB; zify_cond KRB.
    2: { zstep. zstep. zstep. zstep. zstep; if_cases KRA; zify_cond KRA.
         { exfalso. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr. clear -Hr KRA KRB. destruct Hr as [-> | ->]; [vm_compute in KRB; exact (KRB eq_refl) | vm_compute in KRA; exact (KRA eq_refl)]. }
         zstep; if_cases KRE; zify_cond KRE.
         { (* [comment removed for export] *) eapply pp_exit. exact PS3. }
         exfalso. unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr. clear -Hr KRE KRB. destruct Hr as [-> | ->]; [vm_compute in KRB; exact (KRB eq_refl) | vm_compute in KRE; discriminate KRE]. }
    assert (R0 : rv = 0) by (clear -KRB Hr; unfold MBEDTLS_ERR_MPI_ALLOC_FAILED in Hr; destruct Hr as [-> | ->]; [reflexivity | vm_compute in KRB; discriminate KRB]). flat constr:((Hr0 R0)) 2%nat. intros SG3 _.
    (* [comment removed for export] *)
    flat constr:(PS3) 13%nat. intros HH HTc _ RAT _ _ _ _ SOK _ ST FR KY.
    flat constr:(RAT) 14%nat. intros HD _ AN AE OKN _ _ ALL _ _ CB CINq PN _. unfold RSA_CTX_SIZE in CB, CINq. cbn [r_N r_E r_len] in AN, OKN, PN, ALL.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros BRq _.
    flat constr:(HOUT) 2%nat. flclear HOUT. intros AN3 _. 
    zstep. zstep.
    pose proof U_mpi_size_spec as SP. unfold mpi_size_stmt, U_MPI_SIZE in SP.
    eapply aevtM_cut_evt; [exact MK| eapply SP with (lo := lo) (LB := LB3) (dX := dN3); rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by lia;
      first [ exact HX3 | exact MI | exact ST | rewrite AN; reflexivity | lia
            | intros HO; (flat constr:((mpdr_blk_facts usegs L m3 LB3 _ (proj1 HX3) HO BRq)) 5%nat; intros _ _ P0 P4 _); lia
            | destruct (md_own dN3) eqn:HO; [ pose proof (proj1 HX3) as (_ & _ & _ & _ & _ & OW); rewrite HO in OW; (flat constr:(OW) 2%nat; flclear OW; intros -> ->); lia
                                             | (flat constr:((mpdr_blk_facts usegs L m3 LB3 _ (proj1 HX3) HO BRq)) 5%nat; intros _ _ P0 P4 _); lia
                                             | exfalso; exact (proj1 OKN HO) ]
            | match goal with |- ?g => idtac "UNS3" g end ] |].
    clear SP. cbv beta. intros ms' PO. unfold mpi_size_post in PO. rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by lia.
    flat constr:(PO) 20%nat. flclear PO. intros w0 w1 w2 v1 v2 v3 v4 v5 v6 v7 w3 w4 w5 w6 m4 -> MU4 WM4 MI4 ST4.
    replace (ret_pc (Z_to_bv 64 0x2a968)) with (Z_to_bv 64 0x2a968) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (PS4 : PST m4 mo3 h3 LB3 (mkRSA (r_len r) dN3 (r_E r)) (Z_to_bv 64 lv) (Z_to_bv 64 pcur))
      by (eapply pstate_below; try eassumption; try lia; first [exact PS3| exact MU4]).
    flat constr:((proj1 HX3)) 6%nat. intros _ _ _ _ NR3 _. unfold MPI_MAX_LIMBS in NR3.
    pose proof (core_bitlen_range (md_limbs dN3) (md_n dN3) ltac:(clear -NR3; lia)) as CBR.
    clear PS3 HH HTc RAT HD SOK ST FR KY ALL BRq MU4 WM4 MI. rename MI4 into MI.
    flat constr:(PS4) 13%nat. intros HH _ _ RAT _ _ _ _ _ _ ST FR _.
    flat constr:(RAT) 2%nat. intros HD _. unfold rsa_head_cells in HD. cbn [r_len] in HD.
    (* [comment removed for export] *)
    pose proof (munch_refl [(C + 8, C + 16)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
    pose proof (conj HH I) as HH0. clear HH.
    zstep.
    flat constr:(HH0) 2%nat. flclear HH0. intros HH _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    lazymatch goal with HD' : rw_cells usegs m5 C [C4 _; C4 _; C8 (Z_to_bv 64 ?lenv)], MI5 : mem_inv usegs m5 |- _ =>
      assert (PS5 : PST m5 mo3 h3 LB3 (mkRSA lenv dN3 (r_E r)) (Z_to_bv 64 lv) (Z_to_bv 64 pcur))
        by (eapply pstate_len with (r := mkRSA (r_len r) dN3 (r_E r)); try eassumption; first [exact PS4| exact MU| exact HD'| clear -CBR NR3; lia]) end.
    eapply seg_C; [exact PS5| lia| lia| exact SG3| exact OE].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050@L19355408692.1  L22706553362.3  L25382598580.1  L34360476045.156L42751698021.15600000400=00A00n01QS2spS2sp1a2HaS2spS2ra2sp1C3KEY3kbs2C03SPB4lxv05lxv172H82H93H18S2ra2sp1C3KEY3kbs5lxv175lxv182H62H7". (* [comment removed for export] *)
  Lemma seg_A : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))Pmoq,$4.Phq,(5.$5<.VL,VHI,)PLBq,(6.$7.)Pr,$8.Plenw,(2.&40.)Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Px2,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(5=.$5<.VL,VHI,Vra,Vsp,Vs0,Vs1,Vs2,Vm,Vmo,Vh,VLB,VC,VKEY,Vlo,Vkbs,R17.R16.R15.R14.R13.R12.(33.&40.VKEY,))P,(:.$45.(46.(52.R14.))$53.)P,(:.$45.(46.(54.R15.))$53.)(36.$5<.R19.(37.$5<.VL,VHI,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VC,Vlo,Vm,Vmo,)(<.(=.R14.(33.&40.(21.(13.&40.Vsp,)-30.))Vgp,Vtp,R13.R12.R11.(33.&40.(21.VKEY,(29.(2:.(2.&8.)Vkbs,))))(33.&40.VC,)R10.R?.R>.R=.R<.R;.R:.R9.R8.Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(33.&40.+2:8;<.)Vfc,(?.(2.&40.))R1:.(10.$5<.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros PS1 ON OE.
    flat constr:(PS1) 13%nat. intros HH HTc _ RAT _ _ _ _ SOK MI ST FR KY.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    rename mq into m1.
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) [SUM_gettagP])
      by (intros AL; repeat constructor; apply apply_summary_sound; apply sum_gettagP_valid).
    apply (lxp_aevtM_of_evt usegs moq _ _ MK).
    lx_run_tac (PLANS [0x2aa4c; 0x2a8f8; 0x2a91c] [] 80%N [SUM_gettagP]); lx_tree.
    all: apply evt_done; cbv beta.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ ?mx _) =>
         (* [comment removed for export] *)
         repeat (lazymatch goal with Hf0 : rw_cells usegs mx (bv_unsigned sp + -48) ?cs0 |- _ =>
                   let v := eval vm_compute in (-48 + Z.of_nat (cells_size cs0)) in
                   match goal with Hf1 : rw_cells usegs mx (bv_unsigned sp + v) ?cs1 |- _ =>
                     let Hj := fresh "J" in
                     pose proof (proj2 (rw_cells_app usegs mx (bv_unsigned sp + -48) cs0 cs1)) as Hj;
                     cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in Hj;
                     replace (bv_unsigned sp + v) with (bv_unsigned sp + -48 + Z.of_nat (cells_size cs0)) in Hf1 by (cbn; clear; lia);
                     specialize (Hj (conj Hf0 Hf1)); clear Hf0 Hf1; cbn [app] in Hj end end);
         lazymatch goal with Hm : munch ?W1 ?ma mx, Hw : wmono _ ?ma' mx, Hi : mem_inv _ mx, Hf : rw_cells usegs mx (bv_unsigned sp + -48) [C8 ?lw; C8 ?pw; _; _; _; _] |- _ =>
           let MUW := fresh "MUW" in let PSx := fresh "PSx" in
           assert (MUW : munch [(bv_unsigned sp + -48, bv_unsigned sp)] ma mx) by (eapply munch_weaken; [| exact Hm]; intros a Ha; clear -Ha; cbn in Ha |- *; lia);
           assert (PSx : PST mx moq hq LBq r lw pw) by (eapply pstate_frame; try eassumption; first [exact PS1| exact Hf| exact MUW]);
           lazymatch pc with
           | 174668 => eapply pp_exit; exact PSx
           | 174328 => eapply pp_err; exact PSx
           | _ => eapply seg_B; [exact PSx| first [clear_disj; lia | lia] | first [clear_disj; lia | lia] | exact ON| exact OE]
           end
         end end.
    all: match goal with |- ?g => idtac "SEGA-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End RP.

Lemma fj8p : ltac2:(CDefT.buildp (gd_tbl_P_rsa_parse_pubkey ()) "Pmq,P,(2.&40.)(3.(2.&8.))PA,$15.Pbs,(6.(2.&8.))Prest,(6.$4>.)P,(4=.$5<.R4.R3.(1>.$4>.(5?.#8.R2.)R1.))(4=.$5<.R5.R4.(1>.$4>.(4?.(60.R3.))R2.))")
(* [comment removed for export] *).
Proof.
  intros mq A bs rest H. flat constr:(H) 2%nat. intros ((LEN & WF) & _) _. cbn [cell_wf] in LEN.
  eapply rw_cells_reshape; [exact H| split; [exact I| exact WF]|].
  cbn [cells_bytes cbytes]. rewrite le8_le_bytes_to_word by exact LEN. reflexivity.
Qed.

Section MAIN.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L10508741246.85L10508741246.86L10508741246.87L11741095640.83L11805467289.83L11805467289.84L19354909044.84L25382082548.84L25604052563.83L25604052563.84L26924648792.84L31378308326.85L31392867444.84L37414286068.84L43061788809.83L43442376564.83L43654564952.84L49705053714.83L49705053714.84L57412954142.86L59499841752.84L7510805464.84 00000100h01h02502E02U02b02o03?03O03\03i04604C04d05105>05R05f06D06Q06^FS1L3HLS2ra2sp1C3KEY3kbs2lo2HD3SLO3SPB2C02HB5Ha_st5Hl_stS1L3HLS2ra2sp2s01C3KEY3kbs2lo2HD3SLO3SPB2C02HB5Ha_st5Hl_st2s12s2S2ra2sp1C3kbsS2ra2sp1C3kbs2HBS2ra2sp1C3kbs2HBS2ra2sp1C3kbsS2ra2sp1C3kbsS2ra2sp1C3kbs2HBS2ra2sp1C3kbs2HBS2ra2sp1C3kbsS2ra2sp1C3kbsS2ra2sp1C3kbsS2ra2sp1C3kbsS1L3HLS2ra2sp1C3kbs2lo3SLO3SPB2C0S2ra2sp1C3kbsS2ra2sp1C3kbsS2ra2sp1C3kbs3SPB2HBS2ra2sp1C3kbs3SPB2HBS2ra2sp1C3KEY3kbs2K02KB3SPB2C0S2ra2sp1C3kbsS2ra2sp1C3kbs". (* [comment removed for export] *)
  Theorem U_rsa_parse_pubkey_spec : forall MSF, MSF = U_MEMSET_FUNC -> rsa_parse_pubkey_stmt usegs L HI U_RSA_PARSE_PUBKEY MSF.
  Proof.
    intros MSF HMSF. unfold rsa_parse_pubkey_stmt, U_RSA_PARSE_PUBKEY. intros until lo.
    intros HH RAT KY K0 KB CRK DKC DKS ST SLO ACL HTOP SPA DHI TP MI SOK CA RA -> -> ->. unfold RSA_CTX_SIZE in DKC.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR _.
    flat constr:(RAT) 13%nat. intros _ _ _ _ _ _ _ _ CAL C0 CB CIN _. unfold RSA_CTX_SIZE in CB, CIN.
    flat constr:((proj1 (Forall_forall _ _) HBR _ CIN)) 5%nat. intros _ _ _ CAC CND. cbn [fst snd] in CAC, CND.
    flat constr:(KY) 3%nat. intros _ KLEN _.
    pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    pose proof (conj HH I) as HH0. pose proof (conj RAT I) as RAT0. pose proof (conj KY I) as KY0. pose proof (conj SOK I) as SOK0. pose proof (conj ST I) as ST0. pose proof (conj MI I) as MI0.
    clear HH RAT SOK.
    carve_frame 48%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply fj8p in FR.
    zstep; if_cases KW0; zify_cond KW0; [exfalso; rewrite ?unsigned_lit in KW0 by lia; lia|].
    zstep. zstep. zstep. zstep. zstep; if_cases KN0; zify_cond KN0; [b2z_close KN0|].
    flat constr:(HH0) 2%nat. flclear HH0. intros HH _. flat constr:(RAT0) 2%nat. flclear RAT0. intros RAT _. flat constr:(KY0) 2%nat. flclear KY0. intros KY' _. flat constr:(SOK0) 2%nat. flclear SOK0. intros SOK _. flat constr:(ST0) 2%nat. flclear ST0. intros ST0 _. flat constr:(MI0) 2%nat. flclear MI0. intros MI0 _.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 KEY) + Z.of_nat (length kbs))) with (Z_to_bv 64 (KEY + Z.of_nat (length kbs))) by (rewrite unsigned_lit by lia; reflexivity).
    eapply seg_A; try eassumption; try reflexivity.
    1: { eapply pstate_init; eassumption. }
    all: reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MAIN.
