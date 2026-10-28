(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Image Asn1Aux Asn1AuxA X509Aux X509AuxB.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_asn1_sequence_free U_asn1_free_named_data_list_shallow U_asn1_get_sequence_of_A U_x509_get_name_A U_x509_parse_san_A U_x509_get_san_ext_A U_x509_get_san_ext.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPHeap. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums1.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P01b03cf5d6888ec8 0 5 0 1 3 1 5 1 30 1 36 1P026399fb03fcb032 0 5 0 1 20 1 28 1 31 1 32 1P034e617f267fa071 0 2 0 1 5 1P03d9f6abec2ec25b 0 4 0 1 18 1 31 1 32 1P041aeedb91894ecf 2 16 1 1 8 3 2 1 34 1 35 1 6 0 1 22 1 30 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 1 34 1 35 1 37 8P04a1ccaaa24fc044 0 5 0 1 20 1 28 1 31 1 32 1P0589494fb75ff539 0 3 0 1 33 1 34 1P06ecb0522871dec2 0 4 0 1 3 1 34 1 35 1P06f14ab4c198ba40 0 2 0 1 26 1P072217ab6b7a0573 2 14 0 6 0 1 3 1 23 1 31 1 34 1 35 1 0 4 0 1 2 1 34 1 35 1P073d9aa9137a31ed 0 2 0 1 5 1P0755231d461e2b8c 0 4 0 1 18 1 31 1 32 1P08c7e8d286bbac87 0 5 0 1 42 1 50 1 53 1 54 1P0a2b2444f19eb4a5 0 5 0 1 20 1 28 1 31 1 32 1P0b21ed4a34fa917c 0 4 0 1 2 1 35 1 36 1P0dd10dc03189c816 0 2 0 1 27 1P0e517d4a715bc683 1 1 8 3 1 1 33 1 36 1 4 2 2 34 2 35 2 37 16P0ec770e2d7ae4443 2 14 0 6 0 1 3 1 23 1 31 1 34 1 35 1 0 4 0 1 2 1 34 1 35 1P0f6fae3cdff5e318 0 2 0 1 4 1P0f92651e529fa8d1 0 2 0 1 1 1P1088023d9453534f 0 2 0 1 6 1P10fbfd8566db03b7 0 5 0 1 20 1 28 1 31 1 32 1P138f223122bfe17b 0 5 0 1 30 1 38 1 41 1 42 1P139e3706f1f87c41 0 5 0 1 27 1 35 1 38 1 39 1P13e7a14847a0add6 0 1 1 1P13ecbb8c7eff51ee 1 1 8 3 1 1 33 1 36 1 4 2 2 34 2 35 2 37 16P15740c8eacd2fc01 0 6 0 1 3 1 4 1 5 1 30 1 36 1P175fd3e28c7b8c9c 0 2 0 1 4 1P186c1210a031779a 1 1 8 3 0 1 34 1 35 1 6 2 2 22 2 30 2 33 2 36 2 37 16P18f7b104c0739892 1 1 8 3 1 1 34 1 35 1 4 2 2 33 2 36 2 37 16P1925f8b37c5184ed 0 5 0 1 42 1 50 1 53 1 54 1P19b2790881855016 0 5 0 1 42 1 50 1 53 1 54 1P1ad6873763771a92 0 3 0 1 33 1 34 1P1c5439873a5a4bb5 0 5 0 1 30 1 38 1 41 1 42 1P1e6237c9c2fa26a1 1 1 16 2 0 1 31 1 3 5 1 32 1 33 16P1f6244ca92eb9350 1 1 8 2 23 1 32 1 3 0 1 31 1 33 8P21e8fa1ecf47f017 0 5 0 1 30 1 38 1 41 1 42 1P2205f1ea60ef10ef 0 2 0 1 7 1P22116120be100046 0 2 0 1 1 1P2367aed9258d0e32 0 6 0 1 3 1 4 1 5 1 30 1 36 1P240e5d5eb4a3f7e0 0 4 0 1 18 1 31 1 32 1P2420a82e67d5c9df 0 5 0 1 27 1 35 1 38 1 39 1P27290ae978c7977c 0 2 0 1 5 1P286d38a49fe7914c 0 5 0 1 20 1 28 1 31 1 32 1P2a2dc89bf21e7086 0 2 0 1 21 1P2aa11b9976bc3679 0 4 0 1 18 1 31 1 32 1P2aa7087b99ccfb91 2 15 1 1 8 3 2 1 34 1 35 1 6 0 1 22 1 30 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 1 34 1 35 1 37 8P2cc0da3ef6f4e617 2 16 1 1 8 3 2 1 34 1 35 1 6 0 1 22 1 30 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 1 34 1 35 1 37 8P2ec5fa1ea6ff5406 1 1 8 3 0 1 34 1 35 1 6 2 2 22 2 30 2 33 2 36 2 37 16P2f87d7e43973d0de 1 1 8 3 0 1 34 1 35 1 6 2 2 22 2 30 2 33 2 36 2 37 16P2f93e6ad4e608d8e 2 14 0 6 0 1 3 1 23 1 31 1 34 1 35 1 0 4 0 1 2 1 34 1 35 1P2fc3992c162b21f4 0 6 1 1 2 1 22 1 30 1 33 1 34 1P30797ae5fbe18b4b 1 1 8 3 1 1 34 1 35 1 6 2 2 22 2 30 2 33 2 36 2 37 16P31086f70d7bfb0a1 2 15 1 1 8 3 2 1 34 1 35 1 6 0 1 22 1 30 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 1 34 1 35 1 37 8P31b4a5a87aa1c46c 0 4 0 1 4 1 33 1 34 1P3233fac1d5cf2a36 2 16 1 1 8 3 2 1 34 1 35 1 6 0 1 22 1 30 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 1 34 1 35 1 37 8P3292db73ddaa8e92 0 5 0 1 3 1 5 1 30 1 36 1P336d382eb0ec606c 0 2 0 1 24 1P33d3a8f638a10db9 0 2 0 1 25 1P3839778bc8eb32eb 2 14 0 6 0 1 3 1 23 1 31 1 34 1 35 1 0 4 0 1 2 1 34 1 35 1P3848ae2072ed8631 0 4 0 1 2 1 33 1 34 1P38de729c0d40b4d6 2 16 1 1 8 3 2 1 34 1 35 1 6 0 1 22 1 30 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 1 34 1 35 1 37 8P3917e9dde644de85 1 1 8 3 1 1 33 1 36 1 4 2 2 34 2 35 2 37 16P397bd30d315de58b 0 6 1 1 3 1 23 1 31 1 34 1 35 1P3ab3ce0445bcdf63 0 4 0 1 18 1 31 1 32 1P3d0598d2e9219eac 1 1 8 3 0 1 33 1 36 1 4 2 2 34 2 35 2 37 16P3d1fd32d1d059792 0 5 0 1 27 1 35 1 38 1 39 1P3d83901830bd0a37 0 4 0 1 4 1 33 1 34 1P3e034d7c6bd2f5fe 2 15 1 1 8 3 2 1 34 1 35 1 6 0 1 22 1 30 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 1 34 1 35 1 37 8P3f8d9b5e395a781c 2 15 1 1 8 3 2 1 34 1 35 1 6 0 1 22 1 30 1 33 1 36 1 37 8 1 1 8 3 1 1 33 1 36 1 4 0 1 34 1 35 1 37 8N0098f03589395c50N00c9da9315d8a56dN0366ace92664d3ffN04406f7d71ea0dcfN0587ae3850f953bcN0650f4bf96874479N06ec685d9175d38bN070b46e37eccfa3fN072845c7cf4403c3N079e13840815f3a3N086e8884f74b6658N089ec265ed8cb851N090b965239fb41a8N0a57aeb8086ee171N0aaf48b5c6d8fdd5N0b185ea1d8e65315N0c6defe7b9f93790N0e4e243a354ee12bN0ed55329f7c22f9dN0ede4e27b18f24f1N10f05925ce73dcdeN121143023d99faf1N122e29d542dcf747N1241415672115b66N12825fa7d51c3089N12a62be55abf9eb4N14c882087032ab1dN14f55127de918e36N15f0a6dae020ad96N1601530476f95342N1609a66cddc60254N16cd5b168dded06bN183ab2b0b9626c1bN1923b28189e8a291N1967e8eeeb1e83a8N198eb730a9af0677N199de41e8e502e37N19d267b54bda51b1N1d6e86ce56ec38a1N1edf26ff799c3118N1f967e4140bf2f71N20d99bef8ea0be3bN21317fadd759739eN2147406b993639d1N21c1299261087361N21c3da7eefbb3efbN231cae8f7523983dN237a5201276fc199N23f59600684b035fN24a78d0746494cc1N24a7b0a60b3898d1N24c33dc0dca86146N25f9184577662147N267be59fc1bc8bcaN267cee8f1ebd516eN26c90f88c022bbcdN275a341db9c5ac13N27be3fdb3473262aN29059ac2df8e9b89N292a667df8642a18N2969b8d49b88776aN2afa4a86a0805696N2b337cbb2d2becddN2b4041cc9a27f3deN2b505f4d021345c3N2bd89b1deffa06abN2c02cee265df56f0N2cfed34629c5bbc9N2d0dc560c9eaa827N2d8a31eab5647221N2dcab1a399fbfdedN2ddd09167fc5540aN2e95209316ffb41dN30571cf783fa6244N31d1fb0a26a115e5N320ba2d93a7e305dN331aaf49d2f80186N333e675053c786c2N3410dfb156e036b6N347f394698de7fa7N361258077b75c1deN3786ae93529de7e4N38607cfc5ea5f379N39a7f60cb52085a1N3a58811ab2258e24N3bec61d47aa6f739N3bf4f0aca86c52b9N3db600b9b69b7ea0"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_x509_get_san () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_san_ext_A.x509_get_san_ext_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_iface"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_calloc"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_name_A.U_CALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_free"; "RocqVerifyHarness.AgentSubmission.U.U_asn1_free_named_data_list_shallow.U_FREE"; "x509_get_san_stmt"; "U_X509_GET_SAN"].


Definition U_X509_GET_SAN : Z := 0x28df8.
Notation X509_GET_SAN_STACK := 528 (only parsing).

Definition x509_get_san_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pmo,$3.Ph,(4.O4.O3.O2.)PLB,(5.$6.)PPP,$7.PCUR,$7.PP,$7.PEND,$7.PBUF,$7.Plo,$7.Pbs,(5.(0.&8.))Pct,(0.&40.)Pcpad,(0.&40.)P,(8.O4.O3.O2.R;.R:.R=.R<.)P,(9.O4.R>.R:.(:.$;.(<.(=.&40.R8.))(>.$;.)))P,(9.O4.R?.R:.(?.R4.R3.===))P,(10.O4.R10.R8.R6.)P,(11.R9.R;.)P,(11.R<.R;.)P,(11.R<.(12.R;.(13.(14.(0.&8.)R9.))))P,(15.(12.R<.(13.(14.(0.&8.)R:.)))(16.+2.+3?.))P,(17.(11.(12.R11.+8.)R10.)(11.(12.R10.+20.)R11.))P,(17.(11.(12.R12.+8.)R>.)(11.(12.R>.(13.(14.(0.&8.)R<.)))R12.))P,(17.(11.(12.R12.+20.)R?.)(11.(12.R?.(13.(14.(0.&8.)R=.)))R12.))P,(18.$7.(19.R14.+8.)=)P,(18.$7.(19.R14.+8.)=)P,(15.=R16.)P,(15.=R16.)P,(15.=R14.)P,(1:.O4.R1=.R14.(1;.&40.R3=.))P,(11.R15.(1<.(1<.(1;.&40.R3>.)+210.)(1=.O3.)))P,(11.(1>.O3.)R16.)P,(11.(1;.&40.R40.)(1?.O4.O3.O2.R1>.))P,(18.$7.(19.(1;.&40.R41.)+10.)=)P,(11.(20.O3.)(1>.O3.))P,(11.(21.O3.)(22.O3.))P,(11.(20.O3.)(23.O3.))P,(17.(11.(12.R21.+8.)R1<.)(11.(1;.&40.R45.)R21.))P,(17.(11.(12.R21.+20.)R1=.)(11.(1;.&40.R46.)R21.))P,(17.(11.(12.R1?.(13.(14.(0.&8.)R1=.)))R1>.)(11.(1;.&40.R47.)R1?.))P,(24.O3.R25.R1?.(1?.O4.O3.O2.R26.)R24.+8.)P,(24.O3.R26.R20.(1?.O4.O3.O2.R27.)R24.+20.)P,(25.O3.R27.R21.R22.(13.(14.(0.&8.)R20.)))P,(18.(0.&40.)R49.(=.&40.(26.O3.)))P,(27.O4.R2<.)P,(18.(0.&40.)R45.(=.&40.R29.))P,(18.(0.&40.)R45.(=.&40.R27.))P,(18.(0.&40.)R45.(=.&40.R2:.))(28.O4.R2?.(29.O4.O3.O2.R51.R50.R4?.R4>.R4:.R49.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R32.R31.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R30.R2?.)(2:.(2;.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.)R32.(=.&40.O1.)R31.(2<.(0.&40.))R30.(2=.O4.)))")
(* [comment removed for export] *).

Section Walk.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HEXT : x509_get_san_ext_stmt usegs L HI U_X509_GET_SAN_EXT.
  Hypothesis HLS : 0 <= hl_stack L.

  (* [comment removed for export] *)
  Ltac epi0 r' p' HW sp lo m mo h :=
    zstep; zstep; zstep; zstep; zstep; zstep;
    lazymatch goal with
    | F0 : rw_cells _ ?mx (bv_unsigned sp + -48) _, FL : rw_cells _ ?mx (bv_unsigned sp + -40) _, FR2 : rw_cells _ ?mx (bv_unsigned sp + -32) _,
      ST' : stk _ ?mx lo _, MU : munch _ m ?mx, WM : wmono _ m ?mx |- _ =>
        let FRx := fresh "FRx" in let FRy := fresh "FRy" in let HHf := fresh "HHf" in let HPXf := fresh "HPXf" in
        chunk_join FL FR2 FRx; chunk_join F0 FRx FRy; release_frame FRy ST' (bv_unsigned sp);
        (flat constr:((HW _ MU WM)) 2%nat; intros HHf HPXf);
        apply aevtM_done; unfold x509_get_san_ext_post; flexi 15%nat;
        exists mx, mo, h, r', p'; eexists; eexists; exists 0, 0, 0, ([] : list Z);
        split; [reflexivity|];
        (flsplit; repeat match goal with |- _ /\ _ => split end); try assumption; try reflexivity;
        try apply mo_frame_refl; try eassumption; try (left; (flsplit; repeat split); reflexivity); try (intros xx [])
    end.

  (* [comment removed for export] *)
  #[local] Ltac lxp_is_protected H ::= lazymatch H with HEXT => idtac | HLS => idtac end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0@D14790846209.146D14792959895.172D14827235721.186D19552440442.187D20846730761.185D21483245952.186D23235990531.146D23685514265.146D2774177417.186 D3356939157.146 D3487245548.146 D45993506670.185D60941357161.146D62798430467.146D63527981802.146D808409667.146  L14726981937.148L17438901875.148L18994852257.0  L19037413286.110L19037413287.112L23235990531.141L26049370394.1  L30491076894.148L31378308326.91 L3356939157.141 L38346198145.148L43059266230.89 L45048480778.148L47571973569.112L49628314070.148L60941357161.141L61477003928.148L64029270448.112L64029270449.108L6566174622.150 L6566697626.115 L6566697627.112 L67917912743.148L68287240788.110L6952084072.1   L748424846.148  R23223785569.185R3369148407.187 R60945636363.18600001M02j03f03g04c04d04e05n06j06k08008108209L0:T0<50<60=<0==0>L0?[0@a0@f0Ah0B60C80EK0F20G?0H;0I70J90K;0K<0K=0LS0LT0LU0LV0M]0Ma0O@0PG0QJ0RMS1L3HLS2sp2PP3CUR2lo2bs3NZ13NZ23SLO3ACL3ACP3SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S1L3HLS2sp2PP3CUR2lo2bs3NZ13NZ23SLO3ACL3ACP3SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP3CUR2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4FS2sp2PP3CUR2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4FFS2sp2PP3CUR3END2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44lxv03H14S2sp2PP3CUR2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4FS1L2sp2PP3CUR2lo2bs3SLO1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4FFS2sp2PP3CUR1P3BUF2bs2B13NZ13NZ23SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44lxv03H13S1L2HI2sp1h2PP3CUR2bs4HTOP1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S1L3HLS2sp2PP3CUR2lo2bs3NZ13NZ23SLO3ACL3SPA3ACP3SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4FS2sp2PP3CUR3BUF2bs2D22D31j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4SS2sp2PP3CUR1P3END2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44lxv03H103H11S2sp2PP3CUR1P3END2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44lxv03H103H11S2sp2PP3CUR3BUF2lo2bs2HD1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S3CURS2sp2PP3CUR2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ41r3Hr6S2sp2PP3CUR2bsS2sp2PP3CUR2lo2bs2HD1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S1L3HLS2sp2PP3CUR1P3END3BUF2lo2bs2B12B32D12D22D33AL13AL23NZ13NZ23SLO3SPA3DS13DS23DS33SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44lxv03H133H14S1L3HLS2sp2PP3CUR2lo2bs3NZ13NZ23SLO3SPRS2sp2PP3CUR3END2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44lxv03x183Hp6S2sp2PP3CUR2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP3CUR2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP3CUR2lo2bs2HD1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP3CUR2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ41r3Hr6FFS1L2HI2sp1h2PP3CUR2bs3NZ13NZ23SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ42h63HT6FFFS2sp2PP3CUR2bs1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ43lxv2H53H13S2PPS2sp2PP3CUR1P3END2bs3NZ13NZ23SPR1j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ44lxv03H133x183Hp6S2sp2PP3CUR3BUF2lo2bs3DS31j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP3CUR2lo2bs3DS21j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4S2sp2PP3CUR2lo2bs3DS11j2j02j12j22j32j43LXJ4LXJ04LXJ14LXJ24LXJ34LXJ4". (* [comment removed for export] *)
  Lemma U_x509_get_san_walk : x509_get_san_stmt usegs L HI U_X509_GET_SAN.
  Proof.
  (* [comment removed for export] *)
  unfold x509_get_san_stmt, U_X509_GET_SAN.
  intros until cpad.
  intros HH HPP HCUR HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL HTOP SPA DHI DIM1 DIM2 DS1 DS2 DS3
    CWPP CWCUR CRBUF TP MI -> -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  try (unfold bv_modulus in SPR).
  try (cbn in SPR).
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  pose proof (rw_cells_bound _ _ _ _ HCUR) as CURB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ seq_cells] in PPB, CURB.
  change (Z.of_nat 8) with 8 in PPB.
  change (Z.of_nat 32) with 32 in CURB.
  pose proof (bytes_at_bound _ _ _ _ HBUF) as BB.
  flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR0 _.
  pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
  pose proof (conj HH I) as HHbox.
  try (unfold seq_cells in HCUR).
  pose proof (munch_refl [(PP, PP + 8); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 48%nat ST.
  lxp_split_frame [8;8;8;8;8;8]%nat.
  (* [comment removed for export] *)
  try (pose proof (heap_presx_refl usegs L LB (bv_unsigned sp) [(PP, PP + 8); (CUR, CUR + 32)] m) as HPX0).
  (* [comment removed for export] *)
  pose proof (@sums1_ok) as LXSUMS.
  lxp_run (PLANS [0x28790] [] 53%N SUMS1).
  { (* [comment removed for export] *)
    try (pose proof U_asn1_get_tag_spec as SP).
    (* [comment removed for export] *)
    try (lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end).
    try (match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lxp_gc. try lxp_statics.
    (* [comment removed for export] *)
    pose proof HEXT as SPE.
    try (unfold x509_get_san_ext_stmt, U_X509_GET_SAN_EXT in SPE).
    (* [comment removed for export] *)
    eapply aevtM_cut; [ eapply SPE with (PP := PP) (CUR := CUR) (END := END) (BUF := BUF) (bs := bs) (lo := lo) (LB := LB) (h := h);
      rewrite ?(unsigned_lit (bv_unsigned sp + -48)) by dlia; lxp_reg_refl; try eassumption; try reflexivity; try flia2 | ].
    try clear SPE.
    intros ms' mo' PO.
    try (unfold x509_get_san_ext_post in PO).
    destruct_exs PO.
    flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2.
    subst ms' mo'.
    try (rewrite ?(unsigned_lit (bv_unsigned sp + -48)) in PO by dlia).
    flat constr:(PO) 16%nat. flclear PO. intros MI6 ST6 MF6 HT6 Ha0 Hr6 HPP6 Hp6 HCUR6 HCB6 Hcn HCH6 HND6 HAP6 HH6 HPX6.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m6; rename mox into mo6 end.
    match type of HH6 with HEAP _ _ _ ?hh _ _ _ => rename hh into h6 end.
    match type of Ha0 with ?x = Z_to_bv 64 ?rr => subst x; rename rr into r end.
    pose proof (heap_mok _ _ HI _ _ _ _ HH6) as MK6.
    lxp_after_call.   (* [comment removed for export] *)
    try clear MK.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    try clear ST5. try clear MI5. try clear HPX5. try clear HPX6. try clear MU. try clear WM. try clear HBUF. try clear HPP. try clear HCUR. try clear HH5.
    lxp_gc.
    lxp_run (PLANS [0x28790] [] 53%N SUMS1).
    lxp_ret_open.   (* [comment removed for export] *)
    apply aevtM_done.
    unfold x509_get_san_ext_post.
    flexi 15%nat.
    all: lxp_ret_close.
  }
  { (* [comment removed for export] *)
    try (pose proof U_asn1_get_tag_spec as SP).
    (* [comment removed for export] *)
    try (lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end).
    try (match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    try (try replace (Z_to_bv 64 18446744073709542042) with (Z_to_bv 64 (-9574)) by (apply bv_eq; reflexivity)).
    lxp_ret.
  }
  { (* [comment removed for export] *)
    try (pose proof U_asn1_get_tag_spec as SP).
    (* [comment removed for export] *)
    try (lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end).
    try (match goal with H : ?x = Z_to_bv 64 ?rr |- _ => subst x; rename rr into r end).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    lxp_ret.
  }
  Unshelve. all: try lxp_default.   (* [comment removed for export] *)
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Lemma U_x509_get_san_spec : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_san ()) "PL,$2>.PHI,(2?.$30.R1.)P,(18.$7.(31.R2.)$32.)P,(18.$7.(33.R3.)$34.)P,(11.=(1=.R4.))(35.$30.R5.R4.$36.)")
(* [comment removed for export] *).
Proof.
  intros L HI HC HF HLS. apply U_x509_get_san_walk; [| exact HLS].
  apply U_x509_get_san_ext_spec; assumption.
Qed.
