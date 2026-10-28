(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string U_platform_zeroize U_mpi_free U_mpi_addsub U_mpi_grow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxExpr LxDec LxMem LxStep LxRun LxDenot LxSoundRun LxSum LxSoundSum LxTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00185497075d8c54 0 2 0 1 9 1P00ce19bf369a49d1 2 17 1 1 8 3 2 1 36 1 37 1 6 0 1 27 1 28 1 35 1 38 1 39 8 1 1 8 3 1 1 35 1 38 1 4 0 2 36 2 37 2 39 16P011da9e0f6f94aa2 0 2 0 1 10 1P01ea735e4eb26ab1 2 19 1 1 8 3 1 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P02173fb720d487b3 0 2 0 1 18 1P0246971bc1466296 2 17 1 1 8 3 2 1 36 1 37 1 6 0 1 27 1 28 1 35 1 38 1 39 8 1 1 8 3 1 1 35 1 38 1 4 0 2 36 2 37 2 39 16P0343929e3f802d7e 1 2 8 2 0 1 34 1 8 2 21 1 35 1 2 36 1 37 1P0411dfcc0b589e4b 1 1 64 9 0 16 10 16 18 16 19 16 20 16 24 16 30 16 33 16 34 16 2 9 1 35 1P05f8da740b634724 0 5 0 1 19 1 24 1 33 1 34 1P05fd93a965c03623 2 21 1 1 8 3 1 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P07e6336fdc207fe0 2 17 1 1 8 3 1 1 36 1 37 1 6 0 1 21 1 26 1 35 1 38 1 39 8 1 1 8 3 2 1 35 1 38 1 4 0 1 36 1 37 1 39 8P087abb3112a21d9a 0 2 0 1 1 1P093ed57860dbd46b 0 2 0 1 1 1P094db55dbd11fe61 0 2 0 1 18 1P09a9271ee7ba463e 0 2 0 1 9 1P0a0c1d423a432143 0 5 0 1 27 1 28 1 35 1 36 1P0a445b78ff1b39a7 2 24 1 1 8 3 1 1 41 1 42 1 6 0 1 32 1 33 1 40 1 43 1 44 8 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P0b6993af028dabb1 0 5 0 1 27 1 28 1 35 1 36 1P0f4d88b2f24c4a80 2 20 1 1 8 3 1 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P1058d45d5c491a87 0 2 0 1 18 1P1471a816baf42d3b 0 2 0 1 9 1P161e0a512741affc 0 5 0 1 30 1 31 1 38 1 39 1P1794d73100318c14 0 2 0 1 2 1P184615f1240c706c 2 20 1 1 8 3 1 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P190aa4cbaa839131 0 2 0 1 13 1P1acd21eed0a9ac15 1 1 8 2 21 1 35 1 3 0 1 34 1 36 8P1c85eb0ad1ddd70c 0 2 0 1 19 1P1f53b6c6f1d21ddf 0 2 0 1 9 1P1fd7ac68bffab82b 0 5 0 1 29 1 30 1 37 1 38 1P2222c4525b666f9e 0 7 0 1 11 1 14 4 17 1 25 1 26 1 27 1P24699718db71669c 0 3 0 1 1 1 15 1P2670e6834c07b275 2 23 1 1 8 3 1 1 41 1 42 1 6 0 1 32 1 33 1 40 1 43 1 44 8 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P270cdb030b7bec81 0 2 0 1 1 1P29d07762b3a8edc2 2 17 1 1 8 3 2 1 36 1 37 1 6 0 1 27 1 28 1 35 1 38 1 39 8 1 1 8 3 1 1 35 1 38 1 4 0 2 36 2 37 2 39 16P2a4a86ec7d753d60 0 2 0 1 8 1P2c5c8739f745ffa9 1 1 16 2 11 1 34 1 3 0 1 33 1 35 16P2c6372e5d7c7a9dd 0 2 0 1 18 1P2c6bd354db570b3d 0 2 0 1 9 1P2cefc2b2929b1be8 2 17 1 1 8 3 2 1 36 1 37 1 6 0 1 27 1 28 1 35 1 38 1 39 8 1 1 8 3 1 1 35 1 38 1 4 0 2 36 2 37 2 39 16P2dc629a6b6a355a2 2 24 1 1 8 3 1 1 41 1 42 1 6 0 1 32 1 33 1 40 1 43 1 44 8 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P2f4147e064e7fe3e 0 2 0 1 18 1P2f42e469aa8dae0a 0 7 0 1 11 1 14 4 17 1 25 1 26 1 27 1P2f578984ef6bdacd 0 4 0 8 2 8 34 8 35 8P2f57f1bc8084aa0d 2 17 1 1 8 3 1 1 36 1 37 1 6 0 1 21 1 26 1 35 1 38 1 39 8 1 1 8 3 2 1 35 1 38 1 4 0 1 36 1 37 1 39 8P30b783fed72b9213 0 2 0 1 14 1P3105d6a15d72f376 0 3 0 1 1 1 13 1P31c1d5233a26475f 0 2 0 1 15 1P3361d737809b2b91 2 23 1 1 8 3 1 1 41 1 42 1 6 0 1 32 1 33 1 40 1 43 1 44 8 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P3401e23865de7750 0 5 0 1 32 1 33 1 40 1 41 1P349101cf7f55781e 0 5 0 1 17 1 22 1 29 1 30 1P3552e5eaa675955b 2 19 1 1 8 3 1 1 38 1 39 1 6 0 1 29 1 30 1 37 1 40 1 41 8 1 1 8 3 2 1 37 1 40 1 4 0 2 38 2 39 2 41 16P35c8ebcdc2a85cf5 0 2 0 1 14 1P360480468e42c209 1 2 16 2 0 1 33 1 16 2 11 1 34 1 2 35 1 36 1P39c0934a0925bf84 0 2 0 1 8 1P3a04c6fd65035103 0 2 0 1 13 1P3f6e5ea918018eef 0 2 0 1 18 1N00bd406fd4aaa657N00f7bbc3d9a6b227N015fc65cfed5c9c2N016e430e81930bfbN02bf8e8c39da1f2bN03ecc5b52b245d67N03f26063f5b3456aN03f42a98e4d4eac3N055abe6089b026d7N0a2ecd5e32b44ad0N0bb3cfa625e89b8aN0ccaf81ae52a8f9fN0d3262619892b337N0e852dc3b3287736N0e9aa885d6cee0c8N10c5ac60d6c80c26N11afd18136fa925aN11ce80b1b47676ffN14ae0fa42f861962N14af8789ea2e4091N154446b22c1044dbN16796237fee607f3N1709e985f746ff7aN1829b330d863b63aN19f090fe4e308df2N19f7d75fe5550ff6N1dd52a4a19ef2122N1dd744e154db07c3N1e20f9318d6f8b54N1e8c8fe6300f5937N1eec3efaabdc72dfN1f0095c40b500df3N21c814d7902fd698N2332fd49750b9d92N23ee27dbb8f7c6b9N25356e26b42baa33N2602658439639a4dN28a581a9e0f5758aN2984a25140fe5831N29a40752f2401d0aN29da5ad6d079bab1N2a1b6c85b883b418N2a92937129633202N2a9d29470b87e9b1N2bb2291843f5eb95N2f69cc69941798f9N2fc552ae87dae57dN305a33268970cf85N31eb66acf3b6223bN324dc9f4cb2b0e3fN32c3b9ea8ba2ed57N337fa6e946ade422N33b51b147fe7f12bN34c28a91dd883af3N34dc002ce0ddcb67N356648f58601991eN37d535e800b03ac9N3957e6c4f779dd05N39f446d97be1c95dN3a71df5340539cc0N3d10c0b8c49ed739N3d4c5c640d4794f8N3d53de0a8b95b9e9N3e2eea988d4bea7dN3f70c37e7718821cN3f7df761d67b8269N3f857a7738526349"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_resize_clear () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.MBEDTLS_ERR_MPI_ALLOC_FAILED"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpd_writable"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "resize_clear_R"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_waddr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"].


Definition U_MPI_RESIZE_CLEAR : Z := 0x1fe38.
Definition U_MEMSET : Z := 0x46e44.

Notation MPI_RESIZE_CLEAR_STACK := 48 (only parsing).

Definition resize_clear_R (limbs : Z) (dX : mpd) (LB : list blk) (r : Z) (dX' : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_resize_clear ()) "(0.(1.(0.(2.$3.O2.=)(0.(2.$3.(4.O1.)+1.)(0.(2.$3.(5.O1.)O5.)(0.(2.(6.(7.&40.))(8.O1.)(9.(7.&40.)(:.&40.=)(;.O5.)))(<.(2.$3.O5.=)(2.$=.(>.O1.)$?.))))))(0.(2.$3.O2.$10.)(0.(2.$3.(4.O1.)+1.)(0.(2.$3.(5.O1.)=)(0.(2.(6.(7.&40.))(8.O1.)(11.(7.&40.)))(2.$=.(>.O1.)$?.))))))(0.(2.$3.(12.O1.)(12.O4.))Pb,$13.P,(14.$13.R1.(15.O1.))(1.(14.$13.R2.(15.O4.))(16.(14.$13.R2.O3.)))))")
(* [comment removed for export] *).

Definition mpi_resize_clear_stmt (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L) (ENTRY MSF : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_resize_clear ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Ps0,(7.&40.)Ps1,(7.&40.)Pa0,(7.&40.)Pa1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps4,(7.&40.)Ps5,(7.&40.)Ps6,(7.&40.)Ps7,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)PF,(17.&5.(7.&40.))Pfc,(7.&20.)Pm,P,(7.&40.)(18.(7.&8.))Pmo,$19.Ph,(1:.O5.O4.O3.)PLB,(6.$13.)PdX,$1;.Pnl,$3.Plo,$3.P,(1<.O5.O4.O3.R5.R4.R7.R6.)P,(1=.O5.R8.R5.(12.R4.)(:.&40.(4.R4.))(5.R4.)(1>.R4.)(8.R4.)(1?.R4.)(>.R4.))P,(16.(2.$=.(>.R5.)$20.))P,(21.O4.R7.(22.&40.R2:.)(23.O5.O4.O3.R8.)R6.)P,(0.(24.=R6.)(25.R6.(26.+2.+40.)))P,(27.O5.R<.R6.(22.&40.R2<.))P,(24.R7.(28.(28.(22.&40.R2=.)+30.)(29.O4.)))P,(24.(2:.O4.)R8.)P,(24.(22.&40.R2?.)(23.O5.O4.O3.R=.))P,(2.$3.(2;.(22.&40.R30.)+10.)=)P,(24.(2<.O4.)(2:.O4.))P,(2.(7.&40.)R30.(:.&40.(2=.O4.)))P,(2>.O5.R13.)P,(2?.O5.O4.R14.)P,(30.O4.O1.+8.)P,(2.(7.&40.)R2>.(:.&40.(12.R12.)))P,(2.(7.&40.)R2>.(:.&40.R12.))(31.O5.R17.(32.O5.O4.O3.R39.R38.R37.R36.R32.R31.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1:.R19.R16.R15.R14.(33.R13.R14.R15.)R12.R18.R17.)(34.(35.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R1:.(:.&40.O2.)R19.(36.(7.&40.))R18.(37.O5.)))")
(* [comment removed for export] *).
Section RC.
  Variable L : heap_layout.
  Variable HI : heap_iface usegs L.
  Hypothesis HFREE : hl_free L = U_FREE.
  Hypothesis HCALLOC : hl_calloc L = U_CALLOC.
  Hypothesis HLS : 0 <= hl_stack L.
  Hypothesis SW : forall a, hl_static L a -> hl_written L a.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP usegs L HI h LB m mo -> List.NoDup (map fst LB).

  (* [comment removed for export] *)
  Ltac flia := first [clear_disj; lia | lia].
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L12779162959.12L18926747689.12L18926759668.1200000:00;00@S1a1b1k2HkSS1a1b". (* [comment removed for export] *)
  Lemma zbv_mod64 : forall a b, (a - b) mod 18446744073709551616 = 0 -> (Z_to_bv 64 a : word) = Z_to_bv 64 b.
  Proof.
    intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    apply Z.mod_divide in H; [| lia]. flat constr:(H) 2%nat. flclear H. intros k Hk. replace a with (b + k * 18446744073709551616) by lia. apply Z.mod_add. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac fix_regs :=
    repeat match goal with |- context [Z_to_bv 64 (Zpos ?p)] =>
      let z := constr:(Zpos p) in
      lazymatch eval compute in (Z.leb (2^63) z) with
      | true => let z' := eval compute in (z - 2^64)%Z in replace (Z_to_bv 64 z : word) with (Z_to_bv 64 z' : word) by (apply zbv_mod64; reflexivity)
      end end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L54391995694.31L54398102733.3200000L00bS1L2HI2sp1h2lo4HTOP3SLO1a2HfS1L2HI2sp1h2lo3SLO1a1C". (* [comment removed for export] *)
  Lemma run_heap : ltac2:(CDefT.buildp (gd_tbl_P_mpi_resize_clear ()) "Psp,(7.&40.)Ph,(1:.$38.VL,VHI,)Phc,(1:.$38.VL,VHI,)PLBc,(6.$13.)Pmc,P,(7.&40.)(18.(7.&8.))Pm',P,(7.&40.)(18.(7.&8.))Pmoc,$19.PW,(6.$39.)PX,$3.Plo,$3.P,(1<.$38.VL,VHI,R8.R7.R6.R4.)P,(2.$3.(23.$38.VL,VHI,R9.)(23.$38.VL,VHI,R:.))P,(24.(22.&40.R<.)(23.$38.VL,VHI,R;.))P,(24.(2:.VL,)R4.)P,(24.R5.(28.(22.&40.R>.)+20.))P,Pa,$3.P,(0.(24.R8.R1.)(25.R1.(3:.R8.+10.)))(3;.VL,R>.(22.&40.R11.)(23.$38.VL,VHI,R10.)R2.)P,(3<.R9.R<.R;.)P,(3=.$38.R=.R<.)P,Pa,$3.P,(16.(3>.R<.R1.))(1.(0.(24.(28.(22.&40.R14.)+20.)R2.)(25.R2.(22.&40.R14.)))(0.(24.R<.R2.)(25.R2.(3:.R<.+10.))))(1<.$38.VL,VHI,R11.R10.R>.R=.)")
(* [comment removed for export] *).
  Proof.
    intros sp h hc LBc mc m' moc W X lo HH HT HTOP ACL SLO XCW MU WM WC.
    eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH| exact ACL| exact MU| exact WM|].
    intros a Ha NO. rewrite HT. destruct (WC a NO) as [Hf|Hx]; [left; lia|].
    destruct (XCW a Hx) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L59308562768.30L59308579027.32L59308585861.30L59308743383.3400000<00X00c01BS2dX1a2Hx2O1S1L2sp2lo3DHI3ACL3SLO1a1C2HfS2sp1a1C2HfS1L2sp2lo3ACL3SLO1a1B1k1R2Hf2B4". (* [comment removed for export] *)
  Lemma run_presx : ltac2:(CDefT.buildp (gd_tbl_P_mpi_resize_clear ()) "Psp,(7.&40.)PLB,(6.$13.)PdX,$1;.Pm,P,(7.&40.)(18.(7.&8.))Pmc,P,(7.&40.)(18.(7.&8.))Pm',P,(7.&40.)(18.(7.&8.))PW,(6.$39.)Plo,$3.P,(3?.$38.VL,R7.(22.&40.R8.)(40.R6.)R5.R4.)P,(41.(42.$3.$3.)Lb,(42.$3.$3.)(43.VL,(44.$3.$3.R1.)(45.$3.$3.R1.))R8.)P,(24.(2<.VL,)(2:.VL,))P,(24.(2:.VL,)R4.)P,(24.R5.(28.(22.&40.R<.)+20.))P,(3<.R7.R9.R8.)P,(3=.$38.R:.R9.)P,Pa,$3.P,(16.(3>.R:.R1.))(1.(0.(24.(28.(22.&40.R11.)+20.)R2.)(25.R2.(22.&40.R11.)))(0.(24.(12.R?.)R2.)(25.R2.(3:.(12.R?.)+10.))))(3?.$38.VL,R?.(22.&40.R10.)(40.R>.)R=.R;.)")
(* [comment removed for export] *).
  Proof.
    intros sp LB dX m mc m' W lo HPX HBR DHI ACL SLO MU WM WC.
    eapply heap_presx_trans; [exact HPX|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
    intros a Ha Hc Ho. destruct (outside_dec W a) as [O|NO]; [exact O| exfalso].
    destruct (WC a NO) as [Hf|Hx].
    - destruct Hc as [C|[C|([B k] & Hb & R)]]; [lia| destruct DIMG; lia| pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (_ & _ & _ & B4 & _); cbn in R, B4; lia].
    - cbn in Ho. flat constr:(Ho) 2%nat. flclear Ho. intros O1 _. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59308585861.2600000MS1L2sp2lo3DHI3ACL3SLO1a2Ha2Hf". (* [comment removed for export] *)
  Lemma run_statics : ltac2:(CDefT.buildp (gd_tbl_P_mpi_resize_clear ()) "Psp,(7.&40.)Pmc,P,(7.&40.)(18.(7.&8.))Pm',P,(7.&40.)(18.(7.&8.))PW,(6.$39.)PX,$3.Plo,$3.P,(2?.$38.VL,R5.)P,(24.(2<.VL,)(2:.VL,))P,(24.(2:.VL,)R3.)P,(24.R4.(28.(22.&40.R9.)+20.))P,Pa,$3.P,(0.(24.R7.R1.)(25.R1.(3:.R7.+10.)))P,(0.(24.(46.VL,)R2.)(25.R2.(2<.VL,)))(47.VL,R3.)P,(3<.R8.R:.R9.)P,Pa,$3.P,(16.(3>.R:.R1.))(1.(0.(24.(28.(22.&40.R>.)+20.)R2.)(25.R2.(22.&40.R>.)))(0.(24.R:.R2.)(25.R2.(3:.R:.+10.))))(2?.$38.VL,R;.)")
(* [comment removed for export] *).
  Proof.
    intros sp mc m' W X lo SOK DHI ACL SLO XD MU WC.
    eapply statics_ok_munch; [exact SOK| exact MU|]. intros a Ha NW. destruct (outside_dec W a) as [O|NO]; [exact O| exfalso].
    destruct (WC a NO) as [Hf|Hx]; [lia| exact (NW (XD a Hx Ha))].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L52516111147.78L56523165257.77000004008S2dXS2dX". (* [comment removed for export] *)
  Lemma L_EMPTY : ltac2:(CDefT.buildp (gd_tbl_P_mpi_resize_clear ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Ps0,(7.&40.)Ps1,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps4,(7.&40.)Ps5,(7.&40.)Ps6,(7.&40.)Ps7,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)PF,(17.&5.(7.&40.))Pfc,(7.&20.)Pm,P,(7.&40.)(18.(7.&8.))Pmo,$19.Ph,(1:.$38.VL,VHI,)PLB,(6.$13.)PdX,$1;.Pnl,$3.Plo,$3.Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Pa1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)Pmc,P,(7.&40.)(18.(7.&8.))Pm',P,(7.&40.)(18.(7.&8.))Pmoc,$19.Phc,(1:.$38.VL,VHI,)PLBc,(6.$13.)PW,(6.$39.)Ppad,(7.&40.)Pr,$3.P,(1<.$38.VL,VHI,R5.R4.R8.R6.)P,(2.$3.(23.$38.VL,VHI,R6.)(23.$38.VL,VHI,R1<.))P,(48.R1>.R8.)P,(2?.$38.VL,R;.)P,(3?.$38.VL,R1>.(22.&40.R32.)(40.R1=.)R21.R<.)P,Pa,$3.P,(0.(24.(12.R1?.)R1.)(25.R1.(3:.(12.R1?.)+10.)))(3;.VL,R;.(22.&40.R35.)(23.$38.VL,VHI,R22.)R2.)P,Pa,$3.P,(0.(24.(12.R20.)R1.)(25.R1.(3:.(12.R20.)+10.)))P,(0.(24.(46.VL,)R2.)(25.R2.(2<.VL,)))(47.VL,R3.)P,(24.(22.&40.R35.)(23.$38.VL,VHI,R22.))P,(24.(2:.VL,)R1?.)P,(24.R20.(28.(22.&40.R37.)+20.))P,(41.(42.$3.$3.)Lb,(42.$3.$3.)(43.VL,(44.$3.$3.R1.)(45.$3.$3.R1.))R24.)P,(24.(2<.VL,)(2:.VL,))P,(3<.R?.R14.R13.)P,(3=.$38.R15.R14.)P,Pa,$3.P,(16.(3>.R12.R1.))(1.(0.(24.(28.(22.&40.R3>.)+20.)R2.)(25.R2.(22.&40.R3>.)))(0.(24.(12.R29.)R2.)(25.R2.(3:.(12.R29.)+10.))))P,(2>.$38.R16.)P,(27.$38.R17.R27.(22.&40.R3>.))P,(49.$38.R18.(12.R2:.)(4:.$4;.(4<.(:.&40.=))(4:.$4;.(4=.(:.&40.+1.))(4:.$4;.(4=.R13.)(11.$4;.)))))P,(2.$3.(2;.(12.R2;.)+8.)=)P,(25.=(12.R2<.))P,(4>.R2>.R2=.R18.(4?.(12.R2=.)+1.==(11.(7.&40.))R16.$?.))P,(1.(0.(2.$3.R16.=)(2.$3.R2=.=))(2.$3.R16.$10.))(31.$38.R1<.(32.$38.VL,VHI,R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R31.R30.R2?.(33.R2>.R2?.R30.)R2=.R33.R32.)(34.(35.R45.R44.R43.R42.R2<.R2;.R2:.R41.R40.(:.&40.R17.)R29.R28.R27.R26.R25.R24.R23.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R22.R21.R20.R1?.)R35.(50.R45.)R34.(36.(7.&40.))R1=.(37.$38.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros HH HT MF SOK HPX XCW XD HTOP ACL SLO HBR DHI MU WM WC MI' ST' CH XAL X0 MO Hr.
    apply aevtM_done. unfold mpi_binop_post. flexi 14%nat. exists m', moc, hc, LBc, (mkMPD (md_addr dX) 1 0 0 [] pad LNull), r.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact MF|]. split; [exact HT|].
    split; [exact (run_heap sp h hc LBc mc m' moc W (md_addr dX) lo HH HT HTOP ACL SLO XCW MU WM WC)|].
    split. { split; [|left; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split. { pose proof (rw_cells_split_C4 usegs m' (md_addr dX) [C8 (Z_to_bv 64 0)] _ [C4 pad] CH) as CH'. cbn [app] in CH'.
               rewrite unsigned_lit in CH' by lia. exact CH'. }
      split; [exact XAL|]. split; [exact X0|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|]. split; reflexivity. }
    split; [exact MO|].
    split; [exact (run_presx sp LB dX m mc m' W lo HPX HBR DHI ACL SLO MU WM WC)|].
    split; [exact (run_statics sp mc m' W (md_addr dX) lo SOK DHI ACL SLO XD MU WC)|].
    unfold resize_clear_R; cbn [md_sg md_n md_limbs md_own md_addr mpd_blk md_p].
    split; [| split; [reflexivity| intros b []]].
    destruct Hr as [[-> ->] | ->]; [left; cbn; (flsplit; repeat split); auto; congruence| right; (flsplit; repeat split); reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L18740969513.81L34146086572.81L3636250620.81 L45231782292.81L59314873579.8200000<00H00W00f014S2dX2nl1A2NLS2dX2nl1A2NLS2dX2nl1A2X02NLS2dX2nl1A2X02NLS2dX2nl1A2NL1H". (* [comment removed for export] *)
  Lemma L_ZEROS : ltac2:(CDefT.buildp (gd_tbl_P_mpi_resize_clear ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Ps0,(7.&40.)Ps1,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps4,(7.&40.)Ps5,(7.&40.)Ps6,(7.&40.)Ps7,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)PF,(17.&5.(7.&40.))Pfc,(7.&20.)Pm,P,(7.&40.)(18.(7.&8.))Pmo,$19.Ph,(1:.$38.VL,VHI,)PLB,(6.$13.)PdX,$1;.Pnl,$3.Plo,$3.Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Pa1,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)Pmc,P,(7.&40.)(18.(7.&8.))Pm',P,(7.&40.)(18.(7.&8.))Pmoc,$19.Phc,(1:.$38.VL,VHI,)PLB',(6.$13.)PW,(6.$39.)Ppad,(7.&40.)PA,$3.Pzs,(6.(7.&8.))P,(1<.$38.VL,VHI,R6.R5.R9.R7.)P,(2.$3.(23.$38.VL,VHI,R7.)(23.$38.VL,VHI,R1=.))P,(48.R1?.R9.)P,(2?.$38.VL,R<.)P,(3?.$38.VL,R1?.(22.&40.R33.)(40.R1>.)R22.R=.)P,Pa,$3.P,(0.(24.(12.R20.)R1.)(25.R1.(3:.(12.R20.)+10.)))(3;.VL,R<.(22.&40.R36.)(23.$38.VL,VHI,R23.)R2.)P,Pa,$3.P,(0.(24.(12.R21.)R1.)(25.R1.(3:.(12.R21.)+10.)))P,(0.(24.(46.VL,)R2.)(25.R2.(2<.VL,)))(47.VL,R3.)P,(24.(22.&40.R36.)(23.$38.VL,VHI,R23.))P,(24.(2:.VL,)R20.)P,(24.R21.(28.(22.&40.R38.)+20.))P,(41.(42.$3.$3.)Lb,(42.$3.$3.)(43.VL,(44.$3.$3.R1.)(45.$3.$3.R1.))R25.)P,(24.(2<.VL,)(2:.VL,))P,(3<.R10.R15.R14.)P,(3=.$38.R16.R15.)P,Pa,$3.P,(16.(3>.R13.R1.))(1.(0.(24.(28.(22.&40.R3?.)+20.)R2.)(25.R2.(22.&40.R3?.)))(0.(24.(12.R2:.)R2.)(25.R2.(3:.(12.R2:.)+10.))))P,(2>.$38.R17.)P,(27.$38.R18.R28.(22.&40.R3?.))P,(49.$38.R19.(12.R2;.)(4:.$4;.(4<.(:.&40.R13.))(4:.$4;.(51.(:.&40.+1.))(4:.$4;.(51.(:.&40.R2:.))(4:.$4;.(4=.R14.)(11.$4;.))))))P,(2.$3.(2;.(12.R2<.)+8.)=)P,(25.=(12.R2=.))P,(49.$38.R1<.R16.(4:.$4;.(52.(;.(53.+4.R2=.))R15.)(11.$4;.)))P,(2.(6.(7.&8.))R16.(9.(7.&8.)(:.&8.=)(;.(53.+4.R2>.))))P,(0.(24.+1.R2?.)(24.R2?.+2710.))P,(14.(42.$3.$3.)(54.$3.$3.R19.(53.+4.R30.))R1<.)P,(2.$3.(2;.R1:.+10.)=)P,(4>.R34.R33.R1>.(4?.(12.R33.)+1.R32.R1;.(9.(7.&40.)(:.&40.=)(;.R32.))R1<.$55.))P,(1.(14.(42.$3.$3.)(54.$3.$3.R1<.(53.+4.R33.))(15.R34.))(16.(14.(42.$3.$3.)(54.$3.$3.R1<.(53.+4.R33.))R35.)))(31.$38.R22.(32.$38.VL,VHI,R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R37.R36.R35.(33.R34.R35.R36.)R33.R39.R38.)(34.(35.R4;.R4:.R49.R48.R32.R31.R30.R47.R46.(:.&40.=)R2?.R2>.R2=.R2<.R2;.R2:.R29.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R28.R27.R26.R25.)R3;.(50.R4;.)R3:.(36.(7.&40.))R23.(37.$38.)))")
(* [comment removed for export] *).
  Proof.
    intros until zs. intros HH HT MF SOK HPX XCW XD HTOP ACL SLO HBR DHI MU WM WC MI' ST' CH XAL X0 HZ -> NL AIN A16 MO AFR.
    apply aevtM_done. unfold mpi_binop_post. flexi 14%nat.
    exists m', moc, hc, LB', (mkMPD (md_addr dX) 1 nl A (repeat (Z_to_bv 64 0) (Z.to_nat nl)) pad LHeap), 0.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact MF|]. split; [exact HT|].
    split; [exact (run_heap sp h hc LB' mc m' moc W (md_addr dX) lo HH HT HTOP ACL SLO XCW MU WM WC)|].
    split. { split; [|left; reflexivity]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact CH|]. split; [exact XAL|]. split; [exact X0|]. split; [rewrite repeat_length; lia|]. split; [unfold MPI_MAX_LIMBS; lia|].
      split; [lia|]. split; [exact AIN|]. split; [exact A16|].
      eapply u32arr_of_cells; [exact HZ|]. rewrite u32s_repeat0. f_equal. lia. }
    split; [exact MO|].
    split; [exact (run_presx sp LB dX m mc m' W lo HPX HBR DHI ACL SLO MU WM WC)|].
    split; [exact (run_statics sp mc m' W (md_addr dX) lo SOK DHI ACL SLO XD MU WC)|].
    unfold resize_clear_R; cbn [md_sg md_n md_limbs md_own md_addr mpd_blk md_p].
    split; [left; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [intros; exfalso; lia| discriminate]|].
    split; [reflexivity|]. intros b [<-|[]]. exact AFR.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00M0@L12012090472.124L12047647016.124L29638086697.110L29638089019.113L29644522319.111L33947267987.108L35172967071.86 L38242068361.86 L39409830041.110L39409930731.122L40823250123.86 L41560719952.124L41564767562.110L49340251976.124L51209633155.119L51209633155.122L51912986396.115L52516111152.116L53251943872.86 L53516691675.86 L55554145250.126L59308530391.88 L59308579027.121L59314873579.122L59315317366.118L63238479518.122L65500066615.115L7190686615.104 L7193109011.86  00000V00a00l01601J01P01\01k02602C02I02l03J03U03V04Q05:05B05Q06?06Q06b07d08`09T09d09l0:N0;0S1L3HLS2sp1X2nl2lo3ACL3SLO2X03ACP1A2A0S2sp1X2nl1AS2sp1X1a2HaS2sp1X1a1CS1L2HI2sp1h1X1a2Ha1CS2sp1XS2sp1X2nl2NLS2sp1X2nl2X02NLS2sp1X1a2HaS2sp1X1A1a2NOS2sp1XS1L3HLS2sp1X2lo3ACL3SLO2X03ACP1A2A0S1L3HLS2sp1X2lo3ACL3SLO2X03ACPS2sp1X2nl1AFS1L3HLS2sp1X2nl2lo3ACL3SLO3SPA3XAL2X02NL3ACP1A2A03A162A42XAS1L3HLS2sp1X2nl2lo3ACL3SLO2X02NL3ACP1A2A0S2sp1X1AS1L2sp1X2lo3SLOS1L2HI3HLS2sp1h1X2lo2hc2HT4HTOP3ACL3SLO2X03ACPS2sp1X2nl1A1B1k2H4S2sp1X1n1P1a1R2HoS1L3HLS2sp1X2nl2lo3ACL3SLO3SPA3DHI2X03ACP1A2A02A42A51a2Ha1C1D1H2H0S1L3HLS2sp1X2nl2lo3ACL3SLO3SPA2X03ACP1A2A02A41a2Ha1C1B1k1R1HS1L2HI3HLS2sp1h1X2nl2lo3ACL3SLO2X03ACP1A2A02A41a1C1SS1L2sp1X2nl1A2A4S2sp1X1AS1L3HLS2sp1X2lo3ACL3SLO3SPB2X03ACPS1L3HLS2sp1X2lo3ACL3SLO3SPB2X03ACP". (* [comment removed for export] *)
  Lemma L_CALLOC : ltac2:(CDefT.buildp (gd_tbl_P_mpi_resize_clear ()) "Pra,(7.&40.)Psp,(7.&40.)Pgp,(7.&40.)Ptp,(7.&40.)Ps0,(7.&40.)Ps1,(7.&40.)Ps2,(7.&40.)Ps3,(7.&40.)Ps4,(7.&40.)Ps5,(7.&40.)Ps6,(7.&40.)Ps7,(7.&40.)Ps8,(7.&40.)Ps9,(7.&40.)Ps10,(7.&40.)Ps11,(7.&40.)PF,(17.&5.(7.&40.))Pfc,(7.&20.)Pm,P,(7.&40.)(18.(7.&8.))Pmo,$19.Ph,(1:.$38.VL,VHI,)PLB,(6.$13.)PdX,$1;.Pnl,$3.Plo,$3.Pt0,(7.&40.)Pt1,(7.&40.)Pt2,(7.&40.)Pa2,(7.&40.)Pa3,(7.&40.)Pa4,(7.&40.)Pa5,(7.&40.)Pa6,(7.&40.)Pa7,(7.&40.)Pt3,(7.&40.)Pt4,(7.&40.)Pt5,(7.&40.)Pt6,(7.&40.)Pmc,P,(7.&40.)(18.(7.&8.))Pmoc,$19.Phc,(1:.$38.VL,VHI,)PLBc,(6.$13.)Ppad,(7.&40.)P,(1<.$38.VL,VHI,R3.R2.R5.R4.)P,(2.$3.(23.$38.VL,VHI,R4.)(23.$38.VL,VHI,R18.))P,(48.R1:.R6.)P,(2?.$38.VL,R8.)P,(3?.$38.VL,R1:.(22.&40.R2>.)(40.R19.)R1=.R9.)P,Pa,$3.P,(0.(24.(12.R1;.)R1.)(25.R1.(3:.(12.R1;.)+10.)))(3;.VL,R9.(22.&40.R31.)(23.$38.VL,VHI,R1>.)R2.)P,Pa,$3.P,(0.(24.(12.R1<.)R1.)(25.R1.(3:.(12.R1<.)+10.)))P,(0.(24.(46.VL,)R2.)(25.R2.(2<.VL,)))(47.VL,R3.)P,(24.(22.&40.R31.)(23.$38.VL,VHI,R1>.))P,(24.(2:.VL,)R1;.)P,(24.R1<.(28.(28.(22.&40.R33.)+30.)(29.VL,)))P,(2.$3.(2;.(22.&40.R34.)+10.)=)P,(25.(22.&40.R35.)(26.+2.+40.))P,(2.(7.&40.)R34.(:.&40.(2=.VL,)))P,(41.(42.$3.$3.)Lb,(42.$3.$3.)(43.VL,(44.$3.$3.R1.)(45.$3.$3.R1.))R23.)P,(24.(2<.VL,)(2:.VL,))P,(2>.$38.R14.)P,(27.$38.R15.R23.(3:.(22.&40.R3:.)-20.))P,(49.$38.R16.(3:.(22.&40.R3;.)-20.)(4:.$4;.(4<.R36.)(4:.$4;.(4<.R37.)(4:.$4;.(4<.R38.)(4:.$4;.(4<.R3<.)(11.$4;.))))))P,(49.$38.R17.(12.R27.)(4:.$4;.(4<.(:.&40.=))(4:.$4;.(4=.(:.&40.+1.))(4:.$4;.(4=.R13.)(11.$4;.)))))P,(2.$3.(2;.(12.R28.)+8.)=)P,(25.=(12.R29.))P,(24.(3:.(12.R2:.)+10.)(26.+2.+40.))P,(1.(24.(3:.(12.R2;.)+10.)R29.)(24.(22.&40.R40.)(12.R2;.)))P,(0.(24.+1.R2;.)(24.R2;.+2710.))P,(4>.R2>.R2=.R1:.(4?.(12.R2=.)+1.==(11.(7.&40.))R19.$?.))P,PA,$3.P,PB,$3.Pk,$3.P,(14.(42.$3.$3.)(54.$3.$3.R2.R1.)R1>.)(1.(24.(3:.R4.(53.+4.R31.))R3.)(24.(3:.R3.R2.)R4.))P,(25.=R2.)P,(24.(3:.R3.(53.+4.R30.))(2:.VL,))(0.(4>.R33.R32.(4:.(42.$3.$3.)(54.$3.$3.R4.(53.+4.R31.))R1?.)(4?.(12.R32.)+1.R31.R4.(9.(7.&40.)(:.&40.=)(;.R31.))R1>.$55.))(1.(14.(42.$3.$3.)(54.$3.$3.R4.(53.+4.R31.))(15.R32.))(16.(14.(42.$3.$3.)(54.$3.$3.R4.(53.+4.R31.))R33.))))(31.$38.R1>.(32.$38.VL,VHI,R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R31.R30.R2?.(33.R2>.R2?.R30.)R2=.R33.R32.)(34.(35.(:.&40.+1?>?4.)(:.&40.(3:.(22.&40.R44.)-20.))R43.R42.R2<.R2;.R2:.(:.&40.(12.R2?.))(:.&40.R2>.)(:.&40.R2>.)(:.&40.+4.)R29.R28.R27.R26.R25.R24.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R23.R22.R21.R20.)R35.(:.&40.+3?960.)R34.(36.(7.&40.))R1?.(37.$38.)))")
(* [comment removed for export] *).
  Proof.
    intros until pad. destruct dX as [X sg n P limbs pad0 own]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
    intros HH HT MF SOK HPX XCW XD HTOP ACL SLO SPA SPB TP HBR DHI MI ST FR CH XAL X0 X16 XS NL MO0 MOA.
    pose proof alloc_ceiling_pos as ACP. pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK.
    assert (LBS : forall b a, In b LB -> fst b <= a < fst b + snd b -> outside (mpd_ivs (mkMPD X sg n P limbs pad0 own)) a -> In b LBc).
    { intros [B k] a Hb R Ho. flat constr:(MO0) 5%nat. flclear MO0. intros _ _ _ M4 _. apply (M4 _ Hb). cbn [mpd_blk md_own md_p md_n].
      destruct own; [intros []| | intros []]. intros [E|[]]. injection E as <- <-. cbn in Ho, R. lia. }
    replace (Z_to_bv 64 0x3f960) with (Z_to_bv 64 (hl_calloc L)) by (rewrite HCALLOC; reflexivity).
    eapply aevtM_cut; [ eapply (heap_calloc usegs L HI) with (cnt := nl) (sz := 4) (lo := lo);
      rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia; try eassumption; try reflexivity; try lia | ].
    intros ms' mo' PO. unfold call_post in PO. destruct_exs PO. flat constr:(PO) 2%nat. flclear PO. intros E PO.
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
    destruct_ands PO.
    lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    lazymatch goal with |- aevtM _ ?mox _ (MS _ _ _ _ _ ?mx _) => rename mx into m7; rename mox into mo7 end.
    match goal with H : heap_pres _ _ _ _ mc m7 |- _ => rename H into HPc end.
    match goal with H : stk _ m7 _ _ |- _ => rename H into ST7 end.
    match goal with H : mem_inv _ m7 |- _ => rename H into MI7 end.
    match goal with H : mo_frame moc mo7 |- _ => rename H into MF7 end.
    apply (heap_pres_rw_cells usegs L _ _ mc m7 _ _ HPc) in FR; [| cbn [cells_size csize Nat.add]; intros a Ha; left; lia ].
    apply (heap_pres_rw_cells usegs L _ _ mc m7 _ _ HPc) in CH; [| cbn [cells_size csize Nat.add]; intros a Ha;
         destruct (XCW a ltac:(lia)) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C] ].
    assert (SOK7 : statics_ok usegs L m7) by (eapply statics_ok_heap_pres; [exact SOK| exact HPc| exact SW]).
    assert (HPX7 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg n P limbs pad0 own)) m m7).
    { eapply heap_presx_trans; [exact HPX|]. intros a Ha Hc Ho. apply HPc; [exact Ha|].
      destruct Hc as [C|[C|(b & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists b; split; [exact (LBS b a Hb R Ho)| exact R]]. }
    clear HH SOK HPX HPc MK ST MI.
    destruct PO as (h7 & HT7 & [[-> HH7] | (A & -> & HBA & HH7 & HNEW)]); pose proof (heap_mok _ _ HI _ _ _ _ HH7) as MK7.
    { (* [comment removed for export] *)
      rewrite TP. apply (lxp_aevtM_of_evt usegs mo7 _ _ MK7).
      lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
      all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
      all: lazymatch goal with E : @eq mem ?mx ?mc0 |- _ => subst mx end.
      lazymatch goal with Hm : munch _ m7 m7, Hw : wmono _ m7 m7 |- _ =>
        eapply (L_EMPTY ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB (mkMPD X sg n P limbs pad0 own) nl lo
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 m7 mo7 h7 LBc _ pad);
        [exact HH7| rewrite HT7; exact HT| eapply mo_frame_trans; [exact MF| exact MF7]| exact SOK7| exact HPX7| exact XCW| exact XD
        | exact HTOP| exact ACL| lia| exact HBR| exact DHI| exact Hm| exact Hw| intros a NO; exfalso; exact (NO I)
        | assumption| assumption| exact CH| exact XAL| exact X0| exact MO0| right; reflexivity] end. }
    (* [comment removed for export] *)
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH7)) 2%nat. intros HBR7 HAP7.
    pose proof HBA as HBA'. flat constr:(HBA') 5%nat. flclear HBA'. intros A0 A16 _ A4 A5. flat constr:(HAP7) 2%nat. flclear HAP7. intros HAPA _.
    assert (XA' : forall a, X <= a < X + 16 -> ~ (A <= a < A + nl * 4)).
    { intros a Ha C. destruct (XCW a Ha) as [S|[[D NS]|([B k] & Hb & R)]]; [lia| destruct DIMG; lia| pose proof (HAPA B k Hb); cbn in R; lia]. }
    pose proof (pointwise_apart X 16 A (nl * 4) ltac:(lia) ltac:(lia) XA') as XA. clear XA'.
    (* [comment removed for export] *)
    pose proof (rw_cells_split_C4 usegs m7 X [C8 (Z_to_bv 64 0)] _ [C4 pad] CH) as CH2; cbn [app] in CH2; rewrite unsigned_lit in CH2 by lia; cbn in CH2; clear CH.
    lazymatch type of HNEW with ?T => change (lx_hidden T) in HNEW end.
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo7 _ _ MK7).
    lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs; unfold lx_hidden in HNEW.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    lazymatch goal with Hm : munch ?W m7 m9, Hw : wmono _ m7 m9, Hc : rw_cells _ m9 X _ |- _ =>
      apply (rw_cells_transport usegs W m7 m9) in HNEW; [| exact Hm| exact Hw| cbn; flia];
      destruct (MOA A ltac:(intros B k Hb; pose proof (HAPA B k Hb); lia) A0 ltac:(lia)) as [MO9 AFR];
      eapply (L_ZEROS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo h LB (mkMPD X sg n P limbs pad0 own) nl lo
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7 m9 mo7 h7 ((A, nl * 4) :: LBc) W pad A);
      [exact HH7| rewrite HT7; exact HT| eapply mo_frame_trans; [exact MF| exact MF7]| exact SOK7| exact HPX7
      | intros a Ha; destruct (XCW a Ha) as [C|[C|([B k] & Hb & R)]]; [left; exact C| right; left; exact C| right; right; exists (B, k); split; [right; exact Hb|exact R]]
      | exact XD| exact HTOP| exact ACL| lia| exact HBR| exact DHI| exact Hm| exact Hw| intros a NO; cbn in NO |- *; right; flia
      | assumption| assumption| exact Hc| exact XAL| exact X0
      | replace (4 * nl) with (nl * 4) by lia; exact HNEW| f_equal; lia| exact NL| left; f_equal; lia| exact A16
      | replace (nl * 4) with (4 * nl) by lia; exact MO9| exact AFR] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01Y0@L10104690546.105L10108887159.118L10108887159.121L10110901746.104L11668620365.100L11670653879.102L13313426870.123L14704351223.97 L16628975680.83 L1943863265.79  L22700267513.120L23266343037.96 L23266724191.129L23431794531.119L25920922575.95 L25920922688.99 L25920922817.99 L26106920326.83 L29300996232.102L29300996232.103L29300996232.104L29300996232.105L29300996232.106L29300996232.120L29300996232.127L29300996232.131L29300996232.94 L29300996232.98 L29638047992.125L29638086697.125L29638086697.126L29644522319.126L29644522319.127L29768015777.118L34290115814.85 L34303729078.122L38231715032.97 L38231715032.98 L38447825886.97 L38447825886.98 L39409830041.125L39409830041.126L41558346840.92 L41558346840.96 L41558489716.118L41558489845.125L41558490490.129L41560573297.101L41560573297.103L41560655089.100L41560655857.102L41570977777.102L41570977777.104L43055153712.83 L43418819142.123L43418819142.124L43783956694.129L43784083956.96 L45288670583.97 L45288670583.98 L45374583978.96 L45374965128.129L48695681152.97 L48695681152.98 L50716086261.119L51796838330.119L53518944813.100L54299285.97    L54299285.98    L55239977583.123L55239977583.124L55799931056.126L55799931056.127L56560440097.0  L59308562897.128L59308562897.129L59308579797.104L59308579930.95 L59308579930.96 L59308664813.96 L59308977657.102L59308977657.103L59308977657.98 L59314873579.129L59315300849.127L59315300849.128L64638675.102   L65502163868.81 L65803042429.119L6624980440.124 L6624980440.127 L66797865.100   L68238445262.102L68244655752.97 L68244655752.98 L7186886453.97  L7186886453.98  L7190686615.116 L7190686615.117 L772750287.81   L874674126.92   L874791394.96   L8895070966.126 L8895070966.129 R22706564033.12200000g00h01m02d03Z04P04a05;05V05k06D06\07607N07k08H08e09F09\0:20:H0:^0;40;J0;`0<60<J0<^0=30=I0=_0>>0>]0?60?E0?V0@00@J0@g0AD0AZ0B00BS0C60C^0DF0Dn0EV0F>0Ff0GN0H60H^0IA0J40Jg0K<0KO0LC0M70MF0MW0MX0MY0NL0O70OH0Ok0PN0Pd0Q:0QV0R20R30RM0Rg0SK0S]0So0TA0TX0To0UF0VN0WK0XH0Xk0Y:0YP0YQ0ZU0[80[\0\@0\d0]T0^D0_40_d0`G0`_0a70a80b50b`S1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X03LEN2XB2P04PRNGFS1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB3XAL2X03LEN2XP2XB3PAL2P04PRNG2H4S1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X03LEN2XB2P04PRNGS1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2P04PRNG2H4S1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2P04PRNG2H4S2sp1X1P5limbs2XBS2sp1X1n5limbs2nl2XB2H22H3S1L2sp1X1n1P5limbs2XB2P02P4S1L2sp1X5limbs3ACP2XBS2sp1X1n1P5limbs2XB3x141HS2sp1X2nl2XB5LXKT02H22H5S2sp1X1P5limbs2nl2XB2H42H5S2sp1X1n1P5limbs2XB1a2NOS1L2sp1X1n1P5limbs2XB4PRNG2H1S1L2sp1X1n1P5limbs2XB4PRNG2H3S1L2sp1X1n1P5limbs2XB4PRNG2H2S2sp1X1n1b5limbs3SPB2X03LEN2XB2N0S2sp1X1P5limbs2XB1a2NOS2sp1X1P5limbs2XB1a2NOS2sp1X1P5limbs2XB1a2NOS2sp1X1P5limbs2XB1a2NOS2sp1X1P5limbs2XB1a2NOS2sp1X1P5limbs2XB1a2NOS2sp1X1P5limbs2XB1a2NOS2sp1X1P5limbs2XB1a2NOS2sp1X2XB5LXKT01a2NOS2sp1X2XB5LXKT01a2NOS2sp1X1P5limbs2XB1a1CS2sp1X1P5limbs2XB1a2HaS2sp1X1P5limbs2XB1a2HaS1L2HI2sp1h1X1P5limbs2XB1a2Ha1CS1L2HI2sp1h1X1P5limbs2XB1a2Ha1CS2sp1X1n1P5limbs2NR2XB2N1S2sp1X5limbs2XBS2sp1X1P5limbs2XBS1L2sp1X1P5limbs2lo3SLO2XBS1L2sp1X1P5limbs2lo3SLO2XBS1L2HI2sp1h1X1P5limbs4HTOP2XBS1L2HI2sp1h1X1P5limbs4HTOP2XBS2sp1X1P5limbs2XB1a2HaS2sp1X1P5limbs2XB1a2HaS1L3HLS2sp1X2lo3SLO3SPB2X02XB5LXKT0S1L3HLS2sp1X2lo3SLO3SPB2X02XB5LXKT0S1L3HLS2sp1X1P5limbs2lo3SLO3SPB2X02XB2P0S1L3HLS2sp1X1P5limbs2lo3SLO3SPB2X02XB2P0S1L3HLS2sp1X1P5limbs2lo3SLO3SPB2X02XB2P0S1L3HLS2sp1X1P5limbs2lo3SLO3SPB2X02XB2P0S1L3HLS2sp1X1P5limbs2lo3SLO3SPB2X02XB2P0S1L3HLS2sp1X1P5limbs2lo3SLO3SPB2X02XB2P0S1L3HLS2sp1X1P5limbs2lo3SLO3SPB2X02XB2P0S1L3HLS2sp1X1P5limbs2lo3SLO3SPB2X02XB2P0S1L3HLS2sp1X1P5limbs2lo3SLO3SPB2X02XB2P0S1L3HLS2sp1X5limbs2lo3SLO3SPB2X02XBS1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2P04PRNGS1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2P04PRNGS2sp1X1P5limbs3SPB2XBS2sp1X3SPB2XB5LXKT0S1L3HLS2sp1X1P5limbs2lo3SLO3ACL3SPA3ACP3SPB2X02XB2P0S1L3HLS2sp1X1P5limbs2lo3SLO3ACL3SPA3ACP3SPB2X02XB2P0S2sp1X2XB5LXKT0S2sp1X1P5limbs2XBFFS1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XB2P04PRNGS1L2sp1X1n1P5limbs2lo3ACL3SPB2X02XB2P04PRNGS2sp1X1P5limbs2XBS2sp1X1n1P5limbs3SPB2X02NR2XB2N12P0S2sp1X1n1P5limbs3SPB2X02NR2XB2N12P0S2sp1X1n1P5limbs2XP2XBS2sp1X1n1P5limbs2XP2XBS1L2HI2sp1h1X1P5limbs2XB1a1CS1L2HI2sp1h1X1P5limbs2XB1a1CSS2sp1X1n1P5limbs2XB1a1R2O2S2sp1X1n1P5limbs2XB1a1R2O2S2sp1X2nl2NB3SPB2X02XB5LXKT02H51A2H6S2sp1X5limbs2XB2H4S2sp1X5limbs2XB2H2S2sp1X5limbs2XB2H2S2sp1X1P5limbs2XB2P02H2S2sp1X1P5limbs2XB2P02H3S2sp1X1P5limbs2XB2P02H1S1L3HLS2sp1X1n1P5limbs2nl2lo3SLO3ACL3SPB2X02XB2N12P04PRNG2H41A3A4'3NAP1HS1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XP2XB2P04PRNG1a2Ha1RS1L3HLS2sp1X1n1P5limbs2lo3SLO3ACL3SPB2X02XP2XB2P04PRNG1a2Ha1RS2sp1X1n1P5limbs3SPB2X02NR2XB2P02H4S2sp1X5limbs2XBS2sp1X1n1P5limbs2XP2XBFS1L3HLS2sp1X2sg1n1P5limbs3pad2nl2lo3SLO3ACL3SPB2X02XB2P02H32H41A3A4'S2sp1X1n1P5limbs3SPB2X02NR2XB2P02H4S2sp1X1n1P5limbs3SPB2X03LEN2XB2P02H4S2sp1X1n1P5limbs3SPB2X03LEN2XB2N12P0S2sp1X1n1P5limbs3SPB2X03LEN2XB2N12P0S1L3HLS2sp1X1P5limbs2lo3SLO3ACL3ACP3SPB2X02XB2P0S1L3HLS2sp1X1P5limbs2lo3SLO3ACL3ACP3SPB2X02XB2P0S1L3HLS2sp1X1P5limbs2lo3SLO3ACL3ACP3SPB2X02XB2P0S1L3HLS2sp1X1P5limbs2lo3SLO3ACL3ACP3SPB2X02XB2P0S1L3HLS2sp1X5limbs2lo3SLO3SPB2X02XBS2sp1X2nl2NB2XB5LXKT02H2S2sp1X5limbs2nl2NB2XB2H3FS1L3HLS2sp1X1n1P5limbs2nl2lo3SLO3ACL3SPB2X02XB2P02H32H41A3A4'S1L4DIMG2sp1X1n1P5limbs3SPB2X02XB2P02P51a1H". (* [comment removed for export] *)
  Lemma U_mpi_resize_clear_spec : mpi_resize_clear_stmt usegs L HI U_MPI_RESIZE_CLEAR U_MEMSET_FUNC.
  Proof.
    unfold mpi_resize_clear_stmt, U_MPI_RESIZE_CLEAR. intros until lo. intros HH MA NST XW NB ST SLO ACL HTOP SPA DHI TP MI SOK CA -> ->.
    pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK. pose proof alloc_ceiling_pos as ACP.
    pose proof (bv_unsigned_in_range 64 sp) as SPB. change (bv_modulus 64) with (2^64) in SPB.
    flat constr:((heap_blocks _ _ HI _ _ _ _ HH)) 2%nat. intros HBR HAP. pose proof (HND _ _ _ _ HH) as ND.
    destruct dX as [X sg n P limbs pad own].
    flat constr:(MA) 6%nat. flclear MA. intros CH XAL X0 LEN NR OWN. unfold mpi_cells in CH.
    flat constr:(XW) 3%nat. flclear XW. intros XCW XD XP. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
    unfold MPI_MAX_LIMBS in NR. pose proof (rw_cells_bound _ _ _ _ CH) as XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (client_wrange_where L _ _ _ X 16 lo XCW ltac:(lia) HBR DHI ACL ltac:(lia)) as XS.
    (* [comment removed for export] *)
    assert (OWF : (own = LNull /\ P = 0 /\ n = 0 /\ limbs = []) \/ (own = LHeap /\ 1 <= n /\ In (P, 4 * n) LB /\ P mod 16 = 0 /\ u32arr usegs m P limbs /\ 0 < P /\ P + 4 * n <= alloc_ceiling)).
    { destruct own as [| |]; [left| right| exfalso; exact (NST eq_refl)].
      - flat constr:(OWN) 2%nat. flclear OWN. intros P0 N0. split; [reflexivity|]. split; [exact P0|]. split; [exact N0|]. destruct limbs; [reflexivity| cbn in LEN; lia].
      - flat constr:(OWN) 4%nat. flclear OWN. intros N1 PIN PAL PCH. flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros P0 _ _ P4 P5. cbn in P0, P4, P5.
        split; [reflexivity|]. split; [exact N1|]. split; [exact PIN|]. split; [exact PAL|]. split; [exact PCH|]. split; [exact P0| exact P4]. }
    clear OWN.
    assert (PRNG : 0 <= P /\ P + 4 * n <= alloc_ceiling) by (destruct OWF as [(_ & -> & -> & _)|(_ & _ & _ & _ & _ & P0 & P4)]; lia).
    carve_frame 32%nat ST.
    assert (HPX0 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg n P limbs pad own)) m m) by apply heap_presx_refl.
    (* [comment removed for export] *)
    assert (LXSUMS : forall AL, Forall (summary_okG usegs AL []) (@nil summary)) by (intros AL; constructor).
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK).
    lx_run_tac (PLANS [0x25a0c; 0x46e44; 0x3f960] [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
    all: lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
         lazymatch goal with Hm : munch ?W ?mA mx, Hw : wmono _ ?mA' mx |- _ => rename Hm into MU1; rename Hw into WM1; rename mx into m1 end end.
    (* [comment removed for export] *)
    1: { assert (PZ : P = 0) by flia. destruct OWF as [(-> & -> & -> & ->)|(_ & _ & _ & _ & _ & P0 & _)]; [| exfalso; lia].
         lazymatch goal with Hc : rw_cells _ m1 X _ |- _ =>
         eapply L_EMPTY; [exact HH| reflexivity| apply mo_frame_refl| exact SOK| exact HPX0| exact XCW| exact XD| exact HTOP| exact ACL| flia| exact HBR| exact DHI
           | exact MU1| exact WM1| intros a NO; cbn in NO |- *; flia| assumption| assumption| exact Hc| exact XAL| exact X0
           | apply mpd_out_same_blocks; cbn; [reflexivity| discriminate| reflexivity]| left; split; [reflexivity| flia]] end. }
    (* [comment removed for export] *)
    2: { assert (PZ : P = 0) by flia. destruct OWF as [(-> & -> & -> & ->)|(_ & _ & _ & _ & _ & P0 & _)]; [| exfalso; lia].
         lazymatch goal with Hc : rw_cells _ m1 X _ |- _ =>
         eapply L_EMPTY; [exact HH| reflexivity| apply mo_frame_refl| exact SOK| exact HPX0| exact XCW| exact XD| exact HTOP| exact ACL| flia| exact HBR| exact DHI
           | exact MU1| exact WM1| intros a NO; cbn in NO |- *; flia| assumption| assumption| exact Hc| exact XAL| exact X0
           | apply mpd_out_same_blocks; cbn; [reflexivity| discriminate| reflexivity]| right; reflexivity] end. }
    (* [comment removed for export] *)
    2: { assert (PZ : P = 0) by flia. destruct OWF as [(-> & -> & -> & ->)|(_ & _ & _ & _ & _ & P0 & _)]; [| exfalso; lia].
         lazymatch goal with Hc : rw_cells _ m1 X _, Hf : rw_cells _ m1 (bv_unsigned sp + -32) _ |- _ =>
         eapply L_CALLOC;
         [ exact (run_heap sp h h LB m m1 mo _ X lo HH eq_refl HTOP ACL ltac:(flia) XCW MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia))
         | reflexivity| apply mo_frame_refl
         | exact (run_statics sp m m1 _ X lo SOK DHI ACL ltac:(flia) XD MU1 ltac:(intros a NO; cbn in NO |- *; flia))
         | exact (run_presx sp LB _ m m m1 _ lo HPX0 HBR DHI ACL ltac:(flia) MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia))
         | exact XCW| exact XD| exact HTOP| exact ACL| exact SLO| exact SPA| flia| exact TP| exact HBR| exact DHI
         | assumption| assumption| exact Hf| exact Hc| exact XAL| exact X0| cbn [md_addr]; flia| exact XS| flia
         | apply mpd_out_same_blocks; cbn; [reflexivity| discriminate| reflexivity]
         | intros A HAPA' A0 A4; split;
           [ cbn [md_addr md_own mpd_blk md_p md_n]; split; [reflexivity|]; split; [discriminate|];
             split; [intros b [<-|Hb]; [right; left; reflexivity| left; exact Hb]|]; split; [intros b Hb Hn; right; exact Hb| intros b []]
           | right; intros Hin; pose proof (HAPA' A (4 * nl) Hin); lia ] ] end. }
    (* [comment removed for export] *)
    3: {
    assert (EN : nl = n) by flia. subst nl.
    destruct OWF as [(_ & _ & -> & _)|(-> & N1 & PIN & PAL & PCH & P0 & P4)]; [exfalso; flia|]. specialize (XP eq_refl).
    flat constr:((proj1 (Forall_forall _ _) HBR _ PIN)) 5%nat. intros _ _ _ _ P5. cbn in P5.
    lazymatch goal with Hc : rw_cells _ m1 X _, Hf : rw_cells _ m1 (bv_unsigned sp + -32) _, Hs : stk _ m1 _ _, Hi : mem_inv _ m1 |- _ =>
      rename Hc into CH1; rename Hf into FR1; rename Hs into ST1; rename Hi into MI1 end.
    pose proof (run_heap sp h h LB m m1 mo _ X lo HH eq_refl HTOP ACL ltac:(flia) XCW MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia)) as HH1.
    pose proof (run_statics sp m m1 _ X lo SOK DHI ACL ltac:(flia) XD MU1 ltac:(intros a NO; cbn in NO |- *; flia)) as SOK1.
    pose proof (run_presx sp LB _ m m m1 _ lo HPX0 HBR DHI ACL ltac:(flia) MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia)) as HPX1.
    pose proof (heap_mok _ _ HI _ _ _ _ HH1) as MK1.
    lazymatch type of MU1 with munch ?W _ _ => apply (u32arr_transport usegs W m m1) in PCH; [| exact MU1| exact WM1| cbn; flia] end.
    clear ST MI CH FR MK MU1 WM1 HPX0.
    pose proof (munch_refl [(P, P + 4 * n)] m1) as MU. pose proof (wmono_refl usegs m1) as WM.
    (* [comment removed for export] *)
    apply u32arr_cells in PCH.
    pose proof U_memset_spec as SPs. unfold memset_stmt in SPs.
    eapply aevtM_cut_evt; [ exact MK1 | eapply SPs; rewrite ?unsigned_lit by lia; [ replace (Z.to_nat (4 * n)) with (4 * length limbs)%nat by lia; exact PCH | assumption ] | ].
    clear SPs PCH. unfold memset_post. rewrite !unsigned_lit by lia. post_call usegs m1.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    match goal with H : rw_cells usegs m2 P _ |- _ => rename H into PZ end.
    assert (HH2 : HEAP usegs L HI h LB m2 mo).
    { eapply (Asn1AuxA.HEAP_munch usegs L HI) with (SP := lo); [exact HH1| exact ACL| exact MU| exact WM|].
      intros a Ha NO. cbn in NO. right; right. exists (P, 4 * n). split; [exact PIN| cbn; lia]. }
    assert (HPX2 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg n P limbs pad LHeap)) m m2).
    { eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. cbn in Ho |- *. flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _. split; [exact O2| exact I]. }
    clear HH1 HPX1 MU WM. pose proof (heap_mok _ _ HI _ _ _ _ HH2) as MK2.
    lazymatch type of PZ with ?T => change (lx_hidden T) in PZ end.
    (* [comment removed for export] *)
    rewrite TP. apply (lxp_aevtM_of_evt usegs mo _ _ MK2).
    lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
    all: apply evt_done; cbv beta; rewrite <- TP; fix_regs; unfold lx_hidden in PZ.
    lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with Hm : munch ?W m2 mx, Hw : wmono _ m2 mx, Hc : rw_cells _ mx X _ |- _ =>
      apply (rw_cells_transport usegs W m2 mx) in PZ; [| exact Hm| exact Hw| cbn; flia];
      eapply L_ZEROS; [exact HH2| reflexivity| apply mo_frame_refl| exact SOK1| exact HPX2| exact XCW| exact XD| exact HTOP| exact ACL| flia| exact HBR| exact DHI
        | exact Hm| exact Hw| intros a NO; cbn in NO |- *; flia| assumption| assumption| exact Hc| exact XAL| exact X0
        | exact PZ| cbn; reflexivity| cbn [md_n]; flia| exact PIN| exact PAL
        | apply mpd_out_same_blocks; cbn; [reflexivity| discriminate| reflexivity]| left; left; reflexivity]
    end end.
    }
    (* [comment removed for export] *)
    1: {
      assert (EN : nl = 0) by flia.
      destruct OWF as [(_ & -> & _ & _)|(-> & N1 & PIN & PAL & PCH & P0 & P4)]; [exfalso; flia|]. specialize (XP eq_refl).
      pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK1.
      lazymatch goal with Hc : rw_cells _ m1 X _, Hf : rw_cells _ m1 (bv_unsigned sp + -32) _, Hs : stk _ m1 _ _, Hi : mem_inv _ m1 |- _ =>
        rename Hc into CH1; rename Hf into FR1; rename Hs into ST1; rename Hi into MI1 end.
      pose proof (run_heap sp h h LB m m1 mo _ X lo HH eq_refl HTOP ACL ltac:(flia) XCW MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia)) as HH1.
      pose proof (run_statics sp m m1 _ X lo SOK DHI ACL ltac:(flia) XD MU1 ltac:(intros a NO; cbn in NO |- *; flia)) as SOK1.
      pose proof (run_presx sp LB _ m m m1 _ lo HPX0 HBR DHI ACL ltac:(flia) MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia)) as HPX1.
      lazymatch type of MU1 with munch ?W _ _ => apply (u32arr_transport usegs W m m1) in PCH; [| exact MU1| exact WM1| cbn; flia] end.
      clear ST MI CH FR MK MU1 WM1 HPX0 HH SOK.
      (* [comment removed for export] *)
      apply u32arr_cells in PCH.
      eapply aevtM_cut.
      { eapply (U_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := P) (len := 4 * n) (lo := lo) (junk := u32s limbs);
          rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia; try eassumption; try reflexivity; try lia.
        right. split; [exact PIN|]. replace (Z.to_nat (4 * n)) with (4 * length limbs)%nat by lia. exact PCH. }
      cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
      flat constr:(PO) 20%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m4 mo4 h4 E PO. injection E as -> ->.
      rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
      flat constr:(PO) 7%nat. flclear PO. intros MI4 ST4 MF4 HT4 HH4 PX4 SOK4.
      lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      pose proof (HND _ _ _ _ HH4) as ND4.
      apply (heap_presx_rw_cells usegs L _ _ _ m1 m4 _ _ PX4) in FR1; [| cbn [cells_size csize Nat.add]; intros a Ha; left; lia | cbn; split; [lia| exact I] ].
      apply (heap_presx_rw_cells usegs L _ _ _ m1 m4 _ _ PX4) in CH1;
        [| cbn [cells_size csize Nat.add]; intros a Ha;
           destruct (XCW a ltac:(lia)) as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists (B, k); split; [|exact R]];
           apply (in_lb_remove_other LB P (4 * n) B k ND PIN Hb); intros E; injection E as -> ->; cbn in R; lia
         | cbn; split; [lia| exact I] ].
      clear PCH.
      assert (HPX4 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg n P limbs pad LHeap)) m m4).
      { eapply heap_presx_trans; [exact HPX1|]. intros a Ha Hc Ho. cbn in Ho. flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _.
        apply PX4; [exact Ha| | cbn; split; [exact O2| exact I]].
        destruct Hc as [C|[C|([B k] & Hb & R)]]; [left; first [clear_disj; lia | lia]| right; left; exact C| right; right; exists (B, k); split; [|exact R]].
        apply (in_lb_remove_other LB P (4 * n) B k ND PIN Hb). intros E; injection E as -> ->; cbn in R; lia. }
      assert (XCW4 : forall a, X <= a < X + 16 -> client_waddr L (lb_remove P LB) (bv_unsigned sp) (heap_top usegs L HI h) a).
      { intros a Ha. destruct (XCW a Ha) as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists (B, k); split; [|exact R]].
        apply (in_lb_remove_other LB P (4 * n) B k ND PIN Hb). intros E; injection E as -> ->; cbn in R; lia. }
      assert (MO4 : mpd_out LB (mkMPD X sg n P limbs pad LHeap) (lb_remove P LB) (mkMPD X 1 0 0 [] pad LNull)).
      { cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
        split. { intros b Hb. left. eapply In_lb_remove. exact Hb. }
        split. { intros [B k] Hb Hn. apply (in_lb_remove_other LB P (4 * n) B k ND PIN Hb). intros E. apply Hn. left. symmetry. exact E. }
        intros b [<-|[]] Hin. exfalso. exact (lb_remove_notin LB P (4 * n) ND Hin). }
      clear PX4 HPX1 HH1 SOK1 MK1. pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
      rewrite TP. apply (lxp_aevtM_of_evt usegs mo4 _ _ MK4).
      lx_run_tac (PLANS (@nil Z) [] 40%N (@nil summary)); lx_tree.
      all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
      lazymatch goal with |- aevtM _ _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch goal with Hm : munch ?W m4 mx, Hw : wmono _ m4 mx, Hc : rw_cells _ mx X _ |- _ =>
        eapply L_EMPTY; [exact HH4| exact HT4| exact MF4| exact SOK4| exact HPX4| exact XCW4| exact XD| exact HTOP| exact ACL| flia| exact HBR| exact DHI
          | exact Hm| exact Hw| intros a NO; cbn in NO |- *; flia| assumption| assumption| exact Hc| exact XAL| exact X0
          | exact MO4| left; split; [reflexivity| exact EN]]
      end end. }
    (* [comment removed for export] *)
    1: {
      destruct OWF as [(_ & -> & _ & _)|(-> & N1 & PIN & PAL & PCH & P0 & P4)]; [exfalso; flia|]. specialize (XP eq_refl).
      pose proof (heap_mok _ _ HI _ _ _ _ HH) as MK1.
      lazymatch goal with Hc : rw_cells _ m1 X _, Hf : rw_cells _ m1 (bv_unsigned sp + -32) _, Hs : stk _ m1 _ _, Hi : mem_inv _ m1 |- _ =>
        rename Hc into CH1; rename Hf into FR1; rename Hs into ST1; rename Hi into MI1 end.
      pose proof (run_heap sp h h LB m m1 mo _ X lo HH eq_refl HTOP ACL ltac:(flia) XCW MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia)) as HH1.
      pose proof (run_statics sp m m1 _ X lo SOK DHI ACL ltac:(flia) XD MU1 ltac:(intros a NO; cbn in NO |- *; flia)) as SOK1.
      pose proof (run_presx sp LB _ m m m1 _ lo HPX0 HBR DHI ACL ltac:(flia) MU1 WM1 ltac:(intros a NO; cbn in NO |- *; flia)) as HPX1.
      lazymatch type of MU1 with munch ?W _ _ => apply (u32arr_transport usegs W m m1) in PCH; [| exact MU1| exact WM1| cbn; flia] end.
      clear ST MI CH FR MK MU1 WM1 HPX0 HH SOK.
      (* [comment removed for export] *)
      apply u32arr_cells in PCH.
      eapply aevtM_cut.
      { eapply (U_zeroize_and_free_spec L HI HFREE HLS SW DIMG) with (buf := P) (len := 4 * n) (lo := lo) (junk := u32s limbs);
          rewrite ?(unsigned_lit (bv_unsigned sp + -32)) by lia; try eassumption; try reflexivity; try lia.
        right. split; [exact PIN|]. replace (Z.to_nat (4 * n)) with (4 * length limbs)%nat by lia. exact PCH. }
      cbv beta. intros ms' mo' PO. unfold zeroize_and_free_post in PO.
      flat constr:(PO) 20%nat. flclear PO. intros y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m4 mo4 h4 E PO. injection E as -> ->.
      rewrite ?(unsigned_lit (bv_unsigned sp + -32)) in PO by lia.
      flat constr:(PO) 7%nat. flclear PO. intros MI4 ST4 MF4 HT4 HH4 PX4 SOK4.
      lazymatch goal with |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?x)) _ _ _ _) =>
        replace (ret_pc (Z_to_bv 64 x)) with (Z_to_bv 64 x) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
      pose proof (HND _ _ _ _ HH4) as ND4.
      apply (heap_presx_rw_cells usegs L _ _ _ m1 m4 _ _ PX4) in FR1; [| cbn [cells_size csize Nat.add]; intros a Ha; left; lia | cbn; split; [lia| exact I] ].
      apply (heap_presx_rw_cells usegs L _ _ _ m1 m4 _ _ PX4) in CH1;
        [| cbn [cells_size csize Nat.add]; intros a Ha;
           destruct (XCW a ltac:(lia)) as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists (B, k); split; [|exact R]];
           apply (in_lb_remove_other LB P (4 * n) B k ND PIN Hb); intros E; injection E as -> ->; cbn in R; lia
         | cbn; split; [lia| exact I] ].
      clear PCH.
      assert (HPX4 : heap_presx usegs L LB (bv_unsigned sp) (mpd_ivs (mkMPD X sg n P limbs pad LHeap)) m m4).
      { eapply heap_presx_trans; [exact HPX1|]. intros a Ha Hc Ho. cbn in Ho. flat constr:(Ho) 3%nat. flclear Ho. intros O1 O2 _.
        apply PX4; [exact Ha| | cbn; split; [exact O2| exact I]].
        destruct Hc as [C|[C|([B k] & Hb & R)]]; [left; first [clear_disj; lia | lia]| right; left; exact C| right; right; exists (B, k); split; [|exact R]].
        apply (in_lb_remove_other LB P (4 * n) B k ND PIN Hb). intros E; injection E as -> ->; cbn in R; lia. }
      assert (XCW4 : forall a, X <= a < X + 16 -> client_waddr L (lb_remove P LB) (bv_unsigned sp) (heap_top usegs L HI h) a).
      { intros a Ha. destruct (XCW a Ha) as [C|[C|([B k] & Hb & R)]]; [left; lia| right; left; exact C| right; right; exists (B, k); split; [|exact R]].
        apply (in_lb_remove_other LB P (4 * n) B k ND PIN Hb). intros E; injection E as -> ->; cbn in R; lia. }
      assert (MO4 : mpd_out LB (mkMPD X sg n P limbs pad LHeap) (lb_remove P LB) (mkMPD X 1 0 0 [] pad LNull)).
      { cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
        split. { intros b Hb. left. eapply In_lb_remove. exact Hb. }
        split. { intros [B k] Hb Hn. apply (in_lb_remove_other LB P (4 * n) B k ND PIN Hb). intros E. apply Hn. left. symmetry. exact E. }
        intros b [<-|[]] Hin. exfalso. exact (lb_remove_notin LB P (4 * n) ND Hin). }
      clear PX4 HPX1 HH1 SOK1 MK1. pose proof (heap_mok _ _ HI _ _ _ _ HH4) as MK4.
      assert (MOA : forall A, (forall B k, In (B, k) (lb_remove P LB) -> A + 4 * nl <= B \/ B + k <= A) -> 0 < A -> A + 4 * nl <= alloc_ceiling ->
         mpd_out LB (mkMPD X sg n P limbs pad LHeap) ((A, 4 * nl) :: lb_remove P LB) (mkMPD X 1 nl A (repeat (Z_to_bv 64 0) (Z.to_nat nl)) pad LHeap)
         /\ (In (A, 4 * nl) (mpd_blk (mkMPD X sg n P limbs pad LHeap)) \/ ~ In (A, 4 * nl) LB)).
      { intros A HAPA' A0' A4'. split.
        - cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
          split. { intros b [<-|Hb]; [right; left; reflexivity| left; eapply In_lb_remove; exact Hb]. }
          split. { intros [B k] Hb Hn. right. apply (in_lb_remove_other LB P (4 * n) B k ND PIN Hb). intros E. apply Hn. left. symmetry. exact E. }
          intros b [<-|[]] [E|Hin]; [injection E; flia| exfalso; exact (lb_remove_notin LB P (4 * n) ND Hin)].
        - cbn [mpd_blk md_own md_p md_n]. right. intros Hin. destruct (Z.eq_dec A P) as [EAP|NAP].
          + exact (nodup_fst_neq LB P (4 * n) A (4 * nl) ND PIN Hin ltac:(intros E; injection E; flia) EAP).
          + pose proof (HAPA' A (4 * nl) (In_lb_remove_keep P (4 * nl) A LB Hin NAP)). lia. }
      rewrite TP. apply (lxp_aevtM_of_evt usegs mo4 _ _ MK4).
      lx_run_tac (PLANS [0x3f960] [] 40%N (@nil summary)); lx_tree.
      all: apply evt_done; cbv beta; rewrite <- TP; fix_regs.
      all: lazymatch goal with |- aevtM _ _ _ (MS _ _ ?pc _ _ ?mx _) =>
           lazymatch goal with Hm : munch ?W ?mq mx, Hw : wmono _ ?mq' mx, Hc : rw_cells _ mx _ [C8 _; C4 _; C4 _] |- _ =>
           lazymatch pc with
           | ret_pc _ =>
             eapply L_EMPTY; [exact HH4| exact HT4| exact MF4| exact SOK4| exact HPX4| exact XCW4| exact XD| exact HTOP| exact ACL| flia| exact HBR| exact DHI
               | exact Hm| exact Hw| intros a NO; cbn in NO |- *; flia| assumption| assumption| exact Hc| exact XAL| exact X0
               | exact MO4| right; reflexivity]
           | _ =>
             lazymatch goal with Hf : rw_cells _ mx _ [C8 _; C8 _; C8 _; C8 _] |- _ =>
             eapply L_CALLOC;
             [ exact (run_heap sp h h4 (lb_remove P LB) m4 mx mo4 _ X lo HH4 HT4 HTOP ACL ltac:(flia) XCW4 Hm Hw ltac:(intros a NO; cbn in NO |- *; flia))
             | exact HT4| exact MF4
             | exact (run_statics sp m4 mx _ X lo SOK4 DHI ACL ltac:(flia) XD Hm ltac:(intros a NO; cbn in NO |- *; flia))
             | exact (run_presx sp LB _ m m4 mx _ lo HPX4 HBR DHI ACL ltac:(flia) Hm Hw ltac:(intros a NO; cbn in NO |- *; flia))
             | exact XCW4| exact XD| exact HTOP| exact ACL| exact SLO| exact SPA| flia| exact TP| exact HBR| exact DHI
             | assumption| assumption| exact Hf| exact Hc| exact XAL| exact X0| cbn [md_addr]; flia| exact XS| flia
             | exact MO4| exact MOA ] end
           end end end. }
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End RC.
