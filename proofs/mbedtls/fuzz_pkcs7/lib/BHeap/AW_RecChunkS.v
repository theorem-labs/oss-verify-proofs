(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Madvise.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AJ AKinvS AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_MmapFixedNR AW_Munmap AW_Poison AW_Populate.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Dealloc AW_QPut AW_CbRecycle AW_CbRecycleS AW_LargeFree AW_MunmapCfg AW_PoisonBig AW_PoisonBigCfg AW_LargeFreeCfg
     AW_CfgDefs AW_RecChunk HMLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AW_RecChunkS () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_SPACEBEG_CELL"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.dealloc_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PoisonBig.rsmr_statics"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Lists.ListDef.map"; "Stdlib.ZArith.BinInt.Z.add"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.map_has"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.page_round_up_Z"; "Corelib.Init.Datatypes.true"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_LargeFree.rmp_PB"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_LargeFree.rmp_PE"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.madvise_dontneed_ok"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.madvise_model"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_GSTATS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_SEC_MUTEX"; "Stdlib.ZArith.BinInt.Z.mul"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "ARUN_1.RecChunkS.rs_W"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MunmapCfg.wmono_out"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "ARUN_1.rs_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_LargeFree.sec_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.upd"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Lists.ListDef.repeat"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.hdr_w0"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.hdr_rest"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Peano.lt"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "ARUN_1.RecChunkS.rs_post"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CbRecycle.A_CB_RECYCLE"].

Section ARUN_1. Context {hAR : arun}.
Definition rs_statics (m : mem) (SB CTX T : Z) (can : word) (dd madv : byte) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_RecChunkS ()) "(0.(1.$2.O7.$3.(4.$5.(6.(7.&40.O6.))(8.$5.)))(0.(9.O7.O4.O5.)(0.(:.O7.)(;.O7.O3.O2.O1.))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma u64x16_splitS : ltac2:(CDefT.buildp (gd_tbl_AW_RecChunkS ()) "Pm,P,(<.&40.)(=.(<.&8.))PA,$>.Pxs,(?.(<.&40.))P,(10.$2.R3.R2.R1.)P,(11.$12.(13.(<.&40.)R2.)#10.)(14.(<.&40.)Lx7,(<.&40.)(14.(<.&40.)Lx8,(<.&40.)(14.(<.&40.)Lx13,(<.&40.)(14.(<.&40.)Lx14,(<.&40.)(14.(<.&40.)Lx15,(<.&40.)(14.(?.(<.&40.))Lya,(?.(<.&40.))(14.(?.(<.&40.))Lyb,(?.(<.&40.))(0.(11.(?.(<.&40.))R:.(15.(<.&40.)R2.(15.(<.&40.)(4.(<.&40.)R7.(4.(<.&40.)R6.(8.(<.&40.))))(15.(<.&40.)R1.(15.(<.&40.)(4.(<.&40.)R5.(4.(<.&40.)R4.(8.(<.&40.))))(4.(<.&40.)R3.(8.(<.&40.))))))))(0.(11.$12.(13.(<.&40.)R2.)#7.)(0.(11.$12.(13.(<.&40.)R1.)#4.)(0.(16.$2.R<.R;.(17.(<.&40.)$5.$6.R2.))(0.(16.$2.R<.(18.R;.+38.)(4.$5.(6.R7.)(4.$5.(6.R6.)(8.$5.))))(0.(16.$2.R<.(18.R;.+48.)(17.(<.&40.)$5.$6.R1.))(0.(16.$2.R<.(18.R;.+68.)(4.$5.(6.R5.)(4.$5.(6.R4.)(8.$5.))))(16.$2.R<.(18.R;.+78.)(4.$5.(6.R3.)(8.$5.)))))))))))))))))")
(* [comment removed for export] *).
Proof.
  intros m A xs U L.
  destruct xs as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|x8 [|x9 [|x10 [|x11 [|x12 [|x13 [|x14 [|x15 [|]]]]]]]]]]]]]]]]]; try discriminate L.
  apply u64arr_cells in U. cbn [map] in U.
  dexists x7, x8, x13, x14, x15, [x0; x1; x2; x3; x4; x5; x6], [x9; x10; x11; x12].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  change [C8 x0; C8 x1; C8 x2; C8 x3; C8 x4; C8 x5; C8 x6; C8 x7; C8 x8; C8 x9; C8 x10; C8 x11; C8 x12; C8 x13; C8 x14; C8 x15]
    with ([C8 x0; C8 x1; C8 x2; C8 x3; C8 x4; C8 x5; C8 x6] ++ [C8 x7; C8 x8] ++ [C8 x9; C8 x10; C8 x11; C8 x12] ++ [C8 x13; C8 x14] ++ [C8 x15]) in U.
  apply rw_cells_app in U as [U0 U]. apply rw_cells_app in U as [U1 U]. apply rw_cells_app in U as [U2 U]. apply rw_cells_app in U as [U3 U4].
  Ltac fixaddr U A off := match type of U with rw_cells _ _ ?a _ => replace a with (A + off) in U by (cbn [cells_size csize Nat.add]; clear; lia) end.
  fixaddr U1 A 56. fixaddr U2 A 72. fixaddr U3 A 104. fixaddr U4 A 120.
  split; [exact U0|]. split; [exact U1|]. split; [exact U2|]. split; [exact U3| exact U4].
Qed.

#[using="Type"] Lemma u64x16_joinS : ltac2:(CDefT.buildp (gd_tbl_AW_RecChunkS ()) "Pm,P,(<.&40.)(=.(<.&8.))PA,$>.Px7,(<.&40.)Px8,(<.&40.)Px13,(<.&40.)Px14,(<.&40.)Px15,(<.&40.)Pya,(?.(<.&40.))Pyb,(?.(<.&40.))P,(11.$12.(13.(<.&40.)R2.)#7.)P,(11.$12.(13.(<.&40.)R2.)#4.)P,(16.$2.R;.R:.(17.(<.&40.)$5.$6.R4.))P,(16.$2.R<.(18.R;.+38.)(4.$5.(6.R:.)(4.$5.(6.R9.)(8.$5.))))P,(16.$2.R=.(18.R<.+48.)(17.(<.&40.)$5.$6.R5.))P,(16.$2.R>.(18.R=.+68.)(4.$5.(6.R:.)(4.$5.(6.R9.)(8.$5.))))P,(16.$2.R?.(18.R>.+78.)(4.$5.(6.R9.)(8.$5.)))(10.$2.R10.R?.(15.(<.&40.)R9.(15.(<.&40.)(4.(<.&40.)R>.(4.(<.&40.)R=.(8.(<.&40.))))(15.(<.&40.)R8.(15.(<.&40.)(4.(<.&40.)R<.(4.(<.&40.)R;.(8.(<.&40.))))(4.(<.&40.)R:.(8.(<.&40.))))))))")
(* [comment removed for export] *).
Proof.
  intros m A x7 x8 x13 x14 x15 ya yb La Lb U0 U1 U2 U3 U4.
  destruct ya as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|]]]]]]]]; try discriminate La.
  destruct yb as [|x9 [|x10 [|x11 [|x12 [|]]]]]; try discriminate Lb.
  apply cells_u64arr. cbn [map app].
  change [C8 x0; C8 x1; C8 x2; C8 x3; C8 x4; C8 x5; C8 x6; C8 x7; C8 x8; C8 x9; C8 x10; C8 x11; C8 x12; C8 x13; C8 x14; C8 x15]
    with ([C8 x0; C8 x1; C8 x2; C8 x3; C8 x4; C8 x5; C8 x6] ++ [C8 x7; C8 x8] ++ [C8 x9; C8 x10; C8 x11; C8 x12] ++ [C8 x13; C8 x14] ++ [C8 x15]).
  cbn [map] in U0, U2.
  Ltac fixg A off := match goal with |- rw_cells _ _ ?a _ /\ _ => replace a with (A + off) by (cbn [cells_size csize Nat.add]; clear; lia)
                                    | |- rw_cells _ _ ?a _ => replace a with (A + off) by (cbn [cells_size csize Nat.add]; clear; lia) end.
  apply rw_cells_app; split; [exact U0|]. apply rw_cells_app. fixg A 56. split; [exact U1|]. apply rw_cells_app. fixg A 72. split; [exact U2|].
  apply rw_cells_app. fixg A 104. split; [exact U3|]. fixg A 120. exact U4.
Qed.

Section RecChunkS.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  Variables (T CTX SB : Z).
  Hypothesis GSB : 0x10007fff9000 <= SB /\ SB + 2^37 + 4096 <= ACEIL.
  Hypothesis GT : (Timg T /\ Tband T) /\ T + 4096 <= ACEIL.
  Hypothesis GCTX : (0x65f000 <= CTX /\ Pband CTX 0x10000) /\ CTX + 0x10000 <= ACEIL.
  Hypothesis GTC : CTX + 0x10000 <= T \/ T + 4096 <= CTX.
  Hypothesis CST : crange CS T 4096.
  Hypothesis CSCTX : crange CS CTX 0x10000.

  (* [comment removed for export] *)
  Variables (h ms sz idx : Z).
  Let p := h + 4096.
  Let S := 0x7fff8000 + h / 8.
  Let k := ms / 8.
  Variables (K Kd : Model -> Prop).
  Hypothesis KL : kinv AL CS K.
  (* [comment removed for export] *)
  Variable CS' : Z -> Prop.
  Hypothesis CSOK' : cs_ok AL CS'.
  Hypothesis KdL : kinv AL CS' Kd.
  Hypothesis HAS : ltac2:(CDefT.buildp (gd_tbl_AW_RecChunkS ()) "Pmo,$19.P,A1.VK,R1.(11.$1:.(1;.(1<.(1=.R2.))(7.&40.Vh,)(7.&40.(1>.Vms,)))$1?.)")
(* [comment removed for export] *).
  Hypothesis T_unmap : forall mo, K mo -> Kd (munmap_model h (page_round_up_Z ms) mo).
  Variables (can : word) (dd madv : byte).
  Hypothesis POISON : poison0_siteS CS K h ms can dd madv.
  (* [comment removed for export] *)
  Hypothesis HASM : ltac2:(CDefT.buildp (gd_tbl_AW_RecChunkS ()) "Pmo,$19.P,A1.VK,R1.P,(20.(21.VS,)(22.(18.VS,Vk,)))(11.$1:.(23.(1=.R3.)(7.&40.(21.VS,))(7.&40.(24.(22.(18.VS,Vk,))(21.VS,))))$1?.)")
(* [comment removed for export] *).
  Hypothesis T_madv : ltac2:(CDefT.buildp (gd_tbl_AW_RecChunkS ()) "Pmo,$19.P,A1.VK,R1.P,(20.(21.VS,)(22.(18.VS,Vk,)))A1.VK,(25.(21.VS,)(24.(22.(18.VS,Vk,))(21.VS,))R3.)")
(* [comment removed for export] *).
  Hypothesis NOROM : forall x : word, rmp_PB S <= bv_unsigned x < rmp_PE (S + k) -> ro_addr asegs x = false.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Definition rs_W (lo SP PA last HD : Z) : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AW_RecChunkS ()) "(4.(26.$>.$>.)(27.$>.$>.O5.O4.)(4.(26.$>.$>.)(27.$>.$>.(18.VT,+;18.)(18.VT,+;28.))(4.(26.$>.$>.)(27.$>.$>.(18.VT,+;48.)(18.VT,+;58.))(4.(26.$>.$>.)(27.$>.$>.(18.$28.+78.)(18.$28.+81.))(4.(26.$>.$>.)(27.$>.$>.(18.$28.+90.)(18.$28.+:0.))(4.(26.$>.$>.)(27.$>.$>.(18.$29.+10.)(18.$29.+20.))(4.(26.$>.$>.)(27.$>.$>.$2:.(18.$2:.+4.))(4.(26.$>.$>.)(27.$>.$>.(18.O3.(2;.+8.Vidx,))(18.(18.O3.(2;.+8.Vidx,))+8.))(4.(26.$>.$>.)(27.$>.$>.(18.O2.+18.)(18.O2.+20.))(4.(26.$>.$>.)(27.$>.$>.VS,(18.VS,Vk,))(4.(26.$>.$>.)(27.$>.$>.Vh,(18.Vh,Vms,))(8.(26.$>.$>.)))))))))))))")
(* [comment removed for export] *).

  Definition rs_post (SP : Z) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (PA nres n last lms lsz HD lo : Z) (bases : list Z) (m0 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_RecChunkS ()) "Lcf,$2<.(14.$2=.Lms',$2=.(14.$19.Lmo',$19.(14.(<.&40.)Lt0,(<.&40.)(14.(<.&40.)Lt1,(<.&40.)(14.(<.&40.)Lt2,(<.&40.)(14.(<.&40.)La0,(<.&40.)(14.(<.&40.)La1,(<.&40.)(14.(<.&40.)La2,(<.&40.)(14.(<.&40.)La3,(<.&40.)(14.(<.&40.)La4,(<.&40.)(14.(<.&40.)La5,(<.&40.)(14.(<.&40.)La6,(<.&40.)(14.(<.&40.)La7,(<.&40.)(14.(<.&40.)Lt3,(<.&40.)(14.(<.&40.)Lt4,(<.&40.)(14.(<.&40.)Lt5,(<.&40.)(14.(<.&40.)Lt6,(<.&40.)(14.(<.&40.)Lnfr',(<.&40.)(14.(<.&40.)Lcal',(<.&40.)(14.(<.&40.)Lg2',(<.&40.)(14.(<.&40.)Lg3',(<.&40.)(14.(?.(<.&40.))Lxs',(?.(<.&40.))(14.P,(<.&40.)(=.(<.&8.))Lm',P,(<.&40.)(=.(<.&8.))(0.(11.$2<.R18.(2>.R17.R16.))(0.(11.$2=.R17.(2?.(30.O1:.(7.&40.O1;.)O19.(7.&40.$31.)R15.R14.R13.O18.O17.R12.R11.R10.R?.R>.R=.R<.R;.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.R:.R9.R8.R7.)O<.(32.O1:.)O;.(33.(<.&40.))R1.(34.$2.)))(0.A1.VKd,R16.(0.(35.R1.R16.)(0.(36.(37.O3.O1;.O:.O7.O4.)O1.R1.)(0.(38.Vh,Vms,O1.R1.)(0.(39.$2.R1.)(0.(3:.$2.R1.O3.O1;.)(0.(3;.R1.VSB,VCTX,VT,Vcan,Vdd,Vmadv,)(0.(3<.R1.O:.O9.(24.O8.+1.)(7.&8.=)R6.R5.R4.R3.=)(0.(10.$2.R1.O:.(17.$>.(<.&40.)(7.&40.)(3=.$>.O2.(3>.Vidx,)O7.)))(0.P,(20.Vidx,(24.O8.+1.))(16.$2.R2.O7.(4.$5.(6.(7.&40.O7.))(4.$5.(6.(7.&40.O6.))(4.$5.(6.(7.&40.O5.))(4.$5.(6.(7.&40.Vidx,))(8.$5.))))))(0.(10.$2.R1.(18.VT,+:>0.)R2.)(0.(11.$12.(13.(<.&40.)R2.)#10.)(0.(16.$2.R1.VS,(4.$5.(3?.(3>.Vk,)(40.(<.&8.)(7.&8.=)(3>.Vk,)))(8.$5.)))Px,(<.&40.)P,(0.(41.Vh,(42.&40.R1.))(20.(42.&40.R1.)(18.Vh,Vms,)))(11.(=.(<.&8.))A1.R3.R2.(33.(<.&8.)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  #[using="AL IMG ALWF CSOK GSB GT GCTX GTC CST CSCTX KL CSOK' KdL HAS T_unmap POISON HASM T_madv NOROM"] Theorem rec_sec_cfgS : ltac2:(CDefT.buildp (gd_tbl_AW_RecChunkS ()) "PQ,P,$2<.SpPra,(<.&40.)Pgp,(<.&40.)Ptp,(<.&40.)Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Ps0,(<.&40.)Ps1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Ps2,(<.&40.)Ps3,(<.&40.)Ps4,(<.&40.)Ps5,(<.&40.)Ps6,(<.&40.)Ps7,(<.&40.)Ps8,(<.&40.)Ps9,(<.&40.)Ps10,(<.&40.)Ps11,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)Pmun,(<.&40.)Pmuned,(<.&40.)Pnfr,(<.&40.)Pcal,(<.&40.)Pg2,(<.&40.)Pg3,(<.&40.)Psorted,(<.&8.)PSP,$>.PCBP,$>.PHD,$>.Pn0,$>.Pctx,$>.Pb1,$>.Pst,$>.PPA,$>.Pnres,$>.Pn,$>.Plast,$>.Plms,$>.Plsz,$>.Plo,$>.Pbases,(?.$>.)Pxs,(?.(<.&40.))Pjunk,(?.(<.&8.))PF,(43.&5.(<.&40.))Pfc,(<.&20.)Pm,P,(<.&40.)(=.(<.&8.))Pmo,$19.P,(11.$>.(44.Vh,+1000.)=)P,(0.(41.+65?000.Vh,)(45.(41.(18.Vh,Vms,)+7???7000.)(41.+10007???8000.Vh,)))P,(41.(18.Vh,Vms,)(46.VhAR,))P,(0.(41.+1000.Vms,)(20.Vms,(47.+2.+2;.)))P,(11.$>.(44.Vms,+1000.)=)P,(0.(41.=Vsz,)(20.Vsz,(47.+2.+40.)))P,(45.(41.(18.Vh,Vms,)VSB,)(41.(18.VSB,(47.+2.+25.))Vh,))P,(41.Vp,R1:.)P,(41.(18.R1;.+10.)(18.Vh,Vms,))P,(0.(41.=R1;.)(20.R1;.(47.+2.+20.)))P,(0.(41.=R19.)(20.R19.+100.))P,(0.(41.=R1;.)(20.R1;.+100.))P,(16.$2.R>.R1?.(48.R1<.R1;.))P,(16.$2.R?.(18.R20.+4.)(49.R1?.R1>.))P,(45.(41.(18.VT,+1000.)Vh,)(41.(18.Vh,Vms,)VT,))P,(45.(41.(18.VCTX,+10000.)Vh,)(41.(18.Vh,Vms,)VCTX,))P,(0.(41.=Vidx,)(20.Vidx,R1<.))P,(41.R1=.(4:.(13.$>.R18.)))P,(20.(4:.(13.$>.R19.))(47.+2.+28.))P,(11.(=.$>.)(4;.$>.R1:.(3>.Vidx,))(4<.$>.Vh,))P,(11.(=.$>.)(4;.$>.R1;.(3>.(24.R20.+1.)))(4<.$>.R1?.))P,(0.(41.+65?000.R23.)(45.(41.(18.R23.+800000.)+7???7000.)(41.+10007???8000.R23.)))P,(0.(41.(2;.+8.(4:.(13.$>.R1=.)))+800000.)(41.(18.R24.+800000.)(46.VhAR,)))P,(0.(41.=R24.)(20.R24.(47.+2.+40.)))P,Pj,$12.Pb,$>.P,(11.(=.$>.)(4;.$>.R21.R2.)(4<.$>.R1.))P,(4=.R3.(3>.R27.))(0.(0.(41.=R3.)(20.R3.(47.+2.+3?.)))P,(4>.(11.$12.R4.(3>.Vidx,)))(45.(41.(18.R4.+1000.)Vh,)(41.(18.Vh,Vms,)R4.)))P,(3<.R1;.R27.R26.R25.R2?.R33.R32.R31.R30.=)P,(10.$2.R1<.R28.(17.$>.(<.&40.)(7.&40.)R21.))P,(4?.VCS,R29.(2;.+8.(4:.(13.$>.R22.))))P,(16.$2.R1>.Vh,(4.$5.(6.(7.&40.Vh,))(4.$5.(6.(7.&40.Vms,))(4.$5.(6.(7.&40.Vsz,))(4.$5.(6.(7.&40.Vidx,))(8.$5.))))))P,(4?.VCS,Vh,Vms,)P,(45.(41.(18.R2<.(2;.+8.(4:.(13.$>.R25.))))Vh,)(41.(18.Vh,Vms,)R2<.))P,(45.(0.(11.$>.Vidx,(24.R2;.+1.))(11.$>.R2:.Vh,))(0.(20.Vidx,(24.R2;.+1.))(0.(0.(41.+65?000.R2:.)(45.(41.(18.R2:.+1000.)+7???7000.)(41.+10007???8000.R2:.)))(0.(41.(18.R2:.+1000.)(46.VhAR,))(0.(45.(41.(18.R2:.+1000.)Vh,)(41.(18.Vh,Vms,)R2:.))(0.(45.(41.(18.R2=.(2;.+8.(4:.(13.$>.R26.))))R2:.)(41.(18.R2:.+1000.)R2=.))(0.(45.(41.(18.VT,+1000.)R2:.)(41.(18.R2:.+1000.)VT,))(0.(45.(41.(18.VCTX,+10000.)R2:.)(41.(18.R2:.+1000.)VCTX,))(0.(16.$2.R21.R2:.(4.$5.(6.(7.&40.R2:.))(4.$5.(6.(7.&40.R29.))(4.$5.(6.(7.&40.R28.))(4.$5.(6.(7.&40.(24.R2;.+1.)))(8.$5.))))))(4?.VCS,R2:.+20.))))))))))P,(45.(41.(18.VT,+1000.)R2>.)(41.(18.R2>.(2;.+8.(4:.(13.$>.R27.))))VT,))P,(45.(41.(18.VCTX,+10000.)R2?.)(41.(18.R2?.(2;.+8.(4:.(13.$>.R28.))))VCTX,))P,(10.$2.R24.(18.VT,+:>0.)R28.)P,(11.$12.(13.(<.&40.)R29.)#10.)P,(3;.R26.VSB,VCTX,VT,Vcan,Vdd,Vmadv,)P,(16.$2.R27.VS,(4.$5.(3?.(3>.Vk,)R2:.)(8.$5.)))P,(3:.$2.R28.R2>.R3;.)P,(41.(46.VhAR,)R2?.)P,(41.R30.(24.R3=.+2>0.))P,(41.R3>.(47.+2.+3>.))P,(11.$>.(44.R3?.+10.)=)P,(4?.VCS,R33.(24.R40.R33.))P,(4?.VCS',R34.(24.R41.R34.))P,(39.$2.R2?.)P,(11.(<.&40.)R64.(7.&40.$31.))P,A1.VK,R30.P,(35.R32.R31.)P,Pc',$2<.P,(50.R47.R6:.R69.R64.R63.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R36.R35.R40.R3?.R3>.R3=.R3<.R3;.R45.R3:.R39.R34.R1.)(51.$2.R6<.R2.)(51.$2.R6;.(2>.(2?.(30.R6:.(7.&40.R47.)R69.R68.R67.R66.R65.R64.R63.(7.&40.R46.)(7.&40.R45.)R62.R61.R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.)R36.(7.&40.$52.)R35.(33.(<.&40.))R34.(34.$2.))R33.))")
(* [comment removed for export] *).
  Proof.
    intros Q ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mun muned nfr cal g2 g3 sorted
      SP CBP HD n0 ctx b1 st PA nres n last lms lsz lo bases xs junk F fc m mo
      HAL HHI HMS MSB MSA SZB HNP HD0 HD1 NB STB B1B HW0 HW1 ATH ACH IDX NBL LB NI NL PAL PAH NRB BASES SEC ARR PACS HDR HCS APH CASES ATP ACP
      TST LXS RSS SH ST LOIMG SPL SPH SPA SCS SCS' MI TP HK HJ HC.
    facts. subst tp.
    pose proof GSB as [SB0 SB1]. pose proof GT as [T0 T1]. pose proof GCTX as [CX0 CX1].
    dpose RSS as (SBC & DS & PS & RS).
    assert (Hp : p = h + 4096) by reflexivity. assert (HSd : S = 0x7fff8000 + h / 8) by reflexivity. assert (HKd : k = ms / 8) by reflexivity.
    pose proof (Z.div_mod h 8 ltac:(clear; lia)) as DH. pose proof (Z.mod_pos_bound h 8 ltac:(clear; lia)) as DHB.
    pose proof (Z.div_mod ms 8 ltac:(clear; lia)) as DM. pose proof (Z.mod_pos_bound ms 8 ltac:(clear; lia)) as DMB.
    assert (SKB : ((h + ms <= 0x7fff7000 /\ 0x800c3e00 <= S /\ S + k <= 0x8fff7000) \/ (0x10007fff8000 <= h /\ 0x20008fff000 <= S /\ S + k <= 0x10007fff0000)) /\ 0 <= k)
      by (rewrite HSd, HKd; clear -DH DHB DM DMB HHI HMS MSB; lia).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    ddestruct (u64x16_splitS m (T + 2784) xs TST LXS) as (x7 & x8 & x13 & x14 & x15 & ya & yb & HXS & La & Lb & U0 & U1 & U2 & U3 & U4).
    replace (T + 2784 + 56) with (T + 2840) in U1 by (clear; lia). replace (T + 2784 + 72) with (T + 2856) in U2 by (clear; lia).
    replace (T + 2784 + 104) with (T + 2888) in U3 by (clear; lia). replace (T + 2784 + 120) with (T + 2904) in U4 by (clear; lia).
    assert (DJ1 : forall A j, (A + j <= lo \/ SP <= A) -> (A + j <= A_SEC_MUTEX \/ A_SEC_MUTEX + 4 <= A) -> (A + j <= T + 2840 \/ T + 2856 <= A) ->
                  disjoint_from [(lo, SP); (A_SEC_MUTEX, A_SEC_MUTEX + 4); (T + 2840, T + 2856)] A j)
      by (intros A j H1 H2 H3; cbn; clear -H1 H2 H3; repeat split; lia).
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL CS K
              (fun ms' => exists (e0 e1 e2 b3 b4 b5 b6 b7 : word) (m1 : mem),
                 ms' = MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) e0 e1 e2 s0 s1 (Z_to_bv 64 A_SECONDARY) (Z_to_bv 64 A_GSTATS) (Z_to_bv 64 p) b3 b4 b5 b6 b7
                               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_LARGE_DEALLOC) fc None m1 (seg_rom asegs)
                 /\ munch [(lo, SP); (A_SEC_MUTEX, A_SEC_MUTEX + 4); (T + 2840, T + 2856)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo SP
                 /\ gbb_cells m1 PA nres n sorted 0)
              Q _ mo KL HK); [exact HJ| |].
    { eapply evtA_cut.
      { eapply (cbrS_A AL IMG ALWF CS CSOK) with (lo := lo) (SB := SB);
          first [ exact SBC | exact ST | exact LOIMG | exact MI | exact SCS
                | clear -SB0; lia | clear -SB1; lia | clear -Hp HD0 HD1 HHI HMS; lia | clear -Hp HD0 HD1 HNP; lia | clear -SPL; lia | exact SPH
                | match goal with |- ?G => idtac "RS1-LEFTOVER" G end ]. }
      cbv beta. (intros ms1 dd_H; ddestruct dd_H as (m1 & MU1 & WM1 & MI1 & FR1 & ST1 & ->)).
      assert (DJ0 : forall A j, (A + j <= lo \/ SP <= A) -> disjoint_from [(lo, SP)] A j) by (intros A j H; cbn; clear -H; lia).
      (* [comment removed for export] *)
      dpose SEC as (Q1 & Q2 & Q3 & Q4 & Q5).
      eapply evtA_cut.
      { eapply (gbb_spec AL IMG ALWF CS CSOK) with (PA := PA) (nres := nres) (n := n) (h := h) (ms := ms) (sz := sz) (idx := idx) (lo := lo) (bases := bases) (sorted := sorted).
        all: lazymatch goal with
             | |- evtA _ _ _ _ _ => idtac
             | |- nth_error _ _ = Some h => exact NI
             | |- h mod 4096 = 0 => exact HAL
             | |- forall j b, _ => exact BASES
             | |- gbb_cells _ _ _ _ _ _ => split; [| split]; (eapply rw_cells_munch; [eassumption| exact MU1| apply DJ0; unfold A_SECONDARY, A_SEC_MUTEX, A_INSTANCE; cbn; clear -LOIMG; lia])
             | |- u64arr _ _ _ _ => eapply u64arr_transport; [exact ARR| exact MU1| exact WM1| apply DJ0; rewrite map_length; clear -PAH LOIMG; lia]
             | |- crange _ _ (8 * _) => exact PACS
             | |- rw_cells _ _ h _ => eapply rw_cells_munch; [exact HDR| exact MU1| apply DJ0; cbn; clear -HMS MSB LOIMG; lia]
             | |- crange _ h _ => eapply crange_sub; [exact HCS| clear; lia| clear -MSB; lia]
             | |- stk _ _ _ _ => exact ST1
             | |- mem_inv _ _ => exact MI1
             | |- crange _ _ _ => eapply crange_sub; [exact SCS| clear; lia| clear -SPL; lia]
             | |- _ => clear - SPL SPH LOIMG IDX NBL LB PAL PAH NRB HHI HMS MSB SZB Hp HD0 HD1; lia
             end. }
      cbv beta. (intros ms2 dd_H; ddestruct dd_H as (m2 & x5 & x11 & x12 & y13 & y14 & y15 & y16 & y17 & MU2 & WM2 & MI2 & GBB2 & ST2 & ->)).
      replace (ret_pc (Z_to_bv 64 A_CBRS_B)) with (Z_to_bv 64 A_CBRS_B) by (symmetry; apply ret_pc_even; [clear; unfold A_CBRS_B; lia | reflexivity]).
      fold p.
      assert (DJ2 : forall A j, (A + j <= lo \/ SP + -48 <= A) -> (A + j <= A_SEC_MUTEX \/ A_SEC_MUTEX + 4 <= A) -> disjoint_from [(lo, SP + -48); (A_SEC_MUTEX, A_SEC_MUTEX + 4)] A j)
        by (intros A j H1 H2; cbn; clear -H1 H2; repeat split; lia).
      assert (MU02 : munch [(lo, SP); (A_SEC_MUTEX, A_SEC_MUTEX + 4)] m m2).
      { eapply munch_trans; [eapply munch_weaken; [| exact MU1]| eapply munch_weaken; [| exact MU2]]; clear; solve_sub_fp. }
      pose proof (wmono_trans asegs _ _ _ WM1 WM2) as WM02.
      assert (DJ02 : forall A j, (A + j <= lo \/ SP <= A) -> (A + j <= A_SEC_MUTEX \/ A_SEC_MUTEX + 4 <= A) -> disjoint_from [(lo, SP); (A_SEC_MUTEX, A_SEC_MUTEX + 4)] A j)
        by (intros A j H1 H2; cbn; clear -H1 H2; repeat split; lia).
      (* [comment removed for export] *)
      eapply evtA_mono.
      { eapply (cbrS_B AL IMG ALWF CS CSOK) with (SB := SB) (n := n0) (ctx := ctx) (b1 := b1) (st := st) (T := T) (CTX := CTX) (lo := lo) (m0 := m2) (rf := x7) (rfd := x8).
        all: lazymatch goal with
             | |- evtA _ _ _ _ _ => idtac
             | |- ro_cells _ _ A_SPACEBEG_CELL _ => eapply ro_cells_transport; [exact SBC| exact MU02| apply DJ02; unfold A_SPACEBEG_CELL, A_SEC_MUTEX, A_INSTANCE; cbn; clear -LOIMG; lia]
             | |- rw_cells _ _ _ (hdr_w0 _ _) => eapply rw_cells_munch; [exact HW0| exact MU02| apply DJ02; unfold A_SEC_MUTEX, A_INSTANCE; cbn; clear -Hp HD0 HD1 HHI HMS LOIMG; lia]
             | |- rw_cells _ _ _ (hdr_rest _ _) => eapply rw_cells_munch; [exact HW1| exact MU02| apply DJ02; unfold A_SEC_MUTEX, A_INSTANCE; cbn; clear -Hp HD0 HD1 HHI HMS LOIMG; lia]
             | |- crange _ _ 16 => eapply crange_sub; [exact HCS| clear -Hp HD0; lia| clear -HD1; lia]
             | |- rw_cells _ _ (T + 2840) _ => eapply rw_cells_munch; [exact U1| exact MU02| apply DJ02; unfold A_SEC_MUTEX, A_INSTANCE; cbn; clear -T0 T1 LOIMG SPL; lia]
             | |- dealloc_statics _ _ _ => eapply dealloc_statics_transport_fine; [exact DS| exact MU02| |];
                                            [intros A' n' H1' H2' | intros A' n' [H1' H2']]; apply DJ02; unfold A_SEC_MUTEX, A_INSTANCE in *; cbn;
                                            [clear -H1' LOIMG; lia| clear -H1' H2'; lia| clear -H1' H2' CX0 CX1 LOIMG; lia| clear -H1' CX0; lia]
             | |- crange _ T _ => exact CST
             | |- crange _ CTX _ => exact CSCTX
             | |- cbr_frame _ _ _ _ _ _ _ _ => unfold cbr_frame in FR1 |- *; eapply rw_cells_munch; [exact FR1| exact MU2| apply DJ2; unfold A_SEC_MUTEX, A_INSTANCE; cbn; clear -LOIMG SPL; lia]
             | |- stk _ _ _ _ => exact ST2
             | |- munch _ _ _ => apply munch_refl
             | |- wmono _ _ _ => apply wmono_refl
             | |- mem_inv _ _ => exact MI2
             | |- crange _ _ _ => exact SCS
             | |- _ => first [exact ATH | clear - SPL SPH LOIMG SB0 SB1 Hp HD0 HD1 HHI HMS HNP MSB NB STB B1B T0 T1 CX0 CX1 ATH; lia]
             end. }
      cbv beta. intros ms3 P3. unfold cbrS_post in P3.
      ddestruct P3 as (m3 & e0 & e1 & e2 & b3 & b4 & b5 & b6 & b7 & MU3 & WM3 & MI3 & ST3 & ->).
      dexists e0, e1, e2, b3, b4, b5, b6, b7, m3. split; [reflexivity|].
      split. { eapply munch_trans; [eapply munch_weaken; [| exact MU02]| eapply munch_weaken; [| exact MU3]]; clear; solve_sub_fp. }
      split; [exact (wmono_trans asegs _ _ _ WM02 WM3)|]. split; [exact MI3|]. split; [exact ST3|].
      ddestruct GBB2 as (G1 & G2 & G3). unfold A_SECONDARY, A_SEC_MUTEX, A_INSTANCE in *.
      split; [| split]; [eapply (rw_cells_munch _ _ _ _ _ G1 MU3) | eapply (rw_cells_munch _ _ _ _ _ G2 MU3) | eapply (rw_cells_munch _ _ _ _ _ G3 MU3)];
        cbn; clear -LOIMG T0; repeat split; lia. }
    (* [comment removed for export] *)
    cbn beta. intros ms4 mo4 P4 HK4 MM4 HJ4.
    ddestruct P4 as (e0 & e1 & e2 & b3 & b4 & b5 & b6 & b7 & m4 & -> & MU4 & WM4 & MI4 & ST4 & GBB4).
    assert (DJ4 : forall A n', (A + n' <= lo \/ SP <= A) -> (A + n' <= A_SEC_MUTEX \/ A_SEC_MUTEX + 4 <= A) -> (A + n' <= T + 2840 \/ T + 2856 <= A) ->
                  disjoint_from [(lo, SP); (A_SEC_MUTEX, A_SEC_MUTEX + 4); (T + 2840, T + 2856)] A n')
      by (intros A n' H1 H2 H3; cbn; clear -H1 H2 H3; repeat split; lia).
    assert (FD4 : fine_dj [(lo, SP); (A_SEC_MUTEX, A_SEC_MUTEX + 4); (T + 2840, T + 2856)]).
    { intros A n' H1 H2. apply DJ4; unfold A_SEC_MUTEX in *; clear -H1 H2 LOIMG T0; lia. }
    assert (TR4 : forall A cs0, rw_cells asegs m A cs0 -> (A + Z.of_nat (cells_size cs0) <= lo \/ SP <= A) ->
              (A + Z.of_nat (cells_size cs0) <= A_SEC_MUTEX \/ A_SEC_MUTEX + 4 <= A) -> (A + Z.of_nat (cells_size cs0) <= T + 2840 \/ T + 2856 <= A) -> rw_cells asegs m4 A cs0)
      by (intros A cs0 H H1 H2 H3; eapply rw_cells_munch; [exact H| exact MU4| apply DJ4; assumption]).
    (* [comment removed for export] *)
    pose proof (proj2 U1) as WR1. cbn [cells_size csize Nat.add] in WR1. change (Z.of_nat 16) with 16 in WR1.
    apply (wr_at_transport asegs m m4) in WR1; [| exact WM4].
    ddestruct (wr_at_off_C8C8 m4 (T + 2840) WR1 ltac:(clear -T0; lia)) as (r1 & r2 & U1').
    dpose SEC as (Q1 & Q2 & Q3 & Q4 & Q5).
    eapply (large_free_cfgS AL IMG ALWF CS CSOK h ms sz idx K Kd KL CS' CSOK' KdL HAS T_unmap can dd madv POISON HASM T_madv NOROM Q)
      with (sorted := sorted) (g2 := g2) (g3 := g3) (mun := x13) (muned := x14) (nfr := nfr) (cal := cal) (PA := PA) (nres := nres) (n := n)
           (last := last) (lms := lms) (lsz := lsz) (T := T) (CTX := CTX) (lo := lo) (bases := bases) (junk := junk).
    all: lazymatch goal with
         | |- aevtS _ _ _ => idtac
         | |- forall c', _ -> _ => idtac
         | |- h mod 4096 = 0 => exact HAL
         | |- ms mod 4096 = 0 => exact MSA
         | |- nth_error _ (Z.to_nat idx) = _ => exact NI
         | |- nth_error _ _ = Some _ => exact NL
         | |- sec_cells _ _ _ _ _ _ _ _ _ _ => ddestruct GBB4 as (G1 & G2 & G3); split; [exact G1|]; split; [exact G2|]; split; [| split; [| exact G3]];
                                                [apply (TR4 _ _ Q3) | apply (TR4 _ _ Q4)]; unfold A_GSTATS, A_SEC_MUTEX, A_INSTANCE; cbn; clear -LOIMG T0; lia
         | |- u64arr _ _ _ _ => eapply u64arr_transport; [exact ARR| exact MU4| exact WM4| apply DJ4; rewrite map_length; unfold A_SEC_MUTEX, A_INSTANCE; clear -PAL PAH LOIMG ATP; lia]
         | |- crange _ _ (8 * _) => exact PACS
         | |- rw_cells _ _ h _ => apply (TR4 _ _ HDR); unfold A_SEC_MUTEX, A_INSTANCE; cbn; clear -HHI HMS MSB LOIMG ATH; lia
         | |- crange _ h _ => exact HCS
         | |- _ /\ _ \/ _ => destruct CASES as [L|(C1 & C2 & C3 & C4 & C5 & C6 & C7 & LH & LCS)]; [left; exact L| right];
                             split; [exact C1|]; split; [exact C2|]; split; [exact C3|]; split; [exact C4|]; split; [exact C5|]; split; [exact C6|]; split; [exact C7|];
                             split; [| exact LCS]; apply (TR4 _ _ LH); unfold A_SEC_MUTEX, A_INSTANCE; cbn; clear -C2 C3 C6 LOIMG; lia
         | |- rw_cells _ _ (T + 2888) _ => apply (TR4 _ _ U3); unfold A_SEC_MUTEX, A_INSTANCE; cbn; clear -T0 T1 SPL LOIMG; lia
         | |- crange _ T _ => exact CST
         | |- crange _ CTX _ => exact CSCTX
         | |- dealloc_statics _ _ _ => eapply dealloc_statics_transport_fine; [exact DS| exact MU4| exact FD4|];
                                        intros A n' [H1' H2']; apply DJ4; unfold A_SEC_MUTEX, A_INSTANCE in *; cbn; [clear -H2' CX1 LOIMG; lia| clear -H1' CX0; lia| clear -H1' H2' GTC; lia]
         | |- poison_statics _ => exact (poison_statics_transport_fine _ _ _ PS MU4 FD4)
         | |- rsmr_statics _ _ _ _ => exact (rsmr_statics_transport_fine _ _ _ _ _ _ RS MU4 FD4)
         | |- rw_cells _ _ _ [CB _ _] => change (2147450880 + h / 8) with S; change (ms / 8) with k; apply (TR4 _ _ SH); cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SKB; lia); unfold A_SEC_MUTEX, A_INSTANCE; clear -SKB LOIMG T0; lia
         | |- stk _ _ _ _ => exact ST4
         | |- _ mod 16 = 0 => exact SPA
         | |- crange CS' _ _ => eapply crange_sub; [exact SCS'| clear; lia| clear; lia]
         | |- crange _ _ _ => exact SCS
         | |- mem_inv _ _ => exact MI4
         | |- K _ => exact HK4
         | |- J _ _ => exact HJ4
         | |- _ => first [exact IDX | exact HNP | exact ATH | exact ACH | exact APH | exact ATP | exact ACP | exact GTC | exact BASES
                        | clear - SPL SPH LOIMG HHI HMS MSB SZB IDX NBL LB PAL PAH NRB T0 T1 CX0 CX1; lia ]
         end.
    (* [comment removed for export] *)
    intros c5 P5. unfold lfree_postS in P5.
    ddestruct P5 as (ms5 & mo5 & y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & nfr' & cal' & g2' & g3' & m5
                    & -> & -> & MU5 & WMO5 & MI5 & ST5 & SEC5 & ARR5 & LH5 & (mun' & muned' & TST5) & SHZ5 & NONE5 & HKd5 & HJ5).
    change (2147450880 + h / 8) with S in MU5, SHZ5. change (ms / 8) with k in MU5, SHZ5.
    assert (MU05 : munch (rs_W lo SP PA last HD) m m5).
    { unfold rs_W. eapply munch_trans; [eapply munch_weaken; [| exact MU4]| eapply munch_weaken; [| exact MU5]]; unfold lfree_W, ldA_W; clear; solve_sub_fp. }
    assert (WMO05 : wmono_out h ms m m5) by (eapply wmono_out_trans; [apply wmono_out_of_wmono; exact WM4| exact WMO5]).
    assert (LASTB : (0x65f000 <= last /\ (last + 32 <= 0x7fff7000 \/ 0x10007fff8000 <= last)) /\ last + 32 <= ACEIL /\ (T + 4096 <= last \/ last + 32 <= T)).
    { destruct CASES as [[_ ->]|(_ & C2 & C3 & _ & _ & C6 & _)]; [clear -HHI HMS MSB ATH; lia| clear -C2 C3 C6; lia]. }
    assert (DJ5 : forall A n', (A + n' <= lo \/ SP <= A) -> (A + n' <= T + 2840 \/ T + 2856 <= A) -> (A + n' <= T + 2888 \/ T + 2904 <= A) ->
                  (A + n' <= A_INSTANCE \/ A_INSTANCE + 1024 <= A) -> (A + n' <= PA \/ PA + 8 * Z.of_nat (length bases) <= A) ->
                  (A + n' <= last \/ last + 32 <= A) -> (A + n' <= S \/ S + k <= A) -> (A + n' <= h \/ h + ms <= A) ->
                  disjoint_from (rs_W lo SP PA last HD) A n').
    { intros A n' H1 H2 H3 H4 H5 H6 H7 H8. unfold rs_W, A_GSTATS, A_SEC_MUTEX. cbn. clear -H1 H2 H3 H4 H5 H6 H7 H8 IDX NBL. repeat split; lia. }
    assert (FD5 : fine_dj (rs_W lo SP PA last HD)).
    { intros A n' H1 H2. apply DJ5; clear -H1 H2 LOIMG T0 PAL LASTB SKB HHI; lia. }
    assert (TRT : forall A cs0, rw_cells asegs m A cs0 -> T + 2784 <= A -> A + Z.of_nat (cells_size cs0) <= T + 2912 ->
              (A + Z.of_nat (cells_size cs0) <= T + 2840 \/ T + 2856 <= A) -> (A + Z.of_nat (cells_size cs0) <= T + 2888 \/ T + 2904 <= A) -> rw_cells asegs m5 A cs0).
    { intros A cs0 H H1 H2 H3 H4. eapply rw_cells_transport_out; [exact H| exact MU05| exact WMO05| | clear -H1 H2 ATH; lia].
      apply DJ5; unfold A_INSTANCE; clear -H1 H2 H3 H4 SPL LOIMG T0 T1 ATP ATH LASTB SKB; lia. }
    apply HC. unfold rs_post.
    eexists _, mo5. deexists 15. dexists nfr', cal', g2', g3', (ya ++ [r1; r2] ++ yb ++ [mun'; muned'] ++ [x15]), m5.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HKd5|]. split; [exact HJ5|].
    split; [exact MU05|]. split; [exact WMO05|]. split; [exact MI5|]. split; [exact ST5|].
    split. { split; [| split; [| split]].
             - eapply ro_cells_transport; [exact SBC| exact MU05|]. unfold rs_W, A_SPACEBEG_CELL, A_GSTATS, A_SEC_MUTEX, A_INSTANCE. cbn.
               clear -LOIMG T0 PAL LASTB SKB HHI IDX. repeat split; lia.
             - eapply dealloc_statics_transport_fine; [exact DS| exact MU05| exact FD5|].
               intros A n' [H1' H2']; apply DJ5; unfold A_INSTANCE; clear -H1' H2' CX0 CX1 LOIMG GTC ACP ACH LASTB SKB CASES HHI HMS MSB; lia.
             - exact (poison_statics_transport_fine _ _ _ PS MU05 FD5).
             - exact (rsmr_statics_transport_fine _ _ _ _ _ _ RS MU05 FD5). }
    split; [exact SEC5|]. split; [exact ARR5|]. split; [exact LH5|].
    split. { apply u64x16_joinS; [exact La| exact Lb| | | | |].
             - apply (TRT _ _ U0); rewrite ?cells_size_C8s, ?La; clear; lia.
             - replace (T + 2784 + 56) with (T + 2840) by (clear; lia). eapply rw_cells_transport_out; [exact U1'| exact MU5| exact WMO5| | cbn; clear -ATH; lia].
               unfold lfree_W, ldA_W, A_GSTATS, A_SEC_MUTEX, A_INSTANCE. cbn. clear -SPL LOIMG T0 T1 ATP ATH HMS MSB PAL LASTB SKB HHI IDX NBL. repeat split; lia.
             - replace (T + 2784 + 72) with (T + 2856) by (clear; lia). apply (TRT _ _ U2); rewrite ?cells_size_C8s, ?Lb; clear; lia.
             - replace (T + 2784 + 104) with (T + 2888) by (clear; lia). exact TST5.
             - replace (T + 2784 + 120) with (T + 2904) by (clear; lia). apply (TRT _ _ U4); cbn; clear; lia. }
    split. { rewrite !app_length. cbn [length]. rewrite La, Lb. reflexivity. }
    split; [exact SHZ5| exact NONE5].
  Qed.
End RecChunkS.

End ARUN_1.
