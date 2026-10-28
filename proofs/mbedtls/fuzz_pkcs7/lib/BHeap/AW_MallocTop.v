(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Arr Bytes Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import DivergeSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AKinv AJ AKinvS ASpinS AW_MmapAnon AW_MmapDie ASpin
     AW_DepotA AW_DepotB AW_DepotC AW_DepotD AW_DepotE AW_DepotF AW_DepotCfg AW_DepotInv AW_DepotTop
     AW_MallocA AW_AllocA AW_Poison AW_AllocB AW_MallocB AW_MallocC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_MallocTop () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.dkeep"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.A_DEP_END"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dblk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.sblk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.eq"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.fin_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.true"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_cs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_statics"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Lists.ListDef.Forall"; "ARUN_1.MallocTop.mkeep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kAllocBegMagic"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.pgv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_STACK_DEPOT_PUT"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocA.A_PC_MALLOC"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocC.msegA_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_GOT_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_FL_PPART"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "ARUN_1.MallocTop.mtop_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocA.A_MALLOC"].

Section ARUN_1. Context {hAR : arun}.
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L34301640341.9L46253703355.7L58852693222.900000Q00e01?S2nb1A2sz1k2H31x2X12X22XR2bl1j2H4S1A2sz2H21x2X12X22XRS2lo2SP1A2sz2H11x2X12X22XR". (* [comment removed for export] *)
#[using="Type"] Lemma dkeep_window : ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Plo,$2.PSP,$2.Pnb,(3.$2.)Pbl,(3.$2.)PA,$2.Psz,$2.P,(4.R8.R7.R6.R5.R4.R3.)P,(5.=R3.)P,(5.(6.R4.R3.)(7.+2.+40.))P,(8.(5.(6.R5.R4.)R9.)(5.R8.R5.))P,(8.(5.(6.R6.R5.)$9.)(5.$:.R6.))P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R:.))))(8.(5.(6.R9.R8.)(?.R;.R2.))(5.(6.(?.R;.R2.)(7.+2.+14.))R9.))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R:.))))(8.(5.(6.R:.R9.)(10.R;.R2.))(5.(6.(10.R;.R2.)(7.+2.+17.))R:.))(11.(12.(13.$2.$2.)(14.$2.$2.=R9.)(12.(13.$2.$2.)(14.$2.$2.(6.R9.R8.)(7.+2.+40.))(15.(13.$2.$2.))))R?.R>.)")
(* [comment removed for export] *).
Proof.
  intros m m' lo SP nb bl A sz DK A0 A1 H1 H2 H3 H4 x Hx. cbn [outside] in Hx. ddestruct Hx as (X1 & X2 & _).
  pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
  apply DK.
  - clear - H1 X1 X2 XR. lia.
  - clear - H2 X1 X2 XR. lia.
  - intros k Hk. specialize (H3 k Hk). clear - H3 X1 X2 XR. lia.
  - intros j Hj. specialize (H4 j Hj). clear - H4 X1 X2 XR. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L34301640341.7L58852693222.700000I00[S2nb1k2BN1x2X22XR2bl1j2BSS2lo2SP2LO1x2X22XR". (* [comment removed for export] *)
#[using="Type"] Lemma dkeep_low : ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Plo,$2.PSP,$2.Pnb,(3.$2.)Pbl,(3.$2.)P,(4.R6.R5.R4.R3.R2.R1.)P,(5.+65?000.R5.)P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R5.))))(5.+65?000.(?.R6.R2.))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R5.))))(5.+65?000.(10.R6.R2.))(11.(12.(13.$2.$2.)(14.$2.$2.$9.$:.)(12.(13.$2.$2.)(14.$2.$2.+65?000.(7.+2.+40.))(15.(13.$2.$2.))))R:.R9.)")
(* [comment removed for export] *).
Proof.
  intros m m' lo SP nb bl DK LO BN BS x Hx. cbn [outside] in Hx. ddestruct Hx as (X1 & X2 & _).
  pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
  apply DK.
  - clear - LO X1 X2 XR. lia.
  - exact X1.
  - intros k Hk. specialize (BN k Hk). clear - BN X1 X2 XR. lia.
  - intros j Hj. specialize (BS j Hj). clear - BS X1 X2 XR. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L12510468287.12L12510468412.12L35810605576.12L38817116879.12L42560531743.12L49818960752.1200000<00H00P00\00d010S1A1n1b1w2n1S1A1n1b1w2n0S1A1n2HnS1A1b1w1l2l0S1b1w2HwS1A1n1b2n01l". (* [comment removed for export] *)
#[using="Type"] Lemma apart_of_cs : ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "PP,P,$2.SpPA,$2.Pn,$2.Pb,$2.Pw,$2.P,(16.R5.R4.R3.)P,Px,$2.P,A1.R7.R1.(17.(;.(5.R5.R2.)(<.R2.(6.R5.R4.))))P,(<.=R5.)P,(<.=R4.)(8.(5.(6.R8.R7.)R6.)(5.(6.R6.R5.)R8.))")
(* [comment removed for export] *).
Proof.
  intros P A n b w CR NB Hn Hw. destruct (Z_lt_dec b A).
  - destruct (Z_lt_dec A (b + w)); [| lia]. exfalso. apply (NB A); [apply CR; lia| lia].
  - destruct (Z_lt_dec b (A + n)); [| lia]. exfalso. apply (NB b); [apply CR; lia| lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L38391271824.6L40393003166.6L40393036188.6L51972276493.600000>00L00Z00hS2nb2sn1k2Hk1nS2nb2sn1k2Hk1nS2nb2sn1k2Hk1lS2nb2sn1k2Hk1l". (* [comment removed for export] *)
#[using="Type"] Lemma dblk_app_cases : ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "Pnb,(3.$2.)Psn,(3.$2.)Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.(18.$2.R3.R2.)))))(8.(;.(;.(5.=R2.)(<.R2.(=.(>.$2.R4.))))(19.$2.(?.(18.$2.R4.R3.)R2.)(?.R4.R2.)))(1:.$2.(?.(18.$2.R4.R3.)R2.)R3.))")
(* [comment removed for export] *).
Proof.
  intros nb sn k Hk. unfold dblk. rewrite app_length in Hk. destruct (Z_lt_dec k (Z.of_nat (length nb))).
  - left. rewrite app_nth1 by lia. split; [lia| reflexivity].
  - right. rewrite app_nth2 by lia. apply nth_In. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L60111930915.6L60111963937.6L62297192733.6L65065749905.600000>00L00Z00hS2bl2sb1j2Hj1nS2bl2sb1j2Hj1lS2bl2sb1j2Hj1nS2bl2sb1j2Hj1l". (* [comment removed for export] *)
#[using="Type"] Lemma sblk_app_cases : ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "Pbl,(3.$2.)Psb,(3.$2.)Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.(18.$2.R3.R2.)))))(8.(;.(;.(5.=R2.)(<.R2.(=.(>.$2.R4.))))(19.$2.(10.(18.$2.R4.R3.)R2.)(10.R4.R2.)))(1:.$2.(10.(18.$2.R4.R3.)R2.)R3.))")
(* [comment removed for export] *).
Proof.
  intros bl sb j Hj. unfold sblk. rewrite app_length in Hj. destruct (Z_lt_dec j (Z.of_nat (length bl))).
  - left. rewrite app_nth1 by lia. split; [lia| reflexivity].
  - right. rewrite app_nth2 by lia. apply nth_In. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
#[using="Type"] Lemma crange_mono : forall (P Q : Z -> Prop) A n, crange P A n -> (forall x, P x -> Q x) -> crange Q A n.
Proof. intros P Q A n CR PQ x Hx. apply PQ, CR, Hx. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L21336472346.24L28173504856.24L33291596760.24L55318717784.24L56760563032.24L62226382936.24L63833463896.24000001002003004005006007SSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma allocA_statics_transport2 : ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "PW,(3.$1;.)PWc,(3.$1;.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PT,$2.PCTX,$2.P,(1<.R4.R2.R1.)P,(11.R7.R5.R4.)P,(11.R7.R6.R5.)P,PA,$2.Pn,$2.P,(8.(;.(5.+10000.R2.)(5.(6.R2.R1.)$9.))(;.(5.$:.R2.)(5.(6.R2.R1.)+65?000.)))(1=.R<.R3.R2.)P,(1=.R9.(6.R5.+98.)+8.)(1<.R8.R7.R6.)")
(* [comment removed for export] *).
Proof.
  intros W Wc m m' T CTX S MU MUc DJ DJC. unfold allocA_statics in *.
  unfold A_ASAN_INITED, A_RSS_CELL, A_DEBRUIJN, A_LOGTBL1, A_LOGTBL2, A_MINRZ, A_MAXUSER, A_INSTANCE, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_SS, A_DEP_END in *.
  decompose [and] S. repeat split;
    first [ eapply ro_cells_transport; [eassumption| exact MUc| exact DJC]
          | eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia] ].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L14576631123.16L22558837203.16L28584480211.16L3020354003.16 L40047757011.16L53427412307.16L55320813779.16L63846471379.16L68312912339.16000001002003004005006007008009SSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma fin_statics_transport2 : ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "PW,(3.$1;.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))P,(1>.R2.)P,(11.R4.R3.R2.)P,PA,$2.Pn,$2.P,(8.(;.(5.+10000.R2.)(5.(6.R2.R1.)$9.))(;.(5.$:.R2.)(5.(6.R2.R1.)+65?000.)))(1=.R8.R3.R2.)(1>.R4.)")
(* [comment removed for export] *).
Proof.
  intros W m m' S MU DJ. unfold fin_statics in *.
  unfold A_GOT_LSANTLS, A_LSAN_CNT, A_MAGIC_CELL, A_MHOOKS, A_GOT_FLAGS, A_FLAGS, A_FL_MAXFILL, A_FL_FILLB, A_GOT_RMEMSET, A_RMEMSET, A_MUSL_MEMSET, kAllocBegMagic, A_SS, A_DEP_END in *.
  decompose [and] S. repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L30938057274.29L38467752502.34L39087947745.29L50423199290.29L52419108410.29L68363415354.2900000>00Q00_00m01;01IS2nb2tf2bl3DMLS2nb2tf2bl3DML1i2HiS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DML". (* [comment removed for export] *)
#[using="Type"] Lemma depot_inv_transport : ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "PW,(3.$1;.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PN,$2.Pnb,(3.$2.)Ptf,$2.Pbl,(3.$2.)P,(1?.VhAR,R6.R4.R3.R2.R1.)P,(11.R8.R7.R6.)P,(20.$21.R8.R7.)P,PA,$2.Pn,$2.P,(;.(5.+10000.R2.)(5.(6.R2.R1.)+65?000.))(1=.R=.R3.R2.)P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R8.))))(1=.R=.(?.R9.R2.)(7.+2.+14.))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R7.))))(1=.R>.(10.R8.R2.)(7.+2.+17.))(1?.VhAR,R;.R:.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros W m m' N nb tf bl DI MU WM LO DN DS.
  ddestruct DI as (NC & DT & DM & DNO & WF & MX & (alloc & SSX) & DB & SB & TF0 & BL & BA).
  dpose DM as (DM1 & DMF & DML).
  split. { eapply rw_cells_transport; [exact NC| exact MU| exact WM| apply LO; unfold A_DEP_N; cbn; lia]. }
  split. { eapply (dtab_transport _ m m' N DT MU WM). apply LO. unfold A_DEP; lia. }
  split. { eapply (dmap1_transport _ m m' nb DM MU WM). apply LO. unfold A_DEP_MAP1; lia. }
  split. { eapply (dnodes_transport _ m m' nb N DNO MU WM DMF). intros b Hb.
           ddestruct (In_nth nb b 0 Hb) as (i & Hi & E). specialize (DN (Z.of_nat i) ltac:(lia)). unfold dblk in DN. rewrite Nat2Z.id, E in DN. exact DN. }
  split; [exact WF|].
  split. { eapply rw_cells_transport; [exact MX| exact MU| exact WM| apply LO; unfold A_DEP_NODES; cbn; lia]. }
  split. { exists alloc. eapply rw_cells_transport; [exact SSX| exact MU| exact WM| apply LO; unfold A_SS; cbn; lia]. }
  split. { eapply (dblocks_transport _ m m' bl DB MU WM). apply LO. unfold A_SS; lia. }
  split. { eapply (sblks_transport _ m m' bl SB MU WM). exact DS. }
  split; [exact TF0|]. split; [exact BL| exact BA].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section MallocTop.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CSf : list Z -> list Z -> Z -> Prop.
  Variable K : list Z -> list Z -> Model -> Prop.
  Hypothesis CSOKf : forall nb bl, cs_ok AL (CSf nb bl).
  Hypothesis KL : forall nb bl, kinv AL (CSf nb bl) (K nb bl).
  Hypothesis CSmono_n : forall nb bl a x, CSf nb bl x -> CSf (nb ++ [a]) bl x.
  Hypothesis CSmono_s : forall nb bl a x, CSf nb bl x -> CSf nb (bl ++ [a]) x.
  Hypothesis K_apart : ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "Pnb,(3.$2.)Pbl,(3.$2.)Pmo,$22.Pa,(0.&40.)Pn,(0.&40.)P,A3.VK,R5.R4.R3.P,(19.$23.(24.(18.(13.(0.&40.)(0.&40.))(25.(26.R4.))(27.(26.R4.)))R3.R2.)$28.)P,(5.+10000.(29.&40.R3.))P,(5.(6.(29.&40.R5.)(29.&40.R4.))(2:.VhAR,))Px,$2.P,(8.A3.VCSf,R:.R9.R1.(;.(5.(2;.VAL,)R1.)(<.R1.(2<.VAL,))))(17.(;.(5.(29.&40.R8.)R2.)(<.R2.(6.(29.&40.R8.)(29.&40.R7.)))))")
(* [comment removed for export] *).
  Variables (Gn Gs : list Z -> list Z -> Prop).   (* [comment removed for export] *)
  Hypothesis T_node : ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "Pnb,(3.$2.)Pbl,(3.$2.)Pmo,$22.Pa,(0.&40.)P,A2.VGn,R4.R3.P,A3.VK,R5.R4.R3.P,(19.$2.(2=.(29.&40.R3.)+1000.)=)P,(<.=(29.&40.R4.))P,(5.(6.(29.&40.R5.)(7.+2.+14.))(2:.VhAR,))P,(19.$23.(24.(18.(13.(0.&40.)(0.&40.))(25.(26.R7.))(27.(26.R7.)))R6.(2>.&40.(7.+2.+14.)))$28.)(;.A3.VK,(18.$2.R:.(12.$2.(29.&40.R7.)(15.$2.)))R9.(2?.+22.R7.(7.+2.+14.)R8.)(16.A2.VCSf,(18.$2.R:.(12.$2.(29.&40.R7.)(15.$2.)))R9.(29.&40.R7.)(7.+2.+14.)))")
(* [comment removed for export] *).
  Hypothesis T_store : ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "Pnb,(3.$2.)Pbl,(3.$2.)Pmo,$22.Pa,(0.&40.)P,A2.VGs,R4.R3.P,A3.VK,R5.R4.R3.P,(19.$2.(2=.(29.&40.R3.)+1000.)=)P,(<.=(29.&40.R4.))P,(5.(6.(29.&40.R5.)(7.+2.+17.))(2:.VhAR,))P,(19.$23.(24.(18.(13.(0.&40.)(0.&40.))(25.(26.R7.))(27.(26.R7.)))R6.(2>.&40.(7.+2.+17.)))$28.)(;.A3.VK,R:.(18.$2.R9.(12.$2.(29.&40.R7.)(15.$2.)))(2?.+4022.R7.(7.+2.+17.)R8.)(16.A2.VCSf,R:.(18.$2.R9.(12.$2.(29.&40.R7.)(15.$2.)))(29.&40.R7.)(7.+2.+17.)))")
(* [comment removed for export] *).
  Hypothesis ROOM_n : forall nb bl mo, Gn nb bl -> K nb bl mo -> exists a, anon_grantable 0x22 (2^20) mo a.
  Hypothesis ROOM_s : forall nb bl mo, Gs nb bl -> K nb bl mo -> exists a, anon_grantable 0x4022 (2^23) mo a.
  Hypothesis CSf_noshadow : forall nb bl x, CSf nb bl x -> ~ (0x7fff8000 <= x < 0x10007fff8000).
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  Variables (SP n lo T CTX TOP TID SB cnt csz : Z) (pw : word).
  Let STK := SP + -2128.
  Let SPA := SP + -2128 + -16.
  Let c := class_of (needed2 n).
  Let AB := SB + c * 2^32 + 16 * (bv_unsigned pw mod 2^32).
  Let UB := AB + rz_size n.
  Let CHB := AB + rz_size n + -16.
  Let SUB := 0x7fff8000 + UB / 8.
  Let PGS := 0x7fff8000 + Z.shiftr (UB + nfix n / 8 * 8) 3.
  Let KF := Z.min (nfix n) 4096.
  Hypothesis NB : 0 <= n < 2^32.
  Hypothesis FP : from_primary n = true.
  Hypothesis LOIMG : ACEIL <= lo.
  Hypothesis SPL : lo <= SP - 4096.
  Hypothesis SPA16 : SP mod 16 = 0.
  Hypothesis TOP0 : 2^23 <= TOP. Hypothesis TOP1 : TOP <= 2^47. Hypothesis TOP2 : SP + 16 <= 2^47.   (* [comment removed for export] *)
  Hypothesis T0 : Timg T. Hypothesis T1 : T + 4096 <= ACEIL. Hypothesis TAL : T mod 4096 = 0.
  Hypothesis CX0 : 0x65f000 <= CTX. Hypothesis CX1 : CTX + 0x10000 <= ACEIL.
  Hypothesis TC : T + 4096 <= CTX \/ CTX + 0x10000 <= T.
  Hypothesis TIDB : 0 <= TID < 2^31.
  Hypothesis SB0 : 0 <= SB. Hypothesis SB1 : SB + 2^37 < 2^47. Hypothesis SBAL : SB mod 4096 = 0.
  Hypothesis HCNT : 1 <= cnt <= 16. Hypothesis HCSZ : 0 <= csz < 2^64.
  Hypothesis AB0 : 0x65f000 <= AB. Hypothesis AB1 : AB + needed2 n <= ACEIL.
  Hypothesis ABT : AB + needed2 n <= T \/ T + 4096 <= AB.
  Hypothesis ABC : AB + needed2 n <= CTX \/ CTX + 0x10000 <= AB.
  Hypothesis RNG : AB + needed2 n <= 0x7fff8000 \/ 0x10007fff8000 <= AB.
  Hypothesis TNS : T + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= T.
  Hypothesis CTXNS : CTX + 0x10000 <= 0x7fff8000 \/ 0x10007fff8000 <= CTX.
  (* [comment removed for export] *)
  Variables (LO TOPU d : Z).
  Hypothesis LOB : LO <= SP.
  Hypothesis TOPUB : TOP <= TOPU <= 2^64.

  (* [comment removed for export] *)
  Definition mkeep (m m' : mem) (nb bl : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "Px,(0.&40.)Za,$2.(29.&40.R1.)P,(17.(;.(5.Vlo,R1.)(<.R1.VSP,)))P,(17.(;.(5.$9.R2.)(<.R2.$:.)))P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.O2.))))(17.(;.(5.(?.O2.R2.)R5.)(<.R5.(6.(?.O2.R2.)(7.+2.+14.)))))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.O1.))))(17.(;.(5.(10.O1.R2.)R6.)(<.R6.(6.(10.O1.R2.)(7.+2.+17.)))))P,(17.(;.(5.(6.(6.VT,+=0.)(30.+50.Vc,))R5.)(<.R5.(6.(6.(6.VT,+=0.)(30.+50.Vc,))+4.))))P,(17.(;.(5.(6.VT,+:>0.)R6.)(<.R6.(6.VT,+:>8.))))P,(17.(;.(5.(6.VT,+:?0.)R7.)(<.R7.(6.VT,+<61.))))P,(17.(;.(5.VCHB,R8.)(<.R8.(6.VCHB,+10.))))P,(17.(;.(5.VAB,R9.)(<.R9.(6.VAB,+10.))))P,(17.(;.(5.VSUB,R:.)(<.R:.(6.VSUB,(31.(32.Vn,)+8.)))))P,(17.(;.(5.VPGS,R;.)(<.R;.(6.VPGS,+1.))))P,(17.(;.(5.VUB,R<.)(<.R<.(6.VUB,VKF,))))(19.(1.(0.&8.))A1.O3.R>.A1.O4.R>.)")
(* [comment removed for export] *).

  Definition mtop_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (N tf : Z) (nb bl : list Z) (mx : word) (ws16 : list word) (pgb : byte) (m0 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "Lcf,$33.(34.$35.Lms',$35.(34.$22.Lmo',$22.(34.(3.$2.)Lnb',(3.$2.)(34.(3.$2.)Lbl',(3.$2.)(34.$2.LN',$2.(34.$2.Ltf',$2.(34.$2.Lid,$2.(34.(0.&40.)Lt0,(0.&40.)(34.(0.&40.)Lt1,(0.&40.)(34.(0.&40.)Lt2,(0.&40.)(34.(0.&40.)La1,(0.&40.)(34.(0.&40.)La2,(0.&40.)(34.(0.&40.)La3,(0.&40.)(34.(0.&40.)La4,(0.&40.)(34.(0.&40.)La5,(0.&40.)(34.(0.&40.)La6,(0.&40.)(34.(0.&40.)La7,(0.&40.)(34.(0.&40.)Lt3,(0.&40.)(34.(0.&40.)Lt4,(0.&40.)(34.(0.&40.)Lt5,(0.&40.)(34.(0.&40.)Lt6,(0.&40.)(34.$2.Lb1',$2.(34.(0.&40.)Lstw,(0.&40.)(34.(0.&40.)Lj0,(0.&40.)(34.(0.&40.)Lj1,(0.&40.)(34.(0.&40.)Lj2,(0.&40.)(34.(3.(0.&40.))Lbs,(3.(0.&40.))(34.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(;.(19.$33.R1=.(36.R1<.R1;.))(;.(19.$35.R1<.(37.(38.O18.(2>.&40.VSP,)O17.(2>.&40.$39.)R15.R14.R13.O16.O15.(2>.&40.VUB,)R12.R11.R10.R?.R>.R=.R<.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R;.R:.R9.R8.)O:.(3:.O18.)O9.(3;.(0.&40.))R1.(3<.$21.)))(;.A3.VK,R1:.R19.R1;.(;.(3=.R1.R1;.)(;.(1?.VhAR,R1.R18.R1:.R17.R19.)(;.(3>.A2.VCSf,R1:.R19.R1:.R19.)(;.(3?.R1.)(;.(;.(5.+1.R16.)(5.R16.R18.))(;.(;.(5.O8.R18.)(5.R18.(6.O8.+1.)))(;.(;.(5.O7.R17.)(5.R17.(6.O7.(30.+2.(6.Vd,+3.)))))(;.(5.(40.R17.(30.+1?.(31.R17.(7.+2.+14.))))(6.(40.O7.(30.+1?.(31.O7.(7.+2.+14.))))(6.Vd,+3.)))(;.Px,$2.P,A3.VCSf,O6.O5.R1.A3.VCSf,R1<.R1;.R2.(;.(34.(3.$2.)Lsn,(3.$2.)(34.(3.$2.)Lsb,(3.$2.)(;.(19.(3.$2.)R1<.(18.$2.O6.R2.))(;.(19.(3.$2.)R1;.(18.$2.O5.R1.))(;.(41.$2.Lb,$2.Px,$2.P,A3.VCSf,O6.O5.R1.(17.(;.(5.R3.R2.)(<.R2.(6.R3.(7.+2.+14.)))))R2.)(41.$2.Lb,$2.Px,$2.P,A3.VCSf,O6.O5.R1.(17.(;.(5.R3.R2.)(<.R2.(6.R3.(7.+2.+17.)))))R1.))))))(;.(42.O1.R1.R1:.R19.)(;.(20.$21.O1.R1.)(;.(43.$21.R1.)(;.(44.$21.R1.Vlo,VSP,)(;.(45.$21.R1.VCHB,(12.$46.(47.(2>.&8.$48.))(12.$46.(47.(2>.&8.R7.))(12.$46.(49.(2>.&40.=))(12.$46.(4:.(2>.&40.(32.Vn,)))(12.$46.(4;.(2>.&40.(4<.(30.VTID,(7.+2.+20.))R16.)))(15.$46.)))))))(;.(19.$2.(4=.R7.+3.)+1.)(;.(;.(5.=R7.)(<.R7.+100.))(;.P,(<.+10.(4>.Vn,))(45.$21.R2.VAB,(12.$46.(4;.(2>.&40.$4?.))(12.$46.(4;.(2>.&40.VCHB,))(15.$46.))))(;.(45.$21.R1.VSUB,(12.$46.(50.(51.(31.(32.Vn,)+8.))(52.(0.&8.)(2>.&8.=)(51.(31.(32.Vn,)+8.))))(15.$46.)))(;.(45.$21.R1.VPGS,(12.$46.(47.(53.Vn,O2.))(15.$46.)))(;.(45.$21.R1.VUB,(12.$46.(50.(51.VKF,)(52.(0.&8.)(2>.&8.+;>.)(51.VKF,)))(15.$46.)))(;.(45.$21.R1.(6.(6.VT,+=0.)(30.+50.Vc,))(12.$46.(4:.(2>.&40.(40.Vcnt,+1.)))(12.$46.(4:.O4.)(12.$46.(4;.(2>.&40.Vcsz,))(15.$46.)))))(;.(54.$21.R1.(6.(6.(6.VT,+=0.)(30.+50.Vc,))+10.)O3.)(;.(45.$21.R1.(6.VT,+:>0.)(12.$46.(4;.R6.)(15.$46.)))(;.(45.$21.R1.(6.VT,+:?0.)(12.$46.(4;.R5.)(12.$46.(4;.R4.)(12.$46.(4;.R3.)(15.$46.)))))(;.(55.$21.R1.(6.VT,+;60.)R2.)(;.(19.$56.(>.(0.&40.)R2.)#20.)(45.$21.R1.(6.VT,+<60.)(12.$46.(47.(2>.&8.=))(15.$46.)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition segAB_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (CS' : Z -> Prop)
      (mx : word) (ws16 : list word) (b0 : byte) (w8 : word) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "Lms',$35.(34.(0.&40.)Lx5,(0.&40.)(34.(0.&40.)Lx6,(0.&40.)(34.(0.&40.)Lx7,(0.&40.)(34.(0.&40.)Lx12,(0.&40.)(34.(0.&40.)Lx13,(0.&40.)(34.(0.&40.)Lx14,(0.&40.)(34.(0.&40.)Lx15,(0.&40.)(34.(0.&40.)Lx16,(0.&40.)(34.(0.&40.)Lx17,(0.&40.)(34.(0.&40.)Lt3,(0.&40.)(34.(0.&40.)Lt4,(0.&40.)(34.(0.&40.)Lt5,(0.&40.)(34.(0.&40.)Lt6,(0.&40.)(34.$2.Lb1,$2.(34.(0.&40.)Lstw',(0.&40.)(34.(3.(0.&8.))Lfr0,(3.(0.&8.))(34.(3.(0.&8.))Lfr1,(3.(0.&8.))(34.(3.(0.&8.))Lfr2,(3.(0.&8.))(34.(3.(0.&40.))Lws,(3.(0.&40.))(34.$2.Lsize,$2.(34.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(;.(19.$35.R16.(37.(38.(2>.&40.+47>40.)(2>.&40.(6.VSPA,-80.))O15.(2>.&40.$39.)R15.R14.R13.(2>.&40.+1.)(2>.&40.(32.Vn,))(2>.&40.(6.VSTK,+10.))(2>.&40.R2.)R12.R11.R10.R?.R>.R=.(2>.&40.VAB,)(2>.&40.(57.Vn,))(2>.&40.VUB,)(2>.&40.VCHB,)(2>.&40.$58.)(2>.&40.VSTK,)(2>.&40.(30.VTID,(7.+2.+20.)))(2>.&40.(6.VUB,(32.Vn,)))(2>.&40.VT,)(2>.&40.+1.)R<.R;.R:.R9.)O8.(2>.&40.$59.)O7.(3;.(0.&40.))R1.(3<.$21.)))(;.(11.(12.(13.$2.$2.)(14.$2.$2.Vlo,VSP,)(12.(13.$2.$2.)(14.$2.$2.(6.VT,+<60.)(6.VT,+<61.))(12.(13.$2.$2.)(14.$2.$2.(6.(6.VT,+=0.)(30.+50.Vc,))(6.(6.(6.VT,+=0.)(30.+50.Vc,))+4.))(12.(13.$2.$2.)(14.$2.$2.(6.VT,+:>0.)(6.VT,+:>8.))(12.(13.$2.$2.)(14.$2.$2.VCHB,(6.VCHB,+8.))(15.(13.$2.$2.)))))))O1.R1.)(;.(20.$21.O1.R1.)(;.(43.$21.R1.)(;.(45.$21.R1.VCHB,(12.$46.(47.O3.)(12.$46.(47.(2>.&8.R8.))(12.$46.(49.(2>.&40.=))(12.$46.(4:.(2>.&40.(32.Vn,)))(12.$46.(4;.O2.)(15.$46.)))))))(;.(19.$2.(4=.R8.+3.)+1.)(;.(;.(5.=R8.)(<.R8.+100.))(;.(5:.R1.VSPA,R6.+1.(2>.&40.+47:64.)(2>.&40.VSP,)(2>.&40.Vn,)(2>.&40.$5;.)(2>.&40.+1.)(2>.&40.VSTK,)(2>.&40.(6.VSP,-51.))O>.O=.O<.O;.O:.O9.)(;.(45.$21.R1.(6.(6.VT,+=0.)(30.+50.Vc,))(12.$46.(4:.(2>.&40.(40.Vcnt,+1.)))(12.$46.(4:.O5.)(12.$46.(4;.(2>.&40.Vcsz,))(15.$46.)))))(;.(54.$21.R1.(6.(6.(6.VT,+=0.)(30.+50.Vc,))+10.)O4.)(;.(45.$21.R1.(6.VT,+:>0.)(12.$46.(4;.R7.)(15.$46.)))(;.(45.$21.R1.(6.VT,+<60.)(12.$46.(47.(2>.&8.=))(15.$46.)))(;.(45.$21.R1.(6.VSP,-38.)(12.$46.(4;.O?.)(12.$46.(4;.O10.)(12.$46.(4;.O11.)(12.$46.(4;.O12.)(12.$46.(4;.O13.)(12.$46.(4;.O14.)(12.$46.(4;.O16.)(15.$46.)))))))))(;.(45.$21.R1.VSTK,(12.$46.(4;.(2>.&40.(6.VSTK,+10.)))(12.$46.(4;.(2>.&40.R2.))(15.$46.))))(;.(55.$21.R1.(6.VSTK,+10.)R3.)(;.(19.$56.(>.(0.&40.)R3.)#1>.)(;.(;.(5.+1.R2.)(5.R2.+1>.))(;.(5.R2.(6.Vd,+2.))(;.(45.$21.R1.(6.VSTK,+100.)(12.$46.(50.#708.R5.)(15.$46.)))(;.(45.$21.R1.(6.VSTK,+808.)(12.$46.(4;.(2>.&40.VSP,))(15.$46.)))(;.(45.$21.R1.(6.VSTK,+810.)(12.$46.(50.#8.R4.)(15.$46.)))(;.(45.$21.R1.(6.VSTK,-10.)(12.$46.(4;.(2>.&40.VSP,))(12.$46.(4;.(2>.&40.+6978<.))(15.$46.))))(44.$21.R1.Vlo,(6.VSPA,-80.)))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition segCC_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (id b1 : Z) (pgb : byte) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "Lms',$35.(34.(0.&40.)Lt0,(0.&40.)(34.(0.&40.)Lt1,(0.&40.)(34.(0.&40.)Lt2,(0.&40.)(34.(0.&40.)La1,(0.&40.)(34.(0.&40.)La2,(0.&40.)(34.(0.&40.)La3,(0.&40.)(34.(0.&40.)La4,(0.&40.)(34.(0.&40.)La5,(0.&40.)(34.(0.&40.)La6,(0.&40.)(34.(0.&40.)La7,(0.&40.)(34.(0.&40.)Lt3,(0.&40.)(34.(0.&40.)Lt4,(0.&40.)(34.(0.&40.)Lt5,(0.&40.)(34.(0.&40.)Lt6,(0.&40.)(34.(0.&40.)Lj0,(0.&40.)(34.(0.&40.)Lj1,(0.&40.)(34.(0.&40.)Lj2,(0.&40.)(34.(3.(0.&40.))Lbs,(3.(0.&40.))(34.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(;.(19.$35.R14.(37.(38.O14.(2>.&40.VSP,)O13.(2>.&40.$39.)R13.R12.R11.O12.O11.(2>.&40.VUB,)R10.R?.R>.R=.R<.R;.R:.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.R9.R8.R7.R6.)O6.(3:.O14.)O5.(3;.(0.&40.))R1.(3<.$21.)))(;.(11.(12.(13.$2.$2.)(14.$2.$2.Vlo,VSP,)(12.(13.$2.$2.)(14.$2.$2.VCHB,(6.VCHB,+10.))(12.(13.$2.$2.)(14.$2.$2.VAB,(6.VAB,+10.))(12.(13.$2.$2.)(14.$2.$2.VSUB,(6.VSUB,(31.(32.Vn,)+8.)))(12.(13.$2.$2.)(14.$2.$2.VPGS,(6.VPGS,+1.))(12.(13.$2.$2.)(14.$2.$2.(6.VT,+:?0.)(6.VT,+<60.))(12.(13.$2.$2.)(14.$2.$2.VUB,(6.VUB,VKF,))(15.(13.$2.$2.)))))))))O1.R1.)(;.(20.$21.O1.R1.)(;.(43.$21.R1.)(;.(45.$21.R1.VCHB,(12.$46.(47.(2>.&8.$48.))(12.$46.(47.(2>.&8.(4=.O3.+?3.)))(12.$46.(49.(2>.&40.=))(12.$46.(4:.(2>.&40.(32.Vn,)))(12.$46.(4;.(2>.&40.(4<.(30.VTID,(7.+2.+20.))O4.)))(15.$46.)))))))(;.P,(<.+10.(4>.Vn,))(45.$21.R2.VAB,(12.$46.(4;.(2>.&40.$4?.))(12.$46.(4;.(2>.&40.VCHB,))(15.$46.))))(;.(45.$21.R1.VSUB,(12.$46.(50.(51.(31.(32.Vn,)+8.))(52.(0.&8.)(2>.&8.=)(51.(31.(32.Vn,)+8.))))(15.$46.)))(;.(45.$21.R1.VPGS,(12.$46.(47.(53.Vn,O2.))(15.$46.)))(;.(45.$21.R1.(6.VT,+:?0.)(12.$46.(4;.R5.)(12.$46.(4;.R4.)(12.$46.(4;.R3.)(15.$46.)))))(;.(55.$21.R1.(6.VT,+;60.)R2.)(;.(19.$56.(>.(0.&40.)R2.)#20.)(;.(45.$21.R1.VUB,(12.$46.(50.(51.VKF,)(52.(0.&8.)(2>.&8.+;>.)(51.VKF,)))(15.$46.)))(44.$21.R1.Vlo,VSP,))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "04`0@L10067488504.15 L10166131045.11 L10184698968.7  L10298762028.6  L10432845006.19 L11371687879.9  L12174020959.13 L12312996686.15 L12313239769.7  L12314936157.4  L12522026373.1  L12612756728.15 L12667050709.19 L12673339327.25 L13178357403.3  L13517127406.5  L13579960363.24 L13658889335.10 L14125296670.5  L1483834644.3   L15102277312.2  L15508334621.1  L16085917475.9  L16121740397.8  L1637893174.1   L16861361330.2  L16924645992.1  L16941726106.2  L16953760212.0  L17120848823.0  L17617975394.5  L17681108189.13 L17702421713.323L18100411007.1  L18302958969.1  L18953470697.5  L19013267669.16 L19032820896.7  L19723288167.7  L19935419217.13 L2016213390.6   L2022960349.1   L2031783603.1   L20352426335.4  L20515605447.9  L20569364719.19 L20569364719.20 L20575397333.22 L20575653253.25 L20610289741.22 L20703260783.15 L20703260783.17 L20709543253.21 L20879028953.14 L21620292829.14 L21837150928.7  L2189761147.7   L22013886778.7  L22845783647.13 L23121257776.16 L23200727809.7  L23343287261.0  L23591891289.1  L2426953944.24  L24371011332.20 L24554346056.25 L24554356248.21 L24560632610.15 L24560632610.19 L24661954803.9  L24888640584.236L24888640626.2  L25705851087.2  L25762269614.19 L25783062314.22 L25783330682.25 L25982463935.15 L25984553605.21 L25984564570.8  L26250242907.21 L26394404329.14 L26443528976.24 L26498427253.14 L26875580408.11 L27697017043.4  L27848808849.2  L28352845277.13 L28573892092.8  L28762839709.0  L28807883413.11 L28980904646.24 L2978961816.0   L29836529785.1  L30339995769.1  L30435077518.8  L30487501431.17 L30573236684.7  L30628028653.16 L30633099225.1  L30787585704.1  L31213588927.16 L31919753266.25 L31920021602.22 L32447096858.1  L32952788708.21 L33092297043.21 L33237847169.4  L33437887829.15 L33437887829.17 L33444171887.21 L33620938677.15 L33708843013.9  L33722663298.13 L33722663298.14 L33903360202.7  L33945784403.3  L34239203029.7  L34301889471.12 L34303987253.14 L34477649339.16 L35151535643.15 L35247679960.20 L35688020061.14 L36013130575.13 L36193165570.2  L36415714444.285L36747432620.19 L37099247901.5  L37181991793.19 L37181991793.20 L37184093723.25 L37253898247.15 L37396631557.0  L37637199976.0  L37806260371.11 L37880534170.24 L38235734261.1  L38411370647.14 L38630860083.8  L38650024428.24 L38700110972.1  L38968734492.7  L39188636933.0  L39220637093.0  L39315242130.2  L39332637397.0  L39398132.15    L39625440799.16 L39651577319.7  L39812883104.8  L39831478948.2  L39922156156.16 L39953279860.6  L39982730872.24 L40186053667.24 L40396832886.235L40507775107.3  L40605191700.4  L41484975808.5  L41532811307.7  L41693098334.15 L42043760438.21 L42150790267.5  L42409219784.3  L4376446781.16  L44072790135.4  L4414829022.19  L44345217427.2  L44716101839.24 L44876607696.284L44880059389.14 L44916467928.8  L45295076406.1  L45334955688.1  L45578113577.24 L45588035969.7  L46071731361.10 L46590136587.22 L46736111460.11 L46798637366.1  L46902177661.2  L47386102014.2  L47539285122.8  L47695029500.5  L48164027662.4  L48191369178.1  L48349372034.13 L48349372034.14 L48364285643.24 L48793009578.2  L48872708136.9  L49303139973.22 L49305488319.20 L50001739424.6  L50604644431.13 L50775210429.5  L50803510888.1  L5101951897.13  L51164003032.19 L51170291634.25 L51362018088.1  L51557032766.16 L51765344620.1  L51802805993.24 L52286288041.21 L52310674614.1  L52409438585.16 L52566565077.19 L52566565077.20 L52635831073.0  L52672460549.16 L52694201704.1  L52786865963.19 L52786865963.20 L53574104168.1  L54508837114.2  L54543288399.14 L54641519825.5  L55291269785.13 L55296199685.24 L55400759076.14 L55588686165.0  L55899845783.3  L5600130087.15  L56294960569.9  L56376963496.1  L56750996366.2  L56827281061.15 L56827281061.17 L56829363103.21 L57056911013.7  L57274486538.19 L57368301315.17 L57545127939.10 L57628700040.11 L57841731802.3  L57924165753.1  L58086072525.7  L58339951995.21 L58535452555.16 L58633210367.5  L58850337862.14 L58852434380.12 L5916318900.0   L59170280814.5  L60108165195.235L60204643024.6  L60742259251.14 L60951736609.3  L61030858054.299L61035084364.212L61035084364.214L61035084364.228L61035084364.230L61323045984.7  L61323110347.9  L62209427327.1  L62243755231.14 L6286992857.14  L63202193422.3  L63330810425.7  L63368316718.213L63368316718.215L63368316718.229L63368316718.231L63374621462.300L63443763453.14 L63737759283.1  L63897450449.5  L647770090.14   L64838801051.1  L6502693056.4   L6507294813.1   L65843502758.3  L65843502758.4  L66401606425.22 L6644560746.3   L66567258875.6  L66577255403.16 L66763458562.8  L66767552517.15 L67040294811.16 L67108790937.14 L67367103066.24 L67509844005.16 L6757205483.2   L67645412170.5  L67649359651.14 L67680528389.1  L68545323609.1  L68592373110.21 L6863246781.9   L6878027143.8   L7799702881.1   L8042593858.19  L8168648040.1   L8265267294.0   L8806423751.11  L8806423751.8   L8912407864.8   L8929606249.11  L9648528327.3   L9714519104.7   L984703108.14   00000G00c01101C02002F02P02k03703@03D03`04H05G05O05d06Z07007>07F07M07R07m08J08N08W08Z08`08a08b09709S0;90;=0;@0;J0;h0<?0<R0=60=G0=K0=O0=X0>80>\0?G0@:0@`0AD0AW0B:0Bh0CI0Ce0D=0DS0Db0Dl0EV0El0Em0F10Fg0Gc0H\0IE0I_0JF0J]0Ke0Ki0L00LP0M;0N60NI0O70OH0P90PS0QI0Q^0R<0RK0RR0Rn0SD0SE0S_0TU0TV0TY0T\0U70UK0UY0V90V=0VA0Vd0W_0XJ0XN0Xm0Y^0Yg0ZC0Zn0[_0\00\F0\_0]B0]Z0]e0^80^Q0_30_Q0`;0`f0aK0aU0aX0cj0dR0d`0eH0f70g20gH0gI0gJ0gi0hd0hh0iM0ib0jZ0j^0k00k10k20k80k90kW0l:0lR0ll0m60mN0me0n`0oV11`11m12712J12V13113b14014714W14c15F15M16E18W19819U19Y19]1:X1:n1;<1;h1<C1<G1<O1<X1=41=<1=F1=I1=b1>E1?@1?G1?^1@Y1AH1AY1Ac1An1B11B@1Bc1Cb1Cf1D>1DB1E=1Eo1F31FV1GC1H71H81HV1HY1IB1J21J61J=1JG1JZ1Ji1K_1L>1L?1LF1Ld1M;1M?1MC1M[1NC1O41OJ1Oc1PO1Pe1QD1QN1QQ1Qh1RY1Ri1S01SD1SS1ST1S[1Ue1V71V\1Vg1X>1YJ1ZV1[b1\n1]E1]\1]`1^91^Z1^b1_11`=1aI1bU1ca1e81eY1e]1ei1fH1fN1fX1f\1fd1fn1ge1h01hE1hc1i11iB1i`1io1jj1kH1kO1kX1l=1lA1lE1m:1mU1n01n51n]1n`1na1o@1oV1oh20C20M20`21JS3hAR1n2SB2pw2CR3Hrz2RCS3hAR1n1T2SB2pw3ABT3N2B4RZSBS1n2SB2pw1c2ABS1n2SB2pw1c2AB3AB0S3hAR2SP1n2lo2SB2pw3SUB3PGS5LOIMG3AB13N2E3NDBS1n2SB2pw1c2AB2KF4N2B'S3hAR1T2pwS3hAR1n1T2SB2pw3ABT3N2B3HrzS3hAR1n1T2CRS2SP4TOP2S2SPS3hAR2SP2lo3CTX2pw5LOIMG3CX1S3hAR1n2SB2pw1c2AB2KF3AB04RZSB3NFB1A1k1HS3hAR1n1T2SB2pw1c2AB3SUB3PGS2KF3ABT4RZSB3NFB4N2B'3KFB1A1k2Ha2HbS1n1T2CRS3hAR2SP2lo5LOIMG3SPLS3hAR1n2SB2pw1c2AB3SUB3PGS2KF4RZSB3nb'3NFB3KFB1k2Y42Y5S3bl'1j1A1w2H12H22n11lS3hAR2lo5LOIMGS1n1T2CRS1n3NFBS3CTXS3hAR1n2SB2pw1c2AB3AB14ASHES3hAR2SP2lo5LOIMG3SPL3nb'1k1HS2SPS3CTX3CX0S1TS1T2T0SSS3hAR2SP2lo5LOIMG3SPLS3hAR1n1T2SB2pw3ABT3N2B4RZSBS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3SB02tf4ws162bs3LWS2HL3ASH2ws4HL303tf'1A2sz2A'1k1H2H0S2SPS1TS3hAR1T2T0S3hAR1n1T2pw2bl1j4APTs2CR4RZSBS1n2SB2pw1c2AB3AB04ASHES2SP2lo1T1A1k2H12H2S3hAR1n2lo2SB2pw1c2AB5LOIMG3AB14ASHES1n2SB2pw1c2AB2RCS2SPS2SPS2SP4TOP2S1n2SB2pw1c2AB3AB04RZSB4ASHE3NFBS3hAR1n1T2SB2pw1c2AB2KF2T03NFB1A1k1HS3hAR2SP1n1T2SB2pw3SPA1c2AB2KF2T03NFB1A1k1HS3hAR2SP1n2lo1T2SB2pw3SUB3PGS2KF5LOIMG3SPL2T11A1k1HS3hAR1n1T2SB2pw1c2AB3SUB3PGS2KF1A1k2HbS3hAR2SP1n2lo2SB2pw3SUB3PGS2KF1A1k1HS3hAR1T2pw2T01A1k1HS3hAR2SP2lo1T2pw5LOIMG3SPL2T11A1k1HS3hAR1n1T2SB2pw3AB03AB13RNG3TNS4ASHE1A1k2H12H2S3hAR1n1T2SB2pw1c2AB3ABT3N2B4RZSBS3hAR1n1T2SB2pw3ABT3N2B4RZSBS3hAR1n2lo1T5LOIMG2T12CRS3hAR2lo3CTX5LOIMG3CX1S3bl'1j1A2n02n2S3hAR1T2pwS3hAR2SP1n2lo1T2SB2pw2KF5LOIMG2T13AB14N2B'S3hAR2lo3CTX5LOIMG3CX1SS2SPS3hAR1n2SB2pw1c2AB3SUB3PGS2KF4RZSB3bl'3NFB3KFB1j2Y42Y5S3hAR1n2lo1T2SB2pw1c2AB5LOIMG3AB03AB13RNG3TNS4ASHE1A1k2H12H2S3hAR2SP1n2lo1T2SB2pw1c2AB3SUB3PGS2KF5LOIMG2T13NFB1A1k2HbS3hAR2SP1n2lo2SB2pw5LOIMG3AB14ASHE1A1k2H2S3hAR2SP2lo2pw5LOIMG1A1k1HS3hAR2SP1n2lo2SB2pw1c2AB2KF5LOIMG1A1k1HS1n2SB2pw1c2AB3ASH4DIV8S3hAR2SP1n1T2SB2pw3SPA1c2AB2UB3CHB3SUB3PGS2KF3SB04ws162bs3LWS2HL2ws4HL30S2SPS1n3NFBS3hAR1n2SB2pw3SUB3PGS3NFB3Hrz2RCS3hAR2SP1n2lo2SB2pw3SUB3PGS2KF3SPL1A1k1H2X1S3hAR1n1T2SB2pw1c2AB3SUB3PGS2KF4RZSB3NFB3KFB4X1''1A1k2Ha2HbS3hAR1T2pw2T01A1k1HS3hAR1n1T2SB2pw3AB03AB13RNG3TNS4ASHE1A1k2H12H2S3hAR1T2T01A1k2HkS3hAR1n1T2SB2pw1c2AB3SUB3PGS2KF4RZSB3NFB3KFB4X2''S3hAR1n2SB2pw1c2AB2KF4RZSBS3hAR1n2SB2pw1c2AB3SUB3PGS2KF4RZSB3bl'3NFB3KFB1j2Y32Y5S3hAR1n2SB2pw1c2AB2KFS3hAR1n2lo2SB2pw5LOIMG3AB13N2BS1n3FP'3N2E3NDBS2SP2loS3hAR1n1T2SB2pw3ABT3N2B4RZSBS2SP1n2lo1T2SB2pw1x2HxSS3hAR1n2SB2pw1c2AB3N2E3NDBS3hAR2SP1n2lo2SB2pw1c2AB3SUB3PGS2KF5LOIMG3bl'3NFB1j2Y5SS1TS1TS3hAR2lo1T3CTX5LOIMG2T13CX1S3hAR2SP2lo2pw1A1k1HS3hAR1T3CTX2TCS3hAR1n1T2SB2pw2KF3ABT4RZSB4N2B'S2SPS2SPS3hAR1n1T2SB2pw2KF3ABT2CR4RZSB4N2B'S3hAR1n1T2SB2pw1c2AB3SUB3PGS2KF4RZSB3NFB3KFB4X2''1A1k2Ha2HbS3hAR2SP1n2lo2SB2pw3SUB3PGS2KF3SPL1A1k1H2X2S2SPS3hAR1n1T2SB2pw1c2AB3SUB3PGS2KFS3hAR1n1T2SB2pw1c2AB3SUB3PGS2KF4RZSB3NFB3KFB4X1''S2SP4TOP2S3hAR1n2SB2pw3AB04RZSB1A1k1HS3hAR2SP1n2lo2SB2pw5LOIMG3SPL3AB13N2B1A1k1HS3hAR1n2SB2pw3AB13RNG3N2E3NDB4RZSB4ASHE1A1k2H12H2S3hAR1T3CTX2pw2TCS1n2SB2pw1c2AB2KF4RZSBS3hAR2SP2lo1T2pw5LOIMG2T1S3hAR2SP1n2lo1T2SB2pw1c2AB5LOIMG2T1S3hAR1n2lo1T5LOIMG2T12CRS2SP2lo3SPLS3hAR2lo1T5LOIMG2T1S1T2pw1x2H71n2H52H62SB2H8S1n2SB2pw1x2H82H93H103H111T2H73H12S3hAR1n1T2pw2bl1j4APTs2CR4RZSBS3hAR2SP1n2lo1T2SB2pw5LOIMG2T13AB13N2B3HrzS3hAR2SP1n2lo2SB2pw3SPA1c2AB2KF5LOIMG1A1k1HS1n2SB2pw1c2AB2UB3PGS3N2B4RZSB3NFB2X2S3hAR1T2pwS1nS3hAR2SP1n1T3CTX2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3CX02TC3SB03AB03ABT3ABC3RNG3TNS5CTXNS2tf4ws162bs3LWS2HL2ws4HL303N2E3NDB3N2B4RZSB3bl'3tf'1j2HjS3hAR1n2SB2pw3SUB3PGS3N2E3NDB3NFB3Hrz2X2S1n2SB2pw1c2ABS3hAR1n2SB2pw1c2AB2KF3AB04RZSB3NFB1A1k1HS3hAR2SP1n2SB2pw3SPA1c2AB2KF3AB04RZSB3NFB1A1k1HS3hAR1n1T2SB2pw1c2AB3SUB3PGS2KF3ABT4RZSB3NFB4N2B'1A1k2Ha2HbS3hAR1n1T3CTX2pw2TC2CRSSS3hAR1n2lo2SB2pw1c2AB5LOIMG3AB1S3hAR1n2SB2pw1c2AB3SUB3PGS2KF4RZSB3nb'3NFB4N2B'3KFB1k2Y22Y5S2loS1n2SB2pw1c2AB2UB3PGS3N2B4RZSB3NFB2X2S3hAR2lo5LOIMG1A1k2HkS3hAR1n1T2SB2pw1c2AB3SUB3PGS2KF4RZSB3nb'3NFB3KFB1k2Y12Y5S2SPS1n2SB2pw1c2AB3N2BSSS1T2T0SS3hAR1n1T2SB2pw3ABT2CR3N2B3HrzS3hAR1n2SB2pw2bl1j4APAs2CR3N2B4RZSBS1d2tf4size3SZD3tf'4TFB'S1n2SB2pw1c2AB3ASH3N2E3NDBS4size3SZBS3hAR2SP2lo5LOIMG2nb1k1XS1d2tf4size3SZD3tf'3TFPS3hAR1n2SB2pw1c2AB3SUB3PGS2KF4RZSB3bl'3NFB4N2B'3KFB1j2Y22Y5S3hAR1n2SB2pw1c2AB3SUB3PGS2KF4RZSB3nb'3NFB3KFB1k2Y32Y5S3hAR2SP1n1T3CTX2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3CX02TC3SB03AB03ABT3ABC3RNG3TNS5CTXNS2nb4ws162bs3LWS2HL1k2ws4HL303N2E3NDB3N2B4RZSB2HkS3hAR3CTX3CX1S1n1T1c2CRS3hAR2lo1T5LOIMG2T1S3hAR1n1T2CRS3hAR1n1T2SB2pw3ABT3N2B3HrzS3hAR1n1T2SB2pw1c2AB3SUB3PGS2KF3ABT4RZSB3NFB4N2B'S3hAR2lo5LOIMGS1A1k1HS3hAR1n1T2SB2pw2KF3ABT4RZSB4N2B'S2SP2lo1x2H1S3hAR1n1T2SB2pw3SUB3PGS3ABT3N2E3NDBS1n3NFBS3hAR1n1T2SB2pw1c2AB3SUB3PGS2KF4RZSB3bl'3NFB3KFB1j2Y12Y5S3hAR2SP1n1T3CTX2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3CX02TC3SB03AB03ABT3ABC3RNG3TNS5CTXNS2tf4ws162bs3LWS2HL2ws4HL303N2E3NDB3N2B4RZSB3nb'3tf'1k2HkS3hAR1n1T2SB2pw1c2AB3ABT3N2B4RZSBS3hAR2SP2lo5LOIMG3SPL3bl'1j1HS2SPS2SPS3hAR1n2SB2pw1c2AB3SUB3PGS2KF4RZSB3bl'3NFB4N2B'3KFB1j2Y22Y5S3hAR1n2SB2pw1c2AB3AB1S1A1w2H12H22HwS3hAR1n2SB2pw1c2AB2UB3SUB3AB14ASHE4N2B'4SUBES3hAR1n2SB2pw1c2AB3AB14ASHES2SPS2SP3SPAS3CTX3CX0S1n2SB2pw1c2AB3AB04RZSB4ASHES1n4N2B'S1n1T1c2CRS1TS3hAR2SP2lo1T2pw5LOIMG2T1S3hAR2SP1n2lo1T2SB2pw1c2AB5LOIMG2T1S3hAR1n2SB2pw1c2AB3SUB3PGS2KF4RZSB3nb'3NFB4N2B'3KFB1k2Y22Y5S3bl'1jS1n2SB2pw1c2AB3ASH4N2B'S3hAR2SP1n2lo2SB2pw3SUB3PGS2KF5LOIMG3SPL3AB14N2B'3KFB1A1k1HS3hAR2SP1n2SB2pw3SPA1c2AB2KF3AB04RZSB3NFB1A1k1HS1n2SB2pw1c2AB2RCS3hAR1T2pwS1n1H2H02H1S1TS3hAR1n1T2pw2CRS3hAR1n2SB2pw1c2AB2KF3AB03NFB1A1k1HS3hAR1n1T2SB2pw1c2AB3SUB3PGS2KF3ABT4RZSB3NFB4N2B'3KFB1A1k2Ha2HbS2SPS3hAR2SP2lo5LOIMG2bl1j1XS2SPS3hAR1n2SB2pw1c2AB3SUB3PGS2KF4RZSB3bl'3NFB4N2B'3KFB1j2Y22Y5S3hAR2SP1n2lo1T2SB2pw1c2AB3SUB3PGS2KF5LOIMG2T13NFBS2SPS3hAR1n2SB2pw2nb1k4APAn2CR3N2B4RZSBS3hAR1n2SB2pw1c2AB2KF3AB04RZSB4ASHE3NFB1A1k1HS3hAR2SP1n2SB2pw3SPA1c2AB2KF3AB04RZSB4ASHE3NFB1A1k1HSS3hAR1n1T2pw2bl1j4APTs2CR4RZSBS1TS3hAR1n2SB2pw1c2AB2KF3AB04RZSB4ASHE1A1k1HS3hAR2SP1n2SB2pw3SPA1c2AB2KF3AB04RZSB4ASHE1A1k1HS2SPS3nb'1kS3hAR1T2pwS3hAR2lo1T5LOIMG2T1S3hAR1n1T2pw2CRS3hAR2SP1n2lo2SB2pw1c2AB3SUB3PGS2KF5LOIMG3nb'3NFB1k2Y5S2SP1n2lo2SB2pw1c2AB2UB3SUB3X1'SS1A1k1HS3hAR1n3CTX2SB2pw3ABC3N2B4RZSBS1n2SB2pw1c2AB3ASH4N2B'S2SPS2SPS3hAR1n1T2pw2T02CR1A1k1HS3hAR2SP1n2lo1T2pw5LOIMG3SPL2T12CR1A1k1HS3hAR1n1T2SB2pw3AB03AB13RNG3TNS2CR4ASHE1A1k2H12H2S1n2SB2pw1c2AB3N2E3NDBS3hAR1n2SB2pw3SUB3PGS3HrzS3hAR1n2SB2pw1c2AB2UB3PGS3AB14ASHE4N2B'4PGSES3nb'1k1A1w2H12H22n11lS2SP1n2lo1T2SB2pw1c2AB3CHB1x2HxS1n2KF3KFBS1TS1n2SB2pw1c2AB3AB04ASHES3hAR1n1T2SB2pw1c2AB3SUB3PGS2KF3ABT4RZSB4N2B'3KFBS3hAR1n2SB2pw2KFS3hAR1TS2SP1n2lo2SB2pw1x2H1S2SP2lo2pw1x2H1SS3hAR1TS3hAR2SP1n1T3CTX2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3CX02TC3SB03AB03ABT3ABC3RNG3TNS5CTXNS2bl4ws162bs3LWS2HL1j2ws4HL303N2E3NDB3N2B4RZSB2HjS1n2SB2pw1c2AB3AB0S1n2SB2pw1c2AB2UB3SUB3N2B4RZSB3NFB2X1S2SP2lo3SPLS3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3SB02tf4ws162bs3LWS2HL3ASH2ws4HL303tf'S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3SB04ws162bs3LWS2HL2ws4HL30S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3SB04ws162bs3LWS2HL2ws4HL30S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3SB04ws162bs3LWS2HL2ws4HL30S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3SB04ws162bs3LWS2HL2ws4HL30S1n2SB2pw1c2AB3ASH4RZSBS1n2SB2pw1c2AB3ASH4RZSBS2SPS3hAR2SP2lo1T2pw5LOIMG2T1S3hAR1n1T2SB2pw1c2AB3ABT3N2B4RZSBS1n1T2CRS3nb'1k1A2n02n2S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3SB04ws162bs3LWS2HL2ws4HL30S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3SB04ws162bs3LWS2HL2ws4HL30S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3SB04ws162bs3LWS2HL2ws4HL30S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3SB04ws162bs3LWS2HL2ws4HL30S3hAR2SP1n1T2SB2pw3STK3SPA1c2AB2UB3CHB3SUB3PGS2KF3SB02tf4ws162bs3LWS2HL3ASH2ws4HL303tf'S3hAR1n1T2SB2pw1c2AB3ABT3N2B4RZSBS2SPS1n3NFB1H2H0S2SP1n2lo2SB2pw1c2AB2UB3PGS3X2'S4sizeS1n1T1c2CRS2SPS1n1T2CRS1n1T1c2CRS3hAR2SP1n2lo2SB2pw3SUB3PGS2KF5LOIMG3SPL3AB14N2B'1A1k1HS1n3N2E3NDBS1N3NB22N'2id3IDB3NB'S3hAR1n1T2pw2nb1k4APTn2CR4RZSBS3hAR1T3CTX2TCS3hAR1T3CTX2pw2TCS3hAR1n1T2pw2nb1k4APTn2CR4RZSBS3hAR1n1T2pw2CRS3hAR1n2SB2pw1c2AB3SUB3PGS2KF4RZSB3nb'3NFB4N2B'3KFB1k2Y22Y5S3hAR1n1T2pw2nb1k4APTn2CR4RZSBS2SP2loS1n2H02H1S1n2SB2pw1c2AB2UB3SUB3N2B4RZSB3NFB2X1S2SPS2SPS3hAR1n1T2SB2pw1c2AB3SUB3PGS2KF3ABT4RZSB3NFB4N2B'3KFBS1n2SB2pw1c2AB3ASH4RZSB3NFBS1n2SB2pw1c2AB3ASH4RZSB3NFBS3CTXS3hAR1n2SB2pw3SUB3PGS3N2E3NDB3NFB3Hrz2X1S1TSS2SP1n2lo1T2SB2pw1c2AB3CHB1x2HxS2SP1n2lo1T2SB2pw1x2HxS1n2SB2pw1c2AB3ASHS3hAR1n2SB2pw1c2AB3AB04ASHES3hAR1T2T1S1n2SB2pw1c2AB4RZSBS3hAR2SP1n2lo2SB2pw1c2AB2KF5LOIMG3AB14N2B'". (* [comment removed for export] *)
  #[using="AL IMG ALWF CSOKf KL CSmono_n CSmono_s K_apart T_node T_store ROOM_n ROOM_s CSf_noshadow ASB STK SPA NB FP LOIMG SPL SPA16 TOP0 TOP1 TOP2 T0 T1 TAL CX0 CX1 TC TIDB SB0 SB1 SBAL HCNT HCSZ AB0 AB1 ABT ABC RNG TNS CTXNS LOB TOPUB"] Theorem malloc_hit_cfg : ltac2:(CDefT.buildp (gd_tbl_AW_MallocTop ()) "Pra,(0.&40.)Pgp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pmx,(0.&40.)Pstw,(0.&40.)Pw2,(0.&40.)Pw4,(0.&40.)Pw8,(0.&40.)Pj0,(0.&40.)Pj1,(0.&40.)Pj2,(0.&40.)Pmg0,(0.&40.)Pmg1,(0.&40.)Pb0,(0.&8.)Pb1,(0.&8.)Pshb,(0.&8.)Ppgb,(0.&8.)PF,(5<.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$22.PN,$2.Ptf,$2.Pnb,(3.$2.)Pbl,(3.$2.)Pws16,(3.(0.&40.))Pbs,(3.(0.&40.))Psj,(3.(0.&8.))Puj,(3.(0.&8.))P,(5=.$21.R:.VLO,VTOPU,(29.&40.R31.)VSP,Vd,)P,(5>.R;.VT,VCTX,)P,(1<.R<.VT,VCTX,)P,(5?.R=.)P,(1>.R>.)P,(60.$21.R?.$61.(12.$46.(4;.(2>.&40.$62.))(15.$46.)))P,(60.$21.R10.$63.(12.$46.(47.(2>.&8.+1.))(15.$46.)))P,(60.$21.R11.(6.$58.+20.)(12.$46.(4;.(2>.&40.VSB,))(15.$46.)))P,(60.$21.R12.(6.VT,+8.)(12.$46.(4;.(2>.&40.VTOP,))(12.$46.(4;.(2>.&40.(40.VTOP,(7.+2.+17.))))(15.$46.))))P,(60.$21.R13.(6.VT,+28.)(12.$46.(47.(2>.&8.=))(15.$46.)))P,(45.$21.R14.(6.VT,+<60.)(12.$46.(47.(2>.&8.=))(15.$46.)))P,(60.$21.R15.VT,(12.$46.(4;.(2>.&40.VCTX,))(15.$46.)))P,(60.$21.R16.(6.VCTX,+8.)(12.$46.(4:.(2>.&40.VTID,))(15.$46.)))P,(16.A2.VCSf,R13.R12.VT,+1000.)P,(16.A2.VCSf,R14.R13.VCTX,+10000.)P,(19.$56.(>.(0.&40.)R13.)#10.)P,(19.(1.(0.&40.))(64.(0.&40.)R14.(51.(40.Vcnt,+1.)))(65.(0.&40.)Vpw,))P,(45.$21.R1;.(6.(6.VT,+=0.)(30.+50.Vc,))(12.$46.(4:.(2>.&40.Vcnt,))(12.$46.(4:.R2;.)(12.$46.(4;.(2>.&40.Vcsz,))(15.$46.)))))P,(54.$21.R1<.(6.(6.(6.VT,+=0.)(30.+50.Vc,))+10.)R16.)P,(45.$21.R1=.(6.VT,+:>0.)(12.$46.(4;.R2<.)(15.$46.)))P,(45.$21.R1>.(6.VT,+:?0.)(12.$46.(4;.R29.)(12.$46.(4;.R28.)(12.$46.(4;.R27.)(15.$46.)))))P,(55.$21.R1?.(6.VT,+;60.)R18.)P,(19.$56.(>.(0.&40.)R19.)#20.)P,(16.A2.VCSf,R1=.R1<.VAB,(57.Vn,))P,(45.$21.R22.VCHB,(12.$46.(47.R28.)(12.$46.(47.R27.)(12.$46.(49.R30.)(12.$46.(4:.R2?.)(12.$46.(4;.R2>.)(15.$46.)))))))P,P,(<.+10.(4>.Vn,))(45.$21.R24.VAB,(12.$46.(4;.R2<.)(12.$46.(4;.R2;.)(15.$46.))))P,(45.$21.R24.VUB,(12.$46.(50.(51.VKF,)R1;.)(15.$46.)))P,(60.$21.R25.(6.+7???8000.(66.VAB,+3.))(12.$46.(47.R29.)(15.$46.)))P,(17.(19.$2.(29.&8.R2:.)=))P,(45.$21.R27.VSUB,(12.$46.(50.(51.(31.(32.Vn,)+8.))R1?.)(15.$46.)))P,(45.$21.R28.VPGS,(12.$46.(47.R2;.)(15.$46.)))P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R26.))))(8.(5.(6.VT,+1000.)(?.R27.R2.))(5.(6.(?.R27.R2.)(7.+2.+14.))VT,))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R26.))))(8.(5.(6.VT,+1000.)(10.R27.R2.))(5.(6.(10.R27.R2.)(7.+2.+17.))VT,))P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R28.))))(8.(5.(6.VCTX,+10000.)(?.R29.R2.))(5.(6.(?.R29.R2.)(7.+2.+14.))VCTX,))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R28.))))(8.(5.(6.VCTX,+10000.)(10.R29.R2.))(5.(6.(10.R29.R2.)(7.+2.+17.))VCTX,))P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R2:.))))(8.(5.(6.VAB,(57.Vn,))(?.R2;.R2.))(5.(6.(?.R2;.R2.)(7.+2.+14.))VAB,))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R2:.))))(8.(5.(6.VAB,(57.Vn,))(10.R2;.R2.))(5.(6.(10.R2;.R2.)(7.+2.+17.))VAB,))P,(1?.VhAR,R2?.R2=.R2;.R2<.R2:.)P,(3>.A2.VCSf,R2<.R2;.R2<.R2;.)P,(3?.R31.)P,(5.(6.R2?.+80.)(7.+2.+20.))P,(5.(6.R31.+2.)(40.(7.+2.+1?.)(7.+2.+1<.)))P,(44.$21.R34.VSP,VTOP,)P,(16.A2.VCSf,R31.R30.VSP,(40.VTOP,VSP,))P,(44.$21.R36.Vlo,VSP,)P,(16.A2.VCSf,R33.R32.Vlo,(40.VSP,Vlo,))P,(43.$21.R38.)P,A3.VK,R35.R34.R38.P,(3=.R3:.R39.)P,A2.VGn,R37.R36.P,A2.VGs,R38.R37.P,Px,$2.A2.VGs,(18.$2.R3:.(12.$2.R1.(15.$2.)))R39.(67.$21.(68.R6:.R69.R65.R64.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R40.R3?.R3<.R3;.R3:.R39.R4>.R38.R41.R3>.)(36.(37.(38.R6:.(2>.&40.VSP,)R69.(2>.&40.$39.)R68.R67.R66.R65.R64.(2>.&40.Vn,)R63.R62.R61.R60.R5?.R5>.R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.)R40.(2>.&40.$69.)R3?.(3;.(0.&40.))R3>.(3<.$21.))R3=.))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mx stw w2 w4 w8 j0 j1 j2 mg0 mg1
      b0 b1 shb pgb F fc m mo N tf nb bl ws16 bs sj uj
      CH0 MS8 AS PS FS GOTFL PPART SBC THR TSW UNW TH TIDC TCS CTXCS LWS NTH PC ARR STC STH STB HL ACS HDR MG UC SHC SHB SH PGC
      APTn APTs APCn APCs APAn APAs DI DCS DST TFMAX NB2 STT STCS ST SCS MI HK HJ GN GS GSX.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ CH0) as D0.
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf nb bl) (K nb bl) (segAB_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (CSf nb bl) mx ws16 b0 w8 m) _ _ mo (KL nb bl) HK); [exact HJ| |].
    {
      eapply evtA_cut.
      { eapply (msegA AL IMG ALWF (CSf nb bl) (CSOKf nb bl)); try eassumption. }
      cbn beta. (intros ms1 dd_H; ddestruct dd_H as (y0 & y1 & y2 & y6 & y7 & y3 & y4 & y5 & y6' & m1 & ws & size & fr1 & fr2 & -> &
                            MU1 & WM1 & MI1 & FR7 & STKC & HTR & HL30 & SZB & SZD & F1800 & TFBP & F8 & AFR & UNW1 & ST1 & SR1)).
      (* [comment removed for export] *)
      assert (DJ1 : forall A k, A + k <= lo -> (A + k <= T + 3168 \/ T + 3169 <= A) -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k)
        by (intros A k H1 H2; cbn [disjoint_from]; clear - H1 H2; lia).
      pose proof FP as FP'. unfold from_primary, kMaxSize in FP'. apply Z.leb_le in FP'.
      assert (N2E : needed2 n = needed n) by (unfold needed2; rewrite FP; reflexivity).
      assert (NDB : 24 <= needed n).
      { unfold needed, rounded, round_up. pose proof (rz_size_bound n). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). clear - H H0 H1 NB. lia. }
      pose proof (class_of_range (needed2 n) ltac:(clear - NDB N2E FP'; lia)) as CR. fold c in CR.
      assert (N2B : rz_size n + 8 <= needed2 n).
      { rewrite N2E. unfold needed, rounded, round_up. pose proof (rz_size_bound n). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). clear - H H0 H1 NB. lia. }
      eapply evtA_mono.
      { eapply (msegB AL IMG ALWF (CSf nb bl) (CSOKf nb bl) SP n lo T CTX TID SB cnt csz pw) with (size := size) (mx := mx) (stw := stw); try eassumption.
        - eapply (allocA_statics_transport _ m m1 T CTX AS MU1). { intros A k Hk. apply DJ1; cbn; clear - Hk LOIMG T0; lia. } apply DJ1; cbn; clear - LOIMG T1 CX1 TC; lia.
        - clear - SZB. lia.
        - eapply ro_cells_transport; [exact SBC| exact MU1| apply DJ1; unfold A_INSTANCE; cbn; clear - LOIMG T0; lia].
        - eapply rw_cells_transport; [exact PC| exact MU1| exact WM1| apply DJ1; cbn; clear - LOIMG T1 CR; subst c; lia].
        - eapply u32arr_transport; [exact ARR| exact MU1| exact WM1| apply DJ1; rewrite LWS; cbn; clear - LOIMG T1 CR; subst c; lia].
        - eapply rw_cells_transport; [exact STC| exact MU1| exact WM1| apply DJ1; cbn; clear - LOIMG T1; lia].
        - pose proof (rz_size_bound n) as RZSB. eapply rw_cells_transport; [exact HDR| exact MU1| exact WM1| apply DJ1; cbn; subst CHB AB c; clear - LOIMG AB1 ABT N2B RZSB; lia].
        - eapply ro_cells_transport; [exact TH| exact MU1| apply DJ1; cbn; clear - LOIMG T1; lia].
        - eapply ro_cells_transport; [exact TIDC| exact MU1| apply DJ1; cbn; clear - LOIMG CX1 TC; lia]. }
      cbn beta. (intros ms2 dd_H; ddestruct dd_H as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & t3' & t4' & t5' & t6' & b1n & stw' & fr0 & m2 & -> &
                            MU2 & WM2 & MI2 & HDR2 & B1A & B1B & AFR2 & PC2 & ARR2 & STC2 & ST2)).
      pose proof (rz_size_bound n) as RZSB.
      assert (DJ2 : forall A k, SPA <= A -> disjoint_from [(lo, SPA); (T + 208 + 80 * c, T + 208 + 80 * c + 4); (T + 2784, T + 2792); (CHB, CHB + 8)] A k).
      { intros A k H. cbn [disjoint_from]. subst CHB AB c SPA STK. clear - H T1 AB1 N2B RZSB LOIMG SPL CR. repeat split; lia. }
      exists x5, x6, x7, x12, x13, x14, x15, x16, x17, t3', t4', t5', t6', b1n, stw', fr0, fr1, fr2, ws, size, m2.
      split; [reflexivity|].
      split. { eapply munch_trans. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]. clear. intros x Hx. lia. }
               eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]. subst SPA STK. clear. intros x Hx. lia. }
      split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2|].
      split; [exact HDR2|]. split; [exact B1A|]. split; [exact B1B|]. split; [exact AFR2|]. split; [exact PC2|]. split; [exact ARR2|]. split; [exact STC2|].
      split. { eapply rw_cells_transport; [exact UNW1| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. subst CHB AB c SPA STK. clear - T1 AB1 ABT N2B RZSB LOIMG CR. repeat split; lia. }
      split. { eapply rw_cells_transport; [exact FR7| exact MU2| exact WM2| apply DJ2; subst SPA STK; clear; lia]. }
      split. { eapply rw_cells_transport; [exact STKC| exact MU2| exact WM2| apply DJ2; subst SPA STK; clear; lia]. }
      split. { eapply u64arr_transport; [exact HTR| exact MU2| exact WM2| apply DJ2; subst SPA STK; clear; lia]. }
      split; [exact HL30|]. split; [exact SZB|]. split; [exact SZD|].
      split. { eapply rw_cells_transport; [exact F1800| exact MU2| exact WM2| apply DJ2; subst SPA STK; clear; lia]. }
      split. { eapply rw_cells_transport; [exact TFBP| exact MU2| exact WM2| apply DJ2; subst SPA STK; clear; lia]. }
      split. { eapply rw_cells_transport; [exact F8| exact MU2| exact WM2| apply DJ2; subst SPA STK; clear; lia]. }
      split. { eapply rw_cells_transport; [exact AFR| exact MU2| exact WM2| apply DJ2; subst SPA STK; clear; lia]. }
      exact ST2. }
    (* [comment removed for export] *)
    cbn beta. intros ms2 mo2 PO HK2 MM2 HJ2.
    ddestruct PO as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & t3' & t4' & t5' & t6' & b1n & stw' & fr0 & fr1 & fr2 & ws & size & m2 & -> &
                    MU2 & WM2 & MI2 & HDR2 & B1A & B1B & AFR2 & PC2 & ARR2 & STC2 & UNW2 & FR7 & STKC & HTR & HL30 & SZB & SZD & F1800 & TFBP & F8 & AFR & ST2).
    cbn [ms_mem MS MSsvc] in HJ2.
    pose proof FP as FP'. unfold from_primary, kMaxSize in FP'. apply Z.leb_le in FP'.
    assert (N2E : needed2 n = needed n) by (unfold needed2; rewrite FP; reflexivity).
    assert (NDB : 24 <= needed n).
    { unfold needed, rounded, round_up. pose proof (rz_size_bound n). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). clear - H H0 H1 NB. lia. }
    pose proof (class_of_range (needed2 n) ltac:(clear - NDB N2E FP'; lia)) as CR. fold c in CR.
    assert (N2B : rz_size n + 8 <= needed2 n).
    { rewrite N2E. unfold needed, rounded, round_up. pose proof (rz_size_bound n). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). clear - H H0 H1 NB. lia. }
    pose proof (rz_size_bound n) as RZSB.
    assert (DJW : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from [(lo, SP); (T + 3168, T + 3169); (T + 208 + 80 * c, T + 208 + 80 * c + 4); (T + 2784, T + 2792); (CHB, CHB + 8)] A k).
    { intros A k H. cbn [disjoint_from]. subst CHB AB c. clear - H T0 AB0 RZSB LOIMG CR. repeat split; lia. }
    assert (DI2 : depot_inv m2 N nb tf bl).
    { eapply (depot_inv_transport _ m m2 N nb tf bl DI MU2 WM2 DJW).
      - intros k Hk. specialize (APTn k Hk). specialize (APAn k Hk). dpose (proj1 (proj2 (proj2 DI))) as (_ & DMF & _).
        dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb) DMF (Z.to_nat k) 0 ltac:(lia)) as (_ & X & _).
        cbn [disjoint_from]. subst CHB AB c. unfold dblk in *. clear - APTn APAn X LOIMG N2B RZSB CR. repeat split; lia.
      - intros j Hj. specialize (APTs j Hj). specialize (APAs j Hj).
        dpose (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DI)))))))) as (_ & DBF & _).
        dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl) DBF (Z.to_nat j) 0 ltac:(lia)) as (_ & X & _).
        cbn [disjoint_from]. subst CHB AB c. unfold sblk in *. clear - APTs APAs X LOIMG N2B RZSB CR. repeat split; lia. }
    assert (DST2 : depot_statics m2) by (eapply (depot_statics_transport _ m m2 DST MU2); intros A k H; apply DJW; clear - H; lia).
    assert (SCS2 : crange (CSf nb bl) lo (SPA + -128 - lo)) by (eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear; lia| subst SPA STK; clear; lia]).
    assert (TCS2 : crange (CSf nb bl) (STK + 16) 240) by (eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear - SPL; try subst STK; lia| subst STK; clear; lia]).
    assert (SPAAL : (SPA + -128) mod 16 = 0).
    { subst SPA STK. clear - SPA16. replace (SP + -2128 + -16 + -128) with (SP + (-142) * 16) by lia. rewrite Z.add_mod, Z_mod_mult, Z.add_0_r, Z.mod_mod by lia. exact SPA16. }
    assert (TRAL : (STK + 16) mod 8 = 0).
    { subst STK. pose proof (Z.div_mod SP 16 ltac:(lia)) as E. rewrite SPA16, Z.add_0_r in E. rewrite E. clear.
      replace (16 * (SP / 16) + -2128 + 16) with ((2 * (SP / 16) - 264) * 8) by lia. apply Z_mod_mult. }
    eapply aevtS_bind.
    { replace (Z_to_bv 64 size) with (Z_to_bv 64 (size + 0 * 2^32)) by (f_equal; clear; lia).
      eapply (depot_put_cfg AL IMG ALWF CSf K CSOKf KL CSmono_n CSmono_s K_apart Gn Gs T_node T_store ROOM_n ROOM_s) with (lo := lo);
        first [exact HK2| exact HJ2| exact MI2| exact DI2| exact DST2| exact HTR| exact HL30| exact SZB| exact DCS| exact ST2| exact SCS2| exact TCS2| exact LOIMG
              | exact SPAAL| exact TRAL| exact TFMAX| exact NB2| exact GN| exact GS| exact GSX| idtac].
      - clear; lia.
      - subst SPA STK; clear; lia.
      - clear - TOP1 TOP2; try subst STK; lia.
      - subst SPA STK; clear - SPL; lia.
      - subst SPA STK; clear - TOP1 TOP2; lia. }
    (* [comment removed for export] *)
    intros c3 PO3.
    ddestruct PO3 as (ms3 & mo3 & nb' & bl' & N' & tf' & id & x5' & x6' & x7' & x11' & x12' & x13' & x14' & x15' & x16' & x17' & x28 & x29 & x30 & x31 & m3
                     & -> & -> & HK3 & HJ3 & DI3 & DCS3 & DST3 & IDB & NB' & TFB' & TFP & CSM & BLK & DK3 & WM3 & ST3 & MI3 & HTR3).
    replace (ret_pc (Z_to_bv 64 294464)) with (Z_to_bv 64 0x47e40) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    ddestruct BLK as (sn & sb & Enb & Ebl & Fn & Fs).
    (* [comment removed for export] *)
    dpose (proj1 (proj2 (proj2 DI3))) as (_ & DMF3 & _).
    dpose (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DI3)))))))) as (_ & DBF3 & _).
    assert (BN : forall k, 0 <= k < Z.of_nat (length nb') -> 0x65f000 <= dblk nb' k /\ dblk nb' k + 2^20 <= ACEIL).
    { intros k Hk. dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb') DMF3 (Z.to_nat k) 0 ltac:(lia)) as (X & Y & _).
      unfold dblk. split; [exact X| exact Y]. }
    assert (BS : forall j, 0 <= j < Z.of_nat (length bl') -> 0x65f000 <= sblk bl' j /\ sblk bl' j + 2^23 <= ACEIL).
    { intros j Hj. dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl') DBF3 (Z.to_nat j) 0 ltac:(lia)) as (X & Y & _).
      unfold sblk. split; [exact X| exact Y]. }
    assert (BNold : forall k (A w : Z), 0 <= k < Z.of_nat (length nb') -> crange (CSf nb bl) A w -> 0 < w ->
              (forall k0, 0 <= k0 < Z.of_nat (length nb) -> A + w <= dblk nb k0 \/ dblk nb k0 + 2^20 <= A) ->
              A + w <= dblk nb' k \/ dblk nb' k + 2^20 <= A).
    { intros k A w Hk CR0 Hw OLD. rewrite Enb in Hk |- *. destruct (dblk_app_cases nb sn k Hk) as [[Hk' ->]| HIn].
      - apply OLD. exact Hk'.
      - eapply (apart_of_cs (CSf nb bl) A w _ (2^20) CR0); [| exact Hw| clear; lia]. exact (proj1 (Forall_forall _ _) Fn _ HIn). }
    assert (BSold : forall j (A w : Z), 0 <= j < Z.of_nat (length bl') -> crange (CSf nb bl) A w -> 0 < w ->
              (forall j0, 0 <= j0 < Z.of_nat (length bl) -> A + w <= sblk bl j0 \/ sblk bl j0 + 2^23 <= A) ->
              A + w <= sblk bl' j \/ sblk bl' j + 2^23 <= A).
    { intros j A w Hj CR0 Hw OLD. rewrite Ebl in Hj |- *. destruct (sblk_app_cases bl sb j Hj) as [[Hj' ->]| HIn].
      - apply OLD. exact Hj'.
      - eapply (apart_of_cs (CSf nb bl) A w _ (2^23) CR0); [| exact Hw| clear; lia]. exact (proj1 (Forall_forall _ _) Fs _ HIn). }
    destruct DCS3 as [NBCS3 BLCS3].
    assert (BNsh : forall k (A w : Z), 0 <= k < Z.of_nat (length nb') -> 0x7fff8000 <= A -> A + w <= 0x10007fff8000 -> 0 < w ->
              A + w <= dblk nb' k \/ dblk nb' k + 2^20 <= A).
    { intros k A w Hk H1 H2 Hw. specialize (NBCS3 k Hk).
      destruct (Z_le_dec (dblk nb' k + 2^20) A); [right; assumption|]. destruct (Z_le_dec (A + w) (dblk nb' k)); [left; assumption|]. exfalso.
      destruct (Z_le_dec A (dblk nb' k)).
      - apply (CSf_noshadow nb' bl' (dblk nb' k)); [apply NBCS3; clear; lia| clear - H1 H2 Hw n0 n1 l; lia].
      - apply (CSf_noshadow nb' bl' A); [apply NBCS3; clear - n0 n1 n2; lia| clear - H1 H2 Hw n0 n1 n2; lia]. }
    assert (BSsh : forall j (A w : Z), 0 <= j < Z.of_nat (length bl') -> 0x7fff8000 <= A -> A + w <= 0x10007fff8000 -> 0 < w ->
              A + w <= sblk bl' j \/ sblk bl' j + 2^23 <= A).
    { intros j A w Hj H1 H2 Hw. specialize (BLCS3 j Hj).
      destruct (Z_le_dec (sblk bl' j + 2^23) A); [right; assumption|]. destruct (Z_le_dec (A + w) (sblk bl' j)); [left; assumption|]. exfalso.
      destruct (Z_le_dec A (sblk bl' j)).
      - apply (CSf_noshadow nb' bl' (sblk bl' j)); [apply BLCS3; clear; lia| clear - H1 H2 Hw n0 n1 l; lia].
      - apply (CSf_noshadow nb' bl' A); [apply BLCS3; clear - n0 n1 n2; lia| clear - H1 H2 Hw n0 n1 n2; lia]. }
    (* [comment removed for export] *)
    pose proof (dkeep_low m2 m3 lo (SPA + -128) nb' bl' DK3 ltac:(subst SPA STK; clear - LOIMG SPL; lia)
                  ltac:(intros k Hk; exact (proj1 (BN k Hk))) ltac:(intros j Hj; exact (proj1 (BS j Hj)))) as MUlow.
    assert (MUT : munch [(0, T); (T + 4096, 2^64)] m2 m3).
    { eapply (dkeep_window m2 m3 lo (SPA + -128) nb' bl' T 4096 DK3); [clear - T0; lia| clear - T1; lia| left; subst SPA STK; clear - T1 LOIMG SPL; lia| unfold A_SS, A_DEP_END; clear - T0; lia| |].
      - intros k Hk. apply (BNold k T 4096 Hk TCS ltac:(clear; lia) APTn).
      - intros j Hj. apply (BSold j T 4096 Hj TCS ltac:(clear; lia) APTs). }
    assert (MUC : munch [(0, CTX); (CTX + 0x10000, 2^64)] m2 m3).
    { eapply (dkeep_window m2 m3 lo (SPA + -128) nb' bl' CTX 0x10000 DK3); [clear - CX0; lia| clear - CX1; lia| left; subst SPA STK; clear - CX1 LOIMG SPL; lia| unfold A_SS, A_DEP_END; clear - CX0; lia| |].
      - intros k Hk. apply (BNold k CTX 0x10000 Hk CTXCS ltac:(clear; lia) APCn).
      - intros j Hj. apply (BSold j CTX 0x10000 Hj CTXCS ltac:(clear; lia) APCs). }
    assert (MUA : munch [(0, AB); (AB + needed2 n, 2^64)] m2 m3).
    { eapply (dkeep_window m2 m3 lo (SPA + -128) nb' bl' AB (needed2 n) DK3); [clear - AB0; lia| clear - AB1; lia| left; subst SPA STK; clear - AB1 LOIMG SPL; lia| unfold A_SS, A_DEP_END; clear - AB0; lia| |].
      - intros k Hk. apply (BNold k AB (needed2 n) Hk ACS ltac:(clear - NDB N2E; lia) APAn).
      - intros j Hj. apply (BSold j AB (needed2 n) Hj ACS ltac:(clear - NDB N2E; lia) APAs). }
    set (ASH := 0x7fff8000 + Z.shiftr AB 3) in *.
    assert (ASHE : Z.shiftr AB 3 = AB / 8) by (rewrite Z.shiftr_div_pow2 by (clear; lia); reflexivity).
    assert (MUSH : munch [(0, ASH); (ASH + (needed2 n / 8 + 2), 2^64)] m2 m3).
    { eapply (dkeep_window m2 m3 lo (SPA + -128) nb' bl' ASH (needed2 n / 8 + 2) DK3);
        [clear - AB0 ASHE; try subst ASH; lia| clear - AB0 AB1 ASHE; try subst ASH; lia| left; subst ASH SPA STK; clear - AB0 AB1 ASHE LOIMG SPL; lia
        | unfold A_SS, A_DEP_END; clear - AB0 ASHE; try subst ASH; lia| |].
      - intros k Hk. apply (BNsh k ASH (needed2 n / 8 + 2) Hk); clear - AB0 AB1 ASHE NDB N2E; try subst ASH; lia.
      - intros j Hj. apply (BSsh j ASH (needed2 n / 8 + 2) Hj); clear - AB0 AB1 ASHE NDB N2E; try subst ASH; lia. }
    assert (MUST : munch [(0, SPA + -128); (SPA + -128 + 2272, 2^64)] m2 m3).
    { eapply (dkeep_window m2 m3 lo (SPA + -128) nb' bl' (SPA + -128) 2272 DK3);
        [subst SPA STK; clear - SPL LOIMG; lia| subst SPA STK; clear - TOP1 TOP2; lia| right; clear; lia| right; unfold A_DEP_END; subst SPA STK; clear - LOIMG SPL; lia| |].
      - intros k Hk. right. pose proof (BN k Hk). subst SPA STK; clear - H LOIMG SPL; lia.
      - intros j Hj. right. pose proof (BS j Hj). subst SPA STK; clear - H LOIMG SPL; lia. }
    (* [comment removed for export] *)
    assert (UBE : UB = CHB + 16) by (subst UB CHB; clear; lia).
    assert (NFB : 1 <= nfix n <= Z.max n 1) by (unfold nfix; clear - NB; lia).
    assert (N2B' : nfix n + rz_size n <= needed2 n).
    { rewrite N2E. unfold needed, rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). clear - H H0 NB NFB. lia. }
    assert (KFB : 1 <= KF <= nfix n) by (clear - NFB; try subst KF; lia).
    assert (SUBE : SUB = ASH + rz_size n / 8).
    { subst SUB ASH UB. rewrite ASHE. pose proof (rz_size_cases n) as RC. clear - RC. lia. }
    assert (PGSE : PGS = ASH + rz_size n / 8 + nfix n / 8).
    { subst PGS ASH UB. rewrite ASHE, Z.shiftr_div_pow2 by (clear; lia). pose proof (rz_size_cases n) as RC. clear - RC. lia. }
    assert (SHW : forall A k, ASH <= A -> A + k <= ASH + (needed2 n / 8 + 2) ->
              disjoint_from [(lo, SP); (T + 3168, T + 3169); (T + 208 + 80 * c, T + 208 + 80 * c + 4); (T + 2784, T + 2792); (CHB, CHB + 8)] A k).
    { intros A k H1 H2. cbn [disjoint_from]. subst ASH CHB AB c. clear - H1 H2 ASHE AB0 AB1 LOIMG TNS RNG CR NDB N2E RZSB. repeat split; lia. }
    assert (AS2 : allocA_statics m2 T CTX).
    { eapply (allocA_statics_transport _ m m2 T CTX AS MU2); [intros A k H; apply DJW; exact H|]. cbn [disjoint_from]. subst CHB AB c. clear - LOIMG CX1 TC ABC CR N2B RZSB. repeat split; lia. }
    assert (PS2 : poison_statics m2) by (eapply (poison_statics_transport _ m m2 PS MU2); intros A k H; apply DJW; clear - H; lia).
    assert (FS2 : fin_statics m2) by (eapply (fin_statics_transport _ m m2 FS MU2); intros A k H; apply DJW; exact H).
    assert (GOTFL2 : ro_cells asegs m2 A_GOT_FLAGS [C8 (Z_to_bv 64 A_FLAGS)]) by (eapply ro_cells_transport; [exact GOTFL| exact MU2| apply DJW; unfold A_GOT_FLAGS; cbn; clear; lia]).
    assert (PPART2 : ro_cells asegs m2 A_FL_PPART [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact PPART| exact MU2| apply DJW; unfold A_FL_PPART; cbn; clear; lia]).
    assert (SHC2 : ro_cells asegs m2 ASH [C1 shb]) by (eapply ro_cells_transport; [exact SHC| exact MU2| apply SHW; cbn; clear - NDB N2E; lia]).
    assert (SH2 : rw_cells asegs m2 SUB [CB (Z.to_nat (nfix n / 8)) sj]).
    { eapply rw_cells_transport; [exact SH| exact MU2| exact WM2| apply SHW; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - NFB; lia); rewrite SUBE; clear - N2B' NFB RZSB; lia]. }
    assert (DIV8 : rz_size n / 8 + nfix n / 8 <= needed2 n / 8).
    { pose proof (rz_size_cases n) as RC. pose proof (Z.div_mod (nfix n) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(clear; lia)).
      apply Z.div_le_lower_bound; [clear; lia|]. clear - RC H H0 N2B'. lia. }
    assert (PGC2 : rw_cells asegs m2 PGS [C1 pgb]).
    { eapply rw_cells_transport; [exact PGC| exact MU2| exact WM2| apply SHW; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat]; rewrite PGSE; clear - DIV8 NFB RZSB; lia]. }
    assert (STH2 : rw_cells asegs m2 (T + 2800) [C8 j0; C8 j1; C8 j2]).
    { eapply rw_cells_transport; [exact STH| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. subst CHB AB c. clear - LOIMG T1 ABT CR N2B RZSB. repeat split; lia. }
    assert (STB2 : u64arr asegs m2 (T + 2912) bs).
    { eapply u64arr_transport; [exact STB| exact MU2| exact WM2|]. rewrite HL. cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul]. subst CHB AB c. clear - LOIMG T1 ABT CR N2B RZSB. repeat split; lia. }
    assert (UC2 : rw_cells asegs m2 UB [CB (Z.to_nat KF) uj]).
    { eapply rw_cells_transport; [exact UC| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - KFB; lia).
      subst UB CHB AB c. clear - LOIMG T1 ABT CR N2B' KFB RZSB AB1. repeat split; lia. }
    assert (MG2 : 16 < rz_size n -> rw_cells asegs m2 AB [C8 mg0; C8 mg1]).
    { intros Hrz. eapply rw_cells_transport; [exact (MG Hrz)| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add].
      pose proof (rz_size_cases n) as RC. subst CHB AB c. clear - LOIMG T1 ABT CR N2B RC Hrz AB1. repeat split; lia. }
    (* [comment removed for export] *)
    assert (WD : forall A sz A' k, A <= A' -> A' + k <= A + sz -> disjoint_from [(0, A); (A + sz, 2^64)] A' k) by (intros; cbn [disjoint_from]; lia).
    assert (LOWD : forall A k, (0x10000 <= A /\ A + k <= A_SS) \/ (A_DEP_END <= A /\ A + k <= 0x65f000) -> disjoint_from [(A_SS, A_DEP_END); (0x65f000, 2^64)] A k)
      by (intros A k H; unfold A_SS, A_DEP_END in *; cbn [disjoint_from]; clear - H; lia).
    assert (AS3 : allocA_statics m3 T CTX) by (eapply (allocA_statics_transport2 _ _ m2 m3 T CTX AS2 MUlow MUC LOWD); apply WD; clear; lia).
    assert (PS3 : poison_statics m3) by (eapply (poison_statics_transport _ m2 m3 PS2 MUlow); intros A k H; apply LOWD; left; exact H).
    assert (FS3 : fin_statics m3) by (eapply (fin_statics_transport2 _ m2 m3 FS2 MUlow LOWD)).
    assert (GOTFL3 : ro_cells asegs m3 A_GOT_FLAGS [C8 (Z_to_bv 64 A_FLAGS)]) by (eapply ro_cells_transport; [exact GOTFL2| exact MUlow| apply LOWD; unfold A_GOT_FLAGS, A_SS; cbn; clear; lia]).
    assert (PPART3 : ro_cells asegs m3 A_FL_PPART [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact PPART2| exact MUlow| apply LOWD; unfold A_FL_PPART, A_SS; cbn; clear; lia]).
    assert (SHC3 : ro_cells asegs m3 ASH [C1 shb]) by (eapply ro_cells_transport; [exact SHC2| exact MUSH| apply WD; cbn; clear - NDB N2E; lia]).
    assert (SH3 : rw_cells asegs m3 SUB [CB (Z.to_nat (nfix n / 8)) sj]).
    { eapply rw_cells_transport; [exact SH2| exact MUSH| exact WM3| apply WD; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - NFB; lia); rewrite SUBE; clear - N2B' NFB RZSB; lia]. }
    assert (PGC3 : rw_cells asegs m3 PGS [C1 pgb]).
    { eapply rw_cells_transport; [exact PGC2| exact MUSH| exact WM3| apply WD; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat]; rewrite PGSE; clear - DIV8 NFB RZSB; lia]. }
    assert (STH3 : rw_cells asegs m3 (T + 2800) [C8 j0; C8 j1; C8 j2]) by (eapply rw_cells_transport; [exact STH2| exact MUT| exact WM3| apply WD; cbn; clear; lia]).
    assert (STB3 : u64arr asegs m3 (T + 2912) bs) by (eapply u64arr_transport; [exact STB2| exact MUT| exact WM3| apply WD; rewrite ?HL; clear; lia]).
    assert (UC3 : rw_cells asegs m3 UB [CB (Z.to_nat KF) uj]).
    { eapply rw_cells_transport; [exact UC2| exact MUA| exact WM3| apply WD; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - KFB; lia); clear - RZSB KFB N2B'; try subst UB; lia]. }
    assert (MG3 : 16 < rz_size n -> rw_cells asegs m3 AB [C8 mg0; C8 mg1]).
    { intros Hrz. eapply rw_cells_transport; [exact (MG2 Hrz)| exact MUA| exact WM3| apply WD; cbn; clear - NDB N2E; lia]. }
    assert (HDR3 : rw_cells asegs m3 CHB [C1 b0; C1 (Z_to_bv 8 b1n); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nfix n)); C8 w8]).
    { eapply rw_cells_transport; [exact HDR2| exact MUA| exact WM3| apply WD; cbn; clear - RZSB N2B; try subst CHB; lia]. }
    assert (AFR3 : allocA_frame m3 SPA fr0 1 (Z_to_bv 64 0x47a64) (Z_to_bv 64 SP) (Z_to_bv 64 n) (Z_to_bv 64 A_PC_MALLOC) (Z_to_bv 64 1) (Z_to_bv 64 STK) (Z_to_bv 64 (SP + -81)) s6 s7 s8 s9 s10 s11).
    { unfold allocA_frame in *. eapply rw_cells_transport; [exact AFR2| exact MUST| exact WM3| apply WD; cbn; subst SPA STK; clear; lia]. }
    assert (PC3 : rw_cells asegs m3 (T + 208 + 80 * c) [C4 (Z_to_bv 64 (cnt - 1)); C4 mx; C8 (Z_to_bv 64 csz)]) by (eapply rw_cells_transport; [exact PC2| exact MUT| exact WM3| apply WD; cbn; clear - CR; lia]).
    assert (ARR3 : u32arr asegs m3 (T + 208 + 80 * c + 16) ws16) by (eapply u32arr_transport; [exact ARR2| exact MUT| exact WM3| apply WD; rewrite ?LWS; clear - CR; lia]).
    assert (STC3 : rw_cells asegs m3 (T + 2784) [C8 stw']) by (eapply rw_cells_transport; [exact STC2| exact MUT| exact WM3| apply WD; cbn; clear; lia]).
    assert (UNW3 : rw_cells asegs m3 (T + 3168) [C1 (Z_to_bv 8 0)]) by (eapply rw_cells_transport; [exact UNW2| exact MUT| exact WM3| apply WD; cbn; clear; lia]).
    assert (FR7' : rw_cells asegs m3 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_transport; [exact FR7| exact MUST| exact WM3| apply WD; cbn; subst SPA STK; clear; lia]).
    assert (STKC3 : rw_cells asegs m3 STK [C8 (Z_to_bv 64 (STK + 16)); C8 (Z_to_bv 64 size)]) by (eapply rw_cells_transport; [exact STKC| exact MUST| exact WM3| apply WD; cbn; subst SPA STK; clear; lia]).
    assert (F1800' : rw_cells asegs m3 (STK + 256) [CB 1800 fr1]) by (eapply rw_cells_transport; [exact F1800| exact MUST| exact WM3| apply WD; cbn; subst SPA STK; clear; lia]).
    assert (TFBP' : rw_cells asegs m3 (STK + 2056) [C8 (Z_to_bv 64 SP)]) by (eapply rw_cells_transport; [exact TFBP| exact MUST| exact WM3| apply WD; cbn; subst SPA STK; clear; lia]).
    assert (F8' : rw_cells asegs m3 (STK + 2064) [CB 8 fr2]) by (eapply rw_cells_transport; [exact F8| exact MUST| exact WM3| apply WD; cbn; subst SPA STK; clear; lia]).
    assert (AFR' : rw_cells asegs m3 (STK + -16) [C8 (Z_to_bv 64 SP); C8 (Z_to_bv 64 0x6978c)]) by (eapply rw_cells_transport; [exact AFR| exact MUST| exact WM3| apply WD; cbn; subst SPA STK; clear; lia]).
    assert (TCS3 : crange (CSf nb' bl') T 4096) by (exact (crange_mono _ _ _ _ TCS CSM)).
    assert (CTXCS3 : crange (CSf nb' bl') CTX 0x10000) by (exact (crange_mono _ _ _ _ CTXCS CSM)).
    assert (ACS3 : crange (CSf nb' bl') AB (needed2 n)) by (exact (crange_mono _ _ _ _ ACS CSM)).
    assert (SCS3 : crange (CSf nb' bl') lo (SP - lo)) by (exact (crange_mono _ _ _ _ SCS CSM)).
    assert (IDB' : 0 <= id < 2^31) by (clear - IDB NB' NB2; lia).
    clear AS2 PS2 FS2 GOTFL2 PPART2 SHC2 SH2 PGC2 STH2 STB2 UC2 MG2.
    assert (SHAP : forall A k, ASH <= A -> A + k <= ASH + (needed2 n / 8 + 2) ->
              (A + k <= AB \/ AB + needed2 n <= A) /\ A + k <= lo /\ (A + k <= T \/ T + 4096 <= A)).
    { intros A k H1 H2. subst ASH. clear - H1 H2 ASHE AB0 AB1 LOIMG TNS RNG NDB N2E. lia. }
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf nb' bl') (K nb' bl') (segCC_post ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc id b1n pgb m3) _ _ mo3 (KL nb' bl') HK3); [exact HJ3| |].
    {
      eapply evtA_cut.
      { eapply (msegC1 AL IMG ALWF (CSf nb' bl') (CSOKf nb' bl') SP n lo T CTX TID SB pw); try eassumption. all: clear - TOP1 TOP2; lia. }
      cbn beta. (intros ms4 dd_H; ddestruct dd_H as (x1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y22 & y28 & y29 & y30 & y31 & j0' & j1' & j2' & bs' & m4 & -> &
                            MU4 & WM4 & MI4 & AFR4 & HDR4 & SH4 & PGC4 & STH4 & STB4 & HL4 & UC4 & ST4)).
      assert (DJ4lo : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from [(lo, SPA + -128); (CHB + 8, CHB + 16); (SUB, SUB + nfix n / 8); (PGS, PGS + 1); (T + 2800, T + 3168); (UB, UB + KF)] A k).
      { intros A k H. cbn [disjoint_from]. rewrite SUBE, PGSE. subst UB CHB ASH. clear - H T0 AB0 RZSB LOIMG ASHE NFB. repeat split; lia. }
      assert (DJ4hi : forall A k, SPA <= A -> disjoint_from [(lo, SPA + -128); (CHB + 8, CHB + 16); (SUB, SUB + nfix n / 8); (PGS, PGS + 1); (T + 2800, T + 3168); (UB, UB + KF)] A k).
      { intros A k H. dpose (SHAP SUB (nfix n / 8) ltac:(rewrite SUBE; clear - RZSB; lia) ltac:(rewrite SUBE; clear - RZSB NFB N2B'; lia)) as (_ & X1 & _).
        dpose (SHAP PGS 1 ltac:(rewrite PGSE; clear - RZSB NFB; lia) ltac:(rewrite PGSE; clear - RZSB NFB N2B'; lia)) as (_ & X2 & _).
        cbn [disjoint_from]. subst UB CHB AB SPA STK c. clear - H X1 X2 T1 AB1 LOIMG SPL N2B' KFB RZSB. repeat split; lia. }
      assert (FS4 : fin_statics m4) by (eapply (fin_statics_transport _ m3 m4 FS3 MU4); exact DJ4lo).
      assert (MG4 : 16 < rz_size n -> rw_cells asegs m4 AB [C8 mg0; C8 mg1]).
      { intros Hrz. dpose (SHAP SUB (nfix n / 8) ltac:(rewrite SUBE; clear - RZSB; lia) ltac:(rewrite SUBE; clear - RZSB NFB N2B'; lia)) as (X1 & _ & _).
        dpose (SHAP PGS 1 ltac:(rewrite PGSE; clear - RZSB NFB; lia) ltac:(rewrite PGSE; clear - RZSB NFB N2B'; lia)) as (X2 & _ & _).
        eapply rw_cells_transport; [exact (MG3 Hrz)| exact MU4| exact WM4|]. cbn [disjoint_from cells_size csize Nat.add].
        pose proof (rz_size_cases n) as RC. subst UB CHB AB c. clear - X1 X2 LOIMG AB1 ABT RC Hrz NDB N2E NFB. repeat split; lia. }
      assert (AFR'4 : rw_cells asegs m4 (STK + -16) [C8 (Z_to_bv 64 SP); C8 (Z_to_bv 64 0x6978c)]) by (eapply rw_cells_transport; [exact AFR'| exact MU4| exact WM4| apply DJ4hi; subst SPA STK; clear; lia]).
      assert (FR7'4 : rw_cells asegs m4 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_transport; [exact FR7'| exact MU4| exact WM4| apply DJ4hi; subst SPA STK; clear; lia]).
      assert (STKC4 : rw_cells asegs m4 STK [C8 (Z_to_bv 64 (STK + 16)); C8 (Z_to_bv 64 size)]) by (eapply rw_cells_transport; [exact STKC3| exact MU4| exact WM4| apply DJ4hi; subst SPA STK; clear; lia]).
      assert (HTR4 : u64arr asegs m4 (STK + 16) ws) by (eapply u64arr_transport; [exact HTR3| exact MU4| exact WM4| apply DJ4hi; subst SPA STK; clear; lia]).
      assert (F1800'4 : rw_cells asegs m4 (STK + 256) [CB 1800 fr1]) by (eapply rw_cells_transport; [exact F1800'| exact MU4| exact WM4| apply DJ4hi; subst SPA STK; clear; lia]).
      assert (TFBP'4 : rw_cells asegs m4 (STK + 2056) [C8 (Z_to_bv 64 SP)]) by (eapply rw_cells_transport; [exact TFBP'| exact MU4| exact WM4| apply DJ4hi; subst SPA STK; clear; lia]).
      assert (F8'4 : rw_cells asegs m4 (STK + 2064) [CB 8 fr2]) by (eapply rw_cells_transport; [exact F8'| exact MU4| exact WM4| apply DJ4hi; subst SPA STK; clear; lia]).
      eapply evtA_mono.
      { eapply (msegC2 AL IMG ALWF (CSf nb' bl') (CSOKf nb' bl') SP n lo T TID SB pw) with (q0 := s0) (q1 := s1) (q2 := s2) (q3 := s3) (q4 := s4) (q5 := s5); try eassumption.
        all: clear - TOP1 TOP2; lia. }
      cbn beta. (intros ms5 dd_H; ddestruct dd_H as (z0 & z1 & z2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & z3 & z4 & z5 & z6 & m5 & -> & MU5 & WM5 & MI5 & HDR5 & MG5 & ST5)).
      dpose (SHAP SUB (nfix n / 8) ltac:(rewrite SUBE; clear - RZSB; lia) ltac:(rewrite SUBE; clear - RZSB NFB N2B'; lia)) as (X1 & X1' & X1'').
      dpose (SHAP PGS 1 ltac:(rewrite PGSE; clear - RZSB NFB; lia) ltac:(rewrite PGSE; clear - RZSB NFB N2B'; lia)) as (X2 & X2' & X2'').
      dexists z0, z1, z2, q1, q2, q3, q4, q5, q6, q7, z3, z4, z5, z6, j0', j1', j2', bs', m5.
      split; [reflexivity|].
      split. { eapply munch_trans. { eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]. subst KF PGS SUB CHB UB AB c SPA STK. clear. intros x Hx. lia. }
               eapply munch_weaken; [| exact MU5]. unfold sub_fp; cbn [outside]. subst KF PGS SUB CHB UB AB c SPA STK. clear. intros x Hx. lia. }
      split; [eapply wmono_trans; [exact WM4| exact WM5]|]. split; [exact MI5|].
      split; [exact HDR5|]. split; [exact MG5|].
      split. { eapply rw_cells_transport; [exact SH4| exact MU5| exact WM5|]. cbn [disjoint_from cells_size csize Nat.add]. rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - NFB; lia).
               subst CHB. clear - X1 X1' RZSB N2B NFB. repeat split; lia. }
      split. { eapply rw_cells_transport; [exact PGC4| exact MU5| exact WM5|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat].
               subst CHB. clear - X2 X2' RZSB N2B NFB. repeat split; lia. }
      split. { eapply rw_cells_transport; [exact STH4| exact MU5| exact WM5|]. cbn [disjoint_from cells_size csize Nat.add]. subst CHB. clear - LOIMG T1 ABT N2B RZSB. repeat split; lia. }
      split. { eapply u64arr_transport; [exact STB4| exact MU5| exact WM5|]. rewrite HL4. cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul]. subst CHB. clear - LOIMG T1 ABT N2B RZSB. repeat split; lia. }
      split; [exact HL4|].
      split. { eapply rw_cells_transport; [exact UC4| exact MU5| exact WM5|]. cbn [disjoint_from cells_size csize Nat.add]. rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - KFB; lia).
               subst UB CHB. clear - LOIMG AB1 N2B' KFB RZSB. repeat split; lia. }
      exact ST5. }
    (* [comment removed for export] *)
    cbn beta. intros ms5 mo5 PO5 HK5 MM5 HJ5.
    ddestruct PO5 as (z0 & z1 & z2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & z3 & z4 & z5 & z6 & j0' & j1' & j2' & bs' & m5 & -> &
                     MU5 & WM5 & MI5 & HDR5 & MG5 & SH5 & PGC5 & STH5 & STB5 & HL5 & UC5 & ST5).
    apply aevtS_now.
    eexists. dexists mo5, nb', bl', N', tf', id. dexists z0, z1, z2, q1, q2, q3, q4, q5, q6, q7, z3, z4, z5, z6. dexists (Z.land b1n 243), stw', j0', j1', j2', bs', m5.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HK5|]. split; [exact HJ5|].
    assert (DJ5lo : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from [(lo, SP); (CHB, CHB + 16); (AB, AB + 16); (SUB, SUB + nfix n / 8); (PGS, PGS + 1); (T + 2800, T + 3168); (UB, UB + KF)] A k).
    { intros A k H. cbn [disjoint_from]. rewrite SUBE, PGSE. subst UB CHB ASH. clear - H T0 AB0 RZSB LOIMG ASHE NFB. repeat split; lia. }
    dpose (SHAP SUB (nfix n / 8) ltac:(rewrite SUBE; clear - RZSB; lia) ltac:(rewrite SUBE; clear - RZSB NFB N2B'; lia)) as (X1 & X1' & X1'').
    dpose (SHAP PGS 1 ltac:(rewrite PGSE; clear - RZSB NFB; lia) ltac:(rewrite PGSE; clear - RZSB NFB N2B'; lia)) as (X2 & X2' & X2'').
    split.
    { eapply (depot_inv_transport _ m3 m5 N' nb' tf' bl' DI3 MU5 WM5 DJ5lo).
      - intros k Hk. pose proof (BNold k T 4096 Hk TCS ltac:(clear; lia) APTn) as Y1. pose proof (BNold k AB (needed2 n) Hk ACS ltac:(clear - NDB N2E; lia) APAn) as Y2.
        pose proof (BNsh k SUB (nfix n / 8 + 1) Hk ltac:(rewrite SUBE; clear - RZSB AB0 ASHE; try subst ASH; lia) ltac:(clear - X1' LOIMG NFB AB1 X1 RNG SUBE ASHE AB0 NDB N2E RZSB N2B'; subst ASH; lia) ltac:(clear - NFB; lia)) as Y3.
        pose proof (BNsh k PGS 1 Hk ltac:(rewrite PGSE; clear - RZSB AB0 ASHE NFB; try subst ASH; lia) ltac:(clear - NFB AB1 PGSE ASHE AB0 NDB N2E RZSB N2B'; subst ASH; lia) ltac:(clear; lia)) as Y4.
        pose proof (BN k Hk) as Y5.
        cbn [disjoint_from]. subst UB CHB. clear - Y1 Y2 Y3 Y4 Y5 LOIMG RZSB N2B' KFB NFB. repeat split; lia.
      - intros j Hj. pose proof (BSold j T 4096 Hj TCS ltac:(clear; lia) APTs) as Y1. pose proof (BSold j AB (needed2 n) Hj ACS ltac:(clear - NDB N2E; lia) APAs) as Y2.
        pose proof (BSsh j SUB (nfix n / 8 + 1) Hj ltac:(rewrite SUBE; clear - RZSB AB0 ASHE; try subst ASH; lia) ltac:(clear - X1' LOIMG NFB AB1 X1 RNG SUBE ASHE AB0 NDB N2E RZSB N2B'; subst ASH; lia) ltac:(clear - NFB; lia)) as Y3.
        pose proof (BSsh j PGS 1 Hj ltac:(rewrite PGSE; clear - RZSB AB0 ASHE NFB; try subst ASH; lia) ltac:(clear - NFB AB1 PGSE ASHE AB0 NDB N2E RZSB N2B'; subst ASH; lia) ltac:(clear; lia)) as Y4.
        pose proof (BS j Hj) as Y5.
        cbn [disjoint_from]. subst UB CHB. clear - Y1 Y2 Y3 Y4 Y5 LOIMG RZSB N2B' KFB NFB. repeat split; lia. }
    split; [split; [exact NBCS3| exact BLCS3]|].
    split; [eapply (depot_statics_transport _ m3 m5 DST3 MU5); intros A k H; apply DJ5lo; clear - H; lia|].
    split; [exact IDB|]. split; [exact NB'|]. split; [clear - TFB' SZD SZB; lia|]. split; [clear - TFP SZD; lia|]. split; [exact CSM|].
    split; [dexists sn, sb; split; [exact Enb| split; [exact Ebl| split; [exact Fn| exact Fs]]]|].
    split.
    { (* [comment removed for export] *)
      intros x. cbv zeta. intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
      pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
      rewrite (MU5 x). 2:{ cbn [outside]. clear - H1 H8 H9 H10 H11 H7 H12. subst KF PGS SUB CHB UB AB c. repeat split; try exact I; lia. }
      rewrite (DK3 x). 2:{ subst SPA STK. clear - H1. lia. } 2:{ exact H2. } 2:{ exact H3. } 2:{ exact H4. }
      apply (MU2 x). cbn [outside]. clear - H1 H5 H6 H7 H8. subst CHB AB c. repeat split; try exact I; lia. }
    split; [eapply wmono_trans; [exact WM2| eapply wmono_trans; [exact WM3| exact WM5]]|].
    split; [exact MI5|]. split; [exact ST5|].
    split; [exact HDR5|].
    split. { rewrite <- Z.land_assoc. change (Z.land 243 3) with 3. exact B1A. }
    split. { apply (land_lt_pow2 b1n 243 8); [exact B1B| clear; lia]. }
    split; [exact MG5|]. split; [exact SH5|]. split; [exact PGC5|]. split; [exact UC5|].
    assert (DJ5T : forall A k, T <= A -> A + k <= T + 2800 -> disjoint_from [(lo, SP); (CHB, CHB + 16); (AB, AB + 16); (SUB, SUB + nfix n / 8); (PGS, PGS + 1); (T + 2800, T + 3168); (UB, UB + KF)] A k).
    { intros A k Ha Hb. cbn [disjoint_from]. subst UB CHB. clear - Ha Hb X1'' X2'' LOIMG T1 ABT RZSB N2B' KFB NFB. repeat split; lia. }
    split; [eapply rw_cells_transport; [exact PC3| exact MU5| exact WM5| apply DJ5T; cbn; clear - CR; try subst c; lia]|].
    split; [eapply u32arr_transport; [exact ARR3| exact MU5| exact WM5| apply DJ5T; rewrite ?LWS; cbn; clear - CR; try subst c; lia]|].
    split; [eapply rw_cells_transport; [exact STC3| exact MU5| exact WM5| apply DJ5T; cbn; clear; lia]|].
    split; [exact STH5|]. split; [exact STB5|]. split; [exact HL5|].
    eapply rw_cells_transport; [exact UNW3| exact MU5| exact WM5|].
    cbn [disjoint_from cells_size csize Nat.add]. subst UB CHB. clear - X1'' X2'' LOIMG T1 ABT RZSB N2B' KFB NFB. repeat split; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MallocTop.

End ARUN_1.
