(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Arr Bytes Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import DivergeSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AKinv AJ AKinvS AKinvM ASpinS AW_MmapAnon AW_MmapDie ASpin
     AW_DepotA AW_DepotB AW_DepotC AW_DepotD AW_DepotE AW_DepotF AW_DepotCfg AW_DepotInv AW_DepotTop
     AW_MallocA AW_AllocA AW_Poison AW_AllocB AW_MallocB AW_MallocC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_CfgS AW_ClassId AW_Combined AW_Refill AW_GetFrom AW_Populate AW_Populate2 AW_CfgDefs
     AW_PopulateCfgS AW_GetFromCfgS AW_RefillCfgS AW_CombinedCfgS AW_MallocGenLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ASplit AKinvSplit AW_PopulateSplit AW_GetFromSplit AW_RefillSplit AW_CombinedSplit.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import SRz.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_MallocGenSplit () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.dkeep"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.A_DEP_END"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dblk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.sblk"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.not"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Logic.eq"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.fin_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_OOM_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocB.A_ERRNO"; "ARUN_1.oe_ok"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.thr_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CfgDefs.mwc_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CfgDefs.pop_statics"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.fixrw_grantable"; "RocqVerifyHarness.AgentSubmission.BHeap.AKinvM.scar_site"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CfgDefs.unit_if"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.max_count"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Lists.ListDef.repeat"; "ARUN_1.MallocGenSplit.gkeep"; "ARUN_1.MallocGenSplit.mgen_windows"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "Stdlib.ZArith.BinInt.Z.min"; "ARUN_1.MallocGenSplit.pgw"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_GetFrom.cpy"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate2.carve_list"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_cs"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kAllocBegMagic"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.pgv"; "Stdlib.ZArith.BinInt.Z.b2z"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.from_primary"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Combined.A_COMBINED"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocA.A_PC_MALLOC"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocC.msegA_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.MallocGenSplit.head_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocA.A_MALLOC"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_MRN_CELL"; "ARUN_1.MallocGenSplit.ChunkArm.cwin"; "ARUN_1.MallocGenSplit.ChunkArm.zkeep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_GOT_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_FL_PPART"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "ARUN_1.MallocGenSplit.ChunkArm.chunk_post"; "ARUN_1.MallocGenSplit.fchunk"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.TSet"; "Corelib.Lists.ListDef.firstn"; "ARUN_1.MallocGenSplit.hsh"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "ARUN_1.MallocGenSplit.mgen_postN"; "Corelib.Init.Logic.True"; "RocqVerifyHarness.AgentSubmission.LibA.SRz.srealizesJ"; "ARUN_1.MallocGenSplit.mgen_postC"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.t_alt2"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Refill.pc_old"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Refill.pc_new"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L34301640341.9L46253703355.7L58852693222.900000Q00e01?S2nb1A2sz1k2H31x2X12X22XR2bl1j2H4S1A2sz2H21x2X12X22XRS2lo2SP1A2sz2H11x2X12X22XR". (* [comment removed for export] *)
#[using="Type"] Lemma dkeep_window : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Plo,$2.PSP,$2.Pnb,(3.$2.)Pbl,(3.$2.)PA,$2.Psz,$2.P,(4.R8.R7.R6.R5.R4.R3.)P,(5.=R3.)P,(5.(6.R4.R3.)(7.+2.+40.))P,(8.(5.(6.R5.R4.)R9.)(5.R8.R5.))P,(8.(5.(6.R6.R5.)$9.)(5.$:.R6.))P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R:.))))(8.(5.(6.R9.R8.)(?.R;.R2.))(5.(6.(?.R;.R2.)(7.+2.+14.))R9.))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R:.))))(8.(5.(6.R:.R9.)(10.R;.R2.))(5.(6.(10.R;.R2.)(7.+2.+17.))R:.))(11.(12.(13.$2.$2.)(14.$2.$2.=R9.)(12.(13.$2.$2.)(14.$2.$2.(6.R9.R8.)(7.+2.+40.))(15.(13.$2.$2.))))R?.R>.)")
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
#[using="Type"] Lemma dkeep_low : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Plo,$2.PSP,$2.Pnb,(3.$2.)Pbl,(3.$2.)P,(4.R6.R5.R4.R3.R2.R1.)P,(5.+65?000.R5.)P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R5.))))(5.+65?000.(?.R6.R2.))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R5.))))(5.+65?000.(10.R6.R2.))(11.(12.(13.$2.$2.)(14.$2.$2.$9.$:.)(12.(13.$2.$2.)(14.$2.$2.+65?000.(7.+2.+40.))(15.(13.$2.$2.))))R:.R9.)")
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
#[using="Type"] Lemma apart_of_cs : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PP,P,$2.SpPA,$2.Pn,$2.Pb,$2.Pw,$2.P,(16.R5.R4.R3.)P,Px,$2.P,A1.R7.R1.(17.(;.(5.R5.R2.)(<.R2.(6.R5.R4.))))P,(<.=R5.)P,(<.=R4.)(8.(5.(6.R8.R7.)R6.)(5.(6.R6.R5.)R8.))")
(* [comment removed for export] *).
Proof.
  intros P A n b w CR NB Hn Hw. destruct (Z_lt_dec b A).
  - destruct (Z_lt_dec A (b + w)); [| lia]. exfalso. apply (NB A); [apply CR; lia| lia].
  - destruct (Z_lt_dec b (A + n)); [| lia]. exfalso. apply (NB b); [apply CR; lia| lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L38391271824.6L40393003166.6L40393036188.6L51972276493.600000>00L00Z00hS2nb2sn1k2Hk1nS2nb2sn1k2Hk1nS2nb2sn1k2Hk1lS2nb2sn1k2Hk1l". (* [comment removed for export] *)
#[using="Type"] Lemma dblk_app_cases : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pnb,(3.$2.)Psn,(3.$2.)Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.(18.$2.R3.R2.)))))(8.(;.(;.(5.=R2.)(<.R2.(=.(>.$2.R4.))))(19.$2.(?.(18.$2.R4.R3.)R2.)(?.R4.R2.)))(1:.$2.(?.(18.$2.R4.R3.)R2.)R3.))")
(* [comment removed for export] *).
Proof.
  intros nb sn k Hk. unfold dblk. rewrite app_length in Hk. destruct (Z_lt_dec k (Z.of_nat (length nb))).
  - left. rewrite app_nth1 by lia. split; [lia| reflexivity].
  - right. rewrite app_nth2 by lia. apply nth_In. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L60111930915.6L60111963937.6L62297192733.6L65065749905.600000>00L00Z00hS2bl2sb1j2Hj1nS2bl2sb1j2Hj1lS2bl2sb1j2Hj1nS2bl2sb1j2Hj1l". (* [comment removed for export] *)
#[using="Type"] Lemma sblk_app_cases : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pbl,(3.$2.)Psb,(3.$2.)Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.(18.$2.R3.R2.)))))(8.(;.(;.(5.=R2.)(<.R2.(=.(>.$2.R4.))))(19.$2.(10.(18.$2.R4.R3.)R2.)(10.R4.R2.)))(1:.$2.(10.(18.$2.R4.R3.)R2.)R3.))")
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
#[using="Type"] Lemma allocA_statics_transport2 : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PW,(3.$1;.)PWc,(3.$1;.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PT,$2.PCTX,$2.P,(1<.R4.R2.R1.)P,(11.R7.R5.R4.)P,(11.R7.R6.R5.)P,PA,$2.Pn,$2.P,(8.(;.(5.+10000.R2.)(5.(6.R2.R1.)$9.))(;.(5.$:.R2.)(5.(6.R2.R1.)+65?000.)))(1=.R<.R3.R2.)P,(1=.R9.(6.R5.+98.)+8.)(1<.R8.R7.R6.)")
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
#[using="Type"] Lemma fin_statics_transport2 : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PW,(3.$1;.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))P,(1>.R2.)P,(11.R4.R3.R2.)P,PA,$2.Pn,$2.P,(8.(;.(5.+10000.R2.)(5.(6.R2.R1.)$9.))(;.(5.$:.R2.)(5.(6.R2.R1.)+65?000.)))(1=.R8.R3.R2.)(1>.R4.)")
(* [comment removed for export] *).
Proof.
  intros W m m' S MU DJ. unfold fin_statics in *.
  unfold A_GOT_LSANTLS, A_LSAN_CNT, A_MAGIC_CELL, A_MHOOKS, A_GOT_FLAGS, A_FLAGS, A_FL_MAXFILL, A_FL_FILLB, A_GOT_RMEMSET, A_RMEMSET, A_MUSL_MEMSET, kAllocBegMagic, A_SS, A_DEP_END in *.
  decompose [and] S. repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L30938057274.29L38467752502.34L39087947745.29L50423199290.29L52419108410.29L68363415354.2900000>00Q00_00m01;01IS2nb2tf2bl3DMLS2nb2tf2bl3DML1i2HiS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DML". (* [comment removed for export] *)
#[using="Type"] Lemma depot_inv_transport : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PW,(3.$1;.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PN,$2.Pnb,(3.$2.)Ptf,$2.Pbl,(3.$2.)P,(1?.VhAR,R6.R4.R3.R2.R1.)P,(11.R8.R7.R6.)P,(20.$21.R8.R7.)P,PA,$2.Pn,$2.P,(;.(5.+10000.R2.)(5.(6.R2.R1.)+65?000.))(1=.R=.R3.R2.)P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R8.))))(1=.R=.(?.R9.R2.)(7.+2.+14.))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R7.))))(1=.R>.(10.R8.R2.)(7.+2.+17.))(1?.VhAR,R;.R:.R9.R8.R7.)")
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


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L38467752502.34L42191696609.29L42322306618.29L44454573114.29L45013190714.29L52172301114.2900000C00Q00_00m01;01IS2nb2tf2bl3DML1i2HiS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DML". (* [comment removed for export] *)
#[using="Type"] Lemma depot_inv_transport_z : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PW,(3.$1;.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PN,$2.Pnb,(3.$2.)Ptf,$2.Pbl,(3.$2.)P,(1?.VhAR,R6.R4.R3.R2.R1.)P,(11.R8.R7.R6.)P,(20.$21.R8.R7.)P,PA,$2.Pn,$2.P,(;.(5.$9.R2.)(5.(6.R2.R1.)$:.))(1=.R=.R3.R2.)P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R8.))))(1=.R=.(?.R9.R2.)(7.+2.+14.))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.R7.))))(1=.R>.(10.R8.R2.)(7.+2.+17.))(1?.VhAR,R;.R:.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros W m m' N nb tf bl DI MU WM LO DN DS. unfold A_SS, A_DEP_END in LO.
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

(* [comment removed for export] *)
Definition oe_ok (W : list (Z * Z)) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PA,$2.Pn,$2.P,(;.(5.+10000.R2.)(5.(6.R2.R1.)+65?000.))P,(8.(5.(6.R3.R2.)$22.)(5.(6.$22.+1.)R3.))P,(8.(5.(6.R4.R3.)$23.)(5.(6.$23.+4.)R4.))(1=.O1.R5.R4.)")
(* [comment removed for export] *).
Local Ltac2 Set LiaOrc.tbl := fun () => "01f0?L1016139096.13 L10579485967.19L10929721347.24L10929772047.19L11325592233.24L11718937091.24L11718986767.19L11773891202.14L1250738807.13 L12826460094.18L12828638393.24L12833961688.13L15907591870.24L15907672242.19L15907739199.14L16277462403.24L16277511055.19L17551717508.24L17758015417.24L19254389673.24L20283852969.24L20285901742.18L20581820676.24L21299991079.13L21404241854.24L21404289458.19L21457996718.18L21905285294.24L21905368738.19L23859864489.24L2512665091.19 L2512665091.24 L2512747535.19 L2514843908.24 L2647891247.14 L28672091577.24L28879866809.24L29411425033.14L29831343538.19L31339188484.24L32166266279.13L32989746857.24L33042691843.18L3511064238.24 L3511144610.19 L35157515193.24L35611749124.24L35882884537.24L37388143607.13L38604933380.24L39372486825.24L40564408254.18L4213726649.24 L43102784953.24L43378022447.14L44282745017.24L44423279529.24L44592647097.24L45899836601.24L46294007812.24L47205027753.24L47311045671.19L47914608759.19L4806644649.24 L4879756292.24 L49860406276.24L50491738884.24L50734993074.19L50735073470.24L5130164952.19 L51459284740.24L51656413097.24L51858431678.18L53276602546.19L53276653246.24L53480189759.14L53881541799.13L54356750498.19L54356833966.24L5462968233.24 L5465064098.19 L5465113774.19 L5465113774.24 L55365107460.24L56647939672.13L57103269538.19L57103349934.24L58039122850.19L58039205294.24L59120196343.13L6057249922.14 L6057364483.24 L6057445903.19 L60924711086.18L61006030014.24L61006111410.19L6218487714.19 L62552927279.14L62553254562.19L62553304238.24L64337003433.24L64933078441.24L65987086210.14L66316186628.24L66318366467.18L66856582329.24L67982604687.19L67982688131.24L68321855551.14L7403131058.19 L7403181758.24 L8345788687.19 L8345872131.24 L8670447619.18 L8780515257.24 L8782611122.19 L8782693566.19 L8782693566.24 00000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00D00E00F00G00H00I00J00K00L00M00N00O00P00Q00R00S00T00U00V00W00X00Y00Z00[00\00]00^00_00`00a00b00c00d00e00f00g00h00i00j00k00l00m00n00o01001101201301401501601701801901:01;01<01=01>01?01@01A01B01C01D01E01F01G01H01I01J01K01L01M01N01O01P01Q01R01S01T01U01V01W01X01Y01Z01[01\01]01^01_01`01a01b01c01d01e01fSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSFSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma statics5_transport_oe : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PW,(3.$1;.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PCTX,$2.PT,$2.PSB,$2.P,(11.R6.R5.R4.)P,(24.R7.)P,(1=.R8.(6.R5.+98.)+8.)(;.P,(25.R8.)(25.R8.)(;.P,(26.R8.)(26.R8.)(;.P,(27.R8.R6.R5.)(27.R8.R7.R6.)(;.P,(28.R8.)(28.R8.)P,(29.R8.R4.)(29.R8.R5.)))))")
(* [comment removed for export] *).
Proof.
  intros W m m' CTX T SB MU DJ DJC. unfold oe_ok, A_OOM_CELL, A_ERRNO in DJ.
  split; [| split; [| split; [| split]]].
  - (intros dd_H; ddestruct dd_H as (DS & CS & c1 & c2 & c3 & M1 & M2 & M3)). split; [|split].
    + destruct DS as [G1 G2]. split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ]); unfold A_GOT_CFLAGS, A_CFLAGS; cbn; lia.
    + ddestruct CS as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold cstatics.
      unfold A_GOT_PAGESZ, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_DECORATE, A_MMAP_LIMIT, A_GOT_SEALED2, A_DYING in *.
      split; [|split; [|split; [|split; [|split; [|split]]]]];
        (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
    + dexists c1, c2, c3. unfold A_MUR1, A_MUR2, A_MUR3 in *.
      repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ]); cbn; lia.
  - intros PS. unfold poison_statics in *.
    unfold A_CANPOISON, A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND, A_GOT_RMEMSET, A_RMEMSET, A_GOT_CFLAGS, A_CF_CSMT in *.
    decompose [and] PS. repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
  - (intros dd_H; ddestruct dd_H as (T1 & T2 & T3 & T4)). unfold thr_statics. unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR in *.
    repeat split; first [eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia] | eapply ro_cells_transport; [exact T4| exact MU| exact DJC]].
  - intros MW. unfold mwc_statics in *. unfold A_GOT_PAGESZ, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_DECORATE, A_MMAP_LIMIT, A_GOT_SEALED2, A_GOT_DYING, A_DYING in *.
    decompose [and] MW. repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
  - (intros dd_H; ddestruct dd_H as (P1 & P2 & P3)). unfold pop_statics. unfold A_INTERVAL, A_PREMAPPED, A_INSTANCE in *.
    repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section MallocGenSplit.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  (* [comment removed for export] *)
  Variable CSf : option bool -> option bool -> list Z -> list Z -> Z -> Prop.
  Variable K : option bool -> option bool -> list Z -> list Z -> Model -> Prop.
  Hypothesis CSOKf : forall u f nb bl, cs_ok AL (CSf u f nb bl).
  Hypothesis KL : forall u f nb bl, kinv AL (CSf u f nb bl) (K u f nb bl).
  Hypothesis CSf_noshadow : forall u f nb bl x, CSf u f nb bl x -> ~ (0x7fff8000 <= x < 0x10007fff8000).
  (* [comment removed for export] *)
  Variables (nb0 bl0 : list Z).
  Hypothesis CSmono_u : forall b f y, CSf None f nb0 bl0 y -> CSf (Some b) f nb0 bl0 y.
  Hypothesis CSmono_f : forall u b y, CSf u None nb0 bl0 y -> CSf u (Some b) nb0 bl0 y.
  Hypothesis CSmono_n : forall u f nb bl a x, CSf u f nb bl x -> CSf u f (nb ++ [a]) bl x.
  Hypothesis CSmono_s : forall u f nb bl a x, CSf u f nb bl x -> CSf u f nb (bl ++ [a]) x.

  (* [comment removed for export] *)
  Variables (SP n lo T CTX TOP TID SB RI mu mfa : Z).
  Let c := class_of (needed2 n).
  Let cs := class_size c.
  Let R := RI + 128 * c.
  Let RB := SB + c * 2^32.
  Let FA := RB + 0xE0000000.
  Let UA := RB + mu.
  Let FAA := FA + mfa.
  Let PCR := T + 208 + 80 * c.
  Let STK := SP + -2128.
  Let SPA := SP + -2128 + -16.
  Hypothesis NB : 0 <= n < 2^32.
  Hypothesis FP : from_primary n = true.
  Hypothesis LOIMG : ACEIL <= lo.
  Hypothesis SPL : lo <= SP - 4096.
  Hypothesis SPA16 : SP mod 16 = 0.
  Hypothesis TOP0 : 2^23 <= TOP. Hypothesis TOP1 : TOP <= 2^47. Hypothesis TOP2 : SP + 16 <= 2^47.   (* [comment removed for export] *)
  Hypothesis TIDB : 0 <= TID < 2^31.
  (* [comment removed for export] *)
  Variables (LO TOPU d : Z).
  Hypothesis LOB : LO <= SP.
  Hypothesis TOPUB : TOP <= TOPU <= 2^64.
  Hypothesis GSB : 0x10007fff9000 <= SB /\ SB mod 4096 = 0 /\ RI = SB + 2^37 /\ RI + 4096 <= ACEIL.
  Hypothesis GT : (Timg T /\ Tband T) /\ T + 4096 <= ACEIL /\ T mod 4096 = 0.
  Hypothesis GCTX : (0x65f000 <= CTX /\ Pband CTX 0x10000) /\ CTX + 0x10000 <= ACEIL.
  Hypothesis GSEP : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "(;.(8.(5.(6.VT,+1000.)VSB,)(5.(6.(6.VSB,(7.+2.+25.))+1000.)VT,))(;.(8.(5.(6.VCTX,+10000.)VT,)(5.(6.VT,+1000.)VCTX,))(8.(5.(6.VCTX,+10000.)VSB,)(5.(6.(6.VSB,(7.+2.+25.))+1000.)VCTX,))))")
(* [comment removed for export] *).
  Hypothesis GMU : 0 <= mu /\ mu mod 4096 = 0 /\ mu <= 0xE0000000.
  Hypothesis GMFA : 0 <= mfa /\ mfa mod 2^18 = 0 /\ mfa + 2^18 <= 2^29.

  (* [comment removed for export] *)
  Hypothesis LEDGER_U : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pmo,$2:.P,(5.(6.Vmu,(7.+2.+12.))+>0000000.)P,A5.VK,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,R2.(;.(19.$2<.(2=.(2>.(2?.R3.))(30.&40.VUA,)(30.&40.(7.+2.+12.)))$31.)(8.(19.$2<.(32.(33.(2?.R3.))(30.&40.VUA,)(30.&40.(7.+2.+12.)))$31.)(19.$2<.(2=.(18.(13.(0.&40.)(0.&40.))(2>.(2?.R3.))(33.(2?.R3.)))(30.&40.VUA,)(30.&40.(7.+2.+12.)))$31.)))")
(* [comment removed for export] *).
  Hypothesis TU_commit : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pmo,$2:.P,(5.(6.Vmu,(7.+2.+12.))+>0000000.)P,A5.VK,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,R2.P,(19.$2<.(32.(33.(2?.R3.))(30.&40.VUA,)(30.&40.(7.+2.+12.)))$31.)A5.VK,(34.$2<.$31.)(2;.$2<.)Vnb0,Vbl0,(35.+32.VUA,(7.+2.+12.)R4.)")
(* [comment removed for export] *).
  Hypothesis TU_fresh : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pmo,$2:.P,(5.(6.Vmu,(7.+2.+12.))+>0000000.)P,A5.VK,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,R2.P,(19.$2<.(2=.(18.(13.(0.&40.)(0.&40.))(2>.(2?.R3.))(33.(2?.R3.)))(30.&40.VUA,)(30.&40.(7.+2.+12.)))$31.)A5.VK,(34.$2<.$31.)(2;.$2<.)Vnb0,Vbl0,(36.+32.VUA,(7.+2.+12.)R4.)")
(* [comment removed for export] *).
  Hypothesis LEDGER_F : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pu,(1.$2<.)Pmo,$2:.P,(8.(19.(1.$2<.)R2.(2;.$2<.))(19.(1.$2<.)R2.(34.$2<.$31.)))P,A5.VK,R3.(2;.$2<.)Vnb0,Vbl0,R2.(;.(19.$2<.(2=.(2>.(2?.R3.))(30.&40.VFAA,)(30.&40.(7.+2.+12.)))$31.)(8.(19.$2<.(32.(33.(2?.R3.))(30.&40.VFAA,)(30.&40.(7.+2.+12.)))$31.)(19.$2<.(2=.(18.(13.(0.&40.)(0.&40.))(2>.(2?.R3.))(33.(2?.R3.)))(30.&40.VFAA,)(30.&40.(7.+2.+12.)))$31.)))")
(* [comment removed for export] *).
  Hypothesis TF_commit : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pu,(1.$2<.)Pmo,$2:.P,(8.(19.(1.$2<.)R2.(2;.$2<.))(19.(1.$2<.)R2.(34.$2<.$31.)))P,A5.VK,R3.(2;.$2<.)Vnb0,Vbl0,R2.P,(19.$2<.(32.(33.(2?.R3.))(30.&40.VFAA,)(30.&40.(7.+2.+12.)))$31.)A5.VK,R5.(34.$2<.$31.)Vnb0,Vbl0,(35.+32.VFAA,(7.+2.+12.)R4.)")
(* [comment removed for export] *).
  Hypothesis TF_fresh : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pu,(1.$2<.)Pmo,$2:.P,(8.(19.(1.$2<.)R2.(2;.$2<.))(19.(1.$2<.)R2.(34.$2<.$31.)))P,A5.VK,R3.(2;.$2<.)Vnb0,Vbl0,R2.P,(19.$2<.(2=.(18.(13.(0.&40.)(0.&40.))(2>.(2?.R3.))(33.(2?.R3.)))(30.&40.VFAA,)(30.&40.(7.+2.+12.)))$31.)A5.VK,R5.(34.$2<.$31.)Vnb0,Vbl0,(36.+32.VFAA,(7.+2.+12.)R4.)")
(* [comment removed for export] *).
  Hypothesis ROOM_U : forall mo, mu + 2^18 <= 0xE0000000 -> K None None nb0 bl0 mo -> fixrw_grantable 0x32 UA (2^18) mo.
  (* [comment removed for export] *)
  Hypothesis SCAR_U : mu + 2^18 <= 0xE0000000 -> scar_site AL (CSf None None nb0 bl0) (K None None nb0 bl0) UA (2^18).
  Hypothesis ROOM_F : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pu,(1.$2<.)Pmo,$2:.P,(8.(19.(1.$2<.)R2.(2;.$2<.))(19.(1.$2<.)R2.(34.$2<.$31.)))P,A5.VK,R3.(2;.$2<.)Vnb0,Vbl0,R2.(37.+32.VFAA,(7.+2.+12.)R3.)")
(* [comment removed for export] *).
  Hypothesis SCAR_F : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pu,(1.$2<.)P,(8.(19.(1.$2<.)R1.(2;.$2<.))(19.(1.$2<.)R1.(34.$2<.$31.)))(38.VhAR,VAL,A4.VCSf,R2.(2;.$2<.)Vnb0,Vbl0,A4.VK,R2.(2;.$2<.)Vnb0,Vbl0,VFAA,(7.+2.+12.))")
(* [comment removed for export] *).
  Hypothesis CSUz : forall f, crange (CSf (Some true) f nb0 bl0) UA (2^18).
  Hypothesis CSFz : forall u, crange (CSf u (Some true) nb0 bl0) FAA (2^18).

  (* [comment removed for export] *)
  Hypothesis K_apart : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pu,(1.$2<.)Pf,(1.$2<.)Pnb,(3.$2.)Pbl,(3.$2.)Pmo,$2:.Pa,(0.&40.)Pw,(0.&40.)P,A5.VK,R7.R6.R5.R4.R3.P,(19.$2<.(2=.(18.(13.(0.&40.)(0.&40.))(2>.(2?.R4.))(33.(2?.R4.)))R3.R2.)$31.)P,(5.+10000.(39.&40.R3.))P,(5.(6.(39.&40.R5.)(39.&40.R4.))(3:.VhAR,))Px,$2.P,(8.A5.VCSf,R<.R;.R:.R9.R1.(;.(5.(3;.VAL,)R1.)(<.R1.(3<.VAL,))))(17.(;.(5.(39.&40.R8.)R2.)(<.R2.(6.(39.&40.R8.)(39.&40.R7.)))))")
(* [comment removed for export] *).
  Variables (Gn Gs : option bool -> option bool -> list Z -> list Z -> Prop).
  Hypothesis T_node : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pu,(1.$2<.)Pf,(1.$2<.)Pnb,(3.$2.)Pbl,(3.$2.)Pmo,$2:.Pa,(0.&40.)P,A4.VGn,R6.R5.R4.R3.P,A5.VK,R7.R6.R5.R4.R3.P,(19.$2.(3=.(39.&40.R3.)+1000.)=)P,(<.=(39.&40.R4.))P,(5.(6.(39.&40.R5.)(7.+2.+14.))(3:.VhAR,))P,(19.$2<.(2=.(18.(13.(0.&40.)(0.&40.))(2>.(2?.R7.))(33.(2?.R7.)))R6.(30.&40.(7.+2.+14.)))$31.)(;.A5.VK,R<.R;.(18.$2.R:.(12.$2.(39.&40.R7.)(15.$2.)))R9.(3>.+22.R7.(7.+2.+14.)R8.)(16.A4.VCSf,R<.R;.(18.$2.R:.(12.$2.(39.&40.R7.)(15.$2.)))R9.(39.&40.R7.)(7.+2.+14.)))")
(* [comment removed for export] *).
  Hypothesis T_store : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pu,(1.$2<.)Pf,(1.$2<.)Pnb,(3.$2.)Pbl,(3.$2.)Pmo,$2:.Pa,(0.&40.)P,A4.VGs,R6.R5.R4.R3.P,A5.VK,R7.R6.R5.R4.R3.P,(19.$2.(3=.(39.&40.R3.)+1000.)=)P,(<.=(39.&40.R4.))P,(5.(6.(39.&40.R5.)(7.+2.+17.))(3:.VhAR,))P,(19.$2<.(2=.(18.(13.(0.&40.)(0.&40.))(2>.(2?.R7.))(33.(2?.R7.)))R6.(30.&40.(7.+2.+17.)))$31.)(;.A5.VK,R<.R;.R:.(18.$2.R9.(12.$2.(39.&40.R7.)(15.$2.)))(3>.+4022.R7.(7.+2.+17.)R8.)(16.A4.VCSf,R<.R;.R:.(18.$2.R9.(12.$2.(39.&40.R7.)(15.$2.)))(39.&40.R7.)(7.+2.+17.)))")
(* [comment removed for export] *).
  Hypothesis ROOM_n : forall u f nb bl mo, Gn u f nb bl -> K u f nb bl mo -> exists a, anon_grantable 0x22 (2^20) mo a.
  Hypothesis ROOM_s : forall u f nb bl mo, Gs u f nb bl -> K u f nb bl mo -> exists a, anon_grantable 0x4022 (2^23) mo a.

  (* [comment removed for export] *)
  Definition fchunk (m : mem) (au : Z) (p : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Zoff,$2.(3?.+10.(3=.(39.&40.O1.)(7.+2.+20.)))(;.(5.(6.R1.Vcs,)O2.)(;.(40.(3.(0.&8.))Lbs,(3.(0.&8.))(41.$21.O3.(6.VRB,R2.)(12.$42.(43.(44.Vcs,)R1.)(15.$42.))))(40.(0.&8.)Lsh0,(0.&8.)(40.(3.(0.&8.))Lshs,(3.(0.&8.))(;.(41.$21.O3.(6.+7???8000.(45.(6.VRB,R3.)+8.))(12.$42.(46.R2.)(12.$42.(43.(44.(47.(45.Vcs,+8.)+1.))R1.)(15.$42.))))(17.(19.$2.(39.&8.R2.)=)))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition gkeep (W : list (Z * Z)) (m m' : mem) (nb bl : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Px,(0.&40.)Za,$2.(39.&40.R1.)P,(48.O5.R1.)P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.O2.))))(17.(;.(5.(?.O2.R2.)R4.)(<.R4.(6.(?.O2.R2.)(7.+2.+14.)))))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.O1.))))(17.(;.(5.(10.O1.R2.)R5.)(<.R5.(6.(10.O1.R2.)(7.+2.+17.)))))(19.(1.(0.&8.))A1.O3.R5.A1.O4.R5.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition mgen_windows (Wx : list (Z * Z)) : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "(12.(13.$2.$2.)(14.$2.$2.Vlo,VSP,)(12.(13.$2.$2.)(14.$2.$2.$9.$:.)(12.(13.$2.$2.)(14.$2.$2.(6.VT,+<60.)(6.VT,+<61.))(12.(13.$2.$2.)(14.$2.$2.(6.VT,+:>0.)(6.VT,+:>8.))(12.(13.$2.$2.)(14.$2.$2.(6.VT,+:>8.)(6.VT,+:?0.))(12.(13.$2.$2.)(14.$2.$2.(6.VT,+:?0.)(6.VT,+<60.))(12.(13.$2.$2.)(14.$2.$2.(6.VT,+;38.)(6.VT,+;48.))(12.(13.$2.$2.)(14.$2.$2.VUA,(6.VUA,(7.+2.+12.)))(12.(13.$2.$2.)(14.$2.$2.(6.+7???8000.(45.VUA,+8.))(6.(6.+7???8000.(45.VUA,+8.))+8000.))(12.(13.$2.$2.)(14.$2.$2.VFA,(6.VFAA,(7.+2.+12.)))(12.(13.$2.$2.)(14.$2.$2.(6.+7???8000.(45.VFAA,+8.))(6.(6.+7???8000.(45.VFAA,+8.))+8000.))(12.(13.$2.$2.)(14.$2.$2.VR,(6.VR,+8.))(12.(13.$2.$2.)(14.$2.$2.(6.VR,+10.)(6.VR,+18.))(12.(13.$2.$2.)(14.$2.$2.(6.VR,+18.)(6.VR,+20.))(12.(13.$2.$2.)(14.$2.$2.(6.VR,+20.)(6.VR,+28.))(12.(13.$2.$2.)(14.$2.$2.(6.VR,+30.)(6.VR,+38.))(12.(13.$2.$2.)(14.$2.$2.(6.VR,+44.)(6.VR,+45.))(12.(13.$2.$2.)(14.$2.$2.(6.VR,+48.)(6.VR,+50.))(12.(13.$2.$2.)(14.$2.$2.$22.(6.$22.+1.))(12.(13.$2.$2.)(14.$2.$2.$23.(6.$23.+4.))O1.))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition pgw : Z := if nfix n mod 8 =? 0 then 0 else 1.

  (* [comment removed for export] *)
  Definition mgen_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (N tf au nf cnt : Z) (exb : bv 8) (csw j0 j1 j2 : word) (fa js0 ds bs : list word) (shU shF : list byte) (oomb : byte) (e0 : word)
      (Wx : list (Z * Z)) (X : mem -> Prop) (m0 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Lcf,$49.(40.$4:.Lms',$4:.(40.$2:.Lmo',$2:.(40.$2.Lres,$2.(40.(1.$2<.)Lu,(1.$2<.)(40.(1.$2<.)Lf,(1.$2<.)(40.(3.$2.)Lnb',(3.$2.)(40.(3.$2.)Lbl',(3.$2.)(40.(0.&40.)Lt0,(0.&40.)(40.(0.&40.)Lt1,(0.&40.)(40.(0.&40.)Lt2,(0.&40.)(40.(0.&40.)La1,(0.&40.)(40.(0.&40.)La2,(0.&40.)(40.(0.&40.)La3,(0.&40.)(40.(0.&40.)La4,(0.&40.)(40.(0.&40.)La5,(0.&40.)(40.(0.&40.)La6,(0.&40.)(40.(0.&40.)La7,(0.&40.)(40.(0.&40.)Lt3,(0.&40.)(40.(0.&40.)Lt4,(0.&40.)(40.(0.&40.)Lt5,(0.&40.)(40.(0.&40.)Lt6,(0.&40.)(40.(0.&40.)Lstw',(0.&40.)(40.(0.&40.)Lcstw',(0.&40.)(40.(0.&40.)Lj1',(0.&40.)(40.(0.&40.)Lj2',(0.&40.)(40.(0.&40.)Lj3',(0.&40.)(40.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))Zmu',$2.(6.Vmu,(4;.R18.))Zmfa',$2.(6.Vmfa,(4;.R18.))Znw,$2.(45.(47.R2.O13.)Vcs,)Zk,$2.(45.(4<.Vc,)+2.)(;.(19.$49.R20.(4=.R1?.R1>.))(;.(19.$4:.R1?.(4>.(4?.O25.(30.&40.VSP,)O24.(30.&40.$50.)R18.R17.R16.O23.O22.(30.&40.R1=.)R15.R14.R13.R12.R11.R10.R?.O21.O20.O1?.O1>.O1=.O1<.O1;.O1:.O19.O18.R>.R=.R<.R;.)O17.(51.O25.)O16.(2;.(0.&40.))R5.(52.$21.)))(;.A5.VK,R1<.R1;.R1:.R19.R1>.(;.(53.R5.R1>.)(;.(;.(5.R4.+>0000000.)(5.(47.R4.O13.)(7.+2.+13.)))(;.(20.$21.O1.R5.)(;.(54.$21.R5.)(;.(55.$21.R5.Vlo,VSP,)(;.Px,$2.P,A5.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,R1.A5.VCSf,R1>.R1=.R1<.R1;.R2.(;.(25.R5.)(;.(26.R5.)(;.(27.R5.VCTX,VT,)(;.(28.R5.)(;.(29.R5.VSB,)(;.(41.$21.R5.VR,(12.$42.(56.(30.&40.=))(15.$42.)))(;.(41.$21.R5.(6.VR,+18.)(12.$42.(56.(30.&40.R3.))(15.$42.)))(;.(41.$21.R5.(6.VR,+28.)(12.$42.(56.(30.&40.=))(15.$42.)))(;.(41.$21.R5.(6.VR,+30.)(12.$42.(56.(30.&40.R4.))(15.$42.)))(;.(41.$21.R5.(6.VR,+38.)(12.$42.(56.(30.&40.=))(15.$42.)))(;.(41.$21.R5.(6.VR,+48.)(12.$42.(56.R:.)(15.$42.)))(;.(41.$21.R5.(6.VT,+:>0.)(12.$42.(56.R9.)(15.$42.)))(;.(41.$21.R5.(6.VT,+;38.)(12.$42.(56.R8.)(12.$42.(56.R7.)(15.$42.))))(;.(41.$21.R5.(6.VT,+:>8.)(12.$42.(56.R6.)(15.$42.)))(;.P,(19.(1.$2<.)R1;.(34.$2<.$31.))(41.$21.R6.(6.+7???8000.(45.VFAA,+8.))(12.$42.(43.(44.+8000.)(57.(0.&8.)(30.&8.+?:.)(44.+8000.)))(15.$42.)))(;.P,(17.(19.(1.$2<.)R1;.(34.$2<.$31.)))(41.$21.R6.(6.+7???8000.(45.VFAA,+8.))(12.$42.(43.(44.+8000.)O6.)(15.$42.)))(;.P,(17.(19.(1.$2<.)R1<.(34.$2<.$31.)))P,(5.(6.Vmu,(7.+2.+12.))+>0000000.)(41.$21.R7.(6.+7???8000.(45.VUA,+8.))(12.$42.(43.(44.+8000.)O7.)(15.$42.)))(;.(41.$21.R5.(6.VT,+<60.)(12.$42.(46.(30.&8.=))(15.$42.)))(;.A1.O2.R5.(8.(;.(19.$2.R1=.=)(;.(17.(19.(1.$2<.)R1;.(34.$2<.$31.)))(;.(19.$2.O11.=)(;.(19.(3.$2.)R1:.Vnb0,)(;.(19.(3.$2.)R19.Vbl0,)(;.(58.(59.O3.)O1.R5.Vnb0,Vbl0,)(;.(1?.VhAR,R5.O15.Vnb0,O14.Vbl0,)(;.(41.$21.R5.VPCR,(12.$42.(5:.(30.&40.=))(12.$42.(5:.(30.&40.(4<.Vc,)))(12.$42.(56.O?.)(15.$42.)))))(;.(5;.$21.R5.(6.VPCR,+10.)O9.)(;.(41.$21.R5.(6.VR,+10.)(12.$42.(56.(30.&40.O12.))(15.$42.)))(;.(41.$21.R5.(6.VR,+20.)(12.$42.(56.(30.&40.O13.))(15.$42.)))(;.(41.$21.R5.(6.VR,+44.)(12.$42.(46.O10.)(15.$42.)))(;.(5;.$21.R5.VFA,O;.)(;.(5;.$21.R5.(6.VFA,(3?.+4.O12.))O:.)(;.P,(19.(1.$2<.)R1<.(34.$2<.$31.))(;.(41.$21.R6.VUA,(12.$42.(43.(44.(7.+2.+12.))(57.(0.&8.)(30.&8.=)(44.(7.+2.+12.))))(15.$42.)))(41.$21.R6.(6.+7???8000.(45.VUA,+8.))(12.$42.(43.(44.+8000.)(57.(0.&8.)(30.&8.+?:.)(44.+8000.)))(15.$42.))))(;.(41.$21.R5.$22.(12.$42.(46.(30.&8.+1.))(15.$42.)))(;.(41.$21.R5.$23.(12.$42.(5:.(30.&40.+<.))(15.$42.)))(;.(41.$21.R5.(6.VT,+:?0.)(12.$42.(56.O>.)(12.$42.(56.O=.)(12.$42.(56.O<.)(15.$42.)))))(5<.$21.R5.(6.VT,+;60.)O8.)))))))))))))))))))(40.$2.LAB,$2.(40.$2.Lcnt',$2.(40.(3.(0.&40.))Lds',(3.(0.&40.))(40.(0.&40.)Lpw,(0.&40.)(40.$2.LN',$2.(40.$2.Ltf',$2.(40.$2.Lid,$2.(40.$2.Lb1',$2.(40.(0.&8.)Lpgb,(0.&8.)(40.(0.&40.)Lsj0,(0.&40.)(40.(0.&40.)Lsj1,(0.&40.)(40.(0.&40.)Lsj2,(0.&40.)(40.(3.(0.&40.))Lbs',(3.(0.&40.))ZUB,$2.(6.R=.(5=.Vn,))ZCHB,$2.(6.R1.-10.)ZSUB,$2.(6.+7???8000.(45.R2.+8.))ZPGS,$2.(6.+7???8000.(5>.(6.R3.(3?.(45.(5?.Vn,)+8.)+8.))+3.))ZKF,$2.(60.(5?.Vn,)+1000.)ZCW,(3.(13.$2.$2.))(12.(13.$2.$2.)(14.$2.$2.R4.(6.R4.+10.))(12.(13.$2.$2.)(14.$2.$2.R12.(6.R12.+10.))(12.(13.$2.$2.)(14.$2.$2.R5.(6.R5.R1.))(15.(13.$2.$2.)))))ZSW,(3.(13.$2.$2.))(12.(13.$2.$2.)(14.$2.$2.R4.(6.R4.(45.(5?.Vn,)+8.)))(12.(13.$2.$2.)(14.$2.$2.R3.(6.R3.$61.))(15.(13.$2.$2.))))(;.(19.$2.R31.R7.)(;.(19.$2.R14.(6.VRB,(3?.+10.(3=.(39.&40.R11.)(7.+2.+20.)))))(;.(;.(5.+1.R13.)(5.R13.+10.))(;.(19.(1.(0.&40.))(62.(0.&40.)R12.(44.(47.R13.+1.)))(34.(0.&40.)R11.))(;.(19.$63.(>.(0.&40.)R12.)#10.)(;.(58.(18.(13.$2.$2.)R2.(18.(13.$2.$2.)R1.(59.O3.)))O1.R19.R2>.R2=.)(;.(41.$21.R19.VPCR,(12.$42.(5:.(30.&40.(47.R13.+1.)))(12.$42.(5:.(30.&40.(4<.Vc,)))(12.$42.(56.O?.)(15.$42.)))))(;.(5;.$21.R19.(6.VPCR,+10.)R12.)(;.(8.(;.(19.$2.R13.O11.)(;.(19.(3.(0.&40.))R12.O9.)(;.(19.(1.$2<.)R30.(2;.$2<.))(;.(19.(1.$2<.)R2?.(2;.$2<.))(;.(41.$21.R19.(6.VR,+10.)(12.$42.(56.(30.&40.O12.))(15.$42.)))(;.(41.$21.R19.(6.VR,+20.)(12.$42.(56.(30.&40.O13.))(15.$42.)))(;.(41.$21.R19.(6.VR,+44.)(12.$42.(46.O10.)(15.$42.)))(;.(5;.$21.R19.VFA,O;.)(5;.$21.R19.(6.VFA,(3?.+4.O12.))O:.)))))))))(;.(19.$2.O11.=)(;.(19.$2.R13.R15.)(;.(17.(19.(1.$2<.)R30.(34.$2<.$64.)))(;.(17.(19.(1.$2<.)R2?.(34.$2<.$64.)))(40.(3.(0.&40.))Lnew,(3.(0.&40.))(40.(3.(0.&40.))Lws,(3.(0.&40.))(40.(3.(0.&40.))Lfa',(3.(0.&40.))(40.(3.(0.&40.))Lrest,(3.(0.&40.))(40.$2.Lnf',$2.(40.$2.Lau',$2.(40.(0.&8.)Lex',(0.&8.)(;.(19.(3.(0.&40.))R19.(65.(44.R1<.)R6.O9.))(;.(19.(3.(0.&40.))(18.(0.&40.)O;.R7.)(18.(0.&40.)R5.R6.))(;.(19.$63.(>.(0.&40.)R6.)(44.R1<.))(;.(19.$2.(=.(>.(0.&40.)R5.))R3.)(;.(8.(;.(19.(3.(0.&40.))R7.(15.(0.&40.)))(;.(19.(1.$2<.)R37.(2;.$2<.))(;.(19.(1.$2<.)R36.(2;.$2<.))(;.(5.R1<.O12.)(;.(19.$2.R2.O13.)(19.(0.&8.)R1.O10.))))))(;.(19.(3.(0.&40.))R7.(66.O13.Vcs,(44.R1=.)))(;.(<.O12.R1<.)(;.(5.(47.R1<.O12.)R1=.)(;.(19.$2.R2.(6.O13.(3?.R1=.Vcs,)))(;.(19.(0.&8.)R1.(30.&8.=))(;.(<.=R1=.)P,(19.(1.$2<.)R36.(34.$2<.$31.))(<.Vmfa,(3?.+4.(6.O12.R1>.))))))))))(;.(41.$21.R20.(6.VR,+10.)(12.$42.(56.(30.&40.R3.))(15.$42.)))(;.(41.$21.R20.(6.VR,+20.)(12.$42.(56.(30.&40.R2.))(15.$42.)))(;.(41.$21.R20.(6.VR,+44.)(12.$42.(46.R1.)(15.$42.)))(;.(5;.$21.R20.VFA,R5.)(;.(5;.$21.R20.(6.VFA,(3?.+4.R3.))R4.)(19.$2.(3?.+4.(6.R3.(=.(>.(0.&40.)R4.))))R1>.)))))))))))))))))))))))(;.P,(19.(1.$2<.)R30.(34.$2<.$31.))(40.(3.(0.&8.))Lzb,(3.(0.&8.))(40.(3.(0.&8.))Lush,(3.(0.&8.))(;.(41.$21.R1<.VUA,(12.$42.(43.(44.(7.+2.+12.))R2.)(15.$42.)))(;.(41.$21.R1<.(6.+7???8000.(45.VUA,+8.))(12.$42.(43.(44.+8000.)R1.)(15.$42.)))(;.Pi,$63.P,(67.R1.(44.(7.+2.+12.)))P,(48.R7.(6.VUA,(=.R2.)))(19.(1.(0.&8.))(62.(0.&8.)R5.R3.)(34.(0.&8.)(30.&8.=)))Pi,$63.P,(67.R1.(44.+8000.))P,(48.R6.(6.(6.+7???8000.(45.VUA,+8.))(=.R2.)))(19.(1.(0.&8.))(62.(0.&8.)R4.R3.)(34.(0.&8.)(30.&8.+?:.))))))))(;.(1?.VhAR,R19.R10.R2>.R?.R2=.)(;.(68.A4.VCSf,R30.R2?.R2>.R2=.R2>.R2=.)(;.(;.(5.+1.R>.)(5.R>.R10.))(;.(;.(5.O15.R10.)(5.R10.(6.O15.+1.)))(;.(;.(5.O14.R?.)(5.R?.(6.O14.(3?.+2.(6.Vd,+3.)))))(;.(5.(47.R?.(3?.+1?.(45.R?.(7.+2.+14.))))(6.(47.O14.(3?.+1?.(45.O14.(7.+2.+14.))))(6.Vd,+3.)))(;.(40.(3.$2.)Lsn,(3.$2.)(40.(3.$2.)Lsb,(3.$2.)(;.(19.(3.$2.)R30.(18.$2.Vnb0,R2.))(;.(19.(3.$2.)R2?.(18.$2.Vbl0,R1.))(;.(69.$2.Lb,$2.Px,$2.P,A5.VCSf,R34.R33.Vnb0,Vbl0,R1.(17.(;.(5.R3.R2.)(<.R2.(6.R3.(7.+2.+14.)))))R2.)(69.$2.Lb,$2.Px,$2.P,A5.VCSf,R34.R33.Vnb0,Vbl0,R1.(17.(;.(5.R3.R2.)(<.R2.(6.R3.(7.+2.+17.)))))R1.))))))(;.(16.A4.VCSf,R30.R2?.R2>.R2=.R14.Vcs,)(;.(41.$21.R19.R6.(12.$42.(46.(30.&8.$6:.))(12.$42.(46.(30.&8.R=.))(12.$42.(6;.(30.&40.=))(12.$42.(5:.(30.&40.(5?.Vn,)))(12.$42.(56.(30.&40.(6<.(3?.VTID,(7.+2.+20.))R>.)))(15.$42.)))))))(;.(19.$2.(6=.R=.+3.)+1.)(;.(;.(5.=R=.)(<.R=.+100.))(;.P,(<.+10.(5=.Vn,))(41.$21.R1:.R15.(12.$42.(56.(30.&40.$6>.))(12.$42.(56.(30.&40.R7.))(15.$42.))))(;.(41.$21.R19.R5.(12.$42.(43.(44.(45.(5?.Vn,)+8.))(57.(0.&8.)(30.&8.=)(44.(45.(5?.Vn,)+8.))))(15.$42.)))(;.(41.$21.R19.R4.(12.$42.(46.(6?.Vn,R<.))(15.$42.)))(;.(41.$21.R19.R7.(12.$42.(43.(44.R3.)(57.(0.&8.)(30.&8.+;>.)(44.R3.)))(15.$42.)))(;.(41.$21.R19.(6.VT,+:?0.)(12.$42.(56.R;.)(12.$42.(56.R:.)(12.$42.(56.R9.)(15.$42.)))))(;.(5<.$21.R19.(6.VT,+;60.)R8.)(;.(19.$63.(>.(0.&40.)R8.)#20.)(;.(41.$21.R19.$22.(12.$42.(46.O5.)(15.$42.)))(41.$21.R19.$23.(12.$42.(5:.O4.)(15.$42.)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition mgen_postN (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (N tf au nf cnt : Z) (exb : bv 8) (csw j0 j1 j2 : word) (fa js0 ds bs : list word) (shU shF : list byte) (oomb : byte) (e0 : word)
      (Wx : list (Z * Z)) (X : mem -> Prop) (m0 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Lcf,$49.(40.$4:.Lms',$4:.(40.$2:.Lmo',$2:.(40.$2.Lres,$2.(40.(1.$2<.)Lu,(1.$2<.)(40.(1.$2<.)Lf,(1.$2<.)(40.(3.$2.)Lnb',(3.$2.)(40.(3.$2.)Lbl',(3.$2.)(40.(0.&40.)Lt0,(0.&40.)(40.(0.&40.)Lt1,(0.&40.)(40.(0.&40.)Lt2,(0.&40.)(40.(0.&40.)La1,(0.&40.)(40.(0.&40.)La2,(0.&40.)(40.(0.&40.)La3,(0.&40.)(40.(0.&40.)La4,(0.&40.)(40.(0.&40.)La5,(0.&40.)(40.(0.&40.)La6,(0.&40.)(40.(0.&40.)La7,(0.&40.)(40.(0.&40.)Lt3,(0.&40.)(40.(0.&40.)Lt4,(0.&40.)(40.(0.&40.)Lt5,(0.&40.)(40.(0.&40.)Lt6,(0.&40.)(40.(0.&40.)Lstw',(0.&40.)(40.(0.&40.)Lcstw',(0.&40.)(40.(0.&40.)Lj1',(0.&40.)(40.(0.&40.)Lj2',(0.&40.)(40.(0.&40.)Lj3',(0.&40.)(40.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))Zmu',$2.(6.Vmu,(4;.R18.))Zmfa',$2.(6.Vmfa,(4;.R18.))Znw,$2.(45.(47.R2.O13.)Vcs,)Zk,$2.(45.(4<.Vc,)+2.)(;.(19.$49.R20.(4=.R1?.R1>.))(;.(19.$4:.R1?.(4>.(4?.O25.(30.&40.VSP,)O24.(30.&40.$50.)R18.R17.R16.O23.O22.(30.&40.R1=.)R15.R14.R13.R12.R11.R10.R?.O21.O20.O1?.O1>.O1=.O1<.O1;.O1:.O19.O18.R>.R=.R<.R;.)O17.(51.O25.)O16.(2;.(0.&40.))R5.(52.$21.)))(;.A5.VK,R1<.R1;.R1:.R19.R1>.(;.(53.R5.R1>.)(;.(;.(5.R4.+>0000000.)(5.(47.R4.O13.)(7.+2.+13.)))(;.(20.$21.O1.R5.)(;.(54.$21.R5.)(;.(55.$21.R5.Vlo,VSP,)(;.Px,$2.P,A5.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,R1.A5.VCSf,R1>.R1=.R1<.R1;.R2.(;.(25.R5.)(;.(26.R5.)(;.(27.R5.VCTX,VT,)(;.(28.R5.)(;.(29.R5.VSB,)(;.(41.$21.R5.VR,(12.$42.(56.(30.&40.=))(15.$42.)))(;.(41.$21.R5.(6.VR,+18.)(12.$42.(56.(30.&40.R3.))(15.$42.)))(;.(41.$21.R5.(6.VR,+28.)(12.$42.(56.(30.&40.=))(15.$42.)))(;.(41.$21.R5.(6.VR,+30.)(12.$42.(56.(30.&40.R4.))(15.$42.)))(;.(41.$21.R5.(6.VR,+38.)(12.$42.(56.(30.&40.=))(15.$42.)))(;.(41.$21.R5.(6.VR,+48.)(12.$42.(56.R:.)(15.$42.)))(;.(41.$21.R5.(6.VT,+:>0.)(12.$42.(56.R9.)(15.$42.)))(;.(41.$21.R5.(6.VT,+;38.)(12.$42.(56.R8.)(12.$42.(56.R7.)(15.$42.))))(;.(41.$21.R5.(6.VT,+:>8.)(12.$42.(56.R6.)(15.$42.)))(;.P,(19.(1.$2<.)R1;.(34.$2<.$31.))(41.$21.R6.(6.+7???8000.(45.VFAA,+8.))(12.$42.(43.(44.+8000.)(57.(0.&8.)(30.&8.+?:.)(44.+8000.)))(15.$42.)))(;.P,(17.(19.(1.$2<.)R1;.(34.$2<.$31.)))(41.$21.R6.(6.+7???8000.(45.VFAA,+8.))(12.$42.(43.(44.+8000.)O6.)(15.$42.)))(;.P,(17.(19.(1.$2<.)R1<.(34.$2<.$31.)))P,(5.(6.Vmu,(7.+2.+12.))+>0000000.)(41.$21.R7.(6.+7???8000.(45.VUA,+8.))(12.$42.(43.(44.+8000.)O7.)(15.$42.)))(;.(41.$21.R5.(6.VT,+<60.)(12.$42.(46.(30.&8.=))(15.$42.)))(;.A1.O2.R5.(;.(19.$2.R1=.=)(;.(17.(19.(1.$2<.)R1;.(34.$2<.$31.)))(;.(19.$2.O11.=)(;.(19.(3.$2.)R1:.Vnb0,)(;.(19.(3.$2.)R19.Vbl0,)(;.(58.(59.O3.)O1.R5.Vnb0,Vbl0,)(;.(1?.VhAR,R5.O15.Vnb0,O14.Vbl0,)(;.(41.$21.R5.VPCR,(12.$42.(5:.(30.&40.=))(12.$42.(5:.(30.&40.(4<.Vc,)))(12.$42.(56.O?.)(15.$42.)))))(;.(5;.$21.R5.(6.VPCR,+10.)O9.)(;.(41.$21.R5.(6.VR,+10.)(12.$42.(56.(30.&40.O12.))(15.$42.)))(;.(41.$21.R5.(6.VR,+20.)(12.$42.(56.(30.&40.O13.))(15.$42.)))(;.(41.$21.R5.(6.VR,+44.)(12.$42.(46.O10.)(15.$42.)))(;.(5;.$21.R5.VFA,O;.)(;.(5;.$21.R5.(6.VFA,(3?.+4.O12.))O:.)(;.P,(19.(1.$2<.)R1<.(34.$2<.$31.))(;.(41.$21.R6.VUA,(12.$42.(43.(44.(7.+2.+12.))(57.(0.&8.)(30.&8.=)(44.(7.+2.+12.))))(15.$42.)))(41.$21.R6.(6.+7???8000.(45.VUA,+8.))(12.$42.(43.(44.+8000.)(57.(0.&8.)(30.&8.+?:.)(44.+8000.)))(15.$42.))))(;.(41.$21.R5.$22.(12.$42.(46.(30.&8.+1.))(15.$42.)))(;.(41.$21.R5.$23.(12.$42.(5:.(30.&40.+<.))(15.$42.)))(;.(41.$21.R5.(6.VT,+:?0.)(12.$42.(56.O>.)(12.$42.(56.O=.)(12.$42.(56.O<.)(15.$42.)))))(5<.$21.R5.(6.VT,+;60.)O8.))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Definition mgen_postC (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (N tf au nf cnt : Z) (exb : bv 8) (csw j0 j1 j2 : word) (fa js0 ds bs : list word) (shU shF : list byte) (oomb : byte) (e0 : word)
      (Wx : list (Z * Z)) (X : mem -> Prop) (m0 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Lcf,$49.(40.$4:.Lms',$4:.(40.$2:.Lmo',$2:.(40.$2.Lres,$2.(40.(1.$2<.)Lu,(1.$2<.)(40.(1.$2<.)Lf,(1.$2<.)(40.(3.$2.)Lnb',(3.$2.)(40.(3.$2.)Lbl',(3.$2.)(40.(0.&40.)Lt0,(0.&40.)(40.(0.&40.)Lt1,(0.&40.)(40.(0.&40.)Lt2,(0.&40.)(40.(0.&40.)La1,(0.&40.)(40.(0.&40.)La2,(0.&40.)(40.(0.&40.)La3,(0.&40.)(40.(0.&40.)La4,(0.&40.)(40.(0.&40.)La5,(0.&40.)(40.(0.&40.)La6,(0.&40.)(40.(0.&40.)La7,(0.&40.)(40.(0.&40.)Lt3,(0.&40.)(40.(0.&40.)Lt4,(0.&40.)(40.(0.&40.)Lt5,(0.&40.)(40.(0.&40.)Lt6,(0.&40.)(40.(0.&40.)Lstw',(0.&40.)(40.(0.&40.)Lcstw',(0.&40.)(40.(0.&40.)Lj1',(0.&40.)(40.(0.&40.)Lj2',(0.&40.)(40.(0.&40.)Lj3',(0.&40.)(40.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))Zmu',$2.(6.Vmu,(4;.R18.))Zmfa',$2.(6.Vmfa,(4;.R18.))Znw,$2.(45.(47.R2.O13.)Vcs,)Zk,$2.(45.(4<.Vc,)+2.)(;.(19.$49.R20.(4=.R1?.R1>.))(;.(19.$4:.R1?.(4>.(4?.O25.(30.&40.VSP,)O24.(30.&40.$50.)R18.R17.R16.O23.O22.(30.&40.R1=.)R15.R14.R13.R12.R11.R10.R?.O21.O20.O1?.O1>.O1=.O1<.O1;.O1:.O19.O18.R>.R=.R<.R;.)O17.(51.O25.)O16.(2;.(0.&40.))R5.(52.$21.)))(;.A5.VK,R1<.R1;.R1:.R19.R1>.(;.(53.R5.R1>.)(;.(;.(5.R4.+>0000000.)(5.(47.R4.O13.)(7.+2.+13.)))(;.(20.$21.O1.R5.)(;.(54.$21.R5.)(;.(55.$21.R5.Vlo,VSP,)(;.Px,$2.P,A5.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,R1.A5.VCSf,R1>.R1=.R1<.R1;.R2.(;.(25.R5.)(;.(26.R5.)(;.(27.R5.VCTX,VT,)(;.(28.R5.)(;.(29.R5.VSB,)(;.(41.$21.R5.VR,(12.$42.(56.(30.&40.=))(15.$42.)))(;.(41.$21.R5.(6.VR,+18.)(12.$42.(56.(30.&40.R3.))(15.$42.)))(;.(41.$21.R5.(6.VR,+28.)(12.$42.(56.(30.&40.=))(15.$42.)))(;.(41.$21.R5.(6.VR,+30.)(12.$42.(56.(30.&40.R4.))(15.$42.)))(;.(41.$21.R5.(6.VR,+38.)(12.$42.(56.(30.&40.=))(15.$42.)))(;.(41.$21.R5.(6.VR,+48.)(12.$42.(56.R:.)(15.$42.)))(;.(41.$21.R5.(6.VT,+:>0.)(12.$42.(56.R9.)(15.$42.)))(;.(41.$21.R5.(6.VT,+;38.)(12.$42.(56.R8.)(12.$42.(56.R7.)(15.$42.))))(;.(41.$21.R5.(6.VT,+:>8.)(12.$42.(56.R6.)(15.$42.)))(;.P,(19.(1.$2<.)R1;.(34.$2<.$31.))(41.$21.R6.(6.+7???8000.(45.VFAA,+8.))(12.$42.(43.(44.+8000.)(57.(0.&8.)(30.&8.+?:.)(44.+8000.)))(15.$42.)))(;.P,(17.(19.(1.$2<.)R1;.(34.$2<.$31.)))(41.$21.R6.(6.+7???8000.(45.VFAA,+8.))(12.$42.(43.(44.+8000.)O6.)(15.$42.)))(;.P,(17.(19.(1.$2<.)R1<.(34.$2<.$31.)))P,(5.(6.Vmu,(7.+2.+12.))+>0000000.)(41.$21.R7.(6.+7???8000.(45.VUA,+8.))(12.$42.(43.(44.+8000.)O7.)(15.$42.)))(;.(41.$21.R5.(6.VT,+<60.)(12.$42.(46.(30.&8.=))(15.$42.)))(;.A1.O2.R5.(40.$2.LAB,$2.(40.$2.Lcnt',$2.(40.(3.(0.&40.))Lds',(3.(0.&40.))(40.(0.&40.)Lpw,(0.&40.)(40.$2.LN',$2.(40.$2.Ltf',$2.(40.$2.Lid,$2.(40.$2.Lb1',$2.(40.(0.&8.)Lpgb,(0.&8.)(40.(0.&40.)Lsj0,(0.&40.)(40.(0.&40.)Lsj1,(0.&40.)(40.(0.&40.)Lsj2,(0.&40.)(40.(3.(0.&40.))Lbs',(3.(0.&40.))ZUB,$2.(6.R=.(5=.Vn,))ZCHB,$2.(6.R1.-10.)ZSUB,$2.(6.+7???8000.(45.R2.+8.))ZPGS,$2.(6.+7???8000.(5>.(6.R3.(3?.(45.(5?.Vn,)+8.)+8.))+3.))ZKF,$2.(60.(5?.Vn,)+1000.)ZCW,(3.(13.$2.$2.))(12.(13.$2.$2.)(14.$2.$2.R4.(6.R4.+10.))(12.(13.$2.$2.)(14.$2.$2.R12.(6.R12.+10.))(12.(13.$2.$2.)(14.$2.$2.R5.(6.R5.R1.))(15.(13.$2.$2.)))))ZSW,(3.(13.$2.$2.))(12.(13.$2.$2.)(14.$2.$2.R4.(6.R4.(45.(5?.Vn,)+8.)))(12.(13.$2.$2.)(14.$2.$2.R3.(6.R3.$61.))(15.(13.$2.$2.))))(;.(19.$2.R31.R7.)(;.(19.$2.R14.(6.VRB,(3?.+10.(3=.(39.&40.R11.)(7.+2.+20.)))))(;.(;.(5.+1.R13.)(5.R13.+10.))(;.(19.(1.(0.&40.))(62.(0.&40.)R12.(44.(47.R13.+1.)))(34.(0.&40.)R11.))(;.(19.$63.(>.(0.&40.)R12.)#10.)(;.(58.(18.(13.$2.$2.)R2.(18.(13.$2.$2.)R1.(59.O3.)))O1.R19.R2>.R2=.)(;.(41.$21.R19.VPCR,(12.$42.(5:.(30.&40.(47.R13.+1.)))(12.$42.(5:.(30.&40.(4<.Vc,)))(12.$42.(56.O?.)(15.$42.)))))(;.(5;.$21.R19.(6.VPCR,+10.)R12.)(;.(8.(;.(19.$2.R13.O11.)(;.(19.(3.(0.&40.))R12.O9.)(;.(19.(1.$2<.)R30.(2;.$2<.))(;.(19.(1.$2<.)R2?.(2;.$2<.))(;.(41.$21.R19.(6.VR,+10.)(12.$42.(56.(30.&40.O12.))(15.$42.)))(;.(41.$21.R19.(6.VR,+20.)(12.$42.(56.(30.&40.O13.))(15.$42.)))(;.(41.$21.R19.(6.VR,+44.)(12.$42.(46.O10.)(15.$42.)))(;.(5;.$21.R19.VFA,O;.)(5;.$21.R19.(6.VFA,(3?.+4.O12.))O:.)))))))))(;.(19.$2.O11.=)(;.(19.$2.R13.R15.)(;.(17.(19.(1.$2<.)R30.(34.$2<.$64.)))(;.(17.(19.(1.$2<.)R2?.(34.$2<.$64.)))(40.(3.(0.&40.))Lnew,(3.(0.&40.))(40.(3.(0.&40.))Lws,(3.(0.&40.))(40.(3.(0.&40.))Lfa',(3.(0.&40.))(40.(3.(0.&40.))Lrest,(3.(0.&40.))(40.$2.Lnf',$2.(40.$2.Lau',$2.(40.(0.&8.)Lex',(0.&8.)(;.(19.(3.(0.&40.))R19.(65.(44.R1<.)R6.O9.))(;.(19.(3.(0.&40.))(18.(0.&40.)O;.R7.)(18.(0.&40.)R5.R6.))(;.(19.$63.(>.(0.&40.)R6.)(44.R1<.))(;.(19.$2.(=.(>.(0.&40.)R5.))R3.)(;.(8.(;.(19.(3.(0.&40.))R7.(15.(0.&40.)))(;.(19.(1.$2<.)R37.(2;.$2<.))(;.(19.(1.$2<.)R36.(2;.$2<.))(;.(5.R1<.O12.)(;.(19.$2.R2.O13.)(19.(0.&8.)R1.O10.))))))(;.(19.(3.(0.&40.))R7.(66.O13.Vcs,(44.R1=.)))(;.(<.O12.R1<.)(;.(5.(47.R1<.O12.)R1=.)(;.(19.$2.R2.(6.O13.(3?.R1=.Vcs,)))(;.(19.(0.&8.)R1.(30.&8.=))(;.(<.=R1=.)P,(19.(1.$2<.)R36.(34.$2<.$31.))(<.Vmfa,(3?.+4.(6.O12.R1>.))))))))))(;.(41.$21.R20.(6.VR,+10.)(12.$42.(56.(30.&40.R3.))(15.$42.)))(;.(41.$21.R20.(6.VR,+20.)(12.$42.(56.(30.&40.R2.))(15.$42.)))(;.(41.$21.R20.(6.VR,+44.)(12.$42.(46.R1.)(15.$42.)))(;.(5;.$21.R20.VFA,R5.)(;.(5;.$21.R20.(6.VFA,(3?.+4.R3.))R4.)(19.$2.(3?.+4.(6.R3.(=.(>.(0.&40.)R4.))))R1>.)))))))))))))))))))))))(;.P,(19.(1.$2<.)R30.(34.$2<.$31.))(40.(3.(0.&8.))Lzb,(3.(0.&8.))(40.(3.(0.&8.))Lush,(3.(0.&8.))(;.(41.$21.R1<.VUA,(12.$42.(43.(44.(7.+2.+12.))R2.)(15.$42.)))(;.(41.$21.R1<.(6.+7???8000.(45.VUA,+8.))(12.$42.(43.(44.+8000.)R1.)(15.$42.)))(;.Pi,$63.P,(67.R1.(44.(7.+2.+12.)))P,(48.R7.(6.VUA,(=.R2.)))(19.(1.(0.&8.))(62.(0.&8.)R5.R3.)(34.(0.&8.)(30.&8.=)))Pi,$63.P,(67.R1.(44.+8000.))P,(48.R6.(6.(6.+7???8000.(45.VUA,+8.))(=.R2.)))(19.(1.(0.&8.))(62.(0.&8.)R4.R3.)(34.(0.&8.)(30.&8.+?:.))))))))(;.(1?.VhAR,R19.R10.R2>.R?.R2=.)(;.(68.A4.VCSf,R30.R2?.R2>.R2=.R2>.R2=.)(;.(;.(5.+1.R>.)(5.R>.R10.))(;.(;.(5.O15.R10.)(5.R10.(6.O15.+1.)))(;.(;.(5.O14.R?.)(5.R?.(6.O14.(3?.+2.(6.Vd,+3.)))))(;.(5.(47.R?.(3?.+1?.(45.R?.(7.+2.+14.))))(6.(47.O14.(3?.+1?.(45.O14.(7.+2.+14.))))(6.Vd,+3.)))(;.(40.(3.$2.)Lsn,(3.$2.)(40.(3.$2.)Lsb,(3.$2.)(;.(19.(3.$2.)R30.(18.$2.Vnb0,R2.))(;.(19.(3.$2.)R2?.(18.$2.Vbl0,R1.))(;.(69.$2.Lb,$2.Px,$2.P,A5.VCSf,R34.R33.Vnb0,Vbl0,R1.(17.(;.(5.R3.R2.)(<.R2.(6.R3.(7.+2.+14.)))))R2.)(69.$2.Lb,$2.Px,$2.P,A5.VCSf,R34.R33.Vnb0,Vbl0,R1.(17.(;.(5.R3.R2.)(<.R2.(6.R3.(7.+2.+17.)))))R1.))))))(;.(16.A4.VCSf,R30.R2?.R2>.R2=.R14.Vcs,)(;.(41.$21.R19.R6.(12.$42.(46.(30.&8.$6:.))(12.$42.(46.(30.&8.R=.))(12.$42.(6;.(30.&40.=))(12.$42.(5:.(30.&40.(5?.Vn,)))(12.$42.(56.(30.&40.(6<.(3?.VTID,(7.+2.+20.))R>.)))(15.$42.)))))))(;.(19.$2.(6=.R=.+3.)+1.)(;.(;.(5.=R=.)(<.R=.+100.))(;.P,(<.+10.(5=.Vn,))(41.$21.R1:.R15.(12.$42.(56.(30.&40.$6>.))(12.$42.(56.(30.&40.R7.))(15.$42.))))(;.(41.$21.R19.R5.(12.$42.(43.(44.(45.(5?.Vn,)+8.))(57.(0.&8.)(30.&8.=)(44.(45.(5?.Vn,)+8.))))(15.$42.)))(;.(41.$21.R19.R4.(12.$42.(46.(6?.Vn,R<.))(15.$42.)))(;.(41.$21.R19.R7.(12.$42.(43.(44.R3.)(57.(0.&8.)(30.&8.+;>.)(44.R3.)))(15.$42.)))(;.(41.$21.R19.(6.VT,+:?0.)(12.$42.(56.R;.)(12.$42.(56.R:.)(12.$42.(56.R9.)(15.$42.)))))(;.(5<.$21.R19.(6.VT,+;60.)R8.)(;.(19.$63.(>.(0.&40.)R8.)#20.)(;.(41.$21.R19.$22.(12.$42.(46.O5.)(15.$42.)))(41.$21.R19.$23.(12.$42.(5:.O4.)(15.$42.))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Ltac facts :=
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L27705381220.6 L61035084364.78L63368316718.7900000?018021S1n3FP'1H2H02H1S3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPAS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA". (* [comment removed for export] *)
  #[using="hAR SP T SB RI mu mfa c cs R RB FA UA FAA PCR STK SPA FP"] Lemma needed2_prim : needed2 n = needed n /\ 24 <= needed n <= 0x10000.
  Proof.
    pose proof FP as FP'. unfold from_primary, kMaxSize in FP'. apply Z.leb_le in FP'.
    unfold needed2. rewrite FP. split; [reflexivity|].
    unfold needed, rounded, round_up in *. pose proof (rz_size_bound n).
    pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
    clear - H H0 H1 NB FP'. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L27692757971.2L64862237351.200000500:S1n1BS1n1H". (* [comment removed for export] *)
  #[using="hAR SP T SB RI mu mfa cs R RB FA UA FAA PCR STK SPA FP"] Lemma c_range : 1 <= c <= 31.
  Proof. pose proof needed2_prim as [E B]. pose proof (class_of_range (needed2 n) ltac:(rewrite E; clear - B; lia)) as H. subst c. clear - H. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition head_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (CS : Z -> Prop) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Lms',$4:.(40.(0.&40.)Lt0,(0.&40.)(40.(0.&40.)Lt1,(0.&40.)(40.(0.&40.)Lt2,(0.&40.)(40.(0.&40.)Lx14,(0.&40.)(40.(0.&40.)Lx15,(0.&40.)(40.(0.&40.)Lx16,(0.&40.)(40.(0.&40.)Lx17,(0.&40.)(40.(0.&40.)Lt3,(0.&40.)(40.(0.&40.)Lt4,(0.&40.)(40.(0.&40.)Lt5,(0.&40.)(40.(0.&40.)Lt6,(0.&40.)(40.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(40.(3.(0.&40.))Lws,(3.(0.&40.))(40.$2.Lsize,$2.(40.(3.(0.&8.))Lfr0,(3.(0.&8.))(40.(3.(0.&8.))Lfr1,(3.(0.&8.))(40.(3.(0.&8.))Lfr2,(3.(0.&8.))(;.(19.$4:.R12.(4>.(4?.(30.&40.+47=34.)(30.&40.(6.VSPA,-80.))O11.(30.&40.$50.)R11.R10.R?.(30.&40.(70.(71.Vn,)))(30.&40.(5?.Vn,))(30.&40.$72.)(30.&40.(6.VT,+=0.))(30.&40.(73.Vn,))(30.&40.+8.)R>.R=.R<.R;.(30.&40.+8.)(30.&40.(73.Vn,))(30.&40.(5=.Vn,))(30.&40.Vn,)(30.&40.$72.)(30.&40.VSTK,)(30.&40.-8.)(30.&40.+7.)(30.&40.VT,)(30.&40.+1.)R:.R9.R8.R7.)O4.(30.&40.$74.)O3.(2;.(0.&40.))R6.(52.$21.)))(;.(11.(12.(13.$2.$2.)(14.$2.$2.Vlo,VSP,)(12.(13.$2.$2.)(14.$2.$2.(6.VT,+<60.)(6.VT,+<61.))(15.(13.$2.$2.))))O1.R6.)(;.(20.$21.O1.R6.)(;.(54.$21.R6.)(;.(41.$21.R6.(6.VSP,-38.)(12.$42.(56.O;.)(12.$42.(56.O<.)(12.$42.(56.O=.)(12.$42.(56.O>.)(12.$42.(56.O?.)(12.$42.(56.O10.)(12.$42.(56.O12.)(15.$42.)))))))))(;.(41.$21.R6.VSTK,(12.$42.(56.(30.&40.(6.VSTK,+10.)))(12.$42.(56.(30.&40.R4.))(15.$42.))))(;.(5<.$21.R6.(6.VSTK,+10.)R5.)(;.(19.$63.(>.(0.&40.)R5.)#1>.)(;.(;.(5.+1.R4.)(5.R4.+1>.))(;.(5.R4.(6.Vd,+2.))(;.(41.$21.R6.(6.VSTK,+100.)(12.$42.(43.#708.R2.)(15.$42.)))(;.(41.$21.R6.(6.VSTK,+808.)(12.$42.(56.(30.&40.VSP,))(15.$42.)))(;.(41.$21.R6.(6.VSTK,+810.)(12.$42.(43.#8.R1.)(15.$42.)))(;.(41.$21.R6.(6.VSTK,-10.)(12.$42.(56.(30.&40.VSP,))(12.$42.(56.(30.&40.+6978<.))(15.$42.))))(;.(41.$21.R6.(6.VT,+<60.)(12.$42.(46.(30.&8.=))(15.$42.)))(;.(75.R6.VSPA,R3.+1.(30.&40.+47:64.)(30.&40.VSP,)(30.&40.Vn,)(30.&40.$76.)(30.&40.+1.)(30.&40.VSTK,)(30.&40.(6.VSP,-51.))O:.O9.O8.O7.O6.O5.)(;.(55.$21.R6.Vlo,(6.VSPA,-80.))(55.$21.R6.(6.VSP,-10.)(77.VTOP,VSP,))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00T0>L12582944717.8L18188948954.2L19723288167.7L2031783603.1 L2261078798.7 L22706556809.5L23532110458.2L24888640626.2L24897143244.3L25864701137.5L25984564570.8L27848808849.2L30435077518.8L30787585704.1L31482858393.3L32382492013.2L32447096858.1L35247679960.8L36841451887.6L38235734261.1L38630860083.8L40655039027.1L40821008992.6L45334955688.1L51362018088.1L52016747867.7L5429770831.4 L54570223649.3L55067900321.4L56376963496.1L58633807628.3L58913627406.0L63737759283.1L66249744396.4L66763458562.8L9265737838.6 00000K00Q00d00h01E01W01`01a01e02802I02P02f02j03203:03>03Y03j03n04C04G04X04\04`05=05F05Q05a05e05o06006406=06K06dS3hAR2SP2lo3SPA5LOIMG1A1k1HS1T2T0S2SP2lo1T1A1k2H12H2S2SPS3hAR2SP2lo3CTX3SPA5LOIMG3CX1S2SP2lo3SPA1x2Hx1TS3CTX3CX0SS2SPS3hAR2lo1T5LOIMG2T1S3hAR1T2T01A1k2HkS2SP2loS3hAR2lo3CTX5LOIMG3CX1S2SPS2SP3SPAS2SP3SPHS2SPS3hAR2SP2lo3SPA5LOIMG1A1k1HS2SP2lo3SPA1A1k1HS2loS3hAR2lo5LOIMG1A1k2HkS2SPS2SP2lo3SPA1A1k1HS2SPS2SPS3hAR2SP2lo3CTX3SPA5LOIMG3CX1S2SP4TOP2S2SP2lo3SPLS2SP2lo3SPA4SPALS2SPS1T3CTX2TCSS2SPS2SP1q2HqS3hAR1T3CTX2TCS3hAR2SP2lo5LOIMG3SPL3SPH". (* [comment removed for export] *)
  #[using="hAR IMG ALWF SB NB LOIMG SPL SPA16 TOP0 TOP1 TOP2 LOB TOPUB GT GCTX GSEP"] Lemma mseg_head : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PCS,P,$2.SpPCSOK,(78.VAL,R1.)Pra,(0.&40.)Pgp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(79.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))P,(7:.$21.R1.VLO,VTOPU,(39.&40.R1:.)VSP,Vd,)P,(7;.R2.VT,VCTX,)P,(1<.R3.VT,VCTX,)P,(7<.$21.R4.(6.VT,+8.)(12.$42.(56.(30.&40.VTOP,))(12.$42.(56.(30.&40.(47.VTOP,(7.+2.+17.))))(15.$42.))))P,(7<.$21.R5.(6.VT,+28.)(12.$42.(46.(30.&8.=))(15.$42.)))P,(41.$21.R6.(6.VT,+<60.)(12.$42.(46.(30.&8.=))(15.$42.)))P,(16.R27.VT,+1000.)P,(16.R28.VCTX,+10000.)P,(55.$21.R9.VSP,VTOP,)P,(16.R2:.VSP,(47.VTOP,VSP,))P,(55.$21.R;.Vlo,VSP,)P,(16.R2<.Vlo,(47.VSP,Vlo,))P,(54.$21.R=.)(7=.$21.VAL,R2>.(7>.R2<.R2;.R27.R26.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R10.R?.R2>.R>.)(4>.(4?.R2<.(30.&40.VSP,)R2;.(30.&40.$50.)R2:.R29.R28.R27.R26.(30.&40.Vn,)R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(30.&40.$7?.)R?.(2;.(0.&40.))R>.(52.$21.)))")
(* [comment removed for export] *).
  Proof.
    intros CS CSOK ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      UWC MS8 AS THR TSW UNW TCS CTXCS STT STCS ST SCS MI.
    facts. dpose GT as (T0 & T1 & TAL). pose proof GCTX as (CX0 & CX1). dpose GSEP as (SEP1 & TC & SEP3).
    assert (SPH : SP <= 2^62) by (clear - TOP1 TOP2; lia).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (msegA AL IMG ALWF CS CSOK); first [exact NB| exact UWC| exact LOB| exact TOPUB| exact MS8| exact THR| exact TSW| exact UNW| exact TOP0| exact TOP1| exact TOP2| exact TCS| exact CTXCS
        | exact STT| exact STCS| exact ST| exact LOIMG| exact SPL| exact SPA16| exact SCS| exact MI| idtac].
      - clear - T0; lia. - exact T1. - clear - CX0; lia. - exact CX1. - clear - TC; lia. }
    cbn beta. (intros ms1 dd_H; ddestruct dd_H as (y0 & y1 & y2 & y6 & y7 & y3 & y4 & y5 & y6' & m1 & ws & size & fr1 & fr2 & -> &
                          MU1 & WM1 & MI1 & FR7 & STKC & HTR & HL30 & SZB & SZD & F1800 & TFBP & F8 & AFR & UNW1 & ST1 & SR1)).
    assert (DJ1 : forall A k, A + k <= lo -> (A + k <= T + 3168 \/ T + 3169 <= A) -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k)
      by (intros A k H1 H2; cbn [disjoint_from]; clear - H1 H2; lia).
    assert (AS1 : allocA_statics m1 T CTX).
    { eapply (allocA_statics_transport _ m m1 T CTX AS MU1). { intros A k Hk. apply DJ1; cbn; clear - Hk LOIMG T0; lia. } apply DJ1; cbn; clear - LOIMG T1 CX1 TC; lia. }
    assert (SPAAL : SPA mod 16 = 0).
    { subst SPA STK. clear - SPA16. apply Z.mod_divide in SPA16; [| lia]. apply Z.mod_divide; [lia|]. destruct SPA16 as [q Hq]. exists (q - 134). lia. }
    assert (STKB : 0 < STK < 2^64) by (clear - SPL LOIMG SPH; try subst STK; lia).
    assert (SCSA : crange CS lo (SPA - lo)) by (eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst SPA STK; clear; lia]).
    assert (SPAL : lo <= SPA - 512) by (subst SPA STK; clear - SPL; lia). assert (SPAH : SPA <= 2^62) by (subst SPA STK; clear - SPH; lia).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (alloc_proA AL IMG ALWF CS CSOK); [exact NB| exact STKB| clear; lia| exact AS1| exact ST1| exact LOIMG| clear - SPAL; lia| exact SPAH| exact SPAAL| exact SCSA| exact MI1]. }
    cbn beta. (intros ms2 dd_H; ddestruct dd_H as (x10 & x11 & x12 & x13 & m2 & fr0 & -> & MU2 & WM2 & MI2 & FR2 & ST2)).
    assert (LO2 : forall A k, (A + k <= lo \/ SPA <= A) -> disjoint_from [(lo, SPA)] A k) by (intros A k H; cbn [disjoint_from]; clear - H; lia).
    assert (AS2 : allocA_statics m2 T CTX) by (eapply (allocA_statics_transport _ m1 m2 T CTX AS1 MU2); [intros A k H; apply LO2; clear - H LOIMG; lia| apply LO2; clear - CX1 LOIMG; lia]).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (alloc_proB AL IMG ALWF CS CSOK) with (W := []); [exact NB| exact AS2| exact ST2| exact LOIMG| exact SPAL| exact SPAH| exact SPAAL| exact SCSA| apply munch_refl| apply wmono_refl| exact MI2]. }
    cbn beta. (intros ms3 dd_H; ddestruct dd_H as (m3 & PB & MU3 & WM3 & MI3 & MU3' & ST3)). ddestruct PB as (y11 & y12 & y13 & y14 & ->).
    assert (LO3 : forall A k, (A + k <= lo \/ SPA + -128 <= A) -> disjoint_from [(lo, SPA + -128)] A k) by (intros A k H; cbn [disjoint_from]; clear - H; lia).
    assert (AS3 : allocA_statics m3 T CTX) by (eapply (allocA_statics_transport _ m2 m3 T CTX AS2 MU3'); [intros A k H; apply LO3; clear - H LOIMG; lia| apply LO3; clear - CX1 LOIMG; lia]).
    eapply evtA_cut.
    { eapply (alloc_proC AL IMG ALWF CS CSOK) with (W := []); [exact NB| exact AS3| | exact CX1| | exact T1| exact CTXCS| exact TCS| exact ST3| exact LOIMG| exact SPAL| exact SPAH| exact SPAAL| exact SCSA| apply munch_refl| apply wmono_refl| exact MI3| reflexivity].
      - clear - CX0; lia. - clear - T0; lia. }
    cbn beta. (intros ms4 dd_H; ddestruct dd_H as (m4 & PCp & MU4 & WM4 & MI4 & MU4' & ST4)). ddestruct PCp as (z14 & z15 & z16 & z17 & ->).
    apply evtA_done. unfold head_post.
    assert (MU14 : munch [(lo, SPA)] m1 m4).
    { eapply munch_trans; [exact MU2|]. eapply munch_trans; (eapply munch_weaken; [| eassumption]); unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
    assert (WM14 : wmono asegs m1 m4) by (eapply wmono_trans; [exact WM2| eapply wmono_trans; [exact WM3| exact WM4]]).
    assert (LO14 : forall A k, (A + k <= lo \/ SPA <= A) -> disjoint_from [(lo, SPA)] A k) by (intros A k H; cbn [disjoint_from]; clear - H; lia).
    deexists 11. dexists m4, ws, size, fr0, fr1, fr2.
    split; [reflexivity|].
    split. { eapply munch_trans; [exact MU1|]. eapply munch_weaken; [| exact MU14]. unfold sub_fp; cbn [outside]; subst SPA STK; clear; intros x Hx; lia. }
    split; [exact (wmono_trans _ _ _ _ WM1 WM14)|]. split; [exact MI4|].
    split; [eapply rw_cells_transport; [exact FR7| exact MU14| exact WM14| apply LO14; right; subst SPA STK; cbn; clear; lia]|].
    split; [eapply rw_cells_transport; [exact STKC| exact MU14| exact WM14| apply LO14; right; subst SPA STK; cbn; clear; lia]|].
    split; [eapply u64arr_transport; [exact HTR| exact MU14| exact WM14| apply LO14; right; subst SPA STK; clear; lia]|].
    split; [exact HL30|]. split; [exact SZB|]. split; [exact SZD|].
    split; [eapply rw_cells_transport; [exact F1800| exact MU14| exact WM14| apply LO14; right; subst SPA STK; clear; lia]|].
    split; [eapply rw_cells_transport; [exact TFBP| exact MU14| exact WM14| apply LO14; right; subst SPA STK; clear; lia]|].
    split; [eapply rw_cells_transport; [exact F8| exact MU14| exact WM14| apply LO14; right; subst SPA STK; clear; lia]|].
    split; [eapply rw_cells_transport; [exact AFR| exact MU14| exact WM14| apply LO14; right; subst SPA STK; clear; lia]|].
    split; [eapply rw_cells_transport; [exact UNW1| exact MU14| exact WM14| apply LO14; left; cbn; clear - T1 LOIMG; lia]|].
    split. { unfold allocA_frame in *. eapply rw_cells_transport; [exact FR2| eapply munch_trans; [exact MU3'| exact MU4']| eapply wmono_trans; [exact WM3| exact WM4]|].
             cbn [disjoint_from cells_size csize Nat.add]. clear. split; [right; lia| exact I]. }
    split; [exact ST4|].
    eapply stk_transport_disjoint; [exact SR1| exact MU14| exact WM14| apply LO14; right; subst SPA STK; clear; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L11380347005.3 L15041258067.89L29105961052.3 L31747570154.0 L45706641970.1 L50463732076.3 L54702911965.93L61653547298.91L63988471514.95L8873338536.3  00000;01:01E01F01J01U02T03S04R04]S2SP2lo3SPLS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2ws2HLS2SP2lo3SPLSS2SPS2SP2lo3SPLS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2ws2HLS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2ws2HLS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2ws2HLS2SP2lo3SPL". (* [comment removed for export] *)
  #[using="hAR n T SB RI mu mfa c cs R RB FA UA FAA PCR SPA SPL"] Lemma stk_rebuild : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pm,P,(0.&40.)(1.(0.&8.))Psize,$2.Pws,(3.(0.&40.))Pfr1,(3.(0.&8.))Pfr2,(3.(0.&8.))P,(55.$21.R5.Vlo,VSTK,)P,(19.$63.(>.(0.&40.)R4.)#1>.)P,(41.$21.R7.VSTK,(12.$42.(56.(30.&40.(6.VSTK,+10.)))(12.$42.(56.(30.&40.R6.))(15.$42.))))P,(5<.$21.R8.(6.VSTK,+10.)R6.)P,(41.$21.R9.(6.VSTK,+100.)(12.$42.(43.#708.R6.)(15.$42.)))P,(41.$21.R:.(6.VSTK,+808.)(12.$42.(56.(30.&40.VSP,))(15.$42.)))P,(41.$21.R;.(6.VSTK,+810.)(12.$42.(43.#8.R7.)(15.$42.)))(55.$21.R<.Vlo,(6.VSP,-38.))")
(* [comment removed for export] *).
  Proof.
    intros m size ws fr1 fr2 ST HL STKC HTR F1800 TFB F8.
    pose proof (stk_release asegs m lo STK _ ST STKC ltac:(clear - SPL; try subst STK; lia)) as R0. cbn [cells_size csize Nat.add] in R0.
    assert (TRC : rw_cells asegs m (STK + Z.of_nat 16) [CB (length (u64s ws)) (u64s ws)]).
    { replace (STK + Z.of_nat 16) with (STK + 16) by lia. apply rw_cells_of_u8arr. destruct HTR as [HB HW]. split; [exact HB|]. rewrite u64s_length, HL. rewrite HL in HW. replace (Z.of_nat (8 * 30)) with (8 * Z.of_nat 30) by (clear; lia). exact HW. }
    pose proof (stk_release asegs m lo _ _ R0 TRC ltac:(clear - SPL; try subst STK; lia)) as R1. cbn [cells_size csize Nat.add] in R1. rewrite u64s_length, HL in R1.
    assert (F1800' : rw_cells asegs m (STK + Z.of_nat 16 + Z.of_nat (8 * 30)) [CB 1800 fr1]) by (replace (STK + Z.of_nat 16 + Z.of_nat (8 * 30)) with (STK + 256) by lia; exact F1800).
    pose proof (stk_release asegs m lo _ _ R1 F1800' ltac:(clear - SPL; try subst STK; lia)) as R2. cbn [cells_size csize Nat.add] in R2.
    assert (TFB' : rw_cells asegs m (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800) [C8 (Z_to_bv 64 SP)]) by (replace (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800) with (STK + 2056) by lia; exact TFB).
    pose proof (stk_release asegs m lo _ _ R2 TFB' ltac:(clear - SPL; try subst STK; lia)) as R3. cbn [cells_size csize Nat.add] in R3.
    assert (F8' : rw_cells asegs m (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800 + Z.of_nat 8) [CB 8 fr2]) by (replace (STK + Z.of_nat 16 + Z.of_nat (8 * 30) + Z.of_nat 1800 + Z.of_nat 8) with (STK + 2064) by lia; exact F8).
    pose proof (stk_release asegs m lo _ _ R3 F8' ltac:(clear - SPL; try subst STK; lia)) as R4. cbn [cells_size csize Nat.add] in R4.
    lazymatch type of R4 with stk _ _ _ ?hi => replace hi with (SP + -56) in R4 by (subst STK; clear; lia) end. exact R4.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0>L12589220599.9L1337647443.3 L15455868178.3L20957647993.4L24888640626.2L24897143244.3L25590112999.8L27418375329.0L27848808849.2L33948242119.1L341863661.3  L35442361799.1L37889868708.5L38235734261.1L38417689572.1L39656936750.5L40139750667.4L40440761484.1L42289303773.2L42333736447.9L42476413511.1L42629649926.2L44714545569.0L48489320647.1L50650825377.2L5429770831.4 L54570223649.3L57628700040.4L59379581035.3L66249744396.4L6787527454.9 L6793809444.8 L8346817460.8 00000F00Q00\00l00m01101B01C01J01N01Y01]01n02202602K02T02X02`02k02o03703803<03D03M03X03d03k04404P04k05FS3hAR2SP2lo3SPA1A1k2H1S2SP2lo3SPLS2SP2lo3SPLS2SP2lo3SPA4SPALSS2SPS3hAR2SP2lo1A1k1HSS2SP2loS2SPS2SP2lo3SPLS2SPS3hAR2SP2lo5LOIMGS2loS2SPS3hAR2SP2lo3SPA5LOIMGS2SP1q2HqS2SPS2SP3SPHS2SP2lo1x1HS2SPS2SP3SPHSS2SPS2SP3STKS2SP4TOP2S2SP2lo3SPLS2SP2lo1x2HxS2SP2loS2SP1q2HqS3hAR2SP2lo3SPA5LOIMG1A1k2H2S3hAR2SP2lo5LOIMG3SPL1A1k1HS3hAR2SP2lo5LOIMG3SPL1A1k1H". (* [comment removed for export] *)
  #[using="hAR IMG ALWF T SB RI mu mfa c cs R RB FA UA FAA PCR LOIMG SPL SPA16 TOP2"] Lemma mseg_null : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PCS,P,$2.SpPCSOK,(78.VAL,R1.)Pra,(0.&40.)Pgp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px8,(0.&40.)Px20,(0.&40.)Px26,(0.&40.)Pe0,(0.&40.)Poomb,(0.&8.)PF,(79.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(1.(0.&8.))Pm,P,(0.&40.)(1.(0.&8.))Psize,$2.Pws,(3.(0.&40.))Pfr0,(3.(0.&8.))Pfr1,(3.(0.&8.))Pfr2,(3.(0.&8.))PW,(3.(13.$2.$2.))P,(75.R7.VSPA,R4.+1.(30.&40.+47:64.)(30.&40.VSP,)(30.&40.Vn,)(30.&40.$76.)(30.&40.+1.)(30.&40.VSTK,)(30.&40.(6.VSP,-51.))R19.R18.R17.R16.R15.R14.)P,(41.$21.R8.$22.(12.$42.(46.R<.)(15.$42.)))P,(7<.$21.R9.$80.(12.$42.(46.(30.&8.+1.))(15.$42.)))P,(41.$21.R:.$23.(12.$42.(5:.R?.)(15.$42.)))P,(41.$21.R;.(6.VSTK,-10.)(12.$42.(56.(30.&40.VSP,))(12.$42.(56.(30.&40.+6978<.))(15.$42.))))P,(41.$21.R<.(6.VSP,-38.)(12.$42.(56.R1?.)(12.$42.(56.R20.)(12.$42.(56.R21.)(12.$42.(56.R22.)(12.$42.(56.R2:.)(12.$42.(56.R2;.)(12.$42.(56.R30.)(15.$42.)))))))))P,(41.$21.R=.VSTK,(12.$42.(56.(30.&40.(6.VSTK,+10.)))(12.$42.(56.(30.&40.R<.))(15.$42.))))P,(5<.$21.R>.(6.VSTK,+10.)R<.)P,(19.$63.(>.(0.&40.)R=.)#1>.)P,(41.$21.R10.(6.VSTK,+100.)(12.$42.(43.#708.R<.)(15.$42.)))P,(41.$21.R11.(6.VSTK,+808.)(12.$42.(56.(30.&40.VSP,))(15.$42.)))P,(41.$21.R12.(6.VSTK,+810.)(12.$42.(43.#8.R=.)(15.$42.)))P,(55.$21.R13.Vlo,(6.VSPA,-80.))P,(16.R3:.Vlo,(47.VSP,Vlo,))P,(11.(12.(13.$2.$2.)(14.$2.$2.Vlo,VSP,)(12.(13.$2.$2.)(14.$2.$2.$22.(6.$22.+1.))(12.(13.$2.$2.)(14.$2.$2.$23.(6.$23.+4.))R?.)))R16.R15.)P,(20.$21.R17.R16.)P,(54.$21.R17.)(7=.$21.VAL,R3>.Lms',$4:.(40.(0.&40.)Ly0,(0.&40.)(40.(0.&40.)Ly1,(0.&40.)(40.(0.&40.)Ly2,(0.&40.)(40.(0.&40.)Lya1,(0.&40.)(40.(0.&40.)Lya2,(0.&40.)(40.(0.&40.)Lya3,(0.&40.)(40.(0.&40.)Lya4,(0.&40.)(40.(0.&40.)Lya5,(0.&40.)(40.(0.&40.)Lya6,(0.&40.)(40.(0.&40.)Lya7,(0.&40.)(40.(0.&40.)Ly3,(0.&40.)(40.(0.&40.)Ly4,(0.&40.)(40.(0.&40.)Ly5,(0.&40.)(40.(0.&40.)Ly6,(0.&40.)(40.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(;.(19.$4:.R10.(4>.(4?.R4<.(30.&40.VSP,)R4;.(30.&40.$50.)R?.R>.R=.R47.R46.(30.&40.=)R<.R;.R:.R9.R8.R7.R6.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R5.R4.R3.R2.)R2;.(51.R4<.)R2:.(2;.(0.&40.))R1.(52.$21.)))(;.(11.(12.(13.$2.$2.)(14.$2.$2.Vlo,VSP,)(12.(13.$2.$2.)(14.$2.$2.$22.(6.$22.+1.))(12.(13.$2.$2.)(14.$2.$2.$23.(6.$23.+4.))R22.)))R29.R1.)(;.(20.$21.R29.R1.)(;.(54.$21.R1.)(;.(41.$21.R1.$22.(12.$42.(46.(30.&8.+1.))(15.$42.)))(;.(41.$21.R1.$23.(12.$42.(5:.(30.&40.+<.))(15.$42.)))(55.$21.R1.Vlo,VSP,))))))))))))))))))))))(4>.(4?.(30.&40.+47=34.)(30.&40.(6.VSPA,-80.))R3;.(30.&40.$50.)R3:.R39.R38.R20.(30.&40.(5?.Vn,))(30.&40.=)R35.R34.R33.R32.R31.R30.R2?.(30.&40.+8.)(30.&40.(73.Vn,))R1?.(30.&40.Vn,)(30.&40.$72.)(30.&40.VSTK,)(30.&40.-8.)(30.&40.+7.)R1>.(30.&40.+1.)R24.R23.R22.R21.)R1;.(30.&40.+47=34.)R1:.(2;.(0.&40.))R18.(52.$21.)))")
(* [comment removed for export] *).
  Proof.
    intros CS CSOK ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x8 x20 x26 e0 oomb F fc m0 m size ws fr0 fr1 fr2 W
      AFR OOM MRN ERR FR16 FR7 STKC HTR HL F1800 TFB F8 ST SCS MU WM MI.
    facts. assert (SPH : SP <= 2^62) by (clear - TOP1 TOP2; lia).
    assert (SPAL : lo <= SPA - 512) by (subst SPA STK; clear - SPL; lia). assert (SPAH : SPA <= 2^63) by (subst SPA STK; clear - SPH; lia).
    assert (SPAAL : SPA mod 16 = 0).
    { subst SPA STK. clear - SPA16. apply Z.mod_divide in SPA16; [| lia]. apply Z.mod_divide; [lia|]. destruct SPA16 as [q Hq]. exists (q - 134). lia. }
    assert (SCSA : crange CS lo (SPA - lo)) by (eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst SPA STK; clear; lia]).
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (alloc_null AL IMG ALWF CS CSOK) with (m0 := m) (W := []) (T := T);
        [exact AFR| exact OOM| exact MRN| exact ST| exact LOIMG| clear - SPAL; lia| exact SPAH| exact SPAAL| exact SCSA| apply munch_refl| apply wmono_refl| exact MI]. }
    cbn beta. (intros ms1 dd_H; ddestruct dd_H as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m1 & -> & MU1 & WM1 & MI1 & OOM1 & ST1)).
    replace (ret_pc (Z_to_bv 64 0x47a64)) with (Z_to_bv 64 0x47a64) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    assert (DJ1 : forall A k, (A + k <= lo \/ SPA <= A) -> lo <= A -> disjoint_from [(lo, SPA); (A_OOM_CELL, A_OOM_CELL + 1)] A k).
    { intros A k H1 H2. unfold A_OOM_CELL. cbn [disjoint_from]. clear - H1 H2 LOIMG. repeat split; lia. }
    (* [comment removed for export] *)
    eapply evtA_cut.
    { eapply (amalloc_null AL IMG ALWF CS CSOK) with (SP := STK) (m0 := m1) (W := []);
        [ | | | exact LOIMG| clear - SPL; try subst STK; lia| clear - SPH; try subst STK; lia| | | apply munch_refl| apply wmono_refl| exact MI1| reflexivity].
      - replace (STK + -16) with SPA by (subst SPA STK; clear; lia). eapply rw_cells_transport; [exact FR16| exact MU1| exact WM1| apply DJ1; cbn; subst SPA STK; clear - SPL; lia].
      - eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1| unfold A_ERRNO, A_OOM_CELL; cbn; clear - LOIMG; lia].
      - replace (STK + -16) with SPA by (subst SPA STK; clear; lia). exact ST1.
      - subst STK. clear - SPA16. apply Z.mod_divide in SPA16; [| lia]. apply Z.mod_divide; [lia|]. destruct SPA16 as [q Hq]. exists (q - 133). lia.
      - eapply (crange_sub CS lo (SP - lo)); [exact SCS| clear; lia| subst STK; clear; lia]. }
    cbn beta. (intros ms2 dd_H; ddestruct dd_H as (x11 & m2 & -> & MU2 & WM2 & MI2 & ERR2 & ST2)).
    replace (ret_pc (Z_to_bv 64 0x6978c)) with (Z_to_bv 64 0x6978c) by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
    assert (MU12 : munch [(lo, STK); (A_OOM_CELL, A_OOM_CELL + 1); (A_ERRNO, A_ERRNO + 4)] m m2).
    { eapply munch_trans. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; subst SPA STK; clear; intros x Hx; lia. }
      eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; subst STK; clear; intros x Hx; lia. }
    pose proof (wmono_trans _ _ _ _ WM1 WM2) as WM12.
    assert (DJ2 : forall A k, STK <= A -> disjoint_from [(lo, STK); (A_OOM_CELL, A_OOM_CELL + 1); (A_ERRNO, A_ERRNO + 4)] A k).
    { intros A k H. unfold A_OOM_CELL, A_ERRNO. cbn [disjoint_from]. subst STK. clear - H LOIMG SPL. repeat split; lia. }
    assert (ST3 : stk asegs m2 lo (SP + -56)).
    { eapply stk_rebuild; [exact ST2| exact HL| | | | |].
      - eapply rw_cells_transport; [exact STKC| exact MU12| exact WM12| apply DJ2; clear; lia].
      - eapply u64arr_transport; [exact HTR| exact MU12| exact WM12| apply DJ2; subst STK; clear; lia].
      - eapply rw_cells_transport; [exact F1800| exact MU12| exact WM12| apply DJ2; subst STK; clear; lia].
      - eapply rw_cells_transport; [exact TFB| exact MU12| exact WM12| apply DJ2; subst STK; clear; lia].
      - eapply rw_cells_transport; [exact F8| exact MU12| exact WM12| apply DJ2; subst STK; clear; lia]. }
    assert (FR7' : rw_cells asegs m2 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
      by (eapply rw_cells_transport; [exact FR7| exact MU12| exact WM12| apply DJ2; subst STK; clear; lia]).
    (* [comment removed for export] *)
    eapply evtA_mono.
    { subst STK. eapply (malloc_epi AL IMG ALWF CS CSOK); [exact FR7'| exact ST3| exact LOIMG| clear - SPL; lia| exact SPH| exact SPA16| exact SCS| exact MI2]. }
    cbn beta. intros ms3 (-> & ST4).
    deexists 14. exists m2. split; [reflexivity|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU12]. unfold sub_fp; cbn [outside]. subst STK. clear. intros x Hx. decompose [and] Hx. repeat split; auto. lia. }
    split; [exact (wmono_trans _ _ _ _ WM WM12)|]. split; [exact MI2|].
    split; [eapply rw_cells_transport; [exact OOM1| exact MU2| exact WM2| unfold A_OOM_CELL, A_ERRNO; cbn; clear - LOIMG SPL; try subst STK; lia]|].
    split; [exact ERR2| exact ST4].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section ChunkArm.
    Variables (u f : option bool) (pw : word).
    Let AB := SB + c * 2^32 + 16 * (bv_unsigned pw mod 2^32).
    Let UB := AB + rz_size n.
    Let CHB := AB + rz_size n + -16.
    Let SUB := 0x7fff8000 + UB / 8.
    Let PGS := 0x7fff8000 + Z.shiftr (UB + nfix n / 8 * 8) 3.
    Let KF := Z.min (nfix n) 4096.
    Let ASH := 0x7fff8000 + Z.shiftr AB 3.
    Let CSc := CSf u f nb0 bl0.
    Hypothesis AB1 : AB + needed2 n <= SB + c * 2^32 + 0xE0000000.
    (* [comment removed for export] *)
    Hypothesis APTn : forall k, 0 <= k < Z.of_nat (length nb0) -> T + 4096 <= dblk nb0 k \/ dblk nb0 k + 2^20 <= T.
    Hypothesis APTs : forall j, 0 <= j < Z.of_nat (length bl0) -> T + 4096 <= sblk bl0 j \/ sblk bl0 j + 2^23 <= T.
    Hypothesis APCn : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vnb0,))))(8.(5.(6.VCTX,+10000.)(?.Vnb0,R2.))(5.(6.(?.Vnb0,R2.)(7.+2.+14.))VCTX,))")
(* [comment removed for export] *).
    Hypothesis APCs : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vbl0,))))(8.(5.(6.VCTX,+10000.)(10.Vbl0,R2.))(5.(6.(10.Vbl0,R2.)(7.+2.+17.))VCTX,))")
(* [comment removed for export] *).
    Hypothesis APSn : forall k, 0 <= k < Z.of_nat (length nb0) -> RI + 4096 <= dblk nb0 k \/ dblk nb0 k + 2^20 <= SB.
    Hypothesis APSs : forall j, 0 <= j < Z.of_nat (length bl0) -> RI + 4096 <= sblk bl0 j \/ sblk bl0 j + 2^23 <= SB.
    Hypothesis TCS : crange CSc T 4096.
    Hypothesis CTXCS : crange CSc CTX 0x10000.
    Hypothesis ACS : crange CSc AB (needed2 n).
    Hypothesis SCS : crange CSc lo (SP - lo).

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L18190854626.9900001HS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2GT2pw2AB2UB3CHB3SUB3PGS2KF3ASH". (* [comment removed for export] *)
    #[using="hAR SP n SB RI mu mfa c cs R RB FA UA FAA PCR STK SPA GT pw AB UB CHB SUB PGS KF ASH"] Lemma T0 : Timg T. Proof. pose proof GT. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L61482307031.9900001HS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2GT2pw2AB2UB3CHB3SUB3PGS2KF3ASH". (* [comment removed for export] *)
    #[using="SP n SB RI mu mfa c cs R RB FA UA FAA PCR STK SPA GT pw AB UB CHB SUB PGS KF ASH"] Lemma T1 : T + 4096 <= ACEIL. Proof. pose proof GT. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L23536159298.9900001NS3hAR2SP1n1T3CTX2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA4GCTX2pw2AB2UB3CHB3SUB3PGS2KF3ASH". (* [comment removed for export] *)
    #[using="hAR SP n T SB RI mu mfa c cs R RB FA UA FAA PCR STK SPA GCTX pw AB UB CHB SUB PGS KF ASH"] Lemma CX0 : 0x65f000 <= CTX. Proof. pose proof GCTX. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L45743032595.9900001NS3hAR2SP1n1T3CTX2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA4GCTX2pw2AB2UB3CHB3SUB3PGS2KF3ASH". (* [comment removed for export] *)
    #[using="SP n T SB RI mu mfa c cs R RB FA UA FAA PCR STK SPA GCTX pw AB UB CHB SUB PGS KF ASH"] Lemma CX1 : CTX + 0x10000 <= ACEIL. Proof. pose proof GCTX. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L58632167809.9900001NS3hAR2SP1n1T3CTX2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA4GSEP2pw2AB2UB3CHB3SUB3PGS2KF3ASH". (* [comment removed for export] *)
    #[using="hAR SP n SB RI mu mfa c cs R RB FA UA FAA PCR STK SPA GSEP pw AB UB CHB SUB PGS KF ASH"] Lemma TC : T + 4096 <= CTX \/ CTX + 0x10000 <= T. Proof. pose proof GSEP. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L1048143380.9900001IS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA3GSB2pw2AB2UB3CHB3SUB3PGS2KF3ASH". (* [comment removed for export] *)
    #[using="hAR SP n T RI mu mfa c cs R RB FA UA FAA PCR STK SPA GSB pw AB UB CHB SUB PGS KF ASH"] Lemma SB0 : 0 <= SB. Proof. pose proof GSB. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    #[using="hAR n T CTX TOP TID RI mu mfa NB TIDB TOPU TOPUB GSB GT GCTX GSEP GMU GMFA"] Lemma SBAL : SB mod 4096 = 0. Proof. pose proof GSB. tauto. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L27614488698.4000009S2SP4TOP2". (* [comment removed for export] *)
    #[using="TOP2"] Lemma SPH : SP + 16 <= 2^47. Proof. clear - TOP1 TOP2. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L22311521842.10000001\S3hAR2SP1n1T3CTX2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA3GSB2GT4GCTX4GSEP2pw2UB3CHB3SUB3PGS2KF3ASH1H2H0". (* [comment removed for export] *)
    #[using="hAR SP lo T CTX RI mu mfa cs R RB FA UA FAA PCR STK SPA FP LOIMG SPL SPA16 GSB GT GCTX GSEP GMU GMFA UB CHB SUB PGS KF ASH"] Lemma AB0 : 0x65f000 <= AB. Proof. subst AB. pose proof GSB. pose proof c_range. pose proof (Z.mod_pos_bound (bv_unsigned pw) (2^32)). lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L22657719303.9900001YS3hAR2SP1n1T3CTX2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA3GSB2GT4GCTX4GSEP2pw2UB3CHB3SUB3PGS2KF3ASH1H". (* [comment removed for export] *)
    #[using="hAR SP lo T CTX RI mu mfa cs R RB FA UA FAA PCR STK SPA FP LOIMG SPL SPA16 GSB GT GCTX GSEP GMU GMFA UB CHB SUB PGS KF ASH"] Lemma ABsb : SB <= AB. Proof. subst AB. pose proof c_range. pose proof (Z.mod_pos_bound (bv_unsigned pw) (2^32)). lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L17796533536.10000001NS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA3GSB2pw2AB2UB3CHB3SUB3PGS2KF3ASH1H2H0". (* [comment removed for export] *)
    #[using="hAR SP lo T CTX RI mu mfa cs R RB FA UA FAA PCR STK SPA FP LOIMG SPL SPA16 GSB GT GCTX GSEP GMU GMFA UB CHB SUB PGS KF ASH"] Lemma ABlo : 0x10007fff9000 <= AB. Proof. pose proof ABsb. pose proof GSB. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L8890663330.900000JS3hAR1n2SB2RI1c2pw1H2H02H1". (* [comment removed for export] *)
    #[using="hAR SP T mu mfa cs R RB FA UA FAA PCR STK SPA FP GSB AB1"] Lemma ABhi : AB + needed2 n <= RI. Proof. pose proof AB1. pose proof GSB. pose proof c_range. subst AB. clear - H H0 H1. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L5821062177.10000001[S3hAR2SP1n1T3CTX2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2GT4GCTX4GSEP2pw2AB2UB3CHB3SUB3PGS2KF3ASH1H2H0". (* [comment removed for export] *)
    #[using="SP lo T CTX RI mu mfa cs R RB FA UA FAA PCR STK SPA FP LOIMG SPL GSB GT GCTX GSEP GMU GMFA UB CHB SUB PGS KF ASH AB1"] Lemma AB1' : AB + needed2 n <= ACEIL. Proof. pose proof ABhi. pose proof GSB. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L45782187069.10200001^S3hAR2SP1n1T3CTX2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2GT4GCTX4GSEP2pw2AB2UB3CHB3SUB3PGS2KF3ASH1H2H02H2". (* [comment removed for export] *)
    #[using="hAR SP lo CTX RI mu mfa cs R RB FA UA FAA PCR STK SPA FP LOIMG SPL SPA16 GSB GT GCTX GSEP GMU GMFA UB CHB SUB PGS KF ASH AB1"] Lemma ABT : AB + needed2 n <= T \/ T + 4096 <= AB. Proof. pose proof ABsb. pose proof ABhi. pose proof GSEP. pose proof GSB. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L60574223525.10200001^S3hAR2SP1n1T3CTX2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2GT4GCTX4GSEP2pw2AB2UB3CHB3SUB3PGS2KF3ASH1H2H02H2". (* [comment removed for export] *)
    #[using="hAR SP lo T RI mu mfa cs R RB FA UA FAA PCR STK SPA FP LOIMG SPL SPA16 GSB GT GCTX GSEP GMU GMFA UB CHB SUB PGS KF ASH AB1"] Lemma ABC : AB + needed2 n <= CTX \/ CTX + 0x10000 <= AB. Proof. pose proof ABsb. pose proof ABhi. pose proof GSEP. pose proof GSB. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L17794445592.9900001GS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2pw2AB2UB3CHB3SUB3PGS2KF3ASH1H". (* [comment removed for export] *)
    #[using="hAR SP lo T CTX RI mu mfa cs R RB FA UA FAA PCR STK SPA FP LOIMG SPL SPA16 GSB GT GCTX GSEP GMU GMFA UB CHB SUB PGS KF ASH"] Lemma RNG : AB + needed2 n <= 0x7fff8000 \/ 0x10007fff8000 <= AB. Proof. right. pose proof ABlo. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L10417939618.9900001HS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2GT2pw2AB2UB3CHB3SUB3PGS2KF3ASH". (* [comment removed for export] *)
    #[using="hAR SP n SB RI mu mfa c cs R RB FA UA FAA PCR STK SPA GT pw AB UB CHB SUB PGS KF ASH"] Lemma TNS : T + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= T. Proof. pose proof GT. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L31696321418.9900001NS3hAR2SP1n1T3CTX2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA4GCTX2pw2AB2UB3CHB3SUB3PGS2KF3ASH". (* [comment removed for export] *)
    #[using="hAR SP n T SB RI mu mfa c cs R RB FA UA FAA PCR STK SPA GCTX pw AB UB CHB SUB PGS KF ASH"] Lemma CTXNS : CTX + 0x10000 <= 0x7fff8000 \/ 0x10007fff8000 <= CTX. Proof. pose proof GCTX. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L20574038211.10400001jS3hAR3nb02SP1n1T3CTX2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2GT4GCTX4GSEP2pw2AB2UB3CHB3SUB3PGS2KF3ASH1k2Hk1H2H02H12H2". (* [comment removed for export] *)
    #[using="hAR SP lo T CTX RI mu mfa cs R RB FA UA FAA PCR STK SPA FP LOIMG SPL SPA16 GSB GT GCTX GSEP GMU GMFA UB CHB SUB PGS KF ASH AB1 APSn"] Lemma APAn : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vnb0,))))(8.(5.(6.VAB,(73.Vn,))(?.Vnb0,R2.))(5.(6.(?.Vnb0,R2.)(7.+2.+14.))VAB,))")
(* [comment removed for export] *).
    Proof. intros k Hk. pose proof (APSn k Hk). pose proof ABsb. pose proof ABhi. pose proof GSB. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L61587179402.10400001jS3hAR3bl02SP1n1T3CTX2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2GT4GCTX4GSEP2pw2AB2UB3CHB3SUB3PGS2KF3ASH1j2Hj1H2H02H12H2". (* [comment removed for export] *)
    #[using="hAR SP lo T CTX RI mu mfa cs R RB FA UA FAA PCR STK SPA FP LOIMG SPL SPA16 GSB GT GCTX GSEP GMU GMFA UB CHB SUB PGS KF ASH AB1 APSs"] Lemma APAs : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vbl0,))))(8.(5.(6.VAB,(73.Vn,))(10.Vbl0,R2.))(5.(6.(10.Vbl0,R2.)(7.+2.+17.))VAB,))")
(* [comment removed for export] *).
    Proof. intros j Hj. pose proof (APSs j Hj). pose proof ABsb. pose proof ABhi. pose proof GSB. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L18928473169.97L8357967512.6  00001B01US3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2pw2UB3CHB3SUB3PGS2KF3ASHS1n2SB1c2pw1H5SBAL'". (* [comment removed for export] *)
    #[using="hAR SP T CTX TOP TID RI mu mfa cs R RB FA UA FAA PCR STK SPA NB TIDB TOPU TOPUB GSB GT GCTX GSEP GMU GMFA UB CHB SUB PGS KF ASH"] Lemma AB_al : AB mod 16 = 0.
    Proof.
      subst AB. pose proof (Z.div_mod SB 4096 ltac:(lia)). pose proof SBAL as SBAL'.
      replace (SB + c * 2^32 + 16 * (bv_unsigned pw mod 2^32)) with ((SB / 4096 * 256 + c * 2^28 + bv_unsigned pw mod 2^32) * 16) by (clear - H SBAL'; lia).
      apply Z_mod_mult.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Definition zone (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "(8.(;.A1.VCSc,O1.(8.(;.(5.VSB,O1.)(<.O1.(6.VRI,+1000.)))(8.(;.(5.VT,O1.)(<.O1.(6.VT,+:?0.)))(;.(5.VCTX,O1.)(<.O1.(6.VCTX,+10000.))))))(8.(;.(5.(6.+7???8000.(45.VSB,+8.))O1.)(<.O1.(6.+7???8000.(45.(6.VRI,+1000.)+8.))))(;.(;.(5.+10000.O1.)(<.O1.+65?000.))(17.(;.(5.$9.O1.)(<.O1.$:.))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)
    Definition cwin : list (Z * Z) := [(CHB, CHB + 16); (AB, AB + 16); (UB, UB + KF); (SUB, SUB + nfix n / 8); (PGS, PGS + 1)].
    Definition zkeep (m m' : mem) : Prop := forall x : word, zone (bv_unsigned x) -> outside cwin (bv_unsigned x) -> m' x = m x.
    
    Definition chunk_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (N tf : Z) (m0 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Lcf,$49.(40.$4:.Lms',$4:.(40.$2:.Lmo',$2:.(40.(3.$2.)Lnb',(3.$2.)(40.(3.$2.)Lbl',(3.$2.)(40.$2.LN',$2.(40.$2.Ltf',$2.(40.$2.Lid,$2.(40.(0.&40.)Lt0,(0.&40.)(40.(0.&40.)Lt1,(0.&40.)(40.(0.&40.)Lt2,(0.&40.)(40.(0.&40.)La1,(0.&40.)(40.(0.&40.)La2,(0.&40.)(40.(0.&40.)La3,(0.&40.)(40.(0.&40.)La4,(0.&40.)(40.(0.&40.)La5,(0.&40.)(40.(0.&40.)La6,(0.&40.)(40.(0.&40.)La7,(0.&40.)(40.(0.&40.)Lt3,(0.&40.)(40.(0.&40.)Lt4,(0.&40.)(40.(0.&40.)Lt5,(0.&40.)(40.(0.&40.)Lt6,(0.&40.)(40.$2.Lb1',$2.(40.(0.&8.)Lpgb,(0.&8.)(40.(0.&40.)Lj0,(0.&40.)(40.(0.&40.)Lj1,(0.&40.)(40.(0.&40.)Lj2,(0.&40.)(40.(3.(0.&40.))Lbs,(3.(0.&40.))(40.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(;.(19.$49.R1=.(4=.R1<.R1;.))(;.(19.$4:.R1<.(4>.(4?.O13.(30.&40.VSP,)O12.(30.&40.$50.)R15.R14.R13.O11.O10.(30.&40.VUB,)R12.R11.R10.R?.R>.R=.R<.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R;.R:.R9.R8.)O5.(51.O13.)O4.(2;.(0.&40.))R1.(52.$21.)))(;.A5.VK,Vu,Vf,R1:.R19.R1;.(;.(53.R1.R1;.)(;.(1?.VhAR,R1.R18.R1:.R17.R19.)(;.(68.A4.VCSf,Vu,Vf,R1:.R19.R1:.R19.)(;.(25.R1.)(;.(;.(5.+1.R16.)(5.R16.R18.))(;.(;.(5.O3.R18.)(5.R18.(6.O3.+1.)))(;.(;.(5.O2.R17.)(5.R17.(6.O2.(3?.+2.(6.Vd,+3.)))))(;.(5.(47.R17.(3?.+1?.(45.R17.(7.+2.+14.))))(6.(47.O2.(3?.+1?.(45.O2.(7.+2.+14.))))(6.Vd,+3.)))(;.Px,$2.P,A1.VCSc,R1.A5.VCSf,Vu,Vf,R1<.R1;.R2.(;.(40.(3.$2.)Lsn,(3.$2.)(40.(3.$2.)Lsb,(3.$2.)(;.(19.(3.$2.)R1<.(18.$2.Vnb0,R2.))(;.(19.(3.$2.)R1;.(18.$2.Vbl0,R1.))(;.(69.$2.Lb,$2.Px,$2.P,A1.VCSc,R1.(17.(;.(5.R3.R2.)(<.R2.(6.R3.(7.+2.+14.)))))R2.)(69.$2.Lb,$2.Px,$2.P,A1.VCSc,R1.(17.(;.(5.R3.R2.)(<.R2.(6.R3.(7.+2.+17.)))))R1.))))))(;.(58.(12.(13.$2.$2.)(14.$2.$2.Vlo,VSP,)(12.(13.$2.$2.)(14.$2.$2.$9.$:.)(12.(13.$2.$2.)(14.$2.$2.(6.VT,+:?0.)(6.VT,+<61.))$81.)))O1.R1.R1:.R19.)(;.(82.O1.R1.)(;.(20.$21.O1.R1.)(;.(54.$21.R1.)(;.(55.$21.R1.Vlo,VSP,)(;.(41.$21.R1.VCHB,(12.$42.(46.(30.&8.$6:.))(12.$42.(46.(30.&8.R7.))(12.$42.(6;.(30.&40.=))(12.$42.(5:.(30.&40.(5?.Vn,)))(12.$42.(56.(30.&40.(6<.(3?.VTID,(7.+2.+20.))R16.)))(15.$42.)))))))(;.(19.$2.(6=.R7.+3.)+1.)(;.(;.(5.=R7.)(<.R7.+100.))(;.P,(<.+10.(5=.Vn,))(41.$21.R2.VAB,(12.$42.(56.(30.&40.$6>.))(12.$42.(56.(30.&40.VCHB,))(15.$42.))))(;.(41.$21.R1.VSUB,(12.$42.(43.(44.(45.(5?.Vn,)+8.))(57.(0.&8.)(30.&8.=)(44.(45.(5?.Vn,)+8.))))(15.$42.)))(;.(41.$21.R1.VPGS,(12.$42.(46.(6?.Vn,R6.))(15.$42.)))(;.P,(19.$2.(3=.(5?.Vn,)+8.)=)(19.(1.(0.&8.))A1.R2.(83.VPGS,)A1.O1.(83.VPGS,))(;.(41.$21.R1.VUB,(12.$42.(43.(44.VKF,)(57.(0.&8.)(30.&8.+;>.)(44.VKF,)))(15.$42.)))(;.(41.$21.R1.(6.VT,+:?0.)(12.$42.(56.R5.)(12.$42.(56.R4.)(12.$42.(56.R3.)(15.$42.)))))(;.(5<.$21.R1.(6.VT,+;60.)R2.)(;.(19.$63.(>.(0.&40.)R2.)#20.)(41.$21.R1.(6.VT,+<60.)(12.$42.(46.(30.&8.=))(15.$42.))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

    Local Ltac2 Set LiaOrc.tbl := fun () => "0440@L10067488504.15 L10184698968.7  L10298762028.6  L10307921259.3  L10432845006.19 L11371687879.9  L12104406627.2  L12314936157.4  L12522026373.1  L12582944717.13 L12589220599.19 L12667050709.19 L13517127406.5  L13579960363.24 L13658889335.10 L15102277312.2  L15508334621.1  L15527186106.6  L15571301765.13 L16085917475.9  L16121740397.8  L1637893174.1   L1645577035.7   L16861361330.2  L16924645992.1  L16941726106.2  L16953760212.0  L17120848823.0  L17617975394.5  L17681108189.13 L17702421713.346L18100411007.1  L18302958969.1  L19032820896.7  L19469671376.15 L19935419217.13 L2016213390.6   L2022960349.1   L2031783603.1   L20352426335.4  L20515605447.9  L20569364719.19 L20569364719.20 L20575397333.22 L20610289741.22 L20879028953.14 L20957647993.4  L21620292829.13 L22013886778.7  L2250315199.13  L2284693595.14  L22993860706.9  L23200727809.7  L23249493300.11 L23249493300.18 L23249493300.7  L23343287261.0  L23591891289.1  L23858932922.9  L2420374951.2   L2426953944.24  L24371011332.20 L24560632610.19 L24661954803.9  L24888640626.2  L24897143244.3  L25705851087.2  L25762269614.19 L25783062314.22 L26250242907.21 L26394404329.14 L26443528976.24 L26498427253.14 L27466439871.3  L27848808849.2  L28352845277.13 L28573892092.8  L28762839709.0  L28807883413.11 L28934870315.6  L28980904646.24 L29718441094.4  L2978961816.0   L29836529785.1  L30487501431.14 L30633099225.1  L30787585704.1  L31920021602.22 L32382492013.2  L32447096858.1  L32952788708.21 L33092297043.21 L33237847169.4  L33437887829.13 L33437887829.14 L33444171887.19 L33708843013.9  L33722663298.14 L33945784403.3  L34239203029.7  L34301611314.13 L34301889471.8  L34303987252.14 L34304081326.11 L34304081326.18 L34304081326.7  L34307914268.4  L34307914268.6  L35247679960.20 L35688020061.14 L36119987158.5  L36193165570.2  L36415714444.3  L36747432620.19 L37062637461.4  L37099247901.5  L37181991793.19 L37181991793.20 L37396631557.0  L37637199976.0  L37808371721.11 L37880534170.24 L3813344308.4   L38235734261.1  L38411370647.14 L38650024428.24 L38700110972.1  L38968734492.7  L39188636933.0  L39220637093.0  L39315242130.2  L39332637397.0  L39477371493.2  L39651577319.6  L39812883104.8  L39831478948.2  L39953279860.6  L39982730872.24 L40186053667.24 L40507775107.3  L42043760438.21 L42150790267.5  L42307583955.14 L42409219784.3  L42757006147.16 L44072790135.4  L44072791548.8  L4414829022.19  L44345217427.2  L44716101839.24 L44876607696.3  L44880059389.14 L44916467928.8  L45295076406.1  L45334955688.1  L45578113577.24 L45594312987.7  L45705144536.6  L46071731361.10 L46590136587.22 L46736111460.11 L46798637366.1  L46902177661.2  L47386102014.2  L47539285122.8  L47695029500.5  L48191369178.1  L48349372034.14 L48364285643.24 L48793009578.2  L48872708136.9  L49303139973.22 L49305488319.20 L50001739424.6  L51164003032.19 L51362018088.1  L51765344620.1  L51802805993.24 L52286288041.21 L52310674614.1  L52566565077.19 L52566565077.20 L52635831073.0  L52694201704.1  L52786865963.19 L52786865963.20 L53285612562.8  L54508837114.2  L54570223649.3  L55296199685.24 L55400759076.14 L55588686165.0  L55899845783.3  L5600130087.13  L56294960569.9  L56376963496.1  L57056911013.7  L57274486538.19 L57368301315.17 L57545127939.10 L57841731802.3  L57924165753.1  L58086072525.7  L58339951995.21 L58535452555.16 L58850337863.14 L58850482141.12 L58850482141.19 L58850482141.8  L58913627406.0  L5916318900.0   L60204643024.6  L60742259251.14 L60951736609.3  L61027106802.2  L61030858054.315L61035084364.216L61323045984.7  L61323110347.9  L62209427327.1  L6286992857.14  L63330810425.7  L63368316718.217L63374621462.316L63443763453.14 L63737759283.1  L63897450449.5  L64346037083.14 L647770090.14   L64838801051.1  L6507294813.1   L65759562885.13 L66249744396.4  L66401606425.22 L6644560746.3   L66567258875.6  L67367103066.24 L6757205483.2   L67645412170.5  L67649359651.14 L67680528389.1  L68545323609.1  L68592373110.21 L6863246781.9   L6878027143.8   L7799702881.1   L7981005011.14  L8042593858.19  L8265267294.0   L8759167375.5   L8806423751.8   L8858115205.13  L8873338536.3   L8912407864.8   L8929606249.11  L9648528327.3   L9714519104.6   L9714519104.7   L9818858585.12  L984703108.14   00000K00Y00k01501c02902A02J02N02l03Z04B04W05M05c05j05o06H06b07>07[07_08608?08B08H08I08J08_09B0;?0;C0;F0;]0<G0<l0==0=A0=E0=N0=n0>W0?G0@:0@^0A?0AO0B20BA0B^0C;0CZ0D00DF0Dl0E>0E?0EC0E`0Eg0F]0GZ0HA0HX0HY0H]0Hd0ID0Io0J`0K:0L00LE0LO0LV0M90MO0MP0Mj0N<0O20O;0O<0O?0OS0OW0O[0PF0PN0PR0Q10Qb0Qk0RN0S:0T30TI0Tl0U70UJ0V10V?0Va0WB0X60XH0XY0Y30Y^0ZC0ZU0ZX0Zb0[J0[S0[a0\I0]80]90]:0]Z0^U0^X0^\0_A0`90`=0`O0`P0`Q0`W0`X0``0a80aR0a\0b30bn0cd0d10df0e40e[0eb0fL0fX0fg0gR0gY0hQ0h[0i<0iY0i]0ia0j\0k30kI0kW0l:0lV0lZ0lb0lk0mG0mO0mR0n50o00o70oN10J11911J11m12112513013b13f14S15G15H15K16416d17?17F17Q18G18f18g18n19S19j19n1:D1:]1;J1;`1;j1;m1<D1=91=P1=d1>F1?O1?m1?n1?o1@A1@f1A11A21B`1DG1D^1E51E91EZ1Ei1GP1I>1I_1Ic1Io1JL1Jk1K11K51KO1KX1LP1L[1M01Mk1N21N;1N`1Nd1Nh1O]1P81PS1PX1Q?1Qg1Qh1R=1RS1Rm1S81SJ1Se1So1TB1TU1U@1UkS3hAR2SP1n2SB3SPA2pw3Hrz2RCS1n2SB1c2pw2ABS1n2SB1c2pw2AB3AB0S3bl01j2HjS3hAR2SP1n2lo2SB5LOIMG2pw3SUB3PGS4AB1'3N2E3NDBS1n2SB1c2pw2AB2KF4N2B'S2SP3SPHS2SP4TOP2S2SPS3hAR2SP2lo3SPA5LOIMG2pw1A1k1HS3hAR2SP1n2lo2SB3SPA5LOIMG2pw4AB1'4ASHE1A1k2H2S3hAR1n2SB1c2pw2AB2KF3AB04RZSB3NFB1A1k1HS3hAR2SP2lo5LOIMG3SPLS3hAR1n2SB1c2pw2AB3SUB3PGS2KF4RZSB3nb'3NFB3KFB1k2Y42Y5S3bl'1j1A1w2H12H22n11lS1n3NFBS3CTXS3hAR2SP2lo5LOIMG3SPL3SPHS3hAR2SP2lo1T3SPA5LOIMG2T1S3hAR1n2SB1c2pw2AB4AB1'4ASHES3hAR2SP2lo5LOIMG3SPL3nb'1k1HS2SPS3hAR1n2SB1c2pw2AB4AB1'S3CTX3CX0S1TS1T2T0SSS3hAR2SP2lo5LOIMG3SPLS3hAR2SP1n1T2SB3SPA2pw3ABT3N2B4RZSBS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2pw2AB2UB3CHB3SUB3PGS2KF3ASH2tf2ws2bs4HL302HL3SB03tf'1A2sz2A'1k1H2H0S2SPS1TS1n2SB1c2pw2AB3AB04ASHES3hAR2SP1n2lo2SB3SPA5LOIMG2pw4AB1'3N2B3HrzS3hAR1n2lo2SB1c5LOIMG2pw2AB4AB1'4ASHES1n2SB1c2pw2AB2RCS2SPS2SPS2SP4TOP2S1n2SB1c2pw2AB3AB04RZSB4ASHE3NFBS3hAR1n1T2SB1c2pw2AB2KF2T04RZSB3NFB1A1k1HS3hAR2SP1n1T2SB1c3SPA2pw2AB2KF2T04RZSB3NFB1A1k1HS3hAR2SP1n2lo1T2SB5LOIMG3SPL2pw3SUB3PGS2KF2T11A1k1HS3hAR2SP1n2lo2SB2pw3SUB3PGS2KF1A1k1HS3hAR1n1T2SB1c2pw2AB3ABT3N2B4RZSBS2SP2lo3SPA4SPALS3hAR2SP1n1T2SB3SPA2pw3ABT3N2B4RZSBS3bl'1j1A2n02n2S3hAR2SP2lo3CTX3SPA5LOIMG3CX1S3hAR3nb02SP2lo3SPA5LOIMG1k1XS1n3CTX2SB1c2pw2AB3ABC3N2B4RZSBS3hAR2lo3CTX5LOIMG3CX1S3hAR2SB2RI1x3HSH4SBloS3hAR1T3CTX2SB2RI3CX02TC1x2HW4SBlo3GT'S3hAR1T1x4HLOW3GT'SS2SPS1n1T2SB1c2pw2AB3ABT3N2B4RZSBS2SP2loS3hAR1n2SB1c2pw2AB3SUB3PGS2KF4RZSB3bl'3NFB3KFB1j2Y42Y5S3hAR1n2lo1T2SB1c5LOIMG2pw2AB3AB04AB1'3RNG3TNS4ASHE1A1k2H12H2S3hAR2SP1n2lo2SB1c5LOIMG2pw2AB2KF1A1k1HS1n2SB1c2pw2AB3ASH4DIV8SS2SPS1n3NFBS3hAR1n2SB2pw3SUB3PGS3NFB3Hrz2RCS3hAR2SP1n2lo2SB3SPL2pw3SUB3PGS2KF1A1k1H2X1S3hAR1n1T2SB1c2pw2AB3SUB3PGS2KF4RZSB3NFB3KFB4X2''S3hAR1n2SB1c2pw2AB2KF4RZSBS3hAR1n2SB1c2pw2AB3SUB3PGS2KF4RZSB3bl'3NFB3KFB1j2Y32Y5S3hAR1n2SB1c2pw2AB2KFS3nb01k2HkS2SP2loS3hAR2SP1n1T2SB3SPA2pw3ABT3N2B4RZSBS2SP1n2lo1T2SB2pw1x2HxSS3hAR1n2SB1c2pw2AB3N2E3NDBS1n2SB1c2pw2AB3N2BS3hAR2SP1n2lo2SB1c5LOIMG2pw2AB3SUB3PGS2KF3bl'3NFB1j2Y5S2SP1q2HqSS1TS3hAR2SP2lo2pw1A1k1HS2SPS2SPS3hAR2SP1n2lo2SB3SPL2pw3SUB3PGS2KF1A1k1H2X2S2SP3SPHS2SPS3hAR1n1T2SB1c2pw2AB3SUB3PGS2KFS3hAR1n1T2SB1c2pw2AB3SUB3PGS2KF4RZSB3NFB3KFB4X1''S2SP4TOP2S3hAR2SP1n2SB3SPA2pw3AB04RZSB1A1k1HS3hAR2SP1n2lo2SB5LOIMG3SPL2pw4AB1'3N2B1A1k1HS3hAR2SP1n2SB3SPA2pw4AB1'3RNG3N2E3NDB4RZSB4ASHE1A1k2H12H2S1n2SB1c2pw2AB2KF4RZSBS3hAR2SP1n2lo1T2SB1c5LOIMG2pw2AB2T1S2SP2lo3SPLS3hAR2lo1T5LOIMG2T1S3nb01T3CTX2SB2RI1x2HW1k2Y12Y22Y33bl01jS1n2SB2pw1x2H8S1n2SB2pw1x2H82H93H103H111T2H73H12S3hAR1T2SB2RI1x3HSH4SBlo4RIhi3GT'S3hAR1T3CTX2SB2RI3CX02TC1x2HW4SBlo3ERI4SEP14SEP33GT'S3hAR1T1x4HLOW3GT'S3nb'1x1k1Y3bl'1jS3hAR3nb'1x4HLOW1k1Y3bl'1jS3hAR2SP1n2lo2SB1c3SPA5LOIMG2pw2AB2KF1A1k1HS1n2SB1c2pw2AB2UB3PGS3N2B4RZSB3NFB2X2S2SB2RI1x3HSH4SBloS1nS3bl'1j2HjS3hAR1n2SB2pw3SUB3PGS3N2E3NDB3NFB3Hrz2X2S2SP1q2HqS1n2SB1c2pw2ABS3hAR1n2SB1c2pw2AB2KF3AB04RZSB3NFB1A1k1HS3hAR2SP1n2SB1c3SPA2pw2AB2KF3AB04RZSB3NFB1A1k1HSSS3hAR1n2lo2SB1c5LOIMG2pw2AB4AB1'S3hAR1n2SB1c2pw2AB3SUB3PGS2KF4RZSB3nb'3NFB4N2B'3KFB1k2Y22Y5S1qS2loS1n2SB1c2pw2AB2UB3PGS3N2B4RZSB3NFB2X2S3hAR1n1T2SB1c2pw2AB3SUB3PGS2KF4RZSB3nb'3NFB3KFB1k2Y12Y5S2SPS1n2SB1c2pw2AB3N2BSSS1T2T0SS1n4NDB'S1d2tf4size3SZD3tf'4TFB'S1n2SB1c2pw2AB3ASH3N2E3NDBS4size3SZBS1d2tf4size3SZD3tf'3TFPS3hAR1n2SB1c2pw2AB3SUB3PGS2KF4RZSB3bl'3NFB4N2B'3KFB1j2Y22Y5S3hAR1n2SB1c2pw2AB3SUB3PGS2KF4RZSB3nb'3NFB3KFB1k2Y32Y5S3hAR3CTX3CX1S3hAR1n1T2SB1c2pw2AB3SUB3PGS2KF3ABT4RZSB3NFB4N2B'3KFBS3hAR2lo5LOIMGS3hAR3nb02SP1n2SB3SPA2pw3N2B4RZSB1k3APAS1A1k1HS3hAR2SP1n2lo2SB3SPA5LOIMG2pw2KF4AB1'4N2B'S2SP2lo1x2H1S2SP2lo2pw1x2H1S3hAR1n1T2SB2pw3SUB3PGS3ABT3N2E3NDB3NFB3HrzS1n3NFBS3hAR1n1T2SB1c2pw2AB3SUB3PGS2KF4RZSB3bl'3NFB3KFB1j2Y12Y5S3nb'1k2HkS3hAR1n1T2SB1c2pw2AB3ABT3N2B4RZSBS3hAR2SP2lo5LOIMG3SPL3bl'1j1HS2SPS2SPS3hAR1n2SB1c2pw2AB3SUB3PGS2KF4RZSB3bl'3NFB4N2B'3KFB1j2Y22Y5S3hAR1n2SB1c2pw2AB4AB1'S3hAR2SB2RI1x3HSH4RIhiS1A1w2H12H22HwS3hAR1n2SB1c2pw2AB2UB3SUB4AB1'4N2B'S3hAR1n2SB1c2pw2AB4AB1'4ASHES2SPS2SP3SPAS3CTX3CX0S1n2SB1c2pw2AB3AB04RZSB4ASHES1n4N2B'S1TS3hAR2SP1n2lo1T2SB1c5LOIMG2pw2AB2T1S3hAR1n2SB1c2pw2AB3SUB3PGS2KF4RZSB3nb'3NFB4N2B'3KFB1k2Y22Y5S3bl'1jS1n2SB1c2pw2AB3ASH4N2B'S3hAR2SP1n2lo2SB5LOIMG3SPL2pw3SUB3PGS2KF4AB1'4N2B'3KFB1A1k1HS3hAR2SP1n2SB1c3SPA2pw2AB2KF3AB04RZSB3NFB1A1k1HS1n2SB1c2pw2AB2RCS3hAR1n2SB1c2pw2AB2KF3AB03NFB1A1k1HS2SPS2SPS3hAR1n2SB1c2pw2AB3SUB3PGS2KF4RZSB3bl'3NFB4N2B'3KFB1j2Y22Y5S3hAR2SP1n2lo1T2SB1c5LOIMG2pw2AB3SUB3PGS2KF2T13NFBS2SPS3hAR1n2SB1c2pw2AB2KF3AB04RZSB4ASHE3NFB1A1k1HS3hAR2SP1n2SB1c3SPA2pw2AB2KF3AB04RZSB4ASHE3NFB1A1k1HSS1TS3hAR1n2SB1c2pw2AB2KF3AB04RZSB4ASHE1A1k1HS3hAR2SP1n2SB1c3SPA2pw2AB2KF3AB04RZSB4ASHE1A1k1HS3hAR1n2SB1c2pw2AB4AB1'3N2BS3nb'1kS2SP2lo3SPLS3hAR2SP1n2lo2SB1c5LOIMG2pw2AB3SUB3PGS2KF3nb'3NFB1k2Y5S2SP1n2lo2SB1c2pw2AB2UB3SUB3X1'SS1A1k1HS3hAR2SP1n3CTX2SB3SPA2pw3ABC3N2B4RZSBS1n2SB1c2pw2AB3ASH4N2B'S2SPS1n2SB1c2pw2AB3N2E3NDBS3hAR1n2SB2pw3SUB3PGS3HrzS3hAR1n2SB1c2pw2AB2UB3PGS4AB1'4ASHE4N2B'4PGSES3nb'1k1A1w2H12H22n11lS1n2KF3KFBS1TS1n2SB1c2pw2AB3AB04ASHES3hAR1n1T2SB1c2pw2AB3SUB3PGS2KF3ABT4RZSB3NFB4N2B'3KFBS3hAR2SP1n2SB3SPA2pw2KFS2SP1n2lo2SB2pw1x2H1S3hAR2SP2lo2SB2RI5LOIMG1x3HSH4RIhiS3hAR2SP2lo1T3CTX2SB2RI5LOIMG3CX03CX12TC1x2HW4SBlo3ERI4RIhi4SEP14SEP33GT'S3hAR2SP2lo1T5LOIMG1x4HLOW3GT'SSS1n2SB1c2pw2AB3AB0S1n2SB1c2pw2AB2UB3SUB3N2B4RZSB3NFB2X1S2SP2lo3SPLSS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2pw2AB2UB3CHB3SUB3PGS2KF3ASH2tf2ws2bs4HL302HL3SB03tf'S3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2pw2AB2UB3CHB3SUB3PGS2KF3ASH2ws2bs4HL302HL3SB0S1n2SB1c2pw2AB3ASH4RZSBS1n2SB1c2pw2AB3ASH4RZSBS2SPS3hAR1n1T2SB1c2pw2AB3ABT3N2B4RZSBS3nb'1k1A2n02n2S3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2pw2AB2UB3CHB3SUB3PGS2KF3ASH2ws2bs4HL302HL3SB0S3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2pw2AB2UB3CHB3SUB3PGS2KF3ASH2tf2ws2bs4HL302HL3SB03tf'S3hAR1n1T2SB1c2pw2AB3ABT3N2B4RZSBS2SPS1n3NFB1H2H0S3hAR3bl02SP2lo3SPA5LOIMG1j1XS2SP1n2lo2SB1c2pw2AB2UB3PGS3X2'S4sizeS2SPS3hAR2SP2lo1T3SPA5LOIMG2T1S2SP1q2HqS3hAR2SP1n2lo2SB5LOIMG3SPL2pw3SUB3PGS2KF4AB1'4N2B'1A1k1HS1n3N2E3NDBS1N3NB22N'2id3IDB3NB'S3hAR1n2SB1c2pw2AB3SUB3PGS2KF4RZSB3nb'3NFB4N2B'3KFB1k2Y22Y5S2SP2loS1n2H02H1S1n2SB1c2pw2AB2UB3SUB3N2B4RZSB3NFB2X1S2SPS2SPS3hAR1n1T2SB1c2pw2AB3SUB3PGS2KF3ABT4RZSB3NFB4N2B'3KFBS1n2SB1c2pw2AB3ASH4RZSB3NFBS1n2SB1c2pw2AB3ASH4RZSB3NFBS3CTXS3hAR3bl02SP1n2SB3SPA2pw3N2B4RZSB1j3APAS3hAR1n2SB2pw3SUB3PGS3N2E3NDB3NFB3Hrz2X1SS3hAR2SP2lo5LOIMG3SPLS2SP1n2lo1T2SB2pw1x2HxS3hAR2SP2lo1T3SPA5LOIMG2T1S2SP2lo3SPLS1n2SB1c2pw2AB3ASHS3hAR1n2SB1c2pw2AB3AB04ASHES3hAR1T2T1S1n2SB1c2pw2AB4RZSBS1n2SB1c2pw2AB4RZSBS3hAR2SP1n2lo2SB1c5LOIMG3SPL2pw2AB4AB1'3N2BS3hAR2SP1n2lo2SB1c5LOIMG2pw2AB2KF4AB1'4N2B'". (* [comment removed for export] *)
    #[using="AL IMG ALWF ASB CSOKf KL CSf_noshadow CSmono_n CSmono_s TOP mu mfa cs R RB FA UA FAA PCR NB FP LOIMG SPL SPA16 TOP2 TIDB TOPU TOPUB GSB GT GCTX GSEP GMU GMFA K_apart T_node T_store ROOM_n ROOM_s AB1 APTn APTs APCn APCs APSn APSs TCS CTXCS ACS SCS"] Theorem mseg_chunk : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pra,(0.&40.)Pgp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pw2,(0.&40.)Pw4,(0.&40.)Pw8,(0.&40.)Pj0,(0.&40.)Pj1,(0.&40.)Pj2,(0.&40.)Pmg0,(0.&40.)Pmg1,(0.&40.)Pb0,(0.&8.)Pb1,(0.&8.)Pshb,(0.&8.)Ppgb,(0.&8.)PF,(79.&5.(0.&40.))Pfc,(0.&20.)Pmc,P,(0.&40.)(1.(0.&8.))Pmoc,$2:.PN,$2.Ptf,$2.Psize,$2.Pws,(3.(0.&40.))Pbs,(3.(0.&40.))Psj,(3.(0.&8.))Puj,(3.(0.&8.))Pfr0,(3.(0.&8.))Pfr1,(3.(0.&8.))Pfr2,(3.(0.&8.))P,(1<.R<.VT,VCTX,)P,(26.R=.)P,(1>.R>.)P,(25.R?.)P,(7<.$21.R10.$84.(12.$42.(56.(30.&40.$85.))(15.$42.)))P,(7<.$21.R11.$86.(12.$42.(46.(30.&8.+1.))(15.$42.)))P,(7<.$21.R12.VT,(12.$42.(56.(30.&40.VCTX,))(15.$42.)))P,(7<.$21.R13.(6.VCTX,+8.)(12.$42.(5:.(30.&40.VTID,))(15.$42.)))P,(41.$21.R14.VCHB,(12.$42.(46.R1:.)(12.$42.(46.R19.)(12.$42.(6;.R22.)(12.$42.(5:.R21.)(12.$42.(56.R20.)(15.$42.)))))))P,P,(<.+10.(5=.Vn,))(41.$21.R16.VAB,(12.$42.(56.R1>.)(12.$42.(56.R1=.)(15.$42.))))P,(41.$21.R16.VUB,(12.$42.(43.(44.VKF,)R>.)(15.$42.)))P,(7<.$21.R17.VASH,(12.$42.(46.R1;.)(15.$42.)))P,(17.(19.$2.(39.&8.R1<.)=))P,(41.$21.R19.VSUB,(12.$42.(43.(44.(45.(5?.Vn,)+8.))R12.)(15.$42.)))P,(41.$21.R1:.VPGS,(12.$42.(46.R1=.)(15.$42.)))P,(75.R1;.VSPA,R12.+1.(30.&40.+47:64.)(30.&40.VSP,)(30.&40.Vn,)(30.&40.$76.)(30.&40.+1.)(30.&40.VSTK,)(30.&40.(6.VSP,-51.))R33.R32.R31.R30.R2?.R2>.)P,(41.$21.R1<.(6.VSTK,-10.)(12.$42.(56.(30.&40.VSP,))(12.$42.(56.(30.&40.+6978<.))(15.$42.))))P,(41.$21.R1=.(6.VSP,-38.)(12.$42.(56.R36.)(12.$42.(56.R37.)(12.$42.(56.R38.)(12.$42.(56.R39.)(12.$42.(56.R41.)(12.$42.(56.R42.)(12.$42.(56.R47.)(15.$42.)))))))))P,(41.$21.R1>.VSTK,(12.$42.(56.(30.&40.(6.VSTK,+10.)))(12.$42.(56.(30.&40.R1:.))(15.$42.))))P,(5<.$21.R1?.(6.VSTK,+10.)R1:.)P,(19.$63.(>.(0.&40.)R1;.)#1>.)P,(;.(5.+1.R1=.)(5.R1=.+1>.))P,(5.R1>.(6.Vd,+2.))P,(41.$21.R23.(6.VSTK,+100.)(12.$42.(43.#708.R19.)(15.$42.)))P,(41.$21.R24.(6.VSTK,+808.)(12.$42.(56.(30.&40.VSP,))(15.$42.)))P,(41.$21.R25.(6.VSTK,+810.)(12.$42.(43.#8.R1:.)(15.$42.)))P,(41.$21.R26.(6.VT,+<60.)(12.$42.(46.(30.&8.=))(15.$42.)))P,(41.$21.R27.(6.VT,+:?0.)(12.$42.(56.R32.)(12.$42.(56.R31.)(12.$42.(56.R30.)(15.$42.)))))P,(5<.$21.R28.(6.VT,+;60.)R22.)P,(19.$63.(>.(0.&40.)R23.)#20.)P,(1?.VhAR,R2:.R28.Vnb0,R27.Vbl0,)P,(68.VCSc,Vnb0,Vbl0,)P,(5.(6.R29.+80.)(7.+2.+20.))P,(5.(6.R2;.+2.)(47.(7.+2.+1?.)(7.+2.+1<.)))P,(55.$21.R2>.Vlo,(6.VSPA,-80.))P,(54.$21.R2?.)P,A5.VK,Vu,Vf,Vnb0,Vbl0,R2?.P,(53.R31.R30.)P,A4.VGn,Vu,Vf,Vnb0,Vbl0,P,A4.VGs,Vu,Vf,Vnb0,Vbl0,P,Px,$2.A4.VGs,Vu,Vf,(18.$2.Vnb0,(12.$2.R1.(15.$2.)))Vbl0,(87.$21.(88.R5?.R5>.R5:.R59.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R37.R36.R33.R32.R35.)(4=.(4>.(4?.(30.&40.+47=34.)(30.&40.(6.VSPA,-80.))R5>.(30.&40.$50.)R5=.R5<.R5;.(30.&40.(70.(71.Vn,)))(30.&40.(5?.Vn,))(30.&40.VAB,)R58.R57.R56.R55.R54.R53.R52.(30.&40.+8.)(30.&40.(73.Vn,))(30.&40.(5=.Vn,))(30.&40.Vn,)(30.&40.$72.)(30.&40.VSTK,)(30.&40.-8.)(30.&40.+7.)(30.&40.VT,)(30.&40.+1.)R47.R46.R45.R44.)R37.(30.&40.+47=34.)R36.(2;.(0.&40.))R35.(52.$21.))R34.))")
(* [comment removed for export] *).
    Proof.
      intros ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 w2 w4 w8 j0 j1 j2 mg0 mg1 b0 b1 shb pgb F fc mc moc N tf size ws bs sj uj fr0 fr1 fr2
        AS PS FS DST GOTFL PPART TH TIDC HDR MG UC SHC SHB SH PGC AFR FR16 FR7 STKC HTR HL30 SZB SZD F1800 TFBP F8 UNW STH STB HL DI DCS TFMAX NB2 ST MI HK HJ GN GS GSX.
      facts. pose proof T0 as T0. pose proof T1 as T1. pose proof CX0 as CX0. pose proof CX1 as CX1. pose proof TC as TC. pose proof SB0 as SB0. pose proof SBAL as SBAL.
      pose proof SPH as SPH. pose proof AB0 as AB0. pose proof AB1' as AB1'. pose proof ABT as ABT. pose proof ABC as ABC. pose proof RNG as RNG. pose proof TNS as TNS. pose proof CTXNS as CTXNS.
      pose proof AB_al as ABAL. pose proof needed2_prim as [N2E NDB']. pose proof c_range as CR.
      assert (NDB : 24 <= needed n) by (clear - NDB'; lia).
      assert (N2B : rz_size n + 8 <= needed2 n).
      { rewrite N2E. unfold needed, rounded, round_up. pose proof (rz_size_bound n). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). clear - H H0 H1 NB. lia. }
      pose proof (rz_size_bound n) as RZSB.
      assert (SPAL : lo <= SPA - 512) by (subst SPA STK; clear - SPL; lia). assert (SPAH : SPA <= 2^62) by (subst SPA STK; clear - SPH; lia).
      assert (SPAAL : SPA mod 16 = 0).
      { subst SPA STK. clear - SPA16. apply Z.mod_divide in SPA16; [| lia]. apply Z.mod_divide; [lia|]. destruct SPA16 as [q Hq]. exists (q - 134). lia. }
      assert (SCSA : crange CSc lo (SPA - lo)) by (eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear; lia| subst SPA STK; clear; lia]).
      (* [comment removed for export] *)
      eapply (evtA_aevtS_KJ AL CSc (K u f nb0 bl0)
                (hdr_post SPA gp (Z_to_bv 64 A_TP) (Z_to_bv 64 A_INSTANCE) (Z_to_bv 64 STK) t3 t4 t5 t6 F fc n AB STK T (STK + 16) size TID 1 lo b0 w8
                   (Z_to_bv 64 0x47a64) (Z_to_bv 64 SP) (Z_to_bv 64 n) (Z_to_bv 64 A_PC_MALLOC) (Z_to_bv 64 1) (Z_to_bv 64 STK) (Z_to_bv 64 (SP + -81)) s6 s7 s8 s9 s10 s11 fr0 [] mc)
                _ _ moc (KL u f nb0 bl0) HK); [exact HJ| |].
      { eapply (alloc_hdr AL IMG ALWF CSc (CSOKf u f nb0 bl0)) with (CTX := CTX);
          [ exact NB | clear - AB0; lia | clear - AB1'; lia | exact ABAL | clear - SPL LOIMG SPH; try subst STK; lia | clear - SZB; lia | exact TIDB | clear; lia
          | clear - SPL LOIMG; try subst STK; lia | subst STK SPA; clear; lia | clear - SPH; try subst STK; lia | |
          | exact T0 | exact T1 | exact TCS | exact CX0 | exact CX1 | exact CTXCS | | | | |
          | exact AFR | exact HDR | exact TH | exact TIDC | | exact ST | exact LOIMG | clear - SPAL; lia | exact SPAH | exact SPAAL | exact SCSA | apply munch_refl | apply wmono_refl | exact MI ].
        - subst STK. clear - SPA16. apply Z.mod_divide in SPA16; [|lia]. destruct SPA16 as [q Hq]. rewrite Hq. replace (q * 16 + -2128) with ((2 * q - 266) * 8) by lia. apply Z_mod_mult.
        - eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear - SPL; try subst STK; lia| subst STK; clear; lia].
        - eapply (crange_sub _ AB (needed2 n)); [exact ACS| clear - RZSB; lia| clear - N2B; lia].
        - left. subst STK. clear - AB1' N2B LOIMG SPL. lia.
        - clear - AB1' N2B. lia.
        - clear - ABT N2B RZSB. lia.
        - clear - ABC N2B RZSB. lia.
        - destruct STKC as [STKC0 _]. exact STKC0. }
      cbn beta. intros ms2 mo2 PO HK2 MM2 HJ2. unfold hdr_post in PO.
      ddestruct PO as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & b1n & m2 & -> & MU2 & WM2 & MI2 & HDR2 & B1A & B1B & AFR2 & ST2). cbn [ms_mem MS MSsvc] in HJ2.
      rewrite FP. change (Z.b2z true) with 1.
      fold UB in HDR2 |- *. fold CHB in MU2, HDR2 |- *.
      (* [comment removed for export] *)
      assert (DJW : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from [(lo, SPA); (CHB, CHB + 8)] A k).
      { intros A k H. cbn [disjoint_from]. subst CHB AB c. clear - H AB0 RZSB LOIMG. repeat split; lia. }
      assert (DJhi : forall A k, SPA <= A -> disjoint_from [(lo, SPA); (CHB, CHB + 8)] A k).
      { intros A k H. cbn [disjoint_from]. subst CHB AB c SPA STK. clear - H AB1' RZSB N2B LOIMG SPL. repeat split; lia. }
      dpose (proj1 (proj2 (proj2 DI))) as (_ & DMF & _).
      dpose (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DI)))))))) as (_ & DBF & _).
      assert (DI2 : depot_inv m2 N nb0 tf bl0).
      { eapply (depot_inv_transport _ mc m2 N nb0 tf bl0 DI MU2 WM2 DJW).
        - intros k Hk. pose proof (APAn k Hk) as APA.
          dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb0) DMF (Z.to_nat k) 0 ltac:(clear - Hk; lia)) as (_ & X & _).
          cbn [disjoint_from]. subst CHB AB c. unfold dblk in *. clear - APA X LOIMG N2B RZSB. repeat split; lia.
        - intros j Hj. pose proof (APAs j Hj) as APA.
          dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl0) DBF (Z.to_nat j) 0 ltac:(clear - Hj; lia)) as (_ & X & _).
          cbn [disjoint_from]. subst CHB AB c. unfold sblk in *. clear - APA X LOIMG N2B RZSB. repeat split; lia. }
      assert (DST2 : depot_statics m2) by (eapply (depot_statics_transport _ mc m2 DST MU2); intros A k H; apply DJW; clear - H; lia).
      assert (SCS2 : crange CSc lo (SPA + -128 - lo)) by (eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear; lia| subst SPA STK; clear; lia]).
      assert (TCS2 : crange CSc (STK + 16) 240) by (eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear - SPL; try subst STK; lia| subst STK; clear; lia]).
      assert (SPAAL2 : (SPA + -128) mod 16 = 0).
      { subst SPA STK. clear - SPA16. apply Z.mod_divide in SPA16; [| lia]. apply Z.mod_divide; [lia|]. destruct SPA16 as [q Hq]. exists (q - 142). lia. }
      assert (TRAL : (STK + 16) mod 8 = 0).
      { subst STK. clear - SPA16. apply Z.mod_divide in SPA16; [| lia]. apply Z.mod_divide; [lia|]. destruct SPA16 as [q Hq]. exists (2 * q - 264). lia. }
      assert (HTR2 : u64arr asegs m2 (STK + 16) ws) by (eapply u64arr_transport; [exact HTR| exact MU2| exact WM2| apply DJhi; subst SPA STK; clear; lia]).
      eapply aevtS_bind.
      { replace (Z_to_bv 64 size) with (Z_to_bv 64 (size + 0 * 2^32)) by (f_equal; clear; lia).
        eapply (depot_put_cfg AL IMG ALWF (CSf u f) (K u f) (CSOKf u f) (KL u f) (CSmono_n u f) (CSmono_s u f) (K_apart u f) (Gn u f) (Gs u f)
                  (T_node u f) (T_store u f) (ROOM_n u f) (ROOM_s u f)) with (lo := lo);
          first [exact HK2| exact HJ2| exact MI2| exact DI2| exact DST2| exact HTR2| exact HL30| exact SZB| exact DCS| exact ST2| exact SCS2| exact TCS2| exact LOIMG
                | exact SPAAL2| exact TRAL| exact TFMAX| exact NB2| exact GN| exact GS| exact GSX| idtac].
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
      dpose (proj1 (proj2 (proj2 DI3))) as (_ & DMF3 & _).
      dpose (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DI3)))))))) as (_ & DBF3 & _).
      assert (BN : forall k, 0 <= k < Z.of_nat (length nb') -> 0x65f000 <= dblk nb' k /\ dblk nb' k + 2^20 <= ACEIL).
      { intros k Hk. dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb') DMF3 (Z.to_nat k) 0 ltac:(clear - Hk; lia)) as (X & Y & _).
        unfold dblk. split; [exact X| exact Y]. }
      assert (BS : forall j, 0 <= j < Z.of_nat (length bl') -> 0x65f000 <= sblk bl' j /\ sblk bl' j + 2^23 <= ACEIL).
      { intros j Hj. dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl') DBF3 (Z.to_nat j) 0 ltac:(clear - Hj; lia)) as (X & Y & _).
        unfold sblk. split; [exact X| exact Y]. }
      assert (BNold : forall k (A w : Z), 0 <= k < Z.of_nat (length nb') -> crange CSc A w -> 0 < w ->
                (forall k0, 0 <= k0 < Z.of_nat (length nb0) -> A + w <= dblk nb0 k0 \/ dblk nb0 k0 + 2^20 <= A) ->
                A + w <= dblk nb' k \/ dblk nb' k + 2^20 <= A).
      { intros k A w Hk CR0 Hw OLD. rewrite Enb in Hk |- *. destruct (dblk_app_cases nb0 sn k Hk) as [[Hk' ->]| HIn].
        - apply OLD. exact Hk'.
        - eapply (apart_of_cs CSc A w _ (2^20) CR0); [| exact Hw| clear; lia]. exact (proj1 (Forall_forall _ _) Fn _ HIn). }
      assert (BSold : forall j (A w : Z), 0 <= j < Z.of_nat (length bl') -> crange CSc A w -> 0 < w ->
                (forall j0, 0 <= j0 < Z.of_nat (length bl0) -> A + w <= sblk bl0 j0 \/ sblk bl0 j0 + 2^23 <= A) ->
                A + w <= sblk bl' j \/ sblk bl' j + 2^23 <= A).
      { intros j A w Hj CR0 Hw OLD. rewrite Ebl in Hj |- *. destruct (sblk_app_cases bl0 sb j Hj) as [[Hj' ->]| HIn].
        - apply OLD. exact Hj'.
        - eapply (apart_of_cs CSc A w _ (2^23) CR0); [| exact Hw| clear; lia]. exact (proj1 (Forall_forall _ _) Fs _ HIn). }
      destruct DCS3 as [NBCS3 BLCS3].
      assert (BNsh : forall k (A w : Z), 0 <= k < Z.of_nat (length nb') -> 0x7fff8000 <= A -> A + w <= 0x10007fff8000 -> 0 < w ->
                A + w <= dblk nb' k \/ dblk nb' k + 2^20 <= A).
      { intros k A w Hk H1 H2 Hw. specialize (NBCS3 k Hk).
        destruct (Z_le_dec (dblk nb' k + 2^20) A); [right; assumption|]. destruct (Z_le_dec (A + w) (dblk nb' k)); [left; assumption|]. exfalso.
        destruct (Z_le_dec A (dblk nb' k)).
        - apply (CSf_noshadow u f nb' bl' (dblk nb' k)); [apply NBCS3; clear; lia| clear - H1 H2 Hw n0 n1 l; lia].
        - apply (CSf_noshadow u f nb' bl' A); [apply NBCS3; clear - n0 n1 n2; lia| clear - H1 H2 Hw n0 n1 n2; lia]. }
      assert (BSsh : forall j (A w : Z), 0 <= j < Z.of_nat (length bl') -> 0x7fff8000 <= A -> A + w <= 0x10007fff8000 -> 0 < w ->
                A + w <= sblk bl' j \/ sblk bl' j + 2^23 <= A).
      { intros j A w Hj H1 H2 Hw. specialize (BLCS3 j Hj).
        destruct (Z_le_dec (sblk bl' j + 2^23) A); [right; assumption|]. destruct (Z_le_dec (A + w) (sblk bl' j)); [left; assumption|]. exfalso.
        destruct (Z_le_dec A (sblk bl' j)).
        - apply (CSf_noshadow u f nb' bl' (sblk bl' j)); [apply BLCS3; clear; lia| clear - H1 H2 Hw n0 n1 l; lia].
        - apply (CSf_noshadow u f nb' bl' A); [apply BLCS3; clear - n0 n1 n2; lia| clear - H1 H2 Hw n0 n1 n2; lia]. }
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
      { eapply (dkeep_window m2 m3 lo (SPA + -128) nb' bl' AB (needed2 n) DK3); [clear - AB0; lia| clear - AB1'; lia| left; subst SPA STK; clear - AB1' LOIMG SPL; lia| unfold A_SS, A_DEP_END; clear - AB0; lia| |].
        - intros k Hk. apply (BNold k AB (needed2 n) Hk ACS ltac:(clear - NDB N2E; lia) APAn).
        - intros j Hj. apply (BSold j AB (needed2 n) Hj ACS ltac:(clear - NDB N2E; lia) APAs). }
      assert (ASHE : Z.shiftr AB 3 = AB / 8) by (rewrite Z.shiftr_div_pow2 by (clear; lia); reflexivity).
      assert (MUSH : munch [(0, ASH); (ASH + (needed2 n / 8 + 2), 2^64)] m2 m3).
      { eapply (dkeep_window m2 m3 lo (SPA + -128) nb' bl' ASH (needed2 n / 8 + 2) DK3);
          [clear - AB0 ASHE; try subst ASH; lia| clear - AB0 AB1' ASHE; try subst ASH; lia| left; subst ASH SPA STK; clear - AB0 AB1' ASHE LOIMG SPL; lia
          | unfold A_SS, A_DEP_END; clear - AB0 ASHE; try subst ASH; lia| |].
        - intros k Hk. apply (BNsh k ASH (needed2 n / 8 + 2) Hk); clear - AB0 AB1' ASHE NDB N2E; try subst ASH; lia.
        - intros j Hj. apply (BSsh j ASH (needed2 n / 8 + 2) Hj); clear - AB0 AB1' ASHE NDB N2E; try subst ASH; lia. }
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
      assert (DIV8 : rz_size n / 8 + nfix n / 8 <= needed2 n / 8).
      { pose proof (rz_size_cases n) as RC. pose proof (Z.div_mod (nfix n) 8 ltac:(clear; lia)). pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(clear; lia)).
        apply Z.div_le_lower_bound; [clear; lia|]. clear - RC H H0 N2B'. lia. }
      assert (SHW : forall A k, ASH <= A -> A + k <= ASH + (needed2 n / 8 + 2) -> disjoint_from [(lo, SPA); (CHB, CHB + 8)] A k).
      { intros A k H1 H2. cbn [disjoint_from]. subst ASH CHB AB c. clear - H1 H2 ASHE AB0 AB1' LOIMG RNG NDB N2E RZSB. repeat split; lia. }
      assert (AS2 : allocA_statics m2 T CTX).
      { eapply (allocA_statics_transport _ mc m2 T CTX AS MU2); [intros A k H; apply DJW; exact H|]. cbn [disjoint_from]. subst CHB AB c. clear - LOIMG CX1 ABC N2B RZSB. repeat split; lia. }
      assert (PS2 : poison_statics m2) by (eapply (poison_statics_transport _ mc m2 PS MU2); intros A k H; apply DJW; clear - H; lia).
      assert (FS2 : fin_statics m2) by (eapply (fin_statics_transport _ mc m2 FS MU2); intros A k H; apply DJW; exact H).
      assert (GOTFL2 : ro_cells asegs m2 A_GOT_FLAGS [C8 (Z_to_bv 64 A_FLAGS)]) by (eapply ro_cells_transport; [exact GOTFL| exact MU2| apply DJW; unfold A_GOT_FLAGS; cbn; clear; lia]).
      assert (PPART2 : ro_cells asegs m2 A_FL_PPART [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact PPART| exact MU2| apply DJW; unfold A_FL_PPART; cbn; clear; lia]).
      assert (SHC2 : ro_cells asegs m2 ASH [C1 shb]) by (eapply ro_cells_transport; [exact SHC| exact MU2| apply SHW; cbn; clear - NDB N2E; lia]).
      assert (SH2 : rw_cells asegs m2 SUB [CB (Z.to_nat (nfix n / 8)) sj]).
      { eapply rw_cells_transport; [exact SH| exact MU2| exact WM2| apply SHW; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - NFB; lia); rewrite SUBE; clear - N2B' NFB RZSB; lia]. }
      assert (PGC2 : rw_cells asegs m2 PGS [C1 pgb]).
      { eapply rw_cells_transport; [exact PGC| exact MU2| exact WM2| apply SHW; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat]; rewrite PGSE; clear - DIV8 NFB RZSB; lia]. }
      assert (STH2 : rw_cells asegs m2 (T + 2800) [C8 j0; C8 j1; C8 j2]).
      { eapply rw_cells_transport; [exact STH| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. subst CHB AB c. clear - LOIMG T1 ABT N2B RZSB. repeat split; lia. }
      assert (STB2 : u64arr asegs m2 (T + 2912) bs).
      { eapply u64arr_transport; [exact STB| exact MU2| exact WM2|]. rewrite HL. cbn [disjoint_from Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul]. subst CHB AB c. clear - LOIMG T1 ABT N2B RZSB. repeat split; lia. }
      assert (UC2 : rw_cells asegs m2 UB [CB (Z.to_nat KF) uj]).
      { eapply rw_cells_transport; [exact UC| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by (clear - KFB; lia).
        subst UB CHB AB c. clear - LOIMG T1 ABT N2B' KFB RZSB AB1'. repeat split; lia. }
      assert (MG2 : 16 < rz_size n -> rw_cells asegs m2 AB [C8 mg0; C8 mg1]).
      { intros Hrz. eapply rw_cells_transport; [exact (MG Hrz)| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add].
        pose proof (rz_size_cases n) as RC. subst CHB AB c. clear - LOIMG T1 ABT N2B RC Hrz AB1'. repeat split; lia. }
      assert (UNW2 : rw_cells asegs m2 (T + 3168) [C1 (Z_to_bv 8 0)]).
      { eapply rw_cells_transport; [exact UNW| exact MU2| exact WM2|]. cbn [disjoint_from cells_size csize Nat.add]. subst CHB AB c. clear - LOIMG T1 ABT N2B RZSB. repeat split; lia. }
      assert (FR16' : rw_cells asegs m2 (STK + -16) [C8 (Z_to_bv 64 SP); C8 (Z_to_bv 64 0x6978c)]) by (eapply rw_cells_transport; [exact FR16| exact MU2| exact WM2| apply DJhi; subst SPA STK; clear; lia]).
      assert (FR7' : rw_cells asegs m2 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_transport; [exact FR7| exact MU2| exact WM2| apply DJhi; subst SPA STK; clear; lia]).
      assert (STKC2 : rw_cells asegs m2 STK [C8 (Z_to_bv 64 (STK + 16)); C8 (Z_to_bv 64 size)]) by (eapply rw_cells_transport; [exact STKC| exact MU2| exact WM2| apply DJhi; subst SPA STK; clear; lia]).
      assert (F1800' : rw_cells asegs m2 (STK + 256) [CB 1800 fr1]) by (eapply rw_cells_transport; [exact F1800| exact MU2| exact WM2| apply DJhi; subst SPA STK; clear; lia]).
      assert (TFBP' : rw_cells asegs m2 (STK + 2056) [C8 (Z_to_bv 64 SP)]) by (eapply rw_cells_transport; [exact TFBP| exact MU2| exact WM2| apply DJhi; subst SPA STK; clear; lia]).
      assert (F8' : rw_cells asegs m2 (STK + 2064) [CB 8 fr2]) by (eapply rw_cells_transport; [exact F8| exact MU2| exact WM2| apply DJhi; subst SPA STK; clear; lia]).
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
      assert (UNW3 : rw_cells asegs m3 (T + 3168) [C1 (Z_to_bv 8 0)]) by (eapply rw_cells_transport; [exact UNW2| exact MUT| exact WM3| apply WD; cbn; clear; lia]).
      assert (FR7'3 : rw_cells asegs m3 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_transport; [exact FR7'| exact MUST| exact WM3| apply WD; cbn; subst SPA STK; clear; lia]).
      assert (STKC3 : rw_cells asegs m3 STK [C8 (Z_to_bv 64 (STK + 16)); C8 (Z_to_bv 64 size)]) by (eapply rw_cells_transport; [exact STKC2| exact MUST| exact WM3| apply WD; cbn; subst SPA STK; clear; lia]).
      assert (F1800'3 : rw_cells asegs m3 (STK + 256) [CB 1800 fr1]) by (eapply rw_cells_transport; [exact F1800'| exact MUST| exact WM3| apply WD; cbn; subst SPA STK; clear; lia]).
      assert (TFBP'3 : rw_cells asegs m3 (STK + 2056) [C8 (Z_to_bv 64 SP)]) by (eapply rw_cells_transport; [exact TFBP'| exact MUST| exact WM3| apply WD; cbn; subst SPA STK; clear; lia]).
      assert (F8'3 : rw_cells asegs m3 (STK + 2064) [CB 8 fr2]) by (eapply rw_cells_transport; [exact F8'| exact MUST| exact WM3| apply WD; cbn; subst SPA STK; clear; lia]).
      assert (FR16'3 : rw_cells asegs m3 (STK + -16) [C8 (Z_to_bv 64 SP); C8 (Z_to_bv 64 0x6978c)]) by (eapply rw_cells_transport; [exact FR16'| exact MUST| exact WM3| apply WD; cbn; subst SPA STK; clear; lia]).
      assert (TCS3 : crange (CSf u f nb' bl') T 4096) by (exact (crange_mono _ _ _ _ TCS CSM)).
      assert (CTXCS3 : crange (CSf u f nb' bl') CTX 0x10000) by (exact (crange_mono _ _ _ _ CTXCS CSM)).
      assert (ACS3 : crange (CSf u f nb' bl') AB (needed2 n)) by (exact (crange_mono _ _ _ _ ACS CSM)).
      assert (SCS3 : crange (CSf u f nb' bl') lo (SP - lo)) by (exact (crange_mono _ _ _ _ SCS CSM)).
      assert (IDB' : 0 <= id < 2^31) by (clear - IDB NB' NB2; lia).
      clear AS2 PS2 FS2 GOTFL2 PPART2 SHC2 SH2 PGC2 STH2 STB2 UC2 MG2.
      assert (SHAP : forall A k, ASH <= A -> A + k <= ASH + (needed2 n / 8 + 2) ->
                (A + k <= AB \/ AB + needed2 n <= A) /\ A + k <= lo /\ (A + k <= T \/ T + 4096 <= A)).
      { intros A k H1 H2. subst ASH. clear - H1 H2 ASHE AB0 AB1' LOIMG TNS RNG NDB N2E. lia. }
      (* [comment removed for export] *)
      eapply (evtA_aevtS_KJ AL (CSf u f nb' bl') (K u f nb' bl')
                (fun ms' => exists (z0 z1 z2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 z3 z4 z5 z6 j0' j1' j2' : word) (bs' : list word) (m5 : mem),
                   ms' = MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 A_TP) z0 z1 z2 s0 s1 (Z_to_bv 64 UB) ya1 ya2 ya3 ya4 ya5 ya6 ya7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
                            F (ret_pc ra) fc None m5 (seg_rom asegs)
                   /\ munch [(lo, SP); (CHB, CHB + 16); (AB, AB + 16); (SUB, SUB + nfix n / 8); (PGS, PGS + 1); (T + 2800, T + 3168); (UB, UB + KF)] m3 m5
                   /\ wmono asegs m3 m5 /\ mem_inv asegs m5
                   /\ rw_cells asegs m5 CHB [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 (Z.land b1n 243)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nfix n)); C8 (Z_to_bv 64 (Z.lor (TID * 2^32) id))]
                   /\ (16 < rz_size n -> rw_cells asegs m5 AB [C8 (Z_to_bv 64 kAllocBegMagic); C8 (Z_to_bv 64 CHB)])
                   /\ rw_cells asegs m5 SUB [CB (Z.to_nat (nfix n / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (nfix n / 8)))]
                   /\ rw_cells asegs m5 PGS [C1 (pgv n pgb)]
                   /\ rw_cells asegs m5 (T + 2800) [C8 j0'; C8 j1'; C8 j2'] /\ u64arr asegs m5 (T + 2912) bs' /\ length bs' = 32%nat
                   /\ rw_cells asegs m5 UB [CB (Z.to_nat KF) (repeat (Z_to_bv 8 0xbe) (Z.to_nat KF))]
                   /\ stk asegs m5 lo SP)
                _ _ mo3 (KL u f nb' bl') HK3); [exact HJ3| |].
      {
        eapply evtA_cut.
        { eapply (msegC1 AL IMG ALWF (CSf u f nb' bl') (CSOKf u f nb' bl') SP n lo T CTX TID SB pw);
            first [sassumption | cassumption | exact NB| exact FP| exact LOIMG| exact SPL| exact SPH| exact SPA16| exact T0| exact T1| exact CX0| exact CX1| exact TC| exact TIDB| exact SB0| exact SBAL
                  | exact AB0| exact AB1'| exact ABT| exact ABC| exact ASB| exact TNS| exact CTXNS| exact IDB'| exact B1B| exact SHB| exact RNG
                  | exact AS3| exact TCS3| exact CTXCS3| exact PS3| exact FS3| exact GOTFL3| exact PPART3| exact ACS3| exact HDR3| exact SHC3| exact SH3| exact PGC3
                  | exact STH3| exact STB3| exact HL| exact UC3| exact AFR3| exact ST3| exact SCS3| exact MI3]. }
        cbn beta. (intros ms4 dd_H; ddestruct dd_H as (x1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y22 & y28 & y29 & y30 & y31 & j0' & j1' & j2' & bs' & m4 & -> &
                              MU4 & WM4 & MI4 & AFR4 & HDR4 & SH4 & PGC4 & STH4 & STB4 & HL4 & UC4 & ST4)).
        assert (DJ4lo : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from [(lo, SPA + -128); (CHB + 8, CHB + 16); (SUB, SUB + nfix n / 8); (PGS, PGS + 1); (T + 2800, T + 3168); (UB, UB + KF)] A k).
        { intros A k H. cbn [disjoint_from]. rewrite SUBE, PGSE. subst UB CHB ASH. clear - H T0 AB0 RZSB LOIMG ASHE NFB. repeat split; lia. }
        assert (DJ4hi : forall A k, SPA <= A -> disjoint_from [(lo, SPA + -128); (CHB + 8, CHB + 16); (SUB, SUB + nfix n / 8); (PGS, PGS + 1); (T + 2800, T + 3168); (UB, UB + KF)] A k).
        { intros A k H. dpose (SHAP SUB (nfix n / 8) ltac:(rewrite SUBE; clear - RZSB; lia) ltac:(rewrite SUBE; clear - RZSB NFB N2B'; lia)) as (_ & X1 & _).
          dpose (SHAP PGS 1 ltac:(rewrite PGSE; clear - RZSB NFB; lia) ltac:(rewrite PGSE; clear - RZSB NFB N2B'; lia)) as (_ & X2 & _).
          cbn [disjoint_from]. subst UB CHB AB SPA STK c. clear - H X1 X2 T1 AB1' LOIMG SPL N2B' KFB RZSB. repeat split; lia. }
        assert (FS4 : fin_statics m4) by (eapply (fin_statics_transport _ m3 m4 FS3 MU4); exact DJ4lo).
        assert (MG4 : 16 < rz_size n -> rw_cells asegs m4 AB [C8 mg0; C8 mg1]).
        { intros Hrz. dpose (SHAP SUB (nfix n / 8) ltac:(rewrite SUBE; clear - RZSB; lia) ltac:(rewrite SUBE; clear - RZSB NFB N2B'; lia)) as (X1 & _ & _).
          dpose (SHAP PGS 1 ltac:(rewrite PGSE; clear - RZSB NFB; lia) ltac:(rewrite PGSE; clear - RZSB NFB N2B'; lia)) as (X2 & _ & _).
          eapply rw_cells_transport; [exact (MG3 Hrz)| exact MU4| exact WM4|]. cbn [disjoint_from cells_size csize Nat.add].
          pose proof (rz_size_cases n) as RC. subst UB CHB AB c. clear - X1 X2 LOIMG AB1' ABT RC Hrz NDB N2E NFB. repeat split; lia. }
        assert (AFR'4 : rw_cells asegs m4 (STK + -16) [C8 (Z_to_bv 64 SP); C8 (Z_to_bv 64 0x6978c)]) by (eapply rw_cells_transport; [exact FR16'3| exact MU4| exact WM4| apply DJ4hi; subst SPA STK; clear; lia]).
        assert (FR7'4 : rw_cells asegs m4 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (eapply rw_cells_transport; [exact FR7'3| exact MU4| exact WM4| apply DJ4hi; subst SPA STK; clear; lia]).
        assert (STKC4 : rw_cells asegs m4 STK [C8 (Z_to_bv 64 (STK + 16)); C8 (Z_to_bv 64 size)]) by (eapply rw_cells_transport; [exact STKC3| exact MU4| exact WM4| apply DJ4hi; subst SPA STK; clear; lia]).
        assert (HTR4 : u64arr asegs m4 (STK + 16) ws) by (eapply u64arr_transport; [exact HTR3| exact MU4| exact WM4| apply DJ4hi; subst SPA STK; clear; lia]).
        assert (F1800'4 : rw_cells asegs m4 (STK + 256) [CB 1800 fr1]) by (eapply rw_cells_transport; [exact F1800'3| exact MU4| exact WM4| apply DJ4hi; subst SPA STK; clear; lia]).
        assert (TFBP'4 : rw_cells asegs m4 (STK + 2056) [C8 (Z_to_bv 64 SP)]) by (eapply rw_cells_transport; [exact TFBP'3| exact MU4| exact WM4| apply DJ4hi; subst SPA STK; clear; lia]).
        assert (F8'4 : rw_cells asegs m4 (STK + 2064) [CB 8 fr2]) by (eapply rw_cells_transport; [exact F8'3| exact MU4| exact WM4| apply DJ4hi; subst SPA STK; clear; lia]).
        eapply evtA_mono.
        { eapply (msegC2 AL IMG ALWF (CSf u f nb' bl') (CSOKf u f nb' bl') SP n lo T TID SB pw) with (q0 := s0) (q1 := s1) (q2 := s2) (q3 := s3) (q4 := s4) (q5 := s5);
            first [exact NB| exact FP| exact LOIMG| exact SPL| exact SPH| exact SPA16| exact T0| exact T1| exact TIDB| exact SB0| exact SBAL
                  | exact AB0| exact AB1'| exact ABT| exact ASB| exact TNS| exact B1B| exact ACS3| exact FS4| exact HDR4| exact MG4| exact AFR4| exact AFR'4| exact FR7'4
                  | exact STKC4| exact HTR4| exact HL30| exact F1800'4| exact TFBP'4| exact F8'4| exact ST4| exact SCS3| exact MI4| idtac].
          all: match goal with |- ?G => fail "msegC2 side" G end. }
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
                 subst UB CHB. clear - LOIMG AB1' N2B' KFB RZSB. repeat split; lia. }
        exact ST5. }
      (* [comment removed for export] *)
      cbn beta. intros ms5 mo5 PO5 HK5 MM5 HJ5.
      ddestruct PO5 as (z0 & z1 & z2 & q1 & q2 & q3 & q4 & q5 & q6 & q7 & z3 & z4 & z5 & z6 & j0' & j1' & j2' & bs' & m5 & -> &
                       MU5 & WM5 & MI5 & HDR5 & MG5 & SH5 & PGC5 & STH5 & STB5 & HL5 & UC5 & ST5).
      apply aevtS_now. unfold chunk_post.
      eexists. dexists mo5, nb', bl', N', tf', id. dexists z0, z1, z2, q1, q2, q3, q4, q5, q6, q7, z3, z4, z5, z6. dexists (Z.land b1n 243), pgb, j0', j1', j2', bs', m5.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HK5|]. split; [exact HJ5|].
      assert (DJ5lo : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from [(lo, SP); (CHB, CHB + 16); (AB, AB + 16); (SUB, SUB + nfix n / 8); (PGS, PGS + 1); (T + 2800, T + 3168); (UB, UB + KF)] A k).
      { intros A k H. cbn [disjoint_from]. rewrite SUBE, PGSE. subst UB CHB ASH. clear - H T0 AB0 RZSB LOIMG ASHE NFB. repeat split; lia. }
      dpose (SHAP SUB (nfix n / 8) ltac:(rewrite SUBE; clear - RZSB; lia) ltac:(rewrite SUBE; clear - RZSB NFB N2B'; lia)) as (X1 & X1' & X1'').
      dpose (SHAP PGS 1 ltac:(rewrite PGSE; clear - RZSB NFB; lia) ltac:(rewrite PGSE; clear - RZSB NFB N2B'; lia)) as (X2 & X2' & X2'').
      split.
      { eapply (depot_inv_transport _ m3 m5 N' nb' tf' bl' DI3 MU5 WM5 DJ5lo).
        - intros k Hk. pose proof (BNold k T 4096 Hk TCS ltac:(clear; lia) APTn) as Y1. pose proof (BNold k AB (needed2 n) Hk ACS ltac:(clear - NDB N2E; lia) APAn) as Y2.
          pose proof (BNsh k SUB (nfix n / 8 + 1) Hk ltac:(rewrite SUBE; clear - RZSB AB0 ASHE; try subst ASH; lia) ltac:(clear - X1' LOIMG NFB AB1' X1 RNG SUBE ASHE AB0 NDB N2E RZSB N2B'; subst ASH; lia) ltac:(clear - NFB; lia)) as Y3.
          pose proof (BNsh k PGS 1 Hk ltac:(rewrite PGSE; clear - RZSB AB0 ASHE NFB; try subst ASH; lia) ltac:(clear - NFB AB1' PGSE ASHE AB0 NDB N2E RZSB N2B'; subst ASH; lia) ltac:(clear; lia)) as Y4.
          pose proof (BN k Hk) as Y5.
          cbn [disjoint_from]. subst UB CHB. clear - Y1 Y2 Y3 Y4 Y5 LOIMG RZSB N2B' KFB NFB. repeat split; lia.
        - intros j Hj. pose proof (BSold j T 4096 Hj TCS ltac:(clear; lia) APTs) as Y1. pose proof (BSold j AB (needed2 n) Hj ACS ltac:(clear - NDB N2E; lia) APAs) as Y2.
          pose proof (BSsh j SUB (nfix n / 8 + 1) Hj ltac:(rewrite SUBE; clear - RZSB AB0 ASHE; try subst ASH; lia) ltac:(clear - X1' LOIMG NFB AB1' X1 RNG SUBE ASHE AB0 NDB N2E RZSB N2B'; subst ASH; lia) ltac:(clear - NFB; lia)) as Y3.
          pose proof (BSsh j PGS 1 Hj ltac:(rewrite PGSE; clear - RZSB AB0 ASHE NFB; try subst ASH; lia) ltac:(clear - NFB AB1' PGSE ASHE AB0 NDB N2E RZSB N2B'; subst ASH; lia) ltac:(clear; lia)) as Y4.
          pose proof (BS j Hj) as Y5.
          cbn [disjoint_from]. subst UB CHB. clear - Y1 Y2 Y3 Y4 Y5 LOIMG RZSB N2B' KFB NFB. repeat split; lia. }
      split; [split; [exact NBCS3| exact BLCS3]|].
      split; [eapply (depot_statics_transport _ m3 m5 DST3 MU5); intros A k H; apply DJ5lo; clear - H; lia|].
      split; [exact IDB|]. split; [exact NB'|]. split; [clear - TFB' SZD; lia|]. split; [clear - TFP SZD; lia|]. split; [exact CSM|].
      split; [dexists sn, sb; split; [exact Enb| split; [exact Ebl| split; [exact Fn| exact Fs]]]|].
      assert (GK : gkeep ((lo, SP) :: (A_SS, A_DEP_END) :: (T + 2800, T + 3169) :: cwin) mc m5 nb' bl').
      { intros x. cbv zeta. intros HO HBn HBs. unfold cwin in HO. cbn [outside app] in HO. ddestruct HO as (H1 & H2 & H7 & H8 & H9 & H12 & H10 & H11 & _).
        pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
        rewrite (MU5 x). 2:{ cbn [outside]. clear - H1 H8 H9 H10 H11 H7 H12. subst KF PGS SUB CHB UB AB c. repeat split; try exact I; lia. }
        rewrite (DK3 x). 2:{ subst SPA STK. clear - H1. lia. } 2:{ exact H2. } 2:{ exact HBn. } 2:{ exact HBs. }
        apply (MU2 x). cbn [outside]. subst CHB AB c SPA STK. clear - H1 H8. repeat split; try exact I; lia. }
      split; [exact GK|].
      split.
      { (* [comment removed for export] *)
        intros x HZ HO. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
        dpose GSB as (SBlo & _ & ERI & RIhi). dpose GSEP as (SEP1 & _ & SEP3).
        apply GK.
        - unfold cwin in HO |- *. cbn [outside app] in HO |- *. unfold zone in HZ. unfold A_SS, A_DEP_END in *. pose proof GT as GT'.
          ddestruct HO as (H8 & H9 & H12 & H10 & H11 & _).
          destruct HZ as [[HC HW] | [HSH | HLOW]]; (split; [| split; [| split; [| repeat split; assumption]]]).
          all: first [clear - HW LOIMG SBlo ERI RIhi SEP1 SEP3 GT' CX0 CX1 TC; lia | clear - HSH LOIMG SBlo RIhi GT'; lia | clear - HLOW LOIMG GT'; lia].
        - intros k Hk. unfold zone in HZ. destruct HZ as [[HC HW] | [HSH | HLOW]].
          + rewrite Enb in Hk |- *. destruct (dblk_app_cases nb0 sn k Hk) as [[Hk' ->]| HIn].
            * pose proof (APSn k Hk') as Y1. pose proof (APTn k Hk') as Y2. pose proof (APCn k Hk') as Y3. clear - HW Y1 Y2 Y3 SBlo ERI. lia.
            * intros HB. exact (proj1 (Forall_forall _ _) Fn _ HIn _ HC HB).
          + pose proof (BNsh k (bv_unsigned x) 1 Hk ltac:(clear - HSH SBlo; lia) ltac:(clear - HSH RIhi; lia) ltac:(clear; lia)) as Y. clear - Y. lia.
          + pose proof (BN k Hk) as Y. clear - Y HLOW. lia.
        - intros j Hj. unfold zone in HZ. destruct HZ as [[HC HW] | [HSH | HLOW]].
          + rewrite Ebl in Hj |- *. destruct (sblk_app_cases bl0 sb j Hj) as [[Hj' ->]| HIn].
            * pose proof (APSs j Hj') as Y1. pose proof (APTs j Hj') as Y2. pose proof (APCs j Hj') as Y3. clear - HW Y1 Y2 Y3 SBlo ERI. lia.
            * intros HB. exact (proj1 (Forall_forall _ _) Fs _ HIn _ HC HB).
          + pose proof (BSsh j (bv_unsigned x) 1 Hj ltac:(clear - HSH SBlo; lia) ltac:(clear - HSH RIhi; lia) ltac:(clear; lia)) as Y. clear - Y. lia.
          + pose proof (BS j Hj) as Y. clear - Y HLOW. lia. }
      split; [eapply wmono_trans; [exact WM2| eapply wmono_trans; [exact WM3| exact WM5]]|].
      split; [exact MI5|]. split; [exact ST5|].
      split; [exact HDR5|].
      split. { rewrite <- Z.land_assoc. change (Z.land 243 3) with 3. exact B1A. }
      split. { apply (land_lt_pow2 b1n 243 8); [exact B1B| clear; lia]. }
      split; [exact MG5|]. split; [exact SH5|]. split; [exact PGC5|].
      split.
      { (* [comment removed for export] *)
        intros E0. pose proof PGC5 as P5. unfold pgv in P5. rewrite (proj2 (Z.eqb_eq _ _) E0) in P5.
        assert (NS : find_segment asegs PGS 1 = None) by (apply asegs_none; [rewrite PGSE; clear - AB0 ASHE RZSB NFB; try subst ASH; lia| clear; lia]).
        rewrite (rw_C1_at asegs m5 PGS pgb P5 NS). rewrite (rw_C1_at asegs mc PGS pgb PGC NS). reflexivity. }
      split; [exact UC5|]. split; [exact STH5|]. split; [exact STB5|]. split; [exact HL5|].
      eapply rw_cells_transport; [exact UNW3| exact MU5| exact WM5|].
      cbn [disjoint_from cells_size csize Nat.add]. clear GK. subst UB CHB. clear - X1'' X2'' LOIMG T1 ABT RZSB N2B' KFB NFB. repeat split; lia.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End ChunkArm.

  (* [comment removed for export] *)
  #[using="CSmono_u CSmono_f"] Lemma CSinc0 : forall u f y, CSf None None nb0 bl0 y -> CSf u f nb0 bl0 y.
  Proof. intros [b|] [b'|] y H; [apply CSmono_u; apply CSmono_f; exact H| apply CSmono_u; exact H| apply CSmono_f; exact H| exact H]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L54961752591.3000008S1n1c2Hc". (* [comment removed for export] *)
  #[using="hAR SP T SB RI mu mfa R RB FA UA FAA PCR STK SPA FP"] Lemma cs_mod16 : cs mod 16 = 0.
  Proof.
    pose proof c_range as Hc. subst cs.
    exact (proj1 (Z.eqb_eq _ _) (zall_spec (fun y => class_size y mod 16 =? 0) (Z.to_nat 31) 1 ltac:(vm_compute; reflexivity) c ltac:(clear - Hc; lia))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="hAR SP T SB RI mu mfa R RB FA UA FAA PCR STK SPA FP"] Lemma cs_range : 32 <= cs <= 65536. Proof. exact (class_size_range c c_range). Qed.

  (* [comment removed for export] *)
  Definition hsh (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "Pa,$2.P,(;.(5.(6.+7???8000.(45.VRB,+8.))R1.)(5.R1.(6.+7???8000.(45.(6.VRB,+>0000000.)+8.))))(40.(0.&8.)Lb,(0.&8.)(41.$21.O1.R3.(12.$42.(46.R1.)(15.$42.))))")
(* [comment removed for export] *).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L3826536157.9 L39220637093.000000I00JS3hAR1n2SB2RI1c1a2Ha1H2H0S". (* [comment removed for export] *)
  #[using="hAR SP T RI mu mfa cs R FA UA FAA PCR STK SPA FP GSB"] Lemma hsh_mono : forall W m m', hsh m -> munch W m m' -> wmono asegs m m' -> hsh m'.
  Proof.
    intros W m m' H MU WM a Ha. destruct (H a Ha) as [b Hb]. clear H. eapply (byte_mono asegs W m m' a b Hb MU WM).
    apply asegs_none; [| clear; lia]. pose proof GSB. pose proof c_range. unfold RB in Ha. clear - Ha H H0. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L18933043916.8 L24890723542.10L29621006102.9 L31210597507.9 L3804884257.11 L42474671727.94L43581313045.4 L67245162224.9 00000>00H00[01201J02E02Q02gS3hAR1n2SB1c1pS1n1c2cs1pS1n2SB1c2cs2RB1p2PRS1n2SB1c2cs2RB2au1p3OFFS1n2SB1c2cs2au1p3OFF3CSRS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA1pS1n1c2cs3CSRS3hAR1n2SB2RI1c1p1H2H0". (* [comment removed for export] *)
  #[using="hAR SP T RI mu mfa R FA UA FAA PCR STK SPA FP GSB"] Lemma fchunk_transport : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PW,(3.$1;.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Pau,$2.Pp,(0.&40.)P,(89.R4.R2.R1.)P,(11.R6.R5.R4.)P,(20.$21.R6.R5.)P,PA,$2.Pk,$2.P,(5.VRB,R2.)P,(5.(6.R3.R2.)(6.VRB,R8.))(1=.R<.R4.R3.)P,PA,$2.Pk,$2.P,(5.(6.+7???8000.(45.VRB,+8.))R2.)P,(5.(6.R3.R2.)(6.+7???8000.(45.(6.VRB,R9.)+8.)))(1=.R=.R4.R3.)(89.R8.R7.R6.)")
(* [comment removed for export] *).
  Proof.
    (intros W m m' au p dd_H; ddestruct dd_H as (OFF & (bs & HB) & (sh0 & shs & HS & NZ)); intros MU WM DB DS). pose proof cs_range as CSR. pose proof cs_mod16 as CS16.
    pose proof (Z.mod_pos_bound (bv_unsigned p) (2^32) ltac:(lia)) as PR.
    split; [exact OFF|]. split.
    - exists bs. eapply rw_cells_transport; [exact HB| exact MU| exact WM| apply DB; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - CSR; lia); clear - OFF PR; lia].
    - dexists sh0, shs. split; [| exact NZ]. eapply rw_cells_transport; [exact HS| exact MU| exact WM| apply DS; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - CSR; lia)].
      + pose proof GSB. subst RB. clear - PR H. pose proof (Z.div_mod SB 4096 ltac:(lia)). lia.
      + subst RB. clear - OFF PR CSR CS16. pose proof (Z.div_mod cs 16 ltac:(lia)). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="hAR SP T RI mu mfa R FA UA FAA PCR STK SPA FP GSB"] Lemma pool_transport : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PW,(3.$1;.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Pau,$2.Pl,(3.(0.&40.))P,(69.(0.&40.)(89.R4.R2.)R1.)P,(11.R6.R5.R4.)P,(20.$21.R6.R5.)P,PA,$2.Pk,$2.P,(5.VRB,R2.)P,(5.(6.R3.R2.)(6.VRB,R8.))(1=.R<.R4.R3.)P,PA,$2.Pk,$2.P,(5.(6.+7???8000.(45.VRB,+8.))R2.)P,(5.(6.R3.R2.)(6.+7???8000.(45.(6.VRB,R9.)+8.)))(1=.R=.R4.R3.)(69.(0.&40.)(89.R8.R7.)R6.)")
(* [comment removed for export] *).
  Proof. intros W m m' au l H MU WM DB DS. eapply Forall_impl; [| exact H]. intros p Hp. eapply fchunk_transport; [exact Hp| exact MU| exact WM| exact DB| exact DS]. Qed.

  #[using="Type"] Lemma u64arr_munch : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PW,(3.$1;.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PA,$2.Pws,(3.(0.&40.))P,(5<.$21.R4.R2.R1.)P,(11.R6.R5.R4.)P,(1=.R7.R4.(3?.+8.(=.(>.(0.&40.)R3.))))(5<.$21.R6.R5.R4.)")
(* [comment removed for export] *).
  Proof.
    intros W m m' A ws [Hb Hw] MU DJ. split.
    - eapply bytes_at_transport; eauto. rewrite u64s_length, Nat2Z.inj_mul. exact DJ.
    - eapply wr_at_munch; eauto.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L18933043916.8 L24890723542.10L29621006102.9 L31210597507.9 L3804884257.11 L42474671727.93L43581313045.4 L67245162224.9 00000>00H00[01201J02E02Q02gS3hAR1n2SB1c1pS1n1c2cs1pS1n2SB1c2cs2RB1p2PRS1n2SB1c2cs2RB2au1p3OFFS1n2SB1c2cs2au1p3OFF3CSRS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA1pS1n1c2cs3CSRS3hAR1n2SB2RI1c1p1H2H0". (* [comment removed for export] *)
  #[using="hAR SP T RI mu mfa R FA UA FAA PCR STK SPA FP GSB"] Lemma fchunk_munch : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PW,(3.$1;.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Pau,$2.Pp,(0.&40.)P,(89.R4.R2.R1.)P,(11.R6.R5.R4.)P,PA,$2.Pk,$2.P,(5.VRB,R2.)P,(5.(6.R3.R2.)(6.VRB,R7.))(1=.R;.R4.R3.)P,PA,$2.Pk,$2.P,(5.(6.+7???8000.(45.VRB,+8.))R2.)P,(5.(6.R3.R2.)(6.+7???8000.(45.(6.VRB,R8.)+8.)))(1=.R<.R4.R3.)(89.R7.R6.R5.)")
(* [comment removed for export] *).
  Proof.
    (intros W m m' au p dd_H; ddestruct dd_H as (OFF & (bs & HB) & (sh0 & shs & HS & NZ)); intros MU DB DS). pose proof cs_range as CSR. pose proof cs_mod16 as CS16.
    pose proof (Z.mod_pos_bound (bv_unsigned p) (2^32) ltac:(lia)) as PR.
    split; [exact OFF|]. split.
    - exists bs. eapply rw_cells_munch; [exact HB| exact MU| apply DB; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - CSR; lia); clear - OFF PR; lia].
    - dexists sh0, shs. split; [| exact NZ]. eapply rw_cells_munch; [exact HS| exact MU| apply DS; cbn [cells_size csize Nat.add]; rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - CSR; lia)].
      + pose proof GSB. subst RB. clear - PR H. pose proof (Z.div_mod SB 4096 ltac:(lia)). lia.
      + subst RB. clear - OFF PR CSR CS16. pose proof (Z.div_mod cs 16 ltac:(lia)). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="hAR SP T RI mu mfa R FA UA FAA PCR STK SPA FP GSB"] Lemma pool_munch : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PW,(3.$1;.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))Pau,$2.Pl,(3.(0.&40.))P,(69.(0.&40.)(89.R4.R2.)R1.)P,(11.R6.R5.R4.)P,PA,$2.Pk,$2.P,(5.VRB,R2.)P,(5.(6.R3.R2.)(6.VRB,R7.))(1=.R;.R4.R3.)P,PA,$2.Pk,$2.P,(5.(6.+7???8000.(45.VRB,+8.))R2.)P,(5.(6.R3.R2.)(6.+7???8000.(45.(6.VRB,R8.)+8.)))(1=.R<.R4.R3.)(69.(0.&40.)(89.R7.R6.)R5.)")
(* [comment removed for export] *).
  Proof. intros W m m' au l H MU DB DS. eapply Forall_impl; [| exact H]. intros p Hp. eapply fchunk_munch; [exact Hp| exact MU| exact DB| exact DS]. Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "08T0@L10009363542.38 L10009363542.40 L10015668588.35 L10049798517.17 L10054450872.34 L10118203588.16 L10140493218.39 L10210605711.19 L10217539573.33 L10217539573.35 L10274126988.21 L10278559848.6  L10307921259.3  L10326949034.11 L10512070732.39 L10598670465.11 L10609050916.28 L10702588176.8  L11125573801.33 L11125573801.35 L11136423676.6  L11179226509.28 L11188449489.2  L11210639066.6  L11266334853.36 L117293985.40   L12054223420.39 L1225372328.34  L12376458638.8  L12433800977.21 L12522026373.1  L12673344616.23 L12673344745.26 L12677617336.38 L12761674836.5  L12862884641.2  L12865463121.26 L13125566298.21 L13328137276.23 L13328137405.26 L13332500204.38 L13392737556.26 L13392737685.23 L13396739909.38 L13415130216.1  L13546343634.40 L1358472242.39  L13636421100.6  L13821507617.3  L13982808854.21 L13992303238.21 L14529942053.2  L14798118929.40 L15002076226.39 L15100376903.2  L15572525375.33 L15732996402.39 L15786958986.2  L1587938449.21  L15953230509.2  L16329970322.23 L16333758530.38 L16378060235.39 L1637893174.1   L16427811904.8  L16730790281.28 L16842783084.39 L16964261176.11 L17120848823.0  L1746374919.12  L1770588981.36  L18076307788.21 L18080222632.6  L18284602179.36 L18289752719.21 L18302958969.1  L18404416940.6  L18568419057.40 L18820494961.40 L18926572867.30 L18926759668.13 L18928751437.426L18928767426.407L18933043916.12 L19045990537.21 L19131746828.21 L19135698664.6  L1925825477.3   L19305944170.39 L19344668279.21 L19545310187.2  L19545310191.3  L19704062231.39 L19723288167.7  L19764912339.9  L1994926337.40  L20009076335.35 L20011187029.38 L20011187029.40 L20348672026.21 L20604267895.35 L20610551885.38 L20610551885.40 L20703260783.35 L20709543253.38 L20709543253.40 L207740136.6    L20836822950.8  L20936524850.39 L21026692994.36 L21091747050.11 L21196358698.11 L212140044.21   L21279792490.39 L21484273060.28 L21629852572.3  L21725399676.38 L21831749564.39 L2189761147.7   L22013687057.40 L22120290505.39 L22174551818.2  L22343894949.9  L22657062026.28 L22724381928.1  L2279284007.11  L22953571684.40 L22953572370.43 L22984328200.9  L23028283098.6  L23188247429.36 L23294334865.21 L23304605630.15 L23343287261.0  L2357568477.35  L2363858663.38  L2363858663.40  L2375534541.2   L23803517183.0  L23898603878.1  L23929545039.40 L24006580716.39 L24109524442.1  L24144998104.34 L24226811473.26 L24322338809.1  L24413245228.6  L24545243113.23 L24554356127.9  L24554356248.6  L24560632610.7  L24854934790.21 L24888640626.2  L24891049031.422L24892851395.11 L24893049158.421L24896606255.11 L24897143244.12 L24897143244.3  L25153276879.4  L25315005151.26 L25379332253.38 L25379332253.40 L25381428647.35 L2542880046.34  L25538123100.39 L25847583755.26 L25864701137.6  L25977033196.8  L25982463935.8  L25984553605.13 L25984553605.9  L26013379921.6  L26095055493.36 L26116322524.38 L26396448700.39 L2647262414.5   L26606187674.28 L26848617105.21 L27181232506.43 L27181235212.40 L27466439871.3  L2750523041.40  L27600588140.39 L27697017043.3  L27706333745.19 L27848808849.2  L28042659880.34 L28156715786.40 L28156718716.43 L28540910183.21 L28762839709.0  L2880327153.30  L29109465037.38 L29109465037.40 L29115749111.35 L29435446705.26 L29452980609.8  L29677298433.1  L29718441094.4  L29757571546.6  L29879685821.33 L29879685821.35 L30108342789.36 L30130474185.11 L30233433986.39 L30338059610.6  L30339995769.1  L30378678657.11 L30435077518.7  L30437516088.6  L30573236684.7  L30604076560.8  L30663996904.1  L30892283345.6  L31194525850.21 L3148603910.21  L31525159917.17 L31533430865.6  L31640645505.11 L31769455548.39 L31782326386.4  L31897782189.9  L32058929066.11 L32061267910.21 L32652926642.39 L32758332925.13 L32896197943.40 L33110395611.6  L33154884329.28 L33227838273.3  L33337353996.21 L33349663720.6  L33399094770.8  L33467735639.40 L33606059170.39 L33698313473.11 L33767074080.40 L34169490961.21 L34301840561.4  L34301840690.33 L34301841077.37 L34357058654.38 L34445664355.36 L34458320289.21 L34706040863.33 L35125087399.35 L35131388317.38 L35131388317.40 L35233459586.38 L35233459586.40 L35239743672.35 L35393843785.7  L35730156934.21 L35847935625.40 L35847937023.43 L35867261841.22 L3597417215.0   L36075687453.0  L36191859358.7  L36193165570.2  L36242603004.1  L36406153938.2  L3646482674.8   L36565753704.6  L36569727884.21 L36571201320.0  L36670452064.28 L36819807445.26 L36948563441.40 L36981996200.34 L37252000528.39 L37695338273.40 L37725871377.21 L37806923217.21 L37906787233.40 L3812222724.33  L3812222724.35  L38235734261.1  L38446489793.11 L38475802529.40 L38630853356.13 L38630853356.9  L38637156310.8  L38700110972.1  L39160644010.11 L39188636933.0  L39220637093.0  L39332637397.0  L395858539.12   L39774454594.11 L39808216143.40 L40541032097.40 L40653650929.37 L40690307201.8  L40702779304.34 L4070786866.39  L41154907957.36 L41398109864.34 L41488597692.39 L41549943719.35 L41556242077.38 L41556242077.40 L41757127204.6  L41882435733.9  L4190050508.2   L42149244736.8  L42312019697.11 L42473080748.6  L42554935773.0  L42817616661.16 L42817616661.17 L42819977213.7  L42908497706.11 L42984359187.6  L43581313045.4  L43655446538.2  L43810840756.38 L44072740983.4  L44108320741.36 L44150440701.3  L44300882312.15 L44437059391.13 L44683283690.4  L45184660297.8  L45295076406.1  L45396721589.34 L45450153110.14 L45626123802.21 L45635383918.15 L46336287196.36 L4638274038.28  L46446536810.38 L46450547259.26 L46450547386.23 L46573847558.21 L46680981092.22 L46798637366.1  L46801378195.26 L47312073682.40 L47409641326.38 L47514216928.28 L4819779461.36  L48324997040.28 L48500666668.6  L48595508494.38 L48648739903.6  L48712615400.6  L48716536076.21 L48736336254.19 L48736336254.20 L48883743118.38 L49029283034.38 L49779527525.21 L49791865729.6  L49946329501.38 L49946329501.40 L49952636071.35 L4999168337.4   L49995285886.4  L50003475879.10 L50132325126.21 L50171351240.34 L50376799635.2  L50434248917.38 L50434248917.40 L50440547823.35 L50694634314.14 L50720667200.6  L50810147341.28 L50811079681.40 L51226421522.0  L51485564634.6  L51765344620.1  L51788915964.1  L51901902375.33 L52229988184.34 L52310674614.1  L52412439154.21 L52469894736.11 L52482632712.19 L52482632712.20 L52530306974.8  L52594603377.40 L52694741641.39 L52793108830.38 L52806941544.1  L52930216858.21 L52937896755.8  L52973276663.10 L52973276663.8  L53380004446.38 L53385470898.11 L53412032513.11 L53586826820.6  L53728160474.26 L53777391274.11 L53779857969.4  L54082232744.34 L54082473377.40 L5429770831.4   L54509494956.6  L54548870487.40 L54558294872.34 L54641519825.6  L54891896087.12 L55082185895.35 L55084272029.38 L55084272029.40 L55379812102.28 L5538628448.33  L55410835542.7  L55588686165.0  L5580650899.12  L55899845783.3  L55997489714.10 L55997509718.16 L55997509718.17 L55997509718.6  L55997509718.8  L56164433861.8  L56248205346.7  L56488697498.21 L57019285036.6  L57055401635.16 L57155905586.39 L5721498072.4   L57333628785.17 L57408811761.40 L57432918668.21 L57436486790.21 L57436804712.6  L57485903630.6  L57544720881.40 L57598913569.40 L57924165753.1  L58409901413.9  L58429566721.11 L58835949340.1  L58869690912.40 L59009349437.15 L59204339248.28 L59241684639.6  L59273826574.38 L59308696420.11 L59308696420.9  L59308845553.3  L59314955108.11 L59552029477.0  L5983160098.39  L6002171007.23  L60418839161.9  L60432055545.1  L60536527916.6  L60575329176.33 L60662235184.15 L60694006433.40 L60785358792.0  L60990546787.33 L61030858054.404L61076581038.38 L61080885374.23 L6131481214.38  L61477218587.36 L61649787821.2  L61834075013.36 L61980786136.6  L62156106983.37 L62156107616.33 L62339778138.6  L62507327512.6  L62582126956.35 L62584210518.38 L62584210518.40 L62682894286.26 L62719081734.4  L62740636161.11 L62884884705.38 L63220859395.11 L63351710914.38 L63351710914.40 L63357999608.35 L63374621462.405L63404914589.0  L63626208655.38 L63821274278.34 L63897450449.5  L64334606430.38 L64355056882.5  L64400185569.35 L64406480347.38 L64406480347.40 L6444131489.40  L64640476714.11 L64672813665.0  L65648049560.39 L6600342017.1   L6659308522.2   L66625802082.39 L6669525048.2   L6669536739.5   L6669597647.5   L6673760071.9   L66751039889.21 L66763458562.7  L66804175198.38 L67093916046.34 L67099864699.34 L67332458778.21 L67352125345.40 L6755912037.4   L67594658270.38 L67673999556.17 L67680528389.1  L67717556775.3  L67782583095.0  L67834325417.23 L6783662148.0   L6787527454.6   L6793809444.7   L68387087208.30 L6882516600.39  L701988789.36   L7332611253.11  L7419229193.28  L7515578105.15  L7515640660.9   L7657788065.28  L7673915391.0   L7716739305.26  L7794613303.40  L78595897.7     L8201234081.0   L8333054259.6   L8346817460.7   L8353115790.6   L8368274852.6   L8423093436.39  L8731824801.40  L8927212310.6   L8929693118.38  L8934309742.23  L8934309871.26  L8990428885.36  L9047092781.2   L9281665857.10  L9488195994.21  L9508785502.38  00001H02J03a04O05Y06E07H08408k09d0:D0:T0:^0;70<Q0=30>F0>T0?L0@K0@Y0A;0AB0AL0BF0C\0E60F@0FV0G>0GB0HI0IM0K:0KG0KN0L?0M50N80O80Pn0Q[0RK0Sn0T10UG0Va0W10W<0Wh0Xc0Xl0ZB0[\0[b0\k0^E0^F0^n0_30_O0`20aL0aP0a^0c10d40dI0dJ0do0f@0f`0g00gb0hJ0hM0h]0i^0j_0k30kG0mM0o90oJ10E10e11511?12[13G13O13P14n15A15]16\17m18b1:B1;81<51=L1>^1?o1@d1BD1BT1Bn1DH1E:1ES1El1FL1GK1H^1Hi1I`1K:1KP1Lf1N@1NA1N^1OV1OY1On1Pg1Q[1R51R?1S91Sa1TH1TI1U`1W81XE1XJ1XK1XN1Yk1Zn1[11[\1\41\71\G1\c1];1]I1]`1^[1^\1`b1a31c91cJ1c[1c_1ck1dX1el1g61hL1iR1jQ1kA1kT1ko1l?1l_1m31mF1n@1oV21021E22X23@24A25F25P26f27i28428i29029g2:e2<12<g2<h2=<2>P2?Z2A02AR2Aa2Ad2Am2B72C;2DF2EW2F72GM2GW2GZ2H<2HR2Hh2I62ID2IG2IZ2JP2KK2Kl2L?2La2N;2NH2Nd2O=2P82QR2R52SJ2SX2TP2TX2U82UH2Ua2W:2X=2X_2Z<2Zd2Zo2\S2^82_72`H2a>2b32cI2d]2eg2g;2hE2i[2in2ji2kc2lh2mX2mY2mZ2mm2n02n32n92nR2nb2oB2oC2oe30=31>32H33b35;35c36K37a38P39F39J39l3;B3;_3<93<M3<Q3<j3<k3<l3<m3=P3=n3?K3@a3AW3Af3C03DJ3E[3Fe3H?3IU3Ji3L33LE3LT3L]3Lk3MI3MY3MZ3NF3No3OF3O_3P03P<3P=3Q33Q?3RF3RP3S73SZ3Sg3TB3TF3UP3V43Vj3WW3XQ3YA3[;3\E3]R3^M3_G3_K3`83aN3bM3bo3ci3e<3eL3fb3g23gB3gb3hW3iI3j_3l93lY3li3n=3oG40]40i41641H42C43=43E44D45d47547Q47^48@49?49@49J49N49Q4:N4;94;=4;e4<G4=34=`4>64?74@U4AT4AW4BM4B`4C64CL4DK4D`4EB4ET4El4FE4FR4G\4I24I;4IK4Jd4KO4Kb4L=4MS4Ng4P14QD4R84RS4RT4S74S>4S]4TD4U64UH4U^4V24VM4WC4WS4X:4YT4Y`4ZU4[V4\64]14]A4]S4^T4_m4`04`?4`a4`d4bA4bi4d<4dJ4e`4f@4fZ4fc4gG4gH4hK4i84iU4iX4ih4jd4kQ4lg4lh4mO4o?50Y51552<53;53@54:54H55E56N56X56i58859H5:J5:j5;55;W5<V5=65>75?W5@h5BX5BY5CT5Db5Dn5FC5FQ5Gb5Hc5JC5KY5L25L35MI5ML5MT5Nn5O45OC5OR5Og5PO5P]5Q\5RS5Sa5TW5Um5V35WI5X65X:5XE5XF5Y=5Y>5YF5YQ5Ye5[A5\R5\k5][5^A5^\5_o5`05`]5b25bE5bF5bY5bd5bl5c?5dY5eo5f@5h:5iG5jQ5kK5kP5kl5lb5maS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MU03MF02CR2RS3FAS1A1k2H12H2S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU1A1k2H24SBlo3FASS3hAR2SP1n2lo1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR5LOIMG3SPL4RIhi3MF03FAS1A1k1H4SBlo3MU0S1n2SB2RI2mu3mfa1c2RB2FA2au3HAU3MF03FAS1A1k2H2S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FASS3hAR1n2SB2RI2mu3mfa1c2RB2FA2UA4SBlo3MU03FASS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX02TC2CR2RS3FASS3hAR1n2SB2RI2mu3mfa1c2RB2FA2UA4SBlo3MU03FASS3hAR1n2SB3mfa1c2cs2RB2FA3FAA2nf3js04LJS01f2pw3ABv4UIFfS3hAR1n2SB3mfa1c2cs2RB2FA3FAA1f2pw3fa'4rest3nf'5Lrest3ABvS1n2SB2RI1c2cs1R2RB2FA2RS2pw3ABvS1n2SB2RI1c1R2RSS3bl01j2HjS3hAR1n2SB2RI1c1R4SBlo2RSS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX04SBlo3ERI4SEP12TC4SEP33MF02CR2RS3FASS3hAR1n2lo2SB2RI1c1R5LOIMG4RIhi2RSS3hAR1n1T2SB2RI2mu3mfa1c2cs2RB2FA3PCR2T04SBlo3ERI4SEP13MF02CR3FAS1u2pw3ABv3CHI4ABloS3hAR3nb01k2X0S3hAR1n2SB2mu3mfa1c2cs2RB2FA3FAA2nf3js03HNF1u2pw3ABv3CHIS3hAR1n2SB2mu3mfa1c2cs2RB2FA3FAA1u2pw3fa'4rest3nf'4Lfa'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'2pw4LDS'3ws'3fa'3Lws2nw3ABv1w1i2HiS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2au2fa3js02ds2bs3LDS2HL3MU03MF02ws4HL303ds'2pw4LDS'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'2pw4LDS'3ws'3fa'3Lws2nw3ABv1w1i2HiS1n2SB2mu1c2RB2auS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2au2fa3js02ds2bs3LDS2HL3MU03MF02ws4HL303ds'2pw4LDS'3ws'3fa'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'4rest3nf'4Lfa'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'4rest3nf'4Lfa'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'S1n1c2cs4RZSB3NFB4N2B'4N2CSSS1n2SB2RI1c2cs2RB2pw3ABv4ABlo1A1k1HS1A1k1HS1T3CTX2SB2RI3CX01a2AR2O82O92GES1n1T3CTX2SB2RI2mu3mfa1c2RB2FA3FAS1a2HaS1n1T3CTX2SB2RI2mu3mfa1c2RB2FA2UA3MU03MF03FAS1a2HaS1T3CTX2SB2RI1a2HaS1T3CTX2SB2RI3ERI1a2HaS1n2SB2RI1c1R3ERI2CRS1n1c2cs4RZSB3NFB4N2B'4N2CSS1n2SB2RI2mu3mfa1c2cs1R2RB2FA3ERI3MF03FAS1u2pw3ABv3CHIS1n2SB2RI1c1R2RSS1n2SB2RI2mu3mfa1c2RB2FA3ERI3MUH3MF12CRS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX04SBlo3ERI4SEP12TC4SEP33MF02CR2RS3FASS2SB2RI1a2HaS1n2SB2RI2mu3mfa1c2cs2RB2FA4SBlo3MF03FAS1u2pw3ABv3CHIS3hAR3bl01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T02CR2RS3FAS1j2Y1S1n2SB2RI1c2cs1R2RB2FA2RS2pw3ABvS1n2SB2RI2mu3mfa1c2cs1R2RB2FA4SBlo3ERI3MF03FAS1u2pw3ABv3CHIS1n2SB2RI1c1R2RSS1n2mu1c2cs2pw3OFFS3hAR3nb01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T02CR2RS3FAS1k2Y1S3hAR3nb01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FAS1k2Y12Y22Y3S1TS3hAR1A1k2H12H3S3hAR1n2lo2SB2RI1c1R5LOIMG4RIhi2RSS1TS3hAR3nb01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MU03MF02CR2RS3FAS1k2Y12Y22Y3S1n2SB2RI2mu3mfa1c2RB2FA2nf3js04LJS03FASS3hAR1n1T2SB2RI2mu3mfa1c2cs2RB2FA3PCR2T04SBlo3ERI4RIhi3MF02CR3FAS1u2pw3ABv3CHI4ABloS1n1T1c3PCR2CRS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU2T04SBlo3ERI4RIhi3MF02CR4TMOD2RS3FASS1n2SB2mu1c2cs2RB2pw3OFF1y2Hy2GES1n2SB3mfa1c2RB2FA1a2Ha2GES1x2Hx2XRS1n2SB1c2RB2pw3ABv4PGSv2P11x2O51E2W5SS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX02TC2CR2RS3FASS3hAR1n2SB2RI2mu3mfa1c2RB2FA2au4SBlo3FAS1A2H1S1n2SB2RI1c2cs2RB2pw3ABv4ABloS1TS1n2SB2RI1c1R2RSS3hAR1n2SB3mfa1c2cs2RB2FA3FAA2nf3js04HNF24LJS01f2pw3ABv4UIFfS1n2SB2RI2mu3mfa1c2RB2FA2UA4SBlo3MU03FAS1i2HiS3hAR3nb01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FAS1k2Y12Y2SS3hAR1n2SB2mu1c2cs2RB2FA2UA2pw3ABv1i2HiS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2au2fa3js02ds2bs3LDS2HL3MU03MF02ws4HL303ds'2pw4LDS'3ABvS3hAR1n3CTX2SB2RI2mu3mfa1c2cs2RB2FA3CX04SBlo3CSR3FAS1u2pw3ABv4RZSB3NFB3MNF3CHI4ABlo1A1k2H1S1n2SB1c2cs2RB2pw3ABv1A1k2H3S3hAR2SP1n2lo1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR5LOIMG2au4RIhi3MF03FASS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU4SBlo3FAS3ERIS3CTXS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3ERI3MF03FASS1n1T1c3PCR2CRS3hAR1n2SB2RI2mu3mfa1c2cs2RB2FA2UA3FAS1u2pw3ABv3CHI4ABlo1i2HiS3hAR1n2SB2RI2mu3mfa1c2cs2RB2FA2UA3FAS1u2pw3ABv4RZSB3NFB3CHI4ABlo1i2Hi2O2S3hAR1T2T0S1A2sz1x2O62O72XRS3hAR2SP1n2lo1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR5LOIMG3SPL4RIhi3FAS1A1k1H4SBloS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP12CR2RS3FAS1A1k2H12H2S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU3FAS1A1k2H24SBloS1n2SB2RI1c2cs2RB2FA2pw3ABv4ABloS1T2T01i2HiS3hAR1n2lo2SB2RI1c1R5LOIMG4RIhi2RSS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au4SBlo3ERI3MF03FASS1n2SB2mu1c2cs2RB2pw3OFF1y2Hy2GES3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR3ERI3MF03FAS1A1k2H12H2S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU2T04SBlo3ERI4SEP13MF02CR2RS3FAS1A1k2H12H24RIhiS3hAR2SP1n2lo1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR5LOIMG3SPL2T12RS1A1k1H2T02CR3FASS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2au2fa3js02ds2bs3LDS2HL3MU03MF02ws4HL303ds'2pw4LDS'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". (* [comment removed for export] *)
  #[using="AL IMG ALWF ASB CSOKf KL CSf_noshadow CSmono_u CSmono_f CSmono_n CSmono_s STK SPA NB FP LOIMG SPL SPA16 TOP0 TOP1 TOP2 TIDB LOB TOPUB GSB GT GCTX GSEP GMU GMFA LEDGER_U TU_commit TU_fresh LEDGER_F TF_commit TF_fresh ROOM_U SCAR_U ROOM_F SCAR_F CSUz CSFz K_apart T_node T_store ROOM_n ROOM_s"] Theorem malloc_prim_noinit_split : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PTA,$8:.PTB,$8:.Pra,(0.&40.)Pgp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pcsw,(0.&40.)Pcstw,(0.&40.)Pstw,(0.&40.)Pj0,(0.&40.)Pj1,(0.&40.)Pj2,(0.&40.)Pj1',(0.&40.)Pj2',(0.&40.)Pj3',(0.&40.)Pe0,(0.&40.)Pexb,(0.&8.)Poomb,(0.&8.)PF,(79.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$2:.PN,$2.Ptf,$2.Pau,$2.Pnf,$2.Pcnt,$2.Pfa,(3.(0.&40.))Pjs0,(3.(0.&40.))Pds,(3.(0.&40.))Pbs,(3.(0.&40.))PshU,(3.(0.&8.))PshF,(3.(0.&8.))Ptb,(3.(0.&8.))P,(7:.$21.R>.VLO,VTOPU,(39.&40.R33.)VSP,Vd,)P,(7;.R?.VT,VCTX,)P,(1<.R10.VT,VCTX,)P,(26.R11.)P,(1>.R12.)P,(27.R13.VCTX,VT,)P,(28.R14.)P,(29.R15.VSB,)P,(25.R16.)P,(7<.$21.R17.$84.(12.$42.(56.(30.&40.$85.))(15.$42.)))P,(7<.$21.R18.$86.(12.$42.(46.(30.&8.+1.))(15.$42.)))P,(7<.$21.R19.(6.$72.+20.)(12.$42.(56.(30.&40.VSB,))(15.$42.)))P,(7<.$21.R1:.(6.$72.+30.)(12.$42.(56.(30.&40.VRI,))(15.$42.)))P,(41.$21.R1;.$22.(12.$42.(46.R1>.)(15.$42.)))P,(7<.$21.R1<.$80.(12.$42.(46.(30.&8.+1.))(15.$42.)))P,(41.$21.R1=.$23.(12.$42.(5:.R22.)(15.$42.)))P,(7<.$21.R1>.(6.VT,+8.)(12.$42.(56.(30.&40.VTOP,))(12.$42.(56.(30.&40.(47.VTOP,(7.+2.+17.))))(15.$42.))))P,(7<.$21.R1?.(6.VT,+28.)(12.$42.(46.(30.&8.=))(15.$42.)))P,(41.$21.R20.(6.VT,+<60.)(12.$42.(46.(30.&8.=))(15.$42.)))P,(7<.$21.R21.VT,(12.$42.(56.(30.&40.VCTX,))(15.$42.)))P,(7<.$21.R22.(6.VCTX,+8.)(12.$42.(5:.(30.&40.VTID,))(15.$42.)))P,(16.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,VT,+1000.)P,(16.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,VCTX,+10000.)P,(16.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,VRI,+1000.)P,(;.(5.=R20.)(5.R20.+10.))P,(19.$63.(>.(0.&40.)R1>.)#10.)P,(41.$21.R28.VPCR,(12.$42.(5:.(30.&40.R22.))(12.$42.(5:.(30.&40.(4<.Vc,)))(12.$42.(56.R36.)(15.$42.)))))P,(5;.$21.R29.(6.VPCR,+10.)R20.)P,(41.$21.R2:.(6.VT,+:>0.)(12.$42.(56.R37.)(15.$42.)))P,(41.$21.R2;.(6.VT,+:?0.)(12.$42.(56.R36.)(12.$42.(56.R35.)(12.$42.(56.R34.)(15.$42.)))))P,(5<.$21.R2<.(6.VT,+;60.)R22.)P,(19.$63.(>.(0.&40.)R23.)#20.)P,(41.$21.R2>.(6.VT,+;38.)(12.$42.(56.R36.)(12.$42.(56.R35.)(15.$42.))))P,(41.$21.R2?.(6.VT,+:>8.)(12.$42.(56.R35.)(15.$42.)))P,(;.(5.=R2<.)(5.R2<.Vmu,))P,(5.(47.Vmu,R2=.)(7.+2.+13.))P,(19.$2.(3=.R2>.+10.)=)P,(5.=R2>.)P,(5.(3?.+4.R2?.)Vmfa,)P,(5.(6.(3?.+4.(6.R30.(7.+2.+>.)))(7.+2.+12.))(7.+2.+1=.))P,(19.$2.(=.(>.(0.&40.)R2?.))R31.)P,(19.$2.(3?.+4.(6.R32.(=.(>.(0.&40.)R2?.))))Vmfa,)P,(16.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,VFA,Vmfa,)P,(16.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,VRB,Vmu,)P,(41.$21.R3:.VR,(12.$42.(56.(30.&40.=))(15.$42.)))P,(41.$21.R3;.(6.VR,+10.)(12.$42.(56.(30.&40.R36.))(15.$42.)))P,(41.$21.R3<.(6.VR,+18.)(12.$42.(56.(30.&40.Vmfa,))(15.$42.)))P,(41.$21.R3=.(6.VR,+20.)(12.$42.(56.(30.&40.R39.))(15.$42.)))P,(41.$21.R3>.(6.VR,+28.)(12.$42.(56.(30.&40.=))(15.$42.)))P,(41.$21.R3?.(6.VR,+30.)(12.$42.(56.(30.&40.Vmu,))(15.$42.)))P,(41.$21.R40.(6.VR,+38.)(12.$42.(56.(30.&40.=))(15.$42.)))P,(41.$21.R41.(6.VR,+44.)(12.$42.(46.R45.)(15.$42.)))P,(41.$21.R42.(6.VR,+48.)(12.$42.(56.R4>.)(15.$42.)))P,(41.$21.R43.(6.+7???8000.(45.VUA,+8.))(12.$42.(43.(44.+8000.)R38.)(15.$42.)))P,(41.$21.R44.(6.+7???8000.(45.VFAA,+8.))(12.$42.(43.(44.+8000.)R38.)(15.$42.)))P,(5;.$21.R45.VFA,R3>.)P,(5;.$21.R46.(6.VFA,(3?.+4.R41.))R3>.)P,(69.(0.&40.)(89.R47.R43.)(8;.(0.&40.)(44.R41.)R3>.))P,(69.(0.&40.)(89.R48.R44.)R41.)P,(41.$21.R49.(6.VRB,R45.)(12.$42.(43.(44.(47.Vmu,R45.))R3<.)(15.$42.)))P,(41.$21.R4:.(6.+7???8000.(45.(6.VRB,R46.)+8.))(12.$42.(43.(44.(45.(47.Vmu,R46.)+8.))(57.(0.&8.)(30.&8.+?:.)(44.(45.(47.Vmu,R46.)+8.))))(15.$42.)))P,(8<.R4;.)P,(1?.VhAR,R4<.R4:.Vnb0,R49.Vbl0,)P,(68.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,Vnb0,Vbl0,)P,(5.(6.R4;.+80.)(7.+2.+20.))P,(5.(6.R4=.+2.)(47.(7.+2.+1?.)(7.+2.+1<.)))P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vnb0,))))(8.(5.(6.VT,+1000.)(?.Vnb0,R2.))(5.(6.(?.Vnb0,R2.)(7.+2.+14.))VT,))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vbl0,))))(8.(5.(6.VT,+1000.)(10.Vbl0,R2.))(5.(6.(10.Vbl0,R2.)(7.+2.+17.))VT,))P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vnb0,))))(8.(5.(6.VCTX,+10000.)(?.Vnb0,R2.))(5.(6.(?.Vnb0,R2.)(7.+2.+14.))VCTX,))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vbl0,))))(8.(5.(6.VCTX,+10000.)(10.Vbl0,R2.))(5.(6.(10.Vbl0,R2.)(7.+2.+17.))VCTX,))P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vnb0,))))(8.(5.(6.VRI,+1000.)(?.Vnb0,R2.))(5.(6.(?.Vnb0,R2.)(7.+2.+14.))VSB,))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vbl0,))))(8.(5.(6.VRI,+1000.)(10.Vbl0,R2.))(5.(6.(10.Vbl0,R2.)(7.+2.+17.))VSB,))P,(55.$21.R56.VSP,VTOP,)P,(16.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,VSP,(47.VTOP,VSP,))P,(55.$21.R58.Vlo,VSP,)P,(16.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,Vlo,(47.VSP,Vlo,))P,(54.$21.R5:.)P,A5.VK,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,R5:.P,(53.R5<.R5;.)P,Pu,(1.$2<.)Pf,(1.$2<.)A4.VGn,R2.R1.Vnb0,Vbl0,P,Pu,(1.$2<.)Pf,(1.$2<.)A4.VGs,R2.R1.Vnb0,Vbl0,P,Pu,(1.$2<.)Pf,(1.$2<.)Px,$2.A4.VGs,R3.R2.(18.$2.Vnb0,(12.$2.R1.(15.$2.)))Vbl0,P,(19.$2.R5:.=)P,(<.R5<.(45.(4<.Vc,)+2.))P,(<.Vmu,(6.R5>.(3?.Vcs,(47.(45.(4<.Vc,)+2.)R5=.))))P,(5.(6.Vmu,(7.+2.+12.))+>0000000.)P,A1.R90.(15.$8=.)P,A1.R90.(15.$8=.)P,Pcf,$49.P,(8>.R91.R90.R8<.R8;.R83.R82.R81.R80.R7?.R7>.R7=.R7<.R7;.R7:.R69.R68.R65.R64.R63.R62.R61.R6;.R75.R72.R71.R70.R60.R5?.R5>.R5=.R5<.R5;.R6:.R6<.(12.(13.$2.$2.)(14.$2.$2.VPCR,(6.VPCR,+4.))(12.(13.$2.$2.)(14.$2.$2.(6.VPCR,+10.)(6.(6.VPCR,+10.)+40.))(15.(13.$2.$2.))))L,P,(0.&40.)(1.(0.&8.))$8?.R67.R1.)(90.$21.R2.R94.)P,Pcf,$49.P,(91.R92.R91.R8=.R8<.R84.R83.R82.R81.R80.R7?.R7>.R7=.R7<.R7;.R6:.R69.R66.R65.R64.R63.R62.R6<.R76.R73.R72.R71.R61.R60.R5?.R5>.R5=.R5<.R6;.R6=.(12.(13.$2.$2.)(14.$2.$2.VPCR,(6.VPCR,+4.))(12.(13.$2.$2.)(14.$2.$2.(6.VPCR,+10.)(6.(6.VPCR,+10.)+40.))(15.(13.$2.$2.))))L,P,(0.&40.)(1.(0.&8.))$8?.R68.R1.)(90.$21.R2.R94.)(90.$21.(4=.(4>.(4?.R92.(30.&40.VSP,)R91.(30.&40.$50.)R90.R8?.R8>.R8=.R8<.(30.&40.Vn,)R8;.R8:.R89.R88.R87.R86.R85.R84.R83.R82.R81.R80.R7?.R7>.R7=.R7<.R7;.R7:.R79.R78.R77.)R6:.(30.&40.$7?.)R69.(2;.(0.&40.))R68.(52.$21.))R67.)(92.R94.R93.))")
(* [comment removed for export] *).
  Proof.
    intros TA TB ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 csw cstw stw j0 j1 j2 j1' j2' j3' e0 exb oomb F fc m mo
      N tf au nf cnt fa js0 ds bs shU shF tb
      UWC MS8 AS PS FS TS MWS PPS DST GOTFL PPART SBC RIC OOM MRN ERR THR TSW UNW TH TIDC TCS CTXCS RICS
      HCNT LDS PC ARR STC STH STB HL TJ SJ
      HAU HINV AUAL HNF HNF2 HNF3 LFA LJS0 CSFA CSRB MX NF MFA AU M40 MUC M56 EX STW SHU SHF HFAR HJS
      POOLC POOLF TAIL TAILSH HSH DI DCS TFMAX NB2 APTn APTs APCn APCs APSn APSs
      STT STCS ST SCS MI HK HJ GN GS GSX CNT00 GMISS NEEDU UOK A0n B0n HNUL HCHK.
    facts. dpose GT as (T0 & T1 & TAL). pose proof GCTX as (CX0 & CX1). dpose GSB as (SBlo & SBAL & ERI & RIhi). dpose GSEP as (SEP1 & TC & SEP3).
    dpose GMU as (MU0 & MUAL & MUH). dpose GMFA as (MF0 & MFAL & MF1).
    pose proof c_range as CR. pose proof needed2_prim as [N2E NDB]. pose proof cs_range as CSR. pose proof cs_mod16 as CS16.
    assert (SPH : SP <= 2^62) by (clear - TOP1 TOP2; lia). assert (RBE : RB = SB + c * 2^32) by reflexivity. assert (FAE : FA = RB + 0xE0000000) by reflexivity.
    assert (UAE : UA = RB + mu) by reflexivity. assert (FAAE : FAA = FA + mfa) by reflexivity. assert (PCRE : PCR = T + 208 + 80 * c) by reflexivity. assert (RE : R = RI + 128 * c) by reflexivity.
    pose proof (Z.mod_pos_bound (mu - au) 8 ltac:(clear; lia)) as TMOD. pose proof (Z.div_mod (mu - au) 8 ltac:(clear; lia)) as TDIV.
    (* [comment removed for export] *)
    eapply (evtA_srzJ_KJ AL (CSf None None nb0 bl0) (K None None nb0 bl0) _ _ _ mo (KL None None nb0 bl0) HK); [exact HJ| |].
    { eapply (mseg_head (CSf None None nb0 bl0) (CSOKf None None nb0 bl0));
        first [sassumption | cassumption | exact UWC| exact MS8| exact AS| exact THR| exact TSW| exact UNW| exact TCS| exact CTXCS| exact STT| exact STCS| exact ST| exact SCS| exact MI]. }
    cbn beta. intros ms1 mo1 PO HK1 MM1 HJ1. unfold head_post in PO.
    ddestruct PO as (tq0 & tq1 & tq2 & y14 & y15 & y16 & y17 & tq3 & tq4 & tq5 & tq6 & m1 & ws & size & fr0 & fr1 & fr2 & -> &
                    MU1 & WM1 & MI1 & FR7 & STKC & HTR & HL30 & SZB & SZD & F1800 & TFBP & F8 & FR16 & UNW1 & AFR & ST1 & SR1).
    assert (DJ1 : forall A k, A + k <= lo -> (A + k <= T + 3168 \/ T + 3169 <= A) -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k)
      by (intros A k H1 H2; cbn [disjoint_from]; clear - H1 H2; lia).
    assert (LOW1 : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k) by (intros A k H; apply DJ1; clear - H LOIMG T0; lia).
    (* [comment removed for export] *)
    assert (SLAB1 : forall A k, SB <= A -> A + k <= RI + 4096 -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k)
      by (intros A k H1 H2; apply DJ1; clear - H1 H2 LOIMG RIhi ERI SEP1; lia).
    assert (SHD1 : forall A k, 0x7fff8000 <= A -> A + k <= 0x10007fff8000 -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k)
      by (intros A k H1 H2; apply DJ1; clear - H1 H2 LOIMG T0; lia).
    assert (TLO1 : forall A k, T <= A -> A + k <= T + 3168 -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k)
      by (intros A k H1 H2; apply DJ1; clear - H1 H2 LOIMG T1; lia).
    Ltac t1 H MU WM DJ tac := eapply rw_cells_transport; [exact H| exact MU| exact WM| apply DJ; cbn [cells_size csize Nat.add length map]; tac].
    assert (PC1 : rw_cells asegs m1 PCR [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 (max_count c)); C8 csw]) by (t1 PC MU1 WM1 TLO1 ltac:(clear - CR PCRE; lia)).
    assert (ARR1 : u32arr asegs m1 (PCR + 16) ds) by (eapply u32arr_transport; [exact ARR| exact MU1| exact WM1| apply TLO1; rewrite ?LDS; clear - CR PCRE; lia]).
    assert (STC1 : rw_cells asegs m1 (T + 2784) [C8 cstw]) by (t1 STC MU1 WM1 TLO1 ltac:(clear; lia)).
    assert (STH1 : rw_cells asegs m1 (T + 2800) [C8 j0; C8 j1; C8 j2]) by (t1 STH MU1 WM1 TLO1 ltac:(clear; lia)).
    assert (STB1 : u64arr asegs m1 (T + 2912) bs) by (eapply u64arr_transport; [exact STB| exact MU1| exact WM1| apply TLO1; rewrite ?HL; clear; lia]).
    assert (TJ1 : rw_cells asegs m1 (T + 2872) [C8 j1'; C8 j2']) by (t1 TJ MU1 WM1 TLO1 ltac:(clear; lia)).
    assert (SJ1 : rw_cells asegs m1 (T + 2792) [C8 j3']) by (t1 SJ MU1 WM1 TLO1 ltac:(clear; lia)).
    assert (RS : SB <= R /\ R + 128 <= RI + 4096) by (clear - CR ERI RE; lia).
    assert (MX1 : rw_cells asegs m1 R [C8 (Z_to_bv 64 0)]) by (t1 MX MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (NF1 : rw_cells asegs m1 (R + 16) [C8 (Z_to_bv 64 nf)]) by (t1 NF MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (MFA1 : rw_cells asegs m1 (R + 24) [C8 (Z_to_bv 64 mfa)]) by (t1 MFA MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (AU1 : rw_cells asegs m1 (R + 32) [C8 (Z_to_bv 64 au)]) by (t1 AU MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (M401 : rw_cells asegs m1 (R + 40) [C8 (Z_to_bv 64 0)]) by (t1 M40 MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (MUC1 : rw_cells asegs m1 (R + 48) [C8 (Z_to_bv 64 mu)]) by (t1 MUC MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (M561 : rw_cells asegs m1 (R + 56) [C8 (Z_to_bv 64 0)]) by (t1 M56 MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (EX1 : rw_cells asegs m1 (R + 68) [C1 exb]) by (t1 EX MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (STW1 : rw_cells asegs m1 (R + 72) [C8 stw]) by (t1 STW MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (FAS : SB <= RB /\ FA + mfa + 2^18 <= RI /\ RB + mu <= FA) by (clear - CR ERI MU0 MUH MF0 MF1 RBE FAE; lia).
    assert (SHU1 : rw_cells asegs m1 (0x7fff8000 + UA / 8) [CB (Z.to_nat 32768) shU]).
    { t1 SHU MU1 WM1 SHD1 ltac:(clear - FAS SBlo RIhi MU0 MF0 UAE; lia). }
    assert (SHF1 : rw_cells asegs m1 (0x7fff8000 + FAA / 8) [CB (Z.to_nat 32768) shF]).
    { t1 SHF MU1 WM1 SHD1 ltac:(clear - FAS SBlo RIhi MU0 MF0 FAAE FAE; lia). }
    assert (HFAR1 : u32arr asegs m1 FA fa) by (eapply u32arr_transport; [exact HFAR| exact MU1| exact WM1| apply SLAB1; rewrite ?LFA; clear - FAS HNF HNF2 MF0 MU0; lia]).
    assert (HJS1 : u32arr asegs m1 (FA + 4 * nf) js0) by (eapply u32arr_transport; [exact HJS| exact MU1| exact WM1| apply SLAB1; clear - FAS HNF LJS0 MF0 MU0; lia]).
    assert (PS1 : poison_statics m1) by (eapply (poison_statics_transport _ m m1 PS MU1); intros A k H; apply LOW1; clear - H; lia).
    assert (TS1 : thr_statics m1 CTX T).
    { eapply (thr_statics_transport _ m m1 CTX T TS MU1); [apply LOW1; unfold A_TSD_INITED; clear; lia| apply LOW1; unfold A_TSD_PTR; clear; lia| apply LOW1; unfold A_TSD_ARR; clear; lia|].
      apply DJ1; clear - CX1 LOIMG TC; lia. }
    assert (MWS1 : mwc_statics m1) by (eapply (mwc_statics_transport _ m m1 MWS MU1); intros A k H; apply LOW1; clear - H; lia).
    assert (PPS1 : pop_statics m1 SB) by (eapply (pop_statics_transport _ m m1 SB PPS MU1); intros A k H; apply LOW1; clear - H; lia).
    assert (RIC1 : ro_cells asegs m1 (A_INSTANCE + 48) [C8 (Z_to_bv 64 RI)]) by (eapply ro_cells_transport; [exact RIC| exact MU1| apply LOW1; unfold A_INSTANCE; cbn; clear; lia]).
    assert (POOLC1 : Forall (fchunk m1 au) (firstn (Z.to_nat cnt) ds)).
    { eapply pool_transport; [exact POOLC| exact MU1| exact WM1| intros A k H1 H2; apply SLAB1; clear - H1 H2 FAS HAU MF0 MU0; lia| intros A k H1 H2; apply SHD1; clear - H1 H2 FAS HAU SBlo RIhi ERI CR RBE MF0 MU0; lia]. }
    assert (POOLF1 : Forall (fchunk m1 au) fa).
    { eapply pool_transport; [exact POOLF| exact MU1| exact WM1| intros A k H1 H2; apply SLAB1; clear - H1 H2 FAS HAU MF0 MU0; lia| intros A k H1 H2; apply SHD1; clear - H1 H2 FAS HAU SBlo RIhi ERI CR RBE MF0 MU0; lia]. }
    assert (TAIL1 : rw_cells asegs m1 (RB + au) [CB (Z.to_nat (mu - au)) tb]) by (t1 TAIL MU1 WM1 SLAB1 ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - HAU; lia); clear - FAS HAU MF0 MU0; lia)).
    assert (TAILSH1 : rw_cells asegs m1 (0x7fff8000 + (RB + au) / 8) [CB (Z.to_nat ((mu - au) / 8)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((mu - au) / 8)))]).
    { t1 TAILSH MU1 WM1 SHD1 ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - HAU TMOD TDIV; lia); clear - FAS HAU SBlo RIhi ERI CR TMOD TDIV RBE MF0 MU0; lia). }
    pose proof (hsh_mono _ m m1 HSH MU1 WM1) as HSH1.
    assert (OOM1 : rw_cells asegs m1 A_OOM_CELL [C1 oomb]) by (t1 OOM MU1 WM1 LOW1 ltac:(unfold A_OOM_CELL; clear; lia)).
    assert (MRN1 : ro_cells asegs m1 A_MRN_CELL [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact MRN| exact MU1| apply LOW1; unfold A_MRN_CELL; cbn; clear; lia]).
    assert (ERR1 : rw_cells asegs m1 A_ERRNO [C4 e0]) by (t1 ERR MU1 WM1 LOW1 ltac:(unfold A_ERRNO; clear; lia)).
    dpose (proj1 (proj2 (proj2 DI))) as (_ & DMF & _).
    dpose (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DI)))))))) as (_ & DBF & _).
    assert (DI1 : depot_inv m1 N nb0 tf bl0).
    { eapply (depot_inv_transport _ m m1 N nb0 tf bl0 DI MU1 WM1 LOW1).
      - intros k Hk. pose proof (APTn k Hk) as Y.
        dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb0) DMF (Z.to_nat k) 0 ltac:(clear - Hk; lia)) as (_ & X & _).
        unfold dblk in *. apply DJ1; clear - X Y LOIMG; lia.
      - intros j Hj. pose proof (APTs j Hj) as Y.
        dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl0) DBF (Z.to_nat j) 0 ltac:(clear - Hj; lia)) as (_ & X & _).
        unfold sblk in *. apply DJ1; clear - X Y LOIMG; lia. }
    assert (DST1 : depot_statics m1) by (eapply (depot_statics_transport _ m m1 DST MU1); intros A k H; apply LOW1; clear - H; lia).
    assert (AS1 : allocA_statics m1 T CTX).
    { eapply (allocA_statics_transport _ m m1 T CTX AS MU1); [intros A k H; apply LOW1; exact H| apply DJ1; clear - CX1 LOIMG TC; lia]. }
    assert (FS1 : fin_statics m1) by (eapply (fin_statics_transport _ m m1 FS MU1); intros A k H; apply LOW1; exact H).
    assert (GOTFL1 : ro_cells asegs m1 A_GOT_FLAGS [C8 (Z_to_bv 64 A_FLAGS)]) by (eapply ro_cells_transport; [exact GOTFL| exact MU1| apply LOW1; unfold A_GOT_FLAGS; cbn; clear; lia]).
    assert (PPART1 : ro_cells asegs m1 A_FL_PPART [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact PPART| exact MU1| apply LOW1; unfold A_FL_PPART; cbn; clear; lia]).
    assert (TH1 : ro_cells asegs m1 T [C8 (Z_to_bv 64 CTX)]) by (eapply ro_cells_transport; [exact TH| exact MU1| apply TLO1; cbn; clear; lia]).
    assert (TIDC1 : ro_cells asegs m1 (CTX + 8) [C4 (Z_to_bv 64 TID)]) by (eapply ro_cells_transport; [exact TIDC| exact MU1| apply DJ1; cbn; clear - CX1 LOIMG TC; lia]).
    clear PC ARR STC STH STB TJ SJ MX NF MFA AU M40 MUC M56 EX STW SHU SHF HFAR HJS PS TS MWS PPS RIC POOLC POOLF TAIL TAILSH HSH OOM MRN ERR DST AS FS GOTFL PPART TH TIDC MS8 THR TSW UNW STT.
    (* [comment removed for export] *)
    assert (CST' : forall u f, crange (CSf u f nb0 bl0) T 4096) by (intros u f y Hy; apply CSinc0; apply TCS; exact Hy).
    assert (CSCTX' : forall u f, crange (CSf u f nb0 bl0) CTX 0x10000) by (intros u f y Hy; apply CSinc0; apply CTXCS; exact Hy).
    assert (CSRI' : forall u f, crange (CSf u f nb0 bl0) RI 4096) by (intros u f y Hy; apply CSinc0; apply RICS; exact Hy).
    assert (SPAAL2 : (SPA + -128) mod 16 = 0).
    { subst SPA STK. clear - SPA16. apply Z.mod_divide in SPA16; [| lia]. apply Z.mod_divide; [lia|]. destruct SPA16 as [q Hq]. exists (q - 142). lia. }
    eapply (combined_split_noinit AL IMG ALWF (fun u f => CSf u f nb0 bl0) (fun u f => CSOKf u f nb0 bl0) CSmono_u CSmono_f ASB T CTX SB RI c GSB c_range GT GCTX GSEP
              CST' CSCTX' CSRI' (fun u f => K u f nb0 bl0) (fun u f => KL u f nb0 bl0) mu mfa LEDGER_U TU_commit TU_fresh LEDGER_F TF_commit TF_fresh GMU GMFA CSUz CSFz ROOM_U SCAR_U ROOM_F SCAR_F TA TB)
      with (lo := lo) (x := needed2 n) (au := au) (nf := nf) (cnt := cnt) (fa := fa) (js0 := js0) (ds := ds) (shU := shU) (shF := shF) (exb := exb) (csw := csw) (cstw := cstw) (stw := stw) (j1 := j1') (j2 := j2') (j3 := j3').
    all: lazymatch goal with
         | |- forall ok c', _ => idtac
         | |- 1 <= needed2 n <= 0x10000 => clear - N2E NDB; lia
         | |- class_of _ = c => reflexivity
         | |- rw_cells _ _ (T + 208 + 80 * c) _ => exact PC1
         | |- u32arr _ _ (T + 208 + 80 * c + 16) _ => exact ARR1
         | |- rw_cells _ _ (T + 2784) _ => exact STC1
         | |- rw_cells _ _ (RI + 128 * c) _ => exact MX1
         | |- rw_cells _ _ (RI + 128 * c + 16) _ => exact NF1
         | |- rw_cells _ _ (RI + 128 * c + 24) _ => exact MFA1
         | |- rw_cells _ _ (RI + 128 * c + 32) _ => exact AU1
         | |- rw_cells _ _ (RI + 128 * c + 40) _ => exact M401
         | |- rw_cells _ _ (RI + 128 * c + 48) _ => exact MUC1
         | |- rw_cells _ _ (RI + 128 * c + 56) _ => exact M561
         | |- rw_cells _ _ (RI + 128 * c + 68) _ => exact EX1
         | |- rw_cells _ _ (RI + 128 * c + 72) _ => exact STW1
         | |- rw_cells _ _ (T + 2872) _ => exact TJ1
         | |- rw_cells _ _ (T + 2792) _ => exact SJ1
         | |- rw_cells _ _ (0x7fff8000 + (SB + c * 2^32 + mu) / 8) _ => exact SHU1
         | |- rw_cells _ _ (0x7fff8000 + (SB + c * 2^32 + 0xE0000000 + mfa) / 8) _ => exact SHF1
         | |- u32arr _ _ (SB + c * 2^32 + 0xE0000000) _ => exact HFAR1
         | |- u32arr _ _ (SB + c * 2^32 + 0xE0000000 + 4 * _) _ => exact HJS1
         | |- poison_statics _ => exact PS1
         | |- thr_statics _ _ _ => exact TS1
         | |- mwc_statics _ => exact MWS1
         | |- pop_statics _ _ => exact PPS1
         | |- ro_cells _ _ (A_INSTANCE + 48) _ => exact RIC1
         | |- stk _ _ _ _ => exact ST1
         | |- crange _ (SB + c * 2^32 + 0xE0000000) _ => exact CSFA
         | |- crange _ lo _ => eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear; lia| subst SPA STK; clear; lia]
         | |- mem_inv _ _ => exact MI1
         | |- K _ _ _ _ _ => exact HK1
         | |- J _ _ => cbn [ms_mem MS MSsvc] in HJ1; exact HJ1
         | |- _ = Z_to_bv 64 A_TP => reflexivity
         | |- (SPA + -128) mod 16 = 0 => exact SPAAL2
         | |- _ => first [sassumption | cassumption | exact CNT00| exact GMISS| exact NEEDU| exact UOK| assumption| exact HAU| exact HINV| exact AUAL| exact HNF| exact HNF2| exact HNF3| exact LFA| exact LJS0| exact LDS| exact HCNT| exact LOIMG
                         | (subst SPA STK; clear - SPL; lia) | (subst SPA STK; clear - SPH; lia) ]
         end.
    all: lazymatch goal with |- forall ok c', _ => idtac | |- ?G => fail "combined premise" G end.
    (* [comment removed for export] *)
    intros ok cf PO. unfold comb_cpostS in PO.
    ddestruct PO as (ms2 & mo2 & AB & u & f & v0 & v1 & v2 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & mm & k1 & k2 & k3 & stw' & cstw' & -> & -> &
                    MU2 & WM2 & MI2 & ST2 & HK2 & HJ2 & MUB2 & PS2 & TS2 & MWS2 & PPS2 & RIC2 & MX2 & MFA2 & M402 & MUC2 & M562 & STW2 & STC2 & TJ2 & SJ2 & USH & USHn & FSH & FSHn & _ & ARM).
    replace (ret_pc (Z_to_bv 64 0x47d34)) with (Z_to_bv 64 0x47d34) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    (* [comment removed for export] *)
    assert (DJ2 : forall A k, SPA + -128 <= A -> disjoint_from
              ((lo, SPA + -128) :: (UA, UA + 2^18) :: (0x7fff8000 + UA / 8, 0x7fff8000 + UA / 8 + 32768) :: (FA, FAA + 2^18) :: (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)
               :: (T + 2872, T + 2888) :: (T + 2792, T + 2800) :: (T + 2784, T + 2792) :: (R, R + 8) :: (R + 16, R + 24) :: (R + 24, R + 32) :: (R + 32, R + 40) :: (R + 48, R + 56)
               :: (R + 68, R + 69) :: (R + 72, R + 80) :: [(PCR, PCR + 4); (PCR + 16, PCR + 16 + 64)]) A k).
    { intros A k H. cbn [disjoint_from app]. subst SPA STK. clear - H FAS RS RIhi LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    assert (LOW2 : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from
              ((lo, SPA + -128) :: (UA, UA + 2^18) :: (0x7fff8000 + UA / 8, 0x7fff8000 + UA / 8 + 32768) :: (FA, FAA + 2^18) :: (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)
               :: (T + 2872, T + 2888) :: (T + 2792, T + 2800) :: (T + 2784, T + 2792) :: (R, R + 8) :: (R + 16, R + 24) :: (R + 24, R + 32) :: (R + 32, R + 40) :: (R + 48, R + 56)
               :: (R + 68, R + 69) :: (R + 72, R + 80) :: [(PCR, PCR + 4); (PCR + 16, PCR + 16 + 64)]) A k).
    { intros A k H. cbn [disjoint_from app]. subst SPA STK. clear - H FAS RS RIhi LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    Ltac t2 H MU DJ tac := eapply rw_cells_munch; [exact H| exact MU| apply DJ; cbn [cells_size csize Nat.add length map]; tac].
    assert (AFR2 : allocA_frame mm SPA fr0 1 (Z_to_bv 64 0x47a64) (Z_to_bv 64 SP) (Z_to_bv 64 n) (Z_to_bv 64 A_PC_MALLOC) (Z_to_bv 64 1) (Z_to_bv 64 STK) (Z_to_bv 64 (SP + -81)) s6 s7 s8 s9 s10 s11).
    { unfold allocA_frame in *. t2 AFR MU2 DJ2 ltac:(subst SPA STK; clear; lia). }
    assert (FR162 : rw_cells asegs mm (STK + -16) [C8 (Z_to_bv 64 SP); C8 (Z_to_bv 64 0x6978c)]) by (t2 FR16 MU2 DJ2 ltac:(subst SPA STK; clear; lia)).
    assert (FR72 : rw_cells asegs mm (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (t2 FR7 MU2 DJ2 ltac:(subst SPA STK; clear; lia)).
    assert (STKC2 : rw_cells asegs mm STK [C8 (Z_to_bv 64 (STK + 16)); C8 (Z_to_bv 64 size)]) by (t2 STKC MU2 DJ2 ltac:(subst SPA STK; clear; lia)).
    assert (HTR2 : u64arr asegs mm (STK + 16) ws) by (eapply u64arr_munch; [exact HTR| exact MU2| apply DJ2; subst SPA STK; clear; lia]).
    assert (F18002 : rw_cells asegs mm (STK + 256) [CB 1800 fr1]) by (t2 F1800 MU2 DJ2 ltac:(subst SPA STK; clear; lia)).
    assert (TFBP2 : rw_cells asegs mm (STK + 2056) [C8 (Z_to_bv 64 SP)]) by (t2 TFBP MU2 DJ2 ltac:(subst SPA STK; clear; lia)).
    assert (F82 : rw_cells asegs mm (STK + 2064) [CB 8 fr2]) by (t2 F8 MU2 DJ2 ltac:(subst SPA STK; clear; lia)).
    assert (UNW2 : rw_cells asegs mm (T + 3168) [C1 (Z_to_bv 8 0)]).
    { eapply rw_cells_munch; [exact UNW1| exact MU2|]. cbn [disjoint_from app cells_size csize Nat.add]. subst SPA STK. clear - FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    assert (OOM2 : rw_cells asegs mm A_OOM_CELL [C1 oomb]) by (t2 OOM1 MU2 LOW2 ltac:(unfold A_OOM_CELL; clear; lia)).
    assert (MRN2 : ro_cells asegs mm A_MRN_CELL [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact MRN1| exact MU2| apply LOW2; unfold A_MRN_CELL; cbn; clear; lia]).
    assert (ERR2 : rw_cells asegs mm A_ERRNO [C4 e0]) by (t2 ERR1 MU2 LOW2 ltac:(unfold A_ERRNO; clear; lia)).
    assert (DST2 : depot_statics mm) by (eapply (depot_statics_transport _ m1 mm DST1 MU2); intros A k H; apply LOW2; clear - H; lia).
    assert (SCSc : crange (CSf u f nb0 bl0) lo (SP - lo)) by (intros y Hy; apply CSinc0; apply SCS; exact Hy).
    assert (DJT2 : forall A k, T + 2800 <= A -> A + k <= T + 2872 \/ (T + 2888 <= A /\ A + k <= T + 3168) -> disjoint_from
              ((lo, SPA + -128) :: (UA, UA + 2^18) :: (0x7fff8000 + UA / 8, 0x7fff8000 + UA / 8 + 32768) :: (FA, FAA + 2^18) :: (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)
               :: (T + 2872, T + 2888) :: (T + 2792, T + 2800) :: (T + 2784, T + 2792) :: (R, R + 8) :: (R + 16, R + 24) :: (R + 24, R + 32) :: (R + 32, R + 40) :: (R + 48, R + 56)
               :: (R + 68, R + 69) :: (R + 72, R + 80) :: [(PCR, PCR + 4); (PCR + 16, PCR + 16 + 64)]) A k).
    { intros A k H1 H2. cbn [disjoint_from app]. subst SPA STK. clear - H1 H2 FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    assert (STH2 : rw_cells asegs mm (T + 2800) [C8 j0; C8 j1; C8 j2]) by (eapply rw_cells_munch; [exact STH1| exact MU2| apply DJT2; cbn; clear; lia]).
    assert (STB2 : u64arr asegs mm (T + 2912) bs) by (eapply u64arr_munch; [exact STB1| exact MU2| apply DJT2; rewrite ?HL; clear; lia]).
    assert (BNS0 : forall k, 0 <= k < Z.of_nat (length nb0) -> dblk nb0 k + 2^20 <= 0x7fff8000 \/ 0x10007fff8000 <= dblk nb0 k).
    { intros k Hk. destruct DCS as [D1 _]. pose proof (D1 k Hk) as CRk.
      destruct (Z_le_gt_dec (dblk nb0 k + 2^20) 0x7fff8000) as [H1|H1]; [left; exact H1| right].
      destruct (Z_le_gt_dec 0x10007fff8000 (dblk nb0 k)) as [H2|H2]; [exact H2| exfalso].
      destruct (Z_lt_ge_dec (dblk nb0 k) 0x7fff8000) as [H3|H3].
      - apply (CSf_noshadow None None nb0 bl0 0x7fff8000); [apply CRk; clear - H1 H3; lia| clear; lia].
      - apply (CSf_noshadow None None nb0 bl0 (dblk nb0 k)); [apply CRk; clear; lia| clear - H2 H3; lia]. }
    assert (BSS0 : forall j, 0 <= j < Z.of_nat (length bl0) -> sblk bl0 j + 2^23 <= 0x7fff8000 \/ 0x10007fff8000 <= sblk bl0 j).
    { intros j Hj. destruct DCS as [_ D2]. pose proof (D2 j Hj) as CRj.
      destruct (Z_le_gt_dec (sblk bl0 j + 2^23) 0x7fff8000) as [H1|H1]; [left; exact H1| right].
      destruct (Z_le_gt_dec 0x10007fff8000 (sblk bl0 j)) as [H2|H2]; [exact H2| exfalso].
      destruct (Z_lt_ge_dec (sblk bl0 j) 0x7fff8000) as [H3|H3].
      - apply (CSf_noshadow None None nb0 bl0 0x7fff8000); [apply CRj; clear - H1 H3; lia| clear; lia].
      - apply (CSf_noshadow None None nb0 bl0 (sblk bl0 j)); [apply CRj; clear; lia| clear - H2 H3; lia]. }
    assert (DI2 : depot_inv mm N nb0 tf bl0).
    { eapply (depot_inv_transport _ m1 mm N nb0 tf bl0 DI1 MU2 WM2 LOW2).
      - intros k Hk. pose proof (APTn k Hk) as Y1. pose proof (APSn k Hk) as Y2. pose proof (BNS0 k Hk) as Y3.
        dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb0) DMF (Z.to_nat k) 0 ltac:(clear - Hk; lia)) as (_ & X & _).
        unfold dblk in *. cbn [disjoint_from app]. subst SPA STK. clear - X Y1 Y2 Y3 FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia.
      - intros j Hj. pose proof (APTs j Hj) as Y1. pose proof (APSs j Hj) as Y2. pose proof (BSS0 j Hj) as Y3.
        dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl0) DBF (Z.to_nat j) 0 ltac:(clear - Hj; lia)) as (_ & X & _).
        unfold sblk in *. cbn [disjoint_from app]. subst SPA STK. clear - X Y1 Y2 Y3 FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    destruct ok; cbv beta iota.
    2:{ (* [comment removed for export] *)
      ddestruct ARM as (EAB & Fn & CNT0 & PC2 & NF2 & AU2 & EX2 & HFAR2 & HJS2 & ARR2). subst AB.
      eapply (evtA_srzJ_KJ AL (CSf u f nb0 bl0) (K u f nb0 bl0) _ _ _ mo2 (KL u f nb0 bl0) HK2); [exact HJ2| |].
      { eapply (mseg_null (CSf u f nb0 bl0) (CSOKf u f nb0 bl0)) with (m0 := mm) (W := []);
          first [exact AFR2| exact OOM2| exact MRN2| exact ERR2| exact FR162| exact FR72| exact STKC2| exact HTR2| exact HL30| exact F18002| exact TFBP2| exact F82| exact ST2| exact SCSc
                | apply munch_refl| apply wmono_refl| exact MI2]. }
      cbn beta. (intros ms3 mo3 dd_H; ddestruct dd_H as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m3 & -> & MU3 & WM3 & MI3 & OOM3 & ERR3 & ST3); intros HK3 MM3 HJ3).
      apply HNUL. unfold mgen_postN.
      eexists. dexists mo3, 0, u, f, nb0, bl0. dexists y0, y1, y2, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6. dexists stw', cstw', k1, k2, k3, m3.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HK3|]. split; [exact HJ3|]. split; [exact MUB2|].
      split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3))|]. split; [exact MI3|]. split; [exact ST3|].
      split; [intros y Hy; apply CSinc0; exact Hy|].
      assert (OE : oe_ok [(lo, SP); (A_OOM_CELL, A_OOM_CELL + 1); (A_ERRNO, A_ERRNO + 4)]).
      { intros A k H1 H2 H3. cbn [disjoint_from]. clear - H1 H2 H3 LOIMG. repeat split; lia. }
      assert (DJ3 : forall A k, (A + k <= 0x10000 \/ 0x65f000 <= A) -> A + k <= lo -> disjoint_from [(lo, SP); (A_OOM_CELL, A_OOM_CELL + 1); (A_ERRNO, A_ERRNO + 4)] A k).   (* [comment removed for export] *)
      { intros A k H1 H2. unfold A_OOM_CELL, A_ERRNO. cbn [disjoint_from]. clear - H1 H2. repeat split; lia. }
      destruct (statics5_transport_oe _ mm m3 CTX T SB MU3 OE ltac:(apply DJ3; clear - CX0 CX1 LOIMG; lia)) as (D1 & D2 & D3 & D4 & D5).
      split; [exact (D1 DST2)|]. split; [exact (D2 PS2)|]. split; [exact (D3 TS2)|]. split; [exact (D4 MWS2)|]. split; [exact (D5 PPS2)|].
      Ltac t3 H MU WM DJ tac := eapply rw_cells_transport; [exact H| exact MU| exact WM| apply DJ; cbn [cells_size csize Nat.add length map]; tac].
      split; [t3 MX2 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|].
      split; [t3 MFA2 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|]. split; [t3 M402 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|].
      split; [t3 MUC2 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|]. split; [t3 M562 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|].
      split; [t3 STW2 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|]. split; [t3 STC2 MU3 WM3 DJ3 ltac:(clear - T0 T1 LOIMG; lia)|].
      split; [t3 TJ2 MU3 WM3 DJ3 ltac:(clear - T0 T1 LOIMG; lia)|]. split; [t3 SJ2 MU3 WM3 DJ3 ltac:(clear - T0 T1 LOIMG; lia)|].
      split; [intros Hf; t3 (FSH Hf) MU3 WM3 DJ3 ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia); clear - FAS SBlo RIhi LOIMG MU0 MF0 FAAE FAE RBE; lia)|].
      split; [intros Hf; t3 (FSHn Hf) MU3 WM3 DJ3 ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia); clear - FAS SBlo RIhi LOIMG MU0 MF0 FAAE FAE RBE; lia)|].
      split; [intros Hu HMU; t3 (USHn Hu HMU) MU3 WM3 DJ3 ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia); clear - FAS SBlo RIhi LOIMG MU0 MF0 UAE RBE; lia)|].
      split; [t3 UNW2 MU3 WM3 DJ3 ltac:(clear - T0 T1 LOIMG; lia)|].
      split; [exact I|].
      split; [reflexivity|]. split; [exact Fn|]. split; [exact CNT0|]. split; [reflexivity|]. split; [reflexivity|].
      split.
      { (* [comment removed for export] *)
        intros x. cbv zeta. intros HO _ _. unfold mgen_windows in HO. cbn [outside app] in HO.
        ddestruct HO as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15 & O16 & O17 & O18 & O19 & O20 & O21 & O22 & _).
        rewrite (MU3 x) by (cbn [outside]; repeat split; first [exact O1| exact O19| exact O20| exact I]).
        rewrite (MU2 x). 2:{ cbn [outside app]. subst SPA STK.
                             repeat split; first [sassumption | cassumption | exact O8| exact O9| exact O10| exact O11| exact O7| exact O5| exact O4| exact O12| exact O13| exact O14| exact O15| exact O16| exact O17| exact O18| exact O21| exact O22| exact I | (clear - O1; lia)]. }
        apply (MU1 x). cbn [outside]. repeat split; first [exact O1| exact O3| exact I]. }
      split. { (* [comment removed for export] *)
        eapply (depot_inv_transport_z _ mm m3 N nb0 tf bl0 DI2 MU3 WM3).
        - intros A k H. unfold A_SS, A_DEP_END, A_OOM_CELL, A_ERRNO in *. cbn [disjoint_from]. clear - H LOIMG. repeat split; lia.
        - intros k Hk. dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb0) DMF (Z.to_nat k) 0 ltac:(clear - Hk; lia)) as (X0 & X & _).
          unfold dblk, A_OOM_CELL, A_ERRNO in *. cbn [disjoint_from]. clear - X0 X LOIMG. repeat split; lia.
        - intros j Hj. dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl0) DBF (Z.to_nat j) 0 ltac:(clear - Hj; lia)) as (X0 & X & _).
          unfold sblk, A_OOM_CELL, A_ERRNO in *. cbn [disjoint_from]. clear - X0 X LOIMG. repeat split; lia. }
      split; [t3 PC2 MU3 WM3 DJ3 ltac:(clear - T0 T1 LOIMG CR PCRE; lia)|].
      split; [eapply u32arr_transport; [exact ARR2| exact MU3| exact WM3| apply DJ3; rewrite ?LDS; clear - T0 T1 LOIMG CR PCRE; lia]|].
      split; [t3 NF2 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|]. split; [t3 AU2 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|]. split; [t3 EX2 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|].
      split; [eapply u32arr_transport; [exact HFAR2| exact MU3| exact WM3| apply DJ3; rewrite ?LFA; clear - FAS SBlo RIhi LOIMG MU0 MF0 HNF HNF2 FAE RBE; lia]|].
      split; [eapply u32arr_transport; [exact HJS2| exact MU3| exact WM3| apply DJ3; clear - FAS SBlo RIhi LOIMG MU0 MF0 HNF LJS0 FAE RBE; lia]|].
      split. { intros Hu. destruct (USH Hu) as [Z1 Z2]. split.
               - t3 Z1 MU3 WM3 DJ3 ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia); clear - FAS SBlo RIhi LOIMG MU0 MF0 UAE RBE; lia).
               - t3 Z2 MU3 WM3 DJ3 ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia); clear - FAS SBlo RIhi LOIMG MU0 MF0 UAE RBE; lia). }
      split; [exact OOM3|]. split; [exact ERR3|].
      split.
      - eapply rw_cells_transport; [exact STH2| exact MU3| exact WM3| apply DJ3; cbn; clear - T0 T1 LOIMG; lia].
      - eapply u64arr_transport; [exact STB2| exact MU3| exact WM3| apply DJ3; rewrite ?HL; clear - T0 T1 LOIMG; lia].
    }
    (* [comment removed for export] *)
    ddestruct ARM as (cnt' & ds' & pw & EAB & HC' & NTH & LDS' & PC2 & ARR2 & CASES). subst AB.
    (* [comment removed for export] *)
    assert (DJP2 : forall A k, RB <= A -> A + k <= RB + au -> disjoint_from
              ((lo, SPA + -128) :: (UA, UA + 2^18) :: (0x7fff8000 + UA / 8, 0x7fff8000 + UA / 8 + 32768) :: (FA, FAA + 2^18) :: (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)
               :: (T + 2872, T + 2888) :: (T + 2792, T + 2800) :: (T + 2784, T + 2792) :: (R, R + 8) :: (R + 16, R + 24) :: (R + 24, R + 32) :: (R + 32, R + 40) :: (R + 48, R + 56)
               :: (R + 68, R + 69) :: (R + 72, R + 80) :: [(PCR, PCR + 4); (PCR + 16, PCR + 16 + 64)]) A k).
    { intros A k H1 H2. cbn [disjoint_from app]. subst SPA STK. clear - H1 H2 HAU FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    assert (DJPS2 : forall A k, 0x7fff8000 + RB / 8 <= A -> A + k <= 0x7fff8000 + (RB + au) / 8 -> disjoint_from
              ((lo, SPA + -128) :: (UA, UA + 2^18) :: (0x7fff8000 + UA / 8, 0x7fff8000 + UA / 8 + 32768) :: (FA, FAA + 2^18) :: (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)
               :: (T + 2872, T + 2888) :: (T + 2792, T + 2800) :: (T + 2784, T + 2792) :: (R, R + 8) :: (R + 16, R + 24) :: (R + 24, R + 32) :: (R + 32, R + 40) :: (R + 48, R + 56)
               :: (R + 68, R + 69) :: (R + 72, R + 80) :: [(PCR, PCR + 4); (PCR + 16, PCR + 16 + 64)]) A k).
    { intros A k H1 H2. cbn [disjoint_from app]. subst SPA STK. clear - H1 H2 HAU FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    pose proof (pool_munch _ m1 mm au _ POOLC1 MU2 DJP2 DJPS2) as POOLC2. pose proof (pool_munch _ m1 mm au _ POOLF1 MU2 DJP2 DJPS2) as POOLF2.
    assert (TAIL2 : rw_cells asegs mm (RB + au) [CB (Z.to_nat (mu - au)) tb]).
    { eapply rw_cells_munch; [exact TAIL1| exact MU2|]. cbn [disjoint_from app cells_size csize Nat.add]. rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - HAU; lia). subst SPA STK.
      clear - HAU FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    assert (TAILSH2 : rw_cells asegs mm (0x7fff8000 + (RB + au) / 8) [CB (Z.to_nat ((mu - au) / 8)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((mu - au) / 8)))]).
    { eapply rw_cells_munch; [exact TAILSH1| exact MU2|]. cbn [disjoint_from app cells_size csize Nat.add]. rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - HAU TMOD TDIV; lia). subst SPA STK.
      clear - HAU FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE TMOD TDIV. repeat split; lia. }
    pose proof (max_cached_fits c c_range) as [MCF1 MCF2].
    set (ABv := RB + 16 * (bv_unsigned pw mod 2^32)) in *.
    pose proof (Z.mod_pos_bound (bv_unsigned pw) (2^32) ltac:(clear; lia)) as PWR.
    (* [comment removed for export] *)
    assert (CHUNK : 16 * (bv_unsigned pw mod 2^32) + cs <= mu + unit_if u
                    /\ (exists cbs, rw_cells asegs mm ABv [CB (Z.to_nat cs) cbs])
                    /\ (exists sh0 shs, rw_cells asegs mm (0x7fff8000 + ABv / 8) [C1 sh0; CB (Z.to_nat (cs / 8 - 1)) shs] /\ bv_unsigned sh0 <> 0)).
    { destruct CASES as [(Ecnt & Eds & Eu & Ef & _) | (CNT0 & Ecnt & Un & Fn & new & ws' & fa' & rest & nf' & au' & ex' & Eds & Efa & Lws & Lfa' & SRC & _)].
      - (* [comment removed for export] *)
        subst cnt' ds'.
        assert (IN : In pw (firstn (Z.to_nat cnt) ds)) by (eapply In_firstn_of_nth; [exact NTH| clear - HC'; lia]).
        destruct (proj1 (Forall_forall _ _) POOLC2 pw IN) as (OFF & HB & HS).
        split; [destruct u as [[|]|]; cbn [unit_if]; clear - OFF HAU; lia|]. split; [exact HB| exact HS].
      - (* [comment removed for export] *)
        subst cnt'. ddestruct (cpy_last (Z.to_nat (max_count c / 2)) ws' ds Lws ltac:(clear - MCF2; lia)) as (w & NW & NC).
        rewrite <- Eds in NC. replace (Z.to_nat (max_count c / 2) - 1)%nat with (Z.to_nat (max_count c / 2 - 1)) in NC by (clear - MCF2; lia).
        rewrite NTH in NC. injection NC as Epw.
        assert (EOFF : bv_unsigned pw mod 2^32 = bv_unsigned w mod 2^32) by (rewrite Epw; apply sx32_mod32).
        assert (INW : In w (fa ++ new)) by (rewrite Efa; apply in_or_app; right; eapply nth_error_In; exact NW).
        apply in_app_or in INW. destruct INW as [INF | INN].
        + destruct (proj1 (Forall_forall _ _) POOLF2 w INF) as (OFF & HB & HS). subst ABv. rewrite EOFF in *.
          split; [destruct u as [[|]|]; cbn [unit_if]; clear - OFF HAU; lia|]. split; [exact HB| exact HS].
        + destruct SRC as [(Enew & _) | (Enew & NFK & KNW & Eau' & Eex' & Un')].
          { exfalso. rewrite Enew in INN. exact INN. }
          rewrite Enew in INN. destruct (In_carve_list _ _ _ _ INN) as (i & Hi & Ew).
          destruct u as [[|]|]; [| exfalso; exact (Un eq_refl)|]; cbn [unit_if] in Hi, KNW |- *; fold cs in Hi, KNW, Ew, Eau' |- *.
          { (* [comment removed for export] *)
          set (nw := (mu + 2^18 - au) / cs) in *.
          assert (NWB : 0 <= nw /\ nw * cs <= mu + 2^18 - au).
          { subst nw. pose proof (Z.div_pos (mu + 2^18 - au) cs ltac:(clear - HAU; lia) ltac:(clear - CSR; lia)). pose proof (Z.mul_div_le (mu + 2^18 - au) cs ltac:(clear - CSR; lia)). clear - H H0. lia. }
          assert (OFFE : 16 * (bv_unsigned pw mod 2^32) = au + Z.of_nat i * cs).
          { rewrite EOFF, Ew. pose proof (Z.div_mod au 16 ltac:(lia)) as DA. rewrite AUAL, Z.add_0_r in DA. pose proof (Z.div_mod cs 16 ltac:(lia)) as DC. rewrite CS16, Z.add_0_r in DC.
            assert (E16 : (au + Z.of_nat i * cs) / 16 = au / 16 + Z.of_nat i * (cs / 16)).
            { rewrite DA at 1. rewrite DC at 1. replace (16 * (au / 16) + Z.of_nat i * (16 * (cs / 16))) with ((au / 16 + Z.of_nat i * (cs / 16)) * 16) by (clear; lia). rewrite Z.div_mul by (clear; lia). reflexivity. }
            rewrite E16. assert (BND : 0 <= au / 16 + Z.of_nat i * (cs / 16) < 2^32) by (clear - DA DC Hi NWB HAU MUH CSR; nia).
            rewrite unsigned_lit by (clear - BND; lia). rewrite Z.mod_small by exact BND. clear - DA DC; lia. }
          assert (CHB2 : Z.of_nat i * cs + cs <= nw * cs) by (clear - Hi NWB CSR; nia).
          split; [rewrite OFFE; clear - CHB2 NWB; lia|].
          destruct (USH eq_refl) as [UZ USHz].
          assert (BIG : rw_cells asegs mm (RB + au) [CB (Z.to_nat (mu - au) + Z.to_nat (2^18))%nat (tb ++ repeat (Z_to_bv 8 0) (Z.to_nat (2^18)))]).
          { apply CB_merge; [exact TAIL2|]. rewrite Z2Nat.id by (clear - HAU; lia). replace (RB + au + (mu - au)) with UA by (cbv delta [UA] in *; clear; lia). exact UZ. }
          assert (BIGSH : rw_cells asegs mm (0x7fff8000 + (RB + au) / 8) [CB (Z.to_nat ((mu - au) / 8) + Z.to_nat 32768)%nat (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((mu - au) / 8) + Z.to_nat 32768)%nat)]).
          { rewrite (List.repeat_app (Z_to_bv 8 0xfa)). apply CB_merge; [exact TAILSH2|]. rewrite Z2Nat.id by (clear - HAU TMOD TDIV; lia).
            replace (0x7fff8000 + (RB + au) / 8 + (mu - au) / 8) with (0x7fff8000 + UA / 8); [exact USHz|].
            cbv delta [UA] in *. pose proof (Z.div_mod RB 4096 ltac:(lia)) as DR. rewrite RBE in DR at 1.
            clear - AUAL MUAL HAU RBE SBAL. pose proof (Z.div_mod au 16 ltac:(lia)). pose proof (Z.div_mod mu 4096 ltac:(lia)). pose proof (Z.div_mod SB 4096 ltac:(lia)). nia. }
          split.
          * exists (firstn (Z.to_nat cs) (skipn (Z.to_nat (Z.of_nat i * cs)) (tb ++ repeat (Z_to_bv 8 0) (Z.to_nat (2^18))))).
            replace ABv with (RB + au + Z.of_nat (Z.to_nat (Z.of_nat i * cs))) by (subst ABv; rewrite Z2Nat.id by (clear - CSR; nia); clear - OFFE; lia).
            apply (CB_sub asegs mm _ _ _ _ _ BIG). clear - CHB2 NWB HAU CSR; nia.
          * dexists (Z_to_bv 8 0xfa), (repeat (Z_to_bv 8 0xfa) (Z.to_nat (cs / 8 - 1))). split; [| clear; vm_compute; intros E; discriminate E].
            lazymatch type of BIGSH with rw_cells _ _ _ [CB ?nE25 _] => assert (HOKE25 : (Z.to_nat (Z.of_nat i * cs / 8) + Z.to_nat (cs / 8) <= nE25)%nat) by (clear - CHB2 NWB HAU CSR CS16 TMOD TDIV; nia) end. (* [comment removed for export] *)
            pose proof (CB_sub asegs mm _ _ _ (Z.to_nat (Z.of_nat i * cs / 8)) (Z.to_nat (cs / 8)) BIGSH HOKE25) as SUBSH.
            rewrite firstn_skipn_repeat in SUBSH by exact HOKE25. clear HOKE25.
            replace (0x7fff8000 + (RB + au) / 8 + Z.of_nat (Z.to_nat (Z.of_nat i * cs / 8))) with (0x7fff8000 + ABv / 8) in SUBSH.
            2:{ subst ABv. rewrite OFFE. rewrite Z2Nat.id by (apply Z.div_pos; clear - CSR; nia).
                clear - AUAL RBE SBAL CS16. pose proof (Z.div_mod au 16 ltac:(lia)). pose proof (Z.div_mod cs 16 ltac:(lia)). pose proof (Z.div_mod SB 4096 ltac:(lia)). nia. }
            eapply rw_cells_reshape; [exact SUBSH| cbn; rewrite repeat_length; split; [exact I| split; [reflexivity| exact I]] |].
            cbn [cells_bytes cbytes app]. rewrite !app_nil_r. replace (Z.to_nat (cs / 8)) with (S (Z.to_nat (cs / 8 - 1))) by (clear - CSR; lia). reflexivity.
          }
          { (* [comment removed for export] *)
          rewrite Z.add_0_r in Hi, KNW |- *. set (nw := (mu - au) / cs) in *.
          assert (NWB : 0 <= nw /\ nw * cs <= mu - au).
          { subst nw. pose proof (Z.div_pos (mu - au) cs ltac:(clear - HAU; lia) ltac:(clear - CSR; lia)). pose proof (Z.mul_div_le (mu - au) cs ltac:(clear - CSR; lia)). clear - H H0. lia. }
          assert (OFFE : 16 * (bv_unsigned pw mod 2^32) = au + Z.of_nat i * cs).
          { rewrite EOFF, Ew. pose proof (Z.div_mod au 16 ltac:(lia)) as DA. rewrite AUAL, Z.add_0_r in DA. pose proof (Z.div_mod cs 16 ltac:(lia)) as DC. rewrite CS16, Z.add_0_r in DC.
            assert (E16 : (au + Z.of_nat i * cs) / 16 = au / 16 + Z.of_nat i * (cs / 16)).
            { rewrite DA at 1. rewrite DC at 1. replace (16 * (au / 16) + Z.of_nat i * (16 * (cs / 16))) with ((au / 16 + Z.of_nat i * (cs / 16)) * 16) by (clear; lia). rewrite Z.div_mul by (clear; lia). reflexivity. }
            rewrite E16. assert (BND : 0 <= au / 16 + Z.of_nat i * (cs / 16) < 2^32) by (clear - DA DC Hi NWB HAU MUH CSR; nia).
            rewrite unsigned_lit by (clear - BND; lia). rewrite Z.mod_small by exact BND. clear - DA DC; lia. }
          assert (CHB2 : Z.of_nat i * cs + cs <= nw * cs) by (clear - Hi NWB CSR; nia).
          split; [rewrite OFFE; clear - CHB2 NWB; lia|].
          pose proof TAIL2 as BIG. pose proof TAILSH2 as BIGSH.
          split.
          * exists (firstn (Z.to_nat cs) (skipn (Z.to_nat (Z.of_nat i * cs)) tb)).
            replace ABv with (RB + au + Z.of_nat (Z.to_nat (Z.of_nat i * cs))) by (subst ABv; rewrite Z2Nat.id by (clear - CSR; nia); clear - OFFE; lia).
            apply (CB_sub asegs mm _ _ _ _ _ BIG). clear - CHB2 NWB HAU CSR; nia.
          * dexists (Z_to_bv 8 0xfa), (repeat (Z_to_bv 8 0xfa) (Z.to_nat (cs / 8 - 1))). split; [| clear; vm_compute; intros E; discriminate E].
            lazymatch type of BIGSH with rw_cells _ _ _ [CB ?nE25 _] => assert (HOKE25 : (Z.to_nat (Z.of_nat i * cs / 8) + Z.to_nat (cs / 8) <= nE25)%nat) by (clear - CHB2 NWB HAU CSR CS16 TMOD TDIV; nia) end. (* [comment removed for export] *)
            pose proof (CB_sub asegs mm _ _ _ (Z.to_nat (Z.of_nat i * cs / 8)) (Z.to_nat (cs / 8)) BIGSH HOKE25) as SUBSH.
            rewrite firstn_skipn_repeat in SUBSH by exact HOKE25. clear HOKE25.
            replace (0x7fff8000 + (RB + au) / 8 + Z.of_nat (Z.to_nat (Z.of_nat i * cs / 8))) with (0x7fff8000 + ABv / 8) in SUBSH.
            2:{ subst ABv. rewrite OFFE. rewrite Z2Nat.id by (apply Z.div_pos; clear - CSR; nia).
                clear - AUAL RBE SBAL CS16. pose proof (Z.div_mod au 16 ltac:(lia)). pose proof (Z.div_mod cs 16 ltac:(lia)). pose proof (Z.div_mod SB 4096 ltac:(lia)). nia. }
            eapply rw_cells_reshape; [exact SUBSH| cbn; rewrite repeat_length; split; [exact I| split; [reflexivity| exact I]] |].
            cbn [cells_bytes cbytes app]. rewrite !app_nil_r. replace (Z.to_nat (cs / 8)) with (S (Z.to_nat (cs / 8 - 1))) by (clear - CSR; lia). reflexivity.
          } }
    ddestruct CHUNK as (OFF & (cbs & CBS) & (sh0 & shs & CSH & NZ)).
    pose proof (rz_size_bound n) as RZSB. pose proof (rz_size_cases n) as RC.
    assert (NFB : 1 <= nfix n <= Z.max n 1) by (unfold nfix; clear - NB; lia).
    assert (N2B' : nfix n + rz_size n <= needed2 n).
    { rewrite N2E. unfold needed, rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). clear - H H0 NB NFB. lia. }
    assert (N2CS : needed2 n <= cs) by (pose proof (class_fitsL (needed2 n) ltac:(clear - N2E NDB; lia)) as CF; exact CF).
    pose proof (Z.div_mod (nfix n) 8 ltac:(clear; lia)) as DNF. pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(clear; lia)) as MNF.
    assert (ABv8 : ABv mod 16 = 0).
    { subst ABv. pose proof (Z.div_mod SB 4096 ltac:(lia)) as DS.
      replace (RB + 16 * (bv_unsigned pw mod 2^32)) with ((SB / 4096 * 256 + c * 2^28 + bv_unsigned pw mod 2^32) * 16) by (rewrite RBE; clear - DS SBAL; lia). apply Z_mod_mult. }
    pose proof (Z.div_mod ABv 16 ltac:(clear; lia)) as DAB. rewrite ABv8, Z.add_0_r in DAB.
    pose proof (Z.div_mod cs 16 ltac:(clear; lia)) as DCS16. rewrite CS16, Z.add_0_r in DCS16.
    (* [comment removed for export] *)
    pose proof (CB_sub asegs mm ABv (Z.to_nat cs) cbs (Z.to_nat (rz_size n - 16)) 16 CBS ltac:(clear - RZSB N2B' N2CS NFB; lia)) as HDRc.
    rewrite Z2Nat.id in HDRc by (clear - RZSB; lia). destruct (CB16_hdr asegs mm _ _ HDRc) as (b0 & b1 & w2 & w4 & w8 & HDR2). clear HDRc.
    pose proof (CB_sub asegs mm ABv (Z.to_nat cs) cbs 0 16 CBS ltac:(clear - CSR; lia)) as MGc. rewrite Z.add_0_r in MGc.
    destruct (CB16_words asegs mm _ _ MGc) as (mg0 & mg1 & MG2). clear MGc.
    pose proof (CB_sub asegs mm ABv (Z.to_nat cs) cbs (Z.to_nat (rz_size n)) (Z.to_nat (Z.min (nfix n) 4096)) CBS ltac:(clear - RZSB N2B' N2CS NFB; lia)) as UC2.
    rewrite Z2Nat.id in UC2 by (clear - RZSB; lia).
    pose proof CSH as CSH'. change [C1 sh0; CB (Z.to_nat (cs / 8 - 1)) shs] with ([C1 sh0] ++ [CB (Z.to_nat (cs / 8 - 1)) shs]) in CSH'.
    apply rw_cells_app in CSH' as [SHC2 SHT]. cbn [cells_size csize Nat.add] in SHT.
    pose proof (CB_sub asegs mm _ _ shs (Z.to_nat (rz_size n / 8 - 1)) (Z.to_nat (nfix n / 8)) SHT ltac:(clear - RZSB RC N2B' N2CS NFB DNF MNF DCS16 CSR; lia)) as SH2.
    replace (0x7fff8000 + ABv / 8 + Z.of_nat 1 + Z.of_nat (Z.to_nat (rz_size n / 8 - 1))) with (0x7fff8000 + (ABv + rz_size n) / 8) in SH2
      by (rewrite Z2Nat.id by (clear - RC; lia); clear - RC DAB; lia).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (hsh_mono _ _ _ HSH1 MU2 WM2) as HSH2.
    (* [comment removed for export] *)
    assert (PGC2 : exists pgb, rw_cells asegs mm (0x7fff8000 + Z.shiftr (ABv + rz_size n + nfix n / 8 * 8) 3) [C1 pgb]).
    { rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
      destruct (Z_lt_ge_dec (rz_size n / 8 + nfix n / 8) (cs / 8)) as [LT|GE].
      - pose proof (CB_sub asegs mm _ _ shs (Z.to_nat (rz_size n / 8 + nfix n / 8 - 1)) 1 SHT ltac:(clear - LT RZSB RC NFB DNF MNF DCS16 CSR; lia)) as B1.
        rewrite Z2Nat.id in B1 by (clear - RC NFB DNF MNF; lia).
        replace (0x7fff8000 + ABv / 8 + Z.of_nat 1 + (rz_size n / 8 + nfix n / 8 - 1)) with (0x7fff8000 + (ABv + rz_size n + nfix n / 8 * 8) / 8) in B1 by (clear - RC DAB DNF MNF; lia).
        destruct (CB1_byte asegs mm _ _ B1) as [b Hb]. exists b. exact Hb.
      - apply HSH2. subst ABv. clear - GE OFF RC DAB DNF MNF DCS16 CSR RBE FAS MU0 MUH MUB2 HAU N2B' N2CS SBAL PWR. pose proof (Z.div_mod SB 4096 ltac:(lia)).
        assert (unit_if u <= 2^18) by (destruct u as [[|]|]; cbn; lia). split; nia. }
    destruct PGC2 as [pgb PGC2].
    replace (ABv + (rz_size n - 16)) with (ABv + rz_size n + -16) in HDR2 by (clear; lia).
    assert (UIF : 0 <= unit_if u <= 2^18) by (destruct u as [[|]|]; cbn; clear; lia). assert (UIFf : 0 <= unit_if f <= 2^18) by (destruct f as [[|]|]; cbn; clear; lia).
    assert (AB1c : ABv + needed2 n <= SB + c * 2^32 + 0xE0000000) by (clear - OFF N2CS MUH MUB2 UIF RBE; try subst ABv; lia).
    assert (ACScs : crange (CSf u f nb0 bl0) ABv cs).
    { intros y Hy. destruct (Z_lt_ge_dec y (RB + mu)) as [LT|GE].
      - apply CSinc0. apply CSRB. subst ABv. clear - Hy LT PWR. lia.
      - destruct u as [[|]|]; cbn [unit_if] in OFF; [| exfalso; clear - Hy GE OFF; try subst ABv; lia | exfalso; clear - Hy GE OFF; try subst ABv; lia].
        apply (CSUz f). subst ABv. cbv delta [UA] in *. clear - Hy GE OFF. lia. }
    assert (ACSc : crange (CSf u f nb0 bl0) ABv (needed2 n)) by (eapply crange_sub; [exact ACScs| clear; lia| clear - N2CS; lia]).
    assert (DCSc : depot_cs (CSf u f nb0 bl0) nb0 bl0).
    { destruct DCS as [D1 D2]. split; [intros k Hk y Hy; apply CSinc0; exact (D1 k Hk y Hy)| intros j Hj y Hy; apply CSinc0; exact (D2 j Hj y Hy)]. }
    assert (AS2 : allocA_statics mm T CTX).
    { eapply (allocA_statics_transport _ m1 mm T CTX AS1 MU2); [intros A k H; apply LOW2; exact H|]. cbn [disjoint_from app cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. subst SPA STK.
      clear - FAS RS RIhi ERI SEP1 SEP3 TC LOIMG SPL T0 T1 CX0 CX1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    assert (FS2 : fin_statics mm) by (eapply (fin_statics_transport _ m1 mm FS1 MU2); intros A k H; apply LOW2; exact H).
    assert (GOTFL2 : ro_cells asegs mm A_GOT_FLAGS [C8 (Z_to_bv 64 A_FLAGS)]) by (eapply ro_cells_transport; [exact GOTFL1| exact MU2| apply LOW2; unfold A_GOT_FLAGS; cbn; clear; lia]).
    assert (PPART2 : ro_cells asegs mm A_FL_PPART [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact PPART1| exact MU2| apply LOW2; unfold A_FL_PPART; cbn; clear; lia]).
    assert (DJTT2 : forall A k, T <= A -> A + k <= T + 208 -> disjoint_from
              ((lo, SPA + -128) :: (UA, UA + 2^18) :: (0x7fff8000 + UA / 8, 0x7fff8000 + UA / 8 + 32768) :: (FA, FAA + 2^18) :: (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)
               :: (T + 2872, T + 2888) :: (T + 2792, T + 2800) :: (T + 2784, T + 2792) :: (R, R + 8) :: (R + 16, R + 24) :: (R + 24, R + 32) :: (R + 32, R + 40) :: (R + 48, R + 56)
               :: (R + 68, R + 69) :: (R + 72, R + 80) :: [(PCR, PCR + 4); (PCR + 16, PCR + 16 + 64)]) A k).
    { intros A k H1 H2. cbn [disjoint_from app]. subst SPA STK. clear - H1 H2 FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    assert (TH2 : ro_cells asegs mm T [C8 (Z_to_bv 64 CTX)]) by (eapply ro_cells_transport; [exact TH1| exact MU2| apply DJTT2; cbn; clear; lia]).
    assert (TIDC2 : ro_cells asegs mm (CTX + 8) [C4 (Z_to_bv 64 TID)]).
    { eapply ro_cells_transport; [exact TIDC1| exact MU2|]. cbn [disjoint_from app cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. subst SPA STK.
      clear - FAS RS RIhi ERI SEP1 SEP3 TC LOIMG SPL T0 T1 CX0 CX1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    (* [comment removed for export] *)
    eapply (srzJ_of_aevtS asegs); [| exact B0n |].
    { eapply (mseg_chunk u f pw) with (mg0 := mg0) (mg1 := mg1) (b0 := b0) (b1 := b1) (w2 := w2) (w4 := w4) (w8 := w8) (shb := sh0) (pgb := pgb) (sj := _) (uj := _)
                                     (j0 := j0) (j1 := j1) (j2 := j2) (bs := bs) (N := N) (tf := tf) (size := size) (ws := ws) (fr0 := fr0) (fr1 := fr1) (fr2 := fr2).
      all: lazymatch goal with
           | |- _ + needed2 n <= _ => exact AB1c
           | |- crange _ T 4096 => exact (CST' u f)
           | |- crange _ CTX 0x10000 => exact (CSCTX' u f)
           | |- crange _ lo _ => exact SCSc
           | |- crange _ _ (needed2 n) => exact ACSc
           | |- allocA_statics _ _ _ => exact AS2
           | |- poison_statics _ => exact PS2
           | |- fin_statics _ => exact FS2
           | |- depot_statics _ => exact DST2
           | |- ro_cells _ _ A_GOT_FLAGS _ => exact GOTFL2
           | |- ro_cells _ _ A_FL_PPART _ => exact PPART2
           | |- ro_cells _ _ T _ => exact TH2
           | |- ro_cells _ _ (CTX + 8) _ => exact TIDC2
           | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HDR2
           | |- 16 < rz_size n -> _ => intros _; exact MG2
           | |- rw_cells _ _ _ [CB (Z.to_nat (Z.min _ _)) _] => exact UC2
           | |- ro_cells _ _ (0x7fff8000 + Z.shiftr _ 3) _ => rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; exact (proj1 SHC2)
           | |- bv_unsigned _ <> 0 => exact NZ
           | |- rw_cells _ _ (0x7fff8000 + _ / 8) [CB _ _] => exact SH2
           | |- rw_cells _ _ (0x7fff8000 + Z.shiftr _ 3) _ => exact PGC2
           | |- allocA_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact AFR2
           | |- rw_cells _ _ (STK + -16) _ => exact FR162
           | |- rw_cells _ _ (SP + -56) _ => exact FR72
           | |- rw_cells _ _ STK _ => exact STKC2
           | |- u64arr _ _ (STK + 16) _ => exact HTR2
           | |- length _ = 30%nat => exact HL30
           | |- 1 <= _ <= 30 => exact SZB
           | |- _ <= d + 2 => exact SZD
           | |- rw_cells _ _ (STK + 256) _ => exact F18002
           | |- rw_cells _ _ (STK + 2056) _ => exact TFBP2
           | |- rw_cells _ _ (STK + 2064) _ => exact F82
           | |- rw_cells _ _ (T + 3168) _ => exact UNW2
           | |- rw_cells _ _ (T + 2800) _ => exact STH2
           | |- u64arr _ _ (T + 2912) _ => exact STB2
           | |- length _ = 32%nat => exact HL
           | |- depot_inv _ _ _ _ _ => exact DI2
           | |- depot_cs _ _ _ => exact DCSc
           | |- _ + 128 <= 2^32 => exact TFMAX
           | |- _ + 2 <= _ => exact NB2
           | |- stk _ _ _ _ => exact ST2
           | |- mem_inv _ _ => exact MI2
           | |- K _ _ _ _ _ => exact HK2
           | |- J _ _ => exact HJ2
           | |- Gn _ _ _ _ => apply GN
           | |- Gs _ _ (_ ++ _) _ => apply GSX
           | |- Gs _ _ _ _ => apply GS
           | |- forall x, Gs _ _ _ _ => intros x0; apply GSX
           | |- forall k, _ => first [exact APTn| exact APCn| exact APSn| exact APTs| exact APCs| exact APSs| (intros x0; apply GSX)| match goal with |- ?G => fail 99 "FK" G end]
           | |- ?G => fail "mseg_chunk premise" G
           end. }
    intros cf' PO'. unfold chunk_post in PO'. fold RB in PO'. fold ABv in PO'.
    ddestruct PO' as (ms9 & mo9 & nb' & bl' & N' & tf' & id & z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & b1' & pgb' & sj0 & sj1 & sj2 & bs9 & m9
                      & -> & -> & HK9 & HJ9 & DI9 & DCS9 & DST9 & IDB & NB' & TFB' & TFP & CSM & BLK & GK & ZK & WM9 & MI9 & ST9 & HDR9 & B1A & B1B & MG9 & SH9 & PGC9 & PGU & UC9 & STH9 & STB9 & HL9 & UNW9).
    (* [comment removed for export] *)
    assert (PGWc : (nfix n mod 8 = 0 /\ pgw = 0) \/ (nfix n mod 8 <> 0 /\ pgw = 1)).
    { unfold pgw. destruct (Z.eqb_spec (nfix n mod 8) 0); [left| right]; split; auto. }
    set (PGSv := 0x7fff8000 + Z.shiftr (ABv + rz_size n + nfix n / 8 * 8) 3) in *.
    assert (PGSE : PGSv = 0x7fff8000 + (ABv + rz_size n) / 8 + nfix n / 8).
    { subst PGSv. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. clear - DAB RC DNF MNF. lia. }
    set (cw := [(ABv + rz_size n + -16, ABv + rz_size n + -16 + 16); (ABv, ABv + 16); (ABv + rz_size n, ABv + rz_size n + Z.min (nfix n) 4096);
                (0x7fff8000 + (ABv + rz_size n) / 8, 0x7fff8000 + (ABv + rz_size n) / 8 + nfix n / 8); (PGSv, PGSv + pgw)]).
    assert (ZK' : forall x : word, zone u f (bv_unsigned x) -> outside cw (bv_unsigned x) -> m9 x = mm x).
    { intros x HZ HO. subst cw. cbn [outside app] in HO. ddestruct HO as (O1 & O2 & O3 & O4 & O5 & _).
      destruct (Z.eq_dec (bv_unsigned x) PGSv) as [E|NE].
      - destruct PGWc as [[E0 P0]|[E1 P1]]; [| exfalso; clear - O5 E P1; lia].
        rewrite <- (Z_to_bv_bv_unsigned x). rewrite E. exact (PGU E0).
      - apply ZK; [exact HZ|]. unfold cwin. cbn [outside]. refine (conj O1 (conj O2 (conj O3 (conj O4 (conj _ I))))).
        match goal with |- ~ (?P <= _ < _) => change PGSv with P in NE end. clear - NE. intros [H1 H2]. apply NE. lia. }
    assert (ZKM : forall A sz, (forall a, A <= a < A + sz -> zone u f a) -> munch (cw ++ [(0, A); (A + sz, 2^64)]) mm m9).
    { intros A sz HZ x Hx. subst cw. cbn [outside app] in Hx. ddestruct Hx as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & _).
      pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
      apply ZK'; [apply HZ; clear - O6 O7 XR; lia|]. cbn [outside]. clear - O1 O2 O3 O4 O5. tauto. }
    (* [comment removed for export] *)
    dpose GSEP as (_ & _ & SEP3').
    assert (CHI : ABv + cs <= RB + mu + unit_if u /\ RB <= ABv /\ RB + mu + unit_if u <= FA) by (subst ABv; cbv delta [FA] in *; clear - OFF PWR UIF MUH MUB2 RBE; lia).
    (* [comment removed for export] *)
    assert (ZR : forall a, RI <= a < RI + 4096 -> zone u f a) by (intros a Ha; left; split; [apply (CSRI' u f); exact Ha| clear - Ha ERI SBlo; lia]).
    assert (ZT : forall a, T <= a < T + 2800 -> zone u f a) by (intros a Ha; left; split; [apply (CST' u f); clear - Ha; lia| clear - Ha; lia]).
    assert (ZC : forall a, CTX <= a < CTX + 0x10000 -> zone u f a) by (intros a Ha; left; split; [apply (CSCTX' u f); exact Ha| clear - Ha; lia]).
    assert (ZL : forall a, 0x10000 <= a < 0x10000 + (A_SS - 0x10000) -> zone u f a) by (intros a Ha; right; right; unfold A_SS, A_DEP_END in *; clear - Ha; lia).
    assert (ZH : forall a, A_DEP_END <= a < A_DEP_END + (0x65f000 - A_DEP_END) -> zone u f a) by (intros a Ha; right; right; unfold A_SS, A_DEP_END in *; clear - Ha; lia).
    assert (ZS : forall a, 0x7fff8000 + SB / 8 <= a < 0x7fff8000 + SB / 8 + ((RI + 4096) / 8 - SB / 8) -> zone u f a) by (intros a Ha; right; left; clear - Ha; lia).
    assert (ZF : forall a, FA <= a < FA + (mfa + unit_if f) -> zone u f a).
    { intros a Ha. left. split; [| clear - Ha FAS MF0 UIF; destruct f as [[|]|]; cbn [unit_if] in Ha; lia].
      destruct (Z_lt_ge_dec a (FA + mfa)) as [LT|GE]; [apply CSinc0; apply CSFA; clear - Ha LT; lia|].
      destruct f as [[|]|]; cbn [unit_if] in Ha; [| exfalso; clear - Ha GE; lia| exfalso; clear - Ha GE; lia]. apply (CSFz u). cbv delta [FAA] in *. clear - Ha GE. lia. }
    assert (ZU : u = Some true -> forall a, UA <= a < UA + 2^18 -> zone u f a).
    { intros Eu a Ha. left. split; [subst u; apply (CSUz f); exact Ha| clear - Ha FAS MU0 MF0 UAE; lia]. }
    pose proof (ZKM _ _ ZR) as MUR. pose proof (ZKM _ _ ZT) as MUT. pose proof (ZKM _ _ ZS) as MUS. pose proof (ZKM _ _ ZF) as MUF.
    (* [comment removed for export] *)
    assert (ZKW : forall W, (forall a, 0 <= a < 2^64 -> outside W a -> zone u f a /\ outside cw a) -> munch W mm m9).
    { intros W HW x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
      destruct (HW _ XR Hx) as [HZ HO]. exact (ZK' x HZ HO). }
    assert (MUlow9 : munch (cw ++ [(0, 0x10000); (A_SS, A_DEP_END); (0x65f000, 2^64)]) mm m9).   (* [comment removed for export] *)
    { apply ZKW. intros a AR Ha. unfold cw in Ha. cbn [outside app] in Ha. ddestruct Ha as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & _).
      split; [| unfold cw; cbn [outside]; clear - O1 O2 O3 O4 O5; tauto]. right. right. clear - O6 O7 O8 AR. lia. }
    assert (MUthr9 : munch (cw ++ [(0, 0x10000); (A_SS, A_DEP_END); (0x65f000, CTX); (CTX + 0x10000, 2^64)]) mm m9).
    { apply ZKW. intros a AR Ha. unfold cw in Ha. cbn [outside app] in Ha. ddestruct Ha as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & _).
      split; [| unfold cw; cbn [outside]; clear - O1 O2 O3 O4 O5; tauto].
      destruct (Z_lt_ge_dec a 0x65f000) as [LT|GE]; [right; right; clear - O6 O7 LT AR; lia| left; split; [apply (CSCTX' u f); clear - O8 O9 GE CX0 AR; lia| clear - O8 O9 GE CX0 AR; lia]]. }
    (* [comment removed for export] *)
    assert (RZ16 : rz_size n mod 16 = 0) by (clear - RC; lia). pose proof (Z.div_mod (rz_size n) 16 ltac:(clear; lia)) as DRZ. rewrite RZ16, Z.add_0_r in DRZ.
    assert (DJW : forall A k A0 sz, (A + k <= ABv \/ ABv + cs <= A) -> (A + k <= 0x7fff8000 + ABv / 8 \/ 0x7fff8000 + (ABv + cs) / 8 <= A) ->
              (A + k <= 0 \/ A0 <= A) -> A + k <= A0 + sz -> disjoint_from (cw ++ [(0, A0); (A0 + sz, 2^64)]) A k).
    { intros A k A0 sz H1 H2 H3 H4. unfold cw. cbn [disjoint_from app]. rewrite PGSE.
      clear - H1 H2 H3 H4 PGWc DNF MNF RZSB N2B' N2CS NFB DAB DRZ DCS16 CSR. repeat split; lia. }
    assert (DJW2 : forall A k, (A + k <= ABv \/ ABv + cs <= A) -> (A + k <= 0x7fff8000 + ABv / 8 \/ 0x7fff8000 + (ABv + cs) / 8 <= A) -> 0x10000 <= A /\ A + k <= A_SS ->
              disjoint_from (cw ++ [(0, 0x10000); (A_SS, A_DEP_END); (0x65f000, 2^64)]) A k).
    { intros A k H1 H2 H3. unfold cw. cbn [disjoint_from app]. rewrite PGSE. unfold A_SS, A_DEP_END in *.
      clear - H1 H2 H3 PGWc DNF MNF RZSB N2B' N2CS NFB DAB DRZ DCS16 CSR. repeat split; lia. }
    (* [comment removed for export] *)
    assert (ABlo : 0x10007fff9000 <= ABv /\ ABv + cs <= RI) by (clear - CHI FAS SBlo MU0 MF0; lia).
    Ltac t9 H MU WM DJ tac := eapply rw_cells_transport; [exact H| exact MU| exact WM| apply DJ; cbn [cells_size csize Nat.add length map Z.of_nat Pos.of_succ_nat Pos.succ]; tac].
    apply HCHK. unfold mgen_postC.
    eexists. dexists mo9, (ABv + rz_size n), u, f, nb', bl'. dexists z0, z1, z2, za1, za2, za3, za4, za5, za6, za7, z3, z4, z5, z6.
    (* [comment removed for export] *)
    assert (TJ9 : exists q1 q2, rw_cells asegs m9 (T + 2872) [C8 q1; C8 q2]).
    { assert (TJc : rw_cells asegs mm (T + 2872) [CB 16 (le8 k1 ++ le8 k2)]) by (eapply rw_cells_reshape; [exact TJ2| cbn [cells_wf cell_wf]; rewrite app_length, !length_le8; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite !app_nil_r; reflexivity]).
      assert (MUall : munch [(0, 2^64)] mm m9) by (intros x Hx; exfalso; cbn in Hx; pose proof (bv_unsigned_in_range 64 x) as XR; unfold bv_modulus in XR; change (2 ^ Z.of_N 64) with (2^64) in XR; clear - Hx XR; lia).
      destruct (CB_holed asegs _ mm m9 (T + 2872) 16 _ TJc MUall WM9 ltac:(intros i Hi; apply asegs_none_off; clear - T0 Hi; lia)) as [bs' [H' _]].
      destruct (CB16_words asegs m9 _ _ H') as (q1 & q2 & H''). dexists q1, q2. exact H''. }
    ddestruct TJ9 as (q1 & q2 & TJ9).
    dexists stw', cstw', q1, q2, k3, m9.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HK9|]. split; [exact HJ9|]. split; [exact MUB2|].
    split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM9))|]. split; [exact MI9|]. split; [exact ST9|].
    split; [intros y Hy; apply CSM; apply CSinc0; exact Hy|].
    split; [exact DST9|].
    split; [eapply (poison_statics_transport _ mm m9 PS2 MUlow9); intros A k H; apply DJW2; unfold A_SS in *; clear - H ABlo; lia|].
    split. { ddestruct TS2 as (X1 & X2 & X3 & X4). unfold thr_statics. unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR in *.
             assert (DJT : forall A k, (A + k <= A_SS \/ (A_DEP_END <= A /\ A + k <= 0x65f000) \/ (CTX <= A /\ A + k <= CTX + 0x10000)) -> 0x10000 <= A ->
                       disjoint_from (cw ++ [(0, 0x10000); (A_SS, A_DEP_END); (0x65f000, CTX); (CTX + 0x10000, 2^64)]) A k).
             { intros A k H1 H2. unfold cw. cbn [disjoint_from app]. rewrite PGSE. unfold A_SS, A_DEP_END in *. dpose GSEP as (_ & _ & SEPc).
               clear - H1 H2 PGWc DNF MNF RZSB N2B' N2CS NFB DAB DRZ DCS16 CSR ABlo CX0 CX1 SEPc CHI FAS ERI RIhi SBlo. repeat split; lia. }
             repeat split; (eapply ro_cells_transport; [eassumption| exact MUthr9| apply DJT; unfold A_SS, A_DEP_END; cbn; clear - CX0; lia]). }
    split; [eapply (mwc_statics_transport _ mm m9 MWS2 MUlow9); intros A k H; apply DJW2; unfold A_SS in *; clear - H ABlo; lia|].
    split; [eapply (pop_statics_transport _ mm m9 SB PPS2 MUlow9); intros A k H; apply DJW2; unfold A_SS in *; clear - H ABlo; lia|].
    split; [t9 MX2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|]. split; [t9 MFA2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|].
    split; [t9 M402 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|]. split; [t9 MUC2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|].
    split; [t9 M562 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|]. split; [t9 STW2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|].
    split; [t9 STC2 MUT WM9 DJW ltac:(clear - ABlo CHI FAS ERI SBlo MF0 MU0 SEP1 T0 T1 CR PCRE RIhi; lia)|]. split; [exact TJ9|].
    split; [t9 SJ2 MUT WM9 DJW ltac:(clear - ABlo CHI FAS ERI SBlo MF0 MU0 SEP1 T0 T1 CR PCRE RIhi; lia)|].
    (* [comment removed for export] *)
    split; [intros Hf; t9 (FSH Hf) MUS WM9 DJW ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia); clear - ABlo CHI FAS ERI SBlo RIhi MF0 MU0 UIF UAE FAAE FAE RBE PGSE PGWc DNF MNF RZSB N2B' N2CS DAB DRZ DCS16 CSR; lia)|].
    split; [intros Hf; t9 (FSHn Hf) MUS WM9 DJW ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia); clear - ABlo CHI FAS ERI SBlo RIhi MF0 MU0 UIF UAE FAAE FAE RBE PGSE PGWc DNF MNF RZSB N2B' N2CS DAB DRZ DCS16 CSR; lia)|].
    split. { intros Hu HMU. assert (OFF' : 16 * (bv_unsigned pw mod 2^32) + cs <= mu) by (destruct u as [[|]|]; cbn [unit_if] in OFF; [exfalso; apply Hu; reflexivity| clear - OFF; lia| clear - OFF; lia]).
             t9 (USHn Hu HMU) MUS WM9 DJW ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia);
                assert (ABvE : ABv = RB + 16 * (bv_unsigned pw mod 2^32)) by reflexivity;
                clear - OFF' ABlo CHI FAS ERI SBlo RIhi MF0 MU0 UIF UAE FAAE FAE RBE PGSE PGWc DNF MNF RZSB N2B' N2CS DAB DRZ DCS16 CSR PWR ABvE; lia). }
    split; [exact UNW9|]. split; [exact I|].
    dexists ABv, cnt', ds', pw, N', tf', id, b1', pgb', sj0, sj1, sj2, bs9.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HC'|]. split; [exact NTH|]. split; [exact LDS'|].
    split.
    { (* [comment removed for export] *)
      intros x. cbv zeta. intros HO HBn HBs. cbn [outside app] in HO. unfold mgen_windows in HO. cbn [outside app] in HO.
      ddestruct HO as (W1 & W2 & W3 & W4 & W5 & O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15 & O16 & O17 & O18 & O19 & O20 & O21 & O22 & _).
      transitivity (mm x).
      - destruct (Z.eq_dec (bv_unsigned x) PGSv) as [E|NE].
        + destruct PGWc as [[E0 P0]|[E1 P1]]; [| exfalso; clear - W5 E P1; lia]. rewrite <- (Z_to_bv_bv_unsigned x). rewrite E. exact (PGU E0).
        + apply GK; [| exact HBn| exact HBs]. unfold cwin. cbn [outside]. refine (conj O1 (conj O2 (conj _ (conj W1 (conj W2 (conj W3 (conj W4 (conj _ I)))))))).
          * clear - O3 O6. lia.
          * match goal with |- ~ (?P <= _ < _) => change PGSv with P in NE end. clear - NE. intros [H1 H2]. apply NE. lia.
      - rewrite (MU2 x). 2:{ cbn [outside app]. subst SPA STK.
                             repeat split; first [sassumption | cassumption | exact O8| exact O9| exact O10| exact O11| exact O7| exact O5| exact O4| exact O12| exact O13| exact O14| exact O15| exact O16| exact O17| exact O18| exact O21| exact O22| exact I | (clear - O1; lia)]. }
        apply (MU1 x). cbn [outside]. repeat split; first [exact O1| exact O3| exact I]. }
    split; [t9 PC2 MUT WM9 DJW ltac:(clear - ABlo CHI FAS ERI SBlo MF0 MU0 SEP1 T0 T1 CR PCRE RIhi; lia)|].
    split; [eapply u32arr_transport; [exact ARR2| exact MUT| exact WM9| rewrite LDS'; apply DJW; clear - ABlo CHI FAS ERI SBlo MF0 MU0 SEP1 T0 T1 CR PCRE RIhi; lia]|].
    split.
    { destruct CASES as [(Ecnt & Eds & Eu & Ef & NF2 & AU2 & EX2 & HFAR2 & HJS2) | (CNT0 & Ecnt & Un & Fn & new & ws' & fa' & rest & nf' & au' & ex' & Eds & Efa & Lws & Lfa' & SRC & NF2 & AU2 & EX2 & HFAR2 & HREST2 & Lrest)].
      - left. split; [exact Ecnt|]. split; [exact Eds|]. split; [exact Eu|]. split; [exact Ef|].
        split; [t9 NF2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|]. split; [t9 AU2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|]. split; [t9 EX2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|].
        split; [eapply u32arr_transport; [exact HFAR2| exact MUF| exact WM9| rewrite LFA; apply DJW; clear - ABlo CHI FAS ERI SBlo RIhi MF0 MU0 UIF UIFf HNF HNF2 LJS0 FAAE FAE RBE; lia]|].
        eapply u32arr_transport; [exact HJS2| exact MUF| exact WM9| apply DJW; clear - ABlo CHI FAS ERI SBlo RIhi MF0 MU0 UIF UIFf HNF HNF2 LJS0 FAAE FAE RBE; lia].
      - right. split; [exact CNT0|]. split; [exact Ecnt|]. split; [exact Un|]. split; [exact Fn|].
        dexists new, ws', fa', rest, nf', au', ex'.
        split; [exact Eds|]. split; [exact Efa|]. split; [exact Lws|]. split; [exact Lfa'|]. split; [exact SRC|].
        split; [t9 NF2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|]. split; [t9 AU2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|]. split; [t9 EX2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|].
        split; [eapply u32arr_transport; [exact HFAR2| exact MUF| exact WM9| rewrite Lfa'; apply DJW; cbn; clear - ABlo CHI FAS ERI SBlo RIhi MF0 MU0 UIF UIFf Lrest HNF FAAE FAE RBE; lia]|].
        split; [| exact Lrest]. eapply u32arr_transport; [exact HREST2| exact MUF| exact WM9| apply DJW; cbn; clear - ABlo CHI FAS ERI SBlo RIhi MF0 MU0 UIF UIFf Lrest HNF Lfa' FAAE FAE RBE; lia]. }
    split.
    { (* [comment removed for export] *)
      intros Eu. destruct (USH Eu) as [UZ USHz]. pose proof (ZKM _ _ (ZU Eu)) as MUU.
      destruct (CB_holed asegs _ mm m9 UA _ _ UZ MUU WM9 ltac:(intros i Hi; apply asegs_none; [clear - Hi FAS SBlo UAE MU0; lia| clear; lia])) as [zb [ZB9 ZBH]].
      destruct (CB_holed asegs _ mm m9 _ _ _ USHz MUS WM9 ltac:(intros i Hi; apply asegs_none; [clear - Hi FAS SBlo UAE MU0; lia| clear; lia])) as [ush [USH9 USHH]].
      dexists zb, ush. split; [exact ZB9|]. split; [exact USH9|]. split.
      - intros i Hi HO. rewrite (ZBH i Hi); [apply nth_error_repeat; exact Hi|]. unfold cw. cbn [outside app] in HO |- *. ddestruct HO as (O1 & O2 & O3 & _).
        rewrite PGSE. clear - O1 O2 O3 Hi ABlo CHI FAS SBlo ERI RIhi MU0 MF0 UAE RZSB N2B' N2CS NFB PGWc. repeat split; try exact I; first [lia | match goal with |- ?G => fail 99 "DBG" G end].
      - intros i Hi HO. rewrite (USHH i Hi); [apply nth_error_repeat; exact Hi|]. unfold cw. cbn [outside app] in HO |- *. ddestruct HO as (O1 & O2 & _).
        rewrite ?Z.shiftr_div_pow2 in O2 by (clear; lia). change (2 ^ 3) with 8 in O2.
        revert O1 O2. rewrite PGSE. intros O1 O2. clear - O1 O2 Hi ABlo CHI FAS SBlo ERI RIhi MU0 MF0 UAE RZSB N2B' N2CS NFB PGWc DAB DRZ DNF MNF DCS16. repeat split; try exact I; first [lia | match goal with |- ?G => fail 99 "DBG2" G end]. }
    split; [exact DI9|]. split; [exact DCS9|]. split; [exact IDB|]. split; [exact NB'|]. split; [exact TFB'|]. split; [exact TFP|]. split; [exact BLK|].
    split; [intros y Hy; apply CSM; apply ACScs; exact Hy|].
    split; [exact HDR9|]. split; [exact B1A|]. split; [exact B1B|]. split; [exact MG9|]. split; [exact SH9|]. split; [exact PGC9|]. split; [exact UC9|].
    split; [exact STH9|]. split; [exact STB9|]. split; [exact HL9|].
    split; [eapply rw_cells_transport; [exact OOM2| exact MUlow9| exact WM9| apply DJW2; unfold A_OOM_CELL, A_SS; cbn; clear - ABlo; lia]|].
    eapply rw_cells_transport; [exact ERR2| exact MUlow9| exact WM9|]. unfold cw, A_ERRNO, A_SS, A_DEP_END.
    cbn [disjoint_from app cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite PGSE.
    clear - ABlo CHI FAS PGWc DNF MNF RZSB N2B' N2CS NFB DAB DRZ DCS16 CSR. repeat split; first [lia | match goal with |- ?G => fail 99 "ERRLIA" G end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "08I0@L10009363542.38 L10009363542.40 L10015668588.35 L10049798517.17 L10054450872.34 L10118203588.16 L10140493218.39 L10210605711.19 L10217539573.35 L10274126988.21 L10278559848.6  L10307921259.3  L10326949034.11 L10512070732.39 L10598670465.11 L10609050916.28 L10634931672.34 L10702588176.8  L11125573801.35 L11179226509.28 L11188449489.2  L11210639066.6  L11266334853.36 L117293985.40   L11920473469.27 L1225372328.34  L12376458638.8  L12433800977.21 L12522026373.1  L12673344616.23 L12673344745.26 L12677617336.38 L12761674836.5  L12862884641.2  L12865463121.26 L13125566298.21 L13328137276.23 L13328137405.26 L13332500204.38 L13392737556.26 L13392737685.23 L13396739909.38 L13415130216.1  L13546343634.40 L1358472242.39  L13636421100.6  L13821507617.3  L13982808854.21 L13992303238.21 L14529942053.2  L14798118929.40 L1483954540.27  L15002076226.39 L15100376903.2  L15572525375.33 L15732996402.39 L15786958986.2  L1587938449.21  L15953230509.2  L16329970322.23 L16333758530.38 L16378060235.39 L1637893174.1   L16427811904.8  L16730790281.28 L16842783084.39 L16964261176.11 L17120848823.0  L1746374919.12  L1770588981.36  L18076307788.21 L18080222632.6  L18284602179.36 L18289752719.21 L18302958969.1  L18404416940.6  L18568419057.40 L18820494961.40 L18926572867.30 L18926759668.13 L18928751437.428L18928767426.409L18933043916.12 L19045990537.21 L19131746828.21 L19135698664.6  L1925825477.3   L19305944170.39 L19344668279.21 L19545310187.2  L19545310191.3  L19704062231.39 L19723288167.7  L19764912339.9  L1994926337.40  L20009076335.35 L20011187029.38 L20011187029.40 L20348672026.21 L20604267895.35 L20610551885.38 L20610551885.40 L20703260783.35 L20709543253.38 L20709543253.40 L207740136.6    L20836822950.8  L20936524850.39 L2096835953.40  L21026692994.36 L21091747050.11 L21196358698.11 L212140044.21   L21279792490.39 L21484273060.28 L21629852572.3  L21725399676.38 L21831749564.39 L2189761147.7   L22013687057.40 L22120290505.39 L22174551818.2  L22343894949.9  L22657062026.28 L22724381928.1  L2279284007.11  L22953571684.40 L22953572370.43 L22984328200.9  L23028283098.6  L23188247429.36 L23294334865.21 L23304605630.15 L23343287261.0  L2357568477.35  L2363858663.38  L2363858663.40  L2375534541.2   L23803517183.0  L23898603878.1  L23929545039.40 L24006580716.39 L24109524442.1  L24144998104.34 L24226811473.26 L24322338809.1  L24413245228.6  L24545243113.23 L24554356127.9  L24554356248.6  L24560632610.7  L24854934790.21 L24888640626.2  L24891049031.424L24892851395.11 L24893049158.423L24896606255.11 L24897143244.12 L24897143244.3  L25153276879.4  L25315005151.26 L25379332253.38 L25379332253.40 L25381428647.35 L2542880046.34  L25538123100.39 L25847583755.26 L25864701137.6  L25977033196.8  L25982463935.8  L25984553605.13 L25984553605.9  L26013379921.6  L26095055493.36 L26396448700.39 L2647262414.5   L26606187674.28 L26848617105.21 L27181232506.43 L27181235212.40 L27466439871.3  L2750523041.40  L27600588140.39 L27697017043.3  L27698369826.39 L27706333745.19 L27848808849.2  L28156715786.40 L28156718716.43 L28540910183.21 L28762839709.0  L2880327153.30  L29109465037.38 L29109465037.40 L29115749111.35 L29435446705.26 L29452980609.8  L29677298433.1  L29718441094.4  L29757571546.6  L29879685821.35 L30130474185.11 L30233433986.39 L30338059610.6  L30339995769.1  L30378678657.11 L30435077518.7  L30437516088.6  L30573236684.7  L30604076560.8  L30663996904.1  L30892283345.6  L31194525850.21 L3148603910.21  L31525159917.17 L31533430865.6  L31640645505.11 L31769455548.39 L31782326386.4  L31897782189.9  L32058929066.11 L32061267910.21 L32758332925.13 L32896197943.40 L33154884329.28 L33227838273.3  L33337353996.21 L33349663720.6  L33399094770.8  L33606059170.39 L33698313473.11 L33767074080.40 L33903535282.8  L34169490961.21 L34301840561.4  L34301840690.33 L34301841077.37 L34357058654.38 L34458320289.21 L34706040863.33 L35125087399.35 L35131388317.38 L35131388317.40 L35233459586.38 L35233459586.40 L35239743672.35 L35393843785.7  L35730156934.21 L35847935625.40 L35847937023.43 L35867261841.22 L3597417215.0   L36075687453.0  L36191859358.7  L36193165570.2  L36242603004.1  L36406153938.2  L3646482674.8   L36489735793.40 L36565753704.6  L36569727884.21 L36571201320.0  L36670452064.28 L36819807445.26 L36948563441.40 L36981996200.34 L37725871377.21 L37806923217.21 L37906787233.40 L3812222724.35  L38235734261.1  L38446489793.11 L38475802529.40 L38630853356.13 L38630853356.9  L38637156310.8  L38700110972.1  L39160644010.11 L39188636933.0  L39220637093.0  L39332637397.0  L395858539.12   L39774454594.11 L39808216143.40 L40541032097.40 L40558890220.39 L40653650929.37 L40690307201.8  L40702779304.34 L4070786866.39  L41154907957.36 L41398109864.34 L41488597692.39 L41549943719.35 L41556242077.38 L41556242077.40 L41757127204.6  L41882435733.9  L42149244736.8  L42312019697.11 L42473080748.6  L42554935773.0  L42817616661.16 L42817616661.17 L42819977213.7  L42908497706.11 L42984359187.6  L43581313045.4  L43655446538.2  L43810840756.38 L44072740983.4  L44108320741.36 L44110593132.3  L44150440701.3  L44300882312.15 L44437059391.13 L44683283690.4  L45184660297.8  L45295076406.1  L45396721589.34 L45450153110.14 L45626123802.21 L45635383918.15 L46336287196.36 L4638274038.28  L46446536810.38 L46450547259.26 L46450547386.23 L46573847558.21 L46680981092.22 L46798637366.1  L46801378195.26 L47312073682.40 L47409641326.38 L47514216928.28 L4819779461.36  L48324997040.28 L48500666668.6  L48595508494.38 L48648739903.6  L48712615400.6  L48716536076.21 L48736336254.19 L48736336254.20 L48883743118.38 L49029283034.38 L49779527525.21 L49791865729.6  L49946329501.38 L49946329501.40 L49952636071.35 L4999168337.4   L49995285886.4  L50003475879.10 L50132325126.21 L50171351240.34 L50194977587.3  L50376799635.2  L50434248917.38 L50434248917.40 L50440547823.35 L50694634314.14 L50720667200.6  L50810147341.28 L50811079681.40 L51226421522.0  L51485564634.6  L51765344620.1  L51788915964.1  L51901902375.33 L52229988184.34 L52310674614.1  L52412439154.21 L52469894736.11 L52482632712.19 L52482632712.20 L52530306974.8  L52594603377.40 L52694741641.39 L52793108830.38 L52806941544.1  L52930216858.21 L52937896755.8  L52973276663.10 L52973276663.8  L53380004446.38 L53385470898.11 L53412032513.11 L53586826820.6  L53728160474.26 L53777391274.11 L53779857969.4  L54082232744.34 L54082473377.40 L5429770831.4   L54509494956.6  L54558294872.34 L54641519825.6  L54891896087.12 L55082185895.35 L55084272029.38 L55084272029.40 L55379812102.28 L5538628448.33  L55410835542.7  L5556750885.8   L55588686165.0  L5580650899.12  L55899845783.3  L55997489714.10 L55997509718.16 L55997509718.17 L55997509718.6  L55997509718.8  L56164433861.8  L56248205346.7  L56488697498.21 L57019285036.6  L57055401635.16 L57155905586.39 L5721498072.4   L57333628785.17 L57408811761.40 L57432918668.21 L57436486790.21 L57436804712.6  L57485903630.6  L57544720881.40 L57924165753.1  L58409901413.9  L58429566721.11 L58835949340.1  L58869690912.40 L59009349437.15 L59204339248.28 L59273826574.38 L59308696420.11 L59308696420.9  L59308845553.3  L59314955108.11 L59321251735.3  L59552029477.0  L5983160098.39  L6002171007.23  L60418839161.9  L60432055545.1  L60536527916.6  L60662235184.15 L60694006433.40 L60785358792.0  L60990546787.33 L61030858054.406L61076581038.38 L61080885374.23 L61313163918.38 L6131481214.38  L61477218587.36 L61649787821.2  L61834075013.36 L62156106983.37 L62156107616.33 L62339778138.6  L62507327512.6  L62582126956.35 L62584210518.38 L62584210518.40 L62682894286.26 L62719081734.4  L62740636161.11 L62884884705.38 L63220859395.11 L63374621462.407L63404914589.0  L63626208655.38 L63821274278.34 L63897450449.5  L64334606430.38 L64355056882.5  L6444131489.40  L64640476714.11 L64672813665.0  L65648049560.39 L6600342017.1   L6659308522.2   L6669525048.2   L6669536739.5   L6669597647.5   L6673760071.9   L66751039889.21 L66763458562.7  L66804175198.38 L67099864699.34 L67332458778.21 L67352125345.40 L67523687663.35 L67525773781.38 L67525773781.40 L6755912037.4   L67673999556.17 L67680528389.1  L67717556775.3  L67782583095.0  L67834325417.23 L6783662148.0   L6787527454.6   L6793809444.7   L68188979381.36 L68387087208.30 L6882516600.39  L701988789.36   L7332611253.11  L7336713913.27  L7419229193.28  L7515578105.15  L7515640660.9   L7657788065.28  L7673915391.0   L7716739305.26  L7794613303.40  L78595897.7     L8201234081.0   L8333054259.6   L8346817460.7   L8353115790.6   L8368274852.6   L8423093436.39  L8731824801.40  L8927212310.6   L8929693118.38  L8934309742.23  L8934309871.26  L8990428885.36  L9047092781.2   L9209891117.27  L9281665857.10  L9488195994.21  L9508785502.38  00001H02J03a04O05Y06E07H08408n09N09^09h0:A0;[0<=0=P0>;0>I0?I0?k0@20@<0A60BL0C]0Dg0E=0Ee0Ei0G00H40Ia0In0J50Jf0K\0L_0M_0OU0PB0Q20RU0RX0Sn0UH0UX0Uc0VO0WJ0WS0Xi0YL0Zf0Zl0[o0]I0]J0^20^70^S0_60`P0`T0`b0b50c80cM0cN0d30eD0ed0f40ff0gN0gQ0ga0hb0ic0j70jK0lQ0n=0nN0oI0oi10910C11_12K12S12T14214E14a15`17117f19F1:<1;91<P1=b1?31?h1AH1AX1B21CL1DM1E?1EX1F11FQ1GP1Hc1Hn1Ie1K?1KU1Lk1NE1NF1Nc1O[1O^1P31Pl1Q`1R:1RD1S>1Sf1TM1TN1Ue1W=1XJ1XO1XP1XS1Z01[31[61[a1\91\<1\L1\h1]@1]N1]e1^`1^a1`g1a81c>1cO1c`1cd1d01d]1f11g;1hQ1iW1jV1kF1kY1l11lA1la1m51mH1nB1o\20121D21l22m24224<25R26U26`27c28X28_29]2:i2;_2;`2<42=H2>R2?h2@J2@Y2@\2@e2@o2B;2B[2D12D;2D>2D`2E62EL2EZ2Eh2Ek2F>2G42Go2HP2Hc2IE2J_2Jl2KH2Ka2L\2M?2NT2OL2OT2P42PD2P]2Q`2RB2S_2T72T_2Tj2VN2X32Y22Yh2Z^2\42]H2^R2_f2a02bF2bY2cT2dN2eS2fC2fD2fE2fX2f[2f^2fd2g=2h>2hN2hn2ho2iQ2ii2jj2l42l\2mD2nZ2oQ2oU30731M31j32D32X32\33533633733833[34935V36l37o38e3943:>3;X3<i3>33?M3@c3B73CA3CS3Cb3D03DN3D^3D_3EK3F43FK3Fd3G53GA3GB3H83HD3IK3IS3I]3JD3Jg3K43KL3KP3LZ3M>3N43Na3O[3PK3RE3SO3T\3UW3VQ3VU3WB3XX3YW3Z93[33\F3\V3]l3^<3^L3^l3_a3`S3ai3cC3cc3d33eG3fQ3gg3h33h@3hR3iM3jG3jO3jW3kV3m63nG3nc3o03oR40Q40R40\40`40c41Z42E42I43143S44?44l45B46C47a48`48c49Y49l4:B4:X4;W4;l4<N4<`4=84=Q4=^4>h4@>4@G4@W4AB4AU4B04CF4DZ4Ed4G74Ge4H@4HO4HP4I34I:4IY4J@4K24KD4KZ4Kn4LI4M?4MO4N64OP4O\4PQ4QR4R24Rm4S=4SO4TP4TS4Tb4UD4UG4Vd4WL4X_4Z54ZU4Zo4[84[\4[k4[l4\o4]\4^94^<4^L4_94`O4`P4a74bg4dA4d]4f34g:4h94h>4i84j54k>4kH4kY4lh4n84o:4oZ4oe50G51F51f53V53W54R55`55l57A57O58e59>59?5:U5:X5:`5:f5;55;D5;Y5<A5<O5=N5>\5?R5@h5B95Bn5DN5DT5EA5EE5EP5EQ5FH5FI5FQ5F\5Gm5HA5I]5Jn5KG5LX5MH5Mn5NI5O\5O]5PJ5Q_5R25R35RF5RQ5RY5Rl5TF5U\5Um5Wg5Y45Z>5[85[=5[`5\<5]25^1S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MU03MF02CR2RS3FAS1A1k2H12H2S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU1A1k2H24SBlo3FASS3hAR2SP1n2lo1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR5LOIMG3SPL4RIhi3MF03FAS1A1k1H4SBlo3MU0S1n2SB2RI2mu3mfa1c2RB2FA2au3HAU3MF03FAS1A1k2H2S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FASS3hAR1n2SB2RI2mu3mfa1c2RB2FA2UA4SBlo3MU03FASS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX02TC2CR2RS3FASS3hAR1n2SB2RI2mu3mfa1c2RB2FA2UA4SBlo3MU03FASS3hAR1n2SB3mfa1c2cs2RB2FA3FAA1f2pw3fa'5rest'3nf'5Lrest3ABvS1n2SB2RI1c2cs1R2RB2FA2RS2pw3ABvS1n2SB2RI1c1R2RSS3bl01j2HjS3hAR1n2SB2RI1c1R4SBlo2RSS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX04SBlo3ERI4SEP12TC4SEP33MF02CR2RS3FASS3hAR1n2lo2SB2RI1c1R5LOIMG4RIhi2RSS3hAR1n1T2SB2RI2mu3mfa1c2cs2RB2FA3PCR2T04SBlo3ERI4SEP13MF02CR3FAS1u2pw3ABv3CHI4ABloS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCRS3hAR3nb01k2X0S3hAR1n2SB2mu3mfa1c2cs2RB2FA3FAA1u2pw3fa'5rest'3nf'4Lfa'3ABv3CHIS3hAR1n1T2SB1c2cs2RB2FA3PCR2pw3ABvS3bl01jS3hAR1T2T0S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3ERI3MF03FASS3hAR3nb01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FAS1k2Y12Y2S3hAR1n1T2SB2RI2mu3mfa1c2cs2RB2FA2T04SBlo3ERI4RIhi3MF03FAS1u2pw3ABv3CHI4ABlo1j2HjS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FASS3hAR3nb02lo5LOIMG1k1XS1n2SB2RI2mu3mfa1c2cs1R2RB2FA3FAS2pw3ABvS2SPS1n2SB1c2cs2RB3CSR2pw3ABv4RZSB3NFB4N2B'4N2CS3DNF3MNF4PGWc3DRZ1A1k2H12H3S1n2SB1c2cs2RB3CSR2pw3ABv4RZSB3NFB4N2B'4N2CS3DNF3MNF4PGWc3DRZ1A1k2H1S3hAR1n3CTX2SB2RI2mu3mfa1c2cs2RB2FA3CX04SBlo3ERI3CSR3FAS1u2pw3ABv4RZSB3NFB4N2B'4N2CS3MNF3CHI4ABlo1A1k2H14SEPcS1n1c2cs2au1iS3nb01kS1n2SB2RI1c2cs2RB2FA2pw3ABv4RZSB3NFB3DAB3DRZ4ABloS1n2SB2RI2mu3mfa1c2cs1R2RB2FA3ERI3MF03FAS1u2pw3ABv3CHIS1n2SB1c2cs2RB3CSR2pw3ABv4RZSB3NFB4N2B'4N2CS3DNF3MNF4PGWc1A1k2H12H3S1n2SB1c2cs2RB3CSR2pw3ABv4RZSB3NFB4N2B'4N2CS3DNF3MNF4PGWc1A1k2H1S3hAR1n3CTX2SB2RI2mu3mfa1c2cs2RB2FA3CX04SBlo3ERI3CSR3FAS1u2pw3ABv4RZSB3NFB4N2B'4N2CS3DNF3MNF4PGWc3CHI4ABlo1A1k2H14SEPcS1n2SB1c2cs2RB3CSR2pw3ABv4RZSB3NFB3MNF1A1k2H1S1n2SB1c2cs2RB3CSR2pw3ABv4RZSB3NFB3MNF1A1k2H12H3S3hAR1n3CTX2SB2RI2mu3mfa1c2cs2RB2FA3CX04SBlo3ERI3CSR3FAS1u2pw3ABv4RZSB3NFB3MNF3CHI4ABlo1A1k2H14SEPcS1TS3hAR3bl01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FAS1j2Y12Y2S3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX04SBlo3ERI4SEP12TC4SEP33MF02CR2RS3FASS1n2SB2RI1c1R2RSS2SP2lo3SPLS3hAR1n2SB2RI2mu3mfa1c2RB2FA2au4RIhi3MF03FASS1n2SB2RI2mu3mfa1c2cs1R2RB2FA4SBlo3ERI3MF03FAS1u2pw3ABv3CHIS3CTX3CX0S3hAR3nb01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FAS1k2Y12Y2S3hAR1n1T2SB1c2cs2RB2FA2pw3ABv1j2HjS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX04SBlo3ERI4SEP12TC4SEP33MF02CR2RS3FASS1n2RCS3hAR1n2SB2RI2mu3mfa1c2cs2RB2FA3FAA4SBlo3FAS1u2pw5rest'3nf'3ABv3CHIS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX04SBlo3ERI4SEP12TC4SEP33MF02CR2RS3FASSS1n2SB2RI2mu3mfa1c2cs1R2RB2FA3FAS2pw3ABvS3CTXS1n2SB1c2cs2RB2pw3ABv1A1k2H3S3hAR1n2SB1c2cs2RB2FA2pw3ABv1A1k2H2S3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX04SBlo3ERI4SEP12TC4SEP33MF02CR2RS3FASS2SPS3hAR3nb01k2X0S3hAR1n1T2SB2RI2mu3mfa1c2cs2RB2FA3PCR2T04SBlo3ERI4RIhi3MF02CR3FAS1u2pw3ABv3CHI4ABloS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX02TC2CR2RS3FASS3hAR1n1T1c3PCR2T02CRSS1n1c2cs3CSR4RZSB3NFB4N2B'4N2CS5DCS16S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU2T04SBlo3ERI4SEP13MF02CR2RS3FASS1n2SB2RI1c2cs1R2RB2FA2RS2pw3ABvS1n2SB2RI1c1R2RSS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3FASS3hAR1n2SB2RI2mu3mfa1c2RB2FA2nf4SBlo3FASS1TS1n2SB2RI1c1R2RSS3hAR3bl01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T02CR2RS3FAS1j2Y1S3hAR3bl01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T02CR2RS3FAS1j2Y1S1n2SB1c2cs2RB2FA2pwS1n2SB2mu1c2RB2au2csS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2au2fa3js02ds2bs3LDS2HL3MU03MF02ws4HL303ds'2pw4LDS'3ws'3fa'3Lws2nw3ABv1w1i2HiS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2au2fa3js02ds2bs3LDS2HL3MU03MF02ws4HL303ds'2pw4LDS'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'2pw4LDS'3ws'3fa'3Lws2nw3ABv1w1i2HiS1n2SB2mu1c2RB2auS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2au2fa3js02ds2bs3LDS2HL3MU03MF02ws4HL303ds'2pw4LDS'3ws'3fa'3Lws2nw3ABv1w1i2HiS1n2SB1c2cs2RB2auS1n2SB1c2cs2RB2auS2SPS1n1c2cs3CSRS1n2SB2RI1c2cs2RB2FA2pw3ABv4RZSB3DAB3DRZ4ABloS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FAS1A1k2H12H2S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU3ERI3MF03FAS1A1k2H24SBloS3hAR2SP1n2lo1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR5LOIMG3SPL4RIhi2RS1A1k1H4SBlo3MF03FASS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP12CR2RS3FASS3hAR2SP1n2lo1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR5LOIMG3CX1S1n2SB1c2cs2RB3CSR2pw3ABv4RZSB3NFB3MNF1A1k2A02H3S3hAR2lo1T5LOIMG2T1S1n2mu1c2cs2au3HAU1w3OFFS3hAR1T2T01A1k1HS3hAR1T2SB2RI3ERI4SEP11A1k2H12H2S3hAR1T2T01A1k2H12H2S3hAR2lo1T5LOIMG2T1S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3ERI3MF03FASS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX04SBlo3ERI4SEP12TC4SEP33MF02CR2RS3FASS2mu2au3HAU4TMOD4TDIVS3hAR1n1T2SB2RI2mu3mfa1c2cs2RB2FA3PCR2T04SBlo3ERI4SEP13MF02CR3FAS1u2pw3ABv3CHI4ABloS1n2SB2RI2mu3mfa1c2cs1R2RB2FA3FAS2pw3ABvS3hAR1n2SB2RI2mu3mfa1c2cs2RB2FA2UA3FAA3FAS1u2pw3ABv4PGSv3CHI4ABloS3hAR1n2SB2RI2mu3mfa1c2cs2RB2FA2UA3FAA3ERI3FAS1u2pw3ABv4PGSv3CHI4ABloS3nb01k2HkS3hAR3bl01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FAS1j2Y12Y2S3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX02TC2CR2RS3FASS1n3N2E3NDBS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX02TC2CR2RS3FASS3hAR1n2lo2SB2RI2mu3mfa1c2RB2FA2UA5LOIMG4RIhi3MF03FASS2SP2loS3hAR1n2SB2RI2mu3mfa1c2cs2RB2FA2UA3FAA3ERI3FAS2pw3ABv3DAB4PGSvS3hAR1n2SB2RI2mu3mfa1c2cs2RB2FA2UA3FAA3ERI3MF03FAS1u2pw3ABv3DAB4PGSv3UIF3CHIS3hAR1n2lo2SB2RI2mu3mfa1c2RB2FA5LOIMG2nf4HNF24RIhi3FASSS1n2SB1c2cs2RB2FA2pwS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FAS1A1k2H12H2S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU3ERI3MF03FAS1A1k2H24SBloS3hAR2SP1n2lo1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR5LOIMG3SPL4RIhi2RS1A1k1H4SBlo3MF03FASS1n2SB1c2cs2RB2pw3ABv1A1k2A02sz2H4S3hAR3nb01T1k1YS1TS2SP1q2HqS3hAR1T2T0S3hAR1n2SB2RI2mu3mfa1c2cs2RB2FA3FAA4SBlo3FAS1u2pw3fa'5rest'3nf'4Lfa'3ABv3CHIS1n2SB2mu1c2cs2RB2pw3PWR1y2Hy2LTS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX04SBlo3ERI4SEP12TC4SEP32CR2RS3FASS3hAR1T2T0S1TS3hAR1n2lo2SB2RI1c1R5LOIMG4RIhi2RSS3hAR2lo3CTX5LOIMG3CX1S3hAR2lo3CTX5LOIMG3CX1S3hAR1T3CTX2TCS3hAR3bl01j2X0S1TS3hAR2lo1T5LOIMG2T1S1n2SB2RI2mu3mfa1c2cs1R2RB2FA3ERI3MF03FAS1u2pw3ABv3CHIS1n2SB2RI2mu3mfa1c2cs1R2RB2FA4SBlo3ERI3MF03FAS1u2pw3ABv3CHIS1n2SB2RI2mu3mfa1c2RB2FA3FAS1A2H1S3hAR2lo1T5LOIMG2T1S3hAR1n2lo2SB2RI1c1R5LOIMG4RIhi2RSS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX04SBlo3ERI4SEP12TC4SEP33MF02CR2RS3FASS3bl01j2H12H3S1n2mu1c2cs2au2nw1i3NWB4CHB2S3hAR1n2SB2RI1c1R4SBlo2RSS1n2SB2RI2mu3mfa1c2cs1R2RB2FA4SBlo3ERI3MF03FAS1u2pw3ABv3CHIS1n2SB2RI2mu3mfa1c2RB2FA2au3HAU3FASS3hAR3bl01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP12CR2RS3FAS1j2Y12Y22Y3S3hAR1n1T2SB2RI2mu3mfa1c2cs2RB2FA3PCR3ERI3MF03FAS2pw3ABvS1T1a2HaS1n2SB2RI1c2cs1R2RB2FA2RS2pw3ABvS1n2SB2RI1c1R2RSS3hAR3nb02SP2lo5LOIMG1k1XS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX02TC2CR2RS3FASS3hAR1n2lo2SB2RI1c1R5LOIMG4RIhi2RSS3hAR3bl01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MU03MF02CR2RS3FAS1j2Y12Y22Y3S3hAR2lo1T5LOIMG2T11j2HjS1n2SB2RI2mu3mfa1c2cs1R2RB2FA3FAS2pw3ABvS1T1x2O32O6S3hAR1n2SB2RI2mu3mfa1c2cs2RB2FA2UA3FAS1u2pw3ABv4RZSB3NFB3CHI4ABlo1i2Hi2O12O34SBlo3MU04N2B'4N2CS4PGWcS3hAR1n2SB2RI2mu3mfa1c2cs2RB2FA2UA3FAS1u2pw3ABv4RZSB3CHI4ABlo1i2Hi3NFB3MNF3DAB4PGWc3DRZ2O12O23ERI3MF0S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au4SBlo3ERI3MF03FASS1n2SB2RI2mu3mfa1c2cs1R2RB2FA3ERI3MF03FAS1u2pw3ABv3CHIS3hAR1n2SB3mfa1c2cs2RB2FA3FAA1f2pw5rest'3nf'5Lrest3ABvS3hAR2SP1n2lo1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR5LOIMG3SPL4RIhi2RS1A1k1H4SBlo3MF03FASS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FAS1A1k2H12H2S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU3ERI3MF03FAS1A1k2H24SBloS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FAS1A1k2H12H2S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU3ERI3MF03FAS1A1k2H24SBloS3hAR2SP1n2lo1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR5LOIMG3SPL4RIhi2RS1A1k1H4SBlo3MF03FASS1n1c2cs2au1i2DA2DCS1n2SB2RI2mu3mfa1c2cs1R2RB2FA4SBlo3ERI3MF03FAS1u2pw3ABv3CHIS3hAR1n2SB2RI2mu3mfa1c2cs2RB2FA2UA3FAA3MF03FAS2pw3ABv4PGSvS3hAR1n2SB2RI2mu3mfa1c2cs2RB2FA2UA3FAA3CSR3FAS1u2pw3ABv4PGSv3CHI4OFF'S3hAR1n2SB2RI2mu3mfa1c2RB2FA2nf3js03HNF4SBlo3FASSSS1n2mu1c2cs2au1H2H0S1nS1TS1n2RCS3hAR3bl02SP2lo5LOIMG1j1XS3hAR3nb01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T02CR2RS3FAS1k2Y1S1n2SB2RI1c1R2RSS1n2SB2RI1c2cs1R2RB2FA2RS2pw3ABvSS3hAR1n1T2SB1c2cs2RB2FA3PCR2pw3ABvS1n2SB1c2cs2RB2FA2pw3ABvS3hAR3nb01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T02CR2RS3FAS1k2Y1S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FASS1n2SB2RI2mu3mfa1c2cs1R2RB2FA3FAS2pw3ABvS1n2SB2RI2mu3mfa1c2cs1R2RB2FA3FAS2pw3ABvS3hAR3bl01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FAS1j2Y12Y2S3hAR1n2SB3mfa1c2cs2RB2FA3FAA2pw3fa'5rest'3nf'4Lfa'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'3nf'3ABv3CHIS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCRS2SPS1n2SB2RI2mu3mfa1c2cs1R2RB2FA3FAS2pw3ABvS3hAR1n2lo2SB2RI1c1R5LOIMG4RIhi2RSS3hAR1n2SB2RI2mu3mfa1c2RB2FA2UA4SBlo3MU03FASS3hAR1n2SB2RI2mu3mfa1c2RB2FA3FAA4SBlo3MF03FASS3hAR3bl02lo5LOIMG1j1XS3hAR3nb01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T02CR2RS3FAS1k2Y1S3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX04SBlo3ERI4SEP12TC4SEP33MU03MF02CR2RS3FASS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au4SBlo3ERI3MF03FASS1TS1n2SB2RI2mu3mfa1c2cs1R2RB2FA3ERI3MF03FAS1u2pw3ABv3CHIS1n2SB1c2pw1x2H12H2S1n2SB1c2RB2pw3ABv3DABS1n2SB1c2RB2pw3ABv3DABS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au4SBlo3ERI3MF03FASS1n1c2cs3CSR5DCS162LTS3hAR1n2lo2SB2RI1c1R5LOIMG4RIhi2RSS1n2SB1c2RB2pw3ABvS1n2SB1c2cs2RB2FA2pw3ABvS3hAR1n2SB2RI1c1R4SBlo2RSS3nb01k2H12H3S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FASS3hAR3nb01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FAS1k2Y12Y2S2SP4TOP2S1n2SB2RI1c1R2RSS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCRS3hAR2lo1T5LOIMG2T1S1n2SB1c2cs2RB2pw3ABv1A1k1HS3hAR2SP1n2lo1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR5LOIMG3SPL4RIhi2RS1A1k1H4SBlo3MF03FASS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FAS1A1k2H12H2S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU3ERI3MF03FAS1A1k2H24SBloS3hAR1n1T2SB2RI2mu3mfa1c2cs2RB2FA3PCR2T04SBlo3ERI4RIhi3MF02CR3FAS1u2pw3ABv3CHI4ABloS3hAR1n2SB3mfa1c2cs2RB2FA3FAA2pw5rest'3nf'3ABvS1n1c2cs4RZSB3NFB4N2B'4N2CSS3hAR1T2T01j2HjSS1n2SB2RI1c2cs2RB2pw3ABv4ABlo1A1k1HS1A1k1HS1T3CTX2SB2RI3CX01a2AR2O82O92GES1n1T3CTX2SB2RI2mu3mfa1c2RB2FA3FAS1a2HaS1n1T3CTX2SB2RI2mu3mfa1c2RB2FA2UA3MU03MF03FAS1a2HaS1T3CTX2SB2RI1a2HaS1T3CTX2SB2RI3ERI1a2HaS1n2SB2RI1c1R3ERI2CRS1n1c2cs4RZSB3NFB4N2B'4N2CSS1n2SB2RI2mu3mfa1c2cs1R2RB2FA3ERI3MF03FAS1u2pw3ABv3CHIS1n2SB2RI1c1R2RSS1n2SB2RI2mu3mfa1c2RB2FA3ERI3MUH3MF12CRS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX04SBlo3ERI4SEP12TC4SEP33MF02CR2RS3FASS2SB2RI1a2HaS1n2SB2RI2mu3mfa1c2cs2RB2FA4SBlo3MF03FAS1u2pw3ABv3CHIS3hAR3bl01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T02CR2RS3FAS1j2Y1S1n2SB2RI1c2cs1R2RB2FA2RS2pw3ABvS1n2SB2RI2mu3mfa1c2cs1R2RB2FA4SBlo3ERI3MF03FAS1u2pw3ABv3CHIS1n2SB2RI1c1R2RSS1n2mu1c2cs2pw3OFFS3hAR3nb01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T02CR2RS3FAS1k2Y1S1TS3hAR1A1k2H12H3S3hAR1n2lo2SB2RI1c1R5LOIMG4RIhi2RSS1TS3hAR3nb01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MU03MF02CR2RS3FAS1k2Y12Y22Y3S1n2SB2RI2mu3mfa1c2RB2FA2nf3js04LJS03FASS3hAR1n1T2SB2RI2mu3mfa1c2cs2RB2FA3PCR2T04SBlo3ERI4RIhi3MF02CR3FAS1u2pw3ABv3CHI4ABloS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU2T04SBlo3ERI4RIhi3MF02CR4TMOD2RS3FASS1n2SB2mu1c2cs2RB2pw3OFF1y2Hy2GES1n2SB3mfa1c2RB2FA1a2Ha2GES1x2Hx2XRS1n2SB1c2RB2pw3ABv4PGSv2P11x2O51E2W5S4cnt'3HC'4EcntSS3hAR1n1T3CTX2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T03CX02TC2CR2RS3FASS3hAR1n2SB2RI2mu3mfa1c2RB2FA2au4SBlo3FAS1A2H1S1n2SB2RI1c2cs2RB2pw3ABv4ABloS1TS1n2SB2RI1c1R2RSS1n2SB2RI2mu3mfa1c2RB2FA2UA4SBlo3MU03FAS1i2HiS3hAR3nb01n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP13MF02CR2RS3FAS1k2Y12Y2SS3hAR1n2SB2mu1c2cs2RB2FA2UA2pw3ABv1i2HiS3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2au2fa3js02ds2bs3LDS2HL3MU03MF02ws4HL303ds'2pw4LDS'3ABvS3hAR1n3CTX2SB2RI2mu3mfa1c2cs2RB2FA3CX04SBlo3CSR3FAS1u2pw3ABv4RZSB3NFB3MNF3CHI4ABlo1A1k2H1S1n2SB1c2cs2RB2pw3ABv1A1k2H3S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU2T04SBlo3ERI4RIhi3MF02CR4TMOD2RS3FASS3hAR2SP1n2lo1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR5LOIMG2au4RIhi3MF03FASS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU4SBlo3FAS3ERIS3CTXS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3ERI3MF03FASS3hAR1n2SB2RI2mu3mfa1c2cs2RB2FA2UA3FAS1u2pw3ABv3CHI4ABlo1i2HiS3hAR1n2SB2RI2mu3mfa1c2cs2RB2FA2UA3FAS1u2pw3ABv4RZSB3NFB3CHI4ABlo1i2Hi2O2S3hAR1T2T0S1A2sz1x2O62O72XRS3hAR2SP1n2lo1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR5LOIMG3SPL4RIhi3FAS1A1k1H4SBloS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2T04SBlo3ERI4SEP12CR2RS3FAS1A1k2H12H2S3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au3HAU3FAS1A1k2H24SBloS1n2SB2RI1c2cs2RB2FA2pw3ABv4ABloS1T2T01i2HiS3hAR1n2lo2SB2RI1c1R5LOIMG4RIhi2RSS3hAR1n1T2SB2RI2mu3mfa1c1R2RB2FA2UA3FAA3PCR2au4SBlo3ERI3MF03FASS1n2SB2mu1c2cs2RB2pw3OFF1y2Hy2GES3hAR2SP1n1T2SB2RI2mu3mfa1c2cs1R2RB2FA2UA3FAA3PCR3STK3SPA2au2fa3js02ds2bs3LDS2HL3MU03MF02ws4HL303ds'2pw4LDS'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". (* [comment removed for export] *)
  #[using="AL IMG ALWF ASB CSOKf KL CSf_noshadow CSmono_u CSmono_f CSmono_n CSmono_s STK SPA NB FP LOIMG SPL SPA16 TOP0 TOP1 TOP2 TIDB LOB TOPUB GSB GT GCTX GSEP GMU GMFA LEDGER_U TU_commit TU_fresh LEDGER_F TF_commit TF_fresh ROOM_U SCAR_U ROOM_F SCAR_F CSUz CSFz K_apart T_node T_store ROOM_n ROOM_s"] Theorem malloc_prim_init_split : ltac2:(CDefT.buildp (gd_tbl_AW_MallocGenSplit ()) "PTA,$8:.PTB,$8:.Pra,(0.&40.)Pgp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pcstw,(0.&40.)Pstw,(0.&40.)Pj0,(0.&40.)Pj1,(0.&40.)Pj2,(0.&40.)Pj1',(0.&40.)Pj2',(0.&40.)Pj3',(0.&40.)Pe0,(0.&40.)Pexb,(0.&8.)Poomb,(0.&8.)PF,(79.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))Pmo,$2:.PN,$2.Ptf,$2.Pau,$2.Pnf,$2.PcntF,P,$2.(0.&40.)PmxF,P,$2.(0.&40.)PcsxF,P,$2.(0.&40.)Prest,P,$2.(3.$42.)Pfa,(3.(0.&40.))Pjs0,(3.(0.&40.))Pds,(3.(0.&40.))Pbs,(3.(0.&40.))PshU,(3.(0.&8.))PshF,(3.(0.&8.))Ptb,(3.(0.&8.))P,(7:.$21.R11.VLO,VTOPU,(39.&40.R35.)VSP,Vd,)P,(7;.R12.VT,VCTX,)P,(1<.R13.VT,VCTX,)P,(26.R14.)P,(1>.R15.)P,(27.R16.VCTX,VT,)P,(28.R17.)P,(29.R18.VSB,)P,(25.R19.)P,(7<.$21.R1:.$84.(12.$42.(56.(30.&40.$85.))(15.$42.)))P,(7<.$21.R1;.$86.(12.$42.(46.(30.&8.+1.))(15.$42.)))P,(7<.$21.R1<.(6.$72.+20.)(12.$42.(56.(30.&40.VSB,))(15.$42.)))P,(7<.$21.R1=.(6.$72.+30.)(12.$42.(56.(30.&40.VRI,))(15.$42.)))P,(41.$21.R1>.$22.(12.$42.(46.R21.)(15.$42.)))P,(7<.$21.R1?.$80.(12.$42.(46.(30.&8.+1.))(15.$42.)))P,(41.$21.R20.$23.(12.$42.(5:.R25.)(15.$42.)))P,(7<.$21.R21.(6.VT,+8.)(12.$42.(56.(30.&40.VTOP,))(12.$42.(56.(30.&40.(47.VTOP,(7.+2.+17.))))(15.$42.))))P,(7<.$21.R22.(6.VT,+28.)(12.$42.(46.(30.&8.=))(15.$42.)))P,(41.$21.R23.(6.VT,+<60.)(12.$42.(46.(30.&8.=))(15.$42.)))P,(7<.$21.R24.VT,(12.$42.(56.(30.&40.VCTX,))(15.$42.)))P,(7<.$21.R25.(6.VCTX,+8.)(12.$42.(5:.(30.&40.VTID,))(15.$42.)))P,(16.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,VT,+1000.)P,(16.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,VCTX,+10000.)P,(16.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,VRI,+1000.)P,(19.$63.(>.(0.&40.)R1=.)#10.)P,Pj,$2.(19.$63.(93.A1.R22.R1.)#40.)P,Pj,$2.P,(;.(5.+1.R1.)(5.R1.+1?.))(94.R2=.VT,R27.R26.R25.R24.R2.)P,(19.(0.&40.)A1.R26.Vc,(30.&40.=))P,(19.(0.&40.)A1.R26.Vc,(30.&40.=))P,(19.(3.$42.)A1.R25.Vc,(12.$42.(43.#40.(95.R22.))(15.$42.)))P,(41.$21.R2?.(6.VT,+:>0.)(12.$42.(56.R3<.)(15.$42.)))P,(41.$21.R30.(6.VT,+:?0.)(12.$42.(56.R3;.)(12.$42.(56.R3:.)(12.$42.(56.R39.)(15.$42.)))))P,(5<.$21.R31.(6.VT,+;60.)R24.)P,(19.$63.(>.(0.&40.)R25.)#20.)P,(41.$21.R33.(6.VT,+;38.)(12.$42.(56.R3;.)(12.$42.(56.R3:.)(15.$42.))))P,(41.$21.R34.(6.VT,+:>8.)(12.$42.(56.R3:.)(15.$42.)))P,(;.(5.=R31.)(5.R31.Vmu,))P,(5.(47.Vmu,R32.)(7.+2.+13.))P,(19.$2.(3=.R33.+10.)=)P,(5.=R33.)P,(5.(3?.+4.R34.)Vmfa,)P,(5.(6.(3?.+4.(6.R35.(7.+2.+>.)))(7.+2.+12.))(7.+2.+1=.))P,(19.$2.(=.(>.(0.&40.)R31.))R36.)P,(19.$2.(3?.+4.(6.R37.(=.(>.(0.&40.)R31.))))Vmfa,)P,(16.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,VFA,Vmfa,)P,(16.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,VRB,Vmu,)P,(41.$21.R3?.VR,(12.$42.(56.(30.&40.=))(15.$42.)))P,(41.$21.R40.(6.VR,+10.)(12.$42.(56.(30.&40.R3;.))(15.$42.)))P,(41.$21.R41.(6.VR,+18.)(12.$42.(56.(30.&40.Vmfa,))(15.$42.)))P,(41.$21.R42.(6.VR,+20.)(12.$42.(56.(30.&40.R3>.))(15.$42.)))P,(41.$21.R43.(6.VR,+28.)(12.$42.(56.(30.&40.=))(15.$42.)))P,(41.$21.R44.(6.VR,+30.)(12.$42.(56.(30.&40.Vmu,))(15.$42.)))P,(41.$21.R45.(6.VR,+38.)(12.$42.(56.(30.&40.=))(15.$42.)))P,(41.$21.R46.(6.VR,+44.)(12.$42.(46.R4:.)(15.$42.)))P,(41.$21.R47.(6.VR,+48.)(12.$42.(56.R53.)(15.$42.)))P,(41.$21.R48.(6.+7???8000.(45.VUA,+8.))(12.$42.(43.(44.+8000.)R3:.)(15.$42.)))P,(41.$21.R49.(6.+7???8000.(45.VFAA,+8.))(12.$42.(43.(44.+8000.)R3:.)(15.$42.)))P,(5;.$21.R4:.VFA,R40.)P,(5;.$21.R4;.(6.VFA,(3?.+4.R46.))R40.)P,(69.(0.&40.)(89.R4<.R48.)R42.)P,(41.$21.R4=.(6.VRB,R49.)(12.$42.(43.(44.(47.Vmu,R49.))R3=.)(15.$42.)))P,(41.$21.R4>.(6.+7???8000.(45.(6.VRB,R4:.)+8.))(12.$42.(43.(44.(45.(47.Vmu,R4:.)+8.))(57.(0.&8.)(30.&8.+?:.)(44.(45.(47.Vmu,R4:.)+8.))))(15.$42.)))P,(8<.R4?.)P,(1?.VhAR,R50.R4>.Vnb0,R4=.Vbl0,)P,(68.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,Vnb0,Vbl0,)P,(5.(6.R4?.+80.)(7.+2.+20.))P,(5.(6.R51.+2.)(47.(7.+2.+1?.)(7.+2.+1<.)))P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vnb0,))))(8.(5.(6.VT,+1000.)(?.Vnb0,R2.))(5.(6.(?.Vnb0,R2.)(7.+2.+14.))VT,))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vbl0,))))(8.(5.(6.VT,+1000.)(10.Vbl0,R2.))(5.(6.(10.Vbl0,R2.)(7.+2.+17.))VT,))P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vnb0,))))(8.(5.(6.VCTX,+10000.)(?.Vnb0,R2.))(5.(6.(?.Vnb0,R2.)(7.+2.+14.))VCTX,))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vbl0,))))(8.(5.(6.VCTX,+10000.)(10.Vbl0,R2.))(5.(6.(10.Vbl0,R2.)(7.+2.+17.))VCTX,))P,Pk,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vnb0,))))(8.(5.(6.VRI,+1000.)(?.Vnb0,R2.))(5.(6.(?.Vnb0,R2.)(7.+2.+14.))VSB,))P,Pj,$2.P,(;.(5.=R1.)(<.R1.(=.(>.$2.Vbl0,))))(8.(5.(6.VRI,+1000.)(10.Vbl0,R2.))(5.(6.(10.Vbl0,R2.)(7.+2.+17.))VSB,))P,(55.$21.R5:.VSP,VTOP,)P,(16.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,VSP,(47.VTOP,VSP,))P,(55.$21.R5<.Vlo,VSP,)P,(16.A4.VCSf,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,Vlo,(47.VSP,Vlo,))P,(54.$21.R5>.)P,A5.VK,(2;.$2<.)(2;.$2<.)Vnb0,Vbl0,R5>.P,(53.R60.R5?.)P,Pu,(1.$2<.)Pf,(1.$2<.)A4.VGn,R2.R1.Vnb0,Vbl0,P,Pu,(1.$2<.)Pf,(1.$2<.)A4.VGs,R2.R1.Vnb0,Vbl0,P,Pu,(1.$2<.)Pf,(1.$2<.)Px,$2.A4.VGs,R3.R2.(18.$2.Vnb0,(12.$2.R1.(15.$2.)))Vbl0,P,(<.R5?.(45.(4<.Vc,)+2.))P,(<.Vmu,(6.R61.(3?.Vcs,(47.(45.(4<.Vc,)+2.)R60.))))P,(5.(6.Vmu,(7.+2.+12.))+>0000000.)P,A1.R92.(15.$8=.)P,A1.R92.(15.$8=.)P,Pcf,$49.P,(8>.R93.R92.R8>.R8=.R85.R84.R83.R82.R81.R80.R7?.R7>.R7=.R7<.R6<.R6;.R68.R67.R66.R65.=R6>.(30.&40.Vcs,)R75.R74.R73.R60.R5?.R5>.R5=.R5<.R5;.R6=.R6?.(12.(13.$2.$2.)(14.$2.$2.(6.VT,+120.)(6.VT,+:=0.))(15.(13.$2.$2.)))Lmm,P,(0.&40.)(1.(0.&8.))Pj,$2.P,(;.(5.+1.R1.)(5.R1.+1?.))P,(17.(19.$2.R2.Vc,))(96.R4.VT,R68.R65.R3.)R6:.R1.)(90.$21.R2.R96.)P,Pcf,$49.P,(91.R94.R93.R8?.R8>.R86.R85.R84.R83.R82.R81.R80.R7?.R7>.R7=.R6=.R6<.R69.R68.R67.R66.=R6?.(30.&40.Vcs,)R76.R75.R74.R61.R60.R5?.R5>.R5=.R5<.R6>.R70.(12.(13.$2.$2.)(14.$2.$2.(6.VT,+120.)(6.VT,+:=0.))(15.(13.$2.$2.)))Lmm,P,(0.&40.)(1.(0.&8.))Pj,$2.P,(;.(5.+1.R1.)(5.R1.+1?.))P,(17.(19.$2.R2.Vc,))(96.R4.VT,R69.R66.R3.)R6;.R1.)(90.$21.R2.R96.)(90.$21.(4=.(4>.(4?.R94.(30.&40.VSP,)R93.(30.&40.$50.)R92.R91.R90.R8?.R8>.(30.&40.Vn,)R8=.R8<.R8;.R8:.R89.R88.R87.R86.R85.R84.R83.R82.R81.R80.R7?.R7>.R7=.R7<.R7;.R7:.R79.)R6=.(30.&40.$7?.)R6<.(2;.(0.&40.))R6;.(52.$21.))R6:.)(92.R96.R95.))")
(* [comment removed for export] *).
  Proof.
    intros TA TB ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 cstw stw j0 j1 j2 j1' j2' j3' e0 exb oomb F fc m mo
      N tf au nf cntF mxF csxF rest fa js0 ds bs shU shF tb
      UWC MS8 AS PS FS TS MWS PPS DST GOTFL PPART SBC RIC OOM MRN ERR THR TSW UNW TH TIDC TCS CTXCS RICS
      LDS REST PCS CNT0 MX0 RESTC STC STH STB HL TJ SJ
      HAU HINV AUAL HNF HNF2 HNF3 LFA LJS0 CSFA CSRB MX NF MFA AU M40 MUC M56 EX STW SHU SHF HFAR HJS
      POOLF TAIL TAILSH HSH DI DCS TFMAX NB2 APTn APTs APCn APCs APSn APSs
      STT STCS ST SCS MI HK HJ GN GS GSX GMISS NEEDU UOK A0n B0n HNUL HCHK.
    facts. dpose GT as (T0 & T1 & TAL). pose proof GCTX as (CX0 & CX1). dpose GSB as (SBlo & SBAL & ERI & RIhi). dpose GSEP as (SEP1 & TC & SEP3).
    dpose GMU as (MU0 & MUAL & MUH). dpose GMFA as (MF0 & MFAL & MF1).
    pose proof c_range as CR. pose proof needed2_prim as [N2E NDB]. pose proof cs_range as CSR. pose proof cs_mod16 as CS16.
    assert (SPH : SP <= 2^62) by (clear - TOP1 TOP2; lia). assert (RBE : RB = SB + c * 2^32) by reflexivity. assert (FAE : FA = RB + 0xE0000000) by reflexivity.
    assert (UAE : UA = RB + mu) by reflexivity. assert (FAAE : FAA = FA + mfa) by reflexivity. assert (PCRE : PCR = T + 208 + 80 * c) by reflexivity. assert (RE : R = RI + 128 * c) by reflexivity.
    pose proof (Z.mod_pos_bound (mu - au) 8 ltac:(clear; lia)) as TMOD. pose proof (Z.div_mod (mu - au) 8 ltac:(clear; lia)) as TDIV.
    (* [comment removed for export] *)
    eapply (evtA_srzJ_KJ AL (CSf None None nb0 bl0) (K None None nb0 bl0) _ _ _ mo (KL None None nb0 bl0) HK); [exact HJ| |].
    { eapply (mseg_head (CSf None None nb0 bl0) (CSOKf None None nb0 bl0));
        first [sassumption | cassumption | exact UWC| exact MS8| exact AS| exact THR| exact TSW| exact UNW| exact TCS| exact CTXCS| exact STT| exact STCS| exact ST| exact SCS| exact MI]. }
    cbn beta. intros ms1 mo1 PO HK1 MM1 HJ1. unfold head_post in PO.
    ddestruct PO as (tq0 & tq1 & tq2 & y14 & y15 & y16 & y17 & tq3 & tq4 & tq5 & tq6 & m1 & ws & size & fr0 & fr1 & fr2 & -> &
                    MU1 & WM1 & MI1 & FR7 & STKC & HTR & HL30 & SZB & SZD & F1800 & TFBP & F8 & FR16 & UNW1 & AFR & ST1 & SR1).
    assert (DJ1 : forall A k, A + k <= lo -> (A + k <= T + 3168 \/ T + 3169 <= A) -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k)
      by (intros A k H1 H2; cbn [disjoint_from]; clear - H1 H2; lia).
    assert (LOW1 : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k) by (intros A k H; apply DJ1; clear - H LOIMG T0; lia).
    (* [comment removed for export] *)
    assert (SLAB1 : forall A k, SB <= A -> A + k <= RI + 4096 -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k)
      by (intros A k H1 H2; apply DJ1; clear - H1 H2 LOIMG RIhi ERI SEP1; lia).
    assert (SHD1 : forall A k, 0x7fff8000 <= A -> A + k <= 0x10007fff8000 -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k)
      by (intros A k H1 H2; apply DJ1; clear - H1 H2 LOIMG T0; lia).
    assert (TLO1 : forall A k, T <= A -> A + k <= T + 3168 -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k)
      by (intros A k H1 H2; apply DJ1; clear - H1 H2 LOIMG T1; lia).
    Ltac ti1 H MU WM DJ tac := eapply rw_cells_transport; [exact H| exact MU| exact WM| apply DJ; cbn [cells_size csize Nat.add length map]; tac].
    assert (PCS1 : forall j, 1 <= j <= 31 -> pc_old m1 T cntF mxF csxF rest j).
    { intros j Hj. unfold pc_old. ti1 (PCS j Hj) MU1 WM1 TLO1 ltac:(rewrite ?cells_size_app, ?REST; cbn [cells_size csize Nat.add]; clear - Hj; lia). }
    assert (STC1 : rw_cells asegs m1 (T + 2784) [C8 cstw]) by (ti1 STC MU1 WM1 TLO1 ltac:(clear; lia)).
    assert (STH1 : rw_cells asegs m1 (T + 2800) [C8 j0; C8 j1; C8 j2]) by (ti1 STH MU1 WM1 TLO1 ltac:(clear; lia)).
    assert (STB1 : u64arr asegs m1 (T + 2912) bs) by (eapply u64arr_transport; [exact STB| exact MU1| exact WM1| apply TLO1; rewrite ?HL; clear; lia]).
    assert (TJ1 : rw_cells asegs m1 (T + 2872) [C8 j1'; C8 j2']) by (ti1 TJ MU1 WM1 TLO1 ltac:(clear; lia)).
    assert (SJ1 : rw_cells asegs m1 (T + 2792) [C8 j3']) by (ti1 SJ MU1 WM1 TLO1 ltac:(clear; lia)).
    assert (RS : SB <= R /\ R + 128 <= RI + 4096) by (clear - CR ERI RE; lia).
    assert (MX1 : rw_cells asegs m1 R [C8 (Z_to_bv 64 0)]) by (ti1 MX MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (NF1 : rw_cells asegs m1 (R + 16) [C8 (Z_to_bv 64 nf)]) by (ti1 NF MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (MFA1 : rw_cells asegs m1 (R + 24) [C8 (Z_to_bv 64 mfa)]) by (ti1 MFA MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (AU1 : rw_cells asegs m1 (R + 32) [C8 (Z_to_bv 64 au)]) by (ti1 AU MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (M401 : rw_cells asegs m1 (R + 40) [C8 (Z_to_bv 64 0)]) by (ti1 M40 MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (MUC1 : rw_cells asegs m1 (R + 48) [C8 (Z_to_bv 64 mu)]) by (ti1 MUC MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (M561 : rw_cells asegs m1 (R + 56) [C8 (Z_to_bv 64 0)]) by (ti1 M56 MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (EX1 : rw_cells asegs m1 (R + 68) [C1 exb]) by (ti1 EX MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (STW1 : rw_cells asegs m1 (R + 72) [C8 stw]) by (ti1 STW MU1 WM1 SLAB1 ltac:(clear - RS; lia)).
    assert (FAS : SB <= RB /\ FA + mfa + 2^18 <= RI /\ RB + mu <= FA) by (clear - CR ERI MU0 MUH MF0 MF1 RBE FAE; lia).
    assert (SHU1 : rw_cells asegs m1 (0x7fff8000 + UA / 8) [CB (Z.to_nat 32768) shU]).
    { ti1 SHU MU1 WM1 SHD1 ltac:(clear - FAS SBlo RIhi MU0 MF0 UAE; lia). }
    assert (SHF1 : rw_cells asegs m1 (0x7fff8000 + FAA / 8) [CB (Z.to_nat 32768) shF]).
    { ti1 SHF MU1 WM1 SHD1 ltac:(clear - FAS SBlo RIhi MU0 MF0 FAAE FAE; lia). }
    assert (HFAR1 : u32arr asegs m1 FA fa) by (eapply u32arr_transport; [exact HFAR| exact MU1| exact WM1| apply SLAB1; rewrite ?LFA; clear - FAS HNF HNF2 MF0 MU0; lia]).
    assert (HJS1 : u32arr asegs m1 (FA + 4 * nf) js0) by (eapply u32arr_transport; [exact HJS| exact MU1| exact WM1| apply SLAB1; clear - FAS HNF LJS0 MF0 MU0; lia]).
    assert (PS1 : poison_statics m1) by (eapply (poison_statics_transport _ m m1 PS MU1); intros A k H; apply LOW1; clear - H; lia).
    assert (TS1 : thr_statics m1 CTX T).
    { eapply (thr_statics_transport _ m m1 CTX T TS MU1); [apply LOW1; unfold A_TSD_INITED; clear; lia| apply LOW1; unfold A_TSD_PTR; clear; lia| apply LOW1; unfold A_TSD_ARR; clear; lia|].
      apply DJ1; clear - CX1 LOIMG TC; lia. }
    assert (MWS1 : mwc_statics m1) by (eapply (mwc_statics_transport _ m m1 MWS MU1); intros A k H; apply LOW1; clear - H; lia).
    assert (PPS1 : pop_statics m1 SB) by (eapply (pop_statics_transport _ m m1 SB PPS MU1); intros A k H; apply LOW1; clear - H; lia).
    assert (RIC1 : ro_cells asegs m1 (A_INSTANCE + 48) [C8 (Z_to_bv 64 RI)]) by (eapply ro_cells_transport; [exact RIC| exact MU1| apply LOW1; unfold A_INSTANCE; cbn; clear; lia]).
    assert (POOLF1 : Forall (fchunk m1 au) fa).
    { eapply pool_transport; [exact POOLF| exact MU1| exact WM1| intros A k H1 H2; apply SLAB1; clear - H1 H2 FAS HAU MF0 MU0; lia| intros A k H1 H2; apply SHD1; clear - H1 H2 FAS HAU SBlo RIhi ERI CR RBE MF0 MU0; lia]. }
    assert (TAIL1 : rw_cells asegs m1 (RB + au) [CB (Z.to_nat (mu - au)) tb]) by (ti1 TAIL MU1 WM1 SLAB1 ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - HAU; lia); clear - FAS HAU MF0 MU0; lia)).
    assert (TAILSH1 : rw_cells asegs m1 (0x7fff8000 + (RB + au) / 8) [CB (Z.to_nat ((mu - au) / 8)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((mu - au) / 8)))]).
    { ti1 TAILSH MU1 WM1 SHD1 ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - HAU TMOD TDIV; lia); clear - FAS HAU SBlo RIhi ERI CR TMOD TDIV RBE MF0 MU0; lia). }
    pose proof (hsh_mono _ m m1 HSH MU1 WM1) as HSH1.
    assert (OOM1 : rw_cells asegs m1 A_OOM_CELL [C1 oomb]) by (ti1 OOM MU1 WM1 LOW1 ltac:(unfold A_OOM_CELL; clear; lia)).
    assert (MRN1 : ro_cells asegs m1 A_MRN_CELL [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact MRN| exact MU1| apply LOW1; unfold A_MRN_CELL; cbn; clear; lia]).
    assert (ERR1 : rw_cells asegs m1 A_ERRNO [C4 e0]) by (ti1 ERR MU1 WM1 LOW1 ltac:(unfold A_ERRNO; clear; lia)).
    dpose (proj1 (proj2 (proj2 DI))) as (_ & DMF & _).
    dpose (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DI)))))))) as (_ & DBF & _).
    assert (DI1 : depot_inv m1 N nb0 tf bl0).
    { eapply (depot_inv_transport _ m m1 N nb0 tf bl0 DI MU1 WM1 LOW1).
      - intros k Hk. pose proof (APTn k Hk) as Y.
        dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb0) DMF (Z.to_nat k) 0 ltac:(clear - Hk; lia)) as (_ & X & _).
        unfold dblk in *. apply DJ1; clear - X Y LOIMG; lia.
      - intros j Hj. pose proof (APTs j Hj) as Y.
        dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl0) DBF (Z.to_nat j) 0 ltac:(clear - Hj; lia)) as (_ & X & _).
        unfold sblk in *. apply DJ1; clear - X Y LOIMG; lia. }
    assert (DST1 : depot_statics m1) by (eapply (depot_statics_transport _ m m1 DST MU1); intros A k H; apply LOW1; clear - H; lia).
    assert (AS1 : allocA_statics m1 T CTX).
    { eapply (allocA_statics_transport _ m m1 T CTX AS MU1); [intros A k H; apply LOW1; exact H| apply DJ1; clear - CX1 LOIMG TC; lia]. }
    assert (FS1 : fin_statics m1) by (eapply (fin_statics_transport _ m m1 FS MU1); intros A k H; apply LOW1; exact H).
    assert (GOTFL1 : ro_cells asegs m1 A_GOT_FLAGS [C8 (Z_to_bv 64 A_FLAGS)]) by (eapply ro_cells_transport; [exact GOTFL| exact MU1| apply LOW1; unfold A_GOT_FLAGS; cbn; clear; lia]).
    assert (PPART1 : ro_cells asegs m1 A_FL_PPART [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact PPART| exact MU1| apply LOW1; unfold A_FL_PPART; cbn; clear; lia]).
    assert (TH1 : ro_cells asegs m1 T [C8 (Z_to_bv 64 CTX)]) by (eapply ro_cells_transport; [exact TH| exact MU1| apply TLO1; cbn; clear; lia]).
    assert (TIDC1 : ro_cells asegs m1 (CTX + 8) [C4 (Z_to_bv 64 TID)]) by (eapply ro_cells_transport; [exact TIDC| exact MU1| apply DJ1; cbn; clear - CX1 LOIMG TC; lia]).
    clear PCS STC STH STB TJ SJ MX NF MFA AU M40 MUC M56 EX STW SHU SHF HFAR HJS PS TS MWS PPS RIC POOLF TAIL TAILSH HSH OOM MRN ERR DST AS FS GOTFL PPART TH TIDC MS8 THR TSW UNW STT.
    (* [comment removed for export] *)
    assert (CST' : forall u f, crange (CSf u f nb0 bl0) T 4096) by (intros u f y Hy; apply CSinc0; apply TCS; exact Hy).
    assert (CSCTX' : forall u f, crange (CSf u f nb0 bl0) CTX 0x10000) by (intros u f y Hy; apply CSinc0; apply CTXCS; exact Hy).
    assert (CSRI' : forall u f, crange (CSf u f nb0 bl0) RI 4096) by (intros u f y Hy; apply CSinc0; apply RICS; exact Hy).
    assert (SPAAL2 : (SPA + -128) mod 16 = 0).
    { subst SPA STK. clear - SPA16. apply Z.mod_divide in SPA16; [| lia]. apply Z.mod_divide; [lia|]. destruct SPA16 as [q Hq]. exists (q - 142). lia. }
    eapply (combined_split_init AL IMG ALWF (fun u f => CSf u f nb0 bl0) (fun u f => CSOKf u f nb0 bl0) CSmono_u CSmono_f ASB T CTX SB RI c GSB c_range GT GCTX GSEP
              CST' CSCTX' CSRI' (fun u f => K u f nb0 bl0) (fun u f => KL u f nb0 bl0) mu mfa LEDGER_U TU_commit TU_fresh LEDGER_F TF_commit TF_fresh GMU GMFA CSUz CSFz ROOM_U SCAR_U ROOM_F SCAR_F TA TB)
      with (lo := lo) (x := needed2 n) (au := au) (nf := nf) (cnt := cntF) (mx := mxF) (csx := csxF) (rest := rest) (fa := fa) (js0 := js0) (ds := ds) (shU := shU) (shF := shF) (exb := exb) (cstw := cstw) (stw := stw) (j1 := j1') (j2 := j2') (j3 := j3').
    all: lazymatch goal with
         | |- forall j, cells_size _ = _ => exact REST
         | |- forall j, 1 <= j <= 31 -> pc_old _ _ _ _ _ _ j => exact PCS1
         | |- forall ok c', _ => idtac
         | |- 1 <= needed2 n <= 0x10000 => clear - N2E NDB; lia
         | |- class_of _ = c => reflexivity
         | |- _ c = Z_to_bv 64 0 => first [exact CNT0| exact MX0]
         | |- _ c = [CB _ _] => exact RESTC
         | |- rw_cells _ _ (T + 2784) _ => exact STC1
         | |- rw_cells _ _ (RI + 128 * c) _ => exact MX1
         | |- rw_cells _ _ (RI + 128 * c + 16) _ => exact NF1
         | |- rw_cells _ _ (RI + 128 * c + 24) _ => exact MFA1
         | |- rw_cells _ _ (RI + 128 * c + 32) _ => exact AU1
         | |- rw_cells _ _ (RI + 128 * c + 40) _ => exact M401
         | |- rw_cells _ _ (RI + 128 * c + 48) _ => exact MUC1
         | |- rw_cells _ _ (RI + 128 * c + 56) _ => exact M561
         | |- rw_cells _ _ (RI + 128 * c + 68) _ => exact EX1
         | |- rw_cells _ _ (RI + 128 * c + 72) _ => exact STW1
         | |- rw_cells _ _ (T + 2872) _ => exact TJ1
         | |- rw_cells _ _ (T + 2792) _ => exact SJ1
         | |- rw_cells _ _ (0x7fff8000 + (SB + c * 2^32 + mu) / 8) _ => exact SHU1
         | |- rw_cells _ _ (0x7fff8000 + (SB + c * 2^32 + 0xE0000000 + mfa) / 8) _ => exact SHF1
         | |- u32arr _ _ (SB + c * 2^32 + 0xE0000000) _ => exact HFAR1
         | |- u32arr _ _ (SB + c * 2^32 + 0xE0000000 + 4 * _) _ => exact HJS1
         | |- poison_statics _ => exact PS1
         | |- thr_statics _ _ _ => exact TS1
         | |- mwc_statics _ => exact MWS1
         | |- pop_statics _ _ => exact PPS1
         | |- ro_cells _ _ (A_INSTANCE + 48) _ => exact RIC1
         | |- stk _ _ _ _ => exact ST1
         | |- crange _ (SB + c * 2^32 + 0xE0000000) _ => exact CSFA
         | |- crange _ lo _ => eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear; lia| subst SPA STK; clear; lia]
         | |- mem_inv _ _ => exact MI1
         | |- K _ _ _ _ _ => exact HK1
         | |- J _ _ => cbn [ms_mem MS MSsvc] in HJ1; exact HJ1
         | |- _ = Z_to_bv 64 A_TP => reflexivity
         | |- (SPA + -128) mod 16 = 0 => exact SPAAL2
         | |- _ => first [sassumption | cassumption | exact GMISS| exact NEEDU| exact UOK| assumption| exact HAU| exact HINV| exact AUAL| exact HNF| exact HNF2| exact HNF3| exact LFA| exact LJS0| exact LDS| exact LOIMG
                         | (subst SPA STK; clear - SPL; lia) | (subst SPA STK; clear - SPH; lia) ]
         end.
    all: lazymatch goal with |- forall ok c', _ => idtac | |- ?G => fail "combined premise" G end.
    (* [comment removed for export] *)
    intros ok cf PO. unfold comb_cpostS in PO.
    ddestruct PO as (ms2 & mo2 & AB & u & f & v0 & v1 & v2 & va1 & va2 & va3 & va4 & va5 & va6 & va7 & v3 & v4 & v5 & v6 & mm & k1 & k2 & k3 & stw' & cstw' & -> & -> &
                    MU2 & WM2 & MI2 & ST2 & HK2 & HJ2 & MUB2 & PS2 & TS2 & MWS2 & PPS2 & RIC2 & MX2 & MFA2 & M402 & MUC2 & M562 & STW2 & STC2 & TJ2 & SJ2 & USH & USHn & FSH & FSHn & PCN2 & ARM).
    replace (ret_pc (Z_to_bv 64 0x47d34)) with (Z_to_bv 64 0x47d34) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    (* [comment removed for export] *)
    assert (DJ2 : forall A k, SPA + -128 <= A -> disjoint_from
              ((lo, SPA + -128) :: (UA, UA + 2^18) :: (0x7fff8000 + UA / 8, 0x7fff8000 + UA / 8 + 32768) :: (FA, FAA + 2^18) :: (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)
               :: (T + 2872, T + 2888) :: (T + 2792, T + 2800) :: (T + 2784, T + 2792) :: (R, R + 8) :: (R + 16, R + 24) :: (R + 24, R + 32) :: (R + 32, R + 40) :: (R + 48, R + 56)
               :: (R + 68, R + 69) :: (R + 72, R + 80) :: [(T + 288, T + 2768)]) A k).
    { intros A k H. cbn [disjoint_from app]. subst SPA STK. clear - H FAS RS RIhi LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    assert (LOW2 : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from
              ((lo, SPA + -128) :: (UA, UA + 2^18) :: (0x7fff8000 + UA / 8, 0x7fff8000 + UA / 8 + 32768) :: (FA, FAA + 2^18) :: (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)
               :: (T + 2872, T + 2888) :: (T + 2792, T + 2800) :: (T + 2784, T + 2792) :: (R, R + 8) :: (R + 16, R + 24) :: (R + 24, R + 32) :: (R + 32, R + 40) :: (R + 48, R + 56)
               :: (R + 68, R + 69) :: (R + 72, R + 80) :: [(T + 288, T + 2768)]) A k).
    { intros A k H. cbn [disjoint_from app]. subst SPA STK. clear - H FAS RS RIhi LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    Ltac ti2 H MU DJ tac := eapply rw_cells_munch; [exact H| exact MU| apply DJ; cbn [cells_size csize Nat.add length map]; tac].
    assert (AFR2 : allocA_frame mm SPA fr0 1 (Z_to_bv 64 0x47a64) (Z_to_bv 64 SP) (Z_to_bv 64 n) (Z_to_bv 64 A_PC_MALLOC) (Z_to_bv 64 1) (Z_to_bv 64 STK) (Z_to_bv 64 (SP + -81)) s6 s7 s8 s9 s10 s11).
    { unfold allocA_frame in *. ti2 AFR MU2 DJ2 ltac:(subst SPA STK; clear; lia). }
    assert (FR162 : rw_cells asegs mm (STK + -16) [C8 (Z_to_bv 64 SP); C8 (Z_to_bv 64 0x6978c)]) by (ti2 FR16 MU2 DJ2 ltac:(subst SPA STK; clear; lia)).
    assert (FR72 : rw_cells asegs mm (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (ti2 FR7 MU2 DJ2 ltac:(subst SPA STK; clear; lia)).
    assert (STKC2 : rw_cells asegs mm STK [C8 (Z_to_bv 64 (STK + 16)); C8 (Z_to_bv 64 size)]) by (ti2 STKC MU2 DJ2 ltac:(subst SPA STK; clear; lia)).
    assert (HTR2 : u64arr asegs mm (STK + 16) ws) by (eapply u64arr_munch; [exact HTR| exact MU2| apply DJ2; subst SPA STK; clear; lia]).
    assert (F18002 : rw_cells asegs mm (STK + 256) [CB 1800 fr1]) by (ti2 F1800 MU2 DJ2 ltac:(subst SPA STK; clear; lia)).
    assert (TFBP2 : rw_cells asegs mm (STK + 2056) [C8 (Z_to_bv 64 SP)]) by (ti2 TFBP MU2 DJ2 ltac:(subst SPA STK; clear; lia)).
    assert (F82 : rw_cells asegs mm (STK + 2064) [CB 8 fr2]) by (ti2 F8 MU2 DJ2 ltac:(subst SPA STK; clear; lia)).
    assert (UNW2 : rw_cells asegs mm (T + 3168) [C1 (Z_to_bv 8 0)]).
    { eapply rw_cells_munch; [exact UNW1| exact MU2|]. cbn [disjoint_from app cells_size csize Nat.add]. subst SPA STK. clear - FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    assert (OOM2 : rw_cells asegs mm A_OOM_CELL [C1 oomb]) by (ti2 OOM1 MU2 LOW2 ltac:(unfold A_OOM_CELL; clear; lia)).
    assert (MRN2 : ro_cells asegs mm A_MRN_CELL [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact MRN1| exact MU2| apply LOW2; unfold A_MRN_CELL; cbn; clear; lia]).
    assert (ERR2 : rw_cells asegs mm A_ERRNO [C4 e0]) by (ti2 ERR1 MU2 LOW2 ltac:(unfold A_ERRNO; clear; lia)).
    assert (DST2 : depot_statics mm) by (eapply (depot_statics_transport _ m1 mm DST1 MU2); intros A k H; apply LOW2; clear - H; lia).
    assert (SCSc : crange (CSf u f nb0 bl0) lo (SP - lo)) by (intros y Hy; apply CSinc0; apply SCS; exact Hy).
    assert (DJT2 : forall A k, T + 2800 <= A -> A + k <= T + 2872 \/ (T + 2888 <= A /\ A + k <= T + 3168) -> disjoint_from
              ((lo, SPA + -128) :: (UA, UA + 2^18) :: (0x7fff8000 + UA / 8, 0x7fff8000 + UA / 8 + 32768) :: (FA, FAA + 2^18) :: (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)
               :: (T + 2872, T + 2888) :: (T + 2792, T + 2800) :: (T + 2784, T + 2792) :: (R, R + 8) :: (R + 16, R + 24) :: (R + 24, R + 32) :: (R + 32, R + 40) :: (R + 48, R + 56)
               :: (R + 68, R + 69) :: (R + 72, R + 80) :: [(T + 288, T + 2768)]) A k).
    { intros A k H1 H2. cbn [disjoint_from app]. subst SPA STK. clear - H1 H2 FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    assert (STH2 : rw_cells asegs mm (T + 2800) [C8 j0; C8 j1; C8 j2]) by (eapply rw_cells_munch; [exact STH1| exact MU2| apply DJT2; cbn; clear; lia]).
    assert (STB2 : u64arr asegs mm (T + 2912) bs) by (eapply u64arr_munch; [exact STB1| exact MU2| apply DJT2; rewrite ?HL; clear; lia]).
    assert (BNS0 : forall k, 0 <= k < Z.of_nat (length nb0) -> dblk nb0 k + 2^20 <= 0x7fff8000 \/ 0x10007fff8000 <= dblk nb0 k).
    { intros k Hk. destruct DCS as [D1 _]. pose proof (D1 k Hk) as CRk.
      destruct (Z_le_gt_dec (dblk nb0 k + 2^20) 0x7fff8000) as [H1|H1]; [left; exact H1| right].
      destruct (Z_le_gt_dec 0x10007fff8000 (dblk nb0 k)) as [H2|H2]; [exact H2| exfalso].
      destruct (Z_lt_ge_dec (dblk nb0 k) 0x7fff8000) as [H3|H3].
      - apply (CSf_noshadow None None nb0 bl0 0x7fff8000); [apply CRk; clear - H1 H3; lia| clear; lia].
      - apply (CSf_noshadow None None nb0 bl0 (dblk nb0 k)); [apply CRk; clear; lia| clear - H2 H3; lia]. }
    assert (BSS0 : forall j, 0 <= j < Z.of_nat (length bl0) -> sblk bl0 j + 2^23 <= 0x7fff8000 \/ 0x10007fff8000 <= sblk bl0 j).
    { intros j Hj. destruct DCS as [_ D2]. pose proof (D2 j Hj) as CRj.
      destruct (Z_le_gt_dec (sblk bl0 j + 2^23) 0x7fff8000) as [H1|H1]; [left; exact H1| right].
      destruct (Z_le_gt_dec 0x10007fff8000 (sblk bl0 j)) as [H2|H2]; [exact H2| exfalso].
      destruct (Z_lt_ge_dec (sblk bl0 j) 0x7fff8000) as [H3|H3].
      - apply (CSf_noshadow None None nb0 bl0 0x7fff8000); [apply CRj; clear - H1 H3; lia| clear; lia].
      - apply (CSf_noshadow None None nb0 bl0 (sblk bl0 j)); [apply CRj; clear; lia| clear - H2 H3; lia]. }
    assert (DI2 : depot_inv mm N nb0 tf bl0).
    { eapply (depot_inv_transport _ m1 mm N nb0 tf bl0 DI1 MU2 WM2 LOW2).
      - intros k Hk. pose proof (APTn k Hk) as Y1. pose proof (APSn k Hk) as Y2. pose proof (BNS0 k Hk) as Y3.
        dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb0) DMF (Z.to_nat k) 0 ltac:(clear - Hk; lia)) as (_ & X & _).
        unfold dblk in *. cbn [disjoint_from app]. subst SPA STK. clear - X Y1 Y2 Y3 FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia.
      - intros j Hj. pose proof (APTs j Hj) as Y1. pose proof (APSs j Hj) as Y2. pose proof (BSS0 j Hj) as Y3.
        dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl0) DBF (Z.to_nat j) 0 ltac:(clear - Hj; lia)) as (_ & X & _).
        unfold sblk in *. cbn [disjoint_from app]. subst SPA STK. clear - X Y1 Y2 Y3 FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    destruct ok; cbv beta iota.
    2:{ (* [comment removed for export] *)
      ddestruct ARM as (EAB & Fn & CNT0' & PC2 & NF2 & AU2 & EX2 & HFAR2 & HJS2 & ARR2). subst AB.
      eapply (evtA_srzJ_KJ AL (CSf u f nb0 bl0) (K u f nb0 bl0) _ _ _ mo2 (KL u f nb0 bl0) HK2); [exact HJ2| |].
      { eapply (mseg_null (CSf u f nb0 bl0) (CSOKf u f nb0 bl0)) with (m0 := mm) (W := []);
          first [exact AFR2| exact OOM2| exact MRN2| exact ERR2| exact FR162| exact FR72| exact STKC2| exact HTR2| exact HL30| exact F18002| exact TFBP2| exact F82| exact ST2| exact SCSc
                | apply munch_refl| apply wmono_refl| exact MI2]. }
      cbn beta. (intros ms3 mo3 dd_H; ddestruct dd_H as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m3 & -> & MU3 & WM3 & MI3 & OOM3 & ERR3 & ST3); intros HK3 MM3 HJ3).
      apply HNUL. unfold mgen_postN.
      eexists. dexists mo3, 0, u, f, nb0, bl0. dexists y0, y1, y2, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6. dexists stw', cstw', k1, k2, k3, m3.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HK3|]. split; [exact HJ3|]. split; [exact MUB2|].
      split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3))|]. split; [exact MI3|]. split; [exact ST3|].
      split; [intros y Hy; apply CSinc0; exact Hy|].
      assert (OE : oe_ok [(lo, SP); (A_OOM_CELL, A_OOM_CELL + 1); (A_ERRNO, A_ERRNO + 4)]).
      { intros A k H1 H2 H3. cbn [disjoint_from]. clear - H1 H2 H3 LOIMG. repeat split; lia. }
      assert (DJ3 : forall A k, (A + k <= 0x10000 \/ 0x65f000 <= A) -> A + k <= lo -> disjoint_from [(lo, SP); (A_OOM_CELL, A_OOM_CELL + 1); (A_ERRNO, A_ERRNO + 4)] A k).   (* [comment removed for export] *)
      { intros A k H1 H2. unfold A_OOM_CELL, A_ERRNO. cbn [disjoint_from]. clear - H1 H2. repeat split; lia. }
      destruct (statics5_transport_oe _ mm m3 CTX T SB MU3 OE ltac:(apply DJ3; clear - CX0 CX1 LOIMG; lia)) as (D1 & D2 & D3 & D4 & D5).
      split; [exact (D1 DST2)|]. split; [exact (D2 PS2)|]. split; [exact (D3 TS2)|]. split; [exact (D4 MWS2)|]. split; [exact (D5 PPS2)|].
      Ltac ti3 H MU WM DJ tac := eapply rw_cells_transport; [exact H| exact MU| exact WM| apply DJ; cbn [cells_size csize Nat.add length map]; tac].
      split; [ti3 MX2 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|].
      split; [ti3 MFA2 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|]. split; [ti3 M402 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|].
      split; [ti3 MUC2 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|]. split; [ti3 M562 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|].
      split; [ti3 STW2 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|]. split; [ti3 STC2 MU3 WM3 DJ3 ltac:(clear - T0 T1 LOIMG; lia)|].
      split; [ti3 TJ2 MU3 WM3 DJ3 ltac:(clear - T0 T1 LOIMG; lia)|]. split; [ti3 SJ2 MU3 WM3 DJ3 ltac:(clear - T0 T1 LOIMG; lia)|].
      split; [intros Hf; ti3 (FSH Hf) MU3 WM3 DJ3 ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia); clear - FAS SBlo RIhi LOIMG MU0 MF0 FAAE FAE RBE; lia)|].
      split; [intros Hf; ti3 (FSHn Hf) MU3 WM3 DJ3 ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia); clear - FAS SBlo RIhi LOIMG MU0 MF0 FAAE FAE RBE; lia)|].
      split; [intros Hu HMU; ti3 (USHn Hu HMU) MU3 WM3 DJ3 ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia); clear - FAS SBlo RIhi LOIMG MU0 MF0 UAE RBE; lia)|].
      split; [ti3 UNW2 MU3 WM3 DJ3 ltac:(clear - T0 T1 LOIMG; lia)|].
      split; [intros j Hj NEj; unfold pc_new; ti3 (PCN2 j Hj NEj) MU3 WM3 DJ3 ltac:(rewrite ?cells_size_app, ?REST; cbn [cells_size csize Nat.add]; clear - T0 T1 LOIMG Hj; lia)|].
      split; [reflexivity|]. split; [exact Fn|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split.
      { (* [comment removed for export] *)
        intros x. cbv zeta. intros HO _ _. unfold mgen_windows in HO. cbn [outside app] in HO.
        ddestruct HO as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15 & O16 & O17 & O18 & O19 & O20 & O21 & _).
        rewrite (MU3 x) by (cbn [outside]; repeat split; first [exact O1| exact O19| exact O20| exact I]).
        rewrite (MU2 x). 2:{ cbn [outside app]. subst SPA STK.
                             repeat split; first [sassumption | cassumption | exact O8| exact O9| exact O10| exact O11| exact O7| exact O5| exact O4| exact O12| exact O13| exact O14| exact O15| exact O16| exact O17| exact O18| exact O21| exact I | (clear - O1; lia)]. }
        apply (MU1 x). cbn [outside]. repeat split; first [exact O1| exact O3| exact I]. }
      split. { (* [comment removed for export] *)
        eapply (depot_inv_transport_z _ mm m3 N nb0 tf bl0 DI2 MU3 WM3).
        - intros A k H. unfold A_SS, A_DEP_END, A_OOM_CELL, A_ERRNO in *. cbn [disjoint_from]. clear - H LOIMG. repeat split; lia.
        - intros k Hk. dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb0) DMF (Z.to_nat k) 0 ltac:(clear - Hk; lia)) as (X0 & X & _).
          unfold dblk, A_OOM_CELL, A_ERRNO in *. cbn [disjoint_from]. clear - X0 X LOIMG. repeat split; lia.
        - intros j Hj. dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl0) DBF (Z.to_nat j) 0 ltac:(clear - Hj; lia)) as (X0 & X & _).
          unfold sblk, A_OOM_CELL, A_ERRNO in *. cbn [disjoint_from]. clear - X0 X LOIMG. repeat split; lia. }
      split; [ti3 PC2 MU3 WM3 DJ3 ltac:(clear - T0 T1 LOIMG CR PCRE; lia)|].
      split; [eapply u32arr_transport; [exact ARR2| exact MU3| exact WM3| apply DJ3; rewrite ?LDS; clear - T0 T1 LOIMG CR PCRE; lia]|].
      split; [ti3 NF2 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|]. split; [ti3 AU2 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|]. split; [ti3 EX2 MU3 WM3 DJ3 ltac:(clear - RS SBlo RIhi LOIMG; lia)|].
      split; [eapply u32arr_transport; [exact HFAR2| exact MU3| exact WM3| apply DJ3; rewrite ?LFA; clear - FAS SBlo RIhi LOIMG MU0 MF0 HNF HNF2 FAE RBE; lia]|].
      split; [eapply u32arr_transport; [exact HJS2| exact MU3| exact WM3| apply DJ3; clear - FAS SBlo RIhi LOIMG MU0 MF0 HNF LJS0 FAE RBE; lia]|].
      split. { intros Hu. destruct (USH Hu) as [Z1 Z2]. split.
               - ti3 Z1 MU3 WM3 DJ3 ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia); clear - FAS SBlo RIhi LOIMG MU0 MF0 UAE RBE; lia).
               - ti3 Z2 MU3 WM3 DJ3 ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia); clear - FAS SBlo RIhi LOIMG MU0 MF0 UAE RBE; lia). }
      split; [exact OOM3|]. split; [exact ERR3|].
      split.
      - eapply rw_cells_transport; [exact STH2| exact MU3| exact WM3| apply DJ3; cbn; clear - T0 T1 LOIMG; lia].
      - eapply u64arr_transport; [exact STB2| exact MU3| exact WM3| apply DJ3; rewrite ?HL; clear - T0 T1 LOIMG; lia].
    }
    (* [comment removed for export] *)
    ddestruct ARM as (cnt' & ds' & pw & EAB & HC' & NTH & LDS' & PC2 & ARR2 & CASES). subst AB.
    (* [comment removed for export] *)
    assert (DJP2 : forall A k, RB <= A -> A + k <= RB + au -> disjoint_from
              ((lo, SPA + -128) :: (UA, UA + 2^18) :: (0x7fff8000 + UA / 8, 0x7fff8000 + UA / 8 + 32768) :: (FA, FAA + 2^18) :: (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)
               :: (T + 2872, T + 2888) :: (T + 2792, T + 2800) :: (T + 2784, T + 2792) :: (R, R + 8) :: (R + 16, R + 24) :: (R + 24, R + 32) :: (R + 32, R + 40) :: (R + 48, R + 56)
               :: (R + 68, R + 69) :: (R + 72, R + 80) :: [(T + 288, T + 2768)]) A k).
    { intros A k H1 H2. cbn [disjoint_from app]. subst SPA STK. clear - H1 H2 HAU FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    assert (DJPS2 : forall A k, 0x7fff8000 + RB / 8 <= A -> A + k <= 0x7fff8000 + (RB + au) / 8 -> disjoint_from
              ((lo, SPA + -128) :: (UA, UA + 2^18) :: (0x7fff8000 + UA / 8, 0x7fff8000 + UA / 8 + 32768) :: (FA, FAA + 2^18) :: (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)
               :: (T + 2872, T + 2888) :: (T + 2792, T + 2800) :: (T + 2784, T + 2792) :: (R, R + 8) :: (R + 16, R + 24) :: (R + 24, R + 32) :: (R + 32, R + 40) :: (R + 48, R + 56)
               :: (R + 68, R + 69) :: (R + 72, R + 80) :: [(T + 288, T + 2768)]) A k).
    { intros A k H1 H2. cbn [disjoint_from app]. subst SPA STK. clear - H1 H2 HAU FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    pose proof (pool_munch _ m1 mm au _ POOLF1 MU2 DJP2 DJPS2) as POOLF2.
    assert (TAIL2 : rw_cells asegs mm (RB + au) [CB (Z.to_nat (mu - au)) tb]).
    { eapply rw_cells_munch; [exact TAIL1| exact MU2|]. cbn [disjoint_from app cells_size csize Nat.add]. rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - HAU; lia). subst SPA STK.
      clear - HAU FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    assert (TAILSH2 : rw_cells asegs mm (0x7fff8000 + (RB + au) / 8) [CB (Z.to_nat ((mu - au) / 8)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((mu - au) / 8)))]).
    { eapply rw_cells_munch; [exact TAILSH1| exact MU2|]. cbn [disjoint_from app cells_size csize Nat.add]. rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear - HAU TMOD TDIV; lia). subst SPA STK.
      clear - HAU FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE TMOD TDIV. repeat split; lia. }
    pose proof (max_cached_fits c c_range) as [MCF1 MCF2].
    set (ABv := RB + 16 * (bv_unsigned pw mod 2^32)) in *.
    pose proof (Z.mod_pos_bound (bv_unsigned pw) (2^32) ltac:(clear; lia)) as PWR.
    (* [comment removed for export] *)
    assert (CHUNK : 16 * (bv_unsigned pw mod 2^32) + cs <= mu + unit_if u
                    /\ (exists cbs, rw_cells asegs mm ABv [CB (Z.to_nat cs) cbs])
                    /\ (exists sh0 shs, rw_cells asegs mm (0x7fff8000 + ABv / 8) [C1 sh0; CB (Z.to_nat (cs / 8 - 1)) shs] /\ bv_unsigned sh0 <> 0)).
    { destruct CASES as [(Ecnt & Eds & Eu & Ef & _) | (CNT0' & Ecnt & Un & Fn & new & ws' & fa' & rest' & nf' & au' & ex' & Eds & Efa & Lws & Lfa' & SRC & _)].
      - (* [comment removed for export] *)
        exfalso. clear - Ecnt HC'. lia.
      - (* [comment removed for export] *)
        subst cnt'. ddestruct (cpy_last (Z.to_nat (max_count c / 2)) ws' ds Lws ltac:(clear - MCF2; lia)) as (w & NW & NC).
        rewrite <- Eds in NC. replace (Z.to_nat (max_count c / 2) - 1)%nat with (Z.to_nat (max_count c / 2 - 1)) in NC by (clear - MCF2; lia).
        rewrite NTH in NC. injection NC as Epw.
        assert (EOFF : bv_unsigned pw mod 2^32 = bv_unsigned w mod 2^32) by (rewrite Epw; apply sx32_mod32).
        assert (INW : In w (fa ++ new)) by (rewrite Efa; apply in_or_app; right; eapply nth_error_In; exact NW).
        apply in_app_or in INW. destruct INW as [INF | INN].
        + destruct (proj1 (Forall_forall _ _) POOLF2 w INF) as (OFF & HB & HS). subst ABv. rewrite EOFF in *.
          split; [destruct u as [[|]|]; cbn [unit_if]; clear - OFF HAU; lia|]. split; [exact HB| exact HS].
        + destruct SRC as [(Enew & _) | (Enew & NFK & KNW & Eau' & Eex' & Un')].
          { exfalso. rewrite Enew in INN. exact INN. }
          rewrite Enew in INN. destruct (In_carve_list _ _ _ _ INN) as (i & Hi & Ew).
          destruct u as [[|]|]; [| exfalso; exact (Un eq_refl)|]; cbn [unit_if] in Hi, KNW |- *; fold cs in Hi, KNW, Ew, Eau' |- *.
          { (* [comment removed for export] *)
          set (nw := (mu + 2^18 - au) / cs) in *.
          assert (NWB : 0 <= nw /\ nw * cs <= mu + 2^18 - au).
          { subst nw. pose proof (Z.div_pos (mu + 2^18 - au) cs ltac:(clear - HAU; lia) ltac:(clear - CSR; lia)). pose proof (Z.mul_div_le (mu + 2^18 - au) cs ltac:(clear - CSR; lia)). clear - H H0. lia. }
          assert (OFFE : 16 * (bv_unsigned pw mod 2^32) = au + Z.of_nat i * cs).
          { rewrite EOFF, Ew. pose proof (Z.div_mod au 16 ltac:(lia)) as DA. rewrite AUAL, Z.add_0_r in DA. pose proof (Z.div_mod cs 16 ltac:(lia)) as DC. rewrite CS16, Z.add_0_r in DC.
            assert (E16 : (au + Z.of_nat i * cs) / 16 = au / 16 + Z.of_nat i * (cs / 16)).
            { rewrite DA at 1. rewrite DC at 1. replace (16 * (au / 16) + Z.of_nat i * (16 * (cs / 16))) with ((au / 16 + Z.of_nat i * (cs / 16)) * 16) by (clear; lia). rewrite Z.div_mul by (clear; lia). reflexivity. }
            rewrite E16. assert (BND : 0 <= au / 16 + Z.of_nat i * (cs / 16) < 2^32) by (clear - DA DC Hi NWB HAU MUH CSR; nia).
            rewrite unsigned_lit by (clear - BND; lia). rewrite Z.mod_small by exact BND. clear - DA DC; lia. }
          assert (CHB2 : Z.of_nat i * cs + cs <= nw * cs) by (clear - Hi NWB CSR; nia).
          split; [rewrite OFFE; clear - CHB2 NWB; lia|].
          destruct (USH eq_refl) as [UZ USHz].
          assert (BIG : rw_cells asegs mm (RB + au) [CB (Z.to_nat (mu - au) + Z.to_nat (2^18))%nat (tb ++ repeat (Z_to_bv 8 0) (Z.to_nat (2^18)))]).
          { apply CB_merge; [exact TAIL2|]. rewrite Z2Nat.id by (clear - HAU; lia). replace (RB + au + (mu - au)) with UA by (cbv delta [UA] in *; clear; lia). exact UZ. }
          assert (BIGSH : rw_cells asegs mm (0x7fff8000 + (RB + au) / 8) [CB (Z.to_nat ((mu - au) / 8) + Z.to_nat 32768)%nat (repeat (Z_to_bv 8 0xfa) (Z.to_nat ((mu - au) / 8) + Z.to_nat 32768)%nat)]).
          { rewrite (List.repeat_app (Z_to_bv 8 0xfa)). apply CB_merge; [exact TAILSH2|]. rewrite Z2Nat.id by (clear - HAU TMOD TDIV; lia).
            replace (0x7fff8000 + (RB + au) / 8 + (mu - au) / 8) with (0x7fff8000 + UA / 8); [exact USHz|].
            cbv delta [UA] in *. pose proof (Z.div_mod RB 4096 ltac:(lia)) as DR. rewrite RBE in DR at 1.
            clear - AUAL MUAL HAU RBE SBAL. pose proof (Z.div_mod au 16 ltac:(lia)). pose proof (Z.div_mod mu 4096 ltac:(lia)). pose proof (Z.div_mod SB 4096 ltac:(lia)). nia. }
          split.
          * exists (firstn (Z.to_nat cs) (skipn (Z.to_nat (Z.of_nat i * cs)) (tb ++ repeat (Z_to_bv 8 0) (Z.to_nat (2^18))))).
            replace ABv with (RB + au + Z.of_nat (Z.to_nat (Z.of_nat i * cs))) by (subst ABv; rewrite Z2Nat.id by (clear - CSR; nia); clear - OFFE; lia).
            apply (CB_sub asegs mm _ _ _ _ _ BIG). clear - CHB2 NWB HAU CSR; nia.
          * dexists (Z_to_bv 8 0xfa), (repeat (Z_to_bv 8 0xfa) (Z.to_nat (cs / 8 - 1))). split; [| clear; vm_compute; intros E; discriminate E].
            lazymatch type of BIGSH with rw_cells _ _ _ [CB ?nE25 _] => assert (HOKE25 : (Z.to_nat (Z.of_nat i * cs / 8) + Z.to_nat (cs / 8) <= nE25)%nat) by (clear - CHB2 NWB HAU CSR CS16 TMOD TDIV; nia) end. (* [comment removed for export] *)
            pose proof (CB_sub asegs mm _ _ _ (Z.to_nat (Z.of_nat i * cs / 8)) (Z.to_nat (cs / 8)) BIGSH HOKE25) as SUBSH.
            rewrite firstn_skipn_repeat in SUBSH by exact HOKE25. clear HOKE25.
            replace (0x7fff8000 + (RB + au) / 8 + Z.of_nat (Z.to_nat (Z.of_nat i * cs / 8))) with (0x7fff8000 + ABv / 8) in SUBSH.
            2:{ subst ABv. rewrite OFFE. rewrite Z2Nat.id by (apply Z.div_pos; clear - CSR; nia).
                clear - AUAL RBE SBAL CS16. pose proof (Z.div_mod au 16 ltac:(lia)). pose proof (Z.div_mod cs 16 ltac:(lia)). pose proof (Z.div_mod SB 4096 ltac:(lia)). nia. }
            eapply rw_cells_reshape; [exact SUBSH| cbn; rewrite repeat_length; split; [exact I| split; [reflexivity| exact I]] |].
            cbn [cells_bytes cbytes app]. rewrite !app_nil_r. replace (Z.to_nat (cs / 8)) with (S (Z.to_nat (cs / 8 - 1))) by (clear - CSR; lia). reflexivity.
          }
          { (* [comment removed for export] *)
          rewrite Z.add_0_r in Hi, KNW |- *. set (nw := (mu - au) / cs) in *.
          assert (NWB : 0 <= nw /\ nw * cs <= mu - au).
          { subst nw. pose proof (Z.div_pos (mu - au) cs ltac:(clear - HAU; lia) ltac:(clear - CSR; lia)). pose proof (Z.mul_div_le (mu - au) cs ltac:(clear - CSR; lia)). clear - H H0. lia. }
          assert (OFFE : 16 * (bv_unsigned pw mod 2^32) = au + Z.of_nat i * cs).
          { rewrite EOFF, Ew. pose proof (Z.div_mod au 16 ltac:(lia)) as DA. rewrite AUAL, Z.add_0_r in DA. pose proof (Z.div_mod cs 16 ltac:(lia)) as DC. rewrite CS16, Z.add_0_r in DC.
            assert (E16 : (au + Z.of_nat i * cs) / 16 = au / 16 + Z.of_nat i * (cs / 16)).
            { rewrite DA at 1. rewrite DC at 1. replace (16 * (au / 16) + Z.of_nat i * (16 * (cs / 16))) with ((au / 16 + Z.of_nat i * (cs / 16)) * 16) by (clear; lia). rewrite Z.div_mul by (clear; lia). reflexivity. }
            rewrite E16. assert (BND : 0 <= au / 16 + Z.of_nat i * (cs / 16) < 2^32) by (clear - DA DC Hi NWB HAU MUH CSR; nia).
            rewrite unsigned_lit by (clear - BND; lia). rewrite Z.mod_small by exact BND. clear - DA DC; lia. }
          assert (CHB2 : Z.of_nat i * cs + cs <= nw * cs) by (clear - Hi NWB CSR; nia).
          split; [rewrite OFFE; clear - CHB2 NWB; lia|].
          pose proof TAIL2 as BIG. pose proof TAILSH2 as BIGSH.
          split.
          * exists (firstn (Z.to_nat cs) (skipn (Z.to_nat (Z.of_nat i * cs)) tb)).
            replace ABv with (RB + au + Z.of_nat (Z.to_nat (Z.of_nat i * cs))) by (subst ABv; rewrite Z2Nat.id by (clear - CSR; nia); clear - OFFE; lia).
            apply (CB_sub asegs mm _ _ _ _ _ BIG). clear - CHB2 NWB HAU CSR; nia.
          * dexists (Z_to_bv 8 0xfa), (repeat (Z_to_bv 8 0xfa) (Z.to_nat (cs / 8 - 1))). split; [| clear; vm_compute; intros E; discriminate E].
            lazymatch type of BIGSH with rw_cells _ _ _ [CB ?nE25 _] => assert (HOKE25 : (Z.to_nat (Z.of_nat i * cs / 8) + Z.to_nat (cs / 8) <= nE25)%nat) by (clear - CHB2 NWB HAU CSR CS16 TMOD TDIV; nia) end. (* [comment removed for export] *)
            pose proof (CB_sub asegs mm _ _ _ (Z.to_nat (Z.of_nat i * cs / 8)) (Z.to_nat (cs / 8)) BIGSH HOKE25) as SUBSH.
            rewrite firstn_skipn_repeat in SUBSH by exact HOKE25. clear HOKE25.
            replace (0x7fff8000 + (RB + au) / 8 + Z.of_nat (Z.to_nat (Z.of_nat i * cs / 8))) with (0x7fff8000 + ABv / 8) in SUBSH.
            2:{ subst ABv. rewrite OFFE. rewrite Z2Nat.id by (apply Z.div_pos; clear - CSR; nia).
                clear - AUAL RBE SBAL CS16. pose proof (Z.div_mod au 16 ltac:(lia)). pose proof (Z.div_mod cs 16 ltac:(lia)). pose proof (Z.div_mod SB 4096 ltac:(lia)). nia. }
            eapply rw_cells_reshape; [exact SUBSH| cbn; rewrite repeat_length; split; [exact I| split; [reflexivity| exact I]] |].
            cbn [cells_bytes cbytes app]. rewrite !app_nil_r. replace (Z.to_nat (cs / 8)) with (S (Z.to_nat (cs / 8 - 1))) by (clear - CSR; lia). reflexivity.
          } }
    ddestruct CHUNK as (OFF & (cbs & CBS) & (sh0 & shs & CSH & NZ)).
    pose proof (rz_size_bound n) as RZSB. pose proof (rz_size_cases n) as RC.
    assert (NFB : 1 <= nfix n <= Z.max n 1) by (unfold nfix; clear - NB; lia).
    assert (N2B' : nfix n + rz_size n <= needed2 n).
    { rewrite N2E. unfold needed, rounded, round_up. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). clear - H H0 NB NFB. lia. }
    assert (N2CS : needed2 n <= cs) by (pose proof (class_fitsL (needed2 n) ltac:(clear - N2E NDB; lia)) as CF; exact CF).
    pose proof (Z.div_mod (nfix n) 8 ltac:(clear; lia)) as DNF. pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(clear; lia)) as MNF.
    assert (ABv8 : ABv mod 16 = 0).
    { subst ABv. pose proof (Z.div_mod SB 4096 ltac:(lia)) as DS.
      replace (RB + 16 * (bv_unsigned pw mod 2^32)) with ((SB / 4096 * 256 + c * 2^28 + bv_unsigned pw mod 2^32) * 16) by (rewrite RBE; clear - DS SBAL; lia). apply Z_mod_mult. }
    pose proof (Z.div_mod ABv 16 ltac:(clear; lia)) as DAB. rewrite ABv8, Z.add_0_r in DAB.
    pose proof (Z.div_mod cs 16 ltac:(clear; lia)) as DCS16. rewrite CS16, Z.add_0_r in DCS16.
    (* [comment removed for export] *)
    pose proof (CB_sub asegs mm ABv (Z.to_nat cs) cbs (Z.to_nat (rz_size n - 16)) 16 CBS ltac:(clear - RZSB N2B' N2CS NFB; lia)) as HDRc.
    rewrite Z2Nat.id in HDRc by (clear - RZSB; lia). destruct (CB16_hdr asegs mm _ _ HDRc) as (b0 & b1 & w2 & w4 & w8 & HDR2). clear HDRc.
    pose proof (CB_sub asegs mm ABv (Z.to_nat cs) cbs 0 16 CBS ltac:(clear - CSR; lia)) as MGc. rewrite Z.add_0_r in MGc.
    destruct (CB16_words asegs mm _ _ MGc) as (mg0 & mg1 & MG2). clear MGc.
    pose proof (CB_sub asegs mm ABv (Z.to_nat cs) cbs (Z.to_nat (rz_size n)) (Z.to_nat (Z.min (nfix n) 4096)) CBS ltac:(clear - RZSB N2B' N2CS NFB; lia)) as UC2.
    rewrite Z2Nat.id in UC2 by (clear - RZSB; lia).
    pose proof CSH as CSH'. change [C1 sh0; CB (Z.to_nat (cs / 8 - 1)) shs] with ([C1 sh0] ++ [CB (Z.to_nat (cs / 8 - 1)) shs]) in CSH'.
    apply rw_cells_app in CSH' as [SHC2 SHT]. cbn [cells_size csize Nat.add] in SHT.
    pose proof (CB_sub asegs mm _ _ shs (Z.to_nat (rz_size n / 8 - 1)) (Z.to_nat (nfix n / 8)) SHT ltac:(clear - RZSB RC N2B' N2CS NFB DNF MNF DCS16 CSR; lia)) as SH2.
    replace (0x7fff8000 + ABv / 8 + Z.of_nat 1 + Z.of_nat (Z.to_nat (rz_size n / 8 - 1))) with (0x7fff8000 + (ABv + rz_size n) / 8) in SH2
      by (rewrite Z2Nat.id by (clear - RC; lia); clear - RC DAB; lia).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    pose proof (hsh_mono _ _ _ HSH1 MU2 WM2) as HSH2.
    (* [comment removed for export] *)
    assert (PGC2 : exists pgb, rw_cells asegs mm (0x7fff8000 + Z.shiftr (ABv + rz_size n + nfix n / 8 * 8) 3) [C1 pgb]).
    { rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
      destruct (Z_lt_ge_dec (rz_size n / 8 + nfix n / 8) (cs / 8)) as [LT|GE].
      - pose proof (CB_sub asegs mm _ _ shs (Z.to_nat (rz_size n / 8 + nfix n / 8 - 1)) 1 SHT ltac:(clear - LT RZSB RC NFB DNF MNF DCS16 CSR; lia)) as B1.
        rewrite Z2Nat.id in B1 by (clear - RC NFB DNF MNF; lia).
        replace (0x7fff8000 + ABv / 8 + Z.of_nat 1 + (rz_size n / 8 + nfix n / 8 - 1)) with (0x7fff8000 + (ABv + rz_size n + nfix n / 8 * 8) / 8) in B1 by (clear - RC DAB DNF MNF; lia).
        destruct (CB1_byte asegs mm _ _ B1) as [b Hb]. exists b. exact Hb.
      - apply HSH2. subst ABv. clear - GE OFF RC DAB DNF MNF DCS16 CSR RBE FAS MU0 MUH MUB2 HAU N2B' N2CS SBAL PWR. pose proof (Z.div_mod SB 4096 ltac:(lia)).
        assert (unit_if u <= 2^18) by (destruct u as [[|]|]; cbn; lia). split; nia. }
    destruct PGC2 as [pgb PGC2].
    replace (ABv + (rz_size n - 16)) with (ABv + rz_size n + -16) in HDR2 by (clear; lia).
    assert (UIF : 0 <= unit_if u <= 2^18) by (destruct u as [[|]|]; cbn; clear; lia). assert (UIFf : 0 <= unit_if f <= 2^18) by (destruct f as [[|]|]; cbn; clear; lia).
    assert (AB1c : ABv + needed2 n <= SB + c * 2^32 + 0xE0000000) by (clear - OFF N2CS MUH MUB2 UIF RBE; try subst ABv; lia).
    assert (ACScs : crange (CSf u f nb0 bl0) ABv cs).
    { intros y Hy. destruct (Z_lt_ge_dec y (RB + mu)) as [LT|GE].
      - apply CSinc0. apply CSRB. subst ABv. clear - Hy LT PWR. lia.
      - destruct u as [[|]|]; cbn [unit_if] in OFF; [| exfalso; clear - Hy GE OFF; try subst ABv; lia | exfalso; clear - Hy GE OFF; try subst ABv; lia].
        apply (CSUz f). subst ABv. cbv delta [UA] in *. clear - Hy GE OFF. lia. }
    assert (ACSc : crange (CSf u f nb0 bl0) ABv (needed2 n)) by (eapply crange_sub; [exact ACScs| clear; lia| clear - N2CS; lia]).
    assert (DCSc : depot_cs (CSf u f nb0 bl0) nb0 bl0).
    { destruct DCS as [D1 D2]. split; [intros k Hk y Hy; apply CSinc0; exact (D1 k Hk y Hy)| intros j Hj y Hy; apply CSinc0; exact (D2 j Hj y Hy)]. }
    assert (AS2 : allocA_statics mm T CTX).
    { eapply (allocA_statics_transport _ m1 mm T CTX AS1 MU2); [intros A k H; apply LOW2; exact H|]. cbn [disjoint_from app cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. subst SPA STK.
      clear - FAS RS RIhi ERI SEP1 SEP3 TC LOIMG SPL T0 T1 CX0 CX1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    assert (FS2 : fin_statics mm) by (eapply (fin_statics_transport _ m1 mm FS1 MU2); intros A k H; apply LOW2; exact H).
    assert (GOTFL2 : ro_cells asegs mm A_GOT_FLAGS [C8 (Z_to_bv 64 A_FLAGS)]) by (eapply ro_cells_transport; [exact GOTFL1| exact MU2| apply LOW2; unfold A_GOT_FLAGS; cbn; clear; lia]).
    assert (PPART2 : ro_cells asegs mm A_FL_PPART [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact PPART1| exact MU2| apply LOW2; unfold A_FL_PPART; cbn; clear; lia]).
    assert (DJTT2 : forall A k, T <= A -> A + k <= T + 208 -> disjoint_from
              ((lo, SPA + -128) :: (UA, UA + 2^18) :: (0x7fff8000 + UA / 8, 0x7fff8000 + UA / 8 + 32768) :: (FA, FAA + 2^18) :: (0x7fff8000 + FAA / 8, 0x7fff8000 + FAA / 8 + 32768)
               :: (T + 2872, T + 2888) :: (T + 2792, T + 2800) :: (T + 2784, T + 2792) :: (R, R + 8) :: (R + 16, R + 24) :: (R + 24, R + 32) :: (R + 32, R + 40) :: (R + 48, R + 56)
               :: (R + 68, R + 69) :: (R + 72, R + 80) :: [(T + 288, T + 2768)]) A k).
    { intros A k H1 H2. cbn [disjoint_from app]. subst SPA STK. clear - H1 H2 FAS RS RIhi ERI SEP1 LOIMG SPL T0 T1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    assert (TH2 : ro_cells asegs mm T [C8 (Z_to_bv 64 CTX)]) by (eapply ro_cells_transport; [exact TH1| exact MU2| apply DJTT2; cbn; clear; lia]).
    assert (TIDC2 : ro_cells asegs mm (CTX + 8) [C4 (Z_to_bv 64 TID)]).
    { eapply ro_cells_transport; [exact TIDC1| exact MU2|]. cbn [disjoint_from app cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. subst SPA STK.
      clear - FAS RS RIhi ERI SEP1 SEP3 TC LOIMG SPL T0 T1 CX0 CX1 SBlo MU0 MF0 CR UAE FAAE FAE PCRE RBE. repeat split; lia. }
    (* [comment removed for export] *)
    eapply (srzJ_of_aevtS asegs); [| exact B0n |].
    { eapply (mseg_chunk u f pw) with (mg0 := mg0) (mg1 := mg1) (b0 := b0) (b1 := b1) (w2 := w2) (w4 := w4) (w8 := w8) (shb := sh0) (pgb := pgb) (sj := _) (uj := _)
                                     (j0 := j0) (j1 := j1) (j2 := j2) (bs := bs) (N := N) (tf := tf) (size := size) (ws := ws) (fr0 := fr0) (fr1 := fr1) (fr2 := fr2).
      all: lazymatch goal with
           | |- _ + needed2 n <= _ => exact AB1c
           | |- crange _ T 4096 => exact (CST' u f)
           | |- crange _ CTX 0x10000 => exact (CSCTX' u f)
           | |- crange _ lo _ => exact SCSc
           | |- crange _ _ (needed2 n) => exact ACSc
           | |- allocA_statics _ _ _ => exact AS2
           | |- poison_statics _ => exact PS2
           | |- fin_statics _ => exact FS2
           | |- depot_statics _ => exact DST2
           | |- ro_cells _ _ A_GOT_FLAGS _ => exact GOTFL2
           | |- ro_cells _ _ A_FL_PPART _ => exact PPART2
           | |- ro_cells _ _ T _ => exact TH2
           | |- ro_cells _ _ (CTX + 8) _ => exact TIDC2
           | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HDR2
           | |- 16 < rz_size n -> _ => intros _; exact MG2
           | |- rw_cells _ _ _ [CB (Z.to_nat (Z.min _ _)) _] => exact UC2
           | |- ro_cells _ _ (0x7fff8000 + Z.shiftr _ 3) _ => rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; exact (proj1 SHC2)
           | |- bv_unsigned _ <> 0 => exact NZ
           | |- rw_cells _ _ (0x7fff8000 + _ / 8) [CB _ _] => exact SH2
           | |- rw_cells _ _ (0x7fff8000 + Z.shiftr _ 3) _ => exact PGC2
           | |- allocA_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact AFR2
           | |- rw_cells _ _ (STK + -16) _ => exact FR162
           | |- rw_cells _ _ (SP + -56) _ => exact FR72
           | |- rw_cells _ _ STK _ => exact STKC2
           | |- u64arr _ _ (STK + 16) _ => exact HTR2
           | |- length _ = 30%nat => exact HL30
           | |- 1 <= _ <= 30 => exact SZB
           | |- _ <= d + 2 => exact SZD
           | |- rw_cells _ _ (STK + 256) _ => exact F18002
           | |- rw_cells _ _ (STK + 2056) _ => exact TFBP2
           | |- rw_cells _ _ (STK + 2064) _ => exact F82
           | |- rw_cells _ _ (T + 3168) _ => exact UNW2
           | |- rw_cells _ _ (T + 2800) _ => exact STH2
           | |- u64arr _ _ (T + 2912) _ => exact STB2
           | |- length _ = 32%nat => exact HL
           | |- depot_inv _ _ _ _ _ => exact DI2
           | |- depot_cs _ _ _ => exact DCSc
           | |- _ + 128 <= 2^32 => exact TFMAX
           | |- _ + 2 <= _ => exact NB2
           | |- stk _ _ _ _ => exact ST2
           | |- mem_inv _ _ => exact MI2
           | |- K _ _ _ _ _ => exact HK2
           | |- J _ _ => exact HJ2
           | |- Gn _ _ _ _ => apply GN
           | |- Gs _ _ (_ ++ _) _ => apply GSX
           | |- Gs _ _ _ _ => apply GS
           | |- forall x, Gs _ _ _ _ => intros x0; apply GSX
           | |- forall k, _ => first [exact APTn| exact APCn| exact APSn| exact APTs| exact APCs| exact APSs| (intros x0; apply GSX)| match goal with |- ?G => fail 99 "FK" G end]
           | |- ?G => fail "mseg_chunk premise" G
           end. }
    intros cf' PO'. unfold chunk_post in PO'. fold RB in PO'. fold ABv in PO'.
    ddestruct PO' as (ms9 & mo9 & nb' & bl' & N' & tf' & id & z0 & z1 & z2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & b1' & pgb' & sj0 & sj1 & sj2 & bs9 & m9
                      & -> & -> & HK9 & HJ9 & DI9 & DCS9 & DST9 & IDB & NB' & TFB' & TFP & CSM & BLK & GK & ZK & WM9 & MI9 & ST9 & HDR9 & B1A & B1B & MG9 & SH9 & PGC9 & PGU & UC9 & STH9 & STB9 & HL9 & UNW9).
    (* [comment removed for export] *)
    assert (PGWc : (nfix n mod 8 = 0 /\ pgw = 0) \/ (nfix n mod 8 <> 0 /\ pgw = 1)).
    { unfold pgw. destruct (Z.eqb_spec (nfix n mod 8) 0); [left| right]; split; auto. }
    set (PGSv := 0x7fff8000 + Z.shiftr (ABv + rz_size n + nfix n / 8 * 8) 3) in *.
    assert (PGSE : PGSv = 0x7fff8000 + (ABv + rz_size n) / 8 + nfix n / 8).
    { subst PGSv. rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. clear - DAB RC DNF MNF. lia. }
    set (cw := [(ABv + rz_size n + -16, ABv + rz_size n + -16 + 16); (ABv, ABv + 16); (ABv + rz_size n, ABv + rz_size n + Z.min (nfix n) 4096);
                (0x7fff8000 + (ABv + rz_size n) / 8, 0x7fff8000 + (ABv + rz_size n) / 8 + nfix n / 8); (PGSv, PGSv + pgw)]).
    assert (ZK' : forall x : word, zone u f (bv_unsigned x) -> outside cw (bv_unsigned x) -> m9 x = mm x).
    { intros x HZ HO. subst cw. cbn [outside app] in HO. ddestruct HO as (O1 & O2 & O3 & O4 & O5 & _).
      destruct (Z.eq_dec (bv_unsigned x) PGSv) as [E|NE].
      - destruct PGWc as [[E0 P0]|[E1 P1]]; [| exfalso; clear - O5 E P1; lia].
        rewrite <- (Z_to_bv_bv_unsigned x). rewrite E. exact (PGU E0).
      - apply ZK; [exact HZ|]. unfold cwin. cbn [outside]. refine (conj O1 (conj O2 (conj O3 (conj O4 (conj _ I))))).
        match goal with |- ~ (?P <= _ < _) => change PGSv with P in NE end. clear - NE. intros [H1 H2]. apply NE. lia. }
    assert (ZKM : forall A sz, (forall a, A <= a < A + sz -> zone u f a) -> munch (cw ++ [(0, A); (A + sz, 2^64)]) mm m9).
    { intros A sz HZ x Hx. subst cw. cbn [outside app] in Hx. ddestruct Hx as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & _).
      pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
      apply ZK'; [apply HZ; clear - O6 O7 XR; lia|]. cbn [outside]. clear - O1 O2 O3 O4 O5. tauto. }
    (* [comment removed for export] *)
    dpose GSEP as (_ & _ & SEP3').
    assert (CHI : ABv + cs <= RB + mu + unit_if u /\ RB <= ABv /\ RB + mu + unit_if u <= FA) by (subst ABv; cbv delta [FA] in *; clear - OFF PWR UIF MUH MUB2 RBE; lia).
    (* [comment removed for export] *)
    assert (ZR : forall a, RI <= a < RI + 4096 -> zone u f a) by (intros a Ha; left; split; [apply (CSRI' u f); exact Ha| clear - Ha ERI SBlo; lia]).
    assert (ZT : forall a, T <= a < T + 2800 -> zone u f a) by (intros a Ha; left; split; [apply (CST' u f); clear - Ha; lia| clear - Ha; lia]).
    assert (ZC : forall a, CTX <= a < CTX + 0x10000 -> zone u f a) by (intros a Ha; left; split; [apply (CSCTX' u f); exact Ha| clear - Ha; lia]).
    assert (ZL : forall a, 0x10000 <= a < 0x10000 + (A_SS - 0x10000) -> zone u f a) by (intros a Ha; right; right; unfold A_SS, A_DEP_END in *; clear - Ha; lia).
    assert (ZH : forall a, A_DEP_END <= a < A_DEP_END + (0x65f000 - A_DEP_END) -> zone u f a) by (intros a Ha; right; right; unfold A_SS, A_DEP_END in *; clear - Ha; lia).
    assert (ZS : forall a, 0x7fff8000 + SB / 8 <= a < 0x7fff8000 + SB / 8 + ((RI + 4096) / 8 - SB / 8) -> zone u f a) by (intros a Ha; right; left; clear - Ha; lia).
    assert (ZF : forall a, FA <= a < FA + (mfa + unit_if f) -> zone u f a).
    { intros a Ha. left. split; [| clear - Ha FAS MF0 UIF; destruct f as [[|]|]; cbn [unit_if] in Ha; lia].
      destruct (Z_lt_ge_dec a (FA + mfa)) as [LT|GE]; [apply CSinc0; apply CSFA; clear - Ha LT; lia|].
      destruct f as [[|]|]; cbn [unit_if] in Ha; [| exfalso; clear - Ha GE; lia| exfalso; clear - Ha GE; lia]. apply (CSFz u). cbv delta [FAA] in *. clear - Ha GE. lia. }
    assert (ZU : u = Some true -> forall a, UA <= a < UA + 2^18 -> zone u f a).
    { intros Eu a Ha. left. split; [subst u; apply (CSUz f); exact Ha| clear - Ha FAS MU0 MF0 UAE; lia]. }
    pose proof (ZKM _ _ ZR) as MUR. pose proof (ZKM _ _ ZT) as MUT. pose proof (ZKM _ _ ZS) as MUS. pose proof (ZKM _ _ ZF) as MUF.
    (* [comment removed for export] *)
    assert (ZKW : forall W, (forall a, 0 <= a < 2^64 -> outside W a -> zone u f a /\ outside cw a) -> munch W mm m9).
    { intros W HW x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
      destruct (HW _ XR Hx) as [HZ HO]. exact (ZK' x HZ HO). }
    assert (MUlow9 : munch (cw ++ [(0, 0x10000); (A_SS, A_DEP_END); (0x65f000, 2^64)]) mm m9).   (* [comment removed for export] *)
    { apply ZKW. intros a AR Ha. unfold cw in Ha. cbn [outside app] in Ha. ddestruct Ha as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & _).
      split; [| unfold cw; cbn [outside]; clear - O1 O2 O3 O4 O5; tauto]. right. right. clear - O6 O7 O8 AR. lia. }
    assert (MUthr9 : munch (cw ++ [(0, 0x10000); (A_SS, A_DEP_END); (0x65f000, CTX); (CTX + 0x10000, 2^64)]) mm m9).
    { apply ZKW. intros a AR Ha. unfold cw in Ha. cbn [outside app] in Ha. ddestruct Ha as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & _).
      split; [| unfold cw; cbn [outside]; clear - O1 O2 O3 O4 O5; tauto].
      destruct (Z_lt_ge_dec a 0x65f000) as [LT|GE]; [right; right; clear - O6 O7 LT AR; lia| left; split; [apply (CSCTX' u f); clear - O8 O9 GE CX0 AR; lia| clear - O8 O9 GE CX0 AR; lia]]. }
    (* [comment removed for export] *)
    assert (RZ16 : rz_size n mod 16 = 0) by (clear - RC; lia). pose proof (Z.div_mod (rz_size n) 16 ltac:(clear; lia)) as DRZ. rewrite RZ16, Z.add_0_r in DRZ.
    assert (DJW : forall A k A0 sz, (A + k <= ABv \/ ABv + cs <= A) -> (A + k <= 0x7fff8000 + ABv / 8 \/ 0x7fff8000 + (ABv + cs) / 8 <= A) ->
              (A + k <= 0 \/ A0 <= A) -> A + k <= A0 + sz -> disjoint_from (cw ++ [(0, A0); (A0 + sz, 2^64)]) A k).
    { intros A k A0 sz H1 H2 H3 H4. unfold cw. cbn [disjoint_from app]. rewrite PGSE.
      clear - H1 H2 H3 H4 PGWc DNF MNF RZSB N2B' N2CS NFB DAB DRZ DCS16 CSR. repeat split; lia. }
    assert (DJW2 : forall A k, (A + k <= ABv \/ ABv + cs <= A) -> (A + k <= 0x7fff8000 + ABv / 8 \/ 0x7fff8000 + (ABv + cs) / 8 <= A) -> 0x10000 <= A /\ A + k <= A_SS ->
              disjoint_from (cw ++ [(0, 0x10000); (A_SS, A_DEP_END); (0x65f000, 2^64)]) A k).
    { intros A k H1 H2 H3. unfold cw. cbn [disjoint_from app]. rewrite PGSE. unfold A_SS, A_DEP_END in *.
      clear - H1 H2 H3 PGWc DNF MNF RZSB N2B' N2CS NFB DAB DRZ DCS16 CSR. repeat split; lia. }
    (* [comment removed for export] *)
    assert (ABlo : 0x10007fff9000 <= ABv /\ ABv + cs <= RI) by (clear - CHI FAS SBlo MU0 MF0; lia).
    Ltac ti9 H MU WM DJ tac := eapply rw_cells_transport; [exact H| exact MU| exact WM| apply DJ; cbn [cells_size csize Nat.add length map Z.of_nat Pos.of_succ_nat Pos.succ]; tac].
    apply HCHK. unfold mgen_postC.
    eexists. dexists mo9, (ABv + rz_size n), u, f, nb', bl'. dexists z0, z1, z2, za1, za2, za3, za4, za5, za6, za7, z3, z4, z5, z6.
    (* [comment removed for export] *)
    assert (TJ9 : exists q1 q2, rw_cells asegs m9 (T + 2872) [C8 q1; C8 q2]).
    { assert (TJc : rw_cells asegs mm (T + 2872) [CB 16 (le8 k1 ++ le8 k2)]) by (eapply rw_cells_reshape; [exact TJ2| cbn [cells_wf cell_wf]; rewrite app_length, !length_le8; split; [reflexivity| exact I]| cbn [cells_bytes cbytes]; rewrite !app_nil_r; reflexivity]).
      assert (MUall : munch [(0, 2^64)] mm m9) by (intros x Hx; exfalso; cbn in Hx; pose proof (bv_unsigned_in_range 64 x) as XR; unfold bv_modulus in XR; change (2 ^ Z.of_N 64) with (2^64) in XR; clear - Hx XR; lia).
      destruct (CB_holed asegs _ mm m9 (T + 2872) 16 _ TJc MUall WM9 ltac:(intros i Hi; apply asegs_none_off; clear - T0 Hi; lia)) as [bs' [H' _]].
      destruct (CB16_words asegs m9 _ _ H') as (q1 & q2 & H''). dexists q1, q2. exact H''. }
    ddestruct TJ9 as (q1 & q2 & TJ9).
    dexists stw', cstw', q1, q2, k3, m9.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HK9|]. split; [exact HJ9|]. split; [exact MUB2|].
    split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM9))|]. split; [exact MI9|]. split; [exact ST9|].
    split; [intros y Hy; apply CSM; apply CSinc0; exact Hy|].
    split; [exact DST9|].
    split; [eapply (poison_statics_transport _ mm m9 PS2 MUlow9); intros A k H; apply DJW2; unfold A_SS in *; clear - H ABlo; lia|].
    split. { ddestruct TS2 as (X1 & X2 & X3 & X4). unfold thr_statics. unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR in *.
             assert (DJT : forall A k, (A + k <= A_SS \/ (A_DEP_END <= A /\ A + k <= 0x65f000) \/ (CTX <= A /\ A + k <= CTX + 0x10000)) -> 0x10000 <= A ->
                       disjoint_from (cw ++ [(0, 0x10000); (A_SS, A_DEP_END); (0x65f000, CTX); (CTX + 0x10000, 2^64)]) A k).
             { intros A k H1 H2. unfold cw. cbn [disjoint_from app]. rewrite PGSE. unfold A_SS, A_DEP_END in *. dpose GSEP as (_ & _ & SEPc).
               clear - H1 H2 PGWc DNF MNF RZSB N2B' N2CS NFB DAB DRZ DCS16 CSR ABlo CX0 CX1 SEPc CHI FAS ERI RIhi SBlo. repeat split; lia. }
             repeat split; (eapply ro_cells_transport; [eassumption| exact MUthr9| apply DJT; unfold A_SS, A_DEP_END; cbn; clear - CX0; lia]). }
    split; [eapply (mwc_statics_transport _ mm m9 MWS2 MUlow9); intros A k H; apply DJW2; unfold A_SS in *; clear - H ABlo; lia|].
    split; [eapply (pop_statics_transport _ mm m9 SB PPS2 MUlow9); intros A k H; apply DJW2; unfold A_SS in *; clear - H ABlo; lia|].
    split; [ti9 MX2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|]. split; [ti9 MFA2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|].
    split; [ti9 M402 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|]. split; [ti9 MUC2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|].
    split; [ti9 M562 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|]. split; [ti9 STW2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|].
    split; [ti9 STC2 MUT WM9 DJW ltac:(clear - ABlo CHI FAS ERI SBlo MF0 MU0 SEP1 T0 T1 CR PCRE RIhi; lia)|]. split; [exact TJ9|].
    split; [ti9 SJ2 MUT WM9 DJW ltac:(clear - ABlo CHI FAS ERI SBlo MF0 MU0 SEP1 T0 T1 CR PCRE RIhi; lia)|].
    (* [comment removed for export] *)
    split; [intros Hf; ti9 (FSH Hf) MUS WM9 DJW ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia); clear - ABlo CHI FAS ERI SBlo RIhi MF0 MU0 UIF UAE FAAE FAE RBE PGSE PGWc DNF MNF RZSB N2B' N2CS DAB DRZ DCS16 CSR; lia)|].
    split; [intros Hf; ti9 (FSHn Hf) MUS WM9 DJW ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia); clear - ABlo CHI FAS ERI SBlo RIhi MF0 MU0 UIF UAE FAAE FAE RBE PGSE PGWc DNF MNF RZSB N2B' N2CS DAB DRZ DCS16 CSR; lia)|].
    split. { intros Hu HMU. assert (OFF' : 16 * (bv_unsigned pw mod 2^32) + cs <= mu) by (destruct u as [[|]|]; cbn [unit_if] in OFF; [exfalso; apply Hu; reflexivity| clear - OFF; lia| clear - OFF; lia]).
             ti9 (USHn Hu HMU) MUS WM9 DJW ltac:(rewrite ?Nat.add_0_r, ?Z2Nat.id by (clear; lia);
                assert (ABvE : ABv = RB + 16 * (bv_unsigned pw mod 2^32)) by reflexivity;
                clear - OFF' ABlo CHI FAS ERI SBlo RIhi MF0 MU0 UIF UAE FAAE FAE RBE PGSE PGWc DNF MNF RZSB N2B' N2CS DAB DRZ DCS16 CSR PWR ABvE; lia). }
    split; [exact UNW9|].
    split; [intros j Hj NEj; unfold pc_new; ti9 (PCN2 j Hj NEj) MUT WM9 DJW ltac:(rewrite ?cells_size_app, ?REST; cbn [cells_size csize Nat.add]; clear - ABlo CHI FAS ERI SBlo MF0 MU0 SEP1 T0 T1 Hj RIhi; lia)|].
    dexists ABv, cnt', ds', pw, N', tf', id, b1', pgb', sj0, sj1, sj2, bs9.
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HC'|]. split; [exact NTH|]. split; [exact LDS'|].
    split.
    { (* [comment removed for export] *)
      intros x. cbv zeta. intros HO HBn HBs. cbn [outside app] in HO. unfold mgen_windows in HO. cbn [outside app] in HO.
      ddestruct HO as (W1 & W2 & W3 & W4 & W5 & O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11 & O12 & O13 & O14 & O15 & O16 & O17 & O18 & O19 & O20 & O21 & _).
      transitivity (mm x).
      - destruct (Z.eq_dec (bv_unsigned x) PGSv) as [E|NE].
        + destruct PGWc as [[E0 P0]|[E1 P1]]; [| exfalso; clear - W5 E P1; lia]. rewrite <- (Z_to_bv_bv_unsigned x). rewrite E. exact (PGU E0).
        + apply GK; [| exact HBn| exact HBs]. unfold cwin. cbn [outside]. refine (conj O1 (conj O2 (conj _ (conj W1 (conj W2 (conj W3 (conj W4 (conj _ I)))))))).
          * clear - O3 O6. lia.
          * match goal with |- ~ (?P <= _ < _) => change PGSv with P in NE end. clear - NE. intros [H1 H2]. apply NE. lia.
      - rewrite (MU2 x). 2:{ cbn [outside app]. subst SPA STK.
                             repeat split; first [sassumption | cassumption | exact O8| exact O9| exact O10| exact O11| exact O7| exact O5| exact O4| exact O12| exact O13| exact O14| exact O15| exact O16| exact O17| exact O18| exact O21| exact I | (clear - O1; lia)]. }
        apply (MU1 x). cbn [outside]. repeat split; first [exact O1| exact O3| exact I]. }
    split; [ti9 PC2 MUT WM9 DJW ltac:(clear - ABlo CHI FAS ERI SBlo MF0 MU0 SEP1 T0 T1 CR PCRE RIhi; lia)|].
    split; [eapply u32arr_transport; [exact ARR2| exact MUT| exact WM9| rewrite LDS'; apply DJW; clear - ABlo CHI FAS ERI SBlo MF0 MU0 SEP1 T0 T1 CR PCRE RIhi; lia]|].
    split.
    { destruct CASES as [(Ecnt & Eds & Eu & Ef & NF2 & AU2 & EX2 & HFAR2 & HJS2) | (CNT0' & Ecnt & Un & Fn & new & ws' & fa' & rest' & nf' & au' & ex' & Eds & Efa & Lws & Lfa' & SRC & NF2 & AU2 & EX2 & HFAR2 & HREST2 & Lrest)].
      - exfalso. clear - Ecnt HC'. lia.
      - right. split; [exact CNT0'|]. split; [exact Ecnt|]. split; [exact Un|]. split; [exact Fn|].
        dexists new, ws', fa', rest', nf', au', ex'.
        split; [exact Eds|]. split; [exact Efa|]. split; [exact Lws|]. split; [exact Lfa'|]. split; [exact SRC|].
        split; [ti9 NF2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|]. split; [ti9 AU2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|]. split; [ti9 EX2 MUR WM9 DJW ltac:(clear - RS ABlo CHI FAS ERI SBlo MF0 MU0; lia)|].
        split; [eapply u32arr_transport; [exact HFAR2| exact MUF| exact WM9| rewrite Lfa'; apply DJW; cbn; clear - ABlo CHI FAS ERI SBlo RIhi MF0 MU0 UIF UIFf Lrest HNF FAAE FAE RBE; lia]|].
        split; [| exact Lrest]. eapply u32arr_transport; [exact HREST2| exact MUF| exact WM9| apply DJW; cbn; clear - ABlo CHI FAS ERI SBlo RIhi MF0 MU0 UIF UIFf Lrest HNF Lfa' FAAE FAE RBE; lia]. }
    split.
    { (* [comment removed for export] *)
      intros Eu. destruct (USH Eu) as [UZ USHz]. pose proof (ZKM _ _ (ZU Eu)) as MUU.
      destruct (CB_holed asegs _ mm m9 UA _ _ UZ MUU WM9 ltac:(intros i Hi; apply asegs_none; [clear - Hi FAS SBlo UAE MU0; lia| clear; lia])) as [zb [ZB9 ZBH]].
      destruct (CB_holed asegs _ mm m9 _ _ _ USHz MUS WM9 ltac:(intros i Hi; apply asegs_none; [clear - Hi FAS SBlo UAE MU0; lia| clear; lia])) as [ush [USH9 USHH]].
      dexists zb, ush. split; [exact ZB9|]. split; [exact USH9|]. split.
      - intros i Hi HO. rewrite (ZBH i Hi); [apply nth_error_repeat; exact Hi|]. unfold cw. cbn [outside app] in HO |- *. ddestruct HO as (O1 & O2 & O3 & _).
        rewrite PGSE. clear - O1 O2 O3 Hi ABlo CHI FAS SBlo ERI RIhi MU0 MF0 UAE RZSB N2B' N2CS NFB PGWc. repeat split; try exact I; first [lia | match goal with |- ?G => fail 99 "DBG" G end].
      - intros i Hi HO. rewrite (USHH i Hi); [apply nth_error_repeat; exact Hi|]. unfold cw. cbn [outside app] in HO |- *. ddestruct HO as (O1 & O2 & _).
        rewrite ?Z.shiftr_div_pow2 in O2 by (clear; lia). change (2 ^ 3) with 8 in O2.
        revert O1 O2. rewrite PGSE. intros O1 O2. clear - O1 O2 Hi ABlo CHI FAS SBlo ERI RIhi MU0 MF0 UAE RZSB N2B' N2CS NFB PGWc DAB DRZ DNF MNF DCS16. repeat split; try exact I; first [lia | match goal with |- ?G => fail 99 "DBG2" G end]. }
    split; [exact DI9|]. split; [exact DCS9|]. split; [exact IDB|]. split; [exact NB'|]. split; [exact TFB'|]. split; [exact TFP|]. split; [exact BLK|].
    split; [intros y Hy; apply CSM; apply ACScs; exact Hy|].
    split; [exact HDR9|]. split; [exact B1A|]. split; [exact B1B|]. split; [exact MG9|]. split; [exact SH9|]. split; [exact PGC9|]. split; [exact UC9|].
    split; [exact STH9|]. split; [exact STB9|]. split; [exact HL9|].
    split; [eapply rw_cells_transport; [exact OOM2| exact MUlow9| exact WM9| apply DJW2; unfold A_OOM_CELL, A_SS; cbn; clear - ABlo; lia]|].
    eapply rw_cells_transport; [exact ERR2| exact MUlow9| exact WM9|]. unfold cw, A_ERRNO, A_SS, A_DEP_END.
    cbn [disjoint_from app cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite PGSE.
    clear - ABlo CHI FAS PGWc DNF MNF RZSB N2B' N2CS NFB DAB DRZ DCS16 CSR. repeat split; first [lia | match goal with |- ?G => fail 99 "ERRLIA" G end].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End MallocGenSplit.

End ARUN_1.
