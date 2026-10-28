(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
     AW_Large AW_MapOrDie AW_LargeCfgS AW_MmapFixedNR AW_PoisonBig AW_PoisonBigCfg AW_MallocGenLib AW_MallocGen AW_SecB AW_SecC AW_MallocSecS
     AW_CallocA AW_CallocB AW_CallocC AW_CallocSecC AW_CallocGen AW_CallocSecS.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
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
Ltac2 gd_tbl_AW_CallocSecTop () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_LargeCfgS.img_static_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dblk"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.sblk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PoisonBig.rsmr_statics"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.true"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.anon_grantable"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PoisonBigCfg.poison0_siteS"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CallocSecS.dstat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CallocSecS.DIE_NEED"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.die_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.A_SPIN_MMAPDIE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MapOrDie.mod_answered"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rounded"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.A_DEP_END"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "Stdlib.ZArith.BinInt.Z.mul"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_OOM_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocB.A_ERRNO"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "ARUN_1.CallocSec.msec_cwin"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_cs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_statics"; "Corelib.Lists.ListDef.Forall"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kAllocBegMagic"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.pgv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_LargeCfgS.limg"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocC.msegA_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.fin_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Large.large_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.thr_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CfgDefs.mwc_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_GOT_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_FL_PPART"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_MRN_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_LargeCfgS.shadow_wr"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "ARUN_1.CallocSec.msec_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_CallocA.A_CALLOC"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L10581581829.22L11775529221.22L28221527474.22L2891830110.22 L29738675806.22L30591810590.22L30787687534.22L34515976471.22L36428071266.22L38872409506.22L4300841669.22 L48047082007.22L54607516834.22L55319072279.22L60137559518.22L6059544325.22 L63754764293.22L65472494626.22L65757338903.22L65985053701.22L719850199.22  L8266780183.22 00000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00D00E00FSSSSSSSSSSSSSSSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma allocA_statics_transport_i : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "PW,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PT,$4.PCTX,$4.P,(5.R4.R2.R1.)P,(6.R6.R5.R4.)P,(7.R7.)P,(8.R8.(9.R4.+98.)+8.)(5.R7.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros W m m' T CTX S MU DJ DJC. unfold allocA_statics, img_static_ok in *.
  unfold A_ASAN_INITED, A_RSS_CELL, A_DEBRUIJN, A_LOGTBL1, A_LOGTBL2, A_MINRZ, A_MAXUSER, A_INSTANCE, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR in *.
  decompose [and] S. repeat split; (eapply ro_cells_transport; [eassumption| exact MU| first [exact DJC| apply DJ; cbn; lia]]).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00B0?L10579486094.16L16277510926.16L1791839388.16 L23615256988.16L32748239260.16L34816162972.16L36655376540.16L40211055758.16L45409267086.16L50493836942.16L5060208796.16 L51457186446.16L54853288348.16L62473061518.16L63253116686.16L66318283150.16L66573539996.16L8264682396.16 00000100200300400500600700800900:00;00<00=00>00?00@00A00BSSSSSSSSSSSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma fin_statics_transport_i : forall W m m', fin_statics m -> munch W m m' -> img_static_ok W -> fin_statics m'.
Proof.
  intros W m m' S MU DJ. unfold fin_statics, img_static_ok in *.
  unfold A_GOT_LSANTLS, A_LSAN_CNT, A_MAGIC_CELL, A_MHOOKS, A_GOT_FLAGS, A_FLAGS, A_FL_MAXFILL, A_FL_FILLB, A_GOT_RMEMSET, A_RMEMSET, A_MUSL_MEMSET, kAllocBegMagic, A_INSTANCE in *.
  decompose [and] S. repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00H0?L10929582012.20L11719062972.20L15976218267.15L16277316156.20L23615439022.14L2512799164.15 L2512799164.20 L33042532540.14L34076139694.14L34879885742.14L35363529646.20L37930651054.15L37930651054.20L41425883566.20L42311357870.20L46454732462.20L5130315111.15 L6057522108.20 L65755308462.20L66318469308.14L66573345710.20L67982786620.20L8345721020.20 L8670607292.14 00000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00D00E00F00G00HSSSSSSSSSSSSSSSSSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma depot_statics_transport_i : forall W m m', depot_statics m -> munch W m m' -> img_static_ok W -> depot_statics m'.
Proof.
  (intros W m m' dd_H; ddestruct dd_H as (DS & CS & c1 & c2 & c3 & M1 & M2 & M3); intros MU DJ). unfold img_static_ok, A_INSTANCE in DJ. split; [|split].
  - destruct DS as [G1 G2]. split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ]); unfold A_GOT_CFLAGS, A_CFLAGS; cbn; lia.
  - ddestruct CS as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold cstatics.
    unfold A_GOT_PAGESZ, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_DECORATE, A_MMAP_LIMIT, A_GOT_SEALED2, A_DYING in *.
    split; [|split; [|split; [|split; [|split; [|split]]]]];
      (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia]).
  - dexists c1, c2, c3. unfold A_MUR1, A_MUR2, A_MUR3 in *.
    repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ]); cbn; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L14789013544.29L29802938152.29L30938057274.29L38467752502.34L39087947745.29L50423199290.29L52419108410.29L63266128424.29L68361472029.29L68363415354.29L8725813800.29 00000>00L00Z00m01;01I01W01e02302A02OS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DML1i2HiS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DML". (* [comment removed for export] *)
#[using="Type"] Lemma depot_inv_transport_i : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "PW,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PN,$4.Pnb,(0.$4.)Ptf,$4.Pbl,(0.$4.)P,(:.VhAR,R6.R4.R3.R2.R1.)P,(6.R8.R7.R6.)P,(;.$<.R8.R7.)P,(7.R:.)P,Pk,$4.P,(=.(>.=R1.)(?.R1.(10.(11.$4.R8.))))(8.R=.(12.R9.R2.)(13.+2.+14.))P,Pj,$4.P,(=.(>.=R1.)(?.R1.(10.(11.$4.R7.))))(8.R>.(14.R8.R2.)(13.+2.+17.))(:.VhAR,R;.R:.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros W m m' N nb tf bl DI MU WM LO DN DS. unfold img_static_ok, A_INSTANCE in LO.
  ddestruct DI as (NC & DT & DM & DNO & WF & MX & (alloc & SSX) & DB & SB & TF0 & BL & BA).
  dpose DM as (DM1 & DMF & DML).
  split. { eapply rw_cells_transport; [exact NC| exact MU| exact WM| apply LO; unfold A_DEP_N; cbn; lia]. }
  split. { eapply (dtab_transport _ m m' N DT MU WM). apply LO; unfold A_DEP; lia. }
  split. { eapply (dmap1_transport _ m m' nb DM MU WM). apply LO; unfold A_DEP_MAP1; lia. }
  split. { eapply (dnodes_transport _ m m' nb N DNO MU WM DMF). intros b Hb.
           ddestruct (In_nth nb b 0 Hb) as (i & Hi & E). specialize (DN (Z.of_nat i) ltac:(lia)). unfold dblk in DN. rewrite Nat2Z.id, E in DN. exact DN. }
  split; [exact WF|].
  split. { eapply rw_cells_transport; [exact MX| exact MU| exact WM| apply LO; unfold A_DEP_NODES; cbn; lia]. }
  split. { exists alloc. eapply rw_cells_transport; [exact SSX| exact MU| exact WM| apply LO; unfold A_SS; cbn; lia]. }
  split. { eapply (dblocks_transport _ m m' bl DB MU WM). apply LO; unfold A_SS; lia. }
  split. { eapply (sblks_transport _ m m' bl SB MU WM). exact DS. }
  split; [exact TF0|]. split; [exact BL| exact BA].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
#[using="Type"] Lemma rsmr_statics_transport_i : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "PW,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))Pcan,(2.&40.)Pdd,(2.&8.)Pmadv,(2.&8.)P,(15.R5.R3.R2.R1.)P,(6.R7.R6.R5.)P,(7.R8.)(15.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof. intros W m m' can dd madv S MU DJ. eapply (rsmr_statics_transport2 W m m' can dd madv S MU). intros A n H1 _ H3. apply DJ; assumption. Qed.
#[using="Type"] Lemma munch_img_static_ok_lo : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "PW,(0.$1.)P,PA,$4.Pn,$4.P,(=.(>.+10000.R2.)(>.(9.R2.R1.)+65?000.))(8.R4.R3.R2.)(7.R2.)")
(* [comment removed for export] *).
Proof. intros W H A n H1 _. apply H. exact H1. Qed.

Section CallocSec.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  (* [comment removed for export] *)
  Variable CSf : list (Z * Z) -> Z -> list Z -> list Z -> Z -> Prop.
  Variable K : list (Z * Z) -> Z -> list Z -> list Z -> Model -> Prop.
  Hypothesis CSOKf : forall sc r nb bl, cs_ok AL (CSf sc r nb bl).
  Hypothesis KL : forall sc r nb bl, kinv AL (CSf sc r nb bl) (K sc r nb bl).
  Hypothesis CSf_noshadow : forall sc r nb bl x, CSf sc r nb bl x -> ~ (0x7fff8000 <= x < 0x10007fff8000).
  (* [comment removed for export] *)
  Variables (nb0 bl0 : list Z).
  Hypothesis CSmono_l : forall sc r p y, CSf sc r nb0 bl0 y -> CSf (sc ++ [p]) r nb0 bl0 y.
  Hypothesis CSmono_p : forall sc r y, CSf sc r nb0 bl0 y -> CSf sc (r + 1) nb0 bl0 y.
  Hypothesis CSmono_n : forall sc r nb bl b x, CSf sc r nb bl x -> CSf sc r (nb ++ [b]) bl x.
  Hypothesis CSmono_s : forall sc r nb bl b x, CSf sc r nb bl x -> CSf sc r nb (bl ++ [b]) x.

  (* [comment removed for export] *)
  Variables (SP n lo T CTX TOP TID SB PA : Z).
  Let STK := SP + -2136.
  Let SPA := SP + -2136 + -56.
  Let ms := map_size (needed2 n).
  Hypothesis NB : 0 <= n < 2^31.
  Variables (cnt0 sz0 : Z).
  Hypothesis CB0 : 0 <= cnt0 < 2^64.
  Hypothesis SZ0 : 0 <= sz0 < 2^64.
  Hypothesis EN0 : n = cnt0 * sz0.
  Hypothesis FP : from_primary n = false.
  Hypothesis LOIMG : ACEIL <= lo.
  Hypothesis SPL : lo <= SP - 4096.
  Hypothesis SPA16 : SP mod 16 = 0.
  Hypothesis TOP0 : 2^23 <= TOP. Hypothesis TOP1 : TOP <= 2^47. Hypothesis TOP2 : SP + 16 <= 2^47.   (* [comment removed for export] *)
  Hypothesis TIDB : 0 <= TID < 2^31.
  Variables (LO TOPU d : Z).
  Hypothesis LOB : LO <= SP.
  Hypothesis TOPUB : TOP <= TOPU <= 2^64.
  Hypothesis GSB : 0x10007fff9000 <= SB /\ SB mod 4096 = 0 /\ SB + 2^37 + 4096 <= ACEIL.
  Hypothesis GT : (Timg T /\ Tband T) /\ T + 4096 <= ACEIL /\ T mod 4096 = 0.
  Hypothesis GCTX : (0x65f000 <= CTX /\ Pband CTX 0x10000) /\ CTX + 0x10000 <= ACEIL.
  Hypothesis GPA : (0x65f000 <= PA /\ Pband PA 0x800000) /\ PA + 0x800000 <= ACEIL /\ PA mod 4096 = 0.
  Hypothesis GSEP : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "(=.(16.(>.(9.VT,+1000.)VSB,)(>.(9.(9.VSB,(13.+2.+25.))+1000.)VT,))(=.(16.(>.(9.VCTX,+10000.)VT,)(>.(9.VT,+1000.)VCTX,))(=.(16.(>.(9.VCTX,+10000.)VSB,)(>.(9.(9.VSB,(13.+2.+25.))+1000.)VCTX,))(=.(16.(>.(9.VT,+1000.)VPA,)(>.(9.VPA,+800000.)VT,))(16.(>.(9.VCTX,+10000.)VPA,)(>.(9.VPA,+800000.)VCTX,))))))")
(* [comment removed for export] *).
  Hypothesis CST : forall sc r nb bl, crange (CSf sc r nb bl) T 4096.
  Hypothesis CSCTX : forall sc r nb bl, crange (CSf sc r nb bl) CTX 0x10000.
  Hypothesis CSPA : forall sc r nb bl, 0 <= r -> 0x20000 * r <= 0x800000 -> crange (CSf sc r nb bl) PA (0x20000 * r).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable Gl : list (Z * Z) -> Z -> Z -> Prop.
  Variable Gp : list (Z * Z) -> Z -> Prop.
  Let U (r : Z) := PA + 0x20000 * r.
  Hypothesis K_apart_l : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "Psc,(0.(17.$4.$4.))Pr,$4.Pmo,$18.Pa,(2.&40.)Pw,(2.&40.)P,A5.VK,R5.R4.Vnb0,Vbl0,R3.P,(19.$1:.(1;.(1<.(17.(2.&40.)(2.&40.))(1=.(1>.R4.))(1?.(1>.R4.)))R3.R2.)$20.)P,(>.+10000.(21.&40.R3.))P,(>.(9.(21.&40.R5.)(21.&40.R4.))(22.VhAR,))Py,$4.P,(16.A5.VCSf,R:.R9.Vnb0,Vbl0,R1.(16.(=.(>.(23.VAL,)R1.)(?.R1.(24.VAL,)))(16.(=.(>.+7???7000.R1.)(?.R1.+10007???8000.))(=.(>.VPA,R1.)(?.R1.(9.VPA,+800000.))))))(25.(=.(>.(21.&40.R8.)R2.)(?.R2.(9.(21.&40.R8.)(21.&40.R7.)))))")
(* [comment removed for export] *).
  Hypothesis T_large : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "Psc,(0.(17.$4.$4.))Pr,$4.Pmsz,$4.Pmo,$18.Pa,(2.&40.)P,A3.VGl,R5.R4.R3.P,A5.VK,R6.R5.Vnb0,Vbl0,R3.P,(19.$4.(26.(21.&40.R3.)+1000.)=)P,(?.=(21.&40.R4.))P,(>.(9.(21.&40.R5.)R7.)(22.VhAR,))P,(19.$1:.(1;.(1<.(17.(2.&40.)(2.&40.))(1=.(1>.R7.))(1?.(1>.R7.)))R6.(27.&40.R8.))$20.)(=.A5.VK,(1<.(17.$4.$4.)R;.(28.(17.$4.$4.)(29.$4.$4.(21.&40.R7.)R9.)(2:.(17.$4.$4.))))R:.Vnb0,Vbl0,(2;.+22.R7.R9.R8.)(2<.A4.VCSf,(1<.(17.$4.$4.)R;.(28.(17.$4.$4.)(29.$4.$4.(21.&40.R7.)R9.)(2:.(17.$4.$4.))))R:.Vnb0,Vbl0,(21.&40.R7.)R9.))")
(* [comment removed for export] *).
  Hypothesis LEDGER_P : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "Psc,(0.(17.$4.$4.))Pr,$4.Pmo,$18.P,A2.VGp,R3.R2.P,A5.VK,R4.R3.Vnb0,Vbl0,R2.(=.(19.$1:.(1;.(1=.(1>.R3.))(27.&40.A1.VU,R4.)(27.&40.+20000.))$20.)(16.(19.$1:.(2=.(1?.(1>.R3.))(27.&40.A1.VU,R4.)(27.&40.+20000.))$20.)(19.$1:.(1;.(1<.(17.(2.&40.)(2.&40.))(1=.(1>.R3.))(1?.(1>.R3.)))(27.&40.A1.VU,R4.)(27.&40.+20000.))$20.)))")
(* [comment removed for export] *).
  Hypothesis TP_commit : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "Psc,(0.(17.$4.$4.))Pr,$4.Pmo,$18.P,A2.VGp,R3.R2.P,A5.VK,R4.R3.Vnb0,Vbl0,R2.P,(19.$1:.(2=.(1?.(1>.R3.))(27.&40.A1.VU,R4.)(27.&40.+20000.))$20.)(=.A5.VK,R6.(9.R5.+1.)Vnb0,Vbl0,(2>.+32.A1.VU,R5.+20000.R4.)(2<.A4.VCSf,R6.(9.R5.+1.)Vnb0,Vbl0,A1.VU,R5.+20000.))")
(* [comment removed for export] *).
  Hypothesis TP_fresh : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "Psc,(0.(17.$4.$4.))Pr,$4.Pmo,$18.P,A2.VGp,R3.R2.P,A5.VK,R4.R3.Vnb0,Vbl0,R2.P,(19.$1:.(1;.(1<.(17.(2.&40.)(2.&40.))(1=.(1>.R3.))(1?.(1>.R3.)))(27.&40.A1.VU,R4.)(27.&40.+20000.))$20.)(=.A5.VK,R6.(9.R5.+1.)Vnb0,Vbl0,(2?.+32.A1.VU,R5.+20000.R4.)(2<.A4.VCSf,R6.(9.R5.+1.)Vnb0,Vbl0,A1.VU,R5.+20000.))")
(* [comment removed for export] *).
  Hypothesis ROOM_P : forall sc r mo, Gp sc r -> K sc r nb0 bl0 mo -> fixrw_grantable 0x32 (U r) 0x20000 mo.
  (* [comment removed for export] *)
  Hypothesis SCAR_P : forall sc r, Gp sc r -> hole_site AL (CSf sc r nb0 bl0) (K sc r nb0 bl0) (U r) 0x20000.
  (* [comment removed for export] *)
  Hypothesis SEC_APART : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "Psc,(0.(17.$4.$4.))Pr,$4.Pnb,(0.$4.)Pbl,(0.$4.)Pmo,$18.Pp,(17.$4.$4.)P,A5.VK,R6.R5.R4.R3.R2.P,(30.(17.$4.$4.)R2.R7.)(16.(>.(9.(31.$4.$4.R3.)(32.$4.$4.R3.))VSB,)(>.(9.(9.VSB,(13.+2.+25.))+1000.)(31.$4.$4.R3.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Hypothesis K_apart : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "Psc,(0.(17.$4.$4.))Pr,$4.Pnb,(0.$4.)Pbl,(0.$4.)Pmo,$18.Pa,(2.&40.)Pw,(2.&40.)P,A5.VK,R7.R6.R5.R4.R3.P,(19.$1:.(1;.(1<.(17.(2.&40.)(2.&40.))(1=.(1>.R4.))(1?.(1>.R4.)))R3.R2.)$20.)P,(>.+10000.(21.&40.R3.))P,(>.(9.(21.&40.R5.)(21.&40.R4.))(22.VhAR,))Px,$4.P,(16.A5.VCSf,R<.R;.R:.R9.R1.(=.(>.(23.VAL,)R1.)(?.R1.(24.VAL,))))(25.(=.(>.(21.&40.R8.)R2.)(?.R2.(9.(21.&40.R8.)(21.&40.R7.)))))")
(* [comment removed for export] *).
  Variables (Gn Gs : list (Z * Z) -> Z -> list Z -> list Z -> Prop).
  Hypothesis T_node : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "Psc,(0.(17.$4.$4.))Pr,$4.Pnb,(0.$4.)Pbl,(0.$4.)Pmo,$18.Pa,(2.&40.)P,A4.VGn,R6.R5.R4.R3.P,A5.VK,R7.R6.R5.R4.R3.P,(19.$4.(26.(21.&40.R3.)+1000.)=)P,(?.=(21.&40.R4.))P,(>.(9.(21.&40.R5.)(13.+2.+14.))(22.VhAR,))P,(19.$1:.(1;.(1<.(17.(2.&40.)(2.&40.))(1=.(1>.R7.))(1?.(1>.R7.)))R6.(27.&40.(13.+2.+14.)))$20.)(=.A5.VK,R<.R;.(1<.$4.R:.(28.$4.(21.&40.R7.)(2:.$4.)))R9.(2;.+22.R7.(13.+2.+14.)R8.)(2<.A4.VCSf,R<.R;.(1<.$4.R:.(28.$4.(21.&40.R7.)(2:.$4.)))R9.(21.&40.R7.)(13.+2.+14.)))")
(* [comment removed for export] *).
  Hypothesis T_store : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "Psc,(0.(17.$4.$4.))Pr,$4.Pnb,(0.$4.)Pbl,(0.$4.)Pmo,$18.Pa,(2.&40.)P,A4.VGs,R6.R5.R4.R3.P,A5.VK,R7.R6.R5.R4.R3.P,(19.$4.(26.(21.&40.R3.)+1000.)=)P,(?.=(21.&40.R4.))P,(>.(9.(21.&40.R5.)(13.+2.+17.))(22.VhAR,))P,(19.$1:.(1;.(1<.(17.(2.&40.)(2.&40.))(1=.(1>.R7.))(1?.(1>.R7.)))R6.(27.&40.(13.+2.+17.)))$20.)(=.A5.VK,R<.R;.R:.(1<.$4.R9.(28.$4.(21.&40.R7.)(2:.$4.)))(2;.+4022.R7.(13.+2.+17.)R8.)(2<.A4.VCSf,R<.R;.R:.(1<.$4.R9.(28.$4.(21.&40.R7.)(2:.$4.)))(21.&40.R7.)(13.+2.+17.)))")
(* [comment removed for export] *).
  Hypothesis ROOM_n : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "Psc,(0.(17.$4.$4.))Pr,$4.Pnb,(0.$4.)Pbl,(0.$4.)Pmo,$18.P,A4.VGn,R5.R4.R3.R2.P,A5.VK,R6.R5.R4.R3.R2.(33.(2.&40.)La,(2.&40.)(34.VhAR,+22.(13.+2.+14.)R4.R1.))")
(* [comment removed for export] *).
  Hypothesis ROOM_s : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "Psc,(0.(17.$4.$4.))Pr,$4.Pnb,(0.$4.)Pbl,(0.$4.)Pmo,$18.P,A4.VGs,R5.R4.R3.R2.P,A5.VK,R6.R5.R4.R3.R2.(33.(2.&40.)La,(2.&40.)(34.VhAR,+4022.(13.+2.+17.)R4.R1.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Variables (can : word) (dd madv : byte).
  Hypothesis PZ : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "Psc,(0.(17.$4.$4.))Pr,$4.Pnb,(0.$4.)Pbl,(0.$4.)PA,$4.Pw,$4.P,(19.$4.(26.R2.+8.)=)P,(19.$4.(26.R2.+8.)=)P,(>.+8.R3.)P,(>.R4.(13.+2.+28.))P,(16.(=.(>.+8.R6.)(=.(>.R6.+7???7??8.)(>.(9.R6.R5.)+7???8000.)))(=.(>.+10007???8000.R6.)(=.(>.+10007???8008.(9.R6.R5.))(=.(>.R6.+7??????????8.)(>.(9.R6.R5.)+800000000000.)))))(35.VhAR,A4.VCSf,R;.R:.R9.R8.A4.VK,R;.R:.R9.R8.R7.R6.Vcan,Vdd,Vmadv,)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Hypothesis MOD_DIE : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "PCS,P,$4.SpPgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)Pra,(2.&40.)PSP0,$4.PF,(36.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Paddr,$4.Psize,$4.Plo0,$4.Pfr,(0.(2.&8.))P,(37.VAL,R21.)P,(=.(>.=R5.)(?.R5.(13.+2.+2?.)))P,(=.(?.=R5.)(>.R5.(13.+2.+28.)))P,(38.$<.R8.(9.R<.-60.)(28.$39.(3:.(27.&40.+32.))(28.$39.(3;.#2<.R4.)(28.$39.(3<.R1:.)(28.$39.(3<.R1;.)(28.$39.(3<.R1<.)(28.$39.(3<.R1=.)(28.$39.(3<.R1>.)(28.$39.(3<.R=.)(2:.$39.))))))))))P,(3=.R9.)P,(3>.$<.R:.R7.(9.R>.-60.))P,(>.+65?000.R8.)P,(>.R9.(3?.R10.$40.))P,(>.R11.(13.+2.+3?.))P,(6.(28.(17.$4.$4.)(29.$4.$4.R;.R12.)(2:.(17.$4.$4.)))R?.R>.)P,(;.$<.R10.R?.)P,(41.$<.R10.)P,(2<.R2=.R>.(3?.R15.R>.))(42.$<.VAL,R2>.(43.R14.$44.)(45.(27.&40.(3?.(13.+2.+40.)+<.))R16.R2=.R2<.R2;.R2:.R29.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R15.R14.R11.R10.R12.))")
(* [comment removed for export] *).

  Ltac facts :=
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L12339200442.3 L13925108942.2 L13925138262.3 L17120848823.0 L18926759668.86L18928824262.84L18930958230.85L25047882783.4 L36644267936.2 L3822649421.3  L3822711765.2  L3823029717.2  L38599263692.2 L38599474124.2 L38599510100.3 L40040019413.3 L40040056397.2 L44282459030.3 L65117206605.2 L65117517269.3 L65117521485.2 L8646232868.3  00000:00A00B00C00]01701Q01Y01_01`01a01b01i01j01k01l02302=02D02E02F02PS1n2ms3MSZS1n3N2BFSS3hAR2SP1n1T2SB2PA3STK3SPAS3hAR2SP1n1T2SB2PA3STK3SPAS3hAR2SP1n1T2SB2PA3STK3SPAS1n1H2H0S1n2NBFFFS1n3RNBFFFS1n3N2BS1n2ms3MSZS1n3RNBFFS1n2ms3MSZ". (* [comment removed for export] *)
  #[using="hAR SP T SB PA STK SPA NB FP"] Lemma sec_n : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "(=.(>.+?<01.Vn,)(=.(19.$4.(46.Vn,)Vn,)(=.(19.$4.(47.Vn,)+800.)(=.(19.$4.(48.Vn,)(9.(49.Vn,)+1000.))(=.(=.(>.Vn,(49.Vn,))(>.(49.Vn,)(9.Vn,+7.)))(=.(19.$4.(26.(49.Vn,)+8.)=)(=.(=.(?.+10000.(48.Vn,))(>.(48.Vn,)(9.Vn,+1007.)))(=.(=.(>.(9.(48.Vn,)+1000.)Vms,)(?.Vms,(9.(48.Vn,)+2000.)))(=.(19.$4.(26.Vms,+1000.)=)(19.$4.(26.(48.Vn,)+8.)=))))))))))")
(* [comment removed for export] *).
  Proof.
    dpose (sec_sizes n ltac:(clear - NB; lia) FP) as (NLO & NFX & RZ & N2E & RNB & RN8 & N2B).
    assert (MSZ : needed2 n + 4096 <= ms < needed2 n + 8192 /\ ms mod 4096 = 0).
    { subst ms. unfold map_size. pose proof (Z.div_mod (needed2 n + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (needed2 n + 4095) 4096 ltac:(lia)).
      split; [clear - H H0 N2B; lia|]. rewrite Z.add_mod, Z_mod_mult, Z.add_0_l by lia. reflexivity. }
    repeat match goal with |- _ /\ _ => split end; try assumption; try (clear - MSZ; lia); try (clear - N2B; lia); try (clear - RNB; lia).
    rewrite N2E. rewrite Z.add_mod, RN8 by (clear; lia). reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L64447787965.7800000MS3hAR2SP1n1T2SB2PA3STK3SPA2ms". (* [comment removed for export] *)
  #[using="hAR SP n T SB PA STK SPA ms"] Lemma DIE_NEED_ge : 368 <= DIE_NEED. Proof. unfold DIE_NEED. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="CSPA"] Lemma CSPA' : forall sc r, 0 <= r -> 0x20000 * r <= 0x800000 -> crange (CSf sc r nb0 bl0) PA (0x20000 * r).
  Proof. intros sc r. apply CSPA. Qed.


  Let STK' := SP + -2136.
  Let SPA' := SP + -2136 + -56.
  Let ms' := map_size (needed2 n).

  (* [comment removed for export] *)
  Definition msec_cwin (a r' ncks : Z) : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "(28.(17.$4.$4.)(29.$4.$4.Vlo,VSP,)(28.(17.$4.$4.)(29.$4.$4.$4:.$4;.)(28.(17.$4.$4.)(29.$4.$4.(9.VT,+:?0.)(9.VT,+;08.))(28.(17.$4.$4.)(29.$4.$4.(9.VT,+;58.)(9.VT,+;60.))(28.(17.$4.$4.)(29.$4.$4.O3.(9.O3.Vms',))(28.(17.$4.$4.)(29.$4.$4.(9.+7???8000.(4<.O3.+8.))(9.(9.+7???8000.(4<.O3.+8.))(4<.Vms',+8.)))(28.(17.$4.$4.)(29.$4.$4.(9.VT,+<60.)(9.VT,+<61.))(28.(17.$4.$4.)(29.$4.$4.(9.VT,+;38.)(9.VT,+;48.))(28.(17.$4.$4.)(29.$4.$4.(9.$4=.+70.)(9.$4=.+2=0.))(28.(17.$4.$4.)(29.$4.$4.(9.VPA,(4>.+8.O1.))(9.VPA,(4>.+8.(4>.+4000.O2.))))(2:.(17.$4.$4.))))))))))))")
(* [comment removed for export] *).

  Definition msec_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (sc : list (Z * Z)) (r N tf ncks : Z) (ps : list word) (js1 js2 : word) (m0 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "Lcf,$4?.(33.$50.Lms'',$50.(33.$18.Lmo',$18.(33.$4.Lres,$4.(33.(0.(17.$4.$4.))Lsc',(0.(17.$4.$4.))(33.$4.Lr',$4.(33.(0.$4.)Lnb',(0.$4.)(33.(0.$4.)Lbl',(0.$4.)(33.(2.&40.)Lt0,(2.&40.)(33.(2.&40.)Lt1,(2.&40.)(33.(2.&40.)Lt2,(2.&40.)(33.(2.&40.)La1,(2.&40.)(33.(2.&40.)La2,(2.&40.)(33.(2.&40.)La3,(2.&40.)(33.(2.&40.)La4,(2.&40.)(33.(2.&40.)La5,(2.&40.)(33.(2.&40.)La6,(2.&40.)(33.(2.&40.)La7,(2.&40.)(33.(2.&40.)Lt3,(2.&40.)(33.(2.&40.)Lt4,(2.&40.)(33.(2.&40.)Lt5,(2.&40.)(33.(2.&40.)Lt6,(2.&40.)(33.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(=.(19.$4?.R17.(51.R16.R15.))(=.(19.$50.R16.(52.(53.O19.(27.&40.VSP,)O18.(27.&40.$54.)R?.R>.R=.O17.O16.(27.&40.R14.)R<.R;.R:.R9.R8.R7.R6.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.R5.R4.R3.R2.)O;.(55.O19.)O:.(56.(2.&40.))R1.(57.$<.)))(=.A5.VK,R13.R12.R11.R10.R15.(=.(58.R1.R15.)(=.(;.$<.O1.R1.)(=.(41.$<.R1.)(=.(3>.$<.R1.Vlo,VSP,)(=.Px,$4.P,A5.VCSf,O9.O8.Vnb0,Vbl0,R1.A5.VCSf,R15.R14.R13.R12.R2.(=.(38.$<.R1.(9.VT,+<60.)(28.$39.(59.(27.&8.=))(2:.$39.)))(16.(=.(19.$4.R14.=)(=.(19.(0.(17.$4.$4.))R13.O9.)(=.(19.$4.R12.O8.)(=.(19.(0.$4.)R11.Vnb0,)(=.(19.(0.$4.)R10.Vbl0,)(=.(6.(28.(17.$4.$4.)(29.$4.$4.Vlo,VSP,)(28.(17.$4.$4.)(29.$4.$4.(9.VT,+<60.)(9.VT,+<61.))(28.(17.$4.$4.)(29.$4.$4.$5:.(9.$5:.+1.))(28.(17.$4.$4.)(29.$4.$4.$5;.(9.$5;.+4.))(2:.(17.$4.$4.))))))O1.R1.)(=.(38.$<.R1.$5:.(28.$39.(59.(27.&8.+1.))(2:.$39.)))(38.$<.R1.$5;.(28.$39.(3:.(27.&40.+<.))(2:.$39.))))))))))(33.$4.La,$4.(33.$4.LN',$4.(33.$4.Ltf',$4.(33.$4.Lid,$4.(33.$4.Lb1',$4.(33.(2.&8.)Lpgb,(2.&8.)(33.(2.&40.)Lj0,(2.&40.)(33.(2.&40.)Lj1,(2.&40.)(33.(2.&40.)Lj2,(2.&40.)(33.(2.&40.)Lj4,(2.&40.)(33.(0.(2.&40.))Lrest',(0.(2.&40.))ZAB,$4.(9.R;.+1000.)ZUB,$4.(9.R1.(47.Vn,))ZCHB,$4.(9.(9.R2.(47.Vn,))-10.)Zrd,$4.(4>.(4<.(46.Vn,)+8.)+8.)Zr8,$4.(4>.(4<.(9.(46.Vn,)+7.)+8.)+8.)ZSHA,$4.(9.+7???8000.(4<.R10.+8.))ZS1,$4.(9.+7???8000.(4<.R6.+8.))ZSUB,$4.(9.+7???8000.(4<.R6.+8.))ZPGS,$4.(9.+7???8000.(5<.(9.R7.R5.)+3.))ZS2,$4.(9.+7???8000.(4<.(9.R8.R5.)+8.))Zk2,$4.(4<.(3?.(9.R15.Vms',)(9.R9.R6.))+8.)(=.(19.$4.R2:.R:.)(=.(19.(0.(17.$4.$4.))R29.(1<.(17.$4.$4.)O9.(28.(17.$4.$4.)(29.$4.$4.R16.Vms',)(2:.(17.$4.$4.)))))(=.(16.(19.$4.R28.O8.)(=.(19.$4.R28.(9.O8.+1.))(19.$4.O5.(4>.+4000.O8.))))(=.(>.(9.O5.+1.)(4>.+4000.R28.))(=.(>.+65?000.R16.)(=.(19.$4.(26.R16.+1000.)=)(=.(>.(9.R16.Vms',)(22.VhAR,))(=.(16.(>.(9.R16.Vms',)+7???7000.)(>.+10007???8000.R16.))(=.(16.(>.(9.R16.Vms',)VPA,)(>.(9.VPA,+800000.)R16.))(=.(16.(>.(9.R16.Vms',)VT,)(>.(9.VT,+1000.)R16.))(=.(16.(>.(9.R16.Vms',)VCTX,)(>.(9.VCTX,+10000.)R16.))(=.Py,$4.P,A5.VCSf,O9.O8.Vnb0,Vbl0,R1.(25.(=.(>.R18.R2.)(?.R2.(9.R18.Vms',))))(=.(2<.A4.VCSf,R29.R28.R27.R26.R16.Vms',)(=.Px,(2.&40.)Zy,$4.(21.&40.R1.)P,(5=.(5>.R18.R2:.O5.)R1.)P,Pk,$4.P,(=.(>.=R1.)(?.R1.(10.(11.$4.R2;.))))(25.(=.(>.(12.R2<.R2.)R4.)(?.R4.(9.(12.R2<.R2.)(13.+2.+14.)))))P,Pj,$4.P,(=.(>.=R1.)(?.R1.(10.(11.$4.R2;.))))(25.(=.(>.(14.R2<.R2.)R5.)(?.R5.(9.(14.R2<.R2.)(13.+2.+17.)))))(19.(3.(2.&8.))A1.R1<.R5.A1.O1.R5.)(=.(:.VhAR,R17.R15.R27.R14.R26.)(=.(5?.A4.VCSf,R29.R28.R27.R26.R27.R26.)(=.(60.R17.)(=.(=.(>.+1.R13.)(>.R13.R15.))(=.(=.(>.O7.R15.)(>.R15.(9.O7.+1.)))(=.(=.(>.O6.R14.)(>.R14.(9.O6.(4>.+2.(9.Vd,+3.)))))(=.(>.(3?.R14.(4>.+1?.(4<.R14.(13.+2.+14.))))(9.(3?.O6.(4>.+1?.(4<.O6.(13.+2.+14.))))(9.Vd,+3.)))(=.(33.(0.$4.)Lsn,(0.$4.)(33.(0.$4.)Lsb,(0.$4.)(=.(19.(0.$4.)R29.(1<.$4.Vnb0,R2.))(=.(19.(0.$4.)R28.(1<.$4.Vbl0,R1.))(=.(61.$4.Lb,$4.Px,$4.P,A5.VCSf,R2=.R2<.Vnb0,Vbl0,R1.(25.(=.(>.R3.R2.)(?.R2.(9.R3.(13.+2.+14.)))))R2.)(61.$4.Lb,$4.Px,$4.P,A5.VCSf,R2=.R2<.Vnb0,Vbl0,R1.(25.(=.(>.R3.R2.)(?.R2.(9.R3.(13.+2.+17.)))))R1.))))))(=.(38.$<.R17.R16.(28.$39.(3<.(27.&40.R16.))(28.$39.(3<.(27.&40.Vms',))(28.$39.(3<.(27.&40.(48.Vn,)))(28.$39.(3<.(27.&40.O5.))(2:.$39.))))))(=.(38.$<.R17.(9.R16.+20.)(28.$39.(3;.(62.+?>0.)(63.(2.&8.)(27.&8.=)(62.+?>0.)))(2:.$39.)))(=.(38.$<.R17.R;.(28.$39.(3<.(27.&40.$64.))(28.$39.(3<.(27.&40.R9.))(2:.$39.))))(=.(38.$<.R17.(9.R;.+10.)(28.$39.(3;.(62.+7>0.)(63.(2.&8.)(27.&8.=)(62.+7>0.)))(2:.$39.)))(=.(38.$<.R17.R9.(28.$39.(59.(27.&8.$65.))(28.$39.(59.(27.&8.R12.))(28.$39.(66.(27.&40.=))(28.$39.(3:.(27.&40.(46.Vn,)))(28.$39.(3<.(27.&40.(67.(4>.VTID,(13.+2.+20.))R13.)))(2:.$39.)))))))(=.(19.$4.(68.R12.+3.)+1.)(=.(=.(>.=R12.)(?.R12.+100.))(=.(38.$<.R17.R:.(28.$39.(3;.(62.(3?.(9.R16.Vms',)R:.))(63.(2.&8.)(27.&8.=)(62.(3?.(9.R16.Vms',)R:.))))(2:.$39.)))(=.(38.$<.R17.R6.(28.$39.(3;.#200.(63.(2.&8.)(27.&8.+?:.)#200.))(2:.$39.)))(=.(38.$<.R17.R5.(28.$39.(3;.#100.(63.(2.&8.)(27.&8.+?:.)#100.))(2:.$39.)))(=.(38.$<.R17.R4.(28.$39.(3;.(62.(4<.R8.+8.))(63.(2.&8.)(27.&8.=)(62.(4<.R8.+8.))))(2:.$39.)))(=.(38.$<.R17.R3.(28.$39.(59.(69.Vn,R11.))(2:.$39.)))(=.(38.$<.R17.R2.(28.$39.(3;.(62.R1.)(63.(2.&8.)(27.&8.+?:.)(62.R1.)))(2:.$39.)))(=.(38.$<.R17.(9.VT,+:?0.)(28.$39.(3<.R10.)(28.$39.(3<.R?.)(28.$39.(3<.R>.)(2:.$39.)))))(=.(38.$<.R17.(9.VT,+;58.)(28.$39.(3<.R=.)(2:.$39.)))(=.(6:.R17.(4>.+4000.R28.)(9.O5.+1.)(27.&8.=)=)(=.(6;.$<.R17.VPA,(1<.(2.&40.)O4.(28.(2.&40.)(27.&40.R16.)(2:.(2.&40.)))))(=.(6;.$<.R17.(9.VPA,(4>.+8.(9.O5.+1.)))R<.)(=.(19.$4.(10.(11.(2.&40.)R<.))(3?.(3?.(4>.+4000.R28.)O5.)+1.))(38.$<.R17.(9.VT,+;38.)(28.$39.(3<.(27.&40.(9.(21.&40.O3.)+1.)))(28.$39.(3<.(27.&40.(9.(21.&40.O2.)Vms',)))(2:.$39.))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "03c0@L10307921259.3  L10411448474.2  L10411715762.41 L10655081154.7  L10724981692.5  L11188449489.2  L11526216857.41 L11552630106.46 L11729460503.46 L11729460503.48 L11748760990.46 L11963168791.41 L12044386942.41 L12337219384.41 L12862884641.2  L13028470563.46 L13415130216.1  L13538905239.0  L13927381460.41 L14000275181.50 L14473091822.41 L14547012368.0  L14790099685.46 L15124624562.46 L15508334621.1  L15514365477.53 L15603774829.1  L15795332857.1  L16069058845.46 L16198262312.1  L16924645992.1  L16992530622.1  L17120848823.0  L17702421713.445L18138412583.46 L18242311618.46 L18302958969.1  L19131546391.0  L19723288167.7  L20970275072.46 L21031402204.50 L21031402204.51 L21303659476.53 L21778056205.46 L2189761147.7   L22111872012.46 L22312243734.3  L22706556809.4  L23165266403.41 L23343287261.0  L23534125650.41 L23538177192.7  L23803517183.0  L23898603878.1  L24148960601.1  L24477532539.4  L24759906015.49 L24888640626.2  L24897143244.3  L25013901401.46 L25578703086.46 L25703561724.1  L25982463935.8  L25984553605.11 L25984553605.9  L26094996503.0  L26234493799.53 L26448404441.46 L26937647705.1  L27098544669.46 L27466439871.3  L27602168912.41 L27674889058.46 L27848808849.2  L27850791182.18 L28573892092.5  L28762839709.0  L2934734959.18  L29492715482.53 L2965218324.46  L2978961816.0   L29836529785.1  L30105183150.6  L30131412550.4  L30176908071.46 L30278173202.1  L30435077518.7  L30460553082.46 L30573236684.7  L30663996904.1  L31062529309.1  L31698219930.41 L31949200002.1  L32321905461.8  L33010442966.53 L33736009865.4  L3389960226.4   L33998387.1     L34301640341.14 L34301640341.8  L34308191119.9  L34326450205.4  L34626666713.1  L3535991410.5   L3543818163.1   L35898177818.1  L3597417215.0   L36075687453.0  L36176875184.46 L36415714444.3  L36466722475.46 L36466722475.48 L36644267936.2  L36841451887.6  L36841451887.8  L37041841271.46 L37331538387.6  L3735167083.2   L3735167087.3   L37637199976.0  L38235734261.1  L3826744053.41  L38442651814.2  L38550656074.53 L38630853356.11 L38630853356.9  L38637156310.8  L38653465194.50 L38653465194.51 L39031256621.53 L39461273556.50 L39563368086.8  L39633675993.46 L39917037827.1  L40099728360.1  L40346103378.18 L40346277114.46 L40348180955.41 L4082070957.47  L41013459011.41 L4142414455.0   L41641425437.46 L41770846504.1  L42218248895.5  L42350675462.53 L42554935773.0  L43254444199.8  L4331235796.41  L43609532904.1  L44070693117.48 L44255427093.53 L44280509716.41 L44345069824.18 L44681781299.10 L4475740951.0   L44876607696.3  L45095732027.3  L45311807539.41 L45736542467.41 L46071731361.10 L46253703355.7  L4849962516.4   L49644866280.1  L49661812247.46 L49661812247.48 L49989462439.10 L50191011140.46 L50436346076.50 L50436346076.51 L51245445121.1  L51522211912.46 L51568894470.41 L51723252852.1  L52077530728.41 L5231564960.46  L52324132761.48 L52587762724.5  L52694201704.1  L5277303987.46  L5295645394.41  L52985841638.46 L53781746718.53 L53983606775.0  L5429770831.4   L5518817004.0   L55271404928.41 L55493475438.41 L55588686165.0  L55798853586.46 L55798853586.48 L55899845783.3  L56263543455.41 L56735592241.18 L56944303196.4  L57461980763.46 L57492440930.46 L57628700040.5  L5796862057.0   L58825343241.4  L58829355425.41 L58852693222.9  L58877046873.47 L58877250289.18 L5937835007.0   L59837619752.1  L60236645543.46 L60432055545.1  L60779458884.0  L60850359937.5  L60862592638.46 L61193383935.0  L61484467655.41 L62728963852.10 L629353612.47   L629353612.49   L63404914589.0  L63423827809.7  L63483193685.41 L63489899714.49 L63635226190.46 L64406245300.8  L65157263119.46 L65271643703.0  L65568526750.46 L6600342017.1   L66693385734.46 L66763458562.7  L67407106969.53 L67871595483.46 L67892594823.47 L6828212339.46  L68508395546.1  L7673915391.0   L7736816859.46  L7799702881.1   L7924813449.53  L8201234081.0   L8469824738.1   L8500347500.0   L8936406240.50  L9036595869.46  L9184761768.1   L9391694955.1   00000:00@01F01U01d01k02H02l02m04>05>05[06a07<07C07d07g07h08C09809T09U0:00:G0:L0:n0;20;50;L0;P0;S0;W0;X0=10=H0>30>60>70>J0>a0?Q0@b0Bb0D10DG0Dd0Dn0E:0EW0EX0F^0G70G80G;0G>0GK0HT0HU0HY0I40IP0IS0Ic0J<0JJ0JK0LK0Lf0Li0M@0MJ0Mf0N?0NF0OB0OP0OQ0PM0Po0QJ0QK0QN0Q^0Qk0RB0RF0R\0S30SA0SD0SI0TO0TS0Ti0UK0UV0Ue0Ui0VS0Vl0WK0WY0W\0Wo0X30X70X80X90XW0Xa0Xb0Z70Z=0ZO0Zk0[P0[`0[h0[i0[j0[n0\J0\Q0]70]S0]m0^A0_D0`l0aK0b`0c60cQ0cU0cX0dT0e;0e\0fC0fc0fd0g;0g?0gR0h70h80hI0hg0hj0ik0jP0jk0kg0l=0l>0lH0lS0m20mQ0m_0n30n>0nA0nB0oS0oi10F11[13013313J13h13m14N14e15R15c15f16I17O18Z19919:19C19D19h1:D1:E1:F1;F1;M1;o1<k1=41=N1=g1>51>61>E1>j1?D1?k1@g1@h1@l1AC1AF1AG1AY1B?1B@1B\1C71C81C91C:1CI1DO1EX1F21FC1Ff1Fg1Gg1Gj1Hj1I81IZ1J51J^1K;1K?1K@1K[1K`1LF1LG1LK1LL1Ml1NC1NG1NJS3bl01j2HjS1T2T0S3hAR2SP1n1T3CTX2PA2ms4STK'4SPA'1r4ncks3HNC2T03CX03PA03N2B3MSZ2r'4HR'0S3nb01k1A2n02n2S1n1T2ms1a4ABT0S3bl01jS3hAR2SP1n2ms4STK'4SPA'2qm2DMS3hAR2SP1n2ms4STK'4SPA'1a2qa2qm1H2H2FS3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks4SEP41a2r'2qa2qm2qx3GEO3H153H203H223H24S3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEO3H16S3hAR2SP1n2ms4STK'4SPA'1a3ACES3hAR2SP1n1T3CTX2PA2ms4STK'4SPA'1r4ncks3HNC2T03CX03PA03N2B3MSZ2r'4HR'0S3hAR2SP1n2ms4STK'4SPA'3MSZS3nb01kS3hAR2SP1n2PA2ms4STK'4SPA'2r'3H20S1TSS3hAR2SP1n2ms4STK'4SPA'3N2BS3hAR2SP1n2lo2ms4STK'4SPA'1A1k2H12H91T2H23H153CTX3H16S3hAR2SP1n2ms4STK'4SPA'4SPAESS3hAR2SP1n2ms4STK'4SPA'3H10S3hAR2SP1n2ms4STK'4SPA'S3CTXS3hAR3nb02SP1n1T2ms4STK'4SPA'1k2Y2S2SPS1TS3hAR2SP1n2ms4STK'4SPA'S2SPS1TS2qaSS3hAR2SP1n1T2SB2PA3STK3SPA2ms4STK'4SPA'3ms'2tf2ps4rest2ws4HL301a5rest'3tf'1A2sz2A'1k1H2H0S3hAR2SP1n2ms4STK'4SPA'S3hAR2SP1n2lo2PA2ms4STK'4SPA'2r'2H73H183H24S1TSS2SP2lo1T1A1k2H12H2S3hAR2SP1n2ms4STK'4SPA'S3hAR2SP1n2ms4STK'4SPA'1a1A1k2H12H42lo2H52H93H10S3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm3ABT2qx3GEO1A1k2H12H22H43ABCS3hAR3bl02SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEO1j1X2Y12Y22Y32Y41H2H12H02H22H32H42H53H153H163H193H203H223H213H24S3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEO1H2H12H22H33H223H24S3hAR2lo3CTX5LOIMG3CX1S3hAR2SP1n1T2ms4STK'4SPA'3H13S1n2NB3N2BS2SP2lo1x2HxS3hAR2SP1n2ms4STK'4SPA'2qx2DXSS3hAR2SP1n1T3CTX2PA2ms4STK'4SPA'1r4ncks3HNC2T03CX03PA03N2B3MSZ2r'4HR'0S3hAR2SP2lo1T5LOIMG2T02T1SS1TS1TS3hAR3nb'1k1HS3hAR3bl02SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEO2jj1Y3H24SS2SPS3hAR2SP1n2ms4STK'4SPA'3H10S3hAR2SP1n2ms4STK'4SPA'1a2H2S1TS3hAR1T2T01A1k1HS3hAR1T2PA4SEP41A1k2H12H2S3hAR1T1A1k2H2SS3hAR3nb02SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEO1k1X2Y12Y22Y32Y41H2H12H02H22H32H42H53H153H163H193H203H223H213H24S3hAR2SP1n2ms4STK'4SPA'3H10S1TS3hAR2SP1n2ms4STK'4SPA'S3nb01k2HkS3hAR2SP1n2ms4TOP24STK'4SPA'S3hAR2SP1n1T2ms4STK'4SPA'S2SP2loS3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEOS2SP2lo1T1x2HxSS3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEOS3hAR3bl02SP1n2ms4STK'4SPA'1a1j2Y1S3hAR2SP1n2ms4STK'4SPA'3H10SS1TS3nb01n2ms1a1k1XS3hAR3bl'1j1HS3hAR2SP1n2ms4STK'4SPA'S2SPS3hAR2lo3CTX5LOIMG3CX1S3hAR2SP1n2ms4STK'4SPA'S3hAR1T3CTX2TCS1TS3CTXS3hAR2SP1n1T3CTX2PA2ms4STK'4SPA'1r4ncks3HNC2T03CX03PA03N2B3MSZ2r'4HR'0S2r'S3hAR3nb02lo5LOIMG1k1XS3hAR3bl02SP1n1T2ms4STK'4SPA'1j2Y2S1T3bl'1j1YS2PA1r4ncks3HNCS2SPS1n2ms1a2qa2qm4SHAE3MS81A2sz2O61x2X12X22XRS1T1A2sz2O31x2X12X22XR2O4S3nb'1A2sz1x2X12X22XR1k1H3bl'1jS1n2ms3N2B3MSZS1TS2PA1r4ncks3HNC3HNRS2SPS2SPSSS3hAR2SP1n2PA2ms4STK'4SPA'3H20S3bl'1j2HjFS3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks4SEP41a2r'3ABP2qa2qm2qx3GEO3H153H203H223H24S1n2NBS2SP2lo4SPA'1A1k1HS3hAR2SP2lo5LOIMG4SPA'1A1k1HS3hAR2SP1n2PA2ms4STK'4SPA'2r'3H183H24S3bl01n2ms1a1j1XS2SP3SPHFSS2loS3hAR2SP1n2ms4STK'4SPA'1a2A0S2r'2R0S3hAR3bl02SP1n2ms4STK'4SPA'2qa2qm1j2Y4S3hAR2lo2PA5LOIMG3PA11A1k2H2S3hAR2lo1T5LOIMG2T11A1k2H2S3hAR2lo5LOIMG1A1k1HS3hAR2SP1n2PA2ms4STK'4SPA'4ncks2r'1A1k2H13H223H232lo2H93H103H203H26S3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks4SEP41a2r'2qa2qm2qx3GEO1A1k2H12H23H173H223H243H233H264SEP53H21S3hAR3nb02SP1n2ms4STK'4SPA'1k1XS3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEO1A1k2H12H22H93H103H183H19S3hAR3bl02lo5LOIMG1j1XS3hAR2SP1n2ms4STK'4SPA'3H10S2PAS1TS3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEOS3hAR2SP1n2ms4STK'4SPA'4ncks2r'3H213H23S3hAR2SP1n2ms4STK'4SPA'1r2r'4HR'0S3hAR2SP1n2ms4STK'4SPA'1a2qa2qm1H2H12H3S3hAR2SP1n2lo2ms5LOIMG4STK'4SPA'SS3hAR2SP1n2ms4STK'4SPA'S2SPS2PA1r4ncks3HNC3HNRS3hAR3bl02SP1n2lo2ms4STK'4SPA'1j1X2H7SS3hAR3bl01T1j1Y1XS3hAR2SP1n2PA2ms4STK'4SPA'3PA1S1TS3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEO1x2O1S3hAR3nb02SP1n2lo2ms4STK'4SPA'1k1X2H7S3hAR2SP1n2ms4STK'4SPA'3MSZS3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEOS3nb01k1A1w2H12H22n11lSS3nb'1k2HkS2SP2lo3SPLS3hAR2SP1n2ms4STK'4SPA'1a2qa2DAS3hAR2SP1n3CTX2ms4STK'4SPA'3CX1S1A1w2H12H22HwS1A2sz2O21x2X12X22XRS1T3nb'1k1YS1TFS3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks4SEP41a2r'2qa2qm2qx3GEO3H153H203H223H24S3bl01j1A1w2H12H22n11lS3hAR2SP1n1T2ms4STK'4SPA'3H12S3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEO1A1k2H12H23H182H93H103H15S3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks2TC1a2r'2qa2qm2qx3GEO1A1k2H12H23H173H193H21S1TS3hAR2SP1n2ms4STK'4SPA'S3hAR2SP1n2lo2ms3SPL4STK'4SPA'S3CTXS3hAR2SP1n2ms4STK'4SPA'1r2r'4HR'0S3hAR2SP1n2ms4STK'4SPA'S3hAR2SP1n2PA2ms4STK'4SPA'4ncks2ps3LPS2r'3H23S1n3CTX2ms1a4ABC0S1TS3hAR2SP1n2PA2ms4STK'4SPA'4ncks3H21S3hAR2SP1n1T3CTX2PA2ms4STK'4SPA'1r4ncks3HNC2T03CX03PA03N2B3MSZ2r'4HR'0S3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEO1H2H12H22H33H15S3hAR3bl02SP1n2ms4STK'4SPA'1j1XSS2SP4TOP2SS3hAR2SP1n2ms4STK'4SPA'4ncks2r'4NCK'S3hAR2SP1n2ms4STK'4SPA'4STKESFS3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm3ABT2qx3GEOS1A1k1HS3hAR2SP1n2ms4STK'4SPA'1r4ncks3HNCS3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEOS2SP1q2HqS3hAR2SP1n2ms4STK'4SPA'2H9S3hAR2SP1n1T2ms4STK'4SPA'S2SP2lo1T1x2HxSS1r3HNR2r'4HR'0S3hAR2SP1n2ms4STK'4SPA'1r3HNR2r'4HR'0S2SP2lo1A2sz2O11x2X12X22XRS3hAR2SP1n2ms4STK'4SPA'1a2qa1H2H25HIGHBS3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEOSS2SPS3hAR2SP1n2ms4STK'4SPA'S1TSS1r4ncks2HR2r'3HR'S3hAR2SP1n2PA2ms4STK'4SPA'4ncks2r'3H23SS3hAR2SP1n1T2ms4STK'4SPA'2T1S1n2ms1a1A2sz2O51x2X12X22XRFFSS3bl01j1A2n02n2S3hAR2SP1n1T3CTX2PA2ms4STK'4SPA'1r4ncks3HNC2T03CX03PA03N2B3MSZ2r'4HR'0S3hAR3nb02SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEO2kk1Y3H24S3hAR2SP1n2ms4STK'4SPA'2H9S3hAR3nb01T1k1Y1XS3hAR2SP1n2lo1T2ms4STK'4SPA'2H73H13SS3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEO3H16S1TS3hAR2SP1n2lo1T3CTX2PA2ms4STK'4SPA'1r4ncks1a2r'2qa2qm2qx3GEO3H16S3hAR1T3CTX2TCS3hAR3nb02SP1n2ms4STK'4SPA'1a1k2Y1S3hAR2SP1n2ms4STK'4SPA'3H10S3hAR2SP1n2ms4STK'4SPA'1a4LOWB2qa1H2H52H3S3hAR2SP1n2lo2ms4STK'4SPA'2H7S2SPSS3hAR2SP1n2ms4STK'4SPA'3H10S3CTXS3hAR3nb02SP1n2ms4STK'4SPA'2qa2qm1k2Y4SS2qmSS3hAR2SP1n2ms4STK'4SPA'1a2qa2qm1A1k2H11H2H42lo2H32H52H93H101T3CTX2PA1r4ncks2r'2qx3GEO2H23H173H21S3hAR2SP1n2ms4STK'4SPA'S2SPS1T". (* [comment removed for export] *)
  #[using="AL IMG ALWF ASB CSOKf KL CSf_noshadow CSmono_l CSmono_p CSmono_n CSmono_s STK SPA ms NB CB0 SZ0 EN0 FP LOIMG SPL SPA16 TOP0 TOP1 TOP2 TIDB LOB TOPUB GSB GT GCTX GPA GSEP CST CSCTX CSPA U K_apart_l T_large LEDGER_P TP_commit TP_fresh ROOM_P SCAR_P SEC_APART K_apart T_node T_store ROOM_n ROOM_s PZ MOD_DIE STK' SPA'"] Theorem calloc_sec_cfgS : ltac2:(CDefT.buildp (gd_tbl_AW_CallocSecTop ()) "Psc,(0.(17.$4.$4.))Pr,$4.Pra,(2.&40.)Pgp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pj0,(2.&40.)Pjj1,(2.&40.)Pjj2,(2.&40.)Pj4,(2.&40.)Pjs1,(2.&40.)Pjs2,(2.&40.)Pe0,(2.&40.)Poomb,(2.&8.)Psrt,(2.&8.)PF,(36.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pmo,$18.PN,$4.Ptf,$4.Pncks,$4.Pps,(0.(2.&40.))Prest,(0.(2.&40.))P,(6<.$<.R7.VLO,VTOPU,(21.&40.R28.)VSP,Vd,)P,(6=.R8.VT,VCTX,)P,(5.R9.VT,VCTX,)P,(6>.R:.)P,(6?.R;.)P,(60.R<.)P,(15.R=.Vcan,Vdd,Vmadv,)P,(70.R>.VPA,)P,(71.R?.VCTX,VT,)P,(72.R10.)P,(73.$<.R11.$74.(28.$39.(3<.(27.&40.$75.))(2:.$39.)))P,(73.$<.R12.$76.(28.$39.(59.(27.&8.+1.))(2:.$39.)))P,(73.$<.R13.(9.$4=.+20.)(28.$39.(3<.(27.&40.VSB,))(2:.$39.)))P,(38.$<.R14.$5:.(28.$39.(59.R18.)(2:.$39.)))P,(73.$<.R15.$77.(28.$39.(59.(27.&8.+1.))(2:.$39.)))P,(38.$<.R16.$5;.(28.$39.(3:.R1;.)(2:.$39.)))P,(73.$<.R17.(9.VT,+8.)(28.$39.(3<.(27.&40.VTOP,))(28.$39.(3<.(27.&40.(3?.VTOP,(13.+2.+17.))))(2:.$39.))))P,(73.$<.R18.(9.VT,+28.)(28.$39.(59.(27.&8.=))(2:.$39.)))P,(38.$<.R19.(9.VT,+<60.)(28.$39.(59.(27.&8.=))(2:.$39.)))P,(73.$<.R1:.VT,(28.$39.(3<.(27.&40.VCTX,))(2:.$39.)))P,(73.$<.R1;.(9.VCTX,+8.)(28.$39.(3:.(27.&40.VTID,))(2:.$39.)))P,(78.R1<.)P,(38.$<.R1=.(9.VT,+:?0.)(28.$39.(3<.R28.)(28.$39.(3<.R27.)(28.$39.(3<.R26.)(2:.$39.)))))P,(38.$<.R1>.(9.VT,+;58.)(28.$39.(3<.R26.)(2:.$39.)))P,(38.$<.R1?.(9.VT,+;38.)(28.$39.(3<.R26.)(28.$39.(3<.R25.)(2:.$39.))))P,(>.=R47.)P,(=.(>.=R1=.)(>.R1=.(4>.+4000.R48.)))P,(>.(9.(4>.+4000.R49.)+4000.)(13.+2.+14.))P,(19.$4.(10.(11.(2.&40.)R1>.))R1?.)P,(19.$4.(10.(11.(2.&40.)R1>.))(3?.(4>.+4000.R4;.)R20.))P,(6:.R25.(4>.+4000.R4<.)R21.R28.=)P,(6;.$<.R26.VPA,R21.)P,(6;.$<.R27.(9.VPA,(4>.+8.R23.))R21.)P,(:.VhAR,R28.R26.Vnb0,R25.Vbl0,)P,(5?.A4.VCSf,R51.R50.Vnb0,Vbl0,Vnb0,Vbl0,)P,(>.(9.R27.+80.)(13.+2.+20.))P,(>.(9.R29.+2.)(3?.(13.+2.+1?.)(13.+2.+1<.)))P,Pk,$4.P,(=.(>.=R1.)(?.R1.(10.(11.$4.Vnb0,))))(16.(>.(9.VT,+1000.)(12.Vnb0,R2.))(>.(9.(12.Vnb0,R2.)(13.+2.+14.))VT,))P,Pj,$4.P,(=.(>.=R1.)(?.R1.(10.(11.$4.Vbl0,))))(16.(>.(9.VT,+1000.)(14.Vbl0,R2.))(>.(9.(14.Vbl0,R2.)(13.+2.+17.))VT,))P,Pk,$4.P,(=.(>.=R1.)(?.R1.(10.(11.$4.Vnb0,))))(16.(>.(9.VCTX,+10000.)(12.Vnb0,R2.))(>.(9.(12.Vnb0,R2.)(13.+2.+14.))VCTX,))P,Pj,$4.P,(=.(>.=R1.)(?.R1.(10.(11.$4.Vbl0,))))(16.(>.(9.VCTX,+10000.)(14.Vbl0,R2.))(>.(9.(14.Vbl0,R2.)(13.+2.+17.))VCTX,))P,Pk,$4.P,(=.(>.=R1.)(?.R1.(10.(11.$4.Vnb0,))))(16.(>.(9.VPA,+800000.)(12.Vnb0,R2.))(>.(9.(12.Vnb0,R2.)(13.+2.+14.))VPA,))P,Pj,$4.P,(=.(>.=R1.)(?.R1.(10.(11.$4.Vbl0,))))(16.(>.(9.VPA,+800000.)(14.Vbl0,R2.))(>.(9.(14.Vbl0,R2.)(13.+2.+17.))VPA,))P,(3>.$<.R32.VSP,VTOP,)P,(2<.A4.VCSf,R5;.R5:.Vnb0,Vbl0,VSP,(3?.VTOP,VSP,))P,(3>.$<.R34.Vlo,VSP,)P,(2<.A4.VCSf,R5=.R5<.Vnb0,Vbl0,Vlo,(3?.VSP,Vlo,))P,(41.$<.R36.)P,A5.VK,R5?.R5>.Vnb0,Vbl0,R36.P,(58.R38.R37.)P,A3.VGl,R61.R60.Vms',P,Pp,(17.$4.$4.)A2.VGp,(1<.(17.$4.$4.)R63.(28.(17.$4.$4.)R1.(2:.(17.$4.$4.))))R62.P,Pp,(17.$4.$4.)Pr',$4.A4.VGn,(1<.(17.$4.$4.)R65.(28.(17.$4.$4.)R2.(2:.(17.$4.$4.))))R1.Vnb0,Vbl0,P,Pp,(17.$4.$4.)Pr',$4.A4.VGs,(1<.(17.$4.$4.)R66.(28.(17.$4.$4.)R2.(2:.(17.$4.$4.))))R1.Vnb0,Vbl0,P,Pp,(17.$4.$4.)Pr',$4.Px,$4.A4.VGs,(1<.(17.$4.$4.)R68.(28.(17.$4.$4.)R3.(2:.(17.$4.$4.))))R2.(1<.$4.Vnb0,(28.$4.R1.(2:.$4.)))Vbl0,(79.$<.(7:.R64.R63.R5?.R5>.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R40.R3?.R66.R65.R3<.R3;.R3:.R39.R45.R44.R3>.)(51.(52.(53.R64.(27.&40.VSP,)R63.(27.&40.$54.)R62.R61.R60.R5?.R5>.(27.&40.Vcnt0,)(27.&40.Vsz0,)R5=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.)R40.(27.&40.$7;.)R3?.(56.(2.&40.))R3>.(57.$<.))R3=.))")
(* [comment removed for export] *).
  Proof.
    intros sc r ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 j0 jj1 jj2 j4 js1 js2 e0 oomb srt F fc m mo N tf ncks ps rest
      UWC MS8 AS PS FS DST RS LS TS MWS GOTFL PPART SBC OOM MRN ERR THR TSW UNW TH TIDC SHW STH ST4 TJ
      HR HNC HNR LPS LREST LI HPS HREST DI DCS TFMAX NB2 APTn APTs APCn APCs APPn APPs STT STCS ST SCS MI HK HJ HGl HGp GN GS GSX.
    facts. dpose GT as (T0 & T1 & TAL). pose proof GCTX as (CX0 & CX1). dpose GSB as (SBlo & SBAL & SBhi). dpose GPA as (PA0 & PA1 & PAL).
    dpose GSEP as (SEP1 & TC & SEP3 & SEP4 & SEP5).
    dpose sec_n as (NLO & NFX & RZ & N2E & RNB & RN8 & N2B & MSZ & MSAL & N28).
    assert (MSE : ms' = ms) by reflexivity.
    assert (NB32 : 0 <= n < 2^32) by (clear - NB; lia). assert (SPH : SP <= 2^62) by (clear - TOP1 TOP2; lia).
    assert (SPAE : SPA' = SP + -2192) by (subst SPA'; clear; lia). assert (STKE : STK' = SP + -2136) by reflexivity.
    (* [comment removed for export] *)
    eapply (evtA_aevtS_KJ AL (CSf sc r nb0 bl0) (K sc r nb0 bl0) _ _ _ mo (KL sc r nb0 bl0) HK); [exact HJ| |].
    { eapply (mseg_head AL IMG ALWF SP n lo T CTX TOP SB NB32 cnt0 sz0 CB0 SZ0 EN0 LOIMG SPL SPA16 TOP0 TOP1 TOP2 LO TOPU d LOB TOPUB GT GCTX (conj SEP1 (conj TC SEP3))
                (CSf sc r nb0 bl0) (CSOKf sc r nb0 bl0));
        first [exact UWC| exact MS8| exact AS| exact THR| exact TSW| exact UNW| apply CST| apply CSCTX| exact STT| exact STCS| exact ST| exact SCS| exact MI]. }
    cbn beta. intros ms1 mo1 PO HK1 MM1 HJ1. unfold head_post in PO.
    ddestruct PO as (tq0 & tq1 & tq2 & y14 & y15 & y16 & y17 & tq3 & tq4 & tq5 & tq6 & m1 & ws & size & fr0 & fr1 & fr2 & fr3 & fr4 & -> &
                    MU1 & WM1 & MI1 & FR7 & STKC & HTR & HL30 & SZB & SZD & F1800 & TFBP & F8 & FJ & FR16 & UNW1 & AFR & ST1 & SR1).
    (* [comment removed for export] *)
    assert (DJ1 : forall A k, A + k <= lo -> (A + k <= T + 3168 \/ T + 3169 <= A) -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k)
      by (intros A k H1 H2; cbn [disjoint_from]; clear - H1 H2; lia).
    assert (LOW1 : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k) by (intros A k H; apply DJ1; clear - H LOIMG T0; lia).
    assert (IMG1 : img_static_ok [(lo, SP); (T + 3168, T + 3169)]) by (apply munch_img_static_ok_lo; exact LOW1).
    assert (TLO1 : forall A k, T <= A -> A + k <= T + 3168 -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k) by (intros A k H1 H2; apply DJ1; clear - H1 H2 LOIMG T1; lia).
    assert (PAD1 : forall A k, PA <= A -> A + k <= PA + 0x800000 -> disjoint_from [(lo, SP); (T + 3168, T + 3169)] A k) by (intros A k H1 H2; apply DJ1; clear - H1 H2 LOIMG PA1 SEP4; lia).
    assert (CTXD1 : disjoint_from [(lo, SP); (T + 3168, T + 3169)] (CTX + 152) 8) by (apply DJ1; clear - CX1 LOIMG TC; lia).
    Ltac t1 H MU WM DJ tac := eapply rw_cells_transport; [exact H| exact MU| exact WM| apply DJ; cbn [cells_size csize Nat.add length map]; tac].
    assert (AS1 : allocA_statics m1 T CTX) by (eapply (allocA_statics_transport _ m m1 T CTX AS MU1); [exact LOW1| exact CTXD1]).
    assert (PS1 : poison_statics m1) by (eapply (poison_statics_transport _ m m1 PS MU1); intros A k H; apply LOW1; clear - H; lia).
    assert (FS1 : fin_statics m1) by (eapply (fin_statics_transport _ m m1 FS MU1); exact LOW1).
    assert (DST1 : depot_statics m1) by (eapply (depot_statics_transport _ m m1 DST MU1); intros A k H; apply LOW1; clear - H; lia).
    assert (RS1 : rsmr_statics m1 can dd madv) by (eapply (rsmr_statics_transport_i _ m m1 can dd madv RS MU1 IMG1)).
    assert (LS1 : large_statics m1 PA) by (eapply (large_statics_transport _ m m1 PA LS MU1); apply LOW1; unfold A_INSTANCE, A_GOT_LNAME, A_LNAME_CELL; clear; lia).
    assert (TS1 : thr_statics m1 CTX T) by (eapply (thr_statics_transport _ m m1 CTX T TS MU1); [apply LOW1; unfold A_TSD_INITED; clear; lia| apply LOW1; unfold A_TSD_PTR; clear; lia| apply LOW1; unfold A_TSD_ARR; clear; lia| exact CTXD1]).
    assert (MWS1 : mwc_statics m1) by (eapply (mwc_statics_transport _ m m1 MWS MU1); intros A k H; apply LOW1; clear - H; lia).
    assert (GOTFL1 : ro_cells asegs m1 A_GOT_FLAGS [C8 (Z_to_bv 64 A_FLAGS)]) by (eapply ro_cells_transport; [exact GOTFL| exact MU1| apply LOW1; unfold A_GOT_FLAGS; cbn; clear; lia]).
    assert (PPART1 : ro_cells asegs m1 A_FL_PPART [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact PPART| exact MU1| apply LOW1; unfold A_FL_PPART; cbn; clear; lia]).
    assert (SBC1 : ro_cells asegs m1 (A_INSTANCE + 32) [C8 (Z_to_bv 64 SB)]) by (eapply ro_cells_transport; [exact SBC| exact MU1| apply LOW1; unfold A_INSTANCE; cbn; clear; lia]).
    assert (MRN1 : ro_cells asegs m1 A_MRN_CELL [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact MRN| exact MU1| apply LOW1; unfold A_MRN_CELL; cbn; clear; lia]).
    assert (OOM1 : rw_cells asegs m1 A_OOM_CELL [C1 oomb]) by (t1 OOM MU1 WM1 LOW1 ltac:(unfold A_OOM_CELL; clear; lia)).
    assert (ERR1 : rw_cells asegs m1 A_ERRNO [C4 e0]) by (t1 ERR MU1 WM1 LOW1 ltac:(unfold A_ERRNO; clear; lia)).
    assert (TH1 : ro_cells asegs m1 T [C8 (Z_to_bv 64 CTX)]) by (eapply ro_cells_transport; [exact TH| exact MU1| apply TLO1; cbn; clear; lia]).
    assert (TIDC1 : ro_cells asegs m1 (CTX + 8) [C4 (Z_to_bv 64 TID)]) by (eapply ro_cells_transport; [exact TIDC| exact MU1| apply DJ1; cbn; clear - CX1 LOIMG TC; lia]).
    pose proof (shadow_wr_mono _ _ SHW WM1) as SHW1.
    assert (STH1 : rw_cells asegs m1 (T + 2800) [C8 j0; C8 jj1; C8 jj2]) by (t1 STH MU1 WM1 TLO1 ltac:(clear; lia)).
    assert (ST41 : rw_cells asegs m1 (T + 2904) [C8 j4]) by (t1 ST4 MU1 WM1 TLO1 ltac:(clear; lia)).
    assert (TJ1 : rw_cells asegs m1 (T + 2872) [C8 js1; C8 js2]) by (t1 TJ MU1 WM1 TLO1 ltac:(clear; lia)).
    assert (LI1 : limg m1 (0x4000 * r) ncks srt 0) by (eapply (limg_transport PA T); [exact LI| exact MU1| exact WM1| apply LOW1; unfold A_INSTANCE; clear; lia]).
    assert (HPS1 : u64arr asegs m1 PA ps) by (eapply u64arr_transport; [exact HPS| exact MU1| exact WM1| apply PAD1; [clear; lia| rewrite <- (Nat2Z.id (length ps)), LPS; clear - HNC HNR; lia]]).
    assert (HREST1 : u64arr asegs m1 (PA + 8 * ncks) rest) by (eapply u64arr_transport; [exact HREST| exact MU1| exact WM1| apply PAD1; [clear - HNC; lia| rewrite <- (Nat2Z.id (length rest)), LREST; clear - HNC HNR; lia]]).
    dpose (proj1 (proj2 (proj2 DI))) as (_ & DMF & _).
    dpose (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DI)))))))) as (_ & DBF & _).
    assert (BN0 : forall k, 0 <= k < Z.of_nat (length nb0) -> 0x65f000 <= dblk nb0 k /\ dblk nb0 k + 2^20 <= ACEIL).
    { intros k Hk. dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb0) DMF (Z.to_nat k) 0 ltac:(clear - Hk; lia)) as (X & Y & _).
      unfold dblk. split; [exact X| exact Y]. }
    assert (BS0 : forall j, 0 <= j < Z.of_nat (length bl0) -> 0x65f000 <= sblk bl0 j /\ sblk bl0 j + 2^23 <= ACEIL).
    { intros j Hj. dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl0) DBF (Z.to_nat j) 0 ltac:(clear - Hj; lia)) as (X & Y & _).
      unfold sblk. split; [exact X| exact Y]. }
    assert (DI1 : depot_inv m1 N nb0 tf bl0).
    { eapply (depot_inv_transport _ m m1 N nb0 tf bl0 DI MU1 WM1 LOW1).
      - intros k Hk. pose proof (APTn k Hk) as Y. pose proof (BN0 k Hk) as X. apply DJ1; clear - X Y LOIMG; lia.
      - intros j Hj. pose proof (APTs j Hj) as Y. pose proof (BS0 j Hj) as X. apply DJ1; clear - X Y LOIMG; lia. }
    clear AS PS FS DST RS LS TS MWS GOTFL PPART SBC MRN OOM ERR TH TIDC STH ST4 TJ LI HPS HREST MS8 THR TSW STT.
    (* [comment removed for export] *)
    assert (SPAAL2 : (SPA' + -128) mod 16 = 0).
    { rewrite SPAE. clear - SPA16. apply Z.mod_divide in SPA16; [| lia]. apply Z.mod_divide; [lia|]. destruct SPA16 as [q Hq]. exists (q - 145). lia. }
    eapply (combined_sec_cfgS AL IMG ALWF ASB (fun sc r => CSf sc r nb0 bl0) (fun sc r => K sc r nb0 bl0) (fun sc r => CSOKf sc r nb0 bl0) (fun sc r => KL sc r nb0 bl0)
              CSmono_l CSmono_p Gl Gp PA T CTX GPA GT GCTX (conj SEP4 (conj TC SEP5))
              (fun sc r => CST sc r nb0 bl0) (fun sc r => CSCTX sc r nb0 bl0) CSPA' K_apart_l T_large LEDGER_P TP_commit TP_fresh ROOM_P SCAR_P
              dstat dstat_transport DIE_NEED DIE_NEED_ge MOD_DIE)
      with (lo := lo) (srt := srt) (rest := rest) (ps := ps) (j1 := js1) (j2 := js2) (sc := sc) (r := r) (ncks := ncks).
    all: cbv beta.
    all: lazymatch goal with
         | |- forall ok c', _ => idtac
         | |- 0x10000 < needed2 n <= 2^32 => clear - N2B NB; lia
         | |- needed2 n mod 8 = 0 => exact N28
         | |- lstat _ _ _ _ _ => split; [exact LS1| split; [exact TS1| split; [exact PS1| split; [exact MWS1| exact (dstat_of_rsmr _ _ _ _ RS1)]]]]
         | |- _ = Z_to_bv 64 A_TP => reflexivity
         | |- shadow_wr _ => exact SHW1
         | |- rw_cells _ _ (T + 2872) _ => exact TJ1
         | |- limg _ _ _ _ _ => exact LI1
         | |- u64arr _ _ PA _ => exact HPS1
         | |- u64arr _ _ _ _ => exact HREST1
         | |- stk _ _ _ _ => exact ST1
         | |- crange _ lo _ => eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear; lia| rewrite ?SPAE; clear; lia]
         | |- mem_inv _ _ => exact MI1
         | |- K _ _ _ _ _ => exact HK1
         | |- J _ _ => exact HJ1
         | |- Gl _ _ _ => exact HGl
         | |- forall p, Gp _ _ => exact HGp
         | |- (_ + -128) mod 16 = 0 => exact SPAAL2
         | |- ?G => first [exact HR| exact HNC| exact HNR| exact LPS| exact LREST| exact LOIMG
                         | (rewrite ?SPAE; unfold DIE_NEED; clear - SPL; lia) | (rewrite ?SPAE; clear - SPH; lia) | fail 99 "combined premise:" G ]
         end.
    all: lazymatch goal with |- forall ok c', _ => idtac | |- ?G => fail "combined premise" G end.
    (* [comment removed for export] *)
    intros ok cf PO. unfold combsec_cpostS in PO.
    ddestruct PO as (ms2 & mo2 & res & u0 & u1 & u2 & ua2 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & mm & -> & -> & MI2 & ST2 & WM2 & SHW2 & LS2 & ARM).
    replace (ret_pc (Z_to_bv 64 0x47d34)) with (Z_to_bv 64 0x47d34) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    destruct ok.
    - (* [comment removed for export] *)
      ddestruct ARM as (a & r' & rest' & -> & HK2 & HJ2 & HR' & NCK' & A0 & AAL & ACE & ABAND & ABP & BCS2 & FRESH & MU2 & HH2 & ZB2 & SHH2 & SHT2 & TJ2 & LI2 & HPS2 & HREST2 & LREST2).
      ddestruct LS2 as (LSm & TSm & PSm & MWSm & DSm).
      fold ms in ACE, ABAND, ABP, BCS2, FRESH, MU2, HH2, ZB2, SHH2, SHT2, HK2, TJ2 |- *.
      set (sc' := sc ++ [(a, ms)]) in *.
      assert (HR'0 : 0 <= r' /\ r' <= r + 1) by (clear - HR' HR; lia).
      assert (INC2 : forall y, CSf sc r nb0 bl0 y -> CSf sc' r' nb0 bl0 y).
      { intros y Hy. subst sc'. destruct HR' as [-> | [-> _]]; [apply CSmono_l; exact Hy| apply CSmono_p; apply CSmono_l; exact Hy]. }
      pose proof (apart_of_cs _ T 4096 a ms (CST sc r nb0 bl0) FRESH ltac:(clear; lia) ltac:(clear - MSZ N2B; lia)) as ABT0.
      assert (ABT : a + ms <= T \/ T + 4096 <= a) by (clear - ABT0; lia). clear ABT0.
      pose proof (apart_of_cs _ CTX 0x10000 a ms (CSCTX sc r nb0 bl0) FRESH ltac:(clear; lia) ltac:(clear - MSZ N2B; lia)) as ABC0.
      assert (ABC : a + ms <= CTX \/ CTX + 0x10000 <= a) by (clear - ABC0; lia). clear ABC0.
      assert (APT : a + ms <= SB \/ SB + 2^37 + 4096 <= a).
      { pose proof (SEC_APART sc' r' nb0 bl0 mo2 (a, ms) HK2 ltac:(subst sc'; apply in_app_iff; right; left; reflexivity)) as X. cbn [fst snd] in X. exact X. }
      assert (TNS : T + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= T) by (clear - T0; lia).
      destruct DCS as [NBCS BLCS].
      assert (APBn : forall k, 0 <= k < Z.of_nat (length nb0) -> a + ms <= dblk nb0 k \/ dblk nb0 k + 2^20 <= a).
      { intros k Hk. pose proof (apart_of_cs _ (dblk nb0 k) (2^20) a ms (NBCS k Hk) FRESH ltac:(clear; lia) ltac:(clear - MSZ N2B; lia)) as X. clear - X; lia. }
      assert (APBs : forall j, 0 <= j < Z.of_nat (length bl0) -> a + ms <= sblk bl0 j \/ sblk bl0 j + 2^23 <= a).
      { intros j Hj. pose proof (apart_of_cs _ (sblk bl0 j) (2^23) a ms (BLCS j Hj) FRESH ltac:(clear; lia) ltac:(clear - MSZ N2B; lia)) as X. clear - X; lia. }
      assert (DCS2 : depot_cs (CSf sc' r' nb0 bl0) nb0 bl0) by (split; [intros k Hk; eapply crange_imp; [exact INC2| exact (NBCS k Hk)]| intros j Hj; eapply crange_imp; [exact INC2| exact (BLCS j Hj)]]).
      assert (SCS2 : crange (CSf sc' r' nb0 bl0) lo (SP - lo)) by (eapply crange_imp; [exact INC2| exact SCS]).
      (* [comment removed for export] *)
      pose proof (Z.div_mod a 4096 ltac:(clear; lia)) as DA. rewrite AAL, Z.add_0_r in DA.
      pose proof (Z.div_mod ms 4096 ltac:(clear; lia)) as DM. rewrite MSAL, Z.add_0_r in DM.
      pose proof (Z.div_mod (needed2 n) 8 ltac:(clear; lia)) as DX. rewrite N28, Z.add_0_r in DX.
      remember (a / 4096) as qa eqn:Hqa. remember (ms / 4096) as qm eqn:Hqm. remember (needed2 n / 8) as qx eqn:Hqx.
      assert (SHAE : 0x7fff8000 + a / 8 = 0x7fff8000 + 512 * qa) by (rewrite DA; replace (4096 * qa) with ((512 * qa) * 8) by (clear; lia); rewrite Z.div_mul by (clear; lia); reflexivity).
      assert (MS8 : ms / 8 = 512 * qm) by (rewrite DM; replace (4096 * qm) with ((512 * qm) * 8) by (clear; lia); rewrite Z.div_mul by (clear; lia); reflexivity).
      rewrite SHAE, MS8 in MU2.
      assert (GEO : a = 4096 * qa /\ ms = 4096 * qm /\ needed2 n = 8 * qx /\ 0x65f000 <= a /\ a + ms <= ACEIL /\ 0x10000 < needed2 n /\ needed2 n + 4096 <= ms /\ ms < needed2 n + 8192
                   /\ ACEIL <= lo /\ lo <= SP - 4096 /\ SPA' = SP + -2192 /\ STK' = SP + -2136 /\ SP + 16 <= 2^47
                   /\ (Timg T /\ Tband T) /\ T + 4096 <= ACEIL /\ (0x65f000 <= CTX /\ Pband CTX 0x10000) /\ CTX + 0x10000 <= ACEIL
                   /\ (0x65f000 <= PA /\ Pband PA 0x800000) /\ PA + 0x800000 <= ACEIL /\ 0 <= ncks /\ ncks + 1 <= 0x4000 * r' /\ 0x4000 * r' <= 2^20 /\ r' <= r + 1 /\ 0 <= r').
      { clear - DA DM DX A0 ACE N2B MSZ LOIMG SPL SPAE STKE TOP1 TOP2 T0 T1 CX0 CX1 PA0 PA1 HNC NCK' HNR HR'0. repeat match goal with |- _ /\ _ => split end; lia. }
      clear DA DM DX Hqa Hqm Hqx.
      (* [comment removed for export] *)
      set (W2 := [(lo, SPA' + -128); (a, a + ms); (0x7fff8000 + 512 * qa, 0x7fff8000 + 512 * qa + 512 * qm); (T + 2872, T + 2888); (A_INSTANCE + 112, A_INSTANCE + 720); (PA + 8 * ncks, PA + 8 * (0x4000 * r'))]) in MU2.
      assert (IMG2 : img_static_ok W2).
      { intros A k H1 H2. unfold W2, A_INSTANCE in *. cbn [disjoint_from]. clear - H1 H2 GEO. decompose [and] GEO. repeat split; lia. }
      assert (LOW2 : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> (A + k <= A_INSTANCE + 112 \/ A_INSTANCE + 720 <= A) -> disjoint_from W2 A k) by (exact IMG2).
      assert (HI2 : forall A k, SPA' + -128 <= A -> A + k <= SP -> disjoint_from W2 A k).
      { intros A k H1 H2. unfold W2, A_INSTANCE. cbn [disjoint_from]. clear - H1 H2 GEO. decompose [and] GEO. repeat split; lia. }
      assert (TW2 : forall A k, T <= A -> A + k <= T + 4096 -> (A + k <= T + 2872 \/ T + 2888 <= A) -> disjoint_from W2 A k).
      { intros A k H1 H2 H3. unfold W2, A_INSTANCE. cbn [disjoint_from].
        split; [clear - H1 H2 GEO; decompose [and] GEO; lia|]. split; [clear - H1 H2 GEO ABT; decompose [and] GEO; lia|].
        split; [clear - H1 H2 GEO; decompose [and] GEO; lia|]. split; [exact H3|].
        split; [clear - H1 H2 GEO; decompose [and] GEO; lia|]. split; [clear - H1 H2 GEO SEP4; decompose [and] GEO; lia| exact I]. }
      assert (CW2 : forall A k, CTX <= A -> A + k <= CTX + 0x10000 -> disjoint_from W2 A k).
      { intros A k H1 H2. unfold W2, A_INSTANCE. cbn [disjoint_from].
        split; [clear - H1 H2 GEO; decompose [and] GEO; lia|]. split; [clear - H1 H2 GEO ABC; decompose [and] GEO; lia|].
        split; [clear - H1 H2 GEO; decompose [and] GEO; lia|]. split; [clear - H1 H2 GEO TC; decompose [and] GEO; lia|].
        split; [clear - H1 H2 GEO; decompose [and] GEO; lia|]. split; [clear - H1 H2 GEO SEP5; decompose [and] GEO; lia| exact I]. }
      Ltac t2 H MU WM DJ tac := eapply rw_cells_transport; [exact H| exact MU| exact WM| apply DJ; cbn [cells_size csize Nat.add length map]; tac].
      assert (AS2 : allocA_statics mm T CTX) by (eapply (allocA_statics_transport_i _ m1 mm T CTX AS1 MU2 IMG2); apply CW2; clear; lia).
      assert (FS2 : fin_statics mm) by (exact (fin_statics_transport_i _ m1 mm FS1 MU2 IMG2)).
      assert (DST2 : depot_statics mm) by (exact (depot_statics_transport_i _ m1 mm DST1 MU2 IMG2)).
      assert (RS2 : rsmr_statics mm can dd madv) by (exact (rsmr_statics_transport_i _ m1 mm can dd madv RS1 MU2 IMG2)).
      assert (GOTFL2 : ro_cells asegs mm A_GOT_FLAGS [C8 (Z_to_bv 64 A_FLAGS)]) by (eapply ro_cells_transport; [exact GOTFL1| exact MU2| apply LOW2; unfold A_GOT_FLAGS, A_INSTANCE; cbn; clear; lia]).
      assert (PPART2 : ro_cells asegs mm A_FL_PPART [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact PPART1| exact MU2| apply LOW2; unfold A_FL_PPART, A_FLAGS, A_INSTANCE; cbn; clear; lia]).
      assert (SBC2 : ro_cells asegs mm (A_INSTANCE + 32) [C8 (Z_to_bv 64 SB)]) by (eapply ro_cells_transport; [exact SBC1| exact MU2| apply LOW2; unfold A_INSTANCE; cbn; clear; lia]).
      assert (MRN2 : ro_cells asegs mm A_MRN_CELL [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact MRN1| exact MU2| apply LOW2; unfold A_MRN_CELL, A_INSTANCE; cbn; clear; lia]).
      assert (OOM2 : rw_cells asegs mm A_OOM_CELL [C1 oomb]) by (t2 OOM1 MU2 WM2 LOW2 ltac:(unfold A_OOM_CELL, A_INSTANCE; clear; lia)).
      assert (ERR2 : rw_cells asegs mm A_ERRNO [C4 e0]) by (t2 ERR1 MU2 WM2 LOW2 ltac:(unfold A_ERRNO, A_INSTANCE; clear; lia)).
      assert (TH2 : ro_cells asegs mm T [C8 (Z_to_bv 64 CTX)]) by (eapply ro_cells_transport; [exact TH1| exact MU2| apply TW2; cbn; clear; lia]).
      assert (TIDC2 : ro_cells asegs mm (CTX + 8) [C4 (Z_to_bv 64 TID)]) by (eapply ro_cells_transport; [exact TIDC1| exact MU2| apply CW2; cbn; clear; lia]).
      assert (UNW2 : rw_cells asegs mm (T + 3168) [C1 (Z_to_bv 8 0)]) by (t2 UNW1 MU2 WM2 TW2 ltac:(clear; lia)).
      assert (STH2 : rw_cells asegs mm (T + 2800) [C8 j0; C8 jj1; C8 jj2]) by (t2 STH1 MU2 WM2 TW2 ltac:(clear; lia)).
      assert (ST42 : rw_cells asegs mm (T + 2904) [C8 j4]) by (t2 ST41 MU2 WM2 TW2 ltac:(clear; lia)).
      assert (FR7_2 : rw_cells asegs mm (SP + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (t2 FR7 MU2 WM2 HI2 ltac:(clear - GEO; decompose [and] GEO; lia)).
      assert (STKC2 : rw_cells asegs mm STK' [C8 (Z_to_bv 64 (STK' + 16)); C8 (Z_to_bv 64 size)]) by (t2 STKC MU2 WM2 HI2 ltac:(clear - GEO; decompose [and] GEO; lia)).
      assert (HTR2 : u64arr asegs mm (STK' + 16) ws) by (eapply u64arr_transport; [exact HTR| exact MU2| exact WM2| apply HI2; rewrite ?HL30; clear - GEO; decompose [and] GEO; lia]).
      assert (F1800_2 : rw_cells asegs mm (STK' + 256) [CB 1800 fr1]) by (t2 F1800 MU2 WM2 HI2 ltac:(clear - GEO; decompose [and] GEO; lia)).
      assert (TFBP2 : rw_cells asegs mm (STK' + 2056) [C8 (Z_to_bv 64 SP)]) by (t2 TFBP MU2 WM2 HI2 ltac:(clear - GEO; decompose [and] GEO; lia)).
      assert (F8_2 : rw_cells asegs mm (STK' + 2064) [CB 8 fr2]) by (t2 F8 MU2 WM2 HI2 ltac:(clear - GEO; decompose [and] GEO; lia)).
      assert (FR16_2 : rw_cells asegs mm (STK' + -56) [CB 8 fr4; C8 (Z_to_bv 64 A_PC_CALLOC); C8 (Z_to_bv 64 cnt0); C8 (Z_to_bv 64 sz0); C8 (Z_to_bv 64 SP); C8 (Z_to_bv 64 0x699c4)]) by (t2 FR16 MU2 WM2 HI2 ltac:(clear - GEO; decompose [and] GEO; lia)).
      assert (FJ2 : rw_cells asegs mm (STK' + -8) [CB 8 fr3]) by (t2 FJ MU2 WM2 HI2 ltac:(clear - GEO; decompose [and] GEO; lia)).
      assert (AFR2 : allocA_frame mm SPA' fr0 0 (Z_to_bv 64 0x48470) (Z_to_bv 64 n) (Z_to_bv 64 STK') (Z_to_bv 64 A_INSTANCE) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 STK') (Z_to_bv 64 (SP + -89)) s7 s8 s9 s10 s11).
      { unfold allocA_frame in *. t2 AFR MU2 WM2 HI2 ltac:(clear - GEO; decompose [and] GEO; lia). }
      (* [comment removed for export] *)
      assert (BNsh0 : forall k (A w : Z), 0 <= k < Z.of_nat (length nb0) -> 0x7fff8000 <= A -> A + w <= 0x10007fff8000 -> 0 < w -> A + w <= dblk nb0 k \/ dblk nb0 k + 2^20 <= A).
      { intros k A w Hk H1 H2 Hw. pose proof (NBCS k Hk) as X.
        destruct (Z_le_dec (dblk nb0 k + 2^20) A); [right; assumption|]. destruct (Z_le_dec (A + w) (dblk nb0 k)); [left; assumption|]. exfalso.
        destruct (Z_le_dec A (dblk nb0 k)).
        - apply (CSf_noshadow sc r nb0 bl0 (dblk nb0 k)); [apply X; clear; lia| clear - H1 H2 Hw n0 n1 l; lia].
        - apply (CSf_noshadow sc r nb0 bl0 A); [apply X; clear - n0 n1 n2; lia| clear - H1 H2 Hw n0 n1 n2; lia]. }
      assert (BSsh0 : forall j (A w : Z), 0 <= j < Z.of_nat (length bl0) -> 0x7fff8000 <= A -> A + w <= 0x10007fff8000 -> 0 < w -> A + w <= sblk bl0 j \/ sblk bl0 j + 2^23 <= A).
      { intros j A w Hj H1 H2 Hw. pose proof (BLCS j Hj) as X.
        destruct (Z_le_dec (sblk bl0 j + 2^23) A); [right; assumption|]. destruct (Z_le_dec (A + w) (sblk bl0 j)); [left; assumption|]. exfalso.
        destruct (Z_le_dec A (sblk bl0 j)).
        - apply (CSf_noshadow sc r nb0 bl0 (sblk bl0 j)); [apply X; clear; lia| clear - H1 H2 Hw n0 n1 l; lia].
        - apply (CSf_noshadow sc r nb0 bl0 A); [apply X; clear - n0 n1 n2; lia| clear - H1 H2 Hw n0 n1 n2; lia]. }
      assert (DI2 : depot_inv mm N nb0 tf bl0).
      { eapply (depot_inv_transport_i _ m1 mm N nb0 tf bl0 DI1 MU2 WM2 IMG2).
        - intros k Hk. pose proof (BN0 k Hk) as X. pose proof (APBn k Hk) as Y1. pose proof (APTn k Hk) as Y2. pose proof (APPn k Hk) as Y3.
          pose proof (BNsh0 k (0x7fff8000 + 512 * qa) (512 * qm) Hk ltac:(clear - GEO; lia) ltac:(clear - GEO ABAND; decompose [and] GEO; lia) ltac:(clear - GEO; lia)) as Y4.
          unfold W2, A_INSTANCE. cbn [disjoint_from]. clear - X Y1 Y2 Y3 Y4 GEO. decompose [and] GEO. repeat split; lia.
        - intros j Hj. pose proof (BS0 j Hj) as X. pose proof (APBs j Hj) as Y1. pose proof (APTs j Hj) as Y2. pose proof (APPs j Hj) as Y3.
          pose proof (BSsh0 j (0x7fff8000 + 512 * qa) (512 * qm) Hj ltac:(clear - GEO; lia) ltac:(clear - GEO ABAND; decompose [and] GEO; lia) ltac:(clear - GEO; lia)) as Y4.
          unfold W2, A_INSTANCE. cbn [disjoint_from]. clear - X Y1 Y2 Y3 Y4 GEO. decompose [and] GEO. repeat split; lia. }
      (* [comment removed for export] *)
      assert (SHU2 : exists sha, rw_cells asegs mm (0x7fff8000 + a / 8 + 512) [CB (Z.to_nat (needed2 n / 8)) sha]).
      { destruct SHW2 as [SWL SWH]. rewrite SHAE. apply wr_at_cells; [clear - GEO; lia|]. rewrite Z2Nat.id by (clear - GEO; lia).
        destruct ABAND as [LOWB|HIGHB].
        - eapply (wr_at_sub _ _ _ _ _ SWL); clear - GEO LOWB; decompose [and] GEO; lia.
        - eapply (wr_at_sub _ _ _ _ _ SWH); clear - GEO HIGHB; decompose [and] GEO; lia. }
      destruct SHU2 as [sha SHU2].
      (* [comment removed for export] *)
      eapply aevtS_mono.
      { assert (R20' : 0x4000 * r' <= 2^20) by (clear - HNR HR'0; lia).
          eapply (csec_chunk AL IMG ALWF ASB CSf K CSOKf KL CSf_noshadow nb0 bl0 CSmono_n CSmono_s SP n lo T CTX TID SB PA NB FP LOIMG SPL SPA16 TOP2 TIDB d
                    GSB GT GCTX GPA GSEP CST CSCTX CSPA K_apart Gn Gs T_node T_store ROOM_n ROOM_s can dd madv PZ sc' r' a ncks
                    A0 AAL ACE ABAND APT ABT ABC (proj1 HR'0) (conj (proj1 HNC) NCK') R20' BCS2 SCS2 APTn APTs APCn APCs APPn APPs APBn APBs)
            with (N := N) (tf := tf) (sha := sha) (pgb := Z_to_bv 8 0) (shs := []) (pg1 := []).
          all: lazymatch goal with
               | |- Gn _ _ _ _ => apply GN
               | |- forall x, Gs _ _ _ _ => intros; apply GSX
               | |- Gs _ _ _ _ => apply GS
               | |- _ => first [eassumption | idtac]
               end.
          all: match goal with |- ?G => fail 99 "leftover" G end.  }
      (* [comment removed for export] *)
      intros cf PC. unfold sec_chunk_post in PC. cbv zeta in PC.
      ddestruct PC as (ms3 & mo3 & nb' & bl' & N' & tf' & id & w0 & w1 & w2' & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4' & w5 & w6 & b1' & pgb & k0 & k1 & k2' & k4 & m3
                      & -> & -> & HK3 & HJ3 & DI3 & DCS3 & DST3 & IDB & NB' & TFB & TFP & CSM3 & BLK & SK & WM3 & MI3 & ST3
                      & HH3 & Z13 & MG3 & Z23 & HDR3 & B1A & B1B & Z33 & SHH3 & S13 & SUB3 & PG3 & S23 & STH3 & ST43 & UNW3).
      ddestruct BLK as (sn & sb & Enb & Ebl & Fn & Fs).
      dpose (proj1 (proj2 (proj2 DI3))) as (_ & DMF3 & _).
      dpose (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DI3)))))))) as (_ & DBF3 & _).
      assert (BN : forall k, 0 <= k < Z.of_nat (length nb') -> 0x65f000 <= dblk nb' k /\ dblk nb' k + 2^20 <= ACEIL).
      { intros k Hk. dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb') DMF3 (Z.to_nat k) 0 ltac:(clear - Hk; lia)) as (X & Y & _).
        unfold dblk. split; [exact X| exact Y]. }
      assert (BS : forall j, 0 <= j < Z.of_nat (length bl') -> 0x65f000 <= sblk bl' j /\ sblk bl' j + 2^23 <= ACEIL).
      { intros j Hj. dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl') DBF3 (Z.to_nat j) 0 ltac:(clear - Hj; lia)) as (X & Y & _).
        unfold sblk. split; [exact X| exact Y]. }
      assert (BNold : forall k (A w : Z), 0 <= k < Z.of_nat (length nb') -> crange (CSf sc' r' nb0 bl0) A w -> 0 < w ->
                (forall k0, 0 <= k0 < Z.of_nat (length nb0) -> A + w <= dblk nb0 k0 \/ dblk nb0 k0 + 2^20 <= A) ->
                A + w <= dblk nb' k \/ dblk nb' k + 2^20 <= A).
      { intros k A w Hk CR0 Hw OLD. rewrite Enb in Hk |- *. destruct (dblk_app_cases nb0 sn k Hk) as [[Hk' ->]| HIn].
        - apply OLD. exact Hk'.
        - eapply (apart_of_cs _ A w _ (2^20) CR0); [| exact Hw| clear; lia]. exact (proj1 (Forall_forall _ _) Fn _ HIn). }
      assert (BSold : forall j (A w : Z), 0 <= j < Z.of_nat (length bl') -> crange (CSf sc' r' nb0 bl0) A w -> 0 < w ->
                (forall j0, 0 <= j0 < Z.of_nat (length bl0) -> A + w <= sblk bl0 j0 \/ sblk bl0 j0 + 2^23 <= A) ->
                A + w <= sblk bl' j \/ sblk bl' j + 2^23 <= A).
      { intros j A w Hj CR0 Hw OLD. rewrite Ebl in Hj |- *. destruct (sblk_app_cases bl0 sb j Hj) as [[Hj' ->]| HIn].
        - apply OLD. exact Hj'.
        - eapply (apart_of_cs _ A w _ (2^23) CR0); [| exact Hw| clear; lia]. exact (proj1 (Forall_forall _ _) Fs _ HIn). }
      (* [comment removed for export] *)
      assert (SKW : forall A sz, 0 <= A -> A + sz <= 2^64 ->
                (A + sz <= lo \/ SP <= A) -> (A + sz <= A_SS \/ A_DEP_END <= A) -> (A + sz <= T + 2800 \/ T + 2824 <= A) -> (A + sz <= T + 2904 \/ T + 2912 <= A) ->
                (A + sz <= a \/ a + ms <= A) -> (A + sz <= 0x7fff8000 + 512 * qa \/ 0x7fff8000 + 512 * qa + 512 * qm <= A) ->
                (forall k, 0 <= k < Z.of_nat (length nb') -> A + sz <= dblk nb' k \/ dblk nb' k + 2^20 <= A) ->
                (forall j, 0 <= j < Z.of_nat (length bl') -> A + sz <= sblk bl' j \/ sblk bl' j + 2^23 <= A) ->
                munch [(0, A); (A + sz, 2^64)] mm m3).
      { intros A sz HA0 HA1 O1 O2 O3 O4 O5 O6 OBn OBs x Hx. cbn [outside] in Hx. ddestruct Hx as (X1 & X2 & _).
        pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
        apply SK.
        - unfold swin. cbn [outside].
          split; [clear - X1 X2 XR O1; lia|]. split; [clear - X1 X2 XR O2; lia|]. split; [clear - X1 X2 XR O3; lia|]. split; [clear - X1 X2 XR O4; lia|].
          split; [clear - X1 X2 XR O5; lia|]. split; [clear - X1 X2 XR O6 SHAE MS8; lia| exact I].
        - intros k Hk. pose proof (OBn k Hk). clear - X1 X2 XR H. lia.
        - intros j Hj. pose proof (OBs j Hj). clear - X1 X2 XR H. lia. }
      assert (MULI : munch [(0, A_INSTANCE + 112); (A_INSTANCE + 112 + 608, 2^64)] mm m3).
      { apply SKW; unfold A_INSTANCE, A_SS, A_DEP_END; try (clear - GEO; decompose [and] GEO; lia).
        - intros k Hk. pose proof (BN k Hk). clear - H. lia. - intros j Hj. pose proof (BS j Hj). clear - H. lia. }
      assert (MUPA : munch [(0, PA); (PA + 8 * (0x4000 * r'), 2^64)] mm m3).
      { assert (R0 : 0 < r') by (clear - GEO; decompose [and] GEO; lia).
        apply SKW; unfold A_SS, A_DEP_END; try (clear - GEO; decompose [and] GEO; lia); try (clear - GEO SEP4 ABP; decompose [and] GEO; lia).
        - intros k Hk. replace (8 * (0x4000 * r')) with (0x20000 * r') by (clear; lia).
          apply (BNold k PA (0x20000 * r') Hk (CSPA sc' r' nb0 bl0 ltac:(clear - GEO; lia) ltac:(clear - GEO; lia)) ltac:(clear - R0; lia)). intros kk Hkk. pose proof (APPn kk Hkk) as Y. clear - Y GEO. decompose [and] GEO. lia.
        - intros j Hj. replace (8 * (0x4000 * r')) with (0x20000 * r') by (clear; lia).
          apply (BSold j PA (0x20000 * r') Hj (CSPA sc' r' nb0 bl0 ltac:(clear - GEO; lia) ltac:(clear - GEO; lia)) ltac:(clear - R0; lia)). intros jj Hjj. pose proof (APPs jj Hjj) as Y. clear - Y GEO. decompose [and] GEO. lia. }
      assert (MUTJ : munch [(0, T + 2872); (T + 2872 + 16, 2^64)] mm m3).
      { apply SKW; unfold A_SS, A_DEP_END; try (clear - GEO; decompose [and] GEO; lia); try (clear - GEO ABT TNS; decompose [and] GEO; lia).
        - intros k Hk. pose proof (BNold k T 4096 Hk (CST sc' r' nb0 bl0) ltac:(clear; lia) APTn) as Y. clear - Y. lia.
        - intros j Hj. pose proof (BSold j T 4096 Hj (CST sc' r' nb0 bl0) ltac:(clear; lia) APTs) as Y. clear - Y. lia. }
      assert (WD : forall A sz A' k, A <= A' -> A' + k <= A + sz -> disjoint_from [(0, A); (A + sz, 2^64)] A' k) by (intros; cbn [disjoint_from]; lia).
      unfold msec_post.
      eexists. dexists mo3, (a + 4096 + rz_size n), sc', r', nb', bl'. dexists w0, w1, w2', wa1, wa2, wa3, wa4, wa5, wa6, wa7, w3, w4', w5, w6. exists m3.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HK3|]. split; [exact HJ3|].
      split; [exact (wmono_trans _ _ _ _ WM1 (wmono_trans _ _ _ _ WM2 WM3))|]. split; [exact MI3|]. split; [exact ST3|].
      split; [intros y Hy; apply CSM3; apply INC2; exact Hy|]. split; [exact UNW3|].
      right. dexists a, N', tf', id, b1', pgb, k0, k1, k2', k4, rest'. cbv zeta.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HR'|]. split; [exact NCK'|].
      split; [exact A0|]. split; [exact AAL|]. split; [exact ACE|]. split; [exact ABAND|]. split; [exact ABP|]. split; [exact ABT|]. split; [exact ABC|].
      split; [exact FRESH|]. split; [exact (ALazy.crange_mono _ _ _ _ CSM3 BCS2)|].
      split.
      { (* [comment removed for export] *)
        intros x. cbv zeta. intros HO HBn HBs. unfold msec_cwin in HO. cbn [outside] in HO. ddestruct HO as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & _).
        pose proof O6 as O6'. rewrite ?MSE in O6'. fold ms in O6'. rewrite SHAE, MS8 in O6'.
        pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
        rewrite (SK x).
        2:{ unfold swin. cbn [outside]. split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|]. split; [exact O5|].
            split; [first [exact O6| clear - O6 SHAE MS8; lia]| exact I]. }
        2:{ exact HBn. } 2:{ exact HBs. }
        rewrite (MU2 x).
        2:{ unfold W2. cbn [outside]. split; [clear - O1 GEO; decompose [and] GEO; lia|]. split; [exact O5|]. split; [exact O6'|]. split; [exact O8|]. split; [exact O9|]. split; [exact O10| exact I]. }
        apply (MU1 x). cbn [outside]. split; [exact O1|]. split; [exact O7| exact I]. }
      split; [exact DI3|]. split; [exact DCS3|]. split; [exact DST3|]. split; [exact IDB|]. split; [exact NB'|]. split; [exact TFB|]. split; [exact TFP|].
      split; [dexists sn, sb; split; [exact Enb| split; [exact Ebl| split; [exact Fn| exact Fs]]]|].
      split; [exact HH3|]. split; [exact Z13|]. split; [exact MG3|]. split; [exact Z23|]. split; [exact HDR3|]. split; [exact B1A|]. split; [exact B1B|].
      split; [exact Z33|]. split; [exact SHH3|]. split; [exact S13|]. split; [exact SUB3|]. split; [exact PG3|]. split; [exact S23|].
      split; [exact STH3|]. split; [exact ST43|].
      split; [eapply (limg_transport PA T); [exact LI2| exact MULI| exact WM3| apply WD; clear; lia]|].
      split; [eapply u64arr_transport; [exact HPS2| exact MUPA| exact WM3| apply WD; [clear; lia| rewrite app_length; cbn [length]; rewrite Nat2Z.inj_add, <- ?LPS; clear - GEO LPS; decompose [and] GEO; lia]]|].
      split; [eapply u64arr_transport; [exact HREST2| exact MUPA| exact WM3| apply WD; [clear - GEO; decompose [and] GEO; lia| rewrite <- (Nat2Z.id (length rest')), LREST2; clear - GEO; decompose [and] GEO; lia]]|].
      split; [exact LREST2|].
      eapply rw_cells_transport; [exact TJ2| exact MUTJ| exact WM3| apply WD; cbn; clear; lia].
    - (* [comment removed for export] *)
      ddestruct ARM as (-> & HK2 & HJ2 & MU2 & TJ2).
      assert (HI2 : forall A k, SPA' + -128 <= A -> disjoint_from [(lo, SPA' + -128)] A k) by (intros A k H; cbn [disjoint_from]; clear - H; lia).
      assert (LOW2 : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from [(lo, SPA' + -128)] A k) by (intros A k H; cbn [disjoint_from]; clear - H LOIMG; lia).
      Ltac t2n H MU WM DJ tac := eapply rw_cells_transport; [exact H| exact MU| exact WM| apply DJ; cbn [cells_size csize Nat.add length map]; tac].
      eapply (evtA_aevtS_KJ AL (CSf sc r nb0 bl0) (K sc r nb0 bl0) _ _ _ mo2 (KL sc r nb0 bl0) HK2); [exact HJ2| |].
      { eapply (mseg_null AL IMG ALWF SP n lo T 0 0 0 0 cnt0 sz0 LOIMG SPL SPA16 TOP2 (CSf sc r nb0 bl0) (CSOKf sc r nb0 bl0)) with (m0 := m1) (W := []) (size := size) (ws := ws) (fr1 := fr1) (fr2 := fr2) (fr3 := fr3) (fr0 := fr0) (oomb := oomb) (e0 := e0).
        - unfold allocA_frame in *. t2n AFR MU2 WM2 HI2 ltac:(rewrite ?SPAE; clear; lia).
        - t2n OOM1 MU2 WM2 LOW2 ltac:(unfold A_OOM_CELL; clear; lia).
        - eapply ro_cells_transport; [exact MRN1| exact MU2| apply LOW2; unfold A_MRN_CELL; cbn; clear; lia].
        - t2n ERR1 MU2 WM2 LOW2 ltac:(unfold A_ERRNO; clear; lia).
        - t2n FR16 MU2 WM2 HI2 ltac:(rewrite ?SPAE, ?STKE; clear; lia).
        - t2n FR7 MU2 WM2 HI2 ltac:(rewrite ?SPAE; clear; lia).
        - t2n FJ MU2 WM2 HI2 ltac:(rewrite ?SPAE, ?STKE; clear; lia).
        - t2n STKC MU2 WM2 HI2 ltac:(rewrite ?SPAE, ?STKE; clear; lia).
        - eapply u64arr_transport; [exact HTR| exact MU2| exact WM2| apply HI2; rewrite ?SPAE, ?STKE; clear; lia].
        - exact HL30.
        - t2n F1800 MU2 WM2 HI2 ltac:(rewrite ?SPAE, ?STKE; clear; lia).
        - t2n TFBP MU2 WM2 HI2 ltac:(rewrite ?SPAE, ?STKE; clear; lia).
        - t2n F8 MU2 WM2 HI2 ltac:(rewrite ?SPAE, ?STKE; clear; lia).
        - exact ST2.
        - exact SCS.
        - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; rewrite ?SPAE; clear; intros x Hx; lia.
        - exact WM2.
        - exact MI2. }
      cbn beta. intros ms3 mo3 PO3 HK3 MM3 HJ3.
      ddestruct PO3 as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m3 & -> & MU3 & WM3 & MI3 & OOM3 & ERR3 & ST3).
      apply aevtS_now. unfold msec_post.
      eexists. dexists mo3, 0, sc, r, nb0, bl0. dexists y0, y1, y2, ya1, ya2, ya3, ya4, ya5, ya6, ya7, y3, y4, y5, y6. exists m3.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HK3|]. split; [exact HJ3|].
      split; [exact (wmono_trans _ _ _ _ WM1 WM3)|]. split; [exact MI3|]. split; [exact ST3|].
      split; [intros y Hy; exact Hy|].
      split; [eapply rw_cells_transport; [exact UNW1| exact MU3| exact WM3| unfold A_OOM_CELL, A_ERRNO; cbn; clear - T0 T1 LOIMG; lia]|].
      left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      split.
      { eapply munch_trans. { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
        eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
      split; [exact OOM3| exact ERR3].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End CallocSec.

End ARUN_1.
