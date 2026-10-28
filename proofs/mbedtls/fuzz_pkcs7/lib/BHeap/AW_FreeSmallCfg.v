(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Arr Bytes Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA AShadow AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AKinv AJ AKinvS ASpinS AW_MmapAnon AW_MmapDie ASpin
     AW_DepotA AW_DepotB AW_DepotC AW_DepotD AW_DepotE AW_DepotF AW_DepotCfg AW_DepotInv AW_DepotTop
     AW_MallocA AW_Poison AW_DKeep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_IMemset AW_IAInit AW_Dealloc AW_FreeA AW_QPut AW_Enqueue AW_FreeC AW_FreeTop.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

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
Ltac2 gd_tbl_AW_FreeSmallCfg () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeTop.img_dj"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dblk"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.sblk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeTop.free_statics"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.A_DEP_END"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.true"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_IA_INIT"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_IA"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_cs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_statics"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.div"; "Corelib.Lists.ListDef.Forall"; "ARUN_1.FreeSmall.fkeep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.hdr_w0"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_QUARANTINE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Dealloc.hdr_rest"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Enqueue.qc_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Enqueue.batch_hdr"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_IAInit.ia_cells"].

Section ARUN_1. Context {hAR : arun}.
Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L11575425235.14L19681308371.20L20825257299.14L21632378003.15L33590297747.20L33907719379.20L38705866195.15L38705866195.20L45338772563.20L47582725459.14L67992941459.20L8050298835.20 00000100200300400500600700800900:00;00<SSSSSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma depot_statics_transport_ia : forall W m m', depot_statics m -> munch W m m' -> img_dj W -> depot_statics m'.
Proof.
  (intros W m m' dd_H; ddestruct dd_H as (DS & CS & c1 & c2 & c3 & M1 & M2 & M3); intros MU DJ). unfold img_dj, A_IA, A_IA_INIT in DJ. split; [|split].
  - destruct DS as [G1 G2]. split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ]); unfold A_GOT_CFLAGS, A_CFLAGS; cbn; lia.
  - ddestruct CS as (X1 & X2 & X3 & X4 & X5 & X6 & X7). unfold cstatics.
    unfold A_GOT_PAGESZ, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_DECORATE, A_MMAP_LIMIT, A_GOT_SEALED2, A_DYING in *.
    repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
  - dexists c1, c2, c3. unfold A_MUR1, A_MUR2, A_MUR3 in *.
    repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ]); cbn; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L19394699669.30L2410573878.30 L25879006102.30L26036254134.30L27135284108.30L280658870.30  L32646196606.30L37415595997.18L38467752502.35L40013342870.30L47519317174.30L50687857481.30L9397011990.30 00000>00L00Z00h01601D01R01]02002>02L02Z02hS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS1A1n2H12H2S2nb2tf2bl3DML1i2HiS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DMLS2nb2tf2bl3DML". (* [comment removed for export] *)
#[using="Type"] Lemma depot_inv_transport_ia : ltac2:(CDefT.buildp (gd_tbl_AW_FreeSmallCfg ()) "PW,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PN,$4.Pnb,(0.$4.)Ptf,$4.Pbl,(0.$4.)P,(5.VhAR,R6.R4.R3.R2.R1.)P,(6.R8.R7.R6.)P,(7.$8.R8.R7.)P,(9.R:.)P,Pk,$4.P,(:.(;.=R1.)(<.R1.(=.(>.$4.R8.))))(?.R=.(10.R9.R2.)(11.+2.+14.))P,Pj,$4.P,(:.(;.=R1.)(<.R1.(=.(>.$4.R7.))))(?.R>.(12.R8.R2.)(11.+2.+17.))(5.VhAR,R;.R:.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros W m m' N nb tf bl DI MU WM DJ DN DS.
  assert (LO : forall A n, A_SS <= A -> A + n <= 0x65f000 -> disjoint_from W A n).
  { intros A n H1 H2. apply DJ. right; right. unfold A_SS, A_IA_INIT in *. lia. }
  ddestruct DI as (NC & DT & DM & DNO & WF & MX & (alloc & SSX) & DB & SB & TF0 & BL & BA).
  dpose DM as (DM1 & DMF & DML).
  split. { eapply rw_cells_transport; [exact NC| exact MU| exact WM| apply LO; unfold A_DEP_N, A_SS; cbn; lia]. }
  split. { eapply (dtab_transport _ m m' N DT MU WM). intros; apply LO; unfold A_DEP, A_SS; lia. }
  split. { eapply (dmap1_transport _ m m' nb DM MU WM). intros; apply LO; unfold A_DEP_MAP1, A_SS; lia. }
  split. { eapply (dnodes_transport _ m m' nb N DNO MU WM DMF). intros b Hb.
           ddestruct (In_nth nb b 0 Hb) as (i & Hi & E). specialize (DN (Z.of_nat i) ltac:(lia)). unfold dblk in DN. rewrite Nat2Z.id, E in DN. exact DN. }
  split; [exact WF|].
  split. { eapply rw_cells_transport; [exact MX| exact MU| exact WM| apply LO; unfold A_DEP_NODES, A_SS; cbn; lia]. }
  split. { exists alloc. eapply rw_cells_transport; [exact SSX| exact MU| exact WM| apply LO; unfold A_SS; cbn; lia]. }
  split. { eapply (dblocks_transport _ m m' bl DB MU WM). intros; apply LO; unfold A_SS; lia. }
  split. { eapply (sblks_transport _ m m' bl SB MU WM). exact DS. }
  split; [exact TF0|]. split; [exact BL| exact BA].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L12660386896.33L14112175056.33L21338765340.23L27898523728.33L28175603024.33L55228533968.33L55320813904.33L62224286800.33L63835560016.33L63846273118.2300000100200300400500600700800900:SSSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma free_statics_transport2 : ltac2:(CDefT.buildp (gd_tbl_AW_FreeSmallCfg ()) "PW,(0.$1.)PWt,(0.$1.)PWc,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Pm',P,(2.&40.)(3.(2.&8.))PT,$4.PCTX,$4.P,(13.R4.R2.R1.)P,(6.R8.R5.R4.)P,(6.R8.R6.R5.)P,(6.R8.R7.R6.)P,PA,$4.Pn,$4.P,(14.(:.(;.+10000.R2.)(;.(15.R2.R1.)$16.))(:.(;.$17.R2.)(;.(15.R2.R1.)+65?000.)))(?.R>.R3.R2.)P,(?.R;.R7.+8.)P,(?.R;.(15.R7.+8.)+4.)P,(?.R<.(15.R8.+98.)+8.)(13.R;.R:.R9.)")
(* [comment removed for export] *).
Proof.
  (intros W Wt Wc m m' T CTX dd_H; ddestruct dd_H as (FS & MF & TT & C8 & QM & GF & FL & PS); intros MU MUt MUc DJ D1 D2 D3).
  unfold free_statics.
  split. { unfold fsegA_statics in *.
           unfold A_ASAN_INITED, A_MCS_CELL, A_GOT_CFLAGS, A_CFLAGS, A_CF_FASTUNW, A_GOT_PAGESZ, A_PAGESZ_CELL, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_SS, A_DEP_END in *.
           decompose [and] FS. repeat split; first [eapply ro_cells_transport; [eassumption| exact MUc| exact D3]
                                                   | eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]]. }
  unfold A_MFHOOKS, A_Q_MAX, A_GOT_FLAGS_, A_FLAGS, A_INSTANCE, A_SS, A_DEP_END in *.
  split; [eapply ro_cells_transport; [exact MF| exact MU| apply DJ; cbn; lia]|].
  split; [eapply ro_cells_transport; [exact TT| exact MUt| exact D1]|].
  split; [eapply ro_cells_transport; [exact C8| exact MUc| exact D2]|].
  split; [eapply ro_cells_transport; [exact QM| exact MU| apply DJ; cbn; lia]|].
  split; [eapply ro_cells_transport; [exact GF| exact MU| apply DJ; cbn; lia]|].
  split; [eapply ro_cells_transport; [exact FL| exact MU| apply DJ; cbn; lia]|].
  eapply poison_statics_transport; [exact PS| exact MU| intros A n H; apply DJ; left; exact H].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section FreeSmall.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CSf : list Z -> list Z -> Z -> Prop.
  Variable K : list Z -> list Z -> Model -> Prop.
  Hypothesis CSOKf : forall nb bl, cs_ok AL (CSf nb bl).
  Hypothesis KL : forall nb bl, kinv AL (CSf nb bl) (K nb bl).
  Hypothesis CSmono_n : forall nb bl a x, CSf nb bl x -> CSf (nb ++ [a]) bl x.
  Hypothesis CSmono_s : forall nb bl a x, CSf nb bl x -> CSf nb (bl ++ [a]) x.
  Hypothesis K_apart : ltac2:(CDefT.buildp (gd_tbl_AW_FreeSmallCfg ()) "Pnb,(0.$4.)Pbl,(0.$4.)Pmo,$18.Pa,(2.&40.)Pn,(2.&40.)P,A3.VK,R5.R4.R3.P,(19.$1:.(1;.(1<.(1=.(2.&40.)(2.&40.))(1>.(1?.R4.))(20.(1?.R4.)))R3.R2.)$21.)P,(;.+10000.(22.&40.R3.))P,(;.(15.(22.&40.R5.)(22.&40.R4.))(23.VhAR,))Px,$4.P,(14.A3.VCSf,R:.R9.R1.(:.(;.(24.VAL,)R1.)(<.R1.(25.VAL,))))(26.(:.(;.(22.&40.R8.)R2.)(<.R2.(15.(22.&40.R8.)(22.&40.R7.)))))")
(* [comment removed for export] *).
  Variables (Gn Gs : list Z -> list Z -> Prop).   (* [comment removed for export] *)
  Hypothesis T_node : ltac2:(CDefT.buildp (gd_tbl_AW_FreeSmallCfg ()) "Pnb,(0.$4.)Pbl,(0.$4.)Pmo,$18.Pa,(2.&40.)P,A2.VGn,R4.R3.P,A3.VK,R5.R4.R3.P,(19.$4.(27.(22.&40.R3.)+1000.)=)P,(<.=(22.&40.R4.))P,(;.(15.(22.&40.R5.)(11.+2.+14.))(23.VhAR,))P,(19.$1:.(1;.(1<.(1=.(2.&40.)(2.&40.))(1>.(1?.R7.))(20.(1?.R7.)))R6.(28.&40.(11.+2.+14.)))$21.)(:.A3.VK,(1<.$4.R:.(29.$4.(22.&40.R7.)(2:.$4.)))R9.(2;.+22.R7.(11.+2.+14.)R8.)(2<.A2.VCSf,(1<.$4.R:.(29.$4.(22.&40.R7.)(2:.$4.)))R9.(22.&40.R7.)(11.+2.+14.)))")
(* [comment removed for export] *).
  Hypothesis T_store : ltac2:(CDefT.buildp (gd_tbl_AW_FreeSmallCfg ()) "Pnb,(0.$4.)Pbl,(0.$4.)Pmo,$18.Pa,(2.&40.)P,A2.VGs,R4.R3.P,A3.VK,R5.R4.R3.P,(19.$4.(27.(22.&40.R3.)+1000.)=)P,(<.=(22.&40.R4.))P,(;.(15.(22.&40.R5.)(11.+2.+17.))(23.VhAR,))P,(19.$1:.(1;.(1<.(1=.(2.&40.)(2.&40.))(1>.(1?.R7.))(20.(1?.R7.)))R6.(28.&40.(11.+2.+17.)))$21.)(:.A3.VK,R:.(1<.$4.R9.(29.$4.(22.&40.R7.)(2:.$4.)))(2;.+4022.R7.(11.+2.+17.)R8.)(2<.A2.VCSf,R:.(1<.$4.R9.(29.$4.(22.&40.R7.)(2:.$4.)))(22.&40.R7.)(11.+2.+17.)))")
(* [comment removed for export] *).
  Hypothesis ROOM_n : forall nb bl mo, Gn nb bl -> K nb bl mo -> exists a, anon_grantable 0x22 (2^20) mo a.
  Hypothesis ROOM_s : forall nb bl mo, Gs nb bl -> K nb bl mo -> exists a, anon_grantable 0x4022 (2^23) mo a.
  Hypothesis CSf_noshadow : forall nb bl x, CSf nb bl x -> ~ (0x7fff8000 <= x < 0x10007fff8000).
  Hypothesis ASB : al_sb AL = 0x7fff8000.

  (* [comment removed for export] *)
  Variables (SP p b1 n ctx lo T CTX TOP len first last bytes bsize : Z) (elems : list word).
  Let STK := SP + -2128.
  Let k := (n + 7) / 8.
  Let SH := 0x7fff8000 + p / 8.
  Hypothesis PL : 0x10007fff8008 <= p. Hypothesis PH : p + 8 + 8 * k <= ACEIL. Hypothesis PA : p mod 16 = 0.
  Hypothesis NB : 0 <= n <= 2^28. Hypothesis CTXB : 0 <= ctx < 2^32. Hypothesis B1B : 0 <= b1 < 256. Hypothesis B13 : Z.land b1 3 = 1.
  Hypothesis LOIMG : ACEIL <= lo.
  Hypothesis SPL : lo <= SP - 4096.
  Hypothesis SPA16 : SP mod 16 = 0.
  Hypothesis TOP0 : 2^23 <= TOP. Hypothesis TOP1 : TOP <= 2^47. Hypothesis TOP2 : SP + 16 <= 2^47.   (* [comment removed for export] *)
  Hypothesis T0 : (Timg T /\ Tband T). Hypothesis T1 : T + 4096 <= ACEIL.
  Hypothesis CX0 : 0x65f000 <= CTX. Hypothesis CX1 : CTX + 0x10000 <= ACEIL.
  Hypothesis TC : T + 4096 <= CTX \/ CTX + 0x10000 <= T.
  Hypothesis CTXNS : CTX + 0x10000 <= 0x7fff8000 \/ 0x10007fff8000 <= CTX.
  Hypothesis L0 : 1 <= len < 2^63. Hypothesis F0 : 0 <= first < 2^64.
  Hypothesis LA0 : 0x10007fff8000 <= last. Hypothesis LA1 : last + 8192 <= ACEIL.
  Hypothesis BY0 : 0 <= bytes. Hypothesis BY1 : bytes + n <= kQuarantineCache.
  Hypothesis BS0 : 0 <= bsize. Hypothesis BS1 : bsize + n < 2^63.
  Hypothesis EL : (length elems < 1021)%nat.
  (* [comment removed for export] *)
  Hypothesis APT : T + 4096 <= p - 16 \/ p + 8 + 8 * k <= T.
  Hypothesis APC : CTX + 0x10000 <= p - 16 \/ p + 8 + 8 * k <= CTX.
  Hypothesis APS : Z.max TOP SP <= p - 16 \/ p + 8 + 8 * k <= lo.   (* [comment removed for export] *)
  Hypothesis ALP : p + 8 + 8 * k <= last \/ last + 8192 <= p - 16.
  Hypothesis ALT : T + 4096 <= last \/ last + 8192 <= T.
  Hypothesis ALC : CTX + 0x10000 <= last \/ last + 8192 <= CTX.
  Hypothesis ASL : Z.max TOP SP <= last \/ last + 8192 <= lo.
  Hypothesis AST : Z.max TOP SP <= T \/ T + 4096 <= lo.
  Hypothesis ASC : Z.max TOP SP <= CTX \/ CTX + 0x10000 <= lo.

  (* [comment removed for export] *)
  Definition fkeep (m m' : mem) (nb bl : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeSmallCfg ()) "Px,(2.&40.)Za,$4.(22.&40.R1.)P,(26.(:.(;.Vlo,R1.)(<.R1.VSP,)))P,(26.(:.(;.$16.R2.)(<.R2.$17.)))P,Pk,$4.P,(:.(;.=R1.)(<.R1.(=.(>.$4.O2.))))(26.(:.(;.(10.O2.R2.)R5.)(<.R5.(15.(10.O2.R2.)(11.+2.+14.)))))P,Pj,$4.P,(:.(;.=R1.)(<.R1.(=.(>.$4.O1.))))(26.(:.(;.(12.O1.R2.)R6.)(<.R6.(15.(12.O1.R2.)(11.+2.+17.)))))P,(26.(:.(;.$2=.R5.)(<.R5.(15.$2=.+4.))))P,(26.(:.(;.$2>.R6.)(<.R6.(15.$2>.+1.))))P,(26.(:.(;.(15.$2>.+8.)R7.)(<.R7.(15.(15.$2>.+8.)+40000.))))P,(26.(:.(;.(15.$2>.+40040.)R8.)(<.R8.(15.(15.$2>.+40040.)+=80.))))P,(26.(:.(;.(15.$2>.+40=<0.)R9.)(<.R9.(15.(15.$2>.+40=<0.)+40248.))))P,(26.(:.(;.(15.$2>.+81008.)R:.)(<.R:.(15.(15.$2>.+81008.)+28.))))P,(26.(:.(;.(15.VT,+50.)R;.)(<.R;.(15.VT,+70.))))P,(26.(:.(;.(15.VT,+;08.)R<.)(<.R<.(15.VT,+;18.))))P,(26.(:.(;.(15.VT,+<60.)R=.)(<.R=.(15.VT,+<61.))))P,(26.(:.(;.(15.Vp,-10.)R>.)(<.R>.(15.Vp,-<.))))P,(26.(:.(;.Vp,R?.)(<.R?.(15.Vp,+8.))))P,(26.(:.(;.VSH,R10.)(<.R10.(15.VSH,Vk,))))P,(26.(:.(;.Vlast,R11.)(<.R11.(15.Vlast,+2000.))))(19.(3.(2.&8.))A1.O3.R13.A1.O4.R13.)")
(* [comment removed for export] *).

  Definition ftop_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (N tf d : Z) (nb bl : list Z) (m0 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeSmallCfg ()) "Lcf,$2?.(30.$31.Lms',$31.(30.$18.Lmo',$18.(30.(0.$4.)Lnb',(0.$4.)(30.(0.$4.)Lbl',(0.$4.)(30.$4.LN',$4.(30.$4.Ltf',$4.(30.$4.Lid,$4.(30.(2.&40.)Lt0,(2.&40.)(30.(2.&40.)Lt1,(2.&40.)(30.(2.&40.)Lt2,(2.&40.)(30.(2.&40.)La0,(2.&40.)(30.(2.&40.)La1,(2.&40.)(30.(2.&40.)La2,(2.&40.)(30.(2.&40.)La3,(2.&40.)(30.(2.&40.)La4,(2.&40.)(30.(2.&40.)La5,(2.&40.)(30.(2.&40.)La6,(2.&40.)(30.(2.&40.)La7,(2.&40.)(30.(2.&40.)Lt3,(2.&40.)(30.(2.&40.)Lt4,(2.&40.)(30.(2.&40.)Lt5,(2.&40.)(30.(2.&40.)Lt6,(2.&40.)(30.(2.&40.)Lfr',(2.&40.)(30.(2.&40.)Lfd',(2.&40.)(30.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(:.(19.$2?.R1:.(32.R19.R18.))(:.(19.$31.R19.(33.(34.O16.(28.&40.VSP,)O15.(28.&40.$35.)R12.R11.R10.O14.O13.R?.R>.R=.R<.R;.R:.R9.R8.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R7.R6.R5.R4.)O8.(36.O16.)O7.(37.(2.&40.))R1.(38.$8.)))(:.A3.VK,R17.R16.R18.(:.(39.R1.R18.)(:.(5.VhAR,R1.R15.R17.R14.R16.)(:.(3:.A2.VCSf,R17.R16.R17.R16.)(:.(3;.R1.)(:.(:.(;.+1.R13.)(;.R13.R15.))(:.(:.(;.O6.R15.)(;.R15.(15.O6.+1.)))(:.(:.(;.O5.R14.)(;.R14.(15.O5.(3<.+2.(15.O4.+3.)))))(:.(;.(3=.R14.(3<.+1?.(3>.R14.(11.+2.+14.))))(15.(3=.O5.(3<.+1?.(3>.O5.(11.+2.+14.))))(15.O4.+3.)))(:.Px,$4.P,A3.VCSf,O3.O2.R1.A3.VCSf,R19.R18.R2.(:.(30.(0.$4.)Lsn,(0.$4.)(30.(0.$4.)Lsb,(0.$4.)(:.(19.(0.$4.)R19.(1<.$4.O3.R2.))(:.(19.(0.$4.)R18.(1<.$4.O2.R1.))(:.(3?.$4.Lb,$4.Px,$4.P,A3.VCSf,O3.O2.R1.(26.(:.(;.R3.R2.)(<.R2.(15.R3.(11.+2.+14.)))))R2.)(3?.$4.Lb,$4.Px,$4.P,A3.VCSf,O3.O2.R1.(26.(:.(;.R3.R2.)(<.R2.(15.R3.(11.+2.+17.)))))R1.))))))(:.(40.O1.R1.R17.R16.)(:.(7.$8.O1.R1.)(:.(41.$8.R1.)(:.(42.$8.R1.Vlo,VSP,)(:.(43.$8.R1.(15.Vp,-10.)(44.Vb1,$45.))(:.(43.$8.R1.(15.Vp,-<.)(46.Vn,Vctx,))(:.(47.$8.R1.Vp,+8.)(:.(43.$8.R1.VSH,(29.$48.(49.(4:.Vk,)(4;.(2.&8.)(28.&8.+?=.)(4:.Vk,)))(2:.$48.)))(:.(43.$8.R1.(15.VT,+50.)(4<.Vlen,Vfirst,Vlast,(15.Vbytes,Vn,)))(:.(43.$8.R1.Vlast,(4=.=(15.Vbsize,Vn,)(15.(=.(>.(2.&40.)Velems,))+1.)))(:.(4>.$8.R1.(15.Vlast,+18.)(1<.(2.&40.)Velems,(29.(2.&40.)(28.&40.(15.Vp,-10.))(2:.(2.&40.)))))(:.(47.$8.R1.Vlast,+2000.)(:.(43.$8.R1.(15.VT,+;08.)(29.$48.(4?.R3.)(29.$48.(4?.R2.)(2:.$48.))))(:.(43.$8.R1.(15.VT,+<60.)(29.$48.(50.(28.&8.=))(2:.$48.)))(51.R1.)))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  End FreeSmall.

End ARUN_1.
