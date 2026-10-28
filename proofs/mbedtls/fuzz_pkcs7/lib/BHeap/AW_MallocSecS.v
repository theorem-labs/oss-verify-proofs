(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem Arr Bytes Asn1Aux CellsX SysStep ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import DivergeSim.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtS AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AKinv AJ AKinvS ASpinS AW_MmapAnon AW_MmapDie ASpin
     AW_DepotA AW_DepotB AW_DepotC AW_DepotD AW_DepotE AW_DepotF AW_DepotCfg AW_DepotInv AW_DepotTop
     AW_MallocA AW_AllocA AW_Poison AW_AllocB AW_MallocB AW_MallocC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_CfgS AW_ClassId AW_Combined AW_Refill AW_GetFrom AW_Populate AW_Populate2 AW_CfgDefs
     AW_Large AW_MapOrDie AW_LargeCfgS AW_MmapFixedNR AW_PoisonBig AW_PoisonBigCfg AW_MallocGenLib AW_MallocGen AW_SecB AW_SecC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ahx.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ahx. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_MallocSecS () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_SEALED2"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DYING"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PoisonBig.rsmr_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.A_DEP_END"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Large.large_statics"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.true"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Corelib.Init.Logic.not"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_fresh"; "Stdlib.Lists.List.In"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.anon_grantable"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PoisonBigCfg.poison0_siteS"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "ARUN_1.dstat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "ARUN_1.DIE_NEED"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.die_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.A_SPIN_MMAPDIE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MapOrDie.mod_answered"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rounded"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.dblk"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.sblk"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.J"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_inv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_cs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotTop.depot_statics"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "Corelib.Lists.ListDef.Forall"; "ARUN_1.MallocSec.skeep"; "ARUN_1.MallocSec.SecChunk.swin"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kAllocBegMagic"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C2"; "Stdlib.ZArith.BinInt.Z.lor"; "Stdlib.ZArith.BinInt.Z.land"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.pgv"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.fin_statics"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_GOT_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_FLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocB.A_FL_PPART"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_AllocA.allocA_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MallocA.A_PC_MALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "ARUN_1.MallocSec.SecChunk.sec_chunk_post"; "Stdlib.ZArith.BinInt.Z.b2z"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.from_primary"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

(* [comment removed for export] *)
Definition dstat (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "(0.(1.$2.O1.$3.(4.$5.(6.(7.&40.+1.))(8.$5.)))(1.$2.O1.$9.(4.$5.(:.(7.&40.=))(8.$5.))))")
(* [comment removed for export] *).
Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L10929582012.8L35363529646.8L41425883566.8L67982786620.8000001002003004SSSS". (* [comment removed for export] *)
#[using="Type"] Lemma dstat_transport : forall W m m', dstat m -> munch W m m' -> img_static_ok W -> dstat m'.
Proof.
  intros W m m' [S1 S2] MU DJ. unfold img_static_ok in DJ. unfold dstat, A_GOT_SEALED2, A_DYING, A_INSTANCE in *.
  split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
#[using="Type"] Lemma dstat_of_rsmr : forall m can dd madv, rsmr_statics m can dd madv -> dstat m.
Proof. intros m can dd madv R. unfold rsmr_statics in R. unfold dstat. decompose [and] R. split; assumption. Qed.
Definition DIE_NEED : Z := 1024.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00T0?L10162850323.22L10581581829.22L10927674117.22L10999894547.22L11721083141.22L12154443539.22L14438195155.22L14673793797.22L15620866579.22L199237139.22  L2514843909.22 L27248877335.22L27345870981.22L3232864535.22 L35365822231.22L35516973829.22L37932560663.22L41423990039.22L42309462295.22L46452558359.22L47260142871.22L48438033939.22L49474115845.22L51751710099.22L55758797957.22L56418622995.22L56469219091.22L6059544325.22 L6323588375.22 L65757338903.22L65950690707.22L67644472887.22L67984702597.22L8266780183.22 L8343692293.22 L8838151699.22 00000100200300400500600700800900:00;00<00=00>00?00@00A00B00C00D00E00F00G00H00I00J00K00L00M00N00O00P00Q00R00S00TSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma rsmr_statics_transport2 : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "PW,(;.$<.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))Pcan,(=.&40.)Pdd,(=.&8.)Pmadv,(=.&8.)P,(?.R5.R3.R2.R1.)P,(10.R7.R6.R5.)P,PA,$11.Pn,$11.P,(0.(12.+10000.R2.)(12.(13.R2.R1.)+65?000.))P,(14.(12.(13.R3.R2.)$15.)(12.$16.R3.))P,(14.(12.(13.R4.R3.)(13.$17.+70.))(12.(13.$17.+2=0.)R4.))(18.R=.R5.R4.)(?.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros W m m' can dd madv S MU DJ. unfold rsmr_statics in *.
  unfold A_GOT_CANARY, A_CANARY, A_LIBC_PAGESZ, A_GOT_CFLAGS, A_CFLAGS, A_MMAP_LIMIT, A_CF_DONTDUMP, A_GOT_SEALED2, A_GOT_PAGESZ, A_PAGESZ_CELL,
    A_GOT_DYING, A_DYING, A_MADV_FLAG, A_SS, A_DEP_END, A_INSTANCE in *.
  decompose [and] S. repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L2706816914.11 L27235009686.11L28489209988.11L40363891090.11L40810955414.11L43246695075.11L51787544415.11L64621320831.11L8229534852.11 000001002003004005006007008009SSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma large_statics_transport2 : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "PW,(;.$<.)Pm,P,(=.&40.)(>.(=.&8.))Pm',P,(=.&40.)(>.(=.&8.))PPA,$11.P,(19.R3.R1.)P,(10.R5.R4.R3.)P,PA,$11.Pn,$11.P,(0.(12.+10000.R2.)(12.(13.R2.R1.)+65?000.))P,(14.(12.(13.R3.R2.)$15.)(12.$16.R3.))P,(14.(12.(13.R4.R3.)(13.$17.+70.))(12.(13.$17.+2=0.)R4.))(18.R;.R5.R4.)(19.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros W m m' PA S MU DJ. unfold large_statics in *. unfold A_GOT_LNAME, A_LNAME_CELL, A_LNAME, A_SS, A_DEP_END, A_INSTANCE in *.
  decompose [and] S. repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section MallocSec.
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
  Let STK := SP + -2128.
  Let SPA := SP + -2128 + -16.
  Let ms := map_size (needed2 n).
  Hypothesis NB : 0 <= n < 2^31.
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
  Hypothesis GSEP : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "(0.(14.(12.(13.VT,+1000.)VSB,)(12.(13.(13.VSB,(1:.+2.+25.))+1000.)VT,))(0.(14.(12.(13.VCTX,+10000.)VT,)(12.(13.VT,+1000.)VCTX,))(0.(14.(12.(13.VCTX,+10000.)VSB,)(12.(13.(13.VSB,(1:.+2.+25.))+1000.)VCTX,))(0.(14.(12.(13.VT,+1000.)VPA,)(12.(13.VPA,+800000.)VT,))(14.(12.(13.VCTX,+10000.)VPA,)(12.(13.VPA,+800000.)VCTX,))))))")
(* [comment removed for export] *).
  Hypothesis CST : forall sc r nb bl, crange (CSf sc r nb bl) T 4096.
  Hypothesis CSCTX : forall sc r nb bl, crange (CSf sc r nb bl) CTX 0x10000.
  Hypothesis CSPA : forall sc r nb bl, 0 <= r -> 0x20000 * r <= 0x800000 -> crange (CSf sc r nb bl) PA (0x20000 * r).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable Gl : list (Z * Z) -> Z -> Z -> Prop.
  Variable Gp : list (Z * Z) -> Z -> Prop.
  Let U (r : Z) := PA + 0x20000 * r.
  Hypothesis K_apart_l : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Psc,(;.(1;.$11.$11.))Pr,$11.Pmo,$1<.Pa,(=.&40.)Pw,(=.&40.)P,A5.VK,R5.R4.Vnb0,Vbl0,R3.P,(1=.$1>.(1?.(20.(1;.(=.&40.)(=.&40.))(21.(22.R4.))(23.(22.R4.)))R3.R2.)$24.)P,(12.+10000.(25.&40.R3.))P,(12.(13.(25.&40.R5.)(25.&40.R4.))(26.VhAR,))Py,$11.P,(14.A5.VCSf,R:.R9.Vnb0,Vbl0,R1.(14.(0.(12.(27.VAL,)R1.)(28.R1.(29.VAL,)))(14.(0.(12.+7???7000.R1.)(28.R1.+10007???8000.))(0.(12.VPA,R1.)(28.R1.(13.VPA,+800000.))))))(2:.(0.(12.(25.&40.R8.)R2.)(28.R2.(13.(25.&40.R8.)(25.&40.R7.)))))")
(* [comment removed for export] *).
  Hypothesis T_large : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Psc,(;.(1;.$11.$11.))Pr,$11.Pmsz,$11.Pmo,$1<.Pa,(=.&40.)P,A3.VGl,R5.R4.R3.P,A5.VK,R6.R5.Vnb0,Vbl0,R3.P,(1=.$11.(2;.(25.&40.R3.)+1000.)=)P,(28.=(25.&40.R4.))P,(12.(13.(25.&40.R5.)R7.)(26.VhAR,))P,(1=.$1>.(1?.(20.(1;.(=.&40.)(=.&40.))(21.(22.R7.))(23.(22.R7.)))R6.(7.&40.R8.))$24.)(0.A5.VK,(20.(1;.$11.$11.)R;.(4.(1;.$11.$11.)(2<.$11.$11.(25.&40.R7.)R9.)(8.(1;.$11.$11.))))R:.Vnb0,Vbl0,(2=.+22.R7.R9.R8.)(2>.A4.VCSf,(20.(1;.$11.$11.)R;.(4.(1;.$11.$11.)(2<.$11.$11.(25.&40.R7.)R9.)(8.(1;.$11.$11.))))R:.Vnb0,Vbl0,(25.&40.R7.)R9.))")
(* [comment removed for export] *).
  Hypothesis LEDGER_P : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Psc,(;.(1;.$11.$11.))Pr,$11.Pmo,$1<.P,A2.VGp,R3.R2.P,A5.VK,R4.R3.Vnb0,Vbl0,R2.(0.(1=.$1>.(1?.(21.(22.R3.))(7.&40.A1.VU,R4.)(7.&40.+20000.))$24.)(14.(1=.$1>.(2?.(23.(22.R3.))(7.&40.A1.VU,R4.)(7.&40.+20000.))$24.)(1=.$1>.(1?.(20.(1;.(=.&40.)(=.&40.))(21.(22.R3.))(23.(22.R3.)))(7.&40.A1.VU,R4.)(7.&40.+20000.))$24.)))")
(* [comment removed for export] *).
  Hypothesis TP_commit : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Psc,(;.(1;.$11.$11.))Pr,$11.Pmo,$1<.P,A2.VGp,R3.R2.P,A5.VK,R4.R3.Vnb0,Vbl0,R2.P,(1=.$1>.(2?.(23.(22.R3.))(7.&40.A1.VU,R4.)(7.&40.+20000.))$24.)(0.A5.VK,R6.(13.R5.+1.)Vnb0,Vbl0,(30.+32.A1.VU,R5.+20000.R4.)(2>.A4.VCSf,R6.(13.R5.+1.)Vnb0,Vbl0,A1.VU,R5.+20000.))")
(* [comment removed for export] *).
  Hypothesis TP_fresh : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Psc,(;.(1;.$11.$11.))Pr,$11.Pmo,$1<.P,A2.VGp,R3.R2.P,A5.VK,R4.R3.Vnb0,Vbl0,R2.P,(1=.$1>.(1?.(20.(1;.(=.&40.)(=.&40.))(21.(22.R3.))(23.(22.R3.)))(7.&40.A1.VU,R4.)(7.&40.+20000.))$24.)(0.A5.VK,R6.(13.R5.+1.)Vnb0,Vbl0,(31.+32.A1.VU,R5.+20000.R4.)(2>.A4.VCSf,R6.(13.R5.+1.)Vnb0,Vbl0,A1.VU,R5.+20000.))")
(* [comment removed for export] *).
  Hypothesis ROOM_P : forall sc r mo, Gp sc r -> K sc r nb0 bl0 mo -> fixrw_grantable 0x32 (U r) 0x20000 mo.
  (* [comment removed for export] *)
  Hypothesis SEC_APART : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Psc,(;.(1;.$11.$11.))Pr,$11.Pnb,(;.$11.)Pbl,(;.$11.)Pmo,$1<.Pp,(1;.$11.$11.)P,A5.VK,R6.R5.R4.R3.R2.P,(32.(1;.$11.$11.)R2.R7.)(14.(12.(13.(33.$11.$11.R3.)(34.$11.$11.R3.))VSB,)(12.(13.(13.VSB,(1:.+2.+25.))+1000.)(33.$11.$11.R3.)))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Hypothesis K_apart : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Psc,(;.(1;.$11.$11.))Pr,$11.Pnb,(;.$11.)Pbl,(;.$11.)Pmo,$1<.Pa,(=.&40.)Pw,(=.&40.)P,A5.VK,R7.R6.R5.R4.R3.P,(1=.$1>.(1?.(20.(1;.(=.&40.)(=.&40.))(21.(22.R4.))(23.(22.R4.)))R3.R2.)$24.)P,(12.+10000.(25.&40.R3.))P,(12.(13.(25.&40.R5.)(25.&40.R4.))(26.VhAR,))Px,$11.P,(14.A5.VCSf,R<.R;.R:.R9.R1.(0.(12.(27.VAL,)R1.)(28.R1.(29.VAL,))))(2:.(0.(12.(25.&40.R8.)R2.)(28.R2.(13.(25.&40.R8.)(25.&40.R7.)))))")
(* [comment removed for export] *).
  Variables (Gn Gs : list (Z * Z) -> Z -> list Z -> list Z -> Prop).
  Hypothesis T_node : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Psc,(;.(1;.$11.$11.))Pr,$11.Pnb,(;.$11.)Pbl,(;.$11.)Pmo,$1<.Pa,(=.&40.)P,A4.VGn,R6.R5.R4.R3.P,A5.VK,R7.R6.R5.R4.R3.P,(1=.$11.(2;.(25.&40.R3.)+1000.)=)P,(28.=(25.&40.R4.))P,(12.(13.(25.&40.R5.)(1:.+2.+14.))(26.VhAR,))P,(1=.$1>.(1?.(20.(1;.(=.&40.)(=.&40.))(21.(22.R7.))(23.(22.R7.)))R6.(7.&40.(1:.+2.+14.)))$24.)(0.A5.VK,R<.R;.(20.$11.R:.(4.$11.(25.&40.R7.)(8.$11.)))R9.(2=.+22.R7.(1:.+2.+14.)R8.)(2>.A4.VCSf,R<.R;.(20.$11.R:.(4.$11.(25.&40.R7.)(8.$11.)))R9.(25.&40.R7.)(1:.+2.+14.)))")
(* [comment removed for export] *).
  Hypothesis T_store : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Psc,(;.(1;.$11.$11.))Pr,$11.Pnb,(;.$11.)Pbl,(;.$11.)Pmo,$1<.Pa,(=.&40.)P,A4.VGs,R6.R5.R4.R3.P,A5.VK,R7.R6.R5.R4.R3.P,(1=.$11.(2;.(25.&40.R3.)+1000.)=)P,(28.=(25.&40.R4.))P,(12.(13.(25.&40.R5.)(1:.+2.+17.))(26.VhAR,))P,(1=.$1>.(1?.(20.(1;.(=.&40.)(=.&40.))(21.(22.R7.))(23.(22.R7.)))R6.(7.&40.(1:.+2.+17.)))$24.)(0.A5.VK,R<.R;.R:.(20.$11.R9.(4.$11.(25.&40.R7.)(8.$11.)))(2=.+4022.R7.(1:.+2.+17.)R8.)(2>.A4.VCSf,R<.R;.R:.(20.$11.R9.(4.$11.(25.&40.R7.)(8.$11.)))(25.&40.R7.)(1:.+2.+17.)))")
(* [comment removed for export] *).
  Hypothesis ROOM_n : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Psc,(;.(1;.$11.$11.))Pr,$11.Pnb,(;.$11.)Pbl,(;.$11.)Pmo,$1<.P,A4.VGn,R5.R4.R3.R2.P,A5.VK,R6.R5.R4.R3.R2.(35.(=.&40.)La,(=.&40.)(36.VhAR,+22.(1:.+2.+14.)R4.R1.))")
(* [comment removed for export] *).
  Hypothesis ROOM_s : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Psc,(;.(1;.$11.$11.))Pr,$11.Pnb,(;.$11.)Pbl,(;.$11.)Pmo,$1<.P,A4.VGs,R5.R4.R3.R2.P,A5.VK,R6.R5.R4.R3.R2.(35.(=.&40.)La,(=.&40.)(36.VhAR,+4022.(1:.+2.+17.)R4.R1.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Variables (can : word) (dd madv : byte).
  Hypothesis PZ : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Psc,(;.(1;.$11.$11.))Pr,$11.Pnb,(;.$11.)Pbl,(;.$11.)PA,$11.Pw,$11.P,(1=.$11.(2;.R2.+8.)=)P,(1=.$11.(2;.R2.+8.)=)P,(12.+8.R3.)P,(12.R4.(1:.+2.+28.))P,(14.(0.(12.+8.R6.)(0.(12.R6.+7???7??8.)(12.(13.R6.R5.)+7???8000.)))(0.(12.+10007???8000.R6.)(0.(12.+10007???8008.(13.R6.R5.))(0.(12.R6.+7??????????8.)(12.(13.R6.R5.)+800000000000.)))))(37.VhAR,A4.VCSf,R;.R:.R9.R8.A4.VK,R;.R:.R9.R8.R7.R6.Vcan,Vdd,Vmadv,)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Hypothesis MOD_DIE : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "PCS,P,$11.SpPgp,(=.&40.)Ptp,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Ps0,(=.&40.)Ps1,(=.&40.)Ps2,(=.&40.)Ps3,(=.&40.)Ps4,(=.&40.)Ps5,(=.&40.)Ps6,(=.&40.)Ps7,(=.&40.)Ps8,(=.&40.)Ps9,(=.&40.)Ps10,(=.&40.)Ps11,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)Pa6,(=.&40.)Pra,(=.&40.)PSP0,$11.PF,(38.&5.(=.&40.))Pfc,(=.&20.)Pm0,P,(=.&40.)(>.(=.&8.))Pmm,P,(=.&40.)(>.(=.&8.))Paddr,$11.Psize,$11.Plo0,$11.Pfr,(;.(=.&8.))P,(39.VAL,R21.)P,(0.(12.=R5.)(28.R5.(1:.+2.+2?.)))P,(0.(28.=R5.)(12.R5.(1:.+2.+28.)))P,(3:.$2.R8.(13.R<.-60.)(4.$5.(:.(7.&40.+32.))(4.$5.(3;.#2<.R4.)(4.$5.(6.R1:.)(4.$5.(6.R1;.)(4.$5.(6.R1<.)(4.$5.(6.R1=.)(4.$5.(6.R1>.)(4.$5.(6.R=.)(8.$5.))))))))))P,(3<.R9.)P,(3=.$2.R:.R7.(13.R>.-60.))P,(12.+65?000.R8.)P,(12.R9.(3>.R10.$3?.))P,(12.R11.(1:.+2.+3?.))P,(10.(4.(1;.$11.$11.)(2<.$11.$11.R;.R12.)(8.(1;.$11.$11.)))R?.R>.)P,(40.$2.R10.R?.)P,(41.$2.R10.)P,(2>.R2=.R>.(3>.R15.R>.))(42.$2.VAL,R2>.(43.R14.$44.)(45.(7.&40.(3>.(1:.+2.+40.)+<.))R16.R2=.R2<.R2;.R2:.R29.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R15.R14.R11.R10.R12.))")
(* [comment removed for export] *).

  Ltac facts :=
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L12339200442.3 L13925108942.2 L13925138262.3 L17120848823.0 L18926759668.80L18928824262.78L18930958230.79L25047882783.4 L36644267936.2 L3822649421.3  L3822711765.2  L3823029717.2  L38599263692.2 L38599474124.2 L38599510100.3 L40040019413.3 L40040056397.2 L44282459030.3 L65117206605.2 L65117517269.3 L65117521485.2 L8646232868.3  00000:00A00B00C00O00[00g00o01501601701801?01@01A01B01I01S01Z01[01\01fS1n2ms3MSZS1n3N2BFSS2SP3STK3SPAS2SP3STK3SPAS2SP3STK3SPAS1n1H2H0S1n2NBFFFS1n3RNBFFFS1n3N2BS1n2ms3MSZS1n3RNBFFS1n2ms3MSZ". (* [comment removed for export] *)
  #[using="hAR SP T SB PA STK SPA NB FP"] Lemma sec_n : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "(0.(12.+?<01.Vn,)(0.(1=.$11.(46.Vn,)Vn,)(0.(1=.$11.(47.Vn,)+800.)(0.(1=.$11.(48.Vn,)(13.(49.Vn,)+1000.))(0.(0.(12.Vn,(49.Vn,))(12.(49.Vn,)(13.Vn,+7.)))(0.(1=.$11.(2;.(49.Vn,)+8.)=)(0.(0.(28.+10000.(48.Vn,))(12.(48.Vn,)(13.Vn,+1007.)))(0.(0.(12.(13.(48.Vn,)+1000.)Vms,)(28.Vms,(13.(48.Vn,)+2000.)))(0.(1=.$11.(2;.Vms,+1000.)=)(1=.$11.(2;.(48.Vn,)+8.)=))))))))))")
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

  (* [comment removed for export] *)
  Definition skeep (W : list (Z * Z)) (m m' : mem) (nb bl : list Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Px,(=.&40.)Zy,$11.(25.&40.R1.)P,(4:.O5.R1.)P,Pk,$11.P,(0.(12.=R1.)(28.R1.(4;.(4<.$11.O2.))))(2:.(0.(12.(4=.O2.R2.)R4.)(28.R4.(13.(4=.O2.R2.)(1:.+2.+14.)))))P,Pj,$11.P,(0.(12.=R1.)(28.R1.(4;.(4<.$11.O1.))))(2:.(0.(12.(4>.O1.R2.)R5.)(28.R5.(13.(4>.O1.R2.)(1:.+2.+17.)))))(1=.(>.(=.&8.))A1.O3.R5.A1.O4.R5.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section SecChunk.
    Variables (sc' : list (Z * Z)) (r' : Z) (a ncks : Z).
    Let CSc := CSf sc' r' nb0 bl0.
    Let AB := a + 4096.
    Let UB := AB + rz_size n.
    Let CHB := AB + rz_size n + -16.
    Let r8 := (nfix n + 7) / 8 * 8.
    Let rd := nfix n / 8 * 8.
    Let S1 := 0x7fff8000 + AB / 8.
    Let S2 := 0x7fff8000 + (UB + r8) / 8.
    Let k2 := (a + ms - (UB + r8)) / 8.
    Let SUB := 0x7fff8000 + UB / 8.
    Let PGS := 0x7fff8000 + Z.shiftr (UB + rd) 3.
    Let SHA := 0x7fff8000 + a / 8.                  (* [comment removed for export] *)
    Hypothesis A0 : 0x65f000 <= a. Hypothesis AAL : a mod 4096 = 0. Hypothesis ACE : a + ms <= ACEIL.
    Hypothesis ABAND : a + ms <= 0x7fff7000 \/ 0x10007fff8000 <= a.
    Hypothesis APT : a + ms <= SB \/ SB + 2^37 + 4096 <= a.
    Hypothesis ABT : a + ms <= T \/ T + 4096 <= a.
    Hypothesis ABC : a + ms <= CTX \/ CTX + 0x10000 <= a.
    Hypothesis ABP : a + ms <= PA \/ PA + 0x800000 <= a.
    Hypothesis HR' : 0 <= r'. Hypothesis NCK : 0 <= ncks /\ ncks + 1 <= 0x4000 * r'. Hypothesis R20 : 0x4000 * r' <= 2^20.
    Hypothesis BCS : crange CSc a ms.
    Hypothesis SCS : crange CSc lo (SP - lo).
    (* [comment removed for export] *)
    Hypothesis APTn : forall k, 0 <= k < Z.of_nat (length nb0) -> T + 4096 <= dblk nb0 k \/ dblk nb0 k + 2^20 <= T.
    Hypothesis APTs : forall j, 0 <= j < Z.of_nat (length bl0) -> T + 4096 <= sblk bl0 j \/ sblk bl0 j + 2^23 <= T.
    Hypothesis APCn : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Pk,$11.P,(0.(12.=R1.)(28.R1.(4;.(4<.$11.Vnb0,))))(14.(12.(13.VCTX,+10000.)(4=.Vnb0,R2.))(12.(13.(4=.Vnb0,R2.)(1:.+2.+14.))VCTX,))")
(* [comment removed for export] *).
    Hypothesis APCs : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Pj,$11.P,(0.(12.=R1.)(28.R1.(4;.(4<.$11.Vbl0,))))(14.(12.(13.VCTX,+10000.)(4>.Vbl0,R2.))(12.(13.(4>.Vbl0,R2.)(1:.+2.+17.))VCTX,))")
(* [comment removed for export] *).
    Hypothesis APPn : forall k, 0 <= k < Z.of_nat (length nb0) -> PA + 0x800000 <= dblk nb0 k \/ dblk nb0 k + 2^20 <= PA.
    Hypothesis APPs : forall j, 0 <= j < Z.of_nat (length bl0) -> PA + 0x800000 <= sblk bl0 j \/ sblk bl0 j + 2^23 <= PA.
    Hypothesis APBn : forall k, 0 <= k < Z.of_nat (length nb0) -> a + ms <= dblk nb0 k \/ dblk nb0 k + 2^20 <= a.
    Hypothesis APBs : forall j, 0 <= j < Z.of_nat (length bl0) -> a + ms <= sblk bl0 j \/ sblk bl0 j + 2^23 <= a.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L18190854626.110000011S3hAR2SP1n1T3STK3SPA2ms2GT1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA". (* [comment removed for export] *)
    #[using="hAR SP n SB PA STK SPA ms GT a AB UB CHB r8 rd S1 S2 k2 SUB PGS SHA"] Lemma T0 : Timg T. Proof. pose proof GT. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L61482307031.110000017S3hAR2SP1n1T2SB2PA3STK3SPA2ms2GT1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA". (* [comment removed for export] *)
    #[using="SP n SB PA STK SPA ms GT a AB UB CHB r8 rd S1 S2 k2 SUB PGS SHA"] Lemma T1 : T + 4096 <= ACEIL. Proof. pose proof GT. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    #[using="hAR GT"] Lemma TAL : T mod 4096 = 0. Proof. dpose GT as (_ & _ & X). exact X. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L23536159298.110000015S3hAR2SP1n3CTX3STK3SPA2ms4GCTX1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA". (* [comment removed for export] *)
    #[using="hAR SP n T SB PA STK SPA ms GCTX a AB UB CHB r8 rd S1 S2 k2 SUB PGS SHA"] Lemma CX0 : 0x65f000 <= CTX. Proof. pose proof GCTX. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L45743032595.11000001=S3hAR2SP1n1T3CTX2SB2PA3STK3SPA2ms4GCTX1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA". (* [comment removed for export] *)
    #[using="SP n T SB PA STK SPA ms GCTX a AB UB CHB r8 rd S1 S2 k2 SUB PGS SHA"] Lemma CX1 : CTX + 0x10000 <= ACEIL. Proof. pose proof GCTX. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L58632167809.11000001=S3hAR2SP1n1T3CTX2SB2PA3STK3SPA2ms4GSEP1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA". (* [comment removed for export] *)
    #[using="hAR SP n SB PA STK SPA ms GSEP a AB UB CHB r8 rd S1 S2 k2 SUB PGS SHA"] Lemma TC : T + 4096 <= CTX \/ CTX + 0x10000 <= T. Proof. pose proof GSEP. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L1048143380.110000013S3hAR2SP1n2SB3STK3SPA2ms3GSB1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA". (* [comment removed for export] *)
    #[using="hAR SP n T PA STK SPA ms GSB a AB UB CHB r8 rd S1 S2 k2 SUB PGS SHA"] Lemma SB0 : 0 <= SB. Proof. pose proof GSB. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L43455192258.110000018S3hAR2SP1n1T2SB2PA3STK3SPA2ms3GSB1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA". (* [comment removed for export] *)
    #[using="SP n T PA STK SPA ms GSB a AB UB CHB r8 rd S1 S2 k2 SUB PGS SHA"] Lemma SB1 : SB + 2^37 + 4096 <= ACEIL. Proof. pose proof GSB. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L27614488698.4000009S2SP4TOP2". (* [comment removed for export] *)
    #[using="TOP2"] Lemma SPH : SP + 16 <= 2^47. Proof. clear - TOP1 TOP2. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L10417939618.110000011S3hAR2SP1n1T3STK3SPA2ms2GT1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA". (* [comment removed for export] *)
    #[using="hAR SP n SB PA STK SPA ms GT a AB UB CHB r8 rd S1 S2 k2 SUB PGS SHA"] Lemma TNS : T + 4096 <= 0x7fff8000 \/ 0x10007fff8000 <= T. Proof. pose proof GT. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L31696321418.110000015S3hAR2SP1n3CTX3STK3SPA2ms4GCTX1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA". (* [comment removed for export] *)
    #[using="hAR SP n T SB PA STK SPA ms GCTX a AB UB CHB r8 rd S1 S2 k2 SUB PGS SHA"] Lemma CTXNS : CTX + 0x10000 <= 0x7fff8000 \/ 0x10007fff8000 <= CTX. Proof. pose proof GCTX. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010@L67267956776.110000013S3hAR2SP1n2PA3STK3SPA2ms3GPA1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA". (* [comment removed for export] *)
    #[using="hAR SP n T SB STK SPA ms GPA a AB UB CHB r8 rd S1 S2 k2 SUB PGS SHA"] Lemma PA0 : (0x65f000 <= PA /\ Pband PA 0x800000). Proof. pose proof GPA. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L4333396420.110000018S3hAR2SP1n1T2SB2PA3STK3SPA2ms3GPA1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA". (* [comment removed for export] *)
    #[using="SP n T SB STK SPA ms GPA a AB UB CHB r8 rd S1 S2 k2 SUB PGS SHA"] Lemma PA1 : PA + 0x800000 <= ACEIL. Proof. pose proof GPA. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    #[using="CST"] Lemma TCSc : crange CSc T 4096. Proof. apply CST. Qed.
    #[using="CSCTX"] Lemma CTXCSc : crange CSc CTX 0x10000. Proof. apply CSCTX. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L2934569678.2000008S2r'3R20". (* [comment removed for export] *)
    #[using="CSPA HR' R20"] Lemma PACSc : crange CSc PA (0x20000 * r'). Proof. apply CSPA; [exact HR'| clear - R20; lia]. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Definition swin : list (Z * Z) := [(T + 2800, T + 2824); (T + 2904, T + 2912); (a, a + ms); (SHA, SHA + ms / 8)].

    Definition sec_chunk_post (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (N tf : Z) (m0 : mem) : config -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Lcf,$4?.(35.$50.Lms',$50.(35.$1<.Lmo',$1<.(35.(;.$11.)Lnb',(;.$11.)(35.(;.$11.)Lbl',(;.$11.)(35.$11.LN',$11.(35.$11.Ltf',$11.(35.$11.Lid,$11.(35.(=.&40.)Lt0,(=.&40.)(35.(=.&40.)Lt1,(=.&40.)(35.(=.&40.)Lt2,(=.&40.)(35.(=.&40.)La1,(=.&40.)(35.(=.&40.)La2,(=.&40.)(35.(=.&40.)La3,(=.&40.)(35.(=.&40.)La4,(=.&40.)(35.(=.&40.)La5,(=.&40.)(35.(=.&40.)La6,(=.&40.)(35.(=.&40.)La7,(=.&40.)(35.(=.&40.)Lt3,(=.&40.)(35.(=.&40.)Lt4,(=.&40.)(35.(=.&40.)Lt5,(=.&40.)(35.(=.&40.)Lt6,(=.&40.)(35.$11.Lb1',$11.(35.(=.&8.)Lpgb,(=.&8.)(35.(=.&40.)Lj0,(=.&40.)(35.(=.&40.)Lj1,(=.&40.)(35.(=.&40.)Lj2,(=.&40.)(35.(=.&40.)Lj4,(=.&40.)(35.P,(=.&40.)(>.(=.&8.))Lm',P,(=.&40.)(>.(=.&8.))(0.(1=.$4?.R1=.(51.R1<.R1;.))(0.(1=.$50.R1<.(52.(53.O13.(7.&40.VSP,)O12.(7.&40.$54.)R15.R14.R13.O11.O10.(7.&40.VUB,)R12.R11.R10.R?.R>.R=.R<.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R;.R:.R9.R8.)O5.(55.O13.)O4.(56.(=.&40.))R1.(57.$2.)))(0.A5.VK,Vsc',Vr',R1:.R19.R1;.(0.(58.R1.R1;.)(0.(59.VhAR,R1.R18.R1:.R17.R19.)(0.(5:.A4.VCSf,Vsc',Vr',R1:.R19.R1:.R19.)(0.(5;.R1.)(0.(0.(12.+1.R16.)(12.R16.R18.))(0.(0.(12.O3.R18.)(12.R18.(13.O3.+1.)))(0.(0.(12.O2.R17.)(12.R17.(13.O2.(5<.+2.(13.Vd,+3.)))))(0.(12.(3>.R17.(5<.+1?.(5=.R17.(1:.+2.+14.))))(13.(3>.O2.(5<.+1?.(5=.O2.(1:.+2.+14.))))(13.Vd,+3.)))(0.Px,$11.P,A1.VCSc,R1.A5.VCSf,Vsc',Vr',R1<.R1;.R2.(0.(35.(;.$11.)Lsn,(;.$11.)(35.(;.$11.)Lsb,(;.$11.)(0.(1=.(;.$11.)R1<.(20.$11.Vnb0,R2.))(0.(1=.(;.$11.)R1;.(20.$11.Vbl0,R1.))(0.(5>.$11.Lb,$11.Px,$11.P,A1.VCSc,R1.(2:.(0.(12.R3.R2.)(28.R2.(13.R3.(1:.+2.+14.)))))R2.)(5>.$11.Lb,$11.Px,$11.P,A1.VCSc,R1.(2:.(0.(12.R3.R2.)(28.R2.(13.R3.(1:.+2.+17.)))))R1.))))))(0.(5?.(4.(1;.$11.$11.)(2<.$11.$11.Vlo,VSP,)(4.(1;.$11.$11.)(2<.$11.$11.$15.$16.)$60.))O1.R1.R1:.R19.)(0.(40.$2.O1.R1.)(0.(41.$2.R1.)(0.(3=.$2.R1.Vlo,VSP,)(0.(3:.$2.R1.Va,(4.$5.(6.(7.&40.Va,))(4.$5.(6.(7.&40.Vms,))(4.$5.(6.(7.&40.(48.Vn,)))(4.$5.(6.(7.&40.Vncks,))(8.$5.))))))(0.(3:.$2.R1.(13.Va,+20.)(4.$5.(3;.(61.+?>0.)(62.(=.&8.)(7.&8.=)(61.+?>0.)))(8.$5.)))(0.(3:.$2.R1.VAB,(4.$5.(6.(7.&40.$63.))(4.$5.(6.(7.&40.VCHB,))(8.$5.))))(0.(3:.$2.R1.(13.VAB,+10.)(4.$5.(3;.(61.+7>0.)(62.(=.&8.)(7.&8.=)(61.+7>0.)))(8.$5.)))(0.(3:.$2.R1.VCHB,(4.$5.(64.(7.&8.$65.))(4.$5.(64.(7.&8.R7.))(4.$5.(66.(7.&40.=))(4.$5.(:.(7.&40.(46.Vn,)))(4.$5.(6.(7.&40.(67.(5<.VTID,(1:.+2.+20.))R16.)))(8.$5.)))))))(0.(1=.$11.(68.R7.+3.)+1.)(0.(0.(12.=R7.)(28.R7.+100.))(0.(3:.$2.R1.VUB,(4.$5.(3;.#1000.(62.(=.&8.)(7.&8.+;>.)#1000.))(8.$5.)))(0.(3:.$2.R1.(13.VUB,+1000.)(4.$5.(3;.(61.(3>.(3>.(13.Va,Vms,)VUB,)+1000.))(62.(=.&8.)(7.&8.=)(61.(3>.(3>.(13.Va,Vms,)VUB,)+1000.))))(8.$5.)))(0.(3:.$2.R1.VSHA,(4.$5.(3;.#200.(62.(=.&8.)(7.&8.+?:.)#200.))(8.$5.)))(0.(3:.$2.R1.VS1,(4.$5.(3;.#100.(62.(=.&8.)(7.&8.+?:.)#100.))(8.$5.)))(0.(3:.$2.R1.VSUB,(4.$5.(3;.(61.(5=.Vrd,+8.))(62.(=.&8.)(7.&8.=)(61.(5=.Vrd,+8.))))(8.$5.)))(0.(3:.$2.R1.VPGS,(4.$5.(64.(69.Vn,R6.))(8.$5.)))(0.(3:.$2.R1.VS2,(4.$5.(3;.(61.Vk2,)(62.(=.&8.)(7.&8.+?:.)(61.Vk2,)))(8.$5.)))(0.(3:.$2.R1.(13.VT,+:?0.)(4.$5.(6.R5.)(4.$5.(6.R4.)(4.$5.(6.R3.)(8.$5.)))))(0.(3:.$2.R1.(13.VT,+;58.)(4.$5.(6.R2.)(8.$5.)))(3:.$2.R1.(13.VT,+<60.)(4.$5.(64.(7.&8.=))(8.$5.))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

    (* [comment removed for export] *)
    Ltac glia GEO := clear - GEO; decompose [and] GEO; lia.
    Ltac geo GEO := cbn [disjoint_from cells_size csize Nat.add length repeat]; rewrite ?repeat_length, ?Nat.add_0_r, ?Z2Nat.id by (clear - GEO; lia);
                    clear - GEO; decompose [and] GEO; repeat split; lia.
    Ltac geoh GEO H := cbn [disjoint_from cells_size csize Nat.add length repeat]; rewrite ?repeat_length, ?Nat.add_0_r, ?Z2Nat.id by (clear - GEO; lia);
                       clear - GEO H; decompose [and] GEO; repeat split; lia.
    Ltac carve GEO H o k name :=
      pose proof (CB_sub asegs _ _ _ _ (Z.to_nat o) (Z.to_nat k) H ltac:(clear - GEO; decompose [and] GEO; lia)) as name;
      rewrite firstn_skipn_repeat in name by (clear - GEO; decompose [and] GEO; lia).
    Ltac t2r GEO H MU WM tac := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length repeat]; rewrite ?repeat_length, ?Nat.add_0_r, ?Z2Nat.id by (clear - GEO; decompose [and] GEO; lia); tac].
    Ltac t2o H MU tac := eapply ro_cells_transport; [exact H| exact MU| cbn [disjoint_from cells_size csize Nat.add]; tac].
    Ltac t3r GEO WD H MU WM3 tac := eapply rw_cells_transport; [exact H| exact MU| exact WM3| apply WD; cbn [cells_size csize Nat.add length repeat app]; rewrite ?app_length, ?firstn_length, ?repeat_length, ?Nat.add_0_r, ?Z2Nat.id by (clear - GEO; decompose [and] GEO; lia); tac].
    (* [comment removed for export] *)
    Ltac find_iv_syn W' pos :=
      lazymatch W' with
      | (?a, ?b) :: ?rest => first [ exists a, b; split; [pos; left; reflexivity | split; apply Z.le_refl ] | find_iv_syn rest ltac:(pos; right) ]
      end.
    Ltac find_iv_geo GEO W' pos :=
      lazymatch W' with
      | (?a, ?b) :: ?rest => first [ exists a, b; split; [pos; left; reflexivity | clear - GEO; decompose [and] GEO; split; lia ] | find_iv_geo GEO rest ltac:(pos; right) ]
      end.
    Ltac ssfp GEO :=
      repeat (apply sub_fp_cons; [ lazymatch goal with |- exists lo' hi', In _ ?W' /\ _ => first [ find_iv_syn W' ltac:(idtac) | find_iv_geo GEO W' ltac:(idtac) ] end | ]);
      apply sub_fp_nil.
    (* [comment removed for export] *)
    Ltac t7r GEO H MU WM tac := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [cells_size csize Nat.add length repeat app]; rewrite ?app_length, ?firstn_length, ?repeat_length, ?Nat.add_0_r, ?Z2Nat.id by (clear - GEO; decompose [and] GEO; lia); tac].

    Local Ltac2 Set LiaOrc.tbl := fun () => "0740@L10184718841.85 L10298644911.83 L10307921259.3  L10413613337.21 L10572040301.85 L10694834340.1  L10982243828.83 L10993891568.86 L11306689438.83 L11307782552.26 L11403396711.26 L11528154259.26 L11905690422.85 L1193272270.83  L12042096597.21 L12115745277.85 L12169910887.84 L1221228413.21  L12217668578.84 L1254471120.84  L12587122807.86 L13028071338.3  L13407719458.85 L13577584687.86 L13658889335.10 L13885063320.84 L13959828051.83 L14066150687.83 L1452918719.83  L1453274127.3   L14604722157.83 L14883279687.83 L14886875796.83 L15099037396.88 L15099037396.89 L15099037397.86 L1526528046.83  L15508334621.1  L15555752140.84 L15585608884.84 L15657401014.85 L15795332857.1  L16347037508.83 L16347106548.2  L163945825.84   L1660404049.83  L16861361330.2  L1688661793.83  L16924645992.1  L16941726106.2  L16953760212.0  L16970375870.83 L16992530622.1  L17120848823.0  L17148686322.83 L17633521235.26 L17649405483.83 L17662969074.83 L17702421713.366L17882144633.85 L18115724343.26 L18238326432.83 L1827379540.84  L18302958969.1  L18466561826.85 L18690384201.1  L18773136240.83 L18926556999.236L18926747693.83 L18928873411.235L19269748166.86 L19269748167.87 L19269748167.88 L19279432654.84 L19386104490.84 L19638779269.83 L20957647993.4  L21719268990.84 L22013886778.7  L22226130652.83 L22229464281.1  L22276674786.86 L22280994223.26 L22282469748.83 L22444975334.85 L2261230734.84  L22629594826.84 L22735146098.83 L22803166828.83 L2288623600.87  L22939191282.84 L22991915347.84 L23167523305.26 L23176591730.83 L23180147446.86 L23180147447.87 L23180147447.88 L23200658561.83 L23343287261.0  L23354854525.85 L23363504942.83 L23430790493.85 L23443613399.83 L23531835385.21 L23827727029.84 L23873772939.84 L23880668745.84 L23898603878.1  L24043785259.83 L24047826958.26 L24168428589.83 L2425102556.86  L24287809665.83 L24314672818.84 L24531589564.84 L24556453016.86 L24556453017.87 L24759905365.86 L2480023215.83  L24806485434.83 L24873647310.21 L24888640626.2  L24897143244.3  L25298574752.83 L25364333118.83 L2545944915.83  L25553687308.83 L25846062621.85 L26244211777.85 L26369363479.87 L26416823808.83 L26420691671.83 L26441178914.26 L26844000389.83 L26983742937.2  L27154370199.85 L27289292333.83 L27370141188.84 L27466439871.3  L27505664444.84 L27567648717.83 L27599741435.21 L27846130387.83 L28066597474.86 L28066597475.88 L28136736109.85 L28193722699.86 L28270115350.3  L2848395327.83  L28526273389.83 L2861274105.84  L28762839709.0  L28978561730.86 L29073221787.84 L29391812856.83 L29448346498.84 L29636014457.83 L29718441094.4  L2978961816.0   L29836529785.1  L29965192371.2  L30024005229.83 L30024336861.3  L30516872349.83 L30666673809.83 L3075336702.1   L31062529309.1  L31290149678.83 L31839289523.83 L31921857250.86 L31921857251.87 L31921857251.88 L31949200002.1  L32427706102.26 L32529474131.83 L33110309043.86 L33248673536.83 L33514448760.26 L33587116426.83 L33676380567.84 L33869284286.83 L33896637847.85 L34110713077.83 L34224124639.86 L34241758421.83 L34303986740.85 L34326536500.83 L34844086423.2  L34851531799.85 L35101767271.4  L35243480674.86 L36157423784.83 L36176492089.2  L36415714444.3  L36644267936.2  L36649891918.83 L37041841917.83 L37062637461.4  L37118884190.26 L37217032958.83 L37333187785.26 L37348504046.83 L37396631557.0  L37544098866.84 L37637199976.0  L3813344308.4   L3822612836.84  L38233345303.87 L38235734261.1  L38238299063.83 L38358425611.83 L38442651814.3  L38469668451.83 L38668991172.84 L38970087795.83 L39188636933.0  L39280637297.0  L39315242130.2  L39332637397.0  L3935718557.85  L39651577319.6  L39737653201.83 L39783232364.83 L39800583565.83 L39831478948.2  L39867723056.83 L39953279860.6  L39980912252.86 L40507775107.3  L41015227880.21 L41579612488.83 L4178491341.83  L41785025371.86 L4182214722.84  L41849201057.83 L41858100606.26 L42150983620.83 L42409219784.3  L42775592028.83 L4311322128.83  L43136556849.26 L43238030251.83 L4329333887.21  L43609532904.1  L43655392405.83 L43755370622.2  L43839967885.83 L43840858252.1  L43959989682.84 L44068555912.83 L44070693495.85 L44070693495.86 L44332321032.84 L44423098732.83 L44583925357.83 L4469623930.84  L44876607696.3  L45297748961.83 L4536638332.88  L4536638333.86  L45427434439.1  L4563733985.85  L45738445992.21 L45775022718.85 L45961998430.85 L46071731361.10 L46117173312.83 L46131445883.84 L46901796045.83 L46902177661.2  L47373976502.83 L47386102014.2  L47864761433.83 L48017183757.1  L48034105986.83 L48043344545.26 L48338973981.85 L48361909967.86 L48412007635.4  L48501686523.83 L48694315878.83 L48694315878.84 L48793009578.2  L49261876754.83 L49428354354.85 L49462460252.26 L49535152962.86 L49535152963.88 L49564803805.83 L49601850885.84 L49673326781.83 L4976423657.83  L49775846755.83 L50316490490.84 L50592940525.83 L51024965284.14 L51168183650.86 L51168183651.88 L51245445121.1  L51566604205.21 L5159101959.84  L51634096446.83 L51723252852.1  L52016866011.85 L5212822301.85  L52284456883.83 L52556427627.85 L52635831073.0  L52694201704.1  L5293223801.21  L52937408104.83 L52990098443.83 L53117978288.84 L53162776015.86 L53285514915.83 L53373227954.83 L53692901581.83 L54252428965.83 L54284146963.83 L5433293273.1   L54502827919.83 L54508837114.2  L54521824380.84 L54570205598.21 L54820495138.85 L55005463671.26 L55269111851.21 L55294381057.86 L55375478753.84 L55588686165.0  L55803458635.86 L55899845783.3  L55958643778.83 L56067688020.83 L56265836340.21 L56393063292.83 L5643552416.83  L56644254481.26 L56735799059.83 L56735799059.84 L56953409736.83 L57031203962.26 L57284553884.86 L57299896250.5  L57401826119.1  L57545127939.10 L58023448229.83 L58031689955.1  L58165227918.84 L58180285192.84 L58194748696.86 L58204059905.84 L58325186954.83 L58345982561.84 L58790820722.2  L58831778826.21 L58913627406.0  L5916318900.0   L59238542828.84 L59291886223.83 L59308518135.4  L59310676816.84 L59314955108.4  L59781483210.83 L59868852119.84 L59963999381.83 L59964192043.2  L60039020898.1  L60040003861.86 L60048435695.83 L60176313192.86 L60217558728.85 L60779458884.0  L60792795122.83 L61027106802.2  L61028641824.2  L61028696700.239L61028710730.241L61028857686.242L61028858315.237L61030876663.83 L61477106382.2  L61486893164.21 L61721776355.1  L61900453511.85 L61953443155.83 L62001483503.86 L62012458667.84 L62183600671.26 L6284022664.83  L63057960289.84 L63139026716.85 L63330810425.7  L63331304866.85 L63368119078.238L63368132624.240L63378225881.83 L63397897997.83 L63480898814.21 L63574020675.84 L63644289245.83 L63819428808.83 L63867716001.0  L64099937830.83 L64183633788.86 L64194056499.83 L64342109424.87 L64452882043.86 L64567772711.85 L64838801051.1  L65002897634.84 L65139927140.86 L65384309954.26 L65601965761.84 L65808597483.84 L65831515062.84 L66122999181.84 L66249744396.4  L66271728014.83 L66278123796.86 L66278123797.87 L66278123797.88 L664362142.0    L6647658600.86  L66567258875.6  L66569225939.84 L66787624418.84 L67484541908.88 L67484541908.89 L67484541909.86 L68225406712.86 L6928348742.83  L7322906252.83  L7468672731.1   L7799702881.1   L7888184628.84  L7889348142.83  L7993956635.86  L8265267294.0   L8594103216.83  L8634160166.84  L8642681606.86  L8843341236.84  L8924118175.83  L8946030930.83  L906692931.83   L9150748385.84  L9320764157.85  L9490636560.85  L9517334448.83  L9648528327.3   L9787421118.83  00001902902C02T05505806@08M09P0:00:F0:h0<Q0=Q0=b0@C0AS0AW0CJ0D\0Ee0F00H90JR0Jh0L30M[0NS0OV0OW0PW0R@0S80TD0Vo0X_0ZD0ZI0\T0]]0_F0_I0`E0`F0an0cJ0cS0dS0dV0d\0d]0eU0eY0eZ0fR0g00hX0iP0jW0k`0l<0m80oD0oG11O11S12e13]14U15M17L18V1:M1<I1>:1?@1?P1@Z1@i1Be1Bh1Dd1E@1Fb1H01I;1K91L91M91ND1P81Qb1R>1S61U91V@1W^1Xi1Xj1[I1\E1^K1_C1_P1aO1c71d:1d=1eB1ea1fY1i21j=1l<1n;1oD21<22o24625@25D25E25F26F27>28f29^2<22>[2@i2B92CE2C[2E;2EA2G`2HX2JA2JK2LF2ME2MN2NQ2OZ2RR2U32Vb2Vk2XV2YN2Z\2Z]2[i2\n2^c2`P2aL2aU2aV2aY2a`2bX2bd2dH2f>2fA2fF2gE2hH2ic2k42lo2m32mI2o131>32:32O34H36937139U3:Q3<D3=M3?V3A53A<3C[3Cg3E03FI3FQ3F[3Fa3GY3Hc3Hl3IK3JU3Ji3L13L23M<3M=3M@3NO3P]3Pa3Q`3S03S;3T;3UH3VD3VE3VF3VL3VM3Xa3Y93Z;3[>3\:3\D3]G3]^3_g3`43`B3a>3b>3dH3f<3g;3gK3hN3hU3ib3jo3k>3l@3lL3lO3mR3mY3nX3n\40[42G44245`47U48Q49I4;Q4;[4<W4?54A14A44C34C@4DG4F84FF4GM4I84J04J84K?4KH4LP4LT4Mb4N64PL4RU4R`4S\4Tf4V04V74W34Y14YO4ZY4]Q4_J4`l4bT4cP4dW4ee4f]4g;4hA4k54k84kG4lG4n04n54o@51a52j55?55@55C55T57E58m5:75<C5=l5?35?o5A65B25B55Bm5C45DK5DZ5F_5GK5GX5Hd5JM5JN5L=5LD5MG5No5O<5PZ5QY5Qn5SJ5U55V15VM5XZ5Xe5Xh5Y>5Zk5Zo5\65]o5`55a^5cZ5e?5eF5eN5eO5eP5g@5hh5i55jD5jP5kg5m\5nX5nY5n\60^61o63^65I65J66B66C66D67<68468l69d6:\6:c6:m6;16=G6>o6A<6Bm6CB6Dj6FS6H>6HM6JO6KG6L?6Mj6OH6OY6Qc6S06TI6TJ6UJ6WV6XR6Y]6[c6^D6^J6`:6aI6ae6bn6d@6ei6gT6g]6iH6kG6l_6nn6no70^71372d74W75c78N7:>7<H7=K7>J7>M7>R7?[7@[7Aj7Ak7CN7De7Fg7H07I07Ih7Jd7LM7Nl7P97Q67Q@7R`S3hAR2SP1n2lo1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H40S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H21S3bl01j2HjS3hAR1T2PA2T03PA0S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qx2qm2q83TNS2qa2qd2qr3GEO2H22H73H143H183H202H03H213H243H283H293H323H333H35S1nS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qa2H42H0S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3nb'1k2Y22H22H73H143H273H283H323H333H35S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H38S1n2ms2r82rd2qx3NFX3N2E2qr2DR2DXS1n2ms2r82rd3RNB2qr2DRS1n2ms2r82rd2qx3N2E2qm2DM2qr2DR2DXS3hAR2SP1n1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qm2q82qa2H22H73H143H273H283H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H30S3hAR1T2PA2T03PA0S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qx2qm2q83TNS2qa2qd2qr3GEO2H22H73H143H183H202H03H213H243H283H293H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2qa2H72H03H243H28S2SPS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qm2q82qa2qd2H12H73H143H183H202H03H283H293H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2q82qd3H143H203H303H32S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA1A1k1H3H24S2PA2r'3PA0S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1x2O52H22H73H143H273H283H323H333H35S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3nb'1k2Y32H22H63H113H143H163H123H203H173H283H313H32S3bl'1j1A1w2H12H22n11lS3hAR2SP1n2lo3CTX3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H44S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qa2qm2q82qr2H22H62H73H113H143H123H283H32S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H38FS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H30S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qa2q82qd2qr2H22H63H143H123H153H283H313H32S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT1A1k2Ha2HbS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qx2qm2q83TNS2qa2qd2qr3GEO1A1k2Ha2Hb2H22H73H143H183H202H03H213H243H283H323H333H353H30S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1A1k1H3H44S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qr2H22H63H113H143H123H283H32S3CTXS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qx2qm2q82qa2qd2qr2H12H32H63H102H73H133H143H163H183H202H03H283H323H333H35S3hAR2SP1n2lo1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H40S3hAR2SP1n1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qm2q82qa2H22H73H143H273H283H323H333H35S1TS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H39FS3hAR2SP1n1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qm2q82qa2H12H22H73H143H283H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2qa2qr2H42H62H73H112H03H24S3CTX3CX0S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H27S1TS1T2T0SS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS2qaSS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS1n2ms2r82rd2q82D82M82qd2DN2MNS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qr2H22H62H73H113H143H123H283H32S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA1A2sz2A'1k1H2H0S3hAR2SP1n2lo1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H40S1n2ms2r82rd2qx3N2E2qr2DR2DXS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qx2qm2q82qa2qd2qr2H32H63H102H73H133H143H163H183H202H03H273H283H323H333H35S1TS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1x2O52H12H22H73H143H283H323H333H35S2qaS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2q82qd3H143H203H303H32S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qa2qd1A1k1H2H13H223H293H312lo2qm2q82H83H153H213H253H343H363H243H39S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qd1A1k2Hb3H30S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2q82qa2qd1A1k2Ha2Hb2H33H143H163H202H03H213H283H303H32S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H12H22H73H143H183H203H173H243H283H313H333H353H23S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H73H143H202H03H243H283H303H333H353H23S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qd2H23H153H17S2SP2lo3SPA4SPALS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qa2H03H213H28S3bl'1j1A2n02n2S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H22H73H143H153H243H273H283H313H323H333H353H232H1S1TS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA1A1k1H3H223H282lo2qm2q82qa2H32H83H153H253H293H333H343H363H243H39S1n2ms2r82rd2qx3N2E2qr2DR2DXS3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2H72H03H243H283H323H333H23S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qd2H23H173H293H31S3hAR2SP1n2lo3CTX3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H44S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qm2q82qa2qd2H12H32H73H143H163H183H202H03H283H303H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H29S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H35S3hAR3nb02SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA1k1X3H23S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qm2q82qa2qd2H73H143H183H202H03H273H283H293H333H35S3hAR2SP1n3CTX3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABC2qm2q82qa2H12H22H73H143H283H323H333H35S1n2ms2r82rd2qx3N2E2qr2DR2DXS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qa1A1k1H2H13H223H293H302lo2qm2q82qd2H83H153H193H213H253H343H363H243H39S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA1A1k2Hb3H29S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qa1A1k2Ha2Hb2H03H213H283H29S3hAR2SP1n2lo3CTX3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H44SS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qx2qm2q83TNS2qa2qd2qr3GEO2H22H73H143H183H202H03H213H243H283H293H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1x2O62H23H143H283H293H323H333H35S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR3CTX3CX0S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qm2q82qa2qd2H32H73H143H163H183H202H03H273H283H303H323H333H35S3hAR2SP1n1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qm2q82qa2H12H22H73H143H283H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2H13H27S1TS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qa2H12H0S1n2ms2r82rd3RNB2qd2DN2MN2qr2DRS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3bl'1j2Y32H22H63H113H143H163H123H203H173H283H313H32S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H383H39S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qm2q82qa2qd2H32H73H143H163H183H202H03H273H283H313H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qm2q82qa2qd2H32H73H143H163H183H202H03H273H283H303H323H333H35S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA1A1k1H3H24S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA1A1k2Hb3H243H232qm2q82qa2qd2H73H143H183H202H03H283H333H35S3hAR3bl02SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO2jj1Y3H51S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H38S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qa2H03H213H28S2SPSSS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H27S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qa2qm2q82qr2H22H62H73H113H143H123H283H32S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qx2qm2q83TNS2qa2qd2qr3GEO2H73H143H202H03H213H243H283H303H333H35S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qx2qm2q83TNS2qa2qd2qr3GEO2H22H73H143H163H183H203H172H03H213H243H283H313H323H333H35S3hAR3bl02SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1j3APA2H22H73H143H273H283H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2qa2H72H03H243H28S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2qa2H72H03H24S1n2ms2r82rd2q82qr3R8RS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2q82qa2qd2H23H143H163H173H283H313H32S1a2A0S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qx2qm2q83TNS2qa2qd2qr3GEO2H63H102H73H133H143H183H202H03H213H243H283H323H33S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qm2q82qa2H22H73H143H273H283H323H333H35S3nb01k2HkS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qm2q82qa2qd2H32H73H143H163H183H202H03H283H303H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2H1S2SP4TOP2S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H36S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA1A1k1H2H23H22S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1A1k2Hc2H13H275ABAND2Ha2Hb2H73H143H183H202H03H283H333H352H32H63H103H133H163H303H32S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qx2qm2q83TNS2qa2qd2qr3GEO2H22H73H143H183H202H03H213H243H283H293H323H333H35S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3bl'1j2Y1S1a2qm2q8S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qr2H12H22H62H73H113H143H123H283H32S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2q82H23H143H303H32SS3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3bl'1j2Y53H23S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2q82qd2GE3H19S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H73H143H183H202H03H243H283H293H333H353H23S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qa2q82qd2qr2H22H63H143H163H123H203H173H283H32S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H36S2SP1q2HqSS1TS2qa2qdS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS2SP3STK3SPAS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qa2q82qd2H23H143H163H153H173H283H313H32S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qa2qm2q82qd2qr2H12H22H62H73H113H143H123H153H283H313H32S1aS3CTXS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2H1S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H38S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qa2qd1A1k1H3H192H13H223H293H32S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qd1A1k2Hb2H23H173H31S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2q82qa2qd1A1k2Ha2Hb2H33H143H163H183H202H03H213H283H313H32S2r'S1n2ms2r82rd3RNB2qr2DRS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qa2qm2q82qr2H22H62H73H113H143H123H283H32S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3bl'1j2Y22H22H73H143H273H283H323H333H35S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H39S1n2ms2r82rd2q82D82M8S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H22H73H143H153H243H273H283H313H323H333H353H23S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H73H143H183H202H03H243H283H333H353H23S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qx2qm2q83TNS2qa2qd2qr3GEO2H22H63H102H73H133H143H183H202H03H213H243H283H323H33S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H39S3hAR3nb02SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO2k01Y3H51S3hAR2SP1n2lo1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H40S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1x2O52H22H73H143H273H283H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2H22H73H143H283H323H333H35S2qa2q8S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qx2qm2q83TNS2qa2qd2qr3GEO2H63H102H73H133H143H183H202H03H213H243H283H323H33S1n2NB2D82M8S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA1A1k1H3H24S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qd3H143H203H303H333H35S2PA3PA0S3bl'1j2HjS1n2NBS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n2PA3STK3SPA2ms2r'1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H453H51S2SP1q2HqS1n2ms2r82rd2qx2RZ3N2E2qr2DR2DXS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qa2H03H213H28S1n2ms2r82rd2qd4RDE'S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2H42H7SS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qa2H03H273H28SS1qS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2q82qd2EQ1H3H143H15S3hAR3nb02SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1k3APA2H22H73H143H273H283H323H333H35S2loS3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qa2q82H93H283H32S2r'3HR'2R0S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H29S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2q82qd2LT3H313H32S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHASSS1T2T0SS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qx2qm2q83TNS2qa2qd2qr3GEO2H73H143H202H03H213H243H283H303H333H35S1d2tf4size3SZD3tf'4TFB'S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2H7S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H38S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS4size3SZBS3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H37S1d2tf4size3SZD3tf'3TFPS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3bl'1j2Y22H22H73H143H283H323H333H35S3hAR3CTX3CX1S3hAR2lo5LOIMGS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H27S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3nb'1k2Y32H23H143H283H293H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qm2q82qa2qd2H73H143H183H202H03H273H283H293H333H35S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qd3H18S1n2ms2r82rd3NLOS3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H23S1A1k1HS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82H93H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82H93H333H35S1n2ms2NB2r82rdS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qa2H0S3hAR2PA3PA1S1TS3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H37S2qa2q8S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2H1S2qaS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qm2q82qa2qd2H32H73H143H163H183H202H03H273H283H303H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qr2H22H62H73H113H143H123H273H283H32S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1x2O1S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1x2O12XRS3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H22H73H143H183H203H243H283H323H333H353H23S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qx2qm2q82qa2qd2qr2H32H63H102H73H133H143H163H183H202H03H283H323H333H35S3nb'1k2HkS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1A1k2Hc2H13H275ABAND2Ha2Hb2H73H143H183H202H03H283H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA1A1k1H3H223H282lo2qm2q82qa2H32H83H153H253H293H333H343H363H243H39S1aS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qm2q82qa2qd2H32H73H143H163H183H202H03H273H283H313H323H333H35S3hAR3CTX3CX1S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qd3H303H31S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H73H143H202H03H243H283H313H333H353H23S1A1w2H12H22HwS3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H38S3hAR2SP1n3CTX3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABC2qm2q82qa2H22H73H143H273H283H323H333H35S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS2SP3SPAS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qd3H293H30S3CTX3CX0S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2q82qr2H63H12S2qaS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qd2H23H173H293H31S1n2ms2r82rd2q84R8E'S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qx2qm2q83TNS2qa2qd2qr3GEO2H73H143H202H03H213H243H283H303H333H35S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3nb'1k2Y22H22H73H143H283H323H333H35S1n2ms1a2A0S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q83H323H33S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q83H323H33S3bl'1jS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H36S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1x2O62H23H143H283H323H33S1n2ms2r82rd2q82D82M82qd2DN2MNS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA1A1k1H3H223H28S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1A1k2Hc2H13H275ABAND2Ha2Hb2H73H143H183H202H03H283H333H352H32H63H103H133H163H303H32S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H22H73H143H153H243H273H283H313H323H333H353H23S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2H72H03H243H283H323H333H23S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qd2qr2H12H62H73H113H143H123H153H20S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H38S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2q82H23H143H303H32S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS1n2ms3N2E3MSZ2qm2DM2q82DR3R8RS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA1A1k1H3H22S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1A1k2Hc2H15ABAND2Ha2Hb2H73H143H183H202H03H283H333H352H32H63H103H133H163H303H32S1TS3hAR2SP2lo3SPLS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H27S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qr2H22H63H113H143H123H283H293H32S3CTXS3hAR2SP1n2lo3CTX3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H44S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABC2qx2qm2q85CTXNS2qa2qd2qr3GEO2H63H102H73H133H143H183H202H03H213H243H283H323H33S3hAR2SP1n2lo1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H40S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1x2O62H22H63H113H143H163H123H203H173H283H313H32SS1TS3hAR1T2PA2T03PA0S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2H12H22H73H143H243H283H323H333H353H233H38S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qr2H22H62H73H113H143H123H283H32S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q83H323H33S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3nb'1k2Y22H12H22H73H143H283H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2H12H22H73H142H03H243H283H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qd3H303H31S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H243H23S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H39S1TS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3nb'1kS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2q82qa2qd2EQ2H93H283H313H32S3hAR2SP2lo3SPLS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1x2O52H22H73H143H283H323H333H35S1n2ms2r82rd3NLO3RNB2q82D82M82qd2DN2MN2qr2DRS2r'4ncks3NCKS3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3nb'1k2Y53H23S3hAR2SP1n1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qm2q82qa2H22H73H143H273H283H323H333H35SS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3bl'1j2Y1S1A1k1HS3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H36S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qr2H22H62H73H113H143H123H283H32S2r'4ncks3NCKS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qr2H63H112H93H123H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2H1S1n2ms2r82rd2q82D82M8S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2H23H143H283H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H23H143H203H173H283H313H323H333H35S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H39S1n2ms2r82rd2qx3MSZ2qm2DM2DXS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3bl'1j2Y22H22H73H143H273H283H323H333H35S1A1k2H12H2S1nS3nb'1k1A1w2H12H22n11lS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qa2q82qd2qr2H22H63H143H163H123H203H173H283H32S2qaS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qd3H293H30S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H22H73H143H183H203H243H273H283H323H333H353H23S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3bl'1j2Y32H63H113H143H123H203H30S3hAR2SP1n1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qm2q82qa2H22H73H143H273H283H323H333H35S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H12H22H73H143H153H243H273H283H313H323H333H353H23S3hAR2SP1n1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qm2q82qa2H22H73H143H283H323H333H35S2qa2qdS2r'3R20SSS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qm2q82qa2qd2H73H143H183H202H03H283H293H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qa2qm2q82qr2H22H62H73H113H143H123H283H32S2q82qd2GE2LTS3hAR2SP1n3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2R03H473H49S2q82qd2LT1ES3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2qa2H72H03H243H283H23S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H73H143H183H202H03H243H283H293H333H353H23S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H39FS1nS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3nb'1k2Y32H23H143H283H323H33S3hAR2SP1n2lo2PA3STK3SPA2ms2r'1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H453H51S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3nb'1k2Y1S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1x2O1SS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHASSS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS1n3NLOS3hAR1T2T1S2qaS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABC2qx2qm2q85CTXNS2qa2qd2qr3GEO2H73H143H202H03H213H243H283H303H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qa2qm2q82qr2H22H62H73H113H143H123H283H32S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3nb'1k2Y22H22H73H143H273H283H323H333H35S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H73H143H202H03H243H283H313H333H353H23S1n2ms2r82rd2qd2DN2MNS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qr2H22H62H73H113H143H123H283H32S3hAR2SP1n1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qm2q82qa2H22H73H143H273H283H323H333H35S3hAR2SP1n3CTX3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABC2qm2q82qa2H22H73H143H273H283H323H333H35S3nb'1k1A2n02n2S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1x2O62H63H113H143H123H203H30S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qr2H12H22H62H73H113H143H123H283H32S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qa2q82qr2H22H63H143H123H283H32S3hAR1T2PA2T03PA0S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qm2q82qa2qd2H12H22H73H143H153H183H203H172H03H213H243H283H313H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82H93H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qd3H143H203H313H333H35SS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H35S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3bl'1j2Y22H12H22H73H143H283H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS3hAR3bl02SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA1j1X3H23S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3nb'1k2Y32H63H113H143H123H203H30S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABC2qx2qm2q85CTXNS2qa2qd2qr3GEO2H22H73H143H183H202H03H213H243H283H293H323H333H35S4sizeS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qm2q82qa2qd2H73H143H183H202H03H283H293H333H35S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3bl'1j1H3H243H39S1n2ms2r82rd2qx3MSZ2qm2DM2DXS3hAR2SP1n2lo1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H40S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2q82qd3H143H203H313H32S3hAR2SP1n1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qm2q82qa2H22H73H143H273H283H323H333H35S3hAR2SP1n3CTX3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABC2qm2q82qa2H22H73H143H273H283H323H333H35S2SP1q2HqS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qr2H12H22H62H73H113H143H123H283H32S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2q82qa2qd1A1k1H3H153H193H212H13H223H293H332lo2qm2H83H253H343H243H39S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q81A1k2Hb2H23H143H323H33S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qx2qm2q82qa2qd2qr1A1k2Ha2Hb2H32H63H103H133H143H163H183H202H03H213H283H323H33SS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3nb'1k2Y1S1N3NB22N'2id3IDB3NB'S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qm2q82qa2qd2H73H143H202H03H243H283H303H333H353H23S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qm2q82qa2qd2H12H73H143H183H202H03H283H293H333H35S3hAR2SP1n1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT1A1k2Ha2HbS3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA5ABAND2qx2qm2q83TNS2qa2qd2qr3GEO1A1k2Ha2Hb2H22H73H143H183H202H03H213H243H283H323H333H353H30S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO1A1k1H3H44S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3bl'1j2Y32H23H143H283H293H323H333H35S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H34S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2H1S1aS3CTXS3hAR2SP1n2lo1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H40S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H27S3hAR2SP1n2lo3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3nb'1k1H3H243H39SS3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qa2q82qd2H22H93H143H203H173H283H313H32S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2q82qa2qd2EQ2H93H283H313H32S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2qx2qm2q82qa2qd2qr3GEO3bl'1j2Y32H23H143H283H323H33S3hAR2SP1n2lo1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H233H40S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H35S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHAS2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3H36S3hAR2SP1n1T3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qm2q82qa2H22H73H143H273H283H323H333H35S3hAR2SP1n2lo1T3CTX2PA3STK3SPA2ms2r'1a4ncks2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA3ABT2qx2qm2q83TNS2qa2qd2qr3GEO2H22H73H143H183H202H03H213H243H283H293H323H333H35S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2q82qd2LT3H313H32S2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA1H2H2S3hAR1T2T1S3hAR2SP1n3STK3SPA2ms1a2AB2UB3CHB2r82rd2S12S22k23SUB3PGS3SHA2q82qa2qd2H23H143H203H173H283H313H32". (* [comment removed for export] *)
    #[using="AL IMG ALWF ASB CSOKf KL CSf_noshadow CSmono_n CSmono_s NB FP LOIMG SPL SPA16 TOP2 TIDB GSB GT GCTX GPA GSEP CST CSCTX CSPA K_apart T_node T_store ROOM_n ROOM_s PZ A0 AAL ACE ABAND APT ABT ABC HR' NCK R20 BCS SCS APTn APTs APCn APCs APPn APPs APBn APBs"] Theorem msec_chunk : ltac2:(CDefT.buildp (gd_tbl_AW_MallocSecS ()) "Pra,(=.&40.)Pgp,(=.&40.)Pt0,(=.&40.)Pt1,(=.&40.)Pt2,(=.&40.)Ps0,(=.&40.)Ps1,(=.&40.)Pa1,(=.&40.)Pa2,(=.&40.)Pa3,(=.&40.)Pa4,(=.&40.)Pa5,(=.&40.)Pa6,(=.&40.)Pa7,(=.&40.)Ps2,(=.&40.)Ps3,(=.&40.)Ps4,(=.&40.)Ps5,(=.&40.)Ps6,(=.&40.)Ps7,(=.&40.)Ps8,(=.&40.)Ps9,(=.&40.)Ps10,(=.&40.)Ps11,(=.&40.)Pt3,(=.&40.)Pt4,(=.&40.)Pt5,(=.&40.)Pt6,(=.&40.)Pj0,(=.&40.)Pjj1,(=.&40.)Pjj2,(=.&40.)Pj4,(=.&40.)Ppgb,(=.&8.)PF,(38.&5.(=.&40.))Pfc,(=.&20.)Pmc,P,(=.&40.)(>.(=.&8.))Pmoc,$1<.PN,$11.Ptf,$11.Psize,$11.Pws,(;.(=.&40.))Pfr0,(;.(=.&8.))Pfr1,(;.(=.&8.))Pfr2,(;.(=.&8.))Psha,(;.(=.&8.))Pshs,(;.(=.&8.))Ppg1,(;.(=.&8.))P,(6:.R<.VT,VCTX,)P,(6;.R=.)P,(6<.R>.)P,(5;.R?.)P,(?.R10.Vcan,Vdd,Vmadv,)P,(19.R11.VPA,)P,(1.$2.R12.$6=.(4.$5.(6.(7.&40.$6>.))(8.$5.)))P,(1.$2.R13.$6?.(4.$5.(64.(7.&8.+1.))(8.$5.)))P,(1.$2.R14.VT,(4.$5.(6.(7.&40.VCTX,))(8.$5.)))P,(1.$2.R15.(13.VCTX,+8.)(4.$5.(:.(7.&40.VTID,))(8.$5.)))P,(1.$2.R16.(13.$17.+20.)(4.$5.(6.(7.&40.VSB,))(8.$5.)))P,(3:.$2.R17.Va,(4.$5.(6.(7.&40.Va,))(4.$5.(6.(7.&40.Vms,))(4.$5.(6.(7.&40.(48.Vn,)))(4.$5.(6.(7.&40.Vncks,))(8.$5.))))))P,(3:.$2.R18.(13.Va,+20.)(4.$5.(3;.(61.(3>.Vms,+20.))(62.(=.&8.)(7.&8.=)(61.(3>.Vms,+20.))))(8.$5.)))P,(3:.$2.R19.VSHA,(4.$5.(3;.#200.(62.(=.&8.)(7.&8.+?:.)#200.))(8.$5.)))P,(3:.$2.R1:.(13.VSHA,+200.)(4.$5.(3;.(61.(5=.(48.Vn,)+8.))R11.)(8.$5.)))P,(3:.$2.R1;.(13.+7???8000.(5=.(13.(13.Va,+1000.)(48.Vn,))+8.))(4.$5.(3;.(61.(5=.(3>.(3>.Vms,+1000.)(48.Vn,))+8.))(62.(=.&8.)(7.&8.+?:.)(61.(5=.(3>.(3>.Vms,+1000.)(48.Vn,))+8.))))(8.$5.)))P,(70.R1<.VSPA,R16.+1.(7.&40.+47:64.)(7.&40.VSP,)(7.&40.Vn,)(7.&40.$71.)(7.&40.+1.)(7.&40.VSTK,)(7.&40.(13.VSP,-51.))R2=.R2<.R2;.R2:.R29.R28.)P,(3:.$2.R1=.(13.VSTK,-10.)(4.$5.(6.(7.&40.VSP,))(4.$5.(6.(7.&40.+6978<.))(8.$5.))))P,(3:.$2.R1>.(13.VSP,-38.)(4.$5.(6.R30.)(4.$5.(6.R31.)(4.$5.(6.R32.)(4.$5.(6.R33.)(4.$5.(6.R3;.)(4.$5.(6.R3<.)(4.$5.(6.R41.)(8.$5.)))))))))P,(3:.$2.R1?.VSTK,(4.$5.(6.(7.&40.(13.VSTK,+10.)))(4.$5.(6.(7.&40.R1;.))(8.$5.))))P,(72.$2.R20.(13.VSTK,+10.)R1;.)P,(1=.$73.(4<.(=.&40.)R1<.)#1>.)P,(0.(12.+1.R1>.)(12.R1>.+1>.))P,(12.R1?.(13.Vd,+2.))P,(3:.$2.R24.(13.VSTK,+100.)(4.$5.(3;.#708.R1=.)(8.$5.)))P,(3:.$2.R25.(13.VSTK,+808.)(4.$5.(6.(7.&40.VSP,))(8.$5.)))P,(3:.$2.R26.(13.VSTK,+810.)(4.$5.(3;.#8.R1>.)(8.$5.)))P,(3:.$2.R27.(13.VT,+<60.)(4.$5.(64.(7.&8.=))(8.$5.)))P,(3:.$2.R28.(13.VT,+:?0.)(4.$5.(6.R2?.)(4.$5.(6.R2>.)(4.$5.(6.R2=.)(8.$5.)))))P,(3:.$2.R29.(13.VT,+;58.)(4.$5.(6.R2=.)(8.$5.)))P,(59.VhAR,R2:.R28.Vnb0,R27.Vbl0,)P,(5:.VCSc,Vnb0,Vbl0,)P,(12.(13.R29.+80.)(1:.+2.+20.))P,(12.(13.R2;.+2.)(3>.(1:.+2.+1?.)(1:.+2.+1<.)))P,(3=.$2.R2>.Vlo,(13.VSPA,-80.))P,(41.$2.R2?.)P,A5.VK,Vsc',Vr',Vnb0,Vbl0,R2?.P,(58.R31.R30.)P,A4.VGn,Vsc',Vr',Vnb0,Vbl0,P,A4.VGs,Vsc',Vr',Vnb0,Vbl0,P,Px,$11.A4.VGs,Vsc',Vr',(20.$11.Vnb0,(4.$11.R1.(8.$11.)))Vbl0,(74.$2.(75.R58.R57.R53.R52.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R37.R36.R33.R32.R35.)(51.(52.(53.(7.&40.+47=34.)(7.&40.(13.VSPA,-80.))R57.(7.&40.$54.)R56.R55.R54.(7.&40.(76.(77.Vn,)))(7.&40.(46.Vn,))(7.&40.VAB,)R51.R50.R4?.R4>.R4=.R4<.R4;.(7.&40.+8.)(7.&40.(48.Vn,))(7.&40.(47.Vn,))(7.&40.Vn,)(7.&40.$17.)(7.&40.VSTK,)(7.&40.-8.)(7.&40.+7.)(7.&40.VT,)(7.&40.+1.)R40.R3?.R3>.R3=.)R37.(7.&40.+47=34.)R36.(56.(=.&40.))R35.(57.$2.))R34.))")
(* [comment removed for export] *).
    Proof.
      intros ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 j0 jj1 jj2 j4 pgb F fc mc moc N tf size ws fr0 fr1 fr2 sha shs pg1
        AS PS FS DST RS LS GOTFL PPART TH TIDC SBC HH ZB SHH SHU SHT AFR FR16 FR7 STKC HTR HL30 SZB SZD F1800 TFBP F8 UNW STH ST4 DI DCS TFMAX NB2 ST MI HK HJ GN GS GSX.
      facts. pose proof T0 as T0. pose proof T1 as T1. pose proof CX0 as CX0. pose proof CX1 as CX1. pose proof TC as TC. pose proof SB0 as SB0. pose proof SB1 as SB1.
      pose proof SPH as SPH. pose proof TNS as TNS. pose proof CTXNS as CTXNS. pose proof PA0 as PA0. pose proof PA1 as PA1.
      pose proof TCSc as TCS. pose proof CTXCSc as CTXCS. pose proof PACSc as PACS.
      dpose sec_n as (NLO & NFX & RZ & N2E & RNB & RN8 & N2B & MSZ & MSAL & N28).
      assert (ABE : AB = a + 4096) by reflexivity. assert (UBE : UB = AB + rz_size n) by reflexivity. assert (CHBE : CHB = AB + rz_size n + -16) by reflexivity.
      assert (S1E : S1 = 0x7fff8000 + AB / 8) by reflexivity. assert (S2E : S2 = 0x7fff8000 + (UB + r8) / 8) by reflexivity.
      assert (SUBE0 : SUB = 0x7fff8000 + UB / 8) by reflexivity. assert (PGSE0 : PGS = 0x7fff8000 + Z.shiftr (UB + rd) 3) by reflexivity.
      assert (SHAE : SHA = 0x7fff8000 + a / 8) by reflexivity. assert (R8E : r8 = (nfix n + 7) / 8 * 8) by reflexivity. assert (RDE : rd = nfix n / 8 * 8) by reflexivity.
      assert (K2E : k2 = (a + ms - (UB + r8)) / 8) by reflexivity.
      pose proof (Z.div_mod a 4096 ltac:(lia)) as DA. rewrite AAL, Z.add_0_r in DA.
      pose proof (Z.div_mod ms 4096 ltac:(lia)) as DM. rewrite MSAL, Z.add_0_r in DM.
      pose proof (Z.div_mod (nfix n + 7) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (nfix n + 7) 8 ltac:(lia)) as M8.
      pose proof (Z.div_mod (nfix n) 8 ltac:(lia)) as DN. pose proof (Z.mod_pos_bound (nfix n) 8 ltac:(lia)) as MN.
      pose proof (Z.div_mod (rounded n) 8 ltac:(lia)) as DR. rewrite RN8, Z.add_0_r in DR.
      pose proof (Z.div_mod (needed2 n) 8 ltac:(lia)) as DX. rewrite N28, Z.add_0_r in DX.
      (* [comment removed for export] *)
      remember (a / 4096) as qa eqn:Hqa. remember (ms / 4096) as qm eqn:Hqm.
      remember (needed2 n / 8) as qx eqn:Hqx. remember (rounded n / 8) as qr eqn:Hqr.
      pose (q8 := r8 / 8). pose (qd := rd / 8).
      assert (Hq8 : q8 = (nfix n + 7) / 8) by (subst q8; rewrite R8E; rewrite Z.div_mul by (clear; lia); reflexivity).
      assert (Hqd : qd = nfix n / 8) by (subst qd; rewrite RDE; rewrite Z.div_mul by (clear; lia); reflexivity).
      clearbody q8 qd.
      assert (R8E' : r8 = 8 * q8) by (rewrite R8E, Hq8; clear; lia). assert (RDE' : rd = 8 * qd) by (rewrite RDE, Hqd; clear; lia).
      rewrite <- Hq8 in D8. rewrite <- Hqd in DN.
      assert (R8R : q8 <= qr). { rewrite Hq8, Hqr, NFX. unfold rounded, round_up. replace (Z.max n 8) with n by (clear - NLO; lia). replace (n + 8 - 1) with (n + 7) by (clear; lia). clear; lia. }
      assert (G1 : rz_size n = 2048 /\ nfix n = n /\ 0xfc01 <= n /\ n < 2^31 /\ needed2 n = 8 * qx /\ rounded n = 8 * qr /\ qx = qr + 512 /\ n <= 8 * qr <= n + 7
                   /\ ms = 4096 * qm /\ 8 * qx + 4096 <= 4096 * qm < 8 * qx + 8192
                   /\ r8 = 8 * q8 /\ n <= 8 * q8 <= n + 7 /\ q8 <= qr /\ rd = 8 * qd /\ 0 <= 8 * qd <= n /\ n < 8 * qd + 8 /\ qd <= q8 <= qd + 1).
      { rewrite NFX in D8, M8, DN, MN. clear - RZ NFX NLO NB N2E RNB DX DR MSZ DM D8 M8 DN MN R8E' RDE' R8R. repeat match goal with |- _ /\ _ => split end; lia. }
      assert (SHX : Z.shiftr (UB + rd) 3 = 512 * qa + 768 + qd).
      { rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8. rewrite UBE, ABE, RZ, RDE', DA. clear.
        replace (4096 * qa + 4096 + 2048 + 8 * qd) with ((512 * qa + 768 + qd) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
      assert (K2V : k2 = 512 * qm - 768 - q8).
      { rewrite K2E, UBE, ABE, RZ, R8E', DM. replace (a + 4096 * qm - (a + 4096 + 2048 + 8 * q8)) with ((512 * qm - 768 - q8) * 8) by (clear; lia).
        rewrite Z.div_mul by (clear; lia). reflexivity. }
      Ltac dq qa := rewrite Z.div_mul by (clear; lia).
      assert (G2 : a = 4096 * qa /\ 0x65f000 <= a /\ a + ms <= ACEIL /\ AB = a + 4096 /\ UB = a + 6144 /\ CHB = a + 6128
                   /\ SHA = 0x7fff8000 + 512 * qa /\ S1 = SHA + 512 /\ SUB = SHA + 768 /\ PGS = SHA + 768 + qd /\ S2 = SHA + 768 + q8
                   /\ k2 = 512 * qm - 768 - q8 /\ 8 <= k2).
      { split; [exact DA|]. split; [exact A0|]. split; [exact ACE|].
        split; [rewrite ABE; clear; lia|]. split; [rewrite UBE, ABE, RZ; clear; lia|]. split; [rewrite CHBE, ABE, RZ; clear; lia|].
        split. { rewrite SHAE, DA. replace (4096 * qa) with ((512 * qa) * 8) by (clear; lia). dq qa. clear; lia. }
        split. { rewrite S1E, SHAE, ABE, DA. replace (4096 * qa + 4096) with ((512 * qa + 512) * 8) by (clear; lia). replace (4096 * qa) with ((512 * qa) * 8) by (clear; lia). dq qa. dq qa. clear; lia. }
        split. { rewrite SUBE0, SHAE, UBE, ABE, RZ, DA. replace (4096 * qa + 4096 + 2048) with ((512 * qa + 768) * 8) by (clear; lia). replace (4096 * qa) with ((512 * qa) * 8) by (clear; lia). dq qa. dq qa. clear; lia. }
        split. { rewrite PGSE0, SHX, SHAE, DA. replace (4096 * qa) with ((512 * qa) * 8) by (clear; lia). dq qa. clear; lia. }
        split. { rewrite S2E, SHAE, UBE, ABE, RZ, R8E', DA. replace (4096 * qa + 4096 + 2048 + 8 * q8) with ((512 * qa + 768 + q8) * 8) by (clear; lia). replace (4096 * qa) with ((512 * qa) * 8) by (clear; lia). dq qa. dq qa. clear; lia. }
        split; [exact K2V|]. rewrite K2V. clear - MSZ DM N2E RNB DX DR R8R D8 NFX NLO Hqx Hqr. subst qx qr. lia. }
      assert (G3 : lo <= SPA - 512 /\ ACEIL <= lo /\ SPA = SP + -2144 /\ STK = SP + -2128 /\ lo <= SP - 4096 /\ SP + 16 <= 2^47
                   /\ Timg T /\ T + 4096 <= ACEIL /\ 0x65f000 <= CTX /\ CTX + 0x10000 <= ACEIL
                   /\ (0x65f000 <= PA /\ Pband PA 0x800000) /\ PA + 0x800000 <= ACEIL /\ 0 <= ncks /\ ncks + 1 <= 0x4000 * r' /\ 0x4000 * r' <= 2^20).
      { subst SPA STK. clear - LOIMG SPL TOP1 TOP2 T0 T1 CX0 CX1 PA0 PA1 NCK R20. repeat match goal with |- _ /\ _ => split end; lia. }
      (* [comment removed for export] *)
      pose proof (conj G1 (conj G2 G3)) as GEO. clear G1 G2 G3 SHX.
      clear DA DM D8 M8 DN MN DR DX Hqa Hqm Hq8 Hqd Hqx Hqr.
      (* [comment removed for export] *)
      carve GEO ZB 0 4064 Z1. rewrite Z2Nat.id, Z.add_0_r in Z1 by (clear; lia).
      carve GEO ZB 4064 16 MGc. replace (a + 32 + Z.of_nat (Z.to_nat 4064)) with AB in MGc by (clear - GEO; decompose [and] GEO; lia).
      destruct (CB16_words asegs mc AB _ MGc) as (mg0 & mg1 & MG). clear MGc.
      carve GEO ZB 4080 2016 Z2. replace (a + 32 + Z.of_nat (Z.to_nat 4080)) with (AB + 16) in Z2 by (clear - GEO; decompose [and] GEO; lia).
      carve GEO ZB 6096 16 HDc. replace (a + 32 + Z.of_nat (Z.to_nat 6096)) with CHB in HDc by (clear - GEO; decompose [and] GEO; lia).
      destruct (CB16_hdr asegs mc CHB _ HDc) as (b0 & b1 & w2 & w4 & w8 & HDR). clear HDc.
      carve GEO ZB 6112 4096 UC. replace (a + 32 + Z.of_nat (Z.to_nat 6112)) with UB in UC by (clear - GEO; decompose [and] GEO; lia).
      carve GEO ZB 10208 (a + ms - UB - 4096) Z3. replace (a + 32 + Z.of_nat (Z.to_nat 10208)) with (UB + 4096) in Z3 by (clear - GEO; decompose [and] GEO; lia).
      clear ZB.
      (* [comment removed for export] *)
      assert (RD8 : rd / 8 = qd) by (rewrite RDE'; rewrite Z.mul_comm, Z.div_mul by (clear; lia); reflexivity).
      pose proof (CB_sub asegs mc _ _ _ 0 256 SHU ltac:(glia GEO)) as SH1c. rewrite Z.add_0_r in SH1c.
      replace (SHA + 512) with S1 in SH1c by (glia GEO).
      pose proof (CB_sub asegs mc _ _ _ 256 (Z.to_nat qd) SHU ltac:(glia GEO)) as SHSc.
      replace (SHA + 512 + Z.of_nat 256) with SUB in SHSc by (glia GEO).
      assert (PG0 : exists pg, qd < q8 -> rw_cells asegs mc PGS [C1 pg]).
      { destruct (Z_lt_ge_dec qd q8) as [LT|GE].
        - pose proof (CB_sub asegs mc _ _ _ (Z.to_nat (256 + qd)) 1 SHU ltac:(clear - GEO LT; decompose [and] GEO; lia)) as P1.
          replace (SHA + 512 + Z.of_nat (Z.to_nat (256 + qd))) with PGS in P1 by (glia GEO).
          destruct (CB1_byte asegs mc PGS _ P1) as [pg P2]. exists pg. intros _. exact P2.
        - exists (Z_to_bv 8 0). intros LT. exfalso. clear - LT GE. lia. }
      destruct PG0 as [pg0 PG0].
      pose proof (CB_sub asegs mc _ _ _ (Z.to_nat (256 + q8)) (Z.to_nat (qx - 256 - q8)) SHU ltac:(glia GEO)) as S2a.
      replace (SHA + 512 + Z.of_nat (Z.to_nat (256 + q8))) with S2 in S2a by (glia GEO).
      replace ((ms - 4096 - needed2 n) / 8) with (512 * qm - 512 - qx) in SHT.
      2:{ clear - GEO. decompose [and] GEO. replace (ms - 4096 - needed2 n) with ((512 * qm - 512 - qx) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
      replace (2147450880 + (a + 4096 + needed2 n) / 8) with (S2 + Z.of_nat (Z.to_nat (qx - 256 - q8))) in SHT.
      2:{ clear - GEO. decompose [and] GEO. rewrite Z2Nat.id by lia.
          replace (a + 4096 + needed2 n) with ((512 * qa + 512 + qx) * 8) by lia. rewrite Z.div_mul by lia. lia. }
      pose proof (CB_merge asegs mc S2 _ _ _ _ S2a SHT) as SH2c. clear S2a SHT SHU.
      replace (Z.to_nat (qx - 256 - q8) + Z.to_nat (512 * qm - 512 - qx))%nat with (Z.to_nat k2) in SH2c by (glia GEO).
      rewrite <- repeat_app in SH2c || rewrite <- List.repeat_app in SH2c || idtac.
      assert (SPAL : lo <= SPA - 512) by (clear - GEO; decompose [and] GEO; lia). assert (SPAH : SPA <= 2^62) by (clear - GEO; decompose [and] GEO; lia).
      assert (SPAAL : SPA mod 16 = 0).
      { subst SPA. clear - SPA16. apply Z.mod_divide in SPA16; [| lia]. apply Z.mod_divide; [lia|]. destruct SPA16 as [q Hq]. exists (q - 134). lia. }
      assert (SPAAL2 : (SPA + -128) mod 16 = 0).
      { subst SPA. clear - SPA16. apply Z.mod_divide in SPA16; [| lia]. apply Z.mod_divide; [lia|]. destruct SPA16 as [q Hq]. exists (q - 142). lia. }
      assert (SCSA : crange CSc lo (SPA - lo)) by (eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear; lia| clear - GEO; decompose [and] GEO; lia]).
      assert (SCSA2 : crange CSc lo (SPA + -128 - lo)) by (eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear; lia| clear - GEO; decompose [and] GEO; lia]).
      assert (AB16 : AB mod 16 = 0) by (clear - GEO; decompose [and] GEO; replace AB with ((256 * qa + 256) * 16) by lia; apply Z_mod_mult).
      assert (NB32 : 0 <= n < 2^32) by (clear - NB; lia).
      (* [comment removed for export] *)
      eapply (evtA_aevtS_KJ AL CSc (K sc' r' nb0 bl0)
                (hdr_post SPA gp (Z_to_bv 64 A_TP) (Z_to_bv 64 A_INSTANCE) (Z_to_bv 64 STK) t3 t4 t5 t6 F fc n AB STK T (STK + 16) size TID 1 lo b0 w8
                   (Z_to_bv 64 0x47a64) (Z_to_bv 64 SP) (Z_to_bv 64 n) (Z_to_bv 64 A_PC_MALLOC) (Z_to_bv 64 1) (Z_to_bv 64 STK) (Z_to_bv 64 (SP + -81)) s6 s7 s8 s9 s10 s11 fr0 [] mc)
                _ _ moc (KL sc' r' nb0 bl0) HK); [exact HJ| |].
      { eapply (alloc_hdr AL IMG ALWF CSc (CSOKf sc' r' nb0 bl0)) with (CTX := CTX) (b1 := b1) (w2 := w2) (w4 := w4);
          [ exact NB32 | clear - GEO; decompose [and] GEO; lia | clear - GEO; decompose [and] GEO; lia | exact AB16
          | clear - GEO; decompose [and] GEO; lia | clear - SZB; lia | exact TIDB | clear; lia
          | clear - GEO; decompose [and] GEO; lia | clear - GEO; decompose [and] GEO; lia | clear - GEO; decompose [and] GEO; lia | |
          | exact T0 | exact T1 | exact TCS | exact CX0 | exact CX1 | exact CTXCS | | | | |
          | exact AFR | exact HDR | exact TH | exact TIDC | | exact ST | exact LOIMG | clear - SPAL; lia | exact SPAH | exact SPAAL | exact SCSA | apply munch_refl | apply wmono_refl | exact MI ].
        - subst STK. clear - SPA16. apply Z.mod_divide in SPA16; [|lia]. destruct SPA16 as [q Hq]. rewrite Hq. replace (q * 16 + -2128) with ((2 * q - 266) * 8) by lia. apply Z_mod_mult.
        - eapply (crange_sub _ lo (SP - lo)); [exact SCS| clear - GEO; decompose [and] GEO; lia| clear - GEO; decompose [and] GEO; lia].
        - eapply (crange_sub _ a ms); [exact BCS| clear - GEO; decompose [and] GEO; lia| clear - GEO; decompose [and] GEO; lia].
        - left. clear - GEO; decompose [and] GEO; lia.
        - clear - GEO; decompose [and] GEO; lia.
        - clear - GEO ABT; decompose [and] GEO; lia.
        - clear - GEO ABC; decompose [and] GEO; lia.
        - destruct STKC as [STKC0 _]. exact STKC0. }
      cbn beta. intros ms2 mo2 PO HK2 MM2 HJ2. unfold hdr_post in PO.
      ddestruct PO as (x5 & x6 & x7 & x12 & x13 & x14 & x15 & x16 & x17 & b1n & m2 & -> & MU2 & WM2 & MI2 & HDR2 & B1A & B1B & AFR2 & ST2).
      cbn [ms_mem MS MSsvc] in HJ2.
      rewrite FP. change (Z.b2z false) with 0.
      fold UB in HDR2 |- *. fold CHB in MU2, HDR2 |- *.
      (* [comment removed for export] *)
      assert (DJW : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from [(lo, SPA); (CHB, CHB + 8)] A k).
      { intros A k H. cbn [disjoint_from]. clear - H GEO; decompose [and] GEO; repeat split; lia. }
      assert (DJhi : forall A k, SPA <= A -> disjoint_from [(lo, SPA); (CHB, CHB + 8)] A k).
      { intros A k H. cbn [disjoint_from]. clear - H GEO; decompose [and] GEO; repeat split; lia. }
      dpose (proj1 (proj2 (proj2 DI))) as (_ & DMF & _).
      dpose (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DI)))))))) as (_ & DBF & _).
      assert (DI2 : depot_inv m2 N nb0 tf bl0).
      { eapply (depot_inv_transport _ mc m2 N nb0 tf bl0 DI MU2 WM2 DJW).
        - intros k Hk. pose proof (APBn k Hk) as APA.
          dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb0) DMF (Z.to_nat k) 0 ltac:(clear - Hk; lia)) as (_ & X & _).
          cbn [disjoint_from]. unfold dblk in *. clear - APA X GEO. decompose [and] GEO. repeat split; lia.
        - intros j Hj. pose proof (APBs j Hj) as APA.
          dpose (proj1 (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl0) DBF (Z.to_nat j) 0 ltac:(clear - Hj; lia)) as (_ & X & _).
          cbn [disjoint_from]. unfold sblk in *. clear - APA X GEO. decompose [and] GEO. repeat split; lia. }
      assert (DST2 : depot_statics m2) by (eapply (depot_statics_transport _ mc m2 DST MU2); intros A k H; apply DJW; clear - H; lia).
      assert (TCS2 : crange CSc (STK + 16) 240) by (eapply (crange_sub _ lo (SP - lo)); [exact SCS| glia GEO| glia GEO]).
      assert (TRAL : (STK + 16) mod 8 = 0).
      { subst STK. clear - SPA16. apply Z.mod_divide in SPA16; [| lia]. apply Z.mod_divide; [lia|]. destruct SPA16 as [q Hq]. exists (2 * q - 264). lia. }
      assert (HTR2 : u64arr asegs m2 (STK + 16) ws) by (eapply u64arr_transport; [exact HTR| exact MU2| exact WM2| apply DJhi; glia GEO]).
      eapply aevtS_bind.
      { replace (Z_to_bv 64 size) with (Z_to_bv 64 (size + 0 * 2^32)) by (f_equal; clear; lia).
        eapply (depot_put_cfg AL IMG ALWF (CSf sc' r') (K sc' r') (CSOKf sc' r') (KL sc' r') (CSmono_n sc' r') (CSmono_s sc' r') (K_apart sc' r') (Gn sc' r') (Gs sc' r')
                  (T_node sc' r') (T_store sc' r') (ROOM_n sc' r') (ROOM_s sc' r')) with (lo := lo);
          first [exact HK2| exact HJ2| exact MI2| exact DI2| exact DST2| exact HTR2| exact HL30| exact SZB| exact DCS| exact ST2| exact SCSA2| exact TCS2| exact LOIMG
                | exact SPAAL2| exact TRAL| exact TFMAX| exact NB2| exact GN| exact GS| exact GSX| idtac].
        all: first [clear; lia | clear - GEO; decompose [and] GEO; lia | match goal with |- ?G => fail 99 "depot side" G end]. }
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
        - apply (CSf_noshadow sc' r' nb' bl' (dblk nb' k)); [apply NBCS3; clear; lia| clear - H1 H2 Hw n0 n1 l; lia].
        - apply (CSf_noshadow sc' r' nb' bl' A); [apply NBCS3; clear - n0 n1 n2; lia| clear - H1 H2 Hw n0 n1 n2; lia]. }
      assert (BSsh : forall j (A w : Z), 0 <= j < Z.of_nat (length bl') -> 0x7fff8000 <= A -> A + w <= 0x10007fff8000 -> 0 < w ->
                A + w <= sblk bl' j \/ sblk bl' j + 2^23 <= A).
      { intros j A w Hj H1 H2 Hw. specialize (BLCS3 j Hj).
        destruct (Z_le_dec (sblk bl' j + 2^23) A); [right; assumption|]. destruct (Z_le_dec (A + w) (sblk bl' j)); [left; assumption|]. exfalso.
        destruct (Z_le_dec A (sblk bl' j)).
        - apply (CSf_noshadow sc' r' nb' bl' (sblk bl' j)); [apply BLCS3; clear; lia| clear - H1 H2 Hw n0 n1 l; lia].
        - apply (CSf_noshadow sc' r' nb' bl' A); [apply BLCS3; clear - n0 n1 n2; lia| clear - H1 H2 Hw n0 n1 n2; lia]. }
      (* [comment removed for export] *)
      pose proof (dkeep_low m2 m3 lo (SPA + -128) nb' bl' DK3 ltac:(clear - GEO; decompose [and] GEO; lia)
                    ltac:(intros k Hk; exact (proj1 (BN k Hk))) ltac:(intros j Hj; exact (proj1 (BS j Hj)))) as MUlow.
      assert (MUT : munch [(0, T); (T + 4096, 2^64)] m2 m3).
      { eapply (dkeep_window m2 m3 lo (SPA + -128) nb' bl' T 4096 DK3); [clear - T0; lia| clear - T1; lia| left; glia GEO| unfold A_SS, A_DEP_END; clear - T0; lia| |].
        - intros k Hk. apply (BNold k T 4096 Hk TCS ltac:(clear; lia) APTn).
        - intros j Hj. apply (BSold j T 4096 Hj TCS ltac:(clear; lia) APTs). }
      assert (MUC : munch [(0, CTX); (CTX + 0x10000, 2^64)] m2 m3).
      { eapply (dkeep_window m2 m3 lo (SPA + -128) nb' bl' CTX 0x10000 DK3); [clear - CX0; lia| clear - CX1; lia| left; glia GEO| unfold A_SS, A_DEP_END; clear - CX0; lia| |].
        - intros k Hk. apply (BNold k CTX 0x10000 Hk CTXCS ltac:(clear; lia) APCn).
        - intros j Hj. apply (BSold j CTX 0x10000 Hj CTXCS ltac:(clear; lia) APCs). }
      assert (MUB : munch [(0, a); (a + ms, 2^64)] m2 m3).
      { eapply (dkeep_window m2 m3 lo (SPA + -128) nb' bl' a ms DK3); [clear - A0; lia| glia GEO| left; glia GEO| unfold A_SS, A_DEP_END; clear - A0; lia| |].
        - intros k Hk. apply (BNold k a ms Hk BCS ltac:(glia GEO) APBn).
        - intros j Hj. apply (BSold j a ms Hj BCS ltac:(glia GEO) APBs). }
      assert (MUSH : munch [(0, SHA); (SHA + 512 * qm, 2^64)] m2 m3).
      { eapply (dkeep_window m2 m3 lo (SPA + -128) nb' bl' SHA (512 * qm) DK3); [glia GEO| glia GEO| left; glia GEO| unfold A_SS, A_DEP_END; right; glia GEO| |].
        - intros k Hk. apply (BNsh k SHA (512 * qm) Hk); clear - GEO ABAND; decompose [and] GEO; lia.
        - intros j Hj. apply (BSsh j SHA (512 * qm) Hj); clear - GEO ABAND; decompose [and] GEO; lia. }
      assert (MUST : munch [(0, SPA + -128); (SPA + -128 + 2272, 2^64)] m2 m3).
      { eapply (dkeep_window m2 m3 lo (SPA + -128) nb' bl' (SPA + -128) 2272 DK3); [glia GEO| glia GEO| right; clear; lia| right; unfold A_DEP_END; glia GEO| |].
        - intros k Hk. right. pose proof (BN k Hk). clear - H GEO; decompose [and] GEO; lia.
        - intros j Hj. right. pose proof (BS j Hj). clear - H GEO; decompose [and] GEO; lia. }
      assert (MUPA : munch [(0, PA); (PA + 8 * (0x4000 * r'), 2^64)] m2 m3).
      { destruct (Z.eq_dec r' 0) as [R0|R0].
        { exfalso. clear - R0 GEO. decompose [and] GEO. lia. }
        eapply (dkeep_window m2 m3 lo (SPA + -128) nb' bl' PA (8 * (0x4000 * r')) DK3); [clear - PA0; lia| glia GEO| left; glia GEO| unfold A_SS, A_DEP_END; clear - PA0; lia| |].
        - intros k Hk. replace (8 * (0x4000 * r')) with (0x20000 * r') by (clear; lia).
          pose proof (BNold k PA (0x20000 * r') Hk PACS ltac:(clear - R0 HR'; lia)) as X. apply X. intros k0 Hk0. pose proof (APPn k0 Hk0) as Y. clear - Y GEO. decompose [and] GEO. lia.
        - intros j Hj. replace (8 * (0x4000 * r')) with (0x20000 * r') by (clear; lia).
          pose proof (BSold j PA (0x20000 * r') Hj PACS ltac:(clear - R0 HR'; lia)) as X. apply X. intros jj Hjj. pose proof (APPs jj Hjj) as Y. clear - Y GEO. decompose [and] GEO. lia. }
      (* [comment removed for export] *)
      assert (AS2 : allocA_statics m2 T CTX).
      { eapply (allocA_statics_transport _ mc m2 T CTX AS MU2); [intros A k H; apply DJW; exact H|]. cbn [disjoint_from]. clear - GEO ABC; decompose [and] GEO; repeat split; lia. }
      assert (PS2 : poison_statics m2) by (eapply (poison_statics_transport _ mc m2 PS MU2); intros A k H; apply DJW; clear - H; lia).
      assert (FS2 : fin_statics m2) by (eapply (fin_statics_transport _ mc m2 FS MU2); intros A k H; apply DJW; exact H).
      assert (RS2 : rsmr_statics m2 can dd madv) by (eapply (rsmr_statics_transport2 _ mc m2 can dd madv RS MU2); intros A k H _ _; apply DJW; exact H).
      assert (LS2 : large_statics m2 PA) by (eapply (large_statics_transport2 _ mc m2 PA LS MU2); intros A k H _ _; apply DJW; exact H).
      assert (GOTFL2 : ro_cells asegs m2 A_GOT_FLAGS [C8 (Z_to_bv 64 A_FLAGS)]) by (t2o GOTFL MU2 ltac:(apply DJW; unfold A_GOT_FLAGS; clear; lia)).
      assert (PPART2 : ro_cells asegs m2 A_FL_PPART [C1 (Z_to_bv 8 1)]) by (t2o PPART MU2 ltac:(apply DJW; unfold A_FL_PPART; clear; lia)).
      assert (SBC2 : ro_cells asegs m2 (A_INSTANCE + 32) [C8 (Z_to_bv 64 SB)]) by (t2o SBC MU2 ltac:(apply DJW; unfold A_INSTANCE; clear; lia)).
      assert (TH2 : ro_cells asegs m2 T [C8 (Z_to_bv 64 CTX)]) by (t2o TH MU2 ltac:(clear - GEO ABT; decompose [and] GEO; repeat split; lia)).
      assert (TIDC2 : ro_cells asegs m2 (CTX + 8) [C4 (Z_to_bv 64 TID)]) by (t2o TIDC MU2 ltac:(clear - GEO ABC; decompose [and] GEO; repeat split; lia)).
      assert (HH2 : rw_cells asegs m2 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed2 n)); C8 (Z_to_bv 64 ncks)]) by (t2r GEO HH MU2 WM2 ltac:(glia GEO)).
      assert (Z12 : rw_cells asegs m2 (a + 32) [CB (Z.to_nat 4064) (repeat (Z_to_bv 8 0) (Z.to_nat 4064))]) by (t2r GEO Z1 MU2 WM2 ltac:(glia GEO)).
      assert (MG2 : rw_cells asegs m2 AB [C8 mg0; C8 mg1]) by (t2r GEO MG MU2 WM2 ltac:(glia GEO)).
      assert (Z22 : rw_cells asegs m2 (AB + 16) [CB (Z.to_nat 2016) (repeat (Z_to_bv 8 0) (Z.to_nat 2016))]) by (t2r GEO Z2 MU2 WM2 ltac:(glia GEO)).
      assert (UC2 : rw_cells asegs m2 UB [CB (Z.to_nat 4096) (repeat (Z_to_bv 8 0) (Z.to_nat 4096))]) by (t2r GEO UC MU2 WM2 ltac:(glia GEO)).
      assert (Z32 : rw_cells asegs m2 (UB + 4096) [CB (Z.to_nat (a + ms - UB - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (a + ms - UB - 4096)))]) by (t2r GEO Z3 MU2 WM2 ltac:(glia GEO)).
      assert (SHH2 : rw_cells asegs m2 SHA [CB 512 (repeat (Z_to_bv 8 250) 512)]) by (t2r GEO SHH MU2 WM2 ltac:(clear - GEO ABAND; decompose [and] GEO; repeat split; lia)).
      assert (SH1c2 : rw_cells asegs m2 S1 [CB 256 (firstn 256 (skipn 0 sha))]) by (t2r GEO SH1c MU2 WM2 ltac:(clear - GEO ABAND; decompose [and] GEO; repeat split; lia)).
      assert (SHSc2 : rw_cells asegs m2 SUB [CB (Z.to_nat qd) (firstn (Z.to_nat qd) (skipn 256 sha))]) by (t2r GEO SHSc MU2 WM2 ltac:(clear - GEO ABAND; decompose [and] GEO; repeat split; lia)).
      assert (PG02 : qd < q8 -> rw_cells asegs m2 PGS [C1 pg0]) by (intros LT; t2r GEO (PG0 LT) MU2 WM2 ltac:(clear - GEO ABAND; decompose [and] GEO; repeat split; lia)).
      assert (SH2c2 : rw_cells asegs m2 S2 [CB (Z.to_nat k2) (firstn (Z.to_nat (qx - 256 - q8)) (skipn (Z.to_nat (256 + q8)) sha) ++ repeat (Z_to_bv 8 250) (Z.to_nat (512 * qm - 512 - qx)))]).
      { t2r GEO SH2c MU2 WM2 ltac:(clear - GEO ABAND; decompose [and] GEO; repeat split; lia). }
      assert (STH2 : rw_cells asegs m2 (T + 2800) [C8 j0; C8 jj1; C8 jj2]) by (t2r GEO STH MU2 WM2 ltac:(clear - GEO ABT; decompose [and] GEO; repeat split; lia)).
      assert (ST42 : rw_cells asegs m2 (T + 2904) [C8 j4]) by (t2r GEO ST4 MU2 WM2 ltac:(clear - GEO ABT; decompose [and] GEO; repeat split; lia)).
      assert (UNW2 : rw_cells asegs m2 (T + 3168) [C1 (Z_to_bv 8 0)]) by (t2r GEO UNW MU2 WM2 ltac:(clear - GEO ABT; decompose [and] GEO; repeat split; lia)).
      assert (FR16' : rw_cells asegs m2 (STK + -16) [C8 (Z_to_bv 64 SP); C8 (Z_to_bv 64 0x6978c)]) by (t2r GEO FR16 MU2 WM2 ltac:(apply DJhi; glia GEO)).
      assert (FR7' : rw_cells asegs m2 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (t2r GEO FR7 MU2 WM2 ltac:(apply DJhi; glia GEO)).
      assert (STKC2 : rw_cells asegs m2 STK [C8 (Z_to_bv 64 (STK + 16)); C8 (Z_to_bv 64 size)]) by (t2r GEO STKC MU2 WM2 ltac:(apply DJhi; glia GEO)).
      assert (F1800' : rw_cells asegs m2 (STK + 256) [CB 1800 fr1]) by (t2r GEO F1800 MU2 WM2 ltac:(apply DJhi; glia GEO)).
      assert (TFBP' : rw_cells asegs m2 (STK + 2056) [C8 (Z_to_bv 64 SP)]) by (t2r GEO TFBP MU2 WM2 ltac:(apply DJhi; glia GEO)).
      assert (F8' : rw_cells asegs m2 (STK + 2064) [CB 8 fr2]) by (t2r GEO F8 MU2 WM2 ltac:(apply DJhi; glia GEO)).
      clear AS PS FS RS LS GOTFL PPART SBC TH TIDC HH Z1 MG Z2 UC Z3 SHH SH1c SHSc PG0 SH2c STH ST4 UNW FR16 FR7 STKC F1800 TFBP F8.
      (* [comment removed for export] *)
      assert (WD : forall A sz A' k, A <= A' -> A' + k <= A + sz -> disjoint_from [(0, A); (A + sz, 2^64)] A' k) by (intros; cbn [disjoint_from]; lia).
      assert (LOWD : forall A k, (0x10000 <= A /\ A + k <= A_SS) \/ (A_DEP_END <= A /\ A + k <= 0x65f000) -> disjoint_from [(A_SS, A_DEP_END); (0x65f000, 2^64)] A k)
        by (intros A k H; unfold A_SS, A_DEP_END in *; cbn [disjoint_from]; clear - H; lia).
      assert (AS3 : allocA_statics m3 T CTX) by (eapply (allocA_statics_transport2 _ _ m2 m3 T CTX AS2 MUlow MUC LOWD); apply WD; clear; lia).
      assert (PS3 : poison_statics m3) by (eapply (poison_statics_transport _ m2 m3 PS2 MUlow); intros A k H; apply LOWD; left; exact H).
      assert (FS3 : fin_statics m3) by (eapply (fin_statics_transport2 _ m2 m3 FS2 MUlow LOWD)).
      assert (RS3 : rsmr_statics m3 can dd madv) by (eapply (rsmr_statics_transport2 _ m2 m3 can dd madv RS2 MUlow); intros A k H1 H2 H3; apply LOWD; unfold A_SS, A_DEP_END, A_INSTANCE in *; clear - H1 H2 H3; lia).
      assert (LS3 : large_statics m3 PA) by (eapply (large_statics_transport2 _ m2 m3 PA LS2 MUlow); intros A k H1 H2 H3; apply LOWD; unfold A_SS, A_DEP_END, A_INSTANCE in *; clear - H1 H2 H3; lia).
      assert (GOTFL3 : ro_cells asegs m3 A_GOT_FLAGS [C8 (Z_to_bv 64 A_FLAGS)]) by (eapply ro_cells_transport; [exact GOTFL2| exact MUlow| apply LOWD; unfold A_GOT_FLAGS, A_SS; cbn; clear; lia]).
      assert (PPART3 : ro_cells asegs m3 A_FL_PPART [C1 (Z_to_bv 8 1)]) by (eapply ro_cells_transport; [exact PPART2| exact MUlow| apply LOWD; unfold A_FL_PPART, A_SS; cbn; clear; lia]).
      assert (SBC3 : ro_cells asegs m3 (A_INSTANCE + 32) [C8 (Z_to_bv 64 SB)]) by (eapply ro_cells_transport; [exact SBC2| exact MUlow| apply LOWD; unfold A_INSTANCE, A_SS; cbn; clear; lia]).
      assert (TH3 : ro_cells asegs m3 T [C8 (Z_to_bv 64 CTX)]) by (eapply ro_cells_transport; [exact TH2| exact MUT| apply WD; cbn; clear; lia]).
      assert (TIDC3 : ro_cells asegs m3 (CTX + 8) [C4 (Z_to_bv 64 TID)]) by (eapply ro_cells_transport; [exact TIDC2| exact MUC| apply WD; cbn; clear; lia]).
      assert (HH3 : rw_cells asegs m3 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed2 n)); C8 (Z_to_bv 64 ncks)]) by (t3r GEO WD HH2 MUB WM3 ltac:(glia GEO)).
      assert (Z13 : rw_cells asegs m3 (a + 32) [CB (Z.to_nat 4064) (repeat (Z_to_bv 8 0) (Z.to_nat 4064))]) by (t3r GEO WD Z12 MUB WM3 ltac:(glia GEO)).
      assert (MG3 : rw_cells asegs m3 AB [C8 mg0; C8 mg1]) by (t3r GEO WD MG2 MUB WM3 ltac:(glia GEO)).
      assert (Z23 : rw_cells asegs m3 (AB + 16) [CB (Z.to_nat 2016) (repeat (Z_to_bv 8 0) (Z.to_nat 2016))]) by (t3r GEO WD Z22 MUB WM3 ltac:(glia GEO)).
      assert (HDR3 : rw_cells asegs m3 CHB [C1 b0; C1 (Z_to_bv 8 b1n); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nfix n)); C8 w8]) by (t3r GEO WD HDR2 MUB WM3 ltac:(glia GEO)).
      assert (UC3 : rw_cells asegs m3 UB [CB (Z.to_nat 4096) (repeat (Z_to_bv 8 0) (Z.to_nat 4096))]) by (t3r GEO WD UC2 MUB WM3 ltac:(glia GEO)).
      assert (Z33 : rw_cells asegs m3 (UB + 4096) [CB (Z.to_nat (a + ms - UB - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (a + ms - UB - 4096)))]) by (t3r GEO WD Z32 MUB WM3 ltac:(glia GEO)).
      assert (SHH3 : rw_cells asegs m3 SHA [CB 512 (repeat (Z_to_bv 8 250) 512)]) by (t3r GEO WD SHH2 MUSH WM3 ltac:(glia GEO)).
      assert (SH1c3 : rw_cells asegs m3 S1 [CB 256 (firstn 256 (skipn 0 sha))]) by (t3r GEO WD SH1c2 MUSH WM3 ltac:(glia GEO)).
      assert (SHSc3 : rw_cells asegs m3 SUB [CB (Z.to_nat qd) (firstn (Z.to_nat qd) (skipn 256 sha))]) by (t3r GEO WD SHSc2 MUSH WM3 ltac:(glia GEO)).
      assert (PG03 : qd < q8 -> rw_cells asegs m3 PGS [C1 pg0]) by (intros LT; t3r GEO WD (PG02 LT) MUSH WM3 ltac:(glia GEO)).
      assert (SH2c3 : rw_cells asegs m3 S2 [CB (Z.to_nat k2) (firstn (Z.to_nat (qx - 256 - q8)) (skipn (Z.to_nat (256 + q8)) sha) ++ repeat (Z_to_bv 8 250) (Z.to_nat (512 * qm - 512 - qx)))]) by (t3r GEO WD SH2c2 MUSH WM3 ltac:(glia GEO)).
      assert (STH3 : rw_cells asegs m3 (T + 2800) [C8 j0; C8 jj1; C8 jj2]) by (t3r GEO WD STH2 MUT WM3 ltac:(clear; lia)).
      assert (ST43 : rw_cells asegs m3 (T + 2904) [C8 j4]) by (t3r GEO WD ST42 MUT WM3 ltac:(clear; lia)).
      assert (UNW3 : rw_cells asegs m3 (T + 3168) [C1 (Z_to_bv 8 0)]) by (t3r GEO WD UNW2 MUT WM3 ltac:(clear; lia)).
      assert (AFR3 : allocA_frame m3 SPA fr0 1 (Z_to_bv 64 0x47a64) (Z_to_bv 64 SP) (Z_to_bv 64 n) (Z_to_bv 64 A_PC_MALLOC) (Z_to_bv 64 1) (Z_to_bv 64 STK) (Z_to_bv 64 (SP + -81)) s6 s7 s8 s9 s10 s11).
      { unfold allocA_frame in *. t3r GEO WD AFR2 MUST WM3 ltac:(glia GEO). }
      assert (FR7'3 : rw_cells asegs m3 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (t3r GEO WD FR7' MUST WM3 ltac:(glia GEO)).
      assert (STKC3 : rw_cells asegs m3 STK [C8 (Z_to_bv 64 (STK + 16)); C8 (Z_to_bv 64 size)]) by (t3r GEO WD STKC2 MUST WM3 ltac:(glia GEO)).
      assert (F1800'3 : rw_cells asegs m3 (STK + 256) [CB 1800 fr1]) by (t3r GEO WD F1800' MUST WM3 ltac:(glia GEO)).
      assert (TFBP'3 : rw_cells asegs m3 (STK + 2056) [C8 (Z_to_bv 64 SP)]) by (t3r GEO WD TFBP' MUST WM3 ltac:(glia GEO)).
      assert (F8'3 : rw_cells asegs m3 (STK + 2064) [CB 8 fr2]) by (t3r GEO WD F8' MUST WM3 ltac:(glia GEO)).
      assert (FR16'3 : rw_cells asegs m3 (STK + -16) [C8 (Z_to_bv 64 SP); C8 (Z_to_bv 64 0x6978c)]) by (t3r GEO WD FR16' MUST WM3 ltac:(glia GEO)).
      assert (TCS3 : crange (CSf sc' r' nb' bl') T 4096) by (exact (ALazy.crange_mono _ _ _ _ CSM TCS)).
      assert (CTXCS3 : crange (CSf sc' r' nb' bl') CTX 0x10000) by (exact (ALazy.crange_mono _ _ _ _ CSM CTXCS)).
      assert (BCS3 : crange (CSf sc' r' nb' bl') a ms) by (exact (ALazy.crange_mono _ _ _ _ CSM BCS)).
      assert (SCS3 : crange (CSf sc' r' nb' bl') lo (SP - lo)) by (exact (ALazy.crange_mono _ _ _ _ CSM SCS)).
      assert (IDB' : 0 <= id < 2^31) by (clear - IDB NB' NB2; lia).
      assert (SCSA2'' : crange (CSf sc' r' nb' bl') lo (SPA + -128 - lo)) by (exact (ALazy.crange_mono _ _ _ _ CSM SCSA2)).
      clear AS2 PS2 FS2 RS2 LS2 GOTFL2 PPART2 SBC2 TH2 TIDC2 HH2 Z12 MG2 Z22 UC2 Z32 SHH2 SH1c2 SHSc2 PG02 SH2c2 STH2 ST42 UNW2 FR7' STKC2 F1800' TFBP' F8' FR16'.
      (* [comment removed for export] *)
      eapply (evtA_aevtS_KJ AL (CSf sc' r' nb' bl') (K sc' r' nb' bl') _ _ _ mo3 (KL sc' r' nb' bl') HK3); [exact HJ3| |].
      { eapply (ssegC1 AL IMG ALWF (CSf sc' r' nb' bl') (CSOKf sc' r' nb' bl') ASB SP n lo T TID SB PA a ms NB32 FP LOIMG SPL SPH SPA16 TIDB A0 AAL eq_refl ACE ABAND SB0 SB1 APT)
          with (ncks := ncks) (sh1 := firstn 256 (skipn 0 sha)) (sh2 := firstn (Z.to_nat (qx - 256 - q8)) (skipn (Z.to_nat (256 + q8)) sha) ++ repeat (Z_to_bv 8 250) (Z.to_nat (512 * qm - 512 - qx)));
          [ exact IDB' | exact B1B | exact BCS3 | exact HDR3 | exact HH3 | exact SBC3 | exact LS3 | exact PS3 | exact SH1c3 | exact SH2c3 | exact ST3 | exact SCS3 | exact MI3 ]. }
      cbn beta. intros ms4 mo4 PO4 HK4 MM4 HJ4. unfold ssegC1_post in PO4.
      ddestruct PO4 as (y5 & y6 & y7 & ya3 & ya4 & ya5 & ya6 & ya7 & y28 & y29 & y30 & y31 & m4 & -> & MU4 & WM4 & MI4 & HDR4 & SHP1 & SHP2 & ST4).
      cbn [ms_mem MS MSsvc] in HJ4.
      change (munch [(lo, SPA + -128); (CHB + 8, CHB + 16); (S1, S1 + 256); (S2, S2 + k2)] m3 m4) in MU4.
      change (rw_cells asegs m4 S1 [CB 256%nat (repeat (Z_to_bv 8 0xfa) 256%nat)]) in SHP1.
      change (rw_cells asegs m4 S2 [CB (Z.to_nat k2) (repeat (Z_to_bv 8 0xfa) (Z.to_nat k2))]) in SHP2.
      change (rw_cells asegs m4 CHB [C1 b0; C1 (Z_to_bv 8 b1n); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nfix n)); C8 (Z_to_bv 64 (Z.lor (TID * 2^32) id))]) in HDR4.
      assert (DJ4lo : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from [(lo, SPA + -128); (CHB + 8, CHB + 16); (S1, S1 + 256); (S2, S2 + k2)] A k).
      { intros A k H. cbn [disjoint_from]. clear - H GEO. decompose [and] GEO. repeat split; lia. }
      Ltac t4r GEO H MU WM tac := eapply rw_cells_transport; [exact H| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add length repeat app]; rewrite ?app_length, ?firstn_length, ?repeat_length, ?Nat.add_0_r, ?Z2Nat.id by (clear - GEO; decompose [and] GEO; lia); tac].
      assert (PS4 : poison_statics m4) by (eapply (poison_statics_transport _ m3 m4 PS3 MU4); intros A k H; apply DJ4lo; clear - H; lia).
      assert (RS4 : rsmr_statics m4 can dd madv) by (eapply (rsmr_statics_transport2 _ m3 m4 can dd madv RS3 MU4); intros A k H _ _; apply DJ4lo; exact H).
      assert (SHSc4 : rw_cells asegs m4 SUB [CB (Z.to_nat qd) (firstn (Z.to_nat qd) (skipn 256 sha))]) by (t4r GEO SHSc3 MU4 WM4 ltac:(clear - GEO ABAND; decompose [and] GEO; repeat split; lia)).
      rewrite <- RD8 in SHSc4.
      (* [comment removed for export] *)
      assert (UB8 : UB mod 8 = 0) by (clear - GEO; decompose [and] GEO; replace UB with ((512 * qa + 768) * 8) by lia; apply Z_mod_mult).
      assert (RD8m : rd mod 8 = 0) by (rewrite RDE'; rewrite Z.mul_comm; apply Z_mod_mult).
      assert (RD8le : 8 <= rd) by (clear - GEO; decompose [and] GEO; lia).
      assert (RNGU : (8 <= UB /\ UB <= 0x7fff7ff8 /\ UB + rd <= 0x7fff8000) \/ (0x10007fff8000 <= UB /\ 0x10007fff8008 <= UB + rd /\ UB <= 0x7ffffffffff8 /\ UB + rd <= 0x800000000000))
        by (clear - GEO ABAND; decompose [and] GEO; lia).
      assert (RDMAX : rd <= 2^40).
      { unfold rd, nfix. pose proof (Z.div_mod (Z.max n 1) 8 ltac:(clear; lia)) as D8. pose proof (Z.mod_pos_bound (Z.max n 1) 8 ltac:(clear; lia)) as M8. clear - NB D8 M8. lia. }
      pose proof (PZ sc' r' nb' bl' UB rd UB8 RD8m RD8le RDMAX RNGU) as SITE. unfold poison0_siteS in SITE.
      eapply SITE; clear SITE;
        [ eapply (crange_sub _ a ms); [exact BCS3| glia GEO| glia GEO]
        | exact SHSc4 | exact PS4 | exact RS4 | exact ST4 | exact LOIMG | glia GEO | glia GEO | exact SPAAL2 | exact SCSA2'' | exact MI4 | exact HK4 | exact HJ4 | ].
      intros c5 PO5. unfold poison0_postS in PO5.
      ddestruct PO5 as (ms5 & mo5 & z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6 & m5 & -> & -> & MU5 & WM5 & MI5 & SHZ & ST5 & HK5 & HJ5).
      replace (ret_pc (Z_to_bv 64 0x47f4c)) with (Z_to_bv 64 0x47f4c) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
      change (munch [(lo, SPA + -128); (SUB, SUB + rd / 8)] m4 m5) in MU5. rewrite RD8 in MU5.
      change (rw_cells asegs m5 SUB [CB (Z.to_nat (rd / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (rd / 8)))]) in SHZ.
      (* [comment removed for export] *)
      assert (MU35 : munch [(lo, SPA + -128); (CHB + 8, CHB + 16); (S1, S1 + 256); (S2, S2 + k2); (SUB, SUB + qd)] m3 m5).
      { eapply munch_trans. { eapply munch_weaken; [| exact MU4]. unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto. }
        eapply munch_weaken; [| exact MU5]. unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto. }
      assert (WM35 : wmono asegs m3 m5) by (eapply wmono_trans; [exact WM4| exact WM5]).
      assert (DJ5lo : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from [(lo, SPA + -128); (CHB + 8, CHB + 16); (S1, S1 + 256); (S2, S2 + k2); (SUB, SUB + qd)] A k).
      { intros A k H. cbn [disjoint_from]. clear - H GEO. decompose [and] GEO. repeat split; lia. }
      assert (DJ5hi : forall A k, SPA + -128 <= A -> disjoint_from [(lo, SPA + -128); (CHB + 8, CHB + 16); (S1, S1 + 256); (S2, S2 + k2); (SUB, SUB + qd)] A k).
      { intros A k H. cbn [disjoint_from]. clear - H GEO. decompose [and] GEO. repeat split; lia. }
      assert (AS5 : allocA_statics m5 T CTX).
      { eapply (allocA_statics_transport _ m3 m5 T CTX AS3 MU35); [intros A k H; apply DJ5lo; exact H|]. cbn [disjoint_from]. clear - GEO ABC CTXNS; decompose [and] GEO; repeat split; lia. }
      assert (PS5 : poison_statics m5) by (eapply (poison_statics_transport _ m3 m5 PS3 MU35); intros A k H; apply DJ5lo; clear - H; lia).
      assert (FS5 : fin_statics m5) by (eapply (fin_statics_transport _ m3 m5 FS3 MU35); exact DJ5lo).
      assert (GOTFL5 : ro_cells asegs m5 A_GOT_FLAGS [C8 (Z_to_bv 64 A_FLAGS)]) by (t2o GOTFL3 MU35 ltac:(apply DJ5lo; unfold A_GOT_FLAGS; clear; lia)).
      assert (PPART5 : ro_cells asegs m5 A_FL_PPART [C1 (Z_to_bv 8 1)]) by (t2o PPART3 MU35 ltac:(apply DJ5lo; unfold A_FL_PPART; clear; lia)).
      assert (HDR5 : rw_cells asegs m5 CHB [C1 b0; C1 (Z_to_bv 8 b1n); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 (nfix n)); C8 (Z_to_bv 64 (Z.lor (TID * 2^32) id))])
        by (t4r GEO HDR4 MU5 WM5 ltac:(clear - GEO ABAND; decompose [and] GEO; repeat split; lia)).
      assert (MG5 : rw_cells asegs m5 AB [C8 mg0; C8 mg1]) by (t4r GEO MG3 MU35 WM35 ltac:(clear - GEO ABAND; decompose [and] GEO; repeat split; lia)).
      assert (MIN4 : Z.min (nfix n) 4096 = 4096) by (clear - GEO; decompose [and] GEO; lia).
      assert (UC5 : rw_cells asegs m5 UB [CB (Z.to_nat (Z.min (nfix n) 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat 4096))]).
      { rewrite MIN4. t4r GEO UC3 MU35 WM35 ltac:(clear - GEO ABAND; decompose [and] GEO; repeat split; lia). }
      assert (STH5 : rw_cells asegs m5 (T + 2800) [C8 j0; C8 jj1; C8 jj2]) by (t4r GEO STH3 MU35 WM35 ltac:(clear - GEO ABT TNS; decompose [and] GEO; repeat split; lia)).
      assert (ST45 : rw_cells asegs m5 (T + 2904) [C8 j4]) by (t4r GEO ST43 MU35 WM35 ltac:(clear - GEO ABT TNS; decompose [and] GEO; repeat split; lia)).
      assert (AFR5 : allocA_frame m5 SPA fr0 1 (Z_to_bv 64 0x47a64) (Z_to_bv 64 SP) (Z_to_bv 64 n) (Z_to_bv 64 A_PC_MALLOC) (Z_to_bv 64 1) (Z_to_bv 64 STK) (Z_to_bv 64 (SP + -81)) s6 s7 s8 s9 s10 s11).
      { unfold allocA_frame in *. t4r GEO AFR3 MU35 WM35 ltac:(apply DJ5hi; glia GEO). }
      assert (FR16'5 : rw_cells asegs m5 (STK + -16) [C8 (Z_to_bv 64 SP); C8 (Z_to_bv 64 0x6978c)]) by (t4r GEO FR16'3 MU35 WM35 ltac:(apply DJ5hi; glia GEO)).
      assert (FR7'5 : rw_cells asegs m5 (SP + -56) [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (t4r GEO FR7'3 MU35 WM35 ltac:(apply DJ5hi; glia GEO)).
      assert (STKC5 : rw_cells asegs m5 STK [C8 (Z_to_bv 64 (STK + 16)); C8 (Z_to_bv 64 size)]) by (t4r GEO STKC3 MU35 WM35 ltac:(apply DJ5hi; glia GEO)).
      assert (HTR5 : u64arr asegs m5 (STK + 16) ws) by (eapply u64arr_transport; [exact HTR3| exact MU35| exact WM35| apply DJ5hi; glia GEO]).
      assert (F1800'5 : rw_cells asegs m5 (STK + 256) [CB 1800 fr1]) by (t4r GEO F1800'3 MU35 WM35 ltac:(apply DJ5hi; glia GEO)).
      assert (TFBP'5 : rw_cells asegs m5 (STK + 2056) [C8 (Z_to_bv 64 SP)]) by (t4r GEO TFBP'3 MU35 WM35 ltac:(apply DJ5hi; glia GEO)).
      assert (F8'5 : rw_cells asegs m5 (STK + 2064) [CB 8 fr2]) by (t4r GEO F8'3 MU35 WM35 ltac:(apply DJ5hi; glia GEO)).
      (* [comment removed for export] *)
      assert (SHP25 : rw_cells asegs m5 S2 [CB (Z.to_nat k2) (repeat (Z_to_bv 8 0xfa) (Z.to_nat k2))]) by (t4r GEO SHP2 MU5 WM5 ltac:(clear - GEO; decompose [and] GEO; repeat split; lia)).
      assert (PG5 : exists pg, rw_cells asegs m5 PGS [C1 pg] /\ (qd = q8 -> pg = Z_to_bv 8 0xfa)).
      { destruct (Z_lt_ge_dec qd q8) as [LT|GE].
        - exists pg0. split; [| intros E; exfalso; clear - LT E; lia].
          t4r GEO (PG03 LT) MU35 WM35 ltac:(clear - GEO LT ABAND; decompose [and] GEO; repeat split; lia).
        - assert (EQ : qd = q8) by (clear - GE GEO; decompose [and] GEO; lia).
          exists (Z_to_bv 8 0xfa). split; [| reflexivity].
          pose proof (CB_sub asegs m5 S2 _ _ 0 1 SHP25 ltac:(clear - GEO; decompose [and] GEO; lia)) as P1. rewrite Z.add_0_r in P1.
          rewrite firstn_skipn_repeat in P1 by (clear - GEO; decompose [and] GEO; lia).
          replace S2 with PGS in P1 by (clear - GEO EQ; decompose [and] GEO; lia).
          eapply (rw_cells_reshape asegs _ _ _ _ P1); [cbn; exact (conj I I)| reflexivity]. }
      ddestruct PG5 as (pg5 & PG5 & PG5E).
      (* [comment removed for export] *)
      eapply (evtA_aevtS_KJ AL (CSf sc' r' nb' bl') (K sc' r' nb' bl') _ _ _ mo5 (KL sc' r' nb' bl') HK5); [exact HJ5| |].
      { eapply (ssegC2 AL IMG ALWF (CSf sc' r' nb' bl') (CSOKf sc' r' nb' bl') ASB SP n lo T CTX TID a ms NB32 FP LOIMG SPL SPH SPA16 T0 T1 CX0 CX1 TC A0 AAL eq_refl ACE ABAND ABT ABC TNS CTXNS)
          with (q0 := s0) (q1 := s1) (q2 := s2) (q3 := s3) (q4 := s4) (q5 := s5) (mg0 := mg0) (mg1 := mg1) (pgb := pg5) (size := size) (fr1 := fr1) (fr2 := fr2) (ws := ws)
               (uj := repeat (Z_to_bv 8 0) (Z.to_nat 4096)) (fr0 := fr0) (j0 := j0) (j1 := jj1) (j2 := jj2) (j4 := j4) (b0 := b0) (id := id) (b1 := b1n);
          [ exact IDB' | exact B1B | exact BCS3 | exact AS5 | exact TCS3 | exact CTXCS3 | exact PS5 | exact FS5 | exact GOTFL5 | exact PPART5 | exact HDR5 | exact MG5 | exact PG5 | exact UC5
          | exact STH5 | exact ST45 | exact AFR5 | exact FR16'5 | exact FR7'5 | exact STKC5 | exact HTR5 | exact HL30 | exact F1800'5 | exact TFBP'5 | exact F8'5 | exact ST5 | exact SCS3 | exact MI5 ]. }
      cbn beta. intros ms6 mo6 PO6 HK6 MM6 HJ6. unfold ssegC2_post in PO6.
      ddestruct PO6 as (w0 & w1 & w2' & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4' & w5 & w6 & k0 & k1 & k2' & k4 & m6 & -> & MU6 & WM6 & MI6 & HDR6 & MG6 & PG6 & FILL6 & STH6 & ST46 & ST6).
      change (munch [(lo, SP); (PGS, PGS + 1); (T + 2800, T + 2824); (T + 2904, T + 2912); (UB, UB + 4096); (CHB, CHB + 2); (AB, AB + 16)] m5 m6) in MU6.
      (* [comment removed for export] *)
      set (W36 := [(lo, SP); (CHB + 8, CHB + 16); (S1, S1 + 256); (S2, S2 + k2); (SUB, SUB + qd); (PGS, PGS + 1); (T + 2800, T + 2824); (T + 2904, T + 2912); (UB, UB + 4096); (CHB, CHB + 2); (AB, AB + 16)]).
      set (W46 := [(lo, SP); (SUB, SUB + qd); (PGS, PGS + 1); (T + 2800, T + 2824); (T + 2904, T + 2912); (UB, UB + 4096); (CHB, CHB + 2); (AB, AB + 16)]).
      set (W6 := [(lo, SP); (PGS, PGS + 1); (T + 2800, T + 2824); (T + 2904, T + 2912); (UB, UB + 4096); (CHB, CHB + 2); (AB, AB + 16)]) in MU6.
      assert (MU36 : munch W36 m3 m6).
      { eapply munch_trans. { eapply munch_weaken; [| exact MU35]. unfold W36. ssfp GEO. }
        eapply munch_weaken; [| exact MU6]. unfold W36, W6. ssfp GEO. }
      assert (WM36 : wmono asegs m3 m6) by (eapply wmono_trans; [exact WM35| exact WM6]).
      assert (MU46 : munch W46 m4 m6).
      { eapply munch_trans. { eapply munch_weaken; [| exact MU5]. unfold W46. ssfp GEO. }
        eapply munch_weaken; [| exact MU6]. unfold W46, W6. ssfp GEO. }
      assert (WM46 : wmono asegs m4 m6) by (eapply wmono_trans; [exact WM5| exact WM6]).
      assert (DJ6lo : forall A k, 0x10000 <= A /\ A + k <= 0x65f000 -> disjoint_from W36 A k).
      { intros A k H. unfold W36. cbn [disjoint_from]. clear - H GEO. decompose [and] GEO. repeat split; lia. }
      (* [comment removed for export] *)
      assert (DJblk : forall A k, a <= A -> A + k <= a + ms -> (A + k <= AB \/ (AB + 16 <= A /\ A + k <= CHB) \/ UB + 4096 <= A) -> disjoint_from W36 A k).
      { intros A k Ha Hb Hc. unfold W36. cbn [disjoint_from].
        split; [clear - Ha Hb GEO; decompose [and] GEO; lia|].
        split; [clear - Ha Hb Hc GEO; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABAND; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABAND; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABAND; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABAND; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABT; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABT; decompose [and] GEO; lia|].
        split; [clear - Ha Hb Hc GEO; decompose [and] GEO; lia|].
        split; [clear - Ha Hb Hc GEO; decompose [and] GEO; lia|].
        split; [clear - Ha Hb Hc GEO; decompose [and] GEO; lia| exact I]. }
      assert (DJsha : forall A k, SHA <= A -> A + k <= SHA + 512 -> disjoint_from W36 A k).
      { intros A k Ha Hb. unfold W36. cbn [disjoint_from].
        split; [clear - Ha Hb GEO; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABAND; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABAND TNS; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABAND TNS; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABAND; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABAND; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABAND; decompose [and] GEO; lia| exact I]. }
      assert (DJs1 : disjoint_from W46 S1 256).
      { unfold W46. cbn [disjoint_from].
        split; [clear - GEO; decompose [and] GEO; lia|].
        split; [clear - GEO; decompose [and] GEO; lia|].
        split; [clear - GEO; decompose [and] GEO; lia|].
        split; [clear - GEO ABAND TNS; decompose [and] GEO; lia|].
        split; [clear - GEO ABAND TNS; decompose [and] GEO; lia|].
        split; [clear - GEO ABAND; decompose [and] GEO; lia|].
        split; [clear - GEO ABAND; decompose [and] GEO; lia|].
        split; [clear - GEO ABAND; decompose [and] GEO; lia| exact I]. }
      assert (DJ6sh : forall A k, SUB <= A -> A + k <= SHA + 512 * qm -> (A + k <= PGS \/ PGS + 1 <= A) -> disjoint_from W6 A k).
      { intros A k Ha Hb Hc. unfold W6. cbn [disjoint_from].
        split; [clear - Ha Hb GEO; decompose [and] GEO; lia|].
        split; [exact Hc|].
        split; [clear - Ha Hb GEO ABAND TNS; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABAND TNS; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABAND; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABAND; decompose [and] GEO; lia|].
        split; [clear - Ha Hb GEO ABAND; decompose [and] GEO; lia| exact I]. }
      (* [comment removed for export] *)
      assert (HH6 : rw_cells asegs m6 a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed2 n)); C8 (Z_to_bv 64 ncks)]) by (t7r GEO HH3 MU36 WM36 ltac:(apply DJblk; glia GEO)).
      assert (Z16 : rw_cells asegs m6 (a + 32) [CB (Z.to_nat 4064) (repeat (Z_to_bv 8 0) (Z.to_nat 4064))]) by (t7r GEO Z13 MU36 WM36 ltac:(apply DJblk; glia GEO)).
      assert (Z26 : rw_cells asegs m6 (AB + 16) [CB (Z.to_nat 2016) (repeat (Z_to_bv 8 0) (Z.to_nat 2016))]) by (t7r GEO Z23 MU36 WM36 ltac:(apply DJblk; glia GEO)).
      assert (Z36 : rw_cells asegs m6 (UB + 4096) [CB (Z.to_nat (a + ms - UB - 4096)) (repeat (Z_to_bv 8 0) (Z.to_nat (a + ms - UB - 4096)))]) by (t7r GEO Z33 MU36 WM36 ltac:(apply DJblk; glia GEO)).
      assert (SHH6 : rw_cells asegs m6 SHA [CB 512 (repeat (Z_to_bv 8 250) 512)]) by (t7r GEO SHH3 MU36 WM36 ltac:(apply DJsha; glia GEO)).
      assert (UNW6 : rw_cells asegs m6 (T + 3168) [C1 (Z_to_bv 8 0)]).
      { t7r GEO UNW3 MU36 WM36 ltac:(idtac). unfold W36. cbn [disjoint_from].
        split; [clear - GEO; decompose [and] GEO; lia|].
        split; [clear - GEO ABT; decompose [and] GEO; lia|].
        split; [clear - GEO ABAND TNS; decompose [and] GEO; lia|].
        split; [clear - GEO ABAND TNS; decompose [and] GEO; lia|].
        split; [clear - GEO ABAND TNS; decompose [and] GEO; lia|].
        split; [clear - GEO ABAND TNS; decompose [and] GEO; lia|].
        split; [clear; lia|].
        split; [clear; lia|].
        split; [clear - GEO ABT; decompose [and] GEO; lia|].
        split; [clear - GEO ABT; decompose [and] GEO; lia|].
        split; [clear - GEO ABT; decompose [and] GEO; lia| exact I]. }
      assert (SHP16 : rw_cells asegs m6 S1 [CB 256%nat (repeat (Z_to_bv 8 0xfa) 256%nat)]) by (t7r GEO SHP1 MU46 WM46 ltac:(exact DJs1)).
      assert (SHZ6 : rw_cells asegs m6 SUB [CB (Z.to_nat (rd / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (rd / 8)))]).
      { rewrite RD8 in SHZ |- *. t7r GEO SHZ MU6 WM6 ltac:(apply DJ6sh; glia GEO). }
      assert (SHP26 : rw_cells asegs m6 S2 [CB (Z.to_nat k2) (repeat (Z_to_bv 8 0xfa) (Z.to_nat k2))]).
      { destruct (Z_lt_ge_dec qd q8) as [LT|GE].
        - t7r GEO SHP25 MU6 WM6 ltac:(apply DJ6sh; clear - GEO LT; decompose [and] GEO; lia).
        - assert (EQ : qd = q8) by (clear - GE GEO; decompose [and] GEO; lia).
          (* [comment removed for export] *)
          pose proof (CB_sub asegs m5 S2 _ _ 1 (Z.to_nat (k2 - 1)) SHP25 ltac:(clear - GEO; decompose [and] GEO; lia)) as TL.
          rewrite firstn_skipn_repeat in TL by (clear - GEO; decompose [and] GEO; lia). change (Z.of_nat 1) with 1 in TL.
          assert (TL6 : rw_cells asegs m6 (S2 + 1) [CB (Z.to_nat (k2 - 1)) (repeat (Z_to_bv 8 250) (Z.to_nat (k2 - 1)))])
            by (t7r GEO TL MU6 WM6 ltac:(apply DJ6sh; clear - GEO EQ; decompose [and] GEO; lia)).
          pose proof PG6 as P6. change (rw_cells asegs m6 PGS [C1 (pgv n pg5)]) in P6. rewrite (PG5E EQ) in P6. unfold pgv in P6.
          assert (E8 : (nfix n mod 8 =? 0) = true) by (apply (proj2 (Z.eqb_eq _ _)); clear - GEO EQ; decompose [and] GEO; lia).
          rewrite E8 in P6. clear E8.
          replace PGS with S2 in P6 by (clear - GEO EQ; decompose [and] GEO; lia).
          assert (P6' : rw_cells asegs m6 S2 [CB 1%nat [Z_to_bv 8 250]]) by (eapply (rw_cells_reshape asegs _ _ _ _ P6); [cbn; exact (conj eq_refl I)| reflexivity]).
          pose proof (CB_merge asegs m6 S2 _ _ _ _ P6' TL6) as MRG.
          replace (1 + Z.to_nat (k2 - 1))%nat with (Z.to_nat k2) in MRG by (clear - GEO; decompose [and] GEO; lia).
          replace ([Z_to_bv 8 250] ++ repeat (Z_to_bv 8 250) (Z.to_nat (k2 - 1))) with (repeat (Z_to_bv 8 250) (Z.to_nat k2)) in MRG.
          2:{ replace (Z.to_nat k2) with (S (Z.to_nat (k2 - 1))) by (clear - GEO; decompose [and] GEO; lia). reflexivity. }
          exact MRG. }
      apply aevtS_now. unfold sec_chunk_post.
      eexists. dexists mo6, nb', bl', N', tf', id. dexists w0, w1, w2', wa1, wa2, wa3, wa4, wa5, wa6, wa7, w3, w4', w5, w6. dexists (Z.land b1n 243), pg5, k0, k1, k2', k4, m6.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact HK6|]. split; [exact HJ6|].
      split.
      { eapply (depot_inv_transport _ m3 m6 N' nb' tf' bl' DI3 MU36 WM36 DJ6lo).
        - intros k Hk. pose proof (BNold k T 4096 Hk TCS ltac:(clear; lia) APTn) as Y1. pose proof (BNold k a ms Hk BCS ltac:(glia GEO) APBn) as Y2.
          pose proof (BNsh k SHA (512 * qm) Hk ltac:(clear - GEO ABAND; decompose [and] GEO; lia) ltac:(clear - GEO ABAND; decompose [and] GEO; lia) ltac:(glia GEO)) as Y3.
          pose proof (BN k Hk) as Y5.
          unfold W36. cbn [disjoint_from]. split; [clear - Y5 GEO; decompose [and] GEO; lia|]. split; [clear - Y2 GEO; decompose [and] GEO; lia|].
          split; [clear - Y3 GEO; decompose [and] GEO; lia|]. split; [clear - Y3 GEO; decompose [and] GEO; lia|]. split; [clear - Y3 GEO; decompose [and] GEO; lia|]. split; [clear - Y3 GEO; decompose [and] GEO; lia|].
          split; [clear - Y1 GEO; decompose [and] GEO; lia|]. split; [clear - Y1 GEO; decompose [and] GEO; lia|].
          split; [clear - Y2 GEO; decompose [and] GEO; lia|]. split; [clear - Y2 GEO; decompose [and] GEO; lia|]. split; [clear - Y2 GEO; decompose [and] GEO; lia| exact I].
        - intros j Hj. pose proof (BSold j T 4096 Hj TCS ltac:(clear; lia) APTs) as Y1. pose proof (BSold j a ms Hj BCS ltac:(glia GEO) APBs) as Y2.
          pose proof (BSsh j SHA (512 * qm) Hj ltac:(clear - GEO ABAND; decompose [and] GEO; lia) ltac:(clear - GEO ABAND; decompose [and] GEO; lia) ltac:(glia GEO)) as Y3.
          pose proof (BS j Hj) as Y5.
          unfold W36. cbn [disjoint_from]. split; [clear - Y5 GEO; decompose [and] GEO; lia|]. split; [clear - Y2 GEO; decompose [and] GEO; lia|].
          split; [clear - Y3 GEO; decompose [and] GEO; lia|]. split; [clear - Y3 GEO; decompose [and] GEO; lia|]. split; [clear - Y3 GEO; decompose [and] GEO; lia|]. split; [clear - Y3 GEO; decompose [and] GEO; lia|].
          split; [clear - Y1 GEO; decompose [and] GEO; lia|]. split; [clear - Y1 GEO; decompose [and] GEO; lia|].
          split; [clear - Y2 GEO; decompose [and] GEO; lia|]. split; [clear - Y2 GEO; decompose [and] GEO; lia|]. split; [clear - Y2 GEO; decompose [and] GEO; lia| exact I]. }
      split; [split; [exact NBCS3| exact BLCS3]|].
      split; [eapply (depot_statics_transport _ m3 m6 DST3 MU36); intros A k H; apply DJ6lo; clear - H; lia|].
      split; [exact IDB|]. split; [exact NB'|]. split; [clear - TFB' SZD; lia|]. split; [clear - TFP SZD; lia|]. split; [exact CSM|].
      split; [dexists sn, sb; split; [exact Enb| split; [exact Ebl| split; [exact Fn| exact Fs]]]|].
      assert (MS8 : ms / 8 = 512 * qm) by (clear - GEO; decompose [and] GEO; replace ms with ((512 * qm) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
      split.
      { (* [comment removed for export] *)
        intros x. cbv zeta. intros HO HBn HBs. unfold swin in HO. cbn [outside app] in HO. ddestruct HO as (O1 & O2 & O3 & O4 & O5 & O6 & _).
        rewrite MS8 in O6.
        pose proof (bv_unsigned_in_range 64 x) as XR. unfold bv_modulus in XR. change (2 ^ Z.of_N 64) with (2^64) in XR.
        rewrite (MU6 x).
        2:{ unfold W6. cbn [outside]. split; [exact O1|]. split; [clear - O6 GEO; decompose [and] GEO; lia|]. split; [exact O3|]. split; [exact O4|].
            split; [clear - O5 GEO; decompose [and] GEO; lia|]. split; [clear - O5 GEO; decompose [and] GEO; lia|]. split; [clear - O5 GEO; decompose [and] GEO; lia| exact I]. }
        rewrite (MU5 x).
        2:{ cbn [outside]. split; [clear - O1 GEO; decompose [and] GEO; lia|]. split; [clear - O6 GEO; decompose [and] GEO; lia| exact I]. }
        rewrite (MU4 x).
        2:{ cbn [outside]. split; [clear - O1 GEO; decompose [and] GEO; lia|]. split; [clear - O5 GEO; decompose [and] GEO; lia|].
            split; [clear - O6 GEO; decompose [and] GEO; lia|]. split; [clear - O6 GEO; decompose [and] GEO; lia| exact I]. }
        rewrite (DK3 x). 2:{ clear - O1 GEO XR. decompose [and] GEO. lia. } 2:{ exact O2. } 2:{ exact HBn. } 2:{ exact HBs. }
        apply (MU2 x). cbn [outside]. split; [clear - O1 GEO; decompose [and] GEO; lia|]. split; [clear - O5 GEO; decompose [and] GEO; lia| exact I]. }
      split; [eapply wmono_trans; [exact WM2| eapply wmono_trans; [exact WM3| exact WM36]]|].
      split; [exact MI6|]. split; [exact ST6|].
      split; [exact HH6|]. split; [exact Z16|]. split; [exact MG6|]. split; [exact Z26|]. split; [exact HDR6|].
      split. { rewrite <- Z.land_assoc. change (Z.land 243 3) with 3. exact B1A. }
      split. { apply (land_lt_pow2 b1n 243 8); [exact B1B| clear; lia]. }
      split; [exact FILL6|]. split; [exact Z36|].
      split; [exact SHH6|]. split; [exact SHP16|]. split; [exact SHZ6|]. split; [exact PG6|]. split; [exact SHP26|].
      split; [exact STH6|]. split; [exact ST46|]. exact UNW6.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End SecChunk.

End MallocSec.

End ARUN_1.
