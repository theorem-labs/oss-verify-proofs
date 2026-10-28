(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Export MallocKit_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RMallocKit_B () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RNEED_LOCKS"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RPAGE_SIZE"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "Corelib.Numbers.BinNums.Z"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_areas"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cellval"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cell_read"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.Known"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RGOT_SSP"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RP_1.rrepfoot"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Heap.MallocKit_B.agree_on"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Heap.MallocKit_B.ivs_avoid"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_slot"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.META_SIZE"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_cells"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.put_meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_metas"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.shadow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_shadow"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.sparams"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep_ctx"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.pw"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.active"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.usage"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.b8"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.bounces"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_seq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.ge"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.lr_lo"; "RP_1.rfree_fp"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ctx_head_cells"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.actives"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.usages"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.unmap_seqs"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.bouncess"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ctx_tail_cells"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"].



(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

Section RP_1. Context {hRP : run_params}.
Definition rrepfoot (st : mstate) (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "(0.(1.(2.$3.O1.)(4.O1.(5.$3.+3:0.)))(0.(1.(2.$6.O1.)(4.O1.(5.$6.+4.)))(0.(1.(2.$7.O1.)(4.O1.(5.$7.+1.)))(0.(1.(2.$8.O1.)(4.O1.(5.$8.+8.)))(0.(9.$:.Lak,$:.(9.$;.Lar,$;.(1.(<.(=.$;.)(>.$:.$;.(?.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$;.)(18.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$;.)R2.(19.O2.))(1:.$;.R1.))(1.(2.(1;.O2.R2.)O1.)(4.O1.(5.(1;.O2.R2.)+1000.))))))(0.(9.$:.Lb,$:.(9.$1<.Lgh,$1<.(1.(<.(=.$1<.)(>.$:.$1<.(?.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$1<.)(18.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$1<.)R2.(1=.O2.))(1:.$1<.R1.))(1.(2.(1;.O2.R2.)O1.)(4.O1.(5.(1;.O2.R2.)+9.))))))(0.(9.$11.Lrid,$11.(9.$1>.Lr,$1>.(9.$13.Lv,$13.(1.(<.(=.$1>.)(>.$11.$1>.(?.$11.$12.$16.$1>.)(18.$11.$12.$16.$1>.)R3.(1?.O2.))(1:.$1>.R2.))(1.(<.$20.(21.R2.)$22.)(1.(1.(2.(23.R2.)O1.)(4.O1.(5.(23.R2.)(24.(25.R2.)))))(<.$26.(27.(28.O2.R3.)(29.O1.(23.R2.)))(2:.R1.))))))))(0.(1.(2.$2;.O1.)(4.O1.(5.$2;.+8.)))(1.(2.$2<.O1.)(4.O1.(5.$2<.+8.)))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rrepfoot_ctx st a : RCTX <= a < RCTX + 928 -> rrepfoot st a. Proof. intros; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_mlock st a : RMLOCK <= a < RMLOCK + 4 -> rrepfoot st a. Proof. intros; right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_nl st a : RNEED_LOCKS <= a < RNEED_LOCKS + 1 -> rrepfoot st a. Proof. intros; do 2 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_pgsz st a : RPAGE_SIZE <= a < RPAGE_SIZE + 8 -> rrepfoot st a. Proof. intros; do 3 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_area st a ak ar : (s_areas st) !! ak = Some ar -> conc st ak <= a < conc st ak + 4096 -> rrepfoot st a.
Proof. intros; do 4 right; left. dexists ak, ar. auto. Qed.
#[using="Type"] Lemma rrepfoot_group st a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> rrepfoot st a.
Proof. intros; do 5 right; left. dexists b, gh. auto. Qed.
#[using="Type"] Lemma rrepfoot_known st a rid r v : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "P,(<.(=.$1>.)(>.$11.$1>.(?.$11.$12.$16.$1>.)(18.$11.$12.$16.$1>.)O3.(1?.O5.))(1:.$1>.O2.))P,(<.$20.(21.O2.)$22.)P,(1.(2.(23.O2.)O4.)(4.O4.(5.(23.O2.)(24.(25.O2.)))))P,(<.$26.(27.(28.O5.O3.)(29.O4.(23.O2.)))(2:.O1.))(2=.O5.O4.)")
(* [comment removed for export] *).
Proof. intros; do 6 right; left. dexists rid, r, v. auto. Qed.
#[using="Type"] Lemma rrepfoot_got st a : RGOT_SSP <= a < RGOT_SSP + 8 -> rrepfoot st a. Proof. intros; do 7 right; left; assumption. Qed.
#[using="Type"] Lemma rrepfoot_guard st a : RSSP_GUARD <= a < RSSP_GUARD + 8 -> rrepfoot st a. Proof. intros; do 8 right; assumption. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L23517522163.1100000;S1A2bs1i2Hi". (* [comment removed for export] *)
#[using="Type"] Lemma rbytes_at_agree : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pm,P,(2>.&40.)(=.(2>.&8.))Pm',P,(2>.&40.)(=.(2>.&8.))PA,$13.Pbs,(2?.(2>.&8.))P,(30.$31.R4.R2.R1.)P,(32.R5.R4.R3.(33.(34.(2>.&8.)R2.)))(30.$31.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  (intros m m' A bs dd_H; ddestruct dd_H as (H0 & H1 & HB); intros AG). split; [exact H0|]. split; [exact H1|].
  intros i Hi. unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma rrw_cells_agree : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pm,P,(2>.&40.)(=.(2>.&8.))Pm',P,(2>.&40.)(=.(2>.&8.))PA,$13.Pcs,(2?.$35.)P,(36.$31.R4.R2.R1.)P,(32.R5.R4.R3.(33.(37.R2.)))P,(38.$31.R6.R5.)(36.$31.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros m m' A cs [[Hwf HB] HW] AG WM. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply wr_at_transport; eauto.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L47196855304.9000004S2ws". (* [comment removed for export] *)
#[using="Type"] Lemma ru64arr_agree : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pm,P,(2>.&40.)(=.(2>.&8.))Pm',P,(2>.&40.)(=.(2>.&8.))PA,$13.Pws,(2?.(2>.&40.))P,(39.$31.R4.R2.R1.)P,(32.R5.R4.R3.(3:.+8.(33.(34.(2>.&40.)R2.))))P,(38.$31.R6.R5.)(39.$31.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros m m' A ws [HB HW] AG WM. split; [|eapply wr_at_transport; eauto].
  eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma ru8arr_agree : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pm,P,(2>.&40.)(=.(2>.&8.))Pm',P,(2>.&40.)(=.(2>.&8.))PA,$13.Pbs,(2?.(2>.&8.))P,(3;.$31.R4.R2.R1.)P,(32.R5.R4.R3.(33.(34.(2>.&8.)R2.)))P,(38.$31.R6.R5.)(3;.$31.R6.R5.R4.)")
(* [comment removed for export] *).
Proof. intros m m' A bs [HB HW] AG WM. split; [eapply rbytes_at_agree; eauto| eapply wr_at_transport; eauto]. Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00G0?L1312051727.25 L18104250403.35L18104250919.34L19620994688.34L24931798969.25L303848473.34  L3040130149.29 L30494598123.34L31437111947.37L32402591257.34L35969486425.36L37856360665.27L50731377792.34L51483110553.27L52579481817.27L54979511433.27L55122877322.37L59760467673.27L60754081408.34L6086798976.34 L66541521899.34L68233492044.29L68233492044.3100000900:00;00N00W00j01401G01W01j02K02Q02g02m03303903F03L03b04804K04V04fS1A2cs2H0FFS2st2L12L22L32L42B2S1A2cs2H0S2st2L12L22L32L42B5S2st1b1a1HS2st2L12L22L32L42B3S1r1o2Ho2B11a2HaS2st2L12L22L32L42B4S2st2L12L22L32L41a2Ha2B22B32B42B5S1a2HaS2st2L12L22L32L42B22B5S1a2HaS1a2HaS1a2HaS1r1o2B11a2HaS1a2HaS2st2L12L22L32L42B22B3S2st2L12L22L32L42B22B4S2st2L12L22L32L42B2S2st2ak1a1HS2st2ak1k2Hk1a1H". (* [comment removed for export] *)
#[using="Type"] Lemma rmrep_transport_unowned : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pst,$3<.Pm,P,(2>.&40.)(=.(2>.&8.))Pm',P,(2>.&40.)(=.(2>.&8.))PW,(2?.$3=.)P,(3>.VhRP,R4.R3.)P,(3?.R2.R4.R3.)P,(38.$31.R5.R4.)P,(40.R4.(2=.R7.))(3>.VhRP,R8.R6.)")
(* [comment removed for export] *).
Proof.
  (intros st m m' W dd_H; ddestruct dd_H as (WF & CX & GL & AR & GR & SH); intros MU WM HW).
  dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  assert (TC : forall A cs, rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells rsegs m' A cs).
  { intros A cs H HP. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree; eauto. eapply munch_agree; eauto; lia. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - ddestruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    pose proof (u64arr_bound rsegs m _ _ C2) as B2. pose proof (u64arr_bound rsegs m _ _ C3) as B3.
    pose proof (u8arr_bound rsegs m _ _ C4) as B4. pose proof (u8arr_bound rsegs m _ _ C5) as B5.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
    + eapply ru64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L1 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru64arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L2 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L3 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree; eauto. eapply munch_agree; eauto; rewrite ?L4 in *; try lia. intros a Ha. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + apply TC; [exact C6 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
  - ddestruct GL as (G1 & G2 & G3 & G4 & G5). split; [|split; [|split; [|split]]].
    + apply TC; [exact G1 |]. intros a Ha. apply rrepfoot_mlock. cbn in Ha. unfold RMLOCK in *. lia.
    + apply TC; [exact G2 |]. intros a Ha. apply rrepfoot_nl. cbn in Ha. unfold RNEED_LOCKS in *. lia.
    + apply TC; [exact G3 |]. intros a Ha. apply rrepfoot_pgsz. cbn in Ha. unfold RPAGE_SIZE in *. lia.
    + apply TC; [exact G4 |]. intros a Ha. apply rrepfoot_got. cbn in Ha. unfold RGOT_SSP in *. lia.
    + apply TC; [exact G5 |]. intros a Ha. apply rrepfoot_guard. cbn in Ha. unfold RSSP_GUARD in *. lia.
  - intros ak ar Ha. ddestruct (AR ak ar Ha) as (A1 & A2 & A3).
    split; [|split].
    + apply TC; [exact A1 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
    + intros k Hk. apply TC; [apply A2; exact Hk |]. unfold meta_cells; cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. intros a H. eapply rrepfoot_area; [exact Ha|lia].
    + apply TC; [exact A3 |]. intros a H. cbn in H. eapply rrepfoot_area; [exact Ha|lia].
  - intros b gh Hb. ddestruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R |]. intros a H. cbn in H. eapply rrepfoot_group; [exact Hb|lia].
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. split.
    + eapply wr_at_transport; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      dpose Bt as (B0 & B1 & _). cbn in B1.
      eapply rbytes_at_agree; [exact Bt|]. eapply munch_agree; eauto; cbn; try lia. intros a Ha.
      eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00H0?L17223904932.61L19816989356.56L24571379557.63L24659912208.51L25251903056.51L25291224592.51L31509349922.63L31509386111.61L33438641680.51L34044591788.56L38783692830.59L38784077092.62L41343950617.50L45862088364.56L55355253921.56L56253777750.58L56253777750.63L56934558961.63L57830926807.59L62901194256.51L65998309634.63L67469375655.58L8773343404.56 L9530271404.56 00000B01=01d02S03B04104`05@05o06j07`08P08g09b0:]0;90;V0<30<C0=20=^0>:0?50@0S1a2ra4Sa0'2k'3Hk'S2st1g1a1k2Hk2ra2Ca3Sa03Sa13SaL3RB04RBAL2HG3DRa2L12L22L32L4S1a1k2Hk2ra3Sa03RB02r'1o2Ho1H2H13Sa12H0S2st1g1a1k2Hk2ra2Ca3Sa03Sa13SaL3RB04RBAL2HG3DRaS2st1g1a1k2Hk2ra2Ca3Sa03Sa13SaL3RB04RBAL2HG3DRaS2st1g1a1k2Hk2ra2Ca3Sa03Sa13SaL3RB04RBAL2HG3DRaS1a1k2Hk2ra3Sa03Sa13RB03DRa2a'4Sa0'1E2PG2k03Hk0S1a1k2ra3Sa13RB03DRa4Sa0'2k'3NEkS2st1g1a1k2Hk2ra2Ca3Sa03Sa13SaL3RB04RBAL2HG3DRaS2st1g1a1k2Hk2ra2Ca3Sa03Sa13SaL3RB04RBAL2HG3DRa2L12L22L32L4S1a1k2Hk2ra3Sa03Sa13SaL3RB03DRa2a'4Sa0'4Sa1'4SaL'1E2PGS1a1k2Hk2ra3Sa03RB02a'3ra'4Sa0'4Sa1'1H2H13Sa12H0S2st1g1a2ra3Sa01A2cs2HDS2st1g1a1k2Hk2ra2Ca3Sa03Sa13SaL3RB04RBAL2HG3DRa2L12L22L32L4S2st1g1a1k2Hk2ra2Ca3Sa03Sa13SaL3RB04RBAL2HG3DRa2L12L22L32L4S2st1g1a1k2Hk2ra3RB02HG4Sa0'S2st1g1a2ra3Sa02a'4Sa0'2PG2DDS2st1g1a2ra3Sa02a'4Sa0'2PG2DDS2st1a1k2ra4Sa0'S2st1g1a1k2Hk2ra2Ca3Sa03Sa13SaL3RB04RBAL2HG3DRaS1a1k2Hk2ra3Sa03RB01b2rb3Sb11H2H13Sa13Sb02H0S2st1g1a1k2Hk2ra3RB02HG4Sa0'S2st1g1a1k2Hk2ra2Ca3Sa03Sa13SaL3RB04RBAL2HG3DRa2L12L22L32L4S2st1g1a1k2Hk2ra2Ca3Sa03Sa13SaL3RB04RBAL2HG3DRa2L12L22L32L4". (* [comment removed for export] *)
#[using="Type"] Lemma rmrep_put_meta_frame : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pst,$3<.Pm,P,(2>.&40.)(=.(2>.&8.))Pm',P,(2>.&40.)(=.(2>.&8.))Pg,$:.Pmr',$41.P,(3>.VhRP,R5.R4.)P,(42.R6.R3.)P,(3?.(43.(44.$13.$13.)(45.$13.$13.(1;.R7.R4.)(5.(1;.R7.R4.)$46.))(47.(44.$13.$13.)))R6.R5.)P,(38.$31.R7.R6.)P,(36.$31.R7.(1;.R9.R6.)(48.R9.R5.))(3>.VhRP,(49.R7.R6.R:.)R8.)")
(* [comment removed for export] *).
Proof.
  (intros st m m' g mr' MR dd_H; ddestruct dd_H as (a & ar & k & Ha & Hk & Eg); intros MU WM CH).
  dpose MR as (WF & CX & GL & AR & GR & SH).
  ddestruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). rceilb.
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  ddestruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RFa). destruct (rreserved_disjoint _ _ RFa) as [_ DRa].
  pose proof (round_up_pg_ge (r_len ra)) as RU.
  (* [comment removed for export] *)
  assert (Hconc : forall q, conc (put_meta g mr' st) q = conc st q) by (intros; reflexivity).
  assert (Hpw : forall q, pw (put_meta g mr' st) q = pw st q) by (intros [q|]; reflexivity).
  assert (Hmc : forall mr, meta_cells (put_meta g mr' st) mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
  assert (TC : forall A cs, rw_cells rsegs m A cs ->
            (A + Z.of_nat (cells_size cs) <= conc st g \/ conc st g + 40 <= A) -> rw_cells rsegs m' A cs).
  { intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
  split; [|split; [|split; [|split; [|split]]]].
  - exact WF.
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|].
    ddestruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx. unfold RCTX in *.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 | cbn; lia].
    + eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L1. split; [lia|exact I].
    + eapply u64arr_transport; eauto. cbn [disjoint_from]. rewrite L2. split; [lia|exact I].
    + eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L3. split; [lia|exact I].
    + eapply u8arr_transport; eauto. cbn [disjoint_from]. rewrite L4. split; [lia|exact I].
    + apply TC; [exact C6 | cbn; lia].
  - ddestruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]]; (apply TC; [assumption | cbn; lia]).
  - intros a' ar' Ha'. cbn in Ha'.
    ddestruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
    destruct (decide (a' = a)) as [->|NEa].
    + rewrite Ha in Ha'. inversion Ha'; subst ar'.
      ddestruct (AR a ar Ha) as (HD & SL & PD). unfold rarea_rep. rewrite !Hconc, Hpw.
      split; [|split].
      * apply TC; [exact HD| cbn; lia].
      * intros k' Hk'. rewrite Hmc, get_meta_rec_put.
        destruct (Z.eq_dec k' k) as [->|NEk].
        -- rewrite <- Eg, aptr_eqb_refl.
           replace (conc st a + 24 + 40 * k) with (conc st g) by (rewrite HG; lia). exact CH.
        -- replace (aptr_eqb (aadd a (24 + 40 * k')) g) with false.
           2:{ symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn. rewrite N.eqb_refl. cbn. apply Z.eqb_neq. lia. }
           apply TC; [apply SL; lia|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE. nia.
      * apply TC; [exact PD| cbn; lia].
    + assert (PG : fst a' <> fst a \/ (fst a' = fst a /\ (snd a' + 4096 <= snd a \/ snd a + 4096 <= snd a'))).
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE]; [right|left; exact NE]. split; [exact E|].
        assert (snd a' <> snd a) by (intros E2; apply NEa; destruct a, a'; cbn in *; congruence).
        Z.div_mod_to_equations. nia. }
      assert (DD : conc st a' + 4096 <= conc st g \/ conc st g + 40 <= conc st a').
      { rewrite Ca', HG, Ca. destruct PG as [NE|[E PG]].
        - pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
          destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NE); lia.
        - rewrite E, Hra in Hra'. inversion Hra'; subst ra'. lia. }
      eapply rarea_rep_ext; [exact Hconc| |].
      { intros k0 Hk0. rewrite get_meta_rec_put. unfold AREA_HDR, META_SIZE, NSLOTS in *.
        replace (aptr_eqb (aadd a' (24 + 40 * k0)) g) with false; [reflexivity|].
        symmetry. rewrite Eg. unfold aptr_eqb, aadd. cbn [fst snd].
        destruct PG as [NE|[E PG]].
        - rewrite (proj2 (N.eqb_neq _ _) NE). reflexivity.
        - rewrite E, N.eqb_refl. cbn [andb]. apply Z.eqb_neq. lia. }
      ddestruct (AR a' ar' Ha') as (HD & SL & PD). split; [|split].
      * apply TC; [exact HD| cbn; lia].
      * intros k0 Hk0. apply TC; [apply SL; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length]. unfold AREA_HDR, META_SIZE, NSLOTS in *. nia.
      * apply TC; [exact PD| cbn; lia].
  - intros b gh Hb. cbn in Hb. eapply rgroup_rep_ext; [exact Hconc|].
    ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
    ddestruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    apply TC; [exact R|]. cbn. rewrite Cb, HG, Ca.
    assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; inversion Hrb; subst; congruence).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Kb).
    destruct (DJ (fst b) rb (fst a) ra Hrb Hra NE); lia.
  - intros rid r' Hr' Hk'. cbn in Hr'. eapply rshadow_rep_ext; [reflexivity|].
    destruct (SH rid r' Hr' Hk') as [HWr HB]. split; [eapply wr_at_transport; eauto|].
    intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
    eapply bytes_at_transport; eauto. cbn. split; [|exact I].
    assert (NE : rid <> fst a) by (intros E; subst; rewrite Hra in Hr'; inversion Hr'; subst; congruence).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r' Hk').
    rewrite HG, Ca. destruct (DJ rid r' (fst a) ra Hr' Hra NE); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L18426566819.44L2542034953.49 L26226655310.34L27551908512.48L42067209294.34L5285554022.49 L54232856654.34L54521438190.34L55032941733.33L60297354089.51L6225712206.34 00000:00^00_01501601Z01[01\01e02N02OS1r1D1o2HoS2st2ak2ra2Ca3Sa03Sa13SaL3RB04RBAL1DSS2st1b2rb2Cb3Sb03Sb11DSS2st2ak2ra2Ca3Sa03Sa13SaL3RB04RBAL1DSSS1A2cs2HDS2st2ak2ra2Ca3Sa03Sa13SaL3RB04RBAL1D1k2HkS". (* [comment removed for export] *)
#[using="Type"] Lemma rmrep_ctx_frame' : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pst,$3<.Pst',$3<.Pm,P,(2>.&40.)(=.(2>.&8.))Pm',P,(2>.&40.)(=.(2>.&8.))P,(3>.VhRP,R4.R2.)P,(3?.(43.(44.$13.$13.)(45.$13.$13.$3.(5.$3.+3:0.))(47.(44.$13.$13.)))R3.R2.)P,(38.$31.R4.R3.)P,(<.(?.$11.$12.$16.$1>.)(1?.R6.)(1?.R7.))P,(<.(?.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$41.)(4:.R7.)(4:.R8.))P,(<.(?.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$;.)(19.R8.)(19.R9.))P,(<.(?.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$1<.)(1=.R9.)(1=.R:.))P,(<.(?.$11.$12.$16.$4;.)(4<.R:.)(4<.R;.))P,(<.(44.(44.(44.(2?.(44.$13.$13.))$13.)$13.)$13.)(4=.R;.)(4=.R<.))P,(4>.R<.R:.)(3>.VhRP,R=.R;.)")
(* [comment removed for export] *).
Proof.
  (intros st st' m m' dd_H; ddestruct dd_H as (WF & CX & GL & AR & GR & SH); intros MU WM ER EM EA EG ES ERs CX').
  dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  assert (Hgm : forall q, get_meta_rec st' q = get_meta_rec st q) by (intros q; unfold get_meta_rec; rewrite EM; reflexivity).
  assert (Hsh : forall rid, get_shadow st' rid = get_shadow st rid) by (intros rid; unfold get_shadow; rewrite ES; reflexivity).
  assert (TC : forall A cs, rw_cells rsegs m A cs -> (A + Z.of_nat (cells_size cs) <= RCTX \/ RCTX + 928 <= A) -> rw_cells rsegs m' A cs).
  { intros A cs H HD. eapply rw_cells_transport; eauto. cbn. split; [lia|exact I]. }
  unfold RCTX in *.
  split; [|split; [exact CX'|split; [|split; [|split]]]].
  - destruct WF as [RP0 WF']. split; [exact (rparams_ok_same _ _ RP0 ERs)|]. rewrite ER, EA, EG. exact WF'.
  - ddestruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]]; (apply TC; [assumption | cbn; lia]).
  - intros ak ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply Hgm |].
    ddestruct (rarea_conc st ak ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    ddestruct (WR (fst ak) ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    pose proof (round_up_pg_ge (r_len ra)).
    ddestruct (AR ak ar Ha) as (A1 & A2 & A3). split; [|split].
    + apply TC; [exact A1| cbn; lia].
    + intros k Hk. apply TC; [apply A2; exact Hk|]. unfold meta_cells, AREA_HDR, META_SIZE, NSLOTS in *. cbn [cells_size csize Nat.add length]. lia.
    + apply TC; [exact A3| cbn; lia].
  - intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc|].
    ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
    ddestruct (WR (fst b) rb Hrb) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    pose proof (round_up_pg_ge (r_len rb)).
    ddestruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8]. apply TC; [exact R| cbn; lia].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply Hsh|].
    ddestruct (WR rid r Hr) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [_ D].
    destruct (SH rid r Hr Hk) as [HWr HB]. split; [eapply wr_at_transport; eauto|].
    intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
    eapply bytes_at_transport; eauto. cbn. split; [lia|exact I].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rmrep_del_group : forall st m p, rmrep st m -> rmrep (del_group p st) m.
Proof.
  (intros st m p dd_H; ddestruct dd_H as (WF & CX & GL & AR & GR & SH)). dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  assert (Hconc : forall q, conc (del_group p st) q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - split; [exact (conj Hres RPHres)|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
    intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb]. exact (WG b gh Hb).
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX].
  - intros a ar Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
  - intros b gh Hb. cbn in Hb. apply lookup_delete_Some in Hb. destruct Hb as [_ Hb].
    eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)].
  - intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.

#[using="Type"] Lemma rmrep_set_slots : forall st m v, rmrep st m -> rmrep (set_slots v st) m.
Proof.
  (intros st m v dd_H; ddestruct dd_H as (WF & CX & GL & AR & GR & SH)).
  assert (Hconc : forall q, conc (set_slots v st) q = conc st q) by (intros; reflexivity).
  split; [exact WF|]. split; [|split; [exact GL|split; [|split]]].
  - eapply rmrep_ctx_ext; [reflexivity|exact Hconc|exact CX].
  - intros a ar Ha. eapply rarea_rep_ext; [exact Hconc|intros; reflexivity|exact (AR a ar Ha)].
  - intros b gh Hb. eapply rgroup_rep_ext; [exact Hconc|exact (GR b gh Hb)].
  - intros rid r Hr Hk. eapply rshadow_rep_ext; [reflexivity|exact (SH rid r Hr Hk)].
Qed.

#[using="Type"] Lemma rmrep_del_slots : forall st m p s c, rmrep st m -> rmrep (del_slots p s c st) m.
Proof. intros. rewrite del_slots_eq. apply rmrep_set_slots. assumption. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L10248723314.6000008S2sc3Hsc". (* [comment removed for export] *)
#[using="Type"] Lemma rmrep_active_read : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pst,$3<.Pm,P,(2>.&40.)(=.(2>.&8.))Psc,$13.Pa,(2>.&40.)P,(3>.VhRP,R4.R3.)P,(1.(2.=R3.)(4.R3.+30.))P,(<.(2>.&40.)R3.(4?.(5.(5.$3.+50.)(3:.+8.R4.))))(<.(=.(2?.(2>.&8.)))(50.$31.R6.R4.#8.)(1:.(2?.(2>.&8.))(51.(52.R7.(53.R7.R5.)))))")
(* [comment removed for export] *).
Proof.
  (intros st m sc a dd_H; ddestruct dd_H as (_ & (_ & C2 & _) & _); intros Hsc ->).
  eapply u64arr_read; [exact C2 | apply actives_nth; exact Hsc | lia | reflexivity].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L10248723314.6000008S2sc3Hsc". (* [comment removed for export] *)
#[using="Type"] Lemma rmrep_usage_read : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pst,$3<.Pm,P,(2>.&40.)(=.(2>.&8.))Psc,$13.Pa,(2>.&40.)P,(3>.VhRP,R4.R3.)P,(1.(2.=R3.)(4.R3.+30.))P,(<.(2>.&40.)R3.(4?.(5.(5.$3.+1=0.)(3:.+8.R4.))))(<.(=.(2?.(2>.&8.)))(50.$31.R6.R4.#8.)(1:.(2?.(2>.&8.))(51.(54.(55.R7.R5.)))))")
(* [comment removed for export] *).
Proof.
  (intros st m sc a dd_H; ddestruct dd_H as (_ & (_ & _ & C3 & _) & _); intros Hsc ->).
  eapply u64arr_read; [exact C3 | apply usages_nth; exact Hsc | lia | reflexivity].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L10351595562.6000006S1i2Hi". (* [comment removed for export] *)
#[using="Type"] Lemma rmrep_bounces_read : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pst,$3<.Pm,P,(2>.&40.)(=.(2>.&8.))Pi,$13.Pa,(2>.&40.)P,(3>.VhRP,R4.R3.)P,(1.(2.=R3.)(4.R3.+20.))P,(<.(2>.&40.)R3.(4?.(5.(5.$3.+370.)R4.)))(<.(=.(2?.(2>.&8.)))(50.$31.R6.R4.#1.)(1:.(2?.(2>.&8.))(43.(2>.&8.)(56.(57.R7.R5.))(47.(2>.&8.)))))")
(* [comment removed for export] *).
Proof.
  (intros st m i a dd_H; ddestruct dd_H as (_ & (_ & _ & _ & _ & C5 & _) & _); intros Hi ->).
  eapply u8arr_read; [exact C5 | apply bouncess_nth; exact Hi | lia | reflexivity].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma rmrep_seq_read : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pst,$3<.Pm,P,(2>.&40.)(=.(2>.&8.))Pa,(2>.&40.)P,(3>.VhRP,R3.R2.)P,(<.(2>.&40.)R2.(4?.(5.$3.+390.)))(<.(=.(2?.(2>.&8.)))(50.$31.R4.R3.#1.)(1:.(2?.(2>.&8.))(43.(2>.&8.)(56.(58.(59.R5.)))(47.(2>.&8.)))))")
(* [comment removed for export] *).
Proof.
  (intros st m a dd_H; ddestruct dd_H as (_ & (_ & _ & _ & _ & _ & C6) & _); intros ->).
  apply (rw_cells_read_at rsegs m _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 _ C6); reflexivity.
Qed.


(* [comment removed for export] *)


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L2357606288.29 L27249943637.29L30048841659.29L31686385710.29L44354542148.2900000L01201E01^02=S1a1k2Hk2ra3Sa03SaL3RB04RBALS1a1k2Hk2ra3Sa03Sa13SaL3RB04RBAL2D12D2S1a1k2Hk2ra3Sa03RB0S1a1k2ra3Sa03SaL3RB04RBALS3hRP1a1k2Hk2ra3Sa03Sa13RB03RBC". (* [comment removed for export] *)
#[using="Type"] Lemma rmeta_slot_bounds : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pst,$3<.Pm,P,(2>.&40.)(=.(2>.&8.))Pg,$:.P,(3>.VhRP,R3.R2.)P,(42.R4.R2.)(1.(4.=(1;.R5.R3.))(1.(2.(5.(1;.R5.R3.)+28.)(5:.VhRP,))(1.(0.(2.(5.(1;.R5.R3.)+28.)+10000.)(2.+7>000.(1;.R5.R3.)))(1.(<.$13.(5;.(1;.R5.R3.)+4.)=)(5<.(5;.(1;.R5.R3.)+1000.)+18.)))))")
(* [comment removed for export] *).
Proof.
  (intros st m g MR dd_H; ddestruct dd_H as (a & ar & k & Ha & Hk & Eg)). pose proof MR as (WF & _). dpose WF as (_ & WR & _).
  ddestruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  ddestruct (WR (fst a) ra Hra) as (_ & _ & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  rceilb; unfold AREA_HDR, META_SIZE, NSLOTS in *. pose proof (round_up_pg_ge (r_len ra)).
  rewrite HG, Ca. repeat split; first [lia | Z.div_mod_to_equations; nia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L25040091076.24L28104341973.24L48094838382.24L60158501109.2400000I00h01=01JS3hRP1b1r3Sb03Sb13RB03RBCS1b1r3Sb03Sb13SbA3RB03RAL2D12D2S1b1r3Sb03SbA3RB03RALS1b1r3Sb03RB0". (* [comment removed for export] *)
#[using="Type"] Lemma rgroup_bounds : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pst,$3<.Pm,P,(2>.&40.)(=.(2>.&8.))Pb,$:.Pgh,$1<.P,(3>.VhRP,R4.R3.)P,(<.(=.$1<.)(>.$:.$1<.(?.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$1<.)(18.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$1<.)R3.(1=.R5.))(1:.$1<.R2.))(1.(2.=(1;.R6.R4.))(1.(2.(5.(1;.R6.R4.)+10.)(5:.VhRP,))(1.(0.(2.(5.(1;.R6.R4.)+10.)+10000.)(2.+7>000.(1;.R6.R4.)))(<.$13.(5;.(1;.R6.R4.)+10.)=))))")
(* [comment removed for export] *).
Proof.
  intros st m b gh MR Hb. pose proof MR as (WF & _). dpose WF as (_ & WR & _).
  ddestruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & Sb0 & Sb1 & SbA & RB0 & RBC).
  ddestruct (WR (fst b) r Hr) as (_ & RAL & _ & _ & RF). destruct (rreserved_disjoint _ _ RF) as [D1 D2].
  rceilb. pose proof (round_up_pg_ge (r_len r)).
  rewrite Cb. repeat split; try lia. all: apply base16_mod; assumption.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition rfree_fp (st : mstate) (lo sp : Z) (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "(0.(0.(1.(2.O3.O1.)(4.O1.O2.))(0.(1.(2.$3.O1.)(4.O1.(5.$3.+3:0.)))(9.$11.Lrid,$11.(9.$1>.Lr,$1>.(1.(<.(=.$1>.)(>.$11.$1>.(?.$11.$12.$16.$1>.)(18.$11.$12.$16.$1>.)R2.(1?.O4.))(1:.$1>.R1.))(1.(5=.(<.$20.(21.R1.)$22.))(1.(2.(5>.R1.)O1.)(4.O1.(5.(23.R1.)(24.(25.R1.)))))))))))(0.(9.$:.Lb,$:.(9.$1<.Lgh,$1<.(1.(<.(=.$1<.)(>.$:.$1<.(?.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$1<.)(18.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$1<.)R2.(1=.O4.))(1:.$1<.R1.))(1.(2.(1;.O4.R2.)O1.)(4.O1.(5.(1;.O4.R2.)+8.))))))(9.$11.Lrid,$11.(9.$1>.Lr,$1>.(9.$13.Lv,$13.(1.(<.(=.$1>.)(>.$11.$1>.(?.$11.$12.$16.$1>.)(18.$11.$12.$16.$1>.)R3.(1?.O4.))(1:.$1>.R2.))(1.(<.$20.(21.R2.)$22.)(1.(1.(2.(23.R2.)O1.)(4.O1.(5.(23.R2.)(24.(25.R2.)))))(<.$26.(27.(28.O4.R3.)(29.O1.(23.R2.)))(2:.R1.))))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rfree_fp_stack st lo sp a : lo <= a < sp -> rfree_fp st lo sp a.
Proof. intros; left; left; assumption. Qed.
#[using="Type"] Lemma rfree_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> rfree_fp st lo sp a.
Proof. intros; left; right; left; assumption. Qed.
#[using="Type"] Lemma rfree_fp_region st lo sp a rid r : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "P,(<.(=.$1>.)(>.$11.$1>.(?.$11.$12.$16.$1>.)(18.$11.$12.$16.$1>.)O2.(1?.O6.))(1:.$1>.O1.))P,(5=.(<.$20.(21.O1.)$22.))P,(1.(2.(5>.O1.)O3.)(4.O3.(5.(23.O1.)(24.(25.O1.)))))(5?.O6.O5.O4.O3.)")
(* [comment removed for export] *).
Proof. intros; left; right; right. dexists rid, r. auto. Qed.
#[using="Type"] Lemma rfree_fp_group st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 8 -> rfree_fp st lo sp a.
Proof. intros; right; left. dexists b, gh. auto. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L56475171189.2800000ZS2st1q1a2ar1k2Hk2Ha2ra2Ca3Sa03Sa13RB02HG1H". (* [comment removed for export] *)
#[using="Type"] Lemma rfree_fp_meta : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pst,$3<.Pm,P,(2>.&40.)(=.(2>.&8.))Plo,$13.Psp,$13.Pq,$:.Pa,$13.P,(3>.VhRP,R6.R5.)P,(42.R7.R3.)P,(1.(2.(1;.R8.R4.)R3.)(4.R3.(5.(1;.R8.R4.)+28.)))(5?.R9.R7.R6.R4.)")
(* [comment removed for export] *).
Proof.
  (intros st m lo sp q a MR dd_H; ddestruct dd_H as (ar & arr & k & Har & Hk & Eq); intros Ha). pose proof MR as (WF & _).
  ddestruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
  pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  eapply rfree_fp_region; [exact Hra | exact NK | lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L12574408705.1300000BS2lo2sp3sp'1a2HS1H". (* [comment removed for export] *)
#[using="Type"] Lemma rfree_fp_mono : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Pst,$3<.Pst',$3<.Plo,$13.Psp,$13.Psp',$13.Pa,$13.P,(<.(?.$11.$12.$16.$1>.)(1?.R5.)(1?.R6.))P,(<.(?.$11.$12.$16.$4;.)(4<.R6.)(4<.R7.))P,Pb,$:.Pgh,$1<.P,(<.(=.$1<.)(>.$:.$1<.(?.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$1<.)(18.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$1<.)R2.(1=.R9.))(1:.$1<.R1.))(<.(=.$1<.)(>.$:.$1<.(?.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$1<.)(18.$:.(10.$11.$12.$13.$14.)(15.$11.$12.$16.$13.$14.$17.)$1<.)R3.(1=.R;.))(1:.$1<.R2.))P,(2.R5.R6.)P,(5?.R9.R8.R6.R5.)(5?.R;.R9.R8.R6.)")
(* [comment removed for export] *).
Proof.
  intros st st' lo sp sp' a ER ES HG HS H.
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H |].
    right; right. ddestruct H as (rid & r & H1 & H2 & H3). dexists rid, r. rewrite <- ER. auto.
  - right; left. ddestruct H as (b & gh & H1 & H2). dexists b, gh. rewrite <- Hconc. auto.
  - right; right. ddestruct H as (rid & r & v & H1 & H2 & H3 & H4). dexists rid, r, v.
    rewrite <- ER. unfold get_shadow. rewrite <- ES. auto.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma rpres_except_of_munch' : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "PC,Px,$13.SpPW,(2?.$3=.)Pm,P,(2>.&40.)(=.(2>.&8.))Pm',P,(2>.&40.)(=.(2>.&8.))P,(3?.R3.R2.R1.)P,(38.$31.R3.R2.)P,Plo,$13.Phi,$13.P,(60.(44.$13.$13.)(45.$13.$13.R2.R1.)R7.)Px,$13.P,(1.(2.R4.R1.)(4.R1.R3.))A1.R;.R2.(61.R7.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros C W m m' MU WM HW. eapply rpres_except_of_munch; [exact MU | exact WM |].
  intros a _ HC. eapply outside_of_cover; eauto.
Qed.

#[using="Type"] Lemma rpres_except_of_munch_cov : forall C W m m',
  munch W m m' -> wmono rsegs m m' -> ivs_covered C W -> rpres_except C m m'.
Proof. intros. eapply rpres_except_of_munch'; eauto. apply ivs_covered_In. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MR : rmrep st m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono rsegs m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : sparams st' = sparams st.   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis WIN : forall lo hi, In (lo, hi) W -> RCTX <= lo /\ hi <= RCTX + 928.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L53507296417.12L56765667309.2300000E00US2lo2hi1A1n2HD1a2Ha1HS1A1n2HA2HB1a2Ha". (* [comment removed for export] *)
#[using="MU WIN"] Lemma rctxW_avoid : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "PA,$13.Pn,$13.P,(0.(0.(2.(5.R2.R1.)$3.)(2.(5.$3.+3:0.)R2.))Plo,$13.Phi,$13.P,(60.(44.$13.$13.)(45.$13.$13.R2.R1.)VW,)(0.(2.(5.R5.R4.)R3.)(2.R2.R5.)))P,(2.=R3.)P,(2.(5.R4.R3.)(62.+2.+40.))(32.Vm,Vm',R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros A n HD HA HB a Ha. apply MU. rewrite wa_unsigned by lia.
  clear -WIN HD Ha. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
  - destruct HD as [HD|HD].
    + pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
    + pose proof (HD lo hi ltac:(left; reflexivity)). lia.
  - apply IH.
    + intros lo' hi' Hin. apply WIN. right; exact Hin.
    + destruct HD as [HD|HD]; [left; exact HD| right]. intros lo' hi' Hin. apply HD. right; exact Hin.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L1279563825.33 L13264852201.37L18260738130.37L22339628081.33L23547259113.37L27448817732.33L31956956740.33L33982012598.33L36394447921.33L38538082025.37L4687668406.33 L51073614870.33L52945088049.33L53511454605.33L54998819396.33L56461269045.9 L59880513769.37L63817830633.37L8304600113.33 00000100:00C00D00M00N00O00P00Q00Z00[00\00]00^00_00m01601?01@SS2lo2hi1HS2lo2hi1HSS2lo2hi1HSSSSS2lo2hi1HSSSSSS2lo2hi1x2Hx1HS2lo2hi1HS2lo2hi1HS". (* [comment removed for export] *)
#[using="m MR MU WM ER EM EA EG ES ERs WIN"] Lemma rmrep_ctx_frameW : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "P,(0.(36.$31.Vm',$3.(63.Vst',))(1.(<.(2?.$35.)(63.Vst',)(63.Vst,))Plo,$13.Phi,$13.P,(60.(44.$13.$13.)(45.$13.$13.R2.R1.)VW,)(0.(2.(5.$3.+50.)R3.)(2.R2.$3.))))P,(0.(39.$31.Vm',(5.$3.+50.)(64.Vst',))(1.(<.(2?.(2>.&40.))(64.Vst',)(64.Vst,))Plo,$13.Phi,$13.P,(60.(44.$13.$13.)(45.$13.$13.R2.R1.)VW,)(0.(2.(5.$3.+1=0.)R3.)(2.R2.(5.$3.+50.)))))P,(0.(39.$31.Vm',(5.$3.+1=0.)(65.Vst',))(1.(<.(2?.(2>.&40.))(65.Vst',)(65.Vst,))Plo,$13.Phi,$13.P,(60.(44.$13.$13.)(45.$13.$13.R2.R1.)VW,)(0.(2.(5.$3.+350.)R3.)(2.R2.(5.$3.+1=0.)))))P,(0.(3;.$31.Vm',(5.$3.+350.)(66.Vst',))(1.(<.(2?.(2>.&8.))(66.Vst',)(66.Vst,))Plo,$13.Phi,$13.P,(60.(44.$13.$13.)(45.$13.$13.R2.R1.)VW,)(0.(2.(5.$3.+370.)R3.)(2.R2.(5.$3.+350.)))))P,(0.(3;.$31.Vm',(5.$3.+370.)(67.Vst',))(1.(<.(2?.(2>.&8.))(67.Vst',)(67.Vst,))Plo,$13.Phi,$13.P,(60.(44.$13.$13.)(45.$13.$13.R2.R1.)VW,)(0.(2.(5.$3.+390.)R3.)(2.R2.(5.$3.+370.)))))P,(0.(36.$31.Vm',(5.$3.+390.)(68.Vst',))(1.(<.(2?.$35.)(68.Vst',)(68.Vst,))Plo,$13.Phi,$13.P,(60.(44.$13.$13.)(45.$13.$13.R2.R1.)VW,)(0.(2.(5.$3.+3:0.)R3.)(2.R2.(5.$3.+390.)))))(3>.VhRP,Vst',Vm',)")
(* [comment removed for export] *).
Proof.
  intros H1 H2 H3 H4 H5 H6.
  dpose MR as (WF & (C1 & C2 & C3 & C4 & C5 & C6) & GL & AR & GR & SH).
  assert (CX' : rmrep_ctx st' m').
  { unfold rmrep_ctx. split; [|split; [|split; [|split; [|split]]]].
    - destruct H1 as [H|[-> HD]]; [exact H|]. eapply rrw_cells_agree; eauto. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H2 as [H|[-> HD]]; [exact H|]. eapply ru64arr_agree; eauto. rewrite actives_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H3 as [H|[-> HD]]; [exact H|]. eapply ru64arr_agree; eauto. rewrite usages_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H4 as [H|[-> HD]]; [exact H|]. eapply ru8arr_agree; eauto. rewrite unmap_seqs_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H5 as [H|[-> HD]]; [exact H|]. eapply ru8arr_agree; eauto. rewrite bouncess_length. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia.
    - destruct H6 as [H|[-> HD]]; [exact H|]. eapply rrw_cells_agree; eauto. apply rctxW_avoid; [right| unfold RCTX; lia| unfold RCTX; cbn; lia]. cbn. intros lo hi Hin. destruct (HD lo hi Hin); lia. }
  eapply rmrep_ctx_frame'; [exact MR | | exact WM | exact ER | exact EM | exact EA | exact EG | exact ES | exact ERs | exact CX'].
  eapply munch_weaken; [|exact MU]. intros x Hx. cbn in Hx. destruct Hx as [Hx _].
  clear -WIN Hx. induction W as [|[lo hi] W' IH]; cbn; [exact I|]. split.
  - pose proof (WIN lo hi ltac:(left; reflexivity)). lia.
  - apply IH. intros lo' hi' Hin. apply WIN. right; exact Hin.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End CTXFRAME.

(* [comment removed for export] *)
Definition rntf_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) (st' : mstate) (a0v a1v : word) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B ()) "Lms',$69.(9.(2>.&40.)Lt0,(2>.&40.)(9.(2>.&40.)Lt1,(2>.&40.)(9.(2>.&40.)Lt2,(2>.&40.)(9.(2>.&40.)La2,(2>.&40.)(9.(2>.&40.)La3,(2>.&40.)(9.(2>.&40.)La4,(2>.&40.)(9.(2>.&40.)La5,(2>.&40.)(9.(2>.&40.)La6,(2>.&40.)(9.(2>.&40.)La7,(2>.&40.)(9.(2>.&40.)Lt3,(2>.&40.)(9.(2>.&40.)Lt4,(2>.&40.)(9.(2>.&40.)Lt5,(2>.&40.)(9.(2>.&40.)Lt6,(2>.&40.)(9.P,(2>.&40.)(=.(2>.&8.))Lm',P,(2>.&40.)(=.(2>.&8.))(1.(<.$69.R?.(6:.(6;.O18.O17.O16.O15.R>.R=.R<.O14.O13.O2.O1.R;.R:.R9.R8.R7.R6.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R5.R4.R3.R2.)O8.(6<.O18.)O7.(6=.(2>.&40.))R1.(6>.$31.)))(1.(61.(5?.O5.O6.(6?.&40.O17.))O4.R1.)(1.(38.$31.O4.R1.)(1.(70.$31.R1.)(1.(71.$31.R1.O6.(6?.&40.O17.))(3>.VhRP,O3.R1.))))))))))))))))))))")
(* [comment removed for export] *).

End RP_1.
