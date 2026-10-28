(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_A2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B F_am_K F_am_K2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RMallocKit_A2 HP_RF_am_K.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_am_K2 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "Corelib.Init.Logic.eq"; "stdpp.gmap.gmap"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.Z"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_metas"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_areas"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.shadow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_shadow"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.sparams"; "A2.agree_on"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RLIBC"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RGOT_SSP"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "stdpp.base.lookup"; "stdpp.gmap.gmap_lookup"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep_ctx"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.active"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.usage"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.unmap_seq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.bounces"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.actives"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.usages"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.unmap_seqs"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.bouncess"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rregions_wf"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.lr_lo"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_reserved"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ref_reserved"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ranges_free"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.live_ranges"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.not"].

Module A2 := MallocKit_A2.
Module RA2 := HP_RMallocKit_A2.
Section RP_1. Context {hRP : run_params}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00B0?L12818127403.40L13777040192.31L14226839558.37L2308346919.37 L23148579648.31L24219327104.31L24239895705.37L26966012639.31L30609631268.40L31433637599.31L42002756866.37L43081985999.31L45023331904.31L45665994261.39L52153901149.39L66119415344.31L7336757215.31 L8640946911.31 00000800900?00E00F00G00M00N00V00W00]00^00_00j015016017018S1r1o2HoSS2st1aS2st1aSSS2st1aSS1r1o2HoSS2st1aSSS2st1a1k2HkS2st1a1k2HkSSS". (* [comment removed for export] *)
#[using="Type"] Lemma rmrep_agree_but_ctx : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_K2 ()) "Pst,$0.Pst',$0.Pm,P,(1.&40.)(2.(1.&8.))Pm',$3.P,(4.VhRP,R4.R2.)P,(5.(6.$7.$8.$9.$:.)(;.R4.)(;.R5.))P,(5.(6.$<.(=.$7.$8.$>.$?.)(10.$7.$8.$9.$>.$?.$11.)$12.)(13.R5.)(13.R6.))P,(5.(6.$<.(=.$7.$8.$>.$?.)(10.$7.$8.$9.$>.$?.$11.)$14.)(15.R6.)(15.R7.))P,(5.(6.$<.(=.$7.$8.$>.$?.)(10.$7.$8.$9.$>.$?.$11.)$16.)(17.R7.)(17.R8.))P,(5.(6.$7.$8.$9.$18.)(19.R8.)(19.R9.))P,(5.(1:.(1:.(1:.(1;.(1:.$>.$>.))$>.)$>.)$>.)(1<.R9.)(1<.R:.))P,(1=.R9.R8.$1>.+4.)P,(1=.R:.R9.$1?.+68.)P,(1=.R;.R:.$20.+8.)P,(1=.R<.R;.$21.+8.)P,Pa,$<.Par,$14.P,(5.(2.$14.)(22.$<.$14.(6.$<.(=.$7.$8.$>.$?.)(10.$7.$8.$9.$>.$?.$11.)$14.)(23.$<.(=.$7.$8.$>.$?.)(10.$7.$8.$9.$>.$?.$11.)$14.)R2.(15.R11.))(24.$14.R1.))(1=.R10.R?.(25.R12.R3.)+1000.)P,Pb,$<.Pgh,$16.P,(5.(2.$16.)(22.$<.$16.(6.$<.(=.$7.$8.$>.$?.)(10.$7.$8.$9.$>.$?.$11.)$16.)(23.$<.(=.$7.$8.$>.$?.)(10.$7.$8.$9.$>.$?.$11.)$16.)R2.(17.R12.))(24.$16.R1.))(1=.R11.R10.(25.R13.R3.)+9.)P,Prid,$7.Pr,$:.P,(5.(2.$:.)(22.$7.$:.(6.$7.$8.$9.$:.)(23.$7.$8.$9.$:.)R2.(;.R13.))(24.$:.R1.))P,(5.$26.(27.R2.)$28.)(1=.R13.R12.(29.R3.)(2:.(2;.R3.)))P,(2<.R11.R?.)(4.VhRP,R12.R10.)")
(* [comment removed for export] *).
Proof. rceilb.
  (intros st st' m m' dd_H; ddestruct dd_H as (WF & CX & GL & AR & GR & SH); intros ER EM EA EG ES ERs AGL AGC AGS1 AGS2 AGA AGG AGR CX').
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [exact CX'|split; [|split; [|split]]]].
  - ddestruct WF as ((RS & RPRS) & WR & DJ & WA & WG). unfold rregions_wf. rewrite ER, EA, EG. split; [exact (rparams_ok_same _ _ (conj RS RPRS) ERs)|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA| exact WG].
  - ddestruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply RA2.rrw_cells_agree; [exact G1|]. eapply A2.agree_on_sub; [exact AGL| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G2|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G3|]. eapply A2.agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G4|]. eapply A2.agree_on_sub; [exact AGS1| lia| cbn; lia].
    + eapply RA2.rrw_cells_agree; [exact G5|]. eapply A2.agree_on_sub; [exact AGS2| lia| cbn; lia].
  - intros a ar Ha. rewrite EA in Ha. ddestruct (AR a ar Ha) as (A1 & A3 & A4). pose proof (AGA a ar Ha) as AG.
    unfold rarea_rep. rewrite !Hconc.
    assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
    assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
    assert (GM : forall g, get_meta_rec st' g = get_meta_rec st g) by (intros; unfold get_meta_rec; rewrite EM; reflexivity).
    rewrite PW. split; [|split].
    + eapply RA2.rrw_cells_agree; [exact A1|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
    + intros k Hk. rewrite MC, GM. eapply RA2.rrw_cells_agree; [apply A3; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply A2.agree_on_sub; [exact AG| lia| lia].
    + eapply RA2.rrw_cells_agree; [exact A4|]. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - intros b gh Hb. rewrite EG in Hb. ddestruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    rewrite Hconc. replace (pw st' (g_meta gh)) with (pw st (g_meta gh)) by (destruct (g_meta gh); unfold pw, oconc; [rewrite Hconc|]; reflexivity).
    eapply RA2.rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
  - intros rid r Hr Hk. rewrite ER in Hr. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG.
    unfold rshadow_rep. replace (get_shadow st' rid) with (get_shadow st rid) by (unfold get_shadow; rewrite ES; reflexivity). split.
    + eapply RA2.rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply RA2.rbytes_at_agree; [exact Bt|]. cbn. eapply A2.agree_on_sub; [exact AG| lia| lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L1075606356.26 L31791855537.26L45220913492.26L49678737267.26L55755537236.26L572402516.26  L65883718003.26L68466778033.2600000@00P00`01001@01P01`020S2st2L12L22L32L4S2st2L12L22L32L4S2st2L12L22L32L4S2st2L12L22L32L4S2st2L12L22L32L4S2st2L12L22L32L4S2st2L12L22L32L4S2st2L12L22L32L4". (* [comment removed for export] *)
#[using="Type"] Lemma rmrep_ctx_mid_agree : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_K2 ()) "Pst,$0.Pst',$0.Pm,P,(1.&40.)(2.(1.&8.))Pm',$3.P,(4.VhRP,R4.R2.)P,(2=.(5.$2>.(2?.R4.)(2?.R5.))(30.Psc,$>.(5.$31.(32.R5.R1.)(32.R6.R1.))(30.Psc,$>.(5.$>.(33.R5.R1.)(33.R6.R1.))(30.Pi,$>.(5.$>.(34.R5.R1.)(34.R6.R1.))Pi,$>.(5.$>.(35.R5.R1.)(35.R6.R1.))))))P,(5.(6.$7.$8.$9.$:.)(;.R5.)(;.R6.))P,(1=.R5.R4.(36.$37.+50.)+340.)(30.(38.$39.R5.(36.$37.+50.)(3:.R7.))(30.(38.$39.R5.(36.$37.+1=0.)(3;.R7.))(30.(3<.$39.R5.(36.$37.+350.)(3=.R7.))(3<.$39.R5.(36.$37.+370.)(3>.R7.)))))")
(* [comment removed for export] *).
Proof. rceilb.
  (intros st st' m m' dd_H; ddestruct dd_H as (WF & (C1 & C2 & C3 & C4 & C5 & C6) & _); intros HX ER AG).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; unfold conc, get_region; rewrite ER; reflexivity).
  assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity).
  assert (E2 : actives st' = actives st).
  { unfold actives. apply map_ext. intros i. rewrite PW. destruct HX as [E|(E & _)]; [unfold active; rewrite E| rewrite E]; reflexivity. }
  assert (E3 : usages st' = usages st).
  { unfold usages. apply map_ext. intros i. destruct HX as [E|(_ & E & _)]; [unfold usage; rewrite E| rewrite E]; reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st).
  { unfold unmap_seqs. apply map_ext. intros i. destruct HX as [E|(_ & _ & E & _)]; [unfold unmap_seq; rewrite E| rewrite E]; reflexivity. }
  assert (E5 : bouncess st' = bouncess st).
  { unfold bouncess. apply map_ext. intros i. destruct HX as [E|(_ & _ & _ & E)]; [unfold bounces; rewrite E| rewrite E]; reflexivity. }
  rewrite E2, E3, E4, E5.
  assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
  assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
  assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
  assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
  unfold RCTX in *.
  split; [|split; [|split]].
  - eapply RA2.ru64arr_agree; [exact C2|]. rewrite L1. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru64arr_agree; [exact C3|]. rewrite L2. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru8arr_agree; [exact C4|]. rewrite L3. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
  - eapply RA2.ru8arr_agree; [exact C5|]. rewrite L4. eapply A2.agree_on_sub; [exact AG| lia| cbn; lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L56750581748.1600000FS2st1a1r1x2Hx2Ca3Sa11H". (* [comment removed for export] *)
#[using="Type"] Lemma rarea_in_live : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_K2 ()) "Pst,$0.Pa,(1:.$7.$>.)Par,$14.Pr,$:.Px,$>.P,(3?.VhRP,R5.)P,(5.(2.$14.)(22.(1:.$7.$>.)$14.(6.$<.(=.$7.$8.$>.$?.)(10.$7.$8.$9.$>.$?.$11.)$14.)(23.$<.(=.$7.$8.$>.$?.)(10.$7.$8.$9.$>.$?.$11.)$14.)R5.(15.R6.))(24.$14.R4.))P,(5.(2.$:.)(22.$7.$:.(6.$7.$8.$9.$:.)(23.$7.$8.$9.$:.)(40.$7.$>.R6.)(;.R7.))(24.$:.R4.))P,(30.(41.(25.R8.R7.)R4.)(42.R4.(36.(25.R8.R7.)+1000.)))(30.(41.(43.R6.)R5.)(42.R5.(36.(29.R6.)(2:.(2;.R6.)))))")
(* [comment removed for export] *).
Proof. rceilb.
  intros st a ar r x WF Ha Hr Hx. ddestruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & _).
  rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
  pose proof (rarea_lr_lo st a ar r WF Ha Hr). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L56755221199.1600000HS2st1b1r1x2Hx2Cb3Sb03Sb1". (* [comment removed for export] *)
#[using="Type"] Lemma rgroup_in_live : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_K2 ()) "Pst,$0.Pb,(1:.$7.$>.)Pgh,$16.Pr,$:.Px,$>.P,(3?.VhRP,R5.)P,(5.(2.$16.)(22.(1:.$7.$>.)$16.(6.$<.(=.$7.$8.$>.$?.)(10.$7.$8.$9.$>.$?.$11.)$16.)(23.$<.(=.$7.$8.$>.$?.)(10.$7.$8.$9.$>.$?.$11.)$16.)R5.(17.R6.))(24.$16.R4.))P,(5.(2.$:.)(22.$7.$:.(6.$7.$8.$9.$:.)(23.$7.$8.$9.$:.)(40.$7.$>.R6.)(;.R7.))(24.$:.R4.))P,(30.(41.(25.R8.R7.)R4.)(42.R4.(36.(25.R8.R7.)+9.)))(30.(41.(43.R6.)R5.)(42.R5.(36.(29.R6.)(2:.(2;.R6.)))))")
(* [comment removed for export] *).
Proof. rceilb.
  intros st b gh r x WF Hb Hr Hx. ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
  rewrite Hr in Hrb. assert (rb = r) by congruence. subst rb. rewrite (lr_lo_group r Krb). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59308579281.1400000JS2lo1n1x2Hx3Hin1H2H02H12H2". (* [comment removed for export] *)
#[using="hRP"] Lemma rimage_clear_of_ranges_free st lo n x : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_K2 ()) "P,(5.(1;.(1:.$>.$>.))(44.O4.)$45.)P,(5.$46.(47.(48.O4.)O3.O2.)$49.)P,(30.(41.+10000.O1.)(42.O1.+7>000.))(4:.(30.(41.O3.O1.)(42.O1.(36.O3.O2.))))")
(* [comment removed for export] *).
Proof. rceilb.
  intros RS RF Hx Hin. unfold live_ranges in RF. rewrite RS in RF.
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; left; reflexivity)).
  pose proof (ranges_free_In _ _ _ _ _ RF ltac:(apply in_or_app; left; right; right; right; left; reflexivity)). cbn in *. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section GROW.
Variables (st : mstate) (m : mem) (rid : N) (r : region) (off : Z).
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis NK : r_kind r <> RKGroup.
Hypothesis LEN : r_len r = off.
Hypothesis OFF : 0 <= off.
Hypothesis OAL : off mod 4096 = 0.
Hypothesis RF : ranges_free (live_ranges st) (r_base r + off) 4096 = true.
Hypothesis CEIL : r_base r + off + 4096 <= rceil.
Hypothesis RPOS : forall q rq, (s_regions st) !! q = Some rq -> 0 < r_len rq.
Hypothesis UNIQ : forall q rq, (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq <> RKBrk.

Let r' := mkRegion (r_kind r) (r_base r) (off + 4096).
Let st' := set_regions (<[rid := r']> (s_regions st)) st.

#[using="hRP Hr"] Lemma rgr_eq : upd_region rid (fun rg => mkRegion (r_kind rg) (r_base rg) (off + 4096)) st = st'.
Proof. rceilb. unfold st', upd_region, get_region. rewrite Hr. reflexivity. Qed.
#[using="hRP"] Lemma rgr_regions : s_regions st' = <[rid := r']> (s_regions st).
Proof. rceilb. reflexivity. Qed.
#[using="hRP"] Lemma rgr_lookup_inv q rq : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_K2 ()) "P,(5.(2.$:.)(22.$7.$:.(6.$7.$8.$9.$:.)(23.$7.$8.$9.$:.)O2.(;.Vst',))(24.$:.O1.))(2=.(30.(5.$7.O2.Vrid,)(5.$:.O1.Vr',))(30.(4:.(5.$7.O2.Vrid,))(5.(2.$:.)(22.$7.$:.(6.$7.$8.$9.$:.)(23.$7.$8.$9.$:.)O2.(;.Vst,))(24.$:.O1.))))")
(* [comment removed for export] *).
Proof. rceilb.
  rewrite rgr_regions. intros H. destruct (decide (q = rid)) as [->|NE].
  - rewrite lookup_insert_eq in H. left. split; congruence.
  - rewrite lookup_insert_ne in H by congruence. right. auto.
Qed.
#[using="hRP"] Lemma rgr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. rceilb. intros. rewrite rgr_regions, lookup_insert_ne by congruence. reflexivity. Qed.
#[using="hRP"] Lemma rgr_lookup_new : (s_regions st') !! rid = Some r'.
Proof. rceilb. rewrite rgr_regions, lookup_insert_eq. reflexivity. Qed.
#[using="hRP Hr"] Lemma rgr_conc q : conc st' q = conc st q.
Proof. rceilb.
  unfold conc, get_region. destruct (decide (fst q = rid)) as [E|NE].
  - rewrite E, rgr_lookup_new, Hr. reflexivity.
  - rewrite rgr_lookup_old by exact NE. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L17262411808.33L57357483340.1900000L00US3off2r13OAL1q2r01H2H02q02H4S3off3OFF". (* [comment removed for export] *)
#[using="hRP OFF OAL"] Lemma rgr_ru : round_up_pg (off + 4096) = round_up_pg off + 4096.
Proof. rceilb. rewrite !round_up_pg_aligned; [lia| exact OAL|]. Z.div_mod_to_equations. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L1974450422.34 L29558973962.42L39165472031.33L4354141304.33 L60269622843.4900000=00V00j01501eS1r3RL02D22D1S3rid1r3off3OFF1a2A02A11ES3hRP1r3off3OFF4CEILS1r3off3OFFS3rid1r3off3OFF3RB02q12q22NE1q2rq3NEq1D3RLq1H2D2". (* [comment removed for export] *)
#[using="m MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ"] Lemma rgr_regions_wf : rregions_wf st'.
Proof. rceilb.
  pose proof MR as (WF & _). dpose WF as ((RS & RPRS) & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  assert (RU : round_up_pg off = off) by (apply round_up_pg_aligned; exact OAL).
  split; [exact (conj RS RPRS)|]. split; [|split; [|split]].
  - intros q rq Hq. destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]]; [| exact (WR q rq H)].
    cbn [r_base r_len r_kind r']. rewrite rgr_ru, RU. split; [exact RB0|]. split; [exact RBAL|]. split; [lia|]. split; [lia|].
    apply ranges_free_intro. intros b n HI.
    pose proof (ranges_free_In _ _ _ _ _ RFr HI) as D1. rewrite LEN, RU in D1.
    assert (D2 := ranges_free_In _ _ _ _ _ RF ltac:(unfold live_ranges; apply in_or_app; left; rewrite RS; exact HI)).
    destruct HI as [E|[E|[E|[E|[]]]]]; inversion E; subst; lia.
  - intros q1 r1 q2 r2 H1 H2 NE.
    assert (OLD : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
              r_base r' + round_up_pg (r_len r') <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= lr_lo r').
    { intros q rq Hq NEq. cbn [r_base r_len r']. rewrite rgr_ru, RU.
      replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
      destruct (DJ _ _ _ _ Hr Hq ltac:(congruence)) as [D|D]; rewrite ?LEN, ?RU in D.
      - left. pose proof (In_live_ranges st q rq Hq) as HI. unfold region_live_range in HI. unfold lr_lo in *. unfold PGSZ in HI.
        pose proof (RPOS q rq Hq) as RLq. pose proof (round_up_pg_ge (r_len rq)). pose proof (UNIQ q rq Hq NEq) as NB.
        destruct (r_kind rq); [exfalso; apply NB; reflexivity | |]; (pose proof (ranges_free_In _ _ _ _ _ RF HI) as D2; lia).
      - right. exact D. }
    destruct (rgr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rgr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + exact (OLD q2 r2 H2' NE2).
    + destruct (OLD q1 r1 H1' NE1); [right| left]; assumption.
    + exact (DJ q1 r1 q2 r2 H1' H2' NE).
  - intros a ar Ha. ddestruct (WA a ar Ha) as (ra & Hra & A0 & A1 & AAL & NKa & LO).
    destruct (decide (fst a = rid)) as [E|NE].
    + exists r'. rewrite E in Hra |- *. rewrite rgr_lookup_new. rewrite Hr in Hra. assert (ra = r) by congruence. subst ra.
      cbn [r_base r_len r_kind r']. rewrite rgr_ru. replace (lr_lo r') with (lr_lo r) by (unfold lr_lo, r'; cbn; reflexivity).
      rewrite LEN in A1. repeat split; try assumption; lia.
    + exists ra. rewrite rgr_lookup_old by exact NE. repeat split; assumption.
  - intros b gh Hb. ddestruct (WG b gh Hb) as (rb & Hrb & Kb & REST).
    assert (NE : fst b <> rid) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Kb)).
    exists rb. rewrite rgr_lookup_old by exact NE. auto.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="MR Hr NK LEN OFF OAL RF CEIL RPOS UNIQ"] Lemma rmrep_grow_region : rmrep st' m.
Proof. rceilb.
  dpose MR as (WF & CX & GL & AR & GR & SH).
  assert (PW : forall p, pw st' p = pw st p) by (intros [q|]; unfold pw, oconc; [rewrite rgr_conc|]; reflexivity).
  assert (MC : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !PW; reflexivity).
  split; [exact rgr_regions_wf|]. split; [|split; [exact GL|split; [|split]]].
  - ddestruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    replace (ctx_head_cells st') with (ctx_head_cells st) by (unfold ctx_head_cells; change (ctx st') with (ctx st); rewrite !PW; reflexivity).
    replace (actives st') with (actives st) by (unfold actives; apply map_ext; intros; rewrite PW; reflexivity).
    replace (ctx_tail_cells st') with (ctx_tail_cells st).
    2:{ unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st). destruct (c_brk (ctx st)); rewrite ?rgr_conc; reflexivity. }
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C5| exact C6].
  - intros a ar Ha. change (s_areas st') with (s_areas st) in Ha. ddestruct (AR a ar Ha) as (A1 & A3 & A4).
    unfold rarea_rep. rewrite !rgr_conc, PW. change (get_meta_rec st') with (get_meta_rec st).
    split; [exact A1|]. split; [| exact A4]. intros k Hk. rewrite MC. apply A3. exact Hk.
  - intros b gh Hb. change (s_groups st') with (s_groups st) in Hb. ddestruct (GR b gh Hb) as (w8 & R & Hw8).
    exists w8. rewrite rgr_conc, PW. split; assumption.
  - intros q rq Hq Hk. change (get_shadow st' q) with (get_shadow st q).
    destruct (rgr_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
    + exfalso. apply NK. exact Hk.
    + exact (SH q rq H Hk).
Qed.

End GROW.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="hRP"] Lemma rimpl_enode_dec_weaken {A} n (dec dec' : resp -> option A) (G : A -> Prop) (P : A -> machine_state -> Prop) ms :
  impl rsegs (at_node rsegs) (enode n dec) (epost P) ms ->
  (forall rsp a, dec' rsp = Some a -> dec rsp = Some a /\ G a) ->
  impl rsegs (at_node rsegs) (enode n dec') (epost (fun a ms' => P a ms' /\ G a)) ms.
Proof. rceilb.
  intros H HD. unfold enode in *. rewrite rimpl_vis_unfold in H. rewrite rimpl_vis_unfold.
  eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. specialize (Hk rsp).
  destruct (dec' rsp) as [a|] eqn:E.
  - destruct (HD rsp a E) as [E1 HG]. rewrite E1 in Hk. cbn in Hk |- *. eapply evt_mono; [exact Hk|]. intros ms' HP; cbn in *. auto.
  - cbn. apply evt_done. exact I.
Qed.


End RP_1.
