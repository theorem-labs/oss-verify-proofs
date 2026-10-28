(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocTree MallocModel_B F_ntf_B F_am_K.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_am_K () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.zeros"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_wf"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.N"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.N.eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.N_countable"; "stdpp.countable.Z_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_areas"; "Corelib.Init.Datatypes.Some"; "stdpp.base.is_Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.a_check"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.a_nslots"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_areas"; "stdpp.base.insert"; "stdpp.fin_maps.map_insert"; "stdpp.gmap.gmap_partial_alter"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mkArea"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.lr_lo"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.NSLOTS"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aadd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.AREA_HDR"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.META_SIZE"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_metas"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.meta_cells"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta0"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rrepfoot"].



Section RP_1. Context {hRP : run_params}.
#[using="hRP"] Lemma rbytes_at_zeros_sub m A n off k : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_K ()) "P,(0.$1.O5.O4.(2.O3.))P,(3.=O2.)P,(3.(4.O2.(5.O1.))(5.O3.))(0.$1.O5.(4.O4.O2.)(2.O1.))")
(* [comment removed for export] *).
Proof. rceilb.
  (intros dd_H; ddestruct dd_H as (H0 & H1 & HB); intros Hoff Hk). rewrite zeros_length in H1, HB. split; [lia|]. rewrite zeros_length. split; [lia|].
  intros i Hi. replace (A + off + Z.of_nat i) with (A + Z.of_nat (Z.to_nat off + i)) by lia.
  rewrite HB by lia. unfold zeros. rewrite !nth_error_repeat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="hRP"] Lemma rrw_cells_of_zeros m A n off cs : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_K ()) "P,(0.$1.O5.O4.(2.O3.))P,(6.$1.O5.O4.(5.O3.))P,(7.O1.)P,(8.(9.(:.&8.))(;.O1.)(2.(<.O1.)))P,(3.=O2.)P,(3.(4.O2.(5.(<.O1.)))(5.O3.))(=.$1.O5.(4.O4.O2.)O1.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros HB HW WF E Hoff Hsz. apply rw_cells_of_bytes; [exact WF| |].
  - rewrite E. apply (rbytes_at_zeros_sub m A n off); assumption.
  - eapply wr_at_sub; [exact HW| lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rmrep_set_area_next : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_K ()) "Pst,$>.Pm,P,(:.&40.)(?.(:.&8.))Pm',P,(:.&40.)(?.(:.&8.))Pa,$10.Par,$11.Pp,(12.$13.$14.)P,(15.VhRP,R6.R5.)P,(8.(?.$11.)(16.$10.$11.(17.$10.(18.$13.$19.$14.$1:.)(1;.$13.$19.$1<.$14.$1:.$1=.)$11.)(1>.$10.(18.$13.$19.$14.$1:.)(1;.$13.$19.$1<.$14.$1:.$1=.)$11.)R4.(1?.R7.))(20.$11.R3.))P,(21.$22.(16.$13.$22.(17.$13.$19.$1<.$22.)(1>.$13.$19.$1<.$22.)(23.$13.$14.R3.)(24.R8.)))P,(25.(26.(12.$14.$14.)(27.$14.$14.(4.(28.R9.R6.)+8.)(4.(28.R9.R6.)+10.))(29.(12.$14.$14.)))R8.R7.)P,(2:.$1.R9.R8.)P,(=.$1.R9.(28.R;.R8.)(26.$2;.(2<.(2=.(2>.R7.)))(26.$2;.(2<.(2=.(28.R;.R6.)))(26.$2;.(2?.(2=.(30.R7.)))(26.$2;.(2?.(2=.=))(29.$2;.))))))(15.VhRP,(31.(32.$10.$11.(17.$10.(18.$13.$19.$14.$1:.)(1;.$13.$19.$1<.$14.$1:.$1=.)$11.)(33.$10.$11.(17.$10.(18.$13.$19.$14.$1:.)(1;.$13.$19.$1<.$14.$1:.$1=.)$11.)(34.$10.(18.$13.$19.$14.$1:.)(1;.$13.$19.$1<.$14.$1:.$1=.)$11.))R9.(35.(2>.R8.)(20.(12.$13.$14.)R7.)(30.R8.))(1?.R<.))R<.)R:.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros st m m' a ar p MR Ha Hp MU WM CH.
  dpose MR as (WF & CX & GL & AR & GR & SH). dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  ddestruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC). rceilb.
  set (st' := set_areas _ st).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
  assert (AG : forall A cs, rw_cells rsegs m A cs -> (A + Z.of_nat (cells_size cs) <= conc st a + 8 \/ conc st a + 16 <= A) -> rw_cells rsegs m' A cs).
  { intros A cs H HD. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree; [exact H| | exact WM].
    intros x Hx. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *) split; [exact (conj Hres RPHres)|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
    intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = a)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. exact (WA a ar Ha).
    + rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
  - (* [comment removed for export] *) ddestruct CX as (C1 & C2 & C3 & C4 & C5 & C6). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
    unfold rmrep_ctx. change (ctx_head_cells st') with (ctx_head_cells st). change (actives st') with (actives st).
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st).
    change (ctx_tail_cells st') with (ctx_tail_cells st).
    split; [apply AG; [exact C1| cbn; unfold RCTX; lia]|].
    split; [eapply ru64arr_agree; [exact C2| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite actives_length in Hx; unfold RCTX in Hx; lia); rewrite actives_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru64arr_agree; [exact C3| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite usages_length in Hx; unfold RCTX in Hx; lia); rewrite usages_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru8arr_agree; [exact C4| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite unmap_seqs_length in Hx; unfold RCTX in Hx; lia); rewrite unmap_seqs_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    split; [eapply ru8arr_agree; [exact C5| intros x Hx; apply MU; rewrite wa_unsigned by (rewrite bouncess_length in Hx; unfold RCTX in Hx; lia); rewrite bouncess_length in Hx; cbn; unfold RCTX in Hx; lia| exact WM]|].
    apply AG; [exact C6| cbn; unfold RCTX; lia].
  - (* [comment removed for export] *) ddestruct GL as (G1 & G2 & G3 & G4 & G5). pose proof (rreserved_disjoint _ _ (proj2 (proj2 (proj2 (proj2 (WR _ _ Hra)))))) as (_ & _ & DA3 & DA).
    split; [apply AG; [exact G1| cbn; unfold RMLOCK; lia]|]. split; [apply AG; [exact G2| cbn; unfold RNEED_LOCKS; lia]|].
    split; [apply AG; [exact G3| cbn; unfold RPAGE_SIZE; lia]|]. split; [apply AG; [exact G4| cbn; unfold RGOT_SSP; lia]|]. apply AG; [exact G5| cbn; unfold RSSP_GUARD; lia].
  - (* [comment removed for export] *) intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
    change (get_meta_rec st') with (get_meta_rec st).
    assert (MC : forall r, meta_cells st' r = meta_cells st r) by (intros; reflexivity).
    destruct (decide (a' = a)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots]. ddestruct (AR a ar Ha) as (A1 & A2 & A3).
      split; [unfold pw; cbn [oconc]; rewrite Hconc; exact CH|]. split.
      * intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE. lia.
      * apply AG; [exact A3| cbn; lia].
    + rewrite lookup_insert_ne in Ha' by congruence. ddestruct (AR a' ar' Ha') as (A1 & A2 & A3).
      ddestruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
      assert (DIS : conc st a' + 4096 <= conc st a \/ conc st a + 4096 <= conc st a').
      { destruct (N.eq_dec (fst a') (fst a)) as [E|NE2].
        - rewrite E, Hra in Hra'. assert (ra' = ra) by congruence. subst ra'.
          assert (snd a' <> snd a) by (intros E2; apply NE; destruct a, a'; cbn in *; congruence).
          Z.div_mod_to_equations. lia.
        - pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra').
          destruct (DJ _ _ _ _ Hra' Hra NE2); lia. }
      change (pw st' (a_next ar')) with (pw st (a_next ar')).
      split; [apply AG; [exact A1| cbn; lia]|]. split.
      * intros k Hk. rewrite MC. apply AG; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add]. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia.
      * apply AG; [exact A3| cbn; lia].
  - (* [comment removed for export] *) intros b gh Hb. ddestruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [| exact Hw8].
    rewrite Hconc. change (pw st' (g_meta gh)) with (pw st (g_meta gh)). apply AG; [exact R|].
    ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RBb & RBCb).
    assert (NE : fst b <> fst a) by (intros E; rewrite E, Hra in Hrb; assert (rb = ra) by congruence; subst; exact (NK Krb)).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group rb Krb).
    cbn. destruct (DJ _ _ _ _ Hrb Hra NE); lia.
  - (* [comment removed for export] *) intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. change (get_shadow st' rid) with (get_shadow st rid). split.
    + eapply wr_at_transport; [exact HWr| exact WM].
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [B V]. split; [| exact V].
      eapply rbytes_at_agree; [exact B|]. cbn. intros x Hx. apply MU. rewrite wa_unsigned by (destruct (WR _ _ Hr) as (? & ? & ? & RC & ?); rceilb; pose proof (round_up_pg_ge (r_len r)); lia).
      assert (NE : rid <> fst a) by (intros E; rewrite E, Hra in Hr; assert (r = ra) by congruence; subst; exact (NK Hk)).
      pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (lr_lo_group r Hk). cbn. destruct (DJ _ _ _ _ Hr Hra NE); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rmrep_new_area : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_K ()) "Pst,$>.Pm,P,(:.&40.)(?.(:.&8.))Pp,$10.Pr,$22.Pchk,$14.P,(15.VhRP,R5.R4.)P,(8.(?.$11.)(16.$10.$11.(17.$10.(18.$13.$19.$14.$1:.)(1;.$13.$19.$1<.$14.$1:.$1=.)$11.)(1>.$10.(18.$13.$19.$14.$1:.)(1;.$13.$19.$1<.$14.$1:.$1=.)$11.)R4.(1?.R6.))(36.$11.))P,(8.(?.$22.)(16.$13.$22.(17.$13.$19.$1<.$22.)(1>.$13.$19.$1<.$22.)(23.$13.$14.R5.)(24.R7.))(20.$22.R4.))P,(37.(8.$38.(39.R5.)$3:.))P,(3.=(3;.$13.$14.R7.))P,(3.(4.(3;.$13.$14.R8.)+1000.)(3<.(3=.R7.)))P,(8.$14.(3>.(3;.$13.$14.R9.)+1000.)=)P,(3.(3?.R9.)(4.(40.R9.)(3;.$13.$14.R:.)))P,Pk,$14.P,(41.(3.=R1.)(42.R1.$43.))(8.(?.$44.)(16.$10.$44.(17.$10.(18.$13.$19.$14.$1:.)(1;.$13.$19.$1<.$14.$1:.$1=.)$44.)(1>.$10.(18.$13.$19.$14.$1:.)(1;.$13.$19.$1<.$14.$1:.$1=.)$44.)(45.R=.(4.$46.(47.$48.R2.)))(49.R?.))(36.$44.))P,(=.$1.R=.(28.R>.R<.)(26.$2;.(2<.(2=.R:.))(26.$2;.(2<.(2=.=))(26.$2;.(2?.(2=.$43.))(26.$2;.(2?.(2=.=))(29.$2;.))))))P,Pk,$14.P,(41.(3.=R1.)(42.R1.$43.))(=.$1.R10.(4.(4.(28.R11.R?.)$46.)(47.$48.R2.))(4:.R11.$4;.))P,(=.$1.R?.(4.(28.R10.R>.)+?>0.)(26.$2;.(4<.#20.(2.#20.))(29.$2;.)))(15.VhRP,(31.(32.$10.$11.(17.$10.(18.$13.$19.$14.$1:.)(1;.$13.$19.$1<.$14.$1:.$1=.)$11.)(33.$10.$11.(17.$10.(18.$13.$19.$14.$1:.)(1;.$13.$19.$1<.$14.$1:.$1=.)$11.)(34.$10.(18.$13.$19.$14.$1:.)(1;.$13.$19.$1<.$14.$1:.$1=.)$11.))R?.(35.R=.(36.$10.)$43.)(1?.R11.))R11.)R10.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros st m p r chk MR Hnone Hr NK S0 S1 SAL SLR FRESH HDR SLOTS PAD.
  dpose MR as (WF & CX & GL & AR & GR & SH). dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  set (st' := set_areas _ st).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros; reflexivity).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact (conj Hres RPHres)|]. split; [exact WR|]. split; [exact DJ|]. split; [| exact WG].
    intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. destruct (decide (a' = p)) as [->|NE].
    + exists r. repeat split; assumption.
    + rewrite lookup_insert_ne in Ha' by congruence. exact (WA a' ar' Ha').
  - exact CX.
  - exact GL.
  - intros a' ar' Ha'. cbn [st' s_areas set_areas] in Ha'. unfold rarea_rep. rewrite !Hconc.
    change (get_meta_rec st') with (get_meta_rec st). change (meta_cells st') with (meta_cells st).
    destruct (decide (a' = p)) as [->|NE].
    + rewrite lookup_insert_eq in Ha'. inversion Ha'; subst ar'. cbn [a_check a_next a_nslots].
      split; [exact HDR|]. split; [| exact PAD].
      intros k Hk. unfold get_meta_rec. rewrite (FRESH k Hk). cbn [default]. apply SLOTS. exact Hk.
    + rewrite lookup_insert_ne in Ha' by congruence. exact (AR a' ar' Ha').
  - exact GR.
  - exact SH.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rfresh_page_avoids : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_K ()) "Pst,$>.Pm,P,(:.&40.)(?.(:.&8.))Pp,$10.Pr,$22.Pa,$14.P,(15.VhRP,R5.R4.)P,(8.(?.$22.)(16.$13.$22.(17.$13.$19.$1<.$22.)(1>.$13.$19.$1<.$22.)(23.$13.$14.R4.)(24.R6.))(20.$22.R3.))P,(37.(8.$38.(39.R4.)$3:.))P,(3.=(3;.$13.$14.R6.))P,(3.(4.(3;.$13.$14.R7.)+1000.)(3<.(3=.R6.)))P,(8.$14.(3>.(3;.$13.$14.R8.)+1000.)=)P,(3.(3?.R8.)(4.(40.R8.)(3;.$13.$14.R9.)))P,(8.(?.$11.)(16.$10.$11.(17.$10.(18.$13.$19.$14.$1:.)(1;.$13.$19.$1<.$14.$1:.$1=.)$11.)(1>.$10.(18.$13.$19.$14.$1:.)(1;.$13.$19.$1<.$14.$1:.$1=.)$11.)R:.(1?.R<.))(36.$11.))P,(41.(3.(28.R=.R;.)R9.)(42.R9.(4.(28.R=.R;.)+1000.)))(37.(4=.R>.R:.))")
(* [comment removed for export] *).
Proof. rceilb.
  intros st m p r a MR Hr NK S0 S1 SAL SLR ANone Ha.
  pose proof MR as (WF & _). dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  pose proof (conc_region' st p r Hr) as Cp.
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (rreserved_disjoint _ _ RF) as (DR1 & _ & DR23 & DR2). rceilb.
  pose proof (lr_lo_ge r) as LRG. pose proof (round_up_pg_ge (r_len r)) as RU.
  intros [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
  - unfold RCTX in C. lia.
  - unfold RMLOCK in C. lia.
  - unfold RNEED_LOCKS in C. lia.
  - unfold RPAGE_SIZE in C. lia.
  - ddestruct C as (ak & ar & Hak & Hin).
    ddestruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NKa & _).
    destruct (N.eq_dec (fst ak) (fst p)) as [E|NE].
    + rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra.
      assert (NEo : snd ak <> snd p).
      { intros E2. assert (ak = p) by (destruct ak, p; cbn in *; congruence). subst ak. rewrite ANone in Hak. discriminate. }
      Z.div_mod_to_equations. lia.
    + pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE); lia.
  - ddestruct C as (b & gh & Hb & Hin). ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
    assert (NE : fst b <> fst p) by (intros E; rewrite E, Hr in Hrb; assert (rb = r) by congruence; subst; exact (NK Krb)).
    pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
  - ddestruct C as (rid & rg & v & Hrg & Krg & Hin & _).
    assert (NE : rid <> fst p) by (intros E; rewrite E, Hr in Hrg; assert (rg = r) by congruence; subst; exact (NK Krg)).
    pose proof (lr_lo_group rg Krg). destruct (DJ _ _ _ _ Hrg Hr NE); lia.
  - unfold RGOT_SSP in C. lia.
  - unfold RSSP_GUARD in C. lia.
Qed.


End RP_1.
