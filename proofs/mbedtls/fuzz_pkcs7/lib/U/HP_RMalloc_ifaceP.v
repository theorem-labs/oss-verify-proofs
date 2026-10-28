(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocHINV MallocFacts_A Malloc_iface InitMem F_malloc_top Malloc_ifaceP.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMalloc_iface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require MallocFacts_inv2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RMalloc_ifaceP () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "Corelib.Init.Logic.eq"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_A.MFACTS_g"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ref_reserved"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.block"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.blk_slot"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cptr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_slots"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.blk_addr"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.blk_size"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.PState"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_iface.RHEAP"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.Prog.bptr"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.blk_id"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rrepfoot"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RLIBC"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RGOT_SSP"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "Corelib.Lists.ListDef.Forall"; "RocqVerifyHarness.AgentSubmission.U.HP_RMalloc_iface.rclient_write_ok"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64s"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.Heap.MallocRep.wz"; "Corelib.Init.Nat.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"].


(* [comment removed for export] *)
(* [comment removed for export] *)

Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma rregion_addr_facts : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_ifaceP ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Prid,$3.Pr,$4.P,(5.VhRP,R4.R3.)P,(6.(2.$4.)(7.$3.$4.(8.$3.$9.$:.$4.)(;.$3.$9.$:.$4.)R3.(<.R5.))(=.$4.R2.))(>.(?.+1000.(10.R3.))(>.(6.$11.(12.(10.R3.)+1000.)=)(>.(?.(13.(10.R3.)(14.(15.R3.)))(16.VhRP,))P,(17.=(14.(15.R3.)))(18.(?.(13.(10.R4.)(14.(15.R4.)))+10000.)(?.+7>000.(10.R4.))))))")
(* [comment removed for export] *).
Proof. rceilb.
  intros st m rid r (WF & _) Hr. dpose WF as (_ & WR & _).
  ddestruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  split; [|split; [exact RBAL| split; [exact RBC| intros Hn; exact (rreserved_disjoint1 _ _ RFr Hn)]]].
  clear RFr. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma rblock_inside st LB m blk : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_ifaceP ()) "P,(19.$1:.O4.O3.)P,(5.VhRP,O4.O2.)P,(1;.$1<.O1.O3.)(1=.$4.Lr,$4.(1=.$1>.Lg,$1>.(1=.$11.Lidx,$11.(>.(6.(2.$4.)(7.$3.$4.(8.$3.$9.$:.$4.)(;.$3.$9.$:.$4.)(1?.$3.$11.(20.O1.))(<.O4.))(=.$4.R3.))(>.(6.$21.(22.R3.)$23.)(>.(6.(2.(24.$1>.$11.))(7.$25.(24.$1>.$11.)(8.$1>.(26.$3.$9.$11.$27.)(28.$3.$9.$:.$11.$27.$29.)(24.$1>.$11.))(;.$1>.(26.$3.$9.$11.$27.)(28.$3.$9.$:.$11.$27.$29.)(24.$1>.$11.))(20.O1.)(2:.O4.))(=.(24.$1>.$11.)(2;.$1>.$11.R2.R1.)))(>.(?.(10.R3.)(2<.O1.))(>.(?.(13.(2<.O1.)(2=.O1.))(13.(10.R3.)(14.(15.R3.))))(>.(?.=(2=.O1.))(>.(?.+1000.(10.R3.))(>.(?.(13.(10.R3.)(14.(15.R3.)))(16.VhRP,))(18.(?.(13.(10.R3.)(14.(15.R3.)))+10000.)(?.+7>000.(10.R3.))))))))))))))")
(* [comment removed for export] *).
Proof. rceilb.
  intros MF MR IN.
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) blk IN) as [BS BR BZ].
  ddestruct BS as (g & idx & SL & _ & _ & IDX & (off & OFF0 & EA & FIT)).
  ddestruct BR as (r & Hr & Hk).
  pose proof (mf_slots _ _ MF (blk_slot blk) g idx SL) as (b & Hm & Efst & Esnd & _).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd.
  pose proof (mf_gmeta _ _ MF g b Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  ddestruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & _ & SPAN) & S16 & _).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  pose proof (rregion_addr_facts st m _ r MR Hr) as (R4 & _ & RC & RI1).
  dexists r, g, idx. split; [exact Hr|]. split; [exact Hk|]. split; [exact SL|].
  pose proof (round_up_pg_ge (r_len r)) as RU.
  rewrite (conc_region' st (blk_slot blk) r Hr) in EA.
  unfold sstart_of in Esnd, SPAN. rewrite Hm in Esnd, SPAN. cbn [default from_option id snd] in Esnd, SPAN. unfold UNIT, IB in *.
  assert (SK : 0 <= get_stride (get_meta_rec st g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SKL : get_stride (get_meta_rec st g) * idx + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Esnd in EA. rceilb.
  assert (RP : 0 < round_up_pg (r_len r)) by lia. specialize (RI1 RP). lia.
Qed.

#[using="Type"] Lemma RHEAP_blocks_nodup_proof : forall s LB m, RHEAP s LB m -> List.NoDup (map blk_id LB).
Proof. rceilb.
  (intros s LB m dd_H; ddestruct dd_H as (st & LB0 & HP & _ & _ & [_ AR])). pose proof (mf_nodup _ _ (MallocFacts_inv2.areach_facts_proof _ _ AR)) as ND.
  eapply Permutation_NoDup; [apply Permutation_map; exact HP|].
  clear -ND. induction LB0 as [|b LB0 IH]; cbn in *; [constructor|].
  inversion ND; subst. constructor; [|apply IH; assumption].
  intros HI. apply H1. apply in_map_iff in HI. ddestruct HI as (b' & E & HI'). apply in_map_iff. exists b'. split; [|exact HI'].
  unfold blk_slot, blk_id in *. rewrite E. reflexivity.
Qed.

#[using="Type"] Lemma RHEAP_block_range_proof : forall s LB m b, RHEAP s LB m -> In b LB -> rblock_range (blk_addr b) (blk_size b).
Proof. rceilb.
  (intros s LB m b dd_H; ddestruct dd_H as (st & LB0 & HP & _ & MR & [_ AR]); intros HIN). pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN0 : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact HIN]).
  ddestruct (rblock_inside st LB0 m b MF MR IN0) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
  pose proof (proj1 (List.Forall_forall _ _) (mf_blocks _ _ MF) b IN0) as [BS BR _].
  ddestruct BS as (g' & idx' & SL' & _ & _ & _ & (off & OFF0 & EA & FIT)). rewrite SL in SL'. inversion SL'; subst g' idx'. clear SL'.
  pose proof (mf_slots _ _ MF (blk_slot b) g idx SL) as (bb & Hm & Efst & Esnd & IDX).
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Hm, Esnd, IDX.
  pose proof (mf_gmeta _ _ MF g bb Hm) as FG. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in FG. cbv zeta in FG.
  ddestruct FG as (_ & _ & _ & LI & _ & _ & _ & _ & (r' & Hr' & _ & B0 & B16 & SPAN) & S16 & SMOD & _).
  change (s_regions (strip st)) with (s_regions st) in Hr'. rewrite <- Efst in Hr'. rewrite Hr in Hr'. inversion Hr'; subst r'. clear Hr'.
  pose proof MR as (WF & _). dpose WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RAL & _ & RC' & RF).
  unfold sstart_of in SPAN. rewrite Hm in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT in SPAN, S16.
  assert (32 <= round_up_pg (r_len r)) by nia.
  unfold rblock_range. rceilb. split; [lia|]. split; [|lia].
  rewrite EA. rewrite (conc_region' st (blk_slot b) r Hr). rewrite Esnd. unfold sstart_of. rewrite Hm. cbn [default from_option id snd].
  replace (r_base r + (snd bb + UNIT + get_stride (get_meta_rec st g) * idx) + UNIT * off)
    with (r_base r + snd bb + 16 + get_stride (get_meta_rec st g) * idx + 16 * off) by (unfold UNIT; lia).
  apply (mod16_slot (r_base r) (snd bb) (get_stride (get_meta_rec st g)) idx off); try assumption; lia.
Qed.

#[using="Type"] Lemma RHEAP_blocks_disjoint_proof : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_ifaceP ()) "Ps,$2>.PLB,(2?.$1<.)Pm,$30.Pb1,$1<.Pb2,$1<.P,(31.VhRP,R5.R4.R3.)P,(1;.$1<.R3.R5.)P,(1;.$1<.R3.R6.)P,(32.(6.$33.(34.R5.)(34.R4.)))(18.(?.(13.(2<.R6.)(2=.R6.))(2<.R5.))(?.(13.(2<.R5.)(2=.R5.))(2<.R6.)))")
(* [comment removed for export] *).
Proof. rceilb.
  (intros s LB m b1 b2 dd_H; ddestruct dd_H as (st & LB0 & HP & _ & MR & [_ AR]); intros I1 I2 NE). pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (IN1 : In b1 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I1]).
  assert (IN2 : In b2 LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact I2]).
  destruct (decide (blk_slot b1 = blk_slot b2)) as [ES|NS].
  - exfalso. apply NE. pose proof (mf_nodup _ _ MF) as ND.
    clear -ND IN1 IN2 ES. induction LB0 as [|b LB0 IH]; [destruct IN1|]. cbn in ND. inversion ND; subst.
    destruct IN1 as [->|IN1], IN2 as [->|IN2]; [reflexivity| | | apply IH; assumption].
    + exfalso. apply H1. rewrite ES. apply in_map_iff. exists b2; auto.
    + exfalso. apply H1. rewrite <- ES. apply in_map_iff. exists b1; auto.
  - destruct (N.eq_dec (fst (blk_slot b1)) (fst (blk_slot b2))) as [EF|NF].
    + exact (mf_blocks_disjoint _ _ MF b1 b2 IN1 IN2 EF NS).
    + ddestruct (rblock_inside st LB0 m b1 MF MR IN1) as (r1 & g1 & i1 & Hr1 & Hk1 & _ & LO1 & HI1 & _).
      ddestruct (rblock_inside st LB0 m b2 MF MR IN2) as (r2 & g2 & i2 & Hr2 & Hk2 & _ & LO2 & HI2 & _).
      pose proof MR as (WF & _). dpose WF as (_ & _ & DJ & _).
      pose proof (lr_lo_group r1 Hk1). pose proof (lr_lo_group r2 Hk2).
      destruct (DJ _ _ _ _ Hr1 Hr2 NF); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rrepfoot_where st m a : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_ifaceP ()) "P,(5.VhRP,O3.O2.)P,(35.O3.O1.)(>.(17.O1.(16.VhRP,))(18.(>.(?.$36.O1.)(17.O1.(13.$36.+3:0.)))(18.(>.(?.$37.O1.)(17.O1.(13.$37.+4.)))(18.(>.(?.$38.O1.)(17.O1.(13.$38.+38.)))(18.(>.(?.$39.O1.)(17.O1.(13.$39.+8.)))(18.(>.(?.$3:.O1.)(17.O1.(13.$3:.+8.)))(18.(17.O1.+10000.)(?.+7>000.O1.))))))))")
(* [comment removed for export] *).
Proof. rceilb.
  intros MR RF. pose proof MR as (WF & _). dpose WF as (_ & WR & _).
  destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
    rceilb; unfold RCTX, RMLOCK, RLIBC, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD in *.
  - lia. - lia. - lia. - lia.
  - ddestruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC).
    destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa) as D. rceilb.
    pose proof (round_up_pg_ge (r_len ra)). lia.
  - ddestruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb). pose proof (rreserved_disjoint1 _ _ RFb) as D. rceilb.
    pose proof (round_up_pg_ge (r_len rb)). lia.
  - destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint1 _ _ RFq) as D. rceilb. lia.
  - lia. - lia.
Qed.

#[using="Type"] Lemma RHEAP_frame_proof : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_ifaceP ()) "Ps,$2>.PLB,(2?.$1<.)Pm,$30.Pm',P,(1.&40.)(2.(1.&8.))PW,(2?.$3;.)P,(31.VhRP,R5.R4.R3.)P,(3<.R2.R4.R3.)P,(3=.$3>.R5.R4.)P,(3?.(24.$11.$11.)(40.VhRP,R7.)R4.)(31.VhRP,R9.R8.R6.)")
(* [comment removed for export] *).
Proof. rceilb.
  (intros s LB m m' W dd_H; ddestruct dd_H as (st & LB0 & HP & Hst & MR & HI); intros MU WM FW). dexists st, LB0. split; [exact HP|]. split; [exact Hst|].
  split; [|exact HI].
  destruct HI as [_ AR]. pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  pose proof MR as (WF & _). dpose WF as ((RS & RPRS) & WR & DJ & WA & WG).
  eapply (rmrep_transport_unowned st m m' W MR MU WM).
  intros lo hi a Hin Ha RF.
  pose proof (proj1 (List.Forall_forall _ _) FW _ Hin) as CW. cbn [fst snd] in CW.
  destruct (rrepfoot_where st m a MR RF) as [AC AW].
  destruct CW as [CW|[CW|(b & Hb & B1 & B2)]]; cbn [fst snd] in *.
  - rceilb. lia.
  - rceilb; unfold RMLOCK, RLIBC, RCTX, RERRNO, RATP, RGOT_SSP, RSSP_GUARD in *. lia.
  - (* [comment removed for export] *)
    assert (INb : In b LB0) by (eapply Permutation_in; [apply Permutation_sym; exact HP| exact Hb]).
    ddestruct (rblock_inside st LB0 m b MF MR INb) as (r & g & idx & Hr & Hk & SL & LOB & HIB & BZ & R4 & RC & RI1).
    destruct RF as [R1|[R2|[R3|[R4'|[(ak & ar & Hak & Rak)|[(b' & gh & Hb' & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
    + unfold RCTX in R1. lia.
    + unfold RMLOCK in R2. lia.
    + unfold RNEED_LOCKS in R3. lia.
    + unfold RPAGE_SIZE in R4'. lia.
    + ddestruct (rarea_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NEr : fst ak <> fst (blk_slot b)) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      pose proof (rarea_lr_lo st ak ar ra WF Hak Hra). pose proof (lr_lo_group r Hk).
      destruct (DJ _ _ _ _ Hra Hr NEr); lia.
    + ddestruct (rgroup_conc st b' gh WF Hb') as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _).
      destruct (N.eq_dec (fst b') (fst (blk_slot b))) as [E|NEr].
      * rewrite E, Hr in Hrb. inversion Hrb; subst rb.
        pose proof (mf_hdr_clear _ _ MF b' gh b r Hb' INb (eq_sym E) ltac:(change (s_regions (strip st)) with (s_regions st); rewrite E; exact Hr)) as HC. rewrite Cb in Rb. lia.
      * pose proof (lr_lo_group rb Kb). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hrb Hr NEr); lia.
    + destruct (N.eq_dec q (fst (blk_slot b))) as [->|NEr].
      * rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (mf_blk_unknown _ _ MF b r INb Hr a ltac:(lia)) as [h Hh]. rewrite Hh in Cq. discriminate.
      * pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Hk). destruct (DJ _ _ _ _ Hq Hr NEr); lia.
    + unfold RGOT_SSP in R8. lia.
    + unfold RSSP_GUARD in R9. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="hRP"] Lemma reservedZ_ref : reservedZ rsegs = ref_reserved.
Proof. rceilb. vm_compute. reflexivity. Qed.

#[using="hRP"] Lemma u64arr_of_rw_cells' : ltac2:(CDefT.buildp (gd_tbl_HP_RMalloc_ifaceP ()) "Pm,P,(1.&40.)(2.(1.&8.))PA,$11.Pn,$41.Pbs,(2?.(1.&8.))Pk,$41.P,(42.$3>.R5.R4.(43.$44.(45.R3.R2.)(46.$44.)))P,(6.(2?.(1.&8.))R3.(47.(48.(1.&40.)(49.=)R2.)))P,(6.$41.R5.(4:.#8.R3.))(4;.$3>.R8.R7.(48.(1.&40.)(49.=)R4.))")
(* [comment removed for export] *).
Proof. rceilb.
  intros m A n bs k [[Hwf HB] HW] -> Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
  split; [exact HB|]. cbn [cells_size csize] in HW. rewrite repeat_length. replace (8 * Z.of_nat k) with (Z.of_nat (n + 0)) by lia. exact HW.
Qed.

(* [comment removed for export] *)
End RP_1.
Ltac rimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Section RP_2. Context {hRP : run_params}.

End RP_2.
