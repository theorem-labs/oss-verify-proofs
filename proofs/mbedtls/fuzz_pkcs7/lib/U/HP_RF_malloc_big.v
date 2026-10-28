(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import VirginDefs Virgin.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocBlocks MallocHINV.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp F_malloc_enf F_malloc_join F_malloc_small F_malloc_entry F_malloc_core F_malloc_bigw F_malloc_big MallocFacts_AM MallocFacts_AMP.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RF_get_meta HP_RMallocKit_B HP_RMallocKit_B2 HP_RMallocKit_B3 HP_RF_mm_syscalls HP_RMallocKit_A HP_RMalloc_fp HP_RF_enframe HP_RF_malloc_enf HP_RAllocSlot_iface HP_RF_malloc_entry HP_RF_malloc_join HP_RF_malloc_small HP_RF_malloc_core HP_RMallocKit_A2 HP_RF_malloc_bigw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require MallocFacts_inv4.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RKitE4.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_malloc_big () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "Corelib.Init.Logic.eq"; "stdpp.gmap.gmap"; "Corelib.Numbers.BinNums.N"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.meta"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_meta_rec"; "stdpp.decidable.prod_eq_dec"; "Corelib.Numbers.BinNums.Z"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.area"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_areas"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.shadow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.sparams"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rrepfoot"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RCTX"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RLIBC"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RGOT_SSP"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "stdpp.base.lookup"; "stdpp.gmap.gmap_lookup"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.block"; "RocqVerifyHarness.AgentSubmission.Heap.MallocBlocks.AREACH_from"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.ref_reserved"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.MMAP_THRESHOLD"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mmap_answer_ok"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_ceil"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.set_tick"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.live_ranges"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.IB"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.UNIT"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.is_err"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.step_seq"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.new_region"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"].



(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma rmrep_ext : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_big ()) "Pst,$0.Pst',$0.Pm,P,(1.&40.)(2.(1.&8.))P,(3.VhRP,R3.R1.)P,(4.(5.$6.$7.$8.$9.)(:.R3.)(:.R4.))P,(4.$;.(<.R4.)(<.R5.))P,Pq,$=.(4.$>.(?.R6.R1.)(?.R7.R1.))P,(4.(5.$=.(10.$6.$7.$11.$12.)(13.$6.$7.$8.$11.$12.$14.)$15.)(16.R6.)(16.R7.))P,(4.(5.$=.(10.$6.$7.$11.$12.)(13.$6.$7.$8.$11.$12.$14.)$17.)(18.R7.)(18.R8.))P,Prid,$6.(4.$19.(1:.R9.R1.)(1:.R:.R1.))P,(4.(1;.(1;.(1;.(1<.(1;.$11.$11.))$11.)$11.)$11.)(1=.R9.)(1=.R:.))(3.VhRP,R:.R9.)")
(* [comment removed for export] *).
Proof. rceilb.
  (intros st st' m dd_H; ddestruct dd_H as (WF & CX & GL & AR & GR & SH); intros ER EC EM EA EG ES ERs).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - destruct WF as [RP0 WF']. split; [exact (rparams_ok_same _ _ RP0 ERs)|]. rewrite ER, EA, EG. exact WF'.
  - eapply rmrep_ctx_ext; [exact EC| exact Hconc| exact CX].
  - intros a ar Ha. rewrite EA in Ha. eapply rarea_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
  - intros b gh Hb. rewrite EG in Hb. eapply rgroup_rep_ext; [exact Hconc| exact (GR b gh Hb)].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply rshadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.

Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^32.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).

#[using="hRP G0"] Lemma rbf_meta : get_meta_rec stF g = big_meta rid n.
Proof. rceilb.
  unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
  rewrite G0. reflexivity.
Qed.

#[using="hRP"] Lemma rbf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof. rceilb.
  intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="hRP"] Lemma rbm_meta : get_meta_rec stM g = big_meta rid n.
Proof. rceilb. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
#[using="hRP"] Lemma rbm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof. rceilb.
  intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

#[using="hRP GN"] Lemma rbf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof. rceilb.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite GN. reflexivity.
Qed.
#[using="hRP"] Lemma rbm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof. rceilb. reflexivity. Qed.
#[using="hRP"] Lemma rbf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof. rceilb.
  intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="hRP HC"] Lemma rbf_ctx : ctx stF = ctx stM.
Proof. rceilb. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
#[using="hRP HC stM"] Lemma rbf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof. rceilb. rewrite rbf_ctx. reflexivity. Qed.

#[using="G0 GN HC"] Lemma rmrep_big_final m : rmrep stM m -> rmrep stF m.
Proof. rceilb.
  intros MR. eapply (rmrep_ext stM stF m MR); try reflexivity.
  - exact rbf_ctx.
  - intros q. destruct (decide (q = g)) as [->|NE]; [rewrite rbf_meta, rbm_meta; reflexivity| rewrite rbf_meta_other, rbm_meta_other by exact NE; reflexivity].
  - rewrite rbf_groups, rbm_groups. reflexivity.
Qed.


(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L18855444922.22L36642235424.1500000?00ES1n2NR1q1r1H2H0S1n2NR". (* [comment removed for export] *)
#[using="hRP NR"] Lemma rbf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof. rceilb.
  unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. rewrite big_ml_eq by lia.
  replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
  cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="hRP"] Lemma rbf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof. rceilb.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
  unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L38068643883.9 L38075212605.18L38075278641.23L38075278641.2400000M00c01J027S3hRP1a3RCB2R12R22R32R42R82R9S3hRP1a3RCB2rq2Rq2RC1DS3hRP2st1a3RCB1b2Rb2rb2Cb3Sb03Sb13RBC1DS3hRP2st1a3RCB2ak3Rak2ra2Ca3Sa03Sa13RB03RBC1D". (* [comment removed for export] *)
#[using="Type"] Lemma rrepfoot_where2 st m a : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_big ()) "P,(3.VhRP,O3.O2.)P,(1>.O3.O1.)(1?.(20.O1.(21.VhRP,))(22.(1?.(23.$24.O1.)(20.O1.(25.$24.+3:0.)))(22.(1?.(23.$26.O1.)(20.O1.(25.$26.+4.)))(22.(1?.(23.$27.O1.)(20.O1.(25.$27.+38.)))(22.(1?.(23.$28.O1.)(20.O1.(25.$28.+8.)))(22.(1?.(23.$29.O1.)(20.O1.(25.$29.+8.)))(22.(20.O1.+10000.)(23.+7>000.O1.))))))))")
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
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59315036641.1700000ES3hRP3hi'2HS1a2Ha1A1B". (* [comment removed for export] *)
#[using="Type"] Lemma rwrapper_munch_keeps st m m' (spv lo : Z) : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_big ()) "P,(3.VhRP,O5.O4.)P,(2:.(2;.(1;.$11.$11.)(2<.$11.$11.(2=.O2.+50.)O2.)(2;.(1;.$11.$11.)(2<.$11.$11.+5=024.(25.+5=024.+4.))(2>.(1;.$11.$11.))))O4.O3.)P,(2?.$30.O4.O3.)P,(23.(21.VhRP,)(2=.O2.+50.))(3.VhRP,O5.O3.)")
(* [comment removed for export] *).
Proof. rceilb.
  intros MR MU WM HS. eapply (rmrep_transport_unowned st m m' _ MR MU WM).
  intros lo' hi' a [E|[E|[]]] Ha RF; inversion E; subst; destruct (rrepfoot_where2 st m a MR RF) as [A B]; rceilb; unfold RCTX, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD in *; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L56765666539.11000006S1a2Ha". (* [comment removed for export] *)
#[using="hRP"] Lemma rpres_except_of_munch_nw C W m m' :
  munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof. rceilb.
  intros MU HW a Ha Hc. assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. unfold wview. rewrite E. auto.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L47033307802.13L59308847360.16L59309007462.19L59315137787.1300000100200E00_SFS3hRP1a2H22rq2Xa2RCS2lo3spv1a2H11X3hRP2H23RCB". (* [comment removed for export] *)
#[using="Type"] Lemma rfp_below_ceiling K st3 stx m lo spv a :
  rmrep st3 m -> spv <= a -> rceil <= a -> ~ (ralloc_fp K st3 lo spv a \/ rfresh_addr stx a).
Proof. rceilb.
  intros MR H1 H2 [[X|[X|[X|(q & rq & Hq & _ & Xa)]]]|[X _]]; try lia.
  - rewrite unsigned_lit in X by lia. rceilb. lia.
  - rceilb; unfold RCTX in *. lia.
  - pose proof MR as (WF & _). dpose WF as (_ & WR & _). ddestruct (WR q rq Hq) as (_ & _ & _ & RC & _). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L2424960062.5 L36644237772.500000600<S1n2HnS1n2Hn". (* [comment removed for export] *)
#[using="hRP"] Lemma rbig_stride n rid : 0 <= n < 2^32 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof. rceilb. intros Hn. rewrite rbf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma rregion_facts_hi : ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_big ()) "Pst,$0.Pm,P,(1.&40.)(2.(1.&8.))Prid,$6.Pr,$9.P,(3.VhRP,R4.R3.)P,(4.(2.$9.)(31.$6.$9.(5.$6.$7.$8.$9.)(32.$6.$7.$8.$9.)R3.(:.R5.))(33.$9.R2.))(22.(23.(25.(34.R3.)(35.(36.R3.)))+4<000.)(23.+7>000.(34.R3.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros st m rid r (WF & _) Hr. dpose WF as (_ & WR & _).
  ddestruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr).
  destruct (rreserved_disjoint _ _ RFr) as (_ & _ & _ & D). exact D.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rAMP_BIG (ram_pre : mstate -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RF_malloc_big ()) "Pst,$0.PLB,(1<.$37.)Pt,$6.Pxa,$11.Pn,$11.P,(38.$39.R5.R4.)P,(1?.(23.$3:.R2.)(20.R2.(3;.+2.+20.)))P,(4.$3<.(3=.(3>.(3?.R5.R7.))(40.(3?.R5.R7.))(25.(25.R3.$41.)$42.)R4.)$43.)P,(4.$3<.(44.R5.)$45.)A1.O1.(46.(47.$0.$6.(48.$49.R6.(25.(25.R5.$41.)$42.)(3?.R7.R9.))))")
(* [comment removed for export] *).


Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L31185294363.11000006S1n2NR". (* [comment removed for export] *)
#[using="hRP"] Lemma ramp_big : rAMP_BIG (am_pre_g ref_reserved).
Proof. rceilb.
  intros st LB t xa n AR NR VOK ISE. unfold am_pre_g. apply AMpre_big_call; [exact (MallocFacts_inv4.areach_ampre_proof _ _ AR)|].
  unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section BIG.
Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : rAMP_BIG ram_pre.

Local Ltac2 Set LiaOrc.tbl := fun () => "02l0@L10068780064.239L10534872771.127L11127069175.198L133980655.111  L13743415799.213L13768873754.78 L14010212115.198L14788761266.198L14790846228.69 L14790999216.220L14791009665.101L15047292336.239L15529344774.198L18460325067.82 L19245567059.206L19652550953.188L19839384372.220L20534863267.130L20534863267.152L20534865073.122L20534922610.236L21122673213.198L21137365920.71 L21908340778.250L21966953530.239L23018907393.122L23018908187.149L23018909203.122L23019172713.127L23883998457.227L2426971491.237 L2426988754.239 L24929764898.239L24983202619.252L25071898026.84 L25071956112.77 L25075859045.151L25276246480.155L25842606013.148L26494861100.232L26559590511.149L26781109470.234L26879286852.235L26879286858.226L28096043745.229L28097878753.81 L28573734967.228L28573882423.251L28573888615.222L29230858956.241L29524288756.137L29524291444.221L29524452599.218L29524502512.99 L30235536431.242L31172730651.76 L31185573393.96 L31187606295.121L31292287353.221L31292563965.99 L32051918277.227L32051918277.236L32419579590.145L32815663543.186L32921336925.198L32927698140.146L35963458466.205L35963458466.238L362166535.256  L36473240265.241L36642204960.239L36642221988.230L36654802212.236L37406016763.76 L37792503789.122L37792504567.149L37792505599.122L37792760709.127L37794366648.137L38715948274.81 L38717783282.205L38717783282.226L38717783282.229L38717783282.235L38829501949.122L39042514146.250L40100991493.235L40100991499.226L40101057172.155L40111253771.137L40111352072.218L40111465364.71 L40655993129.127L4081038656.239 L4111386568.239 L43120029290.71 L43967602815.149L44017328668.239L44281451014.198L44528913860.188L4511410525.240 L45785840312.241L46171598884.77 L46836598598.239L46856919211.239L47026754202.81 L47028754615.186L47028835333.101L47028849972.220L47028999351.100L47028999824.69 L47028999851.71 L47033307802.229L47033307802.247L47039125434.233L47039408043.155L47039473460.226L47039473462.198L47041273605.94 L47098239585.198L47102046774.122L47102049060.122L47102050092.149L47102305886.127L47104223968.146L47478388169.239L49227089372.71 L49227435899.218L49237472487.155L51159435952.99 L51159436024.131L51902538964.239L52300761199.127L52507718435.238L52509552344.205L52509552344.229L52509552344.238L5251256473.198 L56765530045.228L56765667309.122L56765667309.130L56765667309.152L56765667309.222L56765669119.122L56899489284.155L57394141695.238L57477059391.239L57587722062.198L57589765843.71 L57622606836.248L59227879194.102L59308579027.254L59308587409.111L59314873579.249L59314938599.248L59315137787.247L60951222122.77 L61007160479.230L62315620027.71 L6426363069.251 L6428573309.246 L6432603914.248 L6432667910.145 L64618458169.239L66151427842.253L6644529898.239 L66519621351.239L67442659576.129L67491172501.77 L6755913069.238 L6757748886.205 L6757748886.229 L6757748886.238 L67793881970.137L68367801238.236L68367867290.237L68478600214.238L68480440813.205L68480440813.229L68480440813.238L68480700925.234L7131003197.238 L7137551558.205 L7137551558.229 L7137551558.238 L7390272437.239 L8754299652.71  L9266691294.149 00000D00]01A01H01o02502T03<03V04>04^05205C05T05c06706C06m07F07Y08508C08F08d09>09b0:F0:j0;N0<80<Q0<j0=@0>>0>\0?20?>0?^0@J0A90A]0BJ0Ba0C00C@0CF0DA0EP0F>0FR0Fg0G<0GY0Gc0H<0HB0HH0HY0I=0IS0Il0JI0K:0KF0KU0Kd0L40LL0M?0Ma0N:0NS0Nl0O10OU0P90P]0QA0Qe0R40RP0Rf0SB0S`0T30U10UP0Ug0V>0VU0W40W@0WA0WW0X20XH0Xl0Y@0YQ0Z60ZS0[00[F0[\0\@0\A0\M0\Q0\]0\^0\_0\`0\l0]@0]T0]`0]l0^80^90^U0_10_M0_i0`E0`a0a70a=0aV0ag0ah0b40bJ0bK0bf0c80cJ0cb0d70dH0di0eV0eg0fT0fe0g:0g`0h60hB0hC0hm0iS0j?0jI0kB0kn0la0m70mL0mR0n@0nn0o\10B10V11T11n12J12n13@13T13`13l14@14d15?15Z16?16[17717c18A18\18n19@19e1:91:C1:DS3st12xa3rid3st31g1GS1n3st12NR2xa1L2X03rid2LGS3hRP3RCB2sp2lo3st13CLO2LO2xa2X03ridS2st2xaS3hRP3RCB3st12xa2X03rid3st31g1G4Gpos2GCS2sp1yS3hRP2lo3st13CLO2xa1L2X02XC3ridS3hRP3RCB2sp2lo3st13CLO2LO3SPR2xa2X03ridS3hRP3RCB2sp2lo3CLO2LO3SPRS3hRP3RCB2sp2lo3st13CLO2LO3SPR2xa2X03ridS3hRP3RCB2sp2lo3CLO2LO3SPR2xa2X0S3st12xa3rid3st31g1GS1n3st12NR2xa3ridS3hRP3RCB1r2R12R2S3st12xa3rid2rqS2sp3st12xa3rid1a2HaS3st12xa3ridS3hRP2sp2lo3st13CLO2LO2xa1L2X02XC3rid1a2HaS3st12xa1L2X03rid2XI1a2HaS3st12xa1L3rid1a2HoS3st12xa1L2X03rid1a2rq2Xa2D2S1n3st12xa3ridS1nS3st13rid3st31g1G3GI13GI21r2H0S1n3st12xa3rid3st31g1G3ML1S3hRP3RCB1n3st12NR2xa1L2X02XC3rid2LGS3hRP3RCB1n3st12NR2xa1L2X02XC3rid2LGS3hRP3RCB1n3st12NR2xa1L2X02XC3rid2LGS3hRP3RCB1n3st12NR2xa1L2X02XC3rid2LGS3hRP3RCB1n3st12NR2xa1L2X03rid2LG1a4Hout1XS1n3st12NR2xa3rid3st31g1GS1n3st12NR2xa3rid3st31g1GS3st12xa1L3rid3st31g1GS1n3st12NR2xa1L2X02r02XA3rid3st31g1G3GI13GI21q2RU1r1H2H02q02H4S3hRP3RCB2sp2lo3CLO2LO1r2R22R3S3hRP3RCB2sp2lo3CLO2LOS3st12xa3ridS3hRP2sp2lo3st13CLO2LO2xa2X03ridS3hRP3RCB2sp2lo3st13CLO2LO2xa1L2X02XC3rid2XIS1n3st12NR2xa1L2X02XA3rid2LG2XI3st31g1G3GI13GI2S3hRP3RCB2sp2lo3st13CLO2LO2xa2X03ridS1n3st12NR2xa1L2X03rid2LG2XI1a4Hout2rq2Xa1D1HS2sp3st12xa3rid3st31g1GS2sp3st12xa3ridS3st12xa3rid1a1XS1a2HXS3hRP3RCB2sp1n2lo3st13CLO2LO2NR2xa1L2X02XC3rid2LG1a4Hout2A1S1n3st12NR2xa1L2X02XA3rid2LG2XI3st31g1G4Gpos3GI13GI21q1r2NE3off2Ho2B01D1H2H02H1S3hRP3RCB2sp2lo3st13CLO2LO2xa1L2X02XC3rid1a2HaS3st12xa3rid3st31g1GS2sp2lo3st12LO2xa3ridS2sp2lo3st12LO2xa3ridS2sp2lo3st12LO2xa3rid3st31g1GS2sp2lo2LOS3st12xa1L3rid3st31g1G2HfS1n2NRS1n2NRS1n3st12NR2xa3ridS3hRP3RCB2sp2lo3st13CLO2LO2xa2X03ridS3hRP3RCB2sp2lo3CLO2LOS2st3st12xa3st23st32NX2E2S2st3st12xa3st23st31g1G2NX2E2S1n3st12NR2xa1L2X02XA3rid2LG1q1r2NE3off2Ho2B01D1HS3st12xa3ridS3st12xa2X03ridS3st12xa2X03ridS3st12xa3rid1a1XS3st12xa3rid3st31g1G1a1XS1n3st11L3rid3st31g1G3GI13GI23LUB3off4Hfit1q1r1H2H0S2st1n3st12xa3rid3st31g1G3off2Ho1TS1n3st12NR2xa3rid3st31g1GS1n3st12NR2xa3rid3st31g1GS1n3st12NR2xa3rid3st31g1GS3hRPS3hRP3RCB1n3st12NR2xa1L2X02XC3rid2LGS3hRP3RCB1n3st12NR2xa1L2X02XC3rid2LGS3hRP3RCB1n3st12NR2xa1L2X02XC3rid2LGS3hRP3RCB1n3st12NR2xa1L2X02XC3rid2LGS3hRP3RCB1n3st12NR2xa1L2X02XC3rid2LGS2sp2lo2LO1a2HXS2sp2lo3st12LO2xa2X03rid1a1XS2sp2lo3st12xa3rid1a1XS2sp2lo3st12LO2xa2X03rid1a1XS2sp2lo3st12xa3rid3st31g1G1a1XS3st12xa1L3rid1a2HaS1n3st12NR2xa1L2X02r02XA3rid2LG3st31g1G3GI13GI21q1r1H2H02q02H4S3hRP2lo3st13CLO2xa3rid3st31g1GS3hRP2lo3st13CLO2xa3ridS3hRP2lo3st13CLO2xa3ridS3hRP2lo3st13CLO2xa3ridS3hRP2lo3st13CLO2xa3rid3st31g1GS3hRP2lo3CLOFS3st12xa1L3rid3st31g1GS1n3st12xa1L3rid2LG3st31g1GS3hRP3RCB2sp2lo3CLO2LOS3hRP3RCB2sp2lo3st13CLO2LO2xa2X03ridS3st12xa3rid3st31g1GS3st12xa1L3rid2XIS3hRP2sp2lo3st13CLO2LO2xa2X03rid1a2HaS1n3st12xa3rid3st31g1G3off2HoS3st12xa1L3rid3st31g1G2ov3HovS3hRP3RCB2sp2lo3CLO2LOS3st12xa1L3rid3st31g1GS1n3st12NR2xa1L2X03rid2LG3st31g1G2RUSS3st12xa3ridS2xaS3st12xa3ridSSSS3st12xa3ridS3st12xa3rid3st31g1GS3st12xa3rid3st31g1GS3st12xa3ridS3st12xa3ridS3st12xa3ridSS3hRP3RCB3st12xa1L2X02XC3ridS3hRP3RCB3st12xa1L2X02XC3ridS3hRP3RCB3st12xa1L2X02XC3ridS3hRP3RCB3st12xa1L2X02XC3ridS3hRP3RCB3st12xa1L2X02XC3ridS3hRP3RCB3st12xa1L2X02XC3ridS3st12xa1L3rid3st31g1GS1n2NRS1n3st12NR2xa3rid3st31g1GS1n3st12NR2xa3ridSS3st12xa3ridS3st12xa1L3rid3st31g1GFS3st12xa1L3rid3st31g1G1a2HaS3st12xa1L3rid1a1XS3st12xa1L3rid1a1XS3st12xa3rid3st31g1G1a1XS2sp2lo3st12LO2xa3ridS3st12xa3rid1a2HaS3hRP3RCB3st12xa1L2X02XC3rid1a2HaS3hRP3RCB2sp2lo3st13CLO2LO3SPR2xa2X03rid1a2HaS3st12xa3rid1a2HaS3hRP3RCB2sp2lo3st13CLO2LO3SPR2xa2X03rid1a2HaS3st12xa3rid1a2HaS2sp2lo3st12LO2xa3ridS3st12xa2X03rid3st31g1G2rg3GLg3GHg1a1XS3st12xa1L3rid3st31g1GS3st12xa3ridSS3st12xa2X03rid3st31g1G3GI13GI21r3off2Ho1DS3hRP3RCB2sp2lo3CLO2LO3sp'3SP'2xa2X01yS3st12xa2X03rid3st31g1G1r3off2Ho3rq22Xa1H2H0S2st2xa2HrS1n3st12NR2xa1L2X02XA3rid2LG3st31g1G3GI13GI21r3off2Ho1Y1HS3st12xa2X03rid3st31g1G3GI13GI21r3off2Ho1X1DS3hRP2sp2lo3st13CLO2xa2X03rid3st31g1G1r3off2Ho2BC1XS3hRP3RCB2sp2lo3CLO2LOS1n3st12xa3rid1a4HoutS1n2NRS3hRP3RCB3st12xa2X03rid3st31g1G1r3off2Ho2B02BCS3hRP3RCB3st12xa2X03rid3st31g1G1r3off2Ho2B02BCS3hRP3RCB3st12xa2X03rid3st31g1G1r3off2Ho2B02BCS3hRP3RCB3st12xa2X03rid1r3off2Ho2B02BCS3st12xa3rid3st31g1GS1n3st12NR2xa1L2X02r02XA3rid2LG3st31g1G3GI13GI21q1r1H2H02q02H4S1n3st12xa3rid3st31g1G3ML1S1n3st12xa1L3rid3st31g1G3LUBS1n3st12NR2xa1L2X02XA3rid2LG2XI1w2HwS3hRP2sp2lo3CLO2LOS3st12xa3rid3st31g1GS3st12xa3ridS3st12xa3ridS3st12xa3rid3st31g1GS3hRP3RCB1n3st12NR2xa1L2X02XC3rid2LGS3st12xa1L3rid3st31g1G2rq1DS3st12xa1L3rid3st31g1G2rq1DS3hRP3st12xa1L2X02XC3rid3st31g1G1a2HaS3hRP3st12xa1L2X02XC3rid1a1XS3hRP3st12xa1L2X02XC3rid1a1XS3hRP1n3st12NR2xa1L2X02XC3rid2LG3st31g1G1a1XS3hRP3st12xa2X03rid1a2rq2Xa2RCS3st12xa1L3rid3st31g1G1a2HaS3st12xa1L3rid1a1XS3st12xa1L3rid1a1XS1n3st12NR2xa1L2X03rid2LG3st31g1G1a1XS3st12xa3rid3st31g1GS2sp2lo2LOF". (* [comment removed for export] *)
#[using="ram_pre AM AMP"] Lemma rbig_spec : rbig_stmt.
Proof. rceilb.
  pose proof AMP as AMP_BIG. unfold rAMP_BIG in AMP_BIG.
  intros o m0 st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo t m1 errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' st1.
  intros AR MF MR0 TP CLO LO NR BL MR1 TK1 UA1 MI1 ST1 FR1 ERR1 AUX1 PE1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RAM_STACK in LO. unfold MMAP_THRESHOLD in NR.
  rewrite (malloc_core_big_eq st1 n) by (unfold MMAP_THRESHOLD; lia).
  (* [comment removed for export] *)
  riprefixT. rceilb. subst tp. unfold RATP in ERR1. rewrite unsigned_lit in ERR1 by lia.
  unfold RMLOCK.
  step. step. step. step. step. step. step. step. step.
  apply evt_done.
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -48)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp + -48) by (subst sp'; apply unsigned_lit; lia).
  eapply rimplT_mmap_rw.
  { eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
    [ rewrite SP'; exact ST1 | unfold RATP; rewrite unsigned_lit by lia; exact ERR1 | exact MI1 | reflexivity | unfold IB, UNIT; f_equal; lia
    | reflexivity | reflexivity | reflexivity | reflexivity | unfold IB, UNIT; lia | rewrite SP'; lia | rceilb; lia
    | rewrite SP'; unfold RATP; rewrite unsigned_lit by lia; lia | unfold RATP; rewrite unsigned_lit by lia; lia ]. }
  intros ans ms' PO.
  assert (FRAME : forall m2, munch [(bv_unsigned sp' - 80, bv_unsigned sp'); (381128 + -164, 381128 + -164 + 4)] m1 m2 -> wmono rsegs m1 m2 ->
            rw_cells rsegs m2 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] /\ rmrep st1 m2 /\ rauxv_ok m2 (bv_unsigned sp)
            /\ rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m2 /\ unk_agree st1 o m2).
  { intros m2 MU WM. rewrite SP' in MU. split; [|split; [|split; [|split]]].
    - eapply rw_cells_transport; [exact FR1| exact MU| exact WM| cbn; lia].
    - eapply (rwrapper_munch_keeps st1 m1 m2 (bv_unsigned sp + -48) lo MR1); [| exact WM| rceilb; lia].
      eapply munch_weaken; [|exact MU]. intros y; cbn; lia.
    - eapply rauxv_ok_frame; [exact AUX1| exact MU| exact WM|]. unfold RAUXV_CELL.
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
    - eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_of_munch; [exact MU| exact WM|].
      intros a Ha NC. cbn. split; [|split; [|exact I]]; intros HX; apply NC; left; [left; lia| right; left]. rewrite unsigned_lit by lia. lia.
    - eapply unk_agree_munch; [exact UA1| exact MU| |].
      + intros rid r Hr Hk. dpose (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _). pose proof (rregion_facts_hi st1 m1 rid r MR1 Hr) as R3. rceilb. cbn. lia.
      + intros rid r Hr. dpose (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _). rceilb. lia. }
  destruct ans as [e|xa].
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    ddestruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & He).
    cbn [mmap_val]. destruct (mmap_answer_ok_err (s_ceil st1) (live_ranges st1) (n + IB + UNIT) e He) as [-> ->]. cbn [negb].
    apply rimplT_ret.
    unfold RATP in MU2, ERR2. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
    ddestruct (FRAME m2 MU2 WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2).
    replace (ret_pc (Z_to_bv 64 0x40600)) with (Z_to_bv 64 0x40600) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    eapply evt_cut. { eapply rbig_fail1_walk; [exact FR2| exact ST2| lia| lia]. }
    intros ms'' [-> ST3]. apply evt_done. cbn [rcoreQ].
    dexists m2, (Z_to_bv 64 (F_mm_syscalls.mmap_fix_errno e)). deexists 14. split; [reflexivity|].
    split; [exact MR2|]. split; [exact TK1|]. split; [exact MI2|]. split; [exact ST3|].
    split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR2|]. split; [exact AUX2|]. split; [exact PE2|].
    split; [apply mrel_same; reflexivity|]. split; [exact BL|]. repeat split; reflexivity.
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    destruct PO as [AOK [BAD|PO]].
    { (* [comment removed for export] *)
      cbn [mmap_val].
      erewrite (rmmap_rejects_high (s_ceil st1)); [cbn [negb]; apply rimplT_undef| unfold IB, UNIT; lia| rewrite (rmrep_ceil _ _ MR1); lia| exact AOK| exact BAD]. }
    ddestruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & XR2).
    cbn [mmap_val].
    destruct (mmap_answer_ok (s_ceil st1) (live_ranges st1) (n + IB + UNIT) xa) eqn:VOK.
    2:{ cbn [negb]. apply rimplT_undef. }
    cbn [negb].
    ddestruct (mmap_answer_ok_addr (s_ceil st1) (live_ranges st1) (n + IB + UNIT) xa ltac:(unfold IB, UNIT; lia) AOK VOK) as (X0 & XA & XC & XRF & ISE). rewrite ISE.
    rewrite (rmrep_ceil _ _ MR1) in XC.
    unfold RATP in MU2, ERR2. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
    ddestruct (FRAME m2 ltac:(eapply munch_weaken; [|exact MU2]; intros y; cbn; lia) WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2).
    (* [comment removed for export] *)
    unfold new_region.
    set (rid := s_next_rid st1). set (st2 := set_next_rid (N.succ rid) (set_regions (<[rid:={| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}]> (s_regions st1)) st1)).
    assert (Est2 : st2 = fst (new_region RKGroup xa (n + IB + UNIT) st1)) by reflexivity.
    pose proof (mf_ptrs _ _ MF) as [PT0 FRESH0].
    assert (PT1 : ptrs_in (fun r => r <> rid) st1).
    { eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. unfold st1. cbn. intros ->. lia. }
    destruct (FRESH0 rid ltac:(subst rid; unfold st1; cbn; lia)) as [FRr FRs].
    set (L := mmap_len (n + IB + UNIT)).
    assert (EL : L = round_up_pg (n + IB + UNIT)) by apply mmap_len_round_up.
    pose proof (round_up_pg_ge (n + IB + UNIT)) as LG. rewrite <- EL in LG, XC, XRF.
    unfold F_mm_syscalls.mmap_raw in ST2 |- *. cbn [negb] in ST2 |- *. fold L. fold L in ST2.
    assert (ELm : mmap_len (n + IB + UNIT) = L) by reflexivity. clearbody L. rceilb. unfold IB, UNIT in LG.
    set (mz := apply_zeros m2 [(wa xa, Z_to_bv 64 L)]).
    assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + L <= a) -> mz (wa a) = m2 (wa a)).
    { intros a Ha Ho. unfold mz. apply (zeros_outside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
    assert (ZI : forall a, xa <= a < xa + L -> mz (wa a) = Some (b8 0)).
    { intros a Ha. unfold mz. apply (zeros_inside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
    assert (MRz : rmrep st2 mz).
    { rewrite Est2. eapply (rmrep_new_region st1 m2 mz xa (n + IB + UNIT) RKGroup MR2 PT1 FRs X0 XA ltac:(unfold IB, UNIT; lia));
        rewrite <- ?EL; [rceilb; exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
    fold mz in ST2 |- *.
    (* [comment removed for export] *)
    pose proof MR1 as (WF1 & _). dpose WF1 as ((RS1 & RPRS1) & WR1 & _).
    assert (XI : xa + L <= 0x10000 \/ 0x7e000 <= xa).
    { assert (RFimg : ranges_free ref_reserved xa L = true).
      { apply ranges_free_intro. intros b k HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS1. exact HI. }
      apply (rreserved_disjoint1 _ _ RFimg). lia. }
    assert (MIz : mem_inv rsegs mz).
    { unfold mz. apply (mem_inv_zeros rsegs m2 xa L); try lia; [exact MI2|]. intros w Hw. apply ref_ro_addr_false. lia. }
    assert (FRz : rw_cells rsegs mz (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
    { eapply rrw_cells_agree; [exact FR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
    assert (TKz : ticks_ok st2) by (rewrite Est2; exact TK1).
    assert (UAz : unk_agree st2 o mz).
    { eapply (unk_agree_transfer st1 st2 o m2 mz UA2). intros q r Hq Hk.
      rewrite Est2 in Hq. destruct (rnr_lookup_inv st1 xa (n + IB + UNIT) RKGroup q r Hq) as [[-> ->]|[NE Hq1]].
      - right. intros off h Ho Hc. exfalso. rewrite Est2 in Hc. rewrite (rnr_shadow st1 xa (n + IB + UNIT) RKGroup) in Hc.
        unfold get_shadow in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc. rewrite cell_read_shadow0 in Hc. discriminate.
      - left. split; [exact Hq1|]. split; [rewrite Est2; apply rnr_shadow|]. split; [intros off X; exact X|].
        intros off h Ho Hc NG. ddestruct (WR1 q r Hq1) as (B0 & _ & _ & BC & _). rceilb.
        pose proof (rnr_old_disjoint st1 xa (n + IB + UNIT) ltac:(rewrite <- EL; exact XRF) q r Hq1) as D.
        pose proof (lr_lo_group r Hk). rewrite <- EL in D. apply ZO; lia. }
    (* [comment removed for export] *)
    riprefixT.
    replace (ret_pc (Z_to_bv 64 0x40600)) with (Z_to_bv 64 0x40600) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof (mf_ctx _ _ MF) as FC. ddestruct FC as (FC1 & FC2 & FC3 & FC4 & FC5 & FC6).
    change (ctx (strip st)) with (ctx st) in FC1, FC2, FC3, FC4.
    eapply evt_cut.
    { eapply (rbig_seq_walk sp gp (Z_to_bv 64 381128)) with (st := st2) (lo := lo);
        [exact MRz| rewrite Est2; exact FC4| rewrite unsigned_lit by lia; lia| exact FRz| exact ST2| lia| rceilb; lia| exact MIz]. }
    (intros ms1 dd_H; ddestruct dd_H as (wa0 & wa1 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & MR3)).
    apply evt_done.
    (* [comment removed for export] *)
    assert (MUz : munch [(xa, xa + L)] m2 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
    assert (WMz : wmono rsegs m2 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono rsegs m2 xa L); try lia; exact Hw).
    assert (AUXz : rauxv_ok mz (bv_unsigned sp)).
    { eapply rauxv_ok_frame; [exact AUX2| exact MUz| exact WMz|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
    assert (AUX3 : rauxv_ok m3 (bv_unsigned sp)).
    { eapply rauxv_ok_frame; [exact AUXz| exact MU3| exact WM3|]. unfold RAUXV_CELL, RCTX.
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor. }
    assert (ERRz : rw_cells rsegs mz (381128 + -164) [C4 errv]).
    { eapply rrw_cells_agree; [exact ERR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
    assert (ERR3 : rw_cells rsegs m3 (381128 + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERRz| exact MU3| exact WM3|]. unfold RCTX. cbn. lia. }
    assert (Hconc2 : forall q, fst q <> rid -> conc st2 q = conc st1 q) by (intros q Hq; rewrite Est2; apply rnr_conc; exact Hq).
    assert (BL2 : brk_link_ps (step_seq st2) s).
    { eapply (brk_link_ps_ext st1); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| | exact BL].
      intros rb ob Hb. transitivity (conc st2 (rb, ob)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
      apply Hconc2. cbn. ddestruct PT1 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite Hb in P7. exact P7. }
    assert (TK2' : ticks_ok (step_seq st2)) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); exact TKz).
    eapply AM.
    { apply (AMP_BIG st LB t xa n AR); [unfold MMAP_THRESHOLD; lia| exact VOK| exact ISE]. }
    { exact MR3. }
    { exact TK2'. }
    { exact BL2. }
    { rewrite SP'. eapply rauxv_ok_weaken; [exact AUX3| rceilb; lia]. }
    { rewrite SP'. exact ST3. }
    { rceilb; lia. }
    { rewrite SP'. unfold RAM_STACK. lia. }
    { unfold RATP. rewrite unsigned_lit by lia. exact ERR3. }
    { exact MI3. }
    { reflexivity. }
    intros st3 mo s' ms' PO3 BL3.
    ddestruct PO3 as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m4 & errv4 & -> & MI4 & ST4 & ERR4 & AUX4 & PE4 & MR4 & TK4 & PSM & PSF & PSO & REL).
    rewrite SP' in ST4, AUX4, PE4. unfold RATP in ERR4. rewrite unsigned_lit in ERR4 by lia.
    replace (ret_pc (Z_to_bv 64 0x406f4)) with (Z_to_bv 64 0x406f4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    lazymatch type of FR3 with rw_cells _ _ _ ?cs => assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -48) cs) end.
    { eapply rpres_except_rw_cells; [exact PE4| exact FR3|]. intros a Ha. cbn in Ha. eapply (rfp_below_ceiling _ st3 _ m4); [exact MR4| lia| rceilb; lia]. }
    assert (RR2 : s_regions (step_seq st2) !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
    { rewrite step_seq_eq. destruct (c_seq (ctx st2) =? 255); (rewrite Est2; apply rnr_lookup_new). }
    assert (RR3 : s_regions st3 !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
    { destruct (amr_regions _ _ _ REL rid _ RR2) as (r' & Hr' & K' & B' & L' & G'). rewrite Hr'. f_equal. apply G'. reflexivity. }
    assert (PT2 : ptrs_in (fun q => q <> rid) (step_seq st2)) by (apply ptrs_in_step_seq; rewrite Est2; apply ptrs_in_new_region; exact PT1).
    assert (PT3 : ptrs_in (fun q => q <> rid) st3).
    { apply (amr_ptrs _ _ _ REL); [|exact PT2]. intros q rq Hq Hk ->. rewrite RR3 in Hq. inversion Hq; subst. apply Hk. reflexivity. }
    dpose MR4 as (WF4 & _ & (ML4 & _) & _). dpose WF4 as ((RS4 & RPRS4) & WR4 & DJ4 & _).
    assert (RS3 : s_reserved st3 = ref_reserved) by exact RS4.
    (* [comment removed for export] *)
    assert (PE14 : forall stF, s_reserved stF = s_reserved st ->
              (forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a) ->
              rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m4).
    { intros stF RSF HFP.
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU2| exact WM2|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC; left; left; lia. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X. apply NC.
        do 4 right. split; [rceilb; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      eapply rpres_except_trans. { eapply rpres_except_of_munch; [exact MU3| exact WM3|]. intros a Ha NC. cbn. unfold RCTX in *.
        split; [|split; [|exact I]]; intros X; apply NC; left; [right; right; left; unfold RCTX; lia| right; right; left; unfold RCTX; lia]. }
      eapply rpres_except_mono; [exact PE4|]. intros a [X|X]; [apply (HFP a X)|].
      do 4 right. eapply (rfresh_addr_anti st (step_seq st2)); [| |exact X].
      { transitivity (s_reserved st2); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| rewrite Est2; reflexivity]. }
      intros q rq Hq. exists rq. split; [|repeat split; auto; lia].
      transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
      rewrite Est2, rnr_lookup_old; [exact Hq|]. intros ->. unfold st1 in Hq. cbn in Hq. fold rid in FRr. unfold st1 in FRr. cbn in FRr. rewrite FRr in Hq. discriminate. }
    destruct mo as [g|].
    + (* [comment removed for export] *)
      apply rimplT_ret.
      destruct (amr_result _ _ _ REL g eq_refl) as [G0 MSL].
      dpose (rmeta_chunk_facts st3 m4 g MR4 MSL) as (_ & Gpos & GC & GI1 & GI2 & GRG & (ridg & rg & Hrg & Krg & GLg & GHg)).
      set (G := conc st3 g) in *.
      assert (HG : bv_unsigned (pw st3 (Some g)) = G) by (unfold pw, oconc; fold G; apply wz_unsigned; rceilb; lia).
      assert (GN3 : forall off, (s_groups st3) !! (rid, off) = None).
      { intros off. destruct ((s_groups st3) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
        ddestruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
      assert (AN3 : forall off, (s_areas st3) !! (rid, off) = None).
      { intros off. destruct ((s_areas st3) !! (rid, off)) as [ar|] eqn:E; [|reflexivity].
        ddestruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
      assert (SHN3 : (s_shadow st3) !! rid = None).
      { rewrite (amr_shadow _ _ _ REL). transitivity (s_shadow st2 !! rid); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
        rewrite Est2. exact FRs. }
      assert (HC3 : c_mmap_counter (ctx st3) = c_mmap_counter (ctx st)).
      { rewrite (amr_counter _ _ _ REL). transitivity (c_mmap_counter (ctx st2)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
        rewrite Est2. reflexivity. }
      eapply evt_cut.
      { eapply (rbig_succ_walk st3 m4 g rid xa n (c_mmap_counter (ctx st)) lo MR4 TK4 G0 MSL RR3 GN3 AN3 SHN3 HC3 FC1 ltac:(unfold MMAP_THRESHOLD; lia) ltac:(rceilb; lia) sp gp (Z_to_bv 64 381128));
          [exact HG| exact FR4| exact ST4| lia| exact MI4]. }
      (intros ms5 dd_H; ddestruct dd_H as (a0' & a1' & m7 & -> & MU7 & WM7 & MI7 & ST7 & FR7 & MR7 & TK7)).
      apply evt_done. cbn [rcoreQ].
      set (stF := big_final st3 g rid n).
      rewrite (rbf_counter st3 g rid n (c_mmap_counter (ctx st)) HC3).
      change (pw st3 (Some g)) with (pw stF (Some g)).
      exists (rid, 0), {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}, m7, errv4. deexists 17.
      split; [reflexivity|].
      assert (MRF : rmrep stF m7) by (apply (rmrep_big_final st3 g rid n _ G0 (GN3 0) HC3); exact MR7).
      split; [exact MRF|].
      split; [exact TK7|].
      assert (STRIDE : get_stride (big_meta rid n) = L - 16) by (rewrite rbig_stride by lia; rewrite <- EL; reflexivity).
      assert (NL : forall q rq, (s_regions st3) !! q = Some rq -> q <> rid -> xa + L <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= xa).
      { intros q rq Hq NE. destruct (DJ4 q rq rid _ Hq RR3 NE) as [D|D]; cbn [r_base r_len lr_lo r_kind] in D; rewrite <- ?EL in D; [|lia]. pose proof (lr_lo_ge rq). lia. }
      split.
      { (* [comment removed for export] *)
        assert (UA3 : unk_agree (step_seq st2) o m3).
        { eapply (unk_agree_transfer st2 (step_seq st2) o mz m3 UAz). intros q r Hq Hk. left.
          assert (Hq2 : s_regions st2 !! q = Some r) by (revert Hq; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); intros Hq; exact Hq).
          split; [exact Hq2|]. split; [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
          split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
          intros off h Ho Hc NG. pose proof MRz as (WFz & _). dpose WFz as (_ & WRz & _).
          ddestruct (WRz q r Hq2) as (B0 & _ & _ & BC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). rceilb.
          apply MU3. rewrite wa_unsigned by lia. cbn. unfold RCTX. lia. }
        assert (UA4 : unk_agree st3 o m4).
        { eapply (unk_agree_transfer (step_seq st2) st3 o m3 m4 UA3). intros q r Hq Hk. left.
          assert (Hq2 : s_regions (step_seq st2) !! q = Some r).
          { destruct ((s_regions (step_seq st2)) !! q) as [r2|] eqn:E.
            - destruct (amr_regions _ _ _ REL q r2 E) as (r' & Hr' & K' & _ & _ & G'). rewrite Hq in Hr'. inversion Hr'; subst r'. f_equal. symmetry. apply G'. rewrite <- K'. exact Hk.
            - exfalso. exact (amr_new _ _ _ REL q r Hq E Hk). }
          split; [exact Hq2|]. split; [unfold get_shadow; rewrite (amr_shadow _ _ _ REL); reflexivity|].
          split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; exact (amr_groups _ _ _ REL)|].
          intros off h Ho Hc NG. ddestruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq). rceilb.
          refine (proj1 (PE4 (r_base r + off) ltac:(lia) _)).
          intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
          - lia.
          - rewrite unsigned_lit in X by lia. pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). lia.
          - unfold RCTX in X. pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). lia.
          - assert (NE : q2 <> q) by (intros ->; rewrite Hq in Hq'; inversion Hq'; subst; apply Kq2; exact Hk).
            pose proof (lr_lo_group r Hk). destruct (DJ4 q2 rq2 q r Hq' Hq NE); lia.
          - pose proof (rfresh_live_region (step_seq st2) (r_base r + off) q r X Hq2) as Y. pose proof (lr_lo_group r Hk). lia. }
        eapply (unk_agree_transfer st3 stF o m4 m7 UA4). intros q r Hq Hk. change (s_regions stF) with (s_regions st3) in Hq.
        destruct (N.eq_dec q rid) as [->|NE].
        - right. rewrite RR3 in Hq. inversion Hq; subst r. cbn [r_len]. intros off h Ho Hc.
          change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid) in Hc.
          rewrite cell_read_hh0 in Hc by (exact SHN3 || lia). destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T.
          dexists (rid, 0), (mkGhdr (Some g) 0). split; [|cbn; lia]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)). apply lookup_insert_eq.
        - left. split; [exact Hq|]. split; [apply rbf_shadow_other; exact NE|].
          split. { (intros off dd_H; ddestruct dd_H as (b & gh & Hb & Hf & Ho)). dexists b, gh. split; [|auto]. unfold stF. rewrite (rbf_groups st3 g rid n (GN3 0)).
                   rewrite lookup_insert_ne; [exact Hb|]. intros <-. cbn in Hf. congruence. }
          intros off h Ho Hc NG. ddestruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). rceilb.
          pose proof (NL q r Hq NE). pose proof (lr_lo_group r Hk). pose proof (GRG q r Hq Hk).
          apply MU7; rewrite wa_unsigned by lia; cbn; unfold RCTX; lia. }
      split; [exact MI7|]. split; [exact ST7|]. split; [exact FR7|].
      assert (ERR8 : rw_cells rsegs m7 (381128 + -164) [C4 errv4]).
      { eapply rw_cells_transport; [exact ERR4| exact MU7| exact WM7|]. cbn. unfold RCTX. lia. }
      split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR8|].
      assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
      { intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
        right; right; right. dexists q, rq. split; [exact Hq| split; [exact Kq| exact Xa]]. }
      assert (PE18 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m7).
      { eapply rpres_except_trans. { apply (PE14 stF); [change (s_reserved stF) with (s_reserved st3); rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
        eapply rpres_except_trans.
        { eapply rpres_except_of_munch; [exact MU7| exact WM7|]. intros a Ha NC. cbn. split; [|split; [|split; [|exact I]]]; intros X; apply NC.
          - left. right; right; right. dexists ridg, rg. split; [exact Hrg|]. split; [exact Krg|]. lia.
          - do 4 right. split; [rceilb; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia].
          - left. right; right; left. unfold RCTX in *. lia. }
        apply rpres_except_refl. }
      split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m7 m1 m7); [exact MR0| exact MRF| exact AUX1| exact PE18| rceilb; lia| lia]. }
      assert (MRELF : mrel st stF).
      { split.
        - intros q rq Hq.
          assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
          assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
          { transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
            rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
          destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _).
          exists r'. split; [|repeat split; auto]. exact Hr'.
        - change (s_next_rid stF) with (s_next_rid st3). pose proof (amr_next_rid _ _ _ REL) as NX.
          assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
          rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
        - change (s_reserved stF) with (s_reserved st3). rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
      split. { eapply rpres_except_trans; [| exact PE18]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
               eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
      rewrite (rbf_meta st3 g rid n G0). rewrite STRIDE. cbn [fst snd r_base r_len].
      split. { intros a Ha. do 4 right. split; [rceilb; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      split. { unfold u32. Z.div_mod_to_equations. lia. }
      assert (ML1 : 32 <= big_ml n < 2^40) by (rewrite big_ml_eq by lia; Z.div_mod_to_equations; lia).
      pose proof (round_up_pg_4115 n ltac:(lia)) as RU. rewrite <- EL in RU.
      assert (LUB : L <= n + 4115) by (rewrite RU; Z.div_mod_to_equations; lia).
      rewrite <- big_ml_eq in RU by lia.
      split.
      { (* [comment removed for export] *) constructor; rewrite ?(rbf_meta st3 g rid n G0), ?STRIDE; cbn [m_mem m_last_idx m_avail m_freed m_freeable m_maplen m_sizeclass big_meta fst snd r_kind r_len].
        - reflexivity.
        - exact RR3.
        - reflexivity.
        - lia.
        - reflexivity.
        - lia.
        - lia.
        - rewrite <- EL. lia.
        - lia.
        - rewrite RU. Z.div_mod_to_equations. lia.
        - lia.
        - lia.
        - lia.
        - intros b' gh Hb' Hf. unfold stF in Hb'. rewrite (rbf_groups st3 g rid n (GN3 0)) in Hb'.
          destruct (decide (b' = (rid, 0))) as [->|NEb]; [cbn; lia|].
          rewrite lookup_insert_ne in Hb' by congruence. destruct b' as [b1 b2]. cbn in Hf. subst b1. rewrite GN3 in Hb'. discriminate.
        - change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
          rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + 16 + (L - 16) * 0 - 4 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        - intros off Ho Hfit. Z.div_mod_to_equations. lia.
        - unfold stF. rewrite rbf_slots. replace (0 + 16 + (L - 16) * 0) with 16 by lia. apply lookup_insert_eq.
        - exact MSL.
        - lia.
        - lia.
        - lia.
        - lia.
        - right. repeat split; lia. }
      split. { (* [comment removed for export] *) intros _ ov Hov. cbn [fst snd] in Hov |- *.
               rewrite (rbf_meta st3 g rid n G0), STRIDE in Hov.
               change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
               apply (hh0_virgin (put_meta g (big_metaA rid) st3) rid 16 (L - 16 - 4) SHN3); lia. }
      split. { intros _. unfold F_malloc_enframe.rdv. change (get_shadow stF (fst (rid, 0))) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
               cbn [fst snd]. rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + (16 + (L - 16) * 0) + -3 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      split; [exact MRELF|].
      split. { eapply (brk_link_ps_ext st3); [reflexivity| intros; reflexivity| exact BL3]. }
      repeat split; assumption.
    + (* [comment removed for export] *)
      cbn [pw oconc].
      riprefixT.
      eapply evt_cut.
      { apply rbig_fail2a_walk. exact ML4. }
      intros ms2 ->. apply evt_done.
      eapply rimplT_munmap.
      { eapply (rmunmap_spec) with (A := xa) (L := n + IB + UNIT) (lo := lo);
          [ rewrite unsigned_lit by lia; exact ST4 | rewrite unsigned_lit by lia; exact ERR4 | exact MI4 | reflexivity | unfold IB, UNIT; f_equal; lia
          | lia | rewrite ELm; lia | unfold IB, UNIT; lia | rewrite unsigned_lit by lia; lia
          | rewrite unsigned_lit by lia; rewrite unsigned_lit by lia; lia | rewrite ELm; left; rceilb; lia
          | rewrite ELm, unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia ]. }
      intros ans2 ms3 PM. unfold rmunmap_post in PM.
      ddestruct PM as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & He6).
      rewrite (munmap_answer_ok_range ans2 He6). apply rimplT_ret.
      rewrite ELm in MU6. rewrite !unsigned_lit in MU6 by lia. rewrite unsigned_lit in ST6 by lia. rewrite unsigned_lit in ERR6 by lia.
      replace (ret_pc (Z_to_bv 64 0x407cc)) with (Z_to_bv 64 0x407cc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      lazymatch type of FR4 with rw_cells _ _ _ ?cs => assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp + -48) cs) end.
      { eapply rrw_cells_agree; [exact FR4|]. intros a Ha. cbn in Ha. apply MU6. rewrite wa_unsigned by lia. cbn. rceilb. lia. }
      eapply evt_cut. { eapply rbig_fail2b_walk; [exact FR6| exact ST6| lia| lia]. }
      intros ms4 [-> ST7]. apply evt_done. cbn [rcoreQ].
      set (stF := drop_region rid st3).
      assert (MRF : rmrep stF m6).
      { eapply (rmrep_drop_region st3 m4 m6 rid _ MR4 RR3 PT3). intros a Ha Hout Hin. cbn [r_base r_len lr_lo r_kind] in Hout.
        rewrite <- EL in Hout.
        assert (A1 : a < rceil /\ (a + 1 <= 381128 + -164 \/ 381128 + -164 + 4 <= a) /\ (a < xa \/ xa + L <= a)).
        { destruct Hin as [X|[X|[X|[X|(q & rq & Hq & Xa)]]]];
            [rceilb; unfold RMLOCK in *; lia| rceilb; unfold RLIBC in *; lia| rceilb; unfold RGOT_SSP in *; lia| rceilb; unfold RSSP_GUARD in *; lia|].
          ddestruct (WR4 q rq Hq) as (_ & _ & _ & RC & RFq). pose proof (rreserved_disjoint _ _ RFq) as (_ & _ & _ & D). pose proof (lr_lo_ge rq).
          split; [lia|]. split; [lia|].
          destruct (N.eq_dec q rid) as [->|NE]; [rewrite RR3 in Hq; inversion Hq; subst; cbn [lr_lo r_kind r_base r_len] in Xa; lia|].
          destruct (DJ4 q rq rid _ Hq RR3 NE) as [D2|D2]; cbn [r_base r_len lr_lo r_kind] in D2; rewrite <- ?EL in D2; lia. }
        rceilb.
        apply MU6; rewrite wa_unsigned by lia; cbn; lia. }
      assert (HFPF : forall a, ralloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> rmalloc_fp st stF lo (bv_unsigned sp) a).
      { intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
        right; right; right. dexists q, rq. split; [|split; [exact Kq|exact Xa]].
        unfold stF. rewrite rdr_lookup_old; [exact Hq|]. intros ->. rewrite RR3 in Hq. inversion Hq; subst. apply Kq. reflexivity. }
      assert (PE16 : rpres_except (rmalloc_fp st stF lo (bv_unsigned sp)) m1 m6).
      { eapply rpres_except_trans. { apply (PE14 stF); [unfold stF, drop_region; cbn [s_reserved set_shadow set_regions]; rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
        eapply rpres_except_of_munch_nw; [exact MU6|]. intros a Ha NC. cbn.
        split; [|split; [|split; [|exact I]]]; intros X; apply NC; [left; left; lia| left; right; left; rewrite unsigned_lit by lia; lia|].
        do 4 right. split; [rceilb; lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      exists m6, (F_mm_syscalls.rg_errno ans2 errv4). deexists 14. split; [reflexivity|].
      split; [exact MRF|]. split; [apply rticks_ok_drop_region; exact TK4|]. split; [exact MI6|]. split; [exact ST7|].
      split; [unfold RATP; rewrite unsigned_lit by lia; exact ERR6|].
      split. { eapply (rauxv_ok_malloc_fp st stF lo (bv_unsigned sp) m0 m6 m1 m6); [exact MR0| exact MRF| exact AUX1| exact PE16| rceilb; lia| lia]. }
      assert (MRELF : mrel st stF).
      { split.
        - intros q rq Hq.
          assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
          assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
          { transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
            rewrite Est2, rnr_lookup_old by exact NE. exact Hq. }
          destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _).
          exists r'. split; [|repeat split; auto]. unfold stF. rewrite rdr_lookup_old by exact NE. exact Hr'.
        - unfold stF, drop_region. cbn [s_next_rid set_shadow set_regions]. pose proof (amr_next_rid _ _ _ REL) as NX.
          change (s_next_rid (step_seq st2)) with (s_next_rid (step_seq st2)) in NX.
          assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
          rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
        - unfold stF, drop_region. cbn [s_reserved set_shadow set_regions]. rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
      split. { eapply rpres_except_trans; [| exact PE16]. eapply rpres_except_mono; [exact PE1|]. intros a Ha.
               eapply rmalloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
      split; [exact MRELF|].
      split.
      { eapply (brk_link_ps_ext st3); [reflexivity| | exact BL3]. intros rb ob Hb. unfold stF. apply rdr_conc. cbn.
        ddestruct PT3 as (_ & _ & _ & _ & _ & _ & P7 & _). rewrite Hb in P7. exact P7. }
      repeat split; assumption.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End BIG.

End RP_1.
