(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free F_malloc_enframe.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Export MallocKit_B2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RMallocKit_B2 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.N"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "Corelib.Init.Logic.eq"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cellval"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cell_read"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.Unknown"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Heap.F_malloc_enframe.rdv"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.mem"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.pans_mem"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Heap.MallocKit_B.agree_on"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Corelib.Init.Logic.ex"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rrepfoot"; "RP_1.rgrp_region_addr"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.wview"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"].



(* [comment removed for export] *)
(* [comment removed for export] *)

Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma rimplT_guard {R} o t (c : bool) (k bail : Malloc.M R) s Q ms :
  (c = true -> rimplT o k s Q ms) -> rimplT o (guard t c k bail) s Q ms.
Proof. intros H. unfold guard. destruct c; [apply H; reflexivity| apply rimplT_undef]. Qed.

#[using="Type"] Lemma rimplT_rd8 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q)) s Q ms -> rimplT o (rd8 st q k) s Q ms.
Proof.
  intros H. unfold rd8. unfold rdv in H.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h]; [exact H|].
  apply rimplT_peek. rewrite peek_ok_pans. exact H.
Qed.

#[using="Type"] Lemma rimplT_rd16 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1))) s Q ms -> rimplT o (rd16 st q k) s Q ms.
Proof. intros H. unfold rd16. apply rimplT_rd8, rimplT_rd8. exact H. Qed.

#[using="Type"] Lemma rimplT_rd32 {R} o st q (k : Z -> Malloc.M R) s Q ms :
  rimplT o (k (rdv pans_mem o st q + 256 * rdv pans_mem o st (aadd q 1)
             + 65536 * rdv pans_mem o st (aadd q 2) + 16777216 * rdv pans_mem o st (aadd q 3))) s Q ms ->
  rimplT o (rd32 st q k) s Q ms.
Proof. intros H. unfold rd32. apply rimplT_rd8, rimplT_rd8, rimplT_rd8, rimplT_rd8. exact H. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rimplT_if {R} o (c : bool) (t1 t2 : Malloc.M R) s Q ms :
  (c = true -> rimplT o t1 s Q ms) -> (c = false -> rimplT o t2 s Q ms) -> rimplT o (if c then t1 else t2) s Q ms.
Proof. intros H1 H2. destruct c; auto. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma rrdv_cur : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B2 ()) "Po,Px,(0.&40.)(1.(0.&8.))Pst,$2.PmX,P,(0.&40.)(1.(0.&8.))Pq,(3.$4.$5.)Pr,$6.Px,(0.&8.)P,(7.VhRP,R5.R4.)P,(8.(1.$6.)(9.$4.$6.(:.$4.$;.$<.$6.)(=.$4.$;.$<.$6.)(>.$4.$5.R4.)(?.R6.))(10.$6.R3.))P,(8.$11.(12.R4.)$13.)P,(14.(15.=(16.$4.$5.R6.))(17.(16.$4.$5.R6.)(18.(19.R5.))))P,Ph,$5.P,(8.$1:.(1;.(1<.R:.(>.$4.$5.R8.))(16.$4.$5.R8.))(1=.R1.))(8.(1.(0.&8.))A1.R<.(1>.(1?.(20.R8.)(16.$4.$5.R9.)))A1.R:.(1>.(1?.(20.R8.)(16.$4.$5.R9.))))P,(21.$22.R9.(1?.(20.R7.)(16.$4.$5.R8.))(23.(0.&8.)R6.(24.(0.&8.))))(8.$5.(25.$26.$27.R<.R;.R9.)(28.&8.R7.))")
(* [comment removed for export] *).
Proof.
  intros o st mX q r x MR Hr Hk Ho AG Hb. unfold rdv.
  destruct (cell_read (get_shadow st (fst q)) (snd q)) as [v|h] eqn:E.
  - destruct (rmrep_shadow_read st mX (fst q) r (snd q) v MR Hr Hk Ho E) as [RD Hv].
    pose proof (bytes_at_read rsegs mX _ [x] 0 1 Hb ltac:(lia) ltac:(cbn; lia)) as RD'. cbn [firstn skipn Z.to_nat] in RD'.
    rewrite Z.add_0_r in RD'. rewrite RD in RD'. inversion RD'. rewrite b8_unsigned by lia. reflexivity.
  - unfold pans_mem. rewrite (conc_region' st q r Hr).
    ddestruct Hb as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn; lia)). cbn in HB. rewrite Z.add_0_r in HB.
    unfold mrd in HB |- *. rewrite (AG h eq_refl).
    destruct (mX (wa (r_base r + snd q))) as [b|] eqn:EMX; [inversion HB; subst; reflexivity|].
    exfalso. dpose MR as ((_ & WR & _) & _). destruct (WR _ _ Hr) as (RB0 & _ & _ & RBC & RF). rceilb.
    pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as D.
    rewrite ref_seg_rom_none in HB; [discriminate|]. rewrite wa_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rwview_ext : forall m m' a, m' a = m a -> wview rsegs m' a = wview rsegs m a.
Proof. intros m m' a E. unfold wview. rewrite E. reflexivity. Qed.

#[using="Type"] Lemma rwr_at_agree : forall m m' A n, wr_at rsegs m A n -> agree_on m m' A n -> wr_at rsegs m' A n.
Proof.
  (intros m m' A n dd_H; ddestruct dd_H as (H0 & H1 & HW); intros AG). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (rwview_ext m m') by (apply AG; lia). apply HW. exact Hi.
Qed.

#[using="Type"] Lemma rrw_cells_agree' : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B2 ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PA,$5.Pcs,(29.$2:.)P,(2;.$22.R4.R2.R1.)P,(2<.R5.R4.R3.(2=.(2>.R2.)))(2;.$22.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

#[using="Type"] Lemma ru64arr_agree' : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B2 ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PA,$5.Pws,(29.(0.&40.))P,(2?.$22.R4.R2.R1.)P,(2<.R5.R4.R3.(30.+8.(2=.(31.(0.&40.)R2.))))(2?.$22.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros m m' A ws [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

#[using="Type"] Lemma ru8arr_agree' : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B2 ()) "Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))PA,$5.Pbs,(29.(0.&8.))P,(32.$22.R4.R2.R1.)P,(2<.R5.R4.R3.(2=.(31.(0.&8.)R2.)))(32.$22.R5.R4.R3.)")
(* [comment removed for export] *).
Proof. intros m m' A bs [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.




(* [comment removed for export] *)
Definition rgrp_region_addr (st : mstate) (a : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B2 ()) "(33.$4.Lrid,$4.(33.$6.Lr,$6.(14.(8.(1.$6.)(9.$4.$6.(:.$4.$;.$<.$6.)(=.$4.$;.$<.$6.)R2.(?.O2.))(10.$6.R1.))(14.(8.$11.(12.R1.)$13.)(14.(15.(20.R1.)O1.)(17.O1.(1?.(20.R1.)(18.(19.R1.)))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma rmrep_transport_agree : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B2 ()) "Pst,$2.Pm,P,(0.&40.)(1.(0.&8.))Pm',Px,(0.&40.)(1.(0.&8.))P,(7.VhRP,R3.R2.)P,Pa,$5.P,(14.(15.=R1.)(17.R1.(34.+2.+40.)))P,(35.R6.R2.)(8.(1.(0.&8.))A1.R5.(1>.R3.)A1.R6.(1>.R3.))P,Pa,$5.P,(14.(15.=R1.)(17.R1.(34.+2.+40.)))P,(36.R7.R2.)P,(37.(8.(1.(0.&8.))(38.$22.R7.(1>.R3.))(39.(0.&8.))))(37.(8.(1.(0.&8.))(38.$22.R7.(1>.R4.))(39.(0.&8.))))(7.VhRP,R6.R4.)")
(* [comment removed for export] *).
Proof.
  (intros st m m' dd_H; ddestruct dd_H as (WF & CX & GL & AR & GR & SH); intros AG WG).
  dpose WF as ((Hres & RPHres) & WR & DJ & WA & WGr).
  assert (TC : forall A cs, rw_cells rsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> rrepfoot st a) -> rw_cells rsegs m' A cs).
  { intros A cs H HP. pose proof (rw_cells_bound rsegs m A cs H). eapply rrw_cells_agree'; eauto. intros a Ha. apply AG; [lia| apply HP; exact Ha]. }
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - ddestruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    pose proof (u64arr_bound rsegs m _ _ C2) as B2. pose proof (u64arr_bound rsegs m _ _ C3) as B3.
    pose proof (u8arr_bound rsegs m _ _ C4) as B4. pose proof (u8arr_bound rsegs m _ _ C5) as B5.
    rewrite actives_length in B2. rewrite usages_length in B3. rewrite unmap_seqs_length in B4. rewrite bouncess_length in B5.
    split; [|split; [|split; [|split; [|split]]]].
    + apply TC; [exact C1 |]. intros a Ha. apply rrepfoot_ctx. cbn in Ha. unfold RCTX in *. lia.
    + eapply ru64arr_agree'; eauto. rewrite actives_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru64arr_agree'; eauto. rewrite usages_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree'; eauto. rewrite unmap_seqs_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
    + eapply ru8arr_agree'; eauto. rewrite bouncess_length. intros a Ha. apply AG; [unfold RCTX in *; lia|]. apply rrepfoot_ctx. unfold RCTX in *. lia.
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
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB].
    ddestruct (WR rid r Hr) as (RB0 & _ & _ & RBC & _). rceilb.
    split.
    + ddestruct HWr as (W0 & W1 & HW). split; [exact W0|]. split; [exact W1|].
      intros i Hi. apply WG; [lia| dexists rid, r; repeat split; auto; lia| apply HW; exact Hi].
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. intros a Ha. apply AG; [lia|].
      eapply (rrepfoot_known st a rid r v Hr Hk ltac:(lia)). replace (a - r_base r) with o by lia. exact Hc.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rmrep_transport_agree' : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B2 ()) "Pst,$2.Pm,P,(0.&40.)(1.(0.&8.))Pm',Px,(0.&40.)(1.(0.&8.))P,(7.VhRP,R3.R2.)P,Pa,$5.P,(14.(15.=R1.)(17.R1.(34.+2.+40.)))P,(3:.(35.R6.R2.)(36.R6.R2.))(8.(1.(0.&8.))A1.R5.(1>.R3.)A1.R6.(1>.R3.))(7.VhRP,R5.R3.)")
(* [comment removed for export] *).
Proof.
  intros st m m' MR AG. eapply rmrep_transport_agree; [exact MR| |].
  - intros a Ha Hf. apply AG; auto.
  - intros a Ha Hg. rewrite (rwview_ext m m'); [tauto|]. apply AG; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma rpres_except_of_munch_nw : ltac2:(CDefT.buildp (gd_tbl_HP_RMallocKit_B2 ()) "PC,Px,$5.SpPW,(29.$3;.)Pm,P,(0.&40.)(1.(0.&8.))Pm',P,(0.&40.)(1.(0.&8.))P,(3<.R3.R2.R1.)P,Pa,$5.P,(14.(15.=R1.)(17.R1.(34.+2.+40.)))P,(37.A1.R7.R2.)(3=.R7.R3.)(3>.R6.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros C W m m' MU HW a Ha Hc.
  assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. rewrite (rwview_ext m m' (wa a) E). tauto.
Qed.





End RP_1.
