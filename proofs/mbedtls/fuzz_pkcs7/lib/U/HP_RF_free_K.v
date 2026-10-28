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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocBlocks MallocFacts_B MallocKit_B MallocModel_B MallocKit_B3 MallocFacts_Bpres.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Export F_free_K.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_HP_RF_free_K () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Heap.MallocRep.ticks_ok"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cellval"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.cell_read"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.get_shadow"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.N"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.Known"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocKit_B.rfree_fp"; "RocqVerifyHarness.AgentSubmission.Heap.F_free_K.hdr_st"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_Bpres.KINV"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_Bpres.ZINV"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.rkind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_kind"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.RKGroup"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ghdr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_groups"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Heap.MallocFacts_B.ci_mptrs"; "RocqVerifyHarness.AgentSubmission.Heap.MallocTree.ptrs_in"].


(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma rfree_fp_hdr_st st pf lo (sp sp' : Z) a : ltac2:(CDefT.buildp (gd_tbl_HP_RF_free_K ()) "P,(0.O6.)P,Pk,$1.P,(2.(3.+1.R1.)(3.R1.+3.))(4.$1.Lw,$1.(5.$6.(7.(8.O6.(9.$:.$1.O5.))(;.(<.$:.$1.O5.)R3.))(=.R1.)))P,(3.O2.O3.)P,(>.(?.O6.O5.)O4.O2.O1.)(>.O6.O4.O3.O1.)")
(* [comment removed for export] *).
Proof.
  intros TK HK HS H. destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
  - right; left. exact H.
  - right; right. ddestruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
    dexists rid, r, w. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

#[using="Type"] Lemma rconc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rpw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rconc_drop by exact H. reflexivity. Qed.
#[using="Type"] Lemma rget_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rrec_drop q : get_meta_rec st' q = get_meta_rec st q. Proof. reflexivity. Qed.

#[using="PTR"] Lemma rmeta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof.
  ddestruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). ddestruct (PM q) as (P1 & P2 & P3).
  unfold meta_cells. rewrite !rpw_drop by assumption. reflexivity.
Qed.

#[using="PTR"] Lemma rctx_head_cells_drop : ctx_head_cells st' = ctx_head_cells st.
Proof.
  ddestruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
  rewrite !rpw_drop by assumption. reflexivity.
Qed.
#[using="PTR"] Lemma ractives_drop : actives st' = actives st.
Proof.
  ddestruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
  change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply rpw_drop. apply PA.
Qed.
#[using="PTR"] Lemma rctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof.
  ddestruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
  destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (rconc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

#[using="PTR"] Lemma rmrep_drop_region m : rmrep st m -> rmrep st' m.
Proof.
  intros MR. dpose MR as (WF & CX & GL & AR & GR & SH). dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  ddestruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact (conj Hres RPHres)|]. split; [|split; [|split]].
    + intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto.
    + intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
      apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto.
    + intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. ddestruct (WA a ar Ha) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
    + intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. ddestruct (WG b gh Hb) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
  - unfold rmrep_ctx. rewrite rctx_head_cells_drop, ractives_drop, rctx_tail_cells_drop.
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). exact CX.
  - exact GL.
  - intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. ddestruct (AR a ar Ha) as (A1 & A2 & A3).
    unfold rarea_rep. rewrite (rconc_drop a) by exact Pa. rewrite rpw_drop by exact Pn. split; [exact A1|]. split; [| exact A3].
    intros k Hk. rewrite rrec_drop, rmeta_cells_drop. apply A2. exact Hk.
  - intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. ddestruct (GR b gh Hb) as (w8 & R & Hw). exists w8.
    rewrite (rconc_drop b) by exact Pb. rewrite rpw_drop by exact Pm. auto.
  - intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
    unfold rshadow_rep. rewrite rget_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End DROP.

#[using="Type"] Lemma rptrs_in_norid st2 LB c rid r m : ltac2:(CDefT.buildp (gd_tbl_HP_RF_free_K ()) "P,(10.O6.O5.O4.)P,(11.O6.(12.$13.))P,(14.VhRP,O6.O1.)P,(5.(15.$16.)(17.$:.$16.(18.$:.$19.$1:.$16.)(1;.$:.$19.$1:.$16.)O3.(1<.O6.))(1=.$16.O2.))P,(5.$1>.(1?.O2.)$20.)P,Pb,(21.$:.$1.)Pgh,$22.P,(5.(15.$22.)(17.(21.$:.$1.)$22.(18.$13.(23.$:.$19.$1.$24.)(25.$:.$19.$1:.$1.$24.$26.)$22.)(1;.$13.(23.$:.$19.$1.$24.)(25.$:.$19.$1:.$1.$24.$26.)$22.)R2.(27.O6.))(1=.$22.R1.))(28.(5.$:.(9.$:.$1.R3.)O3.))P,(29.O6.)(2:.Lx,$:.(28.(5.$:.R1.O3.))O6.)")
(* [comment removed for export] *).
Proof.
  (intros K ZI MR Hr Kr NOG dd_H; ddestruct dd_H as (M1 & M2 & M3 & M4 & M5)).
  pose proof MR as (WF & _). dpose WF as ((Hres & RPHres) & WR & DJ & WA & WG).
  assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
  { (intros q dd_H; ddestruct dd_H as (a & ar & k & Ha & Hk & ->); intros E). cbn in E. ddestruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. (intros dd_H; ddestruct dd_H as (r' & Hr' & NK); intros E). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
  unfold ptrs_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
  - apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
  - apply NGr. exact M1.
  - apply NGr. exact M2.
  - apply NGr. exact M3.
  - apply NGr. exact M4.
  - intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
  - destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
    intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
  - intros g. split; [| split].
    + apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
    + apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
    + destruct (m_mem (get_meta_rec st2 g)) as [b|] eqn:MB; cbn; [| exact I].
      destruct (ZI g b MB) as [[ai Hb]|[]]. exact (NOG b _ Hb).
  - intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. ddestruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
  - intros b gh Hb. split; [exact (NOG b gh Hb)|].
    destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
    assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
    exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.


End RP_1.
