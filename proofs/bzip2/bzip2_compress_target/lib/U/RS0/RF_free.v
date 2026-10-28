(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep Arr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_malloc_free F_malloc_enframe MallocBlocks MallocHINV MallocFacts_B. (* [comment removed for export] *) From Stdlib Require ZArith NArith List Lia Bool. From stdpp Require gmap. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require STree Malloc MallocCtrl Prog. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocRep MallocTree MallocBlocks MallocFacts_B. From Stdlib Require Lia. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require MallocKit_A MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres F_mm_syscalls F_ntf F_free_C.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_free.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_free.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_Bpres OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_mm_syscalls OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_ntf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_free_C OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_free.F_free_K OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_free.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_get_meta RF_mm_syscalls.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0 Require RF_free_A RF_free_B RF_free_C RF_ntf.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require F_free.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module RF_free_K.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
Import OssFuzzTheorems.bzip2.bzip2_compress_target.images.Ubsan.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_malloc_free OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocBlocks OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocModel_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocKit_B3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.MallocFacts_Bpres.
Export OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA.F_free.F_free_K.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocRep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocTree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RMallocKit_B3.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.STree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Malloc OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.MallocCtrl OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Monad OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec.Prog.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.RunW.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLia.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilLiaP.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
Lemma rfree_fp_hdr_st st pf lo (sp sp' : Z) a : ticks_ok st ->
  (forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
  sp' <= sp -> rfree_fp (hdr_st st pf) lo sp' a -> rfree_fp st lo sp a.
Proof.
  intros TK HK HS H. destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
  - right; left. exact H.
  - right; right. cps_destruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
    exists rid, r, w. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rconc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rpw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rconc_drop by exact H. reflexivity. Qed.
Lemma rget_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rrec_drop q : get_meta_rec st' q = get_meta_rec st q. Proof. reflexivity. Qed.

Lemma rmeta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof.
  cps_destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). cps_destruct (PM q) as (P1 & P2 & P3).
  unfold meta_cells. rewrite !rpw_drop by assumption. reflexivity.
Qed.

Lemma rctx_head_cells_drop : ctx_head_cells st' = ctx_head_cells st.
Proof.
  cps_destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
  rewrite !rpw_drop by assumption. reflexivity.
Qed.
Lemma ractives_drop : actives st' = actives st.
Proof.
  cps_destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
  change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply rpw_drop. apply PA.
Qed.
Lemma rctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof.
  cps_destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
  destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (rconc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

Lemma rmrep_drop_region m : rmrep st m -> rmrep st' m.
Proof.
  intros MR. cps_pose MR as (WF & CX & GL & AR & GR & SH). cps_pose WF as (Hres & WR & DJ & WA & WG).
  cps_destruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact Hres|]. split; [|split; [|split]].
    + intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto_fast.
    + intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
      apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto_fast.
    + intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. cps_destruct (WA a ar Ha) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
    + intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. cps_destruct (WG b gh Hb) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
  - unfold rmrep_ctx. rewrite rctx_head_cells_drop, ractives_drop, rctx_tail_cells_drop.
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). exact CX.
  - exact GL.
  - intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. cps_destruct (AR a ar Ha) as (A1 & A2 & A3).
    unfold rarea_rep. rewrite (rconc_drop a) by exact Pa. rewrite rpw_drop by exact Pn. split; [exact A1|]. split; [| exact A3].
    intros k Hk. rewrite rrec_drop, rmeta_cells_drop. apply A2. exact Hk.
  - intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. cps_destruct (GR b gh Hb) as (w8 & R & Hw). exists w8.
    rewrite (rconc_drop b) by exact Pb. rewrite rpw_drop by exact Pm. auto.
  - intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
    unfold rshadow_rep. rewrite rget_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End DROP.

Lemma rptrs_in_norid st2 LB c rid r m :
  KINV st2 LB c -> ZINV st2 [] -> rmrep st2 m ->
  (s_regions st2) !! rid = Some r -> r_kind r = RKGroup ->
  (forall b gh, (s_groups st2) !! b = Some gh -> fst b <> rid) ->
  ci_mptrs st2 ->
  ptrs_in (fun x => x <> rid) st2.
Proof.
  (intros K ZI MR Hr Kr NOG; cps_intros (M1 & M2 & M3 & M4 & M5)).
  pose proof MR as (WF & _). cps_pose WF as (Hres & WR & DJ & WA & WG).
  assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
  { (intros q; cps_intros (a & ar & k & Ha & Hk & ->); intros E). cbn in E. cps_destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. (cps_intros (r' & Hr' & NK); intros E). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
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
    intros E. cps_destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
  - intros g. split; [| split].
    + apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
    + apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
    + destruct (m_mem (get_meta_rec st2 g)) as [b|] eqn:MB; cbn; [| exact I].
      destruct (ZI g b MB) as [[ai Hb]|[]]. exact (NOG b _ Hb).
  - intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. cps_destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
  - intros b gh Hb. split; [exact (NOG b gh Hb)|].
    cps_destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
    assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
    exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.


End ACeilS1.
End RF_free_K.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_free_A OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_free_B OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_free_C OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_ntf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.RS0.RF_free.RF_free_K.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilLiaP.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
Local Ltac MA.F_malloc_free.mlia ::= RangeFast.rc_decide ltac:(MA.F_malloc_free.pow_lits; Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia ::= lia_acp.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rfree_end (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (LB' : list block) (m : mem) (errv : word) (s : PState)
    (st' : mstate) (s' : PState) : machine_state -> Prop :=
  fun ms' => s' = s /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st' m'
    /\ rpres_except (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st' a \/ 278844 <= a < 278848) m m'
    /\ (forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r')
    /\ (forall blk', In blk' LB' -> exists r', (s_regions st') !! (fst (blk_slot blk')) = Some r')
    /\ c_brk (ctx st') = c_brk (ctx st)
    /\ (forall brid boff, c_brk (ctx st) = BrkLive brid boff -> (s_regions st') !! brid = (s_regions st) !! brid).

Lemma rerrno_not_free_fp st m lo (sp : Z) a : rmrep st m -> alloc_ceiling <= lo -> 278844 <= a < 278848 -> ~ rfree_fp st lo sp a.
Proof.
  intros MR LO Ha. pose proof MR as (WF & _). cps_pose WF as (Hres & WR & DJ & WA & WG). bz_ceil.
  intros [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - cps_destruct A as (rid & r & Hr & _ & Hin). cps_destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). cps_pose (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (lr_lo_ge r). lia.
  - cps_destruct A as (b & gh & Hb & Hin). cps_destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
    cps_destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). cps_pose (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
  - cps_destruct A as (rid & r & v & Hr & _ & Hin & _). cps_destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). cps_pose (rreserved_disjoint _ _ RF) as (?&?&?&?). lia.
Qed.

(* [comment removed for export] *)
Lemma rmrep_after_munmap st2 rid r2 m4 m5 (slo shi : Z) :
  rmrep (drop_region rid st2) m4 -> rmrep st2 m4 ->
  (s_regions st2) !! rid = Some r2 -> r_kind r2 = RKGroup ->
  munch [(slo, shi); (278844, 278848); (r_base r2, r_base r2 + round_up_pg (r_len r2))]%Z m4 m5 ->
  alloc_ceiling <= slo ->
  rmrep (drop_region rid st2) m5.
Proof.
  intros MRd MR Hr Kr MU LO. pose proof MR as (WF & _). cps_pose WF as (Hres & WR & DJ & WA & WG). bz_ceil.
  cps_pose (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). cps_pose (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). bz_ceil.
  eapply rmrep_transport_agree'; [exact MRd|]. intros a Ha HF. apply MU. rewrite wa_unsigned by lia.
  assert (LOW : a < alloc_ceiling /\ ~ (278844 <= a < 278848) /\ ~ (r_base r2 <= a < r_base r2 + round_up_pg (r_len r2))).
  { destruct HF as [HF|HF].
    - split; [| split].
      + destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
        * unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold RMallocRep.RPAGE_SIZE in C; lia.
        * cps_destruct C as (ak & ar & Hak & Hin). cps_destruct (rarea_conc (drop_region rid st2) ak ar (proj1 MRd) Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & _ & _ & _ & RC). bz_ceil. lia.
        * cps_destruct C as (b & gh & Hb & Hin). cps_destruct (rgroup_conc (drop_region rid st2) b gh (proj1 MRd) Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). bz_ceil. lia.
        * cps_destruct C as (k & rk & v & Hk & _ & Hin & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [_ Hk].
          cps_destruct (WR _ _ Hk) as (_ & _ & _ & RC & _). bz_ceil. lia.
        * unfold RGOT_SSP in C; lia. * unfold RSSP_GUARD in C; lia.
      + intros Hea. exact (rerrno_avoids_repfoot _ _ a MRd Hea HF).
      + intros Hin. destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
        * unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold RMallocRep.RPAGE_SIZE in C; lia.
        * cps_destruct C as (ak & ar & Hak & Ha'). cbn [drop_region s_areas set_shadow set_regions] in Hak.
          cps_destruct (WA ak ar Hak) as (ra & Hra & Sa0 & Sa1 & _ & NK & ALR).
          assert (NE : fst ak <> rid) by (intros E; rewrite E, Hr in Hra; assert (ra = r2) by congruence; subst; exact (NK Kr)).
          rewrite (rconc_drop st2 rid ak NE) in Ha'. rewrite (conc_region' st2 ak ra Hra) in Ha'.
          pose proof (lr_lo_group r2 Kr). destruct (DJ _ _ _ _ Hra Hr NE); lia.
        * cps_destruct C as (b & gh & Hb & Ha'). cbn [drop_region s_groups set_shadow set_regions] in Hb.
          cps_destruct (WG b gh Hb) as (rb & Hrb & Krb & Sb0 & Sb1 & _).
          assert (NE : fst b <> rid).
          { intros E. cps_pose (proj1 MRd) as (_ & _ & _ & _ & WG'). cps_destruct (WG' b gh Hb) as (rb' & Hrb' & _).
            cbn [drop_region s_regions set_shadow set_regions] in Hrb'. rewrite E, lookup_delete_eq in Hrb'. discriminate. }
          rewrite (rconc_drop st2 rid b NE) in Ha'. rewrite (conc_region' st2 b rb Hrb) in Ha'.
          pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
        * cps_destruct C as (k & rk & v & Hk & Kk & Ha' & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
          pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia.
        * unfold RGOT_SSP in C. lia.
        * unfold RSSP_GUARD in C. lia.
    - cps_destruct HF as (k & rk & Hk & Kk & Ha'). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
      cps_destruct (WR _ _ Hk) as (_ & _ & _ & RC & RFk). cps_pose (rreserved_disjoint _ _ RFk) as (?&?&?&?). bz_ceil.
      split; [lia|]. split; [lia|].
      pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia. }
  cps_destruct LOW as (L1 & L2 & L3). cbn [outside]. split; [lia|]. split; [exact L2|]. split; [exact L3| exact I].
Qed.

(* [comment removed for export] *)
Lemma byte_zero_list (x : byte) : bv_unsigned x = 0 -> [x] = [b8 0].
Proof. intros Hx. f_equal. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 x). rewrite Hx. reflexivity. Qed.

Lemma bytes4_range (x0 x1 x2 x3 : byte) :
  0 <= bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3 < 2^32.
Proof.
  pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
  pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
  unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *. lia.
Qed.

Lemma le4_of_bytes (x0 x1 x2 x3 : byte) :
  le4 (wz (bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3)) = [x0; x1; x2; x3].
Proof.
  pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
  pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
  unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *.
  rewrite le4_bytes by lia. unfold b8.
  (* [comment removed for export] *)
  f_equal; [|f_equal; [|f_equal; [|f_equal]]];
    (apply bv_eq; rewrite Z_to_bv_unsigned;
     match goal with |- bv_wrap 8 ?a = _ => change (bv_wrap 8 a) with (a mod 256)%Z end;
     Z.div_mod_to_equations; lia).
Qed.

Lemma shiftr5_ge v : 0 <= v < 256 -> 5 <= Z.shiftr v 5 -> 160 <= v.
Proof. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
Lemma shiftr5_lt v : 0 <= v < 256 -> Z.shiftr v 5 < 5 -> v < 160.
Proof. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
Lemma shiftr5_range v : 0 <= v < 256 -> 0 <= Z.shiftr v 5 < 8.
Proof. intros Hv. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis TP : tp = Z_to_bv 64 RATP.

Theorem rlibc_free_implT : forall (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (s : PState)
    (st : mstate) (blk : block) (off : Z) (errv : word),
  CINV st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  rmrep st m -> mem_inv rsegs m ->
  stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 8192 ->
  rw_cells rsegs m (errno_addr tp) [C4 errv] ->
  a0 = Z_to_bv 64 (blk_addr blk) ->
  rimplT m (free st (Some (aadd (blk_slot blk) (UNIT * off)))) s
        (rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB blk) m errv s)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs)).
Proof using LO TP.
  intros until errv. intros C Hin Hoff HA MR MI ST SLO ERR A0.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (KINV_of_CINV _ _ C) as K0.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as ->.
  { rewrite HA in OA. unfold UNIT in OA. lia. }
  clear OA.
  set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *. set (LB' := lbrm LB blk) in *.
  pose proof (ci_gmetas _ _ C b g HB) as GO.
  cps_destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
  cps_pose MR as (WF & CX & GL & AR & GR & SH). cps_pose WF as (Hres & WR & DJ & WA & WG).
  cps_destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
  rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  cps_destruct (ki_slts _ _ _ K0 _ _ _ SL) as (GMg & Ec & _). fold c0 in Ec.
  cps_destruct HK as (v3 & lo8 & hi & C3 & V31 & C2 & C1 & OFF). fold c0 in C3, C2, C1, OFF.
  cbn [aadd fst snd] in C3, C2, C1, OFF.
  (* [comment removed for export] *)
  assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; exact FB).
  assert (Cp : conc st pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
  assert (Cc : conc st c0 = r_base r + snd c0) by (apply conc_region'; rewrite <- FB; exact Hr).
  assert (Sp : snd pf = snd c0 + 16 * off) by (unfold pf, UNIT; cbn; lia).
  assert (HAp : blk_addr blk = r_base r + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
  assert (Sc : snd c0 = snd b + 16 + get_stride (get_meta_rec st g) * i).
  { rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
  pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (ETP : bv_unsigned tp + -164 = 278844) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).
  pose proof LO as LOv. bz_ceil.
  (* [comment removed for export] *)
  assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
  { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
  assert (SI0 : 0 <= get_stride (get_meta_rec st g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : get_stride (get_meta_rec st g) * (i + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
  unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
  assert (P16m : snd pf mod 16 = 0).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 Hoff. Z.div_mod_to_equations. lia. }
  assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. set (stq := get_stride (get_meta_rec st g)) in *.
    unfold UNIT, IB in *.
    assert (16 * off + 16 <= stq) by (clear - OS SZ SM Hoff S16; Z.div_mod_to_equations; lia).
    rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
  assert (HAR : 0 <= r_base r + snd pf /\ r_base r + snd pf + 16 <= 2^64) by (bz_ceil; pose proof (round_up_pg_ge (r_len r)); lia).
  assert (DRr : r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x66000 <= r_base r) by (apply (rreserved_disjoint1 _ _ RF); lia).
  (* [comment removed for export] *)
  clear SIM SM B16 RBAL AL. change (frozen (snd pf mod 16 = 0)) in P16m.
  assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
  { unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
  destruct HB as [ai Hgh].
  (* [comment removed for export] *)
  assert (Cb : conc st b = r_base r + snd b) by (apply conc_region'; exact Hr).
  pose proof (shiftr5_range v3) as SR5.
  destruct (rmrep_shadow_read st m (fst c0) r (snd c0 + UNIT * off - 3) v3 MR ltac:(rewrite <- FB; exact Hr) Kr ltac:(unfold UNIT, IB in *; lia) C3) as [_ V3R].
  (* [comment removed for export] *)
  assert (RDB : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
            exists x : byte, bytes_at rsegs m (r_base r + snd q) [x] /\ rdv pans_mem m st q = bv_unsigned x).
  { intros q Fq Hq.
    assert (Hrq : s_regions st !! fst q = Some r) by (rewrite Fq; exact Hr).
    destruct (SH _ r Hr Kr) as [WRr _].
    assert (W1 : wr_at rsegs m (r_base r + snd q) 1).
    { cps_destruct WRr as (W0 & Wn & W). split; [lia|]. split; [pose proof (round_up_pg_ge (r_len r)); bz_ceil; lia|].
      intros j Hj. replace (r_base r + snd q + j) with (r_base r + (snd q + j)) by lia. apply W. lia. }
    cps_destruct (rwr_at_bytes_exist m _ 1 W1 ltac:(lia) ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as (bs & L & B).
    destruct bs as [|x [|]]; try discriminate. exists x. split; [exact B|].
    eapply (rrdv_cur m st m q r x MR Hrq Kr Hq); [intros; reflexivity| exact B]. }
  (* [comment removed for export] *)
  unfold free.
  eapply (rimplT_bind m (free_hdr st pf) _ s
           (fun r1 s' ms' => s' = s /\ r1 = Some (hdr_st st pf, g, i) /\
              rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')).
  { unfold free_hdr, get_meta. apply rimplT_guard. intros _.
    apply rimplT_rd16. apply rimplT_rd8. cbv zeta. apply rimplT_rd8.
    rewrite (rdv_known m st (aadd pf (-4)) 0) by (cbn [aadd fst snd]; replace (snd pf + -4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia); exact OK).
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    rewrite (rdv_known m st (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; replace (snd pf + -2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia); exact C2).
    rewrite (rdv_known m st (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; replace (snd pf + -2 + 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia); exact C1).
    cbn [Z.eqb negb]. rewrite EB. unfold get_group. rewrite Hgh. cbn [g_meta].
    apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
    destruct (s_areas st !! area_of g) as [ar|] eqn:AR1; [| apply rimplT_guard; intros; discriminate].
    apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
    unfold slot_start. rewrite (go_mem _ _ _ GO). cbv beta zeta.
    apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
    rewrite V31 in G12, G13, G14, G16.
    set (e := aadd (aadd b (UNIT + get_stride (get_meta_rec st g) * Z.land v3 31)) (get_stride (get_meta_rec st g) - IB)).
    assert (Fe : fst e = fst b) by reflexivity.
    assert (Se : snd e = snd b + 16 + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - 4).
    { unfold e. cbn [aadd snd]. rewrite V31. unfold UNIT, IB. lia. }
    (* [comment removed for export] *)
    pose proof (go_sc _ _ _ GO) as GSC.
    assert (WALK : forall r32 : Z,
      (160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32
          /\ bytes_at rsegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 4) (le4 (wz r32))
          /\ bytes_at rsegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 5) [b8 0]) ->
      (if 160 <=? v3 then r32 else Z.shiftr v3 5) <= conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf) ->
      bytes_at rsegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
      bytes_at rsegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB) [b8 0] ->
      evt rsegs (fun ms' => s = s /\ Some (hdr_st st pf, g, i) = Some (hdr_st st pf, g, i) /\
                 rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom rsegs))).
    { intros r32 BIG RSVLE RB0r RE0.
      eapply evt_mono.
      { eapply (rfree_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st pf r g (mkGhdr (Some g) ai) ar v3 lo8 hi r32);
          first [exact MR | exact MI | exact TK | exact ST | exact LO | exact Kr | idtac].
        all: rewrite ?EB, ?V31.
        - lia.
        - rewrite Fp. exact Hr.
        - rewrite A0, HAp. apply unsigned_lit. lia.
        - exact P16m.
        - rewrite Sp, Sc. lia.
        - unfold pf in OFF |- *. cbn [aadd snd] in OFF |- *. lia.
        - exact PHI.
        - replace (snd pf - 4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. exact OK.
        - replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
        - replace (snd pf - 2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C2.
        - replace (snd pf - 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C1.
        - exact Hgh.
        - reflexivity.
        - exact (go_slot _ _ _ GO).
        - cps_destruct (go_slot _ _ _ GO) as (a & ara & k & Ha & Hk & ->). cps_destruct (WA a ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. lia.
        - exact (go_mem _ _ _ GO).
        - exact AR1.
        - exact G15.
        - exact (go_avail _ _ _ GO).
        - exact (go_freed _ _ _ GO).
        - exact (proj2 (proj2 (proj2 (ki_cx _ _ _ K0)))).
        - lia.
        - rewrite (go_freeable _ _ _ GO). lia.
        - first [ solve [clear - GSC; lia] | lia ].
        - pose proof (go_maplen _ _ _ GO). lia.
        - exact G12.
        - exact G13.
        - exact G14.
        - intros Hsc. apply Z.ltb_lt in Hsc. rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b].
          apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. lia.
        - intros Hsc. destruct (Z.ltb_spec (m_sizeclass (get_meta_rec st g)) 48); [lia|]. apply Z.eqb_eq in G16. exact G16.
        - intros Hml. destruct (Z.eqb_spec (m_maplen (get_meta_rec st g)) 0); [(first [ solve [clear - OFF SZ AEND TOP HAp Hml; lia] | lia ])|]. cbn [negb] in G17. apply Z.leb_le in G17.
          unfold UNIT in G17.
          replace (m_maplen (get_meta_rec st g) * 4096) with (m_maplen (get_meta_rec st g) * 256 * 16) in G17 by lia.
          rewrite Z.div_mul in G17 by lia. lia.
        - lia.
        - exact S16.
        - rewrite Cb, Sp, Sc. unfold UNIT, IB in *. lia.
        - rewrite Cb. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia.
        - exact BIG.
        - exact RSVLE.
        - exact RB0r.
        - exact RE0.
        - intros b' gh' Hb' Fb'. specialize (HD b' gh' Hb' ltac:(rewrite Fb', Fp; exact FB)).
          rewrite (conc_region' st b' r) in HD by (rewrite Fb', Fp; exact Hr). unfold IB in HD.
          clear - HD HAp SZ. lia. (* [comment removed for export] *) }
      intros ms' FP. split; [reflexivity|]. split; [reflexivity|]. unfold hdr_st. rewrite <- V31. exact FP. }
    (* [comment removed for export] *)
    assert (EQE : forall k, r_base r + snd (aadd e (- k)) = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - k).
    { intros k. cbn [aadd snd]. rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (EQE0 : r_base r + snd e = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (ERNG : snd e + 1 <= round_up_pg (r_len r) /\ snd pf <= snd e /\ 16 <= snd e).
    { rewrite Se, Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia. }
    assert (DIFF : snd e - snd pf = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf)).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    
    unfold get_nominal_size. apply rimplT_rd8. cbv zeta.
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    apply rimplT_if; intros HR5.
    - (* [comment removed for export] *)
      apply Z.leb_le in HR5.
      apply rimplT_guard; intros G20. apply Z.eqb_eq in G20.
      apply rimplT_rd32. 
      cps_destruct (RDB (aadd e (-4)) Fe ltac:(cbn [aadd snd]; lia)) as (x0 & BX0 & RX0). rewrite RX0. 
      cps_destruct (RDB (aadd (aadd e (-4)) 1) Fe ltac:(cbn [aadd snd]; lia)) as (x1 & BX1 & RX1). rewrite RX1. 
      cps_destruct (RDB (aadd (aadd e (-4)) 2) Fe ltac:(cbn [aadd snd]; lia)) as (x2 & BX2 & RX2). rewrite RX2.
      cps_destruct (RDB (aadd (aadd e (-4)) 3) Fe ltac:(cbn [aadd snd]; lia)) as (x3 & BX3 & RX3). rewrite RX3.
      pose proof (bytes4_range x0 x1 x2 x3) as U32. pose proof (le4_of_bytes x0 x1 x2 x3) as LE4.
      set (r32 := bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3) in *.
      apply rimplT_guard; intros G21. apply Z.leb_le in G21.
      apply rimplT_rd8. cps_destruct (RDB (aadd e (-5)) Fe ltac:(cbn [aadd snd]; lia)) as (x5 & BX5 & RX5). rewrite RX5.
      apply rimplT_guard; intros G25. apply Z.eqb_eq in G25.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8. cps_destruct (RDB (aadd e (- r32)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8. cps_destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_ge v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = true) by (apply Z.leb_le; exact V160).
      
      apply (WALK r32).
      + intros _. split; [exact G20|]. split; [lia|]. split.
        * rewrite <- (EQE 4). rewrite LE4. change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))).
          apply bytes_at_app. split; [exact BX0|]. apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; cbn [aadd snd] in BX1 |- *; replace (r_base r + (snd e + -4) + 1) with (r_base r + (snd e + -4 + 1)) by lia; exact BX1|].
          apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; cbn [aadd snd] in BX2, BX3 |- *.
          -- replace (r_base r + (snd e + -4) + 1 + 1) with (r_base r + (snd e + -4 + 2)) by lia. exact BX2.
          -- replace (r_base r + (snd e + -4) + 1 + 1 + 1) with (r_base r + (snd e + -4 + 3)) by lia. exact BX3.
        * rewrite <- (EQE 5), <- (byte_zero_list x5 G25). exact BX5.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE r32), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe.
    - (* [comment removed for export] *)
      apply Z.leb_gt in HR5.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8. cps_destruct (RDB (aadd e (- Z.shiftr v3 5)) Fe ltac:(cbn [aadd snd]; (first [ solve [clear - SR5 V3R ERNG; lia] | lia ]))) as (xc & BXc & RXc). rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8. cps_destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_lt v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = false) by (apply Z.leb_gt; exact V160).
      
      apply (WALK 0).
      + intros H. exfalso. clear -H V160. lia.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE (Z.shiftr v3 5)), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe. }

  (intros r1 s' ms1; cps_intros (-> & -> & FH)). cbv beta iota.
  cps_destruct FH as (x1 & x5 & x6 & x7 & junk & m1 & -> & PE1 & WM1 & MI1 & ST1 & FR1 & MR1).
  set (st1 := hdr_st st pf) in *.
  assert (TK1 : ticks_ok st1) by (unfold st1; apply ticks_ok_hdr_st; exact TK).
  assert (MSL1 : meta_slot st1 g) by (exact (go_slot _ _ _ GO)).
  assert (HK123 : forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w).
  { intros k Hk. unfold pf; cbn [aadd fst snd].
    assert (CS : k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct CS as [-> |[-> | ->]];
      [exists hi; replace (snd c0 + UNIT * off - 1) with (snd c0 + UNIT * off - 1) by lia
      |exists lo8|exists v3];
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3]; f_equal; unfold UNIT; lia. }
  assert (FP1 : forall a, rfree_fp st1 lo (bv_unsigned sp - 48) a -> rfree_fp st lo (bv_unsigned sp) a).
  { intros a Ha. eapply (rfree_fp_hdr_st st pf lo (bv_unsigned sp) (bv_unsigned sp - 48) a TK HK123); [lia| exact Ha]. }
  assert (ERR1 : rw_cells rsegs m1 (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1 | exact ERR |]. cbn [cells_size csize Nat.add]. intros a Ha.
    rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
  assert (TF : Z.testbit (m_freed (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_freed (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; left; exact E| reflexivity]. }
  assert (TA : Z.testbit (m_avail (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_avail (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; right; exact E| reflexivity]. }
  (* [comment removed for export] *)
  assert (BLKR : forall stX blk', s_regions stX = s_regions st -> In blk' (lbrm LB blk) -> exists r', s_regions stX !! fst (blk_slot blk') = Some r').
  { intros stX blk' ERX Hb'. rewrite ERX. unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hb' _].
    destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hb') as [(r' & Hr' & _) _ _]. exists r'. exact Hr'. }
  unfold free_tail. cbv zeta. change (get_meta_rec st1 g) with (get_meta_rec st g).
  apply rimplT_guard. intros _.
  apply rimplT_if; intros HC.
  - (* [comment removed for export] *)
    apply negb_true_iff in HC. apply orb_false_iff in HC. destruct HC as [Hfz Hall]. apply Z.eqb_neq in Hfz. apply Z.eqb_neq in Hall.
    apply rimplT_ret.
    eapply evt_mono.
    { eapply (rfree_triv ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 junk lo st st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact Hfz | exact Hall | exact FR1 | exact ST1 | exact LO | reflexivity | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    intros ms' TPo. unfold rftriv_post in TPo.
    cps_destruct TPo as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & PE' & WM' & MI' & ST' & MR').
    split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE' | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
             rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
    split; [exact MR'|].
    split. { eapply rpres_except_mono; [eapply rpres_except_trans; [exact PE1| exact PE']|]. intros a Ha. left. exact Ha. }
    split; [intros rid r' H; exact H|].
    split; [intros blk' Hb'; apply (BLKR _ blk' eq_refl Hb')|].
    split; reflexivity.
  - (* [comment removed for export] *)
    
    assert (HNT : m_freed (get_meta_rec st g) = 0 \/ Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) + bit i = mask_upto (m_last_idx (get_meta_rec st g))).
    { apply negb_false_iff in HC. apply orb_true_iff in HC. destruct HC as [HC|HC]; apply Z.eqb_eq in HC; auto. }
    eapply rimplT_evt.
    { eapply (rfree_tocall ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact HNT | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    (intros ms2; cps_intros (y2 & y3 & y4 & y5 & y6 & y7 & ->)).
    assert (HLB : forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk).
    { intros b' Hb'. unfold LB', lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [H1 H2]. split; [exact H1|].
      intros E. rewrite E, aptr_eqb_refl in H2. exact H2. }
    assert (K1 : KINV st1 LB' 0).
    { unfold st1. eapply (KINV_hdr_st st LB LB' 0 pf blk r C Hin); [| exact HLB | rewrite Fp, FB; reflexivity | rewrite Fp; exact Hr | symmetry; exact HAp | exact P16m].
      unfold LB', lbrm. apply (KINV_filter_slot st LB 0 (fun s => negb (aptr_eqb s (blk_slot blk)))). exact K0. }
    assert (L1 : LPRE st1 LB' 0 g b i).
    { unfold LB', lbrm. apply (LPRE_intro st1 LB 0 g b i blk); [exact (ki_slts _ _ _ K0) | exists ai; exact Hgh | exact SL | exact NFR | exact NG | pose proof (go_sc _ _ _ GO); change (get_meta_rec st1 g) with (get_meta_rec st g); lia]. }
    assert (Z1 : ZINV st1 []) by (unfold st1; apply ZINV_hdr_st; apply (ZINV_of_CINV _ _ C)).
    assert (OOK1 : oracle_ok m m1 st1).
    { unfold st1. apply oracle_ok_hdr_st; [exact TK|]. eapply (roracle_ok_pres m m m1 st lo (bv_unsigned sp) m); [apply oracle_ok_refl | exact MR | exact LO | exact PE1]. }
    change (wz (conc st g)) with (Z_to_bv 64 (conc st1 g)). change (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc st1 g)).
    eapply (rntf_implT gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc m LB' lo LO);
      [exact K1 | exact L1 | exact Z1 | exact MR1 | exact MI1 | exact OOK1 | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; unfold FUEL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia |].
    (* [comment removed for export] *)
    
    intros st2 mi ms3 NQ. unfold rntf_q in NQ.
    cps_destruct NQ as (u0 & u1 & u2 & a0v & a1v & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m3 & -> & MI3 & ST3 & MR3 & PE3 & [c3 KI3] & ZI3 & FR3 & RES3 & OOK3).
    rewrite unsigned_lit in ST3, PE3 by lia.
    replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in PE3 by lia.
    replace (ret_pc (Z_to_bv 64 0x2967c)) with (Z_to_bv 64 0x2967c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (PE13 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
    { eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_mono; [exact PE3| exact FP1]. }
    assert (FR3' : rw_cells rsegs m3 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact FR1 |]. cbn [cells_size csize Nat.add length]. intros a Ha Hfp.
      pose proof (rfree_fp_lt st1 m1 lo (bv_unsigned sp - 48) a MR1 LO ltac:(lia) Hfp). lia. }
    assert (ERR3 : rw_cells rsegs m3 (errno_addr tp) [C4 errv]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
      rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR1 | exact LO | lia]. }
    pose proof (nf_regions _ _ FR3) as ER3. change (s_regions st1) with (s_regions st) in ER3.
    pose proof (nf_brk _ _ FR3) as EB3. change (ctx st1) with (ctx st) in EB3.
    destruct mi as [[bm len]|].
    + (* [comment removed for export] *)
      cbv beta iota.
      cps_destruct RES3 as (-> & -> & LEN & SND & (r2 & Hr2 & Kr2 & Lr2) & NOG).
      replace (negb (len =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
      pose proof Hr2 as Hr2'. rewrite ER3 in Hr2'.
      cps_destruct (WR _ _ Hr2') as (R2B0 & R2AL & R2L & R2C & R2F). bz_ceil.
      assert (R2D : r_base r2 + round_up_pg (r_len r2) <= 0x10000 \/ 0x66000 <= r_base r2) by (apply (rreserved_disjoint1 _ _ R2F); lia).
      assert (CB2 : conc st2 bm = r_base r2) by (rewrite (conc_region' st2 bm r2 Hr2); lia).
      pose proof (round_up_pg_ge (r_len r2)) as RU2.
      eapply rimplT_evt.
      { eapply (rfree_tomunmap sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra (wz (conc st2 bm)) _ _ F fc m3 junk lo len st2 errv);
          first [exact TP | exact MR3 | exact MI3 | exact LEN | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
      intros ms4 FM. unfold rfmun_post in FM.
      cps_destruct FM as (w0 & w1 & w2 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4 & ERR4 & MR4).
      eapply (rimplT_munmap m (conc st2 bm) len _ s).
      { eapply rmunmap_spec.
        - rewrite unsigned_lit by lia. exact ST4.
        - exact ERR4.
        - exact MI4.
        - unfold wz. reflexivity.
        - unfold wz. reflexivity.
        - lia.
        - rewrite Lr2, mmap_len_round. lia.
        - lia.
        - rewrite unsigned_lit by lia. lia.
        - rewrite ETP, unsigned_lit by lia. lia.
        - rewrite Lr2, mmap_len_round, unsigned_lit by lia. lia.
        - rewrite ETP, Lr2, mmap_len_round. lia.
        - rewrite TP; unfold RATP; rewrite unsigned_lit by lia. lia. }
      intros a ms5 MP. cbv beta. unfold rmunmap_post in MP.
      cps_destruct MP as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m5 & -> & MU5 & _ & MI5 & ST5 & ERR5 & ERNG).
      rewrite (munmap_ok_range_val a ERNG).
      apply rimplT_ret.
      replace (ret_pc (Z_to_bv 64 0x296ac)) with (Z_to_bv 64 0x296ac) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      rewrite unsigned_lit in MU5, ST5 by lia. rewrite Lr2, mmap_len_round, ETP in MU5.
      (* [comment removed for export] *)
      assert (AMC2 : amc (ctx st2) = amc (ctx st)) by (rewrite (nf_amc _ _ FR3); reflexivity).
      assert (MP2 : ci_mptrs st2) by (eapply (ci_mptrs_frame st st2 (ci_mp _ _ C) AMC2); [rewrite (nf_areas _ _ FR3); reflexivity| exact ER3]).
      assert (NOG' : forall b' gh, s_groups st2 !! b' = Some gh -> fst b' <> fst bm) by (intros b' gh Hb'; exact (NOG b' gh Hb')).
      pose proof (rptrs_in_norid st2 LB' c3 (fst bm) r2 m4 KI3 ZI3 MR4 Hr2 Kr2 NOG' MP2) as PTR.
      pose proof (rmrep_drop_region st2 (fst bm) PTR m4 MR4) as MRd4.
      assert (MRd5 : rmrep (drop_region (fst bm) st2) m5).
      { eapply (rmrep_after_munmap st2 (fst bm) r2 m4 m5); [exact MRd4 | exact MR4 | exact Hr2 | exact Kr2 | rewrite <- CB2; exact MU5 | lia]. }
      assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rrw_cells_agree'; [exact FR4|]. cbn [cells_size csize Nat.add length]. intros x Hx. apply MU5. rewrite wa_unsigned by lia.
        rewrite ?ETP. cbn [outside]. repeat split; lia. }
      eapply evt_mono.
      { eapply (rfree_fin1 sp gp tp z0 z1 z2 s0 s1 (munmap_ret a) z3 z4 z5 z6 z7 z8 z9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z10 z11 z12 z13 _ ra (sx32 errv) (wz (conc st2 bm)) (wz len) (rg_errno a errv) F fc m5 junk lo (drop_region (fst bm) st2) errv);
          first [exact TP | exact MRd5 | exact MI5 | exact FR5 | apply le4_sx32 | exact ERR5 | exact ST5 | exact LO | lia]. }
      intros ms' FIN. unfold rffin_post in FIN.
      cps_destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
      split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      { (* [comment removed for export] *)
        assert (DR : forall x, r_base r2 <= x < r_base r2 + round_up_pg (r_len r2) -> DROPPED st (drop_region (fst bm) st2) x).
        { intros x Hx. exists (fst bm), r2. split; [exact Hr2'|]. split; [| split; [exact Kr2| exact Hx]].
          cbn [drop_region s_regions set_shadow set_regions]. apply lookup_delete_eq. }
        eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m3 m4 MU4)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 278844 <= a < 278848)); [| exact NC].
          cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m4 m5 MU5)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 278844 <= a < 278848)); [| exact NC].
          cover_intervals ltac:(fun y Hy => first [left; apply rfree_fp_stack; lia | right; right; lia | right; left; apply DR; lia]). }
        eapply (rpres_except_of_munch_nw _ _ m5 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ 278844 <= a < 278848)); [| exact NC].
        cover_intervals ltac:(fun y Hy => first [left; apply rfree_fp_stack; lia | right; right; lia]). }
      split.
      { intros rid r' H. cbn [drop_region s_regions set_shadow set_regions] in H. apply lookup_delete_Some in H. destruct H as [_ H]. rewrite <- ER3. exact H. }
      split.
      { intros blk' Hb'. pose proof (proj1 (List.Forall_forall _ _) (ki_blks _ _ _ KI3) blk' Hb') as BK'.
        destruct BK' as [(g' & i' & bb & SL' & HB' & FB' & _) _ _].
        cps_destruct (go_region _ _ _ (ki_gmetas _ _ _ KI3 bb g' HB')) as (rr & Hrr & _).
        exists rr. cbn [drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne; [rewrite <- FB'; exact Hrr|].
        intros E. destruct HB' as [ai' Hbb]. apply (NOG bb _ Hbb). rewrite E. exact FB'. }
      split; [exact EB3|].
      intros brid boff HB0. cbn [drop_region s_regions set_shadow set_regions ctx s_ctx].
      rewrite <- EB3 in HB0. cps_destruct (ki_bk _ _ _ KI3 brid boff HB0) as (rb & Hrb & Krb).
      rewrite lookup_delete_ne; [rewrite ER3; reflexivity |].
      intros E. rewrite <- E, Hr2 in Hrb. assert (rb = r2) by congruence. subst rb. rewrite Kr2 in Krb. discriminate.
    + (* [comment removed for export] *)
      
      cbv beta iota. cbn in RES3. subst a1v.
      apply rimplT_ret.
      eapply evt_mono.
      { eapply (rfree_fin0 sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra a0v _ _ F fc m3 junk lo st2 errv);
          first [exact TP | exact MR3 | exact MI3 | exact FR3' | exact ERR3 | exact ST3 | exact LO | lia]. }
      intros ms' FIN. unfold rffin_post in FIN.
      cps_destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
      split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply (rpres_except_of_munch_nw _ _ m3 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st2 a \/ 278844 <= a < 278848)); [| exact NC].
        cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
      split; [intros rid r' H; rewrite <- ER3; exact H|].
      split; [intros blk' Hb'; apply (BLKR st2 blk' ER3 Hb')|].
      split; [exact EB3|].
      intros brid boff _. rewrite ER3. reflexivity.
Qed.
End FREE.

End ACeilS1.
