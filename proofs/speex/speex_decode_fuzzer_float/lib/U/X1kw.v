(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj X1bs X1c2 X1bn.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0px X0q2 X0qh X0qk X0qj X0q4.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Export X0p3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1lz X1m1.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Lemma rfree_fp_hdr_st st pf lo (sp sp' : Z) a : ticks_ok st ->
(forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
sp' <= sp -> rfree_fp (hdr_st st pf) lo sp' a -> rfree_fp st lo sp a.
Proof.
intros TK HK HS H. destruct H as [H|[H|H]].
- left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
- right; left. exact H.
- right; right. first [ sf_destruct 7%nat H as rid r v H1 H2 H3 H4 | sf_fb; destruct H as (rid & r & v & H1 & H2 & H3 & H4) ]. destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
first [ unshelve sf_eexists 3%nat; [ exact (rid) | exact (r) | exact (w) | ] | sf_fb; exists rid, r, w ]. auto.
Qed.

Section DROP.
Context {RCEIL : RunCeiling}.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

#[using="Type"] Lemma rdrop_regions : s_regions st' = delete rid (s_regions st). Proof. reflexivity. Qed.
#[using="Type"] Lemma rdrop_shadow : s_shadow st' = delete rid (s_shadow st). Proof. reflexivity. Qed.
#[using="Type"] Lemma rconc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rpw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rconc_drop by exact H. reflexivity. Qed.
#[using="Type"] Lemma rget_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma rrec_drop q : get_meta_rec st' q = get_meta_rec st q. Proof. reflexivity. Qed.

#[using="PTR"] Lemma rmeta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof.
first [ sf_destruct 9%nat PTR as _ _ _ _ _ _ _ PM _ | sf_fb; destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _) ]. destruct (PM q) as (P1 & P2 & P3).
unfold meta_cells. rewrite !rpw_drop by assumption. reflexivity.
Qed.

#[using="PTR"] Lemma rctx_head_cells_drop : ctx_head_cells st' = ctx_head_cells st.
Proof.
first [ sf_destruct 6%nat PTR as P1 P2 P3 P4 P5 _ | sf_fb; destruct PTR as (P1 & P2 & P3 & P4 & P5 & _) ]. unfold ctx_head_cells. change (ctx st') with (ctx st).
rewrite !rpw_drop by assumption. reflexivity.
Qed.
#[using="PTR"] Lemma ractives_drop : actives st' = actives st.
Proof.
first [ sf_destruct 7%nat PTR as _ _ _ _ _ PA _ | sf_fb; destruct PTR as (_ & _ & _ & _ & _ & PA & _) ]. unfold actives. apply map_ext. intros i.
change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply rpw_drop. apply PA.
Qed.
#[using="PTR"] Lemma rctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof.
first [ sf_destruct 8%nat PTR as _ _ _ _ _ _ PB _ | sf_fb; destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _) ]. unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (rconc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

#[using="PTR"] Lemma rmrep_drop_region m : rmrep st m -> rmrep st' m.
Proof.
intros MR. pose proof MR as sfP_; first [ sf_destruct 6%nat sfP_ as WF CX GL AR GR SH | sf_fb; destruct sfP_ as (WF & CX & GL & AR & GR & SH) ]. pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WG | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WG) ].
first [ sf_destruct 10%nat PTR as P1 P2 P3 P4 P5 PA PB PM PAR PG | sf_fb; destruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG) ].
split; [|split; [|split; [|split; [|split]]]].
- split; [exact Hres|]. split; [|split; [|split]].
+ intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto.
+ intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto.
+ intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. destruct (WA a ar Ha) as (r & Hr & REST). exists r.
cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
+ intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. destruct (WG b gh Hb) as (r & Hr & REST). exists r.
cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
- unfold rmrep_ctx. rewrite rctx_head_cells_drop, ractives_drop, rctx_tail_cells_drop.
change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). exact CX.
- exact GL.
- intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. destruct (AR a ar Ha) as (A1 & A2 & A3).
unfold rarea_rep. rewrite (rconc_drop a) by exact Pa. rewrite rpw_drop by exact Pn. split; [exact A1|]. split; [| exact A3].
intros k Hk. rewrite rrec_drop, rmeta_cells_drop. apply A2. exact Hk.
- intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. destruct (GR b gh Hb) as (w8 & R & Hw). exists w8.
rewrite (rconc_drop b) by exact Pb. rewrite rpw_drop by exact Pm. auto.
- intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
unfold rshadow_rep. rewrite rget_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End DROP.

Lemma rptrs_in_norid {RCEIL : RunCeiling} st2 LB c rid r m :
KINV st2 LB c -> ZINV st2 [] -> rmrep st2 m ->
(s_regions st2) !! rid = Some r -> r_kind r = RKGroup ->
(forall b gh, (s_groups st2) !! b = Some gh -> fst b <> rid) ->
ci_mptrs st2 ->
ptrs_in (fun x => x <> rid) st2.
Proof.
intros K ZI MR Hr Kr NOG sfH_; first [ sf_destruct 5%nat sfH_ as M1 M2 M3 M4 M5 | sf_fb; destruct sfH_ as (M1 & M2 & M3 & M4 & M5) ].
pose proof MR as (WF & _). pose proof WF as sfP_; first [ sf_destruct 5%nat sfP_ as Hres WR DJ WA WG | sf_fb; destruct sfP_ as (Hres & WR & DJ & WA & WG) ].
assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
{ intros q sfH_; first [ sf_destruct 6%nat sfH_ as a ar k Ha Hk -> | sf_fb; destruct sfH_ as (a & ar & k & Ha & Hk & ->) ]; intros E. cbn in E. first [ pose proof (WA a ar Ha) as sfP_; sf_destruct 7%nat sfP_ as ra Hra _ _ _ NK _ | sf_fb; destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _) ].
rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
{ intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
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
intros E. first [ pose proof (WA a ar Ha) as sfP_; sf_destruct 7%nat sfP_ as ra Hra _ _ _ NK _ | sf_fb; destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _) ]. rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
- intros b gh Hb. split; [exact (NOG b gh Hb)|].
destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.

