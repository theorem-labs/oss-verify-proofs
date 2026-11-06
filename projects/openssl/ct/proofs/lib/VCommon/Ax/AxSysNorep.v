(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxMem AxZZ AxState AxEntryRel AxSys AxOcc AxAcct AxMeasure AxSysMmap AxGrant AsanWAcc AsanWLazy AxSysNode.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxModelRel AxSysSound AxSysMmapS.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section Norep.
Variables addr len prot flags fd off : word.
Hypothesis Hoff : mmap_off_aligned_b off = true.
Hypothesis Hanon : mmap_anon_b flags = true.
Hypothesis Hlen : w_is0 len = false.
Hypothesis Hmod : mmap_modeled_b prot flags off = false.
Hypothesis Hnoacc : mmap_noaccess_b prot flags off = false.
Hypothesis Hfna : mmap_fixed_noaccess_b prot flags off = false.
Hypothesis Hfrw : mmap_fixed_rw_b prot flags off = false.

Local Notation nZ := (page_round_up_Z (bv_unsigned len)).
Local Notation n := (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))).

(* [comment removed for export] *)
Definition norep_gate (m : Model) : Prop :=
  bv_unsigned addr + nZ < two_pow_64 /\ bv_unsigned addr + nZ <= alloc_top (m_vmmaps m)
  /\ bv_unsigned addr mod page_size = 0 /\ 0 < bv_unsigned addr
  /\ region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) addr n = true.

Lemma norep_gate_null (m : Model) : norep_gate m -> null_ok m nZ addr.
Proof. intros (_ & H2 & H3 & H4 & H5). repeat split; assumption. Qed.

Local Ltac gate G :=
  destruct G as (G1 & G2 & G3 & G4 & G5);
  rewrite ?(proj2 (Z.leb_gt _ _) G1), ?(proj2 (Z.leb_le _ _) G2), ?(proj2 (Z.eqb_eq _ _) G3), ?(proj2 (Z.ltb_lt _ _) G4), ?G5 in *.

Lemma chk_norep_na (eff : SyscallEffect) (m m' : Model) (evs : list event) :
  mmap_noreplace_noaccess_b prot flags off = true -> norep_gate m ->
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  evs = [] /\ ((eff = mkEffect (errno_ret ENOMEM) [] [] /\ m' = m)
               \/ (eff = mkEffectU addr [] [] [(addr, n)] [] [] /\ m' = null_na_model flags addr n m)).
Proof.
  intros Hsh G H. unfold check_mmap in H. rewrite Hoff, Hanon, Hlen, Hmod, Hnoacc, Hfna, Hfrw, Hsh in H.
  cbn [negb] in H. cbv beta iota zeta in H. gate G. cbn [negb] in H.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate H]. destruct zs; [|discriminate H].
  destruct cs; [|discriminate H]. destruct ci; [|discriminate H].
  destruct (errno_ret_in mmap_errnos r) eqn:Ee.
  - destruct us; [|discriminate H]. injection H as <- <-. split; [reflexivity|]. left.
    rewrite (errno_in_enomem r Ee). split; reflexivity.
  - match type of H with (if ?c then _ else _) = _ => destruct c eqn:Ec; [|discriminate H] end.
    injection H as <- <-. split; [reflexivity|]. right.
    apply andb_prop in Ec as [E1 E2]. apply bv_eqb_eq in E1. apply listNN_eqb_eq in E2. subst r us. split; reflexivity.
Qed.

Lemma chk_norep_rw (eff : SyscallEffect) (m m' : Model) (evs : list event) :
  mmap_noreplace_noaccess_b prot flags off = false -> mmap_noreplace_rw_b prot flags off = true -> norep_gate m ->
  check_mmap addr len prot flags fd off eff m = CheckOk m' evs ->
  evs = [] /\ ((eff = mkEffect (errno_ret ENOMEM) [] [] /\ m' = m)
               \/ (eff = mkEffect addr [] [(addr, n)] /\ mmap_noreserve_backed_ok flags m nZ = true
                   /\ m' = null_rw_model flags addr n m)).
Proof.
  intros Hsh0 Hsh G H. unfold check_mmap in H. rewrite Hoff, Hanon, Hlen, Hmod, Hnoacc, Hfna, Hfrw, Hsh0, Hsh in H.
  cbn [negb] in H. cbv beta iota zeta in H. gate G. cbn [negb] in H.
  destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate H]. destruct us; [|discriminate H].
  destruct cs; [|discriminate H]. destruct ci; [|discriminate H].
  destruct (errno_ret_in mmap_errnos r) eqn:Ee.
  - destruct zs; [|discriminate H]. injection H as <- <-. split; [reflexivity|]. left.
    rewrite (errno_in_enomem r Ee). split; reflexivity.
  - match type of H with (if ?c then _ else _) = _ => destruct c eqn:Ec; [|discriminate H] end.
    injection H as <- <-. split; [reflexivity|]. right.
    apply andb_prop in Ec as [Ec E3]. apply andb_prop in Ec as [E1 E2].
    apply bv_eqb_eq in E1. apply listNN_eqb_eq in E2. subst r zs. split; [reflexivity | split; [exact E3 | reflexivity]].
Qed.

Lemma chk_norep_grant_na (m : Model) :
  mmap_noreplace_noaccess_b prot flags off = true -> 0 <= nZ -> norep_gate m ->
  check_mmap addr len prot flags fd off (mkEffectU addr [] [] [(addr, n)] [] []) m = CheckOk (null_na_model flags addr n m) [].
Proof.
  intros Hsh Hn G. pose proof (null_ok_not_errno len m addr Hn (norep_gate_null m G)) as Ee.
  unfold check_mmap. rewrite Hoff, Hanon, Hlen, Hmod, Hnoacc, Hfna, Hfrw, Hsh. cbn [negb]. cbv beta iota zeta.
  gate G. cbn [negb]. rewrite Ee, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Lemma chk_norep_grant_rw (m : Model) :
  mmap_noreplace_noaccess_b prot flags off = false -> mmap_noreplace_rw_b prot flags off = true -> 0 <= nZ -> norep_gate m ->
  mmap_noreserve_backed_ok flags m nZ = true ->
  check_mmap addr len prot flags fd off (mkEffect addr [] [(addr, n)]) m = CheckOk (null_rw_model flags addr n m) [].
Proof.
  intros Hsh0 Hsh Hn G Hb. pose proof (null_ok_not_errno len m addr Hn (norep_gate_null m G)) as Ee.
  unfold check_mmap. rewrite Hoff, Hanon, Hlen, Hmod, Hnoacc, Hfna, Hfrw, Hsh0, Hsh. cbn [negb]. cbv beta iota zeta.
  gate G. cbn [negb]. rewrite Ee, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl), Hb. reflexivity.
Qed.

Lemma chk_norep_modeled (eff : SyscallEffect) (m : Model) :
  mmap_noreplace_noaccess_b prot flags off = true \/ (mmap_noreplace_noaccess_b prot flags off = false /\ mmap_noreplace_rw_b prot flags off = true) ->
  norep_gate m -> check_mmap addr len prot flags fd off eff m <> CheckUnmodeled.
Proof.
  intros Hsh G. unfold check_mmap. rewrite Hoff, Hanon, Hlen, Hmod, Hnoacc, Hfna, Hfrw. cbn [negb]. cbv beta iota zeta.
  destruct Hsh as [Hsh|[Hsh0 Hsh]].
  - rewrite Hsh. gate G. cbn [negb]. destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct zs; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mmap_errnos r); [destruct us; discriminate|].
    match goal with |- (if ?c then _ else _) <> _ => destruct c; discriminate end.
  - rewrite Hsh0, Hsh. gate G. cbn [negb]. destruct eff as [r ws zs us cs ci]. destruct ws; [|discriminate]. destruct us; [|discriminate].
    destruct cs; [|discriminate]. destruct ci; [|discriminate].
    destruct (errno_ret_in mmap_errnos r); [destruct zs; discriminate|].
    match goal with |- (if ?c then _ else _) <> _ => destruct c; discriminate end.
Qed.

End Norep.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Comps.
Variable ρ : valuation.
Variable s : store.
Variables lo hi : Z.
Hypothesis Hsat : sat ρ s.
Hypothesis Hlo : 0 <= lo.
Hypothesis Hhi : hi <= 2 ^ 47.

(* [comment removed for export] *)
Lemma comp_sel_facts (R : region) : comp_sel s lo hi R = true ->
  is_entry R = false /\ is_shadow R = false /\ rbase ρ R mod 8 = 0 /\ to_Z (rg_n R) mod 8 = 0 /\ 0 < to_Z (rg_n R)
  /\ lo <= rbase ρ R /\ rbase ρ R + to_Z (rg_n R) <= hi
  /\ rbase ρ (comp_rg (rg_ts R) (rg_bo R) (to_Z (rg_n R))) = rbase ρ R / 8 + sh_off
  /\ to_Z (rg_n (comp_rg (rg_ts R) (rg_bo R) (to_Z (rg_n R)))) = to_Z (rg_n R) / 8
  /\ region_wf ρ (comp_rg (rg_ts R) (rg_bo R) (to_Z (rg_n R))).
Proof.
  unfold comp_sel. intros H. apply andb_prop in H as [H H7]. apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply negb_true_iff in H1. apply negb_true_iff in H2. apply Z.eqb_eq in H4. apply Z.eqb_eq in H5. apply Z.ltb_lt in H6.
  destruct (lrange s (wS (rg_bo R), rg_ts R)) as [[l h]|] eqn:El; [|discriminate H7].
  apply andb_prop in H7 as [L1 L2]. apply Z.leb_le in L1. apply Z.leb_le in L2.
  pose proof (lrange_sound ρ s _ Hsat _ El) as Hr. cbn [fst snd] in Hr.
  assert (E : leval ρ (wS (rg_bo R), rg_ts R) = wS (rg_bo R) + teval ρ (rg_ts R)) by reflexivity. rewrite E in Hr.
  assert (Hb : rbase ρ R = teval ρ (rg_ts R) + wS (rg_bo R)).
  { unfold rbase, smod. rewrite <- (wS_mod (rg_bo R)), Zplus_mod_idemp_r. rewrite Z.mod_small; [lia|]. unfold two64. lia. }
  destruct (comp_rg_wf ρ (rg_ts R) (rg_bo R) (to_Z (rg_n R)) (rbase ρ R) H3 H4 (eq_sym Hb) ltac:(lia) ltac:(lia) ltac:(lia)) as (C1 & C2 & C3).
  assert (A8 : rbase ρ R mod 8 = 0).
  { rewrite Hb, (teval_tdiv8 ρ _ H3). pose proof (Z.div_mod (wS (rg_bo R)) 8 ltac:(lia)) as D. rewrite H4 in D.
    replace (8 * teval ρ (tdiv8 (rg_ts R)) + wS (rg_bo R)) with ((teval ρ (tdiv8 (rg_ts R)) + wS (rg_bo R) / 8) * 8) by lia. apply Z_mod_mult. }
  split; [exact H1|]. split; [exact H2|]. split; [exact A8|]. split; [exact H5|]. split; [exact H6|]. split; [lia|]. split; [lia|].
  split; [exact C1|]. split; [exact C2 | exact C3].
Qed.

Lemma in_comps (A : list region) (C : region) : In C (norep_comps s lo hi A) ->
  exists R, In R A /\ comp_sel s lo hi R = true /\ C = comp_rg (rg_ts R) (rg_bo R) (to_Z (rg_n R)).
Proof.
  unfold norep_comps. intros H. apply in_flat_map in H as [R [HIn HC]]. exists R. split; [exact HIn|].
  destruct (comp_sel s lo hi R); [|destruct HC]. destruct HC as [<-|[]]. split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma comps_rdisj (R R' : region) : comp_sel s lo hi R = true -> comp_sel s lo hi R' = true -> rdisj ρ R R' ->
  rdisj ρ (comp_rg (rg_ts R) (rg_bo R) (to_Z (rg_n R))) (comp_rg (rg_ts R') (rg_bo R') (to_Z (rg_n R'))).
Proof.
  intros H1 H2 D. destruct (comp_sel_facts R H1) as (_ & _ & A8 & N8 & _ & _ & _ & Cb & Cn & _).
  destruct (comp_sel_facts R' H2) as (_ & _ & A8' & N8' & _ & _ & _ & Cb' & Cn' & _).
  unfold rdisj in *. rewrite Cb, Cn, Cb', Cn'.
  pose proof (Z.div_mod (rbase ρ R) 8 ltac:(lia)) as E1. pose proof (Z.div_mod (to_Z (rg_n R)) 8 ltac:(lia)) as E2.
  pose proof (Z.div_mod (rbase ρ R') 8 ltac:(lia)) as E3. pose proof (Z.div_mod (to_Z (rg_n R')) 8 ltac:(lia)) as E4.
  rewrite A8 in E1. rewrite N8 in E2. rewrite A8' in E3. rewrite N8' in E4. lia.
Qed.

Lemma comps_ok (A : list region) : regions_ok ρ A -> regions_ok ρ (norep_comps s lo hi A).
Proof.
  induction A as [|R A' IH]; [intros _; exact I|]. cbn [regions_ok]. intros (Hwf & Hd & Hok'). unfold norep_comps. cbn [flat_map].
  fold (norep_comps s lo hi A'). destruct (comp_sel s lo hi R) eqn:Es; [|exact (IH Hok')]. cbn [app regions_ok].
  destruct (comp_sel_facts R Es) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Cwf). split; [exact Cwf|]. split; [|exact (IH Hok')].
  apply Forall_forall. intros C' HC'. destruct (in_comps A' C' HC') as [R' [HIn' [Es' ->]]].
  apply (comps_rdisj R R' Es Es'). exact (proj1 (Forall_forall _ _) Hd R' HIn').
Qed.

End Comps.

Lemma regions_ok_app (ρ : valuation) (A1 A2 : list region) :
  regions_ok ρ A1 -> regions_ok ρ A2 -> (forall R1 R2, In R1 A1 -> In R2 A2 -> rdisj ρ R1 R2) -> regions_ok ρ (A1 ++ A2).
Proof.
  induction A1 as [|R A1' IH]; intros H1 H2 Hd; [exact H2|]. cbn [app regions_ok] in *. destruct H1 as (Hwf & HF & Hok').
  split; [exact Hwf|]. split.
  - apply Forall_app. split; [exact HF|]. apply Forall_forall. intros R2 HIn2. exact (Hd R R2 (or_introl eq_refl) HIn2).
  - apply IH; [exact Hok' | exact H2|]. intros R1 R2 HIn1 HIn2. exact (Hd R1 R2 (or_intror HIn1) HIn2).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Main.
Variable segs : list Segment.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Hypothesis Hlow : segs_low segs.

Notation MRm := (MR segs fs0).
Notation RR ρ := (R segs amodel (MRm ρ) LIM ρ).

Section PostRw.
Variable ρ : valuation.
Variable A : AST.
Variable ms : machine_state.
Variable model : Model.
Variable a : word.
Variable nZ : Z.
Variable flags : word.
Variables lo hi : Z.
Variable am' : amodel.
Hypothesis HR : RR ρ A (mkCfg ms model).
Hypothesis Hpc : pc_ok (npc A) = true.
Hypothesis Hn : 0 < nZ < 2 ^ 47.
Hypothesis Hal : nZ mod 4096 = 0.
Hypothesis Hok : null_ok model nZ a.
Hypothesis Hlz : mmap_noreserve_b flags = true.
Hypothesis Heb : eb_above (a_facts A) (am_atop (a_model A)) (a_mem A) = true.
Hypothesis Hpos : forall R, In R (a_mem A) -> 0 < to_Z (rg_n R).
Hypothesis Hlo : 0 <= lo.
Hypothesis Hhi : hi <= 2 ^ 47.

Local Notation n := (Z_to_bv 64 nZ).
Local Notation aZ := (bv_unsigned a).
Local Notation clo := (lo / 8 + sh_off).
Local Notation chi := (hi / 8 + sh_off).
Local Notation m' := (apply_zeros (ms_mem ms) [(a, n)]).
Local Notation model' := (null_rw_model flags a n model).
Local Notation comps := (norep_comps (a_facts A) lo hi (a_mem A)).

Hypothesis Hc_rng : aZ <= clo /\ chi <= aZ + nZ.
Hypothesis Hc_ss : (ls_beg <= clo /\ chi <= ls_end) \/ (hs_beg <= clo /\ chi <= hs_hi).
Hypothesis Hcov_ls : (aZ <= ls_beg /\ ls_end <= aZ + nZ) \/ (aZ + nZ <= ls_beg \/ ls_end <= aZ).
Hypothesis Hcov_hs : (aZ <= hs_beg /\ hs_hi <= aZ + nZ) \/ (aZ + nZ <= hs_beg \/ hs_hi <= aZ).
Hypothesis HM' : MRm ρ am' model'.

Let Hsat : sat ρ (a_facts A) := r_sat _ _ _ _ _ _ _ HR.

(* [comment removed for export] *)
Lemma comp_in (C : region) (z : Z) : In C comps -> in_rg ρ C z ->
  clo <= z < chi /\ exists R, In R (a_mem A) /\ is_entry R = false /\ forall q, preimage z q -> in_rg ρ R q.
Proof.
  intros HC Hz. destruct (in_comps (a_facts A) lo hi (a_mem A) C HC) as [R0 [HIn [Es ->]]].
  destruct (comp_sel_facts ρ (a_facts A) lo hi Hsat Hlo Hhi R0 Es) as (E1 & _ & A8 & N8 & Np & L1 & L2 & Cb & Cn & _).
  unfold in_rg in Hz. rewrite Cb, Cn in Hz.
  pose proof (Z.div_mod (rbase ρ R0) 8 ltac:(lia)) as D1. pose proof (Z.div_mod (to_Z (rg_n R0)) 8 ltac:(lia)) as D2. rewrite A8 in D1. rewrite N8 in D2.
  pose proof (Z.div_le_mono lo (rbase ρ R0) 8 ltac:(lia) L1) as M1.
  pose proof (Z.div_le_mono (rbase ρ R0 + to_Z (rg_n R0)) hi 8 ltac:(lia) L2) as M2.
  assert (E : (rbase ρ R0 + to_Z (rg_n R0)) / 8 = rbase ρ R0 / 8 + to_Z (rg_n R0) / 8).
  { rewrite D1 at 1. rewrite D2 at 1. replace (8 * (rbase ρ R0 / 8) + 0 + (8 * (to_Z (rg_n R0) / 8) + 0)) with ((rbase ρ R0 / 8 + to_Z (rg_n R0) / 8) * 8) by lia.
    apply Z.div_mul. lia. }
  split; [lia|]. exists R0. split; [exact HIn|]. split; [exact E1|]. intros q Hq. unfold preimage in Hq. unfold in_rg. lia.
Qed.

Theorem R_norep_rw (rvx : xv) : xv_val ρ rvx a ->
  RR ρ (with_model A (npc A) (aset (a_regs A) reg_a0 rvx) (comps ++ a_mem A) (a_facts A) am' (a_budget A))
     (mkCfg (setx ms (Z_to_bv 5 10) a (ms_pc_val ms + Z_to_bv 64 4)%bv (ms_resv ms) m') model').
Proof.
  intros Hrv.
  pose proof HR as [_ _ _ _ _ _ Hmem HM Hh [Hb Hl] _ Hhs Hcov Hcomp [N1 [N2 N3]]]. cbn [cfg_ms cfg_model] in *.
  destruct (P_bounds model a nZ Hn Hok) as (B1 & B2 & B3 & B4). destruct (rw_fields model a nZ flags) as (F1 & F2 & F3 & F4 & F5).
  destruct (P_ledger segs model a nZ Hn Hok _ F1 F2) as [Lnew Lold_w]. pose proof (in_ledger_of_w segs _ _ Lold_w) as Lold.
  pose proof (P_free segs LIM fs0 Hlow ρ A ms model a nZ HR Hn Hok) as Hfree.
  destruct (P_atop segs LIM fs0 ρ A ms model a nZ HR Hn Hok Heb) as [_ Hent].
  assert (Hm_in : forall z, aZ <= z < aZ + nZ -> m' (wz z) = Some (Z_to_bv 8 0)) by (intros z Hz; apply zeros_in; [rewrite B4; exact Hz | lia]).
  assert (Hm_out : forall x : word, ~ (aZ <= bv_unsigned x < aZ + nZ) -> m' x = ms_mem ms x) by (intros x Hx; apply zeros_out; rewrite B4; exact Hx).
  pose proof (region_fresh_all segs ρ (a_mem A) (ms_mem ms) model aZ nZ Hmem Hcov Hfree Hent) as Hfresh.
  assert (Hold : forall R0, In R0 (a_mem A) -> forall z, in_rg ρ R0 z -> m' (wz z) = ms_mem ms (wz z)).
  { intros R0 HIn z Hz. apply Hm_out. pose proof (regions_ok_in ρ _ R0 (proj1 Hmem) HIn) as (W1 & _).
    pose proof (smod_range ρ (rg_ts R0) (rg_bo R0)) as Hb0. fold (rbase ρ R0) in Hb0. unfold in_rg in Hz.
    rewrite u_wz by (unfold two64 in *; lia). exact (Hfresh R0 HIn z Hz). }
  apply (R_sys_post segs LIM fs0 ρ A _ ms model _ a rvx _ HR); try reflexivity; try assumption.
  - rewrite F4. exact Hh.
  - cbn [with_model a_budget]. pose proof (P_used_rw segs LIM fs0 ρ A ms model a nZ flags HR Hn Hal Hok) as X. rewrite Hlz in X. lia.
  - rewrite F5. exact Hl.
  - (* [comment removed for export] *) cbn [with_model a_mem]. destruct Hmem as [Hok' HF]. split.
    + apply regions_ok_app; [exact (comps_ok ρ (a_facts A) lo hi Hsat Hlo Hhi _ Hok') | exact Hok'|].
      intros C R0 HC HIn. destruct (in_comps (a_facts A) lo hi (a_mem A) C HC) as [R1 [HIn1 [Es Ec]]].
      destruct (comp_sel_facts ρ (a_facts A) lo hi Hsat Hlo Hhi R1 Es) as (_ & _ & _ & _ & Np & _ & _ & Cb & Cn & _). rewrite <- Ec in Cb, Cn.
      assert (Hcin : forall z, in_rg ρ C z -> aZ <= z < aZ + nZ) by (intros z Hz; destruct (comp_in C z HC Hz) as [X _]; lia).
      pose proof (Hpos R0 HIn) as Hp0. unfold rdisj.
      assert (Hc0 : in_rg ρ C (rbase ρ C)).
      { unfold in_rg. rewrite Cn. pose proof (Z.div_mod (to_Z (rg_n R1)) 8 ltac:(lia)) as D.
        destruct (comp_sel_facts ρ (a_facts A) lo hi Hsat Hlo Hhi R1 Es) as (_ & _ & _ & N8 & _). rewrite N8 in D. lia. }
      destruct (Z_lt_le_dec (rbase ρ R0) (rbase ρ C)) as [L|L].
      * right. destruct (Z_le_gt_dec (rbase ρ R0 + to_Z (rg_n R0)) (rbase ρ C)) as [L2|L2]; [exact L2|].
        exfalso. apply (Hfresh R0 HIn (rbase ρ C)); [unfold in_rg; lia | exact (Hcin _ Hc0)].
      * left. destruct (Z_le_gt_dec (rbase ρ C + to_Z (rg_n C)) (rbase ρ R0)) as [L2|L2]; [exact L2|].
        exfalso. apply (Hfresh R0 HIn (rbase ρ R0)); [unfold in_rg; lia | apply Hcin; unfold in_rg; lia].
    + apply Forall_app. split.
      * apply Forall_forall. intros C HC. destruct (in_comps (a_facts A) lo hi (a_mem A) C HC) as [R1 [HIn1 [Es Ec]]].
        rewrite RRegion_ne by (rewrite Ec; reflexivity). intros y Hy. pose proof (to_Z_bounded y) as Hyb.
        assert (Hin : in_rg ρ C (rbase ρ C + to_Z y)) by (unfold in_rg; lia).
        destruct (comp_in C _ HC Hin) as [Hr _].
        assert (E : m' (wz (rbase ρ C + to_Z y)) = Some (Z_to_bv 8 0)) by (apply Hm_in; lia). split.
        -- exists (Z_to_bv 8 0). split; [unfold rv; rewrite E; reflexivity|].
           rewrite (rbyte_zz segs C y); [reflexivity | right; rewrite Ec; reflexivity | rewrite Ec; reflexivity].
        -- intros _. unfold wview. rewrite E. discriminate.
      * rewrite Forall_forall in *. intros R0 HIn.
        exact (RRegion_mframe segs ρ (ms_mem ms) _ R0 (regions_ok_in ρ _ R0 Hok' HIn) (Hold R0 HIn) (HF R0 HIn)).
  - (* [comment removed for export] *) cbn [with_model a_mem]. destruct (hs_old_of_pos ρ _ _ Hpos Hhs) as (P1 & P2 & P3 & P4). right. split; [|split; [|split]].
    + intros R0 HIn Hs z Hz. apply in_app_or in HIn as [HC|HIn]; [|exact (P1 R0 HIn Hs z Hz)].
      destruct (in_comps (a_facts A) lo hi (a_mem A) R0 HC) as [R1 [_ [_ Ec]]]. rewrite Ec in Hs. discriminate Hs.
    + intros z Hz Hmiss. destruct (Z_lt_le_dec z aZ) as [L|L]; [|destruct (Z_lt_le_dec z (aZ + nZ)) as [L2|L2]].
      * rewrite Hm_out by (rewrite u_wz; [lia | unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, two64 in *; lia]).
        apply (P2 z Hz). intros R0 HIn Hs. exact (Hmiss R0 (in_or_app _ _ _ (or_intror HIn)) Hs).
      * right. apply Hm_in. lia.
      * rewrite Hm_out by (rewrite u_wz; [lia | unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, two64 in *; lia]).
        apply (P2 z Hz). intros R0 HIn Hs. exact (Hmiss R0 (in_or_app _ _ _ (or_intror HIn)) Hs).
    + destruct Hcov_ls as [[C1 C2]|Hm]; [left; intros z Hz; rewrite Hm_in by lia; discriminate|].
      assert (E : forall z, ls_beg <= z < ls_end -> m' (wz z) = ms_mem ms (wz z))
        by (intros z Hz; apply Hm_out; rewrite u_wz by (unfold ls_beg, ls_end, two64 in *; lia); lia).
      destruct P3 as [X|X]; [left | right]; intros z Hz; rewrite (E z Hz); exact (X z Hz).
    + destruct Hcov_hs as [[C1 C2]|Hm]; [left; intros z Hz; rewrite Hm_in by lia; discriminate|].
      assert (E : forall z, hs_beg <= z < hs_hi -> m' (wz z) = ms_mem ms (wz z))
        by (intros z Hz; apply Hm_out; rewrite u_wz by (unfold hs_beg, hs_hi, two64 in *; lia); lia).
      destruct P4 as [X|X]; [left | right]; intros z Hz; rewrite (E z Hz); exact (X z Hz).
  - (* [comment removed for export] *) intros x Hx. destruct (Z_lt_le_dec (bv_unsigned x) aZ) as [L|L]; [|destruct (Z_lt_le_dec (bv_unsigned x) (aZ + nZ)) as [L2|L2]].
    + rewrite Hm_out in Hx by lia. exact (Lold_w _ (Hcov x Hx)).
    + apply Lnew. lia.
    + rewrite Hm_out in Hx by lia. exact (Lold_w _ (Hcov x Hx)).
  - (* [comment removed for export] *) cbn [with_model a_mem]. intros R0 HIn Hs z Hz. apply in_app_or in HIn as [HC|HIn].
    + destruct (comp_in R0 z HC Hz) as [Hr [R1 [HIn1 [E1 Hpre]]]]. split.
      * unfold in_ss. destruct Hc_ss as [[X1 X2]|[X1 X2]]; [left | right]; lia.
      * intros q Hq. apply Lold. destruct Hmem as [Hok' HF].
        exact (region_cov segs ρ model (ms_mem ms) R1 q Hcov (regions_ok_in ρ _ R1 Hok' HIn1) (proj1 (Forall_forall _ _) HF R1 HIn1) E1 (Hpre q Hq)).
    + destruct (Hcomp R0 HIn Hs z Hz) as [C1 C2]. split; [exact C1|]. intros q Hq. exact (Lold _ (C2 q Hq)).
  - (* [comment removed for export] *) cbn [with_model a_mem]. unfold na_ok. rewrite F3. split; [|split].
    + intros x Hx Hq. destruct (Z_lt_le_dec (bv_unsigned x) aZ) as [L|L]; [|destruct (Z_lt_le_dec (bv_unsigned x) (aZ + nZ)) as [L2|L2]].
      * rewrite Hm_out in Hx by lia. exact (N1 x Hx Hq).
      * apply (Hfree (bv_unsigned x) ltac:(lia)). right. right. exact (mr_na_maps segs fs0 ρ _ _ HM _ Hq).
      * rewrite Hm_out in Hx by lia. exact (N1 x Hx Hq).
    + exact N2.
    + intros R0 HIn Hs z Hz q Hpre Hq. apply in_app_or in HIn as [HC|HIn]; [|exact (N3 R0 HIn Hs z Hz q Hpre Hq)].
      destruct (comp_in R0 z HC Hz) as [_ [R1 [HIn1 [E1 Hpre1]]]]. destruct Hmem as [Hok' HF].
      destruct (region_byte segs ρ (ms_mem ms) R1 q (regions_ok_in ρ _ R1 Hok' HIn1) (proj1 (Forall_forall _ _) HF R1 HIn1) E1 (Hpre1 q Hpre)) as [X|X].
      * assert (Hq0 : 0 <= q < two64).
        { pose proof (regions_ok_in ρ _ R1 Hok' HIn1) as (W1 & _). pose proof (smod_range ρ (rg_ts R1) (rg_bo R1)) as Hb0. fold (rbase ρ R1) in Hb0.
          pose proof (Hpre1 q Hpre) as Hi. unfold in_rg in Hi. lia. }
        apply (N1 (wz q) X). rewrite u_wz by (unfold two64 in *; lia). exact Hq.
      * exact (N2 q X Hq).
Qed.

End PostRw.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma norep_free (ρ : valuation) (am : amodel) (m : Model) (s : store) (addr len : Z) :
  MRm ρ am m -> sat ρ s -> 0 <= addr -> 0 < len -> addr + len < two64 ->
  lforall (ent_misses s addr (addr + len)) (am_maps am) = true -> res_misses segs addr (addr + len) = true ->
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) (Z_to_bv 64 addr) (Z_to_bv 64 len) = true.
Proof.
  intros HM Hs Ha Hl Hw He Hr. apply region_free_disj. rewrite !u_Z_to_bv by lia. intros q Hq. apply in_app_or in Hq as [Hq|Hq].
  - rewrite (mr_res segs fs0 ρ _ _ HM) in Hq. pose proof (lforall_forall _ _ Hr q Hq) as X. cbv beta in X.
    unfold iv_disj. apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
  - destruct (MR_maps_ent segs fs0 ρ am m q HM Hq) as [e [HIn [-> Hok]]]. pose proof (lforall_forall _ _ He e HIn) as X. cbv beta in X.
    unfold ent_misses in X. destruct (lrange s (ae_base e)) as [[l h]|] eqn:El; [|discriminate X].
    pose proof (lrange_sound ρ s _ Hs _ El) as Hrg. cbn [fst snd] in Hrg.
    unfold iv_disj. rewrite (ent_val_bas ρ e Hok), (ent_val_bsz ρ e Hok). apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable cfg : SpuriousCfg.
Hypothesis Hcfg2 : sc_alloc cfg = false.
Variable KT : valuation -> list byte -> TSet.

Notation Snd B := (forall ρ c, RR ρ B c -> forall o, out_val ρ B o -> realizes_cfg segs cfg c (KT ρ o)).

(* [comment removed for export] *)
Lemma norep_core (A B : AST) (ρ : valuation) (ms : machine_state) (model : Model) (w : bv 32) (o : list byte) (na : bool) :
  let a := rg ms (Z_to_bv 5 10) in
  let L := rg ms (Z_to_bv 5 11) in
  let P := rg ms (Z_to_bv 5 12) in
  let F := rg ms (Z_to_bv 5 13) in
  let O := rg ms (Z_to_bv 5 15) in
  let n := Z_to_bv 64 (page_round_up_Z (bv_unsigned L)) in
  RR ρ A (mkCfg ms model) -> fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true -> out_val ρ A o -> out_val ρ B o ->
  bv_unsigned (rg ms (Z_to_bv 5 17)) = 222 ->
  mmap_off_aligned_b O = true -> mmap_anon_b F = true -> w_is0 L = false ->
  mmap_modeled_b P F O = false -> mmap_noaccess_b P F O = false -> mmap_fixed_noaccess_b P F O = false -> mmap_fixed_rw_b P F O = false ->
  (if na then mmap_noreplace_noaccess_b P F O = true else mmap_noreplace_noaccess_b P F O = false /\ mmap_noreplace_rw_b P F O = true) ->
  mmap_noreserve_b F = true -> 0 <= page_round_up_Z (bv_unsigned L) ->
  norep_gate a L model ->
  RR ρ B (mkCfg (setx ms (Z_to_bv 5 10) a (ms_pc_val ms + Z_to_bv 64 4)%bv (ms_resv ms)
                   (if na then apply_unmaps (ms_mem ms) [(a, n)] else apply_zeros (ms_mem ms) [(a, n)]))
                (if na then null_na_model F a n model else null_rw_model F a n model)) ->
  Snd B -> realizes_cfg segs cfg (mkCfg ms model) (KT ρ o).
Proof.
  intros a L P F O n HR Hf He Ho HoB H17 Hoff Hanon Hl0 Hmod Hnoacc Hfna Hfrw Hshape Hlz Hn0 Hgate Hpost HS.
  pose proof HR as [Hpc0 Hal Hsvc Hregs Hres Hrom Hmem HM Hh [Hb Hl] Hsat Hhs Hcov Hcomp Hna]. cbn [cfg_ms cfg_model] in *.
  set (x8 := rg ms (Z_to_bv 5 17)) in *.
  assert (Hchk : forall eff m0, check_syscall (sys_input segs (latch ms) x8) eff m0 = check_mmap a L P F (rg ms (Z_to_bv 5 14)) O eff m0)
    by (intros eff m0; exact (check_syscall_222 segs (latch ms) x8 eff m0 H17)).
  assert (Hoffm : injected_family_off cfg (sys_input segs (latch ms) x8) = true).
  { apply family_off_alloc; [exact Hcfg2 | rewrite H17; cbn; tauto | rewrite H17; lia]. }
  pose proof (norep_gate_null a L model Hgate) as Hnull.
  assert (Hnr : refusal_b (sys_input segs (latch ms) x8) model a = false).
  { rewrite (refusal_b_222 segs (latch ms) x8 model a H17). apply refusal_below. destruct Hgate as (_ & G2 & _).
    pose proof (alloc_top_room (m_vmmaps model)) as Rm. unfold stack_max_size in Rm. lia. }
  apply (rzc_latch segs cfg ms model w _ Hh Hsvc Hf He).
  apply (rzc_sys_silent segs cfg (latch ms) model x8 (KT ρ o) Hh eq_refl).
  - rewrite Hchk. apply chk_norep_modeled; try assumption. destruct na; [left; exact Hshape | right; exact Hshape].
  - intros eff m' evs Hc. rewrite Hchk in Hc. destruct na.
    + destruct (chk_norep_na a L P F _ O Hoff Hanon Hl0 Hmod Hnoacc Hfna Hfrw eff model m' evs Hshape Hgate Hc) as [-> [[_ ->]|[_ ->]]];
        (split; [reflexivity|]); [exact Hh|]. destruct (na_fields model a (page_round_up_Z (bv_unsigned L)) F) as (_ & _ & _ & F4 & _). rewrite F4. exact Hh.
    + destruct Hshape as [S0 S1].
      destruct (chk_norep_rw a L P F _ O Hoff Hanon Hl0 Hmod Hnoacc Hfna Hfrw eff model m' evs S0 S1 Hgate Hc) as [-> [[_ ->]|[_ [_ ->]]]];
        (split; [reflexivity|]); [exact Hh|]. destruct (rw_fields model a (page_round_up_Z (bv_unsigned L)) F) as (_ & _ & _ & F4 & _). rewrite F4. exact Hh.
  - destruct na.
    + exists (mkEffectU a [] [] [(a, n)] [] []), (null_na_model F a n model). split; [|exact Hnr].
      rewrite Hchk. apply chk_norep_grant_na; assumption.
    + destruct Hshape as [S0 S1]. exists (mkEffect a [] [(a, n)]), (null_rw_model F a n model). split; [|exact Hnr].
      rewrite Hchk. apply chk_norep_grant_rw; try assumption. unfold mmap_noreserve_backed_ok. rewrite Hlz. reflexivity.
  - intros eff m' Hc Hnr'. specialize (Hnr' Hoffm). rewrite Hchk in Hc. rewrite (refusal_b_222 segs (latch ms) x8 model _ H17) in Hnr'.
    destruct na.
    + destruct (chk_norep_na a L P F _ O Hoff Hanon Hl0 Hmod Hnoacc Hfna Hfrw eff model m' [] Hshape Hgate Hc) as [_ [[-> _]|[-> ->]]].
      * cbn [eff_ret] in Hnr'. rewrite refusal_enomem in Hnr'. discriminate Hnr'.
      * exists (null_na_model F a n model). split; [apply materialize_nil|]. rewrite adv_effect, eff_mem_unmaps. cbn [eff_ret].
        exact (HS ρ _ Hpost o HoB).
    + destruct Hshape as [S0 S1].
      destruct (chk_norep_rw a L P F _ O Hoff Hanon Hl0 Hmod Hnoacc Hfna Hfrw eff model m' [] S0 S1 Hgate Hc) as [_ [[-> _]|[-> [_ ->]]]].
      * cbn [eff_ret] in Hnr'. rewrite refusal_enomem in Hnr'. discriminate Hnr'.
      * exists (null_rw_model F a n model). split; [apply materialize_nil|]. rewrite adv_effect, eff_mem_zeros. cbn [eff_ret].
        exact (HS ρ _ Hpost o HoB).
Qed.

Lemma has_ent_in (e : aent) (l : list aent) : has_ent e l = true -> In e l.
Proof. unfold has_ent. intros H. apply lexists_exists in H as [x [HIn E]]. apply aent_eqb_eq in E. subst x. exact HIn. Qed.

Theorem sys_mmap_noreplace_sound (A : AST) (l : list AST) :
  pc_ok (npc A) = true -> xlit (aget (a_regs A) 17%uint63) = Some 222 ->
  sys_mmap_noreplace segs A = Some l -> (forall B, In B l -> Snd B) ->
  forall ρ c, RR ρ A c -> (exists w, fetch_word segs (ms_pc_val (cfg_ms c)) = Some w /\ is_ecall w = true) ->
  forall o, out_val ρ A o -> realizes_cfg segs cfg c (KT ρ o).
Proof.
  intros Hpc H17x Hs HS ρ [ms model] HR [w [Hf He]] o Ho. cbn [cfg_ms] in Hf.
  unfold sys_mmap_noreplace in Hs. cbv zeta in Hs.
  destruct (xlit (aget (a_regs A) 10%uint63)) as [addr|] eqn:E10; [|discriminate Hs].
  destruct (xlit (aget (a_regs A) 11%uint63)) as [len|] eqn:E11; [|discriminate Hs].
  destruct (xlit (aget (a_regs A) 12%uint63)) as [prot|] eqn:E12; [|discriminate Hs].
  destruct (xlit (aget (a_regs A) 13%uint63)) as [flags|] eqn:E13; [|discriminate Hs].
  destruct (xlit (aget (a_regs A) 15%uint63)) as [off|] eqn:E15; [|discriminate Hs].
  destruct (lrange (a_facts A) (am_atop (a_model A))) as [[tlo thi]|] eqn:Et; [|discriminate Hs].
  match type of Hs with (if ?c then _ else _) = _ => destruct c eqn:Eck; [|discriminate Hs] end. injection Hs as <-.
  apply andb_prop in Eck as [Eck Chs]. apply andb_prop in Eck as [Eck Cpos]. apply andb_prop in Eck as [Eck Cres].
  apply andb_prop in Eck as [Eck Cents]. apply andb_prop in Eck as [Eck Heb]. apply andb_prop in Eck as [Eck Ctlo].
  apply andb_prop in Eck as [Eck Csh]. apply andb_prop in Eck as [Eck Cent]. apply andb_prop in Eck as [Eck Cprot].
  apply andb_prop in Eck as [Coff Cflags]. apply Z.eqb_eq in Coff. apply Z.eqb_eq in Cflags. apply Z.leb_le in Ctlo. apply negb_true_iff in Csh.
  subst off flags.
  pose proof (lforall_forall _ _ Cpos) as Hpos'. cbv beta in Hpos'.
  assert (Hpos : forall R, In R (a_mem A) -> 0 < to_Z (rg_n R)) by (intros R0 HIn; apply Z.ltb_lt; exact (Hpos' R0 HIn)).
  pose proof HR as [_ _ _ Hregs _ _ _ HM _ _ Hsat _ _ _ _]. cbn [cfg_ms cfg_model] in Hregs, HM.
  assert (H17 : bv_unsigned (rg ms (Z_to_bv 5 17)) = 222) by exact (reg_lit ρ _ ms (Z_to_bv 5 17) 17%uint63 222 Hregs eq_refl H17x).
  assert (W10 : rg ms (Z_to_bv 5 10) = Z_to_bv 64 addr) by exact (rg_of_lit _ _ (reg_lit ρ _ ms (Z_to_bv 5 10) 10%uint63 addr Hregs eq_refl E10)).
  assert (W11 : rg ms (Z_to_bv 5 11) = Z_to_bv 64 len) by exact (rg_of_lit _ _ (reg_lit ρ _ ms (Z_to_bv 5 11) 11%uint63 len Hregs eq_refl E11)).
  assert (W12 : rg ms (Z_to_bv 5 12) = Z_to_bv 64 prot) by exact (rg_of_lit _ _ (reg_lit ρ _ ms (Z_to_bv 5 12) 12%uint63 prot Hregs eq_refl E12)).
  assert (W13 : rg ms (Z_to_bv 5 13) = Z_to_bv 64 norep_flags) by exact (rg_of_lit _ _ (reg_lit ρ _ ms (Z_to_bv 5 13) 13%uint63 _ Hregs eq_refl E13)).
  assert (W15 : rg ms (Z_to_bv 5 15) = Z_to_bv 64 0) by exact (rg_of_lit _ _ (reg_lit ρ _ ms (Z_to_bv 5 15) 15%uint63 0 Hregs eq_refl E15)).
  pose proof (lrange_sound ρ _ _ Hsat _ Et) as Hat. cbn [fst snd] in Hat. rewrite <- (mr_atop segs fs0 ρ _ _ HM) in Hat.
  assert (Hprot : prot = 3 \/ prot = 0) by (apply orb_prop in Cprot as [X|X]; apply Z.eqb_eq in X; auto).
  (* [comment removed for export] *)
  assert (Hgate : forall a0 l0, addr = a0 -> len = l0 -> 0 < a0 -> 0 < l0 -> a0 + l0 <= sh_hi -> a0 mod 4096 = 0 ->
            page_round_up_Z l0 = l0 ->
            norep_gate (Z_to_bv 64 a0) (Z_to_bv 64 l0) model).
  { intros a0 l0 -> -> Ha0 Hl0 Hsum Hal0 Hpr. unfold sh_hi in Hsum.
    assert (U1 : bv_unsigned (Z_to_bv 64 a0) = a0) by (apply u_Z_to_bv; unfold two64; lia).
    assert (U2 : bv_unsigned (Z_to_bv 64 l0) = l0) by (apply u_Z_to_bv; unfold two64; lia).
    unfold norep_gate. rewrite U1, U2, Hpr. unfold sh_hi in Ctlo. repeat split; try (unfold two_pow_64; lia); try exact Hal0.
    exact (norep_free ρ _ model _ a0 l0 HM Hsat ltac:(lia) Hl0 ltac:(unfold two64; lia) Cents Cres). }
  apply orb_prop in Cent as [Cent|Cent]; [apply orb_prop in Cent as [Cent|Cent]|]; apply aent_eqb_eq in Cent;
    injection Cent as -> -> Ena.
  - (* [comment removed for export] *)
    assert (prot = 3) by (destruct Hprot as [->| ->]; [reflexivity | discriminate Ena]). subst prot.
    change (aent_eqb (AE (2147446784, []) 268435456 (3 =? 0)) ls_ent) with true in *. cbv iota in *.
    set (B := with_model A _ _ _ _ _ _) in *.
    pose proof (Hgate 2147446784 268435456 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(unfold sh_hi; lia) eq_refl eq_refl) as G. rewrite <- W10, <- W11 in G.
    assert (Hnull : null_ok model 268435456 (rg ms (Z_to_bv 5 10))).
    { pose proof (norep_gate_null _ _ model G) as X. rewrite W11 in X. exact X. }
    refine (norep_core A B ρ ms model w o false HR Hf He Ho Ho H17 _ _ _ _ _ _ _ _ _ _ G _ (HS B (or_introl eq_refl)));
      rewrite ?W11, ?W12, ?W13, ?W15; try reflexivity; [split; reflexivity | discriminate|].
    change (page_round_up_Z (bv_unsigned (Z_to_bv 64 268435456))) with 268435456.
    assert (Ua : bv_unsigned (rg ms (Z_to_bv 5 10)) = 2147446784) by (rewrite W10; reflexivity).
    apply (R_norep_rw ρ A ms model (rg ms (Z_to_bv 5 10)) 268435456 (Z_to_bv 64 norep_flags) 0 sh_lo _ HR Hpc ltac:(lia) eq_refl Hnull eq_refl Heb Hpos
             ltac:(lia) ltac:(unfold sh_lo; lia)).
    + rewrite Ua. unfold sh_lo, sh_off. lia.
    + left. unfold sh_lo, sh_off, ls_beg, ls_end. lia.
    + left. rewrite Ua. unfold ls_beg, ls_end. lia.
    + right. left. rewrite Ua. unfold hs_beg. lia.
    + apply (MR_grant_rw segs fs0 ρ _ model HM ls_ent _ 268435456 (Z_to_bv 64 norep_flags));
        [rewrite Ua; reflexivity | reflexivity | lia | exact Hnull | | intros _; unfold AxLz.BIGMIN; lia | | reflexivity].
      * intros X. rewrite Csh in X. discriminate X.
      * intros _. rewrite Ua. split; [vm_compute; reflexivity | split; reflexivity].
    + cbn [xv_val]. rewrite Ua. reflexivity.
  - (* [comment removed for export] *)
    assert (prot = 0) by (destruct Hprot as [->| ->]; [discriminate Ena | reflexivity]). subst prot.
    change (aent_eqb (AE (2415882240, []) 2199023255552 (0 =? 0)) ls_ent) with false in *.
    change (aent_eqb (AE (2415882240, []) 2199023255552 (0 =? 0)) hs_ent) with false in *. cbv iota in *. cbn [app] in *.
    set (B := with_model A _ _ _ _ _ _) in *.
    pose proof (Hgate 2415882240 2199023255552 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(unfold sh_hi; lia) eq_refl eq_refl) as G. rewrite <- W10, <- W11 in G.
    assert (Hnull : null_ok model 2199023255552 (rg ms (Z_to_bv 5 10))).
    { pose proof (norep_gate_null _ _ model G) as X. rewrite W11 in X. exact X. }
    refine (norep_core A B ρ ms model w o true HR Hf He Ho Ho H17 _ _ _ _ _ _ _ _ _ _ G _ (HS B (or_introl eq_refl)));
      rewrite ?W11, ?W12, ?W13, ?W15; try reflexivity; [discriminate|].
    change (page_round_up_Z (bv_unsigned (Z_to_bv 64 2199023255552))) with 2199023255552.
    assert (Ua : bv_unsigned (rg ms (Z_to_bv 5 10)) = 2415882240) by (rewrite W10; reflexivity).
    apply (R_grant_na_gen segs LIM fs0 Hlow ρ A ms model (rg ms (Z_to_bv 5 10)) 2199023255552 (Z_to_bv 64 norep_flags) HR Hpc ltac:(lia) eq_refl Hnull
             ltac:(intros _; unfold AxLz.BIGMIN; lia)
             gap_ent (XL (wofZ 2415882240)) (a_facts A) (am_next (a_model A))); [rewrite Ua; reflexivity | reflexivity | | exact Hsat | intros _ X; discriminate X | reflexivity].
    cbn [xv_val]. rewrite Ua. reflexivity.
  - (* [comment removed for export] *)
    assert (prot = 3) by (destruct Hprot as [->| ->]; [reflexivity | discriminate Ena]). subst prot.
    change (aent_eqb (AE (2201439137792, []) 15392894357504 (3 =? 0)) ls_ent) with false in *.
    change (aent_eqb (AE (2201439137792, []) 15392894357504 (3 =? 0)) hs_ent) with true in *. cbv iota in *.
    cbn [negb] in Chs. apply andb_prop in Chs as [Chs Clit]. apply andb_prop in Chs as [Cls Cgap].
    set (B := with_model A _ _ _ _ _ _) in *.
    pose proof (Hgate 2201439137792 15392894357504 eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(unfold sh_hi; lia) eq_refl eq_refl) as G. rewrite <- W10, <- W11 in G.
    assert (Hnull : null_ok model 15392894357504 (rg ms (Z_to_bv 5 10))).
    { pose proof (norep_gate_null _ _ model G) as X. rewrite W11 in X. exact X. }
    refine (norep_core A B ρ ms model w o false HR Hf He Ho Ho H17 _ _ _ _ _ _ _ _ _ _ G _ (HS B (or_introl eq_refl)));
      rewrite ?W11, ?W12, ?W13, ?W15; try reflexivity; [split; reflexivity | discriminate|].
    change (page_round_up_Z (bv_unsigned (Z_to_bv 64 15392894357504))) with 15392894357504.
    assert (Ua : bv_unsigned (rg ms (Z_to_bv 5 10)) = 2201439137792) by (rewrite W10; reflexivity).
    apply (R_norep_rw ρ A ms model (rg ms (Z_to_bv 5 10)) 15392894357504 (Z_to_bv 64 norep_flags) sh_hi 140737488355328 _ HR Hpc ltac:(lia) eq_refl Hnull eq_refl Heb Hpos
             ltac:(unfold sh_hi; lia) ltac:(lia)).
    + rewrite Ua. unfold sh_hi, sh_off. lia.
    + right. unfold sh_hi, sh_off, hs_beg, hs_hi. lia.
    + right. right. rewrite Ua. unfold ls_end. lia.
    + left. rewrite Ua. unfold hs_beg, hs_hi. lia.
    + apply MR_shadow_on.
      * apply (MR_grant_rw segs fs0 ρ _ model HM hs_ent _ 15392894357504 (Z_to_bv 64 norep_flags));
          [rewrite Ua; reflexivity | reflexivity | lia | exact Hnull | | intros _; unfold AxLz.BIGMIN; lia | | reflexivity].
        -- intros X. rewrite Csh in X. discriminate X.
        -- intros _. rewrite Ua. split; [vm_compute; reflexivity | split; reflexivity].
      * right. exact (has_ent_in _ _ Cls).
      * right. exact (has_ent_in _ _ Cgap).
      * left. reflexivity.
      * intros e0 [<-|HIn]; [reflexivity|]. pose proof (lforall_forall _ _ Clit e0 HIn) as X. cbv beta in X. apply negb_true_iff in X. exact X.
    + cbn [xv_val]. rewrite Ua. reflexivity.
Qed.

End Sound.

End Main.
