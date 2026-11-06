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
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg AllocSim.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxBytes AxMem AxZZ AxState AxEntryRel AxSys AxOcc AxAcct AxFresh AxMeasure AxSysMmap AxHole AxGrant AxPostFix AsanWAcc AsanWLazy AxSysNode.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxModelRel AxSysSound.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Lemma page_round_up_facts (len : Z) : 0 < len -> 0 < page_round_up_Z len /\ page_round_up_Z len mod 4096 = 0 /\ page_round_up_Z len < len + 4096.
Proof.
  intros H. pose proof (page_round_up_Z_bounds len ltac:(lia)) as B. unfold page_size in B.
  split; [lia|]. split; [unfold page_round_up_Z, page_size; apply Z_mod_mult | lia].
Qed.

Section Main.
Variable segs : list Segment.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Hypothesis Hlow : segs_low segs.

Notation MRm := (MR segs fs0).
Notation RR ρ := (R segs amodel (MRm ρ) LIM ρ).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Post.
Variable ρ : valuation.
Variable A : AST.
Variable ms : machine_state.
Variable model : Model.
Variable g : int.
Variable a : word.
Variable nZ : Z.
Variable flags : word.
Variable ghi : Z.
Hypothesis HR : RR ρ A (mkCfg ms model).
Hypothesis Hpc : pc_ok (npc A) = true.
Hypothesis Hn : 0 < nZ < 2 ^ 47.
Hypothesis Hal : nZ mod 4096 = 0.
Hypothesis Hok : null_ok model nZ a.
Hypothesis Hsh : am_shadow (a_model A) = true.
Hypothesis Heb : eb_above (a_facts A) (am_atop (a_model A)) (a_mem A) = true.

Local Notation n := (Z_to_bv 64 nZ).
Local Notation aZ := (bv_unsigned a).
Local Notation am := (a_model A).
Local Notation ts := [(g, 4096)].

Let HM : MRm ρ am model := r_model _ _ _ _ _ _ _ HR.
Let Hsat : sat ρ (a_facts A) := r_sat _ _ _ _ _ _ _ HR.

Lemma P_bounds : 0 < aZ /\ aZ + nZ <= alloc_top (m_vmmaps model) /\ aZ + nZ < two64 /\ bv_unsigned n = nZ.
Proof. exact (grant_bounds model a nZ (proj1 Hn) Hok). Qed.

Lemma P_atop : 0 <= leval ρ (am_atop am) <= 2 ^ 47 /\ forall R, In R (a_mem A) -> is_entry R = true -> aZ + nZ <= rbase ρ R.
Proof.
  destruct (eb_above_sound ρ _ _ _ Hsat Heb) as [H1 H2]. destruct P_bounds as (_ & B2 & _).
  rewrite (mr_atop segs fs0 ρ _ _ HM) in B2. split; [exact H1|]. intros R0 HIn He. specialize (H2 R0 HIn He). lia.
Qed.

Lemma P_top47 : aZ + nZ <= 2 ^ 47.
Proof. destruct P_atop as [[_ H] _]. destruct P_bounds as (_ & B2 & _). rewrite (mr_atop segs fs0 ρ _ _ HM) in B2. lia. Qed.

Lemma P_al8 : aZ mod 8 = 0 /\ nZ mod 8 = 0.
Proof.
  destruct Hok as (H1 & _). unfold page_size in H1.
  pose proof (Z.div_mod aZ 4096 ltac:(lia)) as D1. pose proof (Z.div_mod nZ 4096 ltac:(lia)) as D2. rewrite H1 in D1. rewrite Hal in D2.
  split.
  - assert (E : aZ = aZ / 4096 * 512 * 8) by lia. rewrite E. apply Z_mod_mult.
  - assert (E : nZ = nZ / 4096 * 512 * 8) by lia. rewrite E. apply Z_mod_mult.
Qed.

Lemma P_free : forall q, aZ <= q < aZ + nZ -> ~ in_ledger segs (m_vmmaps model) q.
Proof.
  destruct Hok as (_ & _ & H3 & H4). exact (ledger_free segs Hlow (m_vmmaps model) a nZ (mr_res segs fs0 ρ _ _ HM) ltac:(lia) H3 H4).
Qed.

Lemma P_side : aZ + nZ <= sh_lo \/ sh_hi <= aZ.
Proof.
  destruct Hok as (_ & _ & _ & H4). destruct P_bounds as (_ & _ & B3 & _). rewrite region_free_app in H4. apply andb_prop in H4 as [_ H4].
  exact (MR_free_span segs fs0 ρ am model a nZ HM (proj1 Hn) B3 H4 Hsh).
Qed.

(* [comment removed for export] *)
Lemma P_ledger (m' : Model) : vm_maps (m_vmmaps m') = (a, n) :: vm_maps (m_vmmaps model) -> alloc_top (m_vmmaps m') = alloc_top (m_vmmaps model) ->
  (forall q, aZ <= q < aZ + nZ -> in_ledger_w segs (m_vmmaps m') q) /\ (forall q, in_ledger_w segs (m_vmmaps model) q -> in_ledger_w segs (m_vmmaps m') q).
Proof.
  intros Em Et. destruct P_bounds as (_ & _ & _ & B4). split.
  - intros q Hq. right. right. rewrite Em. apply inl_cons. left. unfold bas, bsz. cbn [fst snd]. rewrite B4. exact Hq.
  - intros q [Hq|[Hq|Hq]]; [left; exact Hq | right; left; rewrite Et; exact Hq | right; right; rewrite Em; apply inl_cons; right; exact Hq].
Qed.

Lemma rw_fields : vm_maps (m_vmmaps (null_rw_model flags a n model)) = (a, n) :: vm_maps (m_vmmaps model)
  /\ alloc_top (m_vmmaps (null_rw_model flags a n model)) = alloc_top (m_vmmaps model)
  /\ vm_noaccess (m_vmmaps (null_rw_model flags a n model)) = vm_noaccess (m_vmmaps model)
  /\ m_halted (null_rw_model flags a n model) = m_halted model
  /\ vm_limit (m_vmmaps (null_rw_model flags a n model)) = vm_limit (m_vmmaps model).
Proof. unfold null_rw_model. destruct (with_mmap_backing_fields flags a n (with_vmmaps (grant_maps model a n (vm_noaccess (m_vmmaps model))) model)) as (Ev & Eh & _). rewrite Ev, Eh. repeat split; reflexivity. Qed.

Lemma na_fields : vm_maps (m_vmmaps (null_na_model flags a n model)) = (a, n) :: vm_maps (m_vmmaps model)
  /\ alloc_top (m_vmmaps (null_na_model flags a n model)) = alloc_top (m_vmmaps model)
  /\ vm_noaccess (m_vmmaps (null_na_model flags a n model)) = (a, n) :: vm_noaccess (m_vmmaps model)
  /\ m_halted (null_na_model flags a n model) = m_halted model
  /\ vm_limit (m_vmmaps (null_na_model flags a n model)) = vm_limit (m_vmmaps model).
Proof. unfold null_na_model. destruct (with_mmap_backing_fields flags a n (with_vmmaps (grant_maps model a n ((a, n) :: vm_noaccess (m_vmmaps model))) model)) as (Ev & Eh & _). rewrite Ev, Eh. repeat split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma P_used_rw : vm_backing_used (null_rw_model flags a n model) <= vm_backing_used model + (if mmap_noreserve_b flags then 0 else nZ).
Proof.
  destruct P_bounds as (B1 & B2 & B3 & B4). destruct Hok as (A1 & _ & _ & A4). rewrite region_free_app in A4. apply andb_prop in A4 as [_ A4].
  unfold null_rw_model, with_mmap_backing. destruct (mmap_noreserve_b flags).
  - rewrite (used_grant_lazy model a n); [lia | rewrite B4; unfold two64 in *; lia | rewrite B4; lia | exact A4
      | exact (MR_maps_nowrap segs fs0 ρ am model HM) | exact (MR_maps_pos segs fs0 ρ am model HM) | exact A1 | rewrite B4; exact Hal].
  - pose proof (used_grant_eager model a n) as X. rewrite B4 in X. exact X.
Qed.

Lemma P_used_na : vm_backing_used (null_na_model flags a n model) = vm_backing_used model.
Proof.
  destruct P_bounds as (B1 & B2 & B3 & B4). destruct Hok as (A1 & _ & _ & A4). rewrite region_free_app in A4. apply andb_prop in A4 as [_ A4].
  unfold null_na_model, with_mmap_backing. destruct (mmap_noreserve_b flags).
  - apply (used_grant_noaccess_lazy model a n); [rewrite B4; lia | exact A4
      | exact (MR_maps_nowrap segs fs0 ρ am model HM) | exact (MR_maps_pos segs fs0 ρ am model HM) | exact A1 | rewrite B4; exact Hal].
  - apply (used_grant_noaccess model a n); [rewrite B4; lia | exact A4 | exact (MR_maps_pos segs fs0 ρ am model HM)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation s' := (grant_facts g nZ (am_atop am) ghi true (am_maps am) (res_lits (segments_reserved segs)) (a_facts A)).
Local Notation pc' := (ms_pc_val ms + Z_to_bv 64 4)%bv.

Hypothesis Hbigf : mmap_noreserve_b flags = true -> AxLz.BIGMIN <= nZ.     (* [comment removed for export] *)

(* [comment removed for export] *)
Theorem R_grant_na_gen (e : aent) (rv : xv) (s1 : store) (nx : int) :
  leval ρ (ae_base e) = aZ -> ae_size e = nZ -> xv_val ρ rv a -> sat ρ s1 ->
  (am_shadow am = true -> var_ent e = true -> aZ + nZ <= sh_lo \/ sh_hi <= aZ) ->
  AxLz.lzfull e = false ->
  RR ρ (with_model A (npc A) (aset (a_regs A) reg_a0 rv) (a_mem A) s1 (am_grant am e nx) (a_budget A))
     (mkCfg (setx ms (Z_to_bv 5 10) a pc' (ms_resv ms) (apply_unmaps (ms_mem ms) [(a, n)])) (null_na_model flags a n model)).
Proof.
  clear Hsh Heb. intros Ebase Esize Hrv Hs1 Hspan Hnfull.
  pose proof HR as [_ _ _ _ _ _ Hmem _ Hh [Hb Hl] _ Hhs Hcov Hcomp [N1 [N2 N3]]]. cbn [cfg_ms cfg_model] in *.
  destruct P_bounds as (B1 & B2 & B3 & B4). destruct na_fields as (F1 & F2 & F3 & F4 & F5).
  destruct (P_ledger _ F1 F2) as [Lnew_w Lold_w]. pose proof (in_ledger_of_w segs _ _ Lold_w) as Lold.
  assert (Hext : forall x, apply_unmaps (ms_mem ms) [(a, n)] x = ms_mem ms x).
  { intros x. destruct (Z_lt_le_dec (bv_unsigned x) aZ) as [L|L]; [apply unmaps_out; rewrite B4; lia|].
    destruct (Z_lt_le_dec (bv_unsigned x) (aZ + nZ)) as [L2|L2]; [|apply unmaps_out; rewrite B4; lia].
    rewrite unmaps_in by (rewrite B4; lia). destruct (ms_mem ms x) as [b|] eqn:E; [|reflexivity].
    exfalso. apply (P_free (bv_unsigned x) ltac:(lia)). apply (mem_cov_in segs model _ Hcov). rewrite E. discriminate. }
  assert (Hna_new : forall q, inl (vm_noaccess (m_vmmaps (null_na_model flags a n model))) q ->
            inl (vm_noaccess (m_vmmaps model)) q \/ aZ <= q < aZ + nZ).
  { intros q Hq. rewrite F3 in Hq. apply inl_cons in Hq as [Hq|Hq]; [right | left; exact Hq]. unfold bas, bsz in Hq. cbn [fst snd] in Hq. lia. }
  apply (R_sys_post segs LIM fs0 ρ A _ ms model _ a rv _ HR); try reflexivity; try assumption.
  - cbn [with_model a_model]. refine (MR_grant_na segs fs0 ρ am model HM e a nZ flags nx Ebase Esize (proj1 Hn) Hok Hspan Hbigf _ Hnfull Hal).
    intros Hf. rewrite Hf in Hnfull. discriminate Hnfull.
  - rewrite F4. exact Hh.
  - cbn [with_model a_budget]. rewrite P_used_na. exact Hb.
  - rewrite F5. exact Hl.
  - cbn [with_model a_mem]. destruct Hmem as [Hok' HF]. split; [exact Hok'|]. rewrite Forall_forall in *. intros R0 HIn.
    apply (RRegion_mframe segs ρ (ms_mem ms)); [exact (regions_ok_in ρ _ R0 Hok' HIn) | intros z _; apply Hext | exact (HF R0 HIn)].
  - cbn [with_model a_mem]. destruct Hhs as [Hpl|(P1 & P2 & P3 & P4)]; [left; exact Hpl | right]. split; [exact P1|]. split; [|split].
    + intros z Hz Hr. rewrite Hext. exact (P2 z Hz Hr).
    + destruct P3 as [X|X]; [left | right]; intros z Hz; rewrite Hext; exact (X z Hz).
    + destruct P4 as [X|X]; [left | right]; intros z Hz; rewrite Hext; exact (X z Hz).
  - intros x Hx. rewrite Hext in Hx. exact (Lold_w _ (Hcov x Hx)).
  - cbn [with_model a_mem]. intros R0 HIn Hs z Hz. destruct (Hcomp R0 HIn Hs z Hz) as [C1 C2]. split; [exact C1|]. intros q Hq. exact (Lold _ (C2 q Hq)).
  - cbn [with_model a_mem]. split; [|split].
    + intros x Hx Hq. rewrite Hext in Hx. destruct (Hna_new _ Hq) as [Hq'|Hq']; [exact (N1 x Hx Hq') | exact (P_free _ Hq' (mem_cov_in segs model _ Hcov x Hx))].
    + intros z Hz Hq. destruct (Hna_new _ Hq) as [Hq'|Hq']; [exact (N2 z Hz Hq') | exact (P_free _ Hq' (or_introl Hz))].
    + intros R0 HIn Hs z Hz q Hpre Hq. destruct (Hna_new _ Hq) as [Hq'|Hq']; [exact (N3 R0 HIn Hs z Hz q Hpre Hq')|].
      exact (P_free _ Hq' (proj2 (Hcomp R0 HIn Hs z Hz) q Hpre)).
Qed.

Hypothesis Hpos : forall R, In R (a_mem A) -> 0 < to_Z (rg_n R).

(* [comment removed for export] *)
Theorem R_grant_rw_gen (tsb : terms) (ob : w64) (rvx : xv) (ret : word) (s1 : store) (am' : amodel) (model' : Model) (b' : Z) :
  smod ρ tsb ob = aZ -> teval ρ tsb + wS ob = aZ -> tdiv8_ok tsb = true -> wS ob mod 8 = 0 ->
  xv_val ρ rvx ret -> sat ρ s1 -> MRm ρ am' model' ->
  vm_maps (m_vmmaps model') = (a, n) :: vm_maps (m_vmmaps model) -> alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model) ->
  vm_noaccess (m_vmmaps model') = vm_noaccess (m_vmmaps model) -> m_halted model' = m_halted model ->
  vm_limit (m_vmmaps model') = vm_limit (m_vmmaps model) -> vm_backing_used model' <= b' ->
  has_wit (a_facts A) ls_beg ls_end (a_mem A) = true -> has_wit (a_facts A) hs_beg hs_hi (a_mem A) = true ->
  RR ρ (with_model A (npc A) (aset (a_regs A) reg_a0 rvx) (zero_rg tsb ob nZ :: comp_rg tsb ob nZ :: a_mem A) s1 am' b')
     (mkCfg (setx ms (Z_to_bv 5 10) ret pc' (ms_resv ms) (apply_zeros (ms_mem ms) [(a, n)])) model').
Proof.
  intros Esm Ete Ht8 Ho8 Hrv Hs1 HM' F1 F2 F3 F4 F5 Hbud HwL HwH.
  pose proof HR as [_ _ _ _ _ _ Hmem _ Hh [Hb Hl] _ Hhs Hcov Hcomp Hna]. cbn [cfg_ms cfg_model] in *.
  destruct P_bounds as (B1 & B2 & B3 & B4).
  destruct (P_ledger _ F1 F2) as [Lnew_w Lold_w].
  destruct P_al8 as [Ha8 Hn8]. destruct P_atop as [_ Hent].
  pose proof P_top47 as H47. pose proof P_side as Hside. pose proof P_free as Hfree.
  set (R0 := zero_rg tsb ob nZ). set (C0 := comp_rg tsb ob nZ).
  destruct (zero_rg_wf ρ tsb ob nZ aZ Esm ltac:(lia) ltac:(lia)) as (R0b & R0n & R0wf). fold R0 in R0b, R0n, R0wf.
  destruct (comp_rg_wf ρ tsb ob nZ aZ Ht8 Ho8 Ete ltac:(lia) H47 ltac:(lia)) as (C0b & C0n & C0wf). fold C0 in C0b, C0n, C0wf.
  assert (R0k : rg_kind R0 = KZero) by reflexivity. assert (R0c : rg_cells R0 = IEmpty) by reflexivity.
  assert (C0k : rg_kind C0 = KShadow) by reflexivity. assert (C0c : rg_cells C0 = IEmpty) by reflexivity.
  assert (Ha0 : 0 <= aZ) by lia. assert (Hn0 : 0 < nZ) by lia.
  assert (Hm_in : forall z, aZ <= z < aZ + nZ -> apply_zeros (ms_mem ms) [(a, n)] (wz z) = Some (Z_to_bv 8 0))
    by (intros z Hz; apply zeros_in; [rewrite B4; exact Hz | lia]).
  assert (Hm_out : forall x : word, ~ (aZ <= bv_unsigned x < aZ + nZ) -> apply_zeros (ms_mem ms) [(a, n)] x = ms_mem ms x)
    by (intros x Hx; apply zeros_out; rewrite B4; exact Hx).
  pose proof (region_fresh segs ρ (a_mem A) (ms_mem ms) model aZ nZ Hmem Hcov Hfree Hent) as HA_fresh.
  pose proof (comp_fresh segs ρ (a_mem A) model aZ nZ Hcomp Hfree C0 Ha8 Hn8 C0b C0n) as HA_C.
  assert (HC_mapped : forall z, in_rg ρ C0 z -> ms_mem ms (wz z) <> None).
  { intros z Hz. unfold in_rg in Hz. rewrite C0b, C0n in Hz.
    exact (comp_mapped segs Hlow ρ (a_facts A) (a_mem A) (ms_mem ms) aZ nZ Hsat Hmem Hhs HwL HwH Ha0 Hn0 H47 Ha8 Hn8 Hside z Hz). }
  assert (Hna_new : forall q, aZ <= q < aZ + nZ -> ~ inl (vm_noaccess (m_vmmaps model')) q).
  { intros q Hq Hi. rewrite F3 in Hi. apply (Hfree q Hq). right. right. exact (mr_na_maps segs fs0 ρ _ _ HM q Hi). }
  assert (Hna_old : forall q, inl (vm_noaccess (m_vmmaps model')) q -> inl (vm_noaccess (m_vmmaps model)) q)
    by (intros q Hi; rewrite F3 in Hi; exact Hi).
  apply (R_sys_post segs LIM fs0 ρ A _ ms model _ ret rvx _ HR); try reflexivity; try assumption.
  - rewrite F4. exact Hh.
  - rewrite F5. exact Hl.
  - cbn [with_model a_mem]. apply (RMem_fix segs ρ (a_mem A) (ms_mem ms) _ model aZ nZ R0 C0); assumption.
  - cbn [with_model a_mem]. apply (hs_ok_fix ρ (a_mem A) (ms_mem ms) _ aZ nZ R0 C0); assumption.
  - apply (mem_cov_fix segs (ms_mem ms) _ model _ aZ nZ); assumption.
  - cbn [with_model a_mem]. apply (comp_inv_fix segs ρ (a_mem A) model _ aZ nZ R0 C0); assumption.
  - cbn [with_model a_mem]. apply (na_ok_fix segs ρ (a_mem A) (ms_mem ms) _ model _ aZ nZ R0 C0); assumption.
Qed.

(* [comment removed for export] *)
Hypothesis Hg : 4096 * ρ g = bv_unsigned a.
Hypothesis Hghi : ρ g <= ghi.

Lemma P_smod : smod ρ ts w_zero = aZ.
Proof.
  unfold smod. cbn [teval]. change (wZ w_zero) with 0. rewrite Hg. destruct P_bounds as (B1 & _ & B3 & _). rewrite Z.mod_small by lia. lia.
Qed.

Lemma P_gform : leval ρ (gform g) = aZ.
Proof. unfold gform. rewrite leval_lvar. exact Hg. Qed.

Lemma P_val : xv_val ρ (XS ts w_zero) a.
Proof. cbn [xv_val]. rewrite P_smod. reflexivity. Qed.

(* [comment removed for export] *)
Lemma P_facts : sat ρ (grant_facts g nZ (am_atop am) ghi true (am_maps am) (res_lits (segments_reserved segs)) (a_facts A)).
Proof.
  destruct P_bounds as (B1 & B2 & B3 & B4). destruct P_atop as [[T1 T2] _].
  apply (grant_facts_sat ρ g aZ nZ Hg); try assumption; try lia.
  - rewrite <- (mr_atop segs fs0 ρ _ _ HM). exact B2.
  - intros e He. pose proof (MR_ent segs fs0 ρ am model e HM He) as Hek.
    pose proof (grant_free_maps model a nZ (proj1 Hn) Hok _ (MR_ent_in segs fs0 ρ am model e HM He)) as D.
    unfold iv_disj in D. rewrite (ent_val_bas ρ e Hek), (ent_val_bsz ρ e Hek) in D. exact D.
  - apply res_lits_disj. intros q Hq. rewrite <- (mr_res segs fs0 ρ _ _ HM) in Hq. exact (grant_free_res model a nZ (proj1 Hn) Hok q Hq).
  - intros _. exact P_side.
Qed.

Lemma P_span : am_shadow am = true -> var_ent (AE (gform g) nZ false) = true -> aZ + nZ <= sh_lo \/ sh_hi <= aZ.
Proof. intros _ _. exact P_side. Qed.

Theorem R_grant_na :
  RR ρ (with_model A (npc A) (aset (a_regs A) reg_a0 (XS ts w_zero)) (a_mem A) s' (am_grant am (AE (gform g) nZ true) (g + 1)%uint63) (a_budget A))
     (mkCfg (setx ms (Z_to_bv 5 10) a pc' (ms_resv ms) (apply_unmaps (ms_mem ms) [(a, n)])) (null_na_model flags a n model)).
Proof. apply R_grant_na_gen; [exact P_gform | reflexivity | exact P_val | exact P_facts | intros _ _; exact P_side | reflexivity]. Qed.

(* [comment removed for export] *)
Theorem R_grant_rw (b' : Z) :
  has_wit (a_facts A) ls_beg ls_end (a_mem A) = true -> has_wit (a_facts A) hs_beg hs_hi (a_mem A) = true ->
  vm_backing_used model + (if mmap_noreserve_b flags then 0 else nZ) <= b' ->
  RR ρ (with_model A (npc A) (aset (a_regs A) reg_a0 (XS ts w_zero)) (zero_rg ts w_zero nZ :: comp_rg ts w_zero nZ :: a_mem A) s'
          (am_grant am (AE (gform g) nZ false) (g + 1)%uint63) b')
     (mkCfg (setx ms (Z_to_bv 5 10) a pc' (ms_resv ms) (apply_zeros (ms_mem ms) [(a, n)])) (null_rw_model flags a n model)).
Proof.
  intros HwL HwH Hbud. destruct rw_fields as (F1 & F2 & F3 & F4 & F5).
  assert (Ete : teval ρ ts + wS w_zero = aZ) by (cbn [teval]; change (wS w_zero) with 0; lia).
  apply (R_grant_rw_gen ts w_zero (XS ts w_zero) a s' _ _ b' P_smod Ete eq_refl eq_refl P_val P_facts); try assumption.
  - apply (MR_grant_rw segs fs0 ρ am model HM (AE (gform g) nZ false) a nZ flags); [exact P_gform | reflexivity | exact (proj1 Hn) | exact Hok | | exact Hbigf | | reflexivity].
    + intros _ _. exact P_side.
    + intros Hf. discriminate Hf.
  - pose proof P_used_rw. lia.
Qed.

End Post.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
Variable cfg : SpuriousCfg.
Hypothesis Hcfg2 : sc_alloc cfg = false.
Variable KT : valuation -> list byte -> TSet.
Hypothesis KT_agree : forall ρ ρ' o, (forall x, entry_var x = true -> ρ' x = ρ x) -> KT ρ' o = KT ρ o.

Notation Snd B := (forall ρ c, RR ρ B c -> forall o, out_val ρ B o -> realizes_cfg segs cfg c (KT ρ o)).

Lemma R_agree_h : forall v ρ ρ' (A : AST) c, (forall x, x <> v -> ρ' x = ρ x) -> state_occ v A = false -> RR ρ A c -> RR ρ' A c.
Proof. intros v ρ ρ' A c Hag Ho HR. exact (R_agree segs LIM MRm (MR_agree segs fs0) v ρ ρ' A c Hag Ho HR). Qed.

Lemma w_is0_lit (z : Z) : 0 < z < two64 -> w_is0 (Z_to_bv 64 z) = false.
Proof.
  intros H. unfold w_is0. destruct (bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0)) eqn:E; [|reflexivity].
  apply bv_eqb_eq in E. apply (f_equal bv_unsigned) in E. rewrite u_Z_to_bv in E by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0 in E. lia.
Qed.

(* [comment removed for export] *)
Lemma null_core (A : AST) (ρ : valuation) (ms : machine_state) (model : Model) (w : bv 32) (o : list byte)
    (len tlo thi : Z) (na lz : bool) :
  let nZ := page_round_up_Z len in
  let g := am_next (a_model A) in
  let tsg := [(g, 4096)] in
  RR ρ A (mkCfg ms model) -> fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = true -> out_val ρ A o ->
  pc_ok (npc A) = true -> bv_unsigned (rg ms (Z_to_bv 5 17)) = 222 -> state_occ g A = false ->
  0 < len < 70368744177664 -> rg ms (Z_to_bv 5 11) = Z_to_bv 64 len ->
  mmap_off_aligned_b (rg ms (Z_to_bv 5 15)) = true -> mmap_anon_b (rg ms (Z_to_bv 5 13)) = true ->
  (if na then mmap_modeled_b (rg ms (Z_to_bv 5 12)) (rg ms (Z_to_bv 5 13)) (rg ms (Z_to_bv 5 15)) = false
              /\ mmap_noaccess_b (rg ms (Z_to_bv 5 12)) (rg ms (Z_to_bv 5 13)) (rg ms (Z_to_bv 5 15)) = true
   else mmap_modeled_b (rg ms (Z_to_bv 5 12)) (rg ms (Z_to_bv 5 13)) (rg ms (Z_to_bv 5 15)) = true) ->
  mmap_noreserve_b (rg ms (Z_to_bv 5 13)) = lz ->
  lrange (a_facts A) (am_atop (a_model A)) = Some (tlo, thi) ->
  am_shadow (a_model A) = true -> eb_above (a_facts A) (am_atop (a_model A)) (a_mem A) = true -> pack_ok segs (a_model A) nZ tlo = true ->
  (na ||| lz ||| (a_budget A + nZ <=? LIM)) = true ->
  (forall R, In R (a_mem A) -> 0 < to_Z (rg_n R)) ->
  (na ||| (has_wit (a_facts A) ls_beg ls_end (a_mem A) &&& has_wit (a_facts A) hs_beg hs_hi (a_mem A))) = true ->
  (lz = true -> AxLz.BIGMIN <= nZ) ->
  Snd (with_model A (npc A) (aset (a_regs A) reg_a0 (XS tsg w_zero))
         (if na then a_mem A else zero_rg tsg w_zero nZ :: comp_rg tsg w_zero nZ :: a_mem A)
         (grant_facts g nZ (am_atop (a_model A)) ((thi - nZ) / 4096) true (am_maps (a_model A)) (res_lits (segments_reserved segs)) (a_facts A))
         (am_grant (a_model A) (AE (gform g) nZ na) (g + 1)%uint63)
         (if na ||| lz then a_budget A else a_budget A + nZ)) ->
  realizes_cfg segs cfg (mkCfg ms model) (KT ρ o).
Proof.
  intros nZ g tsg HR Hf He Ho Hpc H17 Hfresh Hlen Hlw Hoff Hanon Hshape Hlz Et Hsh Heb Hpack Hbud Hpos Hwit Hbigl HS.
  pose proof HR as [Hpc0 Hal Hsvc Hregs Hres Hrom Hmem HM Hh [Hb Hl] Hsat Hhs Hcov Hcomp Hna]. cbn [cfg_ms cfg_model] in *.
  destruct (page_round_up_facts len (proj1 Hlen)) as (N1 & N2 & N3). fold nZ in N1, N2, N3.
  assert (Hn46 : 0 < nZ < 2 ^ 47) by lia.
  set (x8 := rg ms (Z_to_bv 5 17)) in *.
  set (L := rg ms (Z_to_bv 5 11)) in *. set (P := rg ms (Z_to_bv 5 12)) in *. set (F := rg ms (Z_to_bv 5 13)) in *. set (O := rg ms (Z_to_bv 5 15)) in *.
  assert (HuL : bv_unsigned L = len) by (rewrite Hlw; apply u_Z_to_bv; unfold two64; lia).
  assert (Hl0 : w_is0 L = false) by (rewrite Hlw; apply w_is0_lit; unfold two64; lia).
  assert (Hchk : forall eff m0, check_syscall (sys_input segs (latch ms) x8) eff m0
                 = check_mmap (rg ms (Z_to_bv 5 10)) L P F (rg ms (Z_to_bv 5 14)) O eff m0)
    by (intros eff m0; exact (check_syscall_222 segs (latch ms) x8 eff m0 H17)).
  assert (HnZ : page_round_up_Z (bv_unsigned L) = nZ) by (rewrite HuL; reflexivity).
  assert (Hoffm : injected_family_off cfg (sys_input segs (latch ms) x8) = true).
  { apply family_off_alloc; [exact Hcfg2 | rewrite H17; cbn; tauto | rewrite H17; lia]. }
  (* [comment removed for export] *)
  assert (Hex : exists a0, null_ok model nZ a0).
  { apply (MR_grant_exists segs fs0 ρ (a_model A) model nZ HM N1). unfold pack_ok in Hpack. apply Z.leb_le in Hpack.
    pose proof (lrange_sound ρ _ _ Hsat _ Et) as X. cbn [fst snd] in X. lia. }
  assert (Hback : na = false -> mmap_noreserve_backed_ok F model nZ = true).
  { intros ->. unfold mmap_noreserve_backed_ok. rewrite Hlz. destruct lz; [reflexivity|]. cbn in Hbud. apply Z.leb_le in Hbud. apply Z.leb_le. lia. }
  apply (rzc_latch segs cfg ms model w _ Hh Hsvc Hf He).
  apply (rzc_sys_silent segs cfg (latch ms) model x8 (KT ρ o) Hh eq_refl).
  - rewrite Hchk. apply chk_mmap_null_modeled; try assumption. destruct na; [right; exact Hshape | left; exact Hshape].
  - intros eff m' evs Hc. rewrite Hchk in Hc. destruct na.
    + destruct Hshape as [Sm Sn]. destruct (chk_mmap_null_na _ L P F _ O Hoff Hanon Hl0 eff model m' evs Sm Sn Hc) as [-> [[_ ->]|[a0 [_ [_ ->]]]]];
        (split; [reflexivity|]); [exact Hh|]. rewrite HnZ.
      destruct (na_fields model a0 nZ F) as (_ & _ & _ & F4 & _). rewrite F4. exact Hh.
    + destruct (chk_mmap_null_rw _ L P F _ O Hoff Hanon Hl0 eff model m' evs Hshape Hc) as [-> [[_ ->]|[a0 [_ [_ [_ ->]]]]]];
        (split; [reflexivity|]); [exact Hh|]. rewrite HnZ.
      destruct (rw_fields model a0 nZ F) as (_ & _ & _ & F4 & _). rewrite F4. exact Hh.
  - destruct Hex as [a0 Ha0]. pose proof (grant_bounds model a0 nZ N1 Ha0) as (B1 & B2 & B3 & B4).
    assert (Hnr : refusal_b (sys_input segs (latch ms) x8) model a0 = false).
    { rewrite (refusal_b_222 segs (latch ms) x8 model a0 H17). apply refusal_below.
      pose proof (alloc_top_room (m_vmmaps model)) as Rm. unfold stack_max_size in Rm. lia. }
    destruct na.
    + destruct Hshape as [Sm Sn]. exists (mkEffectU a0 [] [] [(a0, Z_to_bv 64 nZ)] [] []), (null_na_model F a0 (Z_to_bv 64 nZ) model). split; [|exact Hnr].
      rewrite Hchk, <- HnZ. apply chk_mmap_grant_na; try assumption; rewrite HnZ; [lia | exact Ha0].
    + exists (mkEffect a0 [] [(a0, Z_to_bv 64 nZ)]), (null_rw_model F a0 (Z_to_bv 64 nZ) model). split; [|exact Hnr].
      rewrite Hchk, <- HnZ. apply chk_mmap_grant_rw; try assumption; rewrite HnZ; [lia | exact Ha0 | exact (Hback eq_refl)].
  - intros eff m' Hc Hnr. specialize (Hnr Hoffm). rewrite Hchk in Hc.
    rewrite (refusal_b_222 segs (latch ms) x8 model _ H17) in Hnr.
    (* [comment removed for export] *)
    assert (Hcont : forall a0, null_ok model nZ a0 -> forall (mem' : word -> option byte) (m2 : Model),
              (forall ρ', 4096 * ρ' g = bv_unsigned a0 -> ρ' g <= (thi - nZ) / 4096 -> RR ρ' A (mkCfg ms model) ->
                 RR ρ' (with_model A (npc A) (aset (a_regs A) reg_a0 (XS tsg w_zero))
                         (if na then a_mem A else zero_rg tsg w_zero nZ :: comp_rg tsg w_zero nZ :: a_mem A)
                         (grant_facts g nZ (am_atop (a_model A)) ((thi - nZ) / 4096) true (am_maps (a_model A)) (res_lits (segments_reserved segs)) (a_facts A))
                         (am_grant (a_model A) (AE (gform g) nZ na) (g + 1)%uint63)
                         (if na ||| lz then a_budget A else a_budget A + nZ))
                      (mkCfg (setx ms (Z_to_bv 5 10) a0 (ms_pc_val ms + Z_to_bv 64 4)%bv (ms_resv ms) mem') m2)) ->
              realizes_cfg segs cfg (mkCfg (setx ms (Z_to_bv 5 10) a0 (ms_pc_val ms + Z_to_bv 64 4)%bv (ms_resv ms) mem') m2) (KT ρ o)).
    { intros a0 Ha0 mem' m2 Hpost. destruct Ha0 as (A1 & A2 & A3 & A4). unfold page_size in A1.
      set (ρ' := upd_val ρ g (bv_unsigned a0 / 4096)).
      assert (Hag : forall x, x <> g -> ρ' x = ρ x) by exact (upd_val_agree ρ g _).
      assert (Eg : 4096 * ρ' g = bv_unsigned a0).
      { unfold ρ'. rewrite upd_val_same. pose proof (Z.div_mod (bv_unsigned a0) 4096 ltac:(lia)) as D. rewrite A1 in D. lia. }
      assert (Egh : ρ' g <= (thi - nZ) / 4096).
      { unfold ρ'. rewrite upd_val_same. apply Z.div_le_mono; [lia|].
        pose proof (lrange_sound ρ _ _ Hsat _ Et) as X. cbn [fst snd] in X. rewrite <- (mr_atop segs fs0 ρ _ _ HM) in X. lia. }
      rewrite <- (KT_agree ρ ρ' o (agree_entry g ρ ρ' Hag (occ_entry g A Hfresh))).
      exact (HS ρ' _ (Hpost ρ' Eg Egh (R_agree_h g ρ ρ' A _ Hag Hfresh HR)) o (out_agree g ρ ρ' A o Hag Hfresh Ho)). }
    destruct na.
    + destruct Hshape as [Sm Sn]. destruct (chk_mmap_null_na _ L P F _ O Hoff Hanon Hl0 eff model m' [] Sm Sn Hc) as [_ [[-> _]|[a0 [Ha0 [-> ->]]]]].
      * cbn [eff_ret] in Hnr. rewrite refusal_enomem in Hnr. discriminate Hnr.
      * rewrite HnZ in *. exists (null_na_model F a0 (Z_to_bv 64 nZ) model). split; [apply materialize_nil|].
        rewrite adv_effect, eff_mem_unmaps. cbn [eff_ret]. apply (Hcont a0 Ha0). intros ρ' Eg Egh HR'.
        exact (R_grant_na ρ' A ms model g a0 nZ F _ HR' Hpc Hn46 N2 Ha0 Hsh Heb ltac:(rewrite Hlz; exact Hbigl) Eg Egh).
    + destruct (chk_mmap_null_rw _ L P F _ O Hoff Hanon Hl0 eff model m' [] Hshape Hc) as [_ [[-> _]|[a0 [Ha0 [Hbk [-> ->]]]]]].
      * cbn [eff_ret] in Hnr. rewrite refusal_enomem in Hnr. discriminate Hnr.
      * rewrite HnZ in *. exists (null_rw_model F a0 (Z_to_bv 64 nZ) model). split; [apply materialize_nil|].
        rewrite adv_effect, eff_mem_zeros. cbn [eff_ret]. apply (Hcont a0 Ha0). intros ρ' Eg Egh HR'.
        cbn in Hwit. apply andb_prop in Hwit as [W1 W2].
        pose proof HR' as [_ _ _ _ _ _ _ _ _ [Hb' _] _ _ _ _ _]. cbn [cfg_model] in Hb'.
        apply (R_grant_rw ρ' A ms model g a0 nZ F _ HR' Hpc Hn46 N2 Ha0 Hsh Heb ltac:(rewrite Hlz; exact Hbigl) Hpos Eg Egh _ W1 W2).
        rewrite Hlz. cbn [orb]. destruct lz; lia.
Qed.

Theorem sys_mmap_null_sound (A : AST) (l : list AST) :
  pc_ok (npc A) = true -> xlit (aget (a_regs A) 17%uint63) = Some 222 -> state_occ (am_next (a_model A)) A = false ->
  sys_mmap_null segs LIM A = Some l -> (forall B, In B l -> Snd B) ->
  forall ρ c, RR ρ A c -> (exists w, fetch_word segs (ms_pc_val (cfg_ms c)) = Some w /\ is_ecall w = true) ->
  forall o, out_val ρ A o -> realizes_cfg segs cfg c (KT ρ o).
Proof.
  intros Hpc H17x Hfresh Hs HS ρ [ms model] HR [w [Hf He]] o Ho. cbn [cfg_ms] in Hf.
  unfold sys_mmap_null in Hs. cbv zeta in Hs.
  destruct (null_shape A) as [[[nZ na] lz]|] eqn:Esh; [|discriminate Hs].
  destruct (lrange (a_facts A) (am_atop (a_model A))) as [[tlo thi]|] eqn:Et; [|discriminate Hs].
  match type of Hs with (if ?c then _ else _) = _ => destruct c eqn:Eck; [|discriminate Hs] end. injection Hs as <-.
  apply andb_prop in Eck as [Eck Hbigc]. apply andb_prop in Eck as [Eck Hwit]. apply andb_prop in Eck as [Eck Hpos]. apply andb_prop in Eck as [Eck Hbud].
  apply andb_prop in Eck as [Eck Hpack]. apply andb_prop in Eck as [Hsh Heb].
  pose proof (lforall_forall _ _ Hpos) as Hpos'. cbv beta in Hpos'.
  assert (Hpos2 : forall R, In R (a_mem A) -> 0 < to_Z (rg_n R)) by (intros R0 HIn; apply Z.ltb_lt; exact (Hpos' R0 HIn)).
  pose proof (r_regs _ _ _ _ _ _ _ HR) as Hregs. cbn [cfg_ms] in Hregs.
  unfold null_shape in Esh. cbv zeta in Esh.
  destruct (xlit (aget (a_regs A) 11%uint63)) as [len|] eqn:E11; [|discriminate Esh].
  destruct (xlit (aget (a_regs A) 12%uint63)) as [prot|] eqn:E12; [|discriminate Esh].
  destruct (xlit (aget (a_regs A) 13%uint63)) as [flags|] eqn:E13; [|discriminate Esh].
  destruct (xlit (aget (a_regs A) 15%uint63)) as [off|] eqn:E15; [|discriminate Esh].
  match type of Esh with (if ?c then _ else _) = _ => destruct c eqn:Ec; [|discriminate Esh] end. injection Esh as <- <- <-.
  apply andb_prop in Ec as [Ec Cprot]. apply andb_prop in Ec as [Ec Cflags]. apply andb_prop in Ec as [Ec Coff].
  apply andb_prop in Ec as [C1 C2]. apply Z.ltb_lt in C1. apply Z.ltb_lt in C2. apply Z.eqb_eq in Coff. subst off.
  assert (H17 : bv_unsigned (rg ms (Z_to_bv 5 17)) = 222) by exact (reg_lit ρ _ ms (Z_to_bv 5 17) 17%uint63 222 Hregs eq_refl H17x).
  assert (W11 : rg ms (Z_to_bv 5 11) = Z_to_bv 64 len) by exact (rg_of_lit _ _ (reg_lit ρ _ ms (Z_to_bv 5 11) 11%uint63 len Hregs eq_refl E11)).
  assert (W12 : rg ms (Z_to_bv 5 12) = Z_to_bv 64 prot) by exact (rg_of_lit _ _ (reg_lit ρ _ ms (Z_to_bv 5 12) 12%uint63 prot Hregs eq_refl E12)).
  assert (W13 : rg ms (Z_to_bv 5 13) = Z_to_bv 64 flags) by exact (rg_of_lit _ _ (reg_lit ρ _ ms (Z_to_bv 5 13) 13%uint63 flags Hregs eq_refl E13)).
  assert (W15 : rg ms (Z_to_bv 5 15) = Z_to_bv 64 0) by exact (rg_of_lit _ _ (reg_lit ρ _ ms (Z_to_bv 5 15) 15%uint63 0 Hregs eq_refl E15)).
  refine (null_core A ρ ms model w o len tlo thi (prot =? 0) (flags =? 16418) HR Hf He Ho Hpc H17 Hfresh (conj C1 C2) W11 _ _ _ _ Et Hsh Heb Hpack Hbud Hpos2 Hwit _
            (HS _ (or_introl eq_refl))).
  - rewrite W15. reflexivity.
  - rewrite W13. apply orb_prop in Cflags as [X|X]; apply Z.eqb_eq in X; subst flags; reflexivity.
  - rewrite W12, W13, W15. apply orb_prop in Cprot as [X|X]; apply Z.eqb_eq in X; subst prot;
      apply orb_prop in Cflags as [Y|Y]; apply Z.eqb_eq in Y; subst flags; cbn; first [reflexivity | split; reflexivity].
  - rewrite W13. apply orb_prop in Cflags as [X|X]; apply Z.eqb_eq in X; subst flags; reflexivity.
  - intros Elz. rewrite Elz in Hbigc. cbn in Hbigc. apply Z.leb_le in Hbigc. exact Hbigc.
Qed.

End Sound.

End Main.
