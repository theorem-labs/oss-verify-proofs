(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxAcct.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWAcc AxLazy AxLin AxVal AxBytes AxMem AxZZ AxState AxSys AxMeasure AxSysNode AxSysMmap AxGrant AxSysFix AxPostFix.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxFd AxModelRel AxMRFix AxSys2B.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_round_up_bounds (len : Z) : 0 < len -> len <= page_round_up_Z len < len + 4096 /\ page_round_up_Z len mod 4096 = 0.
Proof.
  intros H. unfold page_round_up_Z, page_size. pose proof (Z.div_mod (len + 4095) 4096 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (len + 4095) 4096 ltac:(lia)) as B.
  replace (len + 4096 - 1) with (len + 4095) by lia. split; [lia | apply Z_mod_mult].
Qed.

Lemma fix_shape_spec (A : AST) (prot nZ : Z) (lz : bool) :
  fix_shape A prot = Some (nZ, lz) ->
  exists len flags, xlit (aget (a_regs A) 11%uint63) = Some len /\ xlit (aget (a_regs A) 12%uint63) = Some prot
    /\ xlit (aget (a_regs A) 13%uint63) = Some flags /\ xlit (aget (a_regs A) 15%uint63) = Some 0
    /\ 0 < len < 70368744177664 /\ nZ = page_round_up_Z len /\ (flags = 50 \/ flags = 16434) /\ lz = (flags =? 16434).
Proof.
  unfold fix_shape. destruct (xlit (aget (a_regs A) 11%uint63)) as [len|]; [|discriminate].
  destruct (xlit (aget (a_regs A) 12%uint63)) as [p|]; [|discriminate].
  destruct (xlit (aget (a_regs A) 13%uint63)) as [flags|]; [|discriminate].
  destruct (xlit (aget (a_regs A) 15%uint63)) as [off|]; [|discriminate].
  destruct ((0 <? len) &&& (len <? 70368744177664) &&& (off =? 0) &&& (p =? prot) &&& ((flags =? 50) ||| (flags =? 16434))) eqn:E; [|discriminate].
  intros H. injection H as <- <-.
  apply andb_prop in E as [E E5]. apply andb_prop in E as [E E4]. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
  apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. apply Z.eqb_eq in E3. apply Z.eqb_eq in E4. subst off p.
  exists len, flags. repeat split; try reflexivity; try lia.
  apply orb_prop in E5 as [E5|E5]; apply Z.eqb_eq in E5; [left | right]; exact E5.
Qed.

Lemma len_shape_spec (A : AST) (nZ : Z) :
  len_shape A = Some nZ -> exists len, xlit (aget (a_regs A) 11%uint63) = Some len /\ 0 < len < 70368744177664 /\ nZ = page_round_up_Z len.
Proof.
  unfold len_shape. destruct (xlit (aget (a_regs A) 11%uint63)) as [len|]; [|discriminate].
  destruct ((0 <? len) &&& (len <? 70368744177664)) eqn:E; [|discriminate]. intros H. injection H as <-.
  apply andb_prop in E as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. exists len. repeat split; try reflexivity; lia.
Qed.

Section Shared.
Variable segs : list Segment.
Variable fs0 : Fs.Fs.
Hypothesis Hlow : segs_low segs.

Notation MRm := (MR segs fs0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Gate.
Variable ρ : valuation.
Variable am : amodel.
Variable m : Model.
Hypothesis HM : MRm ρ am m.
Variable e0 : aent.
Hypothesis He0 : In e0 (am_maps am).
Variable f : lin.
Variable len : Z.
Hypothesis Hlen : 0 < len < 70368744177664.
Let nZ := page_round_up_Z len.
Hypothesis Hlo : leval ρ (ae_base e0) <= leval ρ f.
Hypothesis Hhi : leval ρ f + nZ <= leval ρ (ae_base e0) + ae_size e0.
Hypothesis Hal : leval ρ f mod 4096 = 0.
Variables addr lenw : word.
Hypothesis Haddr : bv_unsigned addr = leval ρ f.
Hypothesis Hlenw : bv_unsigned lenw = len.

Lemma gate_nZ : 0 < nZ /\ nZ < 70368744181760 /\ nZ mod 4096 = 0.
Proof. destruct (page_round_up_bounds len ltac:(lia)) as [B1 B2]. unfold nZ. lia. Qed.

Lemma gate_fix_nZ : fix_nZ lenw = nZ.
Proof. unfold fix_nZ. rewrite Hlenw. reflexivity. Qed.

Lemma gate_addr : addr = Z_to_bv 64 (leval ρ f).
Proof. exact (rg_of_lit addr _ Haddr). Qed.

Lemma gate_fix_n : fix_n lenw = Z_to_bv 64 nZ.
Proof. unfold fix_n. rewrite gate_fix_nZ. reflexivity. Qed.

Lemma gate_n_unsigned : bv_unsigned (fix_n lenw) = nZ.
Proof. rewrite gate_fix_n. apply u_Z_to_bv. pose proof gate_nZ. unfold two64. lia. Qed.

Lemma gate_of_MR : fix_gate m addr lenw.
Proof.
  pose proof gate_nZ as (N1 & N2 & N3). pose proof (MR_ent segs fs0 ρ am m e0 HM He0) as (K1 & K2 & K3).
  pose proof (rng_top segs fs0 ρ am m HM e0 He0 f nZ Hhi) as Ht.
  constructor.
  - rewrite Hlenw. lia.
  - rewrite gate_fix_nZ, Haddr. exact Ht.
  - rewrite Haddr. exact Hal.
  - rewrite Haddr. lia.
  - apply region_free_disj. intros q Hq. rewrite gate_n_unsigned, Haddr.
    exact (rng_res segs fs0 ρ am m HM e0 He0 f nZ Hlo Hhi q Hq).
  - unfold map_contains. apply existsb_exists. exists (ent_val ρ e0). split; [exact (MR_ent_in segs fs0 ρ am m e0 HM He0)|].
    pose proof (ent_val_bas ρ e0 (conj K1 (conj K2 K3))) as Eb. pose proof (ent_val_bsz ρ e0 (conj K1 (conj K2 K3))) as Es.
    unfold bas, bsz in Eb, Es. rewrite Eb, Es, gate_n_unsigned, Haddr. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

End Gate.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section NaFresh.
Variable ρ : valuation.
Variable am : amodel.
Variable model : Model.
Variable A : list region.
Variable mem : word -> option byte.
Hypothesis HM : MRm ρ am model.
Hypothesis HRM : RMem segs ρ A mem.
Hypothesis Hna : na_ok segs ρ A model mem.
Variable e0 : aent.
Hypothesis He0 : In e0 (am_maps am).
Hypothesis Hna0 : ae_na e0 = true.
Variables a n : Z.
Hypothesis Hlo : leval ρ (ae_base e0) <= a.
Hypothesis Hhi : a + n <= leval ρ (ae_base e0) + ae_size e0.
Hypothesis Hexp : forall z, a <= z < a + n -> ~ in_exp ρ (am_exp am) e0 z.
Hypothesis Heb : forall R, In R A -> is_entry R = true -> a + n <= rbase ρ R.

Lemma na_point (z : Z) : a <= z < a + n -> inl (vm_noaccess (m_vmmaps model)) z.
Proof. intros Hz. apply (mr_nacov segs fs0 ρ am model HM e0 z He0 Hna0); [unfold in_ent; lia | exact (Hexp z Hz)]. Qed.

Lemma na_fresh : forall R, In R A -> is_shadow R = false -> forall z, in_rg ρ R z -> ~ (a <= z < a + n).
Proof.
  intros R HR Hs z Hz Hr. destruct HRM as [Hok HRR]. pose proof (regions_ok_in ρ A R Hok HR) as Hwf.
  pose proof (proj1 (Forall_forall _ _) HRR R HR) as HRg. destruct (is_entry R) eqn:Ee.
  - pose proof (Heb R HR Ee). unfold in_rg in Hz. lia.
  - rewrite (RRegion_ne segs ρ mem R Ee) in HRg. unfold in_rg in Hz.
    pose proof (smod_range ρ (rg_ts R) (rg_bo R)) as Hb. fold (rbase ρ R) in Hb. destruct Hwf as (W1 & W2 & _).
    assert (Hx : to_Z (of_Z (z - rbase ρ R)) = z - rbase ρ R) by (rewrite of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
    destruct (HRg (of_Z (z - rbase ρ R)) ltac:(lia)) as [[b [Hrv _]] _]. rewrite Hx in Hrv.
    replace (rbase ρ R + (z - rbase ρ R)) with z in Hrv by lia.
    destruct Hna as [N1 [N2 _]]. unfold rv in Hrv. destruct (mem (wz z)) as [b0|] eqn:E.
    + apply (N1 (wz z)); [rewrite E; discriminate|]. rewrite u_wz by (unfold two64 in *; lia). exact (na_point z Hr).
    + pose proof (seg_rom_in_segs segs (wz z) b Hrv) as Hsg. rewrite u_wz in Hsg by (unfold two64 in *; lia).
      exact (N2 z Hsg (na_point z Hr)).
Qed.

Lemma na_comp_fresh (C0 : region) :
  a mod 8 = 0 -> n mod 8 = 0 -> rbase ρ C0 = a / 8 + sh_off -> to_Z (rg_n C0) = n / 8 ->
  forall R, In R A -> is_shadow R = true -> forall z, in_rg ρ R z -> ~ in_rg ρ C0 z.
Proof.
  intros Ha8 Hn8 Hb Hsz R HR Hs z Hz Hc. destruct Hna as [_ [_ N3]]. unfold in_rg in Hc. rewrite Hb, Hsz in Hc.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.div_mod n 8 ltac:(lia)) as Dn. rewrite Ha8 in Da. rewrite Hn8 in Dn.
  apply (N3 R HR Hs z Hz (8 * (z - sh_off))); [unfold preimage; lia|]. apply na_point. lia.
Qed.

End NaFresh.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma expose_ledger (ρ : valuation) (am : amodel) (model model' : Model) (e0 : aent) (a n : Z) :
  MRm ρ am model -> In e0 (am_maps am) -> leval ρ (ae_base e0) <= a -> a + n <= leval ρ (ae_base e0) + ae_size e0 ->
  vm_maps (m_vmmaps model') = vm_maps (m_vmmaps model) -> alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model) ->
  vm_noaccess (m_vmmaps model') = maps_subtract (vm_noaccess (m_vmmaps model)) a (a + n) ->
  (forall q, a <= q < a + n -> in_ledger_w segs (m_vmmaps model') q)
  /\ (forall q, in_ledger_w segs (m_vmmaps model) q -> in_ledger_w segs (m_vmmaps model') q)
  /\ (forall q, a <= q < a + n -> ~ inl (vm_noaccess (m_vmmaps model')) q)
  /\ (forall q, inl (vm_noaccess (m_vmmaps model')) q -> inl (vm_noaccess (m_vmmaps model)) q).
Proof.
  intros HM He0 Hlo Hhi Em Et En. unfold in_ledger_w. rewrite Em, Et, En. repeat split.
  - intros q Hq. right. right. apply (MR_in_ent_inl segs fs0 ρ am model e0 q HM He0). unfold in_ent. lia.
  - intros q Hq. exact Hq.
  - intros q Hq Hi. apply (inl_subtract1 _ _ _ q (mr_na segs fs0 ρ am model HM)) in Hi as [_ Hi]. exact (Hi Hq).
  - intros q Hi. apply (inl_subtract1 _ _ _ q (mr_na segs fs0 ρ am model HM)) in Hi as [Hi _]. exact Hi.
Qed.

End Shared.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Post.
Variable segs : list Segment.
Variable fs0 : Fs.Fs.
Variable LIM : Z.

Notation MRm := (MR segs fs0).
Notation RR ρ := (R segs amodel (MRm ρ) LIM ρ).

Lemma R_sys_post_B (ρ : valuation) (A B : AST) (ms : machine_state) (model m' : Model) (ret : word) (rv : xv) (mem' : word -> option byte) :
  RR ρ A (mkCfg ms model) ->
  a_pc B = npc A -> pc_ok (npc A) = true -> a_regs B = aset (a_regs A) reg_a0 rv -> a_resv B = a_resv A ->
  xv_val ρ rv ret -> sat ρ (a_facts B) -> MRm ρ (a_model B) m' -> m_halted m' = None ->
  vm_backing_used m' <= a_budget B -> vm_limit (m_vmmaps m') = LIM ->
  RMem segs ρ (a_mem B) mem' -> hs_ok ρ (a_mem B) mem' -> mem_cov segs m' mem' -> comp_inv segs ρ (a_mem B) m' ->
  na_ok segs ρ (a_mem B) m' mem' ->
  RR ρ B (mkCfg (setx ms (Z_to_bv 5 10) ret (ms_pc_val ms + Z_to_bv 64 4) (ms_resv ms) mem') m').
Proof.
  intros HR Epc Hok Eregs Eresv Hv Hsat HM Hh Hb Hl HRM Hhs Hcov Hcomp Hna.
  destruct HR as [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15]. cbn [cfg_ms cfg_model] in *.
  constructor; cbn [cfg_ms cfg_model setx ms_pc_val ms_svc_pending ms_rom ms_mem ms_resv]; try assumption.
  - rewrite Epc. unfold npc. rewrite wbv_add, H1, wbv_four. reflexivity.
  - rewrite Epc. exact (pc_ok_spec _ Hok).
  - reflexivity.
  - rewrite Eregs. change reg_a0 with (ri (Z_to_bv 5 10)). apply RRegs_set; assumption.
  - rewrite Eresv. exact H5.
  - split; assumption.
Qed.

(* [comment removed for export] *)
Lemma adv_zeros (ms : machine_state) (ret a n : word) :
  advance_past_svc (apply_effect (latch ms) (mkEffect ret [] [(a, n)]))
  = setx ms (Z_to_bv 5 10) ret (ms_pc_val ms + Z_to_bv 64 4) (ms_resv ms) (apply_zeros (ms_mem ms) [(a, n)]).
Proof. reflexivity. Qed.

Lemma adv_unmaps (ms : machine_state) (ret a n : word) :
  advance_past_svc (apply_effect (latch ms) (mkEffectU ret [] [] [(a, n)] [] []))
  = setx ms (Z_to_bv 5 10) ret (ms_pc_val ms + Z_to_bv 64 4) (ms_resv ms) (apply_unmaps (ms_mem ms) [(a, n)]).
Proof. reflexivity. Qed.

End Post.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma smod_form (ρ : valuation) (f : lin) :
  0 <= fst f < 9223372036854775808 -> 0 <= leval ρ f < AxAcct.two64 -> smod ρ (snd f) (wofZ (fst f)) = leval ρ f.
Proof.
  intros Hc Hv. unfold smod, leval in *. rewrite wZ_wofZ. unfold AxAcct.two64 in Hv.
  rewrite Zplus_mod_idemp_r. rewrite Z.add_comm. apply Z.mod_small. unfold FastWord.two64. lia.
Qed.

Lemma wZ_form (f : lin) : 0 <= fst f < 9223372036854775808 -> wZ (wofZ (fst f)) = fst f.
Proof. intros Hc. rewrite wZ_wofZ. apply Z.mod_small. unfold FastWord.two64. lia. Qed.

Section Expose.
Variable segs : list Segment.
Variable fs0 : Fs.Fs.
Variable LIM : Z.
Hypothesis Hlow : segs_low segs.

Notation MRm := (MR segs fs0).
Notation RR ρ := (R segs amodel (MRm ρ) LIM ρ).

Variable ρ : valuation.
Variable A : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : RR ρ A (mkCfg ms model).
Variable f : lin.
Variable nZ : Z.
Variable e0 : aent.
Hypothesis Hok : expose_ok A f nZ e0 = true.
Hypothesis He0 : In e0 (am_maps (a_model A)).
Hypothesis HnZ : 0 < nZ < 70368744181760.
Hypothesis HnZ4 : nZ mod 4096 = 0.
Hypothesis Hlo : leval ρ (ae_base e0) <= leval ρ f.
Hypothesis Hhi : leval ρ f + nZ <= leval ρ (ae_base e0) + ae_size e0.
Hypothesis Hexp : forall z, leval ρ f <= z < leval ρ f + nZ -> ~ in_exp ρ (am_exp (a_model A)) e0 z.

(* [comment removed for export] *)
Variable model' : Model.
Hypothesis Em : vm_maps (m_vmmaps model') = vm_maps (m_vmmaps model).
Hypothesis Et : alloc_top (m_vmmaps model') = alloc_top (m_vmmaps model).
Hypothesis En : vm_noaccess (m_vmmaps model') = maps_subtract (vm_noaccess (m_vmmaps model)) (leval ρ f) (leval ρ f + nZ).

Let a := leval ρ f.
Let R0 := zero_rg (snd f) (wofZ (fst f)) nZ.
Let C0 := comp_rg (snd f) (wofZ (fst f)) nZ.
Let mem' := apply_zeros (ms_mem ms) [(Z_to_bv 64 a, Z_to_bv 64 nZ)].

Lemma expose_parts :
  ae_na e0 = true /\ var_ent e0 = true /\ am_shadow (a_model A) = true /\ lin_al 4096 f = true
  /\ 0 <= fst f < 9223372036854775808
  /\ eb_above (a_facts A) (am_atop (a_model A)) (a_mem A) = true /\ ss_wit (a_facts A) (a_mem A) = true
  /\ (forall R, In R (a_mem A) -> 0 < to_Z (rg_n R)).
Proof.
  unfold expose_ok in Hok.
  apply andb_prop in Hok as [H H9]. apply andb_prop in H as [H H8]. apply andb_prop in H as [H H7].
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H5. apply Z.ltb_lt in H6.
  repeat split; try assumption.
  intros R HRin. pose proof (lforall_forall _ _ H9 R HRin) as X. cbv beta in X. apply Z.ltb_lt in X. exact X.
Qed.

Lemma expose_geom :
  0 < a /\ a + nZ <= alloc_top (m_vmmaps model) /\ alloc_top (m_vmmaps model) <= 2 ^ 47 /\ a mod 4096 = 0
  /\ (a + nZ <= sh_lo \/ sh_hi <= a)
  /\ (forall R, In R (a_mem A) -> is_entry R = true -> a + nZ <= rbase ρ R).
Proof.
  destruct expose_parts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof HR as [_ _ _ _ _ _ _ HM _ _ Hsat _ _ _ _]. cbn [cfg_ms cfg_model] in *.
  pose proof (MR_ent segs fs0 ρ _ model e0 HM He0) as (K1 & K2 & K3).
  pose proof (rng_top segs fs0 ρ _ model HM e0 He0 f nZ Hhi) as Ht.
  destruct (eb_above_sound ρ _ _ _ Hsat P6) as [Hat Heb]. rewrite <- (mr_atop segs fs0 ρ _ model HM) in Hat, Heb.
  split; [unfold a; lia|]. split; [exact Ht|]. split; [lia|]. split; [exact (lin_al_sound ρ 4096 f ltac:(lia) P4)|]. split.
  - destruct (mr_span segs fs0 ρ _ model HM P3 e0 He0 P2) as [X|X]; [left | right]; unfold a; lia.
  - intros R HRin He. specialize (Heb R HRin He). unfold a. lia.
Qed.

Lemma expose_regions :
  rg_kind R0 = KZero /\ rg_cells R0 = IEmpty /\ rbase ρ R0 = a /\ to_Z (rg_n R0) = nZ /\ region_wf ρ R0
  /\ rg_kind C0 = KShadow /\ rg_cells C0 = IEmpty /\ rbase ρ C0 = a / 8 + sh_off /\ to_Z (rg_n C0) = nZ / 8 /\ region_wf ρ C0.
Proof.
  destruct expose_parts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct expose_geom as (G1 & G2 & G3 & G4 & G5 & G6).
  assert (Hv : 0 <= leval ρ f < AxAcct.two64) by (fold a; unfold AxAcct.two64; lia).
  destruct (zero_rg_wf ρ (snd f) (wofZ (fst f)) nZ a (smod_form ρ f P5 Hv) ltac:(lia) ltac:(unfold FastWord.two64; lia)) as (Z1 & Z2 & Z3).
  assert (Hw8 : wS (wofZ (fst f)) mod 8 = 0).
  { rewrite (wS_wofZ_small (fst f) P5). unfold lin_al in P4. apply andb_prop in P4 as [P4 _]. apply Z.eqb_eq in P4.
    pose proof (Z.div_mod (fst f) 4096 ltac:(lia)) as D. rewrite P4 in D. rewrite D, Z.add_0_r.
    replace (4096 * (fst f / 4096)) with ((512 * (fst f / 4096)) * 8) by lia. apply Z_mod_mult. }
  assert (Hsum : teval ρ (snd f) + wS (wofZ (fst f)) = a) by (rewrite (wS_wofZ_small (fst f) P5); unfold a, leval; lia).
  destruct (comp_rg_wf ρ (snd f) (wofZ (fst f)) nZ a (lin_al_tdiv8 f P4) Hw8 Hsum ltac:(lia) ltac:(lia) ltac:(lia)) as (C1 & C2 & C3).
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact C1|]. split; [exact C2 | exact C3].
Qed.

Lemma expose_a8 : a mod 8 = 0 /\ nZ mod 8 = 0.
Proof.
  destruct expose_geom as (_ & _ & _ & G4 & _).
  pose proof (Z.div_mod a 4096 ltac:(lia)) as D1. pose proof (Z.div_mod nZ 4096 ltac:(lia)) as D2. rewrite G4 in D1. rewrite HnZ4 in D2.
  split; [rewrite D1 | rewrite D2]; rewrite Z.add_0_r;
    [replace (4096 * (a / 4096)) with ((512 * (a / 4096)) * 8) by lia | replace (4096 * (nZ / 4096)) with ((512 * (nZ / 4096)) * 8) by lia];
    apply Z_mod_mult.
Qed.

Lemma expose_words : bv_unsigned (Z_to_bv 64 a) = a /\ bv_unsigned (Z_to_bv 64 nZ) = nZ.
Proof. destruct expose_geom as (G1 & G2 & G3 & _). split; apply u_Z_to_bv; unfold AxAcct.two64; lia. Qed.

Theorem expose_mem :
  RMem segs ρ (R0 :: C0 :: a_mem A) mem' /\ hs_ok ρ (R0 :: C0 :: a_mem A) mem' /\ mem_cov segs model' mem'
  /\ comp_inv segs ρ (R0 :: C0 :: a_mem A) model' /\ na_ok segs ρ (R0 :: C0 :: a_mem A) model' mem'.
Proof.
  destruct expose_parts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  destruct expose_geom as (G1 & G2 & G3 & G4 & G5 & G6).
  destruct expose_regions as (Z1 & Z2 & Z3 & Z4 & Z5 & C1 & C2 & C3 & C4 & C5).
  destruct expose_a8 as [A8 N8]. destruct expose_words as [Wa Wn].
  pose proof HR as [_ _ _ _ _ _ HRM HM _ _ Hsat Hhs Hcov Hcomp Hna]. cbn [cfg_ms cfg_model] in *.
  destruct (expose_ledger segs fs0 ρ _ model model' e0 a nZ HM He0 Hlo Hhi Em Et En) as (L1 & L2 & L3 & L4).
  assert (Hin : forall z, a <= z < a + nZ -> mem' (wz z) = Some (Z_to_bv 8 0)).
  { intros z Hz. unfold mem'. apply zeros_in; [rewrite Wa, Wn; exact Hz | unfold FastWord.two64; lia]. }
  assert (Hout : forall x : word, ~ (a <= bv_unsigned x < a + nZ) -> mem' x = ms_mem ms x).
  { intros x Hx. unfold mem'. apply zeros_out. rewrite Wa, Wn. exact Hx. }
  assert (Hfresh := na_fresh segs fs0 ρ _ model (a_mem A) (ms_mem ms) HM HRM Hna e0 He0 P1 a nZ Hlo Hhi Hexp G6).
  assert (Hcfresh := na_comp_fresh segs fs0 ρ _ model (a_mem A) (ms_mem ms) HM Hna e0 He0 P1 a nZ Hlo Hhi Hexp C0 A8 N8 C3 C4).
  unfold ss_wit in P7. apply andb_prop in P7 as [W1 W2].
  assert (Hmapped : forall z, in_rg ρ C0 z -> ms_mem ms (wz z) <> None).
  { intros z Hz. unfold in_rg in Hz. rewrite C3, C4 in Hz.
    exact (comp_mapped segs Hlow ρ _ _ _ a nZ Hsat HRM Hhs W1 W2 ltac:(lia) ltac:(lia) ltac:(lia) A8 N8 G5 z Hz). }
  assert (Hn0 : 0 < nZ) by lia. assert (Ha0 : 0 <= a) by lia. assert (H47 : a + nZ <= 2 ^ 47) by lia.
  split; [|split; [|split; [|split]]].
  - eapply RMem_fix with (m := ms_mem ms) (model := model) (a := a) (n := nZ); eassumption.
  - eapply hs_ok_fix with (m := ms_mem ms) (a := a) (n := nZ); eassumption.
  - eapply mem_cov_fix with (m := ms_mem ms) (model := model) (a := a) (n := nZ); eassumption.
  - eapply comp_inv_fix with (model := model) (a := a) (n := nZ); eassumption.
  - eapply na_ok_fix with (m := ms_mem ms) (model := model) (a := a) (n := nZ); eassumption.
Qed.

End Expose.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Main.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hcfg2 : sc_alloc cfg = false.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation MRm := (MR segs fs0).
Notation RR ρ := (R segs amodel (MRm ρ) LIM ρ).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fix_nores (flagsw : word) (flags : Z) : bv_unsigned flagsw = flags -> (flags = 50 \/ flags = 16434) ->
  mmap_noreserve_b flagsw = (flags =? 16434).
Proof.
  intros E H. assert (Ew : flagsw = Z_to_bv 64 flags) by (rewrite <- E; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite Ew. destruct H as [->| ->]; vm_compute; reflexivity.
Qed.

Lemma fix_rw_budget (ρ : valuation) (am : amodel) (model : Model) (e0 : aent) (f : lin) (nZ b : Z) (flagsw : word) (flags : Z) :
  MRm ρ am model -> In e0 (am_maps am) -> 0 < nZ -> nZ mod 4096 = 0 -> leval ρ f mod 4096 = 0 ->
  leval ρ (ae_base e0) <= leval ρ f -> leval ρ f + nZ <= leval ρ (ae_base e0) + ae_size e0 ->
  bv_unsigned flagsw = flags -> (flags = 50 \/ flags = 16434) -> vm_backing_used model <= b ->
  vm_backing_used (fix_rw_model flagsw (Z_to_bv 64 (leval ρ f)) (Z_to_bv 64 nZ) model) <= b + (if flags =? 16434 then 0 else nZ).
Proof.
  intros HM He0 Hn Hn4 Hal Hlo Hhi Ef Hfl Hb.
  pose proof (rng_addr segs fs0 ρ am model HM e0 He0 f nZ Hn Hlo Hhi) as Wa.
  pose proof (rng_n segs fs0 ρ am model HM e0 He0 f nZ Hn Hlo Hhi) as Wn.
  pose proof (rng_two64 segs fs0 ρ am model HM e0 He0 f nZ Hhi) as H64.
  pose proof (MR_maps_nowrap segs fs0 ρ am model HM) as N1. pose proof (mr_na segs fs0 ρ am model HM) as N2.
  pose proof (MR_lazy_nowrap segs fs0 ρ am model HM) as N3.
  destruct Hfl as [Hfl|Hfl]; rewrite Hfl; cbn [Z.eqb Pos.eqb].
  - pose proof (used_fix_rw model flagsw (Z_to_bv 64 (leval ρ f)) (Z_to_bv 64 nZ) N1 N2 N3 ltac:(rewrite Wa, Wn; exact H64) 1 ltac:(lia)
                  ltac:(intros x _; apply SW_le_1; exact (mr_pw segs fs0 ρ am model HM))) as X.
    rewrite Wn in X. lia.
  - pose proof (used_fix_rw_lazy model flagsw (Z_to_bv 64 (leval ρ f)) (Z_to_bv 64 nZ) N1 N2 N3 ltac:(rewrite Wa, Wn; exact H64)
                  ltac:(unfold mmap_noreserve_b; rewrite Ef, Hfl; reflexivity) ltac:(rewrite Wa; exact Hal) ltac:(rewrite Wn; exact Hn4)) as X.
    lia.
Qed.

Theorem sys_fix_rw_sound (A : AST) (l : list AST) :
  pc_ok (npc A) = true -> xlit (aget (a_regs A) 17%uint63) = Some 222 -> sys_fix_rw LIM A = Some l ->
  (forall B, In B l -> forall ρ c, RR ρ B c -> forall o, out_val ρ B o -> realizes_cfg segs cfg c (KT ρ o)) ->
  forall ρ c, RR ρ A c -> (exists w, fetch_word segs (ms_pc_val (cfg_ms c)) = Some w /\ is_ecall w = true) ->
  forall o, out_val ρ A o -> realizes_cfg segs cfg c (KT ρ o).
Proof.
  intros Hpc H17 Hsys HS ρ [ms model] HR [w [Hf He]] o Ho. cbn [cfg_ms] in Hf.
  unfold sys_fix_rw in Hsys.
  destruct (fix_shape A 3) as [[nZ lz]|] eqn:Esh; [|discriminate Hsys].
  destruct (xform (a_facts A) (aget (a_regs A) 10%uint63)) as [f|] eqn:Ef; [|discriminate Hsys].
  destruct (find_ent (a_facts A) f nZ (am_maps (a_model A))) as [e0|] eqn:Ee; [|discriminate Hsys].
  destruct (expose_ok A f nZ e0 &&& lforall (exp_miss (a_facts A) f nZ e0) (am_exp (a_model A))
            &&& (a_budget A + (if lz then 0 else nZ) <=? LIM) &&& (negb lz ||| (65536 <=? ae_size e0))) eqn:Ec; [|discriminate Hsys].
  injection Hsys as <-.
  apply andb_prop in Ec as [Ec Kbig]. apply andb_prop in Ec as [Ec Hbud]. apply andb_prop in Ec as [Hok Hmiss]. apply Z.leb_le in Hbud.
  destruct (fix_shape_spec A 3 nZ lz Esh) as (len & flags & L11 & L12 & L13 & L15 & Hlen & EnZ & Hfl & Elz).
  subst nZ. set (nZ := page_round_up_Z len) in *.
  pose proof HR as [H1 H2 H3 H4 H5 H6 H7 H8 H9 [H10 H10'] H11 H12 H13 H14 H15]. cbn [cfg_ms cfg_model] in *.
  (* [comment removed for export] *)
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 17) 17%uint63 222 H4 eq_refl H17) as R17.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 11) 11%uint63 len H4 eq_refl L11) as R11.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 12) 12%uint63 3 H4 eq_refl L12) as R12.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 13) 13%uint63 flags H4 eq_refl L13) as R13.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 15) 15%uint63 0 H4 eq_refl L15) as R15.
  pose proof (xform_sound ρ _ _ (rg ms (Z_to_bv 5 10)) f H11 (H4 (Z_to_bv 5 10)) Ef) as R10.
  (* [comment removed for export] *)
  destruct (find_ent_spec _ f nZ _ e0 Ee) as [He0 Hhas]. destruct (ent_has_sound ρ _ f nZ e0 H11 Hhas) as [Hlo Hhi].
  destruct (page_round_up_bounds len ltac:(lia)) as [Hb1 Hb2]. fold nZ in Hb1, Hb2.
  assert (HnZ : 0 < nZ < 70368744181760) by lia.
  destruct (expose_parts A f nZ e0 Hok) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof (lin_al_sound ρ 4096 f ltac:(lia) P4) as Hal.
  assert (Hexp : forall z, leval ρ f <= z < leval ρ f + nZ -> ~ in_exp ρ (am_exp (a_model A)) e0 z)
    by (intros z Hz; exact (exp_miss_sound ρ _ f nZ e0 _ z H11 Hmiss Hz)).
  (* [comment removed for export] *)
  pose proof (gate_of_MR segs fs0 ρ _ model H8 e0 He0 f len Hlen Hlo Hhi
                Hal (rg ms (Z_to_bv 5 10)) (rg ms (Z_to_bv 5 11)) R10 R11) as G.
  pose proof (fix_rw_shape_lit (rg ms (Z_to_bv 5 12)) (rg ms (Z_to_bv 5 13)) (rg ms (Z_to_bv 5 15)) R12 ltac:(rewrite R13; exact Hfl) R15) as S.
  pose proof (gate_addr ρ f (rg ms (Z_to_bv 5 10)) R10) as Eaddr.
  pose proof (gate_fix_n len (rg ms (Z_to_bv 5 11)) R11) as En. fold nZ in En.
  set (addr := rg ms (Z_to_bv 5 10)) in *. set (flagsw := rg ms (Z_to_bv 5 13)) in *.
  set (m' := fix_rw_model flagsw addr (fix_n (rg ms (Z_to_bv 5 11))) model).
  assert (Em' : m' = fix_rw_model flagsw (Z_to_bv 64 (leval ρ f)) (Z_to_bv 64 nZ) model) by (unfold m'; rewrite En, Eaddr; reflexivity).
  assert (Hused : vm_backing_used m' <= a_budget A + (if lz then 0 else nZ)).
  { rewrite Em', Elz. exact (fix_rw_budget ρ _ model e0 f nZ _ flagsw flags H8 He0 ltac:(lia) Hb2 Hal Hlo Hhi R13 Hfl H10). }
  assert (Hlim : vm_limit (m_vmmaps m') = LIM) by (unfold m'; rewrite fix_rw_vmmaps; exact H10').
  assert (Hbok : mmap_fixed_rw_budget_ok flagsw model addr (fix_n (rg ms (Z_to_bv 5 11))) = true).
  { unfold mmap_fixed_rw_budget_ok, vm_backing_within_limit. fold (fix_rw_model flagsw addr (fix_n (rg ms (Z_to_bv 5 11))) model). fold m'.
    apply Z.leb_le. rewrite Hlim. lia. }
  (* [comment removed for export] *)
  apply (rzc_latch segs cfg ms model w (KT ρ o) H9 H3 Hf He).
  apply (rzc_sys_silent segs cfg (latch ms) model (rg ms (Z_to_bv 5 17)) (KT ρ o) H9 eq_refl).
  - rewrite (check_syscall_222 segs (latch ms) _ _ model R17).
    exact (chk_fix_rw_modeled model addr (rg ms (Z_to_bv 5 11)) (rg ms (Z_to_bv 5 12)) flagsw (rg ms (Z_to_bv 5 14)) (rg ms (Z_to_bv 5 15)) S G _).
  - intros eff m1 evs Hc. rewrite (check_syscall_222 segs (latch ms) _ _ model R17) in Hc.
    destruct (chk_fix_rw_halted model addr _ _ flagsw _ _ eff m1 evs S G Hc) as [E1 E2]. split; [exact E1 | rewrite E2; exact H9].
  - exists (mkEffect addr [] [(addr, fix_n (rg ms (Z_to_bv 5 11)))]), m'. split.
    + rewrite (check_syscall_222 segs (latch ms) _ _ model R17).
      exact (chk_fix_rw_grant model addr (rg ms (Z_to_bv 5 11)) (rg ms (Z_to_bv 5 12)) flagsw (rg ms (Z_to_bv 5 14)) (rg ms (Z_to_bv 5 15)) S G Hbok).
    + rewrite (refusal_b_222 segs (latch ms) _ model _ R17). exact (fix_addr_not_errno model addr _ G).
  - intros eff m1 Hc Hnr. rewrite (check_syscall_222 segs (latch ms) _ _ model R17) in Hc.
    destruct (chk_fix_rw model addr _ _ flagsw _ _ S G eff m1 [] Hc) as [Hr|(-> & -> & _ & _)].
    + exfalso. specialize (Hnr (family_off_alloc segs cfg (latch ms) _ Hcfg2 ltac:(rewrite R17; cbn; tauto) ltac:(rewrite R17; lia))).
      rewrite (refusal_b_222 segs (latch ms) _ model _ R17) in Hnr.
      change (ret_in_errnos [ENOMEM] (eff_ret eff)) with (errno_ret_in mmap_errnos (eff_ret eff)) in Hnr. congruence.
    + fold m'. exists m'. split; [exact (materialize_nil m')|]. rewrite adv_zeros.
      set (B := expose_next A (aset (a_regs A) reg_a0 (aget (a_regs A) reg_a0)) f nZ e0 (a_budget A + (if lz then 0 else nZ))).
      apply (HS B (or_introl eq_refl) ρ); [|exact Ho].
      assert (Hmods : vm_maps (m_vmmaps m') = vm_maps (m_vmmaps model) /\ alloc_top (m_vmmaps m') = alloc_top (m_vmmaps model)
                      /\ vm_noaccess (m_vmmaps m') = maps_subtract (vm_noaccess (m_vmmaps model)) (leval ρ f) (leval ρ f + nZ)).
      { rewrite Em', fix_rw_vmmaps. unfold mmap_fixed_rw_next. cbn [vm_maps vm_noaccess alloc_top vm_init_sp].
        rewrite (rng_addr segs fs0 ρ _ model H8 e0 He0 f nZ ltac:(lia) Hlo Hhi), (rng_n segs fs0 ρ _ model H8 e0 He0 f nZ ltac:(lia) Hlo Hhi).
        repeat split; reflexivity. }
      destruct Hmods as (M1 & M2 & M3).
      destruct (expose_mem segs fs0 LIM Hlow ρ A ms model HR f nZ e0 Hok He0 HnZ Hb2 Hlo Hhi Hexp m' M1 M2 M3) as (X1 & X2 & X3 & X4 & X5).
      rewrite En, Eaddr.
      apply (R_sys_post_B segs fs0 LIM ρ A B ms model m' _ (aget (a_regs A) reg_a0) _ HR); try reflexivity; try assumption.
      * rewrite <- Eaddr. exact (H4 (Z_to_bv 5 10)).
      * rewrite Em'. apply (MR_fix segs fs0 ρ _ model H8 e0 He0 f nZ ltac:(lia) Hlo Hhi (conj Hal ltac:(unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult)) flagsw).
        -- (* [comment removed for export] *)
           intros Hnrk. rewrite (fix_nores flagsw flags R13 Hfl) in Hnrk. rewrite <- Elz in Hnrk. rewrite Hnrk in Kbig. cbn in Kbig.
           apply Z.leb_le in Kbig. exact Kbig.
        -- (* [comment removed for export] *)
           intros Hfk. rewrite (AxLz.lzfull_na e0 P1) in Hfk. discriminate Hfk.
      * unfold m'. rewrite fix_rw_halted. exact H9.
Qed.

End Main.
