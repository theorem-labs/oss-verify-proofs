(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxMem AxMemC AxState AxStep AxSys AxJoin AxJoinSound AxRun.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.

Lemma find_floor_fact_in (fs : list fact) (ts : terms) (k2 : Z) (v : int) (F : lin) :
  find_floor_fact fs ts k2 = Some (v, F) -> In (Fact F 0 (k2 - 1) false) fs.
Proof.
  induction fs as [|[F' lo hi ho] r IH]; cbn [find_floor_fact]; [discriminate|].
  destruct (negb ho &&& (lo =? 0) &&& (hi =? k2 - 1)) eqn:E; [|intros H; right; exact (IH H)].
  destruct (List.find _ (snd F')) as [p|]; [|intros H; right; exact (IH H)].
  intros H. injection H as _ <-. left.
  apply land_true in E as [E E3]. apply land_true in E as [E1 E2].
  apply negb_true_iff in E1. apply Z.eqb_eq in E2, E3. subst. reflexivity.
Qed.

Lemma lin_gcd_divides (ρ : valuation) (F : lin) : (lin_gcd F | leval ρ F).
Proof.
  destruct F as [c ts]. unfold lin_gcd, leval. cbn [fst snd].
  induction ts as [|[x a] r IH]; cbn [fold_right teval snd fst].
  - rewrite Z.add_0_r. apply Z.divide_refl.
  - set (g := fold_right (fun (p : int * Z) g => Z.gcd (snd p) g) c r) in *.
    replace (c + (a * ρ x + teval ρ r)) with (a * ρ x + (c + teval ρ r)) by ring.
    apply Z.divide_add_r.
    + apply Z.divide_mul_l. apply Z.gcd_divide_l.
    + apply (Z.divide_trans _ g); [apply Z.gcd_divide_r | exact IH].
Qed.

Lemma align_cases_cover (k2 g x : Z) : 0 < g -> (g | x) -> 0 <= x <= k2 - 1 -> In x (align_cases k2 g).
Proof.
  intros Hg [j ->] Hx. unfold align_cases. apply in_map_iff.
  assert (Hj0 : 0 <= j) by nia.
  assert (Hj1 : j <= (k2 - 1) / g) by (apply Z.div_le_lower_bound; [exact Hg | lia]).
  exists (Z.to_nat j). split; [rewrite Z2Nat.id by exact Hj0; ring|].
  apply in_seq. split; [lia|]. cbn [plus]. lia.
Qed.

Lemma elim_xv_sound (ρ : valuation) (v : int) (k2 : Z) (F : lin) (q : Z) (x : xv) (w : bv 64) :
  leval ρ F = q -> xv_val ρ x w -> xv_val ρ (elim_xv v k2 F q x) w.
Proof.
  intros HF Hx. destruct x as [l|ts o| | | |]; cbn [elim_xv]; try exact Hx.
  destruct ((acoef v ts =? 0) ||| negb (acoef v ts mod k2 =? 0)); [exact Hx|].
  set (m := acoef v ts / k2). apply mk_xs_sound. cbn [xv_val] in Hx. rewrite Hx. unfold smod.
  rewrite teval_tadd, teval_tscale, wZ_add, wZ_wofZ.
  rewrite Zplus_mod_idemp_r, Z.add_assoc, Zplus_mod_idemp_r. f_equal.
  unfold leval in HF. replace (fst F - q) with (- teval ρ (snd F)) by lia. ring.
Qed.

Lemma aget_imap_elim (v : int) (k2 : Z) (F : lin) (q : Z) (m : aregs) (r : int) :
  aget (imap (elim_xv v k2 F q) m) r = elim_xv v k2 F q (aget m r).
Proof.
  unfold aget. destruct (r =? 0)%uint63; [reflexivity|]. rewrite iget_imap.
  destruct (iget 5 m r); reflexivity.
Qed.

Section Align.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable MR : valuation -> amodel -> Model -> Prop.
Variable KT : valuation -> list byte -> TSet.

Notation RR ρ := (R segs amodel (MR ρ) LIM ρ).
Notation Snd := (Sound segs cfg LIM MR KT).

Lemma R_align_child (ρ : valuation) (A : astate amodel) (c : config) (v : int) (k2 : Z) (F : lin) (q : Z) :
  RR ρ A c -> leval ρ F = q -> RR ρ (align_child A v k2 F q) c.
Proof.
  intros [Hpc Hal Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hna] HF.
  assert (Hs' : sat ρ (sadd (a_facts A) F q q)) by (apply sat_sadd; [exact Hsat | lia]).
  constructor; cbn [align_child a_pc a_regs a_resv a_mem a_facts a_model a_budget]; try assumption.
  apply RRegs_renorm; [exact Hs'|]. intros r. rewrite aget_imap_elim. exact (elim_xv_sound ρ v k2 F q _ _ HF (Hregs r)).
Qed.

Theorem align_sound (A : astate amodel) (r : int) (k : Z) (l : list (astate amodel)) :
  align_children A r k = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hal HS ρ c HR o Ho. pose proof (r_sat _ _ _ _ _ _ _ HR) as Hsat.
  unfold align_children in Hal.
  destruct (aget (a_regs A) r) as [|ts o'| | | |]; try discriminate Hal.
  destruct (find_floor_fact (st_facts (a_facts A)) ts (2 ^ k)) as [[v F]|] eqn:Eff; [|discriminate Hal].
  destruct ((0 <? lin_gcd F) &&& ((2 ^ k - 1) / lin_gcd F <? 8)) eqn:Eg; [|discriminate Hal].
  assert (El : l = map (align_child A v (2 ^ k) F)
                       (List.filter (fun q => feasible (sadd (a_facts A) F q q) F) (align_cases (2 ^ k) (lin_gcd F))))
    by (injection Hal as <-; reflexivity).
  clear Hal. subst l. apply land_true in Eg as [Eg _]. apply Z.ltb_lt in Eg.
  pose proof (find_floor_fact_in _ _ _ _ _ Eff) as Hin.
  destruct Hsat as [_ Hfs]. rewrite Forall_forall in Hfs. pose proof (Hfs _ Hin) as Hfact.
  unfold fact_sat in Hfact. cbn [fc_hole fc_lo fc_hi fc_f] in Hfact.
  set (q := leval ρ F) in *.
  assert (Hq : In q (align_cases (2 ^ k) (lin_gcd F))) by (apply align_cases_cover; [exact Eg | apply lin_gcd_divides | exact Hfact]).
  assert (Hs' : sat ρ (sadd (a_facts A) F q q)) by (apply sat_sadd; [exact (r_sat _ _ _ _ _ _ _ HR) | unfold q; lia]).
  apply (HS (align_child A v (2 ^ k) F q)).
  - apply in_map_iff. exists q. split; [reflexivity|]. apply filter_In. split; [exact Hq | exact (feasible_sat ρ _ F Hs')].
  - apply R_align_child; [exact HR | reflexivity].
  - exact Ho.
Qed.

End Align.
