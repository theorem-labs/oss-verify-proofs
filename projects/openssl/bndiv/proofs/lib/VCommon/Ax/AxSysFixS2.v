(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxAcct.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWAcc AxLazy AxLin AxVal AxBytes AxMem AxZZ AxState AxSys AxMeasure AxSysNode AxSysMmap AxGrant AxSysFix AxPostFix.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxFd AxModelRel AxMRFix AxSys2B AxSysFixS AxSysFixS3.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sh_rel (ρ : valuation) (a n : Z) (R R' : region) : Prop :=
  same_fields R R' /\
  ((R' = R /\ (is_shadow R = false \/ (is_shadow R = true /\ rg_cells R = IEmpty) \/ forall z, in_rg ρ R z -> ~ (a <= z < a + n)))
   \/ (is_shadow R = true /\ rg_cells R' = IEmpty /\ forall z, in_rg ρ R z -> a <= z < a + n)).

Lemma same_fields_with_cells (R : region) (t : itrie cell) : same_fields R (with_cells R t).
Proof. unfold same_fields, with_cells. cbn [rg_ts rg_bo rg_n rg_kind rg_d]. repeat split; reflexivity. Qed.

Lemma sh_region_sound (ρ : valuation) (s : store) (f : lin) (n : Z) (R R' : region) :
  sat ρ s -> 0 <= leval ρ f <= 2 ^ 47 -> (is_shadow R = true -> forall z, in_rg ρ R z -> in_ss z) ->
  sh_region s f n R = Some R' -> sh_rel ρ (leval ρ f) n R R'.
Proof.
  intros Hs Ha Hss H. unfold sh_region in H. destruct (is_shadow R) eqn:Esh; cbn [negb] in H.
  2: { injection H as <-. split; [apply same_fields_refl|]. left. split; [reflexivity | left; exact Esh]. }
  destruct (is_empty (rg_cells R)) eqn:Eem.
  { injection H as <-. split; [apply same_fields_refl|]. left. split; [reflexivity|]. right. left. split; [exact Esh|].
    unfold is_empty in Eem. destruct (rg_cells R); [reflexivity | discriminate..]. }
  destruct (lrange s (lsub (wS (rg_bo R), rg_ts R) f)) as [[lo hi]|] eqn:El; [|discriminate H].
  pose proof (lrange_sound ρ s _ Hs _ El) as Hr. cbn [fst snd] in Hr. rewrite leval_lsub in Hr.
  destruct (negb ((- 4611686018427387904 <? lo) &&& (hi <? 4611686018427387904))) eqn:Ew; [discriminate H|].
  apply negb_false_iff in Ew. apply andb_prop in Ew as [W1 W2]. apply Z.ltb_lt in W1. apply Z.ltb_lt in W2.
  (* [comment removed for export] *)
  assert (Hbase : forall z, in_rg ρ R z -> rbase ρ R = leval ρ (wS (rg_bo R), rg_ts R)).
  { intros z Hz. pose proof (Hss eq_refl z Hz) as Hzs. unfold in_rg in Hz. pose proof (to_Z_bounded (rg_n R)) as Hnb.
    pose proof (smod_range ρ (rg_ts R) (rg_bo R)) as Hb. fold (rbase ρ R) in Hb.
    assert (E : rbase ρ R = leval ρ (wS (rg_bo R), rg_ts R) mod FastWord.two64).
    { unfold rbase, smod, leval. cbn [fst snd]. rewrite <- (wS_mod (rg_bo R)), Zplus_mod_idemp_r. f_equal. lia. }
    set (v := leval ρ (wS (rg_bo R), rg_ts R)) in *.
    assert (Hv : - 4611686018427387904 < v < 4611686018427387904 + 2 ^ 47) by lia.
    destruct (Z_lt_le_dec v 0) as [Hneg|Hpos].
    - exfalso. rewrite <- (Z_mod_plus_full v 1), Z.mod_small in E by (unfold FastWord.two64; lia).
      unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi in Hzs. change wB with (2 ^ 63) in Hnb. unfold FastWord.two64 in E. lia.
    - rewrite Z.mod_small in E by (unfold FastWord.two64; lia). exact E. }
  destruct ((hi + to_Z (rg_n R) <=? 0) ||| (n <=? lo)) eqn:Em.
  - injection H as <-. split; [apply same_fields_refl|]. left. split; [reflexivity|]. right. right.
    intros z Hz Hr2. pose proof (Hbase z Hz) as Eb. unfold in_rg in Hz. apply orb_prop in Em as [Em|Em]; apply Z.leb_le in Em; lia.
  - destruct ((0 <=? lo) &&& (hi + to_Z (rg_n R) <=? n)) eqn:Ei; [|discriminate H]. injection H as <-.
    apply andb_prop in Ei as [I1 I2]. apply Z.leb_le in I1. apply Z.leb_le in I2.
    split; [apply same_fields_with_cells|]. right. split; [exact Esh|]. split; [reflexivity|].
    intros z Hz. pose proof (Hbase z Hz) as Eb. unfold in_rg in Hz. lia.
Qed.

Lemma sh_regions_sound (ρ : valuation) (s : store) (f : lin) (n : Z) : forall (A A' : list region),
  sat ρ s -> 0 <= leval ρ f <= 2 ^ 47 -> (forall R, In R A -> is_shadow R = true -> forall z, in_rg ρ R z -> in_ss z) ->
  sh_regions s f n A = Some A' -> Forall2 (sh_rel ρ (leval ρ f) n) A A'.
Proof.
  induction A as [|R A IH]; intros A' Hs Ha Hss H; cbn [sh_regions] in H.
  - injection H as <-. constructor.
  - destruct (sh_region s f n R) as [R'|] eqn:E1; [|discriminate H]. destruct (sh_regions s f n A) as [l|] eqn:E2; [|discriminate H].
    injection H as <-. constructor.
    + exact (sh_region_sound ρ s f n R R' Hs Ha (Hss R (or_introl eq_refl)) E1).
    + exact (IH l Hs Ha (fun X HX => Hss X (or_intror HX)) eq_refl).
Qed.

Lemma F2_same (ρ : valuation) (a n : Z) : forall l l', Forall2 (sh_rel ρ a n) l l' -> Forall2 same_fields l l'.
Proof. intros l l' H. induction H as [|R R' l0 l0' H1 _ IH]; constructor; [exact (proj1 H1) | exact IH]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section PostSh.
Variable segs : list Segment.
Variable ρ : valuation.
Variables A A' : list region.
Variables m m' : word -> option byte.
Variables model model' : Model.
Variables a n : Z.

Hypothesis HF : Forall2 (sh_rel ρ a n) A A'.
Hypothesis Hm_in : forall z, a <= z < a + n -> m' (wz z) = Some (Z_to_bv 8 0).
Hypothesis Hm_out : forall x : word, ~ (a <= bv_unsigned x < a + n) -> m' x = m x.
Hypothesis HRM : RMem segs ρ A m.
Hypothesis Hhs : hs_ok ρ A m.
Hypothesis Hold : hs_old ρ A m.          (* [comment removed for export] *)
Hypothesis Hcomp : comp_inv segs ρ A model.
Hypothesis Hcov : mem_cov segs model m.
Hypothesis Hna : na_ok segs ρ A model m.
(* [comment removed for export] *)
Hypothesis Hpart : (ls_beg <= a /\ a + n <= ls_end) \/ (hs_beg <= a /\ a + n <= hs_hi).
Hypothesis Hmapped : forall z, a <= z < a + n -> m (wz z) <> None.
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis Hled_w : forall q, in_ledger_w segs (m_vmmaps model) q -> in_ledger_w segs (m_vmmaps model') q.
Lemma Hled : forall q, in_ledger segs (m_vmmaps model) q -> in_ledger segs (m_vmmaps model') q.
Proof. exact (in_ledger_of_w segs _ _ Hled_w). Qed.
Hypothesis Hna_new : forall q, a <= q < a + n -> ~ inl (vm_noaccess (m_vmmaps model')) q.
Hypothesis Hna_old : forall q, inl (vm_noaccess (m_vmmaps model')) q -> inl (vm_noaccess (m_vmmaps model)) q.

Lemma sh_F2 : Forall2 same_fields A A'.
Proof. exact (F2_same ρ a n A A' HF). Qed.

Lemma sh_range_ss (z : Z) : a <= z < a + n -> in_ss z.
Proof. intros Hz. unfold in_ss. destruct Hpart as [X|X]; [left | right]; lia. Qed.

Lemma sh_mem (z : Z) : 0 <= z < FastWord.two64 -> (a <= z < a + n /\ m' (wz z) = Some (Z_to_bv 8 0)) \/ (~ (a <= z < a + n) /\ m' (wz z) = m (wz z)).
Proof.
  intros Hz. destruct (Z_le_gt_dec a z) as [L1|L1]; [destruct (Z_lt_le_dec z (a + n)) as [L2|L2]|].
  - left. split; [lia | apply Hm_in; lia].
  - right. split; [lia|]. apply Hm_out. rewrite u_wz by (unfold FastWord.two64 in Hz; lia). lia.
  - right. split; [lia|]. apply Hm_out. rewrite u_wz by (unfold FastWord.two64 in Hz; lia). lia.
Qed.

Lemma sh_RRegion (R R' : region) : In R A -> sh_rel ρ a n R R' -> RRegion segs ρ m R -> region_wf ρ R -> RRegion segs ρ m' R'.
Proof.
  intros HRin [HS Hcase] HR Hwf. pose proof (smod_range ρ (rg_ts R) (rg_bo R)) as Hb. fold (rbase ρ R) in Hb. destruct Hwf as (W1 & W2 & _).
  assert (Hfr : (forall z, in_rg ρ R z -> ~ (a <= z < a + n)) -> RRegion segs ρ m' R).
  { intros Hmiss. apply (RRegion_mframe segs ρ m m' R (conj W1 (conj W2 ltac:(destruct (regions_ok_in ρ A R (proj1 HRM) HRin) as (_ & _ & X); exact X)))); [|exact HR].
    intros z Hz. apply Hm_out. rewrite u_wz by (unfold FastWord.two64 in *; lia). exact (Hmiss z Hz). }
  destruct Hcase as [[-> [Hns|[[Hsh Hce]|Hmiss]]]|(Hsh & Hce & Hinside)].
  - apply Hfr. intros z Hz Hr. destruct Hold as [P1 _]. exact (P1 R HRin Hns z Hz (sh_range_ss z Hr)).
  - assert (Hk : rg_kind R = KShadow) by (unfold is_shadow in Hsh; destruct (rg_kind R); first [reflexivity | discriminate Hsh]).
    rewrite RRegion_ne by (unfold is_entry; rewrite Hk; reflexivity). rewrite RRegion_ne in HR by (unfold is_entry; rewrite Hk; reflexivity).
    intros y Hy. pose proof (to_Z_bounded y) as Hyb. destruct (HR y Hy) as [[b [Hrv Hxb]] Hwv].
    destruct (sh_mem (rbase ρ R + to_Z y) ltac:(unfold FastWord.two64 in *; lia)) as [[_ E]|[_ E]].
    + split; [exists (Z_to_bv 8 0); split; [unfold rv; rewrite E; reflexivity | rewrite (rbyte_zz segs R y (or_intror Hk) Hce); reflexivity]|].
      intros _. unfold wview. rewrite E. discriminate.
    + split; [exists b; split; [unfold rv in *; rewrite E; exact Hrv | exact Hxb] | intros X; unfold wview in *; rewrite E; exact (Hwv X)].
  - exact (Hfr Hmiss).
  - assert (Hk : rg_kind R = KShadow) by (unfold is_shadow in Hsh; destruct (rg_kind R); first [reflexivity | discriminate Hsh]).
    destruct HS as (S1 & S2 & S3 & S4 & S5).
    rewrite RRegion_ne by (unfold is_entry; rewrite S4, Hk; reflexivity). intros y Hy. rewrite S3 in Hy. pose proof (to_Z_bounded y) as Hyb.
    assert (Eb : rbase ρ R' = rbase ρ R) by (unfold rbase; rewrite S1, S2; reflexivity). rewrite Eb.
    assert (E : m' (wz (rbase ρ R + to_Z y)) = Some (Z_to_bv 8 0)) by (apply Hm_in; apply Hinside; unfold in_rg; lia).
    assert (Hk' : rg_kind R' = KShadow) by (rewrite S4; exact Hk).
    split; [exists (Z_to_bv 8 0); split; [unfold rv; rewrite E; reflexivity | rewrite (rbyte_zz segs R' y (or_intror Hk') Hce); reflexivity]|].
    intros _. unfold wview. rewrite E. discriminate.
Qed.

Theorem RMem_sh : RMem segs ρ A' m'.
Proof.
  destruct HRM as [Hok HRR]. split; [exact (regions_ok_same ρ A A' sh_F2 Hok)|].
  assert (X : forall l l', Forall2 (sh_rel ρ a n) l l' -> (forall R, In R l -> In R A) -> Forall (RRegion segs ρ m') l').
  { intros l l' H. induction H as [|R R' l0 l0' H1 _ IH]; intros Hsub; constructor.
    - apply (sh_RRegion R R' (Hsub R (or_introl eq_refl)) H1); [exact (proj1 (Forall_forall _ _) HRR R (Hsub R (or_introl eq_refl)))|].
      exact (regions_ok_in ρ A R Hok (Hsub R (or_introl eq_refl))).
    - apply IH. intros X0 HX0. apply Hsub. right. exact HX0. }
  exact (X A A' HF (fun R H => H)).
Qed.

Theorem hs_ok_sh : hs_ok ρ A' m'.
Proof.
  pose proof (hs_old_geom ρ A A' m sh_F2 Hold) as [P1 [P2 [P3 P4]]]. right. split; [exact P1|]. split; [|split].
  - intros z Hss Hout. assert (Hz : 0 <= z < FastWord.two64) by (unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi, FastWord.two64 in *; lia).
    destruct (sh_mem z Hz) as [[_ E]|[_ E]]; [right; exact E | rewrite E; exact (P2 z Hss Hout)].
  - destruct P3 as [X|X].
    + left. intros z Hz. destruct (sh_mem z ltac:(unfold ls_beg, ls_end, FastWord.two64 in *; lia)) as [[_ E]|[_ E]]; rewrite E; [discriminate | exact (X z Hz)].
    + right. intros z Hz. destruct (sh_mem z ltac:(unfold ls_beg, ls_end, FastWord.two64 in *; lia)) as [[Hr _]|[_ E]]; [|rewrite E; exact (X z Hz)].
      exfalso. apply (Hmapped z Hr). apply X. destruct Hpart as [Y|Y]; [exact Hz | unfold ls_beg, ls_end, hs_beg, hs_hi in *; lia].
  - destruct P4 as [X|X].
    + left. intros z Hz. destruct (sh_mem z ltac:(unfold hs_beg, hs_hi, FastWord.two64 in *; lia)) as [[_ E]|[_ E]]; rewrite E; [discriminate | exact (X z Hz)].
    + right. intros z Hz. destruct (sh_mem z ltac:(unfold hs_beg, hs_hi, FastWord.two64 in *; lia)) as [[Hr _]|[_ E]]; [|rewrite E; exact (X z Hz)].
      exfalso. apply (Hmapped z Hr). apply X. destruct Hpart as [Y|Y]; [unfold ls_beg, ls_end, hs_beg, hs_hi in *; lia | exact Hz].
Qed.

Theorem mem_cov_sh : mem_cov segs model' m'.
Proof.
  intros x Hx. apply Hled_w. pose proof (bv_unsigned_in_range 64 x) as Hxr. change (bv_modulus 64) with FastWord.two64 in Hxr.
  assert (Ex : wz (bv_unsigned x) = x) by (unfold wz; apply Z_to_bv_bv_unsigned).
  destruct (sh_mem (bv_unsigned x) Hxr) as [[Hr _]|[_ E]].
  - apply Hcov. rewrite <- Ex. exact (Hmapped _ Hr).
  - rewrite Ex in E. rewrite E in Hx. exact (Hcov x Hx).
Qed.

Theorem comp_inv_sh : comp_inv segs ρ A' model'.
Proof.
  intros R' HR' Hs z Hz. destruct (comp_inv_geom segs ρ A A' model sh_F2 Hcomp R' HR' Hs z Hz) as [H1 H2].
  split; [exact H1|]. intros q Hq. exact (Hled q (H2 q Hq)).
Qed.

Theorem na_ok_sh : na_ok segs ρ A' model' m'.
Proof.
  destruct (na_ok_geom segs ρ A A' model m sh_F2 Hna) as [N1 [N2 N3]]. split; [|split].
  - intros x Hx Hi. pose proof (bv_unsigned_in_range 64 x) as Hxr. change (bv_modulus 64) with FastWord.two64 in Hxr.
    assert (Ex : wz (bv_unsigned x) = x) by (unfold wz; apply Z_to_bv_bv_unsigned).
    destruct (sh_mem (bv_unsigned x) Hxr) as [[Hr _]|[_ E]]; [exact (Hna_new _ Hr Hi)|].
    rewrite Ex in E. rewrite E in Hx. exact (N1 x Hx (Hna_old _ Hi)).
  - intros z Hz Hi. exact (N2 z Hz (Hna_old _ Hi)).
  - intros R' HR' Hs z Hz q Hq Hi. exact (N3 R' HR' Hs z Hz q Hq (Hna_old _ Hi)).
Qed.

End PostSh.

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

Lemma add_exp_na_false (am : amodel) (e0 : aent) (f : lin) (n : Z) : ae_na e0 = false -> add_exp am e0 f n = am.
Proof. intros H. unfold add_exp. rewrite H. destruct am; reflexivity. Qed.

Theorem sys_fix_sh_sound (A : AST) (l : list AST) :
  pc_ok (npc A) = true -> xlit (aget (a_regs A) 17%uint63) = Some 222 -> sys_fix_sh LIM A = Some l ->
  (forall B, In B l -> forall ρ c, RR ρ B c -> forall o, out_val ρ B o -> realizes_cfg segs cfg c (KT ρ o)) ->
  forall ρ c, RR ρ A c -> (exists w, fetch_word segs (ms_pc_val (cfg_ms c)) = Some w /\ is_ecall w = true) ->
  forall o, out_val ρ A o -> realizes_cfg segs cfg c (KT ρ o).
Proof.
  intros Hpc H17 Hsys HS ρ [ms model] HR [w [Hf He]] o Ho. cbn [cfg_ms] in Hf.
  unfold sys_fix_sh in Hsys.
  destruct (fix_shape A 3) as [[nZ lz]|] eqn:Esh; [|discriminate Hsys].
  destruct (xform (a_facts A) (aget (a_regs A) 10%uint63)) as [f|] eqn:Ef; [|discriminate Hsys].
  destruct (find_ent (a_facts A) f nZ (am_maps (a_model A))) as [e0|] eqn:Ee; [|discriminate Hsys].
  match type of Hsys with (if ?c then _ else _) = _ => destruct c eqn:Ec; [|discriminate Hsys] end.
  destruct (sh_regions (a_facts A) f nZ (a_mem A)) as [mem1|] eqn:Erg; [|discriminate Hsys].
  injection Hsys as <-.
  apply andb_prop in Ec as [Ec Kfull]. apply andb_prop in Ec as [Ec Kbig].
  apply andb_prop in Ec as [Ec Hbud]. apply andb_prop in Ec as [Ec Q5]. apply andb_prop in Ec as [Ec Q4].
  apply andb_prop in Ec as [Ec Q3]. apply andb_prop in Ec as [Q1 Q2]. apply negb_true_iff in Q1. apply Z.leb_le in Hbud.
  destruct (fix_shape_spec A 3 nZ lz Esh) as (len & flags & L11 & L12 & L13 & L15 & Hlen & EnZ & Hfl & Elz).
  subst nZ. set (nZ := page_round_up_Z len) in *.
  pose proof HR as [H1 H2 H3 H4 H5 H6 H7 H8 H9 [H10 H10'] H11 H12 H13 H14 H15]. cbn [cfg_ms cfg_model] in *.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 17) 17%uint63 222 H4 eq_refl H17) as R17.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 11) 11%uint63 len H4 eq_refl L11) as R11.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 12) 12%uint63 3 H4 eq_refl L12) as R12.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 13) 13%uint63 flags H4 eq_refl L13) as R13.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 15) 15%uint63 0 H4 eq_refl L15) as R15.
  pose proof (xform_sound ρ _ _ (rg ms (Z_to_bv 5 10)) f H11 (H4 (Z_to_bv 5 10)) Ef) as R10.
  destruct (find_ent_spec _ f nZ _ e0 Ee) as [He0 Hhas]. destruct (ent_has_sound ρ _ f nZ e0 H11 Hhas) as [Hlo Hhi].
  destruct (page_round_up_bounds len ltac:(flia)) as [Hb1 Hb2]. fold nZ in Hb1, Hb2.
  pose proof (lin_al_sound ρ 4096 f ltac:(flia) Q3) as Hal.
  assert (HnZ0 : 0 < nZ) by flia.
  (* [comment removed for export] *)
  assert (Hpart : (ls_beg <= leval ρ f /\ leval ρ f + nZ <= ls_end) \/ (hs_beg <= leval ρ f /\ leval ρ f + nZ <= hs_hi)).
  { unfold in_shadow in Q4. destruct (lrange (a_facts A) f) as [[lo hi]|] eqn:El; [|discriminate Q4].
    pose proof (lrange_sound ρ _ f H11 _ El) as Hr. cbn [fst snd] in Hr.
    apply orb_prop in Q4 as [Q|Q]; apply andb_prop in Q as [Qa Qb]; apply Z.leb_le in Qa; apply Z.leb_le in Qb; [left | right]; flia. }
  set (a := leval ρ f) in *.
  assert (Ha47 : 0 <= a <= 2 ^ 47) by (unfold ls_beg, ls_end, hs_beg, hs_hi in Hpart; flia).
  (* [comment removed for export] *)
  pose proof (gate_of_MR segs fs0 ρ _ model H8 e0 He0 f len Hlen Hlo Hhi Hal (rg ms (Z_to_bv 5 10)) (rg ms (Z_to_bv 5 11)) R10 R11) as G.
  pose proof (fix_rw_shape_lit (rg ms (Z_to_bv 5 12)) (rg ms (Z_to_bv 5 13)) (rg ms (Z_to_bv 5 15)) R12 ltac:(rewrite R13; exact Hfl) R15) as S.
  pose proof (gate_addr ρ f (rg ms (Z_to_bv 5 10)) R10) as Eaddr. fold a in Eaddr.
  pose proof (gate_fix_n len (rg ms (Z_to_bv 5 11)) R11) as En. fold nZ in En.
  pose proof (rng_addr segs fs0 ρ _ model H8 e0 He0 f nZ HnZ0 Hlo Hhi) as Wa. fold a in Wa.
  pose proof (rng_n segs fs0 ρ _ model H8 e0 He0 f nZ HnZ0 Hlo Hhi) as Wn.
  set (addr := rg ms (Z_to_bv 5 10)) in *. set (flagsw := rg ms (Z_to_bv 5 13)) in *.
  set (m' := fix_rw_model flagsw (Z_to_bv 64 a) (Z_to_bv 64 nZ) model).
  assert (Hused : vm_backing_used m' <= a_budget A + (if lz then 0 else nZ)).
  { rewrite Elz. exact (fix_rw_budget segs fs0 KT ρ _ model e0 f nZ _ flagsw flags H8 He0 HnZ0 Hb2 Hal Hlo Hhi R13 Hfl H10). }
  assert (Hlim : vm_limit (m_vmmaps m') = LIM) by (unfold m'; rewrite fix_rw_vmmaps; exact H10').
  assert (Hbok : mmap_fixed_rw_budget_ok flagsw model addr (fix_n (rg ms (Z_to_bv 5 11))) = true).
  { unfold mmap_fixed_rw_budget_ok, vm_backing_within_limit. fold (fix_rw_model flagsw addr (fix_n (rg ms (Z_to_bv 5 11))) model).
    rewrite En, Eaddr. fold m'. apply Z.leb_le. rewrite Hlim. flia. }
  set (mem' := apply_zeros (ms_mem ms) [(Z_to_bv 64 a, Z_to_bv 64 nZ)]).
  apply (rzc_latch segs cfg ms model w (KT ρ o) H9 H3 Hf He).
  apply (rzc_sys_silent segs cfg (latch ms) model (rg ms (Z_to_bv 5 17)) (KT ρ o) H9 eq_refl).
  - rewrite (check_syscall_222 segs (latch ms) _ _ model R17).
    exact (chk_fix_rw_modeled model addr (rg ms (Z_to_bv 5 11)) (rg ms (Z_to_bv 5 12)) flagsw (rg ms (Z_to_bv 5 14)) (rg ms (Z_to_bv 5 15)) S G _).
  - intros eff m1 evs Hc. rewrite (check_syscall_222 segs (latch ms) _ _ model R17) in Hc.
    destruct (chk_fix_rw_halted model addr _ _ flagsw _ _ eff m1 evs S G Hc) as [E1 E2]. split; [exact E1 | rewrite E2; exact H9].
  - exists (mkEffect addr [] [(addr, fix_n (rg ms (Z_to_bv 5 11)))]), (fix_rw_model flagsw addr (fix_n (rg ms (Z_to_bv 5 11))) model). split.
    + rewrite (check_syscall_222 segs (latch ms) _ _ model R17).
      exact (chk_fix_rw_grant model addr (rg ms (Z_to_bv 5 11)) (rg ms (Z_to_bv 5 12)) flagsw (rg ms (Z_to_bv 5 14)) (rg ms (Z_to_bv 5 15)) S G Hbok).
    + rewrite (refusal_b_222 segs (latch ms) _ model _ R17). exact (fix_addr_not_errno model addr _ G).
  - intros eff m1 Hc Hnr. rewrite (check_syscall_222 segs (latch ms) _ _ model R17) in Hc.
    destruct (chk_fix_rw model addr _ _ flagsw _ _ S G eff m1 [] Hc) as [Hr|(-> & -> & _ & _)].
    + exfalso. specialize (Hnr (family_off_alloc segs cfg (latch ms) _ Hcfg2 ltac:(rewrite R17; cbn; tauto) ltac:(rewrite R17; discriminate))).
      rewrite (refusal_b_222 segs (latch ms) _ model _ R17) in Hnr.
      change (ret_in_errnos [ENOMEM] (eff_ret eff)) with (errno_ret_in mmap_errnos (eff_ret eff)) in Hnr. congruence.
    + rewrite En, Eaddr. fold m'. exists m'. split; [exact (materialize_nil m')|]. rewrite adv_zeros. fold mem'.
      set (B := with_model A (npc A) (aset (a_regs A) reg_a0 (aget (a_regs A) reg_a0)) mem1 (a_facts A) (a_model A)
                  (a_budget A + (if lz then 0 else nZ))).
      apply (HS B (or_introl eq_refl) ρ); [|exact Ho].
      assert (Hmods : vm_maps (m_vmmaps m') = vm_maps (m_vmmaps model) /\ alloc_top (m_vmmaps m') = alloc_top (m_vmmaps model)
                      /\ vm_noaccess (m_vmmaps m') = maps_subtract (vm_noaccess (m_vmmaps model)) a (a + nZ)).
      { unfold m'. rewrite fix_rw_vmmaps. unfold mmap_fixed_rw_next. cbn [vm_maps vm_noaccess alloc_top vm_init_sp]. rewrite Wa, Wn.
        repeat split; reflexivity. }
      destruct Hmods as (M1 & M2 & M3).
      destruct (expose_ledger segs fs0 ρ _ model m' e0 a nZ H8 He0 Hlo Hhi M1 M2 M3) as (_ & L2 & L3 & L4).
      assert (HF : Forall2 (sh_rel ρ a nZ) (a_mem A) mem1).
      { apply (sh_regions_sound ρ (a_facts A) f nZ (a_mem A) mem1 H11 Ha47); [|exact Erg].
        intros X HX Hs z Hz. exact (proj1 (H14 X HX Hs z Hz)). }
      assert (Hin : forall z, a <= z < a + nZ -> mem' (wz z) = Some (Z_to_bv 8 0)).
      { intros z Hz. unfold mem'. apply zeros_in; [rewrite Wa, Wn; exact Hz | unfold FastWord.two64; flia]. }
      assert (Hout : forall x : word, ~ (a <= bv_unsigned x < a + nZ) -> mem' x = ms_mem ms x).
      { intros x Hx. unfold mem'. apply zeros_out. rewrite Wa, Wn. exact Hx. }
      assert (Hold : hs_old ρ (a_mem A) (ms_mem ms)).
      { unfold ss_wit in Q5. apply andb_prop in Q5 as [W1 _].
        destruct (has_wit_sound ρ _ ls_beg ls_end _ H11 ltac:(unfold ls_beg; lia) ltac:(unfold ls_end, FastWord.two64; lia) W1) as [W [w0 (HIn & Hsh & _)]].
        exact (hs_old_of_sh ρ _ _ W HIn Hsh H12). }
      assert (Hmapped : forall z, a <= z < a + nZ -> ms_mem ms (wz z) <> None).
      { intros z Hz. unfold ss_wit in Q5. apply andb_prop in Q5 as [W1 W2]. destruct Hpart as [Hp|Hp].
        - destruct (has_wit_sound ρ _ ls_beg ls_end _ H11 ltac:(unfold ls_beg; lia) ltac:(unfold ls_end, FastWord.two64; lia) W1) as [W [w0 (HIn & Hsh & Hw & Hrw)]].
          apply (ss_mapped segs Hlow ρ _ _ W w0 z H7 H12 HIn Hsh Hw). left. split; [exact Hrw | flia].
        - destruct (has_wit_sound ρ _ hs_beg hs_hi _ H11 ltac:(unfold hs_beg; lia) ltac:(unfold hs_hi, FastWord.two64; lia) W2) as [W [w0 (HIn & Hsh & Hw & Hrw)]].
          apply (ss_mapped segs Hlow ρ _ _ W w0 z H7 H12 HIn Hsh Hw). right. split; [exact Hrw | flia]. }
      apply (R_sys_post_B segs fs0 LIM ρ A B ms model m' _ (aget (a_regs A) reg_a0) _ HR); try reflexivity; try assumption.
      * rewrite <- Eaddr. exact (H4 (Z_to_bv 5 10)).
      * assert (Enr : mmap_noreserve_b flagsw = lz) by (rewrite Elz; exact (fix_nores flagsw flags R13 Hfl)).
        assert (K2a : mmap_noreserve_b flagsw = true -> AxLz.BIGMIN <= ae_size e0).
        { intros Hnrk. rewrite Enr in Hnrk. rewrite Hnrk in Kbig. cbn in Kbig. apply Z.leb_le in Kbig. exact Kbig. }
        assert (K2b : AxLz.lzfull e0 = true -> mmap_noreserve_b flagsw = true /\ leval ρ f mod 4096 = 0 /\ nZ mod 4096 = 0).
        { intros Hfk. rewrite Hfk in Kfull. cbn in Kfull. rewrite Enr. split; [exact Kfull|]. split; [exact Hal|].
          unfold nZ, page_round_up_Z, page_size. apply Z_mod_mult. }
        pose proof (MR_fix segs fs0 ρ _ model H8 e0 He0 f nZ HnZ0 Hlo Hhi (conj Hal ltac:(unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult)) flagsw K2a K2b) as X. rewrite (add_exp_na_false _ e0 f nZ Q1) in X. exact X.
      * unfold m'. rewrite fix_rw_halted. exact H9.
      * eapply RMem_sh with (m := ms_mem ms) (A := a_mem A) (a := a) (n := nZ); eassumption.
      * eapply hs_ok_sh with (m := ms_mem ms) (A := a_mem A) (a := a) (n := nZ); eassumption.
      * eapply mem_cov_sh with (m := ms_mem ms) (model := model) (a := a) (n := nZ); eassumption.
      * eapply comp_inv_sh with (A := a_mem A) (model := model) (a := a) (n := nZ); eassumption.
      * eapply na_ok_sh with (A := a_mem A) (m := ms_mem ms) (model := model) (a := a) (n := nZ); eassumption.
Qed.

End Main.
