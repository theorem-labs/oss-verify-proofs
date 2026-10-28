(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Uint63 Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AS Require Import AsanAcct BackingAlgebra AsanCeil.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Mem. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require RzCPS NodesA_madv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_state RT_main_shape RT_allowmain RT_rep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.VCommon Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie AxLazy AxLin AxVal AxMem AxZZ AxState AxSys AxAcct AxMeasure AxLz AxEntryRel AxFd AxModelRel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.AxA Require Import AxExport AxExportM AxExportH AxExportV FinMain1 FinMain2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtAxA Require Import AxExportS AxExportF AxExportL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Lemma A_wf_allow_main : forall L, layout_ok L -> A_wf (allow_main L).
Proof.
  intros L HL. unfold layout_ok in HL.
  destruct HL as ((Hlo & Hhi) & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & _ & _ & _ & (F1 & F2 & F3 & F4 & F5) & _ & (S1 & S2 & S3 & S4 & S5) & _).
  unfold A_wf, allow_main, pg_up, pg_dn, shad, SHB, l_ACEIL, STACK_WIN, SEGTOP_A, page_size, sp_window_lo, sp_window_hi in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  repeat constructor; cbn [fst snd]; lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma allow_main_pos : forall L, layout_ok L -> Forall (fun iv : Z * Z => 0 < snd iv) (allow_main L).
Proof.
  intros L HL. unfold layout_ok in HL.
  destruct HL as ((Hlo & Hhi) & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & HSB & _ & _ & _ & _ & (F1 & F2 & F3 & F4 & F5) & _ & (S1 & S2 & S3 & S4 & S5) & _).
  unfold allow_main, pg_up, pg_dn, shad, SHB, l_ACEIL, STACK_WIN, SEGTOP_A, sp_window_lo, sp_window_hi in *.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma covered_inl (l : list (word * word)) (z : Z) : covered l z = true <-> inl l z.
Proof.
  unfold covered, inl, in_iv, in_rng, BackingAlgebra.B, BackingAlgebra.S, bas, bsz. split.
  - intros H. apply existsb_exists in H as [p [Hp Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    exists p. split; [exact Hp | lia].
  - intros [p [Hp Hz]]. apply existsb_exists. exists p. split; [exact Hp|]. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma filter_vpos_id (l : list (word * word)) : Forall (fun e : word * word => 0 < bv_unsigned (snd e)) l -> List.filter vpos l = l.
Proof.
  induction 1 as [|e r He _ IH]; [reflexivity|]. cbn [List.filter]. unfold vpos at 1. rewrite (proj2 (Z.ltb_lt _ _) He), IH. reflexivity.
Qed.

Section Top.
Hypothesis Hlow : segs_low ctasegs.
Variable fs0 : Fs.Fs.
Variable ρ : valuation.
Variable B : AST.
Variable ms : machine_state.
Variable model : Model.
Hypothesis HR : R ctasegs amodel (MR ctasegs fs0 ρ) target_alloc_limit ρ B (mkCfg ms model).
Variable F : bforms.
Variable main_pc : Z.

Local Notation W := (win_of B).
Local Notation L := (Lm ρ W JUNK F (vm_maps (m_vmmaps model))).
Local Notation AFl := (AFull ρ W JUNK F (vm_maps (m_vmmaps model))).
Local Notation mMl := (mM ρ ms model W JUNK F (vm_maps (m_vmmaps model))).

Hypothesis Hfm : fin_model main_pc SEGTOP_A B = true.
Hypothesis Hfw : fin_win2 target_alloc_limit B = true.
Hypothesis Hlay : layout_ok L.
Hypothesis Hat : leval ρ (am_atop (a_model B)) = l_ACEIL L.
Hypothesis Hwb : JUNK + wins_bytes W <= 2 ^ 36.     (* [comment removed for export] *)

Let HM : MR ctasegs fs0 ρ (a_model B) model := r_model _ _ _ _ _ _ _ HR.

Lemma AFull_cons : AFl = (- JUNK, 0) :: (map (den_w ρ) W ++ allow_main L).
Proof. reflexivity. Qed.

Lemma fin_parts : forallb w_ok W = true /\ hz_ok B W = true /\ a_budget B + (JUNK + wins_bytes W) <= target_alloc_limit
  /\ forallb (w_pos B) W = true /\ big_top_ok B SEGTOP_A = true /\ a_budget B <= JUNK /\ am_shadow (a_model B) = true.
Proof.
  unfold fin_win2 in Hfw. apply andb_prop in Hfw as [Hw Hpos]. unfold fin_win in Hw. cbv zeta in Hw.
  apply andb_prop in Hw as [Hw Hbud]. apply andb_prop in Hw as [Hwok Hhz]. apply Z.leb_le in Hbud.
  unfold fin_model in Hfm. apply andb_prop in Hfm as [Hf Hbj]. apply andb_prop in Hf as [Hf Hbt]. apply Z.leb_le in Hbj.
  apply andb_prop in Hf as [Hf _]. apply andb_prop in Hf as [Hf _]. apply andb_prop in Hf as [_ Hsh].
  repeat split; assumption.
Qed.

Theorem ex_macct_full : RzCPS.macct SEGTOP_A AFl model.
Proof.
  destruct fin_parts as (Hwok & Hhz & Hbud & Hpos & Hbt & Hbj & _).
  unfold RzCPS.macct. split.
  - unfold AFull, AF. apply RzCPS.A_wf_app; [exact (A_wf_A' ρ W JUNK ltac:(unfold JUNK; lia) eq_refl Hwok) | exact (A_wf_allow_main L Hlay)].
  - split; [|split; [exact (r_halted _ _ _ _ _ _ _ HR) | split; [exact (ex_ranges_from ctasegs fs0 _ ρ B ms model HR SEGTOP_A Hbt) | unfold SEGTOP_A; lia]]].
    rewrite AFull_cons.
    apply (ex_minv ctasegs fs0 _ ρ B ms model HR JUNK (map (den_w ρ) W ++ allow_main L)); [unfold JUNK; lia | reflexivity | | exact Hbj |].
    + apply Forall_app. split; [|exact (allow_main_pos L Hlay)].
      apply Forall_forall. intros iv Hiv. apply in_map_iff in Hiv as [w [<- Hw']]. rewrite forallb_forall in Hpos. specialize (Hpos w Hw').
      unfold w_pos in Hpos. destruct (lrange (a_facts B) (fst w)) as [[lo hi]|] eqn:El; [|discriminate Hpos]. apply Z.leb_le in Hpos.
      pose proof (lrange_sound ρ _ _ (r_sat _ _ _ _ _ _ _ HR) _ El) as Xr. cbn [fst snd] in Xr. unfold den_w. cbn [snd].
      destruct (pup_spec (leval ρ (fst w) + snd w)) as (P1 & _ & _). lia.
    + rewrite RzCPS.A_bytes_app. pose proof (hull_bytes ρ W Hwok). pose proof (A_bytes_allow_main L Hlay).
      unfold JUNK, target_alloc_limit in *. change (2 ^ 36) with 68719476736 in Hwb. change (2 ^ 35) with 34359738368 in *. lia.
Qed.


Lemma hz_parts : (forall C, In C (a_mem B) -> 0 < to_Z (rg_n C)) /\ has_wit (a_facts B) ls_beg ls_end (a_mem B) = true
  /\ has_wit (a_facts B) hs_beg hs_hi (a_mem B) = true.
Proof.
  destruct fin_parts as (_ & Hhz & _). unfold hz_ok in Hhz.
  apply land_true in Hhz as [H HwH]. apply land_true in H as [H HwL]. apply land_true in H as [H _]. apply land_true in H as [_ Hpos].
  split; [|split; assumption]. intros C HC. rewrite forallb_forall in Hpos. specialize (Hpos C HC). cbv beta in Hpos. apply Z.ltb_lt in Hpos. exact Hpos.
Qed.

Theorem ex_HZ_full : RzCPS.HZ AFl (mkCfg ms model).
Proof.
  destruct fin_parts as (_ & Hhz & _). intros a Hh Hna.
  apply (ex_HZ ctasegs Hlow fs0 _ ρ B ms model HR W JUNK Hhz a); [|exact Hna].
  exact (RzCPS.mkH_mono _ (A' ρ W JUNK) AFl a (allowed_l ρ W JUNK (allow_main L)) Hh).
Qed.

(* [comment removed for export] *)
Lemma sp0_bounds : 0x7fff80000000 <= l_sp0 L <= 2 ^ 47 /\ l_ACEIL L = l_sp0 L - 8388608.
Proof. destruct Hlay as ((H1 & H2) & _). unfold sp_window_lo, sp_window_hi in *. split; [lia | reflexivity]. Qed.

Hypothesis Hstk : stksh_ok B = true.

Theorem ex_stack_shadow :
  bytes_at ctasegs mMl (shad (l_ACEIL L)) (repeat (Z_to_bv 8 0) (Z.to_nat ((2 ^ 47 - l_ACEIL L) / 8))).
Proof.
  destruct sp0_bounds as [(S1 & S2) EA]. destruct hz_parts as (Hpos & HwL & HwH).
  assert (Hn : 0 <= (2 ^ 47 - l_ACEIL L) / 8) by (apply Z.div_pos; lia).
  assert (Hsum : l_ACEIL L / 8 + (2 ^ 47 - l_ACEIL L) / 8 <= 2 ^ 44).
  { pose proof (Z.div_mod (l_ACEIL L) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (l_ACEIL L) 8 ltac:(lia)).
    pose proof (Z.div_mod (2 ^ 47 - l_ACEIL L) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (2 ^ 47 - l_ACEIL L) 8 ltac:(lia)).
    change (2 ^ 44) with 17592186044416. change (2 ^ 47) with 140737488355328 in *. lia. }
  assert (Hd0 : 0 <= l_ACEIL L / 8) by (apply Z.div_pos; lia).
  unfold bytes_at. rewrite repeat_length, Z2Nat.id by lia. unfold shad, SHB in *.
  split; [lia|]. split; [change (2 ^ 44) with 17592186044416 in Hsum; lia|]. intros i Hi.
  set (z := l_ACEIL L / 8 + 2147450880 + Z.of_nat i).
  assert (Hz : alloc_top (m_vmmaps model) / 8 + sh_off <= z < hs_hi).
  { rewrite (mr_atop ctasegs fs0 ρ _ model HM), Hat. unfold z, sh_off, hs_hi. change (2 ^ 44) with 17592186044416 in Hsum. lia. }
  pose proof (stack_shadow_zero ctasegs Hlow fs0 _ ρ B ms model HR Hpos HwL HwH Hstk z Hz) as Hm0.
  assert (Hv : RzCPS.HID AFl model (wz z) = false).
  { apply (vis_X ρ model W JUNK (allow_main L) (pg_dn (shad (l_ACEIL L))) (pg_up (shad (2 ^ 47))) z
             (in_allow_main ρ W JUNK F (vm_maps (m_vmmaps model)) 3 _ eq_refl) (proj2 (pg_dn_spec _)) (proj2 (pg_up_spec _))).
    - destruct (pg_dn_spec (shad (l_ACEIL L))) as [D1 _]. destruct (pg_up_spec (shad (2 ^ 47))) as [U1 _]. unfold shad, SHB in *.
      change (2 ^ 47 / 8) with 17592186044416 in *. change (2 ^ 44) with 17592186044416 in Hsum. unfold z. lia.
    - unfold z. change (2 ^ 44) with 17592186044416 in Hsum. change (2 ^ 47) with 140737488355328. lia. }
  change (wa (l_ACEIL L / 8 + 2147450880 + Z.of_nat i)) with (wz z).
  unfold mrd, mM, AxExport.mX, mrestrict. fold AFl. rewrite Hv, Hm0. symmetry. apply nth_error_repeat. lia.
Qed.

(* [comment removed for export] *)
Theorem ex_artm_sys (Σ : rtsA) : lay Σ = L -> artm_sys Σ model.
Proof.
  intros EL. destruct fin_parts as (_ & _ & _ & _ & _ & _ & Hsh). destruct sp0_bounds as [(S1 & S2) EA].
  destruct (ex_nowrap ctasegs fs0 _ ρ B ms model HR) as (N1 & N2 & N3).
  assert (Esp : bv_unsigned (vm_init_sp (m_vmmaps model)) = l_sp0 L).
  { pose proof (mr_atop ctasegs fs0 ρ _ model HM) as E. rewrite Hat in E. unfold alloc_top, stack_max_size in E. lia. }
  unfold artm_sys. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - unfold model_ivs_wf, ivs_wf, iv_wf, BackingAlgebra.B, BackingAlgebra.S. split; [exact N1|]. split; [exact N2|]. split; [exact N3|].
    unfold init_sp_ok, sp_window_lo. rewrite Esp. lia.
  - exact (ex_lazy_in_maps ctasegs fs0 _ ρ B ms model HR).
  - exact (ex_maps_apart ctasegs fs0 _ ρ B ms model HR).
  - rewrite EL. exact Esp.
  - intros z Hz. rewrite EL. change (l_maps0 L) with (vm_maps (m_vmmaps model)).
    apply covered_inl. apply (ex_confined ctasegs fs0 _ ρ B ms model HR z). apply covered_inl. exact Hz.
  - intros a Ha. destruct (ex_shadow_lazy ctasegs fs0 _ ρ B ms model HR Hsh a) as [P1 P2].
    + unfold shreg, SHB, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in Ha. lia.
    + split; [exact P1|]. destruct (covered (vm_noaccess (m_vmmaps model)) (bv_unsigned a)) eqn:Ec; [|reflexivity].
      exfalso. apply P2. apply covered_inl. exact Ec.
  - unfold maps_zbound. rewrite (filter_vpos_id _ (ex_maps_pos ctasegs fs0 _ ρ B ms model HR)). lia.
  - exact (ex_noaccess_pos ctasegs fs0 _ ρ B ms model HR).
Qed.

End Top.
