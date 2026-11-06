(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.FCutCert Require Import CutOpsF CutOps.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CXD.
Inductive xop : Type := OBase (op : CX.xop) | OLem (Ps : list kentry) (K : kentry) | ONameB (a : saddr) | ONameW (a : saddr) (w : nat)
  | OAbsW (b : expr) (o n : Z) | OCoalW (b : expr) (o : Z) (n : expr)
  | OCellR (a a' : saddr) (w : nat).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_wr (X : kentry) : bool := match X with KWr _ _ | KWord _ _ _ => true | _ => false end.
Definition keepwr (old new : list kentry) : list kentry :=
  List.filter (fun X => (is_wr X && negb (existsb (APC.kentry_eqb X) new))%bool) old.
Definition readd (ss ss' : sym_state) : sym_state := SGP.set_kn ss' (s_know ss' ++ keepwr (s_know ss) (s_know ss')).
Definition abstract_w (A : APC.atable) (ss : sym_state) (b : expr) (o n : Z) : option sym_state :=
  match SGP.abstract A ss b o n with Some ss' => Some (readd ss ss') | None => None end.
Definition coalesce_w (A : APC.atable) (ss : sym_state) (b : expr) (o : Z) (n : expr) : option sym_state :=
  match SGP.coalesce A ss b o n with Some ss' => Some (readd ss ss') | None => None end.

(* [comment removed for export] *)
Definition covers1 (kn : list kentry) (a : saddr) (K : kentry) : bool :=
  match K with KUnk (SA kb kk) len => zf_covers kn (a_base a) (a_off a) 1 kb kk len | _ => false end.
Definition name_byte (a : saddr) (ss : sym_state) : option sym_state :=
  let kn := s_know ss in let nx := s_next ss in
  if (expr_vars_lt nx (a_base a) && sr_vars_lt nx (s_regs ss) && kn_vars_lt nx kn && existsb (covers1 kn a) kn)%bool
  then Some (SSR (s_pc ss) (s_regs ss) (s_log ss) (KWord a 1 (EVar nx) :: KRange (EVar nx) 0 255 :: kn) (S nx) (s_resv ss))
  else None.

Definition prem_ok (kn : list kentry) (P : kentry) : bool := if CX.has_k kn P then true else CX.fact2_ok kn P.
(* [comment removed for export] *)
Definition coversw (kn : list kentry) (a : saddr) (w : nat) (K : kentry) : bool :=
  match K with KUnk (SA kb kk) len => zf_covers kn (a_base a) (a_off a) w kb kk len | _ => false end.
Definition name_word (a : saddr) (w : nat) (ss : sym_state) : option sym_state :=
  let kn := s_know ss in let nx := s_next ss in
  if (Nat.leb 1 w && Nat.leb w 8 && expr_vars_lt nx (a_base a) && sr_vars_lt nx (s_regs ss) && kn_vars_lt nx kn && existsb (coversw kn a w) kn)%bool
  then Some (SSR (s_pc ss) (s_regs ss) (s_log ss) (KWord a w (EVar nx) :: KRange (EVar nx) 0 (2 ^ (8 * Z.of_nat w) - 1) :: kn) (S nx) (s_resv ss))
  else None.

(* [comment removed for export] *)
Definition addr_lin_eq (a a' : saddr) : bool :=
  let l := lin_of (a_base a) in let l' := lin_of (a_base a') in
  (match lsub_e (snd l) (snd l') with [] => true | _ => false end
   && Z.eqb ((fst l + a_off a - (fst l' + a_off a')) mod 18446744073709551616) 0)%bool.
Definition cell_respell (a a' : saddr) (w : nat) (ss : sym_state) : option sym_state :=
  match SGP.cell_value (s_know ss) a w with
  | Some v => if (addr_lin_eq a a' && APC.flat_x (s_know ss) (a_base a') (a_off a') (ELit (Z.of_nat w)) && APC.kentry_vars_lt (s_next ss) (KWord a' w v))%bool
              then Some (SGP.set_kn ss (KWord a' w v :: s_know ss)) else None
  | None => None
  end.

Definition lem_apply (Ps : list kentry) (K : kentry) (ss : sym_state) : option sym_state :=
  if (forallb (prem_ok (s_know ss)) Ps && APC.kentry_vars_lt (s_next ss) K)%bool then Some (SGP.set_kn ss (K :: s_know ss)) else None.
Section WithA.
Variable A : APC.atable.
Definition xop_apply (op : xop) (ss : sym_state) : option sym_state :=
  match op with
  | OBase o => CX.xop_apply o ss | OLem Ps K => lem_apply Ps K ss | ONameB a => name_byte a ss | ONameW a w => name_word a w ss
  | OAbsW b o n => abstract_w A ss b o n | OCoalW b o n => coalesce_w A ss b o n
  | OCellR a a' w => cell_respell a a' w ss
  end.
Definition xstep (T : list xop) (F : list SGP.region) (id : nat) (ss : sym_state) : option sym_state :=
  match nth_error T id with Some op => xop_apply op ss | None => None end.

(* [comment removed for export] *)
Definition lemma_ok (segs : list Segment) (Ps : list kentry) (K : kentry) : Prop :=
  forall E M, Forall (kentry_ok segs E M) Ps -> kentry_ok segs E M K.
Definition op_ok (segs : list Segment) (op : xop) : Prop := match op with OLem Ps K => lemma_ok segs Ps K | _ => True end.
Definition lemmas_ok (segs : list Segment) (T : list xop) : Prop := Forall (op_ok segs) T.
Definition lemmas_of (T : list xop) : list (list kentry * kentry) :=
  flat_map (fun op => match op with OLem Ps K => [(Ps, K)] | _ => [] end) T.
Lemma lemmas_ok_of : forall segs T, Forall (fun l => lemma_ok segs (fst l) (snd l)) (lemmas_of T) -> lemmas_ok segs T.
Proof.
  intros segs T. induction T as [|op T IH]; intros H; [constructor|].
  destruct op as [o|Ps K|a|a w|b o n|b o n|a a' w]; cbn [lemmas_of flat_map app] in H; try (constructor; [exact I | exact (IH H)]).
  apply Forall_cons_iff in H as [H1 H2]. constructor; [exact H1 | exact (IH H2)].
Qed.

Lemma prem_ok_sound : forall segs E M kn P, know_ok segs E M kn -> prem_ok kn P = true -> kentry_ok segs E M P.
Proof.
  intros segs E M kn P Hkn H. unfold prem_ok in H. destruct (CX.has_k kn P) eqn:Hh.
  - apply CX.has_k_In in Hh. exact (proj1 (Forall_forall _ _) Hkn _ Hh).
  - exact (CX.fact2_ok_sound segs E M kn P Hkn H).
Qed.

Lemma wle1_byte : forall b : byte, word_to_le_bytes 1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof.
  intros b. pose proof (APSX.word_to_le_bytes_of_bytes [b] ltac:(cbn; lia)) as H. cbn [length bytes_le_to_Z] in H.
  change (0 ≪ 8) with 0 in H. rewrite Z.lor_0_r in H. exact H.
Qed.

Lemma name_byte_sound : forall segs nx0 BR F M0 a ss ss' E R Mc,
  forallb (SGP.region_vars_lt nx0) F = true -> SGP.bfacts_vars_lt BR nx0 = true ->
  name_byte a ss = Some ss' -> SGP.INV2 segs nx0 BR F M0 E ss R Mc ->
  exists E', env_agree (s_next ss) E E' /\ SGP.INV2 segs nx0 BR F M0 E' ss' R Mc /\ s_pc ss' = s_pc ss.
Proof.
  intros segs nx0 BR F M0 a ss ss' E R Mc Fv BRv H HI. unfold name_byte in H.
  destruct (expr_vars_lt (s_next ss) (a_base a) && sr_vars_lt (s_next ss) (s_regs ss) && kn_vars_lt (s_next ss) (s_know ss)
            && existsb (covers1 (s_know ss) a) (s_know ss))%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hc Hcov]. apply andb_prop in Hc as [Hc Hkn]. apply andb_prop in Hc as [Hav Hsr].
  pose proof (SGP.i_regs _ _ _ _ _ _ _ _ _ HI) as HR. pose proof (SGP.i_know _ _ _ _ _ _ _ _ _ HI) as HK. pose proof (SGP.i_nx _ _ _ _ _ _ _ _ _ HI) as Hnx.
  (* [comment removed for export] *)
  apply existsb_exists in Hcov as (K0 & HK0in & HK0).
  destruct K0 as [? ? ?|? ?|? ? ?|? ?|? ?|? ? ?|? ?|? ? ? ?|? ? ?|[kb kk] len]; cbn [covers1] in HK0; try discriminate.
  pose proof (proj1 (Forall_forall _ _) HK _ HK0in) as HU. cbn [kentry_ok] in HU. destruct HU as [Hfl Hdef].
  destruct (zf_covers_sound segs E Mc (s_know ss) (a_base a) (a_off a) 1 kb kk len HK ltac:(lia) HK0) as [A1 B1].
  assert (Ea : SA (a_base a) (a_off a) = a) by (destruct a; reflexivity). rewrite Ea in A1, B1.
  assert (Hfa : flat E a 1) by (unfold flat, estart in *; cbn [a_base a_off] in *; lia).
  specialize (Hdef (estart E a - estart E (SA kb kk)) ltac:(lia)).
  replace (estart E (SA kb kk) + (estart E a - estart E (SA kb kk))) with (estart E a) in Hdef by lia.
  destruct (Mc (Z_to_bv 64 (estart E a))) as [b|] eqn:Hb; [|contradiction]. clear Hdef.
  set (E' := APS.ext1 E (s_next ss) (Z_to_bv 64 (bv_unsigned b))).
  pose proof (APS.ext1_agree E (s_next ss) (Z_to_bv 64 (bv_unsigned b))) as Hag. fold E' in Hag.
  exists E'. split; [exact Hag|]. split; [|reflexivity].
  eapply (SGP.INV2_reenv segs nx0 BR F Fv BRv M0 (s_next ss) E E' ss _ R R Mc HI Hag Hnx); cbn [s_regs s_know s_next].
  - exact (regs_ok_agree (s_next ss) E E' (s_regs ss) R Hag Hsr HR).
  - pose proof (bv_unsigned_in_range _ b) as Bb. change (bv_modulus 8) with 256 in Bb.
    assert (Hden : edenot E' (a_base a) = edenot E (a_base a)) by (symmetry; exact (edenot_agree (s_next ss) E E' (a_base a) Hag Hav)).
    assert (Hst : estart E' a = estart E a) by (unfold estart; rewrite Hden; reflexivity).
    constructor; [|constructor; [|exact (know_ok_agree segs (s_next ss) E E' Mc (s_know ss) Hag Hkn HK)]].
    + cbn [kentry_ok]. split; [lia|]. split; [unfold flat in *; rewrite Hst; exact Hfa|].
      cbn [edenot]. unfold E'. rewrite APS.ext1_at. rewrite wle1_byte. apply rdn_one.
      assert (Had : adenot (APS.ext1 E (s_next ss) (Z_to_bv 64 (bv_unsigned b))) a = Z_to_bv 64 (estart E a)).
      { fold E'. apply bv_eq. rewrite (flat_u E' a 1) by (unfold flat in *; rewrite Hst; exact Hfa). rewrite Hst.
        rewrite Z_to_bv_unsigned. unfold bv_wrap. symmetry. apply Z.mod_small. unfold flat in Hfa. change (bv_modulus 64) with (2 ^ 64). lia. }
      rewrite Had, Hb. reflexivity.
    + cbn [kentry_ok edenot]. unfold E'. rewrite APS.ext1_at. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Z.mod_small by lia. lia.
  - lia.
Qed.

Lemma name_word_sound : forall segs nx0 BR F M0 a w ss ss' E R Mc,
  forallb (SGP.region_vars_lt nx0) F = true -> SGP.bfacts_vars_lt BR nx0 = true ->
  name_word a w ss = Some ss' -> SGP.INV2 segs nx0 BR F M0 E ss R Mc ->
  exists E', env_agree (s_next ss) E E' /\ SGP.INV2 segs nx0 BR F M0 E' ss' R Mc /\ s_pc ss' = s_pc ss.
Proof.
  intros segs nx0 BR F M0 a w ss ss' E R Mc Fv BRv H HI. unfold name_word in H.
  destruct (Nat.leb 1 w && Nat.leb w 8 && expr_vars_lt (s_next ss) (a_base a) && sr_vars_lt (s_next ss) (s_regs ss) && kn_vars_lt (s_next ss) (s_know ss)
            && existsb (coversw (s_know ss) a w) (s_know ss))%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hc Hcov]. apply andb_prop in Hc as [Hc Hkn]. apply andb_prop in Hc as [Hc Hsr].
  apply andb_prop in Hc as [Hc Hav]. apply andb_prop in Hc as [Hw1 Hw8]. apply Nat.leb_le in Hw1, Hw8.
  pose proof (SGP.i_regs _ _ _ _ _ _ _ _ _ HI) as HR. pose proof (SGP.i_know _ _ _ _ _ _ _ _ _ HI) as HK. pose proof (SGP.i_nx _ _ _ _ _ _ _ _ _ HI) as Hnx.
  apply existsb_exists in Hcov as (K0 & HK0in & HK0).
  destruct K0 as [? ? ?|? ?|? ? ?|? ?|? ?|? ? ?|? ?|? ? ? ?|? ? ?|[kb kk] len]; cbn [coversw] in HK0; try discriminate.
  pose proof (proj1 (Forall_forall _ _) HK _ HK0in) as HU. cbn [kentry_ok] in HU. destruct HU as [Hfl Hdef].
  destruct (zf_covers_sound segs E Mc (s_know ss) (a_base a) (a_off a) w kb kk len HK Hw8 HK0) as [A1 B1].
  assert (Ea : SA (a_base a) (a_off a) = a) by (destruct a; reflexivity). rewrite Ea in A1, B1.
  assert (Hfa : flat E a (Z.of_nat w)) by (unfold flat, estart in *; cbn [a_base a_off] in *; lia).
  pose proof (flat_u E a _ Hfa) as Hua.
  destruct (rdn_defined segs Mc w (adenot E a)) as (bs & Hbs & Hlen).
  { rewrite Hua. unfold flat in Hfa. lia. }
  { intros j Hj. rewrite Hua. unfold rd1.
    specialize (Hdef (estart E a - estart E (SA kb kk) + Z.of_nat j) ltac:(lia)).
    replace (estart E (SA kb kk) + (estart E a - estart E (SA kb kk) + Z.of_nat j)) with (estart E a + Z.of_nat j) in Hdef by lia.
    destruct (Mc (Z_to_bv 64 (estart E a + Z.of_nat j))); [discriminate | contradiction]. }
  set (V := Z_to_bv 64 (bytes_le_to_Z bs)).
  set (E' := APS.ext1 E (s_next ss) V).
  pose proof (APS.ext1_agree E (s_next ss) V) as Hag. fold E' in Hag.
  exists E'. split; [exact Hag|]. split; [|reflexivity].
  eapply (SGP.INV2_reenv segs nx0 BR F Fv BRv M0 (s_next ss) E E' ss _ R R Mc HI Hag Hnx); cbn [s_regs s_know s_next].
  - exact (regs_ok_agree (s_next ss) E E' (s_regs ss) R Hag Hsr HR).
  - assert (Hden : edenot E' (a_base a) = edenot E (a_base a)) by (symmetry; exact (edenot_agree (s_next ss) E E' (a_base a) Hag Hav)).
    assert (Had : adenot E' a = adenot E a) by (unfold adenot; rewrite Hden; reflexivity).
    assert (Hst : estart E' a = estart E a) by (unfold estart; rewrite Hden; reflexivity).
    pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Hlen in Bb.
    assert (Hpw : 2 ^ (8 * Z.of_nat w) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    constructor; [|constructor; [|exact (know_ok_agree segs (s_next ss) E E' Mc (s_know ss) Hag Hkn HK)]].
    + cbn [kentry_ok]. split; [exact Hw8|]. split; [unfold flat in *; rewrite Hst; exact Hfa|].
      cbn [edenot]. unfold E'. rewrite APS.ext1_at. fold E'. rewrite Had, Hbs. f_equal. symmetry.
      exact (APSX.word_to_le_bytes_of_bytes_n w bs Hlen Hw8).
    + cbn [kentry_ok edenot]. unfold E'. rewrite APS.ext1_at. unfold V. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
      rewrite Z.mod_small by lia. lia.
  - lia.
Qed.

Lemma readd_sound : forall segs nx0 BR F M0 E ss ss' R Mc,
  SGP.INV2 segs nx0 BR F M0 E ss R Mc -> SGP.INV2 segs nx0 BR F M0 E ss' R Mc -> SGP.INV2 segs nx0 BR F M0 E (readd ss ss') R Mc.
Proof.
  intros segs nx0 BR F M0 E ss ss' R Mc HI HI'. unfold readd. apply SGP.set_kn_INV2; [exact HI'|].
  apply Forall_app. split; [exact (SGP.i_know _ _ _ _ _ _ _ _ _ HI')|].
  apply Forall_forall. intros X HX. unfold keepwr in HX. apply filter_In in HX as [HX _].
  exact (proj1 (Forall_forall _ _) (SGP.i_know _ _ _ _ _ _ _ _ _ HI) X HX).
Qed.

Lemma cell_value_In : forall kn a w v, SGP.cell_value kn a w = Some v -> In (KWord a w v) kn.
Proof.
  induction kn as [|K r IH]; intros a w v H; [discriminate|]. cbn [SGP.cell_value] in H.
  destruct K as [a0 w0 e0| | | | | | | | |]; try (right; exact (IH _ _ _ H)).
  destruct (saddr_eqb a a0 && Nat.eqb w w0)%bool eqn:Hb; [|right; exact (IH _ _ _ H)].
  apply andb_prop in Hb as [Ha Hw]. apply saddr_eqb_eq in Ha. apply Nat.eqb_eq in Hw. injection H as <-. subst a0 w0. left. reflexivity.
Qed.
Lemma addr_lin_eq_sound : forall E a a', addr_lin_eq a a' = true -> eqm (estart E a) (estart E a').
Proof.
  intros E a a' H. unfold addr_lin_eq in H. apply andb_prop in H as [Ht Hc]. apply Z.eqb_eq in Hc.
  destruct (lsub_e (snd (lin_of (a_base a))) (snd (lin_of (a_base a')))) as [|x r] eqn:Hs; [|discriminate].
  pose proof (lsub_e_sound E (snd (lin_of (a_base a))) (snd (lin_of (a_base a')))) as Hd. rewrite Hs in Hd. cbn [tden] in Hd.
  destruct (lin_of_sound E (a_base a)) as [q1 H1]. destruct (lin_of_sound E (a_base a')) as [q2 H2]. unfold lden, uE in H1, H2.
  apply Z.mod_divide in Hc; [|lia]. destruct Hc as [q3 H3]. unfold estart. exists (q3 - q1 + q2). lia.
Qed.
Lemma cell_respell_sound : forall segs nx0 BR F M0 a a' w ss ss' E R Mc,
  cell_respell a a' w ss = Some ss' -> SGP.INV2 segs nx0 BR F M0 E ss R Mc -> SGP.INV2 segs nx0 BR F M0 E ss' R Mc /\ s_pc ss' = s_pc ss.
Proof.
  intros segs nx0 BR F M0 a a' w ss ss' E R Mc H HI. unfold cell_respell in H.
  destruct (SGP.cell_value (s_know ss) a w) as [v|] eqn:Hv; [|discriminate].
  destruct (addr_lin_eq a a' && APC.flat_x (s_know ss) (a_base a') (a_off a') (ELit (Z.of_nat w)) && APC.kentry_vars_lt (s_next ss) (KWord a' w v))%bool eqn:Hc; [|discriminate].
  injection H as <-. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hlin Hflat]. split; [|reflexivity].
  pose proof (SGP.i_know _ _ _ _ _ _ _ _ _ HI) as HK.
  apply SGP.set_kn_INV2; [exact HI|]. constructor; [|exact HK].
  pose proof (proj1 (Forall_forall _ _) HK _ (cell_value_In _ _ _ _ Hv)) as HW. cbn [kentry_ok] in HW |- *. destruct HW as (Hw8 & Hfl & Hrd).
  destruct (APS.flat_x_sound segs E Mc (s_know ss) (a_base a') (a_off a') (ELit (Z.of_nat w)) HK Hflat) as (F1 & F2 & F3).
  cbn [edenot] in F2, F3. rewrite u_lit64 in F2, F3. assert (Hwz : (Z.of_nat w) mod two64 = Z.of_nat w) by (apply Z.mod_small; unfold two64; lia). rewrite Hwz in F2, F3.
  assert (Ea' : SA (a_base a') (a_off a') = a') by (destruct a'; reflexivity). rewrite Ea' in F1, F2.
  assert (Hfl' : flat E a' (Z.of_nat w)) by (unfold flat; lia).
  assert (Heq : estart E a = estart E a').
  { destruct (addr_lin_eq_sound E a a' Hlin) as [q Hq]. unfold flat in Hfl, Hfl'. lia. }
  assert (Had : adenot E a' = adenot E a).
  { apply bv_eq. rewrite (flat_u E a' _ Hfl'), (flat_u E a _ Hfl). lia. }
  split; [exact Hw8|]. split; [exact Hfl'|]. rewrite Had. exact Hrd.
Qed.

Theorem xstep_ok : forall segs nx0 BR T F M0,
  (forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None) -> APS.hull_ok A ->
  lemmas_ok segs T -> SGP.XSTEP_ok segs nx0 BR (xstep T) F M0.
Proof.
  intros segs nx0 BR T F M0 HULL1 HULL2 HL Fv BRv fx id ss ss' E R Mc H HI. unfold xstep in H.
  destruct (nth_error T id) as [op|] eqn:Hn; [|discriminate].
  destruct op as [o|Ps K|a|a w|b o n|b o n|a a' w]; cbn [xop_apply] in H.
  7: { destruct (cell_respell_sound segs nx0 BR F M0 a a' w ss ss' E R Mc H HI) as (HI' & Hpc).
       exists fx, E, R, Mc. split; [split; reflexivity|]. split; [exact HI' | rewrite Hpc; apply mst_refl]. }
  4: { destruct (name_word_sound segs nx0 BR F M0 a w ss ss' E R Mc Fv BRv H HI) as (E' & Hag & HI' & Hpc).
       exists fx, E', R, Mc. split; [exact Hag|]. split; [exact HI' | rewrite Hpc; apply mst_refl]. }
  5: { unfold coalesce_w in H. destruct (SGP.coalesce A ss b o n) as [s1|] eqn:Hs; [|discriminate]. injection H as <-.
       destruct (SGP.coalesce_sound segs A nx0 BR HULL1 HULL2 F M0 E ss R Mc b o n s1 HI Hs) as (HI1 & Hpc & _).
       exists fx, E, R, Mc. split; [split; reflexivity|]. split; [exact (readd_sound _ _ _ _ _ _ _ _ _ _ HI HI1)|].
       cbn [readd SGP.set_kn s_pc]. rewrite Hpc. apply mst_refl. }
  4: { unfold abstract_w in H. destruct (SGP.abstract A ss b o n) as [s1|] eqn:Hs; [|discriminate]. injection H as <-.
       destruct (SGP.abstract_sound segs A nx0 BR HULL1 HULL2 F M0 E ss R Mc b o n s1 HI Hs) as (HI1 & Hpc & _).
       exists fx, E, R, Mc. split; [split; reflexivity|]. split; [exact (readd_sound _ _ _ _ _ _ _ _ _ _ HI HI1)|].
       cbn [readd SGP.set_kn s_pc]. rewrite Hpc. apply mst_refl. }
  3: { destruct (name_byte_sound segs nx0 BR F M0 a ss ss' E R Mc Fv BRv H HI) as (E' & Hag & HI' & Hpc).
       exists fx, E', R, Mc. split; [exact Hag|]. split; [exact HI' | rewrite Hpc; apply mst_refl]. }
  - (* [comment removed for export] *)
    refine (CX.xstep_ok segs nx0 BR [o] F M0 Fv BRv fx 0%nat ss ss' E R Mc _ HI). exact H.
  - unfold lem_apply in H.
    destruct (forallb (prem_ok (s_know ss)) Ps && APC.kentry_vars_lt (s_next ss) K)%bool eqn:Hc; [|discriminate]. injection H as <-.
    apply andb_prop in Hc as [Hp _].
    pose proof (proj1 (Forall_forall _ _) HL _ (nth_error_In _ _ Hn)) as Hop. cbn [op_ok] in Hop.
    exists fx, E, R, Mc. split; [split; reflexivity|]. split; [|cbn [SGP.set_kn s_pc]; apply mst_refl].
    apply SGP.set_kn_INV2; [exact HI|]. constructor; [|exact (SGP.i_know _ _ _ _ _ _ _ _ _ HI)].
    apply Hop. apply Forall_forall. intros P HP. rewrite forallb_forall in Hp.
    exact (prem_ok_sound segs E Mc (s_know ss) P (SGP.i_know _ _ _ _ _ _ _ _ _ HI) (Hp P HP)).
Qed.
End WithA.

(* [comment removed for export] *)
Definition lem_eqb (a b : list kentry * kentry) : bool :=
  (APC.kentry_eqb (snd a) (snd b) && Nat.eqb (length (fst a)) (length (fst b)) && forallb (fun p => APC.kentry_eqb (fst p) (snd p)) (combine (fst a) (fst b)))%bool.
Definition lem_dedup (l : list (list kentry * kentry)) : list (list kentry * kentry) := fold_right (fun x acc => if existsb (lem_eqb x) acc then acc else x :: acc) [] l.
Lemma lem_eqb_eq : forall a b, lem_eqb a b = true -> a = b.
Proof.
  intros [pa ka] [pb kb] H. unfold lem_eqb in H. cbn [fst snd] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply APS.kentry_eqb_eq in H1. subst kb. apply Nat.eqb_eq in H2. f_equal.
  revert pb H2 H3. induction pa as [|x pa IH]; intros [|y pb] H2 H3; try discriminate; [reflexivity|].
  cbn [combine forallb fst snd] in H3. apply andb_prop in H3 as [Hx Hr]. apply APS.kentry_eqb_eq in Hx. subst y. f_equal. apply IH; [cbn in H2; lia | exact Hr].
Qed.
Definition LEMS_OK (segs : list Segment) (LEMS : list (list kentry * kentry)) : Prop := Forall (fun l => lemma_ok segs (fst l) (snd l)) LEMS.
Definition lems_chk (LEMS : list (list kentry * kentry)) (T : list xop) : bool := forallb (fun l => existsb (lem_eqb l) LEMS) (lemmas_of T).
Lemma lems_sub : forall segs LEMS T, lems_chk LEMS T = true -> LEMS_OK segs LEMS -> lemmas_ok segs T.
Proof.
  intros segs LEMS T H HL. apply lemmas_ok_of. apply Forall_forall. intros l Hl. unfold lems_chk in H. rewrite forallb_forall in H. specialize (H l Hl).
  apply existsb_exists in H as (l' & Hin & He). apply lem_eqb_eq in He. subst l'. exact (proj1 (Forall_forall _ _) HL l Hin).
Qed.
End CXD.
