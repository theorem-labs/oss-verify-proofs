(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec AxSymExec3 AxSymExec3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Module AX2K.
Import AX2 AX2B.

(* [comment removed for export] *)
Lemma lin_range_shift : forall rng c d ts,
  lin_range rng (c + d)%Z ts = match lin_range rng c ts with Some (lo, hi) => Some ((lo + d)%Z, (hi + d)%Z) | None => None end.
Proof.
  intros rng c d ts. induction ts as [|[k a] rest IH]; [reflexivity|].
  cbn [lin_range]. rewrite IH. destruct (rng a) as [[al ah]|]; [|reflexivity].
  destruct (lin_range rng c rest) as [[lo hi]|]; [|reflexivity].
  destruct (Z.leb 0 k); f_equal; f_equal; lia.
Qed.

(* [comment removed for export] *)
Definition plain_ge0B (bc : bctx) (pos neg : xterms) : bool :=
  match lin_range (erangeB bc) (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) with
  | Some (lo, hi) =>
      if Z.leb 0 lo then if Z.leb 0 hi then if xt_nowrapB bc pos then xt_nowrapB bc neg else false else false else false
  | None => false
  end.

Lemma plain_ge0B_core : forall bc pos neg, plain_ge0B bc pos neg = true -> lin_ge0_coreB bc pos neg = true.
Proof.
  intros bc pos neg H. unfold plain_ge0B in H. unfold lin_ge0_coreB.
  destruct (lin_range (erangeB bc) (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg))) as [[lo hi]|]; [|discriminate].
  destruct (Z.leb 0 lo) eqn:Hlo; [|discriminate]. destruct (Z.leb 0 hi) eqn:Hhi; [|discriminate].
  destruct (xt_nowrapB bc pos); [|discriminate]. rewrite H. cbn [negb].
  unfold lin_hopeless. replace (Z.ltb hi 0) with false by (symmetry; apply Z.ltb_ge; apply Z.leb_le; exact Hhi).
  unfold lin_test_rB. rewrite Hlo. reflexivity.
Qed.

Lemma plain_ge0B_ge0 : forall bc pos neg, plain_ge0B bc pos neg = true -> lin_ge0BF bc pos neg = true.
Proof. intros bc pos neg H. rewrite lin_ge0BF_eq. unfold lin_ge0B. rewrite (plain_ge0B_core _ _ _ H). reflexivity. Qed.

Lemma plain_ge0B_mono : forall bc pos neg pos' neg',
  xt_lin pos' = xt_lin pos -> xt_lin neg' = xt_lin neg ->
  (xt_nowrapB bc pos = true -> xt_nowrapB bc pos' = true) -> (xt_nowrapB bc neg = true -> xt_nowrapB bc neg' = true) ->
  (xt_const pos - xt_const neg <= xt_const pos' - xt_const neg')%Z ->
  plain_ge0B bc pos neg = true -> plain_ge0B bc pos' neg' = true.
Proof.
  intros bc pos neg pos' neg' Ep En Np Nn Hc H. unfold plain_ge0B in *. rewrite Ep, En.
  replace (xt_const pos' - xt_const neg')%Z
    with ((xt_const pos - xt_const neg) + ((xt_const pos' - xt_const neg') - (xt_const pos - xt_const neg)))%Z by lia.
  rewrite lin_range_shift.
  destruct (lin_range (erangeB bc) (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg))) as [[lo hi]|]; [|discriminate].
  destruct (Z.leb 0 lo) eqn:Hlo; [|discriminate]. destruct (Z.leb 0 hi) eqn:Hhi; [|discriminate].
  destruct (xt_nowrapB bc pos) eqn:P; [|discriminate]. rewrite (Np eq_refl), (Nn H).
  apply Z.leb_le in Hlo, Hhi.
  replace (Z.leb 0 (lo + (xt_const pos' - xt_const neg' - (xt_const pos - xt_const neg)))) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb 0 (hi + (xt_const pos' - xt_const neg' - (xt_const pos - xt_const neg)))) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma snorm_id : forall z, (- 2 ^ 63 <= z < 2 ^ 63)%Z -> snorm z = z.
Proof.
  intros z Hz. unfold snorm, mtwo63z, two63z.
  replace (Z.leb (- 2 ^ 63) z) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.ltb z (2 ^ 63)) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma lin_nowrapRB_lit : forall bc m, (0 <= m < 2 ^ 63)%Z -> lin_nowrapRB bc (ELit m) = true.
Proof.
  intros bc m Hm. unfold lin_nowrapRB. cbn [lin_of fst snd srl_expandB]. rewrite (snorm_id m) by lia.
  unfold lin_testB. cbn [lin_range].
  replace (Z.leb 0 (m + 0)) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.ltb (m + 0) two64) with true by (symmetry; apply Z.ltb_lt; unfold two64; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Definition hull_lin (bc : bctx) (gkb : expr) (glo ghi : Z) (c : saddr) (ml : expr) : bool :=
  if shares_var gkb (a_base c) then
    if (if Z.leb glo ghi then Z.ltb (ghi - glo) (2 ^ 63) else false) then
      if plain_ge0B bc [(gkb, glo)] [(a_base c, a_off c)]
      then plain_ge0B bc [(a_base c, a_off c); (ml, 0%Z)] [(gkb, glo); (ELit (ghi - glo), 0%Z)]
      else false
    else false
  else false.

(* [comment removed for export] *)
Lemma hull_lin_member : forall bc gkb glo ghi c ml k m,
  hull_lin bc gkb glo ghi c ml = true -> (glo <= k)%Z -> (k + m <= ghi)%Z -> (0 <= m)%Z ->
  sub_itvB bc gkb k m c ml = true.
Proof.
  intros bc gkb glo ghi c ml k m H Hk Hkm Hm. unfold hull_lin in H.
  destruct (shares_var gkb (a_base c)) eqn:SV; [|discriminate].
  destruct (Z.leb glo ghi) eqn:Hle; [|discriminate]. destruct (Z.ltb (ghi - glo) (2 ^ 63)) eqn:Hlt; [|discriminate].
  apply Z.leb_le in Hle. apply Z.ltb_lt in Hlt.
  destruct (plain_ge0B bc [(gkb, glo)] [(a_base c, a_off c)]) eqn:P1; [|discriminate]. rename H into P2.
  unfold sub_itvB.
  match goal with |- (if ?X then true else _) = true => destruct X; [reflexivity|] end.
  replace (Z.leb 0 m && Z.ltb m two64)%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt; unfold two64]; lia).
  unfold xinsideB. rewrite SV. unfold xinside0B.
  rewrite (plain_ge0B_ge0 bc [(gkb, k)] [(a_base c, a_off c)]).
  - apply plain_ge0B_ge0.
    apply (plain_ge0B_mono bc [(a_base c, a_off c); (ml, 0%Z)] [(gkb, glo); (ELit (ghi - glo), 0%Z)]); [reflexivity | reflexivity | auto | | | exact P2].
    + cbn [xt_nowrapB]. intros N. apply andb_prop in N as [N1 _]. rewrite N1. rewrite lin_nowrapRB_lit by lia. reflexivity.
    + cbn [xt_const lin_of fst]. rewrite (snorm_id (ghi - glo)) by lia. rewrite (snorm_id m) by lia. lia.
  - apply (plain_ge0B_mono bc [(gkb, glo)] [(a_base c, a_off c)]); [reflexivity | reflexivity | auto | auto | | exact P1].
    cbn [xt_const]. lia.
Qed.

(* [comment removed for export] *)
Definition hull_num (bc : bctx) (gkb : expr) (glo ghi : Z) (c : saddr) (ml : expr) : bool :=
  if shares_var gkb (a_base c) then false
  else if novars (a_base c) then
    if (if Z.leb glo ghi then Z.ltb (ghi - glo) (2 ^ 63) else false) then
      match xloB bc (a_base c), xhiB bc (a_base c) with
      | Some lo2, Some hi2 =>
          if Z.eqb lo2 hi2 then
            match base_rangeB bc gkb, xloB bc ml with
            | Some (lo1, hi1), Some l2 => (Z.leb (lo2 + a_off c) (lo1 + glo) && Z.leb (hi1 + ghi) (lo2 + a_off c + l2))%bool
            | _, _ => false
            end
          else false
      | _, _ => false
      end
    else false
  else false.

Lemma hull_num_member : forall bc gkb glo ghi c ml k m,
  hull_num bc gkb glo ghi c ml = true -> (glo <= k)%Z -> (k + m <= ghi)%Z -> (0 <= m)%Z ->
  sub_itvB bc gkb k m c ml = true.
Proof.
  intros bc gkb glo ghi c ml k m H Hk Hkm Hm. unfold hull_num in H.
  destruct (shares_var gkb (a_base c)) eqn:SV; [discriminate|].
  destruct (novars (a_base c)) eqn:NV; [|discriminate].
  destruct (Z.leb glo ghi) eqn:Hle; [|discriminate]. destruct (Z.ltb (ghi - glo) (2 ^ 63)) eqn:Hlt; [|discriminate].
  apply Z.leb_le in Hle. apply Z.ltb_lt in Hlt.
  destruct (xloB bc (a_base c)) as [lo2|] eqn:X1; [|discriminate]. destruct (xhiB bc (a_base c)) as [hi2|] eqn:X2; [|discriminate].
  destruct (Z.eqb lo2 hi2) eqn:EQ; [|discriminate].
  destruct (base_rangeB bc gkb) as [[lo1 hi1]|] eqn:BR; [|discriminate]. destruct (xloB bc ml) as [l2|] eqn:X3; [|discriminate].
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
  unfold sub_itvB.
  match goal with |- (if ?X then true else _) = true => destruct X; [reflexivity|] end.
  replace (Z.leb 0 m && Z.ltb m two64)%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt; unfold two64]; lia).
  unfold xinsideB. rewrite SV, NV. unfold xinside_numB. rewrite X1, X2, EQ, BR, X3. cbn [xhiB].
  assert (Z64 : zlit64 m = m).
  { unfold zlit64. replace (Z.leb 0 m && Z.ltb m two64)%bool with true
      by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt; unfold two64]; lia). reflexivity. }
  rewrite Z64.
  replace (Z.leb (lo2 + a_off c) (lo1 + k)) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (hi1 + k + m) (lo2 + a_off c + l2)) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Definition hull_in (bc : bctx) (gkb : expr) (glo ghi : Z) (c : saddr) (ml : expr) : bool :=
  if (if expr_eqb gkb (a_base c) then
        if Z.leb (a_off c) glo then match xloB bc ml with Some l => Z.leb ghi (a_off c + l) | None => false end else false
      else false)
  then true else if hull_lin bc gkb glo ghi c ml then true else hull_num bc gkb glo ghi c ml.

Lemma hull_in_member : forall bc gkb glo ghi c ml k m,
  hull_in bc gkb glo ghi c ml = true -> (glo <= k)%Z -> (k + m <= ghi)%Z -> (0 <= m)%Z ->
  sub_itvB bc gkb k m c ml = true.
Proof.
  intros bc gkb glo ghi c ml k m H Hk Hkm Hm. unfold hull_in in H.
  assert (ALT : (if hull_lin bc gkb glo ghi c ml then true else hull_num bc gkb glo ghi c ml) = true -> sub_itvB bc gkb k m c ml = true).
  { intros A. destruct (hull_lin bc gkb glo ghi c ml) eqn:HL;
      [apply (hull_lin_member bc gkb glo ghi); assumption | apply (hull_num_member bc gkb glo ghi); assumption]. }
  destruct (expr_eqb gkb (a_base c)) eqn:He; [|apply ALT; exact H].
  destruct (Z.leb (a_off c) glo) eqn:Ho; [|apply ALT; exact H].
  destruct (xloB bc ml) as [l|] eqn:Hx; [|apply ALT; exact H].
  destruct (Z.leb ghi (a_off c + l)) eqn:Hl; [|apply ALT; exact H].
  apply Z.leb_le in Ho, Hl. unfold sub_itvB. rewrite He, Hx. cbn [andb].
  replace (Z.leb (a_off c) k) with true by (symmetry; apply Z.leb_le; lia).
  replace (Z.leb (k + m) (a_off c + l)) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cg_of2 (bc : bctx) (g : gval) : list positive :=
  match g with
  | (_, gkb, _, (glo, ghi)) =>
      List.map fst (List.filter (fun t : positive * (saddr * expr) => let '(c, ml) := snd t in hull_in bc gkb glo ghi c ml)
                                (rt_sides (bc_rt bc)))
  end.
(* [comment removed for export] *)
Definition mk_gl2 (bc : bctx) (bnds : gtab) (sxs : list stx) : ptree gfl :=
  pt_map (fun g => (g, mk_fl (if forallb (fun sx => verdict sx g) sxs then [] else cg_of2 bc g) g sxs)) bnds.

Lemma cg_of2_In : forall bc b gkb obr glo ghi j,
  In j (cg_of2 bc (b, gkb, obr, (glo, ghi))) ->
  exists c ml, rt_In (bc_rt bc) j c ml /\ hull_in bc gkb glo ghi c ml = true.
Proof.
  intros bc b gkb obr glo ghi j H. unfold cg_of2 in H. apply in_map_iff in H as [[j' [c ml]] [E F]]. cbn in E. subst j'.
  apply filter_In in F as [F1 F2]. cbn [snd] in F2. exists c, ml. split; [exact F1 | exact F2].
Qed.

Lemma in_sidesB_In : forall bc D b k m c ml,
  In (c, ml) D -> sub_itvB bc b k m c ml = true -> in_sidesB bc D b k m = true.
Proof.
  intros bc D b k m c ml. induction D as [|[c' ml'] D IH]; intros HIn HS; [destruct HIn|].
  cbn [in_sidesB]. destruct HIn as [E|HIn].
  - injection E as -> ->. rewrite HS. reflexivity.
  - rewrite (IH HIn HS). destruct (sub_itvB bc b k m c' ml'); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma verdict_disjR2_inb : forall bc t sx g ei m,
  bc_rt bc = mk_rt (bc_fk bc) -> SX_OK bc t sx ->
  verdict_disjR (cg_of2 bc g) sx g = true -> inb g ei = true -> ei_m ei = Some m -> (0 <= m)%Z ->
  Pos.eqb (ei_bid ei) (sx_bid sx) = false
  /\ in_sidesB bc (sp_D (sx_sp sx)) (ei_kb ei) (ei_k ei) m = true.
Proof.
  intros bc t sx [[[b gkb] obr] [glo ghi]] ei m E (SXin & SXbr & SXsp & SXps) Hv Hi Hm Hm0.
  unfold verdict_disjR in Hv. unfold inb in Hi. rewrite Hm in Hi.
  apply andb_prop in Hi as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [Hi H2]. apply andb_prop in Hi as [H1 H1'].
  apply Pos.eqb_eq in H1. subst b. apply Z.leb_le in H3. apply Z.leb_le in H4. apply p_expr_eqb_eq in H1'. subst gkb.
  destruct (Pos.eqb (ei_bid ei) (sx_bid sx)); [discriminate|]. split; [reflexivity|].
  apply existsb_exists in Hv as [j [INj Pj]]. apply pmem_In in Pj. rewrite SXps in Pj.
  destruct (cg_of2_In _ _ _ _ _ _ _ INj) as [c [ml [R COND]]].
  pose proof (partners_of_sides _ _ _ _ _ _ _ E Pj R) as IND.
  rewrite SXsp. unfold mk_sprepB, elen. rewrite disj_sidesBM_fst. cbn [sp_D]. fold (zlit64 (Z.of_nat (sx_w sx))).
  apply (in_sidesB_In _ _ _ _ _ c ml IND).
  apply (hull_in_member bc (ei_kb ei) glo ghi); [exact COND | lia | lia | exact Hm0].
Qed.

Lemma zlit64_nonneg : forall z, (0 <= zlit64 z)%Z.
Proof.
  intros z. unfold zlit64. destruct (Z.leb 0 z && Z.ltb z two64)%bool eqn:E.
  - apply andb_prop in E as [E _]. apply Z.leb_le in E. exact E.
  - pose proof (Z.mod_pos_bound z two64 ltac:(unfold two64; lia)). lia.
Qed.
Lemma kdescr_m_nonneg : forall K kb kk m, kdescr K = Some (kb, kk, Some m) -> (0 <= m)%Z.
Proof.
  intros K kb kk m H.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kdescr] in H; try discriminate;
    try (injection H as _ _ <-; apply zlit64_nonneg);
    try (destruct len as [z| | | | | | |]; try discriminate; injection H as _ _ <-; apply zlit64_nonneg).
  destruct (Z.ltb (hi - lo) (2 ^ 64)); [|discriminate]. injection H as _ _ <-. apply zlit64_nonneg.
Qed.

Lemma entriesG2_eq : forall fk sxs bnds kn infos t1,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) sxs -> Forall2 (EINF (mkbc fk) t1) kn infos ->
  entriesG (mkbc fk) sxs (mk_gl2 (mkbc fk) bnds sxs) kn infos = chainRo fk (map strip sxs) kn.
Proof.
  intros fk sxs bnds kn infos t1 HT HS HF. induction HF as [|K oi rest irest HK HF IH].
  - cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
  - cbn [entriesG]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app, IH. f_equal.
    rewrite <- (chain_slow_eq fk sxs [K] (Forall_SX_sp _ _ _ HS)).
    pose proof (Forall_SX_sp _ _ _ HS) as HSP.
    destruct oi as [ei|]; cbn [EINF] in HK.
    + destruct HK as (HD & HIn & Hbr).
      assert (FULL : forall okb, okb = kbase K ->
        chainK2 (mkbc fk) sxs K okb
          (match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end)
          (match okb with Some _ => ei_br ei | None => None end) = chain_slow (mkbc fk) sxs [K]).
      { intros okb Hokb. apply chainK2_eq; [exact HSP|exact Hokb|].
        destruct okb as [kb|]; [|reflexivity].
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & _ & _)]; [|cbn in Hokb; discriminate].
        rewrite <- Hokb in HB. injection HB as ->.
        split; [exact Hbr|]. exact (Forall_SX_same _ _ _ _ _ HT HIn HS). }
      unfold mk_gl2. rewrite pt_get_map.
      destruct (pt_get bnds (ei_gid ei)) as [g|]; [|apply FULL; reflexivity].
      destruct (inb g ei) eqn:Hinb; [|apply FULL; reflexivity].
      rewrite <- (FULL (kbase K) eq_refl). apply chainKF_eq.
      intros sx Hsx Hv.
      assert (Hm : exists m, ei_m ei = Some m).
      { unfold inb in Hinb. destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]. }
      destruct Hm as [m Hm].
      pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp & SXps).
      rewrite Hm in HD.
      unfold verdict2R in Hv. destruct (verdict sx g) eqn:Hv1.
      { destruct (verdict_inb_num _ _ _ _ Hv1 Hinb Hm) as (Hne & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
        * rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_based; [exact HB|exact HD|exact Hsp| | exact Hnum].
          rewrite <- Hbr. exact Hbr2.
        * cbn [kbase]. rewrite Hkb, Hk in *.
          eapply prune1pcK_keep_img; [exact HD| |exact Hsp| rewrite <- Hbr; exact Hbr2 | exact Hnum].
          rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne. }
      (* [comment removed for export] *)
      assert (Hv2 : verdict_disjR (cg_of2 (mkbc fk) g) sx g = true).
      { destruct (forallb (fun sx0 => verdict sx0 g) sxs); [|exact Hv].
        exfalso. unfold verdict_disjR in Hv. destruct g as [[[b gkb] obr] hull]. destruct (Pos.eqb b (sx_bid sx)); discriminate. }
      destruct (verdict_disjR2_inb _ _ _ _ _ _ (mkbc_rt fk) (proj1 (Forall_forall _ _) HS sx Hsx) Hv2 Hinb Hm (kdescr_m_nonneg _ _ _ _ HD))
        as [Hne HSD].
      destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
      * rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_sides; [exact HB|exact HD|exact HSD].
      * cbn [kbase]. rewrite Hkb, Hk in *.
        eapply prune1pcK_keep_img_sides; [exact HD| |exact HSD].
        rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne.
    + apply chainK2_eq; [exact HSP| symmetry; apply kdescr_None_kbase; exact HK | reflexivity].
Qed.

Definition carryG2 (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxs bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_part bc sxs ++ entriesG bc sxs (mk_gl2 bc (gs_bnds gs) sxs) kn infos.

Lemma carryG2_eq : forall log kn,
  carryG2 (mkbc (facts_of kn)) log kn = SPRo (facts_of kn) (rev log) ++ chainRo (facts_of kn) (rev log) kn.
Proof.
  intros log kn. unfold carryG2.
  destruct (mk_stxs (mkbc (facts_of kn)) log nt_empty) as [sxs t0] eqn:E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & Hmap & _).
  destruct (scan_entries (mkbc (facts_of kn)) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
  assert (HS1 : Forall (SX_OK (mkbc (facts_of kn)) t1) sxs).
  { apply Forall_impl with (P := SX_OK (mkbc (facts_of kn)) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
  rewrite (stores_part_eq _ _ _ HT0 HS0), (entriesG2_eq _ _ _ _ _ _ HT1 HS1 HF), Hmap. reflexivity.
Qed.

(* [comment removed for export] *)
Definition carryK2 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryG2 bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryK2_eq : forall log kn hints,
  carryK2 (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. unfold carryK2. destruct log as [|s older]; [reflexivity|].
  destruct hints as [|h hs]; [|apply carryB_eq].
  rewrite carry_vertical, carryG2_eq. reflexivity.
Qed.
Lemma carryK2_carryK : forall log kn hints,
  carryK2 (mkbc (facts_of kn)) log kn hints = carryK (mkbc (facts_of kn)) log kn hints.
Proof. intros. rewrite carryK2_eq, carryK_eq. reflexivity. Qed.


(* [comment removed for export] *)
Lemma lin_test_relB_mono : forall bc c d ts (T T' : Z -> Z -> bool),
  (forall lo hi, T lo hi = true -> T' (lo + d)%Z (hi + d)%Z = true) ->
  lin_test_relB bc c ts T = true -> lin_test_relB bc (c + d)%Z ts T' = true.
Proof.
  intros bc c d ts T T' HT H. unfold lin_test_relB in *. destruct (bc_fs bc) as [|f fs]; [discriminate|].
  destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|discriminate].
  rewrite lin_range_shift. destruct (lin_range (erangeB bc) c ts') as [[lo hi]|]; [|discriminate].
  replace (lo + d + lo0)%Z with (lo + lo0 + d)%Z by lia. replace (hi + d + hi0)%Z with (hi + hi0 + d)%Z by lia. apply HT. exact H.
Qed.
Lemma lin_testB_mono : forall bc c d ts (T T' : Z -> Z -> bool),
  (forall lo hi, T lo hi = true -> T' (lo + d)%Z (hi + d)%Z = true) ->
  lin_testB bc c ts T = true -> lin_testB bc (c + d)%Z ts T' = true.
Proof.
  intros bc c d ts T T' HT H. unfold lin_testB in *. rewrite lin_range_shift.
  destruct (lin_range (erangeB bc) c ts) as [[lo hi]|].
  - destruct (T lo hi) eqn:E.
    + rewrite (HT _ _ E). reflexivity.
    + rewrite (lin_test_relB_mono bc c d ts T T' HT H). destruct (T' (lo + d)%Z (hi + d)%Z); reflexivity.
  - exact (lin_test_relB_mono bc c d ts T T' HT H).
Qed.

(* [comment removed for export] *)
Definition hull_apart (bc : bctx) (b1 : expr) (k1lo k1hi : Z) (gkb : expr) (glo ghi : Z) : bool :=
  if shares_var b1 gkb then
    let l1 := lin_of b1 in let l2 := lin_of gkb in
    let ts := lsub_e (snd l2) (snd l1) in
    if (if lin_testB bc (fst l2 + glo - fst l1 - k1hi)%Z ts (fun lo _ => Z.leb 0 lo) then true
        else lin_testB bc (fst l2 + ghi - fst l1 - k1lo)%Z ts (fun _ hi => Z.leb hi 0))
    then (if lin_nowrapRB bc b1 then lin_nowrapRB bc gkb else false) else false
  else false.

Lemma hull_apart_member : forall bc b1 k1lo k1hi gkb glo ghi k1 n1 k2 n2,
  hull_apart bc b1 k1lo k1hi gkb glo ghi = true ->
  (k1lo <= k1)%Z -> (k1 + n1 <= k1hi)%Z -> (glo <= k2)%Z -> (k2 + n2 <= ghi)%Z ->
  shares_var b1 gkb = true /\ lin_apart0BF bc b1 k1 n1 gkb k2 n2 = true.
Proof.
  intros bc b1 k1lo k1hi gkb glo ghi k1 n1 k2 n2 H H1 H2 H3 H4. unfold hull_apart in H.
  destruct (shares_var b1 gkb); [|discriminate]. split; [reflexivity|]. cbv zeta in H.
  unfold lin_apart0BF. cbv zeta.
  match type of H with (if ?X then ?Y else false) = true => destruct X eqn:EX; [|discriminate]; rewrite H end.
  match goal with |- (if ?T then true else false) = true => assert (E : T = true); [|rewrite E; reflexivity] end.
  destruct (lin_testB bc (fst (lin_of gkb) + glo - fst (lin_of b1) - k1hi)%Z (lsub_e (snd (lin_of gkb)) (snd (lin_of b1))) (fun lo _ => Z.leb 0 lo)) eqn:EA.
  - replace (fst (lin_of gkb) + k2 - fst (lin_of b1) - k1)%Z
      with ((fst (lin_of gkb) + glo - fst (lin_of b1) - k1hi) + ((k2 - glo) + (k1hi - k1)))%Z by lia.
    apply (lin_testB_mono bc _ _ _ (fun lo _ => Z.leb 0 lo)); [|exact EA].
    intros lo hi Hlo. apply Z.leb_le in Hlo. apply Bool.orb_true_iff. left. apply Z.leb_le. lia.
  - replace (fst (lin_of gkb) + k2 - fst (lin_of b1) - k1)%Z
      with ((fst (lin_of gkb) + ghi - fst (lin_of b1) - k1lo) + (- ((ghi - k2) + (k1 - k1lo))))%Z by lia.
    apply (lin_testB_mono bc _ _ _ (fun _ hi => Z.leb hi 0)); [|exact EX].
    intros lo hi Hhi. apply Z.leb_le in Hhi. apply Bool.orb_true_iff. right. apply Z.leb_le. lia.
Qed.

(* [comment removed for export] *)
Lemma prune1pcK_keep_linapart : forall bc sp wa w wv K kb kk m br2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  shares_var (a_base wa) kb = true ->
  lin_apart0BF bc (a_base wa) (a_off wa) (zlit64 (Z.of_nat w)) kb kk m = true ->
  prune1pcK bc sp wa w wv K false br2 = PKeep.
Proof.
  intros bc sp wa w wv K kb kk m br2 HB HD HSV HL.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
    try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
    unfold prune1pcK; cbn [a_base a_off]; unfold ranges_apart_pcBF; cbn [elen]; rewrite ?zlit64_idem; rewrite HSV, HL;
    repeat match goal with |- context [if ?c then true else true] => replace (if c then true else true) with true by (destruct c; reflexivity) end;
    cbn; reflexivity.
Qed.

(* [comment removed for export] *)
Definition sx_hull (sxs : list stx) (bid : positive) : option (Z * Z) :=
  fold_right (fun sx acc =>
                if Pos.eqb (sx_bid sx) bid then
                  let lo := a_off (sx_a sx) in let hi := (lo + sx_m1 sx)%Z in
                  match acc with Some (l, h) => Some (Z.min l lo, Z.max h hi) | None => Some (lo, hi) end
                else acc) None sxs.
Lemma sx_hull_In : forall sxs sx, In sx sxs ->
  exists l h, sx_hull sxs (sx_bid sx) = Some (l, h) /\ (l <= a_off (sx_a sx))%Z /\ (a_off (sx_a sx) + sx_m1 sx <= h)%Z.
Proof.
  induction sxs as [|s rest IH]; intros sx HIn; [destruct HIn|]. cbn [sx_hull fold_right]. fold (sx_hull rest (sx_bid sx)).
  destruct HIn as [->|HIn].
  - rewrite Pos.eqb_refl. destruct (sx_hull rest (sx_bid sx)) as [[l h]|]; eexists; eexists; (split; [reflexivity|]); lia.
  - destruct (IH sx HIn) as (l & h & E & A & B). rewrite E.
    destruct (Pos.eqb (sx_bid s) (sx_bid sx)); eexists; eexists; (split; [reflexivity|]); lia.
Qed.
(* [comment removed for export] *)
Definition sx_base (sxs : list stx) (bid : positive) : option expr :=
  match List.find (fun sx => Pos.eqb (sx_bid sx) bid) sxs with Some sx => Some (a_base (sx_a sx)) | None => None end.
Lemma sx_base_same : forall bc t sxs sx b1,
  NTI bc t -> Forall (SX_OK bc t) sxs -> In sx sxs -> sx_base sxs (sx_bid sx) = Some b1 -> b1 = a_base (sx_a sx).
Proof.
  intros bc t sxs sx b1 HT HS HIn H. unfold sx_base in H.
  destruct (List.find (fun sx0 => Pos.eqb (sx_bid sx0) (sx_bid sx)) sxs) as [s|] eqn:F; [|discriminate]. injection H as <-.
  apply find_some in F as [FIn Fe].
  pose proof (proj1 (Forall_forall _ _) HS s FIn) as (S1 & _). pose proof (proj1 (Forall_forall _ _) HS sx HIn) as (S2 & _).
  pose proof (nt_same_eq _ _ _ _ _ _ HT S1 S2) as E. rewrite Fe in E. symmetry in E. apply p_expr_eqb_eq in E. exact E.
Qed.

(* [comment removed for export] *)
Fixpoint bids_of (vd : stx -> bool) (sxs : list stx) (acc : list positive) : list positive :=
  match sxs with
  | [] => acc
  | sx :: rest => bids_of vd rest (if vd sx then acc else if pmem (sx_bid sx) acc then acc else sx_bid sx :: acc)
  end.
Definition apart_bids (bc : bctx) (vd : stx -> bool) (g : gval) (sxs : list stx) : list positive :=
  match g with
  | (gb, gkb, _, (glo, ghi)) =>
      List.filter (fun bid => if Pos.eqb gb bid then false else
                              match sx_base sxs bid, sx_hull sxs bid with
                              | Some b1, Some (l, h) => hull_apart bc b1 l h gkb glo ghi
                              | _, _ => false
                              end) (bids_of vd sxs [])
  end.

(* [comment removed for export] *)
Fixpoint mk_flV (vd : stx -> bool) (sxs : list stx) : list (stx * list stx) :=
  match sxs with
  | [] => []
  | sx :: rest => if vd sx then mk_flV vd rest else (sx, rest) :: mk_flV vd rest
  end.
Lemma chainKFV_eq : forall bc vd sxs K okb same_of br2,
  (forall sx, In sx sxs -> vd sx = true ->
     prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 = PKeep) ->
  chainKF bc (mk_flV vd sxs) K okb same_of br2 = chainK2 bc sxs K okb same_of br2.
Proof.
  intros bc vd sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 Hf; [reflexivity|].
  cbn [mk_flV chainK2].
  assert (IH' : chainKF bc (mk_flV vd rest) K okb same_of br2 = chainK2 bc rest K okb same_of br2)
    by (apply IH; intros; apply Hf; [right|]; assumption).
  destruct (vd sx) eqn:Hv.
  - rewrite (Hf sx (or_introl eq_refl) Hv). exact IH'.
  - cbn [chainKF]. destruct (prune1pcK _ _ _ _ _ K _ br2); [exact IH'|reflexivity].
Qed.

(* [comment removed for export] *)
Definition vd12 (cg ab : list positive) (g : gval) (sx : stx) : bool :=
  if verdict2R cg sx g then true else pmem (sx_bid sx) ab.
Definition mk_gl3 (bc : bctx) (bnds : gtab) (sxs : list stx) : ptree gfl :=
  pt_map (fun g =>
            let cg := if forallb (fun sx => verdict sx g) sxs then [] else cg_of2 bc g in
            let ab := apart_bids bc (fun sx => verdict2R cg sx g) g sxs in
            (g, mk_flV (vd12 cg ab g) sxs)) bnds.

Lemma entriesG3_eq : forall fk sxs bnds kn infos t1,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) sxs -> Forall2 (EINF (mkbc fk) t1) kn infos ->
  entriesG (mkbc fk) sxs (mk_gl3 (mkbc fk) bnds sxs) kn infos = chainRo fk (map strip sxs) kn.
Proof.
  intros fk sxs bnds kn infos t1 HT HS HF. induction HF as [|K oi rest irest HK HF IH].
  - cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
  - cbn [entriesG]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app, IH. f_equal.
    rewrite <- (chain_slow_eq fk sxs [K] (Forall_SX_sp _ _ _ HS)).
    pose proof (Forall_SX_sp _ _ _ HS) as HSP.
    destruct oi as [ei|]; cbn [EINF] in HK.
    + destruct HK as (HD & HIn & Hbr).
      assert (FULL : forall okb, okb = kbase K ->
        chainK2 (mkbc fk) sxs K okb
          (match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end)
          (match okb with Some _ => ei_br ei | None => None end) = chain_slow (mkbc fk) sxs [K]).
      { intros okb Hokb. apply chainK2_eq; [exact HSP|exact Hokb|].
        destruct okb as [kb|]; [|reflexivity].
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & _ & _)]; [|cbn in Hokb; discriminate].
        rewrite <- Hokb in HB. injection HB as ->.
        split; [exact Hbr|]. exact (Forall_SX_same _ _ _ _ _ HT HIn HS). }
      unfold mk_gl3. rewrite pt_get_map.
      destruct (pt_get bnds (ei_gid ei)) as [g|]; [|apply FULL; reflexivity].
      destruct (inb g ei) eqn:Hinb; [|apply FULL; reflexivity].
      rewrite <- (FULL (kbase K) eq_refl). cbv zeta. apply chainKFV_eq.
      intros sx Hsx Hv.
      assert (Hm : exists m, ei_m ei = Some m).
      { unfold inb in Hinb. destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]. }
      destruct Hm as [m Hm].
      pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp & SXps).
      rewrite Hm in HD.
      unfold vd12 in Hv.
      match type of Hv with (if verdict2R ?CG sx g then true else _) = true => set (cg := CG) in *; destruct (verdict2R cg sx g) eqn:Hv12 end.
      { (* [comment removed for export] *)
        unfold verdict2R in Hv12. destruct (verdict sx g) eqn:Hv1.
        { destruct (verdict_inb_num _ _ _ _ Hv1 Hinb Hm) as (Hne & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
          destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
          * rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_based; [exact HB|exact HD|exact Hsp| | exact Hnum].
            rewrite <- Hbr. exact Hbr2.
          * cbn [kbase]. rewrite Hkb, Hk in *.
            eapply prune1pcK_keep_img; [exact HD| |exact Hsp| rewrite <- Hbr; exact Hbr2 | exact Hnum].
            rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne. }
        assert (Hv2 : verdict_disjR (cg_of2 (mkbc fk) g) sx g = true).
        { subst cg. destruct (forallb (fun sx0 => verdict sx0 g) sxs); [|exact Hv12].
          exfalso. unfold verdict_disjR in Hv12. destruct g as [[[b gkb] obr] hull]. destruct (Pos.eqb b (sx_bid sx)); discriminate. }
        destruct (verdict_disjR2_inb _ _ _ _ _ _ (mkbc_rt fk) (proj1 (Forall_forall _ _) HS sx Hsx) Hv2 Hinb Hm (kdescr_m_nonneg _ _ _ _ HD))
          as [Hne HSD].
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
        * rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_sides; [exact HB|exact HD|exact HSD].
        * cbn [kbase]. rewrite Hkb, Hk in *.
          eapply prune1pcK_keep_img_sides; [exact HD| |exact HSD].
          rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne. }
      (* [comment removed for export] *)
      apply pmem_In in Hv. destruct g as [[[gb gkb] obr] [glo ghi]]. unfold apart_bids in Hv.
      apply filter_In in Hv as [_ Hc].
      destruct (Pos.eqb gb (sx_bid sx)) eqn:Hgb; [discriminate|].
      destruct (sx_base sxs (sx_bid sx)) as [b1|] eqn:Hb1; [|discriminate].
      destruct (sx_hull sxs (sx_bid sx)) as [[l h]|] eqn:Hh; [|discriminate].
      pose proof (sx_base_same _ _ _ _ _ HT HS Hsx Hb1) as ->.
      destruct (sx_hull_In sxs sx Hsx) as (l' & h' & Hh' & Hl & Hhh). rewrite Hh in Hh'. injection Hh' as <- <-.
      unfold inb in Hinb. rewrite Hm in Hinb.
      apply andb_prop in Hinb as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [Hi H2]. apply andb_prop in Hi as [H1 H1'].
      apply Pos.eqb_eq in H1. subst gb. apply Z.leb_le in H3. apply Z.leb_le in H4. apply p_expr_eqb_eq in H1'. subst gkb.
      destruct (hull_apart_member _ _ _ _ _ _ _ (a_off (sx_a sx)) (sx_m1 sx) (ei_k ei) m Hc Hl Hhh H3 H4) as [HSV HLA].
      destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
      * rewrite HB. rewrite Hgb. eapply prune1pcK_keep_linapart; [exact HB | exact HD | exact HSV | exact HLA].
      * exfalso. rewrite Hkb in HSV. clear - HSV. destruct (a_base (sx_a sx)); cbn in HSV; discriminate.
    + apply chainK2_eq; [exact HSP| symmetry; apply kdescr_None_kbase; exact HK | reflexivity].
Qed.

Definition carryG3 (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxs bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_part bc sxs ++ entriesG bc sxs (mk_gl3 bc (gs_bnds gs) sxs) kn infos.
Lemma carryG3_eq : forall log kn,
  carryG3 (mkbc (facts_of kn)) log kn = SPRo (facts_of kn) (rev log) ++ chainRo (facts_of kn) (rev log) kn.
Proof.
  intros log kn. unfold carryG3.
  destruct (mk_stxs (mkbc (facts_of kn)) log nt_empty) as [sxs t0] eqn:E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & Hmap & _).
  destruct (scan_entries (mkbc (facts_of kn)) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
  assert (HS1 : Forall (SX_OK (mkbc (facts_of kn)) t1) sxs).
  { apply Forall_impl with (P := SX_OK (mkbc (facts_of kn)) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
  rewrite (stores_part_eq _ _ _ HT0 HS0), (entriesG3_eq _ _ _ _ _ _ HT1 HS1 HF), Hmap. reflexivity.
Qed.
Definition carryK3 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryG3 bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryK3_eq : forall log kn hints,
  carryK3 (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. unfold carryK3. destruct log as [|s older]; [reflexivity|].
  destruct hints as [|h hs]; [|apply carryB_eq].
  rewrite carry_vertical, carryG3_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Record ldig : Type := LD { ld_sv : bool; ld_nw : bool; ld_c0 : Z; ld_plain : option (Z * Z); ld_rel : option (Z * Z) }.
Definition mk_ldig (bc : bctx) (b1 b2 : expr) : ldig :=
  if shares_var b1 b2 then
    let l1 := lin_of b1 in let l2 := lin_of b2 in
    let ts := lsub_e (snd l2) (snd l1) in
    LD true (if lin_nowrapRB bc b1 then lin_nowrapRB bc b2 else false) (fst l2 - fst l1)%Z
       (lin_range (erangeB bc) 0%Z ts)
       (match bc_fs bc with
        | [] => None
        | fs => match sum_subst fs ts 0 0 false with
                | (ts', (lo0, hi0), true) =>
                    match lin_range (erangeB bc) 0%Z ts' with Some (lo, hi) => Some ((lo + lo0)%Z, (hi + hi0)%Z) | None => None end
                | _ => None
                end
        end)
  else LD false false 0%Z None None.
Definition dig_test (n1 n2 c : Z) (r : option (Z * Z)) : bool :=
  match r with Some (lo, hi) => (Z.leb n1 (lo + c) || Z.leb (hi + c) (- n2))%bool | None => false end.
Definition dig_apart (d : ldig) (k1 n1 k2 n2 : Z) : bool :=
  if ld_sv d then
    let c := (ld_c0 d + k2 - k1)%Z in
    if (if dig_test n1 n2 c (ld_plain d) then true else dig_test n1 n2 c (ld_rel d)) then ld_nw d else false
  else false.

Lemma dig_apart_eq : forall bc b1 b2 k1 n1 k2 n2,
  dig_apart (mk_ldig bc b1 b2) k1 n1 k2 n2 = (if shares_var b1 b2 then lin_apart0BF bc b1 k1 n1 b2 k2 n2 else false).
Proof.
  intros bc b1 b2 k1 n1 k2 n2. unfold dig_apart, mk_ldig. destruct (shares_var b1 b2); [|reflexivity].
  cbn [ld_sv ld_nw ld_c0 ld_plain ld_rel]. unfold lin_apart0BF. cbv zeta.
  set (ts := lsub_e (snd (lin_of b2)) (snd (lin_of b1))).
  set (c := (fst (lin_of b2) - fst (lin_of b1) + k2 - k1)%Z).
  replace (fst (lin_of b2) + k2 - fst (lin_of b1) - k1)%Z with (0 + c)%Z by (subst c; lia).
  assert (E : (if dig_test n1 n2 c (lin_range (erangeB bc) 0%Z ts) then true
               else dig_test n1 n2 c
                      (match bc_fs bc with
                       | [] => None
                       | f :: fs => match sum_subst (f :: fs) ts 0 0 false with
                               | (ts', (lo0, hi0), true) =>
                                   match lin_range (erangeB bc) 0%Z ts' with Some (lo, hi) => Some ((lo + lo0)%Z, (hi + hi0)%Z) | None => None end
                               | _ => None
                               end
                       end))
              = lin_testB bc (0 + c)%Z ts (fun lo hi => (Z.leb n1 lo || Z.leb hi (- n2))%bool)).
  { unfold lin_testB, lin_test_relB. rewrite lin_range_shift.
    assert (R : dig_test n1 n2 c
                      (match bc_fs bc with
                       | [] => None
                       | f :: fs => match sum_subst (f :: fs) ts 0 0 false with
                               | (ts', (lo0, hi0), true) =>
                                   match lin_range (erangeB bc) 0%Z ts' with Some (lo, hi) => Some ((lo + lo0)%Z, (hi + hi0)%Z) | None => None end
                               | _ => None
                               end
                       end)
                = match bc_fs bc with
                  | [] => false
                  | f :: fs => match sum_subst (f :: fs) ts 0 0 false with
                          | (ts', (lo0, hi0), true) =>
                              match lin_range (erangeB bc) (0 + c)%Z ts' with
                              | Some (lo, hi) => (Z.leb n1 (lo + lo0) || Z.leb (hi + hi0) (- n2))%bool
                              | None => false
                              end
                          | _ => false
                          end
                  end).
    { destruct (bc_fs bc) as [|f fs]; [reflexivity|].
      destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|reflexivity].
      rewrite lin_range_shift. destruct (lin_range (erangeB bc) 0%Z ts') as [[lo hi]|]; [|reflexivity].
      unfold dig_test. replace (lo + lo0 + c)%Z with (lo + c + lo0)%Z by lia. replace (hi + hi0 + c)%Z with (hi + c + hi0)%Z by lia. reflexivity. }
    rewrite R. destruct (lin_range (erangeB bc) 0%Z ts) as [[lo hi]|]; reflexivity. }
  destruct (bc_fs bc) as [|f fs] eqn:EF.
  - rewrite <- E. reflexivity.
  - rewrite <- E. reflexivity.
Qed.

(* [comment removed for export] *)
Definition hull_apart_dig (d : ldig) (k1lo k1hi glo ghi : Z) : bool :=
  if ld_sv d then
    let ta (r : option (Z * Z)) := match r with Some (lo, _) => Z.leb 0 (lo + (ld_c0 d + glo - k1hi)) | None => false end in
    let tb (r : option (Z * Z)) := match r with Some (_, hi) => Z.leb (hi + (ld_c0 d + ghi - k1lo)) 0 | None => false end in
    if (if (if ta (ld_plain d) then true else ta (ld_rel d)) then true else (if tb (ld_plain d) then true else tb (ld_rel d)))
    then ld_nw d else false
  else false.
Lemma lin_testB_dig : forall bc c ts (T : Z -> Z -> bool),
  lin_testB bc (0 + c)%Z ts T =
  (if match lin_range (erangeB bc) 0%Z ts with Some (lo, hi) => T (lo + c)%Z (hi + c)%Z | None => false end then true
   else match (match bc_fs bc with
               | [] => None
               | fs => match sum_subst fs ts 0 0 false with
                       | (ts', (lo0, hi0), true) =>
                           match lin_range (erangeB bc) 0%Z ts' with Some (lo, hi) => Some ((lo + lo0)%Z, (hi + hi0)%Z) | None => None end
                       | _ => None
                       end
               end) with Some (lo, hi) => T (lo + c)%Z (hi + c)%Z | None => false end).
Proof.
  intros bc c ts T. unfold lin_testB, lin_test_relB. rewrite lin_range_shift.
  assert (R : match bc_fs bc with
              | [] => false
              | f :: fs => match sum_subst (f :: fs) ts 0 0 false with
                      | (ts', (lo0, hi0), true) =>
                          match lin_range (erangeB bc) (0 + c)%Z ts' with Some (lo, hi) => T (lo + lo0)%Z (hi + hi0)%Z | None => false end
                      | _ => false
                      end
              end
              = match (match bc_fs bc with
               | [] => None
               | f :: fs => match sum_subst (f :: fs) ts 0 0 false with
                       | (ts', (lo0, hi0), true) =>
                           match lin_range (erangeB bc) 0%Z ts' with Some (lo, hi) => Some ((lo + lo0)%Z, (hi + hi0)%Z) | None => None end
                       | _ => None
                       end
               end) with Some (lo, hi) => T (lo + c)%Z (hi + c)%Z | None => false end).
  { destruct (bc_fs bc) as [|f fs]; [reflexivity|].
    destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] [|]]; [|reflexivity].
    rewrite lin_range_shift. destruct (lin_range (erangeB bc) 0%Z ts') as [[lo hi]|]; [|reflexivity].
    replace (lo + lo0 + c)%Z with (lo + c + lo0)%Z by lia. replace (hi + hi0 + c)%Z with (hi + c + hi0)%Z by lia. reflexivity. }
  destruct (bc_fs bc) as [|f fs] eqn:EF.
  - destruct (lin_range (erangeB bc) 0%Z ts) as [[lo hi]|]; [destruct (T (lo + c)%Z (hi + c)%Z)|]; reflexivity.
  - rewrite R. destruct (lin_range (erangeB bc) 0%Z ts) as [[lo hi]|]; reflexivity.
Qed.
Lemma hull_apart_dig_eq : forall bc b1 k1lo k1hi gkb glo ghi,
  hull_apart_dig (mk_ldig bc b1 gkb) k1lo k1hi glo ghi = hull_apart bc b1 k1lo k1hi gkb glo ghi.
Proof.
  intros bc b1 k1lo k1hi gkb glo ghi. unfold hull_apart_dig, hull_apart, mk_ldig. destruct (shares_var b1 gkb); [|reflexivity].
  cbn [ld_sv ld_nw ld_c0 ld_plain ld_rel]. cbv zeta.
  set (ts := lsub_e (snd (lin_of gkb)) (snd (lin_of b1))).
  replace (fst (lin_of gkb) + glo - fst (lin_of b1) - k1hi)%Z with (0 + (fst (lin_of gkb) - fst (lin_of b1) + glo - k1hi))%Z by lia.
  replace (fst (lin_of gkb) + ghi - fst (lin_of b1) - k1lo)%Z with (0 + (fst (lin_of gkb) - fst (lin_of b1) + ghi - k1lo))%Z by lia.
  rewrite !lin_testB_dig.
  destruct (lin_range (erangeB bc) 0%Z ts) as [[lo hi]|];
    destruct (match bc_fs bc with [] => None | f :: fs => _ end) as [[lo' hi']|]; reflexivity.
Qed.

(* [comment removed for export] *)
Definition visitD (bc : bctx) (sx : stx) (od : option ldig) (K : kentry) (kk m : Z) (same : bool) (br2 : option (Z * Z)) : pk_res :=
  match od with
  | Some d => if (if same then false else dig_apart d (a_off (sx_a sx)) (sx_m1 sx) kk m) then PKeep
              else prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2
  | None => prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2
  end.
Lemma visitD_eq : forall bc sx od K kb kk m same br2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  (forall d, od = Some d -> d = mk_ldig bc (a_base (sx_a sx)) kb) ->
  visitD bc sx od K kk m same br2 = prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K same br2.
Proof.
  intros bc sx od K kb kk m same br2 HB HD Hd. unfold visitD. destruct od as [d|]; [|reflexivity].
  destruct same; [reflexivity|]. rewrite (Hd d eq_refl), dig_apart_eq.
  destruct (shares_var (a_base (sx_a sx)) kb) eqn:SV; [|reflexivity].
  destruct (lin_apart0BF bc (a_base (sx_a sx)) (a_off (sx_a sx)) (sx_m1 sx) kb kk m) eqn:LA; [|reflexivity].
  symmetry. eapply prune1pcK_keep_linapart; [exact HB | exact HD | exact SV | exact LA].
Qed.

(* [comment removed for export] *)
Fixpoint chainKFD (bc : bctx) (fl : list (stx * list stx)) (dgf : stx -> option ldig) (K : kentry) (kk m : Z) (okb : option expr)
         (same_of : positive -> bool) (br2 : option (Z * Z)) : list kentry :=
  match fl with
  | [] => [K]
  | (sx, rest) :: fl' =>
      match visitD bc sx (match okb with Some _ => dgf sx | None => None end) K kk m (same_of (sx_bid sx)) br2 with
      | PKeep => chainKFD bc fl' dgf K kk m okb same_of br2
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 else chain_slow bc rest [K']
                                  | None => chain_slow bc rest [K']
                                  end) l
          | None => chain_slow bc rest l
          end
      end
  end.

(* [comment removed for export] *)
Lemma chainK2_skip : forall fk sx rest K okb same_of br2,
  okb = kbase K ->
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) rest ->
  match okb with
  | Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) rest
  | None => br2 = None
  end ->
  pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2) = [K] ->
  chainK2 (mkbc fk) (sx :: rest) K okb same_of br2 = chainK2 (mkbc fk) rest K okb same_of br2.
Proof.
  intros fk sx rest K okb same_of br2 Hokb HS HK HP. cbn [chainK2].
  destruct (prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2) as [|l]; [reflexivity|].
  cbn [pk_list] in HP. subst l. destruct okb as [kb|].
  - cbn [flat_map]. rewrite <- Hokb. rewrite p_expr_eqb_refl. apply app_nil_r.
  - symmetry. apply chainK2_eq; [exact HS | exact Hokb | exact HK].
Qed.

Lemma chainKFDV_eq : forall fk vd dgf sxs K kk m okb same_of br2,
  okb = kbase K ->
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
  match okb with
  | Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) sxs
  | None => br2 = None
  end ->
  (forall kb, okb = Some kb -> kdescr K = Some (kb, kk, Some m)
                               /\ forall sx d, In sx sxs -> dgf sx = Some d -> d = mk_ldig (mkbc fk) (a_base (sx_a sx)) kb) ->
  (forall sx, In sx sxs -> vd sx = true ->
     pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2) = [K]) ->
  chainKFD (mkbc fk) (mk_flV vd sxs) dgf K kk m okb same_of br2 = chainK2 (mkbc fk) sxs K okb same_of br2.
Proof.
  intros fk vd dgf sxs. induction sxs as [|sx rest IH]; intros K kk m okb same_of br2 Hokb HS HK HDG Hvd; [reflexivity|].
  apply Forall_cons_iff in HS as [HS1 HS].
  assert (HK' : match okb with
                | Some kb => br2 = base_rangeB (mkbc fk) kb /\ Forall (fun sx => same_of (sx_bid sx) = expr_eqb kb (a_base (sx_a sx))) rest
                | None => br2 = None
                end).
  { destruct okb as [kb|]; [|exact HK]. destruct HK as [Hbr HF]. apply Forall_cons_iff in HF as [_ HF]. exact (conj Hbr HF). }
  assert (IH' : chainKFD (mkbc fk) (mk_flV vd rest) dgf K kk m okb same_of br2 = chainK2 (mkbc fk) rest K okb same_of br2).
  { apply IH; [exact Hokb | exact HS | exact HK' | | intros s Hs; apply Hvd; right; exact Hs].
    intros kb Hkb. destruct (HDG kb Hkb) as [A B]. split; [exact A|]. intros s d Hs. apply B. right. exact Hs. }
  cbn [mk_flV]. destruct (vd sx) eqn:Hv.
  - rewrite IH'. symmetry. apply chainK2_skip; [exact Hokb | exact HS | exact HK' | apply Hvd; [left; reflexivity | exact Hv]].
  - cbn [chainKFD chainK2].
    assert (EV : visitD (mkbc fk) sx (match okb with Some _ => dgf sx | None => None end) K kk m (same_of (sx_bid sx)) br2
                 = prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2).
    { destruct okb as [kb|]; [|reflexivity]. destruct (HDG kb eq_refl) as [A B].
      eapply visitD_eq; [symmetry; exact Hokb | exact A |]. intros d Hd. apply (B sx d); [left; reflexivity | exact Hd]. }
    rewrite EV. destruct (prune1pcK _ _ _ _ _ K _ br2); [exact IH' | reflexivity].
Qed.

(* [comment removed for export] *)
Definition kwf (K : kentry) : bool :=
  match K with
  | KWord _ w' _ => Z.ltb (Z.of_nat w') two64
  | KZero _ (ELit l0) | KUnk _ (ELit l0) | KFill _ (ELit l0) _ => if Z.ltb 0 l0 then Z.ltb l0 two64 else false
  | KImg lo hi => Z.ltb lo hi
  | _ => true
  end.
Lemma zlit64_small : forall z, (0 <= z < 2 ^ 64)%Z -> zlit64 z = z.
Proof.
  intros z Hz. unfold zlit64, two64. replace (Z.leb 0 z && Z.ltb z (2 ^ 64))%bool with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma zlit64_mod : forall z, zlit64 z = (z mod 2 ^ 64)%Z.
Proof.
  intros z. unfold zlit64, two64. destruct (Z.leb 0 z && Z.ltb z (2 ^ 64))%bool eqn:E; [|reflexivity].
  apply andb_prop in E as [A B]. apply Z.leb_le in A. apply Z.ltb_lt in B. symmetry. apply Z.mod_small. lia.
Qed.
Lemma ktrim_outside : forall mk kb kk l0 k w,
  (0 < l0 < 2 ^ 64)%Z -> (kk + l0 <= k \/ k + Z.of_nat w <= kk)%Z -> ktrim mk kb kk l0 k w = [mk (SA kb kk) (ELit l0)].
Proof.
  intros mk kb kk l0 k w Hl Ho. unfold ktrim. rewrite (Z.mod_small l0) by lia. cbv zeta.
  destruct Ho as [Ho|Ho].
  - replace (Z.min k (kk + l0)) with (kk + l0)%Z by lia.
    replace (Z.ltb kk (kk + l0)) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (Z.ltb (Z.max kk (k + Z.of_nat w)) (kk + l0)) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (kk + l0 - kk)%Z with l0 by lia. reflexivity.
  - replace (Z.ltb kk (Z.min k (kk + l0))) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (Z.max kk (k + Z.of_nat w)) with kk by lia.
    replace (Z.ltb kk (kk + l0)) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (kk + l0 - kk)%Z with l0 by lia. reflexivity.
Qed.

Lemma prune1pcK_same_outside : forall bc sp wa w wv K kb kk m same br2 glo ghi,
  kdescr K = Some (kb, kk, Some m) -> kwf K = true ->
  (match kbase K with Some _ => same = true | None => a_base wa = ELit 0%Z end) ->
  (glo <= kk)%Z -> (kk + m <= ghi)%Z -> (a_off wa + Z.of_nat w <= glo \/ ghi <= a_off wa)%Z ->
  pk_list K (prune1pcK bc sp wa w wv K same br2) = [K].
Proof.
  intros bc sp wa w wv K kb kk m same br2 glo ghi HD HW HSm H1 H2 Ho.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kdescr] in HD; try discriminate; cbn [kbase] in HSm; cbn [kwf] in HW.
  - (* [comment removed for export] *) injection HD as <- <- <-. subst same. apply Z.ltb_lt in HW. unfold two64 in HW.
    rewrite zlit64_small in H2 by lia. unfold prune1pcK.
    replace (Z.leb (k + Z.of_nat w') (a_off wa) || Z.leb (a_off wa + Z.of_nat w) k)%bool with true; [reflexivity|].
    symmetry. apply Bool.orb_true_iff. destruct Ho as [Ho|Ho]; [right | left]; apply Z.leb_le; lia.
  - (* [comment removed for export] *) destruct len as [l0| | | | | | |]; try discriminate. injection HD as <- <- <-. subst same.
    destruct (Z.ltb 0 l0) eqn:A; [|discriminate]. apply Z.ltb_lt in A, HW. unfold two64 in HW. rewrite zlit64_small in H2 by lia.
    unfold prune1pcK. cbn [pk_list]. apply ktrim_outside; lia.
  - (* [comment removed for export] *) destruct len as [l0| | | | | | |]; try discriminate. injection HD as <- <- <-. subst same.
    rewrite zlit64_mod in H2. unfold prune1pcK. cbv zeta.
    replace (Z.leb (k + l0 mod 2 ^ 64) (a_off wa) || Z.leb (a_off wa + Z.of_nat w) k)%bool with true; [reflexivity|].
    symmetry. apply Bool.orb_true_iff. destruct Ho as [Ho|Ho]; [right | left]; apply Z.leb_le; lia.
  - (* [comment removed for export] *) destruct (Z.ltb (hi - lo) (2 ^ 64)) eqn:B; [|discriminate]. injection HD as <- <- <-.
    apply Z.ltb_lt in HW, B. rewrite zlit64_small in H2 by lia.
    unfold prune1pcK. rewrite HSm. cbn [pk_list]. cbv zeta.
    destruct Ho as [Ho|Ho].
    + replace (Z.ltb lo (Z.min (a_off wa) hi)) with false by (symmetry; apply Z.ltb_ge; lia).
      replace (Z.max lo (a_off wa + Z.of_nat w)) with lo by lia.
      replace (Z.ltb lo hi) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    + replace (Z.min (a_off wa) hi) with hi by lia.
      replace (Z.ltb lo hi) with true by (symmetry; apply Z.ltb_lt; lia).
      replace (Z.ltb (Z.max lo (a_off wa + Z.of_nat w)) hi) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - (* [comment removed for export] *) destruct len as [l0| | | | | | |]; try discriminate. injection HD as <- <- <-. subst same.
    destruct (Z.ltb 0 l0) eqn:A; [|discriminate]. apply Z.ltb_lt in A, HW. unfold two64 in HW. rewrite zlit64_small in H2 by lia.
    unfold prune1pcK. cbn [pk_list]. apply (ktrim_outside (fun a n => KFill a n fc)); lia.
  - (* [comment removed for export] *) destruct len as [l0| | | | | | |]; try discriminate. injection HD as <- <- <-. subst same.
    destruct (Z.ltb 0 l0) eqn:A; [|discriminate]. apply Z.ltb_lt in A, HW. unfold two64 in HW. rewrite zlit64_small in H2 by lia.
    unfold prune1pcK. cbn [pk_list]. apply ktrim_outside; lia.
Qed.

(* [comment removed for export] *)
Definition klen (K : kentry) : option expr :=
  match K with KZero _ l | KUnk _ l | KFill _ l _ | KBlob _ l _ => Some l | _ => None end.
Definition vd_sym (sx : stx) (bid : positive) (br2 : option (Z * Z)) (kk : Z) (h2 : option Z) : bool :=
  if Pos.eqb bid (sx_bid sx) then false else
  match sp_rng (sx_sp sx), br2, sp_h1 (sx_sp sx), h2 with
  | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2' =>
      (Z.leb (hi1 + a_off (sx_a sx) + h1) (lo2 + kk) || Z.leb (hi2 + kk + h2') (lo1 + a_off (sx_a sx)))%bool
  | _, _, _, _ => false
  end.
Lemma prune1pcK_keep_symnum : forall bc sx K kb kk len bid br2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, None) -> klen K = Some len ->
  vd_sym sx bid br2 kk (xhiB bc len) = true ->
  prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K false br2 = PKeep.
Proof.
  intros bc sx K kb kk len bid br2 HB HD HL Hv. unfold vd_sym in Hv.
  destruct (Pos.eqb bid (sx_bid sx)); [discriminate|].
  destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|] eqn:E1; [|discriminate].
  destruct br2 as [[lo2 hi2]|]; [|discriminate].
  destruct (sp_h1 (sx_sp sx)) as [h1|] eqn:E3; [|discriminate].
  destruct (xhiB bc len) as [h2|] eqn:E4; [|discriminate].
  destruct K as [[b k] w' v|[b k] l|[b k] l bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] l fc|[b k] l];
    cbn [kbase kdescr klen] in HB, HD, HL; try discriminate; injection HB as ->; injection HL as ->;
    (destruct len as [z| | | | | | |]; [discriminate| | | | | | |]); injection HD as <-;
    unfold prune1pcK; cbn [a_base a_off]; unfold ranges_apart_pcBF; cbn [elen]; rewrite E1, E3, E4, Hv; reflexivity.
Qed.

(* [comment removed for export] *)
Definition gfl4 : Type := (gval * list (stx * list stx) * list (positive * ldig))%type.
Definition dg_lookup (tab : list (positive * ldig)) (sx : stx) : option ldig :=
  match List.find (fun p : positive * ldig => Pos.eqb (fst p) (sx_bid sx)) tab with Some p => Some (snd p) | None => None end.
(* [comment removed for export] *)
Definition vd_cheap (cg : list positive) (g : gval) (sx : stx) : bool :=
  if verdict2R cg sx g then true else
  match g with
  | (gb, _, _, (glo, ghi)) =>
      if Pos.eqb gb (sx_bid sx) then (Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) glo || Z.leb ghi (a_off (sx_a sx)))%bool else false
  end.
Definition mk_tab (bc : bctx) (g : gval) (sxs : list stx) (bids : list positive) : list (positive * ldig) :=
  match g with
  | (gb, gkb, _, _) =>
      flat_map (fun bid => if Pos.eqb gb bid then [] else
                           match sx_base sxs bid with
                           | Some b1 => let d := mk_ldig bc b1 gkb in if ld_sv d then [(bid, d)] else []
                           | None => []
                           end) bids
  end.
Definition mk_ab (g : gval) (sxs : list stx) (tab : list (positive * ldig)) : list positive :=
  match g with
  | (_, _, _, (glo, ghi)) =>
      List.map fst (List.filter (fun p : positive * ldig =>
                                   match sx_hull sxs (fst p) with Some (l, h) => hull_apart_dig (snd p) l h glo ghi | None => false end) tab)
  end.
Definition mk_g4 (bc : bctx) (sxs : list stx) (g : gval) : gfl4 :=
  let cg := if forallb (fun sx => verdict sx g) sxs then [] else cg_of2 bc g in
  let tab := mk_tab bc g sxs (bids_of (vd_cheap cg g) sxs []) in
  let ab := mk_ab g sxs tab in
  (g, mk_flV (fun sx => if vd_cheap cg g sx then true else pmem (sx_bid sx) ab) sxs, tab).
Definition mk_gl4 (bc : bctx) (bnds : gtab) (sxs : list stx) : ptree gfl4 := pt_map (mk_g4 bc sxs) bnds.

Lemma mk_tab_In : forall bc gb gkb obr hull sxs bids bid d,
  In (bid, d) (mk_tab bc (gb, gkb, obr, hull) sxs bids) ->
  Pos.eqb gb bid = false /\ exists b1, sx_base sxs bid = Some b1 /\ d = mk_ldig bc b1 gkb.
Proof.
  intros bc gb gkb obr hull sxs bids bid d H. unfold mk_tab in H. apply in_flat_map in H as [bid' [_ H]].
  destruct (Pos.eqb gb bid') eqn:E; [destruct H|].
  destruct (sx_base sxs bid') as [b1|] eqn:EB; [|destruct H]. cbv zeta in H.
  destruct (ld_sv (mk_ldig bc b1 gkb)); [|destruct H]. destruct H as [H|[]]. injection H as -> <-.
  split; [exact E|]. exists b1. split; [exact EB | reflexivity].
Qed.

Fixpoint entriesG4 (bc : bctx) (sxs : list stx) (gl : ptree gfl4) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           let okb := kbase K in
           let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
           let br2 := match okb with Some _ => ei_br ei | None => None end in
           match ei_m ei with
           | Some m =>
               match pt_get gl (ei_gid ei) with
               | Some (g, fl, tab) =>
                   if (if inb g ei then kwf K else false) then chainKFD bc fl (dg_lookup tab) K (ei_k ei) m okb same_of br2
                   else chainK2 bc sxs K okb same_of br2
               | None => chainK2 bc sxs K okb same_of br2
               end
           | None =>
               match okb, klen K with
               | Some _, Some len =>
                   let h2 := xhiB bc len in
                   chainKF bc (mk_flV (fun sx => vd_sym sx (ei_bid ei) br2 (ei_k ei) h2) sxs) K okb same_of br2
               | _, _ => chainK2 bc sxs K okb same_of br2
               end
           end
       | None => chainK2 bc sxs K None (fun _ => false) None
       end) ++ entriesG4 bc sxs gl rest irest
  | _, _ => []
  end.

Lemma entriesG4_eq : forall fk sxs bnds kn infos t1,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) sxs -> Forall2 (EINF (mkbc fk) t1) kn infos ->
  entriesG4 (mkbc fk) sxs (mk_gl4 (mkbc fk) bnds sxs) kn infos = chainRo fk (map strip sxs) kn.
Proof.
  intros fk sxs bnds kn infos t1 HT HS HF. induction HF as [|K oi rest irest HK HF IH].
  - cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
  - cbn [entriesG4]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app, IH. f_equal.
    rewrite <- (chain_slow_eq fk sxs [K] (Forall_SX_sp _ _ _ HS)).
    pose proof (Forall_SX_sp _ _ _ HS) as HSP.
    destruct oi as [ei|]; cbn [EINF] in HK.
    2:{ apply chainK2_eq; [exact HSP| symmetry; apply kdescr_None_kbase; exact HK | reflexivity]. }
    destruct HK as (HD & HIn & Hbr).
    (* [comment removed for export] *)
    assert (HKK : match kbase K with
                  | Some kb => (match kbase K with Some _ => ei_br ei | None => None end) = base_rangeB (mkbc fk) kb
                               /\ Forall (fun sx => (match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end) (sx_bid sx)
                                                    = expr_eqb kb (a_base (sx_a sx))) sxs
                  | None => (match kbase K with Some _ => ei_br ei | None => None end) = None
                  end).
    { destruct (kbase K) as [kb|] eqn:HB0; [|reflexivity].
      destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & _ & _)]; [|cbn in HB0; discriminate].
      rewrite HB0 in HB. injection HB as ->. split; [exact Hbr|]. exact (Forall_SX_same _ _ _ _ _ HT HIn HS). }
    assert (FULL : chainK2 (mkbc fk) sxs K (kbase K)
          (match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end)
          (match kbase K with Some _ => ei_br ei | None => None end) = chain_slow (mkbc fk) sxs [K]).
    { apply chainK2_eq; [exact HSP | reflexivity | exact HKK]. }
    cbv zeta.
    destruct (ei_m ei) as [m|] eqn:Hm.
    + (* [comment removed for export] *)
      unfold mk_gl4. rewrite pt_get_map.
      destruct (pt_get bnds (ei_gid ei)) as [g|]; [|exact FULL]. unfold mk_g4. cbv zeta.
      destruct (inb g ei) eqn:Hinb; [|exact FULL]. destruct (kwf K) eqn:HW; [|exact FULL].
      rewrite <- FULL.
      set (cg := if forallb (fun sx => verdict sx g) sxs then [] else cg_of2 (mkbc fk) g).
      set (tab := mk_tab (mkbc fk) g sxs (bids_of (vd_cheap cg g) sxs [])).
      destruct g as [[[gb gkb] obr] [glo ghi]].
      pose proof Hinb as Hinb0. unfold inb in Hinb0. rewrite Hm in Hinb0.
      apply andb_prop in Hinb0 as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [Hi H2]. apply andb_prop in Hi as [H1 H1'].
      apply Pos.eqb_eq in H1. apply Z.leb_le in H3. apply Z.leb_le in H4. apply p_expr_eqb_eq in H1'.
      apply chainKFDV_eq; [reflexivity | exact HSP | exact HKK | |].
      * (* [comment removed for export] *)
        intros kb Hkb. destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & _ & _)]; [|cbn in Hkb; discriminate].
        rewrite Hkb in HB. injection HB as ->. split; [exact HD|].
        intros sx d Hsx Hd. unfold dg_lookup in Hd.
        destruct (List.find (fun p : positive * ldig => Pos.eqb (fst p) (sx_bid sx)) tab) as [[bid' d']|] eqn:F; [|discriminate].
        injection Hd as <-. apply find_some in F as [FIn Fe]. cbn [fst] in Fe. apply Pos.eqb_eq in Fe. subst bid'.
        unfold tab in FIn. destruct (mk_tab_In _ _ _ _ _ _ _ _ _ FIn) as (_ & b1 & Hb1 & ->).
        rewrite (sx_base_same _ _ _ _ _ HT HS Hsx Hb1). rewrite H1'. reflexivity.
      * (* [comment removed for export] *)
        intros sx Hsx Hv.
        pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp & SXps).
        destruct (vd_cheap cg (gb, gkb, obr, (glo, ghi)) sx) eqn:Hvc.
        { unfold vd_cheap in Hvc. destruct (verdict2R cg sx (gb, gkb, obr, (glo, ghi))) eqn:Hv12.
          { (* [comment removed for export] *)
            match goal with |- pk_list K ?X = _ => assert (EP : X = PKeep); [|rewrite EP; reflexivity] end.
            unfold verdict2R in Hv12. destruct (verdict sx (gb, gkb, obr, (glo, ghi))) eqn:Hv1.
            { destruct (verdict_inb_num _ _ _ _ Hv1 Hinb Hm) as (Hne & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
              destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
              * rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_based; [exact HB|exact HD|exact Hsp| | exact Hnum].
                rewrite <- Hbr. exact Hbr2.
              * cbn [kbase]. rewrite Hkb, Hk in *.
                eapply prune1pcK_keep_img; [exact HD| |exact Hsp| rewrite <- Hbr; exact Hbr2 | exact Hnum].
                rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne. }
            assert (Hv2 : verdict_disjR (cg_of2 (mkbc fk) (gb, gkb, obr, (glo, ghi))) sx (gb, gkb, obr, (glo, ghi)) = true).
            { subst cg. destruct (forallb (fun sx0 => verdict sx0 (gb, gkb, obr, (glo, ghi))) sxs); [|exact Hv12].
              exfalso. unfold verdict_disjR in Hv12. destruct (Pos.eqb gb (sx_bid sx)); discriminate. }
            destruct (verdict_disjR2_inb _ _ _ _ _ _ (mkbc_rt fk) (proj1 (Forall_forall _ _) HS sx Hsx) Hv2 Hinb Hm (kdescr_m_nonneg _ _ _ _ HD))
              as [Hne HSD].
            destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
            * rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_sides; [exact HB|exact HD|exact HSD].
            * cbn [kbase]. rewrite Hkb, Hk in *.
              eapply prune1pcK_keep_img_sides; [exact HD| |exact HSD].
              rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne. }
          (* [comment removed for export] *)
          destruct (Pos.eqb gb (sx_bid sx)) eqn:Hgb; [|discriminate].
          apply Bool.orb_true_iff in Hvc.
          eapply (prune1pcK_same_outside _ _ _ _ _ K (ei_kb ei) (ei_k ei) m _ _ glo ghi); [exact HD | exact HW | | exact H3 | exact H4 |].
          - destruct (kbase K) as [kb|] eqn:HB0.
            + rewrite <- H1. exact Hgb.
            + destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & EK & Hkb & Hk)]; [rewrite HB in HB0; discriminate|].
              pose proof (nt_same_eq _ _ _ _ _ _ HT HIn SXin) as E. rewrite <- H1, Hgb, Hkb in E. symmetry in E.
              apply p_expr_eqb_eq in E. symmetry. exact E.
          - destruct Hvc as [A|A]; apply Z.leb_le in A; [left | right]; lia. }
        (* [comment removed for export] *)
        match goal with |- pk_list K ?X = _ => assert (EP : X = PKeep); [|rewrite EP; reflexivity] end.
        apply pmem_In in Hv. unfold mk_ab in Hv. apply in_map_iff in Hv as [[bid d] [Eb Hf]]. cbn [fst] in Eb. subst bid.
        apply filter_In in Hf as [Htab Hc]. cbn [fst snd] in Hc.
        unfold tab in Htab. destruct (mk_tab_In _ _ _ _ _ _ _ _ _ Htab) as (Hgb & b1 & Hb1 & ->).
        destruct (sx_hull sxs (sx_bid sx)) as [[l h]|] eqn:Hh; [|discriminate].
        rewrite hull_apart_dig_eq in Hc.
        pose proof (sx_base_same _ _ _ _ _ HT HS Hsx Hb1) as ->.
        destruct (sx_hull_In sxs sx Hsx) as (l' & h' & Hh' & Hl & Hhh). rewrite Hh in Hh'. injection Hh' as <- <-.
        subst gb gkb.
        destruct (hull_apart_member _ _ _ _ _ _ _ (a_off (sx_a sx)) (sx_m1 sx) (ei_k ei) m Hc Hl Hhh H3 H4) as [HSV HLA].
        destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
        -- rewrite HB. rewrite Hgb. eapply prune1pcK_keep_linapart; [exact HB | exact HD | exact HSV | exact HLA].
        -- exfalso. rewrite Hkb in HSV. clear - HSV. destruct (a_base (sx_a sx)); cbn in HSV; discriminate.
    + (* [comment removed for export] *)
      destruct (kbase K) as [kb|] eqn:HB0; [|exact FULL].
      destruct (klen K) as [len|] eqn:HL; [|exact FULL].
      rewrite <- FULL. apply chainKFV_eq.
      intros sx Hsx Hv.
      assert (Hne : Pos.eqb (ei_bid ei) (sx_bid sx) = false).
      { unfold vd_sym in Hv. destruct (Pos.eqb (ei_bid ei) (sx_bid sx)); [discriminate | reflexivity]. }
      rewrite Hne.
      destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & _ & _)]; [|cbn in HB0; discriminate].
      rewrite HB0 in HB. injection HB as ->.
      eapply prune1pcK_keep_symnum; [exact HB0 | exact HD | exact HL | exact Hv].
Qed.

Definition carryG4 (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxs bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_part bc sxs ++ entriesG4 bc sxs (mk_gl4 bc (gs_bnds gs) sxs) kn infos.
Lemma carryG4_eq : forall log kn,
  carryG4 (mkbc (facts_of kn)) log kn = SPRo (facts_of kn) (rev log) ++ chainRo (facts_of kn) (rev log) kn.
Proof.
  intros log kn. unfold carryG4.
  destruct (mk_stxs (mkbc (facts_of kn)) log nt_empty) as [sxs t0] eqn:E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & Hmap & _).
  destruct (scan_entries (mkbc (facts_of kn)) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
  assert (HS1 : Forall (SX_OK (mkbc (facts_of kn)) t1) sxs).
  { apply Forall_impl with (P := SX_OK (mkbc (facts_of kn)) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
  rewrite (stores_part_eq _ _ _ HT0 HS0), (entriesG4_eq _ _ _ _ _ _ HT1 HS1 HF), Hmap. reflexivity.
Qed.
(* [comment removed for export] *)
Definition carryK4 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryG4 bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryK4_eq : forall log kn hints,
  carryK4 (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. unfold carryK4. destruct log as [|s older]; [reflexivity|].
  destruct hints as [|h hs]; [|apply carryB_eq].
  rewrite carry_vertical, carryG4_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Definition hv_num (sp : sprep) (uk : Z) (g : gval) : bool :=
  match g with
  | (_, _, obr, (glo, ghi)) =>
      match sp_rng sp, obr, sp_h1 sp with
      | Some (lo1, hi1), Some (lo2, hi2), Some h1 => (Z.leb (hi1 + uk + h1) (lo2 + glo) || Z.leb (hi2 + ghi) (lo1 + uk))%bool
      | _, _, _ => false
      end
  end.
Definition hv_sides (bc : bctx) (sp : sprep) (g : gval) : bool :=
  match g with
  | (_, gkb, _, (glo, ghi)) => existsb (fun cm : saddr * expr => hull_in bc gkb glo ghi (fst cm) (snd cm)) (sp_Dx sp)
  end.
Definition hv (bc : bctx) (sp : sprep) (uk : Z) (g : gval) : bool := if hv_num sp uk g then true else hv_sides bc sp g.

Lemma in_sides_xB_In : forall bc D b k z c ml,
  In (c, ml) D -> sub_itvB bc b k (zlit64 z) c ml = true -> in_sides_xB bc D b k (ELit z) = true.
Proof.
  intros bc D b k z c ml. induction D as [|[c' ml'] D IH]; intros HIn HS; [destruct HIn|].
  cbn [in_sides_xB]. unfold sub_itv_xB at 1. destruct HIn as [E|HIn].
  - injection E as -> ->. rewrite HS. reflexivity.
  - rewrite (IH HIn HS). destruct (sub_itvB bc b k (zlit64 z) c' ml'); reflexivity.
Qed.

Lemma hv_member : forall bc ub uk un g ei z,
  hv bc (mk_sprepB bc ub uk un) uk g = true -> inb g ei = true -> ei_m ei = Some (zlit64 z) ->
  ei_br ei = base_rangeB bc (ei_kb ei) ->
  ranges_apart_pBF bc (mk_sprepB bc ub uk un) ub uk un (ei_kb ei) (ei_k ei) (ELit z) = true.
Proof.
  intros bc ub uk un [[[gb gkb] obr] [glo ghi]] ei z Hv Hinb Hm Hbr.
  unfold inb in Hinb. rewrite Hm in Hinb.
  apply andb_prop in Hinb as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [Hi H2]. apply andb_prop in Hi as [H1 H1'].
  apply Z.leb_le in H3. apply Z.leb_le in H4. apply p_expr_eqb_eq in H1'. subst gkb.
  assert (Hobr : obr = base_rangeB bc (ei_kb ei)).
  { rewrite <- Hbr. destruct obr as [[a b]|], (ei_br ei) as [[a' b']|]; cbn [obr_eqb] in H2; try discriminate; [|reflexivity].
    apply andb_prop in H2 as [X Y]. apply Z.eqb_eq in X. apply Z.eqb_eq in Y. subst. reflexivity. }
  pose proof (zlit64_nonneg z) as Hz0.
  unfold hv in Hv. destruct (hv_num (mk_sprepB bc ub uk un) uk (gb, ei_kb ei, obr, (glo, ghi))) eqn:Hn.
  - (* [comment removed for export] *)
    unfold hv_num in Hn. rewrite Hobr in Hn.
    destruct (sp_rng (mk_sprepB bc ub uk un)) as [[lo1 hi1]|] eqn:E1; [|discriminate].
    destruct (base_rangeB bc (ei_kb ei)) as [[lo2 hi2]|] eqn:E2; [|discriminate].
    destruct (sp_h1 (mk_sprepB bc ub uk un)) as [h1|] eqn:E3; [|discriminate].
    assert (NUM : (Z.leb (hi1 + uk + h1) (lo2 + ei_k ei) || Z.leb (hi2 + ei_k ei + zlit64 z) (lo1 + uk))%bool = true).
    { apply Bool.orb_true_iff in Hn. apply Bool.orb_true_iff. destruct Hn as [A|A]; apply Z.leb_le in A; [left|right]; apply Z.leb_le; lia. }
    unfold ranges_apart_pBF. rewrite E1, E2.
    destruct un as [z1| | | | | | |];
      try (rewrite E3; cbn [xhiB]; rewrite NUM; reflexivity).
    (* [comment removed for export] *)
    assert (E3' : h1 = zlit64 z1) by (unfold mk_sprepB in E3; cbn [sp_h1 xhiB] in E3; injection E3 as <-; reflexivity).
    subst h1. rewrite NUM. reflexivity.
  - (* [comment removed for export] *)
    unfold hv_sides in Hv. apply existsb_exists in Hv as [[c ml] [HIn Hc]]. cbn [fst snd] in Hc.
    pose proof (hull_in_member bc (ei_kb ei) glo ghi c ml (ei_k ei) (zlit64 z) Hc H3 H4 Hz0) as HS.
    unfold ranges_apart_pBF.
    destruct un as [z1| | | | | | |].
    + (* [comment removed for export] *)
      assert (ED : sp_D (mk_sprepB bc ub uk (ELit z1)) = sp_Dx (mk_sprepB bc ub uk (ELit z1))) by reflexivity.
      rewrite ED. rewrite (in_sidesB_In _ _ _ _ _ c ml HIn HS).
      repeat match goal with |- context [if ?c then true else true] => replace (if c then true else true) with true by (destruct c; reflexivity) end.
      match goal with |- (if ?c then true else true) = true => destruct c; reflexivity | |- _ => reflexivity end.
    + rewrite (in_sides_xB_In _ _ _ _ _ c ml HIn HS). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
    + rewrite (in_sides_xB_In _ _ _ _ _ c ml HIn HS). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
    + rewrite (in_sides_xB_In _ _ _ _ _ c ml HIn HS). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
    + rewrite (in_sides_xB_In _ _ _ _ _ c ml HIn HS). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
    + rewrite (in_sides_xB_In _ _ _ _ _ c ml HIn HS). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
    + rewrite (in_sides_xB_In _ _ _ _ _ c ml HIn HS). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
    + rewrite (in_sides_xB_In _ _ _ _ _ c ml HIn HS). match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
Qed.

(* [comment removed for export] *)
Definition sub_itvBQ (bc : bctx) (qp : qprep) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
        match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
      else false)
  then true
  else if (Z.leb 0 n && Z.ltb n two64)%bool then xinsideBQ bc qp b k (ELit n) (a_base c) (a_off c) m else false.
Lemma sub_itvBQ_eq : forall bc b k n c m, sub_itvBQ bc (mkqp bc b (ELit n)) b k n c m = sub_itvB bc b k n c m.
Proof. intros. unfold sub_itvBQ, sub_itvB. rewrite xinsideBQ_eq. reflexivity. Qed.
Definition regsQ (bc : bctx) (b : expr) (k n : Z) : list positive :=
  let qp := mkqp bc b (ELit n) in
  List.map fst (List.filter (fun t : positive * (saddr * expr) => sub_itvBQ bc qp b k n (fst (snd t)) (snd (snd t))) (rt_sides (bc_rt bc))).
Lemma regsQ_eq : forall bc b k n, regsQ bc b k n = regs bc b k n.
Proof.
  intros. unfold regsQ, regs. f_equal. apply filter_ext. intros t. apply sub_itvBQ_eq.
Qed.

Definition dcache : Type := list (expr * (option (Z * Z) * ldig)).
Fixpoint dc_find (dc : dcache) (kb : expr) : option (option (Z * Z) * ldig) :=
  match dc with
  | [] => None
  | (b, v) :: rest => if expr_eqb kb b then Some v else dc_find rest kb
  end.
Definition DCOK (bc : bctx) (rb : expr) (dc : dcache) : Prop :=
  Forall (fun e : expr * (option (Z * Z) * ldig) => snd e = (base_rangeB bc (fst e), mk_ldig bc rb (fst e))) dc.
Lemma dc_find_ok : forall bc rb dc kb v, DCOK bc rb dc -> dc_find dc kb = Some v -> v = (base_rangeB bc kb, mk_ldig bc rb kb).
Proof.
  intros bc rb dc kb v H. induction dc as [|[b v'] rest IH]; cbn [dc_find]; [discriminate|].
  apply Forall_cons_iff in H as [H1 H]. cbn [fst snd] in H1.
  destruct (expr_eqb kb b) eqn:E; [|exact (IH H)].
  intros X. injection X as <-. apply p_expr_eqb_eq in E. subst b. exact H1.
Qed.
(* [comment removed for export] *)
Definition ranges_apartQD (bc : bctx) (r1 : option (Z * Z)) (RQ RS : list positive) (v : option (Z * Z) * ldig)
           (k1 n1 k2 n2 : Z) : bool :=
  if (match r1, fst v with
      | Some (lo1, hi1), Some (lo2, hi2) =>
          (Z.leb (hi1 + k1 + n1) (lo2 + k2) || Z.leb (hi2 + k2 + n2) (lo1 + k1))%bool
      | _, _ => false
      end) then true
  else if kdisj_apartR bc RQ RS then true
  else dig_apart (snd v) k1 n1 k2 n2.
Lemma ranges_apartQD_eq : forall bc r1 RQ RS b1 k1 n1 b2 k2 n2,
  ranges_apartQD bc r1 RQ RS (base_rangeB bc b2, mk_ldig bc b1 b2) k1 n1 k2 n2 = ranges_apartQR bc r1 RQ RS b1 k1 n1 b2 k2 n2.
Proof. intros. unfold ranges_apartQD, ranges_apartQR, lin_apartB. cbn [fst snd]. rewrite dig_apart_eq. reflexivity. Qed.

Fixpoint log_lookupQD (bc : bctx) (log : list sentry) (lrs : list (list positive)) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) (q : option (option (Z * Z) * list positive)) (dc : dcache) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      let lrs' := match lrs with _ :: t => t | [] => [] end in
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupQD bc rest lrs' rb rk n sx hints acc q dc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let q' := match q with Some x => x | None => (base_rangeB bc rb, regsQ bc rb rk (Z.of_nat n)) end in
          let rs := match lrs with r :: _ => r | [] => regs bc kb kk (Z.of_nat w) end in
          let '(dv, dc') := match dc_find dc kb with
                            | Some x => (x, dc)
                            | None => let x := (base_rangeB bc kb, mk_ldig bc rb kb) in (x, (kb, x) :: dc)
                            end in
          if ranges_apartQD bc (fst q') (snd q') rs dv rk (Z.of_nat n) kk (Z.of_nat w)
          then log_lookupQD bc rest lrs' rb rk n sx hints acc (Some q') dc'
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupQD bc rest lrs' rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) (Some q') dc'
          end
      end
  end.
Lemma log_lookupQD_eq : forall bc log lrs rb rk n sx hints acc q dc,
  DCOK bc rb dc ->
  (q = None \/ q = Some (base_rangeB bc rb, regs bc rb rk (Z.of_nat n))) ->
  log_lookupQD bc log lrs rb rk n sx hints acc q dc = log_lookupQL bc log lrs rb rk n sx hints acc q.
Proof.
  intros bc log. induction log as [|[[kb kk] w v] rest IH]; intros lrs rb rk n sx hints acc q dc HD Q; [reflexivity|].
  cbn [log_lookupQD log_lookupQL].
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity.
  - apply IH; assumption.
  - assert (EQ : (match q with Some x => x | None => (base_rangeB bc rb, regsQ bc rb rk (Z.of_nat n)) end)
                 = (match q with Some x => x | None => (base_rangeB bc rb, regs bc rb rk (Z.of_nat n)) end))
      by (rewrite regsQ_eq; reflexivity).
    rewrite EQ. clear EQ.
    set (q' := match q with Some x => x | None => (base_rangeB bc rb, regs bc rb rk (Z.of_nat n)) end).
    assert (Q' : Some q' = None \/ Some q' = Some (base_rangeB bc rb, regs bc rb rk (Z.of_nat n))).
    { right. subst q'. destruct Q as [-> | ->]; reflexivity. }
    destruct (dc_find dc kb) as [x|] eqn:F.
    + rewrite (dc_find_ok _ _ _ _ _ HD F). rewrite ranges_apartQD_eq.
      destruct (ranges_apartQR bc (fst q') (snd q') _ rb rk (Z.of_nat n) kb kk (Z.of_nat w)); [apply IH; assumption|].
      destruct hints as [|[|] hs]; [| | reflexivity]; apply IH; assumption.
    + rewrite ranges_apartQD_eq.
      assert (HD' : DCOK bc rb ((kb, (base_rangeB bc kb, mk_ldig bc rb kb)) :: dc)) by (constructor; [reflexivity | exact HD]).
      destruct (ranges_apartQR bc (fst q') (snd q') _ rb rk (Z.of_nat n) kb kk (Z.of_nat w)); [apply IH; assumption|].
      destruct hints as [|[|] hs]; [| | reflexivity]; apply IH; assumption.
Qed.

(* [comment removed for export] *)
Fixpoint wr_syn (bc : bctx) (kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
          then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
          else false)
      then true
      else wr_syn bc rest a n
  | _ :: rest => wr_syn bc rest a n
  end.
Lemma wr_syn_covered : forall bc kn a n, wr_syn bc kn a n = true -> wr_coveredB bc kn a n = true.
Proof.
  intros bc kn a n. induction kn as [|K rest IH]; [discriminate|].
  destruct K as [? ? ?|? ?|? ? ?|? ?|? ?|? ? ?|[kb kk] len|? ? ? ?|? ? ?|? ?]; cbn [wr_syn wr_coveredB]; try exact IH.
  destruct (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
            then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end else false); [reflexivity|].
  intros H. rewrite (IH H). destruct (xinsideB bc (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len); reflexivity.
Qed.
Definition wr_covered2 (bc : bctx) (kn : list kentry) (a : saddr) (n : nat) : bool :=
  if wr_syn bc kn a n then true else wr_coveredB bc kn a n.
Lemma wr_covered2_eq : forall bc kn a n, wr_covered2 bc kn a n = wr_coveredB bc kn a n.
Proof. intros. unfold wr_covered2. destruct (wr_syn bc kn a n) eqn:E; [symmetry; apply wr_syn_covered; exact E | reflexivity]. Qed.
Definition storeok_scB2 (bc : bctx) (a : saddr) (n : nat) : list sidecond :=
  if wr_covered2 bc (bc_fk bc) a n then [] else [SCStoreOk a n].
Lemma storeok_scB2_eqf : forall bc, storeok_scB2 bc = storeok_scB bc.
Proof. intros bc. apply functional_extensionality; intros a. apply functional_extensionality; intros n. unfold storeok_scB2, storeok_scB. rewrite wr_covered2_eq. reflexivity. Qed.

(* [comment removed for export] *)
Definition sym_readBI2 (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (lrs : list (list positive)) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupQD bc (s_log ss) lrs (a_base a) (a_off a) n sx' (sc_hints scr) [] None [] with   (* [comment removed for export] *)
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.
Lemma sym_readBI2_eqf : forall segs ss bc kx lrs, sym_readBI2 segs ss bc kx lrs = sym_readBI segs ss bc kx lrs.
Proof.
  intros. apply functional_extensionality; intros scr. apply functional_extensionality; intros a.
  apply functional_extensionality; intros n. apply functional_extensionality; intros sx'.
  unfold sym_readBI2, sym_readBI. rewrite log_lookupQD_eq; [reflexivity | constructor | left; reflexivity].
Qed.

Definition sym_stepBI2 (bc : bctx) (kx : kix) (lrs : list (list positive)) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branchB bc c a b with
            | Some t => Some t
            | None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
                      | Some t => Some t
                      | None => enum_branchB bc c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      match sym_readBI2 segs ss bc kx lrs scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bv_signed imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_scB bc a n ++ storeok_scB2 bc a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readBI2 segs ss bc kx lrs scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_scB bc a n ++ storeok_scB2 bc a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_readBI2 segs ss bc kx lrs scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scB2 bc a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.

Lemma sym_stepBI2_eq : forall bc kx lrs segs i ss scr, sym_stepBI2 bc kx lrs segs i ss scr = sym_stepBI bc kx lrs segs i ss scr.
Proof. intros. unfold sym_stepBI2, sym_stepBI. rewrite sym_readBI2_eqf, storeok_scB2_eqf. reflexivity. Qed.

Definition regsEQ (bc : bctx) (e : sentry) : list positive :=
  match e with SE (SA kb kk) w _ => regsQ bc kb kk (Z.of_nat w) end.
Lemma regsEQ_eq : forall bc e, regsEQ bc e = regsE bc e.
Proof. intros bc [[kb kk] w v]. unfold regsEQ, regsE. apply regsQ_eq. Qed.
Definition lrs_step2 (bc : bctx) (ss ss' : sym_state) (lrs : list (list positive)) : list (list positive) :=
  if Nat.eqb (length (s_log ss')) (length (s_log ss)) then lrs
  else match s_log ss' with e :: _ => regsEQ bc e :: lrs | [] => lrs end.
Lemma lrs_step2_eq : forall bc ss ss' lrs, lrs_step2 bc ss ss' lrs = lrs_step bc ss ss' lrs.
Proof. intros. unfold lrs_step2, lrs_step. destruct (Nat.eqb _ _); [reflexivity|]. destruct (s_log ss'); [reflexivity|]. rewrite regsEQ_eq. reflexivity. Qed.

Section Exec2.
Variable segs : list Segment.
Definition sym_stepXBI2 (bc : bctx) (kx : kix) (lrs : list (list positive)) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepBI2 bc kx lrs segs i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')
      then SOk (cap_rd K i ss') (x_filterB segs bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.
Lemma sym_stepXBI2_eq : forall bc kx lrs K i ss scr, sym_stepXBI2 bc kx lrs K i ss scr = sym_stepXBI segs bc kx lrs K i ss scr.
Proof. intros. unfold sym_stepXBI2, sym_stepXBI. rewrite sym_stepBI2_eq. reflexivity. Qed.
Fixpoint sym_execTXBI2_go (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
         (lrs : list (list positive)) : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXBI2 bc kx lrs K i ss scr_nil with
          | SOk ss' [] _ => sym_execTXBI2_go bc kx t K f false stops ss' (if s_clean ss' then ss' else ck) (lrs_step2 bc ss ss' lrs)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Lemma sym_execTXBI2_go_eq : forall bc kx t K fuel first stops ss ck lrs,
  sym_execTXBI2_go bc kx t K fuel first stops ss ck lrs = sym_execTXBI_go segs bc kx t K fuel first stops ss ck lrs.
Proof.
  intros bc kx t K fuel. induction fuel as [|f IH]; intros first stops ss ck lrs; [reflexivity|].
  cbn [sym_execTXBI2_go sym_execTXBI_go].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite sym_stepXBI2_eq. destruct (sym_stepXBI segs bc kx lrs K i ss scr_nil) as [ss' scs scr'|]; [|reflexivity].
  destruct scs; [|reflexivity]. rewrite lrs_step2_eq. apply IH.
Qed.
Definition sym_execTXBI2 (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTXBI2_go bc kx t K fuel first stops (clr ss) (clr ss) (List.map (regsE bc) (s_log ss)).
Lemma sym_execTXBI2_eq : forall bc kx t K fuel first stops ss,
  sym_execTXBI2 bc kx t K fuel first stops ss = sym_execTXBI segs bc kx t K fuel first stops ss.
Proof. intros. unfold sym_execTXBI2, sym_execTXBI. apply sym_execTXBI2_go_eq. Qed.
End Exec2.

(* [comment removed for export] *)
Fixpoint mk_stxs2 (bc : bctx) (log : list sentry) (t : ntab) : list stx * ntab :=
  match log with
  | [] => ([], t)
  | SE a w v :: older =>
      let '(sxs, t1) := mk_stxs2 bc older t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let RS := regsQ bc (a_base a) (a_off a) (zlit64 (Z.of_nat w)) in
      (sxs ++ [STX a w v (mk_sprepR bc RS (a_base a) w) bid (bi_br bi) (partners_of (bc_rt bc) RS)], t2)
  end.
Lemma mk_stxs2_eq : forall bc log t, mk_stxs2 bc log t = mk_stxs bc log t.
Proof.
  intros bc log. induction log as [|[a w v] older IH]; intros t; [reflexivity|].
  cbn [mk_stxs2 mk_stxs]. rewrite IH. rewrite regsQ_eq. reflexivity.
Qed.
Definition carryG5 (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxs2 bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_part bc sxs ++ entriesG4 bc sxs (mk_gl4 bc (gs_bnds gs) sxs) kn infos.
Lemma carryG5_eq : forall bc log kn, carryG5 bc log kn = carryG4 bc log kn.
Proof. intros. unfold carryG5, carryG4. rewrite mk_stxs2_eq. reflexivity. Qed.
Definition carryK5 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryG5 bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryK5_eq : forall log kn hints,
  carryK5 (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. rewrite <- carryK4_eq. unfold carryK5, carryK4.
  destruct log; [reflexivity|]. destruct hints; [|reflexivity]. rewrite carryG5_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Definition bhtab : Type := list (positive * (option (Z * Z) * option (Z * Z))).   (* [comment removed for export] *)
Definition sx_rng (sxs : list stx) (bid : positive) : option (Z * Z) :=
  match List.find (fun sx => Pos.eqb (sx_bid sx) bid) sxs with Some sx => sp_rng (sx_sp sx) | None => None end.
Fixpoint bid_list (sxs : list stx) (acc : list positive) : list positive :=
  match sxs with
  | [] => acc
  | sx :: rest => bid_list rest (if pmem (sx_bid sx) acc then acc else sx_bid sx :: acc)
  end.
Definition mk_bh (sxs : list stx) : bhtab := List.map (fun bid => (bid, (sx_rng sxs bid, sx_hull sxs bid))) (bid_list sxs []).
Definition hullnum (g : gval) (bid : positive) (v : option (Z * Z) * option (Z * Z)) : bool :=
  match g with
  | (gb, _, obr, (glo, ghi)) =>
      if Pos.eqb gb bid then false else
      match fst v, obr, snd v with
      | Some (lo1, hi1), Some (lo2, hi2), Some (k1lo, k1hi) => (Z.leb (hi1 + k1hi - lo2) glo || Z.leb ghi (lo1 + k1lo - hi2))%bool
      | _, _, _ => false
      end
  end.
Fixpoint bh_find (bt : list (positive * bool)) (bid : positive) : bool :=
  match bt with
  | [] => false
  | (b, v) :: rest => if Pos.eqb bid b then v else bh_find rest bid
  end.
Definition vnum (bt : list (positive * bool)) (g : gval) (sx : stx) : bool :=
  if bh_find bt (sx_bid sx) then true else verdict sx g.

Lemma sx_rng_same : forall bc t sxs sx,
  NTI bc t -> Forall (SX_OK bc t) sxs -> In sx sxs -> sx_rng sxs (sx_bid sx) = sp_rng (sx_sp sx).
Proof.
  intros bc t sxs sx HT HS HIn. unfold sx_rng.
  destruct (List.find (fun sx0 => Pos.eqb (sx_bid sx0) (sx_bid sx)) sxs) as [s|] eqn:F.
  - apply find_some in F as [FIn Fe].
    pose proof (proj1 (Forall_forall _ _) HS s FIn) as (S1 & _ & P1 & _). pose proof (proj1 (Forall_forall _ _) HS sx HIn) as (S2 & _ & P2 & _).
    pose proof (nt_same_eq _ _ _ _ _ _ HT S1 S2) as E. rewrite Fe in E. symmetry in E. apply p_expr_eqb_eq in E.
    rewrite P1, P2, E. unfold mk_sprepB, elen. reflexivity.
  - exfalso. pose proof (find_none _ _ F sx HIn) as X. cbn beta in X. rewrite Pos.eqb_refl in X. discriminate X.
Qed.
Lemma hullnum_verdict : forall bc t sxs sx g,
  NTI bc t -> Forall (SX_OK bc t) sxs -> In sx sxs ->
  hullnum g (sx_bid sx) (sx_rng sxs (sx_bid sx), sx_hull sxs (sx_bid sx)) = true -> verdict sx g = true.
Proof.
  intros bc t sxs sx [[[gb gkb] obr] [glo ghi]] HT HS HIn H. unfold hullnum in H. cbn [fst snd] in H. unfold verdict.
  destruct (Pos.eqb gb (sx_bid sx)); [discriminate|].
  rewrite (sx_rng_same _ _ _ _ HT HS HIn) in H.
  destruct (sp_rng (sx_sp sx)) as [[lo1 hi1]|]; [|discriminate]. destruct obr as [[lo2 hi2]|]; [|discriminate].
  destruct (sx_hull_In sxs sx HIn) as (l & h & Eh & Hl & Hh). rewrite Eh in H.
  apply Bool.orb_true_iff in H. apply Bool.orb_true_iff. destruct H as [A|A]; apply Z.leb_le in A; [left|right]; apply Z.leb_le; lia.
Qed.
Lemma bh_find_map : forall (f : positive -> bool) l bid, bh_find (List.map (fun b => (b, f b)) l) bid = true -> f bid = true.
Proof.
  intros f l bid. induction l as [|b rest IH]; cbn [List.map bh_find]; [discriminate|].
  destruct (Pos.eqb_spec bid b) as [->|NE]; [intros H; exact H | exact IH].
Qed.

(* [comment removed for export] *)
Definition mk_bt (bh : bhtab) (g : gval) : list (positive * bool) := List.map (fun e => (fst e, hullnum g (fst e) (snd e))) bh.
Lemma vnum_eq : forall bc t sxs g sx,
  NTI bc t -> Forall (SX_OK bc t) sxs -> In sx sxs -> vnum (mk_bt (mk_bh sxs) g) g sx = verdict sx g.
Proof.
  intros bc t sxs g sx HT HS HIn. unfold vnum.
  destruct (bh_find (mk_bt (mk_bh sxs) g) (sx_bid sx)) eqn:F; [|reflexivity].
  symmetry. apply (hullnum_verdict bc t sxs sx g HT HS HIn).
  unfold mk_bt, mk_bh in F. rewrite List.map_map in F. cbn [fst snd] in F.
  exact (bh_find_map (fun bid => hullnum g bid (sx_rng sxs bid, sx_hull sxs bid)) _ _ F).
Qed.

Definition vd_cheap5 (bt : list (positive * bool)) (cg : list positive) (g : gval) (sx : stx) : bool :=
  if (if vnum bt g sx then true else verdict_disjR cg sx g) then true else
  match g with
  | (gb, _, _, (glo, ghi)) =>
      if Pos.eqb gb (sx_bid sx) then (Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) glo || Z.leb ghi (a_off (sx_a sx)))%bool else false
  end.
Definition mk_g5 (bc : bctx) (sxs : list stx) (bh : bhtab) (g : gval) : gfl4 :=
  let bt := mk_bt bh g in
  let cg := if forallb (fun sx => vnum bt g sx) sxs then [] else cg_of2 bc g in
  let tab := mk_tab bc g sxs (bids_of (vd_cheap5 bt cg g) sxs []) in
  let ab := mk_ab g sxs tab in
  (g, mk_flV (fun sx => if vd_cheap5 bt cg g sx then true else pmem (sx_bid sx) ab) sxs, tab).
Definition mk_gl5 (bc : bctx) (bnds : gtab) (sxs : list stx) : ptree gfl4 := let bh := mk_bh sxs in pt_map (mk_g5 bc sxs bh) bnds.

Lemma forallb_ext_in : forall (A : Type) (f g : A -> bool) l, (forall x, In x l -> f x = g x) -> forallb f l = forallb g l.
Proof. intros A f g l. induction l as [|x r IH]; intros H; [reflexivity|]. cbn. rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy. Qed.
Lemma bids_of_ext_in : forall (f g : stx -> bool) l acc, (forall x, In x l -> f x = g x) -> bids_of f l acc = bids_of g l acc.
Proof. intros f g l. induction l as [|x r IH]; intros acc H; [reflexivity|]. cbn [bids_of]. rewrite (H x (or_introl eq_refl)). apply IH. intros y Hy. apply H. right. exact Hy. Qed.
Lemma mk_flV_ext_in : forall (f g : stx -> bool) l, (forall x, In x l -> f x = g x) -> mk_flV f l = mk_flV g l.
Proof. intros f g l. induction l as [|x r IH]; intros H; [reflexivity|]. cbn [mk_flV]. rewrite (H x (or_introl eq_refl)), IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy. Qed.
Lemma pt_map_ext : forall (A B : Type) (f g : A -> B) t, (forall a, f a = g a) -> pt_map f t = pt_map g t.
Proof. intros A B f g t H. induction t as [|l IHl o r IHr]; [reflexivity|]. cbn. rewrite IHl, IHr. destruct o; [rewrite H|]; reflexivity. Qed.

Lemma mk_g5_eq : forall bc t sxs g,
  NTI bc t -> Forall (SX_OK bc t) sxs -> mk_g5 bc sxs (mk_bh sxs) g = mk_g4 bc sxs g.
Proof.
  intros bc t sxs g HT HS. unfold mk_g5, mk_g4. cbv zeta.
  assert (EV : forall sx, In sx sxs -> vnum (mk_bt (mk_bh sxs) g) g sx = verdict sx g) by (intros sx HIn; exact (vnum_eq bc t sxs g sx HT HS HIn)).
  assert (EF : forallb (fun sx => vnum (mk_bt (mk_bh sxs) g) g sx) sxs = forallb (fun sx => verdict sx g) sxs) by (apply forallb_ext_in; exact EV).
  rewrite EF. clear EF.
  set (cg := if forallb (fun sx => verdict sx g) sxs then [] else cg_of2 bc g).
  assert (EC : forall sx, In sx sxs -> vd_cheap5 (mk_bt (mk_bh sxs) g) cg g sx = vd_cheap cg g sx).
  { intros sx HIn. unfold vd_cheap5, vd_cheap, verdict2R. rewrite (EV sx HIn). reflexivity. }
  assert (EB : bids_of (vd_cheap5 (mk_bt (mk_bh sxs) g) cg g) sxs [] = bids_of (vd_cheap cg g) sxs []) by (apply bids_of_ext_in; exact EC).
  rewrite EB. clear EB.
  set (tab := mk_tab bc g sxs (bids_of (vd_cheap cg g) sxs [])).
  f_equal. f_equal. apply mk_flV_ext_in. intros sx HIn. rewrite (EC sx HIn). reflexivity.
Qed.

Lemma mk_gl5_eq : forall bc t sxs bnds, NTI bc t -> Forall (SX_OK bc t) sxs -> mk_gl5 bc bnds sxs = mk_gl4 bc bnds sxs.
Proof. intros bc t sxs bnds HT HS. unfold mk_gl5, mk_gl4. apply pt_map_ext. intros g. exact (mk_g5_eq bc t sxs g HT HS). Qed.

Definition carryG6 (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxs2 bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_part bc sxs ++ entriesG4 bc sxs (mk_gl5 bc (gs_bnds gs) sxs) kn infos.
Lemma carryG6_eq : forall fk log kn, carryG6 (mkbc fk) log kn = carryG5 (mkbc fk) log kn.
Proof.
  intros fk log kn. unfold carryG6, carryG5. rewrite mk_stxs2_eq.
  destruct (mk_stxs (mkbc fk) log nt_empty) as [sxs t0] eqn:E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & _ & _).
  destruct (scan_entries (mkbc fk) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  rewrite (mk_gl5_eq _ _ _ _ HT0 HS0). reflexivity.
Qed.
Definition carryK6 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryG6 bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryK6_eq : forall log kn hints,
  carryK6 (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. rewrite <- carryK5_eq. unfold carryK6, carryK5.
  destruct log; [reflexivity|]. destruct hints; [|reflexivity]. rewrite carryG6_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Definition regs_x (bc : bctx) (b : expr) (k : Z) (n : expr) : list positive :=
  List.map fst (List.filter (fun t : positive * (saddr * expr) => sub_itv_xB bc b k n (fst (snd t)) (snd (snd t))) (rt_sides (bc_rt bc))).
Lemma regs_x_In : forall bc b k n j, In j (regs_x bc b k n) ->
  exists c ml, rt_In (bc_rt bc) j c ml /\ sub_itv_xB bc b k n c ml = true.
Proof.
  intros bc b k n j H. unfold regs_x in H. apply in_map_iff in H as [[j' [c ml]] [E F]]. cbn in E. subst j'.
  apply filter_In in F as [F1 F2]. cbn [fst snd] in F2. exists c, ml. split; [exact F1 | exact F2].
Qed.
Lemma in_sides_xB_In2 : forall bc D b k n c ml,
  In (c, ml) D -> sub_itv_xB bc b k n c ml = true -> in_sides_xB bc D b k n = true.
Proof.
  intros bc D b k n c ml. induction D as [|[c' ml'] D IH]; intros HIn HS; [destruct HIn|].
  cbn [in_sides_xB]. destruct HIn as [E|HIn].
  - injection E as -> ->. rewrite HS. reflexivity.
  - rewrite (IH HIn HS). destruct (sub_itv_xB bc b k n c' ml'); reflexivity.
Qed.
Definition vd_symR (RE : list positive) (sx : stx) (bid : positive) (br2 : option (Z * Z)) (kk : Z) (h2 : option Z) : bool :=
  if vd_sym sx bid br2 kk h2 then true
  else if Pos.eqb bid (sx_bid sx) then false else existsb (fun j => pmem j (sx_ps sx)) RE.
Lemma prune1pcK_keep_symsides : forall bc sx K kb kk len br2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, None) -> klen K = Some len ->
  in_sides_xB bc (sp_Dx (sx_sp sx)) kb kk len = true ->
  prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K false br2 = PKeep.
Proof.
  intros bc sx K kb kk len br2 HB HD HL HS.
  destruct K as [[b k] w' v|[b k] l|[b k] l bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] l fc|[b k] l];
    cbn [kbase kdescr klen] in HB, HD, HL; try discriminate; injection HB as ->; injection HL as ->;
    (destruct len as [z| | | | | | |]; [discriminate| | | | | | |]); injection HD as <-;
    unfold prune1pcK; cbn [a_base a_off]; unfold ranges_apart_pcBF; cbn [elen]; rewrite HS;
    repeat match goal with |- context [if ?c then true else true] => replace (if c then true else true) with true by (destruct c; reflexivity) end;
    cbn; try reflexivity;
    match goal with |- (if ?c then _ else _) = _ => destruct c; reflexivity | |- _ => idtac end.
Qed.

Fixpoint entriesG7 (bc : bctx) (sxs : list stx) (gl : ptree gfl4) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           let okb := kbase K in
           let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
           let br2 := match okb with Some _ => ei_br ei | None => None end in
           match ei_m ei with
           | Some m =>
               match pt_get gl (ei_gid ei) with
               | Some (g, fl, tab) =>
                   if (if inb g ei then kwf K else false) then chainKFD bc fl (dg_lookup tab) K (ei_k ei) m okb same_of br2
                   else chainK2 bc sxs K okb same_of br2
               | None => chainK2 bc sxs K okb same_of br2
               end
           | None =>
               match okb, klen K with
               | Some kb, Some len =>
                   let h2 := xhiB bc len in
                   let RE := regs_x bc kb (ei_k ei) len in       (* [comment removed for export] *)
                   chainKF bc (mk_flV (fun sx => vd_symR RE sx (ei_bid ei) br2 (ei_k ei) h2) sxs) K okb same_of br2
               | _, _ => chainK2 bc sxs K okb same_of br2
               end
           end
       | None => chainK2 bc sxs K None (fun _ => false) None
       end) ++ entriesG7 bc sxs gl rest irest
  | _, _ => []
  end.

Lemma entriesG7_eq : forall fk sxs gl kn infos t1,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) sxs -> Forall2 (EINF (mkbc fk) t1) kn infos ->
  entriesG7 (mkbc fk) sxs gl kn infos = entriesG4 (mkbc fk) sxs gl kn infos.
Proof.
  intros fk sxs gl kn infos t1 HT HS HF. induction HF as [|K oi rest irest HK HF IH]; [reflexivity|].
  cbn [entriesG7 entriesG4]. rewrite IH. f_equal.
  destruct oi as [ei|]; [|reflexivity]. cbn [EINF] in HK. destruct HK as (HD & HIn & Hbr).
  cbv zeta. destruct (ei_m ei) as [m|] eqn:Hm; [reflexivity|].
  destruct (kbase K) as [kb|] eqn:HB0; [|reflexivity]. destruct (klen K) as [len|] eqn:HL; [|reflexivity].
  destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & _ & _)]; [|cbn in HB0; discriminate].
  rewrite HB0 in HB. injection HB as ->.
  pose proof (Forall_SX_sp _ _ _ HS) as HSP.
  (* [comment removed for export] *)
  transitivity (chainK2 (mkbc fk) sxs K (Some (ei_kb ei)) (Pos.eqb (ei_bid ei)) (ei_br ei)).
  - apply chainKFV_eq. intros sx Hsx Hv.
    pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp & SXps).
    unfold vd_symR in Hv. destruct (vd_sym sx (ei_bid ei) (ei_br ei) (ei_k ei) (xhiB (mkbc fk) len)) eqn:Hv1.
    + assert (Hne : Pos.eqb (ei_bid ei) (sx_bid sx) = false) by (unfold vd_sym in Hv1; destruct (Pos.eqb (ei_bid ei) (sx_bid sx)); [discriminate | reflexivity]).
      rewrite Hne. eapply prune1pcK_keep_symnum; [exact HB0 | exact HD | exact HL | exact Hv1].
    + destruct (Pos.eqb (ei_bid ei) (sx_bid sx)) eqn:Hne; [discriminate|].
      apply existsb_exists in Hv as [j [INj Pj]]. apply pmem_In in Pj. rewrite SXps in Pj.
      destruct (regs_x_In _ _ _ _ _ INj) as [c [ml [R COND]]].
      pose proof (partners_of_sides _ _ _ _ _ _ _ (mkbc_rt fk) Pj R) as IND.
      eapply prune1pcK_keep_symsides; [exact HB0 | exact HD | exact HL |].
      rewrite SXsp. unfold mk_sprepB, elen. rewrite disj_sidesBM_fst. cbn [sp_Dx]. fold (zlit64 (Z.of_nat (sx_w sx))).
      exact (in_sides_xB_In2 _ _ _ _ _ c ml IND COND).
  - symmetry. apply chainKFV_eq. intros sx Hsx Hv.
    assert (Hne : Pos.eqb (ei_bid ei) (sx_bid sx) = false) by (unfold vd_sym in Hv; destruct (Pos.eqb (ei_bid ei) (sx_bid sx)); [discriminate | reflexivity]).
    rewrite Hne. eapply prune1pcK_keep_symnum; [exact HB0 | exact HD | exact HL | exact Hv].
Qed.

Definition carryG7 (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxs2 bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_part bc sxs ++ entriesG7 bc sxs (mk_gl5 bc (gs_bnds gs) sxs) kn infos.
Lemma carryG7_eq : forall fk log kn, carryG7 (mkbc fk) log kn = carryG6 (mkbc fk) log kn.
Proof.
  intros fk log kn. unfold carryG7, carryG6.
  destruct (mk_stxs2 (mkbc fk) log nt_empty) as [sxs t0] eqn:E. rewrite mk_stxs2_eq in E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & _ & _).
  destruct (scan_entries (mkbc fk) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
  assert (HS1 : Forall (SX_OK (mkbc fk) t1) sxs).
  { apply Forall_impl with (P := SX_OK (mkbc fk) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
  rewrite (entriesG7_eq _ _ _ _ _ _ HT1 HS1 HF). reflexivity.
Qed.
(* [comment removed for export] *)
Definition carryK7 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryG7 bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryK7_eq : forall log kn hints,
  carryK7 (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. rewrite <- carryK6_eq. unfold carryK7, carryK6.
  destruct log; [reflexivity|]. destruct hints; [|reflexivity]. rewrite carryG7_eq. reflexivity.
Qed.


(* [comment removed for export] *)
Definition vd_sideR (RE : list positive) (bid : positive) (sx : stx) : bool :=
  if Pos.eqb bid (sx_bid sx) then false else existsb (fun j => pmem j (sx_ps sx)) RE.
Definition K13_MIN : nat := 8.
(* [comment removed for export] *)
Definition k13_need (dgf : stx -> option ldig) (bid : positive) (fl : list (stx * list stx)) : nat :=
  length (List.filter (fun p => match dgf (fst p) with Some _ => false | None => negb (Pos.eqb bid (sx_bid (fst p))) end) fl).
Definition fl_sides (bc : bctx) (dgf : stx -> option ldig) (fl : list (stx * list stx)) (kb : expr) (kk m : Z) (bid : positive) : list (stx * list stx) :=
  if Nat.leb K13_MIN (k13_need dgf bid fl) then
    match regsQ bc kb kk m with        (* [comment removed for export] *)
    | [] => fl
    | RE => List.filter (fun p => negb (vd_sideR RE bid (fst p))) fl
    end
  else fl.

Lemma vd_sideR_keep : forall fk t sx K kb kk m bid,
  SX_OK (mkbc fk) t sx ->
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  vd_sideR (regs (mkbc fk) kb kk m) bid sx = true ->
  prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (Pos.eqb bid (sx_bid sx)) (base_rangeB (mkbc fk) kb) = PKeep.
Proof.
  intros fk t sx K kb kk m bid (SXin & SXbr & SXsp & SXps) HB HD Hv.
  unfold vd_sideR in Hv. destruct (Pos.eqb bid (sx_bid sx)); [discriminate|].
  apply existsb_exists in Hv as [j [INj Pj]]. apply pmem_In in Pj. rewrite SXps in Pj.
  destruct (regs_In_ex _ _ _ _ _ INj) as [c [ml [R COND]]].
  pose proof (partners_of_sides _ _ _ _ _ _ _ (mkbc_rt fk) Pj R) as IND.
  eapply prune1pcK_keep_sides; [exact HB | exact HD |].
  rewrite SXsp. unfold mk_sprepB, elen. rewrite disj_sidesBM_fst. cbn [sp_D]. fold (zlit64 (Z.of_nat (sx_w sx))).
  exact (in_sidesB_In _ _ _ _ _ c ml IND COND).
Qed.

(* [comment removed for export] *)
Lemma chainKFD_filter : forall bc dgf K kk m okb same_of br2 (vd : stx -> bool) fl,
  (forall p, In p fl -> vd (fst p) = true ->
     prune1pcK bc (sx_sp (fst p)) (sx_a (fst p)) (sx_w (fst p)) (sx_v (fst p)) K (same_of (sx_bid (fst p))) br2 = PKeep) ->
  chainKFD bc (List.filter (fun p => negb (vd (fst p))) fl) dgf K kk m okb same_of br2 = chainKFD bc fl dgf K kk m okb same_of br2.
Proof.
  intros bc dgf K kk m okb same_of br2 vd fl. induction fl as [|[sx rest] fl IH]; intros H; [reflexivity|].
  assert (IH' : chainKFD bc (List.filter (fun p => negb (vd (fst p))) fl) dgf K kk m okb same_of br2 = chainKFD bc fl dgf K kk m okb same_of br2)
    by (apply IH; intros p Hp; apply H; right; exact Hp).
  cbn [List.filter fst]. destruct (vd sx) eqn:Hv; cbn [negb].
  - rewrite IH'. cbn [chainKFD].
    pose proof (H (sx, rest) (or_introl eq_refl) Hv) as HP. cbn [fst] in HP.
    assert (EV : visitD bc sx (match okb with Some _ => dgf sx | None => None end) K kk m (same_of (sx_bid sx)) br2 = PKeep).
    { unfold visitD. destruct (match okb with Some _ => dgf sx | None => None end) as [d|]; [|exact HP].
      destruct (if same_of (sx_bid sx) then false else dig_apart d (a_off (sx_a sx)) (sx_m1 sx) kk m); [reflexivity | exact HP]. }
    rewrite EV. reflexivity.
  - cbn [chainKFD]. destruct (visitD bc sx (match okb with Some _ => dgf sx | None => None end) K kk m (same_of (sx_bid sx)) br2); [exact IH' | reflexivity].
Qed.

Lemma fl_sides_eq : forall fk t sxs fl dgf K kb kk m bid,
  Forall (SX_OK (mkbc fk) t) sxs -> Forall (fun p => In (fst p) sxs) fl ->
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  chainKFD (mkbc fk) (fl_sides (mkbc fk) dgf fl kb kk m bid) dgf K kk m (Some kb) (Pos.eqb bid) (base_rangeB (mkbc fk) kb)
  = chainKFD (mkbc fk) fl dgf K kk m (Some kb) (Pos.eqb bid) (base_rangeB (mkbc fk) kb).
Proof.
  intros fk t sxs fl dgf K kb kk m bid HS HF HB HD. unfold fl_sides.
  destruct (Nat.leb K13_MIN (k13_need dgf bid fl)); [|reflexivity].
  rewrite regsQ_eq. destruct (regs (mkbc fk) kb kk m) as [|j RE] eqn:ER; [reflexivity|]. rewrite <- ER.
  apply chainKFD_filter. intros p Hp Hv.
  pose proof (proj1 (Forall_forall _ _) HF p Hp) as Hin.
  pose proof (proj1 (Forall_forall _ _) HS (fst p) Hin) as SX.
  exact (vd_sideR_keep fk t (fst p) K kb kk m bid SX HB HD Hv).
Qed.

(* [comment removed for export] *)
Definition sub_itv_xBQ (bc : bctx) (qp : qprep) (b : expr) (k : Z) (n : expr) (c : saddr) (m : expr) : bool :=
  match n with
  | ELit z => sub_itvB bc b k (zlit64 z) c m
  | _ => xinsideBQ bc qp b k n (a_base c) (a_off c) m
  end.
Lemma sub_itv_xBQ_eq : forall bc b k n c m, sub_itv_xBQ bc (mkqp bc b n) b k n c m = sub_itv_xB bc b k n c m.
Proof. intros. unfold sub_itv_xBQ, sub_itv_xB. destruct n; try reflexivity; apply xinsideBQ_eq. Qed.
Definition regs_xQ (bc : bctx) (b : expr) (k : Z) (n : expr) : list positive :=
  let qp := mkqp bc b n in
  List.map fst (List.filter (fun t : positive * (saddr * expr) => sub_itv_xBQ bc qp b k n (fst (snd t)) (snd (snd t))) (rt_sides (bc_rt bc))).
Lemma regs_xQ_eq : forall bc b k n, regs_xQ bc b k n = regs_x bc b k n.
Proof. intros. unfold regs_xQ, regs_x. f_equal. apply filter_ext. intros t. apply sub_itv_xBQ_eq. Qed.

Fixpoint entriesG8 (bc : bctx) (sxs : list stx) (gl : ptree gfl4) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           let okb := kbase K in
           let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
           let br2 := match okb with Some _ => ei_br ei | None => None end in
           match ei_m ei with
           | Some m =>
               match pt_get gl (ei_gid ei) with
               | Some (g, fl, tab) =>
                   if (if inb g ei then kwf K else false) then
                     chainKFD bc (match okb with Some kb => fl_sides bc (dg_lookup tab) fl kb (ei_k ei) m (ei_bid ei) | None => fl end)
                              (dg_lookup tab) K (ei_k ei) m okb same_of br2          (* [comment removed for export] *)
                   else chainK2 bc sxs K okb same_of br2
               | None => chainK2 bc sxs K okb same_of br2
               end
           | None =>
               match okb, klen K with
               | Some kb, Some len =>
                   let h2 := xhiB bc len in
                   let RE := regs_xQ bc kb (ei_k ei) len in       (* [comment removed for export] *)
                   chainKF bc (mk_flV (fun sx => vd_symR RE sx (ei_bid ei) br2 (ei_k ei) h2) sxs) K okb same_of br2
               | _, _ => chainK2 bc sxs K okb same_of br2
               end
           end
       | None => chainK2 bc sxs K None (fun _ => false) None
       end) ++ entriesG8 bc sxs gl rest irest
  | _, _ => []
  end.

Lemma entriesG8_eq : forall fk sxs gl kn infos t1,
  Forall (SX_OK (mkbc fk) t1) sxs -> Forall2 (EINF (mkbc fk) t1) kn infos ->
  (forall gid g fl tab, pt_get gl gid = Some (g, fl, tab) -> Forall (fun p => In (fst p) sxs) fl) ->
  entriesG8 (mkbc fk) sxs gl kn infos = entriesG7 (mkbc fk) sxs gl kn infos.
Proof.
  intros fk sxs gl kn infos t1 HS HF HG. induction HF as [|K oi rest irest HK HF IH]; [reflexivity|].
  cbn [entriesG8 entriesG7]. rewrite IH. f_equal.
  destruct oi as [ei|]; [|reflexivity]. cbn [EINF] in HK. destruct HK as (HD & HIn & Hbr).
  cbv zeta. destruct (ei_m ei) as [m|] eqn:Hm; [|rewrite ?regs_xQ_eq; destruct (kbase K); [destruct (klen K); [rewrite regs_xQ_eq|]|]; reflexivity].
  match goal with |- context [match ?X with Some _ => _ | None => chainK2 _ _ _ _ _ _ end] => destruct X as [[[g fl] tab]|] eqn:HGet; [|reflexivity] end.
  destruct (if inb g ei then kwf K else false); [|reflexivity].
  destruct (kbase K) as [kb|] eqn:HB0; [|reflexivity].
  destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & _ & _)]; [|cbn in HB0; discriminate].
  rewrite HB0 in HB. injection HB as ->. rewrite Hbr.
  apply (fl_sides_eq fk t1 sxs fl (dg_lookup tab) K (ei_kb ei) (ei_k ei) m (ei_bid ei) HS (HG _ _ _ _ HGet) HB0).
  first [exact HD | rewrite HD; reflexivity | rewrite HD, Hm; reflexivity].
Qed.

Lemma mk_flV_In : forall vd sxs p, In p (mk_flV vd sxs) -> In (fst p) sxs.
Proof.
  intros vd sxs. induction sxs as [|sx rest IH]; intros p H; [destruct H|]. cbn [mk_flV] in H.
  destruct (vd sx); [right; exact (IH p H)|]. destruct H as [<-|H]; [left; reflexivity | right; exact (IH p H)].
Qed.
Lemma mk_gl5_fl_In : forall bc bnds sxs gid g fl tab,
  pt_get (mk_gl5 bc bnds sxs) gid = Some (g, fl, tab) -> Forall (fun p => In (fst p) sxs) fl.
Proof.
  intros bc bnds sxs gid g fl tab H. unfold mk_gl5 in H. cbv zeta in H. rewrite pt_get_map in H.
  destruct (pt_get bnds gid) as [g0|]; [|discriminate]. unfold mk_g5 in H. cbv zeta in H. injection H as _ <- _.
  apply Forall_forall. intros p Hp. exact (mk_flV_In _ _ _ Hp).
Qed.

Definition carryG8 (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxs2 bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_part bc sxs ++ entriesG8 bc sxs (mk_gl5 bc (gs_bnds gs) sxs) kn infos.
Lemma carryG8_eq : forall fk log kn, carryG8 (mkbc fk) log kn = carryG7 (mkbc fk) log kn.
Proof.
  intros fk log kn. unfold carryG8, carryG7.
  destruct (mk_stxs2 (mkbc fk) log nt_empty) as [sxs t0] eqn:E. rewrite mk_stxs2_eq in E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & _ & _).
  destruct (scan_entries (mkbc fk) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
  assert (HS1 : Forall (SX_OK (mkbc fk) t1) sxs).
  { apply Forall_impl with (P := SX_OK (mkbc fk) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
  rewrite (entriesG8_eq _ _ _ _ _ _ HS1 HF (mk_gl5_fl_In _ _ _)). reflexivity.
Qed.
(* [comment removed for export] *)
Definition carryK8 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryG8 bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryK8_eq : forall log kn hints,
  carryK8 (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. rewrite <- carryK7_eq. unfold carryK8, carryK7.
  destruct log; [reflexivity|]. destruct hints; [|reflexivity]. rewrite carryG8_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Definition rel_ge0B (bc : bctx) (pos neg : xterms) : bool :=
  if xt_nowrapB bc pos then
    if xt_nowrapB bc neg then
      let c := (xt_const pos - xt_const neg)%Z in
      let ts := lsub_e (xt_lin pos) (xt_lin neg) in
      let r0 := lin_range (erangeB bc) c ts in
      if lin_hopeless r0 then false else lin_test_rB bc r0 c ts (fun lo _ => Z.leb 0 lo)
    else false
  else false.

Lemma rel_ge0B_core : forall bc pos neg, rel_ge0B bc pos neg = true -> lin_ge0_coreB bc pos neg = true.
Proof.
  intros bc pos neg H. unfold rel_ge0B in H. unfold lin_ge0_coreB.
  destruct (xt_nowrapB bc pos); [|discriminate]. destruct (xt_nowrapB bc neg); [|discriminate]. cbn [negb]. cbv zeta in H.
  destruct (lin_hopeless (lin_range (erangeB bc) (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)))); [discriminate|].
  rewrite H. reflexivity.
Qed.
Lemma rel_ge0B_ge0 : forall bc pos neg, rel_ge0B bc pos neg = true -> lin_ge0BF bc pos neg = true.
Proof. intros bc pos neg H. rewrite lin_ge0BF_eq. unfold lin_ge0B. rewrite (rel_ge0B_core _ _ _ H). reflexivity. Qed.

Lemma lin_test_relB_shift : forall bc c d ts, (0 <= d)%Z ->
  lin_test_relB bc c ts (fun lo _ => Z.leb 0 lo) = true -> lin_test_relB bc (c + d)%Z ts (fun lo _ => Z.leb 0 lo) = true.
Proof.
  intros bc c d ts Hd H. unfold lin_test_relB in *. destruct (bc_fs bc) as [|f fs]; [discriminate|].
  destruct (sum_subst (f :: fs) ts 0 0 false) as [[ts' [lo0 hi0]] b]. destruct b; [|discriminate].
  rewrite lin_range_shift. destruct (lin_range (erangeB bc) c ts') as [[lo hi]|]; [|discriminate].
  apply Z.leb_le in H. apply Z.leb_le. lia.
Qed.

Lemma rel_ge0B_mono : forall bc pos neg pos' neg',
  xt_lin pos' = xt_lin pos -> xt_lin neg' = xt_lin neg ->
  (xt_nowrapB bc pos = true -> xt_nowrapB bc pos' = true) -> (xt_nowrapB bc neg = true -> xt_nowrapB bc neg' = true) ->
  (xt_const pos - xt_const neg <= xt_const pos' - xt_const neg')%Z ->
  rel_ge0B bc pos neg = true -> rel_ge0B bc pos' neg' = true.
Proof.
  intros bc pos neg pos' neg' Ep En Np Nn Hc H. unfold rel_ge0B in *. rewrite Ep, En.
  destruct (xt_nowrapB bc pos) eqn:P; [|discriminate]. destruct (xt_nowrapB bc neg) eqn:N; [|discriminate].
  rewrite (Np eq_refl), (Nn eq_refl). cbv zeta in *.
  set (d := ((xt_const pos' - xt_const neg') - (xt_const pos - xt_const neg))%Z).
  assert (Hd : (0 <= d)%Z) by (unfold d; lia).
  replace (xt_const pos' - xt_const neg')%Z with ((xt_const pos - xt_const neg) + d)%Z by (unfold d; lia).
  rewrite lin_range_shift.
  destruct (lin_range (erangeB bc) (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg))) as [[lo hi]|] eqn:R.
  - cbn [lin_hopeless] in *. destruct (Z.ltb hi 0) eqn:Hh; [discriminate|]. apply Z.ltb_ge in Hh.
    replace (Z.ltb (hi + d) 0) with false by (symmetry; apply Z.ltb_ge; lia).
    unfold lin_test_rB in *. destruct (Z.leb 0 lo) eqn:Hlo.
    + apply Z.leb_le in Hlo. replace (Z.leb 0 (lo + d)) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    + destruct (Z.leb 0 (lo + d)); [reflexivity|]. apply lin_test_relB_shift; [exact Hd | exact H].
  - cbn [lin_hopeless] in *. unfold lin_test_rB in *. apply lin_test_relB_shift; [exact Hd | exact H].
Qed.

(* [comment removed for export] *)
Definition hull_rel (bc : bctx) (gkb : expr) (glo ghi : Z) (c : saddr) (ml : expr) : bool :=
  if shares_var gkb (a_base c) then
    if (if Z.leb glo ghi then Z.ltb (ghi - glo) (2 ^ 63) else false) then
      if rel_ge0B bc [(gkb, glo)] [(a_base c, a_off c)]
      then rel_ge0B bc [(a_base c, a_off c); (ml, 0%Z)] [(gkb, glo); (ELit (ghi - glo), 0%Z)]
      else false
    else false
  else false.

Lemma hull_rel_member : forall bc gkb glo ghi c ml k m,
  hull_rel bc gkb glo ghi c ml = true -> (glo <= k)%Z -> (k + m <= ghi)%Z -> (0 <= m)%Z ->
  sub_itvB bc gkb k m c ml = true.
Proof.
  intros bc gkb glo ghi c ml k m H Hk Hkm Hm. unfold hull_rel in H.
  destruct (shares_var gkb (a_base c)) eqn:SV; [|discriminate].
  destruct (Z.leb glo ghi) eqn:Hle; [|discriminate]. destruct (Z.ltb (ghi - glo) (2 ^ 63)) eqn:Hlt; [|discriminate].
  apply Z.leb_le in Hle. apply Z.ltb_lt in Hlt.
  destruct (rel_ge0B bc [(gkb, glo)] [(a_base c, a_off c)]) eqn:P1; [|discriminate]. rename H into P2.
  unfold sub_itvB.
  match goal with |- (if ?X then true else _) = true => destruct X; [reflexivity|] end.
  replace (Z.leb 0 m && Z.ltb m two64)%bool with true
    by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt; unfold two64]; lia).
  unfold xinsideB. rewrite SV. unfold xinside0B.
  rewrite (rel_ge0B_ge0 bc [(gkb, k)] [(a_base c, a_off c)]).
  - apply rel_ge0B_ge0.
    apply (rel_ge0B_mono bc [(a_base c, a_off c); (ml, 0%Z)] [(gkb, glo); (ELit (ghi - glo), 0%Z)]); [reflexivity | reflexivity | auto | | | exact P2].
    + cbn [xt_nowrapB]. intros N. apply andb_prop in N as [N1 _]. rewrite N1. rewrite lin_nowrapRB_lit by lia. reflexivity.
    + cbn [xt_const lin_of fst]. rewrite (snorm_id (ghi - glo)) by lia. rewrite (snorm_id m) by lia. lia.
  - apply (rel_ge0B_mono bc [(gkb, glo)] [(a_base c, a_off c)]); [reflexivity | reflexivity | auto | auto | | exact P1].
    cbn [xt_const]. lia.
Qed.
(* [comment removed for export] *)
Local Open Scope Z_scope.
Record wce : Type := WCE { wc_b : expr; wc_lo : Z; wc_hi : Z; wc_sides : list (saddr * expr); wc_wr : bool }.
Definition wcache : Type := list wce.
Definition wc_in (b : expr) (k n : Z) (e : wce) : bool :=
  if expr_eqb b (wc_b e) then (if Z.leb (wc_lo e) k then Z.leb (k + n) (wc_hi e) else false) else false.
Definition wc_get (wc : wcache) (b : expr) (k n : Z) : option wce := List.find (wc_in b k n) wc.
Definition side_eqb (x y : saddr * expr) : bool :=
  if expr_eqb (a_base (fst x)) (a_base (fst y)) then (if Z.eqb (a_off (fst x)) (a_off (fst y)) then expr_eqb (snd x) (snd y) else false) else false.
Lemma side_eqb_eq : forall x y, side_eqb x y = true -> x = y.
Proof.
  intros [[b1 o1] m1] [[b2 o2] m2] H. unfold side_eqb in H. cbn [fst snd a_base a_off] in H.
  destruct (expr_eqb b1 b2) eqn:E1; [|discriminate]. destruct (Z.eqb o1 o2) eqn:E2; [|discriminate].
  apply p_expr_eqb_eq in E1, H. apply Z.eqb_eq in E2. subst. reflexivity.
Qed.
Fixpoint wr_hull (bc : bctx) (kn : list kentry) (b : expr) (glo ghi : Z) : bool :=
  match kn with
  | [] => false
  | KWr c len :: rest => if hull_rel bc b glo ghi c len then true else wr_hull bc rest b glo ghi
  | _ :: rest => wr_hull bc rest b glo ghi
  end.
Definition wce_ok (bc : bctx) (e : wce) : Prop :=
  Forall (fun s => hull_rel bc (wc_b e) (wc_lo e) (wc_hi e) (fst s) (snd s) = true) (wc_sides e)
  /\ (wc_wr e = true -> wr_hull bc (bc_fk bc) (wc_b e) (wc_lo e) (wc_hi e) = true).
Definition WCOK (bc : bctx) (wc : wcache) : Prop := Forall (wce_ok bc) wc.

Definition regsW (wc : wcache) (bc : bctx) (b : expr) (k n : Z) : list positive :=
  match wc_get wc b k n with
  | Some e =>
      if Z.leb 0 n then
        let qp := mkqp bc b (ELit n) in
        List.map fst (List.filter (fun t : positive * (saddr * expr) =>
                                     if existsb (side_eqb (snd t)) (wc_sides e) then true else sub_itvBQ bc qp b k n (fst (snd t)) (snd (snd t))) (rt_sides (bc_rt bc)))
      else regsQ bc b k n
  | None => regsQ bc b k n
  end.
Lemma wc_get_in : forall wc b k n e, wc_get wc b k n = Some e -> In e wc /\ b = wc_b e /\ wc_lo e <= k /\ k + n <= wc_hi e.
Proof.
  intros wc b k n e H. unfold wc_get in H. apply find_some in H as [HI HP]. unfold wc_in in HP.
  destruct (expr_eqb b (wc_b e)) eqn:E; [|discriminate]. destruct (Z.leb (wc_lo e) k) eqn:L; [|discriminate].
  apply p_expr_eqb_eq in E. apply Z.leb_le in L, HP. auto.
Qed.
Lemma regsW_eq : forall bc wc b k n, WCOK bc wc -> regsW wc bc b k n = regs bc b k n.
Proof.
  intros bc wc b k n HW. unfold regsW. destruct (wc_get wc b k n) as [e|] eqn:G; [|apply regsQ_eq].
  destruct (Z.leb 0 n) eqn:Hn; [|apply regsQ_eq]. apply Z.leb_le in Hn.
  destruct (wc_get_in _ _ _ _ _ G) as (HI & -> & Hlo & Hhi).
  pose proof (proj1 (Forall_forall _ _) HW e HI) as [HS _].
  unfold regs. f_equal. apply filter_ext. intros t.
  destruct (existsb (side_eqb (snd t)) (wc_sides e)) eqn:EX; [|apply sub_itvBQ_eq].
  apply existsb_exists in EX as [s [INs Es]]. apply side_eqb_eq in Es. subst s.
  pose proof (proj1 (Forall_forall _ _) HS (snd t) INs) as HH.
  symmetry. exact (hull_rel_member bc (wc_b e) (wc_lo e) (wc_hi e) (fst (snd t)) (snd (snd t)) k n HH Hlo Hhi Hn).
Qed.

Definition SOKw (bc : bctx) (wc : wcache) (a : saddr) (n : nat) : list sidecond :=
  match wc_get wc (a_base a) (a_off a) (Z.of_nat n) with
  | Some e => if wc_wr e then [] else storeok_scB2 bc a n
  | None => storeok_scB2 bc a n
  end.
Lemma wr_hull_covered : forall bc kn a n glo ghi,
  wr_hull bc kn (a_base a) glo ghi = true -> glo <= a_off a -> a_off a + Z.of_nat n <= ghi -> wr_coveredB bc kn a n = true.
Proof.
  intros bc kn a n glo ghi. induction kn as [|K rest IH]; intros H Hlo Hhi; [discriminate|].
  destruct K as [? ? ?|? ?|? ? ?|? ?|? ?|? ? ?|[kb kk] len|? ? ? ?|? ? ?|? ?]; cbn [wr_hull wr_coveredB] in *; try (apply IH; assumption).
  destruct (hull_rel bc (a_base a) glo ghi (SA kb kk) len) eqn:HH.
  - pose proof (hull_rel_member bc (a_base a) glo ghi (SA kb kk) len (a_off a) (Z.of_nat n) HH Hlo Hhi (Nat2Z.is_nonneg n)) as S.
    unfold sub_itvB in S. cbn [a_base a_off] in S.
    destruct (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
              then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end else false); [reflexivity|].
    destruct (Z.leb 0 (Z.of_nat n) && Z.ltb (Z.of_nat n) two64)%bool; [|discriminate]. rewrite S. reflexivity.
  - rewrite (IH H Hlo Hhi).
    destruct (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
              then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end else false); [reflexivity|].
    destruct (xinsideB bc (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len); reflexivity.
Qed.
Lemma SOKw_eq : forall bc wc a n, WCOK bc wc -> SOKw bc wc a n = storeok_scB2 bc a n.
Proof.
  intros bc wc a n HW. unfold SOKw. destruct (wc_get wc (a_base a) (a_off a) (Z.of_nat n)) as [e|] eqn:G; [|reflexivity].
  destruct (wc_wr e) eqn:W; [|reflexivity].
  destruct (wc_get_in _ _ _ _ _ G) as (HI & Eb & Hlo & Hhi).
  pose proof (proj1 (Forall_forall _ _) HW e HI) as [_ HWr]. specialize (HWr W). rewrite <- Eb in HWr.
  unfold storeok_scB2. rewrite wr_covered2_eq. rewrite (wr_hull_covered _ _ _ _ _ _ HWr Hlo Hhi). reflexivity.
Qed.

Definition WCW : Z := 65536.
Definition wc_step (bc : bctx) (ss ss' : sym_state) (wc : wcache) : wcache :=
  if Nat.eqb (length (s_log ss')) (length (s_log ss)) then wc
  else match s_log ss' with
       | SE (SA b k) w _ :: _ =>
           match wc_get wc b k (Z.of_nat w) with
           | Some _ => wc
           | None =>
               if wr_syn bc (bc_fk bc) (SA b k) w then wc      (* [comment removed for export] *)
               else let glo := k - WCW in let ghi := k + Z.of_nat w in      (* [comment removed for export] *)
                    let sides := List.filter (fun s : saddr * expr => hull_rel bc b glo ghi (fst s) (snd s)) (List.map snd (rt_sides (bc_rt bc))) in
                    let wr := wr_hull bc (bc_fk bc) b glo ghi in
                    match sides, wr with
                    | [], false => wc
                    | _, _ => WCE b glo ghi sides wr :: wc
                    end
           end
       | [] => wc
       end.
Lemma wc_step_ok : forall bc ss ss' wc, WCOK bc wc -> WCOK bc (wc_step bc ss ss' wc).
Proof.
  intros bc ss ss' wc HW. unfold wc_step. destruct (Nat.eqb _ _); [exact HW|].
  destruct (s_log ss') as [|[[b k] w v] rest]; [exact HW|].
  destruct (wc_get wc b k (Z.of_nat w)); [exact HW|]. destruct (wr_syn bc (bc_fk bc) (SA b k) w); [exact HW|]. cbv zeta.
  assert (NEW : wce_ok bc (WCE b (k - WCW) (k + Z.of_nat w)
                                (List.filter (fun s : saddr * expr => hull_rel bc b (k - WCW) (k + Z.of_nat w) (fst s) (snd s)) (List.map snd (rt_sides (bc_rt bc))))
                                (wr_hull bc (bc_fk bc) b (k - WCW) (k + Z.of_nat w)))).
  { split; cbn [wc_b wc_lo wc_hi wc_sides wc_wr].
    - apply Forall_forall. intros s Hs. apply filter_In in Hs as [_ Hs]. exact Hs.
    - intros H. exact H. }
  revert NEW.
  generalize (List.filter (fun s : saddr * expr => hull_rel bc b (k - WCW) (k + Z.of_nat w) (fst s) (snd s)) (List.map snd (rt_sides (bc_rt bc)))).
  generalize (wr_hull bc (bc_fk bc) b (k - WCW) (k + Z.of_nat w)).
  intros wr sides NEW. destruct sides as [|s0 sr]; destruct wr; try exact HW; constructor; try exact HW; exact NEW.
Qed.

Fixpoint log_lookupQDW (wc : wcache) (bc : bctx) (log : list sentry) (lrs : list (list positive)) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) (q : option (option (Z * Z) * list positive)) (dc : dcache) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      let lrs' := match lrs with _ :: t => t | [] => [] end in
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupQDW wc bc rest lrs' rb rk n sx hints acc q dc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let q' := match q with Some x => x | None => (base_rangeB bc rb, regsW wc bc rb rk (Z.of_nat n)) end in
          let rs := match lrs with r :: _ => r | [] => regs bc kb kk (Z.of_nat w) end in
          let '(dv, dc') := match dc_find dc kb with
                            | Some x => (x, dc)
                            | None => let x := (base_rangeB bc kb, mk_ldig bc rb kb) in (x, (kb, x) :: dc)
                            end in
          if ranges_apartQD bc (fst q') (snd q') rs dv rk (Z.of_nat n) kk (Z.of_nat w)
          then log_lookupQDW wc bc rest lrs' rb rk n sx hints acc (Some q') dc'
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupQDW wc bc rest lrs' rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc) (Some q') dc'
          end
      end
  end.

Lemma log_lookupQDW_eq : forall wc bc log lrs rb rk n sx hints acc q dc,
  WCOK bc wc -> log_lookupQDW wc bc log lrs rb rk n sx hints acc q dc = log_lookupQD bc log lrs rb rk n sx hints acc q dc.
Proof.
  intros wc bc log. induction log as [|[[kb kk] w v] rest IH]; intros lrs rb rk n sx hints acc q dc HW; [reflexivity|].
  cbn [log_lookupQDW log_lookupQD].
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity.
  - apply IH; exact HW.
  - rewrite (regsW_eq bc wc rb rk (Z.of_nat n) HW), <- (regsQ_eq bc rb rk (Z.of_nat n)).
    set (q' := match q with Some x => x | None => (base_rangeB bc rb, regsQ bc rb rk (Z.of_nat n)) end).
    destruct (dc_find dc kb) as [x|].
    + destruct (ranges_apartQD bc (fst q') (snd q') _ x rk (Z.of_nat n) kk (Z.of_nat w)); [apply IH; exact HW|].
      destruct hints as [|[|] hs]; [| | reflexivity]; apply IH; exact HW.
    + destruct (ranges_apartQD bc (fst q') (snd q') _ _ rk (Z.of_nat n) kk (Z.of_nat w)); [apply IH; exact HW|].
      destruct hints as [|[|] hs]; [| | reflexivity]; apply IH; exact HW.
Qed.
Definition sym_stepBI2G (RD : sym_state -> scripts -> saddr -> nat -> bool -> option (expr * list sidecond * scripts * nat)) (SOK : saddr -> nat -> list sidecond) (bc : bctx) (kx : kix) (lrs : list (list positive)) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluKB bc op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwKB bc ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdKB bc op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_exprB bc (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branchB bc c a b with
            | Some t => Some t
            | None => match decide_branchB bc c (conc_exprB bc a) (conc_exprB bc b) with
                      | Some t => Some t
                      | None => enum_branchB bc c a b
                      end
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrKB bc (g rs) (bv_signed imm) in
      match RD ss scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrKB bc (g rs1) (bv_signed imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_scB bc a n ++ SOK a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match RD ss scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_scB bc a n ++ SOK a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedbB bc e wd then
            let a := to_saddrKB bc e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match RD ss scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ SOK a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.


Lemma sym_stepBI2_G : forall bc kx lrs segs i ss scr,
  sym_stepBI2 bc kx lrs segs i ss scr = sym_stepBI2G (fun ss0 scr0 => sym_readBI2 segs ss0 bc kx lrs scr0) (storeok_scB2 bc) bc kx lrs segs i ss scr.
Proof. intros. reflexivity. Qed.

Section Exec3.
Variable segs : list Segment.
Definition sym_readBI3 (wc : wcache) (ss : sym_state) (bc : bctx) (kx : kix) (lrs : list (list positive)) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookupQDW wc bc (s_log ss) lrs (a_base a) (a_off a) n sx' (sc_hints scr) [] None [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extKB bc v, flat_scB bc a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupABI bc kx segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extKB bc v, flat_scB bc a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_scB bc a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.
Lemma sym_readBI3_eq : forall wc ss bc kx lrs scr a n sx', WCOK bc wc ->
  sym_readBI3 wc ss bc kx lrs scr a n sx' = sym_readBI2 segs ss bc kx lrs scr a n sx'.
Proof. intros. unfold sym_readBI3, sym_readBI2. rewrite log_lookupQDW_eq by assumption. reflexivity. Qed.
Definition lrs_step3 (wc : wcache) (bc : bctx) (ss ss' : sym_state) (lrs : list (list positive)) : list (list positive) :=
  if Nat.eqb (length (s_log ss')) (length (s_log ss)) then lrs
  else match s_log ss' with SE (SA kb kk) w _ :: _ => regsW wc bc kb kk (Z.of_nat w) :: lrs | [] => lrs end.
Lemma lrs_step3_eq : forall wc bc ss ss' lrs, WCOK bc wc -> lrs_step3 wc bc ss ss' lrs = lrs_step2 bc ss ss' lrs.
Proof.
  intros. unfold lrs_step3, lrs_step2. destruct (Nat.eqb _ _); [reflexivity|]. destruct (s_log ss') as [|[[kb kk] w v] r]; [reflexivity|].
  rewrite regsW_eq by assumption. unfold regsEQ. rewrite regsQ_eq. reflexivity.
Qed.
Definition sym_stepXBI3 (bc : bctx) (kx : kix) (lrs : list (list positive)) (wc : wcache) (K : nat) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  match sym_stepBI2G (fun ss0 scr0 => sym_readBI3 wc ss0 bc kx lrs scr0) (SOKw bc wc) bc kx lrs segs i ss scr with
  | SOk ss' scs scr' =>
      if Nat.leb (s_next ss) (s_next ss')
      then SOk (cap_rd K i ss') (x_filterB segs bc ss ss' scs) scr'
      else SStop
  | SStop => SStop
  end.
Lemma sym_stepXBI3_eq : forall bc kx lrs wc K i ss scr, WCOK bc wc ->
  sym_stepXBI3 bc kx lrs wc K i ss scr = sym_stepXBI2 segs bc kx lrs K i ss scr.
Proof.
  intros bc kx lrs wc K i ss scr HW. unfold sym_stepXBI3, sym_stepXBI2. rewrite sym_stepBI2_G.
  replace (fun ss0 scr0 => sym_readBI3 wc ss0 bc kx lrs scr0) with (fun ss0 scr0 => sym_readBI2 segs ss0 bc kx lrs scr0).
  2:{ apply functional_extensionality; intros ss0. apply functional_extensionality; intros scr0. apply functional_extensionality; intros a.
      apply functional_extensionality; intros n. apply functional_extensionality; intros sx'. symmetry. apply sym_readBI3_eq. exact HW. }
  replace (SOKw bc wc) with (storeok_scB2 bc).
  2:{ apply functional_extensionality; intros a. apply functional_extensionality; intros n. symmetry. apply SOKw_eq. exact HW. }
  reflexivity.
Qed.
Fixpoint sym_execTXBI3_go (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
         (lrs : list (list positive)) (wc : wcache) : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXBI3 bc kx lrs wc K i ss scr_nil with
          | SOk ss' [] _ =>
              let wc' := wc_step bc ss ss' wc in
              sym_execTXBI3_go bc kx t K f false stops ss' (if s_clean ss' then ss' else ck) (lrs_step3 wc' bc ss ss' lrs) wc'
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Lemma sym_execTXBI3_go_eq : forall bc kx t K fuel first stops ss ck lrs wc, WCOK bc wc ->
  sym_execTXBI3_go bc kx t K fuel first stops ss ck lrs wc = sym_execTXBI2_go segs bc kx t K fuel first stops ss ck lrs.
Proof.
  intros bc kx t K fuel. induction fuel as [|f IH]; intros first stops ss ck lrs wc HW; [reflexivity|].
  cbn [sym_execTXBI3_go sym_execTXBI2_go].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|]; [|reflexivity].
  rewrite sym_stepXBI3_eq by exact HW. destruct (sym_stepXBI2 segs bc kx lrs K i ss scr_nil) as [ss' scs scr'|]; [|reflexivity].
  destruct scs; [|reflexivity]. cbv zeta.
  rewrite lrs_step3_eq by (apply wc_step_ok; exact HW). apply IH. apply wc_step_ok. exact HW.
Qed.
Definition sym_execTXBI3 (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) : sym_state :=
  sym_execTXBI3_go bc kx t K fuel first stops (clr ss) (clr ss) (List.map (regsE bc) (s_log ss)) [].
Lemma sym_execTXBI3_eq : forall bc kx t K fuel first stops ss,
  sym_execTXBI3 bc kx t K fuel first stops ss = sym_execTXBI2 segs bc kx t K fuel first stops ss.
Proof. intros. unfold sym_execTXBI3, sym_execTXBI2. apply sym_execTXBI3_go_eq. constructor. Qed.
End Exec3.

(* [comment removed for export] *)
Section Exec5.
Variable segs : list Segment.
Fixpoint sym_execTXBI5_go (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
         (lrs lck : list (list positive)) (wc : wcache) : sym_state * list (list positive) :=
  match fuel with
  | O => if s_clean ss then (ss, lrs) else (ck, lck)
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then (ss, lrs) else (ck, lck)) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then (ss, lrs) else (ck, lck)
      | Some i =>
          match sym_stepXBI3 segs bc kx lrs wc K i ss scr_nil with
          | SOk ss' [] _ =>
              let wc' := wc_step bc ss ss' wc in
              let lrs' := lrs_step3 wc' bc ss ss' lrs in
              sym_execTXBI5_go bc kx t K f false stops ss' (if s_clean ss' then ss' else ck) lrs' (if s_clean ss' then lrs' else lck) wc'
          | _ => if s_clean ss then (ss, lrs) else (ck, lck)
          end
      end
  end.
Lemma sym_execTXBI5_go_fst : forall bc kx t K fuel first stops ss ck lrs lck wc,
  fst (sym_execTXBI5_go bc kx t K fuel first stops ss ck lrs lck wc) = sym_execTXBI3_go segs bc kx t K fuel first stops ss ck lrs wc.
Proof.
  intros bc kx t K fuel. induction fuel as [|f IH]; intros first stops ss ck lrs lck wc.
  - cbn. destruct (s_clean ss); reflexivity.
  - cbn [sym_execTXBI5_go sym_execTXBI3_go].
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [destruct (s_clean ss); reflexivity|].
    destruct (itab_lookup t (s_pc ss)) as [i|]; [|destruct (s_clean ss); reflexivity].
    destruct (sym_stepXBI3 segs bc kx lrs wc K i ss scr_nil) as [ss' scs scr'|]; [|destruct (s_clean ss); reflexivity].
    destruct scs; [|destruct (s_clean ss); reflexivity]. cbv zeta. apply IH.
Qed.
Lemma sym_execTXBI5_go_lrs : forall t K fuel first stops ss ck lrs lck wc,
  let bc := mkbc (facts_of (s_know ss)) in
  lrs = List.map (regsE bc) (s_log ss) -> lck = List.map (regsE bc) (s_log ck) -> WCOK bc wc ->
  snd (sym_execTXBI5_go bc (mk_kix (s_know ss)) t K fuel first stops ss ck lrs lck wc)
  = List.map (regsE bc) (s_log (fst (sym_execTXBI5_go bc (mk_kix (s_know ss)) t K fuel first stops ss ck lrs lck wc))).
Proof.
  intros t K fuel. induction fuel as [|f IH]; intros first stops ss ck lrs lck wc bc L LC HW.
  - cbn. destruct (s_clean ss); cbn [fst snd]; assumption.
  - cbn [sym_execTXBI5_go].
    destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [destruct (s_clean ss); cbn [fst snd]; assumption|].
    destruct (itab_lookup t (s_pc ss)) as [i|]; [|destruct (s_clean ss); cbn [fst snd]; assumption].
    destruct (sym_stepXBI3 segs bc (mk_kix (s_know ss)) lrs wc K i ss scr_nil) as [ss' scs scr'|] eqn:E; [|destruct (s_clean ss); cbn [fst snd]; assumption].
    destruct scs; [|destruct (s_clean ss); cbn [fst snd]; assumption]. cbv zeta.
    (* [comment removed for export] *)
    assert (E' : sym_stepX segs K i ss scr_nil = SOk ss' [] scr').
    { rewrite <- E. unfold bc. rewrite sym_stepXBI3_eq by exact HW. rewrite sym_stepXBI2_eq. symmetry. apply sym_stepXBI_eq. exact L. }
    pose proof (sym_stepX_know segs _ _ _ _ _ _ _ E') as EK.
    assert (L' : lrs_step3 (wc_step bc ss ss' wc) bc ss ss' lrs = List.map (regsE bc) (s_log ss')).
    { rewrite lrs_step3_eq by (apply wc_step_ok; exact HW). rewrite lrs_step2_eq.
      apply lrs_step_ok; [exact (sym_stepX_log segs _ _ _ _ _ _ _ E') | exact L]. }
    unfold bc in *. rewrite <- EK in *.
    apply IH; [exact L' | destruct (s_clean ss'); [exact L' | exact LC] | apply wc_step_ok; exact HW].
Qed.
Definition sym_execTXBI5 (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state)
  : sym_state * list (list positive) :=
  let l0 := List.map (regsE bc) (s_log ss) in
  sym_execTXBI5_go bc kx t K fuel first stops (clr ss) (clr ss) l0 l0 [].
Lemma sym_execTXBI5_spec : forall kn0 t K fuel first stops ss, s_know ss = kn0 ->
  sym_execTXBI5 (mkbc (facts_of kn0)) (mk_kix kn0) t K fuel first stops ss
  = (sym_execTXBI3 segs (mkbc (facts_of kn0)) (mk_kix kn0) t K fuel first stops ss,
     List.map (regsE (mkbc (facts_of kn0))) (s_log (sym_execTXBI3 segs (mkbc (facts_of kn0)) (mk_kix kn0) t K fuel first stops ss))).
Proof.
  intros kn0 t K fuel first stops ss <-. unfold sym_execTXBI5, sym_execTXBI3. cbv zeta.
  set (l0 := List.map (regsE (mkbc (facts_of (s_know ss)))) (s_log ss)).
  rewrite (surjective_pairing (sym_execTXBI5_go _ _ _ _ _ _ _ _ _ _ _ _)). f_equal.
  - apply sym_execTXBI5_go_fst.
  - rewrite <- sym_execTXBI5_go_fst with (lck := l0).
    replace (s_know ss) with (s_know (clr ss)) by (destruct ss; reflexivity).
    apply (sym_execTXBI5_go_lrs t K fuel first stops (clr ss) (clr ss) l0 l0 []).
    + unfold l0. destruct ss; reflexivity.
    + unfold l0. destruct ss; reflexivity.
    + constructor.
Qed.
End Exec5.

(* [comment removed for export] *)
Fixpoint mk_stxs3 (bc : bctx) (log : list sentry) (lrs : list (list positive)) (t : ntab) : list (stx * list positive) * ntab :=
  match log with
  | [] => ([], t)
  | SE a w v :: older =>
      let '(sxr, t1) := mk_stxs3 bc older (match lrs with _ :: r => r | [] => [] end) t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let RS := match lrs with
                | R :: _ => if Nat.leb w 8 then R else regsQ bc (a_base a) (a_off a) (zlit64 (Z.of_nat w))
                | [] => regsQ bc (a_base a) (a_off a) (zlit64 (Z.of_nat w))
                end in
      (sxr ++ [(STX a w v (mk_sprepR bc RS (a_base a) w) bid (bi_br bi) (partners_of (bc_rt bc) RS), RS)], t2)
  end.
Definition stx_rs_ok (bc : bctx) (p : stx * list positive) : Prop := snd p = regs_w bc (sx_a (fst p)) (sx_w (fst p)).
Lemma mk_stxs3_ok : forall bc log lrs t, lrs = List.map (regsE bc) log ->
  (List.map fst (fst (mk_stxs3 bc log lrs t)), snd (mk_stxs3 bc log lrs t)) = mk_stxs2 bc log t
  /\ Forall (stx_rs_ok bc) (fst (mk_stxs3 bc log lrs t)).
Proof.
  intros bc log. induction log as [|[a w v] older IH]; intros lrs t L; [split; [reflexivity | constructor]|].
  cbn [List.map] in L. subst lrs. cbn [mk_stxs3 mk_stxs2].
  destruct (IH (List.map (regsE bc) older) t eq_refl) as [E2 F2].
  destruct (mk_stxs3 bc older (List.map (regsE bc) older) t) as [sxr1 t1]. cbn [fst snd] in E2, F2. rewrite <- E2.
  destruct (intern bc t1 (a_base a)) as [[bid bi] t2].
  assert (ER : (if Nat.leb w 8 then regsE bc (SE a w v) else regsQ bc (a_base a) (a_off a) (zlit64 (Z.of_nat w)))
               = regsQ bc (a_base a) (a_off a) (zlit64 (Z.of_nat w))).
  { destruct (Nat.leb w 8) eqn:W; [|reflexivity]. apply Nat.leb_le in W. destruct a as [kb kk]. cbn [regsE a_base a_off].
    rewrite regsQ_eq. rewrite zlit64_small; [reflexivity|]. split; [lia|]. change (2 ^ 64)%Z with 18446744073709551616%Z. lia. }
  rewrite ER. cbn [fst snd]. split.
  - rewrite map_app. reflexivity.
  - apply Forall_app. split; [exact F2|]. constructor; [|constructor]. unfold stx_rs_ok. cbn [fst snd sx_a sx_w]. unfold regs_w. apply regsQ_eq.
Qed.

Definition K17_MIN : nat := 8.
Fixpoint stores_part3 (bc : bctx) (sxr : list (stx * list positive)) : list kentry :=   (* [comment removed for export] *)
  match sxr with
  | [] => []
  | (sx, RE) :: newer =>
      let nw := List.map fst newer in
      stores_part3 bc newer ++
      (if (if Nat.leb K17_MIN (length nw) then match RE with [] => false | _ :: _ => true end else false)
       then chainKF bc (mk_flV (vd_sideR RE (sx_bid sx)) nw) (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx)
       else chainK2 bc nw (KWord (sx_a sx) (sx_w sx) (sx_v sx)) (Some (a_base (sx_a sx))) (Pos.eqb (sx_bid sx)) (sx_br sx))
  end.
Lemma stores_part3_eq : forall fk t sxr,
  Forall (SX_OK (mkbc fk) t) (List.map fst sxr) -> Forall (stx_rs_ok (mkbc fk)) sxr ->
  stores_part3 (mkbc fk) sxr = stores_part (mkbc fk) (List.map fst sxr).
Proof.
  intros fk t sxr. induction sxr as [|[sx RE] newer IH]; intros HS HR; [reflexivity|].
  cbn [List.map fst] in HS. apply Forall_cons_iff in HS as [HS0 HS]. apply Forall_cons_iff in HR as [HR0 HR].
  cbn [stores_part3 stores_part List.map fst]. rewrite (IH HS HR). f_equal.
  destruct (if Nat.leb K17_MIN (length (List.map fst newer)) then match RE with [] => false | _ :: _ => true end else false); [|reflexivity].
  apply chainKFV_eq. intros sx' Hin Hv.
  pose proof (proj1 (Forall_forall _ _) HS sx' Hin) as SX'.
  destruct HS0 as (_ & SXbr & _ & _). rewrite SXbr.
  unfold stx_rs_ok in HR0. cbn [fst snd] in HR0. subst RE. unfold regs_w in Hv.
  destruct (sx_a sx) as [kb kk] eqn:EA. cbn [a_base a_off] in *.
  exact (vd_sideR_keep fk t sx' (KWord (SA kb kk) (sx_w sx) (sx_v sx)) kb kk (zlit64 (Z.of_nat (sx_w sx))) (sx_bid sx) SX' eq_refl eq_refl Hv).
Qed.

Definition carryG9 (bc : bctx) (log : list sentry) (lrs : list (list positive)) (kn : list kentry) : list kentry :=
  let '(sxr, t0) := mk_stxs3 bc log lrs nt_empty in
  let sxs := List.map fst sxr in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_part3 bc sxr ++ entriesG8 bc sxs (mk_gl5 bc (gs_bnds gs) sxs) kn infos.
Lemma carryG9_eq : forall fk log lrs kn, lrs = List.map (regsE (mkbc fk)) log -> carryG9 (mkbc fk) log lrs kn = carryG8 (mkbc fk) log kn.
Proof.
  intros fk log lrs kn L. unfold carryG9, carryG8.
  destruct (mk_stxs3_ok (mkbc fk) log lrs nt_empty L) as [E2 FR].
  destruct (mk_stxs3 (mkbc fk) log lrs nt_empty) as [sxr t0]. cbn [fst snd] in E2, FR. rewrite <- E2.
  pose proof E2 as E. symmetry in E. rewrite mk_stxs2_eq in E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & _ & _).
  rewrite (stores_part3_eq fk t0 sxr HS0 FR). reflexivity.
Qed.
Definition carryK9 (bc : bctx) (log : list sentry) (lrs : list (list positive)) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryG9 bc log lrs kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryK9_eq : forall log lrs kn hints, lrs = List.map (regsE (mkbc (facts_of kn))) log ->
  carryK9 (mkbc (facts_of kn)) log lrs kn hints = carry log kn hints.
Proof.
  intros log lrs kn hints L. rewrite <- carryK8_eq. unfold carryK9, carryK8.
  destruct log; [reflexivity|]. destruct hints; [|reflexivity]. rewrite carryG9_eq by exact L. reflexivity.
Qed.

Lemma carryK9_eq2 : forall log kn0 kn hints, kn = kn0 ->
  carryK9 (mkbc (facts_of kn0)) log (List.map (regsE (mkbc (facts_of kn0))) log) kn hints = carry log kn hints.
Proof. intros log kn0 kn hints ->. apply carryK9_eq. reflexivity. Qed.

End AX2K.
