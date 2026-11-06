(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AxSymExec3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.

Module AX2C.
Import AX2 AX2B.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition zofw (w : nat) : Z :=
  match w with
  | 1%nat => 1 | 2%nat => 2 | 4%nat => 4 | 8%nat => 8
  | _ => Z.of_nat w
  end.
Lemma zofw_eq : forall w, zofw w = Z.of_nat w.
Proof. intros w. do 9 (destruct w as [|w]; [reflexivity|]). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint side_cover (bc : bctx) (gb : expr) (glo ghi : Z) (D : list (saddr * expr)) : bool :=
  match D with
  | [] => false
  | (c, m) :: r =>
      if (if expr_eqb gb (a_base c) then
            if Z.leb (a_off c) glo then match xloB bc m with Some ml => Z.leb ghi (a_off c + ml) | None => false end else false
          else false)
      then true else side_cover bc gb glo ghi r
  end.
Definition verdict_side (bc : bctx) (t : ntab) (sx : stx) (g : gval) : bool :=
  match g with
  | (b, _, (glo, ghi)) =>
      if Pos.eqb b (sx_bid sx) then false else
      match sp_D (sx_sp sx) with
      | [] => false
      | D => match pt_get (nt_info t) b with
             | Some bi => side_cover bc (bi_base bi) glo ghi D
             | None => false
             end
      end
  end.
Definition verdict2 (bc : bctx) (t : ntab) (sx : stx) (g : gval) : bool :=
  if verdict sx g then true else verdict_side bc t sx g.
Fixpoint mk_fl2 (bc : bctx) (t : ntab) (g : gval) (sxs : list stx) : list (stx * list stx) :=
  match sxs with
  | [] => []
  | sx :: rest => if verdict2 bc t sx g then mk_fl2 bc t g rest else (sx, rest) :: mk_fl2 bc t g rest
  end.
Definition mk_gl2 (bc : bctx) (t : ntab) (bnds : gtab) (sxs : list stx) : ptree gfl := pt_map (fun g => (g, mk_fl2 bc t g sxs)) bnds.

(* [comment removed for export] *)
Definition entry1 (bc : bctx) (sbs : list (positive * expr)) (sxs : list stx) (gl : ptree gfl) (K : kentry) (ei : einfo) : list kentry :=
  let okb := kbase K in
  let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
  let br2 := match okb with Some _ => ei_br ei | None => None end in
  let fa_of := match okb, kbkl K with
               | Some kb, Some (_, _, len) => fa_entry bc (mk_aqs bc sbs kb len) kb
               | _, _ => fa_none
               end in
  match pt_get gl (ei_gid ei) with
  | Some (g, fl) => if inb g ei then chainKF bc fl K okb same_of br2 fa_of else chainK2 bc sxs K okb same_of br2 fa_of
  | None => chainK2 bc sxs K okb same_of br2 fa_of
  end.
Fixpoint entriesG2 (bc : bctx) (sbs : list (positive * expr)) (sxs : list stx) (gl : ptree gfl) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      match oi with
      | Some ei => entry1 bc sbs sxs gl K ei ++ entriesG2 bc sbs sxs gl rest irest
      | None => K :: entriesG2 bc sbs sxs gl rest irest      (* [comment removed for export] *)
      end
  | _, _ => []
  end.
Definition carryG2 (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxs bc log nt_empty in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, t1) := r in
  stores_part bc sxs ++ entriesG2 bc (store_bases sxs) sxs (mk_gl2 bc t1 (gs_bnds gs) sxs) kn infos.
Definition carryK2 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | [_], [] | [_; _], [] => carryB bc log kn []
  | _, [] => (carryG2 bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.

(* [comment removed for export] *)
Lemma side_cover_in_sides : forall bc gb glo ghi D kk m,
  side_cover bc gb glo ghi D = true -> glo <= kk -> kk + m <= ghi -> in_sidesB bc D gb kk m = true.
Proof.
  intros bc gb glo ghi D kk m. induction D as [|[c m'] r IH]; intros H Hlo Hhi; [discriminate H|].
  cbn [side_cover] in H. cbn [in_sidesB].
  destruct (expr_eqb gb (a_base c)) eqn:EB.
  - destruct (Z.leb (a_off c) glo) eqn:EL.
    + destruct (xloB bc m') as [ml|] eqn:EX.
      * destruct (Z.leb ghi (a_off c + ml)) eqn:EH.
        -- unfold sub_itvB. rewrite EB, EX. apply Z.leb_le in EL. apply Z.leb_le in EH.
           replace (Z.leb (a_off c) kk) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
           replace (Z.leb (kk + m) (a_off c + ml)) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
        -- destruct (sub_itvB bc gb kk m c m'); [reflexivity|]. apply IH; assumption.
      * destruct (sub_itvB bc gb kk m c m'); [reflexivity|]. apply IH; assumption.
    + destruct (sub_itvB bc gb kk m c m'); [reflexivity|]. apply IH; assumption.
  - destruct (sub_itvB bc gb kk m c m'); [reflexivity|]. apply IH; assumption.
Qed.

Lemma prune1pcK_keep_side_based : forall bc sp wa w wv K kb kk m br2,
  kbase K = Some kb -> kdescr K = Some (kb, kk, Some m) ->
  in_sidesB bc (sp_D sp) kb kk m = true ->
  forall fa, prune1pcK bc sp wa w wv K false br2 fa = PKeep.
Proof.
  intros bc sp wa w wv K kb kk m br2 HB HD Hin fa. destruct fa; [reflexivity|].
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [kbase kdescr] in HB, HD; try discriminate; injection HB as ->;
    try (injection HD as <- <-); try (destruct len as [z| | | | | | |]; try discriminate; injection HD as <- <-);
    unfold prune1pcK; (destruct (pk_keepb _ _ _ _); [reflexivity|]); unfold prune1pcK0; cbn [a_base a_off]; unfold ranges_apart_pcB; cbn [elen];
    rewrite Hin;
    match goal with |- context [if (if ?c then true else true) then _ else _] => destruct c; reflexivity end.
Qed.

Lemma prune1pcK_keep_side_img : forall bc sp wa w wv lo hi m same br2,
  kdescr (KImg lo hi) = Some (ELit 0%Z, lo, Some m) ->
  expr_eqb (ELit 0%Z) (a_base wa) = false ->
  in_sidesB bc (sp_D sp) (ELit 0%Z) lo m = true ->
  forall fa, prune1pcK bc sp wa w wv (KImg lo hi) same br2 fa = PKeep.
Proof.
  intros bc sp wa w wv lo hi m same br2 HD Hne Hin fa. destruct fa; [reflexivity|].
  cbn [kdescr] in HD. destruct (Z.ltb (hi - lo) (2 ^ 64)) eqn:Hlt; [|discriminate]. injection HD as <-.
  unfold prune1pcK. destruct (pk_keepb _ _ _ _); [reflexivity|]. unfold prune1pcK0. destruct wa as [wb k]. cbn [a_base a_off] in *.
  assert (STEP : (if ranges_apart_pB bc sp wb k (elen w) (ELit 0%Z) lo (ELit (hi - lo)) then PKeep else PRepl []) = PKeep).
  { unfold ranges_apart_pB. cbn [elen]. rewrite Hin.
    match goal with |- context [if (if ?c then true else true) then _ else _] => destruct c; reflexivity end. }
  rewrite Hlt. destruct wb as [z| | | | | | |]; try exact STEP.
  destruct z; try exact STEP. cbn in Hne. discriminate.
Qed.

(* [comment removed for export] *)
Lemma chainKF_eq2 : forall bc t g sxs K okb same_of br2 fa_of,
  (forall sx, In sx sxs -> verdict2 bc t sx g = true ->
     prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 (fa_of sx K) = PKeep) ->
  chainKF bc (mk_fl2 bc t g sxs) K okb same_of br2 fa_of = chainK2 bc sxs K okb same_of br2 fa_of.
Proof.
  intros bc t g sxs. induction sxs as [|sx rest IH]; intros K okb same_of br2 fa_of Hf; [reflexivity|].
  cbn [mk_fl2 chainK2].
  assert (IH' : chainKF bc (mk_fl2 bc t g rest) K okb same_of br2 fa_of = chainK2 bc rest K okb same_of br2 fa_of)
    by (apply IH; intros; apply Hf; [right|]; assumption).
  destruct (verdict2 bc t sx g) eqn:Hv.
  - rewrite (Hf sx (or_introl eq_refl) Hv). exact IH'.
  - cbn [chainKF]. destruct (prune1pcK _ _ _ _ _ K _ br2 _); [exact IH'|reflexivity].
Qed.

Lemma chainK2_fact : forall bc sxs K okb same_of br2 fa_of,
  kdescr K = None -> chainK2 bc sxs K okb same_of br2 fa_of = [K].
Proof.
  intros bc sxs K okb same_of br2 fa_of HD. induction sxs as [|sx rest IH]; [reflexivity|].
  cbn [chainK2].
  assert (E : prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 (fa_of sx K) = PKeep).
  { unfold prune1pcK. destruct (fa_of sx K); [reflexivity|]. destruct (pk_keepb _ _ _ _); [reflexivity|].
    destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
      cbn [kdescr] in HD; try discriminate; reflexivity. }
  rewrite E. exact IH.
Qed.

(* [comment removed for export] *)
Lemma entry1_eq : forall fk sbs sxs bnds t1 K ei,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) sxs ->
  EINF (mkbc fk) t1 K (Some ei) ->
  entry1 (mkbc fk) sbs sxs (mk_gl2 (mkbc fk) t1 bnds sxs) K ei = entry1 (mkbc fk) sbs sxs (mk_gl bnds sxs) K ei.
Proof.
  intros fk sbs sxs bnds t1 K ei HT HS HK. cbn [EINF] in HK. destruct HK as (HD & HIn & Hbr).
  unfold entry1. cbv zeta. unfold mk_gl2, mk_gl. rewrite !pt_get_map.
  destruct (pt_get bnds (ei_gid ei)) as [g|]; [|reflexivity].
  destruct (inb g ei) eqn:Hinb; [|reflexivity].
  assert (Hm : exists m, ei_m ei = Some m).
  { unfold inb in Hinb. destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]. }
  destruct Hm as [m Hm]. rewrite Hm in HD.
  (* [comment removed for export] *)
  transitivity (chainK2 (mkbc fk) sxs K (kbase K)
                  (match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end)
                  (match kbase K with Some _ => ei_br ei | None => None end)
                  (match kbase K, kbkl K with
                   | Some kb, Some (_, _, len) => fa_entry (mkbc fk) (mk_aqs (mkbc fk) sbs kb len) kb
                   | _, _ => fa_none
                   end)).
  2: { symmetry. apply chainKF_eq. intros sx Hsx Hv.
       destruct (verdict_inb_num _ _ _ _ Hv Hinb Hm) as (Hne & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
       pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp).
       destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
       - rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_based; [exact HB|exact HD|exact Hsp| | exact Hnum].
         rewrite <- Hbr. exact Hbr2.
       - cbn [kbase]. rewrite Hkb, Hk in *.
         eapply prune1pcK_keep_img; [exact HD| |exact Hsp| rewrite <- Hbr; exact Hbr2 | exact Hnum].
         rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne. }
  apply chainKF_eq2. intros sx Hsx Hv. unfold verdict2 in Hv.
  destruct (verdict sx g) eqn:Hv1.
  - (* [comment removed for export] *)
    destruct (verdict_inb_num _ _ _ _ Hv1 Hinb Hm) as (Hne & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
    pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp).
    destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
    + rewrite HB. rewrite Hne. rewrite Hbr. eapply prune1pcK_keep_based; [exact HB|exact HD|exact Hsp| | exact Hnum].
      rewrite <- Hbr. exact Hbr2.
    + cbn [kbase]. rewrite Hkb, Hk in *.
      eapply prune1pcK_keep_img; [exact HD| |exact Hsp| rewrite <- Hbr; exact Hbr2 | exact Hnum].
      rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne.
  - (* [comment removed for export] *)
    destruct g as [[b obr] [glo ghi]]. unfold verdict_side in Hv. unfold inb in Hinb. rewrite Hm in Hinb.
    apply andb_prop in Hinb as [Hi H4]. apply andb_prop in Hi as [Hi H3]. apply andb_prop in Hi as [H1 H2].
    apply Pos.eqb_eq in H1. subst b. apply Z.leb_le in H3. apply Z.leb_le in H4.
    destruct (Pos.eqb (ei_bid ei) (sx_bid sx)) eqn:Hne; [discriminate|].
    destruct (sp_D (sx_sp sx)) as [|d0 drest] eqn:ED; [discriminate|]. rewrite <- ED in Hv.
    destruct HT as [HA HBq]. destruct (HA _ _ _ HIn) as (_ & Hinfo & _). rewrite Hinfo in Hv. cbn [bi_base] in Hv.
    pose proof (side_cover_in_sides _ _ _ _ _ _ _ Hv H3 H4) as Hsides.
    pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & SXbr & SXsp).
    destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)].
    + rewrite HB. rewrite Hne. eapply prune1pcK_keep_side_based; [exact HB|exact HD|exact Hsides].
    + cbn [kbase]. rewrite Hkb, Hk in *.
      eapply prune1pcK_keep_side_img; [exact HD| |exact Hsides].
      rewrite <- (nt_same_eq _ _ _ _ _ _ (conj HA HBq) HIn SXin). exact Hne.
Qed.

Lemma entriesG2_eq : forall fk sxs sbs bnds kn infos t1,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) sxs -> Forall2 (EINF (mkbc fk) t1) kn infos ->
  entriesG2 (mkbc fk) sbs sxs (mk_gl2 (mkbc fk) t1 bnds sxs) kn infos = entriesG (mkbc fk) sbs sxs (mk_gl bnds sxs) kn infos.
Proof.
  intros fk sxs sbs bnds kn infos t1 HT HS HF. induction HF as [|K oi rest irest HK HF IH]; [reflexivity|].
  cbn [entriesG2 entriesG]. rewrite IH. destruct oi as [ei|].
  - f_equal. rewrite (entry1_eq _ _ _ _ _ _ _ HT HS HK). reflexivity.
  - cbn [EINF] in HK. rewrite (chainK2_fact _ _ _ _ _ _ _ HK). reflexivity.
Qed.

Lemma carryG2_eq : forall fk log kn, carryG2 (mkbc fk) log kn = carryG (mkbc fk) log kn.
Proof.
  intros fk log kn. unfold carryG2, carryG.
  destruct (mk_stxs (mkbc fk) log nt_empty) as [sxs t0] eqn:E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & Hmap & _).
  destruct (scan_entries (mkbc fk) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
  assert (HS1 : Forall (SX_OK (mkbc fk) t1) sxs).
  { apply Forall_impl with (P := SX_OK (mkbc fk) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
  rewrite (entriesG2_eq _ _ _ _ _ _ _ HT1 HS1 HF). reflexivity.
Qed.

Lemma carryK2_eqK : forall fk log kn hints, carryK2 (mkbc fk) log kn hints = carryK (mkbc fk) log kn hints.
Proof.
  intros fk log kn hints. unfold carryK2, carryK.
  destruct log as [|s1 [|s2 [|s3 older]]]; try reflexivity.
  destruct hints; [|reflexivity]. rewrite carryG2_eq. reflexivity.
Qed.
Lemma carryK2_eq : forall log kn hints, carryK2 (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof. intros. rewrite carryK2_eqK. apply carryK_eq. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sides := list (saddr * expr).
Fixpoint sides_eqb (l1 l2 : sides) : bool :=
  match l1, l2 with
  | [], [] => true
  | (c1, m1) :: r1, (c2, m2) :: r2 =>
      if expr_eqb (a_base c1) (a_base c2) then
        if Z.eqb (a_off c1) (a_off c2) then if expr_eqb m1 m2 then sides_eqb r1 r2 else false else false
      else false
  | _, _ => false
  end.
Definition ctab := list (positive * (sides * sides)).
Fixpoint ct_find (t : ctab) (D Dx : sides) : option positive :=
  match t with
  | [] => None
  | (id, (D', Dx')) :: r => if (if sides_eqb D D' then sides_eqb Dx Dx' else false) then Some id else ct_find r D Dx
  end.
(* [comment removed for export] *)
Fixpoint mk_cls (sxs : list stx) (t : ctab) (next : positive) : list (stx * positive) * ctab :=
  match sxs with
  | [] => ([], t)
  | sx :: rest =>
      let D := sp_D (sx_sp sx) in let Dx := sp_Dx (sx_sp sx) in
      match ct_find t D Dx with
      | Some id => let '(l, t') := mk_cls rest t next in ((sx, id) :: l, t')
      | None => let '(l, t') := mk_cls rest (t ++ [(next, (D, Dx))]) (Pos.succ next) in ((sx, next) :: l, t')
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition smemo := list (saddr * expr * bool).
Fixpoint sm_get (m : smemo) (c : saddr) (n : expr) : option bool :=
  match m with
  | [] => None
  | (c', n', v) :: r =>
      if (if expr_eqb (a_base c) (a_base c') then if Z.eqb (a_off c) (a_off c') then expr_eqb n n' else false else false)
      then Some v else sm_get r c n
  end.
Definition sget (m : smemo) (c : saddr) (n : expr) (f : unit -> bool) : bool * smemo :=
  match sm_get m c n with Some v => (v, m) | None => let v := f tt in (v, (c, n, v) :: m) end.
Fixpoint disj_sidesM (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (m : smemo) : sides * smemo :=
  match kn with
  | [] => ([], m)
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(r, ma) := disj_sidesM bc rest b1 k1 n1 m in
      let '(v2, mb) := sget ma c2 m2 (fun _ => sub_itvB bc b1 k1 n1 c2 m2) in
      let r1 := if v2 then (c1, m1) :: r else r in
      let '(v1, mc) := sget mb c1 m1 (fun _ => sub_itvB bc b1 k1 n1 c1 m1) in
      (if v1 then (c2, m2) :: r1 else r1, mc)
  | _ :: rest => disj_sidesM bc rest b1 k1 n1 m
  end.
Fixpoint disj_sides_xM (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (m : smemo) : sides * smemo :=
  match kn with
  | [] => ([], m)
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(r, ma) := disj_sides_xM bc rest b1 k1 n1 m in
      let '(v2, mb) := sget ma c2 m2 (fun _ => sub_itv_xB bc b1 k1 n1 c2 m2) in
      let r1 := if v2 then (c1, m1) :: r else r in
      let '(v1, mc) := sget mb c1 m1 (fun _ => sub_itv_xB bc b1 k1 n1 c1 m1) in
      (if v1 then (c2, m2) :: r1 else r1, mc)
  | _ :: rest => disj_sides_xM bc rest b1 k1 n1 m
  end.
Definition mk_sprepM (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) : sprep :=
  SPrep (base_rangeB bc b1) (xhiB bc n1)
        (match n1 with ELit z1 => fst (disj_sidesM bc (bc_fk bc) b1 k1 (zlit64 z1) []) | _ => [] end)
        (fst (disj_sides_xM bc (bc_fk bc) b1 k1 n1 [])).
(* [comment removed for export] *)
Definition fastp (bc : bctx) (b : expr) (k n : Z) (c : saddr) (m : expr) : bool :=
  if (expr_eqb b (a_base c) && Z.leb (a_off c) k)%bool then
    match xloB bc m with Some ml => Z.leb (k + n) (a_off c + ml) | None => false end
  else false.
Definition tD (bc : bctx) (b1 : expr) (k1 n1 : Z) (mx : smemo) (c : saddr) (m : expr) : bool :=
  if fastp bc b1 k1 n1 c m then true
  else match sm_get mx c m with Some v => v | None => sub_itvB bc b1 k1 n1 c m end.
Fixpoint disj_sidesD (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (mx : smemo) : sides :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sidesD bc rest b1 k1 n1 mx in
      let r1 := if tD bc b1 k1 n1 mx c2 m2 then (c1, m1) :: r else r in
      if tD bc b1 k1 n1 mx c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sidesD bc rest b1 k1 n1 mx
  end.
Definition mk_sprepM2 (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) : sprep :=
  match n1 with
  | ELit z1 =>
      if (if Z.leb 0 z1 then Z.ltb z1 two64 else false) then
        let '(Dx, mx) := disj_sides_xM bc (bc_fk bc) b1 k1 n1 [] in
        SPrep (base_rangeB bc b1) (xhiB bc n1) (disj_sidesD bc (bc_fk bc) b1 k1 z1 mx) Dx
      else mk_sprepM bc b1 k1 n1
  | _ => mk_sprepM bc b1 k1 n1
  end.
(* [comment removed for export] *)
Record xq := XQ { xq_nw : bool; xq_stA : list ge0_stage; xq_cA : Z; xq_stB : list ge0_stage; xq_cB : Z }.
Definition mk_xq (bc : bctx) (b1 : expr) (c : saddr) (m : expr) : xq :=
  let b2 := a_base c in
  XQ (if lin_nowrapRB bc b1 then if lin_nowrapRB bc b2 then lin_nowrapRB bc m else false else false)
     (ge0_stagesB bc (lsub_e (xt_lin [(b1, 0)]) (xt_lin [(b2, 0)]))) (xt_const [(b1, 0)] - xt_const [(b2, a_off c)])
     (ge0_stagesB bc (lsub_e (xt_lin [(b2, 0); (m, 0)]) (xt_lin [(b1, 0)]))) (xt_const [(b2, a_off c); (m, 0)] - xt_const [(b1, 0)]).
Definition xq_eval (q : xq) (k1 : Z) (wnw : bool) (wc : Z) : bool :=
  if xq_nw q then if wnw then
    if ge0_eval (xq_stA q) (xq_cA q + k1) then ge0_eval (xq_stB q) (xq_cB q - k1 - wc) else false
  else false else false.
(* [comment removed for export] *)
Definition xcache := list (positive * expr * list (saddr * expr * xq)).
Fixpoint xc_sides (xc : xcache) (bid : positive) (b1 : expr) : list (saddr * expr * xq) :=
  match xc with
  | [] => []
  | (id, b, l) :: r => if Pos.eqb bid id then (if expr_eqb b1 b then l else []) else xc_sides r bid b1
  end.
Fixpoint xs_get (l : list (saddr * expr * xq)) (c : saddr) (m : expr) : option xq :=
  match l with
  | [] => None
  | (c', m', q) :: r =>
      if (if expr_eqb (a_base c) (a_base c') then if Z.eqb (a_off c) (a_off c') then expr_eqb m m' else false else false)
      then Some q else xs_get r c m
  end.
Fixpoint xc_put (xc : xcache) (bid : positive) (b1 : expr) (l : list (saddr * expr * xq)) : xcache :=
  match xc with
  | [] => [(bid, b1, l)]
  | (id, b, l0) :: r => if Pos.eqb bid id then (bid, b1, l) :: r else (id, b, l0) :: xc_put r bid b1 l
  end.
(* [comment removed for export] *)
Definition tXq (bc : bctx) (b1 : expr) (k1 : Z) (w : nat) (wnw : bool) (wc : Z) (xl : list (saddr * expr * xq)) (c : saddr) (m : expr)
  : bool * list (saddr * expr * xq) :=
  if shares_var b1 (a_base c) then
    match xs_get xl c m with
    | Some q => (xq_eval q k1 wnw wc, xl)
    | None => let q := mk_xq bc b1 c m in (xq_eval q k1 wnw wc, (c, m, q) :: xl)
    end
  else (sub_itv_xB bc b1 k1 (ELit (Z.of_nat w)) c m, xl).
Fixpoint disj_sides_xQ (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (w : nat) (wnw : bool) (wc : Z)
         (sm : smemo) (xl : list (saddr * expr * xq)) : sides * smemo * list (saddr * expr * xq) :=
  match kn with
  | [] => ([], sm, xl)
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(r, sma, xla) := disj_sides_xQ bc rest b1 k1 w wnw wc sm xl in
      let '(v2, smb, xlb) := match sm_get sma c2 m2 with
                             | Some v => (v, sma, xla)
                             | None => let '(v, xl') := tXq bc b1 k1 w wnw wc xla c2 m2 in (v, (c2, m2, v) :: sma, xl')
                             end in
      let r1 := if v2 then (c1, m1) :: r else r in
      let '(v1, smc, xlc) := match sm_get smb c1 m1 with
                             | Some v => (v, smb, xlb)
                             | None => let '(v, xl') := tXq bc b1 k1 w wnw wc xlb c1 m1 in (v, (c1, m1, v) :: smb, xl')
                             end in
      (if v1 then (c2, m2) :: r1 else r1, smc, xlc)
  | _ :: rest => disj_sides_xQ bc rest b1 k1 w wnw wc sm xl
  end.
Definition mk_sprepQ (bc : bctx) (bid : positive) (b1 : expr) (k1 : Z) (w : nat) (xc : xcache) : sprep * xcache :=
  if Nat.leb w 8 then
    let '(Dx, mx, xl) := disj_sides_xQ bc (bc_fk bc) b1 k1 w (wlit_nw bc w) (wlit_c w) [] (xc_sides xc bid b1) in
    (SPrep (base_rangeB bc b1) (xhiB bc (elen w)) (disj_sidesD bc (bc_fk bc) b1 k1 (Z.of_nat w) mx) Dx, xc_put xc bid b1 xl)
  else (mk_sprepM2 bc b1 k1 (elen w), xc).
Fixpoint mk_stxsQ (bc : bctx) (log : list sentry) (t : ntab) (xc : xcache) : list stx * ntab * xcache :=
  match log with
  | [] => ([], t, xc)
  | SE a w v :: older =>
      let '(sxs, t1, xc1) := mk_stxsQ bc older t xc in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let '(sp, xc2) := mk_sprepQ bc bid (a_base a) (a_off a) w xc1 in
      (sxs ++ [STX a w v sp bid (bi_br bi)], t2, xc2)
  end.
Fixpoint mk_stxsM (bc : bctx) (log : list sentry) (t : ntab) : list stx * ntab :=
  match log with
  | [] => ([], t)
  | SE a w v :: older =>
      let '(sxs, t1) := mk_stxsM bc older t in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      (sxs ++ [STX a w v (mk_sprepM2 bc (a_base a) (a_off a) (elen w)) bid (bi_br bi)], t2)
  end.

(* [comment removed for export] *)
Definition side : Type := (saddr * expr)%type.
Definition stab := list (positive * side).
Fixpoint st_find (t : stab) (c : saddr) (m : expr) : option positive :=
  match t with
  | [] => None
  | (id, (c', m')) :: r =>
      if (if expr_eqb m m' then if Z.eqb (a_off c) (a_off c') then expr_eqb (a_base c) (a_base c') else false else false)
      then Some id else st_find r c m
  end.
Definition st_intern (t : stab) (next : positive) (c : saddr) (m : expr) : positive * stab * positive :=
  match st_find t c m with Some id => (id, t, next) | None => (next, (next, (c, m)) :: t, Pos.succ next) end.
Definition kdl := list ((positive * side) * (positive * side)).
Fixpoint mk_kdl (fk : list kentry) (t : stab) (next : positive) : kdl * stab * positive :=
  match fk with
  | [] => ([], t, next)
  | KDisj c1 m1 c2 m2 :: rest =>
      let '(i1, t1, n1) := st_intern t next c1 m1 in
      let '(i2, t2, n2) := st_intern t1 n1 c2 m2 in
      let '(l, t3, n3) := mk_kdl rest t2 n2 in
      (((i1, (c1, m1)), (i2, (c2, m2))) :: l, t3, n3)
  | _ :: rest => mk_kdl rest t next
  end.
(* [comment removed for export] *)
Fixpoint dsG (f : saddr -> expr -> bool) (l : list (side * side)) : sides :=
  match l with
  | [] => []
  | ((c1, m1), (c2, m2)) :: rest =>
      let r := dsG f rest in
      let r1 := if f c2 m2 then (c1, m1) :: r else r in
      if f c1 m1 then (c2, m2) :: r1 else r1
  end.
Definition kd_pairs (fk : list kentry) : list (side * side) :=
  flat_map (fun K => match K with KDisj c1 m1 c2 m2 => [((c1, m1), (c2, m2))] | _ => [] end) fk.
(* [comment removed for export] *)
Section DSI.
Variable ST : Type.
Variable g : ST -> positive -> saddr -> expr -> bool * ST.
Definition vget (vm : list (positive * bool)) (st : ST) (i : positive) (c : saddr) (m : expr) : bool * list (positive * bool) * ST :=
  match alookupP vm i with
  | Some v => (v, vm, st)
  | None => let '(v, st') := g st i c m in (v, (i, v) :: vm, st')
  end.
Fixpoint dsI (kd : kdl) (vm : list (positive * bool)) (st : ST) : sides * list (positive * bool) * ST :=
  match kd with
  | [] => ([], vm, st)
  | ((i1, (c1, m1)), (i2, (c2, m2))) :: rest =>
      let '(r, va, sa) := dsI rest vm st in
      let '(v2, vb, sb) := vget va sa i2 c2 m2 in
      let r1 := if v2 then (c1, m1) :: r else r in
      let '(v1, vc, sc) := vget vb sb i1 c1 m1 in
      (if v1 then (c2, m2) :: r1 else r1, vc, sc)
  end.
End DSI.
Definition xli := list (positive * xq).
Definition gX (bc : bctx) (b1 : expr) (k1 : Z) (w : nat) (wnw : bool) (wc : Z) (xl : xli) (i : positive) (c : saddr) (m : expr) : bool * xli :=
  if shares_var b1 (a_base c) then
    match alookupP xl i with
    | Some q => (xq_eval q k1 wnw wc, xl)
    | None => let q := mk_xq bc b1 c m in (xq_eval q k1 wnw wc, (i, q) :: xl)
    end
  else (sub_itv_xB bc b1 k1 (ELit (Z.of_nat w)) c m, xl).
Definition gD (bc : bctx) (b1 : expr) (k1 n1 : Z) (vmx : list (positive * bool)) (u : unit) (i : positive) (c : saddr) (m : expr) : bool * unit :=
  (if fastp bc b1 k1 n1 c m then true
   else match alookupP vmx i with Some v => v | None => sub_itvB bc b1 k1 n1 c m end, u).
Definition xcacheI := list (positive * expr * xli).
Fixpoint xcI_sides (xc : xcacheI) (bid : positive) (b1 : expr) : xli :=
  match xc with
  | [] => []
  | (id, b, l) :: r => if Pos.eqb bid id then (if expr_eqb b1 b then l else []) else xcI_sides r bid b1
  end.
Fixpoint xcI_put (xc : xcacheI) (bid : positive) (b1 : expr) (l : xli) : xcacheI :=
  match xc with
  | [] => [(bid, b1, l)]
  | (id, b, l0) :: r => if Pos.eqb bid id then (bid, b1, l) :: r else (id, b, l0) :: xcI_put r bid b1 l
  end.
Definition mk_sprepI (bc : bctx) (kd : kdl) (bid : positive) (b1 : expr) (k1 : Z) (w : nat) (xc : xcacheI) : sprep * xcacheI :=
  if Nat.leb w 8 then
    let '(Dx, vmx, xl) := dsI xli (gX bc b1 k1 w (wlit_nw bc w) (wlit_c w)) kd [] (xcI_sides xc bid b1) in
    let '(D, _, _) := dsI unit (gD bc b1 k1 (Z.of_nat w) vmx) kd [] tt in
    (SPrep (base_rangeB bc b1) (xhiB bc (elen w)) D Dx, xcI_put xc bid b1 xl)
  else (mk_sprepM2 bc b1 k1 (elen w), xc).
Fixpoint mk_stxsI (bc : bctx) (kd : kdl) (log : list sentry) (t : ntab) (xc : xcacheI) : list stx * ntab * xcacheI :=
  match log with
  | [] => ([], t, xc)
  | SE a w v :: older =>
      let '(sxs, t1, xc1) := mk_stxsI bc kd older t xc in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let '(sp, xc2) := mk_sprepI bc kd bid (a_base a) (a_off a) w xc1 in
      (sxs ++ [STX a w v sp bid (bi_br bi)], t2, xc2)
  end.

Definition memo := list (positive * bool).
Definition mget (dc : positive) (m : memo) (f : unit -> bool) : bool * memo :=
  match alookupP m dc with Some v => (v, m) | None => let v := f tt in (v, (dc, v) :: m) end.
Record ehoist := EH { eh_h2 : option Z; eh_e2 : option Z }.
Definition mk_eh (bc : bctx) (br2 : option (Z * Z)) (kb : expr) (kk : Z) (len : expr) : ehoist :=
  let h2o := xhiB bc len in
  EH h2o (match br2, h2o with Some (lo2, hi2), Some h2 => end_hiB bc kb kk len lo2 hi2 h2 | _, _ => None end).

Definition rapM (bc : bctx) (sp : sprep) (dc : positive) (eh : ehoist) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) (m : memo) : bool * memo :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then (true, m)
      else let '(v, m') := mget dc m (fun _ => in_sidesB bc (sp_D sp) b2 k2 m2) in
           if v then (true, m') else (lin_apartB bc b1 k1 m1 b2 k2 m2, m')
  | _, _ =>
    if (match sp_rng sp, br2, sp_h1 sp, eh_h2 eh with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match eh_e2 eh with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then (true, m)
    else let '(v, m') := mget dc m (fun _ => in_sides_xB bc (sp_Dx sp) b2 k2 n2) in
         if v then (true, m')
         else ((if negb (shares_var b1 b2) then false
                else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
                else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]), m')
  end.

Definition prune1pcK0M (bc : bctx) (sp : sprep) (dc : positive) (eh : ehoist) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) (m : memo) : pk_res * memo :=
  let k := a_off wa in
  let wb := a_base wa in
  let zfK (mk : saddr -> expr -> kentry) (kb : expr) (kk : Z) (len : expr) :=
    if same then
      (match len with
       | ELit l0 => PRepl (ktrim mk kb kk l0 k w)
       | _ => if Z.leb (k + Z.of_nat w) kk then PKeep
              else if lin_ge0B bc [(wb, k)] [(kb, kk); (len, 0%Z)] then PKeep
              else PRepl (kcutB bc mk wb k (elen w) kb kk len)
       end, m)
    else let '(ap, m') := rapM bc sp dc eh wb k (elen w) br2 kb kk len m in
    if ap then (PKeep, m')
    else (match kcutB bc mk wb k (elen w) kb kk len with
          | [] => if ap then PKeep else PRepl []
          | cut => PRepl cut
          end, m') in
  match K with
  | KZero (SA kb kk) len => zfK KZero kb kk len
  | KFill (SA kb kk) len c => zfK (fun a n => KFill a n c) kb kk len
  | KUnk (SA kb kk) len => zfK KUnk kb kk len
  | KWord (SA kb kk) w' v =>
      if same then (prune1pcK0 bc sp wa w wv K same br2, m)
      else let '(ap, m') := rapM bc sp dc eh wb k (elen w) br2 kb kk (elen w') m in
      if ap then (PKeep, m')
      else if (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool then (PKeep, m')
      else if ap then (PKeep, m') else (PRepl [], m')
  | KBlob (SA kb kk) len bk =>
      if same then (prune1pcK0 bc sp wa w wv K same br2, m)
      else let '(ap, m') := rapM bc sp dc eh wb k (elen w) br2 kb kk len m in
           ((if ap then PKeep else PRepl []), m')
  | _ => (prune1pcK0 bc sp wa w wv K same br2, m)
  end.
Definition prune1pcKM (bc : bctx) (sp : sprep) (dc : positive) (eh : ehoist) (wa : saddr) (w : nat) (wv : expr) (K : kentry) (same : bool)
  (br2 : option (Z * Z)) (fa : bool) (m : memo) : pk_res * memo :=
  if fa then (PKeep, m) else
  if pk_keepb wa w K same then (PKeep, m) else prune1pcK0M bc sp dc eh wa w wv K same br2 m.

(* [comment removed for export] *)
Fixpoint chainKFM (bc : bctx) (eh : ehoist) (fl : list (stx * positive * list stx)) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) (fa_of : stx -> kentry -> bool) (m : memo) : list kentry :=
  match fl with
  | [] => [K]
  | (sx, dc, rest) :: fl' =>
      let '(r, m') := prune1pcKM bc (sx_sp sx) dc eh (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 (fa_of sx K) m in
      match r with
      | PKeep => chainKFM bc eh fl' K okb same_of br2 fa_of m'
      | PRepl l =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2 bc rest K' okb same_of br2 fa_of else chain_slow bc rest [K']
                                  | None => chain_slow bc rest [K']
                                  end) l
          | None => chain_slow bc rest l
          end
      end
  end.
Fixpoint mk_fl3 (bc : bctx) (t : ntab) (g : gval) (sxcs : list (stx * positive)) : list (stx * positive * list stx) :=
  match sxcs with
  | [] => []
  | (sx, dc) :: rest => if verdict2 bc t sx g then mk_fl3 bc t g rest else (sx, dc, map fst rest) :: mk_fl3 bc t g rest
  end.
(* [comment removed for export] *)
Fixpoint all_fl (sxcs : list (stx * positive)) : list (stx * positive * list stx) :=
  match sxcs with
  | [] => []
  | (sx, dc) :: rest => (sx, dc, map fst rest) :: all_fl rest
  end.
Definition gfl3 : Type := (gval * list (stx * positive * list stx))%type.
Definition mk_gl3 (bc : bctx) (t : ntab) (bnds : gtab) (sxcs : list (stx * positive)) : ptree gfl3 :=
  pt_map (fun g => (g, mk_fl3 bc t g sxcs)) bnds.

(* [comment removed for export] *)
Definition regK (K : kentry) : bool :=
  match K with
  | KWord _ w _ => Nat.leb w 8
  | KZero _ (ELit l0) | KFill _ (ELit l0) _ | KUnk _ (ELit l0) | KBlob _ (ELit l0) _ => if Z.ltb 0 l0 then Z.ltb l0 two64 else false
  | KImg lo hi => if Z.ltb lo hi then Z.ltb (hi - lo) two64 else false
  | _ => false
  end.
Definition sfilt (bid : positive) (kk hi : Z) (x : stx * positive * list stx) : bool :=
  let sx := fst (fst x) in
  if Pos.eqb bid (sx_bid sx) then
    (if Z.leb hi (a_off (sx_a sx)) then false else if Z.leb (a_off (sx_a sx) + zofw (sx_w sx)) kk then false else true)
  else true.
Definition sfl (K : kentry) (ei : einfo) (fl : list (stx * positive * list stx)) : list (stx * positive * list stx) :=
  match ei_m ei with
  | Some m => if regK K then List.filter (sfilt (ei_bid ei) (ei_k ei) (ei_k ei + m)) fl else fl
  | None => fl
  end.
(* [comment removed for export] *)
Definition entry3c (bc : bctx) (sbs : list (positive * expr)) (K : kentry) (ei : einfo) (fl : list (stx * positive * list stx)) : list kentry :=
  match fl with
  | [] => [K]
  | _ =>
    let okb := kbase K in
    let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
    let br2 := match okb with Some _ => ei_br ei | None => None end in
    let fa_of := match okb, kbkl K with
                 | Some kb, Some (_, _, len) => fa_entry bc (mk_aqs bc sbs kb len) kb
                 | _, _ => fa_none
                 end in
    let eh := match kbkl K with Some (kb, kk, len) => mk_eh bc br2 kb kk len | None => EH None None end in
    chainKFM bc eh fl K okb same_of br2 fa_of []
  end.
Definition entry3 (bc : bctx) (sbs : list (positive * expr)) (afl : list (stx * positive * list stx)) (gl : ptree gfl3) (K : kentry) (ei : einfo) : list kentry :=
  match pt_get gl (ei_gid ei) with
  | Some (g, fl) => if inb g ei then entry3c bc sbs K ei (sfl K ei fl) else entry3c bc sbs K ei (sfl K ei afl)
  | None => entry3c bc sbs K ei (sfl K ei afl)
  end.
Fixpoint entriesG3 (bc : bctx) (sbs : list (positive * expr)) (afl : list (stx * positive * list stx)) (gl : ptree gfl3) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      match oi with
      | Some ei => entry3 bc sbs afl gl K ei ++ entriesG3 bc sbs afl gl rest irest
      | None => K :: entriesG3 bc sbs afl gl rest irest
      end
  | _, _ => []
  end.
Definition carryG3 (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(kd, _, _) := mk_kdl (bc_fk bc) [] xH in
  let '(sxs, t0, _) := mk_stxsI bc kd log nt_empty [] in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, t1) := r in
  let '(sxcs, _) := mk_cls sxs [] xH in
  stores_part bc sxs ++ entriesG3 bc (store_bases sxs) (all_fl sxcs) (mk_gl3 bc t1 (gs_bnds gs) sxcs) kn infos.
Definition carryK3 (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | [_], [] | [_; _], [] => carryB bc log kn []
  | _, [] => (carryG3 bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sm_get_In : forall m c n v, sm_get m c n = Some v -> In (c, n, v) m.
Proof.
  induction m as [|[[c' n'] v'] r IH]; cbn [sm_get]; intros c n v H; [discriminate|].
  destruct (expr_eqb (a_base c) (a_base c')) eqn:E1; [|right; apply IH; exact H].
  destruct (Z.eqb (a_off c) (a_off c')) eqn:E2; [|right; apply IH; exact H].
  destruct (expr_eqb n n') eqn:E3; [|right; apply IH; exact H].
  injection H as <-. apply p_expr_eqb_eq in E1. apply Z.eqb_eq in E2. apply p_expr_eqb_eq in E3.
  left. destruct c, c'. cbn [a_base a_off] in E1, E2. subst. reflexivity.
Qed.
Definition SMOK (f : saddr -> expr -> bool) (m : smemo) : Prop := forall c n v, In (c, n, v) m -> v = f c n.
Lemma sget_ok : forall f m c n, SMOK f m -> fst (sget m c n (fun _ => f c n)) = f c n /\ SMOK f (snd (sget m c n (fun _ => f c n))).
Proof.
  intros f m c n HM. unfold sget. destruct (sm_get m c n) as [v|] eqn:E; cbn [fst snd].
  - split; [exact (HM _ _ _ (sm_get_In _ _ _ _ E)) | exact HM].
  - split; [reflexivity|]. intros c' n' v' [H|H]; [injection H as <- <- <-; reflexivity | exact (HM _ _ _ H)].
Qed.
Lemma disj_sidesM_eq : forall bc kn b1 k1 n1 m, SMOK (sub_itvB bc b1 k1 n1) m ->
  fst (disj_sidesM bc kn b1 k1 n1 m) = disj_sidesB bc kn b1 k1 n1 /\ SMOK (sub_itvB bc b1 k1 n1) (snd (disj_sidesM bc kn b1 k1 n1 m)).
Proof.
  intros bc kn b1 k1 n1. induction kn as [|K rest IH]; intros m HM; [split; [reflexivity|exact HM]|].
  destruct K as [a w v|a l|a l bk|lo hi|e1 mm|e' lo hi|a n|c1 m1 c2 m2|a l c|a l]; cbn [disj_sidesM disj_sidesB]; try (apply IH; exact HM).
  destruct (IH m HM) as [E HM1]. destruct (disj_sidesM bc rest b1 k1 n1 m) as [r ma]. cbn [fst snd] in E, HM1. subst r.
  destruct (sget_ok (sub_itvB bc b1 k1 n1) ma c2 m2 HM1) as [E2 HM2].
  destruct (sget ma c2 m2 (fun _ => sub_itvB bc b1 k1 n1 c2 m2)) as [v2 mb]. cbn [fst snd] in E2, HM2. subst v2.
  destruct (sget_ok (sub_itvB bc b1 k1 n1) mb c1 m1 HM2) as [E1 HM3].
  destruct (sget mb c1 m1 (fun _ => sub_itvB bc b1 k1 n1 c1 m1)) as [v1 mc]. cbn [fst snd] in E1, HM3 |- *. subst v1.
  split; [reflexivity|exact HM3].
Qed.
Lemma disj_sides_xM_eq : forall bc kn b1 k1 n1 m, SMOK (sub_itv_xB bc b1 k1 n1) m ->
  fst (disj_sides_xM bc kn b1 k1 n1 m) = disj_sides_xB bc kn b1 k1 n1 /\ SMOK (sub_itv_xB bc b1 k1 n1) (snd (disj_sides_xM bc kn b1 k1 n1 m)).
Proof.
  intros bc kn b1 k1 n1. induction kn as [|K rest IH]; intros m HM; [split; [reflexivity|exact HM]|].
  destruct K as [a w v|a l|a l bk|lo hi|e1 mm|e' lo hi|a n|c1 m1 c2 m2|a l c|a l]; cbn [disj_sides_xM disj_sides_xB]; try (apply IH; exact HM).
  destruct (IH m HM) as [E HM1]. destruct (disj_sides_xM bc rest b1 k1 n1 m) as [r ma]. cbn [fst snd] in E, HM1. subst r.
  destruct (sget_ok (sub_itv_xB bc b1 k1 n1) ma c2 m2 HM1) as [E2 HM2].
  destruct (sget ma c2 m2 (fun _ => sub_itv_xB bc b1 k1 n1 c2 m2)) as [v2 mb]. cbn [fst snd] in E2, HM2. subst v2.
  destruct (sget_ok (sub_itv_xB bc b1 k1 n1) mb c1 m1 HM2) as [E1 HM3].
  destruct (sget mb c1 m1 (fun _ => sub_itv_xB bc b1 k1 n1 c1 m1)) as [v1 mc]. cbn [fst snd] in E1, HM3 |- *. subst v1.
  split; [reflexivity|exact HM3].
Qed.
Lemma SMOK_nil : forall f, SMOK f []. Proof. intros f c n v H. destruct H. Qed.
Lemma mk_sprepM_eq : forall bc b1 k1 n1, mk_sprepM bc b1 k1 n1 = mk_sprepB bc b1 k1 n1.
Proof.
  intros. unfold mk_sprepM, mk_sprepB.
  rewrite (proj1 (disj_sides_xM_eq bc (bc_fk bc) b1 k1 n1 [] (SMOK_nil _))).
  destruct n1; try reflexivity. rewrite (proj1 (disj_sidesM_eq bc (bc_fk bc) b1 k1 _ [] (SMOK_nil _))). reflexivity.
Qed.
Lemma zlit64_id : forall z, 0 <= z < two64 -> zlit64 z = z.
Proof.
  intros z [H0 H1]. unfold zlit64.
  replace (Z.leb 0 z) with true by (symmetry; apply Z.leb_le; exact H0).
  replace (Z.ltb z two64) with true by (symmetry; apply Z.ltb_lt; exact H1). reflexivity.
Qed.
Lemma tD_eq : forall bc b1 k1 n1 mx c m,
  0 <= n1 < two64 -> SMOK (sub_itv_xB bc b1 k1 (ELit n1)) mx -> tD bc b1 k1 n1 mx c m = sub_itvB bc b1 k1 n1 c m.
Proof.
  intros bc b1 k1 n1 mx c m [H0 H1] HM. unfold tD, fastp, sub_itvB.
  match goal with |- (if ?c then true else _) = (if ?d then true else _) => change d with c; destruct c; [reflexivity|] end.
  destruct (sm_get mx c m) as [v|] eqn:E; [|reflexivity].
  rewrite (HM _ _ _ (sm_get_In _ _ _ _ E)). unfold sub_itv_xB.
  replace (Z.leb 0 n1) with true by (symmetry; apply Z.leb_le; exact H0).
  replace (Z.ltb n1 two64) with true by (symmetry; apply Z.ltb_lt; exact H1). reflexivity.
Qed.
Lemma disj_sidesD_eq : forall bc kn b1 k1 n1 mx,
  0 <= n1 < two64 -> SMOK (sub_itv_xB bc b1 k1 (ELit n1)) mx -> disj_sidesD bc kn b1 k1 n1 mx = disj_sidesB bc kn b1 k1 n1.
Proof.
  intros bc kn b1 k1 n1 mx Hn HM. induction kn as [|K rest IH]; [reflexivity|].
  destruct K; cbn [disj_sidesD disj_sidesB]; try exact IH. rewrite IH, !(tD_eq _ _ _ _ _ _ _ Hn HM). reflexivity.
Qed.
Lemma mk_sprepM2_eq : forall bc b1 k1 n1, mk_sprepM2 bc b1 k1 n1 = mk_sprepB bc b1 k1 n1.
Proof.
  intros bc b1 k1 n1. unfold mk_sprepM2. destruct n1 as [z1| | | | | | |]; try apply mk_sprepM_eq.
  destruct (Z.leb 0 z1) eqn:E0; [|apply mk_sprepM_eq]. destruct (Z.ltb z1 two64) eqn:E1; [|apply mk_sprepM_eq].
  apply Z.leb_le in E0. apply Z.ltb_lt in E1.
  destruct (disj_sides_xM_eq bc (bc_fk bc) b1 k1 (ELit z1) [] (SMOK_nil _)) as [EX HM].
  destruct (disj_sides_xM bc (bc_fk bc) b1 k1 (ELit z1) []) as [Dx mx]. cbn [fst snd] in EX, HM. subst Dx.
  unfold mk_sprepB. rewrite (zlit64_id z1 (conj E0 E1)). rewrite (disj_sidesD_eq _ _ _ _ _ _ (conj E0 E1) HM). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma xq_eval_ok : forall bc b1 c m k1 w,
  xq_eval (mk_xq bc b1 c m) k1 (wlit_nw bc w) (wlit_c w) = xinside0B bc b1 k1 (ELit (Z.of_nat w)) (a_base c) (a_off c) m.
Proof.
  intros bc b1 c m k1 w. unfold xinside0B. rewrite !lin_ge0B_staged.
  rewrite (xt_lin_k b1 k1), (xt_lin_k (a_base c) (a_off c)), (xt_lin_k2 (a_base c) (a_off c) m), (xt_lin_lit b1 k1 (Z.of_nat w)).
  unfold xq_eval, mk_xq, wlit_nw, wlit_c. cbn [xq_nw xq_stA xq_cA xq_stB xq_cB xt_nowrapB].
  replace (xt_const [(b1, 0)] - xt_const [(a_base c, a_off c)] + k1) with (xt_const [(b1, k1)] - xt_const [(a_base c, a_off c)]) by (cbn [xt_const]; lia).
  replace (xt_const [(a_base c, a_off c); (m, 0)] - xt_const [(b1, 0)] - k1 - xt_const [(ELit (Z.of_nat w), 0)])
     with (xt_const [(a_base c, a_off c); (m, 0)] - xt_const [(b1, k1); (ELit (Z.of_nat w), 0)]) by (cbn [xt_const]; lia).
  destruct (lin_nowrapRB bc b1); destruct (lin_nowrapRB bc (a_base c)); destruct (lin_nowrapRB bc m);
    destruct (lin_nowrapRB bc (ELit (Z.of_nat w))); cbn [andb];
    repeat match goal with |- context [ge0_eval ?a ?b] => destruct (ge0_eval a b) end; reflexivity.
Qed.
Definition XL_OK (bc : bctx) (b1 : expr) (xl : list (saddr * expr * xq)) : Prop :=
  forall c m q, In (c, m, q) xl -> q = mk_xq bc b1 c m.
Lemma xs_get_In : forall l c m q, xs_get l c m = Some q -> In (c, m, q) l.
Proof.
  induction l as [|[[c' m'] q'] r IH]; cbn [xs_get]; intros c m q H; [discriminate|].
  destruct (expr_eqb (a_base c) (a_base c')) eqn:E1; [|right; apply IH; exact H].
  destruct (Z.eqb (a_off c) (a_off c')) eqn:E2; [|right; apply IH; exact H].
  destruct (expr_eqb m m') eqn:E3; [|right; apply IH; exact H].
  injection H as <-. apply p_expr_eqb_eq in E1. apply Z.eqb_eq in E2. apply p_expr_eqb_eq in E3.
  left. destruct c, c'. cbn [a_base a_off] in E1, E2. subst. reflexivity.
Qed.
Lemma tXq_ok : forall bc b1 k1 w xl c m, XL_OK bc b1 xl ->
  fst (tXq bc b1 k1 w (wlit_nw bc w) (wlit_c w) xl c m) = sub_itv_xB bc b1 k1 (ELit (Z.of_nat w)) c m
  /\ XL_OK bc b1 (snd (tXq bc b1 k1 w (wlit_nw bc w) (wlit_c w) xl c m)).
Proof.
  intros bc b1 k1 w xl c m HX. unfold tXq. destruct (shares_var b1 (a_base c)) eqn:HS; [|split; [reflexivity|exact HX]].
  assert (E : forall q, q = mk_xq bc b1 c m -> xq_eval q k1 (wlit_nw bc w) (wlit_c w) = sub_itv_xB bc b1 k1 (ELit (Z.of_nat w)) c m).
  { intros q ->. rewrite xq_eval_ok. unfold sub_itv_xB, xinsideB. rewrite HS. reflexivity. }
  destruct (xs_get xl c m) as [q|] eqn:EG; cbn [fst snd].
  - split; [apply E; exact (HX _ _ _ (xs_get_In _ _ _ _ EG)) | exact HX].
  - split; [apply E; reflexivity|]. intros c' m' q' [H|H]; [injection H as <- <- <-; reflexivity | exact (HX _ _ _ H)].
Qed.
Lemma disj_sides_xQ_eq : forall bc kn b1 k1 w sm xl,
  SMOK (sub_itv_xB bc b1 k1 (ELit (Z.of_nat w))) sm -> XL_OK bc b1 xl ->
  fst (fst (disj_sides_xQ bc kn b1 k1 w (wlit_nw bc w) (wlit_c w) sm xl)) = disj_sides_xB bc kn b1 k1 (ELit (Z.of_nat w))
  /\ SMOK (sub_itv_xB bc b1 k1 (ELit (Z.of_nat w))) (snd (fst (disj_sides_xQ bc kn b1 k1 w (wlit_nw bc w) (wlit_c w) sm xl)))
  /\ XL_OK bc b1 (snd (disj_sides_xQ bc kn b1 k1 w (wlit_nw bc w) (wlit_c w) sm xl)).
Proof.
  intros bc kn b1 k1 w. induction kn as [|K rest IH]; intros sm xl HM HX; [repeat split; assumption|].
  destruct K as [a ww v|a l|a l bk|lo hi|e1 mm|e' lo hi|a n|c1 m1 c2 m2|a l c|a l]; cbn [disj_sides_xQ disj_sides_xB]; try (apply IH; assumption).
  destruct (IH sm xl HM HX) as (E & HMa & HXa).
  destruct (disj_sides_xQ bc rest b1 k1 w (wlit_nw bc w) (wlit_c w) sm xl) as [[r sma] xla]. cbn [fst snd] in E, HMa, HXa. subst r.
  (* [comment removed for export] *)
  assert (STEP : forall sm0 xl0 c m, SMOK (sub_itv_xB bc b1 k1 (ELit (Z.of_nat w))) sm0 -> XL_OK bc b1 xl0 ->
            let res := match sm_get sm0 c m with
                       | Some v => (v, sm0, xl0)
                       | None => let '(v, xl') := tXq bc b1 k1 w (wlit_nw bc w) (wlit_c w) xl0 c m in (v, (c, m, v) :: sm0, xl')
                       end in
            fst (fst res) = sub_itv_xB bc b1 k1 (ELit (Z.of_nat w)) c m
            /\ SMOK (sub_itv_xB bc b1 k1 (ELit (Z.of_nat w))) (snd (fst res)) /\ XL_OK bc b1 (snd res)).
  { intros sm0 xl0 c m HM0 HX0. cbv zeta. destruct (sm_get sm0 c m) as [v|] eqn:EG; cbn [fst snd].
    - split; [exact (HM0 _ _ _ (sm_get_In _ _ _ _ EG))|]. split; assumption.
    - destruct (tXq_ok bc b1 k1 w xl0 c m HX0) as [Et HXt].
      destruct (tXq bc b1 k1 w (wlit_nw bc w) (wlit_c w) xl0 c m) as [v xl']. cbn [fst snd] in Et, HXt |- *.
      split; [exact Et|]. split; [|exact HXt].
      intros c' m' v' [H|H]; [injection H as <- <- <-; exact Et | exact (HM0 _ _ _ H)]. }
  destruct (STEP sma xla c2 m2 HMa HXa) as (E2 & HMb & HXb). cbv zeta in E2, HMb, HXb.
  destruct (match sm_get sma c2 m2 with Some v => (v, sma, xla) | None => _ end) as [[v2 smb] xlb]. cbn [fst snd] in E2, HMb, HXb. subst v2.
  destruct (STEP smb xlb c1 m1 HMb HXb) as (E1 & HMc & HXc). cbv zeta in E1, HMc, HXc.
  destruct (match sm_get smb c1 m1 with Some v => (v, smb, xlb) | None => _ end) as [[v1 smc] xlc]. cbn [fst snd] in E1, HMc, HXc |- *. subst v1.
  repeat split; assumption.
Qed.
Definition XC_OK (bc : bctx) (xc : xcache) : Prop := forall id b l, In (id, b, l) xc -> XL_OK bc b l.
Lemma XL_OK_nil : forall bc b, XL_OK bc b []. Proof. intros bc b c m q []. Qed.
Lemma xc_sides_ok : forall bc xc bid b1, XC_OK bc xc -> XL_OK bc b1 (xc_sides xc bid b1).
Proof.
  intros bc xc bid b1. induction xc as [|[[id b] l] r IH]; intros HC; [apply XL_OK_nil|].
  cbn [xc_sides]. destruct (Pos.eqb bid id).
  - destruct (expr_eqb b1 b) eqn:E; [|apply XL_OK_nil]. apply p_expr_eqb_eq in E. subst b. exact (HC _ _ _ (or_introl eq_refl)).
  - apply IH. intros id' b' l' H. exact (HC _ _ _ (or_intror H)).
Qed.
Lemma xc_put_ok : forall bc xc bid b1 l, XC_OK bc xc -> XL_OK bc b1 l -> XC_OK bc (xc_put xc bid b1 l).
Proof.
  intros bc xc bid b1 l. induction xc as [|[[id b] l0] r IH]; intros HC HL.
  - intros id' b' l' [H|[]]. injection H as <- <- <-. exact HL.
  - cbn [xc_put]. destruct (Pos.eqb bid id).
    + intros id' b' l' [H|H]; [injection H as <- <- <-; exact HL | exact (HC _ _ _ (or_intror H))].
    + intros id' b' l' [H|H]; [exact (HC _ _ _ (or_introl H))|].
      exact (IH (fun i bb ll Hin => HC i bb ll (or_intror Hin)) HL _ _ _ H).
Qed.
Lemma mk_sprepQ_eq : forall bc bid b1 k1 w xc, XC_OK bc xc ->
  fst (mk_sprepQ bc bid b1 k1 w xc) = mk_sprepB bc b1 k1 (elen w) /\ XC_OK bc (snd (mk_sprepQ bc bid b1 k1 w xc)).
Proof.
  intros bc bid b1 k1 w xc HC. unfold mk_sprepQ. destruct (Nat.leb w 8) eqn:EW; [|split; [apply mk_sprepM2_eq|exact HC]].
  apply Nat.leb_le in EW.
  assert (Hw : 0 <= Z.of_nat w < two64) by (unfold two64; lia).
  destruct (disj_sides_xQ_eq bc (bc_fk bc) b1 k1 w [] (xc_sides xc bid b1) (SMOK_nil _) (xc_sides_ok bc xc bid b1 HC)) as (EX & HM & HX).
  destruct (disj_sides_xQ bc (bc_fk bc) b1 k1 w (wlit_nw bc w) (wlit_c w) [] (xc_sides xc bid b1)) as [[Dx mx] xl]. cbn [fst snd] in EX, HM, HX |- *.
  subst Dx. split; [|apply xc_put_ok; assumption].
  unfold mk_sprepB, elen. rewrite (zlit64_id _ Hw), (disj_sidesD_eq _ _ _ _ _ _ Hw HM). reflexivity.
Qed.
Lemma mk_stxsQ_eq : forall bc log t xc, XC_OK bc xc ->
  fst (mk_stxsQ bc log t xc) = mk_stxs bc log t /\ XC_OK bc (snd (mk_stxsQ bc log t xc)).
Proof.
  intros bc log. induction log as [|[a w v] older IH]; intros t xc HC; [split; [reflexivity|exact HC]|].
  cbn [mk_stxsQ mk_stxs]. destruct (IH t xc HC) as [E HC1].
  destruct (mk_stxsQ bc older t xc) as [[sxs t1] xc1]. cbn [fst snd] in E, HC1. rewrite <- E.
  destruct (intern bc t1 (a_base a)) as [[bid bi] t2].
  destruct (mk_sprepQ_eq bc bid (a_base a) (a_off a) w xc1 HC1) as [ES HC2].
  destruct (mk_sprepQ bc bid (a_base a) (a_off a) w xc1) as [sp xc2]. cbn [fst snd] in ES, HC2 |- *. subst sp.
  split; [reflexivity|exact HC2].
Qed.
(* [comment removed for export] *)
Lemma st_find_In : forall t c m id, st_find t c m = Some id -> In (id, (c, m)) t.
Proof.
  induction t as [|[id' [c' m']] r IH]; cbn [st_find]; intros c m id H; [discriminate|].
  destruct (expr_eqb m m') eqn:E3; [|right; apply IH; exact H].
  destruct (Z.eqb (a_off c) (a_off c')) eqn:E2; [|right; apply IH; exact H].
  destruct (expr_eqb (a_base c) (a_base c')) eqn:E1; [|right; apply IH; exact H].
  injection H as <-. apply p_expr_eqb_eq in E1. apply Z.eqb_eq in E2. apply p_expr_eqb_eq in E3.
  left. destruct c, c'. cbn [a_base a_off] in E1, E2. subst. reflexivity.
Qed.
Definition STOK (t : stab) (next : positive) : Prop :=
  (forall i sd, In (i, sd) t -> (i < next)%positive) /\ (forall i sd sd', In (i, sd) t -> In (i, sd') t -> sd = sd').
Lemma st_intern_ok : forall t next c m i t' next',
  STOK t next -> st_intern t next c m = (i, t', next') ->
  STOK t' next' /\ (forall p, In p t -> In p t') /\ In (i, (c, m)) t'.
Proof.
  intros t next c m i t' next' [T1 T2] H. unfold st_intern in H. destruct (st_find t c m) as [id|] eqn:EF.
  - injection H as <- <- <-. split; [split; assumption|]. split; [auto|]. exact (st_find_In _ _ _ _ EF).
  - injection H as <- <- <-. split; [|split; [intros p Hp; right; exact Hp | left; reflexivity]].
    split.
    + intros i sd [Hi|Hi]; [injection Hi as <- <-; apply Pos.lt_succ_diag_r | apply Pos.lt_lt_succ; exact (T1 _ _ Hi)].
    + intros i sd sd' [Hi|Hi] [Hj|Hj].
      * congruence.
      * injection Hi as <- <-. pose proof (T1 _ _ Hj) as X. exfalso. exact (Pos.lt_irrefl _ X).
      * injection Hj as <- <-. pose proof (T1 _ _ Hi) as X. exfalso. exact (Pos.lt_irrefl _ X).
      * exact (T2 _ _ _ Hi Hj).
Qed.
Definition kd_erase (x : (positive * side) * (positive * side)) : side * side := (snd (fst x), snd (snd x)).
Lemma mk_kdl_ok : forall fk t next kd t' next',
  STOK t next -> mk_kdl fk t next = (kd, t', next') ->
  STOK t' next' /\ (forall p, In p t -> In p t') /\ map kd_erase kd = kd_pairs fk
  /\ (forall x, In x kd -> In (fst x) t' /\ In (snd x) t').
Proof.
  induction fk as [|K rest IH]; intros t next kd t' next' HT H.
  - cbn in H. injection H as <- <- <-. split; [exact HT|]. split; [auto|]. split; [reflexivity|]. intros x [].
  - destruct K as [a w v|a l|a l bk|lo hi|e1 mm|e' lo hi|a n|c1 m1 c2 m2|a l c|a l]; cbn [mk_kdl kd_pairs flat_map app] in H |- *;
      try (exact (IH _ _ _ _ _ HT H)).
    destruct (st_intern t next c1 m1) as [[i1 t1] n1] eqn:E1.
    destruct (st_intern t1 n1 c2 m2) as [[i2 t2] n2] eqn:E2.
    destruct (mk_kdl rest t2 n2) as [[l t3] n3] eqn:E3. injection H as <- <- <-.
    destruct (st_intern_ok _ _ _ _ _ _ _ HT E1) as (HT1 & Hi1 & Hin1).
    destruct (st_intern_ok _ _ _ _ _ _ _ HT1 E2) as (HT2 & Hi2 & Hin2).
    destruct (IH _ _ _ _ _ HT2 E3) as (HT3 & Hi3 & Hmap & Hall).
    split; [exact HT3|]. split; [intros p Hp; apply Hi3, Hi2, Hi1; exact Hp|].
    split; [cbn [map kd_erase fst snd]; rewrite Hmap; reflexivity|].
    intros x [Hx|Hx]; [subst x; cbn [fst snd]; split; [apply Hi3, Hi2; exact Hin1 | apply Hi3; exact Hin2] | exact (Hall x Hx)].
Qed.
Lemma disj_sidesB_dsG : forall bc fk b1 k1 n1, disj_sidesB bc fk b1 k1 n1 = dsG (sub_itvB bc b1 k1 n1) (kd_pairs fk).
Proof.
  intros bc fk b1 k1 n1. induction fk as [|K rest IH]; [reflexivity|].
  destruct K; cbn [disj_sidesB kd_pairs flat_map app dsG]; try exact IH. rewrite IH. reflexivity.
Qed.
Lemma disj_sides_xB_dsG : forall bc fk b1 k1 n1, disj_sides_xB bc fk b1 k1 n1 = dsG (sub_itv_xB bc b1 k1 n1) (kd_pairs fk).
Proof.
  intros bc fk b1 k1 n1. induction fk as [|K rest IH]; [reflexivity|].
  destruct K; cbn [disj_sides_xB kd_pairs flat_map app dsG]; try exact IH. rewrite IH. reflexivity.
Qed.
Definition VMOK (f : saddr -> expr -> bool) (tbl : stab) (vm : list (positive * bool)) : Prop :=
  forall i v, In (i, v) vm -> forall c m, In (i, (c, m)) tbl -> v = f c m.
Lemma dsI_eq : forall (ST : Type) (g : ST -> positive -> saddr -> expr -> bool * ST) (f : saddr -> expr -> bool) (INV : ST -> Prop) (tbl : stab),
  (forall st i c m, In (i, (c, m)) tbl -> INV st -> fst (g st i c m) = f c m /\ INV (snd (g st i c m))) ->
  (forall i sd sd', In (i, sd) tbl -> In (i, sd') tbl -> sd = sd') ->
  forall kd vm st, (forall x, In x kd -> In (fst x) tbl /\ In (snd x) tbl) -> VMOK f tbl vm -> INV st ->
  fst (fst (dsI ST g kd vm st)) = dsG f (map kd_erase kd)
  /\ VMOK f tbl (snd (fst (dsI ST g kd vm st))) /\ INV (snd (dsI ST g kd vm st)).
Proof.
  intros ST g f INV tbl Hg Hfun.
  assert (VG : forall vm st i c m, In (i, (c, m)) tbl -> VMOK f tbl vm -> INV st ->
            fst (fst (vget ST g vm st i c m)) = f c m /\ VMOK f tbl (snd (fst (vget ST g vm st i c m))) /\ INV (snd (vget ST g vm st i c m))).
  { intros vm st i c m Hin HV HI. unfold vget. destruct (alookupP vm i) as [v|] eqn:EL; cbn [fst snd].
    - split; [exact (HV _ _ (alookupP_In _ _ _ _ EL) _ _ Hin)|]. split; assumption.
    - destruct (Hg st i c m Hin HI) as [Ef HI']. destruct (g st i c m) as [v st']. cbn [fst snd] in Ef, HI' |- *.
      split; [exact Ef|]. split; [|exact HI'].
      intros i' v' [H|H] c' m' Hin'; [|exact (HV _ _ H _ _ Hin')].
      injection H as <- <-. pose proof (Hfun _ _ _ Hin Hin') as X. injection X as <- <-. exact Ef. }
  induction kd as [|[[i1 [c1 m1]] [i2 [c2 m2]]] rest IH]; intros vm st Hall HV HI; [repeat split; assumption|].
  cbn [dsI map kd_erase fst snd dsG].
  destruct (IH vm st (fun x Hx => Hall x (or_intror Hx)) HV HI) as (E & HVa & HIa).
  destruct (dsI ST g rest vm st) as [[r va] sa]. cbn [fst snd] in E, HVa, HIa. subst r.
  destruct (Hall _ (or_introl eq_refl)) as [Hin1 Hin2]. cbn [fst snd] in Hin1, Hin2.
  destruct (VG va sa i2 c2 m2 Hin2 HVa HIa) as (E2 & HVb & HIb).
  destruct (vget ST g va sa i2 c2 m2) as [[v2 vb] sb]. cbn [fst snd] in E2, HVb, HIb. subst v2.
  destruct (VG vb sb i1 c1 m1 Hin1 HVb HIb) as (E1 & HVc & HIc).
  destruct (vget ST g vb sb i1 c1 m1) as [[v1 vc] sc]. cbn [fst snd] in E1, HVc, HIc |- *. subst v1.
  repeat split; assumption.
Qed.
Definition XLI_OK (bc : bctx) (tbl : stab) (b1 : expr) (xl : xli) : Prop :=
  forall i q, In (i, q) xl -> forall c m, In (i, (c, m)) tbl -> q = mk_xq bc b1 c m.
Lemma gX_ok : forall bc tbl b1 k1 w,
  (forall i sd sd', In (i, sd) tbl -> In (i, sd') tbl -> sd = sd') ->
  forall xl i c m, In (i, (c, m)) tbl -> XLI_OK bc tbl b1 xl ->
  fst (gX bc b1 k1 w (wlit_nw bc w) (wlit_c w) xl i c m) = sub_itv_xB bc b1 k1 (ELit (Z.of_nat w)) c m
  /\ XLI_OK bc tbl b1 (snd (gX bc b1 k1 w (wlit_nw bc w) (wlit_c w) xl i c m)).
Proof.
  intros bc tbl b1 k1 w Hfun xl i c m Hin HX. unfold gX. destruct (shares_var b1 (a_base c)) eqn:HS; [|split; [reflexivity|exact HX]].
  assert (E : forall q, q = mk_xq bc b1 c m -> xq_eval q k1 (wlit_nw bc w) (wlit_c w) = sub_itv_xB bc b1 k1 (ELit (Z.of_nat w)) c m).
  { intros q ->. rewrite xq_eval_ok. unfold sub_itv_xB, xinsideB. rewrite HS. reflexivity. }
  destruct (alookupP xl i) as [q|] eqn:EG; cbn [fst snd].
  - split; [apply E; exact (HX _ _ (alookupP_In _ _ _ _ EG) _ _ Hin) | exact HX].
  - split; [apply E; reflexivity|]. intros i' q' [H|H] c' m' Hin'; [|exact (HX _ _ H _ _ Hin')].
    injection H as <- <-. pose proof (Hfun _ _ _ Hin Hin') as X. injection X as <- <-. reflexivity.
Qed.
Lemma gD_ok : forall bc tbl b1 k1 n1 vmx, 0 <= n1 < two64 -> VMOK (sub_itv_xB bc b1 k1 (ELit n1)) tbl vmx ->
  forall (u : unit) i c m, In (i, (c, m)) tbl -> True ->
  fst (gD bc b1 k1 n1 vmx u i c m) = sub_itvB bc b1 k1 n1 c m /\ True.
Proof.
  intros bc tbl b1 k1 n1 vmx [H0 H1] HV u i c m Hin _. split; [|exact I]. unfold gD, fastp, sub_itvB. cbn [fst].
  match goal with |- (if ?c then true else _) = (if ?d then true else _) => change d with c; destruct c; [reflexivity|] end.
  destruct (alookupP vmx i) as [v|] eqn:E; [|reflexivity].
  rewrite (HV _ _ (alookupP_In _ _ _ _ E) _ _ Hin). unfold sub_itv_xB.
  replace (Z.leb 0 n1) with true by (symmetry; apply Z.leb_le; exact H0).
  replace (Z.ltb n1 two64) with true by (symmetry; apply Z.ltb_lt; exact H1). reflexivity.
Qed.
Definition XCI_OK (bc : bctx) (tbl : stab) (xc : xcacheI) : Prop := forall id b l, In (id, b, l) xc -> XLI_OK bc tbl b l.
Lemma xcI_sides_ok : forall bc tbl xc bid b1, XCI_OK bc tbl xc -> XLI_OK bc tbl b1 (xcI_sides xc bid b1).
Proof.
  intros bc tbl xc bid b1. induction xc as [|[[id b] l] r IH]; intros HC; [intros i q []|].
  cbn [xcI_sides]. destruct (Pos.eqb bid id).
  - destruct (expr_eqb b1 b) eqn:E; [|intros i q []]. apply p_expr_eqb_eq in E. subst b. exact (HC _ _ _ (or_introl eq_refl)).
  - apply IH. intros id' b' l' H. exact (HC _ _ _ (or_intror H)).
Qed.
Lemma xcI_put_ok : forall bc tbl xc bid b1 l, XCI_OK bc tbl xc -> XLI_OK bc tbl b1 l -> XCI_OK bc tbl (xcI_put xc bid b1 l).
Proof.
  intros bc tbl xc bid b1 l. induction xc as [|[[id b] l0] r IH]; intros HC HL.
  - intros id' b' l' [H|[]]. injection H as <- <- <-. exact HL.
  - cbn [xcI_put]. destruct (Pos.eqb bid id).
    + intros id' b' l' [H|H]; [injection H as <- <- <-; exact HL | exact (HC _ _ _ (or_intror H))].
    + intros id' b' l' [H|H]; [exact (HC _ _ _ (or_introl H))|].
      exact (IH (fun i bb ll Hin => HC i bb ll (or_intror Hin)) HL _ _ _ H).
Qed.
Lemma mk_sprepI_eq : forall bc kd tbl bid b1 k1 w xc,
  (forall i sd sd', In (i, sd) tbl -> In (i, sd') tbl -> sd = sd') ->
  (forall x, In x kd -> In (fst x) tbl /\ In (snd x) tbl) -> map kd_erase kd = kd_pairs (bc_fk bc) ->
  XCI_OK bc tbl xc ->
  fst (mk_sprepI bc kd bid b1 k1 w xc) = mk_sprepB bc b1 k1 (elen w) /\ XCI_OK bc tbl (snd (mk_sprepI bc kd bid b1 k1 w xc)).
Proof.
  intros bc kd tbl bid b1 k1 w xc Hfun Hall Hmap HC. unfold mk_sprepI.
  destruct (Nat.leb w 8) eqn:EW; [|split; [apply mk_sprepM2_eq|exact HC]]. apply Nat.leb_le in EW.
  assert (Hw : 0 <= Z.of_nat w < two64) by (unfold two64; lia).
  destruct (dsI_eq xli (gX bc b1 k1 w (wlit_nw bc w) (wlit_c w)) (sub_itv_xB bc b1 k1 (ELit (Z.of_nat w))) (XLI_OK bc tbl b1) tbl
              (gX_ok bc tbl b1 k1 w Hfun) Hfun kd [] (xcI_sides xc bid b1) Hall (fun i v H => match H with end) (xcI_sides_ok bc tbl xc bid b1 HC))
    as (EX & HVx & HX).
  destruct (dsI xli (gX bc b1 k1 w (wlit_nw bc w) (wlit_c w)) kd [] (xcI_sides xc bid b1)) as [[Dx vmx] xl]. cbn [fst snd] in EX, HVx, HX.
  destruct (dsI_eq unit (gD bc b1 k1 (Z.of_nat w) vmx) (sub_itvB bc b1 k1 (Z.of_nat w)) (fun _ => True) tbl
              (gD_ok bc tbl b1 k1 (Z.of_nat w) vmx Hw HVx) Hfun kd [] tt Hall (fun i v H => match H with end) I) as (ED & _ & _).
  destruct (dsI unit (gD bc b1 k1 (Z.of_nat w) vmx) kd [] tt) as [[D vmd] u]. cbn [fst snd] in ED |- *.
  split; [|apply xcI_put_ok; assumption].
  unfold mk_sprepB, elen. rewrite (zlit64_id _ Hw), disj_sidesB_dsG, disj_sides_xB_dsG, <- Hmap, <- EX, <- ED. reflexivity.
Qed.
Lemma mk_stxsI_eq : forall bc kd tbl log t xc,
  (forall i sd sd', In (i, sd) tbl -> In (i, sd') tbl -> sd = sd') ->
  (forall x, In x kd -> In (fst x) tbl /\ In (snd x) tbl) -> map kd_erase kd = kd_pairs (bc_fk bc) ->
  XCI_OK bc tbl xc ->
  fst (mk_stxsI bc kd log t xc) = mk_stxs bc log t /\ XCI_OK bc tbl (snd (mk_stxsI bc kd log t xc)).
Proof.
  intros bc kd tbl log t xc Hfun Hall Hmap. revert t xc.
  induction log as [|[a w v] older IH]; intros t xc HC; [split; [reflexivity|exact HC]|].
  cbn [mk_stxsI mk_stxs]. destruct (IH t xc HC) as [E HC1].
  destruct (mk_stxsI bc kd older t xc) as [[sxs t1] xc1]. cbn [fst snd] in E, HC1. rewrite <- E.
  destruct (intern bc t1 (a_base a)) as [[bid bi] t2].
  destruct (mk_sprepI_eq bc kd tbl bid (a_base a) (a_off a) w xc1 Hfun Hall Hmap HC1) as [ES HC2].
  destruct (mk_sprepI bc kd bid (a_base a) (a_off a) w xc1) as [sp xc2]. cbn [fst snd] in ES, HC2 |- *. subst sp.
  split; [reflexivity|exact HC2].
Qed.
Lemma mk_stxsM_eq : forall bc log t, mk_stxsM bc log t = mk_stxs bc log t.
Proof.
  intros bc log. induction log as [|[a w v] older IH]; intros t; [reflexivity|].
  cbn [mk_stxsM mk_stxs]. rewrite IH. destruct (mk_stxs bc older t) as [sxs t1].
  destruct (intern bc t1 (a_base a)) as [[bid bi] t2]. rewrite mk_sprepM2_eq. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sides_eqb_eq : forall l1 l2, sides_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|[c1 m1] r1 IH]; intros [|[c2 m2] r2] H; cbn [sides_eqb] in H; try discriminate; [reflexivity|].
  destruct (expr_eqb (a_base c1) (a_base c2)) eqn:E1; [|discriminate].
  destruct (Z.eqb (a_off c1) (a_off c2)) eqn:E2; [|discriminate].
  destruct (expr_eqb m1 m2) eqn:E3; [|discriminate].
  apply p_expr_eqb_eq in E1. apply Z.eqb_eq in E2. apply p_expr_eqb_eq in E3. rewrite (IH _ H).
  destruct c1, c2. cbn [a_base a_off] in E1, E2. subst. reflexivity.
Qed.
Lemma ct_find_In : forall t D Dx id, ct_find t D Dx = Some id -> In (id, (D, Dx)) t.
Proof.
  induction t as [|[id' [D' Dx']] r IH]; cbn [ct_find]; intros D Dx id H; [discriminate|].
  destruct (sides_eqb D D') eqn:E1; [|right; apply IH; exact H].
  destruct (sides_eqb Dx Dx') eqn:E2; [|right; apply IH; exact H].
  injection H as <-. apply sides_eqb_eq in E1. apply sides_eqb_eq in E2. subst. left. reflexivity.
Qed.
Definition spk (sx : stx) : sides * sides := (sp_D (sx_sp sx), sp_Dx (sx_sp sx)).
Definition CT_OK (t : ctab) (next : positive) : Prop :=
  NoDup (map fst t) /\ forall k x, In (k, x) t -> (k < next)%positive.
Lemma mk_cls_ok : forall sxs t next l t',
  CT_OK t next -> mk_cls sxs t next = (l, t') ->
  map fst l = sxs /\ NoDup (map fst t') /\ (forall p, In p t -> In p t') /\ (forall sx dc, In (sx, dc) l -> In (dc, spk sx) t').
Proof.
  induction sxs as [|sx rest IH]; intros t next l t' [HN HL] H; cbn [mk_cls] in H.
  - injection H as <- <-. split; [reflexivity|]. split; [exact HN|]. split; [auto|]. intros sx dc [].
  - destruct (ct_find t (sp_D (sx_sp sx)) (sp_Dx (sx_sp sx))) as [id|] eqn:EF.
    + destruct (mk_cls rest t next) as [l0 t0] eqn:E0. injection H as <- <-.
      destruct (IH _ _ _ _ (conj HN HL) E0) as (Hm & HN' & Hinc & Hin).
      split; [cbn [map fst]; rewrite Hm; reflexivity|]. split; [exact HN'|]. split; [exact Hinc|].
      intros sx' dc [Hp|Hp]; [|apply Hin; exact Hp]. injection Hp as <- <-.
      apply Hinc. apply ct_find_In. exact EF.
    + destruct (mk_cls rest (t ++ [(next, (sp_D (sx_sp sx), sp_Dx (sx_sp sx)))]) (Pos.succ next)) as [l0 t0] eqn:E0. injection H as <- <-.
      assert (HOK : CT_OK (t ++ [(next, (sp_D (sx_sp sx), sp_Dx (sx_sp sx)))]) (Pos.succ next)).
      { split.
        - rewrite map_app. cbn [map fst]. apply NoDup_app_remove_l with (l := []). cbn [app].
          apply NoDup_rev in HN. rewrite <- (rev_involutive (map fst t ++ [next])). apply NoDup_rev.
          rewrite rev_app_distr. cbn [rev app]. constructor; [|exact HN].
          intros Hc. apply in_rev in Hc. apply in_map_iff in Hc as [[k x] [Hk Hc]]. cbn [fst] in Hk. subst k.
          pose proof (HL _ _ Hc) as Hlt. lia.
        - intros k x Hc. apply in_app_or in Hc as [Hc|[Hc|[]]]; [pose proof (HL _ _ Hc); lia|]. injection Hc as <- <-. lia. }
      destruct (IH _ _ _ _ HOK E0) as (Hm & HN' & Hinc & Hin).
      split; [cbn [map fst]; rewrite Hm; reflexivity|]. split; [exact HN'|].
      split; [intros p Hp; apply Hinc; apply in_or_app; left; exact Hp|].
      intros sx' dc [Hp|Hp]; [|apply Hin; exact Hp]. injection Hp as <- <-.
      apply Hinc. apply in_or_app. right. left. reflexivity.
Qed.
Lemma CT_OK_nil : CT_OK [] xH.
Proof. split; [constructor|intros k x []]. Qed.
Lemma NoDup_key_eq : forall (T : Type) (t : list (positive * T)) k x y, NoDup (map fst t) -> In (k, x) t -> In (k, y) t -> x = y.
Proof.
  intros T t. induction t as [|[k0 x0] r IH]; intros k x y HN Hx Hy; [destruct Hx|].
  cbn [map fst] in HN. apply NoDup_cons_iff in HN as [Hni HN].
  destruct Hx as [Hx|Hx]; destruct Hy as [Hy|Hy].
  - congruence.
  - injection Hx as <- <-. exfalso. apply Hni. apply in_map_iff. exists (k0, y). split; [reflexivity|exact Hy].
  - injection Hy as <- <-. exfalso. apply Hni. apply in_map_iff. exists (k0, x). split; [reflexivity|exact Hx].
  - exact (IH _ _ _ HN Hx Hy).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qf (bc : bctx) (b2 : expr) (k2 : Z) (n2 : expr) (dx : sides * sides) : bool :=
  match n2 with
  | ELit z2 => in_sidesB bc (fst dx) b2 k2 (zlit64 z2)
  | _ => in_sides_xB bc (snd dx) b2 k2 n2
  end.
Definition MOK (bc : bctx) (tbl : ctab) (b2 : expr) (k2 : Z) (n2 : expr) (m : memo) : Prop :=
  forall dc v, In (dc, v) m -> forall dx, In (dc, dx) tbl -> v = qf bc b2 k2 n2 dx.
Lemma MOK_nil : forall bc tbl b2 k2 n2, MOK bc tbl b2 k2 n2 []. Proof. intros bc tbl b2 k2 n2 dc v []. Qed.
Lemma mget_ok : forall bc tbl b2 k2 n2 m dc dx (f : unit -> bool),
  NoDup (map fst tbl) -> In (dc, dx) tbl -> MOK bc tbl b2 k2 n2 m -> f tt = qf bc b2 k2 n2 dx ->
  fst (mget dc m f) = qf bc b2 k2 n2 dx /\ MOK bc tbl b2 k2 n2 (snd (mget dc m f)).
Proof.
  intros bc tbl b2 k2 n2 m dc dx f HN Hin HM Hf. unfold mget.
  destruct (alookupP m dc) as [v|] eqn:E; cbn [fst snd].
  - split; [exact (HM _ _ (alookupP_In _ _ _ _ E) _ Hin) | exact HM].
  - split; [exact Hf|]. intros dc' v' [H|H] dx' Hin'; [|exact (HM _ _ H _ Hin')].
    injection H as <- <-. rewrite Hf. f_equal. exact (NoDup_key_eq _ _ _ _ _ HN Hin Hin').
Qed.

Lemma rapM_eq : forall bc tbl sp dc b1 k1 z1 br2 b2 k2 n2 m,
  NoDup (map fst tbl) -> In (dc, (sp_D sp, sp_Dx sp)) tbl -> MOK bc tbl b2 k2 n2 m ->
  fst (rapM bc sp dc (mk_eh bc br2 b2 k2 n2) b1 k1 (ELit z1) br2 b2 k2 n2 m) = ranges_apart_pcB bc sp b1 k1 (ELit z1) br2 b2 k2 n2
  /\ MOK bc tbl b2 k2 n2 (snd (rapM bc sp dc (mk_eh bc br2 b2 k2 n2) b1 k1 (ELit z1) br2 b2 k2 n2 m)).
Proof.
  intros bc tbl sp dc b1 k1 z1 br2 b2 k2 n2 m HN Hin HM.
  unfold rapM, ranges_apart_pcB. destruct n2 as [z2| | | | | | |].
  - cbv zeta.
    match goal with |- context [if ?c then (true, m) else _] => destruct c; [split; [reflexivity|exact HM]|] end.
    destruct (mget_ok bc tbl b2 k2 (ELit z2) m dc _ (fun _ => in_sidesB bc (sp_D sp) b2 k2 (zlit64 z2)) HN Hin HM eq_refl) as [E HM'].
    destruct (mget dc m _) as [v m']. cbn [fst snd] in E, HM'. unfold qf in E. cbn [fst] in E. subst v.
    destruct (in_sidesB bc (sp_D sp) b2 k2 (zlit64 z2)); cbn [fst snd]; split; try reflexivity; exact HM'.
  - cbn [mk_eh eh_h2 eh_e2].
    match goal with |- context [if ?c then (true, m) else _] =>
      match goal with |- context [if ?d then true else if in_sides_xB _ _ _ _ _ then _ else _] =>
        assert (EC : c = d) by (destruct (sp_rng sp) as [[? ?]|]; [|reflexivity]; destruct br2 as [[? ?]|]; [|reflexivity];
                                destruct (sp_h1 sp); [|reflexivity]; destruct (xhiB bc _); reflexivity);
        rewrite EC; destruct d; [split; [reflexivity|exact HM]|] end end.
    match goal with |- context [mget dc m ?f] =>
      destruct (mget_ok bc tbl b2 k2 _ m dc _ f HN Hin HM eq_refl) as [E HM']; destruct (mget dc m f) as [v m'] end.
    cbn [fst snd] in E, HM'. unfold qf in E. cbn [snd] in E. subst v.
    match goal with |- context [in_sides_xB ?a ?b ?c ?d ?e] => destruct (in_sides_xB a b c d e) end; cbn [fst snd]; split; try reflexivity; exact HM'.
  - cbn [mk_eh eh_h2 eh_e2].
    match goal with |- context [if ?c then (true, m) else _] =>
      match goal with |- context [if ?d then true else if in_sides_xB _ _ _ _ _ then _ else _] =>
        assert (EC : c = d) by (destruct (sp_rng sp) as [[? ?]|]; [|reflexivity]; destruct br2 as [[? ?]|]; [|reflexivity];
                                destruct (sp_h1 sp); [|reflexivity]; destruct (xhiB bc _); reflexivity);
        rewrite EC; destruct d; [split; [reflexivity|exact HM]|] end end.
    match goal with |- context [mget dc m ?f] =>
      destruct (mget_ok bc tbl b2 k2 _ m dc _ f HN Hin HM eq_refl) as [E HM']; destruct (mget dc m f) as [v m'] end.
    cbn [fst snd] in E, HM'. unfold qf in E. cbn [snd] in E. subst v.
    match goal with |- context [in_sides_xB ?a ?b ?c ?d ?e] => destruct (in_sides_xB a b c d e) end; cbn [fst snd]; split; try reflexivity; exact HM'.
  - cbn [mk_eh eh_h2 eh_e2].
    match goal with |- context [if ?c then (true, m) else _] =>
      match goal with |- context [if ?d then true else if in_sides_xB _ _ _ _ _ then _ else _] =>
        assert (EC : c = d) by (destruct (sp_rng sp) as [[? ?]|]; [|reflexivity]; destruct br2 as [[? ?]|]; [|reflexivity];
                                destruct (sp_h1 sp); [|reflexivity]; destruct (xhiB bc _); reflexivity);
        rewrite EC; destruct d; [split; [reflexivity|exact HM]|] end end.
    match goal with |- context [mget dc m ?f] =>
      destruct (mget_ok bc tbl b2 k2 _ m dc _ f HN Hin HM eq_refl) as [E HM']; destruct (mget dc m f) as [v m'] end.
    cbn [fst snd] in E, HM'. unfold qf in E. cbn [snd] in E. subst v.
    match goal with |- context [in_sides_xB ?a ?b ?c ?d ?e] => destruct (in_sides_xB a b c d e) end; cbn [fst snd]; split; try reflexivity; exact HM'.
  - cbn [mk_eh eh_h2 eh_e2].
    match goal with |- context [if ?c then (true, m) else _] =>
      match goal with |- context [if ?d then true else if in_sides_xB _ _ _ _ _ then _ else _] =>
        assert (EC : c = d) by (destruct (sp_rng sp) as [[? ?]|]; [|reflexivity]; destruct br2 as [[? ?]|]; [|reflexivity];
                                destruct (sp_h1 sp); [|reflexivity]; destruct (xhiB bc _); reflexivity);
        rewrite EC; destruct d; [split; [reflexivity|exact HM]|] end end.
    match goal with |- context [mget dc m ?f] =>
      destruct (mget_ok bc tbl b2 k2 _ m dc _ f HN Hin HM eq_refl) as [E HM']; destruct (mget dc m f) as [v m'] end.
    cbn [fst snd] in E, HM'. unfold qf in E. cbn [snd] in E. subst v.
    match goal with |- context [in_sides_xB ?a ?b ?c ?d ?e] => destruct (in_sides_xB a b c d e) end; cbn [fst snd]; split; try reflexivity; exact HM'.
  - cbn [mk_eh eh_h2 eh_e2].
    match goal with |- context [if ?c then (true, m) else _] =>
      match goal with |- context [if ?d then true else if in_sides_xB _ _ _ _ _ then _ else _] =>
        assert (EC : c = d) by (destruct (sp_rng sp) as [[? ?]|]; [|reflexivity]; destruct br2 as [[? ?]|]; [|reflexivity];
                                destruct (sp_h1 sp); [|reflexivity]; destruct (xhiB bc _); reflexivity);
        rewrite EC; destruct d; [split; [reflexivity|exact HM]|] end end.
    match goal with |- context [mget dc m ?f] =>
      destruct (mget_ok bc tbl b2 k2 _ m dc _ f HN Hin HM eq_refl) as [E HM']; destruct (mget dc m f) as [v m'] end.
    cbn [fst snd] in E, HM'. unfold qf in E. cbn [snd] in E. subst v.
    match goal with |- context [in_sides_xB ?a ?b ?c ?d ?e] => destruct (in_sides_xB a b c d e) end; cbn [fst snd]; split; try reflexivity; exact HM'.
  - cbn [mk_eh eh_h2 eh_e2].
    match goal with |- context [if ?c then (true, m) else _] =>
      match goal with |- context [if ?d then true else if in_sides_xB _ _ _ _ _ then _ else _] =>
        assert (EC : c = d) by (destruct (sp_rng sp) as [[? ?]|]; [|reflexivity]; destruct br2 as [[? ?]|]; [|reflexivity];
                                destruct (sp_h1 sp); [|reflexivity]; destruct (xhiB bc _); reflexivity);
        rewrite EC; destruct d; [split; [reflexivity|exact HM]|] end end.
    match goal with |- context [mget dc m ?f] =>
      destruct (mget_ok bc tbl b2 k2 _ m dc _ f HN Hin HM eq_refl) as [E HM']; destruct (mget dc m f) as [v m'] end.
    cbn [fst snd] in E, HM'. unfold qf in E. cbn [snd] in E. subst v.
    match goal with |- context [in_sides_xB ?a ?b ?c ?d ?e] => destruct (in_sides_xB a b c d e) end; cbn [fst snd]; split; try reflexivity; exact HM'.
  - cbn [mk_eh eh_h2 eh_e2].
    match goal with |- context [if ?c then (true, m) else _] =>
      match goal with |- context [if ?d then true else if in_sides_xB _ _ _ _ _ then _ else _] =>
        assert (EC : c = d) by (destruct (sp_rng sp) as [[? ?]|]; [|reflexivity]; destruct br2 as [[? ?]|]; [|reflexivity];
                                destruct (sp_h1 sp); [|reflexivity]; destruct (xhiB bc _); reflexivity);
        rewrite EC; destruct d; [split; [reflexivity|exact HM]|] end end.
    match goal with |- context [mget dc m ?f] =>
      destruct (mget_ok bc tbl b2 k2 _ m dc _ f HN Hin HM eq_refl) as [E HM']; destruct (mget dc m f) as [v m'] end.
    cbn [fst snd] in E, HM'. unfold qf in E. cbn [snd] in E. subst v.
    match goal with |- context [in_sides_xB ?a ?b ?c ?d ?e] => destruct (in_sides_xB a b c d e) end; cbn [fst snd]; split; try reflexivity; exact HM'.
Qed.


Definition KMOK (bc : bctx) (tbl : ctab) (K : kentry) (m : memo) : Prop :=
  match kbkl K with Some (kb, kk, len) => MOK bc tbl kb kk len m | None => True end.
Definition eh_of (bc : bctx) (br2 : option (Z * Z)) (K : kentry) : ehoist :=
  match kbkl K with Some (kb, kk, len) => mk_eh bc br2 kb kk len | None => EH None None end.

Lemma prune1pcK0M_eq : forall bc tbl sp dc wa w wv K same br2 m,
  NoDup (map fst tbl) -> In (dc, (sp_D sp, sp_Dx sp)) tbl -> KMOK bc tbl K m ->
  fst (prune1pcK0M bc sp dc (eh_of bc br2 K) wa w wv K same br2 m) = prune1pcK0 bc sp wa w wv K same br2
  /\ KMOK bc tbl K (snd (prune1pcK0M bc sp dc (eh_of bc br2 K) wa w wv K same br2 m)).
Proof.
  intros bc tbl sp dc wa w wv K same br2 m HN Hin HM.
  destruct K as [[kb kk] w' v|[kb kk] len|[kb kk] len bk|lo hi|e' m'|e' lo' hi'|[eb ek] en|c1 m1 c2 m2|[kb kk] len fc|[kb kk] len];
    unfold KMOK, eh_of in *; cbn [kbkl] in *; unfold prune1pcK0M; try (cbn [fst snd]; split; [reflexivity|exact HM]).
  - (* [comment removed for export] *)
    destruct same; [cbn [fst snd]; split; [reflexivity|exact HM]|].
    unfold prune1pcK0, elen.
    destruct (rapM_eq bc tbl sp dc (a_base wa) (a_off wa) (Z.of_nat w) br2 kb kk (ELit (Z.of_nat w')) m HN Hin HM) as [E HM'].
    destruct (rapM bc sp dc _ (a_base wa) (a_off wa) (ELit (Z.of_nat w)) br2 kb kk (ELit (Z.of_nat w')) m) as [ap m2].
    cbn [fst snd] in E, HM'. rewrite <- E. destruct ap; cbn [fst snd]; [split; [reflexivity|exact HM']|].
    destruct (Nat.eqb w 1 && Nat.eqb w' 1 && expr_eqb wv v)%bool; cbn [fst snd]; split; try reflexivity; exact HM'.
  - (* [comment removed for export] *)
    destruct same; [cbn [fst snd]; split; [reflexivity|exact HM]|].
    unfold prune1pcK0, elen.
    destruct (rapM_eq bc tbl sp dc (a_base wa) (a_off wa) (Z.of_nat w) br2 kb kk len m HN Hin HM) as [E HM'].
    destruct (rapM bc sp dc _ (a_base wa) (a_off wa) (ELit (Z.of_nat w)) br2 kb kk len m) as [ap m2].
    cbn [fst snd] in E, HM'. rewrite <- E. destruct ap; cbn [fst snd]; split; try reflexivity; exact HM'.
  - (* [comment removed for export] *)
    destruct same; [cbn [fst snd]; split; [reflexivity|exact HM]|].
    unfold prune1pcK0, elen.
    destruct (rapM_eq bc tbl sp dc (a_base wa) (a_off wa) (Z.of_nat w) br2 kb kk len m HN Hin HM) as [E HM'].
    destruct (rapM bc sp dc _ (a_base wa) (a_off wa) (ELit (Z.of_nat w)) br2 kb kk len m) as [ap m2].
    cbn [fst snd] in E, HM'. rewrite <- E. destruct ap; cbn [fst snd]; split; try reflexivity; exact HM'.
  - (* [comment removed for export] *)
    destruct same; [cbn [fst snd]; split; [reflexivity|exact HM]|].
    unfold prune1pcK0, elen.
    destruct (rapM_eq bc tbl sp dc (a_base wa) (a_off wa) (Z.of_nat w) br2 kb kk len m HN Hin HM) as [E HM'].
    destruct (rapM bc sp dc _ (a_base wa) (a_off wa) (ELit (Z.of_nat w)) br2 kb kk len m) as [ap m2].
    cbn [fst snd] in E, HM'. rewrite <- E. destruct ap; cbn [fst snd]; split; try reflexivity; exact HM'.
  - (* [comment removed for export] *)
    destruct same; [cbn [fst snd]; split; [reflexivity|exact HM]|].
    unfold prune1pcK0, elen.
    destruct (rapM_eq bc tbl sp dc (a_base wa) (a_off wa) (Z.of_nat w) br2 kb kk len m HN Hin HM) as [E HM'].
    destruct (rapM bc sp dc _ (a_base wa) (a_off wa) (ELit (Z.of_nat w)) br2 kb kk len m) as [ap m2].
    cbn [fst snd] in E, HM'. rewrite <- E. destruct ap; cbn [fst snd]; split; try reflexivity; exact HM'.
Qed.

Lemma prune1pcKM_eq : forall bc tbl sp dc wa w wv K same br2 fa m,
  NoDup (map fst tbl) -> In (dc, (sp_D sp, sp_Dx sp)) tbl -> KMOK bc tbl K m ->
  fst (prune1pcKM bc sp dc (eh_of bc br2 K) wa w wv K same br2 fa m) = prune1pcK bc sp wa w wv K same br2 fa
  /\ KMOK bc tbl K (snd (prune1pcKM bc sp dc (eh_of bc br2 K) wa w wv K same br2 fa m)).
Proof.
  intros. unfold prune1pcKM, prune1pcK. destruct fa; [split; [reflexivity|assumption]|].
  destruct (pk_keepb wa w K same); [split; [reflexivity|assumption]|]. apply prune1pcK0M_eq; assumption.
Qed.

Definition erase (x : stx * positive * list stx) : stx * list stx := (fst (fst x), snd x).
Lemma chainKFM_eq : forall bc tbl fl K okb same_of br2 fa_of m,
  NoDup (map fst tbl) -> (forall sx dc rest, In (sx, dc, rest) fl -> In (dc, spk sx) tbl) -> KMOK bc tbl K m ->
  chainKFM bc (eh_of bc br2 K) fl K okb same_of br2 fa_of m = chainKF bc (map erase fl) K okb same_of br2 fa_of.
Proof.
  intros bc tbl fl. induction fl as [|[[sx dc] rest] fl' IH]; intros K okb same_of br2 fa_of m HN HC HM; [reflexivity|].
  cbn [chainKFM chainKF map erase fst snd].
  destruct (prune1pcKM_eq bc tbl (sx_sp sx) dc (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 (fa_of sx K) m HN
              (HC sx dc rest (or_introl eq_refl)) HM) as [E HM'].
  destruct (prune1pcKM bc (sx_sp sx) dc _ (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 (fa_of sx K) m) as [r m'].
  cbn [fst snd] in E, HM'. rewrite <- E. destruct r as [|l]; [|reflexivity].
  apply IH; [exact HN | intros sx' dc' rest' Hin; apply (HC sx' dc' rest'); right; exact Hin | exact HM'].
Qed.

Lemma mk_fl3_erase : forall bc t g sxcs, map erase (mk_fl3 bc t g sxcs) = mk_fl2 bc t g (map fst sxcs).
Proof.
  intros bc t g sxcs. induction sxcs as [|[sx dc] rest IH]; [reflexivity|].
  cbn [mk_fl3 mk_fl2 map fst]. destruct (verdict2 bc t sx g); [exact IH|]. cbn [map erase fst snd]. rewrite IH. reflexivity.
Qed.
Lemma mk_fl3_In : forall bc t g sxcs sx dc rest, In (sx, dc, rest) (mk_fl3 bc t g sxcs) -> In (sx, dc) sxcs.
Proof.
  intros bc t g sxcs. induction sxcs as [|[sx0 dc0] r IH]; intros sx dc rest H; [destruct H|].
  cbn [mk_fl3] in H. destruct (verdict2 bc t sx0 g); [right; exact (IH _ _ _ H)|].
  destruct H as [H|H]; [injection H as <- <- _; left; reflexivity | right; exact (IH _ _ _ H)].
Qed.
Lemma all_fl_In : forall sxcs sx dc rest, In (sx, dc, rest) (all_fl sxcs) -> In (sx, dc) sxcs.
Proof.
  induction sxcs as [|[sx0 dc0] r IH]; intros sx dc rest H; [destruct H|].
  cbn [all_fl] in H. destruct H as [H|H]; [injection H as <- <- _; left; reflexivity | right; exact (IH _ _ _ H)].
Qed.
Lemma chainKF_all : forall bc sxcs K okb same_of br2 fa_of,
  chainKF bc (map erase (all_fl sxcs)) K okb same_of br2 fa_of = chainK2 bc (map fst sxcs) K okb same_of br2 fa_of.
Proof.
  intros bc sxcs. induction sxcs as [|[sx dc] rest IH]; intros K okb same_of br2 fa_of; [reflexivity|].
  cbn [all_fl map erase fst snd chainKF chainK2].
  destruct (prune1pcK _ _ _ _ _ K _ br2 _); [apply IH|reflexivity].
Qed.

Lemma prune1pcK_keep_same : forall bc sp wa w wv K kb kk m br2 same,
  regK K = true -> kdescr K = Some (kb, kk, Some m) ->
  expr_eqb kb (a_base wa) = true ->
  (match kbase K with Some _ => same = true | None => True end) ->
  (kk + m <= a_off wa \/ a_off wa + Z.of_nat w <= kk) ->
  forall fa, prune1pcK bc sp wa w wv K same br2 fa = PKeep.
Proof.
  intros bc sp wa w wv K kb kk m br2 same HR HD HB HS Hdis fa. destruct fa; [reflexivity|].
  unfold prune1pcK.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [regK] in HR; try discriminate HR; cbn [kdescr kbase] in HD, HS.
  - (* [comment removed for export] *)
    injection HD as <- <- <-. subst same. apply Nat.leb_le in HR.
    rewrite zlit64_id in Hdis by (unfold two64; lia).
    cbn [pk_keepb]. unfold prune1pcK0.
    replace (Z.leb (k + Z.of_nat w') (a_off wa) || Z.leb (a_off wa + Z.of_nat w) k)%bool with true; [reflexivity|].
    symmetry. apply Bool.orb_true_iff. destruct Hdis as [H|H]; [left|right]; apply Z.leb_le; lia.
  - (* [comment removed for export] *)
    destruct len as [l0| | | | | | |]; try discriminate HR. injection HD as <- <- <-. subst same.
    destruct (Z.ltb 0 l0) eqn:H0; [|discriminate HR]. apply Z.ltb_lt in H0. apply Z.ltb_lt in HR.
    rewrite zlit64_id in Hdis by lia.
    assert (G : pk_keepb wa w (KZero (SA b k) (ELit l0)) true = true).
    { cbn [pk_keepb]. cbv zeta. rewrite zmod64_eq. change (2 ^ 64) with two64. rewrite Z.mod_small by lia.
      rewrite Z.eqb_refl. replace (Z.ltb 0 l0) with true by (symmetry; apply Z.ltb_lt; exact H0). rewrite !Bool.andb_true_r.
      apply Bool.orb_true_iff. destruct Hdis as [H|H]; [left|right]; apply Z.leb_le; lia. }
    rewrite G. reflexivity.
  - (* [comment removed for export] *)
    destruct len as [l0| | | | | | |]; try discriminate HR. injection HD as <- <- <-. subst same.
    destruct (Z.ltb 0 l0) eqn:H0; [|discriminate HR]. apply Z.ltb_lt in H0. apply Z.ltb_lt in HR.
    rewrite zlit64_id in Hdis by lia.
    cbn [pk_keepb]. unfold prune1pcK0. cbv zeta. change (2 ^ 64) with two64. rewrite Z.mod_small by lia.
    replace (Z.leb (k + l0) (a_off wa) || Z.leb (a_off wa + Z.of_nat w) k)%bool with true; [reflexivity|].
    symmetry. apply Bool.orb_true_iff. destruct Hdis as [H|H]; [left|right]; apply Z.leb_le; lia.
  - (* [comment removed for export] *)
    destruct (Z.ltb lo hi) eqn:H0; [|discriminate HR]. apply Z.ltb_lt in H0. apply Z.ltb_lt in HR.
    change (2 ^ 64) with two64 in HD.
    replace (Z.ltb (hi - lo) two64) with true in HD by (symmetry; apply Z.ltb_lt; exact HR).
    injection HD as <- <- <-. rewrite zlit64_id in Hdis by lia.
    apply p_expr_eqb_eq in HB.
    assert (G : pk_keepb wa w (KImg lo hi) same = true).
    { cbn [pk_keepb]. rewrite <- HB.
      replace (Z.ltb lo hi) with true by (symmetry; apply Z.ltb_lt; exact H0). rewrite Bool.andb_true_r.
      apply Bool.orb_true_iff. destruct Hdis as [H|H]; [left|right]; apply Z.leb_le; lia. }
    rewrite G. reflexivity.
  - (* [comment removed for export] *)
    destruct len as [l0| | | | | | |]; try discriminate HR. injection HD as <- <- <-. subst same.
    destruct (Z.ltb 0 l0) eqn:H0; [|discriminate HR]. apply Z.ltb_lt in H0. apply Z.ltb_lt in HR.
    rewrite zlit64_id in Hdis by lia.
    assert (G : pk_keepb wa w (KFill (SA b k) (ELit l0) fc) true = true).
    { cbn [pk_keepb]. cbv zeta. rewrite zmod64_eq. change (2 ^ 64) with two64. rewrite Z.mod_small by lia.
      rewrite Z.eqb_refl. replace (Z.ltb 0 l0) with true by (symmetry; apply Z.ltb_lt; exact H0). rewrite !Bool.andb_true_r.
      apply Bool.orb_true_iff. destruct Hdis as [H|H]; [left|right]; apply Z.leb_le; lia. }
    rewrite G. reflexivity.
  - (* [comment removed for export] *)
    destruct len as [l0| | | | | | |]; try discriminate HR. injection HD as <- <- <-. subst same.
    destruct (Z.ltb 0 l0) eqn:H0; [|discriminate HR]. apply Z.ltb_lt in H0. apply Z.ltb_lt in HR.
    rewrite zlit64_id in Hdis by lia.
    assert (G : pk_keepb wa w (KUnk (SA b k) (ELit l0)) true = true).
    { cbn [pk_keepb]. cbv zeta. rewrite zmod64_eq. change (2 ^ 64) with two64. rewrite Z.mod_small by lia.
      rewrite Z.eqb_refl. replace (Z.ltb 0 l0) with true by (symmetry; apply Z.ltb_lt; exact H0). rewrite !Bool.andb_true_r.
      apply Bool.orb_true_iff. destruct Hdis as [H|H]; [left|right]; apply Z.leb_le; lia. }
    rewrite G. reflexivity.
Qed.

Lemma chainKF_filter_erase : forall bc p fl K okb same_of br2 fa_of,
  (forall sx dc rest, In (sx, dc, rest) fl -> p (sx, dc, rest) = false ->
     prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 (fa_of sx K) = PKeep) ->
  chainKF bc (map erase (List.filter p fl)) K okb same_of br2 fa_of = chainKF bc (map erase fl) K okb same_of br2 fa_of.
Proof.
  intros bc p fl. induction fl as [|[[sx dc] rest] fl' IH]; intros K okb same_of br2 fa_of Hp; [reflexivity|].
  assert (IH' : chainKF bc (map erase (List.filter p fl')) K okb same_of br2 fa_of = chainKF bc (map erase fl') K okb same_of br2 fa_of)
    by (apply IH; intros sx' dc' rest' Hin; apply Hp; right; exact Hin).
  cbn [List.filter]. destruct (p (sx, dc, rest)) eqn:E.
  - cbn [map erase fst snd chainKF]. destruct (prune1pcK _ _ _ _ _ K _ br2 _); [exact IH'|reflexivity].
  - cbn [map erase fst snd chainKF]. rewrite (Hp sx dc rest (or_introl eq_refl) E). exact IH'.
Qed.

Lemma entry3_eq : forall fk tbl sbs sxcs t1 bnds K ei,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) (map fst sxcs) -> EINF (mkbc fk) t1 K (Some ei) ->
  NoDup (map fst tbl) -> (forall sx dc, In (sx, dc) sxcs -> In (dc, spk sx) tbl) ->
  entry3 (mkbc fk) sbs (all_fl sxcs) (mk_gl3 (mkbc fk) t1 bnds sxcs) K ei
  = entry1 (mkbc fk) sbs (map fst sxcs) (mk_gl2 (mkbc fk) t1 bnds (map fst sxcs)) K ei.
Proof.
  intros fk tbl sbs sxcs t1 bnds K ei HT HS HK HN HC. cbn [EINF] in HK. destruct HK as (HD & HIn & Hbr).
  set (br2 := match kbase K with Some _ => ei_br ei | None => None end).
  set (same_of := match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ : positive => false end).
  assert (E3C : forall fl, entry3c (mkbc fk) sbs K ei fl
            = chainKFM (mkbc fk) (eh_of (mkbc fk) br2 K) fl K (kbase K) same_of br2
                       (match kbase K, kbkl K with
                        | Some kb, Some (_, _, len) => fa_entry (mkbc fk) (mk_aqs (mkbc fk) sbs kb len) kb
                        | _, _ => fa_none
                        end) []).
  { intros fl. destruct fl; reflexivity. }
  unfold entry3, entry1. cbv zeta. unfold mk_gl3, mk_gl2. rewrite !pt_get_map.
  fold br2. fold same_of.
  assert (HM0 : KMOK (mkbc fk) tbl K []) by (unfold KMOK; destruct (kbkl K) as [[[? ?] ?]|]; [apply MOK_nil|exact I]).
  (* [comment removed for export] *)
  assert (SFL : forall fl fa_of, (forall sx dc rest, In (sx, dc, rest) fl -> In (sx, dc) sxcs) ->
            chainKFM (mkbc fk) (eh_of (mkbc fk) br2 K) (sfl K ei fl) K (kbase K) same_of br2 fa_of []
            = chainKF (mkbc fk) (map erase fl) K (kbase K) same_of br2 fa_of).
  { intros fl fa_of Hfl.
    assert (Hsub : forall x, In x (sfl K ei fl) -> In x fl).
    { intros x Hx. unfold sfl in Hx. destruct (ei_m ei); [|exact Hx]. destruct (regK K); [|exact Hx]. apply filter_In in Hx. exact (proj1 Hx). }
    rewrite (chainKFM_eq (mkbc fk) tbl); [| exact HN | intros sx dc rest Hin; apply HC; apply (Hfl sx dc rest); apply Hsub; exact Hin | exact HM0].
    unfold sfl. destruct (ei_m ei) as [m|] eqn:Hm; [|reflexivity]. destruct (regK K) eqn:HR; [|reflexivity].
    apply chainKF_filter_erase. intros sx dc rest Hin Hp. unfold sfilt in Hp. cbn [fst] in Hp. rewrite zofw_eq in Hp.
    destruct (Pos.eqb (ei_bid ei) (sx_bid sx)) eqn:Hb; [|discriminate Hp].
    assert (Hsx : In sx (map fst sxcs)) by (apply in_map_iff; exists (sx, dc); split; [reflexivity|exact (Hfl _ _ _ Hin)]).
    pose proof (proj1 (Forall_forall _ _) HS sx Hsx) as (SXin & _ & _).
    pose proof (nt_same_eq _ _ _ _ _ _ HT HIn SXin) as EQB. rewrite Hb in EQB. symmetry in EQB.

    eapply prune1pcK_keep_same; [exact HR | exact HD | exact EQB | |].
    - subst same_of. destruct (kbase K); [exact Hb|exact I].
    - destruct (Z.leb (ei_k ei + m) (a_off (sx_a sx))) eqn:E1; [left; apply Z.leb_le; exact E1|].
      destruct (Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) (ei_k ei)) eqn:E2; [right; apply Z.leb_le; exact E2|discriminate Hp]. }
  assert (ALL : forall fa_of, chainKFM (mkbc fk) (eh_of (mkbc fk) br2 K) (sfl K ei (all_fl sxcs)) K (kbase K) same_of br2 fa_of []
                              = chainK2 (mkbc fk) (map fst sxcs) K (kbase K) same_of br2 fa_of).
  { intros. rewrite SFL; [apply chainKF_all|]. intros sx dc rest Hin. exact (all_fl_In _ _ _ _ Hin). }
  destruct (pt_get bnds (ei_gid ei)) as [g|]; [|rewrite E3C; apply ALL].
  destruct (inb g ei); [|rewrite E3C; apply ALL].
  rewrite E3C, SFL; [rewrite mk_fl3_erase; reflexivity|].
  intros sx dc rest Hin. exact (mk_fl3_In _ _ _ _ _ _ _ Hin).
Qed.

Lemma entriesG3_eq : forall fk tbl sbs sxcs t1 bnds kn infos,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) (map fst sxcs) -> Forall2 (EINF (mkbc fk) t1) kn infos ->
  NoDup (map fst tbl) -> (forall sx dc, In (sx, dc) sxcs -> In (dc, spk sx) tbl) ->
  entriesG3 (mkbc fk) sbs (all_fl sxcs) (mk_gl3 (mkbc fk) t1 bnds sxcs) kn infos
  = entriesG2 (mkbc fk) sbs (map fst sxcs) (mk_gl2 (mkbc fk) t1 bnds (map fst sxcs)) kn infos.
Proof.
  intros fk tbl sbs sxcs t1 bnds kn infos HT HS HF HN HC. induction HF as [|K oi rest irest HK HF IH]; [reflexivity|].
  cbn [entriesG3 entriesG2]. rewrite IH. destruct oi as [ei|]; [|reflexivity].
  rewrite (entry3_eq fk tbl _ _ _ _ _ _ HT HS HK HN HC). reflexivity.
Qed.

Lemma carryG3_eq : forall fk log kn, carryG3 (mkbc fk) log kn = carryG2 (mkbc fk) log kn.
Proof.
  intros fk log kn. unfold carryG3, carryG2.
  destruct (mk_kdl (bc_fk (mkbc fk)) [] xH) as [[kd stbl] nx] eqn:EK.
  destruct (mk_kdl_ok _ _ _ _ _ _ (conj (fun i sd (H : In (i, sd) []) => match H with end) (fun i sd sd' (H : In (i, sd) []) => match H with end)) EK)
    as ((_ & Hfun) & _ & HmapK & HallK).
  pose proof (proj1 (mk_stxsI_eq (mkbc fk) kd stbl log nt_empty [] Hfun HallK HmapK (fun id b l H => match H with end))) as EQ.
  clear Hfun HmapK HallK EK.
  destruct (mk_stxs (mkbc fk) log nt_empty) as [sxs t0] eqn:E.
  destruct (mk_stxsI (mkbc fk) kd log nt_empty []) as [[sxsq t0q] xcq]. cbn [fst] in EQ. injection EQ as -> ->.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & Hmap & _).
  destruct (scan_entries (mkbc fk) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
  assert (HS1 : Forall (SX_OK (mkbc fk) t1) sxs).
  { apply Forall_impl with (P := SX_OK (mkbc fk) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
  destruct (mk_cls sxs [] xH) as [sxcs tbl] eqn:EC.
  destruct (mk_cls_ok _ _ _ _ _ CT_OK_nil EC) as (Hms & HN & _ & HC).
  rewrite <- Hms in HS1.
  rewrite (entriesG3_eq fk tbl _ _ _ _ _ _ HT1 HS1 HF HN HC), Hms. reflexivity.
Qed.
Lemma carryK3_eqK : forall fk log kn hints, carryK3 (mkbc fk) log kn hints = carryK (mkbc fk) log kn hints.
Proof.
  intros fk log kn hints. rewrite <- carryK2_eqK. unfold carryK3, carryK2.
  destruct log as [|s1 [|s2 [|s3 older]]]; try reflexivity.
  destruct hints; [|reflexivity]. rewrite carryG3_eq. reflexivity.
Qed.
Lemma carryK3_eq : forall log kn hints, carryK3 (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof. intros. rewrite carryK3_eqK. apply carryK_eq. Qed.

End AX2C.
