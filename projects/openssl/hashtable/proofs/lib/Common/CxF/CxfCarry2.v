(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B CxfCarry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module CXFC2.
Import AX2. Import AX2B. Import CXFC.

(* [comment removed for export] *)
Definition img_in (g : gval) (K' : kentry) : bool :=
  match K', g with
  | KImg lo' hi', (_, _, _, (glo, ghi)) =>
      if Z.ltb (hi' - lo') (2 ^ 64) then if Z.leb glo lo' then Z.leb (lo' + zlit64 (hi' - lo')) ghi else false else false
  | _, _ => false
  end.
Definition sfF : positive -> bool := fun _ => false.

Fixpoint chainKFM2 (bc : bctx) (g : gval) (fl : flF) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) (m : memo2) : list kentry :=
  match fl with
  | [] => [K]
  | (sxr, rest) :: fl' =>
      let sx := fst sxr in
      match prune1pcKM bc (sx_sp sx) (fst (snd sxr)) (snd (snd sxr)) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m with
      | (PKeep, m') => chainKFM2 bc g fl' K okb same_of br2 m'
      | (PRepl l, m') =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2M bc rest K' okb same_of br2 (if subj_tail_eqb K K' then m' else memo0)
                                                else chain_slow bc (map fst rest) [K']
                                  | None => chain_slow bc (map fst rest) [K']
                                  end) l
          | None => flat_map (fun K' => if img_in g K' then chainKFM2 bc g fl' K' None sfF None memo0
                                        else chain_slow bc (map fst rest) [K']) l
          end
      end
  end.

(* [comment removed for export] *)
Fixpoint img_okF (bc : bctx) (g : gval) (fl : flF) : Prop :=
  match fl with
  | [] => True
  | (sxr, rest) :: fl' =>
      (forall K', img_in g K' = true -> chainKF bc (fl_proj fl') K' None sfF None = chain_slow bc (map fst rest) [K'])
      /\ img_okF bc g fl'
  end.

Lemma chainKFM2_eq : forall bc, rt_fun bc -> forall g fl K okb same_of br2 m, fl_ok bc fl -> kmemo_ok bc K m ->
  (forall kb, okb = Some kb -> kbase K = Some kb) -> (okb = None -> img_okF bc g fl) ->
  chainKFM2 bc g fl K okb same_of br2 m = chainKF bc (fl_proj fl) K okb same_of br2.
Proof.
  intros bc RTF g fl. induction fl as [|[[sx [RS DI]] rest] fl' IH]; intros K okb same_of br2 m HS Hm HB HI; [reflexivity|].
  apply Forall_cons_iff in HS as [[H1 HR] HS]. cbn [chainKFM2 chainKF fl_proj map fst snd].
  destruct (prune1pcKM_spec bc RTF (sx_sp sx) RS DI (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m Hm H1) as [E1 E2].
  destruct (prune1pcKM bc (sx_sp sx) RS DI (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m) as [r m']. cbn [fst snd] in E1, E2.
  rewrite <- E1. destruct r as [|l].
  - apply IH; try assumption. intros EN. destruct (HI EN) as [_ H]. exact H.
  - destruct okb as [kb|].
    + apply flat_map_ext'. intros K'. destruct (kbase K') as [kb'|] eqn:HK'; [|reflexivity].
      destruct (expr_eqb kb' kb) eqn:Eb; [|reflexivity]. apply p_expr_eqb_eq in Eb. subst kb'.
      apply (chainK2M_eq bc RTF); [exact HR | | intros kb0 H0; injection H0 as <-; exact HK'].
      destruct (subj_tail_eqb K K') eqn:Es; [|apply kmemo_ok0].
      apply (kmemo_ok_subj bc K K' m'); [|exact E2]. exact (subj_tail_eqb_eq K K' kb (HB kb eq_refl) HK' Es).
    + destruct (HI eq_refl) as [HK HI']. cbn [fl_proj map fst snd] in HK.
      rewrite (chain_slow_flat_map bc (map fst rest) l). apply flat_map_ext'. intros K'.
      destruct (img_in g K') eqn:EI; [|reflexivity].
      rewrite (IH K' None sfF None memo0 HS (kmemo_ok0 bc K')); [exact (HK K' EI) | intros kb H0; discriminate | intros _; exact HI'].
Qed.

(* [comment removed for export] *)
Fixpoint chainKFM2B (bc : bctx) (g : gval) (fl : flF) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) (m : memo2) : list kentry * blkc :=
  match fl with
  | [] => ([K], mm_blk m)
  | (sxr, rest) :: fl' =>
      let sx := fst sxr in
      match prune1pcKM bc (sx_sp sx) (fst (snd sxr)) (snd (snd sxr)) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m with
      | (PKeep, m') => chainKFM2B bc g fl' K okb same_of br2 m'
      | (PRepl l, m') =>
          (match okb with
           | Some kb =>
               flat_map (fun K' => match kbase K' with
                                   | Some kb' => if expr_eqb kb' kb then chainK2M bc rest K' okb same_of br2 (if subj_tail_eqb K K' then m' else memo0)
                                                 else chain_slow bc (map fst rest) [K']
                                   | None => chain_slow bc (map fst rest) [K']
                                   end) l
           | None => flat_map (fun K' => if img_in g K' then chainKFM2 bc g fl' K' None sfF None memo0
                                         else chain_slow bc (map fst rest) [K']) l
           end, mm_blk m')
      end
  end.
Lemma chainKFM2B_spec : forall bc, rt_fun bc -> forall g fl K okb same_of br2 m, fl_ok bc fl -> kmemo_ok bc K m ->
  fst (chainKFM2B bc g fl K okb same_of br2 m) = chainKFM2 bc g fl K okb same_of br2 m /\ blk_ok bc (snd (chainKFM2B bc g fl K okb same_of br2 m)).
Proof.
  intros bc RTF g fl. induction fl as [|[[sx [RS DI]] rest] fl' IH]; intros K okb same_of br2 m HS Hm; [split; [reflexivity|exact (kmemo_ok_blk bc K m Hm)]|].
  apply Forall_cons_iff in HS as [[H1 HR] HS]. cbn [chainKFM2B chainKFM2 fst snd].
  destruct (prune1pcKM_spec bc RTF (sx_sp sx) RS DI (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m Hm H1) as [_ E2].
  destruct (prune1pcKM bc (sx_sp sx) RS DI (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m) as [r m']. cbn [fst snd] in E2 |- *.
  destruct r as [|l]; [apply IH; assumption|]. cbn [fst snd]. split; [reflexivity|exact (kmemo_ok_blk bc K m' E2)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma img_keep : forall fk t sx g ei m lo' hi',
  NTI (mkbc fk) t -> SX_OK (mkbc fk) t sx ->
  ei_kb ei = ELit 0%Z -> In (ELit 0%Z, ei_bid ei) (nt_bucket t (bkey (ELit 0%Z))) -> ei_br ei = base_rangeB (mkbc fk) (ELit 0%Z) ->
  inb g ei = true -> ei_m ei = Some m ->
  img_in g (KImg lo' hi') = true ->
  verdict2R (cg_of (mkbc fk) g) sx g = true ->
  prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) (KImg lo' hi') (sfF (sx_bid sx)) None = PKeep.
Proof.
  intros fk t sx g ei m lo' hi' HT HSX Hkb HIn Hbr Hinb Hm HI Hv.
  destruct g as [[[b gkb] obr] [glo ghi]]. cbn [img_in] in HI.
  destruct (Z.ltb (hi' - lo') (2 ^ 64)) eqn:Hlt; [|discriminate]. destruct (Z.leb glo lo') eqn:Hlo; [|discriminate].
  (* [comment removed for export] *)
  set (ei' := EI (ei_bid ei) (ei_gid ei) (ELit 0%Z) (ei_br ei) lo' (Some (zlit64 (hi' - lo')))).
  assert (Hinb' : inb (b, gkb, obr, (glo, ghi)) ei' = true).
  { unfold inb in Hinb |- *. rewrite Hm in Hinb. cbn [ei_m ei_bid ei_kb ei_br ei_k ei'].
    apply andb_prop in Hinb as [Hinb _]. apply andb_prop in Hinb as [Hinb _]. apply andb_prop in Hinb as [Hinb H2]. apply andb_prop in Hinb as [H1 H1'].
    rewrite Hkb in H1'. rewrite H1, H1', H2, Hlo, HI. reflexivity. }
  assert (HD : kdescr (KImg lo' hi') = Some (ELit 0%Z, lo', Some (zlit64 (hi' - lo')))) by (cbn [kdescr]; rewrite Hlt; reflexivity).
  pose proof HSX as (SXin & SXbr & SXsp & SXps).
  unfold verdict2R in Hv. destruct (verdict sx (b, gkb, obr, (glo, ghi))) eqn:Hv1.
  - destruct (verdict_inb_num _ _ ei' _ Hv1 Hinb' eq_refl) as (Hne & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
    cbn [ei_bid ei_br ei_k ei'] in Hne, Hbr2, Hnum.
    eapply prune1pcK_keep_img; [exact HD| |exact Hsp| rewrite <- Hbr; exact Hbr2 | exact Hnum].
    rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne.
  - apply (verdict_disjR_disj _ _ _ _ (mkbc_rt fk) HSX) in Hv.
    destruct (verdict_disj_inb _ _ _ ei' _ Hv Hinb' eq_refl) as [Hne HSD]. cbn [ei_bid ei_kb ei_k ei'] in Hne, HSD.
    eapply prune1pcK_keep_img_sides; [exact HD| |exact HSD].
    rewrite <- (nt_same_eq _ _ _ _ _ _ HT HIn SXin). exact Hne.
Qed.

Lemma img_slow : forall fk t g ei m rest K',
  NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) rest ->
  ei_kb ei = ELit 0%Z -> In (ELit 0%Z, ei_bid ei) (nt_bucket t (bkey (ELit 0%Z))) -> ei_br ei = base_rangeB (mkbc fk) (ELit 0%Z) ->
  inb g ei = true -> ei_m ei = Some m -> img_in g K' = true ->
  chainKF (mkbc fk) (mk_fl (cg_of (mkbc fk) g) g rest) K' None sfF None = chain_slow (mkbc fk) rest [K'].
Proof.
  intros fk t g ei m rest K' HT HS Hkb HIn Hbr Hinb Hm HI.
  destruct K' as [| | |lo' hi'| | | | | |]; try (destruct g as [[[? ?] ?] [? ?]]; discriminate).
  rewrite chainKF_eq.
  - apply chainK2_eq; [exact (Forall_SX_sp _ _ _ HS) | reflexivity | reflexivity].
  - intros sx Hsx Hv. exact (img_keep fk t sx g ei m lo' hi' HT (proj1 (Forall_forall _ _) HS sx Hsx) Hkb HIn Hbr Hinb Hm HI Hv).
Qed.

Lemma img_okF_mk : forall fk t g ei m sxs,
  NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) (map fst sxs) ->
  ei_kb ei = ELit 0%Z -> In (ELit 0%Z, ei_bid ei) (nt_bucket t (bkey (ELit 0%Z))) -> ei_br ei = base_rangeB (mkbc fk) (ELit 0%Z) ->
  inb g ei = true -> ei_m ei = Some m ->
  img_okF (mkbc fk) g (mk_flF (cg_of (mkbc fk) g) g sxs).
Proof.
  intros fk t g ei m sxs HT HS Hkb HIn Hbr Hinb Hm. induction sxs as [|sx rest IH]; [exact I|].
  cbn [map] in HS. apply Forall_cons_iff in HS as [_ HS]. cbn [mk_flF].
  destruct (verdict2R (cg_of (mkbc fk) g) (fst sx) g); [exact (IH HS)|]. cbn [img_okF]. split; [|exact (IH HS)].
  intros K' HI. rewrite mk_flF_proj. exact (img_slow fk t g ei m (map fst rest) K' HT HS Hkb HIn Hbr Hinb Hm HI).
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint entriesGM2 (bc : bctx) (sxs : list stxr) (gl : ptree gflF) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           let okb := kbase K in
           let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
           let br2 := match okb with Some _ => ei_br ei | None => None end in
           match pt_get gl (ei_gid ei) with
           | Some (g, fl) => if inb g ei then chainKFM2 bc g fl K okb same_of br2 memo0 else chainK2M bc sxs K okb same_of br2 memo0
           | None => chainK2M bc sxs K okb same_of br2 memo0
           end
       | None => if is_pure K then [K] else chainK2M bc sxs K None (fun _ => false) None memo0
       end) ++ entriesGM2 bc sxs gl rest irest
  | _, _ => []
  end.
Lemma entriesGM2_eq : forall fk t sxs bnds kn infos,
  NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) (map fst sxs) -> Forall (sx_ok (mkbc fk)) sxs -> Forall2 (EINF (mkbc fk) t) kn infos ->
  entriesGM2 (mkbc fk) sxs (mk_glF (mkbc fk) bnds sxs) kn infos = entriesGM (mkbc fk) sxs (mk_glF (mkbc fk) bnds sxs) kn infos.
Proof.
  intros fk t sxs bnds kn infos HT HS HSX HF. pose proof (rt_fun_mk (mkbc fk) (mkbc_rt fk)) as RTF.
  induction HF as [|K oi rest irest HK HF IH]; [reflexivity|].
  cbn [entriesGM2 entriesGM]. rewrite IH. f_equal.
  destruct oi as [ei|]; [|reflexivity]. unfold mk_glF. rewrite !pt_get_map.
  destruct (pt_get bnds (ei_gid ei)) as [g|]; [|reflexivity].
  destruct (inb g ei) eqn:Hinb; [|reflexivity].
  rewrite (chainKFM_eq (mkbc fk) RTF); [|apply mk_flF_ok; exact HSX | apply kmemo_ok0 | intros kb H; exact H].
  apply (chainKFM2_eq (mkbc fk) RTF); [apply mk_flF_ok; exact HSX | apply kmemo_ok0 | intros kb H; exact H|].
  intros HN. cbn [EINF] in HK. destruct HK as (HD & HIn & Hbr).
  assert (Hm : exists m, ei_m ei = Some m).
  { unfold inb in Hinb. destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]. }
  destruct Hm as [m Hm].
  destruct (kdescr_kbase _ _ _ _ HD) as [HB|(lo & hi & -> & Hkb & Hk)]; [rewrite HB in HN; discriminate|].
  rewrite Hkb in HIn, Hbr.
  exact (img_okF_mk fk t g ei m sxs HT HS Hkb HIn Hbr Hinb Hm).
Qed.

(* [comment removed for export] *)
Fixpoint entriesGM2B (bc : bctx) (sxs : list stxr) (gl : ptree gflF) (kn : list kentry) (infos : list (option einfo)) (B : blkc) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      let rb := (match oi with
                 | Some ei =>
                     let okb := kbase K in
                     let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
                     let br2 := match okb with Some _ => ei_br ei | None => None end in
                     match pt_get gl (ei_gid ei) with
                     | Some (g, fl) => if inb g ei then chainKFM2B bc g fl K okb same_of br2 (memo0b B) else chainK2MB bc sxs K okb same_of br2 (memo0b B)
                     | None => chainK2MB bc sxs K okb same_of br2 (memo0b B)
                     end
                 | None => if is_pure K then ([K], B) else chainK2MB bc sxs K None (fun _ => false) None (memo0b B)
                 end) in
      fst rb ++ entriesGM2B bc sxs gl rest irest (snd rb)
  | _, _ => []
  end.
Lemma entriesGM2B_eq : forall fk t sxs bnds kn infos B,
  NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) (map fst sxs) -> Forall (sx_ok (mkbc fk)) sxs -> Forall2 (EINF (mkbc fk) t) kn infos ->
  blk_ok (mkbc fk) B ->
  entriesGM2B (mkbc fk) sxs (mk_glF (mkbc fk) bnds sxs) kn infos B = entriesGM (mkbc fk) sxs (mk_glF (mkbc fk) bnds sxs) kn infos.
Proof.
  intros fk t sxs bnds kn infos B HT HS HSX HF. pose proof (rt_fun_mk (mkbc fk) (mkbc_rt fk)) as RTF. revert B.
  induction HF as [|K oi rest irest HK HF IH]; intros B HB; [reflexivity|].
  cbn [entriesGM2B entriesGM].
  assert (K2 : forall okb same_of br2, (forall kb, okb = Some kb -> kbase K = Some kb) ->
            fst (chainK2MB (mkbc fk) sxs K okb same_of br2 (memo0b B)) = chainK2M (mkbc fk) sxs K okb same_of br2 memo0
            /\ blk_ok (mkbc fk) (snd (chainK2MB (mkbc fk) sxs K okb same_of br2 (memo0b B)))).
  { intros okb same_of br2 HB0. destruct (chainK2MB_spec (mkbc fk) RTF sxs K okb same_of br2 (memo0b B) HSX (kmemo_ok0b _ K B HB)) as [E1 E2].
    split; [|exact E2]. rewrite E1. rewrite !(chainK2M_eq (mkbc fk) RTF); try assumption; [reflexivity | apply kmemo_ok0 | apply kmemo_ok0b; exact HB]. }
  destruct oi as [ei|].
  2:{ destruct (is_pure K); [cbn [fst snd]; f_equal; apply IH; exact HB|].
      destruct (K2 None (fun _ => false) None) as [E1 E2]; [discriminate|]. rewrite E1. f_equal. apply IH. exact E2. }
  unfold mk_glF. rewrite !pt_get_map.
  destruct (pt_get bnds (ei_gid ei)) as [g|].
  2:{ destruct (K2 (kbase K) (match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end) (match kbase K with Some _ => ei_br ei | None => None end)) as [E1 E2]; [intros kb H; exact H|].
      rewrite E1. f_equal. apply IH. exact E2. }
  destruct (inb g ei) eqn:Hinb.
  2:{ destruct (K2 (kbase K) (match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end) (match kbase K with Some _ => ei_br ei | None => None end)) as [E1 E2]; [intros kb H; exact H|].
      rewrite E1. f_equal. apply IH. exact E2. }
  assert (FLOK : fl_ok (mkbc fk) (mk_flF (cg_of (mkbc fk) g) g sxs)) by (apply mk_flF_ok; exact HSX).
  destruct (chainKFM2B_spec (mkbc fk) RTF g (mk_flF (cg_of (mkbc fk) g) g sxs) K (kbase K)
              (match kbase K with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end) (match kbase K with Some _ => ei_br ei | None => None end)
              (memo0b B) FLOK (kmemo_ok0b _ K B HB)) as [E1 E2].
  rewrite E1. f_equal; [|apply IH; exact E2].
  assert (IMG : kbase K = None -> img_okF (mkbc fk) g (mk_flF (cg_of (mkbc fk) g) g sxs)).
  { intros HN. cbn [EINF] in HK. destruct HK as (HD & HIn & Hbr).
    assert (Hm : exists m, ei_m ei = Some m) by (unfold inb in Hinb; destruct (ei_m ei) as [m|]; [exists m; reflexivity|discriminate]).
    destruct Hm as [m Hm].
    destruct (kdescr_kbase _ _ _ _ HD) as [HB0|(lo & hi & -> & Hkb & Hk)]; [rewrite HB0 in HN; discriminate|].
    rewrite Hkb in HIn, Hbr. exact (img_okF_mk fk t g ei m sxs HT HS Hkb HIn Hbr Hinb Hm). }
  rewrite (chainKFM2_eq (mkbc fk) RTF); [|exact FLOK | apply kmemo_ok0b; exact HB | intros kb H; exact H | exact IMG].
  rewrite (chainKFM_eq (mkbc fk) RTF); [reflexivity | exact FLOK | apply kmemo_ok0 | intros kb H; exact H].
Qed.

Definition carryGFL2 (bc : bctx) (log : list sentry) (lrs : list (list positive)) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := fst (mk_stxsFC bc log lrs nt_empty) in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_partM bc sxs ++ entriesGM2B bc sxs (mk_glV bc (gs_bnds gs) sxs) kn infos [].
Definition carryKFL2 (bc : bctx) (log : list sentry) (lrs : list (list positive)) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryGFL2 bc log lrs kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryKFL2_eq : forall fk log lrs kn hints, lrs = map (regsE (mkbc fk)) log ->
  carryKFL2 (mkbc fk) log lrs kn hints = carryKFL (mkbc fk) log lrs kn hints.
Proof.
  intros fk log lrs kn hints L. unfold carryKFL2, carryKFL. destruct log as [|s0 older]; [reflexivity|]. destruct hints; [|reflexivity].
  f_equal. f_equal. unfold carryGFL2, carryGFL.
  rewrite (proj1 (mk_stxsFC_eq (mkbc fk) (s0 :: older) lrs nt_empty)), (mk_stxsFL_eq (mkbc fk) (s0 :: older) lrs nt_empty L).
  pose proof (mk_stxsF_eq (mkbc fk) (s0 :: older) nt_empty) as EM.
  pose proof (mk_stxsF_ok (mkbc fk) (s0 :: older) nt_empty (mkbc_rt fk)) as HSX.
  destruct (mk_stxsF (mkbc fk) (s0 :: older) nt_empty) as [sxs t0]. cbn [fst snd] in EM, HSX.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) EM) as (HT0 & HS0 & _ & _).
  destruct (scan_entries (mkbc fk) kn t0 gst_empty) as [[infos t1] gs] eqn:ES.
  destruct (scan_entries_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hmono & HF).
  assert (HS1 : Forall (SX_OK (mkbc fk) t1) (map fst sxs)).
  { apply Forall_impl with (P := SX_OK (mkbc fk) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hmono. }
  f_equal. rewrite mk_glV_eq. exact (entriesGM2B_eq fk t1 sxs (gs_bnds gs) kn infos [] HT1 HS1 HSX HF (Forall_nil _)).
Qed.
End CXFC2.
