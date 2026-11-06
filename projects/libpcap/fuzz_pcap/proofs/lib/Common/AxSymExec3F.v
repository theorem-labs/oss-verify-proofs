(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk SymExec AxSymExec3 AxSymExec3B AxSymExec3Sound. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.SymExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Ltac vmeq_cast := lazymatch goal with |- @eq ?T _ ?b => vm_cast_no_check (@eq_refl T b) end.
Ltac vmeq_conj := lazymatch goal with
  | |- _ /\ _ => split; vmeq_conj
  | |- @eq _ _ _ => vmeq_cast
  end.
(* [comment removed for export] *)
Ltac vmeq_refl := lazymatch goal with
  | |- @eq ?T _ ?b => tryif has_evar b then (vm_compute; reflexivity) else vm_cast_no_check (@eq_refl T b)
  | |- _ => vm_compute; reflexivity
  end.

(* [comment removed for export] *)
Module AX2W.
Import AX2. Import AX2B.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition gkeyW (kk : Z) : positive :=
  let g := Z.shiftr kk 10 in Z.to_pos (if Z.leb 0 g then 2 * g + 1 else - (2 * g))%Z.
Record gstW := GSW { gw_gid : ptree (ptree positive); gw_next : positive; gw_bnds : ptree (gval * expr) }.
Definition gsw_empty : gstW := GSW PTLeaf xH PTLeaf.
Definition ggroupW (gs : gstW) (bid : positive) (kk : Z) : positive * gstW :=
  let gk := gkeyW kk in
  let inner := match pt_get (gw_gid gs) bid with Some i => i | None => PTLeaf end in
  match pt_get inner gk with
  | Some gid => (gid, gs)
  | None => let gid := gw_next gs in
            (gid, GSW (pt_set bid (pt_set gk gid inner) (gw_gid gs)) (Pos.succ gid) (gw_bnds gs))
  end.
Definition bnd_addW (gs : gstW) (gid bid : positive) (obr : option (Z * Z)) (kb : expr) (lo hi : Z) : gstW :=
  GSW (gw_gid gs) (gw_next gs)
      (match pt_get (gw_bnds gs) gid with
       | Some ((b, o, (l, h)), kb0) => pt_set gid ((b, o, (Z.min l lo, Z.max h hi)), kb0) (gw_bnds gs)
       | None => pt_set gid ((bid, obr, (lo, hi)), kb) (gw_bnds gs)
       end).

(* [comment removed for export] *)
Fixpoint scanW (bc : bctx) (kn : list kentry) (t : ntab) (gs : gstW) : list (option einfo) * ntab * gstW :=
  match kn with
  | [] => ([], t, gs)
  | K :: rest =>
      match kbase K with
      | Some kb =>
          let '(r, t1) := intern bc t kb in
          let '(bid, bi) := r in
          match K with
          | KWord (SA _ kk) w _ =>
              if Nat.leb w 8 then
                let m := zlit64 (Z.of_nat w) in
                let '(gid, gs0) := ggroupW gs bid kk in
                let gs1 := bnd_addW gs0 gid bid (bi_br bi) kb kk (kk + m) in
                let '(infos, t2, gs2) := scanW bc rest t1 gs1 in
                (Some (EI bid gid kb (bi_br bi) kk (Some m)) :: infos, t2, gs2)
              else let '(infos, t2, gs2) := scanW bc rest t1 gs in (Some (EI bid xH kb (bi_br bi) 0 None) :: infos, t2, gs2)
          | _ => let '(infos, t2, gs2) := scanW bc rest t1 gs in (Some (EI bid xH kb (bi_br bi) 0 None) :: infos, t2, gs2)
          end
      | None => let '(infos, t2, gs2) := scanW bc rest t gs in (None :: infos, t2, gs2)
      end
  end.

(* [comment removed for export] *)
Fixpoint dsyn (bc : bctx) (D : list (saddr * expr)) (kb : expr) (lo hi : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r =>
      if (if expr_eqb kb (a_base c) then Z.leb (a_off c) lo else false) then
        match xloB bc m with
        | Some ml => if Z.leb hi (a_off c + ml) then true else dsyn bc r kb lo hi
        | None => dsyn bc r kb lo hi
        end
      else dsyn bc r kb lo hi
  end.

(* [comment removed for export] *)
Definition verdictW (bc : bctx) (kb : expr) (g : gval) (sx : stx) : bool :=
  match g with
  | (b, obr, (glo, ghi)) =>
      if Pos.eqb b (sx_bid sx) then
        (if Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) glo then true else Z.leb ghi (a_off (sx_a sx)))
      else if verdict sx g then true
      else dsyn bc (sp_D (sx_sp sx)) kb glo ghi
  end.

Fixpoint mk_flV (vd : stx -> bool) (sxs : list stx) : list (stx * list stx) :=
  match sxs with
  | [] => []
  | sx :: rest => if vd sx then mk_flV vd rest else (sx, rest) :: mk_flV vd rest
  end.
Definition glW : Type := ptree (gval * expr * list (stx * list stx)).
Definition mk_glW (bc : bctx) (bnds : ptree (gval * expr)) (sxs : list stx) : glW :=
  pt_map (fun ge => match ge with (g, kb) => (g, kb, mk_flV (verdictW bc kb g) sxs) end) bnds.

(* [comment removed for export] *)
Fixpoint chainKN (bc : bctx) (sxs : list stx) (K : kentry) : list kentry :=
  match sxs with
  | [] => [K]
  | sx :: rest =>
      match prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K false None with
      | PKeep => chainKN bc rest K
      | PRepl l => flat_map (fun K' => match kbase K' with None => chainKN bc rest K' | Some _ => chain_slow bc rest [K'] end) l
      end
  end.
Fixpoint entriesW (bc : bctx) (sxs : list stx) (gl : glW) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           match K with
           | KWord _ w _ =>
               if Nat.leb w 8 then
                 match pt_get gl (ei_gid ei) with
                 | Some (g, kb, fl) =>
                     if (if inb g ei then expr_eqb kb (ei_kb ei) else false)
                     then chainKF bc fl K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                     else chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                 | None => chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                 end
               else chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
           | _ => chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
           end
       | None => chainKN bc sxs K
       end) ++ entriesW bc sxs gl rest irest
  | _, _ => []
  end.


(* [comment removed for export] *)
Fixpoint scan_stores (sxs : list stx) (gs : gstW) : list (option positive) * gstW :=
  match sxs with
  | [] => ([], gs)
  | sx :: rest =>
      if Nat.leb (sx_w sx) 8 then
        let kk := a_off (sx_a sx) in
        let m := zlit64 (Z.of_nat (sx_w sx)) in
        let '(gid, gs0) := ggroupW gs (sx_bid sx) kk in
        let gs1 := bnd_addW gs0 gid (sx_bid sx) (sx_br sx) (a_base (sx_a sx)) kk (kk + m) in
        let '(ogs, gs2) := scan_stores rest gs1 in
        (Some gid :: ogs, gs2)
      else let '(ogs, gs2) := scan_stores rest gs in (None :: ogs, gs2)
  end.
Definition tblS : Type := ptree (gval * expr * list (stx * list stx)).
Definition tbl_push (bc : bctx) (sx : stx) (newer : list stx) (t : tblS) : tblS :=
  pt_map (fun ge => match ge with (g, kb, l) => (g, kb, if verdictW bc kb g sx then l else (sx, newer) :: l) end) t.
Definition tbl_init (bnds : ptree (gval * expr)) : tblS :=
  pt_map (fun ge => match ge with (g, kb) => (g, kb, []) end) bnds.
Definition sx_ei (sx : stx) (gid : positive) : einfo :=
  EI (sx_bid sx) gid (a_base (sx_a sx)) (sx_br sx) (a_off (sx_a sx)) (Some (zlit64 (Z.of_nat (sx_w sx)))).
Fixpoint stores_partW (bc : bctx) (sxs : list stx) (ogs : list (option positive)) (t0 : tblS) : list kentry * tblS :=
  match sxs with
  | [] => ([], t0)
  | sx :: newer =>
      let '(og, ogs') := match ogs with [] => (None, []) | og :: r => (og, r) end in
      let '(res, t1) := stores_partW bc newer ogs' t0 in
      let item := KWord (sx_a sx) (sx_w sx) (sx_v sx) in
      let okb := Some (a_base (sx_a sx)) in
      let ch := match og with
                | Some gid =>
                    match pt_get t1 gid with
                    | Some (g, kb, fl) =>
                        if (if Nat.leb (sx_w sx) 8 then (if inb g (sx_ei sx gid) then expr_eqb kb (a_base (sx_a sx)) else false) else false)
                        then chainKF bc fl item okb (Pos.eqb (sx_bid sx)) (sx_br sx)
                        else chainK2 bc newer item okb (Pos.eqb (sx_bid sx)) (sx_br sx)
                    | None => chainK2 bc newer item okb (Pos.eqb (sx_bid sx)) (sx_br sx)
                    end
                | None => chainK2 bc newer item okb (Pos.eqb (sx_bid sx)) (sx_br sx)
                end in
      (res ++ ch, tbl_push bc sx newer t1)
  end.

Definition carryW (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxs bc log nt_empty in
  let '(r, gs) := scanW bc kn t0 gsw_empty in
  let '(infos, _) := r in
  let '(ogs, gss) := scan_stores sxs gsw_empty in
  fst (stores_partW bc sxs ogs (tbl_init (gw_bnds gss))) ++ entriesW bc sxs (mk_glW bc (gw_bnds gs) sxs) kn infos.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mk_glW_get : forall bc bnds sxs gid,
  pt_get (mk_glW bc bnds sxs) gid =
  match pt_get bnds gid with Some (g, kb) => Some (g, kb, mk_flV (verdictW bc kb g) sxs) | None => None end.
Proof.
  intros bc bnds sxs gid. unfold mk_glW. rewrite pt_get_map. destruct (pt_get bnds gid) as [[g kb]|]; reflexivity.
Qed.

Lemma chainKF_eqV : forall bc vd sxs K okb same_of br2,
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

Lemma dsyn_in_sides : forall bc D kb glo ghi k n,
  dsyn bc D kb glo ghi = true -> glo <= k -> k + n <= ghi -> in_sidesB bc D kb k n = true.
Proof.
  intros bc D kb glo ghi k n. induction D as [|[c m] r IH]; intros H Hlo Hhi; cbn [dsyn] in H; [discriminate|].
  cbn [in_sidesB].
  destruct (if expr_eqb kb (a_base c) then Z.leb (a_off c) glo else false) eqn:E1.
  - destruct (expr_eqb kb (a_base c)) eqn:E2; [|discriminate]. apply Z.leb_le in E1.
    destruct (xloB bc m) as [ml|] eqn:E3.
    + destruct (Z.leb ghi (a_off c + ml)) eqn:E4.
      * apply Z.leb_le in E4. unfold sub_itvB. rewrite E2.
        replace (Z.leb (a_off c) k) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite E3.
        replace (Z.leb (k + n) (a_off c + ml)) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
      * destruct (sub_itvB bc kb k n c m); [reflexivity|]. apply IH; assumption.
    + destruct (sub_itvB bc kb k n c m); [reflexivity|]. apply IH; assumption.
  - destruct (sub_itvB bc kb k n c m); [reflexivity|]. apply IH; assumption.
Qed.

Lemma zlit64_nat8 : forall w, Nat.leb w 8 = true -> zlit64 (Z.of_nat w) = Z.of_nat w.
Proof.
  intros w H. apply Nat.leb_le in H. unfold zlit64, two64.
  replace (Z.leb 0 (Z.of_nat w) && Z.ltb (Z.of_nat w) (2 ^ 64))%bool with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; [apply Z.leb_le; lia|apply Z.ltb_lt; lia].
Qed.

(* [comment removed for export] *)
Lemma verdictW_keep : forall bc sx kb g ei kk w v,
  ei_br ei = base_rangeB bc (ei_kb ei) ->
  Nat.leb w 8 = true -> ei_m ei = Some (zlit64 (Z.of_nat w)) -> ei_k ei = kk ->
  inb g ei = true -> expr_eqb kb (ei_kb ei) = true -> verdictW bc kb g sx = true ->
  prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) (KWord (SA (ei_kb ei) kk) w v)
            (Pos.eqb (ei_bid ei) (sx_bid sx)) (ei_br ei) = PKeep.
Proof.
  intros bc sx kb g ei kk w v Hbr Hw Hm Hk Hinb Hkb Hv.
  apply p_expr_eqb_eq in Hkb. subst kb.
  pose proof (zlit64_nat8 w Hw) as Zw.
  pose proof Hinb as Hinb0.
  destruct g as [[b obr] [glo ghi]].
  unfold inb in Hinb. rewrite Hm in Hinb.
  apply andb_prop in Hinb as [Hinb H4]. apply andb_prop in Hinb as [Hinb H3]. apply andb_prop in Hinb as [H1 H2].
  apply Pos.eqb_eq in H1. subst b. apply Z.leb_le in H3. apply Z.leb_le in H4. rewrite Hk, Zw in *.
  unfold verdictW in Hv.
  destruct (Pos.eqb (ei_bid ei) (sx_bid sx)) eqn:Eb.
  - (* [comment removed for export] *)
    unfold prune1pcK.
    replace ((kk + Z.of_nat w <=? a_off (sx_a sx)) || (a_off (sx_a sx) + Z.of_nat (sx_w sx) <=? kk))%bool with true
      by (symmetry; apply Bool.orb_true_iff;
          destruct (Z.leb (a_off (sx_a sx) + Z.of_nat (sx_w sx)) glo) eqn:E5;
          [apply Z.leb_le in E5; right; apply Z.leb_le; lia | apply Z.leb_le in Hv; left; apply Z.leb_le; lia]).
    reflexivity.
  - destruct (verdict sx (ei_bid ei, obr, (glo, ghi))) eqn:Hvd.
    + (* [comment removed for export] *)
      rewrite <- Zw in Hm.
      destruct (verdict_inb_num sx _ ei _ Hvd Hinb0 Hm) as (_ & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
      rewrite Hbr. rewrite Hbr in Hbr2.
      eapply (prune1pcK_keep_based bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) (KWord (SA (ei_kb ei) kk) w v) (ei_kb ei) kk (zlit64 (Z.of_nat w)) lo1 hi1 lo2 hi2);
        [reflexivity | reflexivity | exact Hsp | exact Hbr2 | rewrite Hk in Hnum; exact Hnum].
    + (* [comment removed for export] *)
      unfold prune1pcK.
      assert (RA : ranges_apart_pcB bc (sx_sp sx) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx)) (ei_br ei) (ei_kb ei) kk (elen w) = true).
      { unfold ranges_apart_pcB, elen. cbv zeta.
        destruct (match sp_rng (sx_sp sx), ei_br ei with
                  | Some (lo1, hi1), Some (lo2, hi2) =>
                      ((hi1 + a_off (sx_a sx) + zlit64 (Z.of_nat (sx_w sx)) <=? lo2 + kk) || (hi2 + kk + zlit64 (Z.of_nat w) <=? lo1 + a_off (sx_a sx)))%bool
                  | _, _ => false end); [reflexivity|].
        rewrite Zw. rewrite (dsyn_in_sides bc _ _ glo ghi kk (Z.of_nat w) Hv H3 H4). reflexivity. }
      rewrite RA. reflexivity.
Qed.

Lemma verdictW_keep_a : forall bc sx kb g ei a w v,
  ei_br ei = base_rangeB bc (ei_kb ei) -> a_base a = ei_kb ei -> a_off a = ei_k ei ->
  Nat.leb w 8 = true -> ei_m ei = Some (zlit64 (Z.of_nat w)) ->
  inb g ei = true -> expr_eqb kb (ei_kb ei) = true -> verdictW bc kb g sx = true ->
  prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) (KWord a w v)
            (Pos.eqb (ei_bid ei) (sx_bid sx)) (ei_br ei) = PKeep.
Proof.
  intros bc sx kb g ei [b k] w v Hbr Hb Hk Hw Hm Hi Hkb Hv. cbn [a_base a_off] in Hb, Hk. subst b.
  exact (verdictW_keep bc sx kb g ei k w v Hbr Hw Hm (eq_sym Hk) Hi Hkb Hv).
Qed.

Lemma chainKN_eq : forall fk sxs K,
  Forall (fun sx => sx_sp sx = mk_sprepB (mkbc fk) (a_base (sx_a sx)) (a_off (sx_a sx)) (elen (sx_w sx))) sxs ->
  kbase K = None -> chainKN (mkbc fk) sxs K = chain_slow (mkbc fk) sxs [K].
Proof.
  intros fk sxs. induction sxs as [|sx rest IH]; intros K HS HK; [reflexivity|].
  apply Forall_cons_iff in HS as [H1 HS]. cbn [chainKN chain_slow flat_map]. rewrite app_nil_r.
  unfold g1cB at 1.
  assert (E : pk_list K (prune1pcK (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K false None)
              = fst (fst (prune1pcB (mkbc fk) (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K [] (obrB (mkbc fk) K)))).
  { autorewrite with bceq. unfold obrB. rewrite HK. apply prune1pcK_eq. rewrite HK. exact I. }
  destruct (prune1pcK _ _ _ _ _ K _ None) as [|l]; cbn [pk_list] in E; rewrite <- E.
  - apply IH; assumption.
  - rewrite (chain_slow_flat_map _ rest l). f_equal. apply functional_extensionality. intros K'.
    destruct (kbase K') as [kb'|] eqn:HB'; [reflexivity|]. apply IH; assumption.
Qed.

(* [comment removed for export] *)
Definition EINFW (bc : bctx) (t : ntab) (K : kentry) (oi : option einfo) : Prop :=
  match oi with
  | None => kbase K = None
  | Some ei => kbase K = Some (ei_kb ei) /\ In (ei_kb ei, ei_bid ei) (nt_bucket t (bkey (ei_kb ei)))
               /\ ei_br ei = base_rangeB bc (ei_kb ei)
               /\ (forall a w v, K = KWord a w v -> Nat.leb w 8 = true -> a_off a = ei_k ei /\ ei_m ei = Some (zlit64 (Z.of_nat w)))
  end.
Lemma EINFW_mono : forall bc t t' K oi,
  (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)) -> EINFW bc t K oi -> EINFW bc t' K oi.
Proof.
  intros bc t t' K [ei|] Hm H; cbn [EINFW] in *; [|exact H].
  destruct H as (A & B & C & D). split; [exact A|]. split; [apply Hm; exact B|]. split; [exact C|exact D].
Qed.

Lemma scanW_ok : forall fk kn t gs infos t' gs',
  NTI (mkbc fk) t -> scanW (mkbc fk) kn t gs = (infos, t', gs') ->
  NTI (mkbc fk) t'
  /\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k))
  /\ Forall2 (EINFW (mkbc fk) t') kn infos.
Proof.
  intros fk kn. induction kn as [|K rest IH]; intros t gs infos t' gs' HT H.
  - cbn in H. injection H as <- <- <-. split; [exact HT|]. split; [intros; assumption|]. constructor.
  - cbn [scanW] in H.
    destruct (kbase K) as [kb|] eqn:HB.
    + destruct (intern (mkbc fk) t kb) as [[bid bi] t1] eqn:EIn.
      destruct (intern_ok _ _ _ _ _ _ HT EIn) as (HT1 & Hbi & HIn & Hm1).
      assert (GEN : forall gs1 ei, ei_kb ei = kb -> ei_bid ei = bid -> ei_br ei = bi_br bi ->
                (forall a w v, K = KWord a w v -> Nat.leb w 8 = true -> a_off a = ei_k ei /\ ei_m ei = Some (zlit64 (Z.of_nat w))) ->
                scanW (mkbc fk) rest t1 gs1 = (match infos with [] => [] | _ :: r => r end, t', gs') ->
                infos = Some ei :: match infos with [] => [] | _ :: r => r end ->
                NTI (mkbc fk) t' /\ (forall k p, In p (nt_bucket t k) -> In p (nt_bucket t' k)) /\ Forall2 (EINFW (mkbc fk) t') (K :: rest) infos).
      { intros gs1 ei E1 E2 E3 E4 ES Hinf.
        destruct (IH _ _ _ _ _ HT1 ES) as (HT2 & Hm2 & HF).
        split; [exact HT2|]. split; [intros k p Hp; apply Hm2; apply Hm1; exact Hp|].
        rewrite Hinf. constructor; [|exact HF]. cbn [EINFW].
        rewrite E1, E2, E3. split; [exact HB|]. split; [apply Hm2; exact HIn|]. split; [rewrite Hbi; reflexivity|exact E4]. }
      destruct K as [[kb0 kk] w v|[kb0 kk] len|[kb0 kk] len bk|lo hi|e' m'|e' lo' hi'|[kb0 kk] n|a1 n1 a2 n2|[kb0 kk] len fc|[kb0 kk] len];
        cbn [kbase] in HB; try discriminate; injection HB as <-.
      * destruct (Nat.leb w 8) eqn:Hw.
        -- destruct (ggroupW gs bid kk) as [gid gs0] eqn:EG.
           destruct (scanW (mkbc fk) rest t1 (bnd_addW gs0 gid bid (bi_br bi) kb0 kk (kk + zlit64 (Z.of_nat w)))) as [[infos2 t2] gs2] eqn:ES.
           injection H as <- <- <-.
           eapply (GEN _ (EI bid gid kb0 (bi_br bi) kk (Some (zlit64 (Z.of_nat w))))); try reflexivity; [|exact ES].
           intros a w' v' EQ _. injection EQ as <- <- <-. split; reflexivity.
        -- destruct (scanW (mkbc fk) rest t1 gs) as [[infos2 t2] gs2] eqn:ES. injection H as <- <- <-.
           eapply (GEN _ (EI bid xH kb0 (bi_br bi) 0 None)); try reflexivity; [|exact ES].
           intros a w' v' EQ Hw'. injection EQ as <- <- <-. rewrite Hw in Hw'. discriminate.
      * destruct (scanW (mkbc fk) rest t1 gs) as [[infos2 t2] gs2] eqn:ES. injection H as <- <- <-.
        eapply (GEN _ (EI bid xH kb0 (bi_br bi) 0 None)); try reflexivity; [|exact ES]. intros a w' v' EQ. discriminate.
      * destruct (scanW (mkbc fk) rest t1 gs) as [[infos2 t2] gs2] eqn:ES. injection H as <- <- <-.
        eapply (GEN _ (EI bid xH kb0 (bi_br bi) 0 None)); try reflexivity; [|exact ES]. intros a w' v' EQ. discriminate.
      * destruct (scanW (mkbc fk) rest t1 gs) as [[infos2 t2] gs2] eqn:ES. injection H as <- <- <-.
        eapply (GEN _ (EI bid xH kb0 (bi_br bi) 0 None)); try reflexivity; [|exact ES]. intros a w' v' EQ. discriminate.
      * destruct (scanW (mkbc fk) rest t1 gs) as [[infos2 t2] gs2] eqn:ES. injection H as <- <- <-.
        eapply (GEN _ (EI bid xH kb0 (bi_br bi) 0 None)); try reflexivity; [|exact ES]. intros a w' v' EQ. discriminate.
    + destruct (scanW (mkbc fk) rest t gs) as [[infos2 t2] gs2] eqn:ES.
      injection H as <- <- <-.
      destruct (IH _ _ _ _ _ HT ES) as (HT2 & Hm2 & HF).
      split; [exact HT2|]. split; [exact Hm2|]. constructor; [exact HB | exact HF].
Qed.

Lemma entriesW_eq : forall fk sxs bnds kn infos t1,
  NTI (mkbc fk) t1 -> Forall (SX_OK (mkbc fk) t1) sxs -> Forall2 (EINFW (mkbc fk) t1) kn infos ->
  entriesW (mkbc fk) sxs (mk_glW (mkbc fk) bnds sxs) kn infos = chainRo fk (map strip sxs) kn.
Proof.
  intros fk sxs bnds kn infos t1 HT HS HF. induction HF as [|K oi rest irest HK HF IH].
  - cbn. clear. induction sxs as [|sx r IH]; [reflexivity|]. cbn. destruct (strip sx). exact IH.
  - cbn [entriesW]. change (K :: rest) with ([K] ++ rest). rewrite chainRo_app, IH. f_equal.
    rewrite <- (chain_slow_eq fk sxs [K] (Forall_SX_sp _ _ _ HS)).
    pose proof (Forall_SX_sp _ _ _ HS) as HSP.
    destruct oi as [ei|]; cbn [EINFW] in HK.
    + destruct HK as (HB & HIn & Hbr & HKW).
      assert (FULL : chainK2 (mkbc fk) sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei) = chain_slow (mkbc fk) sxs [K]).
      { apply chainK2_eq; [exact HSP|reflexivity|]. rewrite HB.
        split; [exact Hbr|]. exact (Forall_SX_same _ _ _ _ _ HT HIn HS). }
      destruct K as [[kb0 kk] w v|[kb0 kk] len|[kb0 kk] len bk|lo hi|e' m'|e' lo' hi'|[kb0 kk] n|a1 n1 a2 n2|[kb0 kk] len fc|[kb0 kk] len];
        try exact FULL.
      destruct (Nat.leb w 8) eqn:Hw; [|exact FULL].
      rewrite mk_glW_get. destruct (pt_get bnds (ei_gid ei)) as [[g kb]|]; [|exact FULL].
      destruct (if inb g ei then expr_eqb kb (ei_kb ei) else false) eqn:Hc; [|exact FULL].
      rewrite <- FULL. apply chainKF_eqV.
      intros sx Hsx Hv.
      cbn [kbase] in HB. injection HB as ->.
      destruct (HKW _ _ _ eq_refl Hw) as (Hk & Hm). cbn [a_off] in Hk.
      destruct (inb g ei) eqn:Hi; [|discriminate].
      exact (verdictW_keep (mkbc fk) sx kb g ei kk w v Hbr Hw Hm (eq_sym Hk) Hi Hc Hv).
    + apply chainKN_eq; [exact HSP | exact HK].
Qed.

Lemma stores_partW_tbl : forall bc bnds sxs ogs gid,
  pt_get (snd (stores_partW bc sxs ogs (tbl_init bnds))) gid =
  match pt_get bnds gid with Some (g, kb) => Some (g, kb, mk_flV (verdictW bc kb g) sxs) | None => None end.
Proof.
  intros bc bnds sxs. induction sxs as [|sx newer IH]; intros ogs gid.
  - cbn [stores_partW snd]. unfold tbl_init. rewrite pt_get_map. destruct (pt_get bnds gid) as [[g kb]|]; reflexivity.
  - cbn [stores_partW].
    destruct (match ogs with [] => (None, []) | og :: r => (og, r) end) as [og ogs'].
    destruct (stores_partW bc newer ogs' (tbl_init bnds)) as [res t1] eqn:E.
    cbn [snd]. unfold tbl_push. rewrite pt_get_map.
    pose proof (IH ogs' gid) as H. rewrite E in H. cbn [snd] in H. rewrite H.
    destruct (pt_get bnds gid) as [[g kb]|]; [|reflexivity]. cbn [mk_flV]. reflexivity.
Qed.

Lemma stores_partW_eq : forall fk t sxs ogs bnds,
  NTI (mkbc fk) t -> Forall (SX_OK (mkbc fk) t) sxs ->
  fst (stores_partW (mkbc fk) sxs ogs (tbl_init bnds)) = stores_part (mkbc fk) sxs.
Proof.
  intros fk t sxs. induction sxs as [|sx newer IH]; intros ogs bnds HT HS; [reflexivity|].
  apply Forall_cons_iff in HS as [H1 HS].
  cbn [stores_partW stores_part].
  destruct (match ogs with [] => (None, []) | og :: r => (og, r) end) as [og ogs'].
  pose proof (stores_partW_tbl (mkbc fk) bnds newer ogs') as HTB.
  destruct (stores_partW (mkbc fk) newer ogs' (tbl_init bnds)) as [res t1] eqn:E.
  cbn [fst]. pose proof (IH ogs' bnds HT HS) as IH'. rewrite E in IH'. cbn [fst] in IH'. rewrite IH'. f_equal.
  destruct H1 as (HIn & Hbr & _).
  pose proof (Forall_SX_sp _ _ _ HS) as HSP.
  destruct og as [gid|]; [|reflexivity].
  specialize (HTB gid). cbn [snd] in HTB. rewrite HTB.
  destruct (pt_get bnds gid) as [[g kb]|]; [|reflexivity].
  destruct (Nat.leb (sx_w sx) 8) eqn:Hw; [|reflexivity].
  destruct (inb g (sx_ei sx gid)) eqn:Hi; [|reflexivity].
  destruct (expr_eqb kb (a_base (sx_a sx))) eqn:Hkb; [|reflexivity].
  apply chainKF_eqV. intros sx' _ Hv.
  exact (verdictW_keep_a (mkbc fk) sx' kb g (sx_ei sx gid) (sx_a sx) (sx_w sx) (sx_v sx) Hbr eq_refl eq_refl Hw eq_refl Hi Hkb Hv).
Qed.

Lemma carryW_eq : forall log kn,
  carryW (mkbc (facts_of kn)) log kn = SPRo (facts_of kn) (rev log) ++ chainRo (facts_of kn) (rev log) kn.
Proof.
  intros log kn. unfold carryW.
  destruct (mk_stxs (mkbc (facts_of kn)) log nt_empty) as [sxs t0] eqn:E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & Hmap & _).
  destruct (scanW (mkbc (facts_of kn)) kn t0 gsw_empty) as [[infos t1] gs] eqn:ES.
  destruct (scanW_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & Hm & HF).
  assert (HS1 : Forall (SX_OK (mkbc (facts_of kn)) t1) sxs).
  { apply Forall_impl with (P := SX_OK (mkbc (facts_of kn)) t0); [|exact HS0]. intros sx. apply SX_OK_mono. exact Hm. }
  destruct (scan_stores sxs gsw_empty) as [ogs gss].
  rewrite (stores_partW_eq _ _ _ _ _ HT0 HS0), (stores_part_eq _ _ _ HT0 HS0), (entriesW_eq _ _ _ _ _ _ HT1 HS1 HF), Hmap. reflexivity.
Qed.

(* [comment removed for export] *)
Definition carryWK (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryW bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryWK_eq : forall log kn hints,
  carryWK (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. unfold carryWK. destruct log as [|s older]; [reflexivity|].
  destruct hints as [|h hs]; [|apply carryB_eq].
  rewrite carry_vertical, carryW_eq. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zdesc (K : kentry) : option (Z * Z) :=
  match K with
  | KZero (SA _ kk) (ELit z) | KFill (SA _ kk) (ELit z) _ | KUnk (SA _ kk) (ELit z) | KBlob (SA _ kk) (ELit z) _ => Some (kk, zlit64 z)
  | _ => None
  end.

Fixpoint zhulls (kn : list kentry) (infos : list (option einfo)) (t : ptree (gval * expr)) : ptree (gval * expr) :=
  match kn, infos with
  | K :: rest, Some ei :: irest =>
      match zdesc K with
      | Some (kk, m) =>
          zhulls rest irest
            (match pt_get t (ei_bid ei) with
             | Some ((b, o, (l, h)), kb0) => pt_set (ei_bid ei) ((b, o, (Z.min l kk, Z.max h (kk + m))), kb0) t
             | None => pt_set (ei_bid ei) ((ei_bid ei, ei_br ei, (kk, kk + m)), ei_kb ei) t
             end)
      | None => zhulls rest irest t
      end
  | _ :: rest, None :: irest => zhulls rest irest t
  | _, _ => t
  end.

Definition verdictZ (bc : bctx) (kb : expr) (g : gval) (sx : stx) : bool :=
  match g with
  | (b, obr, (glo, ghi)) =>
      if Pos.eqb b (sx_bid sx) then false
      else if verdict sx g then true
      else dsyn bc (sp_D (sx_sp sx)) kb glo ghi
  end.

Definition mk_glZ (bc : bctx) (bnds : ptree (gval * expr)) (sxs : list stx) : glW :=
  pt_map (fun ge => match ge with (g, kb) => (g, kb, mk_flV (verdictZ bc kb g) sxs) end) bnds.

Lemma mk_glZ_get : forall bc bnds sxs gid,
  pt_get (mk_glZ bc bnds sxs) gid =
  match pt_get bnds gid with Some (g, kb) => Some (g, kb, mk_flV (verdictZ bc kb g) sxs) | None => None end.
Proof.
  intros bc bnds sxs gid. unfold mk_glZ. rewrite pt_get_map. destruct (pt_get bnds gid) as [[g kb]|]; reflexivity.
Qed.

Fixpoint entriesZ (bc : bctx) (sxs : list stx) (gl glz : glW) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           match K with
           | KWord _ w _ =>
               if Nat.leb w 8 then
                 match pt_get gl (ei_gid ei) with
                 | Some (g, kb, fl) =>
                     if (if inb g ei then expr_eqb kb (ei_kb ei) else false)
                     then chainKF bc fl K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                     else chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                 | None => chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                 end
               else chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
           | _ =>
               match zdesc K with
               | Some (kk, m) =>
                   match pt_get glz (ei_bid ei) with
                   | Some (g, kb, fl) =>
                       if (if inb g (EI (ei_bid ei) xH (ei_kb ei) (ei_br ei) kk (Some m)) then expr_eqb kb (ei_kb ei) else false)
                       then chainKF bc fl K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                       else chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                   | None => chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
                   end
               | None => chainK2 bc sxs K (kbase K) (Pos.eqb (ei_bid ei)) (ei_br ei)
               end
           end
       | None => chainKN bc sxs K
       end) ++ entriesZ bc sxs gl glz rest irest
  | _, _ => []
  end.

Lemma zdesc_kdescr : forall K kk m kb0, zdesc K = Some (kk, m) -> kbase K = Some kb0 -> kdescr K = Some (kb0, kk, Some m).
Proof.
  intros K kk m kb0 H HB.
  destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
    cbn [zdesc kdescr kbase] in *; try discriminate;
    destruct len as [z| | | | | | |]; try discriminate; injection H as <- <-; injection HB as <-; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma verdictZ_keep : forall bc sx kb g bid br K kb0 kk m,
  br = base_rangeB bc kb0 -> kbase K = Some kb0 -> zdesc K = Some (kk, m) ->
  inb g (EI bid xH kb0 br kk (Some m)) = true -> expr_eqb kb kb0 = true -> verdictZ bc kb g sx = true ->
  prune1pcK bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K (Pos.eqb bid (sx_bid sx)) br = PKeep.
Proof.
  intros bc sx kb g bid br K kb0 kk m Hbr HB HZ Hinb Hkb Hv.
  apply p_expr_eqb_eq in Hkb. subst kb.
  pose proof Hinb as Hinb0.
  destruct g as [[b obr] [glo ghi]].
  unfold inb in Hinb. cbn [ei_m ei_bid ei_br ei_k] in Hinb.
  apply andb_prop in Hinb as [Hinb H4]. apply andb_prop in Hinb as [Hinb H3]. apply andb_prop in Hinb as [H1 H2].
  apply Pos.eqb_eq in H1. subst b. apply Z.leb_le in H3. apply Z.leb_le in H4.
  unfold verdictZ in Hv. destruct (Pos.eqb bid (sx_bid sx)) eqn:Eb; [discriminate|].
  destruct (verdict sx (bid, obr, (glo, ghi))) eqn:Hvd.
  - (* [comment removed for export] *)
    destruct (verdict_inb_num sx _ _ m Hvd Hinb0 eq_refl) as (_ & lo1 & hi1 & lo2 & hi2 & Hsp & Hbr2 & Hnum).
    cbn [ei_br ei_k] in Hbr2, Hnum. rewrite Hbr. rewrite Hbr in Hbr2.
    exact (prune1pcK_keep_based bc (sx_sp sx) (sx_a sx) (sx_w sx) (sx_v sx) K kb0 kk m lo1 hi1 lo2 hi2
             HB (zdesc_kdescr K kk m kb0 HZ HB) Hsp Hbr2 Hnum).
  - (* [comment removed for export] *)
    pose proof (dsyn_in_sides bc _ _ glo ghi kk m Hv H3 H4) as HS.
    destruct K as [[b k] w' v|[b k] len|[b k] len bk|lo hi|e' m'|e' lo' hi'|[b k] n|a1 n1 a2 n2|[b k] len fc|[b k] len];
      cbn [zdesc kbase] in HZ, HB; try discriminate;
      destruct len as [z| | | | | | |]; try discriminate; injection HZ as <- <-; injection HB as <-;
      unfold prune1pcK; cbn [a_base a_off]; unfold ranges_apart_pcB; cbn [elen];
      rewrite HS; match goal with |- context [if ?c then true else true] => destruct c end; reflexivity.
Qed.

Lemma entriesZ_W : forall fk sxs gl bnds kn infos t1,
  NTI (mkbc fk) t1 -> Forall2 (EINFW (mkbc fk) t1) kn infos ->
  entriesZ (mkbc fk) sxs gl (mk_glZ (mkbc fk) bnds sxs) kn infos = entriesW (mkbc fk) sxs gl kn infos.
Proof.
  intros fk sxs gl bnds kn infos t1 HT HF. induction HF as [|K oi rest irest HK HF IH]; [reflexivity|].
  cbn [entriesZ entriesW]. rewrite IH. f_equal.
  destruct oi as [ei|]; [|reflexivity]. cbn [EINFW] in HK. destruct HK as (HB & HIn & Hbr & _).
  destruct K as [[kb0 kk] w v|[kb0 kk] len|[kb0 kk] len bk|lo hi|e' m'|e' lo' hi'|[kb0 kk] n|a1 n1 a2 n2|[kb0 kk] len fc|[kb0 kk] len];
    try reflexivity;
    (destruct (zdesc _) as [[zk zm]|] eqn:HZ; [|reflexivity]);
    rewrite mk_glZ_get; (destruct (pt_get bnds (ei_bid ei)) as [[g kb]|]; [|reflexivity]);
    (destruct (if inb g (EI (ei_bid ei) xH (ei_kb ei) (ei_br ei) zk (Some zm)) then expr_eqb kb (ei_kb ei) else false) eqn:Hc; [|reflexivity]);
    (destruct (inb g (EI (ei_bid ei) xH (ei_kb ei) (ei_br ei) zk (Some zm))) eqn:Hi; [|discriminate]);
    apply chainKF_eqV; intros sx _ Hv;
    exact (verdictZ_keep (mkbc fk) sx kb g (ei_bid ei) (ei_br ei) _ (ei_kb ei) zk zm Hbr HB HZ Hi Hc Hv).
Qed.

(* [comment removed for export] *)
Fixpoint sp_look (l : list (expr * Z * nat * sprep)) (b : expr) (kk : Z) (w : nat) : option sprep :=
  match l with
  | [] => None
  | (b', k', w', s) :: r => if (expr_eqb b' b && Z.eqb k' kk && Nat.eqb w' w)%bool then Some s else sp_look r b kk w
  end.
Fixpoint mk_stxsM_go (bc : bctx) (log : list sentry) (t : ntab) (memo : ptree (list (expr * Z * nat * sprep)))
  : list stx * ntab * ptree (list (expr * Z * nat * sprep)) :=
  match log with
  | [] => ([], t, memo)
  | SE a w v :: older =>
      let '(sxs, t1, memo1) := mk_stxsM_go bc older t memo in
      let '(r, t2) := intern bc t1 (a_base a) in
      let '(bid, bi) := r in
      let bucket := match pt_get memo1 bid with Some l => l | None => [] end in
      let '(sp, memo2) := match sp_look bucket (a_base a) (a_off a) w with
                          | Some s => (s, memo1)
                          | None => let s := mk_sprepB bc (a_base a) (a_off a) (elen w) in
                                    (s, pt_set bid ((a_base a, a_off a, w, s) :: bucket) memo1)
                          end in
      (STX a w v sp bid (bi_br bi) :: sxs, t2, memo2)
  end.
Definition mk_stxsM (bc : bctx) (log : list sentry) (t : ntab) : list stx * ntab :=
  let '(sxs, t', _) := mk_stxsM_go bc log t PTLeaf in (rev sxs, t').

Definition MEMO_OK (bc : bctx) (memo : ptree (list (expr * Z * nat * sprep))) : Prop :=
  forall id l, pt_get memo id = Some l -> forall b k w s, In (b, k, w, s) l -> s = mk_sprepB bc b k (elen w).

Lemma sp_look_ok : forall bc l b kk w s,
  (forall b' k' w' s', In (b', k', w', s') l -> s' = mk_sprepB bc b' k' (elen w')) ->
  sp_look l b kk w = Some s -> s = mk_sprepB bc b kk (elen w).
Proof.
  intros bc l b kk w s Hl. induction l as [|[[[b' k'] w'] s'] r IH]; cbn [sp_look]; [discriminate|].
  destruct (expr_eqb b' b && Z.eqb k' kk && Nat.eqb w' w)%bool eqn:E.
  - intros H. injection H as <-. apply andb_prop in E as [E E3]. apply andb_prop in E as [E1 E2].
    apply p_expr_eqb_eq in E1. apply Z.eqb_eq in E2. apply Nat.eqb_eq in E3. subst.
    exact (Hl _ _ _ _ (or_introl eq_refl)).
  - apply IH. intros. apply (Hl b'0 k'0 w'0 s'0). right. assumption.
Qed.

Lemma mk_stxsM_go_eq : forall bc log t memo, MEMO_OK bc memo ->
  let '(sxs, t', memo') := mk_stxsM_go bc log t memo in
  sxs = rev (fst (mk_stxs bc log t)) /\ t' = snd (mk_stxs bc log t) /\ MEMO_OK bc memo'.
Proof.
  intros bc log. induction log as [|[a w v] older IH]; intros t memo HM; [cbn; auto|].
  cbn [mk_stxsM_go mk_stxs].
  specialize (IH t memo HM).
  destruct (mk_stxsM_go bc older t memo) as [[sxs1 t1] memo1].
  destruct (mk_stxs bc older t) as [sxs0 t0]. cbn [fst snd] in IH. destruct IH as (-> & -> & HM1).
  destruct (intern bc t0 (a_base a)) as [[bid bi] t2].
  set (bucket := match pt_get memo1 bid with Some l => l | None => [] end).
  assert (HB : forall b' k' w' s', In (b', k', w', s') bucket -> s' = mk_sprepB bc b' k' (elen w')).
  { intros b' k' w' s' Hin. unfold bucket in Hin. destruct (pt_get memo1 bid) as [l|] eqn:El; [|destruct Hin].
    exact (HM1 bid l El b' k' w' s' Hin). }
  destruct (sp_look bucket (a_base a) (a_off a) w) as [s|] eqn:El.
  - pose proof (sp_look_ok bc bucket _ _ _ _ HB El) as ->. cbn [fst snd]. rewrite rev_app_distr. cbn. auto.
  - cbn [fst snd]. rewrite rev_app_distr. cbn. split; [reflexivity|]. split; [reflexivity|].
    intros id l Hg b' k' w' s' Hin.
    destruct (Pos.eq_dec id bid) as [->|Hne].
    + rewrite pt_gss in Hg. injection Hg as <-. destruct Hin as [Hin|Hin].
      * injection Hin as <- <- <- <-. reflexivity.
      * exact (HB b' k' w' s' Hin).
    + rewrite (pt_gso _ id bid _ memo1 Hne) in Hg. exact (HM1 id l Hg b' k' w' s' Hin).
Qed.

Lemma mk_stxsM_eq : forall bc log t, mk_stxsM bc log t = mk_stxs bc log t.
Proof.
  intros bc log t. unfold mk_stxsM.
  assert (HM0 : MEMO_OK bc PTLeaf) by (intros id l H; rewrite pt_get_leaf in H; discriminate).
  pose proof (mk_stxsM_go_eq bc log t PTLeaf HM0) as H.
  destruct (mk_stxsM_go bc log t PTLeaf) as [[sxs t'] memo']. destruct H as (-> & -> & _).
  rewrite rev_involutive. destruct (mk_stxs bc log t); reflexivity.
Qed.

Definition carryWZ (bc : bctx) (log : list sentry) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := mk_stxsM bc log nt_empty in
  let '(r, gs) := scanW bc kn t0 gsw_empty in
  let '(infos, _) := r in
  let '(ogs, gss) := scan_stores sxs gsw_empty in
  fst (stores_partW bc sxs ogs (tbl_init (gw_bnds gss)))
    ++ entriesZ bc sxs (mk_glW bc (gw_bnds gs) sxs) (mk_glZ bc (zhulls kn infos PTLeaf) sxs) kn infos.

Lemma carryWZ_eq : forall log kn, carryWZ (mkbc (facts_of kn)) log kn = carryW (mkbc (facts_of kn)) log kn.
Proof.
  intros log kn. unfold carryWZ, carryW. rewrite mk_stxsM_eq.
  destruct (mk_stxs (mkbc (facts_of kn)) log nt_empty) as [sxs t0] eqn:E.
  destruct (mk_stxs_ok _ _ _ _ _ (NTI_empty _) E) as (HT0 & HS0 & _ & _).
  destruct (scanW (mkbc (facts_of kn)) kn t0 gsw_empty) as [[infos t1] gs] eqn:ES.
  destruct (scanW_ok _ _ _ _ _ _ _ HT0 ES) as (HT1 & _ & HF).
  destruct (scan_stores sxs gsw_empty) as [ogs gss].
  f_equal. apply (entriesZ_W _ _ _ _ _ _ _ HT1 HF).
Qed.

Definition carryWZK (bc : bctx) (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryWZ bc log kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma carryWZK_eq : forall log kn hints,
  carryWZK (mkbc (facts_of kn)) log kn hints = carry log kn hints.
Proof.
  intros log kn hints. rewrite <- carryWK_eq. unfold carryWZK, carryWK.
  destruct log as [|s older]; [reflexivity|]. destruct hints as [|h hs]; [|reflexivity].
  rewrite carryWZ_eq. reflexivity.
Qed.

End AX2W.

Module AX2F.
Import AX2. Import AX2B.

(* [comment removed for export] *)
Definition mk_lprep (bc : bctx) (b1 : expr) (k1 : Z) (n1 : nat) : sprep :=
  SPrep (base_rangeB bc b1) None (disj_sidesB bc (bc_fk bc) b1 k1 (zlit64 (Z.of_nat n1))) [].

Lemma zlit64_nat8F : forall w, Nat.leb w 8 = true -> zlit64 (Z.of_nat w) = Z.of_nat w.
Proof.
  intros w H. apply Nat.leb_le in H. unfold zlit64, two64.
  replace (Z.leb 0 (Z.of_nat w) && Z.ltb (Z.of_nat w) (2 ^ 64))%bool with true; [reflexivity|].
  symmetry. apply andb_true_intro. split; [apply Z.leb_le; lia|apply Z.ltb_lt; lia].
Qed.

Lemma lprep_apart : forall fk b1 k1 n1 b2 k2 n2, Nat.leb n1 8 = true -> Nat.leb n2 8 = true ->
  ranges_apart_pB (mkbc fk) (mk_lprep (mkbc fk) b1 k1 n1) b1 k1 (elen n1) b2 k2 (elen n2)
  = ranges_apartB (mkbc fk) b1 k1 (Z.of_nat n1) b2 k2 (Z.of_nat n2).
Proof.
  intros fk b1 k1 n1 b2 k2 n2 H1 H2.
  transitivity (ranges_apart_pB (mkbc fk) (mk_sprepB (mkbc fk) b1 k1 (elen n1)) b1 k1 (elen n1) b2 k2 (elen n2)).
  { unfold ranges_apart_pB, mk_lprep, mk_sprepB, elen. cbn [sp_rng sp_D]. reflexivity. }
  autorewrite with bceq. rewrite AX2S.ranges_apart_p_eq. unfold ranges_apart_x, elen.
  rewrite !zlit64_nat8F by assumption. reflexivity.
Qed.

Fixpoint log_lookupP (bc : bctx) (sp : sprep) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupP bc sp rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          if (if Nat.leb w 8 then ranges_apart_pB bc sp rb rk (elen n) kb kk (elen w)
              else ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w))
          then log_lookupP bc sp rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupP bc sp rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.

Lemma log_lookupP_eq : forall fk log rb rk n sx hints acc, Nat.leb n 8 = true ->
  log_lookupP (mkbc fk) (mk_lprep (mkbc fk) rb rk n) log rb rk n sx hints acc
  = log_lookupB (mkbc fk) log rb rk n sx hints acc.
Proof.
  intros fk log rb rk n sx. induction log as [|[[kb kk] w v] rest IH]; intros hints acc Hn; [reflexivity|].
  cbn [log_lookupP log_lookupB].
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity.
  - apply IH. exact Hn.
  - destruct (Nat.leb w 8) eqn:Hw; [rewrite (lprep_apart fk rb rk n kb kk w Hn Hw)|];
      (destruct (ranges_apartB (mkbc fk) rb rk (Z.of_nat n) kb kk (Z.of_nat w)); [apply IH; exact Hn|]);
      destruct hints as [|[|] hs]; try reflexivity; apply IH; exact Hn.
Qed.

Definition sym_readBIP (segs : list Segment) (ss : sym_state) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match (if Nat.leb n 8
         then log_lookupP bc (mk_lprep bc (a_base a) (a_off a) n) (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) []
         else log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) []) with
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

Lemma sym_readBIP_eqf : forall fk segs ss, sym_readBIP segs ss (mkbc fk) = sym_readBI segs ss (mkbc fk).
Proof.
  intros fk segs ss. bcfe. unfold sym_readBIP, sym_readBI.
  match goal with |- context [Nat.leb ?n 8] => destruct (Nat.leb n 8) eqn:Hn end; [|reflexivity].
  rewrite log_lookupP_eq by exact Hn. reflexivity.
Qed.

Definition sym_stepBIP (bc : bctx) (kx : kix) (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
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
      match sym_readBIP segs ss bc kx scr a n sx' with
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
              (flat_scB bc a n ++ storeok_scB bc a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readBIP segs ss bc kx scr a n (amo_sx wd) with
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
                  (flat_scB bc a n ++ storeok_scB bc a n) scr
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
                match sym_readBIP segs ss bc kx scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.

Lemma sym_stepBIP_eq : forall fk kx segs i ss scr,
  sym_stepBIP (mkbc fk) kx segs i ss scr = sym_stepBI (mkbc fk) kx segs i ss scr.
Proof. intros. unfold sym_stepBIP, sym_stepBI. rewrite sym_readBIP_eqf. reflexivity. Qed.



(* [comment removed for export] *)
Record lgx := LGX { lx_nt : ntab; lx_hull : ptree (Z * Z) }.
Definition lgx0 : lgx := LGX nt_empty PTLeaf.
Definition hull_ext (h : ptree (Z * Z)) (id : positive) (lo hi : Z) : ptree (Z * Z) :=
  pt_set id (match pt_get h id with Some (l, hh) => (Z.min l lo, Z.max hh hi) | None => (lo, hi) end) h.
Definition lx_push (bc : bctx) (x : lgx) (e : sentry) : positive * lgx :=
  let '(r, nt') := intern bc (lx_nt x) (a_base (e_addr e)) in
  let '(id, _) := r in
  (id, LGX nt' (hull_ext (lx_hull x) id (a_off (e_addr e)) (a_off (e_addr e) + zlit64 (Z.of_nat (e_width e))))).
Fixpoint lx_of_log (bc : bctx) (log : list sentry) : lgx * list positive :=
  match log with
  | [] => (lgx0, [])
  | e :: rest => let '(x, ids) := lx_of_log bc rest in let '(id, x') := lx_push bc x e in (x', id :: ids)
  end.

Definition gnum (sp : sprep) (br2 : option (Z * Z)) (rk m1 glo ghi : Z) : bool :=
  match sp_rng sp, br2 with
  | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + rk + m1 - lo2) glo || Z.leb ghi (lo1 + rk - hi2))%bool
  | _, _ => false
  end.
Definition gverdict (bc : bctx) (sp : sprep) (x : lgx) (rk m1 : Z) (id : positive) : bool :=
  match pt_get (nt_info (lx_nt x)) id, pt_get (lx_hull x) id with
  | Some bi, Some (glo, ghi) => if gnum sp (bi_br bi) rk m1 glo ghi then true else AX2W.dsyn bc (sp_D sp) (bi_base bi) glo ghi
  | _, _ => false
  end.

Fixpoint log_lookupG (bc : bctx) (sp : sprep) (x : lgx) (memo : ptree bool) (log : list sentry) (ids : list positive)
         (rb : expr) (rk : Z) (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match log, ids with
  | [], _ => LMiss acc hints
  | _ :: _, [] => log_lookupP bc sp log rb rk n sx hints acc
  | SE (SA kb kk) w v :: rest, id :: ids' =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupG bc sp x memo rest ids' rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          let '(gv, memo') := match pt_get memo id with
                              | Some b => (b, memo)
                              | None => let b := gverdict bc sp x rk (zlit64 (Z.of_nat n)) id in (b, pt_set id b memo)
                              end in
          if (Nat.leb w 8 && gv)%bool then log_lookupG bc sp x memo' rest ids' rb rk n sx hints acc else
          if (if Nat.leb w 8 then ranges_apart_pB bc sp rb rk (elen n) kb kk (elen w)
              else ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w))
          then log_lookupG bc sp x memo' rest ids' rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupG bc sp x memo' rest ids' rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.

Definition hull_has (h : ptree (Z * Z)) (id : positive) (lo hi : Z) : Prop :=
  exists glo ghi, pt_get h id = Some (glo, ghi) /\ (glo <= lo)%Z /\ (hi <= ghi)%Z.
Definition LXI (bc : bctx) (x : lgx) (log : list sentry) (ids : list positive) : Prop :=
  NTI bc (lx_nt x) /\
  Forall2 (fun e id => In (a_base (e_addr e), id) (nt_bucket (lx_nt x) (bkey (a_base (e_addr e))))
                       /\ hull_has (lx_hull x) id (a_off (e_addr e)) (a_off (e_addr e) + zlit64 (Z.of_nat (e_width e)))) log ids.

Lemma hull_ext_has : forall h id lo hi id' lo' hi',
  hull_has h id' lo' hi' -> hull_has (hull_ext h id lo hi) id' lo' hi'.
Proof.
  intros h id lo hi id' lo' hi' (glo & ghi & Hg & H1 & H2). unfold hull_has, hull_ext.
  destruct (Pos.eq_dec id' id) as [->|Hne].
  - rewrite pt_gss, Hg. exists (Z.min glo lo), (Z.max ghi hi). split; [reflexivity|lia].
  - rewrite (pt_gso _ id' id _ h Hne). exists glo, ghi. auto.
Qed.
Lemma hull_ext_new : forall h id lo hi, (lo <= hi)%Z -> hull_has (hull_ext h id lo hi) id lo hi.
Proof.
  intros h id lo hi Hle. unfold hull_has, hull_ext. rewrite pt_gss.
  destruct (pt_get h id) as [[l hh]|]; [exists (Z.min l lo), (Z.max hh hi) | exists lo, hi]; split; try reflexivity; lia.
Qed.

Lemma zlit64_nonneg : forall z, (0 <= zlit64 z)%Z.
Proof.
  intros z. unfold zlit64, two64. destruct (Z.leb 0 z && Z.ltb z (2 ^ 64))%bool eqn:E.
  - apply andb_prop in E as [E _]. apply Z.leb_le in E. exact E.
  - apply Z.mod_pos_bound. lia.
Qed.

Lemma lx_push_ok : forall bc x log ids e id x',
  LXI bc x log ids -> lx_push bc x e = (id, x') -> LXI bc x' (e :: log) (id :: ids).
Proof.
  intros bc x log ids e id x' [HT HF] H. unfold lx_push in H.
  destruct (intern bc (lx_nt x) (a_base (e_addr e))) as [[id0 bi] nt'] eqn:EI. injection H as <- <-.
  destruct (intern_ok _ _ _ _ _ _ HT EI) as (HT' & _ & HIn & Hm). split; [exact HT'|].
  constructor.
  - split; [exact HIn|]. apply hull_ext_new. pose proof (zlit64_nonneg (Z.of_nat (e_width e))). lia.
  - eapply Forall2_impl; [|exact HF]. intros e' id' [H1 H2]. split; [apply Hm; exact H1|]. apply hull_ext_has. exact H2.
Qed.

Lemma lx_of_log_ok : forall bc log, let '(x, ids) := lx_of_log bc log in LXI bc x log ids.
Proof.
  intros bc log. induction log as [|e rest IH]; cbn [lx_of_log].
  - split; [apply NTI_empty|constructor].
  - destruct (lx_of_log bc rest) as [x ids]. destruct (lx_push bc x e) as [id x'] eqn:E.
    exact (lx_push_ok _ _ _ _ _ _ _ IH E).
Qed.

(* [comment removed for export] *)
Lemma gverdict_apart : forall fk x kb kk w id rb rk n,
  NTI (mkbc fk) (lx_nt x) -> In (kb, id) (nt_bucket (lx_nt x) (bkey kb)) ->
  hull_has (lx_hull x) id kk (kk + zlit64 (Z.of_nat w))%Z -> Nat.leb w 8 = true -> Nat.leb n 8 = true ->
  gverdict (mkbc fk) (mk_lprep (mkbc fk) rb rk n) x rk (zlit64 (Z.of_nat n)) id = true ->
  ranges_apart_pB (mkbc fk) (mk_lprep (mkbc fk) rb rk n) rb rk (elen n) kb kk (elen w) = true.
Proof.
  intros fk x kb kk w id rb rk n [HA _] HIn (glo & ghi & Hh & H1 & H2) Hw Hn Hv.
  destruct (HA _ _ _ HIn) as (_ & Hinfo & _).
  unfold gverdict in Hv. rewrite Hinfo, Hh in Hv. cbn [bi_br bi_base] in Hv.
  rewrite (AX2W.zlit64_nat8 w Hw) in H2.
  unfold ranges_apart_pB, elen. cbv zeta.
  destruct (gnum (mk_lprep (mkbc fk) rb rk n) (base_rangeB (mkbc fk) kb) rk (zlit64 (Z.of_nat n)) glo ghi) eqn:Hg.
  - unfold gnum in Hg.
    destruct (sp_rng (mk_lprep (mkbc fk) rb rk n)) as [[lo1 hi1]|]; [|discriminate].
    destruct (base_rangeB (mkbc fk) kb) as [[lo2 hi2]|]; [|discriminate].
    rewrite (AX2W.zlit64_nat8 w Hw).
    replace ((hi1 + rk + zlit64 (Z.of_nat n) <=? lo2 + kk)%Z || (hi2 + kk + Z.of_nat w <=? lo1 + rk)%Z)%bool with true; [reflexivity|].
    symmetry. apply Bool.orb_true_iff in Hg as [Hg|Hg]; apply Z.leb_le in Hg; apply Bool.orb_true_iff;
      [left|right]; apply Z.leb_le; lia.
  - pose proof (AX2W.dsyn_in_sides _ _ _ glo ghi kk (Z.of_nat w) Hv H1 H2) as HS.
    rewrite (AX2W.zlit64_nat8 w Hw), HS.
    match goal with |- (if ?c then true else true) = true => destruct c; reflexivity end.
Qed.

Definition MEMOG (bc : bctx) (sp : sprep) (x : lgx) (rk m1 : Z) (memo : ptree bool) : Prop :=
  forall id b, pt_get memo id = Some b -> b = gverdict bc sp x rk m1 id.

Lemma log_lookupG_eq : forall fk x log ids memo rb rk n sx hints acc,
  Nat.leb n 8 = true -> LXI (mkbc fk) x log ids ->
  MEMOG (mkbc fk) (mk_lprep (mkbc fk) rb rk n) x rk (zlit64 (Z.of_nat n)) memo ->
  log_lookupG (mkbc fk) (mk_lprep (mkbc fk) rb rk n) x memo log ids rb rk n sx hints acc
  = log_lookupP (mkbc fk) (mk_lprep (mkbc fk) rb rk n) log rb rk n sx hints acc.
Proof.
  intros fk x log. induction log as [|[[kb kk] w v] rest IH]; intros ids memo rb rk n sx hints acc Hn [HT HF] HM;
    [reflexivity|].
  inversion HF as [|e0 id l0 ids' [HIn Hh] HF' E1 E2]; subst.
  cbn [log_lookupG log_lookupP].
  assert (HL : LXI (mkbc fk) x rest ids') by (split; assumption).
  destruct (rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w)); try reflexivity; [apply IH; assumption|].
  set (gv0 := gverdict (mkbc fk) (mk_lprep (mkbc fk) rb rk n) x rk (zlit64 (Z.of_nat n)) id).
  assert (HGM : exists memo', (match pt_get memo id with Some b => (b, memo) | None => (gv0, pt_set id gv0 memo) end) = (gv0, memo')
                 /\ MEMOG (mkbc fk) (mk_lprep (mkbc fk) rb rk n) x rk (zlit64 (Z.of_nat n)) memo').
  { destruct (pt_get memo id) as [b|] eqn:Eb.
    - exists memo. rewrite (HM _ _ Eb). split; [reflexivity|exact HM].
    - exists (pt_set id gv0 memo). split; [reflexivity|].
      intros id' b' Hb'. destruct (Pos.eq_dec id' id) as [->|Hne].
      + rewrite pt_gss in Hb'. injection Hb' as <-. reflexivity.
      + rewrite (pt_gso _ id' id _ memo Hne) in Hb'. exact (HM _ _ Hb'). }
  destruct HGM as (memo' & Egm & HM'). rewrite Egm. cbv beta iota.
  destruct (Nat.leb w 8) eqn:Hw; cbn [andb].
  - destruct gv0 eqn:Hgv.
    + rewrite (gverdict_apart fk x kb kk w id rb rk n HT HIn Hh Hw Hn Hgv). apply IH; assumption.
    + destruct (ranges_apart_pB _ _ _ _ _ _ _ _); [apply IH; assumption|].
      destruct hints as [|[|] hs]; try reflexivity; apply IH; assumption.
  - destruct (ranges_apartB _ _ _ _ _ _ _); [apply IH; assumption|].
    destruct hints as [|[|] hs]; try reflexivity; apply IH; assumption.
Qed.

Definition sym_readBIG (segs : list Segment) (ss : sym_state) (x : lgx) (ids : list positive) (bc : bctx) (kx : kix) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match (if Nat.leb n 8
         then log_lookupG bc (mk_lprep bc (a_base a) (a_off a) n) x PTLeaf (s_log ss) ids (a_base a) (a_off a) n sx' (sc_hints scr) []
         else log_lookupB bc (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) []) with
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


Lemma sym_readBIG_eq : forall fk segs ss x ids kx scr, LXI (mkbc fk) x (s_log ss) ids ->
  sym_readBIG segs ss x ids (mkbc fk) kx scr = sym_readBIP segs ss (mkbc fk) kx scr.
Proof.
  intros fk segs ss x ids kx scr HL. apply functional_extensionality. intros a.
  apply functional_extensionality. intros n. apply functional_extensionality. intros sx'.
  unfold sym_readBIG, sym_readBIP. destruct (Nat.leb n 8) eqn:Hn; [|reflexivity].
  rewrite (log_lookupG_eq fk x (s_log ss) ids PTLeaf (a_base a) (a_off a) n sx' (sc_hints scr) [] Hn HL); [reflexivity|].
  intros id b H. rewrite pt_get_leaf in H. discriminate.
Qed.

Definition sym_stepBIG (bc : bctx) (kx : kix) (segs : list Segment) (i : instr) (ss : sym_state) (x : lgx) (ids : list positive) (scr : scripts) : stepres :=
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
      match sym_readBIG segs ss x ids bc kx scr a n sx' with
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
              (flat_scB bc a n ++ storeok_scB bc a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedbB bc e wd then
        let a := to_saddrKB bc e 0 in
        match sym_readBIG segs ss x ids bc kx scr a n (amo_sx wd) with
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
                  (flat_scB bc a n ++ storeok_scB bc a n) scr
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
                match sym_readBIG segs ss x ids bc kx scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newvalB bc wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_scB bc a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.


Lemma sym_stepBIG_eq : forall fk kx segs i ss x ids scr, LXI (mkbc fk) x (s_log ss) ids ->
  sym_stepBIG (mkbc fk) kx segs i ss x ids scr = sym_stepBIP (mkbc fk) kx segs i ss scr.
Proof.
  intros fk kx segs i ss x ids scr HL. unfold sym_stepBIG, sym_stepBIP.
  rewrite (sym_readBIG_eq fk segs ss x ids kx scr HL). reflexivity.
Qed.

Definition is_storeI (i : instr) : bool :=
  match i with Store _ _ _ _ | Sc _ _ _ _ _ _ | Amo _ _ _ _ _ _ _ => true | _ => false end.

(* [comment removed for export] *)
Lemma sym_stepBIP_log : forall bc kx segs i ss scr ss' scs scr',
  sym_stepBIP bc kx segs i ss scr = SOk ss' scs scr' ->
  if is_storeI i then exists e, s_log ss' = e :: s_log ss else s_log ss' = s_log ss.
Proof.
  intros bc kx segs i ss scr ss' scs scr' H.
  destruct i; cbn [is_storeI]; unfold sym_stepBIP in H; unfold sset, sjump in H;
    repeat match type of H with
           | context [match ?c with _ => _ end] => destruct c; try discriminate H
           | context [if ?c then _ else _] => destruct c; try discriminate H
           end;
    try discriminate H; injection H as <- <- <-; cbn [s_log]; eauto.
Qed.

Definition lx_step (bc : bctx) (i : instr) (r : stepres) (x : lgx) (ids : list positive) : lgx * list positive :=
  if is_storeI i then
    match r with
    | SOk ss' _ _ => match s_log ss' with e :: _ => let '(id, x') := lx_push bc x e in (x', id :: ids) | [] => (x, ids) end
    | SStop => (x, ids)
    end
  else (x, ids).

Lemma lx_step_ok : forall bc kx segs i ss scr ss' scs scr' x ids,
  LXI bc x (s_log ss) ids -> sym_stepBIP bc kx segs i ss scr = SOk ss' scs scr' ->
  let '(x', ids') := lx_step bc i (SOk ss' scs scr') x ids in LXI bc x' (s_log ss') ids'.
Proof.
  intros bc kx segs i ss scr ss' scs scr' x ids HL H.
  pose proof (sym_stepBIP_log _ _ _ _ _ _ _ _ _ H) as HG. unfold lx_step.
  destruct (is_storeI i).
  - destruct HG as (e & He). rewrite He.
    destruct (lx_push bc x e) as [id x'] eqn:Ep. exact (lx_push_ok _ _ _ _ _ _ _ HL Ep).
  - rewrite HG. exact HL.
Qed.

Section WithSegs.
Variable segs : list Segment.

Fixpoint sym_execF_go (bc : bctx) (kx : kix) (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
                  (ss : sym_state) (acc : list sidecond)
                  (ck : sym_state * list sidecond * scripts)
  : sym_state * list sidecond * scripts :=
  match fuel with
  | O => if s_clean ss then (ss, acc, scr) else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then (ss, acc, scr) else ck) else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then (ss, acc, scr) else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then (ss, acc, scr) else ck) else
          match decode_any w with
          | None => if s_clean ss then (ss, acc, scr) else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then (ss, acc, scr) else ck) else
              match sym_stepBIP bc kx segs i ss scr with
              | SOk ss' scs scr' =>
                  let acc' := sc_add scs acc in
                  sym_execF_go bc kx f false stops scr' ss' acc'
                    (if s_clean ss' then (ss', acc', scr') else ck)
              | SStop => if s_clean ss then (ss, acc, scr) else ck
              end
          end
      end
  end.

(* [comment removed for export] *)
Definition sym_execF (kn : list kentry) (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
           (ss : sym_state) (acc : list sidecond) : sym_state * list sidecond * scripts :=
  sym_execF_go (mkbc (facts_of kn)) (mk_kix kn) fuel first stops scr (clr ss) acc (clr ss, acc, scr).

#[using="Type"] Lemma sym_execF_go_eq : forall fuel kn first stops scr ss acc ck,
  s_know ss = kn ->
  sym_execF_go (mkbc (facts_of kn)) (mk_kix kn) fuel first stops scr ss acc ck
  = sym_exec_go segs fuel first stops scr ss acc ck.
Proof.
  intros fuel. induction fuel as [|f IH]; intros kn first stops scr ss acc ck Hk;
    cbn [sym_execF_go sym_exec_go]; [reflexivity|].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|reflexivity].
  destruct (is_ecall w); [reflexivity|].
  destruct (decode_any w) as [[i sz]|]; [|reflexivity].
  destruct (negb (Z.eqb sz 4)); [reflexivity|].
  subst kn. rewrite sym_stepBIP_eq, sym_stepBI_eq, sym_stepB_eq.
  destruct (sym_step segs i ss scr) as [ss' scs scr'|] eqn:Hs; [|reflexivity].
  apply IH. exact (sym_step_know segs i ss scr ss' scs scr' Hs).
Qed.

#[using="Type"] Lemma sym_execF_eq : forall kn fuel first stops scr ss acc,
  s_know ss = kn ->
  sym_execF kn fuel first stops scr ss acc = sym_exec segs fuel first stops scr ss acc.
Proof.
  intros kn fuel first stops scr ss acc Hk. unfold sym_execF, sym_exec.
  apply sym_execF_go_eq. exact Hk.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sym_exec_viaF : forall kn fuel first stops scr ss acc r,
  s_know ss = kn ->
  sym_execF kn fuel first stops scr ss acc = r ->
  sym_exec segs fuel first stops scr ss acc = r.
Proof. intros kn fuel first stops scr ss acc r Hk H. rewrite <- (sym_execF_eq kn) by exact Hk. exact H. Qed.


(* [comment removed for export] *)
Fixpoint mk_itab_rs (rs : list (Z * nat)) (t : itab) : itab :=
  match rs with
  | [] => t
  | (lo, n) :: r => mk_itab_rs r (mk_itab_fuel segs n lo t)
  end.
#[using="Type"] Lemma mk_itab_rs_sound : forall rs t, itab_sound segs t -> itab_sound segs (mk_itab_rs rs t).
Proof.
  intros rs. induction rs as [|[lo n] r IH]; intros t Ht; cbn [mk_itab_rs]; [exact Ht|].
  apply IH. apply mk_itab_fuel_sound. exact Ht.
Qed.
#[using="Type"] Lemma itab_leaf_sound : itab_sound segs PTLeaf.
Proof. intros pc i. unfold itab_lookup. destruct pc; try discriminate. rewrite pt_get_leaf. discriminate. Qed.

Fixpoint sym_execFT_go (t : itab) (bc : bctx) (kx : kix) (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
                  (ss : sym_state) (acc : list sidecond)
                  (ck : sym_state * list sidecond * scripts)
  : sym_state * list sidecond * scripts :=
  match fuel with
  | O => if s_clean ss then (ss, acc, scr) else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then (ss, acc, scr) else ck) else
      match itab_lookup t (s_pc ss) with
      | Some i =>
          match sym_stepBIP bc kx segs i ss scr with
          | SOk ss' scs scr' =>
              let acc' := sc_add scs acc in
              sym_execFT_go t bc kx f false stops scr' ss' acc'
                (if s_clean ss' then (ss', acc', scr') else ck)
          | SStop => if s_clean ss then (ss, acc, scr) else ck
          end
      | None =>
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then (ss, acc, scr) else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then (ss, acc, scr) else ck) else
          match decode_any w with
          | None => if s_clean ss then (ss, acc, scr) else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then (ss, acc, scr) else ck) else
              match sym_stepBIP bc kx segs i ss scr with
              | SOk ss' scs scr' =>
                  let acc' := sc_add scs acc in
                  sym_execFT_go t bc kx f false stops scr' ss' acc'
                    (if s_clean ss' then (ss', acc', scr') else ck)
              | SStop => if s_clean ss then (ss, acc, scr) else ck
              end
          end
      end
      end
  end.

Fixpoint sym_execFG_go (t : itab) (bc : bctx) (kx : kix) (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
                  (ss : sym_state) (x : lgx) (ids : list positive) (acc : list sidecond)
                  (ck : sym_state * list sidecond * scripts)
  : sym_state * list sidecond * scripts :=
  match fuel with
  | O => if s_clean ss then (ss, acc, scr) else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then (ss, acc, scr) else ck) else
      match itab_lookup t (s_pc ss) with
      | Some i =>
          match sym_stepBIG bc kx segs i ss x ids scr with
          | SOk ss' scs scr' =>
              let acc' := sc_add scs acc in
              let '(x', ids') := lx_step bc i (SOk ss' scs scr') x ids in
              sym_execFG_go t bc kx f false stops scr' ss' x' ids' acc'
                (if s_clean ss' then (ss', acc', scr') else ck)
          | SStop => if s_clean ss then (ss, acc, scr) else ck
          end
      | None =>
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => if s_clean ss then (ss, acc, scr) else ck
      | Some w =>
          if is_ecall w then (if s_clean ss then (ss, acc, scr) else ck) else
          match decode_any w with
          | None => if s_clean ss then (ss, acc, scr) else ck
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (if s_clean ss then (ss, acc, scr) else ck) else
              match sym_stepBIG bc kx segs i ss x ids scr with
              | SOk ss' scs scr' =>
                  let acc' := sc_add scs acc in
                  let '(x', ids') := lx_step bc i (SOk ss' scs scr') x ids in
                  sym_execFG_go t bc kx f false stops scr' ss' x' ids' acc'
                    (if s_clean ss' then (ss', acc', scr') else ck)
              | SStop => if s_clean ss then (ss, acc, scr) else ck
              end
          end
      end
      end
  end.


#[using="Type"] Lemma sym_execFG_go_eq : forall t kx fuel fk first stops scr ss x ids acc ck, LXI (mkbc fk) x (s_log ss) ids ->
  sym_execFG_go t (mkbc fk) kx fuel first stops scr ss x ids acc ck = sym_execFT_go t (mkbc fk) kx fuel first stops scr ss acc ck.
Proof.
  intros t kx fuel. induction fuel as [|f IH]; intros fk first stops scr ss x ids acc ck HL;
    cbn [sym_execFG_go sym_execFT_go]; [reflexivity|].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|].
  - rewrite (sym_stepBIG_eq fk kx segs i ss x ids scr HL).
    destruct (sym_stepBIP (mkbc fk) kx segs i ss scr) as [ss' scs scr'|] eqn:Hs; [|reflexivity].
    pose proof (lx_step_ok _ _ _ _ _ _ _ _ _ x ids HL Hs) as HL'.
    destruct (lx_step (mkbc fk) i (SOk ss' scs scr') x ids) as [x' ids']. apply IH. exact HL'.
  - destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|reflexivity].
    destruct (is_ecall w); [reflexivity|].
    destruct (decode_any w) as [[i sz]|]; [|reflexivity].
    destruct (negb (Z.eqb sz 4)); [reflexivity|].
    rewrite (sym_stepBIG_eq fk kx segs i ss x ids scr HL).
    destruct (sym_stepBIP (mkbc fk) kx segs i ss scr) as [ss' scs scr'|] eqn:Hs; [|reflexivity].
    pose proof (lx_step_ok _ _ _ _ _ _ _ _ _ x ids HL Hs) as HL'.
    destruct (lx_step (mkbc fk) i (SOk ss' scs scr') x ids) as [x' ids']. apply IH. exact HL'.
Qed.

(* [comment removed for export] *)
Definition sym_execFT (t : itab) (kn : list kentry) (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
           (ss : sym_state) (acc : list sidecond) : sym_state * list sidecond * scripts :=
  let bc := mkbc (facts_of kn) in
  let '(x, ids) := lx_of_log bc (s_log (clr ss)) in
  sym_execFG_go t bc (mk_kix kn) fuel first stops scr (clr ss) x ids acc (clr ss, acc, scr).

#[using="Type"] Lemma sym_execFT_go_eq : forall t, itab_sound segs t -> forall fuel kn first stops scr ss acc ck,
  s_know ss = kn ->
  sym_execFT_go t (mkbc (facts_of kn)) (mk_kix kn) fuel first stops scr ss acc ck
  = sym_exec_go segs fuel first stops scr ss acc ck.
Proof.
  intros t Ht fuel. induction fuel as [|f IH]; intros kn first stops scr ss acc ck Hk;
    cbn [sym_execFT_go sym_exec_go]; [reflexivity|].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (itab_lookup t (s_pc ss)) as [i|] eqn:Hl.
  - pose proof (Ht _ _ Hl) as He. unfold itab_entry in He.
    destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|discriminate].
    destruct (is_ecall w); [discriminate|].
    destruct (decode_any w) as [[i' sz]|]; [|discriminate].
    destruct (Z.eqb sz 4) eqn:Esz; [|discriminate]. injection He as ->. cbn [negb].
    subst kn. rewrite sym_stepBIP_eq, sym_stepBI_eq, sym_stepB_eq.
    destruct (sym_step segs i ss scr) as [ss' scs scr'|] eqn:Hs; [|reflexivity].
    apply IH. exact (sym_step_know segs i ss scr ss' scs scr' Hs).
  - destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|reflexivity].
    destruct (is_ecall w); [reflexivity|].
    destruct (decode_any w) as [[i sz]|]; [|reflexivity].
    destruct (negb (Z.eqb sz 4)); [reflexivity|].
    subst kn. rewrite sym_stepBIP_eq, sym_stepBI_eq, sym_stepB_eq.
    destruct (sym_step segs i ss scr) as [ss' scs scr'|] eqn:Hs; [|reflexivity].
    apply IH. exact (sym_step_know segs i ss scr ss' scs scr' Hs).
Qed.

#[using="Type"] Lemma sym_exec_viaFT : forall t kn fuel first stops scr ss acc r,
  itab_sound segs t -> s_know ss = kn ->
  sym_execFT t kn fuel first stops scr ss acc = r ->
  sym_exec segs fuel first stops scr ss acc = r.
Proof.
  intros t kn fuel first stops scr ss acc r Ht Hk H. rewrite <- H. unfold sym_execFT, sym_exec.
  pose proof (lx_of_log_ok (mkbc (facts_of kn)) (s_log (clr ss))) as HL.
  destruct (lx_of_log (mkbc (facts_of kn)) (s_log (clr ss))) as [x ids].
  rewrite (sym_execFG_go_eq t (mk_kix kn) fuel (facts_of kn) first stops scr (clr ss) x ids acc (clr ss, acc, scr) HL).
  symmetry. apply (sym_execFT_go_eq t Ht). exact Hk.
Qed.

End WithSegs.

(* [comment removed for export] *)
Definition carryF (log : list sentry) (kn : list kentry) (hints : list bool) : list kentry * list sidecond * list bool :=
  AX2W.carryWZK (mkbc (facts_of kn)) log kn hints.
Lemma carryF_eq : forall log kn hints, carryF log kn hints = carry log kn hints.
Proof. intros. unfold carryF. apply AX2W.carryWZK_eq. Qed.
Lemma carry_viaF : forall log kn hints r, carryF log kn hints = r -> carry log kn hints = r.
Proof. intros log kn hints r H. rewrite <- carryF_eq. exact H. Qed.

End AX2F.
