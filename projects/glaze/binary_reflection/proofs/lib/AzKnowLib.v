(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.AzSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.AzPlan OSSVerify.Proofs.glaze.binary_reflection.lib.AzAPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzGPS OSSVerify.Proofs.glaze.binary_reflection.lib.AzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition in_lshadow (L : list (Z * Z)) (z : Z) : Prop := exists b n, In (b, n) L /\ in_shadow SB b n z.
(* [comment removed for export] *)
Definition in_sshadow {RC : run_ceil} (z : Z) : Prop := SB + CEIL_run / 8 <= z < HEAPLO.
Lemma in_lshadow_app : forall L1 L2 z, in_lshadow (L1 ++ L2) z <-> in_lshadow L1 z \/ in_lshadow L2 z.
Proof.
  intros L1 L2 z. unfold in_lshadow. split.
  - intros (b & n & Hin & Hz). apply in_app_iff in Hin as [Hin|Hin]; [left|right]; exists b, n; split; assumption.
  - intros [(b & n & Hin & Hz)|(b & n & Hin & Hz)]; exists b, n; split; try assumption; apply in_app_iff; [left|right]; assumption.
Qed.
Lemma in_lshadow_mono : forall L L' z, (forall x, In x L -> In x L') -> in_lshadow L z -> in_lshadow L' z.
Proof. intros L L' z Hs (b & n & Hin & Hz). exists b, n. split; [apply Hs; exact Hin | exact Hz]. Qed.

Section KnowLib.
Variable SEGS : list Segment.
Context {RC : run_ceil}.   (* [comment removed for export] *)
Context {SFL : stk_floor}.   (* [comment removed for export] *)
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable G : gtable.

#[local] Notation owned := (GPS.owned SWIN PERMc SPTOPc).

(* [comment removed for export] *)
Definition in_ishadow (z : Z) : Prop := SB + g_ro_lo G / 8 <= z < SB + (g_img_hi G + 7) / 8.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shz (E : env) (objs : list (expr * expr)) (top : Z) (z : Z) : Prop :=
  in_lshadow (blocks_den E objs) z \/ in_sshadow z \/ in_ishadow z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition in_kfoot (E : env) (K : kentry) (x : Z) : Prop :=
  match kfoot E K with Some (s, l) => s <= x < s + l | None => False end.

Lemma kentry_ok_footprint : forall E M M' K,
  kentry_ok SEGS E M K ->
  (forall x : word, in_kfoot E K (bv_unsigned x) -> M' x = M x) ->
  kentry_ok SEGS E M' K.
Proof.
  intros E M M' K HK Hout.
  assert (RD : forall (a : word) k, (bv_unsigned a + Z.of_nat k <= 2 ^ 64)%Z ->
     (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat k -> M' x = M x) ->
     rdn SEGS M' a k = rdn SEGS M a k).
  { intros a k Hnw Hd. apply rdn_ext; [exact Hnw|]. intros x Hx. apply Hd. lia. }
  unfold in_kfoot, kfoot in Hout.
  destruct K as [[b k] w v|[b k] nn|[b k] nn kb|ilo ihi|e m|e rlo rhi|[b k] nn|a1 n1 a2 n2|[b k] nn fc|[b k] nn | [b k] nn | fv flo fd]; cbn [kentry_ok] in *;
    try exact HK.
  8: { (* [comment removed for export] *)
       destruct HK as (Hfl & H47 & Hz). split; [exact Hfl|]. split; [exact H47|]. intros z Hzz.
       destruct Hfl as (F1 & F2 & F3 & F4).
       destruct (Hz z Hzz) as (bt & Hbt & Hv). exists bt. split; [|exact Hv].
       rewrite Hout; [exact Hbt|]. unfold SB in *.
       assert (D1 : (estart E (SA b k) / 8 <= z / 8)%Z) by (apply Z.div_le_mono; lia).
       assert (D2 : (z / 8 <= (estart E (SA b k) + elenZ E nn - 1) / 8)%Z) by (apply Z.div_le_mono; lia).
       assert (D3 : (0 <= estart E (SA b k) / 8)%Z) by (apply Z.div_pos; lia).
       assert (D4 : ((estart E (SA b k) + elenZ E nn - 1) / 8 < 2 ^ 44)%Z) by (apply Z.div_lt_upper_bound; lia).
       rewrite u64_lit by lia. lia. }
  7: { destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
       rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
  6: { destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
       rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia. }
  - destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite RD; [exact Hrd | rewrite (flat_u E _ _ Hfl); destruct Hfl; lia |].
    intros x Hx. apply Hout. rewrite (flat_u E _ _ Hfl) in Hx. lia.
  - destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi. destruct Hfl as (F1 & F2 & F3 & F4).
    rewrite Hout; [apply Hz; exact Hi|]. rewrite u64_lit by lia. lia.
  - destruct HK as (HA & HB & HC). split; [exact HA|]. split; [exact HB|]. intros i Hi.
    rewrite Hout; [apply HC; lia|]. rewrite u64_lit by lia. lia.
  - destruct HK as [Hfl Hs]. split; [exact Hfl|]. intros d m Hd0 Hdm.
    pose proof (Hs d m Hd0 Hdm) as H. destruct Hfl as (F1 & F2 & F3 & F4).
    destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|].
    intros x Hx. rewrite u64_lit in Hx by lia.
    unfold wview. rewrite Hout by lia. fold (wview SEGS M x).
    eapply (store_ok_all SEGS M (Datatypes.S m')); [| exact H |]; rewrite u64_lit by lia; lia.
  - (* [comment removed for export] *)
    destruct HK as [HK HR]. split; [|exact HR].
    destruct (kfpc_cases _ _ _ _ HK) as [ANY | (T & FR & LT)]; [apply ANY|]. rewrite T in Hout.
    apply (AX2S.fpc_kept M M'); [exact HK|]. intros a Ha. unfold AX2S.FPC_HI in *.
    pose proof (u64_range (edenot E flo)). apply Hout. rewrite u64_lit by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_add_off : forall (x : word) (off : Z),
  0 <= bv_unsigned x + off < 2 ^ 64 ->
  bv_unsigned (Z_to_bv 64 (bv_unsigned x + bv_unsigned (Z_to_bv 64 off))) = bv_unsigned x + off.
Proof.
  intros x off H. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. apply Z.mod_small. exact H.
Qed.

Lemma in_blocks_den : forall E live b n z,
  In (b, n) live -> GPS.uE E b <= z < GPS.uE E b + GPS.uE E n -> in_blocks (blocks_den E live) z.
Proof.
  intros E live b n z Hin Hz. exists (GPS.uE E b), (GPS.uE E n). split; [|exact Hz].
  unfold blocks_den. apply in_map_iff. exists (b, n). split; [reflexivity | exact Hin].
Qed.

Lemma bflat_x_sound : forall E M k b off n,
  know_ok SEGS E M k -> bflat_x k b off n = true ->
  0 <= estart E (SA b off) /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ estart E (SA b off) < 2 ^ 64.
Proof.
  intros E M k b off n HK H. unfold bflat_x in H.
  destruct (base_range k b) as [[lo hi]|] eqn:Hb; [|discriminate].
  destruct (xhi k n) as [nh|] eqn:Hnh; [|discriminate].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3. unfold two64 in H2, H3.
  pose proof (base_range_sound SEGS E M k b lo hi HK Hb). pose proof (xhi_sound SEGS E M k n nh HK Hnh).
  unfold estart. cbn [a_base a_off]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition owned3 (Lc : list (Z * Z)) (a : word) : Prop :=
  in_blocks Lc (bv_unsigned a) \/ in_wins PERMc (bv_unsigned a) \/ (SFLOOR <= bv_unsigned a < SPTOPc).
Lemma owned3_owned : forall Lc a, owned3 Lc a -> owned Lc a.
Proof. intros Lc a [H|[H|H]]; [left; exact H | right; left; exact H | right; right; left; exact H]. Qed.


Lemma owned_x_sound3 : forall E M k live perm fl top bud b off n (a : word),
  know_ok SEGS E M k ->
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (live ++ perm) = true ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc -> GPS.floor_sem E fl top bud ->
  owned_x k (live ++ perm) fl top bud b off n = true ->
  estart E (SA b off) <= bv_unsigned a < estart E (SA b off) + elenZ E n ->
  owned3 (blocks_den E live) a.
Proof.
  intros E M k live perm fl top bud b off n a HK Hflat Hperm Htop Hfl Ho Ha. unfold owned3. unfold owned_x in Ho. apply orb_prop in Ho as [Ho|Ho].
  - apply existsb_exists in Ho as [[lb0 ln] [Hin Hx]]. cbn [fst snd] in Hx.
    destruct (split_lit lb0) as [lb lk] eqn:Hsp0.
    pose proof (proj1 (forallb_forall _ _) Hflat _ Hin) as Hfl0. cbn [fst snd] in Hfl0. rewrite Hsp0 in Hfl0.
    pose proof (bflat_x_sound E _ k lb lk ln HK Hfl0) as (F1 & F2 & F3).
    pose proof (xinside_sound SEGS E M k b off n lb lk ln HK Hx) as [X1 X2].
    pose proof (split_lit_denot E lb0 lb lk Hsp0) as Hd.
    rewrite !estart_SA in X1. rewrite !estart_SA in X2. rewrite !estart_SA in Ha. rewrite !estart_SA in F1. rewrite !estart_SA in F2.
    unfold elenZ in *.
    pose proof (u64_range (edenot E lb)). pose proof (u64_range a). pose proof (u64_range (edenot E ln)).
    assert (Hu : GPS.uE E lb0 = bv_unsigned (edenot E lb) + lk) by (unfold GPS.uE; rewrite Hd; apply u64_lit; lia).
    apply in_app_iff in Hin as [Hin|Hin].
    + left. eapply (in_blocks_den E live lb0 ln); [exact Hin|]. rewrite Hu. unfold GPS.uE. lia.
    + right. left. rewrite <- Hperm. eapply (GPS.in_wins_den E perm lb0 ln); [exact Hin|]. rewrite Hu. unfold GPS.uE. lia.
  - (* [comment removed for export] *)
    right. right. rewrite <- Htop. exact (proj1 (GPS.in_floor_sound SEGS E M k fl top bud b off n a HK Ho Hfl Ha)).
Qed.

(* [comment removed for export] *)
Lemma owned_sp_x_sound : forall E M k live perm fl top bud sp b off n (a : word),
  know_ok SEGS E M k ->
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (live ++ perm) = true ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc -> GPS.floor_sem E fl top bud ->
  owned_sp_x k (live ++ perm) fl top bud sp b off n = true ->
  estart E (SA b off) <= bv_unsigned a < estart E (SA b off) + elenZ E n ->
  in_blocks (blocks_den E live) (bv_unsigned a) \/ in_wins PERMc (bv_unsigned a)
  \/ (GPS.uE E sp <= bv_unsigned a /\ SFLOOR <= bv_unsigned a < SPTOPc).
Proof.
  intros E M k live perm fl top bud sp b off n a HK Hflat Hperm Htop Hfl Ho Ha. unfold owned_sp_x in Ho. apply orb_prop in Ho as [Ho|Ho].
  - assert (OX : owned_x k (live ++ perm) fl top bud b off n = true) by (unfold owned_x; rewrite Ho; reflexivity).
    destruct (owned_x_sound3 E M k live perm fl top bud b off n a HK Hflat Hperm Htop Hfl OX Ha) as [H1|[H2|H3]]; [left; exact H1 | right; left; exact H2 |].
    (* [comment removed for export] *)
    apply existsb_exists in Ho as [[lb0 ln] [Hin Hx]]. cbn [fst snd] in Hx.
    destruct (split_lit lb0) as [lb lk] eqn:Hsp0.
    pose proof (proj1 (forallb_forall _ _) Hflat _ Hin) as Hfl0. cbn [fst snd] in Hfl0. rewrite Hsp0 in Hfl0.
    pose proof (bflat_x_sound E _ k lb lk ln HK Hfl0) as (F1 & F2 & F3).
    pose proof (xinside_sound SEGS E M k b off n lb lk ln HK Hx) as [X1 X2].
    pose proof (split_lit_denot E lb0 lb lk Hsp0) as Hd.
    rewrite !estart_SA in X1. rewrite !estart_SA in X2. rewrite !estart_SA in Ha. rewrite !estart_SA in F1. rewrite !estart_SA in F2.
    unfold elenZ in *.
    pose proof (u64_range (edenot E lb)). pose proof (u64_range a). pose proof (u64_range (edenot E ln)).
    assert (Hu : GPS.uE E lb0 = bv_unsigned (edenot E lb) + lk) by (unfold GPS.uE; rewrite Hd; apply u64_lit; lia).
    apply in_app_iff in Hin as [Hin|Hin].
    + left. eapply (in_blocks_den E live lb0 ln); [exact Hin|]. rewrite Hu. unfold GPS.uE. lia.
    + right. left. rewrite <- Hperm. eapply (GPS.in_wins_den E perm lb0 ln); [exact Hin|]. rewrite Hu. unfold GPS.uE. lia.
  - apply andb_prop in Ho as [Ho Hsp]. right. right.
    pose proof (lin_ge0_sound SEGS E M k _ _ HK Hsp) as L. cbn [xt_den] in L.
    rewrite <- Htop. rewrite estart_SA in Ha. split; [unfold GPS.uE; lia|].
    exact (proj1 (GPS.in_floor_sound SEGS E M k fl top bud b off n a HK Ho Hfl ltac:(rewrite estart_SA; exact Ha))).
Qed.

Lemma owned_x_sound : forall E M k live perm fl top bud b off n (a : word),
  know_ok SEGS E M k ->
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (live ++ perm) = true ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc -> GPS.floor_sem E fl top bud ->
  owned_x k (live ++ perm) fl top bud b off n = true ->
  estart E (SA b off) <= bv_unsigned a < estart E (SA b off) + elenZ E n ->
  owned (blocks_den E live) a.
Proof. intros. apply owned3_owned. eapply owned_x_sound3; eassumption. Qed.

(* [comment removed for export] *)
Lemma in_floor_top_ok : forall k fl top bud b off n, in_floor k fl top bud b off n = true -> top_ok k fl top bud = true.
Proof.
  intros k fl top bud b off n H. unfold in_floor in H. unfold top_ok.
  destruct (split_lit top) as [tb tk]. destruct (base_range k tb) as [[tlo thi]|]; [|destruct fl; discriminate].
  destruct fl as [f|]; [apply andb_prop in H as [H _]|]; apply andb_prop in H as [H _]; exact H.
Qed.

Lemma top_ok_sound : forall E M k fl top bud tb tk,
  know_ok SEGS E M k -> top_ok k fl top bud = true -> split_lit top = (tb, tk) ->
  sptop_den E top = bv_unsigned (edenot E tb) + tk /\ 0 <= bud /\ 0 < bv_unsigned (edenot E tb) + tk < 2 ^ 64
  /\ (fl = None -> CEIL + bud <= bv_unsigned (edenot E tb) + tk).
Proof.
  intros E M k fl top bud tb tk HK H Hsp. unfold top_ok in H. rewrite Hsp in H.
  destruct (base_range k tb) as [[tlo thi]|] eqn:Hbr; [|destruct fl; discriminate].
  pose proof (base_range_sound SEGS E M k tb tlo thi HK Hbr) as [B1 B2].
  pose proof (u64_range (edenot E tb)) as Rt.
  assert (NUM : 0 <= bud /\ 0 < tlo + tk /\ thi + tk < 2 ^ 64 /\ (fl = None -> CEIL + bud <= tlo + tk)).
  { destruct fl as [f|]; apply andb_prop in H as [H H3]; apply andb_prop in H as [H1 H2];
      apply Z.leb_le in H1; apply Z.ltb_lt in H3; [apply Z.ltb_lt in H2 | apply Z.leb_le in H2]; unfold CEIL, two64 in *;
      (split; [lia|]); (split; [lia|]); (split; [lia|]); intros HN; [discriminate HN | lia]. }
  destruct NUM as (N1 & N2 & N3 & N4).
  assert (Ht : uE E top = bv_unsigned (edenot E tb) + tk).
  { unfold uE. rewrite (split_lit_denot E top tb tk Hsp). apply u64_lit. lia. }
  unfold sptop_den. rewrite Ht. destruct (Z.eqb_spec (bv_unsigned (edenot E tb) + tk) 0) as [Hz|Hz]; [lia|].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. intros HN. specialize (N4 HN). lia.
Qed.

(* [comment removed for export] *)
Lemma floor_term_sound : forall E M k fl top bud fb fo,
  know_ok SEGS E M k -> top_ok k fl top bud = true -> GPS.floor_sem E fl top bud -> floor_term fl top bud = (fb, fo) ->
  CEIL_run <= uE E fb + fo.
Proof. pose proof sfloor_ge as SFG_.
  intros E M k fl top bud fb fo HK Htok Hfl Hft. unfold floor_term in Hft.
  destruct (split_lit top) as [tb tk] eqn:Hsp.
  destruct (top_ok_sound E M k fl top bud tb tk HK Htok Hsp) as (TOPEQ & Hb & TOPR & TOPN).
  destruct fl as [f|]; cbn [GPS.floor_sem] in Hfl; injection Hft as <- <-.
  - lia.
  - rewrite TOPEQ in Hfl. unfold uE. lia.
Qed.

Lemma stack_x_sound : forall E M k fl top bud e,
  know_ok SEGS E M k -> GPS.floor_sem E fl top bud -> stack_x k fl top bud e = true -> CEIL_run <= uE E e.
Proof.
  intros E M k fl top bud e HK Hfl H. unfold stack_x in H. apply andb_prop in H as [Htok Hlin].
  destruct (floor_term fl top bud) as [fb fo] eqn:Hft.
  pose proof (floor_term_sound E M k fl top bud fb fo HK Htok Hfl Hft) as F.
  pose proof (lin_ge0_sound SEGS E M k _ _ HK Hlin) as L. cbn [xt_den] in L. unfold uE in *. lia.
Qed.

(* [comment removed for export] *)
Lemma srange_x_sound : forall E M k fl top bud b off n,
  know_ok SEGS E M k -> GPS.floor_sem E fl top bud -> srange_x k fl top bud b off n = true ->
  CEIL_run <= bv_unsigned (edenot E b) + off
  /\ bv_unsigned (edenot E b) + off + bv_unsigned (edenot E n) <= two47
  /\ estart E (SA b off) = bv_unsigned (edenot E b) + off /\ elenZ E n = bv_unsigned (edenot E n).
Proof.
  intros E M k fl top bud b off n HK Hfl H. unfold srange_x in H.
  apply andb_prop in H as [H Hbr]. apply andb_prop in H as [Htok Hlin].
  destruct (floor_term fl top bud) as [fb fo] eqn:Hft.
  pose proof (floor_term_sound E M k fl top bud fb fo HK Htok Hfl Hft) as F.
  pose proof (lin_ge0_sound SEGS E M k _ _ HK Hlin) as L. cbn [xt_den] in L.
  destruct (base_range k b) as [[blo bhi]|] eqn:Hb; [|discriminate]. destruct (xhi k n) as [nh|] eqn:Hnh; [|discriminate].
  apply andb_prop in Hbr as [Hbr H3]. apply andb_prop in Hbr as [Hbr H4]. apply andb_prop in Hbr as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
  pose proof (base_range_sound SEGS E M k b blo bhi HK Hb) as [B1 B2]. pose proof (xhi_sound SEGS E M k n nh HK Hnh) as N2.
  pose proof (u64_range (edenot E n)) as Rn. pose proof (u64_range (edenot E b)) as Rb. pose proof GlzConst.ceil_lo as CL.
  (* [comment removed for export] *)
  assert (END : bv_unsigned (edenot E b) + off + bv_unsigned (edenot E n) <= two47).
  { unfold send_hi in H3. unfold two64 in H4.
    assert (DF : bv_unsigned (edenot E b) + off + bv_unsigned (edenot E n) <= bhi + off + nh) by lia.
    assert (SUM : forall n', xrange2 k (eadd (eaddz b off) n') <> None -> n' = n ->
                  forall jl jh, xrange2 k (eadd (eaddz b off) n') = Some (jl, jh) -> bv_unsigned (edenot E b) + off + bv_unsigned (edenot E n) <= jh).
    { intros n' _ -> jl jh Hj. pose proof (xrange2_sound SEGS E M k _ jl jh HK Hj) as [_ J2].
      assert (S1 : bv_unsigned (edenot E (eaddz b off)) = bv_unsigned (edenot E b) + off).
      { unfold eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u_lit64. unfold two64.
        rewrite Zplus_mod_idemp_r. apply Z.mod_small. lia. }
      assert (S2 : bv_unsigned (edenot E (eadd (eaddz b off) n)) = bv_unsigned (edenot E (eaddz b off)) + bv_unsigned (edenot E n)).
      { unfold eadd. rewrite mkAlu_denot, u_add64. apply Z.mod_small. rewrite S1. unfold two64. lia. }
      rewrite S2, S1 in J2. exact J2. }
    lazymatch type of H3 with context [if ?c then _ else _] => destruct c; [lia|] end.   (* [comment removed for export] *)
    destruct (xrange2 k (eadd (eaddz b off) n)) as [[jl jh]|] eqn:Hj; [pose proof (SUM _ ltac:(rewrite Hj; discriminate) eq_refl jl jh Hj); lia | lia]. }
  unfold two47 in *.
  split; [unfold uE in *; lia|]. split; [lia|]. split.
  - rewrite estart_SA. reflexivity.
  - unfold elenZ. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma send_hi_sound : forall E M k b off n dflt,
  know_ok SEGS E M k ->
  0 <= bv_unsigned (edenot E b) + off ->
  bv_unsigned (edenot E b) + off + bv_unsigned (edenot E n) < two64 ->
  bv_unsigned (edenot E b) + off + bv_unsigned (edenot E n) <= dflt ->
  bv_unsigned (edenot E b) + off + bv_unsigned (edenot E n) <= send_hi k b off n dflt.
Proof.
  intros E M k b off n dflt HK H0 H64 Hd. unfold send_hi.
  pose proof (u64_range (edenot E n)) as Rn. pose proof (u64_range (edenot E b)) as Rb.
  lazymatch goal with |- context [if ?c then _ else _] => destruct c; [lia|] end.
  destruct (xrange2 k (eadd (eaddz b off) n)) as [[jl jh]|] eqn:Hj; [|lia].
  pose proof (xrange2_sound SEGS E M k _ jl jh HK Hj) as [_ J2].
  assert (S1 : bv_unsigned (edenot E (eaddz b off)) = bv_unsigned (edenot E b) + off).
  { unfold eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u_lit64. unfold two64.
    rewrite Zplus_mod_idemp_r. apply Z.mod_small. unfold two64 in H64. lia. }
  assert (S2 : bv_unsigned (edenot E (eadd (eaddz b off) n)) = bv_unsigned (edenot E (eaddz b off)) + bv_unsigned (edenot E n)).
  { unfold eadd. rewrite mkAlu_denot, u_add64. apply Z.mod_small. rewrite S1. unfold two64 in *. lia. }
  rewrite S2, S1 in J2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lit_disjoint_sound : forall lo hi ps z,
  lit_disjoint lo hi ps = true -> lo <= z < hi -> ~ in_wins ps z.
Proof.
  intros lo hi ps z. induction ps as [|[a b] r IH]; intros H Hz [l [h [Hin Hlh]]].
  - destruct Hin.
  - cbn [lit_disjoint] in H. apply andb_prop in H as [H1 H2].
    destruct Hin as [Heq|Hin].
    + injection Heq as <- <-. apply orb_prop in H1 as [H1|H1]; apply Z.leb_le in H1; lia.
    + apply (IH H2 Hz). exists l, h. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma in_wins_privx : forall z, in_wins (g_privx G) z <-> errw G z \/ in_wins (g_priv G) z.
Proof.
  intros z. unfold g_privx, errw, in_wins. split.
  - intros (lo & hi & [H|H] & Hz); [injection H as <- <-; left; exact Hz | right; exists lo, hi; split; assumption].
  - intros [Hz|(lo & hi & H & Hz)]; [exists (g_errno G), (g_errno G + 4); split; [left; reflexivity | exact Hz] | exists lo, hi; split; [right; exact H | exact Hz]].
Qed.

(* [comment removed for export] *)
Definition frame_kept (stk : Z) (Lc : list (Z * Z)) (sp : Z) (a : word) : Prop :=
  (owned Lc a /\ ~ (sp - stk <= bv_unsigned a < sp) /\ ~ errw G (bv_unsigned a))
  \/ (g_ro_lo G <= bv_unsigned a < g_img_hi G /\ ~ in_wins (g_privx G) (bv_unsigned a))
  \/ (SPTOPc <= bv_unsigned a /\ sp <= SPTOPc)
  \/ sp <= bv_unsigned a.                         (* [comment removed for export] *)

Lemma kn_vars_lt_filter_vars : forall v (f : kentry -> bool) l,
  kn_vars_lt v (List.filter (fun K => kentry_vars_lt v K && f K)%bool l) = true.
Proof.
  intros v f l. induction l as [|K r IH]; [reflexivity|].
  cbn [List.filter]. destruct (kentry_vars_lt v K && f K)%bool eqn:Hc; [|exact IH].
  cbn [kn_vars_lt]. apply andb_prop in Hc as [-> _]. exact IH.
Qed.

Lemma kn_vars_lt_app2 : forall v l1 l2, kn_vars_lt v l1 = true -> kn_vars_lt v l2 = true -> kn_vars_lt v (l1 ++ l2) = true.
Proof.
  intros v l1 l2 H1 H2. induction l1 as [|K r IH]; [exact H2|]. cbn [kn_vars_lt app] in *.
  apply andb_prop in H1 as [-> Hr]. exact (IH Hr).
Qed.

Lemma keep_owned_vars : forall stk k live objs fl top bud sp v, kn_vars_lt v (keep_owned G stk k live objs fl top bud sp v) = true.
Proof.
  intros stk k live objs fl top bud sp v. rewrite keep_owned_eq. unfold keep_owned_ref. destruct (split_lit sp) as [spb spk].
  apply kn_vars_lt_app2; [|apply kn_vars_lt_app2; [|apply kn_vars_lt_app2]]; apply kn_vars_lt_filter_vars.
Qed.

(* [comment removed for export] *)
Lemma kwr_bytes : forall E M b o n,
  kentry_ok SEGS E M (KWr (SA b o) n) <->
  (flat E (SA b o) (elenZ E n) /\ forall x : word, estart E (SA b o) <= bv_unsigned x < estart E (SA b o) + elenZ E n ->
                                     RiscvSemantics.store_ok SEGS M x 1 = true).
Proof.
  intros E M b o n. cbn [kentry_ok]. split; intros [Hfl H]; split; try exact Hfl; pose proof Hfl as (F1 & F2 & F3 & F4).
  - intros x Hx. replace x with (Z_to_bv 64 (estart E (SA b o) + (bv_unsigned x - estart E (SA b o)))).
    2:{ apply bv_eq. rewrite u64_lit by lia. lia. }
    apply (H (bv_unsigned x - estart E (SA b o)) 1%nat); [lia | cbn; lia].
  - intros d m Hd Hdm. destruct m as [|m']; [reflexivity|].
    apply store_ok_of_all; [rewrite u64_lit by lia; lia|]. intros x Hx. rewrite u64_lit in Hx by lia.
    eapply (store_ok_all SEGS M 1 x); [change (Z.of_nat 1) with 1; pose proof (u64_range x); lia | apply H; lia | change (Z.of_nat 1) with 1; lia].
Qed.

Lemma store_ok1_ext : forall M M' (x : word), M' x = M x -> RiscvSemantics.store_ok SEGS M' x 1 = RiscvSemantics.store_ok SEGS M x 1.
Proof. intros M M' x H. cbn [RiscvSemantics.store_ok]. unfold wview. rewrite H. reflexivity. Qed.
(* [comment removed for export] *)
Lemma store_ok1_errno : forall M M' (x : word), (M x <> None -> M' x <> None) ->
  RiscvSemantics.store_ok SEGS M x 1 = true -> RiscvSemantics.store_ok SEGS M' x 1 = true.
Proof.
  intros M M' x H Hs. cbn [RiscvSemantics.store_ok] in *. unfold wview in *.
  destruct (M x) as [b|] eqn:HMx.
  - destruct (M' x) as [b'|] eqn:HM'x; [reflexivity|]. exfalso. apply H; congruence.
  - destruct (M' x) as [b'|]; [reflexivity | exact Hs].
Qed.

(* [comment removed for export] *)
Lemma above_x_sound : forall E M k top sp b off n (x : word),
  know_ok SEGS E M k -> above_x k top sp b off n = true -> sptop_den E top = SPTOPc ->
  estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E n ->
  SPTOPc <= bv_unsigned x /\ bv_unsigned (edenot E sp) <= SPTOPc.
Proof.
  intros E M k top sp b off n x HK H Htop Hx. unfold above_x in H.
  destruct (xlo k top) as [tlo|] eqn:Ht; [|discriminate].
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  apply Z.ltb_lt in H.
  pose proof (xlo_sound SEGS E M k top tlo HK Ht) as T0.
  pose proof (lin_ge0_sound SEGS E M k [(b, off)] [(top, 0)] HK X1) as L1. cbn [xt_den] in L1.
  pose proof (lin_ge0_sound SEGS E M k [(top, 0)] [(sp, 0)] HK X0) as L2. cbn [xt_den] in L2.
  assert (HT : SPTOPc = bv_unsigned (edenot E top)).
  { rewrite <- Htop. unfold sptop_den, GPS.uE. destruct (Z.eqb_spec (bv_unsigned (edenot E top)) 0); [lia | reflexivity]. }
  rewrite HT. rewrite estart_SA in Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma img_lit_x_sound : forall E M k b off n (x : word),
  know_ok SEGS E M k -> img_lit_x G k b off n = true ->
  0 <= estart E (SA b off) -> estart E (SA b off) < 2 ^ 64 ->
  estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E n ->
  g_ro_lo G <= bv_unsigned x < g_img_hi G /\ ~ in_wins (g_privx G) (bv_unsigned x).
Proof.
  intros E M k b off n x HK H E1 E2 Hx. unfold img_lit_x in H.
  destruct (xlo k (eaddz b off)) as [lo|] eqn:Hl; [|discriminate]. destruct (xhi k (eaddz b off)) as [hi|] eqn:Hh; [|discriminate].
  destruct (xhi k n) as [nh|] eqn:Hnh; [|discriminate].
  apply andb_prop in H as [H Hdj]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  pose proof (xlo_sound SEGS E M k _ lo HK Hl) as S1. pose proof (xhi_sound SEGS E M k _ hi HK Hh) as S2. pose proof (xhi_sound SEGS E M k n nh HK Hnh) as S3.
  unfold eaddz in S1, S2. rewrite mkAlu_denot in S1, S2. cbn [edenot] in S1, S2. rewrite alu_add in S1, S2. unfold v_add in S1, S2.
  rewrite estart_SA in Hx, E1, E2. rewrite u_add_off in S1, S2 by lia. unfold elenZ in Hx.
  split; [lia|]. eapply lit_disjoint_sound; [exact Hdj | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma keep_shadow_foot : forall E M k objs fl top bud sp K (x : word),
  know_ok SEGS E M k -> kentry_ok SEGS E M K -> keep_shadow G k objs fl top bud sp K = true ->
  GPS.floor_sem E fl top bud ->
  in_kfoot E K (bv_unsigned x) -> shz E objs (uE E sp) (bv_unsigned x).
Proof.
  intros E M k objs fl top bud sp K x HK HKK Hkeep Hflr Hx. unfold in_kfoot, kfoot in Hx.
  assert (SK : forall b off n nn, shadow_kept k objs fl top bud b off n = true -> n = ELit nn ->
            estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + nn -> shz E objs (uE E sp) (bv_unsigned x)).
  { intros b off n nn Hsk Hn Hxx. subst n. unfold shadow_kept in Hsk.
    destruct (srl3_base b) as [xb|] eqn:Hb; [|discriminate].
    apply andb_prop in Hsk as [Hsk Halt]. apply andb_prop in Hsk as [Hxal Hnn]. apply Z.leb_le in Hxal. apply Z.leb_le in Hnn.
    rewrite estart_SA in Hxx. rewrite (srl3_base_denot E b xb Hb) in Hxx.
    pose proof (ealign3_mod8 SEGS E M k xb HK Hxal) as Hx8. unfold uE in Hx8.
    apply orb_prop in Halt as [Hst|Hob].
    - (* [comment removed for export] *) right. left.
      apply andb_prop in Hst as [Hst Hsr]. apply andb_prop in Hst as [Hsb Hn43]. apply Z.leb_le in Hsb. apply Z.ltb_lt in Hn43.
      destruct (srange_x_sound E M k fl top bud xb (8 * (off - SB)) (ELit (8 * nn)) HK Hflr Hsr) as (R1 & R2 & _ & _).
      cbn [edenot] in R2. rewrite u64_lit in R2 by lia.
      unfold in_sshadow. unfold uE in *. unfold two47, SB, HEAPLO in *.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      lia.
    - (* [comment removed for export] *) left.
      destruct (shadow_objs_x_sound SEGS E M k objs xb off nn (bv_unsigned x) HK Hxal Hob Hxx) as (bb & ln & Hinb & Hsh).
      exists bb, ln. split; [exact Hinb | exact Hsh]. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  assert (SI : forall b off n nn, ishadow_lit_x G b off n = true -> n = ELit nn ->
            estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + nn -> shz E objs (uE E sp) (bv_unsigned x)).
  { intros b off n nn Hil Hn Hxx. subst n. unfold ishadow_lit_x in Hil.
    destruct b as [z| | | | | | |]; try discriminate. destruct z; try discriminate.
    repeat match type of Hil with (_ && _)%bool = true => apply andb_prop in Hil as [Hil ?Y] end.
    apply Z.leb_le in Hil. apply Z.leb_le in Y0. apply Z.leb_le in Y.
    rewrite estart_SA in Hxx. cbn [edenot] in Hxx. rewrite u64_lit in Hxx by lia.
    right. right. unfold in_ishadow.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia. }
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  (* [comment removed for export] *)
  assert (S3 : forall b off n nn, (shadow_kept k objs fl top bud b off n || ishadow_lit_x G b off n)%bool = true -> n = ELit nn ->
            estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + nn -> shz E objs (uE E sp) (bv_unsigned x)).
  { intros b off n nn H3 Hn Hxx. apply orb_prop in H3 as [H3|H3];
      [eapply (SK b off n nn); eassumption | eapply (SI b off n nn); eassumption]. }
  assert (L3 : forall b off n, (shadow_kept k objs fl top bud b off n || ishadow_lit_x G b off n)%bool = true ->
            exists z, n = ELit z /\ 0 <= z).
  { intros b off n H3. apply orb_prop in H3 as [H1|H1].
    - unfold shadow_kept in H1. destruct (srl3_base b); [|discriminate]. destruct n as [z| | | | | | |]; try discriminate.
      apply andb_prop in H1 as [H1 _]. apply andb_prop in H1 as [_ Hz]. apply Z.leb_le in Hz. exists z. split; [reflexivity | exact Hz].
    - unfold ishadow_lit_x in H1. destruct b as [z0| | | | | | |]; try discriminate. destruct z0; try discriminate. destruct n as [z| | | | | | |]; try discriminate.
      apply andb_prop in H1 as [H1 _]. apply andb_prop in H1 as [_ Hz]. apply Z.leb_le in Hz. exists z. split; [reflexivity | exact Hz]. }
  unfold keep_shadow in Hkeep.
  destruct K as [[b o] w vv|[b o] nn|[b o] nn kb|ilo ihi|e m|e rlo rhi|[b o] nn|a1 n1 a2 n2|[b o] nn fc|[b o] nn | [b o] nn | fv flo fd];
    try discriminate Hkeep; cbn [kentry_ok] in HKK.
  - (* [comment removed for export] *) destruct HKK as (Hw8 & Hfl & Hrd). eapply (S3 b o _ (Z.of_nat w)); [exact Hkeep | reflexivity | exact Hx].
  - (* [comment removed for export] *) destruct HKK as [Hfl _].
    assert (EN : exists nn0, nn = ELit nn0 /\ elenZ E nn <= nn0).
    { destruct (L3 b o nn Hkeep) as (z & Hz & Hz0). exists z. split; [exact Hz|]. subst nn.
      unfold elenZ. cbn [edenot]. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_le; [exact Hz0 | reflexivity]. }
    destruct EN as (nn0 & Enn & Hel).
    assert (Hx' : estart E (SA b o) <= bv_unsigned x < estart E (SA b o) + nn0) by lia.
    eapply (S3 b o nn nn0); [exact Hkeep | exact Enn | exact Hx'].
  - (* [comment removed for export] *) destruct HKK as [Hfl _].
    assert (EN : exists nn0, nn = ELit nn0 /\ elenZ E nn <= nn0).
    { destruct (L3 b o nn Hkeep) as (z & Hz & Hz0). exists z. split; [exact Hz|]. subst nn.
      unfold elenZ. cbn [edenot]. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_le; [exact Hz0 | reflexivity]. }
    destruct EN as (nn0 & Enn & Hel).
    assert (Hx' : estart E (SA b o) <= bv_unsigned x < estart E (SA b o) + nn0) by lia.
    eapply (S3 b o nn nn0); [exact Hkeep | exact Enn | exact Hx'].
  - (* [comment removed for export] *) destruct HKK as [Hfl _].
    assert (EN : exists nn0, nn = ELit nn0 /\ elenZ E nn <= nn0).
    { destruct (L3 b o nn Hkeep) as (z & Hz & Hz0). exists z. split; [exact Hz|]. subst nn.
      unfold elenZ. cbn [edenot]. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_le; [exact Hz0 | reflexivity]. }
    destruct EN as (nn0 & Enn & Hel).
    assert (Hx' : estart E (SA b o) <= bv_unsigned x < estart E (SA b o) + nn0) by lia.
    eapply (S3 b o nn nn0); [exact Hkeep | exact Enn | exact Hx'].
  - (* [comment removed for export] *) destruct HKK as [Hfl _].
    assert (EN : exists nn0, nn = ELit nn0 /\ elenZ E nn <= nn0).
    { destruct (L3 b o nn Hkeep) as (z & Hz & Hz0). exists z. split; [exact Hz|]. subst nn.
      unfold elenZ. cbn [edenot]. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_le; [exact Hz0 | reflexivity]. }
    destruct EN as (nn0 & Enn & Hel).
    assert (Hx' : estart E (SA b o) <= bv_unsigned x < estart E (SA b o) + nn0) by lia.
    eapply (S3 b o nn nn0); [exact Hkeep | exact Enn | exact Hx'].
  - (* [comment removed for export] *) destruct HKK as [Hfl _].
    assert (EN : exists nn0, nn = ELit nn0 /\ elenZ E nn <= nn0).
    { destruct (L3 b o nn Hkeep) as (z & Hz & Hz0). exists z. split; [exact Hz|]. subst nn.
      unfold elenZ. cbn [edenot]. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_le; [exact Hz0 | reflexivity]. }
    destruct EN as (nn0 & Enn & Hel).
    assert (Hx' : estart E (SA b o) <= bv_unsigned x < estart E (SA b o) + nn0) by lia.
    eapply (S3 b o nn nn0); [exact Hkeep | exact Enn | exact Hx'].
  - (* [comment removed for export] *)
    destruct HKK as (Hfl & H47 & _). pose proof Hfl as (F1 & F2 & F3 & F4). rewrite estart_SA in Hx, H47, F1, F2, F4.
    apply andb_prop in Hkeep as [Hl0 Hkeep]. destruct (xlo k nn) as [nl|] eqn:Hnl; [|discriminate]. apply Z.ltb_lt in Hl0.
    pose proof (xlo_sound SEGS E M k nn nl HK Hnl) as Bnl. unfold elenZ in F3, F4, Hx, H47.
    set (s0 := bv_unsigned (edenot E b) + o) in *. set (l0 := bv_unsigned (edenot E nn)) in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (HULL : forall B N, B <= s0 -> s0 + l0 <= B + N -> in_shadow SB B N (bv_unsigned x)).
    { intros B N HB HN. unfold in_shadow. unfold SB in *. lia. }
    assert (STK : CEIL_run <= s0 -> s0 + l0 <= two47 -> in_sshadow (bv_unsigned x)).
    { intros HTc HTs. unfold in_sshadow. pose proof GlzConst.ceil_lo as CL. unfold SB, HEAPLO, two47, CEIL in *. lia. }
    assert (IMG : g_ro_lo G <= s0 -> s0 + l0 <= g_img_hi G -> in_ishadow (bv_unsigned x)).
    { intros I1 I2. unfold in_ishadow. unfold SB in *. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    apply orb_prop in Hkeep as [Hkeep|Him]; [apply orb_prop in Hkeep as [Hkb|Hsp]|].
    + (* [comment removed for export] *)
      apply existsb_exists in Hkb as [[lb0 ln] [Hin Hxi]]. cbn [fst snd] in Hxi.
      destruct (split_lit lb0) as [lb lk] eqn:Hls. apply andb_prop in Hxi as [Hxi Hbf].
      destruct (xinside_sound SEGS E M k b o nn lb lk ln HK Hxi) as [X1 X2]. rewrite !estart_SA in X1, X2. unfold elenZ in X2. fold s0 in X1, X2. fold l0 in X2.
      destruct (bflat_x_sound E M k lb lk ln HK Hbf) as (B1 & B2 & B3). rewrite estart_SA in B1, B2, B3.
      assert (Hu : uE E lb0 = bv_unsigned (edenot E lb) + lk) by (unfold uE; rewrite (split_lit_denot E lb0 lb lk Hls); apply u64_lit; lia).
      left. exists (uE E lb0), (uE E ln). split.
      * unfold blocks_den. apply in_map_iff. exists (lb0, ln). split; [reflexivity | exact Hin].
      * rewrite Hu. apply HULL; unfold uE, elenZ in *; lia.
    + (* [comment removed for export] *)
      right. left.
      destruct (srange_x_sound E M k fl top bud b o nn HK Hflr Hsp) as (R1 & R2 & _ & _). fold s0 in R1, R2. fold l0 in R2.
      apply STK; [exact R1 | exact R2].
    + (* [comment removed for export] *)
      right. right.
      assert (Him' : forall y : word, s0 <= bv_unsigned y < s0 + l0 -> g_ro_lo G <= bv_unsigned y < g_img_hi G /\ ~ in_wins (g_privx G) (bv_unsigned y)).
      { intros y Hy. apply (img_lit_x_sound E M k b o nn y HK Him); rewrite ?estart_SA; unfold elenZ; unfold s0, l0 in *; lia. }
      destruct (Him' (Z_to_bv 64 s0) ltac:(rewrite u64_lit by lia; lia)) as [[I1 _] _]. rewrite u64_lit in I1 by lia.
      destruct (Him' (Z_to_bv 64 (s0 + l0 - 1)) ltac:(rewrite u64_lit by lia; lia)) as [[_ I2] _]. rewrite u64_lit in I2 by lia.
      apply IMG; lia.
Qed.

(* [comment removed for export] *)
Lemma errno_apart_x_sound : forall E M k b off n (x : word),
  know_ok SEGS E M k -> errno_apart_x G k b off n = true ->
  estart E (SA b off) <= bv_unsigned x < estart E (SA b off) + elenZ E n -> ~ errw G (bv_unsigned x).
Proof.
  intros E M k b off n x HK H Hx He. unfold errno_apart_x in H.
  apply andb_prop in H as [H Hap]. apply andb_prop in H as [H0 H4]. apply Z.leb_le in H0. apply Z.ltb_lt in H4.
  pose proof (ranges_apart_x_sound SEGS E M k _ _ _ (ELit 0) (g_errno G) (ELit 4) HK Hap) as Hd.
  rewrite !estart_SA in Hd. unfold elenZ in Hd. cbn [edenot] in Hd. rewrite (u64_lit 0) in Hd by lia. rewrite (u64_lit 4) in Hd by lia.
  rewrite estart_SA in Hx. unfold elenZ in Hx. unfold errw in He.
  replace ((0 + g_errno G) mod 2 ^ 64) with (g_errno G) in Hd by (rewrite Z.mod_small; lia). lia.
Qed.

Lemma keep_owned_sound : forall stk E M M' k live perm objs fl top bud sp spb spk v K,
  0 <= stk < 2 ^ 62 ->    (* [comment removed for export] *)
  know_ok SEGS E M k ->
  forallb (fun bl => let '(lb, lk) := split_lit (fst bl) in bflat_x k lb lk (snd bl)) (live ++ perm) = true ->
  wins_den E perm = PERMc -> sptop_den E top = SPTOPc ->
  split_lit sp = (spb, spk) -> 0 <= bv_unsigned (edenot E spb) + spk < 2 ^ 64 ->
  GPS.floor_sem E fl top bud ->               (* [comment removed for export] *)
  (forall a : word, frame_kept stk (blocks_den E live) (bv_unsigned (edenot E sp)) a -> M' a = M a) ->
  (forall a : word, bv_unsigned (edenot E sp) - stk <= bv_unsigned a < bv_unsigned (edenot E sp) ->
                    M' a <> None /\ RiscvSemantics.store_ok SEGS M' a 1 = true) ->
  (forall a : word, errw G (bv_unsigned a) -> M a <> None -> M' a <> None) ->   (* [comment removed for export] *)
  (forall a : word, shz E objs (uE E sp) (bv_unsigned a) -> M' a = M a) ->      (* [comment removed for export] *)
  In K (keep_owned G stk k (live ++ perm) objs fl top bud sp v) -> kentry_ok SEGS E M' K.
Proof.
  intros stk E M M' k live perm objs fl top bud sp spb spk v K Hstk HK Hflat Hperm Htop Hsp Hspr Hceil Hfr Hscr Herr Hshz Hin.
  rewrite keep_owned_eq in Hin. unfold keep_owned_ref in Hin. rewrite Hsp in Hin. apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]]].
  4:{ (* [comment removed for export] *)
      apply filter_In in Hin as [Hin Hkeep]. apply andb_prop in Hkeep as [_ Hkeep].
      pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
      destruct K as [| | | | | | | | | | | fv flo fd]; try discriminate. cbn [kentry_ok] in HKK |- *. unfold keep_kfpc in Hkeep.
      pose proof (lin_ge0_sound SEGS E M k _ _ HK Hkeep) as L. cbn [xt_den] in L.
      destruct HKK as [HKK HR]. split; [|exact HR].   (* [comment removed for export] *)
      apply (AX2S.fpc_kept_gen M _ _ _ HKK M'). destruct (AX2S.fpc_shape _ _ _ _ HKK) as [ST|FR]; [left; exact ST | right].
      intros a Ha. pose proof (u64_range (edenot E sp)) as SPR. unfold AX2S.FPC_HI in Ha.
      assert (Hau : bv_unsigned (Z_to_bv 64 a) = a) by (apply u64_lit; lia).
      apply Hfr. right; right; right. rewrite Hau. unfold GPS.uE in *. lia. }
  3:{ (* [comment removed for export] *)
      apply filter_In in Hin as [Hin Hkeep]. apply andb_prop in Hkeep as [_ Hkeep].
      pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
      eapply kentry_ok_footprint; [exact HKK|]. intros x Hx. apply Hshz.
      exact (keep_shadow_foot E M k objs fl top bud sp K x HK HKK Hkeep Hceil Hx). }
  - (* [comment removed for export] *)
    apply filter_In in Hin as [Hin Hkeep]. apply andb_prop in Hkeep as [_ Hkeep].
    pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK. unfold keep_sticky in Hkeep.
    destruct K as [[b o] w vv|[b o] nn|[b o] nn kb|ilo ihi|e m|e rlo rhi|[b o] nn|a1 n1 a2 n2|[b o] nn fc|[b o] nn | [b o] nn | fv flo fd];
      try exact HKK; try discriminate.
    + (* [comment removed for export] *) apply andb_prop in Hkeep as [Hkeep Hdj]. apply andb_prop in Hkeep as [Hlo Hhi].
      apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
      eapply kentry_ok_footprint; [exact HKK|]. intros x Hx. unfold in_kfoot, kfoot in Hx.
      apply Hfr. right. left. split; [lia|]. eapply lit_disjoint_sound; [exact Hdj | lia].
    + (* [comment removed for export] *) apply (proj1 (kwr_bytes E M b o nn)) in HKK as [Hfl HS]. apply (proj2 (kwr_bytes E M' b o nn)). split; [exact Hfl|].
      intros x Hx. apply orb_prop in Hkeep as [Hkeep|Habv].
      2:{ pose proof (above_x_sound E M k top sp b o nn x HK Habv Htop Hx) as AB.
          rewrite (store_ok1_ext M M' x); [apply HS; exact Hx|]. apply Hfr. right; right; left. exact AB. }
      pose proof (owned_x_sound3 E M k live perm fl top bud b o nn x HK Hflat Hperm Htop Hceil Hkeep Hx) as Ho.
      destruct (errw_dec G (bv_unsigned x)) as [Hew|Hnew]; [apply (store_ok1_errno M M' x (Herr x Hew)); apply HS; exact Hx|].   (* [comment removed for export] *)
      destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (edenot E sp) - stk)) as [Hl|Hge];
        [| destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (edenot E sp))) as [Hl2|Hge2]; [exact (proj2 (Hscr x ltac:(lia)))|]].
      all: rewrite (store_ok1_ext M M' x); [apply HS; exact Hx|]; apply Hfr; left; split; [apply owned3_owned; exact Ho | split; [lia | exact Hnew]].
    + (* [comment removed for export] *) cbn [kentry_ok] in HKK |- *. destruct HKK as [Hfl HS]. split; [exact Hfl|]. intros i Hi.
      pose proof Hfl as (F1 & F2 & F3 & F4). set (x := Z_to_bv 64 (estart E (SA b o) + i)).
      assert (Hux : bv_unsigned x = estart E (SA b o) + i) by (unfold x; apply u64_lit; lia).
      apply orb_prop in Hkeep as [Hkeep|Habv].
      2:{ pose proof (above_x_sound E M k top sp b o nn x HK Habv Htop ltac:(rewrite Hux; lia)) as AB.
          rewrite (Hfr x); [apply HS; exact Hi|]. right; right; left. exact AB. }
      pose proof (owned_x_sound3 E M k live perm fl top bud b o nn x HK Hflat Hperm Htop Hceil Hkeep ltac:(rewrite Hux; lia)) as Ho.
      destruct (errw_dec G (bv_unsigned x)) as [Hew|Hnew]; [apply (Herr x Hew); apply HS; exact Hi|].   (* [comment removed for export] *)
      destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (edenot E sp) - stk)) as [Hl|Hge];
        [| destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (edenot E sp))) as [Hl2|Hge2]; [exact (proj1 (Hscr x ltac:(lia)))|]].
      all: rewrite (Hfr x); [apply HS; exact Hi|]; left; split; [apply owned3_owned; exact Ho | split; [lia | exact Hnew]].
  - (* [comment removed for export] *)
    apply filter_In in Hin as [Hin Hkeep]. apply andb_prop in Hkeep as [_ Hkeep].
    assert (HKc : know_ok SEGS E M (kn_cutout (kn_cutout k spb (spk - stk) (ELit stk)) (ELit 0) (g_errno G) (ELit 4))).
    { eapply know_ok_cutout; [eapply know_ok_cutout; [exact HK|]; intros; reflexivity|]. intros; reflexivity. }   (* [comment removed for export] *)
    pose proof (proj1 (Forall_forall _ _) HKc K Hin) as HKK.
    unfold keep_content in Hkeep.
    destruct K as [[b o] w vv|[b o] nn|[b o] nn kb|ilo ihi|e m|e rlo rhi|[b o] nn|a1 n1 a2 n2|[b o] nn fc|[b o] nn | [b o] nn | fv flo fd];
      cbn [kentry_range] in Hkeep; try discriminate.
    1: assert (Hw8 : Z.of_nat w <= 8) by (cbn [kentry_ok] in HKK; destruct HKK as [Hw _]; lia).
    all: rewrite Hsp in Hkeep.
    all: pose proof (split_lit_denot E sp spb spk Hsp) as Hspd.
    all: (eapply kentry_ok_footprint; [exact HKK|]; intros x Hx; unfold in_kfoot, kfoot in Hx).
    (* [comment removed for export] *)
    all: (apply orb_prop in Hkeep as [Hkeep|Himg];
          [| apply Hfr; right; left;
             cbn [kentry_ok] in HKK;
             lazymatch type of HKK with
             | _ /\ flat _ _ _ /\ _ => destruct HKK as (Hw8' & Hfl0 & Hrest0)
             | flat _ _ _ /\ _ => destruct HKK as [Hfl0 Hrest0]
             end;
             destruct Hfl0 as (G1 & G2 & G3 & G4);
             eapply (img_lit_x_sound E M k b o _ x HK Himg); [lia | lia |];
             rewrite ?APS.elenZ_lit by lia; exact Hx ]).
    all: (apply orb_prop in Hkeep as [Hkeep|Habv];
          [ apply andb_prop in Hkeep as [Hkeep Hape]; apply andb_prop in Hkeep as [Hown Hap]; apply Hfr; left   (* [comment removed for export] *)
          | apply Hfr; right; right; left;
            pose proof (above_x_sound E M k top sp _ _ _ x HK Habv Htop) as AB;
            rewrite !estart_SA in AB, Hx; unfold elenZ in AB, Hx; cbn [edenot] in AB, Hx;
            rewrite ?(u64_lit (Z.of_nat w)) in AB by lia; exact (AB Hx) ]).
    all: pose proof (ranges_apart_x_sound SEGS E M k _ _ _ spb (spk - stk) (ELit stk) HK Hap) as Hd.
    all: (rewrite !estart_SA in Hd; rewrite !estart_SA in Hx; unfold elenZ in Hd, Hx; cbn [edenot] in Hd, Hx;
          rewrite (u64_lit stk) in Hd by lia; rewrite ?(u64_lit (Z.of_nat w)) in Hd by lia; rewrite Hspd).
    all: (pose proof (u64_range (edenot E spb)); pose proof (u64_range x)).
    all: (split; [ eapply owned_x_sound; [exact HK | exact Hflat | exact Hperm | exact Htop | exact Hceil | exact Hown |]; rewrite !estart_SA; unfold elenZ; cbn [edenot]; rewrite ?u64_lit by lia; lia |]).
    all: (split; [| eapply (errno_apart_x_sound E M k _ _ _ x HK Hape); rewrite !estart_SA; unfold elenZ; cbn [edenot]; rewrite ?u64_lit by lia; lia ]).   (* [comment removed for export] *)
    all: intros [HA HB]; rewrite u64_lit in HA, HB by lia; lia.
Qed.


End KnowLib.
