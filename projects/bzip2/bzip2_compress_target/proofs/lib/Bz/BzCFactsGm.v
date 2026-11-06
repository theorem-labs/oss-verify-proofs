(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzArrD BzCMem BzCStream BzCState BzCMtf BzCRebuildF.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams BzParamsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gm_facts (e : est) : Prop :=
  zbok (e_arr1 e) /\ zbok (e_arr2 e) /\ 1 <= e_nblock e <= NBLOCKMAX + 9 /\
  zdefr (e_inUse e) 0 256 /\ (forall i, 0 <= i < 256 -> zget (e_inUse e) i = 0 \/ zget (e_inUse e) i = 1) /\
  (forall j, 0 <= j < e_nblock e -> zget (e_inUse e) (rd8 (e_arr2 e) j) = 1) /\
  (forall i, 0 <= i < e_nblock e -> 0 <= rd32 (e_arr1 e) i < e_nblock e).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zfill0_get : forall n a i x, zget (zfill0 n a i) x = (if (i <=? x) && (x <? i + Z.of_nat n) then 0 else zget a x).
Proof.
  induction n as [|n IH]; intros a i x; cbn [zfill0].
  - destruct (Z.leb_spec i x), (Z.ltb_spec x (i + Z.of_nat 0)); cbn [andb]; try reflexivity; lia.
  - rewrite IH, zget_zset. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    destruct (Z.leb_spec (i + 1) x), (Z.ltb_spec x (i + 1 + Z.of_nat n)), (Z.eqb_spec x i), (Z.leb_spec i x), (Z.ltb_spec x (i + (Z.of_nat n + 1))); cbn [andb]; try reflexivity; lia.
Qed.
Lemma zfill0_def : forall n a i x, zdef (zfill0 n a i) x = (((i <=? x) && (x <? i + Z.of_nat n)) || zdef a x)%bool.
Proof.
  induction n as [|n IH]; intros a i x; cbn [zfill0].
  - destruct (Z.leb_spec i x), (Z.ltb_spec x (i + Z.of_nat 0)); cbn [andb orb]; try reflexivity; lia.
  - rewrite IH, zdef_zset. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    destruct (Z.leb_spec (i + 1) x), (Z.ltb_spec x (i + 1 + Z.of_nat n)), (Z.eqb_spec x i), (Z.leb_spec i x), (Z.ltb_spec x (i + (Z.of_nat n + 1))), (zdef a x); cbn [andb orb]; try reflexivity; lia.
Qed.
Lemma yy_init_get : forall n a i x, zget (yy_init n a i) x = (if (i <=? x) && (x <? i + Z.of_nat n) then x else zget a x).
Proof.
  induction n as [|n IH]; intros a i x; cbn [yy_init].
  - destruct (Z.leb_spec i x), (Z.ltb_spec x (i + Z.of_nat 0)); cbn [andb]; try reflexivity; lia.
  - rewrite IH, zget_zset. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    destruct (Z.leb_spec (i + 1) x), (Z.ltb_spec x (i + 1 + Z.of_nat n)), (Z.eqb_spec x i), (Z.leb_spec i x), (Z.ltb_spec x (i + (Z.of_nat n + 1))); cbn [andb]; try reflexivity; lia.
Qed.
Lemma yy_init_def : forall n a i x, zdef (yy_init n a i) x = (((i <=? x) && (x <? i + Z.of_nat n)) || zdef a x)%bool.
Proof.
  induction n as [|n IH]; intros a i x; cbn [yy_init].
  - destruct (Z.leb_spec i x), (Z.ltb_spec x (i + Z.of_nat 0)); cbn [andb orb]; try reflexivity; lia.
  - rewrite IH, zdef_zset. replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    destruct (Z.leb_spec (i + 1) x), (Z.ltb_spec x (i + 1 + Z.of_nat n)), (Z.eqb_spec x i), (Z.leb_spec i x), (Z.ltb_spec x (i + (Z.of_nat n + 1))), (zdef a x); cbn [andb orb]; try reflexivity; lia.
Qed.
Lemma zfill0_S : forall n a i, zfill0 (S n) a i = zfill0 n (zset a i 0) (i + 1). Proof. reflexivity. Qed.
Lemma yy_init_S : forall n a i, yy_init (S n) a i = yy_init n (zset a i i) (i + 1). Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mk_maps_S : forall n inUse unseq i k,
  mk_maps (S n) inUse unseq i k =
  (if negb (zget inUse i =? 0) then mk_maps n inUse (zset unseq i k) (i + 1) (k + 1) else mk_maps n inUse unseq (i + 1) k).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint cntU (n : nat) (inUse : zarr) (i : Z) : Z :=
  match n with O => 0 | S n' => (if zget inUse i =? 0 then 0 else 1) + cntU n' inUse (i + 1) end.
Lemma cntU_S : forall n inUse i, cntU (S n) inUse i = (if zget inUse i =? 0 then 0 else 1) + cntU n inUse (i + 1).
Proof. reflexivity. Qed.
Lemma cntU_range : forall n inUse i, 0 <= cntU n inUse i <= Z.of_nat n.
Proof. induction n as [|n IH]; intros inUse i; cbn [cntU]; [lia|]. pose proof (IH inUse (i + 1)). destruct (zget inUse i =? 0); lia. Qed.
Lemma cntU_split : forall n1 n2 inUse i, cntU (n1 + n2) inUse i = cntU n1 inUse i + cntU n2 inUse (i + Z.of_nat n1).
Proof.
  induction n1 as [|n1 IH]; intros n2 inUse i; cbn [cntU Nat.add].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH. replace (i + 1 + Z.of_nat n1) with (i + Z.of_nat (S n1)) by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma mk_maps_spec : forall n inUse unseq i k,
  snd (mk_maps n inUse unseq i k) = k + cntU n inUse i /\
  (forall x, i <= x < i + Z.of_nat n -> zget inUse x <> 0 ->
     zdef (fst (mk_maps n inUse unseq i k)) x = true /\ zget (fst (mk_maps n inUse unseq i k)) x = k + cntU (Z.to_nat (x - i)) inUse i) /\
  (forall x, (x < i \/ i + Z.of_nat n <= x \/ zget inUse x = 0) ->
     zdef (fst (mk_maps n inUse unseq i k)) x = zdef unseq x /\ zget (fst (mk_maps n inUse unseq i k)) x = zget unseq x).
Proof.
  induction n as [|n IH]; intros inUse unseq i k.
  - cbn. split; [lia|]. split; [intros; lia| intros; split; reflexivity].
  - rewrite mk_maps_S. cbn [cntU]. destruct (Z.eqb_spec (zget inUse i) 0) as [Z0|NZ]; cbn [negb].
    + cps_destruct (IH inUse unseq (i + 1) k) as (A & B & C). split; [rewrite A; lia|]. split.
      * intros x Hx Ux. assert (x <> i) by congruence.
        destruct (B x ltac:(lia) Ux) as [D V]. split; [exact D|]. rewrite V.
        replace (Z.to_nat (x - i)) with (S (Z.to_nat (x - (i + 1)))) by lia. cbn [cntU]. rewrite (proj2 (Z.eqb_eq _ _) Z0). lia.
      * intros x Hx. apply C. lia.
    + cps_destruct (IH inUse (zset unseq i k) (i + 1) (k + 1)) as (A & B & C). split; [rewrite A; lia|]. split.
      * intros x Hx Ux. destruct (Z.eq_dec x i) as [->|NE].
        -- destruct (C i ltac:(lia)) as [D V]. rewrite D, V, zdef_zset_same, zget_zset_same.
           replace (Z.to_nat (i - i)) with 0%nat by lia. cbn [cntU]. split; [reflexivity| lia].
        -- destruct (B x ltac:(lia) Ux) as [D V]. split; [exact D|]. rewrite V.
           replace (Z.to_nat (x - i)) with (S (Z.to_nat (x - (i + 1)))) by lia. cbn [cntU].
           replace (zget inUse i =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). lia.
      * intros x Hx. destruct (C x ltac:(lia)) as [D V]. rewrite D, V, zdef_zset, zget_zset.
        destruct (Z.eqb_spec x i); [subst; lia| split; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pts.
  Variable e : est.
  Definition gp_maps : zarr * Z := mk_maps 256 (e_inUse e) (e_unseqToSeq e) 0 0.
  Definition gp_unseq : zarr := fst gp_maps.
  Definition gp_nInUse : Z := snd gp_maps.
  Definition gp_EOB : Z := gp_nInUse + 1.
  Definition gp_mtf0 : zarr := zfill0 (Z.to_nat (gp_EOB + 1)) (e_mtfFreq e) 0.
  Definition gp_yy0 : zarr := yy_init (Z.to_nat gp_nInUse) znew 0.
  Definition gp_s0 : gms := GMS (e_arr1 e) gp_mtf0 gp_yy0 0 0.
  (* [comment removed for export] *)
  Definition gp_st (i : nat) : gms := gm_loop i (e_arr2 e) gp_unseq (e_nblock e) 0 gp_s0.
  (* [comment removed for export] *)
  Definition gp_fin (s : gms) : zarr * zarr * Z :=
    let '(arr1, mtfFreq, wr) :=
      (if 0 <? gm_zPend s then mtf_zrun 64%nat (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1)
       else (gm_arr1 s, gm_mtfFreq s, gm_wr s)) in
    mtf_emit arr1 mtfFreq wr gp_EOB.
End Pts.
Lemma gp_EOB_eq : forall e, gp_EOB e = gp_nInUse e + 1. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition gm_j (nblock : Z) (s : gms) (i : Z) : Z :=
  let j := rd32 (gm_arr1 s) i - 1 in if j <? 0 then j + nblock else j.
Lemma gm_iter_same : forall arr2 unseq nblock i s,
  zget (gm_yy s) 0 = zget unseq (rd8 arr2 (gm_j nblock s i)) ->
  gm_iter arr2 unseq nblock i s = GMS (gm_arr1 s) (gm_mtfFreq s) (gm_yy s) (gm_wr s) (gm_zPend s + 1).
Proof. intros arr2 unseq nblock i s E. unfold gm_iter, gm_j in *. cbv zeta. rewrite (proj2 (Z.eqb_eq _ _) E). reflexivity. Qed.
Lemma gm_iter_new : forall arr2 unseq nblock i s arr1a mfa wra Y' p',
  let ll := zget unseq (rd8 arr2 (gm_j nblock s i)) in
  zget (gm_yy s) 0 <> ll ->
  (if 0 <? gm_zPend s then mtf_zrun 64%nat (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1)
   else (gm_arr1 s, gm_mtfFreq s, gm_wr s)) = (arr1a, mfa, wra) ->
  mtf_search 258%nat (zset (gm_yy s) 1 (zget (gm_yy s) 0)) ll (zget (gm_yy s) 1) 1 = (Y', ll, p') ->
  gm_iter arr2 unseq nblock i s = GMS (wr16 arr1a (2 * wra) (p' + 1)) (zincr mfa (p' + 1)) (zset Y' 0 ll) (wra + 1) 0.
Proof.
  intros arr2 unseq nblock i s arr1a mfa wra Y' p' ll NE E1 E2. unfold gm_iter. unfold gm_j in *. cbv zeta. subst ll.
  rewrite (proj2 (Z.eqb_neq _ _) NE). rewrite E1, E2. reflexivity.
Qed.

Lemma gm_loop_snoc : forall n arr2 unseq nblock i s,
  gm_loop (S n) arr2 unseq nblock i s = gm_iter arr2 unseq nblock (i + Z.of_nat n) (gm_loop n arr2 unseq nblock i s).
Proof.
  induction n as [|n IH]; intros arr2 unseq nblock i s.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - transitivity (gm_loop (S n) arr2 unseq nblock (i + 1) (gm_iter arr2 unseq nblock i s)); [reflexivity|].
    rewrite IH. cbn [gm_loop]. f_equal; lia.
Qed.
Lemma gp_st_S : forall e i, gp_st e (S i) = gm_iter (e_arr2 e) (gp_unseq e) (e_nblock e) (Z.of_nat i) (gp_st e i).
Proof. intros. unfold gp_st. rewrite gm_loop_snoc. f_equal; lia. Qed.
Lemma gp_st_0 : forall e, gp_st e 0 = gp_s0 e. Proof. reflexivity. Qed.

Lemma generateMTFValues_eq : forall e,
  generateMTFValues e znew =
  (let '(arr1, mtfFreq, wr) := gp_fin e (gp_st e (Z.to_nat (e_nblock e))) in
   (EST (e_mode e) (e_state e) (e_avail_in_expect e) arr1 (e_arr2 e) (e_ftab e) (e_origPtr e)
        (e_state_in_ch e) (e_state_in_len e) (e_nblock e) (e_state_out_pos e) (gp_nInUse e) (e_inUse e) (gp_unseq e)
        (e_bw e) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e) wr mtfFreq (e_selector e) (e_selectorMtf e)
        (e_len e) (e_code e) (e_rfreq e) (e_len_pack e),
    gm_yy (gp_st e (Z.to_nat (e_nblock e))))).
Proof.
  intros e. unfold generateMTFValues, gp_fin, gp_st, gp_s0, gp_mtf0, gp_yy0, gp_EOB, gp_nInUse, gp_unseq, gp_maps.
  destruct (mk_maps 256 (e_inUse e) (e_unseqToSeq e) 0 0) as [unseq nInUse]. cbn [fst snd].
  set (s := gm_loop _ _ _ _ _ _). clearbody s. destruct (if 0 <? gm_zPend s then _ else _) as [[arr1 mf] wr]. cbv beta iota zeta in *. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zget_wr16_other : forall a o v k, (k < o \/ o + 1 < k) -> zget (wr16 a o v) k = zget a k.
Proof. intros a o v k H. unfold wr16. rewrite !zget_zset_other by lia. reflexivity. Qed.

Lemma mtf_zrun_S : forall f arr1 mf wr z,
  mtf_zrun (S f) arr1 mf wr z =
  (let '(arr1', mf', wr') := mtf_emit arr1 mf wr (if Z.land z 1 =? 0 then BZ_RUNA else BZ_RUNB) in
   if z <? 2 then (arr1', mf', wr') else mtf_zrun f arr1' mf' wr' ((z - 2) / 2)).
Proof. reflexivity. Qed.
Lemma mtf_search_S : forall f Y ll rtmp p,
  mtf_search (S f) Y ll rtmp p =
  (if ll =? rtmp then (Y, rtmp, p) else mtf_search f (zset Y (p + 1) rtmp) ll (zget Y (p + 1)) (p + 1)).
Proof. reflexivity. Qed.

Lemma mtf_search_stop : forall f Y ll rtmp p, ll = rtmp -> mtf_search f Y ll rtmp p = (Y, rtmp, p).
Proof. intros [|f] Y ll rtmp p E; [reflexivity|]. rewrite mtf_search_S. rewrite (proj2 (Z.eqb_eq _ _) E). reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint zr_cnt (f : nat) (z : Z) : Z :=
  match f with O => 0 | S f' => if z <? 2 then 1 else 1 + zr_cnt f' ((z - 2) / 2) end.
Lemma zr_cnt_S : forall f z, zr_cnt (S f) z = (if z <? 2 then 1 else 1 + zr_cnt f ((z - 2) / 2)). Proof. reflexivity. Qed.
Lemma zr_cnt_bound : forall f z, 0 <= z -> 0 <= zr_cnt f z <= z + 1.
Proof.
  induction f as [|f IH]; intros z Hz; cbn [zr_cnt]; [lia|].
  destruct (Z.ltb_spec z 2); [lia|]. pose proof (IH ((z - 2) / 2) ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed.

Section Inv.
  Variable e : est.
  Hypothesis GF : gm_facts e.
  Notation nb := (e_nblock e). Notation nInUse := (gp_nInUse e). Notation unseq := (gp_unseq e). Notation EOB := (gp_EOB e).


  (* [comment removed for export] *)
  Lemma maps_facts :
    1 <= nInUse <= 256 /\
    (forall b, 0 <= b < 256 -> zget (e_inUse e) b <> 0 -> zdef unseq b = true /\ 0 <= zget unseq b < nInUse) /\
    (forall j, 0 <= j < nb -> zdef unseq (rd8 (e_arr2 e) j) = true /\ 0 <= zget unseq (rd8 (e_arr2 e) j) < nInUse).
  Proof.
    cps_destruct GF as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1).
    cps_destruct (mk_maps_spec 256 (e_inUse e) (e_unseqToSeq e) 0 0) as (A & B & C).
    unfold gp_nInUse, gp_unseq, gp_maps. set (MM := mk_maps 256 (e_inUse e) (e_unseqToSeq e) 0 0) in *.
    assert (U : forall b, 0 <= b < 256 -> zget (e_inUse e) b <> 0 -> zdef (fst MM) b = true /\ 0 <= zget (fst MM) b < snd MM).
    { intros b Hb Ub. destruct (B b ltac:(lia) Ub) as [D V]. split; [exact D|]. rewrite V, A. rewrite Z.sub_0_r.
      pose proof (cntU_range (Z.to_nat b) (e_inUse e) 0).
      pose proof (cntU_split (Z.to_nat b) (256 - Z.to_nat b) (e_inUse e) 0) as SP. replace (Z.to_nat b + (256 - Z.to_nat b))%nat with 256%nat in SP by lia.
      assert (1 <= cntU (256 - Z.to_nat b) (e_inUse e) (0 + Z.of_nat (Z.to_nat b))).
      { replace (256 - Z.to_nat b)%nat with (S (255 - Z.to_nat b)) by lia. rewrite cntU_S. replace (0 + Z.of_nat (Z.to_nat b)) with b by lia.
        replace (zget (e_inUse e) b =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ub).
        pose proof (cntU_range (255 - Z.to_nat b) (e_inUse e) (b + 1)). lia. }
      lia. }
    split; [|split; [exact U|]].
    - rewrite A. pose proof (cntU_range 256 (e_inUse e) 0). split; [|lia].
      pose proof (F5 0 ltac:(lia)) as F0. pose proof (BOK2 0) as R0. unfold rd8 in F0.
      destruct (U (zget (e_arr2 e) 0) R0 ltac:(rewrite F0; lia)). lia.
    - intros j Hj. apply U; [apply BOK2|]. rewrite (F5 j Hj). lia.
  Qed.
  (* [comment removed for export] *)
  #[local] Opaque gp_maps gp_nInUse gp_unseq gp_EOB.
  Let EE : gp_EOB e = gp_nInUse e + 1 := gp_EOB_eq e.

  Definition yperm (yy : zarr) : Prop :=
    (forall p, 0 <= p < nInUse -> zdef yy p = true /\ 0 <= zget yy p < nInUse) /\
    (forall v, 0 <= v < nInUse -> exists p, 0 <= p < nInUse /\ zget yy p = v).

  Definition GI (i : Z) (s : gms) : Prop :=
    0 <= gm_wr s /\ 0 <= gm_zPend s /\ gm_wr s + gm_zPend s <= i /\
    yperm (gm_yy s) /\
    (forall v, 0 <= v <= EOB -> zdef (gm_mtfFreq s) v = true /\ 0 <= zget (gm_mtfFreq s) v) /\
    sumF (fun v => zget (gm_mtfFreq s) v) 0 (Z.to_nat (EOB + 1)) = gm_wr s /\
    zbok (gm_arr1 s) /\ (forall k, 2 * gm_wr s <= k -> zget (gm_arr1 s) k = zget (e_arr1 e) k) /\
    (forall k, 0 <= k < gm_wr s -> 0 <= rd16 (gm_arr1 s) (2 * k) <= EOB).

  (* [comment removed for export] *)
  Definition EMI (arr1 mf : zarr) (wr : Z) : Prop :=
    0 <= wr /\
    (forall v, 0 <= v <= EOB -> zdef mf v = true /\ 0 <= zget mf v) /\
    sumF (fun v => zget mf v) 0 (Z.to_nat (EOB + 1)) = wr /\
    zbok arr1 /\ (forall k, 2 * wr <= k -> zget arr1 k = zget (e_arr1 e) k) /\
    (forall k, 0 <= k < wr -> 0 <= rd16 arr1 (2 * k) <= EOB).
  Lemma emit_ok : forall arr1 mf wr v, EMI arr1 mf wr -> 0 <= v <= EOB ->
    let '(arr1', mf', wr') := mtf_emit arr1 mf wr v in wr' = wr + 1 /\ EMI arr1' mf' wr'.
  Proof.
    (intros arr1 mf wr v; cps_intros (W0 & MD & SM & BOK & FR & MV); intros Hv). unfold mtf_emit. split; [reflexivity|].
    pose proof (proj1 maps_facts) as NI. pose proof EE as EE'.
    split; [lia|]. split.
    { intros u Hu. rewrite zdef_zincr, zget_zincr. destruct (Z.eqb_spec u v); cbv [orb]; [subst u; destruct (MD v Hv); split; [reflexivity| lia]| apply MD; exact Hu]. }
    split.
    { rewrite (sumF_upd (Z.to_nat (gp_EOB e + 1)) (fun u => zget mf u) (fun u => zget (zincr mf v) u) 0 v 1); [lia| lia|].
      intros x. rewrite zget_zincr. destruct (Z.eqb_spec x v); [subst x; reflexivity| reflexivity]. }
    split; [apply zbok_wr16; exact BOK|]. split.
    { intros k Hk. rewrite zget_wr16_other by lia. apply FR. lia. }
    intros k Hk. destruct (Z.eq_dec k wr) as [->|NE].
    - rewrite rd16_wr16_same by lia. lia.
    - rewrite rd16_wr16_other by lia. apply MV. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma zrun_ok : forall f arr1 mf wr z, EMI arr1 mf wr -> 0 <= z ->
    let '(arr1', mf', wr') := mtf_zrun f arr1 mf wr z in wr' = wr + zr_cnt f z /\ EMI arr1' mf' wr'.
  Proof.
    induction f as [|f IH]; intros arr1 mf wr z EM Hz.
    - cbv [mtf_zrun zr_cnt]. split; [lia| exact EM].
    - rewrite mtf_zrun_S, zr_cnt_S. pose proof (proj1 maps_facts) as NI.
      pose proof (emit_ok arr1 mf wr (if Z.land z 1 =? 0 then BZ_RUNA else BZ_RUNB) EM ltac:(unfold BZ_RUNA, BZ_RUNB; pose proof EE; destruct (Z.land z 1 =? 0); lia)) as EO.
      destruct (mtf_emit arr1 mf wr _) as [[arr1' mf'] wr']. cbv beta iota zeta in *. destruct EO as [-> EM'].
      destruct (Z.ltb_spec z 2); [split; [lia| exact EM']|].
      specialize (IH arr1' mf' (wr + 1) ((z - 2) / 2) EM' ltac:(Z.div_mod_to_equations; lia)).
      destruct (mtf_zrun f arr1' mf' (wr + 1) ((z - 2) / 2)) as [[arr1'' mf''] wr'']. cbv beta iota zeta in *. destruct IH as [-> EM'']. split; [lia| exact EM''].
  Qed.

  (* [comment removed for export] *)
  Lemma search_ok : forall f Y ll rtmp p yy,
    yperm yy -> 0 <= ll < nInUse -> 1 <= p ->
    (* [comment removed for export] *)
    (forall k, 1 <= k <= p -> zget Y k = zget yy (k - 1) /\ zdef Y k = true) ->
    (forall k, p < k -> zget Y k = zget yy k /\ zdef Y k = zdef yy k) ->
    rtmp = zget yy p -> p < nInUse ->
    (forall k, 1 <= k < p -> zget yy k <> ll) -> zget yy 0 <> ll ->
    (Z.to_nat (nInUse - p) <= f)%nat ->
    let '(Y', rtmp', p') := mtf_search f Y ll rtmp p in
    rtmp' = ll /\ p <= p' < nInUse /\ zget yy p' = ll /\
    (forall k, 1 <= k <= p' -> zget Y' k = zget yy (k - 1) /\ zdef Y' k = true) /\
    (forall k, p' < k -> zget Y' k = zget yy k /\ zdef Y' k = zdef yy k).
  Proof.
    induction f as [|f IH]; intros Y ll rtmp p yy YP Hll Hp SH AB RT PN NB N0 FU.
    - exfalso. lia.
    - rewrite mtf_search_S. destruct (Z.eqb_spec ll rtmp) as [EQ|NE].
      + split; [congruence|]. split; [lia|]. split; [congruence|]. split; [exact SH| exact AB].
      + (* [comment removed for export] *)
        destruct YP as [YR YS]. cps_destruct (YS ll Hll) as (p0 & Hp0 & Ep0).
        assert (P0 : p < p0). { destruct (Z_lt_le_dec p p0); [lia|]. exfalso. destruct (Z.eq_dec p0 0) as [->|]; [congruence|].
          destruct (Z.eq_dec p0 p) as [->|]; [congruence|]. apply (NB p0); lia. }
        destruct (AB (p + 1) ltac:(lia)) as [G1 D1].
        unshelve epose proof (IH (zset Y (p + 1) rtmp) ll (zget Y (p + 1)) (p + 1) yy (conj YR YS) Hll ltac:(lia) _ _ _ _ _ _ _) as IH'.
        * intros k Hk. rewrite zget_zset, zdef_zset. destruct (Z.eqb_spec k (p + 1)) as [->|NK]; cbv [orb].
          -- split; [rewrite RT; f_equal; lia| reflexivity].
          -- apply SH. lia.
        * intros k Hk. rewrite zget_zset_other, zdef_zset_other by lia. apply AB. lia.
        * rewrite G1. reflexivity.
        * lia.
        * intros k Hk. destruct (Z.eq_dec k p) as [->|]; [congruence| apply NB; lia].
        * exact N0.
        * lia.
        * clear IH. destruct (mtf_search f (zset Y (p + 1) rtmp) ll (zget Y (p + 1)) (p + 1)) as [[Y' rtmp'] p']. cbv beta iota zeta in *.
          cps_destruct IH' as (R1 & R2 & R3 & R4 & R5).
          split; [exact R1|]. split; [lia|]. split; [exact R3|]. split; [exact R4| exact R5].
  Qed.

  (* [comment removed for export] *)
  Lemma gm_iter_GI : forall i s, 0 <= i < nb -> GI i s -> GI (i + 1) (gm_iter (e_arr2 e) unseq nb i s).
  Proof.
    (intros i s Hi; cps_intros (W0 & Z0 & WZ & YP & MD & SM & BOK & FR & MV)).
    cps_destruct GF as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1).
    cps_destruct maps_facts as (NI & UB & UJ).
    unfold gm_iter. cbv zeta.
    (* [comment removed for export] *)
    assert (PTR : rd32 (gm_arr1 s) i = rd32 (e_arr1 e) i).
    { unfold rd32. rewrite !FR by lia. reflexivity. }
    rewrite !PTR. pose proof (M1 i Hi) as PR.
    set (j0 := rd32 (e_arr1 e) i - 1).
    set (j := if j0 <? 0 then j0 + nb else j0).
    assert (Hj : 0 <= j < nb) by (subst j j0; destruct (Z.ltb_spec (rd32 (e_arr1 e) i - 1) 0); lia).
    destruct (UJ j Hj) as [DU RU]. set (ll := zget unseq (rd8 (e_arr2 e) j)) in *.
    destruct (Z.eqb_spec (zget (gm_yy s) 0) ll) as [EQ|NE].
    - (* [comment removed for export] *)
      split; [cbn [gm_wr gm_zPend]; lia|]. split; [cbn [gm_wr gm_zPend]; lia|]. split; [cbn [gm_wr gm_zPend]; lia|]. split; [exact YP|]. split; [exact MD|]. split; [exact SM|].
      split; [exact BOK|]. split; [exact FR| exact MV].
    - (* [comment removed for export] *)
      assert (EM0 : EMI (gm_arr1 s) (gm_mtfFreq s) (gm_wr s)) by (repeat (split; [assumption|]); assumption).
      assert (ZR : let '(arr1, mtfFreq, wr) := (if 0 <? gm_zPend s then mtf_zrun 64 (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1)
                                                 else (gm_arr1 s, gm_mtfFreq s, gm_wr s)) in
                   gm_wr s <= wr <= gm_wr s + gm_zPend s /\ EMI arr1 mtfFreq wr).
      { destruct (Z.ltb_spec 0 (gm_zPend s)).
        - pose proof (zrun_ok 64 (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1) EM0 ltac:(lia)) as ZO.
          destruct (mtf_zrun 64 _ _ _ _) as [[a1 mf1] wr1]. cbv beta iota zeta in *. destruct ZO as [-> EM1].
          pose proof (zr_cnt_bound 64 (gm_zPend s - 1) ltac:(lia)). split; [lia| exact EM1].
        - split; [lia| exact EM0]. }
      destruct (if 0 <? gm_zPend s then _ else _) as [[arr1 mf] wr]. cbv beta iota zeta in *. destruct ZR as [WR EM1].
      (* [comment removed for export] *)
      destruct YP as [YR YS].
      pose proof (search_ok 258 (zset (gm_yy s) 1 (zget (gm_yy s) 0)) ll (zget (gm_yy s) 1) 1 (gm_yy s) (conj YR YS) RU ltac:(lia)) as SO.
      assert (N1 : 1 < nInUse). { cps_destruct (YS ll RU) as (p0 & Hp0 & Ep0). destruct (Z.eq_dec p0 0) as [->|]; [congruence| lia]. }
      specialize (SO ltac:(intros k Hk; replace k with 1 by lia; rewrite zget_zset_same, zdef_zset_same; replace (1 - 1) with 0 by lia; split; reflexivity)
                     ltac:(intros k Hk; rewrite zget_zset_other, zdef_zset_other by lia; split; reflexivity) eq_refl N1 ltac:(intros; lia) NE ltac:(lia)).
      destruct (mtf_search 258 _ _ _ _) as [[Y' rtmp'] p']. cbv beta iota zeta in *. cps_destruct SO as (R1 & R2 & R3 & R4 & R5).
      pose proof (emit_ok arr1 mf wr (p' + 1) EM1 ltac:(pose proof EE; lia)) as EO.
      destruct (mtf_emit arr1 mf wr (p' + 1)) as [[arr1' mf'] wr']. cbv beta iota zeta in *. destruct EO as [-> (E1 & E2 & E3 & E4 & E5 & E6)].
      unfold GI. cbn [gm_wr gm_zPend gm_yy gm_mtfFreq gm_arr1].
      split; [lia|]. split; [lia|]. split; [lia|]. split.
      { (* [comment removed for export] *)
        split.
        - intros q Hq. rewrite zget_zset, zdef_zset. destruct (Z.eqb_spec q 0) as [->|NQ]; cbv [orb].
          + rewrite R1. split; [reflexivity| lia].
          + destruct (Z_lt_le_dec p' q).
            * destruct (R5 q ltac:(lia)) as [-> ->]. apply YR. lia.
            * destruct (R4 q ltac:(lia)) as [-> ->]. split; [reflexivity|]. apply YR. lia.
        - intros v Hv. cps_destruct (YS v Hv) as (q & Hq & Eq).
          destruct (Z.eq_dec q p') as [->|NQ].
          + exists 0. rewrite zget_zset_same. split; [lia| congruence].
          + destruct (Z_lt_le_dec p' q).
            * exists q. rewrite zget_zset_other by lia. destruct (R5 q ltac:(lia)) as [-> _]. split; [lia| exact Eq].
            * exists (q + 1). rewrite zget_zset_other by lia. destruct (R4 (q + 1) ltac:(lia)) as [-> _].
              replace (q + 1 - 1) with q by lia. split; [lia| exact Eq]. }
      split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5| exact E6].
  Qed.

  Lemma gp_s0_GI : GI 0 (gp_s0 e).
  Proof.
    cps_destruct GF as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1). cps_destruct maps_facts as (NI & UB & UJ).
    unfold GI, gp_s0. cbn [gm_wr gm_zPend gm_yy gm_mtfFreq gm_arr1].
    split; [lia|]. split; [lia|]. split; [lia|]. split.
    { unfold yperm, gp_yy0. split.
      - intros p Hp. rewrite yy_init_def, yy_init_get.
        replace ((0 <=? p) && (p <? 0 + Z.of_nat (Z.to_nat nInUse)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
        split; [reflexivity| lia].
      - intros v Hv. exists v. rewrite yy_init_get.
        replace ((0 <=? v) && (v <? 0 + Z.of_nat (Z.to_nat nInUse)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
        split; [lia| reflexivity]. }
    split.
    { intros v Hv. unfold gp_mtf0. pose proof EE. rewrite zfill0_def, zfill0_get.
      replace ((0 <=? v) && (v <? 0 + Z.of_nat (Z.to_nat (EOB + 1))))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
      split; [reflexivity| lia]. }
    split.
    { unfold gp_mtf0. pose proof EE. rewrite (sumF_ext _ _ (fun _ => 0)).
      - assert (G : forall n j, sumF (fun _ : Z => 0) j n = 0) by (induction n as [|n0 IH0]; intros; cbn [sumF]; [reflexivity| rewrite IH0; lia]).
        apply G.
      - intros b Hb. rewrite zfill0_get.
        replace ((0 <=? b) && (b <? 0 + Z.of_nat (Z.to_nat (EOB + 1))))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
        reflexivity. }
    split; [exact BOK1|]. split; [intros; reflexivity| intros; lia].
  Qed.

  Lemma gp_st_GI : forall i, (Z.of_nat i <= nb) -> GI (Z.of_nat i) (gp_st e i).
  Proof.
    induction i as [|i IH]; intros Hi.
    - rewrite gp_st_0. exact gp_s0_GI.
    - rewrite gp_st_S. replace (Z.of_nat (S i)) with (Z.of_nat i + 1) by lia. apply gm_iter_GI; [lia|]. apply IH. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma gp_fin_ok : let s := gp_st e (Z.to_nat nb) in
    let '(arr1', mf', wr') := gp_fin e s in
    GI nb s /\ gm_wr s + 1 <= wr' <= nb + 1 /\ EMI arr1' mf' wr' /\ 1 <= zget mf' EOB.
  Proof.
    cps_destruct GF as (BOK1 & BOK2 & NB & DEFI & IU01 & F5 & M1). pose proof (proj1 maps_facts) as NI.
    cbv zeta. pose proof (gp_st_GI (Z.to_nat nb) ltac:(lia)) as G. replace (Z.of_nat (Z.to_nat nb)) with nb in G by lia.
    set (s := gp_st e (Z.to_nat nb)) in *. unfold gp_fin.
    cps_destruct G as (W0 & Z0 & WZ & YP & MD & SM & BOK & FR & MV).
    assert (EM0 : EMI (gm_arr1 s) (gm_mtfFreq s) (gm_wr s)) by (repeat (split; [assumption|]); assumption).
    assert (ZR : let '(arr1, mtfFreq, wr) := (if 0 <? gm_zPend s then mtf_zrun 64 (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1)
                                               else (gm_arr1 s, gm_mtfFreq s, gm_wr s)) in
                 gm_wr s <= wr <= gm_wr s + gm_zPend s /\ EMI arr1 mtfFreq wr).
    { destruct (Z.ltb_spec 0 (gm_zPend s)).
      - pose proof (zrun_ok 64 (gm_arr1 s) (gm_mtfFreq s) (gm_wr s) (gm_zPend s - 1) EM0 ltac:(lia)) as ZO.
        destruct (mtf_zrun 64 _ _ _ _) as [[a1 mf1] wr1]. cbv beta iota zeta in *. destruct ZO as [-> EM1].
        pose proof (zr_cnt_bound 64 (gm_zPend s - 1) ltac:(lia)). split; [lia| exact EM1].
      - split; [lia| exact EM0]. }
    destruct (if 0 <? gm_zPend s then _ else _) as [[arr1 mf] wr]. cbv beta iota zeta in *. destruct ZR as [WR EM1].
    pose proof (emit_ok arr1 mf wr EOB EM1 ltac:(pose proof EE; lia)) as EO.
    unfold mtf_emit in *. destruct EO as [_ EM2].
    split; [repeat (split; [assumption|]); assumption|]. split; [lia|]. split; [exact EM2|].
    rewrite zget_zincr, Z.eqb_refl. cps_destruct EM1 as (_ & MD1 & _). destruct (MD1 EOB ltac:(pose proof EE; lia)). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma EMI_get : forall arr1 mf wr v, EMI arr1 mf wr -> 0 <= v <= EOB -> zdef mf v = true /\ 0 <= zget mf v <= wr.
  Proof.
    (intros arr1 mf wr v; cps_intros (W0 & MD & SM & _); intros Hv). destruct (MD v Hv) as [D R]. split; [exact D|]. split; [exact R|].
    rewrite <- SM. pose proof EE.
    apply (sumF_term_le (Z.to_nat (EOB + 1)) (fun u => zget mf u) 0 v); [|lia].
    intros b Hb. destruct (MD b ltac:(lia)). lia.
  Qed.
  Lemma GI_EMI : forall i s, GI i s -> EMI (gm_arr1 s) (gm_mtfFreq s) (gm_wr s).
  Proof. (intros i s; cps_intros (W0 & Z0 & WZ & YP & MD & SM & BOK & FR & MV)). repeat (split; [assumption|]). assumption. Qed.
End Inv.
End ACeilS1.

#[global] Opaque gp_maps gp_nInUse gp_unseq gp_EOB.
Section ACeilS2. Context {BZP : BzParams}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gm_post (e e' : est) : Prop :=
  let alphaSize := e_nInUse e' + 2 in let EOB := e_nInUse e' + 1 in
  1 <= e_nInUse e' <= 256 /\
  1 <= e_nMTF e' <= e_nblock e + 1 /\
  (forall v, 0 <= v <= EOB -> zdef (e_mtfFreq e') v = true /\ 0 <= zget (e_mtfFreq e') v) /\
  sumF (fun v => zget (e_mtfFreq e') v) 0 (Z.to_nat alphaSize) = e_nMTF e' /\
  1 <= zget (e_mtfFreq e') EOB /\
  zbok (e_arr1 e') /\ (forall k, 0 <= k < e_nMTF e' -> 0 <= rd16 (e_arr1 e') (2 * k) <= EOB) /\
  (forall b, 0 <= b < 256 -> zget (e_inUse e) b <> 0 -> zdef (e_unseqToSeq e') b = true /\ 0 <= zget (e_unseqToSeq e') b < e_nInUse e') /\
  (* [comment removed for export] *)
  e_nblock e' = e_nblock e /\ e_arr2 e' = e_arr2 e /\ e_inUse e' = e_inUse e /\ e_bw e' = e_bw e /\ e_ftab e' = e_ftab e /\
  e_origPtr e' = e_origPtr e /\ e_blockNo e' = e_blockNo e /\ e_blockCRC e' = e_blockCRC e /\ e_combinedCRC e' = e_combinedCRC e /\
  e_len e' = e_len e /\ e_code e' = e_code e /\ e_rfreq e' = e_rfreq e /\ e_len_pack e' = e_len_pack e /\
  e_selector e' = e_selector e /\ e_selectorMtf e' = e_selectorMtf e /\ e_mode e' = e_mode e /\ e_state e' = e_state e /\
  e_avail_in_expect e' = e_avail_in_expect e /\ e_state_in_ch e' = e_state_in_ch e /\ e_state_in_len e' = e_state_in_len e /\
  e_state_out_pos e' = e_state_out_pos e.

Theorem generateMTFValues_post : forall e, gm_facts e -> gm_post e (fst (generateMTFValues e znew)).
Proof.
  intros e GF. rewrite generateMTFValues_eq.
  pose proof (gp_fin_ok e GF) as FO. cbv zeta in FO.
  destruct (gp_fin e (gp_st e (Z.to_nat (e_nblock e)))) as [[arr1' mf'] wr']. cbv beta iota zeta in *. cbn [fst].
  cps_destruct FO as (G & WR & (E1 & E2 & E3 & E4 & E5 & E6) & EOBC).
  cps_destruct (maps_facts e GF) as (NI & UB & UJ). destruct G as (W0 & _).
  unfold gm_post. cbn [e_nInUse e_nMTF e_mtfFreq e_arr1 e_unseqToSeq e_nblock e_arr2 e_inUse e_bw e_ftab e_origPtr e_blockNo e_blockCRC e_combinedCRC
    e_len e_code e_rfreq e_len_pack e_selector e_selectorMtf e_mode e_state e_avail_in_expect e_state_in_ch e_state_in_len e_state_out_pos].
  pose proof (gp_EOB_eq e) as EE. rewrite EE in *.
  split; [exact NI|]. split; [lia|]. split; [exact E2|]. split; [replace (gp_nInUse e + 2) with (gp_nInUse e + 1 + 1) by lia; exact E3|].
  split; [exact EOBC|]. split; [exact E4|]. split; [exact E6|]. split; [exact UB|].
  repeat (split; [reflexivity|]). reflexivity.
Qed.

End ACeilS2.
