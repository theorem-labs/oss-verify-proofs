(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import Ledger Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState AInv ALogic1 ABudget APlace LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zone_eq_dec : forall z z' : zone, {z = z'} + {z <> z'}.
Proof. intros [a b] [c d]. destruct (Z.eq_dec a c); destruct (Z.eq_dec b d); try (right; congruence). left; congruence. Defined.

Fixpoint zremove (z : zone) (B : list zone) : list zone :=
  match B with [] => [] | b :: B' => if zone_eq_dec z b then B' else b :: zremove z B' end.

Lemma zremove_in : forall z b B, In b B -> b <> z -> In b (zremove z B).
Proof.
  intros z b B. induction B as [|c B IH]; intros Hin NE; [destruct Hin|]. cbn.
  destruct (zone_eq_dec z c) as [->|NC].
  - destruct Hin as [->|Hin]; [congruence| exact Hin].
  - destruct Hin as [->|Hin]; [left; reflexivity| right; exact (IH Hin NE)].
Qed.

Lemma zsum_in_remove : forall z B x y, In z B -> zsum_in B x y = zclamp z x y + zsum_in (zremove z B) x y.
Proof.
  intros z B x y. induction B as [|c B IH]; intros Hin; [destruct Hin|]. cbn.
  destruct (zone_eq_dec z c) as [->|NC]; [reflexivity|].
  destruct Hin as [->|Hin]; [congruence|]. cbn. rewrite (IH Hin). lia.
Qed.

Lemma zcount_remove : forall z B x y, In z B -> zcount B x y = (if zmeets_dec z x y then 1 else 0) + zcount (zremove z B) x y.
Proof.
  intros z B x y. induction B as [|c B IH]; intros Hin; [destruct Hin|]. cbn.
  destruct (zone_eq_dec z c) as [->|NC]; [reflexivity|].
  destruct Hin as [->|Hin]; [congruence|]. cbn. rewrite (IH Hin). lia.
Qed.

(* [comment removed for export] *)
Lemma zdisj_notin : forall z L, (forall z', In z' L -> zapart z z') -> fst z < snd z ->
  (forall z', In z' L -> fst z' < snd z') -> ~ In z L.
Proof.
  intros [a b] L AP NE NEL Hin. pose proof (AP _ Hin) as X. pose proof (NEL _ Hin) as Y. unfold zapart in X. cbn in *. lia.
Qed.

Lemma zsum_in_dominated : forall L B x y,
  zdisj L -> (forall z, In z L -> fst z < snd z) -> (forall z, In z L -> In z B) ->
  zsum_in L x y <= zsum_in B x y /\ zcount L x y <= zcount B x y.
Proof.
  induction L as [|z L IH]; intros B x y D NE INC.
  - cbn. split; [apply zsum_in_nonneg| apply zcount_nonneg].
  - cbn. destruct D as [AP D].
    assert (HzB : In z B) by (apply INC; left; reflexivity).
    assert (NIN : ~ In z L) by (apply zdisj_notin; [exact AP| apply NE; left; reflexivity| intros z' Hz'; apply NE; right; exact Hz']).
    destruct (IH (zremove z B) x y D ltac:(intros z' Hz'; apply NE; right; exact Hz')
                 ltac:(intros z' Hz'; apply zremove_in; [apply INC; right; exact Hz'| intros ->; exact (NIN Hz')])) as [S C].
    rewrite (zsum_in_remove z B x y HzB), (zcount_remove z B x y HzB). lia.
Qed.

(* [comment removed for export] *)
Lemma zsum_in_le_lengths : forall B x y, (forall z, In z B -> fst z <= snd z) ->
  zsum_in B x y <= fold_right (fun z acc => (snd z - fst z) + acc) 0 B.
Proof.
  induction B as [|z B IH]; intros x y NE; cbn; [lia|].
  pose proof (NE z (or_introl eq_refl)). specialize (IH x y ltac:(intros; apply NE; right; assumption)).
  unfold zclamp. destruct z as [a b]; cbn in *. lia.
Qed.
Lemma zcount_le_length : forall B x y, zcount B x y <= Z.of_nat (length B).
Proof. induction B as [|z B IH]; intros; cbn; [lia|]. specialize (IH x y). destruct (zmeets_dec z x y); lia. Qed.

(* [comment removed for export] *)
Lemma zsum_in_below : forall B x y, (forall z, In z B -> snd z <= x) -> zsum_in B x y = 0 /\ zcount B x y = 0.
Proof.
  induction B as [|z B IH]; intros x y H; cbn; [lia|].
  destruct (IH x y ltac:(intros; apply H; right; assumption)) as [S C]. rewrite S, C.
  pose proof (H z (or_introl eq_refl)). split.
  - unfold zclamp. destruct z; cbn in *; lia.
  - destruct (zmeets_dec z x y) as [M|M]; [| lia]. unfold zmeets in M. destruct z; cbn in *; lia.
Qed.

Lemma zsum_in_app : forall A B x y, zsum_in (A ++ B) x y = zsum_in A x y + zsum_in B x y.
Proof. induction A as [|z A IH]; intros; cbn; [lia|]. rewrite IH. lia. Qed.
Lemma zcount_app : forall A B x y, zcount (A ++ B) x y = zcount A x y + zcount B x y.
Proof. induction A as [|z A IH]; intros; cbn; [lia|]. rewrite IH. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zone_of (e : word * word) : zone := (Ledger.lo e, Ledger.hi e).
Definition zone_ofZ (bs : Z * Z) : zone := (fst bs, fst bs + snd bs).

Lemma zdisj_of_nooverlap : forall X, nooverlap X -> zdisj (map zone_of X).
Proof.
  induction X as [|e X IH]; intros NO; cbn; [exact I|]. destruct NO as [H NO]. split; [| exact (IH NO)].
  intros z' Hz'. apply in_map_iff in Hz' as (e' & <- & He'). pose proof (H e' He') as D.
  unfold zapart, zone_of. cbn. lia.
Qed.

Lemma zone_of_ofZ : forall e, zone_of e = zone_ofZ (bv_unsigned (fst e), bv_unsigned (snd e)).
Proof. intros [b s]. reflexivity. Qed.

Lemma zclamp_ofZ_le : forall bs x y, 0 <= snd bs -> zclamp (zone_ofZ bs) x y <= snd bs.
Proof. intros [b s] x y H. unfold zone_ofZ, zclamp. cbn in *. lia. Qed.
Lemma zsum_fog : forall fog x y, Forall (fun bs => 0 <= fst bs /\ 0 < snd bs <= 8192) fog ->
  zsum_in (map zone_ofZ fog) x y <= 8192 * Z.of_nat (length fog).
Proof.
  induction fog as [|bs fog IH]; intros x y F; [cbn; lia|]. apply Forall_cons_iff in F as [X F]. cbv beta in X.
  cbn [map zsum_in length]. rewrite Nat2Z.inj_succ. pose proof (zclamp_ofZ_le bs x y ltac:(lia)). specialize (IH x y F). lia.
Qed.

(* [comment removed for export] *)
Lemma mmap_noreserve_b_50 : mmap_noreserve_b (Z_to_bv 64 50) = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Weights.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.
  Variable A : AState.
  Hypothesis W : WF AL_pasan A.   (* [comment removed for export] *)
  Let P := a_pl A.
  Let K := kHighMemBeg.

  (* [comment removed for export] *)
  Lemma zclamp_le_len : forall b s x y, 0 <= s -> zclamp (b, b + s) x y <= s.
  Proof. intros. unfold zclamp. cbn. lia. Qed.
  Lemma zclamp_below : forall b s x y, b + s <= x -> zclamp (b, b + s) x y = 0.
  Proof. intros. unfold zclamp. cbn. lia. Qed.

  Definition fixed_maps : list (Z * Z) :=
    [ (p_b6 P, kSpaceReserve); (p_pa P, kPtrArrayReserve); (kHighShadowMapBeg, kHighShadowMapSize); (kLowShadowMapBeg, 0x10000000);
      (p_thr P, 4096); (p_ctx P, 0x10000); (p_fs P, kFakeStackBytes); (p_nodes0 P, kDepotNodesBlock);
      (p_frames0 P, kStackStoreBlockBytes); (p_itab P, 0x38e000); (p_m64k P, 0x10000);
      (p_gvec P, 4096); (p_dvec P, 4096); (p_m11 P, 4096); (p_dtls P, 4096) ].
  Lemma big_maps_split : forall sec, big_maps_ P sec = fixed_maps ++ map (fun s => (cs_map s, map_size (cs_n s))) (sr_chunks sec).
  Proof. reflexivity. Qed.

  Lemma fixed_bigmaps_weight : forall y,
    zsum_in (map zone_ofZ fixed_maps) K y <= kSpaceReserve + kPtrArrayReserve + 4096 + 0x10000 + kFakeStackBytes
        + kDepotNodesBlock + kStackStoreBlockBytes + 0x38e000 + 0x10000 + 4 * 4096
    /\ zcount (map zone_ofZ fixed_maps) K y <= 15.
  Proof.
    intros y. unfold fixed_maps. split.
    - cbn [zsum_in map]. unfold zone_ofZ. cbn [fst snd].
      pose proof (zclamp_le_len (p_b6 P) kSpaceReserve K y ltac:(unfold kSpaceReserve; lia)).
      pose proof (zclamp_le_len (p_pa P) kPtrArrayReserve K y ltac:(unfold kPtrArrayReserve; lia)).
      pose proof (zclamp_below kHighShadowMapBeg kHighShadowMapSize K y ltac:(unfold K, kHighShadowMapBeg, kHighShadowMapSize, kHighMemBeg; lia)).
      pose proof (zclamp_below kLowShadowMapBeg 0x10000000 K y ltac:(unfold K, kLowShadowMapBeg, kHighMemBeg; lia)).
      pose proof (zclamp_le_len (p_thr P) 4096 K y ltac:(lia)).
      pose proof (zclamp_le_len (p_ctx P) 0x10000 K y ltac:(lia)).
      pose proof (zclamp_le_len (p_fs P) kFakeStackBytes K y ltac:(unfold kFakeStackBytes; lia)).
      pose proof (zclamp_le_len (p_nodes0 P) kDepotNodesBlock K y ltac:(unfold kDepotNodesBlock; lia)).
      pose proof (zclamp_le_len (p_frames0 P) kStackStoreBlockBytes K y ltac:(unfold kStackStoreBlockBytes; lia)).
      pose proof (zclamp_le_len (p_itab P) 0x38e000 K y ltac:(lia)).
      pose proof (zclamp_le_len (p_m64k P) 0x10000 K y ltac:(lia)).
      pose proof (zclamp_le_len (p_gvec P) 4096 K y ltac:(lia)).
      pose proof (zclamp_le_len (p_dvec P) 4096 K y ltac:(lia)).
      pose proof (zclamp_le_len (p_m11 P) 4096 K y ltac:(lia)).
      pose proof (zclamp_le_len (p_dtls P) 4096 K y ltac:(lia)).
      lia.
    - eapply Z.le_trans; [apply zcount_le_length|]. cbn. lia.
  Qed.

  Lemma sec_maps_weight : forall y,
    zsum_in (map zone_ofZ (map (fun s => (cs_map s, map_size (cs_n s))) (sr_chunks (a_sec A)))) K y <= 2^32
    /\ zcount (map zone_ofZ (map (fun s => (cs_map s, map_size (cs_n s))) (sr_chunks (a_sec A)))) K y <= NLIVE_MAX + 4178.
  Proof.
    intros y. pose proof (wf_sec_eager A W) as [E1 _]. pose proof (wf_sec_sums A W) as [_ L2].
    destruct (wfS A W) as (_ & _ & _ & SIN & _).
    split.
    - eapply Z.le_trans; [apply zsum_in_le_lengths|].
      { intros z Hz. apply in_map_iff in Hz as (bs & <- & Hbs). apply in_map_iff in Hbs as (s & <- & Hs). cbn.
        pose proof (SIN s Hs) as (X & _). unfold kMaxPrimaryUser in X. pose proof (map_size_ge (cs_n s) ltac:(lia)). lia. }
      eapply Z.le_trans; [| exact E1]. clear. generalize (sr_chunks (a_sec A)) as ch.
      induction ch as [|c ch IH]; [cbn; lia|]. cbn [map fold_right zone_ofZ fst snd].
      change (sec_eager_ (c :: ch)) with (map_size (cs_n c) + sec_eager_ ch). lia.
    - eapply Z.le_trans; [apply zcount_le_length|]. rewrite !map_length. exact L2.
  Qed.
End Weights.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pa_reserved_eq : segments_reserved rsegs =
  [(Z_to_bv 64 0x10000, Z_to_bv 64 0x25000); (Z_to_bv 64 0x35000, Z_to_bv 64 0x73000); (Z_to_bv 64 0xa8000, Z_to_bv 64 0x2000); (Z_to_bv 64 0xaa000, Z_to_bv 64 0x560000)].
Proof.
  pose proof pa_seg_bases as (B0 & S0 & B1 & S1 & B2 & S2 & B3 & S3).
  unfold segments_reserved, rsegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments.
  cbn [map]. unfold segment_reservation. rewrite B0, S0, B1, S1, B2, S2, B3, S3. cbv zeta.
  change (page_round_down_Z 0x10000) with 0x10000. change (page_round_up_Z (0x10000 + 0x25000)) with 0x35000.
  change (page_round_down_Z 0x35000) with 0x35000. change (page_round_up_Z (0x35000 + 0x73000)) with 0xa8000.
  change (page_round_down_Z 0xa8000) with 0xa8000. change (page_round_up_Z (0xa8000 + 0x2000)) with 0xaa000.
  change (page_round_down_Z 0xaa000) with 0xaa000. change (page_round_up_Z (0xaa000 + 0x560000)) with 0x60a000.
  reflexivity.
Qed.
Lemma pa_reserved_inside : forall e, In e (segments_reserved rsegs) ->
  0x10000 <= bv_unsigned (fst e) /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 0x60a000.
Proof.
  intros e He. rewrite pa_reserved_eq in He.
  destruct He as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd]; rewrite !unsigned_lit by lia; lia.
Qed.
Lemma pa_reserved_cover : forall x, 0x10000 <= x < 0x60a000 -> zcovb (segments_reserved rsegs) x = true.
Proof.
  intros x Hx. rewrite pa_reserved_eq. unfold zcovb. cbn [existsb]. unfold zin_rangeb, Ledger.lo, Ledger.hi. cbn [fst snd].
  rewrite !unsigned_lit by lia.
  destruct (Z_lt_le_dec x 0x35000); [| destruct (Z_lt_le_dec x 0xa8000); [| destruct (Z_lt_le_dec x 0xaa000)]].
  - replace (0x10000 <=? x) with true by (symmetry; apply Z.leb_le; lia). replace (x <? 0x10000 + 0x25000) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - replace (0x35000 <=? x) with true by (symmetry; apply Z.leb_le; lia). replace (x <? 0x35000 + 0x73000) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [andb orb]. rewrite !orb_true_r. reflexivity.
  - replace (0xa8000 <=? x) with true by (symmetry; apply Z.leb_le; lia). replace (x <? 0xa8000 + 0x2000) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [andb orb]. rewrite !orb_true_r. reflexivity.
  - replace (0xaa000 <=? x) with true by (symmetry; apply Z.leb_le; lia). replace (x <? 0xaa000 + 0x560000) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn [andb orb]. rewrite !orb_true_r. reflexivity.
Qed.
Lemma pa_reserved_free : forall b k, 0x60a000 <= b -> 0 < k -> b + k <= 2^64 ->
  region_free (segments_reserved rsegs) (Z_to_bv 64 b) (Z_to_bv 64 k) = true.
Proof.
  intros b k Hb Hk Hbk. apply region_free_intro. intros b' s' Hin.   (* [comment removed for export] *)
  pose proof (pa_reserved_inside _ Hin) as X. cbn [fst snd] in X. unfold iv_overlap. rewrite !unsigned_lit by lia.
  apply andb_false_iff. left. apply Z.ltb_ge. lia.
Qed.

Section Cover.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.

  (* [comment removed for export] *)
  Lemma pa_cover_reserved : forall A m md, pa_ainv A m md -> vm_reserved (m_vmmaps md) = segments_reserved rsegs.
  Proof. intros A m md AI. exact (proj2 (proj2 (ai_cover _ _ _ _ _ _ _ AI))). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pa_cover_image_reserved : forall A m md x, pa_ainv A m md -> 0x10000 <= x < 0x60a000 ->
    zcovb (vm_reserved (m_vmmaps md)) x = true.
  Proof. intros A m md x AI Hx. rewrite (pa_cover_reserved A m md AI). exact (pa_reserved_cover x Hx). Qed.
  Lemma pa_cover_reserved_free : forall A m md b k, pa_ainv A m md -> 0x60a000 <= b -> 0 < k -> b + k <= 2^64 ->
    region_free (vm_reserved (m_vmmaps md)) (Z_to_bv 64 b) (Z_to_bv 64 k) = true.
  Proof. intros A m md b k AI Hb Hk Hbk. rewrite (pa_cover_reserved A m md AI). exact (pa_reserved_free b k Hb Hk Hbk). Qed.

  (* [comment removed for export] *)
  Theorem grant_room : forall A (h : VmMaps) (nZ : Z),
    WF AL_pasan A -> acover_ LPA (a_pl A) (a_sec A) h -> nooverlap (vm_maps h) -> alloc_top h = alloc_ceiling ->
    0 < nZ -> nZ mod 4096 = 0 -> nZ <= 2^30 + 2^16 ->
    exists g, g mod 4096 = 0 /\ 0 < g /\ kHighMemBeg <= g /\ g + nZ <= alloc_top h
              /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
  Proof.
    intros A h nZ W ((fog & FL & FS & COV & _ & _) & _ & RSV) NO TOP HnZ HAl Hcap. pose proof alloc_ceiling_val as CE.
    assert (RES : forall e, In e (vm_reserved h) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= kHighMemBeg).
    { intros e He. rewrite RSV in He. pose proof (pa_reserved_inside e He). unfold kHighMemBeg. lia. }
    destruct (wfM A W) as [_ BB].
    set (zs := map zone_of (vm_maps h)).
    set (B := map zone_ofZ (big_maps_ (a_pl A) (a_sec A) ++ fog ++ [(kShadowGapBeg, kHighShadowMapBeg - kShadowGapBeg)])).
    assert (NEz : forall z, In z zs -> fst z < snd z).
    { intros z Hz. subst zs. apply in_map_iff in Hz as (e & <- & He). unfold zone_of, Ledger.lo, Ledger.hi. cbn.
      pose proof (COV e He) as X. cbv zeta in X. destruct X as [X|[X|X]].
      - pose proof (BB _ _ X). lia.
      - pose proof (proj1 (Forall_forall _ _) FS _ X) as Y. cbn in Y. lia.
      - injection X as E1 E2. rewrite E2. unfold kShadowGapBeg, kHighShadowMapBeg. lia. }
    assert (INC : forall z, In z zs -> In z B).
    { intros z Hz. subst zs B. apply in_map_iff in Hz as (e & <- & He). rewrite zone_of_ofZ. apply in_map_iff.
      exists (bv_unsigned (fst e), bv_unsigned (snd e)). split; [reflexivity|].
      pose proof (COV e He) as X. cbv zeta in X. destruct X as [X|[X|X]].
      - apply in_app_iff. left. exact X.
      - apply in_app_iff. right. apply in_app_iff. left. exact X.
      - apply in_app_iff. right. apply in_app_iff. right. left. symmetry. exact X. }
    pose proof (zsum_in_dominated zs B kHighMemBeg (alloc_top h) (zdisj_of_nooverlap _ NO) NEz INC) as [DS DC].
    (* [comment removed for export] *)
    assert (BW : zsum_in B kHighMemBeg (alloc_top h) <= 2^38 /\ zcount B kHighMemBeg (alloc_top h) <= 18 + NLIVE_MAX + 4178).
    { subst B. rewrite (big_maps_split A (a_sec A)). rewrite !map_app, !zsum_in_app, !zcount_app.
      pose proof (fixed_bigmaps_weight A (alloc_top h)) as [F1 F2].
      pose proof (sec_maps_weight A W (alloc_top h)) as [S1 S2]. cbn [a_pl] in F1, F2.
      assert (G1 : zsum_in (map zone_ofZ fog) kHighMemBeg (alloc_top h) <= 16384).
      { assert (FS' : Forall (fun bs => 0 <= fst bs /\ 0 < snd bs <= 8192) fog).
        { apply Forall_forall. intros bs Hbs. pose proof (proj1 (Forall_forall _ _) FS bs Hbs) as (X1 & X2 & _). exact (conj X1 X2). }
        pose proof (zsum_fog fog kHighMemBeg (alloc_top h) FS'). lia. }
      pose proof (zcount_le_length (map zone_ofZ fog) kHighMemBeg (alloc_top h)) as G2. rewrite map_length in G2.
      destruct (zsum_in_below (map zone_ofZ [(kShadowGapBeg, kHighShadowMapBeg - kShadowGapBeg)]) kHighMemBeg (alloc_top h)
                  ltac:(intros z [<-|[]]; cbn; unfold kShadowGapBeg, kHighShadowMapBeg, kHighMemBeg; lia)) as [Q1 Q2].
      rewrite Q1, Q2.
      unfold kSpaceReserve, kPtrArrayReserve, kFakeStackBytes, kDepotNodesBlock, kStackStoreBlockBytes in F1. rewrite NLIVE_MAX_eq in *.
      split; lia. }
    destruct BW as [BW1 BW2].
    apply (asan_grant_exists h zs nZ (2^38) (18 + NLIVE_MAX + 4178)).
    - exact HnZ.
    - unfold page_size. exact HAl.
    - exact (zdisj_of_nooverlap _ NO).
    - intros b s Hin Hb Hk. apply in_app_iff in Hin as [Hin|Hin].
      + exfalso. pose proof (RES _ Hin) as X. cbn in X. lia.
      + exists (zone_of (b, s)). split; [subst zs; apply in_map_iff; exists (b, s); split; [reflexivity| exact Hin]|].
        split; [apply NEz; subst zs; apply in_map_iff; exists (b, s); split; [reflexivity| exact Hin]|].
        unfold zone_of, Ledger.lo, Ledger.hi. cbn. lia.
    - unfold ztotal. lia.
    - unfold znum. lia.
    - rewrite TOP. rewrite NLIVE_MAX_eq. unfold page_size, kHighMemBeg. lia.
  Qed.

  (* [comment removed for export] *)
End Cover.
