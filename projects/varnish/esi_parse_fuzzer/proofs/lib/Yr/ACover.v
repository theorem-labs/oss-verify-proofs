(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (segments_reserved keeps only the segments that are not kernel maps; the reserved ledger is the image's reservations followed by the launch's vDSO pair, so pa_cover_reserved states that split, pa_cover_reserved_free takes a range ending at most a page above kHighMemBeg, and grant_room counts the pair as up to two more zones and 81920 more bytes, with a gap search that needs no disjoint zones). *)
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

(* LPS 727298f3: the launch's reserved pair may overlap the zones of the mappings, so the gap
   search of [grant_room] takes no disjointness: a cursor walks up the window from its low end and
   jumps past each zone that blocks it; a jump costs that zone's clamped length and one count, so
   the room the totals promise is never used up. *)
Lemma zclamp_mono_lo : forall z x x' y, x <= x' -> zclamp z x' y <= zclamp z x y.
Proof. intros [a b] x x' y H. unfold zclamp. cbn [fst snd]. lia. Qed.
Lemma zmeets_mono_lo : forall z x x' y, x <= x' -> zmeets z x' y -> zmeets z x y.
Proof. intros [a b] x x' y H M. unfold zmeets in *. cbn [fst snd] in *. lia. Qed.

Lemma zsum_mono_lo : forall zs x x' y, x <= x' -> zsum_in zs x' y <= zsum_in zs x y /\ zcount zs x' y <= zcount zs x y.
Proof.
  induction zs as [|w r IH]; intros x x' y H; cbn [zsum_in zcount]; [lia|].
  destruct (IH x x' y H) as [Sr Cr]. pose proof (zclamp_mono_lo w x x' y H) as ZC.
  destruct (zmeets_dec w x' y) as [M|M]; destruct (zmeets_dec w x y) as [M'|M']; try (split; lia).
  exfalso. exact (M' (zmeets_mono_lo w x x' y H M)).
Qed.

(* [zsum_past]: moving the low end past the end of a zone [z] that meets the window drops at least
   [z]'s clamped length and one count *)
Lemma zsum_past : forall zs z x x' y, x <= x' -> In z zs -> snd z <= x' -> zmeets z x y ->
  zsum_in zs x' y + zclamp z x y <= zsum_in zs x y /\ zcount zs x' y + 1 <= zcount zs x y.
Proof.
  induction zs as [|w r IH]; intros z x x' y H Hin Hs Mz; [destruct Hin|]. cbn [zsum_in zcount].
  destruct (zsum_mono_lo r x x' y H) as [S0 C0].
  destruct Hin as [E|Hin].
  - subst w.
    assert (Z0 : zclamp z x' y = 0) by (apply zclamp_notmeets; intros (_ & _ & M3); lia).
    destruct (zmeets_dec z x' y) as [M|M]; [exfalso; destruct M as (_ & _ & M3); lia|].
    destruct (zmeets_dec z x y) as [M'|M']; [| exfalso; exact (M' Mz)]. split; lia.
  - destruct (IH z x x' y H Hin Hs Mz) as [S1 C1]. pose proof (zclamp_mono_lo w x x' y H) as ZC.
    destruct (zmeets_dec w x' y) as [M|M]; destruct (zmeets_dec w x y) as [M'|M']; try (split; lia).
    exfalso. exact (M' (zmeets_mono_lo w x x' y H M)).
Qed.

Lemma zblock_dec : forall zs x K,
  (exists z, In z zs /\ fst z < snd z /\ fst z < x + K /\ x < snd z) \/ (forall z, In z zs -> zavoids x K z).
Proof.
  induction zs as [|w r IH]; intros x K.
  - right. intros z [].
  - destruct (IH x K) as [(z & Hz & H1 & H2 & H3)|H].
    + left. exists z. split; [right; exact Hz|]. split; [exact H1|]. split; [exact H2| exact H3].
    + destruct (Z_lt_le_dec (fst w) (snd w)) as [W1|W1].
      * destruct (Z_lt_le_dec (fst w) (x + K)) as [W2|W2].
        -- destruct (Z_lt_le_dec x (snd w)) as [W3|W3].
           ++ left. exists w. split; [left; reflexivity|]. split; [exact W1|]. split; [exact W2| exact W3].
           ++ right. intros z [<-|Hz]; [intros _; left; exact W3| exact (H z Hz)].
        -- right. intros z [<-|Hz]; [intros _; right; exact W2| exact (H z Hz)].
      * right. intros z [<-|Hz]; [intros X; lia| exact (H z Hz)].
Qed.

(* [APlace.zone_gap] without its disjointness premise *)
Lemma zone_gap_any : forall zs x y K,
  0 < K -> zsum_in zs x y + (zcount zs x y + 1) * K <= y - x ->
  exists g, x <= g /\ g + K <= y /\ forall z, In z zs -> zavoids g K z.
Proof.
  intros zs x0 y K HK Hroom0.
  assert (MAIN : forall n x, x0 <= x -> zcount zs x y <= Z.of_nat n ->
            zsum_in zs x y + (zcount zs x y + 1) * K <= y - x ->
            exists g, x0 <= g /\ g + K <= y /\ forall z, In z zs -> zavoids g K z).
  { induction n as [|n IH]; intros x Hx Hn Hroom.
    all: pose proof (zsum_in_nonneg zs x y) as S0; pose proof (zcount_nonneg zs x y) as C0.
    all: assert (CK : 0 <= zcount zs x y * K) by (apply Z.mul_nonneg_nonneg; lia).
    all: assert (KY : x + K <= y) by lia.
    all: destruct (zblock_dec zs x K) as [(z & Hz & B1 & B2 & B3)|FREE];
           [| exists x; split; [exact Hx|]; split; [exact KY| exact FREE]].
    all: assert (MZ : zmeets z x y) by (unfold zmeets; lia).
    all: destruct (zsum_past zs z x (snd z) y ltac:(lia) Hz ltac:(lia) MZ) as [S1 C1].
    all: pose proof (zcount_nonneg zs (snd z) y) as C2; pose proof (zsum_in_nonneg zs (snd z) y) as S2.
    - (* no step left, yet the blocking zone is counted *)
      exfalso. cbn [Z.of_nat] in Hn. lia.
    - (* jump to the end of the blocking zone *)
      assert (CL : snd z <= y -> snd z - x <= zclamp z x y + K) by (intros; unfold zclamp; lia).
      assert (CY : y < snd z -> y - x - K < zclamp z x y) by (intros; unfold zclamp; lia).
      assert (M1 : (zcount zs (snd z) y + 1) * K <= zcount zs x y * K) by (apply Z.mul_le_mono_nonneg_r; lia).
      assert (M3 : 1 * K <= zcount zs x y * K) by (apply Z.mul_le_mono_nonneg_r; lia).
      rewrite Nat2Z.inj_succ in Hn.
      apply (IH (snd z)); [lia | lia |].
      destruct (Z_le_gt_dec (snd z) y) as [Y|Y]; [specialize (CL Y)| specialize (CY (Z.gt_lt _ _ Y))]; first [lia | nia]. }
  apply (MAIN (Z.to_nat (zcount zs x0 y)) x0); [lia| | exact Hroom0].
  pose proof (zcount_nonneg zs x0 y) as Q. rewrite Z2Nat.id by exact Q. lia.
Qed.

(* [APlace.asan_grant_exists] without its disjointness premise *)
Lemma asan_grant_any : forall (h : VmMaps) (zs : list zone) (nZ T C : Z),
  0 < nZ -> nZ mod page_size = 0 ->
  (forall b s, In (b, s) (vm_reserved h ++ vm_maps h) ->
     bv_unsigned b < alloc_top h -> kHighMemBeg < bv_unsigned b + bv_unsigned s ->
     exists z, In z zs /\ fst z < snd z /\ fst z <= bv_unsigned b /\ bv_unsigned b + bv_unsigned s <= snd z) ->
  ztotal zs kHighMemBeg (alloc_top h) <= T -> znum zs kHighMemBeg (alloc_top h) <= C ->
  kHighMemBeg + T + (C + 1) * (nZ + page_size) <= alloc_top h ->
  exists g, g mod page_size = 0 /\ 0 < g /\ kHighMemBeg <= g /\ g + nZ <= alloc_top h
            /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
  intros h zs nZ T C HnZ HnAl Hcov HT HC Hroom.
  pose proof (alloc_top_lt h) as Htop. try (unfold two_pow_64 in Htop).
  unfold ztotal, znum in HT, HC.
  pose proof (zcount_nonneg zs kHighMemBeg (alloc_top h)) as C0.
  assert (M : (zcount zs kHighMemBeg (alloc_top h) + 1) * (nZ + page_size) <= (C + 1) * (nZ + page_size))
    by (apply Z.mul_le_mono_nonneg_r; unfold page_size; lia).
  destruct (zone_gap_any zs kHighMemBeg (alloc_top h) (nZ + page_size) ltac:(unfold page_size; lia) ltac:(lia)) as (g & G1 & G2 & G3).
  destruct (free_window_of_gap h zs kHighMemBeg (alloc_top h) nZ HnZ HnAl ltac:(unfold kHighMemBeg; lia) ltac:(lia) Hcov g G1 G2 G3)
    as (A1 & A2 & A3 & FREE).
  cbv zeta in A1, A2, A3, FREE.
  exists (page_round_up_Z g). unfold kHighMemBeg in *.
  split; [exact A1|]. split; [lia|]. split; [lia|]. split; [lia| exact FREE].
Qed.

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

(* LPS 727298f3: the launch's reserved pair as zones: in any window they weigh at most their
   sizes, and count at most their number *)
Lemma rx_zones_weight : forall rx x y,
  zsum_in (map zone_of rx) x y <= res_bytes rx /\ zcount (map zone_of rx) x y <= Z.of_nat (length rx).
Proof.
  induction rx as [|e rx IH]; intros x y; cbn [map zsum_in zcount res_bytes length]; [cbn; lia|].
  destruct (IH x y) as [Sr Cr]. pose proof (bv_unsigned_in_range 64 (snd e)) as R. rewrite Nat2Z.inj_succ.
  assert (CLe : zclamp (zone_of e) x y <= bv_unsigned (snd e)) by (unfold zclamp, zone_of, Ledger.lo, Ledger.hi; cbn [fst snd]; lia).
  destruct (zmeets_dec (zone_of e) x y); lia.
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
  (* LPS 727298f3: [segments_reserved] keeps the segments that are not kernel maps; the image's
     segments are none, by computation *)
  assert (Hfl : segments_reserved rsegs = map segment_reservation rsegs) by reflexivity.
  rewrite Hfl. unfold rsegs, Asan.M.loaded_segments, Asan.Asan_loaded_segments.
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

(* LPS 727298f3: the launch's reserved pair ([AInv.res_launch]): each entry has a positive size and
   lies a page above kHighMemBeg, below 2^47; at most two of them, 81920 bytes in all *)
Lemma res_launch_facts : forall cl rx, res_launch cl rx ->
  (forall e, In e rx -> 0 < bv_unsigned (snd e) /\ kHighMemBeg + 4096 <= bv_unsigned (fst e)
                        /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= 2^47)
  /\ (length rx <= 2)%nat /\ res_bytes rx <= 81920.
Proof.
  intros cl rx (F & L & Bt). split; [| exact (conj L Bt)].
  intros e He. pose proof (proj1 (Forall_forall _ _) F e He) as (P1 & _ & _ & _ & P5 & P6).
  split; [exact P1|]. split; [exact P5| exact P6].
Qed.

(* below a page above kHighMemBeg the reserved ledger is the image's alone: the launch's pair
   sits higher *)
Lemma reserved_free_low : forall rx b k, res_launch LPA rx -> 0x60a000 <= b -> 0 < k -> b + k <= kHighMemBeg + 4096 ->
  region_free (segments_reserved rsegs ++ rx) (Z_to_bv 64 b) (Z_to_bv 64 k) = true.
Proof.
  intros rx b k RX Hb Hk Hbk. destruct (res_launch_facts LPA rx RX) as (RXE & _ & _). unfold kHighMemBeg in *.
  apply region_free_intro. intros b' s' Hin. apply in_app_iff in Hin as [Hin|Hin].
  - pose proof (pa_reserved_inside _ Hin) as X. cbn [fst snd] in X. unfold iv_overlap. rewrite !unsigned_lit by lia.
    apply andb_false_iff. left. apply Z.ltb_ge. lia.
  - pose proof (RXE _ Hin) as (_ & X & _). cbn [fst snd] in X. unfold iv_overlap. rewrite !unsigned_lit by lia.
    apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.

Section Cover.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {DR : DepotRep}.

  (* [comment removed for export] *)
  (* LPS 727298f3: the reserved ledger is the image's reservations followed by the launch's pair
     ([acover_]); it WAS the image's alone *)
  Lemma pa_cover_reserved : forall A m md, pa_ainv A m md ->
    exists rx, vm_reserved (m_vmmaps md) = segments_reserved rsegs ++ rx /\ res_launch LPA rx.
  Proof. intros A m md AI. exact (proj2 (proj2 (ai_cover _ _ _ _ _ _ _ AI))). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pa_cover_image_reserved : forall A m md x, pa_ainv A m md -> 0x10000 <= x < 0x60a000 ->
    zcovb (vm_reserved (m_vmmaps md)) x = true.
  Proof.
    intros A m md x AI Hx. destruct (pa_cover_reserved A m md AI) as (rx & E & _).
    rewrite E, zcovb_app, (pa_reserved_cover x Hx). reflexivity.
  Qed.
  (* LPS 727298f3: the range ends at most a page above kHighMemBeg (it WAS any range below 2^64),
     so it misses the launch's pair *)
  Lemma pa_cover_reserved_free : forall A m md b k, pa_ainv A m md -> 0x60a000 <= b -> 0 < k -> b + k <= kHighMemBeg + 4096 ->
    region_free (vm_reserved (m_vmmaps md)) (Z_to_bv 64 b) (Z_to_bv 64 k) = true.
  Proof.
    intros A m md b k AI Hb Hk Hbk. destruct (pa_cover_reserved A m md AI) as (rx & E & RX). rewrite E.
    exact (reserved_free_low rx b k RX Hb Hk Hbk).
  Qed.

  (* [comment removed for export] *)
  Theorem grant_room : forall A (h : VmMaps) (nZ : Z),
    WF AL_pasan A -> acover_ LPA (a_pl A) (a_sec A) h -> nooverlap (vm_maps h) -> alloc_top h = alloc_ceiling ->
    0 < nZ -> nZ mod 4096 = 0 -> nZ <= 2^30 + 2^16 ->
    exists g, g mod 4096 = 0 /\ 0 < g /\ kHighMemBeg <= g /\ g + nZ <= alloc_top h
              /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
  Proof.
    intros A h nZ W ((fog & FL & FS & COV & _ & _) & _ & (rx & RSV & RX)) NO TOP HnZ HAl Hcap. pose proof alloc_ceiling_val as CE.
    (* LPS 727298f3: the reserved ledger is the image's reservations, all below kHighMemBeg, then the
       launch's pair [rx], which may lie in the window and overlap the mappings: each of its entries
       is a zone of its own, at most two and 81920 bytes ([res_launch]) *)
    assert (RES : forall e, In e (segments_reserved rsegs) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= kHighMemBeg).
    { intros e He. pose proof (pa_reserved_inside e He). unfold kHighMemBeg. lia. }
    destruct (res_launch_facts LPA rx RX) as (RXE & RXL & RXB).
    destruct (wfM A W) as [_ BB].
    set (zm := map zone_of (vm_maps h)).
    set (B := map zone_ofZ (big_maps_ (a_pl A) (a_sec A) ++ fog ++ [(kShadowGapBeg, kHighShadowMapBeg - kShadowGapBeg)])).
    assert (NEz : forall z, In z zm -> fst z < snd z).
    { intros z Hz. subst zm. apply in_map_iff in Hz as (e & <- & He). unfold zone_of, Ledger.lo, Ledger.hi. cbn.
      pose proof (COV e He) as X. cbv zeta in X. destruct X as [X|[X|X]].
      - pose proof (BB _ _ X). lia.
      - pose proof (proj1 (Forall_forall _ _) FS _ X) as Y. cbn in Y. lia.
      - injection X as E1 E2. rewrite E2. unfold kShadowGapBeg, kHighShadowMapBeg. lia. }
    assert (INC : forall z, In z zm -> In z B).
    { intros z Hz. subst zm B. apply in_map_iff in Hz as (e & <- & He). rewrite zone_of_ofZ. apply in_map_iff.
      exists (bv_unsigned (fst e), bv_unsigned (snd e)). split; [reflexivity|].
      pose proof (COV e He) as X. cbv zeta in X. destruct X as [X|[X|X]].
      - apply in_app_iff. left. exact X.
      - apply in_app_iff. right. apply in_app_iff. left. exact X.
      - apply in_app_iff. right. apply in_app_iff. right. left. symmetry. exact X. }
    pose proof (zsum_in_dominated zm B kHighMemBeg (alloc_top h) (zdisj_of_nooverlap _ NO) NEz INC) as [DS DC].
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
    pose proof (rx_zones_weight rx kHighMemBeg (alloc_top h)) as [RW1 RW2].
    apply (asan_grant_any h (zm ++ map zone_of rx) nZ (2^38 + 81920) (18 + NLIVE_MAX + 4178 + 2)).
    - exact HnZ.
    - unfold page_size. exact HAl.
    - intros b s Hin Hb Hk. apply in_app_iff in Hin as [Hin|Hin].
      + rewrite RSV in Hin. apply in_app_iff in Hin as [Hin|Hin].
        * exfalso. pose proof (RES _ Hin) as X. cbn in X. lia.
        * exists (zone_of (b, s)). split; [apply in_or_app; right; apply in_map_iff; exists (b, s); split; [reflexivity| exact Hin]|].
          pose proof (RXE _ Hin) as (P1 & _). cbn [fst snd] in P1.
          unfold zone_of, Ledger.lo, Ledger.hi. cbn. lia.
      + exists (zone_of (b, s)). split; [apply in_or_app; left; subst zm; apply in_map_iff; exists (b, s); split; [reflexivity| exact Hin]|].
        split; [apply NEz; subst zm; apply in_map_iff; exists (b, s); split; [reflexivity| exact Hin]|].
        unfold zone_of, Ledger.lo, Ledger.hi. cbn. lia.
    - unfold ztotal. rewrite zsum_in_app. lia.
    - unfold znum. rewrite zcount_app. lia.
    - rewrite TOP. rewrite NLIVE_MAX_eq. unfold page_size, kHighMemBeg. lia.
  Qed.

  (* [comment removed for export] *)
End Cover.
