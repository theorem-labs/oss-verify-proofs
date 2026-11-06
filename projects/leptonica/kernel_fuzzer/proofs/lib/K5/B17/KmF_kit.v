(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_objkit Km_setelem Km_iface Km_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma keeps_live_of_agf : forall lv frs sp (m m' : mem), agree_on (aclient lv frs sp) m m' -> keeps_live lv m m'.
Proof. intros lv frs sp m m' AG b k Hin a Ha. apply AG. right; right; left. exists b, k. split; [exact Hin| exact Ha]. Qed.

Lemma keeps_live_of_agree : forall lv frs sp W (m m' : mem) L,
  agree_on (fun a => aclient lv frs sp a /\ outside W a) m m' ->
  (forall e, In e L -> In e lv) -> (forall b k x, In (b, k) L -> b <= x < b + k -> outside W x) -> keeps_live L m m'.
Proof.
  intros lv frs sp W m m' L AG S O b k Hin a Ha. apply AG. split; [| exact (O b k _ Hin Ha)].
  right; right; left. exists b, k. split; [exact (S _ Hin)| exact Ha].
Qed.

Lemma keeps_live_sub : forall L L' (m m' : mem), keeps_live L m m' -> (forall e, In e L' -> In e L) -> keeps_live L' m m'.
Proof. intros L L' m m' K S b k Hin a Ha. exact (K b k (S _ Hin) a Ha). Qed.

Lemma chunk_mono : forall live live' p n, (forall e, In e live -> In e live') -> chunk live p n -> chunk live' p n.
Proof. intros live live' p n S (Hin & R). exact (conj (S _ Hin) R). Qed.
Lemma cmap_obj_mono : forall live live' (m : mem) cmap cv, (forall e, In e live -> In e live') ->
  cmap_obj live m cmap cv -> cmap_obj live' m cmap cv.
Proof.
  intros live live' m cmap cv S (C & CH1 & CH2 & R).
  exact (conj C (conj (chunk_mono _ _ _ _ S CH1) (conj (chunk_mono _ _ _ _ S CH2) R))).
Qed.
Lemma pix_obj_mono : forall live live' (m : mem) pix v cv, (forall e, In e live -> In e live') ->
  pix_obj live m pix v cv -> pix_obj live' m pix v cv.
Proof.
  intros live live' m pix v cv S (C & CH & HOK & HD & HCM).
  split; [exact C| split; [exact (chunk_mono _ _ _ _ S CH)| split; [exact HOK| split]]].
  - destruct HD as [HD|(HD & R)]; [left; exact HD| right; exact (conj (chunk_mono _ _ _ _ S HD) R)].
  - destruct HCM as [HCM|(HCM & R)]; [left; exact HCM| right; exact (conj (cmap_obj_mono _ _ _ _ _ S HCM) R)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nodup_live_remove : forall p (l : list (Z * Z)), List.NoDup (map fst l) -> List.NoDup (map fst (live_remove p l)).
Proof.
  intros p l. induction l as [|e l IH]; intros ND; [constructor|]. rewrite lrm_cons. cbn [map] in ND.
  apply List.NoDup_cons_iff in ND as (NI & ND). destruct (fst e =? p); [exact (IH ND)|]. cbn [map]. constructor; [| exact (IH ND)].
  intros Hin. apply NI. apply in_map_iff in Hin as (e' & E & He'). apply in_map_iff. exists e'. split; [exact E| exact (live_remove_sub _ _ _ He')].
Qed.
Lemma nodup_rm_opt : forall p (l : list (Z * Z)), List.NoDup (map fst l) -> List.NoDup (map fst (rm_opt p l)).
Proof. intros p l ND. unfold rm_opt. destruct (p =? 0); [exact ND| exact (nodup_live_remove p l ND)]. Qed.

(* [comment removed for export] *)
Lemma sec_bytes_remove_nodup : forall (l : list (Z * Z)) p n, List.NoDup (map fst l) -> In (p, n) l ->
  sec_bytes l = sec_bytes (live_remove p l) + (if 64512 <? n then n else 0).
Proof.
  induction l as [|[q k] l IH]; intros p n ND Hin; [destruct Hin|]. cbn [map fst] in ND. apply List.NoDup_cons_iff in ND as (NI & ND).
  rewrite lrm_cons. cbn [fst]. destruct (Z.eqb_spec q p) as [E|E].
  - subst q. destruct Hin as [Eq|Hin]; [injection Eq as <-| exfalso; apply NI; apply in_map_iff; exists (p, n); split; [reflexivity| exact Hin]].
    rewrite (live_remove_notin p l NI). cbn [sec_bytes]. lia.
  - destruct Hin as [Eq|Hin]; [injection Eq as <- <-; contradiction|]. cbn [sec_bytes]. rewrite (IH p n ND Hin). lia.
Qed.

(* [comment removed for export] *)
Lemma pix_destroy_sec : forall (L1 : list (Z * Z)) (m : mem) pix v cv,
  List.NoDup (map fst L1) -> pix_obj L1 m pix v cv -> p_data v <> 0 ->
  sec_bytes L1 <= sec_bytes (live_destroy pix v cv L1) + 0x4000000.
Proof.
  intros L1 m pix v cv ND (PXC & PCH & HOK & HD & HCM) DNZ.
  destruct PCH as (PIN & _). destruct HOK as (_ & _ & _ & _ & RS).
  destruct HD as [HD|((DIN & _) & DNP)]; [contradiction|].
  unfold live_destroy, rm_opt. replace (p_data v =? 0) with false by (symmetry; apply Z.eqb_neq; exact DNZ).
  pose proof (sec_bytes_remove_nodup L1 (p_data v) _ ND DIN) as E1.
  pose proof (nodup_live_remove (p_data v) L1 ND) as ND1.
  set (L1a := live_remove (p_data v) L1) in *.
  assert (SR : (if 64512 <? rsize v then rsize v else 0) <= 0x4000000) by (destruct (Z.ltb_spec 64512 (rsize v)); unfold rsize in *; lia).
  assert (PINa : In (pix, 64) L1a) by (apply live_remove_keep; [exact PIN| cbn [fst]; intros E; apply DNP; symmetry; exact E]).
  destruct HCM as [CZ|(((pad & CC) & (CIN & C0 & _) & (AIN & A0 & _) & COK & ACN) & CPX & APX & CPD & APD)].
  - rewrite CZ. cbn [Z.eqb].
    pose proof (sec_bytes_remove_nodup L1a pix 64 ND1 PINa) as E2. cbn in E2. lia.
  - replace (p_cmap v =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    replace (c_arr cv =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    assert (AINa : In (c_arr cv, 4 * c_nalloc cv) L1a) by (apply live_remove_keep; [exact AIN| cbn [fst]; exact APD]).
    pose proof (sec_bytes_remove_nodup L1a (c_arr cv) _ ND1 AINa) as E2.
    pose proof (nodup_live_remove (c_arr cv) L1a ND1) as ND2.
    set (L1b := live_remove (c_arr cv) L1a) in *.
    assert (CINb : In (p_cmap v, 24) L1b)
      by (apply live_remove_keep; [apply live_remove_keep; [exact CIN| cbn [fst]; exact CPD]| cbn [fst]; intros E; apply ACN; symmetry; exact E]).
    pose proof (sec_bytes_remove_nodup L1b (p_cmap v) 24 ND2 CINb) as E3.
    pose proof (nodup_live_remove (p_cmap v) L1b ND2) as ND3.
    set (L1c := live_remove (p_cmap v) L1b) in *.
    assert (PINc : In (pix, 64) L1c)
      by (apply live_remove_keep; [apply live_remove_keep; [exact PINa| cbn [fst]; intros E; apply APX; symmetry; exact E]|
                                   cbn [fst]; intros E; apply CPX; symmetry; exact E]).
    pose proof (sec_bytes_remove_nodup L1c pix 64 ND3 PINc) as E4.
    destruct COK as (HDP & HNA & _). assert (NA : c_nalloc cv <= 256)
      by (rewrite HNA; cbn in HDP; destruct HDP as [<-|[<-|[<-|[<-|[]]]]]; cbn; lia).
    rewrite (proj2 (Z.ltb_ge 64512 (4 * c_nalloc cv)) ltac:(lia)) in E2. cbn in E3, E4. lia.
Qed.

(* [comment removed for export] *)
Lemma live_remove_app_notin' : forall p (X L : list (Z * Z)), ~ In p (map fst X) -> live_remove p (X ++ L) = X ++ live_remove p L.
Proof. intros p X L H. rewrite lrm_app, (live_remove_notin p X H). reflexivity. Qed.
Lemma rm_opt_app_notin' : forall p (X L : list (Z * Z)), (p <> 0 -> ~ In p (map fst X)) -> rm_opt p (X ++ L) = X ++ rm_opt p L.
Proof.
  intros p X L H. unfold rm_opt. destruct (Z.eqb_spec p 0) as [E|E]; [reflexivity|]. exact (live_remove_app_notin' p X L (H E)).
Qed.
Lemma live_destroy_app_notin : forall pix v cv (X L : list (Z * Z)),
  ~ In pix (map fst X) -> (p_data v <> 0 -> ~ In (p_data v) (map fst X)) -> (p_cmap v <> 0 -> ~ In (p_cmap v) (map fst X)) ->
  (p_cmap v <> 0 -> c_arr cv <> 0 -> ~ In (c_arr cv) (map fst X)) ->
  live_destroy pix v cv (X ++ L) = X ++ live_destroy pix v cv L.
Proof.
  intros pix v cv X L HP HD HC HA. unfold live_destroy.
  rewrite (rm_opt_app_notin' (p_data v) X L HD).
  rewrite (rm_opt_app_notin' (if p_cmap v =? 0 then 0 else c_arr cv) X).
  2:{ intros NZ. destruct (Z.eqb_spec (p_cmap v) 0) as [E|E]; [contradiction| exact (HA E NZ)]. }
  rewrite (rm_opt_app_notin' (p_cmap v) X _ HC).
  exact (live_remove_app_notin' pix X _ HP).
Qed.

Lemma rm_opt_sub : forall p (l : list (Z * Z)) e, In e (rm_opt p l) -> In e l.
Proof. intros p l e He. unfold rm_opt in He. destruct (p =? 0); [exact He| exact (live_remove_sub l p e He)]. Qed.
Lemma live_destroy_sub : forall pix v cv (l : list (Z * Z)) e, In e (live_destroy pix v cv l) -> In e l.
Proof.
  intros pix v cv l e He. unfold live_destroy in He. apply live_remove_sub in He.
  apply rm_opt_sub in He. apply rm_opt_sub in He. apply rm_opt_sub in He. exact He.
Qed.

(* [comment removed for export] *)
Definition km_prefix (kel data sy sx : Z) (rows : list Z) : list (Z * Z) :=
  rev (map (fun r => (r, 4 * sx)) rows) ++ [(data, 8 * sy); (kel, 24)].
Lemma km_live_prefix : forall kel data sy sx rows L, km_live kel data sy sx rows L = km_prefix kel data sy sx rows ++ L.
Proof. intros. unfold km_live, km_prefix. rewrite <- app_assoc. reflexivity. Qed.
Lemma km_prefix_fst_in : forall kel data sy sx rows x, In x (map fst (km_prefix kel data sy sx rows)) -> In x (kel :: data :: rows).
Proof.
  intros kel data sy sx rows x H. unfold km_prefix in H. rewrite map_app, map_rev, map_map in H. cbn [map fst] in H.
  rewrite map_id in H. apply in_app_or in H as [H|[E|[E|[]]]].
  - right; right. apply in_rev in H. exact H.
  - right; left; exact E.
  - left; exact E.
Qed.

(* [comment removed for export] *)
Lemma live_destroy_km : forall kel data sy sx rows L (m : mem) pix v cv,
  List.NoDup (map fst (km_live kel data sy sx rows L)) -> pix_obj L m pix v cv ->
  live_destroy pix v cv (km_live kel data sy sx rows L) = km_live kel data sy sx rows (live_destroy pix v cv L).
Proof.
  intros kel data sy sx rows L m pix v cv ND POBJ.
  destruct (km_live_nodup_split _ _ _ _ _ _ ND) as (_ & NIN).
  assert (NX : forall b, In b (map fst L) -> ~ In b (map fst (km_prefix kel data sy sx rows))).
  { intros b Hb Hx. apply (NIN b (km_prefix_fst_in _ _ _ _ _ _ Hx) Hb). }
  destruct POBJ as (_ & (PIN & _) & _ & HD & HCM).
  rewrite !km_live_prefix. apply live_destroy_app_notin.
  - apply NX. apply in_map_iff. exists (pix, 64). split; [reflexivity| exact PIN].
  - intros DNZ. destruct HD as [HD|((DIN & _) & _)]; [contradiction|]. apply NX. apply in_map_iff. exists (p_data v, rsize v). split; [reflexivity| exact DIN].
  - intros CNZ. destruct HCM as [HC|((_ & (CIN & _) & _) & _)]; [contradiction|]. apply NX. apply in_map_iff. exists (p_cmap v, 24). split; [reflexivity| exact CIN].
  - intros CNZ ANZ. destruct HCM as [HC|((_ & _ & (AIN & _) & _) & _)]; [contradiction|]. apply NX. apply in_map_iff.
    exists (c_arr cv, 4 * c_nalloc cv). split; [reflexivity| exact AIN].
Qed.
