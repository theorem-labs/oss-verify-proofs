(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import PropExec MState Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LMeasure LBase LGap04.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMadv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FR_NMAX : Z := 2^23.
Definition FR_MINGRANT : Z := 2^16.
Definition FR_COEF : Z := 130.

(* [comment removed for export] *)
Definition fr_phi (mo : Model) : Z :=
  zsumf (jcost FR_NMAX) (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FR_KW : Z := 2^16.
Definition FR_NBIG : Z := 2^26 + 2^14.
Definition FR_RBIG : Z := 2^39 - 2^35.
Definition fr_count (mo : Model) : Z := Z.of_nat (length (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))).

Definition FRONTR (mo : Model) (R : Z) : Prop :=
  (0 <= R /\ 4096 + fr_phi mo + FR_NMAX + FR_COEF * R <= alloc_ceiling /\ FR_KW * fr_count mo + R <= target_alloc_limit) /\ noaccess_pos mo.

Lemma FRONTR_noaccess_pos : forall mo R, FRONTR mo R -> noaccess_pos mo.
Proof. intros mo R [_ H]. exact H. Qed.

Lemma iv_subtract_pos : forall (a sz : word) lo hi b k, 0 < bv_unsigned sz -> In (b, k) (iv_subtract a sz lo hi) -> 0 < bv_unsigned k.
Proof.
  intros a sz lo hi b k Hsz Hin. unfold iv_subtract in Hin. pose proof (bv_unsigned_in_range 64 sz) as RS. pose proof (bv_unsigned_in_range 64 a) as RA.
  unfold bv_modulus in *. cbn in RS, RA. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [L|L]; [| destruct Hin]. destruct Hin as [E|[]]. injection E as _ <-.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. rewrite Z.mod_small; lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [L|L]; [| destruct Hin]. destruct Hin as [E|[]]. injection E as _ <-.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. rewrite Z.mod_small; lia.
Qed.

Lemma noaccess_subtract_pos : forall (l : list (word * word)) lo hi,
  (forall b k, In (b, k) l -> 0 < bv_unsigned k) -> forall b k, In (b, k) (maps_subtract l lo hi) -> 0 < bv_unsigned k.
Proof.
  induction l as [|[a sz] l IH]; intros lo hi H b k Hin; [destruct Hin|]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
  - eapply iv_subtract_pos; [| exact Hin]. apply (H a sz). left. reflexivity.
  - eapply IH; [| exact Hin]. intros b' k' Hb. apply (H b' k'). right. exact Hb.
Qed.

Lemma noaccess_pos_commit : forall addr n mo, noaccess_pos mo -> noaccess_pos (mm_commit addr n mo).
Proof. intros addr n mo H b k Hin. exact (noaccess_subtract_pos _ _ _ H b k Hin). Qed.

Lemma noaccess_pos_unmap : forall addr n mo, noaccess_pos mo -> noaccess_pos (mm_unmap addr n mo).
Proof. intros addr n mo H b k Hin. exact (noaccess_subtract_pos _ _ _ H b k Hin). Qed.

Lemma jcost_nonneg : forall n e, 0 <= n -> 0 <= jcost n e.
Proof. intros n e Hn. unfold jcost, esz. pose proof (bv_unsigned_in_range 64 (snd e)). lia. Qed.

Lemma jcost_mono : forall n n' e, n <= n' -> jcost n e <= jcost n' e.
Proof. intros. unfold jcost. lia. Qed.

Lemma zsumf_mono {A} : forall (f g : A -> Z) l, (forall x, In x l -> f x <= g x) -> zsumf f l <= zsumf g l.
Proof.
  intros f g l. induction l as [|x l IH]; intros H; cbn [zsumf fold_right]; [lia|]. fold (zsumf f l) (zsumf g l).
  pose proof (H x (or_introl eq_refl)). pose proof (IH (fun y Hy => H y (or_intror Hy))). lia.
Qed.

Lemma zsumf_filter_le {A} : forall (f : A -> Z) (p : A -> bool) l, (forall x, In x l -> 0 <= f x) -> zsumf f (List.filter p l) <= zsumf f l.
Proof.
  intros f p l. induction l as [|x l IH]; intros H; cbn [List.filter zsumf fold_right]; [lia|]. fold (zsumf f l).
  pose proof (H x (or_introl eq_refl)). pose proof (IH (fun y Hy => H y (or_intror Hy))).
  destruct (p x); cbn [zsumf fold_right]; fold (zsumf f (List.filter p l)); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma FRONTR_le : forall mo R R', FRONTR mo R -> 0 <= R' -> R' <= R -> FRONTR mo R'.
Proof. intros mo R R' [[H0 [H HK]] NP] H0' Hle. split; [|exact NP]. split; [exact H0'|]. unfold FR_COEF in *. split; lia. Qed.

Lemma FRONTR_nonneg : forall mo R, FRONTR mo R -> 0 <= R.
Proof. intros mo R [[H _] _]. exact H. Qed.

Lemma FRONTR_vm : forall mo mo' R, FRONTR mo R -> m_vmmaps mo' = m_vmmaps mo -> FRONTR mo' R.
Proof. intros mo mo' R H E. unfold FRONTR, fr_phi, fr_count, noaccess_pos in *. rewrite E. exact H. Qed.

Lemma FRONTR_same_maps : forall mo mo' R, FRONTR mo R ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) -> vm_maps (m_vmmaps mo') = vm_maps (m_vmmaps mo) -> noaccess_pos mo' -> FRONTR mo' R.
Proof. intros mo mo' R [H _] E1 E2 NP. split; [|exact NP]. unfold fr_phi, fr_count in *. rewrite E1, E2. exact H. Qed.

(* [comment removed for export] *)
Lemma FRONTR_commit : forall mo R addr n, FRONTR mo R -> FRONTR (mm_commit addr n mo) R.
Proof.
  intros mo R addr n H. eapply FRONTR_same_maps; [exact H| reflexivity| exact (mm_commit_maps addr n mo)|].
  apply noaccess_pos_commit. exact (FRONTR_noaccess_pos _ _ H).
Qed.

(* [comment removed for export] *)
Lemma FRONTR_unmap : forall mo R addr n, FRONTR mo R -> FRONTR (mm_unmap addr n mo) R.
Proof.
  intros mo R addr n [[H0 [H HK]] NP]. split; [| apply noaccess_pos_unmap; exact NP]. split; [exact H0|]. unfold fr_phi, fr_count in *.
  rewrite (mm_unmap_maps addr n mo).
  replace (vm_reserved (m_vmmaps (mm_unmap addr n mo))) with (vm_reserved (m_vmmaps mo)) by reflexivity.
  rewrite zsumf_app in *. rewrite length_app in *.
  assert (Hle : zsumf (jcost FR_NMAX) (map_remove (vm_maps (m_vmmaps mo)) addr) <= zsumf (jcost FR_NMAX) (vm_maps (m_vmmaps mo))).
  { unfold map_remove. apply zsumf_filter_le. intros e _. apply jcost_nonneg. unfold FR_NMAX. lia. }
  assert (Hlen : (length (map_remove (vm_maps (m_vmmaps mo)) addr) <= length (vm_maps (m_vmmaps mo)))%nat).
  { unfold map_remove. apply List.filter_length_le. }
  unfold FR_KW in *. split; lia.
Qed.

(* [comment removed for export] *)
Theorem FRONTR_placeable : forall mo R n, LOK bsegs mo -> FRONTR mo R -> 0 <= n -> n <= FR_NMAX ->
  mmap_placeable mo n.
Proof.
  intros mo R n HO [[H0 [H _]] _] Hn Hle. apply (mmap_placeable_gap bsegs mo n HO).
  apply vm_gap_available_of_sum; [exact Hn|]. rewrite (lok_top _ _ HO).
  assert (Hm : zsumf (jcost n) (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) <= fr_phi mo).
  { unfold fr_phi. apply zsumf_mono. intros e _. apply jcost_mono. exact Hle. }
  unfold FR_COEF in *. lia.
Qed.

(* [comment removed for export] *)
Theorem FRONTR_grant : forall mo R (a : word) n, FRONTR mo R -> FR_MINGRANT <= n -> n < 2^64 -> n <= R ->
  FRONTR (mm_add_map a (Z_to_bv 64 n) mo) (R - n).
Proof.
  intros mo R a n [[H0 [H HK]] NP] Hmin H64 Hle. split; [| apply noaccess_pos_add_map; exact NP]. split; [lia|]. unfold fr_phi, fr_count in *.
  rewrite (mm_add_map_vmmaps a (Z_to_bv 64 n) mo). cbn [vm_reserved vm_maps].
  rewrite zsumf_app in *. rewrite length_app in *. cbn [zsumf fold_right length]. fold (zsumf (jcost FR_NMAX) (vm_maps (m_vmmaps mo))).
  unfold jcost at 2, esz. cbn [snd]. rewrite unsigned_lit by (unfold FR_MINGRANT in *; lia).
  unfold FR_COEF, FR_NMAX, FR_MINGRANT, FR_KW in *. split; lia.
Qed.

(* [comment removed for export] *)
Theorem FRONTR_grant_lazy : forall mo R (a : word) n, FRONTR mo R -> FR_MINGRANT <= n -> n < 2^64 -> n <= R ->
  FRONTR (mm_add_lazy a (Z_to_bv 64 n) mo) (R - n).
Proof.
  intros mo R a n HF Hmin H64 Hle. eapply FRONTR_vm; [exact (FRONTR_grant mo R a n HF Hmin H64 Hle)|].
  apply mm_add_lazy_vmmaps.
Qed.

(* [comment removed for export] *)
Lemma FRONTR_intro : forall mo R K S,
  0 <= R ->
  Z.of_nat (length (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))) <= K ->
  zsumf esz (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) <= S ->
  4096 + S + K * (FR_NMAX + 4095) + FR_NMAX + FR_COEF * R <= alloc_ceiling ->
  FR_KW * K + R <= target_alloc_limit ->
  noaccess_pos mo ->
  FRONTR mo R.
Proof.
  intros mo R K S HR HK HS Hroom HKW NP. split; [|exact NP]. split; [exact HR|]. split.
  - unfold fr_phi. rewrite zsumf_jcost. unfold FR_NMAX, FR_COEF in *. nia.
  - unfold fr_count, FR_KW in *. lia.
Qed.

(* [comment removed for export] *)
Theorem FRONTR_placeable_big : forall mo R n, LOK bsegs mo -> FRONTR mo R -> 0 <= n -> n <= FR_NBIG -> FR_RBIG <= R ->
  mmap_placeable mo n.
Proof.
  intros mo R n HO HF Hn Hle HR.
  destruct (Z_le_gt_dec n FR_NMAX) as [Hs|Hb]; [exact (FRONTR_placeable mo R n HO HF Hn Hs)|].
  destruct HF as [[H0 [H HK]] _]. apply (mmap_placeable_gap bsegs mo n HO).
  apply vm_gap_available_of_sum; [exact Hn|]. rewrite (lok_top _ _ HO).
  unfold fr_phi in H. rewrite zsumf_jcost in *. unfold fr_count in HK.
  set (K := Z.of_nat (length (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)))) in *.
  set (S := zsumf esz (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo))) in *.
  assert (HK0 : 0 <= K) by (unfold K; lia).
  assert (HKB : K <= 2^19) by (unfold FR_KW, FR_RBIG, target_alloc_limit in *; lia).
  unfold FR_COEF, FR_NMAX, FR_NBIG, FR_RBIG in *. nia.
Qed.

End CeilWrap.
