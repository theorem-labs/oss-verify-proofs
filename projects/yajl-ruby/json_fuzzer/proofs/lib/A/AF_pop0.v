(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FinFun.
From stdpp Require Import base list gmap.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanOps AsanRep AsanKern AsanWf1 AsanBudget2 AsanRealloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_bundle A_balloc5 A_rtok5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section POPM.
Variable E : aenv.
Let SB : Z := ae_space_beg E.

(* [comment removed for export] *)
Definition pop_fresh (au size new : Z) : list Z := rev (map (fun i => (au + i * size) / 16) (ziota 0 (Z.to_nat new))).

Definition st_user (c : Z) (a : astate) : astate :=
  let r := get_region a c in
  upd_cache_mapped (fun m => m + kUserMapSize)
    (upd_ts (ts_on_mmap kUserMapSize)
       (set_region c (mkRegion (rg_mapped_user r + kUserMapSize) (rg_alloc_user r) (rg_free r) (rg_mapped_fa r) (rg_n_allocated r) (rg_n_freed r)) a)).
Definition st_fa (c : Z) (a : astate) : astate :=
  let r := get_region a c in
  upd_ts (ts_on_mmap kFreeArrayMapSize)
    (set_region c (mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_free r) (rg_mapped_fa r + kFreeArrayMapSize) (rg_n_allocated r) (rg_n_freed r)) a).
Definition st_fin (c : Z) (a : astate) : astate :=
  let r := get_region a c in let size := class_size c in let new := (rg_mapped_user r - rg_alloc_user r) / size in
  set_region c (mkRegion (rg_mapped_user r) (rg_alloc_user r + new * size) (rg_free r ++ pop_fresh (rg_alloc_user r) size new) (rg_mapped_fa r)
                         (rg_n_allocated r) (rg_n_freed r)) a.

(* [comment removed for export] *)
Lemma get_region_upd_cache_mapped : forall f s c, get_region (upd_cache_mapped f s) c = get_region s c.
Proof. aceil. intros f s c0; destruct s; reflexivity. Qed.
Lemma get_region_upd_ts : forall f s c, get_region (upd_ts f s) c = get_region s c.
Proof. aceil. intros f s c0; destruct s; reflexivity. Qed.
Lemma st_user_region : forall c a, get_region (st_user c a) c =
  let r := get_region a c in mkRegion (rg_mapped_user r + kUserMapSize) (rg_alloc_user r) (rg_free r) (rg_mapped_fa r) (rg_n_allocated r) (rg_n_freed r).
Proof. aceil. intros c a. unfold st_user. cbv zeta. rewrite get_region_upd_cache_mapped, get_region_upd_ts. apply get_set_region_eq. Qed.
Lemma st_fa_region : forall c a, get_region (st_fa c a) c =
  let r := get_region a c in mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_free r) (rg_mapped_fa r + kFreeArrayMapSize) (rg_n_allocated r) (rg_n_freed r).
Proof. aceil. intros c a. unfold st_fa. cbv zeta. rewrite get_region_upd_ts. apply get_set_region_eq. Qed.
Lemma st_fin_region : forall c a, get_region (st_fin c a) c =
  let r := get_region a c in let size := class_size c in let new := (rg_mapped_user r - rg_alloc_user r) / size in
  mkRegion (rg_mapped_user r) (rg_alloc_user r + new * size) (rg_free r ++ pop_fresh (rg_alloc_user r) size new) (rg_mapped_fa r) (rg_n_allocated r) (rg_n_freed r).
Proof. aceil. intros c a. unfold st_fin. cbv zeta. apply get_set_region_eq. Qed.
Lemma st_user_other : forall c a c', c <> c' -> get_region (st_user c a) c' = get_region a c'.
Proof. aceil. intros c a c' H. unfold st_user. cbv zeta. rewrite get_region_upd_cache_mapped, get_region_upd_ts. apply get_set_region_ne. exact H. Qed.
Lemma st_fa_other : forall c a c', c <> c' -> get_region (st_fa c a) c' = get_region a c'.
Proof. aceil. intros c a c' H. unfold st_fa. cbv zeta. rewrite get_region_upd_ts. apply get_set_region_ne. exact H. Qed.
Lemma st_fin_other : forall c a c', c <> c' -> get_region (st_fin c a) c' = get_region a c'.
Proof. aceil. intros c a c' H. unfold st_fin. cbv zeta. apply get_set_region_ne. exact H. Qed.

(* [comment removed for export] *)
Definition pop_same (a a' : astate) : Prop :=
  as_cache_inited a' = as_cache_inited a /\ as_cache a' = as_cache a /\ as_cache_stale a' = as_cache_stale a /\ as_cache_allocated a' = as_cache_allocated a
  /\ as_ptr_committed a' = as_ptr_committed a /\ as_sec a' = as_sec a /\ as_sec_stale a' = as_sec_stale a /\ as_sec_stats a' = as_sec_stats a
  /\ as_glob_allocated a' = as_glob_allocated a /\ as_glob_mapped a' = as_glob_mapped a /\ as_oom a' = as_oom a
  /\ as_chunks a' = as_chunks a /\ as_dead a' = as_dead a /\ as_tq a' = as_tq a /\ as_gq a' = as_gq a /\ as_keys a' = as_keys a
  /\ as_frames a' = as_frames a /\ as_ia_inited a' = as_ia_inited a /\ as_residue a' = as_residue a /\ as_nprim_ever a' = as_nprim_ever a
  /\ as_node_blocks a' = as_node_blocks a /\ as_store_blocks a' = as_store_blocks a /\ as_store_stored a' = as_store_stored a
  /\ as_ndepot_ins a' = as_ndepot_ins a /\ as_everc a' = as_everc a.
Lemma pop_same_refl : forall a, pop_same a a. Proof. intros a; repeat split; reflexivity. Qed.
Lemma pop_same_trans : forall a b d, pop_same a b -> pop_same b d -> pop_same a d.
Proof. aceil. intros a b d H1 H2. unfold pop_same in *. decompose [and] H1; decompose [and] H2. repeat split; congruence. Qed.
Lemma pop_same_user : forall c a, pop_same a (st_user c a). Proof. intros c a; destruct a; repeat split; reflexivity. Qed.
Lemma pop_same_fa : forall c a, pop_same a (st_fa c a). Proof. intros c a; destruct a; repeat split; reflexivity. Qed.
Lemma pop_same_fin : forall c a, pop_same a (st_fin c a). Proof. intros c a; destruct a; repeat split; reflexivity. Qed.

Lemma st_user_ts : forall c a, as_ts (st_user c a) = ts_on_mmap kUserMapSize (as_ts a). Proof. intros c a; destruct a; reflexivity. Qed.
Lemma st_user_cm : forall c a, as_cache_mapped (st_user c a) = as_cache_mapped a + kUserMapSize. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma st_fa_ts : forall c a, as_ts (st_fa c a) = ts_on_mmap kFreeArrayMapSize (as_ts a). Proof. intros c a; destruct a; reflexivity. Qed.
Lemma st_fa_cm : forall c a, as_cache_mapped (st_fa c a) = as_cache_mapped a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma st_fin_ts : forall c a, as_ts (st_fin c a) = as_ts a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma st_fin_cm : forall c a, as_cache_mapped (st_fin c a) = as_cache_mapped a. Proof. intros c a; destruct a; reflexivity. Qed.

(* [comment removed for export] *)
Definition pop_total (c req : Z) (a : astate) : Z := rg_alloc_user (get_region a c) + req * class_size c.
Definition pop_tf (c : Z) (a : astate) : Z :=
  let r := get_region a c in rg_num_freed r + (rg_mapped_user r - rg_alloc_user r) / class_size c.

Lemma arun_acall : forall e s ans orc f, arun (S f) (acall e s) (ans :: orc) = Some (s, ONorm ans, [e], orc).
Proof. aceil. intros. cbn. destruct f; reflexivity. Qed.

Section Runs.
Variables (c req : Z) (a : astate).
Let r := get_region a c.
Let size := class_size c.
Hypothesis Hc : 1 <= c <= 30.
Hypothesis HREQ : 1 <= req.
Hypothesis RS : req * size <= 65536.
Hypothesis R0 : 0 <= rg_alloc_user r <= rg_mapped_user r.
Hypothesis ROOM700 : rg_mapped_user r + kUserMapSize <= kFreeArrayOffset.

Let SZ : 32 <= size <= 65536. Proof. exact (proj2 (class_size_mod c Hc)). Qed.

(* [comment removed for export] *)
Definition pop_phase1 : AM bool :=
  if rg_mapped_user r <? pop_total c req a then
    let user_map := round_up (pop_total c req a - rg_mapped_user r) kUserMapSize in
    acheck (rg_mapped_user r + user_map <=? kFreeArrayOffset) 700 ;;;
    ok <- call_mmap_fixed (region_beg SB c + rg_mapped_user r) user_map ;;
    if ok then
      aupd (fun s => upd_cache_mapped (fun m => m + user_map)
                       (upd_ts (ts_on_mmap user_map)
                          (set_region c (mkRegion (rg_mapped_user r + user_map) (rg_alloc_user r) (rg_free r) (rg_mapped_fa r)
                                                 (rg_n_allocated r) (rg_n_freed r)) s))) ;;;
      aret true
    else aret false
  else aret true.
(* [comment removed for export] *)
Definition pop_phase2 (ok1 : bool) : AM bool :=
  if negb ok1 then aret false else
  s1 <- aget ;;
  let r1 := get_region s1 c in
  let new_chunks := (rg_mapped_user r1 - rg_alloc_user r1) / size in
  let total_freed := rg_num_freed r1 + new_chunks in
  ok2 <- ensure_free_array_space E c total_freed ;;
  if negb ok2 then aret false else
  s2 <- aget ;;
  let r2 := get_region s2 c in
  let fresh := rev (map (fun i => (rg_alloc_user r2 + i * size) / 16) (ziota 0 (Z.to_nat new_chunks))) in
  aupd (set_region c (mkRegion (rg_mapped_user r2) (rg_alloc_user r2 + new_chunks * size) (rg_free r2 ++ fresh) (rg_mapped_fa r2)
                              (rg_n_allocated r2) (rg_n_freed r2))) ;;;
  aret true.

Lemma pop_unfold : populate_free_array E c req a = abind pop_phase1 pop_phase2 a.
Proof. aceil. reflexivity. Qed.

Lemma user_map_one : rg_mapped_user r < pop_total c req a -> round_up (pop_total c req a - rg_mapped_user r) kUserMapSize = kUserMapSize.
Proof. aceil. intros H. apply round_up_small; [reflexivity|]. unfold pop_total, kUserMapSize in *. subst r size. lia. Qed.

Lemma run_phase1_nogrow : pop_total c req a <= rg_mapped_user r -> forall orc, arun 0%nat (pop_phase1 a) orc = Some (a, ONorm true, [], orc).
Proof. aceil. intros H orc. unfold pop_phase1. replace (_ <? _) with false by (symmetry; apply Z.ltb_ge; exact H). reflexivity. Qed.

Lemma run_phase1_grant : rg_mapped_user r < pop_total c req a -> forall orc,
  arun 1%nat (pop_phase1 a) (AnsOk (region_beg SB c + rg_mapped_user r) :: orc)
  = Some (st_user c a, ONorm true, [AEvMmap (region_beg SB c + rg_mapped_user r) kUserMapSize kProtRw kFlagsFixedRw], orc).
Proof. aceil.
  intros H orc. unfold pop_phase1. replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; exact H).
  rewrite (user_map_one H). unfold acheck. replace (_ <=? _) with true by (symmetry; apply Z.leb_le; exact ROOM700).
  unfold call_mmap_fixed. cbn -[st_user region_beg kUserMapSize get_region set_region upd_ts upd_cache_mapped Z.add Z.eqb].
  rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma run_phase1_enomem : rg_mapped_user r < pop_total c req a -> forall orc,
  arun 1%nat (pop_phase1 a) (AnsErr ENOMEM :: orc)
  = Some (a, ONorm false, [AEvMmap (region_beg SB c + rg_mapped_user r) kUserMapSize kProtRw kFlagsFixedRw], orc).
Proof. aceil.
  intros H orc. unfold pop_phase1. replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; exact H).
  rewrite (user_map_one H). unfold acheck. replace (_ <=? _) with true by (symmetry; apply Z.leb_le; exact ROOM700).
  unfold call_mmap_fixed. cbn -[st_user region_beg kUserMapSize get_region set_region upd_ts upd_cache_mapped Z.add Z.eqb].
  reflexivity.
Qed.
End Runs.

(* [comment removed for export] *)
Lemma pop_run : forall c req a f1 f2 orc a1 ok1 evs1 orc1 a2 o evs2 orc2,
  arun f1 (pop_phase1 c req a a) orc = Some (a1, ONorm ok1, evs1, orc1) ->
  arun f2 (pop_phase2 c ok1 a1) orc1 = Some (a2, o, evs2, orc2) ->
  exists f, arun f (populate_free_array E c req a) orc = Some (a2, o, evs1 ++ evs2, orc2).
Proof. aceil. intros. exists (f1 + f2)%nat. rewrite pop_unfold. eapply arun_abind; eassumption. Qed.

Lemma phase2_false : forall c a1 orc, arun 0%nat (pop_phase2 c false a1) orc = Some (a1, ONorm false, [], orc).
Proof. aceil. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma roundup_next : forall m x, 0 <= m -> m mod 262144 = 0 -> m < x <= m + 262144 -> round_up x 262144 = m + 262144.
Proof. aceil. intros m x Hm HM HX. unfold round_up. Z.div_mod_to_equations. nia. Qed.

Section Runs2.
Variables (c : Z) (a1 : astate).
Let r1 := get_region a1 c.
Hypothesis Hc : 1 <= c <= 30.
Hypothesis MFA0 : 0 <= rg_mapped_fa r1.
Hypothesis MFAM : rg_mapped_fa r1 mod kFreeArrayMapSize = 0.
Hypothesis FA1 : 4 * pop_tf c a1 <= rg_mapped_fa r1 + kFreeArrayMapSize.
Hypothesis FAS : rg_mapped_fa r1 + kFreeArrayMapSize <= kFreeArraySize.

Lemma efa_run_nogrow : 4 * pop_tf c a1 <= rg_mapped_fa r1 -> forall orc,
  arun 0%nat (ensure_free_array_space E c (pop_tf c a1) a1) orc = Some (a1, ONorm true, [], orc).
Proof. aceil.
  intros H orc. unfold ensure_free_array_space. cbn -[get_region Z.ltb Z.mul pop_tf].
  subst r1. replace (_ <? _) with false by (symmetry; apply Z.ltb_ge; exact H). reflexivity.
Qed.

Let NEWFA : rg_mapped_fa r1 < 4 * pop_tf c a1 -> round_up (4 * pop_tf c a1) kFreeArrayMapSize = rg_mapped_fa r1 + kFreeArrayMapSize.
Proof. aceil. intros H. unfold kFreeArrayMapSize in *. apply roundup_next; [exact MFA0| exact MFAM| split; [exact H| exact FA1]]. Qed.

Lemma efa_run_grant : rg_mapped_fa r1 < 4 * pop_tf c a1 -> forall orc,
  arun 1%nat (ensure_free_array_space E c (pop_tf c a1) a1) (AnsOk (free_array SB c + rg_mapped_fa r1) :: orc)
  = Some (st_fa c a1, ONorm true, [AEvMmap (free_array SB c + rg_mapped_fa r1) kFreeArrayMapSize kProtRw kFlagsFixedRw], orc).
Proof. aceil.
  intros H orc. unfold ensure_free_array_space.
  cbn -[get_region Z.ltb Z.leb Z.eqb Z.mul Z.add Z.sub pop_tf round_up free_array kFreeArrayMapSize kFreeArraySize set_region upd_ts st_fa ts_on_mmap].
  subst r1. replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; exact H). rewrite (NEWFA H).
  unfold acheck. replace (_ <=? _) with true by (symmetry; apply Z.leb_le; exact FAS).
  cbn -[get_region Z.eqb Z.mul Z.add Z.sub pop_tf free_array kFreeArrayMapSize set_region upd_ts st_fa ts_on_mmap].
  rewrite Z.eqb_refl. replace (rg_mapped_fa (get_region a1 c) + kFreeArrayMapSize - rg_mapped_fa (get_region a1 c)) with kFreeArrayMapSize by lia.
  reflexivity.
Qed.

Lemma efa_run_enomem : rg_mapped_fa r1 < 4 * pop_tf c a1 -> forall orc,
  arun 1%nat (ensure_free_array_space E c (pop_tf c a1) a1) (AnsErr ENOMEM :: orc)
  = Some (a1, ONorm false, [AEvMmap (free_array SB c + rg_mapped_fa r1) kFreeArrayMapSize kProtRw kFlagsFixedRw], orc).
Proof. aceil.
  intros H orc. unfold ensure_free_array_space.
  cbn -[get_region Z.ltb Z.leb Z.eqb Z.mul Z.add Z.sub pop_tf round_up free_array kFreeArrayMapSize kFreeArraySize set_region upd_ts st_fa ts_on_mmap ENOMEM].
  subst r1. replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; exact H). rewrite (NEWFA H).
  unfold acheck. replace (_ <=? _) with true by (symmetry; apply Z.leb_le; exact FAS).
  cbn -[get_region Z.eqb Z.mul Z.add Z.sub pop_tf free_array kFreeArrayMapSize set_region upd_ts st_fa ts_on_mmap ENOMEM].
  rewrite Z.eqb_refl. replace (rg_mapped_fa (get_region a1 c) + kFreeArrayMapSize - rg_mapped_fa (get_region a1 c)) with kFreeArrayMapSize by lia.
  reflexivity.
Qed.

(* [comment removed for export] *)
Lemma phase2_true : forall f orc s2 ok2 evs orc',
  arun f (ensure_free_array_space E c (pop_tf c a1) a1) orc = Some (s2, ONorm ok2, evs, orc') ->
  rg_mapped_user (get_region s2 c) = rg_mapped_user r1 -> rg_alloc_user (get_region s2 c) = rg_alloc_user r1 ->
  exists f', arun f' (pop_phase2 c true a1) orc = Some ((if ok2 then st_fin c s2 else s2), ONorm ok2, evs, orc').
Proof. aceil.
  intros f orc s2 ok2 evs orc' RUN EM EA. unfold pop_phase2. cbn [negb].
  exists (0 + (f + (0 + 0)))%nat. replace evs with ([] ++ (evs ++ ([] ++ []))) by (rewrite app_nil_r; reflexivity).
  eapply (arun_abind aget); [reflexivity|]. cbv beta zeta.
  eapply arun_abind; [unfold pop_tf in RUN; subst r1; exact RUN|]. cbv beta.
  destruct ok2; cbn [negb].
  - eapply (arun_abind aget); [reflexivity|]. cbv beta.
    unfold st_fin, pop_fresh. cbv zeta. subst r1. rewrite EM, EA. reflexivity.
  - reflexivity.
Qed.
End Runs2.

(* [comment removed for export] *)
Lemma sumZ_upd1 : forall (f g : Z -> Z) (x d : Z) (l : list Z),
  List.NoDup l -> (forall y, In y l -> y <> x -> g y = f y) -> g x = f x + d ->
  sumZ g l = sumZ f l + (if in_dec Z.eq_dec x l then d else 0).
Proof. aceil.
  intros f g x d l. induction l as [|y l IH]; intros ND HO HX; cbn [sumZ]; [destruct (in_dec Z.eq_dec x []); [destruct i|lia]|].
  inversion ND as [|y' l' NI ND']; subst.
  specialize (IH ND' ltac:(intros z Hz Hne; apply HO; [right; exact Hz| exact Hne]) HX).
  destruct (Z.eq_dec y x) as [->|NE].
  - rewrite HX, IH. destruct (in_dec Z.eq_dec x l) as [C|C]; [exfalso; exact (NI C)|].
    destruct (in_dec Z.eq_dec x (x :: l)) as [_|C2]; [lia| exfalso; apply C2; left; reflexivity].
  - rewrite (HO y (or_introl eq_refl) NE), IH. destruct (in_dec Z.eq_dec x l) as [C|C]; destruct (in_dec Z.eq_dec x (y :: l)) as [C2|C2]; try lia.
    + exfalso. apply C2. right. exact C.
    + exfalso. destruct C2 as [E'|E']; [exact (NE E')| exact (C E')].
Qed.
Lemma classes30_nodup : List.NoDup classes30.
Proof. aceil. unfold classes30. apply Injective_map_NoDup; [intros x y H; lia| apply seq_NoDup]. Qed.
Lemma classes30_in : forall c, 1 <= c <= 30 -> In c classes30.
Proof. aceil. intros c Hc. unfold classes30. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. Qed.

Lemma regions_bytes_upd : forall a a' c du df, 1 <= c <= 30 ->
  (forall c', c <> c' -> get_region a' c' = get_region a c') ->
  rg_mapped_user (get_region a' c) = rg_mapped_user (get_region a c) + du ->
  rg_mapped_fa (get_region a' c) = rg_mapped_fa (get_region a c) + df ->
  regions_bytes a' = regions_bytes a + du + df.
Proof. aceil.
  intros a a' c du df Hc OTH EU EF. rewrite !regions_bytes_sumZ.
  rewrite (sumZ_upd1 (fun c0 => rg_mapped_user (get_region a c0) + rg_mapped_fa (get_region a c0))
                     (fun c0 => rg_mapped_user (get_region a' c0) + rg_mapped_fa (get_region a' c0)) c (du + df) classes30 classes30_nodup).
  - destruct (in_dec Z.eq_dec c classes30) as [_|C]; [lia| exfalso; exact (C (classes30_in c Hc))].
  - intros y _ Hy. rewrite (OTH y ltac:(lia)). reflexivity.
  - rewrite EU, EF. lia.
Qed.

Lemma regions_bytes_st_user : forall c a, 1 <= c <= 30 -> regions_bytes (st_user c a) = regions_bytes a + kUserMapSize.
Proof. aceil.
  intros c a Hc. rewrite (regions_bytes_upd a (st_user c a) c kUserMapSize 0 Hc (st_user_other c a)); [lia| |]; rewrite st_user_region; cbn; lia.
Qed.
Lemma regions_bytes_st_fa : forall c a, 1 <= c <= 30 -> regions_bytes (st_fa c a) = regions_bytes a + kFreeArrayMapSize.
Proof. aceil.
  intros c a Hc. rewrite (regions_bytes_upd a (st_fa c a) c 0 kFreeArrayMapSize Hc (st_fa_other c a)); [lia| |]; rewrite st_fa_region; cbn; lia.
Qed.
Lemma regions_bytes_st_fin : forall c a, 1 <= c <= 30 -> regions_bytes (st_fin c a) = regions_bytes a.
Proof. aceil.
  intros c a Hc. rewrite (regions_bytes_upd a (st_fin c a) c 0 0 Hc (st_fin_other c a)); [lia| |]; rewrite st_fin_region; cbn; lia.
Qed.

Lemma a_eager_bytes_st_user : forall c a, 1 <= c <= 30 -> a_eager_bytes (st_user c a) = a_eager_bytes a + kUserMapSize.
Proof. aceil. intros c a Hc. unfold a_eager_bytes, AsanState.sec_bytes. rewrite (regions_bytes_st_user c a Hc). destruct a; cbn -[regions_bytes Z.add Z.mul Z.eqb kUserMapSize kPtrArrayCommit]. lia. Qed.
Lemma a_eager_bytes_st_fa : forall c a, 1 <= c <= 30 -> a_eager_bytes (st_fa c a) = a_eager_bytes a + kFreeArrayMapSize.
Proof. aceil. intros c a Hc. unfold a_eager_bytes, AsanState.sec_bytes. rewrite (regions_bytes_st_fa c a Hc). destruct a; cbn -[regions_bytes Z.add Z.mul Z.eqb kFreeArrayMapSize kPtrArrayCommit]. lia. Qed.

Lemma gapR_st_user : forall c a, 1 <= c <= 30 -> gapR (st_user c a) = gapR a - kUserMapSize.
Proof. aceil. intros c a Hc. unfold gapR. rewrite (regions_bytes_st_user c a Hc). destruct a; cbn -[regions_bytes Z.add Z.mul Z.sub kUserMapSize A_rtok5.kBatchPages]. lia. Qed.
Lemma gapR_st_fa : forall c a, 1 <= c <= 30 -> gapR (st_fa c a) = gapR a - kFreeArrayMapSize.
Proof. aceil. intros c a Hc. unfold gapR. rewrite (regions_bytes_st_fa c a Hc). destruct a; cbn -[regions_bytes Z.add Z.mul Z.sub kFreeArrayMapSize A_rtok5.kBatchPages]. lia. Qed.
Lemma gapD_st_user : forall c a, gapD (st_user c a) = gapD a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma gapD_st_fa : forall c a, gapD (st_fa c a) = gapD a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma gapP_st_user : forall c a, gapP (st_user c a) = gapP a. Proof. intros c a; destruct a; reflexivity. Qed.
Lemma gapP_st_fa : forall c a, gapP (st_fa c a) = gapP a. Proof. intros c a; destruct a; reflexivity. Qed.

Lemma same_fp_st_fin : forall c a, 1 <= c <= 30 -> same_fp a (st_fin c a).
Proof. aceil.
  intros c a Hc. unfold same_fp. rewrite (regions_bytes_st_fin c a Hc).
  pose proof (pop_same_fin c a) as PS. unfold pop_same in PS. decompose [and] PS. repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma AKern_mapped_ext : forall E' s s' mo,
  (forall c, 1 <= c <= kLargestClassID -> rg_mapped_user (get_region s' c) = rg_mapped_user (get_region s c)
                                          /\ rg_mapped_fa (get_region s' c) = rg_mapped_fa (get_region s c)) ->
  as_ptr_committed s' = as_ptr_committed s -> as_sec s' = as_sec s ->
  as_node_blocks s' = as_node_blocks s -> as_store_blocks s' = as_store_blocks s ->
  AKern E' s mo -> AKern E' s' mo.
Proof. aceil.
  intros E' s s' mo R P S NB SB' K.
  destruct K; constructor; rewrite ?P, ?S, ?NB, ?SB'; auto.
  - intros c Hc. destruct (R c Hc) as [-> _]. auto.
  - intros c Hc. destruct (R c Hc) as [_ ->]. auto.
  - intros e He. destruct (ak_lazy e He) as [X|[X|[X|[X|X]]]]; [left| right; left| right; right; left| right; right; right; left| right; right; right; right]; try exact X.
    destruct X as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|]. split; intros c Hc; destruct (R c Hc) as [E1 E2]; rewrite ?E1, ?E2; auto.
Qed.
Lemma AKern_st_fin : forall c a mo, AKern E a mo -> AKern E (st_fin c a) mo.
Proof. aceil.
  intros c a mo K. eapply AKern_mapped_ext; [| | | | | exact K].
  - intros c' Hc'. destruct (Z.eq_dec c c') as [<-|NE]; [rewrite st_fin_region; cbn; auto| rewrite (st_fin_other c a c' NE); auto].
  - destruct a; reflexivity. - destruct a; reflexivity. - destruct a; reflexivity. - destruct a; reflexivity.
Qed.
End POPM.
End RC__1.
