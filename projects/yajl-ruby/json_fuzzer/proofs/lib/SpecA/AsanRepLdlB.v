(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanRep AsanKern AsanDepot
  AsanWf1 AsanWf3 AsanWf4 AsanWf5 AsanWf8 AsanClient AsanRepFrame AsanRepFrame2 AsanBudget AsanHit AsanRepHitB AsanRepX AsanRepCaB AsanRepSecB AsanRepEnqB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SWAP.
Context {X : Type}.
Lemma swap_remove_shape : forall (l : list X) i h, nth_error l i = Some h ->
  (exists l1, l = l1 ++ [h] /\ removelast (list_set l i (List.last l h)) = l1 /\ length l1 = i /\ List.last l h = h)
  \/ (exists l1 l2 z, l = l1 ++ h :: l2 ++ [z] /\ removelast (list_set l i (List.last l h)) = l1 ++ z :: l2 /\ length l1 = i /\ List.last l h = z).
Proof.
  intros l i h Hn. destruct (nth_error_split l i h Hn) as (l1 & l2 & -> & L1).
  destruct l2 as [|y l2'].
  - left. exists l1. rewrite last_last. rewrite <- L1, list_set_app, removelast_app_single. auto.
  - right. pose proof (app_removelast_last h (l := y :: l2') ltac:(discriminate)) as E. rewrite <- removelast_eq in E.
    set (l2 := removelast (y :: l2')) in *. set (z := List.last (y :: l2') h) in *.
    exists l1, l2, z. rewrite E.
    assert (LZ : List.last (l1 ++ h :: l2 ++ [z]) h = z).
    { replace (l1 ++ h :: l2 ++ [z]) with ((l1 ++ h :: l2) ++ [z]) by (rewrite <- app_assoc; reflexivity). apply last_last. }
    rewrite LZ. split; [reflexivity|]. split; [| auto].
    rewrite <- L1, list_set_app. replace (l1 ++ z :: l2 ++ [z]) with ((l1 ++ z :: l2) ++ [z]) by (rewrite <- app_assoc; reflexivity).
    apply removelast_app_single.
Qed.

Lemma NoDup_app_cons_inv : forall (l1 l2 : list X) x, List.NoDup (l1 ++ x :: l2) -> ~ In x l1 /\ ~ In x l2 /\ List.NoDup (l1 ++ l2).
Proof.
  intros l1 l2 x ND. pose proof (List.NoDup_remove _ _ _ ND) as [ND' NI].
  split; [intros H; apply NI; apply in_app_iff; left; exact H|]. split; [intros H; apply NI; apply in_app_iff; right; exact H| exact ND'].
Qed.

Lemma nth_error_lt : forall (l : list X) j y, nth_error l j = Some y -> (j < length l)%nat.
Proof. intros l j y H. apply (proj1 (nth_error_Some l j)). rewrite H. discriminate. Qed.

(* [comment removed for export] *)
Lemma swap_remove_facts : forall (l : list X) i h, nth_error l i = Some h -> List.NoDup l ->
  let l' := removelast (list_set l i (List.last l h)) in
  length l = S (length l')
  /\ (forall y, In y l' <-> In y l /\ y <> h)
  /\ (forall j y, nth_error l' j = Some y ->
        (j = i /\ y = List.last l h /\ y <> h /\ nth_error l (length l') = Some y) \/ (j <> i /\ nth_error l j = Some y /\ y <> h /\ y <> List.last l h))
  /\ In (List.last l h) l.
Proof.
  intros l i h Hn ND l'.
  destruct (swap_remove_shape l i h Hn) as [(l1 & El & El' & L1 & LL)|(l1 & l2 & z & El & El' & L1 & LL)]; subst l'; rewrite El', LL; rewrite El in ND |- *.
  - pose proof (NoDup_app_cons_inv l1 [] h ND) as (N1 & _ & _).
    split; [rewrite length_app; cbn [length]; lia|]. split.
    { intros y. rewrite in_app_iff. cbn [In]. split; [intros H; split; [left; exact H| intros ->; exact (N1 H)]|].
      intros [[H|[H|[]]] NE]; [exact H| exfalso; exact (NE (eq_sym H))]. }
    split.
    { intros j y Hj. right. assert (LT : (j < length l1)%nat) by exact (nth_error_lt _ _ _ Hj).
      split; [lia|]. split; [rewrite nth_error_app1 by exact LT; exact Hj|].
      pose proof (nth_error_In _ _ Hj) as IN. split; intros ->; exact (N1 IN). }
    apply in_app_iff. right. left. reflexivity.
  - pose proof (NoDup_app_cons_inv l1 (l2 ++ [z]) h ND) as (N1 & N2 & ND12).
    replace (l1 ++ l2 ++ [z]) with ((l1 ++ l2) ++ [z]) in ND12 by (rewrite <- app_assoc; reflexivity).
    pose proof (NoDup_app_cons_inv (l1 ++ l2) [] z ND12) as (NZ & _ & _). rewrite in_app_iff in NZ.
    assert (ZH : z <> h) by (intros ->; apply N2; apply in_app_iff; right; left; reflexivity).
    split; [rewrite !length_app; cbn [length]; rewrite length_app; cbn [length]; lia|]. split.
    { intros y. rewrite !in_app_iff. cbn [In]. rewrite in_app_iff. cbn [In]. split.
      - intros [H|[<-|H]]; [split; [left; exact H| intros ->; exact (N1 H)]| split; [right; right; right; left; reflexivity| exact ZH]|].
        split; [right; right; left; exact H| intros ->; apply N2; apply in_app_iff; left; exact H].
      - intros [[H|[H|[H|[H|[]]]]] NE]; [left; exact H| exfalso; exact (NE (eq_sym H))| right; right; exact H| right; left; exact H]. }
    split.
    { intros j y Hj. destruct (Nat.eq_dec j i) as [->|NE].
      - left. rewrite <- L1, nth_error_app2, Nat.sub_diag in Hj by lia. cbn in Hj. injection Hj as <-. split; [reflexivity|]. split; [reflexivity|]. split; [exact ZH|].
        rewrite length_app. cbn [length]. replace (l1 ++ h :: l2 ++ [z]) with ((l1 ++ h :: l2) ++ [z]) by (rewrite <- app_assoc; reflexivity).
        rewrite nth_error_app2 by (rewrite length_app; cbn [length]; lia). rewrite length_app. cbn [length]. rewrite Nat.add_succ_r, Nat.sub_diag. reflexivity.
      - right. split; [exact NE|]. pose proof (nth_error_In _ _ Hj) as IN. rewrite in_app_iff in IN. cbn [In] in IN.
        destruct (Nat.lt_ge_cases j (length l1)) as [LT|GE].
        + rewrite nth_error_app1 in Hj by exact LT. rewrite nth_error_app1 by exact LT. split; [exact Hj|]. pose proof (nth_error_In _ _ Hj) as I1.
          split; intros ->; [exact (N1 I1)| exact (NZ (or_introl I1))].
        + rewrite nth_error_app2 in Hj |- * by lia. destruct (j - length l1)%nat as [|k] eqn:Dk; [lia|]. cbn [nth_error] in Hj |- *.
          rewrite nth_error_app1 by exact (nth_error_lt _ _ _ Hj). split; [exact Hj|]. pose proof (nth_error_In _ _ Hj) as I2.
          split; intros ->; [apply N2; apply in_app_iff; left; exact I2| exact (NZ (or_intror I2))]. }
    apply in_app_iff. right. right. apply in_app_iff. right. left. reflexivity.
Qed.
End SWAP.

Lemma existsb_ext_In : forall {X} (f : X -> bool) (l1 l2 : list X),
  (forall x, f x = true -> (In x l1 <-> In x l2)) -> existsb f l1 = existsb f l2.
Proof.
  intros X f l1 l2 H. destruct (existsb f l1) eqn:A; destruct (existsb f l2) eqn:B; try reflexivity.
  - apply existsb_exists in A as (x & Hx & Fx). assert (B' : existsb f l2 = true) by (apply existsb_exists; exists x; split; [apply (H x Fx); exact Hx| exact Fx]). congruence.
  - apply existsb_exists in B as (x & Hx & Fx). assert (A' : existsb f l1 = true) by (apply existsb_exists; exists x; split; [apply (H x Fx); exact Hx| exact Fx]). congruence.
Qed.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RLD.
Variable segs : list Segment.
Variable E : aenv.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation RW := (rw_cells segs).
#[warnings="-notation-for-abbreviation"] Notation SB := (ae_space_beg E).
#[warnings="-notation-for-abbreviation"] Notation T := (ae_thread E).
#[warnings="-notation-for-abbreviation"] Notation RI := (ae_region_info E).
#[warnings="-notation-for-abbreviation"] Notation PA := (ae_ptr_array E).
#[warnings="-notation-for-abbreviation"] Notation INST := (ae_instance E).
#[warnings="-notation-for-abbreviation"] Notation AREP := (ARep segs E (DepotR segs E)).

(* [comment removed for export] *)
Lemma wr_at_join : forall (mm : mem) a n1 n2, 0 <= n1 -> 0 <= n2 -> wr_at segs mm a n1 -> wr_at segs mm (a + n1) n2 -> wr_at segs mm a (n1 + n2).
Proof.
  intros mm a n1 n2 P1 P2 (A0 & A1 & W1) (B0 & B1 & W2). split; [exact A0|]. split; [lia|].
  intros k Hk. destruct (Z_lt_le_dec k n1) as [LT|GE]; [apply W1; lia|]. replace (a + k) with (a + n1 + (k - n1)) by lia. apply W2. lia.
Qed.
Lemma rw_wr : forall (mm : mem) a cs, RW mm a cs -> wr_at segs mm a (Z.of_nat (cells_size cs)).
Proof. intros mm a cs [_ W]. exact W. Qed.

(* [comment removed for export] *)
Definition ldl_st (cb : Z) (cm : chunkmeta) (sc : secchunk) (i : nat) (a : astate) : astate :=
  let n := cm_n cm in let msz := sc_map_size sc in
  let a1 := upd_chunks (delete cb) (upd_ts (ts_on_real_free n) a) in
  let secl := as_sec a in let lastc := List.last secl sc in
  let a2 := upd_glob (fun x => x - msz) (fun x => x - msz)
              (upd_sec_stats (fun st => mkSecStats (ss_n_allocs st) (ss_n_frees st + 1) (ss_cur st - msz) (ss_max st) (ss_by_size_log st))
                (upd_sec_stale (fun st => <[Z.of_nat (Nat.pred (length secl)) := sc_map_beg lastc]> st)
                  (upd_sec (fun _ => removelast (list_set secl i lastc)) a1))) in
  upd_ts (ts_on_munmap msz) a2.

Section LDL.
Variables (D : list batch) (s : astate) (m m' : mem) (lo cb : Z) (cm : chunkmeta) (sc : secchunk) (i : nat) (qi qj : Z) (junk : list word).
#[warnings="-notation-for-abbreviation"] Notation n := (cm_n cm).
#[warnings="-notation-for-abbreviation"] Notation A := (sc_map_beg sc).
#[warnings="-notation-for-abbreviation"] Notation L := (sc_map_size sc).
#[warnings="-notation-for-abbreviation"] Notation secl := (as_sec s).
#[warnings="-notation-for-abbreviation"] Notation lastc := (List.last (as_sec s) sc).
#[warnings="-notation-for-abbreviation"] Notation secl' := (removelast (list_set (as_sec s) i (List.last (as_sec s) sc))).
#[warnings="-notation-for-abbreviation"] Notation s' := (ldl_st cb cm sc i s).
#[warnings="-notation-for-abbreviation"] Notation SS := (as_sec_stats s).
#[warnings="-notation-for-abbreviation"] Notation TS := (as_ts s).

(* [comment removed for export] *)
Definition FPWldl (z : Z) : Prop :=
     lo <= z
  \/ (INST + kInsNReserved + 8 <= z < INST + kInsNReserved + 17)
  \/ (INST + kInsSecStats + 8 <= z < INST + kInsSecStats + 24)
  \/ (INST + kInsSecMutex <= z < INST + kInsSecMutex + 4)
  \/ (INST + kInsGlobalStats + 16 <= z < INST + kInsGlobalStats + 32)
  \/ (PA + 8 * Z.of_nat i <= z < PA + 8 * Z.of_nat i + 8)
  \/ (sc_map_beg lastc + 24 <= z < sc_map_beg lastc + 32)
  \/ (T + kThrStats + 40 <= z < T + kThrStats + 56) \/ (T + kThrStats + 88 <= z < T + kThrStats + 104)
  \/ (kShadowBase + A / 8 <= z < kShadowBase + A / 8 + L / 8)
  \/ (A <= z < A + L).

Hypothesis Hcm : as_chunks s !! cb = Some cm.
Hypothesis ST : cm_state cm = CQuarantined qi qj.
Hypothesis PC : cm_prim cm = None.
Hypothesis NTH : nth_error (as_sec s) i = Some sc.
Hypothesis AB : cm_alloc_beg cm = A + kPageSize.
Hypothesis REP : AREP s m.
Hypothesis WF : AWf E [] D s.
Hypothesis RENV : renv_ok E s.
Hypothesis AG : forall z, 0 <= z < 2^64 -> ~ FPWldl z -> m' (wa z) = m (wa z).
Hypothesis LO : alloc_ceiling <= lo.
(* [comment removed for export] *)
Hypothesis IMG_INST : forall r, In r (List.tl (arep_img_ranges E)) -> fst r + snd r <= INST \/ INST + 3632 <= fst r.
Hypothesis NC_nres : RW m' (INST + kInsNReserved) [C8 (zw (as_ptr_committed s)); C8 (zw (n_chunks s - 1)); C1 (zb 0)].
Hypothesis NC_stats : RW m' (INST + kInsSecStats) [C8 (zw (ss_n_allocs SS)); C8 (zw (ss_n_frees SS + 1)); C8 (zw (ss_cur SS - L)); C8 (zw (ss_max SS))].
Hypothesis NC_mutex : RW m' (INST + kInsSecMutex) [C4 (zw 0)].
Hypothesis NC_glob : RW m' (INST + kInsGlobalStats + 16) [C8 (zw (as_glob_allocated s - L)); C8 (zw (as_glob_mapped s - L))].
Hypothesis NC_ptr : u64arr segs m' PA (map (fun c => zw (sc_map_beg c)) (as_sec s') ++ junk).
Hypothesis NC_len : (length (as_sec s') + length junk = Z.to_nat kChunksBlockCount)%nat.
Hypothesis NC_idx : sc_map_beg lastc <> A -> RW m' (sc_map_beg lastc + 24) [C8 (zw (Z.of_nat i))].
Hypothesis NC_st1 : RW m' (T + kThrStats + 40) [C8 (zw (ts_real_frees TS + 1)); C8 (zw (ts_really_freed TS + n))].
Hypothesis NC_st2 : RW m' (T + kThrStats + 88) [C8 (zw (ts_munmaps TS + 1)); C8 (zw (ts_munmaped TS + L))].
Hypothesis NC_sh : RW m' (kShadowBase + A / 8) [CB (Z.to_nat (L / 8)) (repeat (zb 0) (Z.to_nat (L / 8)))].

Let BS : blocks_sep E s. Proof. exact (proj1 RENV). Qed.
Let Tpl : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) /\ T + 4096 <= alloc_ceiling. Proof. exact (proj1 (proj2 RENV)). Qed.
Let IMG_IN : forall r, In r (arep_img_ranges E ++ depot_static E) -> fst (ae_img E) <= fst r /\ fst r + snd r <= fst (ae_img E) + snd (ae_img E).
Proof. exact (proj1 (proj2 (proj2 RENV))). Qed.
Let IMG_LO : 0x10000 <= fst (ae_img E). Proof. exact (proj1 (proj2 (proj2 (proj2 RENV)))). Qed.
Let IMG_LOW : forall r, In r (arep_img_ranges E ++ depot_static E) -> 0x10000 <= fst r /\ fst r + snd r <= 0x603000.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 RENV))))). Qed.
Let IMG_DEPSEP : forall x y, In x (arep_img_ranges E) -> In y (depot_static E) -> fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 RENV)))))). Qed.
Let AK : exists mo, AKern E s mo. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RENV))))))). Qed.
Let TDN : T + 4096 <= ae_depot_nodes E \/ ae_depot_nodes E + kDepotNodeBlockBytes <= T.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RENV)))))))). Qed.
Let DN0 : ae_depot_nodes E + kDepotNodeBlockBytes <= PA \/ PA + kPtrArrayLen <= ae_depot_nodes E.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 RENV)))))))). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sc_in : In sc secl. Proof. exact (nth_error_In _ _ NTH). Qed.
Lemma secl_nodup : List.NoDup secl.
Proof. pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & _ & S4 & _) & _). exact (NoDup_map_inv _ _ S4). Qed.
Lemma swap : length secl = S (length secl')
  /\ (forall y, In y secl' <-> In y secl /\ y <> sc)
  /\ (forall j y, nth_error secl' j = Some y ->
        (j = i /\ y = lastc /\ y <> sc /\ nth_error secl (length secl') = Some y) \/ (j <> i /\ nth_error secl j = Some y /\ y <> sc /\ y <> lastc))
  /\ In lastc secl.
Proof. exact (swap_remove_facts secl i sc NTH secl_nodup). Qed.
Lemma lastc_in : In lastc secl. Proof. exact (proj2 (proj2 (proj2 swap))). Qed.

(* [comment removed for export] *)
Lemma sec_facts : forall c, In c secl ->
  sc_map_beg c mod kPageSize = 0 /\ app_mem (sc_map_beg c) (sc_map_size c) /\ sc_map_beg c + sc_map_size c <= alloc_ceiling
  /\ 0 < sc_map_size c /\ sc_map_size c mod kPageSize = 0 /\ 4096 <= sc_map_size c
  /\ (sc_map_beg c + sc_map_size c <= SB \/ SB + kSpaceSize <= sc_map_beg c)
  /\ (forall r, In r (ae_reserved E) -> sc_map_beg c + sc_map_size c <= fst r \/ fst r + snd r <= sc_map_beg c).
Proof.
  intros c Hc. pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 c Hc) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
  pose proof (AsanRepFrame.pos_mod_ge E (sc_map_size c) kPageSize M4 M5 ltac:(unfold kPageSize; lia)) as GE. unfold kPageSize in GE |- *.
  repeat split; assumption.
Qed.
Lemma sec_disj : forall a b, In a secl -> In b secl -> a <> b -> sc_map_beg a + sc_map_size a <= sc_map_beg b \/ sc_map_beg b + sc_map_size b <= sc_map_beg a.
Proof. pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & _ & _ & S5) & _). exact S5. Qed.
Lemma lastc_beg_ne : lastc <> sc -> sc_map_beg lastc <> A.
Proof.
  pose proof lastc_in as LI. revert LI. generalize (List.last secl sc) as lc. intros lc LI NE EQ.
  pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & _ & S4 & _) & _).
  pose proof (in_split _ _ sc_in) as (l1 & l2 & El). rewrite El in LI, S4.
  assert (IN' : In lc (l1 ++ l2)).
  { apply in_app_iff in LI. apply in_app_iff. destruct LI as [H|[H|H]]; [left; exact H| exfalso; exact (NE (eq_sym H))| right; exact H]. }
  rewrite map_app in S4. cbn [map] in S4. apply List.NoDup_remove_2 in S4. apply S4. rewrite <- map_app. apply in_map_iff. exists lc. split; [exact EQ| exact IN'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ld_chunks : as_chunks s' = delete cb (as_chunks s). Proof. clear. destruct s; reflexivity. Qed.
Lemma ld_lookup : forall cb0, as_chunks s' !! cb0 = if decide (cb0 = cb) then None else as_chunks s !! cb0.
Proof. intros cb0. rewrite ld_chunks. destruct (decide (cb0 = cb)) as [->|NE]; [apply lookup_delete_eq| rewrite lookup_delete_ne by congruence; reflexivity]. Qed.
Lemma ld_regions : as_regions s' = as_regions s. Proof. clear. destruct s; reflexivity. Qed.
Lemma ld_sec : as_sec s' = secl'. Proof. clear. destruct s; reflexivity. Qed.
Lemma ld_tq : as_tq s' = as_tq s. Proof. clear. destruct s; reflexivity. Qed.
Lemma ld_gq : as_gq s' = as_gq s. Proof. clear. destruct s; reflexivity. Qed.
Lemma ld_ts : as_ts s' = ts_on_munmap L (ts_on_real_free n TS). Proof. clear. destruct s; reflexivity. Qed.
Lemma ld_ptr : as_ptr_committed s' = as_ptr_committed s. Proof. clear. destruct s; reflexivity. Qed.
Lemma ld_stats : as_sec_stats s' = mkSecStats (ss_n_allocs SS) (ss_n_frees SS + 1) (ss_cur SS - L) (ss_max SS) (ss_by_size_log SS). Proof. clear. destruct s; reflexivity. Qed.
Lemma ld_glob_allocated : as_glob_allocated s' = as_glob_allocated s - L. Proof. clear. destruct s; reflexivity. Qed.
Lemma ld_glob_mapped : as_glob_mapped s' = as_glob_mapped s - L. Proof. clear. destruct s; reflexivity. Qed.
Lemma ld_cache_allocated : as_cache_allocated s' = as_cache_allocated s. Proof. clear. destruct s; reflexivity. Qed.
Lemma ld_cache_mapped : as_cache_mapped s' = as_cache_mapped s. Proof. clear. destruct s; reflexivity. Qed.
Lemma ld_cache_inited : as_cache_inited s' = as_cache_inited s. Proof. clear. destruct s; reflexivity. Qed.
Lemma ld_get_cache : forall c, get_cache s' c = get_cache s c. Proof. clear. intros c. destruct s; reflexivity. Qed.
Lemma ld_ia : as_ia_inited s' = as_ia_inited s. Proof. clear. destruct s; reflexivity. Qed.
Lemma tq_bytes_ld : tq_bytes s' = tq_bytes s. Proof. clear. destruct s; reflexivity. Qed.
Lemma gq_bytes_ld : gq_bytes s' = gq_bytes s. Proof. clear. destruct s; reflexivity. Qed.
Lemma ld_n_chunks : n_chunks s' = n_chunks s - 1.
Proof. unfold n_chunks. rewrite ld_sec. pose proof (proj1 swap) as LEN. clear -LEN. lia. Qed.
Lemma ld_region_of : forall c, region_of s' c = region_of s c. Proof. clear. intros c. unfold region_of, get_region. destruct s; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma i_bound : Z.of_nat i < kChunksBlockCount /\ as_ptr_committed s = kChunksBlockCount.
Proof.
  pose proof WF as (_ & _ & _ & _ & _ & (S1 & S2 & _) & _). pose proof (nth_error_lt secl i sc NTH) as LT.
  destruct S1 as [[P0 SE]|P1]; [rewrite SE in LT; cbn in LT; lia|]. unfold n_chunks in S2. rewrite P1 in S2. split; [clear -LT S2; lia| exact P1].
Qed.
Lemma beg_inj : forall a b, In a secl -> In b secl -> sc_map_beg a = sc_map_beg b -> a = b.
Proof.
  intros a b Ha Hb EQ. destruct (secchunk_eq_dec a b) as [->|NE]; [reflexivity| exfalso].
  pose proof (sec_facts a Ha) as (_ & _ & _ & PA_ & _). pose proof (sec_facts b Hb) as (_ & _ & _ & PB & _).
  destruct (sec_disj a b Ha Hb NE); clear -EQ PA_ PB H; lia.
Qed.
(* [comment removed for export] *)
Lemma cm_block : blk_lo cm = A + 4096 /\ blk_hi s cm = A + L /\ A + 4096 < A + L.
Proof.
  pose proof (chunk_user_in_block E [] D s cb cm WF Hcm) as (U1 & U2 & U3). unfold user_lo, user_hi, kChunkHeaderSize in *.
  pose proof WF as (_ & _ & _ & [K1 _] & _). destruct (K1 _ _ Hcm) as (_ & N & _).
  destruct (block_where E [] D s cb cm WF Hcm) as [(J1 & J2 & c & Hc & PR & _)|(sc0 & Hsc0 & _ & L1 & L2)]; [rewrite PC in PR; discriminate|].
  assert (E0 : sc0 = sc) by (apply beg_inj; [exact Hsc0| exact sc_in| unfold blk_lo, kPageSize in *; clear -L1 AB; lia]). subst sc0.
  unfold blk_lo, kPageSize in *. split; [clear -AB; lia|]. split; [exact L2| clear -U1 U2 N AB L2; lia].
Qed.

Lemma secmap_apart : forall c a, In c secl -> sc_map_beg c <= a < sc_map_beg c + sc_map_size c ->
     ~ (ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000)
  /\ ~ (PA <= a < PA + 0x800000)
  /\ ~ (T <= a < T + 4096)
  /\ (forall b len, (In b (ae_depot_nodes E :: as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In b (ae_store_blk E :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
        ~ (b <= a < b + len))
  /\ ~ (kLowAppEnd <= a < kHighMemBeg)
  /\ (forall r, In r (arep_img_ranges E ++ depot_static E) -> ~ (fst r <= a < fst r + snd r))
  /\ 0 <= a < alloc_ceiling
  /\ ~ (INST <= a < INST + 3632).
Proof.
  intros c a Hc Ha. destruct AK as [mo K]. pose proof (sec_facts c Hc) as (M1 & AM & CE & POS & M5 & GE & SP & SR).
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & _).
  pose proof (SR _ E7) as X7. pose proof (SR _ E8) as X8. pose proof (SR _ E13) as X13. pose proof (SR _ E29) as X29. cbn [fst snd] in X7, X8, X13.
  pose proof (BS (ae_depot_nodes E) kDepotNodeBlockBytes (or_introl (conj (or_introl eq_refl) eq_refl))) as (_ & _ & _ & DNS & _).
  pose proof (ak_store_sep _ _ _ K) as (_ & SBS & _).
  unfold app_mem in AM. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in *.
  split; [clear -Ha X7; lia|]. split; [clear -Ha X8; lia|]. split; [clear -Ha X13; lia|]. split.
  { intros b len [[[<-|Hb] ->]|[[<-|Hb] ->]].
    - destruct (DNS c Hc); clear -Ha H; lia.
    - destruct (ak_blocks_sep _ _ _ K b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & _ & _ & _ & BSC & _). destruct (BSC c Hc); clear -Ha H; lia.
    - destruct (SBS c Hc); unfold kStoreBlockBytes; clear -Ha H; lia.
    - destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & BSC & _). destruct (BSC c Hc); clear -Ha H; lia. }
  split; [clear -Ha AM; lia|].
  pose proof (IMG_IN (INST, 3632) ltac:(apply in_app_iff; left; left; reflexivity)) as [I3 I4]. cbn [fst snd] in I3, I4.
  split.
  { intros r Hr R. pose proof (IMG_IN r Hr) as [I1 I2]. destruct (ae_img E); cbn [fst snd] in *. clear -Ha X29 I1 I2 R. lia. }
  destruct (ae_img E); cbn [fst snd] in *. split; [clear -Ha AM CE; lia| clear -Ha X29 I3 I4; lia].
Qed.

Lemma INST_img : 0x10000 <= INST /\ INST + 3632 <= 0x603000 /\ fst (ae_img E) <= INST /\ INST + 3632 <= fst (ae_img E) + snd (ae_img E).
Proof.
  pose proof (IMG_LOW (INST, 3632) ltac:(apply in_app_iff; left; left; reflexivity)) as [A0 B0].
  pose proof (IMG_IN (INST, 3632) ltac:(apply in_app_iff; left; left; reflexivity)) as [C0 D0]. cbn [fst snd] in *. auto.
Qed.
Lemma win_band : forall z, kShadowBase + A / 8 <= z < kShadowBase + A / 8 + L / 8 -> kLowAppEnd < z < kHighMemBeg.
Proof.
  intros z Hz. pose proof (sec_facts sc sc_in) as (_ & AM & CE & POS & _). pose proof alloc_ceiling_range as CR.
  unfold app_mem in AM. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in *. unfold kShadowBase in *. clear -Hz AM CE CR POS. lia.
Qed.
Lemma Tpage_apart : forall a, T <= a < T + 4096 ->
     ~ (ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000)
  /\ ~ (PA <= a < PA + 0x800000)
  /\ (forall c, In c secl -> ~ (sc_map_beg c <= a < sc_map_beg c + sc_map_size c))
  /\ (forall b0 len, (In b0 (ae_depot_nodes E :: as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In b0 (ae_store_blk E :: as_store_blocks s) /\ len = kStoreBlockBytes) ->
        ~ (b0 <= a < b0 + len))
  /\ ~ (kLowAppEnd < a < kHighMemBeg) /\ ~ (0x10000 <= a < 0x603000).
Proof.
  intros a Ha. destruct AK as [mo K].
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & _).
  split; [clear -Ha E19; lia|]. split; [clear -Ha E23; lia|]. split.
  { intros c Hc R. destruct (secmap_apart c a Hc R) as (_ & _ & NT & _). exact (NT Ha). }
  split.
  { intros b0 len H. destruct H as [[[<-|Hb0] ->]|[[<-|Hb0] ->]].
    - clear -Ha TDN. lia.
    - destruct (ak_blocks_sep _ _ _ K b0 kDepotNodeBlockBytes (or_introl (conj Hb0 eq_refl))) as (_ & _ & _ & _ & _ & R). pose proof (R _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia.
    - pose proof (ak_store_sep _ _ _ K) as (_ & _ & X & _). unfold kPageSize, kStoreBlockBytes in *. clear -Ha X. lia.
    - destruct (ak_blocks_sep _ _ _ K b0 kStoreBlockBytes (or_intror (conj Hb0 eq_refl))) as (_ & _ & _ & _ & _ & R). pose proof (R _ E13) as X. cbn [fst snd] in X. clear -Ha X. lia. }
  unfold app_mem in E14. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in *. pose proof Tpl as [[T1 T2] T3]. clear -Ha E14 T1 T2 T3. split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma AG_at : forall a, 0 <= a < alloc_ceiling -> ~ (T <= a < T + 4096) -> ~ (INST <= a < INST + 3632) -> ~ (PA <= a < PA + 0x800000) ->
  (forall c, In c secl -> sc_map_beg c <= a < sc_map_beg c + sc_map_size c -> c <> sc /\ (c = lastc -> a < sc_map_beg c + 24 \/ sc_map_beg c + 32 <= a)) ->
  ~ (kShadowBase + A / 8 <= a < kShadowBase + A / 8 + L / 8) -> m' (wa a) = m (wa a).
Proof.
  intros a BC NT NI NP NS NW. pose proof alloc_ceiling_range as CR. pose proof i_bound as [IB _].
  pose proof (sec_facts lastc lastc_in) as (_ & _ & _ & _ & _ & GEl & _).
  apply AG; [clear -BC CR; lia|]. unfold FPWldl.
  unfold kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kThrStats, kChunksBlockCount in *.
  intros [X|[X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]].
  - clear -X BC LO. lia.
  - clear -X NI. lia.
  - clear -X NI. lia.
  - clear -X NI. lia.
  - clear -X NI. lia.
  - clear -X NP IB. lia.
  - destruct (NS lastc lastc_in ltac:(clear -X GEl; lia)) as [_ Y]. destruct (Y eq_refl); clear -X H; lia.
  - clear -X NT. lia.
  - clear -X NT. lia.
  - exact (NW X).
  - destruct (NS sc sc_in X) as [Y _]. exact (Y eq_refl).
Qed.
(* [comment removed for export] *)
Lemma AG_off : forall a, 0 <= a < alloc_ceiling -> ~ (T <= a < T + 4096) -> ~ (INST <= a < INST + 3632) -> ~ (PA <= a < PA + 0x800000) ->
  (forall c, In c secl -> ~ (sc_map_beg c <= a < sc_map_beg c + sc_map_size c)) ->
  ~ (kShadowBase + A / 8 <= a < kShadowBase + A / 8 + L / 8) -> m' (wa a) = m (wa a).
Proof. intros a BC NT NI NP NS NW. apply AG_at; try assumption. intros c Hc R. exfalso. exact (NS c Hc R). Qed.

(* [comment removed for export] *)
Lemma AG_resv : forall a, ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000 -> m' (wa a) = m (wa a).
Proof.
  intros a R. pose proof INST_img as (I1 & I2 & _).
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & _).
  rewrite kHighMemBeg_val in E2.
  apply AG_off; [clear -R E2 E5; lia| clear -R E19; lia| clear -R I2 E2; lia| clear -R E20; lia| |].
  - intros c Hc M. destruct (secmap_apart c a Hc M) as (NR & _). exact (NR R).
  - intros W. pose proof (win_band a W) as X. rewrite kHighMemBeg_val in X. clear -X R E2. lia.
Qed.
Lemma space_resv : forall a, SB <= a < SB + kSpaceSize + 0x1000 -> ae_resv_beg E <= a < ae_resv_beg E + 0x2000011000.
Proof. intros a Ha. pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & _). clear -Ha E3 E4. lia. Qed.
Lemma AGri : forall a, RI <= a < RI + kRegSize * kNumClasses -> m' (wa a) = m (wa a).
Proof. intros a Ha. apply AG_resv. apply space_resv. unfold ae_region_info, kRegSize, kNumClasses, kSpaceSize in *. clear -Ha. lia. Qed.
Lemma AGrmap : forall a, in_some_region_map E s a = true -> m' (wa a) = m (wa a).
Proof. intros a RM. pose proof (region_map_in_space E [] D s a WF RM) as SP. apply AG_resv. apply space_resv. unfold kSpaceSize in *. clear -SP. lia. Qed.
Lemma AGfa : forall a c', 0 <= c' < kNumClasses -> free_array SB c' <= a < free_array SB c' + rg_mapped_fa (region_of s c') -> m' (wa a) = m (wa a).
Proof.
  intros a c' Hc Ha. apply AGrmap. unfold in_some_region_map. apply Bool.orb_true_iff. right. apply existsb_exists. exists c'.
  split; [apply In_ziota; unfold kNumClasses in Hc; lia|]. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.
Lemma AGuser : forall a c', 0 <= c' < kNumClasses -> region_beg SB c' <= a < region_beg SB c' + rg_mapped_user (region_of s c') -> m' (wa a) = m (wa a).
Proof.
  intros a c' Hc Ha. apply AGrmap. unfold in_some_region_map. apply Bool.orb_true_iff. left. apply existsb_exists. exists c'.
  split; [apply In_ziota; unfold kNumClasses in Hc; lia|]. apply andb_true_iff. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed.
Lemma AGbat : forall a b, In b (as_tq s ++ as_gq s) -> b_addr b <= a < b_addr b + 24 + 8 * kBatchCap -> m' (wa a) = m (wa a).
Proof.
  intros a b Hb Ha. apply AG_resv. pose proof WF as (WE & WR & _ & _ & WQ & _).
  destruct (batch_block E D s b WQ ltac:(unfold all_batches; rewrite app_assoc; apply in_app_iff; left; exact Hb)) as (CV & _).
  assert (HB24 : 1 <= kBatchClass <= kLargestClassID) by (unfold kBatchClass, kLargestClassID; lia).
  pose proof (carved_in_space E s kBatchClass _ HB24 WR CV) as [J1 J2].
  assert (CS : class_size kBatchClass = 8192) by reflexivity.
  apply space_resv. unfold kBatchCap, kSpaceSize, kRegionSize in *. clear -Ha J1 J2 CS. lia.
Qed.

(* [comment removed for export] *)
Lemma AG_secmap : forall a c, In c secl -> c <> sc -> sc_map_beg c <= a < sc_map_beg c + sc_map_size c ->
  (c = lastc -> a < sc_map_beg c + 24 \/ sc_map_beg c + 32 <= a) -> m' (wa a) = m (wa a).
Proof.
  intros a c Hc NE R LC. destruct (secmap_apart c a Hc R) as (NR & NP & NT & NB & NBD & NIM & BC & NI).
  apply AG_at; [exact BC| exact NT| exact NI| exact NP| |].
  - intros c' Hc' R'. destruct (secchunk_eq_dec c' c) as [->|NE']; [split; [exact NE| exact LC]| exfalso].
    destruct (sec_disj c' c Hc' Hc NE'); clear -R R' H; lia.
  - intros W. pose proof (win_band a W) as X. apply NBD. clear -X. lia.
Qed.
Lemma AGsec : forall a c, In c secl -> c <> sc -> sc_map_beg c <= a < sc_map_beg c + 32 -> (c = lastc -> a < sc_map_beg c + 24) -> m' (wa a) = m (wa a).
Proof.
  intros a c Hc NE Ha LC. pose proof (sec_facts c Hc) as (_ & _ & _ & _ & _ & GE & _).
  apply (AG_secmap a c Hc NE); [clear -Ha GE; lia| intros EQ; left; exact (LC EQ)].
Qed.
Lemma AGcm : forall a cb' cm', as_chunks s !! cb' = Some cm' -> cb' <> cb -> chunk_meta_fp cm' a -> m' (wa a) = m (wa a).
Proof.
  intros a cb' cm' Hcm' NE Ha. pose proof (chunk_meta_in_block E [] D s cb' cm' a WF Hcm' Ha) as [BL BU]. pose proof cm_block as (C1 & C2 & C3).
  destruct (block_where E [] D s cb' cm' WF Hcm') as [(J1 & J2 & _)|(c & Hc & _ & L1 & L2)].
  - apply AG_resv. apply space_resv. clear -BL BU J1 J2. lia.
  - unfold kPageSize in L1. apply (AG_secmap a c Hc); [| clear -BL BU L1 L2; lia| intros _; right; clear -BL L1; lia].
    intros ->. destruct (chunks_disjoint E [] D s cb' cm' cb cm WF Hcm' Hcm NE); clear -BL BU L1 L2 C1 C2 C3 H; lia.
Qed.
(* [comment removed for export] *)
Lemma AGptr : forall a, PA <= a < PA + 8 * kChunksBlockCount -> ~ (PA + 8 * Z.of_nat i <= a < PA + 8 * Z.of_nat i + 8) -> m' (wa a) = m (wa a).
Proof.
  intros a Ha NSL. unfold kChunksBlockCount in Ha. pose proof INST_img as (I1 & I2 & I3 & I4). pose proof alloc_ceiling_range as CR.
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 &
                             E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & E30 & E31 & E32 & E33 & _).
  unfold app_mem in E16. unfold img_sep in E33. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in *.
  apply AG; [clear -Ha E16 E17 CR; lia|]. unfold FPWldl. unfold kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kThrStats in *.
  intros [X|[X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]].
  - clear -X Ha E17 LO. lia.
  - clear -X Ha I3 I4 E33. lia.
  - clear -X Ha I3 I4 E33. lia.
  - clear -X Ha I3 I4 E33. lia.
  - clear -X Ha I3 I4 E33. lia.
  - exact (NSL X).
  - pose proof (sec_facts lastc lastc_in) as (_ & _ & _ & _ & _ & GEl & _). destruct (secmap_apart lastc a lastc_in ltac:(clear -X GEl; lia)) as (_ & NP & _). apply NP. clear -Ha. lia.
  - clear -X Ha E23. lia.
  - clear -X Ha E23. lia.
  - pose proof (win_band a X) as B. rewrite ?kLowAppEnd_val, ?kHighMemBeg_val in B. clear -B Ha E16. lia.
  - destruct (secmap_apart sc a sc_in X) as (_ & NP & _). apply NP. clear -Ha. lia.
Qed.
(* [comment removed for export] *)
Lemma AGimg1 : forall a, in_ranges (List.tl (arep_img_ranges E)) a -> m' (wa a) = m (wa a).
Proof.
  intros a (r & Hr & R). pose proof INST_img as (I1 & I2 & I3 & I4). pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR.
  assert (Hr' : In r (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; left; right; exact Hr).
  pose proof (IMG_LOW r Hr') as [L1 L2]. pose proof (IMG_IN r Hr') as [L3 L4].
  pose proof (IMG_INST r Hr) as SEP.
  pose proof (proj1 WF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E33 & _).
  unfold img_sep in E33.
  apply AG_off; [clear -R L1 L2 CR; lia| clear -R L1 L2 T1 T2; lia| clear -R SEP; lia| clear -R L3 L4 E33; lia| |].
  - intros c Hc M. destruct (secmap_apart c a Hc M) as (_ & _ & _ & _ & _ & NIM & _). exact (NIM r Hr' R).
  - intros W. pose proof (win_band a W) as X. rewrite kLowAppEnd_val in X. clear -X L1 L2 R. lia.
Qed.
(* [comment removed for export] *)
Lemma AGdep : forall a, DepotFP E s a -> m' (wa a) = m (wa a).
Proof.
  intros a Ha. pose proof INST_img as (I1 & I2 & I3 & I4). pose proof Tpl as [[T1 T2] T3]. destruct AK as [mo K]. pose proof alloc_ceiling_range as CR.
  pose proof (proj1 WF) as WE.
  pose proof WE as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 &
                    E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & E30 & E31 & E32 & E33 & _).
  destruct (DepotFP_where E s a Ha) as [(r & Hr & R)|[(b & Hb & R)|(b & Hb & R)]].
  - (* [comment removed for export] *)
    assert (Hr' : In r (arep_img_ranges E ++ depot_static E)) by (apply in_app_iff; right; exact Hr).
    pose proof (IMG_LOW r Hr') as [L1 L2]. pose proof (IMG_IN r Hr') as [L3 L4].
    pose proof (IMG_DEPSEP (INST, 3632) r ltac:(left; reflexivity) Hr) as SEP. cbn [fst snd] in SEP. unfold img_sep in E33.
    apply AG_off; [clear -R L1 L2 CR; lia| clear -R L1 L2 T1 T2; lia| clear -R SEP; lia| clear -R L3 L4 E33; lia| |].
    + intros c Hc M. destruct (secmap_apart c a Hc M) as (_ & _ & _ & _ & _ & NIM & _). exact (NIM r Hr' R).
    + intros W. pose proof (win_band a W) as X. rewrite kLowAppEnd_val in X. clear -X L1 L2 R. lia.
  - (* [comment removed for export] *)
    pose proof (BS b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (AM & CE & BR & BSC & BF & BI). unfold img_sep in BI. unfold app_mem in AM.
    apply AG_off; [clear -R AM CE; rewrite ?kHighMemBeg_val in AM; lia| | clear -R BI I3 I4; lia| | |].
    + intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _). exact (NB b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl)) R).
    + destruct Hb as [<-|Hb]; [unfold kPtrArrayLen in DN0; clear -R DN0; lia|].
      destruct (ak_blocks_sep _ _ _ K b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & RR). pose proof (RR _ E8) as X. cbn [fst snd] in X. clear -R X. lia.
    + intros c Hc M. destruct (secmap_apart c a Hc M) as (_ & _ & _ & NB & _). exact (NB b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl)) R).
    + intros W. pose proof (win_band a W) as X. clear -X R AM. lia.
  - (* [comment removed for export] *)
    pose proof (BS b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (AM & CE & BR & BSC & BF & BI). unfold img_sep in BI. unfold app_mem in AM.
    apply AG_off; [clear -R AM CE; rewrite ?kHighMemBeg_val in AM; lia| | clear -R BI I3 I4; lia| | |].
    + intros HT. destruct (Tpage_apart a HT) as (_ & _ & _ & NB & _). exact (NB b kStoreBlockBytes (or_intror (conj Hb eq_refl)) R).
    + destruct Hb as [<-|Hb].
      * pose proof (ak_store_sep _ _ _ K) as (_ & _ & _ & _ & X). unfold kPtrArrayLen, kStoreBlockBytes in *. clear -R X. lia.
      * destruct (ak_blocks_sep _ _ _ K b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & _ & _ & _ & _ & RR). pose proof (RR _ E8) as X. cbn [fst snd] in X. clear -R X. lia.
    + intros c Hc M. destruct (secmap_apart c a Hc M) as (_ & _ & _ & NB & _). exact (NB b kStoreBlockBytes (or_intror (conj Hb eq_refl)) R).
    + intros W. pose proof (win_band a W) as X. clear -X R AM. lia.
Qed.
(* [comment removed for export] *)
Lemma Sh_granule_range : forall x v, Sh E s x = Some v -> 0 <= x < 2^47.
Proof.
  intros x v Hx. pose proof WF as WF0. pose proof alloc_ceiling_range as CR. unfold Sh in Hx.
  destruct (in_some_region_map E s x) eqn:RM.
  - pose proof (region_map_in_space E [] D s x WF0 RM) as SP. pose proof (proj1 WF0) as (E1 & E2 & E3 & E4 & E5 & _).
    unfold kSpaceSize in *. clear -SP E2 E3 E4 E5 CR. rewrite kHighMemBeg_val in E2. lia.
  - destruct (in_some_sec_map s x) eqn:SM.
    + unfold in_some_sec_map in SM. apply existsb_exists in SM as (c & Hc & Hb). apply andb_true_iff in Hb as [B1 B2].
      apply Z.leb_le in B1. apply Z.ltb_lt in B2. pose proof (sec_facts c Hc) as (_ & HB & S0 & _).
      unfold app_mem in HB. rewrite kHighMemBeg_val, kLowAppEnd_val in HB. clear -B1 B2 HB S0 CR. lia.
    + cbn [orb] in Hx. destruct (sh_default_dom E x && negb (sh_excluded E x)) eqn:C; [|discriminate].
      apply andb_true_iff in C as [C _]. unfold sh_default_dom in C. apply Bool.orb_true_iff in C as [C|C].
      * apply andb_true_iff in C as [C _]. apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
        rewrite kLowAppEnd_val in C2. clear -C1 C2. lia.
      * apply andb_true_iff in C as [C1 C2]. apply Z.leb_le in C1. apply Z.leb_le in C2.
        rewrite kHighMemBeg_val in C1. unfold kHighMemEnd in C2. clear -C1 C2. lia.
Qed.
Lemma AGsh_out : forall g v, Sh E s (8 * g) = Some v -> (8 * g + 8 <= A \/ A + L <= 8 * g) -> m' (wa (kShadowBase + g)) = m (wa (kShadowBase + g)).
Proof.
  intros g v Hg OUT. pose proof (Sh_granule_range _ _ Hg) as GR. pose proof INST_img as (I1 & I2 & _). pose proof alloc_ceiling_range as CR.
  pose proof (sec_facts sc sc_in) as (M1 & _ & _ & _ & M5 & _).
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & _).
  assert (BAND : kLowAppEnd < kShadowBase + g < kHighMemBeg) by (rewrite kLowAppEnd_val, kHighMemBeg_val; unfold kShadowBase; clear -GR; lia).
  pose proof BAND as BANDn. rewrite kLowAppEnd_val, kHighMemBeg_val in BANDn.
  apply AG_off; [clear -BANDn CR; lia| | clear -BANDn I1 I2; lia| unfold app_mem in E16; rewrite kLowAppEnd_val, kHighMemBeg_val in E16; clear -BANDn E16; lia| |].
  - intros HT. destruct (Tpage_apart _ HT) as (_ & _ & _ & _ & NBAND & _). apply NBAND. exact BAND.
  - intros c Hc M. destruct (secmap_apart c _ Hc M) as (_ & _ & _ & _ & NB & _). apply NB. clear -BAND. lia.
  - intros W. unfold kShadowBase, kPageSize in *. clear -W OUT M1 M5. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Lemma AGthr_cells : forall A0 k, T <= A0 -> A0 + k <= T + 4096 ->
  (A0 + k <= T + kThrStats + 40 \/ (T + kThrStats + 56 <= A0 /\ A0 + k <= T + kThrStats + 88) \/ T + kThrStats + 104 <= A0) -> agree_on m m' A0 k.
Proof.
  intros A0 k H0 H1 H2 z Hz. pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR. pose proof INST_img as (I1 & I2 & _). pose proof i_bound as [IB _].
  pose proof (proj1 WF) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & _).
  assert (HT : T <= z < T + 4096) by (clear -Hz H0 H1; lia).
  apply AG; [clear -Hz H0 H1 T1 T3 CR; lia|]. unfold FPWldl. unfold kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kThrStats, kChunksBlockCount in *.
  intros [X|[X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]].
  - clear -X HT T3 LO. lia.
  - clear -X HT I1 I2 T2. lia.
  - clear -X HT I1 I2 T2. lia.
  - clear -X HT I1 I2 T2. lia.
  - clear -X HT I1 I2 T2. lia.
  - clear -X HT E23 IB. lia.
  - pose proof (sec_facts lastc lastc_in) as (_ & _ & _ & _ & _ & GEl & _). destruct (Tpage_apart z HT) as (_ & _ & NS & _). apply (NS lastc lastc_in). clear -X GEl. lia.
  - clear -X Hz H2. lia.
  - clear -X Hz H2. lia.
  - pose proof (win_band z X) as B. unfold app_mem in E14. clear -B HT E14. lia.
  - destruct (Tpage_apart z HT) as (_ & _ & NS & _). exact (NS sc sc_in X).
Qed.
Ltac thr_ag := apply AGthr_cells; unfold kThrUnwinding, kThrCache, kThrCacheStats, kThrStats, kPerClassSize, kThrStackTop, kThrQCache, kNumClasses in *;
  cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; try lia.
(* [comment removed for export] *)
Lemma AGinst : forall A0 k, INST <= A0 -> A0 + k <= INST + 3632 ->
  (A0 + k <= INST + kInsNReserved \/ (INST + kInsSecStats + 32 <= A0 /\ A0 + k <= INST + kInsSecMutex) \/ INST + kInsGlobalStats + 32 <= A0) ->
  agree_on m m' A0 k.
Proof.
  intros A0 k H0 H1 H2 z Hz. pose proof Tpl as [[T1 T2] T3]. pose proof alloc_ceiling_range as CR. pose proof INST_img as (I1 & I2 & I3 & I4).
  pose proof (proj1 WF) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E33 & _).
  unfold img_sep in E33.
  assert (HI : INST <= z < INST + 3632) by (clear -Hz H0 H1; lia).
  apply AG; [clear -HI I1 I2 CR; lia|]. unfold FPWldl. unfold kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kThrStats, kChunksBlockCount in *.
  pose proof i_bound as [IB _]. unfold kChunksBlockCount in IB.
  intros [X|[X|[X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]].
  - clear -X HI I2 CR LO. lia.
  - clear -X Hz H2. lia.
  - clear -X Hz H2. lia.
  - clear -X Hz H2. lia.
  - clear -X Hz H2. lia.
  - clear -X HI I3 I4 E33 IB. lia.
  - pose proof (sec_facts lastc lastc_in) as (_ & _ & _ & _ & _ & GEl & _). destruct (secmap_apart lastc z lastc_in ltac:(clear -X GEl; lia)) as (_ & _ & _ & _ & _ & _ & _ & NI). exact (NI HI).
  - clear -X HI I1 I2 T2. lia.
  - clear -X HI I1 I2 T2. lia.
  - pose proof (win_band z X) as B. rewrite kLowAppEnd_val in B. clear -B HI I2. lia.
  - destruct (secmap_apart sc z sc_in X) as (_ & _ & _ & _ & _ & _ & _ & NI). exact (NI HI).
Qed.
Ltac ins_ag := apply AGinst; unfold kInsSpaceBeg, kInsSecondary, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kInsQuarantine, kInsQMutex,
  kInsQGlobal, kInsFallbackMutex, kInsMaxUserDefined in *; cbn [cells_size csize Nat.add length Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ld_in_region_map : forall x, in_some_region_map E s' x = in_some_region_map E s x.
Proof. intros x. unfold in_some_region_map. reflexivity || (unfold region_of, get_region; rewrite ld_regions; reflexivity). Qed.
Lemma ld_in_sec_map_out : forall x, (x < A \/ A + L <= x) -> in_some_sec_map s' x = in_some_sec_map s x.
Proof.
  intros x Hx. unfold in_some_sec_map. rewrite ld_sec. apply existsb_ext_In. intros c Fc.
  apply andb_true_iff in Fc as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2.
  pose proof (proj1 (proj2 swap) c) as IFF. rewrite IFF. split; [intros [H _]; exact H|].
  intros H. split; [exact H|]. intros ->. clear -Hx F1 F2. lia.
Qed.
Lemma ld_in_sec_map_in : forall x, A <= x < A + L -> in_some_sec_map s' x = false.
Proof.
  intros x Hx. destruct (in_some_sec_map s' x) eqn:SM; [exfalso| reflexivity]. unfold in_some_sec_map in SM. rewrite ld_sec in SM.
  apply existsb_exists in SM as (c & Hc & Fc). apply andb_true_iff in Fc as [F1 F2]. apply Z.leb_le in F1. apply Z.ltb_lt in F2.
  apply (proj1 (proj2 swap) c) in Hc as [Hc NE]. destruct (sec_disj c sc Hc sc_in NE); clear -Hx F1 F2 H; lia.
Qed.
Lemma region_map_off : forall x, A <= x < A + L -> in_some_region_map E s x = false.
Proof.
  intros x Hx. destruct (in_some_region_map E s x) eqn:RM; [exfalso| reflexivity].
  pose proof (region_map_in_space E [] D s x WF RM) as SP. destruct (secmap_apart sc x sc_in Hx) as (NR & _). apply NR. apply space_resv. clear -SP. lia.
Qed.
Lemma blk_hi_span : forall cm', blk_hi s cm' = cm_alloc_beg cm' + block_span cm'.
Proof. intros cm'. unfold blk_hi, block_span. destruct (cm_prim cm'); lia. Qed.
Lemma ld_find_chunk_keep : forall cb0 cm0 a, as_chunks s !! cb0 = Some cm0 -> cb0 <> cb -> blk_lo cm0 <= a < blk_hi s cm0 -> find_chunk s' a = Some cm0.
Proof.
  intros cb0 cm0 a Hcm0 NE0 Ha. unfold find_chunk.
  set (f := fun (_ : Z) (cm1 : chunkmeta) (acc : option chunkmeta) => match acc with Some _ => acc | None =>
             if (cm_alloc_beg cm1 <=? a) && (a <? cm_alloc_beg cm1 + block_span cm1) then Some cm1 else None end).
  assert (IND : forall mm, (forall k v, mm !! k = Some v -> as_chunks s !! k = Some v) ->
            (map_fold f None mm = None /\ mm !! cb0 = None) \/ map_fold f None mm = Some cm0).
  { intros mm. induction mm as [|k v mm NONE FIRST IH] using map_first_key_ind; intros SUB.
    - left. split; [apply map_fold_empty| apply lookup_empty].
    - rewrite map_fold_insert_first_key by assumption.
      assert (SUB' : forall k0 v0, mm !! k0 = Some v0 -> as_chunks s !! k0 = Some v0).
      { intros k0 v0 H. apply SUB. rewrite lookup_insert_ne; [exact H|]. intros ->. rewrite NONE in H. discriminate. }
      pose proof (SUB k v ltac:(apply lookup_insert_eq)) as Hk.
      destruct (IH SUB') as [[R NCB]|R]; rewrite R; cbn.
      + destruct ((cm_alloc_beg v <=? a) && (a <? cm_alloc_beg v + block_span v)) eqn:C.
        * right. apply andb_prop in C as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
          destruct (Z.eq_dec k cb0) as [->|NE]; [rewrite Hcm0 in Hk; injection Hk as <-; reflexivity|].
          exfalso. destruct (chunks_disjoint E [] D s k v cb0 cm0 WF Hk Hcm0 NE) as [DJ|DJ]; rewrite blk_hi_span in *; unfold blk_lo in *; lia.
        * left. split; [reflexivity|]. rewrite lookup_insert_ne; [exact NCB|]. intros ->.
          rewrite Hcm0 in Hk. injection Hk as <-. rewrite blk_hi_span in Ha. unfold blk_lo in Ha.
          assert (C' : (cm_alloc_beg cm0 <=? a) && (a <? cm_alloc_beg cm0 + block_span cm0) = true) by (apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
          rewrite C' in C. discriminate.
      + right. reflexivity. }
  destruct (IND (as_chunks s') ltac:(intros k v H; rewrite ld_lookup in H; destruct (decide (k = cb)); [discriminate| exact H])) as [[_ X]|X]; [| exact X].
  rewrite ld_lookup, decide_False in X by exact NE0. rewrite Hcm0 in X. discriminate.
Qed.
Lemma ld_find_chunk_out : forall x, (x < A \/ A + L <= x) -> find_chunk s' x = find_chunk s x.
Proof.
  intros x Hx. pose proof cm_block as (C1 & C2 & C3).
  destruct (find_chunk s x) as [cm0|] eqn:F0.
  - destruct (find_chunk_some s x cm0 F0) as (cb0 & H0 & R0).
    assert (NE : cb0 <> cb) by (intros ->; rewrite Hcm in H0; injection H0 as <-; rewrite <- blk_hi_span in R0; unfold blk_lo in C1; clear -Hx R0 C1 C2; lia).
    apply (ld_find_chunk_keep cb0 cm0 x H0 NE). rewrite blk_hi_span. unfold blk_lo. exact R0.
  - destruct (find_chunk s' x) as [cm0|] eqn:F3; [exfalso| reflexivity].
    destruct (find_chunk_some s' x cm0 F3) as (cb0 & H0 & R0). rewrite ld_lookup in H0. destruct (decide (cb0 = cb)) as [->|NE]; [discriminate|].
    pose proof (find_chunk_block E [] D s cb0 cm0 x WF H0 ltac:(rewrite blk_hi_span; unfold blk_lo; exact R0)). congruence.
Qed.
Lemma Sh_ld_out : forall x, (x < A \/ A + L <= x) -> Sh E s' x = Sh E s x.
Proof. intros x Hx. unfold Sh. rewrite ld_in_region_map, (ld_in_sec_map_out x Hx), (ld_find_chunk_out x Hx). reflexivity. Qed.
Lemma Sh_ld_in : forall x v, A <= x < A + L -> Sh E s' x = Some v -> v = 0.
Proof.
  intros x v Hx H. unfold Sh in H. rewrite ld_in_region_map, (region_map_off x Hx), (ld_in_sec_map_in x Hx) in H. cbn [orb] in H.
  destruct (sh_default_dom E x && negb (sh_excluded E x)); [injection H as <-; reflexivity| discriminate].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma repA_ld : arep_instance segs E s' m'.
Proof.
  pose proof REP as (RA & _). destruct RA as (A1 & A2 & A3 & A4 & (bsl & A5 & L5) & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  unfold arep_instance. rewrite ld_n_chunks, ld_stats, ld_glob_allocated, ld_glob_mapped, ld_gq, gq_bytes_ld, ld_ptr.
  cbn [ss_n_allocs ss_n_frees ss_cur ss_max].
  split; [eapply rw_cells_agree'; [| exact A1]; ins_ag|].
  split; [eapply rw_cells_agree'; [| exact A2]; ins_ag|].
  split; [exact NC_nres|]. split; [exact NC_stats|].
  split; [exists bsl; split; [| exact L5]; eapply u64arr_agree; [| exact A5]; rewrite L5; ins_ag|].
  split; [exact NC_mutex|]. split; [exact NC_glob|].
  split; [eapply rw_cells_agree'; [| exact A8]; ins_ag|].
  split; [eapply rw_cells_agree'; [| exact A9]; ins_ag|].
  split; [eapply rw_cells_agree'; [| exact A10]; ins_ag|].
  split; [eapply rw_cells_agree'; [| exact A11]; ins_ag|].
  eapply rw_cells_agree'; [| exact A12]; ins_ag.
Qed.

(* [comment removed for export] *)
Lemma repB_ld : arep_regioninfo segs E s' m'.
Proof.
  pose proof REP as (_ & RB & _). pose proof (frameB' segs E s m m' AGri RB) as X. intros c Hc. rewrite ld_region_of. exact (X c Hc).
Qed.
Lemma repC_ld : arep_region_mem segs E s' m'.
Proof.
  pose proof REP as (_ & _ & RC & _). intros c Hc. cbv zeta. rewrite ld_region_of. destruct (RC c Hc) as (W & junk' & U & L').
  split.
  - eapply wr_at_agree; [| exact W]. intros x Hx. exact (AGuser x c Hc Hx).
  - exists junk'. split; [| exact L']. eapply u32arr_agree; [| exact U]. intros x Hx. rewrite length_app, length_map in Hx. apply (AGfa x c Hc). clear -Hx L'. lia.
Qed.

(* [comment removed for export] *)
Lemma repD_ld : arep_thread segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & RD & _). destruct RD as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
  unfold arep_thread. rewrite ld_tq, ld_cache_allocated, ld_cache_mapped, ld_ts, tq_bytes_ld.
  split; [eapply rw_cells_agree'; [| exact D1]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D2]; thr_ag|].
  split; [eapply rw_cells_agree'; [| exact D3]; thr_ag|].
  split.
  { intros c' Hc'. destruct (D4 c' Hc') as (X1 & junk' & X2 & L'). unfold percls_cells. rewrite !ld_get_cache, ld_cache_inited. unfold kNumClasses in Hc'.
    split.
    - eapply rw_cells_agree'; [| exact X1]. unfold percls_cells. thr_ag.
    - exists junk'. split; [| exact L']. eapply u32arr_agree; [| exact X2]. rewrite length_app, length_map. thr_ag. }
  split; [eapply rw_cells_agree'; [| exact D5]; thr_ag|].
  split.
  { pose proof NC_st1 as N1. apply rh_split with (cs1 := [C8 (zw (ts_real_frees TS + 1))]) in N1 as [N5 N6].
    pose proof NC_st2 as N2. apply rh_split with (cs1 := [C8 (zw (ts_munmaps TS + 1))]) in N2 as [N11 N12].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in N6, N12.
    apply u64arr_of_cells.
    - (* [comment removed for export] *)
      destruct D6 as [_ W6]. unfold tstats_words in W6 |- *. rewrite length_map in W6 |- *. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in W6 |- *.
      Ltac wsub W6 := eapply wr_at_agree; [| eapply (wr_at_sub segs _ _ _ _ _ W6); lia]; thr_ag.
      match goal with |- wr_at _ _ _ ?nn => replace nn with (40 + (16 + (32 + (16 + 8)))) by reflexivity end.
      match type of W6 with wr_at _ _ _ ?nn => replace nn with 112 in W6 by reflexivity end.
      apply wr_at_join; [lia| lia| wsub W6|]. apply wr_at_join; [lia| lia| exact (rw_wr _ _ _ NC_st1)|].
      apply wr_at_join; [lia| lia| replace (T + kThrStats + 40 + 16) with (T + kThrStats + 56) by lia; wsub W6|].
      apply wr_at_join; [lia| lia| replace (T + kThrStats + 40 + 16 + 32) with (T + kThrStats + 88) by lia; exact (rw_wr _ _ _ NC_st2)|].
      replace (T + kThrStats + 40 + 16 + 32 + 16) with (T + kThrStats + 104) by lia. wsub W6.
    - intros k w Hk.
      Ltac oldw D6 i := eapply rw_cells_agree'; [| exact (u64arr_cell segs _ _ _ i _ D6 eq_refl)]; thr_ag.
      do 5 (destruct k as [|k]; [cbn in Hk; injection Hk as <-; oldw D6 0%nat || oldw D6 1%nat || oldw D6 2%nat || oldw D6 3%nat || oldw D6 4%nat |]).
      destruct k as [|k]; [cbn in Hk; injection Hk as <-; replace (T + kThrStats + 8 * Z.of_nat 5) with (T + kThrStats + 40) by lia; exact N5|].
      destruct k as [|k]; [cbn in Hk; injection Hk as <-; replace (T + kThrStats + 8 * Z.of_nat 6) with (T + kThrStats + 40 + 8) by lia; exact N6|].
      do 4 (destruct k as [|k]; [cbn in Hk; injection Hk as <-; oldw D6 7%nat || oldw D6 8%nat || oldw D6 9%nat || oldw D6 10%nat |]).
      destruct k as [|k]; [cbn in Hk; injection Hk as <-; replace (T + kThrStats + 8 * Z.of_nat 11) with (T + kThrStats + 88) by lia; exact N11|].
      destruct k as [|k]; [cbn in Hk; injection Hk as <-; replace (T + kThrStats + 8 * Z.of_nat 12) with (T + kThrStats + 88 + 8) by lia; exact N12|].
      destruct k as [|k]; [cbn in Hk; injection Hk as <-; oldw D6 13%nat|].
      destruct k; cbn in Hk; discriminate. }
  split.
  { replace (ts_by_size (ts_on_munmap L (ts_on_real_free n TS))) with (ts_by_size TS) by reflexivity.
    eapply u64arr_agree; [| exact D7]. rewrite length_map, length_ziota. thr_ag. }
  eapply rw_cells_agree'; [| exact D8]; thr_ag.
Qed.

(* [comment removed for export] *)
Lemma repE_ld : arep_secondary segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & RE & _). destruct RE as [_ E2]. pose proof i_bound as [IB P1].
  pose proof swap as (LEN & MEM & IDX & _).
  unfold arep_secondary. rewrite ld_ptr, ld_sec. split.
  - right. split; [exact P1|]. exists junk. pose proof NC_ptr as U. pose proof NC_len as L'. rewrite ld_sec in U, L'. split; [exact U| exact L'].
  - intros j c Hj. destruct (IDX j c Hj) as [(-> & -> & NE & OLD)|(NJ & OLD & NE & NL)].
    + (* [comment removed for export] *)
      destruct (E2 _ _ OLD) as [X1 X2]. pose proof (lastc_beg_ne NE) as BNE. pose proof (sec_facts lastc lastc_in) as (_ & _ & _ & POS & _ & GE & _).
      apply rh_split with (cs1 := [C8 (zw (sc_map_beg lastc)); C8 (zw (sc_map_size lastc)); C8 (zw (sc_needed lastc))]) in X1 as [X1 _].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in X1.
      split.
      * apply (rh_join_at segs m' _ (sc_map_beg lastc + 24) [C8 (zw (sc_map_beg lastc)); C8 (zw (sc_map_size lastc)); C8 (zw (sc_needed lastc))]); [| exact (NC_idx BNE)| cbn; lia].
        eapply rw_cells_agree'; [| exact X1]. intros x Hx. cbn in Hx. apply (AGsec x lastc lastc_in NE); [clear -Hx; lia| intros _; clear -Hx; lia].
      * replace (sc_map_size lastc) with (24 + (8 + (sc_map_size lastc - 32))) by lia.
        apply wr_at_join; [lia| lia| |]; [| apply wr_at_join; [lia| clear -GE; lia| exact (rw_wr _ _ _ (NC_idx BNE))|]].
        -- eapply wr_at_agree; [| eapply (wr_at_sub segs _ _ _ _ _ X2); clear -GE; lia]. intros x Hx. apply (AG_secmap x lastc lastc_in NE); [clear -Hx GE; lia| intros _; left; clear -Hx; lia].
        -- eapply wr_at_agree; [| eapply (wr_at_sub segs _ _ _ _ _ X2); clear -GE; lia]. intros x Hx. apply (AG_secmap x lastc lastc_in NE); [clear -Hx GE; lia| intros _; right; clear -Hx; lia].
    + (* [comment removed for export] *)
      destruct (E2 _ _ OLD) as [X1 X2]. pose proof (nth_error_In _ _ OLD) as Hc.
      split.
      * eapply rw_cells_agree'; [| exact X1]. intros x Hx. cbn in Hx. apply (AGsec x c Hc NE); [clear -Hx; lia| intros EQ; exfalso; exact (NL EQ)].
      * eapply wr_at_agree; [| exact X2]. intros x Hx. apply (AG_secmap x c Hc NE Hx). intros EQ; exfalso; exact (NL EQ).
Qed.

(* [comment removed for export] *)
Lemma repF_ld : arep_chunks segs s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & RF & _).
  intros cb0 cm0 H0. rewrite ld_lookup in H0. destruct (decide (cb0 = cb)) as [->|NE]; [discriminate|].
  destruct (RF cb0 cm0 H0) as (X0 & (b1' & Hb1' & X1) & X2 & X3). split; [exact X0|]. split; [| split].
  - exists b1'. split; [exact Hb1'|]. eapply rw_cells_agree'; [| exact X1]. intros x Hx. cbn in Hx. apply (AGcm x cb0 cm0 H0 NE). left; lia.
  - intros Hrz. eapply rw_cells_agree'; [| exact (X2 Hrz)]. intros x Hx. cbn in Hx. apply (AGcm x cb0 cm0 H0 NE). right; left; split; [exact Hrz| lia].
  - destruct (cm_state cm0) as [i0|i0 j0] eqn:ST0; [exact I|]. eapply rw_cells_agree'; [| exact X3]. intros x Hx. cbn in Hx. apply (AGcm x cb0 cm0 H0 NE). right; right. rewrite ST0. lia.
Qed.

(* [comment removed for export] *)
Lemma repG_ld : arep_batches segs s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & RG & _). pose proof (frameG' segs s m m' AGbat RG) as [G1 G2].
  unfold arep_batches. rewrite ld_tq, ld_gq. split; eapply arep_batch_list_indep; eassumption.
Qed.

(* [comment removed for export] *)
Lemma DepotRep_frame_ag : forall s0 (mm mm' : mem),
  depot_inv E s0 -> DepotRep segs E s0 mm -> (forall a, DepotFPd E s0 a -> mm' (wa a) = mm (wa a)) -> DepotRep segs E s0 mm'.
Proof.
  clear. intros s0 mm mm' (_ & _ & _ & _ & NB0 & _) (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11) AGd.
  assert (NB : forall i0, 1 <= i0 <= zlen (depot_keys E s0) -> i0 / kDepotNodesPerBlock < zlen (node_blocks E s0)).
  { intros i0 Hi. unfold depot_keys, node_blocks, zlen in *. unfold depot_n_ids in NB0. cbn [length]. rewrite length_app in Hi.
    rewrite Nat2Z.inj_succ. apply Z.div_lt_upper_bound; [unfold kDepotNodesPerBlock; lia|]. unfold kDepotNodesPerBlock in *. lia. }
  assert (AGS : forall A0 k, aic_theDepot (ae_ic E) <= A0 -> A0 + k <= aic_theDepot (ae_ic E) + kDepotStaticBytes -> agree_on mm mm' A0 k).
  { intros A0 k H1 H2 x Hx. apply AGd. left. exists (aic_theDepot (ae_ic E), kDepotStaticBytes). split; [left; reflexivity| cbn [fst snd]; lia]. }
  assert (AGT : forall A0 k, aic_stackStore (ae_ic E) <= A0 -> A0 + k <= aic_stackStore (ae_ic E) + kStoreStaticBytes -> agree_on mm mm' A0 k).
  { intros A0 k H1 H2 x Hx. apply AGd. left. exists (aic_stackStore (ae_ic E), kStoreStaticBytes). split; [right; left; reflexivity| cbn [fst snd]; lia]. }
  unfold kDepotStaticBytes, kStoreStaticBytes in *.
  split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]].
  - intros b Hb. eapply rw_cells_agree'; [| exact (R1 b Hb)]. apply AGS; cbn; unfold kTabSize in Hb; lia.
  - eapply rw_cells_agree'; [| exact R2]. apply AGS; cbn; lia.
  - intros k Hk. eapply rw_cells_agree'; [| exact (R3 k Hk)]. apply AGS; cbn; unfold kNodesMap1 in Hk; lia.
  - intros i0 Hi. destruct (R4 i0 Hi) as (sid & X). exists sid. eapply rw_cells_agree'; [| exact X].
    destruct (node_addr_in_block E s0 i0 ltac:(lia) (NB i0 Hi)) as (b & Hb & L1 & L2).
    intros x Hx. apply AGd. right; left. exists b. split; [exact Hb| cbn in Hx; lia].
  - intros b Hb. eapply wr_at_agree; [| exact (R5 b Hb)]. intros x Hx. apply AGd. right; left. exists b. split; [exact Hb| exact Hx].
  - eapply rw_cells_agree'; [| exact R6]. apply AGT; cbn; lia.
  - destruct R7 as (al & X). exists al. eapply rw_cells_agree'; [| exact X]. apply AGT; cbn; lia.
  - intros k Hk. destruct (R8 k Hk) as (X1 & mx & X2). unfold kStoreBlockCount in Hk. split; [| exists mx].
    + eapply rw_cells_agree'; [| exact X1]. apply AGT; cbn; lia.
    + eapply rw_cells_agree'; [| exact X2]. apply AGT; cbn; lia.
  - intros b Hb. destruct (R9 b Hb) as (bs & U & L'). exists bs. split; [| exact L']. eapply u8arr_agree; [| exact U].
    intros x Hx. apply AGd. right; right. exists b. split; [exact Hb| lia].
  - eapply rw_cells_agree'; [| exact R10]. apply AGS; cbn; lia.
  - intros k Hk. eapply rw_cells_agree'; [| exact (R11 k Hk)]. unfold kStoreBlockCount in Hk. apply AGT; cbn; lia.
Qed.
Lemma repH_ld : arep_depot (DepotR segs E) s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & [DI DR] & _).
  pose proof (DepotRep_frame_ag s m m' DI DR AGdep) as DR'. unfold arep_depot, DepotR. split.
  - revert DI. clear. unfold depot_inv, depot_n_ids, dphi. destruct s; cbn; exact (fun H => H).
  - revert DR'. clear. unfold DepotRep, depot_hashes, depot_keys, node_blocks, store_blocks, node_addr. destruct s; cbn; exact (fun H => H).
Qed.

(* [comment removed for export] *)
Ltac zconsts Hx := unfold kInsSpaceBeg, kInsSecondary, kInsNReserved, kInsSecStats, kInsSecMutex, kInsGlobalStats, kInsQuarantine, kInsQMutex,
  kInsQGlobal, kInsFallbackMutex, kInsMaxUserDefined, kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats,
  kThrStats, kThrUnwinding, kRegSize, kBatchCap, kChunksBlockCount, kIaPageSizeOff in Hx |- *.
Ltac ag AG_ ARM := let Hx := fresh "Hx" in intros x Hx; cbn -[Z.add Z.mul Z.sub Z.of_nat Z.to_nat free_array region_beg region_of get_region Z.pow] in Hx; apply AG_; ARM Hx.
Ltac agN1 AG_ k := ag AG_ ltac:(fun Hx => eexists; split; [eapply nth_error_In with (n := k); reflexivity| cbn [fst snd length asan_flags_bytes]; zconsts Hx; lia]).
Lemma repI_ld : arep_globals segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & RI' & _).
  destruct RI' as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15 & I16 & I17 & I18). unfold arep_globals. rewrite ld_ia.
  split; [eapply u8arr_agree; [| exact I1]; agN1 AGimg1 0%nat|].
  split; [eapply rw_cells_agree'; [| exact I2]; agN1 AGimg1 1%nat|].
  split; [eapply rw_cells_agree'; [| exact I3]; agN1 AGimg1 2%nat|].
  split; [eapply rw_cells_agree'; [| exact I4]; agN1 AGimg1 3%nat|].
  split; [eapply rw_cells_agree'; [| exact I5]; agN1 AGimg1 4%nat|].
  split; [eapply rw_cells_agree'; [| exact I6]; agN1 AGimg1 5%nat|].
  split; [eapply rw_cells_agree'; [| exact I7]; agN1 AGimg1 6%nat|].
  split; [eapply rw_cells_agree'; [| exact I8]; agN1 AGimg1 7%nat|].
  split; [eapply rw_cells_agree'; [| exact I9]; agN1 AGimg1 8%nat|].
  split; [eapply rw_cells_agree'; [| exact I10]; agN1 AGimg1 9%nat|].
  split; [eapply rw_cells_agree'; [| exact I11]; agN1 AGimg1 10%nat|].
  split; [eapply rw_cells_agree'; [| exact I12]; agN1 AGimg1 11%nat|].
  split; [eapply rw_cells_agree'; [| exact I13]; agN1 AGimg1 12%nat|].
  split; [eapply u64arr_agree; [| exact I14]; agN1 AGimg1 13%nat|].
  split; [eapply rw_cells_agree'; [| exact I15]; agN1 AGimg1 14%nat|].
  split; [intros Hia; eapply rw_cells_agree'; [| exact (I16 Hia)]; agN1 AGimg1 15%nat|].
  split.
  { eapply u8arr_agree; [| exact I17]. intros x Hx. rewrite zeros_ia_len in Hx.
    apply AGimg1. eexists; split; [eapply nth_error_In with (n := 15%nat); reflexivity| cbn [fst snd]; zconsts Hx; clear -Hx; lia]. }
  eapply wr_at_agree; [| exact I18]. intros x Hx. apply AGimg1. eexists; split; [eapply nth_error_In with (n := 15%nat); reflexivity| cbn [fst snd]; clear -Hx; lia].
Qed.

(* [comment removed for export] *)
Lemma repJ_ld : arep_shadow segs E s' m'.
Proof.
  pose proof REP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RJ). pose proof (sec_facts sc sc_in) as (M1 & _ & _ & POS & M5 & _).
  intros g v Hg.
  destruct (Z_lt_le_dec (8 * g) A) as [LTm|GEm]; [| destruct (Z_lt_le_dec (8 * g) (A + L)) as [IN|GE2]].
  - rewrite (Sh_ld_out (8 * g) (or_introl LTm)) in Hg.
    eapply rw_cells_agree'; [| exact (RJ g v Hg)]. intros x Hx. cbn in Hx. replace x with (kShadowBase + g) by lia.
    apply (AGsh_out g v Hg). left. unfold kPageSize in M1. clear -LTm M1. Z.div_mod_to_equations. lia.
  - rewrite (Sh_ld_in (8 * g) v (conj GEm IN) Hg).
    replace (kShadowBase + g) with (kShadowBase + A / 8 + (g - A / 8)) by lia.
    apply (CB_byte segs m' (kShadowBase + A / 8) (Z.to_nat (L / 8)) (zb 0) (g - A / 8) NC_sh).
    unfold kPageSize in M1, M5. clear -GEm IN M1 M5 POS. Z.div_mod_to_equations. lia.
  - rewrite (Sh_ld_out (8 * g) (or_intror GE2)) in Hg.
    eapply rw_cells_agree'; [| exact (RJ g v Hg)]. intros x Hx. cbn in Hx. replace x with (kShadowBase + g) by lia.
    apply (AGsh_out g v Hg). right. exact GE2.
Qed.

Theorem ARep_after_ldl : AREP s' m'.
Proof.
  split; [exact repA_ld|]. split; [exact repB_ld|]. split; [exact repC_ld|]. split; [exact repD_ld|]. split; [exact repE_ld|].
  split; [exact repF_ld|]. split; [exact repG_ld|]. split; [exact repH_ld|]. split; [exact repI_ld| exact repJ_ld].
Qed.
End LDL.
End RLD.
End RC__1.
