(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_depot_defs R_sec_defs R_asan_defs R_allocate2 RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_geo0 RT_fkit RT_malstate RT_freestate RT_maltail RT_sys_stmt RT_malsec_state RT_malsec_rev.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GWf.
Definition ssum (l : list (Z * Z)) : Z := fold_right (fun e acc => snd e + acc) 0 l.

Lemma ssum_app : forall l1 l2, ssum (l1 ++ l2) = ssum l1 + ssum l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2; [reflexivity|].
  change (ssum ((x :: l1) ++ l2)) with (snd x + ssum (l1 ++ l2)). change (ssum (x :: l1)) with (snd x + ssum l1). rewrite IH. lia.
Qed.

Lemma ssum_nonneg : forall l, Forall (fun e => 0 <= snd e) l -> 0 <= ssum l.
Proof.
  induction l as [|x l IH]; intros H; [cbv [ssum fold_right]; lia|]. apply Forall_cons_iff in H as [H1 H2].
  change (ssum (x :: l)) with (snd x + ssum l). specialize (IH H2). lia.
Qed.

Lemma ssum_incl : forall (l1 l2 : list (Z * Z)), List.NoDup l1 -> incl l1 l2 -> Forall (fun e => 0 <= snd e) l2 -> ssum l1 <= ssum l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 ND HI HF; [cbn; exact (ssum_nonneg l2 HF)|].
  apply List.NoDup_cons_iff in ND as [Hx ND]. destruct (in_split x l2 (HI x (or_introl eq_refl))) as (pre & post & ->).
  assert (HI' : incl l1 (pre ++ post)).
  { intros y Hy. assert (Y : In y (pre ++ x :: post)) by (apply HI; right; exact Hy). apply in_app_or in Y as [Y|[Y|Y]];
      [apply in_or_app; left; exact Y | subst y; contradiction | apply in_or_app; right; exact Y]. }
  apply Forall_app in HF as [HF1 HF2]. apply Forall_cons_iff in HF2 as [Hx0 HF2].
  specialize (IH (pre ++ post) ND HI' ltac:(apply Forall_app; split; assumption)).
  rewrite ssum_app in IH. rewrite ssum_app. unfold ssum in *. cbn [fold_right]. lia.
Qed.

Lemma qsum_ssum : forall bs, qsum bs = ssum (flat_map snd bs).
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [flat_map qsum fold_right]. rewrite ssum_app, <- IH. unfold qsum, qn, ssum. reflexivity.
Qed.

Lemma filter_partition : forall {X} (f : X -> bool) (l : list X), (length (List.filter f l) + length (List.filter (fun x => negb (f x)) l))%nat = length l.
Proof. intros X f l. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter]. destruct (f x); cbn [negb length]; lia. Qed.

Lemma NoDup_map_inj : forall {X Y} (f : X -> Y) (l : list X), List.NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  List.NoDup (map f l).
Proof.
  intros X Y f l. induction l as [|x l IH]; intros ND Hi; [constructor|]. apply List.NoDup_cons_iff in ND as [Hx ND]. cbn [map].
  constructor.
  - intros Hin. apply in_map_iff in Hin as (y & Ey & Hy). assert (y = x) by (apply Hi; [right; exact Hy | left; reflexivity | exact Ey]).
    subst y. contradiction.
  - apply IH; [exact ND|]. intros a b Ha Hb Hab. apply Hi; [right; exact Ha | right; exact Hb | exact Hab].
Qed.

Lemma NoDup_filter' : forall {X} (f : X -> bool) (l : list X), List.NoDup l -> List.NoDup (List.filter f l).
Proof.
  intros X f l. induction l as [|x l IH]; intros ND; [constructor|]. apply List.NoDup_cons_iff in ND as [Hx ND]. cbn [List.filter].
  destruct (f x); [|exact (IH ND)]. constructor; [|exact (IH ND)]. intros Hin. apply filter_In in Hin as [Hin _]. contradiction.
Qed.

Lemma sec_nodup : forall Σ, sec_wf Σ -> List.NoDup (sec Σ) /\ (forall s1 s2, In s1 (sec Σ) -> In s2 (sec Σ) -> s_mb s1 = s_mb s2 -> s1 = s2).
Proof.
  intros Σ (_ & _ & _ & HF & HA & _).
  assert (D : forall k1 k2 s1 s2, nth_error (sec Σ) k1 = Some s1 -> nth_error (sec Σ) k2 = Some s2 -> s_mb s1 = s_mb s2 -> k1 = k2).
  { intros k1 k2 s1 s2 H1 H2 E. destruct (Nat.eq_dec k1 k2) as [X|X]; [exact X|]. exfalso.
    pose proof (HA k1 k2 s1 s2 H1 H2 X) as Y. pose proof (proj1 (Forall_forall _ _) HF s1 (nth_error_In _ _ H1)) as (Hn1 & _).
    pose proof (proj1 (Forall_forall _ _) HF s2 (nth_error_In _ _ H2)) as (Hn2 & _).
    assert (0 < smsz (s_n s1) /\ 0 < smsz (s_n s2)) by (pose proof (smsz_room (s_n s1) ltac:(lia)); pose proof (smsz_room (s_n s2) ltac:(lia)); lia).
    unfold apart in Y. lia. }
  split.
  - apply List.NoDup_nth_error. intros i j Hi Hij. destruct (nth_error (sec Σ) i) as [s1|] eqn:E1; [|apply nth_error_None in E1; lia].
    symmetry in Hij. exact (D i j s1 s1 E1 Hij eq_refl).
  - intros s1 s2 H1 H2 E. destruct (In_nth_error _ _ H1) as (k1 & K1). destruct (In_nth_error _ _ H2) as (k2 & K2).
    pose proof (D k1 k2 s1 s2 K1 K2 E) as ->. rewrite K1 in K2. injection K2 as ->. reflexivity.
Qed.

Theorem sec_count : forall Σ, rt_wf Σ -> Z.of_nat (length (sec Σ)) <= 4244.
Proof.
  intros Σ HW. pose proof HW as (_ & HR & HV & HS & HQ & _ & _ & _ & _ & _ & _ & HC).
  destruct (sec_nodup Σ HS) as (ND & INJ).
  pose proof HS as (_ & _ & _ & HSF & _).
  set (L := List.filter (fun s => negb (s_quar s)) (sec Σ)). set (Q := List.filter s_quar (sec Σ)).
  pose proof (filter_partition s_quar (sec Σ)) as PART. fold Q in PART. fold L in PART.

  assert (HL : (length L <= length (live Σ))%nat).
  { rewrite <- (map_length (fun s => (s_ubeg s, s_n s)) L). apply List.NoDup_incl_length.
    - apply NoDup_map_inj; [exact (NoDup_filter' _ _ ND)|]. intros x y Hx Hy E. injection E as E1 _.
      apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _]. apply INJ; [exact Hx | exact Hy | unfold s_ubeg in E1; lia].
    - intros e He. apply in_map_iff in He as (s & <- & Hs). apply filter_In in Hs as [Hs Hq]. destruct (s_quar s) eqn:E; [discriminate|].
      destruct HV as (_ & _ & _ & _ & V5). exact (V5 s Hs E). }
  assert (HLv : Z.of_nat (length (live Σ)) <= LIVE_MAX) by exact (proj1 HV).

  destruct HQ as (Q1 & Q2 & _ & _ & _ & Q6 & _).
  destruct HC as (_ & C2).
  assert (HQs : Z.of_nat (length Q) * 64513 <= ssum (qents Σ)).
  { set (Q' := map (fun s => (s_mb s + 6128, s_n s)) Q).
    assert (E1 : 64513 * Z.of_nat (length Q) <= ssum Q').
    { unfold Q'. assert (HQF : Forall (fun s => 64513 <= s_n s) Q).
      { apply Forall_forall. intros s Hs. apply filter_In in Hs as [Hs _]. exact (proj1 (proj1 (proj1 (Forall_forall _ _) HSF s Hs))). }
      clear - HQF. induction Q as [|s Q IH]; [cbn; lia|]. apply Forall_cons_iff in HQF as [H1 H2]. cbn [map ssum fold_right length].
      unfold ssum in IH. specialize (IH H2). cbn [snd]. lia. }
    assert (E2 : ssum Q' <= ssum (qents Σ)).
    { apply ssum_incl.
      - unfold Q'. apply NoDup_map_inj; [exact (NoDup_filter' _ _ ND)|]. intros x y Hx Hy E. injection E as Exy _.
        apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _]. apply INJ; [exact Hx | exact Hy | lia].
      - intros e He. unfold Q' in He. apply in_map_iff in He as (s & <- & Hs). apply filter_In in Hs as [Hs Hq]. exact (C2 s Hs Hq).
      - apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) Q6 e He) as
          [(c & i & Hc & Hi & _)|(s & Hs & _ & Hsn & _)].
        + destruct HR as (R1 & _). pose proof (R1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
          pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hi)) as X. cbv beta iota in X. lia.
        + pose proof (proj1 (Forall_forall _ _) HSF s Hs) as ((X & _) & _). lia. }
    lia. }
  assert (HQb : ssum (qents Σ) <= QMAX_L + 0x10000 + QMAX_G + 0x10000).
  { unfold qents. rewrite <- qsum_ssum. unfold qbytes in Q1, Q2. unfold qsum at 1. rewrite fold_right_app.
    assert (X : forall bs acc, fold_right (fun b a => qn b + a) acc bs = qsum bs + acc).
    { induction bs as [|b bs IH]; intros acc; [reflexivity|]. cbn [fold_right]. rewrite IH. unfold qsum. cbn [fold_right]. lia. }
    rewrite X. unfold qsum in *. lia. }
  unfold QMAX_L, QMAX_G, LIVE_MAX in *. rewrite <- PART. rewrite Nat2Z.inj_add. lia.
Qed.

Section MalSecWf.
Variables (Σ : rtsA) (m : mem) (P n : Z) (D' : depot).
Hypothesis HA : ART_A Σ m.
Hypothesis HG : sgrant_ok Σ P (smsz n).
Hypothesis Hn : 64512 < n <= 0x20001000.
Hypothesis Hlive : Z.of_nat (length (live Σ)) < LIVE_MAX.
Hypothesis Hcr : mcost n <= credit Σ.
Hypothesis HDok : depot_ok D' (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis HDinv : dep_step (dep Σ) D'.
#[local] Notation L := (lay Σ).
#[local] Notation msz := (smsz n).

Lemma ms_window : A_wf [shw P n] /\ A_bytes [shw P n] <= mcost n.
Proof using HA HG Hn.
  pose proof (rv_shad Σ m P n HA HG Hn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  pose proof (rv_map Σ m P n HA HG Hn) as (_ & _ & _ & _ & _ & M6 & M7 & M8 & _).
  pose proof (pg_dn_facts (shad P) ltac:(unfold SHB in *; lia)) as (D1 & D2 & D3).
  pose proof (pg_up_facts (shad (P + msz)) ltac:(unfold SHB in *; lia)) as (U1 & U2).
  assert (Hm : msz / 8 <= 0x20005000 / 8) by (apply Z.div_le_mono; lia).
  split.
  - unfold A_wf. apply Forall_cons; [|apply Forall_nil]. unfold shw, page_size. cbn [fst snd]. split; [lia|]. split; assumption.
  - unfold shw. cbn [A_bytes fst snd]. unfold mcost, DCOST. rewrite (proj2 (Z.leb_gt n 64512)) by lia.
    assert (Hms : msz <= 2 * n + 16384).
    { assert (RZ : rz_size n = 2048) by (apply rz_size_big; lia).
      assert (ND : needed n = 8 * ((n + 7) / 8) + 2048) by (unfold needed, rounded; rewrite RZ, !Z.max_l by lia; reflexivity).
      pose proof (Z.mul_div_le (n + 7) 8 ltac:(lia)) as MD. pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)) as DP.
      pose proof (pg_up_facts (needed n + rz_size n) ltac:(rewrite ND, RZ; lia)) as (U & _).
      unfold smsz. rewrite ND, RZ in *. lia. }
    assert (Hm8 : msz / 8 <= n) by (apply Z.div_le_upper_bound; lia).
    lia.
Qed.

Lemma ms_live_new : ~ In (s_ubeg (sec_new P n)) (map fst (live Σ)).
Proof using HA HG Hn.
  intros Hin. apply in_map_iff in Hin as ([p' n'] & Hp' & Hin). cbn [fst] in Hp'. unfold s_ubeg, sec_new in Hp'. cbn [s_mb] in Hp'.
  pose proof (rv_map Σ m P n HA HG Hn) as (M1 & M2 & M3 & M4 & M5 & M6 & _).
  destruct (geo_live Σ m HA p' n' Hin) as [(c & i & Hc & Hi & Ep & X1 & X2 & X3 & X4 & X5)|(s & Hs & _ & Hsn & Ep & X1 & X5)].
  - pose proof (rv_grant_apart Σ m P n HA HG (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as Ap.
    pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). unfold apart, rb, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
  - destruct HG as (_ & Hap).
    pose proof (proj1 (Forall_forall _ _) Hap (secmap s) ltac:(unfold rt_maps; apply in_or_app; left;
      apply in_map; apply (proj1 (in_rev (sec Σ) s)); exact Hs)) as Y.
    destruct (In_nth_error _ _ Hs) as (k0 & Hk0).
    pose proof (rv_sec_app Σ m HA k0 s Hk0) as (Z1 & Z2 & Z3).
    pose proof (rv_map Σ m P n HA HG Hn) as (_ & _ & _ & _ & _ & M6' & _ & _ & M9').
    pose proof (ART_wf Σ m HA) as (_ & _ & _ & (_ & _ & _ & HSF & _) & _).
    pose proof (proj1 (Forall_forall _ _) HSF s Hs) as ((Hns & _) & (Gs1 & _ & Gs3 & _) & _).
    pose proof (smsz_room (s_n s) ltac:(lia)) as SR.
    unfold secmap in Y. cbn [fst snd] in Y. rewrite !unsigned_lit in Y by (unfold l_ACEIL, STACK_WIN in *; lia). unfold apart, s_ubeg in *.
    lia.
Qed.

Theorem mal_sec_wf : rt_wf (mal_sec Σ P n D').
Proof using HA HG Hn Hlive Hcr HDok HDinv.
  pose proof (ART_wf Σ m HA) as HW. pose proof HW as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12).
  assert (POT' : dep_pot (d_n D') (Z.of_nat (length (live Σ)) + 1) (credit Σ - mcost n)) by exact (dep_pot_malloc (dep Σ) D' _ _ n HDinv W9 Hcr).
  pose proof (dep_inv_bounds D' _ _ (proj1 HDinv) POT' ltac:(lia) ltac:(lia)) as (B1 & B2).
  pose proof (sec_count Σ HW) as HSC.
  pose proof (sec_eager_room Σ n HW ltac:(lia) Hcr) as (ER1 & ER2).
  pose proof ms_window as (AW1 & AW2).
  pose proof HG as ((G1 & G2 & G3 & G4 & G5) & Hap).
  pose proof (rv_map Σ m P n HA HG Hn) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  assert (ERm : rt_eager (mal_sec Σ P n D') <= 2 ^ 38) by (rewrite rt_eager_mal, rt_eager_sp; exact ER2).
  assert (SSm : secsum (mal_sec Σ P n D') = secsum Σ + msz) by (unfold secsum, mal_sec; cbn [sec]; rewrite fold_smsz_app; reflexivity).
  unfold mal_sec in ERm, SSm.
  unfold rt_wf, mal_sec. cbn [lay pr ca ca_init sec sec_nres aw ql qg dep fs0 fsc0 fs4 fs1 fs3 ia_init credit live frames ann].
  split; [exact W1|]. split; [exact W2|].
  split.
  {
    unfold live_wf. cbn [pr live lay sec]. destruct W3 as (V1 & V2 & V3 & V4 & V5). split; [cbn [length]; lia|]. split.
    - apply NoDup_ListNoDup. apply NoDup_ListNoDup in V2. cbn [map fst]. constructor; [exact ms_live_new | exact V2].
    - split; [|split].
      + intros p' n' [E|Hin].
        * injection E as <- <-. right. exists (sec_new P n). split; [apply in_or_app; right; left; reflexivity|].
          split; [reflexivity|]. split; reflexivity.
        * destruct (V3 p' n' Hin) as [X|(s & Hs & Hq & Hsn & Ep)]; [left; exact X|]. right. exists s.
          split; [apply in_or_app; left; exact Hs|]. split; [exact Hq|]. split; [exact Hsn | exact Ep].
      + intros c' i' n' Hc' Hn'. right. exact (V4 c' i' n' Hc' Hn').
      + intros s Hs Hq. apply in_app_or in Hs as [Hs|[Hs|[]]].
        * right. exact (V5 s Hs Hq).
        * subst s. left. reflexivity. }
  split.
  {
    unfold sec_wf. cbn [sec sec_nres aw lay]. destruct W4 as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
    split; [rewrite length_app; cbn [length]; unfold SEC_MAX; lia|]. split; [right; reflexivity|]. split; [intros _; reflexivity|].
    split.
    { apply Forall_app. split; [exact S4|]. apply Forall_cons; [|apply Forall_nil]. cbn [sec_new s_mb s_n].
      split; [lia|]. split; [exact (proj1 HG)|].
      pose proof (rv_grant_apart Σ m P n HA HG) as GA.
      split; [exact (GA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity))|].
      split; [exact (GA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; do 5 right; left; reflexivity))|].
      apply Forall_forall. intros [b gn] Hin. exact (GA b gn Hin). }
    split.
    { intros k1 k2 s1 s2 H1 H2 Hne.
      assert (NEW : forall k s, nth_error (sec Σ ++ [sec_new P n]) k = Some s -> (k = length (sec Σ) /\ s = sec_new P n)
                                \/ ((k < length (sec Σ))%nat /\ nth_error (sec Σ) k = Some s)).
      { intros k s Hk. destruct (Nat.lt_ge_cases k (length (sec Σ))) as [X|X].
        - right. split; [exact X|]. rewrite nth_error_app1 in Hk by exact X. exact Hk.
        - left. rewrite nth_error_app2 in Hk by exact X. destruct (k - length (sec Σ))%nat as [|j] eqn:Ej.
          + cbn in Hk. injection Hk as <-. split; [lia | reflexivity].
          + cbn in Hk. destruct j; discriminate. }
      assert (APN : forall s, In s (sec Σ) -> apart (s_mb s) (smsz (s_n s)) P msz).
      { intros s Hs. pose proof (proj1 (Forall_forall _ _) Hap (secmap s) ltac:(unfold rt_maps; apply in_or_app; left;
          apply in_map; apply (proj1 (in_rev (sec Σ) s)); exact Hs)) as Y.
        destruct (In_nth_error _ _ Hs) as (k0 & Hk0). pose proof (rv_sec_app Σ m HA k0 s Hk0) as (Z1 & Z2 & Z3).
        pose proof (proj1 (Forall_forall _ _) S4 s Hs) as ((Hns & _) & (Gs1 & _ & Gs3 & _) & _).
        unfold secmap in Y. cbn [fst snd] in Y. rewrite !unsigned_lit in Y by (unfold l_ACEIL, STACK_WIN in *; lia). unfold apart in *. lia. }
      destruct (NEW k1 s1 H1) as [(E1 & ->)|(K1 & X1)]; destruct (NEW k2 s2 H2) as [(E2 & ->)|(K2 & X2)].
      - exfalso. apply Hne. congruence.
      - pose proof (APN s2 (nth_error_In _ _ X2)) as Y. unfold apart in *. cbn [sec_new s_mb s_n]. lia.
      - exact (APN s1 (nth_error_In _ _ X1)).
      - exact (S5 k1 k2 s1 s2 X1 X2 Hne). }
    split.
    { apply Forall_app. split.
      - apply Forall_forall. intros s Hs. right. exact (proj1 (Forall_forall _ _) S6 s Hs).
      - apply Forall_cons; [|apply Forall_nil]. left. reflexivity. }
    apply Forall_app. split; [exact S7|]. apply Forall_cons; [|apply Forall_nil]. cbn [sec_new s_quar]. intros X. discriminate X. }
  split.
  {
    unfold quar_wf. cbn [ql qg pr lay sec]. destruct W5 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|]. split; [exact Q5|].
    split; [|split; [exact Q7 | exact Q8]].
    apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) Q6 e He) as [X|(s & Hs & Hq & Hsn & Ee)]; [left; exact X|].
    right. exists s. split; [apply in_or_app; left; exact Hs|]. split; [exact Hq|]. split; [exact Hsn | exact Ee]. }
  split.
  {
    unfold fs_wf. cbn [fs0 fsc0 fs4 fs1 fs3 frames lay credit]. destruct W6 as (F1 & F2 & F3 & F3b & F3c & F4 & F5 & F6 & F7 & F8).
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F3b|]. split; [exact F3c|]. split; [exact F4|]. split; [exact F5|]. split; [exact F6|].
    split; [exact F7|]. intros k Hk. pose proof (F8 k Hk) as X. unfold fs_of in *. cbn [fs0 fsc0 fs4 fs1 fs3].
    assert (0 <= mcost n) by (unfold mcost, DCOST; destruct (n <=? 64512); lia). lia. }
  split.
  {
    unfold budget_wf. cbn [credit aw]. destruct W7 as (BW1 & BW2 & BW3 & BW4 & BW5).
    split; [lia|]. split; [exact (A_wf_app [shw P n] (aw Σ) AW1 BW2)|].
    split; [change (shw P n :: aw Σ) with ([shw P n] ++ aw Σ); rewrite A_bytes_app; lia|].
    split; [exact ERm|]. rewrite SSm. lia. }
  split; [exact HDok|]. split; [cbn [length]; rewrite Nat2Z.inj_succ; unfold Z.succ; exact POT'|]. split; [lia|]. split; [exact (proj1 HDinv)|].
  {
    unfold rt_count. cbn [pr sec lay ql qg]. destruct W12 as (C1 & C2). split; [exact C1|].
    intros s Hs Hq. apply in_app_or in Hs as [Hs|[Hs|[]]]; [exact (C2 s Hs Hq)|]. subst s. cbn in Hq. discriminate. }
Qed.

End MalSecWf.
