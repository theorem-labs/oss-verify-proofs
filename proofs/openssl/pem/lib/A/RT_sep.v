(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface R_cache_defs R_prim_defs R_thread R_m2s R_poison R_setshadow R_leaves R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition live_iv (pn : Z * Z) : ivl := (fst pn, fst pn + snd pn).
Definition frame_iv (fk : Z * nat) : ivl := (fst fk, fst fk + fs_size (snd fk) - 8).
Definition fshad_iv (fk : Z * nat) : ivl := (shad (fst fk), shad (fst fk + fs_size (snd fk))).

Definition W_client (Σ : rtsA) (sp : Z) : list ivl :=
  [(sp, USTACK_TOP)] ++ CS_W ++ map live_iv (live Σ) ++ map frame_iv (frames Σ) ++ map fshad_iv (frames Σ).

Lemma not_outside : forall W lo hi x, In (lo, hi) W -> lo <= x < hi -> ~ outside W x.
Proof.
  induction W as [|[lo' hi'] W IH]; intros lo hi x Hin Hx Ho; [exact Hin|]. cbn in Hin, Ho. destruct Ho as [H1 H2].
  destruct Hin as [Hin|Hin]; [injection Hin as <- <-; exact (H1 Hx)| exact (IH _ _ _ Hin Hx H2)].
Qed.

Lemma outside_app_inv : forall W1 W2 x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
Proof.
  induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn in *; [split; [exact I | exact H]|].
  destruct H as [H1 H2]. destruct (IH _ _ H2) as [X Y]. split; [split; [exact H1 | exact X]| exact Y].
Qed.

Lemma outside_map_in : forall {X} (f : X -> ivl) l e x, In e l -> fst (f e) <= x < snd (f e) -> ~ outside (map f l) x.
Proof. intros X f l e x Hin Hx. apply (not_outside _ (fst (f e)) (snd (f e))); [|exact Hx]. apply in_map_iff. exists e. destruct (f e); split; reflexivity || exact Hin. Qed.

Ltac cs_pick lo hi := apply (not_outside CS_W lo hi); [unfold CS_W; repeat (first [left; reflexivity | right]) | lia].
Ltac rt_contra lo hi Hn := exfalso; apply Hn; exists lo, hi; split; [unfold RT_STATIC; repeat (first [left; reflexivity | right]) | lia].

Lemma client_static_cover : forall x, client_static x -> ~ outside CS_W x.
Proof.
  intros x (Hin & Hn). destruct Hin as (lo & hi & Hin & Hx). unfold CLIENT_STATIC in Hin.
  destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
  - cs_pick 0x5a9d08 0x6694d8.
  - cs_pick 0xb8f190 0xb9f190.
  - destruct (Z_lt_le_dec x 0xba3e98); [cs_pick 0xb9f190 0xba3e98|].
    destruct (Z_lt_le_dec x 0xba3ea0); [rt_contra 0xba3e98 0xba3ea0 Hn|].
    destruct (Z_lt_le_dec x 0xba3ee8); [cs_pick 0xba3ea0 0xba3ee8|].
    destruct (Z_lt_le_dec x 0xba3f18); [rt_contra 0xba3ee8 0xba3f18 Hn|].
    destruct (Z_lt_le_dec x 0xba3f20); [cs_pick 0xba3f18 0xba3f20|].
    destruct (Z_lt_le_dec x 0xba3f30); [rt_contra 0xba3f20 0xba3f30 Hn|].
    destruct (Z_lt_le_dec x 0xbc41b0); [cs_pick 0xba3f30 0xbc41b0|].
    destruct (Z_lt_le_dec x 0xbc41b8); [rt_contra 0xbc41b0 0xbc41b8 Hn|].
    destruct (Z_lt_le_dec x 0xbc5298); [cs_pick 0xbc41b8 0xbc5298|].
    destruct (Z_lt_le_dec x 0xbc52a0); [rt_contra 0xbc5298 0xbc52a0 Hn|].
    cs_pick 0xbc52a0 0xbc57d0.
Qed.

(* [comment removed for export] *)
Lemma W_client_cover : forall Σ sp x, aclient (live Σ) (frames Σ) sp x -> ~ outside (W_client Σ sp) x.
Proof.
  intros Σ sp x H Ho. unfold W_client in Ho.
  apply outside_app_inv in Ho as [H1 Ho]. apply outside_app_inv in Ho as [H2 Ho]. apply outside_app_inv in Ho as [H3 Ho].
  apply outside_app_inv in Ho as [H4 H5].
  destruct H as [H|[H|[H|[H|H]]]].
  - cbn in H1. exact (proj1 H1 H).
  - exact (client_static_cover x H H2).
  - destruct H as (p & n & Hin & Hx). exact (outside_map_in live_iv _ (p, n) x Hin ltac:(cbn; lia) H3).
  - destruct H as (f & k & Hin & Hx). exact (outside_map_in frame_iv _ (f, k) x Hin ltac:(cbn; lia) H4).
  - destruct H as (f & k & Hin & Hx). exact (outside_map_in fshad_iv _ (f, k) x Hin ltac:(cbn; lia) H5).
Qed.

(* [comment removed for export] *)
Lemma munch_client : forall Σ sp (m m' : mem),
  (forall a : word, ~ aclient (live Σ) (frames Σ) sp (bv_unsigned a) -> m' a = m a) -> munch (W_client Σ sp) m m'.
Proof. intros Σ sp m m' H x Hx. apply H. intros Hc. exact (W_client_cover Σ sp _ Hc Hx). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma dsj_map : forall {X} (f : X -> ivl) l a n, Forall (fun e => a + n <= fst (f e) \/ snd (f e) <= a) l -> disjoint_from (map f l) a n.
Proof.
  intros X f l a n H. induction l as [|e l IH]; [exact I|]. apply Forall_cons_iff in H as [H1 H2]. cbn [map disjoint_from].
  cbv beta in H1. revert H1. destruct (f e) as [lo hi]. cbn. intros H1. split; [exact H1 | exact (IH H2)].
Qed.

Lemma avoid_client_intro : forall Σ sp a n, a + n <= sp -> disjoint_from CS_W a n ->
  Forall (fun pn => a + n <= fst pn \/ fst pn + snd pn <= a) (live Σ) ->
  Forall (fun fk => a + n <= fst fk \/ fst fk + fs_size (snd fk) - 8 <= a) (frames Σ) ->
  Forall (fun fk => a + n <= shad (fst fk) \/ shad (fst fk + fs_size (snd fk)) <= a) (frames Σ) ->
  disjoint_from (W_client Σ sp) a n.
Proof.
  intros Σ sp a n H1 H2 H3 H4 H5. unfold W_client.
  apply dsj_app; [cbn; split; [left; exact H1 | exact I]|]. apply dsj_app; [exact H2|].
  apply dsj_app; [apply dsj_map; exact H3|]. apply dsj_app; apply dsj_map; assumption.
Qed.

(* [comment removed for export] *)
Lemma dsj_CS_out : forall a n, a + n <= 0x10000 \/ SEGTOP_A <= a -> disjoint_from CS_W a n.
Proof. intros a n H. unfold SEGTOP_A in H. cbn. repeat split; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Geo.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma geo_wf : rt_wf Σ. Proof. exact (ART_wf Σ m HA). Qed.
Lemma geo_layout : layout_ok L. Proof. exact (proj1 geo_wf). Qed.

(* [comment removed for export] *)
Lemma geo_grant : forall b n, In (b, n) (startup_grants L) -> grant_ok L b n.
Proof.
  intros b n Hin. pose proof geo_layout as HL. unfold layout_ok in HL.
  destruct HL as (_ & _ & _ & _ & G1 & _ & _ & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
  unfold startup_grants in Hin. destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]; injection E as <- <-; assumption.
Qed.

Lemma geo_apart : forall i j g1 g2, (i < j)%nat -> nth_error (startup_grants L) i = Some g1 -> nth_error (startup_grants L) j = Some g2 ->
  apart (fst g1) (snd g1) (fst g2) (snd g2).
Proof. pose proof geo_layout as HL. unfold layout_ok in HL. repeat match type of HL with _ /\ ?R => destruct HL as [_ HL] end. exact HL. Qed.

(* [comment removed for export] *)
Lemma geo_prb : l_PRB L <= SB /\ SB + 2 ^ 37 + 4096 <= l_PRB L + 0x2000011000 /\ SB mod 2 ^ 16 = 0.
Proof.
  pose proof geo_layout as HL. unfold layout_ok in HL. destruct HL as (_ & _ & _ & _ & _ & Hsb & Hsb2 & _). lia.
Qed.

(* [comment removed for export] *)
Lemma geo_live : forall p n, In (p, n) (live Σ) ->
  (exists c i, 1 <= c <= 31 /\ nth_error (r_st (pr Σ c)) i = Some (CkAlloc n)
     /\ p = p_ubeg SB c i n /\ p_abeg SB c i + 16 <= p /\ p + n <= p_abeg SB c i + ClassSize c
     /\ rb SB c <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + kUserCap /\ 0 <= n)
  \/ (exists s, In s (sec Σ) /\ s_quar s = false /\ s_n s = n /\ p = s_ubeg s /\ s_mb s + 6144 + n <= s_mb s + smsz n /\ 0 <= n).
Proof.
  intros p n Hin. pose proof geo_wf as (_ & HR & HV & HS & _). destruct HV as (_ & _ & HVin & _).
  destruct (HVin p n Hin) as [(c & i & Hc & Hn & ->)|(s & Hs & Hq & <- & ->)].
  - left. exists c, i. split; [exact Hc|]. split; [exact Hn|]. split; [reflexivity|].
    destruct HR as (HR & _). pose proof (HR c Hc) as (W1 & _ & W3 & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (nth_error_In _ _ Hn) as Hi. pose proof (proj1 (Forall_forall _ _) W10 _ Hi) as (Hn0 & Hfit & _). cbv beta iota in Hn0, Hfit.
    pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
    pose proof (ClassSize_pos c Hc) as Hcs. unfold p_ubeg, p_abeg, rb, kUserCap in *.
    assert (Hm : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
    { replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
      replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
      apply Z.mul_le_mono_nonneg_r; lia. }
    assert (Hx : 0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia).
    assert (Hrz : 16 <= rz_size n) by (unfold rz_size; pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)); lia).
    repeat split; lia.
  - right. exists s. destruct HS as (_ & _ & _ & HSF & _). pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (Hsn & _).
    pose proof (smsz_room (s_n s) ltac:(lia)) as Hroom. unfold s_ubeg. repeat split; try assumption; try reflexivity; lia.
Qed.

End Geo.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sep.
Variables (Σ : rtsA) (m : mem) (sp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hsp : rtA_sp0 Σ - STACK_WIN <= sp.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation W := (W_client Σ sp).

(* [comment removed for export] *)
Lemma sep_frame : forall f k, In (f, k) (frames Σ) -> l_FSB L + 0x9000 <= f /\ f + fs_size k <= l_FSB L + 0xb09000 /\ 0 < fs_size k.
Proof.
  intros f k Hin. destruct (rta_frame_in Σ m f k HA Hin) as (Hk & H1 & H2). split; [exact H1|]. split; [exact H2|].
  unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma sep_fshad : forall f k, In (f, k) (frames Σ) -> SHB <= shad f /\ shad (f + fs_size k) <= K_HIGH_SHADOW_hi.
Proof.
  intros f k Hin. destruct (sep_frame f k Hin) as (H1 & H2 & H3). pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  unfold l_ACEIL, STACK_WIN in G3. pose proof (rta_sp0 Σ m HA) as ((W1 & W2) & _). unfold rtA_sp0, sp_window_hi in *.
  unfold shad, K_HIGH_SHADOW_hi, SHB. split; [pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)); lia|].
  assert ((f + fs_size k) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma sep_fshad_app : forall a n, (a + n <= K_LOW_SHADOW_lo \/ K_HIGH_SHADOW_hi <= a) ->
  Forall (fun fk => a + n <= shad (fst fk) \/ shad (fst fk + fs_size (snd fk)) <= a) (frames Σ).
Proof.
  intros a n H. apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (sep_fshad f k Hin) as [X Y].
  unfold K_LOW_SHADOW_lo, SHB in *. lia.
Qed.

(* [comment removed for export] *)
Lemma sep_stack : forall a n, a + n <= l_ACEIL L -> a + n <= sp.
Proof. intros a n H. unfold l_ACEIL, rtA_sp0 in *. lia. Qed.

(* [comment removed for export] *)
Lemma ac_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from CS_W a n -> disjoint_from W a n.
Proof.
  intros a n H1 H2 H3. pose proof (rta_sp0_range Σ m HA) as Hr. unfold rtA_sp0 in Hr.
  apply avoid_client_intro; [unfold rtA_sp0, STACK_WIN, SEGTOP_A in *; lia | exact H3 | | |].
  - apply Forall_forall. intros [p n'] Hin. cbn [fst snd]. pose proof (rta_live_range Σ m p n' HA Hin) as (_ & _ & X). unfold SEGTOP_A in *. lia.
  - apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (sep_frame f k Hin) as (X & Y & _).
    pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & _ & _ & G5).
    unfold SEGTOP_A in *. lia.
  - apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (sep_fshad f k Hin) as [X _]. unfold SHB, SEGTOP_A in *. lia.
Qed.

(* [comment removed for export] *)
Lemma ac_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof.
  intros b gn a n Hin HP HF H1 H2. pose proof (geo_grant Σ m HA b gn Hin) as (G1 & G2 & G3 & G4 & G5).
  pose proof (geo_prb Σ m HA) as (P1 & P2 & P3).
  apply avoid_client_intro; [apply sep_stack; lia | apply dsj_CS_out; unfold SEGTOP_A in *; lia | | | apply sep_fshad_app; lia].
  - apply Forall_forall. intros [p n'] Hin'. cbn [fst snd].
    destruct (geo_live Σ m HA p n' Hin') as [(c & i & Hc & _ & _ & X1 & X2 & X3 & X4 & X5)|(s & Hs & _ & Hn' & -> & X1 & X5)].
    + unfold rb, apart, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
    + pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
      pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (_ & _ & _ & _ & HG). pose proof (proj1 (Forall_forall _ _) HG (b, gn) Hin) as Ha.
      cbn [fst snd] in Ha. unfold apart, s_ubeg in *. rewrite <- Hn' in X1. lia.
  - apply Forall_forall. intros [f k] Hin'. cbn [fst snd]. destruct (sep_frame f k Hin') as (X & Y & _). unfold apart in HF. lia.
Qed.

(* [comment removed for export] *)
Lemma ac_shad : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
  (forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) -> disjoint_from W a n.
Proof.
  intros lo hi a n Hl Hh H0 H47 H1 H2 HF. pose proof (rta_sp0 Σ m HA) as ((W1 & W2) & _). unfold rtA_sp0, sp_window_lo in *.
  assert (Hs : shad hi <= 2 ^ 44 + SHB) by (unfold shad; assert (hi / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia); lia).
  assert (Hs0 : SHB <= shad lo) by (unfold shad; pose proof (Z.div_pos lo 8 ltac:(lia) ltac:(lia)); lia).
  apply avoid_client_intro; [unfold rtA_sp0, STACK_WIN, SHB in *; lia | apply dsj_CS_out; unfold SHB, SEGTOP_A in *; lia | | |].
  - apply Forall_forall. intros [p n'] Hin. cbn [fst snd]. pose proof (rta_live_range Σ m p n' HA Hin) as (X1 & X2 & _).
    destruct (geo_live Σ m HA p n' Hin) as [(c & i & Hc & _ & _ & Y1 & Y2 & Y3 & Y4 & Y5)|(s & Hs' & _ & Hn' & -> & Y1 & Y5)].
    + pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & _ & G4 & _).
      pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). unfold rb, kUserCap, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *.
      assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
    + pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
      pose proof (proj1 (Forall_forall _ _) HSF s Hs') as (_ & (_ & _ & _ & G4 & _) & _). unfold s_ubeg, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *.
      rewrite <- Hn' in Y1. lia.
  - apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (sep_frame f k Hin) as (X & Y & _).
    pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & _ & G4 & _).
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
  - apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (HF f k Hin) as [X|X]; [left | right];
      unfold shad in *; [ assert (hi / 8 <= f / 8) by (apply Z.div_le_mono; lia) | assert ((f + fs_size k) / 8 <= lo / 8) by (apply Z.div_le_mono; lia) ]; lia.
Qed.

(* [comment removed for export] *)
Lemma ac_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 ->
  (forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
     a + n <= p_ubeg SB c i n' \/ p_ubeg SB c i n' + n' <= a) -> disjoint_from W a n.
Proof.
  intros a n H1 H2 HL. pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  apply avoid_client_intro; [apply sep_stack; lia | apply dsj_CS_out; unfold SEGTOP_A in *; lia | | | apply sep_fshad_app; lia].
  - apply Forall_forall. intros [p n'] Hin'. cbn [fst snd].
    destruct (geo_live Σ m HA p n' Hin') as [(c & i & Hc & Hn' & -> & _)|(s & Hs & _ & Hn' & -> & X1 & X5)]; [exact (HL c i n' Hc Hn')|].
    pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
    pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (_ & _ & Ha & _). unfold apart, s_ubeg in *. rewrite <- Hn' in X1. lia.
  - apply Forall_forall. intros [f k] Hin'. cbn [fst snd]. destruct (sep_frame f k Hin') as (X & Y & _).
    pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart in Ha. lia.
Qed.

(* [comment removed for export] *)
Lemma ac_secmap : forall k0 s0 a n, nth_error (sec Σ) k0 = Some s0 -> s_mb s0 <= a -> a + n <= s_mb s0 + smsz (s_n s0) ->
  (s_quar s0 = false -> a + n <= s_ubeg s0 \/ s_ubeg s0 + s_n s0 <= a) -> disjoint_from W a n.
Proof.
  intros k0 s0 a n Hk0 H1 H2 HU. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & HSP & _).
  pose proof (proj1 (Forall_forall _ _) HSF s0 (nth_error_In _ _ Hk0)) as (_ & (G1 & G2 & G3 & G4 & G5) & Hp & Hf & _).
  apply avoid_client_intro; [apply sep_stack; lia | apply dsj_CS_out; unfold SEGTOP_A in *; lia | | | apply sep_fshad_app; lia].
  - apply Forall_forall. intros [p n'] Hin'. cbn [fst snd].
    destruct (geo_live Σ m HA p n' Hin') as [(c & i & Hc & _ & _ & X1 & X2 & X3 & X4 & X5)|(s & Hs & Hq & Hn' & -> & X1 & X5)].
    + pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). unfold rb, apart, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
    + destruct (In_nth_error _ _ Hs) as (k & Hk). destruct (Nat.eq_dec k k0) as [->|Hne].
      * rewrite Hk0 in Hk. injection Hk as <-. rewrite <- Hn'. exact (HU Hq).
      * pose proof (HSP k k0 s s0 Hk Hk0 Hne) as Ha. unfold apart, s_ubeg in *. rewrite <- Hn' in X1. lia.
  - apply Forall_forall. intros [f k] Hin'. cbn [fst snd]. destruct (sep_frame f k Hin') as (X & Y & _). unfold apart in Hf. lia.
Qed.

(* [comment removed for export] *)
Lemma ac_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 ->
  (forall f k, In (f, k) (frames Σ) -> a + n <= f \/ f + fs_size k - 8 <= a) -> disjoint_from W a n.
Proof.
  intros a n H1 H2 HF. pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  apply avoid_client_intro; [apply sep_stack; lia | apply dsj_CS_out; unfold SEGTOP_A in *; lia | | | apply sep_fshad_app; lia].
  - apply Forall_forall. intros [p n'] Hin'. cbn [fst snd].
    destruct (geo_live Σ m HA p n' Hin') as [(c & i & Hc & _ & _ & X1 & X2 & X3 & X4 & X5)|(s & Hs & _ & Hn' & -> & X1 & X5)].
    + pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha.
      cbn [fst snd] in Ha. unfold rb, apart, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
    + pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
      pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (_ & _ & _ & Ha & _). unfold apart, s_ubeg in *. rewrite <- Hn' in X1. lia.
  - apply Forall_forall. intros [f k] Hin'. cbn [fst snd]. exact (HF f k Hin').
Qed.

End Sep.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Comp.
Variables (Σ : rtsA) (m : mem) (W : list ivl).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).
(* [comment removed for export] *)
Hypothesis R_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from CS_W a n -> disjoint_from W a n.
Hypothesis R_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Hypothesis R_shad : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
  (forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) ->
  (hi <= l_FSB L \/ l_FSB L + 0xb09000 <= lo) -> disjoint_from W a n.
Hypothesis R_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 ->
  (forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
     a + n <= p_ubeg SB c i n' \/ p_ubeg SB c i n' + n' <= a) -> disjoint_from W a n.
Hypothesis R_secmap : forall k0 s0 a n, nth_error (sec Σ) k0 = Some s0 -> s_mb s0 <= a -> a + n <= s_mb s0 + smsz (s_n s0) ->
  (s_quar s0 = false -> a + n <= s_ubeg s0 \/ s_ubeg s0 + s_n s0 <= a) -> disjoint_from W a n.

(* [comment removed for export] *)
Lemma slot_geo : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  rb SB c <= p_abeg SB c i /\ p_abeg SB c i + ClassSize c <= rb SB c + r_muser (pr Σ c) /\ r_muser (pr Σ c) <= kUserCap
  /\ 32 <= ClassSize c /\ ClassSize c mod 32 = 0.
Proof.
  intros c i st Hc Hn. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & _ & W3 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm).
  pose proof (proj1 (nth_error_Some (r_st (pr Σ c)) i) ltac:(rewrite Hn; discriminate)) as Hlt.
  unfold p_abeg, rb in *.
  assert (Hx : Z.of_nat i * ClassSize c + ClassSize c <= ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
  { replace (ClassSize c * Z.of_nat (length (r_st (pr Σ c)))) with (Z.of_nat (length (r_st (pr Σ c))) * ClassSize c) by ring.
    replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring.
    apply Z.mul_le_mono_nonneg_r; lia. }
  assert (0 <= Z.of_nat i * ClassSize c) by (apply Z.mul_nonneg_nonneg; lia). repeat split; lia.
Qed.

Lemma slot_apart : forall c i c' i' st st', 1 <= c <= 31 -> 1 <= c' <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  nth_error (r_st (pr Σ c')) i' = Some st' -> (c <> c' \/ i <> i') ->
  p_abeg SB c i + ClassSize c <= p_abeg SB c' i' \/ p_abeg SB c' i' + ClassSize c' <= p_abeg SB c i.
Proof.
  intros c i c' i' st st' Hc Hc' Hn Hn' Hne.
  pose proof (slot_geo c i st Hc Hn) as (A1 & A2 & A3 & _). pose proof (slot_geo c' i' st' Hc' Hn') as (B1 & B2 & B3 & _).
  destruct (Z.eq_dec c c') as [<-|Hcc].
  - destruct Hne as [Hne|Hne]; [lia|]. unfold p_abeg. pose proof (ClassSize_range c Hc) as (Hcs & _).
    destruct (Nat.lt_ge_cases i i') as [Hl|Hl].
    + left. assert (Z.of_nat i * ClassSize c + ClassSize c <= Z.of_nat i' * ClassSize c).
      { replace (Z.of_nat i * ClassSize c + ClassSize c) with ((Z.of_nat i + 1) * ClassSize c) by ring. apply Z.mul_le_mono_nonneg_r; lia. }
      lia.
    + right. assert (Z.of_nat i' * ClassSize c + ClassSize c <= Z.of_nat i * ClassSize c).
      { replace (Z.of_nat i' * ClassSize c + ClassSize c) with ((Z.of_nat i' + 1) * ClassSize c) by ring. apply Z.mul_le_mono_nonneg_r; lia. }
      lia.
  - unfold rb, kUserCap in *. lia.
Qed.

(* [comment removed for export] *)
Lemma live_in_slot : forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
  p_abeg SB c i + rz_size n' = p_ubeg SB c i n' /\ 16 <= rz_size n' /\ rz_size n' + n' <= ClassSize c /\ 0 <= n'.
Proof.
  intros c i n' Hc Hn. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
  pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as (Hn0 & Hfit & _). cbv beta iota in Hn0, Hfit.
  split; [reflexivity|]. split; [|lia].
  unfold rz_size. pose proof (Z.pow_pos_nonneg 2 (rz_log n') ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma ac_slot : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> p_abeg SB c i <= a ->
  a + n <= p_abeg SB c i + ClassSize c ->
  (forall n', st = CkAlloc n' -> a + n <= p_ubeg SB c i n') -> disjoint_from W a n.
Proof.
  intros c i st a n Hc Hn H1 H2 HU. pose proof (slot_geo c i st Hc Hn) as (S1 & S2 & S3 & _).
  pose proof (geo_prb Σ m HA) as (P1 & P2 & P3).
  apply R_prb; [unfold rb in *; lia | unfold rb, kUserCap in *; assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia; lia|].
  intros c' i' n' Hc' Hn'. destruct (Z.eq_dec c c') as [<-|Hne]; [destruct (Nat.eq_dec i i') as [<-|Hne]|].
  - rewrite Hn in Hn'. injection Hn' as ->. left. exact (HU n' eq_refl).
  - destruct (slot_apart c i c i' st (CkAlloc n') Hc Hc' Hn Hn' (or_intror Hne)) as [X|X];
      pose proof (live_in_slot c i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _); lia.
  - destruct (slot_apart c i c' i' st (CkAlloc n') Hc Hc' Hn Hn' (or_introl Hne)) as [X|X];
      pose proof (live_in_slot c' i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _); lia.
Qed.

(* [comment removed for export] *)
Fixpoint dsjb (V : list ivl) (a n : Z) : bool :=
  match V with [] => true | (lo, hi) :: V' => ((a + n <=? lo) || (hi <=? a)) && dsjb V' a n end.
Lemma dsjb_sound : forall V a n, dsjb V a n = true -> disjoint_from V a n.
Proof.
  induction V as [|[lo hi] V IH]; intros a n H; [exact I|]. cbn [dsjb] in H. apply andb_prop in H as [H1 H2].
  split; [|exact (IH _ _ H2)]. apply orb_prop in H1 as [X|X]; [left; apply Z.leb_le; exact X | right; apply Z.leb_le; exact X].
Qed.
Definition img_ok (r : Z * Z) : bool := ((0x10000 <=? fst r) && (fst r + snd r <=? SEGTOP_A) && dsjb CS_W (fst r) (snd r))%bool.
Lemma ac_lits : forall l, forallb img_ok l = true -> dsjl W l.
Proof.
  intros l H. apply Forall_forall. intros [a n] Hin. pose proof (proj1 (forallb_forall _ _) H _ Hin) as X. unfold img_ok in X.
  cbn [fst snd] in *. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1, X2.
  exact (R_img a n X1 X2 (dsjb_sound _ _ _ X3)).
Qed.

(* [comment removed for export] *)
Lemma ac_T : forall a n, l_T L <= a -> a + n <= l_T L + 4096 -> disjoint_from W a n.
Proof.
  intros a n H1 H2. apply (R_grant (l_T L) 4096); [unfold startup_grants; right; right; left; reflexivity | | | exact H1 | exact H2].
  - pose proof (geo_apart Σ m HA 0 2 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
  - pose proof (geo_apart Σ m HA 2 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_TCX : forall a n, l_TCX L <= a -> a + n <= l_TCX L + 0x10000 -> disjoint_from W a n.
Proof.
  intros a n H1 H2. apply (R_grant (l_TCX L) 0x10000); [unfold startup_grants; right; right; right; left; reflexivity | | | exact H1 | exact H2].
  - pose proof (geo_apart Σ m HA 0 3 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
  - pose proof (geo_apart Σ m HA 3 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_DTV : forall a n, l_DTV L <= a -> a + n <= l_DTV L + 4096 -> disjoint_from W a n.
Proof.
  intros a n H1 H2. apply (R_grant (l_DTV L) 4096); [unfold startup_grants; right; right; right; right; left; reflexivity | | | exact H1 | exact H2].
  - pose proof (geo_apart Σ m HA 0 4 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
  - pose proof (geo_apart Σ m HA 4 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_PAB : forall a n, l_PAB L <= a -> a + n <= l_PAB L + 0x800000 -> disjoint_from W a n.
Proof.
  intros a n H1 H2. apply (R_grant (l_PAB L) 0x800000); [unfold startup_grants; right; left; reflexivity | | | exact H1 | exact H2].
  - pose proof (geo_apart Σ m HA 0 1 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
  - pose proof (geo_apart Σ m HA 1 5 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. exact X.
Qed.
Lemma ac_DNB : forall a n, l_DNB L <= a -> a + n <= l_DNB L + 0x100000 -> disjoint_from W a n.
Proof.
  intros a n H1 H2. apply (R_grant (l_DNB L) 0x100000); [unfold startup_grants; do 6 right; left; reflexivity | | | exact H1 | exact H2].
  - pose proof (geo_apart Σ m HA 0 6 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
  - pose proof (geo_apart Σ m HA 5 6 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
Qed.
Lemma ac_SSB : forall a n, l_SSB L <= a -> a + n <= l_SSB L + 0x800000 -> disjoint_from W a n.
Proof.
  intros a n H1 H2. apply (R_grant (l_SSB L) 0x800000); [unfold startup_grants; do 7 right; left; reflexivity | | | exact H1 | exact H2].
  - pose proof (geo_apart Σ m HA 0 7 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
  - pose proof (geo_apart Σ m HA 5 7 _ _ ltac:(lia) eq_refl eq_refl) as X. cbn [fst snd] in X. unfold apart in *. lia.
Qed.

Lemma av_consts : consts_avoid W L.
Proof.
  unfold consts_avoid, consts_rngs. unfold_consts.
  repeat (apply Forall_cons; [cbn [fst snd];
    first [ apply R_img; [lia | unfold SEGTOP_A; lia | apply dsjb_sound; vm_compute; reflexivity] | apply ac_T; lia | apply ac_TCX; lia ] |]).
  apply Forall_nil.
Qed.

(* [comment removed for export] *)
Lemma av_reg : forall c, 1 <= c <= 31 -> reg_avoid W SB c (pr Σ c) /\ pclass_avoid W (l_T L) c.
Proof.
  intros c Hc. pose proof (geo_prb Σ m HA) as (P1 & P2 & P3). pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
  pose proof (HR c Hc) as (W1 & W2 & W3 & W4 & W5 & W6 & _). pose proof (ClassSize_range c Hc) as (Hcs & Hm32).
  split; [|unfold pclass_avoid, pc_addr, cacheT; apply ac_T; lia].
  unfold reg_avoid. split; [|split].
  - (* [comment removed for export] *) apply R_prb; [unfold rinfo, RIS_of; lia | unfold rinfo, RIS_of; lia|].
    intros c' i' n' Hc' Hn'. pose proof (slot_geo c' i' _ Hc' Hn') as (S1 & S2 & S3 & _).
    pose proof (live_in_slot c' i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _). right. unfold rinfo, RIS_of, rb, kUserCap in *.
    assert (c' * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
  - (* [comment removed for export] *) apply R_prb; [unfold fa, rb; lia | unfold fa, rb, kFaCap in *; assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia; lia|].
    intros c' i' n' Hc' Hn'. pose proof (slot_geo c' i' _ Hc' Hn') as (S1 & S2 & S3 & _).
    pose proof (live_in_slot c' i' n' Hc' Hn') as (Y1 & Y2 & Y3 & _). unfold fa, rb, kUserCap, kFaCap in *.
    destruct (Z.eq_dec c c') as [<-|Hne]; [right; lia|]. destruct (Z_lt_le_dec c c'); [left | right]; lia.
  - (* [comment removed for export] *)
    set (auser := ClassSize c * Z.of_nat (length (r_st (pr Σ c)))).
    assert (Hau : auser mod 8 = 0).
    { unfold auser. rewrite Z.mul_comm. apply Z.mod_divide; [lia|]. apply Z.divide_mul_r. apply Z.mod_divide in Hm32; [|lia].
      apply (Z.divide_trans 8 32); [exists 4; reflexivity | exact Hm32]. }
    assert (Hrb : rb SB c mod 8 = 0) by (unfold rb; apply Z.mod_divide; [lia|]; apply Z.divide_add_r;
      [apply Z.mod_divide in P3; [|lia]; apply (Z.divide_trans 8 (2 ^ 16)); [exists 8192; reflexivity | exact P3] | exists (c * 2 ^ 29); lia]).
    assert (Hmu : r_muser (pr Σ c) mod 8 = 0) by (unfold kUMap in W2; apply Z.mod_divide; [lia|]; apply Z.mod_divide in W2; [|lia];
      apply (Z.divide_trans 8 0x40000); [exists 0x8000; reflexivity | exact W2]).
    apply (R_shad (rb SB c + auser) (rb SB c + r_muser (pr Σ c))).
    + rewrite Z.add_mod by lia. rewrite Hrb, Hau. reflexivity.
    + rewrite Z.add_mod by lia. rewrite Hrb, Hmu. reflexivity.
    + pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _).
      unfold rb. assert (0 <= auser) by (unfold auser; apply Z.mul_nonneg_nonneg; lia). lia.
    + pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & G3 & _).
      pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold l_ACEIL, rtA_sp0, sp_window_hi, STACK_WIN, rb, kUserCap in *.
      assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
    + lia.
    + assert (shad (rb SB c + auser) + Z.max 0 ((r_muser (pr Σ c) - auser) / 8) = shad (rb SB c + r_muser (pr Σ c))); [|lia].
      unfold shad. rewrite Z.max_r by (apply Z.div_pos; lia).
      replace (rb SB c + r_muser (pr Σ c)) with ((rb SB c + auser) + (r_muser (pr Σ c) - auser)) by lia.
      assert (E1 : (rb SB c + auser) mod 8 = 0) by (rewrite Z.add_mod by lia; rewrite Hrb, Hau; reflexivity).
      assert (E2 : (r_muser (pr Σ c) - auser) mod 8 = 0) by (rewrite Zminus_mod, Hmu, Hau; reflexivity).
      apply Z.mod_divide in E1, E2; try (clear; lia). destruct E1 as [q1 E1]. destruct E2 as [q2 E2]. rewrite E1, E2.
      replace (q1 * 8 + q2 * 8) with ((q1 + q2) * 8) by ring. rewrite !Z.div_mul by lia. lia.
    + intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X & Y & _).
      pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
      assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
    + pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
      assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
Qed.

Lemma mod8_of : forall z k, 0 < k -> z mod k = 0 -> (8 | k) -> z mod 8 = 0.
Proof. intros z k Hk H D. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia]. exact (Z.divide_trans _ _ _ D H). Qed.

Lemma abeg_mod8 : forall c i, 1 <= c <= 31 -> p_abeg SB c i mod 8 = 0.
Proof.
  intros c i Hc. pose proof (geo_prb Σ m HA) as (_ & _ & P3). pose proof (ClassSize_range c Hc) as (_ & Hm).
  unfold p_abeg. apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.divide_add_r|].
  - apply Z.mod_divide in P3; [|lia]. apply (Z.divide_trans 8 (2 ^ 16)); [exists 8192; reflexivity | exact P3].
  - exists (c * 2 ^ 29). lia.
  - apply Z.divide_mul_r. apply Z.mod_divide in Hm; [|lia]. apply (Z.divide_trans 8 32); [exists 4; reflexivity | exact Hm].
Qed.

(* [comment removed for export] *)
Lemma ac_slot_shad : forall c i st a n, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st ->
  shad (p_abeg SB c i) <= a -> a + n <= shad (p_abeg SB c i) + ClassSize c / 8 -> disjoint_from W a n.
Proof.
  intros c i st a n Hc Hn H1 H2. pose proof (slot_geo c i st Hc Hn) as (S1 & S2 & S3 & S4 & S5).
  pose proof (abeg_mod8 c i Hc) as M1. pose proof (geo_prb Σ m HA) as (P1 & P2 & P3).
  pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & _ & G3 & _).
  assert (M2 : ClassSize c mod 8 = 0) by (apply (mod8_of _ 32 ltac:(lia) S5); exists 4; reflexivity).
  assert (E : shad (p_abeg SB c i + ClassSize c) = shad (p_abeg SB c i) + ClassSize c / 8).
  { unfold shad. apply Z.mod_divide in M1, M2; try (clear; lia). destruct M1 as [q1 E1]. destruct M2 as [q2 E2].
    rewrite E1, E2. replace (q1 * 8 + q2 * 8) with ((q1 + q2) * 8) by ring. rewrite !Z.div_mul by lia. lia. }
  apply (R_shad (p_abeg SB c i) (p_abeg SB c i + ClassSize c)); [exact M1 | rewrite Z.add_mod, M1, M2 by lia; reflexivity | | | exact H1 | rewrite E; exact H2 | |].
  - unfold rb in S1. lia.
  - pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold l_ACEIL, rtA_sp0, sp_window_hi, STACK_WIN, rb, kUserCap in *.
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
  - intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X & Y & _).
    pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
  - pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha. cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *.
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
Qed.

Lemma rz_facts : forall n, rz_size n mod 16 = 0 /\ 16 <= rz_size n.
Proof.
  intros n. unfold rz_size. pose proof (Z.pow_pos_nonneg 2 (rz_log n) ltac:(lia) ltac:(unfold rz_log; repeat destruct (_ <=? _); lia)).
  split; [rewrite Z.mul_comm; apply Z.mod_mul; lia | lia].
Qed.

(* [comment removed for export] *)
Lemma slot_room : forall c n, 1 <= c <= 31 -> 0 <= n -> rz_size n + n <= ClassSize c ->
  rz_size n + ru8 n <= ClassSize c /\ rz_size n + 16 <= ClassSize c.
Proof.
  intros c n Hc Hn H. pose proof (ClassSize_range c Hc) as (Hcs & Hm). pose proof (rz_facts n) as (R1 & R2).
  assert (Hd : exists k, ClassSize c - rz_size n = 16 * k).
  { exists ((ClassSize c - rz_size n) / 16). pose proof (Z.div_mod (ClassSize c - rz_size n) 16 ltac:(lia)) as D.
    assert ((ClassSize c - rz_size n) mod 16 = 0); [|lia]. rewrite Zminus_mod. rewrite R1.
    replace (ClassSize c mod 16) with 0; [reflexivity|]. symmetry. (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hm; [|lia]; apply (Z.divide_trans 16 32); [exists 2; reflexivity | exact Hm]). }
  destruct Hd as [k Hk]. unfold ru8. split.
  - assert (8 * ((n + 7) / 8) <= 16 * k); [|lia]. assert ((n + 7) / 8 < 2 * k + 1); [|lia]. apply Z.div_lt_upper_bound; lia.
  - destruct (Z_le_dec n 0) as [Hz|Hz].
    + assert (n = 0) by lia. subst n. unfold rz_size, rz_log in *. cbn in *. lia.
    + lia.
Qed.

Lemma ushadow_len : forall n, 0 <= n -> Z.of_nat (length (ushadow n)) = ru8 n / 8.
Proof.
  intros n Hn. unfold ushadow, ru8. rewrite length_app, repeat_length. replace (8 * ((n + 7) / 8) / 8) with ((n + 7) / 8) by (rewrite Z.mul_comm, Z.div_mul; lia).
  destruct (Z.eqb_spec (n mod 8) 0) as [E|E]; cbn [length].
  - pose proof (Z.div_mod n 8 ltac:(lia)) as D. rewrite E in D. rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; lia).
    replace (n + 7) with ((n / 8) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia.
  - pose proof (Z.div_mod n 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as B.
    rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia). cbn [Z.of_nat Pos.of_succ_nat].
    replace (n + 7) with ((n / 8 + 1) * 8 + (n mod 8 - 1)) by lia. rewrite Z.div_add_l by lia. rewrite (Z.div_small (n mod 8 - 1) 8) by lia. lia.
Qed.

Lemma av_pchunk : forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some st -> pchunk_avoid W SB c i st.
Proof.
  intros c i st Hc Hn. unfold pchunk_avoid. pose proof (slot_geo c i st Hc Hn) as (S1 & S2 & S3 & S4 & S5).
  assert (Hfit : forall n, st = CkAlloc n \/ st = CkQuar n -> rz_size n + n <= ClassSize c /\ 0 <= n).
  { intros n Hs. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
    pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. destruct Hs as [->| ->]; cbv beta iota in X; lia. }
  pose proof (abeg_mod8 c i Hc) as M1. apply Z.mod_divide in M1; [|lia]. destruct M1 as [a0 E1].
  apply Z.mod_divide in S5; [|lia]. destruct S5 as [s1 E4].
  assert (ES : ClassSize c / 8 = 4 * s1) by (rewrite E4; replace (s1 * 32) with ((4 * s1) * 8) by ring; apply Z.div_mul; lia).
  assert (EA : shad (p_abeg SB c i) = a0 + SHB) by (unfold shad; rewrite E1, Z.div_mul by lia; reflexivity).
  destruct st as [|n|n|].
  - apply (ac_slot_shad c i CkIdle); [exact Hc | exact Hn | lia | lia].
  - destruct (Hfit n (or_introl eq_refl)) as (F1 & F2). destruct (slot_room c n Hc F2 F1) as (R1 & R2). pose proof (rz_facts n) as (R3 & R4).
    pose proof (ushadow_len n F2) as U. rewrite length_app, Nat2Z.inj_add, farun_len, U.
    apply Z.mod_divide in R3; [|lia]. destruct R3 as [r1 E2]. set (u0 := (n + 7) / 8). assert (E3 : ru8 n = u0 * 8) by (unfold ru8, u0; ring).
    assert (ER : rz_size n / 8 = 2 * r1) by (rewrite E2; replace (r1 * 16) with ((2 * r1) * 8) by ring; apply Z.div_mul; lia).
    assert (EU : ru8 n / 8 = u0) by (rewrite E3; apply Z.div_mul; lia).
    split; [apply (ac_slot c i (CkAlloc n)); [exact Hc | exact Hn | lia | lia | intros n' E; injection E as <-; unfold p_ubeg; lia]|].
    split; [intros Hr; apply (ac_slot c i (CkAlloc n)); [exact Hc | exact Hn | lia | lia | intros n' E; injection E as <-; unfold p_ubeg; lia]|].
    split; [apply (ac_slot_shad c i (CkAlloc n)); [exact Hc | exact Hn | lia | rewrite ER, EU, ES, EA; lia]|].
    assert (EB : shad (p_abeg SB c i + rz_size n + ru8 n) = a0 + 2 * r1 + u0 + SHB).
    { unfold shad. rewrite E1, E2, E3. replace (a0 * 8 + r1 * 16 + u0 * 8) with ((a0 + 2 * r1 + u0) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
    assert (EC : (ClassSize c - rz_size n - ru8 n) / 8 = 4 * s1 - 2 * r1 - u0).
    { rewrite E4, E2, E3. replace (s1 * 32 - r1 * 16 - u0 * 8) with ((4 * s1 - 2 * r1 - u0) * 8) by ring. apply Z.div_mul. lia. }
    apply (ac_slot_shad c i (CkAlloc n)); [exact Hc | exact Hn | rewrite EB, EA; lia | rewrite EB, EC, ES, EA; lia].
  - destruct (Hfit n (or_intror eq_refl)) as (F1 & F2). destruct (slot_room c n Hc F2 F1) as (R1 & R2). pose proof (rz_facts n) as (R3 & R4).
    rewrite !length_app, !Nat2Z.inj_add, !farun_len, fdrun_len.
    apply Z.mod_divide in R3; [|lia]. destruct R3 as [r1 E2]. set (u0 := (n + 7) / 8). assert (E3 : ru8 n = u0 * 8) by (unfold ru8, u0; ring).
    assert (ER : rz_size n / 8 = 2 * r1) by (rewrite E2; replace (r1 * 16) with ((2 * r1) * 8) by ring; apply Z.div_mul; lia).
    assert (EU : ru8 n / 8 = u0) by (rewrite E3; apply Z.div_mul; lia).
    assert (EC : (ClassSize c - rz_size n - ru8 n) / 8 = 4 * s1 - 2 * r1 - u0).
    { rewrite E4, E2, E3. replace (s1 * 32 - r1 * 16 - u0 * 8) with ((4 * s1 - 2 * r1 - u0) * 8) by ring. apply Z.div_mul. lia. }
    split; [apply (ac_slot c i (CkQuar n)); [exact Hc | exact Hn | lia | lia | intros n' E; discriminate E]|].
    split; [intros Hr; apply (ac_slot c i (CkQuar n)); [exact Hc | exact Hn | lia | lia | intros n' E; discriminate E]|].
    apply (ac_slot_shad c i (CkQuar n)); [exact Hc | exact Hn | lia | rewrite ER, EU, EC, ES, EA; lia].
  - apply (ac_slot_shad c i CkBatch); [exact Hc | exact Hn | lia | lia].
Qed.

(* [comment removed for export] *)
Lemma map_geo : forall k s, nth_error (sec Σ) k = Some s ->
  64513 <= s_n s <= 0x8000000 /\ grant_ok L (s_mb s) (smsz (s_n s)) /\ apart (s_mb s) (smsz (s_n s)) (l_FSB L) 0xb09000
  /\ smsz (s_n s) mod 4096 = 0 /\ 6144 + ru8 (s_n s) <= smsz (s_n s).
Proof.
  intros k s Hk. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
  pose proof (proj1 (Forall_forall _ _) HSF s (nth_error_In _ _ Hk)) as (Hn & G & _ & Hf & _).
  split; [exact Hn|]. split; [exact G|]. split; [exact Hf|]. split.
  - unfold smsz, pg_up. rewrite Z.add_mod by lia. rewrite Z.mod_mul by lia. reflexivity.
  - unfold smsz, pg_up, needed, rounded, ru8. rewrite (rz_size_big (s_n s)) by lia. rewrite Z.max_l by lia. rewrite Z.max_l by lia.
    assert (8 * ((s_n s + 7) / 8) + 2048 + 2048 <= (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) / 4096 * 4096); [|lia].
    pose proof (Z.mod_pos_bound (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)).
    pose proof (Z.div_mod (8 * ((s_n s + 7) / 8) + 2048 + 2048 + 4095) 4096 ltac:(lia)). lia.
Qed.

Lemma ac_map_shad : forall k s a n, nth_error (sec Σ) k = Some s ->
  shad (s_mb s) <= a -> a + n <= shad (s_mb s) + smsz (s_n s) / 8 -> disjoint_from W a n.
Proof.
  intros k s a n Hk H1 H2. destruct (map_geo k s Hk) as (Hn & (G1 & G2 & G3 & G4 & G5) & Hf & M2 & _).
  assert (M1 : s_mb s mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) G2); exists 512; reflexivity).
  assert (M3 : smsz (s_n s) mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) M2); exists 512; reflexivity).
  assert (E : shad (s_mb s + smsz (s_n s)) = shad (s_mb s) + smsz (s_n s) / 8).
  { unfold shad. apply Z.mod_divide in M1, M3; try (clear; lia). destruct M1 as [q1 E1]. destruct M3 as [q2 E2].
    rewrite E1, E2. replace (q1 * 8 + q2 * 8) with ((q1 + q2) * 8) by ring. rewrite !Z.div_mul by lia. lia. }
  apply (R_shad (s_mb s) (s_mb s + smsz (s_n s))); [exact M1 | rewrite Z.add_mod, M1, M3 by lia; reflexivity | lia | | exact H1 | rewrite E; exact H2 | |].
  - pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold l_ACEIL, rtA_sp0, sp_window_hi, STACK_WIN in *. lia.
  - intros f k' Hin. destruct (sep_frame Σ m HA f k' Hin) as (X & Y & _). unfold apart in Hf. lia.
  - unfold apart in Hf. lia.
Qed.

Lemma av_schunk : forall k s, nth_error (sec Σ) k = Some s -> schunk_avoid W s.
Proof.
  intros k s Hk. unfold schunk_avoid. destruct (map_geo k s Hk) as (Hn & (G1 & G2 & G3 & G4 & G5) & Hf & M2 & Hroom).
  assert (M1 : s_mb s mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) G2); exists 512; reflexivity).
  apply Z.mod_divide in M1; [|lia]. destruct M1 as [a0 E1]. apply Z.mod_divide in M2; [|lia]. destruct M2 as [q E2].
  set (u0 := (s_n s + 7) / 8). assert (E3 : ru8 (s_n s) = u0 * 8) by (unfold ru8, u0; ring).
  assert (Hu0 : 0 <= u0) by (apply Z.div_pos; lia).
  assert (EA : shad (s_mb s) = a0 + SHB) by (unfold shad; rewrite E1, Z.div_mul by lia; reflexivity).
  assert (EM : smsz (s_n s) / 8 = 512 * q) by (rewrite E2; replace (q * 4096) with ((512 * q) * 8) by ring; apply Z.div_mul; lia).
  assert (EU : ru8 (s_n s) / 8 = u0) by (rewrite E3; apply Z.div_mul; lia).
  assert (Eb : shad (s_mb s + 4096 + 2048) = a0 + 768 + SHB).
  { unfold shad. rewrite E1. replace (a0 * 8 + 4096 + 2048) with ((a0 + 768) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
  assert (Ec : shad (s_mb s + 4096 + 2048 + ru8 (s_n s)) = a0 + 768 + u0 + SHB).
  { unfold shad. rewrite E1, E3. replace (a0 * 8 + 4096 + 2048 + u0 * 8) with ((a0 + 768 + u0) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
  assert (Ed : (smsz (s_n s) - 4096 - 2048 - ru8 (s_n s)) / 8 = 512 * q - 768 - u0).
  { rewrite E2, E3. replace (q * 4096 - 4096 - 2048 - u0 * 8) with ((512 * q - 768 - u0) * 8) by ring. apply Z.div_mul. lia. }
  unfold s_ubeg in *.
  split; [apply (R_secmap k s); [exact Hk | lia | lia | intros _; unfold s_ubeg; lia]|].
  split; [apply (R_secmap k s); [exact Hk | lia | lia | intros _; unfold s_ubeg; lia]|].
  split; [apply (R_secmap k s); [exact Hk | lia | destruct (s_quar s); lia | intros Hq; rewrite Hq; unfold s_ubeg; lia]|].
  split; [apply (ac_map_shad k s); [exact Hk | lia | rewrite EM, EA; change ((4096 + 2048) / 8) with 768; lia]|].
  split; [apply (ac_map_shad k s); [exact Hk | rewrite Eb, EA; lia |]|].
  - destruct (s_quar s); [rewrite fdrun_len, EU | rewrite (ushadow_len (s_n s) ltac:(lia)), EU]; rewrite Eb, EM, EA; lia.
  - apply (ac_map_shad k s); [exact Hk | rewrite Ec, EA; lia | rewrite Ec, Ed, EM, EA; lia].
Qed.

Lemma av_sec : sec_avoid W Σ.
Proof.
  split; [apply ac_lits; vm_compute; reflexivity|]. pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & Hn & _).
  apply ac_PAB; lia.
Qed.

Lemma av_quar : quar_avoid W Σ.
Proof.
  split; [unfold qcacheT; apply ac_T; lia|]. split; [apply ac_lits; vm_compute; reflexivity|].
  pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & HQ & _). destruct HQ as (_ & _ & HB & _).
  apply Forall_forall. intros b Hb. destruct (proj1 (Forall_forall _ _) HB b Hb) as (i & Hi & ->).
  apply (ac_slot 24 i CkBatch); [lia | exact Hi | lia | change (ClassSize 24) with 8192; lia | intros n' E; discriminate E].
Qed.

Lemma av_dep : dep_avoid W L.
Proof. split; [apply ac_lits; vm_compute; reflexivity|]. split; [apply ac_DNB | apply ac_SSB]; lia. Qed.

Lemma av_ia : dsjl W ia_lits.
Proof. apply ac_lits. vm_compute. reflexivity. Qed.

Lemma av_static_shad : Forall (fun r => disjoint_from W (shad (fst r)) (shad (snd r - 1) + 1 - shad (fst r))) CS_AV.
Proof.
  apply Forall_forall. intros r Hr.
  assert (Hlh : 0x10000 <= fst r /\ fst r < snd r /\ snd r <= 0xbc6000) by (unfold CS_AV, CS_ACC, CS_SHX in Hr; cbn [app] in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & _ & _ & G5).
  apply (R_shad 0x10000 SEGTOP_A); [reflexivity | reflexivity | lia | unfold SEGTOP_A; lia | | | |].
  - unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia.
  - unfold shad, SEGTOP_A. assert ((snd r - 1) / 8 < 0x178c00) by (apply Z.div_lt_upper_bound; lia). change (0xbc6000 / 8) with 0x178c00. lia.
  - intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X & Y & _). unfold SEGTOP_A in *. lia.
  - unfold SEGTOP_A in *. lia.
Qed.

Lemma av_shadow : shadow_avoid W L.
Proof.
  unfold shadow_avoid. split; [|exact av_static_shad]. pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & X3). unfold rtA_sp0 in *.
  assert (M1 : l_ACEIL L mod 8 = 0) by (unfold l_ACEIL, STACK_WIN; apply (mod8_of _ 16 ltac:(lia)); [rewrite Zminus_mod, X3; reflexivity | exists 2; reflexivity]).
  apply Z.mod_divide in M1; [|lia]. destruct M1 as [a0 E1].
  apply (R_shad (l_ACEIL L) (2 ^ 47)); [rewrite E1; apply Z.mod_mul; lia | reflexivity | unfold l_ACEIL, STACK_WIN, sp_window_lo in *; lia | lia | lia | | |].
  - unfold shad. rewrite E1, Z.div_mul by lia. rewrite Z.max_r by (apply Z.div_pos; unfold l_ACEIL, STACK_WIN, sp_window_hi in *; lia).
    replace (2 ^ 47 - a0 * 8) with ((2 ^ 44 - a0) * 8) by ring. rewrite Z.div_mul by lia. change (2 ^ 47 / 8) with (2 ^ 44). lia.
  - intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X & Y & _).
    pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & G3 & _).
    right. lia.
  - pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & G3 & _).
    right. lia.
Qed.

(* [comment removed for export] *)
Definition art_avoid_but_fs (W' : list ivl) (Σ' : rtsA) : Prop :=
  consts_avoid W' (lay Σ')
  /\ (forall c, 1 <= c <= 31 -> reg_avoid W' (l_SB (lay Σ')) c (pr Σ' c) /\ pclass_avoid W' (l_T (lay Σ')) c)
  /\ (forall c i st, 1 <= c <= 31 -> nth_error (r_st (pr Σ' c)) i = Some st -> pchunk_avoid W' (l_SB (lay Σ')) c i st)
  /\ (forall k s, nth_error (sec Σ') k = Some s -> schunk_avoid W' s)
  /\ sec_avoid W' Σ' /\ quar_avoid W' Σ' /\ dep_avoid W' (lay Σ') /\ dsjl W' ia_lits /\ shadow_avoid W' (lay Σ').

Theorem art_avoid_gen : art_avoid_but_fs W Σ.
Proof.
  split; [exact av_consts|]. split; [exact av_reg|]. split; [exact av_pchunk|]. split; [exact av_schunk|].
  split; [exact av_sec|]. split; [exact av_quar|]. split; [exact av_dep|]. split; [exact av_ia | exact av_shadow].
Qed.

End Comp.

Section CompFs.
Variables (Σ : rtsA) (m : mem) (W : list ivl).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).
Hypothesis R_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from CS_W a n -> disjoint_from W a n.
Hypothesis R_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
  b <= a -> a + n <= b + gn -> disjoint_from W a n.
Hypothesis R_shad : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
  (forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) -> disjoint_from W a n.
Hypothesis R_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 ->
  (forall f k, In (f, k) (frames Σ) -> a + n <= f \/ f + fs_size k - 8 <= a) -> disjoint_from W a n.

#[local] Notation ac_T := (ac_T Σ m W HA R_grant).
#[local] Notation ac_DTV := (ac_DTV Σ m W HA R_grant).
#[local] Notation ac_lits := (ac_lits W R_img).

(* [comment removed for export] *)
Lemma frame_apart : forall FSB c p c' p', (c = 0 \/ c = 2 \/ c = 1) -> (c' = 0 \/ c' = 2 \/ c' = 1) -> 0 <= p < NF c -> 0 <= p' < NF c' ->
  (c <> c' \/ p <> p') -> frame_addr FSB c p + fsz c <= frame_addr FSB c' p' \/ frame_addr FSB c' p' + fsz c' <= frame_addr FSB c p.
Proof.
  intros FSB c p c' p' Hc Hc' Hp Hp' Hne. unfold frame_addr, NF, fsz in *.
  destruct Hc as [ -> | [ -> | -> ] ]; destruct Hc' as [ -> | [ -> | -> ] ]; cbn in *; lia.
Qed.

Lemma fs_size_fsz : forall k, fs_size k = fsz (Z.of_nat k).
Proof. intros k. unfold fs_size, fsz. rewrite Z.shiftl_mul_pow2 by lia. ring. Qed.

Lemma nth_indep_Z : forall (l : list Z) n d d', (n < length l)%nat -> nth n l d = nth n l d'.
Proof. intros l n d d' H. apply nth_indep. exact H. Qed.

Lemma av_fs_cls : forall k, (k = 0 \/ k = 2 \/ k = 1)%nat -> fs_cls_avoid W (l_FSB L) (Z.of_nat k) (fs_of Σ k).
Proof.
  intros k Hk. pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & _ & HF & _). destruct HF as (F0 & F2 & F4 & HFr & _).
  assert (Hwf : flags_ok (Z.of_nat k) (fss_flags (fs_of Σ k))) by (destruct Hk as [ -> | [ -> | -> ] ]; [exact (proj1 F0) | exact (proj1 F2) | exact (proj1 F4)]).
  destruct Hwf as [Hlen _].
  assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 2 \/ Z.of_nat k = 1) by (destruct Hk as [ -> | [ -> | -> ] ]; cbn; lia).
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  assert (HFB : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0x9000 -> disjoint_from W a n).
  { intros a n H1 H2. apply R_fsb; [lia | lia|]. intros f k' Hin. destruct (sep_frame Σ m HA f k' Hin) as (X & _). left. lia. }
  unfold fs_cls_avoid. split; [apply HFB; destruct Hc as [ -> | [ -> | -> ] ]; lia|]. split.
  - apply HFB; [unfold fl_base, flags_off; destruct Hc as [ -> | [ -> | -> ] ]; cbn; lia|].
    rewrite Hlen. unfold fl_base, flags_off, NF. destruct Hc as [ -> | [ -> | -> ] ]; cbn; lia.
  - intros p Hp Hfl.
    (* [comment removed for export] *)
    assert (Hap : forall f k', In (f, k') (frames Σ) ->
              frame_addr (l_FSB L) (Z.of_nat k) p + fsz (Z.of_nat k) <= f \/ f + fs_size k' <= frame_addr (l_FSB L) (Z.of_nat k) p).
    { intros f k' Hin. destruct (proj1 (Forall_forall _ _) HFr (f, k') Hin) as (Hk' & p' & Hp' & Hf & Hb). cbn [fst snd] in *.
      rewrite fs_size_fsz, Hf.
      assert (Hne : Z.of_nat k <> Z.of_nat k' \/ p <> p').
      { destruct (Z.eq_dec (Z.of_nat k) (Z.of_nat k')) as [E|E]; [right|left; exact E]. intros ->. apply Nat2Z.inj in E. subst k'.
        rewrite (nth_indep_Z _ _ 0 1) in Hb by (apply Nat2Z.inj_lt; rewrite Hlen, Z2Nat.id by lia; lia). congruence. }
      assert (Hc' : Z.of_nat k' = 0 \/ Z.of_nat k' = 2 \/ Z.of_nat k' = 1) by (destruct Hk' as [ -> | [ -> | -> ] ]; cbn; lia).
      exact (frame_apart _ _ _ _ _ Hc Hc' Hp Hp' Hne). }
    pose proof (frame_addr_range (l_FSB L) (Z.of_nat k) p Hc Hp) as (R1 & R2). unfold kFakeStackSize in R2.
    split.
    + apply R_fsb; [lia | lia|]. intros f k' Hin. destruct (Hap f k' Hin) as [X|X]; [left; exact X | right; lia].
    + assert (M1 : frame_addr (l_FSB L) (Z.of_nat k) p mod 8 = 0).
      { unfold frame_addr, fsz. apply (mod8_of _ 64 ltac:(lia)); [|exists 8; reflexivity].
        apply Z.mod_divide in G2; [|lia]. apply Z.mod_divide; [lia|]. destruct G2 as [q Hq]. rewrite Hq.
        destruct Hc as [E|[E|E]]; rewrite E; cbn; [exists (q * 64 + 576 + p) | exists (q * 64 + 576 + 2 * 2 ^ 14 + 4 * p) | exists (q * 64 + 576 + 1 * 2 ^ 14 + 2 * p)]; lia. }
      assert (M2 : fsz (Z.of_nat k) mod 8 = 0) by (unfold fsz; destruct Hc as [ -> | [ -> | -> ] ]; reflexivity).
      apply Z.mod_divide in M1; [|lia]. destruct M1 as [a0 E1]. apply Z.mod_divide in M2; [|lia]. destruct M2 as [b0 E2].
      apply (R_shad (frame_addr (l_FSB L) (Z.of_nat k) p) (frame_addr (l_FSB L) (Z.of_nat k) p + fsz (Z.of_nat k)));
        [rewrite E1; apply Z.mod_mul; lia | rewrite E1, E2, <- Z.mul_add_distr_r; apply Z.mod_mul; lia | lia | | lia | | exact Hap].
      * pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & _). unfold l_ACEIL, rtA_sp0, sp_window_hi, STACK_WIN in *. lia.
      * unfold shad. rewrite E1, E2, <- Z.mul_add_distr_r, !Z.div_mul by lia. lia.
Qed.

Lemma av_fs : fs_avoid W Σ.
Proof.
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & _).
  unfold fs_avoid. split.
  { apply R_fsb; [lia | lia|]. intros f k' Hin. destruct (sep_frame Σ m HA f k' Hin) as (X & _). left. lia. }
  split; [exact (av_fs_cls 0%nat ltac:(lia))|]. split; [exact (av_fs_cls 2%nat ltac:(lia))|]. split; [exact (av_fs_cls 1%nat ltac:(lia))|].
  split; [apply ac_lits; vm_compute; reflexivity|]. split; [apply ac_DTV; lia|]. split; [apply ac_T; lia|].
  (* [comment removed for export] *)
  pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & _ & HF & _). destruct HF as (_ & _ & _ & HFr & HND & _).
  apply Forall_forall. intros [f k] Hin. cbn [fst snd].
  destruct (proj1 (Forall_forall _ _) HFr (f, k) Hin) as (Hk & p & Hp & Hf & _). cbn [fst snd] in *.
  assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 2 \/ Z.of_nat k = 1) by (destruct Hk as [ -> | [ -> | -> ] ]; cbn; lia).
  pose proof (frame_addr_range (l_FSB L) (Z.of_nat k) p Hc Hp) as (R1 & R2). unfold kFakeStackSize in R2. rewrite fs_size_fsz, Hf.
  assert (Hfz : 8 <= fsz (Z.of_nat k)) by (unfold fsz; destruct Hc as [ -> | [ -> | -> ] ]; cbn; lia).
  apply R_fsb; [lia | lia|]. intros f' k' Hin'.
  destruct (proj1 (Forall_forall _ _) HFr (f', k') Hin') as (Hk' & p' & Hp' & Hf' & _). cbn [fst snd] in *.
  assert (Hc' : Z.of_nat k' = 0 \/ Z.of_nat k' = 2 \/ Z.of_nat k' = 1) by (destruct Hk' as [ -> | [ -> | -> ] ]; cbn; lia).
  rewrite fs_size_fsz, Hf'.
  destruct (Z.eq_dec (Z.of_nat k) (Z.of_nat k')) as [Ek|Ek]; [destruct (Z.eq_dec p p') as [Ep|Ep]|].
  - right. rewrite <- Ek, <- Ep. lia.
  - destruct (frame_apart (l_FSB L) _ _ _ _ Hc Hc' Hp Hp' (or_intror Ep)) as [X|X]; [left | right]; rewrite <- Ek in *; lia.
  - destruct (frame_apart (l_FSB L) _ _ _ _ Hc Hc' Hp Hp' (or_introl Ek)) as [X|X]; [left | right]; lia.
Qed.

End CompFs.

(* [comment removed for export] *)
Theorem art_avoid_client : forall Σ m sp, ART_A Σ m -> rtA_sp0 Σ - STACK_WIN <= sp -> art_avoid (W_client Σ sp) Σ.
Proof.
  intros Σ m sp HA Hsp.
  destruct (art_avoid_gen Σ m (W_client Σ sp) HA (ac_img Σ m sp HA Hsp) (ac_grant Σ m sp HA Hsp)
              (fun lo hi a n H1 H2 H3 H4 H5 H6 H7 _ => ac_shad Σ m sp HA Hsp lo hi a n H1 H2 H3 H4 H5 H6 H7)
              (ac_prb Σ m sp HA Hsp) (ac_secmap Σ m sp HA Hsp)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  pose proof (av_fs Σ m (W_client Σ sp) HA (ac_img Σ m sp HA Hsp) (ac_grant Σ m sp HA Hsp) (ac_shad Σ m sp HA Hsp) (ac_fsb Σ m sp HA Hsp)) as A10.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
  split; [exact A7|]. split; [exact A10|]. split; [exact A8 | exact A9].
Qed.


(* [comment removed for export] *)
Theorem ART_client_frame : forall Σ (m m' : mem) (sp : Z), ART_A Σ m -> rtA_sp0 Σ - STACK_WIN <= sp ->
  (forall a : word, ~ aclient (live Σ) (frames Σ) sp (bv_unsigned a) -> m' a = m a) -> wmono asegs m m' -> ART_A Σ m'.
Proof.
  intros Σ m m' sp HA Hsp H WM. apply (ART_transport (W_client Σ sp) Σ m m' HA (munch_client Σ sp m m' H) WM).
  exact (art_avoid_client Σ m sp HA Hsp).
Qed.
