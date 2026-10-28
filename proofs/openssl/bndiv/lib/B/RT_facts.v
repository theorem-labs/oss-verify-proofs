(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface R_sizeclass R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_depot_defs R_fs_defs RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep I_lkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Facts.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma wr_at_stk : forall a n, wr_at bsegs m a n -> 0 <= n -> stk bsegs m a (a + n).
Proof.
  intros a n (H0 & H1 & H) Hn. split; [exact H0|]. split; [lia|]. intros x Hx.
  pose proof (H (x - a) ltac:(lia)) as W. replace (a + (x - a)) with x in W by lia. split; [exact W| exact (wview_mrd_A m _ W)].
Qed.

Lemma wr_at_sub : forall a n a' n', wr_at bsegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at bsegs m a' n'.
Proof. intros a n a' n' (H0 & H1 & H) X1 X2 X3. split; [lia|]. split; [lia|]. intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia. Qed.

(* [comment removed for export] *)
Lemma rta_live_block : forall p n, In (p, n) (live Σ) ->
  p mod 8 = 0 /\ 0 <= n /\ wr_at bsegs m p (ru8 n) /\ bytes_at bsegs m (shad p) (ushadow n) /\ p + ru8 n <= l_ACEIL L.
Proof.
  intros p n Hin. pose proof (ART_chunk Σ m HA) as [HP HS].
  destruct (geo_live Σ m HA p n Hin) as [(c & i & Hc & Hn & -> & X1 & X2 & X3 & X4 & X5)|(s & Hs & Hq & Hn' & -> & X1 & X5)].
  - pose proof (HP c i _ Hc Hn) as (Wr & _ & _ & B1 & _). pose proof (live_in_slot Σ m HA c i n Hc Hn) as (Y1 & Y2 & Y3 & Y4).
    destruct (slot_room c n Hc Y4 Y3) as (R1 & R2). pose proof (abeg_mod8 Σ m HA c i Hc) as M1.
    pose proof (rz_facts n) as (R3 & R4). pose proof (slot_geo Σ m HA c i _ Hc Hn) as (S1 & S2 & S3 & _).
    assert (M2 : rz_size n mod 8 = 0) by (apply (mod8_of _ 16 ltac:(lia) R3); exists 2; reflexivity).
    assert (Mp : p_ubeg SB c i n mod 8 = 0) by (rewrite <- Y1, Z.add_mod, M1, M2 by lia; reflexivity).
    split; [exact Mp|]. split; [exact Y4|]. split; [apply (wr_at_sub _ _ _ _ Wr); [lia | lia | unfold ru8; pose proof (Z.div_pos (n + 7) 8 ltac:(lia) ltac:(lia)); lia]|].
    split.
    + unfold pshadow_alloc in B1. apply bytes_at_app in B1 as [_ B1]. rewrite farun_len, Z.max_r in B1 by (apply Z.div_pos; lia).
      rewrite <- Y1. rewrite (shad_aligned_add (p_abeg SB c i) (rz_size n) M1 ltac:(lia)). exact B1.
    + pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (_ & _ & G3 & _).
      pose proof (geo_prb Σ m HA) as (P1 & P2 & _). unfold rb, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
  - destruct (In_nth_error _ _ Hs) as (k & Hk). pose proof (HS k s Hk) as (_ & Wr & _ & _ & _ & _ & B2 & _). rewrite Hq in B2.
    destruct (map_geo Σ m HA k s Hk) as (Hn & (G1 & G2 & G3 & G4 & G5) & _ & _ & Hroom).
    assert (M1 : s_mb s mod 8 = 0) by (apply (mod8_of _ 4096 ltac:(lia) G2); exists 512; reflexivity).
    unfold s_ubeg. rewrite <- Hn'. split; [apply Z.mod_divide; [lia|]; apply Z.mod_divide in M1; [|lia]; destruct M1 as [q Hq8]; rewrite Hq8; exists (q + 768); lia|].
    split; [lia|].
    split; [apply (wr_at_sub _ _ _ _ Wr); [lia | lia | unfold ru8; pose proof (Z.div_pos (s_n s + 7) 8 ltac:(lia) ltac:(lia)); lia]|].
    split; [replace (s_mb s + 4096 + 2048) with (s_mb s + 4096 + 2048) by ring; exact B2|]. lia.
Qed.

Lemma rta_acc_live : forall p n, In (p, n) (live Σ) -> wr_at bsegs m p n /\ acc bsegs m p n.
Proof.
  intros p n Hin. destruct (rta_live_block p n Hin) as (M & Hn & Wr & B & _). split.
  - apply (wr_at_sub _ _ _ _ Wr); [lia | unfold ru8; pose proof (Z.div_mod (n + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)); lia | exact Hn].
  - pose proof (rta_live_range Σ m p n HA Hin) as (P0 & _). apply (acc_ushadow bsegs m p n M ltac:(lia) Hn B).
Qed.

Lemma rta_live_slack : forall p n, In (p, n) (live Σ) ->
  exists slack, bytes_at bsegs m (p + n) slack /\ (- (p + n)) mod 8 <= Z.of_nat (length slack) /\ p + n + Z.of_nat (length slack) <= rtA_sp0 Σ - STACK_WIN.
Proof.
  intros p n Hin. destruct (rta_live_block p n Hin) as (M & Hn & Wr & _ & Hc).
  assert (Hr : n <= ru8 n < n + 8) by (unfold ru8; pose proof (Z.div_mod (n + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)); lia).
  pose proof (wr_at_stk _ _ Wr ltac:(lia)) as S. destruct (stk_split bsegs m p (p + n) (p + ru8 n) S ltac:(lia)) as [_ S2].
  destruct (stk_bytes bsegs m _ _ S2 ltac:(lia)) as (bs & Hl & Hb). exists bs. split; [exact Hb|]. rewrite Hl, Z2Nat.id by lia.
  split; [|unfold l_ACEIL, rtA_sp0 in *; lia].
  apply Z.mod_divide in M; [|lia]. destruct M as [q Hq]. subst p.
  assert (E : (- (q * 8 + n)) mod 8 = (- n) mod 8) by (replace (- (q * 8 + n)) with (- n + (- q) * 8) by ring; apply Z.mod_add; lia).
  rewrite E. unfold ru8.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma rta_acc_stack : forall a n, l_ACEIL L <= a -> a + n <= USTACK_TOP -> acc bsegs m a n.
Proof.
  intros a n H1 H2. destruct (ART_shadow Σ m HA) as (B & _ & _). pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & X3). unfold rtA_sp0 in *.
  assert (M1 : l_ACEIL L mod 8 = 0) by (unfold l_ACEIL, STACK_WIN; apply (mod8_of _ 16 ltac:(lia)); [rewrite Zminus_mod, X3; reflexivity | exists 2; reflexivity]).
  pose proof (acc_zero_run bsegs m (l_ACEIL L) _ M1 ltac:(unfold l_ACEIL, STACK_WIN, sp_window_lo in *; lia) B) as Acc.
  rewrite Z2Nat.id in Acc by (apply Z.div_pos; unfold l_ACEIL, STACK_WIN, sp_window_hi in *; lia).
  apply (acc_sub bsegs m _ _ _ _ Acc); [exact H1|]. apply Z.mod_divide in M1; [|lia]. destruct M1 as [q Hq]. rewrite Hq.
  replace (2 ^ 47 - q * 8) with ((2 ^ 44 - q) * 8) by ring. rewrite Z.div_mul by lia. unfold USTACK_TOP in H2. lia.
Qed.

(* [comment removed for export] *)
Lemma rta_live_disj : forall p1 n1 p2 n2 l1 l2, live Σ = l1 ++ (p1, n1) :: l2 -> In (p2, n2) (l1 ++ l2) -> p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof.
  intros p1 n1 p2 n2 l1 l2 E Hin. pose proof (geo_wf Σ m HA) as (_ & _ & HV & HS & _). destruct HV as (_ & HND & _).
  assert (H1 : In (p1, n1) (live Σ)) by (rewrite E; apply in_or_app; right; left; reflexivity).
  assert (H2 : In (p2, n2) (live Σ)) by (rewrite E; apply in_or_app; apply in_app_or in Hin as [X|X]; [left; exact X | right; right; exact X]).
  assert (Hne : p1 <> p2).
  { intros <-. rewrite E, map_app in HND. cbn [map fst] in HND. apply NoDup_ListNoDup in HND. apply NoDup_remove_2 in HND. apply HND. rewrite <- map_app.
    apply in_map_iff. exists (p1, n2). split; [reflexivity | exact Hin]. }
  destruct (geo_live Σ m HA p1 n1 H1) as [(c & i & Hc & Hn & -> & X1 & X2 & X3 & X4 & X5)|(s & Hs & Hq & Hn' & -> & X1 & X5)];
  destruct (geo_live Σ m HA p2 n2 H2) as [(c' & i' & Hc' & Hn2 & -> & Y1 & Y2 & Y3 & Y4 & Y5)|(s' & Hs' & Hq' & Hn2' & -> & Y1 & Y5)].
  - destruct (Z.eq_dec c c') as [<-|Hcc]; [destruct (Nat.eq_dec i i') as [<-|Hii]|].
    + rewrite Hn in Hn2. injection Hn2 as <-. exfalso. exact (Hne eq_refl).
    + destruct (slot_apart Σ m HA c i c i' _ _ Hc Hc' Hn Hn2 (or_intror Hii)); lia.
    + destruct (slot_apart Σ m HA c i c' i' _ _ Hc Hc' Hn Hn2 (or_introl Hcc)); lia.
  - pose proof (geo_prb Σ m HA) as (P1 & P2 & _). destruct HS as (_ & _ & _ & HSF & _).
    pose proof (proj1 (Forall_forall _ _) HSF s' Hs') as (_ & _ & Ha & _). unfold apart, s_ubeg, rb, kUserCap in *. rewrite <- Hn2' in Y1.
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
  - pose proof (geo_prb Σ m HA) as (P1 & P2 & _). destruct HS as (_ & _ & _ & HSF & _).
    pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (_ & _ & Ha & _). unfold apart, s_ubeg, rb, kUserCap in *. rewrite <- Hn' in X1.
    assert (c' * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
  - destruct HS as (_ & _ & _ & _ & HSP & _). destruct (In_nth_error _ _ Hs) as (k & Hk). destruct (In_nth_error _ _ Hs') as (k' & Hk').
    destruct (Nat.eq_dec k k') as [<-|Hkk].
    + rewrite Hk in Hk'. injection Hk' as <-. exfalso. exact (Hne eq_refl).
    + pose proof (HSP k k' s s' Hk Hk' Hkk) as Ha. unfold apart, s_ubeg in *. rewrite <- Hn' in X1. rewrite <- Hn2' in Y1. lia.
Qed.

(* [comment removed for export] *)
Lemma rta_frames_range : forall f k, In (f, k) (frames Σ) ->
  0 < f /\ f + fs_size k <= rtA_sp0 Σ - STACK_WIN /\ (f + fs_size k <= 0x10000 \/ SEGTOP_A <= f)
  /\ forall p n, In (p, n) (live Σ) -> f + fs_size k <= p \/ p + n <= f.
Proof.
  intros f k Hin. destruct (sep_frame Σ m HA f k Hin) as (X1 & X2 & X3).
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  unfold l_ACEIL, rtA_sp0 in *. split; [lia|]. split; [lia|]. split; [unfold SEGTOP_A in *; lia|].
  intros p n Hp. destruct (geo_live Σ m HA p n Hp) as [(c & i & Hc & _ & -> & Y1 & Y2 & Y3 & Y4 & Y5)|(s & Hs & _ & Hn' & -> & Y1 & Y5)].
  - pose proof (geo_prb Σ m HA) as (P1 & P2 & _). pose proof (geo_apart Σ m HA 0 5 _ _ ltac:(lia) eq_refl eq_refl) as Ha.
    cbn [fst snd] in Ha. unfold apart, rb, kUserCap in *. assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by lia. lia.
  - pose proof (geo_wf Σ m HA) as (_ & _ & _ & HS & _). destruct HS as (_ & _ & _ & HSF & _).
    pose proof (proj1 (Forall_forall _ _) HSF s Hs) as (_ & _ & _ & Ha & _). unfold apart, s_ubeg in *. rewrite <- Hn' in Y1. lia.
Qed.

End Facts.

Section Facts2.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).

(* [comment removed for export] *)
Lemma busy_slot : forall f k, In (f, k) (frames Σ) ->
  (k = 0 \/ k = 2 \/ k = 4)%nat /\ exists p, 0 <= p < NF (Z.of_nat k) /\ f = frame_addr (l_FSB L) (Z.of_nat k) p
    /\ nth (Z.to_nat p) (fss_flags (fs_of Σ k)) 0 = 1.
Proof.
  intros f k Hin. pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & _ & HF & _). destruct HF as (_ & _ & _ & HFr & _).
  exact (proj1 (Forall_forall _ _) HFr (f, k) Hin).
Qed.

Lemma rta_frames_align : forall f k, In (f, k) (frames Σ) -> f mod 64 = 0 /\ SEGTOP_A <= f.
Proof.
  intros f k Hin. destruct (busy_slot f k Hin) as (Hk & p & Hp & -> & _).
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  pose proof (sep_frame Σ m HA _ _ Hin) as (X & _). unfold SEGTOP_A in *. split; [|lia].
  unfold frame_addr, fsz. apply Z.mod_divide in G2; [|lia]. destruct G2 as [q Hq]. rewrite Hq. apply Z.mod_divide; [lia|].
  destruct Hk as [ -> | [ -> | -> ] ]; cbn; [exists (q * 64 + 576 + p) | exists (q * 64 + 576 + 2 * 2 ^ 14 + 4 * p) | exists (q * 64 + 576 + 4 * 2 ^ 14 + 16 * p)]; lia.
Qed.

Lemma rta_frames_disj : forall f1 k1 f2 k2 l1 l2, frames Σ = l1 ++ (f1, k1) :: l2 -> In (f2, k2) (l1 ++ l2) ->
  f1 + fs_size k1 <= f2 \/ f2 + fs_size k2 <= f1.
Proof.
  intros f1 k1 f2 k2 l1 l2 E Hin. pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & _ & HF & _). destruct HF as (_ & _ & _ & _ & HND & _).
  assert (H1 : In (f1, k1) (frames Σ)) by (rewrite E; apply in_or_app; right; left; reflexivity).
  assert (H2 : In (f2, k2) (frames Σ)) by (rewrite E; apply in_or_app; apply in_app_or in Hin as [X|X]; [left; exact X | right; right; exact X]).
  assert (Hne : (f1, k1) <> (f2, k2)).
  { intros Eq. rewrite E in HND. apply NoDup_ListNoDup in HND. apply NoDup_remove_2 in HND. apply HND. rewrite Eq. exact Hin. }
  destruct (busy_slot f1 k1 H1) as (Hk1 & p1 & Hp1 & -> & _). destruct (busy_slot f2 k2 H2) as (Hk2 & p2 & Hp2 & -> & _).
  assert (Hc1 : Z.of_nat k1 = 0 \/ Z.of_nat k1 = 2 \/ Z.of_nat k1 = 4) by (destruct Hk1 as [ -> | [ -> | -> ] ]; cbn; lia).
  assert (Hc2 : Z.of_nat k2 = 0 \/ Z.of_nat k2 = 2 \/ Z.of_nat k2 = 4) by (destruct Hk2 as [ -> | [ -> | -> ] ]; cbn; lia).
  rewrite !fs_size_fsz. apply (frame_apart _ _ _ _ _ Hc1 Hc2 Hp1 Hp2).
  destruct (Z.eq_dec (Z.of_nat k1) (Z.of_nat k2)) as [Ek|Ek]; [right|left; exact Ek]. intros Ep. apply Hne.
  apply Nat2Z.inj in Ek. subst k2 p2. reflexivity.
Qed.

Lemma rta_fshadow_apart : forall f k, In (f, k) (frames Σ) ->
  (forall p n, In (p, n) (live Σ) -> p + n <= shad f \/ shad (f + fs_size k) <= p)
  /\ (forall f' k', In (f', k') (frames Σ) -> f' + fs_size k' <= shad f \/ shad (f + fs_size k) <= f').
Proof.
  intros f k Hin. split; [intros p n Hp; exact (rta_live_fshadow Σ m p n f k HA Hp Hin)|].
  intros f' k' Hin'. destruct (sep_fshad Σ m HA f k Hin) as (X1 & X2). destruct (sep_frame Σ m HA f' k' Hin') as (Y1 & Y2 & _).
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (_ & _ & _ & G4 & _).
  unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
Qed.

Lemma rta_got_lib : ro_cells bsegs m 0x5e2c40 [C8 (Z_to_bv 64 0xbfae90)] /\ ro_cells bsegs m 0x5e2c40 [C8 (Z_to_bv 64 0xbfae90)].
Proof. pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & X10 & X11 & _)). split; assumption. Qed.

(* [comment removed for export] *)
Lemma rta_acc_static_cs : forall r a n, In r CS_ACC -> fst r <= a -> a + n <= snd r -> acc bsegs m a n.
Proof.
  intros r a n Hr H1 H2. pose proof (ART_shadow Σ m HA) as (_ & _ & _ & SA & _). unfold static_acc in SA.
  pose proof (proj1 (Forall_forall _ _) SA r Hr) as X. cbv beta in X. apply (acc_sub bsegs m _ _ _ _ X); lia.
Qed.

End Facts2.

(* [comment removed for export] *)
Lemma cs_acc_cover : forall x, client_static x -> ~ (0x5e7460 <= x < 0x6a0320) -> ~ (0x5e6660 <= x < 0x5e7140) -> ~ (0xbd6080 <= x < 0xbda540) ->
  exists r, In r CS_ACC /\ fst r <= x < snd r.
Proof.
  intros x (Hin & Hn) Hg Hg1 Hg2. destruct Hin as (lo & hi & Hin & Hx). unfold CLIENT_STATIC in Hin.
  Ltac pick_r lo hi := exists (lo, hi); split; [unfold CS_ACC; repeat (first [left; reflexivity | right]) | cbn; lia].
  Ltac rt_no lo hi Hn := exfalso; apply Hn; exists lo, hi; split; [unfold RT_STATIC; repeat (first [left; reflexivity | right]) | lia].
  destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
  - destruct (Z_lt_le_dec x 0x5e6660); [pick_r 0x5e6630 0x5e6660|].
    destruct (Z_lt_le_dec x 0x5e7140); [exfalso; lia|].
    destruct (Z_lt_le_dec x 0x5e7460); [pick_r 0x5e7140 0x5e7460|].
    destruct (Z_lt_le_dec x 0x6a0320); [exfalso; lia|].
    pick_r 0x6a0320 0x6a0398.
  - pick_r 0xbc6050 0xbd6050.
  - destruct (Z_lt_le_dec x 0xbd6080); [pick_r 0xbd6050 0xbd6080|].
    destruct (Z_lt_le_dec x 0xbda540); [exfalso; lia|].
    destruct (Z_lt_le_dec x 0xbdadf8); [pick_r 0xbda540 0xbdadf8|].
    destruct (Z_lt_le_dec x 0xbdae00); [rt_no 0xbdadf8 0xbdae00 Hn|].
    destruct (Z_lt_le_dec x 0xbdae48); [pick_r 0xbdae00 0xbdae48|].
    destruct (Z_lt_le_dec x 0xbdae90); [rt_no 0xbdae48 0xbdae90 Hn|].
    destruct (Z_lt_le_dec x 0xbfb110); [pick_r 0xbdae90 0xbfb110|].
    destruct (Z_lt_le_dec x 0xbfb118); [rt_no 0xbfb110 0xbfb118 Hn|].
    destruct (Z_lt_le_dec x 0xbfc1f8); [pick_r 0xbfb118 0xbfc1f8|].
    destruct (Z_lt_le_dec x 0xbfc200); [rt_no 0xbfc1f8 0xbfc200 Hn|].
    pick_r 0xbfc200 0xbfc730.
Qed.

Lemma rta_acc_static : forall Σ m a n, ART_A Σ m -> 0 <= a ->
  (forall i, 0 <= i < n -> client_static (a + i) /\ ~ (0x5e7460 <= a + i < 0x6a0320)
                           /\ ~ (0x5e6660 <= a + i < 0x5e7140) /\ ~ (0xbd6080 <= a + i < 0xbda540)) -> acc bsegs m a n.
Proof.
  intros Σ m a n HA Ha H i Hi. destruct (H i Hi) as (H1 & H2 & H3 & H4). destruct (cs_acc_cover _ H1 H2 H3 H4) as (r & Hr & Hx).
  pose proof (rta_acc_static_cs Σ m HA r (a + i) 1 Hr ltac:(lia) ltac:(lia) 0 ltac:(lia)) as (b & Hb & Ho).
  rewrite Z.add_0_r in Hb, Ho. exists b. split; assumption.
Qed.

Lemma rta_acc_lits : forall Σ m, ART_A Σ m -> Forall (fun r => acc bsegs m (fst r) (snd r)) ACC_LITS.
Proof.
  intros Σ m HA. unfold ACC_LITS.
  repeat (apply Forall_cons; [cbv beta; cbn [fst snd];
    match goal with |- acc _ _ ?a ?n => apply (rta_acc_static_cs Σ m HA (a, a + n)); [unfold CS_ACC; solve [repeat (first [left; reflexivity | right])] | cbn; lia | cbn; lia] end|]).
  apply Forall_nil.
Qed.

(* [comment removed for export] *)
Lemma rta_lib_sh : forall Σ m g, ART_A Σ m -> In g GDESC -> bytes_at bsegs m (shad (gd_beg g)) (ushadow (gd_size g)).
Proof.
  intros Σ m g HA Hg. pose proof (ART_shadow Σ m HA) as (_ & _ & _ & _ & LS). exact (proj1 (Forall_forall _ _) LS g Hg).
Qed.

Lemma rta_img_shadow : forall Σ m, ART_A Σ m -> stk bsegs m (shad 0x10000) (shad SEGTOP_A).
Proof.
  intros Σ m HA. pose proof (ART_shadow Σ m HA) as (_ & _ & S & _).
  assert (P : pg_dn (shad 0x10000) <= shad 0x10000) by (vm_compute; discriminate).
  assert (Q : shad 0x10000 <= shad SEGTOP_A) by (vm_compute; discriminate).
  exact (proj2 (stk_split bsegs m _ (shad 0x10000) _ S (conj P Q))).
Qed.

Lemma rta_sh_live : forall Σ m p n, ART_A Σ m -> In (p, n) (live Σ) -> bytes_at bsegs m (shad p) (ushadow n).
Proof. intros Σ m p n HA Hin. destruct (rta_live_block Σ m HA p n Hin) as (_ & _ & _ & B & _). exact B. Qed.
