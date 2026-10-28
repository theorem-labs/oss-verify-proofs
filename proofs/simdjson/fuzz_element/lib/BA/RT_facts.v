(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_glue_defs R_sec_defs R_depot_defs R_fs_defs RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import I_lkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Section Facts.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).

Lemma wr_at_stk : forall a n, wr_at asegs m a n -> 0 <= n -> stk asegs m a (a + n).
Proof.
  intros a n (H0 & H1 & H) Hn. split; [exact H0|]. split; [lia|]. intros x Hx.
  pose proof (H (x - a) ltac:(lia)) as W. replace (a + (x - a)) with x in W by lia. split; [exact W| exact (wview_mrd_A m _ W)].
Qed.

Lemma wr_at_sub : forall a n a' n', wr_at asegs m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> wr_at asegs m a' n'.
Proof. intros a n a' n' (H0 & H1 & H) X1 X2 X3. split; [lia|]. split; [lia|]. intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia. Qed.

Lemma rta_live_lo : forall p n, In (p, n) (live Σ) -> 0x10000 <= p.
Proof.
  intros p n Hin.
  destruct (geo_live Σ m HA p n Hin) as [(c & i & Hc & Hn & -> & X1 & X2 & X3 & X4 & X5)|(s & Hs & Hq & Hn' & -> & X1 & X5)].
  - pose proof (geo_prb Σ m HA) as (P1 & P2 & _).
    pose proof (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
    unfold rb, SEGTOP_A in *. assert (0 <= c * 2 ^ 32) by lia. lia.
  - destruct (In_nth_error _ _ Hs) as (k & Hk). destruct (map_geo Σ m HA k s Hk) as (Hn & (G1 & G2 & G3 & G4 & G5) & _ & _ & Hroom).
    unfold s_ubeg, SEGTOP_A in *. pose proof (smsz_room (s_n s) ltac:(lia)). lia.
Qed.

Lemma rta_live_size : forall p n, In (p, n) (live Σ) -> 1 <= n < 2 ^ 30.
Proof.
  intros p n Hin. pose proof (geo_wf Σ m HA) as (_ & HR & _). destruct HR as (HR & _).
  destruct (geo_live Σ m HA p n Hin) as [(c & i & Hc & Hn & _ & _ & _ & _ & _ & _)|(s & Hs & Hq & Hn' & _ & _ & _)].
  - pose proof (HR c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
    pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as (Hn1 & Hfit & _). cbv beta iota in Hn1, Hfit.
    pose proof (ClassSize_range c Hc). pose proof (rz_facts n). lia.
  - destruct (In_nth_error _ _ Hs) as (k & Hk). destruct (map_geo Σ m HA k s Hk) as (Hsn & _). lia.
Qed.

Lemma rta_live_block : forall p n, In (p, n) (live Σ) ->
  p mod 8 = 0 /\ 0 <= n /\ wr_at asegs m p (ru8 n) /\ bytes_at asegs m (shad p) (ushadowA (alook p n (ann Σ)) n) /\ p + ru8 n <= l_ACEIL L.
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
    + apply bytes_at_app in B1 as [_ B1]. rewrite farun_len, Z.max_r in B1 by (apply Z.div_pos; lia).
      rewrite <- Y1. rewrite (shad_aligned_add (p_abeg SB c i) (rz_size n) M1 ltac:(lia)). unfold p_ubeg. exact B1.
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

Lemma rta_acc_live : forall p k, In (p, k) (vis_live (ann Σ) (live Σ)) -> wr_at asegs m p k /\ acc asegs m p k.
Proof.
  intros p k HinV. destruct (In_vis_live (ann Σ) (live Σ) p k HinV) as (n & Hin & CASES).
  destruct (rta_live_block p n Hin) as (M & Hn & Wr & B & _).
  pose proof (rta_live_range Σ m p n HA Hin) as (P0 & _).
  assert (Hr : n <= ru8 n) by (unfold ru8; pose proof (Z.div_mod (n + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)); lia).
  assert (VAC : forall g, g <= 0 -> wr_at asegs m p g /\ acc asegs m p g).
  { intros g Hg. destruct Wr as (W0 & W1 & _). split; [split; [lia|]; split; [lia|]; intros i Hi; lia | intros i Hi; lia]. }
  destruct CASES as [(AL & ->)|(v & AL & Hk)].
  - rewrite AL in B. cbn [ushadowA] in B. split.
    + apply (wr_at_sub _ _ _ _ Wr); [lia | lia | exact Hn].
    + apply (acc_ushadow asegs m p n M ltac:(lia) Hn B).
  - pose proof (alook_ok p n (ann Σ) v AL) as (V1 & V2 & V3).
    destruct Hk as [ -> | [ -> | -> ] ].
    + rewrite AL in B. rewrite (ushadowA_some n v ltac:(lia) V2 ltac:(apply (mod8_of _ 16 ltac:(lia) V3); exists 2; reflexivity)) in B.
      apply bytes_at_app in B as [B _]. split.
      * apply (wr_at_sub _ _ _ _ Wr); [lia | lia | lia].
      * pose proof (acc_zero_run asegs m p _ M ltac:(lia) B) as ACC. rewrite Z2Nat.id in ACC by (apply Z.div_pos; lia).
        replace v with (8 * (v / 8)) by (pose proof (Z.div_mod v 8 ltac:(lia)); lia). exact ACC.
    + apply VAC. unfold ann_g1. pose proof (Z.div_pos (n / 16) 8192 ltac:(apply Z.div_pos; lia) ltac:(lia)). lia.
    + apply VAC. unfold ann_g2. pose proof (Z.mod_pos_bound (n / 16) 8192 ltac:(lia)). lia.
Qed.

Lemma rta_live_slack : forall p k, In (p, k) (vis_live (ann Σ) (live Σ)) ->
  exists slack, bytes_at asegs m (p + k) slack /\ (- (p + k)) mod 8 <= Z.of_nat (length slack) /\ p + k + Z.of_nat (length slack) <= rtA_sp0 Σ - STACK_WIN.
Proof.
  intros p k HinV. destruct (In_vis_live (ann Σ) (live Σ) p k HinV) as (n & Hin & CASES).
  destruct (rta_live_block p n Hin) as (M & Hn & Wr & _ & Hc).
  assert (Hr : n <= ru8 n < n + 8) by (unfold ru8; pose proof (Z.div_mod (n + 7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)); lia).
  pose proof (rta_live_lo p n Hin) as LO.
  assert (EMPTY : forall g, g mod 8 = 0 -> - 0x10000 < g <= n ->
            exists slack, bytes_at asegs m (p + g) slack /\ (- (p + g)) mod 8 <= Z.of_nat (length slack) /\ p + g + Z.of_nat (length slack) <= rtA_sp0 Σ - STACK_WIN).
  { intros g G8 Gr. exists []. cbn [length Z.of_nat]. split; [split; [lia|]; split; [unfold l_ACEIL, rtA_sp0, USTACK_TOP, STACK_WIN in *; cbn; pose proof (rta_sp0_range Σ m HA); unfold rtA_sp0, SEGTOP_A, STACK_WIN, USTACK_TOP in *; lia|]; intros i Hi; cbn in Hi; lia|].
    split; [|unfold l_ACEIL, rtA_sp0 in *; lia].
    apply Z.mod_divide in M; [|lia]. destruct M as [q Hq]. apply Z.mod_divide in G8; [|lia]. destruct G8 as [r Hr'].
    subst p g. replace (- (q * 8 + r * 8)) with ((- q - r) * 8) by ring. rewrite Z.mod_mul by lia. lia. }
  destruct CASES as [(AL & ->)|(v & AL & Hk)].
  - pose proof (wr_at_stk _ _ Wr ltac:(lia)) as S. destruct (stk_split asegs m p (p + n) (p + ru8 n) S ltac:(lia)) as [_ S2].
    destruct (stk_bytes asegs m _ _ S2 ltac:(lia)) as (bs & Hl & Hb). exists bs. split; [exact Hb|]. rewrite Hl, Z2Nat.id by lia.
    split; [|unfold l_ACEIL, rtA_sp0 in *; lia].
    apply Z.mod_divide in M; [|lia]. destruct M as [q Hq]. subst p.
    assert (E : (- (q * 8 + n)) mod 8 = (- n) mod 8) by (replace (- (q * 8 + n)) with (- n + (- q) * 8) by ring; apply Z.mod_add; lia).
    rewrite E. unfold ru8.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  - pose proof (alook_ok p n (ann Σ) v AL) as (V1 & V2 & V3).
    destruct Hk as [ -> | [ -> | -> ] ].
    + apply EMPTY; [exact V2 | lia].
    + apply EMPTY; unfold ann_g1; pose proof (Z.div_pos (n / 16) 8192 ltac:(apply Z.div_pos; lia) ltac:(lia)).
      * replace (- (8 * (n / 16 / 8192))) with ((- (n / 16 / 8192)) * 8) by ring. apply Z.mod_mul. lia.
      * pose proof (Z.div_le_upper_bound (n / 16) 8192 (n / 16) ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound n 16 n ltac:(lia) ltac:(lia)).
        assert (n / 16 / 8192 < 8192).
        { apply Z.div_lt_upper_bound; [lia|]. apply Z.div_lt_upper_bound; [lia|]. pose proof (rta_live_size p n Hin). lia. }
        lia.
    + apply EMPTY; unfold ann_g2; pose proof (Z.mod_pos_bound (n / 16) 8192 ltac:(lia)).
      * replace (- (8 * ((n / 16) mod 8192))) with ((- ((n / 16) mod 8192)) * 8) by ring. apply Z.mod_mul. lia.
      * pose proof (Z.mod_le (n / 16) 8192 ltac:(apply Z.div_pos; lia) ltac:(lia)). pose proof (Z.div_le_upper_bound n 16 n ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma rta_acc_stack : forall a n, l_ACEIL L <= a -> a + n <= USTACK_TOP -> acc asegs m a n.
Proof.
  intros a n H1 H2. destruct (ART_shadow Σ m HA) as (B & _ & _). pose proof (rta_sp0 Σ m HA) as ((X1 & X2) & X3). unfold rtA_sp0 in *.
  assert (M1 : l_ACEIL L mod 8 = 0) by (unfold l_ACEIL, STACK_WIN; apply (mod8_of _ 16 ltac:(lia)); [rewrite Zminus_mod, X3; reflexivity | exists 2; reflexivity]).
  pose proof (acc_zero_run asegs m (l_ACEIL L) _ M1 ltac:(unfold l_ACEIL, STACK_WIN, sp_window_lo in *; lia) B) as Acc.
  rewrite Z2Nat.id in Acc by (apply Z.div_pos; unfold l_ACEIL, STACK_WIN, sp_window_hi in *; lia).
  apply (acc_sub asegs m _ _ _ _ Acc); [exact H1|]. apply Z.mod_divide in M1; [|lia]. destruct M1 as [q Hq]. rewrite Hq.
  replace (2 ^ 47 - q * 8) with ((2 ^ 44 - q) * 8) by ring. rewrite Z.div_mul by lia. unfold USTACK_TOP in H2. lia.
Qed.

Lemma rta_live_disj_real : forall p1 n1 p2 n2, In (p1, n1) (live Σ) -> In (p2, n2) (live Σ) -> p1 <> p2 -> p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof.
  intros p1 n1 p2 n2 H1 H2 Hne. pose proof (geo_wf Σ m HA) as (_ & _ & HV & HS & _). destruct HV as (_ & HND & _).
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
    + rewrite Hk in Hk'. injection Hk' as <-. exfalso. unfold s_ubeg in Hne. exact (Hne eq_refl).
    + pose proof (HSP k k' s s' Hk Hk' Hkk) as Ha. unfold apart, s_ubeg in *. rewrite <- Hn' in X1. rewrite <- Hn2' in Y1. lia.
Qed.

Lemma vis_pos_count : forall p k, 0 < k -> (count_occ zz_eq_dec (vis_live (ann Σ) (live Σ)) (p, k) <= 1)%nat.
Proof.
  intros p k Hk. pose proof (geo_wf Σ m HA) as (_ & _ & HV & _). destruct HV as (_ & HND & _). apply NoDup_ListNoDup in HND.
  set (D := zz_eq_dec).
  destruct (in_dec D (p, k) (vis_live (ann Σ) (live Σ))) as [HinV|HninV]; [|rewrite (count_occ_not_In D _ _) in HninV; lia].
  destruct (In_vis_live (ann Σ) (live Σ) p k HinV) as (n & Hin & _).
  destruct (vis_live_split (ann Σ) (live Σ) p n HND Hin) as (L1 & L2 & EL & F1 & F2).
  rewrite EL, vis_live_app, vis_live_cons, !count_occ_app.
  rewrite (proj1 (count_occ_not_In D _ _) ltac:(intros X; exact (F1 (p, k) X eq_refl))), (proj1 (count_occ_not_In D _ _) ltac:(intros X; exact (F2 (p, k) X eq_refl))).
  unfold vis1. cbn [fst snd]. destruct (alook p n (ann Σ)) as [v|] eqn:AL.
  - pose proof (alook_ok p n (ann Σ) v AL) as (V1 & _). unfold ann_block. rewrite (proj2 (Z.eqb_neq v n) ltac:(lia)).
    pose proof (Z.div_pos (n / 16) 8192 ltac:(apply Z.div_pos; lia) ltac:(lia)). pose proof (Z.mod_pos_bound (n / 16) 8192 ltac:(lia)).
    cbn [count_occ]. destruct (D (p, ann_g1 n) (p, k)) as [E|_]; [injection E; unfold ann_g1; lia|].
    destruct (D (p, ann_g2 n) (p, k)) as [E|_]; [injection E; unfold ann_g2; lia|]. destruct (D (p, v) (p, k)); cbn; lia.
  - cbn [count_occ]. destruct (D (p, n) (p, k)); cbn; lia.
Qed.

Lemma rta_live_disj : forall p1 n1 p2 n2 l1 l2, vis_live (ann Σ) (live Σ) = l1 ++ (p1, n1) :: l2 -> In (p2, n2) (l1 ++ l2) -> p1 + n1 <= p2 \/ p2 + n2 <= p1.
Proof.
  intros p1 n1 p2 n2 l1 l2 E Hin.
  assert (H1 : In (p1, n1) (vis_live (ann Σ) (live Σ))) by (rewrite E; apply in_or_app; right; left; reflexivity).
  assert (H2 : In (p2, n2) (vis_live (ann Σ) (live Σ))) by (rewrite E; apply in_or_app; apply in_app_or in Hin as [X|X]; [left; exact X | right; right; exact X]).
  destruct (In_vis_live_le (ann Σ) (live Σ) p1 n1 H1) as (N1 & R1 & L1 & _).
  destruct (In_vis_live_le (ann Σ) (live Σ) p2 n2 H2) as (N2 & R2 & L2 & _).
  destruct (Z.eq_dec p1 p2) as [<-|Hne].
  - destruct (Z_le_dec n1 0) as [Z1|Z1]; [left; lia|]. destruct (Z_le_dec n2 0) as [Z2|Z2]; [right; lia|]. exfalso.

    assert (EQ : n2 = n1).
    { destruct (In_vis_live (ann Σ) (live Σ) p1 n1 H1) as (M1 & I1 & C1). destruct (In_vis_live (ann Σ) (live Σ) p1 n2 H2) as (M2 & I2 & C2).
      pose proof (geo_wf Σ m HA) as (_ & _ & HV & _). destruct HV as (_ & HND & _). apply NoDup_ListNoDup in HND.
      assert (M2 = M1) as ->.
      { apply in_split in I1 as (A1 & B1 & EL). rewrite EL in HND, I2. rewrite map_app in HND. cbn [map fst] in HND. apply NoDup_remove in HND as [_ NI].
        apply in_app_or in I2 as [X|[X|X]]; [exfalso | injection X as ->; reflexivity | exfalso]; apply NI; apply in_or_app; [left|right]; apply in_map_iff; eexists; (split; [|exact X]); reflexivity. }
      destruct C1 as [(A1 & ->)|(v1 & A1 & K1)]; destruct C2 as [(A2 & ->)|(v2 & A2 & K2)]; try reflexivity; try (rewrite A1 in A2; discriminate A2).
      rewrite A1 in A2. injection A2 as <-. pose proof (alook_ok p1 M1 (ann Σ) v1 A1) as (O1 & _).
      pose proof (Z.div_pos (M1 / 16) 8192 ltac:(apply Z.div_pos; lia) ltac:(lia)). pose proof (Z.mod_pos_bound (M1 / 16) 8192 ltac:(lia)).
      unfold ann_g1, ann_g2 in K1, K2. lia. }
    subst n2. pose proof (vis_pos_count p1 n1 ltac:(lia)) as C. rewrite E in C.
    rewrite count_occ_app in C. cbn [count_occ] in C. destruct (zz_eq_dec (p1, n1) (p1, n1)) as [_|X]; [|exact (X eq_refl)].
    pose proof (proj1 (count_occ_In zz_eq_dec _ _) Hin) as C2. rewrite count_occ_app in C2. lia.
  - destruct (rta_live_disj_real p1 N1 p2 N2 R1 R2 Hne); lia.
Qed.

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

Lemma rta_live_range_vis : forall p k, In (p, k) (vis_live (ann Σ) (live Σ)) ->
  0 < p /\ p + k <= rtA_sp0 Σ - STACK_WIN /\ (p + k <= 0x10000 \/ SEGTOP_A <= p).
Proof.
  intros p k HinV. destruct (In_vis_live_le (ann Σ) (live Σ) p k HinV) as (n & Hin & Hk & _).
  pose proof (rta_live_range Σ m p n HA Hin) as (A1 & A2 & A3). split; [lia|]. split; [lia|]. lia.
Qed.
Lemma rta_frames_range_vis : forall f k, In (f, k) (frames Σ) ->
  0 < f /\ f + fs_size k <= rtA_sp0 Σ - STACK_WIN /\ (f + fs_size k <= 0x10000 \/ SEGTOP_A <= f)
  /\ forall p n, In (p, n) (vis_live (ann Σ) (live Σ)) -> f + fs_size k <= p \/ p + n <= f.
Proof.
  intros f k Hin. destruct (rta_frames_range f k Hin) as (A1 & A2 & A3 & A4). split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
  intros p n' HinV. destruct (In_vis_live_le (ann Σ) (live Σ) p n' HinV) as (n & Hp & Hk & _). destruct (A4 p n Hp); lia.
Qed.

End Facts.

Section Facts2.
Variables (Σ : rtsA) (m : mem).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).

Lemma busy_slot : forall f k, In (f, k) (frames Σ) ->
  (k = 5 \/ k = 0 \/ k = 4 \/ k = 1)%nat /\ exists p, 0 <= p < NF (Z.of_nat k) /\ f = frame_addr (l_FSB L) (Z.of_nat k) p
    /\ nth (Z.to_nat p) (fss_flags (fs_of Σ k)) 0 = 1.
Proof.
  intros f k Hin. pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & _ & HF & _). destruct HF as (_ & _ & _ & _ & HFr & _).
  exact (proj1 (Forall_forall _ _) HFr (f, k) Hin).
Qed.

Lemma rta_frames_align : forall f k, In (f, k) (frames Σ) -> f mod 64 = 0 /\ SEGTOP_A <= f.
Proof.
  intros f k Hin. destruct (busy_slot f k Hin) as (Hk & p & Hp & -> & _).
  pose proof (geo_grant Σ m HA (l_FSB L) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
  pose proof (sep_frame Σ m HA _ _ Hin) as (X & _). unfold SEGTOP_A in *. split; [|lia].
  unfold frame_addr, fsz. apply Z.mod_divide in G2; [|lia]. destruct G2 as [q Hq]. rewrite Hq. apply Z.mod_divide; [lia|].
  destruct Hk as [ -> | [ -> | [ -> | -> ] ] ]; cbn; [exists (q * 64 + 576 + 5 * 2 ^ 14 + 32 * p) | exists (q * 64 + 576 + 0 * 2 ^ 14 + 1 * p) | exists (q * 64 + 576 + 4 * 2 ^ 14 + 16 * p) | exists (q * 64 + 576 + 1 * 2 ^ 14 + 2 * p)]; lia.
Qed.

Lemma rta_frames_disj : forall f1 k1 f2 k2 l1 l2, frames Σ = l1 ++ (f1, k1) :: l2 -> In (f2, k2) (l1 ++ l2) ->
  f1 + fs_size k1 <= f2 \/ f2 + fs_size k2 <= f1.
Proof.
  intros f1 k1 f2 k2 l1 l2 E Hin. pose proof (geo_wf Σ m HA) as (_ & _ & _ & _ & _ & HF & _). destruct HF as (_ & _ & _ & _ & _ & HND & _).
  assert (H1 : In (f1, k1) (frames Σ)) by (rewrite E; apply in_or_app; right; left; reflexivity).
  assert (H2 : In (f2, k2) (frames Σ)) by (rewrite E; apply in_or_app; apply in_app_or in Hin as [X|X]; [left; exact X | right; right; exact X]).
  assert (Hne : (f1, k1) <> (f2, k2)).
  { intros Eq. rewrite E in HND. apply NoDup_ListNoDup in HND. apply NoDup_remove_2 in HND. apply HND. rewrite Eq. exact Hin. }
  destruct (busy_slot f1 k1 H1) as (Hk1 & p1 & Hp1 & -> & _). destruct (busy_slot f2 k2 H2) as (Hk2 & p2 & Hp2 & -> & _).
  assert (Hc1 : Z.of_nat k1 = 5 \/ Z.of_nat k1 = 0 \/ Z.of_nat k1 = 4 \/ Z.of_nat k1 = 1) by (destruct Hk1 as [ -> | [ -> | [ -> | -> ] ] ]; cbn; lia).
  assert (Hc2 : Z.of_nat k2 = 5 \/ Z.of_nat k2 = 0 \/ Z.of_nat k2 = 4 \/ Z.of_nat k2 = 1) by (destruct Hk2 as [ -> | [ -> | [ -> | -> ] ] ]; cbn; lia).
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

Lemma rta_got_lib : ro_cells asegs m 0x16afd8 [C8 (Z_to_bv 64 0x6c7ea8)] /\ ro_cells asegs m 0x16afd8 [C8 (Z_to_bv 64 0x6c7ea8)].
Proof. pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & X10 & X11 & _)). split; assumption. Qed.

Lemma rta_acc_static_cs : forall r a n, In r CS_ACC -> fst r <= a -> a + n <= snd r -> acc asegs m a n.
Proof.
  intros r a n Hr H1 H2. pose proof (ART_shadow Σ m HA) as (_ & _ & _ & SA & _). unfold static_acc in SA.
  pose proof (proj1 (Forall_forall _ _) SA r Hr) as X. cbv beta in X. apply (acc_sub asegs m _ _ _ _ X); lia.
Qed.

Lemma rta_fshadow_apart_vis : forall f k, In (f, k) (frames Σ) ->
  (forall p n, In (p, n) (vis_live (ann Σ) (live Σ)) -> p + n <= shad f \/ shad (f + fs_size k) <= p)
  /\ (forall f' k', In (f', k') (frames Σ) -> f' + fs_size k' <= shad f \/ shad (f + fs_size k) <= f').
Proof.
  intros f k Hin. destruct (rta_fshadow_apart f k Hin) as [A1 A2]. split; [|exact A2].
  intros p n' HinV. destruct (In_vis_live_le (ann Σ) (live Σ) p n' HinV) as (n & Hp & Hk & _). destruct (A1 p n Hp); lia.
Qed.

End Facts2.

Lemma cs_acc_cover : forall x, client_static x -> ~ (0x16ed30 <= x < 0x170570) -> exists r, In r CS_ACC /\ fst r <= x < snd r.
Proof.
  intros x (Hin & Hn) Hg. destruct Hin as (lo & hi & Hin & Hx). unfold CLIENT_STATIC in Hin.
  Ltac pick_r lo hi := exists (lo, hi); split; [unfold CS_ACC; repeat (first [left; reflexivity | right]) | cbn; lia].
  Ltac rt_no lo hi Hn := exfalso; apply Hn; exists lo, hi; split; [unfold RT_STATIC; repeat (first [left; reflexivity | right]) | lia].
  destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-.
  - destruct (Z_lt_le_dec x 0x16ed30); [pick_r 0x16e760 0x16ed30|].
    destruct (Z_lt_le_dec x 0x170570); [exfalso; lia|].
    pick_r 0x170570 0x1705d8.
  - pick_r 0x696290 0x6a6290.
  - destruct (Z_lt_le_dec x 0x6a62f0); [pick_r 0x6a6290 0x6a62f0|].
    destruct (Z_lt_le_dec x 0x6a6320); [rt_no 0x6a62f0 0x6a6320 Hn|].
    destruct (Z_lt_le_dec x 0x6a6328); [pick_r 0x6a6320 0x6a6328|].
    destruct (Z_lt_le_dec x 0x6a6340); [rt_no 0x6a6328 0x6a6340 Hn|].
    destruct (Z_lt_le_dec x 0x6a6348); [pick_r 0x6a6340 0x6a6348|].
    destruct (Z_lt_le_dec x 0x6a6360); [rt_no 0x6a6348 0x6a6360 Hn|].
    destruct (Z_lt_le_dec x 0x6a6368); [pick_r 0x6a6360 0x6a6368|].
    destruct (Z_lt_le_dec x 0x6a6380); [rt_no 0x6a6368 0x6a6380 Hn|].
    destruct (Z_lt_le_dec x 0x6a6390); [pick_r 0x6a6380 0x6a6390|].
    destruct (Z_lt_le_dec x 0x6a63a0); [rt_no 0x6a6390 0x6a63a0 Hn|].
    destruct (Z_lt_le_dec x 0x6a63a8); [pick_r 0x6a63a0 0x6a63a8|].
    destruct (Z_lt_le_dec x 0x6a63c0); [rt_no 0x6a63a8 0x6a63c0 Hn|].
    destruct (Z_lt_le_dec x 0x6a63c8); [pick_r 0x6a63c0 0x6a63c8|].
    destruct (Z_lt_le_dec x 0x6a63e0); [rt_no 0x6a63c8 0x6a63e0 Hn|].
    destruct (Z_lt_le_dec x 0x6a6410); [pick_r 0x6a63e0 0x6a6410|].
    destruct (Z_lt_le_dec x 0x6a6440); [rt_no 0x6a6410 0x6a6440 Hn|].
    destruct (Z_lt_le_dec x 0x6a6448); [pick_r 0x6a6440 0x6a6448|].
    destruct (Z_lt_le_dec x 0x6a6460); [rt_no 0x6a6448 0x6a6460 Hn|].
    destruct (Z_lt_le_dec x 0x6a7e10); [pick_r 0x6a6460 0x6a7e10|].
    destruct (Z_lt_le_dec x 0x6a7e18); [rt_no 0x6a7e10 0x6a7e18 Hn|].
    destruct (Z_lt_le_dec x 0x6a7e60); [pick_r 0x6a7e18 0x6a7e60|].
    destruct (Z_lt_le_dec x 0x6a7e80); [rt_no 0x6a7e60 0x6a7e80 Hn|].
    destruct (Z_lt_le_dec x 0x6a7e88); [pick_r 0x6a7e80 0x6a7e88|].
    destruct (Z_lt_le_dec x 0x6a7e98); [rt_no 0x6a7e88 0x6a7e98 Hn|].
    destruct (Z_lt_le_dec x 0x6c8128); [pick_r 0x6a7e98 0x6c8128|].
    destruct (Z_lt_le_dec x 0x6c8130); [rt_no 0x6c8128 0x6c8130 Hn|].
    destruct (Z_lt_le_dec x 0x6c9320); [pick_r 0x6c8130 0x6c9320|].
    destruct (Z_lt_le_dec x 0x6c9328); [rt_no 0x6c9320 0x6c9328 Hn|].
    pick_r 0x6c9328 0x6c9858.
Qed.

Lemma rta_acc_static : forall Σ m a n, ART_A Σ m -> 0 <= a ->
  (forall i, 0 <= i < n -> client_static (a + i) /\ ~ (0x16ed30 <= a + i < 0x170570)) -> acc asegs m a n.
Proof.
  intros Σ m a n HA Ha H i Hi. destruct (H i Hi) as [H1 H2]. destruct (cs_acc_cover _ H1 H2) as (r & Hr & Hx).
  pose proof (rta_acc_static_cs Σ m HA r (a + i) 1 Hr ltac:(lia) ltac:(lia) 0 ltac:(lia)) as (b & Hb & Ho).
  rewrite Z.add_0_r in Hb, Ho. exists b. split; assumption.
Qed.

Lemma rta_acc_lits : forall Σ m, ART_A Σ m -> Forall (fun r => acc asegs m (fst r) (snd r)) ACC_LITS.
Proof.
  intros Σ m HA. unfold ACC_LITS.
  repeat (apply Forall_cons; [cbv beta; cbn [fst snd];
    match goal with |- acc _ _ ?a ?n => apply (rta_acc_static_cs Σ m HA (a, a + n)); [unfold CS_ACC; solve [repeat (first [left; reflexivity | right])] | cbn; lia | cbn; lia] end|]).
  apply Forall_nil.
Qed.

Theorem ART_client_frame_vis : forall Σ (m m' : mem) (sp : Z), ART_A Σ m -> rtA_sp0 Σ - STACK_WIN <= sp ->
  (forall a : word, ~ aclient (rtA_live Σ) (frames Σ) sp (bv_unsigned a) -> m' a = m a) -> wmono asegs m m' -> ART_A Σ m'.
Proof.
  intros Σ m m' sp HA Hsp H WM. apply (ART_client_frame Σ m m' sp HA Hsp); [|exact WM].
  intros a Ha. apply H. intros X. apply Ha. exact (aclient_vis (ann Σ) (live Σ) (frames Σ) sp _ X).
Qed.

End GWIN.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
