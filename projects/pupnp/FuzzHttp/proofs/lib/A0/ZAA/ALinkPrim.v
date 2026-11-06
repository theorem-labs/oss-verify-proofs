(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import LiaTuning ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Bridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAA Require Import ALayout APrim APrimLem APrimSpec APrimSpec2 LJ ALinkPg ALinkVm ALink.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section P.
Context {HC : HasCeiling}.
Variable Bs : vmbase.
Variable AL : alayout.
Hypothesis BO : base_ok Bs.
Hypothesis SPACE_EQ : vb_space Bs = al_space AL.
Hypothesis SPACE_AL : al_space AL mod 65536 = 0.

#[using="AL"] Lemma lenZ_kmap : forall d, 0 < d -> d < 2^40 -> d mod K_MAP = 0 -> lenZ d = d /\ d mod 32768 = 0.
Proof.
  intros d H0 H1 Hm. split.
  - apply lenZ_id; [lia|]. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[using="BO SPACE_EQ SPACE_AL"] Lemma link_opt_region : forall v mo (b : bool) c off d (Q : exc unit -> Model -> Prop),
  LINK Bs v mo -> 1 <= c <= 31 ->
  (b = true -> 0 <= off /\ off mod K_MAP = 0 /\ 0 < d /\ d mod K_MAP = 0 /\ off + d <= K_REGION
               /\ vroom Bs v (d + d / 8 + 2 * page_size)) ->
  (forall mo', LINK Bs (mkVA (va_prim v + (if b then d else 0)) (va_chunks v) (va_nsec v) (va_aux v)) mo' ->
               m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo -> Q (Ok tt) mo') ->
  stwfL (t_opt b (region AL c + off) d) mo Q.
Proof.
  intros v mo b c off d Q LK Hc Hb HQ. unfold t_opt. destruct b.
  - destruct (Hb eq_refl) as (O1 & O2 & D1 & D2 & D3 & VR).
    destruct (lenZ_kmap d D1 ltac:(lia) D2) as [EL M32].
    pose proof (region_range AL c Hc) as [R1 R2]. unfold region in *.
    apply (link_commit Bs v mo (al_space AL + c * K_REGION + off) d Q BO LK); rewrite ?EL; try lia.
    + Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    + exact VR.
    + intros mo' LK' F. apply HQ; [| exact F]. exact LK'.
  - unfold t_none. apply stwf_ret. apply HQ; [| split; reflexivity].
    replace (va_prim v + 0) with (va_prim v) by lia. destruct v; exact LK.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[using="AL"] Lemma vroom_after_commit : forall v mo d e,
  LINK Bs v mo -> d mod 32768 = 0 -> vroom Bs v (d + d / 8 + e) ->
  vroom Bs (mkVA (va_prim v + d) (va_chunks v) (va_nsec v) (va_aux v)) e.
Proof.
  intros v mo d e LK Hd VR. destruct (lk_pal Bs v mo LK) as [Hp _]. unfold vroom in *. cbn [va_prim va_chunks va_nsec va_aux].
  rewrite (div8_add_aligned _ _ Hp Hd). lia.
Qed.

Definition D_efa (k : pclass) (total : Z) : Z := efa_new k total - p_mfa k.
Definition pop_k1 (k : pclass) (c r : Z) : pclass :=
  mkPCL (p_nf k) (p_mfa k) (p_au k) (pop_mu k c r) (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k).
Definition D_pop (k : pclass) (c r : Z) : Z := (pop_mu k c r - p_mu k) + D_efa (pop_k1 k c r) (p_nf k + pop_new k c r).
Definition D_gfa (k : pclass) (c n : Z) : Z := if p_nf k <? n then D_pop k c (n - p_nf k) else 0.

#[using="AL"] Lemma eqb_sub0 : forall x y, (x =? y) = (x - y =? 0).
Proof. intros x y. destruct (Z.eqb_spec x y), (Z.eqb_spec (x - y) 0); try reflexivity; lia. Qed.

#[using="AL"] Lemma efa_new_facts : forall k total, 0 <= p_mfa k <= K_FA_SIZE -> p_mfa k mod K_MAP = 0 -> 0 <= total -> 4 * total + K_MAP <= K_FA_SIZE ->
  p_mfa k <= efa_new k total /\ efa_new k total mod K_MAP = 0 /\ efa_new k total <= K_FA_SIZE
  /\ (efa_new k total =? p_mfa k) = (D_efa k total =? 0) /\ 0 <= D_efa k total /\ D_efa k total mod K_MAP = 0.
Proof.
  intros k total H0 Hm Ht Hb. unfold D_efa. rewrite <- eqb_sub0. unfold efa_new.
  destruct (Z.leb_spec (4 * total) (p_mfa k)) as [Hle|Hgt].
  - replace (p_mfa k - p_mfa k) with 0 by lia. repeat split; try reflexivity; try lia; try assumption.
  - pose proof (rup_ge (4 * total) K_MAP ltac:(lia)). pose proof (rup_mod (4 * total) K_MAP ltac:(lia)) as Hr.
    pose proof (rup_lt (4 * total) K_MAP ltac:(lia)).
    assert (rup (4 * total) K_MAP <= K_FA_SIZE) by (apply rup_le; [lia| lia| reflexivity]).
    repeat split; try reflexivity; try lia; try assumption.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[using="BO SPACE_EQ SPACE_AL"] Lemma link_efa : forall v mo c k total (Q : exc unit -> Model -> Prop),
  LINK Bs v mo -> 1 <= c <= 31 ->
  0 <= p_mfa k <= K_FA_SIZE -> p_mfa k mod K_MAP = 0 -> 0 <= total -> 4 * total + K_MAP <= K_FA_SIZE ->
  vroom Bs v (D_efa k total + D_efa k total / 8 + 2 * page_size) ->
  (forall mo', LINK Bs (mkVA (va_prim v + D_efa k total) (va_chunks v) (va_nsec v) (va_aux v)) mo' ->
               m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo -> Q (Ok tt) mo') ->
  stwfL (t_efa AL c k total) mo Q.
Proof.
  intros v mo c k total Q LK Hc H0 Hm Ht Hb VR HQ.
  destruct (efa_new_facts k total H0 Hm Ht Hb) as (E1 & E2 & E3 & E4 & E5 & E6).
  unfold t_efa. replace (fa_base AL c + p_mfa k) with (region AL c + (FA_OFF + p_mfa k)) by (unfold fa_base; lia).
  fold (D_efa k total). rewrite E4.
  apply (link_opt_region v mo (negb (D_efa k total =? 0)) c (FA_OFF + p_mfa k) (D_efa k total) Q LK Hc).
  - intros Hb'. apply negb_true_iff in Hb'. apply Z.eqb_neq in Hb'. unfold D_efa in *.
    repeat split; try lia; try assumption.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  - intros mo' LK' F. apply HQ; [| exact F].
    destruct (Z.eqb_spec (D_efa k total) 0) as [E0|]; cbn [negb] in LK'; [rewrite E0; exact LK'| exact LK'].
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[using="AL"] Lemma vroom_mono : forall v e e', e' <= e -> vroom Bs v e -> vroom Bs v e'.
Proof. intros v e e' H VR. unfold vroom in *. lia. Qed.

#[using="AL"] Lemma pop_mu_facts : forall k c r, 0 <= p_mu k -> p_mu k mod K_MAP = 0 ->
  p_mu k <= pop_mu k c r /\ pop_mu k c r mod K_MAP = 0 /\ (pop_mu k c r - p_mu k) mod K_MAP = 0.
Proof.
  intros k c r H0 Hm. unfold pop_mu. cbv zeta.
  destruct (Z.leb_spec (p_au k + r * class_size c) (p_mu k)) as [Hle|Hgt].
  - replace (p_mu k - p_mu k) with 0 by lia. repeat split; try reflexivity; try lia; try assumption.
  - pose proof (rup_ge (p_au k + r * class_size c - p_mu k) K_MAP ltac:(lia)).
    pose proof (rup_mod (p_au k + r * class_size c - p_mu k) K_MAP ltac:(lia)) as Hr.
    repeat split; try lia.
    + rewrite <- Z.add_mod_idemp_l, Hm by lia. rewrite Z.add_0_l. exact Hr.
    + replace (p_mu k + rup (p_au k + r * class_size c - p_mu k) K_MAP - p_mu k) with (rup (p_au k + r * class_size c - p_mu k) K_MAP) by lia. exact Hr.
Qed.

#[using="AL"] Lemma div8_kmap : forall a b, a mod K_MAP = 0 -> b mod K_MAP = 0 -> (a + b) / 8 = a / 8 + b / 8.
Proof. intros a b Ha Hb. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[using="AL"] Lemma kmap_32k : forall a, a mod K_MAP = 0 -> a mod 32768 = 0.
Proof. intros a Ha. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[using="BO SPACE_EQ SPACE_AL"] Lemma link_populate : forall v mo c k r (Q : exc unit -> Model -> Prop),
  LINK Bs v mo -> 1 <= c <= 31 ->
  0 <= p_mu k -> p_mu k mod K_MAP = 0 -> pop_mu k c r <= FA_OFF ->
  0 <= p_mfa k <= K_FA_SIZE -> p_mfa k mod K_MAP = 0 ->
  0 <= p_nf k + pop_new k c r -> 4 * (p_nf k + pop_new k c r) + K_MAP <= K_FA_SIZE ->
  vroom Bs v (D_pop k c r + D_pop k c r / 8 + 4 * page_size) ->
  (forall mo', LINK Bs (mkVA (va_prim v + D_pop k c r) (va_chunks v) (va_nsec v) (va_aux v)) mo' ->
               m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo -> Q (Ok tt) mo') ->
  stwfL (t_populate AL c k r) mo Q.
Proof.
  intros v mo c k r Q LK Hc Hmu0 Hmum Hfa Hmfa Hmfam Ht0 Htb VR HQ.
  destruct (pop_mu_facts k c r Hmu0 Hmum) as (M1 & M2 & M3).
  destruct (efa_new_facts (pop_k1 k c r) (p_nf k + pop_new k c r) Hmfa Hmfam Ht0 Htb) as (E1 & E2 & E3 & E4 & E5 & E6).
  set (D1 := pop_mu k c r - p_mu k) in *. set (D2 := D_efa (pop_k1 k c r) (p_nf k + pop_new k c r)) in *.
  assert (ED : D_pop k c r = D1 + D2) by reflexivity. rewrite ED in *.
  rewrite (div8_kmap D1 D2 M3 E6) in VR.
  unfold t_populate. cbv zeta. fold (pop_k1 k c r). rewrite (eqb_sub0 (pop_mu k c r) (p_mu k)). fold D1.
  apply stwf_ebind.
  apply (link_opt_region v mo (negb (D1 =? 0)) c (p_mu k) D1 _ LK Hc).
  - intros Hb. apply negb_true_iff in Hb. apply Z.eqb_neq in Hb. unfold page_size in *.
    repeat split; try lia; try assumption. eapply vroom_mono; [| exact VR]. unfold page_size. lia.
  - intros mo1 LK1 [F1 F2].
    assert (LK1' : LINK Bs (mkVA (va_prim v + D1) (va_chunks v) (va_nsec v) (va_aux v)) mo1).
    { destruct (Z.eqb_spec D1 0) as [E0|]; cbn [negb] in LK1; [rewrite E0; exact LK1| exact LK1]. }
    apply (link_efa _ mo1 c (pop_k1 k c r) (p_nf k + pop_new k c r) Q LK1' Hc Hmfa Hmfam Ht0 Htb).
    + fold D2. apply (vroom_after_commit v mo D1 _ LK (kmap_32k _ M3)). eapply vroom_mono; [| exact VR]. unfold page_size. lia.
    + intros mo2 LK2 [G1 G2]. fold D2 in LK2. cbn [va_prim va_chunks va_nsec va_aux] in LK2.
      apply HQ; [| split; congruence]. replace (va_prim v + (D1 + D2)) with (va_prim v + D1 + D2) by lia. exact LK2.
Qed.

#[using="BO SPACE_EQ SPACE_AL"] Lemma link_gfa : forall v mo c k n (Q : exc unit -> Model -> Prop),
  LINK Bs v mo -> 1 <= c <= 31 ->
  (p_nf k < n ->
     0 <= p_mu k /\ p_mu k mod K_MAP = 0 /\ pop_mu k c (n - p_nf k) <= FA_OFF /\
     0 <= p_mfa k <= K_FA_SIZE /\ p_mfa k mod K_MAP = 0 /\
     0 <= p_nf k + pop_new k c (n - p_nf k) /\ 4 * (p_nf k + pop_new k c (n - p_nf k)) + K_MAP <= K_FA_SIZE /\
     vroom Bs v (D_gfa k c n + D_gfa k c n / 8 + 4 * page_size)) ->
  (forall mo', LINK Bs (mkVA (va_prim v + D_gfa k c n) (va_chunks v) (va_nsec v) (va_aux v)) mo' ->
               m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo -> Q (Ok tt) mo') ->
  stwfL (t_gfa AL c k n) mo Q.
Proof.
  intros v mo c k n Q LK Hc Hp HQ. unfold t_gfa, D_gfa in *. destruct (Z.ltb_spec (p_nf k) n) as [Hlt|Hge].
  - destruct (Hp Hlt) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    apply stwf_ebind. apply (link_populate v mo c k (n - p_nf k) _ LK Hc P1 P2 P3 P4 P5 P6 P7 P8).
    intros mo' LK' F. unfold t_none. apply stwf_ret. exact (HQ mo' LK' F).
  - unfold t_none. apply stwf_ret. apply HQ; [| split; reflexivity].
    replace (va_prim v + 0) with (va_prim v) by lia. destruct v; exact LK.
Qed.

#[using="AL"] Lemma refill_budget_facts : forall c k, 1 <= c <= 31 -> pclass_wf c k -> refill_budget c k ->
  let n := max_count c / 2 in
  p_nf k < n ->
  0 <= p_mu k /\ p_mu k mod K_MAP = 0 /\ pop_mu k c (n - p_nf k) <= FA_OFF /\
  0 <= p_mfa k <= K_FA_SIZE /\ p_mfa k mod K_MAP = 0 /\
  0 <= p_nf k + pop_new k c (n - p_nf k) /\ 4 * (p_nf k + pop_new k c (n - p_nf k)) + K_MAP <= K_FA_SIZE.
Proof.
  intros c k Hc WF [RB1 RB2] n Hlt. unfold pclass_wf in WF. cbv zeta in WF.
  destruct WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & _).
  pose proof (class_size_pos c Hc) as Hcs. pose proof (max_count_range c Hc) as [Hmc _].
  assert (Hnf : 0 <= p_nf k) by (rewrite W1; lia).
  assert (Hn8 : n <= 8) by (unfold n; apply Z.div_le_upper_bound; lia).
  assert (Hpm : p_mu k <= pop_mu k c (n - p_nf k) /\ pop_mu k c (n - p_nf k) <= p_mu k + 8 * class_size c + K_MAP).
  { unfold pop_mu. cbv zeta. destruct (Z.leb_spec (p_au k + (n - p_nf k) * class_size c) (p_mu k)); [lia|].
    pose proof (rup_ge (p_au k + (n - p_nf k) * class_size c - p_mu k) K_MAP ltac:(lia)).
    pose proof (rup_lt (p_au k + (n - p_nf k) * class_size c - p_mu k) K_MAP ltac:(lia)).
    assert ((n - p_nf k) * class_size c <= 8 * class_size c) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  assert (Hpn : 0 <= pop_new k c (n - p_nf k) <= (p_mu k + 8 * class_size c + K_MAP - p_au k) / class_size c).
  { unfold pop_new. split; [apply Z.div_pos; lia| apply Z.div_le_mono; lia]. }
  repeat split; try lia; try assumption.
Qed.

#[using="BO SPACE_EQ SPACE_AL"] Lemma link_refill : forall v mo c k (Q : exc unit -> Model -> Prop),
  LINK Bs v mo -> 1 <= c <= 31 -> pclass_wf c k -> refill_budget c k ->
  vroom Bs v (D_gfa k c (max_count c / 2) + D_gfa k c (max_count c / 2) / 8 + 4 * page_size) ->
  (forall mo', LINK Bs (mkVA (va_prim v + D_gfa k c (max_count c / 2)) (va_chunks v) (va_nsec v) (va_aux v)) mo' ->
               m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo -> Q (Ok tt) mo') ->
  stwfL (t_refill AL c k) mo Q.
Proof.
  intros v mo c k Q LK Hc WF RB VR HQ. unfold t_refill. apply stwf_ebind.
  apply (link_gfa v mo c k (max_count c / 2) _ LK Hc).
  - intros Hlt. destruct (refill_budget_facts c k Hc WF RB Hlt) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
    repeat split; try assumption; lia.
  - intros mo' LK' F. unfold t_none. apply stwf_ret. exact (HQ mo' LK' F).
Qed.

Definition D_cdealloc (c : Z) (k : pclass) : Z := if p_cnt k =? max_count c then D_efa k (p_nf k + max_count c / 2) else 0.

#[using="BO SPACE_EQ SPACE_AL"] Lemma link_cdealloc : forall v mo c k (Q : exc unit -> Model -> Prop),
  LINK Bs v mo -> 1 <= c <= 31 -> pclass_wf c k -> drain_budget c k ->
  vroom Bs v (D_cdealloc c k + D_cdealloc c k / 8 + 2 * page_size) ->
  (forall mo', LINK Bs (mkVA (va_prim v + D_cdealloc c k) (va_chunks v) (va_nsec v) (va_aux v)) mo' ->
               m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo -> Q (Ok tt) mo') ->
  stwfL (t_cdealloc AL c k) mo Q.
Proof.
  intros v mo c k Q LK Hc WF DB VR HQ. unfold t_cdealloc, D_cdealloc in *. unfold pclass_wf in WF. cbv zeta in WF.
  destruct WF as (W1 & W2 & W3 & W4 & W5 & W6 & _). pose proof (max_count_range c Hc) as [Hmc _].
  destruct (Z.eqb_spec (p_cnt k) (max_count c)) as [Hfull|Hnot].
  - apply stwf_ebind. apply stwf_ebind.
    apply (link_efa v mo c k (p_nf k + max_count c / 2) _ LK Hc W5 W6).
    + rewrite W1. pose proof (Z.div_pos (max_count c) 2 ltac:(lia) ltac:(lia)). lia.
    + exact DB.
    + exact VR.
    + intros mo' LK' F. unfold t_none. apply stwf_ret. apply stwf_ret. exact (HQ mo' LK' F).
  - unfold t_none. apply stwf_ret. apply HQ; [| split; reflexivity].
    replace (va_prim v + 0) with (va_prim v) by lia. destruct v; exact LK.
Qed.

End P.
