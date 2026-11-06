(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0 AllocA0 ATacAp.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
Import ListNotations.
Open Scope Z_scope.

Section A.
Context {HC : HasCeiling}.
Variable FI : fs_if.
Variable AI : am_if FI.
Local Notation K := (am_K FI AI).
Local Notation BL := (list (block K)).
Hypothesis ASL : forall lo hi, am_static FI AI lo hi -> a0_static lo hi.
Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.

#[using="ASL"] Lemma static_low : forall lo hi, am_static FI AI lo hi -> 0x10000 <= lo /\ hi <= 0x10007fff8000.
Proof.
  intros lo hi H. apply ASL in H. destruct H as [LE H]. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  unfold sh, SHADOW_OFF in H. split; [| lia].
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]; lia.
Qed.

#[using="ASL"] Lemma static_cases : forall lo hi, am_static FI AI lo hi ->
  0x10000 <= lo /\ lo <= hi /\ (hi <= 0x609000 \/ (0x7fff7000 <= lo /\ hi <= 0x10007fff8000)).
Proof.
  intros lo hi H. apply ASL in H. destruct H as [LE H]. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  unfold sh, SHADOW_OFF in H.
  destruct H as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]]]]; (split; [lia|]); (split; [lia|]); first [left; lia | right; Z.div_mod_to_equations; lia].
Qed.

#[using="Type"] Lemma block_shadow_length : forall n, 0 <= n -> 8 * Z.of_nat (length (block_shadow n)) < n + 8.
Proof.
  intros n Hn. unfold block_shadow. rewrite length_app, repeat_length.
  pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
  destruct (Z.eqb_spec (n mod 8) 0); cbn [length]; rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia); lia.
Qed.

#[using="ASL"] Lemma aclient_not_stack : forall s LB0 (LB : BL) m0 q a,
  RHEAP_A FI AI s LB0 m0 -> (forall b, In b LB -> In b LB0) -> aclient FI AI LB q a -> alloc_ceiling <= a -> q <= a.
Proof.
  intros s LB0 LB m0 q a HR HSUB Hc Ha. pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (fsb_ok FI) as (F1 & F2 & _ & _).
  destruct Hc as [Hc|[(lo & hi & Hst & Hr)|[(b & Hb & Hr)|[Hr|[Hr|(b & Hb & Hr)]]]]].
  - exact Hc.
  - pose proof (static_low lo hi Hst). lia.
  - destruct (am_block_range FI AI s LB0 m0 b HR (HSUB b Hb)) as (_ & _ & _ & Hc' & _). lia.
  - lia.
  - unfold sh, SHADOW_OFF in Hr. Z.div_mod_to_equations. lia.
  - destruct (am_block_range FI AI s LB0 m0 b HR (HSUB b Hb)) as (B0 & _ & B2 & Hc' & _).
    pose proof (block_shadow_length (blk_size b) B2). unfold sh, SHADOW_OFF in Hr. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma apres_of_munch : forall (LB : BL) q W m m',
  munch W m m' -> wmono asegs m m' ->
  (forall a, 0 <= a < 2^64 -> aclient FI AI LB q a -> outside W a) ->
  apres FI AI LB q m m'.
Proof.
  intros LB q W m m' MU WM HO a Ha Hc. split.
  - apply gkeep_of_eq. unfold munch in MU. pose proof (MU (wa a)) as E. unfold wa in E. rewrite unsigned_lit in E by lia.
    unfold wa. apply E. apply HO; assumption.
  - intros Hw. apply WM. exact Hw.
Qed.

#[using="Type"] Lemma apres_weaken : forall (LB LB' : BL) q q' m m',
  apres FI AI LB q m m' -> q <= q' -> (forall b, In b LB' -> In b LB) -> apres FI AI LB' q' m m'.
Proof.
  intros LB LB' q q' m m' H HS HL a Ha Hc. apply H; [exact Ha|].
  destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|[Hc|[Hc|(b & Hb & Hr)]]]]].
  - left; lia.
  - right; left; exact Hc.
  - right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
  - do 3 right; left; exact Hc.
  - do 4 right; left; exact Hc.
  - do 5 right. exists b. split; [apply HL; exact Hb| exact Hr].
Qed.

Definition seg_okA (LB : BL) (q : Z) (W : list ivl) : Prop :=
  Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= q)
                    \/ (forall a, fst iv <= a < snd iv -> ~ aclient FI AI LB q a)) W.

#[using="Type"] Lemma outside_of_forall : forall W a, Forall (fun iv : ivl => ~ (fst iv <= a < snd iv)) W -> outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a H; cbn; [exact I|].
  inversion H as [|x l H1 H2]; subst. cbn in H1. split; [exact H1| apply IH; exact H2].
Qed.

#[using="ASL"] Lemma apres_seg : forall s LB0 (LB : BL) q W m0 m m',
  RHEAP_A FI AI s LB0 m0 -> (forall b, In b LB -> In b LB0) ->
  munch W m m' -> wmono asegs m m' -> seg_okA LB q W ->
  apres FI AI LB q m m'.
Proof.
  intros s LB0 LB q W m0 m m' HR HSUB MU WM OK.
  eapply apres_of_munch; [exact MU| exact WM|].
  intros a Ha Hc. apply outside_of_forall. unfold seg_okA in OK.
  eapply Forall_impl; [| exact OK]. cbn. intros [lo' hi'] [[H1 H2]|H3]; cbn in *.
  - intros Hr. pose proof (aclient_not_stack s LB0 LB m0 q a HR HSUB Hc ltac:(lia)). lia.
  - intros Hr. exact (H3 a Hr Hc).
Qed.

#[using="Type"] Lemma lb_remove_sub : forall k (LB : BL) b, In b (lb_remove (am_K_eqb FI AI) k LB) -> In b LB.
Proof.
  induction LB as [|b0 LB IH]; intros b H; [exact H|].
  unfold lb_remove in *. rewrite list.filter_cons in H. destruct (decide _) as [D|D].
  - destruct H as [->|H]; [left; reflexivity| right; apply IH; exact H].
  - right. apply IH. exact H.
Qed.
#[using="Type"] Lemma lb_remove_neq : forall k (LB : BL) b, In b (lb_remove (am_K_eqb FI AI) k LB) -> blk_id b <> k.
Proof.
  induction LB as [|b0 LB IH]; intros b H; [destruct H|].
  unfold lb_remove in *. rewrite list.filter_cons in H. destruct (decide _) as [D|D].
  - destruct H as [->|H]; [| apply IH; exact H].
    intros E. apply Is_true_true_1 in D. rewrite <- E in D.
    destruct (am_K_eqb FI AI (blk_id b) (blk_id b)) eqn:Q; [discriminate|].
    pose proof (proj2 (am_K_eqb_eq FI AI (blk_id b) (blk_id b)) eq_refl). congruence.
  - apply IH. exact H.
Qed.

#[using="ASL"] Lemma fresh_block_not_aclient : forall s LB' (LB : BL) (b : block K) q m a,
  RHEAP_A FI AI s LB' m -> In b LB' -> (forall b0, In b0 LB -> In b0 LB' /\ b0 <> b) ->
  alloc_ceiling <= q ->
  blk_addr b <= a < blk_addr b + blk_size b -> ~ aclient FI AI LB q a.
Proof.
  intros s LB' LB b q m a HR HIN HSUB HQ Hr Hc.
  destruct (am_block_range FI AI s LB' m b HR HIN) as (B0 & _ & B2 & B3 & B4 & B4d & B5).
  pose proof (fsb_ok FI) as (F1 & F2 & _ & _). pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  destruct Hc as [Hc|[(lo & hi & Hst & Hl)|[(b0 & Hb0 & Hr0)|[Hf|[Hf|(b0 & Hb0 & Hr0)]]]]].
  - lia.
  - pose proof (static_cases lo hi Hst). lia.
  - destruct (HSUB b0 Hb0) as [HIN0 NE].
    pose proof (am_blocks_disjoint FI AI s LB' m b0 b HR HIN0 HIN NE). lia.
  - lia.
  - unfold sh, SHADOW_OFF in Hf. Z.div_mod_to_equations. lia.
  - destruct (HSUB b0 Hb0) as [HIN0 _].
    destruct (am_block_range FI AI s LB' m b0 HR HIN0) as (C0 & _ & C2 & C3 & _).
    pose proof (block_shadow_length (blk_size b0) C2). unfold sh, SHADOW_OFF in Hr0. Z.div_mod_to_equations. lia.
Qed.

#[using="Type"] Lemma cons_old : forall s (LB : BL) (b : block K) m,
  RHEAP_A FI AI s (b :: LB) m -> forall b0, In b0 LB -> In b0 (b :: LB) /\ b0 <> b.
Proof.
  intros s LB b m HR b0 Hb0. split; [right; exact Hb0|]. intros ->.
  pose proof (am_blocks_nodup FI AI _ _ _ HR) as ND. cbn in ND. inversion ND as [|xk xl NI ND']; subst.
  apply NI. apply base.list_elem_of_In. exact (in_map blk_id _ _ Hb0).
Qed.

#[using="Type"] Lemma fresh_block_apart : forall s (LB : BL) (b b0 : block K) m A n,
  RHEAP_A FI AI s (b :: LB) m -> In b0 LB -> blk_addr b0 <= A -> A + n <= blk_addr b0 + blk_size b0 ->
  A + n <= blk_addr b \/ blk_addr b + blk_size b <= A.
Proof.
  intros s LB b b0 m A n HR HIN H1 H2. destruct (cons_old s LB b m HR b0 HIN) as [HIN' NE].
  pose proof (am_blocks_disjoint FI AI _ _ _ _ _ HR HIN' (or_introl eq_refl) NE) as D. lia.
Qed.

#[using="Type"] Lemma block_shadow_chunk : forall s (LB : BL) m k A n, RHEAP_A FI AI s LB m -> In (k, A, n) LB ->
  rw_cells asegs m (sh A) (shadow_cells (block_shadow n)).
Proof. intros s LB m k A n HR HIN. exact (am_block_shadow FI AI s LB m (k, A, n) HR HIN). Qed.

#[using="Type"] Lemma block_shw : forall s (LB : BL) m (b : block K) A n,
  RHEAP_A FI AI s LB m -> In b LB -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> 0 <= n -> shw m A n.
Proof.
  intros s LB m b A n HR HIN H1 H2 Hn.
  destruct (am_block_range FI AI s LB m b HR HIN) as (B0 & B1 & B2 & B3 & B4 & B4d & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  split; [| split].
  - eapply (accessible_of_block_shadow m (blk_addr b) (blk_size b)); [exact (am_block_shadow FI AI s LB m b HR HIN)| | exact B2| reflexivity| exact H1| exact H2].
    clear - B1. Z.div_mod_to_equations. lia.
  - eapply sh_readable_sub; [exact (am_block_shread FI AI s LB m b HR HIN)| exact H1| exact H2| exact Hn].
  - unfold win_ok. split; [exact Hn|]. lia.
Qed.

#[using="Type"] Lemma block_win_ok : forall s (LB : BL) m (b : block K),
  RHEAP_A FI AI s LB m -> In b LB -> win_ok (blk_addr b) (blk_size b + 16).
Proof.
  intros s LB m b HR HIN. destruct (am_block_range FI AI s LB m b HR HIN) as (B0 & B1 & B2 & B3 & B4 & B4d & _).
  apply win_ok_of_range; lia.
Qed.

Definition blk_iv (LB : BL) (iv : ivl) : Prop :=
  alloc_ceiling <= fst iv \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

#[using="Type"] Lemma rheap_blk_write : forall s (LB : BL) m m' W,
  RHEAP_A FI AI s LB m -> munch W m m' -> wmono asegs m m' -> Forall (blk_iv LB) W -> RHEAP_A FI AI s LB m'.
Proof.
  intros s LB m m' W HR MU WM HW. eapply (am_heap_frame FI AI); [exact HR| exact MU| exact WM|].
  eapply Forall_impl; [| exact HW]. intros iv [H|H]; [left; exact H| right; right; left; exact H].
Qed.

#[using="Type"] Lemma rfake_blk_write : forall s (LB : BL) st m m' W,
  RHEAP_A FI AI s LB m -> RFAKE FI st m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => blk_iv LB iv /\ fst iv <= snd iv) W -> RFAKE FI st m'.
Proof.
  intros s LB st m m' W HR RF MU WM HW. eapply (rfake_frame FI); [exact RF| exact MU| exact WM|].
  pose proof (fsb_ok FI) as (F1 & F2 & _ & _). pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  eapply Forall_impl; [| exact HW]. intros iv [[H|(b & Hb & H1 & H2)] LE]; left.
  - unfold sh, SHADOW_OFF. split; [right; lia|]. right. Z.div_mod_to_equations. lia.
  - destruct (am_block_range FI AI s LB m b HR Hb) as (B0 & _ & B2 & B3 & B4 & B4d & B5).
    unfold sh, SHADOW_OFF. split; [lia|]. destruct B4d; [left| right]; Z.div_mod_to_equations; lia.
Qed.

#[using="Type"] Lemma env_safe_blk : forall s (LB : BL) m W,
  RHEAP_A FI AI s LB m -> Forall (blk_iv LB) W -> env_safe W.
Proof.
  intros s LB m W HR HW. unfold env_safe. eapply Forall_impl; [| exact HW].
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  intros iv [H|(b & Hb & H1 & H2)]; left; [lia|].
  destruct (am_block_range FI AI s LB m b HR Hb) as (B0 & _ & B2 & B3 & B4 & B4d & _). lia.
Qed.

#[using="Type"] Lemma app_ivs_blk : forall s (LB : BL) m W,
  RHEAP_A FI AI s LB m -> Forall (blk_iv LB) W -> app_ivs W.
Proof.
  intros s LB m W HR HW. unfold app_ivs. eapply Forall_impl; [| exact HW].
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  intros iv [H|(b & Hb & H1 & H2)]; [right; unfold SH_HI; lia|].
  destruct (am_block_range FI AI s LB m b HR Hb) as (B0 & _ & B2 & B3 & B4 & B4d & _). unfold app_iv, SH_HI. lia.
Qed.

Definition apx (W : list ivl) (LB : BL) (q : Z) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> aclient FI AI LB q a -> outside W a ->
    gkeep m m' (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

#[using="Type"] Lemma apx_refl : forall W LB q m, apx W LB q m m.
Proof. intros W LB q m a _ _ _; split; [apply gkeep_refl| auto]. Qed.
#[using="Type"] Lemma apx_trans : forall W LB q m1 m2 m3, apx W LB q m1 m2 -> apx W LB q m2 m3 -> apx W LB q m1 m3.
Proof.
  intros W LB q m1 m2 m3 H1 H2 a Ha Hc Ho. destruct (H1 a Ha Hc Ho) as [E1 W1]. destruct (H2 a Ha Hc Ho) as [E2 W2].
  split; [exact (gkeep_trans _ _ _ _ E1 E2)| auto].
Qed.

#[using="Type"] Lemma apx_mrd : forall W LB q m m' a b, apx W LB q m m' -> 0 <= a < 2^64 -> aclient FI AI LB q a -> outside W a ->
  mrd asegs m (wa a) = Some b -> mrd asegs m' (wa a) = Some b.
Proof. intros W LB q m m' a b AP Ha Hc Ho Hr. exact (gkeep_mrd m m' (wa a) b (proj1 (AP a Ha Hc Ho)) Hr). Qed.
#[using="Type"] Lemma apx_of_apres : forall W LB q m m', apres FI AI LB q m m' -> apx W LB q m m'.
Proof. intros W LB q m m' H a Ha Hc _. apply H; assumption. Qed.
#[using="Type"] Lemma apres_of_apx : forall W LB q m m',
  apx W LB q m m' -> (forall a, 0 <= a < 2^64 -> aclient FI AI LB q a -> outside W a) -> apres FI AI LB q m m'.
Proof. intros W LB q m m' H HO a Ha Hc. apply H; auto. Qed.
#[using="Type"] Lemma aclient_weaken : forall (LB LB' : BL) q q' a,
  aclient FI AI LB' q' a -> q <= q' -> (forall b, In b LB' -> In b LB) -> aclient FI AI LB q a.
Proof.
  intros LB LB' q q' a Hc HS HL.
  destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|[Hc|[Hc|(b & Hb & Hr)]]]]].
  - left; lia.
  - right; left; exact Hc.
  - right; right; left. exists b. split; [apply HL; exact Hb| exact Hr].
  - do 3 right; left; exact Hc.
  - do 4 right; left; exact Hc.
  - do 5 right. exists b. split; [apply HL; exact Hb| exact Hr].
Qed.
#[using="Type"] Lemma apx_weaken : forall W W' (LB LB' : BL) q q' m m',
  apx W LB q m m' -> sub_fp W W' -> q <= q' -> (forall b, In b LB' -> In b LB) -> apx W' LB' q' m m'.
Proof.
  intros W W' LB LB' q q' m m' H HW HS HL a Ha Hc Ho. apply H; [exact Ha| | apply HW; exact Ho].
  eapply aclient_weaken; eauto.
Qed.

#[using="ASL"] Lemma apx_seg : forall s LB0 (LB : BL) q W W0 m0 m m',
  RHEAP_A FI AI s LB0 m0 -> (forall b, In b LB -> In b LB0) ->
  munch W0 m m' -> wmono asegs m m' ->
  Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= q)
                    \/ (forall a, fst iv <= a < snd iv -> ~ aclient FI AI LB q a)
                    \/ inside W (fst iv) (snd iv - fst iv)) W0 ->
  apx W LB q m m'.
Proof.
  intros s LB0 LB q W W0 m0 m m' HR HSUB MU WM OK a Ha Hc Ho. split; [| intros Hw; apply WM; exact Hw].
  apply gkeep_of_eq. unfold munch in MU. pose proof (MU (wa a)) as E. unfold wa in E. rewrite unsigned_lit in E by lia.
  unfold wa. apply E. apply outside_of_forall.
  eapply Forall_impl; [| exact OK]. cbn. intros [lo' hi'] [[H1 H2]|[H3|H4]]; cbn in *.
  - intros Hr. pose proof (aclient_not_stack s LB0 LB m0 q a HR HSUB Hc ltac:(lia)). lia.
  - intros Hr. exact (H3 a Hr Hc).
  - intros Hr. apply (inside_not_outside W lo' (hi' - lo') a H4); [lia| exact Ho].
Qed.

#[using="Type"] Lemma apx_bytes_at : forall W LB q m m' A bs,
  apx W LB q m m' -> bytes_at asegs m A bs -> aclient_range FI AI LB q A (Z.of_nat (length bs)) ->
  disjoint_from W A (Z.of_nat (length bs)) -> bytes_at asegs m' A bs.
Proof.
  intros W LB q m m' A bs HP HB HR HD. pose proof HB as (H0 & H1 & _). apply (bytes_at_gkeep m m' A bs HB). intros i Hi.
  exact (proj1 (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia) ltac:(eapply disjoint_outside; [exact HD| lia]))).
Qed.
#[using="Type"] Lemma apx_wr_at : forall W LB q m m' A n,
  apx W LB q m m' -> wr_at asegs m A n -> aclient_range FI AI LB q A n -> disjoint_from W A n -> wr_at asegs m' A n.
Proof.
  intros W LB q m m' A n HP (H0 & H1 & HW) HR HD. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia) ltac:(eapply disjoint_outside; [exact HD| lia])) as [_ Wv].
  apply Wv. apply HW. exact Hi.
Qed.
#[using="Type"] Lemma apx_rw_cells : forall W LB q m m' A cs,
  apx W LB q m m' -> rw_cells asegs m A cs -> aclient_range FI AI LB q A (Z.of_nat (cells_size cs)) ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof.
  intros W LB q m m' A cs HP [[Hwf HB] HW] HR HD. split; [split; [exact Hwf|]|].
  - eapply apx_bytes_at; eauto; rewrite cells_bytes_length by assumption; assumption.
  - eapply apx_wr_at; eauto.
Qed.

#[using="Type"] Lemma apx_drop : forall W (LB LB' : BL) q q' m m',
  apx W LB q m m' -> q <= q' -> (forall b, In b LB' -> In b LB) ->
  (forall a, 0 <= a < 2^64 -> aclient FI AI LB' q' a -> outside W a) -> apx [] LB' q' m m'.
Proof.
  intros W LB LB' q q' m m' H HS HL HO a Ha Hc _. apply H; [exact Ha| | apply HO; assumption].
  eapply aclient_weaken; eauto.
Qed.

Definition mblocA (LB : BL) (q : Z) (st : fsstate FI) (MB n : Z) : Prop :=
  (q <= MB /\ MB + n <= am_stack_top FI AI)
  \/ (exists b, In b LB /\ blk_addr b <= MB /\ MB + n <= blk_addr b + blk_size b)
  \/ lb (fs_live FI st) MB n.

#[using="Type"] Lemma mblocA_stack : forall LB q st MB n, q <= MB -> MB + n <= am_stack_top FI AI -> mblocA LB q st MB n.
Proof. intros; left; lia. Qed.
#[using="Type"] Lemma mblocA_block : forall LB q st MB n (b : block K),
  In b LB -> blk_addr b <= MB -> MB + n <= blk_addr b + blk_size b -> mblocA LB q st MB n.
Proof. intros LB q st MB n b H H1 H2. right; left. exists b. auto. Qed.
#[using="Type"] Lemma mblocA_fake : forall LB q st MB n, lb (fs_live FI st) MB n -> mblocA LB q st MB n.
Proof. intros; right; right; assumption. Qed.

#[using="Type"] Lemma mblocA_weaken : forall (LB LB' : BL) q q' st st' MB n,
  mblocA LB q st MB n -> q' <= q -> (forall b, In b LB -> In b LB') ->
  (forall g, In g (fs_live FI st) -> In g (fs_live FI st')) -> mblocA LB' q' st' MB n.
Proof.
  intros LB LB' q q' st st' MB n [H|[(b & Hb & H1 & H2)|H]] HS SUB SUBF; [left; lia| |].
  - right; left. exists b. split; [apply SUB; exact Hb| lia].
  - right; right. eapply lb_mono; [exact H| exact SUBF].
Qed.
#[using="Type"] Lemma mblocA_sub : forall (LB : BL) q st MB n MB' n',
  mblocA LB q st MB n -> MB <= MB' -> MB' + n' <= MB + n -> mblocA LB q st MB' n'.
Proof.
  intros LB q st MB n MB' n' [H|[(b & Hb & H1 & H2)|H]] L1 L2; [left; lia| |].
  - right; left. exists b. split; [exact Hb| lia].
  - right; right. eapply Contracts.lb_sub; [exact H| lia| lia].
Qed.

#[using="Type"] Lemma lb_geom : forall st m MB n, RFAKE FI st m -> lb (fs_live FI st) MB n ->
  FSB FI + A0_FS_FRAMES <= MB /\ MB + n <= FSB FI + A0_FS_SIZE.
Proof.
  intros st m MB n RF (g & Hg & G1 & G2). pose proof (live_wf FI st m RF) as WF.
  rewrite Forall_forall in WF. destruct (WF g Hg) as (_ & W1 & W2 & _). lia.
Qed.

#[using="Type"] Lemma mblocA_client : forall (LB : BL) q st m MB n, RFAKE FI st m -> mblocA LB q st MB n -> aclient_range FI AI LB q MB n.
Proof.
  intros LB q st m MB n RF [H|[(b & Hb & H1 & H2)|H]].
  - apply aclient_range_above. lia.
  - eapply aclient_range_block; [exact Hb| lia| lia].
  - destruct (lb_geom st m MB n RF H) as [G1 G2]. apply aclient_range_fs; lia.
Qed.

#[using="Type"] Lemma mblocA_range : forall s LB0 (LB : BL) q st m MB n,
  RHEAP_A FI AI s LB0 m -> (forall b, In b LB -> In b LB0) -> RFAKE FI st m -> mblocA LB q st MB n ->
  alloc_ceiling <= q -> 0 <= n ->
  0x609000 <= MB /\ (MB + n <= alloc_ceiling \/ q <= MB) /\ app_mem MB n.
Proof.
  intros s LB0 LB q st m MB n HR SUB RF ML HQ Hn.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (_ & _ & TK3 & _).
  destruct ML as [H|[(b & Hb & H1 & H2)|H]].
  - unfold app_mem. lia.
  - destruct (am_block_range FI AI _ _ _ _ HR (SUB b Hb)) as (B0 & _ & B2 & B3 & B4 & B4d & _). unfold app_mem. lia.
  - destruct (lb_geom st m MB n RF H) as [G1 G2]. pose proof (fsb_ok FI) as (F1 & F2 & F3 & _). unfold app_mem in *. lia.
Qed.

#[using="AMS"] Lemma mblocA_shadow_client : forall s LB0 (LB : BL) q st m MB n k,
  RHEAP_A FI AI s LB0 m -> (forall b, In b LB -> In b LB0) -> RFAKE FI st m -> mblocA LB q st MB n ->
  alloc_ceiling <= q -> MB mod 8 = 0 -> 0 <= k -> 8 * k <= n ->
  aclient_range FI AI LB q (sh MB) k.
Proof.
  intros s LB0 LB q st m MB n k HR SUB RF ML HQ AL Hk Hkn.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (_ & _ & TK3 & _).
  destruct ML as [H|[(b & Hb & H1 & H2)|H]].
  - eapply (aclient_range_static FI AI _ _ _ _ (sh alloc_ceiling - sh alloc_ceiling mod 8) 0x10007fff8000).
    + apply AMS. unfold a0_static. split; [unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia|]. repeat right. lia.
    + unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
    + unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
  - destruct (am_block_range FI AI _ _ _ _ HR (SUB b Hb)) as (B0 & B1 & B2 & B3 & B4 & B4d & _).
    eapply aclient_range_block_shadow; [exact Hb| |].
    + unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
    + unfold block_shadow. rewrite length_app, repeat_length.
      pose proof (Z.div_mod (blk_size b) 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (blk_size b) 8 ltac:(lia)) as MB8.
      assert (L : Z.of_nat (Z.to_nat (blk_size b / 8) + length (if blk_size b mod 8 =? 0 then [] else [blk_size b mod 8])) * 8 >= blk_size b).
      { rewrite Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia). destruct (Z.eqb_spec (blk_size b mod 8) 0); cbn [length Z.of_nat Pos.of_succ_nat]; lia. }
      unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
  - destruct (lb_geom st m MB n RF H) as [G1 G2]. pose proof (fsb_ok FI) as (F1 & F2 & F3 & F4).
    apply aclient_range_fs_shadow; unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia.
Qed.

#[using="Type"] Lemma mblocA_hf : forall LB0 (LB : BL) q st m MB n,
  RFAKE FI st m -> mblocA LB q st MB n -> alloc_ceiling <= q -> (forall b, In b LB -> In b LB0) ->
  alloc_ceiling <= fst (MB, MB + n)
  \/ (exists lo hi, am_static FI AI lo hi /\ lo <= fst (MB, MB + n) /\ snd (MB, MB + n) <= hi /\ a0_wsafe (fst (MB, MB + n)) (snd (MB, MB + n)))
  \/ (exists b, In b LB0 /\ blk_addr b <= fst (MB, MB + n) /\ snd (MB, MB + n) <= blk_addr b + blk_size b)
  \/ (FSB FI <= fst (MB, MB + n) /\ snd (MB, MB + n) <= FSB FI + A0_FS_SIZE)
  \/ (sh (FSB FI) <= fst (MB, MB + n) /\ snd (MB, MB + n) <= sh (FSB FI) + A0_FS_SHSIZE).
Proof.
  intros LB0 LB q st m MB n RF [H|[(b & Hb & H1 & H2)|H]] HQ SUB; cbn [fst snd].
  - left. lia.
  - right; right; left. exists b. split; [apply SUB; exact Hb| lia].
  - destruct (lb_geom st m MB n RF H) as [G1 G2]. do 3 right; left. lia.
Qed.
#[using="Type"] Lemma mblocA_rf : forall s LB0 (LB : BL) q st m MB n,
  RHEAP_A FI AI s LB0 m -> (forall b, In b LB -> In b LB0) -> mblocA LB q st MB n -> alloc_ceiling <= q -> 0 <= n ->
  ((snd (MB, MB + n) <= FSB FI \/ FSB FI + A0_FS_SIZE <= fst (MB, MB + n))
   /\ (snd (MB, MB + n) <= sh (FSB FI) \/ sh (FSB FI) + A0_FS_SHSIZE <= fst (MB, MB + n)))
  \/ lb (fs_live FI st) (fst (MB, MB + n)) (snd (MB, MB + n) - fst (MB, MB + n))
  \/ ls (fs_live FI st) (fst (MB, MB + n)) (snd (MB, MB + n) - fst (MB, MB + n)).
Proof.
  intros s LB0 LB q st m MB n HR SUB [H|[(b & Hb & H1 & H2)|H]] HQ Hn; cbn [fst snd].
  - left. pose proof (fsb_ok FI) as (F1 & F2 & _ & _). pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold sh, SHADOW_OFF. split; [right; lia|]. right. Z.div_mod_to_equations. lia.
  - left. destruct (am_block_range FI AI _ _ _ _ HR (SUB b Hb)) as (B0 & _ & B2 & B3 & B4 & B4d & B5).
    pose proof (fsb_ok FI) as (F1 & F2 & _ & _). pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    unfold sh, SHADOW_OFF. split; [lia|]. destruct B4d; [left| right]; Z.div_mod_to_equations; lia.
  - right; left. replace (MB + n - MB) with n by lia. exact H.
Qed.

#[using="Type"] Lemma mblocA_other_block : forall s LB0 (LB : BL) q st m MB n (b1 : block K),
  RHEAP_A FI AI s LB0 m -> (forall b, In b LB -> In b LB0 /\ b <> b1) -> In b1 LB0 -> RFAKE FI st m ->
  mblocA LB q st MB n -> alloc_ceiling <= q ->
  MB + n <= blk_addr b1 \/ blk_addr b1 + blk_size b1 <= MB.
Proof.
  intros s LB0 LB q st m MB n b1 HR SUB H1 RF [H|[(b & Hb & Q1 & Q2)|H]] HQ.
  - destruct (am_block_range FI AI _ _ _ _ HR H1) as (_ & _ & _ & R4 & _). right. lia.
  - destruct (SUB b Hb) as [Hb0 NE].
    destruct (am_blocks_disjoint FI AI _ _ _ _ _ HR Hb0 H1 NE); lia.
  - destruct (lb_geom st m MB n RF H) as [G1 G2].
    destruct (am_block_range FI AI _ _ _ _ HR H1) as (_ & _ & _ & _ & _ & _ & R6). lia.
Qed.

#[using="Type"] Lemma mrd_apres : forall (LB : BL) q m m' a v, apres FI AI LB q m m' -> 0 <= a < 2^64 -> aclient FI AI LB q a ->
  mrd asegs m (wa a) = Some v -> mrd asegs m' (wa a) = Some v.
Proof. intros LB q m m' a v AP Ha Hc Hv. exact (apres_mrd FI AI LB q m m' a v AP Ha Hc Hv). Qed.

#[using="Type"] Lemma shw_apres_band : forall (LB : BL) q m m' A n lo hi,
  shw m A n -> apres FI AI LB q m m' ->
  (forall a, lo <= a < hi -> aclient FI AI LB q a) -> 0 <= lo -> hi <= 2^64 -> lo mod 8 = 0 -> hi mod 8 = 0 ->
  lo <= sh A -> (0 < n -> sh (A + n - 1) < hi) ->
  shw m' A n.
Proof.
  intros LB q m m' A n lo hi (AC & RD & WK) AP HB L0 H64 LAL HAL H1 H2. split; [| split; [| exact WK]].
  - intros a Ha. destruct (AC a Ha) as (k & BA & Hk). exists k. split; [| exact Hk].
    eapply (apres_bytes_at FI AI); [exact AP| exact BA|]. cbn [length Z.of_nat Pos.of_succ_nat]. intros x Hx. apply HB.
    assert (sh A <= sh a) by (apply sh_mono; lia). assert (sh a <= sh (A + n - 1)) by (apply sh_mono; lia). specialize (H2 ltac:(lia)). lia.
  - intros Hn a Ha. destruct (RD Hn a Ha) as (v & Hv). exists v. apply (mrd_apres LB q m m' a v AP); [| | exact Hv].
    + specialize (H2 Hn). Z.div_mod_to_equations. lia.
    + apply HB. specialize (H2 Hn). Z.div_mod_to_equations. lia.
Qed.

#[using="AMS"] Lemma mblocA_shw_apres : forall s' LB' (LB : BL) q st m m' MB n,
  mblocA LB q st MB n -> shw m MB n -> apres FI AI LB q m m' -> RFAKE FI st m ->
  RHEAP_A FI AI s' LB' m' -> (forall b, In b LB -> In b LB') -> alloc_ceiling <= q ->
  shw m' MB n.
Proof.
  intros s' LB' LB q st m m' MB n ML SW AP RF HR SUB HQ.
  pose proof (shw_win_ok _ _ _ SW) as [Hn _].
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  pose proof (am_stack_ok FI AI) as (_ & _ & TK3 & _).
  destruct ML as [H|[(b & Hb & H1 & H2)|H]].
  -
    pose proof (Z.mod_pos_bound (sh alloc_ceiling) 8 ltac:(lia)) as M8.
    assert (SC : 0x7fff8000 <= sh alloc_ceiling) by (unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia).
    eapply (shw_apres_band LB q m m' MB n (sh alloc_ceiling - sh alloc_ceiling mod 8) 0x10007fff8000 SW AP).
    + intros a Ha. right; left. exists (sh alloc_ceiling - sh alloc_ceiling mod 8), 0x10007fff8000. split; [| lia].
      apply AMS. unfold a0_static. split; [unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia|]. repeat right. lia.
    + lia.
    + lia.
    + clear. Z.div_mod_to_equations. lia.
    + reflexivity.
    + assert (sh alloc_ceiling <= sh MB) by (apply sh_mono; lia). lia.
    + intros Hp. unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
  - eapply (block_shw s' LB' m' b MB n HR (SUB b Hb)); lia.
  - destruct (lb_geom st m MB n RF H) as [G1 G2]. pose proof (fsb_ok FI) as (F1 & F2 & F3 & F4).
    eapply (shw_apres_band LB q m m' MB n (sh (FSB FI)) (sh (FSB FI) + A0_FS_SHSIZE) SW AP).
    + intros a Ha. do 4 right; left. exact Ha.
    + unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
    + unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
    + unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
    + unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
    + apply sh_mono. lia.
    + intros Hp. unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

Definition rf_ok (st : fsstate FI) (iv : ivl) : Prop :=
  ((snd iv <= FSB FI \/ FSB FI + A0_FS_SIZE <= fst iv) /\ (snd iv <= sh (FSB FI) \/ sh (FSB FI) + A0_FS_SHSIZE <= fst iv))
  \/ lb (fs_live FI st) (fst iv) (snd iv - fst iv) \/ ls (fs_live FI st) (fst iv) (snd iv - fst iv).
#[using="Type"] Lemma rf_ok_stack : forall st lo' hi', alloc_ceiling <= lo' -> rf_ok st (lo', hi').
Proof.
  intros st lo' hi' H. left. cbn [fst snd]. pose proof (fsb_ok FI) as (F1 & F2 & _ & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  unfold sh, SHADOW_OFF. split; [right; lia|]. right. Z.div_mod_to_equations. lia.
Qed.
#[using="Type"] Lemma rf_ok_blk : forall s (LB : BL) m st (b : block K) lo' hi',
  RHEAP_A FI AI s LB m -> In b LB -> blk_addr b <= lo' -> hi' <= blk_addr b + blk_size b -> lo' <= hi' -> rf_ok st (lo', hi').
Proof.
  intros s LB m st b lo' hi' HR Hb H1 H2 H3. left. cbn [fst snd].
  destruct (am_block_range FI AI s LB m b HR Hb) as (B0 & _ & B2 & B3 & B4 & B4d & B5).
  pose proof (fsb_ok FI) as (F1 & F2 & _ & _). pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  unfold sh, SHADOW_OFF. split; [lia|]. destruct B4d; [left| right]; Z.div_mod_to_equations; lia.
Qed.
#[using="Type"] Lemma rf_ok_mbloc : forall s LB0 (LB : BL) q st m MB n,
  RHEAP_A FI AI s LB0 m -> (forall b, In b LB -> In b LB0) -> mblocA LB q st MB n -> alloc_ceiling <= q -> 0 <= n -> rf_ok st (MB, MB + n).
Proof. intros. unfold rf_ok. eapply mblocA_rf; eauto. Qed.

Definition msrcA (LB : BL) (q : Z) (st : fsstate FI) (SRC n : Z) : Prop :=
  mblocA LB q st SRC n
  \/ (0x10000 <= SRC /\ SRC + n <= 0x609000 /\ exists lo hi, am_static FI AI lo hi /\ lo <= SRC /\ SRC + n <= hi).

#[using="Type"] Lemma msrcA_weaken : forall (LB LB' : BL) q q' st st' SRC n,
  msrcA LB q st SRC n -> q' <= q -> (forall b, In b LB -> In b LB') ->
  (forall g, In g (fs_live FI st) -> In g (fs_live FI st')) -> msrcA LB' q' st' SRC n.
Proof. intros LB LB' q q' st st' SRC n [H|H] HS SUB SUBF; [left; eapply mblocA_weaken; eauto| right; exact H]. Qed.

#[using="Type"] Lemma msrcA_client : forall (LB : BL) q st m SRC n, RFAKE FI st m -> msrcA LB q st SRC n -> aclient_range FI AI LB q SRC n.
Proof.
  intros LB q st m SRC n RF [H|(H1 & H2 & lo & hi & HS & L1 & L2)]; [eapply mblocA_client; eauto|].
  eapply aclient_range_static; eauto.
Qed.

#[using="Type"] Lemma msrcA_lo : forall s LB0 (LB : BL) q st m SRC n,
  RHEAP_A FI AI s LB0 m -> (forall b, In b LB -> In b LB0) -> RFAKE FI st m -> msrcA LB q st SRC n ->
  alloc_ceiling <= q -> 0 <= n -> 4096 <= SRC /\ (SRC + n <= alloc_ceiling \/ q <= SRC) /\ SRC + n <= 2^47.
Proof.
  intros s LB0 LB q st m SRC n HR SUB RF [H|(H1 & H2 & _)] HQ Hn.
  - destruct (mblocA_range s LB0 LB q st m SRC n HR SUB RF H HQ Hn) as (A1 & A2 & A3). unfold app_mem in A3. lia.
  - pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR. lia.
Qed.

#[using="Type"] Lemma msrcA_other_block : forall s LB0 (LB : BL) q st m SRC n (b1 : block K),
  RHEAP_A FI AI s LB0 m -> (forall b, In b LB -> In b LB0 /\ b <> b1) -> In b1 LB0 -> RFAKE FI st m ->
  msrcA LB q st SRC n -> alloc_ceiling <= q ->
  SRC + n <= blk_addr b1 \/ blk_addr b1 + blk_size b1 <= SRC.
Proof.
  intros s LB0 LB q st m SRC n b1 HR SUB H1 RF [H|(L1 & L2 & _)] HQ.
  - eapply mblocA_other_block; eauto.
  - destruct (am_block_range FI AI _ _ _ _ HR H1) as (_ & _ & _ & _ & R5 & R5d & _). left. lia.
Qed.

#[using="AMS"] Lemma msrcA_shw_apres : forall s' LB' (LB : BL) q st m m' SRC n,
  msrcA LB q st SRC n -> shw m SRC n -> apres FI AI LB q m m' -> RFAKE FI st m ->
  RHEAP_A FI AI s' LB' m' -> (forall b, In b LB -> In b LB') -> alloc_ceiling <= q ->
  shw m' SRC n.
Proof.
  intros s' LB' LB q st m m' SRC n [H|(L1 & L2 & _)] SW AP RF HR SUB HQ; [eapply mblocA_shw_apres; eauto|].
  pose proof (shw_win_ok _ _ _ SW) as [Hn _].
  eapply (shw_apres_band LB q m m' SRC n 0x7fffa000 0x800b9200 SW AP).
  - intros a Ha. right; left. exists 0x7fffa000, 0x800b9200. split; [| lia].
    apply AMS. unfold a0_static. split; [lia|]. lia.
  - lia.
  - lia.
  - reflexivity.
  - reflexivity.
  - unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
  - intros Hp. unfold sh, SHADOW_OFF. Z.div_mod_to_equations. lia.
Qed.

Definition lb_keepA (ok : option K) (LB : BL) : BL :=
  match ok with None => LB | Some k => lb_remove (am_K_eqb FI AI) k LB end.
#[using="Type"] Lemma lb_keepA_sub : forall ok LB b, In b (lb_keepA ok LB) -> In b LB.
Proof. intros [k|] LB b H; cbn in H; [eapply lb_remove_sub; exact H| exact H]. Qed.

#[using="Type"] Lemma lb_bytes_remove_le : forall k (LB : BL), (forall b, In b LB -> 0 <= blk_size b) ->
  lb_bytes FI AI (lb_remove (am_K_eqb FI AI) k LB) <= lb_bytes FI AI LB /\ (length (lb_remove (am_K_eqb FI AI) k LB) <= length LB)%nat.
Proof.
  induction LB as [|b0 LB IH]; intros HP; [cbn; lia|].
  unfold lb_remove in *. rewrite list.filter_cons. specialize (IH ltac:(intros b Hb; apply HP; right; exact Hb)).
  pose proof (HP b0 (or_introl eq_refl)). destruct (decide _) as [D|D]; cbn [lb_bytes fold_right length] in *; unfold lb_bytes in *; lia.
Qed.

Definition am_budget_le (s : aps FI AI) (LB : BL) (n : Z) : Prop := forall n', 0 <= n' <= n -> am_budget FI AI s LB n'.
#[using="Type"] Lemma am_budget_le_mono : forall s (LB : BL) n n', am_budget_le s LB n -> n' <= n -> am_budget_le s LB n'.
Proof. intros s LB n n' H Hn k Hk. apply H. lia. Qed.
#[using="Type"] Lemma am_budget_le_at : forall s (LB : BL) n n', am_budget_le s LB n -> 0 <= n' <= n -> am_budget FI AI s LB n'.
Proof. intros s LB n n' H Hn. apply H. exact Hn. Qed.

Definition nsec1 (n : Z) : Z := if a0_cls n =? 0 then 1 else 0.
#[using="Type"] Lemma nsec1_range : forall n, 0 <= nsec1 n <= 1.
Proof. intros n. unfold nsec1. destruct (a0_cls n =? 0); lia. Qed.

Variable J : a0_judg FI AI.
Variable AC : am_contracts FI AI J.

Definition orealloc_post_A (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32)
    (st : fsstate FI) (s : aps FI AI) (LB : BL) (ok : option K) (sz n lo : Z) (old : list byte) (m : mem) : aps FI AI -> BL -> machine_state -> Prop :=
  fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (k' : K) (A' : Z) (junk : list byte),
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz A') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ alloc_frame_A FI AI q lo st m m' (lb_keepA ok LB)
    /\ LB' = (k', A', n) :: lb_keepA ok LB /\ RHEAP_A FI AI s' LB' m'
    /\ rw_cells asegs m' A' [CB (Z.to_nat n) (firstn (Z.to_nat (Z.min n sz)) old ++ junk)]
    /\ am_nsec FI AI s' = am_nsec FI AI s + nsec1 n.

#[using="AC"] Lemma orealloc_spec_A : forall (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (LB : BL) (st : fsstate FI) (ok : option K) (A sz n lo : Z)
    (old : list byte) (ras : list Z),
  RHEAP_A FI AI s LB m ->
  match ok with None => A = 0 /\ sz = 0 /\ old = [] | Some k => In (k, A, sz) LB /\ rw_cells asegs m A [CB (Z.to_nat sz) old] end ->
  asan_env asegs m -> RFAKE FI st m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q mod 16 = 0 -> q + 16 < am_stack_top FI AI ->
  mem_inv asegs m ->
  fpchain m (am_stack_top FI AI) q (bv_unsigned s0) ras -> In (PC0_REALLOC :: bv_unsigned ra :: ras) A0_TRACES ->
  a0 = wz A -> a1 = wz n -> 0 < n <= A0_MAXREQ -> am_budget FI AI s LB n ->
  AJ FI AI J (orealloc_post_A ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s LB ok sz n lo old m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz A0_realloc) fc None m (seg_rom asegs))
    s LB.
Proof.
  intros until ras. intros HR OK AE RF ST CLO LO QAL QTOP MI FP TR -> -> HN BUD.
  destruct ok as [k|].
  - destruct OK as [HIN BLK].
    eapply (aj_mono FI AI J). { eapply (ac_realloc FI AI J AC); eauto. }
    intros s' LB' ms' P. unfold realloc_post_A in P. unfold orealloc_post_A.
    destruct P as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & k' & B & junk & E & AF & EL & HR' & BLK' & _ & NS).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', k', B, junk. cbn [lb_keepA]. unfold nsec1. auto 7.
  - destruct OK as (-> & -> & ->).
    eapply (aj_mono FI AI J). { eapply (ac_realloc_null FI AI J AC); eauto; lia. }
    intros s' LB' ms' P. unfold malloc_post_A in P. unfold orealloc_post_A.
    destruct P as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & k' & B & junk & E & AF & EL & HR' & BLK' & _ & _ & NS).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', k', B, junk. cbn [lb_keepA].
    rewrite Z.min_r by lia. cbn [Z.to_nat firstn app]. unfold nsec1. auto 7.
Qed.
End A.
