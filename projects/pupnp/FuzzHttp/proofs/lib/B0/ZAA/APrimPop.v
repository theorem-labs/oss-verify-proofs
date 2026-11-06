(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import APrim APrimLem ACells.
Import ListNotations.
Open Scope Z_scope.

Lemma carve_length : forall au sz n, length (carve au sz n) = n.
Proof. intros. unfold carve. rewrite length_rev, length_map, length_seq. reflexivity. Qed.

Lemma in_carve : forall au sz n v, In v (carve au sz n) <-> exists i, (i < n)%nat /\ v = (au + Z.of_nat i * sz) / 16.
Proof.
  intros au sz n v. unfold carve. rewrite <- in_rev, in_map_iff. split.
  - intros (i & E & Hi). apply in_seq in Hi. exists i. split; [lia| symmetry; exact E].
  - intros (i & Hi & E). exists i. split; [symmetry; exact E| apply in_seq; lia].
Qed.

Lemma carve_NoDup : forall au sz n, 16 <= sz -> au mod 16 = 0 -> sz mod 16 = 0 -> List.NoDup (carve au sz n).
Proof.
  intros au sz n SZ A16 S16. unfold carve. apply NoDup_rev. apply Finite.Injective_map_NoDup; [| apply seq_NoDup].
  intros i j E. Z.div_mod_to_equations. nia.
Qed.

Section W.
Variables (c r : Z) (k : pclass).
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hr : 1 <= r <= 8.
Hypothesis WF : pclass_wf c k.

Hypothesis BUD1 : p_mu k + r * class_size c + K_MAP <= FA_OFF.
Hypothesis BUD2 : 4 * (p_nf k + (p_mu k + r * class_size c + K_MAP - p_au k) / class_size c) + K_MAP <= K_FA_SIZE.

Notation SZ := (class_size c).
Notation total := (p_au k + r * class_size c).
Notation mu' := (pop_mu k c r).
Notation newc := (pop_new k c r).

#[using="k Hc Hr"] Lemma SZ_facts : 32 <= SZ <= 65536 /\ SZ mod 16 = 0 /\ SZ <= r * SZ /\ r * SZ <= 8 * SZ.
Proof.
  pose proof (class_size_pos c Hc) as CS. pose proof (class_size_mod16 c Hc) as CS16.
  split; [exact CS|]. split; [exact CS16|]. split.
  - rewrite <- (Z.mul_1_l SZ) at 1. apply Z.mul_le_mono_nonneg_r; lia.
  - apply Z.mul_le_mono_nonneg_r; lia.
Qed.

#[using="Hc Hr WF BUD1"] Lemma pop_mu_facts : p_mu k <= mu' /\ total <= mu' /\ mu' < total + K_MAP /\ mu' mod K_MAP = 0 /\ mu' <= FA_OFF
  /\ (total <= p_mu k -> mu' = p_mu k) /\ (p_mu k < total -> mu' = p_mu k + rup (total - p_mu k) K_MAP).
Proof.
  pose proof SZ_facts as (CS & CS16 & RS & RS8). unfold pclass_wf in WF.
  destruct WF as (_ & _ & _ & _ & _ & _ & AU & MUF & MUM & _ & GAP & _).
  unfold pop_mu. destruct (Z.leb_spec total (p_mu k)) as [LE|GT]; cbv beta iota.
  - repeat split; try lia. all: intros; lia.
  - pose proof (rup_ge (total - p_mu k) K_MAP ltac:(lia)). pose proof (rup_lt (total - p_mu k) K_MAP ltac:(lia)).
    pose proof (rup_mod (total - p_mu k) K_MAP ltac:(lia)).
    repeat split; try lia. all: intros; lia.
Qed.

#[using="Hc Hr WF BUD1"] Lemma pop_new_facts : 0 <= newc /\ SZ * newc <= mu' - p_au k /\ mu' - p_au k < SZ * newc + SZ /\ newc <= (p_mu k + r * SZ + K_MAP - p_au k) / SZ.
Proof.
  pose proof SZ_facts as (CS & CS16 & RS & RS8). pose proof pop_mu_facts as (M1 & M2 & M3 & M4 & M5 & _).
  unfold pclass_wf in WF. destruct WF as (_ & _ & _ & _ & _ & _ & AU & _).
  unfold pop_new. pose proof (Z.div_mod (mu' - p_au k) SZ ltac:(lia)) as DM. pose proof (Z.mod_pos_bound (mu' - p_au k) SZ ltac:(lia)) as MB.
  split; [apply Z.div_pos; lia|]. split; [lia|]. split; [lia|]. apply Z.div_le_mono; lia.
Qed.

#[using="Type"] Lemma populate_shape :
  p_nf (populate k c r) = p_nf k + newc /\ p_au (populate k c r) = p_au k + newc * SZ /\ p_mu (populate k c r) = mu'
  /\ p_fa (populate k c r) = p_fa k ++ carve (p_au k) SZ (Z.to_nat newc) /\ p_cnt (populate k c r) = p_cnt k /\ p_chunks (populate k c r) = p_chunks k
  /\ p_nalloc (populate k c r) = p_nalloc k /\ p_nfreed (populate k c r) = p_nfreed k
  /\ p_mfa (populate k c r) = efa_new (mkPCL (p_nf k) (p_mfa k) (p_au k) mu' (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k)) (p_nf k + newc).
Proof. unfold populate. cbn. repeat split; reflexivity. Qed.

#[using="c r k"] Lemma efa_new_facts : forall k1 t, 0 <= p_mfa k1 -> p_mfa k1 mod K_MAP = 0 -> 0 <= t -> 4 * t + K_MAP <= K_FA_SIZE ->
  4 * t <= efa_new k1 t /\ p_mfa k1 <= efa_new k1 t /\ efa_new k1 t mod K_MAP = 0 /\ efa_new k1 t <= Z.max (p_mfa k1) K_FA_SIZE.
Proof.
  intros k1 t M0 MM T0 TB. unfold efa_new. destruct (Z.leb_spec (4 * t) (p_mfa k1)) as [LE|GT]; cbv beta iota.
  - repeat split; lia.
  - pose proof (rup_ge (4 * t) K_MAP ltac:(lia)). pose proof (rup_mod (4 * t) K_MAP ltac:(lia)).
    pose proof (rup_le (4 * t) K_FA_SIZE K_MAP ltac:(lia) ltac:(lia) ltac:(reflexivity)). repeat split; lia.
Qed.

#[using="c r k"] Lemma divide16 : forall a b, a mod 16 = 0 -> b mod 16 = 0 -> (a + b) mod 16 = 0.
Proof. intros a b Ha Hb. rewrite Z.add_mod, Ha, Hb by lia. reflexivity. Qed.
#[using="c r k"] Lemma mul_mod16 : forall a b, b mod 16 = 0 -> (a * b) mod 16 = 0.
Proof. intros a b Hb. rewrite Z.mul_mod, Hb, Z.mul_0_r by lia. reflexivity. Qed.
#[using="c r Hc Hr WF"] Lemma au_mod16 : p_au k mod 16 = 0.
Proof.
  pose proof SZ_facts as (CS & CS16 & _). unfold pclass_wf in WF. destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & AUS & _).
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ SZ); apply Z.mod_divide; lia.
Qed.
#[using="r Hc Hr WF"] Lemma carve_val : forall i : nat, 16 * ((p_au k + Z.of_nat i * SZ) / 16) = p_au k + Z.of_nat i * SZ.
Proof.
  intros i. pose proof SZ_facts as (CS & CS16 & _). pose proof au_mod16 as A16.
  pose proof (divide16 _ _ A16 (mul_mod16 (Z.of_nat i) SZ CS16)) as D. Z.div_mod_to_equations. lia.
Qed.

#[using="Hc Hr WF BUD1 BUD2"] Lemma populate_wf : pclass_wf c (populate k c r).
Proof.
  pose proof SZ_facts as (CS & CS16 & RS & RS8).
  pose proof pop_mu_facts as (M1 & M2 & M3 & M4 & M5 & _). pose proof pop_new_facts as (N0 & N1 & N2 & N3).
  pose proof populate_shape as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
  pose proof au_mod16 as AU16.
  pose proof WF as WF0. unfold pclass_wf in WF0.
  destruct WF0 as (Lnf & Lcnt & CNT & NF4 & MFA & MFAM & AU & MUF & MUM & AUS & GAP & ND & FB & NA & NFR).
  pose proof (efa_new_facts (mkPCL (p_nf k) (p_mfa k) (p_au k) mu' (p_nalloc k) (p_nfreed k) (p_fa k) (p_cnt k) (p_chunks k))
                (p_nf k + newc) ltac:(cbn; lia) ltac:(cbn; exact MFAM) ltac:(lia) ltac:(lia)) as (F1 & F2 & F3 & F4). cbn [p_mfa] in F1, F2, F3, F4.
  unfold pclass_wf. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9.
  split. { rewrite length_app, carve_length, Nat2Z.inj_add, Z2Nat.id by lia. lia. }
  split; [exact Lcnt|]. split; [exact CNT|].
  split; [lia|]. split; [lia|]. split; [exact F3|].
  split; [lia|]. split; [lia|]. split; [exact M4|].
  split. { rewrite Z.add_mod, AUS, Z.mod_mul by lia. apply Z.mod_0_l. lia. }
  split; [lia|].
  split.
  {
    apply NoDup_ListNoDup. apply NoDup_ListNoDup in ND.
    apply (Permutation_NoDup (l := carve (p_au k) SZ (Z.to_nat newc) ++ (p_fa k ++ p_chunks k))).
    { rewrite <- app_assoc. apply Permutation_app_swap_app. }
    apply NoDup_app; [apply carve_NoDup; lia| exact ND|].
    intros v Hv Hin. apply in_carve in Hv. destruct Hv as (i & Hi & Ev).
    rewrite List.Forall_forall in FB. specialize (FB v Hin). pose proof (carve_val i) as CV. rewrite <- Ev in CV.
    assert (0 <= Z.of_nat i * SZ) by (apply Z.mul_nonneg_nonneg; lia). lia. }
  split.
  { apply Forall_app. split; [apply Forall_app; split|].
    - eapply Forall_impl; [| apply (proj1 (proj1 (Forall_app _ _ _) FB))]. cbn beta. intros v Hv. lia.
    - apply List.Forall_forall. intros v Hv. apply in_carve in Hv. destruct Hv as (i & Hi & Ev). pose proof (carve_val i) as CV. rewrite <- Ev in CV.
      assert (0 <= Z.of_nat i * SZ) by (apply Z.mul_nonneg_nonneg; lia).
      pose proof (Z.mul_le_mono_nonneg_r (Z.of_nat i + 1) newc SZ ltac:(lia) ltac:(lia)) as UP.
      split; [lia|]. split; [lia|]. rewrite CV, Z.add_mod, AUS, Z.mod_mul by lia. apply Z.mod_0_l. lia.
    - eapply Forall_impl; [| apply (proj2 (proj1 (Forall_app _ _ _) FB))]. cbn beta. intros v Hv. lia. }
  split; [exact NA| exact NFR].
Qed.
End W.

Section TILES.
Context {HC : HasCeiling}.

#[using="Type"] Lemma CB_wf_len : forall m A n bs, rw_cells asegs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[W _] _]. cbn in W. tauto. Qed.

#[using="Type"] Lemma CB_split2 : forall m A (n1 n2 : nat) bs, rw_cells asegs m A [CB (n1 + n2) bs] ->
  rw_cells asegs m A [CB n1 (firstn n1 bs)] /\ rw_cells asegs m (A + Z.of_nat n1) [CB n2 (skipn n1 bs)].
Proof.
  intros m A n1 n2 bs H. pose proof (CB_wf_len _ _ _ _ H) as L.
  assert (H2 : rw_cells asegs m A ([CB n1 (firstn n1 bs)] ++ [CB n2 (skipn n1 bs)])).
  { eapply rw_cells_rebytes; [exact H| | |].
    - cbn. rewrite length_firstn, length_skipn. repeat split; lia.
    - cbn. rewrite !app_nil_r. apply firstn_skipn.
    - cbn. lia. }
  apply rw_cells_app in H2. cbn [cells_size csize Nat.add] in H2. rewrite Nat.add_0_r in H2. exact H2.
Qed.

#[using="Type"] Lemma CB_join2 : forall m A (n1 n2 : nat) b1 b2, rw_cells asegs m A [CB n1 b1] -> rw_cells asegs m (A + Z.of_nat n1) [CB n2 b2] ->
  rw_cells asegs m A [CB (n1 + n2) (b1 ++ b2)].
Proof.
  intros m A n1 n2 b1 b2 H1 H2. pose proof (CB_wf_len _ _ _ _ H1) as L1. pose proof (CB_wf_len _ _ _ _ H2) as L2.
  assert (H : rw_cells asegs m A ([CB n1 b1] ++ [CB n2 b2])).
  { apply rw_cells_app. split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H2. }
  eapply rw_cells_rebytes; [exact H| | |].
  - cbn. rewrite length_app. split; [lia| exact I].
  - cbn. rewrite !app_nil_r. reflexivity.
  - cbn. lia.
Qed.

#[using="Type"] Lemma CB_tiles : forall m (cnt s : nat) A (rest : nat) bs,
  rw_cells asegs m A [CB (cnt * s + rest) bs] ->
  (forall i, (i < cnt)%nat -> exists j, rw_cells asegs m (A + Z.of_nat i * Z.of_nat s) [CB s j])
  /\ (exists j, rw_cells asegs m (A + Z.of_nat cnt * Z.of_nat s) [CB rest j]).
Proof.
  intros m cnt. induction cnt as [|cnt IH]; intros s A rest bs H.
  - split; [intros i Hi; lia|]. exists bs. replace (A + Z.of_nat 0 * Z.of_nat s) with A by lia. exact H.
  - replace (S cnt * s + rest)%nat with (s + (cnt * s + rest))%nat in H by lia.
    destruct (CB_split2 _ _ _ _ _ H) as [H1 H2].
    destruct (IH s (A + Z.of_nat s) rest (skipn s bs) H2) as [T R].
    split.
    + intros i Hi. destruct i as [|i].
      * exists (firstn s bs). replace (A + Z.of_nat 0 * Z.of_nat s) with A by lia. exact H1.
      * destruct (T i ltac:(lia)) as [j Hj]. exists j.
        replace (A + Z.of_nat (S i) * Z.of_nat s) with (A + Z.of_nat s + Z.of_nat i * Z.of_nat s) by lia. exact Hj.
    + destruct R as [j Hj]. exists j. replace (A + Z.of_nat (S cnt) * Z.of_nat s) with (A + Z.of_nat s + Z.of_nat cnt * Z.of_nat s) by lia. exact Hj.
Qed.

#[using="Type"] Lemma firstn_repeat : forall {X} (b : X) n m, (n <= m)%nat -> firstn n (repeat b m) = repeat b n.
Proof. intros X b n. induction n as [|n IH]; intros m Hm; [reflexivity|]. destruct m; [lia|]. cbn. f_equal. apply IH. lia. Qed.
#[using="Type"] Lemma skipn_repeat : forall {X} (b : X) n m, skipn n (repeat b m) = repeat b (m - n).
Proof. intros X b n. induction n as [|n IH]; intros m; [cbn; rewrite Nat.sub_0_r; reflexivity|]. destruct m; [reflexivity|]. cbn. apply IH. Qed.

#[using="Type"] Lemma CB_tiles_repeat : forall m (cnt s : nat) A (rest : nat) b,
  rw_cells asegs m A [CB (cnt * s + rest) (repeat b (cnt * s + rest))] ->
  (forall i, (i < cnt)%nat -> rw_cells asegs m (A + Z.of_nat i * Z.of_nat s) [CB s (repeat b s)])
  /\ rw_cells asegs m (A + Z.of_nat cnt * Z.of_nat s) [CB rest (repeat b rest)].
Proof.
  intros m cnt. induction cnt as [|cnt IH]; intros s A rest b H.
  - split; [intros i Hi; lia|]. replace (A + Z.of_nat 0 * Z.of_nat s) with A by lia. exact H.
  - replace (S cnt * s + rest)%nat with (s + (cnt * s + rest))%nat in H by lia.
    destruct (CB_split2 _ _ _ _ _ H) as [H1 H2].
    rewrite firstn_repeat in H1 by lia. rewrite skipn_repeat in H2. replace (s + (cnt * s + rest) - s)%nat with (cnt * s + rest)%nat in H2 by lia.
    destruct (IH s (A + Z.of_nat s) rest b H2) as [T R].
    split.
    + intros i Hi. destruct i as [|i].
      * replace (A + Z.of_nat 0 * Z.of_nat s) with A by lia. exact H1.
      * replace (A + Z.of_nat (S i) * Z.of_nat s) with (A + Z.of_nat s + Z.of_nat i * Z.of_nat s) by lia. apply T. lia.
    + replace (A + Z.of_nat (S cnt) * Z.of_nat s) with (A + Z.of_nat s + Z.of_nat cnt * Z.of_nat s) by lia. exact R.
Qed.
End TILES.

Section FCF.
Context {HC : HasCeiling}.
#[using="Type"] Lemma free_chunk_frame : forall AL W m m' c v,
  free_chunk AL m c v -> munch W m m' -> wmono asegs m m' -> 1 <= c <= 31 ->
  disjoint_from W (region AL c + 16 * v) (class_size c) -> disjoint_from W (sh (region AL c + 16 * v)) (class_size c / 8) ->
  free_chunk AL m' c v.
Proof.
  intros AL W m m' c v [[j B] S] MU WM Hc D1 D2. pose proof (class_size_pos c Hc) as CS. split; [exists j|].
  - eapply rw_cells_transport; [exact B| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact D1.
  - eapply rw_cells_transport; [exact S| exact MU| exact WM|]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (pose proof (Z.div_pos (class_size c) 8); lia). exact D2.
Qed.
End FCF.
