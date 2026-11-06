(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ALayout ACells LJ AFake.
Import ListNotations.
Open Scope Z_scope.

Lemma firstn_seq_le : forall i n s, (i <= n)%nat -> firstn i (seq s n) = seq s i.
Proof. induction i as [|i IH]; intros n s LE; [reflexivity|]. destruct n as [|n]; [lia|]. cbn [seq firstn]. f_equal. apply IH. lia. Qed.

Lemma map_seq_upd : forall (f g : nat -> byte) n i, (i < n)%nat -> (forall j, (j < n)%nat -> j <> i -> f j = g j) ->
  map f (seq 0 n) = firstn i (map g (seq 0 n)) ++ f i :: skipn (S i) (map g (seq 0 n)).
Proof.
  intros f g n i LT EXT. rewrite firstn_map, skipn_map, skipn_seq, firstn_seq_le by lia.
  replace n with (i + (1 + (n - S i)))%nat at 1 by lia. rewrite !seq_app, !map_app. cbn [seq map Nat.add].
  f_equal.
  - apply map_ext_in; intros j Hj; apply in_seq in Hj; apply EXT; lia.
  - cbn [app]. f_equal. replace (i + 1)%nat with (S i) by lia. apply map_ext_in. intros j Hj. apply in_seq in Hj. apply EXT; lia.
Qed.

Lemma map_seq_nth : forall (f : nat -> byte) n i d, (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
Proof. intros f n i d LT. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact LT). rewrite map_nth, seq_nth by exact LT. reflexivity. Qed.

Lemma prod_eq_dec_Z : forall a b : Z * Z, {a = b} + {a <> b}.
Proof. intros [a1 a2] [b1 b2]. destruct (Z.eq_dec a1 b1) as [<-|N1]; [destruct (Z.eq_dec a2 b2) as [<-|N2]; [left; reflexivity| right; intros E; apply N2; congruence]| right; intros E; apply N1; congruence]. Qed.

Section CBAT.
Context {HC : HasCeiling}.
#[using="Type"] Lemma cb_split_at : forall (m : mem) A (n : nat) bs (i : nat), (i < n)%nat -> rw_cells asegs m A [CB n bs] ->
  rw_cells asegs m A [CB i (firstn i bs)] /\ rw_cells asegs m (A + Z.of_nat i) [C1 (nth i bs (Z_to_bv 8 0))]
  /\ rw_cells asegs m (A + Z.of_nat i + 1) [CB (n - i - 1) (skipn (S i) bs)].
Proof.
  intros m A n bs i LT H.
  assert (LB : length bs = n) by (destruct H as [[WF _] _]; cbn in WF; destruct WF as (W0 & _); exact W0).
  assert (H' : rw_cells asegs m A ([CB i (firstn i bs)] ++ [C1 (nth i bs (Z_to_bv 8 0))] ++ [CB (n - i - 1) (skipn (S i) bs)])).
  { eapply rw_cells_rebytes; [exact H| | |].
    - cbn. rewrite length_firstn, length_skipn. repeat split; lia.
    - cbn [app cells_bytes cbytes]. rewrite !app_nil_r.
      rewrite <- (firstn_skipn i bs) at 4. f_equal.
      assert (LS : (0 < length (skipn i bs))%nat) by (rewrite length_skipn; lia).
      destruct (skipn i bs) as [|b r] eqn:E; [cbn in LS; lia|].
      assert (NB : nth i bs (Z_to_bv 8 0) = b).
      { rewrite <- (firstn_skipn i bs) at 1. rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn, E.
        replace (i - Nat.min i (length bs))%nat with 0%nat by lia. reflexivity. }
      assert (SR : skipn (S i) bs = r).
      { replace (S i) with (1 + i)%nat by lia. rewrite <- skipn_skipn, E. reflexivity. }
      rewrite NB, SR. cbn. unfold bv_to_le_bytes_1 || idtac. reflexivity.
    - cbn. lia. }
  apply rw_cells_app in H' as [H1 H2]. apply rw_cells_app in H2 as [H2 H3]. cbn [cells_size csize Nat.add] in H2, H3.
  rewrite Nat.add_0_r in H2. split; [exact H1|]. split; [exact H2|].
  replace (A + Z.of_nat i + 1) with (A + Z.of_nat (i + 0) + Z.of_nat 1) by lia. exact H3.
Qed.

#[using="Type"] Lemma cb_join_at : forall (m : mem) A (i r : nat) x b y,
  rw_cells asegs m A [CB i x] -> rw_cells asegs m (A + Z.of_nat i) [C1 b] -> rw_cells asegs m (A + Z.of_nat i + 1) [CB r y] ->
  rw_cells asegs m A [CB (i + 1 + r) (x ++ b :: y)].
Proof.
  intros m A i r x b y HX HB HY.
  assert (LX : length x = i) by (destruct HX as [[WF _] _]; cbn in WF; destruct WF as (W0 & _); exact W0).
  assert (LY : length y = r) by (destruct HY as [[WF _] _]; cbn in WF; destruct WF as (W0 & _); exact W0).
  assert (H : rw_cells asegs m A ([CB i x] ++ [C1 b] ++ [CB r y])).
  { apply rw_cells_app. split; [exact HX|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r.
    apply rw_cells_app. split; [exact HB|]. cbn [cells_size csize Nat.add].
    replace (A + Z.of_nat i + Z.of_nat 1) with (A + Z.of_nat i + 1) by lia. exact HY. }
  eapply rw_cells_rebytes; [exact H| | |].
  - cbn. rewrite length_app. cbn [length]. split; [lia| exact I].
  - cbn [app cells_bytes cbytes]. rewrite !app_nil_r. reflexivity.
  - cbn. lia.
Qed.
End CBAT.

Section REP.
Context {HC : HasCeiling}.
Variable fsb : Z.
Hypothesis FSB_OK : 0x609000 <= fsb /\ fsb + A0_FS_SIZE <= alloc_ceiling /\ app_mem fsb A0_FS_SIZE /\ fsb mod 4096 = 0
                    /\ (fsb + A0_FS_SIZE <= 0x7fff7000 \/ 0x10007fff8000 <= fsb).

Definition foff (kp : Z * Z) : Z := fk_flags_off (fst kp) + snd kp.
Definition fbyte (st : fstate) (j : Z) : byte := if existsb (Z.eqb j) (map foff (ft_live st)) then Z_to_bv 8 1 else Z_to_bv 8 0.
Definition NFLAGS : nat := Z.to_nat 32768.
Definition flag_list (st : fstate) : list byte := map (fun i => fbyte st (Z.of_nat i)) (seq 0 NFLAGS).

Definition hint_cells (st : fstate) : list cell :=
  [C8 (wz (ft_hint st 0)); C8 (wz (ft_hint st 1)); C8 (wz (ft_hint st 2)); C8 (wz (ft_hint st 3)); C8 (wz (ft_hint st 4));
   C8 (wz (ft_hint st 5)); C8 (wz (ft_hint st 6)); C8 (wz (ft_hint st 7)); C8 (wz (ft_hint st 8)); C8 (wz (ft_hint st 9));
   C8 (wz (ft_hint st 10)); C8 (wz 20); C1 (Z_to_bv 8 0)].

Definition rf_free (st : fstate) (m : mem) : Prop :=
  forall k pos, 0 <= k <= 10 -> 0 <= pos < fk_N k -> ~ In (k, pos) (ft_live st) ->
    (exists j, rw_cells asegs m (fk_frame fsb k pos) [CB (Z.to_nat (FB_of k)) j])
    /\ (exists j, rw_cells asegs m (sh (fk_frame fsb k pos)) [CB (Z.to_nat (SB_of k)) j]).

Definition RFAKE_B (st : fstate) (m : mem) : Prop :=
  fst_wf st
  /\ rw_cells asegs m fsb (hint_cells st)
  /\ rw_cells asegs m (fsb + 4096) [CB NFLAGS (flag_list st)]
  /\ rf_free st m.

#[using="HC FSB_OK"] Lemma fsb_num : 0 <= fsb /\ fsb mod 4096 = 0 /\ (fsb + A0_FS_SIZE <= sh fsb \/ sh fsb + A0_FS_SHSIZE <= fsb).
Proof. destruct FSB_OK as (B1 & B2 & B3 & B4 & B5). unfold app_mem, sh, SHADOW_OFF in *. lia. Qed.
#[using="FSB_OK"] Lemma fsb_num2 : fsb + A0_FS_SIZE <= alloc_ceiling /\ sh fsb + A0_FS_SHSIZE <= alloc_ceiling /\ 0x7fff8000 <= sh fsb /\ sh fsb + A0_FS_SHSIZE <= 0x10007fff8000.
Proof.
  destruct FSB_OK as (B1 & B2 & B3 & B4 & B5). pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  unfold app_mem, sh, SHADOW_OFF in *. lia.
Qed.

#[using="HC FSB_OK"] Lemma slot_num : forall k pos, 0 <= k <= 10 -> 0 <= pos < fk_N k ->
  fsb + A0_FS_FRAMES <= fk_frame fsb k pos /\ fk_frame fsb k pos + FB_of k <= fsb + A0_FS_SIZE
  /\ sh fsb <= sh (fk_frame fsb k pos) /\ sh (fk_frame fsb k pos) + SB_of k <= sh fsb + A0_FS_SHSIZE
  /\ 0 < FB_of k /\ 0 < SB_of k.
Proof.
  intros k pos Hk Hp. destruct fsb_num as (F0 & FM & _).
  destruct (ff_of_wf fsb F0 FM (k, pos) Hk Hp) as (_ & A1 & A2 & A3 & _). cbv zeta in *. unfold ff_of, ff_size in *. cbn [ff_class ff_addr fst snd] in *.
  destruct (fk_geom k Hk) as (_ & _ & G3 & _ & G5 & _).
  split; [exact A1|]. split; [exact A2|]. unfold sh, SHADOW_OFF. clear - F0 FM A1 A2 A3 G3 G5. Z.div_mod_to_equations. lia.
Qed.

Definition rf_cls (st : fstate) (iv : Z * Z) : Prop :=
  ((snd iv <= fsb \/ fsb + A0_FS_SIZE <= fst iv) /\ (snd iv <= sh fsb \/ sh fsb + A0_FS_SHSIZE <= fst iv))
  \/ lb (fst_live fsb st) (fst iv) (snd iv - fst iv) \/ ls (fst_live fsb st) (fst iv) (snd iv - fst iv).

#[using="Type"] Lemma live_in : forall st g, fst_wf st -> In g (fst_live fsb st) ->
  exists kp, g = ff_of fsb kp /\ In kp (ft_live st) /\ 0 <= fst kp <= 10 /\ 0 <= snd kp < fk_N (fst kp).
Proof.
  intros st g (FA & _) Hin. unfold fst_live in Hin. apply in_map_iff in Hin as (kp & E & Hkp). exists kp. split; [symmetry; exact E|].
  split; [exact Hkp|]. exact (proj1 (Forall_forall _ _) FA kp Hkp).
Qed.

#[using="HC FSB_OK"] Lemma rf_hdr_disjoint : forall st W, fst_wf st -> Forall (rf_cls st) W ->
  forall A n, fsb <= A -> A + n <= fsb + A0_FS_FRAMES -> disjoint_from W A n.
Proof.
  intros st W WF. destruct fsb_num as (F0 & FM & FSA).
  induction W as [|[lo hi] W IH]; intros FA A n HA HB; cbn [disjoint_from]; [exact I|].
  inversion_clear FA as [|x l F1 F2]. split; [| apply IH; assumption]. clear IH F2.
  unfold rf_cls, lb, ls in F1. cbn [fst snd] in F1. destruct F1 as [F|[(g & Hg & G1 & G2)|(g & Hg & G1 & G2)]]; [lia| |].
  - destruct (live_in st g WF Hg) as (kp & -> & _ & Hk & Hp). destruct (slot_num _ _ Hk Hp) as (S1 & S2 & _).
    unfold ff_size, ff_of in *. cbn [ff_class ff_addr fst snd] in *. lia.
  - destruct (live_in st g WF Hg) as (kp & -> & _ & Hk & Hp). destruct (slot_num _ _ Hk Hp) as (_ & _ & S3 & S4 & _).
    unfold ff_shsize, ff_of in *. cbn [ff_class ff_addr fst snd] in *. lia.
Qed.

#[using="HC FSB_OK"] Lemma rf_slot_disjoint : forall st W, fst_wf st -> Forall (rf_cls st) W ->
  forall k pos, 0 <= k <= 10 -> 0 <= pos < fk_N k -> ~ In (k, pos) (ft_live st) ->
  disjoint_from W (fk_frame fsb k pos) (FB_of k) /\ disjoint_from W (sh (fk_frame fsb k pos)) (SB_of k).
Proof.
  intros st W WF. destruct fsb_num as (F0 & FM & FSA).
  induction W as [|[lo hi] W IH]; intros FA k pos Hk Hp NI; cbn [disjoint_from]; [split; exact I|].
  inversion_clear FA as [|x l F1 F2]. destruct (IH F2 k pos Hk Hp NI) as [IH1 IH2]. clear IH F2.
  destruct (slot_num k pos Hk Hp) as (S1 & S2 & S3 & S4 & _).
  unfold rf_cls, lb, ls in F1. cbn [fst snd] in F1. destruct F1 as [F|[(g & Hg & G1 & G2)|(g & Hg & G1 & G2)]].
  - split; (split; [lia| assumption]).
  - destruct (live_in st g WF Hg) as (kp & -> & Hin & Hk' & Hp'). destruct (slot_num _ _ Hk' Hp') as (T1 & T2 & T3 & T4 & _).
    assert (NE : kp <> (k, pos)) by (intros ->; exact (NI Hin)).
    destruct (ff_of_apart fsb F0 FM kp (k, pos) Hk' Hp' Hk Hp NE) as (P1 & _).
    unfold ff_size, ff_of in *. cbn [ff_class ff_addr fst snd] in *. split; (split; [lia| assumption]).
  - destruct (live_in st g WF Hg) as (kp & -> & Hin & Hk' & Hp'). destruct (slot_num _ _ Hk' Hp') as (T1 & T2 & T3 & T4 & _).
    assert (NE : kp <> (k, pos)) by (intros ->; exact (NI Hin)).
    destruct (ff_of_apart fsb F0 FM kp (k, pos) Hk' Hp' Hk Hp NE) as (_ & P2 & _).
    unfold ff_shsize, ff_of in *. cbn [ff_class ff_addr fst snd] in *. split; (split; [lia| assumption]).
Qed.

#[using="HC FSB_OK"] Lemma rfake_transport : forall st m m' W,
  (forall A cs, rw_cells asegs m A cs -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs) ->
  RFAKE_B st m -> Forall (rf_cls st) W -> RFAKE_B st m'.
Proof.
  intros st m m' W TR (WF & HC0 & FL & FREE) FA. split; [exact WF|].
  split. { apply TR; [exact HC0|]. apply (rf_hdr_disjoint st W WF FA); cbn [hint_cells cells_size csize Nat.add]; lia. }
  split. { apply TR; [exact FL|]. apply (rf_hdr_disjoint st W WF FA); cbn [cells_size csize Nat.add]; unfold NFLAGS; lia. }
  intros k pos Hk Hp NI. destruct (FREE k pos Hk Hp NI) as ((j1 & H1) & (j2 & H2)).
  destruct (rf_slot_disjoint st W WF FA k pos Hk Hp NI) as [D1 D2]. destruct (slot_num k pos Hk Hp) as (_ & _ & _ & _ & P1 & P2).
  split; [exists j1; apply TR; [exact H1|]| exists j2; apply TR; [exact H2|]]; cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; assumption.
Qed.

#[using="HC FSB_OK"] Lemma rfake_B_frame : forall st m m' W, RFAKE_B st m -> munch W m m' -> wmono asegs m m' -> Forall (rf_cls st) W -> RFAKE_B st m'.
Proof. intros st m m' W R MU WM FA. apply (rfake_transport st m m' W); [| exact R| exact FA]. intros A cs H D. eapply rw_cells_transport; eauto. Qed.
#[using="HC FSB_OK"] Lemma rfake_B_frame_m : forall st m m' W, RFAKE_B st m -> munch W m m' -> Forall (rf_cls st) W -> RFAKE_B st m'.
Proof. intros st m m' W R MU FA. apply (rfake_transport st m m' W); [| exact R| exact FA]. intros A cs H D. eapply rw_cells_transport_mo; eauto. Qed.
#[using="HC FSB_OK"] Lemma rfake_B_frame_g : forall st m m' W, RFAKE_B st m -> gmunch W m m' -> wmono asegs m m' -> Forall (rf_cls st) W -> RFAKE_B st m'.
Proof. intros st m m' W R MU WM FA. apply (rfake_transport st m m' W); [| exact R| exact FA]. intros A cs H D. eapply rw_cells_gtransport; eauto. Qed.

#[using="HC fsb FSB_OK"] Lemma foff_inj : forall k p k' p', 0 <= k <= 10 -> 0 <= p < fk_N k -> 0 <= k' <= 10 -> 0 <= p' < fk_N k' ->
  foff (k, p) = foff (k', p') -> (k, p) = (k', p').
Proof.
  intros k p k' p' Hk Hp Hk' Hp' E. unfold foff in E. cbn [fst snd] in E.
  destruct (Z.eq_dec k k') as [<-|NK]; [f_equal; lia|]. pose proof (fk_flags_apart k k' Hk Hk' NK). lia.
Qed.

#[using="HC fsb FSB_OK"] Lemma fbyte_spec : forall st k p, fst_wf st -> 0 <= k <= 10 -> 0 <= p < fk_N k ->
  fbyte st (foff (k, p)) = if existsb (Z.eqb p) (lpos st k) then Z_to_bv 8 1 else Z_to_bv 8 0.
Proof.
  intros st k p WF Hk Hp. unfold fbyte.
  assert (E : existsb (Z.eqb (foff (k, p))) (map foff (ft_live st)) = existsb (Z.eqb p) (lpos st k)).
  { apply eq_true_iff_eq. rewrite !existsb_eqb_in, lpos_in, in_map_iff. split.
    - intros ([k' p'] & E & Hin). destruct WF as (FA & _). destruct (proj1 (Forall_forall _ _) FA _ Hin) as [Hk' Hp']. cbn [fst snd] in *.
      rewrite (foff_inj k p k' p' Hk Hp Hk' Hp' (eq_sym E)). exact Hin.
    - intros Hin. exists (k, p). split; [reflexivity| exact Hin]. }
  rewrite E. reflexivity.
Qed.

#[using="HC fsb FSB_OK"] Lemma foff_range : forall k p, 0 <= k <= 10 -> 0 <= p < fk_N k -> 0 <= foff (k, p) < 32768.
Proof. intros k p Hk Hp. destruct (fk_geom k Hk) as (_ & _ & _ & _ & _ & G6 & G7 & _). unfold foff. cbn [fst snd]. lia. Qed.

#[using="HC fsb FSB_OK"] Lemma flag_list_nth : forall st j, 0 <= j < 32768 -> nth (Z.to_nat j) (flag_list st) (Z_to_bv 8 0) = fbyte st j.
Proof. intros st j Hj. unfold flag_list. rewrite map_seq_nth by (unfold NFLAGS; lia). rewrite Z2Nat.id by lia. reflexivity. Qed.

#[using="HC FSB_OK"] Lemma flag_cell : forall st m k p, RFAKE_B st m -> 0 <= k <= 10 -> 0 <= p < fk_N k ->
  rw_cells asegs m (fk_flag fsb k p) [C1 (if existsb (Z.eqb p) (lpos st k) then Z_to_bv 8 1 else Z_to_bv 8 0)].
Proof.
  intros st m k p (WF & _ & FL & _) Hk Hp. pose proof (foff_range k p Hk Hp) as FR.
  destruct (cb_split_at m (fsb + 4096) NFLAGS (flag_list st) (Z.to_nat (foff (k, p))) ltac:(unfold NFLAGS; lia) FL) as (_ & H & _).
  rewrite flag_list_nth, fbyte_spec in H by assumption. rewrite Z2Nat.id in H by lia.
  unfold fk_flag. unfold foff in H. cbn [fst snd] in H. replace (fsb + 4096 + fk_flags_off k + p) with (fsb + 4096 + (fk_flags_off k + p)) by lia. exact H.
Qed.

#[using="HC fsb FSB_OK"] Lemma flag_list_upd : forall st st' k p, 0 <= k <= 10 -> 0 <= p < fk_N k ->
  (forall j, 0 <= j < 32768 -> j <> foff (k, p) -> fbyte st' j = fbyte st j) ->
  flag_list st' = firstn (Z.to_nat (foff (k, p))) (flag_list st) ++ fbyte st' (foff (k, p)) :: skipn (S (Z.to_nat (foff (k, p)))) (flag_list st).
Proof.
  intros st st' k p Hk Hp EXT. pose proof (foff_range k p Hk Hp) as FR. unfold flag_list.
  rewrite (map_seq_upd (fun i => fbyte st' (Z.of_nat i)) (fun i => fbyte st (Z.of_nat i)) NFLAGS (Z.to_nat (foff (k, p)))).
  - rewrite Z2Nat.id by lia. reflexivity.
  - unfold NFLAGS. lia.
  - intros j LT NE. apply EXT; [unfold NFLAGS in LT; lia| lia].
Qed.

#[using="Type"] Lemma fbyte_cons : forall hint kp l j,
  fbyte (mkFST hint (kp :: l)) j = if j =? foff kp then Z_to_bv 8 1 else fbyte (mkFST hint l) j.
Proof. intros hint kp l j. unfold fbyte. cbn [ft_live map existsb]. destruct (j =? foff kp); reflexivity. Qed.

#[using="HC fsb FSB_OK"] Lemma fbyte_notin : forall st k p, fst_wf st -> 0 <= k <= 10 -> 0 <= p < fk_N k -> ~ In (k, p) (ft_live st) -> fbyte st (foff (k, p)) = Z_to_bv 8 0.
Proof.
  intros st k p WF Hk Hp NI. rewrite fbyte_spec by assumption.
  destruct (existsb (Z.eqb p) (lpos st k)) eqn:E; [| reflexivity]. apply existsb_eqb_in, lpos_in in E. contradiction.
Qed.

#[using="HC FSB_OK"] Lemma flags_rejoin : forall st st' k p (m m' : mem) b,
  0 <= k <= 10 -> 0 <= p < fk_N k ->
  rw_cells asegs m (fsb + 4096) [CB NFLAGS (flag_list st)] ->
  (forall A cs, rw_cells asegs m A cs -> fsb + 4096 <= A -> A + Z.of_nat (cells_size cs) <= fsb + A0_FS_FRAMES ->
                (A + Z.of_nat (cells_size cs) <= fk_flag fsb k p \/ fk_flag fsb k p + 1 <= A) -> rw_cells asegs m' A cs) ->
  rw_cells asegs m' (fk_flag fsb k p) [C1 b] -> fbyte st' (foff (k, p)) = b ->
  (forall j, 0 <= j < 32768 -> j <> foff (k, p) -> fbyte st' j = fbyte st j) ->
  rw_cells asegs m' (fsb + 4096) [CB NFLAGS (flag_list st')].
Proof.
  intros st st' k p m m' b Hk Hp FL TR NEW EB EXT. pose proof (foff_range k p Hk Hp) as FR.
  assert (FLG : fk_flag fsb k p = fsb + 4096 + foff (k, p)) by (unfold fk_flag, foff; cbn [fst snd]; lia).
  set (i := Z.to_nat (foff (k, p))). assert (Ii : Z.of_nat i = foff (k, p)) by (unfold i; lia).
  assert (LT : (i < NFLAGS)%nat) by (unfold NFLAGS; lia). assert (NF : Z.of_nat NFLAGS = 32768) by (unfold NFLAGS; lia).
  destruct (cb_split_at m (fsb + 4096) NFLAGS (flag_list st) i LT FL) as (H1 & _ & H3).
  apply TR in H1; [| lia| cbn [cells_size csize Nat.add]; lia| cbn [cells_size csize Nat.add]; lia].
  apply TR in H3; [| lia| cbn [cells_size csize Nat.add]; lia| cbn [cells_size csize Nat.add]; lia].
  rewrite FLG, <- Ii in NEW.
  pose proof (cb_join_at m' (fsb + 4096) i (NFLAGS - i - 1) _ b _ H1 NEW H3) as J.
  replace (i + 1 + (NFLAGS - i - 1))%nat with NFLAGS in J by lia.
  rewrite (flag_list_upd st st' k p Hk Hp EXT), EB. exact J.
Qed.

#[using="FSB_OK"] Lemma rfake_B_malloc : forall st k (m m' : mem) lo q, RFAKE_B st m -> 0 <= k <= 10 -> (length (ft_live st) < 15)%nat ->
  let st' := fst (fst_malloc fsb st k) in let g := snd (fst_malloc fsb st k) in
  munch [(fsb + 8 * k, fsb + 8 * k + 8); (ff_flag g, ff_flag g + 1); (ff_addr g, ff_addr g + FB_of k);
         (sh (ff_addr g), sh (ff_addr g) + SB_of k); (lo, q)] m m' ->
  wmono asegs m m' -> alloc_ceiling <= lo ->
  rw_cells asegs m' fsb (hint_cells st') -> rw_cells asegs m' (ff_flag g) [C1 (Z_to_bv 8 1)] -> RFAKE_B st' m'.
Proof.
  intros st k m m' lo q (WF & HC0 & FL & FREE) Hk LEN st' g MU WM CLO HC' NEWF.
  destruct fsb_num as (F0 & FM & FSA). destruct fsb_num2 as (B2 & B2s & _).
  destruct (fst_probe_ok st k WF Hk) as [NI PR]. cbv zeta in NI, PR.
  set (p := fst_probe st k mod fk_N k) in *.
  assert (Eg : g = ff_of fsb (k, p)) by reflexivity.
  assert (El : ft_live st' = (k, p) :: ft_live st) by reflexivity.
  destruct (slot_num k p Hk PR) as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (foff_range k p Hk PR) as FR.
  assert (FLG : fk_flag fsb k p = fsb + 4096 + foff (k, p)) by (unfold fk_flag, foff; cbn [fst snd]; lia).
  rewrite Eg in MU, NEWF. unfold ff_of in MU, NEWF. cbn [ff_addr ff_flag fst snd] in MU, NEWF.
  split; [exact (fst_malloc_wf fsb F0 st k WF Hk LEN)|]. split; [exact HC'|].
  split.
  - apply (flags_rejoin st st' k p m m' (Z_to_bv 8 1) Hk PR FL); [| exact NEWF| |].
    + intros A cs H A1 A2 A3. eapply rw_cells_transport; [exact H| exact MU| exact WM|]. cbn [disjoint_from]. lia.
    + unfold st', fst_malloc. cbv zeta. cbn [fst]. rewrite fbyte_cons. fold p. rewrite Z.eqb_refl. reflexivity.
    + intros j Hj NE. unfold st', fst_malloc. cbv zeta. cbn [fst]. rewrite fbyte_cons. fold p.
      destruct (j =? foff (k, p)) eqn:E; [apply Z.eqb_eq in E; contradiction|]. unfold fbyte. reflexivity.
  - intros k' p' Hk' Hp' NI'. rewrite El in NI'.
    assert (NE : (k, p) <> (k', p')) by (intros E; apply NI'; left; exact E).
    assert (NI0 : ~ In (k', p') (ft_live st)) by (intros Hin; apply NI'; right; exact Hin).
    destruct (FREE k' p' Hk' Hp' NI0) as ((j1 & H1) & (j2 & H2)).
    destruct (slot_num k' p' Hk' Hp') as (T1 & T2 & T3 & T4 & T5 & T6).
    destruct (ff_of_apart fsb F0 FM (k, p) (k', p') Hk PR Hk' Hp' NE) as (P1 & P2 & _).
    unfold ff_size, ff_shsize, ff_of in P1, P2. cbn [ff_class ff_addr fst snd] in P1, P2.
    split; [exists j1; eapply rw_cells_transport; [exact H1| exact MU| exact WM|]| exists j2; eapply rw_cells_transport; [exact H2| exact MU| exact WM|]];
      cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia.
Qed.

#[using="HC FSB_OK"] Lemma rfake_B_release : forall st ff rest (m m' : mem) cs,
  RFAKE_B st m -> fst_live fsb st = ff :: rest ->
  munch [(ff_flag ff, ff_flag ff + 1)] m m' -> wmono asegs m m' ->
  rw_cells asegs m' (ff_flag ff) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m' (sh (ff_addr ff)) (shadow_cells (repeat 245 (Z.to_nat (ff_shsize ff)))) ->
  rw_cells asegs m' (ff_addr ff) cs -> Z.of_nat (cells_size cs) = ff_size ff ->
  RFAKE_B (fst_release st) m' /\ fst_live fsb (fst_release st) = rest.
Proof.
  intros st ff rest m m' cs (WF & HC0 & FL & FREE) LIVE MU WM NEWF NEWS NEWB SZ.
  destruct fsb_num as (F0 & FM & FSA).
  destruct st as [hint live]. unfold fst_live in LIVE. cbn [ft_live] in LIVE.
  destruct live as [|[k p] r]; [discriminate LIVE|]. cbn [map] in LIVE. injection LIVE as Eff Erest.
  pose proof WF as (FA & ND & _ & _). cbn [ft_live] in FA, ND.
  apply Forall_cons_iff in FA as [[Hk Hp] FA']. cbn [fst snd] in Hk, Hp. apply NoDup_cons_iff in ND as [NI ND'].
  destruct (slot_num k p Hk Hp) as (S1 & S2 & S3 & S4 & S5 & S6). pose proof (foff_range k p Hk Hp) as FR.
  assert (FLG : fk_flag fsb k p = fsb + 4096 + foff (k, p)) by (unfold fk_flag, foff; cbn [fst snd]; lia).
  subst ff. unfold ff_of, ff_size, ff_shsize in *. cbn [ff_class ff_addr ff_flag fst snd] in *.
  pose proof (fst_release_wf fsb F0 (mkFST hint ((k, p) :: r)) WF) as WF'. unfold fst_release in *. cbn [ft_hint ft_live tl] in *.
  split; [| unfold fst_live; cbn [ft_live]; exact Erest].
  split; [exact WF'|].
  split. { eapply rw_cells_transport; [exact HC0| exact MU| exact WM|]. cbn [disjoint_from hint_cells cells_size csize Nat.add]. lia. }
  split.
  - apply (flags_rejoin (mkFST hint ((k, p) :: r)) (mkFST hint r) k p m m' (Z_to_bv 8 0) Hk Hp FL); [| exact NEWF| |].
    + intros A cs0 H A1 A2 A3. eapply rw_cells_transport; [exact H| exact MU| exact WM|]. cbn [disjoint_from]. lia.
    + apply (fbyte_notin (mkFST hint r) k p WF' Hk Hp). cbn [ft_live]. exact NI.
    + intros j Hj NE. rewrite fbyte_cons. destruct (j =? foff (k, p)) eqn:E; [apply Z.eqb_eq in E; contradiction| reflexivity].
  - intros k' p' Hk' Hp' NI'. cbn [ft_live] in NI'.
    destruct (prod_eq_dec_Z (k', p') (k, p)) as [E|NE].
    + injection E as -> ->. split.
      * destruct (rw_cells_forget asegs m' _ cs NEWB) as (j & Hj). exists j.
        replace (Z.to_nat (FB_of k)) with (cells_size cs) by lia. exact Hj.
      * destruct (rw_cells_forget asegs m' _ _ NEWS) as (j & Hj). exists j.
        rewrite cells_size_shadow, repeat_length in Hj. exact Hj.
    + assert (NI0 : ~ In (k', p') (ft_live (mkFST hint ((k, p) :: r)))) by (cbn [ft_live]; intros [E|Hin]; [apply NE; symmetry; exact E| exact (NI' Hin)]).
      destruct (FREE k' p' Hk' Hp' NI0) as ((j1 & H1) & (j2 & H2)).
      destruct (slot_num k' p' Hk' Hp') as (T1 & T2 & T3 & T4 & T5 & T6).
      split; [exists j1; eapply rw_cells_transport; [exact H1| exact MU| exact WM|]| exists j2; eapply rw_cells_transport; [exact H2| exact MU| exact WM|]];
        cbn [disjoint_from cells_size csize Nat.add]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia.
Qed.

End REP.
