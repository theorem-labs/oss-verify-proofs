(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr Tac InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase ALayout ARepExt FsKit AFake_iface AFake_cnt AFake_gc AFake_gcl AFake_gcf. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_sm0. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.AFake_sm2gc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {ov : ARep.annOV}.

Lemma gflag_fk : forall L c p, gflag (al_fake L) c p = fk_flag L c p.
Proof. reflexivity. Qed.
Lemma gframe_fk : forall L c p, gframe (al_fake L) c p = fk_frame L c p.
Proof. intros. unfold gframe, fk_frame, fk_frames, fk_fsize. lia. Qed.
Lemma gcN_fk : forall c, gcN c = fk_nframes c.
Proof. reflexivity. Qed.

Section G.
Variables (L : alayout) (LB : list ablock) (m : amem) (rsf : Z -> Z) (bot cur : Z).
Hypothesis AF : AFAKE (gb:=true) L LB m.
Hypothesis ND : List.NoDup LB.
Hypothesis CLS : forall c F n, In (FKB c F n) LB -> c <= 2.
Hypothesis RS : forall c F n, In (FKB c F n) LB -> 0 <= rsf F < 2^64 /\ rw_cells asegs m (F + 24) [C8 (Z_to_bv 64 (rsf F))].

Definition gfl (c p : Z) : byte := match m (wa (fk_flag L c p)) with Some b => b | None => Z_to_bv 8 0 end.
Definition grs (c p : Z) : Z := rsf (fk_frame L c p).
Definition fk_dead (b : ablock) : bool :=
  match ab_kind b with ABFake _ => (bot <? rsf (ab_addr b)) && (rsf (ab_addr b) <? cur) | _ => false end.
Definition fk_kept : list ablock := List.filter (fun b => negb (fk_dead b)) LB.

Lemma gfl_cell : forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> rw_cells asegs m (gflag (al_fake L) c p) [C1 (gfl c p)].
Proof.
  intros c p Hc Hp. destruct (afake_flag_cell L LB m c p AF Hc Hp) as (b & Cb & Mb). unfold gfl. rewrite Mb. exact Cb.
Qed.

Lemma gfl_block : forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> bv_unsigned (gfl c p) <> 0 ->
  In (FKB c (fk_frame L c p) (fk_fsize c)) LB /\ gfl c p = Z_to_bv 8 1.
Proof.
  intros c p Hc Hp NZ. destruct (afake_flag_cell L LB m c p AF Hc Hp) as (b & Cb & Mb).
  pose proof AF as (_ & _ & _ & _ & _ & _ & _ & FL & LV & _). unfold gfl in *. rewrite Mb in *.
  assert (IN : In (FKB c (fk_frame L c p) (fk_fsize c)) LB) by (apply (FL c p b Hc Hp Mb); intros ->; apply NZ; reflexivity).
  split; [exact IN|]. destruct (LV _ _ _ IN) as (_ & _ & pos' & Hp' & HF' & B1).
  apply (fk_frame_inj L c _ _ ltac:(lia)) in HF'. subst pos'. rewrite Mb in B1. injection B1 as ->. reflexivity.
Qed.

Lemma grs_cell : forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> bv_unsigned (gfl c p) <> 0 ->
  0 <= grs c p < 2^64 /\ rw_cells asegs m (gframe (al_fake L) c p + 24) [C8 (Z_to_bv 64 (grs c p))].
Proof.
  intros c p Hc Hp NZ. destruct (gfl_block c p Hc Hp NZ) as [IN _]. rewrite gframe_fk. exact (RS _ _ _ IN).
Qed.

Lemma gfreed_dead : forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> bv_unsigned (gfl c p) <> 0 ->
  gfreed bot cur (gfl c p) (grs c p) = fk_dead (FKB c (fk_frame L c p) (fk_fsize c)).
Proof.
  intros c p Hc Hp NZ. unfold gfreed, fk_dead, grs. cbn [ab_kind ab_addr].
  replace (bv_unsigned (gfl c p) =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). reflexivity.
Qed.

Lemma gfreed_shadow : forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> gfreed bot cur (gfl c p) (grs c p) = true ->
  c <= 2 /\ exists ws, length ws = Z.to_nat (2 ^ c) /\ rw_cells asegs m (shad (gframe (al_fake L) c p)) (map C8 ws).
Proof.
  intros c p Hc Hp GF.
  assert (NZ : bv_unsigned (gfl c p) <> 0).
  { unfold gfreed in GF. apply andb_prop in GF as [GF _]. apply andb_prop in GF as [GF _]. apply negb_true_iff in GF. apply Z.eqb_neq in GF. exact GF. }
  destruct (gfl_block c p Hc Hp NZ) as [IN _]. pose proof (CLS _ _ _ IN) as C2. split; [exact C2|].
  pose proof AF as (G & _ & _ & _ & _ & _ & DC2 & _). destruct G as (G1 & G2 & G3 & _). unfold FAKESZ in *.
  pose proof (gc_shad_off (al_fake L) c p Hc Hp G2 G3) as (_ & SLO & SHI).
  pose proof (ablk_lin _ _ G2) as (_ & F0 & _ & _). pose proof (gc_geo (al_fake L) c p Hc Hp F0) as (_ & GA & GB).
  pose proof (gc_pows c Hc) as (_ & _ & _ & _ & P8 & PC).
  assert (SUB : shad (al_fake L) <= shad (gframe (al_fake L) c p) /\ shad (gframe (al_fake L) c p) + 8 * 2 ^ c <= shad (al_fake L) + shlen 11571200).
  { rewrite !gc_shad_eq. replace (shlen 11571200) with 1446400 by reflexivity. remember (gframe (al_fake L) c p) as F. remember (2 ^ c) as K. clear - GA GB P8 PC F0 G1. Z.div_mod_to_equations. lia. }
  assert (DCF : dc_at m (shad (gframe (al_fake L) c p)) (8 * 2 ^ c)) by (eapply dc_sub; [exact DC2| lia| lia| lia]).
  assert (CC : c = 0 \/ c = 1 \/ c = 2) by lia. destruct CC as [-> | [-> | ->]].
  - change (8 * 2 ^ 0) with 8 in DCF. destruct (c8_of_dc m _ DCF) as [w W]. exists [w]. split; [reflexivity| exact W].
  - change (8 * 2 ^ 1) with 16 in DCF. destruct (c8c8_of_dc m _ DCF) as (w0 & w1 & W). exists [w0; w1]. split; [reflexivity| exact W].
  - change (8 * 2 ^ 2) with 32 in DCF. destruct (c8x4_of_dc m _ DCF) as (w0 & w1 & w2 & w3 & W). exists [w0; w1; w2; w3]. split; [reflexivity| exact W].
Qed.

Lemma fk_kept_In : forall b, In b fk_kept <-> In b LB /\ fk_dead b = false.
Proof. intros b. unfold fk_kept. rewrite filter_In, negb_true_iff. tauto. Qed.
Lemma fk_kept_NoDup : List.NoDup fk_kept.
Proof. apply NoDup_filter. exact ND. Qed.
Lemma fk_kept_heap : forall p A n, In (HB p A n) LB -> In (HB p A n) fk_kept.
Proof. intros p A n H. apply fk_kept_In. split; [exact H| reflexivity]. Qed.

Lemma fk_kept_hb_ids : hb_ids fk_kept = hb_ids LB.
Proof.
  unfold fk_kept. clear. induction LB as [|b l IH]; [reflexivity|].
  change (List.filter (fun b0 => negb (fk_dead b0)) (b :: l)) with (if negb (fk_dead b) then b :: List.filter (fun b0 => negb (fk_dead b0)) l else List.filter (fun b0 => negb (fk_dead b0)) l).
  unfold hb_ids in *. destruct b as [[p|c] A n]; unfold fk_dead at 1; cbn [ab_kind negb flat_map app].
  - rewrite IH. reflexivity.
  - destruct ((bot <? rsf (ab_addr (mkABlock (ABFake c) A n))) && (rsf (ab_addr (mkABlock (ABFake c) A n)) <? cur)); cbn [negb flat_map ab_kind app]; exact IH.
Qed.

Lemma gc_probe : forall c h, 0 <= c < 11 -> Z.of_nat (fk_count c LB) < fk_nframes c ->
  exists j, 0 <= j < fk_nframes c
    /\ (forall t, 0 <= t < j -> bv_unsigned (gfl' gfl grs bot cur c ((h + t) mod fk_nframes c)) <> 0)
    /\ gfl' gfl grs bot cur c ((h + j) mod fk_nframes c) = Z_to_bv 8 0
    /\ ~ In (FKB c (fk_frame L c ((h + j) mod fk_nframes c)) (fk_fsize c)) fk_kept.
Proof.
  intros c h Hc CNT. assert (NP : 0 < fk_nframes c) by (apply fk_nframes_pos; lia).
  set (busy := fun p => negb (bv_unsigned (gfl' gfl grs bot cur c p) =? 0)).
  destruct (first_free_pos busy (fun p => FKB c (fk_frame L c p) (fk_fsize c)) (List.filter (isfk c) fk_kept) (fk_nframes c) h NP) as (j & Hj & FREE & BUSY).
  - apply NoDup_filter. exact fk_kept_NoDup.
  - intros p1 p2 _ _ E. injection E as E. exact (fk_frame_inj L c p1 p2 ltac:(lia) E).
  - intros p Hp B. apply filter_In. split; [| apply isfk_FKB]. unfold busy in B. apply negb_true_iff in B. apply Z.eqb_neq in B.
    unfold gfl' in B. destruct (gfreed bot cur (gfl c p) (grs c p)) eqn:GF; [exfalso; apply B; reflexivity|].
    destruct (gfl_block c p Hc Hp B) as [IN _]. apply fk_kept_In. split; [exact IN|]. rewrite <- (gfreed_dead c p Hc Hp B). exact GF.
  - pose proof (fk_count_filter_le c (fun b => negb (fk_dead b)) LB) as LE. unfold fk_count, fk_kept in *. lia.
  - exists j. split; [exact Hj|].
    assert (PJ : forall t, 0 <= (h + t) mod fk_nframes c < fk_nframes c) by (intros t; apply Z.mod_pos_bound; exact NP).
    split; [| split].
    + intros t Ht. specialize (BUSY t Ht). unfold busy in BUSY. apply negb_true_iff in BUSY. apply Z.eqb_neq in BUSY. exact BUSY.
    + unfold busy in FREE. apply negb_false_iff in FREE. apply Z.eqb_eq in FREE. apply bv_eq. rewrite FREE. reflexivity.
    + intros Hin. apply fk_kept_In in Hin as [IN ALIVE].
      pose proof AF as (_ & _ & _ & _ & _ & _ & _ & _ & LV & _). destruct (LV _ _ _ IN) as (_ & _ & pos' & Hp' & HF' & B1).
      apply (fk_frame_inj L c _ _ ltac:(lia)) in HF'. subst pos'.
      assert (E1 : gfl c ((h + j) mod fk_nframes c) = Z_to_bv 8 1) by (unfold gfl; rewrite B1; reflexivity).
      assert (NZ : bv_unsigned (gfl c ((h + j) mod fk_nframes c)) <> 0) by (rewrite E1; discriminate).
      unfold busy in FREE. apply negb_false_iff in FREE. apply Z.eqb_eq in FREE. unfold gfl' in FREE.
      rewrite (gfreed_dead c _ Hc (PJ j) NZ), ALIVE in FREE. rewrite E1 in FREE. discriminate FREE.
Qed.

Lemma afake_after_gc : forall (m' : amem) (c0 pos0 : Z) (h0' h1' h2' : word) (hs' : list byte),
  0 <= c0 < 11 -> 0 <= pos0 < gcN c0 ->
  wmono asegs m m' ->
  afake_cells L m' -> rw_cells asegs m' (al_fake L + 88) [C8 (Z_to_bv 64 20)] ->
  rw_cells asegs m' (al_fake L) [C8 h0'; C8 h1'; C8 h2'; CB 64 hs'] ->
  rw_cells asegs m' (al_fake L + 96) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m' (fk_flag L c0 pos0) [C1 (Z_to_bv 8 1)] ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> (c, p) <> (c0, pos0) ->
       rw_cells asegs m' (gflag (al_fake L) c p) [C1 (gfl' gfl grs bot cur c p)]) ->
  ~ In (FKB c0 (fk_frame L c0 pos0) (fk_fsize c0)) fk_kept ->
  rw_cells asegs m' (al_t L + 72) [C8 (Z_to_bv 64 (al_fake L))] ->
  AFAKE (gb:=false) L (FKB c0 (fk_frame L c0 pos0) (fk_fsize c0) :: fk_kept) m'.
Proof.
  intros m' c0 pos0 h0' h1' h2' hs' Hc0 Hp0 WM CE' LOG' HNT' NGC' FL1 FLAGS' NOTIN TFS'.
  pose proof AF as (G & _ & _ & _ & _ & DC1 & DC2 & FL & LV & TFSC).
  pose proof G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & _ & _ & _). unfold AIMG_HI, FAKESZ in *.
  assert (SHLO : 0x62f000 <= shad (al_fake L)).
  { rewrite gc_shad_eq. pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. clear - G2c. Z.div_mod_to_equations. lia. }
  assert (HIGH : forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> 0x62f000 <= fk_flag L c p).
  { intros c p Hc Hp. pose proof (fk_flag_range L c p Hc Hp). lia. }
  split; [exact G|]. split; [exact CE'|]. split; [exists h0', h1', h2', hs'; exact HNT'|]. split; [exact LOG'|]. split; [exact NGC'|].
  split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
  split; [eapply dc_at_any; [exact DC2| exact WM| exact SHLO]|].
  split.
  -
    intros c p b Hc Hp Mb NZ.
    destruct (Z.eq_dec c c0) as [EC|NC]; [destruct (Z.eq_dec p pos0) as [EP|NP]|].
    + subst c p. left. reflexivity.
    + right. assert (NE : (c, p) <> (c0, pos0)) by congruence.
      pose proof (rw_C1_high m' _ _ (FLAGS' c p Hc Hp NE) (HIGH c p Hc Hp)) as M2. rewrite gflag_fk in M2. rewrite M2 in Mb. injection Mb as <-.
      unfold gfl' in NZ. destruct (gfreed bot cur (gfl c p) (grs c p)) eqn:GF; [exfalso; apply NZ; reflexivity|].
      assert (NZ2 : bv_unsigned (gfl c p) <> 0) by (intros E0; apply NZ; apply bv_eq; rewrite E0; reflexivity).
      destruct (gfl_block c p Hc Hp NZ2) as [IN _]. apply fk_kept_In. split; [exact IN|]. rewrite <- (gfreed_dead c p Hc Hp NZ2). exact GF.
    + right. assert (NE : (c, p) <> (c0, pos0)) by congruence.
      pose proof (rw_C1_high m' _ _ (FLAGS' c p Hc Hp NE) (HIGH c p Hc Hp)) as M2. rewrite gflag_fk in M2. rewrite M2 in Mb. injection Mb as <-.
      unfold gfl' in NZ. destruct (gfreed bot cur (gfl c p) (grs c p)) eqn:GF; [exfalso; apply NZ; reflexivity|].
      assert (NZ2 : bv_unsigned (gfl c p) <> 0) by (intros E0; apply NZ; apply bv_eq; rewrite E0; reflexivity).
      destruct (gfl_block c p Hc Hp NZ2) as [IN _]. apply fk_kept_In. split; [exact IN|]. rewrite <- (gfreed_dead c p Hc Hp NZ2). exact GF.
  -
    split; [| exact TFS'].
    intros c F n [E|Hin].
    + injection E as <- <- <-. split; [exact Hc0|]. split; [reflexivity|]. exists pos0. split; [exact Hp0|]. split; [reflexivity|].
      exact (rw_C1_high m' _ _ FL1 (HIGH c0 pos0 Hc0 Hp0)).
    + apply fk_kept_In in Hin as [IN ALIVE]. destruct (LV c F n IN) as (Hc & Hn & pos' & Hp' & HF' & B1).
      split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp'|]. split; [exact HF'|].
      assert (NE : (c, pos') <> (c0, pos0)).
      { intros E. injection E as -> ->. apply NOTIN. apply fk_kept_In. split; [| rewrite <- HF', <- Hn; exact ALIVE]. rewrite <- HF', <- Hn. exact IN. }
      pose proof (rw_C1_high m' _ _ (FLAGS' c pos' Hc Hp' NE) (HIGH c pos' Hc Hp')) as M2. rewrite gflag_fk in M2. rewrite M2. f_equal.
      assert (E1 : gfl c pos' = Z_to_bv 8 1) by (unfold gfl; rewrite B1; reflexivity).
      assert (NZ2 : bv_unsigned (gfl c pos') <> 0) by (rewrite E1; discriminate).
      unfold gfl'. rewrite (gfreed_dead c pos' Hc Hp' NZ2). rewrite <- HF', <- Hn, ALIVE. exact E1.
Qed.
End G.

Section W.
Variables (fs : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (bot cur : Z).
Hypothesis FLO : ablk fs (fs + 11571200).
Hypothesis FHI : fs + 11571200 <= ATOP.
Hypothesis FAL : fs mod 4096 = 0.

Lemma gcW1_hulls : forall c q, 0 <= c < 11 -> 0 <= q < gcN c ->
  fs + 4096 <= gflag fs c q /\ gflag fs c q + 1 <= fs + 36864
  /\ shad (fs + 36864) <= shad (gframe fs c q) /\ shad (gframe fs c q) + 8 * 2 ^ c <= shad (fs + 11571200).
Proof.
  intros c q C Q. pose proof (ablk_lin _ _ FLO) as (_ & F0 & _ & _). pose proof (gc_geo fs c q C Q F0) as (G1 & G2 & G3).
  pose proof (gc_pows c C) as (_ & _ & _ & _ & P8 & PC). split; [lia|]. split; [lia|]. rewrite !gc_shad_eq.
  remember (gframe fs c q) as F. remember (2 ^ c) as K. clear - G2 G3 P8 PC F0 FAL. Z.div_mod_to_equations. lia.
Qed.

Lemma gcWall_disj_hulls : forall A k, 0 <= k ->
  (A + k <= fs + 4096 \/ fs + 36864 <= A) -> (A + k <= shad (fs + 36864) \/ shad (fs + 11571200) <= A) ->
  disjoint_from (gcWall fs fl rs bot cur 0 GC_NCLS) A k.
Proof.
  intros A k K H1 H2. apply gcWall_disjoint; [lia| rewrite GC_NCLS_eq; lia|].
  intros c q C Q _. rewrite GC_NCLS_eq in C. pose proof (gcW1_hulls c q ltac:(lia) Q) as (X1 & X2 & X3 & X4).
  cbn [gcW1 disjoint_from]. split; [lia|]. split; [lia| exact I].
Qed.

Lemma gcWall_disj_kept_shadow : forall c' p A k, 0 <= c' < 11 -> 0 <= p < gcN c' -> gfreed bot cur (fl c' p) (rs c' p) = false ->
  shad (gframe fs c' p) <= A -> A + k <= shad (gframe fs c' p) + 8 * 2 ^ c' -> 0 <= k ->
  disjoint_from (gcWall fs fl rs bot cur 0 GC_NCLS) A k.
Proof.
  intros c' p A k C' P NF A0 A1 K. apply gcWall_disjoint; [lia| rewrite GC_NCLS_eq; lia|].
  intros c q C Q GF. rewrite GC_NCLS_eq in C.
  assert (NE : (c, q) <> (c', p)) by (intros E; injection E as -> ->; congruence).
  eapply disjoint_from_sub; [exact (gcW1_disj_shadow2 fs FLO FHI c q c' p ltac:(lia) Q C' P NE)| lia| lia| lia].
Qed.
Lemma gcWall_disj_kept_flag : forall c' p, 0 <= c' < 11 -> 0 <= p < gcN c' -> gfreed bot cur (fl c' p) (rs c' p) = false ->
  disjoint_from (gcWall fs fl rs bot cur 0 GC_NCLS) (gflag fs c' p) 1.
Proof.
  intros c' p C' P NF. apply gcWall_disjoint; [lia| rewrite GC_NCLS_eq; lia|].
  intros c q C Q GF. rewrite GC_NCLS_eq in C.
  assert (NE : (c, q) <> (c', p)) by (intros E; injection E as -> ->; congruence).
  exact (gcW1_disj_flag2 fs FLO FHI c q c' p ltac:(lia) Q C' P NE).
Qed.

Lemma gcW_Forall : forall (P : Z * Z -> Prop) c (flc : Z -> byte) (rsc : Z -> Z) n i,
  (forall q, i <= q < i + Z.of_nat n -> gfreed bot cur (flc q) (rsc q) = true -> Forall P (gcW1 fs c q)) ->
  Forall P (gcW fs c flc rsc bot cur i n).
Proof.
  intros P c flc rsc n. induction n as [|n IH]; intros i H; cbn [gcW]; [constructor|].
  apply Forall_app. split.
  - destruct (gfreed bot cur (flc i) (rsc i)) eqn:GF; [apply H; [lia| exact GF]| constructor].
  - apply IH. intros q Hq GF. apply H; [lia| exact GF].
Qed.
Lemma gcWall_Forall : forall (P : Z * Z -> Prop) k c, 0 <= c -> c + Z.of_nat k <= 11 ->
  (forall c' q, c <= c' < c + Z.of_nat k -> 0 <= q < gcN c' -> gfreed bot cur (fl c' q) (rs c' q) = true -> Forall P (gcW1 fs c' q)) ->
  Forall P (gcWall fs fl rs bot cur c k).
Proof.
  intros P k. induction k as [|k IH]; intros c C0 CK H; cbn [gcWall]; [constructor|].
  apply Forall_app. split.
  - apply gcW_Forall. intros q Hq GF. apply H; [lia| | exact GF].
    assert (0 < gcN c) by (unfold gcN; apply Z.pow_pos_nonneg; lia). rewrite Z2Nat.id in Hq by lia. lia.
  - apply IH; [lia| lia|]. intros c' q Hc' Hq GF. apply H; [lia| exact Hq| exact GF].
Qed.
End W.

Lemma gcWall_aext : forall L fl rs bot cur,
  ablk (al_fake L) (al_fake L + 11571200) -> al_fake L + 11571200 <= ATOP -> al_fake L mod 4096 = 0 ->
  Forall (aext L) (gcWall (al_fake L) fl rs bot cur 0 GC_NCLS).
Proof.
  intros L fl rs bot cur FLO FHI FAL. apply gcWall_Forall; [lia| rewrite GC_NCLS_eq; lia|].
  intros c q C Q _. rewrite GC_NCLS_eq in C. pose proof (gcW1_hulls (al_fake L) FLO FAL c q ltac:(lia) Q) as (X1 & X2 & X3 & X4).
  pose proof (ablk_lin _ _ FLO) as (_ & F0 & _ & _).
  assert (SH : shad (al_fake L) <= shad (al_fake L + 36864) /\ shad (al_fake L + 11571200) = shad (al_fake L) + shlen 11571200).
  { rewrite !gc_shad_eq. replace (shlen 11571200) with 1446400 by reflexivity. clear - F0 FAL. Z.div_mod_to_equations. lia. }
  unfold gcW1. constructor; [| constructor; [| constructor]]; unfold aext; cbn [fst snd]; intros _.
  - left. lia.
  - right; left. lia.
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import ABase.TwinB ALayout.TwinB ARepExt.TwinB FsKit.TwinB AFake_iface.TwinB AFake_cnt.TwinB AFake_gc.TwinB AFake_gcl.TwinB AFake_gcf.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_sm0.TwinB.AFake_sm2gc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {ov : ARep.TwinB.annOV}.

Lemma gflag_fk : forall L c p, gflag (al_fake L) c p = fk_flag L c p.
Proof. reflexivity. Qed.
Lemma gframe_fk : forall L c p, gframe (al_fake L) c p = fk_frame L c p.
Proof. intros. unfold gframe, fk_frame, fk_frames, fk_fsize. lia. Qed.
Lemma gcN_fk : forall c, gcN c = fk_nframes c.
Proof. reflexivity. Qed.

Section G.
Variables (L : alayout) (LB : list ablock) (m : amem) (rsf : Z -> Z) (bot cur : Z).
Hypothesis AF : AFAKE (gb:=true) L LB m.
Hypothesis ND : List.NoDup LB.
Hypothesis CLS : forall c F n, In (FKB c F n) LB -> c <= 2.
Hypothesis RS : forall c F n, In (FKB c F n) LB -> 0 <= rsf F < 2^64 /\ rw_cells bsegs m (F + 24) [C8 (Z_to_bv 64 (rsf F))].

Definition gfl (c p : Z) : byte := match m (wa (fk_flag L c p)) with Some b => b | None => Z_to_bv 8 0 end.
Definition grs (c p : Z) : Z := rsf (fk_frame L c p).
Definition fk_dead (b : ablock) : bool :=
  match ab_kind b with ABFake _ => (bot <? rsf (ab_addr b)) && (rsf (ab_addr b) <? cur) | _ => false end.
Definition fk_kept : list ablock := List.filter (fun b => negb (fk_dead b)) LB.

Lemma gfl_cell : forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> rw_cells bsegs m (gflag (al_fake L) c p) [C1 (gfl c p)].
Proof.
  intros c p Hc Hp. destruct (afake_flag_cell L LB m c p AF Hc Hp) as (b & Cb & Mb). unfold gfl. rewrite Mb. exact Cb.
Qed.

Lemma gfl_block : forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> bv_unsigned (gfl c p) <> 0 ->
  In (FKB c (fk_frame L c p) (fk_fsize c)) LB /\ gfl c p = Z_to_bv 8 1.
Proof.
  intros c p Hc Hp NZ. destruct (afake_flag_cell L LB m c p AF Hc Hp) as (b & Cb & Mb).
  pose proof AF as (_ & _ & _ & _ & _ & _ & _ & FL & LV & _). unfold gfl in *. rewrite Mb in *.
  assert (IN : In (FKB c (fk_frame L c p) (fk_fsize c)) LB) by (apply (FL c p b Hc Hp Mb); intros ->; apply NZ; reflexivity).
  split; [exact IN|]. destruct (LV _ _ _ IN) as (_ & _ & pos' & Hp' & HF' & B1).
  apply (fk_frame_inj L c _ _ ltac:(lia)) in HF'. subst pos'. rewrite Mb in B1. injection B1 as ->. reflexivity.
Qed.

Lemma grs_cell : forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> bv_unsigned (gfl c p) <> 0 ->
  0 <= grs c p < 2^64 /\ rw_cells bsegs m (gframe (al_fake L) c p + 24) [C8 (Z_to_bv 64 (grs c p))].
Proof.
  intros c p Hc Hp NZ. destruct (gfl_block c p Hc Hp NZ) as [IN _]. rewrite gframe_fk. exact (RS _ _ _ IN).
Qed.

Lemma gfreed_dead : forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> bv_unsigned (gfl c p) <> 0 ->
  gfreed bot cur (gfl c p) (grs c p) = fk_dead (FKB c (fk_frame L c p) (fk_fsize c)).
Proof.
  intros c p Hc Hp NZ. unfold gfreed, fk_dead, grs. cbn [ab_kind ab_addr].
  replace (bv_unsigned (gfl c p) =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). reflexivity.
Qed.

Lemma gfreed_shadow : forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> gfreed bot cur (gfl c p) (grs c p) = true ->
  c <= 2 /\ exists ws, length ws = Z.to_nat (2 ^ c) /\ rw_cells bsegs m (shad (gframe (al_fake L) c p)) (map C8 ws).
Proof.
  intros c p Hc Hp GF.
  assert (NZ : bv_unsigned (gfl c p) <> 0).
  { unfold gfreed in GF. apply andb_prop in GF as [GF _]. apply andb_prop in GF as [GF _]. apply negb_true_iff in GF. apply Z.eqb_neq in GF. exact GF. }
  destruct (gfl_block c p Hc Hp NZ) as [IN _]. pose proof (CLS _ _ _ IN) as C2. split; [exact C2|].
  pose proof AF as (G & _ & _ & _ & _ & _ & DC2 & _). destruct G as (G1 & G2 & G3 & _). unfold FAKESZ in *.
  pose proof (gc_shad_off (al_fake L) c p Hc Hp G2 G3) as (_ & SLO & SHI).
  pose proof (ablk_lin _ _ G2) as (_ & F0 & _ & _). pose proof (gc_geo (al_fake L) c p Hc Hp F0) as (_ & GA & GB).
  pose proof (gc_pows c Hc) as (_ & _ & _ & _ & P8 & PC).
  assert (SUB : shad (al_fake L) <= shad (gframe (al_fake L) c p) /\ shad (gframe (al_fake L) c p) + 8 * 2 ^ c <= shad (al_fake L) + shlen 11571200).
  { rewrite !gc_shad_eq. replace (shlen 11571200) with 1446400 by reflexivity. remember (gframe (al_fake L) c p) as F. remember (2 ^ c) as K. clear - GA GB P8 PC F0 G1. Z.div_mod_to_equations. lia. }
  assert (DCF : dc_at m (shad (gframe (al_fake L) c p)) (8 * 2 ^ c)) by (eapply dc_sub; [exact DC2| lia| lia| lia]).
  assert (CC : c = 0 \/ c = 1 \/ c = 2) by lia. destruct CC as [-> | [-> | ->]].
  - change (8 * 2 ^ 0) with 8 in DCF. destruct (c8_of_dc m _ DCF) as [w W]. exists [w]. split; [reflexivity| exact W].
  - change (8 * 2 ^ 1) with 16 in DCF. destruct (c8c8_of_dc m _ DCF) as (w0 & w1 & W). exists [w0; w1]. split; [reflexivity| exact W].
  - change (8 * 2 ^ 2) with 32 in DCF. destruct (c8x4_of_dc m _ DCF) as (w0 & w1 & w2 & w3 & W). exists [w0; w1; w2; w3]. split; [reflexivity| exact W].
Qed.

Lemma fk_kept_In : forall b, In b fk_kept <-> In b LB /\ fk_dead b = false.
Proof. intros b. unfold fk_kept. rewrite filter_In, negb_true_iff. tauto. Qed.
Lemma fk_kept_NoDup : List.NoDup fk_kept.
Proof. apply NoDup_filter. exact ND. Qed.
Lemma fk_kept_heap : forall p A n, In (HB p A n) LB -> In (HB p A n) fk_kept.
Proof. intros p A n H. apply fk_kept_In. split; [exact H| reflexivity]. Qed.

Lemma fk_kept_hb_ids : hb_ids fk_kept = hb_ids LB.
Proof.
  unfold fk_kept. clear. induction LB as [|b l IH]; [reflexivity|].
  change (List.filter (fun b0 => negb (fk_dead b0)) (b :: l)) with (if negb (fk_dead b) then b :: List.filter (fun b0 => negb (fk_dead b0)) l else List.filter (fun b0 => negb (fk_dead b0)) l).
  unfold hb_ids in *. destruct b as [[p|c] A n]; unfold fk_dead at 1; cbn [ab_kind negb flat_map app].
  - rewrite IH. reflexivity.
  - destruct ((bot <? rsf (ab_addr (mkABlock (ABFake c) A n))) && (rsf (ab_addr (mkABlock (ABFake c) A n)) <? cur)); cbn [negb flat_map ab_kind app]; exact IH.
Qed.

Lemma gc_probe : forall c h, 0 <= c < 11 -> Z.of_nat (fk_count c LB) < fk_nframes c ->
  exists j, 0 <= j < fk_nframes c
    /\ (forall t, 0 <= t < j -> bv_unsigned (gfl' gfl grs bot cur c ((h + t) mod fk_nframes c)) <> 0)
    /\ gfl' gfl grs bot cur c ((h + j) mod fk_nframes c) = Z_to_bv 8 0
    /\ ~ In (FKB c (fk_frame L c ((h + j) mod fk_nframes c)) (fk_fsize c)) fk_kept.
Proof.
  intros c h Hc CNT. assert (NP : 0 < fk_nframes c) by (apply fk_nframes_pos; lia).
  set (busy := fun p => negb (bv_unsigned (gfl' gfl grs bot cur c p) =? 0)).
  destruct (first_free_pos busy (fun p => FKB c (fk_frame L c p) (fk_fsize c)) (List.filter (isfk c) fk_kept) (fk_nframes c) h NP) as (j & Hj & FREE & BUSY).
  - apply NoDup_filter. exact fk_kept_NoDup.
  - intros p1 p2 _ _ E. injection E as E. exact (fk_frame_inj L c p1 p2 ltac:(lia) E).
  - intros p Hp B. apply filter_In. split; [| apply isfk_FKB]. unfold busy in B. apply negb_true_iff in B. apply Z.eqb_neq in B.
    unfold gfl' in B. destruct (gfreed bot cur (gfl c p) (grs c p)) eqn:GF; [exfalso; apply B; reflexivity|].
    destruct (gfl_block c p Hc Hp B) as [IN _]. apply fk_kept_In. split; [exact IN|]. rewrite <- (gfreed_dead c p Hc Hp B). exact GF.
  - pose proof (fk_count_filter_le c (fun b => negb (fk_dead b)) LB) as LE. unfold fk_count, fk_kept in *. lia.
  - exists j. split; [exact Hj|].
    assert (PJ : forall t, 0 <= (h + t) mod fk_nframes c < fk_nframes c) by (intros t; apply Z.mod_pos_bound; exact NP).
    split; [| split].
    + intros t Ht. specialize (BUSY t Ht). unfold busy in BUSY. apply negb_true_iff in BUSY. apply Z.eqb_neq in BUSY. exact BUSY.
    + unfold busy in FREE. apply negb_false_iff in FREE. apply Z.eqb_eq in FREE. apply bv_eq. rewrite FREE. reflexivity.
    + intros Hin. apply fk_kept_In in Hin as [IN ALIVE].
      pose proof AF as (_ & _ & _ & _ & _ & _ & _ & _ & LV & _). destruct (LV _ _ _ IN) as (_ & _ & pos' & Hp' & HF' & B1).
      apply (fk_frame_inj L c _ _ ltac:(lia)) in HF'. subst pos'.
      assert (E1 : gfl c ((h + j) mod fk_nframes c) = Z_to_bv 8 1) by (unfold gfl; rewrite B1; reflexivity).
      assert (NZ : bv_unsigned (gfl c ((h + j) mod fk_nframes c)) <> 0) by (rewrite E1; discriminate).
      unfold busy in FREE. apply negb_false_iff in FREE. apply Z.eqb_eq in FREE. unfold gfl' in FREE.
      rewrite (gfreed_dead c _ Hc (PJ j) NZ), ALIVE in FREE. rewrite E1 in FREE. discriminate FREE.
Qed.

Lemma afake_after_gc : forall (m' : amem) (c0 pos0 : Z) (h0' h1' h2' : word) (hs' : list byte),
  0 <= c0 < 11 -> 0 <= pos0 < gcN c0 ->
  wmono bsegs m m' ->
  afake_cells L m' -> rw_cells bsegs m' (al_fake L + 88) [C8 (Z_to_bv 64 20)] ->
  rw_cells bsegs m' (al_fake L) [C8 h0'; C8 h1'; C8 h2'; CB 64 hs'] ->
  rw_cells bsegs m' (al_fake L + 96) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m' (fk_flag L c0 pos0) [C1 (Z_to_bv 8 1)] ->
  (forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> (c, p) <> (c0, pos0) ->
       rw_cells bsegs m' (gflag (al_fake L) c p) [C1 (gfl' gfl grs bot cur c p)]) ->
  ~ In (FKB c0 (fk_frame L c0 pos0) (fk_fsize c0)) fk_kept ->
  rw_cells bsegs m' (al_t L + 72) [C8 (Z_to_bv 64 (al_fake L))] ->
  AFAKE (gb:=false) L (FKB c0 (fk_frame L c0 pos0) (fk_fsize c0) :: fk_kept) m'.
Proof.
  intros m' c0 pos0 h0' h1' h2' hs' Hc0 Hp0 WM CE' LOG' HNT' NGC' FL1 FLAGS' NOTIN TFS'.
  pose proof AF as (G & _ & _ & _ & _ & DC1 & DC2 & FL & LV & TFSC).
  pose proof G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & _ & _ & _). unfold AIMG_HI, FAKESZ in *.
  assert (SHLO : 0x631000 <= shad (al_fake L)).
  { rewrite gc_shad_eq. pose proof G2 as G2c. unfold ablk, AIMG_HI, KLS in G2c. clear - G2c. Z.div_mod_to_equations. lia. }
  assert (HIGH : forall c p, 0 <= c < 11 -> 0 <= p < gcN c -> 0x631000 <= fk_flag L c p).
  { intros c p Hc Hp. pose proof (fk_flag_range L c p Hc Hp). lia. }
  split; [exact G|]. split; [exact CE'|]. split; [exists h0', h1', h2', hs'; exact HNT'|]. split; [exact LOG'|]. split; [exact NGC'|].
  split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
  split; [eapply dc_at_any; [exact DC2| exact WM| exact SHLO]|].
  split.
  -
    intros c p b Hc Hp Mb NZ.
    destruct (Z.eq_dec c c0) as [EC|NC]; [destruct (Z.eq_dec p pos0) as [EP|NP]|].
    + subst c p. left. reflexivity.
    + right. assert (NE : (c, p) <> (c0, pos0)) by congruence.
      pose proof (rw_C1_high m' _ _ (FLAGS' c p Hc Hp NE) (HIGH c p Hc Hp)) as M2. rewrite gflag_fk in M2. rewrite M2 in Mb. injection Mb as <-.
      unfold gfl' in NZ. destruct (gfreed bot cur (gfl c p) (grs c p)) eqn:GF; [exfalso; apply NZ; reflexivity|].
      assert (NZ2 : bv_unsigned (gfl c p) <> 0) by (intros E0; apply NZ; apply bv_eq; rewrite E0; reflexivity).
      destruct (gfl_block c p Hc Hp NZ2) as [IN _]. apply fk_kept_In. split; [exact IN|]. rewrite <- (gfreed_dead c p Hc Hp NZ2). exact GF.
    + right. assert (NE : (c, p) <> (c0, pos0)) by congruence.
      pose proof (rw_C1_high m' _ _ (FLAGS' c p Hc Hp NE) (HIGH c p Hc Hp)) as M2. rewrite gflag_fk in M2. rewrite M2 in Mb. injection Mb as <-.
      unfold gfl' in NZ. destruct (gfreed bot cur (gfl c p) (grs c p)) eqn:GF; [exfalso; apply NZ; reflexivity|].
      assert (NZ2 : bv_unsigned (gfl c p) <> 0) by (intros E0; apply NZ; apply bv_eq; rewrite E0; reflexivity).
      destruct (gfl_block c p Hc Hp NZ2) as [IN _]. apply fk_kept_In. split; [exact IN|]. rewrite <- (gfreed_dead c p Hc Hp NZ2). exact GF.
  -
    split; [| exact TFS'].
    intros c F n [E|Hin].
    + injection E as <- <- <-. split; [exact Hc0|]. split; [reflexivity|]. exists pos0. split; [exact Hp0|]. split; [reflexivity|].
      exact (rw_C1_high m' _ _ FL1 (HIGH c0 pos0 Hc0 Hp0)).
    + apply fk_kept_In in Hin as [IN ALIVE]. destruct (LV c F n IN) as (Hc & Hn & pos' & Hp' & HF' & B1).
      split; [exact Hc|]. split; [exact Hn|]. exists pos'. split; [exact Hp'|]. split; [exact HF'|].
      assert (NE : (c, pos') <> (c0, pos0)).
      { intros E. injection E as -> ->. apply NOTIN. apply fk_kept_In. split; [| rewrite <- HF', <- Hn; exact ALIVE]. rewrite <- HF', <- Hn. exact IN. }
      pose proof (rw_C1_high m' _ _ (FLAGS' c pos' Hc Hp' NE) (HIGH c pos' Hc Hp')) as M2. rewrite gflag_fk in M2. rewrite M2. f_equal.
      assert (E1 : gfl c pos' = Z_to_bv 8 1) by (unfold gfl; rewrite B1; reflexivity).
      assert (NZ2 : bv_unsigned (gfl c pos') <> 0) by (rewrite E1; discriminate).
      unfold gfl'. rewrite (gfreed_dead c pos' Hc Hp' NZ2). rewrite <- HF', <- Hn, ALIVE. exact E1.
Qed.
End G.

Section W.
Variables (fs : Z) (fl : Z -> Z -> byte) (rs : Z -> Z -> Z) (bot cur : Z).
Hypothesis FLO : ablk fs (fs + 11571200).
Hypothesis FHI : fs + 11571200 <= ATOP.
Hypothesis FAL : fs mod 4096 = 0.

Lemma gcW1_hulls : forall c q, 0 <= c < 11 -> 0 <= q < gcN c ->
  fs + 4096 <= gflag fs c q /\ gflag fs c q + 1 <= fs + 36864
  /\ shad (fs + 36864) <= shad (gframe fs c q) /\ shad (gframe fs c q) + 8 * 2 ^ c <= shad (fs + 11571200).
Proof.
  intros c q C Q. pose proof (ablk_lin _ _ FLO) as (_ & F0 & _ & _). pose proof (gc_geo fs c q C Q F0) as (G1 & G2 & G3).
  pose proof (gc_pows c C) as (_ & _ & _ & _ & P8 & PC). split; [lia|]. split; [lia|]. rewrite !gc_shad_eq.
  remember (gframe fs c q) as F. remember (2 ^ c) as K. clear - G2 G3 P8 PC F0 FAL. Z.div_mod_to_equations. lia.
Qed.

Lemma gcWall_disj_hulls : forall A k, 0 <= k ->
  (A + k <= fs + 4096 \/ fs + 36864 <= A) -> (A + k <= shad (fs + 36864) \/ shad (fs + 11571200) <= A) ->
  disjoint_from (gcWall fs fl rs bot cur 0 GC_NCLS) A k.
Proof.
  intros A k K H1 H2. apply gcWall_disjoint; [lia| rewrite GC_NCLS_eq; lia|].
  intros c q C Q _. rewrite GC_NCLS_eq in C. pose proof (gcW1_hulls c q ltac:(lia) Q) as (X1 & X2 & X3 & X4).
  cbn [gcW1 disjoint_from]. split; [lia|]. split; [lia| exact I].
Qed.

Lemma gcWall_disj_kept_shadow : forall c' p A k, 0 <= c' < 11 -> 0 <= p < gcN c' -> gfreed bot cur (fl c' p) (rs c' p) = false ->
  shad (gframe fs c' p) <= A -> A + k <= shad (gframe fs c' p) + 8 * 2 ^ c' -> 0 <= k ->
  disjoint_from (gcWall fs fl rs bot cur 0 GC_NCLS) A k.
Proof.
  intros c' p A k C' P NF A0 A1 K. apply gcWall_disjoint; [lia| rewrite GC_NCLS_eq; lia|].
  intros c q C Q GF. rewrite GC_NCLS_eq in C.
  assert (NE : (c, q) <> (c', p)) by (intros E; injection E as -> ->; congruence).
  eapply disjoint_from_sub; [exact (gcW1_disj_shadow2 fs FLO FHI c q c' p ltac:(lia) Q C' P NE)| lia| lia| lia].
Qed.
Lemma gcWall_disj_kept_flag : forall c' p, 0 <= c' < 11 -> 0 <= p < gcN c' -> gfreed bot cur (fl c' p) (rs c' p) = false ->
  disjoint_from (gcWall fs fl rs bot cur 0 GC_NCLS) (gflag fs c' p) 1.
Proof.
  intros c' p C' P NF. apply gcWall_disjoint; [lia| rewrite GC_NCLS_eq; lia|].
  intros c q C Q GF. rewrite GC_NCLS_eq in C.
  assert (NE : (c, q) <> (c', p)) by (intros E; injection E as -> ->; congruence).
  exact (gcW1_disj_flag2 fs FLO FHI c q c' p ltac:(lia) Q C' P NE).
Qed.

Lemma gcW_Forall : forall (P : Z * Z -> Prop) c (flc : Z -> byte) (rsc : Z -> Z) n i,
  (forall q, i <= q < i + Z.of_nat n -> gfreed bot cur (flc q) (rsc q) = true -> Forall P (gcW1 fs c q)) ->
  Forall P (gcW fs c flc rsc bot cur i n).
Proof.
  intros P c flc rsc n. induction n as [|n IH]; intros i H; cbn [gcW]; [constructor|].
  apply Forall_app. split.
  - destruct (gfreed bot cur (flc i) (rsc i)) eqn:GF; [apply H; [lia| exact GF]| constructor].
  - apply IH. intros q Hq GF. apply H; [lia| exact GF].
Qed.
Lemma gcWall_Forall : forall (P : Z * Z -> Prop) k c, 0 <= c -> c + Z.of_nat k <= 11 ->
  (forall c' q, c <= c' < c + Z.of_nat k -> 0 <= q < gcN c' -> gfreed bot cur (fl c' q) (rs c' q) = true -> Forall P (gcW1 fs c' q)) ->
  Forall P (gcWall fs fl rs bot cur c k).
Proof.
  intros P k. induction k as [|k IH]; intros c C0 CK H; cbn [gcWall]; [constructor|].
  apply Forall_app. split.
  - apply gcW_Forall. intros q Hq GF. apply H; [lia| | exact GF].
    assert (0 < gcN c) by (unfold gcN; apply Z.pow_pos_nonneg; lia). rewrite Z2Nat.id in Hq by lia. lia.
  - apply IH; [lia| lia|]. intros c' q Hc' Hq GF. apply H; [lia| exact Hq| exact GF].
Qed.
End W.

Lemma gcWall_aext : forall L fl rs bot cur,
  ablk (al_fake L) (al_fake L + 11571200) -> al_fake L + 11571200 <= ATOP -> al_fake L mod 4096 = 0 ->
  Forall (aext L) (gcWall (al_fake L) fl rs bot cur 0 GC_NCLS).
Proof.
  intros L fl rs bot cur FLO FHI FAL. apply gcWall_Forall; [lia| rewrite GC_NCLS_eq; lia|].
  intros c q C Q _. rewrite GC_NCLS_eq in C. pose proof (gcW1_hulls (al_fake L) FLO FAL c q ltac:(lia) Q) as (X1 & X2 & X3 & X4).
  pose proof (ablk_lin _ _ FLO) as (_ & F0 & _ & _).
  assert (SH : shad (al_fake L) <= shad (al_fake L + 36864) /\ shad (al_fake L + 11571200) = shad (al_fake L) + shlen 11571200).
  { rewrite !gc_shad_eq. replace (shlen 11571200) with 1446400 by reflexivity. clear - F0 FAL. Z.div_mod_to_equations. lia. }
  unfold gcW1. constructor; [| constructor; [| constructor]]; unfold aext; cbn [fst snd]; intros _.
  - left. lia.
  - right; left. lia.
Qed.
End CANSEC1.
End TwinB.
