(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AInvWfp.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.  (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)

Section MemFacts.
  Context (segs : list Segment).

  Lemma wz_inj : forall a b, 0 <= a < 2^64 -> 0 <= b < 2^64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
  Proof.
    intros a b Ha Hb E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
    unfold bv_wrap in E. change (bv_modulus 64) with (2^64) in E. rewrite !Z.mod_small in E by lia. exact E.
  Qed.

  (* [comment removed for export] *)
  Lemma junk_at_agree : forall (m m' : mem) a n,
    junk_at segs m a n -> (forall i, 0 <= i < n -> m' (wz (a + i)) = m (wz (a + i))) -> junk_at segs m' a n.
  Proof. (intros m m' a n; (first [ intro dR_108; dex1 dR_108 as bs; destruct dR_108 as [L B] | intro dR_108; dand3 dR_108 as bs L B | intros (bs & L & B) ]); intros AG). exists bs. split; [exact L|]. eapply bytes_at_agree_gen; [exact B|]. intros; apply AG; lia. Qed.
  Lemma fill_at_agree : forall (m m' : mem) a n v,
    fill_at segs m a n v -> (forall i, 0 <= i < n -> m' (wz (a + i)) = m (wz (a + i))) -> fill_at segs m' a n v.
  Proof.
    intros m m' a n v F AG. unfold fill_at in *. eapply bytes_at_agree_gen; [exact F|].
    intros i Hi. rewrite repeat_length in Hi. apply AG. lia.
  Qed.
  Lemma u64_at_agree : forall (m m' : mem) a v, u64_at segs m a v -> (forall i, 0 <= i < 8 -> m' (wz (a + i)) = m (wz (a + i))) -> u64_at segs m' a v.
  Proof. intros m m' a v F AG. unfold u64_at in *. eapply bytes_at_agree_gen; [exact F|]. intros i Hi. rewrite length_le8 in Hi. apply AG; lia. Qed.
  Lemma u32_at_agree : forall (m m' : mem) a v, u32_at segs m a v -> (forall i, 0 <= i < 4 -> m' (wz (a + i)) = m (wz (a + i))) -> u32_at segs m' a v.
  Proof. intros m m' a v F AG. unfold u32_at in *. eapply bytes_at_agree_gen; [exact F|]. intros i Hi. rewrite length_le4 in Hi. apply AG; lia. Qed.
  Lemma u16_at_agree : forall (m m' : mem) a v, u16_at segs m a v -> (forall i, 0 <= i < 2 -> m' (wz (a + i)) = m (wz (a + i))) -> u16_at segs m' a v.
  Proof. intros m m' a v F AG. unfold u16_at in *. eapply bytes_at_agree_gen; [exact F|]. intros i Hi. rewrite length_le2 in Hi. apply AG; lia. Qed.
  Lemma u8_at_agree : forall (m m' : mem) a v, u8_at segs m a v -> m' (wz a) = m (wz a) -> u8_at segs m' a v.
  Proof. intros m m' a v F AG. unfold u8_at in *. eapply bytes_at_agree_gen; [exact F|]. intros i Hi. cbn in Hi. replace i with 0 by lia. rewrite Z.add_0_r. exact AG. Qed.
  Lemma wr_at_agree : forall (m m' : mem) a n,
    wr_at segs m a n -> (forall i, 0 <= i < n -> m' (wz (a + i)) = m (wz (a + i))) -> wr_at segs m' a n.
  Proof.
    (intros m m' a n; (first [ intro dR_109; dand3 dR_109 as H0 H1 W | intros (H0 & H1 & W) ]); intros AG). split; [exact H0|]. split; [exact H1|].
    intros i Hi. unfold wview, wa in *. rewrite (AG i Hi). apply W. exact Hi.
  Qed.
  Lemma rw_cells_agree : forall (m m' : mem) a cs,
    rw_cells segs m a cs -> (forall i, 0 <= i < Z.of_nat (cells_size cs) -> m' (wz (a + i)) = m (wz (a + i))) -> rw_cells segs m' a cs.
  Proof.
    intros m m' a cs [[WFc B] W] AG. split; [split; [exact WFc|]|].
    - eapply bytes_at_agree_gen; [exact B|]. rewrite cells_bytes_length by exact WFc. exact AG.
    - eapply wr_at_agree; [exact W| exact AG].
  Qed.
  (* [comment removed for export] *)
  Lemma mapped_mono : forall (m m' : mem) a n,
    mapped m a n -> (forall i, 0 <= i < n -> m (wz (a + i)) <> None -> m' (wz (a + i)) <> None) -> mapped m' a n.
  Proof. intros m m' a n M NN i Hi. apply NN; [exact Hi|]. apply M. exact Hi. Qed.
  (* [comment removed for export] *)
  Lemma junk_at_of_mapped : forall (m : mem) a n,
    0 <= a -> 0 <= n -> a + n <= 2^64 -> mapped m a n -> junk_at segs m a n.
  Proof.
    intros m a n Ha Hn Htop M.
    exists (map (fun i => match m (wz (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 (Z.to_nat n))).
    rewrite map_length, seq_length. split; [lia|]. split; [lia|]. split; [rewrite map_length, seq_length; lia|].
    intros i Hi. rewrite map_length, seq_length in Hi.
    rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec i (Z.to_nat n)); [|lia]. cbn [option_map Nat.add].
    unfold mrd, wa. specialize (M (Z.of_nat i) ltac:(lia)). destruct (m (wz (a + Z.of_nat i))); [reflexivity| congruence].
  Qed.
  (* [comment removed for export] *)
End MemFacts.

(* [comment removed for export] *)
Lemma mapped_view_iff : forall H m a n, zrange_visible H a n -> mapped (mrestrict H m) a n <-> mapped m a n.
Proof.
  intros H m a n Hv. unfold mapped. split; intros M i Hi; specialize (M i Hi); specialize (Hv i Hi);
  unfold mrestrict in *; unfold wa in Hv; rewrite Hv in *; exact M.
Qed.
Lemma view_visible : forall H (m : mem) a, H (wz a) = false -> mrestrict H m (wz a) = m (wz a).
Proof. intros. unfold mrestrict. rewrite H0. reflexivity. Qed.
(* [comment removed for export] *)
Lemma view_some_visible : forall H (m : mem) (x : word), mrestrict H m x <> None -> H x = false.
Proof. intros H m x. unfold mrestrict. destruct (H x); [congruence| reflexivity]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_hull_of : forall R b s, In (b, s) R -> In (b, b + s) (hull_of R).
Proof. intros R b s H. unfold hull_of. apply in_map_iff. exists (b, s). split; [reflexivity|exact H]. Qed.

Section Pasan.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
Context {DR : DepotRep}.
#[local] Notation WF := (WF AL_pboth).   (* [comment removed for export] *)

(* [comment removed for export] *)

Lemma pa_hull_region : forall A b s, In (b, s) (aregions AL_pboth A) -> In (b, b + s) (pa_hull A).
Proof. intros A b s H. unfold pa_hull, ahull_of, ahull_of_. apply in_or_app. right. apply in_or_app. left. apply in_hull_of. exact H. Qed.
(* [comment removed for export] *)
Lemma pa_hull_extra : forall A lo hi, In (lo, hi) (p_extra (a_pl A)) -> In (lo, hi) (pa_hull A).
Proof. intros A lo hi H. unfold pa_hull, ahull_of, ahull_of_. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fixed_in_aregions : forall A r, In r (fixed_regions_ AL_pboth (a_pl A)) -> In r (aregions AL_pboth A).
Proof. intros A r H. unfold aregions, aregions_. apply in_or_app. left. exact H. Qed.
Lemma sec_in_aregions : forall A r, In r (sec_regions_ (sr_chunks (a_sec A))) -> In r (aregions AL_pboth A).
Proof. intros A r H. unfold aregions, aregions_. apply in_or_app. right. apply in_or_app. right. exact H. Qed.
Lemma classes_regions_in : forall sb reg n r c, (1 <= c)%nat -> (c <= n)%nat ->
  In r (class_regions_ sb (reg (Z.of_nat c)) (Z.of_nat c)) -> In r (classes_regions_ sb reg n).
Proof.
  intros sb reg n. induction n as [|n IH]; intros r c H1 H2 Hr; [lia|].
  cbn [classes_regions_]. apply in_or_app. destruct (Nat.eq_dec c (S n)) as [->|NE]; [right; exact Hr|].
  left. apply (IH r c); [lia|lia|exact Hr].
Qed.
Lemma class_in_aregions : forall A r c, 1 <= c <= 31 ->
  In r (class_regions_ (a_sb A) (a_reg A c) c) -> In r (aregions AL_pboth A).
Proof.
  intros A r c Hc Hr. unfold aregions, aregions_. apply in_or_app. right. apply in_or_app. left.
  unfold a_sb in Hr. replace c with (Z.of_nat (Z.to_nat c)) in Hr by lia.
  apply (classes_regions_in _ _ 31 r (Z.to_nat c)); [lia|lia|exact Hr].
Qed.

(* [comment removed for export] *)
Lemma visible_of_region : forall A b s a n,
  In (b, s) (aregions AL_pboth A) -> b <= a -> a + n <= b + s -> 0 <= a -> b + s <= 2^64 ->
  zrange_visible (hidc (pa_hull A)) a n.
Proof. intros A b s a n Hin Hlo Hhi H0 Htop. eapply zrange_visible_hidc; [apply pa_hull_region; exact Hin| | |exact H0|exact Htop]; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sb_facts : forall A, WF A ->
  a_sb A = space_beg_of (a_b6 A) /\ a_sb A mod 0x10000 = 0 /\ kHighMemBeg <= a_b6 A /\ a_b6 A < a_sb A <= a_b6 A + 0x10000 /\
  a_sb A + kSpaceSize + 4096 <= alloc_ceiling.
Proof.
  intros A W. (first [ pose proof ((wfP A W)) as dR_1; dand5 dR_1 as Hb6 Hhi Hsb Hce _ | destruct (wfP A W) as (Hb6 & Hhi & Hsb & Hce & _) ]).
  pose proof (space_beg_aligned (a_b6 A) Hb6). pose proof (space_beg_range (a_b6 A) Hb6).
  unfold a_sb, a_b6, p_sb in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
Qed.

Lemma region_piece_bounds : forall A c, WF A -> 1 <= c <= 30 ->
  let R := a_reg A c in let rb := region_beg (a_sb A) c in
  kHighMemBeg <= rb /\ a_sb A <= rb /\ 0 <= rg_allocated_user R <= rg_mapped_user R /\ rb + rg_mapped_user R <= rb + kFreeArrayOffset /\
  0 <= rg_mapped_fa R /\ rb + kFreeArrayOffset + rg_mapped_fa R <= rb + kRegionSize /\
  rb + kRegionSize <= a_sb A + kSpaceSize /\ a_sb A + kSpaceSize + 4096 <= alloc_ceiling /\ rb mod 0x10000 = 0 /\
  rg_mapped_user R mod 8 = 0 /\ rg_allocated_user R mod 8 = 0 /\ rg_mapped_fa R mod 8 = 0.
Proof.
  intros A c W Hc. (first [ pose proof ((sb_facts A W)) as dR_2; dand5 dR_2 as E AL HB RG CE | pose proof (sb_facts A W) as (E & AL & HB & RG & CE) ]). set (sb := a_sb A) in *.
  (first [ pose proof ((wfR A W)) as dR_3; dand3 dR_3 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]). specialize (WR c Hc). (first [ dand8 WR as A1 A2 A3 A4 A5 A6 A7 _ | destruct WR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _) ]).
  pose proof (class_size_mod32 c Hc) as CM. pose proof (class_size_range c Hc) as CR.
  cbv zeta. unfold region_beg, kRegionSize, kSpaceSize, kFreeArrayOffset, kFreeArraySize, kHighMemBeg, kUserMapSize, kFreeArrayMapSize in *.
  assert (M1 : (sb + c * 2 ^ 32) mod 0x10000 = 0) by
    (rewrite Z.add_mod, AL by lia; replace (c * 2^32) with ((c * 2^16) * 0x10000) by lia; rewrite Z_mod_mult; reflexivity).
  assert (M2 : rg_mapped_user (a_reg A c) mod 8 = 0) by (apply (mod0_down _ (2^18) 8); [exists (2^15); reflexivity| exact A3]).
  assert (M3 : rg_allocated_user (a_reg A c) mod 8 = 0).
  { apply (mod0_down _ (class_size c) 8); [|exact A4]. apply (Z.divide_trans _ 32); [exists 4; reflexivity|]. apply Z.mod_divide; [lia| exact CM]. }
  assert (M4 : rg_mapped_fa (a_reg A c) mod 8 = 0) by (apply (mod0_down _ (2^18) 8); [exists (2^15); reflexivity| exact A6]).
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try nia; assumption.
Qed.

(* [comment removed for export] *)
Lemma paid_sum_nonneg : forall paid n, (n <= 30)%nat -> 0 <= paid_sum_ paid n.
Proof.
  intros paid n. induction n as [|n IH]; intros Hn; [cbn; lia|]. cbn [paid_sum_].
  pose proof (class_size_range (Z.of_nat (S n)) ltac:(lia)) as CR. specialize (IH ltac:(lia)). nia.
Qed.
Lemma paid_sum_term : forall paid n c, (n <= 30)%nat -> 1 <= c <= Z.of_nat n ->
  class_size c * Z.of_nat (length (paid c)) <= paid_sum_ paid n.
Proof.
  intros paid n. induction n as [|n IH]; intros c Hn Hc; [lia|]. cbn [paid_sum_].
  pose proof (class_size_range (Z.of_nat (S n)) ltac:(lia)) as CR. pose proof (paid_sum_nonneg paid n ltac:(lia)) as NN.
  destruct (Z.eq_dec c (Z.of_nat (S n))) as [->|NE]; [nia|].
  specialize (IH c ltac:(lia) ltac:(lia)). nia.
Qed.
Lemma wf_paid_le : forall A c, WF A -> 1 <= c <= 30 -> 0 <= class_size c * Z.of_nat (length (a_paid A c)) <= PRIMCRED0.
Proof.
  intros A c W Hc. (first [ pose proof ((wfN A W)) as dR_90; dand3 dR_90 as P0 PS _ | destruct (wfN A W) as (P0 & PS & _) ]).
  pose proof (paid_sum_term (a_paid A) 30 c ltac:(lia) ltac:(cbn; lia)) as T. pose proof (class_size_range c Hc) as CR. nia.
Qed.
Lemma wf_au_cap : forall A c, WF A -> 1 <= c <= 30 ->
  rg_allocated_user (a_reg A c) <= kAuCap - 2^27 /\ rg_mapped_user (a_reg A c) <= kAuCap - 2^26.
Proof.
  intros A c W Hc. pose proof (wf_paid_le A c W Hc) as [_ PL]. pose proof (class_size_range c Hc) as CR. pose proof (class_slack_range c) as SL.
  (first [ pose proof ((wfR A W)) as dR_91; dand3 dR_91 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]).
  (first [ pose proof ((WR c Hc)) as dR_92; dand12 dR_92 as A1 _ _ _ _ _ _ _ _ _ A11 _ | destruct (WR c Hc) as (A1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & A11 & _) ]).
  rewrite PRIMCRED0_eq in PL. unfold kAuCap, kUserMapSize, kMaxSize, kQuarantineMaxSize, kQuarantineCacheSize in *. nia.
Qed.

(* [comment removed for export] *)
Lemma wf_region_mono_na : forall c R na na', 1 <= c <= 30 -> na <= na' -> wf_region c R na -> wf_region c R na'.
Proof.
  intros c R na na' Hc LE WR. pose proof (class_size_range c Hc) as CR.
  destruct WR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
  unfold wf_region. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
  split; [exact A7|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|]. split; [nia| exact A12].
Qed.
Lemma paid_sum_add : forall paid c k n,
  paid_sum_ (paid_add paid c k) n = paid_sum_ paid n + (if andb (1 <=? c) (c <=? Z.of_nat n) then class_size c else 0).
Proof.
  intros paid c k n. induction n as [|n IH]; cbn [paid_sum_].
  - destruct (1 <=? c) eqn:E1; destruct (c <=? Z.of_nat 0) eqn:E2; cbn [andb]; try lia. apply Z.leb_le in E1. apply Z.leb_le in E2. cbn in E2. lia.
  - rewrite IH. destruct (Z.eq_dec c (Z.of_nat (S n))) as [E|NE].
    + rewrite <- E. rewrite paid_add_eq. cbn [length]. rewrite Nat2Z.inj_succ.
      replace ((1 <=? c) && (c <=? Z.of_nat n))%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.leb_gt; lia).
      replace ((1 <=? c) && (c <=? c))%bool with true by (symmetry; apply Bool.andb_true_iff; split; apply Z.leb_le; lia).
      nia.
    + rewrite paid_add_ne by (intros X; apply NE; symmetry; exact X).
      destruct (1 <=? c) eqn:E1; cbn [andb]; [| lia].
      destruct (c <=? Z.of_nat n) eqn:E2; destruct (c <=? Z.of_nat (S n)) eqn:E3; try lia.
      * apply Z.leb_le in E2. apply Z.leb_gt in E3. lia.
      * apply Z.leb_gt in E2. apply Z.leb_le in E3. lia.
Qed.
Lemma paid_sum_add_30 : forall paid c k, 1 <= c <= 30 -> paid_sum_ (paid_add paid c k) 30 = paid_sum_ paid 30 + class_size c.
Proof.
  intros paid c k Hc. rewrite paid_sum_add. destruct (1 <=? c) eqn:E1; [| apply Z.leb_gt in E1; lia].
  destruct (c <=? Z.of_nat 30) eqn:E2; [reflexivity| apply Z.leb_gt in E2; cbn in E2; lia].
Qed.
Lemma wf_regions_paid_add : forall reg paid ci c k, 1 <= c <= 30 -> wf_regions_ reg paid ci -> wf_regions_ reg (paid_add paid c k) ci.
Proof.
  intros reg paid ci c k Hc (R1 & R2 & R3). split; [| exact (conj R2 R3)].
  intros c' Hc'. unfold paid_add. destruct (Z.eqb_spec c' c) as [->|NE]; [| exact (R1 c' Hc')].
  cbn [length]. rewrite Nat2Z.inj_succ. apply (wf_region_mono_na c (reg c) (Z.of_nat (length (paid c)))); [exact Hc| lia| exact (R1 c Hc)].
Qed.
Lemma p_live_insert_inv : forall (lm : gmap Z liveinfo) u li c k, lm !! u = None ->
  p_live_ (<[u := li]> lm) c k -> p_live_ lm c k \/ li_chunk li = ChP (CP c k).
Proof.
  intros lm u li c k FR (u0 & n0 & H). destruct (decide (u0 = u)) as [->|NE].
  - rewrite lookup_insert_eq in H. injection H as ->. right. reflexivity.
  - rewrite lookup_insert_ne in H by congruence. left. exists u0, n0. exact H.
Qed.
Lemma p_live_delete_inv : forall (lm : gmap Z liveinfo) u c k, p_live_ (delete u lm) c k -> p_live_ lm c k.
Proof. intros lm u c k (u0 & n0 & H). rewrite lookup_delete_Some in H. destruct H as [_ H]. exists u0, n0. exact H. Qed.
Lemma wf_prim_mono : forall (lm lm' : gmap Z liveinfo) qt qt' qg qg' paid pcred,
  (forall c k, 1 <= c <= 30 -> p_live_ lm' c k \/ p_quar_ qt' qg' c k -> p_live_ lm c k \/ p_quar_ qt qg c k) ->
  wf_prim_ lm qt qg paid pcred -> wf_prim_ lm' qt' qg' paid pcred.
Proof.
  intros lm lm' qt qt' qg qg' paid pcred INC (P0 & PS & PD). split; [exact P0|]. split; [exact PS|].
  intros c k Hc H. exact (PD c k Hc (INC c k Hc H)).
Qed.
(* [comment removed for export] *)
Lemma wf_prim_hit : forall (lm : gmap Z liveinfo) qt qg paid pcred u c k n, 1 <= c <= 30 ->
  wf_prim_ lm qt qg paid pcred -> class_size c <= pcred -> lm !! u = None ->
  wf_prim_ (<[u := LI (ChP (CP c k)) n]> lm) qt qg (paid_add paid c k) (pcred - class_size c).
Proof.
  intros lm qt qg paid pcred u c k n Hc (P0 & PS & PD) LE FR. pose proof (class_size_range c Hc) as CR.
  split; [lia|]. split; [rewrite (paid_sum_add_30 paid c k Hc); lia|].
  intros c' k' Hc' [V|Q].
  - destruct (p_live_insert_inv lm u _ c' k' FR V) as [V0|E].
    + apply paid_add_incl. exact (PD c' k' Hc' (or_introl V0)).
    + cbn [li_chunk] in E. injection E as -> ->. rewrite paid_add_eq. left. reflexivity.
  - apply paid_add_incl. exact (PD c' k' Hc' (or_intror Q)).
Qed.
(* [comment removed for export] *)
Lemma wf_prim_qsame : forall (lm : gmap Z liveinfo) qt qt' qg qg' paid pcred,
  (forall e, In e (q_entries (qt' ++ qg')) -> In e (q_entries (qt ++ qg))) ->
  wf_prim_ lm qt qg paid pcred -> wf_prim_ lm qt' qg' paid pcred.
Proof.
  intros lm qt qt' qg qg' paid pcred INC W. apply (wf_prim_mono lm lm qt qt' qg qg' paid pcred); [| exact W].
  intros c k Hc [V|[n Hn]]; [left; exact V| right]. exists n. apply INC. exact Hn.
Qed.

Lemma carved_chunk_bounds : forall A c k, WF A -> 1 <= c <= 30 -> 0 <= k < carved_count A c ->
  let rb := region_beg (a_sb A) c in
  rb <= chunk_addr (a_sb A) c k /\ chunk_addr (a_sb A) c k + class_size c <= rb + rg_allocated_user (a_reg A c) /\
  chunk_addr (a_sb A) c k mod 32 = 0 /\ 32 <= class_size c <= kMaxSize.
Proof.
  intros A c k W Hc Hk. pose proof (class_size_range c Hc) as CS. (first [ pose proof ((sb_facts A W)) as dR_5; dand3 dR_5 as _ AL _ | pose proof (sb_facts A W) as (_ & AL & _) ]).
  (first [ pose proof ((wfR A W)) as dR_6; dand3 dR_6 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]). (first [ pose proof ((WR c Hc)) as dR_7; dand5 dR_7 as A1 _ _ A4 _ | destruct (WR c Hc) as (A1 & _ & _ & A4 & _) ]).
  cbv zeta. unfold carved_count, carved_count_ in Hk. unfold chunk_addr.
  pose proof (Z_div_mod_eq_full (rg_allocated_user (a_reg A c)) (class_size c)) as DM. rewrite A4, Z.add_0_r in DM.
  split; [nia|]. split; [nia|]. split; [apply chunk_addr_mod32; [exact Hc|lia|exact AL]| lia].
Qed.
(* [comment removed for export] *)
Lemma carved_chunks_disjoint : forall sb c k k', 1 <= c <= 30 -> 0 <= k -> 0 <= k' -> k <> k' ->
  chunk_addr sb c k + class_size c <= chunk_addr sb c k' \/ chunk_addr sb c k' + class_size c <= chunk_addr sb c k.
Proof. intros sb c k k' Hc Hk Hk' NE. pose proof (class_size_range c Hc). unfold chunk_addr. destruct (Z.lt_ge_cases k k'); [left|right]; nia. Qed.
(* [comment removed for export] *)
Lemma regions_disjoint : forall sb c c', c <> c' -> 0 <= c -> 0 <= c' ->
  region_beg sb c + kRegionSize <= region_beg sb c' \/ region_beg sb c' + kRegionSize <= region_beg sb c.
Proof. intros sb c c' NE Hc Hc'. unfold region_beg, kRegionSize. destruct (Z.lt_ge_cases c c'); [left|right]; nia. Qed.

Lemma sec_chunk_bounds : forall A s, WF A -> In s (sr_chunks (a_sec A)) ->
  kMaxPrimaryUser < cs_n s < REQ_MAX /\ cs_map s mod 4096 = 0 /\ app_rangeA AL_pboth (cs_map s) (map_size (cs_n s)) /\ cs_map s + map_size (cs_n s) <= alloc_ceiling /\
  needed_size2 (cs_n s) + kPageSize <= map_size (cs_n s).   (* [comment removed for export] *)
Proof.
  intros A s W Hin. (first [ pose proof ((wfS A W)) as dR_8; dand5 dR_8 as _ _ _ WS _ | destruct (wfS A W) as (_ & _ & _ & WS & _) ]). (first [ pose proof ((WS s Hin)) as dR_9; dand4 dR_9 as B1 B2 B3 B4 | destruct (WS s Hin) as (B1 & B2 & B3 & B4) ]).
  pose proof (map_size_room (cs_n s)). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. exact B3.
Qed.

(* [comment removed for export] *)
Lemma primary_layout : forall sb c k n, 1 <= c <= 30 -> 0 <= n <= kMaxPrimaryUser -> c = class_of n ->
  let ab := chunk_addr sb c k in let u := user_of sb (ChP (CP c k)) n in
  ab + 16 <= u /\ u + n <= ab + class_size c /\ u + user_size n <= ab + class_size c /\ u + 8 <= ab + class_size c /\
  (ab <> u - 16 -> ab + 16 <= u - 16).
Proof.
  intros sb c k n Hc Hn Hcl. cbv zeta. cbn [user_of alloc_beg].
  pose proof (user_end_fits (chunk_addr sb c k) n Hn) as [F1 F2]. rewrite <- Hcl in F2.
  pose proof (rz_size_range n) as RZ. (first [ pose proof ((user_size_pos n ltac:(lia))) as dR_10; dand3 dR_10 as U1 U2 U3 | pose proof (user_size_pos n ltac:(lia)) as (U1 & U2 & U3) ]).
  pose proof (rounded_size_ge n) as [_ R8].
  unfold user_beg, needed_size in *. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros NE. pose proof (rz_size_cases n) as RC. unfold kChunkHeaderSize in *.
  destruct RC as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E in *; lia.
Qed.
Lemma secondary_layout : forall mb n, kMaxPrimaryUser < n ->
  let ab := sec_alloc_beg mb in let u := sec_user_beg mb in
  mb + kSecondaryHeaderSize <= ab /\ ab + 16 <= u - 16 /\ u + n <= mb + map_size n /\ u + user_size n <= mb + map_size n /\ ab = mb + 4096 /\ u = mb + 6144 /\
  u + 8 <= mb + map_size n.
Proof.
  intros mb n Hn. cbv zeta. pose proof (sec_user_end_fits mb n Hn) as [F1 F2]. (first [ pose proof ((user_size_pos n ltac:(unfold kMaxPrimaryUser in Hn; lia))) as dR_11; dand3 dR_11 as U1 U2 U3 | pose proof (user_size_pos n ltac:(unfold kMaxPrimaryUser in Hn; lia)) as (U1 & U2 & U3) ]).
  unfold sec_alloc_beg, sec_user_beg, kSecondaryHeaderSize, kPageSize, kMaxPrimaryUser in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
Qed.

(* [comment removed for export] *)
Lemma sh_high_range : forall a, kHighMemBeg <= a < 2^47 -> kHighShadowMapBeg <= sh a < kHighMemBeg.
Proof. intros a H. unfold sh, kHighMemBeg, kHighShadowMapBeg, kShadowOffset in *.
  assert (0x10007fff8000 / 8 <= a / 8) by (apply Z.div_le_mono; lia). assert (a / 8 <= (2^47 - 1) / 8) by (apply Z.div_le_mono; lia).
  change (0x10007fff8000 / 8) with 0x2000ffff000 in *. change ((2^47 - 1) / 8) with 17592186044415 in *. lia. Qed.
(* [comment removed for export] *)
Lemma sh_mono : forall a b, a <= b -> sh a <= sh b.
Proof. intros. unfold sh. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.
Lemma sh_add8 : forall a k, a mod 8 = 0 -> sh (a + 8 * k) = sh a + k.
Proof. intros a k H. unfold sh. pose proof (Z_div_exact_full_2 a 8 ltac:(lia) H). replace (a + 8 * k) with (k * 8 + a) by lia.
  rewrite Z.div_add_l by lia. lia. Qed.
Lemma sh_add : forall a d, a mod 8 = 0 -> d mod 8 = 0 -> sh (a + d) = sh a + d / 8.
Proof. intros a d Ha Hd. pose proof (Z_div_exact_full_2 d 8 ltac:(lia) Hd). replace (a + d) with (a + 8 * (d / 8)) by lia. apply sh_add8. exact Ha. Qed.
(* [comment removed for export] *)
Lemma app_facts : forall p n, app_rangeA AL_pboth p n ->
  4096 <= p /\ 0 <= n /\ p + n <= alloc_ceiling /\ (p + n <= 0x10000 \/ 0x60a000 <= p) /\ (p + n <= kLowShadowMapBeg \/ kHighMemBeg <= p).
Proof. intros p n H. pose proof alloc_ceiling_val. unfold app_rangeA in H. cbn [al_image_lo al_image_hi AL_pboth] in H. unfold kLowShadowMapBeg, kHighMemBeg in *. lia. Qed.
Lemma app_range_pasan : forall p n, app_rangeA AL_pboth p n <-> app_range LPA p n.
Proof. intros p n. unfold app_rangeA, app_range, app_lo, app_hi, kLowAppEnd. cbn [al_image_lo al_image_hi AL_pboth cl_image_lo cl_image_hi LPA]. tauto. Qed.
Lemma sh_lowapp_range : forall a, 4096 <= a < kLowShadowMapBeg -> 0x7fff8200 <= sh a < 0x8fff6e00.
Proof. intros a H. unfold sh, kShadowOffset, kLowShadowMapBeg in *.
  assert (4096 / 8 <= a / 8) by (apply Z.div_le_mono; lia). assert (a / 8 <= (0x7fff7000 - 1) / 8) by (apply Z.div_le_mono; lia).
  change (4096 / 8) with 512 in *. change ((0x7fff7000 - 1) / 8) with 0xfffedff in *. lia. Qed.
(* [comment removed for export] *)
Definition in_shadow_strict (a : Z) : Prop := kLowShadowBeg <= a < kShadowGapBeg \/ kHighShadowMapBeg <= a < kHighMemBeg.
Lemma strict_in_maps : forall a, in_shadow_strict a -> in_shadow_maps a.
Proof. intros a H. unfold in_shadow_strict, in_shadow_maps, kLowShadowBeg, kShadowGapBeg, kLowShadowMapBeg, kHighShadowMapBeg, kHighShadowMapSize, kHighMemBeg in *. lia. Qed.
Lemma strict_not_app : forall a, in_shadow_strict a -> ~ (0 <= a <= kLowMemEnd \/ kHighMemBeg <= a).
Proof. intros a H. unfold in_shadow_strict, kLowShadowBeg, kShadowGapBeg, kLowMemEnd, kHighShadowMapBeg, kHighMemBeg in *. lia. Qed.
(* [comment removed for export] *)
Lemma sh_iv_strict : forall b s a, b mod 8 = 0 -> s mod 8 = 0 -> 0 < s ->
  ((4096 <= b /\ b + s <= kLowShadowMapBeg) \/ (kHighMemBeg <= b /\ b + s <= 2^47)) ->
  sh b <= a < sh b + s / 8 -> in_shadow_strict a.
Proof.
  intros b s a Hb Hs Hp R Ha. pose proof (sh_add b (s - 8) Hb ltac:(rewrite Zminus_mod, Hs; reflexivity)) as E.
  replace ((s - 8) / 8) with (s / 8 - 1) in E by (replace (s - 8) with (s + (-1) * 8) by lia; rewrite Z.div_add by lia; lia).
  destruct R as [R|R].
  - pose proof (sh_lowapp_range b ltac:(lia)). pose proof (sh_lowapp_range (b + (s - 8)) ltac:(lia)). left. unfold kLowShadowBeg, kShadowGapBeg. lia.
  - pose proof (sh_high_range b ltac:(lia)). pose proof (sh_high_range (b + (s - 8)) ltac:(lia)). right. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma app_not_in_shadow_maps : forall a, (a < kLowShadowMapBeg \/ kHighMemBeg <= a) -> ~ in_shadow_maps a.
Proof. intros a H M. unfold in_shadow_maps, kLowShadowMapBeg, kHighShadowMapBeg, kHighShadowMapSize, kHighMemBeg in *. lia. Qed.
Lemma image_shadow_strict : forall a, pa_image_shadow a -> in_shadow_strict a.
Proof. intros a H. unfold pa_image_shadow in H. assert (sh 0x10000 = 0x7fffa000) by reflexivity. assert (sh 0x60a000 = 0x800b9400) by reflexivity.
  left. unfold kLowShadowBeg, kShadowGapBeg. lia. Qed.
Lemma image_shadow_in_maps : forall a, pa_image_shadow a -> in_shadow_maps a.
Proof. intros a H. apply strict_in_maps, image_shadow_strict, H. Qed.
(* [comment removed for export] *)
Lemma shadow_region_strict : forall b s z, b mod 8 = 0 -> 0 < s ->
  ((4096 <= b /\ b + s <= kLowShadowMapBeg) \/ (kHighMemBeg <= b /\ b + s <= 2^47)) ->
  fst (shadow_region b s) <= z < fst (shadow_region b s) + snd (shadow_region b s) -> in_shadow_strict z.
Proof.
  intros b s z Hb Hs R Hz. unfold shadow_region in Hz. cbn [fst snd] in Hz.
  pose proof (round_down_le (sh b) 8 ltac:(lia)) as D1. pose proof (round_down_gt (sh b) 8 ltac:(lia)) as D2. pose proof (round_down_mod (sh b) 8 ltac:(lia)) as D3.
  pose proof (round_up_ge (sh (b + s - 1) + 1) 8 ltac:(lia)) as U1. pose proof (round_up_lt (sh (b + s - 1) + 1) 8 ltac:(lia)) as U2.
  pose proof (round_up_mod (sh (b + s - 1) + 1) 8 ltac:(lia)) as U3.
  pose proof (Z_div_exact_full_2 _ 8 ltac:(lia) D3) as D4. pose proof (Z_div_exact_full_2 _ 8 ltac:(lia) U3) as U4.
  destruct R as [R|R].
  - pose proof (sh_lowapp_range b ltac:(lia)). pose proof (sh_lowapp_range (b + s - 1) ltac:(lia)). left. unfold kLowShadowBeg, kShadowGapBeg. lia.
  - pose proof (sh_high_range b ltac:(lia)). pose proof (sh_high_range (b + s - 1) ltac:(lia)). right.
    unfold kHighShadowMapBeg, kHighMemBeg in *. lia.
Qed.

(* [comment removed for export] *)
Lemma stack_shadow_iv_facts :
  fst stack_shadow_iv mod 8 = 0 /\ fst stack_shadow_iv <= sh alloc_ceiling < fst stack_shadow_iv + 8 /\
  fst stack_shadow_iv + snd stack_shadow_iv = kHighMemBeg /\ 0x10006fef8000 <= fst stack_shadow_iv.
Proof.
  pose proof alloc_ceiling_val as CE. unfold stack_shadow_iv, shadow_region. cbn [fst snd].
  replace (alloc_ceiling + (2 ^ 47 - alloc_ceiling) - 1) with (2 ^ 47 - 1) by lia.
  change (sh (2 ^ 47 - 1) + 1) with kHighMemBeg. rewrite (round_up_id kHighMemBeg 8 ltac:(lia) eq_refl).
  pose proof (round_down_le (sh alloc_ceiling) 8 ltac:(lia)) as D1. pose proof (round_down_gt (sh alloc_ceiling) 8 ltac:(lia)) as D2.
  pose proof (round_down_mod (sh alloc_ceiling) 8 ltac:(lia)) as D3. pose proof (Z_div_exact_full_2 _ 8 ltac:(lia) D3) as D4.
  assert (LO : 0x10006fef8000 <= sh alloc_ceiling < kHighMemBeg) by (unfold sh, kShadowOffset, kHighMemBeg; lia).
  unfold kHighMemBeg in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bm_nth_fixed : forall A,
  nth_error (big_maps A) 0 = Some (a_b6 A, kSpaceReserve) /\ nth_error (big_maps A) 1 = Some (a_pa A, kPtrArrayReserve) /\
  nth_error (big_maps A) 2 = Some (kHighShadowMapBeg, kHighShadowMapSize) /\ nth_error (big_maps A) 3 = Some (kLowShadowMapBeg, 0x10000000) /\
  nth_error (big_maps A) 4 = Some (a_thr A, 4096) /\ nth_error (big_maps A) 5 = Some (a_ctx A, 0x10000) /\
  nth_error (big_maps A) 6 = Some (a_fs A, kFakeStackBytes) /\ nth_error (big_maps A) 7 = Some (a_nodes0 A, kDepotNodesBlock) /\
  nth_error (big_maps A) 8 = Some (a_frames0 A, kStackStoreBlockBytes) /\ nth_error (big_maps A) 9 = Some (a_itab A, 0x38e000) /\
  nth_error (big_maps A) 10 = Some (a_m64k A, 0x10000) /\ nth_error (big_maps A) 11 = Some (p_gvec (a_pl A), 4096) /\
  nth_error (big_maps A) 12 = Some (p_dvec (a_pl A), 4096) /\ nth_error (big_maps A) 13 = Some (p_m11 (a_pl A), 4096) /\
  nth_error (big_maps A) 14 = Some (p_dtls (a_pl A), 4096).
Proof. intros A. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Lemma bm_nth_sec : forall A i s, nth_error (sr_chunks (a_sec A)) i = Some s ->
  nth_error (big_maps A) (15 + i) = Some (cs_map s, map_size (cs_n s)).
Proof.
  intros A i s H. unfold big_maps, big_maps_.
  rewrite nth_error_app2 by (cbn; lia). cbn [length Nat.sub]. rewrite Nat.sub_diag || idtac.
  replace (15 + i - 15)%nat with i by lia. rewrite nth_error_map, H. reflexivity.
Qed.
Lemma bm_sep : forall A i j bi si bj sj, WF A ->
  nth_error (big_maps A) i = Some (bi, si) -> nth_error (big_maps A) j = Some (bj, sj) -> i <> j ->
  bi + si <= bj \/ bj + sj <= bi.
Proof. intros A i j bi si bj sj W Hi Hj NE. destruct (wfM A W) as [D _]. exact (D i j bi si bj sj Hi Hj NE). Qed.
Lemma bm_bounds : forall A b s, WF A -> In (b, s) (big_maps A) -> 0 <= b /\ 0 < s /\ b + s <= 2^47.
Proof. intros A b s W H. destruct (wfM A W) as [_ B]. apply B. exact H. Qed.
Lemma In_nth_error' : forall {X} (l : list X) x, In x l -> exists i, nth_error l i = Some x.
Proof. intros X l x H. apply In_nth_error in H. exact H. Qed.

(* [comment removed for export] *)
Lemma primary_in_b6 : forall A a, WF A -> a_sb A <= a < a_sb A + kSpaceSize + 4096 -> a_b6 A <= a < a_b6 A + kSpaceReserve.
Proof. intros A a W H. (first [ pose proof ((sb_facts A W)) as dR_12; dand5 dR_12 as _ _ _ R _ | pose proof (sb_facts A W) as (_ & _ & _ & R & _) ]). unfold kSpaceReserve, kSpaceSize in *. lia. Qed.

(* [comment removed for export] *)
Lemma live_user_where : forall A u li a, WF A -> a_livemap A !! u = Some li -> u <= a < u + li_n li ->
  match li_chunk li with
  | ChP (CP c k) => 1 <= c <= 30 /\ 0 <= k < carved_count A c /\ 1 <= li_n li <= kMaxPrimaryUser /\ c = class_of (li_n li) /\
                   u = user_of (a_sb A) (ChP (CP c k)) (li_n li) /\
                   chunk_addr (a_sb A) c k + 16 <= a < chunk_addr (a_sb A) c k + class_size c /\
                   region_beg (a_sb A) c <= chunk_addr (a_sb A) c k /\
                   chunk_addr (a_sb A) c k + class_size c <= region_beg (a_sb A) c + rg_allocated_user (a_reg A c) /\
                   a_sb A <= a < a_sb A + kSpaceSize
  | ChS s => In s (sr_chunks (a_sec A)) /\ kMaxPrimaryUser < li_n li /\ cs_n s = li_n li /\ u = cs_map s + 6144 /\
             cs_map s + 6144 <= a < cs_map s + map_size (cs_n s)
  end.
Proof.
  intros A u li a W Hl Ha. (first [ pose proof ((wfV A W)) as dR_13; dand3 dR_13 as V1 _ _ | destruct (wfV A W) as (V1 & _ & _) ]). specialize (V1 u li Hl). cbv zeta in V1.
  (first [ dand3 V1 as N U C | destruct V1 as (N & U & C) ]). destruct li as [[[c k]|[mb n0]] n]; cbn [li_chunk li_n] in *.
  - (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range n ltac:(lia)) as CR. rewrite <- Hc in CR.
    (first [ pose proof ((primary_layout (a_sb A) c k n CR ltac:(lia) Hc)) as dR_16; dand5 dR_16 as L1 L2 L3 L5 L4 | pose proof (primary_layout (a_sb A) c k n CR ltac:(lia) Hc) as (L1 & L2 & L3 & L5 & L4) ]).
    unfold carved_count. (first [ pose proof ((carved_chunk_bounds A c k W CR Hk)) as dR_17; dand4 dR_17 as B1 B2 B3 B4 | pose proof (carved_chunk_bounds A c k W CR Hk) as (B1 & B2 & B3 & B4) ]).
    pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in RB.
    rewrite U in Ha. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; try assumption.
    all: unfold kFreeArrayOffset, kRegionSize in *; lia.
  - (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). (first [ pose proof ((secondary_layout mb n N2)) as dR_19; dand7 dR_19 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout mb n N2) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]).
    cbn [user_of] in U. cbn [cs_map cs_n]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; lia.
Qed.

Lemma live_user_zone : forall A a, WF A -> in_live_user A a ->
  (a_b6 A <= a < a_b6 A + kSpaceReserve /\ a_sb A <= a < a_sb A + kSpaceSize) \/
  (exists i s, nth_error (sr_chunks (a_sec A)) i = Some s /\ cs_map s + 6144 <= a < cs_map s + map_size (cs_n s)).
Proof.
  (intros A a W; (first [ intro dR_111; dex2 dR_111 as u li; destruct dR_111 as [Hl Ha] | intro dR_111; dand4 dR_111 as u li Hl Ha | intros (u & li & Hl & Ha) ])). pose proof (live_user_where A u li a W Hl Ha) as LW.
  destruct (li_chunk li) as [[c k]|s].
  - left. (first [ dand9 LW as _ _ _ _ _ _ _ _ SB | destruct LW as (_ & _ & _ & _ & _ & _ & _ & _ & SB) ]). split; [apply primary_in_b6; [exact W| lia]| exact SB].
  - right. (first [ dand5 LW as Hin _ _ _ R | destruct LW as (Hin & _ & _ & _ & R) ]). destruct (In_nth_error' _ _ Hin) as [i Hi]. exists i, s. split; assumption.
Qed.

Lemma live_frame_where : forall A ff f a, WF A -> a_fframes A !! ff = Some f -> ff <= a < ff + fsize (ff_class f) ->
  0 <= ff_class f <= 10 /\ ff = fframe_addr (a_fs A) (ff_class f) (ff_pos (a_fhint A (ff_class f)) (ff_class f) (ff_age f)) /\
  a_fs A + kFakeFramesOffset <= ff /\ ff + fsize (ff_class f) <= a_fs A + kFakeStackBytes.
Proof.
  intros A ff f a W Hf Ha. (first [ pose proof ((wfF A W)) as dR_22; dand3 dR_22 as F1 _ _ | destruct (wfF A W) as (F1 & _ & _) ]). (first [ pose proof ((F1 ff f Hf)) as dR_23; dand3 dR_23 as K E AG | destruct (F1 ff f Hf) as (K & E & AG) ]). cbv zeta in *.
  unfold ff_addr_of_ in E. pose proof (ff_pos_range (a_fhint A (ff_class f)) (ff_class f) (ff_age f) K) as PR.
  (first [ pose proof ((fframe_addr_range (a_fs A) (ff_class f) _ K PR)) as dR_24; dand3 dR_24 as R1 R2 R3 | pose proof (fframe_addr_range (a_fs A) (ff_class f) _ K PR) as (R1 & R2 & R3) ]). unfold a_fs in *. rewrite <- E in *.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
Qed.
Lemma live_frame_zone : forall A a, WF A -> in_live_frame A a -> a_fs A + kFakeFramesOffset <= a < a_fs A + kFakeStackBytes.
Proof.
  (intros A a W; (first [ intro dR_112; dex2 dR_112 as ff f; destruct dR_112 as [Hf Ha] | intro dR_112; dand4 dR_112 as ff f Hf Ha | intros (ff & f & Hf & Ha) ])). pose proof (fsize_pos (ff_class f)).
  (first [ pose proof ((live_frame_where A ff f a W Hf ltac:(lia))) as dR_25; dand4 dR_25 as K _ R1 R2 | destruct (live_frame_where A ff f a W Hf ltac:(lia)) as (K & _ & R1 & R2) ]). lia.
Qed.

(* [comment removed for export] *)
Lemma fixed_bm_no_live_user : forall A i b s a, WF A -> (1 <= i <= 14)%nat ->
  nth_error (big_maps A) i = Some (b, s) -> b <= a < b + s -> ~ in_live_user A a.
Proof.
  intros A i b s a W Hi Hn Ha LU. pose proof (bm_nth_fixed A) as (E0 & _).
  destruct (live_user_zone A a W LU) as [[B6 _]|(j & sc & Hj & R)].
  - destruct (bm_sep A i 0 b s _ _ W Hn E0 ltac:(lia)); lia.
  - pose proof (bm_nth_sec A j sc Hj) as Ej. destruct (bm_sep A i (15 + j) b s _ _ W Hn Ej ltac:(lia)); lia.
Qed.
Lemma fixed_bm_no_live_frame : forall A i b s a, WF A -> (i <= 14)%nat -> i <> 6%nat ->
  nth_error (big_maps A) i = Some (b, s) -> b <= a < b + s -> ~ in_live_frame A a.
Proof.
  intros A i b s a W Hi N6 Hn Ha LF. (first [ pose proof ((bm_nth_fixed A)) as dR_26; dand8 dR_26 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]).
  pose proof (live_frame_zone A a W LF). destruct (bm_sep A i 6 b s _ _ W Hn E6 ltac:(lia)); unfold kFakeFramesOffset in *; lia.
Qed.
(* [comment removed for export] *)
Lemma b6_no_live_frame : forall A a, WF A -> a_b6 A <= a < a_b6 A + kSpaceReserve -> ~ in_live_frame A a.
Proof.
  intros A a W Ha LF. (first [ pose proof ((bm_nth_fixed A)) as dR_27; dand8 dR_27 as E0 _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & _ & _ & E6 & _) ]).
  pose proof (live_frame_zone A a W LF). destruct (bm_sep A 0 6 _ _ _ _ W E0 E6 ltac:(lia)); unfold kFakeFramesOffset in *; lia.
Qed.
Lemma sec_no_live_frame : forall A i sc a, WF A -> nth_error (sr_chunks (a_sec A)) i = Some sc ->
  cs_map sc <= a < cs_map sc + map_size (cs_n sc) -> ~ in_live_frame A a.
Proof.
  intros A i sc a W Hi Ha LF. (first [ pose proof ((bm_nth_fixed A)) as dR_28; dand8 dR_28 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]). pose proof (bm_nth_sec A i sc Hi) as Ei.
  pose proof (live_frame_zone A a W LF). destruct (bm_sep A (15 + i) 6 _ _ _ _ W Ei E6 ltac:(lia)); unfold kFakeFramesOffset in *; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rt_statics_static : forall a, rt_statics AL_pboth a -> pa_static a.
Proof. intros a H. unfold rt_statics, pa_static in *. cbn -[Z.add Z.lt Z.le] in H. lia. Qed.
Lemma pa_static_low : forall a, pa_static a -> a < 0x5e7210. Proof. intros a H. unfold pa_static in H. lia. Qed.
Lemma depot_static : forall a, al_stackStore AL_pboth <= a < al_depot_nodes_map1 AL_pboth + 8 * kDepotNodesL1 -> pa_static a.
Proof. intros a H. unfold pa_static. cbn -[Z.add Z.mul Z.lt Z.le] in H. unfold kDepotNodesL1 in H. lia. Qed.

(* [comment removed for export] *)
Definition pa_shared_ivs : list (Z * Z) := paH_ivs.     (* [comment removed for export] *)
Lemma pa_shared_ivs_sound : forall l h a, In (l, h) pa_shared_ivs -> l <= a < h -> pa_shared a.
Proof.
  intros l h a Hin Ha. apply (paH_ivs_sound l h a); [| exact Ha]. unfold in_ivs. apply existsb_exists. exists (l, h). split; [exact Hin|].
  cbn [fst snd]. rewrite !Z.leb_refl. reflexivity.
Qed.
Definition pa_static_ivs : list (Z * Z) := paS_ivs.     (* [comment removed for export] *)
Lemma pa_static_ivs_sound : forall l h a, In (l, h) pa_static_ivs -> l <= a < h -> pa_static a.
Proof.
  intros l h a Hin Ha. apply (paS_ivs_sound l h a); [| exact Ha]. unfold in_ivs. apply existsb_exists. exists (l, h). split; [exact Hin|].
  cbn [fst snd]. rewrite !Z.leb_refl. reflexivity.
Qed.
Definition range_in_ivs (ivs : list (Z * Z)) (lo hi : Z) : bool := existsb (fun lh => (fst lh <=? lo) && (hi <=? snd lh)) ivs.
Definition const_ok (c : Z * list byte) : bool :=
  let lo := fst c in let hi := lo + Z.of_nat (length (snd c)) in
  range_in_ivs pa_shared_ivs lo hi || ((sh 0x10000 <=? lo) && (hi <=? sh 0x60a000)) || range_in_ivs pa_static_ivs lo hi.
Lemma pa_consts_ok : forallb const_ok pa_consts = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Lemma pa_consts_where : forall c a, In c pa_consts -> fst c <= a < fst c + Z.of_nat (length (snd c)) ->
  pa_shared a \/ pa_image_shadow a \/ pa_static a.
Proof.
  intros c a Hin Ha. pose proof pa_consts_ok as OK. rewrite forallb_forall in OK. specialize (OK c Hin).
  unfold const_ok in OK. cbv zeta in OK. apply orb_true_iff in OK as [OK|OK]; [apply orb_true_iff in OK as [OK|OK]|].
  - left. unfold range_in_ivs in OK. apply existsb_exists in OK as ([l h] & Hlh & B). cbn [fst snd] in B.
    apply andb_true_iff in B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
    eapply pa_shared_ivs_sound; [exact Hlh| lia].
  - right; left. apply andb_true_iff in OK as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2. unfold pa_image_shadow. lia.
  - right; right. unfold range_in_ivs in OK. apply existsb_exists in OK as ([l h] & Hlh & B). cbn [fst snd] in B.
    apply andb_true_iff in B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
    eapply pa_static_ivs_sound; [exact Hlh| lia].
Qed.

(* [comment removed for export] *)
Lemma owned_rt : forall A a b s, In (b, s) (runtime_maps A) -> b <= a < b + s ->
  ~ in_live_user A a -> ~ in_live_frame A a -> pa_owned A a.
Proof. intros A a b s Hin Ha NU NF. left. right. left. left. split; [exists b, s; split; assumption| split; assumption]. Qed.
Lemma rt_fixed_in : forall A r, In r [ (a_thr A, 4096); (a_ctx A, 0x10000); (a_ri A, 4096); (a_fs A, kFakeStackBytes);
      (a_nodes0 A, kDepotNodesBlock); (a_frames0 A, kStackStoreBlockBytes); (a_pa A, 8 * kChunksBlockCount);
      (a_itab A, 0x38e000); (a_m64k A, 0x10000); (p_dtls (a_pl A), 4096);
      (p_gvec (a_pl A), 4096); (p_dvec (a_pl A), 4096); (p_m11 (a_pl A), 4096) ] -> In r (runtime_maps A).
Proof. intros A r H. unfold runtime_maps, runtime_maps_. apply in_or_app. left. exact H. Qed.
Lemma rt_class_in : forall A c, 1 <= c <= 30 ->
  In (region_beg (a_sb A) c, rg_mapped_user (a_reg A c)) (runtime_maps A) /\
  In (region_beg (a_sb A) c + kFreeArrayOffset, rg_mapped_fa (a_reg A c)) (runtime_maps A).
Proof.
  intros A c Hc. unfold runtime_maps, runtime_maps_.
  assert (IN : In c (map Z.of_nat (seq 1 30))). { apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia. }
  split; apply in_or_app; right; apply in_or_app; left; apply in_flat_map; exists c; split; [exact IN| cbn; tauto| exact IN| cbn; tauto].
Qed.
Lemma rt_sec_in : forall A sc, In sc (sr_chunks (a_sec A)) -> In (cs_map sc, map_size (cs_n sc)) (runtime_maps A).
Proof. intros A sc H. unfold runtime_maps, runtime_maps_. apply in_or_app; right; apply in_or_app; right. apply in_map_iff. exists sc; auto. Qed.

(* [comment removed for export] *)
Lemma primary_chunk_no_other_user : forall A c k a, WF A -> 1 <= c <= 30 -> 0 <= k < carved_count A c ->
  chunk_addr (a_sb A) c k <= a < chunk_addr (a_sb A) c k + class_size c ->
  forall u li, a_livemap A !! u = Some li -> u <= a < u + li_n li -> li_chunk li = ChP (CP c k).
Proof.
  intros A c k a W Hc Hk Ha u li Hl Hu. pose proof (live_user_where A u li a W Hl Hu) as LW.
  destruct (li_chunk li) as [[c2 k2]|sc] eqn:E.
  - (first [ dand9 LW as C2 K2 _ _ _ R2 RB2 RE2 _ | destruct LW as (C2 & K2 & _ & _ & _ & R2 & RB2 & RE2 & _) ]).
    destruct (Z.eq_dec c2 c) as [->|NC].
    + destruct (Z.eq_dec k2 k) as [->|NK]; [reflexivity|]. exfalso.
      destruct (carved_chunks_disjoint (a_sb A) c k k2 Hc ltac:(lia) ltac:(lia) ltac:(congruence)); lia.
    + exfalso. (first [ pose proof ((carved_chunk_bounds A c k W Hc Hk)) as dR_30; dand3 dR_30 as B1 B2 _ | pose proof (carved_chunk_bounds A c k W Hc Hk) as (B1 & B2 & _) ]). cbv zeta in *.
      pose proof (region_piece_bounds A c W Hc) as P1. pose proof (region_piece_bounds A c2 W C2) as P2. cbv zeta in *.
      destruct (regions_disjoint (a_sb A) c c2 ltac:(congruence) ltac:(lia) ltac:(lia)); unfold kRegionSize, kFreeArrayOffset in *; lia.
  - exfalso. (first [ dand5 LW as Hin _ _ _ R | destruct LW as (Hin & _ & _ & _ & R) ]). destruct (In_nth_error' _ _ Hin) as [j Hj].
    (first [ pose proof ((carved_chunk_bounds A c k W Hc Hk)) as dR_32; dand3 dR_32 as B1 B2 _ | pose proof (carved_chunk_bounds A c k W Hc Hk) as (B1 & B2 & _) ]). pose proof (region_piece_bounds A c W Hc) as P1. cbv zeta in *.
    pose proof (bm_nth_fixed A) as (E0 & _). pose proof (bm_nth_sec A j sc Hj) as Ej.
    assert (a_b6 A <= a < a_b6 A + kSpaceReserve) by (apply primary_in_b6; [exact W| unfold kRegionSize, kFreeArrayOffset in *; lia]).
    destruct (bm_sep A 0 (15 + j) _ _ _ _ W E0 Ej ltac:(lia)); lia.
Qed.
(* [comment removed for export] *)
Lemma sec_map_no_other_user : forall A sc a, WF A -> In sc (sr_chunks (a_sec A)) ->
  cs_map sc <= a < cs_map sc + map_size (cs_n sc) ->
  forall u li, a_livemap A !! u = Some li -> u <= a < u + li_n li -> li_chunk li = ChS sc /\ cs_map sc + 6144 <= a.
Proof.
  intros A sc a W Hin Ha u li Hl Hu. pose proof (live_user_where A u li a W Hl Hu) as LW.
  destruct (In_nth_error' _ _ Hin) as [i Hi]. pose proof (bm_nth_sec A i sc Hi) as Ei.
  destruct (li_chunk li) as [[c2 k2]|sc2] eqn:E.
  - exfalso. (first [ dand9 LW as _ _ _ _ _ _ _ _ SB | destruct LW as (_ & _ & _ & _ & _ & _ & _ & _ & SB) ]). pose proof (bm_nth_fixed A) as (E0 & _).
    pose proof (primary_in_b6 A a W ltac:(lia)). destruct (bm_sep A 0 (15 + i) _ _ _ _ W E0 Ei ltac:(lia)); lia.
  - (first [ dand5 LW as Hin2 _ _ _ R | destruct LW as (Hin2 & _ & _ & _ & R) ]). destruct (In_nth_error' _ _ Hin2) as [j Hj]. pose proof (bm_nth_sec A j sc2 Hj) as Ej.
    destruct (Nat.eq_dec i j) as [<-|NE].
    + rewrite Hi in Hj. injection Hj as <-. split; [reflexivity| lia].
    + exfalso. destruct (bm_sep A (15 + i) (15 + j) _ _ _ _ W Ei Ej ltac:(lia)); lia.
Qed.

(* [comment removed for export] *)
Lemma live_frames_disjoint : forall A ff f ff' f', WF A ->
  a_fframes A !! ff = Some f -> a_fframes A !! ff' = Some f' -> ff <> ff' ->
  ff + fsize (ff_class f) <= ff' \/ ff' + fsize (ff_class f') <= ff.
Proof.
  intros A ff f ff' f' W H1 H2 NE. (first [ pose proof ((wfF A W)) as dR_35; dand3 dR_35 as F1 _ F3 | destruct (wfF A W) as (F1 & _ & F3) ]).
  (first [ pose proof ((F1 ff f H1)) as dR_36; dand3 dR_36 as K1 E1 A1 | destruct (F1 ff f H1) as (K1 & E1 & A1) ]). (first [ pose proof ((F1 ff' f' H2)) as dR_37; dand3 dR_37 as K2 E2 A2 | destruct (F1 ff' f' H2) as (K2 & E2 & A2) ]). cbv zeta in *. unfold ff_addr_of_ in *.
  pose proof (ff_pos_range (a_fhint A (ff_class f)) (ff_class f) (ff_age f) K1) as P1.
  pose proof (ff_pos_range (a_fhint A (ff_class f')) (ff_class f') (ff_age f') K2) as P2.
  rewrite E1, E2. rewrite E1 in NE; rewrite E2 in NE.
  apply fframe_addr_disjoint; try assumption.
  intros EQ. injection EQ as EK EP. apply NE. rewrite <- EK in *. rewrite EP. reflexivity.
Qed.

(* [comment removed for export] *)
Theorem afoot_owned_shared : forall A m md a, pa_ainv A m md -> afoot LPA AL_pboth A a -> pa_owned A a \/ pa_shared a.
Proof.
  intros A m md a AI FT. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W. pose proof alloc_ceiling_val as CE.
  (first [ pose proof ((bm_nth_fixed A)) as dR_38; dand12 dR_38 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11) ]).
  unfold afoot, afoot_ in FT. cbv zeta in FT. cbn [cl_tp cl_shared cl_consts LPA] in FT. rewrite unsigned_lit in FT by lia.
  change (p_sb (a_pl A)) with (a_sb A) in FT. change (p_thr (a_pl A)) with (a_thr A) in FT. change (p_ctx (a_pl A)) with (a_ctx A) in FT.
  change (p_ri (a_pl A)) with (a_ri A) in FT. change (p_pa (a_pl A)) with (a_pa A) in FT. change (p_fs (a_pl A)) with (a_fs A) in FT.
  change (p_nodes0 (a_pl A)) with (a_nodes0 A) in FT. change (p_frames0 (a_pl A)) with (a_frames0 A) in FT.
  destruct FT as [F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|[F|F]]]]]]]]]]]]]]]]]]].
  - (* [comment removed for export] *) left. left. left. apply rt_statics_static. exact F.
  - right. exact F.
  - (first [ dex1 F as c; destruct F as [Hc Ha] | dand3 F as c Hc Ha | destruct F as (c & Hc & Ha) ]). destruct (pa_consts_where c a Hc Ha) as [S|[S|S]]; [right; exact S| left; right; exact S| left; left; left; exact S].
  - right. unfold pa_shared. lia.
  - right. unfold pa_shared. lia.
  - (* [comment removed for export] *) left. eapply (owned_rt A a (a_thr A) 4096); [apply rt_fixed_in; cbn; tauto| exact F| |].
    + eapply (fixed_bm_no_live_user A 4); [exact W| lia| exact E4| exact F].
    + eapply (fixed_bm_no_live_frame A 4); [exact W| lia| lia| exact E4| exact F].
  - (* [comment removed for export] *) left. eapply (owned_rt A a (a_ctx A) 0x10000); [apply rt_fixed_in; cbn; tauto| exact F| |].
    + eapply (fixed_bm_no_live_user A 5); [exact W| lia| exact E5| exact F].
    + eapply (fixed_bm_no_live_frame A 5); [exact W| lia| lia| exact E5| exact F].
  - (* [comment removed for export] *) left. (first [ pose proof ((sb_facts A W)) as dR_40; dand5 dR_40 as _ _ _ R CE2 | pose proof (sb_facts A W) as (_ & _ & _ & R & CE2) ]).
    unfold a_ri, p_ri in F. change (p_sb (a_pl A)) with (a_sb A) in F.
    assert (B6 : a_b6 A <= a < a_b6 A + kSpaceReserve) by (apply primary_in_b6; [exact W| unfold kSpaceSize in *; lia]).
    eapply (owned_rt A a (a_ri A) 4096); [apply rt_fixed_in; cbn; tauto| exact F| |].
    + intros LU. destruct (live_user_zone A a W LU) as [[_ SB]|(j & sc & Hj & Rj)]; [unfold kSpaceSize in *; lia|].
      pose proof (bm_nth_sec A j sc Hj) as Ej. destruct (bm_sep A 0 (15 + j) _ _ _ _ W E0 Ej ltac:(lia)); lia.
    + apply b6_no_live_frame; assumption.
  - (* [comment removed for export] *) left. (first [ dex1 F as c; destruct F as [Hc Ha] | dand3 F as c Hc Ha | destruct F as (c & Hc & Ha) ]). unfold free_array_beg in Ha.
    pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in RB.
    assert (B6 : a_b6 A <= a < a_b6 A + kSpaceReserve) by (apply primary_in_b6; [exact W| unfold kRegionSize, kFreeArrayOffset in *; lia]).
    eapply owned_rt; [apply (proj2 (rt_class_in A c Hc))| exact Ha| |].
    + ((first [ intro dR_113; dex2 dR_113 as u li; destruct dR_113 as [Hl Hu] | intro dR_113; dand4 dR_113 as u li Hl Hu | intros (u & li & Hl & Hu) ])). pose proof (live_user_where A u li a W Hl Hu) as LW. destruct (li_chunk li) as [[c2 k2]|sc].
      * (first [ dand9 LW as C2 K2 _ _ _ R2 RB2 RE2 _ | destruct LW as (C2 & K2 & _ & _ & _ & R2 & RB2 & RE2 & _) ]). pose proof (region_piece_bounds A c2 W C2) as P2. cbv zeta in P2.
        destruct (Z.eq_dec c2 c) as [->|NC]; [unfold kFreeArrayOffset in *; lia|].
        destruct (regions_disjoint (a_sb A) c c2 ltac:(congruence) ltac:(lia) ltac:(lia)); unfold kRegionSize, kFreeArrayOffset in *; lia.
      * (first [ dand5 LW as Hin _ _ _ R | destruct LW as (Hin & _ & _ & _ & R) ]). destruct (In_nth_error' _ _ Hin) as [j Hj]. pose proof (bm_nth_sec A j sc Hj) as Ej.
        destruct (bm_sep A 0 (15 + j) _ _ _ _ W E0 Ej ltac:(lia)); lia.
    + apply b6_no_live_frame; assumption.
  - (* [comment removed for export] *) left. (first [ dex2 F as u li; destruct F as [Hl HF] | dand4 F as u li Hl HF | destruct F as (u & li & Hl & HF) ]). (first [ pose proof ((wfV A W)) as dR_45; dand3 dR_45 as V1 V2 _ | destruct (wfV A W) as (V1 & V2 & _) ]).
    (first [ pose proof ((V1 u li Hl)) as dR_46; dand3 dR_46 as N U C | pose proof (V1 u li Hl) as (N & U & C) ]). cbv zeta in *. unfold hdr_foot in HF.
    destruct li as [[[c k]|[mb n0]] n]; cbn [li_chunk li_n] in *.
    + (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range n ltac:(lia)) as CR. rewrite <- Hc in CR.
      (first [ pose proof ((primary_layout (a_sb A) c k n CR ltac:(lia) Hc)) as dR_48; dand5 dR_48 as L1 L2 L3 L5 L4 | pose proof (primary_layout (a_sb A) c k n CR ltac:(lia) Hc) as (L1 & L2 & L3 & L5 & L4) ]). cbn [user_of alloc_beg] in *.
      (first [ pose proof ((carved_chunk_bounds A c k W CR Hk)) as dR_49; dand4 dR_49 as B1 B2 B3 B4 | pose proof (carved_chunk_bounds A c k W CR Hk) as (B1 & B2 & B3 & B4) ]). pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in *.
      assert (IN : chunk_addr (a_sb A) c k <= a < chunk_addr (a_sb A) c k + class_size c) by (unfold kChunkHeaderSize in *; lia).
      assert (B6 : a_b6 A <= a < a_b6 A + kSpaceReserve) by (apply primary_in_b6; [exact W| unfold kRegionSize, kFreeArrayOffset in *; lia]).
      eapply owned_rt; [apply (proj1 (rt_class_in A c CR))| lia | |].
      * ((first [ intro dR_114; dex2 dR_114 as u2 li2; destruct dR_114 as [Hl2 Hu2] | intro dR_114; dand4 dR_114 as u2 li2 Hl2 Hu2 | intros (u2 & li2 & Hl2 & Hu2) ])). pose proof (primary_chunk_no_other_user A c k a W CR Hk IN u2 li2 Hl2 Hu2) as EQ.
        assert (u2 = u). { destruct (Z.eq_dec u2 u) as [|NE]; [assumption|]. exfalso. exact (V2 u2 u li2 _ Hl2 Hl NE ltac:(rewrite EQ; reflexivity)). }
        subst u2. rewrite Hl in Hl2. injection Hl2 as <-. cbn [li_n] in Hu2. rewrite U in Hu2. lia.
      * apply b6_no_live_frame; assumption.
    + (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). (first [ pose proof ((secondary_layout mb n N2)) as dR_51; dand7 dR_51 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout mb n N2) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]). cbn [user_of alloc_beg] in *.
      (first [ pose proof ((sec_chunk_bounds A _ W Hin)) as dR_52; dand5 dR_52 as _ _ _ _ MR | pose proof (sec_chunk_bounds A _ W Hin) as (_ & _ & _ & _ & MR) ]). cbn [cs_n cs_map] in MR.
      assert (IN : mb <= a < mb + map_size n) by (unfold kChunkHeaderSize, kSecondaryHeaderSize, kPageSize in *; lia).
      destruct (In_nth_error' _ _ Hin) as [i Hi].
      eapply owned_rt; [apply (rt_sec_in A _ Hin)| exact IN| |].
      * ((first [ intro dR_115; dex2 dR_115 as u2 li2; destruct dR_115 as [Hl2 Hu2] | intro dR_115; dand4 dR_115 as u2 li2 Hl2 Hu2 | intros (u2 & li2 & Hl2 & Hu2) ])). destruct (sec_map_no_other_user A _ a W Hin IN u2 li2 Hl2 Hu2) as [EQ GE]. cbn [cs_map] in GE.
        unfold kChunkHeaderSize in *. lia.
      * eapply sec_no_live_frame; [exact W| exact Hi| exact IN].
  - (* [comment removed for export] *) left. (first [ dex1 F as e; destruct F as [He HF] | dand3 F as e He HF | destruct F as (e & He & HF) ]).
    (first [ pose proof ((wfQ A W)) as dR_54; dand8 dR_54 as Q1 Q2 _ _ _ _ _ QL | destruct (wfQ A W) as (Q1 & Q2 & _ & _ & _ & _ & _ & QL) ]).
    assert (WE : wf_qentry_ (a_reg A) (a_sec A) e).
    { unfold q_entries in He. apply in_flat_map in He as (b & Hb & Heb). apply in_app_iff in Hb as [Hb|Hb];
      [pose proof (proj1 (Forall_forall _ _) Q1 b Hb) as WB| pose proof (proj1 (Forall_forall _ _) Q2 b Hb) as WB];
      (first [ dand3 WB as _ _ WB | destruct WB as (_ & _ & WB) ]); exact (proj1 (Forall_forall _ _) WB e Heb). }
    assert (QC : In (qe_chunk e) (quarantined_chunks A)). { unfold quarantined_chunks, quarantined_chunks_. apply in_map_iff. exists e; auto. }
    destruct WE as (N & C). unfold hdr_foot in HF. destruct e as [[[c k]|[mb n0]] n]; cbn [qe_chunk qe_n] in *.
    + (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range n ltac:(lia)) as CR. rewrite <- Hc in CR.
      (first [ pose proof ((primary_layout (a_sb A) c k n CR ltac:(lia) Hc)) as dR_57; dand5 dR_57 as L1 L2 L3 L5 L4 | pose proof (primary_layout (a_sb A) c k n CR ltac:(lia) Hc) as (L1 & L2 & L3 & L5 & L4) ]). cbn [user_of alloc_beg] in *.
      (first [ pose proof ((carved_chunk_bounds A c k W CR Hk)) as dR_58; dand4 dR_58 as B1 B2 B3 B4 | pose proof (carved_chunk_bounds A c k W CR Hk) as (B1 & B2 & B3 & B4) ]). pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in *.
      assert (IN : chunk_addr (a_sb A) c k <= a < chunk_addr (a_sb A) c k + class_size c) by (unfold kChunkHeaderSize in *; lia).
      assert (B6 : a_b6 A <= a < a_b6 A + kSpaceReserve) by (apply primary_in_b6; [exact W| unfold kRegionSize, kFreeArrayOffset in *; lia]).
      eapply owned_rt; [apply (proj1 (rt_class_in A c CR))| lia | |].
      * ((first [ intro dR_116; dex2 dR_116 as u2 li2; destruct dR_116 as [Hl2 Hu2] | intro dR_116; dand4 dR_116 as u2 li2 Hl2 Hu2 | intros (u2 & li2 & Hl2 & Hu2) ])). pose proof (primary_chunk_no_other_user A c k a W CR Hk IN u2 li2 Hl2 Hu2) as EQ.
        apply (QL u2 li2 Hl2). rewrite EQ. exact QC.
      * apply b6_no_live_frame; assumption.
    + (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). (first [ pose proof ((secondary_layout mb n N2)) as dR_60; dand7 dR_60 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout mb n N2) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]). cbn [user_of alloc_beg] in *.
      assert (IN : mb <= a < mb + map_size n) by (unfold kChunkHeaderSize, kSecondaryHeaderSize, kPageSize in *; lia).
      destruct (In_nth_error' _ _ Hin) as [i Hi].
      eapply owned_rt; [apply (rt_sec_in A _ Hin)| exact IN| |].
      * ((first [ intro dR_117; dex2 dR_117 as u2 li2; destruct dR_117 as [Hl2 Hu2] | intro dR_117; dand4 dR_117 as u2 li2 Hl2 Hu2 | intros (u2 & li2 & Hl2 & Hu2) ])). destruct (sec_map_no_other_user A _ a W Hin IN u2 li2 Hl2 Hu2) as [EQ GE].
        apply (QL u2 li2 Hl2). rewrite EQ. exact QC.
      * eapply sec_no_live_frame; [exact W| exact Hi| exact IN].
  - (* [comment removed for export] *) left. (first [ dex1 F as b; destruct F as [Hb Ha] | dand3 F as b Hb Ha | destruct F as (b & Hb & Ha) ]).
    (first [ pose proof ((wfQ A W)) as dR_62; dand3 dR_62 as Q1 Q2 _ | destruct (wfQ A W) as (Q1 & Q2 & _) ]). 
    assert (WB : wf_batch_ (a_reg A) (a_sec A) b).
    { apply in_app_iff in Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) Q1 b Hb)| exact (proj1 (Forall_forall _ _) Q2 b Hb)]. }
    (first [ dand3 WB as _ Hk _ | destruct WB as (_ & Hk & _) ]). assert (C24 : 1 <= kQuarantineBatchClass <= 30) by (unfold kQuarantineBatchClass; lia).
    unfold batch_addr in Ha. rewrite <- class_size_24 in Ha.
    (first [ pose proof ((carved_chunk_bounds A _ _ W C24 Hk)) as dR_64; dand4 dR_64 as B1 B2 B3 B4 | pose proof (carved_chunk_bounds A _ _ W C24 Hk) as (B1 & B2 & B3 & B4) ]). pose proof (region_piece_bounds A _ W C24) as RB. cbv zeta in *.
    assert (B6 : a_b6 A <= a < a_b6 A + kSpaceReserve) by (apply primary_in_b6; [exact W| unfold kRegionSize, kFreeArrayOffset in *; lia]).
    eapply owned_rt; [apply (proj1 (rt_class_in A _ C24))| lia| |].
    + ((first [ intro dR_118; dex2 dR_118 as u2 li2; destruct dR_118 as [Hl2 Hu2] | intro dR_118; dand4 dR_118 as u2 li2 Hl2 Hu2 | intros (u2 & li2 & Hl2 & Hu2) ])). pose proof (primary_chunk_no_other_user A _ _ a W C24 Hk Ha u2 li2 Hl2 Hu2) as EQ.
      (first [ pose proof ((wfX A W kQuarantineBatchClass (ba_idx b) C24 Hk)) as dR_65; dand11 dR_65 as _ _ _ _ _ _ _ _ _ NVB _ | destruct (wfX A W kQuarantineBatchClass (ba_idx b) C24 Hk) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & NVB & _) ]).
      apply NVB. split; [exists u2, (li_n li2); rewrite <- EQ; destruct li2; exact Hl2|].
      split; [reflexivity|]. unfold batch_indices_. apply in_map_iff. exists b; auto.
    + apply b6_no_live_frame; assumption.
  - (* [comment removed for export] *) left. eapply (owned_rt A a (a_pa A) (8 * kChunksBlockCount)); [apply rt_fixed_in; cbn; tauto| exact F| |].
    + eapply (fixed_bm_no_live_user A 1); [exact W| lia| exact E1| unfold kChunksBlockCount, kPtrArrayReserve in *; lia].
    + eapply (fixed_bm_no_live_frame A 1); [exact W| lia| lia| exact E1| unfold kChunksBlockCount, kPtrArrayReserve in *; lia].
  - (* [comment removed for export] *) left. (first [ dex1 F as sc; destruct F as [Hin Ha] | dand3 F as sc Hin Ha | destruct F as (sc & Hin & Ha) ]). destruct (In_nth_error' _ _ Hin) as [i Hi].
    (first [ pose proof ((sec_chunk_bounds A sc W Hin)) as dR_67; dand5 dR_67 as N _ _ _ MR | pose proof (sec_chunk_bounds A sc W Hin) as (N & _ & _ & _ & MR) ]). pose proof (needed_size_ge (cs_n sc)).
    assert (IN : cs_map sc <= a < cs_map sc + map_size (cs_n sc)).
    { rewrite needed_size2_secondary in MR by lia. pose proof (rounded_size_ge (cs_n sc)). unfold kSecondaryHeaderSize, kPageSize in *. lia. }
    eapply owned_rt; [apply (rt_sec_in A _ Hin)| exact IN| |].
    + ((first [ intro dR_119; dex2 dR_119 as u2 li2; destruct dR_119 as [Hl2 Hu2] | intro dR_119; dand4 dR_119 as u2 li2 Hl2 Hu2 | intros (u2 & li2 & Hl2 & Hu2) ])). destruct (sec_map_no_other_user A _ a W Hin IN u2 li2 Hl2 Hu2) as [_ GE]. unfold kSecondaryHeaderSize in *. lia.
    + eapply sec_no_live_frame; [exact W| exact Hi| exact IN].
  - (* [comment removed for export] *) left. eapply (owned_rt A a (a_fs A) kFakeStackBytes); [apply rt_fixed_in; cbn; tauto| unfold kFakeFlagsOffset, kFakeStackBytes in *; lia| |].
    + eapply (fixed_bm_no_live_user A 6); [exact W| lia| exact E6| unfold kFakeFlagsOffset, kFakeStackBytes in *; lia].
    + intros LF. pose proof (live_frame_zone A a W LF). unfold kFakeFlagsOffset, kFakeFramesOffset in *. lia.
  - (* [comment removed for export] *) left. (first [ dex2 F as ff f; destruct F as [Hf Ha] | dand4 F as ff f Hf Ha | destruct F as (ff & f & Hf & Ha) ]). unfold saved_flag_ptr in Ha.
    pose proof (fsize_pos (ff_class f)) as FS.
    (first [ pose proof ((live_frame_where A ff f ff W Hf)) as dR_69; dand4 dR_69 as K E R1 R2 | destruct (live_frame_where A ff f ff W Hf) as (K & E & R1 & R2) ]); [destruct (wfF A W) as (F1 & _); destruct (F1 ff f Hf) as (K & _); pose proof (fsize_pos _ K); lia|].
    specialize (FS K). destruct FS as [FS _].
    eapply (owned_rt A a (a_fs A) kFakeStackBytes); [apply rt_fixed_in; cbn; tauto| unfold kFakeFramesOffset in *; lia| |].
    + eapply (fixed_bm_no_live_user A 6); [exact W| lia| exact E6| unfold kFakeFramesOffset in *; lia].
    + ((first [ intro dR_120; dex2 dR_120 as ff2 f2; destruct dR_120 as [Hf2 Ha2] | intro dR_120; dand4 dR_120 as ff2 f2 Hf2 Ha2 | intros (ff2 & f2 & Hf2 & Ha2) ])). destruct (Z.eq_dec ff ff2) as [<-|NE].
      * rewrite Hf in Hf2. injection Hf2 as <-. lia.
      * pose proof (fsize_pos (ff_class f2)) as FS2.
        destruct (live_frame_where A ff2 f2 ff2 W Hf2) as (K2 & _); [destruct (wfF A W) as (F1 & _); destruct (F1 ff2 f2 Hf2) as (K2 & _); pose proof (fsize_pos _ K2); lia|].
        destruct (live_frames_disjoint A ff f ff2 f2 W Hf Hf2 NE); lia.
  - (* [comment removed for export] *) left. left. right. left. right. left. exact F.
  - (* [comment removed for export] *) left. destruct F as [F|[F|F]].
    + left. left. apply depot_static. exact F.
    + eapply (owned_rt A a (a_nodes0 A) kDepotNodesBlock); [apply rt_fixed_in; cbn; tauto| exact F| |].
      * eapply (fixed_bm_no_live_user A 7); [exact W| lia| exact E7| exact F].
      * eapply (fixed_bm_no_live_frame A 7); [exact W| lia| lia| exact E7| exact F].
    + eapply (owned_rt A a (a_frames0 A) kStackStoreBlockBytes); [apply rt_fixed_in; cbn; tauto| exact F| |].
      * eapply (fixed_bm_no_live_user A 8); [exact W| lia| exact E8| exact F].
      * eapply (fixed_bm_no_live_frame A 8); [exact W| lia| lia| exact E8| exact F].
  - (* [comment removed for export] *) right. unfold pa_shared. lia.
  - (* [comment removed for export] *) left. (first [ dand4 E11 as _ _ _ E14 | destruct E11 as (_ & _ & _ & E14) ]).
    eapply (owned_rt A a (p_dtls (a_pl A)) 4096); [apply rt_fixed_in; cbn; tauto| exact F| |].
    + eapply (fixed_bm_no_live_user A 14); [exact W| lia| exact E14| exact F].
    + eapply (fixed_bm_no_live_frame A 14); [exact W| lia| lia| exact E14| exact F].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma asI_static_owned : forall A a, cl_static LPA a -> pa_owned A a.
Proof. intros A a H. left. left. exact H. Qed.

Lemma asI_minv : forall A m md, pa_ainv A m md -> MInv (pa_hull A) (pa_lhull A) (pa_eager A) md /\ m_halted md = None.   (* [comment removed for export] *)
Proof. intros A m md AI. split; [exact (ai_minv _ _ _ _ _ _ _ AI) | exact (ai_halted _ _ _ _ _ _ _ AI)]. Qed.

Lemma asI_hull_segs : forall A m md, pa_ainv A m md -> H_off_segments (cl_segs LPA) (hidc (pa_hull A)).
Proof. intros A m md _. cbn [cl_segs LPA]. unfold pa_hull, ahull_of, ahull_of_. apply pa_hull_off_segments. Qed.

Lemma asI_image_visible : forall A m md a, pa_ainv A m md -> in_image LPA a -> hidc (pa_hull A) (wz a) = false.
Proof. intros A m md a _ H. unfold pa_hull, ahull_of, ahull_of_. apply pa_image_visible. exact H. Qed.

Lemma asI_md_frame : forall A m md md', pa_ainv A m md ->
  m_vm md' = m_vm md -> m_halted md' = None -> MInv (pa_hull A) (pa_lhull A) (pa_eager A) md' -> pa_ainv A m md'.   (* [comment removed for export] *)
Proof.
  intros A m md md' AI Hvm Hh HM. destruct AI as [W R HR XT LG MI HL CV CE]. split; try assumption.
  - exact (aledger_vm _ _ _ _ md md' Hvm LG).
  - (* [comment removed for export] *) unfold m_vmmaps in *. rewrite Hvm. exact CV.
  - (* [comment removed for export] *) unfold m_vmmaps in *. rewrite Hvm. exact CE.
Qed.

Lemma asI_consts : forall A m md, pa_ainv A m md ->
  Forall (fun c => bytes_at (cl_segs LPA) (aview_of (pa_hull A) m) (fst c) (snd c)) (cl_consts LPA).
Proof. intros A m md AI. destruct (ar_consts _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (C & _). exact C. Qed.

(* [comment removed for export] *)
Lemma heap_shadow_strict : forall A a, WF A -> heap_shadow A a -> in_shadow_strict a.
Proof.
  intros A a W HS. pose proof alloc_ceiling_val as CE. unfold heap_shadow, heap_shadow_ in HS. change (p_sb (a_pl A)) with (a_sb A) in HS.
  destruct HS as [(c & Hc & R)|[(c & Hc & R)|(sc & Hsc & R)]]; cbv zeta in R.
  - pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in RB.
    destruct (Z.eq_dec (rg_mapped_user (a_reg A c)) 0) as [E|NE]; [rewrite E in R; change (0/8) with 0 in R; lia|].
    (first [ dand11 RB as R1 R2 R3 R4 R5 R6 R7 R8 AL MU _ | destruct RB as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & AL & MU & _) ]).
    apply (sh_iv_strict (region_beg (a_sb A) c) (rg_mapped_user (a_reg A c)) a);
      [apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact AL] | exact MU | lia | | exact R].
    right. unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *. lia.
  - pose proof (region_piece_bounds A c W Hc) as RB. cbv zeta in RB.
    destruct (Z.eq_dec (rg_mapped_fa (a_reg A c)) 0) as [E|NE]; [rewrite E in R; change (0/8) with 0 in R; lia|].
    (first [ dand12 RB as R1 R2 R3 R4 R5 R6 R7 R8 AL _ _ MF | destruct RB as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & AL & _ & _ & MF) ]).
    apply (sh_iv_strict (region_beg (a_sb A) c + kFreeArrayOffset) (rg_mapped_fa (a_reg A c)) a);
      [rewrite Z.add_mod by lia; rewrite (mod0_down _ 0x10000 8 ltac:(exists 8192; reflexivity) AL); reflexivity | exact MF | lia | | exact R].
    right. unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *. lia.
  - (first [ pose proof ((sec_chunk_bounds A sc W Hsc)) as dR_73; dand5 dR_73 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_bounds A sc W Hsc) as (B1 & B2 & B3 & B4 & B5) ]). pose proof (map_size_room (cs_n sc)). pose proof (map_size_page (cs_n sc)) as MP.
    apply app_facts in B3.
    apply (sh_iv_strict (cs_map sc) (map_size (cs_n sc)) a);
      [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact B2] | apply (mod0_down _ kPageSize 8); [exists 512; reflexivity| exact MP] | unfold kPageSize in *; lia | | exact R].
    unfold kPageSize in *. lia.
Qed.
Lemma heap_shadow_range : forall A a, WF A -> heap_shadow A a -> in_shadow_maps a.
Proof. intros A a W HS. apply strict_in_maps. exact (heap_shadow_strict A a W HS). Qed.

(* [comment removed for export] *)
Lemma runtime_maps_range : forall A b s a, WF A -> In (b, s) (runtime_maps A) -> b <= a < b + s ->
  (kHighMemBeg <= a < alloc_ceiling) \/ (4096 <= a < kLowShadowMapBeg /\ (a < al_image_lo AL_pboth \/ al_image_hi AL_pboth <= a)).
Proof.
  intros A b s a W Hin Ha. pose proof alloc_ceiling_val as CE. pose proof (wfP A W) as P. apply wf_place_cheap in P.
  (first [ pose proof ((sb_facts A W)) as dR_74; dand5 dR_74 as _ _ HB RG SCE | pose proof (sb_facts A W) as (_ & _ & HB & RG & SCE) ]). cbn [al_image_lo al_image_hi AL_pboth].
  (first [ dand36 P as _ _ _ _ Apa _ _ Athr _ _ Actx _ _ Anod _ _ Afr _ _ Afs _ _ Aitab _ _ Am64 _ _ Agv _ _ Adv _ _ Am11 dR_P_t0; dand4 dR_P_t0 as _ _ Adtls _ | destruct P as (_ & _ & _ & _ & Apa & _ & _ & Athr & _ & _ & Actx & _ & _ & Anod & _ & _ & Afr & _ & _ & Afs & _ & _ &
                 Aitab & _ & _ & Am64 & _ & _ & Agv & _ & _ & Adv & _ & _ & Am11 & _ & _ & Adtls & _) ]).
  apply app_facts in Apa. apply app_facts in Athr. apply app_facts in Actx. apply app_facts in Anod. apply app_facts in Afr.
  apply app_facts in Afs. apply app_facts in Aitab. apply app_facts in Am64. apply app_facts in Agv. apply app_facts in Adv.
  apply app_facts in Am11. apply app_facts in Adtls.
  unfold runtime_maps, runtime_maps_ in Hin. apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
  - unfold a_b6, a_sb, p_ri in *.
    destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; injection E as <- <-.
    + clear - CE Athr Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Actx Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE HB RG SCE Ha. unfold kSpaceSize, kHighMemBeg in *. lia.
    + clear - CE Afs Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Anod Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Afr Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Apa Ha. unfold kChunksBlockCount, kPtrArrayReserve, kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Aitab Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Am64 Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Adtls Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Agv Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Adv Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    + clear - CE Am11 Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
  - left. apply in_flat_map in Hin as (c & Hc & Hin). apply in_map_iff in Hc as (cn & <- & Hcn). apply in_seq in Hcn.
    pose proof (region_piece_bounds A (Z.of_nat cn) W ltac:(lia)) as RB. cbv zeta in RB. change (p_sb (a_pl A)) with (a_sb A) in Hin.
    clear Apa Athr Actx Anod Afr Afs Aitab Am64 Agv Adv Am11 Adtls.
    unfold kHighMemBeg, kFreeArrayOffset, kRegionSize, kSpaceSize in *.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
  - apply in_map_iff in Hin as (sc & E & Hsc). injection E as <- <-.
    (first [ pose proof ((sec_chunk_bounds A sc W Hsc)) as dR_76; dand5 dR_76 as _ _ B3 B4 _ | pose proof (sec_chunk_bounds A sc W Hsc) as (_ & _ & B3 & B4 & _) ]). apply app_facts in B3.
    clear - CE B3 B4 Ha. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
Qed.

(* [comment removed for export] *)
Lemma fs_shadow_not_ghost : forall A a, WF A -> sh (a_fs A) <= a < sh (a_fs A) + kFakeStackBytes / 8 -> ~ ghost_hs_ (a_pl A) a.
Proof.
  intros A a W Ha [_ NV]. apply NV. exists (p_fs (a_pl A)), kFakeStackBytes. split; [cbn; tauto|].
  pose proof (wfP A W) as PL. apply wf_place_cheap in PL.
  assert (F3 : p_fs (a_pl A) mod 4096 = 0) by tauto. assert (F1 : app_rangeA AL_pboth (p_fs (a_pl A)) kFakeStackBytes) by tauto.
  apply app_facts in F1. clear PL. unfold a_fs, sh in *.
  assert (FM : p_fs (a_pl A) mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact F3]).
  pose proof (Z_div_exact_full_2 (p_fs (a_pl A)) 8 ltac:(lia) FM) as E.
  enough (X : (p_fs (a_pl A) + kFakeStackBytes) / 8 = p_fs (a_pl A) / 8 + kFakeStackBytes / 8) by lia.
  rewrite E at 1. rewrite (Z.mul_comm 8), Z.div_add_l by lia. reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma app_not_ghost' : forall P a, (a < kLowShadowMapBeg \/ kHighMemBeg <= a) -> ~ ghost_hs_ P a.
Proof. intros P a Ha [R _]. exact (app_not_in_shadow_maps a Ha R). Qed.

Lemma fs_shadow_strict : forall A a, WF A -> sh (a_fs A) <= a < sh (a_fs A) + kFakeStackBytes / 8 -> in_shadow_strict a.
Proof.
  intros A a W Ha. pose proof alloc_ceiling_val as CE. pose proof (wfP A W) as P. apply wf_place_cheap in P.
  assert (F3 : p_fs (a_pl A) mod 4096 = 0) by tauto. assert (F1 : app_rangeA AL_pboth (p_fs (a_pl A)) kFakeStackBytes) by tauto.
  apply app_facts in F1. clear P. unfold a_fs in *.
  apply (sh_iv_strict (p_fs (a_pl A)) kFakeStackBytes a); [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact F3] | reflexivity | reflexivity | | exact Ha].
  unfold kFakeStackBytes, kLowShadowMapBeg, kHighMemBeg in *. lia.
Qed.
Lemma fs_shadow_in_maps : forall A a, WF A -> sh (a_fs A) <= a < sh (a_fs A) + kFakeStackBytes / 8 -> in_shadow_maps a.
Proof. intros A a W Ha. apply strict_in_maps. exact (fs_shadow_strict A a W Ha). Qed.
(* [comment removed for export] *)
Lemma owned_cases : forall A a, WF A -> pa_owned A a ->
  cl_static LPA a \/ in_regions (runtime_maps A) a \/ in_shadow_maps a.
Proof.
  intros A a W OW. destruct OW as [[S|[[(IR & _ & _)|[HS|[FS _]]]|[GH _]]]|IS].
  - left. exact S.
  - right; left. exact IR.
  - right; right. exact (heap_shadow_range A a W HS).
  - right; right. exact (fs_shadow_in_maps A a W FS).
  - right; right. exact GH.
  - right; right. exact (image_shadow_in_maps a IS).
Qed.

Lemma asI_owned_where : forall A m md a, pa_ainv A m md -> pa_owned A a -> cl_static LPA a \/ heap_zone LPA a.
Proof.
  intros A m md a AI OW. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W. pose proof alloc_ceiling_val as CE.
  unfold heap_zone, in_image. cbn [cl_image_lo cl_image_hi LPA].
  destruct (owned_cases A a W OW) as [S|[IR|SM]]; [left; exact S| |]; right.
  - (first [ dex2 IR as b s; destruct IR as [Hin Hab] | dand4 IR as b s Hin Hab | destruct IR as (b & s & Hin & Hab) ]). pose proof (runtime_maps_range A b s a W Hin Hab). cbn [al_image_lo al_image_hi AL_pboth] in H.
    unfold kHighMemBeg, kLowShadowMapBeg in *. lia.
  - unfold in_shadow_maps, kLowShadowMapBeg, kHighShadowMapBeg, kHighShadowMapSize in *. lia.
Qed.

Lemma owned_lt64 : forall A m md a, pa_ainv A m md -> pa_owned A a -> 0 <= a < 2^64.
Proof.
  intros A m md a AI OW. pose proof alloc_ceiling_val. destruct (asI_owned_where A m md a AI OW) as [S|HZ].
  - cbn [cl_static LPA] in S. unfold pa_static in S. lia.
  - unfold heap_zone in HZ. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_at_func : forall segs (m : mem) a bs bs', bytes_at segs m a bs -> bytes_at segs m a bs' -> length bs = length bs' -> bs = bs'.
Proof.
  (intros segs m a bs bs'; (first [ intro dR_121; dand3 dR_121 as _ _ H1 | intros (_ & _ & H1) ]); (first [ intro dR_122; dand3 dR_122 as _ _ H2 | intros (_ & _ & H2) ]); intros L). apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [LT|GE].
  - rewrite <- (H1 i LT). rewrite <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs i)) by lia. rewrite (proj2 (nth_error_None bs' i)) by lia. reflexivity.
Qed.
Lemma bytes_at_nonnull : forall segs (m : mem) a bs i, bytes_at segs m a bs -> 0 <= i < Z.of_nat (length bs) ->
  (forall x : word, 0x60a000 <= bv_unsigned x -> seg_rom segs x = None) -> 0x60a000 <= a -> m (wz (a + i)) <> None.
Proof.
  (intros segs m a bs i; (first [ intro dR_123; dand3 dR_123 as H0 H1 HB | intros (H0 & H1 & HB) ]); intros Hi ROM Ha). specialize (HB (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in HB by lia.
  unfold mrd, wa in HB. destruct (m (wz (a + i))) eqn:E; [congruence|].
  rewrite ROM in HB. 2:{ rewrite unsigned_lit by lia. lia. } symmetry in HB. apply nth_error_None in HB. lia.
Qed.
Lemma pa_rom_high : forall x : word, 0x60a000 <= bv_unsigned x -> seg_rom (cl_segs LPA) x = None.
Proof. intros x Hx. cbn [cl_segs LPA]. apply pa_seg_rom_none. lia. Qed.

(* [comment removed for export] *)
Lemma sh_ceil_le : forall a n b s, a mod 8 = 0 -> b mod 8 = 0 -> s mod 8 = 0 -> b <= a -> a + n <= b + s ->
  sh b <= sh a /\ sh a + (n + 7) / 8 <= sh b + s / 8.
Proof.
  intros a n b s Ha Hb Hs H1 H2. split; [apply sh_mono; lia|].
  rewrite <- (sh_add b s Hb Hs). unfold sh.
  pose proof (Z_div_exact_full_2 a 8 ltac:(lia) Ha) as Ea. pose proof (Z_div_exact_full_2 (b + s) 8 ltac:(lia) ltac:(rewrite Z.add_mod, Hb, Hs by lia; reflexivity)) as Ebs.
  assert ((n + 7) / 8 < (b + s) / 8 - a / 8 + 1); [|lia].
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma asI_live_ok : forall A m md p n, pa_ainv A m md -> as_live A p = Some n ->
  0 <= n < REQ_MAX /\ p mod 16 = 0 /\ app_range LPA p n /\ p + n <= alloc_ceiling /\
  ~ in_image LPA p /\ mapped (aview_of (pa_hull A) m) p n /\
  (forall i, 0 <= i < n -> ~ pa_owned A (p + i)) /\
  (forall i, 0 <= i < (n + 7) / 8 -> pa_owned A (sh p + i)).   (* [comment removed for export] *)
Proof.
  intros A m md p n AI HL. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W. pose proof alloc_ceiling_val as CE. (first [ pose proof ((sb_facts A W)) as dR_78; dand3 dR_78 as _ SBA _ | pose proof (sb_facts A W) as (_ & SBA & _) ]).
  unfold as_live, as_live_ in HL. destruct (a_livemap A !! p) as [li|] eqn:Hl; [|discriminate]. cbn in HL. injection HL as HL. subst n.
  (first [ pose proof ((wfV A W)) as dR_79; dand3 dR_79 as V1 V2 V3 | destruct (wfV A W) as (V1 & V2 & V3) ]). (first [ pose proof ((V1 p li Hl)) as dR_80; dand3 dR_80 as N U C | pose proof (V1 p li Hl) as (N & U & C) ]). cbv zeta in *.
  (first [ pose proof ((ar_live _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) p li Hl)) as dR_81; dand3 dR_81 as HR MU MC | pose proof (ar_live _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI) p li Hl) as (HR & MU & MC) ]).
  assert (GEO : p mod 16 = 0 /\ app_rangeA AL_pboth p (li_n li) /\ p + li_n li <= alloc_ceiling /\
                (forall i, 0 <= i < (li_n li + 7) / 8 -> heap_shadow A (sh p + i))).
  { destruct li as [[[c k]|[mb n0]] n]; cbn [li_chunk li_n] in *.
    - (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range n ltac:(lia)) as CR. rewrite <- Hc in CR.
      (first [ pose proof ((primary_layout (a_sb A) c k n CR ltac:(lia) Hc)) as dR_83; dand5 dR_83 as L1 L2 L3 L5 L4 | pose proof (primary_layout (a_sb A) c k n CR ltac:(lia) Hc) as (L1 & L2 & L3 & L5 & L4) ]). cbn [user_of alloc_beg] in *.
      (first [ pose proof ((carved_chunk_bounds A c k W CR Hk)) as dR_84; dand4 dR_84 as B1 B2 B3 B4 | pose proof (carved_chunk_bounds A c k W CR Hk) as (B1 & B2 & B3 & B4) ]). pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in *.
      (first [ dand12 RB as R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 | destruct RB as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12) ]).
      assert (PM : p mod 16 = 0) by (rewrite U; apply user_beg_mod16; exact B3).
      split; [exact PM|]. split; [apply app_rangeA_hi; unfold kFreeArrayOffset, kRegionSize, kSpaceSize in *; lia|].
      split; [unfold kFreeArrayOffset, kRegionSize, kSpaceSize in *; lia|].
      intros i Hi. unfold heap_shadow, heap_shadow_. left. exists c. split; [exact CR|]. cbv zeta. change (p_sb (a_pl A)) with (a_sb A).
      pose proof (sh_ceil_le p n (region_beg (a_sb A) c) (rg_mapped_user (a_reg A c))
        ltac:(apply (mod0_down _ 16 8); [exists 2; reflexivity| exact PM]) ltac:(apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact R9]) R10 ltac:(lia) ltac:(lia)). lia.
    - (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). (first [ pose proof ((secondary_layout mb n N2)) as dR_87; dand7 dR_87 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout mb n N2) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]). cbn [user_of alloc_beg] in *.
      (first [ pose proof ((sec_chunk_bounds A _ W Hin)) as dR_88; dand5 dR_88 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_bounds A _ W Hin) as (B1 & B2 & B3 & B4 & B5) ]). cbn [cs_map cs_n] in *.
      pose proof (map_size_page n) as MP.
      assert (PM : p mod 16 = 0). { rewrite U, S6. rewrite Z.add_mod by lia. rewrite (mod0_down mb 4096 16 ltac:(exists 256; reflexivity) B2). reflexivity. }
      split; [exact PM|]. split; [apply (app_rangeA_sub _ _ _ _ _ B3); lia|]. split; [lia|].
      intros i Hi. unfold heap_shadow, heap_shadow_. right. right. exists (CS mb n). split; [exact Hin|]. cbn [cs_map cs_n].
      pose proof (sh_ceil_le p n mb (map_size n) ltac:(apply (mod0_down _ 16 8); [exists 2; reflexivity| exact PM])
        ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact B2]) ltac:(apply (mod0_down _ kPageSize 8); [exists 512; reflexivity| exact MP]) ltac:(lia) ltac:(lia)). lia. }
  (first [ dand4 GEO as PM HB CEIL SHO | destruct GEO as (PM & HB & CEIL & SHO) ]). (first [ pose proof ((app_facts _ _ HB)) as dR_90; dand5 dR_90 as G1 G2 G3 G4 G5 | pose proof (app_facts _ _ HB) as (G1 & G2 & G3 & G4 & G5) ]).
  split; [lia|]. split; [exact PM|].
  split. { unfold app_rangeA in HB. unfold app_range, app_lo, app_hi, kLowAppEnd. cbn [al_image_lo al_image_hi AL_pboth cl_image_lo cl_image_hi LPA] in HB |- *. exact HB. }
  split; [exact CEIL|].
  split. { unfold in_image. cbn [cl_image_lo cl_image_hi LPA]. lia. }
  split; [exact MU|]. split.
  - intros i Hi OW. destruct OW as [[S|[[(IR & NU & _)|OW']|OW']]|OW'].
    + cbn [cl_static LPA] in S. unfold pa_static in S. clear - S G1 G2 G4 Hi. lia.
    + apply NU. exists p, li. split; [exact Hl| lia].
    + assert (SM : in_shadow_maps (p + i)).
      { destruct OW' as [HS|[FS _]]; [exact (heap_shadow_range A _ W HS)| exact (fs_shadow_in_maps A _ W FS)]. }
      exact (app_not_in_shadow_maps (p + i) ltac:(lia) SM).
    + destruct OW' as [GH _]. exact (app_not_in_shadow_maps (p + i) ltac:(lia) GH).
    + apply image_shadow_in_maps in OW'. exact (app_not_in_shadow_maps (p + i) ltac:(lia) OW').
  - intros i Hi. left. right. left. right. left. exact (SHO i Hi).
Qed.

(* [comment removed for export] *)
Lemma asI_live_primary_high : forall A m md p n, pa_ainv A m md -> as_live A p = Some n -> n <= kMaxPrimaryUser -> kHighMemBeg <= p.
Proof.
  intros A m md p n AI HL Hn. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W.
  unfold as_live, as_live_ in HL. destruct (a_livemap A !! p) as [li|] eqn:Hl; [|discriminate]. cbn in HL. injection HL as HL. subst n.
  (first [ pose proof ((wfV A W)) as dR_91; dand3 dR_91 as V1 _ _ | destruct (wfV A W) as (V1 & _ & _) ]). (first [ pose proof ((V1 p li Hl)) as dR_92; dand3 dR_92 as N U C | pose proof (V1 p li Hl) as (N & U & C) ]). cbv zeta in *.
  pose proof (live_user_where A p li p W Hl ltac:(lia)) as LW.
  destruct (li_chunk li) as [[c k]|sc] eqn:E.
  - (first [ dand8 LW as CR Hk _ _ _ IN RB1 _ | destruct LW as (CR & Hk & _ & _ & _ & IN & RB1 & _) ]). pose proof (region_piece_bounds A c W CR) as RB. cbv zeta in RB. lia.
  - (first [ dand3 LW as _ K _ | destruct LW as (_ & K & _) ]). lia.
Qed.

Lemma asI_live_shadow : forall A m md p n, pa_ainv A m md -> as_live A p = Some n ->
  bytes_at (cl_segs LPA) (aview_of (pa_hull A) m) (sh p) (shpat n).
Proof.
  intros A m md p n AI HL. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W. (first [ pose proof ((sb_facts A W)) as dR_95; dand3 dR_95 as _ SBA _ | pose proof (sb_facts A W) as (_ & SBA & _) ]).
  unfold as_live, as_live_ in HL. destruct (a_livemap A !! p) as [li|] eqn:Hl; [|discriminate]. cbn in HL. injection HL as HL. subst n.
  (first [ pose proof ((wfV A W)) as dR_96; dand3 dR_96 as V1 V2 V3 | destruct (wfV A W) as (V1 & V2 & V3) ]). (first [ pose proof ((V1 p li Hl)) as dR_97; dand3 dR_97 as N U C | pose proof (V1 p li Hl) as (N & U & C) ]). cbv zeta in *.
  (first [ pose proof ((ar_shadow _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI))) as dR_98; dand6 dR_98 as _ SL _ _ SS _ | destruct (ar_shadow _ _ _ _ _ (ai_repr _ _ _ _ _ _ _ AI)) as (_ & SL & _ & _ & SS & _) ]).
  destruct li as [[[c k]|[mb n0]] n]; cbn [li_chunk li_n] in *.
  - (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range n ltac:(lia)) as CR. rewrite <- Hc in CR.
    specialize (SL p c k n Hl). unfold pshadow_live in SL. apply bytes_at_app in SL as [_ SL]. apply bytes_at_app in SL as [SL _].
    unfold fa8 in SL. rewrite repeat_length in SL. pose proof (rz_size_range n). rewrite Z2Nat.id in SL by (apply Z.div_pos; lia).
    (first [ pose proof ((carved_chunk_bounds A c k W CR Hk)) as dR_100; dand4 dR_100 as _ _ B3 _ | pose proof (carved_chunk_bounds A c k W CR Hk) as (_ & _ & B3 & _) ]).
    rewrite <- sh_add in SL; [| apply (mod0_down _ 32 8); [exists 4; reflexivity| exact B3] | apply (mod0_down _ 16 8); [exists 2; reflexivity| apply rz_size_mod16]].
    cbn [user_of alloc_beg] in U. unfold user_beg in U. rewrite <- U in SL.
    (first [ pose proof ((user_size_pos n ltac:(lia))) as dR_101; dand3 dR_101 as _ _ E | destruct (user_size_pos n ltac:(lia)) as (_ & _ & E) ]). rewrite E in SL by lia. exact SL.
  - (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). specialize (SS p mb n Hl). unfold sshadow_live in SS.
    apply bytes_at_app in SS as [_ SS]. apply bytes_at_app in SS as [SS _]. unfold fa8 in SS. rewrite repeat_length in SS. change (Z.of_nat (Z.to_nat 768)) with (6144 / 8) in SS.
    (first [ pose proof ((sec_chunk_bounds A _ W Hin)) as dR_103; dand3 dR_103 as _ B2 _ | pose proof (sec_chunk_bounds A _ W Hin) as (_ & B2 & _) ]). cbn [cs_map] in B2.
    rewrite <- sh_add in SS; [| apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact B2] | reflexivity].
    cbn [user_of] in U. unfold sec_user_beg, kPageSize in U. replace (mb + 4096 + 2048) with (mb + 6144) in U by lia. rewrite <- U in SS.
    (first [ pose proof ((user_size_pos n ltac:(lia))) as dR_104; dand3 dR_104 as _ _ E | destruct (user_size_pos n ltac:(lia)) as (_ & _ & E) ]). rewrite E in SS by lia. exact SS.
Qed.

Lemma asI_live_disjoint : forall A m md p n q k, pa_ainv A m md ->
  as_live A p = Some n -> as_live A q = Some k -> p <> q -> p + n <= q \/ q + k <= p.
Proof.
  intros A m md p n q k AI HP HQ NE. pose proof (ai_wf _ _ _ _ _ _ _ AI) as W.
  unfold as_live, as_live_ in HP, HQ.
  destruct (a_livemap A !! p) as [lp|] eqn:Hp; [|discriminate]. destruct (a_livemap A !! q) as [lq|] eqn:Hq; [|discriminate].
  cbn in HP, HQ. injection HP as HP. injection HQ as HQ. subst n k.
  destruct (Z.le_gt_cases (p + li_n lp) q) as [|O1]; [left; assumption|]. destruct (Z.le_gt_cases (q + li_n lq) p) as [|O2]; [right; assumption|]. exfalso.
  set (a := Z.max p q). (first [ pose proof ((wfV A W)) as dR_105; dand3 dR_105 as V1 V2 _ | destruct (wfV A W) as (V1 & V2 & _) ]).
  pose proof (proj1 (V1 p lp Hp)) as Np. pose proof (proj1 (V1 q lq Hq)) as Nq.
  assert (Ap : p <= a < p + li_n lp) by lia. assert (Aq : q <= a < q + li_n lq) by lia.
  apply (V2 p q lp lq Hp Hq NE).
  pose proof (live_user_where A p lp a W Hp Ap) as LW.
  destruct (li_chunk lp) as [[c k]|sc] eqn:E.
  - (first [ dand7 LW as CR Hk _ _ _ IN _ | destruct LW as (CR & Hk & _ & _ & _ & IN & _) ]). symmetry. rewrite <- E. rewrite E.
    apply (primary_chunk_no_other_user A c k a W CR Hk ltac:(lia) q lq Hq Aq).
  - (first [ dand5 LW as Hin _ _ _ IN | destruct LW as (Hin & _ & _ & _ & IN) ]). symmetry.
    exact (proj1 (sec_map_no_other_user A sc a W Hin ltac:(pose proof (secondary_layout (cs_map sc) (cs_n sc)); lia) q lq Hq Aq)).
Qed.

End Pasan.
