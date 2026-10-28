(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode Tac InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AKitQ AModelFacts ARep ALayout AHeapP ARepKit ARepFrame
     ASec ASecFacts APoisonR_iface F_apoison AFrameD ARepFrameD F_asecdealloc F_arecsec ASecRecycle_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import LiaTier0U.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Lemma ablk_int : forall lo hi, ablk lo hi ->      (* [comment removed for export] *)
  exists k, 0 <= k <= 1 /\ 6443008 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6443008 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6443008 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.
Lemma u64arr_app_inv' : forall m A ws1 ws2, u64arr bsegs m A (ws1 ++ ws2) ->
  u64arr bsegs m A ws1 /\ u64arr bsegs m (A + 8 * Z.of_nat (length ws1)) ws2.
Proof.
  intros m A ws1 ws2 [HB HW]. rewrite u64s_app in HB. apply bytes_at_app in HB. destruct HB as [HB1 HB2].
  rewrite u64s_length in HB2. replace (A + Z.of_nat (8 * length ws1)) with (A + 8 * Z.of_nat (length ws1)) in HB2 by lia.
  rewrite length_app in HW. destruct HW as (H0 & H1 & HW).
  split; split; try assumption.
  - split; [lia|]. split; [lia|]. intros i Hi. apply HW. lia.
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + 8 * Z.of_nat (length ws1) + i) with (A + (8 * Z.of_nat (length ws1) + i)) by lia. apply HW. lia.
Qed.

Lemma junk_of_u64arr' : forall m A ws, u64arr bsegs m A ws -> junk_at m A (8 * Z.of_nat (length ws)).
Proof.
  intros m A ws [B W]. exists (u64s ws). split; [split|].
  - cbn. split; [| exact I]. rewrite u64s_length. lia.
  - cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. replace (Z.of_nat (Z.to_nat (8 * Z.of_nat (length ws)))) with (8 * Z.of_nat (length ws)) by lia. exact W.
Qed.

Lemma map_upd : forall {A B} (f : A -> B) (l : list A) i x, map f (upd l i x) = upd (map f l) i (f x).
Proof. intros A B f l. induction l as [|y l IH]; intros [|i] x; cbn; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma upd_app_mid : forall {A} (l1 l2 : list A) (a x : A), upd (l1 ++ a :: l2) (length l1) x = l1 ++ x :: l2.
Proof. intros A l1. induction l1 as [|y l1 IH]; intros l2 a x; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma firstn_snoc : forall {A} (l : list A) (a : A), firstn (length l) (l ++ [a]) = l.
Proof. intros A l a. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Lemma nth_error_last_split : forall {A} (l : list A) n x,
  length l = S n -> nth_error l n = Some x -> l = removelast l ++ [x] /\ length (removelast l) = n.
Proof.
  intros A l n x HL HN.
  assert (NE : l <> []) by (intros ->; discriminate).
  pose proof (app_removelast_last x NE) as E.
  assert (LR : length (removelast l) = n) by (rewrite E, length_app in HL; cbn in HL; lia).
  split; [| exact LR].
  assert (HN' : nth_error (removelast l ++ [last l x]) n = Some x) by (rewrite <- E; exact HN).
  rewrite nth_error_app2 in HN' by lia. rewrite LR, Nat.sub_diag in HN'. cbn in HN'. injection HN' as HN'.
  transitivity (removelast l ++ [last l x]); [exact E| rewrite HN'; reflexivity].
Qed.

Lemma disjoint_from_Forall : forall W A k, disjoint_from W A k <-> Forall (fun iv => A + k <= fst iv \/ snd iv <= A) W.
Proof.
  intros W A k. induction W as [|[lo hi] W IH]; cbn.
  - split; [intros _; constructor| intros _; exact I].
  - split.
    + intros [H1 H2]. constructor; [cbn; exact H1| apply IH; exact H2].
    + intros HF. inversion HF; subst. split; [assumption| apply IH; assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sec_wf1_facts : forall L mb ms n, sec_wf1 L (CSec mb ms n) ->
     mb mod 4096 = 0 /\ ablk mb (mb + ms) /\ mb + ms <= ATOP /\ ms = sec_map_size n
  /\ 64512 < n <= AREQMAX /\ rz_size n = 2048 /\ 73728 <= ms <= 671109120 /\ ms mod 4096 = 0
  /\ needed_size n + 4096 <= ms /\ 0 <= needed_size n /\ sec_clear L mb ms.
Proof.
  intros L mb ms n W. cbn [sec_wf1] in W. destruct W as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & RZ & _ & RSR & _ & NSE & _ & MSR & MSM & MSB). rewrite <- G4 in MSR, MSM, MSB.
  repeat (split; [first [assumption | lia]|]). exact G7.
Qed.

(* [comment removed for export] *)
Lemma bases_dominated : forall L cs mb ms n,
  Forall (sec_wf1 L) cs -> sec_disjoint cs -> In (CSec mb ms n) cs ->
  Forall (fun b => 0 <= b < 2^64 /\ (b <= mb + 6128 -> b <= mb)) (map sec_mb cs).
Proof.
  intros L cs mb ms n WF [ND D] IN. rewrite Forall_map. rewrite Forall_forall in WF |- *. intros ch Hch.
  pose proof (WF ch Hch) as W1. pose proof (WF _ IN) as W0.
  destruct ch as [c k|mb' ms' n']; [destruct W1|]. cbn [sec_mb].
  destruct (sec_wf1_facts _ _ _ _ W1) as (_ & A2 & A3 & _ & _ & _ & A7 & _).
  destruct (sec_wf1_facts _ _ _ _ W0) as (_ & B2 & B3 & _ & _ & _ & B7 & _).
  pose proof (ablk_lin _ _ A2) as (A2a & A2b & A2c & A2d). pose proof (ablk_lin _ _ B2) as (B2a & B2b & B2c & B2d).   (* [comment removed for export] *)
  unfold K_HIGH_MEM in *. split; [lia|]. intros LE.
  assert (DEC : {CSec mb' ms' n' = CSec mb ms n} + {CSec mb' ms' n' <> CSec mb ms n}) by (repeat (decide equality)).
  destruct DEC as [E|NE]; [injection E as -> -> ->; lia|].
  destruct (D _ _ Hch IN NE) as [X|X]; cbn [sec_mb sec_ms] in X; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_cells_hd' : forall m A c cs, rw_cells bsegs m A (c :: cs) -> rw_cells bsegs m A [c].
Proof. intros m A c cs H. apply (proj1 (rw_cells_app bsegs m A [c] cs)) in H as [H _]. exact H. Qed.
Lemma rw_cells_tl' : forall m A c cs, rw_cells bsegs m A (c :: cs) -> rw_cells bsegs m (A + Z.of_nat (csize c)) cs.
Proof. intros m A c cs H. apply (proj1 (rw_cells_app bsegs m A [c] cs)) in H as [_ H]. cbn [cells_size] in H. rewrite Nat.add_0_r in H. exact H. Qed.
Lemma rw_cells_cons' : forall m A c cs,
  rw_cells bsegs m A [c] -> rw_cells bsegs m (A + Z.of_nat (csize c)) cs -> rw_cells bsegs m A (c :: cs).
Proof.
  intros m A c cs H1 H2. apply (proj2 (rw_cells_app bsegs m A [c] cs)). split; [exact H1|].
  cbn [cells_size]. rewrite Nat.add_0_r. exact H2.
Qed.

(* [comment removed for export] *)
Lemma mtx4_join : forall m, rw_cells bsegs m (AINSTANCE + 680) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0xcc941 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0xcc940 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m H1 H2. apply rw_cells_cons'; [exact H1| exact H2]. Qed.
Lemma mtx4_split : forall m, rw_cells bsegs m 0xcc940 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (AINSTANCE + 680) [C1 (Z_to_bv 8 0)] /\ rw_cells bsegs m 0xcc941 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Proof. intros m H. split; [eapply rw_cells_hd'; exact H| apply rw_cells_tl' in H; exact H]. Qed.

(* [comment removed for export] *)
Lemma sec_shadow_cb : forall m mb ms n lv, asec_chunk m (CSec mb ms n) 0 lv \/ (exists idx, asec_chunk m (CSec mb ms n) idx lv) ->
  mb mod 4096 = 0 -> 64512 < n <= AREQMAX -> ms = sec_map_size n -> is_primary n = false ->
  exists shj, rw_cells bsegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj].
Proof.
  intros m mb ms n lv CH MAL NB MSE NPR.
  assert (CH' : exists idx, asec_chunk m (CSec mb ms n) idx lv) by (destruct CH as [CH|CH]; [exists 0; exact CH| exact CH]).
  clear CH. destruct CH' as [idx CH].
  pose proof (sec_facts n ltac:(lia) NPR) as (_ & RZ & _ & RSR & _ & NSE & _ & MSR & MSM & MSB). rewrite <- MSE in MSR, MSM, MSB.
  cbn [asec_chunk] in CH. destruct CH as (_ & _ & _ & _ & _ & _ & S1 & S2 & S3). unfold SEC_UOFF in *.
  assert (GR : 0 <= granules n /\ shad (mb + 6144) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules. rewrite !shad_div, shlen_div. clear -MAL NB RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  destruct GR as (GR1 & GR2 & GR3). rewrite GR2 in S2, S3.
  apply cb_of_fill in S1. apply cb_of_fill in S3.
  pose proof (cb_app m (shad mb) _ _ _ _ S1 ltac:(rewrite Z2Nat.id by lia; exact S2)) as S12.
  replace (shad mb + 768 + granules n) with (shad mb + Z.of_nat (Z.to_nat 768 + Z.to_nat (granules n))) in S3 by (clear -GR1; lia).
  pose proof (cb_app m (shad mb) _ _ _ _ S12 S3) as S123.
  eexists. replace (Z.to_nat (shlen ms)) with (Z.to_nat 768 + Z.to_nat (granules n) + Z.to_nat (ms / 8 - 768 - granules n))%nat; [exact S123|].
  rewrite shlen_div. clear -GR1 GR3. lia.
Qed.

(* [comment removed for export] *)
Lemma premap_of_rt : forall L m, arep_rt L m -> arep_rt2 m -> arep_rt3 m -> premap_cells m.
Proof.
  intros L m RT RT2 RT3.
  destruct RT3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R11 & R12 & R13 & R14 & R15 & R16 & R17).
  destruct RT2 as (_ & Q2 & _).
  unfold premap_cells. split; [eapply rw_cells_hd'; exact R11|]. split; [exact R13|]. split; [exact Q2|].
  split; [apply premap_word_212a00; exact R14|]. split; [apply premap_word_212a18; exact R15|]. split; [exact R16| exact R17].
Qed.

Lemma poison_cells_of_rt : forall L m, arep_rt L m -> poison_cells m.
Proof.
  intros L m RT.
  destruct RT as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18
                  & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27 & R28).
  unfold poison_cells. repeat lazymatch goal with |- _ /\ _ => split end; assumption.
Qed.

(* [comment removed for export] *)
Lemma asec_chunk_frameD : forall L W m m' mb ms n idx lv,
  munch W m m' -> sec_wf1 L (CSec mb ms n) ->
  (forall A k, mb + 32 <= A -> 0 < k -> A + k <= mb + ms -> disjoint_from W A k) ->
  (forall A k, shad mb <= A -> 0 < k -> A + k <= shad mb + ms / 8 -> disjoint_from W A k) ->
  rw_cells bsegs m' mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 idx)] ->
  (exists idx0, asec_chunk m (CSec mb ms n) idx0 lv) -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros L W m m' mb ms n idx lv MU WF1 DC DS HDR [idx0 CH].
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. destruct WF0 as (G1 & G2 & G3 & G4 & G5 & G6 & _).
  pose proof (sec_facts n ltac:(lia) G6) as (_ & _ & RSE & RSR & _ & NSE & _ & MSR & MSM & _). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  destruct GR as (GR1 & GR2 & GR3).
  cbn [asec_chunk] in CH |- *. destruct CH as (H1 & H2 & H3 & H4 & (b1 & ctx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in *.
  split; [exact HDR|].
  split; [eapply junk_frameD; [exact H2| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frameD; [exact H3| exact MU| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frameD; [exact H4| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frameD; [exact H5| exact MU| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frameD; [exact H6| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frameD; [exact S1| exact MU| intros _; apply DS; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frameD; [exact S2| exact MU| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DS; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frameD; [exact S3| exact MU| intros POS; rewrite GR2; apply DS; clear -GR3 GR1 POS; lia].
Qed.

(* [comment removed for export] *)
Lemma cb_zeros_at : forall m A n j, rw_cells bsegs m A [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
  AIMG_HI <= A -> 0 <= j < n -> m (wa (A + j)) = Some (Z_to_bv 8 0).
Proof.
  intros m A n j [[_ B] _] HA Hj. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. destruct B as (B0 & B1 & B).
  rewrite repeat_length in B1, B. specialize (B (Z.to_nat j) ltac:(lia)). rewrite (@nth_error_repeat _ (Z_to_bv 8 0) (Z.to_nat n) (Z.to_nat j) ltac:(clear -Hj; lia)) in B.
  replace (A + Z.of_nat (Z.to_nat j)) with (A + j) in B by lia.
  unfold mrd in B. destruct (m (wa (A + j))) as [b|] eqn:E; [congruence|].
  exfalso. rewrite ref_seg_rom_none in B; [discriminate|]. rewrite wa_unsigned by lia. unfold AIMG_HI in HA. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fstepS_munmap_after_le : forall a l rsp rsp' R R1 R',
  fp_le R R1 -> fstepS (NMunmap a l) rsp R1 R' -> fstepS (NMunmap a l) rsp' R R'.
Proof.
  intros a l rsp rsp' R R1 R' LE [HA HS]. cbn [fstepA fstepS] in HA, HS |- *. split.
  - intros b j Hb Hd. apply HA; [apply LE; exact Hb| exact Hd].
  - eapply fp_le_trans; [exact LE| exact HS].
Qed.

Theorem srec : srec_stmt ASECc RSEC.
Proof.
  unfold srec_stmt.
  intros AQ AD AF cs1 cs2 R k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m st X mb ms n CBA lo SHO ALO ARNG RS AR MI ST CEIL LO SPHI TP -> -> RA RSTK KONT.
  set (ch := CSec mb ms n) in *. set (cs := cs1 ++ ch :: cs2) in *.
  assert (IN : In ch cs) by (subst cs; apply in_elt).
  (* [comment removed for export] *)
  pose proof (alayout_space L ALO) as (SB1 & SB2 & SB3 & SB4).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_ptr L ALO) as OP. unfold aobj in OT, OC, OP.
  pose proof (ao_space L ALO) as OSP.
  pose proof (ad_t_ptr L ALO) as D_t_p. pose proof (ad_ctx_ptr L ALO) as D_c_p. pose proof (ad_t_ctx L ALO) as D_t_c. unfold adisj in D_t_p, D_c_p, D_t_c.
  (* [comment removed for export] *)
  pose proof AR as AR0.
  destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot ah_fake AHS] in HQ, HS, HD.
  pose proof (poison_cells_of_rt L m RT) as PC. pose proof (premap_of_rt L m RT RT2 RT3) as PRM.
  pose proof RT as RT0.
  destruct RT0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TI & TK & _ & _ & _ & _ & _ & _ & _ & _ & _ & T88 & TSD & _ & _ & CT).
  pose proof INST as INST0. destruct INST0 as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  pose proof THR as THR0. destruct THR0 as (Tc0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  (* [comment removed for export] *)
  pose proof HS as HS0. destruct HS0 as (WFS & SARR & SINST & PZ & SHZ).
  pose proof WFS as (_ & WP & WR & WL & WB & WF1 & WD).
  pose proof SINST as (I80 & [srt ISRT] & JST & JBS & PAD & JGL).
  destruct SARR as (order & PO & U64 & JK & PER).
  pose proof (Permutation_length PO) as LENO.
  assert (WF1o : Forall (sec_wf1 L) order).
  { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PO| exact Hc]. }
  assert (WDo : sec_disjoint order) by (eapply sec_disjoint_perm; [apply Permutation_sym; exact PO| exact WD]).
  pose proof (proj1 (Forall_forall _ _) WF1 ch IN) as WFch.
  destruct (sec_wf1_facts L mb ms n WFch) as (MAL & MLO & MCE & MSE & NB & RZ & MSB & MSAL & NMS & NS0 & SCL).
  pose proof NB as NB0. destruct WFch as (_ & _ & _ & _ & _ & NPR & _).
  pose proof SCL as (SC_t & SC_c & SC_s & SC_p & SC_n & SC_st & SC_f & SC_d).
  (* [comment removed for export] *)
  assert (INo : In ch order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact IN]).
  destruct (In_nth_error _ _ INo) as [i NTH].
  assert (IL : (i < length order)%nat) by (apply (proj1 (nth_error_Some order i)); rewrite NTH; discriminate).
  destruct (nth_error order (length order - 1)) as [lch|] eqn:NTHL.
  2: { exfalso. apply nth_error_None in NTHL. lia. }
  assert (INl : In lch order) by (eapply nth_error_In; exact NTHL).
  pose proof (proj1 (Forall_forall _ _) WF1o lch INl) as WFl.
  destruct lch as [lc lk| lmb lms ln]; [destruct WFl|].
  destruct (sec_wf1_facts L lmb lms ln WFl) as (LAL & LLO & LCE & LMSE & LNB & LRZ & LMSB & LMSAL & _ & _ & LSCL).
  pose proof LSCL as (LC_t & LC_c & LC_s & LC_p & _).
  (* [comment removed for export] *)
  destruct (PER i ch NTH) as (lv & _ & CH). pose proof CH as CH0. unfold ch in CH0. cbn [asec_chunk] in CH0.
  destruct CH0 as (H1 & H2 & H3 & H4 & (b1 & cx & H5 & B1 & B3 & CX) & H6 & S1 & S2 & S3).
  unfold SEC_UOFF in H5. replace (mb + 6144 - 16) with (mb + 6128) in H5 by lia.
  destruct (sec_shadow_cb m mb ms n lv (or_intror (ex_intro _ (Z.of_nat i) CH)) MAL NB MSE NPR) as [shj SH].
  (* [comment removed for export] *)
  assert (LHDR : Z.of_nat i <> a_nsec st - 1 ->
      rw_cells bsegs m lmb [C8 (Z_to_bv 64 lmb); C8 (Z_to_bv 64 lms); C8 (Z_to_bv 64 (needed_size ln)); C8 (Z_to_bv 64 (a_nsec st - 1))]
   /\ ablk lmb (lmb + 32) /\ lmb + 32 <= ATOP /\ (lmb + 32 <= mb \/ mb + ms <= lmb)
   /\ (lmb + 32 <= al_t L \/ al_t L + 4096 <= lmb) /\ (lmb + 32 <= al_ctx L \/ al_ctx L + 4096 <= lmb)
   /\ (lmb + 32 <= al_ptr_array L \/ al_ptr_array L + 8 * a_nres st <= lmb)).
  { destruct (PER _ _ NTHL) as (llv & _ & LCH). cbn [asec_chunk] in LCH. destruct LCH as (L1 & _).
    intros NE.
    assert (NEQ : CSec lmb lms ln <> ch).
    { intros E. apply NE. destruct WDo as [ND _]. rewrite <- E in NTH.
      pose proof (proj1 (NoDup_nth_error order) ND i (length order - 1)%nat IL ltac:(rewrite NTH, NTHL; reflexivity)) as EI.
      rewrite <- WL, <- LENO. clear -EI IL. lia. }
    destruct WDo as [_ DJ]. destruct (DJ _ _ INl INo NEQ) as [DL|DL]; unfold ch in DL; cbn [sec_mb sec_ms] in DL.
    all: replace (a_nsec st - 1) with (Z.of_nat (length order - 1)) by (rewrite <- WL, <- LENO; clear -IL; lia).
    all: split; [exact L1|]. all: unfold K_HIGH_MEM in LLO, LCE, OP |- *.
    all: split; [eapply ablk_sub; [exact LLO| clear; lia| clear -LMSB; lia]|]. all: split; [clear -LCE LMSB; lia|].   (* [comment removed for export] *) all: split; [clear -DL LMSB MSB; lia|].
    all: split; [clear -LC_t LMSB; lia|]. all: split; [clear -LC_c LMSB; lia|]. all: clear -LC_p LMSB WR WB; lia. }
  (* [comment removed for export] *)
  eapply (recycle_sec_spec RNG k st Q) with (mb := mb) (ms := ms) (n := n) (idx := Z.of_nat i) (PA := al_ptr_array L)
     (nres := a_nres st) (nsec := a_nsec st) (last := lmb) (ctx := al_ctx L) (t := al_t L) (SB := al_space_beg L) (CBA := CBA) (lo := lo)
     (bases := map sec_mb order) (lw1 := Z_to_bv 64 lms) (lw2 := Z_to_bv 64 (needed_size ln)) (sj := sj) (hsz := Z_to_bv 64 (needed_size n)) (srt := srt)
     (hst := Z_to_bv 8 (if lv then 2 else 3)) (hb1 := Z_to_bv 8 b1) (hctx := Z_to_bv 64 cx) (shj := shj).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PC
       | |- premap_cells _ => exact PRM
       | |- arelro0 _ => exact HRO
       | |- @eq word _ _ => first [reflexivity | exact TP | f_equal; unfold PG; clear -RZ; lia]
       | |- junk_at _ _ 32 => exact JST
       | |- junk_at _ _ 16 => exact JGL
       | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => apply mtx4_join; [exact I680| exact PAD]
       | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact H5
       | |- rw_cells _ _ _ [CB _ _] => exact SH
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ _ _ => first [eassumption | exact I32 | exact I64 | exact I72 | exact I112 | exact ISRT | exact TI | exact TK | exact T88 | exact TSD | exact H1]
       | |- u64arr _ _ _ (map _ _) => rewrite map_map; exact U64
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- Forall _ _ => eapply bases_dominated; [exact WF1o| exact WDo| exact INo]
       | |- nth_error _ (Z.to_nat (Z.of_nat _)) = _ => rewrite Nat2Z.id, nth_error_map, NTH; reflexivity
       | |- nth_error _ _ = _ => replace (Z.to_nat (a_nsec st - 1)) with (length order - 1)%nat by (rewrite <- WL, <- LENO; lia); rewrite nth_error_map, NTHL; reflexivity
       | |- Z.of_nat (length _) = _ => rewrite length_map, LENO; exact WL
       | |- _ -> _ /\ _ => exact LHDR
       | |- _ -> rng _ _ _ => intros _; pose proof (proj1 (Forall_forall _ _) RS _ (Permutation_in _ PO INl)) as [RL _]; cbn [sec_mb sec_ms] in RL;
                               eapply rng_sub'; [exact RL|]; clear -LMSB; lia
       | |- rng_aimg _ => exact (proj1 ARNG)
       | |- rng _ _ (_ - _) => exact RSTK
       | |- rng _ (shad _) _ => pose proof (proj1 (Forall_forall _ _) RS _ IN) as [_ RH]; cbn [sec_mb sec_ms] in RH; rewrite shlen_div; exact RH
       | |- rng _ (al_ptr_array _) _ => destruct ARNG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RP & _); exact RP
       | |- rng _ (al_t _) _ => destruct ARNG as (_ & RT1 & _); exact RT1
       | |- rng _ (al_ctx _) _ => destruct ARNG as (_ & _ & RC & _); eapply rng_sub'; [exact RC|]; clear; lia
       | |- rng _ _ _ => pose proof (proj1 (Forall_forall _ _) RS _ IN) as [RH _]; cbn [sec_mb sec_ms] in RH; exact RH
       | |- forall _, _ => idtac
       | |- _ => idtac
       end.
  all: unfold K_HIGH_MEM, AREQMAX in CEIL, LO, SPHI, OT, OC, OP, MLO, MCE, NB |- *.
  all: pose proof (alayout_ctx L ALO) as (_ & _ & CXI' & _); pose proof (alayout_t L ALO) as (_ & _ & _ & TIC').   (* [comment removed for export] *)
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | |- iclr _ _ => exact TIC' | |- AIMG_HI <= al_ctx _ => exact CXI' | |- a_nres _ <= 1048576 => clear -WR; lia
       | |- sclr (al_ctx _) _ => exact (proj1 (alayout_ctx L ALO)) | |- sclr (al_t _) _ => exact (proj1 (alayout_t L ALO))
       | |- ablk (al_ptr_array _) _ => pose proof (ao_ptr L ALO) as OPx; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OPx; unfold ablk, KLS, AIMG_HI; clear -OPx; lia
       | |- _ => try first [ assumption | exact SC_t
                       | clear -SC_s OSP; unfold K_SPACE_SIZE, K_SPACE_EXTRA; lia
                       | clear -LO; lia | clear -OC; lia | clear -OT; lia | clear -OP WR WB; lia | clear -IL LENO WL; lia
                       | clear -WB; lia | clear -NB; lia | clear -MSB; lia | clear -SC_c; lia | clear -SC_p WR WB; lia
                       | clear -D_t_p WR WB; lia | clear -D_c_p WR WB; lia | clear -D_t_c; lia ]
       end.
  (* [comment removed for export] *)
  intros RNG1 rsp RNG' m' u0 u1 u2 b0 b1' b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 LE1 HF PP.
  apply KONT. unfold srec_ret.
  destruct PP as (MU & MI' & ST' & NSC' & SRT' & JST' & MTX' & JGL' & ARR' & LHDR' & [sj' [STATS' LSJ']] & SHZ').
  unfold sdealloc_W in MU.
  pose proof (fstepS_le _ _ _ _ HF) as LE2. pose proof (fp_le_trans _ _ _ LE1 LE2) as LE.
  assert (I64b : (Z.of_nat i < a_nsec st)) by (rewrite <- WL, <- LENO; clear -IL; lia).
  exists u0, u1, u2, b0, b1', b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', (lmb + 24).
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { (* [comment removed for export] *) unfold srec_hl_ok, sec_clear, K_HIGH_MEM in *. destruct LSCL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    split; [eapply ablk_sub; [exact LLO| clear; lia| clear -LMSB; lia]|]. split; [clear -LCE LMSB; lia|].   (* [comment removed for export] *)
    repeat lazymatch goal with |- _ /\ _ => split end;
      first [clear -Q1 LMSB; lia | clear -Q2 LMSB; lia | clear -Q3 LMSB; lia | clear -Q4 LMSB; lia
            | clear -Q5 LMSB; lia | clear -Q6 LMSB; lia | clear -Q7 LMSB; lia | clear -Q8 LMSB; lia]. }
  split.
  { (* [comment removed for export] *) replace (lmb + 24 - 24) with lmb by (clear; lia).
    destruct (Z.eq_dec lmb mb) as [E|NE].
    - left. rewrite E. clear -MSB. lia.
    - right. exists lms, ln. split; [| exact WFl].
      assert (INc : In (CSec lmb lms ln) cs) by (eapply Permutation_in; [exact PO| exact INl]).
      subst cs. apply in_app_iff in INc. apply in_app_iff. destruct INc as [H1'|[H1'|H1']]; [left; exact H1'| exfalso; apply NE; unfold ch in H1'; congruence| right; exact H1']. }
  split.
  { (* [comment removed for export] *) eapply munch_weaken; [| exact MU]. unfold srec_W, AINSTANCE.
    let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *. clear -Hq I64b WB LO. lia. }
  split; [exact MI'|]. split; [exact ST'|].
  split.
  2: { split; [eapply fstepS_munmap_after_le; [exact LE1| exact HF]|].
       split.
       - eapply arng_mono; [exact LE|]. eapply arng_st; [| | | exact ARNG]; [intros c Hc; reflexivity| reflexivity|].
         rewrite (sec_chunks_of_eq st (set_nsec (a_nsec st - 1) st)) by reflexivity. apply Permutation_refl.
       - eapply RSEC_mono; [exact LE|]. unfold RSEC in RS |- *. subst cs. rewrite Forall_app in RS |- *.
         destruct RS as [RS1 RS2]. split; [exact RS1| exact (Forall_inv_tail RS2)]. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_fake L ALO) as OFK. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in ORS, ON, OS, OFK, OD.
  pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & [kT OTs] & [jT OTi]). pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (OCi & _ & [kC OCs]).   (* [comment removed for export] *)
  pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (ONi & _ & [kN ONs]). pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (OSi & _ & [kS OSs]).
  pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as (OPi & _ & [kP OPs]). pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & [kF OFKs]).
  pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & [kD ODs] & [jD ODi]). pose proof (ao_res_hi L ALO) as RHI.
  destruct (ablk_int _ _ MLO) as [kA MBND]. pose proof (ablk_lin _ _ MLO) as (ML1 & ML2 & _ & _). unfold AIMG_HI in ML1.
  destruct (ablk_int _ _ LLO) as [kL LBND]. pose proof (ablk_lin _ _ LLO) as (LL1 & _ & _ & _). unfold AIMG_HI in LL1.
  pose proof (ad_t_res L ALO) as D_t_r. pose proof (ad_ptr_res L ALO) as D_p_r. pose proof (ad_t_nodes L ALO) as D_t_n. pose proof (ad_t_store L ALO) as D_t_s.
  pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_ptr L ALO) as D_s_p. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_ptr L ALO) as D_f_p.
  pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p.
  unfold adisj in D_t_r, D_p_r, D_t_n, D_t_s, D_n_p, D_s_p, D_t_f, D_f_p, D_t_d, D_d_p.
  pose proof LSCL as (_ & _ & LC_r & _ & LC_n & LC_st & LC_f & LC_d).
  pose proof SCL as (_ & _ & SC_r & _ & _ & _ & _ & _).
  assert (SHR : 0x800bca00 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ shlen ms = ms / 8)   (* [comment removed for export] *)
    by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -MBND ML1 MCE MSB; Z.div_mod_to_equations; lia).
  assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  assert (RAL8 : al_res L mod 8 = 0) by (destruct ORS as [R8 _]; clear -R8; Z.div_mod_to_equations; lia).
  assert (FAL8 : al_fake L mod 8 = 0) by (destruct OFK as [F8 _]; clear -F8; Z.div_mod_to_equations; lia).
  assert (SHSEP : shad mb + shlen ms <= shad (al_res L) \/ shad (al_res L) + shlen 137439023104 <= shad mb).
  { destruct SC_r as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact RAL8]]. }
  assert (SHSEPF : shad mb + shlen ms <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= shad mb).
  { destruct SC_f as [Dr|Dr]; [left; apply shad_sep; [exact Dr| exact MAL8] | right; apply shad_sep; [exact Dr| exact FAL8]]. }
  assert (RSH : 0x2008fff7000 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                /\ shad (al_res L + 137439023104) <= 0x10007fef8000).   (* [comment removed for export] *)
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI. Z.div_mod_to_equations. lia. }
  destruct RSH as (SR1 & SR2 & SR3).
  assert (FSH : 0x800bca00 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 0x10007fef8000).   (* [comment removed for export] *)
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFK OFKi OFKs. Z.div_mod_to_equations. lia. }
  unfold K_HIGH_MEM in ORS, ON, OS, OFK, OD, LCE, LLO.
  (* [comment removed for export] *)
  lazymatch type of MU with munch ?W _ _ => set (Wd := W) in MU end.
  assert (K_img : forall A kk, 65536 <= A -> 0 <= kk -> (A + kk <= 0xcc710 \/ (0xcc968 <= A /\ A + kk <= AIMG_HI)) -> disjoint_from Wd A kk).   (* [comment removed for export] *)
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. unfold AIMG_HI in Y3. clear -Y1 Y2 Y3 CEIL LO OT OP LLO MLO SHR I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB. lia. }
  assert (K_t : forall A kk, al_t L <= A -> 0 <= kk -> (A + kk <= al_t L + 2800 \/ (al_t L + 3168 <= A /\ A + kk <= al_t L + 4096)) -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO OT D_t_p LC_t SC_t SHR I64b WR WB MSB LMSB OTs OTi. lia. }
  assert (K_ctx : forall A kk, al_ctx L <= A -> 0 <= kk -> A + kk <= al_ctx L + 65536 -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO OC D_t_c D_c_p LC_c SC_c SHR I64b WR WB MSB LMSB OT OTs OTi OCs OCi. lia. }
  assert (K_res : forall A kk, al_res L <= A -> 0 <= kk -> A + kk <= al_res L + 137439023104 -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO ORS D_t_r D_p_r LC_r SC_r SHR I64b WR WB MSB LMSB OT OTs OTi RHI. lia. }
  assert (K_shres : forall A kk, shad (al_res L) <= A -> 0 <= kk -> A + kk <= shad (al_res L + 137439023104) -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO SR1 SR2 SR3 SHSEP SHR OT OP LLO MLO I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB. lia. }
  (* [comment removed for export] *)
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  pose proof (ao_space L ALO) as RSP'. pose proof (alayout_space L ALO) as RSPs.
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP'. lia. }
  (* [comment removed for export] *)
  split; [exact WF|].
  split. { eapply arep_rt_frameD; [exact MU | exact RT |]. unfold rt_hulls, ATP88, ATSD.
           repeat (apply Forall_cons; [cbn [fst snd]; first [apply K_img; clear; unfold AIMG_HI; lia | apply K_ctx; clear; lia] |]). apply Forall_nil. }
  split. { (* [comment removed for export] *) unfold ainstance. cbn [a_nres a_nsec set_nsec]. unfold AINSTANCE in *.
           split; [eapply cells_frameD; [exact I32| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I48| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I64| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I72| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [exact NSC'|].
           split; [exact (proj1 (mtx4_split _ MTX'))|].
           split; [eapply cells_frameD; [exact I984| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           split; [eapply cells_frameD; [exact I40| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
           eapply cells_frameD; [exact I56| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]. }
  split. { (* [comment removed for export] *) unfold athread.
           split; [eapply cells_frameD; [exact Tc0| exact MU| apply K_t; clear; cbn; lia]|].
           split; [eapply cells_frameD; [exact T40| exact MU| apply K_t; clear; cbn; lia]|].
           split. { intros c Hc. eapply acache_cells_frameD; [exact MU | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
                    unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply K_t; clear -Hc; lia. }
           split; [eapply junk_frameD; [exact CSTATS| exact MU| intros _; apply K_t; clear; lia]|].
           split; [exists sj'; split; [exact STATS'| exact LSJ']|].
           eapply cells_frameD; [exact UNW| exact MU| apply K_t; clear; cbn; lia]. }
  split.
  { (* [comment removed for export] *)
    intros c Hc. destruct (CLS c Hc) as (REG & FARR & SLOTS & SHADOW).
    destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & QLENF & QLENC & QCNTB & QND & QRANGE).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
    destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frameD; [exact MU | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply K_res; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP'; lia.
    - eapply afreearray_frameD; [exact MU | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply K_res; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
      + apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - eapply (aslots_updateD L Wd m m' MU st _ X X c (-1)); [exact SLOTS | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
      + intros kq Hk _. pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        split; [reflexivity|]. split.
        * apply K_res; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
        * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
          apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
          split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
      + intros POS. apply K_res; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
    - eapply (aslot_shadow_updateD L Wd m m' MU st _ X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros kq Hk _. pose proof (slot_in_region L st c kq ltac:(clear -QS; lia) (proj1 Q1) Hk) as (P5 & P4 & P0).
        pose proof (slot_aligned L c kq SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
        split; [reflexivity|]. apply K_shres; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply K_shres; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  (* [comment removed for export] *)
  assert (K_nodes : disjoint_from Wd (al_nodes L) 1048576).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO ON D_t_n D_n_p LC_n SC_n SHR I64b WR WB OT LMSB MSB OTs OTi ONs ONi. lia. }
  assert (K_store : disjoint_from Wd (al_store L) 8388608).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO OS D_t_s D_s_p LC_st SC_st SHR I64b WR WB OT LMSB MSB OTs OTi OSs OSi. lia. }
  assert (K_fake : disjoint_from Wd (al_fake L) 11571200).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO OFK D_t_f D_f_p LC_f SC_f SHR I64b WR WB OT LMSB MSB OTs OTi OFKs OFKi. lia. }
  assert (K_dtls : disjoint_from Wd (al_dtls L) 4096).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO OD D_t_d D_d_p LC_d SC_d SHR I64b WR WB OT LMSB MSB OTs OTi ODs ODi. lia. }
  assert (K_shfake : disjoint_from Wd (shad (al_fake L)) (shlen 11571200)).
  { subst Wd. cbn [disjoint_from]. clear -CEIL LO FSH SHSEPF SHR OT OP LLO MLO I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB. lia. }
  (* [comment removed for export] *)
  split.
  { eapply (sho_quar _ _ SHO L st _ X X m m' Wd); [exact HQ | exact MU | |].
    - unfold quar_untouched. apply Forall_forall. intros [qlo qhi] Hin. cbn [fst snd].
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_t (al_t L) 208 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia))) as F1.
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img (AINSTANCE + 728) 256 ltac:(clear; unfold AINSTANCE; lia) ltac:(clear; lia) ltac:(clear; unfold AINSTANCE, AIMG_HI; lia))) as F2.
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0xd0f00 0x81030 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F3.
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x15f788 4 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F4.
      rewrite Forall_forall in F1, F2, F3, F4. specialize (F1 _ Hin). specialize (F2 _ Hin). specialize (F3 _ Hin). specialize (F4 _ Hin). cbn [fst snd] in F1, F2, F3, F4.
      split; [clear -F1; lia|]. split; [clear -F2; lia|]. split; [clear -F3; lia|]. split; [clear -F4; lia|].
      intros b Hb. destruct (BB b Hb) as [B1' B2']. pose proof (size_of_class_facts (xb_class b) (proj1 (BUSY b Hb))) as [QSb _].
      pose proof (proj1 (disjoint_from_Forall _ _ _) (K_res (xb_alloc L b) (size_of_class (xb_class b)) B1' ltac:(clear -QSb; lia) B2')) as F5.
      rewrite Forall_forall in F5. specialize (F5 _ Hin). cbn [fst snd] in F5. destruct (xb_st b); [exact I| clear -F5; lia| clear -F5; lia].
    - unfold quar_same. cbn [a_qloc a_qloc_bytes a_qglob a_qglob_bytes a_space_beg set_nsec].
      repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  (* [comment removed for export] *)
  split.
  2: { (* [comment removed for export] *) split.
       { eapply (sho_depot _ _ SHO L m m' Wd); [exact HD | exact MU |].
         pose proof (proj1 (disjoint_from_Forall _ _ _) (K_img 0x1a1bc8 (0x5f1c10 - 0x1a1bc8) ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; unfold AIMG_HI; lia))) as F1.
         pose proof (proj1 (disjoint_from_Forall _ _ _) K_nodes) as F2. pose proof (proj1 (disjoint_from_Forall _ _ _) K_store) as F3.
         apply Forall_forall. intros [qlo qhi] Hin a Ha. rewrite Forall_forall in F1, F2, F3.
         specialize (F1 _ Hin). specialize (F2 _ Hin). specialize (F3 _ Hin). cbn [fst snd] in F1, F2, F3, Ha. clear -F1 F2 F3 Ha. lia. }
       (* [comment removed for export] *)
       split; [eapply arelro_frameD; [exact MU | exact HRO | apply K_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
       split; [eapply arep_rt2_frameD; [exact MU | exact RT2 | | |]; apply K_img; clear; unfold AIMG_HI; lia|].
       split; [| eapply arep_rt3_frameD; [exact MU | exact RT3 |]; unfold rt3_hulls;
                 repeat (apply Forall_cons; [cbn [fst snd]; apply K_img; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
       intros c Hc. destruct (PERC c Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _). unfold K_NUM_CLASSES in Hc.
       assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                    /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
       { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP'. lia. }
       destruct RI as (RI1 & RI2 & RI3). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
       pose proof (aregion_mod L c SAL) as RM.
       eapply (ashadow_avail_frameD L Wd m m' MU st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | reflexivity | reflexivity | |].
       - intros POS. apply K_shres; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
       - intros POS. apply K_shres; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
         rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
         apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }
  (* [comment removed for export] *)
  assert (K_hi : forall A kk, (A + kk <= 65536 \/ 6443008 <= A) -> (A + kk <= 2147446784 \/ 17594333495296 <= A) -> 0 <= kk -> A + kk <= ATOP ->      (* [comment removed for export] *)
            (A + kk <= mb \/ mb + ms <= A) -> (A + kk <= lmb + 24 \/ lmb + 32 <= A) ->
            (A + kk <= al_t L \/ al_t L + 4096 <= A) -> (A + kk <= al_ptr_array L \/ al_ptr_array L + 8388608 <= A) ->
            disjoint_from Wd A kk).
  { intros A kk Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7. subst Wd. cbn [disjoint_from]. clear -Y0 Y1 Y2 Y3 Y4 Y5 Y6 Y7 CEIL LO SHR I64b WR WB. lia. }
  assert (K_sh : forall A kk, 2147446784 <= A -> 0 <= kk -> A + kk <= 17594333495296 ->      (* [comment removed for export] *)
            (A + kk <= shad mb \/ shad mb + shlen ms <= A) -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3 Y4. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 Y4 CEIL LO OT OP LLO MLO I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB. lia. }
  assert (K_pa : forall A kk, al_ptr_array L + 8 * a_nsec st <= A -> 0 <= kk -> A + kk <= al_ptr_array L + 8388608 -> disjoint_from Wd A kk).
  { intros A kk Y1 Y2 Y3. subst Wd. cbn [disjoint_from]. clear -Y1 Y2 Y3 CEIL LO OP D_t_p LC_p SC_p SHR I64b WR WB MSB LMSB OT OTs OTi OPs OPi. lia. }
  (* [comment removed for export] *)
  assert (CHK : forall j mb' ms' n', nth_error order j = Some (CSec mb' ms' n') -> j <> i ->
             sec_wf1 L (CSec mb' ms' n')
          /\ (mb' + ms' <= mb \/ mb + ms <= mb')
          /\ (forall A kk, mb' + 32 <= A -> 0 < kk -> A + kk <= mb' + ms' -> disjoint_from Wd A kk)
          /\ (forall A kk, shad mb' <= A -> 0 < kk -> A + kk <= shad mb' + ms' / 8 -> disjoint_from Wd A kk)
          /\ ((j <> (length order - 1))%nat -> disjoint_from Wd mb' 32)).
  { intros j mb' ms' n' Hj NEj.
    assert (INj : In (CSec mb' ms' n') order) by (eapply nth_error_In; exact Hj).
    pose proof (proj1 (Forall_forall _ _) WF1o _ INj) as Wj.
    destruct (sec_wf1_facts L mb' ms' n' Wj) as (JAL & JLO & JCE & _ & _ & _ & JMSB & _ & _ & _ & JSCL).
    destruct JSCL as (JC_t & _ & _ & JC_p & _). unfold K_HIGH_MEM in JLO, JCE.
    destruct (ablk_int _ _ JLO) as [kJ JB]. pose proof (ablk_lin _ _ JLO) as (JL1 & _ & _ & _). unfold AIMG_HI in JL1.   (* [comment removed for export] *)
    destruct WDo as [ND DJ].
    assert (NEc : CSec mb' ms' n' <> ch).
    { intros E. apply NEj. apply (proj1 (NoDup_nth_error order) ND j i); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]. rewrite Hj, NTH, E. reflexivity. }
    destruct (DJ _ _ INj INo NEc) as [Dc|Dc]; unfold ch in Dc; cbn [sec_mb sec_ms] in Dc.
    all: assert (JAL8 : mb' mod 8 = 0) by (clear -JAL; Z.div_mod_to_equations; lia).
    all: assert (SHJ : shad mb' + ms' / 8 <= shad mb \/ shad mb + shlen ms <= shad mb')
           by (first [ left; rewrite <- shlen_div; apply shad_sep; [exact Dc| exact JAL8] | right; apply shad_sep; [exact Dc| exact MAL8] ]).
    all: assert (SHJR : 0x800bca00 <= shad mb' /\ shad mb' + ms' / 8 <= 17594333495296)
           by (rewrite shad_div; unfold ASHOFF; clear -JB JL1 JCE JMSB; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    all: assert (DLj : (j = length order - 1)%nat \/ (mb' + ms' <= lmb \/ lmb + lms <= mb')).
    1,3: destruct (Nat.eq_dec j (length order - 1)) as [->|NEl]; [left; reflexivity| right].
    1,2: assert (NEl' : CSec mb' ms' n' <> CSec lmb lms ln)
           by (intros E; apply NEl; apply (proj1 (NoDup_nth_error order) ND j (length order - 1)%nat); [apply (proj1 (nth_error_Some order j)); rewrite Hj; discriminate|]; rewrite Hj, NTHL, E; reflexivity);
         destruct (DJ _ _ INj INl NEl') as [X1|X1]; cbn [sec_mb sec_ms] in X1; [left; exact X1| right; exact X1].
    all: split; [exact Wj|]. all: split; [clear -Dc; lia|].
    all: split; [intros A kk Z1 Z2 Z3; apply K_hi; [clear -Z1 JL1; lia| clear -Z1 Z3 JB; lia| clear -Z2; lia| clear -Z3 JCE; lia| clear -Z1 Z3 Dc MSB; lia| | clear -Z1 Z3 JC_t; lia| clear -Z1 Z3 JC_p; lia] |].
    1,3: destruct DLj as [->|DLj]; [rewrite NTHL in Hj; injection Hj as <- <- <-; clear -Z1 Z3; lia | clear -Z1 Z3 DLj LMSB; lia].
    all: split; [intros A kk Z1 Z2 Z3; apply K_sh; [clear -Z1 SHJR; lia| clear -Z2; lia| clear -Z3 SHJR; lia| clear -Z1 Z3 SHJ; lia] |].
    all: intros NEl; destruct DLj as [E|DLj]; [exfalso; exact (NEl E)|].
    all: apply K_hi; [clear -JL1; lia| clear -JB JMSB; lia| clear; lia| clear -JCE JMSB; lia| clear -Dc MSB JMSB; lia| clear -DLj LMSB JMSB; lia| clear -JC_t JMSB; lia| clear -JC_p JMSB; lia]. }
  (* [comment removed for export] *)
  assert (LEN1 : (1 <= length order)%nat) by (clear -IL; lia).
  assert (NSL : a_nsec st = Z.of_nat (length order)) by (rewrite LENO; symmetry; exact WL).
  assert (JK' : junk_at m' (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))).
  { eapply junk_frameD; [exact JK| exact MU|]. intros POS. apply K_pa; [clear; lia| clear -POS; lia| clear -WR WB POS; lia]. }
  assert (LVE : forall c, sec_live (set_nsec (a_nsec st - 1) st) c <-> sec_live st c) by (intros c; unfold sec_live; cbn [a_live set_nsec]; apply iff_refl).
  assert (WFA : asec_wf L (set_nsec (a_nsec st - 1) st) (cs1 ++ cs2)).
  { unfold asec_wf. cbn [a_ptr_array a_nres a_nsec set_nsec]. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|].
    subst cs. rewrite length_app in WL |- *. cbn [length] in WL.
    split; [clear -WL; lia|]. split; [clear -WL WB; lia|].
    split; [apply Forall_app in WF1 as [F1 F2]; apply Forall_app; split; [exact F1| exact (Forall_inv_tail F2)]|].
    destruct WD as [ND DJ]. split; [exact (NoDup_remove_1 _ _ _ ND)|].
    intros ci cj Hi Hj NE.
    apply DJ; [| | exact NE];
      [apply in_app_iff in Hi; apply in_app_iff; destruct Hi as [Hi|Hi]; [left; exact Hi| right; right; exact Hi]
      |apply in_app_iff in Hj; apply in_app_iff; destruct Hj as [Hj|Hj]; [left; exact Hj| right; right; exact Hj]]. }
  assert (INST' : asec_inst L m').
  { unfold asec_inst. split; [eapply cells_frameD; [exact I80| exact MU| apply K_img; clear; unfold AIMG_HI; cbn; lia]|].
    split; [exists (Z_to_bv 8 0); exact SRT'|]. split; [exact JST'|].
    split; [eapply junk_frameD; [exact JBS| exact MU| intros _; subst Wd; cbn [disjoint_from]; clear -CEIL LO OT OP LLO MLO SHR I64b OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB; lia]|].
    split; [exact (proj2 (mtx4_split _ MTX'))| exact JGL']. }
  assert (PZ' : aprim0 L m').
  { unfold aprim0 in *. eapply azero_frameD; [exact PZ| exact MU|]. intros POS.
    apply K_shres; [apply shad_mono; clear -RSP'; lia| clear -POS; lia|].
    rewrite <- shad_add_shlen by (clear -SB3; unfold K_ALIGN in SB3; Z.div_mod_to_equations; lia). apply shad_mono.
    unfold K_REGION. clear -RSP'. lia. }
  assert (SHZn : ashz L (cs1 ++ cs2) m').
  { intros x Hx HFh HC. unfold K_HIGH_MEM, KLS in Hx. unfold AIMG_HI in Hx.
    assert (SX : 0x800bca00 <= shad x < 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -Hx; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    destruct (Z_lt_le_dec x mb) as [LT|GE]; [| destruct (Z_lt_le_dec x (mb + ms)) as [LT2|GE2]].
    2: { (* [comment removed for export] *)
         replace (shad x) with (shad mb + (shad x - shad mb)) by (clear; lia).
         eapply cb_zeros_at; [exact SHZ'| unfold AIMG_HI; clear -SHR; lia|].
         rewrite !shad_div, shlen_div. clear -GE LT2 MAL8 MSAL. Z.div_mod_to_equations. lia. }
    all: rewrite <- (SHZ x ltac:(unfold K_HIGH_MEM, KLS, AIMG_HI; exact Hx) HFh).
    2,4: subst cs; apply Forall_app in HC as [HC1 HC2]; apply Forall_app; split; [exact HC1| constructor; [unfold ch; cbn [sec_mb sec_ms]; first [clear -LT; lia| clear -GE2; lia]| exact HC2]].
    all: apply MU; rewrite wa_unsigned by (clear -SX; lia); subst Wd; cbn [outside].
    all: pose proof (shad_div mb) as SMB; pose proof (shlen_div ms) as SLM; unfold ASHOFF in SMB.
    all: rewrite shad_div in SX |- *; unfold ASHOFF in SX |- *.
    1: clear -SX Hx LT CEIL LO OT OP LLO MLO I64b MAL8 MSAL SMB SLM SHR OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB; Z.div_mod_to_equations; lia.
    1: clear -SX Hx GE2 CEIL LO OT OP LLO MLO I64b MAL8 MSAL SMB SLM SHR OTs OTi OPs OPi MBND ML1 LBND LL1 WR WB LMSB MSB; Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  rewrite Nat2Z.id, map_map in ARR'.
  unfold ASECc. cbn [a_nsec a_nres set_nsec].
  split; [exact WFA|]. split; [| split; [exact INST'| split; [exact PZ'| exact SHZn]]].
  unfold asec_arr. cbn [a_nsec a_nres set_nsec].
  destruct (Nat.eq_dec i (length order - 1)) as [EQ|NE].
  - (* [comment removed for export] *)
    assert (ELCH : CSec lmb lms ln = ch) by (rewrite <- EQ in NTHL; rewrite NTH in NTHL; unfold ch in NTHL |- *; congruence).
    destruct (nth_error_last_split order (length order - 1) ch ltac:(clear -LEN1; lia) ltac:(rewrite <- EQ; exact NTH)) as [EO LR].
    set (order0 := removelast order) in *.
    exists order0.
    split. { apply Permutation_cons_app_inv with (a := ch). eapply Permutation_trans; [apply Permutation_cons_append|]. rewrite <- EO. exact PO. }
    rewrite EO, map_app in ARR'. cbn [map] in ARR'.
    rewrite EQ, <- LR in ARR'.
    rewrite <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0) [] (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    split; [exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) order0)))
               by (rewrite length_map, LR, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite length_map, LR. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order0)%nat) by (apply (proj1 (nth_error_Some order0 j)); rewrite Hj; discriminate).
    assert (Hj' : nth_error order j = Some c) by (rewrite EO, nth_error_app1 by exact JL; exact Hj).
    assert (NEji : j <> i) by (clear -JL LR EQ; lia).
    destruct (PER j c Hj') as (lvj & LVj & CHj). exists lvj. split; [rewrite LVE; exact LVj|].
    pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
    destruct (CHK j mb' ms' n' Hj' NEji) as (Wj & Dj & DCj & DSj & DHj).
    eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
    pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
    eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL LR; lia].
  - (* [comment removed for export] *)
    destruct (List.nth_error_split order i NTH) as (o1 & rest & EO & LO1).
    assert (RL : length rest = (length order - 1 - i)%nat) by (rewrite EO, length_app; cbn [length]; clear -LO1; lia).
    assert (NTHr : nth_error rest (length rest - 1) = Some (CSec lmb lms ln)).
    { rewrite EO in NTHL at 1. rewrite nth_error_app2 in NTHL by (clear -LO1 IL NE; lia).
      replace (length order - 1 - length o1)%nat with (S (length rest - 1)) in NTHL by (clear -RL LO1 IL NE; lia). cbn [nth_error] in NTHL. exact NTHL. }
    destruct (nth_error_last_split rest (length rest - 1) (CSec lmb lms ln) ltac:(clear -RL IL NE; lia) NTHr) as [ER LR].
    set (o2 := removelast rest) in *.
    exists (o1 ++ CSec lmb lms ln :: o2).
    split. { apply Permutation_cons_app_inv with (a := ch).
             apply (Permutation_trans (l' := o1 ++ ch :: rest)); [| rewrite <- EO; exact PO].
             rewrite ER. apply (Permutation_trans (l' := o1 ++ ch :: CSec lmb lms ln :: o2)).
             - apply Permutation_middle.
             - apply Permutation_app_head. apply perm_skip. apply Permutation_cons_append. }
    rewrite EO, ER, map_app in ARR'. cbn [map] in ARR'. rewrite map_app in ARR'. cbn [map] in ARR'.
    rewrite <- LO1, <- (length_map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) in ARR'.
    rewrite (upd_app_mid (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1) _ (Z_to_bv 64 (sec_mb ch)) (Z_to_bv 64 lmb)) in ARR'.
    rewrite app_comm_cons, app_assoc in ARR'.
    destruct (u64arr_app_inv' _ _ _ _ ARR') as [U1 U2].
    assert (LM : length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2) = (length order - 1)%nat).
    { rewrite length_app. cbn [length]. rewrite !length_map, LR, RL, LO1. clear -IL NE. lia. }
    split; [rewrite map_app; cbn [map]; exact U1|].
    split. { replace (8 * (a_nres st - (a_nsec st - 1))) with (8 * Z.of_nat (length [Z_to_bv 64 lmb]) + 8 * (a_nres st - a_nsec st)) by (cbn [length]; clear; lia).
             replace (al_ptr_array L + 8 * (a_nsec st - 1)) with (al_ptr_array L + 8 * Z.of_nat (length (map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o1 ++ Z_to_bv 64 lmb :: map (fun c : achunk => Z_to_bv 64 (sec_mb c)) o2)))
               by (rewrite LM, NSL; clear -LEN1; lia).
             apply junk_merge; [eapply junk_of_u64arr'; exact U2| | cbn [length]; clear; lia| clear -WB; lia].
             rewrite LM. replace (al_ptr_array L + 8 * Z.of_nat (length order - 1) + 8 * Z.of_nat (length [Z_to_bv 64 lmb])) with (al_ptr_array L + 8 * a_nsec st)
               by (cbn [length]; rewrite NSL; clear -LEN1; lia). exact JK'. }
    intros j c Hj.
    assert (JL : (j < length order - 1)%nat).
    { pose proof (proj1 (nth_error_Some (o1 ++ CSec lmb lms ln :: o2) j) ltac:(rewrite Hj; discriminate)) as XJ.
      rewrite length_app in XJ. cbn [length] in XJ. rewrite LR, RL, LO1 in XJ. clear -IL NE XJ. lia. }
    destruct (Nat.eq_dec j i) as [->|NEji].
    + (* [comment removed for export] *)
      rewrite nth_error_app2 in Hj by (rewrite LO1; clear; lia). rewrite LO1, Nat.sub_diag in Hj. cbn [nth_error] in Hj. injection Hj as <-.
      destruct (PER _ _ NTHL) as (lvl & LVl & CHl). exists lvl. split; [rewrite LVE; exact LVl|].
      destruct (CHK _ lmb lms ln NTHL ltac:(clear -NE; lia)) as (Wj & Dj & DCj & DSj & _).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat (length order - 1)); exact CHl].
      apply LHDR'. rewrite NSL. clear -NE IL. lia.
    + assert (Hj' : nth_error order j = Some c).
      { rewrite EO, ER. destruct (Nat.lt_ge_cases j i) as [LT|GE].
        - rewrite nth_error_app1 in Hj by (rewrite LO1; exact LT). rewrite nth_error_app1 by (rewrite LO1; exact LT). exact Hj.
        - rewrite nth_error_app2 in Hj by (rewrite LO1; exact GE). rewrite nth_error_app2 by (rewrite LO1; exact GE). rewrite LO1 in Hj |- *.
          destruct (j - i)%nat as [|d] eqn:Ed; [exfalso; clear -Ed GE NEji; lia|]. cbn [nth_error] in Hj |- *.
          rewrite nth_error_app1; [exact Hj|]. apply (proj1 (nth_error_Some o2 d)). rewrite Hj. discriminate. }
      destruct (PER j c Hj') as (lvj & LVj & CHj). exists lvj. split; [rewrite LVE; exact LVj|].
      pose proof (proj1 (Forall_forall _ _) WF1o c (nth_error_In _ _ Hj')) as Wc. destruct c as [cc ck|mb' ms' n']; [destruct Wc|].
      destruct (CHK j mb' ms' n' Hj' NEji) as (Wj & Dj & DCj & DSj & DHj).
      eapply asec_chunk_frameD; [exact MU| exact Wj| exact DCj| exact DSj| | exists (Z.of_nat j); exact CHj].
      pose proof CHj as CH1. cbn [asec_chunk] in CH1. destruct CH1 as (Hh & _).
      eapply cells_frameD; [exact Hh| exact MU| cbn; apply DHj; clear -JL; lia].
Qed.
End CANSEC1.
