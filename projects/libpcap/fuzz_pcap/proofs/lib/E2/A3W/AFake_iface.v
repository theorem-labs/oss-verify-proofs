(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr Tac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition FAKESZ : Z := 11571200.                 (* [comment removed for export] *)
Definition FK_NCLS : Z := 11.                      (* [comment removed for export] *)
Definition fk_nframes (c : Z) : Z := 2 ^ (14 - c). (* [comment removed for export] *)
Definition fk_fsize (c : Z) : Z := 2 ^ (6 + c).    (* [comment removed for export] *)
Definition fk_flags (L : alayout) (c : Z) : Z := al_fake L + 4096 + (32768 - 2 ^ (15 - c)).
Definition fk_frames (L : alayout) (c : Z) : Z := al_fake L + 36864 + c * 1048576.
Definition fk_flag (L : alayout) (c pos : Z) : Z := fk_flags L c + pos.
Definition fk_frame (L : alayout) (c pos : Z) : Z := fk_frames L c + pos * fk_fsize c.
(* [comment removed for export] *)
Definition fflag (L : alayout) (c F : Z) : Z := fk_flags L c + (F - fk_frames L c) / fk_fsize c.
(* [comment removed for export] *)
Definition fk_hint (L : alayout) (c : Z) : Z := al_fake L + 8 * c.

#[using="Type"] Lemma fk_fsize_pos : forall c, 0 <= c -> 0 < fk_fsize c.
Proof. intros c Hc. unfold fk_fsize. apply Z.pow_pos_nonneg; lia. Qed.
#[using="Type"] Lemma fk_nframes_pos : forall c, c <= 14 -> 0 < fk_nframes c.
Proof. intros c Hc. unfold fk_nframes. apply Z.pow_pos_nonneg; lia. Qed.
#[using="Type"] Lemma fk_class_bytes : forall c, 0 <= c <= 14 -> fk_nframes c * fk_fsize c = 1048576.
Proof.
  intros c Hc. unfold fk_nframes, fk_fsize. rewrite <- Z.pow_add_r by lia.
  replace (14 - c + (6 + c)) with 20 by lia. reflexivity.
Qed.
#[using="Type"] Lemma fk_flags_off : forall c, 0 <= c <= 14 -> 0 <= 32768 - 2 ^ (15 - c) /\ 32768 - 2 ^ (15 - c) + 2 ^ (14 - c) <= 32768 - 2 ^ (14 - c).
Proof.
  intros c Hc. assert (E : 2 ^ (15 - c) = 2 * 2 ^ (14 - c)).
  { replace (15 - c) with (Z.succ (14 - c)) by lia. rewrite Z.pow_succ_r by lia. reflexivity. }
  rewrite E. assert (0 < 2 ^ (14 - c)) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ (14 - c) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2^14) with 16384 in *. lia.
Qed.
#[using="Type"] Lemma fflag_frame : forall L c pos, 0 <= c -> fflag L c (fk_frame L c pos) = fk_flag L c pos.
Proof.
  intros L c pos Hc. unfold fflag, fk_frame, fk_flag. f_equal.
  pose proof (fk_fsize_pos c Hc). replace (fk_frames L c + pos * fk_fsize c - fk_frames L c) with (pos * fk_fsize c) by lia.
  apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fk_flag_range : forall L c pos, 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c ->
  al_fake L + 4096 <= fk_flag L c pos < al_fake L + 36864.
Proof.
  intros L c pos Hc Hp. unfold fk_flag, fk_flags, FK_NCLS, fk_nframes in *.
  pose proof (fk_flags_off c ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma fk_frame_range : forall L c pos, 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c ->
  fk_frames L c <= fk_frame L c pos /\ fk_frame L c pos + fk_fsize c <= fk_frames L c + 1048576
  /\ al_fake L + 36864 <= fk_frame L c pos /\ fk_frame L c pos + fk_fsize c <= al_fake L + FAKESZ.
Proof.
  intros L c pos Hc Hp. unfold fk_frame, fk_frames, FK_NCLS, FAKESZ in *.
  pose proof (fk_class_bytes c ltac:(lia)) as CB. pose proof (fk_fsize_pos c ltac:(lia)).
  assert (pos * fk_fsize c + fk_fsize c <= 1048576) by nia. nia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma fk_frames_disjoint : forall L c1 p1 c2 p2,
  0 <= c1 < FK_NCLS -> 0 <= p1 < fk_nframes c1 -> 0 <= c2 < FK_NCLS -> 0 <= p2 < fk_nframes c2 ->
  (c1, p1) <> (c2, p2) ->
  fk_frame L c1 p1 + fk_fsize c1 <= fk_frame L c2 p2 \/ fk_frame L c2 p2 + fk_fsize c2 <= fk_frame L c1 p1.
Proof.
  intros L c1 p1 c2 p2 H1 P1 H2 P2 NE.
  (pose proof (fk_frame_range L c1 p1 H1 P1) as ndP__; nd_pre ndP__ 3%nat; intros A1 B1 _; nd_post). (pose proof (fk_frame_range L c2 p2 H2 P2) as ndP__; nd_pre ndP__ 3%nat; intros A2 B2 _; nd_post).
  destruct (Z.eq_dec c1 c2) as [<-|NC].
  - assert (p1 <> p2) by congruence. unfold fk_frame. pose proof (fk_fsize_pos c1 ltac:(lia)). nia.
  - unfold fk_frames in *. nia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma fk_flags_disjoint : forall L c1 p1 c2 p2,
  0 <= c1 < FK_NCLS -> 0 <= p1 < fk_nframes c1 -> 0 <= c2 < FK_NCLS -> 0 <= p2 < fk_nframes c2 ->
  (c1, p1) <> (c2, p2) -> fk_flag L c1 p1 <> fk_flag L c2 p2.
Proof.
  intros L c1 p1 c2 p2 H1 P1 H2 P2 NE. unfold fk_flag, fk_flags, FK_NCLS, fk_nframes in *.
  destruct (Z.eq_dec c1 c2) as [<-|NC]; [assert (p1 <> p2) by congruence; lia|].
  pose proof (fk_flags_off c1 ltac:(lia)) as [X1 Y1]. pose proof (fk_flags_off c2 ltac:(lia)) as [X2 Y2].
  (* [comment removed for export] *)
  assert (MONO : forall a b, 0 <= a -> a < b -> b <= 14 -> 32768 - 2 ^ (15 - a) + 2 ^ (14 - a) <= 32768 - 2 ^ (15 - b)).
  { intros a b Ha Hab Hb.
    assert (E : 2 ^ (15 - a) = 2 * 2 ^ (14 - a)) by (replace (15 - a) with (Z.succ (14 - a)) by lia; rewrite Z.pow_succ_r by lia; reflexivity).
    assert (2 ^ (15 - b) <= 2 ^ (14 - a)) by (apply Z.pow_le_mono_r; lia). lia. }
  destruct (Z.lt_ge_cases c1 c2).
  - pose proof (MONO c1 c2 ltac:(lia) ltac:(lia) ltac:(lia)). lia.
  - pose proof (MONO c2 c1 ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afake_geom (L : alayout) : Prop :=
     al_fake L mod 4096 = 0 /\ ablk (al_fake L) (al_fake L + FAKESZ) /\ al_fake L + FAKESZ <= ATOP
  /\ al_dtls L mod 4096 = 0 /\ (sclr (al_dtls L) 4096 /\ iclr (al_dtls L) 4096 /\ 4096 <= al_dtls L) /\ al_dtls L + 4096 <= ATOP
  /\ (sclr (al_t L) 4096 /\ iclr (al_t L) 4096 /\ 4096 <= al_t L) /\ al_t L + 4096 <= ATOP
  /\ (al_fake L + FAKESZ <= al_dtls L \/ al_dtls L + 4096 <= al_fake L)
  /\ (al_t L + 4096 <= al_dtls L \/ al_dtls L + 4096 <= al_t L)
  /\ (al_t L + 4096 <= al_fake L \/ al_fake L + FAKESZ <= al_t L)
  (* [comment removed for export] *)
  /\ (tclr (al_fake L) FAKESZ /\ tclr (al_dtls L) 4096 /\ tclr (al_t L) 4096).      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition afake_cells (L : alayout) (m : amem) : Prop :=
     rw_cells asegs m 0xa7288 [C8 (Z_to_bv 64 0x9f398)]                                 (* [comment removed for export] *)
  /\ rw_cells asegs m (ATPv + -8) [C8 (Z_to_bv 64 (ATPv + 288)); C8 (Z_to_bv 64 (al_fake L))]   (* [comment removed for export] *)
  /\ rw_cells asegs m (ATPv + 8) [C8 (Z_to_bv 64 (al_dtls L))]                              (* [comment removed for export] *)
  /\ rw_cells asegs m (ATPv + 296) [C8 (Z_to_bv 64 (ATPv + 2048))]                                 (* [comment removed for export] *)
  /\ rw_cells asegs m (al_dtls L + 24) [C8 (Z_to_bv 64 ATPv)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1401b1 [C1 (Z_to_bv 8 1)]                                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0x13e098 [C4 (Z_to_bv 64 0)]                                        (* [comment removed for export] *)
  /\ dc_at m (al_t L + 48) 16.                                                              (* [comment removed for export] *)

End CANSEC1.
Notation FKB c F n := (mkABlock (ABFake c) F n).

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition AFAKE (L : alayout) (LB : list ablock) (m : amem) : Prop :=
     afake_geom L
  /\ afake_cells L m
  (* [comment removed for export] *)
  /\ (exists (h0 h1 h2 : word) (hs : list byte), rw_cells asegs m (al_fake L) [C8 h0; C8 h1; C8 h2; CB 64 hs])
  /\ rw_cells asegs m (al_fake L + 88) [C8 (Z_to_bv 64 20)]
  /\ rw_cells asegs m (al_fake L + 96) [C1 (Z_to_bv 8 0)]
  (* [comment removed for export] *)
  /\ dc_at m (al_fake L + 4096) (FAKESZ - 4096)
  /\ dc_at m (shad (al_fake L)) (shlen FAKESZ)
  (* [comment removed for export] *)
  /\ (forall c pos b, 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c ->
        m (wa (fk_flag L c pos)) = Some b -> b <> Z_to_bv 8 0 ->
        In (FKB c (fk_frame L c pos) (fk_fsize c)) LB)
  /\ (forall c F n, In (FKB c F n) LB ->
        0 <= c < FK_NCLS /\ n = fk_fsize c /\
        exists pos, 0 <= pos < fk_nframes c /\ F = fk_frame L c pos /\ m (wa (fk_flag L c pos)) = Some (Z_to_bv 8 1)).

(* [comment removed for export] *)
Definition afake_rng (L : alayout) (RNG : footprint) : Prop :=
  rng RNG (al_fake L) FAKESZ /\ rng RNG (shad (al_fake L)) (shlen FAKESZ) /\ rng RNG (al_dtls L) 4096.

#[using="Type"] Lemma afake_rng_mono : forall L R R', fp_le R R' -> afake_rng L R -> afake_rng L R'.
Proof.
  intros L R R' LE (A & B & C).
  assert (M : forall lo n, rng R lo n -> rng R' lo n).
  { intros lo n (R1 & R2 & R3). split; [exact R1|]. split; [exact R2|]. intros b j Hb Hj. apply LE. apply R3; assumption. }
  repeat split; try apply M; try assumption; destruct A, B, C; tauto.
Qed.

(* [comment removed for export] *)
Definition afake_untouched (L : alayout) (W : list (Z * Z)) : Prop :=
  Forall (fun iv => (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
                 /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
                 /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
                 /\ (snd iv <= 0xa7288 \/ 0xa7288 + 8 <= fst iv)
                 /\ (snd iv <= (ATPv + -8) \/ (ATPv + -8) + 16 <= fst iv)
                 /\ (snd iv <= (ATPv + 8) \/ (ATPv + 8) + 8 <= fst iv)
                 /\ (snd iv <= (ATPv + 296) \/ (ATPv + 296) + 8 <= fst iv)
                 /\ (snd iv <= 0x1401b1 \/ 0x1401b1 + 1 <= fst iv)
                 /\ (snd iv <= 0x13e098 \/ 0x13e098 + 4 <= fst iv)) W.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma disjoint_from_Forall : forall W A n,
  Forall (fun iv : Z * Z => snd iv <= A \/ A + n <= fst iv) W -> disjoint_from W A n.
Proof. induction W as [|[lo hi] W IH]; intros A n H; cbn; [exact I|]. inversion H; subst. cbn in *. split; [lia| apply IH; assumption]. Qed.

#[using="Type"] Lemma munch_outside_range : forall W m m' A n a,
  munch W m m' -> disjoint_from W A n -> A <= a < A + n -> 0 <= a < 2^64 -> m' (wa a) = m (wa a).
Proof.
  intros W m m' A n a MU D Ha Hr. apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma afake_frame : forall L LB m m' W,
  AFAKE L LB m -> munch W m m' -> wmono asegs m m' -> afake_untouched L W -> AFAKE L LB m'.
Proof.
  intros L LB m m' W (G & CE & (h0 & h1 & h2 & hs & HS) & LOG & NGC & DC1 & DC2 & FL & LV) MU WM UT.
  (pose proof G as ndP__; nd_pre ndP__ 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11; nd_post). unfold FAKESZ in *.
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). unfold AIMG_HI in GL1. (nd_pre G5 3%nat; intros G5s G5i G5; nd_post). (nd_pre G7 3%nat; intros G7s G7i G7; nd_post). unfold iclr, sclr, AIMG_LO, AIMG_HI, KLS in G5s, G5i, G7s, G7i.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (DF : disjoint_from W (al_fake L) 11571200) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X1).
  assert (DS : disjoint_from W (shad (al_fake L)) (shlen 11571200)) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X2).
  assert (DD : disjoint_from W (al_dtls L) 4096) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X3).
  assert (D1 : disjoint_from W 0xa7288 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X4).
  assert (D2 : disjoint_from W (ATPv + -8) 16) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X5).
  assert (D3 : disjoint_from W (ATPv + 8) 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X6).
  assert (D4 : disjoint_from W (ATPv + 296) 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X7).
  assert (D5 : disjoint_from W 0x1401b1 1) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X8).
  assert (D6 : disjoint_from W 0x13e098 4) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X9).
  split; [exact G|].
  split.
  { (nd_pre CE 8%nat; intros C1 C2 C3 C4 C5 C6 C7 C8; nd_post). unfold afake_cells.
    repeat lazymatch goal with |- _ /\ _ => split end;
      try (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize Nat.add]; first [assumption | eapply disjoint_from_sub; [exact DD| lia| lia| lia]]]).
    eapply dc_at_any2; [exact C8| exact WM| clear -G7i; lia]. }   (* [comment removed for export] *)
  split.
  { exists h0, h1, h2, hs. eapply rw_cells_transport; [exact HS| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]. }
  split; [eapply rw_cells_transport; [exact LOG| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply rw_cells_transport; [exact NGC| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
  split.
  { eapply dc_at_any; [exact DC2| exact WM|]. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations; lia. }
  split.
  - intros c pos b Hc Hp Hb NZ. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) in Hb by (assumption || lia). eauto.
  - intros c F n Hin. (nd_pre (LV c F n Hin) 6%nat; intros Hc Hn pos Hp HF Hb; nd_post). split; [exact Hc|]. split; [exact Hn|].
    exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) by (assumption || lia). exact Hb.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma afake_blocks : forall L LB LB' m,
  AFAKE L LB m -> (forall c F n, In (FKB c F n) LB' <-> In (FKB c F n) LB) -> AFAKE L LB' m.
Proof.
  intros L LB LB' m (G & CE & HS & LOG & NGC & DC1 & DC2 & FL & LV) EQ.
  split; [exact G|]. split; [exact CE|]. split; [exact HS|]. split; [exact LOG|]. split; [exact NGC|].
  split; [exact DC1|]. split; [exact DC2|]. split.
  - intros c pos b Hc Hp Hb NZ. apply (proj2 (EQ _ _ _)). eapply FL; eauto.
  - intros c F n Hin. apply LV. apply (proj1 (EQ _ _ _)). exact Hin.
Qed.

#[using="Type"] Lemma afake_heap_cons : forall L LB m p A n, AFAKE L LB m <-> AFAKE L (HB p A n :: LB) m.
Proof.
  intros L LB m p A n. split; intros H; eapply afake_blocks; [exact H| | exact H|]; intros c F k; cbn; split; intros X;
    [destruct X as [X|X]; [discriminate| exact X] | right; exact X | right; exact X | destruct X as [X|X]; [discriminate| exact X]].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fk_frame_al64 : forall L c pos, al_fake L mod 4096 = 0 -> 0 <= c -> fk_frame L c pos mod 64 = 0.
Proof.
  intros L c pos AL Hc. unfold fk_frame, fk_frames, fk_fsize.
  assert (E : 2 ^ (6 + c) = 64 * 2 ^ c) by (rewrite Z.pow_add_r by lia; reflexivity). rewrite E.
  replace (al_fake L + 36864 + c * 1048576 + pos * (64 * 2 ^ c))
     with (al_fake L + 64 * (576 + c * 16384 + pos * 2 ^ c)) by lia.
  rewrite Z.add_mod by lia. rewrite Z.mul_comm, Z.mod_mul by lia.
  replace (al_fake L mod 64) with 0; [reflexivity|].
  symmetry. apply Z.mod_divide; [lia|]. apply Z.mod_divide in AL; [|lia].
  destruct AL as [k Hk]. exists (k * 64). lia.
Qed.

#[using="Type"] Lemma afake_lb : forall L LB m c F n, AFAKE L LB m -> In (FKB c F n) LB ->
  0 <= c < FK_NCLS /\ n = fk_fsize c /\ 0 < n /\ F mod 64 = 0
  /\ al_fake L + 36864 <= F /\ F + n <= al_fake L + FAKESZ
  /\ ablk F (F + n) /\ F + n <= ATOP                                  (* [comment removed for export] *)
  /\ exists pos, 0 <= pos < fk_nframes c /\ F = fk_frame L c pos /\ fflag L c F = fk_flag L c pos
     /\ al_fake L + 4096 <= fflag L c F < al_fake L + 36864.
Proof.
  intros L LB m c F n (G & _ & _ & _ & _ & _ & _ & _ & LV) Hin.
  (nd_pre (LV c F n Hin) 6%nat; intros Hc Hn pos Hp HF _; nd_post). (pose proof (fk_frame_range L c pos Hc Hp) as ndP__; nd_pre ndP__ 4%nat; intros R1 R2 R3 R4; nd_post).
  (nd_pre G 4%nat; intros G1 G2 G3 _; nd_post). (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). unfold AIMG_HI in GL1. pose proof (fk_fsize_pos c ltac:(lia)).
  pose proof (fk_frame_al64 L c pos G1 ltac:(lia)). pose proof (fflag_frame L c pos ltac:(lia)).
  pose proof (fk_flag_range L c pos Hc Hp). unfold FAKESZ in *. subst F n.
  repeat lazymatch goal with |- _ /\ _ => split end; try lia.
  { eapply ablk_sub; [exact G2 | lia | lia]. }
  exists pos. repeat split; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma afake_lb_disjoint : forall L LB m c1 F1 n1 c2 F2 n2,
  AFAKE L LB m -> In (FKB c1 F1 n1) LB -> In (FKB c2 F2 n2) LB -> FKB c1 F1 n1 <> FKB c2 F2 n2 ->
  F1 + n1 <= F2 \/ F2 + n2 <= F1.
Proof.
  intros L LB m c1 F1 n1 c2 F2 n2 AF H1 H2 NE.
  (nd_pre AF 9%nat; intros G _ _ _ _ _ _ _ LV; nd_post).
  (nd_pre (LV _ _ _ H1) 6%nat; intros C1 N1 p1 P1 E1 _; nd_post). (nd_pre (LV _ _ _ H2) 6%nat; intros C2 N2 p2 P2 E2 _; nd_post). subst.
  apply fk_frames_disjoint; try assumption. intros E. injection E as <- <-. apply NE. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma afake_flag : forall L LB m c F n, AFAKE L LB m -> In (FKB c F n) LB ->
  rw_cells asegs m (fflag L c F) [C1 (Z_to_bv 8 1)].
Proof.
  intros L LB m c F n AF Hin. (pose proof (afake_lb L LB m c F n AF Hin) as ndP__; nd_pre ndP__ 13%nat; intros Hc _ _ _ _ _ _ _ pos Hp HF EF FR; nd_post).
  (nd_pre AF 9%nat; intros G _ _ _ _ DC1 _ _ LV; nd_post). (nd_pre (LV _ _ _ Hin) 6%nat; intros _ _ pos' Hp' HF' B1; nd_post).
  assert (pos' = pos) as ->.
  { subst F. unfold fk_frame in HF'. pose proof (fk_fsize_pos c ltac:(lia)). nia. }
  rewrite EF. (nd_pre G 4%nat; intros G1 G2 G3 _; nd_post). (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). unfold AIMG_HI in GL1. unfold FAKESZ in *.
  (* [comment removed for export] *)
  destruct (dc_split m (al_fake L + 4096) (fk_flag L c pos - (al_fake L + 4096)) (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096))) ltac:(replace (fk_flag L c pos - (al_fake L + 4096) + (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096)))) with (FAKESZ - 4096) by (unfold FAKESZ; lia); exact DC1) ltac:(lia) ltac:(lia)) as [_ D2].
  replace (al_fake L + 4096 + (fk_flag L c pos - (al_fake L + 4096))) with (fk_flag L c pos) in D2 by lia.
  destruct (dc_split m (fk_flag L c pos) 1 (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096)) - 1) ltac:(replace (1 + (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096)) - 1)) with (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096))) by lia; exact D2) ltac:(lia) ltac:(lia)) as [D3 _].
  destruct (c1_of_dc m _ D3) as [b Hb].
  assert (b = Z_to_bv 8 1) as ->.
  { destruct Hb as [[WF [B0 [B1' BR]]] WR]. specialize (BR 0%nat ltac:(cbn; lia)). cbn in BR. rewrite Z.add_0_r in BR.
    unfold mrd in BR. rewrite B1 in BR. congruence. }
  exact Hb.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma afake_release : forall L LB m c F n,
  AFAKE L (FKB c F n :: LB) m -> ~ In (FKB c F n) LB ->
  AFAKE L LB (write_to_mem m (wa (fflag L c F)) [Z_to_bv 8 0]).
Proof.
  intros L LB m c F n AF NI.
  (pose proof (afake_lb L _ m c F n AF ltac:(left; reflexivity)) as ndP__; nd_pre ndP__ 13%nat; intros Hc Hn Npos _ _ _ _ _ pos Hp HF EF FR; nd_post).
  pose proof (afake_flag L _ m c F n AF ltac:(left; reflexivity)) as FB. rewrite EF in FB |- *.
  (nd_pre AF 9%nat; intros G CE HS LOG NGC DC1 DC2 FL LV; nd_post). (nd_pre G 4%nat; intros G1 G2 G3 Grest; nd_post). (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). unfold AIMG_HI in GL1.
  (pose proof Grest as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ (_ & G7i & _) _; nd_post). unfold iclr, AIMG_LO, AIMG_HI in G7i. unfold FAKESZ in *.
  (pose proof Grest as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ _ _ _ (TCF & _ & _); nd_post).      (* [comment removed for export] *)
  set (m' := write_to_mem m (wa (fk_flag L c pos)) [Z_to_bv 8 0]).
  assert (MU : munch [(fk_flag L c pos, fk_flag L c pos + 1)] m m').
  { subst m'. apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia]. }
  assert (WM : wmono asegs m m') by (subst m'; apply wmono_write, wmono_refl).
  assert (OUT : forall a, 0 <= a < 2^64 -> a <> fk_flag L c pos -> m' (wa a) = m (wa a)).
  { intros a Ha NE. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  assert (AT : m' (wa (fk_flag L c pos)) = Some (Z_to_bv 8 0)).
  { subst m'. rewrite write_to_mem_spec by (cbn; lia). rewrite wa_unsigned by lia.
    replace (fk_flag L c pos <=? fk_flag L c pos) with true by (symmetry; apply Z.leb_refl).
    cbn [length andb]. rewrite Z.sub_diag.
    replace (fk_flag L c pos <? fk_flag L c pos + Z.of_nat 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  split; [exact (conj G1 (conj G2 (conj G3 Grest)))|].
  split.
  { (nd_pre CE 8%nat; intros X1 X2 X3 X4 X5 X6 X7 X8; nd_post). unfold afake_cells. tclr_int TCF.
    repeat lazymatch goal with |- _ /\ _ => split end;
      try (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; lia]).
    eapply dc_at_any2; [exact X8| exact WM| clear -G7i; lia]. }
  split.
  { (nd_pre HS 5%nat; intros h0 h1 h2 hs HS; nd_post). exists h0, h1, h2, hs. eapply rw_cells_transport; [exact HS| exact MU| exact WM| cbn; lia]. }
  split; [eapply rw_cells_transport; [exact LOG| exact MU| exact WM| cbn; lia]|].
  split; [eapply rw_cells_transport; [exact NGC| exact MU| exact WM| cbn; lia]|].
  split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
  split.
  { eapply dc_at_any; [exact DC2| exact WM|]. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations; lia. }
  split.
  - intros c' pos' b Hc' Hp' Hb NZ.
    destruct (Z.eq_dec (fk_flag L c' pos') (fk_flag L c pos)) as [EQ|NE].
    + exfalso. rewrite EQ, AT in Hb. congruence.
    + pose proof (fk_flag_range L c' pos' Hc' Hp'). rewrite OUT in Hb by lia.
      destruct (FL c' pos' b Hc' Hp' Hb NZ) as [E|IN]; [|exact IN].
      exfalso. injection E as <- EF' _. apply NE. subst F. unfold fk_frame in EF'. pose proof (fk_fsize_pos c ltac:(lia)).
      assert (pos' = pos) by (clear -EF' H0; nia). subst pos'. reflexivity.      (* [comment removed for export] *)
  - intros c' F' n' Hin. (nd_pre (LV c' F' n' ltac:(right; exact Hin)) 6%nat; intros Hc' Hn' pos' Hp' HF' B1; nd_post).
    split; [exact Hc'|]. split; [exact Hn'|]. exists pos'. split; [exact Hp'|]. split; [exact HF'|].
    destruct (Z.eq_dec (fk_flag L c' pos') (fk_flag L c pos)) as [EQ|NE].
    + exfalso. apply NI.
      destruct (Z.eq_dec c' c) as [EC|NC]; [| exfalso; refine (fk_flags_disjoint L c' pos' c pos Hc' Hp' Hc Hp _ EQ); congruence].
      destruct (Z.eq_dec pos' pos) as [EP|NP]; [| exfalso; refine (fk_flags_disjoint L c' pos' c pos Hc' Hp' Hc Hp _ EQ); congruence].
      subst c' pos'. rewrite HF, Hn. rewrite <- HF', <- Hn'. exact Hin.
    + pose proof (fk_flag_range L c' pos' Hc' Hp'). rewrite OUT by lia. exact B1.
Qed.
End CANSEC2.
(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition FAKESZ : Z := 11571200.                 (* [comment removed for export] *)
Definition FK_NCLS : Z := 11.                      (* [comment removed for export] *)
Definition fk_nframes (c : Z) : Z := 2 ^ (14 - c). (* [comment removed for export] *)
Definition fk_fsize (c : Z) : Z := 2 ^ (6 + c).    (* [comment removed for export] *)
Definition fk_flags (L : alayout) (c : Z) : Z := al_fake L + 4096 + (32768 - 2 ^ (15 - c)).
Definition fk_frames (L : alayout) (c : Z) : Z := al_fake L + 36864 + c * 1048576.
Definition fk_flag (L : alayout) (c pos : Z) : Z := fk_flags L c + pos.
Definition fk_frame (L : alayout) (c pos : Z) : Z := fk_frames L c + pos * fk_fsize c.
(* [comment removed for export] *)
Definition fflag (L : alayout) (c F : Z) : Z := fk_flags L c + (F - fk_frames L c) / fk_fsize c.
(* [comment removed for export] *)
Definition fk_hint (L : alayout) (c : Z) : Z := al_fake L + 8 * c.

#[using="Type"] Lemma fk_fsize_pos : forall c, 0 <= c -> 0 < fk_fsize c.
Proof. intros c Hc. unfold fk_fsize. apply Z.pow_pos_nonneg; lia. Qed.
#[using="Type"] Lemma fk_nframes_pos : forall c, c <= 14 -> 0 < fk_nframes c.
Proof. intros c Hc. unfold fk_nframes. apply Z.pow_pos_nonneg; lia. Qed.
#[using="Type"] Lemma fk_class_bytes : forall c, 0 <= c <= 14 -> fk_nframes c * fk_fsize c = 1048576.
Proof.
  intros c Hc. unfold fk_nframes, fk_fsize. rewrite <- Z.pow_add_r by lia.
  replace (14 - c + (6 + c)) with 20 by lia. reflexivity.
Qed.
#[using="Type"] Lemma fk_flags_off : forall c, 0 <= c <= 14 -> 0 <= 32768 - 2 ^ (15 - c) /\ 32768 - 2 ^ (15 - c) + 2 ^ (14 - c) <= 32768 - 2 ^ (14 - c).
Proof.
  intros c Hc. assert (E : 2 ^ (15 - c) = 2 * 2 ^ (14 - c)).
  { replace (15 - c) with (Z.succ (14 - c)) by lia. rewrite Z.pow_succ_r by lia. reflexivity. }
  rewrite E. assert (0 < 2 ^ (14 - c)) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ (14 - c) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2^14) with 16384 in *. lia.
Qed.
#[using="Type"] Lemma fflag_frame : forall L c pos, 0 <= c -> fflag L c (fk_frame L c pos) = fk_flag L c pos.
Proof.
  intros L c pos Hc. unfold fflag, fk_frame, fk_flag. f_equal.
  pose proof (fk_fsize_pos c Hc). replace (fk_frames L c + pos * fk_fsize c - fk_frames L c) with (pos * fk_fsize c) by lia.
  apply Z.div_mul. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fk_flag_range : forall L c pos, 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c ->
  al_fake L + 4096 <= fk_flag L c pos < al_fake L + 36864.
Proof.
  intros L c pos Hc Hp. unfold fk_flag, fk_flags, FK_NCLS, fk_nframes in *.
  pose proof (fk_flags_off c ltac:(lia)). lia.
Qed.
#[using="Type"] Lemma fk_frame_range : forall L c pos, 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c ->
  fk_frames L c <= fk_frame L c pos /\ fk_frame L c pos + fk_fsize c <= fk_frames L c + 1048576
  /\ al_fake L + 36864 <= fk_frame L c pos /\ fk_frame L c pos + fk_fsize c <= al_fake L + FAKESZ.
Proof.
  intros L c pos Hc Hp. unfold fk_frame, fk_frames, FK_NCLS, FAKESZ in *.
  pose proof (fk_class_bytes c ltac:(lia)) as CB. pose proof (fk_fsize_pos c ltac:(lia)).
  assert (pos * fk_fsize c + fk_fsize c <= 1048576) by nia. nia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma fk_frames_disjoint : forall L c1 p1 c2 p2,
  0 <= c1 < FK_NCLS -> 0 <= p1 < fk_nframes c1 -> 0 <= c2 < FK_NCLS -> 0 <= p2 < fk_nframes c2 ->
  (c1, p1) <> (c2, p2) ->
  fk_frame L c1 p1 + fk_fsize c1 <= fk_frame L c2 p2 \/ fk_frame L c2 p2 + fk_fsize c2 <= fk_frame L c1 p1.
Proof.
  intros L c1 p1 c2 p2 H1 P1 H2 P2 NE.
  (pose proof (fk_frame_range L c1 p1 H1 P1) as ndP__; nd_pre ndP__ 3%nat; intros A1 B1 _; nd_post). (pose proof (fk_frame_range L c2 p2 H2 P2) as ndP__; nd_pre ndP__ 3%nat; intros A2 B2 _; nd_post).
  destruct (Z.eq_dec c1 c2) as [<-|NC].
  - assert (p1 <> p2) by congruence. unfold fk_frame. pose proof (fk_fsize_pos c1 ltac:(lia)). nia.
  - unfold fk_frames in *. nia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma fk_flags_disjoint : forall L c1 p1 c2 p2,
  0 <= c1 < FK_NCLS -> 0 <= p1 < fk_nframes c1 -> 0 <= c2 < FK_NCLS -> 0 <= p2 < fk_nframes c2 ->
  (c1, p1) <> (c2, p2) -> fk_flag L c1 p1 <> fk_flag L c2 p2.
Proof.
  intros L c1 p1 c2 p2 H1 P1 H2 P2 NE. unfold fk_flag, fk_flags, FK_NCLS, fk_nframes in *.
  destruct (Z.eq_dec c1 c2) as [<-|NC]; [assert (p1 <> p2) by congruence; lia|].
  pose proof (fk_flags_off c1 ltac:(lia)) as [X1 Y1]. pose proof (fk_flags_off c2 ltac:(lia)) as [X2 Y2].
  (* [comment removed for export] *)
  assert (MONO : forall a b, 0 <= a -> a < b -> b <= 14 -> 32768 - 2 ^ (15 - a) + 2 ^ (14 - a) <= 32768 - 2 ^ (15 - b)).
  { intros a b Ha Hab Hb.
    assert (E : 2 ^ (15 - a) = 2 * 2 ^ (14 - a)) by (replace (15 - a) with (Z.succ (14 - a)) by lia; rewrite Z.pow_succ_r by lia; reflexivity).
    assert (2 ^ (15 - b) <= 2 ^ (14 - a)) by (apply Z.pow_le_mono_r; lia). lia. }
  destruct (Z.lt_ge_cases c1 c2).
  - pose proof (MONO c1 c2 ltac:(lia) ltac:(lia) ltac:(lia)). lia.
  - pose proof (MONO c2 c1 ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition afake_geom (L : alayout) : Prop :=
     al_fake L mod 4096 = 0 /\ ablk (al_fake L) (al_fake L + FAKESZ) /\ al_fake L + FAKESZ <= ATOP
  /\ al_dtls L mod 4096 = 0 /\ (sclr (al_dtls L) 4096 /\ iclr (al_dtls L) 4096 /\ 4096 <= al_dtls L) /\ al_dtls L + 4096 <= ATOP
  /\ (sclr (al_t L) 4096 /\ iclr (al_t L) 4096 /\ 4096 <= al_t L) /\ al_t L + 4096 <= ATOP
  /\ (al_fake L + FAKESZ <= al_dtls L \/ al_dtls L + 4096 <= al_fake L)
  /\ (al_t L + 4096 <= al_dtls L \/ al_dtls L + 4096 <= al_t L)
  /\ (al_t L + 4096 <= al_fake L \/ al_fake L + FAKESZ <= al_t L)
  (* [comment removed for export] *)
  /\ (tclr (al_fake L) FAKESZ /\ tclr (al_dtls L) 4096 /\ tclr (al_t L) 4096).      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition afake_cells (L : alayout) (m : amem) : Prop :=
     rw_cells asegs m 0xa7668 [C8 (Z_to_bv 64 0x9f77c)]                                 (* [comment removed for export] *)
  /\ rw_cells asegs m (ATPv + -8) [C8 (Z_to_bv 64 (ATPv + 288)); C8 (Z_to_bv 64 (al_fake L))]   (* [comment removed for export] *)
  /\ rw_cells asegs m (ATPv + 8) [C8 (Z_to_bv 64 (al_dtls L))]                              (* [comment removed for export] *)
  /\ rw_cells asegs m (ATPv + 296) [C8 (Z_to_bv 64 (ATPv + 2048))]                                 (* [comment removed for export] *)
  /\ rw_cells asegs m (al_dtls L + 24) [C8 (Z_to_bv 64 ATPv)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1405b1 [C1 (Z_to_bv 8 1)]                                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0x13e498 [C4 (Z_to_bv 64 0)]                                        (* [comment removed for export] *)
  /\ dc_at m (al_t L + 48) 16.                                                              (* [comment removed for export] *)

End CANSEC1.
Notation FKB c F n := (mkABlock (ABFake c) F n).

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition AFAKE (L : alayout) (LB : list ablock) (m : amem) : Prop :=
     afake_geom L
  /\ afake_cells L m
  (* [comment removed for export] *)
  /\ (exists (h0 h1 h2 : word) (hs : list byte), rw_cells asegs m (al_fake L) [C8 h0; C8 h1; C8 h2; CB 64 hs])
  /\ rw_cells asegs m (al_fake L + 88) [C8 (Z_to_bv 64 20)]
  /\ rw_cells asegs m (al_fake L + 96) [C1 (Z_to_bv 8 0)]
  (* [comment removed for export] *)
  /\ dc_at m (al_fake L + 4096) (FAKESZ - 4096)
  /\ dc_at m (shad (al_fake L)) (shlen FAKESZ)
  (* [comment removed for export] *)
  /\ (forall c pos b, 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c ->
        m (wa (fk_flag L c pos)) = Some b -> b <> Z_to_bv 8 0 ->
        In (FKB c (fk_frame L c pos) (fk_fsize c)) LB)
  /\ (forall c F n, In (FKB c F n) LB ->
        0 <= c < FK_NCLS /\ n = fk_fsize c /\
        exists pos, 0 <= pos < fk_nframes c /\ F = fk_frame L c pos /\ m (wa (fk_flag L c pos)) = Some (Z_to_bv 8 1)).

(* [comment removed for export] *)
Definition afake_rng (L : alayout) (RNG : footprint) : Prop :=
  rng RNG (al_fake L) FAKESZ /\ rng RNG (shad (al_fake L)) (shlen FAKESZ) /\ rng RNG (al_dtls L) 4096.

#[using="Type"] Lemma afake_rng_mono : forall L R R', fp_le R R' -> afake_rng L R -> afake_rng L R'.
Proof.
  intros L R R' LE (A & B & C).
  assert (M : forall lo n, rng R lo n -> rng R' lo n).
  { intros lo n (R1 & R2 & R3). split; [exact R1|]. split; [exact R2|]. intros b j Hb Hj. apply LE. apply R3; assumption. }
  repeat split; try apply M; try assumption; destruct A, B, C; tauto.
Qed.

(* [comment removed for export] *)
Definition afake_untouched (L : alayout) (W : list (Z * Z)) : Prop :=
  Forall (fun iv => (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
                 /\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
                 /\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
                 /\ (snd iv <= 0xa7668 \/ 0xa7668 + 8 <= fst iv)
                 /\ (snd iv <= (ATPv + -8) \/ (ATPv + -8) + 16 <= fst iv)
                 /\ (snd iv <= (ATPv + 8) \/ (ATPv + 8) + 8 <= fst iv)
                 /\ (snd iv <= (ATPv + 296) \/ (ATPv + 296) + 8 <= fst iv)
                 /\ (snd iv <= 0x1405b1 \/ 0x1405b1 + 1 <= fst iv)
                 /\ (snd iv <= 0x13e498 \/ 0x13e498 + 4 <= fst iv)) W.

(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma disjoint_from_Forall : forall W A n,
  Forall (fun iv : Z * Z => snd iv <= A \/ A + n <= fst iv) W -> disjoint_from W A n.
Proof. induction W as [|[lo hi] W IH]; intros A n H; cbn; [exact I|]. inversion H; subst. cbn in *. split; [lia| apply IH; assumption]. Qed.

#[using="Type"] Lemma munch_outside_range : forall W m m' A n a,
  munch W m m' -> disjoint_from W A n -> A <= a < A + n -> 0 <= a < 2^64 -> m' (wa a) = m (wa a).
Proof.
  intros W m m' A n a MU D Ha Hr. apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma afake_frame : forall L LB m m' W,
  AFAKE L LB m -> munch W m m' -> wmono asegs m m' -> afake_untouched L W -> AFAKE L LB m'.
Proof.
  intros L LB m m' W (G & CE & (h0 & h1 & h2 & hs & HS) & LOG & NGC & DC1 & DC2 & FL & LV) MU WM UT.
  (pose proof G as ndP__; nd_pre ndP__ 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11; nd_post). unfold FAKESZ in *.
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). unfold AIMG_HI in GL1. (nd_pre G5 3%nat; intros G5s G5i G5; nd_post). (nd_pre G7 3%nat; intros G7s G7i G7; nd_post). unfold iclr, sclr, AIMG_LO, AIMG_HI, KLS in G5s, G5i, G7s, G7i.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (DF : disjoint_from W (al_fake L) 11571200) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X1).
  assert (DS : disjoint_from W (shad (al_fake L)) (shlen 11571200)) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X2).
  assert (DD : disjoint_from W (al_dtls L) 4096) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X3).
  assert (D1 : disjoint_from W 0xa7668 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X4).
  assert (D2 : disjoint_from W (ATPv + -8) 16) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X5).
  assert (D3 : disjoint_from W (ATPv + 8) 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X6).
  assert (D4 : disjoint_from W (ATPv + 296) 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X7).
  assert (D5 : disjoint_from W 0x1405b1 1) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X8).
  assert (D6 : disjoint_from W 0x13e498 4) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X9).
  split; [exact G|].
  split.
  { (nd_pre CE 8%nat; intros C1 C2 C3 C4 C5 C6 C7 C8; nd_post). unfold afake_cells.
    repeat lazymatch goal with |- _ /\ _ => split end;
      try (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize Nat.add]; first [assumption | eapply disjoint_from_sub; [exact DD| lia| lia| lia]]]).
    eapply dc_at_any2; [exact C8| exact WM| clear -G7i; lia]. }   (* [comment removed for export] *)
  split.
  { exists h0, h1, h2, hs. eapply rw_cells_transport; [exact HS| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]. }
  split; [eapply rw_cells_transport; [exact LOG| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply rw_cells_transport; [exact NGC| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
  split.
  { eapply dc_at_any; [exact DC2| exact WM|]. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations; lia. }
  split.
  - intros c pos b Hc Hp Hb NZ. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) in Hb by (assumption || lia). eauto.
  - intros c F n Hin. (nd_pre (LV c F n Hin) 6%nat; intros Hc Hn pos Hp HF Hb; nd_post). split; [exact Hc|]. split; [exact Hn|].
    exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) by (assumption || lia). exact Hb.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma afake_blocks : forall L LB LB' m,
  AFAKE L LB m -> (forall c F n, In (FKB c F n) LB' <-> In (FKB c F n) LB) -> AFAKE L LB' m.
Proof.
  intros L LB LB' m (G & CE & HS & LOG & NGC & DC1 & DC2 & FL & LV) EQ.
  split; [exact G|]. split; [exact CE|]. split; [exact HS|]. split; [exact LOG|]. split; [exact NGC|].
  split; [exact DC1|]. split; [exact DC2|]. split.
  - intros c pos b Hc Hp Hb NZ. apply (proj2 (EQ _ _ _)). eapply FL; eauto.
  - intros c F n Hin. apply LV. apply (proj1 (EQ _ _ _)). exact Hin.
Qed.

#[using="Type"] Lemma afake_heap_cons : forall L LB m p A n, AFAKE L LB m <-> AFAKE L (HB p A n :: LB) m.
Proof.
  intros L LB m p A n. split; intros H; eapply afake_blocks; [exact H| | exact H|]; intros c F k; cbn; split; intros X;
    [destruct X as [X|X]; [discriminate| exact X] | right; exact X | right; exact X | destruct X as [X|X]; [discriminate| exact X]].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fk_frame_al64 : forall L c pos, al_fake L mod 4096 = 0 -> 0 <= c -> fk_frame L c pos mod 64 = 0.
Proof.
  intros L c pos AL Hc. unfold fk_frame, fk_frames, fk_fsize.
  assert (E : 2 ^ (6 + c) = 64 * 2 ^ c) by (rewrite Z.pow_add_r by lia; reflexivity). rewrite E.
  replace (al_fake L + 36864 + c * 1048576 + pos * (64 * 2 ^ c))
     with (al_fake L + 64 * (576 + c * 16384 + pos * 2 ^ c)) by lia.
  rewrite Z.add_mod by lia. rewrite Z.mul_comm, Z.mod_mul by lia.
  replace (al_fake L mod 64) with 0; [reflexivity|].
  symmetry. apply Z.mod_divide; [lia|]. apply Z.mod_divide in AL; [|lia].
  destruct AL as [k Hk]. exists (k * 64). lia.
Qed.

#[using="Type"] Lemma afake_lb : forall L LB m c F n, AFAKE L LB m -> In (FKB c F n) LB ->
  0 <= c < FK_NCLS /\ n = fk_fsize c /\ 0 < n /\ F mod 64 = 0
  /\ al_fake L + 36864 <= F /\ F + n <= al_fake L + FAKESZ
  /\ ablk F (F + n) /\ F + n <= ATOP                                  (* [comment removed for export] *)
  /\ exists pos, 0 <= pos < fk_nframes c /\ F = fk_frame L c pos /\ fflag L c F = fk_flag L c pos
     /\ al_fake L + 4096 <= fflag L c F < al_fake L + 36864.
Proof.
  intros L LB m c F n (G & _ & _ & _ & _ & _ & _ & _ & LV) Hin.
  (nd_pre (LV c F n Hin) 6%nat; intros Hc Hn pos Hp HF _; nd_post). (pose proof (fk_frame_range L c pos Hc Hp) as ndP__; nd_pre ndP__ 4%nat; intros R1 R2 R3 R4; nd_post).
  (nd_pre G 4%nat; intros G1 G2 G3 _; nd_post). (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). unfold AIMG_HI in GL1. pose proof (fk_fsize_pos c ltac:(lia)).
  pose proof (fk_frame_al64 L c pos G1 ltac:(lia)). pose proof (fflag_frame L c pos ltac:(lia)).
  pose proof (fk_flag_range L c pos Hc Hp). unfold FAKESZ in *. subst F n.
  repeat lazymatch goal with |- _ /\ _ => split end; try lia.
  { eapply ablk_sub; [exact G2 | lia | lia]. }
  exists pos. repeat split; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma afake_lb_disjoint : forall L LB m c1 F1 n1 c2 F2 n2,
  AFAKE L LB m -> In (FKB c1 F1 n1) LB -> In (FKB c2 F2 n2) LB -> FKB c1 F1 n1 <> FKB c2 F2 n2 ->
  F1 + n1 <= F2 \/ F2 + n2 <= F1.
Proof.
  intros L LB m c1 F1 n1 c2 F2 n2 AF H1 H2 NE.
  (nd_pre AF 9%nat; intros G _ _ _ _ _ _ _ LV; nd_post).
  (nd_pre (LV _ _ _ H1) 6%nat; intros C1 N1 p1 P1 E1 _; nd_post). (nd_pre (LV _ _ _ H2) 6%nat; intros C2 N2 p2 P2 E2 _; nd_post). subst.
  apply fk_frames_disjoint; try assumption. intros E. injection E as <- <-. apply NE. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma afake_flag : forall L LB m c F n, AFAKE L LB m -> In (FKB c F n) LB ->
  rw_cells asegs m (fflag L c F) [C1 (Z_to_bv 8 1)].
Proof.
  intros L LB m c F n AF Hin. (pose proof (afake_lb L LB m c F n AF Hin) as ndP__; nd_pre ndP__ 13%nat; intros Hc _ _ _ _ _ _ _ pos Hp HF EF FR; nd_post).
  (nd_pre AF 9%nat; intros G _ _ _ _ DC1 _ _ LV; nd_post). (nd_pre (LV _ _ _ Hin) 6%nat; intros _ _ pos' Hp' HF' B1; nd_post).
  assert (pos' = pos) as ->.
  { subst F. unfold fk_frame in HF'. pose proof (fk_fsize_pos c ltac:(lia)). nia. }
  rewrite EF. (nd_pre G 4%nat; intros G1 G2 G3 _; nd_post). (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). unfold AIMG_HI in GL1. unfold FAKESZ in *.
  (* [comment removed for export] *)
  destruct (dc_split m (al_fake L + 4096) (fk_flag L c pos - (al_fake L + 4096)) (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096))) ltac:(replace (fk_flag L c pos - (al_fake L + 4096) + (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096)))) with (FAKESZ - 4096) by (unfold FAKESZ; lia); exact DC1) ltac:(lia) ltac:(lia)) as [_ D2].
  replace (al_fake L + 4096 + (fk_flag L c pos - (al_fake L + 4096))) with (fk_flag L c pos) in D2 by lia.
  destruct (dc_split m (fk_flag L c pos) 1 (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096)) - 1) ltac:(replace (1 + (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096)) - 1)) with (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096))) by lia; exact D2) ltac:(lia) ltac:(lia)) as [D3 _].
  destruct (c1_of_dc m _ D3) as [b Hb].
  assert (b = Z_to_bv 8 1) as ->.
  { destruct Hb as [[WF [B0 [B1' BR]]] WR]. specialize (BR 0%nat ltac:(cbn; lia)). cbn in BR. rewrite Z.add_0_r in BR.
    unfold mrd in BR. rewrite B1 in BR. congruence. }
  exact Hb.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma afake_release : forall L LB m c F n,
  AFAKE L (FKB c F n :: LB) m -> ~ In (FKB c F n) LB ->
  AFAKE L LB (write_to_mem m (wa (fflag L c F)) [Z_to_bv 8 0]).
Proof.
  intros L LB m c F n AF NI.
  (pose proof (afake_lb L _ m c F n AF ltac:(left; reflexivity)) as ndP__; nd_pre ndP__ 13%nat; intros Hc Hn Npos _ _ _ _ _ pos Hp HF EF FR; nd_post).
  pose proof (afake_flag L _ m c F n AF ltac:(left; reflexivity)) as FB. rewrite EF in FB |- *.
  (nd_pre AF 9%nat; intros G CE HS LOG NGC DC1 DC2 FL LV; nd_post). (nd_pre G 4%nat; intros G1 G2 G3 Grest; nd_post). (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post). unfold AIMG_HI in GL1.
  (pose proof Grest as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ (_ & G7i & _) _; nd_post). unfold iclr, AIMG_LO, AIMG_HI in G7i. unfold FAKESZ in *.
  (pose proof Grest as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ _ _ _ _ _ (TCF & _ & _); nd_post).      (* [comment removed for export] *)
  set (m' := write_to_mem m (wa (fk_flag L c pos)) [Z_to_bv 8 0]).
  assert (MU : munch [(fk_flag L c pos, fk_flag L c pos + 1)] m m').
  { subst m'. apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia]. }
  assert (WM : wmono asegs m m') by (subst m'; apply wmono_write, wmono_refl).
  assert (OUT : forall a, 0 <= a < 2^64 -> a <> fk_flag L c pos -> m' (wa a) = m (wa a)).
  { intros a Ha NE. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
  assert (AT : m' (wa (fk_flag L c pos)) = Some (Z_to_bv 8 0)).
  { subst m'. rewrite write_to_mem_spec by (cbn; lia). rewrite wa_unsigned by lia.
    replace (fk_flag L c pos <=? fk_flag L c pos) with true by (symmetry; apply Z.leb_refl).
    cbn [length andb]. rewrite Z.sub_diag.
    replace (fk_flag L c pos <? fk_flag L c pos + Z.of_nat 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  split; [exact (conj G1 (conj G2 (conj G3 Grest)))|].
  split.
  { (nd_pre CE 8%nat; intros X1 X2 X3 X4 X5 X6 X7 X8; nd_post). unfold afake_cells. tclr_int TCF.
    repeat lazymatch goal with |- _ /\ _ => split end;
      try (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; lia]).
    eapply dc_at_any2; [exact X8| exact WM| clear -G7i; lia]. }
  split.
  { (nd_pre HS 5%nat; intros h0 h1 h2 hs HS; nd_post). exists h0, h1, h2, hs. eapply rw_cells_transport; [exact HS| exact MU| exact WM| cbn; lia]. }
  split; [eapply rw_cells_transport; [exact LOG| exact MU| exact WM| cbn; lia]|].
  split; [eapply rw_cells_transport; [exact NGC| exact MU| exact WM| cbn; lia]|].
  split; [eapply dc_at_any; [exact DC1| exact WM| lia]|].
  split.
  { eapply dc_at_any; [exact DC2| exact WM|]. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations; lia. }
  split.
  - intros c' pos' b Hc' Hp' Hb NZ.
    destruct (Z.eq_dec (fk_flag L c' pos') (fk_flag L c pos)) as [EQ|NE].
    + exfalso. rewrite EQ, AT in Hb. congruence.
    + pose proof (fk_flag_range L c' pos' Hc' Hp'). rewrite OUT in Hb by lia.
      destruct (FL c' pos' b Hc' Hp' Hb NZ) as [E|IN]; [|exact IN].
      exfalso. injection E as <- EF' _. apply NE. subst F. unfold fk_frame in EF'. pose proof (fk_fsize_pos c ltac:(lia)).
      assert (pos' = pos) by (clear -EF' H0; nia). subst pos'. reflexivity.      (* [comment removed for export] *)
  - intros c' F' n' Hin. (nd_pre (LV c' F' n' ltac:(right; exact Hin)) 6%nat; intros Hc' Hn' pos' Hp' HF' B1; nd_post).
    split; [exact Hc'|]. split; [exact Hn'|]. exists pos'. split; [exact Hp'|]. split; [exact HF'|].
    destruct (Z.eq_dec (fk_flag L c' pos') (fk_flag L c pos)) as [EQ|NE].
    + exfalso. apply NI.
      destruct (Z.eq_dec c' c) as [EC|NC]; [| exfalso; refine (fk_flags_disjoint L c' pos' c pos Hc' Hp' Hc Hp _ EQ); congruence].
      destruct (Z.eq_dec pos' pos) as [EP|NP]; [| exfalso; refine (fk_flags_disjoint L c' pos' c pos Hc' Hp' Hc Hp _ EQ); congruence].
      subst c' pos'. rewrite HF, Hn. rewrite <- HF', <- Hn'. exact Hin.
    + pose proof (fk_flag_range L c' pos' Hc' Hp'). rewrite OUT by lia. exact B1.
Qed.
End CANSEC2.
(* [comment removed for export] *)
End TwB.
