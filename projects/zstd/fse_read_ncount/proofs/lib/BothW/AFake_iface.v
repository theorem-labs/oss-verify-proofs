(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr Tac InitMem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import BImg ABase ALayout FsKit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Definition FAKESZ : Z := 11571200.
Definition FK_NCLS : Z := 11.
Definition fk_nframes (c : Z) : Z := 2 ^ (14 - c).
Definition fk_fsize (c : Z) : Z := 2 ^ (6 + c).
Definition fk_flags (L : alayout) (c : Z) : Z := al_fake L + 4096 + (32768 - 2 ^ (15 - c)).
Definition fk_frames (L : alayout) (c : Z) : Z := al_fake L + 36864 + c * 1048576.
Definition fk_flag (L : alayout) (c pos : Z) : Z := fk_flags L c + pos.
Definition fk_frame (L : alayout) (c pos : Z) : Z := fk_frames L c + pos * fk_fsize c.
Definition fflag (L : alayout) (c F : Z) : Z := fk_flags L c + (F - fk_frames L c) / fk_fsize c.
#[using="Type"] Lemma fk_fsize_pos : forall c, 0 <= c -> 0 < fk_fsize c.
Proof. intros c Hc. unfold fk_fsize. apply Z.pow_pos_nonneg; lia. Qed.
#[using="Type"] Lemma fk_class_bytes : forall c, 0 <= c <= 14 -> fk_nframes c * fk_fsize c = 1048576.
Proof.
intros c Hc. unfold fk_nframes, fk_fsize. Local Ltac2 Set LiaHints.tbl := fun () => "0030=29804881703.350307803815.350832180514.3000004008009S2HcS2HcS".
rewrite <- Z.pow_add_r by lia.
replace (14 - c + (6 + c)) with 20 by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fk_flags_off : forall c, 0 <= c <= 14 -> 0 <= 32768 - 2 ^ (15 - c) /\ 32768 - 2 ^ (15 - c) + 2 ^ (14 - c) <= 32768 - 2 ^ (14 - c).
Proof.
intros c Hc. assert (E : 2 ^ (15 - c) = 2 * 2 ^ (14 - c)).
{ Local Ltac2 Set LiaHints.tbl := fun () => "0070=22508313363.32323572090.5 29804881703.329811095109.441422282358.541422330361.460960848180.600000100500900=00>00?00CSS2HcS2HcS2HcSSS2H0".
replace (15 - c) with (Z.succ (14 - c)) by lia. rewrite Z.pow_succ_r by lia. reflexivity. }
rewrite E. assert (0 < 2 ^ (14 - c)) by (apply Z.pow_pos_nonneg; lia).
assert (2 ^ (14 - c) <= 2 ^ 14) by (apply Z.pow_le_mono_r; lia). change (2^14) with 16384 in *. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fflag_frame : forall L c pos, 0 <= c -> fflag L c (fk_frame L c pos) = fk_flag L c pos.
Proof.
intros L c pos Hc. unfold fflag, fk_frame, fk_flag. f_equal.
pose proof (fk_fsize_pos c Hc). Local Ltac2 Set LiaHints.tbl := fun () => "0020=51534834723.661892458575.6000003004S1HS".
replace (fk_frames L c + pos * fk_fsize c - fk_frames L c) with (pos * fk_fsize c) by lia.
apply Z.div_mul. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fk_flag_range : forall L c pos, 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c ->
al_fake L + 4096 <= fk_flag L c pos < al_fake L + 36864.
Proof.
intros L c pos Hc Hp. unfold fk_flag, fk_flags, FK_NCLS, fk_nframes in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=27104211871.64102956105.7 00000400:S2HcS2Hp1H".
pose proof (fk_flags_off c ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fk_frame_range : forall L c pos, 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c ->
fk_frames L c <= fk_frame L c pos /\ fk_frame L c pos + fk_fsize c <= fk_frames L c + 1048576
/\ al_fake L + 36864 <= fk_frame L c pos /\ fk_frame L c pos + fk_fsize c <= al_fake L + FAKESZ.
Proof.
intros L c pos Hc Hp. unfold fk_frame, fk_frames, FK_NCLS, FAKESZ in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=27104211871.668390338709.7000004008S2HcS2Hc".
pose proof (fk_class_bytes c ltac:(lia)) as CB. pose proof (fk_fsize_pos c ltac:(lia)).
assert (pos * fk_fsize c + fk_fsize c <= 1048576) by nia. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fk_frames_disjoint : forall L c1 p1 c2 p2,
0 <= c1 < FK_NCLS -> 0 <= p1 < fk_nframes c1 -> 0 <= c2 < FK_NCLS -> 0 <= p2 < fk_nframes c2 ->
(c1, p1) <> (c2, p2) ->
fk_frame L c1 p1 + fk_fsize c1 <= fk_frame L c2 p2 \/ fk_frame L c2 p2 + fk_fsize c2 <= fk_frame L c1 p1.
Proof.
intros L c1 p1 c2 p2 H1 P1 H2 P2 NE.
pose proof (fk_frame_range L c1 p1 H1 P1) as (A1 & B1 & _). pose proof (fk_frame_range L c2 p2 H2 P2) as (A2 & B2 & _).
destruct (Z.eq_dec c1 c2) as [<-|NC].
- assert (p1 <> p2) by congruence. unfold fk_frame. Local Ltac2 Set LiaHints.tbl := fun () => "0010>49992785745.15000004S2H1".
pose proof (fk_fsize_pos c1 ltac:(lia)). nia.
- unfold fk_frames in *. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fk_flags_disjoint : forall L c1 p1 c2 p2,
0 <= c1 < FK_NCLS -> 0 <= p1 < fk_nframes c1 -> 0 <= c2 < FK_NCLS -> 0 <= p2 < fk_nframes c2 ->
(c1, p1) <> (c2, p2) -> fk_flag L c1 p1 <> fk_flag L c2 p2.
Proof.
intros L c1 p1 c2 p2 H1 P1 H2 P2 NE. unfold fk_flag, fk_flags, FK_NCLS, fk_nframes in *.
Local Ltac2 Set LiaHints.tbl := fun () => "00?0>14203552548.1814513537141.1814977203595.1914979285427.1129183414498.1231584091319.1831987891728.2241422330361.2241434880984.1444053020902.2147936057540.2149992785745.185264624343.18 54573399945.2354951254760.1800000400700A00G00K00Q00V00W00[00c00d00h00l011015S2H2S1HS2P12P22H0S2H11HS2H1S2NC1HS3HabSS2H2S3Hab2HbSS2H1S2H1S1E1HS2H2".
destruct (Z.eq_dec c1 c2) as [<-|NC]; [assert (p1 <> p2) by congruence; lia|].
pose proof (fk_flags_off c1 ltac:(lia)) as [X1 Y1]. pose proof (fk_flags_off c2 ltac:(lia)) as [X2 Y2].
assert (MONO : forall a b, 0 <= a -> a < b -> b <= 14 -> 32768 - 2 ^ (15 - a) + 2 ^ (14 - a) <= 32768 - 2 ^ (15 - b)).
{ intros a b Ha Hab Hb.
assert (E : 2 ^ (15 - a) = 2 * 2 ^ (14 - a)) by (replace (15 - a) with (Z.succ (14 - a)) by lia; rewrite Z.pow_succ_r by lia; reflexivity).
assert (2 ^ (15 - b) <= 2 ^ (14 - a)) by (apply Z.pow_le_mono_r; lia). lia. }
destruct (Z.lt_ge_cases c1 c2).
- pose proof (MONO c1 c2 ltac:(lia) ltac:(lia) ltac:(lia)). lia.
- pose proof (MONO c2 c1 ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition afake_geom (L : alayout) : Prop :=
al_fake L mod 4096 = 0 /\ ablk (al_fake L) (al_fake L + FAKESZ) /\ al_fake L + FAKESZ <= ATOP
/\ al_dtls L mod 4096 = 0 /\ (sclr (al_dtls L) 4096 /\ iclr (al_dtls L) 4096 /\ 4096 <= al_dtls L) /\ al_dtls L + 4096 <= ATOP
/\ (sclr (al_t L) 4096 /\ iclr (al_t L) 4096 /\ 4096 <= al_t L) /\ al_t L + 4096 <= ATOP
/\ (al_fake L + FAKESZ <= al_dtls L \/ al_dtls L + 4096 <= al_fake L)
/\ (al_t L + 4096 <= al_dtls L \/ al_dtls L + 4096 <= al_t L)
/\ (al_t L + 4096 <= al_fake L \/ al_fake L + FAKESZ <= al_t L).
Definition afake_cells (L : alayout) (m : amem) : Prop :=
rw_cells bsegs m 0x9b6b0 [C8 (Z_to_bv 64 0x93834)]
/\ rw_cells bsegs m 0x5d54c8 [C8 (Z_to_bv 64 0x5d54f0); C8 (Z_to_bv 64 (al_fake L))]
/\ rw_cells bsegs m 0x5d54d8 [C8 (Z_to_bv 64 (al_dtls L))]
/\ rw_cells bsegs m 0x5d54f8 [C8 (Z_to_bv 64 0x5d5cd0)]
/\ rw_cells bsegs m (al_dtls L + 24) [C8 (Z_to_bv 64 0x5d54d0)]
/\ rw_cells bsegs m 0x1340f1 [C1 (Z_to_bv 8 1)]
/\ rw_cells bsegs m 0x131fd8 [C4 (Z_to_bv 64 0)]
/\ dc_at m (al_t L + 48) 16.
End CANSEC1.
Notation FKB c F n := (mkABlock (ABFake c) F n).
Section CANSEC2. Context {rc : runConstT}.
Definition AFAKE (L : alayout) (LB : list ablock) (m : amem) : Prop :=
afake_geom L
/\ afake_cells L m
/\ (exists (h0 h1 h2 : word) (hs : list byte), rw_cells bsegs m (al_fake L) [C8 h0; C8 h1; C8 h2; CB 64 hs])
/\ rw_cells bsegs m (al_fake L + 88) [C8 (Z_to_bv 64 20)]
/\ rw_cells bsegs m (al_fake L + 96) [C1 (Z_to_bv 8 0)]
/\ dc_at m (al_fake L + 4096) (FAKESZ - 4096)
/\ dc_at m (shad (al_fake L)) (shlen FAKESZ)
/\ (forall c pos b, 0 <= c < FK_NCLS -> 0 <= pos < fk_nframes c ->
m (wa (fk_flag L c pos)) = Some b -> b <> Z_to_bv 8 0 ->
In (FKB c (fk_frame L c pos) (fk_fsize c)) LB)
/\ (forall c F n, In (FKB c F n) LB ->
0 <= c < FK_NCLS /\ n = fk_fsize c /\
exists pos, 0 <= pos < fk_nframes c /\ F = fk_frame L c pos /\ m (wa (fk_flag L c pos)) = Some (Z_to_bv 8 1)).
Definition afake_rng (L : alayout) (RNG : footprint) : Prop :=
rng RNG (al_fake L) FAKESZ /\ rng RNG (shad (al_fake L)) (shlen FAKESZ) /\ rng RNG (al_dtls L) 4096.
#[using="Type"] Lemma afake_rng_mono : forall L R R', fp_le R R' -> afake_rng L R -> afake_rng L R'.
Proof.
intros L R R' LE (A & B & C).
assert (M : forall lo n, rng R lo n -> rng R' lo n).
{ intros lo n (R1 & R2 & R3). split; [exact R1|]. split; [exact R2|]. intros b j Hb Hj. apply LE. apply R3; assumption. }
repeat split; try apply M; try assumption; destruct A, B, C; tauto.
Qed.
Definition afake_untouched (L : alayout) (W : list (Z * Z)) : Prop :=
Forall (fun iv => (snd iv <= al_fake L \/ al_fake L + 11571200 <= fst iv)
/\ (snd iv <= shad (al_fake L) \/ shad (al_fake L) + shlen 11571200 <= fst iv)
/\ (snd iv <= al_dtls L \/ al_dtls L + 4096 <= fst iv)
/\ (snd iv <= 0x9b6b0 \/ 0x9b6b0 + 8 <= fst iv)
/\ (snd iv <= 0x5d54c8 \/ 0x5d54c8 + 16 <= fst iv)
/\ (snd iv <= 0x5d54d8 \/ 0x5d54d8 + 8 <= fst iv)
/\ (snd iv <= 0x5d54f8 \/ 0x5d54f8 + 8 <= fst iv)
/\ (snd iv <= 0x1340f1 \/ 0x1340f1 + 1 <= fst iv)
/\ (snd iv <= 0x131fd8 \/ 0x131fd8 + 4 <= fst iv)) W.
#[using="Type"] Lemma disjoint_from_Forall : forall W A n,
Forall (fun iv : Z * Z => snd iv <= A \/ A + n <= fst iv) W -> disjoint_from W A n.
Proof. induction W as [|[lo hi] W IH]; intros A n H; cbn; [exact I|]. inversion H; subst. cbn in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>68595135843.10000004S2H2".
split; [lia| apply IH; assumption]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma munch_outside_range : forall W m m' A n a,
munch W m m' -> disjoint_from W A n -> A <= a < A + n -> 0 <= a < 2^64 -> m' (wa a) = m (wa a).
Proof.
intros W m m' A n a MU D Ha Hr. apply MU. Local Ltac2 Set LiaHints.tbl := fun () => "0010>56765669244.11000004S2Hr".
rewrite wa_unsigned by lia. eapply disjoint_outside; eauto.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma afake_frame : forall L LB m m' W,
AFAKE L LB m -> munch W m m' -> wmono bsegs m m' -> afake_untouched L W -> AFAKE L LB m'.
Proof.
intros L LB m m' W (G & CE & (h0 & h1 & h2 & hs & HS) & LOG & NGC & DC1 & DC2 & FL & LV) MU WM UT.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11). unfold FAKESZ in *.
pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in GL1. destruct G5 as (G5s & G5i & G5). destruct G7 as (G7s & G7i & G7). unfold iclr, sclr, AIMG_LO, AIMG_HI, KLS in G5s, G5i, G7s, G7i.
assert (DF : disjoint_from W (al_fake L) 11571200) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X1).
assert (DS : disjoint_from W (shad (al_fake L)) (shlen 11571200)) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X2).
assert (DD : disjoint_from W (al_dtls L) 4096) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X3).
assert (D1 : disjoint_from W 0x9b6b0 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X4).
assert (D2 : disjoint_from W 0x5d54c8 16) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X5).
assert (D3 : disjoint_from W 0x5d54d8 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X6).
assert (D4 : disjoint_from W 0x5d54f8 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X7).
assert (D5 : disjoint_from W 0x1340f1 1) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X8).
assert (D6 : disjoint_from W 0x131fd8 4) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X9).
split; [exact G|].
split.
{ destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). unfold afake_cells.
Local Ltac2 Set LiaHints.tbl := fun () => "00C0>10317641044.5115502292006.5816593502911.5122301225132.7224540717768.5924540717768.6224922218561.5829782367974.5133667104152.5133667104152.5836041970854.514255436838.51 45485620289.514835283270.2  50203890247.5150861283456.5950861283456.6263541249473.5168061171235.5100000100200700Z00h01601701801901:01;01<01=01B01C01F01I01J01KSSS3GL1S2G13G5s3G7s2G93G103G113GL11H2H02H9S3GL13GL31H2H0S3GL13GL31H2H0SSSSSSSS3G7iSS1HS1HSS".
repeat lazymatch goal with |- _ /\ _ => split end;
try (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [cells_size csize Nat.add]; first [assumption | eapply disjoint_from_sub; [exact DD| lia| lia| lia]]]).
eapply dc_at_any2; [exact C8| exact WM| clear -G7i; lia]. }
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
- intros c F n Hin. destruct (LV c F n Hin) as (Hc & Hn & pos & Hp & HF & Hb). split; [exact Hc|]. split; [exact Hn|].
exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp).
rewrite (munch_outside_range W m m' (al_fake L) 11571200) by (assumption || lia). exact Hb.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma afake_blocks : forall L LB LB' m,
AFAKE L LB m -> (forall c F n, In (FKB c F n) LB' <-> In (FKB c F n) LB) -> AFAKE L LB' m.
Proof.
intros L LB LB' m (G & CE & HS & LOG & NGC & DC1 & DC2 & FL & LV) EQ.
split; [exact G|]. split; [exact CE|]. split; [exact HS|]. split; [exact LOG|]. split; [exact NGC|].
split; [exact DC1|]. split; [exact DC2|]. split.
- intros c pos b Hc Hp Hb NZ. apply (proj2 (EQ _ _ _)). eapply FL; eauto.
- intros c F n Hin. apply LV. apply (proj1 (EQ _ _ _)). exact Hin.
Qed.
#[using="Type"] Lemma fk_frame_al64 : forall L c pos, al_fake L mod 4096 = 0 -> 0 <= c -> fk_frame L c pos mod 64 = 0.
Proof.
intros L c pos AL Hc. unfold fk_frame, fk_frames, fk_fsize.
Local Ltac2 Set LiaHints.tbl := fun () => "0060=18933043916.853726910787.753844677559.755830680952.863967162203.668390425458.600000100200300700800<SSSS2HkSS2Hc".
assert (E : 2 ^ (6 + c) = 64 * 2 ^ c) by (rewrite Z.pow_add_r by lia; reflexivity). rewrite E.
replace (al_fake L + 36864 + c * 1048576 + pos * (64 * 2 ^ c))
with (al_fake L + 64 * (576 + c * 16384 + pos * 2 ^ c)) by lia.
rewrite Z.add_mod by lia. rewrite Z.mul_comm, Z.mod_mul by lia.
replace (al_fake L mod 64) with 0; [reflexivity|].
symmetry. apply Z.mod_divide; [lia|]. apply Z.mod_divide in AL; [|lia].
destruct AL as [k Hk]. exists (k * 64). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma afake_lb : forall L LB m c F n, AFAKE L LB m -> In (FKB c F n) LB ->
0 <= c < FK_NCLS /\ n = fk_fsize c /\ 0 < n /\ F mod 64 = 0
/\ al_fake L + 36864 <= F /\ F + n <= al_fake L + FAKESZ
/\ ablk F (F + n) /\ F + n <= ATOP
/\ exists pos, 0 <= pos < fk_nframes c /\ F = fk_frame L c pos /\ fflag L c F = fk_flag L c pos
/\ al_fake L + 4096 <= fflag L c F < al_fake L + 36864.
Proof.
intros L LB m c F n (G & _ & _ & _ & _ & _ & _ & _ & LV) Hin.
destruct (LV c F n Hin) as (Hc & Hn & pos & Hp & HF & _). pose proof (fk_frame_range L c pos Hc Hp) as (R1 & R2 & R3 & R4).
destruct G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in GL1. Local Ltac2 Set LiaHints.tbl := fun () => "00C0>11488724947.2613039329029.2616935258815.2619327104600.2620208819858.26202128865.26  24462445340.2637996307473.2648428668841.2656904781362.2659687526920.2666584576170.2667435096312.2668384130463.2668390434852.2868390435239.2768390435618.267467565610.26 8208515630.26 00000100500600900=00D00L00P00W00[00_00c00g00k00o01301701;01<FS2HpSS1HS2R4S2H12H2S2R43GL3S2R3S2H12H2S2HpS2R3S2H1S2H0S2HcS2HcS2HcS2HcS2HcF".
pose proof (fk_fsize_pos c ltac:(lia)).
pose proof (fk_frame_al64 L c pos G1 ltac:(lia)). pose proof (fflag_frame L c pos ltac:(lia)).
pose proof (fk_flag_range L c pos Hc Hp). unfold FAKESZ in *. subst F n.
repeat lazymatch goal with |- _ /\ _ => split end; try lia.
{ eapply ablk_sub; [exact G2 | lia | lia]. }
exists pos. repeat split; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma afake_lb_disjoint : forall L LB m c1 F1 n1 c2 F2 n2,
AFAKE L LB m -> In (FKB c1 F1 n1) LB -> In (FKB c2 F2 n2) LB -> FKB c1 F1 n1 <> FKB c2 F2 n2 ->
F1 + n1 <= F2 \/ F2 + n2 <= F1.
Proof.
intros L LB m c1 F1 n1 c2 F2 n2 AF H1 H2 NE.
destruct AF as (G & _ & _ & _ & _ & _ & _ & _ & LV).
destruct (LV _ _ _ H1) as (C1 & N1 & p1 & P1 & E1 & _). destruct (LV _ _ _ H2) as (C2 & N2 & p2 & P2 & E2 & _). subst.
apply fk_frames_disjoint; try assumption. intros E. injection E as <- <-. apply NE. reflexivity.
Qed.
#[using="Type"] Lemma afake_flag : forall L LB m c F n, AFAKE L LB m -> In (FKB c F n) LB ->
rw_cells bsegs m (fflag L c F) [C1 (Z_to_bv 8 1)].
Proof.
intros L LB m c F n AF Hin. pose proof (afake_lb L LB m c F n AF Hin) as (Hc & _ & _ & _ & _ & _ & _ & _ & pos & Hp & HF & EF & FR).
destruct AF as (G & _ & _ & _ & _ & DC1 & _ & _ & LV). destruct (LV _ _ _ Hin) as (_ & _ & pos' & Hp' & HF' & B1).
assert (pos' = pos) as ->.
{ subst F. unfold fk_frame in HF'. Local Ltac2 Set LiaHints.tbl := fun () => "0090>14643180512.2741808037741.2855688371807.3556188854029.2757230164919.2861544318748.2764350945276.286758013062.28 68390336548.1900000700800900@00A00B00I00J00NS2EF2FRSSS2EF2FRSSS2EF2FRSS2Hc".
pose proof (fk_fsize_pos c ltac:(lia)). nia. }
rewrite EF. destruct G as (G1 & G2 & G3 & _). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in GL1. unfold FAKESZ in *.
destruct (dc_split m (al_fake L + 4096) (fk_flag L c pos - (al_fake L + 4096)) (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096))) ltac:(replace (fk_flag L c pos - (al_fake L + 4096) + (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096)))) with (FAKESZ - 4096) by (unfold FAKESZ; lia); exact DC1) ltac:(lia) ltac:(lia)) as [_ D2].
replace (al_fake L + 4096 + (fk_flag L c pos - (al_fake L + 4096))) with (fk_flag L c pos) in D2 by lia.
destruct (dc_split m (fk_flag L c pos) 1 (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096)) - 1) ltac:(replace (1 + (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096)) - 1)) with (11571200 - 4096 - (fk_flag L c pos - (al_fake L + 4096))) by lia; exact D2) ltac:(lia) ltac:(lia)) as [D3 _].
destruct (c1_of_dc m _ D3) as [b Hb].
assert (b = Z_to_bv 8 1) as ->.
{ destruct Hb as [[WF [B0 [B1' BR]]] WR]. specialize (BR 0%nat ltac:(cbn; lia)). cbn in BR. rewrite Z.add_0_r in BR.
unfold mrd in BR. rewrite B1 in BR. congruence. }
exact Hb.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma afake_release : forall L LB m c F n,
AFAKE L (FKB c F n :: LB) m -> ~ In (FKB c F n) LB ->
AFAKE L LB (write_to_mem m (wa (fflag L c F)) [Z_to_bv 8 0]).
Proof.
intros L LB m c F n AF NI.
pose proof (afake_lb L _ m c F n AF ltac:(left; reflexivity)) as (Hc & Hn & Npos & _ & _ & _ & _ & _ & pos & Hp & HF & EF & FR).
pose proof (afake_flag L _ m c F n AF ltac:(left; reflexivity)) as FB. rewrite EF in FB |- *.
destruct AF as (G & CE & HS & LOG & NGC & DC1 & DC2 & FL & LV). destruct G as (G1 & G2 & G3 & Grest). pose proof (ablk_lin _ _ G2) as (GL1 & GL2 & GL3 & GL4). unfold AIMG_HI in GL1.
pose proof Grest as (_ & _ & _ & (_ & G7i & _) & _). unfold iclr, AIMG_LO, AIMG_HI in G7i. unfold FAKESZ in *.
set (m' := write_to_mem m (wa (fk_flag L c pos)) [Z_to_bv 8 0]).
assert (MU : munch [(fk_flag L c pos, fk_flag L c pos + 1)] m m').
{ subst m'. Local Ltac2 Set LiaHints.tbl := fun () => "00K0>10954002273.4711375426136.4911375426136.5211807744665.3511807744665.4011807744665.4411807744665.4716593502911.4022301225132.612250247890.49 2250247890.52 22700267513.4124542813936.3829455975410.3529455975410.3829782367974.4035310323626.3835579638113.474835283270.2  51471913697.4751579647101.3551579647101.3852245863521.4756759370246.4162577003217.4765800861025.4768390435239.4700000;00I00W00X00_00f01;01@01P01b02402<02M02X02c02d02e03003503@03M03Z03e03i04404?04CS2EF2FR3GL1S3GL13GL31H2H0S3GL13GL31H2H0SS2EF2FRS2EF2FRS5Grest2EF2FR3GL13GL2S3GL1S2G13GL11H2H02H9S5Grest3GL13GL22NES5Grest3GL13GL22NES3GL22NES2EF2FR3GL13GL31HS2EF2FR3GL1S2EF2FR3GL1SSS2EF2FR3GL1S3G7iS2EF2FR3GL1S2EF2FR3GL31HS2EF2FR3GL31HS2EF2FR3GL1S2HaS2EF2FR3GL1S2EF2FR3GL1S2Hc".
apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia]. }
assert (WM : wmono bsegs m m') by (subst m'; apply wmono_write, wmono_refl).
assert (OUT : forall a, 0 <= a < 2^64 -> a <> fk_flag L c pos -> m' (wa a) = m (wa a)).
{ intros a Ha NE. apply MU. rewrite wa_unsigned by lia. cbn. lia. }
assert (AT : m' (wa (fk_flag L c pos)) = Some (Z_to_bv 8 0)).
{ subst m'. rewrite write_to_mem_spec by (cbn; lia). rewrite wa_unsigned by lia.
replace (fk_flag L c pos <=? fk_flag L c pos) with true by (symmetry; apply Z.leb_refl).
cbn [length andb]. rewrite Z.sub_diag.
replace (fk_flag L c pos <? fk_flag L c pos + Z.of_nat 1) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
split; [exact (conj G1 (conj G2 (conj G3 Grest)))|].
split.
{ destruct CE as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8). unfold afake_cells.
repeat lazymatch goal with |- _ /\ _ => split end;
try (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; lia]).
eapply dc_at_any2; [exact X8| exact WM| clear -G7i; lia]. }
split.
{ destruct HS as (h0 & h1 & h2 & hs & HS). exists h0, h1, h2, hs. eapply rw_cells_transport; [exact HS| exact MU| exact WM| cbn; lia]. }
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
assert (pos' = pos) by nia. subst pos'. reflexivity.
- intros c' F' n' Hin. destruct (LV c' F' n' ltac:(right; exact Hin)) as (Hc' & Hn' & pos' & Hp' & HF' & B1).
split; [exact Hc'|]. split; [exact Hn'|]. exists pos'. split; [exact Hp'|]. split; [exact HF'|].
destruct (Z.eq_dec (fk_flag L c' pos') (fk_flag L c pos)) as [EQ|NE].
+ exfalso. apply NI.
destruct (Z.eq_dec c' c) as [EC|NC]; [| exfalso; refine (fk_flags_disjoint L c' pos' c pos Hc' Hp' Hc Hp _ EQ); congruence].
destruct (Z.eq_dec pos' pos) as [EP|NP]; [| exfalso; refine (fk_flags_disjoint L c' pos' c pos Hc' Hp' Hc Hp _ EQ); congruence].
subst c' pos'. rewrite HF, Hn. rewrite <- HF', <- Hn'. exact Hin.
+ pose proof (fk_flag_range L c' pos' Hc' Hp'). rewrite OUT by lia. exact B1.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC2.
