(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1br.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1nt X1rh X1re X1qu X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.

Definition SBSTATE_SIZEOF : Z := 160.

Record sb_junk := SBJ {
sj_last_ener : word; sj_seed : word; sj_pad1 : list byte; sj_pad2 : list byte;
sj_g0 : list word; sj_g1 : list word; sj_exc : list word; sj_oq : list word; sj_iq : list word;
sj_msp : list word; sj_pg : list word; sj_er : list word }.

Record sb_addrs := SBA {
a_low : Z; a_g0 : Z; a_g1 : Z; a_exc : Z; a_oq : Z; a_iq : Z; a_msp : Z; a_pg : Z; a_er : Z }.

Section Rep.
Context {RCEIL : RunCeiling}.
Variable segs : list Segment.

Variables (NB_MODE_PTR
NB_SUBMODES_PTR
USER_HANDLER
STEREO_HANDLER
WB_MODE_PTR
UWB_MODE_PTR
WB_SUBMODES_PTR
UWB_SUBMODES_PTR     : Z).
Implicit Types s : sbd_state bptr.

Local Notation NBREP := (nbstate_rep segs NB_MODE_PTR NB_SUBMODES_PTR USER_HANDLER STEREO_HANDLER).

Definition sb_mode_ptr (mo : spx_mode) : Z :=
match mo with ModeNB => NB_MODE_PTR | ModeWB => WB_MODE_PTR | ModeUWB => UWB_MODE_PTR end.
Definition sb_submodes_ptr (mo : spx_mode) : Z :=
match mo with ModeUWB => UWB_SUBMODES_PTR | _ => WB_SUBMODES_PTR end.
Definition sb_isave_ptr (OUT : Z) s : Z :=
match sbd_innov_save s with None => 0 | Some k => OUT + 4 * k end.

Definition sb_cells s (a : sb_addrs) (OUT : Z) (j : sb_junk) : list cell :=
[C8 (Z_to_bv 64 (sb_mode_ptr (sbd_mode s)));
C8 (Z_to_bv 64 (a_low a));
C4 (Z_to_bv 64 (sbd_full_frame_size s)); C4 (Z_to_bv 64 (sbd_frame_size s));
C4 (Z_to_bv 64 (sbd_subframeSize s)); C4 (Z_to_bv 64 (sbd_nbSubframes s));
C4 (Z_to_bv 64 (sbd_lpcSize s)); C4 (Z_to_bv 64 (sbd_first s));
C4 (Z_to_bv 64 (sbd_sampling_rate s)); C4 (Z_to_bv 64 (sbd_lpc_enh_enabled s));
C8 (Z_to_bv 64 0);
C8 (Z_to_bv 64 (a_g0 a)); C8 (Z_to_bv 64 (a_g1 a)); C8 (Z_to_bv 64 (a_exc a));
C8 (Z_to_bv 64 (a_oq a)); C8 (Z_to_bv 64 (a_iq a)); C8 (Z_to_bv 64 (a_msp a));
C8 (Z_to_bv 64 (a_pg a)); C8 (Z_to_bv 64 (a_er a));
C8 (Z_to_bv 64 (sb_isave_ptr OUT s));
C4 (sj_last_ener j); C4 (sj_seed j);
C4 (Z_to_bv 64 (sbd_encode_submode s)); CB 4 (sj_pad1 j);
C8 (Z_to_bv 64 (sb_submodes_ptr (sbd_mode s)));
C4 (Z_to_bv 64 (sbd_submodeID s)); CB 4 (sj_pad2 j)].

Definition sb_junk_ok s (j : sb_junk) : Prop :=
length (sj_pad1 j) = 4%nat /\ length (sj_pad2 j) = 4%nat /\
length (sj_g0 j) = 64%nat /\ length (sj_g1 j) = 64%nat /\
Z.of_nat (length (sj_exc j)) = sbd_subframeSize s /\
length (sj_oq j) = 8%nat /\ length (sj_iq j) = 8%nat /\ length (sj_msp j) = 16%nat /\
length (sj_pg j) = 4%nat /\ length (sj_er j) = 4%nat.

Definition sb_inv s : Prop :=
(sbd_mode s = ModeWB \/ sbd_mode s = ModeUWB) /\
sbd_frame_size s = sbm_frameSize (sbd_mode s) /\ sbd_full_frame_size s = 2 * sbd_frame_size s /\
sbd_subframeSize s = sbm_subframeSize (sbd_mode s) /\ sbd_nbSubframes s = 4 /\ sbd_lpcSize s = 8 /\
(sbd_first s = 0 \/ sbd_first s = 1) /\
- 2^31 <= sbd_sampling_rate s < 2^31 /\ - 2^31 <= sbd_lpc_enh_enabled s < 2^31 /\
sbd_encode_submode s = 1 /\ 0 <= sbd_submodeID s <= 7 /\
match sbd_innov_save s with None => True | Some k => 0 <= k end.

Definition sb_blocks s (S : Z) (a : sb_addrs) : list block :=
[(sbd_blk s, S, SBSTATE_SIZEOF);
(sbd_g0_mem s, a_g0 a, 256); (sbd_g1_mem s, a_g1 a, 256); (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s);
(sbd_old_qlsp s, a_oq a, 32); (sbd_interp_qlpc s, a_iq a, 32);
(sbd_pi_gain s, a_pg a, 16); (sbd_exc_rms s, a_er a, 16); (sbd_mem_sp s, a_msp a, 64)].

Definition sb_bufs (m : mem) (a : sb_addrs) (j : sb_junk) : Prop :=
rw_cells segs m (a_g0 a) (f32 (sj_g0 j)) /\ rw_cells segs m (a_g1 a) (f32 (sj_g1 j)) /\
rw_cells segs m (a_exc a) (f32 (sj_exc j)) /\ rw_cells segs m (a_oq a) (f32 (sj_oq j)) /\
rw_cells segs m (a_iq a) (f32 (sj_iq j)) /\ rw_cells segs m (a_msp a) (f32 (sj_msp j)) /\
rw_cells segs m (a_pg a) (f32 (sj_pg j)) /\ rw_cells segs m (a_er a) (f32 (sj_er j)).

Fixpoint decst_rep (OUT STEREO : Z) (m : mem) (S : Z) (d : dec_state bptr) (LBD : list block) {struct d} : Prop :=
match d with
| DecNB st => LBD = [(nb_blk st, S, NBSTATE_SIZEOF)] /\ NBREP m S OUT STEREO st
| DecSB s low => exists (a : sb_addrs) (j : sb_junk) (LBL : list block),
LBD = sb_blocks s S a ++ LBL /\ S mod 8 = 0 /\ 0 < S /\ sb_inv s /\ sb_junk_ok s j /\
rw_cells segs m S (sb_cells s a OUT j) /\ sb_bufs m a j /\
exists OUTL, decst_rep OUTL STEREO m (a_low a) low LBL
end.

Definition top_isave_none (d : dec_state bptr) : Prop :=
match d with DecNB st => nb_innov_save st = None | DecSB s _ => sbd_innov_save s = None end.

Definition dec_exc_ready (m : mem) (S : Z) (d : dec_state bptr) : Prop :=
match d with
| DecNB _ => rw_cells segs m (S + 2032) [C8 (Z_to_bv 64 (S + NB_EXC_OFF))]
| DecSB _ _ => True
end.

Definition lbd_apart (LBD : list block) : Prop :=
forall b1 b2, In b1 LBD -> In b2 LBD -> blk_id b1 <> blk_id b2 ->
blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.

Fixpoint dec_nestedR (d : dec_state bptr) : Prop :=
match d with
| DecNB _ => True
| DecSB s low => dec_mode low = sbm_nb_mode (sbd_mode s) /\ dec_nestedR low
end.

Definition dec_rep (STEREO : Z) (m : mem) (S : Z) (d : dec_state bptr) (LBD : list block) : Prop :=
top_isave_none d /\ (dec_depth d <= 3)%nat /\ List.NoDup (map blk_id LBD) /\ lbd_apart LBD /\ dec_nestedR d /\
exists OUT, decst_rep OUT STEREO m S d LBD.

#[using="Type"] Lemma sb_cells_size : forall s a OUT j, cells_size (sb_cells s a OUT j) = 160%nat.
Proof. intros. reflexivity. Qed.

Definition agree_at (m m' : mem) (A n : Z) : Prop :=
forall a, A <= a < A + n ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

#[using="Type"] Lemma rw_cells_agree_at : forall m m' A cs,
rw_cells segs m A cs -> agree_at m m' A (Z.of_nat (cells_size cs)) -> rw_cells segs m' A cs.
Proof.
intros m m' A cs [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
- destruct HB as (H0 & H1 & HB). pose proof (cells_bytes_length cs Hwf) as L.
split; [exact H0|]. split; [exact H1|]. intros i Hi. rewrite <- (HB i Hi). unfold mrd.
destruct (AG (A + Z.of_nat i) ltac:(lia)) as [E _]. rewrite E. reflexivity.
- destruct HW as (H0 & H1 & HW). split; [exact H0|]. split; [exact H1|].
intros i Hi. destruct (AG (A + i) ltac:(lia)) as [_ W]. apply W. apply HW. exact Hi.
Qed.

Definition agree_blocks (m m' : mem) (LBD : list block) : Prop :=
forall a, 0 <= a < 2^64 -> in_block LBD a ->
m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

#[using="Type"] Lemma agree_blocks_at : forall m m' LBD b A cs,
agree_blocks m m' LBD -> In b LBD -> rw_cells segs m A cs ->
blk_addr b <= A -> A + Z.of_nat (cells_size cs) <= blk_addr b + blk_size b ->
agree_at m m' A (Z.of_nat (cells_size cs)).
Proof.
intros m m' LBD b A cs AG Hb X LO HI a Ha. pose proof (rw_cells_bound _ _ _ _ X) as B.
apply AG; [lia|]. exists b. split; [exact Hb| unfold in_block; lia].
Qed.

#[using="Type"] Lemma agree_blocks_sub : forall m m' L L', agree_blocks m m' L -> (forall b, In b L' -> In b L) -> agree_blocks m m' L'.
Proof. intros m m' L L' AG SUB a Ha (b & Hb & Hab). apply AG; [exact Ha|]. exists b. split; [apply SUB; exact Hb| exact Hab]. Qed.

#[using="Type"] Lemma nbstate_rep_agree : forall m m' ST OUT STEREO (st : nb_state bptr),
NBREP m ST OUT STEREO st -> agree_at m m' ST NBSTATE_SIZEOF -> NBREP m' ST OUT STEREO st.
Proof.
intros m m' ST OUT STEREO st sfH_; first [ sf_destruct 7%nat sfH_ as AL POS INV j JOK CBS X | sf_fb; destruct sfH_ as (AL & POS & INV & j & JOK & CBS & X) ]; intros AG.
split; [exact AL|]. split; [exact POS|]. split; [exact INV|]. exists j. split; [exact JOK|]. split; [exact CBS|].
eapply rw_cells_agree_at; [exact X|]. rewrite (nb_cells_size _ _ _ _ _ _ _ _ JOK). exact AG.
Qed.

#[using="Type"] Lemma decst_rep_agree : forall d OUT STEREO m m' S LBD,
decst_rep OUT STEREO m S d LBD -> agree_blocks m m' LBD -> decst_rep OUT STEREO m' S d LBD.
Proof.
induction d as [st|s low IH]; intros OUT STEREO m m' S LBD R AG.
- destruct R as [-> NB]. split; [reflexivity|]. eapply nbstate_rep_agree; [exact NB|].
first [ sf_destruct 7%nat NB as _ _ _ j JOK _ X | sf_fb; destruct NB as (_ & _ & _ & j & JOK & _ & X) ].
pose proof (agree_blocks_at m m' _ (nb_blk st, S, NBSTATE_SIZEOF) _ _ AG ltac:(left; reflexivity) X ltac:(cbn; lia)) as AA.
rewrite (nb_cells_size _ _ _ S OUT STEREO st j JOK) in AA. apply AA. cbn [blk_addr blk_size fst snd]. unfold NBSTATE_SIZEOF. lia.
- first [ sf_destruct 12%nat R as a j LBL -> AL POS INV JOK X BU OUTL RL | sf_fb; destruct R as (a & j & LBL & -> & AL & POS & INV & JOK & X & BU & OUTL & RL) ].
first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ]. split; [reflexivity|]. split; [exact AL|]. split; [exact POS|]. split; [exact INV|]. split; [exact JOK|].
assert (HB : forall b, In b (sb_blocks s S a) -> In b (sb_blocks s S a ++ LBL)) by (intros b Hb; apply in_app_iff; left; exact Hb).
pose proof JOK as sfP_; first [ sf_destruct 10%nat sfP_ as E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 | sf_fb; destruct sfP_ as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10) ].
split; [|split].
+ eapply rw_cells_agree_at; [exact X|].
eapply (agree_blocks_at m m' _ (sbd_blk s, S, SBSTATE_SIZEOF)); [exact AG| apply HB; left; reflexivity| exact X| cbn; lia|].
cbn [blk_addr blk_size fst snd]. rewrite (sb_cells_size s a OUT j). unfold SBSTATE_SIZEOF. lia.
+ first [ sf_destruct 8%nat BU as B0 B1 B2 B3 B4 B5 B6 B7 | sf_fb; destruct BU as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7) ].
unfold sb_bufs.
repeat match goal with |- _ /\ _ => split end;
(eapply rw_cells_agree_at; [eassumption|]);
[ eapply (agree_blocks_at m m' _ (sbd_g0_mem s, a_g0 a, 256))
| eapply (agree_blocks_at m m' _ (sbd_g1_mem s, a_g1 a, 256))
| eapply (agree_blocks_at m m' _ (sbd_excBuf s, a_exc a, 4 * sbd_subframeSize s))
| eapply (agree_blocks_at m m' _ (sbd_old_qlsp s, a_oq a, 32))
| eapply (agree_blocks_at m m' _ (sbd_interp_qlpc s, a_iq a, 32))
| eapply (agree_blocks_at m m' _ (sbd_mem_sp s, a_msp a, 64))
| eapply (agree_blocks_at m m' _ (sbd_pi_gain s, a_pg a, 16))
| eapply (agree_blocks_at m m' _ (sbd_exc_rms s, a_er a, 16)) ];
(first [exact AG | apply HB; cbn; tauto | eassumption | cbn [blk_addr blk_size fst snd]; rewrite ?cells_size_f32; lia]).
+ exists OUTL. eapply IH; [exact RL|]. eapply agree_blocks_sub; [exact AG|]. intros b Hb. apply in_app_iff. right. exact Hb.
Qed.

#[using="Type"] Lemma decst_rep_reout : forall d OUT1 OUT2 STEREO m S LBD,
top_isave_none d -> decst_rep OUT1 STEREO m S d LBD -> decst_rep OUT2 STEREO m S d LBD.
Proof.
intros d OUT1 OUT2 STEREO m S LBD TOP R. destruct d as [st|s low]; cbn in TOP; cbn [decst_rep] in R |- *.
- destruct R as [EL (AL & POS & INV & j & JOK & CBS & X)]. split; [exact EL|]. split; [exact AL|]. split; [exact POS|]. split; [exact INV|].
exists j. split; [exact JOK|]. split; [exact CBS|]. unfold nb_cells, nb_isave_ptr in X |- *. rewrite TOP in X |- *. exact X.
- first [ sf_destruct 11%nat R as a j LBL EL AL POS INV JOK X BU RL | sf_fb; destruct R as (a & j & LBL & EL & AL & POS & INV & JOK & X & BU & RL) ]. first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j) | exact (LBL) | ] | sf_fb; exists a, j, LBL ].
repeat (split; [assumption|]). split; [| split; [exact BU| exact RL]]. unfold sb_cells, sb_isave_ptr in X |- *. rewrite TOP in X |- *. exact X.
Qed.

#[using="Type"] Lemma dec_exc_ready_agree : forall d OUT STEREO m m' S LBD,
decst_rep OUT STEREO m S d LBD -> dec_exc_ready m S d -> agree_blocks m m' LBD -> dec_exc_ready m' S d.
Proof.
destruct d as [st|s low]; intros OUT STEREO m m' S LBD R EX AG; [|exact I]. cbn in EX |- *.
destruct R as [-> NB]. eapply rw_cells_agree_at; [exact EX|].
eapply (agree_blocks_at m m' _ (nb_blk st, S, NBSTATE_SIZEOF)); [exact AG| left; reflexivity| exact EX| cbn; lia|].
cbn [blk_addr blk_size fst snd cells_size csize Nat.add]. unfold NBSTATE_SIZEOF. lia.
Qed.

#[using="Type"] Lemma dec_rep_frame : forall STEREO m m' S d LBD,
dec_rep STEREO m S d LBD -> agree_blocks m m' LBD -> dec_rep STEREO m' S d LBD.
Proof.
intros STEREO m m' S d LBD sfH_; first [ sf_destruct 7%nat sfH_ as TOP DE ND AP NE OUT R | sf_fb; destruct sfH_ as (TOP & DE & ND & AP & NE & OUT & R) ]; intros AG. split; [exact TOP|]. split; [exact DE|]. split; [exact ND|]. split; [exact AP|]. split; [exact NE|].
exists OUT. eapply decst_rep_agree; eauto.
Qed.

#[using="Type"] Lemma ctl_mode_sameR : forall (d : dec_state bptr) r, dec_mode (snd (speex_decoder_ctl d r)) = dec_mode d.
Proof.
induction d as [st|sb low IH]; intros r; [destruct r; reflexivity|].
destruct r; cbn [speex_decoder_ctl]; try reflexivity.
all: match goal with |- context [speex_decoder_ctl ?lw ?q] => destruct (speex_decoder_ctl lw q) as [vv ll]; reflexivity end.
Qed.
#[using="Type"] Lemma ctl_nested_same : forall (d : dec_state bptr) r, dec_nestedR d -> dec_nestedR (snd (speex_decoder_ctl d r)).
Proof.
induction d as [st|sb low IH]; intros r NE; [destruct r; exact I|].
cbn in NE. destruct NE as [DM NL].
destruct r; cbn [speex_decoder_ctl]; try (split; assumption).
all: match goal with |- context [speex_decoder_ctl ?lw ?q] =>
pose proof (IH q NL) as IH2; pose proof (ctl_mode_sameR lw q) as EM;
destruct (speex_decoder_ctl lw q) as [vv ll]; cbn [snd fst dec_nestedR] in IH2, EM |- *; rewrite ?EM; split; assumption end.
Qed.

#[using="Type"] Lemma agree_blocks_of_munch : forall W m m' LBD,
munch W m m' -> wmono segs m m' -> (forall b a, In b LBD -> blk_addr b <= a < blk_addr b + blk_size b -> outside W a) ->
agree_blocks m m' LBD.
Proof.
intros W m m' LBD MU WM OUT a Ha (b & Hb & Hab). split.
- apply MU. rewrite wa_unsigned by lia. exact (OUT b a Hb Hab).
- apply WM.
Qed.

#[using="Type"] Lemma decst_rep_pos : forall d OUT STEREO m S LBD, decst_rep OUT STEREO m S d LBD -> 0 < S /\ S mod 8 = 0.
Proof.
destruct d as [st|s low]; intros OUT STEREO m S LBD R.
- destruct R as [_ (AL & POS & _)]. split; [exact POS| exact AL].
- first [ sf_destruct 7%nat R as a j LBL _ AL POS _ | sf_fb; destruct R as (a & j & LBL & _ & AL & POS & _) ]. split; [exact POS| exact AL].
Qed.

#[using="Type"] Lemma decst_rep_head : forall d OUT STEREO m S LBD, decst_rep OUT STEREO m S d LBD ->
exists rest, LBD = (match d with DecNB st => nb_blk st | DecSB s _ => sbd_blk s end, S,
match d with DecNB _ => NBSTATE_SIZEOF | DecSB _ _ => SBSTATE_SIZEOF end) :: rest.
Proof.
destruct d as [st|s low]; intros OUT STEREO m S LBD R.
- destruct R as [-> _]. exists []. reflexivity.
- first [ sf_destruct 5%nat R as a j LBL -> _ | sf_fb; destruct R as (a & j & LBL & -> & _) ]. eexists. reflexivity.
Qed.
End Rep.

Lemma dr_bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
split. { apply Z.lor_nonneg. lia. }
pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
rewrite Z.shiftl_mul_pow2 in * by lia.
replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
nia.
Qed.

Lemma dr_Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
pose proof (dr_bytes_le_to_Z_range bs) as HR.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
destruct (Z.ltb_spec0 i 8).
- rewrite Z.shiftl_spec_low by lia. reflexivity.
- rewrite Z.ones_spec_high by lia. apply andb_false_r. }
rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
- rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
rewrite Z.lor_0_l. exact IH.
Qed.

Lemma dr_le4_of_bytes : forall bs : list byte, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
intros bs HL. unfold le4, le_bytes_to_word.
pose proof (dr_bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z in HR.
rewrite unsigned_lit by lia. rewrite <- HL. apply dr_Z_to_le_bytes_to_Z.
Qed.

Lemma rw_cells_C4_of_CB4 : forall segs m P (bs : list byte),
rw_cells segs m P [CB 4 bs] -> rw_cells segs m P [C4 (le_bytes_to_word bs)].
Proof.
intros segs m P bs X. pose proof X as [[[L _] _] _]. cbn in L.
eapply rw_cells_samebytes; [exact X| cbn; tauto| cbn [cells_bytes cbytes app]; rewrite dr_le4_of_bytes by exact L; reflexivity| reflexivity].
Qed.

Definition cb_bytes (func data : Z) (j : list byte * list byte) : list byte :=
fst j ++ le8 (Z_to_bv 64 func) ++ le8 (Z_to_bv 64 data) ++ snd j.

Lemma cb_cells_bytes : forall f d j, cells_bytes (cb_cells f d j) = cb_bytes f d j.
Proof. intros f d [a b]. cbn [cb_cells cells_bytes cbytes cb_bytes fst snd]. rewrite !app_nil_r. reflexivity. Qed.

Lemma cb_bytes_length : forall f d j, length (fst j) = 8%nat -> length (snd j) = 16%nat -> length (cb_bytes f d j) = 40%nat.
Proof. intros f d [a b] La Lb. unfold cb_bytes. cbn [fst snd] in *. rewrite !length_app, !length_le8, La, Lb. reflexivity. Qed.

Fixpoint cbs_bytes (k : nat) (sf sd : Z) (b : bool) (js : list (list byte * list byte)) : list byte :=
match k, js with
| S k', j :: js' => (if (16 - Z.of_nat k =? 9) && b then cb_bytes sf sd j else cb_bytes 0 0 j) ++ cbs_bytes k' sf sd b js'
| _, _ => []
end.

Lemma cbs_cells_bytes : forall k sf sd b js, cells_bytes (cbs_cells k sf sd b js) = cbs_bytes k sf sd b js.
Proof.
induction k as [|k IH]; intros sf sd b [|j js]; try reflexivity.
cbn [cbs_cells cbs_bytes]. cbv zeta. rewrite cells_bytes_app, IH. destruct (_ && _); rewrite cb_cells_bytes; reflexivity.
Qed.

Lemma cbs_bytes_length : forall k sf sd b js, (k <= length js)%nat -> Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) js ->
length (cbs_bytes k sf sd b js) = (40 * k)%nat.
Proof.
induction k as [|k IH]; intros sf sd b [|j js] Hk HF; try reflexivity; [cbn in Hk; lia|].
inversion HF; subst. cbn [cbs_bytes]. cbv zeta. cbn [length] in Hk. rewrite length_app, (IH sf sd b js) by first [lia| assumption].
match goal with H : length (fst j) = 8%nat /\ _ |- _ => destruct H as [L1 L2] end. destruct (_ && _); rewrite cb_bytes_length by assumption; lia.
Qed.

Lemma cbs_bytes_indep : forall k sf sd sd' b b' js, (Z.of_nat k <= 6)%Z -> cbs_bytes k sf sd b js = cbs_bytes k sf sd' b' js.
Proof.
induction k as [|k IH]; intros sf sd sd' b b' [|j js] Hk; try reflexivity.
cbn [cbs_bytes]. replace (16 - Z.of_nat (S k) =? 9) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
rewrite (IH sf sd sd' b b' js) by lia. reflexivity.
Qed.

Lemma firstn_app_len {A} (l1 l2 : list A) n k : length l1 = n -> firstn (n + k) (l1 ++ l2) = l1 ++ firstn k l2.
Proof. intros L. rewrite firstn_app, L, firstn_all2 by lia. f_equal. f_equal. lia. Qed.
Lemma firstn_len_exact {A} (l1 l2 : list A) n : length l1 = n -> firstn n (l1 ++ l2) = l1.
Proof. intros L. rewrite firstn_app, L, firstn_all2, Nat.sub_diag by lia. cbn. apply app_nil_r. Qed.
Lemma skipn_app_len {A} (l1 l2 : list A) n k : length l1 = n -> skipn (n + k) (l1 ++ l2) = skipn k l2.
Proof. intros L. rewrite skipn_app, L, skipn_all2 by lia. cbn. f_equal. lia. Qed.
Lemma skipn_len_exact {A} (l1 l2 : list A) n : length l1 = n -> skipn n (l1 ++ l2) = l2.
Proof. intros L. rewrite skipn_app, L, skipn_all2, Nat.sub_diag by lia. reflexivity. Qed.

Definition pre_bytes (pre : list (list byte * list byte)) : list byte := concat (map (cb_bytes 0 0) pre).

Lemma pre_bytes_length : forall pre, Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) pre ->
length (pre_bytes pre) = (40 * length pre)%nat.
Proof.
induction pre as [|x pre IH]; intros HF; [reflexivity|]. inversion HF; subst. unfold pre_bytes. cbn [map concat].
rewrite length_app. unfold pre_bytes in IH. rewrite IH by assumption. destruct H1 as [L1 L2]. rewrite cb_bytes_length by assumption. cbn [length]. lia.
Qed.

Lemma cbs_bytes_split : forall pre x9 post sf sd b, (length pre <= 9)%nat ->
cbs_bytes (7 + length pre) sf sd b (pre ++ x9 :: post) =
pre_bytes pre ++ (if b then cb_bytes sf sd x9 else cb_bytes 0 0 x9) ++ cbs_bytes 6 sf sd b post.
Proof.
induction pre as [|y pre IH]; intros x9 post sf sd b Hl.
- cbn [length Nat.add app pre_bytes map concat]. cbn [cbs_bytes]. replace (16 - Z.of_nat 7 =? 9) with true by reflexivity. cbn [andb]. reflexivity.
- cbn [length] in Hl |- *. replace (7 + S (length pre))%nat with (S (7 + length pre)) by lia.
cbn [cbs_bytes app]. replace (16 - Z.of_nat (S (7 + length pre)) =? 9) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
rewrite IH by lia. unfold pre_bytes. cbn [map concat]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma cbs_install : forall sf sd0 sd b js,
length js = 16%nat -> Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) js ->
let cbs := cbs_bytes 16 sf sd0 b js in
exists js', length js' = 16%nat /\ Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) js' /\
cbs_bytes 16 sf sd true js' =
firstn 360 cbs ++ le4 (Z_to_bv 64 9) ++ firstn 4 (skipn 364 cbs) ++ le8 (Z_to_bv 64 sf) ++ le8 (Z_to_bv 64 sd) ++ skipn 8 (skipn 12 (skipn 364 cbs)).
Proof.
intros sf sd0 sd b js L HF cbs.

assert (SPL : exists pre x9 post, js = pre ++ x9 :: post /\ length pre = 9%nat /\ length post = 6%nat).
{ exists (firstn 9 js). destruct (skipn 9 js) as [|x9 post] eqn:E.
- exfalso. pose proof (f_equal (@length _) E) as X. rewrite length_skipn in X. cbn in X. lia.
- exists x9, post. split; [rewrite <- E; symmetry; apply firstn_skipn|].
pose proof (f_equal (@length _) E) as X. rewrite length_skipn in X. cbn in X. rewrite length_firstn. lia. }
first [ sf_destruct 6%nat SPL as pre x9 post -> Lpre Lpost | sf_fb; destruct SPL as (pre & x9 & post & -> & Lpre & Lpost) ].
pose proof (proj1 (Forall_app _ _ _) HF) as [Fpre Fx]. inversion Fx; subst. rename H1 into F9. rename H2 into Fpost. clear Fx.
destruct x9 as [a9 b9]. cbn [fst snd] in F9. destruct F9 as [La Lb].
exists (pre ++ (le4 (Z_to_bv 64 9) ++ skipn 4 a9, b9) :: post).
split; [rewrite length_app; cbn [length]; lia|]. split.
{ apply Forall_app. split; [exact Fpre|]. constructor; [| exact Fpost]. cbn [fst snd]. rewrite length_app, length_le4, length_skipn. lia. }
subst cbs.
set (PRE := pre_bytes pre). set (POST := cbs_bytes 6 sf sd0 b post).
assert (LP : length PRE = 360%nat) by (subst PRE; rewrite pre_bytes_length, Lpre by assumption; reflexivity).
assert (X1 : cbs_bytes 16 sf sd0 b (pre ++ (a9, b9) :: post) = PRE ++ (a9 ++ le8 (Z_to_bv 64 (if b then sf else 0)) ++ le8 (Z_to_bv 64 (if b then sd0 else 0)) ++ b9) ++ POST).
{ replace 16%nat with (7 + length pre)%nat by (rewrite Lpre; reflexivity). rewrite cbs_bytes_split by lia. subst PRE POST. destruct b; reflexivity. }
assert (X2 : cbs_bytes 16 sf sd true (pre ++ (le4 (Z_to_bv 64 9) ++ skipn 4 a9, b9) :: post) = PRE ++ ((le4 (Z_to_bv 64 9) ++ skipn 4 a9) ++ le8 (Z_to_bv 64 sf) ++ le8 (Z_to_bv 64 sd) ++ b9) ++ POST).
{ replace 16%nat with (7 + length pre)%nat by (rewrite Lpre; reflexivity). rewrite cbs_bytes_split by lia. subst PRE POST.
rewrite (cbs_bytes_indep 6 sf sd sd0 true b post) by (cbn; lia). reflexivity. }
rewrite X1, X2. clear X1 X2.
set (f0 := Z_to_bv 64 (if b then sf else 0)). set (d0 := Z_to_bv 64 (if b then sd0 else 0)). clearbody f0 d0.
rewrite (firstn_len_exact PRE _ 360 LP).
replace 364%nat with (360 + 4)%nat by reflexivity. rewrite (skipn_app_len PRE _ 360 4 LP).
rewrite <- !app_assoc.
replace (skipn 4 (a9 ++ le8 f0 ++ le8 d0 ++ b9 ++ POST)) with (skipn 4 a9 ++ le8 f0 ++ le8 d0 ++ b9 ++ POST)
by (rewrite skipn_app, La; reflexivity).
assert (L4 : length (skipn 4 a9) = 4%nat) by (rewrite length_skipn, La; reflexivity).
rewrite (firstn_len_exact (skipn 4 a9) _ 4 L4).
replace 12%nat with (4 + 8)%nat by reflexivity. rewrite (skipn_app_len (skipn 4 a9) _ 4 8 L4).
rewrite (skipn_len_exact (le8 f0) _ 8 (length_le8 f0)). rewrite (skipn_len_exact (le8 d0) _ 8 (length_le8 d0)).
reflexivity.
Qed.

Lemma cbs_ok_install : forall SH SD b cbs,
cbs_ok SH SD b cbs ->
cbs_ok SH SD true (firstn 360 cbs ++ le4 (Z_to_bv 64 9) ++ firstn 4 (skipn 364 cbs) ++ le8 (Z_to_bv 64 SH) ++ le8 (Z_to_bv 64 SD) ++ skipn 8 (skipn 12 (skipn 364 cbs))).
Proof.
intros SH SD b cbs sfH_; first [ sf_destruct 4%nat sfH_ as js L HF -> | sf_fb; destruct sfH_ as (js & L & HF & ->) ]. rewrite !cbs_cells_bytes.
first [ pose proof (cbs_install SH SD SD b js L HF) as sfP_; sf_destruct 4%nat sfP_ as js' L' HF' E | sf_fb; destruct (cbs_install SH SD SD b js L HF) as (js' & L' & HF' & E) ].
exists js'. split; [exact L'|]. split; [exact HF'|]. rewrite cbs_cells_bytes. symmetry. exact E.
Qed.
