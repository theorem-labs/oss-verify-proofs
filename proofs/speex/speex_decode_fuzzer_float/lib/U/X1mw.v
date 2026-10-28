(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Ltac asm := first [ eassumption | lazymatch goal with |- ?G => fail 100 "ASMFAIL:" G end ].

Lemma blocks_apart_ij : forall (L : list block) (i j : nat) bi bj,
List.NoDup (map blk_id L) -> lbd_apart L -> (i < j)%nat ->
nth_error L i = Some bi -> nth_error L j = Some bj ->
blk_addr bi + blk_size bi <= blk_addr bj \/ blk_addr bj + blk_size bj <= blk_addr bi.
Proof.
intros L i j bi bj ND AP Hij Hi Hj. apply AP; [eapply nth_error_In; exact Hi| eapply nth_error_In; exact Hj|].
intros E.
pose proof (proj1 (List.NoDup_nth_error (map blk_id L)) ND i j) as U.
rewrite length_map in U.
assert (Hl : (i < length L)%nat) by (apply nth_error_Some; congruence).
rewrite !nth_error_map, Hi, Hj in U. cbn in U. specialize (U Hl ltac:(rewrite E; reflexivity)). lia.
Qed.

Lemma land64_zero_iff : forall r, -2^63 <= r < 2^63 -> (Z.land r 18446744073709551615 = 0 <-> r = 0).
Proof.
intros r Hr. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
split; intros H; [| subst; reflexivity].
destruct (Z_lt_le_dec r 0).
- exfalso. replace r with ((r + 2^64) + (-1) * 2^64) in H by lia.
rewrite Z.mod_add in H by lia. rewrite Z.mod_small in H by lia. lia.
- rewrite Z.mod_small in H by lia. exact H.
Qed.

Lemma lts_zero_lit : forall r, -2^63 <= r < 2^63 -> bv_lts (Z_to_bv 64 0) (Z_to_bv 64 r) = (0 <? r).
Proof. intros r Hr. unfold bv_lts. rewrite !zb_signed_small by lia. reflexivity. Qed.
Lemma eqb_zero_lit : forall r, -2^63 <= r < 2^63 -> bv_eqb (Z_to_bv 64 r) (Z_to_bv 64 0) = (r =? 0).
Proof.
intros r Hr. unfold bv_eqb. destruct (Z.eqb_spec r 0) as [->|NE].
- rewrite Z.eqb_refl. reflexivity.
- apply Z.eqb_neq. intros E. apply NE. apply (proj1 (land64_zero_iff r Hr)).
rewrite <- unsigned_lit_land. rewrite E. reflexivity.
Qed.

Lemma sb_inv_set_submodeID : forall (s : sbd_state bptr) v, sb_inv s -> 0 <= v <= 7 -> sb_inv (set_sbd_submodeID s v).
Proof. intros s v H Hv. unfold sb_inv in *. destruct s; cbn in *. destruct sbd_innov_save; destruct sbd_mode; intuition lia. Qed.
Lemma sb_inv_set_first : forall (s : sbd_state bptr) v, sb_inv s -> (v = 0 \/ v = 1) -> sb_inv (set_sbd_first s v).
Proof. intros s v H Hv. unfold sb_inv in *. destruct s; cbn in *. destruct sbd_innov_save; destruct sbd_mode; intuition lia. Qed.
Lemma sb_blocks_set_submodeID : forall (s : sbd_state bptr) v S a, sb_blocks (set_sbd_submodeID s v) S a = sb_blocks s S a.
Proof. intros. destruct s; reflexivity. Qed.
Lemma sb_blocks_set_first : forall (s : sbd_state bptr) v S a, sb_blocks (set_sbd_first s v) S a = sb_blocks s S a.
Proof. intros. destruct s; reflexivity. Qed.
Ltac close_sbinv :=
first [ assumption |
lazymatch goal with
| |- sb_inv (set_sbd_submodeID _ _) => apply sb_inv_set_submodeID; [close_sbinv | lia]
| |- sb_inv (set_sbd_first _ _) => apply sb_inv_set_first; [close_sbinv | lia]
end ].

Section Inv.
Context {RCEIL : RunCeiling}.
Variable k : nat.
Variable X : sbinv.
Hypothesis IH : sb_ihyps k X.
Local Notation S := (x_S X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation lo := (x_lo X). Local Notation a := (x_a X). Local Notation LBL := (x_LBL X).
Local Notation s0 := (x_s X). Local Notation b0 := (x_b0 X).
Local Notation usp := (bv_unsigned (x_sp X)).
Local Notation FS := (sbd_subframeSize (x_s X)).

#[using="RCEIL k IH"] Lemma FS_cases : FS = 40 \/ FS = 80.
Proof.
pose proof (ih_inv0 _ _ IH) as sfP_; first [ sf_destruct 5%nat sfP_ as Hmo _ _ E _ | sf_fb; destruct sfP_ as (Hmo & _ & _ & E & _) ]. rewrite E. destruct Hmo as [-> | ->]; cbn; lia.
Qed.
#[using="RCEIL k IH"] Lemma fs_eq : sbd_frame_size s0 = 4 * FS.
Proof.
pose proof (ih_inv0 _ _ IH) as sfP_; first [ sf_destruct 5%nat sfP_ as Hmo E1 _ E _ | sf_fb; destruct sfP_ as (Hmo & E1 & _ & E & _) ]. rewrite E1, E. destruct Hmo as [-> | ->]; reflexivity.
Qed.
#[using="RCEIL k IH"] Lemma ffs_eq : sbd_full_frame_size s0 = 8 * FS.
Proof.
pose proof (ih_inv0 _ _ IH) as sfP_; first [ sf_destruct 5%nat sfP_ as Hmo E1 E2 E _ | sf_fb; destruct sfP_ as (Hmo & E1 & E2 & E & _) ]. rewrite E2, E1, E. destruct Hmo as [-> | ->]; reflexivity.
Qed.

#[using="RCEIL k IH"] Lemma USPk : forall c, -24576 <= c <= 0 -> bv_unsigned (Z_to_bv 64 (usp + c)) = usp + c.
Proof.
intros c Hc. pose proof (lay_top_lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ih_lay _ _ IH)) as T0.
pose proof (ih_spx _ _ IH) as SPX. pose proof (ih_lo _ _ IH) as LO. pose proof (ih_RD _ _ IH) as RD.
unfold alloc_ceiling, SB_LOCAL_DEPTH in *. apply unsigned_lit. lia.
Qed.

#[using="Type"] Lemma rdec_depth_of_depth : forall d d' : dec_state bptr, dec_depth d' = dec_depth d -> rdec_depth d' = rdec_depth d.
Proof.
induction d as [st|s low IHd]; intros d' E; destruct d' as [st'|s' low']; cbn in E |- *; try reflexivity.
- pose proof (X1n8.dec_depth_pos low'). lia.
- pose proof (X1n8.dec_depth_pos low). lia.
- rewrite (IHd low') by lia. reflexivity.
Qed.
#[using="Type"] Lemma rdec_depth_nonneg : forall d : dec_state bptr, 0 <= rdec_depth d.
Proof. induction d; cbn; unfold NB_DECODE_DEPTH, NB_FRAME, NB_FPRINTF_DEPTH, SB_LOCAL_DEPTH in *; lia. Qed.
End Inv.

Ltac open_ihyps IH :=
lazymatch type of IH with sb_ihyps _ ?X =>
pose proof (ih_lay _ _ IH) as LAY; pose proof (ih_spx _ _ IH) as SPX; pose proof (ih_sp16 _ _ IH) as SP16;
pose proof (ih_lo _ _ IH) as LO; pose proof (ih_RD _ _ IH) as RD0; unfold SB_LOCAL_DEPTH in LO;
pose proof (ih_hi _ _ IH) as (AHI & OHI & SHI);
pose proof (ih_Sal _ _ IH) as SAL; pose proof (ih_inv0 _ _ IH) as INV0;
pose proof (lay_top_lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as Tlo;
pose proof (lay_top_OUT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as Tout;
pose proof (lay_top_A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as Ta;
pose proof (lay_top_STEREO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as Tst;
pose proof (lay_ceil_S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as CS; pose proof (lay_pos_S _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as PS;
pose proof (lay_ceil_D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as CD; pose proof (lay_pos_D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as PD;
pose proof (lay_ceil_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as CG0; pose proof (lay_pos_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as PG0;
pose proof (lay_ceil_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as CG1; pose proof (lay_pos_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as PG1;
pose proof (lay_ceil_EXC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as CEXC; pose proof (lay_pos_EXC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as PEXC;
pose proof (lay_ceil_OQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as COQ; pose proof (lay_pos_OQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as POQ;
pose proof (lay_ceil_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as CIQ; pose proof (lay_pos_IQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as PIQ;
pose proof (lay_ceil_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as CMSP; pose proof (lay_pos_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as PMSP;
pose proof (lay_ceil_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as CPG; pose proof (lay_pos_PG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as PPG;
pose proof (lay_ceil_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as CER; pose proof (lay_pos_ER _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as PER;
pose proof (proj1 alloc_ceiling_bounds) as ACE; pose proof (proj2 alloc_ceiling_bounds) as ACE';
assert (LOu : x_lo X + 24576 <= bv_unsigned (x_sp X)) by lia;
pose proof (USPk _ _ IH (-384) ltac:(lia)) as USP384;
pose proof (FS_cases _ _ IH) as HFS; pose proof (fs_eq _ _ IH) as Hfs; pose proof (ffs_eq _ _ IH) as Hffs
end.

Ltac open_ctx CTX :=
let MU := fresh "MU" in let WM := fresh "WM" in let MI := fresh "MI" in
let PCS := fresh "PCS" in let JOK := fresh "JOK" in let BUF := fresh "BUF" in let INV := fresh "INV" in
let Emo := fresh "Emo" in let Efs := fresh "Efs" in let Efr := fresh "Efr" in let Eis := fresh "Eis" in
let DR := fresh "DR" in let DD := fresh "DD" in let XR := fresh "XR" in
let REP := fresh "REP" in let BOK := fresh "BOK" in let BK := fresh "BK" in
let XO := fresh "XO" in let LO_ := fresh "Lows" in let XS := fresh "XS" in
let TP := fresh "TP" in let SE := fresh "SE" in let SS := fresh "SS" in
let NM := fresh "NM" in let NST := fresh "NST" in
let Ebl := fresh "Ebl" in
sf_curry 26%nat CTX; intros MU WM MI PCS JOK BUF INV Emo Efs Efr Eis Ebl DR DD XR NM NST REP BOK BK XO LO_ XS TP SE SS; sf_clear CTX; sf_fix_order;
cbv iota in XR;
let BKo := fresh "BKo" in let BKc := fresh "BKc" in let BSZ := fresh "BSZ" in
destruct BK as (BKo & BKc & BSZ);
unfold sbWX, SBSTATE_SIZEOF, BITS_SIZEOF, HOUT_BYTES in MU;
let P0 := fresh "P0" in let P1 := fresh "P1" in let P2 := fresh "P2" in let P3 := fresh "P3" in
let P4 := fresh "P4" in let P5 := fresh "P5" in let P6 := fresh "P6" in let P7 := fresh "P7" in
sf_curry 8%nat PCS; intros P0 P1 P2 P3 P4 P5 P6 P7; sf_clear PCS; sf_fix_order;
unfold sbp_hdr in P0; unfold sbp_ptrs in P2; unfold sbp_cfg in P5;
let B0 := fresh "BG0" in let B1 := fresh "BG1" in let B2 := fresh "BEXC" in let B3 := fresh "BOQ" in
let B4 := fresh "BIQ" in let B5 := fresh "BMSP" in let B6 := fresh "BPG" in let B7 := fresh "BER" in
sf_curry 8%nat BUF; intros B0 B1 B2 B3 B4 B5 B6 B7; sf_clear BUF; sf_fix_order;
let L1 := fresh "Lpad1" in let L2 := fresh "Lpad2" in let L3 := fresh "Lg0" in let L4 := fresh "Lg1" in
let L5 := fresh "Lexc" in let L6 := fresh "Loq" in let L7 := fresh "Liq" in let L8 := fresh "Lmsp" in
let L9 := fresh "Lpg" in let L10 := fresh "Ler" in
pose proof JOK as sfP_; sf_curry 10%nat sfP_; intros L1 L2 L3 L4 L5 L6 L7 L8 L9 L10; sf_clear sfP_; sf_fix_order;
try rewrite Efs in L5.

Ltac sbred :=
cbn [sbd_mode sbd_full_frame_size sbd_frame_size sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first
sbd_sampling_rate sbd_lpc_enh_enabled sbd_innov_save sbd_encode_submode sbd_submodeID
set_sbd_first set_sbd_submodeID].
Ltac sjred := cbn [sj_last_ener sj_seed sj_pad1 sj_pad2 sj_g0 sj_g1 sj_exc sj_oq sj_iq sj_msp sj_pg sj_er].

Ltac close_goal MU :=
lazymatch goal with
| |- munch _ _ _ => first [ exact MU | unfold sbWX, SBSTATE_SIZEOF, BITS_SIZEOF, HOUT_BYTES; exact MU ]
| |- sb_pieces _ _ _ _ _ _ => unfold sb_pieces, sbp_hdr, sbp_ptrs, sbp_cfg; sbred; sjred; repeat match goal with |- _ /\ _ => split end; asm
| |- sb_bufs _ _ _ _ => unfold sb_bufs; sjred; repeat match goal with |- _ /\ _ => split end; asm
| |- sb_junk_ok _ _ => first [ assumption | unfold sb_junk_ok; sbred; sjred; repeat split; first [lia | asm] ]
| |- sb_inv _ => close_sbinv
| |- bits_keep _ _ => unfold bits_keep; repeat split; first [assumption | congruence | lia]
| |- dec_depth _ = _ => first [ assumption | rewrite !ctl_keeps_depth; first [assumption | lia] | congruence | lia ]
| |- sb_blocks _ _ _ = _ => rewrite ?sb_blocks_set_submodeID, ?sb_blocks_set_first; first [assumption | reflexivity | congruence]
| |- dec_mode _ = _ => first [ assumption | rewrite !ctl_keeps_mode; first [assumption | congruence] | congruence ]
| |- dec_nested _ => first [ assumption | repeat apply ctl_keeps_nested; assumption ]
| |- True => exact I
| |- _ => first [ asm | reflexivity | lia | congruence ]
end.
Ltac close_ctx MU := unfold sbctx; repeat match goal with |- _ /\ _ => split end; close_goal MU.

Ltac junk_exists :=
lazymatch goal with
| P3 : rw_cells _ ?m (?st + 128) [C4 ?le] |- _ =>
lazymatch goal with | P4 : rw_cells _ m (st + 132) [C4 ?seed] |- _ =>
lazymatch goal with | P5 : rw_cells _ m (st + 136) [_; CB 4 ?pad1; _] |- _ =>
lazymatch goal with | P7 : rw_cells _ m (st + 156) [CB 4 ?pad2] |- _ =>
lazymatch goal with | P2 : rw_cells _ m (st + 40) [_; _; _; C8 (Z_to_bv 64 ?g0a); C8 (Z_to_bv 64 ?g1a); C8 (Z_to_bv 64 ?exca); C8 (Z_to_bv 64 ?oqa); C8 (Z_to_bv 64 ?iqa); C8 (Z_to_bv 64 ?mspa); C8 (Z_to_bv 64 ?pga); C8 (Z_to_bv 64 ?era); _] |- _ =>
lazymatch goal with | B0 : rw_cells _ m g0a (f32 ?g0) |- _ =>
lazymatch goal with | B1 : rw_cells _ m g1a (f32 ?g1) |- _ =>
lazymatch goal with | B2 : rw_cells _ m exca (f32 ?exc) |- _ =>
lazymatch goal with | B3 : rw_cells _ m oqa (f32 ?oq) |- _ =>
lazymatch goal with | B4 : rw_cells _ m iqa (f32 ?iq) |- _ =>
lazymatch goal with | B5 : rw_cells _ m mspa (f32 ?msp) |- _ =>
lazymatch goal with | B6 : rw_cells _ m pga (f32 ?pg) |- _ =>
lazymatch goal with | B7 : rw_cells _ m era (f32 ?er) |- _ =>
exists (SBJ le seed pad1 pad2 g0 g1 exc oq iq msp pg er)
end end end end end end end end end end end end end.

Ltac frame_exists :=
lazymatch goal with
| FL : rw_cells _ ?m (_ + -384) [C8 ?a0; C8 ?a1; C8 ?a2; C8 ?a3; C8 ?a4; C8 ?a5; C8 ?a6; C8 ?a7; C8 ?a8; C8 ?a9; C8 ?a10; C8 ?a11;
C8 ?a12; C8 ?a13; C8 ?a14; C8 ?a15; C8 ?a16; C8 ?a17; C8 ?a18; C8 ?a19; C8 ?a20; C8 ?a21; C8 ?a22; C8 ?a23;
C8 ?a24; C8 ?a25; C8 ?a26; C8 ?a27; C4 ?a28; C4 ?a29] |- _ =>
exists (SFR a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29)
end.
Ltac close_frame := unfold frame_at, fr_saves, sframe_cells; cbv zeta;
cbn [f_0 f_8 f_16 f_24 f_32 f_40 f_48 f_56 f_64 f_72 f_80 f_88 f_96 f_104 f_112 f_120 f_128 f_136 f_144 f_152
f_160 f_168 f_176 f_184 f_192 f_200 f_208 f_216 f_224 f_dtx];
repeat match goal with |- _ /\ _ => split end; asm.

Ltac nsegs H := cbv delta [X1ff.rsegs X1fd.rsegs X1gj.rsegs] in H.

Ltac name_post :=
lazymatch goal with |- evt _ _ (MS _ _ _ ?fc _ ?m _) =>
try match goal with H : frm0 fc |- _ => rename H into FRMc end;
try match goal with H : stk _ m _ _ |- _ => nsegs H; rename H into STc end;
try match goal with H : DREP _ _ m _ _ _ |- _ => rename H into DRc end;
try match goal with H : mem_inv _ m |- _ => rename H into MI end
end.

Ltac after_bits R b' :=
try clear R; try rename MI0 into MI;
match goal with H : bits_rep _ _ _ _ b' |- _ => rename H into R end.
