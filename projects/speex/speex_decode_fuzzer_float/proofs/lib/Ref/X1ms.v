(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7 X1n8 X1ho X1hm X1hu X1ht X1ih X1nr X1mc X1mv X1mb X1ma X1mw X1mr.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation MODEP mo := (sb_mode_ptr NB_MODE_PTR A_speex_wb_mode A_speex_uwb_mode mo).
Local Notation SUBP mo := (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR mo).

Section Seg.
Context {RCEIL : RunCeiling}.
Variable k : nat.
Variable X : sbinv.
Hypothesis IH : sb_ihyps k X.
Local Notation S := (x_S X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation lo := (x_lo X). Local Notation a := (x_a X). Local Notation LBL := (x_LBL X).
Local Notation s0 := (x_s X). Local Notation b0 := (x_b0 X). Local Notation canary := (x_canary X). Local Notation st := (x_st X).
Local Notation sp := (x_sp X). Local Notation gp := (x_gp X). Local Notation tp := (x_tp X). Local Notation ra0 := (x_ra X).
Local Notation cs0 := (x_s0 X). Local Notation cs1 := (x_s1 X). Local Notation cs2 := (x_s2 X). Local Notation cs3 := (x_s3 X).
Local Notation cs4 := (x_s4 X). Local Notation cs5 := (x_s5 X). Local Notation cs6 := (x_s6 X). Local Notation cs7 := (x_s7 X).
Local Notation cs8 := (x_s8 X). Local Notation cs9 := (x_s9 X). Local Notation cs10 := (x_s10 X). Local Notation cs11 := (x_s11 X).
Local Notation F0 := (x_F X). Local Notation m0 := (x_m0 X).
Local Notation usp := (bv_unsigned (x_sp X)).
Local Notation FS := (sbd_subframeSize (x_s X)).
Local Notation mo := (sbd_mode (x_s X)).
Local Notation HCTL := (h_ctl _ (ih_hyps _ _ IH)).

Definition at_L (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (r : smrec) (sub : Z) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xa0 xs2 xs3 xs6 xs7 xs11 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe) (vpi ver vq viq vak : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -432)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
xa0 (c_a1 kk) (Z_to_bv 64 4096) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
xs2 xs3 (Z_to_bv 64 OUT) (Z_to_bv 64 (usp + -368)) xs6 xs7 (Z_to_bv 64 sub) (Z_to_bv 64 0) (Z_to_bv 64 sub) xs11
(c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x28398) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -432) /\ frame_at X m fr
/\ f_0 fr = Z_to_bv 64 (usp + -304) /\ f_8 fr = Z_to_bv 64 (OUT + 4 * sbd_frame_size s0 + 12) /\ f_16 fr = Z_to_bv 64 (OUT + 4 * sbd_frame_size s0 + 4)
/\ f_24 fr = Z_to_bv 64 (sbmode_struct mo) /\ f_32 fr = Z_to_bv 64 OUT /\ f_40 fr = Z_to_bv 64 0x10378
/\ f_48 fr = Z_to_bv 64 (usp + -420) /\ f_56 fr = Z_to_bv 64 (usp + -428) /\ f_64 fr = Z_to_bv 64 (usp + -336)
/\ f_72 fr = Z_to_bv 64 (usp + -400) /\ f_80 fr = Z_to_bv 64 (usp + -320) /\ f_88 fr = Z_to_bv 64 (S + 132)
/\ f_96 fr = Z_to_bv 64 (usp + -432) /\ f_120 fr = Z_to_bv 64 A /\ f_dtx fr = Z_to_bv 64 dtx /\ (dtx = 0 \/ dtx = 1)
/\ sb_smrec_at mo (sbd_submodeID s1) = Some r /\ 0 <= sub <= 3
/\ rw_cells rsegs m (usp + -320) (f32 vpi) /\ length vpi = 4%nat
/\ rw_cells rsegs m (usp + -336) (f32 ver) /\ length ver = 4%nat
/\ rw_cells rsegs m (usp + -368) (f32 vq) /\ length vq = 8%nat
/\ rw_cells rsegs m (usp + -400) (f32 viq) /\ length viq = 8%nat
/\ rw_cells rsegs m (usp + -432) (f32 vak) /\ length vak = 8%nat.

#[using="RCEIL k IH"] Lemma sbV3 : forall low dtx s1 b r ms, at_V2 X low dtx s1 b r ms -> evt rsegs (at_L low dtx s1 r 0 b) ms.
Proof.
intros low dtx s1 b r ms AT.
first [ sf_destruct 30%nat AT as Fx fc m kk xra j ows stb fr vpi ver vq viq -> FRM CTX ST FRA F0eq Fdtx DTX01 SAT VPI Lvpi VER Lver VQ Lvq VIQ Lviq | sf_fb; destruct AT as (Fx & fc & m & kk & xra & j & ows & stb & fr & vpi & ver & vq & viq & -> & FRM & CTX & ST & FRA & F0eq & Fdtx & DTX01 & SAT & VPI & Lvpi & VER & Lver & VQ & Lvq & VIQ & Lviq) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ _ _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & Inb1 & Ilpc1 & _) ].

zstep. zstep. zstep. zstep.
match goal with |- context [Z_to_bv 64 (usp + -400 + ?e)] => replace (usp + -400 + e) with (usp + -432) by lia end.
zstep. zstep.
match goal with |- context [Z_to_bv 64 (usp + -400 + ?e)] => replace (usp + -400 + e) with (usp + -4496) by lia end.
probe_store ST (usp + -4496).
zstep. rewrite (lts_ge_false' (usp + -432) (usp + -4496)) by lia. zstep.
carve_frame 32%nat ST. destruct (rw_cells_CB_f32 rsegs _ _ 8%nat _ FR) as (vak & Lvak & VAK); clear FR.

zstep. rewrite Inb1. rewrite (sx32_lit 4) by lia. zstep. rewrite (lts_zero_lit 4) by lia. if_false_x.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. lstep. zstep. zstep. zstep. zstep.
apply evt_done. unfold at_L.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _, _, _, _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
first [ unshelve sf_eexists 5%nat; [ exact (vpi) | exact (ver) | exact (vq) | exact (viq) | exact (vak) | ] | sf_fb; exists vpi, ver, vq, viq, vak ].
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctx MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
cbn [f_0 f_8 f_16 f_24 f_32 f_40 f_48 f_56 f_64 f_72 f_80 f_88 f_96 f_104 f_112 f_120 f_128 f_dtx].
repeat match goal with |- _ /\ _ => split end.
all: first [ reflexivity | assumption | lia | f_equal; lia ].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.
End Seg.
