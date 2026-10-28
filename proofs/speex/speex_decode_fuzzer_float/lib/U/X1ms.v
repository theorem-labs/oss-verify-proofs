(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma X1mw X1mr.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac upto p := repeat (tryif ub_at_pc p then fail else (tryif ub_at_if then ub_dec else ub_step)).

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
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xa0 xs2 xs3 xs4 xs7 xs8 xs9 xs11 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe) (vpi ver vq viq vak : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -512)) gp tp (Z_to_bv 64 OUT) (c_t1 kk) (Z_to_bv 64 sub) sp (Z_to_bv 64 S)
xa0 (c_a1 kk) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
xs2 xs3 xs4 (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 (18446744073709551615 - (usp + -512))) xs7 xs8 xs9
(Z_to_bv 64 (usp + -512)) xs11
(c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2f248) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -512) /\ frame_at X m fr
/\ f_0 fr = Z_to_bv 64 (usp + -384) /\ f_8 fr = Z_to_bv 64 0 /\ f_16 fr = Z_to_bv 64 (sbmode_struct mo)
/\ f_24 fr = Z_to_bv 64 (18446744073709551615 - (usp + -416)) /\ f_32 fr = Z_to_bv 64 (usp + -416) /\ f_40 fr = Z_to_bv 64 4
/\ f_56 fr = Z_to_bv 64 2147483647 /\ f_64 fr = Z_to_bv 64 32 /\ f_72 fr = Z_to_bv 64 (18446744073709551615 - (usp + -400))
/\ f_80 fr = Z_to_bv 64 (usp + -508) /\ f_88 fr = Z_to_bv 64 8 /\ f_96 fr = Z_to_bv 64 (S + 132)
/\ f_104 fr = Z_to_bv 64 (usp + -480) /\ f_112 fr = Z_to_bv 64 4 /\ f_120 fr = Z_to_bv 64 (usp + -400)
/\ f_128 fr = Z_to_bv 64 OUT /\ f_144 fr = Z_to_bv 64 (18446744073709551615 - (usp + -448)) /\ f_152 fr = Z_to_bv 64 32
/\ f_160 fr = Z_to_bv 64 A /\ f_176 fr = Z_to_bv 64 (usp + -448) /\ f_184 fr = Z_to_bv 64 0
/\ f_208 fr = Z_to_bv 64 1 /\ f_216 fr = Z_to_bv 64 4294967296 /\ f_dtx fr = Z_to_bv 64 dtx /\ (dtx = 0 \/ dtx = 1)
/\ sb_smrec_at mo (sbd_submodeID s1) = Some r /\ 0 <= sub <= 3
/\ rw_cells rsegs m (usp + -400) (f32 vpi) /\ length vpi = 4%nat
/\ rw_cells rsegs m (usp + -416) (f32 ver) /\ length ver = 4%nat
/\ rw_cells rsegs m (usp + -448) (f32 vq) /\ length vq = 8%nat
/\ rw_cells rsegs m (usp + -480) (f32 viq) /\ length viq = 8%nat
/\ rw_cells rsegs m (usp + -512) (f32 vak) /\ length vak = 8%nat.

#[using="RCEIL k IH"] Lemma sbV3 : forall low dtx s1 b r ms, at_V2 X low dtx s1 b r ms -> evt rsegs (at_L low dtx s1 r 0 b) ms.
Proof.
intros low dtx s1 b r ms AT.
first [ sf_destruct 45%nat AT as Fx fc m kk xra xa0 xa1 j ows stb fr vpi ver vq viq -> FRM CTX ST FRA F0eq F16 F32 F40 F104 F112 F120 F128 F144 F152 F160 F176 F184 F208 Fdtx DTX01 SAT VPI Lvpi VER Lver VQ Lvq VIQ Lviq | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & xa1 & j & ows & stb & fr & vpi & ver & vq & viq & -> & FRM & CTX & ST & FRA & F0eq & F16 & F32 & F40 & F104 & F112 & F120 & F128 & F144 & F152 & F160 & F176 & F184 & F208 & Fdtx & DTX01 & SAT & VPI & Lvpi & VER & Lver & VQ & Lvq & VIQ & Lviq) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ _ _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & Inb1 & Ilpc1 & _) ].

upto 0x2f1ac.
replace (usp + -480 + - (32)) with (usp + -512) by lia.
upto 0x2f1b4.
match goal with |- context [Z_to_bv 64 (usp + -480 + - ?e)] => replace (usp + -480 + - e) with (usp + -4576) by lia end.
probe_store ST (usp + -4576).
zstep. rewrite (lts_ge_false' (usp + -512) (usp + -4576)) by lia. zstep.
carve_frame 32%nat ST. destruct (rw_cells_CB_f32 rsegs _ _ 8%nat _ FR) as (vak & Lvak & VAK); clear FR.
zstep. rewrite Inb1. rewrite (sx32_lit 4) by lia.
upto 0x2f1e4. rewrite F120. upto 0x2f1f0. rewrite F32. upto 0x2f21c. lstep. upto 0x2f248.
pose proof INV0 as (Imo & _).
assert (SMS : 1 <= sbmode_struct mo < 2^63 /\ sbmode_struct mo mod 8 = 0)
by (destruct Imo as [-> | ->]; cbn [sbmode_struct]; unfold A_sb_wb_mode, A_sb_uwb_mode; (split; [lia | reflexivity])).
assert (E8 : forall c, c = 18446744073709551615 -> Z.lor (Z.b2z (Z.land (sbmode_struct mo) c <? 1)) (Z.b2z (0 <? Z.land (Z.land (sbmode_struct mo) c) 7)) = 0).
{ intros c ->. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. rewrite sh_land7.
replace (sbmode_struct mo mod 8) with 0 by lia. replace (sbmode_struct mo <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
rewrite (E8 _ eq_refl) in FL.
rewrite !zb_lxor_ones in FL by lia. rewrite !zb_lxor_ones by lia.
apply evt_done. unfold at_L.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _, _, _, _, _, _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
first [ unshelve sf_eexists 5%nat; [ exact (vpi) | exact (ver) | exact (vq) | exact (viq) | exact (vak) | ] | sf_fb; exists vpi, ver, vq, viq, vak ].
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctx MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
cbn [f_0 f_8 f_16 f_24 f_32 f_40 f_48 f_56 f_64 f_72 f_80 f_88 f_96 f_104 f_112 f_120 f_128 f_136 f_144 f_152 f_160 f_168 f_176 f_184 f_192 f_200 f_208 f_216 f_224 f_dtx].
repeat match goal with |- _ /\ _ => split end.
all: first [ reflexivity | assumption | lia | f_equal; lia ].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.
End Seg.
