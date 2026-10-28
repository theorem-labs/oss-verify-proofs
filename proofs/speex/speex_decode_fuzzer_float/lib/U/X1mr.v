(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma X1mw X1mt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mo.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation MODEP mo := (sb_mode_ptr NB_MODE_PTR A_speex_wb_mode A_speex_uwb_mode mo).
Local Notation SUBP mo := (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR mo).

Ltac probe_store ST e :=
let HS := fresh "HS" in
lazymatch type of ST with stk ?segs ?m ?lo ?hi =>
unshelve epose proof (stk_store_ok m lo hi e 8%nat ST _ _) as HS; [lia | lia |] end;
step; change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)); store_done.
Ltac vgo p := repeat lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => tryif constr_eq q p then fail else (fix_mi; lstep; zsimp)
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ lit_if | ub_chk | ub_dec ]
end.

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

Definition at_V1 (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (b : bits_st bptr) (r : smrec) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xa0 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe) (vpi ver : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -416)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
xa0 (c_a1 kk) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
(Z_to_bv 64 (usp + -416)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 A)
(Z_to_bv 64 (sbmode_struct mo)) cs8 cs9 cs10 cs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2f06c) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -416) /\ frame_at X m fr
/\ f_0 fr = Z_to_bv 64 (usp + -384) /\ f_16 fr = Z_to_bv 64 (sbmode_struct mo) /\ f_32 fr = Z_to_bv 64 (usp + -416)
/\ f_40 fr = Z_to_bv 64 4 /\ f_112 fr = Z_to_bv 64 4 /\ f_120 fr = Z_to_bv 64 (usp + -400) /\ f_128 fr = Z_to_bv 64 OUT
/\ f_160 fr = Z_to_bv 64 A /\ f_184 fr = Z_to_bv 64 0 /\ f_208 fr = Z_to_bv 64 1
/\ f_dtx fr = Z_to_bv 64 dtx /\ (dtx = 0 \/ dtx = 1)
/\ sb_smrec_at mo (sbd_submodeID s1) = Some r
/\ rw_cells rsegs m (usp + -400) (f32 vpi) /\ length vpi = 4%nat
/\ rw_cells rsegs m (usp + -416) (f32 ver) /\ length ver = 4%nat.

#[using="RCEIL k IH"] Lemma sbV1 : forall low dtx s1 b r ms, at_V X low dtx s1 b r ms ->
evt rsegs (at_V1 (snd (speex_decoder_ctl (snd (speex_decoder_ctl low CtlGetPiGain)) CtlGetExc)) dtx s1 b r) ms.
Proof.
intros low dtx s1 b r ms AT.
first [ sf_destruct 23%nat AT as Fx fc m kk xra j ows stb fr -> FRM CTX ST FRA F0eq F16 F128 F160 F184 F208 Fdtx DTX01 SAT | sf_fb; destruct AT as (Fx & fc & m & kk & xra & j & ows & stb & fr & -> & FRM & CTX & ST & FRA & F0eq & F16 & F128 & F160 & F184 & F208 & Fdtx & DTX01 & SAT) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ _ _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & Inb1 & Ilpc1 & _) ].
pose proof (ih_nodup _ _ IH) as ND. pose proof (ih_apart _ _ IH) as APB. pose proof (ih_range _ _ IH) as RNG.
pose proof (ih_dk _ _ IH) as [DK1 DK2].

zstep. rewrite Inb1. rewrite (sx32_lit 4) by lia.
zgo 0x2f000.
match goal with |- context [Z_to_bv 64 (usp + -384 + ?e)] => replace (usp + -384 + e) with (usp + -400) by lia end.
zstep.
match goal with |- context [Z_to_bv 64 (usp + -384 + - ?e)] => replace (usp + -384 + - e) with (usp + -4480) by lia end.
probe_store ST (usp + -4480).
zstep. rewrite (lts_ge_false' (usp + -400) (usp + -4480)) by lia. zstep.
zgo 0x2f014.
carve_frame 16%nat ST. destruct (rw_cells_CB_f32 rsegs _ _ 4%nat _ FR) as (vpi & Lvpi & VPI); clear FR.

zstep. rewrite Inb1. rewrite (sx32_lit 4) by lia.
zgo 0x2f038.
match goal with |- context [Z_to_bv 64 (usp + -400 + ?e)] => replace (usp + -400 + e) with (usp + -416) by lia end.
zstep.
match goal with |- context [Z_to_bv 64 (usp + -400 + - ?e)] => replace (usp + -400 + - e) with (usp + -4496) by lia end.
probe_store ST (usp + -4496).
zstep. rewrite (lts_ge_false' (usp + -416) (usp + -4496)) by lia. zstep.
zgo 0x2f048.
carve_frame 16%nat ST. destruct (rw_cells_CB_f32 rsegs _ _ 4%nat _ FR) as (ver & Lver & VER); clear FR.
pose proof (USPk _ _ IH (-416) ltac:(lia)) as USP416.

zstep. zstep. zstep. zstep.
pose proof (conj XR I) as XRS. pose proof (conj DR I) as DRS.
call (HCTL low ltac:(lia) OUT STEREO (a_low a) LBL CtlGetPiGain (usp + -400) lo).
{ exact DR. } { lia. } { exact I. } { eexists. split; [exact VPI| exact Lvpi]. } { cbn [creq_ptr_ok]. split; lia. } { rewrite USP416. lia. } { exact TP. }
{ intros bx Hx. apply RNG. apply in_app_iff. right. exact Hx. }
{ eapply X1n8.NoDup_map_app_r. exact ND. }
{ eapply lbd_apart_sub; [exact APB|]. intros bx Hx. apply in_app_iff. right. exact Hx. }
{ cbn [creq_size]. rewrite USP416. lia. }
{ intros bx Hx. cbn [creq_size]. pose proof (lay_lbl_ceil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY bx Hx). lia. }
{ rewrite USP416. exact ST. } { exact Tlo. }
{ rewrite USP416. assert (CD3 : ctl_depth low <= 128) by (clear -DD DK2; destruct low as [?|? [?|? [?|? ?]]]; cbn in DD |- *; lia). lia. }
{ exact MI. } { exact FRM. } { reflexivity. } { reflexivity. } { reflexivity. }
cbv beta. clear FRM. name_post.
match goal with H : creq_post _ _ _ _ _ |- _ => cbn [creq_post] in H; destruct H as (vpi1 & VPI1 & Lvpi1); nsegs VPI1 end.
match goal with H : EXCREADY _ _ _ -> _ |- _ => rename H into XRI end.
destruct XRS as [XR0 _]. pose proof (XRI XR0) as XR1. clear XRI XR0. destruct DRS as [DR0 _]. clear DR0.
rewrite USP416 in STc.

zstep. zstep. fix_mi. zstep. zstep. zstep.
pose proof (conj XR1 I) as XRS.
set (low4 := snd (speex_decoder_ctl low CtlGetPiGain)) in *.
call (HCTL low4 ltac:(subst low4; rewrite ctl_keeps_depth; lia) OUT STEREO (a_low a) LBL CtlGetExc (usp + -416) lo).
{ exact DRc. } { subst low4; rewrite ctl_keeps_depth; lia. } { exact I. }
{ split; [| exact XR1]. eexists. split; [exact VER| exact Lver]. } { cbn [creq_ptr_ok]. split; lia. } { rewrite USP416. lia. } { exact TP. }
{ intros bx Hx. apply RNG. apply in_app_iff. right. exact Hx. }
{ eapply X1n8.NoDup_map_app_r. exact ND. }
{ eapply lbd_apart_sub; [exact APB|]. intros bx Hx. apply in_app_iff. right. exact Hx. }
{ cbn [creq_size]. rewrite USP416. lia. }
{ intros bx Hx. cbn [creq_size]. pose proof (lay_lbl_ceil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY bx Hx). lia. }
{ rewrite USP416. exact STc. } { exact Tlo. }
{ rewrite USP416. assert (CD3 : ctl_depth low4 <= 128).
{ assert (DD4 : dec_depth low4 = x_dk X) by (subst low4; rewrite ctl_keeps_depth; exact DD).
clear -DD4 DK2. destruct low4 as [?|? [?|? [?|? ?]]]; cbn in DD4 |- *; lia. } lia. }
{ exact MI. } { exact FRMc. } { reflexivity. } { reflexivity. } { reflexivity. }
cbv beta. clear FRMc. try clear STc. name_post.
match goal with H : creq_post _ _ _ _ _ |- _ => cbn [creq_post] in H; destruct H as (ver1 & VER1 & Lver1); nsegs VER1 end.
match goal with H : EXCREADY _ _ _ -> _ |- _ => rename H into XRI end.
destruct XRS as [XR0 _]. pose proof (XRI XR0) as XR2. clear XRI XR0.
rewrite USP416 in STc.
apply evt_done. unfold at_V1.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). exists vpi1, ver1.
split; [reflexivity|]. split; [exact FRMc|].
split. { subst low4. close_ctx MU. }
split; [exact STc|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
feqs. assumption.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

#[using="Type"] Lemma f32_snoc1' : forall segs m A' done v, rw_cells segs m A' (f32 done ++ [C4 v]) -> rw_cells segs m A' (f32 (done ++ [v])).
Proof. intros segs m A' done v H. rewrite f32_app, f32_cons, f32_nil. exact H. Qed.

Definition at_V2 (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (b : bits_st bptr) (r : smrec) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xa0 xa1 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe) (vpi ver vq viq : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -480)) gp tp (Z_to_bv 64 OUT) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
xa0 xa1 (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (Z_to_bv 64 (sbmode_struct mo)) (Z_to_bv 64 8)
(Z_to_bv 64 (usp + -448)) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 A)
(Z_to_bv 64 (sbmode_struct mo)) cs8 cs9 cs10 cs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2f198) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -480) /\ frame_at X m fr
/\ f_0 fr = Z_to_bv 64 (usp + -384) /\ f_16 fr = Z_to_bv 64 (sbmode_struct mo) /\ f_32 fr = Z_to_bv 64 (usp + -416)
/\ f_40 fr = Z_to_bv 64 4 /\ f_104 fr = Z_to_bv 64 (usp + -480) /\ f_112 fr = Z_to_bv 64 4 /\ f_120 fr = Z_to_bv 64 (usp + -400)
/\ f_128 fr = Z_to_bv 64 OUT /\ f_144 fr = Z_to_bv 64 (18446744073709551615 - (usp + -448)) /\ f_152 fr = Z_to_bv 64 32
/\ f_160 fr = Z_to_bv 64 A /\ f_176 fr = Z_to_bv 64 (usp + -448) /\ f_184 fr = Z_to_bv 64 0 /\ f_208 fr = Z_to_bv 64 1
/\ f_dtx fr = Z_to_bv 64 dtx /\ (dtx = 0 \/ dtx = 1)
/\ sb_smrec_at mo (sbd_submodeID s1) = Some r
/\ rw_cells rsegs m (usp + -400) (f32 vpi) /\ length vpi = 4%nat
/\ rw_cells rsegs m (usp + -416) (f32 ver) /\ length ver = 4%nat
/\ rw_cells rsegs m (usp + -448) (f32 vq) /\ length vq = 8%nat
/\ rw_cells rsegs m (usp + -480) (f32 viq) /\ length viq = 8%nat.

#[using="RCEIL k IH"] Lemma sbV2 : forall low dtx s1 b r ms, at_V1 low dtx s1 b r ms ->
evt rsegs (at_V2 low dtx s1 (lsp_bits LspUnquantHigh b) r) ms.
Proof.
intros low dtx s1 b r ms AT.
first [ sf_destruct 34%nat AT as Fx fc m kk xra xa0 j ows stb fr vpi ver -> FRM CTX ST FRA F0eq F16 F32 F40 F112 F120 F128 F160 F184 F208 Fdtx DTX01 SAT VPI Lvpi VER Lver | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & j & ows & stb & fr & vpi & ver & -> & FRM & CTX & ST & FRA & F0eq & F16 & F32 & F40 & F112 & F120 & F128 & F160 & F184 & F208 & Fdtx & DTX01 & SAT & VPI & Lvpi & VER & Lver) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as _ _ _ _ Inb1 Ilpc1 Ifi1 _ _ _ Iid1 _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & Inb1 & Ilpc1 & Ifi1 & _ & _ & _ & Iid1 & _) ].
pose proof INV0 as (Imo & _). pose proof (subp_ok mo Imo) as (SPr & SPal).

zstep. rewrite Ilpc1. rewrite (sx32_lit 8) by lia.
zgo 0x2f08c.
match goal with |- context [Z_to_bv 64 (usp + -416 + ?e)] => replace (usp + -416 + e) with (usp + -448) by lia end.
zstep.
match goal with |- context [Z_to_bv 64 (usp + -416 + - ?e)] => replace (usp + -416 + - e) with (usp + -4512) by lia end.
probe_store ST (usp + -4512).
zstep. rewrite (lts_ge_false' (usp + -448) (usp + -4512)) by lia. zstep.
zgo 0x2f0a0.
carve_frame 32%nat ST. destruct (rw_cells_CB_f32 rsegs _ _ 8%nat _ FR) as (vq & Lvq & VQ); clear FR.
zgo 0x2f0a8.
match goal with |- context [Z_to_bv 64 (usp + -448 + ?e)] => replace (usp + -448 + e) with (usp + -480) by lia end.
zstep.
match goal with |- context [Z_to_bv 64 (usp + -448 + - ?e)] => replace (usp + -448 + - e) with (usp + -4544) by lia end.
probe_store ST (usp + -4544).
zstep. rewrite (lts_ge_false' (usp + -480) (usp + -4544)) by lia. zstep.
zgo 0x2f0bc.
carve_frame 32%nat ST. destruct (rw_cells_CB_f32 rsegs _ _ 8%nat _ FR) as (viq & Lviq & VIQ); clear FR.
pose proof (USPk _ _ IH (-480) ltac:(lia)) as USP480.

set (id := sbd_submodeID s1) in *.
first [ pose proof (sb_smrec_at_some mo id r SAT) as sfP_; sf_destruct 6%nat sfP_ as INr SMS Hid SPE LSPH _ | sf_fb; destruct (sb_smrec_at_some mo id r SAT) as (INr & SMS & Hid & SPE & LSPH & _) ].
pose proof (sb_smrecs_ptr r INr) as (RLO & RHI & RAL). unfold RTABLES_LO, RTABLES_HI in RLO, RHI.
zgo 0x2f0c4. rewrite (sx32_lit id) by lia. rewrite Emo.
zgo 0x2f0c8. rewrite (Z.shiftl_mul_pow2 id 3) by lia. change (2 ^ 3) with 8.
zgo 0x2f0cc. replace (SUBP mo + id * 8) with (SUBP mo + 8 * id) in * by lia.
zgo 0x2f0f8.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (sb_sub_ptr_read mm mo id _ (sb_tables_of_pristine mm TP) Imo ltac:(lia) eq_refl) as RD;
pose proof (sb_tables_of_pristine mm TP) as sfP_; first [ sf_destruct 8%nat sfP_ as _ _ TR _ _ _ TG _ | sf_fb; destruct sfP_ as (_ & _ & TR & _ & _ & _ & TG & _) ] end.
zstep. clear RD. rewrite SPE.
zgo 0x2f108.
pose proof (TR r INr) as SMC. unfold smrec_cells in SMC. cbv zeta in SMC. rewrite LSPH in SMC. cbn [lsp_entry] in SMC.
zstep. clear SMC TR.
zgo 0x2f118. zstep.
replace (ret_pc (Z_to_bv 64 A_lsp_unquant_high)) with (Z_to_bv 64 A_lsp_unquant_high) by (unfold A_lsp_unquant_high; symmetry; apply ret_pc_even; [lia| reflexivity]).
rewrite F160.
call ((h_lspq _ (ih_hyps _ _ IH)) A D b (usp + -448) vq lo);
[ exact REP | exact BOK | exact TG | exact VQ | exact Lvq
| rewrite USP480; exact ST | rewrite USP480; unfold LSPQ_DEPTH; lia | unfold NB_GLOBALS_TOP; lia
| unfold NB_GLOBALS_TOP; lia | unfold NB_GLOBALS_TOP; lia
| rewrite USP480; cbn [lsp_order]; unfold apart; lia
| rewrite USP480; unfold apart, BITS_SIZEOF; pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP480, BSZ; unfold apart; lia
| cbn [lsp_order]; unfold apart, BITS_SIZEOF; pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| cbn [lsp_order]; rewrite BSZ; unfold apart; lia
| reflexivity | reflexivity | reflexivity | exact MI | exact FRM | lia | lia | ].
after_bits REP (lsp_bits LspUnquantHigh b). cbv beta delta [callR]. clear FRM TG. name_post. rewrite USP480 in STc.
try clear VQ; try clear Lvq.
match goal with H : rw_cells _ _ (usp + -448) (f32 ?w), L : length ?w = _ |- _ => rename H into VQ; rename L into Lvq; rename w into vq1 end.
match goal with H : bits_ok (lsp_bits _ b) |- _ => rename H into BOK1 end.
change (Z.to_nat (lsp_order LspUnquantHigh)) with 8%nat in Lvq.
pose proof (lsp_bits_same LspUnquantHigh b) as (LBsz & LBo & LBc).
pose proof (ih_range _ _ IH (sbd_old_qlsp s0, a_oq a, 32)) as ROQ.
specialize (ROQ ltac:(apply in_app_iff; left; unfold sb_blocks; cbn; tauto)). unfold rblock_range in ROQ. cbn [blk_addr blk_size fst snd] in ROQ.
destruct ROQ as (ROQ0 & ROQal & _ & ROQc & _).
zgo 0x2f134.
rewrite F128, F16. rewrite (sx32_lit (sbd_first s1)) by lia. rewrite Ilpc1. rewrite (sx32_lit 8) by lia.
try rewrite (zb_lxor_ones (usp + -448)) in FL by lia. try rewrite (zb_lxor_ones (usp + -448)) by lia.
zstep. rewrite (eqb_zero_lit (sbd_first s1)) by lia.
if_cases Kfi; zify_bool Kfi.
{
apply evt_done. unfold at_V2.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). exists vpi, ver, vq1, viq.
split; [reflexivity|]. split; [exact FRMc|].
split. { close_ctx MU. }
split; [exact STc|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
feqs. assumption. }
destruct vq1 as [|q0 [|q1 [|q2 [|q3 [|q4 [|q5 [|q6 [|q7 [|? ?]]]]]]]]]; cbn in Lvq; try lia. rewrite !f32_cons, f32_nil in VQ.
destruct (sj_oq j) as [|o0 [|o1 [|o2 [|o3 [|o4 [|o5 [|o6 [|o7 [|? ?]]]]]]]]] eqn:EOQ; cbn in Loq; try lia. rewrite !f32_cons, f32_nil in BOQ.
vgo 0x2f198.
match type of BOQ with rw_cells _ _ _ [C4 ?w0; C4 ?w1; C4 ?w2; C4 ?w3; C4 ?w4; C4 ?w5; C4 ?w6; C4 ?w7] =>
assert (BOQ1 : rw_cells rsegs m (a_oq a) (f32 [w0; w1; w2; w3; w4; w5; w6; w7])) by (rewrite !f32_cons, f32_nil; exact BOQ);
set (oq1 := [w0; w1; w2; w3; w4; w5; w6; w7]) in BOQ1 end.
assert (VQ1 : rw_cells rsegs m (usp + -448) (f32 [q0; q1; q2; q3; q4; q5; q6; q7])) by (rewrite !f32_cons, f32_nil; exact VQ).
assert (Lvq1 : length [q0; q1; q2; q3; q4; q5; q6; q7] = 8%nat) by reflexivity.
clear BOQ VQ.
apply evt_done. unfold at_V2.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _.
first [ unshelve sf_eexists 3%nat; [ exact (SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) (sj_exc j) oq1 (sj_iq j) (sj_msp j) (sj_pg j) (sj_er j)) | exact (ows) | exact (stb) | ] | sf_fb; exists (SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) (sj_exc j) oq1 (sj_iq j) (sj_msp j) (sj_pg j) (sj_er j)), ows, stb ].
eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). exists vpi, ver, [q0; q1; q2; q3; q4; q5; q6; q7], viq.
split; [reflexivity|]. split; [exact FRMc|].
split. { close_ctx MU. }
split; [exact STc|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
feqs. assumption.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.
End Seg.
