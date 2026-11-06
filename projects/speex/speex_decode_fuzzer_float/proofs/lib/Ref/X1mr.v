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
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7 X1n8 X1ho X1hm X1hu X1ht X1ih X1nr X1mc X1mv X1mb X1ma X1mw X1mt.
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

Ltac probe_store ST e :=
let HS := fresh "HS" in
lazymatch type of ST with stk ?segs ?m ?lo ?hi =>
unshelve epose proof (stk_store_ok m lo hi e 8%nat ST _ _) as HS; [lia | lia |] end;
step; change (Z_to_le_bytes 8 0) with (le8 (Z_to_bv 64 0)); store_done.

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
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe) (vpi ver : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -336)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
(Z_to_bv 64 0) (c_a1 kk) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
(Z_to_bv 64 (usp + -320)) (Z_to_bv 64 A) (Z_to_bv 64 OUT) cs5 (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0))
(Z_to_bv 64 (sbmode_struct mo)) (Z_to_bv 64 (usp + -336)) (Z_to_bv 64 0) cs10 cs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x28240) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -336) /\ frame_at X m fr /\ f_0 fr = Z_to_bv 64 (usp + -304)
/\ f_dtx fr = Z_to_bv 64 dtx /\ (dtx = 0 \/ dtx = 1)
/\ sb_smrec_at mo (sbd_submodeID s1) = Some r
/\ rw_cells rsegs m (usp + -320) (f32 vpi) /\ length vpi = 4%nat
/\ rw_cells rsegs m (usp + -336) (f32 ver) /\ length ver = 4%nat.

#[using="Type"] Lemma f32_snoc1' : forall segs m A' done v, rw_cells segs m A' (f32 done ++ [C4 v]) -> rw_cells segs m A' (f32 (done ++ [v])).
Proof. intros segs m A' done v H. rewrite f32_app, f32_cons, f32_nil. exact H. Qed.

#[using="RCEIL k IH"] Lemma sbV1 : forall low dtx s1 b r ms, at_V X low dtx s1 b r ms ->
evt rsegs (at_V1 (snd (speex_decoder_ctl (snd (speex_decoder_ctl low CtlGetPiGain)) CtlGetExc)) dtx s1 b r) ms.
Proof.
intros low dtx s1 b r ms AT.
first [ sf_destruct 18%nat AT as Fx fc m kk xra j ows stb fr -> FRM CTX ST FRA F0eq Fdtx DTX01 SAT | sf_fb; destruct AT as (Fx & fc & m & kk & xra & j & ows & stb & fr & -> & FRM & CTX & ST & FRA & F0eq & Fdtx & DTX01 & SAT) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ _ _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & Inb1 & Ilpc1 & _) ].
pose proof (ih_nodup _ _ IH) as ND. pose proof (ih_apart _ _ IH) as APB. pose proof (ih_range _ _ IH) as RNG.
pose proof (ih_dk _ _ IH) as [DK1 DK2].

zstep.

zstep. rewrite Inb1. rewrite (zx32_small 4) by lia. zstep. zstep. zstep. zstep.
match goal with |- context [Z_to_bv 64 (usp + -304 + ?e)] => replace (usp + -304 + e) with (usp + -320) by lia end.

zstep. zstep.
match goal with |- context [Z_to_bv 64 (usp + -304 + ?e)] => replace (usp + -304 + e) with (usp + -4400) by lia end.
probe_store ST (usp + -4400).
zstep. rewrite (lts_ge_false' (usp + -320) (usp + -4400)) by lia. zstep.
carve_frame 16%nat ST. destruct (rw_cells_CB_f32 rsegs _ _ 4%nat _ FR) as (vpi & Lvpi & VPI); clear FR.

zstep. rewrite Inb1. rewrite (zx32_small 4) by lia. zstep. zstep. zstep. zstep.
match goal with |- context [Z_to_bv 64 (usp + -320 + ?e)] => replace (usp + -320 + e) with (usp + -336) by lia end.
zstep. zstep.
match goal with |- context [Z_to_bv 64 (usp + -320 + ?e)] => replace (usp + -320 + e) with (usp + -4416) by lia end.
probe_store ST (usp + -4416).
zstep. rewrite (lts_ge_false' (usp + -336) (usp + -4416)) by lia. zstep.
carve_frame 16%nat ST. destruct (rw_cells_CB_f32 rsegs _ _ 4%nat _ FR) as (ver & Lver & VER); clear FR.
pose proof (USPk _ _ IH (-336) ltac:(lia)) as USP336.

zstep. zstep. zstep. zstep.
pose proof (conj XR I) as XRS. pose proof (conj DR I) as DRS.
call (HCTL low ltac:(lia) OUT STEREO (a_low a) LBL CtlGetPiGain (usp + -320) lo).
{ exact DR. } { lia. } { exact I. } { eexists. split; [exact VPI| exact Lvpi]. } { exact TP. }
{ intros bx Hx. apply RNG. apply in_app_iff. right. exact Hx. }
{ eapply X1n8.NoDup_map_app_r. exact ND. }
{ eapply lbd_apart_sub; [exact APB|]. intros bx Hx. apply in_app_iff. right. exact Hx. }
{ cbn [creq_size]. rewrite USP336. lia. }
{ intros bx Hx. cbn [creq_size]. pose proof (lay_lbl_ceil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY bx Hx). lia. }
{ rewrite USP336. exact ST. } { exact Tlo. }
{ rewrite USP336. assert (CD3 : ctl_depth low <= 128) by (clear -DD DK2; destruct low as [?|? [?|? [?|? ?]]]; cbn in DD |- *; lia). lia. }
{ exact MI. } { exact FRM. } { reflexivity. } { reflexivity. } { reflexivity. }
cbv beta. clear FRM. name_post.
match goal with H : creq_post _ _ _ _ _ |- _ => cbn [creq_post] in H; destruct H as (vpi1 & VPI1 & Lvpi1); nsegs VPI1 end.
match goal with H : EXCREADY _ _ _ -> _ |- _ => rename H into XRI end.
destruct XRS as [XR0 _]. pose proof (XRI XR0) as XR1. clear XRI XR0. destruct DRS as [DR0 _]. clear DR0.
rewrite USP336 in STc.

zstep. zstep. zstep. zstep.
pose proof (conj XR1 I) as XRS.
set (low4 := snd (speex_decoder_ctl low CtlGetPiGain)) in *.
call (HCTL low4 ltac:(subst low4; rewrite ctl_keeps_depth; lia) OUT STEREO (a_low a) LBL CtlGetExc (usp + -336) lo).
{ exact DRc. } { subst low4; rewrite ctl_keeps_depth; lia. } { exact I. }
{ split; [| exact XR1]. eexists. split; [exact VER| exact Lver]. } { exact TP. }
{ intros bx Hx. apply RNG. apply in_app_iff. right. exact Hx. }
{ eapply X1n8.NoDup_map_app_r. exact ND. }
{ eapply lbd_apart_sub; [exact APB|]. intros bx Hx. apply in_app_iff. right. exact Hx. }
{ cbn [creq_size]. rewrite USP336. lia. }
{ intros bx Hx. cbn [creq_size]. pose proof (lay_lbl_ceil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY bx Hx). lia. }
{ rewrite USP336. exact STc. } { exact Tlo. }
{ rewrite USP336. assert (CD3 : ctl_depth low4 <= 128).
{ assert (DD4 : dec_depth low4 = x_dk X) by (subst low4; rewrite ctl_keeps_depth; exact DD).
clear -DD4 DK2. destruct low4 as [?|? [?|? [?|? ?]]]; cbn in DD4 |- *; lia. } lia. }
{ exact MI. } { exact FRMc. } { reflexivity. } { reflexivity. } { reflexivity. }
cbv beta. clear FRMc. try clear STc. name_post.
match goal with H : creq_post _ _ _ _ _ |- _ => cbn [creq_post] in H; destruct H as (ver1 & VER1 & Lver1); nsegs VER1 end.
match goal with H : EXCREADY _ _ _ -> _ |- _ => rename H into XRI end.
destruct XRS as [XR0 _]. pose proof (XRI XR0) as XR2. clear XRI XR0.
rewrite USP336 in STc.
apply evt_done. unfold at_V1.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). exists vpi1, ver1.
split; [reflexivity|]. split; [exact FRMc|].
split. { subst low4. close_ctx MU. }
split; [exact STc|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
split; [reflexivity|]. split; [exact Fdtx|]. split; [exact DTX01|]. split; [exact SAT|].
split; [exact VPI1|]. split; [exact Lvpi1|]. split; [exact VER1| exact Lver1].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition cpoq_post (PD PS E : Z) (n : nat) (xra xsp xs0 xs1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
(fc : bv 32) (m : mem) : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (m' : mem) (dws sws : list word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 a0 (Z_to_bv 64 E) (Z_to_bv 64 E) (Z_to_bv 64 (PS + 4 * Z.of_nat n)) a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x282e4) fc None m' (seg_rom rsegs)
/\ munch [(PD, E)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' PD (f32 dws) /\ length dws = n /\ rw_cells rsegs m' PS (f32 sws) /\ length sws = n.

#[using="Type"] Lemma cpoq_loop : forall (PD PS E : Z) (n : nat) (xra xsp xs0 xs1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
(fc : bv 32) (mN : mem) rest done sdone q r F m,
(length done + length rest + 1 = n)%nat -> length sdone = length done ->
q = PD + 4 * Z.of_nat (length done) -> r = PS + 4 * Z.of_nat (length done) -> E = PD + 4 * Z.of_nat n ->
E < 2^64 -> PS + 4 * Z.of_nat n < 2^64 -> apart PD (4 * Z.of_nat n) PS (4 * Z.of_nat n) ->
mem_inv rsegs m -> munch [(PD, E)] mN m -> wmono rsegs mN m ->
rw_cells rsegs m PD (f32 done) -> (exists x rest', rest' = rest /\ rw_cells rsegs m q (f32 (x :: rest'))) ->
rw_cells rsegs m PS (f32 sdone) -> (exists y srest, length srest = length rest /\ rw_cells rsegs m r (f32 (y :: srest))) ->
evt rsegs (cpoq_post PD PS E n xra xsp xs0 xs1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 fc mN)
(MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 a0 (Z_to_bv 64 q) (Z_to_bv 64 E) (Z_to_bv 64 r) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x282d0) fc None m (seg_rom rsegs)).
Proof.
intros PD PS E n xra xsp xs0 xs1 a0 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 fc mN.
induction rest as [|x' rest IHr]; intros done sdone q r F m HL HSL Hq Hr HE E64 S64 AP MI MU WM DONE sfH_; first [ sf_destruct 4%nat sfH_ as x rest' -> XR | sf_fb; destruct sfH_ as (x & rest' & -> & XR) ]; intros SDONE sfH2_; first [ sf_destruct 4%nat sfH2_ as y srest HLs YR | sf_fb; destruct sfH2_ as (y & srest & HLs & YR) ];
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ YR) as BY; rewrite cells_size_f32 in BY; cbn [length] in BY;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
pose proof (rw_cells_bound _ _ _ _ SDONE) as BS; rewrite cells_size_f32 in BS; cbn [length] in HL;
unfold apart in AP;
rewrite !f32_cons, ?f32_nil in XR; rewrite !f32_cons in YR.
- destruct srest; [| cbn in HLs; lia]. rewrite f32_nil in YR.
zstep. zstep. zstep. zstep. zstep. if_false_x.
replace (q + 4) with E by lia. replace (r + 4) with (PS + 4 * Z.of_nat n) by lia.
unfold cpoq_post. finish.
+ chunk_snoc DONE XR. apply f32_snoc1' in DONE. exact DONE.
+ rewrite length_app. cbn [length]. lia.
+ chunk_snoc SDONE YR. apply f32_snoc1' in SDONE. exact SDONE.
+ rewrite length_app. cbn [length]. lia.
- destruct srest as [|y' srest]; [cbn in HLs; lia|]. cbn [length] in HLs.
zstep. zstep. zstep. zstep. zstep. if_true_x.
chunk_uncons XR as X1. chunk_snoc DONE X1. apply f32_snoc1' in DONE.
chunk_uncons YR as Y1. chunk_snoc SDONE Y1. apply f32_snoc1' in SDONE.
eapply (IHr (done ++ [_]) (sdone ++ [_]) (q + 4) (r + 4)); try eassumption.
+ rewrite length_app. cbn [length] in *. lia.
+ rewrite !length_app. cbn [length]. lia.
+ rewrite length_app. cbn [length]. lia.
+ rewrite length_app. cbn [length]. lia.
+ sf_eexists 2%nat. split; [reflexivity|]. rewrite f32_cons. exact XR.
+ sf_eexists 2%nat. split; [| rewrite f32_cons; exact YR]. cbn [length] in HLs. lia.
Qed.

Definition at_V2 (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (b : bits_st bptr) (r : smrec) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe) (vpi ver vq viq : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -400)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
(Z_to_bv 64 8) (c_a1 kk) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
(Z_to_bv 64 (usp + -320)) (Z_to_bv 64 A) (Z_to_bv 64 OUT) (Z_to_bv 64 (usp + -368)) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0))
(Z_to_bv 64 (sbmode_struct mo)) (Z_to_bv 64 (usp + -336)) (Z_to_bv 64 0) (Z_to_bv 64 (usp + -400)) cs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x282e4) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -400) /\ frame_at X m fr /\ f_0 fr = Z_to_bv 64 (usp + -304)
/\ f_dtx fr = Z_to_bv 64 dtx /\ (dtx = 0 \/ dtx = 1)
/\ sb_smrec_at mo (sbd_submodeID s1) = Some r
/\ rw_cells rsegs m (usp + -320) (f32 vpi) /\ length vpi = 4%nat
/\ rw_cells rsegs m (usp + -336) (f32 ver) /\ length ver = 4%nat
/\ rw_cells rsegs m (usp + -368) (f32 vq) /\ length vq = 8%nat
/\ rw_cells rsegs m (usp + -400) (f32 viq) /\ length viq = 8%nat.

#[using="RCEIL k IH"] Lemma sbV2 : forall low dtx s1 b r ms, at_V1 low dtx s1 b r ms ->
evt rsegs (at_V2 low dtx s1 (lsp_bits LspUnquantHigh b) r) ms.
Proof.
intros low dtx s1 b r ms AT.
first [ sf_destruct 24%nat AT as Fx fc m kk xra j ows stb fr vpi ver -> FRM CTX ST FRA F0eq Fdtx DTX01 SAT VPI Lvpi VER Lver | sf_fb; destruct AT as (Fx & fc & m & kk & xra & j & ows & stb & fr & vpi & ver & -> & FRM & CTX & ST & FRA & F0eq & Fdtx & DTX01 & SAT & VPI & Lvpi & VER & Lver) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as _ _ _ _ Inb1 Ilpc1 Ifi1 _ _ _ Iid1 _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & Inb1 & Ilpc1 & Ifi1 & _ & _ & _ & Iid1 & _) ].
pose proof INV0 as (Imo & _).

zstep. rewrite Ilpc1. rewrite (sx32_lit 8) by lia. zstep. zstep. zstep. zstep. zstep.
match goal with |- context [Z_to_bv 64 (usp + -336 + ?e)] => replace (usp + -336 + e) with (usp + -368) by lia end.

zstep. zstep.
match goal with |- context [Z_to_bv 64 (usp + -336 + ?e)] => replace (usp + -336 + e) with (usp + -4432) by lia end.
probe_store ST (usp + -4432).
zstep. rewrite (lts_ge_false' (usp + -368) (usp + -4432)) by lia. zstep.
carve_frame 32%nat ST. destruct (rw_cells_CB_f32 rsegs _ _ 8%nat _ FR) as (vq & Lvq & VQ); clear FR.

zstep.
match goal with |- context [Z_to_bv 64 (usp + -368 + ?e)] => replace (usp + -368 + e) with (usp + -400) by lia end.
zstep. zstep.
match goal with |- context [Z_to_bv 64 (usp + -368 + ?e)] => replace (usp + -368 + e) with (usp + -4464) by lia end.
probe_store ST (usp + -4464).
zstep. rewrite (lts_ge_false' (usp + -400) (usp + -4464)) by lia. zstep.
carve_frame 32%nat ST. destruct (rw_cells_CB_f32 rsegs _ _ 8%nat _ FR) as (viq & Lviq & VIQ); clear FR.
pose proof (USPk _ _ IH (-400) ltac:(lia)) as USP400.

set (id := sbd_submodeID s1) in *.
first [ pose proof (sb_smrec_at_some mo id r SAT) as sfP_; sf_destruct 6%nat sfP_ as INr SMS Hid SPE LSPH _ | sf_fb; destruct (sb_smrec_at_some mo id r SAT) as (INr & SMS & Hid & SPE & LSPH & _) ].
zstep. rewrite (sx32_lit id) by lia. zstep. rewrite Emo. zstep. zstep.
rewrite (Z.shiftl_mul_pow2 id 3) by lia. change (2 ^ 3) with 8.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (sb_sub_ptr_read mm mo id _ (sb_tables_of_pristine mm TP) Imo ltac:(lia) eq_refl) as RD;
pose proof (sb_tables_of_pristine mm TP) as sfP_; first [ sf_destruct 8%nat sfP_ as _ _ TR _ _ _ TG _ | sf_fb; destruct sfP_ as (_ & _ & TR & _ & _ & _ & TG & _) ] end.
replace (SUBP mo + id * 8) with (SUBP mo + 8 * id) by lia.
zstep. clear RD. rewrite SPE.
pose proof (TR r INr) as SMC. unfold smrec_cells in SMC. cbv zeta in SMC. rewrite LSPH in SMC. cbn [lsp_entry] in SMC.
zstep. clear SMC TR.

zstep. zstep. zstep.
replace (ret_pc (Z_to_bv 64 A_lsp_unquant_high)) with (Z_to_bv 64 A_lsp_unquant_high) by (unfold A_lsp_unquant_high; symmetry; apply ret_pc_even; [lia| reflexivity]).
call ((h_lspq _ (ih_hyps _ _ IH)) A D b (usp + -368) vq lo);
[ exact REP | exact BOK | exact TG | exact VQ | exact Lvq
| rewrite USP400; exact ST | rewrite USP400; unfold LSPQ_DEPTH; lia | unfold NB_GLOBALS_TOP; lia
| unfold NB_GLOBALS_TOP; lia | unfold NB_GLOBALS_TOP; lia
| rewrite USP400; cbn [lsp_order]; unfold apart; lia
| rewrite USP400; unfold apart, BITS_SIZEOF; pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP400, BSZ; unfold apart; lia
| cbn [lsp_order]; unfold apart, BITS_SIZEOF; pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| cbn [lsp_order]; rewrite BSZ; unfold apart; lia
| reflexivity | reflexivity | reflexivity | exact MI | exact FRM | ].
after_bits REP (lsp_bits LspUnquantHigh b). cbv beta delta [callR]. clear FRM TG. name_post. rewrite USP400 in STc.
try clear VQ; try clear Lvq.
match goal with H : rw_cells _ _ (usp + -368) (f32 ?w), L : length ?w = _ |- _ => rename H into VQ; rename L into Lvq; rename w into vq1 end.
match goal with H : bits_ok (lsp_bits _ b) |- _ => rename H into BOK1 end.
change (Z.to_nat (lsp_order LspUnquantHigh)) with 8%nat in Lvq.
pose proof (lsp_bits_same LspUnquantHigh b) as (LBsz & LBo & LBc).

zstep. rewrite Ilpc1. rewrite (sx32_lit 8) by lia. zstep. rewrite (sx32_lit (sbd_first s1)) by lia. zstep. zstep. zstep.
rewrite (eqb_zero_lit (sbd_first s1)) by lia.

assert (CLOSE : forall (Fx1 : bvmap 5 word) (fc0 : bv 32) (m1 : mem) (xra1 y0 y1 y2 xa1 xa2 xa3 y4 y5 y6 y7 y8 y9 y10 y11 : word) (j1 : sb_junk),
frm0 fc0 ->
sbctx X true m1 s1 low (lsp_bits LspUnquantHigh b) j1 ows stb ->
stk rsegs m1 lo (usp + -400) -> frame_at X m1 fr ->
rw_cells rsegs m1 (usp + -320) (f32 vpi) -> rw_cells rsegs m1 (usp + -336) (f32 ver) ->
(exists vq2, rw_cells rsegs m1 (usp + -368) (f32 vq2) /\ length vq2 = 8%nat) -> rw_cells rsegs m1 (usp + -400) (f32 viq) ->
at_V2 low dtx s1 (lsp_bits LspUnquantHigh b) r
(MS (mkR xra1 (Z_to_bv 64 (usp + -400)) gp tp y0 y1 y2 sp (Z_to_bv 64 S)
(Z_to_bv 64 8) xa1 xa2 xa3 y4 y5 y6 y7
(Z_to_bv 64 (usp + -320)) (Z_to_bv 64 A) (Z_to_bv 64 OUT) (Z_to_bv 64 (usp + -368)) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0))
(Z_to_bv 64 (sbmode_struct mo)) (Z_to_bv 64 (usp + -336)) (Z_to_bv 64 0) (Z_to_bv 64 (usp + -400)) cs11 y8 y9 y10 y11)
Fx1 (Z_to_bv 64 0x282e4) fc0 None m1 (seg_rom rsegs))).
{ intros Fx1 fc0 m1 xra1 y0 y1 y2 xa1 xa2 xa3 y4 y5 y6 y7 y8 y9 y10 y11 j1 FRM0 CTX1 ST1 FRA1 VPI1 VER1 (vq2 & VQ2 & Lvq2) VIQ1. unfold at_V2.
eexists _, _, _, (ICL y0 y1 y2 xa1 xa2 xa3 y4 y5 y6 y7 y8 y9 y10 y11), _. first [ unshelve sf_eexists 8%nat; [ exact (j1) | exact (ows) | exact (stb) | exact (fr) | exact (vpi) | exact (ver) | exact (vq2) | exact (viq) | ] | sf_fb; exists j1, ows, stb, fr, vpi, ver, vq2, viq ].
split; [reflexivity|]. split; [exact FRM0|]. split; [exact CTX1|]. split; [exact ST1|]. split; [exact FRA1|].
split; [exact F0eq|]. split; [exact Fdtx|]. split; [exact DTX01|]. split; [exact SAT|].
split; [exact VPI1|]. split; [exact Lvpi|]. split; [exact VER1|]. split; [exact Lver|].
split; [exact VQ2|]. split; [exact Lvq2|]. split; [exact VIQ1| exact Lviq]. }
if_cases Kfi; zify_bool Kfi.
{
apply evt_done.
eapply CLOSE; [ eassumption | | exact STc | split; [exact FL| exact FV] | exact VPI | exact VER | exists vq1; split; [exact VQ| exact Lvq] | exact VIQ ].
close_ctx MU. }

zstep. rewrite (lts_zero_lit 8) by lia. if_false_x.
zstep. zstep. zstep. zstep.
destruct vq1 as [|q0 vq1']; [cbn in Lvq; lia|].
pose proof (rw_cells_bound _ _ _ _ BOQ) as BBOQ. rewrite cells_size_f32, Loq in BBOQ.
destruct (sj_oq j) as [|o0 oq'] eqn:EOQ; [cbn in Loq; lia|].
eapply evt_cut.
{ eapply (cpoq_loop (a_oq a) (usp + -368) (a_oq a + 32) 8%nat) with (done := []) (sdone := []) (rest := oq') (mN := _);
[ cbn [length]; cbn [length] in Loq; lia | reflexivity | cbn [length]; lia | cbn [length]; lia | cbn; lia | lia | lia
| unfold apart; lia | exact MI | apply munch_refl | apply wmono_refl
| apply rw_cells_nil; lia | sf_eexists 2%nat; split; [reflexivity| exact BOQ]
| apply rw_cells_nil; lia | sf_eexists 2%nat; split; [| exact VQ]; cbn [length] in Lvq, Loq |- *; lia ]. }
lazymatch type of MI with mem_inv _ ?mm => post_call rsegs mm end.
rename MI0 into MI.
match goal with H : rw_cells _ _ (a_oq a) (f32 ?w), L : length ?w = 8%nat |- _ => rename H into BOQ'; rename L into Loq'; rename w into oq1 end.
match goal with H : rw_cells _ _ (usp + -368) (f32 ?w), L : length ?w = 8%nat |- _ => rename H into VQ'; rename L into Lvq'; rename w into vq2 end.
apply evt_done.
eapply CLOSE with (j1 := SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) (sj_exc j) oq1 (sj_iq j) (sj_msp j) (sj_pg j) (sj_er j));
[ eassumption | | exact STc | split; [exact FL| exact FV] | exact VPI | exact VER | exists vq2; split; [exact VQ'| exact Lvq'] | exact VIQ ].
close_ctx MU.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.
End Seg.
