(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma X1mw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma lxor_sgn_nn : forall y, 0 <= y < 2^63 -> Z.lxor y 9223372036854775808 = y + 9223372036854775808.
Proof. intros y Hy. change 9223372036854775808 with (2^63). apply zb_lxor_pow2_small; lia. Qed.
Ltac ub_chk := rewrite ?lxor_sgn_nn by lia; if_false_z.
Ltac zto p := repeat lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => tryif constr_eq q p then fail else zstep end.
Ltac fix_mi := repeat match goal with H : mem_inv ?sg ?mm |- evt ?sg0 _ _ => tryif constr_eq sg sg0 then fail else change (mem_inv sg0 mm) in H end.
Ltac zgo p := repeat lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => tryif constr_eq q p then fail else (fix_mi; lstep; zsimp)
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ub_chk
end.
Ltac feqs := repeat (split; [cbn [f_0 f_8 f_16 f_24 f_32 f_40 f_48 f_56 f_64 f_72 f_80 f_88 f_96 f_104 f_112 f_120 f_128 f_136 f_144
f_152 f_160 f_168 f_176 f_184 f_192 f_200 f_208 f_216 f_224 f_dtx]; first [reflexivity | assumption]|]).

Local Notation MODEP mo := (sb_mode_ptr NB_MODE_PTR A_speex_wb_mode A_speex_uwb_mode mo).
Local Notation SUBP mo := (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR mo).

Lemma mode_struct_read : forall m mo a, sb_tables m -> (mo = ModeWB \/ mo = ModeUWB) -> a = wa (MODEP mo) ->
ov_read_bytes rsegs m a 8 = Some (le8 (Z_to_bv 64 (sbmode_struct mo))).
Proof.
intros m mo a sfH_; first [ sf_destruct 10%nat sfH_ as _ _ _ _ _ _ _ TW TU _ | sf_fb; destruct sfH_ as (_ & _ & _ & _ & _ & _ & _ & TW & TU & _) ]; intros Hmo ->.
destruct Hmo as [-> | ->]; cbn [sb_mode_ptr sbmode_struct].
- change (Some _) with (Some (cbytes (C8 (Z_to_bv 64 A_sb_wb_mode)))).
eapply (rw_cells_read_at rsegs m A_speex_wb_mode _ 0%nat (C8 (Z_to_bv 64 A_sb_wb_mode)) 8); [exact TW| reflexivity| reflexivity| unfold wa; f_equal; lia].
- change (Some _) with (Some (cbytes (C8 (Z_to_bv 64 A_sb_uwb_mode)))).
eapply (rw_cells_read_at rsegs m A_speex_uwb_mode _ 0%nat (C8 (Z_to_bv 64 A_sb_uwb_mode)) 8); [exact TU| reflexivity| reflexivity| unfold wa; f_equal; lia].
Qed.

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

Definition pro_post (j : sb_junk) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
fun ms' => exists (fr : sframe) (m' : mem),
ms' = MS (mkR ra0 (Z_to_bv 64 (usp + -384)) gp tp t0 t1 t2 sp (Z_to_bv 64 S)
(Z_to_bv 64 (a_low a)) (Z_to_bv 64 104) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0))
a3 (Z_to_bv 64 1) a5 a6 a7 (Z_to_bv 64 OUT) cs3 (Z_to_bv 64 0) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0))
cs6 (Z_to_bv 64 (sbmode_struct mo)) cs8 cs9 cs10 cs11 t3 t4 t5 t6)
F0 (Z_to_bv 64 0x2ee8c) fc None m' (seg_rom rsegs)
/\ munch [(usp + -384, usp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (usp + -384)
/\ frame_at X m' fr /\ f_0 fr = Z_to_bv 64 0 /\ f_160 fr = Z_to_bv 64 A /\ f_208 fr = Z_to_bv 64 1
/\ rw_cells rsegs m' S (sbp_hdr s0 a)
/\ rw_cells rsegs m' (S + 40) (sbp_ptrs s0 a OUT).

Lemma modep_ok : forall mo', (mo' = ModeWB \/ mo' = ModeUWB) -> 0 < MODEP mo' < 2^63 /\ MODEP mo' mod 8 = 0.
Proof. intros mo' [-> | ->]; vm_compute; repeat split; reflexivity. Qed.

#[using="RCEIL k IH"] Lemma sbP_pro : forall (j : sb_junk) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (m : mem),
rw_cells rsegs m S (sbp_hdr s0 a) -> rw_cells rsegs m (S + 40) (sbp_ptrs s0 a OUT) -> rtables_pristine m ->
stk rsegs m lo usp -> mem_inv rsegs m ->
evt rsegs (pro_post j t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc m)
(MS (mkR ra0 sp gp tp t0 t1 t2 cs0 cs1 (Z_to_bv 64 S) (Z_to_bv 64 A) (Z_to_bv 64 OUT) a3 a4 a5 a6 a7 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3 t4 t5 t6)
F0 (Z_to_bv 64 A_sb_decode) fc None m (seg_rom rsegs)).
Proof.
intros j t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc m P0 P2 TP STK MI.
unfold A_sb_decode. open_ihyps IH.
pose proof INV0 as sfP_; first [ sf_destruct 12%nat sfP_ as Imo Ifs Iffs IFS Inb Ilpc Ifi Isr Ien Ies Iid Iis | sf_fb; destruct sfP_ as (Imo & Ifs & Iffs & IFS & Inb & Ilpc & Ifi & Isr & Ien & Ies & Iid & Iis) ].
pose proof (modep_ok mo Imo) as (MPr & MPal).
unfold sbp_hdr in P0. unfold sbp_ptrs in P2.
pose proof (munch_refl [(usp + -384, usp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
zstep. carve_frame 384%nat STK.
apply (rw_cells_split_CB rsegs _ _ [] 384 _ _ [232;152]%nat) in FR; [|reflexivity]; cbn [mk_CB_cells app] in FR.
chunk_splitk FR at 1%nat as FL. rename FR into FV.
apply (rw_cells_split_CB rsegs _ _ [] 232 _ _ [224;8]%nat) in FL; [|reflexivity]; cbn [mk_CB_cells app] in FL.
chunk_splitk FL at 1%nat as FLa. rename FL into FLb.
destruct (rw_cells_CB_C8s rsegs _ _ 28%nat _ FLa) as (lw28 & Llw & FL); clear FLa.
destruct lw28 as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 [|w15
[|w16 [|w17 [|w18 [|w19 [|w20 [|w21 [|w22 [|w23 [|w24 [|w25 [|w26 [|w27 [|? ?]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; cbn in Llw; try lia. cbn [map] in FL.
destruct (rw_cells_CB_f32 rsegs _ _ 2%nat _ FLb) as (lp & Llp & FLb'); clear FLb.
destruct lp as [|p1 [|p2 [|? ?]]]; cbn in Llp; try lia. rewrite f32_cons, f32_cons, f32_nil in FLb'.
chunk_cat FL FLb'.
apply (rw_cells_split_CB rsegs _ _ [] 152 _ _ [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FV; [|reflexivity]; cbn [mk_CB_cells app] in FV.
repeat match type of FV with context [CB 8 ?bs] =>
lazymatch bs with
| firstn _ _ => let jj := fresh "jk" in remember bs as jj eqn:EJ in FV; clear EJ
| skipn _ _ => let jj := fresh "jk" in remember bs as jj eqn:EJ in FV; clear EJ
end end.
clear junk Llw Llp.

lstep.
zgo 0x2ee4c. rewrite (sx32_lit (sbd_frame_size s0)) by lia.
zgo 0x2ee50. rewrite (Z.shiftl_mul_pow2 (sbd_frame_size s0) 2) by lia. change (2 ^ 2) with 4.
zgo 0x2ee54. replace (OUT + sbd_frame_size s0 * 4) with (OUT + 4 * sbd_frame_size s0) by lia.
zgo 0x2ee80.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (mode_struct_read mm mo _ (sb_tables_of_pristine mm TP) Imo eq_refl) as RD1 end.
zstep. clear RD1.
zgo 0x2ee8c.
replace (Z.b2z (0 <? OUT)) with 1 in * by (replace (0 <? OUT) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
apply evt_done. unfold pro_post.
exists (SFR (Z_to_bv 64 0) w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 (Z_to_bv 64 A) w21 w22 w23 w24 w25 (Z_to_bv 64 1) w27 p1 p2). eexists.
split; [reflexivity|].
unfold frame_at, fr_saves, sframe_cells; cbv zeta;
cbn [f_0 f_8 f_16 f_24 f_32 f_40 f_48 f_56 f_64 f_72 f_80 f_88 f_96 f_104 f_112 f_120 f_128 f_136 f_144 f_152 f_160 f_168 f_176 f_184 f_192 f_200 f_208 f_216 f_224 f_dtx].
repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity.
Qed.

Definition at_DEC (low1 : dec_state bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra : word) (j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe),
ms = MS (mkR xra (Z_to_bv 64 (usp + -384)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
(Z_to_bv 64 (a_low a)) (Z_to_bv 64 A) (Z_to_bv 64 OUT) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
(Z_to_bv 64 OUT) cs3 (Z_to_bv 64 0) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 A)
(Z_to_bv 64 (sbmode_struct mo)) cs8 cs9 cs10 cs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2eea0) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X false m s0 low1 b0 j ows stb /\ stk rsegs m lo (usp + -384) /\ frame_at X m fr /\ f_0 fr = Z_to_bv 64 0
/\ f_160 fr = Z_to_bv 64 A /\ f_208 fr = Z_to_bv 64 1
/\ isave_ok low1.

Local Notation HCTL := (h_ctl _ (ih_hyps _ _ IH)).
Local Notation HCTLI := (h_ctli _ (ih_hyps _ _ IH)).

#[using="RCEIL k IH"] Lemma sbP1 : forall (OUTL : Z) (low0 : dec_state bptr) (j : sb_junk) (ows : list word) (stb : list byte)
(t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32),
sbctx0 X OUTL m0 s0 low0 b0 j ows stb -> stk rsegs m0 lo usp -> frm0 fc ->
evt rsegs (at_DEC (snd (speex_decoder_ctl low0 (CtlSetInnovationSave (sbd_frame_size s0)))))
(MS (mkR ra0 sp gp tp t0 t1 t2 cs0 cs1 (Z_to_bv 64 S) (Z_to_bv 64 A) (Z_to_bv 64 OUT) a3 a4 a5 a6 a7 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3 t4 t5 t6)
F0 (Z_to_bv 64 A_sb_decode) fc None m0 (seg_rom rsegs)).
Proof.
intros OUTL low0 j ows stb t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc CTX STK FRM.
open_ihyps IH. open_ctx CTX.
pose proof INV0 as sfP_; first [ sf_destruct 12%nat sfP_ as Imo Ifs Iffs IFS Inb Ilpc Ifi Isr Ien Ies Iid Iis | sf_fb; destruct sfP_ as (Imo & Ifs & Iffs & IFS & Inb & Ilpc & Ifi & Isr & Ien & Ies & Iid & Iis) ].
eapply evt_cut. { eapply (sbP_pro j); [exact P0 | exact P2 | exact TP | exact STK | exact MI]. }
cbv beta. intros ms1 sfH_; first [ sf_destruct 13%nat sfH_ as fr m1 -> MU1 WM1 MI1 ST1 FRA F0eq F160 F208 P0' P2' | sf_fb; destruct sfH_ as (fr & m1 & -> & MU1 & WM1 & MI1 & ST1 & FRA & F0eq & F160 & F208 & P0' & P2') ].
clear P0 P2. rename P0' into P0. rename P2' into P2. unfold sbp_hdr in P0. unfold sbp_ptrs in P2.
lazymatch type of MU1 with munch _ ?ma ?mb => transport_after_call rsegs ma mb MU1 WM1 end.
clear MU1 WM1. try clear MI. rename MI1 into MI.
destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV. rewrite F160 in FL.

pose proof (ih_dk _ _ IH) as [DK1 DK2].
zstep. clear XR.
pose proof (ih_nodup _ _ IH) as ND. pose proof (ih_apart _ _ IH) as APB. pose proof (ih_range _ _ IH) as RNG.
pose proof (conj DR I) as DRS.
call (HCTLI low0 ltac:((clear - DK2 DK1 DD low0 X k; lia)) OUTL OUT STEREO (a_low a) LBL (sbd_frame_size s0) (OUT + 4 * sbd_frame_size s0) lo).
{ exact DR. }
{ lia. }
{ cbn. lia. }
{ exact TP. }
{ intros x Hx. apply RNG. apply in_app_iff. right. exact Hx. }
{ eapply X1n8.NoDup_map_app_r. exact ND. }
{ eapply lbd_apart_sub; [exact APB|]. intros x Hx. apply in_app_iff. right. exact Hx. }
{ cbn [creq_size]. rewrite USP384. pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY). lia. }
{ intros x Hx. cbn [creq_size]. pose proof (lay_lbl_ceil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY x Hx). lia. }
{ rewrite USP384. exact ST1. }
{ exact Tlo. }
{ rewrite USP384. pose proof (ih_dk _ _ IH) as [_ D2].
assert (CD3 : ctl_depth low0 <= 128) by (clear -DD D2; destruct low0 as [?|? [?|? [?|? ?]]]; cbn in DD |- *; lia). lia. }
{ exact MI. }
{ exact FRM. }
{ reflexivity. }
{ reflexivity. }
{ reflexivity. }
cbv beta. rename MI0 into MI. rename PC into FRM1. rename PC0 into ST2. rename PC1 into DR1. clear PC2 POST.
destruct DRS as [DR0 _].
rewrite USP384 in ST2.

zstep. zstep. zstep. zstep.
apply evt_done. unfold at_DEC.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM1|].
split. { close_ctx MU. all: match goal with |- ?G => idtac "CTXLEFT:" G end. all: fail. }
split; [exact ST2|]. split; [unfold frame_at, fr_saves; cbv zeta; split; [exact FL | exact FV]|]. split; [cbn [f_0]; exact F0eq|].
split; [cbn [f_160]; first [reflexivity | exact F160]|]. split; [cbn [f_208]; first [reflexivity | exact F208]|].
rewrite Hfs. replace (4 * FS) with (sbm_frameSize mo) by (destruct Imo as [E|E]; rewrite E in *; cbn; pose proof INV0 as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ EFS _ | sf_fb; destruct sfP_ as (_ & _ & _ & EFS & _) ]; rewrite EFS, E; reflexivity).
eapply isave_ok_after_set; [exact DR0| exact Imo| exact NM].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition at_RET (r : Z * dec_state bptr * bits_st bptr) : machine_state -> Prop :=
fun ms => let '(ret, low2, b1) := r in
exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe),
ms = MS (mkR (Z_to_bv 64 0x2eea4) (Z_to_bv 64 (usp + -384)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
(Z_to_bv 64 ret) (c_a1 kk) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
(Z_to_bv 64 OUT) cs3 (Z_to_bv 64 0) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 A)
(Z_to_bv 64 (sbmode_struct mo)) cs8 cs9 cs10 cs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2eea4) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s0 low2 b1 j ows stb /\ stk rsegs m lo (usp + -384) /\ frame_at X m fr /\ f_0 fr = Z_to_bv 64 0
/\ f_160 fr = Z_to_bv 64 A /\ f_208 fr = Z_to_bv 64 1
/\ -2 <= ret <= 0.

Local Notation HNAT := (h_native _ (ih_hyps _ _ IH)).
Local Notation unpackM := (@bits_unpack_unsigned_M PState bptr).
Local Notation peekM := (@bits_peek_M PState bptr).
Local Notation advanceM := (@bits_advance_M PState bptr).
Local Notation remainingM := (@bits_remaining_M PState bptr).

#[using="Type"] Lemma rdec_layout_lower : forall BITS OUTx ST lox u u', rdec_layout BITS OUTx ST lox u -> u' <= u -> rdec_layout BITS OUTx ST lox u'.
Proof. intros BITS OUTx ST lox u u' L Hu. unfold rdec_layout, apart in *. lia. Qed.

#[using="RCEIL k IH"] Lemma sbP_dec : forall low1 ms, at_DEC low1 ms ->
implM rsegs (speex_decode io_notify unpackM peekM advanceM remainingM low1 b0 0) st
(fun r st' ms' => st' = st /\ at_RET r ms') ms.
Proof.
intros low1 ms AT.
first [ sf_destruct 18%nat AT as Fx fc m kk xra j ows stb fr -> FRM CTX ST FRA F0eq F160 F208 ISOK | sf_fb; destruct AT as (Fx & fc & m & kk & xra & j & ows & stb & fr & -> & FRM & CTX & ST & FRA & F0eq & F160 & F208 & ISOK) ].
open_ihyps IH. open_ctx CTX. clear XR. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof (ih_nodup _ _ IH) as ND. pose proof (ih_apart _ _ IH) as APB. pose proof (ih_range _ _ IH) as RNG.
pose proof (ih_dk _ _ IH) as [DK1 DK2].

apply implM_from_evt. zstep. apply evt_done.
pose proof (f32_as_u8arr _ _ _ XO) as [XOU LOU]. rewrite Lows in LOU.
eapply (implM_mono rsegs).
{ eapply (HNAT low1 ltac:(lia)) with (lo := lo) (canary := canary) (LBD := LBL) (Dc := D) (STEREO := STEREO) (OUT := OUT) (stb := stb) (outb := cells_bytes (f32 ows));
try reflexivity.
- exact DR.
- lia.
- exact ISOK.
- exact NST.
- eapply X1n8.NoDup_map_app_r. exact ND.
- eapply lbd_apart_sub; [exact APB|]. intros x Hx. apply in_app_iff. right. exact Hx.
- intros x Hx. apply RNG. apply in_app_iff. right. exact Hx.
- exact REP.
- exact BOK.
- exact (ih_owner _ _ IH).
- exact (ih_Drange _ _ IH).
- intros x Hx. apply (ih_Dapart _ _ IH). apply in_app_iff. right. exact Hx.
- exact XOU.
- rewrite LOU. reflexivity.
- exact (ih_out4 _ _ IH).
- exact XS.
- exact (ih_ster4 _ _ IH).
- exact TP.
- exact SE.
- exact SS.
- rewrite USP384. eapply rdec_layout_lower; [exact (ih_rlay _ _ IH)| lia].
- rewrite USP384. exact ST.
- rewrite USP384, (ih_RDd _ _ IH low1 DD). lia.
- rewrite USP384. lia.
- rewrite USP384. rewrite <- Z.add_mod_idemp_l, SP16 by lia. reflexivity.
- exact MI.
- exact FRM. }
cbv beta. intros r st' ms' POST. destruct r as [[ret low2] b1].
first [ sf_destruct 42%nat POST as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 F' fc' m' outb' stb' -> RET DDe DMe NST' FRM' MU' WM' MI' ST' DR' XR' REP' BOK' OWN' CHR' BSZ' XO' LO' XS' SE' SS' -> | sf_fb; destruct POST as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & F' & fc' & m' & outb' & stb' & -> & RET & DDe & DMe & NST' & FRM' & MU' & WM' & MI' & ST' & DR' & XR' & REP' & BOK' & OWN' & CHR' & BSZ' & XO' & LO' & XS' & SE' & SS' & ->) ].
split; [reflexivity|].
clear DR REP BOK XO XOU LOU XS SE SS ST.
rewrite USP384 in MU', ST'.
lazymatch type of MU' with munch _ ?ma ?mb => transport_after_call rsegs ma mb MU' WM' end.
clear MU' WM'. try clear MI. rename MI' into MI.
destruct (u8arr_as_f32 m' OUT outb' 2000%nat XO' ltac:(unfold HOUT_BYTES in LO'; lia)) as (ows' & Lows' & XO2).
unfold at_RET.
replace (ret_pc (Z_to_bv 64 0x2eea4)) with (Z_to_bv 64 0x2eea4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
eexists F', fc', m', (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), j, ows', stb', fr.
split; [reflexivity|]. split; [exact FRM'|].
split. { close_ctx MU. all: match goal with |- ?G => idtac "CTXLEFT:" G end. all: fail. }
split; [exact ST'|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
split; [exact F0eq|]. split; [exact F160|]. split; [exact F208|]. exact RET.
Qed.

Definition at_X (ret : Z) (s : sbd_state bptr) (low : dec_state bptr) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xsp xa0 xs1 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe),
ms = MS (mkR xra xsp gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp xs1 xa0 (c_a1 kk) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
xs2 (Z_to_bv 64 ret) xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2fb90) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s low b j ows stb /\ stk rsegs m lo (usp + -384) /\ frame_at X m fr /\ -2 <= ret <= 0.

Definition at_W (low : dec_state bptr) (dtx : Z) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xa0 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe),
ms = MS (mkR xra (Z_to_bv 64 (usp + -384)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
xa0 (c_a1 kk) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
(Z_to_bv 64 OUT) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 A)
(Z_to_bv 64 (sbmode_struct mo)) cs8 cs9 cs10 cs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2eedc) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s0 low b j ows stb /\ stk rsegs m lo (usp + -384) /\ frame_at X m fr /\ f_0 fr = Z_to_bv 64 0
/\ f_16 fr = Z_to_bv 64 (sbmode_struct mo) /\ f_128 fr = Z_to_bv 64 OUT /\ f_160 fr = Z_to_bv 64 A /\ f_184 fr = Z_to_bv 64 0
/\ f_208 fr = Z_to_bv 64 1
/\ f_dtx fr = Z_to_bv 64 dtx /\ (dtx = 0 \/ dtx = 1).

Definition QP2 (ret : Z) (low2 : dec_state bptr) (b1 : bits_st bptr) : machine_state -> Prop :=
let '(dtx, low3) := speex_decoder_ctl low2 CtlGetDtxStatus in
if ret =? 0 then at_W low3 dtx b1 else at_X ret s0 low3 b1.

#[using="RCEIL k IH"] Lemma sbP2 : forall ret low2 b1 ms, at_RET (ret, low2, b1) ms -> evt rsegs (QP2 ret low2 b1) ms.
Proof.
intros ret low2 b1 ms AT.
first [ sf_destruct 17%nat AT as Fx fc m kk j ows stb fr -> FRM CTX ST FRA F0eq F160 F208 RET | sf_fb; destruct AT as (Fx & fc & m & kk & j & ows & stb & fr & -> & FRM & CTX & ST & FRA & F0eq & F160 & F208 & RET) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof (ih_nodup _ _ IH) as ND. pose proof (ih_apart _ _ IH) as APB. pose proof (ih_range _ _ IH) as RNG.
pose proof (ih_dk _ _ IH) as [DK1 DK2].

zstep. zstep. zstep. zstep. zstep. zstep.
chunk_splitk FL at 29%nat as FLa.
pose proof (conj XR I) as XRS. rename FL into FLd. rename FLa into FL.
call (HCTL low2 ltac:((clear - DK2 DK1 DD low2 X k; lia)) OUT STEREO (a_low a) LBL CtlGetDtxStatus (usp + -156) lo).
{ exact DR. }
{ lia. }
{ exact I. }
{ eexists. exact FLd. }
{ cbn [creq_ptr_ok]. split; lia. }
{ rewrite USP384. lia. }
{ exact TP. }
{ intros x Hx. apply RNG. apply in_app_iff. right. exact Hx. }
{ eapply X1n8.NoDup_map_app_r. exact ND. }
{ eapply lbd_apart_sub; [exact APB|]. intros x Hx. apply in_app_iff. right. exact Hx. }
{ cbn [creq_size]. rewrite USP384. lia. }
{ intros x Hx. cbn [creq_size]. pose proof (lay_lbl_ceil _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY x Hx). lia. }
{ rewrite USP384. exact ST. }
{ exact Tlo. }
{ rewrite USP384.
assert (CD3 : ctl_depth low2 <= 128) by (clear -DD DK2; destruct low2 as [?|? [?|? [?|? ?]]]; cbn in DD |- *; lia). lia. }
{ exact MI. }
{ exact FRM. }
{ reflexivity. }
{ reflexivity. }
{ reflexivity. }
cbv beta. clear FRM. name_post. rename FRMc into FRM1. rename STc into ST2. rename DRc into DR1.
match goal with H : creq_post _ _ _ _ _ |- _ => cbn [creq_post] in H; destruct H as [FLd' DTX01]; nsegs FLd' end.
match goal with H : EXCREADY _ _ _ -> _ |- _ => rename H into XRI end.
destruct XRS as [XR0 _]. pose proof (XRI XR0) as XR1. clear XRI XR0.
rewrite USP384 in ST2.
chunk_cat FL FLd'.

zstep. unfold QP2. destruct (speex_decoder_ctl low2 CtlGetDtxStatus) as [dtx low3] eqn:ECTL. cbn [fst snd] in *.
assert (DD3 : dec_depth low3 = x_dk X) by (rewrite <- DD, <- (ctl_keeps_depth low2 CtlGetDtxStatus), ECTL; reflexivity).
assert (NM3 : dec_mode low3 = sbm_nb_mode mo) by (rewrite <- NM, <- (ctl_keeps_mode low2 CtlGetDtxStatus), ECTL; reflexivity).
assert (NST3 : dec_nested low3) by (pose proof (ctl_keeps_nested low2 CtlGetDtxStatus NST) as NN; rewrite ECTL in NN; exact NN).
if_cases Kret; zify_cond Kret; pose proof (land64_zero_iff ret ltac:((clear - RET ret; lia))) as KZ.
-
replace (ret =? 0) with false by (symmetry; apply Z.eqb_neq; tauto).
apply evt_done. unfold at_X.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _). sf_eexists 13%nat. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM1|].
split. { close_ctx MU. }
split; [exact ST2|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|]. exact RET.
-
assert (Eret : ret = 0) by tauto. rewrite Eret. rewrite Z.eqb_refl. subst ret.
zgo 0x2eed0.
pose proof INV0 as sfP_; first [ sf_destruct 11%nat sfP_ as _ _ _ _ _ _ _ _ _ Ies _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ies & _) ].
zgo 0x2eed4. rewrite Ies. zgo 0x2eedc.
apply evt_done. unfold at_W.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM1|].
split. { close_ctx MU. }
split; [exact ST2|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
do 6 (split; [cbn [f_0 f_16 f_128 f_160 f_184 f_208]; first [reflexivity | assumption]|]).
split; [reflexivity| exact DTX01].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.
End Seg.
