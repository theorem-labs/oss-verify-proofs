(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma X1mw X1mr X1ms.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
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

Ltac close_ctxE EFS MU := unfold sbctx, sbWX, SBSTATE_SIZEOF, BITS_SIZEOF, HOUT_BYTES; rewrite ?EFS; repeat match goal with |- _ /\ _ => split end; first [close_goal MU | congruence].
Local Ltac ub_chk := rewrite ?lxor_sign_nn by lia; if_false_z.
Local Ltac fix_mi := repeat match goal with H : mem_inv ?sg ?mm |- evt ?sg0 _ _ => tryif constr_eq sg sg0 then fail else change (mem_inv sg0 mm) in H end.
Local Ltac zgo p := repeat lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => tryif constr_eq q p then fail else (fix_mi; lstep; zsimp)
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ub_chk
end.

Definition lframe (fr : sframe) (dtx : Z) : Prop :=
f_0 fr = Z_to_bv 64 (usp + -384) /\ f_8 fr = Z_to_bv 64 0 /\ f_16 fr = Z_to_bv 64 (sbmode_struct mo)
/\ f_24 fr = Z_to_bv 64 (18446744073709551615 - (usp + -416)) /\ f_32 fr = Z_to_bv 64 (usp + -416) /\ f_40 fr = Z_to_bv 64 4
/\ f_56 fr = Z_to_bv 64 2147483647 /\ f_64 fr = Z_to_bv 64 32 /\ f_72 fr = Z_to_bv 64 (18446744073709551615 - (usp + -400))
/\ f_80 fr = Z_to_bv 64 (usp + -508) /\ f_88 fr = Z_to_bv 64 8 /\ f_96 fr = Z_to_bv 64 (S + 132)
/\ f_104 fr = Z_to_bv 64 (usp + -480) /\ f_112 fr = Z_to_bv 64 4 /\ f_120 fr = Z_to_bv 64 (usp + -400)
/\ f_128 fr = Z_to_bv 64 OUT /\ f_144 fr = Z_to_bv 64 (18446744073709551615 - (usp + -448)) /\ f_152 fr = Z_to_bv 64 32
/\ f_160 fr = Z_to_bv 64 A /\ f_176 fr = Z_to_bv 64 (usp + -448) /\ f_184 fr = Z_to_bv 64 0
/\ f_208 fr = Z_to_bv 64 1 /\ f_216 fr = Z_to_bv 64 4294967296 /\ f_dtx fr = Z_to_bv 64 dtx /\ (dtx = 0 \/ dtx = 1).

Definition at_L1_40 (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (r : smrec) (sub : Z) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xa0 xs9 xs11 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe) (vpi ver vq viq vak vexc : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -672)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
xa0 (c_a1 kk) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
(Z_to_bv 64 40) (Z_to_bv 64 (40 * sub)) (Z_to_bv 64 0x103bc) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 (18446744073709551615 - (usp + -512))) (Z_to_bv 64 160)
(Z_to_bv 64 (usp + -672)) xs9 (Z_to_bv 64 (usp + -512)) xs11
(c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2f47c) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -672) /\ frame_at X m fr
/\ lframe fr dtx /\ f_136 fr = Z_to_bv 64 (usp + -512) /\ f_168 fr = Z_to_bv 64 (OUT + 640 + 160 * sub)
/\ f_192 fr = Z_to_bv 64 (sub * 4) /\ f_200 fr = Z_to_bv 64 sub
/\ sb_smrec_at mo (sbd_submodeID s1) = Some r /\ 0 <= sub <= 3
/\ (xs9 = match sbd_innov_save s0 with None => Z_to_bv 64 0 | Some _ => Z_to_bv 64 (OUT + 1280 + 320 * sub) end)
/\ rw_cells rsegs m (usp + -400) (f32 vpi) /\ length vpi = 4%nat
/\ rw_cells rsegs m (usp + -416) (f32 ver) /\ length ver = 4%nat
/\ rw_cells rsegs m (usp + -448) (f32 vq) /\ length vq = 8%nat
/\ rw_cells rsegs m (usp + -480) (f32 viq) /\ length viq = 8%nat
/\ rw_cells rsegs m (usp + -512) (f32 vak) /\ length vak = 8%nat
/\ rw_cells rsegs m (usp + -672) (f32 vexc) /\ length vexc = 40%nat.

Local Ltac nrm := repeat match goal with
| H : ?f ?fr = Z_to_bv 64 _ |- context [?f ?fr] => lazymatch type of fr with sframe => rewrite H end
| H : sbd_subframeSize ?s = _ |- context [sbd_subframeSize ?s] => rewrite H
| H : sbd_frame_size ?s = _ |- context [sbd_frame_size ?s] => rewrite H
| H : sbd_nbSubframes ?s = _ |- context [sbd_nbSubframes ?s] => rewrite H
| H : sbd_lpcSize ?s = _ |- context [sbd_lpcSize ?s] => rewrite H
| |- context [sx32 (Z_to_bv 64 ?e)] => rewrite (sx32_lit e) by lia
| |- context [bv_swrap 32 ?e] => rewrite (swrap32_small e) by lia end.
Local Ltac zgo2 p := repeat lazymatch goal with
| |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => tryif constr_eq q p then fail else (fix_mi; lstep; zsimp; try nrm)
| |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => try nrm; first [ ub_chk | ub_dec ]
end.
#[using="RCEIL k IH"] Lemma sbL1_40 : FS = 40 -> forall low dtx s1 r sub b ms, at_L X low dtx s1 r sub b ms -> evt rsegs (at_L1_40 low dtx s1 r sub b) ms.
Proof.
intros EFS low dtx s1 r sub b ms AT.
first [ sf_destruct 64%nat AT as Fx fc m kk xra xa0 xs2 xs3 xs4 xs7 xs8 xs9 xs11 j ows stb fr vpi ver vq viq vak -> FRM CTX ST FRA F0e F8e F16e F24e F32e F40e F56e F64e F72e F80e F88e F96e F104e F112e F120e F128e F144e F152e F160e F176e F184e F208e F216e Fdtx DTX01 SAT Hsub VPI Lvpi VER Lver VQ Lvq VIQ Lviq VAK Lvak | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & xs2 & xs3 & xs4 & xs7 & xs8 & xs9 & xs11 & j & ows & stb & fr & vpi & ver & vq & viq & vak & -> & FRM & CTX & ST & FRA & F0e & F8e & F16e & F24e & F32e & F40e & F56e & F64e & F72e & F80e & F88e & F96e & F104e & F112e & F120e & F128e & F144e & F152e & F160e & F176e & F184e & F208e & F216e & Fdtx & DTX01 & SAT & Hsub & VPI & Lvpi & VER & Lver & VQ & Lvq & VIQ & Lviq & VAK & Lvak) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ Iffs1 _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & Iffs1 & _ & Inb1 & Ilpc1 & _) ].
assert (Hfs1 : sbd_frame_size s1 = 4 * FS) by (rewrite Efr; exact Hfs).
rewrite EFS in *.
pose proof INV0 as (Imo & _).
pose proof (ih_isave _ _ IH) as KK. rewrite EFS in KK.

zstep. zstep. zstep. zstep. zstep. zstep.
rewrite Efs. rewrite (sx32_lit 40) by lia. rewrite (swrap32_small (sub + 0)) by lia. replace (sub + 0) with sub by lia. rewrite (Z.land_ones sub 64) by lia. rewrite (Z.mod_small sub) by lia. rewrite (swrap32_small (40 * sub)) by lia. rewrite bv_eqb_same_k. cbn [negb]. cbv iota.
zgo2 193244.
match goal with |- context [Z_to_bv 64 (usp + -512 + ?e)] => replace (usp + -512 + e) with (usp + -4608) by lia end.
probe_store ST (usp + -4608).
zstep. replace (usp + -512 + - (160)) with (usp + -672) by lia. rewrite (lts_ge_false' (usp + -672) (usp + -4608)) by lia. zstep.
carve_frame 160%nat ST. change 160%nat with (4 * 40%nat)%nat in FR. destruct (rw_cells_CB_f32 rsegs _ _ 40%nat _ FR) as (vexc & Lvexc & VEXC); clear FR.
pose proof (USPk _ _ IH (-672) ltac:(lia)) as USPX.
zgo2 193260. zstep.
unfold sb_isave_ptr. rewrite Eis.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(OUT, OUT + 8000)] mm) as MUJ; pose proof (wmono_refl rsegs mm) as WMJ end.

lazymatch type of MUJ with munch _ ?MMM _ =>
eapply (evt_cut rsegs (fun ms1 => exists (Fx1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem) (y0 y1 y2 ya0 ya1 ya2 y3 y4 y5 y6 y7 y8 y9 y10 y11 xra1 xs9' : word) (ows1 : list word),
ms1 = MS (mkR xra1 (Z_to_bv 64 (usp + -672)) gp tp y0 y1 y2 sp (Z_to_bv 64 S)
ya0 ya1 ya2 y3 y4 y5 y6 y7
(Z_to_bv 64 40) (Z_to_bv 64 (40 * sub)) xs4 (Z_to_bv 64 (OUT + 640)) (Z_to_bv 64 (18446744073709551615 - (usp + -512))) (Z_to_bv 64 160)
(Z_to_bv 64 (usp + -672)) xs9' (Z_to_bv 64 (usp + -512)) xs11 y8 y9 y10 y11)
Fx1 (Z_to_bv 64 0x2f340) fc1 None m1 (seg_rom rsegs)
/\ frm0 fc1 /\ mem_inv rsegs m1 /\ munch [(OUT, OUT + 8000)] MMM m1 /\ wmono rsegs MMM m1
/\ rw_cells rsegs m1 OUT (f32 ows1) /\ length ows1 = 2000%nat
/\ (xs9' = match sbd_innov_save s0 with None => Z_to_bv 64 0 | Some _ => Z_to_bv 64 (OUT + 1280 + 320 * sub) end))) end.
{ destruct (sbd_innov_save s0) as [kk0|] eqn:EISV.
- subst kk0. replace (OUT + 4 * (8 * 40)) with (OUT + 1280) by lia. if_false_x.
zgo2 193332. zstep.
match goal with |- context [Z_to_bv 64 (OUT + 1280 + 40 * sub * 8)] => replace (OUT + 1280 + 40 * sub * 8) with (OUT + 1280 + 320 * sub) by lia end.
pose proof (f32_split rsegs _ _ ows (Z.to_nat (320 + 80 * sub)) ltac:(rewrite Lows; lia) XO) as [XO1 XO2].
pose proof (f32_split rsegs _ _ (skipn (Z.to_nat (320 + 80 * sub)) ows) 80%nat ltac:(rewrite length_skipn, Lows; lia) XO2) as [XO2a XO3]. clear XO2.
replace (OUT + 4 * Z.of_nat (Z.to_nat (320 + 80 * sub)) + 4 * Z.of_nat 80%nat) with (OUT + 1280 + 320 * sub + 320) in XO3 by lia.
replace (OUT + 4 * Z.of_nat (Z.to_nat (320 + 80 * sub))) with (OUT + 1280 + 320 * sub) in XO2a by lia.
set (owsA := firstn (Z.to_nat (320 + 80 * sub)) ows) in *.
assert (LA : Z.of_nat (length owsA) = 320 + 80 * sub) by (subst owsA; rewrite length_firstn, Lows; lia).
set (owsC := skipn 80%nat (skipn (Z.to_nat (320 + 80 * sub)) ows)) in *.
assert (LC : Z.of_nat (length owsC) = 2000 - 80 - (320 + 80 * sub)) by (subst owsC; rewrite !length_skipn, Lows; lia).
pose proof (f32_as_blob _ _ _ 80%nat XO2a ltac:(rewrite length_firstn, length_skipn, Lows; lia)) as XB. clear XO2a XO.
replace (Z.to_nat (4 * Z.of_nat 80%nat)) with (Z.to_nat 320) in XB by lia.
clearbody owsA owsC.
remember (OUT + 1280 + 320 * sub) as ISV eqn:EISVA.
call (nmemset_specZ ISV 320 0); [exact XB | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | subst ISV; lia | ].
try clear XB. rename MI0 into MI.
match goal with H : rw_cells _ _ ISV [CB _ _] |- _ =>
change (Z.to_nat 320) with (4 * 80%nat)%nat in H at 1;
destruct (rw_cells_CB_f32 rsegs _ _ 80%nat _ H) as (zws & Lz & XO2); clear H end.
subst ISV.
pose proof (f32_join rsegs _ _ _ _ XO1 ltac:(replace (OUT + 4 * Z.of_nat (length owsA)) with (OUT + 1280 + 320 * sub) by lia; exact XO2)) as XO12.
pose proof (f32_join rsegs _ _ _ _ XO12 ltac:(rewrite length_app, Lz; replace (OUT + 4 * Z.of_nat (length owsA + 80%nat)) with (OUT + 1280 + 320 * sub + 320) by lia; exact XO3)) as XO.
clear XO1 XO12 XO2 XO3.
assert (LowsN : length ((owsA ++ zws) ++ owsC) = 2000%nat) by (rewrite !length_app, Lz; lia).
zstep.
apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ((owsA ++ zws) ++ owsC).
split; [reflexivity|]. split; [exact FRM|]. split; [exact MI|]. split; [exact MUJ|]. split; [exact WMJ|].
split; [exact XO|]. split; [exact LowsN| reflexivity].
- if_true. zstep.
apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ows.
split; [reflexivity|]. split; [exact FRM|]. split; [exact MI|]. split; [exact MUJ|]. split; [exact WMJ|].
split; [exact XO|]. split; [exact Lows| reflexivity]. }
cbv beta. intros ms1 sfH_; first [ sf_destruct 29%nat sfH_ as Fx1 fc1 m1 y0 y1 y2 ya0 ya1 ya2 y3 y4 y5 y6 y7 y8 y9 y10 y11 xra1 xs9' ows1 -> FRM1 MI1 MUJ' WMJ' XO1 Lows1 Exs9 | sf_fb; destruct sfH_ as (Fx1 & fc1 & m1 & y0 & y1 & y2 & ya0 & ya1 & ya2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & xra1 & xs9' & ows1 & -> & FRM1 & MI1 & MUJ' & WMJ' & XO1 & Lows1 & Exs9) ].
clear XO Lows. lazymatch type of MUJ' with munch _ ?ma ?mb => transport_after_call rsegs ma mb MUJ' WMJ' end.
clear MUJ' WMJ' MUJ WMJ. try clear MI. rename MI1 into MI. clear FRM. rename FRM1 into FRM. rename XO1 into XO. rename Lows1 into Lows. rename ows1 into ows'.
zgo2 193380. zstep.
pose proof (ih_range _ _ IH (sbd_old_qlsp s0, a_oq a, 32)) as ROQ.
specialize (ROQ ltac:(apply in_app_iff; left; unfold sb_blocks; cbn; tauto)). unfold rblock_range in ROQ. cbn [blk_addr blk_size fst snd] in ROQ.
call ((h_lspi _ (ih_hyps _ _ IH)) (a_oq a) (usp + -448) (usp + -480) sub lo (sj_oq j) vq viq); [ first [ assumption | reflexivity | (rewrite ?USPX; exact ST) | (rewrite ?USPX; unfold apart, LSPI_DEPTH, LSP2LPC_DEPTH, NB_GLOBALS_TOP in *; lia) ] .. | ].
cbv beta delta [callR]. clear FRM. try clear VIQ; try clear Lviq. name_post. rename FRMc into FRM. try rename STc into ST. try rewrite USPX in ST.
match goal with H : rw_cells _ _ (usp + -480) (f32 ?w), L : length ?w = 8%nat |- _ => rename H into VIQ; rename L into Lviq; rename w into viq1 end.
zgo2 193400. zstep.
call ((h_l2l _ (ih_hyps _ _ IH)) (usp + -480) (usp + -512) lo viq1 vak (Z_to_bv 64 0)); [ first [ assumption | reflexivity | (rewrite ?USPX; exact ST) | (rewrite ?USPX; unfold apart, LSPI_DEPTH, LSP2LPC_DEPTH, NB_GLOBALS_TOP in *; lia) ] .. | ].
cbv beta delta [callR]. clear FRM. try clear VAK; try clear Lvak. name_post. rename FRMc into FRM. try rename STc into ST. try rewrite USPX in ST.
match goal with H : rw_cells _ _ (usp + -512) (f32 ?w), L : length ?w = 8%nat |- _ => rename H into VAK; rename L into Lvak; rename w into vak1 end.
try rename MI0 into MI.
pose proof (ih_range _ _ IH (sbd_pi_gain s0, a_pg a, 16)) as RPG.
specialize (RPG ltac:(apply in_app_iff; left; unfold sb_blocks; cbn; tauto)). unfold rblock_range in RPG. cbn [blk_addr blk_size fst snd] in RPG.
zgo2 193464.
pose proof (f32_split rsegs _ _ (sj_pg j) (Z.to_nat sub) ltac:(rewrite Lpg; lia) BPG) as [QPG1 QPG2]. clear BPG.
replace (a_pg a + 4 * Z.of_nat (Z.to_nat sub)) with (a_pg a + sub * 4) in QPG2 by lia.
assert (LPG1 : Z.of_nat (length (firstn (Z.to_nat sub) (sj_pg j))) = sub) by (rewrite length_firstn, Lpg; lia).
destruct (skipn (Z.to_nat sub) (sj_pg j)) as [|pg0 pgrest] eqn:EPGR.
{ exfalso. pose proof (f_equal (@length _) EPGR) as LL. rewrite length_skipn, Lpg in LL. cbn in LL. lia. }
assert (LPGR : Z.of_nat (length pgrest) = 3 - sub).
{ pose proof (f_equal (@length _) EPGR) as LL. rewrite length_skipn, Lpg in LL. cbn in LL. lia. }
clear EPGR. set (pgdone := firstn (Z.to_nat sub) (sj_pg j)) in *. clearbody pgdone.
remember (a_pg a + sub * 4) as PGA eqn:EPGA.
pose proof (rw_cells_bound _ _ _ _ QPG2) as BQPG2. rewrite cells_size_f32 in BQPG2. cbn [length] in BQPG2. rewrite f32_cons in QPG2.
lstep.
destruct vak1 as [|k0 [|k1 [|k2 [|k3 [|k4 [|k5 [|k6 [|k7 [|kx krest]]]]]]]]]; try (cbn in Lvak; lia). rewrite !f32_cons, f32_nil in VAK.
zgo2 193576.
zgo2 193640.
pose proof (f32_split rsegs _ _ vpi (Z.to_nat sub) ltac:(rewrite Lvpi; lia) VPI) as [VPI1 VPI2]. clear VPI1.
replace (usp + -400 + 4 * Z.of_nat (Z.to_nat sub)) with (usp + -400 + sub * 4) in VPI2 by lia.
destruct (skipn (Z.to_nat sub) vpi) as [|pi0 pirest] eqn:EPIR.
{ exfalso. pose proof (f_equal (@length _) EPIR) as LL. rewrite length_skipn, Lvpi in LL. cbn in LL. lia. }
clear EPIR. remember (usp + -400 + sub * 4) as PIA eqn:EPIA. rewrite f32_cons in VPI2.
rewrite (Z.shiftl_mul_pow2 sub 2) by lia. change (2 ^ 2) with 4. replace (usp + -400 + sub * 4) with PIA by lia. zstep. clear VPI2. subst PIA.
zgo2 193656. zstep.
pose proof (f32_as_blob _ _ _ 40%nat VEXC Lvexc) as XB. clear VEXC.
replace (Z.to_nat (4 * Z.of_nat 40%nat)) with (Z.to_nat 160) in XB by lia.
call (nmemset_specZ (usp + -672) 160 0); [exact XB | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
try clear XB. try rename MI0 into MI.
match goal with H : rw_cells _ _ (usp + -672) [CB _ _] |- _ =>
change (Z.to_nat 160) with (4 * 40%nat)%nat in H at 1;
destruct (rw_cells_CB_f32 rsegs _ _ 40%nat _ H) as (zexc & Lzexc & VEXC); clear H end.
lazymatch type of QPG2 with rw_cells _ _ _ (C4 ?v :: f32 pgrest) =>
rewrite <- (f32_cons v pgrest) in QPG2;
pose proof (f32_join rsegs _ _ _ _ QPG1 ltac:(replace (a_pg a + 4 * Z.of_nat (length pgdone)) with PGA by lia; exact QPG2)) as BPG end.
lazymatch type of BPG with rw_cells _ _ _ (f32 ?pgl) => set (pgnew := pgl) in BPG end.
assert (Lpg' : length pgnew = 4%nat) by (subst pgnew; rewrite length_app; cbn [length]; lia). clearbody pgnew.
clear QPG1 QPG2. subst PGA.
replace (Z_to_bv 64 (OUT + 640)) with (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) by (f_equal; lia).
apply evt_done. unfold at_L1_40.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, xs9', _.
exists (SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) (sj_exc j) (sj_oq j) (sj_iq j) (sj_msp j) pgnew (sj_er j)).
exists ows', stb. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). first [ unshelve sf_eexists 6%nat; [ exact (vpi) | exact (ver) | exact (vq) | exact (viq1) | exact ([k0; k1; k2; k3; k4; k5; k6; k7]) | exact (zexc) | ] | sf_fb; exists vpi, ver, vq, viq1, [k0; k1; k2; k3; k4; k5; k6; k7], zexc ].
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctxE EFS MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
split. { unfold lframe. cbn [f_0 f_8 f_16 f_24 f_32 f_40 f_48 f_56 f_64 f_72 f_80 f_88 f_96 f_104 f_112 f_120 f_128 f_136 f_144 f_152 f_160 f_168 f_176 f_184 f_192 f_200 f_208 f_216 f_224 f_dtx].
repeat match goal with |- _ /\ _ => split end; first [ reflexivity | assumption | (f_equal; lia) | (f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; lia) ]. }
cbn [f_0 f_8 f_16 f_24 f_32 f_40 f_48 f_56 f_64 f_72 f_80 f_88 f_96 f_104 f_112 f_120 f_128 f_136 f_144 f_152 f_160 f_168 f_176 f_184 f_192 f_200 f_208 f_216 f_224 f_dtx]. do 4 (split; [first [ reflexivity | assumption | (f_equal; lia) | (f_equal; rewrite ?Z.shiftl_mul_pow2 by lia; lia) ]|]).
split; [exact SAT|]. split; [exact Hsub|]. split; [exact Exs9|].
split; [exact VPI|]. split; [exact Lvpi|]. split; [exact VER|]. split; [exact Lver|]. split; [exact VQ|]. split; [exact Lvq|].
split; [exact VIQ|]. split; [exact Lviq|]. split; [rewrite !f32_cons, f32_nil; exact VAK|]. split; [reflexivity|].
split; [exact VEXC| exact Lzexc].
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

End Seg.
