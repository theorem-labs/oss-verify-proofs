(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma X1mw X1mo X1mt.
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

Lemma f32_snoc1' : forall segs m A done v, rw_cells segs m A (f32 done ++ [C4 v]) -> rw_cells segs m A (f32 (done ++ [v])).
Proof. intros segs m A done v H. rewrite f32_app, f32_cons, f32_nil. exact H. Qed.

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

Local Ltac upto p := repeat (tryif ub_at_pc p then fail else (tryif ub_at_if then ub_dec else ub_step)).

Definition vs_post (B N : Z) (xra xsp xs0 xs1 v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (n : nat) (m : mem) : machine_state -> Prop :=
fun ms' => exists (m' : mem) (ws : list word) (w2 w4 w5 : word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 N) (Z_to_bv 64 B) w2 (Z_to_bv 64 N) w4 w5 v a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x2fc48) fc None m' (seg_rom rsegs)
/\ munch [(B + 4 * N, B + 8 * N)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (B + 4 * N) (f32 ws) /\ length ws = n.

#[using="Type"] Lemma vs_loop : forall (B N : Z) (n : nat) (xra xsp xs0 xs1 v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (mN : mem) rest done m (w2 w4 w5 : word),
(length done + length rest + 1 = n)%nat -> N = Z.of_nat n -> 2 * N < 2^31 -> 0 < B -> B mod 4 = 0 -> B + 8 * N <= 2^64 ->
mem_inv rsegs m -> munch [(B + 4 * N, B + 8 * N)] mN m -> wmono rsegs mN m ->
rw_cells rsegs m (B + 4 * N) (f32 done) ->
(exists x rest', rest' = rest /\ rw_cells rsegs m (B + 4 * N + 4 * Z.of_nat (length done)) (f32 (x :: rest'))) ->
evt rsegs (vs_post B N xra xsp xs0 xs1 v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 F fc n mN)
(MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 (Z.of_nat (length done))) (Z_to_bv 64 B) w2 (Z_to_bv 64 N) w4 w5 v a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x2fc00) fc None m (seg_rom rsegs)).
Proof.
intros B N n xra xsp xs0 xs1 v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 F fc mN.
induction rest as [|x' rest IHr]; intros done m w2 w4 w5 HL HN N31 B0 B4 B63 MI MU WM DONE sfH_;
first [ sf_destruct 4%nat sfH_ as x rest' -> XR | sf_fb; destruct sfH_ as (x & rest' & -> & XR) ];
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD; cbn [length] in HL;
rewrite !f32_cons, ?f32_nil in XR.
- upto 0x2fc40.
replace (B + (N + Z.of_nat (length done) + 0) * 4) with (B + 4 * N + 4 * Z.of_nat (length done)) by lia.
destruct (ex_intro (fun q => q = B + 4 * N + 4 * Z.of_nat (length done)) _ eq_refl) as [q Eq]. rewrite <- Eq in *.
zstep. subst q. rewrite (swrap32_small (Z.of_nat (length done) + 1)) by lia.
upto 0x2fc48.
replace (Z.of_nat (length done) + 1) with N by lia.
unfold vs_post. finish.
+ chunk_snoc DONE XR. apply f32_snoc1' in DONE. exact DONE.
+ rewrite length_app. cbn [length]. lia.
- upto 0x2fc40.
replace (B + (N + Z.of_nat (length done) + 0) * 4) with (B + 4 * N + 4 * Z.of_nat (length done)) by lia.
destruct (ex_intro (fun q => q = B + 4 * N + 4 * Z.of_nat (length done)) _ eq_refl) as [q Eq]. rewrite <- Eq in *.
zstep. subst q. rewrite (swrap32_small (Z.of_nat (length done) + 1)) by lia.
upto 0x2fc00.
chunk_uncons XR as X1. chunk_snoc DONE X1. apply f32_snoc1' in DONE.
replace (Z.of_nat (length done) + 1) with (Z.of_nat (length (done ++ [v]))) by (rewrite length_app; cbn [length]; lia).
match type of XR with rw_cells ?sg ?mm ?ad ?cs => replace ad with (B + 4 * N + 4 * Z.of_nat (length (done ++ [v]))) in XR by (rewrite length_app; cbn [length]; lia) end.
eapply (IHr (done ++ [_])); try eassumption.
+ rewrite length_app. cbn [length] in *. lia.
+ sf_eexists 2%nat. split; [reflexivity|]. rewrite f32_cons. exact XR.
Qed.

Ltac close_ctxE EFS MU := unfold sbctx, sbWX, SBSTATE_SIZEOF, BITS_SIZEOF, HOUT_BYTES; rewrite ?EFS; repeat match goal with |- _ /\ _ => split end; first [close_goal MU | congruence].

Definition at_N1 (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xa0 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe),
ms = MS (mkR xra (Z_to_bv 64 (usp + -384)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
xa0 (Z_to_bv 64 OUT) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
(Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 A)
(Z_to_bv 64 (sbmode_struct mo)) cs8 cs9 cs10 cs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2fa98) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -384) /\ frame_at X m fr /\ f_0 fr = Z_to_bv 64 0
/\ f_16 fr = Z_to_bv 64 (sbmode_struct mo) /\ f_128 fr = Z_to_bv 64 OUT /\ f_160 fr = Z_to_bv 64 A /\ f_184 fr = Z_to_bv 64 0
/\ f_208 fr = Z_to_bv 64 1
/\ f_dtx fr = Z_to_bv 64 dtx /\ (dtx = 0 \/ dtx = 1)
/\ submode_at (sbm_submodes mo) (sbd_submodeID s1) = None.

#[using="RCEIL k IH"] Lemma sbN1_40 : FS = 40 -> forall low dtx s1 b ms, at_N X low dtx s1 b ms -> evt rsegs (at_N1 low dtx s1 b) ms.
Proof.
intros EFS low dtx s1 b ms AT.
first [ sf_destruct 23%nat AT as Fx fc m kk xra j ows stb fr -> FRM CTX ST FRA F0eq F16 F128 F160 F184 F208 Fdtx DTX01 SMN | sf_fb; destruct AT as (Fx & fc & m & kk & xra & j & ows & stb & fr & -> & FRM & CTX & ST & FRA & F0eq & F16 & F128 & F160 & F184 & F208 & Fdtx & DTX01 & SMN) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ Iffs1 _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & Iffs1 & _ & Inb1 & Ilpc1 & _) ].
assert (Hfs1 : sbd_frame_size s1 = 4 * FS) by (rewrite Efr; exact Hfs).
assert (Hffs1 : sbd_full_frame_size s1 = 8 * FS) by (rewrite Iffs1, Hfs1; lia). clear Iffs1.
rewrite EFS in *.
pose proof INV0 as (Imo & _).
pose proof (ih_isave _ _ IH) as KK. rewrite EFS in KK.

zstep. zstep. rewrite F184. zstep. unfold sb_isave_ptr. rewrite Eis.
destruct (sbd_innov_save s0) as [kk0|] eqn:EISV.
-
subst kk0. replace (OUT + 4 * (8 * 40)) with (OUT + 1280) by lia.
if_false_x.
zstep. rewrite Hffs1. rewrite (sx32_lit (8 * 40)) by lia. zstep. zstep. zstep.
pose proof (f32_split rsegs _ _ ows 320%nat ltac:(rewrite Lows; lia) XO) as [XO1 XO2].
pose proof (f32_split rsegs _ _ (skipn 320%nat ows) 320%nat ltac:(rewrite length_skipn, Lows; lia) XO2) as [XO2a XO3]. clear XO2.
replace (OUT + 4 * Z.of_nat 320%nat + 4 * Z.of_nat 320%nat) with (OUT + 2560) in XO3 by lia.
replace (OUT + 4 * Z.of_nat 320%nat) with (OUT + 1280) in XO2a by lia.
set (owsA := firstn 320%nat ows) in *. assert (LA : length owsA = 320%nat) by (subst owsA; rewrite length_firstn, Lows; lia).
set (owsC := skipn 320%nat (skipn 320%nat ows)) in *. assert (LC : length owsC = (2000 - 320%nat - 320%nat)%nat) by (subst owsC; rewrite !length_skipn, Lows; lia).
pose proof (f32_as_blob _ _ _ 320%nat XO2a ltac:(rewrite length_firstn, length_skipn, Lows; lia)) as XB. clear XO2a XO.
replace (Z.to_nat (4 * Z.of_nat 320%nat)) with (Z.to_nat 1280) in XB by lia.
clearbody owsA owsC.
replace (Z.shiftl (8 * 40) 2) with 1280 by reflexivity.
call (nmemset_specZ (OUT + 1280) 1280 0); [exact XB | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
try clear XB. rename MI0 into MI.
match goal with H : rw_cells _ _ (OUT + 1280) [CB _ _] |- _ =>
change (Z.to_nat 1280) with (4 * 320%nat)%nat in H at 1;
destruct (rw_cells_CB_f32 rsegs _ _ 320%nat _ H) as (zws & Lz & XO2); clear H end.
pose proof (f32_join rsegs _ _ _ _ XO1 ltac:(rewrite LA; replace (OUT + 4 * Z.of_nat 320%nat) with (OUT + 1280) by lia; exact XO2)) as XO12.
pose proof (f32_join rsegs _ _ _ _ XO12 ltac:(rewrite length_app, LA, Lz; replace (OUT + 4 * Z.of_nat (320%nat + 320%nat)) with (OUT + 2560) by lia; exact XO3)) as XO.
clear XO1 XO12 XO2 XO3.
assert (LowsN : length ((owsA ++ zws) ++ owsC) = 2000%nat) by (rewrite !length_app, LA, Lz, LC; lia).
zstep. rewrite F128.
apply evt_done. unfold at_N1.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (((owsA ++ zws) ++ owsC)) | exact (stb) | ] | sf_fb; exists j, ((owsA ++ zws) ++ owsC), stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM|].
rewrite <- EISV in Eis.
split. { close_ctxE EFS MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
feqs. exact SMN.
-
if_true. rewrite <- EISV in Eis.
apply evt_done. unfold at_N1.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctxE EFS MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
feqs. exact SMN.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

#[using="RCEIL k IH"] Lemma sbN2_40 : FS = 40 -> forall low dtx s1 b ms, at_N1 low dtx s1 b ms -> evt rsegs (at_X X 0 (set_sbd_first s1 1) low b) ms.
Proof.
intros EFS low dtx s1 b ms AT.
first [ sf_destruct 24%nat AT as Fx fc m kk xra xa0 j ows stb fr -> FRM CTX ST FRA F0eq F16 F128 F160 F184 F208 Fdtx DTX01 SMN | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & j & ows & stb & fr & -> & FRM & CTX & ST & FRA & F0eq & F16 & F128 & F160 & F184 & F208 & Fdtx & DTX01 & SMN) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ Iffs1 _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & Iffs1 & _ & Inb1 & Ilpc1 & _) ].
assert (Hfs1 : sbd_frame_size s1 = 4 * FS) by (rewrite Efr; exact Hfs).
assert (Hffs1 : sbd_full_frame_size s1 = 8 * FS) by (rewrite Iffs1, Hfs1; lia). clear Iffs1.
rewrite EFS in *.
pose proof INV0 as (Imo & _).
pose proof (ih_nodup _ _ IH) as ND. pose proof (ih_apart _ _ IH) as APB. pose proof (ih_range _ _ IH) as RNG.
pose proof (ih_out4 _ _ IH) as O4.
assert (RBA : 0 < a_g0 a /\ a_g0 a mod 16 = 0 /\ 0 < a_g1 a /\ a_g1 a mod 16 = 0 /\ 0 < a_iq a /\ a_iq a mod 16 = 0 /\ 0 < a_msp a /\ a_msp a mod 16 = 0).
{ pose proof (RNG (sbd_g0_mem s0, a_g0 a, 256) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; auto 20)) as R1.
pose proof (RNG (sbd_g1_mem s0, a_g1 a, 256) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; auto 20)) as R2.
pose proof (RNG (sbd_interp_qlpc s0, a_iq a, 32) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; auto 20)) as R5.
pose proof (RNG (sbd_mem_sp s0, a_msp a, 64) ltac:(apply in_app_iff; left; unfold sb_blocks; cbn [In]; auto 20)) as R8.
unfold rblock_range in R1, R2, R5, R8. cbn [blk_addr blk_size fst snd] in R1, R2, R5, R8. lia. }

zstep. rewrite Fdtx. rewrite (sx32_lit dtx) by lia. zstep.
rewrite (eqb_zero_lit dtx) by lia. if_cases Kd; zify_bool Kd.
2:{
upto 0x2fcf8.
assert (PCS : sb_pieces m S s1 a OUT j) by (unfold sb_pieces, sbp_hdr, sbp_ptrs, sbp_cfg; repeat first [assumption | split]).
apply (proj2 (sb_pieces_iff m S s1 a OUT j)) in PCS. clear P0 P1 P2 P3 P4 P5 P6 P7.
assert (BUFS : sb_bufs rsegs m a j) by (unfold sb_bufs; repeat first [assumption | split]). clear BG0 BG1 BEXC BOQ BIQ BMSP BPG BER.
pose proof (f32_as_u8arr _ _ _ XO) as [XOU LOU]. rewrite Lows in LOU. clear XO.
call ((h_lost _ (ih_hyps _ _ IH)) S OUT s1 a j (cells_bytes (f32 ows)) lo (Z_to_bv 64 0));
[ exact PCS | exact JOK | exact INV | exact BUFS | exact XOU | rewrite LOU; reflexivity
| rewrite Ebl; eapply lbd_apart_sub; [exact APB|]; intros x Hx; apply in_app_iff; left; exact Hx
| rewrite Ebl; rewrite map_app in ND; exact (List.NoDup_app_remove_r _ _ ND)
| rewrite Ebl; intros x Hx; apply RNG; apply in_app_iff; left; exact Hx
| exact Tout | exact Tlo
| rewrite USP384; unfold apart, HOUT_BYTES; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP384; exact ST | rewrite USP384; unfold SBLOST_DEPTH; lia | rewrite USP384; lia
| reflexivity | reflexivity | reflexivity | reflexivity | exact MI | exact FRM | exact O4 | ].
clear BUFS. name_post.
match goal with H : rw_cells _ _ S (SBCELLS _ _ _ ?jj) |- _ => rename H into PCS'; rename jj into j' end.
match goal with H : sb_junk_ok _ j' |- _ => rename H into JOK' end.
match goal with H : sb_bufs _ _ a j' |- _ => rename H into BUFS' end.
match goal with H : u8arr _ _ OUT ?ob |- _ => rename H into XOU'; rename ob into outb' end.
match goal with H : Z.of_nat (length outb') = _ |- _ => rename H into LOU' end.
apply (proj1 (sb_pieces_iff _ S _ a OUT j')) in PCS'. first [ sf_destruct 8%nat PCS' as P0 P1 P2 P3 P4 P5 P6 P7 | sf_fb; destruct PCS' as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7) ].
unfold sbp_hdr in P0. unfold sbp_ptrs in P2. unfold sbp_cfg in P5.
first [ sf_destruct 8%nat BUFS' as BG0 BG1 BEXC BOQ BIQ BMSP BPG BER | sf_fb; destruct BUFS' as (BG0 & BG1 & BEXC & BOQ & BIQ & BMSP & BPG & BER) ].
destruct (u8arr_as_f32 _ OUT outb' 2000%nat XOU' ltac:(unfold HOUT_BYTES in LOU'; lia)) as (ows' & Lows' & XO').
clear XOU' LOU' JOK. rewrite USP384 in STc.

zstep. zstep.
apply evt_done. unfold at_X.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _). sf_eexists 13%nat. first [ unshelve sf_eexists 3%nat; [ exact (j') | exact (ows') | exact (stb) | ] | sf_fb; exists j', ows', stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRMc|].
split. { close_ctxE EFS MU. }
split; [exact STc|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|]. lia. }

subst dtx.

zstep. rewrite Hfs1. rewrite (sx32_lit (4 * 40)) by lia. upto 0x2fc00.
pose proof (f32_split rsegs _ _ ows 160%nat ltac:(rewrite Lows; lia) XO) as [XO1 XO2].
pose proof (f32_split rsegs _ _ (skipn 160%nat ows) 160%nat ltac:(rewrite length_skipn, Lows; lia) XO2) as [XO2a XO3]. clear XO2 XO.
replace (OUT + 4 * Z.of_nat 160%nat + 4 * Z.of_nat 160%nat) with (OUT + 1280) in XO3 by lia.
replace (OUT + 4 * Z.of_nat 160%nat) with (OUT + 640) in XO2a by lia.
set (owsA := firstn 160%nat ows) in *. assert (LA : length owsA = 160%nat) by (subst owsA; rewrite length_firstn, Lows; lia).
set (owsB := firstn 160%nat (skipn 160%nat ows)) in *. assert (LB : length owsB = 160%nat) by (subst owsB; rewrite length_firstn, length_skipn, Lows; lia).
set (owsC := skipn 160%nat (skipn 160%nat ows)) in *. assert (LC : length owsC = (2000 - 160%nat - 160%nat)%nat) by (subst owsC; rewrite !length_skipn, Lows; lia).
clearbody owsA owsB owsC.
destruct owsB as [|xb owsB']; [cbn in LB; lia|].
eapply evt_cut.
{ eapply (vs_loop OUT 160 160%nat) with (done := []) (rest := owsB');
[ cbn [length]; cbn [length] in LB; lia | lia | lia | unfold NB_GLOBALS_TOP in *; lia | exact O4 | unfold HOUT_BYTES in *; lia | exact MI | apply munch_refl | apply wmono_refl
| apply rw_cells_nil; lia | sf_eexists 2%nat; split; [reflexivity| cbn [length]; replace (OUT + 4 * 160 + 4 * Z.of_nat 0) with (OUT + 640) by lia; exact XO2a] ]. }
lazymatch goal with |- forall ms1, _ -> evt _ _ _ => post_call rsegs m end.
rename MI0 into MI. replace (OUT + 4 * 160) with (OUT + 640) in * by lia.
match goal with H : rw_cells _ _ (OUT + 640) (f32 ?w), L : length ?w = _ |- _ => rename H into XO2; rename L into LB2; rename w into owsB end.
clear LB xb owsB'.

upto 0x2fc5c. zstep. rewrite F208. upto 0x2fc78.
zstep. rewrite Ilpc1. rewrite (sx32_lit 8) by lia. upto 0x2fc88. zstep. rewrite F184. upto 0x232bc.
pose proof (f32_split rsegs _ _ (sj_msp j) 8%nat ltac:(rewrite Lmsp; lia) BMSP) as [BM1 BM2]. clear BMSP.
replace (a_msp a + 4 * Z.of_nat 8) with (a_msp a + 32) in BM2 by lia.
assert (LM1 : length (firstn 8 (sj_msp j)) = 8%nat) by (rewrite length_firstn, Lmsp; reflexivity).
assert (LM2 : length (skipn 8 (sj_msp j)) = 8%nat) by (rewrite length_skipn, Lmsp; reflexivity).
replace (640 + OUT) with (OUT + 640) by lia.
call ((h_iir _ (ih_hyps _ _ IH)) (OUT + 640) (a_iq a) (OUT + 640) (a_msp a) 160 lo owsB (sj_iq j) owsB (firstn 8 (sj_msp j)) (Z_to_bv 64 0));
[ exact XO2 | rewrite LB2; reflexivity | exact BIQ | exact Liq | exact BM1 | exact LM1 | left; split; reflexivity | lia
| unfold apart; lia | unfold apart; lia
| unfold apart; pose proof (lay_IQ_MSP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| unfold apart; lia
| unfold NB_GLOBALS_TOP in *; lia | Z.to_euclidean_division_equations; lia
| lia | Z.to_euclidean_division_equations; lia
| unfold NB_GLOBALS_TOP in *; lia | Z.to_euclidean_division_equations; lia
| lia | Z.to_euclidean_division_equations; lia
| rewrite USP384; exact ST | rewrite USP384; unfold IIR_DEPTH; lia | unfold NB_GLOBALS_TOP in *; lia | rewrite USP384; lia
| rewrite USP384; unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP384; unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP384; unfold apart; lia | rewrite USP384; unfold apart; lia
| reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | reflexivity | reflexivity | exact MI | exact FRM | ].
cbv beta delta [callR]. rename MI0 into MI. clear FRM.
match goal with H : stk _ _ lo _ |- _ => rename H into ST end. try rewrite USP384 in ST.
match goal with H : rw_cells _ _ (OUT + 640) (f32 ?w), L : length ?w = _ |- _ => rename H into XO2'; rename L into LB2'; rename w into owsB2 end.
match goal with H : rw_cells _ _ (a_msp a) (f32 ?w), L : length ?w = _ |- _ => rename H into BM1'; rename L into LM1'; rename w into msp1 end.
match goal with H : frm0 ?f |- _ => rename H into FRM end.
try clear XO2; try clear LB2; try clear BM1; try clear LM1.

pose proof (f32_join rsegs _ _ _ _ XO1 ltac:(rewrite LA; replace (OUT + 4 * Z.of_nat 160%nat) with (OUT + 640) by lia; exact XO2')) as XOY. clear XO1 XO2'.
assert (LY : length (owsA ++ owsB2) = Z.to_nat 320) by (rewrite length_app, LA, LB2'; lia).
pose proof (f32_join rsegs _ _ _ _ BM1' ltac:(rewrite LM1'; replace (a_msp a + 4 * Z.of_nat 8) with (a_msp a + 32) by lia; exact BM2)) as BMSP. clear BM1' BM2.
assert (Lmsp' : length (msp1 ++ skipn 8 (sj_msp j)) = 16%nat) by (rewrite length_app, LM1', LM2; reflexivity).

zstep. rewrite F128. zstep. rewrite Hfs1. rewrite (sx32_lit (4 * 40)) by lia.
upto 0x2fca4. zstep. rewrite F208. upto 0x2fcc0.
zstep. rewrite Hffs1. rewrite (sx32_lit (8 * 40)) by lia.
pose proof (USPk _ _ IH (-400) ltac:(lia)) as USP400.
carve_frame 16%nat ST.
apply (rw_cells_split_CB rsegs _ _ [] 16 _ _ [8;8]%nat) in FR; [|reflexivity]; cbn [mk_CB_cells app] in FR.
upto 0x2fcdc. zstep. rewrite F184. upto 0x24100.
replace (640 + OUT) with (OUT + 2 * 320) by lia.
chunk_splitk FR at 1%nat as FR8.
call ((h_qmf _ (ih_hyps _ _ IH)) OUT 320 (a_g0 a) (a_g1 a) lo (owsA ++ owsB2) (sj_g0 j) (sj_g1 j) (Z_to_bv 64 0));
[ exact XOY | exact LY | lia | exact BG0 | exact Lg0 | exact BG1 | exact Lg1
| rewrite USP400; exact FR8
| rewrite USP400; exact ST | rewrite USP400; unfold QMF_DEPTH; lia | unfold NB_GLOBALS_TOP; lia | rewrite USP400; lia
| unfold NB_GLOBALS_TOP; lia
| pose proof (lay_img_G0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); unfold NB_GLOBALS_TOP; lia
| pose proof (lay_img_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); unfold NB_GLOBALS_TOP; lia
| rewrite USP400; unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| rewrite USP400; unfold apart; lia | rewrite USP400; unfold apart; lia
| unfold apart; lia | unfold apart; lia
| unfold apart; pose proof (lay_G0_G1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| reflexivity | reflexivity | reflexivity | reflexivity
| reflexivity | reflexivity | reflexivity | reflexivity
| exact MI | exact FRM | exact O4 | lia | Z.to_euclidean_division_equations; lia | lia | Z.to_euclidean_division_equations; lia | ].
cbv beta delta [callR]. rename MI0 into MI. clear FRM. try clear ST. name_post. rename FRMc into FRM. rename STc into ST. rewrite USP400 in ST.
match goal with H : rw_cells _ _ OUT (f32 ?w), L : length ?w = _ |- _ => rename H into XOY'; rename L into LY'; rename w into owsY end.
match goal with H : rw_cells _ _ (a_g0 a) (f32 ?w), L : length ?w = _ |- _ => rename H into BG0'; rename L into Lg0'; rename w into g0' end.
match goal with H : rw_cells _ _ (a_g1 a) (f32 ?w), L : length ?w = _ |- _ => rename H into BG1'; rename L into Lg1'; rename w into g1' end.
try clear XOY LY BG0 BG1.
pose proof (f32_join rsegs _ _ _ _ XOY' ltac:(rewrite LY'; replace (OUT + 4 * Z.of_nat (Z.to_nat 320)) with (OUT + 1280) by lia; exact XO3)) as XO. clear XOY' XO3.
assert (Lows' : length (owsY ++ owsC) = 2000%nat) by (rewrite length_app, LY', LC; lia).

zstep. chunk_cat FR8 FR. release_frame FR8 ST (usp + -384).
upto 0x2fb90.
apply evt_done. unfold at_X.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _). sf_eexists 13%nat.
exists (SBJ (sj_last_ener j) (sj_seed j) (sj_pad1 j) (sj_pad2 j) g0' g1' (sj_exc j) (sj_oq j) (sj_iq j) (msp1 ++ skipn 8 (sj_msp j)) (sj_pg j) (sj_er j)).
exists (owsY ++ owsC), stb. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctxE EFS MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|]. lia.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

End Seg.
