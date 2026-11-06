(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1df X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05q X05s X05u X05t
X081 X05l X05m X09f X06d X069 X082 X08y X0b1 X0b0 X05a X088.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0b4.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0ba X0b8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac simpl_sizes ::=
rewrite ?cells_size_sbp_hdr, ?cells_size_sbp_ptrs, ?cells_size_sbp_cfg, ?cells_size_sb_slots, ?app_length, ?cells_size_app, ?cells_size_f32, ?length_f32;
cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?app_length, ?cells_size_f32, ?length_f32; cbn [length].

Definition sbl_v416A (hb : Z) (sm : submode) : Z := hb - (if sm_double_codebook sm =? 0 then 0 else 224).

Section DA.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.
Hypothesis MEMS : memset_icontract RT e_asan_memset.
Hypothesis INNV : forall p, scb_params_ok p -> innov_unquant_cps RT (ptr := bptr) (InnovSplitCbShapeSignUnquant p).

Lemma sbl_dA : forall (Σ : rts RT) PMc (usp lo hb S OUT A D f sf MODE fsz FS sub fh PD ND : Z) (kh : nat) (v : sb_vslots) (s : sbd_state bptr) (a : sb_addrs)
(b : bits_st bptr) (sm : submode) (pad1 : list byte) (seed : word) (ex ows ler : list word)
(xs3 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
fdfs_only PMc -> mat_stable PMc -> X1cn.frm0 fc ->
rw_cells asegs m (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v) -> v_296 v = Z_to_bv 64 sub -> v_416 v = Z_to_bv 64 hb ->
rw_cells asegs m S (sbp_hdr s a) -> rw_cells asegs m (S + 132) [C4 seed] -> rw_cells asegs m (S + 136) (sbp_cfg s pad1) ->
rw_cells asegs m (S + 152) [C4 (Z_to_bv 64 (sbd_submodeID s))] ->
sbd_subframeSize s = FS -> sbd_frame_size s = fsz -> 0 <= sbd_submodeID s <= 7 ->
((sbd_mode s = ModeWB /\ FS = 40 /\ fsz = 160 /\ hb = usp + -1312) \/ (sbd_mode s = ModeUWB /\ FS = 80 /\ fsz = 320 /\ hb = usp + -1472)) ->
MODE = sbmode_struct (sbd_mode s) -> submode_at (sbm_submodes (sbd_mode s)) (sbd_submodeID s) = Some sm -> 0 <= sub < 4 ->
In (S, 160) (rt_live RT Σ) -> S mod 8 = 0 ->
bits_rep asegs m A D b -> bits_ok b -> In (fh, kh) (rt_frames RT Σ) -> fh <= A -> A + BITS_SIZEOF <= fh + fs_size kh - 8 -> A mod 4 = 0 -> acc asegs m A BITS_SIZEOF ->
In (PD, ND) (rt_live RT Σ) -> PD <= D -> D + sb_buf_size b <= PD + ND -> PD <> S ->
rw_cells asegs m (usp + -768) (f32 ler) -> length ler = 4%nat -> In (usp + -768, 16) (rt_pois RT Σ) ->
rw_cells asegs m OUT (f32 ows) -> length ows = 2000%nat -> fh <= OUT -> OUT + 8000 <= fh + fs_size kh - 8 -> OUT mod 4 = 0 -> acc asegs m OUT 8000 ->
hidp (A + BITS_SIZEOF <= OUT \/ OUT + 8000 <= A) ->
rw_cells asegs m (hb + 32) (f32 ex) -> Z.of_nat (length ex) = FS -> In (hb + 32, 4 * FS) (rt_pois RT Σ) ->
pois_above (rt_pois RT Σ) hb -> rt_frames RT Σ <> [] ->
ART RT Σ m -> mem_inv asegs m -> stk asegs m lo hb -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + SB_LOOP_STACK <= usp + -1088 ->
usp mod 32 = 0 -> usp + 16 <= USTACK_TOP -> tp = Z_to_bv 64 0x630458 ->
cps asegs (ASTA RT Σ PMc (eq (MS (R_L usp hb S sub gp tp (Z_to_bv 64 RA_sbl_memset2) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
xs3 (Z_to_bv 64 FS) (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 0x10184) (Z_to_bv 64 (hb + 32)) t3 t4 t5 t6)
F (ret_pc (Z_to_bv 64 RA_sbl_memset2)) fc None m (seg_rom asegs))))
(fun c => exists Σ', ASTA RT Σ' PMc (fun ms => exists (m' : mem) (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs4 xt3 xt4 xt5 xt6 : word) (F' : bvmap 5 word) (fc' : bv 32)
(v' : sb_vslots) (seed' : word) (ex' : list word),
ms = MS (R_L usp hb S sub gp tp xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
xs3 xs4 (Z_to_bv 64 (4 * sub)) (Z_to_bv 64 (MODE + 32)) (Z_to_bv 64 (S + 32)) (Z_to_bv 64 (hb + 32))
xt3 xt4 xt5 xt6) F' (Z_to_bv 64 SBL_PC_J) fc' None m' (seg_rom asegs)
/\ X1cn.frm0 fc' /\ rt_after RT Σ' hb lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) hb [(usp + -608, usp + -160); (S + 132, S + 136); (A, A + BITS_SIZEOF); (hb + 32, hb + 32 + 4 * FS)] m m'
/\ rw_cells asegs m' (usp + -608) (sb_slots usp S OUT A f sf MODE fsz v') /\ v_296 v' = Z_to_bv 64 sub /\ v_416 v' = Z_to_bv 64 (sbl_v416A hb sm)
/\ v_248 v' = v_248 v /\ v_256 v' = v_256 v /\ v_264 v' = v_264 v
/\ rw_cells asegs m' (S + 132) [C4 seed']
/\ rw_cells asegs m' (hb + 32) (f32 ex') /\ Z.of_nat (length ex') = FS
/\ bits_rep asegs m' A D (sbsub_bits sm b) /\ bits_ok (sbsub_bits sm b) /\ acc asegs m' A BITS_SIZEOF) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ).
Proof.
intros Σ PMc usp lo hb S OUT A D f sf MODE fsz FS sub fh PD ND kh v s a b sm pad1 seed ex ows ler xs3 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
FDO MST FRM SL V296 V416 HD SEEDC CFG IDC EFS EFSZ HSID HMO EMODE SM SUB INL S8 BREP BOK INFH FA1 FA2 A4 ACA INPD PD1 PD2 PDS LERC LLER INPER
OUTC LOUT FO1 FO2 O4 ACO HAO EXC LEX INPX POA FRN ART0 MI0 ST0 LOWS ROOM U32 USPT ETP.
intros T c Hc Hk.
pose proof (AF_LIB Σ m ART0) as LC. pose proof (af_client_consts RT AF Σ m ART0) as CC.
pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
destruct (live_below_lo RT AF Σ m S 160 lo ART0 INL LOWS) as (SPOS & SBLO & LOSH).
pose proof (live_facts RT AF Σ m S 160 ART0 INL) as (_ & _ & _ & SSHD).
pose proof (af_live_small RT AF Σ m S 160 ART0 INL ltac:(lia)) as SSEG.
assert (SOFF : S + 160 <= SH_LO \/ SH_HI <= S) by (clear - SSHD; unfold SH_LO, SH_HI; lia).
destruct (af_acc_live RT AF Σ m S 160 ART0 INL) as (_ & ACS).
assert (LOR2 : lo + 74848 <= usp + -1088) by (clear - ROOM; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in ROOM; lia).
assert (OBS : aobj asegs m S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP, USTACK_TOP in *; lia| exact ACS]).

pose proof (frame_facts RT AF Σ m fh kh ART0 INFH) as (FH0 & FH64 & FHIMG & FHTOP & FHSH & _).
destruct (frame_below_lo RT AF Σ m fh kh lo ART0 INFH LOWS) as (FHLO & _ & _).
assert (ALO : A + BITS_SIZEOF <= lo) by (clear - FA2 FHLO; lia).
assert (OUTLO : OUT + 8000 <= lo) by (clear - FO2 FHLO; lia).
assert (ASH : A + BITS_SIZEOF <= SH_LO \/ SH_HI <= A) by (clear - FHSH FA1 FA2; unfold SH_LO, SH_HI, BITS_SIZEOF in *; lia).
assert (AIMG : IMG_TOP <= A) by (clear - FHIMG FA1; unfold IMG_TOP, SEGTOP_A in *; lia).
destruct (frame_live_apart RT AF Σ m fh kh S 160 ART0 INFH INL) as (SFA & _).
assert (SEPSA : S + 160 <= A \/ A + BITS_SIZEOF <= S) by (clear - SFA FA1 FA2; unfold BITS_SIZEOF in *; lia).
assert (OBA : aobj asegs m A BITS_SIZEOF) by (split; [lia|]; split; [clear - ALO LOR2 USPT; unfold APP_TOP, USTACK_TOP in *; lia| exact ACA]).

destruct (live_below_lo RT AF Σ m PD ND lo ART0 INPD LOWS) as (PD0 & PDLO & _).
destruct (af_acc_live RT AF Σ m PD ND ART0 INPD) as (_ & ACPD).
assert (OBD : aobj asegs m D (sb_buf_size b)).
{ split; [lia|]. split; [clear - PD2 PDLO LOR2 USPT; unfold APP_TOP, USTACK_TOP in *; lia|]. apply (acc_sub asegs m PD ND); [exact ACPD| lia| lia]. }
assert (DLO : D + sb_buf_size b <= lo) by (clear - PD2 PDLO; lia).
assert (PDSA : hidp (PD + ND <= S \/ S + 160 <= PD)).
{ unfold hidp. destruct (in_split _ _ INPD) as (l1 & l2 & E).
apply (af_live_disj RT AF Σ m PD ND S 160 l1 l2 ART0 E). rewrite E in INL. apply in_app_iff in INL. apply in_app_iff.
destruct INL as [H2|[H2|H2]]; [left; exact H2| exfalso; apply PDS; congruence| right; exact H2]. }
pose proof (fun a0 => aclient_split RT AF Σ m hb a0 ART0) as SPL.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) hb [(usp + -608, usp + -160); (S + 132, S + 136); (A, A + BITS_SIZEOF); (hb + 32, hb + 32 + 4 * FS)] m) as PF.
cps_norm. cps_hide.

pose proof (HMO : _ \/ _) as HMO0.
assert (HMO' : sbd_mode s = ModeWB \/ sbd_mode s = ModeUWB) by (destruct HMO0 as [(E & _) | (E & _)]; [left|right]; exact E).
assert (FSB : 40 <= FS <= 80 /\ 160 <= fsz <= 320 /\ (hb = usp + -1312 \/ hb = usp + -1472) /\ 4 * FS + 32 + hb = usp + -1120)
by (clear - HMO0; lia).
assert (HB32 : hb mod 32 = 0) by (destruct FSB as (_ & _ & [-> | ->] & _); clear - U32; Z.div_mod_to_equations; lia).
assert (HID : (sbd_submodeID s = 1 /\ sm = wb_submode1)
\/ (sbd_mode s = ModeWB /\ ((sbd_submodeID s = 2 /\ sm = wb_submode2) \/ (sbd_submodeID s = 3 /\ sm = wb_submode3) \/ (sbd_submodeID s = 4 /\ sm = wb_submode4)))).
{ destruct (sb_submode_cases _ _ _ HMO' HSID SM) as [(EMO & [H|[H|[H|H]]]) | (EMO & EID & ESM)];
[left; exact H | right; split; [exact EMO| tauto] .. | left; split; assumption]. }
clear HMO'.
destruct HID as [(EID & ->) | (EMO & HID)].
-
rewrite EID in IDC.
assert (WIN : (Z.to_nat (fsz + FS * sub) + Z.to_nat FS <= length ows)%nat) by (rewrite LOUT; clear - FSB SUB; nia).
destruct (sbl_f32_win _ OUT ows _ _ OUTC WIN) as (_ & OW2 & _).
replace (OUT + 4 * Z.of_nat (Z.to_nat (fsz + FS * sub))) with (OUT + 4 * fsz + 4 * (FS * sub)) in OW2 by (clear - FSB SUB; nia).
assert (LLI : Z.of_nat (length (firstn (Z.to_nat FS) (skipn (Z.to_nat (fsz + FS * sub)) ows))) = FS)
by (rewrite length_firstn, length_skipn, LOUT; clear - FSB SUB; nia).
remember (firstn (Z.to_nat FS) (skipn (Z.to_nat (fsz + FS * sub)) ows)) as lis eqn:ELIS. clear ELIS WIN.
assert (OBLI : aobj asegs m (OUT + 4 * fsz + 4 * (FS * sub)) (4 * FS)).
{ split; [clear - FSB SUB FO1 FH0; nia|]. split; [clear - OUTLO LOR2 USPT FSB SUB; unfold APP_TOP, USTACK_TOP in *; nia|].
apply (acc_sub asegs m OUT 8000); [exact ACO| clear - FSB SUB; nia | clear - FSB SUB; nia]. }
assert (LI4 : (OUT + 4 * fsz + 4 * (FS * sub)) mod 4 = 0)
by (replace (OUT + 4 * fsz + 4 * (FS * sub)) with (OUT + (fsz + FS * sub) * 4) by ring; rewrite Z_mod_plus_full; exact O4).
assert (LILO : OUT + 4 * fsz + 4 * (FS * sub) + 4 * FS <= lo) by (clear - OUTLO FSB SUB; nia).
assert (SEPSL : S + 160 <= OUT + 4 * fsz + 4 * (FS * sub) \/ OUT + 4 * fsz + 4 * (FS * sub) + 4 * FS <= S)
by (unfold hid in SFA; clear - SFA FO1 FO2 FSB SUB; nia).
assert (SEPAL : A + BITS_SIZEOF <= OUT + 4 * fsz + 4 * (FS * sub) \/ OUT + 4 * fsz + 4 * (FS * sub) + 4 * FS <= A)
by (unfold hidp in HAO; clear - HAO FSB SUB; unfold BITS_SIZEOF in *; nia).
assert (OBEX : aobj asegs m (hb + 32) (4 * FS))
by (split; [clear - FSB LOR2 LOSH; lia|]; split; [clear - FSB USPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (af_acc_pois RT AF Σ m _ _ ART0 INPX)]).
assert (OBM : aobj asegs m MODE 216).
{ rewrite EMODE. destruct HMO0 as [(E & _) | (E & _)]; rewrite E; cbn [sbmode_struct]; (apply (aobj_lit RT AF Σ m _ 216 ART0);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_sb_wb_mode, A_sb_uwb_mode; lia | unfold A_sb_wb_mode, A_sb_uwb_mode, APP_TOP; lia]). }
assert (OBSM : aobj asegs m (sb_sub_addr 1) 88).
{ cbn [sb_sub_addr Z.eqb Pos.eqb]. apply (aobj_lit RT AF Σ m _ 88 ART0);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_wb_submode1; lia | unfold A_wb_submode1, APP_TOP; lia]. }
assert (HMO5 : (sbd_mode s = ModeWB /\ FS = 40) \/ (sbd_mode s = ModeUWB /\ FS = 80)) by (clear - HMO0; tauto).
assert (LOHB : lo <= hb - 32) by (clear - FSB LOR2; lia).
assert (HBU : hb + 32 + 4 * FS <= usp + -1088) by (clear - FSB; lia).
assert (SPH : usp < 2 ^ 63) by (clear - USPT; unfold USTACK_TOP in *; lia).
cps_seg (sbl_e5n usp lo hb S OUT A D f sf MODE fsz FS sub (OUT + 4 * fsz + 4 * (FS * sub)) v s a pad1 b lis ex xs3 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
SL V296 HD EFS CFG IDC OBS S8 SPOS SOFF SBLO HMO5 EMODE OBM OBSM LC SUB BREP BOK OBA OBD ASH ALO DLO AIMG SEPSA eq_refl OW2 LLI OBLI LI4 LILO SEPSL SEPAL
EXC LEX OBEX CC ST0 LOHB HBU LOSH SPH U32 HB32 MI0 FRM).
destruct POST as (m1 & xra1 & xt01 & xt11 & xt21 & xa01 & xa11 & xa21 & xa31 & xa41 & xa51 & xa61 & xa71 & xt31 & xt41 & xt51 & xt61 & F1 & fc1 & exs1
& -> & MU1 & WM1 & MI1 & ST1 & FRM1 & REP1 & EXC1 & LEX1).
clear EXC LEX BREP OW2 OBLI OBEX.
lazymatch type of MU1 with munch ?W _ _ => assert (OF1 : offsh W) by (cbn; clear - ASH FSB LOR2 LOSH; unfold hid, SH_LO, SH_HI, BITS_SIZEOF in *; lia) end.
pose proof (aobj_munch asegs _ m m1 A BITS_SIZEOF OBA MU1 (shfree_of_aobj asegs _ m A BITS_SIZEOF OF1 OBA)) as (_ & _ & ACA1).
cps_seg_post.
apply Hk. exists Σ. split; [| repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-.
exists m1, xra1, xt01, xt11, xt21, xa01, xa11, xa21, xa31, xa41, xa51, xa61, xa71, (Z_to_bv 64 FS), xt31, xt41, xt51, xt61, F1, fc1, v, seed, exs1.
split; [reflexivity|].
split; [exact FRM1|]. split; [split; [eassumption|]; split; [exact MI1|]; split; [exact WM1| exact ST1]|].
split; [exact PF|]. split; [eassumption|]. split; [exact V296|]. split; [unfold sbl_v416A; cbn [wb_submode1 sm_double_codebook Z.eqb]; rewrite Z.sub_0_r; exact V416|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [eassumption|]. split; [exact EXC1|]. split; [exact LEX1|].
split; [exact REP1|]. split; [exact (proj1 (ub_ok b 5 BOK ltac:(lia)))| exact ACA1].
-
assert (EFS40 : FS = 40 /\ fsz = 160 /\ hb = usp + -1312) by (destruct HMO0 as [(_ & H) | (E & _)]; [exact H| rewrite EMO in E; discriminate E]).
destruct EFS40 as (-> & -> & ->).
assert (HID3 : sbd_submodeID s = 2 \/ sbd_submodeID s = 3 \/ sbd_submodeID s = 4) by (clear - HID; tauto).
destruct (sb_gcqb_at m MI0) as (tab & LTAB & TAB).
assert (OBT : aobj asegs m A_gc_quant_bound 64) by (apply (aobj_lit RT AF Σ m _ 64 ART0);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_gc_quant_bound; lia | unfold A_gc_quant_bound, APP_TOP; lia]).
assert (OBM : aobj asegs m MODE 216).
{ rewrite EMODE, EMO; cbn [sbmode_struct]. apply (aobj_lit RT AF Σ m _ 216 ART0);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_sb_wb_mode; lia | unfold A_sb_wb_mode, APP_TOP; lia]. }
assert (OBSM : aobj asegs m (sb_sub_addr (sbd_submodeID s)) 88).
{ destruct HID3 as [E|[E|E]]; rewrite E; cbn [sb_sub_addr Z.eqb Pos.eqb]; (apply (aobj_lit RT AF Σ m _ 88 ART0);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_wb_submode2, A_wb_submode3, A_wb_submode4; lia
| unfold A_wb_submode2, A_wb_submode3, A_wb_submode4, APP_TOP; lia]). }
assert (OBLER : aobj asegs m (usp + -768) 16)
by (split; [clear - LOR2 LOSH; lia|]; split; [clear - USPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (af_acc_pois RT AF Σ m _ _ ART0 INPER)]).
assert (LOHB : lo <= usp + -1312 - 32) by (clear - LOR2; lia).
assert (HBU : usp + -1312 <= usp + -1088) by lia.
assert (SPH : usp < 2 ^ 63) by (clear - USPT; unfold USTACK_TOP in *; lia).
cps_seg (sbl_e5c usp lo (usp + -1312) S OUT A D f sf MODE 160 sub (sbd_submodeID s) (usp + -768) v s a pad1 sm b ler tab xs3 gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
SL HD EFS CFG IDC OBS S8 SPOS SOFF SBLO EMO EMODE OBM HID3 OBSM LC SUB BREP BOK OBA OBD ASH ALO DLO AIMG SEPSA eq_refl LERC LLER OBLER TAB LTAB OBT
CC ST0 LOHB HBU LOSH SPH U32 MI0 FRM).
destruct POST as (m1 & xt01 & xt11 & xt21 & xa71 & xt31 & xt41 & xt51 & xt61 & F1 & fc1 & -> & MU1 & WM1 & MI1 & ST1 & FRM1 & REP1).
clear BREP TAB OBT OBM OBSM OBLER.
lazymatch type of MU1 with munch ?W _ _ => assert (OF1 : offsh W) by (cbn; clear - ASH LOR2 LOSH; unfold hid, SH_LO, SH_HI, BITS_SIZEOF in *; lia) end.
pose proof (aobj_munch asegs _ m m1 A BITS_SIZEOF OBA MU1 (shfree_of_aobj asegs _ m A BITS_SIZEOF OF1 OBA)) as OBA1.
pose proof (aobj_munch asegs _ m m1 D (sb_buf_size b) OBD MU1 (shfree_of_aobj asegs _ m D (sb_buf_size b) OF1 OBD)) as OBD1.
clear OBA OBD ACA OF1.
cps_seg_post.
rename ART into ART1.
pose (P := if sbd_submodeID s =? 2 then split_cb_high_lbr else split_cb_high).
assert (POK : scb_params_ok P).
{ pose proof scb_params_ok_all as ALL. rewrite Forall_forall in ALL. unfold P. destruct (sbd_submodeID s =? 2); apply ALL; cbn [In]; repeat (first [left; reflexivity | right]). }
assert (PARF : ro_cells asegs m1 (sbl_PAR (sbd_submodeID s)) (scb_par_cellsA P) /\ (sbl_PAR (sbd_submodeID s)) mod 8 = 0 /\ 0x10000 <= sbl_PAR (sbd_submodeID s)
/\ sbl_PAR (sbd_submodeID s) + 24 <= IMG_TOP /\ In (sbl_PAR (sbd_submodeID s), 24) ACC_LITS).
{ pose proof (AF_LIB Σ m1 ART1) as LC1. unfold P, sbl_PAR. destruct (sbd_submodeID s =? 2).
- split; [exact (lib_const m1 A_split_cb_high_lbr (scb_par_cellsA split_cb_high_lbr) LC1 ltac:(lc_in))|]. unfold A_split_cb_high_lbr, IMG_TOP. split; [reflexivity|]. split; [lia|]. split; [lia|].
unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]).
- split; [exact (lib_const m1 A_split_cb_high (scb_par_cellsA split_cb_high) LC1 ltac:(lc_in))|]. unfold A_split_cb_high, IMG_TOP. split; [reflexivity|]. split; [lia|]. split; [lia|].
unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]). }
cps_rt (INNV P POK Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 A D (ub b 4)
(usp + -1312 + 32) (S + 132) (sbl_PAR (sbd_submodeID s)) lo S 160 PD ND fh kh ex seed (Z_to_bv 64 0)).
{ exact (proj1 (ub_ok b 4 BOK ltac:(lia))). }
{ right. exact INPX. }
{ split; [exact FA1|]. split; [exact FA2|]. split; [exact (proj2 (proj2 OBA1))| exact A4]. }
{ rewrite (proj1 (proj2 (ub_ok b 4 BOK ltac:(lia)))). exact PD2. }
{ unfold hidp; left; clear - ALO LOR2; unfold BITS_SIZEOF in *; lia. }
{ rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia). exact ST1. }
{ rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia). clear - ROOM; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia. }
{ rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia). clear - USPT; unfold USTACK_TOP in *; lia. }
{ rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia). clear - U32; Z.div_mod_to_equations; lia. }
{ rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia). exact POA. }
intros c2 (Σ2 & Hc2 & LV2 & FRS2 & SP2 & CR2 & PO2).
cps_unpack_lib Hc2 as (v2 & m2 & is2 & seed2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & EXC2 & LEX2 & SEEDC2 & REP2 & OK2 & ACX2 & ACA2).
clear EXC LEX SEEDC REP1 OBA1 OBD1.
cps_tr_lib PRES2.
clear Hc0.
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m1 =>
assert (PF2 : rt_pres_fp L Fr U W0 m0 m2)
by (apply (pres_fp_trans _ _ _ _ m0 m1 m2 PF);
apply (pres_fp_of_pres_fp _ _ _ _ _ _ _ _ m1 m2 PRES2); [intros e He; exact He | intros e He; exact He | lia |];
intros x _ Ho; cbn [outside] in Ho |- *; decompose [and] Ho;
split; [intros Hin; match goal with H : ~ (usp + -1312 + 32 <= x < usp + -1312 + 32 + 4 * 40) |- _ => apply H; clear - Hin; lia end|];
split; [intros Hin; match goal with H : ~ (S + 132 <= x < S + 136) |- _ => apply H; clear - Hin; lia end|];
split; [assumption | exact I]) end.
clear PF. rename PF2 into PF.
pose proof LV2 as LVE2. pose proof FRS2 as FRE2. cps_sigma LV2 FRS2 SP2.

remember (innov_bits (InnovSplitCbShapeSignUnquant P) (ub b 4)) as b2 eqn:EB2.
destruct REP2 as ((rj2 & Lrj2 & OBJ2) & (bs2 & DAT2 & Hbs2) & SIDE2). unfold bits_cells in OBJ2. apply (proj1 (u8arr_rw_CB m2 D bs2)) in DAT2.
destruct (af_acc_live RT AF Σ2 m2 S 160 ART2 INL) as (_ & ACS2).
assert (OBS2 : aobj asegs m2 S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP, USTACK_TOP in *; lia| exact ACS2]).
pose proof (AF_LIB Σ2 m2 ART2) as LC2. pose proof (af_client_consts RT AF Σ2 m2 ART2) as CC2.
assert (OBM2 : aobj asegs m2 MODE 216).
{ rewrite EMODE, EMO; cbn [sbmode_struct]. apply (aobj_lit RT AF Σ2 m2 _ 216 ART2);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_sb_wb_mode; lia | unfold A_sb_wb_mode, APP_TOP; lia]. }
assert (OBSM2 : aobj asegs m2 (sb_sub_addr (sbd_submodeID s)) 88).
{ destruct HID3 as [E|[E|E]]; rewrite E; cbn [sb_sub_addr Z.eqb Pos.eqb]; (apply (aobj_lit RT AF Σ2 m2 _ 88 ART2);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_wb_submode2, A_wb_submode3, A_wb_submode4; lia
| unfold A_wb_submode2, A_wb_submode3, A_wb_submode4, APP_TOP; lia]). }
assert (OBEX2 : aobj asegs m2 (usp + -1312 + 32) 160) by (split; [clear - LOR2 LOSH; lia|]; split; [clear - USPT; unfold APP_TOP, USTACK_TOP in *; lia| exact ACX2]).
assert (HB32' : (usp + -1312) mod 32 = 0) by (clear - U32; Z.div_mod_to_equations; lia).

assert (SCBSZ : forall n hs sbits (bb : bits_st bptr), bits_ok bb -> 0 <= sbits -> bits_ok (scb_bits n hs sbits bb) /\ sb_buf_size (scb_bits n hs sbits bb) = sb_buf_size bb).
{ induction n as [|n IH]; intros hs sbits bb OKb Hs; cbn [scb_bits]; [split; [exact OKb| reflexivity]|].
destruct (negb (hs =? 0)).
- destruct (ub_ok bb 1 OKb ltac:(lia)) as (OK1 & SZ1 & _). destruct (ub_ok (ub bb 1) sbits OK1 Hs) as (OK3 & SZ3 & _).
destruct (IH hs sbits _ OK3 Hs) as (OK4 & SZ4). split; [exact OK4| rewrite SZ4, SZ3, SZ1; reflexivity].
- destruct (ub_ok bb sbits OKb Hs) as (OK3 & SZ3 & _). destruct (IH hs sbits _ OK3 Hs) as (OK4 & SZ4). split; [exact OK4| rewrite SZ4, SZ3; reflexivity]. }
assert (SZB2 : sb_buf_size b2 = sb_buf_size b).
{ rewrite EB2. cbn [innov_bits]. destruct (ub_ok b 4 BOK ltac:(lia)) as (OK4 & SZ4 & _).
assert (SB0 : 0 <= scb_shape_bits P) by (unfold P; destruct (sbd_submodeID s =? 2); cbn; lia).
rewrite (proj2 (SCBSZ (Z.to_nat (scb_nb_subvect P)) (scb_have_sign P) (scb_shape_bits P) (ub b 4) OK4 SB0)). exact SZ4. }
assert (LBS2 : Z.of_nat (length bs2) = sb_buf_size b2)
by (pose proof OK2 as OK'; unfold bits_ok in OK'; rewrite Hbs2, zlength_map_unsigned in OK'; clear - OK'; lia).
assert (DLO2 : D + Z.of_nat (length bs2) <= lo) by (clear - LBS2 SZB2 DLO; lia).
assert (ALO48 : A + 48 <= lo) by (clear - ALO; unfold BITS_SIZEOF in *; lia).
destruct HID as [(EID & ->) | [(EID & ->) | (EID & ->)]].

rewrite EID in IDC, OBSM2.
assert (LO16 : lo <= usp + -1312 - 16) by (clear - LOR2; lia).
cps_seg (sbl_e7a usp lo (usp + -1312) S OUT A f sf MODE 160 sub _ (usp + -1312 + 32) v s a pad1 is2 xs3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2
SL HD EFS CFG IDC OBS2 S8 SPOS SOFF SBLO EMO EMODE OBM2 ltac:(clear; lia) OBSM2 LC2 eq_refl EXC2 LEX2 OBEX2 CC2 ST2 LO16 ltac:(clear; lia) LOSH SPH U32 HB32' MI2 RS2).
destruct POST as (m3 & xra3 & xt03 & xt13 & xt23 & xa03 & xa13 & xa23 & xa33 & xa43 & xa53 & xa63 & xa73 & xt33 & xt43 & xt53 & xt63 & F3 & fc3 & ex3
& -> & MU3 & WM3 & MI3 & ST3 & FRM3 & EXC3 & LEX3).
clear EXC2 LEX2 OBEX2 OBS2 OBM2 OBSM2 LC2 CC2.
lazymatch type of MU3 with munch ?W _ _ => assert (OF3 : offsh W) by (cbn; clear - LOR2 LOSH USPT; unfold SH_LO, SH_HI, USTACK_TOP in *; lia) end.
assert (OBA2 : aobj asegs m2 A BITS_SIZEOF) by (split; [lia|]; split; [clear - ALO LOR2 USPT; unfold APP_TOP, USTACK_TOP, BITS_SIZEOF in *; lia| exact ACA2]).
pose proof (aobj_munch asegs _ m2 m3 A BITS_SIZEOF OBA2 MU3 (shfree_of_aobj asegs _ m2 A BITS_SIZEOF OF3 OBA2)) as (_ & _ & ACA3).
clear OF3 ACA2 OBA2.
cps_seg_post.
assert (REP3 : bits_rep asegs m3 A D b2).
{ split; [exists rj2; split; [exact Lrj2| unfold bits_cells; exact OBJ2]|].
split; [exists bs2; split; [apply (proj2 (u8arr_rw_CB m3 D bs2)); exact DAT2| exact Hbs2]| exact SIDE2]. }
apply Hk. exists Σ2. split; [| rewrite LVE2, FRE2, SP2, CR2, PO2; repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-.
exists m3, xra3, xt03, xt13, xt23, xa03, xa13, xa23, xa33, xa43, xa53, xa63, xa73, (Z_to_bv 64 A), xt33, xt43, xt53, xt63, F3, fc3, v, seed2, ex3.
split; [reflexivity|].
split; [exact FRM3|]. split; [split; [eassumption|]; split; [exact MI3|]; split; [cps_wmono| exact ST3]|].
split; [exact PF|]. split; [eassumption|]. split; [exact V296|]. split; [unfold sbl_v416A; cbn [wb_submode2 wb_submode3 sm_double_codebook Z.eqb]; rewrite Z.sub_0_r; exact V416|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [eassumption|]. split; [exact EXC3|]. split; [clear - LEX3; lia|].
assert (ESB : sbsub_bits wb_submode2 b = b2) by (rewrite EB2; unfold P; rewrite EID; reflexivity).
rewrite ESB. split; [exact REP3|]. split; [exact OK2| exact ACA3].

rewrite EID in IDC, OBSM2.
assert (LO16 : lo <= usp + -1312 - 16) by (clear - LOR2; lia).
cps_seg (sbl_e7a usp lo (usp + -1312) S OUT A f sf MODE 160 sub _ (usp + -1312 + 32) v s a pad1 is2 xs3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2
SL HD EFS CFG IDC OBS2 S8 SPOS SOFF SBLO EMO EMODE OBM2 ltac:(clear; lia) OBSM2 LC2 eq_refl EXC2 LEX2 OBEX2 CC2 ST2 LO16 ltac:(clear; lia) LOSH SPH U32 HB32' MI2 RS2).
destruct POST as (m3 & xra3 & xt03 & xt13 & xt23 & xa03 & xa13 & xa23 & xa33 & xa43 & xa53 & xa63 & xa73 & xt33 & xt43 & xt53 & xt63 & F3 & fc3 & ex3
& -> & MU3 & WM3 & MI3 & ST3 & FRM3 & EXC3 & LEX3).
clear EXC2 LEX2 OBEX2 OBS2 OBM2 OBSM2 LC2 CC2.
lazymatch type of MU3 with munch ?W _ _ => assert (OF3 : offsh W) by (cbn; clear - LOR2 LOSH USPT; unfold SH_LO, SH_HI, USTACK_TOP in *; lia) end.
assert (OBA2 : aobj asegs m2 A BITS_SIZEOF) by (split; [lia|]; split; [clear - ALO LOR2 USPT; unfold APP_TOP, USTACK_TOP, BITS_SIZEOF in *; lia| exact ACA2]).
pose proof (aobj_munch asegs _ m2 m3 A BITS_SIZEOF OBA2 MU3 (shfree_of_aobj asegs _ m2 A BITS_SIZEOF OF3 OBA2)) as (_ & _ & ACA3).
clear OF3 ACA2 OBA2.
cps_seg_post.
assert (REP3 : bits_rep asegs m3 A D b2).
{ split; [exists rj2; split; [exact Lrj2| unfold bits_cells; exact OBJ2]|].
split; [exists bs2; split; [apply (proj2 (u8arr_rw_CB m3 D bs2)); exact DAT2| exact Hbs2]| exact SIDE2]. }
apply Hk. exists Σ2. split; [| rewrite LVE2, FRE2, SP2, CR2, PO2; repeat split; reflexivity].
eapply ASTA_conseq; [eassumption|]. intros ms <-.
exists m3, xra3, xt03, xt13, xt23, xa03, xa13, xa23, xa33, xa43, xa53, xa63, xa73, (Z_to_bv 64 A), xt33, xt43, xt53, xt63, F3, fc3, v, seed2, ex3.
split; [reflexivity|].
split; [exact FRM3|]. split; [split; [eassumption|]; split; [exact MI3|]; split; [cps_wmono| exact ST3]|].
split; [exact PF|]. split; [eassumption|]. split; [exact V296|]. split; [unfold sbl_v416A; cbn [wb_submode2 wb_submode3 sm_double_codebook Z.eqb]; rewrite Z.sub_0_r; exact V416|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [eassumption|]. split; [exact EXC3|]. split; [clear - LEX3; lia|].
assert (ESB : sbsub_bits wb_submode3 b = b2) by (rewrite EB2; unfold P; rewrite EID; reflexivity).
rewrite ESB. split; [exact REP3|]. split; [exact OK2| exact ACA3].

rewrite EID in IDC, OBSM2.
assert (LO4 : lo <= usp + -1312 - 224 - 4192) by (clear - LOR2; lia).
cps_seg (sbl_e7b usp lo (usp + -1312) S OUT A f sf MODE 160 sub (usp + -1312 + 32) v s a pad1 is2 xs3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2
SL HD EFS CFG IDC OBS2 S8 SPOS SOFF SBLO EMO EMODE OBM2 OBSM2 LC2 eq_refl EXC2 LEX2 OBEX2 CC2 ST2 LO4 ltac:(clear; lia) LOSH SPH U32 HB32' MI2 RS2).
destruct POST as (m3 & xt03 & xt13 & xt23 & xa23 & xa33 & xa43 & xa53 & xa63 & xa73 & xt33 & xt43 & xt53 & xt63 & F3 & fc3 & ex3 & jh3
& -> & MU3 & WM3 & MI3 & ST3 & FRM3 & SL3 & EXC3 & LEX3 & HULL3).
clear SL EXC2 LEX2 OBEX2 OBS2 OBM2 OBSM2 LC2 CC2 ST2.
lazymatch type of MU3 with munch ?W _ _ => assert (OF3 : offsh W) by (cbn; clear - LOR2 LOSH USPT; unfold SH_LO, SH_HI, USTACK_TOP in *; lia) end.
assert (OBA2 : aobj asegs m2 A BITS_SIZEOF) by (split; [lia|]; split; [clear - ALO LOR2 USPT; unfold APP_TOP, USTACK_TOP, BITS_SIZEOF in *; lia| exact ACA2]).
pose proof (aobj_munch asegs _ m2 m3 A BITS_SIZEOF OBA2 MU3 (shfree_of_aobj asegs _ m2 A BITS_SIZEOF OF3 OBA2)) as (_ & _ & ACA3).
clear OF3 ACA2 OBA2.
cps_seg_post.
rename ART into ART3.
assert (RR2 : alloca_rr (usp + -1312 + -192) 160 = usp + -1312) by (unfold alloca_rr; clear - U32; Z.div_mod_to_equations; lia).
cps_rt (APO Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (usp + -1312 + -192) 160 lo).
{ rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia). lia. }
{ rewrite RR2. exact POA. }
{ rewrite FRE2. exact FRN. }
{ unfold call_ok. rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia).
split; [exact ST3|]. split; [exact LOWS|]. split; [clear - LOR2; unfold RT_STACK; lia|]. split; [clear - USPT; unfold USTACK_TOP in *; lia|].
clear - U32; Z.div_mod_to_equations; lia. }
intros c4 (Σ4 & Hc4 & PO4 & LV4 & FRS4 & SP4 & CR4).
destruct (ASTA_unpack RT Σ4 PMc _ c4 Hc4) as (ms4 & PO & Hc'); clear Hc4; cbv beta in PO.
destruct PO as (m4 & v04 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ACI4 & ACT4).
cps_ret RS4.
rewrite unsigned_lit in ST4, PRES4 by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia).
clear Hc0.
assert (FA2' : A + 48 <= fh + fs_size kh - 8) by (clear - FA2; unfold BITS_SIZEOF in *; lia).
pres_transport_g PRES4 ltac:(ulc).
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m3 =>
assert (PF4 : rt_pres_fp L Fr U W0 m0 m4)
by (apply (pres_fp_trans _ _ _ _ m0 m3 m4 PF);
apply (pres_fp_mono _ _ _ _ _ _ _ m3 m4 (pres_fp_of_pres _ _ _ W0 m3 m4 PRES4)); [intros e He; rewrite LVE2; exact He | intros e He; rewrite FRE2; exact He | lia]) end.
clear PF. rename PF4 into PF.
pose proof (ACT4 A BITS_SIZEOF ACA3 ltac:(clear - ALO48 LOR2 USPT; unfold USTACK_TOP, BITS_SIZEOF in *; lia) ltac:(left; clear - ALO48 LOR2; unfold BITS_SIZEOF in *; lia)) as ACA4.
clear ACA3 ACT4 PRES4 MU3 ST3 ART3 MI3.
pose proof LV4 as LVE4. pose proof FRS4 as FRE4. cps_sigma LV4 FRS4 SP4.

destruct (af_acc_live RT AF Σ4 m4 S 160 ART4 INL) as (_ & ACS4).
assert (OBS4 : aobj asegs m4 S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP, USTACK_TOP in *; lia| exact ACS4]).
cps_seg (sbl_e8 usp lo (usp + -1312 + -224) S OUT A f sf MODE 160 sub (usp + -1312 + -192) (usp + -1312 + 32) _ s a xs3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4
SL3 HD EFS OBS4 S8 SPOS SOFF SBLO ltac:(clear - LOR2; lia) ltac:(clear; lia) LOSH SPH MI4).
destruct POST as (m5 & -> & MU5 & WM5 & MI5 & SL5).
clear SL3 OBS4 ACS4.
lazymatch type of MU5 with munch ?W _ _ => assert (OF5 : offsh W) by (cbn; clear - LOR2 LOSH USPT; unfold SH_LO, SH_HI, USTACK_TOP in *; lia) end.
assert (OBA4 : aobj asegs m4 A BITS_SIZEOF) by (split; [lia|]; split; [clear - ALO LOR2 USPT; unfold APP_TOP, USTACK_TOP, BITS_SIZEOF in *; lia| exact ACA4]).
pose proof (aobj_munch asegs _ m4 m5 A BITS_SIZEOF OBA4 MU5 (shfree_of_aobj asegs _ m4 A BITS_SIZEOF OF5 OBA4)) as (_ & _ & ACA5).
assert (OBI4 : aobj asegs m4 (usp + -1312 + -192) 160) by (split; [clear - LOR2 LOSH; lia|]; split; [clear - USPT; unfold APP_TOP, USTACK_TOP in *; lia| exact ACI4]).
pose proof (aobj_munch asegs _ m4 m5 _ 160 OBI4 MU5 (shfree_of_aobj asegs _ m4 _ 160 OF5 OBI4)) as OBI5.
clear OF5 OBA4 ACA4 OBI4 ACI4.
cps_seg_post.
rename ART into ART5.

apply (rw_cells_split_CB asegs _ _ [] 224 _ [] [32; 160; 32]%nat) in HULL3; [| reflexivity]. cbn [mk_CB_cells app] in HULL3.
destruct (rw_cells_uncons asegs _ _ _ _ HULL3) as (HLZ2 & HULL3'). destruct (rw_cells_uncons asegs _ _ _ _ HULL3') as (HBODY2 & HRZ2). clear HULL3 HULL3'.
cbn [csize] in HBODY2, HRZ2.
replace (usp + -1312 + -224 + Z.of_nat 32) with (usp + -1312 + -192) in HBODY2, HRZ2 by lia.
replace (usp + -1312 + -192 + Z.of_nat 160) with (usp + -1312 + -32) in HRZ2 by lia.
destruct HBODY2 as [_ WRB2]. cbn [cells_size csize Nat.add] in WRB2. replace (Z.of_nat (160 + 0)) with 160 in WRB2 by lia.
assert (INPI2 : In (usp + -1312 + -192, 160) (rt_pois RT Σ4)) by (rewrite PO4; left; reflexivity).
cps_rt (MEMS Σ4 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (usp + -1312 + -192) 160 z8 lo).
{ unfold checked_dst. rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia). split; [intros _; split|split].
- exact (proj2 (proj2 OBI5)).
- right; right; left. clear - LOWS LOR2 USPT; unfold STACK_WIN, USTACK_TOP in *; lia.
- intros i Hi. left. clear - Hi LOR2 USPT; unfold USTACK_TOP in *; lia.
- exact WRB2. }
{ unfold call_ok. rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia).
split; [exact ST4|]. split; [exact LOWS|]. split; [clear - LOR2; unfold RT_STACK; lia|]. split; [clear - USPT; unfold USTACK_TOP in *; lia|].
clear - U32; Z.div_mod_to_equations; lia. }
intros c6 Hc6. unfold icpt_postF in Hc6.
destruct (ASTA_unpack RT Σ4 PMc _ c6 Hc6) as (ms6 & PO & Hc'); clear Hc6; cbv beta in PO.
destruct PO as (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & BYZ6).
cps_ret RS6.
rewrite unsigned_lit in ST6, PRES6 by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia).
clear Hc.
pres_transport_g PRES6 ltac:(ulc).
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m5 =>
assert (PF6 : rt_pres_fp L Fr U W0 m0 m6)
by (apply (pres_fp_trans _ _ _ _ m0 m5 m6 PF);
apply (pres_fp_of_pres_ex_gen _ _ _ _ _ _ _ _ _ m5 m6 PRES6); [intros e He; rewrite LVE4, LVE2; exact He | intros e He; rewrite FRE4, FRE2; exact He | lia |];
intros x Hx _ Hd; pose proof (SPL x Hx) as SX; clear - SX Hd LOWS SP4 SP2 LOR2; rewrite <- SP2, <- SP4 in SX; lia) end.
clear PF. rename PF6 into PF.
assert (FH8 : fh mod 8 = 0) by (clear - FH64; Z.div_mod_to_equations; lia).
pose proof (fs_size_mod8 kh) as FK8.
assert (DOFF2 : usp + -1312 + -192 + 160 <= SH_LO \/ SH_HI <= usp + -1312 + -192) by (right; clear - LOR2 LOSH; unfold SH_HI in *; lia).
pose proof (acc_pres_ex_frame _ _ _ _ _ m5 m6 fh kh A BITS_SIZEOF PRES6 INFH FH8 FK8 ltac:(lia) FA1 ltac:(clear - FA2; lia)
ltac:(clear - ALO LOR2 USPT; unfold APP_TOP, USTACK_TOP, BITS_SIZEOF in *; lia) DOFF2 ACA5) as ACA6.
assert (I2V : exists ws, length ws = 40%nat /\ rw_cells asegs m6 (usp + -1312 + -192) (f32 ws)).
{ apply (rw_cells_CB_f32 asegs m6 _ 40 (repeat z8 (Z.to_nat 160))).
split; [split; [split; [cbn [cell_wf]; rewrite repeat_length; reflexivity| exact I]| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact BYZ6]|].
cbn [cells_size csize Nat.add]. exact (wr_at_transport asegs m5 m6 _ _ WRB2 WM6). }
destruct I2V as (iz6 & LIZ6 & IZC6).
clear DOFF2 ACA5 PRES6 WRB2 BYZ6 OBI5 MU5 ST4 ART5 MI5.

destruct (af_acc_live RT AF Σ4 m6 S 160 ART6 INL) as (_ & ACS6).
assert (OBS6 : aobj asegs m6 S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP, USTACK_TOP in *; lia| exact ACS6]).
pose proof (AF_LIB Σ4 m6 ART6) as LC6.
assert (OBM6 : aobj asegs m6 MODE 216).
{ rewrite EMODE, EMO; cbn [sbmode_struct]. apply (aobj_lit RT AF Σ4 m6 _ 216 ART6);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_sb_wb_mode; lia | unfold A_sb_wb_mode, APP_TOP; lia]. }
assert (OBSM6 : aobj asegs m6 (sb_sub_addr 4) 88).
{ cbn [sb_sub_addr Z.eqb Pos.eqb]. apply (aobj_lit RT AF Σ4 m6 _ 88 ART6);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_wb_submode4; lia | unfold A_wb_submode4, APP_TOP; lia]. }
cps_seg (sbl_e9 usp lo (usp + -1312 + -224) S OUT A f sf MODE 160 sub (usp + -1312 + -192) (usp + -1312 + 32) _ s a pad1 xs3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6
SL5 CFG IDC OBS6 S8 SPOS SOFF SBLO EMO EMODE OBM6 OBSM6 LC6 ltac:(clear - LOR2; lia) ltac:(clear; lia) LOSH SPH MI6).
destruct POST as (xa76 & ->).
clear OBS6 ACS6 OBM6 OBSM6.
assert (POK2 : scb_params_ok split_cb_high).
{ pose proof scb_params_ok_all as ALL. rewrite Forall_forall in ALL. apply ALL; cbn [In]; repeat (first [left; reflexivity | right]). }
assert (PARF2 : ro_cells asegs m6 A_split_cb_high (scb_par_cellsA split_cb_high) /\ A_split_cb_high mod 8 = 0 /\ 0x10000 <= A_split_cb_high
/\ A_split_cb_high + 24 <= IMG_TOP /\ In (A_split_cb_high, 24) ACC_LITS).
{ split; [exact (lib_const m6 A_split_cb_high (scb_par_cellsA split_cb_high) LC6 ltac:(lc_in))|]. unfold A_split_cb_high, IMG_TOP. split; [reflexivity|]. split; [lia|]. split; [lia|].
unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]). }
assert (REP6 : bits_rep asegs m6 A D b2).
{ split; [exists rj2; split; [exact Lrj2| unfold bits_cells; exact OBJ2]|].
split; [exists bs2; split; [apply (proj2 (u8arr_rw_CB m6 D bs2)); exact DAT2| exact Hbs2]| exact SIDE2]. }
clear OBJ2 DAT2.
assert (POA4 : pois_above (rt_pois RT Σ4) (usp + -1312 + -224)).
{ rewrite PO4. intros e [<-|He]; [unfold pz_lo; cbn [fst]; lia| specialize (POA e He); lia]. }
cps_rt (INNV split_cb_high POK2 Σ4 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 A D b2
(usp + -1312 + -192) (S + 132) A_split_cb_high lo S 160 PD ND fh kh iz6 seed2 (Z_to_bv 64 0)).
{ right. exact INPI2. }
{ split; [exact FA1|]. split; [exact FA2|]. split; [exact ACA6| exact A4]. }
{ unfold hidp; left; clear - ALO LOR2; unfold BITS_SIZEOF in *; lia. }
{ rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia). exact ST6. }
{ rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia). clear - ROOM; unfold RT_STACK, SB_LOOP_STACK, INNOV_STACK in *; lia. }
{ rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia). clear - USPT; unfold USTACK_TOP in *; lia. }
{ rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia). clear - U32; Z.div_mod_to_equations; lia. }
{ rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia). exact POA4. }
intros c7 (Σ7 & Hc7 & LV7 & FRS7 & SP7 & CR7 & PO7).
cps_unpack_lib Hc7 as (v7 & m7 & is7 & seed7 & RS7 & (ART7 & MI7 & WM7 & ST7) & PRES7 & IZC7 & LIZ7 & SEEDC7 & REP7 & OK7 & ACI7 & ACA7).
clear IZC6 LIZ6 SEEDC2 REP6 ACA6.
cps_tr_lib PRES7.
clear Hc.
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m6 =>
assert (PF7 : rt_pres_fp L Fr U W0 m0 m7)
by (apply (pres_fp_trans _ _ _ _ m0 m6 m7 PF);
apply (pres_fp_of_pres_fp _ _ _ _ _ _ _ _ m6 m7 PRES7); [intros e He; rewrite LVE4, LVE2; exact He | intros e He; rewrite FRE4, FRE2; exact He | lia |];
intros x Hx Ho; cbn [outside] in Ho |- *; decompose [and] Ho; pose proof (SPL x Hx) as SX;
split; [intros Hin; clear - SX Hin LOWS SP4 SP2 LOR2; rewrite <- SP2, <- SP4 in SX; lia|];
split; [intros Hin; match goal with H : ~ (S + 132 <= x < S + 136) |- _ => apply H; clear - Hin; lia end|];
split; [assumption | exact I]) end.
clear PF. rename PF7 into PF.
pose proof LV7 as LVE7. pose proof FRS7 as FRE7. cps_sigma LV7 FRS7 SP7.

destruct (af_acc_live RT AF Σ7 m7 S 160 ART7 INL) as (_ & ACS7).
assert (OBS7 : aobj asegs m7 S 160) by (split; [lia|]; split; [clear - SBLO LOR2 USPT; unfold APP_TOP, USTACK_TOP in *; lia| exact ACS7]).
assert (OBI7 : aobj asegs m7 (usp + -1312 + -192) 160) by (split; [clear - LOR2 LOSH; lia|]; split; [clear - USPT; unfold APP_TOP, USTACK_TOP in *; lia| exact ACI7]).
assert (INPX7 : In (usp + -1312 + 32, 160) (rt_pois RT Σ7)) by (rewrite PO7, PO4, PO2; right; exact INPX).
assert (OBX7 : aobj asegs m7 (usp + -1312 + 32) 160)
by (split; [clear - LOR2 LOSH; lia|]; split; [clear - USPT; unfold APP_TOP, USTACK_TOP in *; lia| exact (af_acc_pois RT AF Σ7 m7 _ _ ART7 INPX7)]).
pose proof (af_client_consts RT AF Σ7 m7 ART7) as CC7.
cps_seg (sbl_e10 usp lo (usp + -1312 + -224) S OUT A f sf MODE 160 sub (usp + -1312 + -192) (usp + -1312 + 32) _ s a ex3 is7 xs3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m7
SL5 eq_refl ltac:(cbn [v_120 sbv_416 sbv_120]; f_equal; lia) HD EFS OBS7 S8 SPOS SOFF SBLO ltac:(clear; lia) IZC7 LIZ7 OBI7 ltac:(clear; lia) EXC3 LEX3 OBX7
CC7 ST7 ltac:(clear - LOR2; lia) ltac:(clear; lia) LOSH SPH ltac:(clear - U32; Z.div_mod_to_equations; lia) MI7 RS7).
destruct POST as (m8 & xt08 & xt18 & xt28 & xa28 & xa38 & xa48 & xa58 & xa68 & xa78 & xt38 & xt48 & xt58 & xt68 & F8 & fc8 & ex8 & i28
& -> & MU8 & WM8 & MI8 & ST8 & FRM8 & EXC8 & LEX8 & IZC8 & LIZ8).
clear EXC3 LEX3 IZC7 LIZ7 OBS7 ACS7 OBI7 OBX7 CC7 ACI7.
lazymatch type of MU8 with munch ?W _ _ => assert (OF8 : offsh W) by (cbn; clear - LOR2 LOSH USPT; unfold SH_LO, SH_HI, USTACK_TOP in *; lia) end.
assert (OBA7 : aobj asegs m7 A BITS_SIZEOF) by (split; [lia|]; split; [clear - ALO LOR2 USPT; unfold APP_TOP, USTACK_TOP, BITS_SIZEOF in *; lia| exact ACA7]).
pose proof (aobj_munch asegs _ m7 m8 A BITS_SIZEOF OBA7 MU8 (shfree_of_aobj asegs _ m7 A BITS_SIZEOF OF8 OBA7)) as (_ & _ & ACA8).
clear OF8 OBA7 ACA7.
remember (innov_bits (InnovSplitCbShapeSignUnquant split_cb_high) b2) as b3 eqn:EB3.
destruct REP7 as ((rj3 & Lrj3 & OBJ3) & (bs3 & DAT3 & Hbs3) & SIDE3). unfold bits_cells in OBJ3. apply (proj1 (u8arr_rw_CB m7 D bs3)) in DAT3.
assert (SZB3 : sb_buf_size b3 = sb_buf_size b).
{ rewrite EB3. cbn [innov_bits]. pose proof OK2 as OKb2.
rewrite (proj2 (SCBSZ (Z.to_nat (scb_nb_subvect split_cb_high)) (scb_have_sign split_cb_high) (scb_shape_bits split_cb_high) b2 OKb2 ltac:(cbn; lia))). exact SZB2. }
assert (LBS3 : Z.of_nat (length bs3) = sb_buf_size b3)
by (pose proof OK7 as OK'; unfold bits_ok in OK'; rewrite Hbs3, zlength_map_unsigned in OK'; clear - OK'; lia).
assert (DLO3 : D + Z.of_nat (length bs3) <= lo) by (clear - LBS3 SZB3 DLO; lia).
cps_seg_post.
rename ART into ART8.

cps_rt (AUN Σ7 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m8 (usp + -1312 + -224) (usp + -1312 + -224 + 224) lo).
{ rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia). lia. }
{ intros e He. rewrite PO7, PO4 in He. destruct He as [<-|He].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR2. lia.
- right. specialize (POA e He). lia. }
{ unfold call_ok. rewrite unsigned_lit by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia).
split; [exact ST8|]. split; [exact LOWS|]. split; [clear - LOR2; unfold RT_STACK; lia|]. split; [clear - USPT; unfold USTACK_TOP in *; lia|].
clear - U32; Z.div_mod_to_equations; lia. }
intros c9 (Σ9 & Hc9 & PO9 & LV9 & FRS9 & SP9 & CR9).
destruct (ASTA_unpack RT Σ9 PMc _ c9 Hc9) as (ms9 & PO & Hc'); clear Hc9; cbv beta in PO.
destruct PO as (m9 & v09 & RS9 & (ART9 & MI9 & WM9 & ST9) & PRES9 & ACT9).
cps_ret RS9.
rewrite unsigned_lit in ST9, PRES9 by (clear - LOR2 LOSH USPT; unfold USTACK_TOP in *; lia).
clear Hc.
pres_transport_g PRES9 ltac:(ulc).
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W0 ?m0 m8 =>
assert (PF9 : rt_pres_fp L Fr U W0 m0 m9)
by (apply (pres_fp_trans _ _ _ _ m0 m8 m9 PF);
apply (pres_fp_mono _ _ _ _ _ _ _ m8 m9 (pres_fp_of_pres _ _ _ W0 m8 m9 PRES9));
[intros e He; rewrite LVE7, LVE4, LVE2; exact He | intros e He; rewrite FRE7, FRE4, FRE2; exact He | lia]) end.
clear PF. rename PF9 into PF.
pose proof (ACT9 A BITS_SIZEOF ACA8 ltac:(clear - ALO48 LOR2 USPT; unfold USTACK_TOP, BITS_SIZEOF in *; lia) ltac:(left; clear - ALO48 LOR2; unfold BITS_SIZEOF in *; lia)) as ACA9.
clear ACA8 ACT9 PRES9.

assert (HJ : rw_cells asegs m9 (usp + -1312 + -224) ([CB 32 (firstn 32 jh3)] ++ f32 i28 ++ [CB 32 (firstn 32 (skipn 160 (skipn 32 jh3)))])).
{ apply rw_cells_join; [exact HLZ2|].
replace (usp + -1312 + -224 + Z.of_nat (cells_size [CB 32 (firstn 32 jh3)])) with (usp + -1312 + -192) by (cbn [cells_size csize]; lia).
apply rw_cells_join; [exact IZC8|].
replace (usp + -1312 + -192 + Z.of_nat (cells_size (f32 i28))) with (usp + -1312 + -32) by (rewrite cells_size_f32, LIZ8; lia). exact HRZ2. }
apply rw_cells_to_CB in HJ.
lazymatch type of HJ with rw_cells _ _ _ [CB ?n ?bs] => assert (E224 : n = 224%nat) by (rewrite ?cells_size_app, ?cells_size_f32, LIZ8; reflexivity); rewrite E224 in HJ end.
clear HLZ2 HRZ2 IZC8.
cps_seg (sbl_e11 usp lo (usp + -1312 + -224) S sub (usp + -1312 + 32) MODE _ xs3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m9
HJ ST9 ltac:(clear - LOR2; lia) ltac:(clear; lia) SPH).
destruct POST as (-> & ST10).
replace (usp + -1312 + -224 + 224) with (usp + -1312) in * by lia.
assert (REP9 : bits_rep asegs m9 A D b3).
{ split; [exists rj3; split; [exact Lrj3| unfold bits_cells; exact OBJ3]|].
split; [exists bs3; split; [apply (proj2 (u8arr_rw_CB m9 D bs3)); exact DAT3| exact Hbs3]| exact SIDE3]. }
apply Hk. exists Σ9. split.
2: { rewrite LV9, LVE7, LVE4, LVE2, FRS9, FRE7, FRE4, FRE2, SP9, SP7, SP4, SP2, CR9, CR7, CR4, CR2, PO9, PO7, PO4, PO2.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
rewrite pois_drop_cons_below by (unfold pz_lo; cbn [fst]; lia). apply pois_drop_above. rewrite <- PO2. exact POA. }
eapply ASTA_conseq; [eassumption|]. intros ms <-.
exists m9. do 12 eexists. exists (Z_to_bv 64 (usp + -1312)). do 6 eexists. exists (sbv_416 (sbv_120 v (Z_to_bv 64 (usp + -1312))) (Z_to_bv 64 (usp + -1312 + -224))), seed7, ex8.
split; [reflexivity|].
split; [exact FRM8|]. split; [split; [exact ART9|]; split; [exact MI9|]; split; [cps_wmono| exact ST10]|].
split; [exact PF|]. split; [exact SL5|]. split; [exact V296|]. split; [cbn [v_416 sbv_416]; unfold sbl_v416A; cbn [wb_submode4 sm_double_codebook Z.eqb]; f_equal; lia|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact SEEDC7|]. split; [exact EXC8|]. split; [clear - LEX8; lia|].
assert (ESB : sbsub_bits wb_submode4 b = b3) by (rewrite EB3, EB2; unfold P; rewrite EID; reflexivity).
rewrite ESB. split; [exact REP9|]. split; [exact OK7| exact ACA9].
Qed.
End DA.
