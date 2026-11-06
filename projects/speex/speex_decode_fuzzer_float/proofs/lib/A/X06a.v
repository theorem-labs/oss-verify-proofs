(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1cr X1da X1dg X1df X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require X1nu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05u X05t
X081 X05l X05m X09f X06d X069 X063 X082 X08y X0b1 X0b0 X068 X0az.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X12b X0z5 X0wl X0wn X0wm X0ys X0x2 X0zo X0yt X0zq X11l X11k X0x1.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zo OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac pk_blocks AG :=
lazymatch type of AG with
| agree_blocks bsegs ?m ?m' ?LBD =>
repeat match goal with
| H : ?c -> dec_exc_ready bsegs m ?S ?d, R : DREP ?O ?ST m ?S ?d LBD |- _ =>
let H' := fresh "EXR" in
assert (H' : c -> dec_exc_ready bsegs m' S d) by (let E := fresh in intros E; exact (dec_exc_ready_agree bsegs _ _ _ _ _ _ _ _ d O ST m m' S LBD R (H E) AG));
clear H
end;
repeat match goal with
| R : DREP ?O ?ST m ?S ?d LBD |- _ => eapply decst_rep_agree in R; [| exact AG]
end
end.
Ltac pk_io ERR_rep OUT_rep KEEP :=
lazymatch type of KEEP with
| forall P, fp_local ?IO_FP P -> P ?m -> P ?m' =>
repeat match goal with
| H : ERR_rep m |- _ => apply (KEEP ERR_rep ltac:(assumption)) in H
| H : forall so, OUT_rep so ?m0 -> OUT_rep so m |- _ =>
let H' := fresh "OUTK" in
assert (H' : forall so, OUT_rep so m0 -> OUT_rep so m') by (let so := fresh in let X := fresh in intros so X; exact (KEEP (OUT_rep so) ltac:(auto) (H so X)));
clear H
end
end.

Ltac pk_munch MU WM LBD ERR_rep OUT_rep IO_FP IO_img tacB tacI :=
lazymatch type of MU with
| munch ?W ?m ?m' =>
let AG := fresh "AG" in
assert (AG : agree_blocks bsegs m m' LBD)
by (apply (agree_blocks_of_munch bsegs W m m' LBD MU WM); let b := fresh "b" in let x := fresh "x" in let Hb := fresh "Hb" in let Hx := fresh "Hx" in
intros b x Hb Hx; tacB b x Hb Hx);
pk_blocks AG; clear AG;
let KEEP := fresh "KEEP" in
assert (KEEP : forall P, fp_local IO_FP P -> P m -> P m')
by (let P := fresh "P" in let L := fresh "L" in let Pm := fresh "Pm" in
intros P L Pm; apply (fp_local_munch IO_FP P W m m' L IO_img MU); [| exact Pm];
let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; unfold SEGTOP_A in Hx; tacI x Hx);
pk_io ERR_rep OUT_rep KEEP; clear KEEP
end.

Definition dec_target (d : dec_state bptr) : Z := match d with DecNB _ => A_nb_decode | DecSB _ _ => A_sb_decode end.
Definition mode_dec (MP : Z) : Z := if MP =? A_speex_nb_mode then A_nb_decode else A_sb_decode.

Lemma dec_dispatch_w : forall (ENTRY S MP usp lo : Z)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
(ENTRY = A_speex_decode_native \/ ENTRY = A_speex_decode) ->
(MP = A_speex_nb_mode \/ MP = A_speex_wb_mode \/ MP = A_speex_uwb_mode) ->
rw_cells bsegs m S [C8 (Z_to_bv 64 MP)] -> aobj bsegs m S 8 -> S mod 8 = 0 -> 0 < S -> aobj bsegs m MP 96 ->
stk bsegs m lo usp -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
S + 8 <= lo -> (S + 8 <= SH_LO \/ SH_HI <= S) ->
client_constsB m -> lib_consts m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (xt1 xa3 xa4 xa5 : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 xt1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 xa3 xa4 xa5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (mode_dec MP)) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo usp)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ENTRY) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros HE HM P0 OBS S8 SPOS OBM ST LO LOS SPH SLO SOFF (G1 & G2 & _) LC MI.
unfold gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'.
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 16%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
destruct HM as [-> | [-> | ->]];
[ pose proof (lib_const m A_speex_nb_mode LC_speex_nb_mode LC ltac:(lc_in)) as ND; unfold LC_speex_nb_mode in ND;
replace (mode_dec A_speex_nb_mode) with 0xa16a8 by reflexivity;
assert (AL8 : A_speex_nb_mode mod 8 = 0) by reflexivity;
assert (MPR : 0x10000 <= A_speex_nb_mode /\ A_speex_nb_mode + 96 <= 0x65a180) by (unfold A_speex_nb_mode; lia);
set (MPv := A_speex_nb_mode) in *; clearbody MPv
| pose proof (lib_const m A_speex_wb_mode LC_speex_wb_mode LC ltac:(lc_in)) as ND; unfold LC_speex_wb_mode in ND;
replace (mode_dec A_speex_wb_mode) with 0xbe6c0 by reflexivity;
assert (AL8 : A_speex_wb_mode mod 8 = 0) by reflexivity;
assert (MPR : 0x10000 <= A_speex_wb_mode /\ A_speex_wb_mode + 96 <= 0x65a180) by (unfold A_speex_wb_mode; lia);
set (MPv := A_speex_wb_mode) in *; clearbody MPv
| pose proof (lib_const m A_speex_uwb_mode LC_speex_uwb_mode LC ltac:(lc_in)) as ND; unfold LC_speex_uwb_mode in ND;
replace (mode_dec A_speex_uwb_mode) with 0xbe6c0 by reflexivity;
assert (AL8 : A_speex_uwb_mode mod 8 = 0) by reflexivity;
assert (MPR : 0x10000 <= A_speex_uwb_mode /\ A_speex_uwb_mode + 96 <= 0x65a180) by (unfold A_speex_uwb_mode; lia);
set (MPv := A_speex_uwb_mode) in *; clearbody MPv ];
(destruct HE as [-> | ->]; unfold A_speex_decode_native, A_speex_decode).
1: bato 0x98b70. 2: bato 0x98c58. 3: bato 0x98b70. 4: bato 0x98c58. 5: bato 0x98b70. 6: bato 0x98c58.
all: do 2 astep; release_frame FR ST usp.
1, 2: bato 0xa16a8. 3, 4, 5, 6: bato 0xbe6c0.
all: apply evt_done; do 5 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI| exact ST].
Qed.

Lemma drep_mode_cell : forall OUT STEREO (m : mem) S (d : dec_state bptr) LBD, DREP OUT STEREO m S d LBD ->
exists MP, mode_dec MP = dec_target d /\ (MP = A_speex_nb_mode \/ MP = A_speex_wb_mode \/ MP = A_speex_uwb_mode)
/\ rw_cells bsegs m S [C8 (Z_to_bv 64 MP)].
Proof.
intros OUT STEREO m S [st | s low] LBD R; cbn [decst_rep] in R.
- destruct R as (_ & _ & _ & _ & j & _ & _ & C). exists A_speex_nb_mode. split; [reflexivity|]. split; [left; reflexivity|].
unfold nb_cells, nb_hdr_cells in C. cbn [app] in C. exact (proj1 (rw_cells_uncons _ _ _ _ _ C)).
- destruct R as (a & j & LBL & _ & _ & _ & INV & _ & C & _).
apply sb_pieces_iff in C. destruct C as (HD & _). unfold sbp_hdr in HD. apply rw_cells_uncons in HD. destruct HD as (HD & _).
destruct INV as (IMODE & _). destruct IMODE as [E|E]; rewrite E in HD; cbn [sb_mode_ptr] in HD.
+ exists A_speex_wb_mode. split; [reflexivity|]. split; [right; left; reflexivity| exact HD].
+ exists A_speex_uwb_mode. split; [reflexivity|]. split; [right; right; reflexivity| exact HD].
Qed.

Section DecDispatch.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Theorem dec_cps_dispatch : forall ENTRY (d : dec_state bptr), (ENTRY = A_speex_decode_native \/ ENTRY = A_speex_decode) ->
dec_cps_at RT OUT_rep ERR_rep IO_FP (dec_target d) d -> dec_cps_at RT OUT_rep ERR_rep IO_FP ENTRY d.
Proof using AF ERR_loc OUT_loc IO_img AF_LIB.
intros ENTRY d HE TG. unfold dec_cps_at.
intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S A D LBD b lo fh PD ND kh ows stb q q' ret d' b' PRUN EA0 EA1 EA2 ETP REP DEP ISV NEST NDUP LAL8 LIVE BREP BOK INPD PD1 PD2 PDB OC LOWS STB INFH FA FO FS
HAO HAS HOS FD2 ERR0 SSP0 FRM CRD POA ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
destruct (TG Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S A D LBD b lo fh PD ND kh ows stb q q' ret d' b' PRUN EA0 EA1 EA2 ETP REP DEP ISV NEST NDUP LAL8 LIVE BREP BOK INPD PD1 PD2 PDB OC LOWS STB INFH FA FO FS
HAO HAS HOS FD2 ERR0 SSP0 FRM CRD POA ART0 MI0 FRM0 ST0 LOW LOR SPT SPA) as (bs & EB & _).
exists bs. split; [exact EB|].
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc. subst a0.

destruct (drep_mode_cell OUT STEREO m S d LBD REP) as (MP & EMD & HMP & MPC).
destruct (decst_rep_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP) as (rest & ELB).
assert (INS : In (S, match d with DecNB _ => NBSTATE_SIZEOF | DecSB _ _ => SBSTATE_SIZEOF end) (rt_live RT Σ)).
{ specialize (LIVE (match d with DecNB st => nb_blk st | DecSB s _ => sbd_blk s end, S, match d with DecNB _ => NBSTATE_SIZEOF | DecSB _ _ => SBSTATE_SIZEOF end)).
rewrite ELB in LIVE. exact (LIVE ltac:(left; reflexivity)). }
assert (SZS : 8 <= match d with DecNB _ => NBSTATE_SIZEOF | DecSB _ _ => SBSTATE_SIZEOF end) by (destruct d; unfold NBSTATE_SIZEOF, SBSTATE_SIZEOF; lia).
set (SZ := match d with DecNB _ => NBSTATE_SIZEOF | DecSB _ _ => SBSTATE_SIZEOF end) in *. clearbody SZ.
destruct (live_below_lo RT AF Σ m S SZ lo ART0 INS LOW) as (SPOS & SLO & LOS).
destruct (af_acc_live RT AF Σ m S SZ ART0 INS) as (_ & ACS).
pose proof (live_facts RT AF Σ m S SZ ART0 INS) as (_ & _ & SIMG & SHI).
assert (S8 : S mod 8 = 0) by (exact (proj2 (decst_rep_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP))).
assert (DSP : 0 <= dec_stack d) by (clear; induction d; cbn [dec_stack]; unfold NBDEC_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK; lia).
assert (OBS : aobj bsegs m S 8) by (split; [lia|]; split; [clear - SLO LOR SPT DSP SZS; unfold RT_STACK, APP_TOP, USTACK_TOP in *; lia| exact (acc_sub bsegs m S SZ S 8 ACS ltac:(lia) ltac:(lia))]).
pose proof (AF_LIB Σ m ART0) as LC0. pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (OBM : aobj bsegs m MP 96).
{ destruct HMP as [-> | [-> | ->]]; (apply (aobj_lit RT AF Σ m _ 96 ART0);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode; lia
| unfold A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode, APP_TOP; lia]). }
assert (SOFF : S + 8 <= SH_LO \/ SH_HI <= S) by (clear - SHI SZS; unfold SH_LO, SH_HI in *; lia).
assert (LO16 : lo <= usp - 16) by (clear - LOR DSP; unfold RT_STACK in LOR; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m) as PF.
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.
cps_seg (dec_dispatch_w ENTRY S MP usp lo).
destruct POST as (m1 & xt1 & xa3 & xa4 & xa5 & -> & MU & WM & MI1 & ST1).

destruct BREP as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m D bsb)) in BDAT.
destruct FA as (FA1 & FA2 & ACA & AAL). destruct FO as (FO1 & FO2 & ACO & OAL). destruct FS as (FS1 & FS2 & ACST & SAL).
destruct SSP0 as (gssp & SSP1 & SSP2).
pose proof (fun so (H : OUT_rep so m) => H) as OUTK.
pk_munch MU WM LBD ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => let H1 := fresh in destruct (live_below_lo RT AF Σ m _ _ lo ART0 (LIVE b Hb) LOW) as (_ & H1 & _);
clear - H1 Hx LO16; cbn [outside]; split; [lia | exact I])
ltac:(fun x Hx => clear - Hx LO16 LOS; cbn [outside]; split; [unfold SH_HI in LOS; lia | exact I]).
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
destruct (frame_below_lo RT AF Σ m fh kh lo ART0 INFH LOW) as (BF1 & BF2 & _).
destruct (live_below_lo RT AF Σ m PD ND lo ART0 INPD LOW) as (_ & BLPD & _).
assert (Lbsb : Z.of_nat (length bsb) = sb_buf_size b) by (pose proof BOK as OK'; unfold bits_ok in OK'; rewrite Hbsb, zlength_map_unsigned in OK'; clear - OK'; lia).
assert (BDLO : D + Z.of_nat (length bsb) <= lo) by (clear - Lbsb PD2 BLPD; lia).
unfold BITS_SIZEOF in *.
cps_seg_post.

assert (OF16 : offsh [(usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
pose proof (frame_facts RT AF Σ m1 fh kh ART INFH) as (FP0 & FP64 & FPIMG & FPHI & _).
assert (ACC1 : forall o n, acc bsegs m o n -> 0 <= o -> o + n <= APP_TOP -> acc bsegs m1 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch bsegs _ m m1 o n (conj H0 (conj H1 H)) MU (shfree_of_offsh _ o n OF16 H0 H1)))). }
assert (FA' : in_frame_obj RT Σ m1 fh kh A 48) by (split; [lia|]; split; [lia|]; split; [apply ACC1; [exact ACA| lia| ulc] | exact AAL]).
assert (FO' : in_frame_obj RT Σ m1 fh kh OUT 8000) by (split; [lia|]; split; [lia|]; split; [apply ACC1; [exact ACO| lia| ulc] | exact OAL]).
assert (FS' : in_frame_obj RT Σ m1 fh kh STEREO 24) by (split; [lia|]; split; [lia|]; split; [apply ACC1; [exact ACST| lia| ulc] | exact SAL]).
assert (BREP1 : bits_rep bsegs m1 A D b).
{ split; [exists rjb; split; [exact Lrjb| unfold bits_cells; exact BOBJ]|].
split; [exists bsb; split; [apply (proj2 (u8arr_rw_CB m1 D bsb)); exact BDAT| exact Hbsb]| exact BSIDE]. }
assert (SSP1' : io_ssp m1) by (exists gssp; split; assumption).
rewrite EMD in Hc0.

destruct (TG Σ F0 fs0 ra (Z_to_bv 64 usp) gp tp t0 xt1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 xa3 xa4 xa5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
OUT STEREO S A D LBD b lo fh PD ND kh ows stb q q' ret d' b' PRUN eq_refl EA1 EA2 ETP REP DEP ISV NEST NDUP LAL8 LIVE BREP1 BOK INPD PD1 PD2 PDB OC LOWS STB INFH FA' FO' FS'
HAO HAS HOS FD2 ERR0 SSP1' FRM CRD) as (bs1 & EB1 & CP1).
1-9: try rewrite <- ESP.
{ exact POA. } { exact ART. } { exact MI1. } { exact FRM0. } { exact ST1. } { exact LOW. } { exact LOR. } { exact SPT. } { exact SPA. }
assert (E1 : bs1 = bs) by (rewrite EB1 in EB; apply app_inv_head in EB; congruence). subst bs1.
refine (rz_cpsE RT Σ (PMfd F0 fs0) _ _ _ T c0 Hc0 CP1 _).
intros c' (Σ' & Hc' & PUR).
apply Hk. exists Σ'. split; [| exact PUR].
apply (ASTA_conseq RT Σ' (PMfd F0 fs0) _ _ c' Hc').
intros ms (m' & ows' & stb' & RS & (ART' & MI' & WM' & ST') & PRS & REST).
exists m', ows', stb'. rewrite <- ESP in ST', PRS, RS.  split; [exact RS|].
split; [refine (conj ART' (conj MI' (conj (wmono_trans _ _ _ _ WM WM') ST'))) |].
split; [exact (pres_fp_trans _ _ _ _ m m1 m' PF PRS) |].
destruct REST as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & OK').
refine (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj R8 (conj R9 (conj R10 (conj R11 _))))))))))).
intros so Hso. exact (OK' so (OUTK0 so Hso)).
Qed.

Theorem dec_cps_induction :
(forall st, dec_cps_at RT OUT_rep ERR_rep IO_FP A_nb_decode (DecNB st)) ->
(forall k, (forall d, (dec_depth d <= k)%nat -> dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode_native d) ->
forall s low, (dec_depth low <= k)%nat -> dec_cps_at RT OUT_rep ERR_rep IO_FP A_sb_decode (DecSB s low)) ->
forall d, dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode_native d /\ dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode d.
Proof using AF ERR_loc OUT_loc IO_img AF_LIB.
intros NBD SBD.
assert (H : forall n d, (dec_depth d <= n)%nat ->
dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode_native d /\ dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode d).
{ induction n as [|n IH]; intros d Hd; [destruct d; cbn [dec_depth] in Hd; lia|].
destruct d as [st | s low].
- split; apply dec_cps_dispatch; [left; reflexivity | exact (NBD st) | right; reflexivity | exact (NBD st)].
- assert (SB : dec_cps_at RT OUT_rep ERR_rep IO_FP A_sb_decode (DecSB s low)).
{ apply (SBD n); [intros d' Hd'; exact (proj1 (IH d' Hd')) | cbn [dec_depth] in Hd; lia]. }
split; apply dec_cps_dispatch; [left; reflexivity | exact SB | right; reflexivity | exact SB]. }
intros d. exact (H _ d (le_n _)).
Qed.
End DecDispatch.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition dec_target (d : dec_state bptr) : Z := match d with DecNB _ => A_nb_decode | DecSB _ _ => A_sb_decode end.
Definition mode_dec (MP : Z) : Z := if MP =? A_speex_nb_mode then A_nb_decode else A_sb_decode.

Lemma dec_dispatch_w : forall (ENTRY S MP usp lo : Z)
(ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
(ENTRY = A_speex_decode_native \/ ENTRY = A_speex_decode) ->
(MP = A_speex_nb_mode \/ MP = A_speex_wb_mode \/ MP = A_speex_uwb_mode) ->
rw_cells asegs m S [C8 (Z_to_bv 64 MP)] -> aobj asegs m S 8 -> S mod 8 = 0 -> 0 < S -> aobj asegs m MP 96 ->
stk asegs m lo usp -> lo <= usp - 16 -> SH_HI <= lo -> usp < 2^63 ->
S + 8 <= lo -> (S + 8 <= SH_LO \/ SH_HI <= S) ->
client_consts m -> lib_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (xt1 xa3 xa4 xa5 : word),
ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 xt1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 xa3 xa4 xa5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (mode_dec MP)) fc None m1 (seg_rom asegs)
/\ munch [(usp + -16, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp)
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ENTRY) fc None m (seg_rom asegs)).
Proof.
intros until m. intros HE HM P0 OBS S8 SPOS OBM ST LO LOS SPH SLO SOFF (G1 & G2 & _) LC MI.
unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'. pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'.
pose proof (munch_refl [(usp + -16, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 16%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
destruct HM as [-> | [-> | ->]];
[ pose proof (lib_const m A_speex_nb_mode LC_speex_nb_mode LC ltac:(lc_in)) as ND; unfold LC_speex_nb_mode in ND;
replace (mode_dec A_speex_nb_mode) with 0x9f634 by reflexivity;
assert (AL8 : A_speex_nb_mode mod 8 = 0) by reflexivity;
assert (MPR : 0x10000 <= A_speex_nb_mode /\ A_speex_nb_mode + 96 <= 0x652000) by (unfold A_speex_nb_mode; lia);
set (MPv := A_speex_nb_mode) in *; clearbody MPv
| pose proof (lib_const m A_speex_wb_mode LC_speex_wb_mode LC ltac:(lc_in)) as ND; unfold LC_speex_wb_mode in ND;
replace (mode_dec A_speex_wb_mode) with 0xb67bc by reflexivity;
assert (AL8 : A_speex_wb_mode mod 8 = 0) by reflexivity;
assert (MPR : 0x10000 <= A_speex_wb_mode /\ A_speex_wb_mode + 96 <= 0x652000) by (unfold A_speex_wb_mode; lia);
set (MPv := A_speex_wb_mode) in *; clearbody MPv
| pose proof (lib_const m A_speex_uwb_mode LC_speex_uwb_mode LC ltac:(lc_in)) as ND; unfold LC_speex_uwb_mode in ND;
replace (mode_dec A_speex_uwb_mode) with 0xb67bc by reflexivity;
assert (AL8 : A_speex_uwb_mode mod 8 = 0) by reflexivity;
assert (MPR : 0x10000 <= A_speex_uwb_mode /\ A_speex_uwb_mode + 96 <= 0x652000) by (unfold A_speex_uwb_mode; lia);
set (MPv := A_speex_uwb_mode) in *; clearbody MPv ];
(destruct HE as [-> | ->]; unfold A_speex_decode_native, A_speex_decode).
1: ato 0x98570. 2: ato 0x98620. 3: ato 0x98570. 4: ato 0x98620. 5: ato 0x98570. 6: ato 0x98620.
all: do 2 astep; release_frame FR ST usp.
1, 2: ato 0x9f634. 3, 4, 5, 6: ato 0xb67bc.
all: apply evt_done; do 5 eexists; split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI| exact ST].
Qed.

Lemma drep_mode_cell : forall OUT STEREO (m : mem) S (d : dec_state bptr) LBD, DREP OUT STEREO m S d LBD ->
exists MP, mode_dec MP = dec_target d /\ (MP = A_speex_nb_mode \/ MP = A_speex_wb_mode \/ MP = A_speex_uwb_mode)
/\ rw_cells asegs m S [C8 (Z_to_bv 64 MP)].
Proof.
intros OUT STEREO m S [st | s low] LBD R; cbn [decst_rep] in R.
- destruct R as (_ & _ & _ & _ & j & _ & _ & C). exists A_speex_nb_mode. split; [reflexivity|]. split; [left; reflexivity|].
unfold nb_cells, nb_hdr_cells in C. cbn [app] in C. exact (proj1 (rw_cells_uncons _ _ _ _ _ C)).
- destruct R as (a & j & LBL & _ & _ & _ & INV & _ & C & _).
apply sb_pieces_iff in C. destruct C as (HD & _). unfold sbp_hdr in HD. apply rw_cells_uncons in HD. destruct HD as (HD & _).
destruct INV as (IMODE & _). destruct IMODE as [E|E]; rewrite E in HD; cbn [sb_mode_ptr] in HD.
+ exists A_speex_wb_mode. split; [reflexivity|]. split; [right; left; reflexivity| exact HD].
+ exists A_speex_uwb_mode. split; [reflexivity|]. split; [right; right; reflexivity| exact HD].
Qed.

Section DecDispatch.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable OUT_rep : X1s9.stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
Variable IO_FP : list (Z * Z).
Hypothesis ERR_loc : fp_local IO_FP ERR_rep.
Hypothesis OUT_loc : forall so, fp_local IO_FP (OUT_rep so).
Hypothesis IO_img : forall y, in_ranges IO_FP y -> client_static y.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Theorem dec_cps_dispatch : forall ENTRY (d : dec_state bptr), (ENTRY = A_speex_decode_native \/ ENTRY = A_speex_decode) ->
dec_cps_at RT OUT_rep ERR_rep IO_FP (dec_target d) d -> dec_cps_at RT OUT_rep ERR_rep IO_FP ENTRY d.
Proof using AF ERR_loc OUT_loc IO_img AF_LIB.
intros ENTRY d HE TG. unfold dec_cps_at.
intros Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S A D LBD b lo fh PD ND kh ows stb q q' ret d' b' PRUN EA0 EA1 EA2 ETP REP DEP ISV NEST NDUP LAL8 LIVE BREP BOK INPD PD1 PD2 PDB OC LOWS STB INFH FA FO FS
HAO HAS HOS FD2 ERR0 SSP0 FRM CRD POA ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
destruct (TG Σ F0 fs0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S A D LBD b lo fh PD ND kh ows stb q q' ret d' b' PRUN EA0 EA1 EA2 ETP REP DEP ISV NEST NDUP LAL8 LIVE BREP BOK INPD PD1 PD2 PDB OC LOWS STB INFH FA FO FS
HAO HAS HOS FD2 ERR0 SSP0 FRM CRD POA ART0 MI0 FRM0 ST0 LOW LOR SPT SPA) as (bs & EB & _).
exists bs. split; [exact EB|].
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc. subst a0.

destruct (drep_mode_cell OUT STEREO m S d LBD REP) as (MP & EMD & HMP & MPC).
destruct (decst_rep_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP) as (rest & ELB).
assert (INS : In (S, match d with DecNB _ => NBSTATE_SIZEOF | DecSB _ _ => SBSTATE_SIZEOF end) (rt_live RT Σ)).
{ specialize (LIVE (match d with DecNB st => nb_blk st | DecSB s _ => sbd_blk s end, S, match d with DecNB _ => NBSTATE_SIZEOF | DecSB _ _ => SBSTATE_SIZEOF end)).
rewrite ELB in LIVE. exact (LIVE ltac:(left; reflexivity)). }
assert (SZS : 8 <= match d with DecNB _ => NBSTATE_SIZEOF | DecSB _ _ => SBSTATE_SIZEOF end) by (destruct d; unfold NBSTATE_SIZEOF, SBSTATE_SIZEOF; lia).
set (SZ := match d with DecNB _ => NBSTATE_SIZEOF | DecSB _ _ => SBSTATE_SIZEOF end) in *. clearbody SZ.
destruct (live_below_lo RT AF Σ m S SZ lo ART0 INS LOW) as (SPOS & SLO & LOS).
destruct (af_acc_live RT AF Σ m S SZ ART0 INS) as (_ & ACS).
pose proof (live_facts RT AF Σ m S SZ ART0 INS) as (_ & _ & SIMG & SHI).
assert (S8 : S mod 8 = 0) by (exact (proj2 (decst_rep_pos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ REP))).
assert (DSP : 0 <= dec_stack d) by (clear; induction d; cbn [dec_stack]; unfold NBDEC_STACK, SB_OWN_STACK, SB_LOOP_STACK, INNOV_STACK; lia).
assert (OBS : aobj asegs m S 8) by (split; [lia|]; split; [clear - SLO LOR SPT DSP SZS; unfold RT_STACK, APP_TOP, USTACK_TOP in *; lia| exact (acc_sub asegs m S SZ S 8 ACS ltac:(lia) ltac:(lia))]).
pose proof (AF_LIB Σ m ART0) as LC0. pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (OBM : aobj asegs m MP 96).
{ destruct HMP as [-> | [-> | ->]]; (apply (aobj_lit RT AF Σ m _ 96 ART0);
[ unfold ACC_LITS; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode; lia
| unfold A_speex_nb_mode, A_speex_wb_mode, A_speex_uwb_mode, APP_TOP; lia]). }
assert (SOFF : S + 8 <= SH_LO \/ SH_HI <= S) by (clear - SHI SZS; unfold SH_LO, SH_HI in *; lia).
assert (LO16 : lo <= usp - 16) by (clear - LOR DSP; unfold RT_STACK in LOR; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp (dec_W IO_FP A OUT STEREO LBD) m) as PF.
pose proof (PMfd_mat_stable F0 fs0) as MST. pose proof (PMfd_fdfs_only F0 fs0) as FDO.
cps_seg (dec_dispatch_w ENTRY S MP usp lo).
destruct POST as (m1 & xt1 & xa3 & xa4 & xa5 & -> & MU & WM & MI1 & ST1).

destruct BREP as ((rjb & Lrjb & BOBJ) & (bsb & BDAT & Hbsb) & BSIDE). unfold bits_cells in BOBJ. apply (proj1 (u8arr_rw_CB m D bsb)) in BDAT.
destruct FA as (FA1 & FA2 & ACA & AAL). destruct FO as (FO1 & FO2 & ACO & OAL). destruct FS as (FS1 & FS2 & ACST & SAL).
destruct SSP0 as (gssp & SSP1 & SSP2).
pose proof (fun so (H : OUT_rep so m) => H) as OUTK.
pk_munch MU WM LBD ERR_rep OUT_rep IO_FP IO_img
ltac:(fun b x Hb Hx => let H1 := fresh in destruct (live_below_lo RT AF Σ m _ _ lo ART0 (LIVE b Hb) LOW) as (_ & H1 & _);
clear - H1 Hx LO16; cbn [outside]; split; [lia | exact I])
ltac:(fun x Hx => clear - Hx LO16 LOS; cbn [outside]; split; [unfold SH_HI in LOS; lia | exact I]).
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
destruct (frame_below_lo RT AF Σ m fh kh lo ART0 INFH LOW) as (BF1 & BF2 & _).
destruct (live_below_lo RT AF Σ m PD ND lo ART0 INPD LOW) as (_ & BLPD & _).
assert (Lbsb : Z.of_nat (length bsb) = sb_buf_size b) by (pose proof BOK as OK'; unfold bits_ok in OK'; rewrite Hbsb, zlength_map_unsigned in OK'; clear - OK'; lia).
assert (BDLO : D + Z.of_nat (length bsb) <= lo) by (clear - Lbsb PD2 BLPD; lia).
unfold BITS_SIZEOF in *.
cps_seg_post.

assert (OF16 : offsh [(usp + -16, usp)]) by (cbn; unfold SH_LO, SH_HI in *; lia).
pose proof (frame_facts RT AF Σ m1 fh kh ART INFH) as (FP0 & FP64 & FPIMG & FPHI & _).
assert (ACC1 : forall o n, acc asegs m o n -> 0 <= o -> o + n <= APP_TOP -> acc asegs m1 o n).
{ intros o n H H0 H1. exact (proj2 (proj2 (aobj_munch asegs _ m m1 o n (conj H0 (conj H1 H)) MU (shfree_of_offsh _ o n OF16 H0 H1)))). }
assert (FA' : in_frame_obj RT Σ m1 fh kh A 48) by (split; [lia|]; split; [lia|]; split; [apply ACC1; [exact ACA| lia| ulc] | exact AAL]).
assert (FO' : in_frame_obj RT Σ m1 fh kh OUT 8000) by (split; [lia|]; split; [lia|]; split; [apply ACC1; [exact ACO| lia| ulc] | exact OAL]).
assert (FS' : in_frame_obj RT Σ m1 fh kh STEREO 24) by (split; [lia|]; split; [lia|]; split; [apply ACC1; [exact ACST| lia| ulc] | exact SAL]).
assert (BREP1 : bits_rep asegs m1 A D b).
{ split; [exists rjb; split; [exact Lrjb| unfold bits_cells; exact BOBJ]|].
split; [exists bsb; split; [apply (proj2 (u8arr_rw_CB m1 D bsb)); exact BDAT| exact Hbsb]| exact BSIDE]. }
assert (SSP1' : io_ssp m1) by (exists gssp; split; assumption).
rewrite EMD in Hc0.

destruct (TG Σ F0 fs0 ra (Z_to_bv 64 usp) gp tp t0 xt1 t2 s0 s1 (Z_to_bv 64 S) a1 a2 xa3 xa4 xa5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
OUT STEREO S A D LBD b lo fh PD ND kh ows stb q q' ret d' b' PRUN eq_refl EA1 EA2 ETP REP DEP ISV NEST NDUP LAL8 LIVE BREP1 BOK INPD PD1 PD2 PDB OC LOWS STB INFH FA' FO' FS'
HAO HAS HOS FD2 ERR0 SSP1' FRM CRD) as (bs1 & EB1 & CP1).
1-9: try rewrite <- ESP.
{ exact POA. } { exact ART. } { exact MI1. } { exact FRM0. } { exact ST1. } { exact LOW. } { exact LOR. } { exact SPT. } { exact SPA. }
assert (E1 : bs1 = bs) by (rewrite EB1 in EB; apply app_inv_head in EB; congruence). subst bs1.
refine (rz_cpsE RT Σ (PMfd F0 fs0) _ _ _ T c0 Hc0 CP1 _).
intros c' (Σ' & Hc' & PUR).
apply Hk. exists Σ'. split; [| exact PUR].
apply (ASTA_conseq RT Σ' (PMfd F0 fs0) _ _ c' Hc').
intros ms (m' & ows' & stb' & RS & (ART' & MI' & WM' & ST') & PRS & REST).
exists m', ows', stb'. rewrite <- ESP in ST', PRS, RS.  split; [exact RS|].
split; [refine (conj ART' (conj MI' (conj (wmono_trans _ _ _ _ WM WM') ST'))) |].
split; [exact (pres_fp_trans _ _ _ _ m m1 m' PF PRS) |].
destruct REST as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & OK').
refine (conj R1 (conj R2 (conj R3 (conj R4 (conj R5 (conj R6 (conj R7 (conj R8 (conj R9 (conj R10 (conj R11 _))))))))))).
intros so Hso. exact (OK' so (OUTK0 so Hso)).
Qed.

Theorem dec_cps_induction :
(forall st, dec_cps_at RT OUT_rep ERR_rep IO_FP A_nb_decode (DecNB st)) ->
(forall k, (forall d, (dec_depth d <= k)%nat -> dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode_native d) ->
forall s low, (dec_depth low <= k)%nat -> dec_cps_at RT OUT_rep ERR_rep IO_FP A_sb_decode (DecSB s low)) ->
forall d, dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode_native d /\ dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode d.
Proof using AF ERR_loc OUT_loc IO_img AF_LIB.
intros NBD SBD.
assert (H : forall n d, (dec_depth d <= n)%nat ->
dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode_native d /\ dec_cps_at RT OUT_rep ERR_rep IO_FP A_speex_decode d).
{ induction n as [|n IH]; intros d Hd; [destruct d; cbn [dec_depth] in Hd; lia|].
destruct d as [st | s low].
- split; apply dec_cps_dispatch; [left; reflexivity | exact (NBD st) | right; reflexivity | exact (NBD st)].
- assert (SB : dec_cps_at RT OUT_rep ERR_rep IO_FP A_sb_decode (DecSB s low)).
{ apply (SBD n); [intros d' Hd'; exact (proj1 (IH d' Hd')) | cbn [dec_depth] in Hd; lia]. }
split; apply dec_cps_dispatch; [left; reflexivity | exact SB | right; reflexivity | exact SB]. }
intros d. exact (H _ d (le_n _)).
Qed.
End DecDispatch.
