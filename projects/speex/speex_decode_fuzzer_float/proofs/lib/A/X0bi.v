(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1df X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05q X05s X05t X05l X081 X09e X082 X08y
X089 X0bn X0bk X0bj.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wj X0wl X0wm X0ys X0yt X0zq X12a X127 X126.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wj OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X127 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X126.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma scb_rr : forall a nb, a mod 32 = 0 -> In nb [2; 4; 5; 8] -> alloca_rr a (4 * nb) = a + 64.
Proof. intros a nb H HN. cbn [In] in HN. unfold alloca_rr. destruct HN as [<-|[<-|[<-|[<-|[]]]]]; Z.div_mod_to_equations; lia. Qed.

Lemma bytes_at_same : forall segs (m : mem) a bs1 bs2, bytes_at segs m a bs1 -> bytes_at segs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof.
intros segs m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length bs1)) as [Hi|Hi].
- rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
- rewrite (proj2 (nth_error_None bs1 i) Hi), (proj2 (nth_error_None bs2 i) ltac:(lia)). reflexivity.
Qed.

Lemma lits24_keep : forall (m m' : mem) a cs, mem_inv bsegs m -> mem_inv bsegs m' -> lib_consts m -> lib_consts m' ->
In (a, 24) ACC_LITS -> cells_size cs = 24%nat -> ro_cells bsegs m a cs -> ro_cells bsegs m' a cs.
Proof.
intros m m' a cs MI MI' LC LC' HIN SZ RO.
assert (VIA : forall csT, cells_size csT = 24%nat -> ro_cells bsegs m a csT -> ro_cells bsegs m' a csT -> ro_cells bsegs m' a cs).
{ intros csT SZT (WFT & BT) (_ & BT'). destruct RO as (WF & B). split; [exact WF|].
rewrite (bytes_at_same bsegs m a _ _ B BT); [exact BT'|]. rewrite (cells_bytes_length _ WF), (cells_bytes_length _ WFT). congruence. }
cbn [In ACC_LITS] in HIN.
repeat (destruct HIN as [HIN|HIN]; [pose proof (f_equal snd HIN) as E; cbn [snd] in E; try discriminate E; clear E; apply (f_equal fst) in HIN; cbn [fst] in HIN; subst a|]); try contradiction.
all: first [ apply (ro_cells_rodataB m m' _ cs MI MI'); [lia | rewrite SZ; lia | exact RO]
| lazymatch goal with |- ro_cells _ _ ?a _ =>
lazymatch eval cbv in (find (fun t => Z.eqb (fst t) a) LIB_TABLES) with
| Some (?a', ?csT) => apply (VIA csT eq_refl); [ apply (lib_const m a' csT LC); lc_in | apply (lib_const m' a' csT LC'); lc_in ]
end end ].
Qed.

Section SCB.
Variable RT : rt_sig.
Context {ptr : Type}.
Hypothesis AF : art_facts RT.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.
Local Notation BODY := (scb_body_proof ptr).

Hypothesis AF_LIB : forall (Σ : rts RT) (m : mem), ART RT Σ m -> lib_consts m.

Lemma scbb_eq : forall n hs sb (b : bits_st ptr), scbb n hs sb b = scb_bits n hs sb b.
Proof. induction n as [|n IH]; intros hs sb b; [reflexivity|]. cbn [scbb scb_bits]. apply IH. Qed.

Lemma scbb_size : forall n hs sb (b : bits_st ptr), bits_ok b -> 0 <= sb -> sb_buf_size (scbb n hs sb b) = sb_buf_size b.
Proof.
induction n as [|n IH]; intros hs sb b OK Hsb; [reflexivity|]. cbn [scbb]. destruct (negb (hs =? 0)).
- pose proof (ub_ok b 1 OK ltac:(lia)) as (OK1 & SZ1 & _). pose proof (ub_ok (ub b 1) sb OK1 Hsb) as (OK2 & SZ2 & _). rewrite (IH hs sb _ OK2 Hsb). congruence.
- pose proof (ub_ok b sb OK Hsb) as (OK2 & SZ2 & _). rewrite (IH hs sb _ OK2 Hsb). exact SZ2.
Qed.

Theorem split_cb_innov : forall p, scb_params_ok p -> innov_unquant_cps RT (ptr := ptr) (InnovSplitCbShapeSignUnquant p).
Proof using AF APO AUN AF_LIB.
intros p (PS & PNB & P40 & PSB & PHS & PSZ).
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A D b inn seedp PAR lo P0 N0 PD ND fa ka is0 seed0 stk8
FDO MST -> -> -> -> -> -> -> REP OK (RPAR & PAR8 & PARLO & PARHI & PARLIT) XINN LIS DST XSEED INL0 PL0 PH0 SEED4 INFA FOA INLD PDL PDH HPD HAI ART0 MI0 FRM ST0 LOW LOR SPT U32 POA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st, innov_entryA in Hc. rewrite ESP in Hc. unfold INNOV_STACK in LOR.
set (ssz := scb_subvect_size p) in *. set (nb := scb_nb_subvect p) in *. set (sbits := scb_shape_bits p) in *. set (hs := scb_have_sign p) in *.
set (scbA := shape_cb_addrA (scb_shape_cb p)) in *.
change (ro_cells bsegs m PAR (scb_par_cells ssz nb scbA sbits hs)) in RPAR.
unfold hidp in HPD, HAI.
pose proof (conj (conj ART0 MI0) RPAR) as KEEP0.
assert (LOU : lo <= usp) by (clear - LOR; unfold RT_STACK in LOR; lia).
destruct (dst_obj_facts RT AF Σ m inn 160 lo usp ART0 LOW LOU SPT POA ltac:(lia) DST) as (ACI & I0 & IT & ISH & ILO & IIMG & I4 & ICL & IRNG & ILIVE).
destruct FOA as (FA1 & FA2 & ACA & A4).
destruct (frame_below_lo RT AF Σ m fa ka lo ART0 INFA LOW) as (BFA & _ & LOSH).
pose proof (frame_facts RT AF Σ m fa ka ART0 INFA) as (FFA0 & FFA1 & FFA2 & _ & FFA4 & _).
assert (FA8 : fa mod 8 = 0) by (clear - FFA1; Z.div_mod_to_equations; lia).
pose proof (fs_size_mod8 ka) as FAS8.
destruct (live_below_lo RT AF Σ m PD ND lo ART0 INLD LOW) as (BD0 & BD1 & _).
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL0 LOW) as (BS0 & BS1 & _).
assert (FRN : rt_frames RT Σ <> []) by (intros E; rewrite E in INFA; exact INFA).
assert (SCBR : 0x10000 <= scbA /\ scbA + shape_cb_size (scb_shape_cb p) <= IMG_TOP_B /\ 0 <= scbA < 2 ^ 47)
by (subst scbA; unfold IMG_TOP_B; clear; destruct (scb_shape_cb p); cbn; lia).
unfold IMG_TOP_B in SCBR.
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(inn, inn + 160); (seedp, seedp + 4); (A, A + BITS_SIZEOF)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (FSZ : 0 <= fs_size ka) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (OBP : aobj bsegs m PAR 24) by (apply (aobj_lit RT AF Σ m PAR 24 ART0 PARLIT); unfold APP_TOP, IMG_TOP_B in *; lia).
cps_norm. unfold BITS_SIZEOF in *.
assert (SHI : forall i, 0 <= i < 160 -> SH_LO <= shad (inn + i) < SH_HI) by (intros i Hi; apply shad_in_window; clear - Hi I0 IT; lia).
assert (SHAA : forall i, 0 <= i < 48 -> SH_LO <= shad (A + i) < SH_HI) by (intros i Hi; apply shad_in_window; clear - Hi FA1 FA2 FFA0 BFA LOR SPT; lia).
pose proof (ILIVE PD ND INLD) as IDL. pose proof (ILIVE P0 N0 INL0) as ISL.
destruct (frame_live_apart RT AF Σ m fa ka P0 N0 ART0 INFA INL0) as (FAS & _). destruct (frame_live_apart RT AF Σ m fa ka PD ND ART0 INFA INLD) as (FAD & _).
destruct REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
apply u8arr_rw_CB in DAT.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OK as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
cps_hide.

destruct DST as [(fi & ki & INFI & (FI1 & FI2 & _ & _)) | INPI]; [| pose proof (POA _ INPI) as PAI; unfold pz_lo in PAI; cbn [fst] in PAI].
-

cps_seg (scb_w1 inn PAR A ssz nb scbA sbits hs usp lo).
{ unfold IMG_TOP_B; lia. }
destruct POST as (a2' & j8 & j16 & j24 & j48 & j72 & j80 & jh & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HULL1).
assert (ACI1 : acc bsegs m1 inn 160) by (refine (proj2 (proj2 (aobj_munch bsegs _ m m1 inn 160 _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACI]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA1 : acc bsegs m1 A 48) by (refine (proj2 (proj2 (aobj_munch bsegs _ m m1 A 48 _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACA]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
unfold scb_frame in FR1. cps_seg_post.
assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -288)) = usp + -288) by (apply unsigned_lit; ulc).
assert (U256 : (usp + -256) mod 32 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
assert (U352 : (usp + -352) mod 32 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
pose proof (scb_rr (usp + -256) nb U256 PNB) as RR1. pose proof (scb_rr (usp + -352) nb U352 PNB) as RR2.
replace (usp + -256 + 64) with (usp + -192) in RR1 by (clear; lia). replace (usp + -352 + 64) with (usp + -288) in RR2 by (clear; lia).
assert (NBR : 2 <= nb <= 8) by (clear - PNB; cbn [In] in PNB; lia).
cps_rt (APO Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -256) (4 * nb) lo).
{ rewrite RR1. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
{ cps_callok. }
intros c2 (Σ1 & Hc2 & PO1 & LV1 & FRS1 & SP1 & CR1).
cps_unpack Hc2 as (m2 & v1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACX1 & ACT2).
cps_sigma LV1 FRS1 SP1.
assert (INX1 : In (usp + -256, 4 * nb) (rt_pois RT Σ1)) by (rewrite PO1; left; reflexivity).
assert (ACI2 : acc bsegs m2 inn 160) by (apply (ACT2 inn 160 ACI1); [ulc| rewrite RR1; ulc]).
assert (ACA2 : acc bsegs m2 A 48) by (apply (ACT2 A 48 ACA1); [ulc| left; ulc]).

cps_seg (scb_w2 inn PAR A ssz nb scbA usp lo).
destruct POST as (jh2 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & HULL2).
assert (ACI3 : acc bsegs m3 inn 160) by (refine (proj2 (proj2 (aobj_munch bsegs _ m2 m3 inn 160 _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACI2]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA3 : acc bsegs m3 A 48) by (refine (proj2 (proj2 (aobj_munch bsegs _ m2 m3 A 48 _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACA2]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
clear FR1. unfold scb_frame in FR3. cps_seg_post.
assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -384)) = usp + -384) by (apply unsigned_lit; ulc).
cps_rt (APO Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (usp + -352) (4 * nb) lo).
{ rewrite RR2, PO1. apply pois_above_cons; [rewrite RR1; apply (pois_above_le _ usp); [exact POA| clear; lia]| clear; lia| clear - NBR; lia]. }
{ rewrite FRS1. exact FRN. }
{ cps_callok. }
intros c4 (Σ2 & Hc4 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc4 as (m4 & v4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ACX2 & ACT4).
cps_sigma LV2 FRS2 SP2.
assert (INX2 : In (usp + -352, 4 * nb) (rt_pois RT Σ2)) by (rewrite PO2; left; reflexivity).
assert (INX1' : In (usp + -256, 4 * nb) (rt_pois RT Σ2)) by (rewrite PO2; right; exact INX1).
assert (ACI4 : acc bsegs m4 inn 160) by (apply (ACT4 inn 160 ACI3); [ulc| rewrite RR2; ulc]).
assert (ACA4 : acc bsegs m4 A 48) by (apply (ACT4 A 48 ACA3); [ulc| left; ulc]).

pose proof (lits24_keep m m4 PAR (scb_par_cells ssz nb scbA sbits hs) (proj2 (proj1 KEEP0)) MI4 (AF_LIB _ _ (proj1 (proj1 KEEP0))) (AF_LIB _ _ ART4) PARLIT eq_refl (proj2 KEEP0)) as RPAR4.
assert (OBP4 : aobj bsegs m4 PAR 24) by (apply (aobj_lit RT AF Σ2 m4 PAR 24 ART4 PARLIT); ulc).
pose proof (shape_tab_ro (scb_shape_cb p) m4 MI4) as TB. fold scbA in TB.
assert (LTB : Z.of_nat (length (shape_tab_bytes (scb_shape_cb p))) = 2 ^ sbits * ssz) by (rewrite shape_tab_len; exact PSZ).
assert (OBT : aobj bsegs m4 scbA (2 ^ sbits * ssz)).
{ rewrite <- PSZ. apply (aobj_lit RT AF Σ2 m4 scbA _ ART4 (shape_tab_lit (scb_shape_cb p))); [clear - SCBR; lia | clear - SCBR; unfold APP_TOP; lia]. }
assert (SCB1 : 0x10000 <= scbA) by (clear - SCBR; lia).
assert (SCB2 : scbA + 2 ^ sbits * ssz <= IMG_TOP_B) by (rewrite <- PSZ; unfold IMG_TOP_B; clear - SCBR; lia).
assert (OB1 : aobj bsegs m4 (usp + -256) (4 * nb)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX1')).
assert (OB2 : aobj bsegs m4 (usp + -352) (4 * nb)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX2)).
assert (REP4 : bits_rep bsegs m4 A D b) by (split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [apply u8arr_rw_CB; exact DAT| exact Hbs]| exact SIDE]]).
assert (OBA4 : aobj bsegs m4 A BITS_SIZEOF) by (unfold BITS_SIZEOF; split; [ulc|]; split; [ulc|]; exact ACA4).
destruct (af_acc_live RT AF Σ2 m4 PD ND ART4 INLD) as (_ & ACLD).
assert (OBD4 : aobj bsegs m4 D (sb_buf_size b)) by (split; [ulc|]; split; [ulc|]; exact (acc_sub bsegs m4 PD ND D (sb_buf_size b) ACLD PDL PDH)).
assert (OBI4 : aobj bsegs m4 inn 160) by (split; [ulc|]; split; [ulc|]; exact ACI4).
pose proof (af_client_consts RT AF Σ2 m4 ART4) as CC4.
lazymatch type of FR3 with rw_cells _ _ _ [?k0; ?k8; ?k16; ?k24; ?k32; ?k40; ?k48; ?k56; ?k64; ?k72; ?k80; C8 ?r11; C8 ?r10; C8 ?r9; C8 ?r8; C8 ?r7; C8 ?r6; C8 ?r5; C8 ?r4; C8 ?r3; C8 ?r2; C8 ?r1; C8 ?r0; C8 ?rra] =>
change (rw_cells bsegs m4 (usp + -192) (scb_frame k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra)) in FR3 end.
cps_seg (BODY inn PAR A D ssz nb scbA sbits hs usp lo b is0 (shape_tab_bytes (scb_shape_cb p))).
all: try (unfold IMG_TOP_B, BITS_SIZEOF in *; ulc).
{ pose proof (frame_facts RT AF Σ2 m4 fi ki ART4 INFI) as (_ & _ & FFI2 & _). unfold SEGTOP_A, IMG_TOP_B in *. lia. }
destruct POST as (ra' & t0' & t1' & t2' & a0' & a1' & a2'' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s10' & s11' & t3' & t4' & t5' & t6'
& c0' & c8' & c16' & c24' & c32' & c40' & c48' & jh1' & jh2' & F' & fc' & m5 & is' & -> & MU5 & WM5 & MI5 & FRM5 & ST5 & FR5 & H15 & H25 & REP5 & OK5 & XINN5 & LIS5).
assert (ACI5 : acc bsegs m5 inn 160) by (refine (proj2 (proj2 (aobj_munch bsegs _ m4 m5 inn 160 _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACI4]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI, BITS_SIZEOF; repeat split; ulc| ulc| ulc]]).
assert (ACA5 : acc bsegs m5 A 48) by (refine (proj2 (proj2 (aobj_munch bsegs _ m4 m5 A 48 _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACA4]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI, BITS_SIZEOF; repeat split; ulc| ulc| ulc]]).
set (b' := scbb (Z.to_nat nb) hs sbits b) in *.
destruct REP5 as ((rj5 & Lrj5 & OBJ5) & (bs5 & DAT5 & Hbs5) & SIDE5). unfold bits_cells in OBJ5. apply u8arr_rw_CB in DAT5.
assert (Lbs5 : Z.of_nat (length bs5) = sb_buf_size b).
{ pose proof OK5 as OK'. unfold bits_ok in OK'. rewrite Hbs5, zlength_map_unsigned in OK'. subst b'. rewrite scbb_size in OK' by (first [exact OK | clear - PSB; lia]). lia. }
clear FR3 HULL1 HULL2 XINN OBJ DAT OBP4 OBT OB1 OB2 REP4 OBA4 OBD4 OBI4 ACLD TB RPAR4. unfold scb_frame in FR5. unfold BITS_SIZEOF in MU5.
cps_seg_post.

lazymatch type of FR5 with rw_cells _ _ _ [?k0; ?k8; ?k16; ?k24; ?k32; ?k40; ?k48; ?k56; ?k64; ?k72; ?k80; C8 ?r11; C8 ?r10; C8 ?r9; C8 ?r8; C8 ?r7; C8 ?r6; C8 ?r5; C8 ?r4; C8 ?r3; C8 ?r2; C8 ?r1; C8 ?r0; C8 ?rra] =>
change (rw_cells bsegs m5 (usp + -192) (scb_frame k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra)) in FR5 end.
cps_seg (scb_w5 usp lo _ _ (usp + -384)).
subst ms.
cps_rt (AUN Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (usp + -384) (usp + -128) lo).
{ rewrite PO2, PO1. intros e [<-|[<-|He]].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR2. clear. lia.
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR1. clear. lia.
- right. pose proof (POA e He). lia. }
{ cps_callok. }
intros c8 (Σ3 & Hc8 & PO3 & LV3 & FRS3 & SP3 & CR3).
cps_unpack Hc8 as (m8 & v8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & ACT8).
assert (ACI8 : acc bsegs m8 inn 160) by (apply (ACT8 inn 160 ACI5); [ulc| ulc]).
assert (ACA8 : acc bsegs m8 A 48) by (apply (ACT8 A 48 ACA5); [ulc| left; ulc]).

cps_seg (scb_w6 usp lo).
destruct POST as (-> & ST9).
apply Hk. exists Σ3. split.
2:{ split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
rewrite PO3, PO2, PO1. rewrite !pois_drop_cons_below by (unfold pz_lo; cbn [fst]; clear; lia).
apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v8, m8, is', seed0.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [exact ART8|]. split; [exact MI8|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact XINN5|]. split; [exact LIS5|]. split; [exact XSEED|].
assert (EB : innov_bits (InnovSplitCbShapeSignUnquant p) b = b') by (cbn [innov_bits]; subst b'; symmetry; apply scbb_eq).
rewrite EB.
split; [split; [exists rj5; split; [exact Lrj5| exact OBJ5]| split; [exists bs5; split; [apply u8arr_rw_CB; exact DAT5| exact Hbs5]| exact SIDE5]]|].
split; [exact OK5|]. split; [exact ACI8| exact ACA8].
-

cps_seg (scb_w1 inn PAR A ssz nb scbA sbits hs usp lo).
{ unfold IMG_TOP_B; lia. }
destruct POST as (a2' & j8 & j16 & j24 & j48 & j72 & j80 & jh & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HULL1).
assert (ACI1 : acc bsegs m1 inn 160) by (refine (proj2 (proj2 (aobj_munch bsegs _ m m1 inn 160 _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACI]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA1 : acc bsegs m1 A 48) by (refine (proj2 (proj2 (aobj_munch bsegs _ m m1 A 48 _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACA]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
unfold scb_frame in FR1. cps_seg_post.
assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -288)) = usp + -288) by (apply unsigned_lit; ulc).
assert (U256 : (usp + -256) mod 32 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
assert (U352 : (usp + -352) mod 32 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
pose proof (scb_rr (usp + -256) nb U256 PNB) as RR1. pose proof (scb_rr (usp + -352) nb U352 PNB) as RR2.
replace (usp + -256 + 64) with (usp + -192) in RR1 by (clear; lia). replace (usp + -352 + 64) with (usp + -288) in RR2 by (clear; lia).
assert (NBR : 2 <= nb <= 8) by (clear - PNB; cbn [In] in PNB; lia).
cps_rt (APO Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -256) (4 * nb) lo).
{ rewrite RR1. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
{ cps_callok. }
intros c2 (Σ1 & Hc2 & PO1 & LV1 & FRS1 & SP1 & CR1).
cps_unpack Hc2 as (m2 & v1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACX1 & ACT2).
cps_sigma LV1 FRS1 SP1.
assert (INX1 : In (usp + -256, 4 * nb) (rt_pois RT Σ1)) by (rewrite PO1; left; reflexivity).
assert (ACI2 : acc bsegs m2 inn 160) by (apply (ACT2 inn 160 ACI1); [ulc| rewrite RR1; ulc]).
assert (ACA2 : acc bsegs m2 A 48) by (apply (ACT2 A 48 ACA1); [ulc| left; ulc]).

cps_seg (scb_w2 inn PAR A ssz nb scbA usp lo).
destruct POST as (jh2 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & HULL2).
assert (ACI3 : acc bsegs m3 inn 160) by (refine (proj2 (proj2 (aobj_munch bsegs _ m2 m3 inn 160 _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACI2]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA3 : acc bsegs m3 A 48) by (refine (proj2 (proj2 (aobj_munch bsegs _ m2 m3 A 48 _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACA2]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
clear FR1. unfold scb_frame in FR3. cps_seg_post.
assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -384)) = usp + -384) by (apply unsigned_lit; ulc).
cps_rt (APO Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (usp + -352) (4 * nb) lo).
{ rewrite RR2, PO1. apply pois_above_cons; [rewrite RR1; apply (pois_above_le _ usp); [exact POA| clear; lia]| clear; lia| clear - NBR; lia]. }
{ rewrite FRS1. exact FRN. }
{ cps_callok. }
intros c4 (Σ2 & Hc4 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc4 as (m4 & v4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ACX2 & ACT4).
cps_sigma LV2 FRS2 SP2.
assert (INX2 : In (usp + -352, 4 * nb) (rt_pois RT Σ2)) by (rewrite PO2; left; reflexivity).
assert (INX1' : In (usp + -256, 4 * nb) (rt_pois RT Σ2)) by (rewrite PO2; right; exact INX1).
assert (ACI4 : acc bsegs m4 inn 160) by (apply (ACT4 inn 160 ACI3); [ulc| rewrite RR2; ulc]).
assert (ACA4 : acc bsegs m4 A 48) by (apply (ACT4 A 48 ACA3); [ulc| left; ulc]).

pose proof (lits24_keep m m4 PAR (scb_par_cells ssz nb scbA sbits hs) (proj2 (proj1 KEEP0)) MI4 (AF_LIB _ _ (proj1 (proj1 KEEP0))) (AF_LIB _ _ ART4) PARLIT eq_refl (proj2 KEEP0)) as RPAR4.
assert (OBP4 : aobj bsegs m4 PAR 24) by (apply (aobj_lit RT AF Σ2 m4 PAR 24 ART4 PARLIT); ulc).
pose proof (shape_tab_ro (scb_shape_cb p) m4 MI4) as TB. fold scbA in TB.
assert (LTB : Z.of_nat (length (shape_tab_bytes (scb_shape_cb p))) = 2 ^ sbits * ssz) by (rewrite shape_tab_len; exact PSZ).
assert (OBT : aobj bsegs m4 scbA (2 ^ sbits * ssz)).
{ rewrite <- PSZ. apply (aobj_lit RT AF Σ2 m4 scbA _ ART4 (shape_tab_lit (scb_shape_cb p))); [clear - SCBR; lia | clear - SCBR; unfold APP_TOP; lia]. }
assert (SCB1 : 0x10000 <= scbA) by (clear - SCBR; lia).
assert (SCB2 : scbA + 2 ^ sbits * ssz <= IMG_TOP_B) by (rewrite <- PSZ; unfold IMG_TOP_B; clear - SCBR; lia).
assert (OB1 : aobj bsegs m4 (usp + -256) (4 * nb)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX1')).
assert (OB2 : aobj bsegs m4 (usp + -352) (4 * nb)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX2)).
assert (REP4 : bits_rep bsegs m4 A D b) by (split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [apply u8arr_rw_CB; exact DAT| exact Hbs]| exact SIDE]]).
assert (OBA4 : aobj bsegs m4 A BITS_SIZEOF) by (unfold BITS_SIZEOF; split; [ulc|]; split; [ulc|]; exact ACA4).
destruct (af_acc_live RT AF Σ2 m4 PD ND ART4 INLD) as (_ & ACLD).
assert (OBD4 : aobj bsegs m4 D (sb_buf_size b)) by (split; [ulc|]; split; [ulc|]; exact (acc_sub bsegs m4 PD ND D (sb_buf_size b) ACLD PDL PDH)).
assert (OBI4 : aobj bsegs m4 inn 160) by (split; [ulc|]; split; [ulc|]; exact ACI4).
pose proof (af_client_consts RT AF Σ2 m4 ART4) as CC4.
lazymatch type of FR3 with rw_cells _ _ _ [?k0; ?k8; ?k16; ?k24; ?k32; ?k40; ?k48; ?k56; ?k64; ?k72; ?k80; C8 ?r11; C8 ?r10; C8 ?r9; C8 ?r8; C8 ?r7; C8 ?r6; C8 ?r5; C8 ?r4; C8 ?r3; C8 ?r2; C8 ?r1; C8 ?r0; C8 ?rra] =>
change (rw_cells bsegs m4 (usp + -192) (scb_frame k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra)) in FR3 end.
cps_seg (BODY inn PAR A D ssz nb scbA sbits hs usp lo b is0 (shape_tab_bytes (scb_shape_cb p))).
all: try (unfold IMG_TOP_B, BITS_SIZEOF in *; ulc).
destruct POST as (ra' & t0' & t1' & t2' & a0' & a1' & a2'' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s10' & s11' & t3' & t4' & t5' & t6'
& c0' & c8' & c16' & c24' & c32' & c40' & c48' & jh1' & jh2' & F' & fc' & m5 & is' & -> & MU5 & WM5 & MI5 & FRM5 & ST5 & FR5 & H15 & H25 & REP5 & OK5 & XINN5 & LIS5).
assert (ACI5 : acc bsegs m5 inn 160) by (refine (proj2 (proj2 (aobj_munch bsegs _ m4 m5 inn 160 _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACI4]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI, BITS_SIZEOF; repeat split; ulc| ulc| ulc]]).
assert (ACA5 : acc bsegs m5 A 48) by (refine (proj2 (proj2 (aobj_munch bsegs _ m4 m5 A 48 _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACA4]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI, BITS_SIZEOF; repeat split; ulc| ulc| ulc]]).
set (b' := scbb (Z.to_nat nb) hs sbits b) in *.
destruct REP5 as ((rj5 & Lrj5 & OBJ5) & (bs5 & DAT5 & Hbs5) & SIDE5). unfold bits_cells in OBJ5. apply u8arr_rw_CB in DAT5.
assert (Lbs5 : Z.of_nat (length bs5) = sb_buf_size b).
{ pose proof OK5 as OK'. unfold bits_ok in OK'. rewrite Hbs5, zlength_map_unsigned in OK'. subst b'. rewrite scbb_size in OK' by (first [exact OK | clear - PSB; lia]). lia. }
clear FR3 HULL1 HULL2 XINN OBJ DAT OBP4 OBT OB1 OB2 REP4 OBA4 OBD4 OBI4 ACLD TB RPAR4. unfold scb_frame in FR5. unfold BITS_SIZEOF in MU5.
cps_seg_post.

lazymatch type of FR5 with rw_cells _ _ _ [?k0; ?k8; ?k16; ?k24; ?k32; ?k40; ?k48; ?k56; ?k64; ?k72; ?k80; C8 ?r11; C8 ?r10; C8 ?r9; C8 ?r8; C8 ?r7; C8 ?r6; C8 ?r5; C8 ?r4; C8 ?r3; C8 ?r2; C8 ?r1; C8 ?r0; C8 ?rra] =>
change (rw_cells bsegs m5 (usp + -192) (scb_frame k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra)) in FR5 end.
cps_seg (scb_w5 usp lo _ _ (usp + -384)).
subst ms.
cps_rt (AUN Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (usp + -384) (usp + -128) lo).
{ rewrite PO2, PO1. intros e [<-|[<-|He]].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR2. clear. lia.
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR1. clear. lia.
- right. pose proof (POA e He). lia. }
{ cps_callok. }
intros c8 (Σ3 & Hc8 & PO3 & LV3 & FRS3 & SP3 & CR3).
cps_unpack Hc8 as (m8 & v8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & ACT8).
assert (ACI8 : acc bsegs m8 inn 160) by (apply (ACT8 inn 160 ACI5); [ulc| ulc]).
assert (ACA8 : acc bsegs m8 A 48) by (apply (ACT8 A 48 ACA5); [ulc| left; ulc]).

cps_seg (scb_w6 usp lo).
destruct POST as (-> & ST9).
apply Hk. exists Σ3. split.
2:{ split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
rewrite PO3, PO2, PO1. rewrite !pois_drop_cons_below by (unfold pz_lo; cbn [fst]; clear; lia).
apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v8, m8, is', seed0.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [exact ART8|]. split; [exact MI8|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact XINN5|]. split; [exact LIS5|]. split; [exact XSEED|].
assert (EB : innov_bits (InnovSplitCbShapeSignUnquant p) b = b') by (cbn [innov_bits]; subst b'; symmetry; apply scbb_eq).
rewrite EB.
split; [split; [exists rj5; split; [exact Lrj5| exact OBJ5]| split; [exists bs5; split; [apply u8arr_rw_CB; exact DAT5| exact Hbs5]| exact SIDE5]]|].
split; [exact OK5|]. split; [exact ACI8| exact ACA8].
Qed.
End SCB.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma scb_rr : forall a nb, a mod 32 = 0 -> In nb [2; 4; 5; 8] -> alloca_rr a (4 * nb) = a + 64.
Proof. intros a nb H HN. cbn [In] in HN. unfold alloca_rr. destruct HN as [<-|[<-|[<-|[<-|[]]]]]; Z.div_mod_to_equations; lia. Qed.

Lemma bytes_at_same : forall segs (m : mem) a bs1 bs2, bytes_at segs m a bs1 -> bytes_at segs m a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
Proof.
intros segs m a bs1 bs2 (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length bs1)) as [Hi|Hi].
- rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
- rewrite (proj2 (nth_error_None bs1 i) Hi), (proj2 (nth_error_None bs2 i) ltac:(lia)). reflexivity.
Qed.

Lemma lits24_keep : forall (m m' : mem) a cs, mem_inv asegs m -> mem_inv asegs m' -> lib_consts m -> lib_consts m' ->
In (a, 24) ACC_LITS -> cells_size cs = 24%nat -> ro_cells asegs m a cs -> ro_cells asegs m' a cs.
Proof.
intros m m' a cs MI MI' LC LC' HIN SZ RO.
assert (VIA : forall csT, cells_size csT = 24%nat -> ro_cells asegs m a csT -> ro_cells asegs m' a csT -> ro_cells asegs m' a cs).
{ intros csT SZT (WFT & BT) (_ & BT'). destruct RO as (WF & B). split; [exact WF|].
rewrite (bytes_at_same asegs m a _ _ B BT); [exact BT'|]. rewrite (cells_bytes_length _ WF), (cells_bytes_length _ WFT). congruence. }
cbn [In ACC_LITS] in HIN.
repeat (destruct HIN as [HIN|HIN]; [pose proof (f_equal snd HIN) as E; cbn [snd] in E; try discriminate E; clear E; apply (f_equal fst) in HIN; cbn [fst] in HIN; subst a|]); try contradiction.
all: first [ apply (ro_cells_rodataA m m' _ cs MI MI'); [lia | rewrite SZ; lia | exact RO]
| lazymatch goal with |- ro_cells _ _ ?a _ =>
lazymatch eval cbv in (find (fun t => Z.eqb (fst t) a) LIB_TABLES) with
| Some (?a', ?csT) => apply (VIA csT eq_refl); [ apply (lib_const m a' csT LC); lc_in | apply (lib_const m' a' csT LC'); lc_in ]
end end ].
Qed.

Section SCB.
Variable RT : rt_sig.
Context {ptr : Type}.
Hypothesis AF : art_facts RT.
Hypothesis APO : alloca_poison_contract RT.
Hypothesis AUN : allocas_unpoison_contract RT.
Local Notation BODY := (scb_body_proof ptr).

Hypothesis AF_LIB : forall (Σ : rts RT) (m : mem), ART RT Σ m -> lib_consts m.

Lemma scbb_eq : forall n hs sb (b : bits_st ptr), scbb n hs sb b = scb_bits n hs sb b.
Proof. induction n as [|n IH]; intros hs sb b; [reflexivity|]. cbn [scbb scb_bits]. apply IH. Qed.

Lemma scbb_size : forall n hs sb (b : bits_st ptr), bits_ok b -> 0 <= sb -> sb_buf_size (scbb n hs sb b) = sb_buf_size b.
Proof.
induction n as [|n IH]; intros hs sb b OK Hsb; [reflexivity|]. cbn [scbb]. destruct (negb (hs =? 0)).
- pose proof (ub_ok b 1 OK ltac:(lia)) as (OK1 & SZ1 & _). pose proof (ub_ok (ub b 1) sb OK1 Hsb) as (OK2 & SZ2 & _). rewrite (IH hs sb _ OK2 Hsb). congruence.
- pose proof (ub_ok b sb OK Hsb) as (OK2 & SZ2 & _). rewrite (IH hs sb _ OK2 Hsb). exact SZ2.
Qed.

Theorem split_cb_innov : forall p, scb_params_ok p -> innov_unquant_cps RT (ptr := ptr) (InnovSplitCbShapeSignUnquant p).
Proof using AF APO AUN AF_LIB.
intros p (PS & PNB & P40 & PSB & PHS & PSZ).
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A D b inn seedp PAR lo P0 N0 PD ND fa ka is0 seed0 stk8
FDO MST -> -> -> -> -> -> -> REP OK (RPAR & PAR8 & PARLO & PARHI & PARLIT) XINN LIS DST XSEED INL0 PL0 PH0 SEED4 INFA FOA INLD PDL PDH HPD HAI ART0 MI0 FRM ST0 LOW LOR SPT U32 POA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st, innov_entryA in Hc. rewrite ESP in Hc. unfold INNOV_STACK in LOR.
set (ssz := scb_subvect_size p) in *. set (nb := scb_nb_subvect p) in *. set (sbits := scb_shape_bits p) in *. set (hs := scb_have_sign p) in *.
set (scbA := shape_cb_addrA (scb_shape_cb p)) in *.
change (ro_cells asegs m PAR (scb_par_cells ssz nb scbA sbits hs)) in RPAR.
unfold hidp in HPD, HAI.
pose proof (conj (conj ART0 MI0) RPAR) as KEEP0.
assert (LOU : lo <= usp) by (clear - LOR; unfold RT_STACK in LOR; lia).
destruct (dst_obj_facts RT AF Σ m inn 160 lo usp ART0 LOW LOU SPT POA ltac:(lia) DST) as (ACI & I0 & IT & ISH & ILO & IIMG & I4 & ICL & IRNG & ILIVE).
destruct FOA as (FA1 & FA2 & ACA & A4).
destruct (frame_below_lo RT AF Σ m fa ka lo ART0 INFA LOW) as (BFA & _ & LOSH).
pose proof (frame_facts RT AF Σ m fa ka ART0 INFA) as (FFA0 & FFA1 & FFA2 & _ & FFA4 & _).
assert (FA8 : fa mod 8 = 0) by (clear - FFA1; Z.div_mod_to_equations; lia).
pose proof (fs_size_mod8 ka) as FAS8.
destruct (live_below_lo RT AF Σ m PD ND lo ART0 INLD LOW) as (BD0 & BD1 & _).
destruct (live_below_lo RT AF Σ m P0 N0 lo ART0 INL0 LOW) as (BS0 & BS1 & _).
assert (FRN : rt_frames RT Σ <> []) by (intros E; rewrite E in INFA; exact INFA).
assert (SCBR : 0x10000 <= scbA /\ scbA + shape_cb_size (scb_shape_cb p) <= IMG_TOP /\ 0 <= scbA < 2 ^ 47)
by (subst scbA; unfold IMG_TOP; clear; destruct (scb_shape_cb p); cbn; lia).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(inn, inn + 160); (seedp, seedp + 4); (A, A + BITS_SIZEOF)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (FSZ : 0 <= fs_size ka) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (OBP : aobj asegs m PAR 24) by (apply (aobj_lit RT AF Σ m PAR 24 ART0 PARLIT); unfold APP_TOP, IMG_TOP in *; lia).
cps_norm. unfold BITS_SIZEOF in *.
assert (SHI : forall i, 0 <= i < 160 -> SH_LO <= shad (inn + i) < SH_HI) by (intros i Hi; apply shad_in_window; clear - Hi I0 IT; lia).
assert (SHAA : forall i, 0 <= i < 48 -> SH_LO <= shad (A + i) < SH_HI) by (intros i Hi; apply shad_in_window; clear - Hi FA1 FA2 FFA0 BFA LOR SPT; lia).
pose proof (ILIVE PD ND INLD) as IDL. pose proof (ILIVE P0 N0 INL0) as ISL.
destruct (frame_live_apart RT AF Σ m fa ka P0 N0 ART0 INFA INL0) as (FAS & _). destruct (frame_live_apart RT AF Σ m fa ka PD ND ART0 INFA INLD) as (FAD & _).
destruct REP as ((rj & Lrj & OBJ) & (bs & DAT & Hbs) & SIDE). unfold bits_cells in OBJ.
apply u8arr_rw_CB in DAT.
assert (Lbs : Z.of_nat (length bs) = sb_buf_size b) by (pose proof OK as OK'; unfold bits_ok in OK'; rewrite Hbs, zlength_map_unsigned in OK'; lia).
cps_hide.

destruct DST as [(fi & ki & INFI & (FI1 & FI2 & _ & _)) | INPI]; [| pose proof (POA _ INPI) as PAI; unfold pz_lo in PAI; cbn [fst] in PAI].
-

cps_seg (scb_w1 inn PAR A ssz nb scbA sbits hs usp lo).
destruct POST as (a2' & j8 & j16 & j24 & j48 & j72 & j80 & jh & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HULL1).
assert (ACI1 : acc asegs m1 inn 160) by (refine (proj2 (proj2 (aobj_munch asegs _ m m1 inn 160 _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACI]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA1 : acc asegs m1 A 48) by (refine (proj2 (proj2 (aobj_munch asegs _ m m1 A 48 _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACA]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
unfold scb_frame in FR1. cps_seg_post.
assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -288)) = usp + -288) by (apply unsigned_lit; ulc).
assert (U256 : (usp + -256) mod 32 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
assert (U352 : (usp + -352) mod 32 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
pose proof (scb_rr (usp + -256) nb U256 PNB) as RR1. pose proof (scb_rr (usp + -352) nb U352 PNB) as RR2.
replace (usp + -256 + 64) with (usp + -192) in RR1 by (clear; lia). replace (usp + -352 + 64) with (usp + -288) in RR2 by (clear; lia).
assert (NBR : 2 <= nb <= 8) by (clear - PNB; cbn [In] in PNB; lia).
cps_rt (APO Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -256) (4 * nb) lo).
{ rewrite RR1. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
{ cps_callok. }
intros c2 (Σ1 & Hc2 & PO1 & LV1 & FRS1 & SP1 & CR1).
cps_unpack Hc2 as (m2 & v1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACX1 & ACT2).
cps_sigma LV1 FRS1 SP1.
assert (INX1 : In (usp + -256, 4 * nb) (rt_pois RT Σ1)) by (rewrite PO1; left; reflexivity).
assert (ACI2 : acc asegs m2 inn 160) by (apply (ACT2 inn 160 ACI1); [ulc| rewrite RR1; ulc]).
assert (ACA2 : acc asegs m2 A 48) by (apply (ACT2 A 48 ACA1); [ulc| left; ulc]).

cps_seg (scb_w2 inn PAR ssz nb scbA usp lo).
destruct POST as (jh2 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & HULL2).
assert (ACI3 : acc asegs m3 inn 160) by (refine (proj2 (proj2 (aobj_munch asegs _ m2 m3 inn 160 _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACI2]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA3 : acc asegs m3 A 48) by (refine (proj2 (proj2 (aobj_munch asegs _ m2 m3 A 48 _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACA2]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
clear FR1. unfold scb_frame in FR3. cps_seg_post.
assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -384)) = usp + -384) by (apply unsigned_lit; ulc).
cps_rt (APO Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (usp + -352) (4 * nb) lo).
{ rewrite RR2, PO1. apply pois_above_cons; [rewrite RR1; apply (pois_above_le _ usp); [exact POA| clear; lia]| clear; lia| clear - NBR; lia]. }
{ rewrite FRS1. exact FRN. }
{ cps_callok. }
intros c4 (Σ2 & Hc4 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc4 as (m4 & v4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ACX2 & ACT4).
cps_sigma LV2 FRS2 SP2.
assert (INX2 : In (usp + -352, 4 * nb) (rt_pois RT Σ2)) by (rewrite PO2; left; reflexivity).
assert (INX1' : In (usp + -256, 4 * nb) (rt_pois RT Σ2)) by (rewrite PO2; right; exact INX1).
assert (ACI4 : acc asegs m4 inn 160) by (apply (ACT4 inn 160 ACI3); [ulc| rewrite RR2; ulc]).
assert (ACA4 : acc asegs m4 A 48) by (apply (ACT4 A 48 ACA3); [ulc| left; ulc]).

pose proof (lits24_keep m m4 PAR (scb_par_cells ssz nb scbA sbits hs) (proj2 (proj1 KEEP0)) MI4 (AF_LIB _ _ (proj1 (proj1 KEEP0))) (AF_LIB _ _ ART4) PARLIT eq_refl (proj2 KEEP0)) as RPAR4.
assert (OBP4 : aobj asegs m4 PAR 24) by (apply (aobj_lit RT AF Σ2 m4 PAR 24 ART4 PARLIT); ulc).
pose proof (shape_tab_ro (scb_shape_cb p) m4 MI4) as TB. fold scbA in TB.
assert (LTB : Z.of_nat (length (shape_tab_bytes (scb_shape_cb p))) = 2 ^ sbits * ssz) by (rewrite shape_tab_len; exact PSZ).
assert (OBT : aobj asegs m4 scbA (2 ^ sbits * ssz)).
{ rewrite <- PSZ. apply (aobj_lit RT AF Σ2 m4 scbA _ ART4 (shape_tab_lit (scb_shape_cb p))); [clear - SCBR; lia | clear - SCBR; unfold APP_TOP; lia]. }
assert (SCB1 : 0x10000 <= scbA) by (clear - SCBR; lia).
assert (SCB2 : scbA + 2 ^ sbits * ssz <= IMG_TOP) by (rewrite <- PSZ; unfold IMG_TOP; clear - SCBR; lia).
assert (OB1 : aobj asegs m4 (usp + -256) (4 * nb)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX1')).
assert (OB2 : aobj asegs m4 (usp + -352) (4 * nb)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX2)).
assert (REP4 : bits_rep asegs m4 A D b) by (split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [apply u8arr_rw_CB; exact DAT| exact Hbs]| exact SIDE]]).
assert (OBA4 : aobj asegs m4 A BITS_SIZEOF) by (unfold BITS_SIZEOF; split; [ulc|]; split; [ulc|]; exact ACA4).
destruct (af_acc_live RT AF Σ2 m4 PD ND ART4 INLD) as (_ & ACLD).
assert (OBD4 : aobj asegs m4 D (sb_buf_size b)) by (split; [ulc|]; split; [ulc|]; exact (acc_sub asegs m4 PD ND D (sb_buf_size b) ACLD PDL PDH)).
assert (OBI4 : aobj asegs m4 inn 160) by (split; [ulc|]; split; [ulc|]; exact ACI4).
pose proof (af_client_consts RT AF Σ2 m4 ART4) as CC4.
lazymatch type of FR3 with rw_cells _ _ _ [?k0; ?k8; ?k16; ?k24; ?k32; ?k40; ?k48; ?k56; ?k64; ?k72; ?k80; C8 ?r11; C8 ?r10; C8 ?r9; C8 ?r8; C8 ?r7; C8 ?r6; C8 ?r5; C8 ?r4; C8 ?r3; C8 ?r2; C8 ?r1; C8 ?r0; C8 ?rra] =>
change (rw_cells asegs m4 (usp + -192) (scb_frame k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra)) in FR3 end.
cps_seg (BODY inn PAR A D ssz nb scbA sbits hs usp lo b is0 (shape_tab_bytes (scb_shape_cb p))).
{ unfold BITS_SIZEOF. ulc. } { unfold BITS_SIZEOF. ulc. }
destruct POST as (ra' & t0' & t1' & t2' & a0' & a1' & a2'' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s10' & s11' & t3' & t4' & t5' & t6'
& c0' & c8' & c16' & c24' & c32' & c40' & c48' & jh1' & jh2' & F' & fc' & m5 & is' & -> & MU5 & WM5 & MI5 & FRM5 & ST5 & FR5 & H15 & H25 & REP5 & OK5 & XINN5 & LIS5).
assert (ACI5 : acc asegs m5 inn 160) by (refine (proj2 (proj2 (aobj_munch asegs _ m4 m5 inn 160 _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACI4]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI, BITS_SIZEOF; repeat split; ulc| ulc| ulc]]).
assert (ACA5 : acc asegs m5 A 48) by (refine (proj2 (proj2 (aobj_munch asegs _ m4 m5 A 48 _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACA4]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI, BITS_SIZEOF; repeat split; ulc| ulc| ulc]]).
set (b' := scbb (Z.to_nat nb) hs sbits b) in *.
destruct REP5 as ((rj5 & Lrj5 & OBJ5) & (bs5 & DAT5 & Hbs5) & SIDE5). unfold bits_cells in OBJ5. apply u8arr_rw_CB in DAT5.
assert (Lbs5 : Z.of_nat (length bs5) = sb_buf_size b).
{ pose proof OK5 as OK'. unfold bits_ok in OK'. rewrite Hbs5, zlength_map_unsigned in OK'. subst b'. rewrite scbb_size in OK' by (first [exact OK | clear - PSB; lia]). lia. }
clear FR3 HULL1 HULL2 XINN OBJ DAT OBP4 OBT OB1 OB2 REP4 OBA4 OBD4 OBI4 ACLD TB RPAR4. unfold scb_frame in FR5. unfold BITS_SIZEOF in MU5.
cps_seg_post.

lazymatch type of FR5 with rw_cells _ _ _ [?k0; ?k8; ?k16; ?k24; ?k32; ?k40; ?k48; ?k56; ?k64; ?k72; ?k80; C8 ?r11; C8 ?r10; C8 ?r9; C8 ?r8; C8 ?r7; C8 ?r6; C8 ?r5; C8 ?r4; C8 ?r3; C8 ?r2; C8 ?r1; C8 ?r0; C8 ?rra] =>
change (rw_cells asegs m5 (usp + -192) (scb_frame k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra)) in FR5 end.
cps_seg (scb_w5 usp lo _ _ (usp + -384)).
subst ms.
cps_rt (AUN Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (usp + -384) (usp + -128) lo).
{ rewrite PO2, PO1. intros e [<-|[<-|He]].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR2. clear. lia.
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR1. clear. lia.
- right. pose proof (POA e He). lia. }
{ cps_callok. }
intros c8 (Σ3 & Hc8 & PO3 & LV3 & FRS3 & SP3 & CR3).
cps_unpack Hc8 as (m8 & v8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & ACT8).
assert (ACI8 : acc asegs m8 inn 160) by (apply (ACT8 inn 160 ACI5); [ulc| ulc]).
assert (ACA8 : acc asegs m8 A 48) by (apply (ACT8 A 48 ACA5); [ulc| left; ulc]).

cps_seg (scb_w6 usp lo).
destruct POST as (-> & ST9).
apply Hk. exists Σ3. split.
2:{ split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
rewrite PO3, PO2, PO1. rewrite !pois_drop_cons_below by (unfold pz_lo; cbn [fst]; clear; lia).
apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v8, m8, is', seed0.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [exact ART8|]. split; [exact MI8|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact XINN5|]. split; [exact LIS5|]. split; [exact XSEED|].
assert (EB : innov_bits (InnovSplitCbShapeSignUnquant p) b = b') by (cbn [innov_bits]; subst b'; symmetry; apply scbb_eq).
rewrite EB.
split; [split; [exists rj5; split; [exact Lrj5| exact OBJ5]| split; [exists bs5; split; [apply u8arr_rw_CB; exact DAT5| exact Hbs5]| exact SIDE5]]|].
split; [exact OK5|]. split; [exact ACI8| exact ACA8].
-

cps_seg (scb_w1 inn PAR A ssz nb scbA sbits hs usp lo).
destruct POST as (a2' & j8 & j16 & j24 & j48 & j72 & j80 & jh & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & HULL1).
assert (ACI1 : acc asegs m1 inn 160) by (refine (proj2 (proj2 (aobj_munch asegs _ m m1 inn 160 _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACI]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA1 : acc asegs m1 A 48) by (refine (proj2 (proj2 (aobj_munch asegs _ m m1 A 48 _ MU1 _))); [split; [ulc|]; split; [ulc| exact ACA]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
unfold scb_frame in FR1. cps_seg_post.
assert (EU1 : bv_unsigned (Z_to_bv 64 (usp + -288)) = usp + -288) by (apply unsigned_lit; ulc).
assert (U256 : (usp + -256) mod 32 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
assert (U352 : (usp + -352) mod 32 = 0) by (clear - U32; Z.div_mod_to_equations; lia).
pose proof (scb_rr (usp + -256) nb U256 PNB) as RR1. pose proof (scb_rr (usp + -352) nb U352 PNB) as RR2.
replace (usp + -256 + 64) with (usp + -192) in RR1 by (clear; lia). replace (usp + -352 + 64) with (usp + -288) in RR2 by (clear; lia).
assert (NBR : 2 <= nb <= 8) by (clear - PNB; cbn [In] in PNB; lia).
cps_rt (APO Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 (usp + -256) (4 * nb) lo).
{ rewrite RR1. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
{ cps_callok. }
intros c2 (Σ1 & Hc2 & PO1 & LV1 & FRS1 & SP1 & CR1).
cps_unpack Hc2 as (m2 & v1 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & ACX1 & ACT2).
cps_sigma LV1 FRS1 SP1.
assert (INX1 : In (usp + -256, 4 * nb) (rt_pois RT Σ1)) by (rewrite PO1; left; reflexivity).
assert (ACI2 : acc asegs m2 inn 160) by (apply (ACT2 inn 160 ACI1); [ulc| rewrite RR1; ulc]).
assert (ACA2 : acc asegs m2 A 48) by (apply (ACT2 A 48 ACA1); [ulc| left; ulc]).

cps_seg (scb_w2 inn PAR ssz nb scbA usp lo).
destruct POST as (jh2 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & HULL2).
assert (ACI3 : acc asegs m3 inn 160) by (refine (proj2 (proj2 (aobj_munch asegs _ m2 m3 inn 160 _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACI2]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
assert (ACA3 : acc asegs m3 A 48) by (refine (proj2 (proj2 (aobj_munch asegs _ m2 m3 A 48 _ MU3 _))); [split; [ulc|]; split; [ulc| exact ACA2]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; ulc| ulc| ulc]]).
clear FR1. unfold scb_frame in FR3. cps_seg_post.
assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -384)) = usp + -384) by (apply unsigned_lit; ulc).
cps_rt (APO Σ1 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 (usp + -352) (4 * nb) lo).
{ rewrite RR2, PO1. apply pois_above_cons; [rewrite RR1; apply (pois_above_le _ usp); [exact POA| clear; lia]| clear; lia| clear - NBR; lia]. }
{ rewrite FRS1. exact FRN. }
{ cps_callok. }
intros c4 (Σ2 & Hc4 & PO2 & LV2 & FRS2 & SP2 & CR2).
cps_unpack Hc4 as (m4 & v4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & ACX2 & ACT4).
cps_sigma LV2 FRS2 SP2.
assert (INX2 : In (usp + -352, 4 * nb) (rt_pois RT Σ2)) by (rewrite PO2; left; reflexivity).
assert (INX1' : In (usp + -256, 4 * nb) (rt_pois RT Σ2)) by (rewrite PO2; right; exact INX1).
assert (ACI4 : acc asegs m4 inn 160) by (apply (ACT4 inn 160 ACI3); [ulc| rewrite RR2; ulc]).
assert (ACA4 : acc asegs m4 A 48) by (apply (ACT4 A 48 ACA3); [ulc| left; ulc]).

pose proof (lits24_keep m m4 PAR (scb_par_cells ssz nb scbA sbits hs) (proj2 (proj1 KEEP0)) MI4 (AF_LIB _ _ (proj1 (proj1 KEEP0))) (AF_LIB _ _ ART4) PARLIT eq_refl (proj2 KEEP0)) as RPAR4.
assert (OBP4 : aobj asegs m4 PAR 24) by (apply (aobj_lit RT AF Σ2 m4 PAR 24 ART4 PARLIT); ulc).
pose proof (shape_tab_ro (scb_shape_cb p) m4 MI4) as TB. fold scbA in TB.
assert (LTB : Z.of_nat (length (shape_tab_bytes (scb_shape_cb p))) = 2 ^ sbits * ssz) by (rewrite shape_tab_len; exact PSZ).
assert (OBT : aobj asegs m4 scbA (2 ^ sbits * ssz)).
{ rewrite <- PSZ. apply (aobj_lit RT AF Σ2 m4 scbA _ ART4 (shape_tab_lit (scb_shape_cb p))); [clear - SCBR; lia | clear - SCBR; unfold APP_TOP; lia]. }
assert (SCB1 : 0x10000 <= scbA) by (clear - SCBR; lia).
assert (SCB2 : scbA + 2 ^ sbits * ssz <= IMG_TOP) by (rewrite <- PSZ; unfold IMG_TOP; clear - SCBR; lia).
assert (OB1 : aobj asegs m4 (usp + -256) (4 * nb)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX1')).
assert (OB2 : aobj asegs m4 (usp + -352) (4 * nb)) by (split; [ulc|]; split; [ulc|]; exact (af_acc_pois RT AF Σ2 m4 _ _ ART4 INX2)).
assert (REP4 : bits_rep asegs m4 A D b) by (split; [exists rj; split; [exact Lrj| exact OBJ]| split; [exists bs; split; [apply u8arr_rw_CB; exact DAT| exact Hbs]| exact SIDE]]).
assert (OBA4 : aobj asegs m4 A BITS_SIZEOF) by (unfold BITS_SIZEOF; split; [ulc|]; split; [ulc|]; exact ACA4).
destruct (af_acc_live RT AF Σ2 m4 PD ND ART4 INLD) as (_ & ACLD).
assert (OBD4 : aobj asegs m4 D (sb_buf_size b)) by (split; [ulc|]; split; [ulc|]; exact (acc_sub asegs m4 PD ND D (sb_buf_size b) ACLD PDL PDH)).
assert (OBI4 : aobj asegs m4 inn 160) by (split; [ulc|]; split; [ulc|]; exact ACI4).
pose proof (af_client_consts RT AF Σ2 m4 ART4) as CC4.
lazymatch type of FR3 with rw_cells _ _ _ [?k0; ?k8; ?k16; ?k24; ?k32; ?k40; ?k48; ?k56; ?k64; ?k72; ?k80; C8 ?r11; C8 ?r10; C8 ?r9; C8 ?r8; C8 ?r7; C8 ?r6; C8 ?r5; C8 ?r4; C8 ?r3; C8 ?r2; C8 ?r1; C8 ?r0; C8 ?rra] =>
change (rw_cells asegs m4 (usp + -192) (scb_frame k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra)) in FR3 end.
cps_seg (BODY inn PAR A D ssz nb scbA sbits hs usp lo b is0 (shape_tab_bytes (scb_shape_cb p))).
{ unfold BITS_SIZEOF. ulc. } { unfold BITS_SIZEOF. ulc. }
destruct POST as (ra' & t0' & t1' & t2' & a0' & a1' & a2'' & a3' & a4' & a5' & a6' & a7' & s2' & s3' & s4' & s5' & s6' & s7' & s8' & s10' & s11' & t3' & t4' & t5' & t6'
& c0' & c8' & c16' & c24' & c32' & c40' & c48' & jh1' & jh2' & F' & fc' & m5 & is' & -> & MU5 & WM5 & MI5 & FRM5 & ST5 & FR5 & H15 & H25 & REP5 & OK5 & XINN5 & LIS5).
assert (ACI5 : acc asegs m5 inn 160) by (refine (proj2 (proj2 (aobj_munch asegs _ m4 m5 inn 160 _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACI4]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI, BITS_SIZEOF; repeat split; ulc| ulc| ulc]]).
assert (ACA5 : acc asegs m5 A 48) by (refine (proj2 (proj2 (aobj_munch asegs _ m4 m5 A 48 _ MU5 _))); [split; [ulc|]; split; [ulc| exact ACA4]| apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI, BITS_SIZEOF; repeat split; ulc| ulc| ulc]]).
set (b' := scbb (Z.to_nat nb) hs sbits b) in *.
destruct REP5 as ((rj5 & Lrj5 & OBJ5) & (bs5 & DAT5 & Hbs5) & SIDE5). unfold bits_cells in OBJ5. apply u8arr_rw_CB in DAT5.
assert (Lbs5 : Z.of_nat (length bs5) = sb_buf_size b).
{ pose proof OK5 as OK'. unfold bits_ok in OK'. rewrite Hbs5, zlength_map_unsigned in OK'. subst b'. rewrite scbb_size in OK' by (first [exact OK | clear - PSB; lia]). lia. }
clear FR3 HULL1 HULL2 XINN OBJ DAT OBP4 OBT OB1 OB2 REP4 OBA4 OBD4 OBI4 ACLD TB RPAR4. unfold scb_frame in FR5. unfold BITS_SIZEOF in MU5.
cps_seg_post.

lazymatch type of FR5 with rw_cells _ _ _ [?k0; ?k8; ?k16; ?k24; ?k32; ?k40; ?k48; ?k56; ?k64; ?k72; ?k80; C8 ?r11; C8 ?r10; C8 ?r9; C8 ?r8; C8 ?r7; C8 ?r6; C8 ?r5; C8 ?r4; C8 ?r3; C8 ?r2; C8 ?r1; C8 ?r0; C8 ?rra] =>
change (rw_cells asegs m5 (usp + -192) (scb_frame k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 r11 r10 r9 r8 r7 r6 r5 r4 r3 r2 r1 r0 rra)) in FR5 end.
cps_seg (scb_w5 usp lo _ _ (usp + -384)).
subst ms.
cps_rt (AUN Σ2 PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 (usp + -384) (usp + -128) lo).
{ rewrite PO2, PO1. intros e [<-|[<-|He]].
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR2. clear. lia.
- left. unfold pz_lo, pz_hi. cbn [fst snd]. rewrite RR1. clear. lia.
- right. pose proof (POA e He). lia. }
{ cps_callok. }
intros c8 (Σ3 & Hc8 & PO3 & LV3 & FRS3 & SP3 & CR3).
cps_unpack Hc8 as (m8 & v8 & RS8 & (ART8 & MI8 & WM8 & ST8) & PRES8 & ACT8).
assert (ACI8 : acc asegs m8 inn 160) by (apply (ACT8 inn 160 ACI5); [ulc| ulc]).
assert (ACA8 : acc asegs m8 A 48) by (apply (ACT8 A 48 ACA5); [ulc| left; ulc]).

cps_seg (scb_w6 usp lo).
destruct POST as (-> & ST9).
apply Hk. exists Σ3. split.
2:{ split; [congruence|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
rewrite PO3, PO2, PO1. rewrite !pois_drop_cons_below by (unfold pz_lo; cbn [fst]; clear; lia).
apply pois_drop_above. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists v8, m8, is', seed0.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [exact ART8|]. split; [exact MI8|]. split; [cps_wmono| exact ST9]. }
split; [exact PF|]. split; [exact XINN5|]. split; [exact LIS5|]. split; [exact XSEED|].
assert (EB : innov_bits (InnovSplitCbShapeSignUnquant p) b = b') by (cbn [innov_bits]; subst b'; symmetry; apply scbb_eq).
rewrite EB.
split; [split; [exists rj5; split; [exact Lrj5| exact OBJ5]| split; [exists bs5; split; [apply u8arr_rw_CB; exact DAT5| exact Hbs5]| exact SIDE5]]|].
split; [exact OK5|]. split; [exact ACI8| exact ACA8].
Qed.
End SCB.
