(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qz X1r8.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s
X09u X0ae X09p X09q X0ab X0ac X0a6.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X110 X10c X10d X10x X10y X10s.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X110 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X10s.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section OggPageoutCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis PSK : ogg_sync_pageseek_cps RT.

Definition ogg_sync_pageout_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A G D f lo : Z) (k : nat) (sy : sync_st bptr) (bytes j0 j1 j2 j3 : list byte) r ogo (sy' : sync_st bptr),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 G -> tp = Z_to_bv 64 0x638c98 ->
sync_rep m A D sy bytes -> sync_inv2 sy -> 0 < A -> 0 < G -> sync_live RT Σ sy D ->
rw_cells bsegs m G [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] ->
ogg_sync_pageout sy = Some ((r, ogo), sy') ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 32 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 32 <= G \/ G + 32 <= A) ->
ART RT Σ m -> mem_inv bsegs m ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 160 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_sync_pageout m)))
(ASTA RT Σ PMc (fun ms => exists m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz r) m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))] m m'
/\ sync_rep m' A D sy' bytes
/\ rw_cells bsegs m' G (og_cells D ogo [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3]))).

Lemma po_loop : forall (fuel : nat) (Σ : rts RT) PMc (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc (m0 : mem)
(A G D f lo usp : Z) (k : nat) (bytes j0 j1 j2 j3 j8 : list byte) r ogo (sy' : sync_st bptr) (T : TSet),
fdfs_only PMc -> mat_stable PMc -> 0 < A -> 0 < G ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 32 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 32 <= G \/ G + 32 <= A) ->
rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 160 <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
0 <= D -> D + Z.of_nat (length bytes) <= lo ->
(forall c', ASTA RT Σ PMc (fun ms => exists m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra (Z_to_bv 64 usp) gp (Z_to_bv 64 0x638c98) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz r) m' ms
/\ rt_after RT Σ usp lo m0 m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))] m0 m'
/\ sync_rep m' A D sy' bytes
/\ rw_cells bsegs m' G (og_cells D ogo [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3])) c' -> realizes bsegs c' T) ->
forall (sy : sync_st bptr) (m : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) c,
pageout_loop fuel sy = Some ((r, ogo), sy') ->
sync_rep m A D sy bytes -> sync_inv2 sy -> sync_live RT Σ sy D ->
rw_cells bsegs m G [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] ->
rw_cells bsegs m (usp + -32) (po_frame ra s0 s1 j8) ->
ART RT Σ m -> mem_inv bsegs m -> stk bsegs m lo (usp + -32) -> wmono bsegs m0 m ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))] m0 m ->
ASTA RT Σ PMc (eq (MS (mkR (Z_to_bv 64 RA_po_pageseek) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x638c98) t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 G)
(Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_pageseek) fc None m (seg_rom bsegs))) c ->
realizes bsegs c T.
Proof using AF PSK.
induction fuel as [|fuel IH]; intros Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 A G D f lo usp k bytes j0 j1 j2 j3 j8 r ogo sy' T
FDO MST A0 G0 INF FA1 FA2 FG1 FG2 SEP_AG LOW LOR SPT SPA D0 DLO Hk sy m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c RES REP INV2 INL OG FR ART0 MI0 ST0 WM0 PF Hc;
[discriminate RES|].
cbn [pageout_loop] in RES. destruct (ogg_sync_pageseek sy) as [[r1 og1] sy1] eqn:E1.
destruct (ogg_sync_pageseek_inv2 sy r1 og1 sy1 INV2 E1) as (INV2' & OGR).
pose proof (ogg_sync_pageseek_inv sy r1 og1 sy1 (proj1 INV2) E1) as (_ & EFILL & EBUF & EDATA & ESTO & _).
assert (RR : - 2^31 < r1 < 2^31).
{ destruct REP as (_ & (_ & (_ & F1) & _) & _). exact (pageseek_ret_range sy r1 og1 sy1 (proj1 INV2) F1 E1). }
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; clear - LOR SPT BF3; unfold RT_STACK, USTACK_TOP, SH_HI in *; lia).
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
unfold po_frame in FR.
cps_norm.
cps_rt (PSK Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m A G D f lo k sy bytes j0 j1 j2 j3 r1 og1 sy1).
all: [> lazymatch goal with
| |- stk _ _ _ _ => rewrite EU; exact ST0
| |- _ mod 16 = 0 => rewrite EU; clear - SPA; Z.div_mod_to_equations; lia
| |- _ => first [ rewrite EU; ulc | ulc ]
end .. | ].
intros kc2 Hc2.
ogg_unpackL Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & REP2 & OG2). destruct RS2 as (-> & ->).
assert (DJA : disjoint_from [(usp + -32, usp)] A 32) by (cbn [disjoint_from]; split; [left; clear - FA2 BF1 LOR; lia| exact I]).
assert (DJD : disjoint_from [(usp + -32, usp)] D (Z.of_nat (length bytes))) by (cbn [disjoint_from]; split; [left; clear - DLO LOR; lia| exact I]).
destruct (Z.ltb_spec 0 r1) as [POS|NPOS].
-
injection RES as <- <- <-.
destruct og1 as [pg|]; [| exfalso; clear - OGR POS; lia]. cbn [og_cells] in OG2. unfold page_cells in OG2.
cps_seg (po_w2_ret A G r1 usp lo j8).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & ST3).
apply (sync_rep_transport _ m2 m3 A D sy1 bytes MU3 WM3 DJA DJD) in REP2.
clear FR. cps_seg_post.
apply Hk. eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m3.
replace (0 <? r1) with true by (symmetry; apply Z.ltb_lt; exact POS).
split; [unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI3|]. split; [cps_wmono| exact ST3]. }
split; [exact PF|]. split; [exact REP2| exact OG2].
- assert (og1 = None) as -> by (destruct og1 as [pg|]; [destruct OGR as (X & _); lia| reflexivity]).
cbn [og_cells] in OG2.
destruct (Z.eqb_spec r1 0) as [->|NZ].
+
injection RES as <- <- <-.
cps_seg (po_w2_ret A G 0 usp lo j8).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & ST3).
apply (sync_rep_transport _ m2 m3 A D sy1 bytes MU3 WM3 DJA DJD) in REP2.
clear FR. cps_seg_post.
apply Hk. eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m3.
split; [unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI3|]. split; [cps_wmono| exact ST3]. }
split; [exact PF|]. split; [exact REP2| exact OG2].
+ destruct (Z.eqb_spec (sy_unsynced sy1) 0) as [UZ|UNZ].
*
injection RES as <- <- <-.
destruct REP2 as (SY2 & FOK2 & DAT2 & SEP2). unfold sync_cells in SY2.
cps_seg (po_w2_unsync A G D r1 usp lo sy1 j8).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & ST3 & SY3). unfold sync_cells_u in SY3.
assert (DAT3 : sync_data m3 D sy1 bytes).
{ unfold sync_data in *. destruct (sy_data sy1); [| exact DAT2]. destruct DAT2 as (X1 & ARR & X3 & X4 & X5).
split; [exact X1|]. split; [| exact (conj X3 (conj X4 X5))].
apply (u8arr_transport bsegs _ m2 m3 D bytes ARR MU3 WM3). cbn [disjoint_from]. split; [| split; [left; clear - DLO LOR; lia| exact I]].
rewrite X3 in SEP2 |- *. clear - SEP2. lia. }
clear FR SY2. cps_seg_post.
apply Hk. eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m3.
split; [unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI3|]. split; [cps_wmono| exact ST3]. }
split; [exact PF|]. split; [| exact OG2].
split; [exact SY3|]. split; [destruct FOK2 as (G1 & G2 & G3 & G4 & G5 & G6); unfold sync_fields_ok, int31 in *; cbn [sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]; repeat split; try tauto; lia|].
split; [| exact SEP2]. apply (sync_data_same m3 D sy1); [reflexivity| reflexivity| reflexivity| exact DAT3].
*
pose proof REP2 as (SY2 & FOK2 & _). unfold sync_cells in SY2.
cps_seg (po_w2_loop A G D r1 sy1).
lazymatch type of POST with ?x = _ => subst x end.
refine (IH Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 A G D f lo usp k bytes j0 j1 j2 j3 j8 r ogo sy' T
FDO MST A0 G0 INF FA1 FA2 FG1 FG2 SEP_AG LOW LOR SPT SPA D0 DLO Hk sy1 m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ RES REP2 INV2' _ OG2 FR ART2 MI2 ST2 ltac:(cps_wmono) PF Hc1).
unfold sync_live in *. rewrite EDATA, ESTO. exact INL.
Qed.

Theorem ogg_sync_pageout_ok : ogg_sync_pageout_cps.
Proof using AF PSK.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A G D f lo k sy bytes j0 j1 j2 j3 r ogo sy'
FDO MST -> -> -> REP INV2 A0 G0 INL OG RES INF FA1 FA2 FG1 FG2 SEP_AG ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof REP as (SY & FOK & DAT & SEP).
assert (DF : 0 <= D /\ D + Z.of_nat (length bytes) <= lo).
{ unfold sync_data in DAT. unfold sync_live in INL. destruct (sy_data sy) as [p|].
- destruct DAT as (D0 & _ & LEN & _). specialize (INL ltac:(intros X; discriminate X)).
destruct (live_below_lo RT AF Σ m D (sy_storage sy) lo ART0 INL LOW) as (_ & BD1 & _). rewrite LEN. split; [lia| exact BD1].
- destruct DAT as (-> & -> & _). cbn [length]. clear - BF3. unfold SH_HI in *. lia. }
destruct DF as (D0 & DLO).
unfold ogg_sync_pageout, ogg_sync_check in RES.
replace (sy_storage sy <? 0) with false in RES by (symmetry; apply Z.ltb_ge; destruct FOK as ((X & _) & _); exact X).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
unfold sync_cells in SY.
cps_norm.
cps_seg (po_w1 A G D usp lo sy).
destruct POST as (m1 & j8 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
assert (REP1 : sync_rep m1 A D sy bytes).
{ apply (sync_rep_transport _ m m1 A D sy bytes MU1 WM1); [| | exact REP]; cbn [disjoint_from]; (split; [left| exact I]); [clear - FA2 BF1 LOR; lia| clear - DLO LOR; lia]. }
clear SY. cps_seg_post.
refine (po_loop (pageout_fuel sy) Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A G D f lo usp k bytes j0 j1 j2 j3 j8 r ogo sy' T
FDO MST A0 G0 INF FA1 FA2 FG1 FG2 SEP_AG LOW LOR SPT SPA D0 DLO _ sy m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ RES REP1 INV2 INL OG FR1 ART MI1 ST1 WM1 PF Hc0).
intros c' Hc'. apply Hk. rewrite ESP. exact Hc'.
Qed.
End OggPageoutCPS.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section OggPageoutCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis PSK : ogg_sync_pageseek_cps RT.

Definition ogg_sync_pageout_cps : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (A G D f lo : Z) (k : nat) (sy : sync_st bptr) (bytes j0 j1 j2 j3 : list byte) r ogo (sy' : sync_st bptr),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 G -> tp = Z_to_bv 64 0x630458 ->
sync_rep m A D sy bytes -> sync_inv2 sy -> 0 < A -> 0 < G -> sync_live RT Σ sy D ->
rw_cells asegs m G [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] ->
ogg_sync_pageout sy = Some ((r, ogo), sy') ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 32 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 32 <= G \/ G + 32 <= A) ->
ART RT Σ m -> mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 160 <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_ogg_sync_pageout m)))
(ASTA RT Σ PMc (fun ms => exists m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz r) m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))] m m'
/\ sync_rep m' A D sy' bytes
/\ rw_cells asegs m' G (og_cells D ogo [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3]))).

Lemma po_loop : forall (fuel : nat) (Σ : rts RT) PMc (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc (m0 : mem)
(A G D f lo usp : Z) (k : nat) (bytes j0 j1 j2 j3 j8 : list byte) r ogo (sy' : sync_st bptr) (T : TSet),
fdfs_only PMc -> mat_stable PMc -> 0 < A -> 0 < G ->
In (f, k) (rt_frames RT Σ) -> f <= A -> A + 32 <= f + fs_size k - 8 -> f <= G -> G + 32 <= f + fs_size k - 8 -> (A + 32 <= G \/ G + 32 <= A) ->
rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + 160 <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 ->
0 <= D -> D + Z.of_nat (length bytes) <= lo ->
(forall c', ASTA RT Σ PMc (fun ms => exists m',
ret_stL (fun F' fc' => F' = F /\ fc' = fc) ra (Z_to_bv 64 usp) gp (Z_to_bv 64 0x630458) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (wz r) m' ms
/\ rt_after RT Σ usp lo m0 m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))] m0 m'
/\ sync_rep m' A D sy' bytes
/\ rw_cells asegs m' G (og_cells D ogo [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3])) c' -> realizes asegs c' T) ->
forall (sy : sync_st bptr) (m : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) c,
pageout_loop fuel sy = Some ((r, ogo), sy') ->
sync_rep m A D sy bytes -> sync_inv2 sy -> sync_live RT Σ sy D ->
rw_cells asegs m G [CB 8 j0; CB 8 j1; CB 8 j2; CB 8 j3] ->
rw_cells asegs m (usp + -32) (po_frame ra s0 s1 j8) ->
ART RT Σ m -> mem_inv asegs m -> stk asegs m lo (usp + -32) -> wmono asegs m0 m ->
rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))] m0 m ->
ASTA RT Σ PMc (eq (MS (mkR (Z_to_bv 64 RA_po_pageseek) (Z_to_bv 64 (usp + -32)) gp (Z_to_bv 64 0x630458) t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 G)
(Z_to_bv 64 A) (Z_to_bv 64 G) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 A_ogg_sync_pageseek) fc None m (seg_rom asegs))) c ->
realizes asegs c T.
Proof using AF PSK.
induction fuel as [|fuel IH]; intros Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 A G D f lo usp k bytes j0 j1 j2 j3 j8 r ogo sy' T
FDO MST A0 G0 INF FA1 FA2 FG1 FG2 SEP_AG LOW LOR SPT SPA D0 DLO Hk sy m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 c RES REP INV2 INL OG FR ART0 MI0 ST0 WM0 PF Hc;
[discriminate RES|].
cbn [pageout_loop] in RES. destruct (ogg_sync_pageseek sy) as [[r1 og1] sy1] eqn:E1.
destruct (ogg_sync_pageseek_inv2 sy r1 og1 sy1 INV2 E1) as (INV2' & OGR).
pose proof (ogg_sync_pageseek_inv sy r1 og1 sy1 (proj1 INV2) E1) as (_ & EFILL & EBUF & EDATA & ESTO & _).
assert (RR : - 2^31 < r1 < 2^31).
{ destruct REP as (_ & (_ & (_ & F1) & _) & _). exact (pageseek_ret_range sy r1 og1 sy1 (proj1 INV2) F1 E1). }
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -32)) = usp + -32) by (apply unsigned_lit; clear - LOR SPT BF3; unfold RT_STACK, USTACK_TOP, SH_HI in *; lia).
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
unfold po_frame in FR.
cps_norm.
cps_rt (PSK Σ PMc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m A G D f lo k sy bytes j0 j1 j2 j3 r1 og1 sy1).
all: [> lazymatch goal with
| |- stk _ _ _ _ => rewrite EU; exact ST0
| |- _ mod 16 = 0 => rewrite EU; clear - SPA; Z.div_mod_to_equations; lia
| |- _ => first [ rewrite EU; ulc | ulc ]
end .. | ].
intros kc2 Hc2.
ogg_unpackL Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & REP2 & OG2). destruct RS2 as (-> & ->).
assert (DJA : disjoint_from [(usp + -32, usp)] A 32) by (cbn [disjoint_from]; split; [left; clear - FA2 BF1 LOR; lia| exact I]).
assert (DJD : disjoint_from [(usp + -32, usp)] D (Z.of_nat (length bytes))) by (cbn [disjoint_from]; split; [left; clear - DLO LOR; lia| exact I]).
destruct (Z.ltb_spec 0 r1) as [POS|NPOS].
-
injection RES as <- <- <-.
destruct og1 as [pg|]; [| exfalso; clear - OGR POS; lia]. cbn [og_cells] in OG2. unfold page_cells in OG2.
cps_seg (po_w2_ret A G r1 usp lo j8).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & ST3).
apply (sync_rep_transport _ m2 m3 A D sy1 bytes MU3 WM3 DJA DJD) in REP2.
clear FR. cps_seg_post.
apply Hk. eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m3.
replace (0 <? r1) with true by (symmetry; apply Z.ltb_lt; exact POS).
split; [unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI3|]. split; [cps_wmono| exact ST3]. }
split; [exact PF|]. split; [exact REP2| exact OG2].
- assert (og1 = None) as -> by (destruct og1 as [pg|]; [destruct OGR as (X & _); lia| reflexivity]).
cbn [og_cells] in OG2.
destruct (Z.eqb_spec r1 0) as [->|NZ].
+
injection RES as <- <- <-.
cps_seg (po_w2_ret A G 0 usp lo j8).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & ST3).
apply (sync_rep_transport _ m2 m3 A D sy1 bytes MU3 WM3 DJA DJD) in REP2.
clear FR. cps_seg_post.
apply Hk. eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m3.
split; [unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI3|]. split; [cps_wmono| exact ST3]. }
split; [exact PF|]. split; [exact REP2| exact OG2].
+ destruct (Z.eqb_spec (sy_unsynced sy1) 0) as [UZ|UNZ].
*
injection RES as <- <- <-.
destruct REP2 as (SY2 & FOK2 & DAT2 & SEP2). unfold sync_cells in SY2.
cps_seg (po_w2_unsync A G D r1 usp lo sy1 j8).
destruct POST as (m3 & -> & MU3 & WM3 & MI3 & ST3 & SY3). unfold sync_cells_u in SY3.
assert (DAT3 : sync_data m3 D sy1 bytes).
{ unfold sync_data in *. destruct (sy_data sy1); [| exact DAT2]. destruct DAT2 as (X1 & ARR & X3 & X4 & X5).
split; [exact X1|]. split; [| exact (conj X3 (conj X4 X5))].
apply (u8arr_transport asegs _ m2 m3 D bytes ARR MU3 WM3). cbn [disjoint_from]. split; [| split; [left; clear - DLO LOR; lia| exact I]].
rewrite X3 in SEP2 |- *. clear - SEP2. lia. }
clear FR SY2. cps_seg_post.
apply Hk. eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m3.
split; [unfold ret_stL; do 16 eexists; split; [reflexivity| split; reflexivity]|].
split. { split; [assumption|]. split; [exact MI3|]. split; [cps_wmono| exact ST3]. }
split; [exact PF|]. split; [| exact OG2].
split; [exact SY3|]. split; [destruct FOK2 as (G1 & G2 & G3 & G4 & G5 & G6); unfold sync_fields_ok, int31 in *; cbn [sy_storage sy_fill sy_returned sy_unsynced sy_headerbytes sy_bodybytes]; repeat split; try tauto; lia|].
split; [| exact SEP2]. apply (sync_data_same m3 D sy1); [reflexivity| reflexivity| reflexivity| exact DAT3].
*
pose proof REP2 as (SY2 & FOK2 & _). unfold sync_cells in SY2.
cps_seg (po_w2_loop A G D r1 sy1).
lazymatch type of POST with ?x = _ => subst x end.
refine (IH Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 A G D f lo usp k bytes j0 j1 j2 j3 j8 r ogo sy' T
FDO MST A0 G0 INF FA1 FA2 FG1 FG2 SEP_AG LOW LOR SPT SPA D0 DLO Hk sy1 m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ RES REP2 INV2' _ OG2 FR ART2 MI2 ST2 ltac:(cps_wmono) PF Hc1).
unfold sync_live in *. rewrite EDATA, ESTO. exact INL.
Qed.

Theorem ogg_sync_pageout_ok : ogg_sync_pageout_cps.
Proof using AF PSK.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A G D f lo k sy bytes j0 j1 j2 j3 r ogo sy'
FDO MST -> -> -> REP INV2 A0 G0 INL OG RES INF FA1 FA2 FG1 FG2 SEP_AG ART0 MI0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (BF1 & BF2 & BF3).
pose proof REP as (SY & FOK & DAT & SEP).
assert (DF : 0 <= D /\ D + Z.of_nat (length bytes) <= lo).
{ unfold sync_data in DAT. unfold sync_live in INL. destruct (sy_data sy) as [p|].
- destruct DAT as (D0 & _ & LEN & _). specialize (INL ltac:(intros X; discriminate X)).
destruct (live_below_lo RT AF Σ m D (sy_storage sy) lo ART0 INL LOW) as (_ & BD1 & _). rewrite LEN. split; [lia| exact BD1].
- destruct DAT as (-> & -> & _). cbn [length]. clear - BF3. unfold SH_HI in *. lia. }
destruct DF as (D0 & DLO).
unfold ogg_sync_pageout, ogg_sync_check in RES.
replace (sy_storage sy <? 0) with false in RES by (symmetry; apply Z.ltb_ge; destruct FOK as ((X & _) & _); exact X).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(A, A + 32); (G, G + 32); (D, D + Z.of_nat (length bytes))] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
unfold sync_cells in SY.
cps_norm.
cps_seg (po_w1 A G D usp lo sy).
destruct POST as (m1 & j8 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
assert (REP1 : sync_rep m1 A D sy bytes).
{ apply (sync_rep_transport _ m m1 A D sy bytes MU1 WM1); [| | exact REP]; cbn [disjoint_from]; (split; [left| exact I]); [clear - FA2 BF1 LOR; lia| clear - DLO LOR; lia]. }
clear SY. cps_seg_post.
refine (po_loop (pageout_fuel sy) Σ PMc ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m A G D f lo usp k bytes j0 j1 j2 j3 j8 r ogo sy' T
FDO MST A0 G0 INF FA1 FA2 FG1 FG2 SEP_AG LOW LOR SPT SPA D0 DLO _ sy m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ RES REP1 INV2 INL OG FR1 ART MI1 ST1 WM1 PF Hc0).
intros c' Hc'. apply Hk. rewrite ESP. exact Hc'.
Qed.
End OggPageoutCPS.
