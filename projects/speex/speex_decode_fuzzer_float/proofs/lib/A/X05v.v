(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05u X05t
X081 X05l X07y X05m X09f X06d X069 X05y X05w X064 X062 X063
X082 X08y X0b1 X0b0 X068 X0ay X061.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X12b X0z5 X0wl X0wn X0wm X0ys X0yq X0x2 X0wr X0wp X0wx X0wv X0zo X0ww X0yt X0zq X11l X11k X0x1 X11i X0wu.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0z5 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wm OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wp OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wx OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wv OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zo OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ww OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x1 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X11i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wu.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Local Ltac trm MU WM H tacD :=
lazymatch type of MU with
| munch ?W ?m ?m' =>
lazymatch type of H with
| rw_cells bsegs m ?A0 ?cs =>
let H' := fresh "T" in
assert (H' : rw_cells bsegs m' A0 cs)
by (apply (rw_cells_transport bsegs W m m' A0 cs H MU WM); cbn [disjoint_from]; simpl_sizes; tacD);
clear H; rename H' into H
end
end.

Lemma dst_obj_factsB : forall (RT : rt_sig), art_facts RT -> forall (Σ : rts RT) (m : mem) o n lo usp,
ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo <= usp -> usp + 16 <= USTACK_TOP -> pois_above (rt_pois RT Σ) usp -> 0 < n ->
dst_obj RT Σ m o n ->
acc bsegs m o n /\ 0 < o /\ o + n <= APP_TOP /\ (o + n <= SH_LO \/ SH_HI <= o) /\ (o + n <= lo \/ usp <= o) /\ IMG_TOP_B <= o /\ o mod 4 = 0
/\ (forall i, 0 <= i < n -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp (o + i))
/\ rng_class RT Σ o n
/\ (forall p k, In (p, k) (rt_live RT Σ) -> p + k <= o \/ o + n <= p).
Proof.
intros RT AF Σ m o n lo usp ART0 LOW LU UT POA N0 DST.
pose proof (dst_obj_facts RT AF Σ m o n lo usp ART0 LOW LU UT POA N0 DST) as (X1 & X2 & X3 & X4 & X5 & _ & X7 & X8 & X9 & X10).
split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
split; [| split; [exact X7|]; split; [exact X8|]; split; [exact X9| exact X10]].
destruct DST as [(f & k & INF & (O1 & O2 & O3 & O4)) | INP].
- pose proof (frame_facts RT AF Σ m f k ART0 INF) as (F0 & _ & FI & _). unfold IMG_TOP_B, SEGTOP_A in *. lia.
- pose proof (af_pois_range RT AF Σ m o n ART0 INP) as (A32 & _ & R1 & R2).
pose proof (POA (o, n) INP) as PA. unfold pz_lo in PA. cbn [fst] in PA.
pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
unfold STACK_WIN, USTACK_TOP, APP_TOP, SH_LO, SH_HI, IMG_TOP_B in *. lia.
Qed.

Section Ctl2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Theorem ctl2_cps_nb : forall st, ctl2_cps_at RT (DecNB st).
Proof using AF AF_LIB.
intros st Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUTL OUT STEREO S LBD r P lo FDO MST -> -> -> -> GRP REP EOUT DEP ND AL8 OK PRE LIVE DST FRMS CRD POA ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
cbn [ctl_stack] in LOR. unfold NBCTL_STACK in LOR.
pose proof REP as REP0. cbn [decst_rep] in REP0. destruct REP0 as [ELBD NB]. subst LBD.
pose proof (LIVE _ ltac:(left; reflexivity)) as INL. unfold blk_addr, blk_size in INL. cbn [fst snd] in INL. unfold NBSTATE_SIZEOF in INL.
destruct (live_below_lo RT AF Σ m S 2968 lo ART0 INL LOW) as (BD0 & BD1 & LOS).
destruct (af_acc_live RT AF Σ m S 2968 ART0 INL) as (_ & ACS).
pose proof (live_facts RT AF Σ m S 2968 ART0 INL) as (_ & _ & SIMG & SHI).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (AF_LIB Σ m ART0) as LC0.
assert (OBM : aobj bsegs m A_speex_nb_mode 96)
by (apply (aobj_lit RT AF Σ m A_speex_nb_mode 96 ART0); [unfold ACC_LITS, A_speex_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_nb_mode; lia | unfold A_speex_nb_mode, APP_TOP; lia]).
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.

assert (DSTP : match r with CtlSetInnovationSave _ => True
| _ => aobj bsegs m P (creq_size r) /\ P mod 4 = 0 /\ IMG_TOP_B <= P /\ (P + creq_size r <= SH_LO \/ SH_HI <= P) /\ (P + creq_size r <= lo \/ usp <= P)
/\ (forall b, In b [(nb_blk st, S, NBSTATE_SIZEOF)] -> P + creq_size r <= blk_addr b \/ blk_addr b + blk_size b <= P) end).
{ destruct r; try discriminate GRP; try exact I; cbn [creq_size] in *;
[ pose proof (dst_obj_factsB RT AF Σ m P 16 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_factsB RT AF Σ m P 16 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_factsB RT AF Σ m P 4 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF ];
destruct DF as (ACP & PP0 & PT & POFF & PAP & PIMG & P4 & _ & _ & PLV);
(split; [split; [lia|]; split; [exact PT| exact ACP]|]; split; [exact P4|]; split; [exact PIMG|]; split; [exact POFF|]; split; [exact PAP|];
intros b [<-|[]]; unfold blk_addr, blk_size; cbn [fst snd]; unfold NBSTATE_SIZEOF; pose proof (PLV _ _ INL) as PLS; clear - PLS; lia). }
cps_norm.
refine (rz_evt RT AF Σ PMc _ _ T c MST Hc (rctl2_nb st OUTL OUT STEREO S _ r P lo usp ra gp (Z_to_bv 64 6524056) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m GRP REP EOUT OK PRE _ DSTP OBM ST0 LOS _ _ CC0 LC0 MI0 FRM0) _).
- intros b [<-|[]]. unfold ablk, blk_addr, blk_size. cbn [fst snd]. unfold NBSTATE_SIZEOF.
split; [split; [lia|]; split; [ulc| exact ACS]|]. split; [exact (proj1 NB)|]. split; [unfold SH_LO, SH_HI; lia|]. split; [unfold IMG_TOP_B; ulc| exact BD1].
- unfold NBCTL_STACK. ulc.
- ulc.
- intros ms' c' POST Hc'. clear Hc.
destruct POST as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F' & fc' & m' & -> & MU & WM & MI' & FRM' & ST' & REP' & CP' & EXC').

assert (PF : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (creq_ivs P r ++ blocks_ivs [(nb_blk st, S, NBSTATE_SIZEOF)]) m m').
{ apply (pres_fp_of_munch _ _ _ _ _ m m' MU). intros x Hx Ho. unfold ctlW. apply outside_cons. split; [| exact Ho].
cbn [fst snd]. pose proof (SPL x Hx) as SX. clear - SX LOW. lia. }
assert (ACLP : match r with CtlSetInnovationSave _ => True | _ => forall i, 0 <= i < creq_size r -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp (P + i) end).
{ destruct r; try discriminate GRP; try exact I; cbn [creq_size] in *;
[ pose proof (dst_obj_factsB RT AF Σ m P 16 lo usp ART0 LOW ltac:(ulc) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_factsB RT AF Σ m P 16 lo usp ART0 LOW ltac:(ulc) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_factsB RT AF Σ m P 4 lo usp ART0 LOW ltac:(ulc) SPT POA ltac:(lia) DST) as DF ];
exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DF)))))))). }
assert (ART' : X14x.ART RT Σ m').
{ apply (af_frame RT AF Σ m m' lo ART0 LOW); [| exact WM]. intros a0 Ha. apply MU.
unfold ctlW. apply outside_cons. cbn [fst snd]. split; [intros Hin; apply Ha; left; clear - Hin SPT; unfold USTACK_TOP in *; lia|].
assert (HB : outside (blocks_ivs [(nb_blk st, S, NBSTATE_SIZEOF)]) (bv_unsigned a0)).
{ cbn [blocks_ivs map outside blk_addr blk_size fst snd]. unfold NBSTATE_SIZEOF. split; [| exact I].
intros Hin; apply Ha; right; right; left; exists S, 2968; split; [exact INL| exact Hin]. }
destruct r; try discriminate GRP; cbn [creq_ivs creq_size app] in *; try exact HB; apply outside_cons; cbn [fst snd]; (split; [| exact HB]);
intros Hin; apply Ha;
(apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp (rt_live RT Σ) (rt_frames RT Σ) lo); [| intros e He; exact He| intros e He; exact He| ulc]);
replace (bv_unsigned a0) with (P + (bv_unsigned a0 - P)) by ring; apply ACLP; clear - Hin; lia. }
assert (DST' : match r with CtlSetInnovationSave _ => True | _ => dst_obj RT Σ m' P (creq_size r) end).
{ assert (OFW : offsh (ctlW lo usp P r [(nb_blk st, S, NBSTATE_SIZEOF)])).
{ unfold ctlW. destruct r; try discriminate GRP; cbn [creq_ivs creq_size app blocks_ivs map blk_addr blk_size fst snd offsh]; unfold NBSTATE_SIZEOF;
cbn [creq_size] in *; try exact I;
[ pose proof (dst_obj_factsB RT AF Σ m P 16 lo usp ART0 LOW ltac:(ulc) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_factsB RT AF Σ m P 16 lo usp ART0 LOW ltac:(ulc) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_factsB RT AF Σ m P 4 lo usp ART0 LOW ltac:(ulc) SPT POA ltac:(lia) DST) as DF | ];
try destruct DF as (_ & _ & _ & POFF & _);
repeat split; first [clear - LOS SHI POFF SPT | clear - LOS SHI SPT]; unfold SH_LO, SH_HI in *; lia. }
destruct r; try discriminate GRP; try exact I; cbn [creq_size] in *;
(destruct DST as [(f & k & INF & (O1 & O2 & O3 & O4)) | INP]; [left; exists f, k; split; [exact INF|]; split; [exact O1|]; split; [exact O2|]; split; [| exact O4] | right; exact INP]);
(pose proof (frame_facts RT AF Σ m f k ART0 INF) as (FF0 & _);
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (FB & _ & _);
refine (proj2 (proj2 (aobj_munch bsegs _ m m' P _ (conj _ (conj _ O3)) MU _))); [clear - FF0 O1; lia| clear - O2 FB LOR SPT; unfold APP_TOP, USTACK_TOP, RT_STACK in *; lia|];
apply shfree_of_offsh; [exact OFW| clear - FF0 O1; lia| clear - O2 FB LOR SPT; unfold APP_TOP, USTACK_TOP, RT_STACK in *; lia]). }
apply Hk. exists Σ. split; [| cbn [dec_depth]; repeat split; lia].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM']|].
split. { split; [exact ART'|]. split; [exact MI'|]. split; [exact WM| exact ST']. }
split; [exact PF|]. split; [exact REP'|]. split; [exact CP'|]. split; [exact EXC'| exact DST'].
Qed.

Section SBARMS2.
Variables (usp S P f sf : Z) (gp tp t0 t1 t2 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Let R (c : Z) (xra xa0 xa1 xa2 xa3 xa4 xa5 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96)) xa0 xa1 xa2 xa3 xa4 xa5 a6 a7
(Z_to_bv 64 f) (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 c) (Z_to_bv 64 f) (Z_to_bv 64 sf) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6.
Hypothesis MI : mem_inv bsegs m.
Hypothesis SB : 0 < S /\ S + 160 < 2^63.
Hypothesis PB : 0 <= P /\ P + 24 < 2^63.
Hypothesis OBS : aobj bsegs m S 160.
Hypothesis S8 : S mod 8 = 0.
Hypothesis SOFF : S + 160 <= SH_LO \/ SH_HI <= S.

Lemma sbarm2_pig : forall (s : sbd_state bptr) (a : sb_addrs) (OUT : Z) (j : sb_junk) (mp al : Z) (ffs fs sfs lpc fst sr enh : word) (qs ws : list word)
(ra a0 a1 a2 a3 a4 a5 : word),
rw_cells bsegs m S (sbhd mp al ffs fs sfs (Z_to_bv 64 4) lpc fst sr enh) -> rw_cells bsegs m (S + 48) (sbtl s a OUT j) ->
aobj bsegs m (a_pg a) 16 -> a_pg a mod 8 = 0 -> 0 < a_pg a -> rw_cells bsegs m (a_pg a) (f32 qs) -> length qs = 4%nat ->
aobj bsegs m P 16 -> P mod 4 = 0 -> 0 < P -> rw_cells bsegs m P (f32 ws) -> length ws = 4%nat ->
(P + 16 <= S \/ S + 160 <= P) -> (P + 16 <= a_pg a \/ a_pg a + 16 <= P) -> (P + 16 <= SH_LO \/ SH_HI <= P) ->
evt bsegs (fun ms' => exists (m' : mem) (F' : bvmap 5 word) (ws' : list word) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 : word),
ms' = MS (mkR ra (Z_to_bv 64 (usp + -96)) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96)) (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 f) (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 100) (Z_to_bv 64 f) (Z_to_bv 64 sf) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom bsegs)
/\ munch [(P, P + 16)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' P (f32 ws') /\ length ws' = 4%nat /\ rw_cells bsegs m' (a_pg a) (f32 qs)
/\ rw_cells bsegs m' S (sbhd mp al ffs fs sfs (Z_to_bv 64 4) lpc fst sr enh) /\ rw_cells bsegs m' (S + 48) (sbtl s a OUT j))
(MS (R 100 ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc 100)) fc None m (seg_rom bsegs)).
Proof using All.
intros s a OUT j mp al ffs fs sfs lpc fst sr enh qs ws ra a0 a1 a2 a3 a4 a5 HD TL OBQ Q8 QPOS QS LQS OBP P4 PPOS WS LWS APS APQ POFF.
unfold sbhd, sbtl in *. unfold R, A_sbctl_epi, sbctl_armpc. cbn [Z.eqb Pos.eqb].
pose proof OBS as (OS0 & OS1 & _). pose proof OBP as (OP0 & OP1 & _). pose proof OBQ as (OQ0 & OQ1 & _). unfold APP_TOP in *.
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof POFF as POFF'. unfold SH_LO, SH_HI in POFF'.
pose proof (munch_refl [(P, P + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(P, P + 16)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (Q4 : a_pg a mod 4 = 0) by (clear - Q8; Z.div_mod_to_equations; lia).
assert (Q4a : (a_pg a + 4) mod 4 = 0) by (clear - Q8; Z.div_mod_to_equations; lia).
assert (Q4b : (a_pg a + 8) mod 4 = 0) by (clear - Q8; Z.div_mod_to_equations; lia).
assert (Q4c : (a_pg a + 12) mod 4 = 0) by (clear - Q8; Z.div_mod_to_equations; lia).
assert (P4a : (P + 4) mod 4 = 0) by (clear - P4; Z.div_mod_to_equations; lia).
assert (P4b : (P + 8) mod 4 = 0) by (clear - P4; Z.div_mod_to_equations; lia).
assert (P4c : (P + 12) mod 4 = 0) by (clear - P4; Z.div_mod_to_equations; lia).
destruct qs as [|q0 [|q1 [|q2 [|q3 []]]]]; cbn [length] in LQS; try lia.
destruct ws as [|w0 [|w1 [|w2 [|w3 []]]]]; cbn [length] in LWS; try lia.
rewrite !f32_cons, f32_nil in QS, WS.
bato 0xbd828. rewrite sx32_lit by lia. bato 0xbd8c4.
astep. chk_merge OBP 4.
bato 0xbd8c4. astep. chk_merge OBP 4.
bato 0xbd8c4. astep. chk_merge OBP 4.
bato 0xbd8c4. astep. chk_merge OBP 4.
bato 0xbe340.
apply evt_done. do 2 eexists. exists [Sem.nan_box (Sem.low32 q0); Sem.nan_box (Sem.low32 q1); Sem.nan_box (Sem.low32 q2); Sem.nan_box (Sem.low32 q3)].
do 10 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [rewrite !f32_cons, f32_nil; exact WS|]. split; [reflexivity|]. split; [rewrite !f32_cons, f32_nil; exact QS|].
split; [exact HD| exact TL].
Qed.

Lemma sbarm2_exc : forall (s : sbd_state bptr) (a : sb_addrs) (OUT : Z) (j : sb_junk) (mp al : Z) (ffs fs sfs lpc fst sr enh : word) (qs ws : list word)
(ra a0 a1 a2 a3 a4 a5 : word),
rw_cells bsegs m S (sbhd mp al ffs fs sfs (Z_to_bv 64 4) lpc fst sr enh) -> rw_cells bsegs m (S + 48) (sbtl s a OUT j) ->
aobj bsegs m (a_er a) 16 -> a_er a mod 8 = 0 -> 0 < a_er a -> rw_cells bsegs m (a_er a) (f32 qs) -> length qs = 4%nat ->
aobj bsegs m P 16 -> P mod 4 = 0 -> 0 < P -> rw_cells bsegs m P (f32 ws) -> length ws = 4%nat ->
(P + 16 <= S \/ S + 160 <= P) -> (P + 16 <= a_er a \/ a_er a + 16 <= P) -> (P + 16 <= SH_LO \/ SH_HI <= P) ->
evt bsegs (fun ms' => exists (m' : mem) (F' : bvmap 5 word) (ws' : list word) (xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 : word),
ms' = MS (mkR ra (Z_to_bv 64 (usp + -96)) gp tp xt0 xt1 xt2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96)) (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5 xa6 xa7
(Z_to_bv 64 f) (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 101) (Z_to_bv 64 f) (Z_to_bv 64 sf) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom bsegs)
/\ munch [(P, P + 16)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
/\ rw_cells bsegs m' P (f32 ws') /\ length ws' = 4%nat /\ rw_cells bsegs m' (a_er a) (f32 qs)
/\ rw_cells bsegs m' S (sbhd mp al ffs fs sfs (Z_to_bv 64 4) lpc fst sr enh) /\ rw_cells bsegs m' (S + 48) (sbtl s a OUT j))
(MS (R 101 ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc 101)) fc None m (seg_rom bsegs)).
Proof using All.
intros s a OUT j mp al ffs fs sfs lpc fst sr enh qs ws ra a0 a1 a2 a3 a4 a5 HD TL OBQ Q8 QPOS QS LQS OBP P4 PPOS WS LWS APS APQ POFF.
unfold sbhd, sbtl in *. unfold R, A_sbctl_epi, sbctl_armpc. cbn [Z.eqb Pos.eqb].
pose proof OBS as (OS0 & OS1 & _). pose proof OBP as (OP0 & OP1 & _). pose proof OBQ as (OQ0 & OQ1 & _). unfold APP_TOP in *.
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof POFF as POFF'. unfold SH_LO, SH_HI in POFF'.
pose proof (munch_refl [(P, P + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(P, P + 16)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (Q4 : a_er a mod 4 = 0) by (clear - Q8; Z.div_mod_to_equations; lia).
assert (Q4a : (a_er a + 4) mod 4 = 0) by (clear - Q8; Z.div_mod_to_equations; lia).
assert (Q4b : (a_er a + 8) mod 4 = 0) by (clear - Q8; Z.div_mod_to_equations; lia).
assert (Q4c : (a_er a + 12) mod 4 = 0) by (clear - Q8; Z.div_mod_to_equations; lia).
assert (P4a : (P + 4) mod 4 = 0) by (clear - P4; Z.div_mod_to_equations; lia).
assert (P4b : (P + 8) mod 4 = 0) by (clear - P4; Z.div_mod_to_equations; lia).
assert (P4c : (P + 12) mod 4 = 0) by (clear - P4; Z.div_mod_to_equations; lia).
destruct qs as [|q0 [|q1 [|q2 [|q3 []]]]]; cbn [length] in LQS; try lia.
destruct ws as [|w0 [|w1 [|w2 [|w3 []]]]]; cbn [length] in LWS; try lia.
rewrite !f32_cons, f32_nil in QS, WS.
bato 0xbe1d8. rewrite sx32_lit by lia. bato 0xbe274.
astep. chk_merge OBP 4.
bato 0xbe274. astep. chk_merge OBP 4.
bato 0xbe274. astep. chk_merge OBP 4.
bato 0xbe274. astep. chk_merge OBP 4.
bato 0xbe340.
apply evt_done. do 2 eexists. exists [Sem.nan_box (Sem.low32 q0); Sem.nan_box (Sem.low32 q1); Sem.nan_box (Sem.low32 q2); Sem.nan_box (Sem.low32 q3)].
do 10 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [rewrite !f32_cons, f32_nil; exact WS|]. split; [reflexivity|]. split; [rewrite !f32_cons, f32_nil; exact QS|].
split; [exact HD| exact TL].
Qed.

Lemma sbarm2_isv : forall (s : sbd_state bptr) (a : sb_addrs) (OUTL OUT' off : Z) (j : sb_junk) (ra a0 a1 a2 a3 a4 a5 : word),
P = OUT' + 4 * off ->
rw_cells bsegs m (S + 48) (sbtl s a OUTL j) ->
evt bsegs (fun ms' => exists (m' : mem) (xa1 : word), ms' = MS (R 104 ra (Z_to_bv 64 0) xa1 a2 a3 a4 a5) F (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom bsegs)
/\ rw_cells bsegs m' (S + 48) (sbtl (set_sbd_innov_save s (Some off)) a OUT' j)
/\ munch [(S + 120, S + 128)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m')
(MS (R 104 ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc 104)) fc None m (seg_rom bsegs)).
Proof using MI SB OBS S8 SOFF.
clear PB. intros s a OUTL OUT' off j ra a0 a1 a2 a3 a4 a5 EP TL.
unfold sbtl in *. unfold R, A_sbctl_epi, sbctl_armpc. cbn [Z.eqb Pos.eqb].
pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *. pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'.
pose proof (munch_refl [(S + 120, S + 128)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(S + 120, S + 128)]) by (cbn; unfold SH_LO, SH_HI; lia).
bato 0xbe340.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [| split; [exact MU|]; split; [exact WM| assumption]].
cbn [sb_isave_ptr set_sbd_innov_save sbd_innov_save sbd_encode_submode sbd_mode sbd_submodeID]. rewrite <- EP. exact TL.
Qed.

Lemma sbarm2_dtx : forall (mp al : Z) (ffs fs sfs nsf lpc fst sr enh : word) (ra a0 a1 a2 a3 a4 a5 : word),
rw_cells bsegs m S (sbhd mp al ffs fs sfs nsf lpc fst sr enh) ->
evt bsegs (fun ms' => exists xa3 xa4 xa5 : word,
ms' = MS (R 103 (Z_to_bv 64 0xbe1ac) (Z_to_bv 64 al) (Z_to_bv 64 103) (Z_to_bv 64 P) xa3 xa4 xa5) F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom bsegs))
(MS (R 103 ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc 103)) fc None m (seg_rom bsegs)).
Proof using MI SB OBS S8 SOFF.
clear PB. intros mp al ffs fs sfs nsf lpc fst sr enh ra a0 a1 a2 a3 a4 a5 HD. unfold sbhd in HD. unfold R, A_speex_decoder_ctl, sbctl_armpc. cbn [Z.eqb Pos.eqb].
pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *.
bato 0x98c74.
apply evt_done. do 3 eexists. reflexivity.
Qed.
End SBARMS2.

Lemma sbctl_w1_anyP : forall (usp lo S MP P c : Z) (hrest : list cell) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells bsegs m S (C8 (Z_to_bv 64 MP) :: hrest) -> Z.of_nat (cells_size hrest) = 40 ->
aobj bsegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= lo \/ usp <= S) ->
ro_cells bsegs m MP (sb_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11) -> aobj bsegs m MP 96 -> MP mod 8 = 0 -> 0x10000 <= MP -> MP + 104 <= 0x65a180 ->
0 <= c < 2^31 ->
stk bsegs m lo usp -> lo <= usp - 96 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_constsB m -> mem_inv bsegs m ->
evt bsegs (fun ms => exists (m1 : mem) (j8 : list byte) (xt1 xa3 xa4 xa5 : word),
ms = MS (mkR (Z_to_bv 64 RA_sbctl_smalloc) (Z_to_bv 64 (usp + -96)) gp tp t0 xt1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96))
(Z_to_bv 64 64) (Z_to_bv 64 gB_shadow_memory_dynamic_address) (Z_to_bv 64 1) xa3 xa4 xa5 a6 a7
s2 (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 c) s6 s7 (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_stack_malloc_0) fc None m1 (seg_rom bsegs)
/\ munch [(usp + -96, usp)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (usp + -96)
/\ rw_cells bsegs m1 (usp + -96) (sbctl_frame (CB 8 j8) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 c) (Z_to_bv 64 P) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom bsegs)).
Proof.
intros until m. intros P0 HR OBS S8 S0 SHI AP ND OBM AL8 MPLO MPHI CR ST LO LOS SPH SP32 (G1 & G2 & G3 & G4) MI.
unfold A_speex_decoder_ctl, RA_sbctl_smalloc, e_stack_malloc_0, sbctl_frame, sb_desc_cells, A_sb_decoder_ctl,
gB_GOT_shadow_offset_cell, gB_shadow_memory_dynamic_address, gB_GOT_detect_uar, gB_detect_stack_use_after_return in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (munch_refl [(usp + -96, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
assert (OF : offsh [(usp + -96, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 96%nat ST.
apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
bato 0xbd590.
bato 0xbd5c4. astep. rewrite land_m32_al by lia.
bato 0xbd5f0. rewrite sx32_small by (unfold int31; lia).
bato 0x51314.
apply evt_done. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Lemma creq2_pre_agree_sb : forall STEREO (m m' : mem) S S' s low s' low' P r, creq_grp1 r = false ->
creq_pre STEREO m S (DecSB s low) P r -> agree_at bsegs m m' P (creq_size r) -> creq_pre STEREO m' S' (DecSB s' low') P r.
Proof.
intros STEREO m m' S S' s low s' low' P r G PRE AG. destruct r; try discriminate G; cbn [creq_pre creq_size dec_exc_ready] in *.
- destruct PRE as (ws & X & L). exists ws. split; [| exact L]. exact (rw_cells_agree_at bsegs m m' P _ X ltac:(rewrite cells_size_f32, L; exact AG)).
- destruct PRE as ((ws & X & L) & _). split; [| exact I]. exists ws. split; [| exact L]. exact (rw_cells_agree_at bsegs m m' P _ X ltac:(rewrite cells_size_f32, L; exact AG)).
- destruct PRE as (w & X). exists w. exact (rw_cells_agree_at bsegs m m' P _ X AG).
- exact I.
Qed.

Lemma dst_obj_sigma : forall (Σ Σ' : rts RT) (m : mem) o n, dst_obj RT Σ m o n -> rt_frames RT Σ' = rt_frames RT Σ -> rt_pois RT Σ' = rt_pois RT Σ -> dst_obj RT Σ' m o n.
Proof.
intros Σ Σ' m o n [(f & k & INF & IFO) | INP] EF EP; [left; exists f, k; split; [rewrite EF; exact INF| exact IFO]| right; rewrite EP; exact INP].
Qed.

Theorem ctl2_cps_sb : forall s low, ctl2_cps_at RT low -> ctl2_cps_at RT (DecSB s low).
Proof using AF SM0 AF_LIB.
intros s low IH Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUTL OUT STEREO S LBD r P lo FDO MST -> -> -> -> GRP REP EOUT DEP ND AL8 OK PRE LIVE DST FRMS CRD POA ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
cbn [ctl_stack dec_depth] in LOR, DEP, FRMS, CRD.
assert (CSP : 0 <= ctl_stack low) by (clear; induction low; cbn [ctl_stack]; unfold NBCTL_STACK; lia).
pose proof REP as REP0. cbn [decst_rep] in REP0. destruct REP0 as (a & j & LBL & ELBD & S8 & SPOS & INV & JOK & X & BUFS & OUTLL & RLOW).
pose proof INV as (IMODE & _).
rewrite sb_cells_split in X.

assert (INL : In (S, 160) (rt_live RT Σ)).
{ specialize (LIVE (sbd_blk s, S, SBSTATE_SIZEOF)). rewrite ELBD in LIVE. specialize (LIVE ltac:(left; reflexivity)). exact LIVE. }
destruct (live_below_lo RT AF Σ m S 160 lo ART0 INL LOW) as (_ & BS1 & LOS).
destruct (af_acc_live RT AF Σ m S 160 ART0 INL) as (_ & ACS).
pose proof (live_facts RT AF Σ m S 160 ART0 INL) as (_ & _ & _ & SHI).
assert (SZ : 0 <= creq_size r <= 16) by (destruct r; try discriminate GRP; cbn; lia).

assert (PDF : forall x, P <= x < P + creq_size r -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x /\ (forall p k, In (p, k) (rt_live RT Σ) -> ~ (p <= x < p + k))).
{ destruct r; try discriminate GRP; cbn [creq_size] in *; try (intros x Hx; exfalso; lia);
[ pose proof (dst_obj_factsB RT AF Σ m P 16 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_factsB RT AF Σ m P 16 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_factsB RT AF Σ m P 4 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF ];
destruct DF as (_ & _ & _ & _ & _ & _ & _ & ACL & _ & PLV);
(intros x Hx; split; [replace x with (P + (x - P)) by ring; apply ACL; lia| intros p k Hp Hin; pose proof (PLV p k Hp) as H; lia]). }

assert (DF0 : match r with CtlSetInnovationSave _ => True
| _ => acc bsegs m P (creq_size r) /\ 0 < P /\ P + creq_size r <= APP_TOP /\ (P + creq_size r <= SH_LO \/ SH_HI <= P)
/\ (P + creq_size r <= lo \/ usp <= P) /\ IMG_TOP_B <= P /\ P mod 4 = 0 end).
{ destruct r; try discriminate GRP; try exact I; cbn [creq_size] in *;
[ pose proof (dst_obj_factsB RT AF Σ m P 16 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_factsB RT AF Σ m P 16 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_factsB RT AF Σ m P 4 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF ];
destruct DF as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & _); exact (conj D1 (conj D2 (conj D3 (conj D4 (conj D5 (conj D6 D7)))))). }
assert (ACCK2 : forall m', rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + creq_size r) :: blocks_ivs LBD) m m' ->
match r with CtlSetInnovationSave _ => True | _ => dst_obj RT Σ m' P (creq_size r) end).
{ intros m' PR. destruct r; try discriminate GRP; try exact I; cbn [creq_size] in *;
(destruct DST as [(fp & kp & INFP & (O1 & O2 & O3 & O4)) | INP]; [left; exists fp, kp; split; [exact INFP|]; split; [exact O1|]; split; [exact O2|]; split; [| exact O4] | right; exact INP]);
(apply (acc_of_pres_fp RT AF Σ m m m' usp _ fp kp P _ ART0 INFP O1 O2 PR); [| exact O3]);
(intros x Hx; split; [cbn [fst snd]; pose proof (frame_facts RT AF Σ m fp kp ART0 INFP) as (_ & _ & _ & _ & FH & _); pose proof (fs_size_ge64 kp) as FSZ;
clear - Hx FH O1 O2 FSZ; unfold SH_LO, SH_HI in *; lia
| exact (outside_blocks_shadow RT AF Σ m LBD x ART0 LIVE Hx)]). }

pose proof (AF_LIB Σ m ART0) as LC0.
set (MP := sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) in *.
assert (MPF : exists c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11, ro_cells bsegs m MP (sb_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11)
/\ aobj bsegs m MP 96 /\ MP mod 8 = 0 /\ 0x10000 <= MP /\ MP + 104 <= 0x65a180).
{ subst MP. destruct IMODE as [E|E]; rewrite E; cbn [sb_mode_ptr].
- do 12 eexists. split; [exact (lib_const m A_speex_wb_mode LC_speex_wb_mode LC0 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ m A_speex_wb_mode 96 ART0); [unfold ACC_LITS, A_speex_wb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_wb_mode; lia | unfold A_speex_wb_mode, APP_TOP; lia]|].
unfold A_speex_wb_mode. repeat split; lia.
- do 12 eexists. split; [exact (lib_const m A_speex_uwb_mode LC_speex_uwb_mode LC0 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ m A_speex_uwb_mode 96 ART0); [unfold ACC_LITS, A_speex_uwb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_uwb_mode; lia | unfold A_speex_uwb_mode, APP_TOP; lia]|].
unfold A_speex_uwb_mode. repeat split; lia. }
destruct MPF as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & ND0 & OBM & MP8 & MPLO & MPHI).
pose proof (eq_refl : MP = sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) as EMP. clearbody MP.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (OBS : aobj bsegs m S 160) by (split; [lia|]; split; [unfold APP_TOP, STACK_WIN, USTACK_TOP, RT_STACK in *; lia| exact ACS]).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp (blocks_ivs LBD) m) as PF.
pose proof (fun E : rt_frames RT Σ = [] => af_pois_nil RT AF Σ m ART0 E) as PNIL.
assert (LIVE0 : blocks_in_live RT Σ LBD) by exact LIVE.
assert (POUT : forall x, P <= x < P + creq_size r -> outside (blocks_ivs LBD) x).
{ intros x Hx. apply outside_blocks_ivs. intros b Hb Hin. exact (proj2 (PDF x Hx) _ _ (LIVE b Hb) Hin). }
assert (PCL : forall x, P <= x < P + creq_size r -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x) by (intros x Hx; exact (proj1 (PDF x Hx))).
pose proof (fun m' S' low' (PR : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (blocks_ivs LBD) m m') (WM : wmono bsegs m m')
(PB0 : 0 <= P) (PB1 : P + creq_size r <= 2^64) =>
creq2_pre_agree_sb STEREO m m' S S' s low s low' P r GRP PRE
(agree_at_of_pres_fp _ _ usp _ m m' P (creq_size r) PR WM PB0 PB1 (fun x Hx => conj (PCL x Hx) (POUT x Hx)))) as PREK.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
assert (CODE : sbctl_code_ok (ctl_req_code r)) by (unfold sbctl_code_ok; destruct r; cbn [ctl_req_code]; tauto).
assert (CRNG : 0 <= ctl_req_code r < 2^31) by (destruct r; cbn; lia).
assert (LO96 : lo <= usp + -96) by (clear - LOR CSP; unfold RT_STACK in LOR; lia).
cps_norm. cps_hide.

piece X HD. rename X into TL. unfold sbhd in HD. unfold sbtl in TL.
cps_seg (sbctl_w1_anyP usp lo S MP P (ctl_req_code r)).
{ reflexivity. } { ulc. }
destruct POST as (m1 & j8 & xt1 & xa3 & xa4 & xa5 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
assert (BOUT : forall b x, In b (tl (sb_blocks s S a) ++ LBL) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ ~ (P <= x < P + creq_size r)).
{ intros b x Hb Hx.
assert (Hb' : In b LBD) by (rewrite ELBD; cbn [sb_blocks tl app] in Hb |- *; right; exact Hb).
pose proof (LIVE b Hb') as LB.
destruct (live_below_lo RT AF Σ m _ _ lo ART0 LB LOW) as (_ & B1 & _).
assert (NE : blk_addr b <> S).
{ rewrite ELBD in ND. cbn [sb_blocks app map blk_id blk_addr fst snd] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _].
intros E. apply NI. rewrite <- E. cbn [sb_blocks tl app] in Hb. exact (in_map blk_id _ _ Hb). }
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 LB INL NE) as B3.
split; [clear - B1 Hx; lia|]. split; [clear - B3 Hx; unfold hid in *; lia|].
intros HP. exact (proj2 (PDF x HP) _ _ LB Hx). }
pose proof (agree_blocks_of_munch bsegs _ m m1 (tl (sb_blocks s S a) ++ LBL) MU1 WM1
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO96; cbn [outside]; split; [lia| exact I])) as AG1.
cps_seg_post.
apply (sb_bufs_agree s S a j m m1) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG1| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG1| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG1.

cps_rt_sized SM0 0. { cbn; tauto. } { pose proof (dec_depth_pos low) as DP; clear - CRD DP; lia. } { cps_callok. }
intros cc2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
Time cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS).
assert (LIVE1 : blocks_in_live RT Σ1 LBD) by (intros b Hb; rewrite LV1; exact (LIVE b Hb)).
pose proof (agree_blocks_of_pres RT Σ (rt_frames RT Σ) (usp + -96) m1 m2 (tl (sb_blocks s S a) ++ LBL) PRES2 WM2
ltac:(intros b Hb; apply LIVE; rewrite ELBD; cbn [sb_blocks tl app] in Hb |- *; right; exact Hb)) as AG2.
apply (sb_bufs_agree s S a j m1 m2) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG2| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG2| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG2.
Time cps_new_frame ART2 FRS1 LV1 SP1 WRF WRS sf. cps_hide.
assert (BOUT2 : forall b x, In b (tl (sb_blocks s S a) ++ LBL) -> blk_addr b <= x < blk_addr b + blk_size b ->
(x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x Hb Hx.
assert (Hb' : In b LBD) by (rewrite ELBD; cbn [sb_blocks tl app] in Hb |- *; right; exact Hb).
destruct (frame_live_apart RT AF Σ1 m2 f 0%nat _ _ ART2 INF (LIVE1 b Hb')) as (B2 & B3).
change (fs_size 0) with 64 in B2, B3. rewrite SHF0, <- SHF in B3. clear - B2 B3 Hx. lia. }

cps_seg (sbctl_w2 usp lo S P (ctl_req_code r) f sf).
destruct POST as (m3 & a0' & a1' & a2' & j24 & l32 & j36 & j40 & l48 & j52 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & FRB3 & FRS3).
Time pose proof (agree_blocks_of_munch bsegs _ m2 m3 (tl (sb_blocks s S a) ++ LBL) MU3 WM3
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; pose proof (BOUT2 b x Hb Hx) as H2; clear - H1 H2 LO96; cbn [outside]; repeat split; lia)) as AG3.
apply (sb_bufs_agree s S a j m2 m3) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG3| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG3| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG3 FR1 FRB FRS.
unfold sbctl_frame in FR3. unfold sbctl_fhdr in FRB3. unfold sbctl_shadow, bF1, bF3, bF8 in FRS3.
cps_seg_post.
destruct (af_acc_live RT AF Σ1 m3 S 160 ART INL) as (_ & ACS3).
assert (OBS3 : aobj bsegs m3 S 160) by (split; [lia|]; split; [ulc| exact ACS3]).
assert (SOFF : S + 160 <= SH_LO \/ SH_HI <= S) by (clear - SHI; unfold hid, SH_LO, SH_HI in *; lia).
assert (HD3 : rw_cells bsegs m3 S (sbhd MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s))
(Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s))
(Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)))) by exact HD.
assert (SBF : 0 < S /\ S + 160 < 2^63) by (split; ulc).
clear HD. cps_hide.
assert (WM03 : wmono bsegs m m3) by cps_wmono.
assert (PRE3 : match r with CtlSetInnovationSave _ => True | _ => creq_pre STEREO m3 S (DecSB s low) P r end).
{ destruct r; try discriminate GRP; try exact I; destruct DF0 as (_ & PP0 & PT & _);
exact (PREK m3 S low PF WM03 ltac:(clear - PP0; lia) ltac:(clear - PT; cbn [creq_size] in *; unfold APP_TOP in *; lia)). }
clear PREK PRE.
apply (pres_fp_weaken _ _ _ _ ((P, P + creq_size r) :: blocks_ivs LBD)) in PF; [| intros x Hx; exact (proj2 Hx)].
assert (OUTB : forall x, (lo <= x \/ (S <= x < S + 160) \/ (P <= x < P + creq_size r) \/ (f <= x < f + 64) \/ (sf <= x < sf + 8)) -> outside (blocks_ivs LBL) x).
{ intros x Hx. apply outside_blocks_ivs. intros b Hb Hin.
pose proof (BOUT b x ltac:(apply in_app_iff; right; exact Hb) Hin) as H1. pose proof (BOUT2 b x ltac:(apply in_app_iff; right; exact Hb) Hin) as H2.
clear - Hx H1 H2. lia. }
assert (APL : forall b x, In b (tl (sb_blocks s S a)) -> blk_addr b <= x < blk_addr b + blk_size b -> outside (blocks_ivs LBL) x).
{ intros b x Hb Hx. apply outside_blocks_ivs. intros b2 Hb2 Hin.
assert (NE : blk_addr b <> blk_addr b2).
{ rewrite ELBD, map_app in ND. apply (NoDup_app_in_neq _ _ (blk_id b) (blk_id b2) ND); [apply in_map; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| apply in_map; exact Hb2]. }
pose proof (live_apart RT AF Σ1 m3 _ _ _ _ ART (LIVE1 b ltac:(rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb))
(LIVE1 b2 ltac:(rewrite ELBD; apply in_app_iff; right; exact Hb2)) NE) as AP.
clear - AP Hx Hin. unfold hid in *. lia. }
assert (PFA : forall x, P <= x < P + creq_size r -> ~ (f <= x < f + 64) /\ ~ (sf <= x < sf + 8)) by (intros x Hx; exact (NAF x (PCL x Hx))).
assert (NDL : List.NoDup (map blk_id LBL)) by (rewrite ELBD, map_app in ND; exact (List.NoDup_app_remove_l _ _ ND)).
assert (LIVEL : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT Σ1)) by (intros b Hb; apply LIVE1; rewrite ELBD; apply in_app_iff; right; exact Hb).
assert (FRM1 : (length (rt_frames RT Σ1) + dec_depth low <= FRAMES_MAX)%nat) by (rewrite FRS1; cbn [length]; clear - FRMS; lia).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; ulc).
assert (SPA96 : (usp + -96) mod 32 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
assert (AL8L : blocks_al8 LBL) by (intros x Hx; apply AL8; rewrite ELBD; apply in_app_iff; right; exact Hx).
subst LBD. cbn [sb_blocks app blocks_ivs map blk_addr blk_size fst snd] in PF. unfold SBSTATE_SIZEOF in PF.
destruct r; try discriminate GRP; cbn [ctl_req_code creq_size creq_align] in *.
1: {
subst OUTL. destruct DF0 as (ACP & PP0 & PT & POFF & PAP & PIMG & P4).
cbn [creq_pre] in PRE3. destruct PRE3 as (ws & WS3 & LWS).
pose proof INV as (_ & _ & _ & _ & NSF4 & _).
assert (INPG : In (a_pg a, 16) (rt_live RT Σ1)) by exact (LIVE1 (sbd_pi_gain s, a_pg a, 16) ltac:(cbn [sb_blocks app In]; do 6 right; left; reflexivity)).
assert (INPG0 : In (a_pg a, 16) (rt_live RT Σ)) by (rewrite <- LV1; exact INPG).
destruct (af_acc_live RT AF Σ1 m3 _ _ ART INPG) as (_ & ACPG).
destruct (live_below_lo RT AF Σ1 m3 _ _ lo ART INPG LOW) as (PGP & PGLO & _).
assert (OBPG : aobj bsegs m3 (a_pg a) 16) by (split; [ulc|]; split; [ulc| exact ACPG]).
assert (PG8 : a_pg a mod 8 = 0) by exact (AL8 (sbd_pi_gain s, a_pg a, 16) ltac:(cbn [sb_blocks app In]; do 6 right; left; reflexivity)).
pose proof BUFS as (BG0 & BG1 & BEX & BOQ & BIQ & BMS & BPG & BER). clear BG0 BG1 BEX BOQ BIQ BMS BER.
pose proof JOK as (_ & _ & _ & _ & _ & _ & _ & _ & LPG & _).
assert (ACP3 : acc bsegs m3 P 16).
{ destruct (ACCK2 m3 PF) as [(fp & kp & INFP & (O1 & O2 & O3 & O4)) | INP]; [exact O3|]. apply (af_acc_pois RT AF Σ1 m3 P 16 ART). rewrite PO1. exact INP. }
assert (OBP3 : aobj bsegs m3 P 16) by (split; [lia|]; split; [ulc| exact ACP3]).
assert (INL0 : In (S, 160) (rt_live RT Σ)) by (rewrite <- LV1; exact INL).
assert (APS : P + 16 <= S \/ S + 160 <= P).
{ pose proof (proj2 (PDF P ltac:(lia)) S 160 INL0) as E1. pose proof (proj2 (PDF (P + 15) ltac:(lia)) S 160 INL0) as E2. clear - E1 E2. lia. }
assert (APQ : P + 16 <= a_pg a \/ a_pg a + 16 <= P).
{ pose proof (proj2 (PDF P ltac:(lia)) _ _ INPG0) as E1. pose proof (proj2 (PDF (P + 15) ltac:(lia)) _ _ INPG0) as E2. clear - E1 E2. lia. }
rewrite NSF4 in HD3.
cps_seg (sbarm2_pig usp S P f sf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 MI3 SBF ltac:(clear - PP0 PT; cbn in *; lia) OBS3 S8 SOFF
s a OUT j MP (a_low a) _ _ _ _ _ _ _ (sj_pg j) ws _ _ _ _ _ _ _ HD3 TL OBPG PG8 ltac:(destruct (live_below_lo RT AF Σ1 m3 _ _ lo ART INPG LOW) as (X & _); exact X) BPG LPG OBP3 P4 ltac:(clear - PP0; lia) WS3 LWS APS APQ POFF).
destruct POST as (m4 & F4 & ws4 & yt0 & yt1 & yt2 & yb1 & yb2 & yb3 & yb4 & yb5 & yb6 & yb7 & -> & MU4 & WM4 & MI4 & WS4 & LWS4 & BPG4 & HD4 & TL4).
pose proof (agree_blocks_of_munch bsegs _ m3 m4 (tl (sb_blocks s S a) ++ LBL) MU4 WM4
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1; cbn [outside]; split; [lia| exact I])) as AG4.
apply (sb_bufs_agree s S a j m3 m4) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG4 HD3 TL WS3 BPG BPG4 OBP3 OBPG APS APQ. unfold sbhd in HD4. unfold sbtl in TL4. rename TL4 into TL.
assert (PFA1 : P + 16 <= f \/ f + 64 <= P) by (pose proof (PFA P ltac:(lia)) as (E1 & _); pose proof (PFA (P + 15) ltac:(lia)) as (E2 & _); clear - E1 E2; lia).
assert (ART4 : X14x.ART RT Σ1 m4).
{ apply (af_frame RT AF Σ1 m3 m4 lo ART LOW); [| exact WM4]. intros a0 Ha. apply MU4. cbn [outside]. split; [| exact I]. intros Hin. apply Ha.
apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp (rt_live RT Σ1) (rt_frames RT Σ1) lo); [| intros e He; rewrite LV1; exact He| intros e He; rewrite FRS1; right; exact He| ulc].
apply PCL. exact Hin. }
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W m m3 =>
assert (PF4 : rt_pres_fp L Fr U W m m4)
by (apply (pres_fp_trans _ _ _ _ m m3 m4 PF); apply (pres_fp_of_munch _ _ _ _ _ m3 m4 MU4); intros x _ Ho; cbn [outside] in Ho |- *; destruct Ho as (Ho & _); split; [exact Ho| exact I])
end.
clear PF ART. rename PF4 into PF. rename ART4 into ART.
trm MU4 WM4 FR3 ltac:(clear - PAP LO96; unfold hid in *; lia).
trm MU4 WM4 FRB3 ltac:(clear - PFA1; lia).
trm MU4 WM4 FRS3 ltac:(clear - POFF SHF1 SHF2; unfold hid, SH_LO, SH_HI in *; lia).
assert (ST4 : stk bsegs m4 lo (usp + -96)) by (apply (stk_transport_disjoint bsegs _ m3 m4 lo (usp + -96) ST3 MU4 WM4); cbn [disjoint_from]; clear - PAP LO96; unfold hid in *; lia).
clear ST3 ST2 MU4 MI3.

assert (FRSE : rw_cells bsegs m4 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch bsegs _ m4 m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m4 m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ1 = (f, 0%nat) :: rt_frames RT Σ) by (exact FRS1).
assert (EL2 : rt_live RT Σ1 = rt_live RT Σ) by (exact LV1).
lazymatch goal with A : X14x.ART RT Σ1 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO1 (PNIL E)) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < P \/ P + 16 <= fl).
{ destruct (Z_lt_dec fl P) as [L|L]; [left; exact L|]. destruct (Z_le_dec (P + 16) fl) as [G|G]; [right; exact G|]. exfalso.
exact (NFL fl (PCL fl ltac:(clear - L G; lia)) eq_refl). }
assert (FR6 : rw_cells bsegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks bsegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch bsegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
rewrite <- NSF4 in HD4.
apply Hk. exists Σ3.
split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|];
split; [pose proof (dec_depth_pos low) as DP0; clear - EC CR1 DP0; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM0]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (dst_obj_sigma Σ Σ3 m7 P 16 (ACCK2 m7 PF) EF (eq_trans EP PO1)) as DST7.
cbn [speex_decoder_ctl fst snd creq_post dec_exc_ready creq_size].
split; [| split; [exists ws4; split; [exact WS4| exact LWS4]| split; [intros _; exact I| exact DST7]]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app bsegs m7 S _ _)); split; [exact HD4| exact TL]|].
split; [exact BUFS|]. exists OUTLL. exact RLOW. }
1: {
subst OUTL. destruct DF0 as (ACP & PP0 & PT & POFF & PAP & PIMG & P4).
cbn [creq_pre] in PRE3. destruct PRE3 as ((ws & WS3 & LWS) & _).
pose proof INV as (_ & _ & _ & _ & NSF4 & _).
assert (INER : In (a_er a, 16) (rt_live RT Σ1)) by exact (LIVE1 (sbd_exc_rms s, a_er a, 16) ltac:(cbn [sb_blocks app In]; do 7 right; left; reflexivity)).
assert (INER0 : In (a_er a, 16) (rt_live RT Σ)) by (rewrite <- LV1; exact INER).
destruct (af_acc_live RT AF Σ1 m3 _ _ ART INER) as (_ & ACER).
destruct (live_below_lo RT AF Σ1 m3 _ _ lo ART INER LOW) as (ERP & ERLO & _).
assert (OBER : aobj bsegs m3 (a_er a) 16) by (split; [ulc|]; split; [ulc| exact ACER]).
assert (ER8 : a_er a mod 8 = 0) by exact (AL8 (sbd_exc_rms s, a_er a, 16) ltac:(cbn [sb_blocks app In]; do 7 right; left; reflexivity)).
pose proof BUFS as (BG0 & BG1 & BEX & BOQ & BIQ & BMS & BPG & BER). clear BG0 BG1 BEX BOQ BIQ BMS BPG.
pose proof JOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & LPG).
assert (ACP3 : acc bsegs m3 P 16).
{ destruct (ACCK2 m3 PF) as [(fp & kp & INFP & (O1 & O2 & O3 & O4)) | INP]; [exact O3|]. apply (af_acc_pois RT AF Σ1 m3 P 16 ART). rewrite PO1. exact INP. }
assert (OBP3 : aobj bsegs m3 P 16) by (split; [lia|]; split; [ulc| exact ACP3]).
assert (INL0 : In (S, 160) (rt_live RT Σ)) by (rewrite <- LV1; exact INL).
assert (APS : P + 16 <= S \/ S + 160 <= P).
{ pose proof (proj2 (PDF P ltac:(lia)) S 160 INL0) as E1. pose proof (proj2 (PDF (P + 15) ltac:(lia)) S 160 INL0) as E2. clear - E1 E2. lia. }
assert (APQ : P + 16 <= a_er a \/ a_er a + 16 <= P).
{ pose proof (proj2 (PDF P ltac:(lia)) _ _ INER0) as E1. pose proof (proj2 (PDF (P + 15) ltac:(lia)) _ _ INER0) as E2. clear - E1 E2. lia. }
rewrite NSF4 in HD3.
cps_seg (sbarm2_exc usp S P f sf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 MI3 SBF ltac:(clear - PP0 PT; cbn in *; lia) OBS3 S8 SOFF
s a OUT j MP (a_low a) _ _ _ _ _ _ _ (sj_er j) ws _ _ _ _ _ _ _ HD3 TL OBER ER8 ltac:(destruct (live_below_lo RT AF Σ1 m3 _ _ lo ART INER LOW) as (X & _); exact X) BER LPG OBP3 P4 ltac:(clear - PP0; lia) WS3 LWS APS APQ POFF).
destruct POST as (m4 & F4 & ws4 & yt0 & yt1 & yt2 & yb1 & yb2 & yb3 & yb4 & yb5 & yb6 & yb7 & -> & MU4 & WM4 & MI4 & WS4 & LWS4 & BER4 & HD4 & TL4).
pose proof (agree_blocks_of_munch bsegs _ m3 m4 (tl (sb_blocks s S a) ++ LBL) MU4 WM4
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1; cbn [outside]; split; [lia| exact I])) as AG4.
apply (sb_bufs_agree s S a j m3 m4) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG4 HD3 TL WS3 BER BER4 OBP3 OBER APS APQ. unfold sbhd in HD4. unfold sbtl in TL4. rename TL4 into TL.
assert (PFA1 : P + 16 <= f \/ f + 64 <= P) by (pose proof (PFA P ltac:(lia)) as (E1 & _); pose proof (PFA (P + 15) ltac:(lia)) as (E2 & _); clear - E1 E2; lia).
assert (ART4 : X14x.ART RT Σ1 m4).
{ apply (af_frame RT AF Σ1 m3 m4 lo ART LOW); [| exact WM4]. intros a0 Ha. apply MU4. cbn [outside]. split; [| exact I]. intros Hin. apply Ha.
apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp (rt_live RT Σ1) (rt_frames RT Σ1) lo); [| intros e He; rewrite LV1; exact He| intros e He; rewrite FRS1; right; exact He| ulc].
apply PCL. exact Hin. }
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W m m3 =>
assert (PF4 : rt_pres_fp L Fr U W m m4)
by (apply (pres_fp_trans _ _ _ _ m m3 m4 PF); apply (pres_fp_of_munch _ _ _ _ _ m3 m4 MU4); intros x _ Ho; cbn [outside] in Ho |- *; destruct Ho as (Ho & _); split; [exact Ho| exact I])
end.
clear PF ART. rename PF4 into PF. rename ART4 into ART.
trm MU4 WM4 FR3 ltac:(clear - PAP LO96; unfold hid in *; lia).
trm MU4 WM4 FRB3 ltac:(clear - PFA1; lia).
trm MU4 WM4 FRS3 ltac:(clear - POFF SHF1 SHF2; unfold hid, SH_LO, SH_HI in *; lia).
assert (ST4 : stk bsegs m4 lo (usp + -96)) by (apply (stk_transport_disjoint bsegs _ m3 m4 lo (usp + -96) ST3 MU4 WM4); cbn [disjoint_from]; clear - PAP LO96; unfold hid in *; lia).
clear ST3 ST2 MU4 MI3.

assert (FRSE : rw_cells bsegs m4 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch bsegs _ m4 m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m4 m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ1 = (f, 0%nat) :: rt_frames RT Σ) by (exact FRS1).
assert (EL2 : rt_live RT Σ1 = rt_live RT Σ) by (exact LV1).
lazymatch goal with A : X14x.ART RT Σ1 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO1 (PNIL E)) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < P \/ P + 16 <= fl).
{ destruct (Z_lt_dec fl P) as [L|L]; [left; exact L|]. destruct (Z_le_dec (P + 16) fl) as [G|G]; [right; exact G|]. exfalso.
exact (NFL fl (PCL fl ltac:(clear - L G; lia)) eq_refl). }
assert (FR6 : rw_cells bsegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks bsegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch bsegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
rewrite <- NSF4 in HD4.
apply Hk. exists Σ3.
split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|];
split; [pose proof (dec_depth_pos low) as DP0; clear - EC CR1 DP0; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM0]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (dst_obj_sigma Σ Σ3 m7 P 16 (ACCK2 m7 PF) EF (eq_trans EP PO1)) as DST7.
cbn [speex_decoder_ctl fst snd creq_post dec_exc_ready creq_size].
split; [| split; [exists ws4; split; [exact WS4| exact LWS4]| split; [intros _; exact I| exact DST7]]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app bsegs m7 S _ _)); split; [exact HD4| exact TL]|].
split; [exact BUFS|]. exists OUTLL. exact RLOW. }
1: {
subst OUTL. destruct DF0 as (ACP & PP0 & PT & POFF & PAP & PIMG & P4).
cps_seg (sbarm2_dtx usp S P f sf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 MI3 SBF OBS3 S8 SOFF).
destruct POST as (ya3 & ya4 & ya5 & ->).
assert (DST1 : dst_obj RT Σ1 m3 P 4).
{ destruct (ACCK2 m3 PF) as [(fp & kp & INFP & IFO) | INP]; [left; exists fp, kp; split; [rewrite FRS1; right; exact INFP| exact IFO]| right; rewrite PO1; exact INP]. }
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes bsegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ1 PMc) with (OUTL := OUTLL) (OUT := OUTLL) (STEREO := STEREO) (S := a_low a) (LBD := LBL) (r := CtlGetDtxStatus) (P := P) (lo := lo); cps_auto | ].
{ rewrite EU. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
{ rewrite EU. exact ST3. }
intros cc5 (Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2 & PO2).
destruct (ASTA_unpack RT Σ2 PMc _ cc5 Hc5) as (ms5 & PO5 & Hc5'). clear Hc5. cbv beta in PO5.
destruct PO5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & REP5 & CP5 & EXC5 & DST5).
destruct RS5 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F5 & fc5 & -> & FRM5).
rewrite EU in *. cbn [creq_ivs creq_size app] in PRES5.

assert (INL0 : In (S, 160) (rt_live RT Σ)) by (rewrite <- LV1; exact INL).
assert (APS : P + 4 <= S \/ S + 160 <= P).
{ pose proof (proj2 (PDF P ltac:(lia)) S 160 INL0) as E1. pose proof (proj2 (PDF (P + 3) ltac:(lia)) S 160 INL0) as E2. clear - E1 E2. lia. }
assert (PFA1 : P + 4 <= f \/ f + 64 <= P) by (pose proof (PFA P ltac:(lia)) as (E1 & _); pose proof (PFA (P + 3) ltac:(lia)) as (E2 & _); clear - E1 E2; lia).
xfp PRES5 WM5 OUTB FR3. xfp PRES5 WM5 OUTB FRB3. xfp PRES5 WM5 OUTB FRS3. xfp PRES5 WM5 OUTB HD3. xfp PRES5 WM5 OUTB TL.
assert (AG5 : agree_blocks bsegs m3 m5 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ1 _ _ _ m3 m5 _ PRES5 WM5).
- intros b Hb. apply LIVE1. apply in_app_iff. left. cbn [sb_blocks tl] in Hb |- *. right. exact Hb.
- intros b x Hb Hx. split; [| exact (APL b x Hb Hx)].
pose proof (BOUT b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H1. clear - H1. cbn [fst snd]. lia. }
apply (sb_bufs_agree s S a j m3 m5) in BUFS; [| exact JOK | exact AG5]. clear AG5 RLOW.
assert (PF5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + 4) :: (S, S + 160) :: blocks_ivs (tl (sb_blocks s S a) ++ LBL)) m m5).
{ apply (pres_fp_trans _ _ _ _ m m3 m5 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -96) _ m3 m5 PRES5).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x Hx (O1 & O2 & O3). split; [exact O1| exact (outside_blocks_app_r (tl (sb_blocks s S a)) LBL x O3)]. }
clear PF PRES5. rename PF5 into PF.
cps_sigma LV2 FRS2 SP2.
destruct CP5 as (ARG5 & RV5).
destruct (af_acc_live RT AF Σ2 m5 S 160 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj bsegs m5 S 160) by (split; [lia|]; split; [ulc| exact ACS5]).
cps_seg (sbarm_pass_b usp S P f sf).
subst ms.
clear OBS5 ACS5. unfold sbhd in HD3.

assert (FRSE : rw_cells bsegs m5 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch bsegs _ m5 m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m5 m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by (rewrite LV2; exact LV1).
lazymatch goal with A : X14x.ART RT Σ2 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO2 (eq_trans PO1 (PNIL E))) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < P \/ P + 4 <= fl).
{ destruct (Z_lt_dec fl P) as [L|L]; [left; exact L|]. destruct (Z_le_dec (P + 4) fl) as [G|G]; [right; exact G|]. exfalso.
exact (NFL fl (PCL fl ltac:(clear - L G; lia)) eq_refl). }
assert (FR6 : rw_cells bsegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks bsegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch bsegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
rewrite LV2. apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3. split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [clear - EC CR2 CR1; cbn [dec_depth] in *; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (dst_obj_sigma Σ Σ3 m7 P 4 (ACCK2 m7 PF) EF (eq_trans EP (eq_trans PO2 PO1))) as DST7.
cbn [speex_decoder_ctl] in *. destruct (speex_decoder_ctl low CtlGetDtxStatus) as [v' low'] eqn:EC5. cbn [fst snd creq_post dec_exc_ready] in *.
split; [| split; [split; [exact ARG5| exact RV5]| split; [intros _; exact I| exact DST7]]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app bsegs m7 S _ _)); split; [exact HD3| exact TL]|].
split; [exact BUFS|]. exists OUTLL. exact REP5. }
1: {
cbn [creq_ok] in OK. destruct OK as (EP & OFF160).
cps_seg (sbarm2_isv usp S P f sf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 MI3 SBF OBS3 S8 SOFF s a OUTL OUT off j _ _ _ _ _ _ _ EP TL).
destruct POST as (m4 & xa1 & -> & TL4 & MU4 & WM4 & MI4).
pose proof (agree_blocks_of_munch bsegs _ m3 m4 (tl (sb_blocks s S a) ++ LBL) MU4 WM4
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1; cbn [outside]; split; [lia| exact I])) as AG4.
apply (sb_bufs_agree s S a j m3 m4) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG4 TL. unfold sbtl in TL4. rename TL4 into TL. unfold sbhd in HD3.
cps_seg_post.

assert (FRSE : rw_cells bsegs m4 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch bsegs _ m4 m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m4 m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ1 = (f, 0%nat) :: rt_frames RT Σ) by (exact FRS1).
assert (EL2 : rt_live RT Σ1 = rt_live RT Σ) by (exact LV1).
lazymatch goal with A : X14x.ART RT Σ1 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO1 (PNIL E)) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FR6 : rw_cells bsegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks bsegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch bsegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3.
split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|];
split; [pose proof (dec_depth_pos low) as DP0; clear - EC CR1 DP0; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM0]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [apply (pres_fp_weaken _ _ _ _ _ _ _ PF); intros x Hx; cbn [creq_ivs app] in Hx; split; [cbn [fst snd]; clear; lia| exact Hx]|].
cbn [speex_decoder_ctl fst snd creq_post dec_exc_ready].
split; [| split; [exact I| split; [intros _; exact I| exact I]]].
pose proof INV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12).
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|].
split; [unfold sb_inv; cbn [set_sbd_innov_save sbd_mode sbd_frame_size sbd_full_frame_size sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first
sbd_sampling_rate sbd_lpc_enh_enabled sbd_encode_submode sbd_submodeID sbd_innov_save];
refine (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj I7 (conj I8 (conj I9 (conj I10 (conj I11 _))))))))))); clear - OFF160; lia|].
split; [exact JOK|].
split; [rewrite sb_cells_split; cbn [set_sbd_innov_save sbd_mode sbd_full_frame_size sbd_frame_size sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first
sbd_sampling_rate sbd_lpc_enh_enabled]; rewrite <- EMP; apply (proj2 (rw_cells_app bsegs m7 S _ _)); split; [exact HD3| exact TL]|].
split; [exact BUFS|]. exists OUTLL. exact RLOW. }
Qed.

Theorem ctl2_cps_all : forall d, ctl2_cps_at RT d.
Proof using AF SM0 AF_LIB.
induction d as [st | s low IH]; [exact (ctl2_cps_nb st) | exact (ctl2_cps_sb s low IH)].
Qed.
End Ctl2.

End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Local Ltac trm MU WM H tacD :=
lazymatch type of MU with
| munch ?W ?m ?m' =>
lazymatch type of H with
| rw_cells asegs m ?A0 ?cs =>
let H' := fresh "T" in
assert (H' : rw_cells asegs m' A0 cs)
by (apply (rw_cells_transport asegs W m m' A0 cs H MU WM); cbn [disjoint_from]; simpl_sizes; tacD);
clear H; rename H' into H
end
end.

Section Ctl2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SM0 : stack_malloc_contract RT 0.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Theorem ctl2_cps_nb : forall st, ctl2_cps_at RT (DecNB st).
Proof using AF AF_LIB.
intros st Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUTL OUT STEREO S LBD r P lo FDO MST -> -> -> -> GRP REP EOUT DEP ND AL8 OK PRE LIVE DST FRMS CRD POA ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
cbn [ctl_stack] in LOR. unfold NBCTL_STACK in LOR.
pose proof REP as REP0. cbn [decst_rep] in REP0. destruct REP0 as [ELBD NB]. subst LBD.
pose proof (LIVE _ ltac:(left; reflexivity)) as INL. unfold blk_addr, blk_size in INL. cbn [fst snd] in INL. unfold NBSTATE_SIZEOF in INL.
destruct (live_below_lo RT AF Σ m S 2968 lo ART0 INL LOW) as (BD0 & BD1 & LOS).
destruct (af_acc_live RT AF Σ m S 2968 ART0 INL) as (_ & ACS).
pose proof (live_facts RT AF Σ m S 2968 ART0 INL) as (_ & _ & SIMG & SHI).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (AF_LIB Σ m ART0) as LC0.
assert (OBM : aobj asegs m A_speex_nb_mode 96)
by (apply (aobj_lit RT AF Σ m A_speex_nb_mode 96 ART0); [unfold ACC_LITS, A_speex_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_nb_mode; lia | unfold A_speex_nb_mode, APP_TOP; lia]).
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.

assert (DSTP : match r with CtlSetInnovationSave _ => True
| _ => aobj asegs m P (creq_size r) /\ P mod 4 = 0 /\ IMG_TOP <= P /\ (P + creq_size r <= SH_LO \/ SH_HI <= P) /\ (P + creq_size r <= lo \/ usp <= P)
/\ (forall b, In b [(nb_blk st, S, NBSTATE_SIZEOF)] -> P + creq_size r <= blk_addr b \/ blk_addr b + blk_size b <= P) end).
{ destruct r; try discriminate GRP; try exact I; cbn [creq_size] in *;
[ pose proof (dst_obj_facts RT AF Σ m P 16 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_facts RT AF Σ m P 16 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_facts RT AF Σ m P 4 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF ];
destruct DF as (ACP & PP0 & PT & POFF & PAP & PIMG & P4 & _ & _ & PLV);
(split; [split; [lia|]; split; [exact PT| exact ACP]|]; split; [exact P4|]; split; [exact PIMG|]; split; [exact POFF|]; split; [exact PAP|];
intros b [<-|[]]; unfold blk_addr, blk_size; cbn [fst snd]; unfold NBSTATE_SIZEOF; pose proof (PLV _ _ INL) as PLS; clear - PLS; lia). }
cps_norm.
refine (rz_evt RT AF Σ PMc _ _ T c MST Hc (rctl2_nb st OUTL OUT STEREO S _ r P lo usp ra gp (Z_to_bv 64 6489176) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m GRP REP EOUT OK PRE _ DSTP OBM ST0 LOS _ _ CC0 LC0 MI0 FRM0) _).
- intros b [<-|[]]. unfold ablk, blk_addr, blk_size. cbn [fst snd]. unfold NBSTATE_SIZEOF.
split; [split; [lia|]; split; [ulc| exact ACS]|]. split; [exact (proj1 NB)|]. split; [unfold SH_LO, SH_HI; lia|]. split; [unfold IMG_TOP; ulc| exact BD1].
- unfold NBCTL_STACK. ulc.
- ulc.
- intros ms' c' POST Hc'. clear Hc.
destruct POST as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F' & fc' & m' & -> & MU & WM & MI' & FRM' & ST' & REP' & CP' & EXC').

assert (PF : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (creq_ivs P r ++ blocks_ivs [(nb_blk st, S, NBSTATE_SIZEOF)]) m m').
{ apply (pres_fp_of_munch _ _ _ _ _ m m' MU). intros x Hx Ho. unfold ctlW. apply outside_cons. split; [| exact Ho].
cbn [fst snd]. pose proof (SPL x Hx) as SX. clear - SX LOW. lia. }
assert (ACLP : match r with CtlSetInnovationSave _ => True | _ => forall i, 0 <= i < creq_size r -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp (P + i) end).
{ destruct r; try discriminate GRP; try exact I; cbn [creq_size] in *;
[ pose proof (dst_obj_facts RT AF Σ m P 16 lo usp ART0 LOW ltac:(ulc) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_facts RT AF Σ m P 16 lo usp ART0 LOW ltac:(ulc) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_facts RT AF Σ m P 4 lo usp ART0 LOW ltac:(ulc) SPT POA ltac:(lia) DST) as DF ];
exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 DF)))))))). }
assert (ART' : X0ec.ART RT Σ m').
{ apply (af_frame RT AF Σ m m' lo ART0 LOW); [| exact WM]. intros a0 Ha. apply MU.
unfold ctlW. apply outside_cons. cbn [fst snd]. split; [intros Hin; apply Ha; left; clear - Hin SPT; unfold USTACK_TOP in *; lia|].
assert (HB : outside (blocks_ivs [(nb_blk st, S, NBSTATE_SIZEOF)]) (bv_unsigned a0)).
{ cbn [blocks_ivs map outside blk_addr blk_size fst snd]. unfold NBSTATE_SIZEOF. split; [| exact I].
intros Hin; apply Ha; right; right; left; exists S, 2968; split; [exact INL| exact Hin]. }
destruct r; try discriminate GRP; cbn [creq_ivs creq_size app] in *; try exact HB; apply outside_cons; cbn [fst snd]; (split; [| exact HB]);
intros Hin; apply Ha;
(apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp (rt_live RT Σ) (rt_frames RT Σ) lo); [| intros e He; exact He| intros e He; exact He| ulc]);
replace (bv_unsigned a0) with (P + (bv_unsigned a0 - P)) by ring; apply ACLP; clear - Hin; lia. }
assert (DST' : match r with CtlSetInnovationSave _ => True | _ => dst_obj RT Σ m' P (creq_size r) end).
{ assert (OFW : offsh (ctlW lo usp P r [(nb_blk st, S, NBSTATE_SIZEOF)])).
{ unfold ctlW. destruct r; try discriminate GRP; cbn [creq_ivs creq_size app blocks_ivs map blk_addr blk_size fst snd offsh]; unfold NBSTATE_SIZEOF;
cbn [creq_size] in *; try exact I;
[ pose proof (dst_obj_facts RT AF Σ m P 16 lo usp ART0 LOW ltac:(ulc) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_facts RT AF Σ m P 16 lo usp ART0 LOW ltac:(ulc) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_facts RT AF Σ m P 4 lo usp ART0 LOW ltac:(ulc) SPT POA ltac:(lia) DST) as DF | ];
try destruct DF as (_ & _ & _ & POFF & _);
repeat split; first [clear - LOS SHI POFF SPT | clear - LOS SHI SPT]; unfold SH_LO, SH_HI in *; lia. }
destruct r; try discriminate GRP; try exact I; cbn [creq_size] in *;
(destruct DST as [(f & k & INF & (O1 & O2 & O3 & O4)) | INP]; [left; exists f, k; split; [exact INF|]; split; [exact O1|]; split; [exact O2|]; split; [| exact O4] | right; exact INP]);
(pose proof (frame_facts RT AF Σ m f k ART0 INF) as (FF0 & _);
destruct (frame_below_lo RT AF Σ m f k lo ART0 INF LOW) as (FB & _ & _);
refine (proj2 (proj2 (aobj_munch asegs _ m m' P _ (conj _ (conj _ O3)) MU _))); [clear - FF0 O1; lia| clear - O2 FB LOR SPT; unfold APP_TOP, USTACK_TOP, RT_STACK in *; lia|];
apply shfree_of_offsh; [exact OFW| clear - FF0 O1; lia| clear - O2 FB LOR SPT; unfold APP_TOP, USTACK_TOP, RT_STACK in *; lia]). }
apply Hk. exists Σ. split; [| cbn [dec_depth]; repeat split; lia].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM']|].
split. { split; [exact ART'|]. split; [exact MI'|]. split; [exact WM| exact ST']. }
split; [exact PF|]. split; [exact REP'|]. split; [exact CP'|]. split; [exact EXC'| exact DST'].
Qed.

Section SBARMS2.
Variables (usp S P f sf : Z) (gp tp t0 t1 t2 a6 a7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Let R (c : Z) (xra xa0 xa1 xa2 xa3 xa4 xa5 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96)) xa0 xa1 xa2 xa3 xa4 xa5 a6 a7
(Z_to_bv 64 f) (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 c) (Z_to_bv 64 f) (Z_to_bv 64 sf) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6.
Hypothesis MI : mem_inv asegs m.
Hypothesis SB : 0 < S /\ S + 160 < 2^63.
Hypothesis PB : 0 <= P /\ P + 24 < 2^63.
Hypothesis OBS : aobj asegs m S 160.
Hypothesis S8 : S mod 8 = 0.
Hypothesis SOFF : S + 160 <= SH_LO \/ SH_HI <= S.

Lemma sbarm2_pig : forall (s : sbd_state bptr) (a : sb_addrs) (OUT : Z) (j : sb_junk) (mp al : Z) (ffs fs sfs lpc fst sr enh : word) (qs ws : list word)
(ra a0 a1 a2 a3 a4 a5 : word),
rw_cells asegs m S (sbhd mp al ffs fs sfs (Z_to_bv 64 4) lpc fst sr enh) -> rw_cells asegs m (S + 48) (sbtl s a OUT j) ->
aobj asegs m (a_pg a) 16 -> a_pg a mod 8 = 0 -> rw_cells asegs m (a_pg a) (f32 qs) -> length qs = 4%nat ->
aobj asegs m P 16 -> P mod 4 = 0 -> rw_cells asegs m P (f32 ws) -> length ws = 4%nat ->
(P + 16 <= S \/ S + 160 <= P) -> (P + 16 <= a_pg a \/ a_pg a + 16 <= P) -> (P + 16 <= SH_LO \/ SH_HI <= P) ->
evt asegs (fun ms' => exists (m' : mem) (F' : bvmap 5 word) (ws' : list word) (xs3 xa1 xa2 xa3 xa4 xa5 : word),
ms' = MS (mkR ra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96)) (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5 a6 a7
(Z_to_bv 64 f) xs3 (Z_to_bv 64 S) (Z_to_bv 64 100) (Z_to_bv 64 f) (Z_to_bv 64 sf) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom asegs)
/\ munch [(P, P + 16)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' P (f32 ws') /\ length ws' = 4%nat /\ rw_cells asegs m' (a_pg a) (f32 qs)
/\ rw_cells asegs m' S (sbhd mp al ffs fs sfs (Z_to_bv 64 4) lpc fst sr enh) /\ rw_cells asegs m' (S + 48) (sbtl s a OUT j))
(MS (R 100 ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc 100)) fc None m (seg_rom asegs)).
Proof using All.
intros s a OUT j mp al ffs fs sfs lpc fst sr enh qs ws ra a0 a1 a2 a3 a4 a5 HD TL OBQ Q8 QS LQS OBP P4 WS LWS APS APQ POFF.
unfold sbhd, sbtl in *. unfold R, A_sbctl_epi, sbctl_armpc. cbn [Z.eqb Pos.eqb].
pose proof OBS as (OS0 & OS1 & _). pose proof OBP as (OP0 & OP1 & _). pose proof OBQ as (OQ0 & OQ1 & _). unfold APP_TOP in *.
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof POFF as POFF'. unfold SH_LO, SH_HI in POFF'.
pose proof (munch_refl [(P, P + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(P, P + 16)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (Q4 : a_pg a mod 4 = 0) by (clear - Q8; Z.div_mod_to_equations; lia).
destruct qs as [|q0 [|q1 [|q2 [|q3 []]]]]; cbn [length] in LQS; try lia.
destruct ws as [|w0 [|w1 [|w2 [|w3 []]]]]; cbn [length] in LWS; try lia.
rewrite !f32_cons, f32_nil in QS, WS.
ato 0xb5d38.
replace (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 4)) mod 4294967296)) with (Z_to_bv 64 4) by (rewrite sx32_lit by lia; reflexivity).
ato 0xb5d4c. astep. chk_merge OBP 4.
ato 0xb5d4c. astep. chk_merge OBP 4.
ato 0xb5d4c. astep. chk_merge OBP 4.
ato 0xb5d4c. astep. chk_merge OBP 4.
ato 0xb6374.
apply evt_done. do 2 eexists. exists [Sem.nan_box (Sem.low32 q0); Sem.nan_box (Sem.low32 q1); Sem.nan_box (Sem.low32 q2); Sem.nan_box (Sem.low32 q3)].
do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [rewrite !f32_cons, f32_nil; exact WS|]. split; [reflexivity|]. split; [rewrite !f32_cons, f32_nil; exact QS|].
split; [exact HD| exact TL].
Qed.

Lemma sbarm2_exc : forall (s : sbd_state bptr) (a : sb_addrs) (OUT : Z) (j : sb_junk) (mp al : Z) (ffs fs sfs lpc fst sr enh : word) (qs ws : list word)
(ra a0 a1 a2 a3 a4 a5 : word),
rw_cells asegs m S (sbhd mp al ffs fs sfs (Z_to_bv 64 4) lpc fst sr enh) -> rw_cells asegs m (S + 48) (sbtl s a OUT j) ->
aobj asegs m (a_er a) 16 -> a_er a mod 8 = 0 -> rw_cells asegs m (a_er a) (f32 qs) -> length qs = 4%nat ->
aobj asegs m P 16 -> P mod 4 = 0 -> rw_cells asegs m P (f32 ws) -> length ws = 4%nat ->
(P + 16 <= S \/ S + 160 <= P) -> (P + 16 <= a_er a \/ a_er a + 16 <= P) -> (P + 16 <= SH_LO \/ SH_HI <= P) ->
evt asegs (fun ms' => exists (m' : mem) (F' : bvmap 5 word) (ws' : list word) (xs3 xa1 xa2 xa3 xa4 xa5 : word),
ms' = MS (mkR ra (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96)) (Z_to_bv 64 0) xa1 xa2 xa3 xa4 xa5 a6 a7
(Z_to_bv 64 f) xs3 (Z_to_bv 64 S) (Z_to_bv 64 101) (Z_to_bv 64 f) (Z_to_bv 64 sf) (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom asegs)
/\ munch [(P, P + 16)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ rw_cells asegs m' P (f32 ws') /\ length ws' = 4%nat /\ rw_cells asegs m' (a_er a) (f32 qs)
/\ rw_cells asegs m' S (sbhd mp al ffs fs sfs (Z_to_bv 64 4) lpc fst sr enh) /\ rw_cells asegs m' (S + 48) (sbtl s a OUT j))
(MS (R 101 ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc 101)) fc None m (seg_rom asegs)).
Proof using All.
intros s a OUT j mp al ffs fs sfs lpc fst sr enh qs ws ra a0 a1 a2 a3 a4 a5 HD TL OBQ Q8 QS LQS OBP P4 WS LWS APS APQ POFF.
unfold sbhd, sbtl in *. unfold R, A_sbctl_epi, sbctl_armpc. cbn [Z.eqb Pos.eqb].
pose proof OBS as (OS0 & OS1 & _). pose proof OBP as (OP0 & OP1 & _). pose proof OBQ as (OQ0 & OQ1 & _). unfold APP_TOP in *.
pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'. pose proof POFF as POFF'. unfold SH_LO, SH_HI in POFF'.
pose proof (munch_refl [(P, P + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(P, P + 16)]) by (cbn; unfold SH_LO, SH_HI; lia).
assert (Q4 : a_er a mod 4 = 0) by (clear - Q8; Z.div_mod_to_equations; lia).
destruct qs as [|q0 [|q1 [|q2 [|q3 []]]]]; cbn [length] in LQS; try lia.
destruct ws as [|w0 [|w1 [|w2 [|w3 []]]]]; cbn [length] in LWS; try lia.
rewrite !f32_cons, f32_nil in QS, WS.
ato 0xb6458.
replace (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 4)) mod 4294967296)) with (Z_to_bv 64 4) by (rewrite sx32_lit by lia; reflexivity).
ato 0xb646c. astep. chk_merge OBP 4.
ato 0xb646c. astep. chk_merge OBP 4.
ato 0xb646c. astep. chk_merge OBP 4.
ato 0xb646c. astep. chk_merge OBP 4.
ato 0xb6374.
apply evt_done. do 2 eexists. exists [Sem.nan_box (Sem.low32 q0); Sem.nan_box (Sem.low32 q1); Sem.nan_box (Sem.low32 q2); Sem.nan_box (Sem.low32 q3)].
do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|].
split; [rewrite !f32_cons, f32_nil; exact WS|]. split; [reflexivity|]. split; [rewrite !f32_cons, f32_nil; exact QS|].
split; [exact HD| exact TL].
Qed.

Lemma sbarm2_isv : forall (s : sbd_state bptr) (a : sb_addrs) (OUTL OUT' off : Z) (j : sb_junk) (ra a0 a1 a2 a3 a4 a5 : word),
P = OUT' + 4 * off ->
rw_cells asegs m (S + 48) (sbtl s a OUTL j) ->
evt asegs (fun ms' => exists (m' : mem) (xa1 : word), ms' = MS (R 104 ra (Z_to_bv 64 0) xa1 a2 a3 a4 a5) F (Z_to_bv 64 A_sbctl_epi) fc None m' (seg_rom asegs)
/\ rw_cells asegs m' (S + 48) (sbtl (set_sbd_innov_save s (Some off)) a OUT' j)
/\ munch [(S + 120, S + 128)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
(MS (R 104 ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc 104)) fc None m (seg_rom asegs)).
Proof using MI SB OBS S8 SOFF.
clear PB. intros s a OUTL OUT' off j ra a0 a1 a2 a3 a4 a5 EP TL.
unfold sbtl in *. unfold R, A_sbctl_epi, sbctl_armpc. cbn [Z.eqb Pos.eqb].
pose proof OBS as (OS0 & OS1 & _). unfold APP_TOP in *. pose proof SOFF as SOFF'. unfold SH_LO, SH_HI in SOFF'.
pose proof (munch_refl [(S + 120, S + 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(S + 120, S + 128)]) by (cbn; unfold SH_LO, SH_HI; lia).
ato 0xb6374.
apply evt_done. do 2 eexists. split; [reflexivity|].
split; [| split; [exact MU|]; split; [exact WM| assumption]].
cbn [sb_isave_ptr set_sbd_innov_save sbd_innov_save sbd_encode_submode sbd_mode sbd_submodeID]. rewrite <- EP. exact TL.
Qed.

Lemma sbarm2_dtx : forall (mp al : Z) (ffs fs sfs nsf lpc fst sr enh : word) (ra a0 a1 a2 a3 a4 a5 : word),
rw_cells asegs m S (sbhd mp al ffs fs sfs nsf lpc fst sr enh) ->
evt asegs (fun ms' => exists xa3 xa4 xa5 : word,
ms' = MS (R 103 (Z_to_bv 64 0xb6370) (Z_to_bv 64 al) (Z_to_bv 64 103) (Z_to_bv 64 P) xa3 xa4 xa5) F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom asegs))
(MS (R 103 ra a0 a1 a2 a3 a4 a5) F (Z_to_bv 64 (sbctl_armpc 103)) fc None m (seg_rom asegs)).
Proof using MI SB OBS S8 SOFF.
clear PB. intros mp al ffs fs sfs nsf lpc fst sr enh ra a0 a1 a2 a3 a4 a5 HD. unfold sbhd in HD. unfold R, A_speex_decoder_ctl, sbctl_armpc. cbn [Z.eqb Pos.eqb].
ato 0x98638.
apply evt_done. do 3 eexists. reflexivity.
Qed.
End SBARMS2.

Lemma sbctl_w1_anyP : forall (usp lo S MP P c : Z) (hrest : list cell) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : word)
(ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
rw_cells asegs m S (C8 (Z_to_bv 64 MP) :: hrest) -> Z.of_nat (cells_size hrest) = 40 ->
aobj asegs m S 160 -> S mod 8 = 0 -> 0 < S -> S + 160 < 2^63 -> (S + 160 <= lo \/ usp <= S) ->
ro_cells asegs m MP (sb_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11) -> aobj asegs m MP 96 -> MP mod 8 = 0 -> 0x10000 <= MP -> MP + 104 <= 0x652000 ->
0 <= c < 2^31 ->
stk asegs m lo usp -> lo <= usp - 96 -> SH_HI <= lo -> usp < 2^63 -> usp mod 32 = 0 ->
client_consts m -> mem_inv asegs m ->
evt asegs (fun ms => exists (m1 : mem) (j8 : list byte) (xt1 xa3 xa4 xa5 : word),
ms = MS (mkR (Z_to_bv 64 RA_sbctl_smalloc) (Z_to_bv 64 (usp + -96)) gp tp t0 xt1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -96))
(Z_to_bv 64 64) (Z_to_bv 64 g_shadow_memory_dynamic_address) (Z_to_bv 64 1) xa3 xa4 xa5 a6 a7
s2 (Z_to_bv 64 P) (Z_to_bv 64 S) (Z_to_bv 64 c) s6 s7 (Z_to_bv 64 SHB) s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 e_stack_malloc_0) fc None m1 (seg_rom asegs)
/\ munch [(usp + -96, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -96)
/\ rw_cells asegs m1 (usp + -96) (sbctl_frame (CB 8 j8) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra))
(MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 S) (Z_to_bv 64 c) (Z_to_bv 64 P) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 A_speex_decoder_ctl) fc None m (seg_rom asegs)).
Proof.
intros until m. intros P0 HR OBS S8 S0 SHI AP ND OBM AL8 MPLO MPHI CR ST LO LOS SPH SP32 (G1 & G2 & G3 & G4) MI.
unfold A_speex_decoder_ctl, RA_sbctl_smalloc, e_stack_malloc_0, sbctl_frame, sb_desc_cells, A_sb_decoder_ctl,
g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
pose proof LOS as LOS'. unfold SH_LO, SH_HI in LOS'.
pose proof (munch_refl [(usp + -96, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
assert (OF : offsh [(usp + -96, usp)]) by (cbn; unfold SH_LO, SH_HI; lia).
carve_frame 96%nat ST.
apply (rw_cells_split_CB asegs _ _ [] 96 _ [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
ato 0xb5ab8.
ato 0xb5aec. astep. rewrite land_m32_al by lia.
ato 0xb5b10. rewrite sx32_small by (unfold int31; lia).
ato 0x51228.
apply evt_done. do 6 eexists. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact FR].
Qed.

Lemma creq2_pre_agree_sb : forall STEREO (m m' : mem) S S' s low s' low' P r, creq_grp1 r = false ->
creq_pre STEREO m S (DecSB s low) P r -> agree_at asegs m m' P (creq_size r) -> creq_pre STEREO m' S' (DecSB s' low') P r.
Proof.
intros STEREO m m' S S' s low s' low' P r G PRE AG. destruct r; try discriminate G; cbn [creq_pre creq_size dec_exc_ready] in *.
- destruct PRE as (ws & X & L). exists ws. split; [| exact L]. exact (rw_cells_agree_at asegs m m' P _ X ltac:(rewrite cells_size_f32, L; exact AG)).
- destruct PRE as ((ws & X & L) & _). split; [| exact I]. exists ws. split; [| exact L]. exact (rw_cells_agree_at asegs m m' P _ X ltac:(rewrite cells_size_f32, L; exact AG)).
- destruct PRE as (w & X). exists w. exact (rw_cells_agree_at asegs m m' P _ X AG).
- exact I.
Qed.

Lemma dst_obj_sigma : forall (Σ Σ' : rts RT) (m : mem) o n, dst_obj RT Σ m o n -> rt_frames RT Σ' = rt_frames RT Σ -> rt_pois RT Σ' = rt_pois RT Σ -> dst_obj RT Σ' m o n.
Proof.
intros Σ Σ' m o n [(f & k & INF & IFO) | INP] EF EP; [left; exists f, k; split; [rewrite EF; exact INF| exact IFO]| right; rewrite EP; exact INP].
Qed.

Theorem ctl2_cps_sb : forall s low, ctl2_cps_at RT low -> ctl2_cps_at RT (DecSB s low).
Proof using AF SM0 AF_LIB.
intros s low IH Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUTL OUT STEREO S LBD r P lo FDO MST -> -> -> -> GRP REP EOUT DEP ND AL8 OK PRE LIVE DST FRMS CRD POA ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
intros T c Hc Hk.
set (usp := bv_unsigned sp) in *.
assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
unfold entry_st in Hc. rewrite ESP in Hc.
cbn [ctl_stack dec_depth] in LOR, DEP, FRMS, CRD.
assert (CSP : 0 <= ctl_stack low) by (clear; induction low; cbn [ctl_stack]; unfold NBCTL_STACK; lia).
pose proof REP as REP0. cbn [decst_rep] in REP0. destruct REP0 as (a & j & LBL & ELBD & S8 & SPOS & INV & JOK & X & BUFS & OUTLL & RLOW).
pose proof INV as (IMODE & _).
rewrite sb_cells_split in X.

assert (INL : In (S, 160) (rt_live RT Σ)).
{ specialize (LIVE (sbd_blk s, S, SBSTATE_SIZEOF)). rewrite ELBD in LIVE. specialize (LIVE ltac:(left; reflexivity)). exact LIVE. }
destruct (live_below_lo RT AF Σ m S 160 lo ART0 INL LOW) as (_ & BS1 & LOS).
destruct (af_acc_live RT AF Σ m S 160 ART0 INL) as (_ & ACS).
pose proof (live_facts RT AF Σ m S 160 ART0 INL) as (_ & _ & _ & SHI).
assert (SZ : 0 <= creq_size r <= 16) by (destruct r; try discriminate GRP; cbn; lia).

assert (PDF : forall x, P <= x < P + creq_size r -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x /\ (forall p k, In (p, k) (rt_live RT Σ) -> ~ (p <= x < p + k))).
{ destruct r; try discriminate GRP; cbn [creq_size] in *; try (intros x Hx; exfalso; lia);
[ pose proof (dst_obj_facts RT AF Σ m P 16 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_facts RT AF Σ m P 16 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_facts RT AF Σ m P 4 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF ];
destruct DF as (_ & _ & _ & _ & _ & _ & _ & ACL & _ & PLV);
(intros x Hx; split; [replace x with (P + (x - P)) by ring; apply ACL; lia| intros p k Hp Hin; pose proof (PLV p k Hp) as H; lia]). }

assert (DF0 : match r with CtlSetInnovationSave _ => True
| _ => acc asegs m P (creq_size r) /\ 0 < P /\ P + creq_size r <= APP_TOP /\ (P + creq_size r <= SH_LO \/ SH_HI <= P)
/\ (P + creq_size r <= lo \/ usp <= P) /\ IMG_TOP <= P /\ P mod 4 = 0 end).
{ destruct r; try discriminate GRP; try exact I; cbn [creq_size] in *;
[ pose proof (dst_obj_facts RT AF Σ m P 16 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_facts RT AF Σ m P 16 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF
| pose proof (dst_obj_facts RT AF Σ m P 4 lo usp ART0 LOW ltac:(unfold RT_STACK in LOR; lia) SPT POA ltac:(lia) DST) as DF ];
destruct DF as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & _); exact (conj D1 (conj D2 (conj D3 (conj D4 (conj D5 (conj D6 D7)))))). }
assert (ACCK2 : forall m', rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + creq_size r) :: blocks_ivs LBD) m m' ->
match r with CtlSetInnovationSave _ => True | _ => dst_obj RT Σ m' P (creq_size r) end).
{ intros m' PR. destruct r; try discriminate GRP; try exact I; cbn [creq_size] in *;
(destruct DST as [(fp & kp & INFP & (O1 & O2 & O3 & O4)) | INP]; [left; exists fp, kp; split; [exact INFP|]; split; [exact O1|]; split; [exact O2|]; split; [| exact O4] | right; exact INP]);
(apply (acc_of_pres_fp RT AF Σ m m m' usp _ fp kp P _ ART0 INFP O1 O2 PR); [| exact O3]);
(intros x Hx; split; [cbn [fst snd]; pose proof (frame_facts RT AF Σ m fp kp ART0 INFP) as (_ & _ & _ & _ & FH & _); pose proof (fs_size_ge64 kp) as FSZ;
clear - Hx FH O1 O2 FSZ; unfold SH_LO, SH_HI in *; lia
| exact (outside_blocks_shadow RT AF Σ m LBD x ART0 LIVE Hx)]). }

pose proof (AF_LIB Σ m ART0) as LC0.
set (MP := sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) in *.
assert (MPF : exists c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11, ro_cells asegs m MP (sb_desc_cells c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11)
/\ aobj asegs m MP 96 /\ MP mod 8 = 0 /\ 0x10000 <= MP /\ MP + 104 <= 0x652000).
{ subst MP. destruct IMODE as [E|E]; rewrite E; cbn [sb_mode_ptr].
- do 12 eexists. split; [exact (lib_const m A_speex_wb_mode LC_speex_wb_mode LC0 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ m A_speex_wb_mode 96 ART0); [unfold ACC_LITS, A_speex_wb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_wb_mode; lia | unfold A_speex_wb_mode, APP_TOP; lia]|].
unfold A_speex_wb_mode. repeat split; lia.
- do 12 eexists. split; [exact (lib_const m A_speex_uwb_mode LC_speex_uwb_mode LC0 ltac:(lc_in))|].
split; [apply (aobj_lit RT AF Σ m A_speex_uwb_mode 96 ART0); [unfold ACC_LITS, A_speex_uwb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_uwb_mode; lia | unfold A_speex_uwb_mode, APP_TOP; lia]|].
unfold A_speex_uwb_mode. repeat split; lia. }
destruct MPF as (c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & c8 & c9 & c10 & c11 & ND0 & OBM & MP8 & MPLO & MPHI).
pose proof (eq_refl : MP = sb_mode_ptr A_speex_nb_mode A_speex_wb_mode A_speex_uwb_mode (sbd_mode s)) as EMP. clearbody MP.
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
assert (OBS : aobj asegs m S 160) by (split; [lia|]; split; [unfold APP_TOP, STACK_WIN, USTACK_TOP, RT_STACK in *; lia| exact ACS]).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp (blocks_ivs LBD) m) as PF.
pose proof (fun E : rt_frames RT Σ = [] => af_pois_nil RT AF Σ m ART0 E) as PNIL.
assert (LIVE0 : blocks_in_live RT Σ LBD) by exact LIVE.
assert (POUT : forall x, P <= x < P + creq_size r -> outside (blocks_ivs LBD) x).
{ intros x Hx. apply outside_blocks_ivs. intros b Hb Hin. exact (proj2 (PDF x Hx) _ _ (LIVE b Hb) Hin). }
assert (PCL : forall x, P <= x < P + creq_size r -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x) by (intros x Hx; exact (proj1 (PDF x Hx))).
pose proof (fun m' S' low' (PR : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp (blocks_ivs LBD) m m') (WM : wmono asegs m m')
(PB0 : 0 <= P) (PB1 : P + creq_size r <= 2^64) =>
creq2_pre_agree_sb STEREO m m' S S' s low s low' P r GRP PRE
(agree_at_of_pres_fp _ _ usp _ m m' P (creq_size r) PR WM PB0 PB1 (fun x Hx => conj (PCL x Hx) (POUT x Hx)))) as PREK.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
assert (CODE : sbctl_code_ok (ctl_req_code r)) by (unfold sbctl_code_ok; destruct r; cbn [ctl_req_code]; tauto).
assert (CRNG : 0 <= ctl_req_code r < 2^31) by (destruct r; cbn; lia).
assert (LO96 : lo <= usp + -96) by (clear - LOR CSP; unfold RT_STACK in LOR; lia).
cps_norm. cps_hide.

piece X HD. rename X into TL. unfold sbhd in HD. unfold sbtl in TL.
cps_seg (sbctl_w1_anyP usp lo S MP P (ctl_req_code r)).
{ reflexivity. } { ulc. }
destruct POST as (m1 & j8 & xt1 & xa3 & xa4 & xa5 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
assert (BOUT : forall b x, In b (tl (sb_blocks s S a) ++ LBL) -> blk_addr b <= x < blk_addr b + blk_size b ->
x < lo /\ (x < S \/ S + 160 <= x) /\ ~ (P <= x < P + creq_size r)).
{ intros b x Hb Hx.
assert (Hb' : In b LBD) by (rewrite ELBD; cbn [sb_blocks tl app] in Hb |- *; right; exact Hb).
pose proof (LIVE b Hb') as LB.
destruct (live_below_lo RT AF Σ m _ _ lo ART0 LB LOW) as (_ & B1 & _).
assert (NE : blk_addr b <> S).
{ rewrite ELBD in ND. cbn [sb_blocks app map blk_id blk_addr fst snd] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _].
intros E. apply NI. rewrite <- E. cbn [sb_blocks tl app] in Hb. exact (in_map blk_id _ _ Hb). }
pose proof (live_apart RT AF Σ m _ _ _ _ ART0 LB INL NE) as B3.
split; [clear - B1 Hx; lia|]. split; [clear - B3 Hx; unfold hid in *; lia|].
intros HP. exact (proj2 (PDF x HP) _ _ LB Hx). }
pose proof (agree_blocks_of_munch asegs _ m m1 (tl (sb_blocks s S a) ++ LBL) MU1 WM1
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1 LO96; cbn [outside]; split; [lia| exact I])) as AG1.
Time cps_seg_post.
apply (sb_bufs_agree s S a j m m1) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG1| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG1| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG1.

cps_rt_sized SM0 0. { cbn; tauto. } { pose proof (dec_depth_pos low) as DP; clear - CRD DP; lia. } { cps_callok. }
intros cc2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR1 & FPOS & F64 & FTOP & PO1).
Time cps_unpack Hc2 as (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WRF & WRS).
assert (LIVE1 : blocks_in_live RT Σ1 LBD) by (intros b Hb; rewrite LV1; exact (LIVE b Hb)).
pose proof (agree_blocks_of_pres RT Σ (rt_frames RT Σ) (usp + -96) m1 m2 (tl (sb_blocks s S a) ++ LBL) PRES2 WM2
ltac:(intros b Hb; apply LIVE; rewrite ELBD; cbn [sb_blocks tl app] in Hb |- *; right; exact Hb)) as AG2.
apply (sb_bufs_agree s S a j m1 m2) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG2| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG2| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG2.
Time cps_new_frame ART2 FRS1 LV1 SP1 WRF WRS sf. cps_hide.
assert (BOUT2 : forall b x, In b (tl (sb_blocks s S a) ++ LBL) -> blk_addr b <= x < blk_addr b + blk_size b ->
(x < f \/ f + 64 <= x) /\ (x < sf \/ sf + 8 <= x)).
{ intros b x Hb Hx.
assert (Hb' : In b LBD) by (rewrite ELBD; cbn [sb_blocks tl app] in Hb |- *; right; exact Hb).
destruct (frame_live_apart RT AF Σ1 m2 f 0%nat _ _ ART2 INF (LIVE1 b Hb')) as (B2 & B3).
change (fs_size 0) with 64 in B2, B3. rewrite SHF0, <- SHF in B3. clear - B2 B3 Hx. lia. }

cps_seg (sbctl_w2 usp lo S P (ctl_req_code r) f sf).
destruct POST as (m3 & a0' & a1' & a2' & j24 & l32 & j36 & j40 & l48 & j52 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & FRB3 & FRS3).
Time pose proof (agree_blocks_of_munch asegs _ m2 m3 (tl (sb_blocks s S a) ++ LBL) MU3 WM3
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; pose proof (BOUT2 b x Hb Hx) as H2; clear - H1 H2 LO96; cbn [outside]; repeat split; lia)) as AG3.
apply (sb_bufs_agree s S a j m2 m3) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG3| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG3| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG3 FR1 FRB FRS.
unfold sbctl_frame in FR3. unfold sbctl_fhdr in FRB3. unfold sbctl_shadow, bF1, bF3, bF8 in FRS3.
Time cps_seg_post.
destruct (af_acc_live RT AF Σ1 m3 S 160 ART INL) as (_ & ACS3).
assert (OBS3 : aobj asegs m3 S 160) by (split; [lia|]; split; [ulc| exact ACS3]).
assert (SOFF : S + 160 <= SH_LO \/ SH_HI <= S) by (clear - SHI; unfold hid, SH_LO, SH_HI in *; lia).
assert (HD3 : rw_cells asegs m3 S (sbhd MP (a_low a) (Z_to_bv 64 (sbd_full_frame_size s)) (Z_to_bv 64 (sbd_frame_size s)) (Z_to_bv 64 (sbd_subframeSize s))
(Z_to_bv 64 (sbd_nbSubframes s)) (Z_to_bv 64 (sbd_lpcSize s)) (Z_to_bv 64 (sbd_first s))
(Z_to_bv 64 (sbd_sampling_rate s)) (Z_to_bv 64 (sbd_lpc_enh_enabled s)))) by exact HD.
assert (SBF : 0 < S /\ S + 160 < 2^63) by (split; ulc).
clear HD. cps_hide.
assert (WM03 : wmono asegs m m3) by cps_wmono.
assert (PRE3 : match r with CtlSetInnovationSave _ => True | _ => creq_pre STEREO m3 S (DecSB s low) P r end).
{ destruct r; try discriminate GRP; try exact I; destruct DF0 as (_ & PP0 & PT & _);
exact (PREK m3 S low PF WM03 ltac:(clear - PP0; lia) ltac:(clear - PT; cbn [creq_size] in *; unfold APP_TOP in *; lia)). }
clear PREK PRE.
apply (pres_fp_weaken _ _ _ _ ((P, P + creq_size r) :: blocks_ivs LBD)) in PF; [| intros x Hx; exact (proj2 Hx)].
assert (OUTB : forall x, (lo <= x \/ (S <= x < S + 160) \/ (P <= x < P + creq_size r) \/ (f <= x < f + 64) \/ (sf <= x < sf + 8)) -> outside (blocks_ivs LBL) x).
{ intros x Hx. apply outside_blocks_ivs. intros b Hb Hin.
pose proof (BOUT b x ltac:(apply in_app_iff; right; exact Hb) Hin) as H1. pose proof (BOUT2 b x ltac:(apply in_app_iff; right; exact Hb) Hin) as H2.
clear - Hx H1 H2. lia. }
assert (APL : forall b x, In b (tl (sb_blocks s S a)) -> blk_addr b <= x < blk_addr b + blk_size b -> outside (blocks_ivs LBL) x).
{ intros b x Hb Hx. apply outside_blocks_ivs. intros b2 Hb2 Hin.
assert (NE : blk_addr b <> blk_addr b2).
{ rewrite ELBD, map_app in ND. apply (NoDup_app_in_neq _ _ (blk_id b) (blk_id b2) ND); [apply in_map; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| apply in_map; exact Hb2]. }
pose proof (live_apart RT AF Σ1 m3 _ _ _ _ ART (LIVE1 b ltac:(rewrite ELBD; apply in_app_iff; left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb))
(LIVE1 b2 ltac:(rewrite ELBD; apply in_app_iff; right; exact Hb2)) NE) as AP.
clear - AP Hx Hin. unfold hid in *. lia. }
assert (PFA : forall x, P <= x < P + creq_size r -> ~ (f <= x < f + 64) /\ ~ (sf <= x < sf + 8)) by (intros x Hx; exact (NAF x (PCL x Hx))).
assert (NDL : List.NoDup (map blk_id LBL)) by (rewrite ELBD, map_app in ND; exact (List.NoDup_app_remove_l _ _ ND)).
assert (LIVEL : forall b, In b LBL -> In (blk_addr b, blk_size b) (rt_live RT Σ1)) by (intros b Hb; apply LIVE1; rewrite ELBD; apply in_app_iff; right; exact Hb).
assert (FRM1 : (length (rt_frames RT Σ1) + dec_depth low <= FRAMES_MAX)%nat) by (rewrite FRS1; cbn [length]; clear - FRMS; lia).
assert (EU : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; ulc).
assert (SPA96 : (usp + -96) mod 32 = 0) by (clear - SPA; Z.div_mod_to_equations; lia).
assert (AL8L : blocks_al8 LBL) by (intros x Hx; apply AL8; rewrite ELBD; apply in_app_iff; right; exact Hx).
subst LBD. cbn [sb_blocks app blocks_ivs map blk_addr blk_size fst snd] in PF. unfold SBSTATE_SIZEOF in PF.
destruct r; try discriminate GRP; cbn [ctl_req_code creq_size creq_align] in *.
1: {
subst OUTL. destruct DF0 as (ACP & PP0 & PT & POFF & PAP & PIMG & P4).
cbn [creq_pre] in PRE3. destruct PRE3 as (ws & WS3 & LWS).
pose proof INV as (_ & _ & _ & _ & NSF4 & _).
assert (INPG : In (a_pg a, 16) (rt_live RT Σ1)) by exact (LIVE1 (sbd_pi_gain s, a_pg a, 16) ltac:(cbn [sb_blocks app In]; do 6 right; left; reflexivity)).
assert (INPG0 : In (a_pg a, 16) (rt_live RT Σ)) by (rewrite <- LV1; exact INPG).
destruct (af_acc_live RT AF Σ1 m3 _ _ ART INPG) as (_ & ACPG).
destruct (live_below_lo RT AF Σ1 m3 _ _ lo ART INPG LOW) as (PGP & PGLO & _).
assert (OBPG : aobj asegs m3 (a_pg a) 16) by (split; [ulc|]; split; [ulc| exact ACPG]).
assert (PG8 : a_pg a mod 8 = 0) by exact (AL8 (sbd_pi_gain s, a_pg a, 16) ltac:(cbn [sb_blocks app In]; do 6 right; left; reflexivity)).
pose proof BUFS as (BG0 & BG1 & BEX & BOQ & BIQ & BMS & BPG & BER). clear BG0 BG1 BEX BOQ BIQ BMS BER.
pose proof JOK as (_ & _ & _ & _ & _ & _ & _ & _ & LPG & _).
assert (ACP3 : acc asegs m3 P 16).
{ destruct (ACCK2 m3 PF) as [(fp & kp & INFP & (O1 & O2 & O3 & O4)) | INP]; [exact O3|]. apply (af_acc_pois RT AF Σ1 m3 P 16 ART). rewrite PO1. exact INP. }
assert (OBP3 : aobj asegs m3 P 16) by (split; [lia|]; split; [ulc| exact ACP3]).
assert (INL0 : In (S, 160) (rt_live RT Σ)) by (rewrite <- LV1; exact INL).
assert (APS : P + 16 <= S \/ S + 160 <= P).
{ pose proof (proj2 (PDF P ltac:(lia)) S 160 INL0) as E1. pose proof (proj2 (PDF (P + 15) ltac:(lia)) S 160 INL0) as E2. clear - E1 E2. lia. }
assert (APQ : P + 16 <= a_pg a \/ a_pg a + 16 <= P).
{ pose proof (proj2 (PDF P ltac:(lia)) _ _ INPG0) as E1. pose proof (proj2 (PDF (P + 15) ltac:(lia)) _ _ INPG0) as E2. clear - E1 E2. lia. }
rewrite NSF4 in HD3.
cps_seg (sbarm2_pig usp S P f sf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 MI3 SBF ltac:(clear - PP0 PT; cbn in *; lia) OBS3 S8 SOFF
s a OUT j MP (a_low a) _ _ _ _ _ _ _ (sj_pg j) ws _ _ _ _ _ _ _ HD3 TL OBPG PG8 BPG LPG OBP3 P4 WS3 LWS APS APQ POFF).
destruct POST as (m4 & F4 & ws4 & xs3 & yb1 & yb2 & yb3 & yb4 & yb5 & -> & MU4 & WM4 & MI4 & WS4 & LWS4 & BPG4 & HD4 & TL4).
pose proof (agree_blocks_of_munch asegs _ m3 m4 (tl (sb_blocks s S a) ++ LBL) MU4 WM4
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1; cbn [outside]; split; [lia| exact I])) as AG4.
apply (sb_bufs_agree s S a j m3 m4) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG4 HD3 TL WS3 BPG BPG4 OBP3 OBPG APS APQ. unfold sbhd in HD4. unfold sbtl in TL4. rename TL4 into TL.
assert (PFA1 : P + 16 <= f \/ f + 64 <= P) by (pose proof (PFA P ltac:(lia)) as (E1 & _); pose proof (PFA (P + 15) ltac:(lia)) as (E2 & _); clear - E1 E2; lia).
assert (ART4 : X0ec.ART RT Σ1 m4).
{ apply (af_frame RT AF Σ1 m3 m4 lo ART LOW); [| exact WM4]. intros a0 Ha. apply MU4. cbn [outside]. split; [| exact I]. intros Hin. apply Ha.
apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp (rt_live RT Σ1) (rt_frames RT Σ1) lo); [| intros e He; rewrite LV1; exact He| intros e He; rewrite FRS1; right; exact He| ulc].
apply PCL. exact Hin. }
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W m m3 =>
assert (PF4 : rt_pres_fp L Fr U W m m4)
by (apply (pres_fp_trans _ _ _ _ m m3 m4 PF); apply (pres_fp_of_munch _ _ _ _ _ m3 m4 MU4); intros x _ Ho; cbn [outside] in Ho |- *; destruct Ho as (Ho & _); split; [exact Ho| exact I])
end.
clear PF ART. rename PF4 into PF. rename ART4 into ART.
trm MU4 WM4 FR3 ltac:(clear - PAP LO96; unfold hid in *; lia).
trm MU4 WM4 FRB3 ltac:(clear - PFA1; lia).
trm MU4 WM4 FRS3 ltac:(clear - POFF SHF1 SHF2; unfold hid, SH_LO, SH_HI in *; lia).
assert (ST4 : stk asegs m4 lo (usp + -96)) by (apply (stk_transport_disjoint asegs _ m3 m4 lo (usp + -96) ST3 MU4 WM4); cbn [disjoint_from]; clear - PAP LO96; unfold hid in *; lia).
clear ST3 ST2 MU4 MI3.

assert (FRSE : rw_cells asegs m4 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch asegs _ m4 m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m4 m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
Time cps_seg_post.

assert (EF2 : rt_frames RT Σ1 = (f, 0%nat) :: rt_frames RT Σ) by (exact FRS1).
assert (EL2 : rt_live RT Σ1 = rt_live RT Σ) by (exact LV1).
lazymatch goal with A : X0ec.ART RT Σ1 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO1 (PNIL E)) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < P \/ P + 16 <= fl).
{ destruct (Z_lt_dec fl P) as [L|L]; [left; exact L|]. destruct (Z_le_dec (P + 16) fl) as [G|G]; [right; exact G|]. exfalso.
exact (NFL fl (PCL fl ltac:(clear - L G; lia)) eq_refl). }
assert (FR6 : rw_cells asegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks asegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch asegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
rewrite <- NSF4 in HD4.
apply Hk. exists Σ3.
split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|];
split; [pose proof (dec_depth_pos low) as DP0; clear - EC CR1 DP0; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM0]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (dst_obj_sigma Σ Σ3 m7 P 16 (ACCK2 m7 PF) EF (eq_trans EP PO1)) as DST7.
cbn [speex_decoder_ctl fst snd creq_post dec_exc_ready creq_size].
split; [| split; [exists ws4; split; [exact WS4| exact LWS4]| split; [intros _; exact I| exact DST7]]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app asegs m7 S _ _)); split; [exact HD4| exact TL]|].
split; [exact BUFS|]. exists OUTLL. exact RLOW. }
1: {
subst OUTL. destruct DF0 as (ACP & PP0 & PT & POFF & PAP & PIMG & P4).
cbn [creq_pre] in PRE3. destruct PRE3 as ((ws & WS3 & LWS) & _).
pose proof INV as (_ & _ & _ & _ & NSF4 & _).
assert (INER : In (a_er a, 16) (rt_live RT Σ1)) by exact (LIVE1 (sbd_exc_rms s, a_er a, 16) ltac:(cbn [sb_blocks app In]; do 7 right; left; reflexivity)).
assert (INER0 : In (a_er a, 16) (rt_live RT Σ)) by (rewrite <- LV1; exact INER).
destruct (af_acc_live RT AF Σ1 m3 _ _ ART INER) as (_ & ACER).
destruct (live_below_lo RT AF Σ1 m3 _ _ lo ART INER LOW) as (ERP & ERLO & _).
assert (OBER : aobj asegs m3 (a_er a) 16) by (split; [ulc|]; split; [ulc| exact ACER]).
assert (ER8 : a_er a mod 8 = 0) by exact (AL8 (sbd_exc_rms s, a_er a, 16) ltac:(cbn [sb_blocks app In]; do 7 right; left; reflexivity)).
pose proof BUFS as (BG0 & BG1 & BEX & BOQ & BIQ & BMS & BPG & BER). clear BG0 BG1 BEX BOQ BIQ BMS BPG.
pose proof JOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & LPG).
assert (ACP3 : acc asegs m3 P 16).
{ destruct (ACCK2 m3 PF) as [(fp & kp & INFP & (O1 & O2 & O3 & O4)) | INP]; [exact O3|]. apply (af_acc_pois RT AF Σ1 m3 P 16 ART). rewrite PO1. exact INP. }
assert (OBP3 : aobj asegs m3 P 16) by (split; [lia|]; split; [ulc| exact ACP3]).
assert (INL0 : In (S, 160) (rt_live RT Σ)) by (rewrite <- LV1; exact INL).
assert (APS : P + 16 <= S \/ S + 160 <= P).
{ pose proof (proj2 (PDF P ltac:(lia)) S 160 INL0) as E1. pose proof (proj2 (PDF (P + 15) ltac:(lia)) S 160 INL0) as E2. clear - E1 E2. lia. }
assert (APQ : P + 16 <= a_er a \/ a_er a + 16 <= P).
{ pose proof (proj2 (PDF P ltac:(lia)) _ _ INER0) as E1. pose proof (proj2 (PDF (P + 15) ltac:(lia)) _ _ INER0) as E2. clear - E1 E2. lia. }
rewrite NSF4 in HD3.
cps_seg (sbarm2_exc usp S P f sf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 MI3 SBF ltac:(clear - PP0 PT; cbn in *; lia) OBS3 S8 SOFF
s a OUT j MP (a_low a) _ _ _ _ _ _ _ (sj_er j) ws _ _ _ _ _ _ _ HD3 TL OBER ER8 BER LPG OBP3 P4 WS3 LWS APS APQ POFF).
destruct POST as (m4 & F4 & ws4 & xs3 & yb1 & yb2 & yb3 & yb4 & yb5 & -> & MU4 & WM4 & MI4 & WS4 & LWS4 & BER4 & HD4 & TL4).
pose proof (agree_blocks_of_munch asegs _ m3 m4 (tl (sb_blocks s S a) ++ LBL) MU4 WM4
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1; cbn [outside]; split; [lia| exact I])) as AG4.
apply (sb_bufs_agree s S a j m3 m4) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG4 HD3 TL WS3 BER BER4 OBP3 OBER APS APQ. unfold sbhd in HD4. unfold sbtl in TL4. rename TL4 into TL.
assert (PFA1 : P + 16 <= f \/ f + 64 <= P) by (pose proof (PFA P ltac:(lia)) as (E1 & _); pose proof (PFA (P + 15) ltac:(lia)) as (E2 & _); clear - E1 E2; lia).
assert (ART4 : X0ec.ART RT Σ1 m4).
{ apply (af_frame RT AF Σ1 m3 m4 lo ART LOW); [| exact WM4]. intros a0 Ha. apply MU4. cbn [outside]. split; [| exact I]. intros Hin. apply Ha.
apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp (rt_live RT Σ1) (rt_frames RT Σ1) lo); [| intros e He; rewrite LV1; exact He| intros e He; rewrite FRS1; right; exact He| ulc].
apply PCL. exact Hin. }
lazymatch type of PF with rt_pres_fp ?L ?Fr ?U ?W m m3 =>
assert (PF4 : rt_pres_fp L Fr U W m m4)
by (apply (pres_fp_trans _ _ _ _ m m3 m4 PF); apply (pres_fp_of_munch _ _ _ _ _ m3 m4 MU4); intros x _ Ho; cbn [outside] in Ho |- *; destruct Ho as (Ho & _); split; [exact Ho| exact I])
end.
clear PF ART. rename PF4 into PF. rename ART4 into ART.
trm MU4 WM4 FR3 ltac:(clear - PAP LO96; unfold hid in *; lia).
trm MU4 WM4 FRB3 ltac:(clear - PFA1; lia).
trm MU4 WM4 FRS3 ltac:(clear - POFF SHF1 SHF2; unfold hid, SH_LO, SH_HI in *; lia).
assert (ST4 : stk asegs m4 lo (usp + -96)) by (apply (stk_transport_disjoint asegs _ m3 m4 lo (usp + -96) ST3 MU4 WM4); cbn [disjoint_from]; clear - PAP LO96; unfold hid in *; lia).
clear ST3 ST2 MU4 MI3.

assert (FRSE : rw_cells asegs m4 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch asegs _ m4 m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m4 m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
Time cps_seg_post.

assert (EF2 : rt_frames RT Σ1 = (f, 0%nat) :: rt_frames RT Σ) by (exact FRS1).
assert (EL2 : rt_live RT Σ1 = rt_live RT Σ) by (exact LV1).
lazymatch goal with A : X0ec.ART RT Σ1 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO1 (PNIL E)) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < P \/ P + 16 <= fl).
{ destruct (Z_lt_dec fl P) as [L|L]; [left; exact L|]. destruct (Z_le_dec (P + 16) fl) as [G|G]; [right; exact G|]. exfalso.
exact (NFL fl (PCL fl ltac:(clear - L G; lia)) eq_refl). }
assert (FR6 : rw_cells asegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks asegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch asegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
rewrite <- NSF4 in HD4.
apply Hk. exists Σ3.
split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|];
split; [pose proof (dec_depth_pos low) as DP0; clear - EC CR1 DP0; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM0]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (dst_obj_sigma Σ Σ3 m7 P 16 (ACCK2 m7 PF) EF (eq_trans EP PO1)) as DST7.
cbn [speex_decoder_ctl fst snd creq_post dec_exc_ready creq_size].
split; [| split; [exists ws4; split; [exact WS4| exact LWS4]| split; [intros _; exact I| exact DST7]]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app asegs m7 S _ _)); split; [exact HD4| exact TL]|].
split; [exact BUFS|]. exists OUTLL. exact RLOW. }
1: {
subst OUTL. destruct DF0 as (ACP & PP0 & PT & POFF & PAP & PIMG & P4).
cps_seg (sbarm2_dtx usp S P f sf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 MI3 SBF OBS3 S8 SOFF).
destruct POST as (ya3 & ya4 & ya5 & ->).
assert (DST1 : dst_obj RT Σ1 m3 P 4).
{ destruct (ACCK2 m3 PF) as [(fp & kp & INFP & IFO) | INP]; [left; exists fp, kp; split; [rewrite FRS1; right; exact INFP| exact IFO]| right; rewrite PO1; exact INP]. }
lazymatch goal with Hc : ASTA ?RT ?Σ ?PMc (eq ?ms) ?c |- realizes asegs ?c ?T => refine (rz_cps RT Σ PMc ms _ T c Hc _ _) end;
[ eapply (IH Σ1 PMc) with (OUTL := OUTLL) (OUT := OUTLL) (STEREO := STEREO) (S := a_low a) (LBD := LBL) (r := CtlGetDtxStatus) (P := P) (lo := lo); cps_auto | ].
{ rewrite EU. apply (pois_above_le _ usp); [exact POA| clear; lia]. }
{ rewrite EU. exact ST3. }
intros cc5 (Σ2 & Hc5 & LV2 & FRS2 & SP2 & CR2 & PO2).
destruct (ASTA_unpack RT Σ2 PMc _ cc5 Hc5) as (ms5 & PO5 & Hc5'). clear Hc5. cbv beta in PO5.
destruct PO5 as (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & REP5 & CP5 & EXC5 & DST5).
destruct RS5 as (zt0 & zt1 & zt2 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & F5 & fc5 & -> & FRM5).
rewrite EU in *. cbn [creq_ivs creq_size app] in PRES5.

assert (INL0 : In (S, 160) (rt_live RT Σ)) by (rewrite <- LV1; exact INL).
assert (APS : P + 4 <= S \/ S + 160 <= P).
{ pose proof (proj2 (PDF P ltac:(lia)) S 160 INL0) as E1. pose proof (proj2 (PDF (P + 3) ltac:(lia)) S 160 INL0) as E2. clear - E1 E2. lia. }
assert (PFA1 : P + 4 <= f \/ f + 64 <= P) by (pose proof (PFA P ltac:(lia)) as (E1 & _); pose proof (PFA (P + 3) ltac:(lia)) as (E2 & _); clear - E1 E2; lia).
xfp PRES5 WM5 OUTB FR3. xfp PRES5 WM5 OUTB FRB3. xfp PRES5 WM5 OUTB FRS3. xfp PRES5 WM5 OUTB HD3. xfp PRES5 WM5 OUTB TL.
assert (AG5 : agree_blocks asegs m3 m5 (tl (sb_blocks s S a))).
{ apply (agree_blocks_of_pres_fp RT Σ1 _ _ _ m3 m5 _ PRES5 WM5).
- intros b Hb. apply LIVE1. apply in_app_iff. left. cbn [sb_blocks tl] in Hb |- *. right. exact Hb.
- intros b x Hb Hx. split; [| exact (APL b x Hb Hx)].
pose proof (BOUT b x ltac:(apply in_app_iff; left; exact Hb) Hx) as H1. clear - H1. cbn [fst snd]. lia. }
apply (sb_bufs_agree s S a j m3 m5) in BUFS; [| exact JOK | exact AG5]. clear AG5 RLOW.
assert (PF5 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp ((P, P + 4) :: (S, S + 160) :: blocks_ivs (tl (sb_blocks s S a) ++ LBL)) m m5).
{ apply (pres_fp_trans _ _ _ _ m m3 m5 PF). apply (pres_fp_of_pres_fp _ _ _ _ (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -96) _ m3 m5 PRES5).
- intros e He. rewrite LV1. exact He.
- intros e He. rewrite FRS1. right. exact He.
- lia.
- intros x Hx (O1 & O2 & O3). split; [exact O1| exact (outside_blocks_app_r (tl (sb_blocks s S a)) LBL x O3)]. }
clear PF PRES5. rename PF5 into PF.
cps_sigma LV2 FRS2 SP2.
destruct CP5 as (ARG5 & RV5).
destruct (af_acc_live RT AF Σ2 m5 S 160 ART5 INL) as (_ & ACS5).
assert (OBS5 : aobj asegs m5 S 160) by (split; [lia|]; split; [ulc| exact ACS5]).
cps_seg (sbarm_pass_b usp S P f sf).
subst ms.
clear OBS5 ACS5. unfold sbhd in HD3.

assert (FRSE : rw_cells asegs m5 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch asegs _ m5 m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m5 m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ2 = (f, 0%nat) :: rt_frames RT Σ) by (rewrite FRS2; exact FRS1).
assert (EL2 : rt_live RT Σ2 = rt_live RT Σ) by (rewrite LV2; exact LV1).
lazymatch goal with A : X0ec.ART RT Σ2 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO2 (eq_trans PO1 (PNIL E))) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FLP : fl < P \/ P + 4 <= fl).
{ destruct (Z_lt_dec fl P) as [L|L]; [left; exact L|]. destruct (Z_le_dec (P + 4) fl) as [G|G]; [right; exact G|]. exfalso.
exact (NFL fl (PCL fl ltac:(clear - L G; lia)) eq_refl). }
assert (FR6 : rw_cells asegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks asegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch asegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
rewrite LV2. apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in REP5; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3. split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|]; split; [clear - EC CR2 CR1; cbn [dec_depth] in *; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM5]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [exact PF|].
pose proof (dst_obj_sigma Σ Σ3 m7 P 4 (ACCK2 m7 PF) EF (eq_trans EP (eq_trans PO2 PO1))) as DST7.
cbn [speex_decoder_ctl] in *. destruct (speex_decoder_ctl low CtlGetDtxStatus) as [v' low'] eqn:EC5. cbn [fst snd creq_post dec_exc_ready] in *.
split; [| split; [split; [exact ARG5| exact RV5]| split; [intros _; exact I| exact DST7]]].
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|]. split; [exact INV|]. split; [exact JOK|].
split; [rewrite sb_cells_split, <- EMP; apply (proj2 (rw_cells_app asegs m7 S _ _)); split; [exact HD3| exact TL]|].
split; [exact BUFS|]. exists OUTLL. exact REP5. }
1: {
cbn [creq_ok] in OK. destruct OK as (EP & OFF160).
cps_seg (sbarm2_isv usp S P f sf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 MI3 SBF OBS3 S8 SOFF s a OUTL OUT off j _ _ _ _ _ _ _ EP TL).
destruct POST as (m4 & xa1 & -> & TL4 & MU4 & WM4 & MI4).
pose proof (agree_blocks_of_munch asegs _ m3 m4 (tl (sb_blocks s S a) ++ LBL) MU4 WM4
ltac:(intros b x Hb Hx; pose proof (BOUT b x Hb Hx) as H1; clear - H1; cbn [outside]; split; [lia| exact I])) as AG4.
apply (sb_bufs_agree s S a j m3 m4) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG4| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG4 TL. unfold sbtl in TL4. rename TL4 into TL. unfold sbhd in HD3.
cps_seg_post.

assert (FRSE : rw_cells asegs m4 sf (sbctl_shadow bF8 bF8)) by exact FRS3. clear FRS3.
chunk_uncons FRB3 as HDF.
cps_seg (sbctl_epi_a usp f sf).
destruct POST as (m6 & -> & MU6 & WM6 & MI6 & FRS6).
pose proof (agree_blocks_of_munch asegs _ m4 m6 (tl (sb_blocks s S a) ++ LBL) MU6 WM6
ltac:(intros b x Hb Hx; pose proof (BOUT2 b x Hb Hx) as H2; clear - H2; cbn [outside]; repeat split; lia)) as AG6.
apply (sb_bufs_agree s S a j m4 m6) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG6| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG6 HDF FRSE FRB3 . unfold sbctl_shadow_dead, bF5 in FRS6. cbn [map repeat] in FRS6.
cps_seg_post.

assert (EF2 : rt_frames RT Σ1 = (f, 0%nat) :: rt_frames RT Σ) by (exact FRS1).
assert (EL2 : rt_live RT Σ1 = rt_live RT Σ) by (exact LV1).
lazymatch goal with A : X0ec.ART RT Σ1 _ |- _ => rename A into ARTX end.
cps_release_intro ARTX EF2 EL2 (fun E : rt_frames RT Σ = [] => eq_trans PO1 (PNIL E)) Σ3 fl.
assert (FLS : fl < S \/ S + 160 <= fl).
{ destruct (Z_lt_dec fl S) as [L|L]; [left; exact L|]. destruct (Z_le_dec (S + 160) fl) as [G|G]; [right; exact G|]. exfalso. apply NAC.
right; right; left. exists S, 160. split; [exact INL| clear - L G; lia]. }
assert (FR6 : rw_cells asegs m6 (usp + -96) (sbctl_frame (C8 (Z_to_bv 64 f)) s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)) by exact FR3. clear FR3.
cps_seg (sbctl_epi_b usp lo f fl).
destruct POST as (m7 & -> & MU7 & WM7 & MI7 & ST7 & FLG7).
assert (AG7 : agree_blocks asegs m6 m7 (tl (sb_blocks s S a) ++ LBL)).
{ apply (agree_blocks_of_munch asegs _ m6 m7 _ MU7 WM7). intros b x Hb Hx. cbn [outside]. split; [| exact I]. intros Hfl.
apply NAC. right; right; left. exists (blk_addr b), (blk_size b). split; [| clear - Hx Hfl; lia].
apply LIVE1. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; cbn [sb_blocks tl] in Hb |- *; right; exact Hb| right; exact Hb]. }
apply (sb_bufs_agree s S a j m6 m7) in BUFS; [| exact JOK | eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; left; exact Hb]].
eapply decst_rep_agree in RLOW; [| eapply agree_blocks_sub; [exact AG7| intros b Hb; apply in_app_iff; right; exact Hb]].
clear AG7 FR6 FRS6.
cps_release_done REL MU7 WM7 FLG7.
apply Hk. exists Σ3.
split; [| cbn [dec_depth]; split; [congruence|]; split; [congruence|]; split; [congruence|];
split; [pose proof (dec_depth_pos low) as DP0; clear - EC CR1 DP0; lia| congruence]].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m7.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM0]|].
split. { split; [assumption|]. split; [exact MI7|]. split; [cps_wmono| exact ST7]. }
split; [apply (pres_fp_weaken _ _ _ _ _ _ _ PF); intros x Hx; cbn [creq_ivs app] in Hx; split; [cbn [fst snd]; clear; lia| exact Hx]|].
cbn [speex_decoder_ctl fst snd creq_post dec_exc_ready].
split; [| split; [exact I| split; [intros _; exact I| exact I]]].
pose proof INV as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12).
cbn [decst_rep]. exists a, j, LBL. split; [reflexivity|]. split; [exact S8|]. split; [exact SPOS|].
split; [unfold sb_inv; cbn [set_sbd_innov_save sbd_mode sbd_frame_size sbd_full_frame_size sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first
sbd_sampling_rate sbd_lpc_enh_enabled sbd_encode_submode sbd_submodeID sbd_innov_save];
refine (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj I7 (conj I8 (conj I9 (conj I10 (conj I11 _))))))))))); clear - OFF160; lia|].
split; [exact JOK|].
split; [rewrite sb_cells_split; cbn [set_sbd_innov_save sbd_mode sbd_full_frame_size sbd_frame_size sbd_subframeSize sbd_nbSubframes sbd_lpcSize sbd_first
sbd_sampling_rate sbd_lpc_enh_enabled]; rewrite <- EMP; apply (proj2 (rw_cells_app asegs m7 S _ _)); split; [exact HD3| exact TL]|].
split; [exact BUFS|]. exists OUTLL. exact RLOW. }
Qed.

Theorem ctl2_cps_all : forall d, ctl2_cps_at RT d.
Proof using AF SM0 AF_LIB.
induction d as [st | s low IH]; [exact (ctl2_cps_nb st) | exact (ctl2_cps_sb s low IH)].
Qed.
End Ctl2.
