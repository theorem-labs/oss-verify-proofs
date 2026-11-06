(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1cg X1ck X1cu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05p X05s X05u
X081 X05l X05m X09f X06d X069 X05y X05z X060.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0yr X0wl X0wn X0ys X0x2 X0wr X0ws X0wt.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wn OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ys OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wr OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ws OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wt.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Fixpoint ctl_stack (d : dec_state bptr) : Z := match d with DecNB _ => NBCTL_STACK | DecSB _ low => 96 + ctl_stack low end.

Section CtlCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Definition ctl_cps_at (d : dec_state bptr) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (OUT STEREO S : Z) (LBD : list block) (r : ctl_req) (P lo fp : Z) (kp : nat),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (ctl_req_code r) -> a2 = Z_to_bv 64 P -> tp = Z_to_bv 64 0x638c98 ->
creq_grp1 r = true ->
DREP OUT STEREO m S d LBD -> (dec_depth d <= 3)%nat -> List.NoDup (map blk_id LBD) ->
creq_ok OUT P r -> creq_pre STEREO m S d P r ->
(forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ)) ->
In (fp, kp) (rt_frames RT Σ) -> fp <= P -> P + creq_size r <= fp + fs_size kp - 8 -> acc bsegs m P (creq_size r) -> P mod creq_align r = 0 ->
(length (rt_frames RT Σ) + dec_depth d <= FRAMES_MAX)%nat -> Z.of_nat (dec_depth d) <= rt_credit RT Σ + 1 ->
ART RT Σ m -> mem_inv bsegs m -> X1cn.frm0 fc ->
stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + ctl_stack d <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_ctl m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun _ fc' => X1cn.frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (creq_ivs P r ++ blocks_ivs LBD) m m'
/\ DREP OUT STEREO m' S (snd (speex_decoder_ctl d r)) LBD
/\ creq_post STEREO m' P r (fst (speex_decoder_ctl d r))
/\ acc bsegs m' P (creq_size r)) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - (Z.of_nat (dec_depth d) - 1) <= rt_credit RT Σ' <= rt_credit RT Σ
/\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem ctl_cps_nb : forall st, ctl_cps_at (DecNB st).
Proof using AF AF_LIB.
intros st Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S LBD r P lo fp kp FDO MST -> -> -> -> GRP REP DEP ND OK PRE LIVE INF FP1 FP2 ACP PAL FRM CRD ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
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
destruct (frame_below_lo RT AF Σ m fp kp lo ART0 INF LOW) as (BF1 & BF2 & _).
pose proof (frame_facts RT AF Σ m fp kp ART0 INF) as (FP0 & FP64 & FPIMG & _ & FPHI & _ & _ & _ & _ & _).
destruct (frame_live_apart RT AF Σ m fp kp S 2968 ART0 INF INL) as (FLA1 & _).
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (SZ : 0 <= creq_size r <= 24) by (destruct r; cbn; lia).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (AF_LIB Σ m ART0) as LC0.
assert (OBM : aobj bsegs m A_speex_nb_mode 96)
by (apply (aobj_lit RT AF Σ m A_speex_nb_mode 96 ART0); [unfold ACC_LITS, A_speex_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_nb_mode; lia | unfold A_speex_nb_mode, APP_TOP; lia]).
assert (EW : creq_ivs P r ++ blocks_ivs [(nb_blk st, S, NBSTATE_SIZEOF)] = [(P, P + creq_size r); (S, S + 2968)])
by (destruct r; try discriminate GRP; reflexivity).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(P, P + creq_size r); (S, S + 2968)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm.
refine (rz_evt RT AF Σ PMc _ _ T c MST Hc (rctl_nbA st OUT STEREO S _ r P lo usp ra gp (Z_to_bv 64 6524056) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m GRP REP OK PRE _ _ PAL ltac:(clear - FP0 FP1; lia) OBM _ _ ST0 _ _ _ CC0 LC0 MI0 FRM0) _).
- intros b [<-|[]]. unfold ablk, blk_addr, blk_size. cbn [fst snd]. unfold NBSTATE_SIZEOF.
split; [split; [lia|]; split; [ulc| exact ACS]|]. split; [exact (proj1 NB)|]. split; [unfold SH_LO, SH_HI; lia|]. split; [unfold IMG_TOP_B, IMG_TOP; ulc| exact BD1].
- split; [lia|]. split; [ulc| exact ACP].
- left. lia.
- intros b [<-|[]]. unfold blk_addr, blk_size. cbn [fst snd]. unfold NBSTATE_SIZEOF. lia.
- exact LOS.
- unfold NBCTL_STACK. ulc.
- ulc.
- intros ms' c' POST Hc'. clear Hc.
destruct POST as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F' & fc' & m' & -> & MU & WM & MI' & FRM' & ST' & REP' & CP' & _).
rewrite (ctlW_grp1 _ _ _ _ _ GRP) in MU. cbn [blocks_ivs map blk_addr blk_size fst snd] in MU. unfold NBSTATE_SIZEOF in MU.
assert (ACP' : acc bsegs m' P (creq_size r)).
{ refine (proj2 (proj2 (aobj_munch bsegs _ m m' P (creq_size r) _ MU _))); [split; [lia|]; split; [ulc| exact ACP]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; lia| lia| ulc]. }
cps_seg_post.
apply Hk. exists Σ. split; [| cbn [dec_depth]; repeat split; lia].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM']|].
split. { split; [assumption|]. split; [exact MI'|]. split; [exact WM| exact ST']. }
split; [rewrite EW; exact PF|]. split; [exact REP'|]. split; [exact CP'| exact ACP'].
Qed.
End CtlCPS.

End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Fixpoint ctl_stack (d : dec_state bptr) : Z := match d with DecNB _ => NBCTL_STACK | DecSB _ low => 96 + ctl_stack low end.

Section CtlCPS.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis AF_LIB : forall Σ m, ART RT Σ m -> lib_consts m.

Definition ctl_cps_at (d : dec_state bptr) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (OUT STEREO S : Z) (LBD : list block) (r : ctl_req) (P lo fp : Z) (kp : nat),
fdfs_only PMc -> mat_stable PMc ->
a0 = Z_to_bv 64 S -> a1 = Z_to_bv 64 (ctl_req_code r) -> a2 = Z_to_bv 64 P -> tp = Z_to_bv 64 0x630458 ->
creq_grp1 r = true ->
DREP OUT STEREO m S d LBD -> (dec_depth d <= 3)%nat -> List.NoDup (map blk_id LBD) ->
creq_ok OUT P r -> creq_pre STEREO m S d P r ->
(forall b, In b LBD -> In (blk_addr b, blk_size b) (rt_live RT Σ)) ->
In (fp, kp) (rt_frames RT Σ) -> fp <= P -> P + creq_size r <= fp + fs_size kp - 8 -> acc asegs m P (creq_size r) -> P mod creq_align r = 0 ->
(length (rt_frames RT Σ) + dec_depth d <= FRAMES_MAX)%nat -> Z.of_nat (dec_depth d) <= rt_credit RT Σ + 1 ->
ART RT Σ m -> mem_inv asegs m -> frm0 fc ->
stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + RT_STACK + ctl_stack d <= bv_unsigned sp ->
bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 32 = 0 ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc A_speex_decoder_ctl m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m',
ret_stL (fun _ fc' => frm0 fc') ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (creq_ivs P r ++ blocks_ivs LBD) m m'
/\ DREP OUT STEREO m' S (snd (speex_decoder_ctl d r)) LBD
/\ creq_post STEREO m' P r (fst (speex_decoder_ctl d r))
/\ acc asegs m' P (creq_size r)) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - (Z.of_nat (dec_depth d) - 1) <= rt_credit RT Σ' <= rt_credit RT Σ
/\ rt_pois RT Σ' = rt_pois RT Σ).

Theorem ctl_cps_nb : forall st, ctl_cps_at (DecNB st).
Proof using AF AF_LIB.
intros st Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
OUT STEREO S LBD r P lo fp kp FDO MST -> -> -> -> GRP REP DEP ND OK PRE LIVE INF FP1 FP2 ACP PAL FRM CRD ART0 MI0 FRM0 ST0 LOW LOR SPT SPA.
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
destruct (frame_below_lo RT AF Σ m fp kp lo ART0 INF LOW) as (BF1 & BF2 & _).
pose proof (frame_facts RT AF Σ m fp kp ART0 INF) as (FP0 & FP64 & FPIMG & _ & FPHI & _ & _ & _ & _ & _).
destruct (frame_live_apart RT AF Σ m fp kp S 2968 ART0 INF INL) as (FLA1 & _).
assert (FSZ : 0 <= fs_size kp) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
assert (SZ : 0 <= creq_size r <= 24) by (destruct r; cbn; lia).
pose proof (af_client_consts RT AF Σ m ART0) as CC0.
pose proof (AF_LIB Σ m ART0) as LC0.
assert (OBM : aobj asegs m A_speex_nb_mode 96)
by (apply (aobj_lit RT AF Σ m A_speex_nb_mode 96 ART0); [unfold ACC_LITS, A_speex_nb_mode; cbn [In]; repeat (first [left; reflexivity | right]) | unfold A_speex_nb_mode; lia | unfold A_speex_nb_mode, APP_TOP; lia]).
assert (EW : creq_ivs P r ++ blocks_ivs [(nb_blk st, S, NBSTATE_SIZEOF)] = [(P, P + creq_size r); (S, S + 2968)])
by (destruct r; try discriminate GRP; reflexivity).
pose proof (pres_fp_refl (rt_live RT Σ) (rt_frames RT Σ) usp [(P, P + creq_size r); (S, S + 2968)] m) as PF.
pose proof (fun a => aclient_split RT AF Σ m usp a ART0) as SPL.
cps_norm.
refine (rz_evt RT AF Σ PMc _ _ T c MST Hc (rctl_nbA st OUT STEREO S _ r P lo usp ra gp (Z_to_bv 64 6489176) t0 t1 t2 s0 s1 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m GRP REP OK PRE _ _ PAL OBM _ _ ST0 _ _ _ CC0 LC0 MI0 FRM0) _).
- intros b [<-|[]]. unfold ablk, blk_addr, blk_size. cbn [fst snd]. unfold NBSTATE_SIZEOF.
split; [split; [lia|]; split; [ulc| exact ACS]|]. split; [exact (proj1 NB)|]. split; [unfold SH_LO, SH_HI; lia|]. split; [unfold IMG_TOP; ulc| exact BD1].
- split; [lia|]. split; [ulc| exact ACP].
- left. lia.
- intros b [<-|[]]. unfold blk_addr, blk_size. cbn [fst snd]. unfold NBSTATE_SIZEOF. lia.
- exact LOS.
- unfold NBCTL_STACK. ulc.
- ulc.
- intros ms' c' POST Hc'. clear Hc.
destruct POST as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F' & fc' & m' & -> & MU & WM & MI' & FRM' & ST' & REP' & CP' & _).
rewrite (ctlW_grp1 _ _ _ _ _ GRP) in MU. cbn [blocks_ivs map blk_addr blk_size fst snd] in MU. unfold NBSTATE_SIZEOF in MU.
assert (ACP' : acc asegs m' P (creq_size r)).
{ refine (proj2 (proj2 (aobj_munch asegs _ m m' P (creq_size r) _ MU _))); [split; [lia|]; split; [ulc| exact ACP]|].
apply shfree_of_offsh; [cbn; unfold SH_LO, SH_HI; repeat split; lia| lia| ulc]. }
cps_seg_post.
apply Hk. exists Σ. split; [| cbn [dec_depth]; repeat split; lia].
eapply ASTA_conseq; [eassumption|]. intros ms <-. exists m'.
split; [rewrite ESP; unfold ret_stL; do 16 eexists; split; [reflexivity| exact FRM']|].
split. { split; [assumption|]. split; [exact MI'|]. split; [exact WM| exact ST']. }
split; [rewrite EW; exact PF|]. split; [exact REP'|]. split; [exact CP'| exact ACP'].
Qed.
End CtlCPS.
