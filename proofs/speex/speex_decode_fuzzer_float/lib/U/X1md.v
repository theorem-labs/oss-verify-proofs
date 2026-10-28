(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma X1mw X1mo X1mu X1me.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma nodup_app_ids : forall (L1 L2 : list block) x y,
List.NoDup (map blk_id (L1 ++ L2)) -> In x L1 -> In y L2 -> blk_id x <> blk_id y.
Proof.
induction L1 as [|z L1 IHL]; intros L2 x y ND Hx Hy; [destruct Hx|].
cbn in ND. inversion ND as [|u l NI ND']; subst.
destruct Hx as [<- | Hx].
- intros E. apply NI. rewrite map_app. apply in_app_iff. right. rewrite E. apply in_map. exact Hy.
- eapply IHL; eassumption.
Qed.

Lemma in_nth_error {T} : forall (L : list T) i x, nth_error L i = Some x -> In x L.
Proof. intros L i x H. eapply nth_error_In. exact H. Qed.

Section Layout.
Context {RCEIL : RunCeiling}.
Variable (s : sbd_state bptr) (S OUT BITS Dc DSZ STEREO lo usp : Z) (a : sb_addrs) (LBL : list block).
Let L := sb_blocks s S a ++ LBL.
Hypothesis RLAY : rdec_layout BITS OUT STEREO lo usp.
Hypothesis RNG : forall x, In x L -> rblock_range (blk_addr x) (blk_size x).
Hypothesis ND : List.NoDup (map blk_id L).
Hypothesis AP : lbd_apart L.
Hypothesis DRNG : rblock_range Dc DSZ.
Hypothesis DAP : forall x, In x L -> apart Dc DSZ (blk_addr x) (blk_size x).

#[using="L RLAY RNG ND AP DRNG DAP"] Lemma sb_layout_intro :
sb_layout S OUT BITS Dc DSZ STEREO (a_g0 a) (a_g1 a) (a_exc a) (4 * sbd_subframeSize s) (a_oq a) (a_iq a) (a_msp a) (a_pg a) (a_er a) lo usp LBL.
Proof.
unfold rdec_layout, apart, BITS_SIZEOF, HOUT_BYTES in RLAY.
first [ sf_destruct 10%nat RLAY as T1 T2 T3 T4 P1 P2 P3 K1 K2 K3 | sf_fb; destruct RLAY as (T1 & T2 & T3 & T4 & P1 & P2 & P3 & K1 & K2 & K3) ].

pose proof (RNG _ (in_nth_error L 0 _ eq_refl)) as R0. pose proof (RNG _ (in_nth_error L 1 _ eq_refl)) as R1.
pose proof (RNG _ (in_nth_error L 2 _ eq_refl)) as R2. pose proof (RNG _ (in_nth_error L 3 _ eq_refl)) as R3.
pose proof (RNG _ (in_nth_error L 4 _ eq_refl)) as R4. pose proof (RNG _ (in_nth_error L 5 _ eq_refl)) as R5.
pose proof (RNG _ (in_nth_error L 6 _ eq_refl)) as R6. pose proof (RNG _ (in_nth_error L 7 _ eq_refl)) as R7.
pose proof (RNG _ (in_nth_error L 8 _ eq_refl)) as R8.
pose proof (DAP _ (in_nth_error L 0 _ eq_refl)) as Q0. pose proof (DAP _ (in_nth_error L 1 _ eq_refl)) as Q1.
pose proof (DAP _ (in_nth_error L 2 _ eq_refl)) as Q2. pose proof (DAP _ (in_nth_error L 3 _ eq_refl)) as Q3.
pose proof (DAP _ (in_nth_error L 4 _ eq_refl)) as Q4. pose proof (DAP _ (in_nth_error L 5 _ eq_refl)) as Q5.
pose proof (DAP _ (in_nth_error L 6 _ eq_refl)) as Q6. pose proof (DAP _ (in_nth_error L 7 _ eq_refl)) as Q7.
pose proof (DAP _ (in_nth_error L 8 _ eq_refl)) as Q8.
cbn [blk_addr blk_size fst snd] in R0, R1, R2, R3, R4, R5, R6, R7, R8, Q0, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8.
unfold rblock_range, apart, SBSTATE_SIZEOF in R0, R1, R2, R3, R4, R5, R6, R7, R8, Q0, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, DRNG.

Ltac pp i j H :=
pose proof (blocks_apart_ij _ i j _ _ ND AP ltac:(lia) eq_refl eq_refl) as H; cbn [blk_addr blk_size fst snd] in H; unfold SBSTATE_SIZEOF in H.
pp 0%nat 1%nat PR_0_1. pp 0%nat 2%nat PR_0_2. pp 0%nat 3%nat PR_0_3. pp 0%nat 4%nat PR_0_4. pp 0%nat 5%nat PR_0_5. pp 0%nat 6%nat PR_0_6. pp 0%nat 7%nat PR_0_7. pp 0%nat 8%nat PR_0_8.
pp 1%nat 2%nat PR_1_2. pp 1%nat 3%nat PR_1_3. pp 1%nat 4%nat PR_1_4. pp 1%nat 5%nat PR_1_5. pp 1%nat 6%nat PR_1_6. pp 1%nat 7%nat PR_1_7. pp 1%nat 8%nat PR_1_8.
pp 2%nat 3%nat PR_2_3. pp 2%nat 4%nat PR_2_4. pp 2%nat 5%nat PR_2_5. pp 2%nat 6%nat PR_2_6. pp 2%nat 7%nat PR_2_7. pp 2%nat 8%nat PR_2_8.
pp 3%nat 4%nat PR_3_4. pp 3%nat 5%nat PR_3_5. pp 3%nat 6%nat PR_3_6. pp 3%nat 7%nat PR_3_7. pp 3%nat 8%nat PR_3_8.
pp 4%nat 5%nat PR_4_5. pp 4%nat 6%nat PR_4_6. pp 4%nat 7%nat PR_4_7. pp 4%nat 8%nat PR_4_8.
pp 5%nat 6%nat PR_5_6. pp 5%nat 7%nat PR_5_7. pp 5%nat 8%nat PR_5_8.
pp 6%nat 7%nat PR_6_7. pp 6%nat 8%nat PR_6_8.
pp 7%nat 8%nat PR_7_8.
constructor.
{ exact T4. }
{ exact T2. }
{ exact T1. }
{ exact T3. }
{ clear -P1; lia. }
{ clear -P3; lia. }
{ clear -P2; lia. }
{ clear -K2; lia. }
{ clear -K1; lia. }
{ clear -K3; lia. }
{ clear -R0; lia. }
{ clear -R0; lia. }
{ clear -R0; lia. }
{ clear -DRNG; lia. }
{ clear -DRNG; lia. }
{ clear -DRNG; lia. }
{ clear -R1; lia. }
{ clear -R1; lia. }
{ clear -R1; lia. }
{ clear -R2; lia. }
{ clear -R2; lia. }
{ clear -R2; lia. }
{ clear -R3; lia. }
{ clear -R3; lia. }
{ clear -R3; lia. }
{ clear -R4; lia. }
{ clear -R4; lia. }
{ clear -R4; lia. }
{ clear -R5; lia. }
{ clear -R5; lia. }
{ clear -R5; lia. }
{ clear -R8; lia. }
{ clear -R8; lia. }
{ clear -R8; lia. }
{ clear -R6; lia. }
{ clear -R6; lia. }
{ clear -R6; lia. }
{ clear -R7; lia. }
{ clear -R7; lia. }
{ clear -R7; lia. }
{ clear -Q0; lia. }
{ clear -PR_0_1; lia. }
{ clear -PR_0_2; lia. }
{ clear -PR_0_3; lia. }
{ clear -PR_0_4; lia. }
{ clear -PR_0_5; lia. }
{ clear -PR_0_8; lia. }
{ clear -PR_0_6; lia. }
{ clear -PR_0_7; lia. }
{ clear -Q1; lia. }
{ clear -Q2; lia. }
{ clear -Q3; lia. }
{ clear -Q4; lia. }
{ clear -Q5; lia. }
{ clear -Q8; lia. }
{ clear -Q6; lia. }
{ clear -Q7; lia. }
{ clear -PR_1_2; lia. }
{ clear -PR_1_3; lia. }
{ clear -PR_1_4; lia. }
{ clear -PR_1_5; lia. }
{ clear -PR_1_8; lia. }
{ clear -PR_1_6; lia. }
{ clear -PR_1_7; lia. }
{ clear -PR_2_3; lia. }
{ clear -PR_2_4; lia. }
{ clear -PR_2_5; lia. }
{ clear -PR_2_8; lia. }
{ clear -PR_2_6; lia. }
{ clear -PR_2_7; lia. }
{ clear -PR_3_4; lia. }
{ clear -PR_3_5; lia. }
{ clear -PR_3_8; lia. }
{ clear -PR_3_6; lia. }
{ clear -PR_3_7; lia. }
{ clear -PR_4_5; lia. }
{ clear -PR_4_8; lia. }
{ clear -PR_4_6; lia. }
{ clear -PR_4_7; lia. }
{ clear -PR_5_8; lia. }
{ clear -PR_5_6; lia. }
{ clear -PR_5_7; lia. }
{ clear -PR_6_8; lia. }
{ clear -PR_7_8; lia. }
{ clear -PR_6_7; lia. }
{ intros bb Hbb; pose proof (RNG bb ltac:(apply in_app_iff; right; exact Hbb)) as RB; unfold rblock_range in RB; clear -RB; lia. }
{ intros bb Hbb; pose proof (AP _ bb (in_nth_error L 0 _ eq_refl) ltac:(apply in_app_iff; right; exact Hbb) (nodup_app_ids (sb_blocks s S a) LBL _ bb ND (in_nth_error (sb_blocks s S a) 0 _ eq_refl) Hbb)) as AB; cbn [blk_addr blk_size fst snd] in AB; unfold SBSTATE_SIZEOF in AB; clear -AB; lia. }
{ intros bb Hbb; pose proof (DAP bb ltac:(apply in_app_iff; right; exact Hbb)) as QB; unfold apart in QB; clear -QB; lia. }
{ intros bb Hbb; pose proof (AP _ bb (in_nth_error L 1 _ eq_refl) ltac:(apply in_app_iff; right; exact Hbb) (nodup_app_ids (sb_blocks s S a) LBL _ bb ND (in_nth_error (sb_blocks s S a) 1 _ eq_refl) Hbb)) as AB; cbn [blk_addr blk_size fst snd] in AB; unfold SBSTATE_SIZEOF in AB; clear -AB; lia. }
{ intros bb Hbb; pose proof (AP _ bb (in_nth_error L 2 _ eq_refl) ltac:(apply in_app_iff; right; exact Hbb) (nodup_app_ids (sb_blocks s S a) LBL _ bb ND (in_nth_error (sb_blocks s S a) 2 _ eq_refl) Hbb)) as AB; cbn [blk_addr blk_size fst snd] in AB; unfold SBSTATE_SIZEOF in AB; clear -AB; lia. }
{ intros bb Hbb; pose proof (AP _ bb (in_nth_error L 3 _ eq_refl) ltac:(apply in_app_iff; right; exact Hbb) (nodup_app_ids (sb_blocks s S a) LBL _ bb ND (in_nth_error (sb_blocks s S a) 3 _ eq_refl) Hbb)) as AB; cbn [blk_addr blk_size fst snd] in AB; unfold SBSTATE_SIZEOF in AB; clear -AB; lia. }
{ intros bb Hbb; pose proof (AP _ bb (in_nth_error L 4 _ eq_refl) ltac:(apply in_app_iff; right; exact Hbb) (nodup_app_ids (sb_blocks s S a) LBL _ bb ND (in_nth_error (sb_blocks s S a) 4 _ eq_refl) Hbb)) as AB; cbn [blk_addr blk_size fst snd] in AB; unfold SBSTATE_SIZEOF in AB; clear -AB; lia. }
{ intros bb Hbb; pose proof (AP _ bb (in_nth_error L 5 _ eq_refl) ltac:(apply in_app_iff; right; exact Hbb) (nodup_app_ids (sb_blocks s S a) LBL _ bb ND (in_nth_error (sb_blocks s S a) 5 _ eq_refl) Hbb)) as AB; cbn [blk_addr blk_size fst snd] in AB; unfold SBSTATE_SIZEOF in AB; clear -AB; lia. }
{ intros bb Hbb; pose proof (AP _ bb (in_nth_error L 8 _ eq_refl) ltac:(apply in_app_iff; right; exact Hbb) (nodup_app_ids (sb_blocks s S a) LBL _ bb ND (in_nth_error (sb_blocks s S a) 8 _ eq_refl) Hbb)) as AB; cbn [blk_addr blk_size fst snd] in AB; unfold SBSTATE_SIZEOF in AB; clear -AB; lia. }
{ intros bb Hbb; pose proof (AP _ bb (in_nth_error L 6 _ eq_refl) ltac:(apply in_app_iff; right; exact Hbb) (nodup_app_ids (sb_blocks s S a) LBL _ bb ND (in_nth_error (sb_blocks s S a) 6 _ eq_refl) Hbb)) as AB; cbn [blk_addr blk_size fst snd] in AB; unfold SBSTATE_SIZEOF in AB; clear -AB; lia. }
{ intros bb Hbb; pose proof (AP _ bb (in_nth_error L 7 _ eq_refl) ltac:(apply in_app_iff; right; exact Hbb) (nodup_app_ids (sb_blocks s S a) LBL _ bb ND (in_nth_error (sb_blocks s S a) 7 _ eq_refl) Hbb)) as AB; cbn [blk_addr blk_size fst snd] in AB; unfold SBSTATE_SIZEOF in AB; clear -AB; lia. }
Qed.
End Layout.

Section ModelGlue.
Context {RCEIL : RunCeiling}.
Local Notation unpackM := (@bits_unpack_unsigned_M PState bptr).
Local Notation peekM := (@bits_peek_M PState bptr).
Local Notation advanceM := (@bits_advance_M PState bptr).
Local Notation remainingM := (@bits_remaining_M PState bptr).
Local Notation LD := (speex_decode io_notify unpackM peekM advanceM remainingM).

#[using="Type"] Lemma sb_decode_LD_ext : forall (s : sbd_state bptr) (low : dec_state bptr) LD1 LD2 b out (st : PState),
sbd_encode_submode s = 1 ->
(forall d b' o st', dec_depth d = dec_depth low -> LD1 d b' o st' = LD2 d b' o st') ->
sb_decode io_notify unpackM peekM remainingM s low LD1 b out st = sb_decode io_notify unpackM peekM remainingM s low LD2 b out st.
Proof.
intros s low LD1 LD2 b out st ES EXT.
rewrite !(sb_decode_unfold io_notify s low _ b out ES).
destruct (speex_decoder_ctl low (CtlSetInnovationSave (out + sbd_frame_size s))) as [u low1] eqn:EC.
unfold mbind at 1. unfold mbind at 2.
rewrite (EXT low1 b out st); [reflexivity|].
pose proof (ctl_keeps_depth low (CtlSetInnovationSave (out + sbd_frame_size s))) as DK. rewrite EC in DK. exact DK.
Qed.

#[using="Type"] Lemma speex_decode_SB : forall (s : sbd_state bptr) (low : dec_state bptr) b out (st : PState),
sbd_encode_submode s = 1 ->
LD (DecSB s low) b out st =
(mbind (sb_decode io_notify unpackM peekM remainingM s low LD b out)
(fun r => let '(r0, sl, b1) := r in let '(st', low') := sl in mret (r0, DecSB st' low', b1))) st.
Proof.
intros s low b out st ES. unfold speex_decode at 1. cbn [dec_depth speex_decode_n].
unfold mbind. rewrite (sb_decode_LD_ext s low (speex_decode_n io_notify unpackM peekM advanceM remainingM (dec_depth low)) LD b out st ES).
- reflexivity.
- intros d b' o st' E. unfold speex_decode. rewrite E. reflexivity.
Qed.
End ModelGlue.

Theorem sb_decode_ok {RCEIL : RunCeiling} : sb_decode_goal.
Proof.
intros k HY s low DK. unfold rdec_at.
intros ra sp gp tp t0 t1 t2 s0r s1r a0 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r s5r s6r s7r s8r s9r s10r s11r t3 t4 t5 t6 F fc m st OUT STEREO S LBD b BITS Dc lo outb stb canary.
intros DR D3 ISOK NEST ND AP RNG REP BOK OWN DRNG DAP XOU LOU OUT4 XS ST4 TP SE SS RLAY ST BUD SPX SP16 MI FRM -> -> ->.
cbn [decst_rep] in DR.
first [ sf_destruct 12%nat DR as a j LBL ELBD SAL POS INV JOK CELLS BUFS OUTL DRL | sf_fb; destruct DR as (a & j & LBL & ELBD & SAL & POS & INV & JOK & CELLS & BUFS & OUTL & DRL) ]. subst LBD.
destruct (u8arr_as_f32 _ OUT outb 2000%nat XOU ltac:(unfold HOUT_BYTES in LOU; lia)) as (ows & Lows & XO).
change (dec_depth (DecSB s low)) with (Datatypes.S (dec_depth low)) in D3.
change (rdec_depth (DecSB s low)) with (SB_LOCAL_DEPTH + rdec_depth low) in BUD.
change (dec_nested (DecSB s low)) with (dec_mode low = sbm_nb_mode (sbd_mode s) /\ dec_nested low) in NEST. destruct NEST as [NM NST].
set (X := SBI S OUT BITS Dc STEREO lo canary s a LBL b (rdec_depth low) (dec_depth low) st ra sp gp tp
s0r s1r s2r s3r s4r s5r s6r s7r s8r s9r s10r s11r F m).
destruct (proj1 REP) as (rj & Lrj & RA). pose proof (rw_cells_bound _ _ _ _ RA) as BA. rewrite (bits_cells_size _ _ _ Lrj) in BA. clear RA.
pose proof (rw_cells_bound _ _ _ _ XS) as BS. cbn [cells_size csize Nat.add] in BS.
pose proof (rw_cells_bound _ _ _ _ XO) as BO. rewrite cells_size_f32, Lows in BO.
assert (IHX : sb_ihyps k X).
{ unfold X; constructor; cbn [x_S x_out x_A x_D x_stereo x_lo x_canary x_s x_a x_LBL x_b0 x_RD x_dk x_st x_ra x_sp x_gp x_tp x_F x_m0].
- apply sb_layout_intro; assumption.
- unfold SB_LOCAL_DEPTH in *. lia.
- apply rdec_depth_nonneg.
- intros d E. apply rdec_depth_of_depth. exact E.
- split; [exact DK | lia].
- exact SPX.
- lia.
- exact SP16.
- exact SAL.
- exact OUT4.
- exact ST4.
- exact INV.
- cbn [isave_ok] in ISOK. destruct (sbd_innov_save s) as [kk|]; [| exact I].
pose proof INV as sfP_; first [ sf_destruct 5%nat sfP_ as Hmo E1 _ E3 _ | sf_fb; destruct sfP_ as (Hmo & E1 & _ & E3 & _) ]. rewrite ISOK, E1, E3. destruct Hmo as [-> | ->]; reflexivity.
- exact ND.
- exact AP.
- exact RNG.
- exact DRNG.
- exact DAP.
- exact RLAY.
- exact OWN.
- exact HY. }
assert (CTX0 : sbctx0 X OUTL m s low b j ows stb).
{ unfold X, sbctx0, sbWX; cbn [x_S x_out x_A x_D x_stereo x_lo x_canary x_s x_a x_LBL x_b0 x_RD x_dk x_st x_ra x_sp x_gp x_tp x_F x_m0].
split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
split; [apply (proj1 (sb_pieces_iff _ _ _ _ _ _)); exact CELLS|]. split; [exact JOK|]. split; [exact BUFS|]. split; [exact INV|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact DRL|]. split; [reflexivity|]. split; [exact I|]. split; [exact NM|]. split; [exact NST|].
split; [exact REP|]. split; [exact BOK|]. split; [unfold bits_keep; cbn; repeat split; reflexivity|].
split; [exact XO|]. split; [exact Lows|]. split; [exact XS|]. split; [exact TP|]. split; [exact SE| exact SS]. }
pose proof (sb_decode_main k X IHX OUTL low j ows stb t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc CTX0 ST FRM) as MAIN.
unfold X in MAIN. clear IHX CTX0. clearbody X. clear X.
cbn [x_S x_out x_A x_D x_stereo x_lo x_canary x_s x_a x_LBL x_b0 x_RD x_dk x_st x_ra x_sp x_gp x_tp x_F x_m0
x_s0 x_s1 x_s2 x_s3 x_s4 x_s5 x_s6 x_s7 x_s8 x_s9 x_s10 x_s11] in MAIN.
pose proof INV as sfP_; first [ sf_destruct 11%nat sfP_ as _ _ _ _ _ _ _ _ _ Ies _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ies & _) ].
eapply implM_eqM. { apply speex_decode_SB. exact Ies. }
eapply implM_bind. { exact MAIN. }
intros [[ret [s' low']] b'] st' ms' [-> HEND]. cbv beta.
apply implM_ret. apply evt_done.
first [ sf_destruct 12%nat HEND as Fx fc' m' kk j' ows' stb' -> FRM' CTX' ST' RET' | sf_fb; destruct HEND as (Fx & fc' & m' & kk & j' & ows' & stb' & -> & FRM' & CTX' & ST' & RET') ].
cbn [x_S x_out x_A x_D x_stereo x_lo x_canary x_s x_a x_LBL x_b0 x_RD x_dk x_st x_ra x_sp x_gp x_tp x_F x_m0
x_s0 x_s1 x_s2 x_s3 x_s4 x_s5 x_s6 x_s7 x_s8 x_s9 x_s10 x_s11] in FRM', CTX', ST', RET' |- *.
first [ sf_destruct 26%nat CTX' as MU WM MI' PCS JOK' BUF INV' Emo Efs Efr Eis Ebl DR' DD XR NM' NST' REP' BOK' (BKo & BKc & BSZ) XO' Lows' XS' TP' SE' SS' | sf_fb; destruct CTX' as (MU & WM & MI' & PCS & JOK' & BUF & INV' & Emo & Efs & Efr & Eis & Ebl & DR' & DD & XR & NM' & NST' & REP' & BOK' & (BKo & BKc & BSZ) & XO' & Lows' & XS' & TP' & SE' & SS') ].
unfold rdec_post.
first [ unshelve sf_eexists 17%nat; [ exact ((c_t0 kk)) | exact ((c_t1 kk)) | exact ((c_t2 kk)) | exact ((c_a1 kk)) | exact ((c_a2 kk)) | exact ((c_a3 kk)) | exact ((c_a4 kk)) | exact ((c_a5 kk)) | exact ((c_a6 kk)) | exact ((c_a7 kk)) | exact ((c_t3 kk)) | exact ((c_t4 kk)) | exact ((c_t5 kk)) | exact ((c_t6 kk)) | exact (Fx) | exact (fc') | exact (m') | ] | sf_fb; exists (c_t0 kk), (c_t1 kk), (c_t2 kk), (c_a1 kk), (c_a2 kk), (c_a3 kk), (c_a4 kk), (c_a5 kk), (c_a6 kk), (c_a7 kk), (c_t3 kk), (c_t4 kk), (c_t5 kk), (c_t6 kk), Fx, fc', m' ].
pose proof (f32_as_u8arr _ _ _ XO') as [XOU' LOU'].
exists (cells_bytes (f32 ows')), stb'.
split; [reflexivity|]. split; [exact RET'|].
split; [change (Datatypes.S (dec_depth low') = Datatypes.S (dec_depth low)); rewrite DD; reflexivity|].
split; [exact Emo|].
split; [change (dec_mode low' = sbm_nb_mode (sbd_mode s') /\ dec_nested low'); split; [rewrite Emo; exact NM'| exact NST']|].
split; [exact FRM'|].
split. { unfold sbWX in MU. cbn [x_S x_out x_A x_D x_stereo x_lo x_a x_LBL x_s x_sp x_m0] in MU.
unfold sbW. rewrite blocks_ivs_app, blocks_ivs_sb9. unfold SBSTATE_SIZEOF, BITS_SIZEOF, HOUT_BYTES in *. exact MU. }
split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
split. { cbn [decst_rep]. first [ unshelve sf_eexists 3%nat; [ exact (a) | exact (j') | exact (LBL) | ] | sf_fb; exists a, j', LBL ]. split; [rewrite Ebl; reflexivity|]. split; [exact SAL|]. split; [exact POS|].
split; [exact INV'|]. split; [exact JOK'|]. split; [apply (proj2 (sb_pieces_iff _ _ _ _ _ _)); exact PCS|].
split; [exact BUF|]. exists OUT. exact DR'. }
split; [exact I|].
split; [exact REP'|]. split; [exact BOK'|]. split; [exact BKo|]. split; [exact BKc|]. split; [exact BSZ|].
split; [exact XOU'|]. split; [rewrite LOU', Lows'; reflexivity|].
split; [exact XS'|]. split; [exact SE'|]. split; [exact SS'| reflexivity].
Qed.
