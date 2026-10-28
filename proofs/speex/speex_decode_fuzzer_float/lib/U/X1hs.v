(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1hn X1hw X1hz X1i0 X1i1 X1i2 X1ie X1i9 X1ia X1ib X1ic X1id X1ig.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Pure.
Context {RCEIL : RunCeiling}.
Context {St ptr : Type}.
Local Notation unpackM := (@bits_unpack_unsigned_M St ptr).
Implicit Types b : bits_st ptr.

Definition nb_rest (sm : submode) (st1 : nb_state ptr) b : M St (Z * nb_state ptr * bits_st ptr) :=
b <- lsp_unquant unpackM (sm_lsp_unquant sm) b ;;
' (ol_pitch, b0) <- (if negb (sm_lbr_pitch sm =? -1)
then ' (p, b0) <- unpackM b 7 ;; mret (NB_PITCH_START + p, b0)
else mret (0, b)) ;;
b1 <- (if negb (sm_forced_pitch_gain sm =? 0) then ' (_, b1) <- unpackM b0 4 ;; mret b1 else mret b0) ;;
' (_, b2) <- unpackM b1 5 ;;
' (st, b3) <- (if nb_submodeID st1 =? 1
then ' (extra, b3) <- unpackM b2 4 ;;
mret (set_nb_dtx_enabled st1 (if extra =? 15 then 1 else 0), b3)
else mret (st1, b2)) ;;
' (st0, b4) <- nb_decode_subframes unpackM 4 0 sm ol_pitch
(if 1 <? nb_submodeID st then set_nb_dtx_enabled st 0 else st) b3 ;;
mret (0, set_nb_pitch_gain_buf_idx (set_nb_count_lost (set_nb_first st0 0) 0)
(if 2 <? nb_pitch_gain_buf_idx st0 + 1 then 0 else nb_pitch_gain_buf_idx st0 + 1), b4).

Definition nb_rest_pure (sm : submode) (st1 : nb_state ptr) b : option (nb_state ptr * bits_st ptr) :=
let b1 := lsp_bits (sm_lsp_unquant sm) b in
match subframes_pure 4 0 sm (segD_olp sm b1) (segD_st st1 sm b1) (segD_bits st1 sm b1) with
| Some (st3, b3) => Some (nb_end st3, b3)
| None => None
end.

#[using="Type"] Lemma nb_rest_run : forall sm st1 b s,
sm_ltp_unquant sm <> None -> sm_innovation_unquant sm <> None ->
nb_rest sm st1 b s = match nb_rest_pure sm st1 b with
| Some (st', b') => Ret (Ok ((0, st', b'), s))
| None => Ret Unr
end.
Proof.
intros sm st1 b s HK HI. unfold nb_rest, nb_rest_pure.
unfold mbind at 1. rewrite lsp_unquant_run, ebind_ret_ok. cbn [fst snd].
set (b1 := lsp_bits (sm_lsp_unquant sm) b). clearbody b1.
unfold mbind at 1.
assert (H1 : (if negb (sm_lbr_pitch sm =? -1) then ' (p, b0) <- unpackM b1 7 ;; mret (NB_PITCH_START + p, b0) else mret (0, b1)) s
= Ret (Ok ((segD_olp sm b1, segD_b1 sm b1), s))).
{ unfold segD_olp, segD_b1. destruct (negb (sm_lbr_pitch sm =? -1)); [| reflexivity].
unfold bits_unpack_unsigned_M, mbind, mret. rewrite unpack_eta, ebind_ret_ok. cbn [fst snd].
rewrite (Z.add_comm NB_PITCH_START). reflexivity. }
rewrite H1, ebind_ret_ok. cbn [fst snd]. clear H1.
unfold mbind at 1.
assert (H2 : (if negb (sm_forced_pitch_gain sm =? 0) then ' (_, b0) <- unpackM (segD_b1 sm b1) 4 ;; mret b0 else mret (segD_b1 sm b1)) s
= Ret (Ok (segD_b2 sm b1, s))).
{ unfold segD_b2. destruct (negb (sm_forced_pitch_gain sm =? 0)); [| reflexivity].
unfold bits_unpack_unsigned_M, mbind, mret. rewrite unpack_eta, ebind_ret_ok. reflexivity. }
rewrite H2, ebind_ret_ok. clear H2.
unfold mbind at 1. unfold bits_unpack_unsigned_M at 1. unfold mret at 1. rewrite unpack_eta, ebind_ret_ok. cbn [fst snd].
fold (segD_b3 sm b1).
unfold mbind at 1.
assert (H3 : (if nb_submodeID st1 =? 1
then ' (extra, b3) <- unpackM (segD_b3 sm b1) 4 ;; mret (set_nb_dtx_enabled st1 (if extra =? 15 then 1 else 0), b3)
else mret (st1, segD_b3 sm b1)) s
= Ret (Ok ((if nb_submodeID st1 =? 1 then (set_nb_dtx_enabled st1 (if uv (segD_b3 sm b1) 4 =? 15 then 1 else 0), ub (segD_b3 sm b1) 4)
else (st1, segD_b3 sm b1)), s))).
{ destruct (nb_submodeID st1 =? 1); [| reflexivity].
unfold bits_unpack_unsigned_M, mbind, mret. rewrite unpack_eta, ebind_ret_ok. reflexivity. }
rewrite H3, ebind_ret_ok. clear H3.
unfold segD_st, segD_bits.
destruct (Z.eqb_spec (nb_submodeID st1) 1) as [E1|E1]; cbn [fst snd].
1: replace (1 <? nb_submodeID (set_nb_dtx_enabled st1 (if uv (segD_b3 sm b1) 4 =? 15 then 1 else 0))) with false
by (symmetry; apply Z.ltb_ge; destruct st1; cbn in E1 |- *; lia).
all: unfold mbind at 1; rewrite nb_decode_subframes_run by assumption.
all: destruct (subframes_pure 4 0 sm _ _ _) as [[st3 b3]|]; rewrite ?ebind_ret_ok, ?ebind_ret_unr; reflexivity.
Qed.
End Pure.

Section Main.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Variable notify : list Z -> X1qx.M PState unit.
Variable STR_TOP : Z.
Variable X : nbinv ptr.
Hypothesis NH : nb_hyps notify STR_TOP X.
Local Notation ST := (x_st X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation ISV := (x_isv X). Local Notation lo := (x_lo X).
Local Notation st0 := (x_st0 X). Local Notation b0 := (x_b0 X).
Local Notation sp := (x_sp X). Local Notation gp := (x_gp X). Local Notation tp := (x_tp X). Local Notation ra0 := (x_ra X).
Local Notation cs0 := (x_s0 X). Local Notation cs1 := (x_s1 X). Local Notation cs2 := (x_s2 X). Local Notation cs3 := (x_s3 X).
Local Notation cs4 := (x_s4 X). Local Notation cs5 := (x_s5 X). Local Notation cs6 := (x_s6 X). Local Notation cs7 := (x_s7 X).
Local Notation cs8 := (x_s8 X). Local Notation cs9 := (x_s9 X). Local Notation cs10 := (x_s10 X). Local Notation cs11 := (x_s11 X).
Local Notation F0 := (x_F X). Local Notation m0 := (x_m0 X). Local Notation canary := (x_canary X).
Local Notation usp := (bv_unsigned (x_sp X)).
Local Notation NBP := (nb_pieces rsegs NB_MODE_PTR NB_SUBMODES_PTR A_speex_default_user_handler).
Local Notation unpackM := (@bits_unpack_unsigned_M PState ptr).
Local Notation advanceM := (@bits_advance_M PState ptr).
Local Notation remainingM := (@bits_remaining_M PState ptr).
Local Notation POST s := (nb_decode_post (x_serr X) (x_sspc X) ST OUT A D STEREO ISV lo canary ra0 sp gp tp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 F0 m0 s).

Let HSEG_E : forall r mo olp st b ms, at_E X r mo olp 40 0 st b ms ->
match subframes_pure 4 0 (smr_sm r) olp st b with
| Some (st', b') => evt rsegs (fun ms' => exists bp, at_F X r mo olp bp st' b' ms') ms
| None => True
end := nbE notify STR_TOP X NH.
Let HSEG_N : forall b ms, at_N X b ms -> evt rsegs (at_X X 0 (nb_null (set_nb_submodeID st0 0)) b) ms := nbN notify STR_TOP X NH.
Let HSEG_F : forall r mo olp bp st b ms, at_F X r mo olp bp st b ms -> evt rsegs (at_G X 0 st b) ms := nbF notify STR_TOP X NH.
Let HSEG_G : forall st b ms, at_G X 0 st b ms -> evt rsegs (at_H X st b) ms := nbG notify STR_TOP X NH.
Let HSEG_H : forall st b ms, at_H X st b ms -> evt rsegs (at_X X 0 (nb_end st) b) ms := nbH notify STR_TOP X NH.
Let HSEG_X : forall rr st b s ms, at_X X rr st b ms -> evt rsegs (POST s (rr, st, b) s) ms := nbX notify STR_TOP X NH.

#[using="Type"] Lemma smrec_unq : forall r, In r nb_smrecs ->
sm_ltp_unquant (smr_sm r) <> None /\ sm_innovation_unquant (smr_sm r) <> None.
Proof.
intros r H. cbn [nb_smrecs In] in H.
repeat (destruct H as [<- | H]; [split; cbv; discriminate|]). contradiction.
Qed.

#[using="Type"] Lemma at_B_mo : forall mo b ms, at_B X mo b ms -> 0 <= mo <= 8.
Proof.
intros mo b ms AT.
first [ sf_destruct 33%nat AT as Fx fc m k xra xa0 xs0 xs1 xs2 xs4 xs5 xs6 xs7 xs8 xs10 xs11 j ows iws sws fr _ _ _ _ _ _ _ _ _ _ Hmo _ | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & xs0 & xs1 & xs2 & xs4 & xs5 & xs6 & xs7 & xs8 & xs10 & xs11 & j & ows & iws & sws & fr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmo & _) ].
exact Hmo.
Qed.

#[using="STR_TOP NH HSEG_E HSEG_N HSEG_F HSEG_G HSEG_H HSEG_X"] Theorem nb_decode_main : forall (s : PState) (j : nb_junk) (ows iws sws : list word) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32),
NBP m0 ST OUT STEREO st0 j -> nb_junk_ok j -> cbs_ok A_speex_std_stereo_request_handler STEREO (nb_stereo_cb st0) (j_cbs j) ->
bits_rep rsegs m0 A D b0 -> bits_ok b0 ->
rw_cells rsegs m0 OUT (f32 ows) -> length ows = 160%nat ->
rw_cells rsegs m0 ISV (f32 iws) -> length iws = 160%nat ->
rw_cells rsegs m0 STEREO (f32 sws) -> length sws = 2%nat ->
stk rsegs m0 lo usp -> mem_inv rsegs m0 -> frm0 fc ->
implM rsegs (nb_decode notify unpackM advanceM remainingM st0 b0) s (POST s)
(MS (mkR ra0 sp gp tp t0 t1 t2 cs0 cs1 (Z_to_bv 64 ST) (Z_to_bv 64 A) (Z_to_bv 64 OUT) a3 a4 a5 a6 a7 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3 t4 t5 t6)
F0 (Z_to_bv 64 A_nb_decode) fc None m0 (seg_rom rsegs)).
Proof.
intros s j ows iws sws t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc PCS JOK CBS REP BOK XO Lows XI Liws XS Lsws STK MI FRM.
pose proof (h_inv0 _ _ _ NH) as INV0. pose proof INV0 as (_ & Ies & _).
unfold nb_decode. rewrite Ies. cbn [Z.eqb negb].
eapply (implM_bind rsegs).
{ eapply (nbA_entry notify STR_TOP X NH); eassumption. }
intros sr s' ms' [-> HQ]. destruct sr as [rr b | mo b].
-
cbn in HQ. apply implM_ret. apply HSEG_X. exact HQ.
-
cbn [nb_submodeID set_nb_submodeID] in HQ |- *. cbv zeta.
pose proof (at_B_mo _ _ _ HQ) as Hmo.
pose proof (nbB notify STR_TOP X NH mo b ms' HQ) as EB. unfold QB in EB.
destruct (smrec_cases mo Hmo) as [(-> & _ & SAT & SMN) | (r & SAT & INr & _ & _ & SMS & LORD)].
+
rewrite SAT in EB. cbn [nb_submodeID set_nb_submodeID submode_at Z.ltb Z.to_nat nth nb_submodes].
apply implM_ret. eapply evt_cut; [exact EB|]. intros ms2 HN2.
eapply evt_cut; [apply HSEG_N; exact HN2|]. intros ms3 HX3. apply HSEG_X. exact HX3.
+ rewrite SAT in EB. cbn [nb_submodeID set_nb_submodeID]. rewrite SMS.
change (implM rsegs (nb_rest (smr_sm r) (set_nb_submodeID st0 mo) b) s (POST s) ms').
destruct (smrec_unq r INr) as [HK HI].
unfold implM. rewrite (nb_rest_run (smr_sm r) (set_nb_submodeID st0 mo) b s HK HI).
destruct (nb_rest_pure (smr_sm r) (set_nb_submodeID st0 mo) b) as [[st' b']|] eqn:ER; [| apply impl_ret_unr].
apply impl_ret_ok. cbn [epost fst snd].
unfold nb_rest_pure in ER. cbv zeta in ER.
destruct (subframes_pure 4 0 (smr_sm r) _ _ _) as [[st3 b3]|] eqn:ES; [| discriminate].
injection ER as <- <-.
eapply evt_cut; [exact EB|]. intros ms2 HC.
eapply evt_cut; [exact (nbC notify STR_TOP X NH _ _ _ _ HC)|]. intros ms3 HD1.
eapply evt_cut; [exact (nbD1 notify STR_TOP X NH _ _ _ _ HD1)|]. intros ms4 HD2.
eapply evt_cut; [exact (nbD2 notify STR_TOP X NH _ _ _ _ _ _ HD2)|]. intros ms5 HE.
pose proof (HSEG_E _ _ _ _ _ _ HE) as EE. rewrite ES in EE.
eapply evt_cut; [exact EE|]. intros ms6 [bp HF].
eapply evt_cut; [exact (HSEG_F _ _ _ _ _ _ _ HF)|]. intros ms7 HG.
eapply evt_cut; [exact (HSEG_G _ _ _ HG)|]. intros ms8 HH.
eapply evt_cut; [exact (HSEG_H _ _ _ HH)|]. intros ms9 HX. apply HSEG_X. exact HX.
Qed.
End Main.
