(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma X1mw X1mo.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1g6 X1g4 X1g7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
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
Local Notation unpackM := (@bits_unpack_unsigned_M PState bptr).
Local Notation peekM := (@bits_peek_M PState bptr).
Local Notation advanceM := (@bits_advance_M PState bptr).
Local Notation remainingM := (@bits_remaining_M PState bptr).
Local Notation HN := (h_notify _ (ih_hyps _ _ IH)).


Lemma subp_ok : forall mo', (mo' = ModeWB \/ mo' = ModeUWB) -> 0 < SUBP mo' < 2^62 /\ SUBP mo' mod 8 = 0.
Proof. intros mo' [-> | ->]; vm_compute; repeat split; reflexivity. Qed.

Definition at_M (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xa0 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe),
ms = MS (mkR xra (Z_to_bv 64 (usp + -384)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
xa0 (Z_to_bv 64 OUT) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
(Z_to_bv 64 OUT) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 A)
(Z_to_bv 64 (sbmode_struct mo)) cs8 cs9 cs10 cs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2ef94) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -384) /\ frame_at X m fr /\ f_0 fr = Z_to_bv 64 0
/\ f_16 fr = Z_to_bv 64 (sbmode_struct mo) /\ f_128 fr = Z_to_bv 64 OUT /\ f_160 fr = Z_to_bv 64 A /\ f_184 fr = Z_to_bv 64 0
/\ f_208 fr = Z_to_bv 64 1
/\ f_dtx fr = Z_to_bv 64 dtx /\ (dtx = 0 \/ dtx = 1).

Definition QW (low : dec_state bptr) (dtx : Z) (sr : (sbd_state bptr * bits_st bptr) + (sbd_state bptr * bits_st bptr)) : machine_state -> Prop :=
match sr with
| inr (s1, b1) => at_X X (-2) s1 low b1
| inl (s1, b1) => at_M low dtx s1 b1
end.

Definition at_W0 (low : dec_state bptr) (dtx : Z) (b b1 : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xa0 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe),
ms = MS (mkR xra (Z_to_bv 64 (usp + -384)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
xa0 (c_a1 kk) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
(Z_to_bv 64 OUT) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 A)
(Z_to_bv 64 (sbmode_struct mo)) cs8 cs9 cs10 cs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2ef8c) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s0 low b1 j ows stb /\ stk rsegs m lo (usp + -384) /\ frame_at X m fr /\ f_0 fr = Z_to_bv 64 0
/\ f_16 fr = Z_to_bv 64 (sbmode_struct mo) /\ f_128 fr = Z_to_bv 64 OUT /\ f_160 fr = Z_to_bv 64 A /\ f_184 fr = Z_to_bv 64 0
/\ f_208 fr = Z_to_bv 64 1
/\ f_dtx fr = Z_to_bv 64 dtx /\ (dtx = 0 \/ dtx = 1)
/\ sbw_id b = 0 /\ sbw_bits b = b1.

#[using="RCEIL k IH"] Lemma sbW0 : forall low dtx b b1 ms, at_W0 low dtx b b1 ms ->
evt rsegs (fun ms' => implM rsegs (sbw_M io_notify s0 b) st (fun sr st' ms'' => st' = st /\ QW low dtx sr ms'') ms') ms.
Proof.
intros low dtx b b1 ms AT.
first [ sf_destruct 25%nat AT as Fx fc m kk xra xa0 j ows stb fr -> FRM CTX ST FRA F0eq F16 F128 F160 F184 F208 Fdtx DTX01 ID0 EB1 | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & j & ows & stb & fr & -> & FRM & CTX & ST & FRA & F0eq & F16 & F128 & F160 & F184 & F208 & Fdtx & DTX01 & ID0 & EB1) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV. rewrite F128 in FL.
zgo 0x2ef94.
apply evt_done. unfold implM. rewrite sbw_M_run. cbv zeta. rewrite ID0, EB1. cbn [Z.eqb negb andb].
apply impl_ret_ok. cbn [epost fst snd]. apply evt_done. split; [reflexivity|]. unfold QW, at_M.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctx MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
feqs. exact DTX01.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

#[using="RCEIL k IH"] Lemma sbW : forall low dtx b ms, at_W X low dtx b ms ->
implM rsegs (sbw_M io_notify s0 b) st (fun sr st' ms' => st' = st /\ QW low dtx sr ms') ms.
Proof.
intros low dtx b ms AT.
first [ sf_destruct 23%nat AT as Fx fc m kk xra xa0 j ows stb fr -> FRM CTX ST FRA F0eq F16 F128 F160 F184 F208 Fdtx DTX01 | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & j & ows & stb & fr & -> & FRM & CTX & ST & FRA & F0eq & F16 & F128 & F160 & F184 & F208 & Fdtx & DTX01) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV. rewrite F128 in FL.
open_bits REP BOK.
apply implM_from_evt.

zstep. zstep. call (X1g6.speex_bits_remaining_spec A D b); [exact REP | exact BOK | exact MI |].
after_bits REP b. match goal with H : ?v = Z_to_bv 64 (speex_bits_remaining b) |- _ => subst v end.

zstep. rewrite (lts_zero_lit (speex_bits_remaining b)) by lia.
if_cases Krem; zify_bool Krem.
{
apply sbW0 with (b1 := b). unfold at_W0.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctx MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
feqs.
unfold sbw_id, sbw_bits, sbw_wb. replace (0 <? speex_bits_remaining b) with false by (symmetry; apply Z.ltb_ge; lia). split; reflexivity. }

zstep. zstep. call (X1g4.speex_bits_peek_spec A D b); [exact REP | exact BOK | exact MI |].
destruct (speex_bits_peek b) as [wbv bp] eqn:EPK. cbn [fst snd] in *.
pose proof (speex_bits_peek_ok b wbv bp BOK EPK) as (BOKp & WBV & _).
pose proof (peek_same b) as PS3. rewrite EPK in PS3. cbn [snd] in PS3. destruct PS3 as (PSsz & PSo & PSc).
after_bits REP bp. match goal with H : ?v = Z_to_bv 64 wbv |- _ => subst v end.
assert (SWB : sbw_wb b = (wbv, bp)).
{ unfold sbw_wb. replace (0 <? speex_bits_remaining b) with true by (symmetry; apply Z.ltb_lt; lia). exact EPK. }

zstep. rewrite (eqb_zero_lit wbv) by lia. if_cases Kwb; zify_bool Kwb.
{
apply sbW0 with (b1 := bp). unfold at_W0.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctx MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
feqs.
unfold sbw_id, sbw_bits. rewrite SWB, Kwb. split; reflexivity. }

zstep. zstep. zstep.
call (X1g7.speex_bits_unpack_unsigned_spec A D bp 1); [exact REP | exact BOKp | lia | exact MI |].
rewrite (unpack_eta bp 1) in *. cbn [fst snd] in *. after_bits REP (ub bp 1).
pose proof (ub_ok bp 1 BOKp ltac:(lia)) as BOK1. pose proof (ub_same bp 1) as (U1sz & U1o & U1c).
zstep. zstep. zstep.
call (X1g7.speex_bits_unpack_unsigned_spec A D (ub bp 1) 3); [exact REP | exact BOK1 | lia | exact MI |].
rewrite (unpack_eta (ub bp 1) 3) in *. cbn [fst snd] in *. after_bits REP (ub (ub bp 1) 3).
match goal with H : ?v = Z_to_bv 64 (uv (ub bp 1) 3) |- _ => subst v end.
pose proof (ub_ok (ub bp 1) 3 BOK1 ltac:(lia)) as BOK3. pose proof (ub_same (ub bp 1) 3) as (U3sz & U3o & U3c).
pose proof (speex_bits_unpack_unsigned_ok (ub bp 1) 3 _ _ BOK1 ltac:(lia) (unpack_eta (ub bp 1) 3)) as (_ & ID8 & _).
set (id := uv (ub bp 1) 3) in *. set (b3 := ub (ub bp 1) 3) in *.
assert (Kwbf : (wbv =? 0) = false) by (apply Z.eqb_neq; exact Kwb).
assert (SID : sbw_id b = id) by (unfold sbw_id; rewrite SWB, Kwbf; reflexivity).
assert (SBI : sbw_bits b = b3) by (unfold sbw_bits; rewrite SWB, Kwbf; reflexivity).

zgo 0x2ef14. zstep. rewrite (eqb_zero_lit id) by lia. if_cases Kid; zify_bool Kid.
{
apply evt_done. unfold implM. rewrite sbw_M_run. cbv zeta. rewrite SID, SBI, Kid. cbn [Z.eqb negb andb].
apply impl_ret_ok. cbn [epost fst snd]. apply evt_done. split; [reflexivity|]. unfold QW, at_M.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [rewrite <- Kid; reflexivity|]. split; [exact FRM|].
split. { rewrite <- Kid. close_ctx MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
feqs. exact DTX01. }

pose proof INV0 as (Imo & _). pose proof (subp_ok mo Imo) as (SPr & SPal).
zgo 0x2ef24. rewrite (Z.shiftl_mul_pow2 id 3) by lia. change (2 ^ 3) with 8.
zgo 0x2ef28. replace (SUBP mo + id * 8) with (SUBP mo + 8 * id) in * by lia.
zgo 0x2ef48.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (sb_sub_ptr_read mm mo id _ (sb_tables_of_pristine mm TP) Imo ltac:(lia) eq_refl) as RD end.
zstep. clear RD.

destruct (sb_smrec_cases mo id Imo ltac:(lia)) as [(SP0 & SAT & SMN) | (r & SAT & INr & SPE & SPnz & SMS & _)].
-
rewrite SP0. zstep. if_false.
pose proof (sb_tables_of_pristine _ TP) as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ _ _ TG TS _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & TG & TS & _) ]. unfold NB_GOT_STDERR, NB_STDERR_VAR, NB_RSTDERR in TG, TS.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
clear TG TS. apply evt_done.
eapply implM_eqM with (c' := (io_notify MSG_INVALID_MODE ;;; mret (inr (set_sbd_submodeID s0 id, b3)))).
{ rewrite sbw_M_run. cbv zeta. rewrite SID, SBI.
replace (sbd_mode (set_sbd_submodeID s0 id)) with mo by (destruct (x_s X); reflexivity).
rewrite SMN. replace (id =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
eapply implM_bind.
{ eapply HN with (lo := lo); try reflexivity.
- apply cstr_invalid_mode; [exact MI| unfold NB_GLOBALS_TOP; lia| unfold SB_STR_TOP; lia].
- exact SE.
- rewrite USP384. exact ST.
- rewrite USP384. unfold NB_FPRINTF_DEPTH. lia.
- unfold NB_GLOBALS_TOP. lia.
- rewrite USP384. lia.
- exact SS.
- exact MI.
- exact FRM. }
cbv beta. intros [] st2 ms2 PN.
first [ sf_destruct 28%nat PN as y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 Ft fc2 m2 -> MUn WMn MI2 FRM2 _ ST2 SE2 SS2 -> | sf_fb; destruct PN as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & Ft & fc2 & m2 & -> & MUn & WMn & MI2 & FRM2 & _ & ST2 & SE2 & SS2 & ->) ].
rewrite USP384 in MUn, ST2. unfold NB_RSTDERR in MUn.
clear SE SS ST.
lazymatch type of MUn with munch _ ?m1 _ => transport_after_call rsegs m1 m2 MUn WMn end.
clear MUn WMn. try clear MI. rename MI2 into MI.
replace (ret_pc (Z_to_bv 64 0x2ef70)) with (Z_to_bv 64 0x2ef70) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
apply implM_from_evt. zstep. zstep. apply evt_done.
apply implM_ret. apply evt_done. split; [reflexivity|]. unfold QW, at_X.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _). sf_eexists 13%nat. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM2|].
split. { close_ctx MU. }
split; [exact ST2|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|]. lia.
-
rewrite SPE. zstep.
pose proof (sb_smrecs_ptr r INr) as (RLO & RHI & _). unfold RTABLES_LO, RTABLES_HI in RLO, RHI.
rewrite (eqb_zero_lit (smr_ptr r)) by lia. replace (smr_ptr r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
apply evt_done. unfold implM. rewrite sbw_M_run. cbv zeta. rewrite SID, SBI. cbn [sbd_mode set_sbd_submodeID].
replace (sbd_mode (set_sbd_submodeID s0 id)) with mo by (destruct (x_s X); reflexivity).
rewrite SMS. replace (negb (id =? 0) && false) with false by (destruct (id =? 0); reflexivity).
apply impl_ret_ok. cbn [epost fst snd]. apply evt_done. split; [reflexivity|]. unfold QW, at_M.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctx MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
feqs. exact DTX01.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Definition at_N (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe),
ms = MS (mkR xra (Z_to_bv 64 (usp + -384)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
(Z_to_bv 64 0) (Z_to_bv 64 OUT) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
(Z_to_bv 64 OUT) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 A)
(Z_to_bv 64 (sbmode_struct mo)) cs8 cs9 cs10 cs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2fa78) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -384) /\ frame_at X m fr /\ f_0 fr = Z_to_bv 64 0
/\ f_16 fr = Z_to_bv 64 (sbmode_struct mo) /\ f_128 fr = Z_to_bv 64 OUT /\ f_160 fr = Z_to_bv 64 A /\ f_184 fr = Z_to_bv 64 0
/\ f_208 fr = Z_to_bv 64 1
/\ f_dtx fr = Z_to_bv 64 dtx /\ (dtx = 0 \/ dtx = 1)
/\ submode_at (sbm_submodes mo) (sbd_submodeID s1) = None.

Definition at_V (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (b : bits_st bptr) (r : smrec) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe),
ms = MS (mkR xra (Z_to_bv 64 (usp + -384)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
(Z_to_bv 64 (smr_ptr r)) (c_a1 kk) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
(Z_to_bv 64 OUT) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 A)
(Z_to_bv 64 (sbmode_struct mo)) cs8 cs9 cs10 cs11 (c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2efd8) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -384) /\ frame_at X m fr /\ f_0 fr = Z_to_bv 64 0
/\ f_16 fr = Z_to_bv 64 (sbmode_struct mo) /\ f_128 fr = Z_to_bv 64 OUT /\ f_160 fr = Z_to_bv 64 A /\ f_184 fr = Z_to_bv 64 0
/\ f_208 fr = Z_to_bv 64 1
/\ f_dtx fr = Z_to_bv 64 dtx /\ (dtx = 0 \/ dtx = 1)
/\ sb_smrec_at mo (sbd_submodeID s1) = Some r.

Definition QM (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (b : bits_st bptr) : machine_state -> Prop :=
match sb_smrec_at mo (sbd_submodeID s1) with
| None => at_N low dtx s1 b
| Some r => at_V low dtx s1 b r
end.

#[using="RCEIL k IH"] Lemma sbM : forall low dtx s1 b ms, at_M low dtx s1 b ms -> evt rsegs (QM low dtx s1 b) ms.
Proof.
intros low dtx s1 b ms AT.
first [ sf_destruct 23%nat AT as Fx fc m kk xra xa0 j ows stb fr -> FRM CTX ST FRA F0eq F16 F128 F160 F184 F208 Fdtx DTX01 | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & j & ows & stb & fr & -> & FRM & CTX & ST & FRA & F0eq & F16 & F128 & F160 & F184 & F208 & Fdtx & DTX01) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV0 as (Imo & _). pose proof INV as sfP_; first [ sf_destruct 12%nat sfP_ as _ _ _ _ _ _ _ _ _ _ Iid _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Iid & _) ].
pose proof (subp_ok mo Imo) as (SPr & SPal).
set (id := sbd_submodeID s1) in *.

zgo 0x2ef9c. rewrite (sx32_lit id) by lia. rewrite Emo.
zgo 0x2efa0. rewrite (Z.shiftl_mul_pow2 id 3) by lia. change (2 ^ 3) with 8.
zgo 0x2efa4. replace (SUBP mo + id * 8) with (SUBP mo + 8 * id) in * by lia.
zgo 0x2efd0.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (sb_sub_ptr_read mm mo id _ (sb_tables_of_pristine mm TP) Imo ltac:(lia) eq_refl) as RD end.
zstep. clear RD.

unfold QM. destruct (sb_smrec_cases mo id Imo ltac:(lia)) as [(SP0 & SAT & SMN) | (r & SAT & INr & SPE & SPnz & SMS & _)].
- rewrite SP0. zstep. if_true. rewrite SAT.
apply evt_done. unfold at_N.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctx MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
feqs. exact SMN.
- rewrite SPE. zstep.
pose proof (sb_smrecs_ptr r INr) as (RLO & RHI & _). unfold RTABLES_LO, RTABLES_HI in RLO, RHI.
rewrite (eqb_zero_lit (smr_ptr r)) by lia. replace (smr_ptr r =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
rewrite SAT. apply evt_done. unfold at_V.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _. first [ unshelve sf_eexists 3%nat; [ exact (j) | exact (ows) | exact (stb) | ] | sf_fb; exists j, ows, stb ]. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctx MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
feqs. exact SAT.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.
End Seg.
