(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.

Lemma implM_from_evt : forall {Y} (c : M PState Y) s Q ms,
evt rsegs (fun ms' => implM rsegs c s Q ms') ms -> implM rsegs c s Q ms.
Proof. intros Y c s Q ms H. unfold implM in *. eapply impl_evt; [exact H|]. intros ms' H'; exact H'. Qed.

Lemma remaining_range : forall {ptr} (bb : bits_st ptr), bits_ok bb -> -1 <= speex_bits_remaining bb <= sb_nbBits bb.
Proof.
intros ptr bb OK. unfold speex_bits_remaining. unfold bits_ok, bits_pos in OK.
destruct (negb (sb_overflow bb =? 0)); unfold bits_pos; lia.
Qed.

Lemma nb_inv_set_submodeID : forall {ptr} (st : nb_state ptr) mo, nb_inv st -> 0 <= mo <= 8 -> nb_inv (set_nb_submodeID st mo).
Proof. intros ptr st mo H Hm. unfold nb_inv in *. destruct st; cbn in *. destruct nb_innov_save; lia. Qed.

Lemma nb_inv_set_dtx : forall {ptr} (st : nb_state ptr) v, nb_inv st -> (v = 0 \/ v = 1) -> nb_inv (set_nb_dtx_enabled st v).
Proof. intros ptr st v H Hv. unfold nb_inv in *. destruct st; cbn in *. destruct nb_innov_save; lia. Qed.
Lemma nb_inv_set_voc : forall {ptr} (st : nb_state ptr) v, nb_inv st -> 0 <= v <= 143 -> nb_inv (set_nb_voc_offset st v).
Proof. intros ptr st v H Hv. unfold nb_inv in *. destruct st; cbn in *. destruct nb_innov_save; lia. Qed.
Lemma nb_inv_set_first : forall {ptr} (st : nb_state ptr) v, nb_inv st -> (v = 0 \/ v = 1) -> nb_inv (set_nb_first st v).
Proof. intros ptr st v H Hv. unfold nb_inv in *. destruct st; cbn in *. destruct nb_innov_save; lia. Qed.
Lemma nb_inv_set_count_lost : forall {ptr} (st : nb_state ptr), nb_inv st -> nb_inv (set_nb_count_lost st 0).
Proof. intros ptr st H. unfold nb_inv in *. destruct st; cbn in *. destruct nb_innov_save; lia. Qed.
Lemma nb_inv_set_idx : forall {ptr} (st : nb_state ptr) v, nb_inv st -> 0 <= v <= 2 -> nb_inv (set_nb_pitch_gain_buf_idx st v).
Proof. intros ptr st v H Hv. unfold nb_inv in *. destruct st; cbn in *. destruct nb_innov_save; lia. Qed.

Ltac close_inv :=
first [ assumption |
lazymatch goal with
| |- nb_inv (set_nb_submodeID _ _) => apply nb_inv_set_submodeID; [close_inv | lia]
| |- nb_inv (set_nb_dtx_enabled _ _) => apply nb_inv_set_dtx; [close_inv | first [lia | destruct (_ =? _); lia] ]
| |- nb_inv (set_nb_voc_offset _ _) => apply nb_inv_set_voc; [close_inv | lia]
| |- nb_inv (set_nb_first _ _) => apply nb_inv_set_first; [close_inv | lia]
| |- nb_inv (set_nb_count_lost _ 0) => apply nb_inv_set_count_lost; close_inv
| |- nb_inv (set_nb_pitch_gain_buf_idx _ _) => apply nb_inv_set_idx; [close_inv | lia]
| |- nb_inv (if ?c then _ else _) =>
first [ let c' := eval vm_compute in c in change c with c'; cbv iota | destruct c ]; close_inv
end ].

Lemma cbs_cells_wf : forall k sf sd bb js, Forall (fun p => length (fst p) = 8%nat /\ length (snd p) = 16%nat) js ->
cells_wf (cbs_cells k sf sd bb js).
Proof.
induction k as [|k IH]; intros sf sd bb js F; [exact I|].
destruct js as [|j0 js]; [exact I|]. cbn [cbs_cells]. cbv zeta. inversion F; subst.
apply cells_wf_app. split; [| apply IH; assumption].
destruct H1 as [L1 L2]. destruct (_ && _); cbn; repeat split; assumption.
Qed.

Lemma msg_invalid_mode_at : forall m, mem_inv rsegs m ->
bytes_at rsegs m A_MSG_INVALID_MODE (nb_zb MSG_INVALID_MODE ++ Z_to_bv 8 0 :: [Z_to_bv 8 0x2d]).
Proof.
intros m MI.
pose proof (ro_cells_image rsegs m A_MSG_INVALID_MODE (nb_zb MSG_INVALID_MODE ++ Z_to_bv 8 0 :: [Z_to_bv 8 0x2d]) MI
ltac:(vm_compute; reflexivity) ltac:(unfold A_MSG_INVALID_MODE; lia) ltac:(unfold A_MSG_INVALID_MODE; cbn; lia)) as RO.
destruct RO as [_ HB]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
Qed.
Lemma msg_more_than_two_at : forall m, mem_inv rsegs m ->
bytes_at rsegs m A_MSG_MORE_THAN_TWO_WB (nb_zb MSG_MORE_THAN_TWO_WB ++ Z_to_bv 8 0 :: [Z_to_bv 8 0x49]).
Proof.
intros m MI.
pose proof (ro_cells_image rsegs m A_MSG_MORE_THAN_TWO_WB (nb_zb MSG_MORE_THAN_TWO_WB ++ Z_to_bv 8 0 :: [Z_to_bv 8 0x49]) MI
ltac:(vm_compute; reflexivity) ltac:(unfold A_MSG_MORE_THAN_TWO_WB; lia) ltac:(unfold A_MSG_MORE_THAN_TWO_WB; cbn; lia)) as RO.
destruct RO as [_ HB]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB. exact HB.
Qed.
Lemma cstr_invalid_mode : forall STR_TOP m lo' sp', mem_inv rsegs m -> NB_GLOBALS_TOP <= lo' -> 0x104d0 <= STR_TOP ->
nb_cstr_arg STR_TOP m (Z_to_bv 64 A_MSG_INVALID_MODE) MSG_INVALID_MODE lo' sp'.
Proof.
intros STR_TOP m lo' sp' MI GL ST. unfold nb_cstr_arg. exists [Z_to_bv 8 0x2d].
unfold A_MSG_INVALID_MODE. rewrite unsigned_lit by lia.
split; [apply msg_invalid_mode_at; exact MI|].
split; [unfold MSG_INVALID_MODE; cbn; repeat constructor; lia|].
replace (zlength MSG_INVALID_MODE) with 50 by (vm_compute; reflexivity).
replace (zlength [Z_to_bv 8 45]) with 1 by (vm_compute; reflexivity).
change ((- (66444 + 50 + 1)) mod 8) with 1.
unfold NB_GLOBALS_TOP in *. lia.
Qed.
Lemma cstr_more_than_two : forall STR_TOP m lo' sp', mem_inv rsegs m -> NB_GLOBALS_TOP <= lo' -> 0x104d0 <= STR_TOP ->
nb_cstr_arg STR_TOP m (Z_to_bv 64 A_MSG_MORE_THAN_TWO_WB) MSG_MORE_THAN_TWO_WB lo' sp'.
Proof.
intros STR_TOP m lo' sp' MI GL ST. unfold nb_cstr_arg. exists [Z_to_bv 8 0x49].
unfold A_MSG_MORE_THAN_TWO_WB. rewrite unsigned_lit by lia.
split; [apply msg_more_than_two_at; exact MI|].
split; [unfold MSG_MORE_THAN_TWO_WB; cbn; repeat constructor; lia|].
replace (zlength MSG_MORE_THAN_TWO_WB) with 61 by (vm_compute; reflexivity).
replace (zlength [Z_to_bv 8 73]) with 1 by (vm_compute; reflexivity).
change ((- (66705 + 61 + 1)) mod 8) with 1.
unfold NB_GLOBALS_TOP in *. lia.
Qed.

Ltac nbred :=
cbn [nb_first nb_count_lost nb_sampling_rate nb_innov_save nb_pitch_gain_buf_idx nb_encode_submode nb_submodeID
nb_lpc_enh_enabled nb_stereo_cb nb_voc_offset nb_dtx_enabled nb_isWideband nb_highpass_enabled nb_isave_ptr
set_nb_first set_nb_count_lost set_nb_submodeID set_nb_voc_offset set_nb_dtx_enabled set_nb_pitch_gain_buf_idx].
Ltac jred := cbn [j_last_ol_gain j_excbuf j_exc j_old_qlsp j_interp_qlpc j_mem_sp j_mem_hp j_pi_gain j_levels j_last_pitch
j_last_pitch_gain j_pitch_gain_buf j_seed j_pad1 j_cbs j_ucb j_voc j_pad2 fst snd].
Ltac asm := first [ eassumption | lazymatch goal with |- ?G => fail 100 "ASMFAIL:" G end ].

Section Inv.
Context {RCEIL : RunCeiling}.
Context {ptr : Type}.
Variable notify : list Z -> X1qx.M PState unit.
Variable STR_TOP : Z.
Variable X : nbinv ptr.
Hypothesis NH : nb_hyps notify STR_TOP X.
Local Notation ST := (x_st X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation D := (x_D X).
Local Notation STEREO := (x_stereo X). Local Notation ISV := (x_isv X). Local Notation lo := (x_lo X).
Local Notation m0 := (x_m0 X). Local Notation canary := (x_canary X).
Local Notation usp := (bv_unsigned (x_sp X)).

#[using="notify STR_TOP NH"] Lemma lay_tops_X : 0x6e000 <= lo /\ 0 < ST /\ 0x6e000 <= OUT /\ 0x6e000 <= A /\ 0 < D /\ 0x6e000 <= STEREO /\ 0x6e000 <= ISV.
Proof. exact (lay_tops _ _ _ _ _ _ _ _ _ (h_lay _ _ _ NH)). Qed.

#[using="Type"] Lemma nbW_eq : nbW X = [(lo, usp); (ST, ST + 2968); (OUT, OUT + 640); (ISV, ISV + 640); (A, A + 48); (STEREO, STEREO + 8)].
Proof. reflexivity. Qed.

#[using="notify STR_TOP NH"] Lemma nbW_below : forall m, munch (nbW X) m0 m ->
disjoint_from (nbW X) NB_TABLES_LO (NB_TABLES_HI - NB_TABLES_LO) /\
disjoint_from (nbW X) NB_RSTDERR 232 /\ disjoint_from (nbW X) NB_GOT_SSP 8 /\ disjoint_from (nbW X) NB_SSP_GUARD 8.
Proof.
intros m _. pose proof lay_tops_X as sfP_; first [ sf_destruct 7%nat sfP_ as T0 T1 T2 T3 T4 T5 T6 | sf_fb; destruct sfP_ as (T0 & T1 & T2 & T3 & T4 & T5 & T6) ].
pose proof (lay_win_ST _ _ _ _ _ _ _ _ _ (h_lay _ _ _ NH)) as W1.
unfold nbW, NB_TABLES_LO, NB_TABLES_HI, NB_RSTDERR, NB_GOT_SSP, NB_SSP_GUARD, NBSTATE_SIZEOF, BITS_SIZEOF in *. cbn. lia.
Qed.
#[using="notify STR_TOP NH"] Lemma ctx_tables : forall m, munch (nbW X) m0 m -> nb_tables m.
Proof. intros m MU. eapply nb_tables_transport; [exact (h_tab0 _ _ _ NH)| exact MU| apply (proj1 (nbW_below m MU))]. Qed.
#[using="notify STR_TOP NH"] Lemma ctx_serr : forall m, munch (nbW X) m0 m -> wmono rsegs m0 m -> x_serr X m.
Proof. intros m MU WM. eapply (h_serrf _ _ _ NH); [exact (h_serr0 _ _ _ NH)| exact MU| exact WM| apply (proj1 (proj2 (nbW_below m MU)))]. Qed.
#[using="notify STR_TOP NH"] Lemma ctx_sspc : forall m, munch (nbW X) m0 m -> wmono rsegs m0 m -> x_sspc X m canary.
Proof. intros m MU WM. pose proof (nbW_below m MU) as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ D1 D2 | sf_fb; destruct sfP_ as (_ & _ & D1 & D2) ]. eapply (h_sspcf _ _ _ NH); [exact (h_sspc0 _ _ _ NH)| exact MU| exact WM| exact D1| exact D2]. Qed.
#[using="Type"] Lemma munch_nbW_full : forall m, munch (nbW X) m0 m -> munch (nb_W ST OUT A STEREO ISV lo usp) m0 m.
Proof. intros m MU. eapply munch_weaken; [|exact MU]. unfold sub_fp, nbW, nb_W. cbn. intros x Hx. lia. Qed.
#[using="notify STR_TOP NH"] Lemma USP_eq : bv_unsigned (Z_to_bv 64 (usp + -912)) = usp + -912.
Proof.
pose proof lay_tops_X as (T0 & _). pose proof (h_lo _ _ _ NH) as LO. pose proof (h_spx _ _ _ NH) as SPX.
unfold NB_DECODE_DEPTH, NB_FRAME, NB_FPRINTF_DEPTH in LO. apply unsigned_lit; lia.
Qed.
End Inv.

Ltac open_hyps NH :=
lazymatch type of NH with nb_hyps _ _ ?X =>
pose proof (h_lay _ _ _ NH) as LAY; pose proof (h_lo _ _ _ NH) as LO; pose proof (h_spx _ _ _ NH) as SPX;
pose proof (h_inv0 _ _ _ NH) as INV0;
unfold NB_DECODE_DEPTH, NB_FRAME, NB_FPRINTF_DEPTH in LO;
pose proof (lay_tops _ _ _ _ _ _ _ _ _ LAY) as sfP_; sf_curry 7%nat sfP_; intros T0 T1 T2 T3 T4 T5 T6; sf_clear sfP_; sf_fix_order;
pose proof (USP_eq _ _ X NH) as USP
end.

Ltac open_ctx CTX :=
let MU := fresh "MU" in let WM := fresh "WM" in let MI := fresh "MI" in let STK := fresh "STK" in
let PCS := fresh "PCS" in let JOK := fresh "JOK" in let CBS := fresh "CBS" in let INV := fresh "INV" in let REP := fresh "REP" in
let BOK := fresh "BOK" in let BSZ := fresh "BSZ" in let XO := fresh "XO" in let LO_ := fresh "Lows" in
let XI := fresh "XI" in let LI := fresh "Liws" in let XS := fresh "XS" in let LS := fresh "Lsws" in
sf_curry 17%nat CTX; intros MU WM MI STK PCS JOK CBS INV REP BOK BSZ XO LO_ XI LI XS LS; sf_clear CTX; sf_fix_order;
unfold nbW, NBSTATE_SIZEOF, BITS_SIZEOF in MU;
let P0 := fresh "P0" in let P1 := fresh "P1" in let P2 := fresh "P2" in let P3 := fresh "P3" in let P4 := fresh "P4" in
let P5 := fresh "P5" in let P6 := fresh "P6" in let P7 := fresh "P7" in let P8 := fresh "P8" in let P9 := fresh "P9" in
let P10 := fresh "P10" in let P11 := fresh "P11" in let P12 := fresh "P12" in let P13 := fresh "P13" in let P14 := fresh "P14" in
let P15 := fresh "P15" in let P16 := fresh "P16" in let P17 := fresh "P17" in let P18 := fresh "P18" in
sf_curry 19%nat PCS; intros P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18; sf_clear PCS; sf_fix_order;
unfold nb_hdr_cells in P0; unfold nb_cfg_cells in P14; unfold nb_ucb_cells, cb_cells in P16; unfold nb_tail_cells in P18;
let L1 := fresh "Lexc" in let L3 := fresh "Loq" in let L4 := fresh "Liq" in let L5 := fresh "Lmsp" in let L6 := fresh "Lmhp" in
let L7 := fresh "Lpig" in let L9 := fresh "Llev" in let L11 := fresh "Lpgb" in let Lp1 := fresh "Lpad1" in let L15 := fresh "Lcbs" in
let L16 := fresh "Lucb" in let L17 := fresh "Lvoc" in let Lp2 := fresh "Lpad2" in
pose proof JOK as sfP_; sf_curry 13%nat sfP_; intros L1 L3 L4 L5 L6 L7 L9 L11 Lp1 L15 L16 L17 Lp2; sf_clear sfP_; sf_fix_order.
Ltac open_frame FRA :=
let FA := fresh "FA" in let FL := fresh "FL" in let FQ := fresh "FQ" in let FK := fresh "FK" in let FE := fresh "FE" in
let FI := fresh "FI" in let FS := fresh "FS" in let FP := fresh "FP" in let FV := fresh "FV" in
sf_curry 9%nat FRA; intros FA FL FQ FK FE FI FS FP FV; sf_clear FRA; sf_fix_order;
unfold fa_cells in FA; unfold fl_cells in FL; unfold fp_cells in FP; unfold fr_saves in FV; cbv zeta in FV.
Ltac open_fok FOK :=
let L1 := fresh "Lfiq" in let L2 := fresh "Lfak" in let L3 := fresh "Lfe32" in let L4 := fresh "Lfinn" in let L5 := fresh "Lfql" in
pose proof FOK as sfP_; sf_curry 5%nat sfP_; intros L1 L2 L3 L4 L5; sf_clear sfP_; sf_fix_order.

Ltac open_bits REP BOK :=
lazymatch type of REP with bits_rep _ _ ?A ?D ?b =>
pose proof (bits_ints A D b BOK (proj2 (proj2 REP))) as sfP_; sf_curry 13%nat sfP_; intros In Ic Ib Io Iv Is Rc Rb Rp Rn Rs R1 Rov; sf_clear sfP_; sf_fix_order;
unfold int31, BITS_BUF_MAX, bits_pos in In, Ic, Ib, Io, Iv, Is, Rc, Rb, Rp, Rn, Rs, R1;
pose proof (remaining_range b BOK) as RR
end.

Ltac close_goal MU :=
lazymatch goal with
| |- munch (nb_W _ _ _ _ _ _ _) _ _ =>
first [ exact MU | unfold nb_W, NBSTATE_SIZEOF, BITS_SIZEOF, NB_RSTDERR; exact MU
| apply munch_nbW_full; rewrite nbW_eq; exact MU ]
| |- munch _ _ _ => first [ exact MU | rewrite nbW_eq; exact MU ]
| |- nb_pieces _ _ _ _ _ _ _ _ _ _ =>
unfold nb_pieces, nb_hdr_cells, nb_cfg_cells, nb_ucb_cells, cb_cells, nb_tail_cells; unfold nb_isave_ptr in *; nbred; jred;
repeat match goal with |- _ /\ _ => split end; asm
| |- nb_inv _ => close_inv
| |- nb_junk_ok _ => first [ assumption | unfold nb_junk_ok; jred; repeat split; first [lia | asm] ]
| |- cbs_ok _ _ _ _ => nbred; jred; asm
| |- nb_tables _ => first [ assumption | eapply ctx_tables; [eassumption | rewrite nbW_eq; exact MU]
| eapply nb_tables_transport; [eassumption | eassumption | cbn [disjoint_from]; unfold NB_TABLES_LO, NB_TABLES_HI, NB_RSTDERR; lia] ]
| |- x_serr _ _ => first [ assumption | eapply ctx_serr; [eassumption | rewrite ?nbW_eq; asm | asm] ]
| |- x_sspc _ _ _ => first [ assumption | eapply ctx_sspc; [eassumption | rewrite ?nbW_eq; asm | asm] ]
| |- sb_buf_size _ = sb_buf_size _ =>
rewrite ?skip_bits_size, ?user_handler_bits_size, ?inband_bits_size, ?lsp_bits_size, ?ltp_bits_size, ?innov_bits_size, ?adv_size, ?ub_size;
first [ assumption | congruence | lia ]
| |- _ => first [ asm | lia ]
end.
Ltac close_ctxX MU := unfold nbctxX; repeat match goal with |- _ /\ _ => split end; close_goal MU.
Ltac close_ctx MU := unfold nbctx; repeat match goal with |- _ /\ _ => split end; close_goal MU.
Ltac close_frame := unfold frame_at, fr_saves; cbv zeta; repeat match goal with |- _ /\ _ => split end; asm.

Ltac junk_exists :=
lazymatch goal with
| P0 : rw_cells _ ?m ?st [C8 _; C4 _; C4 _; C4 _; C4 ?log; C8 _] |- _ =>
lazymatch goal with | P1 : rw_cells _ m (st + 32) (f32 ?eb) |- _ =>
lazymatch goal with | P2 : rw_cells _ m (st + 2032) [C8 (Z_to_bv 64 ?exc)] |- _ =>
lazymatch goal with | P3 : rw_cells _ m (st + 2040) (f32 ?oq) |- _ =>
lazymatch goal with | P4 : rw_cells _ m (st + 2080) (f32 ?iq) |- _ =>
lazymatch goal with | P5 : rw_cells _ m (st + 2120) (f32 ?msp) |- _ =>
lazymatch goal with | P6 : rw_cells _ m (st + 2160) (f32 ?mhp) |- _ =>
lazymatch goal with | P7 : rw_cells _ m (st + 2168) (f32 ?pig) |- _ =>
lazymatch goal with | P9 : rw_cells _ m (st + 2192) (f32 ?lev) |- _ =>
lazymatch goal with | P10 : rw_cells _ m (st + 2204) [C4 ?lp; C4 ?lpg] |- _ =>
lazymatch goal with | P11 : rw_cells _ m (st + 2212) (f32 ?pgb) |- _ =>
lazymatch goal with | P13 : rw_cells _ m (st + 2228) [C4 ?seed] |- _ =>
lazymatch goal with | P14 : rw_cells _ m (st + 2232) [_; CB 4 ?pad1; _; _; _] |- _ =>
lazymatch goal with | P15 : rw_cells _ m (st + 2256) [CB 640 ?cbs] |- _ =>
lazymatch goal with | P16 : rw_cells _ m (st + 2896) [CB 8 ?ja; _; _; CB 16 ?jb] |- _ =>
lazymatch goal with | P17 : rw_cells _ m (st + 2936) (f32 ?voc) |- _ =>
lazymatch goal with | P18 : rw_cells _ m (st + 2948) [_; _; _; _; CB 4 ?pad2] |- _ =>
exists (NBJ log eb exc oq iq msp mhp pig lev lp lpg pgb seed pad1 cbs (ja, jb) voc pad2)
end end end end end end end end end end end end end end end end end.

Ltac frame_exists :=
lazymatch goal with
| FA : rw_cells _ ?m (_ + -912) [C8 ?a0; C8 ?a1; C8 ?a2; C8 ?a3; C8 ?a4; C8 ?a5] |- _ =>
lazymatch goal with
| FL : rw_cells _ m (_ + -864) [C8 ?v48; C8 ?v56; C4 ?p64; C4 ?v68; C8 ?v72; C8 ?v80; C8 ?v88; C8 ?v96; C8 ?v104; C8 ?v112; C8 ?v120; C8 ?v128] |- _ =>
lazymatch goal with
| FQ : rw_cells _ m (_ + -776) (f32 ?iq) |- _ =>
lazymatch goal with
| FK : rw_cells _ m (_ + -736) (f32 ?ak) |- _ =>
lazymatch goal with
| FE : rw_cells _ m (_ + -576) (f32 ?e32) |- _ =>
lazymatch goal with
| FI : rw_cells _ m (_ + -416) (f32 ?inn) |- _ =>
lazymatch goal with
| FS : rw_cells _ m (_ + -256) (f32 ?ql) |- _ =>
lazymatch goal with
| FP : rw_cells _ m (_ + -216) [C4 ?g0; C4 ?g1; C4 ?g2; C4 ?pv] |- _ =>
exists (FRM a0 a1 a2 a3 a4 a5 v48 v56 p64 v68 v72 v80 v88 v96 v104 v112 v120 v128 iq ak e32 inn ql g0 g1 g2 pv)
end end end end end end end end.
Ltac close_fok := first [ assumption | unfold frame_ok; cbn [f_iq f_ak f_e32 f_inn f_ql]; repeat split; first [lia | asm] ].
Ltac close_feqs := cbn [f_v48 f_v56 f_v68 f_v72 f_v80 f_v88 f_v96 f_v104 f_v112 f_v120 f_v128]; jred;
repeat match goal with |- _ /\ _ => split end;
first [ reflexivity | assumption | lia
| left; split; [assumption | lia] | right; split; [assumption | lia]
| asm ].
Ltac close_frame' := unfold frame_at, fr_saves, fa_cells, fl_cells, fp_cells; cbv zeta;
cbn [f_a0 f_a1 f_a2 f_a3 f_a4 f_a5 f_v48 f_v56 f_p64 f_v68 f_v72 f_v80 f_v88 f_v96 f_v104 f_v112 f_v120 f_v128 f_iq f_ak f_e32 f_inn f_ql f_g0 f_g1 f_g2 f_pv];
repeat match goal with |- _ /\ _ => split end; asm.

Ltac close_X :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
lazymatch goal with MU : munch _ (x_m0 _) m |- _ =>
apply evt_done; split; [reflexivity|]; cbv beta iota; unfold at_X;
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _); sf_eexists 13%nat;
junk_exists; sf_eexists 3%nat; frame_exists; split; [reflexivity|];
split; [asm|]; split; [close_ctxX MU|]; split; [close_fok|]; split; [close_frame'| close_feqs]
end end.
Ltac close_B :=
lazymatch goal with |- at_B _ _ _ (MS _ _ _ _ _ ?m _) =>
lazymatch goal with MU : munch _ (x_m0 _) m |- _ =>
unfold at_B; eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _); sf_eexists 12%nat;
junk_exists; sf_eexists 3%nat; frame_exists; split; [reflexivity|];
split; [asm|]; split; [close_ctx MU|]; split; [close_fok|]; split; [close_frame'| close_feqs]
end end.
Ltac close_A :=
lazymatch goal with |- at_A _ _ _ (MS _ _ _ _ _ ?m _) =>
lazymatch goal with MU : munch _ (x_m0 _) m |- _ =>
unfold at_A; eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _); sf_eexists 2%nat;
junk_exists; sf_eexists 3%nat; frame_exists; split; [reflexivity|];
split; [asm|]; split; [close_ctx MU|]; split; [close_fok|]; split; [close_frame'| close_feqs]
end end.

Tactic Notation "close_cut" integer(n) :=
lazymatch goal with |- ?P (MS _ _ _ _ _ ?m _) =>
lazymatch goal with MU : munch _ (x_m0 _) m |- _ =>
hnf; eexists; eexists; eexists; eexists (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _); do n eexists;
junk_exists; sf_eexists 3%nat; frame_exists; split; [reflexivity|];
split; [asm|]; split; [close_ctx MU|]; split; [close_fok|];
first [ split; [close_frame' | close_feqs] | close_frame' ]
end end.

Ltac after_bits R b' :=
try clear R; try rename MI0 into MI;
match goal with H : bits_rep _ _ _ _ b' |- _ => rename H into R end.
