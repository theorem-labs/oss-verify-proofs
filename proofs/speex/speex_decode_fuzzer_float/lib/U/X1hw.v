(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1hx X1g6 X1g7 X1g0.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ucond_rw := unfold_cond; fold_lit_ux; repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Ltac uif b := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) => replace c with b; [cbv iota | symmetry; ucond_rw; solve_cond_rec] end.

Section SegA.
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

Definition pro_post (j : nb_junk) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
fun ms' => exists (fr : frame) (m' : mem),
ms' = MS (mkR ra0 (Z_to_bv 64 (usp + -912)) gp tp t0 t1 t2 cs0 (Z_to_bv 64 ST) (Z_to_bv 64 A) (Z_to_bv 64 0) (Z_to_bv 64 OUT)
a3 a4 a5 a6 a7 cs2 (Z_to_bv 64 (ST + 32)) cs4 cs5 cs6 cs7 cs8
(Z_to_bv 64 (ST + 2184)) cs10 (Z_to_bv 64 A) t3 t4 t5 t6)
F0 (Z_to_bv 64 0x20c04) fc None m' (seg_rom rsegs)
/\ munch [(usp - 912, usp); (ST + 2032, ST + 2040)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (usp + -912)
/\ frame_ok fr /\ frame_at X m' fr
/\ f_v48 fr = Z_to_bv 64 (ST + 2047) /\ f_v80 fr = Z_to_bv 64 OUT /\ f_v88 fr = Z_to_bv 64 ST
/\ f_v112 fr = Z_to_bv 64 A /\ f_v120 fr = Z_to_bv 64 0
/\ rw_cells rsegs m' ST (nb_hdr_cells NB_MODE_PTR st0 (j_last_ol_gain j))
/\ rw_cells rsegs m' (ST + 2032) [C8 (Z_to_bv 64 (ST + 1368))]
/\ rw_cells rsegs m' (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st0 (j_pad1 j)).

#[using="notify STR_TOP NH"] Lemma nbA_pro : forall (j : nb_junk) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (m : mem),
rw_cells rsegs m ST (nb_hdr_cells NB_MODE_PTR st0 (j_last_ol_gain j)) ->
rw_cells rsegs m (ST + 2032) [C8 (Z_to_bv 64 (j_exc j))] ->
rw_cells rsegs m (ST + 2232) (nb_cfg_cells NB_SUBMODES_PTR st0 (j_pad1 j)) ->
0 < A -> A + 48 <= 2^64 ->
stk rsegs m lo usp -> mem_inv rsegs m ->
evt rsegs (pro_post j t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc m)
(MS (mkR ra0 sp gp tp t0 t1 t2 cs0 cs1 (Z_to_bv 64 ST) (Z_to_bv 64 A) (Z_to_bv 64 OUT) a3 a4 a5 a6 a7 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3 t4 t5 t6)
F0 (Z_to_bv 64 A_nb_decode) fc None m (seg_rom rsegs)).
Proof.
intros j t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc m P0 P2 P14 Apos Amax STK MI.
unfold A_nb_decode. open_hyps NH.
pose proof INV0 as sfP_; first [ sf_destruct 12%nat sfP_ as Icl Ies Ihp Ifi Ivo Iix Ism Idt Iwb Ien Isr Iis | sf_fb; destruct sfP_ as (Icl & Ies & Ihp & Ifi & Ivo & Iix & Ism & Idt & Iwb & Ien & Isr & Iis) ].
unfold nb_hdr_cells in P0. unfold nb_cfg_cells in P14.
pose proof (munch_refl [(usp - 912, usp); (ST + 2032, ST + 2040)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (h_sthi _ _ _ NH) as STHI. pose proof (h_stal _ _ _ NH) as STAL. unfold NBSTATE_SIZEOF in STHI.
assert (L7 : Z.land ST 7 = 0) by (change 7 with (Z.ones 3); rewrite (Z.land_ones ST 3) by lia; exact STAL).
zstep. carve_frame 912%nat STK.
apply (rw_cells_split_CB rsegs _ _ [] 912 _ _ [48;88;40;160;160;160;40;16;200]%nat) in FR; [|reflexivity]; cbn [mk_CB_cells app] in FR.
chunk_splitk FR at 1%nat as FA; chunk_splitk FR at 1%nat as FL; chunk_splitk FR at 1%nat as FQ; chunk_splitk FR at 1%nat as FK;
chunk_splitk FR at 1%nat as FE; chunk_splitk FR at 1%nat as FI; chunk_splitk FR at 1%nat as FS; chunk_splitk FR at 1%nat as FP.
rename FR into FV.

destruct (rw_cells_CB_C8s rsegs _ _ 6%nat _ FA) as (la & Lla & FA'); clear FA.
destruct la as [|fa0 [|fa1 [|fa2 [|fa3 [|fa4 [|fa5 [|? ?]]]]]]]; cbn in Lla; try lia. cbn [map] in FA'.
apply (rw_cells_split_CB rsegs _ _ [] 88 _ _ [16;8;64]%nat) in FL; [|reflexivity]; cbn [mk_CB_cells app] in FL.
chunk_splitk FL at 1%nat as FL1; chunk_splitk FL at 1%nat as FL2. rename FL into FL3.
destruct (rw_cells_CB_C8s rsegs _ _ 2%nat _ FL1) as (lb & Llb & FL1'); clear FL1.
destruct lb as [|v48 [|v56 [|? ?]]]; cbn in Llb; try lia. cbn [map] in FL1'.
destruct (rw_cells_CB_f32 rsegs _ _ 2%nat _ FL2) as (lc & Llc & FL2'); clear FL2.
destruct lc as [|p64 [|v68 [|? ?]]]; cbn in Llc; try lia.
destruct (rw_cells_CB_C8s rsegs _ _ 8%nat _ FL3) as (ld & Lld & FL3'); clear FL3.
destruct ld as [|v72 [|v80 [|v88 [|v96 [|v104 [|v112 [|v120 [|v128 [|? ?]]]]]]]]]; cbn in Lld; try lia. cbn [map] in FL3'.
rewrite f32_cons, f32_cons, f32_nil in FL2'. chunk_cat FL1' FL2'. chunk_cat FL1' FL3'. rename FL1' into FL.
destruct (rw_cells_CB_f32 rsegs _ _ 10%nat _ FQ) as (iq & Liq & FQ'); clear FQ.
destruct (rw_cells_CB_f32 rsegs _ _ 40%nat _ FK) as (ak & Lak & FK'); clear FK.
destruct (rw_cells_CB_f32 rsegs _ _ 40%nat _ FE) as (e32 & Le32 & FE'); clear FE.
destruct (rw_cells_CB_f32 rsegs _ _ 40%nat _ FI) as (inn & Linn & FI'); clear FI.
destruct (rw_cells_CB_f32 rsegs _ _ 10%nat _ FS) as (ql & Lql & FS'); clear FS.
destruct (rw_cells_CB_f32 rsegs _ _ 4%nat _ FP) as (lg & Llg & FP'); clear FP.
destruct lg as [|g0 [|g1 [|g2 [|pv [|? ?]]]]]; cbn in Llg; try lia. rewrite !f32_cons, f32_nil in FP'.
apply (rw_cells_split_CB rsegs _ _ [] 200 _ _ [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FV; [|reflexivity]; cbn [mk_CB_cells app] in FV.
repeat match type of FV with context [CB 8 ?bs] =>
lazymatch bs with
| firstn _ _ => let jj := fresh "jk" in remember bs as jj eqn:EJ in FV; clear EJ
| skipn _ _ => let jj := fresh "jk" in remember bs as jj eqn:EJ in FV; clear EJ
end end.
clear junk.

do 25 zstep.

zstep. zstep. zstep.
zstep. uif true.
zstep. zstep. zstep. rewrite L7. if_true_x.
zstep. zstep. zstep. zstep. uif true.
zstep. zstep. zstep. zstep. uif true.
zstep. zstep. zstep. zstep. uif true.
zstep. zstep. zstep. zstep. fix_lit_store. zstep. zstep. zstep. zstep.
zstep. zstep. if_false_x.
zstep. rewrite Ies. zstep. if_false.
zstep.
apply evt_done. unfold pro_post.
exists (FRM fa0 fa1 fa2 fa3 fa4 fa5 (Z_to_bv 64 (ST + 2047)) v56 p64 v68 v72 (Z_to_bv 64 OUT) (Z_to_bv 64 ST) v96 v104 (Z_to_bv 64 A) (Z_to_bv 64 0) v128 iq ak e32 inn ql g0 g1 g2 pv).
eexists. split; [reflexivity|].
unfold frame_ok, frame_at, fa_cells, fl_cells, fp_cells, fr_saves; cbv zeta; cbn [f_a0 f_a1 f_a2 f_a3 f_a4 f_a5 f_v48 f_v56 f_p64 f_v68 f_v72 f_v80 f_v88 f_v96 f_v104 f_v112 f_v120 f_v128 f_iq f_ak f_e32 f_inn f_ql f_g0 f_g1 f_g2 f_pv].
repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity; try lia.
Qed.

#[using="STR_TOP NH"] Lemma nbA_loop : forall fuel (s : PState) b ms,
at_A X 0x20d54 b ms ->
implM rsegs (nb_mode_search notify unpackM advanceM remainingM fuel st0 b) s (QA X s) ms.
Proof.
induction fuel as [|fuel IH]; intros s b ms AT.
{ cbn [nb_mode_search]. apply implM_unr. }
pose proof AT as AT0.
first [ sf_destruct 22%nat AT as Fx fc m k xra xa0 j ows iws sws fr -> FRM CTX FOK FRA E48 E80 E88 E112 E120 JEXC | sf_fb; destruct AT as (Fx & fc & m & k & xra & xa0 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E80 & E88 & E112 & E120 & JEXC) ].
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK. open_bits REP BOK.
rewrite E48, E80, E88, E112, E120 in FL.
apply implM_from_evt.
zstep. zstep. call (X1g6.speex_bits_remaining_spec A D b); [exact REP | exact BOK | exact MI |].
after_bits REP b. match goal with H : ?v = Z_to_bv 64 (speex_bits_remaining b) |- _ => subst v end.
zstep. if_cases K5; zify_cond K5; rewrite ?signed_lit_small in K5 by lia.
-
apply evt_done. apply (nbA_body notify STR_TOP X NH fuel s b); [exact (IH s) | lia | close_A].
-
zstep. apply evt_done. rewrite nb_mode_search_S. eapply implM_bind_run; [reflexivity|]. cbv beta.
replace (speex_bits_remaining b <? 5) with true by (symmetry; apply Z.ltb_lt; lia).
apply implM_ret. close_X.
Qed.

#[using="STR_TOP NH"] Lemma nbA_entry : forall (s : PState) (j : nb_junk) (ows iws sws : list word) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32),
NBP m0 ST OUT STEREO st0 j -> nb_junk_ok j -> cbs_ok A_speex_std_stereo_request_handler STEREO (nb_stereo_cb st0) (j_cbs j) ->
bits_rep rsegs m0 A D b0 -> bits_ok b0 ->
rw_cells rsegs m0 OUT (f32 ows) -> length ows = 160%nat ->
rw_cells rsegs m0 ISV (f32 iws) -> length iws = 160%nat ->
rw_cells rsegs m0 STEREO (f32 sws) -> length sws = 2%nat ->
stk rsegs m0 lo usp -> mem_inv rsegs m0 -> frm0 fc ->
implM rsegs (nb_mode_search notify unpackM advanceM remainingM (nb_search_fuel b0) st0 b0) s (QA X s)
(MS (mkR ra0 sp gp tp t0 t1 t2 cs0 cs1 (Z_to_bv 64 ST) (Z_to_bv 64 A) (Z_to_bv 64 OUT) a3 a4 a5 a6 a7 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 t3 t4 t5 t6)
F0 (Z_to_bv 64 A_nb_decode) fc None m0 (seg_rom rsegs)).
Proof.
intros s j ows iws sws t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc PCS JOK CBS REP BOK XO Lows XI Liws XS Lsws STK MI FRM.
open_hyps NH.
pose proof (munch_refl (nbW X) m0) as MU. pose proof (wmono_refl rsegs m0) as WM. unfold nbW, NBSTATE_SIZEOF, BITS_SIZEOF in MU.
assert (INV : nb_inv st0) by exact INV0. assert (BSZ : sb_buf_size b0 = sb_buf_size b0) by reflexivity.

first [ sf_destruct 19%nat PCS as P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 | sf_fb; destruct PCS as (P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18) ].
pose proof JOK as sfP_; first [ sf_destruct 13%nat sfP_ as Lexc Loq Liq Lmsp Lmhp Lpig Llev Lpgb Lpad1 Lcbs Lucb Lvoc Lpad2 | sf_fb; destruct sfP_ as (Lexc & Loq & Liq & Lmsp & Lmhp & Lpig & Llev & Lpgb & Lpad1 & Lcbs & Lucb & Lvoc & Lpad2) ].
unfold nb_ucb_cells, cb_cells in P16; unfold nb_tail_cells in P18.
open_bits REP BOK.
pose proof (proj2 (proj2 REP)) as SIDE. pose proof SIDE as (_ & Apos & _).
pose proof REP as ((rjx & Lrjx & OBJx) & _ & _). pose proof (rw_cells_bound _ _ _ _ OBJx) as BA.
rewrite bits_cells_size in BA by exact Lrjx. clear OBJx.
unfold nb_search_fuel.
apply implM_from_evt.
call (nbA_pro j t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc m0); [exact P0 | exact P2 | exact P14 | exact Apos | cbn [Z.of_nat] in BA; lia | exact STK | exact MI |].
try rename MI0 into MI.
match goal with H : frame_at X _ _ |- _ => rename H into FRA end. open_frame FRA.
match goal with H : frame_ok _ |- _ => rename H into FOK end. open_fok FOK.
match goal with H : rw_cells _ _ ST (nb_hdr_cells _ _ _) |- _ => rename H into P0; unfold nb_hdr_cells in P0 end.
match goal with H : rw_cells _ _ (ST + 2232) (nb_cfg_cells _ _ _) |- _ => rename H into P14; unfold nb_cfg_cells in P14 end.
match goal with H : stk _ _ lo _ |- _ => rename H into STK end.
match goal with H : f_v48 _ = _ |- _ => rename H into E48 end. match goal with H : f_v80 _ = _ |- _ => rename H into E80 end.
match goal with H : f_v88 _ = _ |- _ => rename H into E88 end. match goal with H : f_v112 _ = _ |- _ => rename H into E112 end.
match goal with H : f_v120 _ = _ |- _ => rename H into E120 end.
rewrite E48, E80, E88, E112, E120 in FL.

zstep. call (X1g6.speex_bits_remaining_spec A D b0); [exact REP | exact BOK | exact MI |].
after_bits REP (x_b0 X). match goal with H : ?v = Z_to_bv 64 (speex_bits_remaining b0) |- _ => subst v end.
zstep. zstep. zstep. if_cases K5; zify_cond K5; rewrite ?signed_lit_small in K5 by lia.
2:{
zstep. apply evt_done. rewrite nb_mode_search_S. eapply implM_bind_run; [reflexivity|]. cbv beta.
replace (speex_bits_remaining b0 <? 5) with true by (symmetry; apply Z.ltb_lt; lia).
apply implM_ret. close_X. }

zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
apply evt_done.
apply (nbA_body notify STR_TOP X NH _ s b0); [apply (nbA_loop) | lia | close_A].
Qed.
End SegA.
