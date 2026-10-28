(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ho X1hm X1hu X1ih X1ht X1if.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma f32_snoc1 : forall segs m A done v, rw_cells segs m A (f32 done ++ [C4 v]) -> rw_cells segs m A (f32 (done ++ [v])).
Proof. intros segs m A done v H. rewrite f32_app, f32_cons, f32_nil. exact H. Qed.

Section Seg.
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
Local Notation F0 := (x_F X). Local Notation m0 := (x_m0 X). Local Notation canary := (x_canary X).
Local Notation usp := (bv_unsigned (x_sp X)).

Definition rand_post (PX : Z) (xra xsp s0 s1 a0 a2 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
(m : mem) : machine_state -> Prop :=
fun ms' => exists (w a7 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ws : list word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 s0 s1 a0 w a2 a3 a4 (Z_to_bv 64 (PX + 640)) (Z_to_bv 64 (PX + 640)) a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x21090) fc' None m' (seg_rom rsegs)
/\ munch [(PX, PX + 640)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ rw_cells rsegs m' PX (f32 ws) /\ length ws = 160%nat.

Local Ltac ucond_rw := unfold_cond; fold_lit_ux; repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end.
Local Ltac uif b := lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?x else ?y) ?fc ?rv ?m ?ro) =>
replace c with b; [cbv iota | symmetry; ucond_rw; solve_cond_rec] end.

#[using="Type"] Lemma rand_loop : forall (PX : Z) (xra xsp s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word) (mN : mem)
rest done (w a7 : word) q kz F fc m,
0 < PX ->
(length done + S (length rest) = 160)%nat ->
q = PX + 4 * Z.of_nat (length done) -> kz = Z.of_nat (S (length rest)) ->
frm0 fc -> mem_inv rsegs m -> munch [(PX, PX + 640)] mN m -> wmono rsegs mN m ->
rw_cells rsegs m PX (f32 done) -> (exists x rest', rest' = rest /\ rw_cells rsegs m q (f32 (x :: rest'))) ->
evt rsegs (rand_post PX xra xsp (Z_to_bv 64 1013904223) (Z_to_bv 64 8388607) (Z_to_bv 64 PX) (Z_to_bv 64 1065353216) (Z_to_bv 64 1) (Z_to_bv 64 1)
(Z_to_bv 64 1664525) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 mN)
(MS (mkR xra xsp gp tp t0 t1 t2 (Z_to_bv 64 1013904223) (Z_to_bv 64 8388607) (Z_to_bv 64 PX) w (Z_to_bv 64 1065353216) (Z_to_bv 64 1) (Z_to_bv 64 1)
(Z_to_bv 64 q) (Z_to_bv 64 q) a7 (Z_to_bv 64 1664525) (Z_to_bv 64 kz) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x21038) fc None m (seg_rom rsegs)).
Proof.
intros PX xra xsp s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 mN.
induction rest as [|x' rest IH]; intros done w a7 q kz F fc m HP HL Hq Hk FRM MI MU WM DONE sfH_; first [ sf_destruct 4%nat sfH_ as x rest' -> XR | sf_fb; destruct sfH_ as (x & rest' & -> & XR) ];
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD; cbn [length] in HL, Hk;
rewrite !f32_cons, ?f32_nil in XR.
-
zstep. zstep. zstep. uif true. zstep. zstep.
replace (Z.lxor 1 (Z.b2z (q <? 1))) with 1 by (replace (q <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
zstep. uif true. zstep. uif true.
zstep. zstep. zstep. zstep. step. step. step. step. step. zstep. zstep. zstep. uif false.
replace (q + 4) with (PX + 640) by lia. replace (kz + -1) with 0 by lia.
unfold rand_post. finish.
+ chunk_snoc DONE XR. apply f32_snoc1 in DONE. exact DONE.
+ rewrite length_app. cbn [length]. lia.
-
zstep. zstep. zstep. uif true. zstep. zstep.
replace (Z.lxor 1 (Z.b2z (q <? 1))) with 1 by (replace (q <? 1) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
zstep. uif true. zstep. uif true.
zstep. zstep. zstep. zstep. step. step. step. step. step. zstep. zstep. zstep. uif true.
chunk_uncons XR as X1. chunk_snoc DONE X1. apply f32_snoc1 in DONE.
eapply (IH (done ++ [_]) _ _ (q + 4) (kz + -1)); try eassumption.
+ rewrite length_app. cbn [length] in *. lia.
+ rewrite length_app. cbn [length]. lia.
+ cbn [length] in *. lia.
+ sf_eexists 2%nat. split; [reflexivity|]. rewrite f32_cons. exact XR.
Qed.

Ltac nbred_in H :=
cbn [nb_first nb_count_lost nb_sampling_rate nb_innov_save nb_pitch_gain_buf_idx nb_encode_submode nb_submodeID
nb_lpc_enh_enabled nb_stereo_cb nb_voc_offset nb_dtx_enabled nb_isWideband nb_highpass_enabled nb_isave_ptr
set_nb_first set_nb_count_lost set_nb_submodeID set_nb_voc_offset set_nb_dtx_enabled set_nb_pitch_gain_buf_idx] in H.

Ltac close_atX :=
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
lazymatch goal with MU : munch _ (x_m0 _) m |- _ =>
apply evt_done; unfold at_X;
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _); sf_eexists 13%nat;
junk_exists; sf_eexists 3%nat; frame_exists; split; [reflexivity|];
split; [asm|]; split; [close_ctxX MU|]; split; [close_fok|]; split; [close_frame'| close_feqs]
end end.

#[using="notify STR_TOP NH"] Lemma nbN2 : forall b ms, at_N1 X b ms -> evt rsegs (at_X X 0 (nb_null (set_nb_submodeID st0 0)) b) ms.
Proof.
intros b ms AT. unfold nb_null.
first [ sf_destruct 29%nat AT as Fx fc m k xs5 xs6 xs7 xs8 xs10 xs11 j ows iws sws fr -> FRM CTX FOK FRA E48 E80 E120 JEXC EA2 EA3 EA4 EA5 EA6 | sf_fb; destruct AT as (Fx & fc & m & k & xs5 & xs6 & xs7 & xs8 & xs10 & xs11 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E48 & E80 & E120 & JEXC & EA2 & EA3 & EA4 & EA5 & EA6) ].
rewrite EA2, EA3, EA4, EA5, EA6. clear EA2 EA3 EA4 EA5 EA6.
open_hyps NH. open_ctx CTX. open_frame FRA. open_fok FOK.
first [ pose proof (exc_split3 _ _ _ P1 Lexc) as sfP_; sf_destruct 6%nat sfP_ as PE1 PE2 PE3 LE1 LE2 LE3 | sf_fb; destruct (exc_split3 _ _ _ P1 Lexc) as (PE1 & PE2 & PE3 & LE1 & LE2 & LE3) ]. clear P1.
pose proof (f32_split rsegs _ _ (f_inn fr) 10 ltac:(rewrite Lfinn; lia) FI) as [FI1 FI2]. clear FI.
replace (usp + -416 + 4 * Z.of_nat 10) with (usp + -376) in FI2 by lia.
assert (LFI2 : length (skipn 10 (f_inn fr)) = 30%nat) by (rewrite length_skipn; lia).
assert (Llpc : length (firstn 10 (f_inn fr)) = 10%nat) by (rewrite length_firstn; lia).

pose proof (rw_cells_bound _ _ _ _ PE2) as BPE. rewrite cells_size_f32, LE2 in BPE.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
lazymatch type of PE2 with rw_cells _ _ _ (f32 ?ws) =>
destruct ws as [|xw0 rest0] eqn:Ews; [cbn in LE2; lia|];
call (rand_loop (ST + 1368) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc rest0 []);
[ lia | cbn [length] in *; lia | cbn [length]; lia | cbn [length] in *; lia | assumption | exact MI | apply munch_refl | apply wmono_refl
| rewrite f32_nil; apply rw_cells_nil; lia | sf_eexists 2%nat; split; [reflexivity| exact PE2] | ]
end end.
try clear PE2. try clear LE2. try clear Ews. clear BPE. try rename MI0 into MI.
match goal with H : rw_cells _ _ (ST + 1368) (f32 ?ws), L : length ?ws = _ |- _ => rename H into PE2; rename L into LE2 end.

zstep. zstep. lstep.

zstep. rewrite E48. zstep. zstep. zstep. zstep. zstep. rewrite E80. zstep. rewrite E120. zstep.
pose proof (h_stal _ _ _ NH) as STAL. pose proof (h_sp16 _ _ _ NH) as SP16. pose proof (h_out4 _ _ _ NH) as OUT4.
pose proof (lay_ST_stk _ _ _ _ _ _ _ _ _ LAY) as LSS. pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ LAY) as LOS.
lazymatch type of PE2 with rw_cells _ _ _ (f32 ?exc) =>
lazymatch type of FI1 with rw_cells _ _ _ (f32 ?lpc) =>
call ((h_iir _ _ _ NH) (ST + 1368) (usp + -416) OUT (ST + 2120) 160 lo exc lpc ows (j_mem_sp j) (Z_to_bv 64 0));
[ exact PE2 | rewrite LE2; reflexivity | exact FI1 | exact Llpc | exact P5 | exact Lmsp
| right; split; [unfold apart; slia | split; [exact XO | rewrite Lows; reflexivity]]
| lia | unfold apart; slia | unfold apart; slia | unfold apart; slia | unfold apart; slia
| lia | clear - STAL; Z.div_mod_to_equations; lia | lia | clear - SP16; Z.div_mod_to_equations; lia
| lia | exact OUT4 | lia | clear - STAL; Z.div_mod_to_equations; lia
| rewrite USP; exact STK | rewrite USP; unfold IIR_DEPTH; lia | exact T0 | rewrite USP; lia
| rewrite USP; unfold apart; lia | rewrite USP; unfold apart; lia | rewrite USP; unfold apart; lia | rewrite USP; unfold apart; lia
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| assumption | assumption | ]
end end.
cbv beta delta [callR]. try rename MI0 into MI. rewrite USP in *. try clear XO. try clear Lows. try clear P5. try clear Lmsp.
match goal with H : rw_cells _ _ OUT (f32 ?ws), L : length ?ws = _ |- _ => rename H into XO; rename L into Lows; cbn in Lows end.
match goal with H : rw_cells _ _ (ST + 2120) (f32 ?ws), L : length ?ws = _ |- _ => rename H into P5; rename L into Lmsp end.

zstep. unfold nb_isave_ptr. nbred.
pose proof (h_isv _ _ _ NH) as HISV.

destruct (exc_join3 _ _ _ _ _ PE1 PE2 PE3 LE1 LE2 LE3) as [P1 Lexc1]. clear PE1 PE2 PE3.
lazymatch type of FI1 with rw_cells _ ?mm _ (f32 ?lpc) =>
assert (FI : rw_cells rsegs mm (usp + -416) (f32 (lpc ++ skipn 10 (f_inn fr))))
by (apply f32_join; [exact FI1 | rewrite Llpc; replace (usp + -416 + 4 * Z.of_nat 10) with (usp + -376) by lia; exact FI2]);
assert (Lfinn2 : length (lpc ++ skipn 10 (f_inn fr)) = 40%nat) by (rewrite length_app, Llpc, LFI2; reflexivity)
end.
clear FI1 FI2.
assert (INV1 : nb_inv (set_nb_count_lost (set_nb_first (set_nb_submodeID st0 0) 1) 0))
by (apply nb_inv_set_count_lost; apply nb_inv_set_first; [exact INV | lia]).
destruct (nb_innov_save st0) as [kis|] eqn:EIS.
-
pose proof (rw_cells_bound _ _ _ _ XI) as BXI. rewrite cells_size_f32, Liws in BXI.
rewrite <- HISV. zstep. if_false_x. zstep. zstep. zstep.
pose proof (f32_as_blob _ _ _ 160%nat XI Liws) as XIB. clear XI.
call (nmemset_specZ ISV 640 0 (cells_bytes (f32 iws)) _); [exact XIB | assumption | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
try rename MI0 into MI.
match goal with H : rw_cells _ ?mm ISV [CB _ _] |- _ =>
assert (XI : rw_cells rsegs mm ISV (f32 (repeat (Z_to_bv 64 0) 160)))
by (eapply rw_cells_recast; [exact H | apply cells_wf_f32 | vm_compute; reflexivity]);
clear H end.
assert (Liws0 : length (repeat (Z_to_bv 64 0) 160) = 160%nat) by (rewrite repeat_length; reflexivity).
zstep. lstep. zstep. close_atX.
-
zstep. if_true. zstep. lstep. zstep. close_atX.
Qed.

#[using="notify STR_TOP NH"] Lemma nbN : forall b ms, at_N X b ms -> evt rsegs (at_X X 0 (nb_null (set_nb_submodeID st0 0)) b) ms.
Proof.
intros b ms AT. eapply evt_cut; [exact (nbN1 notify STR_TOP X NH b ms AT)|].
intros ms' H'. exact (nbN2 b ms' H').
Qed.
End Seg.
