(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1ho X1hm X1hu X1ih X1ht X1if.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1nt X1rh X1re X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
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

Definition rand_post (PX : Z) (xra xsp s0 s1 a0 a2 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
(m : mem) : machine_state -> Prop :=
fun ms' => exists (w a5 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (ws : list word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 s0 s1 a0 w a2 (Z_to_bv 64 (PX + 640)) (Z_to_bv 64 (PX + 640)) a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x1f1ac) fc' None m' (seg_rom rsegs)
/\ munch [(PX, PX + 640)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc' /\ rw_cells rsegs m' PX (f32 ws) /\ length ws = 160%nat.

#[using="Type"] Lemma rand_loop : forall (PX : Z) (xra xsp s1 a0 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word) (mN : mem)
rest done (w a5 : word) q F fc m,
(length done + S (length rest) = 160)%nat ->
q = PX + 4 * Z.of_nat (length done) ->
frm0 fc -> mem_inv rsegs m -> munch [(PX, PX + 640)] mN m -> wmono rsegs mN m ->
rw_cells rsegs m PX (f32 done) -> (exists x rest', rest' = rest /\ rw_cells rsegs m q (f32 (x :: rest'))) ->
evt rsegs (rand_post PX xra xsp (Z_to_bv 64 1013904223) s1 a0 (Z_to_bv 64 1065353216) a6 a7 (Z_to_bv 64 8388607) (Z_to_bv 64 1664525)
s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 mN)
(MS (mkR xra xsp gp tp t0 t1 t2 (Z_to_bv 64 1013904223) s1 a0 w (Z_to_bv 64 1065353216) (Z_to_bv 64 (PX + 640)) (Z_to_bv 64 q) a5 a6 a7
(Z_to_bv 64 8388607) (Z_to_bv 64 1664525) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1f17c) fc None m (seg_rom rsegs)).
Proof.
intros PX xra xsp s1 a0 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 mN.
induction rest as [|x' rest IH]; intros done w a5 q F fc m HL Hq FRM MI MU WM DONE sfH_; first [ sf_destruct 4%nat sfH_ as x rest' -> XR | sf_fb; destruct sfH_ as (x & rest' & -> & XR) ];
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD; cbn [length] in HL;
rewrite !f32_cons, ?f32_nil in XR.
-
zstep. zstep. zstep. zstep. step. step. step. step. step. zstep. zstep. zstep. if_false_x.
replace (q + 4) with (PX + 640) by lia.
unfold rand_post. finish.
+ chunk_snoc DONE XR. apply f32_snoc1 in DONE. exact DONE.
+ rewrite length_app. cbn [length]. lia.
- zstep. zstep. zstep. zstep. step. step. step. step. step. zstep. zstep. zstep. if_true_x.
chunk_uncons XR as X1. chunk_snoc DONE X1. apply f32_snoc1 in DONE.
eapply (IH (done ++ [_]) _ _ (q + 4)); try eassumption.
+ rewrite length_app. cbn [length] in *. lia.
+ rewrite length_app. cbn [length]. lia.
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
first [ sf_destruct 23%nat AT as Fx fc m k xs4 xs8 j ows iws sws fr -> FRM CTX FOK FRA E56 E104 E112 JEXC EA2 EA3 EA4 | sf_fb; destruct AT as (Fx & fc & m & k & xs4 & xs8 & j & ows & iws & sws & fr & -> & FRM & CTX & FOK & FRA & E56 & E104 & E112 & JEXC & EA2 & EA3 & EA4) ].
rewrite EA2, EA3, EA4. clear EA2 EA3 EA4.
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
replace (ST + 2008) with (ST + 1368 + 640) by lia;
call (rand_loop (ST + 1368) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc rest0 []);
[ cbn [length] in *; lia | cbn [length]; lia | assumption | exact MI | apply munch_refl | apply wmono_refl
| rewrite f32_nil; apply rw_cells_nil; lia | sf_eexists 2%nat; split; [reflexivity| exact PE2] | ]
end end.
try clear PE2. try clear LE2. try clear Ews. clear BPE. try rename MI0 into MI.
match goal with H : rw_cells _ _ (ST + 1368) (f32 ?ws), L : length ?ws = _ |- _ => rename H into PE2; rename L into LE2 end.

zstep. zstep. lstep.

zstep. zstep. zstep. zstep. zstep. zstep. zstep.
lazymatch type of PE2 with rw_cells _ _ _ (f32 ?exc) =>
lazymatch type of FI1 with rw_cells _ _ _ (f32 ?lpc) =>
call ((h_iir _ _ _ NH) (ST + 1368) (usp + -416) OUT (ST + 2120) 160 exc lpc ows (j_mem_sp j) (Z_to_bv 64 0));
[ exact PE2 | rewrite LE2; reflexivity | exact FI1 | exact Llpc | exact P5 | exact Lmsp
| right; split; [unfold apart; slia | split; [exact XO | rewrite Lows; reflexivity]]
| lia | unfold apart; slia | unfold apart; slia | unfold apart; slia | unfold apart; slia
| reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
| assumption | assumption | ]
end end.
cbv beta delta [callR]. try rename MI0 into MI. try clear XO. try clear Lows. try clear P5. try clear Lmsp.
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
