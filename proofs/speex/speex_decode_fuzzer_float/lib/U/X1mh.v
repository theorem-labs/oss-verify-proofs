(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma X1mw X1mr X1mf.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff X1g7.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Ubsan.M.loaded_segments.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Notation MODEP mo := (sb_mode_ptr NB_MODE_PTR A_speex_wb_mode A_speex_uwb_mode mo).
Local Notation SUBP mo := (sb_submodes_ptr WB_SUBMODES_PTR UWB_SUBMODES_PTR mo).

Ltac exact_at H :=
lazymatch goal with |- rw_cells ?s ?m ?A ?cs =>
lazymatch type of H with rw_cells _ _ ?B _ => first [ exact H | replace A with B by lia; exact H ] end end.

Ltac fp_join pc :=
lazymatch goal with |- evt ?segs _ (MS ?R _ _ ?fc None ?m ?rom) =>
eapply (evt_cut segs (fun ms1 => exists Fx1 : bvmap 5 word, ms1 = MS R Fx1 (Z_to_bv 64 pc) fc None m rom))
end.

Lemma gcqb_cell : forall m q, mem_inv rsegs m -> 0 <= q < 16 -> exists bs, length bs = 4%nat /\ ro_cells rsegs m (78700 + 4 * q) [CB 4 bs].
Proof.
intros m q MI Hq. assert (C : q = 0 \/ q = 1 \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 5 \/ q = 6 \/ q = 7 \/ q = 8 \/ q = 9 \/ q = 10 \/ q = 11 \/ q = 12 \/ q = 13 \/ q = 14 \/ q = 15) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]]]]]]].
- exists [Z_to_bv 8 132; Z_to_bv 8 211; Z_to_bv 8 122; Z_to_bv 8 63]. split; [reflexivity|]. change (78700 + 4 * 0) with 78700.
apply (ro_cells_image rsegs m 78700 [Z_to_bv 8 132; Z_to_bv 8 211; Z_to_bv 8 122; Z_to_bv 8 63] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 222; Z_to_bv 8 84; Z_to_bv 8 164; Z_to_bv 8 63]. split; [reflexivity|]. change (78700 + 4 * 1) with 78704.
apply (ro_cells_image rsegs m 78704 [Z_to_bv 8 222; Z_to_bv 8 84; Z_to_bv 8 164; Z_to_bv 8 63] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 80; Z_to_bv 8 83; Z_to_bv 8 215; Z_to_bv 8 63]. split; [reflexivity|]. change (78700 + 4 * 2) with 78708.
apply (ro_cells_image rsegs m 78708 [Z_to_bv 8 80; Z_to_bv 8 83; Z_to_bv 8 215; Z_to_bv 8 63] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 153; Z_to_bv 8 18; Z_to_bv 8 13; Z_to_bv 8 64]. split; [reflexivity|]. change (78700 + 4 * 3) with 78712.
apply (ro_cells_image rsegs m 78712 [Z_to_bv 8 153; Z_to_bv 8 18; Z_to_bv 8 13; Z_to_bv 8 64] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 190; Z_to_bv 8 217; Z_to_bv 8 56; Z_to_bv 8 64]. split; [reflexivity|]. change (78700 + 4 * 4) with 78716.
apply (ro_cells_image rsegs m 78716 [Z_to_bv 8 190; Z_to_bv 8 217; Z_to_bv 8 56; Z_to_bv 8 64] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 143; Z_to_bv 8 54; Z_to_bv 8 114; Z_to_bv 8 64]. split; [reflexivity|]. change (78700 + 4 * 5) with 78720.
apply (ro_cells_image rsegs m 78720 [Z_to_bv 8 143; Z_to_bv 8 54; Z_to_bv 8 114; Z_to_bv 8 64] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 33; Z_to_bv 8 176; Z_to_bv 8 158; Z_to_bv 8 64]. split; [reflexivity|]. change (78700 + 4 * 6) with 78724.
apply (ro_cells_image rsegs m 78724 [Z_to_bv 8 33; Z_to_bv 8 176; Z_to_bv 8 158; Z_to_bv 8 64] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 141; Z_to_bv 8 238; Z_to_bv 8 207; Z_to_bv 8 64]. split; [reflexivity|]. change (78700 + 4 * 7) with 78728.
apply (ro_cells_image rsegs m 78728 [Z_to_bv 8 141; Z_to_bv 8 238; Z_to_bv 8 207; Z_to_bv 8 64] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 126; Z_to_bv 8 58; Z_to_bv 8 8; Z_to_bv 8 65]. split; [reflexivity|]. change (78700 + 4 * 8) with 78732.
apply (ro_cells_image rsegs m 78732 [Z_to_bv 8 126; Z_to_bv 8 58; Z_to_bv 8 8; Z_to_bv 8 65] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 178; Z_to_bv 8 128; Z_to_bv 8 50; Z_to_bv 8 65]. split; [reflexivity|]. change (78700 + 4 * 9) with 78736.
apply (ro_cells_image rsegs m 78736 [Z_to_bv 8 178; Z_to_bv 8 128; Z_to_bv 8 50; Z_to_bv 8 65] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 54; Z_to_bv 8 229; Z_to_bv 8 105; Z_to_bv 8 65]. split; [reflexivity|]. change (78700 + 4 * 10) with 78740.
apply (ro_cells_image rsegs m 78740 [Z_to_bv 8 54; Z_to_bv 8 229; Z_to_bv 8 105; Z_to_bv 8 65] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 29; Z_to_bv 8 61; Z_to_bv 8 153; Z_to_bv 8 65]. split; [reflexivity|]. change (78700 + 4 * 11) with 78744.
apply (ro_cells_image rsegs m 78744 [Z_to_bv 8 29; Z_to_bv 8 61; Z_to_bv 8 153; Z_to_bv 8 65] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 166; Z_to_bv 8 202; Z_to_bv 8 200; Z_to_bv 8 65]. split; [reflexivity|]. change (78700 + 4 * 12) with 78748.
apply (ro_cells_image rsegs m 78748 [Z_to_bv 8 166; Z_to_bv 8 202; Z_to_bv 8 200; Z_to_bv 8 65] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 234; Z_to_bv 8 140; Z_to_bv 8 3; Z_to_bv 8 66]. split; [reflexivity|]. change (78700 + 4 * 13) with 78752.
apply (ro_cells_image rsegs m 78752 [Z_to_bv 8 234; Z_to_bv 8 140; Z_to_bv 8 3; Z_to_bv 8 66] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 125; Z_to_bv 8 95; Z_to_bv 8 44; Z_to_bv 8 66]. split; [reflexivity|]. change (78700 + 4 * 14) with 78756.
apply (ro_cells_image rsegs m 78756 [Z_to_bv 8 125; Z_to_bv 8 95; Z_to_bv 8 44; Z_to_bv 8 66] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 16; Z_to_bv 8 221; Z_to_bv 8 97; Z_to_bv 8 66]. split; [reflexivity|]. change (78700 + 4 * 15) with 78760.
apply (ro_cells_image rsegs m 78760 [Z_to_bv 8 16; Z_to_bv 8 221; Z_to_bv 8 97; Z_to_bv 8 66] MI); [vm_compute; reflexivity | lia | cbn; lia].
Qed.

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

Ltac close_ctxE EFS MU := unfold sbctx, sbWX, SBSTATE_SIZEOF, BITS_SIZEOF, HOUT_BYTES; rewrite ?EFS; repeat match goal with |- _ /\ _ => split end; first [close_goal MU | congruence].

#[using="RCEIL k IH"] Lemma FS40_mode : FS = 40 -> mo = ModeWB /\ True.
Proof. intros E. pose proof (ih_inv0 _ _ IH) as sfP_; first [ sf_destruct 5%nat sfP_ as Hmo _ _ E2 _ | sf_fb; destruct sfP_ as (Hmo & _ & _ & E2 & _) ]. rewrite E2 in E. destruct Hmo as [M|M]; rewrite M in E |- *; cbn in E; [split; [reflexivity| exact I] | lia]. Qed.
#[using="RCEIL k IH"] Lemma FS80_mode : FS = 80 -> mo = ModeUWB /\ True.
Proof. intros E. pose proof (ih_inv0 _ _ IH) as sfP_; first [ sf_destruct 5%nat sfP_ as Hmo _ _ E2 _ | sf_fb; destruct sfP_ as (Hmo & _ & _ & E2 & _) ]. rewrite E2 in E. destruct Hmo as [M|M]; rewrite M in E |- *; cbn in E; [lia | split; [reflexivity| exact I]]. Qed.

Local Ltac fdec := (bnorm; bdec; first [ lit_if | sh_if | if_false_z | if_true_z ]).
Local Ltac fupto p := repeat (tryif ub_at_pc p then fail else (tryif ub_at_if then fdec else (zstep))).

Definition fold_post (PS PD : Z) (N : nat) (ss : list word) (B S5 O T : Z)
(xra xsp xs0 xs1 s4 s6 s7 s9 s10 s11 t4 t5 t6 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (dws : list word) (xt0 xt1 xa6 xa7 : word),
ms' = MS (mkR xra xsp gp tp xt0 xt1 (Z_to_bv 64 O) xs0 xs1 (Z_to_bv 64 (Z.of_nat N)) (Z_to_bv 64 (Z.of_nat N)) (Z_to_bv 64 (4 * Z.of_nat N))
(Z_to_bv 64 (Z.of_nat N)) (Z_to_bv 64 (2^64 - 1 - PD)) (Z_to_bv 64 (PD + 4)) xa6 xa7
(Z_to_bv 64 (Z.of_nat N)) (Z_to_bv 64 B) s4 (Z_to_bv 64 S5) s6 s7 (Z_to_bv 64 PD) s9 s10 s11 (Z_to_bv 64 T) t4 t5 t6)
F' (Z_to_bv 64 0x2f8b8) fc' None m' (seg_rom rsegs)
/\ munch [(PD, PD + 4 * Z.of_nat N)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ frm0 fc'
/\ rw_cells rsegs m' PD (f32 dws) /\ length dws = N /\ rw_cells rsegs m' PS (f32 ss) /\ length ss = N.

#[using="Type"] Lemma fold_loop : forall (PS PD : Z) (N : nat) (B S5 O T : Z) (fv : word)
(xra xsp xs0 xs1 s4 s6 s7 s9 s10 s11 t4 t5 t6 : word)
(mN : mem) (p : nat) srest sdone rest done (j q : Z) (t0 t1 a6 a7 : word) F fc m,
length srest = (2 * p + 2)%nat -> length rest = length srest -> length sdone = length done -> (length done + length srest = N)%nat ->
j = Z.of_nat (length done) -> q = 4 * j -> PS = S5 + 4 * B ->
0 <= B -> B + Z.of_nat N < 2^31 -> 0 < S5 -> S5 mod 4 = 0 -> PS + 4 * Z.of_nat N < 2^64 -> 0 < O < 2^64 ->
0 <= PD -> PD + 4 * Z.of_nat N < 2^64 -> apart PD (4 * Z.of_nat N) PS (4 * Z.of_nat N) ->
apart PD (4 * Z.of_nat N) (bv_unsigned xs0 + -176) 8 -> apart PD (4 * Z.of_nat N) (T + 32) 4 ->
mem_inv rsegs m -> munch [(PD, PD + 4 * Z.of_nat N)] mN m -> wmono rsegs mN m -> frm0 fc ->
rw_cells rsegs m (bv_unsigned xs0 + -176) [C8 (Z_to_bv 64 1)] -> rw_cells rsegs m (T + 32) [C4 fv] ->
rw_cells rsegs m PD (f32 done) -> rw_cells rsegs m (PD + q) (f32 rest) ->
rw_cells rsegs m PS (f32 sdone) -> rw_cells rsegs m (PS + q) (f32 srest) ->
evt rsegs (fold_post PS PD N (sdone ++ srest) B S5 O T xra xsp xs0 xs1 s4 s6 s7 s9 s10 s11 t4 t5 t6 mN)
(MS (mkR xra xsp gp tp t0 t1 (Z_to_bv 64 O) xs0 xs1 (Z_to_bv 64 (Z.of_nat N)) (Z_to_bv 64 j) (Z_to_bv 64 q) (Z_to_bv 64 j)
(Z_to_bv 64 (2^64 - 1 - PD)) (Z_to_bv 64 (PD + 4)) a6 a7
(Z_to_bv 64 (Z.of_nat N)) (Z_to_bv 64 B) s4 (Z_to_bv 64 S5) s6 s7 (Z_to_bv 64 PD) s9 s10 s11 (Z_to_bv 64 T) t4 t5 t6)
F (Z_to_bv 64 0x2f7ec) fc None m (seg_rom rsegs)).
Proof.
intros PS PD N B S5 O T fv xra xsp xs0 xs1 s4 s6 s7 s9 s10 s11 t4 t5 t6 mN.
induction p as [|p IHp]; intros srest sdone rest done j q t0 t1 a6 a7 F fc m Ls Lr Lsd LN Hj Hq HPS B0 BN S50 S54 PSN O0 PD0 PDN AP AP1 AP2 MI MU WM FRM C1 CT DONE YR SDONE XR;
(destruct srest as [|x1 [|x2 srest']]; try (cbn in Ls; lia)); (destruct rest as [|y1 [|y2 rest']]; try (cbn in Lr; lia));
cbn [length] in Ls, Lr, LN;
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ YR) as BY; rewrite cells_size_f32 in BY; cbn [length] in BY;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
pose proof (rw_cells_bound _ _ _ _ SDONE) as BS; rewrite cells_size_f32 in BS;
unfold apart in AP, AP1, AP2; rewrite !f32_cons, ?f32_nil in XR; rewrite !f32_cons, ?f32_nil in YR.
- destruct srest'; [| cbn in Ls; lia]. destruct rest'; [| cbn in Lr; lia]. rewrite f32_nil in XR, YR. cbn [length] in *.
(zstep; zstep; zstep). rewrite (swrap32_small (B + j)) by lia. rewrite bv_eqb_same_k. cbn [negb]. cbv iota. (zstep; zstep; zstep; zstep). zstep. fdec. fupto 0x2f8b4. destruct (ex_intro (fun z => z = PS + q) _ eq_refl) as [Qs EQs]. rewrite <- EQs in *. destruct (ex_intro (fun z => z = PD + q) _ eq_refl) as [Qd EQd]. rewrite <- EQd in *. rewrite ?(Z.shiftl_mul_pow2 (B + j) 2) by lia. change (2 ^ 2) with 4 in *. replace (S5 + (B + j) * 4) with Qs by lia. zstep. fupto 0x2f8b4. rewrite <- EQd. zstep. fupto 0x2f8b4. replace ((B + j + 1) * 4 + S5) with (Qs + 4) by lia. zstep. fupto 0x2f8b4. replace (PD + 4 + q) with (Qd + 4) by lia. zstep. fupto 0x2f8b4. zstep. rewrite lts_lit_k by lia. replace (j + 2 <? Z.of_nat N) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
rewrite (swrap32_small (j + 2)) by lia.
replace (j + 2) with (Z.of_nat N) by lia. replace (q + 8) with (4 * Z.of_nat N) by lia.
unfold fold_post.
chunk_uncons XR as X1. chunk_snoc SDONE X1. chunk_snoc SDONE XR. rewrite <- app_assoc in SDONE. cbn [app] in SDONE.
chunk_uncons YR as Y1. chunk_snoc DONE Y1. chunk_snoc DONE YR. rewrite <- app_assoc in DONE. cbn [app] in DONE.
lazymatch type of DONE with rw_cells _ _ _ (f32 ?d ++ [C4 ?u; C4 ?v]) => replace (f32 d ++ [C4 u; C4 v]) with (f32 (d ++ [u; v])) in DONE by (rewrite f32_app; reflexivity) end.
lazymatch type of SDONE with rw_cells _ _ _ (f32 ?d ++ [C4 ?u; C4 ?v]) => replace (f32 d ++ [C4 u; C4 v]) with (f32 (d ++ [u; v])) in SDONE by (rewrite f32_app; reflexivity) end.
finish.
+ exact DONE.
+ rewrite length_app. cbn [length]. lia.
+ rewrite length_app. cbn [length]. lia.
- cbn [length] in *.
(zstep; zstep; zstep). rewrite (swrap32_small (B + j)) by lia. rewrite bv_eqb_same_k. cbn [negb]. cbv iota. (zstep; zstep; zstep; zstep). zstep. fdec. fupto 0x2f8b4. destruct (ex_intro (fun z => z = PS + q) _ eq_refl) as [Qs EQs]. rewrite <- EQs in *. destruct (ex_intro (fun z => z = PD + q) _ eq_refl) as [Qd EQd]. rewrite <- EQd in *. rewrite ?(Z.shiftl_mul_pow2 (B + j) 2) by lia. change (2 ^ 2) with 4 in *. replace (S5 + (B + j) * 4) with Qs by lia. zstep. fupto 0x2f8b4. rewrite <- EQd. zstep. fupto 0x2f8b4. replace ((B + j + 1) * 4 + S5) with (Qs + 4) by lia. zstep. fupto 0x2f8b4. replace (PD + 4 + q) with (Qd + 4) by lia. zstep. fupto 0x2f8b4. zstep. rewrite lts_lit_k by lia. replace (j + 2 <? Z.of_nat N) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
rewrite (swrap32_small (j + 2)) by lia.
chunk_uncons XR as X1. chunk_uncons XR as X2. chunk_snoc SDONE X1. chunk_snoc SDONE X2. rewrite <- app_assoc in SDONE. cbn [app] in SDONE.
chunk_uncons YR as Y1. chunk_uncons YR as Y2. chunk_snoc DONE Y1. chunk_snoc DONE Y2. rewrite <- app_assoc in DONE. cbn [app] in DONE.
lazymatch type of DONE with rw_cells _ _ _ (f32 ?d ++ [C4 ?u; C4 ?v]) => replace (f32 d ++ [C4 u; C4 v]) with (f32 (d ++ [u; v])) in DONE by (rewrite f32_app; reflexivity) end.
lazymatch type of SDONE with rw_cells _ _ _ (f32 ?d ++ [C4 ?u; C4 ?v]) => replace (f32 d ++ [C4 u; C4 v]) with (f32 (d ++ [u; v])) in SDONE by (rewrite f32_app; reflexivity) end.
replace (sdone ++ x1 :: x2 :: srest') with ((sdone ++ [x1; x2]) ++ srest') by (rewrite <- app_assoc; reflexivity).
subst Qs Qd.
eapply (IHp srest' (sdone ++ [x1; x2]) rest' (done ++ [_; _]) (j + 2) (q + 8)).
all: try eassumption.
all: first [ exact_at XR | exact_at YR | rewrite ?length_app; cbn [length] in *; lia ].
Qed.

Definition dadd_post (PD PI : Z) (is : list word)
(xra xsp xs0 xs1 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 t0 t1 t2 t3 t4 t5 t6 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (dws : list word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 160) (Z_to_bv 64 (2^64 - 1 - PD)) (Z_to_bv 64 (2^64 - 1 - PI)) (Z_to_bv 64 160)
(Z_to_bv 64 (PD + 160)) a5 a6 a7 (Z_to_bv 64 0) s3 (Z_to_bv 64 (PI + 160)) s5 s6 s7 s8 s9 s10 (Z_to_bv 64 0) t3 t4 t5 t6)
F' (Z_to_bv 64 0x2f778) fc' None m' (seg_rom rsegs)
/\ munch [(PD, PD + 160)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ frm0 fc'
/\ rw_cells rsegs m' PD (f32 dws) /\ length dws = 40%nat /\ rw_cells rsegs m' PI (f32 is) /\ length is = 40%nat.

#[using="Type"] Lemma dadd_loop : forall (PD PI : Z) (xra xsp xs0 xs1 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 t0 t1 t2 t3 t4 t5 t6 : word)
(mN : mem) rest irest idone done (q r : Z) F fc m,
(length done + length rest = 40)%nat -> length irest = length rest -> length idone = length done -> (1 <= length rest)%nat ->
q = PD + 4 * Z.of_nat (length done) -> r = PI + 4 * Z.of_nat (length done) ->
0 <= PD -> 0 <= PI -> PD + 160 < 2^64 -> PI + 160 < 2^64 -> apart PD 160 PI 160 ->
mem_inv rsegs m -> munch [(PD, PD + 160)] mN m -> wmono rsegs mN m -> frm0 fc ->
rw_cells rsegs m PD (f32 done) -> rw_cells rsegs m q (f32 rest) ->
rw_cells rsegs m PI (f32 idone) -> rw_cells rsegs m r (f32 irest) ->
evt rsegs (dadd_post PD PI (idone ++ irest) xra xsp xs0 xs1 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 t0 t1 t2 t3 t4 t5 t6 mN)
(MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 (4 * Z.of_nat (length done))) (Z_to_bv 64 (2^64 - 1 - PD)) (Z_to_bv 64 (2^64 - 1 - PI)) (Z_to_bv 64 160)
(Z_to_bv 64 q) a5 a6 a7 (Z_to_bv 64 (Z.of_nat (length rest))) s3 (Z_to_bv 64 r) s5 s6 s7 s8 s9 s10 (Z_to_bv 64 (Z.of_nat (length rest))) t3 t4 t5 t6)
F (Z_to_bv 64 0x2f740) fc None m (seg_rom rsegs)).
Proof.
intros PD PI xra xsp xs0 xs1 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 t0 t1 t2 t3 t4 t5 t6 mN.
induction rest as [|y rest IHr]; intros irest idone done q r F fc m LN Li Lid L1 Hq Hr P0 I0 E64 I64 AP MI MU WM FRM DONE YR IDONE XR;
[cbn in L1; lia|].
destruct irest as [|x irest']; [cbn in Li; lia|]. cbn [length] in LN, Li, L1.
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX.
pose proof (rw_cells_bound _ _ _ _ YR) as BY; rewrite cells_size_f32 in BY; cbn [length] in BY.
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD.
pose proof (rw_cells_bound _ _ _ _ IDONE) as BS; rewrite cells_size_f32 in BS.
unfold apart in AP. rewrite !f32_cons in XR. rewrite !f32_cons in YR.
zstep. cbn [length]. if_false_z. zstep. if_false_z. zstep. if_false_z. zstep. if_false_z.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
destruct rest as [|y' rest'].
- destruct irest'; [| cbn in Li; lia]. rewrite f32_nil in XR, YR.
cbn [length] in *.
if_false_z.
replace (q + 4) with (PD + 160) by lia. replace (r + 4) with (PI + 160) by lia.
replace (4 * Z.of_nat (length done) + 4) with 160 by lia. replace (Z.of_nat 1 + -1) with 0 by lia.
unfold dadd_post.
chunk_snoc IDONE XR. apply f32_snoc1' in IDONE.
chunk_snoc DONE YR. apply f32_snoc1' in DONE.
finish.
all: first [ exact DONE | rewrite length_app; cbn [length]; lia | f_equal; f_equal; lia ].
- destruct irest' as [|x' irest'']; [cbn in Li; lia|]. cbn [length] in *.
if_true_z.
chunk_uncons XR as X1. chunk_snoc IDONE X1. apply f32_snoc1' in IDONE.
chunk_uncons YR as Y1. chunk_snoc DONE Y1. apply f32_snoc1' in DONE.
replace (idone ++ x :: x' :: irest'') with ((idone ++ [x]) ++ x' :: irest'') by (rewrite <- app_assoc; reflexivity).
replace (4 * Z.of_nat (length done) + 4) with (4 * Z.of_nat (length (done ++ [fadd_s RNE (nan_box (low32 y)) (nan_box (low32 x))]))) by (rewrite length_app; cbn [length]; lia).
replace (Z.of_nat (Datatypes.S (Datatypes.S (length rest'))) + -1) with (Z.of_nat (length (y' :: rest'))) by (cbn [length]; lia).
eapply (IHr (x' :: irest'') (idone ++ [x]) (done ++ [fadd_s RNE (nan_box (low32 y)) (nan_box (low32 x))]) (q + 4) (r + 4)).
all: try eassumption.
all: first [ rewrite !f32_cons; exact_at XR | rewrite f32_cons; exact_at YR | rewrite ?length_app; cbn [length] in *; lia ].
Qed.

Definition at_L2_40 (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (r : smrec) (sub : Z) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xa0 xs2 xs3 xs4 xs9 xs11 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe) (vpi ver vq viq vak vexc : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -672)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
xa0 (c_a1 kk) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
xs2 xs3 xs4 (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 (18446744073709551615 - (usp + -512))) (Z_to_bv 64 160)
(Z_to_bv 64 (usp + -672)) xs9 (Z_to_bv 64 (usp + -512)) xs11
(c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2f8b8) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -672) /\ frame_at X m fr
/\ lframe X fr dtx /\ f_136 fr = Z_to_bv 64 (usp + -512) /\ f_168 fr = Z_to_bv 64 (OUT + 640 + 160 * sub)
/\ f_192 fr = Z_to_bv 64 (sub * 4) /\ f_200 fr = Z_to_bv 64 sub
/\ sb_smrec_at mo (sbd_submodeID s1) = Some r /\ 0 <= sub <= 3
/\ (xs9 = match sbd_innov_save s0 with None => Z_to_bv 64 0 | Some _ => Z_to_bv 64 (OUT + 1280 + 320 * sub) end)
/\ rw_cells rsegs m (usp + -400) (f32 vpi) /\ length vpi = 4%nat
/\ rw_cells rsegs m (usp + -416) (f32 ver) /\ length ver = 4%nat
/\ rw_cells rsegs m (usp + -448) (f32 vq) /\ length vq = 8%nat
/\ rw_cells rsegs m (usp + -480) (f32 viq) /\ length viq = 8%nat
/\ rw_cells rsegs m (usp + -512) (f32 vak) /\ length vak = 8%nat
/\ rw_cells rsegs m (usp + -672) (f32 vexc) /\ length vexc = 40%nat.

Definition at_L2_80 (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (r : smrec) (sub : Z) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xa0 xs2 xs3 xs4 xs9 xs11 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe) (vpi ver vq viq vak vexc : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -832)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
xa0 (c_a1 kk) (c_a2 kk) (c_a3 kk) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
xs2 xs3 xs4 (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 (18446744073709551615 - (usp + -512))) (Z_to_bv 64 320)
(Z_to_bv 64 (usp + -832)) xs9 (Z_to_bv 64 (usp + -512)) xs11
(c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x2f8b8) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -832) /\ frame_at X m fr
/\ lframe X fr dtx /\ f_136 fr = Z_to_bv 64 (usp + -512) /\ f_168 fr = Z_to_bv 64 (OUT + 1280 + 320 * sub)
/\ f_192 fr = Z_to_bv 64 (sub * 4) /\ f_200 fr = Z_to_bv 64 sub
/\ sb_smrec_at mo (sbd_submodeID s1) = Some r /\ 0 <= sub <= 3
/\ (xs9 = match sbd_innov_save s0 with None => Z_to_bv 64 0 | Some _ => Z_to_bv 64 (OUT + 2560 + 640 * sub) end)
/\ rw_cells rsegs m (usp + -400) (f32 vpi) /\ length vpi = 4%nat
/\ rw_cells rsegs m (usp + -416) (f32 ver) /\ length ver = 4%nat
/\ rw_cells rsegs m (usp + -448) (f32 vq) /\ length vq = 8%nat
/\ rw_cells rsegs m (usp + -480) (f32 viq) /\ length viq = 8%nat
/\ rw_cells rsegs m (usp + -512) (f32 vak) /\ length vak = 8%nat
/\ rw_cells rsegs m (usp + -832) (f32 vexc) /\ length vexc = 80%nat.

#[using="RCEIL k IH"] Lemma sbL2f_40 : FS = 40 -> forall low dtx s1 r sub b ms, sm_innovation_unquant (smr_sm r) = None ->
at_L1_40 X low dtx s1 r sub b ms -> evt rsegs (at_L2_40 low dtx s1 r sub (ub b 5)) ms.
Proof.
intros EFS low dtx s1 r sub b ms HKI AT.
first [ sf_destruct 43%nat AT as Fx fc m kk xra xa0 xs9 xs11 j ows stb fr vpi ver vq viq vak vexc -> FRM CTX ST FRA LFR F136e F168e F192e F200e SAT Hsub Exs9 VPI Lvpi VER Lver VQ Lvq VIQ Lviq VAK Lvak VEXC Lvexc | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & xs9 & xs11 & j & ows & stb & fr & vpi & ver & vq & viq & vak & vexc & -> & FRM & CTX & ST & FRA & LFR & F136e & F168e & F192e & F200e & SAT & Hsub & Exs9 & VPI & Lvpi & VER & Lver & VQ & Lvq & VIQ & Lviq & VAK & Lvak & VEXC & Lvexc) ].
pose proof LFR as sfP_; first [ sf_destruct 25%nat sfP_ as F0e F8e F16e F24e F32e F40e F56e F64e F72e F80e F88e F96e F104e F112e F120e F128e F144e F152e F160e F176e F184e F208e F216e Fdtx DTX01 | sf_fb; destruct sfP_ as (F0e & F8e & F16e & F24e & F32e & F40e & F56e & F64e & F72e & F80e & F88e & F96e & F104e & F112e & F120e & F128e & F144e & F152e & F160e & F176e & F184e & F208e & F216e & Fdtx & DTX01) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ Iffs1 _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & Iffs1 & _ & Inb1 & Ilpc1 & _) ].
assert (Hfs1 : sbd_frame_size s1 = 4 * FS) by (rewrite Efr; exact Hfs).
rewrite EFS in *.
pose proof INV0 as (Imo & _).
pose proof (USPk _ _ IH (-672) ltac:(lia)) as USPX.
set (id := sbd_submodeID s1) in *.
first [ pose proof (sb_smrec_at_some mo id r SAT) as sfP_; sf_destruct 6%nat sfP_ as INr SMS Hid SPE LSPH UWBN | sf_fb; destruct (sb_smrec_at_some mo id r SAT) as (INr & SMS & Hid & SPE & LSPH & UWBN) ].

assert (SUBPok : 0 < SUBP mo < 2^62 /\ SUBP mo mod 8 = 0) by (destruct Imo as [E|E]; rewrite E; vm_compute; repeat split; reflexivity).
assert (AL0 : (SUBP mo + 8 * id) mod 8 = 0) by (replace (SUBP mo + 8 * id) with (SUBP mo + id * 8) by lia; rewrite Z.mod_add by lia; lia).
pose proof (sb_smrecs_ptr r INr) as (RLO & RHI & RAL). unfold RTABLES_LO, RTABLES_HI in RLO, RHI.
zstep. rewrite (sx32_lit id) by lia. zstep. rewrite Emo. zstep. zstep. rewrite (Z.shiftl_mul_pow2 id 3) by lia. change (2 ^ 3) with 8.
replace (SUBP mo + id * 8) with (SUBP mo + 8 * id) by lia.
zstep. zstep. zstep. if_false_z.
zstep. zstep. zstep. zstep. zstep. rewrite (lxor_sign_nn id) by lia. bdec. lit_if.
zstep. if_false_z.
zstep. zstep. rewrite (land7_al _ AL0). if_false_z.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (sb_sub_ptr_read mm mo id _ (sb_tables_of_pristine mm TP) Imo ltac:(lia) eq_refl) as RD;
pose proof (sb_tables_of_pristine mm TP) as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ TR _ | sf_fb; destruct sfP_ as (_ & _ & TR & _) ] end.
zstep. clear RD. rewrite SPE.
zstep. if_false_z.
zstep. zstep. rewrite (land7_al _ RAL). if_false_z.
zstep.
pose proof (TR r INr) as SMC. unfold smrec_cells in SMC. cbv zeta in SMC. rewrite HKI in SMC. cbn [innov_entry] in SMC.
unfold A_split_cb_shape_sign_unquant, A_noise_codebook_unquant in SMC.
zstep. clear SMC TR.

zstep. zstep. zstep. zstep. zstep. try if_true_x.

zstep. zstep. rewrite F160e. zstep.
call (X1g7.speex_bits_unpack_unsigned_spec A D b 5); [exact REP | exact BOK | lia | exact MI |].
rewrite (unpack_eta b 5) in *. cbn [fst snd] in *. after_bits REP (ub b 5).
pose proof (ub_ok b 5 BOK ltac:(lia)) as BOK5. pose proof (ub_same b 5) as (U5sz & U5o & U5c).
pose proof (speex_bits_unpack_unsigned_ok b 5 _ _ BOK ltac:(lia) (unpack_eta b 5)) as (_ & Q32 & _).
match goal with H : ?v = Z_to_bv 64 (uv b 5) |- _ => subst v end.
name_post. try rename FRMc into FRM. try rename STc into ST. try rewrite USPX in ST.

zstep. zstep. rewrite (swrap32_small (uv b 5 + -10)) by lia. rewrite (lts_lit_k (uv b 5 + -10) (uv b 5)) by lia.
replace (uv b 5 + -10 <? uv b 5) with true by (symmetry; apply Z.ltb_lt; lia). if_false_x.
zstep. zstep. zstep. zstep.
call ((h_exp _ (ih_hyps _ _ IH)) lo); [rewrite USPX; exact ST | rewrite USPX; unfold EXP_DEPTH; lia | exact MI | exact FRM |].
cbv beta delta [callR]. clear FRM. name_post. rename FRMc into FRM. rename STc into ST. rewrite USPX in ST.

zstep. zstep. zstep. fp_join 0x2f7b8.
{ zstep. if_cases Kc; [apply evt_done; eexists; reflexivity | zstep; apply evt_done; eexists; reflexivity]. }
cbv beta. intros ms1 (Fx1 & ->).

zstep. zstep. zstep. zstep. rewrite F128e, F16e. rewrite Efs. rewrite (sx32_lit 40) by lia. rewrite (lts_zero_lit 40) by lia. if_false_x.
zstep. rewrite F8e. zstep. if_false_z.
zstep. zstep. zstep. zstep. zstep. zstep. zstep.

pose proof (ih_out4 _ _ IH) as OUT4.
assert (TMO : sbmode_struct mo = A_sb_wb_mode) by (rewrite (proj1 (FS40_mode EFS)); reflexivity).
rewrite TMO.
replace (Z.lxor (usp + -672) 18446744073709551615) with (2^64 - 1 - (usp + -672)) by (rewrite zb_lxor_ones by lia; lia).
replace (usp + -668) with (usp + -672 + 4) by lia.
pose proof FL as FLc. chunk_splitk FLc at 26%nat as FLa. clear FLa. chunk_splitk FLc at 1%nat as F208c. clear FLc. rewrite F208e in F208c.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (sb_tables_of_pristine mm TP) as sfP_; first [ sf_destruct 11%nat sfP_ as _ _ _ _ _ _ _ _ _ TWB _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TWB & _) ] end.
unfold sb_wb_mode_cells in TWB. chunk_splitk TWB at 7%nat as TWa. clear TWa. chunk_splitk TWB at 1%nat as TFV. clear TWB.
pose proof (f32_split rsegs _ _ ows (Z.to_nat (160 + 40 * sub)) ltac:(rewrite Lows; lia) XO) as [_ XO2].
pose proof (f32_split rsegs _ _ (skipn (Z.to_nat (160 + 40 * sub)) ows) 40%nat ltac:(rewrite length_skipn, Lows; lia) XO2) as [XSRC _]. clear XO2.
replace (OUT + 4 * Z.of_nat (Z.to_nat (160 + 40 * sub))) with (OUT + 640 + 160 * sub) in XSRC by lia.
assert (LSRC : length (firstn 40%nat (skipn (Z.to_nat (160 + 40 * sub)) ows)) = 40%nat) by (rewrite length_firstn, length_skipn, Lows; lia).
set (src := firstn 40%nat (skipn (Z.to_nat (160 + 40 * sub)) ows)) in *. clearbody src.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (fold_loop (OUT + 640 + 160 * sub) (usp + -672) 40%nat (40 * sub) (OUT + 4 * sbd_frame_size s0) OUT A_sb_wb_mode _
_ _ _ _ _ _ _ _ _ _ _ _ _ mc 19%nat src [] vexc [] 0 0 _ _ _ _ _ _ mc);
[ exact LSRC | rewrite Lvexc, LSRC; reflexivity | reflexivity | cbn [length]; rewrite LSRC; reflexivity | reflexivity | lia
| lia | lia | lia | lia | first [lia | (rewrite Hfs; replace (OUT + 4 * (4 * 40)) with (OUT + 160 * 4) by lia; rewrite Z.mod_add by lia; exact OUT4)]
| lia | lia | lia | lia
| unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| unfold apart; lia | unfold apart, A_sb_wb_mode; lia
| exact MI | apply munch_refl | apply wmono_refl | exact FRM
| exact_at F208c | exact TFV
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at VEXC
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at XSRC | ] end.
cbv beta. clear FRM. try clear VEXC. try clear XSRC. name_post. rename FRMc into FRM. try rename STc into ST.
apply evt_done. unfold at_L2_40.
lazymatch goal with H : rw_cells _ _ (usp + -672) (f32 ?w) |- _ => set (DWS := w) in * end.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _, _, _, _.
exists j, ows, stb, fr, vpi, ver, vq, viq, vak, DWS.
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctxE EFS MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
split; [exact LFR|].
split; [exact F136e|]. split; [exact F168e|]. split; [exact F192e|]. split; [exact F200e|].
split; [exact SAT|]. split; [exact Hsub|]. split; [exact Exs9|].
split; [exact VPI|]. split; [exact Lvpi|]. split; [exact VER|]. split; [exact Lver|]. split; [exact VQ|]. split; [exact Lvq|].
split; [exact VIQ|]. split; [exact Lviq|]. split; [exact VAK|]. split; [exact Lvak|].
split; assumption.

Unshelve. all: exact (Z_to_bv 64 0).
Qed.

End Seg.
