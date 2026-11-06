(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Plain.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7 X1n8 X1ho X1hm X1hu X1ht X1ih X1nr X1mc X1mv X1mb X1ma X1mw X1mr X1mf.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1ff X1g7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Local Notation rsegs := Plain.M.loaded_segments.
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

Lemma gcqb_cell : forall m q, mem_inv rsegs m -> 0 <= q < 16 -> exists bs, length bs = 4%nat /\ ro_cells rsegs m (78708 + 4 * q) [CB 4 bs].
Proof.
intros m q MI Hq. assert (C : q = 0 \/ q = 1 \/ q = 2 \/ q = 3 \/ q = 4 \/ q = 5 \/ q = 6 \/ q = 7 \/ q = 8 \/ q = 9 \/ q = 10 \/ q = 11 \/ q = 12 \/ q = 13 \/ q = 14 \/ q = 15) by lia.
destruct C as [-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]]]]]]]]].
- exists [Z_to_bv 8 132; Z_to_bv 8 211; Z_to_bv 8 122; Z_to_bv 8 63]. split; [reflexivity|]. change (78708 + 4 * 0) with 78708.
apply (ro_cells_image rsegs m 78708 [Z_to_bv 8 132; Z_to_bv 8 211; Z_to_bv 8 122; Z_to_bv 8 63] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 222; Z_to_bv 8 84; Z_to_bv 8 164; Z_to_bv 8 63]. split; [reflexivity|]. change (78708 + 4 * 1) with 78712.
apply (ro_cells_image rsegs m 78712 [Z_to_bv 8 222; Z_to_bv 8 84; Z_to_bv 8 164; Z_to_bv 8 63] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 80; Z_to_bv 8 83; Z_to_bv 8 215; Z_to_bv 8 63]. split; [reflexivity|]. change (78708 + 4 * 2) with 78716.
apply (ro_cells_image rsegs m 78716 [Z_to_bv 8 80; Z_to_bv 8 83; Z_to_bv 8 215; Z_to_bv 8 63] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 153; Z_to_bv 8 18; Z_to_bv 8 13; Z_to_bv 8 64]. split; [reflexivity|]. change (78708 + 4 * 3) with 78720.
apply (ro_cells_image rsegs m 78720 [Z_to_bv 8 153; Z_to_bv 8 18; Z_to_bv 8 13; Z_to_bv 8 64] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 190; Z_to_bv 8 217; Z_to_bv 8 56; Z_to_bv 8 64]. split; [reflexivity|]. change (78708 + 4 * 4) with 78724.
apply (ro_cells_image rsegs m 78724 [Z_to_bv 8 190; Z_to_bv 8 217; Z_to_bv 8 56; Z_to_bv 8 64] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 143; Z_to_bv 8 54; Z_to_bv 8 114; Z_to_bv 8 64]. split; [reflexivity|]. change (78708 + 4 * 5) with 78728.
apply (ro_cells_image rsegs m 78728 [Z_to_bv 8 143; Z_to_bv 8 54; Z_to_bv 8 114; Z_to_bv 8 64] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 33; Z_to_bv 8 176; Z_to_bv 8 158; Z_to_bv 8 64]. split; [reflexivity|]. change (78708 + 4 * 6) with 78732.
apply (ro_cells_image rsegs m 78732 [Z_to_bv 8 33; Z_to_bv 8 176; Z_to_bv 8 158; Z_to_bv 8 64] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 141; Z_to_bv 8 238; Z_to_bv 8 207; Z_to_bv 8 64]. split; [reflexivity|]. change (78708 + 4 * 7) with 78736.
apply (ro_cells_image rsegs m 78736 [Z_to_bv 8 141; Z_to_bv 8 238; Z_to_bv 8 207; Z_to_bv 8 64] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 126; Z_to_bv 8 58; Z_to_bv 8 8; Z_to_bv 8 65]. split; [reflexivity|]. change (78708 + 4 * 8) with 78740.
apply (ro_cells_image rsegs m 78740 [Z_to_bv 8 126; Z_to_bv 8 58; Z_to_bv 8 8; Z_to_bv 8 65] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 178; Z_to_bv 8 128; Z_to_bv 8 50; Z_to_bv 8 65]. split; [reflexivity|]. change (78708 + 4 * 9) with 78744.
apply (ro_cells_image rsegs m 78744 [Z_to_bv 8 178; Z_to_bv 8 128; Z_to_bv 8 50; Z_to_bv 8 65] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 54; Z_to_bv 8 229; Z_to_bv 8 105; Z_to_bv 8 65]. split; [reflexivity|]. change (78708 + 4 * 10) with 78748.
apply (ro_cells_image rsegs m 78748 [Z_to_bv 8 54; Z_to_bv 8 229; Z_to_bv 8 105; Z_to_bv 8 65] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 29; Z_to_bv 8 61; Z_to_bv 8 153; Z_to_bv 8 65]. split; [reflexivity|]. change (78708 + 4 * 11) with 78752.
apply (ro_cells_image rsegs m 78752 [Z_to_bv 8 29; Z_to_bv 8 61; Z_to_bv 8 153; Z_to_bv 8 65] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 166; Z_to_bv 8 202; Z_to_bv 8 200; Z_to_bv 8 65]. split; [reflexivity|]. change (78708 + 4 * 12) with 78756.
apply (ro_cells_image rsegs m 78756 [Z_to_bv 8 166; Z_to_bv 8 202; Z_to_bv 8 200; Z_to_bv 8 65] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 234; Z_to_bv 8 140; Z_to_bv 8 3; Z_to_bv 8 66]. split; [reflexivity|]. change (78708 + 4 * 13) with 78760.
apply (ro_cells_image rsegs m 78760 [Z_to_bv 8 234; Z_to_bv 8 140; Z_to_bv 8 3; Z_to_bv 8 66] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 125; Z_to_bv 8 95; Z_to_bv 8 44; Z_to_bv 8 66]. split; [reflexivity|]. change (78708 + 4 * 14) with 78764.
apply (ro_cells_image rsegs m 78764 [Z_to_bv 8 125; Z_to_bv 8 95; Z_to_bv 8 44; Z_to_bv 8 66] MI); [vm_compute; reflexivity | lia | cbn; lia].
- exists [Z_to_bv 8 16; Z_to_bv 8 221; Z_to_bv 8 97; Z_to_bv 8 66]. split; [reflexivity|]. change (78708 + 4 * 15) with 78768.
apply (ro_cells_image rsegs m 78768 [Z_to_bv 8 16; Z_to_bv 8 221; Z_to_bv 8 97; Z_to_bv 8 66] MI); [vm_compute; reflexivity | lia | cbn; lia].
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

Definition fold_post (PS PD : Z) (N : nat) (ss : list word)
(xra xsp xs0 xs1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (dws : list word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 (PD + 4 * Z.of_nat N + 4)) (Z_to_bv 64 (PS + 4 * Z.of_nat N + 4)) (Z_to_bv 64 (PS + 4 * Z.of_nat N + 4)) a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x28748) fc' None m' (seg_rom rsegs)
/\ munch [(PD, PD + 4 * Z.of_nat N)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ frm0 fc'
/\ rw_cells rsegs m' PD (f32 dws) /\ length dws = N /\ rw_cells rsegs m' PS (f32 ss) /\ length ss = N.

#[using="Type"] Lemma fold_loop : forall (PS PD : Z) (N : nat) (xra xsp xs0 xs1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
(mN : mem) (p : nat) srest sdone rest done (q r E : Z) F fc m,
length srest = (2 * p + 2)%nat -> length rest = length srest -> length sdone = length done -> (length done + length srest = N)%nat ->
q = PD + 4 * Z.of_nat (length done) + 4 -> r = PS + 4 * Z.of_nat (length done) + 4 -> E = PS + 4 * Z.of_nat N + 4 ->
PD + 4 * Z.of_nat N + 4 < 2^64 -> PS + 4 * Z.of_nat N + 4 < 2^64 -> apart PD (4 * Z.of_nat N) PS (4 * Z.of_nat N) ->
mem_inv rsegs m -> munch [(PD, PD + 4 * Z.of_nat N)] mN m -> wmono rsegs mN m -> frm0 fc ->
rw_cells rsegs m PD (f32 done) -> rw_cells rsegs m (q + -4) (f32 rest) ->
rw_cells rsegs m PS (f32 sdone) -> rw_cells rsegs m (r + -4) (f32 srest) ->
evt rsegs (fold_post PS PD N (sdone ++ srest) xra xsp xs0 xs1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 mN)
(MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 q) (Z_to_bv 64 r) (Z_to_bv 64 E) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x2871c) fc None m (seg_rom rsegs)).
Proof.
intros PS PD N xra xsp xs0 xs1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 mN.
induction p as [|p IHp]; intros srest sdone rest done q r E F fc m Ls Lr Lsd LN Hq Hr HE E64 S64 AP MI MU WM FRM DONE YR SDONE XR; subst E;
(destruct srest as [|x1 [|x2 srest']]; try (cbn in Ls; lia)); (destruct rest as [|y1 [|y2 rest']]; try (cbn in Lr; lia));
cbn [length] in Ls, Lr, LN;
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX;
pose proof (rw_cells_bound _ _ _ _ YR) as BY; rewrite cells_size_f32 in BY; cbn [length] in BY;
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD;
pose proof (rw_cells_bound _ _ _ _ SDONE) as BS; rewrite cells_size_f32 in BS;
unfold apart in AP; rewrite !f32_cons, ?f32_nil in XR; rewrite !f32_cons, ?f32_nil in YR.
- destruct srest'; [| cbn in Ls; lia]. destruct rest'; [| cbn in Lr; lia]. rewrite f32_nil in XR, YR. cbn [length] in *.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_false_x.
replace (q + 8) with (PD + 4 * Z.of_nat N + 4) by lia. replace (r + 8) with (PS + 4 * Z.of_nat N + 4) by lia.
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
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_true_x.
chunk_uncons XR as X1. chunk_uncons XR as X2. chunk_snoc SDONE X1. chunk_snoc SDONE X2. rewrite <- app_assoc in SDONE. cbn [app] in SDONE.
chunk_uncons YR as Y1. chunk_uncons YR as Y2. chunk_snoc DONE Y1. chunk_snoc DONE Y2. rewrite <- app_assoc in DONE. cbn [app] in DONE.
lazymatch type of DONE with rw_cells _ _ _ (f32 ?d ++ [C4 ?u; C4 ?v]) => replace (f32 d ++ [C4 u; C4 v]) with (f32 (d ++ [u; v])) in DONE by (rewrite f32_app; reflexivity) end.
lazymatch type of SDONE with rw_cells _ _ _ (f32 ?d ++ [C4 ?u; C4 ?v]) => replace (f32 d ++ [C4 u; C4 v]) with (f32 (d ++ [u; v])) in SDONE by (rewrite f32_app; reflexivity) end.
replace (sdone ++ x1 :: x2 :: srest') with ((sdone ++ [x1; x2]) ++ srest') by (rewrite <- app_assoc; reflexivity).
eapply (IHp srest' (sdone ++ [x1; x2]) rest' (done ++ [_; _]) (q + 8) (r + 8) (PS + 4 * Z.of_nat N + 4)).
all: try eassumption.
all: first [ exact_at XR | exact_at YR | rewrite ?length_app; cbn [length] in *; lia ].
Qed.

Definition dadd_post (PD PI : Z) (is : list word)
(xra xsp xs0 xs1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (dws : list word),
ms' = MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 (PI + 160)) (Z_to_bv 64 (PD + 160)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 (PI + 160)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (Z_to_bv 64 0x28690) fc' None m' (seg_rom rsegs)
/\ munch [(PD, PD + 160)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ frm0 fc'
/\ rw_cells rsegs m' PD (f32 dws) /\ length dws = 40%nat /\ rw_cells rsegs m' PI (f32 is) /\ length is = 40%nat.

#[using="Type"] Lemma dadd_loop : forall (PD PI : Z) (xra xsp xs0 xs1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
(mN : mem) rest irest idone done (q r E : Z) F fc m,
(length done + length rest = 40)%nat -> length irest = length rest -> length idone = length done -> (1 <= length rest)%nat ->
q = PD + 4 * Z.of_nat (length done) -> r = PI + 4 * Z.of_nat (length done) -> E = PI + 160 ->
PD + 160 < 2^64 -> PI + 160 < 2^64 -> apart PD 160 PI 160 ->
mem_inv rsegs m -> munch [(PD, PD + 160)] mN m -> wmono rsegs mN m -> frm0 fc ->
rw_cells rsegs m PD (f32 done) -> rw_cells rsegs m q (f32 rest) ->
rw_cells rsegs m PI (f32 idone) -> rw_cells rsegs m r (f32 irest) ->
evt rsegs (dadd_post PD PI (idone ++ irest) xra xsp xs0 xs1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 mN)
(MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 E) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 r) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x28674) fc None m (seg_rom rsegs)).
Proof.
intros PD PI xra xsp xs0 xs1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 mN.
induction rest as [|y rest IHr]; intros irest idone done q r E F fc m LN Li Lid L1 Hq Hr HE E64 I64 AP MI MU WM FRM DONE YR IDONE XR;
[cbn in L1; lia|]. subst E.
destruct irest as [|x irest']; [cbn in Li; lia|]. cbn [length] in LN, Li, L1.
pose proof (rw_cells_bound _ _ _ _ XR) as BX; rewrite cells_size_f32 in BX; cbn [length] in BX.
pose proof (rw_cells_bound _ _ _ _ YR) as BY; rewrite cells_size_f32 in BY; cbn [length] in BY.
pose proof (rw_cells_bound _ _ _ _ DONE) as BD; rewrite cells_size_f32 in BD.
pose proof (rw_cells_bound _ _ _ _ IDONE) as BS; rewrite cells_size_f32 in BS.
unfold apart in AP. rewrite !f32_cons in XR. rewrite !f32_cons in YR.
destruct rest as [|y' rest'].
- destruct irest'; [| cbn in Li; lia]. rewrite f32_nil in XR, YR.
zstep. zstep. zstep. zstep. zstep. zstep. zstep.
cbn [length] in *.
replace (q + 4) with (PD + 160) by lia. replace (r + 4) with (PI + 160) by lia. if_false_x.
unfold dadd_post.
chunk_snoc IDONE XR. apply f32_snoc1' in IDONE.
chunk_snoc DONE YR. apply f32_snoc1' in DONE.
finish.
+ exact DONE.
+ rewrite length_app. cbn [length]. lia.
+ rewrite length_app. cbn [length]. lia.
- destruct irest' as [|x' irest'']; [cbn in Li; lia|]. cbn [length] in *.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. if_true_x.
chunk_uncons XR as X1. chunk_snoc IDONE X1. apply f32_snoc1' in IDONE.
chunk_uncons YR as Y1. chunk_snoc DONE Y1. apply f32_snoc1' in DONE.
replace (idone ++ x :: x' :: irest'') with ((idone ++ [x]) ++ x' :: irest'') by (rewrite <- app_assoc; reflexivity).
eapply (IHr (x' :: irest'') (idone ++ [x]) (done ++ [_]) (q + 4) (r + 4) (PI + 160)).
all: try eassumption.
all: first [ rewrite !f32_cons; exact_at XR | rewrite f32_cons; exact_at YR | rewrite ?length_app; cbn [length] in *; lia ].
Qed.

Definition at_L2_40 (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (r : smrec) (sub : Z) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xa0 xs2 xs11 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe) (vpi ver vq viq vak vexc : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -592)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
xa0 (c_a1 kk) (c_a2 kk) (Z_to_bv 64 40) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
xs2 (Z_to_bv 64 (sub * 4)) (Z_to_bv 64 OUT) (Z_to_bv 64 (usp + -368)) (Z_to_bv 64 (usp + -432)) (Z_to_bv 64 (usp + -592))
(Z_to_bv 64 sub) (Z_to_bv 64 0) (Z_to_bv 64 sub) xs11
(c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x28748) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -592) /\ frame_at X m fr
/\ lframe X fr dtx /\ f_104 fr = Z_to_bv 64 (OUT + 640 + 160 * sub) /\ f_112 fr = Z_to_bv 64 (usp + -432)
/\ sb_smrec_at mo (sbd_submodeID s1) = Some r /\ 0 <= sub <= 3
/\ (xs11 = match sbd_innov_save s0 with None => Z_to_bv 64 0 | Some _ => Z_to_bv 64 (OUT + 1280 + 320 * sub) end)
/\ rw_cells rsegs m (usp + -320) (f32 vpi) /\ length vpi = 4%nat
/\ rw_cells rsegs m (usp + -336) (f32 ver) /\ length ver = 4%nat
/\ rw_cells rsegs m (usp + -368) (f32 vq) /\ length vq = 8%nat
/\ rw_cells rsegs m (usp + -400) (f32 viq) /\ length viq = 8%nat
/\ rw_cells rsegs m (usp + -432) (f32 vak) /\ length vak = 8%nat
/\ rw_cells rsegs m (usp + -592) (f32 vexc) /\ length vexc = 40%nat.

Definition at_L2_80 (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (r : smrec) (sub : Z) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (kk : iclob) (xra xa0 xs2 xs11 : word)
(j : sb_junk) (ows : list word) (stb : list byte) (fr : sframe) (vpi ver vq viq vak vexc : list word),
ms = MS (mkR xra (Z_to_bv 64 (usp + -752)) gp tp (c_t0 kk) (c_t1 kk) (c_t2 kk) sp (Z_to_bv 64 S)
xa0 (c_a1 kk) (c_a2 kk) (Z_to_bv 64 80) (c_a4 kk) (c_a5 kk) (c_a6 kk) (c_a7 kk)
xs2 (Z_to_bv 64 (sub * 4)) (Z_to_bv 64 OUT) (Z_to_bv 64 (usp + -368)) (Z_to_bv 64 (usp + -432)) (Z_to_bv 64 (usp + -752))
(Z_to_bv 64 sub) (Z_to_bv 64 0) (Z_to_bv 64 sub) xs11
(c_t3 kk) (c_t4 kk) (c_t5 kk) (c_t6 kk))
Fx (Z_to_bv 64 0x28748) fc None m (seg_rom rsegs)
/\ frm0 fc /\ sbctx X true m s1 low b j ows stb /\ stk rsegs m lo (usp + -752) /\ frame_at X m fr
/\ lframe X fr dtx /\ f_104 fr = Z_to_bv 64 (OUT + 1280 + 320 * sub) /\ f_112 fr = Z_to_bv 64 (usp + -432)
/\ sb_smrec_at mo (sbd_submodeID s1) = Some r /\ 0 <= sub <= 3
/\ (xs11 = match sbd_innov_save s0 with None => Z_to_bv 64 0 | Some _ => Z_to_bv 64 (OUT + 2560 + 640 * sub) end)
/\ rw_cells rsegs m (usp + -320) (f32 vpi) /\ length vpi = 4%nat
/\ rw_cells rsegs m (usp + -336) (f32 ver) /\ length ver = 4%nat
/\ rw_cells rsegs m (usp + -368) (f32 vq) /\ length vq = 8%nat
/\ rw_cells rsegs m (usp + -400) (f32 viq) /\ length viq = 8%nat
/\ rw_cells rsegs m (usp + -432) (f32 vak) /\ length vak = 8%nat
/\ rw_cells rsegs m (usp + -752) (f32 vexc) /\ length vexc = 80%nat.

#[using="RCEIL k IH"] Lemma sbL2f_40 : FS = 40 -> forall low dtx s1 r sub b ms, sm_innovation_unquant (smr_sm r) = None ->
at_L1_40 X low dtx s1 r sub b ms -> evt rsegs (at_L2_40 low dtx s1 r sub (ub b 5)) ms.
Proof.
intros EFS low dtx s1 r sub b ms HKI AT.
first [ sf_destruct 40%nat AT as Fx fc m kk xra xa0 xs11 j ows stb fr vpi ver vq viq vak vexc -> FRM CTX ST FRA LFR F104e F112e SAT Hsub Exs11 VPI Lvpi VER Lver VQ Lvq VIQ Lviq VAK Lvak VEXC Lvexc | sf_fb; destruct AT as (Fx & fc & m & kk & xra & xa0 & xs11 & j & ows & stb & fr & vpi & ver & vq & viq & vak & vexc & -> & FRM & CTX & ST & FRA & LFR & F104e & F112e & SAT & Hsub & Exs11 & VPI & Lvpi & VER & Lver & VQ & Lvq & VIQ & Lviq & VAK & Lvak & VEXC & Lvexc) ].
pose proof LFR as sfP_; first [ sf_destruct 16%nat sfP_ as F0e F8e F16e F24e F32e F40e F48e F56e F64e F72e F80e F88e F96e F120e Fdtx DTX01 | sf_fb; destruct sfP_ as (F0e & F8e & F16e & F24e & F32e & F40e & F48e & F56e & F64e & F72e & F80e & F88e & F96e & F120e & Fdtx & DTX01) ].
open_ihyps IH. open_ctx CTX. destruct FRA as [FL FV]. unfold sframe_cells in FL. unfold fr_saves in FV. cbv zeta in FV.
pose proof INV as sfP_; first [ sf_destruct 7%nat sfP_ as _ _ Iffs1 _ Inb1 Ilpc1 _ | sf_fb; destruct sfP_ as (_ & _ & Iffs1 & _ & Inb1 & Ilpc1 & _) ].
assert (Hfs1 : sbd_frame_size s1 = 4 * FS) by (rewrite Efr; exact Hfs).
rewrite EFS in *.
pose proof INV0 as (Imo & _).
pose proof (USPk _ _ IH (-592) ltac:(lia)) as USPX.
set (id := sbd_submodeID s1) in *.
first [ pose proof (sb_smrec_at_some mo id r SAT) as sfP_; sf_destruct 6%nat sfP_ as INr SMS Hid SPE LSPH UWBN | sf_fb; destruct (sb_smrec_at_some mo id r SAT) as (INr & SMS & Hid & SPE & LSPH & UWBN) ].

zstep. rewrite (sx32_lit id) by lia. zstep. rewrite Emo. zstep. zstep.
rewrite (Z.shiftl_mul_pow2 id 3) by lia. change (2 ^ 3) with 8.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (sb_sub_ptr_read mm mo id _ (sb_tables_of_pristine mm TP) Imo ltac:(lia) eq_refl) as RD;
pose proof (sb_tables_of_pristine mm TP) as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ TR _ | sf_fb; destruct sfP_ as (_ & _ & TR & _) ] end.
replace (SUBP mo + id * 8) with (SUBP mo + 8 * id) by lia.
zstep. clear RD. rewrite SPE.
pose proof (TR r INr) as SMC. unfold smrec_cells in SMC. cbv zeta in SMC. rewrite HKI in SMC. cbn [innov_entry] in SMC.
unfold A_split_cb_shape_sign_unquant, A_noise_codebook_unquant in SMC.
zstep. clear SMC TR.

zstep. try if_true_x.

zstep. zstep. rewrite F120e. zstep.
call (X1g7.speex_bits_unpack_unsigned_spec A D b 5); [exact REP | exact BOK | lia | exact MI |].
rewrite (unpack_eta b 5) in *. cbn [fst snd] in *. after_bits REP (ub b 5).
pose proof (ub_ok b 5 BOK ltac:(lia)) as BOK5. pose proof (ub_same b 5) as (U5sz & U5o & U5c).
pose proof (speex_bits_unpack_unsigned_ok b 5 _ _ BOK ltac:(lia) (unpack_eta b 5)) as (_ & Q32 & _).
match goal with H : ?v = Z_to_bv 64 (uv b 5) |- _ => subst v end.
name_post. try rename FRMc into FRM. try rename STc into ST. try rewrite USPX in ST.

zstep. zstep. zstep. zstep. zstep.
call ((h_exp _ (ih_hyps _ _ IH)) lo); [rewrite USPX; exact ST | rewrite USPX; unfold EXP_DEPTH; lia | exact MI | exact FRM |].
cbv beta delta [callR]. clear FRM. name_post. rename FRMc into FRM. rename STc into ST. rewrite USPX in ST.

zstep. zstep. fp_join 0x286d4.
{ zstep. if_cases Kc; [apply evt_done; eexists; reflexivity | zstep; apply evt_done; eexists; reflexivity]. }
cbv beta. intros ms1 (Fx1 & ->).

zstep. rewrite Efs. rewrite (sx32_lit 40) by lia. zstep. rewrite (lts_zero_lit 40) by lia. if_false_x. zstep.

zstep. rewrite F24e.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
pose proof (sb_tables_of_pristine mm TP) as sfP_; first [ sf_destruct 11%nat sfP_ as _ _ _ _ _ _ _ _ _ TWB TUWB | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & TWB & TUWB) ] end.
rewrite (proj1 (FS40_mode EFS)). cbn [sbmode_struct].
unfold A_sb_wb_mode, A_sb_uwb_mode in TWB, TUWB |- *. cbv delta [sb_wb_mode_cells sb_uwb_mode_cells] in TWB, TUWB.
zstep. clear TWB TUWB.

zstep. rewrite (swrap32_small (40 * sub)) by lia.
zstep. zstep. zstep. zstep. rewrite (Z.shiftl_mul_pow2 (40 * sub) 2) by lia. change (2 ^ 2) with 4.
zstep. zstep. zstep. rewrite F16e. rewrite Hfs. zstep. zstep.
replace (Z.land (Z.shiftl 40 2 + -4) (-8)) with 152 by reflexivity.
zstep. rewrite F8e. rewrite Hfs. zstep. zstep.

pose proof (f32_split rsegs _ _ ows (Z.to_nat (160 + 40 * sub)) ltac:(rewrite Lows; lia) XO) as [_ XO2].
pose proof (f32_split rsegs _ _ (skipn (Z.to_nat (160 + 40 * sub)) ows) 40%nat ltac:(rewrite length_skipn, Lows; lia) XO2) as [XSRC _]. clear XO2.
replace (OUT + 4 * Z.of_nat (Z.to_nat (160 + 40 * sub))) with (OUT + 640 + 160 * sub) in XSRC by lia.
assert (LSRC : length (firstn 40%nat (skipn (Z.to_nat (160 + 40 * sub)) ows)) = 40%nat) by (rewrite length_firstn, length_skipn, Lows; lia).
set (src := firstn 40%nat (skipn (Z.to_nat (160 + 40 * sub)) ows)) in *. clearbody src.
remember (OUT + 640 + 160 * sub) as PSRC eqn:EPS.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
call (fold_loop PSRC (usp + -592) 40%nat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mc 19%nat src [] vexc []);
[ exact LSRC | rewrite Lvexc; symmetry; exact LSRC | reflexivity | cbn [length]; lia | cbn [length]; lia | cbn [length]; subst PSRC; lia | subst PSRC; lia
| lia | subst PSRC; lia | subst PSRC; unfold apart; pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY); lia
| exact MI | apply munch_refl | apply wmono_refl | exact FRM
| rewrite f32_nil; apply rw_cells_nil; lia | exact_at VEXC
| rewrite f32_nil; apply rw_cells_nil; subst PSRC; lia | exact_at XSRC | ] end.
cbv beta. clear FRM. try clear VEXC. clear XSRC. name_post. rename FRMc into FRM. try rename STc into ST.
cbn [app] in *.
replace (PSRC + 4 * Z.of_nat 40%nat + 4) with (OUT + 640 + 160 * sub + 160 + 4) by lia. subst PSRC.
set (XS11V := xs11) in *. set (OWSV := ows) in *.
apply evt_done. unfold at_L2_40.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, XS11V.
lazymatch goal with P : rw_cells _ _ (S + 132) [C4 ?sd] |- _ =>
exists (SBJ (sj_last_ener j) sd (sj_pad1 j) (sj_pad2 j) (sj_g0 j) (sj_g1 j) (sj_exc j) (sj_oq j) (sj_iq j) (sj_msp j) (sj_pg j) (sj_er j)) end.
exists OWSV, stb. eexists (SFR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _). first [ unshelve sf_eexists 5%nat; [ exact (vpi) | exact (ver) | exact (vq) | exact (viq) | exact (vak) | ] | sf_fb; exists vpi, ver, vq, viq, vak ].
lazymatch goal with H : rw_cells _ _ (usp + -592) (f32 ?w) |- _ => exists w end.
split; [reflexivity|]. split; [exact FRM|].
split. { close_ctxE EFS MU. }
split; [exact ST|]. split; [unfold frame_at, fr_saves, sframe_cells; cbv zeta; split; [exact FL | exact FV]|].
split. { exact LFR. }
cbn [f_104 f_112]. split; [exact F104e|]. split; [exact F112e|].
split; [exact SAT|]. split; [exact Hsub|]. split; [exact Exs11|].
split; [exact VPI|]. split; [exact Lvpi|]. split; [exact VER|]. split; [exact Lver|]. split; [exact VQ|]. split; [exact Lvq|].
split; [exact VIQ|]. split; [exact Lviq|]. split; [exact VAK|]. split; [exact Lvak|].
split; [assumption | first [assumption | lia]].

Unshelve. all: exact (Z_to_bv 64 0).
Qed.

End Seg.
