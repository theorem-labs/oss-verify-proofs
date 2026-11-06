(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bj X1cf X1bp X1bs X1c2 X1br.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qp X0pw.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ea X1fl X1m2 X1m3 X1m5 X1fr X1h7 X1go X1hk.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj X1nk X1n7. From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1n8 X1ho X1hm X1hu X1ht X1ih. From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nr. From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1mc X1mv X1mb X1ma X1mw X1mr X1mf.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ff X1g7.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1nt X1rh X1re X1r6.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import UbDec.
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
intros m q memOk qRange.
pose (romb := fun z => match seg_rom rsegs (wa z) with Some v => v | None => Z_to_bv 8 0 end).
set (word4 := map (fun d => romb (78700 + 4 * q + d)) [0; 1; 2; 3]).
exists word4. split; [reflexivity |].
change (ro_cells rsegs m (78700 + 4 * q) [CB (length word4) word4]).
apply ro_cells_image; [exact memOk | | lia | cbn [word4 length map]; lia].
assert (qList : In q (map Z.of_nat (seq 0 16))).
{ apply in_map_iff. exists (Z.to_nat q). split; [lia | apply in_seq; lia]. }
cbn [seq map Z.of_nat] in qList.
repeat (destruct qList as [<- | qList]; [vm_compute; reflexivity |]).
destruct qList.
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
fun ms => exists (Fe : bvmap 5 word) (fce : bv 32) (me : mem) (sums : list word),
ms = MS (mkR xra xsp gp tp t0 t1 t2 xs0 xs1 (Z_to_bv 64 160) (Z_to_bv 64 (2^64 - 1 - PD)) (Z_to_bv 64 (2^64 - 1 - PI))
(Z_to_bv 64 160) (Z_to_bv 64 (PD + 160)) a5 a6 a7
(Z_to_bv 64 0) s3 (Z_to_bv 64 (PI + 160)) s5 s6 s7 s8 s9 s10 (Z_to_bv 64 0) t3 t4 t5 t6)
Fe (Z_to_bv 64 0x2f778) fce None me (seg_rom rsegs)
/\ munch [(PD, PD + 160)] m me /\ wmono rsegs m me /\ mem_inv rsegs me /\ frm0 fce
/\ rw_cells rsegs me PD (f32 sums) /\ length sums = 40%nat /\ rw_cells rsegs me PI (f32 is) /\ length is = 40%nat.

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
intros PD PI xra xsp xs0 xs1 a5 a6 a7 s3 s5 s6 s7 s8 s9 s10 t0 t1 t2 t3 t4 t5 t6 mN rest.
induction rest as [|x more onMore]; intros irest idone done q r F fc m sumLen iLen idLen restPos qAt rAt.
- cbn in restPos. lia.
- destruct irest as [|y imore]; [cbn in iLen; lia|].
  intros PDlo PIlo PDhi PIhi disj memOk munchD monoD frmOk doneC restC idoneC irestC.
  cbn [length] in sumLen, iLen, restPos |- *.
  rewrite f32_cons in restC, irestC.
  unfold apart in disj.
  pose proof (rw_cells_bound _ _ _ _ doneC) as doneB. rewrite cells_size_f32 in doneB.
  pose proof (rw_cells_bound _ _ _ _ idoneC) as idoneB. rewrite cells_size_f32 in idoneB.
  zstep. fdec. fupto 194420.
  remember (fadd_s RNE (nan_box (low32 x)) (nan_box (low32 y))) as v eqn:vDef. clear vDef.
  chunk_uncons restC as vC. chunk_snoc doneC vC. apply f32_snoc1' in doneC.
  chunk_uncons irestC as yC. chunk_snoc idoneC yC. apply f32_snoc1' in idoneC.
  destruct more as [|x2 more2].
  + destruct imore as [|y2 imore2]; [|cbn in iLen; lia].
    cbn [length] in sumLen.
    zstep. fdec.
    replace (4 * Z.of_nat (length done) + 4) with 160 by lia.
    replace (q + 4) with (PD + 160) by lia.
    replace (r + 4) with (PI + 160) by lia.
    change (Z.of_nat (Datatypes.S (length (@nil word))) + -1) with 0.
    finish.
    * exact doneC.
    * rewrite length_app. cbn [length]. lia.
    * rewrite length_app. cbn [length]. lia.
  + destruct imore as [|y2 imore2]; [cbn in iLen; lia|].
    cbn [length] in sumLen, iLen.
    zstep. fdec.
    replace (4 * Z.of_nat (length done) + 4) with (4 * Z.of_nat (length (done ++ [v]))) by (rewrite length_app; cbn [length]; lia).
    replace (Z.of_nat (Datatypes.S (length (x2 :: more2))) + -1) with (Z.of_nat (length (x2 :: more2))) by (cbn [length]; lia).
    rewrite (app_assoc idone [y] (y2 :: imore2)).
    apply onMore; cbn [length] in *; rewrite ?length_app; cbn [length]; try lia; try assumption.
Qed.

Definition at_L2_40 (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (r : smrec) (sub : Z) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fj : bvmap 5 word) (fcj : bv 32) (mj : mem) (cl : iclob) (wra wa0 ws2 ws3 ws4 ws9 ws11 : word)
(jk : sb_junk) (outs : list word) (stw : list byte) (sfr : sframe) (pig erms ql iql akl excs : list word),
ms = MS (mkR wra (Z_to_bv 64 (usp + -672)) gp tp (c_t0 cl) (c_t1 cl) (c_t2 cl) sp (Z_to_bv 64 S)
wa0 (c_a1 cl) (c_a2 cl) (c_a3 cl) (c_a4 cl) (c_a5 cl) (c_a6 cl) (c_a7 cl)
ws2 ws3 ws4 (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 (18446744073709551615 - (usp + -512))) (Z_to_bv 64 160)
(Z_to_bv 64 (usp + -672)) ws9 (Z_to_bv 64 (usp + -512)) ws11 (c_t3 cl) (c_t4 cl) (c_t5 cl) (c_t6 cl))
Fj (Z_to_bv 64 0x2f8b8) fcj None mj (seg_rom rsegs)
/\ frm0 fcj /\ sbctx X true mj s1 low b jk outs stw /\ stk rsegs mj lo (usp + -672) /\ frame_at X mj sfr /\ lframe X sfr dtx
/\ f_136 sfr = Z_to_bv 64 (usp + -512) /\ f_168 sfr = Z_to_bv 64 (OUT + 640 + 160 * sub)
/\ f_192 sfr = Z_to_bv 64 (sub * 4) /\ f_200 sfr = Z_to_bv 64 sub
/\ sb_smrec_at mo (sbd_submodeID s1) = Some r /\ 0 <= sub <= 3
/\ ws9 = match sbd_innov_save s0 with Some _ => Z_to_bv 64 (OUT + 1280 + 320 * sub) | None => Z_to_bv 64 0 end
/\ rw_cells rsegs mj (usp + -400) (f32 pig) /\ length pig = 4%nat /\ rw_cells rsegs mj (usp + -416) (f32 erms) /\ length erms = 4%nat
/\ rw_cells rsegs mj (usp + -448) (f32 ql) /\ length ql = 8%nat /\ rw_cells rsegs mj (usp + -480) (f32 iql) /\ length iql = 8%nat
/\ rw_cells rsegs mj (usp + -512) (f32 akl) /\ length akl = 8%nat /\ rw_cells rsegs mj (usp + -672) (f32 excs) /\ length excs = 40%nat.

Definition at_L2_80 (low : dec_state bptr) (dtx : Z) (s1 : sbd_state bptr) (r : smrec) (sub : Z) (b : bits_st bptr) : machine_state -> Prop :=
fun ms => exists (Fj : bvmap 5 word) (fcj : bv 32) (mj : mem) (cl : iclob) (wra wa0 ws2 ws3 ws4 ws9 ws11 : word)
(jk : sb_junk) (outs : list word) (stw : list byte) (sfr : sframe) (pig erms ql iql akl excs : list word),
ms = MS (mkR wra (Z_to_bv 64 (usp + -832)) gp tp (c_t0 cl) (c_t1 cl) (c_t2 cl) sp (Z_to_bv 64 S)
wa0 (c_a1 cl) (c_a2 cl) (c_a3 cl) (c_a4 cl) (c_a5 cl) (c_a6 cl) (c_a7 cl)
ws2 ws3 ws4 (Z_to_bv 64 (OUT + 4 * sbd_frame_size s0)) (Z_to_bv 64 (18446744073709551615 - (usp + -512))) (Z_to_bv 64 320)
(Z_to_bv 64 (usp + -832)) ws9 (Z_to_bv 64 (usp + -512)) ws11 (c_t3 cl) (c_t4 cl) (c_t5 cl) (c_t6 cl))
Fj (Z_to_bv 64 0x2f8b8) fcj None mj (seg_rom rsegs)
/\ frm0 fcj /\ sbctx X true mj s1 low b jk outs stw /\ stk rsegs mj lo (usp + -832) /\ frame_at X mj sfr /\ lframe X sfr dtx
/\ f_136 sfr = Z_to_bv 64 (usp + -512) /\ f_168 sfr = Z_to_bv 64 (OUT + 1280 + 320 * sub)
/\ f_192 sfr = Z_to_bv 64 (sub * 4) /\ f_200 sfr = Z_to_bv 64 sub
/\ sb_smrec_at mo (sbd_submodeID s1) = Some r /\ 0 <= sub <= 3
/\ ws9 = match sbd_innov_save s0 with Some _ => Z_to_bv 64 (OUT + 2560 + 640 * sub) | None => Z_to_bv 64 0 end
/\ rw_cells rsegs mj (usp + -400) (f32 pig) /\ length pig = 4%nat /\ rw_cells rsegs mj (usp + -416) (f32 erms) /\ length erms = 4%nat
/\ rw_cells rsegs mj (usp + -448) (f32 ql) /\ length ql = 8%nat /\ rw_cells rsegs mj (usp + -480) (f32 iql) /\ length iql = 8%nat
/\ rw_cells rsegs mj (usp + -512) (f32 akl) /\ length akl = 8%nat /\ rw_cells rsegs mj (usp + -832) (f32 excs) /\ length excs = 80%nat.

#[using="RCEIL k IH"] Lemma sbL2f_40 : FS = 40 -> forall low dtx s1 r sub b ms, sm_innovation_unquant (smr_sm r) = None ->
at_L1_40 X low dtx s1 r sub b ms -> evt rsegs (at_L2_40 low dtx s1 r sub (ub b 5)) ms.
Proof.
intros fs40 low dtx s1 r sub b ms noInnov atL1.
unfold at_L1_40 in atL1.
destruct atL1 as (Fx & fc & m & kk & xra & xa0 & xs9 & xs11 & j & ows & stb & fr & vpi & ver & vq & viq & vak & vexc
  & -> & frmOk & ctx & stack & frame & lfr & fr136 & fr168 & fr192 & fr200 & smrecAt & subRange & s9Def
  & piC & piLen & erC & erLen & qC & qLen & iqC & iqLen & akC & akLen & excC & excLen).
open_ihyps IH. open_ctx ctx. rewrite fs40 in *.
destruct (FS40_mode fs40) as [wbMode _].
destruct frame as [frCells frSaves]. unfold sframe_cells in frCells.
pose proof lfr as (l0 & l8 & l16 & l24 & l32 & l40 & l56 & l64 & l72 & l80 & l88 & l96 & l104 & l112 & l120 & l128
  & l144 & l152 & l160 & l176 & l184 & l208 & l216 & ldtx & dtxRange).
assert (recAtWB : sb_smrec_at ModeWB (sbd_submodeID s1) = Some r) by (rewrite <- wbMode; exact smrecAt).
pose proof (sb_smrec_at_some _ _ _ recAtWB) as (inRecs & _ & idRange & ptrEq & _ & _).
pose proof (sb_smrecs_ptr r inRecs) as ptrRange. unfold RTABLES_LO, RTABLES_HI in ptrRange.
pose proof (sb_tables_of_pristine m TP) as tables.
pose proof (sb_sub_ptr_read m ModeWB (sbd_submodeID s1) _ tables (or_introl eq_refl) ltac:(lia) eq_refl) as subRd.
rewrite ptrEq in subRd. change (SUBP ModeWB) with 245272 in subRd.
pose proof tables as (_ & _ & recCells & _). clear tables.
specialize (recCells r inRecs). unfold smrec_cells in recCells. rewrite noInnov in recCells.
(* submode pointer and innovation_unquant slot *)
zstep. rewrite (sx32_lit (sbd_submodeID s1)) by lia.
zstep. rewrite Emo, wbMode. change (SUBP ModeWB) with 245272.
fupto 194432.
clear subRd recCells.
(* folding branch: quant = unpack(bits, 5) *)
zstep. zstep. rewrite l160. zstep.
call (speex_bits_unpack_unsigned_spec A D b 5); [exact REP | exact BOK | lia | exact MI |].
rewrite unpack_eta in PC, POST. cbn [fst snd] in PC, POST. subst x.
pose proof (speex_bits_unpack_unsigned_ok b 5 _ _ BOK ltac:(lia) (unpack_eta b 5)) as (bokU & vRange & _).
pose proof (ub_same b 5) as (ubSz & ubOwn & ubChars).
zstep. rewrite (swrap32_small (uv b 5 + -10)) by lia. zstep. fdec.
fupto 211376.
(* g = exp(...) *)
pose proof (USPk _ _ IH (-672) ltac:(lia)) as usp672.
pose proof (lay_A_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as aStk.
call (h_exp _ (ih_hyps _ _ IH) lo); [rewrite usp672; exact stack | rewrite usp672; unfold EXP_DEPTH; lia | exact MI0 | exact FRM |].
unfold callR. zstep. zstep. zstep.
fp_join 194488.
{ zstep. lazymatch goal with |- context [if ?c then _ else _] => destruct c end.
  - apply evt_done. eexists. reflexivity.
  - zstep. apply evt_done. eexists. reflexivity. }
intros msJ (Fy & ->).
zstep. rewrite Efs. zstep. rewrite l128. zstep. rewrite l16, wbMode. change (sbmode_struct ModeWB) with 245232.
zstep. fdec. zstep. rewrite l8.
fupto 194540.
rewrite (sx32_lit 40) by lia. rewrite (zb_lxor_ones (usp + -672)) by lia.
replace (usp + -668) with (usp + -672 + 4) by lia.
(* the folding loop *)
destruct (f32_split rsegs _ _ ows (Z.to_nat (160 + 40 * sub)) ltac:(lia) XO) as [_ owsRest].
destruct (f32_split rsegs _ _ (skipn (Z.to_nat (160 + 40 * sub)) ows) 40 ltac:(rewrite length_skipn; lia) owsRest) as [owsMid _].
clear owsRest.
replace (OUT + 4 * Z.of_nat (Z.to_nat (160 + 40 * sub))) with (OUT + 4 * sbd_frame_size s0 + 4 * (40 * sub)) in owsMid by lia.
pose proof frCells as frTail. do 26 (let junk := fresh in chunk_uncons frTail as junk; clear junk).
chunk_uncons frTail as f208C. clear frTail. rewrite l208 in f208C.
pose proof (sb_wb_mode_of_pristine _ TP) as wbCells. unfold sb_wb_mode_cells in wbCells.
do 7 (let junk := fresh in chunk_uncons wbCells as junk; clear junk).
chunk_uncons wbCells as gainC. clear wbCells. unfold A_sb_wb_mode in gainC.
pose proof (lay_OUT_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LAY) as outStk.
pose proof (ih_out4 _ _ IH) as out4.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mNow _) =>
  call (fold_loop (OUT + 4 * sbd_frame_size s0 + 4 * (40 * sub)) (usp + -672) 40 (40 * sub) (OUT + 4 * sbd_frame_size s0) OUT 245232
    (Z_to_bv 64 1063675494) _ _ _ _ _ _ _ _ _ _ _ _ _ mNow 19 (firstn 40 (skipn (Z.to_nat (160 + 40 * sub)) ows)) [] vexc [] 0 0
    _ _ _ _ _ _ _) end.
1-28: first [ reflexivity | assumption | apply munch_refl | apply wmono_refl
  | rewrite ?length_firstn, ?length_skipn; cbn [length]; lia
  | apply rw_cells_nil; lia | exact_at f208C | exact_at gainC | exact_at excC | exact_at owsMid
  | unfold apart; lia | lia ].
(* at the join 0x2f8b8 *)
apply evt_done. unfold at_L2_40.
eexists _, _, _, (ICL _ _ _ _ _ _ _ _ _ _ _ _ _ _), _, _, _, _, _, xs9, xs11, j, ows, stb, fr, vpi, ver, vq, viq, vak, _.
split; [reflexivity |].
rewrite usp672 in *.
split; [assumption |].
split; [close_ctxE fs40 MU |].
split; [assumption |].
split; [unfold frame_at; split; assumption |].
repeat (split; [eassumption |]). eassumption.
Qed.

End Seg.
