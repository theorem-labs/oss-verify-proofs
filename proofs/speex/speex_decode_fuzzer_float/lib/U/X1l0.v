(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0pw X0qx X0qw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1nl X1m8 X1fr X1no X1np X1h7 X1kd X1k9.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd X1ei.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1oc X1o8 X1rm X1r3 X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation rsegs := X1gj.rsegs.

Ltac ua := change X1ff.rsegs with X1gj.rsegs in *; change U.X1fd.rsegs with X1gj.rsegs in *.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Lemma u64ro_read : forall m A ws (i : Z) w a,
bytes_at rsegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> (0 <= i)%Z -> a = wa (A + 8 * i) ->
ov_read_bytes rsegs m a 8 = Some (le8 w).
Proof.
intros m A ws i w a Hb Hn Hi ->.
first [ pose proof (u64s_split _ _ _ Hn) as sfP_; sf_destruct 6%nat sfP_ as pre post E Hlen Eu Hlu | sf_fb; destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu) ].
replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
rewrite (bytes_at_ov_read rsegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
2:{ rewrite Eu, !app_length, length_le8, Hlu. lia. }
rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

Definition ADP0 (mm : mem) : Prop :=
rw_cells rsegs mm RINITIALIZED [C1 (Z_to_bv 8 0)] /\ rtables_pristine mm.

Definition adp0_addr (a : Z) : Prop := (RINITIALIZED <= a < RINITIALIZED + 1) \/ (RTABLES_LO <= a < RTABLES_HI).

Lemma ADP0_agree : forall (P : Z -> Prop) m m', agree_on rsegs P m m' -> (forall a, adp0_addr a -> P a) -> ADP0 m -> ADP0 m'.
Proof.
intros P m m' AG HP (A1 & A2). unfold ADP0, adp0_addr, RINITIALIZED in *. split.
- eapply rw_cells_agree; [exact AG| exact A1| intros a Ha; apply HP; cbn in Ha; lia].
- eapply rtables_pristine_agree; [exact AG| intros a Ha; apply HP; lia| exact A2].
Qed.
Lemma ADP0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> ADP0 m -> ADP0 m'.
Proof.
intros LB SP m m' HP. apply (ADP0_agree _ _ _ HP). intros a Ha. right; left.
unfold adp0_addr, RINITIALIZED, RTABLES_LO, RTABLES_HI, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma ADP0_munch : forall W m m', munch W m m' -> wmono rsegs m m' -> (forall a, adp0_addr a -> outside W a) -> ADP0 m -> ADP0 m'.
Proof. intros W m m' MU WM HW. apply (ADP0_agree _ _ _ (agree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

Lemma rexit_init : forall m : mem,
(forall a : word, (0x3b000 <= bv_unsigned a < 0x6e000)%Z -> outside rcrt_written (bv_unsigned a) -> m a = None) ->
rw_cells rsegs m RDSO [C8 (Z_to_bv 64 RDSO)] /\ AXSTAT false m.
Proof.
intros m NONE. unfold AXSTAT, RDSO, RAEF_INCB, RATEXIT, RATEXIT_A0, ax_cells. cbn [Z.add].
rimg_chunk0 NONE m 0x3d0e8 [C8 (Z_to_bv 64 0x3d0e8)] H1.
rimg_chunk0 NONE m 0x4d354 [C1 (Z_to_bv 8 0)] H2.
rimg_chunk0 NONE m 0x6d490 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4);
C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] H3.
rimg_chunk0 NONE m 0x6d5b0 [C8 (Z_to_bv 64 0)] H4.
split; [exact H1|]. split; [exact H2|]. split; [exact H3| exact H4].
Qed.

Section A.
Context {RCEIL : RunCeiling}.
Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (TID : Z).
Hypothesis VSP : valid_sp sp0.
Hypothesis HCEIL : alloc_ceiling = LO sp0.
Hypothesis VARGV : valid_argv argv.
Hypothesis VENVP : valid_envp envp.
Hypothesis HT : 0 < TID < 4194304.
Hypothesis RHF : rheap_frame_stmt.
Notation usp0 := (bv_unsigned sp0).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 RATP).
Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
Notation LO' := (LO sp0).

Definition BASE (mm : mem) : Prop :=
stk rsegs mm LO' (usp0 + -128) /\ mem_inv rsegs mm /\ RSTAT TID false mm /\ rauxv_ok mm usp0 /\ bytes_at rsegs mm usp0 IMGB
/\ stderr_wfile0 mm /\ stdout_file mm stdout_init.

#[using="RCEIL VSP VARGV VENVP"] Lemma IMGB_len : usp0 + Z.of_nat (length IMGB) <= 2^64.
Proof.
destruct VSP as (A & B & C). unfold sp_window_lo, sp_window_hi in *.
pose proof (build_stack_bytes_length rph sp0 argv envp uid hw rnd). pose proof (raw_len_nonneg argv envp).
destruct VARGV as (A1 & A2 & _). destruct VENVP as (E1 & E2 & _). unfold raw_len, struct_size, argc, envc in *. lia.
Qed.

#[using="Type"] Lemma BASE_heap_pres : forall LB m m', BASE m -> rheap_pres LB (usp0 + -128) m m' ->
mem_inv rsegs m' -> stk rsegs m' LO' (usp0 + -128) -> rauxv_ok m' usp0 -> BASE m'.
Proof.
intros LB m m' sfH_; first [ sf_destruct 7%nat sfH_ as ST MI RS AUX IMG SE SO | sf_fb; destruct sfH_ as (ST & MI & RS & AUX & IMG & SE & SO) ]; intros HP MI' ST' AUX'.
split; [exact ST'|]. split; [exact MI'|]. split; [eapply RSTAT_heap_pres; [exact HP| exact RS]|]. split; [exact AUX'|].
split; [eapply rheap_pres_bytes_at; [exact HP| exact IMG| left; lia]|].
split; [eapply stderr_wfile0_heap_pres; [exact HP| exact SE]| eapply stdout_file_heap_pres; [exact HP| exact SO]].
Qed.

Definition WOK (iv : Z * Z) : Prop :=
(LO' <= fst iv /\ snd iv <= usp0 + -128) \/ (fst iv = RERRNO /\ snd iv = RERRNO + 4)
\/ (snd iv <= alloc_ceiling /\ (snd iv <= 0x10000 \/ 0x6e000 <= fst iv))
\/ (RSTG <= fst iv /\ snd iv <= RSTG + 65536).

#[using="VSP HCEIL"] Lemma WOK_outside : forall W a, Forall WOK W ->
(usp0 + -128 <= a \/ (0x10000 <= a < 0x6e000 /\ ~ (RERRNO <= a < RERRNO + 4) /\ ~ (RSTG <= a < RSTG + 65536))) -> outside W a.
Proof.
pose proof (sp_facts sp0 VSP HCEIL) as SF. unfold LO in *.
induction W as [|[lo1 hi1] W IH]; intros a HW Ha; cbn; [exact I|].
inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
unfold WOK, LO, RERRNO, RSTG in H1. cbn [fst snd] in H1. unfold RERRNO, RSTG in Ha. lia.
Qed.

#[using="VSP HCEIL VARGV VENVP"] Lemma BASE_munch : forall W m m', BASE m -> Forall WOK W -> munch W m m' -> wmono rsegs m m' ->
mem_inv rsegs m' -> stk rsegs m' LO' (usp0 + -128) -> BASE m'.
Proof.
intros W m m' sfH_; first [ sf_destruct 7%nat sfH_ as ST MI RS AUX IMG SE SO | sf_fb; destruct sfH_ as (ST & MI & RS & AUX & IMG & SE & SO) ]; intros HW MU WM MI' ST'. pose proof (sp_facts sp0 VSP HCEIL) as SF. pose proof IMGB_len as IL. unfold LO in *.
split; [exact ST'|]. split; [exact MI'|].
split; [eapply RSTAT_munch; [exact MU| exact WM| intros a Ha; apply WOK_outside; [exact HW| unfold rstat_addr, RERRNO, RSTG in *; lia]| exact RS]|].
split.
{ eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
eapply Forall_impl; [| exact HW]. intros [lo1 hi1] H. unfold WOK, RERRNO, RAUXV_CELL, RLIBC, LO, RSTG in *. cbn [fst snd] in *. lia. }
split.
{ eapply bytes_at_agree; [eapply agree_on_of_munch; [exact MU| exact WM]| exact IMG|]. intros a Ha. cbn. apply WOK_outside; [exact HW| left; lia]. }
split.
- eapply stderr_wfile0_munch; [exact MU| exact WM| | exact SE]. intros a Ha. apply WOK_outside; [exact HW| unfold stderr_addr, RERRNO, RSTG in *; lia].
- eapply stdout_file_munch; [exact MU| exact WM| | exact SO]. intros a Ha. apply WOK_outside; [exact HW| unfold stdout_addr, RERRNO, RSTG in *; lia].
Qed.

#[using="VSP HCEIL"] Lemma ADP0_munchW : forall W m m', Forall WOK W -> munch W m m' -> wmono rsegs m m' -> ADP0 m -> ADP0 m'.
Proof.
intros W m m' HW MU WM. apply (ADP0_munch _ _ _ MU WM). intros a Ha. apply WOK_outside; [exact HW| unfold adp0_addr, RINITIALIZED, RTABLES_LO, RTABLES_HI, RERRNO, RSTG in *; lia].
Qed.

#[using="VSP HCEIL RHF"] Lemma RHEAP_munchW : forall s LB W m m', Forall WOK W -> munch W m m' -> wmono rsegs m m' ->
(forall iv, In iv W -> snd iv <= alloc_ceiling -> (snd iv <= 0x10000 \/ 0x6e000 <= fst iv) ->
exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) ->
RHEAP s LB m -> RHEAP s LB m'.
Proof.
intros s LB W m m' HW MU WM HB HP. pose proof (sp_facts sp0 VSP HCEIL) as SF. unfold LO in *.
eapply RHF; [exact HP| exact MU| exact WM|].
apply Forall_forall. intros [lo1 hi1] Hin. pose proof (proj1 (Forall_forall _ _) HW _ Hin) as H.
unfold WOK, rclient_write_ok, RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RREPLACED, LO, RSTG in *. cbn [fst snd] in *.
destruct H as [H|[H|[H|H]]]; [left; lia| right; left; lia| right; right| right; left; lia]. apply (HB (lo1, hi1)); [exact Hin| cbn; lia| cbn; lia].
Qed.

#[using="RCEIL VSP HCEIL"] Lemma main_prologue : forall (Q : machine_state -> Prop) (ra s0 s1 a0 a1 a2 s2 s3 t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem),
stk rsegs m LO' (usp0 + -48) -> mem_inv rsegs m ->
(forall m' pad, rw_cells rsegs m' (usp0 + -128) [CB 8 pad; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] -> stk rsegs m' LO' (usp0 + -128) ->
munch [(usp0 - 128, usp0 - 48)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
evt rsegs Q (MS (mkR ra (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1bcb4) fc None m' (seg_rom rsegs))) ->
evt rsegs Q (MS (mkR ra (Z_to_bv 64 (usp0 + -48)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1bc88) fc None m (seg_rom rsegs)).
Proof.
intros until m. intros ST MI K. pose proof (sp_facts sp0 VSP HCEIL) as SF. unfold LO in *.
pose proof (munch_refl [(usp0 - 128, usp0 - 48)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
zstep. carve_frame 80%nat ST.
do 10 zstep.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => eapply (K mx) end; [exact FR| exact ST| exact MU| exact WM| assumption].
Qed.

Definition P1 (F : bvmap 5 word) (ms : machine_state) : Prop :=
exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (fc : bv 32) (mm : mem) (pad : list byte),
ms = MS (mkR (Z_to_bv 64 0x310d0) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
(Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
(Z_to_bv 64 0x1bc88) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1bcb8) fc None mm (seg_rom rsegs)
/\ MFRAME sp0 argv mm pad s7 s6 s5 s4 /\ BASE mm /\ RHEAP (ps_init alloc_ceiling (reservedZ rsegs)) [] mm /\ ADP0 mm
/\ rw_cells rsegs mm RERRNO [C4 (Z_to_bv 64 0)] /\ frm0 fc
/\ (exists stg, rw_cells rsegs mm RSTG [CB (Z.to_nat 65536) stg]).
End A.

Section A2.
Context {RCEIL : RunCeiling}.
Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (F : bvmap 5 word).
Hypothesis VSP : valid_sp sp0.
Hypothesis HCEIL : alloc_ceiling = LO sp0.
Hypothesis HSEC : run_secret = rnd_w1 rnd.
Hypothesis HCAN : run_canary = canary_of (rnd_w0 rnd).
Hypothesis VARGV : valid_argv argv.
Hypothesis VENVP : valid_envp envp.
Hypothesis RHI : rheap_init_stmt.
Hypothesis RHF : rheap_frame_stmt.
Hypothesis FPR : @fprintf_diag_stmt PState.
Hypothesis FWX : fwritex_stderr_stmt.
Hypothesis SWF : stdio_write_flush_stmt.
Notation usp0 := (bv_unsigned sp0).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 RATP).
Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).
Notation LO' := (LO sp0).

#[using="VSP HCEIL HSEC HCAN VARGV VENVP RHI RHF"] Lemma main_to_test : forall (ms : machine_state) (Q : machine_state -> Prop),
rat_main sp0 argv envp uid hw rnd F ms ->
(forall (TID : Z) (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (mm : mem) (pad : list byte),
0 < TID < 4194304 ->
MFRAME sp0 argv mm pad s7 s6 s5 s4 -> BASE sp0 argv envp uid hw rnd TID mm -> RHEAP (ps_init alloc_ceiling (reservedZ rsegs)) [] mm -> ADP0 mm ->
rw_cells rsegs mm RERRNO [C4 (Z_to_bv 64 0)] -> (exists stg, rw_cells rsegs mm RSTG [CB (Z.to_nat 65536) stg]) ->
evt rsegs Q (MS (mkR (Z_to_bv 64 0x310d0) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
(Z_to_bv 64 2) (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
(Z_to_bv 64 0x1bc88) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1bcb4) (Z_to_bv 32 0) None mm (seg_rom rsegs))) ->
evt rsegs Q ms.
Proof.
intros ms Q AM K.
first [ sf_destruct 64%nat AM as t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 t P0 pg m -> MI ST TD ERR TLS LIBC1 LIBC2 MTLS SYSI PROG HWCAP ENV DSS GUARD GOT0 GOTM GCX G28 G38 G50 GOTG GF IA FA GD0 INI FIN EXL SOU SEU SIN OFL SOF SEF IMG IMGW HP0 NONE HT | sf_fb; destruct AM as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & t & P0 & pg & m & -> & MI & ST & TD & ERR & TLS & LIBC1 & LIBC2 & MTLS & SYSI & PROG & HWCAP & ENV & DSS & GUARD & GOT0 & GOTM & GCX & G28 & G38 & G50 & GOTG & GF & IA & FA & GD0 & INI & FIN & EXL & SOU & SEU & SIN & OFL & SOF & SEF & IMG & IMGW & HP0 & NONE & HT) ].
pose proof (sp_facts sp0 VSP HCEIL) as SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. unfold LO in *.
pose proof (bytes_at_bound _ _ _ _ IMG) as IMGBD.
pose proof (heap_init sp0 argv envp rnd m NONE LIBC1 LIBC2 GOTG GUARD MI HCAN RHI) as [HP0i AUXC].
pose proof (rauxv_ok_init sp0 argv envp uid hw rnd m NONE LIBC1 LIBC2 GOTG GUARD MI IMG HCEIL HSEC HCAN RHI) as AI.
pose proof (initialized_init m NONE) as C1. pose proof (tables_pristine_init m NONE) as C2.
destruct (rexit_init m NONE) as [DSOI AXI].
destruct (stage_init m NONE) as [stg SG].
pose proof (stderr_wfile0_init m NONE) as SE.
change X1nl.rsegs with rsegs in *. change X1gj.rsegs with rsegs in *.
clear TLS MTLS SYSI PROG HWCAP ENV DSS GOT0 GOTM G38 G50 IA INI IMGW HP0 NONE.
replace (usp0 - 8388608) with (usp0 + -8388608) in ST by lia.
eapply (main_prologue sp0 VSP HCEIL); [unfold LO; replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST| exact MI|].
intros m1 pad FR ST1 MU WM MI1. unfold LO in ST1.
pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
assert (OUT : forall a, (a < usp0 - 128 \/ usp0 - 48 <= a) -> (fun a0 : Z => outside [(usp0 - 128, usp0 - 48)] a0) a) by (intros a Ha; cbn; lia).
apply (K t t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1 pad HT).
- exact FR.
- split; [unfold LO; replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST1|]. split; [exact MI1|].
split. { eapply (RSTAT_agree t _ _ _ AG); [intros a Ha; apply OUT; unfold rstat_addr in Ha; lia|].
unfold RSTAT. split; [exact TD|]. split; [exact EXL|]. split; [exact GF|]. split; [exact FA|]. split; [exact FIN|]. split; [exact GCX|].
split; [exact OFL|]. split; [exact SIN|]. split; [exact SOU|]. split; [exact SEU|]. split; [exact G28|]. split; [exact GD0|].
split; [exact DSOI| exact AXI]. }
split. { eapply rauxv_ok_frame; [exact AI| exact MU| exact WM|]. constructor; [| constructor]. unfold RAUXV_CELL, RLIBC. cbn [fst snd]. lia. }
split. { eapply bytes_at_agree; [exact AG| exact IMG| intros a Ha; apply OUT; lia]. }
split. { eapply (stderr_wfile0_agree _ _ _ AG); [intros a Ha; apply OUT; unfold stderr_addr in Ha; lia| exact SE]. }
eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT; unfold stdout_addr in Ha; lia| exact SOF].
- eapply RHF; [exact HP0i| exact MU| exact WM|]. constructor; [| constructor]. left. cbn [fst snd]. unfold alloc_ceiling in *. lia.
- eapply (ADP0_agree _ _ _ AG); [intros a Ha; apply OUT; unfold adp0_addr, RINITIALIZED, RTABLES_LO, RTABLES_HI in Ha; lia|]. split; [exact C1| exact C2].
- eapply rw_cells_agree; [exact AG| unfold RERRNO; exact ERR| intros a Ha; apply OUT; cbn in Ha; unfold RERRNO in Ha; lia].
- exists stg. eapply rw_cells_agree; [exact AG| exact SG| intros a Ha; apply OUT; cbn [cells_size csize Nat.add] in Ha; unfold RSTG in Ha; lia].
Qed.

#[using="VSP HCEIL HSEC HCAN VARGV VENVP RHI RHF"] Lemma main_to_P1 : forall (arg0 arg1 : list byte) (ms : machine_state) (Q : machine_state -> Prop),
argv = [arg0; arg1] -> rat_main sp0 argv envp uid hw rnd F ms ->
(forall TID ms', 0 < TID < 4194304 -> P1 sp0 argv envp uid hw rnd TID F ms' -> evt rsegs Q ms') ->
evt rsegs Q ms.
Proof.
intros arg0 arg1 ms Q EARGV AM K.
eapply main_to_test; [exact AM|]. intros TID t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mm pad HT FR BA HP CJ ERR SG.
unfold argc. rewrite EARGV. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- EARGV.
pose proof BA as (ST & MI & _).
zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
apply (K TID); [exact HT|].
unfold P1. sf_eexists 20%nat. first [ unshelve sf_eexists 3%nat; [ exact ((Z_to_bv 32 0)) | exact (mm) | exact (pad) | ] | sf_fb; exists (Z_to_bv 32 0), mm, pad ]. split; [reflexivity|].
split; [exact FR|]. split; [exact BA|]. split; [exact HP|]. split; [exact CJ|]. split; [exact ERR|]. split; [vm_compute; reflexivity| exact SG].
Qed.

#[using="VSP HCEIL HSEC HCAN VARGV VENVP RHI RHF FPR FWX SWF"] Lemma main_usage_gen : forall {R : Type} (r : R) (Q : R -> PState -> machine_state -> Prop),
(forall s' ms', rat_exit 2 s' ms' -> Q r s' ms') ->
forall ms, rat_main sp0 argv envp uid hw rnd F ms -> Z.of_nat (length argv) <> 2 ->
implM rsegs (io_diag (DUsage (nth 0 (argv_Z argv) [])) ;;; mret r) (ps_init alloc_ceiling (reservedZ rsegs)) Q ms.
Proof.
intros R r Q HQ ms AM HARGC.
apply (implM_evt rsegs _ _ _ (fun ms' => implM rsegs (io_diag (DUsage (nth 0 (argv_Z argv) [])) ;;; mret r) (ps_init alloc_ceiling (reservedZ rsegs)) Q ms'));
[| intros ms' H; exact H].
eapply main_to_test; [exact AM|]. intros TID t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mm pad HT FR BA HP CJ ERR _.
pose proof (sp_facts sp0 VSP HCEIL) as SF. pose proof (IMGB_len sp0 argv envp uid hw rnd VSP VARGV VENVP) as IL. unfold LO in *.
pose proof BA as sfP_; first [ sf_destruct 7%nat sfP_ as ST MI RS AUX IMG SE SO | sf_fb; destruct sfP_ as (ST & MI & RS & AUX & IMG & SE & SO) ]. unfold LO in ST.
pose proof RS as sfP_; first [ sf_destruct 14%nat sfP_ as _ _ _ _ _ _ _ _ _ _ G28 GD0 _ _ | sf_fb; destruct sfP_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _ & _) ].
first [ sf_destruct 5%nat VARGV as ARGC _ ARGLEN NONUL _ | sf_fb; destruct VARGV as (ARGC & _ & ARGLEN & NONUL & _) ].
destruct argv as [|arg0 argv'] eqn:EARGV; [cbn in ARGC; lia|]. rewrite <- EARGV in *.

first [ pose proof (argv_cstring sp0 argv envp uid hw rnd mm IMG 0 arg0 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia)) as sfP_; sf_destruct 7%nat sfP_ as p0 slack0 HP0 P0LO P0HI STR0 SLK0 | sf_fb; destruct (argv_cstring sp0 argv envp uid hw rnd mm IMG 0 arg0 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia)) as (p0 & slack0 & HP0 & P0LO & P0HI & STR0 & SLK0) ]. unfold str_base, struct_size, argc, envc in P0LO.
destruct (stack_pieces sp0 argv envp uid hw rnd mm IMG) as (_ & ARGVP & _).
assert (A0NN : ~ In (Z_to_bv 8 0) arg0) by (rewrite EARGV in NONUL; inversion NONUL; assumption).
assert (A0LEN : Z.of_nat (length arg0) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN; assumption).
unfold argc. zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.

zstep. zstep. zstep.
pose proof (u64ro_read mm (usp0 + 8) (argv_ptrs sp0 argv envp ++ [Z_to_bv 64 0]) 0 (Z_to_bv 64 p0) (Z_to_bv 64 (usp0 + 8))
ARGVP ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length, EARGV; cbn; lia); exact HP0) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
zstep. clear RD. zstep. zstep. zstep.

apply evt_done.
eapply implM_bind.
{ eapply (FPR (DUsage (nth 0 (argv_Z argv) []))) with (lo := usp0 - 8388608) (canary := run_canary);
[exact FWX| exact SWF| apply stderr_wfile0_wfile; exact SE| reflexivity| | rewrite unsigned_lit by lia; exact ST
| rewrite unsigned_lit by lia; unfold FPRINTF_DEPTH; lia| unfold GLOBALS_TOP; lia| rewrite unsigned_lit by lia; lia
| apply (RHEAP_ssp _ _ _ HP)| exact MI| vm_compute; reflexivity].
cbn [diag_args]. split; [reflexivity|]. exists slack0.
rewrite EARGV. cbn [argv_Z map nth]. rewrite unsigned_lit by lia.
unfold X1ei.zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
split; [exact STR0|]. split; [apply map_unsigned_pos; exact A0NN|]. split; [lia|].
split; [unfold X1oc.INT_MAX; lia|]. split; [right; rewrite unsigned_lit by lia; lia| unfold GLOBALS_TOP; lia]. }
cbv beta. intros [] st' ms' PO.
first [ sf_destruct 28%nat PO as u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 Ft fc' m2 -> MUc WMc MI2 FRM2 FEQ ST2 SEW SSP2 -> | sf_fb; destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ->) ].
rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
replace (ret_pc (Z_to_bv 64 0x1be3c)) with (Z_to_bv 64 0x1be3c) by (symmetry; rpc).
pose proof (agree_on_of_munch _ _ _ MUc WMc) as AG.
assert (OUT : forall a, (usp0 - 128 <= a /\ ~ (0x3d110 <= a < 0x3d110 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x3d110, 0x3d110 + 232)] a0) a).
{ intros a Ha. cbn. lia. }
assert (OUT2 : forall a, (0x10000 <= a < 0x6e000 /\ ~ (0x3d110 <= a < 0x3d110 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x3d110, 0x3d110 + 232)] a0) a).
{ intros a Ha. cbn. lia. }
apply implM_ret. unfold MFRAME in FR.
apply (rw_cells_agree rsegs _ _ _ _ _ AG) in FR; [| intros a Ha; apply OUT; cbn in Ha; lia].
apply (evt_mono rsegs (rat_exit 2 (ps_init alloc_ceiling (reservedZ rsegs)))); [| intros msq Hq; exact (HQ _ _ Hq)].
zstep.
eapply (main_return sp0 argv TID VSP HCEIL HT 2 (ps_init alloc_ceiling (reservedZ rsegs)) []).
- exact FR.
- unfold LO. replace (usp0 - 8388608) with (usp0 + -8388608) in ST2 by lia. exact ST2 || exact ST2.
- eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS].
- eapply RHF; [exact HP| exact MUc| exact WMc|].
constructor; [left; cbn [fst snd]; unfold alloc_ceiling in *; lia|]. constructor; [| constructor].
right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RREPLACED. lia.
- cbn [ps_so ps_init]. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SO].
- apply stderr_wfile_file. exact SEW.
- exact MI2.
Qed.

#[using="VSP HCEIL HSEC HCAN VARGV VENVP RHI RHF FPR FWX SWF"] Lemma main_usage : forall ms, rat_main sp0 argv envp uid hw rnd F ms -> Z.of_nat (length argv) <> 2 ->
implM rsegs (rmain_model argv) (ps_init alloc_ceiling (reservedZ rsegs)) (fun code s' ms' => rat_exit code s' ms') ms.
Proof.
intros ms AM HARGC.
unfold rmain_model, main_model. unfold argv_Z at 1. rewrite length_map.
replace (Z.of_nat (length argv) =? 2) with false by (symmetry; apply Z.eqb_neq; exact HARGC). cbn [negb].
exact (main_usage_gen 2 (fun code s' ms' => rat_exit code s' ms') (fun _ _ H => H) ms AM HARGC).
Qed.
End A2.
