(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bm X1bo X1c9 X1br X1cd X1bs X1c2 X1c6.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pv X0pw X0qx.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1nm X1nl X1ea.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1qx X1ri X1o8 X1rm X1r3 X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopLevel.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Local Notation rsegs := Ubsan.M.loaded_segments.
Local Notation z64 := (Z_to_bv 64 0).

Definition rat_exit (code : Z) (s : PState) (ms : machine_state) : Prop :=
exists (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo t : Z) (td0 td1 td2 td3 guard : word)
(cdt thr sec : byte) (tm1 : word) (k : bool),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x31568) fc None m (seg_rom rsegs)
/\ stk rsegs m lo (bv_unsigned sp)
/\ rw_cells rsegs m 0x4d388 [C8 td0; C8 td1; C8 td2; C8 td3; C4 (Z_to_bv 64 t)]
/\ rw_cells rsegs m 0x6d6b0 [C4 z64]
/\ rw_cells rsegs m 0x3c0d8 [C8 (Z_to_bv 64 0x3b6f8); C8 (Z_to_bv 64 0x3b6f0)]
/\ rw_cells rsegs m 0x3b6f0 [C8 (Z_to_bv 64 0x1bbf8)]
/\ rw_cells rsegs m 0x3d348 [C1 (Z_to_bv 8 0)]
/\ rw_cells rsegs m 0x3c010 [C8 (Z_to_bv 64 RCXA_FINALIZE); C8 z64]
/\ rw_cells rsegs m 0x6d6d8 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1]
/\ rw_cells rsegs m 0x6db08 [C8 z64] /\ rw_cells rsegs m 0x6daf8 [C8 z64]
/\ rw_cells rsegs m 0x3d2e8 [C8 (Z_to_bv 64 RSTDOUT)] /\ rw_cells rsegs m 0x3d1f8 [C8 (Z_to_bv 64 RSTDERR)]
/\ stdout_file m (ps_so s) /\ stderr_file m
/\ rw_cells rsegs m 0x3c0d0 [C8 (Z_to_bv 64 0x6d6b8)] /\ rw_cells rsegs m 0x6d6b8 [C8 guard]
/\ mem_inv rsegs m
/\ tp = Z_to_bv 64 0x4d450 /\ a0 = Z_to_bv 64 code
/\ 0 < t < 4194304 /\ lo <= bv_unsigned sp - 176 /\ 0x6e000 <= lo
/\ AXSTAT k m /\ rw_cells rsegs m RDSO [C8 (Z_to_bv 64 RDSO)].

Definition rmain_model (argv : list (list byte)) : M PState Z :=
main_model io_diag raw_malloc raw_free RSTAGE_ubsan
(target_alloc_init (St:=PState)) run (target_alloc_count (St:=PState)) (argv_Z argv).

Definition rmain_stmt {RCEIL : RunCeiling} : Prop :=
forall (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (F : bvmap 5 word) (ms : machine_state),
valid_sp sp0 -> valid_argv argv -> valid_envp envp -> is_mkF F ->
alloc_ceiling = bv_unsigned sp0 - 8388608 ->
run_secret = rnd_w1 rnd ->
run_canary = canary_of (rnd_w0 rnd) ->
rat_main sp0 argv envp uid hw rnd F ms ->
implM rsegs (rmain_model argv) (ps_init alloc_ceiling (reservedZ rsegs)) (fun code s' ms' => rat_exit code s' ms') ms.

Lemma rimpl_msys_of_enode : forall {St A} (n : node) (pl : resp -> option A) (Q : A -> machine_state -> Prop) (s : St) ms,
impl rsegs (at_node rsegs) (enode n pl) (epost Q) ms ->
impl rsegs (at_node rsegs) (X1qx.msys n pl s) (epost (fun p ms' => Q (fst p) ms' /\ snd p = s)) ms.
Proof.
intros St A n pl Q s ms H. unfold X1qx.msys, enode in *. cbn in *.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp. specialize (Hk rsp). destruct (pl rsp) as [a|]; cbn in *; [|exact Hk].
eapply evt_mono; [exact Hk|]. intros ms2 HQ. cbn. auto.
Qed.

Section Compose.
Context {RCEIL : RunCeiling}.
Hypothesis STDIO_EXIT : stdio_exit_spec_stmt ps_so set_so_ps.
Hypothesis MAIN : rmain_stmt.

#[using="STDIO_EXIT"] Lemma rexit_from_rat_exit : forall (s : PState) (Q : Empty_set -> PState -> machine_state -> Prop) code ms,
rat_exit code s ms -> implM rsegs (io_exit code) s Q ms.
Proof.
intros s Q code ms H.
first [ rename H into sfR_; sf_destruct 48%nat sfR_ as ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo t td0 td1 td2 td3 guard cdt thr sec tm1 k -> H | sf_fb; destruct H as (ra & sp & gp & tp & t0 & t1 & t2 & s0 & s1 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s2 & s3 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & F & fc & m & lo & t & td0 & td1 & td2 & td3 & guard & cdt & thr & sec & tm1 & k & -> & H) ].
first [ sf_destruct 24%nat H as ST TD EXL GF FA FIN GCX LCH OFL SIN SOU SEU SOF SEF GG GU MI Htp Ha0 Ht LO LOLO AX DSO | sf_fb; destruct H as (ST & TD & EXL & GF & FA & FIN & GCX & LCH & OFL & SIN & SOU & SEU & SOF & SEF & GG & GU & MI & Htp & Ha0 & Ht & LO & LOLO & AX & DSO) ].
unfold io_exit.
eapply (X1ea.exit_spec ps_so set_so_ps STDIO_EXIT s Q);
[exact ST | exact TD | exact EXL | exact GF | exact FA | exact FIN | exact GCX | exact LCH | exact OFL | exact SIN | exact SOU | exact SEU | exact SOF | exact SEF | exact GG | exact GU | exact MI | exact Htp | exact Ha0 | exact Ht | exact LO | exact LOLO | exact AX | exact DSO].
Qed.

#[using="STDIO_EXIT MAIN"] Theorem ref_impl_from_main : forall (en : ExecEntry) (inp : ProcInput),
valid_entry (mkImage rsegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp ->
valid_input_core inp ->
alloc_ceiling = bv_unsigned (en_sp en) - 0x800000 ->
run_secret = rnd_w1 (en_draw en) ->
run_canary = canary_of (rnd_w0 (en_draw en)) ->
impl rsegs (at_node rsegs) (prog_ubsan rsegs RSTAGE_ubsan alloc_ceiling (in_argv inp)) (epost (fun (_ : unit) (_ : machine_state) => True))
(ms0F rsegs Ubsan.M.init_pc Ubsan.M.phdrs en inp).
Proof.
intros [sp0 brk mb rnd] inp VE VI HCEIL HSEC HCAN.
pose proof (valid_entry_parts _ _ _ _ _ _ _ _ VI VE) as sfP_; first [ sf_destruct 4%nat sfP_ as VSP _ _ FIT | sf_fb; destruct sfP_ as (VSP & _ & _ & FIT) ]. clear VE.
pose proof VI as (VARGV & VENVP & _).
destruct inp as [argv envp fs sin uid gid grps net nof sigm hw abt va].
cbn [en_sp en_draw in_argv in_envp in_fs en_brk in_uid in_hwcap] in *.
unfold ms0F. cbn [en_sp en_draw in_argv in_envp in_uid in_hwcap].
unfold prog_ubsan, prog.
set (s0 := ps_init alloc_ceiling (reservedZ rsegs)).
eapply (impl_ebind _ _ _ _ _ (fun (_ : Empty_set * PState) (_ : machine_state) => True)).
2:{ intros [v ?] ms' _. destruct v. }
unfold prog_with. unfold X1qx.mbind at 1.
eapply (impl_ebind _ _ _ _ _ (fun (p : unit * PState) ms' => rat_main sp0 argv envp uid hw rnd mkF0 ms' /\ snd p = s0)).
- unfold X1r6.startup, X1qx.mbind.
eapply (impl_ebind _ _ _ _ _ (fun (p : Z * PState) ms' => rat_main sp0 argv envp uid hw rnd mkF0 ms' /\ snd p = s0)).
+ exact (rimpl_msys_of_enode _ _ _ _ _ (rstartup_specF sp0 argv envp uid hw rnd VSP VARGV VENVP FIT)).
+ intros [a s] ms' [H Hs]. cbn in H, Hs. cbn [fst snd]. apply impl_ret_ok. apply evt_done. cbn. auto.
- intros [u s] ms' [AM Hs]. cbn in Hs. subst s. cbn [fst snd].
change (X1qx.implM rsegs (X1qx.mbind (rmain_model argv) (fun code => io_exit code)) s0 (fun _ _ _ => True) ms').
eapply (X1qx.implM_bind rsegs).
+ exact (MAIN sp0 argv envp uid hw rnd mkF0 ms' VSP VARGV VENVP is_mkF_mkF0 HCEIL HSEC HCAN AM).
+ intros code s' ms'' AE. cbn in AE. apply rexit_from_rat_exit. exact AE.
Qed.
End Compose.
