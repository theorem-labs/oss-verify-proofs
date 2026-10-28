(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bq.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0pw X0qw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1nl X1m8 X1fr X1no X1h7 X1kd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require X1ff X1fd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1o8 X1r3 X1r6.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation rsegs := X1gj.rsegs.

Ltac ua := change X1ff.rsegs with X1gj.rsegs in *; change U.X1fd.rsegs with X1gj.rsegs in *.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section CTX.
Context {RCEIL : RunCeiling}.
Variables (sp0 : word) (argv envp : list (list byte)) (TID : Z).
Notation usp0 := (bv_unsigned sp0).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 RATP).

Definition LO : Z := usp0 - 8388608.

Definition MFRAME (mm : mem) (pad : list byte) (s7v s6v s5v s4v : word) : Prop :=
rw_cells rsegs mm (usp0 + -128)
[CB 8 pad; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 (Z_to_bv 64 (envp_addr sp0 argv)); C8 (Z_to_bv 64 0x1bc88);
C8 (Z_to_bv 64 (argc argv)); C8 (Z_to_bv 64 (usp0 + 8)); C8 (Z_to_bv 64 0x310d0)].

Definition RSTAT (k : bool) (mm : mem) : Prop :=
rw_cells rsegs mm 0x4d388 [C8 (Z_to_bv 64 0x4d388); C8 (Z_to_bv 64 0x4d388); C8 (Z_to_bv 64 0x4d388); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 TID)]
/\ rw_cells rsegs mm 0x6d6b0 [C4 (Z_to_bv 64 0)]
/\ rw_cells rsegs mm 0x3c0d8 [C8 (Z_to_bv 64 0x3b6f8); C8 (Z_to_bv 64 0x3b6f0)]
/\ rw_cells rsegs mm 0x3b6f0 [C8 (Z_to_bv 64 0x1bbf8)]
/\ rw_cells rsegs mm 0x3d348 [C1 (Z_to_bv 8 0)]
/\ rw_cells rsegs mm 0x3c010 [C8 (Z_to_bv 64 RCXA_FINALIZE); C8 (Z_to_bv 64 0)]
/\ rw_cells rsegs mm 0x6db08 [C8 (Z_to_bv 64 0)]
/\ rw_cells rsegs mm 0x6daf8 [C8 (Z_to_bv 64 0)]
/\ rw_cells rsegs mm 0x3d2e8 [C8 (Z_to_bv 64 0x3d200)]
/\ rw_cells rsegs mm 0x3d1f8 [C8 (Z_to_bv 64 0x3d110)]
/\ rw_cells rsegs mm 0x3c020 [C8 (Z_to_bv 64 0x3bfd0)]
/\ rw_cells rsegs mm 0x3bfd0 [C8 (Z_to_bv 64 0x3d110)]
/\ rw_cells rsegs mm RDSO [C8 (Z_to_bv 64 RDSO)]
/\ AXSTAT k mm.

Definition rstat0_addr (a : Z) : Prop :=
(0x4d388 <= a < 0x4d3ac) \/ (0x6d6b0 <= a < 0x6d6b4) \/ (0x3c0d8 <= a < 0x3c0e8) \/ (0x3b6f0 <= a < 0x3b6f8)
\/ (0x3d348 <= a < 0x3d349) \/ (0x3c010 <= a < 0x3c020) \/ (0x6daf8 <= a < 0x6db00) \/ (0x6db08 <= a < 0x6db10)
\/ (0x3d2e8 <= a < 0x3d2f0) \/ (0x3d1f8 <= a < 0x3d200) \/ (0x3c020 <= a < 0x3c028) \/ (0x3bfd0 <= a < 0x3bfd8)
\/ (0x3d0e8 <= a < 0x3d0f0).

Definition rstat_addr (a : Z) : Prop :=
(0x4d388 <= a < 0x4d3ac) \/ (0x6d6b0 <= a < 0x6d6b4) \/ (0x3c0d8 <= a < 0x3c0e8) \/ (0x3b6f0 <= a < 0x3b6f8)
\/ (0x3d348 <= a < 0x3d349) \/ (0x3c010 <= a < 0x3c020) \/ (0x6daf8 <= a < 0x6db00) \/ (0x6db08 <= a < 0x6db10)
\/ (0x3d2e8 <= a < 0x3d2f0) \/ (0x3d1f8 <= a < 0x3d200) \/ (0x3c020 <= a < 0x3c028) \/ (0x3bfd0 <= a < 0x3bfd8)
\/ (0x3d0e8 <= a < 0x3d0f0) \/ (0x4d354 <= a < 0x4d355) \/ (0x6d490 <= a < 0x6d4b8) \/ (0x6d5b0 <= a < 0x6d5b8).

Ltac tr AG HP A := eapply rw_cells_agree; [exact AG| exact A| intros a Ha; apply HP; unfold rstat_addr; cbn in Ha; lia].

#[using="Type"] Lemma RSTAT_agree : forall {k : bool} (P : Z -> Prop) m m', agree_on rsegs P m m' -> (forall a, rstat_addr a -> P a) -> RSTAT k m -> RSTAT k m'.
Proof.
intros k P m m' AG HP sfH_; first [ sf_destruct 14%nat sfH_ as A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 | sf_fb; destruct sfH_ as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14) ]. unfold RSTAT.
split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [tr AG HP A3|]. split; [tr AG HP A4|].
split; [tr AG HP A5|]. split; [tr AG HP A6|]. split; [tr AG HP A7|]. split; [tr AG HP A8|].
split; [tr AG HP A9|]. split; [tr AG HP A10|]. split; [tr AG HP A11|]. split; [tr AG HP A12|].
split; [unfold RDSO in *; tr AG HP A13|].
destruct A14 as [X1 X2]. unfold AXSTAT, RAEF_INCB, RATEXIT, RATEXIT_A0, RAEF_GUARD, RATEXIT_CALL, ax_cells in *. cbn [Z.add] in *.
split; [tr AG HP X1|]. destruct k; destruct X2 as [X2 X3]; (split; [tr AG HP X2| tr AG HP X3]).
Qed.

Ltac tr0 AG HP A := eapply rw_cells_agree; [exact AG| exact A| intros a Ha; apply HP; unfold rstat0_addr; cbn in Ha; lia].

#[using="Type"] Lemma RSTAT_reax : forall {k k' : bool} (P : Z -> Prop) m m', agree_on rsegs P m m' -> (forall a, rstat0_addr a -> P a) ->
RSTAT k m -> AXSTAT k' m' -> RSTAT k' m'.
Proof.
intros k k' P m m' AG HP sfH_ AX'; first [ sf_destruct 14%nat sfH_ as A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 _ | sf_fb; destruct sfH_ as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & _) ]. unfold RSTAT.
split; [tr0 AG HP A1|]. split; [tr0 AG HP A2|]. split; [tr0 AG HP A3|]. split; [tr0 AG HP A4|].
split; [tr0 AG HP A5|]. split; [tr0 AG HP A6|]. split; [tr0 AG HP A7|]. split; [tr0 AG HP A8|].
split; [tr0 AG HP A9|]. split; [tr0 AG HP A10|]. split; [tr0 AG HP A11|]. split; [tr0 AG HP A12|].
split; [unfold RDSO in *; tr0 AG HP A13| exact AX'].
Qed.

#[using="Type"] Lemma RSTAT_ax : forall {k : bool} m, RSTAT k m -> AXSTAT k m.
Proof.
intros k m sfH_; first [ sf_destruct 14%nat sfH_ as _ _ _ _ _ _ _ _ _ _ _ _ _ A14 | sf_fb; destruct sfH_ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & A14) ]. exact A14.
Qed.

#[using="Type"] Lemma RSTAT_heap_pres : forall {k : bool} LB SP m m', rheap_pres LB SP m m' -> RSTAT k m -> RSTAT k m'.
Proof.
intros k LB SP m m' HP. apply (RSTAT_agree _ _ _ HP). intros a Ha. right; left.
unfold rstat_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.

#[using="Type"] Lemma pres_except_agree : forall LB SP X m m', pres_except rsegs (rclient_addr LB SP) X m m' ->
agree_on rsegs (fun a => 0 <= a < 2^64 /\ rclient_addr LB SP a /\ ~ in_ivs X a) m m'.
Proof. intros LB SP X m m' H a Ha (R & C & NX). apply H; assumption. Qed.

#[using="Type"] Lemma RSTAT_pres_except : forall {k : bool} LB SP X m m', pres_except rsegs (rclient_addr LB SP) X m m' ->
(forall a, in_ivs X a -> ~ rstat_addr a) -> RSTAT k m -> RSTAT k m'.
Proof.
intros k LB SP X m m' PE HX. apply (RSTAT_agree _ _ _ (pres_except_agree _ _ _ _ _ PE)). intros a Ha.
split; [unfold rstat_addr in Ha; lia|]. split.
- right; left. unfold rstat_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
- intros Hx. exact (HX a Hx Ha).
Qed.

#[using="Type"] Lemma RSTAT_munch : forall {k : bool} W m m', munch W m m' -> wmono rsegs m m' -> (forall a, rstat_addr a -> outside W a) -> RSTAT k m -> RSTAT k m'.
Proof.
intros k W m m' MU WM HW. apply (RSTAT_agree _ _ _ (agree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha.
Qed.
End CTX.

Definition stdout_addr (a : Z) : Prop := (0x3d200 <= a < 0x3d2e8) \/ (0x6db20 <= a < 0x6df20).
Definition stderr_addr (a : Z) : Prop := 0x3d110 <= a < 0x3d1f8.

Lemma stdout_file_agree : forall (P : Z -> Prop) m m' so,
agree_on rsegs P m m' -> (forall a, stdout_addr a -> P a) -> stdout_file m so -> stdout_file m' so.
Proof.
intros P m m' so AG HP sfH_; first [ sf_destruct 10%nat sfH_ as flags mode tail bufbytes F1 F2 F3 F4 F5 F6 | sf_fb; destruct sfH_ as (flags & mode & tail & bufbytes & F1 & F2 & F3 & F4 & F5 & F6) ].
first [ unshelve sf_eexists 4%nat; [ exact (flags) | exact (mode) | exact (tail) | exact (bufbytes) | ] | sf_fb; exists flags, mode, tail, bufbytes ]. split; [| split; [exact F2| split; [| split; [exact F4| split; [exact F5| exact F6]]]]].
- eapply rw_cells_agree; [exact AG| exact F1|]. intros a Ha. apply HP. left. cbn in Ha. lia.
- eapply rw_cells_agree; [exact AG| exact F3|]. intros a Ha. apply HP. right. cbn in Ha. lia.
Qed.

Lemma stderr_wfile0_agree : forall (P : Z -> Prop) m m',
agree_on rsegs P m m' -> (forall a, stderr_addr a -> P a) -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof.
intros P m m' AG HP sfH_; first [ sf_destruct 9%nat sfH_ as flags mode e wend tail F1 F2 F3 F4 | sf_fb; destruct sfH_ as (flags & mode & e & wend & tail & F1 & F2 & F3 & F4) ].
first [ unshelve sf_eexists 5%nat; [ exact (flags) | exact (mode) | exact (e) | exact (wend) | exact (tail) | ] | sf_fb; exists flags, mode, e, wend, tail ]. split; [| split; [exact F2| split; [exact F3| exact F4]]].
eapply rw_cells_agree; [exact AG| exact F1|]. intros a Ha. apply HP. unfold stderr_addr. cbn in Ha. lia.
Qed.

Lemma stdout_file_heap_pres : forall LB SP m m' so, rheap_pres LB SP m m' -> stdout_file m so -> stdout_file m' so.
Proof.
intros LB SP m m' so HP. apply (stdout_file_agree _ _ _ _ HP). intros a Ha. right; left.
unfold stdout_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stderr_wfile0_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof.
intros LB SP m m' HP. apply (stderr_wfile0_agree _ _ _ HP). intros a Ha. right; left.
unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stdout_file_munch : forall W m m' so, munch W m m' -> wmono rsegs m m' -> (forall a, stdout_addr a -> outside W a) -> stdout_file m so -> stdout_file m' so.
Proof. intros W m m' so MU WM HW. apply (stdout_file_agree _ _ _ _ (agree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma stderr_wfile0_munch : forall W m m', munch W m m' -> wmono rsegs m m' -> (forall a, stderr_addr a -> outside W a) -> stderr_wfile0 m -> stderr_wfile0 m'.
Proof. intros W m m' MU WM HW. apply (stderr_wfile0_agree _ _ _ (agree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma stdout_file_pres_except : forall LB SP X m m' so, pres_except rsegs (rclient_addr LB SP) X m m' ->
(forall a, in_ivs X a -> ~ stdout_addr a) -> stdout_file m so -> stdout_file m' so.
Proof.
intros LB SP X m m' so PE HX. apply (stdout_file_agree _ _ _ _ (pres_except_agree _ _ _ _ _ PE)). intros a Ha.
split; [unfold stdout_addr in Ha; lia|]. split.
- right; left. unfold stdout_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
- intros Hx. exact (HX a Hx Ha).
Qed.

Lemma stderr_wfile_agree : forall (P : Z -> Prop) m m',
agree_on rsegs P m m' -> (forall a, stderr_addr a -> P a) -> stderr_wfile m -> stderr_wfile m'.
Proof.
intros P m m' AG HP sfH_; first [ sf_destruct 7%nat sfH_ as flags mode e wend tail F1 F2 | sf_fb; destruct sfH_ as (flags & mode & e & wend & tail & F1 & F2) ].
first [ unshelve sf_eexists 5%nat; [ exact (flags) | exact (mode) | exact (e) | exact (wend) | exact (tail) | ] | sf_fb; exists flags, mode, e, wend, tail ]. split; [| exact F2].
eapply rw_cells_agree; [exact AG| exact F1|]. intros a Ha. apply HP. unfold stderr_addr. cbn in Ha. lia.
Qed.
Lemma stderr_wfile_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> stderr_wfile m -> stderr_wfile m'.
Proof.
intros LB SP m m' HP. apply (stderr_wfile_agree _ _ _ HP). intros a Ha. right; left.
unfold stderr_addr, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma stderr_wfile_munch : forall W m m', munch W m m' -> wmono rsegs m m' -> (forall a, stderr_addr a -> outside W a) -> stderr_wfile m -> stderr_wfile m'.
Proof. intros W m m' MU WM HW. apply (stderr_wfile_agree _ _ _ (agree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.

Lemma rtables_pristine_agree : forall (P : Z -> Prop) m m',
agree_on rsegs P m m' -> (forall a, RTABLES_LO <= a < RTABLES_HI -> P a) -> rtables_pristine m -> rtables_pristine m'.
Proof.
intros P m m' AG HP H a Ha. pose proof (H a Ha) as E.
destruct (AG (bv_unsigned a) ltac:(pose proof (bv_unsigned_in_range 64 a) as R; unfold bv_modulus in R; cbn in R; lia) (HP _ Ha)) as [E' _].
unfold wa in E'. rewrite Z_to_bv_bv_unsigned in E'. rewrite E'. exact E.
Qed.
Lemma rtables_pristine_heap_pres : forall LB SP m m', rheap_pres LB SP m m' -> rtables_pristine m -> rtables_pristine m'.
Proof.
intros LB SP m m' HP. apply (rtables_pristine_agree _ _ _ HP). intros a Ha. right; left.
unfold RTABLES_LO, RTABLES_HI, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
Qed.
Lemma rtables_pristine_munch : forall W m m', munch W m m' -> wmono rsegs m m' -> (forall a, RTABLES_LO <= a < RTABLES_HI -> outside W a) ->
rtables_pristine m -> rtables_pristine m'.
Proof. intros W m m' MU WM HW. apply (rtables_pristine_agree _ _ _ (agree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha. Qed.
Lemma rtables_pristine_pres_except : forall LB SP X m m', pres_except rsegs (rclient_addr LB SP) X m m' ->
(forall a, in_ivs X a -> ~ (RTABLES_LO <= a < RTABLES_HI)) -> rtables_pristine m -> rtables_pristine m'.
Proof.
intros LB SP X m m' PE HX. apply (rtables_pristine_agree _ _ _ (pres_except_agree _ _ _ _ _ PE)). intros a Ha.
split; [unfold RTABLES_LO, RTABLES_HI in Ha; lia|]. split.
- right; left. unfold RTABLES_LO, RTABLES_HI, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia.
- intros Hx. exact (HX a Hx Ha).
Qed.

Lemma RHEAP_ssp {RCEIL : RunCeiling} : forall s LB m, RHEAP s LB m -> ssp_cells m run_canary.
Proof.
intros s LB m sfH_; first [ sf_destruct 6%nat sfH_ as st LB0 _ _ MREP _ | sf_fb; destruct sfH_ as (st & LB0 & _ & _ & MREP & _) ]. first [ sf_destruct 4%nat MREP as _ _ (_ & _ & _ & G1 & G2) _ | sf_fb; destruct MREP as (_ & _ & (_ & _ & _ & G1 & G2) & _) ].
unfold ssp_cells, got_ssp, ssp_guard. unfold RGOT_SSP, RSSP_GUARD in G1, G2. split; [exact G1| exact G2].
Qed.

Section EXITS.
Context {RCEIL : RunCeiling}.
Variables (sp0 : word) (argv envp : list (list byte)) (TID : Z).
Notation usp0 := (bv_unsigned sp0).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 RATP).
Hypothesis VSP : valid_sp sp0.
Hypothesis HCEIL : alloc_ceiling = LO sp0.
Hypothesis HT : 0 < TID < 4194304.

#[using="VSP HCEIL"] Lemma sp_facts : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0 /\ alloc_ceiling <= LO sp0 /\ LO sp0 + 8388608 = usp0 /\ 0x6e000 <= LO sp0.
Proof. destruct VSP as (A & B & C). rewrite HCEIL. unfold LO, sp_window_lo, sp_window_hi, stack_max_size in *. repeat split; lia. Qed.

#[using="HT"] Lemma rat_exit_intro : forall (code : Z) (s : PState) (LB : list block) (SP : Z) (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (k : bool),
stk rsegs m lo SP -> lo <= SP - 176 -> 0x6e000 <= lo -> 0 <= SP < 2^64 ->
RSTAT TID k m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv rsegs m ->
rat_exit code s (MS (mkR ra (Z_to_bv 64 SP) gpv tpv t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x31568) fc None m (seg_rom rsegs)).
Proof.
intros until k. intros ST LOS LOLO SPR sfH_; first [ sf_destruct 14%nat sfH_ as TD EXL GF FA FIN GCX OFL SIN SOU SEU _ _ DSO AX | sf_fb; destruct sfH_ as (TD & EXL & GF & FA & FIN & GCX & OFL & SIN & SOU & SEU & _ & _ & DSO & AX) ]; intros HP SOF SEF MI.
first [ pose proof (RHEAP_libc_head _ _ _ HP) as sfP_; sf_destruct 5%nat sfP_ as cdt thr sec tm1 LC | sf_fb; destruct (RHEAP_libc_head _ _ _ HP) as (cdt & thr & sec & tm1 & LC) ].
pose proof (RHEAP_ssp _ _ _ HP) as [G1 G2]. unfold got_ssp, ssp_guard in G1, G2.
unfold rat_exit. sf_eexists 33%nat. first [ unshelve sf_eexists 8%nat; [ exact (m) | exact (lo) | exact (TID) | exact ((Z_to_bv 64 0x4d388)) | exact ((Z_to_bv 64 0x4d388)) | exact ((Z_to_bv 64 0x4d388)) | exact ((Z_to_bv 64 0)) | exact (run_canary) | ] | sf_fb; exists m, lo, TID, (Z_to_bv 64 0x4d388), (Z_to_bv 64 0x4d388), (Z_to_bv 64 0x4d388), (Z_to_bv 64 0), run_canary ].
first [ unshelve sf_eexists 5%nat; [ exact (cdt) | exact (thr) | exact (sec) | exact (tm1) | exact (k) | ] | sf_fb; exists cdt, thr, sec, tm1, k ].
split; [reflexivity|]. rewrite !unsigned_lit by lia. split; [exact ST|]. split; [exact TD|]. split; [exact EXL|]. split; [exact GF|]. split; [exact FA|].
split; [exact FIN|]. split; [exact GCX|]. split; [exact LC|]. split; [exact OFL|]. split; [exact SIN|]. split; [exact SOU|]. split; [exact SEU|].
split; [exact SOF|]. split; [exact SEF|]. split; [exact G1|]. split; [exact G2|]. split; [exact MI|].
split; [reflexivity|]. split; [reflexivity|]. split; [exact HT|]. split; [lia|]. split; [lia|]. split; [exact AX| exact DSO].
Qed.

#[using="VSP HCEIL HT"] Lemma main_return : forall (code : Z) (s : PState) (LB : list block) (x1 t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(pad : list byte) (s7v s6v s5v s4v : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (k : bool),
MFRAME sp0 argv m pad s7v s6v s5v s4v ->
stk rsegs m (LO sp0) (usp0 + -128) ->
RSTAT TID k m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv rsegs m ->
evt rsegs (rat_exit code s)
(MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 code) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1be84) fc None m (seg_rom rsegs)).
Proof.
intros until k. intros FR ST RS HP SOF SEF MI. pose proof sp_facts as SF. unfold LO in *. unfold MFRAME in FR.
do 11 zstep. release_frame FR ST (usp0 + -48). zstep.
replace (ret_pc (Z_to_bv 64 0x310d0)) with (Z_to_bv 64 0x310d0) by (symmetry; rpc).
zstep.
apply evt_done. eapply rat_exit_intro; [exact ST| lia| lia| lia| exact RS| exact HP| exact SOF| exact SEF| exact MI].
Qed.

#[using="VSP HCEIL HT"] Lemma exit2_tail : forall (s : PState) (LB : list block) (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (k : bool),
stk rsegs m (LO sp0) (usp0 + -128) ->
RSTAT TID k m -> RHEAP s LB m -> stdout_file m (ps_so s) -> stderr_file m -> mem_inv rsegs m ->
evt rsegs (rat_exit 2 s)
(MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x1bf10) fc None m (seg_rom rsegs)).
Proof.
intros until k. intros ST RS HP SOF SEF MI. pose proof sp_facts as SF. unfold LO in *.
zstep. zstep.
apply evt_done. eapply rat_exit_intro; [exact ST| lia| lia| lia| exact RS| exact HP| exact SOF| exact SEF| exact MI].
Qed.
End EXITS.
