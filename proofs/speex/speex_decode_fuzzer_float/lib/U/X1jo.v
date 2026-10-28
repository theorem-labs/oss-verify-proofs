(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0pa X0p9 X0qn X0py X0qc X0qd X0qg X0qe X0qf X0qh X0qj.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0ql X0q1 X0o1 X0o2 X0oj X0o4 X0ns X0nt X0nw.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1ky X1lz X1m0 X1m1 X1lw X1lx X1m4 X1k8 X1jk X1k4 X1k6 X1jv X1jl X1jn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0qa.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LEVEL.
Context {RCEIL : RunCeiling}.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> X1qu.M R) (bail : X1qu.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : RAREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RAS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms'.
Let F0 : RISTF st LB := X0qa.ist_facts_proof st0 LB st AR IS.

Definition rag_ctx (st1 st2 : mstate) (mm : aptr) (m3 : mem) (s' : PState) (errv' : word) (junk : list byte) (oo : mem) : Prop :=
ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
rmrep st2 m3 /\ ticks_ok st2 /\ unk_agree st2 o m3 /\ mem_inv rsegs m3 /\ stk rsegs m3 lo (bv_unsigned sp + -144) /\
rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
rw_cells rsegs m3 (errno_addr tp) [C4 errv'] /\ rauxv_ok m3 (bv_unsigned sp) /\
rpres_except (rmalloc_fp st0 st2 lo (bv_unsigned sp)) m m3 /\
brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s.

Definition rcnt_state (pc : Z) (st2 : mstate) (mm : aptr) (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m3 : mem) : machine_state :=
MS (mkR (Z_to_bv 64 0x328f8) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
(wz (usage st2 sc)) (wz 4096) (wz (size_class sc * UNIT + 16)) (wz 2048) (wz (size_class sc * UNIT * cnt1)) (wz (size_class sc * UNIT * cnt1 + 16)) a6' a7'
a1 (wz cnt1) (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc)) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc))
(wz (size_class sc * UNIT)) (Z_to_bv 64 RSIZE_CLASSES) s10 s11 t3' t4' t5' t6')
F (Z_to_bv 64 pc) fc None m3 (seg_rom rsegs).

Definition rHMM_stmt : Prop :=
forall st1 st2 mm m3 s' errv' junk oo (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
rag_ctx st1 st2 mm m3 s' errv' junk oo ->
1 <= cnt1 <= 32 -> 2048 < size_class sc * UNIT * cnt1 + UNIT ->
rimplT o (ag_mmap sc req k bail st2 mm cnt1) s' Q (rcnt_state 0x329cc st2 mm cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' m3).

Definition rHNEST_stmt : Prop :=
forall st1 st2 mm m3 s' errv' junk oo (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
rag_ctx st1 st2 mm m3 s' errv' junk oo ->
1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
rimplT o (ag_nest f sc k bail st2 mm cnt1) s' Q (rcnt_state 0x32a10 st2 mm cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' m3).

Hypothesis HMM : rHMM_stmt.
Hypothesis HNEST : rHNEST_stmt.

#[using="LB AR SC RQ FIT HMM HNEST"] Lemma rhag_ok : rHAG_stmt f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req.
Proof.
intros st1 st2 mm m3 s' errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk oo.
intros TF TR ACT0 LF IS2 ER2 AC2 REL G0 MSL MR3 TK3 UA3 MI3 ST3 FR3 ERR3 AUX3 PE03 BL2 PSM PSF PSO.
assert (CTXT : rag_ctx st1 st2 mm m3 s' errv' junk oo) by (repeat (split; [assumption|]); assumption).
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
unfold alloc_ceiling in CLO.
pose proof (X0qa.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
pose proof (mf_usage _ _ MF2 sc) as UR. change (usage (strip st2) sc) with (usage st2 sc) in UR.
pose proof (size_class_range sc SC) as SZR.
rewrite (ag_body_eq f sc req k bail st2 mm).
riprefixT. unfold rag_regs.
eapply evt_cut.
{ eapply (rcount_walk st2 m3 sc MR3 SC UR). exact MI3. }
cbv beta. intros ms' sfH_; first [ sf_destruct 4%nat sfH_ as a2'' a3'' a4'' -> | sf_fb; destruct sfH_ as (a2'' & a3'' & a4'' & ->) ].
set (size := size_class sc * UNIT).
set (cnt0 := if sc <? 9 then small_cnt_pick sc (usage st2 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st2 sc)) size).
assert (C0R : 1 <= cnt0 <= 32).
{ pose proof (rcnt0_range st2 sc SC) as X. change (1 <= cnt0 <= 32). split; [| apply X].
subst cnt0. destruct (Z.ltb_spec sc 9).
- unfold small_cnt_pick. pose proof (small_cnt_range sc 0). pose proof (small_cnt_range sc 1). pose proof (small_cnt_range sc 2).
destruct (negb _); [lia|]. destruct (negb _); lia.
- apply halve_big_pos; [| subst size; unfold UNIT; lia]. pose proof (med_cnt_range (Z.land sc 3) ltac:(pose proof (land3_range sc); lia)) as [MC _].
pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) (usage st2 sc) ltac:(lia)). lia. }
eapply evt_cut.
{ eapply (rcnt2_walk (usage st2 sc) size cnt0); [subst size; unfold UNIT; lia| lia| exact MI3]. }
cbv beta. intros ms' ->. unfold rcnt_regs.
set (cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0) in *.
assert (C1R : 1 <= cnt1 <= 32) by (subst cnt1; destruct (_ && _); lia).
assert (EC : ag_cnt1 sc st2 = cnt1).
{ unfold ag_cnt1. subst cnt1 cnt0 size. rewrite (Z.mul_comm UNIT (size_class sc)). reflexivity. }
rewrite EC. replace (UNIT * size_class sc * cnt1) with (size * cnt1) by (subst size; lia).
apply evt_done.
destruct (Z.ltb_spec (PGSZ / 2) (size * cnt1 + UNIT)) as [BIG|SMALLc].
- pose proof (HMM st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in BIG; cbn in BIG; subst size; lia)) as X.
unfold rcnt_state in X. subst size. unfold UNIT in X |- *. replace (size_class sc * 16 * cnt1 + 16) with (size_class sc * 16 * cnt1 + 16) in X by lia. exact X.
- pose proof (HNEST st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in SMALLc; cbn in SMALLc; subst size; lia)) as X.
unfold rcnt_state in X. subst size. unfold UNIT in X |- *. exact X.
Qed.
End LEVEL.
