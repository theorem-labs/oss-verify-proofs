(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0pb X0pa X0p9 X0qn X0py X0qc X0qd.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qg.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0qe X0ol X0pd X0qp.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ql X0q1 X0qf X0o1 X0o2 X0oj X0o3 X0o4 X0ns X0nt.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require X0qa.
Import ListNotations.
Open Scope Z_scope.

Lemma halve_big_pos F : forall cnt sz, 1 <= cnt -> 0 <= sz < 2^18 -> 1 <= halve_big F cnt sz.
Proof.
induction F as [|F IH]; intros cnt sz Hc Hs; cbn [halve_big]; [lia|].
destruct (Z.leb_spec (65536 * UNIT) (sz * cnt)) as [LE|GT]; [|lia].
apply IH; [|lia]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. unfold UNIT in LE.
assert (2 <= cnt) by nia. Z.div_mod_to_equations. lia.
Qed.

Section LEVEL.
Context {RCEIL : RunCeiling}.
Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> X1qu.M R) (bail : X1qu.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_ok m (bv_unsigned sp).
Hypothesis ST : stk asegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK (S f).
Hypothesis ERR : rw_cells asegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv asegs m.
Hypothesis MED : rw_cells asegs m MEDTAB medtab_cells.
Hypothesis GP : gp = Z_to_bv 64 AGP.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
implT o (k st1 idx) s' Q ms'.
Let F0 : ISTF st LB := X0qa.ist_facts_proof st0 LB st AR IS.

Definition ag_ctx (st1 st2 : mstate) (mm : aptr) (m3 : mem) (s' : PState) (errv' : word) (j : list byte) (oo : mem) : Prop :=
ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
mrep st2 m3 /\ ticks_ok st2 /\ unk_agree st2 o m3 /\ mem_inv asegs m3 /\ stk asegs m3 lo (bv_unsigned sp + -96) /\
rw_cells asegs m3 (bv_unsigned sp + -96) (ag_frame sc j s4 s3 s2 s1 s0 ra) /\
rw_cells asegs m3 (errno_addr tp) [C4 errv'] /\ auxv_ok m3 (bv_unsigned sp) /\ rw_cells asegs m3 MEDTAB medtab_cells /\
pres_except (malloc_fp st0 st2 lo (bv_unsigned sp)) m m3 /\
brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s.

Definition HMM_stmt : Prop :=
forall st1 st2 mm m3 s' errv' j oo (cnt1 : Z) (t0' t2' a3' t4' t6' : word),
ag_ctx st1 st2 mm m3 s' errv' j oo ->
1 <= cnt1 <= 32 -> 2048 < size_class sc * UNIT * cnt1 + UNIT ->
implT o (ag_mmap sc req k bail st2 mm cnt1) s' Q
(MS (mkR (Z_to_bv 64 0x163fc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' (wz (size_class sc * UNIT)) t2' (Z_to_bv 64 sc) (Z_to_bv 64 CTX)
(wz 4096) (wz (size_class sc * UNIT * cnt1)) (wz (usage st2 sc)) a3' (Z_to_bv 64 SIZE_CLASSES) (wz 2048) (wz cnt1) (Z_to_bv 64 (conc st2 mm))
(Z_to_bv 64 (sc + 10)) (wz (size_class sc)) a1 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (sc + 58)) t4' (wz (4 * cnt1)) t6')
F (Z_to_bv 64 0x16640) fc None m3 (seg_rom asegs)).

Definition HNEST_stmt : Prop :=
forall st1 st2 mm m3 s' errv' j oo (cnt1 : Z) (t0' t2' a3' t5' t6' : word),
ag_ctx st1 st2 mm m3 s' errv' j oo ->
1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
implT o (ag_nest f sc k bail st2 mm cnt1) s' Q
(MS (mkR (Z_to_bv 64 0x163fc) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' (wz (size_class sc * UNIT)) t2' (Z_to_bv 64 sc) (Z_to_bv 64 CTX)
(wz 4096) (wz (size_class sc * UNIT * cnt1)) (wz (usage st2 sc)) a3' (Z_to_bv 64 SIZE_CLASSES) (wz 2048) (wz cnt1) (Z_to_bv 64 (conc st2 mm))
(Z_to_bv 64 (sc + 10)) (wz (size_class sc)) a1 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (sc + 58)) (wz cnt1) t5' t6')
F (Z_to_bv 64 0x16954) fc None m3 (seg_rom asegs)).

Hypothesis HMM : HMM_stmt.
Hypothesis HNEST : HNEST_stmt.

End LEVEL.
