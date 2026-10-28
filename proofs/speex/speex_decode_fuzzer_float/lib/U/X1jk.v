(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0p9 X0qn X0py X0qc X0qd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0ql X0q1 X0o2 X0ns.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m4 X1k8.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
Import ListNotations.
Open Scope Z_scope.

Notation RAREACH := (AREACH_from ref_reserved).
Notation RISTF := (@ISTF_g _ ref_reserved).
Notation RAMP_AS := (AMP_AS_g ref_reserved).

Lemma rimplT_steq {RCEIL : RunCeiling} {R} o (t1 t2 : X1qu.M R) s Q ms :
steq t1 t2 -> rimplT o t1 s Q ms -> rimplT o t2 s Q ms.
Proof.
intros Hs H. unfold rimplT, mrun, prun in *. eapply rimplM_membed_steq; [|exact H]. apply eruns_steq. exact Hs.
Qed.

Lemma rimplT_nat2 {RCEIL : RunCeiling} {X Y R} o (P : forall R', (X -> Y -> X1qu.M R') -> X1qu.M R' -> X1qu.M R')
(k : X -> Y -> X1qu.M R) bail s (QS : option (X * Y) -> PState -> machine_state -> Prop) Q ms :
steq (P R k bail) (sbind (P _ kS bS) (KF k bail)) ->
rimplT o (P _ kS bS) s QS ms ->
(forall x y s' ms', QS (Some (x, y)) s' ms' -> leaf_of o (P _ kS bS) (Some (x, y)) -> rimplT o (k x y) s' Q ms') ->
(forall s' ms', QS None s' ms' -> leaf_of o (P _ kS bS) None -> rimplT o bail s' Q ms') ->
rimplT o (P R k bail) s Q ms.
Proof.
intros NAT H HK HB. eapply rimplT_steq; [apply steq_sym; exact NAT|].
eapply rimplT_bind; [eapply rimplT_reach; exact H|].
intros [[x y]|] s' ms' [HQ HL]; cbn [KF]; eauto.
Qed.

Definition ras_pre2 {RCEIL : RunCeiling} (st0 st : mstate) (sc req : Z) (fuel : nat) : Prop :=
(exists LB, RAREACH st0 LB /\ IST st0 st) /\ ENTRY_REL st0 st /\ ALLC st
/\ 0 <= sc < 48 /\ 0 <= req < 2^32 /\ req + 4 <= 16 * size_class sc.

Definition ras_post2 {RCEIL : RunCeiling}
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(o m : mem) (st0 st : mstate) (s : PState) (lo sc req : Z)
(st1 : mstate) (idx : Z) (s' : PState) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
/\ rw_cells rsegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' (bv_unsigned sp)
/\ rmrep st1 m' /\ ticks_ok st1 /\ unk_agree st1 o m'
/\ rpres_except (rmalloc_fp st0 st1 lo (bv_unsigned sp)) m m'
/\ mrel st st1 /\ brk_link_ps st1 s'
/\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
/\ as_inv2 st0 st st1 sc idx
/\ 0 <= c_mmap_counter (ctx st1) < 2^32
/\ (idx = -1
\/ (0 <= idx /\ exists g b r, active st1 sc = Some g /\ slot_ok st1 g b r idx req
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st1 g) * idx + get_stride (get_meta_rec st1 g) - 4 ->
rmalloc_fp st0 st1 lo (bv_unsigned sp) a)
/\ (s_regions st0 = ∅ -> rdv pans_mem o st1 (fst b, snd b + (16 + get_stride (get_meta_rec st1 g) * idx) + -3) = 0))).

Lemma ras_post2_post {RCEIL : RunCeiling} : ras_post2 = ras_post as_inv2.
Proof. reflexivity. Qed.

Definition ralloc_slot_stmt2 {RCEIL : RunCeiling} (fuel : nat) : Prop :=
forall (R : Type) (k : mstate -> Z -> X1qu.M R) (bail : X1qu.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
ras_pre2 st0 st sc req fuel ->
rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
(forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
rimplT o (k st1 idx) s' Q ms') ->
rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).

Lemma ralloc_slot_stmt2_all {RCEIL : RunCeiling} : (forall fuel, ralloc_slot_stmt2 fuel) -> ralloc_slot_stmt ras_pre2 as_inv2.
Proof. intros H. exact H. Qed.

Lemma ralloc_slot_stmtL {RCEIL : RunCeiling} (fuel : nat) : ralloc_slot_stmt2 fuel ->
forall (R : Type) (k : mstate -> Z -> X1qu.M R) (bail : X1qu.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st0 st : mstate) (lo sc req : Z) (errv : word),
ras_pre2 st0 st sc req fuel ->
rmrep st m -> ticks_ok st -> unk_agree st o m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAS_STACK sc ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 sc -> a1 = Z_to_bv 64 req ->
(forall st1 idx s' ms',
ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
leaf_of o (alloc_slot full_lay fuel st sc req kS bS) (Some (st1, idx)) ->
rimplT o (k st1 idx) s' Q ms') ->
rimplT o (alloc_slot full_lay fuel st sc req k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_slot_entry) fc None m (seg_rom rsegs)).
Proof.
intros AS. intros until errv. intros PRE MR TK UA BL AUX ST CLO LO ER MI TP A0 A1 K.
eapply (rimplT_nat2 o (fun R' k' b' => @alloc_slot R' full_lay fuel st sc req k' b') k bail s
(fun r s' ms' => match r with
| Some (st1, idx) => ras_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms'
| None => False end)).
- apply alloc_slot_nat.
- eapply AS; try eassumption. intros st1 idx s' ms' HP. apply rimplT_ret. apply evt_done. exact HP.
- intros x y s' ms' HP HL. exact (K x y s' ms' HP HL).
- intros s' ms' [].
Qed.

Lemma ralloc_meta_stmtL {RCEIL : RunCeiling} (am_pre : mstate -> Prop) : ralloc_meta_stmt am_pre ->
forall (R : Type) (k : mstate -> optr -> X1qu.M R) (bail : X1qu.M R) (o : mem)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
am_pre st -> s_ceil st = alloc_ceiling   ->
rmrep st m -> ticks_ok st -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RAM_STACK ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
tp = Z_to_bv 64 0x4d450 ->
(forall st1 mo s' ms',
ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
brk_link_ps st1 s' ->
leaf_of o (alloc_meta st kS bS) (Some (st1, mo)) ->
rimplT o (k st1 mo) s' Q ms') ->
rimplT o (alloc_meta st k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 ralloc_meta_entry) fc None m (seg_rom rsegs)).
Proof.
intros AM. intros until errv. intros PRE CEILS MR TK BL AUX ST CLO LO ER MI TP K.
eapply (rimplT_nat2 o (fun R' k' b' => @alloc_meta R' st k' b') k bail s
(fun r s' ms' => match r with
| Some (st1, mo) => ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' /\ brk_link_ps st1 s'
| None => False end)).
- apply alloc_meta_nat.
- eapply AM; try eassumption. intros st1 mo s' ms' HP HB. apply rimplT_ret. apply evt_done. split; assumption.
- intros x y s' ms' [HP HB] HL. exact (K x y s' ms' HP HB HL).
- intros s' ms' [].
Qed.
