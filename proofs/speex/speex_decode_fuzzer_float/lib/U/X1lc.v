(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0p9 X0qn X0py X0qd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0p8 X0pd.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1lw X1m4 X1la X1k8.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Definition renf_hyp {RCEIL : RunCeiling} {R} (K : mstate -> option (aptr * Z) -> X1qu.M R) (o m0 : mem) (st : mstate) (s : PState)
(Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) : Prop :=
forall (st2 : mstate) (g b : aptr) (r : region) (idx : Z) (m1 : mem) (s' : PState) (errv : word)
(t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
rmrep st2 m1 -> ticks_ok st2 -> unk_agree st2 o m1 -> mem_inv rsegs m1 ->
stk rsegs m1 lo (bv_unsigned sp + -48) ->
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
(forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
rmalloc_fp st st2 lo (bv_unsigned sp) a) ->
0 <= c_mmap_counter (ctx st2) < 2^32 ->
slot_ok st2 g b r idx n ->
(expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0) ->
mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (K st2 (Some (g, idx))) s' Q
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x326b4) fc None m1 (seg_rom rsegs)).

Definition rfail_hyp {RCEIL : RunCeiling} {R} (K : mstate -> option (aptr * Z) -> X1qu.M R) (o m0 : mem) (st : mstate) (s : PState)
(Q : R -> PState -> machine_state -> Prop)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (lo : Z) : Prop :=
forall (st2 : mstate) (m1 : mem) (s' : PState) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
rmrep st2 m1 -> ticks_ok st2 -> mem_inv rsegs m1 -> stk rsegs m1 lo (bv_unsigned sp) ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1 ->
mrel st st2 -> brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
rimplT o (K st2 None) s' Q
(MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom rsegs)).

Lemma rmalloc_fp_cases {RCEIL : RunCeiling} st st2 lo sp m0 m2 a :
rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a ->
lo <= a < sp \/ a < alloc_ceiling.
Proof.
intros (WF & _) (WF2 & _) H. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
unfold alloc_ceiling in *.
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
- left; exact H.
- right. rewrite unsigned_lit in H by lia. lia.
- right. unfold RCTX in H. lia.
- right. first [ pose proof (WR2 rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RC _ | sf_fb; destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _) ]. unfold alloc_ceiling in RC. lia.
- right. first [ pose proof (WR2 rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RC _ | sf_fb; destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _) ]. unfold alloc_ceiling in RC. lia.
- right. first [ pose proof (WR (fst b) r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RC _ | sf_fb; destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _) ]. unfold alloc_ceiling in RC. lia.
- right. first [ pose proof (WR (fst b) r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RC _ | sf_fb; destruct (WR (fst b) r Hr) as (_ & _ & _ & RC & _) ]. unfold alloc_ceiling in RC. lia.
- right. unfold alloc_ceiling in FC. lia.
Qed.

Lemma rframe_after_call {RCEIL : RunCeiling} st st2 lo sp' m0 m m' m2 A cs :
rmrep st m0 -> rmrep st2 m2 ->
rpres_except (rmalloc_fp st st2 lo sp') m m' -> rw_cells rsegs m A cs ->
sp' <= A -> alloc_ceiling <= A -> rw_cells rsegs m' A cs.
Proof.
intros MR0 MR2 PE H HA HC. eapply rpres_except_rw_cells; [exact PE| exact H|].
intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp' m0 m2 a MR0 MR2 Hfp); lia.
Qed.

Lemma rmalloc_fp_sp_mono {RCEIL : RunCeiling} st st2 lo sp1 sp2 a : sp1 <= sp2 -> rmalloc_fp st st2 lo sp1 a -> rmalloc_fp st st2 lo sp2 a.
Proof.
intros H [[X|X]|X]; [left; left; lia| left; right; exact X| right; exact X].
Qed.

Lemma rmalloc_fp_st_mono {RCEIL : RunCeiling} st sta stb lo sp a : mrel sta stb -> rmalloc_fp st sta lo sp a -> rmalloc_fp st stb lo sp a.
Proof. intros [HR _ _] H. eapply rmalloc_fp_mono; [exact HR| exact H]. Qed.

Lemma rmalloc_fp_image {RCEIL : RunCeiling} st st2 lo sp m0 m2 a :
rmrep st m0 -> rmrep st2 m2 -> rmalloc_fp st st2 lo sp a -> alloc_ceiling <= lo ->
0x3b000 <= a < 0x6e000 -> RCTX <= a < RCTX + 928 \/ 0x4d3ac <= a < 0x4d3b0.
Proof.
intros (WF & _) (WF2 & _) H CLO HA. pose proof WF as (_ & WR & _). pose proof WF2 as (_ & WR2 & _).
unfold alloc_ceiling in *.
assert (IMG : forall P : Prop, (forall rid r, (s_regions st) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)
/\ (forall rid r, (s_regions st2) !! rid = Some r -> r_base r <= a < r_base r + round_up_pg (r_len r) -> P)).
{ intros P. split; intros rid r Hr Ha.
- first [ pose proof (WR rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR rid r Hr) as (_ & _ & _ & _ & RF) ]. pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia.
- first [ pose proof (WR2 rid r Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ _ RF | sf_fb; destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF) ]. pose proof (rreserved_disjoint2 _ _ RF ltac:(lia)) as [D1 D2]. exfalso. lia. }
destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
- exfalso. lia.
- right. rewrite unsigned_lit in H by lia. lia.
- left. exact H.
- pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
- pose proof (lr_lo_ge r). apply (proj2 (IMG _) rid r Hr ltac:(lia)).
- apply (proj1 (IMG _) (fst b) r Hr Ha).
- apply (proj1 (IMG _) (fst b) r Hr Ha).
-
exfalso. pose proof WF as (RS & _). pose proof (rfresh_image st a (conj FC FR) RS). lia.
Qed.

Lemma rauxv_ok_malloc_fp {RCEIL : RunCeiling} st st2 lo sp m0 m2 m m' B :
rmrep st m0 -> rmrep st2 m2 -> rauxv_ok m B -> rpres_except (rmalloc_fp st st2 lo sp) m m' ->
alloc_ceiling <= lo -> sp <= B -> rauxv_ok m' B.
Proof.
intros MR0 MR2 AUX PE CLO SB. eapply rauxv_ok_pres; [exact AUX| exact PE| |].
- intros a Ha Hfp. destruct (rmalloc_fp_cases st st2 lo sp m0 m2 a MR0 MR2 Hfp); [lia|].
first [ sf_destruct 14%nat AUX as av x3 x4 x5 x16 x6 x11 x12 x23 rnd _ _ _ HH | sf_fb; destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & _ & _ & _ & HH) ]. unfold alloc_ceiling in *. lia.
- intros a Ha Hfp. unfold RAUXV_CELL, RLIBC in Ha.
destruct (rmalloc_fp_image st st2 lo sp m0 m2 a MR0 MR2 Hfp CLO ltac:(lia)) as [X|X]; unfold RCTX in X; lia.
Qed.
