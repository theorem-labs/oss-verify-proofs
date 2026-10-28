(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0p9 X0qn X0py X0qd X0px.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0p8 X0pd X0pe X0pa.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1ky X1lz X1m0 X1lw X1m4 X1la X1k8 X1lb X1lc X1ld.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Notation RAREACH := (AREACH_from ref_reserved).

Definition rcoreQ {RCEIL : RunCeiling} (o m0 : mem) (st : mstate) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
(res : mstate * option (aptr * Z)) (s' : PState) (ms' : machine_state) : Prop :=
match res with
| (st2, Some (g, idx)) =>
exists (b : aptr) (r : region) (m1 : mem) (errv : word) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra' : word),
ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK)
a0 a1 a2 a3 a4 a5 a6 a7 (pw st2 (Some g)) (wz idx) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x326b4) fc None m1 (seg_rom rsegs)
/\ rmrep st2 m1 /\ ticks_ok st2 /\ unk_agree st2 o m1 /\ mem_inv rsegs m1
/\ stk rsegs m1 lo (bv_unsigned sp + -48)
/\ rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]
/\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
/\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
< r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
rmalloc_fp st st2 lo (bv_unsigned sp) a)
/\ 0 <= c_mmap_counter (ctx st2) < 2^32
/\ slot_ok st2 g b r idx n
/\ (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0)
/\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
| (st2, None) =>
exists (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0v s1v (wz 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m1 (seg_rom rsegs)
/\ rmrep st2 m1 /\ ticks_ok st2 /\ mem_inv rsegs m1 /\ stk rsegs m1 lo (bv_unsigned sp)
/\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st st2 lo (bv_unsigned sp)) m0 m1
/\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
end.

Lemma renf_hyp_ret {RCEIL : RunCeiling} o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
renf_hyp (fun st1 r => ret (st1, r)) o m0 st s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo.
Proof.
intros st2 g b r idx m1 s' errv t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 ra'; intros.
apply rimplT_ret. apply evt_done. cbn [rcoreQ].
first [ unshelve sf_eexists 4%nat; [ exact (b) | exact (r) | exact (m1) | exact (errv) | ] | sf_fb; exists b, r, m1, errv ]. sf_eexists 17%nat. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

Lemma rfail_hyp_ret {RCEIL : RunCeiling} o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo :
rfail_hyp (fun st1 r => ret (st1, r)) o m0 st s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc lo.
Proof.
intros st2 m1 s' errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6; intros.
apply rimplT_ret. apply evt_done. cbn [rcoreQ].
exists m1, errv. sf_eexists 14%nat. split; [reflexivity|]. repeat match goal with |- _ /\ _ => split; [assumption|] end. assumption.
Qed.

Definition rbig_stmt {RCEIL : RunCeiling} : Prop :=
forall (o m0 : mem) (st : mstate) (LB : list block) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z) (t : N)
(m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' : word),
let st1 := set_tick t st in
RAREACH st LB -> RMFACTS st LB -> rmrep st m0 -> tp = Z_to_bv 64 RATP ->
alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - RAM_STACK -> MMAP_THRESHOLD <= n < 2^32 -> brk_link_ps st s ->
rmrep st1 m1 -> ticks_ok st1 -> unk_agree st1 o m1 -> mem_inv rsegs m1 ->
stk rsegs m1 lo (bv_unsigned sp + -48) ->
rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] ->
rw_cells rsegs m1 (errno_addr tp) [C4 errv] -> rauxv_ok m1 (bv_unsigned sp) ->
rpres_except (rmalloc_fp st st1 lo (bv_unsigned sp)) m0 m1 ->
rimplT o (malloc_core full_lay st1 n) s (rcoreQ o m0 st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo)
(MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 n) (Z_to_bv 64 RMLOCK) (Z_to_bv 64 131052) a1 a2 a3 a4 a5 a6 a7
s2r s3r s4r s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x32404) fc None m1 (seg_rom rsegs)).

Section CORE.
Context {RCEIL : RunCeiling}.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

#[using="as_pre as_inv RAS AS_PRE RBIG"] Lemma rmalloc_core_implT :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
(m : mem) (st : mstate) (LB : list block) (s : PState) (n lo : Z) (errv : word) (t : N),
RAREACH st LB -> RMFACTS st LB -> rmrep st m -> brk_link_ps st s ->
rauxv_ok m (bv_unsigned sp) ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
rw_cells rsegs m (errno_addr tp) [C4 errv] -> mem_inv rsegs m ->
tp = Z_to_bv 64 RATP ->
a0 = Z_to_bv 64 n -> 0 <= n < 2^32 -> (s_tick st < t)%N ->
rimplT m (malloc_core full_lay (set_tick t st) n) s
(rcoreQ m m st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs)).
Proof.
intros until t. intros AR MF MR BL AUX ST CLO LO ERR MI TP HA N TT.
pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (RAS_STACK_ge 0) as ASG.
assert (RB0 : forall rid r1, (s_regions st) !! rid = Some r1 -> 0 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
{ intros rid r1 H1. pose proof (rregion_facts st m rid r1 MR H1) as sfP_; first [ sf_destruct 4%nat sfP_ as X1 _ X2 _ | sf_fb; destruct sfP_ as (X1 & _ & X2 & _) ]. unfold alloc_ceiling in X2. lia. }
pose proof MR as sfP_; first [ sf_destruct 4%nat sfP_ as WF0 CX0 GL0 _ | sf_fb; destruct sfP_ as (WF0 & CX0 & GL0 & _) ]. destruct GL0 as (_ & NL & _).
assert (PREP : forall m1, munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
rmrep (set_tick t st) m1 /\ ticks_ok (set_tick t st) /\ unk_agree (set_tick t st) m m1
/\ rw_cells rsegs m1 (errno_addr tp) [C4 errv] /\ rauxv_ok m1 (bv_unsigned sp)
/\ rpres_except (rmalloc_fp st (set_tick t st) lo (bv_unsigned sp)) m m1).
{ intros m1 MU WM. unfold alloc_ceiling in CLO.
split. { apply rmrep_set_tick. eapply rmrep_transport_high; [exact MR| exact MU| exact WM| intros lo' hi' [E|[]]; inversion E; unfold alloc_ceiling; lia]. }
split. { apply ticks_ok_set_tick; [lia|]. exact (mf_ticks _ _ MF). }
split. { eapply unk_agree_munch; [| exact MU| |].
- eapply unk_agree_ext; [apply unk_agree_refl| reflexivity| intros; reflexivity| reflexivity].
- intros rid r1 H1 K1. pose proof (RB0 rid r1 H1). cbn. lia.
- intros rid r1 H1. pose proof (RB0 rid r1 H1). lia. }
split. { eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. subst tp. unfold RATP. rewrite unsigned_lit by lia. cbn. lia. }
split. { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. unfold RAUXV_CELL. constructor; [cbn; lia| constructor]. }
eapply rpres_except_of_munch; [exact MU| exact WM|]. intros a Ha NC. cbn. split; [|exact I]. intros HX. apply NC. left. left. lia. }
destruct (Z.le_gt_cases MMAP_THRESHOLD n) as [TH|TH].
-
riprefixT. eapply evt_cut.
{ eapply (rentry_big_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| unfold alloc_ceiling in CLO; lia| lia| exact MI]. }
intros ms' sfH_; first [ sf_destruct 8%nat sfH_ as a1' m1 -> FR ST1 MU WM MI1 | sf_fb; destruct sfH_ as (a1' & m1 & -> & FR & ST1 & MU & WM & MI1) ].
first [ pose proof (PREP m1 MU WM) as sfP_; sf_destruct 6%nat sfP_ as MR1 TK1 UA1 ERR1 AUX1 PE1 | sf_fb; destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1) ].
apply evt_done.
eapply (RBIG m m st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t); try eassumption.
+ unfold RAM_STACK. lia.
+ lia.
-
unfold malloc_core.
replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; lia).
riprefixT. eapply evt_cut.
{ eapply (rmalloc_entry_walk ra sp gp tp); [exact HA| unfold MMAP_THRESHOLD in *; lia| exact ST| unfold alloc_ceiling in CLO; lia| lia| exact MI| exact NL]. }
intros ms' sfH_; first [ sf_destruct 11%nat sfH_ as a0' a1' a2' a3' m1 -> FR ST1 MU WM MI1 | sf_fb; destruct sfH_ as (a0' & a1' & a2' & a3' & m1 & -> & FR & ST1 & MU & WM & MI1) ].
first [ pose proof (PREP m1 MU WM) as sfP_; sf_destruct 6%nat sfP_ as MR1 TK1 UA1 ERR1 AUX1 PE1 | sf_fb; destruct (PREP m1 MU WM) as (MR1 & TK1 & UA1 & ERR1 & AUX1 & PE1) ].
pose proof (size_to_class_props n ltac:(lia)) as (SCR & SFIT & _).
apply evt_done.
eapply (rmalloc_small_implT (fun st1 r => ret (st1, r)) (ret (set_tick t st, None)) m m st LB s _ ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 F fc n lo t as_pre as_inv RAS).
all: try eassumption.
+ apply renf_hyp_ret.
+ apply rfail_hyp_ret.
+ unfold RAS_STACK. lia.
+ reflexivity.
+ intros sc' Hsc' Hfit'. eapply AS_PRE; [exact AR| exact MF| exact TT| exact Hsc'| lia| exact Hfit'].
Qed.
End CORE.
