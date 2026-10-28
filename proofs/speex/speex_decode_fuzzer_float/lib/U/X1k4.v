(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bs X1c2 X1bn X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0pb X0p9 X0qn X0py X0qd X0qg X0qe X0qf X0qh X0qj X0qk.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1qx X1r3.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qo X0ql X0q1 X0o1 X0o2 X0ns X0oc X0od X0oe X0of X0og X0oh X0oi X0pn.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1ky X1lz X1m0 X1m1 X1lg X1lw X1lx X1m4 X1kr X1lb X1ld X1li X1lj X1k8 X1jk X1ly.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rta_frame {RCEIL : RunCeiling} (junk : list byte) (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) : list cell :=
[CB 48 junk; C8 run_canary; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Lemma ras_ret {RCEIL : RunCeiling} : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m0 m : word -> option byte) (W : list (Z * Z)) (junk : list byte) (st' : mstate) (lo : Z),
rmrep st' m -> mem_inv rsegs m ->
rw_cells rsegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
stk rsegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m -> wmono rsegs m0 m ->
evt rsegs (fun ms' => exists (a1' a2' : word) m',
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m' (seg_rom rsegs)
/\ munch ((bv_unsigned sp - 144, bv_unsigned sp) :: W)%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp) /\ rmrep st' m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x32f60) fc None m (seg_rom rsegs)).
Proof.
intros until lo. intros MR' MI FR ST LO LOLE MU WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof MR' as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ (_ & _ & _ & _ & GUARD) _ | sf_fb; destruct sfP_ as (_ & _ & (_ & _ & _ & _ & GUARD) & _) ].
unfold alloc_ceiling, RSSP_GUARD, rta_frame in *.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs. pose proof (wmono_refl rsegs m) as WMs.

st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR2 : rmrep st' mX)
by (eapply rmrep_transport_high; [exact MR' | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply evt_done. sf_eexists 3%nat. split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR2.
Qed.

Section FIN.
Context {RCEIL : RunCeiling}.
Variables (st : mstate) (m : mem) (g : aptr) (mask : Z) (lo : Z).
Let G := conc st g.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis MASK : 0 < mask < 2^32.
Hypothesis CLO : alloc_ceiling <= lo.

#[using="MR MSL MASK CLO"] Lemma rfin_walk :
forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 gw : word)
(s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc junk,
bv_unsigned gw = G ->
rw_cells rsegs m (bv_unsigned sp + -144) (rta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
stk rsegs m lo (bv_unsigned sp + -144) -> lo <= bv_unsigned sp - 144 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists (a1' a2' a3' : word) m' k,
0 <= k < 32 /\ lowbit mask = 2 ^ k /\
ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (wz k) a1' a2' a3' a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
F (ret_pc rav) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rmrep (upd_meta g (m_set_avail (mask - lowbit mask)) st) m')
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 gw (wz (sxv mask)) a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x328a0) fc None m (seg_rom rsegs)).
Proof.
intros until junk. intros HG FR ST LO MI.
pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_chunk_facts st m g MR MSL) as sfP_; first [ sf_destruct 6%nat sfP_ as CH Gpos GC GI1 GI2 _ | sf_fb; destruct sfP_ as (CH & Gpos & GC & GI1 & GI2 & _) ]. fold G in CH, Gpos, GC, GI1, GI2.
unfold meta_cells in CH. rewrite <- HG in CH.
destruct (lowbit_facts mask ltac:(lia)) as (k & Hk & LB).
assert (P2 : 0 < 2 ^ k <= mask).
{ first [ pose proof (lowbit_nonzero mask ltac:(lia)) as sfP_; sf_destruct 4%nat sfP_ as k' Hk' E L | sf_fb; destruct (lowbit_nonzero mask ltac:(lia)) as (k' & Hk' & E & L) ]. rewrite LB in E.
apply Z.pow_inj_r in E; [|lia|lia|lia]. subst k'. split; [apply Z.pow_pos_nonneg; lia| exact L]. }
assert (P32 : 2 ^ k < 2 ^ 32) by (apply Z.pow_lt_mono_r; lia).
pose proof (sxv_range mask) as RA. pose proof (sxv_range (2 ^ k)) as RK.
unfold alloc_ceiling, rta_frame, RSSP_GUARD in *.

step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.

step. rewrite (wz_unsigned (sxv mask)), (wz_unsigned (sxv (2 ^ k))) by assumption. rewrite (swrap_word (sxv mask - sxv (2 ^ k))).

pose proof (munch_refl [(G, G + 40)]%Z m) as MUg. pose proof (wmono_refl rsegs m) as WMg.
step.
lazymatch goal with H : rw_cells rsegs ?mc (bv_unsigned gw) ?cs |- _ =>
apply (rw_cells_congr rsegs mc (bv_unsigned gw) cs
(meta_cells st (m_set_avail (mask - lowbit mask) (get_meta_rec st g)))) in H;
[| unfold meta_cells; cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail]; rewrite LB, (le4_avail_sub mask (2 ^ k)) by lia; reflexivity
| reflexivity | cbn; tauto ];
rewrite HG in H;
pose proof (rmrep_put_meta_frame st m mc g _ MR MSL MUg WMg H) as MR1; rewrite <- upd_meta_put in MR1; clear H MUg WMg
end.

step. if_cases K0; zify_cond K0.
{ exfalso. rewrite ?wz_unsigned in K0 by assumption. pose proof (proj1 (sxv_zero (2 ^ k) ltac:(lia)) K0). lia. }
clear K0.

step. step. rewrite (Z.land_comm (bv_unsigned (wz (sxv mask)))). rewrite (negw_and_lowbit mask) by lia. rewrite LB.
step. step. change 125613361 with rDB32.
step. step. step. rewrite (mul_srliw27_sxv k) by lia.
pose proof (rdbi_range k) as DR.
step. step. rewrite ?(unsigned_lit (rdbi k)) by lia.
lazymatch goal with HI : mem_inv rsegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
step. rewrite ?zxb_b8, ?(wz_unsigned k) by lia. clear DBR.

step.
rewrite ?LB in MR1.
eapply evt_mono.
{ eapply (ras_ret sp gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav F fc m _ _ junk _ lo);
[exact MR1 | assumption | exact FR | exact ST | unfold alloc_ceiling; lia | lia | exact MU | exact WM]. }
cbv beta. intros ms' sfH_; first [ sf_destruct 9%nat sfH_ as a1' a2' m' -> MU' WM' MI' ST' MR' | sf_fb; destruct sfH_ as (a1' & a2' & m' & -> & MU' & WM' & MI' & ST' & MR') ].
sf_eexists 4%nat. exists k. split; [lia|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
End FIN.
