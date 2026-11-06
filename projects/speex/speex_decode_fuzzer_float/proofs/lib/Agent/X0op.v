(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0ok.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pu X0qm X0pc X0qn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0qh X0qk X0qj X0pm.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Definition am_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ CTX <= a < CTX + 928
\/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).

Lemma am_fp_alloc_fp st lo sp a : am_fp st lo sp a -> alloc_fp (fun k => k <> RKGroup) st lo sp a.
Proof. unfold am_fp, alloc_fp. tauto. Qed.
Lemma am_fp_stack st lo sp a : lo <= a < sp -> am_fp st lo sp a.
Proof. intros; left; assumption. Qed.
Lemma am_fp_ctx st lo sp a : CTX <= a < CTX + 928 -> am_fp st lo sp a.
Proof. intros; right; left; assumption. Qed.
Lemma am_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
lr_lo r <= a < r_base r + round_up_pg (r_len r) -> am_fp st lo sp a.
Proof. intros; right; right. exists rid, r. auto. Qed.
Lemma am_fp_meta {RCEIL : RunCeiling} : forall st m lo sp q a, mrep st m -> meta_slot st q ->
conc st q <= a < conc st q + 40 -> am_fp st lo sp a.
Proof.
intros st m lo sp q a MR sfH_; first [ sf_destruct 6%nat sfH_ as ar arr k Har Hk Eq | sf_fb; destruct sfH_ as (ar & arr & k & Har & Hk & Eq) ]; intros Ha. pose proof MR as (WF & _).
first [ pose proof (area_conc st ar arr WF Har) as sfP_; sf_destruct 10%nat sfP_ as ra Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | sf_fb; destruct (area_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC) ].
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (area_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
eapply am_fp_region; [exact Hra | exact NK | lia].
Qed.

Lemma am_fp_area {RCEIL : RunCeiling} : forall st m lo sp ak ar a, mrep st m -> (s_areas st) !! ak = Some ar ->
conc st ak <= a < conc st ak + 4096 -> am_fp st lo sp a.
Proof.
intros st m lo sp ak ar a MR Har Ha. pose proof MR as (WF & _).
first [ pose proof (area_conc st ak ar WF Har) as sfP_; sf_destruct 10%nat sfP_ as ra Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | sf_fb; destruct (area_conc st ak ar WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC) ].
pose proof (area_lr_lo st ak ar ra WF Har Hra).
eapply am_fp_region; [exact Hra | exact NK | lia].
Qed.
Lemma am_fp_same st st' lo sp a : s_regions st' = s_regions st -> am_fp st' lo sp a <-> am_fp st lo sp a.
Proof. intros ER. unfold am_fp. rewrite ER. tauto. Qed.

Definition am_ret_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (stF : mstate) (m : word -> option byte) (st' : mstate) (rv : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs)
/\ pres_except (am_fp stF lo (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
/\ stk asegs m' lo (bv_unsigned sp)
/\ mrep st' m'.

Definition am_took (st : mstate) (q : aptr) (cnt : Z) : mstate :=
upd_meta q clr_links (upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).

