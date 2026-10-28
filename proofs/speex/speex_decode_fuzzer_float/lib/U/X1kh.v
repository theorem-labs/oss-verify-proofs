(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1c8 X1bj.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0pc X0qn X0qk X0pl X0pm X0qh X0qj X0op.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1lz X1m1 X1li.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ram_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ RCTX <= a < RCTX + 928
\/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).

Lemma ram_fp_alloc_fp st lo sp a : ram_fp st lo sp a -> ralloc_fp (fun k => k <> RKGroup) st lo sp a.
Proof. unfold ram_fp, ralloc_fp. tauto. Qed.
Lemma ram_fp_stack st lo sp a : lo <= a < sp -> ram_fp st lo sp a.
Proof. intros; left; assumption. Qed.
Lemma ram_fp_ctx st lo sp a : RCTX <= a < RCTX + 928 -> ram_fp st lo sp a.
Proof. intros; right; left; assumption. Qed.
Lemma ram_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
lr_lo r <= a < r_base r + round_up_pg (r_len r) -> ram_fp st lo sp a.
Proof. intros; right; right. exists rid, r. auto. Qed.
Lemma ram_fp_not_errno {RCEIL : RunCeiling} st lo sp a : ram_fp st lo sp a -> rregions_wf st -> alloc_ceiling <= lo ->
~ (errno_addr (Z_to_bv 64 0x4d450) <= a < errno_addr (Z_to_bv 64 0x4d450) + 4).
Proof.
intros [H|[H|(rid & r & Hr & _ & H)]] (_ & WR & _) LO; unfold RCTX, alloc_ceiling in *; rewrite ?unsigned_lit by lia; try lia.
first [ pose proof (WR _ _ Hr) as sfP_; sf_destruct 5%nat sfP_ as _ _ _ RBC RF | sf_fb; destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF) ]. first [ pose proof (rreserved_disjoint _ _ RF) as sfP_; sf_destruct 4%nat sfP_ as _ _ D23 D2 | sf_fb; destruct (rreserved_disjoint _ _ RF) as (_ & _ & D23 & D2) ].
pose proof (lr_lo_ge r). unfold alloc_ceiling in RBC. lia.
Qed.
Lemma ram_fp_meta {RCEIL : RunCeiling} : forall st m lo sp q a, rmrep st m -> meta_slot st q ->
conc st q <= a < conc st q + 40 -> ram_fp st lo sp a.
Proof.
intros st m lo sp q a MR sfH_; first [ sf_destruct 6%nat sfH_ as ar arr k Har Hk Eq | sf_fb; destruct sfH_ as (ar & arr & k & Har & Hk & Eq) ]; intros Ha. pose proof MR as (WF & _).
first [ pose proof (rarea_conc st ar arr WF Har) as sfP_; sf_destruct 10%nat sfP_ as ra Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | sf_fb; destruct (rarea_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC) ].
assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
pose proof (rarea_lr_lo st ar arr ra WF Har Hra).
unfold AREA_HDR, META_SIZE, NSLOTS in *.
eapply ram_fp_region; [exact Hra | exact NK | lia].
Qed.

Lemma ram_fp_area {RCEIL : RunCeiling} : forall st m lo sp ak ar a, rmrep st m -> (s_areas st) !! ak = Some ar ->
conc st ak <= a < conc st ak + 4096 -> ram_fp st lo sp a.
Proof.
intros st m lo sp ak ar a MR Har Ha. pose proof MR as (WF & _).
first [ pose proof (rarea_conc st ak ar WF Har) as sfP_; sf_destruct 10%nat sfP_ as ra Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | sf_fb; destruct (rarea_conc st ak ar WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC) ].
pose proof (rarea_lr_lo st ak ar ra WF Har Hra).
eapply ram_fp_region; [exact Hra | exact NK | lia].
Qed.
Lemma ram_fp_same st st' lo sp a : s_regions st' = s_regions st -> ram_fp st' lo sp a <-> ram_fp st lo sp a.
Proof. intros ER. unfold ram_fp. rewrite ER. tauto. Qed.

Definition ram_ret_post {RCEIL : RunCeiling} (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (stF : mstate) (m : word -> option byte) (st' : mstate) (rv : word) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ rpres_except (ram_fp stF lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ rmrep st' m'.

Definition ram_frame {RCEIL : RunCeiling} (junk : list byte) (s4 s3 s2 s1 s0 ra : word) : list cell :=
[CB 8 junk; C8 run_canary; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma ram_tail {RCEIL : RunCeiling} : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (q : aptr),
rmrep st m -> mem_inv rsegs m -> meta_slot st q ->
rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (upd_meta q clr_links st) (Z_to_bv 64 (conc st q)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st q)) a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3232c) fc None m (seg_rom rsegs)).
Proof.
intros until q. intros MR MI MSq FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ q MR MSq) as sfP_; first [ sf_destruct 5%nat sfP_ as GB0 GB1 GB2 GB4 _ | sf_fb; destruct sfP_ as (GB0 & GB1 & GB2 & GB4 & _) ].
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st q, conc st q + 40)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof MR as sfP_; first [ sf_destruct 4%nat sfP_ as _ _ (_ & _ & _ & _ & GUARD) _ | sf_fb; destruct sfP_ as (_ & _ & (_ & _ & _ & _ & GUARD) & _) ].
rmeta_chunk MR MSq CH.
unfold alloc_ceiling, RSSP_GUARD, ram_frame in *.
rmeta_open (conc st q) MUq WMq.

st1. st1.
rmeta_close MR MSq MUq WMq CH (put_meta q (clr_links (get_meta_rec st q)) st) MR2.
rewrite <- upd_meta_put in MR2.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z mX) as MUs; pose proof (wmono_refl rsegs mX) as WMs end.

st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }

st1. st1. st1. st1. st1. st1. st1. st1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
assert (MR3 : rmrep (upd_meta q clr_links st) mX)
by (eapply rmrep_transport_high; [exact MR2 | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; unfold alloc_ceiling; lia]) end.
clear MUs WMs.
release_frame FR ST (bv_unsigned sp).
apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
- intros x Hx. apply ram_fp_stack. lia.
- intros x Hx. eapply ram_fp_meta; [exact MR | exact MSq | lia]. }
apply evt_done. unfold ram_ret_post. sf_eexists 15%nat.
split; [reflexivity|].
split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR3.
Qed.

Lemma ram_b0 {RCEIL : RunCeiling} : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
(m : word -> option byte) (junk : list byte) (lo cnt : Z) (st : mstate) (q : aptr),
rmrep st m -> mem_inv rsegs m -> meta_slot st q -> 0 <= cnt < 2^64 ->
rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
evt rsegs (ram_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (am_took st q cnt) (Z_to_bv 64 (conc st q)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st q)) (Z_to_bv 64 cnt) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x32320) fc None m (seg_rom rsegs)).
Proof.
intros until q. intros MR MI MSq HC FR ST LO LOLE.
pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
pose proof (rmeta_slot_bounds st _ q MR MSq) as sfP_; first [ sf_destruct 5%nat sfP_ as GB0 GB1 GB2 GB4 _ | sf_fb; destruct sfP_ as (GB0 & GB1 & GB2 & GB4 & _) ].
pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU.
pose proof (wmono_refl rsegs m) as WM.
pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1.
unfold alloc_ceiling, RCTX, RMLOCK in *.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
pose proof (munch_refl [(RCTX + 24, RCTX + 40)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
unfold RCTX in MUc.

st1. st1. st1.
set (st1 := upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : rmrep st1 mX) end.
{ eapply (rmrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
- intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- left. unfold ctx_head_cells, RCTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
unfold pw at 2. cbn [oconc]. change (conc st1 (aadd q META_SIZE)) with (conc st (aadd q META_SIZE)).
rewrite (conc_aadd st q META_SIZE) by (first [ sf_destruct 6%nat MSq as a ar k Ha Hk -> | sf_fb; destruct MSq as (a & ar & k & Ha & Hk & ->) ]; cbn; pose proof MR as (WF' & _);
destruct (rarea_conc st a ar WF' Ha) as (ra & Hra & _); rewrite Hra; eauto).
unfold META_SIZE, wz. exact C1.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia.
- right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold RCTX. lia. }
clear MUc WMc C1.
change (conc st q) with (conc st1 q).
eapply evt_mono.
{ eapply (ram_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo st1 q);
[exact MR1 | assumption | exact MSq | exact FR | exact ST | unfold alloc_ceiling; lia | lia]. }
intros ms' RP. unfold ram_ret_post in RP |- *.
first [ sf_destruct 21%nat RP as v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 m' -> PE' WM' MI' ST' MR' | sf_fb; destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR') ].
sf_eexists 15%nat. split; [reflexivity|].
split.
{ apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
- eapply rpres_except_trans; [exact MU|]. eapply rpres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (ram_fp_same st st1 lo _ a eq_refl)). exact Ha.
- cbn [ivs_covered]. split; [|split; [|exact I]].
+ intros x Hx. apply ram_fp_stack. lia.
+ intros x Hx. apply ram_fp_ctx. unfold RCTX. lia. }
split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.
