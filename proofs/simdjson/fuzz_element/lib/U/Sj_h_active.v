(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_h_arith.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_h_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition SJ_GET_ACTIVE : Z := 0x4187c.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition sj_cells0 : list cell :=
  [C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (MallocRep.zeros 6); CB 32 (MallocRep.zeros 32);
   C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (MallocRep.zeros 6); CB 64 (MallocRep.zeros 64);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (MallocRep.zeros 4)].

Lemma sj_statics_fresh_cells : forall m, sj_statics m false -> rw_cells usegs m SJ_STATICS_LO sj_cells0.
Proof.
  intros m [H _]. unfold sj_cells in H. eapply rw_cells_recast; [exact H| | |].
  - cbn. repeat split.
  - vm_compute. reflexivity.
  - reflexivity.
Qed.

Definition getact_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SJ_ACTIVE_IMPL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(q - 64, q); (SJ_STATICS_LO, SJ_STATICS_HI)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo q /\ sj_statics m' true.

Lemma getact_init_spec : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo : Z),
  stk usegs m lo q -> GLOBALS_TOP <= lo -> lo <= q - 64 -> 0 <= q < 2^64 -> mem_inv usegs m -> sj_statics m true ->
  evt usegs (getact_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SJ_GET_ACTIVE) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST GLO LO Hq MI SJS. destruct SJS as (SJS & PJL & ELX).
  unfold SJ_GET_ACTIVE, GLOBALS_TOP, sj_cells, SJ_STATICS_LO, SJ_FALLBACK, SJ_FALLBACK_VPTR, SJ_STR_NAME, SJ_STR_DESC in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(q - 64, q); (0xedae8, SJ_IMPL_HI)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  step. carve_frame 32%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

  step. step. step. step. step. step. step. step.
  if_false.

  step. step. step. step. release_frame FR ST q. step. step.
  apply evt_done. unfold getact_post, SJ_ACTIVE_IMPL. do 14 eexists. eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [|eassumption]; intros x Hx; unfold SJ_STATICS_LO, SJ_STATICS_HI in Hx; cbn [outside] in Hx |- *; lia|].
  split; [eassumption|]. split; [eassumption|]. split; [exact ST|].
  split; [unfold sj_cells, SJ_STATICS_LO, SJ_FALLBACK, SJ_FALLBACK_VPTR, SJ_STR_NAME, SJ_STR_DESC; eassumption|].
  lazymatch goal with MU_ : munch _ m ?m', WM_ : wmono _ m ?m' |- Pj_loc_defs.pj_locale ?m' /\ _ =>
    split; [ eapply (pj_locale_munch _ m m' MU_ WM_); [intros a Ha; cbn [outside]; lia| exact PJL]
           | eapply (el_extra_munch _ m m' MU_ WM_); [intros a Ha; cbn [outside]; lia| exact ELX] ] end.
Qed.
Ltac hbr := first [if_true | if_false].

Lemma getact_fresh_spec : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo : Z),
  stk usegs m lo q -> GLOBALS_TOP <= lo -> lo <= q - 64 -> 0 <= q < 2^64 -> mem_inv usegs m -> sj_statics m false ->
  evt usegs (getact_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SJ_GET_ACTIVE) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST GLO LO Hq MI SJS. pose proof (sj_statics_locale _ _ SJS) as PJL. pose proof (sj_statics_extra _ _ SJS) as ELX.
  apply sj_statics_fresh_cells in SJS.
  unfold SJ_GET_ACTIVE, GLOBALS_TOP, sj_cells0, SJ_STATICS_LO in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(q - 64, q); (0xedae8, SJ_IMPL_HI)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  step. carve_frame 32%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

  do 8 step. hbr.

  do 3 step. do 3 step. hbr. do 3 step. hbr. do 2 step. hbr. do 5 hstep.

  do 2 step. hbr. step.
  step. carve_frame 32%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 32 junk0 [] [8;8;8;8]%nat) in FR0; [|reflexivity]. cbn [mk_CB_cells app] in FR0.
  do 3 hstep. do 5 step. hbr.
  do 3 step. do 3 step. hbr. do 3 step. hbr. do 2 step. hbr. do 5 hstep.
  do 2 step. hbr.

  do 7 step. do 4 hstep. step. hstep. hstep.

  do 5 step. release_frame FR0 ST (q + -32). step. do 5 hstep.

  step. hstep. step. step. do 5 hstep.

  do 4 step. release_frame FR ST q. step. step.
  apply evt_done. unfold getact_post, SJ_ACTIVE_IMPL. do 14 eexists. eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [|eassumption]; intros x Hx; unfold SJ_STATICS_LO, SJ_STATICS_HI in Hx; cbn [outside] in Hx |- *; lia|].
  split; [eassumption|]. split; [eassumption|]. split; [exact ST|].
  split; [unfold sj_cells, SJ_STATICS_LO, SJ_FALLBACK, SJ_FALLBACK_VPTR, SJ_STR_NAME, SJ_STR_DESC, MallocRep.wz; eassumption|].
  lazymatch goal with MU_ : munch _ m ?m', WM_ : wmono _ m ?m' |- Pj_loc_defs.pj_locale ?m' /\ _ =>
    split; [ eapply (pj_locale_munch _ m m' MU_ WM_); [intros a Ha; cbn [outside]; lia| exact PJL]
           | eapply (el_extra_munch _ m m' MU_ WM_); [intros a Ha; cbn [outside]; lia| exact ELX] ] end.
Qed.

Lemma getact_spec : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo : Z) (init : bool),
  stk usegs m lo q -> GLOBALS_TOP <= lo -> lo <= q - 64 -> 0 <= q < 2^64 -> mem_inv usegs m -> sj_statics m init ->
  evt usegs (getact_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SJ_GET_ACTIVE) fc None m (seg_rom usegs)).
Proof. intros until init. intros ST GLO LO Hq MI SJS. destruct init; [eapply getact_init_spec| eapply getact_fresh_spec]; eassumption. Qed.

End WithCeiling0.

