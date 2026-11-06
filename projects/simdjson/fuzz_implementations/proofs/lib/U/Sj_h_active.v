(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_h_arith.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.U Require Import Layout Exit Printf_wfile Pj_loc_defs Sj_iface Sj_kit Sj_new Sj_h_kit Imp_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition SJ_GET_ACTIVE : Z := 0x4461c.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma sj_cells_false_X : forall m A, rw_cells usegs m A (sj_cells false) -> rw_cells usegs m A sj_cells_zero.
Proof.
  intros m A H. unfold sj_cells in H. eapply rw_cells_recast; [exact H| | |].
  - cbn. repeat split.
  - vm_compute. reflexivity.
  - reflexivity.
Qed.
Definition sj_statics_mid (m : mem) : Prop := rw_cells usegs m SJ_STATICS_LO sj_cells_mid /\ LOCB m /\ el_extra m /\ imp_ios m.
Lemma sj_statics_mid_agree : forall P m m',
  agree_on P m m' -> (forall a, sjs_addr a -> P a) -> sj_statics_mid m -> sj_statics_mid m'.
Proof.
  intros P m m' AG HP (H & L & EX & IO). pose proof (sj_statics_agree P m m' true AG HP) as SA.
  unfold sj_statics_mid, sjs_addr, SJ_STATICS_LO, SJ_STATICS_HI in *.
  split; [eapply rw_cells_agree; [exact AG| exact H|]; intros a Ha; apply HP; rewrite sj_cellsX_size in Ha; lia|].
  split; [eapply LOCB_agree; [exact AG| | exact L]; intros a Ha; apply HP; lia|].
  split; [eapply el_extra_agree; [exact AG| | exact EX]; intros a Ha; apply HP; lia|].
  eapply imp_ios_agree; [exact AG| | exact IO]. intros a Ha. apply HP. pose proof (imp_ios_addr_bounds a Ha) as HB__; unfold IOS in HB__; lia.
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
  intros until lo. intros ST GLO LO Hq MI SJS. destruct SJS as (SJS & PJL & ELX & IOS0).
  unfold SJ_GET_ACTIVE, GLOBALS_TOP, sj_cells, SJ_STATICS_LO, SJ_FALLBACK, SJ_AVP_ARR, SJ_FALLBACK_VPTR, SJ_STR_NAME, SJ_STR_DESC in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(q - 64, q); (0xf3300, SJ_IMPL_HI)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  step. carve_frame 32%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

  step. step. step. step. step. step. step. step.
  if_false.

  step. step. step. step. release_frame FR ST q. step. step.
  apply evt_done. unfold getact_post, SJ_ACTIVE_IMPL. do 14 eexists. eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [|eassumption]; intros x Hx; unfold SJ_STATICS_LO, SJ_STATICS_HI in Hx; cbn [outside] in Hx |- *; lia|].
  split; [eassumption|]. split; [eassumption|]. split; [exact ST|].
  split; [unfold sj_cells, SJ_STATICS_LO, SJ_FALLBACK, SJ_AVP_ARR, SJ_FALLBACK_VPTR, SJ_STR_NAME, SJ_STR_DESC; eassumption|].
  lazymatch goal with MU_ : munch _ m ?m', WM_ : wmono _ m ?m' |- _ =>
    pose proof (agree_on_of_munch _ _ _ MU_ WM_) as AGF;
    split; [ eapply LOCB_agree; [exact AGF| intros a Ha; cbn [outside]; lia| exact PJL]
           | split; [ eapply (el_extra_munch _ m m' MU_ WM_); [intros a Ha; cbn [outside]; lia| exact ELX]
                    | eapply imp_ios_agree; [exact AGF| intros a Ha; pose proof (imp_ios_addr_bounds a Ha) as HB__; unfold IOS in HB__; cbn [outside]; lia| exact IOS0] ] ] end.
Qed.
Ltac hbr := first [if_true | if_false].

Lemma getact_mid_spec : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (q lo : Z),
  stk usegs m lo q -> GLOBALS_TOP <= lo -> lo <= q - 64 -> 0 <= q < 2^64 -> mem_inv usegs m -> sj_statics_mid m ->
  evt usegs (getact_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SJ_GET_ACTIVE) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST GLO LO Hq MI SJS. destruct SJS as (SJS & PJL & ELX & IOS0).
  unfold sj_cells_mid, sj_cellsX, gcell in SJS. cbn [app] in SJS.
  unfold SJ_GET_ACTIVE, GLOBALS_TOP, SJ_STATICS_LO, SJ_FALLBACK, SJ_AVP_ARR, SJ_FALLBACK_VPTR, SJ_STR_NAME, SJ_STR_DESC in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(q - 64, q); (0xf3300, SJ_IMPL_HI)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  step. carve_frame 32%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 32 junk [] [8;8;8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.

  do 8 step. hbr.

  do 3 step. do 3 step. hbr. do 3 step. hbr. do 2 step. hbr. do 5 hstep.

  do 2 step. hbr. step.

  step. carve_frame 32%nat ST.
  apply (rw_cells_split_CB usegs _ _ [] 32 junk0 [] [8;8;8;8]%nat) in FR0; [|reflexivity]. cbn [mk_CB_cells app] in FR0.
  do 3 hstep. do 5 step. hbr.
  do 3 step. release_frame FR0 ST (q + -32). step. step.

  step. hstep. step. step. do 5 hstep.

  do 4 step. release_frame FR ST q. step. step.
  apply evt_done. unfold getact_post, SJ_ACTIVE_IMPL. do 14 eexists. eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [|eassumption]; intros x Hx; unfold SJ_STATICS_LO, SJ_STATICS_HI in Hx; cbn [outside] in Hx |- *; lia|].
  split; [eassumption|]. split; [eassumption|]. split; [exact ST|].
  split; [unfold sj_cells, SJ_STATICS_LO, SJ_FALLBACK, SJ_AVP_ARR, SJ_FALLBACK_VPTR, SJ_STR_NAME, SJ_STR_DESC; eassumption|].
  lazymatch goal with MU_ : munch _ m ?m', WM_ : wmono _ m ?m' |- _ =>
    pose proof (agree_on_of_munch _ _ _ MU_ WM_) as AGF;
    split; [ eapply LOCB_agree; [exact AGF| intros a Ha; cbn [outside]; lia| exact PJL]
           | split; [ eapply (el_extra_munch _ m m' MU_ WM_); [intros a Ha; cbn [outside]; lia| exact ELX]
                    | eapply imp_ios_agree; [exact AGF| intros a Ha; pose proof (imp_ios_addr_bounds a Ha) as HB__; unfold IOS in HB__; cbn [outside]; lia| exact IOS0] ] ] end.
Qed.

End WithCeiling0.
