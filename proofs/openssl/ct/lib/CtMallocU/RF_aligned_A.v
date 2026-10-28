(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_B Malloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocKit_B RAligned_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl LibProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition raligned_entry_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (al n mp lo : Z) : machine_state -> Prop :=
  fun ms' => exists (m1 : word -> option byte) (junk : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x2b4d18) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 al) (Z_to_bv 64 n)
                  (Z_to_bv 64 (aligned_req al n)) (Z_to_bv 64 n) (Z_to_bv 64 16) (Z_to_bv 64 8) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmalloc_entry) fc None m1 (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m m1 /\ wmono ctusegs m m1 /\ mem_inv ctusegs m1 /\ stk ctusegs m1 lo (bv_unsigned sp + -48)
    /\ rw_cells ctusegs m1 (bv_unsigned sp + -48) [CB 8 junk; C8 s1; C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 0x2b4c40); C8 s0; C8 ra].

Lemma raligned_entry_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (al n mp lo : Z),
  a0 = Z_to_bv 64 mp -> a1 = Z_to_bv 64 al -> a2 = Z_to_bv 64 n ->
  (al = 32 \/ al = 64) -> 0 <= n -> aligned_req al n < 2^32 -> 0 <= mp < 2^64 ->
  rw_cells ctusegs m (RCTX + 928) [C4 (wz 0); C4 (wz 0)] ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv ctusegs m ->
  evt ctusegs (raligned_entry_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m al n mp lo)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 RPOSIX_MEMALIGN_SYM) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros -> -> -> HAL N0 NR MP REPL ST CLO LO MI.
  unfold RPOSIX_MEMALIGN_SYM, RCTX, aligned_req, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold OssFuzzTheorems.Proofs.openssl.ct.lib.Spec.Malloc.MCEIL in *; try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *.
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  change (3487024 + 928) with 3487952 in REPL.
  (* [comment removed for export] *)
  step. step. if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]. clear K0.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. st1. st1. st1.
  (* [comment removed for export] *)
  step. step. step. step.
  (* [comment removed for export] *)
  carve_frame 32%nat ST. st1. st1. st1. st1.
  (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1.
  { exfalso. apply K1. rewrite ?unsigned_lit by lia. destruct HAL as [-> | ->]; reflexivity. }
  clear K1.
  (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2.
  { exfalso. apply K2. rewrite ?unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small; [reflexivity| destruct HAL as [-> | ->]; lia]. }
  clear K2.
  (* [comment removed for export] *)
  step. step. if_cases K3; zify_cond K3.
  { exfalso. revert K3.
    assert (LX : Z.lxor al 18446744073709551615 = 18446744073709551615 - al).
    { change 18446744073709551615 with (Z.ones 64). rewrite <- Z.ldiff_ones_l_low; [| lia| apply (Z.le_lt_trans _ 7); [| lia]; destruct HAL as [-> | ->]; cbn; lia].
      symmetry. apply Z.sub_nocarry_ldiff. apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0.
      destruct (Z.lt_ge_cases i 64) as [Hi64|Hi64]; [rewrite Z.ones_spec_low by lia; cbn; apply andb_false_r|].
      rewrite (Z.bits_above_log2 al i); [reflexivity| lia|]. apply (Z.le_lt_trans _ 7); [destruct HAL as [-> | ->]; cbn; lia| lia]. }
    rewrite LX. rewrite ?unsigned_lit by lia. lia. }
  clear K3.
  (* [comment removed for export] *)
  step. step. step. try (if_cases K4; zify_cond K4; [| exfalso; apply K4; rewrite ?unsigned_lit by lia; reflexivity]; clear K4).
  (* [comment removed for export] *)
  step. step. if_cases K5; zify_cond K5; [| exfalso; rewrite ?unsigned_lit in K5 by lia; lia]. clear K5.
  (* [comment removed for export] *)
  step. step. step. step. step.
  apply evt_done. unfold raligned_entry_post, rmalloc_entry, aligned_req.
  lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists mx end.
  lazymatch goal with FR : rw_cells ctusegs _ (bv_unsigned sp + -48) [CB 8 ?j; _; _; _] |- _ => exists j end || eexists.
  split.
  { cbv delta [mkR]. repeat f_equal; first [reflexivity | lia | apply bv_eq; rewrite ?unsigned_lit by lia; first [reflexivity | lia]]. }
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
  (* [comment removed for export] *)
  lazymatch goal with
  | FR1 : rw_cells ctusegs ?mx (bv_unsigned sp + -48) ?cs1, FR2 : rw_cells ctusegs ?mx2 (bv_unsigned sp + -16) ?cs2 |- _ =>
      pose proof (proj2 (rw_cells_app ctusegs mx (bv_unsigned sp + -48) cs1 cs2) ltac:(split; [exact FR1| cbn; replace (bv_unsigned sp + -48 + 32) with (bv_unsigned sp + -16) by lia; exact FR2])) as FRS;
      cbn [app] in FRS; exact FRS
  end.
Qed.
End WithCeiling0.
