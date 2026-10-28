(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Nodes RzCPS NodesA SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Canon Stdio Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread I_consts RT_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma land_m8 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551608 = 8 * (x / 8).
Proof.
  intros x Hx. change 18446744073709551608 with (Z.ldiff (Z.ones 64) (Z.ones 3)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^3) with 8. lia.
Qed.

Lemma qc_word2 : forall r, 1 <= r <= 64 ->
  Z.land (bv_unsigned (Z_to_bv 64 (2147450880 + bv_unsigned (Z_to_bv 64 (6906512 + r + -1)) ≫ 3))) 18446744073709551608
  = if r <=? 48 then 2148314192 else 2148314200.
Proof.
  intros r Hr. rewrite (unsigned_lit (6906512 + r + -1)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  rewrite unsigned_lit by (split; [apply Z.add_nonneg_nonneg; [lia| apply Z.div_pos; lia]| Z.div_mod_to_equations; lia]).
  rewrite land_m8 by (split; [apply Z.add_nonneg_nonneg; [lia| apply Z.div_pos; lia]| Z.div_mod_to_equations; lia]).
  destruct (Z.leb_spec r 48); Z.div_mod_to_equations; lia.
Qed.

Section ReadB.
Hypothesis RIP : rip_stmt.

Lemma read_walkB_qc : forall (sp fd count r : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) junk junk1,
  stk asegs m lo (sp + -2144) -> 0x7fff7f800000 <= lo -> lo + 2304 <= sp -> sp < 2^47 -> 0 <= fd < 2^32 -> 0 <= count <= 65536 ->
  1 <= r <= 64 ->
  m2s_cells m ->
  ro_cells asegs m 0x800CAC50 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (sp + -2144) [CB 8 junk1; C8 (Z_to_bv 64 0x6ec20)] ->
  rw_cells asegs m (sp + -2128) [CB 2080 junk] ->
  rw_cells asegs m (sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv asegs m ->
  evt asegs (fun ms' => (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom asegs))
                 /\ stk asegs m lo sp)
    (MS (mkR (Z_to_bv 64 0x163014) (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 g_read_stage)
             (Z_to_bv 64 r) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
             (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 count) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x15d5c4) fc None m (seg_rom asegs)).
Proof using.
  intros until junk1. intros ST LO0 LO UT Hfd Hcnt Hr (GOT & SHC & HM) SW FRr FRb FRt MI.
  unfold g_read_stage, SHB in *. pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (ESr : bv_signed (Z_to_bv 64 r) = r).
  { unfold bv_signed. rewrite EUr. apply bv_swrap_small. change (bv_half_modulus 64) with (2^63). lia. }
  do 4 step.
  do 3 step. if_true.
  step.
  step. if_false.
  step. if_false.
  do 4 step. if_false.
  do 3 step.
  assert (C2 : bv_ltu (Z_to_bv 64 (r + -65)) (Z_to_bv 64 (-64)) = false).
  { unfold bv_ltu. rewrite !unsigned_lit_wrap. apply Z.ltb_ge. Z.div_mod_to_equations. lia. }
  rewrite C2; cbv iota.
  do 12 step.
  rewrite (qc_word2 r Hr).
  destruct (Z.leb_spec r 48) as [H48|H48].
  - step. step. step. if_false.
    release_frame FRr ST (sp + -2128).
    release_frame FRb ST (sp + -48).
    do 9 step.
    release_frame FRt ST sp.
    apply evt_done. split; [| exact ST].
    do 14 eexists. reflexivity.
  - step. step. step. if_false.
    release_frame FRr ST (sp + -2128).
    release_frame FRb ST (sp + -48).
    do 9 step.
    release_frame FRt ST sp.
    apply evt_done. split; [| exact ST].
    do 14 eexists. reflexivity.
Qed.

Lemma read_walkB_rip : forall (sp fd count r : Z) (ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) junk junk1,
  stk asegs m lo (sp + -2144) -> 0x7fff7f800000 <= lo -> lo + 2304 <= sp -> sp < 2^47 -> 0 <= fd < 2^32 -> 0 <= count <= 65536 ->
  65 <= r <= 65536 ->
  m2s_cells m -> acc asegs m g_read_stage r ->
  rw_cells asegs m (sp + -2144) [CB 8 junk1; C8 (Z_to_bv 64 0x6ec20)] ->
  rw_cells asegs m (sp + -2128) [CB 2080 junk] ->
  rw_cells asegs m (sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  mem_inv asegs m ->
  evt asegs (fun ms' => exists (m' : mem),
                 (exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs))
                 /\ munch [(sp + -2208, sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
                 /\ stk asegs m' lo sp)
    (MS (mkR (Z_to_bv 64 0x163014) (Z_to_bv 64 (sp + -2144)) gp tp t0 t1 t2 (Z_to_bv 64 sp) (Z_to_bv 64 g_read_stage)
             (Z_to_bv 64 r) (Z_to_bv 64 g_read_stage) (Z_to_bv 64 count) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
             (Z_to_bv 64 0) (Z_to_bv 64 63) (Z_to_bv 64 count) (Z_to_bv 64 fd) (Z_to_bv 64 1) s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x15d5c4) fc None m (seg_rom asegs)).
Proof using RIP.
  intros until junk1. intros ST LO0 LO UT Hfd Hcnt Hr M2S ACC FRr FRb FRt MI.
  unfold g_read_stage in *. pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(sp + -2208, sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUr : bv_unsigned (Z_to_bv 64 r) = r) by (apply unsigned_lit; lia).
  assert (ESr : bv_signed (Z_to_bv 64 r) = r).
  { unfold bv_signed. rewrite EUr. apply bv_swrap_small. change (bv_half_modulus 64) with (2^63). lia. }
  do 4 step.
  do 3 step. if_true.
  step.
  step. if_false.
  step. if_false.
  do 4 step. if_false.
  do 3 step.
  assert (C2 : bv_ltu (Z_to_bv 64 (r + -65)) (Z_to_bv 64 (-64)) = true).
  { unfold bv_ltu. rewrite !unsigned_lit_wrap. apply Z.ltb_lt. Z.div_mod_to_equations. lia. }
  rewrite C2; cbv iota.
  release_frame FRr ST (sp + -2128).
  assert (EUs : bv_unsigned (Z_to_bv 64 (sp + -2128)) = sp + -2128) by (apply unsigned_lit; lia).
  do 4 step.
  call RIP.
  - reflexivity.
  - reflexivity.
  - exact ACC.
  - lia.
  - left. unfold kLowMemEnd. lia.
  - exact M2S.
  - rewrite EUs. exact ST.
  - rewrite EUs. lia.
  - unfold kHighShadowEnd. lia.
  - exact MI.
  - rewrite EUs in POST. rename POST into ST.
    do 3 step. if_true.
    release_frame FRb ST (sp + -48).
    do 9 step.
    release_frame FRt ST sp.
    apply evt_done. eexists. split; [do 14 eexists; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact ST.
Qed.

End ReadB.
