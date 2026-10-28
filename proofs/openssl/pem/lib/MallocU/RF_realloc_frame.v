(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RF_enframe.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.pem.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition rr_frame (ra s0 s1 s2 s3 s4 s5 s6 : word) : list cell := [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Definition rrpro_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a2 m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b2768) fc None m' (seg_rom usegs)
    /\ rw_cells usegs m' (bv_unsigned sp + -64) (rr_frame ra s0 s1 s2 s3 s4 s5 s6)
    /\ stk usegs m' lo (bv_unsigned sp + -64)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Lemma rrealloc_prologue : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : word -> option byte) (lo : Z),
  bv_unsigned a0 <> 0 -> bv_unsigned a1 < 2^62 ->
  stk usegs m lo (bv_unsigned sp) -> 0x353000 <= lo -> lo <= bv_unsigned sp - 64 -> mem_inv usegs m ->
  evt usegs (rrpro_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b270c) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros A0 N ST ILO LO MI.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. step. if_cases K0; zify_cond K0. { exfalso. lia. }
  step. carve_frame 64%nat ST. step. step. step. step. step. step. step. step.
  step. step. step.
  step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  apply evt_done. unfold rrpro_post, rr_frame. do 2 eexists. split; [reflexivity|].
  split; [exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM| assumption].
Qed.

(* [comment removed for export] *)
Definition rrepi_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs)
    /\ stk usegs m lo (bv_unsigned sp).

Lemma rrealloc_epilogue : forall (x1 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 q0 q1 q2 q3 q4 q5 q6 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (lo : Z),
  rw_cells usegs m (bv_unsigned sp + -64) (rr_frame ra s0 s1 s2 s3 s4 s5 s6) ->
  stk usegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 64 -> mem_inv usegs m ->
  evt usegs (rrepi_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc lo m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 q0 q1 a0 a1 a2 a3 a4 a5 a6 a7 q2 q3 q4 q5 q6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b2b28) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until lo. intros FR ST LO MI. unfold rr_frame in FR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold rrepi_post. do 14 eexists. split; [reflexivity| exact ST].
Qed.

(* [comment removed for export] *)
Definition rr_setsize_mem (m : word -> option byte) (P E n k : Z) : word -> option byte :=
  let r := E - P - n in
  let m1 := if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0] in
  let m2 := if 5 <=? r then write_to_mem (write_to_mem m1 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)) else m1 in
  write_to_mem m2 (wa (P - 3)) [b8 (k + 32 * Z.min r 5)].

Definition rrinp_post (x1 sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (P E n k : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 m',
    ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b2b28) fc None m' (seg_rom usegs)
    /\ m' = rr_setsize_mem m P E n k
    /\ mem_inv usegs m'.

Lemma rrealloc_inplace_walk : forall (x1 sp gp tp t1 t2 s0 s1 a0 a2 a3 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (P E n b3 : Z),
  let k := Z.land b3 31 in
  bv_unsigned a0 = P -> mem_inv usegs m ->
  wr_at usegs m (P - 3) (E - P + 3) -> bytes_at usegs m (P - 3) [b8 b3] -> 0 <= b3 < 256 ->
  E + 5 <= 2^64 -> 16 <= P -> 0 <= n -> P + n <= E -> E - P - n < 2^31 ->
  evt usegs (rrinp_post x1 sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 F fc m P E n k)
      (MS (mkR x1 sp gp tp (wz E) t1 t2 s0 s1 a0 (Z_to_bv 64 n) a2 a3 a4 a5 (wz (E + 4)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b2ad8) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until b3. intros k HP MI WR BK B3 ETOP P16 N0 PNE EP.
  set (r := E - P - n).
  assert (KR : 0 <= k < 32). { unfold k. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  change (wz (E + 4)) with (Z_to_bv 64 (E + 4)). change (wz E) with (Z_to_bv 64 E).
  (* [comment removed for export] *)
  step. rewrite HP.
  step. rewrite ?(wz_unsigned E), ?(unsigned_lit E), ?(unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
  replace (E - (n + P)) with r by (unfold r; lia).
  (* [comment removed for export] *)
  assert (FINB : forall (rr : Z) (mc : word -> option byte) (y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 : word),
    0 <= rr <= 5 -> mem_inv usegs mc -> wr_at usegs mc (P - 3) (E - P + 3) -> bytes_at usegs mc (P - 3) [b8 b3] ->
    evt usegs (fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 m',
                 ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x2b2b28) fc None m' (seg_rom usegs)
                 /\ m' = write_to_mem mc (wa (P - 3)) [b8 (k + 32 * rr)] /\ mem_inv usegs m')
      (MS (mkR x1 sp gp tp y5 y6 y7 s0 s1 a0 (Z_to_bv 64 rr) y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
          F (Z_to_bv 64 0x2b2b14) fc None mc (seg_rom usegs))).
  { intros rr mc y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 RR MIc WRc BKc.
    (* [comment removed for export] *)
    pose proof (bytes_at_read usegs mc (P - 3) [b8 b3] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK.
    cbv [take drop Z.to_nat] in RK. replace (P - 3 + 0) with (P + -3) in RK by lia. change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK.
    rewrite <- HP in RK.
    step. clear RK. rewrite ?zxb_b8 by lia.
    step. rewrite ?(wz_unsigned b3) by lia. fold k.
    step. rewrite (unsigned_lit rr), Z.shiftl_mul_pow2 by lia.
    step. rewrite (unsigned_lit (rr * 2 ^ 5)), (unsigned_lit k) by lia. rewrite (lor_shl5 rr k) by lia.
    replace (Z.land k 31) with k by (unfold k; rewrite <- Z.land_assoc; reflexivity).
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. replace (k + rr * 32) with (k + 32 * rr) by lia.
    pose proof (wr_at_store_ok usegs mc _ _ 0 1%nat WRc ltac:(lia) ltac:(lia)) as SO.
    replace (P - 3 + 0) with (P + -3) in SO by lia. change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in SO. rewrite <- HP in SO.
    step. rewrite (le1_wz (k + 32 * rr)) by lia. rewrite HP. sdk.
    apply evt_done. do 13 eexists. split; [reflexivity|]. split; [| assumption].
    lazymatch goal with E2 : ?mx = write_to_mem _ _ _ |- _ => rewrite E2 end. first [reflexivity | f_equal; unfold wa; f_equal; lia]. }
  assert (R0 : 0 <= r < 2^31) by (unfold r; lia).
  (* [comment removed for export] *)
  step. if_cases KZ; zify_cond KZ; rewrite ?(unsigned_lit r) in KZ by lia.
  - (* [comment removed for export] *)
    step. step.
    eapply evt_mono; [apply (FINB 0 m); [lia| exact MI| exact WR| exact BK]; exact (wz 0)|].
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & m' & -> & Em & MI').
    unfold rrinp_post. do 13 eexists. split; [reflexivity|]. split; [| exact MI'].
    rewrite Em. unfold rr_setsize_mem. fold r. rewrite KZ. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta.
    rewrite Z.min_l by lia. reflexivity.
  - (* [comment removed for export] *)
    step. rewrite ?(wz_unsigned E), ?(unsigned_lit E), ?(unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by (unfold r; lia).
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. rewrite ?(wz_unsigned E), ?(unsigned_lit E) by lia. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (n + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    + (* [comment removed for export] *)
      step.
      lazymatch goal with E2 : ?mc = write_to_mem m _ _, MIc : mem_inv usegs ?mc, WRc : wr_at usegs ?mc (P - 3) _, BKc : bytes_at usegs ?mc (P - 3) _ |- _ =>
        eapply evt_mono; [apply (FINB r mc); [lia| exact MIc| exact WRc| exact BKc]; exact (wz 0)|] end.
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & m' & -> & Em & MI').
      unfold rrinp_post. do 13 eexists. split; [reflexivity|]. split; [| exact MI'].
      rewrite Em. unfold rr_setsize_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta. rewrite Z.min_l by lia.
      repeat match goal with E3 : ?mx = write_to_mem _ _ _ |- _ => rewrite E3 end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
    + (* [comment removed for export] *)
      sok (E - P - 2) 1%nat (E + 4 + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - P - 1) 4%nat (E + 4 + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      lazymatch goal with MIc : mem_inv usegs ?mc, WRc : wr_at usegs ?mc (P - 3) _, BKc : bytes_at usegs ?mc (P - 3) _ |- _ =>
        eapply evt_mono; [apply (FINB 5 mc); [lia| exact MIc| exact WRc| exact BKc]; exact (wz 0)|] end.
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & m' & -> & Em & MI').
      unfold rrinp_post. do 13 eexists. split; [reflexivity|]. split; [| exact MI'].
      rewrite Em. unfold rr_setsize_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta. rewrite Z.min_r by lia.
      repeat match goal with E3 : ?mx = write_to_mem _ _ _ |- _ => rewrite E3 end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.
End WithCeiling0.
