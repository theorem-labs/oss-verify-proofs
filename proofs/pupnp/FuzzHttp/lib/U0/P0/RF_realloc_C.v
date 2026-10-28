(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import RMallocRep RMallocTree RF_enframe RF_realloc_A.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rset_size_mem (m : word -> option byte) (P E n k : Z) : word -> option byte :=
  let r := E - P - n in
  let m3 := if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0] in
  let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m3, r) in
  write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].

Definition rrip_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : word -> option byte) (P E n k : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ m' = rset_size_mem m P E n k
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Ltac read_k := lazymatch goal with BKc : bytes_at rsegs ?mc (?P - 3) [b8 ?k] |- _ =>
      pose proof (bytes_at_read rsegs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
      cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
      change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.
Ltac sok off len addr := lazymatch goal with W : wr_at rsegs ?mc (?P - 3) _ |- _ =>
    let H := fresh "SO" in
    pose proof (wr_at_store_ok rsegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
    replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.

Lemma rrealloc_ip_walk : forall (ra sp gp tp t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 q0 q1 q2 q3 q4 q5 q6 : word) F fc (m : mem) (lo P E n k : Z),
  bv_unsigned a0 = P -> a1 = Z_to_bv 64 n ->
  mem_inv rsegs m ->
  wr_at rsegs m (P - 3) (E - P + 3) ->
  bytes_at rsegs m (P - 3) [b8 k] ->
  rw_cells rsegs m (bv_unsigned sp + -64) (rr_frame q6 q5 q4 q3 q2 q1 q0 ra0) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> E + 1 <= lo -> lo <= bv_unsigned sp - 64 ->
  16 <= P -> P + n <= E -> 0 <= n -> E - P - n < 2^31 -> 0 <= k < 256 ->
  evt rsegs (rrip_post ra0 sp gp tp q0 q1 q2 q3 q4 q5 q6 s7 s8 s9 s10 s11 a0 F fc lo m P E n k)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (E + 4)) a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19d28) fc None m (seg_rom rsegs)).
Proof.
  intros until k. intros HP HN MI WR BK FR ST ELO LO P16 PNE N0 R31 HK. subst a1. unfold rr_frame in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (r := E - P - n).
  assert (K31 : 0 <= Z.land k 31 < 32).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound k (2^5)). lia. }

  assert (JN : forall (t0v a1v a2v : word) (m4 : mem) (r' : Z),
    bv_unsigned a1v = r' -> 0 <= r' <= 5 ->
    mem_inv rsegs m4 -> wr_at rsegs m4 (P - 3) (E - P + 3) -> bytes_at rsegs m4 (P - 3) [b8 k] ->
    rw_cells rsegs m4 (bv_unsigned sp + -64) [C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 ra0] -> stk rsegs m4 lo (bv_unsigned sp + -64) ->
    (let '(m4', r'') := (if 5 <=? r then (write_to_mem (write_to_mem (if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0]) (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5)
                         else ((if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0]), r)) in m4 = m4' /\ r' = r'') ->
    evt rsegs (rrip_post ra0 sp gp tp q0 q1 q2 q3 q4 q5 q6 s7 s8 s9 s10 s11 a0 F fc lo m P E n k)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0v t1 t2 s0 s1 a0 a1v a2v a3 a4 a5 (Z_to_bv 64 (E + 4)) a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19d64) fc None m4 (seg_rom rsegs))).
  { intros t0v a1v a2v m4 r' HA1 HR' MI4 WR4 BK4 FR4 ST4 HM4.

    read_k. step. clear RK. rewrite ?zxb_b8 by lia.
    step. rewrite ?(wz_unsigned k) by lia.
    step. rewrite HA1, Z.shiftl_mul_pow2 by lia.
    step. rewrite (unsigned_lit (r' * 2 ^ 5)), (unsigned_lit (Z.land k 31)) by lia.
    rewrite (lor_shl5 r' (Z.land k 31)) by lia.
    replace (Z.land (Z.land k 31) 31) with (Z.land k 31) by (change 31 with (Z.ones 5); rewrite !Z.land_ones by lia; rewrite Z.mod_mod by lia; reflexivity).
    sok 0 1%nat (P + -3).
    step. rewrite (le1_wz (Z.land k 31 + Z.shiftl r' 5)) by (rewrite Z.shiftl_mul_pow2 by lia; lia). sdk.

    step. step. step. step. step. step. step. step. step. step.
    release_frame FR4 ST4 (bv_unsigned sp).
    apply evt_done. unfold rrip_post. do 14 eexists. eexists. split; [reflexivity|].
    split; [| split; assumption].
    lazymatch goal with E1 : ?mx = write_to_mem _ _ _ |- _ => rewrite E1 end.
    unfold rset_size_mem. fold r. destruct (5 <=? r); destruct HM4 as [-> ->]; reflexivity. }

  step. step. rewrite (unsigned_lit E), HP, (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
  replace (E - (n + P)) with r by lia.
  assert (R0 : 0 <= r < 2^31) by (unfold r; lia).

  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  -
    step. step. eapply (JN _ _ _ m 0); try assumption; [apply unsigned_lit; lia| lia|].
    rewrite KR. cbn. auto.
  -
    step. rewrite ?(unsigned_lit E), ?HP, ?(unsigned_lit (n + P)) by lia. rewrite ?(swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (n + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.

    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small, ?signed_lit_small in K5 by lia.
    +
      step. eapply (JN _ _ _ _ r); try assumption; [apply unsigned_lit; lia| lia|].
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      split; [| reflexivity]. lazymatch goal with E1 : ?mx = write_to_mem _ _ _ |- _ => rewrite E1 end. repeat (f_equal; try (unfold wa; f_equal; lia)).
    +
      sok (E - P - 2) 1%nat (E + 4 + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - P - 1) 4%nat (E + 4 + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step. eapply (JN _ _ _ _ 5); try assumption; [apply unsigned_lit; lia| lia|].
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      split; [| reflexivity].
      repeat match goal with E1 : ?mx = write_to_mem _ _ _ |- _ => rewrite E1; clear E1 end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.
