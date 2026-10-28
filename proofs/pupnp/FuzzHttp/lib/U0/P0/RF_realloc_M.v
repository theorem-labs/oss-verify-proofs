(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SysMm SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs ImgFacts.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe Malloc_fp F_malloc_entry MallocKit_A3 ASlot_W14.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import RMallocRep RMallocTree RF_enframe RF_malloc_entry RF_realloc_A RF_realloc_B RF_realloc_C RF_realloc_D RMalloc_iface.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition rrmm_pre (ra sp gp tp t0 t1 s0 s1 a0 a1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 0x1ffec) s0 s1 a0 a1 a2 a3 a4 (Z_to_bv 64 63) a6 a7
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0x1ffeb) t4 t5 t6)
                         F (Z_to_bv 64 0x19c00) fc None m (seg_rom rsegs).

Lemma rrealloc_B_mm : forall (ra sp gp tp t0 t1 t2 t3 t4 t5 t6 s0 s1 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc (m : mem) (n : Z),
  a1 = Z_to_bv 64 n -> MMAP_THRESHOLD <= n < 2^32 -> mem_inv rsegs m ->
  evt rsegs (rrmm_pre ra sp gp tp t0 t1 s0 s1 a0 a1 a2 (Z_to_bv 64 63) a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 63) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19b44) fc None m (seg_rom rsegs)).
Proof.
  intros until n. intros -> N MI. unfold MMAP_THRESHOLD in N.
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
  step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
  step. step. if_cases K3; zify_cond K3. { exfalso. rewrite ?unsigned_lit in K3 by lia. lia. }
  step. step. if_cases K4; zify_cond K4. 2:{ exfalso. apply K4. reflexivity. }
  apply evt_done. reflexivity.
Qed.

Lemma pg_unique : forall y r1 r2, y <= r1 < y + 4096 -> r1 mod 4096 = 0 -> y <= r2 < y + 4096 -> r2 mod 4096 = 0 -> r1 = r2.
Proof. intros. Z.div_mod_to_equations. lia. Qed.

Lemma needed_eq : forall off n, 0 <= off -> 0 <= n ->
  (n + 4095 + 16 * off + 20) - (n + 4095 + 16 * off + 20) mod 4096 = round_up_pg (n + UNIT * off + UNIT + IB).
Proof.
  intros off n Ho Hn. pose proof (MI_Cnt.round_up_pg_spec (n + UNIT * off + UNIT + IB)) as [A B]. unfold UNIT, IB in *.
  apply (pg_unique (n + 16 * off + 16 + 4)); try assumption; Z.div_mod_to_equations; lia.
Qed.

Definition rrmm_join (ra sp gp tp t0 t1 s1 a1 a2 a3 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (a0v base nn on : Z) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 0x1ffec) (Z_to_bv 64 nn) s1 (Z_to_bv 64 a0v) a1 a2 a3 (Z_to_bv 64 on) a5 a6 a7
                              s2 (Z_to_bv 64 base) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0x1ffeb) t4 t5 t6)
                         F (Z_to_bv 64 0x19c50) fc None m (seg_rom rsegs).

Definition rrmm_call (sp gp tp t0 t1 s1 a5 a6 a7 s2 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (P B n base nn on : Z) : machine_state -> Prop :=
  fun ms' => ms' = MS (mkR (Z_to_bv 64 0x19c44) sp gp tp t0 t1 (Z_to_bv 64 0x1ffec) (Z_to_bv 64 nn) s1 (Z_to_bv 64 B) (Z_to_bv 64 on) (Z_to_bv 64 nn) (Z_to_bv 64 1)
                              (Z_to_bv 64 on) a5 a6 a7 s2 (Z_to_bv 64 base) (Z_to_bv 64 4095) (Z_to_bv 64 P) (Z_to_bv 64 n) s7 s8 s9 s10 s11 (Z_to_bv 64 0x1ffeb) t4 t5 t6)
                         F (Z_to_bv 64 0x19ed4) fc None m (seg_rom rsegs).

Lemma rrealloc_mm_pre {HCEIL : HasCeiling} : forall (ra sp gp tp t0 t4 t5 t6 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) F fc (m : mem)
    (P B n off low maplen : Z),
  let base := UNIT * off in let on := 4096 * maplen in let nn := round_up_pg (n + UNIT * off + UNIT + IB) in
  P = B + 16 + base -> 0 <= off <= 255 -> 0 <= n < 2^32 -> 16 <= B -> B + on <= alloc_ceiling -> 0 <= low < 4096 -> 1 <= maplen ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => (on = nn /\ rrmm_join ra sp gp tp t0 (Z_to_bv 64 (B + 16)) s1 (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 (-4096)) (Z_to_bv 64 (n + 4095 + 16 * off + 20)) a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m P base nn on ms')
                     \/ (on <> nn /\ rrmm_call sp gp tp t0 (Z_to_bv 64 (B + 16)) s1 (Z_to_bv 64 (n + 4095 + 16 * off + 20)) a6 a7 s2 s7 s8 s9 s10 s11 t4 t5 t6 F fc m P B n base nn on ms'))
    (MS (mkR ra sp gp tp t0 (Z_to_bv 64 (B + 16)) (Z_to_bv 64 0x1ffec) s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) (Z_to_bv 64 B) (Z_to_bv 64 63) (Z_to_bv 64 (low + 4096 * maplen)) (Z_to_bv 64 63) a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0x1ffeb) t4 t5 t6)
        F (Z_to_bv 64 0x19c00) fc None m (seg_rom rsegs)).
Proof.
  intros until maplen. intros base on nn HP Ho Hn HB HC Hlow Hml MI. ceil_facts.
  assert (NN : (n + 4095 + 16 * off + 20) - (n + 4095 + 16 * off + 20) mod 4096 = nn) by (subst nn; apply needed_eq; lia).
  pose proof (MI_Cnt.round_up_pg_spec (n + UNIT * off + UNIT + IB)) as [RA RB]. fold nn in RA, RB. unfold UNIT, IB in RA.
  subst P base on. unfold UNIT, IB.
  step. step. rewrite (unsigned_lit (B + 16)) by lia. replace (B + 16 + 16 * off + - (B + 16)) with (16 * off) by lia.
  step. step. step. step. step.
  step. rewrite (unsigned_lit (n + 4095 + 16 * off + 20)) by lia. rewrite land_m4096 by lia. rewrite NN.
  step. rewrite ?(unsigned_lit (low + 4096 * maplen)) by lia. rewrite land_m4096 by lia. replace (low + 4096 * maplen - (low + 4096 * maplen) mod 4096) with (4096 * maplen) by (Z.div_mod_to_equations; lia).
  step. if_cases K0; zify_cond K0.
  - apply evt_done. left. split; [rewrite ?unsigned_lit in K0 by lia; lia|]. unfold rrmm_join. unfold UNIT. reflexivity.
  - step. step. step. step. step. step. step.
    apply evt_done. right. split; [intros E; apply K0; rewrite E; reflexivity|]. unfold rrmm_call. unfold UNIT. reflexivity.
Qed.

Lemma rrealloc_mm_ret : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x19c44) sp gp tp t0 t1 t2 s0 s1 s5 s6 a0 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 0x19c50) fc None m (seg_rom rsegs))
      (MS (mkR (Z_to_bv 64 0x19c44) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19c44) fc None m (seg_rom rsegs)).
Proof. intros. step. step. step. apply evt_done. reflexivity. Qed.

Lemma rrealloc_mm_fail : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  evt rsegs (fun ms' => exists a3', ms' = MS (mkR (Z_to_bv 64 0x19cf8) sp gp tp t0 t1 t2 a1 a0 a1 a1 (Z_to_bv 64 (-1)) a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (-1)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19c50) fc None m (seg_rom rsegs)).
Proof.
  intros. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  eapply evt_mono; [apply rrgen_tomalloc|]. intros ms' ->. eexists. reflexivity.
Qed.

Definition rrmm_mem (m : word -> option byte) (G Bn nn mword P E n k : Z) : word -> option byte :=
  rset_size_mem (write_to_mem (write_to_mem (write_to_mem m (wa (G + 16)) (le8 (wz Bn))) (wa (G + 32)) (le8 (wz (Z.lor (Z.land mword 4095) nn))))
                              (wa E) [b8 0]) P E n k.

Definition rrmm_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : word -> option byte) (G Bn nn mword P E n k : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ m' = rrmm_mem m G Bn nn mword P E n k
    /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Local Ltac read_k := lazymatch goal with BKc : bytes_at rsegs ?mc (?P - 3) [b8 ?k] |- _ =>
      pose proof (bytes_at_read rsegs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
      cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
      change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.
Local Ltac sok off len addr := lazymatch goal with W : wr_at rsegs ?mc (?P - 3) _ |- _ =>
    let H := fresh "SO" in
    pose proof (wr_at_store_ok rsegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
    replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.
Local Ltac sokG off len addr := lazymatch goal with W : wr_at rsegs ?mc (?G + 16) 24 |- _ =>
    let H := fresh "SO" in
    pose proof (wr_at_store_ok rsegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
    replace (G + 16 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.

Lemma rrealloc_mm_tail : forall (ra sp gp tp t0 t1 t2 a0 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 gw : word)
    (ra0 q0 q1 q2 q3 q4 q5 q6 : word) F fc (m : mem) (lo G Bn nn mword off n k : Z),
  let P := Bn + 16 + UNIT * off in let E := Bn + nn - IB in
  bv_unsigned gw = G -> mem_inv rsegs m ->
  ov_read_bytes rsegs m (wa (G + 32)) 8 = Some (le8 (wz mword)) -> 0 <= mword < 2^64 ->
  wr_at rsegs m (G + 16) 24 ->
  wr_at rsegs m (P - 3) (E - P + 4) ->
  bytes_at rsegs m (P - 3) [b8 k] -> 0 <= k < 256 ->
  (G + 40 <= P - 3 \/ E + 1 <= G + 16) -> G + 40 <= lo ->
  rw_cells rsegs m (bv_unsigned sp + -64) (rr_frame q6 q5 q4 q3 q2 q1 q0 ra0) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> E + 1 <= lo -> lo <= bv_unsigned sp - 64 ->
  16 <= Bn -> 0 <= off -> 0 <= n -> P + n <= E -> E - P - n < 2^31 -> 0 <= nn < 2^63 -> nn mod 4096 = 0 ->
  evt rsegs (rrmm_post ra0 sp gp tp q0 q1 q2 q3 q4 q5 q6 s7 s8 s9 s10 s11 F fc lo m G Bn nn mword P E n k)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 nn) gw a0 (Z_to_bv 64 n) (Z_to_bv 64 Bn) a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 (UNIT * off)) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19c50) fc None m (seg_rom rsegs)).
Proof.
  intros until k. intros P E HG MI RMW MW WG WR BK HK DG GLO FR ST ELO LO B16 OFF0 N0 PNE R31 NN NA. unfold rr_frame in *.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ gw) as GR. change (bv_modulus 64) with (2^64) in GR. rewrite HG in GR.
  subst P E. unfold UNIT, IB in *.
  set (P := Bn + 16 + 16 * off) in *. set (E := Bn + nn - 4) in *.
  set (r := E - P - n).
  assert (R0 : 0 <= r < 2^31) by (unfold r; lia).
  assert (K31 : 0 <= Z.land k 31 < 32).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound k (2^5)). lia. }
  assert (MW12 : 0 <= Z.land mword 4095 < 4096).
  { change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound mword (2^12)). lia. }
  assert (LOR : Z.lor (Z.land mword 4095) nn = Z.land mword 4095 + nn /\ 0 <= Z.land mword 4095 + nn < 2^64).
  { split; [| lia]. replace nn with (nn / 4096 * 2 ^ 12) at 1 by (change (2^12) with 4096; Z.div_mod_to_equations; lia).
    rewrite (lor_small_shl (nn / 4096) 12 (Z.land mword 4095)) by lia. change (2^12) with 4096. Z.div_mod_to_equations; lia. }
  destruct LOR as [LOR LORR].

  assert (JN : forall (t0v a1v a2v a3v a4v a5v a6v : word) (m4 : mem) (r' : Z),
    bv_unsigned a1v = r' -> 0 <= r' <= 5 ->
    mem_inv rsegs m4 -> wr_at rsegs m4 (P - 3) (E - P + 4) -> bytes_at rsegs m4 (P - 3) [b8 k] ->
    rw_cells rsegs m4 (bv_unsigned sp + -64) [C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 ra0] -> stk rsegs m4 lo (bv_unsigned sp + -64) ->
    (let m3e := write_to_mem (write_to_mem (write_to_mem m (wa (G + 16)) (le8 (wz Bn))) (wa (G + 32)) (le8 (wz (Z.lor (Z.land mword 4095) nn)))) (wa E) [b8 0] in
     let '(m4', r'') := (if 5 <=? r then (write_to_mem (write_to_mem (if r =? 0 then m3e else write_to_mem m3e (wa (E - r)) [b8 0]) (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5)
                         else ((if r =? 0 then m3e else write_to_mem m3e (wa (E - r)) [b8 0]), r)) in m4 = m4' /\ r' = r'') ->
    evt rsegs (rrmm_post ra0 sp gp tp q0 q1 q2 q3 q4 q5 q6 s7 s8 s9 s10 s11 F fc lo m G Bn nn mword P E n k)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0v t1 t2 (Z_to_bv 64 nn) gw (Z_to_bv 64 P) a1v a2v a3v a4v a5v a6v a7
               s2 (Z_to_bv 64 (16 * off)) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19d64) fc None m4 (seg_rom rsegs))).
  { intros t0v a1v a2v a3v a4v a5v a6v m4 r' HA1 HR' MI4 WR4 BK4 FR4 ST4 HM4.

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
    apply evt_done. unfold rrmm_post. do 14 eexists. eexists. split; [reflexivity|].
    split; [| split; assumption].
    lazymatch goal with E1 : ?mx = write_to_mem _ _ _ |- _ => rewrite E1 end.
    unfold rrmm_mem, rset_size_mem. fold E. fold r. destruct (5 <=? r); destruct HM4 as [-> ->]; reflexivity. }

  step. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. cbv in K0. lia. }

  assert (RMW' : ov_read_bytes rsegs m (Z_to_bv 64 (bv_unsigned gw + 32)) 8 = Some (le8 (wz mword))) by (rewrite HG; exact RMW).
  step. clear RMW'.

  step. step. step. step. step. step. step. step.
  rewrite ?(wz_unsigned mword) by lia. rewrite ?(unsigned_lit (Z.land mword 4095)), ?(unsigned_lit nn) by lia. rewrite LOR.
  rewrite ?(unsigned_lit (Bn + nn + -4)), ?(unsigned_lit (n + (Bn + 16 * off + 16))) by lia.
  replace (Bn + nn + -4 - (n + (Bn + 16 * off + 16))) with r by (unfold r, E, P; lia). rewrite (swrap32_small r) by lia.
  replace (Bn + 16 * off + 16) with P by (unfold P; lia). replace (Bn + nn + -4) with E by (unfold E; lia).

  sokG 0 8%nat (bv_unsigned gw + 16).
  step. change (le8 (Z_to_bv 64 Bn)) with (le8 (wz Bn)). sdk.
  sokG 16 8%nat (bv_unsigned gw + 32).
  step. change (le8 (Z_to_bv 64 (Z.land mword 4095 + nn))) with (le8 (wz (Z.land mword 4095 + nn))). sdk.
  sok (E - P + 3) 1%nat (Bn + nn + -4).
  step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.

  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  -
    step. step. eapply (JN _ _ _ _ _ _ _ _ 0); try assumption; [apply unsigned_lit; lia| lia|].
    rewrite KR. cbn zeta. rewrite Z.eqb_refl. cbn iota.
    repeat match goal with E1 : ?mx = write_to_mem _ _ _ |- _ => rewrite E1; clear E1 end.
    split; [| reflexivity]. rewrite HG. unfold E. repeat (f_equal; try (unfold wa; f_equal; lia)).
  -
    step. rewrite ?(unsigned_lit E), ?(unsigned_lit (n + P)) by lia. rewrite ?(swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (n + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.

    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small, ?signed_lit_small in K5 by lia.
    +
      step. eapply (JN _ _ _ _ _ _ _ _ r); try assumption; [apply unsigned_lit; lia| lia|].
      cbn zeta. replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      split; [| reflexivity].
      repeat match goal with E1 : ?mx = write_to_mem _ _ _ |- _ => rewrite E1; clear E1 end.
      rewrite HG. unfold E. repeat (f_equal; try (unfold wa; f_equal; lia)).
    +
      sok (E - P - 2) 1%nat (Bn + nn + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - P - 1) 4%nat (Bn + nn + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step. eapply (JN _ _ _ _ _ _ _ _ 5); try assumption; [apply unsigned_lit; lia| lia|].
      cbn zeta. replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      split; [| reflexivity].
      repeat match goal with E1 : ?mx = write_to_mem _ _ _ |- _ => rewrite E1; clear E1 end.
      rewrite HG. unfold E. repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.
