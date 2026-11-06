(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_malloc_free A_F_malloc_fast A_F_malloc_enframe A_MallocTree A_MallocFacts_A A_MallocKit_A A_MallocRep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl MI_WGroup Realloc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RF_enframe RMallocKit_A RMalloc_fp.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition rinplace_mem (m : word -> option byte) (P E n b3 : Z) : word -> option byte :=
  let r := E - P - n in
  let m3 := if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0] in
  let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m3, r) in
  write_to_mem m4 (wa (P - 3)) [b8 (Z.land b3 31 + Z.shiftl r' 5)].

Definition rinpl_post (sp gp tp s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v : word) (F : bvmap 5 word) (fc : bv 32)
   (m : word -> option byte) (P E n b3 : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 m',
    ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
                  s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom rsegs)
    /\ m' = rinplace_mem m P E n b3
    /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Ltac read_k := lazymatch goal with BKc : bytes_at rsegs ?mc (?P - 3) [b8 ?k] |- _ =>
      pose proof (bytes_at_read rsegs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
      cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
      change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.
Ltac sok off len addr := lazymatch goal with W : wr_at rsegs ?mc (?P - 3) _ |- _ =>
    let H := fresh "SO" in
    pose proof (wr_at_store_ok rsegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
    replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.

Section INPL_W.
Variables (ra1 sp gp tp s7 s8 s9 s10 s11 t4 t5 t6 : word) (rav s0v s1v s2v s3v s4v s5v s6v : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (P n E b3 : Z).
Hypotheses (HN : 0 <= n) (PNE : P + n <= E) (R31 : E - P - n < 2^31) (P3 : 3 <= P) (EHI : E + 4 < 2^64) (B3R : 0 <= b3 < 256)
    (WR : wr_at rsegs m (P - 3) (E - P + 3)) (BK : bytes_at rsegs m (P - 3) [b8 b3])
    (FR : rw_cells rsegs m (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
    (SPE : E <= bv_unsigned sp) (SPH : bv_unsigned sp + 64 <= 2^64) (MI : mem_inv rsegs m).
Let POST := rinpl_post sp gp tp s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v F fc m P E n b3.

Lemma inpl_7d4 : forall (t0v t1v t2v a2v a3v a4v a5v a6v a7v s0 s1 s2 s3 s4 s5 s6 t3v : word) (mj : mem) (r' : Z),
  0 <= r' <= 5 ->
  mem_inv rsegs mj -> wr_at rsegs mj (P - 3) (E - P + 3) -> bytes_at rsegs mj (P - 3) [b8 b3] ->
  rw_cells rsegs mj (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  (forall m', m' = write_to_mem mj (wa (P - 3)) [b8 (Z.land b3 31 + Z.shiftl r' 5)] -> m' = rinplace_mem m P E n b3) ->
  evt rsegs POST
      (MS (mkR ra1 sp gp tp t0v t1v t2v s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 r') a2v a3v a4v a5v a6v a7v
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
          F (Z_to_bv 64 0x49e14) fc None mj (seg_rom rsegs)).
Proof.
  intros until r'. intros HR MIj WRj BKj FRj EM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (K31 : 0 <= Z.land b3 31 < 32).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }

  read_k. step. clear RK. rewrite ?zxb_b8 by lia.
  step. rewrite ?(wz_unsigned b3) by lia.
  step. rewrite (unsigned_lit r'), Z.shiftl_mul_pow2 by lia.
  step. rewrite (unsigned_lit (r' * 2 ^ 5)), (unsigned_lit (Z.land b3 31)) by lia. rewrite (lor_shl5 r' (Z.land b3 31)) by lia.
  rewrite <- Z.land_assoc. change (Z.land 31 31) with 31.
  sok 0 1%nat (P + -3).
  step. change (le1 (Z_to_bv 64 (Z.land b3 31 + Z.shiftl r' 5))) with (le1 (wz (Z.land b3 31 + Z.shiftl r' 5))).
  rewrite (le1_wz (Z.land b3 31 + Z.shiftl r' 5)) by (rewrite Z.shiftl_mul_pow2 by lia; lia). sdk.

  step. step. step. step. step. step. step. step. step. step.
  apply evt_done. unfold POST, rinpl_post. do 12 eexists. split; [reflexivity|].
  split; [apply EM; replace (P - 3) with (P + -3) by lia; assumption|]. split; assumption.
Qed.

Lemma inpl_798 : forall (t1v t2v s0 s1 a2v a3v a4v a5v a7v s2 s3 s4 s5 s6 t3v : word),
  evt rsegs POST
      (MS (mkR ra1 sp gp tp (Z_to_bv 64 E) t1v t2v s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2v a3v a4v a5v (Z_to_bv 64 (E + 4)) a7v
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
          F (Z_to_bv 64 0x49dd8) fc None m (seg_rom rsegs)).
Proof.
  intros.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (r := E - P - n).

  step. step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
  replace (E - (n + P)) with r by lia.
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  -
    step. step.
    eapply inpl_7d4; try eassumption; [lia|].
    intros m' ->. unfold rinplace_mem. fold r. rewrite KR. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta.
    change (Z.shiftl 0 5) with 0. reflexivity.
  -
    step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (n + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.

    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    +
      step.
      eapply inpl_7d4; try eassumption; [lia|].
      intros m' ->. unfold rinplace_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
    +
      sok (E - P - 2) 1%nat (E + 4 + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - P - 1) 4%nat (E + 4 + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      eapply inpl_7d4; try eassumption; [lia|].
      intros m' ->. unfold rinplace_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.

Lemma inpl_6f8 : forall (t0v t1v t2v s0 s1 a2v a5v a7v s2 s3 s4 s5 s6 t3v : word),
  evt rsegs POST
      (MS (mkR ra1 sp gp tp t0v t1v t2v s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 (P + n)) a2v (Z_to_bv 64 (E + 4)) (Z_to_bv 64 E) a5v
               (Z_to_bv 64 (E - P - n)) a7v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
          F (Z_to_bv 64 0x49d38) fc None m (seg_rom rsegs)).
Proof.
  intros.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (r := E - P - n).

  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  -
    step. step.
    eapply inpl_7d4; try eassumption; [lia|].
    intros m' ->. unfold rinplace_mem. fold r. rewrite KR. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta.
    change (Z.shiftl 0 5) with 0. reflexivity.
  -
    step. rewrite (unsigned_lit E), (unsigned_lit (P + n)) by lia. rewrite (swrap32_small (E - (P + n))) by lia.
    replace (E - (P + n)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (n + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.

    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    + step.
      eapply inpl_7d4; try eassumption; [lia|].
      intros m' ->. unfold rinplace_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
    +
      sok (E - P - 2) 1%nat (E + 4 + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - P - 1) 4%nat (E + 4 + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      eapply inpl_7d4; try eassumption; [lia|].
      intros m' ->. unfold rinplace_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.
End INPL_W.

Section INPL_R.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off b3 : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : rmrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis RS32 : stride - 4 - 16 * off - n < 2^32.
Hypothesis SL : (s_slots st2) !! (fst b, snd b + 16 + stride * k) = Some (g, k).
Hypothesis HB3 : Z.land b3 31 = k.

Lemma iconc_b : B = r_base r + snd b.
Proof. unfold B. apply (conc_region' st2 b r Hr). Qed.

Lemma isk_nonneg : 0 <= stride * k.
Proof. apply Z.mul_nonneg_nonneg; lia. Qed.

Lemma iwr8_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o < snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 256 ->
  rmrep (wr8 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst b, o) v stx)
  /\ s_regions (wr8 (fst b, o) v stx) = s_regions st2 /\ s_groups (wr8 (fst b, o) v stx) = s_groups st2.
Proof.
  intros stx mx o v MRx TKx ER EG Ho Hv. pose proof isk_nonneg.
  split; [| split; [apply ticks_ok_wr8; exact TKx| split; [rewrite <- ER; reflexivity| rewrite <- EG; reflexivity]]].
  apply (rmrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma iwr32_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o -> o + 4 <= snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 2^32 ->
  rmrep (wr32 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst b, o) v stx)
  /\ s_regions (wr32 (fst b, o) v stx) = s_regions st2 /\ s_groups (wr32 (fst b, o) v stx) = s_groups st2.
Proof.
  intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof isk_nonneg.
  split; [| split; [| split; [rewrite <- ER; reflexivity| rewrite <- EG; reflexivity]]].
  1-2: apply (rmrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv];
       intros b' gh Hb' Hf; rewrite EG in Hb'; destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma rinplace_mrep :
  let c : cptr := (fst b, snd b + 16 + stride * k) in
  rmrep (inplace_full st2 c off n) (rinplace_mem m4 (P0 + 16 * off) (P0 + stride - 4) n b3)
  /\ ticks_ok (inplace_full st2 c off n).
Proof.
  pose proof iconc_b as CB. pose proof isk_nonneg as SK.
  cbv zeta. unfold inplace_full.
  replace (s_slots st2 !! (fst b, snd b + 16 + stride * k)) with (Some (g, k)) by (symmetry; exact SL).
  cbv beta iota. set (st0 := set_tick _ st2).
  assert (M0 : rmrep st0 m4) by (apply rmrep_set_tick; exact MR).
  assert (T0 : ticks_ok st0) by (apply ticks_ok_set_tick; [lia| exact TK]).
  assert (ER0 : s_regions st0 = s_regions st2) by reflexivity.
  assert (EG0 : s_groups st0 = s_groups st2) by reflexivity.
  fold mr. fold stride.
  unfold aadd. cbn [fst snd].
  set (po := snd b + 16 + stride * k + UNIT * off).
  set (e := snd b + 16 + stride * k + (stride - IB)).
  assert (Epo : P0 + 16 * off = r_base r + po) by (unfold po, P0, UNIT; lia).
  assert (Ee : P0 + stride - 4 = r_base r + e) by (unfold e, P0, IB; lia).
  unfold rinplace_mem. rewrite Epo, Ee. cbv zeta.
  unfold ss_list, aadd. cbn [fst snd].
  set (rsv := e - po - n).
  replace (r_base r + e - (r_base r + po) - n) with rsv by (unfold rsv; lia).
  assert (RSV : 0 <= rsv < 2^32) by (unfold rsv, e, po, UNIT, IB; lia).
  assert (RSVe : rsv <= e - po) by (unfold rsv; lia).
  assert (PO : snd b + 16 + stride * k <= po) by (unfold po, UNIT; lia).
  assert (EE : e = snd b + 16 + stride * k + stride - 4) by (unfold e, IB; lia).
  clearbody po e rsv.

  rewrite wrs_app.
  set (stF := wrs (if negb (rsv =? 0) then _ else _) st0).
  set (mF := if rsv =? 0 then _ else _).
  assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st2 /\ s_groups stF = s_groups st2).
  { subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb wrs].
    - split; [exact M0|]. split; [exact T0|]. split; assumption.
    - destruct (iwr8_rep _ _ (e + - rsv) 0 M0 T0 ER0 EG0) as (M1 & T1 & R1 & G1); [lia| lia|].
      replace (r_base r + e - rsv) with (r_base r + (e + - rsv)) by lia.
      split; [exact M1|]. split; [exact T1|]. split; assumption. }
  clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).

  rewrite wrs_app.
  set (stG := wrs (if 5 <=? rsv then _ else _) stF).
  set (mG := if 5 <=? rsv then _ else _).
  assert (PG : rmrep stG (fst mG) /\ ticks_ok stG /\ 0 <= snd mG <= 5 /\ Z.min rsv 5 = snd mG
                /\ s_regions stG = s_regions st2 /\ s_groups stG = s_groups st2).
  { subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd wrs].
    - destruct (iwr8_rep _ _ (e + -5) 0 MF TF ERf EGf) as (M1 & T1 & R1 & G1); [lia| lia|].
      destruct (iwr32_rep _ _ (e + -4) rsv M1 T1 R1 G1) as (M2 & T2 & R2 & G2); [lia| lia| lia|].
      unfold wr32, aadd in M2, T2, R2, G2. cbn [fst snd] in M2, T2, R2, G2.
      replace (r_base r + e - 5) with (r_base r + (e + -5)) by lia.
      replace (r_base r + e - 4) with (r_base r + (e + -4)) by lia.
      split; [exact M2|]. split; [exact T2|]. split; [lia|]. split; [lia|]. split; assumption.
    - split; [exact MF|]. split; [exact TF|]. split; [lia|]. split; [lia|]. split; assumption. }
  clearbody stG mG. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
  destruct PG as (MG & TG & R2 & MIN & ERg & EGg).

  cbn [wrs].
  assert (KV : 0 <= Z.land b3 31 + Z.shiftl r2 5 < 256).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
    assert (0 <= Z.land b3 31 < 32) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound b3 (2^5)); lia). lia. }
  destruct (iwr8_rep _ _ (po + -3) (Z.land b3 31 + Z.shiftl r2 5) MG TG ERg EGg) as (MH & TH & _); [lia| exact KV|].
  rewrite MIN, <- HB3.
  replace (Z.land b3 31 + 32 * r2) with (Z.land b3 31 + Z.shiftl r2 5) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^5) with 32; lia).
  replace (r_base r + po - 3) with (r_base r + (po + -3)) by lia.
  destruct (rmrep_havoc _ _ (fst b, po) n MH TH) as [MZ TZ].
  split; [exact MZ| exact TZ].
Qed.
End INPL_R.

Section RSS.
Variables (st0 : mstate) (m4 : mem) (b : aptr) (r : region) (S k n off b3 : Z).
Let po := snd b + 16 + S * k + 16 * off.
Let e := snd b + 16 + S * k + (S - 4).

Hypothesis M0 : rmrep st0 m4.
Hypothesis T0 : ticks_ok st0.
Hypothesis Hr : (s_regions st0) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k.
Hypothesis SPAN : snd b + 16 + S * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= S.
Hypothesis NOGRP : forall b' gh, (s_groups st0) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + S * k - 4 \/ snd b + 16 + S * k + S - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= S.
Hypothesis RS32 : S - 4 - 16 * off - n < 2^32.
Hypothesis HB3 : Z.land b3 31 = k.

Lemma jsk_nonneg : 0 <= S * k.
Proof. apply Z.mul_nonneg_nonneg; lia. Qed.

Lemma jwr8_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st0 -> s_groups stx = s_groups st0 ->
  snd b + 16 + S * k - 4 <= o < snd b + 16 + S * k + S - 4 ->
  0 <= v < 256 ->
  rmrep (wr8 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst b, o) v stx)
  /\ s_regions (wr8 (fst b, o) v stx) = s_regions st0 /\ s_groups (wr8 (fst b, o) v stx) = s_groups st0.
Proof.
  intros stx mx o v MRx TKx ER EG Ho Hv. pose proof jsk_nonneg. rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  split; [| split; [apply ticks_ok_wr8; exact TKx| split; [rewrite <- ER; reflexivity| rewrite <- EG; reflexivity]]].
  apply (rmrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma jwr32_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st0 -> s_groups stx = s_groups st0 ->
  snd b + 16 + S * k - 4 <= o -> o + 4 <= snd b + 16 + S * k + S - 4 ->
  0 <= v < 2^32 ->
  rmrep (wr32 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst b, o) v stx)
  /\ s_regions (wr32 (fst b, o) v stx) = s_regions st0 /\ s_groups (wr32 (fst b, o) v stx) = s_groups st0.
Proof.
  intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof jsk_nonneg. rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  split; [| split; [| split; [rewrite <- ER; reflexivity| rewrite <- EG; reflexivity]]].
  1-2: apply (rmrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv];
       intros b' gh Hb' Hf; rewrite EG in Hb'; destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma rss_mrep :
  rmrep (havoc (fst b, po) n (wrs (ss_list (fst b, po) (fst b, e) n k) st0)) (rinplace_mem m4 (r_base r + po) (r_base r + e) n b3)
  /\ ticks_ok (havoc (fst b, po) n (wrs (ss_list (fst b, po) (fst b, e) n k) st0)).
Proof.
  pose proof jsk_nonneg as SK.
  assert (ER0 : s_regions st0 = s_regions st0) by reflexivity.
  assert (EG0 : s_groups st0 = s_groups st0) by reflexivity.
  unfold rinplace_mem. cbv zeta.
  unfold ss_list, aadd. cbn [fst snd].
  set (rsv := e - po - n).
  replace (r_base r + e - (r_base r + po) - n) with rsv by (unfold rsv; lia).
  assert (RSV : 0 <= rsv < 2^32) by (unfold rsv, e, po; lia).
  assert (RSVe : rsv <= e - po) by (unfold rsv; lia).
  assert (PO : snd b + 16 + S * k <= po) by (unfold po; lia).
  assert (EE : e = snd b + 16 + S * k + S - 4) by (unfold e; lia).
  clearbody po e rsv.

  rewrite wrs_app.
  set (stF := wrs (if negb (rsv =? 0) then _ else _) st0).
  set (mF := if rsv =? 0 then _ else _).
  assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st0 /\ s_groups stF = s_groups st0).
  { subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb wrs].
    - split; [exact M0|]. split; [exact T0|]. split; reflexivity.
    - destruct (jwr8_rep _ _ (e + - rsv) 0 M0 T0 ER0 EG0) as (M1 & T1 & R1 & G1); [lia| lia|].
      replace (r_base r + e - rsv) with (r_base r + (e + - rsv)) by lia.
      split; [exact M1|]. split; [exact T1|]. split; assumption. }
  clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).

  rewrite wrs_app.
  set (stG := wrs (if 5 <=? rsv then _ else _) stF).
  set (mG := if 5 <=? rsv then _ else _).
  assert (PG : rmrep stG (fst mG) /\ ticks_ok stG /\ 0 <= snd mG <= 5 /\ Z.min rsv 5 = snd mG
                /\ s_regions stG = s_regions st0 /\ s_groups stG = s_groups st0).
  { subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd wrs].
    - destruct (jwr8_rep _ _ (e + -5) 0 MF TF ERf EGf) as (M1 & T1 & R1 & G1); [lia| lia|].
      destruct (jwr32_rep _ _ (e + -4) rsv M1 T1 R1 G1) as (M2 & T2 & R2 & G2); [lia| lia| lia|].
      unfold wr32, aadd in M2, T2, R2, G2. cbn [fst snd] in M2, T2, R2, G2.
      replace (r_base r + e - 5) with (r_base r + (e + -5)) by lia.
      replace (r_base r + e - 4) with (r_base r + (e + -4)) by lia.
      split; [exact M2|]. split; [exact T2|]. split; [lia|]. split; [lia|]. split; assumption.
    - split; [exact MF|]. split; [exact TF|]. split; [lia|]. split; [lia|]. split; assumption. }
  clearbody stG mG. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
  destruct PG as (MG & TG & R2 & MIN & ERg & EGg).

  cbn [wrs].
  assert (KV : 0 <= Z.land b3 31 + Z.shiftl r2 5 < 256).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
    assert (0 <= Z.land b3 31 < 32) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound b3 (2^5)); lia). lia. }
  destruct (jwr8_rep _ _ (po + -3) (Z.land b3 31 + Z.shiftl r2 5) MG TG ERg EGg) as (MH & TH & _); [lia| exact KV|].
  rewrite MIN, <- HB3.
  replace (Z.land b3 31 + 32 * r2) with (Z.land b3 31 + Z.shiftl r2 5) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^5) with 32; lia).
  replace (r_base r + po - 3) with (r_base r + (po + -3)) by lia.
  destruct (rmrep_havoc _ _ (fst b, po) n MH TH) as [MZ TZ].
  split; [exact MZ| exact TZ].
Qed.
End RSS.

End CEIL.

Ltac read_k := lazymatch goal with BKc : bytes_at rsegs ?mc (?P - 3) [b8 ?k] |- _ =>
      pose proof (bytes_at_read rsegs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
      cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
      change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.
Ltac sok off len addr := lazymatch goal with W : wr_at rsegs ?mc (?P - 3) _ |- _ =>
    let H := fresh "SO" in
    pose proof (wr_at_store_ok rsegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
    replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_fast OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_enframe OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocTree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocRep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_WGroup OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Realloc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog.
Import RMallocRep.TwinB RMallocTree.TwinB RF_enframe.TwinB RMallocKit_A.TwinB RMalloc_fp.TwinB.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition rinplace_mem (m : word -> option byte) (P E n b3 : Z) : word -> option byte :=
  let r := E - P - n in
  let m3 := if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0] in
  let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m3, r) in
  write_to_mem m4 (wa (P - 3)) [b8 (Z.land b3 31 + Z.shiftl r' 5)].

Definition rinpl_post (sp gp tp s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v : word) (F : bvmap 5 word) (fc : bv 32)
   (m : word -> option byte) (P E n b3 : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 m',
    ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
                  s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom rsegs)
    /\ m' = rinplace_mem m P E n b3
    /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Ltac read_k := lazymatch goal with BKc : bytes_at rsegs ?mc (?P - 3) [b8 ?k] |- _ =>
      pose proof (bytes_at_read rsegs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
      cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
      change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.
Ltac sok off len addr := lazymatch goal with W : wr_at rsegs ?mc (?P - 3) _ |- _ =>
    let H := fresh "SO" in
    pose proof (wr_at_store_ok rsegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
    replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.

Section INPL_W.
Variables (ra1 sp gp tp s7 s8 s9 s10 s11 t4 t5 t6 : word) (rav s0v s1v s2v s3v s4v s5v s6v : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (P n E b3 : Z).
Hypotheses (HN : 0 <= n) (PNE : P + n <= E) (R31 : E - P - n < 2^31) (P3 : 3 <= P) (EHI : E + 4 < 2^64) (B3R : 0 <= b3 < 256)
    (WR : wr_at rsegs m (P - 3) (E - P + 3)) (BK : bytes_at rsegs m (P - 3) [b8 b3])
    (FR : rw_cells rsegs m (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
    (SPE : E <= bv_unsigned sp) (SPH : bv_unsigned sp + 64 <= 2^64) (MI : mem_inv rsegs m).
Let POST := rinpl_post sp gp tp s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v F fc m P E n b3.

Lemma inpl_7d4 : forall (t0v t1v t2v a2v a3v a4v a5v a6v a7v s0 s1 s2 s3 s4 s5 s6 t3v : word) (mj : mem) (r' : Z),
  0 <= r' <= 5 ->
  mem_inv rsegs mj -> wr_at rsegs mj (P - 3) (E - P + 3) -> bytes_at rsegs mj (P - 3) [b8 b3] ->
  rw_cells rsegs mj (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  (forall m', m' = write_to_mem mj (wa (P - 3)) [b8 (Z.land b3 31 + Z.shiftl r' 5)] -> m' = rinplace_mem m P E n b3) ->
  evt rsegs POST
      (MS (mkR ra1 sp gp tp t0v t1v t2v s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 r') a2v a3v a4v a5v a6v a7v
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
          F (Z_to_bv 64 0x4b618) fc None mj (seg_rom rsegs)).
Proof.
  intros until r'. intros HR MIj WRj BKj FRj EM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (K31 : 0 <= Z.land b3 31 < 32).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }

  read_k. step. clear RK. rewrite ?zxb_b8 by lia.
  step. rewrite ?(wz_unsigned b3) by lia.
  step. rewrite (unsigned_lit r'), Z.shiftl_mul_pow2 by lia.
  step. rewrite (unsigned_lit (r' * 2 ^ 5)), (unsigned_lit (Z.land b3 31)) by lia. rewrite (lor_shl5 r' (Z.land b3 31)) by lia.
  rewrite <- Z.land_assoc. change (Z.land 31 31) with 31.
  sok 0 1%nat (P + -3).
  step. change (le1 (Z_to_bv 64 (Z.land b3 31 + Z.shiftl r' 5))) with (le1 (wz (Z.land b3 31 + Z.shiftl r' 5))).
  rewrite (le1_wz (Z.land b3 31 + Z.shiftl r' 5)) by (rewrite Z.shiftl_mul_pow2 by lia; lia). sdk.

  step. step. step. step. step. step. step. step. step. step.
  apply evt_done. unfold POST, rinpl_post. do 12 eexists. split; [reflexivity|].
  split; [apply EM; replace (P - 3) with (P + -3) by lia; assumption|]. split; assumption.
Qed.

Lemma inpl_798 : forall (t1v t2v s0 s1 a2v a3v a4v a5v a7v s2 s3 s4 s5 s6 t3v : word),
  evt rsegs POST
      (MS (mkR ra1 sp gp tp (Z_to_bv 64 E) t1v t2v s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2v a3v a4v a5v (Z_to_bv 64 (E + 4)) a7v
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
          F (Z_to_bv 64 0x4b5dc) fc None m (seg_rom rsegs)).
Proof.
  intros.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (r := E - P - n).

  step. step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
  replace (E - (n + P)) with r by lia.
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  -
    step. step.
    eapply inpl_7d4; try eassumption; [lia|].
    intros m' ->. unfold rinplace_mem. fold r. rewrite KR. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta.
    change (Z.shiftl 0 5) with 0. reflexivity.
  -
    step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (n + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.

    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    +
      step.
      eapply inpl_7d4; try eassumption; [lia|].
      intros m' ->. unfold rinplace_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
    +
      sok (E - P - 2) 1%nat (E + 4 + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - P - 1) 4%nat (E + 4 + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      eapply inpl_7d4; try eassumption; [lia|].
      intros m' ->. unfold rinplace_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.

Lemma inpl_6f8 : forall (t0v t1v t2v s0 s1 a2v a5v a7v s2 s3 s4 s5 s6 t3v : word),
  evt rsegs POST
      (MS (mkR ra1 sp gp tp t0v t1v t2v s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 (P + n)) a2v (Z_to_bv 64 (E + 4)) (Z_to_bv 64 E) a5v
               (Z_to_bv 64 (E - P - n)) a7v s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
          F (Z_to_bv 64 0x4b53c) fc None m (seg_rom rsegs)).
Proof.
  intros.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (r := E - P - n).

  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  -
    step. step.
    eapply inpl_7d4; try eassumption; [lia|].
    intros m' ->. unfold rinplace_mem. fold r. rewrite KR. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta.
    change (Z.shiftl 0 5) with 0. reflexivity.
  -
    step. rewrite (unsigned_lit E), (unsigned_lit (P + n)) by lia. rewrite (swrap32_small (E - (P + n))) by lia.
    replace (E - (P + n)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (n + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.

    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    + step.
      eapply inpl_7d4; try eassumption; [lia|].
      intros m' ->. unfold rinplace_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
    +
      sok (E - P - 2) 1%nat (E + 4 + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - P - 1) 4%nat (E + 4 + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      eapply inpl_7d4; try eassumption; [lia|].
      intros m' ->. unfold rinplace_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.
End INPL_W.

Section INPL_R.
Variables (st2 : mstate) (m4 : mem) (g b : aptr) (r : region) (k n off b3 : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.

Hypothesis MR : rmrep st2 m4.
Hypothesis TK : ticks_ok st2.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis RS32 : stride - 4 - 16 * off - n < 2^32.
Hypothesis SL : (s_slots st2) !! (fst b, snd b + 16 + stride * k) = Some (g, k).
Hypothesis HB3 : Z.land b3 31 = k.

Lemma iconc_b : B = r_base r + snd b.
Proof. unfold B. apply (conc_region' st2 b r Hr). Qed.

Lemma isk_nonneg : 0 <= stride * k.
Proof. apply Z.mul_nonneg_nonneg; lia. Qed.

Lemma iwr8_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o < snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 256 ->
  rmrep (wr8 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst b, o) v stx)
  /\ s_regions (wr8 (fst b, o) v stx) = s_regions st2 /\ s_groups (wr8 (fst b, o) v stx) = s_groups st2.
Proof.
  intros stx mx o v MRx TKx ER EG Ho Hv. pose proof isk_nonneg.
  split; [| split; [apply ticks_ok_wr8; exact TKx| split; [rewrite <- ER; reflexivity| rewrite <- EG; reflexivity]]].
  apply (rmrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma iwr32_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st2 -> s_groups stx = s_groups st2 ->
  snd b + 16 + stride * k - 4 <= o -> o + 4 <= snd b + 16 + stride * k + stride - 4 ->
  0 <= v < 2^32 ->
  rmrep (wr32 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst b, o) v stx)
  /\ s_regions (wr32 (fst b, o) v stx) = s_regions st2 /\ s_groups (wr32 (fst b, o) v stx) = s_groups st2.
Proof.
  intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof isk_nonneg.
  split; [| split; [| split; [rewrite <- ER; reflexivity| rewrite <- EG; reflexivity]]].
  1-2: apply (rmrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv];
       intros b' gh Hb' Hf; rewrite EG in Hb'; destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma rinplace_mrep :
  let c : cptr := (fst b, snd b + 16 + stride * k) in
  rmrep (inplace_full st2 c off n) (rinplace_mem m4 (P0 + 16 * off) (P0 + stride - 4) n b3)
  /\ ticks_ok (inplace_full st2 c off n).
Proof.
  pose proof iconc_b as CB. pose proof isk_nonneg as SK.
  cbv zeta. unfold inplace_full.
  replace (s_slots st2 !! (fst b, snd b + 16 + stride * k)) with (Some (g, k)) by (symmetry; exact SL).
  cbv beta iota. set (st0 := set_tick _ st2).
  assert (M0 : rmrep st0 m4) by (apply rmrep_set_tick; exact MR).
  assert (T0 : ticks_ok st0) by (apply ticks_ok_set_tick; [lia| exact TK]).
  assert (ER0 : s_regions st0 = s_regions st2) by reflexivity.
  assert (EG0 : s_groups st0 = s_groups st2) by reflexivity.
  fold mr. fold stride.
  unfold aadd. cbn [fst snd].
  set (po := snd b + 16 + stride * k + UNIT * off).
  set (e := snd b + 16 + stride * k + (stride - IB)).
  assert (Epo : P0 + 16 * off = r_base r + po) by (unfold po, P0, UNIT; lia).
  assert (Ee : P0 + stride - 4 = r_base r + e) by (unfold e, P0, IB; lia).
  unfold rinplace_mem. rewrite Epo, Ee. cbv zeta.
  unfold ss_list, aadd. cbn [fst snd].
  set (rsv := e - po - n).
  replace (r_base r + e - (r_base r + po) - n) with rsv by (unfold rsv; lia).
  assert (RSV : 0 <= rsv < 2^32) by (unfold rsv, e, po, UNIT, IB; lia).
  assert (RSVe : rsv <= e - po) by (unfold rsv; lia).
  assert (PO : snd b + 16 + stride * k <= po) by (unfold po, UNIT; lia).
  assert (EE : e = snd b + 16 + stride * k + stride - 4) by (unfold e, IB; lia).
  clearbody po e rsv.

  rewrite wrs_app.
  set (stF := wrs (if negb (rsv =? 0) then _ else _) st0).
  set (mF := if rsv =? 0 then _ else _).
  assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st2 /\ s_groups stF = s_groups st2).
  { subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb wrs].
    - split; [exact M0|]. split; [exact T0|]. split; assumption.
    - destruct (iwr8_rep _ _ (e + - rsv) 0 M0 T0 ER0 EG0) as (M1 & T1 & R1 & G1); [lia| lia|].
      replace (r_base r + e - rsv) with (r_base r + (e + - rsv)) by lia.
      split; [exact M1|]. split; [exact T1|]. split; assumption. }
  clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).

  rewrite wrs_app.
  set (stG := wrs (if 5 <=? rsv then _ else _) stF).
  set (mG := if 5 <=? rsv then _ else _).
  assert (PG : rmrep stG (fst mG) /\ ticks_ok stG /\ 0 <= snd mG <= 5 /\ Z.min rsv 5 = snd mG
                /\ s_regions stG = s_regions st2 /\ s_groups stG = s_groups st2).
  { subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd wrs].
    - destruct (iwr8_rep _ _ (e + -5) 0 MF TF ERf EGf) as (M1 & T1 & R1 & G1); [lia| lia|].
      destruct (iwr32_rep _ _ (e + -4) rsv M1 T1 R1 G1) as (M2 & T2 & R2 & G2); [lia| lia| lia|].
      unfold wr32, aadd in M2, T2, R2, G2. cbn [fst snd] in M2, T2, R2, G2.
      replace (r_base r + e - 5) with (r_base r + (e + -5)) by lia.
      replace (r_base r + e - 4) with (r_base r + (e + -4)) by lia.
      split; [exact M2|]. split; [exact T2|]. split; [lia|]. split; [lia|]. split; assumption.
    - split; [exact MF|]. split; [exact TF|]. split; [lia|]. split; [lia|]. split; assumption. }
  clearbody stG mG. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
  destruct PG as (MG & TG & R2 & MIN & ERg & EGg).

  cbn [wrs].
  assert (KV : 0 <= Z.land b3 31 + Z.shiftl r2 5 < 256).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
    assert (0 <= Z.land b3 31 < 32) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound b3 (2^5)); lia). lia. }
  destruct (iwr8_rep _ _ (po + -3) (Z.land b3 31 + Z.shiftl r2 5) MG TG ERg EGg) as (MH & TH & _); [lia| exact KV|].
  rewrite MIN, <- HB3.
  replace (Z.land b3 31 + 32 * r2) with (Z.land b3 31 + Z.shiftl r2 5) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^5) with 32; lia).
  replace (r_base r + po - 3) with (r_base r + (po + -3)) by lia.
  destruct (rmrep_havoc _ _ (fst b, po) n MH TH) as [MZ TZ].
  split; [exact MZ| exact TZ].
Qed.
End INPL_R.

Section RSS.
Variables (st0 : mstate) (m4 : mem) (b : aptr) (r : region) (S k n off b3 : Z).
Let po := snd b + 16 + S * k + 16 * off.
Let e := snd b + 16 + S * k + (S - 4).

Hypothesis M0 : rmrep st0 m4.
Hypothesis T0 : ticks_ok st0.
Hypothesis Hr : (s_regions st0) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k.
Hypothesis SPAN : snd b + 16 + S * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= S.
Hypothesis NOGRP : forall b' gh, (s_groups st0) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + S * k - 4 \/ snd b + 16 + S * k + S - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= S.
Hypothesis RS32 : S - 4 - 16 * off - n < 2^32.
Hypothesis HB3 : Z.land b3 31 = k.

Lemma jsk_nonneg : 0 <= S * k.
Proof. apply Z.mul_nonneg_nonneg; lia. Qed.

Lemma jwr8_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st0 -> s_groups stx = s_groups st0 ->
  snd b + 16 + S * k - 4 <= o < snd b + 16 + S * k + S - 4 ->
  0 <= v < 256 ->
  rmrep (wr8 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) [b8 v]) /\ ticks_ok (wr8 (fst b, o) v stx)
  /\ s_regions (wr8 (fst b, o) v stx) = s_regions st0 /\ s_groups (wr8 (fst b, o) v stx) = s_groups st0.
Proof.
  intros stx mx o v MRx TKx ER EG Ho Hv. pose proof jsk_nonneg. rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  split; [| split; [apply ticks_ok_wr8; exact TKx| split; [rewrite <- ER; reflexivity| rewrite <- EG; reflexivity]]].
  apply (rmrep_wr8 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| |exact Hv].
  intros b' gh Hb' Hf. rewrite EG in Hb'. destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma jwr32_rep : forall stx mx (o v : Z),
  rmrep stx mx -> ticks_ok stx ->
  s_regions stx = s_regions st0 -> s_groups stx = s_groups st0 ->
  snd b + 16 + S * k - 4 <= o -> o + 4 <= snd b + 16 + S * k + S - 4 ->
  0 <= v < 2^32 ->
  rmrep (wr32 (fst b, o) v stx) (write_to_mem mx (wa (r_base r + o)) (le4 (wz v))) /\ ticks_ok (wr32 (fst b, o) v stx)
  /\ s_regions (wr32 (fst b, o) v stx) = s_regions st0 /\ s_groups (wr32 (fst b, o) v stx) = s_groups st0.
Proof.
  intros stx mx o v MRx TKx ER EG Ho Ho4 Hv. pose proof jsk_nonneg. rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN.
  split; [| split; [| split; [rewrite <- ER; reflexivity| rewrite <- EG; reflexivity]]].
  1-2: apply (rmrep_wr32 stx mx (fst b, o) v r MRx TKx); cbn [fst snd]; [rewrite ER; exact Hr| exact Hk| lia| lia| |exact Hv];
       intros b' gh Hb' Hf; rewrite EG in Hb'; destruct (NOGRP b' gh Hb' Hf); lia.
Qed.

Lemma rss_mrep :
  rmrep (havoc (fst b, po) n (wrs (ss_list (fst b, po) (fst b, e) n k) st0)) (rinplace_mem m4 (r_base r + po) (r_base r + e) n b3)
  /\ ticks_ok (havoc (fst b, po) n (wrs (ss_list (fst b, po) (fst b, e) n k) st0)).
Proof.
  pose proof jsk_nonneg as SK.
  assert (ER0 : s_regions st0 = s_regions st0) by reflexivity.
  assert (EG0 : s_groups st0 = s_groups st0) by reflexivity.
  unfold rinplace_mem. cbv zeta.
  unfold ss_list, aadd. cbn [fst snd].
  set (rsv := e - po - n).
  replace (r_base r + e - (r_base r + po) - n) with rsv by (unfold rsv; lia).
  assert (RSV : 0 <= rsv < 2^32) by (unfold rsv, e, po; lia).
  assert (RSVe : rsv <= e - po) by (unfold rsv; lia).
  assert (PO : snd b + 16 + S * k <= po) by (unfold po; lia).
  assert (EE : e = snd b + 16 + S * k + S - 4) by (unfold e; lia).
  clearbody po e rsv.

  rewrite wrs_app.
  set (stF := wrs (if negb (rsv =? 0) then _ else _) st0).
  set (mF := if rsv =? 0 then _ else _).
  assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st0 /\ s_groups stF = s_groups st0).
  { subst stF mF. destruct (Z.eqb_spec rsv 0) as [E|NE]; cbn [negb wrs].
    - split; [exact M0|]. split; [exact T0|]. split; reflexivity.
    - destruct (jwr8_rep _ _ (e + - rsv) 0 M0 T0 ER0 EG0) as (M1 & T1 & R1 & G1); [lia| lia|].
      replace (r_base r + e - rsv) with (r_base r + (e + - rsv)) by lia.
      split; [exact M1|]. split; [exact T1|]. split; assumption. }
  clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).

  rewrite wrs_app.
  set (stG := wrs (if 5 <=? rsv then _ else _) stF).
  set (mG := if 5 <=? rsv then _ else _).
  assert (PG : rmrep stG (fst mG) /\ ticks_ok stG /\ 0 <= snd mG <= 5 /\ Z.min rsv 5 = snd mG
                /\ s_regions stG = s_regions st0 /\ s_groups stG = s_groups st0).
  { subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd wrs].
    - destruct (jwr8_rep _ _ (e + -5) 0 MF TF ERf EGf) as (M1 & T1 & R1 & G1); [lia| lia|].
      destruct (jwr32_rep _ _ (e + -4) rsv M1 T1 R1 G1) as (M2 & T2 & R2 & G2); [lia| lia| lia|].
      unfold wr32, aadd in M2, T2, R2, G2. cbn [fst snd] in M2, T2, R2, G2.
      replace (r_base r + e - 5) with (r_base r + (e + -5)) by lia.
      replace (r_base r + e - 4) with (r_base r + (e + -4)) by lia.
      split; [exact M2|]. split; [exact T2|]. split; [lia|]. split; [lia|]. split; assumption.
    - split; [exact MF|]. split; [exact TF|]. split; [lia|]. split; [lia|]. split; assumption. }
  clearbody stG mG. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
  destruct PG as (MG & TG & R2 & MIN & ERg & EGg).

  cbn [wrs].
  assert (KV : 0 <= Z.land b3 31 + Z.shiftl r2 5 < 256).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32.
    assert (0 <= Z.land b3 31 < 32) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; pose proof (Z.mod_pos_bound b3 (2^5)); lia). lia. }
  destruct (jwr8_rep _ _ (po + -3) (Z.land b3 31 + Z.shiftl r2 5) MG TG ERg EGg) as (MH & TH & _); [lia| exact KV|].
  rewrite MIN, <- HB3.
  replace (Z.land b3 31 + 32 * r2) with (Z.land b3 31 + Z.shiftl r2 5) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^5) with 32; lia).
  replace (r_base r + po - 3) with (r_base r + (po + -3)) by lia.
  destruct (rmrep_havoc _ _ (fst b, po) n MH TH) as [MZ TZ].
  split; [exact MZ| exact TZ].
Qed.
End RSS.

End CEIL.

Ltac read_k := lazymatch goal with BKc : bytes_at rsegs ?mc (?P - 3) [b8 ?k] |- _ =>
      pose proof (bytes_at_read rsegs mc (P - 3) [b8 k] 0 1 BKc ltac:(lia) ltac:(cbn; lia)) as RK;
      cbv [take drop Z.to_nat] in RK; replace (P - 3 + 0) with (P + -3) in RK by lia;
      change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK end.
Ltac sok off len addr := lazymatch goal with W : wr_at rsegs ?mc (?P - 3) _ |- _ =>
    let H := fresh "SO" in
    pose proof (wr_at_store_ok rsegs mc _ _ off len W ltac:(lia) ltac:(lia)) as H;
    replace (P - 3 + off) with addr in H by lia; change (wa addr) with (Z_to_bv 64 addr) in H end.
End TwinB.
