(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import Malloc_fp F_malloc_entry.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RF_get_meta RF_malloc_entry RF_realloc_A RF_realloc_AS RF_enframe RF_aligned_B.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import MI_WFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.flia ::= first [ assumption | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.slim; lia | lia ].
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.ZBridge.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Definition rrealloc_ret_post (sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v : word) (F : bvmap 5 word) (fc : bv 32)
    (m' : word -> option byte) (P : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word,
    ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom ctusegs).

(* [comment removed for export] *)
Lemma rrealloc_ss_t1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0v s1v s2v s3v s4v s5v s6v : word) F fc (m : word -> option byte) (P E b3 idx r' : Z),
  rw_cells ctusegs m (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  mem_inv ctusegs m -> bv_unsigned sp + 64 <= 2^64 ->
  wr_at ctusegs m (P - 3) (E - P + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] -> Z.land b3 31 = idx ->
  16 <= P -> P <= E -> E + 1 <= 2^63 -> 0 <= idx < 32 -> 0 <= r' <= 5 -> 0 <= b3 < 256 ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 64 <= P - 3) ->
  evt ctusegs (rrealloc_ret_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc
               (write_to_mem m (wa (P - 3)) [b8 (Z.land b3 31 + Z.shiftl r' 5)]) P)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 r') a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b5360) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until r'. intros FR MI SPB W BK B31 P16 PE E63 IDX R5 B3 DJF.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (* [comment removed for export] *)
  pose proof (bytes_at_read ctusegs m (P - 3) [b8 b3] 0 1 BK ltac:(lia) ltac:(cbn; lia)) as RK.
  cbv [take drop Z.to_nat] in RK. replace (P - 3 + 0) with (P + -3) in RK by lia. change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in RK.
  step. clear RK. rewrite ?zxb_b8 by lia.
  (* [comment removed for export] *)
  step. rewrite ?(wz_unsigned b3), ?B31 by lia.
  step. rewrite (unsigned_lit r'), Z.shiftl_mul_pow2 by lia.
  step. rewrite (unsigned_lit (r' * 2 ^ 5)), (unsigned_lit idx) by lia. rewrite (lor_shl5 r' idx) by lia.
  (* [comment removed for export] *)
  pose proof (wr_at_store_ok ctusegs m (P - 3) (E - P + 3) 0 1 W ltac:(lia) ltac:(lia)) as SO1.
  replace (P - 3 + 0) with (P + -3) in SO1 by lia. change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in SO1.
  assert (K31 : Z.land idx 31 = idx) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  step. rewrite (le1_wz (Z.land idx 31 + Z.shiftl r' 5)) by (rewrite K31, Z.shiftl_mul_pow2 by lia; lia). sdk.
  (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step. step.
  repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E in *; clear E end.
  try replace (idx + r' * 2 ^ 5) with (Z.land b3 31 + Z.shiftl r' 5) in * by (rewrite B31, Z.shiftl_mul_pow2 by lia; lia).
  try replace (Z.land idx 31 + Z.shiftl r' 5) with (Z.land b3 31 + Z.shiftl r' 5) in * by (rewrite K31, B31; reflexivity).
  replace (wa (P + -3)) with (wa (P - 3)) in * by (f_equal; lia).
  apply evt_done. unfold rrealloc_ret_post. do 14 eexists.
  repeat f_equal; try reflexivity; try (apply bv_eq; rewrite ?unsigned_lit by lia; lia).
Qed.

(* [comment removed for export] *)
Lemma rrealloc_ss_t2 : forall (ra sp gp tp t1 t2 s0 s1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0v s1v s2v s3v s4v s5v s6v : word) F fc (m : word -> option byte) (P E b3 idx n : Z),
  rw_cells ctusegs m (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  mem_inv ctusegs m -> bv_unsigned sp + 64 <= 2^64 ->
  wr_at ctusegs m (P - 3) (E - P + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] -> Z.land b3 31 = idx ->
  16 <= P -> P + n <= E -> E + 1 <= 2^63 -> 0 <= n -> 0 <= idx < 32 -> 0 <= b3 < 256 ->
  E - P - n < 2^31 ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 64 <= P - 3) ->
  evt ctusegs (rrealloc_ret_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc (rss_mem m P E n b3) P)
      (MS (mkR ra sp gp tp (Z_to_bv 64 E) t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 a3 a4 a5 (Z_to_bv 64 (E + 4)) a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b5324) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until n. intros FR MI SPB W BK B31 P16 PNE E63 N0 IDX B3 R31 DJF.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (r := E - P - n).
  assert (POSTEQ : forall mk ms, rrealloc_ret_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc mk P ms ->
            mk = rss_mem m P E n b3 -> rrealloc_ret_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc (rss_mem m P E n b3) P ms).
  { intros mk ms H E0. rewrite <- E0. exact H. }
  (* [comment removed for export] *)
  step. step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
  replace (E - (n + P)) with r by lia.
  (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  - (* [comment removed for export] *)
    step. step.
    eapply evt_mono.
    { eapply (rrealloc_ss_t1) with (ra0:=ra0) (s0v:=s0v) (s1v:=s1v) (s2v:=s2v) (s3v:=s3v) (s4v:=s4v) (s5v:=s5v) (s6v:=s6v)
                                   (P:=P) (E:=E) (b3:=b3) (idx:=idx) (r':=0); try eassumption; try lia. }
    intros ms PO. eapply POSTEQ; [exact PO|].
    unfold rss_mem. fold r. rewrite KR. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta.
    repeat (f_equal; try (unfold wa; f_equal; lia)).
  - (* [comment removed for export] *)
    step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (E - r - P + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    + (* [comment removed for export] *)
      step.
      eapply evt_mono.
      { eapply (rrealloc_ss_t1) with (ra0:=ra0) (s0v:=s0v) (s1v:=s1v) (s2v:=s2v) (s3v:=s3v) (s4v:=s4v) (s5v:=s5v) (s6v:=s6v)
                                     (P:=P) (E:=E) (b3:=b3) (idx:=idx) (r':=r); try eassumption; try lia. }
      intros ms PO. eapply POSTEQ; [exact PO|].
      unfold rss_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      repeat match goal with E0 : ?mx = write_to_mem _ _ _ |- _ => rewrite E0 end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
    + (* [comment removed for export] *)
      sok (E - P - 2) 1%nat (E + 4 + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - P - 1) 4%nat (E + 4 + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      eapply evt_mono.
      { eapply (rrealloc_ss_t1) with (ra0:=ra0) (s0v:=s0v) (s1v:=s1v) (s2v:=s2v) (s3v:=s3v) (s4v:=s4v) (s5v:=s5v) (s6v:=s6v)
                                     (P:=P) (E:=E) (b3:=b3) (idx:=idx) (r':=5); try eassumption; try lia. }
      intros ms PO. eapply POSTEQ; [exact PO|].
      unfold rss_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      repeat match goal with E0 : ?mx = write_to_mem _ _ _ |- _ => rewrite E0 end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.
(* [comment removed for export] *)
Lemma rrealloc_t3i : forall ra sp gp tp t1 t2 s0 s1 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (ra0 s0v s1v s2v s3v s4v s5v s6v : word) (P E b3 idx n sc : Z),
  rw_cells ctusegs m (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  bv_unsigned sp + 64 <= 2^64 ->
  wr_at ctusegs m (P - 3) (E - P + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] -> Z.land b3 31 = idx ->
  16 <= P -> P + n <= E -> E + 1 <= 2^63 -> 0 <= idx < 32 -> 0 <= b3 < 256 ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 64 <= P - 3) ->
  0 <= n < 2^32 -> n < 131052 -> 0 <= sc < 48 -> sc <= size_to_class n + 1 -> E - P < 2^31 ->
  mem_inv ctusegs m ->
  evt ctusegs (rrealloc_ret_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc (rss_mem m P E n b3) P)
      (MS (mkR ra sp gp tp (Z_to_bv 64 E) t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) a2 (wz sc) a4 (Z_to_bv 64 467628) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b5140) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until sc. intros FR SPB W BK B31 P16 PNE E63 IDX B3 DJF NR NMM SC SCI EP31 MI.
  assert (HN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (R31 : E - P - n < 2^31) by lia.
  (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1; rewrite ?unsigned_lit, ?HN in K1 by lia. { exfalso. lia. }
  pose proof (size_to_class_props n ltac:(unfold MMAP_THRESHOLD; lia)) as (SCR & SFIT & LG).
  step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit, ?HN in K2 by lia. lia. }
  clear K2.
  (* [comment removed for export] *)
  step. rewrite ?HN. step. step. rewrite ?(unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
  assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
  (* [comment removed for export] *)
  assert (JOIN : forall (t1' a4' a5' a7' : word) (c : Z), c = size_to_class n ->
    evt ctusegs (rrealloc_ret_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc (rss_mem m P E n b3) P)
      (MS (mkR ra sp gp tp (Z_to_bv 64 E) t1' (Z_to_bv 64 131072) s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) (Z_to_bv 64 c) (wz sc) a4' a5' (Z_to_bv 64 (E + 4)) a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               (Z_to_bv 64 131051) t4 t5 t6) F (Z_to_bv 64 0x2b52dc) fc None m (seg_rom ctusegs))).
  { intros t1' a4' a5' a7' c ->.
    step. rewrite ?(unsigned_lit (size_to_class n)), (swrap32_small (size_to_class n + 1)) by lia.
    step. if_cases K3; zify_cond K3; rewrite ?signed_wz_small, ?wz_unsigned in K3 by lia.
    2:{ exfalso. unfold wz in K3. rewrite ?signed_wz_small in K3 by lia. lia. }
    eapply rrealloc_ss_t2; try eassumption; try lia. }
  step. if_cases KS; zify_cond KS; rewrite ?HN, ?(unsigned_lit 157) in KS by lia.
  - (* [comment removed for export] *)
    apply JOIN. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
  - (* [comment removed for export] *)
    assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (rclz_pow_eq x XR) as [PW RV4].
    (* [comment removed for export] *)
    step.
    step. rewrite ?(unsigned_lit x), ?srliw_small by lia.
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite ?(unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
    step. rewrite ?(unsigned_lit x), ?srliw_small by lia.
    step. rewrite ?(unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit v2), ?srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite ?(unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite ?(unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite ?(unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.
    (* [comment removed for export] *)
    step. step. rewrite ?(unsigned_lit w4) by lia.
    step. rewrite ?(unsigned_lit (w4 + 1)) by lia. rewrite ?(unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    assert (K13 : 3 <= k <= 12) by (apply LG; lia).
    (* [comment removed for export] *)
    step. step. step.
    step. rewrite ?(unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    lazymatch goal with HI : mem_inv ctusegs ?mc |- _ => pose proof (rdebruijn_read mc k HI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR end.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. rewrite ?(wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. rewrite ?(unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    step. step. rewrite ?(unsigned_lit (120 - i)) by lia. try replace (121 - (120 - i)) with (i + 1) by lia. try replace (121 + - (120 - i)) with (i + 1) by lia.
    step. rewrite ?(unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. replace (467628 + (i + 1) * 2) with (467628 + 2 * (i + 1)) by lia.
    lazymatch goal with HI : mem_inv ctusegs ?mc |- _ => pose proof (rsize_classes_read mc (i + 1) HI ltac:(lia)) as RS1; unfold RSIZE_CLASSES in RS1 end.
    step. rewrite ?zx16_wz by lia. clear RS1.
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      evt ctusegs (rrealloc_ret_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc (rss_mem m P E n b3) P)
        (MS (mkR ra sp gp tp (Z_to_bv 64 E) (Z_to_bv 64 308304) (Z_to_bv 64 131072) s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 n) (Z_to_bv 64 q) (wz sc) (Z_to_bv 64 (120 - i)) (Z_to_bv 64 467628) (Z_to_bv 64 (E + 4))
                 (Z_to_bv 64 c) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 131051) t4 t5 t6)
            F (Z_to_bv 64 0x2b52c0) fc None m (seg_rom ctusegs))).
    { intros i1 c Hi1 Hc.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite ?(unsigned_lit c), (unsigned_lit (120 - i)) by lia. try replace (c - (120 - i)) with i1 by lia. try replace (c + - (120 - i)) with i1 by lia.
      step. rewrite ?(unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (467628 + i1 * 2) with (467628 + 2 * i1) by lia.
      pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      (* [comment removed for export] *)
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite ?(unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite ?(unsigned_lit 0), Z.lor_0_r by lia.
        apply JOIN. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * rewrite ?(unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite ?(unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        apply JOIN. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    (* [comment removed for export] *)
    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
    + (* [comment removed for export] *)
      step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + (* [comment removed for export] *)
      step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.


(* [comment removed for export] *)
Lemma rrealloc_t2b_I : forall ra sp gp tp t1 s0 s1 a0 a1 a2 a4 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (ra0 s0v s1v s2v s3v s4v s5v s6v : word) (P E rsv n sc b3 : Z),
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> 0 <= P -> P <= E -> E + 1 <= 2^63 -> 0 <= rsv <= E - P -> rsv < 2^32 ->
  bytes_at ctusegs m (E - rsv) [b8 0] -> bytes_at ctusegs m E [b8 0] -> 0 <= b3 < 256 ->
  rw_cells ctusegs m (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] -> bv_unsigned sp + 64 <= 2^64 ->
  wr_at ctusegs m (P - 3) (E - P + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] -> Z.land b3 31 = Z.land b3 31 -> 16 <= P ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 64 <= P - 3) -> n < 131052 -> E - P < 2^31 ->
  0 <= n < 2^32 -> 0 <= sc < 48 -> sc <= size_to_class n + 1 -> n <= E - P -> mem_inv ctusegs m ->
  evt ctusegs (rrealloc_ret_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc (rss_mem m P E n b3) P)
      (MS (mkR ra sp gp tp (Z_to_bv 64 E) t1 (wz rsv) s0 s1 a0 a1 a2 (wz sc) a4 (Z_to_bv 64 467628) (Z_to_bv 64 (E + 4)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b5118) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until b3. intros HP HN P0 ELO EHI RSV RSV32 RB0r RE0 B3 FRI SPBI WI BKI B31I P16I DJFI NMMI EP31I NR SC SHR LE MI.
  assert (IDXI : 0 <= Z.land b3 31 < 32). { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  pose proof (bytes_at_read ctusegs m _ _ 0 1 RB0r ltac:(lia) ltac:(cbn; lia)) as RDr. cbn [firstn skipn Z.to_nat] in RDr. rewrite Z.add_0_r in RDr.
  pose proof (bytes_at_read ctusegs m _ _ 0 1 RE0 ltac:(lia) ltac:(cbn; lia)) as RDe. cbn [firstn skipn Z.to_nat] in RDe. rewrite Z.add_0_r in RDe.
  (* [comment removed for export] *)
  st1. st1. if_cases K1; zify_cond K1. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia. lia. }
  (* [comment removed for export] *)
  st1. replace (E + - rsv) with (E - rsv) by lia. change (Z_to_bv 64 (E - rsv)) with (wa (E - rsv)).
  st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. apply K2. reflexivity. }
  (* [comment removed for export] *)
  change (Z_to_bv 64 E) with (wa E).
  st1. st1. if_cases K3; zify_cond K3. 2:{ exfalso. apply K3. reflexivity. }
  rewrite HP. replace (E + - P) with (E - P) by lia.
  replace a0 with (Z_to_bv 64 P) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
  replace a1 with (Z_to_bv 64 n) by (apply bv_eq; rewrite unsigned_lit by lia; lia).
  eapply rrealloc_t3i with (idx := Z.land b3 31); try eassumption; try lia.
Qed.

(* [comment removed for export] *)
Lemma rrealloc_t2_I : forall ra sp gp tp t1 t2 s0 s1 a0 a1 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (ra0 s0v s1v s2v s3v s4v s5v s6v : word) (P B E stride idx b3 r32 n sc : Z),
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> 0 <= P -> 0 <= B -> 16 <= stride -> 0 <= idx < 32 -> 0 <= b3 < 256 ->
  E = B + 16 + stride * idx + stride - 4 -> P <= E -> E + 1 <= 2^63 ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at ctusegs m (E - 4) (le4 (wz r32)) /\ bytes_at ctusegs m (E - 5) [b8 0]) ->
  0 <= rsv <= E - P -> bytes_at ctusegs m (E - rsv) [b8 0] -> bytes_at ctusegs m E [b8 0] ->
  rw_cells ctusegs m (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] -> bv_unsigned sp + 64 <= 2^64 ->
  wr_at ctusegs m (P - 3) (E - P + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] -> Z.land b3 31 = Z.land b3 31 -> 16 <= P ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 64 <= P - 3) -> n < 131052 -> E - P < 2^31 ->
  0 <= n < 2^32 -> 0 <= sc < 48 -> sc <= size_to_class n + 1 -> n <= E - P -> mem_inv ctusegs m ->
  evt ctusegs (rrealloc_ret_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc (rss_mem m P E n b3) P)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) t1 t2 s0 s1 a0 a1 (wz B) (wz sc) a4 (Z_to_bv 64 467628) (Z_to_bv 64 stride) (wz b3) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b50d0) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until sc. intros rsv0 rsv HP HN P0 B0 S16 IDX B3 HE ELO EHI BIG RSV RB0r RE0 FRI SPBI WI BKI B31I P16I DJFI NMMI EP31I NR SC SHR LE MI.
  assert (RSV0 : 0 <= rsv0 < 8).
  { unfold rsv0. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (RSVR : 0 <= rsv < 2^32).
  { unfold rsv. destruct (Z.leb_spec 160 b3); [destruct (BIG ltac:(lia)) as (_ & ? & _); lia| lia]. }
  assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  st1. st1. st1. st1. st1. st1. st1.
  replace (B + stride * idx + 16 + stride + -4) with E by lia. fold rsv0.
  (* [comment removed for export] *)
  st1. if_cases Kb; zify_cond Kb; rewrite ?wz_unsigned in Kb by lia.
  - (* [comment removed for export] *)
    replace (Z_to_bv 64 rsv0) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [lia| reflexivity]).
    replace (Z_to_bv 64 (B + stride * idx + 16 + stride)) with (Z_to_bv 64 (E + 4)) by (f_equal; lia).
    eapply rrealloc_t2b_I with (E:=E) (rsv:=rsv) (n:=n) (sc:=sc) (b3:=b3); try eassumption; try lia.
  - (* [comment removed for export] *)
    destruct (BIG ltac:(lia)) as (R5 & R32 & RB4 & RB5).
    pose proof (bytes_at_read ctusegs m _ _ 0 4 RB4 ltac:(lia) ltac:(rewrite length_le4; cbn; lia)) as RD4.
    cbn [skipn Z.to_nat] in RD4. rewrite firstn_all2 in RD4 by (rewrite length_le4; lia). rewrite Z.add_0_r in RD4.
    replace (E - 4) with (B + stride * idx + 16 + stride + -8) in RD4 by lia.
    pose proof (bytes_at_read ctusegs m _ _ 0 1 RB5 ltac:(lia) ltac:(cbn; lia)) as RD5. cbn [firstn skipn Z.to_nat] in RD5. rewrite Z.add_0_r in RD5.
    replace (E - 5) with (B + stride * idx + 16 + stride + -9) in RD5 by lia.
    (* [comment removed for export] *)
    st1. st1. if_cases K5; zify_cond K5. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K5 by lia. lia. }
    (* [comment removed for export] *)
    st1. rewrite zx32_wz' by lia. st1. st1. if_cases K6; zify_cond K6. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K6 by lia. lia. }
    (* [comment removed for export] *)
    st1. st1. if_cases K7; zify_cond K7. 2:{ exfalso. apply K7. rewrite ?wz_unsigned by lia. reflexivity. }
    replace (wz r32) with (wz rsv) by (unfold rsv; destruct (Z.leb_spec 160 b3); [reflexivity| lia]).
    replace (Z_to_bv 64 (B + stride * idx + 16 + stride)) with (Z_to_bv 64 (E + 4)) by (f_equal; lia).
    eapply rrealloc_t2b_I with (E:=E) (rsv:=rsv) (n:=n) (sc:=sc) (b3:=b3); try eassumption; try lia.
Qed.

(* [comment removed for export] *)
Lemma rrealloc_t1s_I : forall ra sp gp tp t1 s0 s1 a0 a1 a4 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (ra0 s0v s1v s2v s3v s4v s5v s6v : word) (P B E idx b3 r32 n sc : Z),
  let stride := 16 * size_class sc in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  sc < 48 ->
  ov_read_bytes ctusegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc))) ->
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> 0 <= P -> 0 <= B -> 16 <= stride -> 0 <= idx < 32 -> 0 <= b3 < 256 ->
  E = B + 16 + stride * idx + stride - 4 -> P <= E -> E + 1 <= 2^63 ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at ctusegs m (E - 4) (le4 (wz r32)) /\ bytes_at ctusegs m (E - 5) [b8 0]) ->
  0 <= rsv <= E - P -> bytes_at ctusegs m (E - rsv) [b8 0] -> bytes_at ctusegs m E [b8 0] ->
  rw_cells ctusegs m (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] -> bv_unsigned sp + 64 <= 2^64 ->
  wr_at ctusegs m (P - 3) (E - P + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] -> Z.land b3 31 = Z.land b3 31 -> 16 <= P ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 64 <= P - 3) -> n < 131052 -> E - P < 2^31 ->
  0 <= n < 2^32 -> 0 <= sc < 48 -> sc <= size_to_class n + 1 -> n <= E - P -> mem_inv ctusegs m ->
  evt ctusegs (rrealloc_ret_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc (rss_mem m P E n b3) P)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) t1 (Z_to_bv 64 (sc * 2)) s0 s1 a0 a1 (wz B) (wz sc) a4 (Z_to_bv 64 467628) a6 (wz b3) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b50c4) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until sc. intros stride rsv0 rsv SC48 RS HP HN P0 B0 S16 IDX B3 HE ELO EHI BIG RSV RB0r RE0 FRI SPBI WI BKI B31I P16I DJFI NMMI EP31I NR SC SHR LE MI.
  assert (RS' : ov_read_bytes ctusegs m (Z_to_bv 64 (467628 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
  { replace (Z_to_bv 64 (467628 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
  pose proof (size_class_range sc ltac:(lia)) as SZ.
  st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia.
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  replace (Z_to_bv 64 (size_class sc * 16)) with (Z_to_bv 64 stride) by (unfold stride; f_equal; lia).
  apply (rrealloc_t2_I _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P B E stride idx b3 r32 n sc HP HN P0 B0 S16 IDX B3 HE ELO EHI BIG RSV RB0r RE0 FRI SPBI WI BKI B31I P16I DJFI NMMI EP31I NR SC SHR LE MI).
Qed.

(* [comment removed for export] *)
Lemma rrealloc_t1_I : forall ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (ra0 s0v s1v s2v s3v s4v s5v s6v : word) (P B idx b3 r32 n sc off16 last_idx freeable maplen : Z),
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let stride := if (last_idx =? 0) && negb (maplen =? 0) then 4096 * maplen - 16 else 16 * size_class sc in
  let E := B + 16 + stride * idx + stride - 4 in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  (sc < 48 -> ov_read_bytes ctusegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= off16 < 65536 -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= maplen < 2^40 ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> 0 <= P -> 0 <= B -> 16 <= stride -> 0 <= idx < 32 -> 0 <= b3 < 256 ->
  P <= E -> E + 1 <= 2^63 ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at ctusegs m (E - 4) (le4 (wz r32)) /\ bytes_at ctusegs m (E - 5) [b8 0]) ->
  0 <= rsv <= E - P -> bytes_at ctusegs m (E - rsv) [b8 0] -> bytes_at ctusegs m E [b8 0] ->
  rw_cells ctusegs m (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] -> bv_unsigned sp + 64 <= 2^64 ->
  wr_at ctusegs m (P - 3) (E - P + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] -> Z.land b3 31 = Z.land b3 31 -> 16 <= P ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 64 <= P - 3) -> n < 131052 -> E - P < 2^31 ->
  0 <= n < 2^32 -> 0 <= sc < 48 -> sc <= size_to_class n + 1 -> n <= E - P -> mem_inv ctusegs m ->
  evt ctusegs (rrealloc_ret_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc (rss_mem m P E n b3) P)
      (MS (mkR ra sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) s0 s1 a0 a1 (wz B) (wz sc) (wz mword) (Z_to_bv 64 467628) (wz off16) (wz b3) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b50a8) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until maplen. intros mword stride E rsv0 rsv RS O16 LI FB ML Hml SC48 HP HN P0 B0 S16 IDX B3 ELO EHI BIG RSV RB0r RE0 FRI SPBI WI BKI B31I P16I DJFI NMMI EP31I NR SC SHR LE MI.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (MW4 : Z.shiftr mword 12 = maplen).
  { subst mword. rewrite Z.shiftr_div_pow2 by lia. change (2^12) with 4096.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia. lia. }
  st1. rewrite MW4. st1. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    assert (STR : stride = 16 * size_class sc).
    { unfold stride. rewrite (proj2 (Z.eqb_eq _ _) K), andb_false_r. reflexivity. }
    eapply rrealloc_t1s_I with (P:=P) (B:=B) (E:=E) (idx:=idx) (b3:=b3) (r32:=r32) (n:=n) (sc:=sc);
      [exact (SC48 (or_introl K))| exact (RS (SC48 (or_introl K)))| exact HP| exact HN| exact P0| exact B0| rewrite <- STR; exact S16| exact IDX| exact B3
      | unfold E; rewrite STR; reflexivity| exact ELO| exact EHI| exact BIG| exact RSV| exact RB0r| exact RE0
      | exact FRI| exact SPBI| exact WI| exact BKI| exact B31I| exact P16I| exact DJFI| exact NMMI| exact EP31I
      | exact NR| exact SC| exact SHR| exact LE| exact MI].
  - (* [comment removed for export] *)
    st1. st1. st1. if_cases K2; zify_cond K2.
    2:{ exfalso. rewrite Z.shiftl_mul_pow2 in K2 by lia. change (2^8) with 256 in K2. change 18446744073709551615 with (Z.ones 64) in K2.
        rewrite Z.land_ones, wz_unsigned in K2 by lia. rewrite Z.mod_small in K2 by lia. specialize (Hml K). lia. }
    (* [comment removed for export] *)
    st1. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    + (* [comment removed for export] *)
      assert (STR : stride = 4096 * maplen - 16).
      { unfold stride. rewrite (proj2 (Z.eqb_eq _ _) K3). replace (maplen =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). reflexivity. }
      assert (MWP : mword - mword mod 4096 = 4096 * maplen).
      { subst mword. replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with ((last_idx + 32 * freeable + 64 * sc) + maplen * 4096) by lia.
        rewrite Z.mod_add, Z.mod_small by lia. lia. }
      st1. st1. rewrite land_pgmask by lia. rewrite MWP. st1. st1.
      replace (Z_to_bv 64 (4096 * maplen + -16)) with (Z_to_bv 64 stride) by (rewrite STR; f_equal; lia).
      eapply rrealloc_t2_I with (P:=P) (B:=B) (E:=E) (stride:=stride) (idx:=idx) (b3:=b3) (r32:=r32) (n:=n) (sc:=sc);
        [exact HP| exact HN| exact P0| exact B0| exact S16| exact IDX| exact B3| reflexivity| exact ELO| exact EHI| exact BIG| exact RSV| exact RB0r| exact RE0
        | exact FRI| exact SPBI| exact WI| exact BKI| exact B31I| exact P16I| exact DJFI| exact NMMI| exact EP31I
        | exact NR| exact SC| exact SHR| exact LE| exact MI].
    + (* [comment removed for export] *)
      assert (STR : stride = 16 * size_class sc).
      { unfold stride. rewrite (proj2 (Z.eqb_neq _ _) K3). reflexivity. }
      eapply rrealloc_t1s_I with (P:=P) (B:=B) (E:=E) (idx:=idx) (b3:=b3) (r32:=r32) (n:=n) (sc:=sc);
        [exact (SC48 (or_intror K3))| exact (RS (SC48 (or_intror K3)))| exact HP| exact HN| exact P0| exact B0| rewrite <- STR; exact S16| exact IDX| exact B3
        | unfold E; rewrite STR; reflexivity| exact ELO| exact EHI| exact BIG| exact RSV| exact RB0r| exact RE0
      | exact FRI| exact SPBI| exact WI| exact BKI| exact B31I| exact P16I| exact DJFI| exact NMMI| exact EP31I
      | exact NR| exact SC| exact SHR| exact LE| exact MI].
Qed.

Lemma rrealloc_hdr_walk_I : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (ra0 s0v s1v s2v s3v s4v s5v s6v : word) (P G B A n : Z) (b3 off16 avail freed last_idx freeable sc maplen secret r32 : Z) (prev next : word),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  let stride := if (last_idx =? 0) && negb (maplen =? 0) then 4096 * maplen - 16 else 16 * size_class sc in
  let E := B + 16 + stride * idx + stride - 4 in
  let rsv0 := Z.shiftr b3 5 in
  let rsv := if 160 <=? b3 then r32 else rsv0 in
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  ov_read_bytes ctusegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes ctusegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes ctusegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes ctusegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells ctusegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes ctusegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes ctusegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes ctusegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63) ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (* [comment removed for export] *)
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  16 <= stride -> 0 <= B -> P <= E -> E + 1 <= 2^63 ->
  (160 <= b3 -> rsv0 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at ctusegs m (E - 4) (le4 (wz r32)) /\ bytes_at ctusegs m (E - 5) [b8 0]) ->
  0 <= rsv <= E - P -> bytes_at ctusegs m (E - rsv) [b8 0] -> bytes_at ctusegs m E [b8 0] ->
  rw_cells ctusegs m (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] -> bv_unsigned sp + 64 <= 2^64 ->
  wr_at ctusegs m (P - 3) (E - P + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] -> Z.land b3 31 = Z.land b3 31 -> 16 <= P ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 64 <= P - 3) -> n < 131052 -> E - P < 2^31 ->
  (* [comment removed for export] *)
  0 <= n < 2^32 -> n <= E - P -> sc <= size_to_class n + 1 -> sc < 48 -> mem_inv ctusegs m ->
  evt ctusegs (rrealloc_ret_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc (rss_mem m P E n b3) P)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b4fb4) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until next. intros idx mword stride E rsv0 rsv HP HN AL PLO PHI HB HA GLO GHI R4 R3 R2 RG MM RA RC RS B3 O16 AV FR SE LI FB SC ML
    Hidx Hav Hfr Hsc Hsc63 Hml SC48 S16 B0 ELO EHI BIG RSV RB0r RE0 FRI SPBI WI BKI B31I P16I DJFI NMMI EP31I NR LE SHR SC48b MI.
  assert (MWR : 0 <= mword < 2^64) by (subst mword; lia).
  assert (IDX : 0 <= idx < 32). { subst idx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound b3 (2^5)). lia. }
  st1. st1. if_cases K; zify_cond K. 2:{ exfalso. change 15 with (2^4 - 1) in K. rewrite zb_land_mask in K by lia. lia. }
  st1. st1. st1. st1. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  st1. rewrite Z.shiftl_mul_pow2 by lia. change (2^4) with 16.
  st1.
  assert (RG' : ov_read_bytes ctusegs m (Z_to_bv 64 (P - off16 * 16 + -16)) 8 = Some (le8 (wz G))).
  { replace (P - off16 * 16 + -16) with B by lia. exact RG. }
  st1.
  set (gw := wz G) in *. assert (HG : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; lia).
  rewrite <- HG in MM. clearbody gw.
  assert (GW : gw = wz G) by (rewrite <- HG; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  st1. st1. st1. fold idx. st1. if_cases K3; zify_cond K3. 2:{ exfalso. rewrite wz_unsigned in K3 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW1 : Z.land mword 31 = last_idx).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. subst mword. change (2^5) with 32.
    replace (last_idx + 32 * freeable + 64 * sc + 4096 * maplen) with (last_idx + (freeable + 2 * sc + 128 * maplen) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
  st1. st1. rewrite MW1. st1. if_cases K4; zify_cond K4. 2:{ exfalso. lia. }
  (* [comment removed for export] *)
  st1. rewrite sx32_wz_sxv by lia. st1. st1.
  rewrite sllw1_word' by lia.
  assert (P2 : 0 <= 2 ^ idx < 2^32) by (split; [apply Z.pow_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
  pose proof (sxv_range avail) as SXA. pose proof (sxv_range (2 ^ idx)) as SXI.
  assert (LA : Z.land avail (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit avail idx ltac:(lia) ltac:(lia))); exact Hav).
  assert (LF : Z.land freed (2 ^ idx) = 0) by (apply (proj2 (land_pow2_testbit freed idx ltac:(lia) ltac:(lia))); exact Hfr).
  st1. rewrite sxv_land, LA, (sxv_small 0) by lia. st1. if_cases K5; zify_cond K5. 2:{ exfalso. apply K5. reflexivity. }
  (* [comment removed for export] *)
  pose proof (sxv_range freed) as SXF.
  st1. rewrite sx32_wz_sxv by lia. st1. rewrite sxv_land, LF, (sxv_small 0) by lia. st1. if_cases K6; zify_cond K6. 2:{ exfalso. apply K6. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. rewrite land_pgmask by lia. rewrite HG, <- HA. st1. unfold RCTX in RC. st1. st1.
  if_cases K7; zify_cond K7. 2:{ exfalso. rewrite ?wz_unsigned in K7 by lia. lia. }
  (* [comment removed for export] *)
  assert (MW2 : Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl mword 52))) 58 = sc).
  { rewrite unsigned_lit_wrap, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. subst mword.
    replace ((last_idx + 32 * freeable + 64 * sc + 4096 * maplen) * 2 ^ 52)
      with ((last_idx + 32 * freeable + 64 * sc) * 2^52 + maplen * 2^64) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
    replace ((last_idx + 32 * freeable + 64 * sc) * 2 ^ 52) with ((last_idx + 32 * freeable) * 2^52 + sc * 2^58) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia. }
  assert (P0 : 0 <= P) by lia.
  assert (TAIL : forall x1 x28 x29 x8 x9 x18,
    evt ctusegs (rrealloc_ret_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc (rss_mem m P E n b3) P)
      (MS (mkR x1 sp gp tp (Z_to_bv 64 idx) (Z_to_bv 64 last_idx) (Z_to_bv 64 (sc * 2)) x8 x9 a0 a1 (wz B) (wz sc) (wz mword) (Z_to_bv 64 467628) (wz off16) (wz b3) x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6) F (Z_to_bv 64 0x2b50a8) fc None m (seg_rom ctusegs))).
  { intros. eapply rrealloc_t1_I with (P:=P) (B:=B) (idx:=idx) (b3:=b3) (r32:=r32) (n:=n) (sc:=sc) (off16:=off16) (last_idx:=last_idx) (freeable:=freeable) (maplen:=maplen);
      [exact RS| exact O16| exact LI| exact FB| exact ML| exact Hml| exact SC48| exact HP| exact HN| exact P0| exact B0| exact S16| exact IDX| exact B3
      | exact ELO| exact EHI| exact BIG| exact RSV| exact RB0r| exact RE0
      | exact FRI| exact SPBI| exact WI| exact BKI| exact B31I| exact P16I| exact DJFI| exact NMMI| exact EP31I
      | exact NR| lia| exact SHR| exact LE| exact MI]. }
  st1. st1. st1. st1. rewrite MW2. st1. rewrite (Z.shiftl_mul_pow2 sc 1) by lia. change (2^1) with 2. st1. st1. if_cases K8; zify_cond K8.
  - (* [comment removed for export] *)
    specialize (Hsc63 ltac:(rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia)).
    st1. st1. if_cases K9; zify_cond K9. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K9 by lia. lia. }
    rewrite GW. apply TAIL.
  - (* [comment removed for export] *)
    assert (SCLT : sc < 48) by (rewrite ?wz_unsigned, ?unsigned_lit in K8 by lia; lia).
    specialize (RS SCLT). specialize (Hsc SCLT).
    assert (RS' : ov_read_bytes ctusegs m (Z_to_bv 64 (467628 + sc * 2)) 2 = Some (le2 (wz (size_class sc)))).
    { replace (Z_to_bv 64 (467628 + sc * 2)) with (wa (RSIZE_CLASSES + 2 * sc)) by (unfold wa, RSIZE_CLASSES; f_equal; lia). exact RS. }
    pose proof (size_class_range sc ltac:(lia)) as SZ.
    st1. st1. try rewrite (Z.mod_small (size_class sc)) by lia.
    st1. st1. if_cases K10; zify_cond K10. 2:{ exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K10 by nia. nia. }
    st1. st1. st1. if_cases K11; zify_cond K11. { exfalso. rewrite ?wz_unsigned, ?unsigned_lit in K11 by nia. nia. }
    st1. rewrite GW. apply TAIL.
Qed.

(* [comment removed for export] *)
Lemma rrealloc_hdr_walk_eq_I : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
   (ra0 s0v s1v s2v s3v s4v s5v s6v : word) (P G B A n : Z) (b3 off16 avail freed last_idx freeable sc maplen secret r32 : Z) (prev next : word) (stride E rsv : Z),
  let idx := Z.land b3 31 in
  let mword := last_idx + 32 * freeable + 64 * sc + 4096 * maplen in
  stride = (if (last_idx =? 0) && negb (maplen =? 0) then 4096 * maplen - 16 else 16 * size_class sc) ->
  E = B + 16 + stride * idx + stride - 4 ->
  rsv = (if 160 <=? b3 then r32 else Z.shiftr b3 5) ->
  bv_unsigned a0 = P -> bv_unsigned a1 = n -> P mod 16 = 0 -> 16 * off16 + 16 <= P -> P + 16 <= 2^64 ->
  B = P - 16 * off16 - 16 -> A = G - G mod 4096 -> 0 <= G -> G + 40 <= 2^64 ->
  ov_read_bytes ctusegs m (wa (P - 4)) 1 = Some [b8 0] ->
  ov_read_bytes ctusegs m (wa (P - 3)) 1 = Some [b8 b3] ->
  ov_read_bytes ctusegs m (wa (P - 2)) 2 = Some (le2 (wz off16)) ->
  ov_read_bytes ctusegs m (wa B) 8 = Some (le8 (wz G)) ->
  rw_cells ctusegs m G [C8 prev; C8 next; C8 (wz B); C4 (wz avail); C4 (wz freed); C8 (wz mword)] ->
  ov_read_bytes ctusegs m (wa A) 8 = Some (le8 (wz secret)) ->
  ov_read_bytes ctusegs m (wa RCTX) 8 = Some (le8 (wz secret)) ->
  (sc < 48 -> ov_read_bytes ctusegs m (wa (RSIZE_CLASSES + 2 * sc)) 2 = Some (le2 (wz (size_class sc)))) ->
  0 <= b3 < 256 -> 0 <= off16 < 65536 -> 0 <= avail < 2^32 -> 0 <= freed < 2^32 -> 0 <= secret < 2^64 ->
  0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  idx <= last_idx -> Z.testbit avail idx = false -> Z.testbit freed idx = false ->
  (sc < 48 -> size_class sc * idx <= off16 < size_class sc * (idx + 1)) ->
  (48 <= sc -> sc = 63) ->
  (maplen <> 0 -> off16 <= maplen * 256 - 1) ->
  (maplen = 0 \/ last_idx <> 0 -> sc < 48) ->
  16 <= stride -> 0 <= B -> P <= E -> E + 1 <= 2^63 ->
  (160 <= b3 -> Z.shiftr b3 5 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at ctusegs m (E - 4) (le4 (wz r32)) /\ bytes_at ctusegs m (E - 5) [b8 0]) ->
  0 <= rsv <= E - P -> bytes_at ctusegs m (E - rsv) [b8 0] -> bytes_at ctusegs m E [b8 0] ->
  rw_cells ctusegs m (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] -> bv_unsigned sp + 64 <= 2^64 ->
  wr_at ctusegs m (P - 3) (E - P + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] -> Z.land b3 31 = Z.land b3 31 -> 16 <= P ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 64 <= P - 3) -> n < 131052 -> E - P < 2^31 ->
  0 <= n < 2^32 -> n <= E - P -> sc <= size_to_class n + 1 -> sc < 48 -> mem_inv ctusegs m ->
  evt ctusegs (rrealloc_ret_post sp gp tp s7 s8 s9 s10 s11 ra0 s0v s1v s2v s3v s4v s5v s6v F fc (rss_mem m P E n b3) P)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x2b4fb4) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until rsv. intros idx mword -> -> ->. intros.
  eapply rrealloc_hdr_walk_I with (P:=P) (G:=G) (B:=B) (A:=A) (n:=n) (b3:=b3) (off16:=off16) (avail:=avail) (freed:=freed)
    (last_idx:=last_idx) (freeable:=freeable) (sc:=sc) (maplen:=maplen) (secret:=secret) (r32:=r32) (prev:=prev) (next:=next); eassumption.
Qed.

End WithCeiling0.
