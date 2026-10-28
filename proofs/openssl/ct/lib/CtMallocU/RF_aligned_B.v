(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Znumtheory.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RF_enframe.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
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
Definition rss_mem (m : word -> option byte) (P E n b3 : Z) : word -> option byte :=
  let r := E - P - n in
  let m3 := if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0] in
  let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m3, r) in
  write_to_mem m4 (wa (P - 3)) [b8 (Z.land b3 31 + Z.shiftl r' 5)].

(* [comment removed for export] *)
Definition raligned_mem (m : word -> option byte) (P S E n idx b3 adj q' : Z) : word -> option byte :=
  if adj =? 0 then rss_mem m P E n b3
  else let P' := P + adj in
       let m1 := write_to_mem m (wa (P' - 4)) [b8 0] in
       let m2 := write_to_mem m1 (wa (P' - 3)) [b8 idx] in
       let m3 := write_to_mem m2 (wa (P' - 2)) (le2 (wz q')) in
       let m4 := rss_mem m3 P' E n idx in
       let m5 := write_to_mem m4 (wa (S - 3)) [b8 224] in
       write_to_mem m5 (wa (S - 2)) (le2 (wz ((P' - S) / 16))).

(* [comment removed for export] *)
Definition raligned_ret_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (P' mp : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word,
    ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + 48)) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 0) (Z_to_bv 64 P') a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None (write_to_mem m (wa mp) (le8 (Z_to_bv 64 P'))) (seg_rom ctusegs).

(* [comment removed for export] *)
Lemma raligned_epilogues : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0v s1v : word) F fc (m : word -> option byte) (P' mp : Z) (junk : list byte),
  rw_cells ctusegs m (bv_unsigned sp) [CB 8 junk; C8 s1v; C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 0x2b4c40); C8 s0v; C8 ra0] ->
  wr_at ctusegs m mp 8 -> 0 <= mp -> mp + 8 <= 2^64 -> bv_unsigned sp + 48 <= mp \/ mp + 8 <= bv_unsigned sp ->
  0 < P' < 2^64 -> mem_inv ctusegs m -> bv_unsigned sp + 48 <= 2^64 ->
  evt ctusegs (raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc m P' mp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P') a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b4ce4) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros FR WMP MP0 MP1 MPD PR MI SPB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (* [comment removed for export] *)
  step. step. step. step. step.
  (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
  (* [comment removed for export] *)
  step. step.
  pose proof (wr_at_store_ok ctusegs m mp 8 0 8 WMP ltac:(lia) ltac:(lia)) as SOK. rewrite Z.add_0_r in SOK.
  step. sdk.
  (* [comment removed for export] *)
  step. step. step. step.
  apply evt_done. unfold raligned_ret_post. do 13 eexists.
  repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
  repeat f_equal; try reflexivity; try (apply bv_eq; rewrite ?unsigned_lit by lia; lia).
Qed.

(* [comment removed for export] *)
Lemma raligned_t1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0v s1v : word) F fc (m : word -> option byte) (P' S E mp idx r' : Z) (junk : list byte),
  rw_cells ctusegs m (bv_unsigned sp) [CB 8 junk; C8 s1v; C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 0x2b4c40); C8 s0v; C8 ra0] ->
  wr_at ctusegs m mp 8 -> 0 <= mp -> mp + 8 <= 2^64 -> bv_unsigned sp + 48 <= mp \/ mp + 8 <= bv_unsigned sp ->
  mem_inv ctusegs m -> bv_unsigned sp + 48 <= 2^64 ->
  wr_at ctusegs m (S - 3) (E - S + 3) -> bytes_at ctusegs m (P' - 3) [b8 idx] ->
  16 <= S -> S + 16 <= P' -> P' <= E -> E + 1 <= 2^63 -> 0 <= idx < 32 -> 0 <= r' <= 5 -> (P' - S) mod 16 = 0 -> P' - S < 2^20 ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 48 <= S - 3) -> (E <= mp \/ mp + 8 <= S - 3) ->
  evt ctusegs (raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc
               (write_to_mem (write_to_mem (write_to_mem m (wa (P' - 3)) [b8 (Z.land idx 31 + Z.shiftl r' 5)]) (wa (S - 3)) [b8 224]) (wa (S - 2)) (le2 (wz ((P' - S) / 16))))
               P' mp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P') (Z_to_bv 64 r') a2 a3 a4 (Z_to_bv 64 S) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b4f00) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros FR WMP MP0 MP1 MPD MI SPB W BK S16 SP PE E63 IDX R5 PM16 PS20 DJF DJM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (K31 : Z.land idx 31 = idx) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  (* [comment removed for export] *)
  pose proof (bytes_at_read ctusegs m (P' - 3) [b8 idx] 0 1 BK ltac:(lia) ltac:(cbn; lia)) as RK.
  cbv [take drop Z.to_nat] in RK. replace (P' - 3 + 0) with (P' + -3) in RK by lia. change (wa (P' + -3)) with (Z_to_bv 64 (P' + -3)) in RK.
  step. clear RK. rewrite ?zxb_b8 by lia.
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit r'), Z.shiftl_mul_pow2 by lia.
  step. rewrite ?(wz_unsigned idx), ?K31 by lia.
  step. rewrite (unsigned_lit (r' * 2 ^ 5)), (unsigned_lit idx) by lia. rewrite (lor_shl5 r' idx) by lia.
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit P'), (unsigned_lit S), (swrap32_small (P' - S)) by lia.
  (* [comment removed for export] *)
  pose proof (wr_at_store_ok ctusegs m (S - 3) (E - S + 3) (P' - S) 1 W ltac:(lia) ltac:(lia)) as SO1.
  replace (S - 3 + (P' - S)) with (P' + -3) in SO1 by lia. change (wa (P' + -3)) with (Z_to_bv 64 (P' + -3)) in SO1.
  step. rewrite (le1_wz (Z.land idx 31 + Z.shiftl r' 5)) by (rewrite K31, Z.shiftl_mul_pow2 by lia; lia). sdk.
  (* [comment removed for export] *)
  step. step. rewrite (unsigned_lit (P' - S)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    lazymatch goal with Wc : wr_at ctusegs mc (S - 3) _ |- _ =>
      pose proof (wr_at_store_ok ctusegs mc (S - 3) (E - S + 3) 0 1 Wc ltac:(lia) ltac:(lia)) as SO2 end end.
  replace (S - 3 + 0) with (S + -3) in SO2 by lia. change (wa (S + -3)) with (Z_to_bv 64 (S + -3)) in SO2.
  step. rewrite le1_neg32. sdk.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    lazymatch goal with Wc : wr_at ctusegs mc (S - 3) _ |- _ =>
      pose proof (wr_at_store_ok ctusegs mc (S - 3) (E - S + 3) 1 2 Wc ltac:(lia) ltac:(lia)) as SO3 end end.
  replace (S - 3 + 1) with (S + -2) in SO3 by lia. change (wa (S + -2)) with (Z_to_bv 64 (S + -2)) in SO3.
  step. change (le2 (Z_to_bv 64 ((P' - S) / 16))) with (le2 (wz ((P' - S) / 16))). sdk.
  (* [comment removed for export] *)
  step.
  repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E in *; clear E end.
  replace (idx + r' * 2 ^ 5) with (Z.land idx 31 + Z.shiftl r' 5) in * by (rewrite K31, Z.shiftl_mul_pow2 by lia; lia).
  replace (wa (P' + -3)) with (wa (P' - 3)) in * by (f_equal; lia).
  replace (wa (S + -3)) with (wa (S - 3)) in * by (f_equal; lia).
  replace (wa (S + -2)) with (wa (S - 2)) in * by (f_equal; lia).
  eapply raligned_epilogues; try eassumption; try lia.
Qed.

(* [comment removed for export] *)
Definition raligned_mem_nz (m : word -> option byte) (P' S E n idx q' : Z) : word -> option byte :=
  let m1 := write_to_mem m (wa (P' - 4)) [b8 0] in
  let m2 := write_to_mem m1 (wa (P' - 3)) [b8 idx] in
  let m3 := write_to_mem m2 (wa (P' - 2)) (le2 (wz q')) in
  let m4 := rss_mem m3 P' E n idx in
  let m5 := write_to_mem m4 (wa (S - 3)) [b8 224] in
  write_to_mem m5 (wa (S - 2)) (le2 (wz ((P' - S) / 16))).

Lemma raligned_ret_post_mem sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc (m m' : word -> option byte) P' mp ms :
  m = m' -> raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc m P' mp ms ->
  raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc m' P' mp ms.
Proof. intros -> H. exact H. Qed.

(* [comment removed for export] *)
Lemma raligned_t2 : forall (ra sp gp tp t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0v s1v : word) F fc (m : word -> option byte) (P' S E mp idx n q' : Z) (junk : list byte),
  rw_cells ctusegs m (bv_unsigned sp) [CB 8 junk; C8 s1v; C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 0x2b4c40); C8 s0v; C8 ra0] ->
  wr_at ctusegs m mp 8 -> 0 <= mp -> mp + 8 <= 2^64 -> bv_unsigned sp + 48 <= mp \/ mp + 8 <= bv_unsigned sp ->
  mem_inv ctusegs m -> bv_unsigned sp + 48 <= 2^64 ->
  wr_at ctusegs m (S - 3) (E - S + 3) ->
  16 <= S -> S + 16 <= P' -> P' + n <= E -> E + 1 <= 2^63 -> 0 <= n -> 0 <= idx < 32 -> (P' - S) mod 16 = 0 -> P' - S < 2^20 ->
  E - P' - n < 2^31 -> 0 <= q' < 65536 ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 48 <= S - 3) -> (E <= mp \/ mp + 8 <= S - 3) ->
  evt ctusegs (raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc (raligned_mem_nz m P' S E n idx q') P' mp)
      (MS (mkR ra sp gp tp (Z_to_bv 64 0) t1 t2 s0 s1 (Z_to_bv 64 P') (Z_to_bv 64 idx) (Z_to_bv 64 (P' + n)) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 E) (Z_to_bv 64 S) a6 (Z_to_bv 64 q')
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b4e8c) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros FR WMP MP0 MP1 MPD MI SPB W S16 SP PNE E63 N0 IDX PM16 PS20 R31 Q16 DJF DJM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (r := E - P' - n).
  assert (POSTEQ : forall mk ms, raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc mk P' mp ms ->
            mk = raligned_mem_nz m P' S E n idx q' ->
            raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc (raligned_mem_nz m P' S E n idx q') P' mp ms).
  { intros mk ms H E0. rewrite <- E0. exact H. }
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit E), (unsigned_lit (P' + n)) by lia. rewrite (swrap32_small (E - (P' + n))) by lia.
  replace (E - (P' + n)) with r by lia.
  (* [comment removed for export] *)
  sok (P' - S - 1) 1%nat (P' + -4).
  step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
  (* [comment removed for export] *)
  sok (P' - S) 1%nat (P' + -3).
  step. change (Z_to_bv 64 idx) with (wz idx) at 1. rewrite (le1_wz idx) by lia. sdk.
  lazymatch goal with E2 : ?mc = write_to_mem ?mq (wa ?a) [b8 idx] |- _ =>
    pose proof (bytes_at_write_same ctusegs mq a [b8 idx] ltac:(lia) ltac:(cbn; lia)) as BK; rewrite <- E2 in BK;
    replace a with (P' - 3) in BK by lia end.
  (* [comment removed for export] *)
  sok (P' - S + 1) 2%nat (P' + -2).
  step. change (le2 (Z_to_bv 64 q')) with (le2 (wz q')). sdk.
  (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  - (* [comment removed for export] *)
    step. step.
    eapply evt_mono.
    { eapply (raligned_t1) with (ra0:=ra0) (s0v:=s0v) (s1v:=s1v) (P':=P') (S:=S) (E:=E) (mp:=mp) (idx:=idx) (r':=0) (junk:=junk); try eassumption; try lia. }
    intros ms PO. eapply POSTEQ; [exact PO|].
    unfold raligned_mem_nz, rss_mem. fold r. rewrite KR. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta.
    repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
    repeat (f_equal; try (unfold wa; f_equal; lia)).
  - (* [comment removed for export] *)
    step. rewrite (unsigned_lit E), (unsigned_lit (P' + n)) by lia. rewrite (swrap32_small (E - (P' + n))) by lia.
    replace (E - (P' + n)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (E - r - S + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    + (* [comment removed for export] *)
      step.
      eapply evt_mono.
      { eapply (raligned_t1) with (ra0:=ra0) (s0v:=s0v) (s1v:=s1v) (P':=P') (S:=S) (E:=E) (mp:=mp) (idx:=idx) (r':=r) (junk:=junk); try eassumption; try lia. }
      intros ms PO. eapply POSTEQ; [exact PO|].
      unfold raligned_mem_nz, rss_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
    + (* [comment removed for export] *)
      sok (E - S - 2) 1%nat (E + 4 + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - S - 1) 4%nat (E + 4 + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      eapply evt_mono.
      { eapply (raligned_t1) with (ra0:=ra0) (s0v:=s0v) (s1v:=s1v) (P':=P') (S:=S) (E:=E) (mp:=mp) (idx:=idx) (r':=5) (junk:=junk); try eassumption; try lia. }
      intros ms PO. eapply POSTEQ; [exact PO|].
      unfold raligned_mem_nz, rss_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.

(* [comment removed for export] *)
Lemma raligned_t1z : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0v s1v : word) F fc (m : word -> option byte) (P S E mp b3 idx r' : Z) (junk : list byte),
  rw_cells ctusegs m (bv_unsigned sp) [CB 8 junk; C8 s1v; C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 0x2b4c40); C8 s0v; C8 ra0] ->
  wr_at ctusegs m mp 8 -> 0 <= mp -> mp + 8 <= 2^64 -> bv_unsigned sp + 48 <= mp \/ mp + 8 <= bv_unsigned sp ->
  mem_inv ctusegs m -> bv_unsigned sp + 48 <= 2^64 ->
  wr_at ctusegs m (S - 3) (E - S + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] -> Z.land b3 31 = idx ->
  16 <= S -> S <= P -> P <= E -> E + 1 <= 2^63 -> 0 <= idx < 32 -> 0 <= r' <= 5 -> 0 <= b3 < 256 ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 48 <= S - 3) -> (E <= mp \/ mp + 8 <= S - 3) ->
  evt ctusegs (raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc
               (write_to_mem m (wa (P - 3)) [b8 (Z.land b3 31 + Z.shiftl r' 5)]) P mp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) (Z_to_bv 64 r') a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b4f40) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros FR WMP MP0 MP1 MPD MI SPB W BK B31 S16 SP PE E63 IDX R5 B3 DJF DJM.
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
  pose proof (wr_at_store_ok ctusegs m (S - 3) (E - S + 3) (P - S) 1 W ltac:(lia) ltac:(lia)) as SO1.
  replace (S - 3 + (P - S)) with (P + -3) in SO1 by lia. change (wa (P + -3)) with (Z_to_bv 64 (P + -3)) in SO1.
  assert (K31 : Z.land idx 31 = idx) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  step. rewrite (le1_wz (Z.land idx 31 + Z.shiftl r' 5)) by (rewrite K31, Z.shiftl_mul_pow2 by lia; lia). sdk.
  (* [comment removed for export] *)
  step.
  repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E in *; clear E end.
  try replace (idx + r' * 2 ^ 5) with (Z.land b3 31 + Z.shiftl r' 5) in * by (rewrite B31, Z.shiftl_mul_pow2 by lia; lia).
  try replace (Z.land idx 31 + Z.shiftl r' 5) with (Z.land b3 31 + Z.shiftl r' 5) in * by (rewrite K31, B31; reflexivity).
  replace (wa (P + -3)) with (wa (P - 3)) in * by (f_equal; lia).
  eapply raligned_epilogues; try eassumption; try lia.
Qed.

(* [comment removed for export] *)
Lemma raligned_t2z : forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0v s1v : word) F fc (m : word -> option byte) (P S E mp b3 idx n : Z) (junk : list byte),
  rw_cells ctusegs m (bv_unsigned sp) [CB 8 junk; C8 s1v; C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 0x2b4c40); C8 s0v; C8 ra0] ->
  wr_at ctusegs m mp 8 -> 0 <= mp -> mp + 8 <= 2^64 -> bv_unsigned sp + 48 <= mp \/ mp + 8 <= bv_unsigned sp ->
  mem_inv ctusegs m -> bv_unsigned sp + 48 <= 2^64 ->
  wr_at ctusegs m (S - 3) (E - S + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] -> Z.land b3 31 = idx ->
  16 <= S -> S <= P -> P + n <= E -> E + 1 <= 2^63 -> 0 <= n -> 0 <= idx < 32 -> 0 <= b3 < 256 ->
  E - P - n < 2^31 ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 48 <= S - 3) -> (E <= mp \/ mp + 8 <= S - 3) ->
  evt ctusegs (raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc (rss_mem m P E n b3) P mp)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 (Z_to_bv 64 n) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 E) a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b4ec4) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros FR WMP MP0 MP1 MPD MI SPB W BK B31 S16 SP PNE E63 N0 IDX B3 R31 DJF DJM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (r := E - P - n).
  assert (POSTEQ : forall mk ms, raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc mk P mp ms ->
            mk = rss_mem m P E n b3 -> raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc (rss_mem m P E n b3) P mp ms).
  { intros mk ms H E0. rewrite <- E0. exact H. }
  (* [comment removed for export] *)
  step. step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
  replace (E - (n + P)) with r by lia.
  (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  - (* [comment removed for export] *)
    replace (Z_to_bv 64 r) with (Z_to_bv 64 0) by (rewrite KR; reflexivity).
    eapply evt_mono.
    { eapply (raligned_t1z) with (ra0:=ra0) (s0v:=s0v) (s1v:=s1v) (P:=P) (S:=S) (E:=E) (mp:=mp) (b3:=b3) (idx:=idx) (r':=0) (junk:=junk); try eassumption; try lia. }
    intros ms PO. eapply POSTEQ; [exact PO|].
    unfold rss_mem. fold r. rewrite KR. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota zeta.
    repeat (f_equal; try (unfold wa; f_equal; lia)).
  - (* [comment removed for export] *)
    step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (E - r - S + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    + (* [comment removed for export] *)
      step.
      eapply evt_mono.
      { eapply (raligned_t1z) with (ra0:=ra0) (s0v:=s0v) (s1v:=s1v) (P:=P) (S:=S) (E:=E) (mp:=mp) (b3:=b3) (idx:=idx) (r':=r) (junk:=junk); try eassumption; try lia. }
      intros ms PO. eapply POSTEQ; [exact PO|].
      unfold rss_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
    + (* [comment removed for export] *)
      sok (E - S - 2) 1%nat (E + 4 + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - S - 1) 4%nat (E + 4 + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      eapply evt_mono.
      { eapply (raligned_t1z) with (ra0:=ra0) (s0v:=s0v) (s1v:=s1v) (P:=P) (S:=S) (E:=E) (mp:=mp) (b3:=b3) (idx:=idx) (r':=5) (junk:=junk); try eassumption; try lia. }
      intros ms PO. eapply POSTEQ; [exact PO|].
      unfold rss_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      repeat match goal with E : ?mx = write_to_mem _ _ _ |- _ => rewrite E end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.

(* [comment removed for export] *)
Lemma land_neg_align (P al k : Z) : 0 <= P < 2^64 -> al = 2^k -> 0 <= k <= 64 ->
  Z.land (al - 1) ((- P) mod 2^64) = (- P) mod al.
Proof.
  intros HP -> Hk. rewrite Z.land_comm. replace (2 ^ k - 1) with (Z.ones k) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  rewrite Z.land_ones by lia.
  rewrite <- (Znumtheory.Zmod_div_mod (2^k) (2^64) (- P)); [reflexivity| apply Z.pow_pos_nonneg; lia| lia|].
  exists (2^(64 - k)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma raligned_store_walk : forall (ra sp gp tp t0 t1 s1 a3 a5 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra0 s0v s1v : word) F fc (m : word -> option byte) (P Bb stride idx n al mp b3 : Z) (junk : list byte),
  let S0 := Bb + 16 in let S := S0 + stride * idx in let E := S0 + stride * (idx + 1) - 4 in
  let adj := (- P) mod al in let P' := P + adj in
  rw_cells ctusegs m (bv_unsigned sp) [CB 8 junk; C8 s1v; C8 (Z_to_bv 64 mp); C8 (Z_to_bv 64 0x2b4c40); C8 s0v; C8 ra0] ->
  wr_at ctusegs m mp 8 -> 0 <= mp -> mp + 8 <= 2^64 -> bv_unsigned sp + 48 <= mp \/ mp + 8 <= bv_unsigned sp ->
  mem_inv ctusegs m -> bv_unsigned sp + 48 <= 2^64 ->
  wr_at ctusegs m (S - 3) (E - S + 3) -> bytes_at ctusegs m (P - 3) [b8 b3] -> Z.land b3 31 = idx -> 0 <= b3 < 256 ->
  0 <= Bb -> Bb mod 16 = 0 -> 16 <= stride -> stride mod 16 = 0 -> 0 <= idx < 32 -> E + 5 <= 2^63 ->
  S <= P -> P mod 16 = 0 -> P - S <= 16 * 255 -> 0 <= n -> (al = 32 \/ al = 64) -> P + n + al - 16 <= E ->
  E - P - n + al < 2^31 -> (idx = 0 \/ stride * (idx + 1) < 2^20) ->
  (E <= bv_unsigned sp \/ bv_unsigned sp + 48 <= S - 3) -> (E <= mp \/ mp + 8 <= S - 3) ->
  evt ctusegs (raligned_ret_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra0 s0v s1v F fc
               (raligned_mem m P S E n idx b3 adj ((P' - S0) / 16)) P' mp)
      (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (- P)) (Z_to_bv 64 al) s1 (Z_to_bv 64 P) (Z_to_bv 64 idx) (Z_to_bv 64 n) a3 (Z_to_bv 64 Bb) a5
               (Z_to_bv 64 stride) (Z_to_bv 64 (idx + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b4e40) fc None m (seg_rom ctusegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until junk. intros S0 S E adj P' FR WMP MP0 MP1 MPD MI SPB W BK B31 B3 BB0 BB16 S16 SM16 IDX E63 SP P16 OFF N0 HAL PNE R31 Q20 DJF DJM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SI1 : stride * (idx + 1) = stride * idx + stride) by lia.
  assert (ADJ : 0 <= adj < al /\ adj mod 16 = 0 /\ (P + adj) mod al = 0).
  { subst adj. assert (AL0 : 0 < al) by (clear - HAL; lia). pose proof (Z.mod_pos_bound (- P) al AL0) as MB.
    split; [lia|]. split.
    - destruct HAL as [-> | ->].
      + rewrite <- (Znumtheory.Zmod_div_mod 16 32 (- P)); [| lia| lia| exists 2; reflexivity].
        replace (- P) with ((- (P / 16)) * 16) by (pose proof (Z.div_mod P 16 ltac:(lia)); lia). rewrite Z_mod_mult. reflexivity.
      + rewrite <- (Znumtheory.Zmod_div_mod 16 64 (- P)); [| lia| lia| exists 4; reflexivity].
        replace (- P) with ((- (P / 16)) * 16) by (pose proof (Z.div_mod P 16 ltac:(lia)); lia). rewrite Z_mod_mult. reflexivity.
    - rewrite Zplus_mod_idemp_r. replace (P + - P) with 0 by lia. apply Z.mod_0_l. lia. }
  destruct ADJ as (ADJR & ADJ16 & PAL).
  assert (ADJB : adj <= al - 16).
  { pose proof (Z.div_mod adj 16 ltac:(lia)). pose proof (Z.div_mod al 16 ltac:(lia)). destruct HAL as [-> | ->]; lia. }
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit stride), ?(unsigned_lit (idx + 1)) by lia. try rewrite (Z.mod_small (stride * (idx + 1))) by nia.
  step. step.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (al + -1)) by lia.
  match goal with |- context [Z.land (al + -1) ?x] => replace (Z.land (al + -1) x) with adj end.
  2:{ replace (al + -1) with (al - 1) by lia. subst adj. symmetry.
      match goal with |- Z.land _ ?x = _ => replace x with ((- P) mod 2^64) by (rewrite ?Z_to_bv_unsigned; unfold bv_wrap; cbn [bv_modulus Z.of_N]; first [reflexivity| lia]) end.
      destruct HAL as [-> | ->]; [apply (land_neg_align P 32 5); [lia| reflexivity| lia] | apply (land_neg_align P 64 6); [lia| reflexivity| lia]]. }
  (* [comment removed for export] *)
  step. replace (Bb + 16 + stride * (idx + 1) + -4) with E by (subst E S0; lia).
  step. if_cases KA; zify_cond KA; rewrite ?(unsigned_lit adj) in KA by lia.
  - (* [comment removed for export] *)
    replace (raligned_mem m P S E n idx b3 adj ((P' - S0) / 16)) with (rss_mem m P E n b3) by (unfold raligned_mem; rewrite KA; reflexivity).
    replace P' with P by (subst P'; lia).
    replace (Bb + 16 + stride * (idx + 1)) with (E + 4) by (subst E S0; lia).
    eapply (raligned_t2z) with (S:=S) (b3:=b3) (idx:=idx); try eassumption; try lia.
  - (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit stride), ?(unsigned_lit idx) by lia. try rewrite (Z.mod_small (stride * idx)) by nia.
    step. fold P'.
    step. rewrite ?(unsigned_lit (Bb + 16)) by lia. replace (P' + - (Bb + 16)) with (P' - S0) by (subst S0; lia).
    assert (PS0 : 0 <= P' - S0 < 2^20).
    { clear - SP SI0 SI1 ADJR ADJB HAL OFF PNE N0 Q20. subst P' S S0 E. split; [lia|]. destruct Q20 as [-> | Q]; [rewrite Z.mul_0_r in *; lia| lia]. }
    step. rewrite ?(unsigned_lit (P' - S0)), ?Z.shiftr_div_pow2 by lia. rewrite (Z.div_small (P' - S0) (2^20)) by lia.
    step. rewrite ?(unsigned_lit 0), ?Z.shiftl_0_l by lia.
    step. rewrite ?(unsigned_lit (P' - S0)), ?Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
    step. try (if_cases KT; zify_cond KT; [| exfalso; apply KT; reflexivity]).
    (* [comment removed for export] *)
    step. replace (Bb + 16 + stride * idx) with S by (subst S S0; lia).
    step. replace (n + P') with (P' + n) by lia.
    replace (Bb + 16 + stride * (idx + 1)) with (E + 4) by (subst E S0; lia).
    replace (raligned_mem m P S E n idx b3 adj ((P' - S0) / 16)) with (raligned_mem_nz m P' S E n idx ((P' - S0) / 16))
      by (unfold raligned_mem; replace (adj =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    subst S0.
    (* [comment removed for export] *)
    eapply (raligned_t2) with (S:=S) (idx:=idx); try eassumption;
      first [ solve [clear - BB0 SI0; lia] | solve [clear - SP KA ADJR ADJ16; lia] | solve [clear - PNE ADJB; lia] | solve [clear - E63; lia]
            | solve [clear - P16 BB16 SM16 ADJ16 SI0; lia] | solve [clear - PS0 SI0; lia] | solve [clear - R31 ADJR; lia] | solve [clear - PS0; lia]
            | lia ].
Qed.
End WithCeiling0.
