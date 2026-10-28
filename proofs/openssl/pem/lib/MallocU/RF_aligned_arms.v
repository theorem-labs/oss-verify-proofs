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
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RF_enframe RF_realloc_frame RF_aligned_head.
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

Definition raarm_post (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (mf : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 t3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b2498) fc None m' (seg_rom usegs)
    /\ m' = mf /\ mem_inv usegs m'.

(* [comment removed for export] *)
Lemma raligned_same_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (P E n b3 : Z),
  let k := Z.land b3 31 in
  bv_unsigned a0 = P -> mem_inv usegs m ->
  wr_at usegs m (P - 3) (E - P + 3) -> bytes_at usegs m (P - 3) [b8 b3] -> 0 <= b3 < 256 ->
  E + 5 <= 2^64 -> 16 <= P -> 0 <= n -> P + n <= E -> E - P - n < 2^31 ->
  evt usegs (raarm_post ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 a0 F fc (rr_setsize_mem m P E n k))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 n) (wz (E + 4)) (wz E) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b2678) fc None m (seg_rom usegs)).
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
  assert (FINB : forall (rr : Z) (mc : word -> option byte) (y12 y13 y14 : word),
    0 <= rr <= 5 -> mem_inv usegs mc -> wr_at usegs mc (P - 3) (E - P + 3) -> bytes_at usegs mc (P - 3) [b8 b3] ->
    evt usegs (raarm_post ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 a0 F fc (write_to_mem mc (wa (P - 3)) [b8 (k + 32 * rr)]))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 rr) y12 y13 y14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b26f4) fc None mc (seg_rom usegs))).
  { intros rr mc y12 y13 y14 RR MIc WRc BKc.
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
    step.
    apply evt_done. unfold raarm_post. do 13 eexists. split; [reflexivity|]. split; [| assumption].
    lazymatch goal with E2 : ?mx = write_to_mem _ _ _ |- _ => rewrite E2 end. first [reflexivity | f_equal; unfold wa; f_equal; lia]. }
  assert (R0 : 0 <= r < 2^31) by (unfold r; lia).
  (* [comment removed for export] *)
  step. if_cases KZ; zify_cond KZ; rewrite ?(unsigned_lit r) in KZ by lia.
  - (* [comment removed for export] *)
    rewrite KZ.
    eapply evt_mono; [apply (FINB 0 m); [lia| exact MI| exact WR| exact BK]|].
    intros ms' (y5 & y6 & y7 & y8 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & m' & -> & Em & MI').
    unfold raarm_post. do 13 eexists. split; [reflexivity|]. split; [| exact MI'].
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
        eapply evt_mono; [apply (FINB r mc); [lia| exact MIc| exact WRc| exact BKc]|] end.
      intros ms' (y5 & y6 & y7 & y8 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & m' & -> & Em & MI').
      unfold raarm_post. do 13 eexists. split; [reflexivity|]. split; [| exact MI'].
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
        eapply evt_mono; [apply (FINB 5 mc); [lia| exact MIc| exact WRc| exact BKc]|] end.
      intros ms' (y5 & y6 & y7 & y8 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & m' & -> & Em & MI').
      unfold raarm_post. do 13 eexists. split; [reflexivity|]. split; [| exact MI'].
      rewrite Em. unfold rr_setsize_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta. rewrite Z.min_r by lia.
      repeat match goal with E3 : ?mx = write_to_mem _ _ _ |- _ => rewrite E3 end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.

(* [comment removed for export] *)
Definition ra_move_mem (m : word -> option byte) (S P' E n idx q' off' : Z) : word -> option byte :=
  let m1 := write_to_mem m (wa (P' - 4)) [b8 0] in
  let m2 := write_to_mem m1 (wa (P' - 3)) [b8 idx] in
  let m3 := write_to_mem m2 (wa (P' - 2)) (le2 (wz q')) in
  let m4 := rr_setsize_mem m3 P' E n idx in
  let m5 := write_to_mem m4 (wa (S - 3)) [b8 224] in
  write_to_mem m5 (wa (S - 2)) (le2 (wz off')).

Lemma raligned_move_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (P B E n idx stride adj : Z),
  let P' := P + adj in
  let S := B + 16 + stride * idx in
  bv_unsigned a0 = P -> mem_inv usegs m ->
  wr_at usegs m (S - 3) (E - S + 3) ->
  E + 5 <= 2^64 -> 0 <= B -> 0 <= idx < 32 -> 0 <= stride < 2^20 -> S + 16 <= P' -> 0 < adj < 64 -> 0 <= n -> P' + n <= E -> E - P' - n < 2^31 -> P' - B - 16 < 2^20 -> 16 <= S ->
  evt usegs (raarm_post ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 (Z_to_bv 64 P') F fc
               (ra_move_mem m S P' E n idx ((P' - B - 16) / 16) ((P' - S) / 16)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz idx) (Z_to_bv 64 n) (wz (E + 4)) (wz E) (wz (B + 16)) (wz stride) (wz adj)
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b2610) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until adj. intros P' S HP MI WR ETOP B0 IDX ST0 SP ADJ N0 PNE EP PB S16.
  set (r := E - P' - n).
  assert (SI0 : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (K31 : Z.land idx 31 = idx) by (change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  change (wz (E + 4)) with (Z_to_bv 64 (E + 4)). change (wz E) with (Z_to_bv 64 E). change (wz (B + 16)) with (Z_to_bv 64 (B + 16)).
  change (wz stride) with (Z_to_bv 64 stride). change (wz adj) with (Z_to_bv 64 adj). change (wz idx) with (Z_to_bv 64 idx).
  (* [comment removed for export] *)
  assert (XR : 0 <= P' - B - 16 < 2^20) by (unfold S in SP; lia).
  assert (X20 : Z.shiftr (P' - B - 16) 20 = 0) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia).
  step. rewrite ?(unsigned_lit stride), ?(unsigned_lit idx) by lia.
  step. rewrite ?HP, ?(unsigned_lit adj) by lia. fold P'.
  step. rewrite ?(unsigned_lit P'), ?(unsigned_lit (B + 16)) by lia. replace (P' + - (B + 16)) with (P' - B - 16) by lia.
  step. rewrite ?(unsigned_lit (P' - B - 16)) by lia. rewrite X20.
  step. rewrite ?(unsigned_lit 0) by lia. change (Z.shiftl 0 48) with 0.
  step. rewrite ?(unsigned_lit (P' - B - 16)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (B + 16)), ?(unsigned_lit (stride * idx)) by lia. replace (B + 16 + stride * idx) with S by reflexivity.
  step. rewrite ?(unsigned_lit n), ?(unsigned_lit P') by lia.
  step. rewrite ?(unsigned_lit E), ?(unsigned_lit (n + P')) by lia. rewrite (swrap32_small (E - (n + P'))) by lia.
  replace (E - (n + P')) with r by (unfold r; lia).
  assert (R0 : 0 <= r < 2^31) by (unfold r; lia).
  (* [comment removed for export] *)
  sok (P' - S - 1) 1%nat (P' + -4).
  step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
  sok (P' - S) 1%nat (P' + -3).
  step. change (le1 (Z_to_bv 64 idx)) with (le1 (wz idx)). rewrite (le1_wz idx) by lia. sdk.
  lazymatch goal with E2 : ?mc = write_to_mem ?mp (wa ?a) [b8 idx] |- _ =>
    pose proof (bytes_at_write_same usegs mp a [b8 idx] ltac:(lia) ltac:(cbn; lia)) as BK; rewrite <- E2 in BK;
    replace a with (P' - 3) in BK by lia end.
  sok (P' - S + 1) 2%nat (P' + -2).
  step. change (le2 (Z_to_bv 64 ((P' - B - 16) / 16))) with (le2 (wz ((P' - B - 16) / 16))). sdk.
  (* [comment removed for export] *)
  assert (FINM : forall (rr : Z) (mc : word -> option byte) (y5 y12 y14 y16 y17 : word),
    0 <= rr <= 5 -> mem_inv usegs mc -> wr_at usegs mc (S - 3) (E - S + 3) -> bytes_at usegs mc (P' - 3) [b8 idx] ->
    evt usegs (raarm_post ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 (Z_to_bv 64 P') F fc
                 (write_to_mem (write_to_mem (write_to_mem mc (wa (P' - 3)) [b8 (idx + 32 * rr)]) (wa (S - 3)) [b8 224]) (wa (S - 2)) (le2 (wz ((P' - S) / 16)))))
      (MS (mkR ra sp gp tp y5 t1 t2 s0 s1 (Z_to_bv 64 P') (Z_to_bv 64 rr) y12 (Z_to_bv 64 (E + 4)) y14 (Z_to_bv 64 S) y16 y17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b26b4) fc None mc (seg_rom usegs))).
  { intros rr mc y5 y12 y14 y16 y17 RR MIc WRc BKc.
    (* [comment removed for export] *)
    read_k. step. clear RK. rewrite ?zxb_b8 by lia.
    step. rewrite ?(unsigned_lit rr), Z.shiftl_mul_pow2 by lia.
    step. rewrite ?(wz_unsigned idx), ?(unsigned_lit idx), ?K31 by lia.
    step. rewrite ?(unsigned_lit (rr * 2 ^ 5)), ?(unsigned_lit idx) by lia. rewrite (lor_shl5 rr idx) by lia. rewrite K31.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 5) with 32. replace (idx + rr * 32) with (idx + 32 * rr) by lia.
    step. rewrite ?(unsigned_lit P'), ?(unsigned_lit S) by lia. rewrite (swrap32_small (P' - S)) by lia.
    sok (P' - S) 1%nat (P' + -3).
    step. change (le1 (Z_to_bv 64 (idx + 32 * rr))) with (le1 (wz (idx + 32 * rr))). rewrite (le1_wz (idx + 32 * rr)) by lia. sdk.
    (* [comment removed for export] *)
    step. step. rewrite ?(unsigned_lit (P' - S)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
    sok 0 1%nat (S + -3).
    step. rewrite le1_neg32. sdk.
    sok 1 2%nat (S + -2).
    step. change (le2 (Z_to_bv 64 ((P' - S) / 16))) with (le2 (wz ((P' - S) / 16))). sdk.
    step.
    apply evt_done. unfold raarm_post. do 13 eexists. split; [reflexivity|]. split; [| assumption].
    repeat match goal with E3 : ?mx = write_to_mem _ _ _ |- _ => rewrite E3 end.
    repeat (f_equal; try (unfold wa; f_equal; lia)). }
  (* [comment removed for export] *)
  step. if_cases KZ; zify_cond KZ; rewrite ?(unsigned_lit r) in KZ by lia.
  - (* [comment removed for export] *)
    step. step.
    lazymatch goal with MIc : mem_inv usegs ?mc, WRc : wr_at usegs ?mc (S - 3) _, BKc : bytes_at usegs ?mc (P' - 3) _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_mono; [apply (FINM 0 mc); [lia| exact MIc| exact WRc| exact BKc]|] end.
    intros ms' (y5 & y6 & y7 & y8 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & m' & -> & Em & MI').
    unfold raarm_post. do 13 eexists. split; [reflexivity|]. split; [| exact MI'].
    rewrite Em. unfold ra_move_mem, rr_setsize_mem. cbv zeta. fold r. rewrite KZ. change (0 =? 0) with true. change (5 <=? 0) with false. cbv beta iota.
    rewrite Z.min_l by lia.
    repeat match goal with E3 : ?mx = write_to_mem _ _ _ |- _ => rewrite E3 end.
    repeat (f_equal; try (unfold wa; f_equal; lia)).
  - (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit E), ?(unsigned_lit (n + P')) by lia. rewrite (swrap32_small (E - (n + P'))) by lia.
    replace (E - (n + P')) with r by (unfold r; lia).
    step. rewrite ?(unsigned_lit r) by lia. rewrite (swrap32_small (0 - r)) by lia.
    step. rewrite ?(unsigned_lit E) by lia. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (E - r - S + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    + (* [comment removed for export] *)
      step.
      lazymatch goal with MIc : mem_inv usegs ?mc, WRc : wr_at usegs ?mc (S - 3) _, BKc : bytes_at usegs ?mc (P' - 3) _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply evt_mono; [apply (FINM r mc); [lia| exact MIc| exact WRc| exact BKc]|] end.
      intros ms' (y5 & y6 & y7 & y8 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & m' & -> & Em & MI').
      unfold raarm_post. do 13 eexists. split; [reflexivity|]. split; [| exact MI'].
      rewrite Em. unfold ra_move_mem, rr_setsize_mem. cbv zeta. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota. rewrite Z.min_l by lia.
      repeat match goal with E3 : ?mx = write_to_mem _ _ _ |- _ => rewrite E3 end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
    + (* [comment removed for export] *)
      sok (E - S - 2) 1%nat (E + 4 + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - S - 1) 4%nat (E + 4 + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      lazymatch goal with MIc : mem_inv usegs ?mc, WRc : wr_at usegs ?mc (S - 3) _, BKc : bytes_at usegs ?mc (P' - 3) _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply evt_mono; [apply (FINM 5 mc); [lia| exact MIc| exact WRc| exact BKc]|] end.
      intros ms' (y5 & y6 & y7 & y8 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & m' & -> & Em & MI').
      unfold raarm_post. do 13 eexists. split; [reflexivity|]. split; [| exact MI'].
      rewrite Em. unfold ra_move_mem, rr_setsize_mem. cbv zeta. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota. rewrite Z.min_r by lia.
      repeat match goal with E3 : ?mx = write_to_mem _ _ _ |- _ => rewrite E3 end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.
End WithCeiling0.
