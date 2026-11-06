(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad RawAlloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_fp F_malloc_entry.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UF_malloc_entry UF_enframe UF_realloc_hdr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition rstc_post (ra sp gp tp t0 t2 s0 s1 a0 a1 a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
   (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists t1 a4 a5 a7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (size_to_class n)) a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19e5c) fc None m (seg_rom usegs).

Lemma rrealloc_stc_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (n : Z),
  a1 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD -> mem_inv usegs m ->
  evt usegs (rstc_post ra sp gp tp t0 t2 s0 s1 a0 a1 a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 (Z_to_bv 64 68648) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19cd0) fc None m (seg_rom usegs)).
Proof.
  intros until n. intros HA N MI. subst a1.
  pose proof (size_to_class_props n N) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in N.
  (* [comment removed for export] *)
  step. step. step.
  rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
  assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
  step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
  - (* [comment removed for export] *)
    apply evt_done. unfold rstc_post. do 4 eexists.
    rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity.
  - (* [comment removed for export] *)
    assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (rclz_pow_eq x XR) as [PW RV4].
    (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    assert (K13 : 3 <= k <= 12) by (apply LG; lia).
    (* [comment removed for export] *)
    step. step. step.
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. unfold RDEBRUIJN in DBR.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 - (120 - i)) with (i + 1) by lia.
    step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. replace (68648 + (i + 1) * 2) with (68648 + 2 * (i + 1)) by lia.
    pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold RSIZE_CLASSES in RS1.
    step. rewrite ?zx16_wz by lia. clear RS1.
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      evt usegs (rstc_post ra sp gp tp t0 t2 s0 s1 a0 (Z_to_bv 64 n) a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n)
        (MS (mkR ra sp gp tp t0 (Z_to_bv 64 68616) t2 s0 s1 a0 (Z_to_bv 64 n)
                 (Z_to_bv 64 q) a3 (Z_to_bv 64 (120 - i)) (Z_to_bv 64 68648) a6 (Z_to_bv 64 c)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x19e40) fc None m (seg_rom usegs))).
    { intros i1 c Hi1 Hc.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c - (120 - i)) with i1 by lia.
      step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (68648 + i1 * 2) with (68648 + 2 * i1) by lia.
      pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      (* [comment removed for export] *)
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
        apply evt_done. unfold rstc_post. do 4 eexists. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        apply evt_done. unfold rstc_post. do 4 eexists. rewrite STC, STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
    + (* [comment removed for export] *)
      step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + (* [comment removed for export] *)
      step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rset_size_mem (m : mem) (P E n k : Z) : mem :=
  let r := E - P - n in
  let m3 := if r =? 0 then m else write_to_mem m (wa (E - r)) [b8 0] in
  let '(m4, r') := if 5 <=? r then (write_to_mem (write_to_mem m3 (wa (E - 5)) [b8 0]) (wa (E - 4)) (le4 (wz r)), 5) else (m3, r) in
  write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)].

Definition rss_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (P E n k : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None (rset_size_mem m P E n k) (seg_rom usegs)
    /\ mem_inv usegs (rset_size_mem m P E n k)
    /\ stk usegs (rset_size_mem m P E n k) lo (bv_unsigned sp).

Lemma land31_small k : 0 <= k -> 0 <= Z.land k 31 < 32.
Proof. intros. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound k (2^5)). lia. Qed.

Lemma rrealloc_ss_walk : forall (ra sp gp tp t1 t2 s0 s1 a0 a2 a3 a4 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (rax s0x s1x s2x s3x s4x s5x s6x : word) F fc (m : mem) (P E n k lo : Z),
  bv_unsigned a0 = P -> mem_inv usegs m ->
  rw_cells usegs m (bv_unsigned sp + -64) (rre_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
  stk usegs m lo (bv_unsigned sp + -64) -> lo <= bv_unsigned sp - 64 -> E + 4 <= lo ->
  wr_at usegs m (P - 3) (E - P + 3) -> bytes_at usegs m (P - 3) [b8 k] ->
  16 <= P -> 0 <= n -> P + n <= E -> E - P - n < 2^31 -> E + 5 <= 2^64 -> 0 <= k < 256 ->
  evt usegs (rss_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc lo m P E n k)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) t1 t2 s0x s1x a0 (Z_to_bv 64 n) a2 a3 a4 a5 (Z_to_bv 64 (E + 4)) a7
               s2x s3x s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19ea4) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros HP MI FR ST SLO ELO WR BK P16 N0 PNE EP E5 HK.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (land31_small k ltac:(lia)) as K31.
  set (r := E - P - n).
  unfold rre_frame in FR.
  (* [comment removed for export] *)
  step. rewrite HP.
  step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
  replace (E - (n + P)) with r by lia.
  (* [comment removed for export] *)
  assert (FIN : forall (a2v t0v : word) (m4 : mem) (r' : Z),
    0 <= r' <= 5 ->
    mem_inv usegs m4 ->
    rw_cells usegs m4 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m4 lo (bv_unsigned sp + -64) ->
    wr_at usegs m4 (P - 3) (E - P + 3) -> bytes_at usegs m4 (P - 3) [b8 k] ->
    write_to_mem m4 (wa (P - 3)) [b8 (Z.land k 31 + Z.shiftl r' 5)] = rset_size_mem m P E n k ->
    evt usegs (rss_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 F fc lo m P E n k)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0v t1 t2 s0x s1x a0 (Z_to_bv 64 r') a2v a3 a4 a5 (Z_to_bv 64 (E + 4)) a7
               s2x s3x s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19ee0) fc None m4 (seg_rom usegs))).
  { intros a2v t0v m4 r' R' MI4 FR4 ST4 WR4 BK4 EQ.
    clear FR ST WR BK MI.
    (* [comment removed for export] *)
    read_k. replace (P + -3) with (bv_unsigned a0 + -3) in RK by lia. step. clear RK. rewrite ?zxb_b8 by lia.
    step. rewrite ?(wz_unsigned k) by lia.
    step. rewrite (unsigned_lit r'), Z.shiftl_mul_pow2 by lia.
    step. rewrite (unsigned_lit (r' * 2 ^ 5)), (unsigned_lit (Z.land k 31)) by lia.
    rewrite (lor_shl5 r' (Z.land k 31)) by lia.
    replace (Z.land (Z.land k 31) 31) with (Z.land k 31) by (rewrite <- Z.land_assoc; reflexivity).
    sok 0 1%nat (P + -3). replace (P + -3) with (bv_unsigned a0 + -3) in SO by lia.
    step. change (Z_to_bv 64 (Z.land k 31 + Z.shiftl r' 5)) with (wz (Z.land k 31 + Z.shiftl r' 5)).
    rewrite (le1_wz (Z.land k 31 + Z.shiftl r' 5)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    replace (bv_unsigned a0 + -3) with (P - 3) by lia. sdk.
    (* [comment removed for export] *)
    do 10 step.
    release_frame FR4 ST4 (bv_unsigned sp).
    apply evt_done. unfold rss_post. do 14 eexists.
    lazymatch goal with E1 : ?mx = write_to_mem _ _ _ |- _ => rewrite EQ in E1; subst mx end.
    split; [reflexivity|]. split; [assumption | exact ST4]. }
  (* [comment removed for export] *)
  step. if_cases KR; zify_cond KR; rewrite ?(unsigned_lit r) in KR by lia.
  - (* [comment removed for export] *)
    step. step.
    eapply (FIN _ _ m 0); [lia| exact MI| exact FR| exact ST| exact WR| exact BK|].
    unfold rset_size_mem. fold r. rewrite KR. reflexivity.
  - (* [comment removed for export] *)
    step. rewrite (unsigned_lit E), (unsigned_lit (n + P)) by lia. rewrite (swrap32_small (E - (n + P))) by lia.
    replace (E - (n + P)) with r by lia.
    step. rewrite (unsigned_lit r), (swrap32_small (0 - r)) by lia.
    step. replace (E + (0 - r)) with (E - r + 0) by lia.
    step.
    sok (n + 3) 1%nat (E - r + 0).
    step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_wz_small in K5 by lia.
    + (* [comment removed for export] *)
      step.
      lazymatch goal with E1 : ?mx = write_to_mem _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply (FIN _ _ mx r); [lia| assumption| assumption| assumption| assumption| assumption|] end.
      unfold rset_size_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with false by (symmetry; apply Z.leb_gt; lia). cbv beta iota zeta.
      repeat match goal with E1 : ?mx = write_to_mem _ _ _ |- _ => rewrite E1; clear E1 end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
    + (* [comment removed for export] *)
      sok (E - P - 2) 1%nat (E + 4 + -9).
      step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
      sok (E - P - 1) 4%nat (E + 4 + -8).
      step. change (le4 (Z_to_bv 64 r)) with (le4 (wz r)). sdk.
      step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        eapply (FIN _ _ mx 5); [lia| assumption| assumption| assumption| assumption| assumption|] end.
      unfold rset_size_mem. fold r.
      replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (5 <=? r) with true by (symmetry; apply Z.leb_le; lia). cbv beta iota zeta.
      repeat match goal with E1 : ?mx = write_to_mem _ _ _ |- _ => rewrite E1; clear E1 end.
      repeat (f_equal; try (unfold wa; f_equal; lia)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End RC__1.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMalloc_fp UMallocKit_A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section SETSIZE.
Variables (st2 : mstate) (m : mem) (g b : aptr) (r : region) (k n off b3 : Z).
Let mr := get_meta_rec st2 g.
Let stride := get_stride mr.
Let B := conc st2 b.
Let P0 := B + 16 + stride * k.
Let P := P0 + 16 * off.
Let E := P0 + stride - 4.

Hypothesis MR : rmrep st2 m.
Hypothesis TK : ticks_ok st2.
Hypothesis Hr : (s_regions st2) !! (fst b) = Some r.
Hypothesis Hk : r_kind r = RKGroup.
Hypothesis B0 : 0 <= snd b.
Hypothesis K0 : 0 <= k < 32.
Hypothesis SPAN : snd b + 16 + stride * (k + 1) <= round_up_pg (r_len r).
Hypothesis S16 : 16 <= stride.
Hypothesis NOGRP : forall b' gh, (s_groups st2) !! b' = Some gh -> fst b' = fst b ->
  snd b' + 9 <= snd b + 16 + stride * k - 4 \/ snd b + 16 + stride * k + stride - 4 <= snd b'.
Hypothesis OFF0 : 0 <= off.
Hypothesis N0 : 0 <= n.
Hypothesis FIT : 16 * off + n + 4 <= stride.
Hypothesis S31 : stride - 4 - 16 * off - n < 2^31.
Hypothesis B3 : 0 <= b3.

Lemma rset_size_rep :
  let p := (fst b, snd b + 16 + stride * k + 16 * off) in
  let e := (fst b, snd b + 16 + stride * k + stride - 4) in
  rmrep (set_size p e n b3 st2) (rset_size_mem m P E n b3) /\ ticks_ok (set_size p e n b3 st2).
Proof.
  pose proof (rconc_b st2 b r Hr) as CB. fold B in CB. pose proof (rsk_nonneg st2 g b k n K0 S16) as SK. fold mr stride in SK.
  cbv zeta. unfold set_size, rset_size_mem, aadd. cbn [fst snd].
  set (po := snd b + 16 + stride * k + 16 * off).
  set (rsv := snd b + 16 + stride * k + stride - 4 - po - n).
  assert (Ersv : E - P - n = rsv) by (unfold rsv, po, E, P, P0; lia). rewrite Ersv.
  assert (RSV : 0 <= rsv <= stride - 4 - 16 * off - n) by (unfold rsv, po; lia).
  assert (EE : forall d, E - d = r_base r + (snd b + 16 + stride * k + stride - 4 + - d)) by (intros; unfold E, P0; lia).
  assert (EP3 : P - 3 = r_base r + (po + -3)) by (unfold P, P0, po; lia).
  set (stF := if negb (rsv =? 0) then _ else _).
  set (mF := if rsv =? 0 then _ else _).
  assert (PF : rmrep stF mF /\ ticks_ok stF /\ s_regions stF = s_regions st2 /\ s_groups stF = s_groups st2).
  { subst stF mF. destruct (Z.eqb_spec rsv 0) as [Ez|NE]; cbn [negb].
    - split; [exact MR|]. split; [exact TK|]. split; reflexivity.
    - destruct (rwr8_rep st2 g b r k n Hr Hk B0 K0 SPAN S16 NOGRP st2 m (snd b + 16 + stride * k + stride - 4 + - rsv) 0 MR TK eq_refl eq_refl)
        as [MF TF]; [fold mr stride; unfold rsv, po; lia| lia|].
      rewrite (EE rsv). split; [exact MF|]. split; [exact TF|]. split; reflexivity. }
  clearbody stF mF. destruct PF as (MF & TF & ERf & EGf).
  set (stG := if 5 <=? rsv then _ else _).
  set (mG := if 5 <=? rsv then _ else _).
  assert (PG : rmrep (fst stG) (fst mG) /\ ticks_ok (fst stG) /\ snd stG = snd mG /\ 0 <= snd mG <= 5
                /\ s_regions (fst stG) = s_regions st2 /\ s_groups (fst stG) = s_groups st2).
  { subst stG mG. destruct (Z.leb_spec 5 rsv) as [LE|GT]; cbn [fst snd].
    - (* [comment removed for export] *)
      rewrite (wr32_wr8_comm st2 g b k n K0 (fst b, snd b + 16 + stride * k + stride - 4 + -4) (fst b, snd b + 16 + stride * k + stride - 4 + -5)) by (cbn; lia || reflexivity).
      destruct (rwr8_rep st2 g b r k n Hr Hk B0 K0 SPAN S16 NOGRP _ _ (snd b + 16 + stride * k + stride - 4 + -5) 0 MF TF ERf EGf) as [M1 T1];
        [fold mr stride; lia| lia|].
      destruct (rwr32_rep st2 g b r k n Hr Hk B0 K0 SPAN S16 NOGRP _ _ (snd b + 16 + stride * k + stride - 4 + -4) rsv M1 T1 ERf EGf) as [M2 T2];
        [fold mr stride; lia| fold mr stride; lia| lia|].
      rewrite (EE 4), (EE 5). split; [exact M2|]. split; [exact T2|]. split; [reflexivity|]. split; [lia|]. split; assumption.
    - split; [exact MF|]. split; [exact TF|]. split; [reflexivity|]. split; [lia|]. split; assumption. }
  clearbody stG mG. destruct stG as [stg r1]. destruct mG as [mg r2]. cbn [fst snd] in PG |- *.
  destruct PG as (MG & TG & -> & R2 & ERg & EGg).
  assert (KV : 0 <= Z.land b3 31 + Z.shiftl r2 5 < 256).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2^5) with 32. pose proof (land31_small b3 B3). lia. }
  destruct (rwr8_rep st2 g b r k n Hr Hk B0 K0 SPAN S16 NOGRP _ _ (po + -3) (Z.land b3 31 + Z.shiftl r2 5) MG TG ERg EGg) as [MH TH];
    [fold mr stride; unfold po; lia| exact KV|].
  rewrite EP3. split; [exact MH| exact TH].
Qed.
End SETSIZE.
End RC__2.
