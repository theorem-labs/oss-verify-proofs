(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import Malloc_fp F_malloc_entry.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RF_malloc_entry RF_realloc_head.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

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
Definition rstc_post (ra sp gp tp t0 t2 s0 s1 a0 a1 a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (n : Z) : machine_state -> Prop :=
  fun ms' => exists t1 a4 a5 a7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (size_to_class n)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b2a90) fc None m (seg_rom usegs).

Lemma rrealloc_stc_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (n : Z),
  a1 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD -> mem_inv usegs m ->
  evt usegs (rstc_post ra sp gp tp t0 t2 s0 s1 a0 a1 a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 (Z_to_bv 64 0x720c4) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b2904) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
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
    pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step.
    rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : stc_q q = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 - (120 - i)) with (i + 1) by lia.
    step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. replace (467140 + (i + 1) * 2) with (467140 + 2 * (i + 1)) by lia.
    pose proof (rsize_classes_read m (i + 1) MI ltac:(lia)) as RS1; unfold RSIZE_CLASSES in RS1.
    step. rewrite ?zx16_wz by lia. clear RS1.
    assert (J1 : forall (i1 c : Z),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      evt usegs (rstc_post ra sp gp tp t0 t2 s0 s1 a0 (Z_to_bv 64 n) a3 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n)
        (MS (mkR ra sp gp tp t0 (Z_to_bv 64 307920) t2 s0 s1 a0 (Z_to_bv 64 n) (Z_to_bv 64 q) a3 (Z_to_bv 64 (120 - i)) (Z_to_bv 64 467140) a6 (Z_to_bv 64 c)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2b2a74) fc None m (seg_rom usegs))).
    { intros i1 c Hi1 Hc.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit c), (unsigned_lit (120 - i)) by lia. replace (c - (120 - i)) with i1 by lia.
      step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (467140 + i1 * 2) with (467140 + 2 * i1) by lia.
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
Definition rarm_grow (sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (n ER : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4,
    ms' = MS (mkR (Z_to_bv 64 0x2b2aa8) sp gp tp t0 t1 t2 (Z_to_bv 64 n) a0 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7
                  (wz ER) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b14ec) fc None m (seg_rom usegs).
Definition rarm_inplace (ra sp gp tp s0 s1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (n E ER : Z) : machine_state -> Prop :=
  fun ms' => exists t1 t2 a2 a3 a4 a5 a7 t3 t4,
    ms' = MS (mkR ra sp gp tp (wz E) t1 t2 s0 s1 a0 (Z_to_bv 64 n) a2 a3 a4 a5 (wz (E + 4)) a7
                  (wz ER) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b2ad8) fc None m (seg_rom usegs).

Lemma rrealloc_arms_walk : forall (ra sp gp tp t1 t2 s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (n G B sc mword E P ER : Z),
  a1 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD -> mem_inv usegs m -> 0 <= sc < 64 -> 0 <= E - P < 2^64 ->
  evt usegs (fun ms' => (rarm_grow sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 F fc m n ER ms' /\ (E - P < n \/ size_to_class n + 1 < sc))
                        \/ (rarm_inplace ra sp gp tp s0 (wz G) s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 F fc m n E ER ms' /\ n <= E - P /\ sc <= size_to_class n + 1))
      (MS (mkR ra sp gp tp (wz E) t1 t2 s0 (wz G) a0 a1 (wz B) (wz sc) (wz mword) (Z_to_bv 64 0x720c4) (wz (E + 4)) (wz (E - P))
               (wz ER) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x2b28f4) fc None m (seg_rom usegs)).
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  intros until ER. intros HA N MI SC AV. subst a1.
  pose proof (size_to_class_props n N) as (SCR & _ & _). unfold MMAP_THRESHOLD in N.
  assert (GROW : forall (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 : word),
    evt usegs (fun ms' => rarm_grow sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a0 F fc m n ER ms')
      (MS (mkR ra sp gp tp x5 x6 x7 s0 (wz G) a0 (Z_to_bv 64 n) x12 x13 x14 x15 x16 x17 (wz ER) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
          F (Z_to_bv 64 0x2b2a98) fc None m (seg_rom usegs))).
  { intros. step. step. step. step. apply evt_done. unfold rarm_grow. do 12 eexists. reflexivity. }
  (* [comment removed for export] *)
  step. step. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite ?unsigned_lit in K2 by lia. lia. }
    eapply evt_mono; [apply GROW|]. intros ms' H. left. split; [exact H| left; lia].
  - eapply evt_cut; [eapply (rrealloc_stc_walk ra sp gp tp _ _ _ s0 _ a0 (Z_to_bv 64 n) _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ t5 t6 F fc m n); [reflexivity| unfold MMAP_THRESHOLD; lia| exact MI]|].
    intros ms1 (x6 & x14 & x15 & x17 & ->).
    (* [comment removed for export] *)
    step. step. if_cases K3; zify_cond K3.
    + apply evt_done. right. split; [unfold rarm_inplace; do 9 eexists; reflexivity|]. split; [lia|].
      unfold wz in K3. rewrite (swrap32_small (size_to_class n + 1)), !SFModel.signed_of_Z in K3 by lia. lia.
    + eapply evt_mono; [apply GROW|]. intros ms' H. left. split; [exact H| right]. unfold wz in K3. rewrite (swrap32_small (size_to_class n + 1)), !SFModel.signed_of_Z in K3 by lia. lia.
Qed.
End WithCeiling0.
