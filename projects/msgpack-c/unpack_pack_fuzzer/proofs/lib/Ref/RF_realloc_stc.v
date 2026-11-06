(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_malloc_free A_F_malloc_fast A_F_malloc_enframe A_MallocTree A_MallocFacts_A A_MallocKit_A.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_Malloc_fp A_F_malloc_entry.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RF_malloc_entry RF_realloc_dec.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section STC.
Variables (ra1 sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (P n old G B stride E : Z) (i sc : Z) (mword : Z) (Q : machine_state -> Prop).
Hypotheses (HN : 0 <= n < 2^48) (HO : 0 <= old) (PE : P + old <= E) (EHI : E + 4 < 2^64) (P0 : 0 < P) (SC : 0 <= sc < 64)
           (MI : mem_inv rsegs m).

Definition gstate (pc : Z) (t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29 : word) : machine_state :=
  MS (mkR ra1 sp gp tp t0v t1v y7 s0v s1v (Z_to_bv 64 P) (Z_to_bv 64 n) a2v a3v a4v a5v a6v a7v
          (Z_to_bv 64 (P + old)) s3v s4v s5v s6v s7 s8 s9 s10 s11 y28 y29 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition istate (t1v y7 a2v a4v a5v a7v y28 y29 : word) : machine_state :=
  MS (mkR ra1 sp gp tp (Z_to_bv 64 E) t1v y7 s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n) a2v (Z_to_bv 64 sc) a4v a5v
          (Z_to_bv 64 (E + 4)) a7v (Z_to_bv 64 (P + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
     F (Z_to_bv 64 0x49dd8) fc None m (seg_rom rsegs).

Lemma stc_750 : forall (t1v y7 a4v a5v a7v y28 y29 : word),
  (forall t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29',
      move_cond P n E sc ->
      evt rsegs Q (gstate 0x49d98 t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29')) ->
  (forall t1v y7 a2v a4v a5v a7v y28, n <= E - P -> n < MMAP_THRESHOLD -> sc <= size_to_class n + 1 ->
      evt rsegs Q (istate t1v y7 a2v a4v a5v a7v y28 y29)) ->
  n < MMAP_THRESHOLD -> n <= E - P ->
  evt rsegs Q (MS (mkR ra1 sp gp tp (Z_to_bv 64 E) t1v y7 s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n) (Z_to_bv 64 (size_to_class n))
                       (Z_to_bv 64 sc) a4v a5v (Z_to_bv 64 (E + 4)) a7v (Z_to_bv 64 (P + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
                  F (Z_to_bv 64 0x49d90) fc None m (seg_rom rsegs)).
Proof.
  intros until y29. intros KMOVE KINPL NT NA.
  pose proof (size_to_class_props n ltac:(unfold MMAP_THRESHOLD in *; lia)) as (SCR & SFIT & LG).
  step. rewrite ?(unsigned_lit (size_to_class n)) by lia.
  rewrite (swrap32_small (size_to_class n + 1)) by lia.
  step. if_cases K; zify_cond K; rewrite ?signed_of_Z in K by lia.
  - apply KINPL; lia.
  - apply KMOVE. unfold move_cond. unfold MMAP_THRESHOLD in *. lia.
Qed.

Lemma stc_5c4 : forall (y7 y28 y29 : word),
  (forall t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29',
      move_cond P n E sc ->
      evt rsegs Q (gstate 0x49d98 t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29')) ->
  (forall t1v y7 a2v a4v a5v a7v y28, n <= E - P -> n < MMAP_THRESHOLD -> sc <= size_to_class n + 1 ->
      evt rsegs Q (istate t1v y7 a2v a4v a5v a7v y28 y29)) ->
  n < MMAP_THRESHOLD -> n <= E - P ->
  evt rsegs Q (dstate ra1 sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m P n old G B stride E i sc mword
                      0x49c04 y7 (Z_to_bv 64 87200) y28 y29).
Proof.
  intros y7 y28 y29 KMOVE KINPL NT NA. unfold dstate.
  pose proof (size_to_class_props n ltac:(unfold MMAP_THRESHOLD in *; lia)) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in NT.

  step. step. step.
  rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
  assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
  step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
  -
    replace q with (size_to_class n).
    2:{ rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity. }
    apply stc_750; assumption || (unfold MMAP_THRESHOLD; lia).
  -
    assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (rclz_pow_eq x XR) as [PW RV4].
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    assert (RX : 0 <= x < 2 ^ 13) by lia.

    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.

    step. rewrite (unsigned_lit x), srliw_small by lia.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.

    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.

    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.

    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.

    step. step. rewrite (unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    assert (K13 : 3 <= k <= 12) by (apply LG; lia).

    step. step. step.
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR.
    step. rewrite ?zxb_b8 by lia. clear DBR.

    step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i0 := 4 * k - 4). assert (IR : 8 <= i0 <= 44) by lia.
    replace (124 - 4 * k) with (120 - i0) by lia.
    assert (STQ : stc_q q = (let i1 := if size_class (i0 + 1) <? x then i0 + 2 else i0 in if size_class i1 <? x then i1 + 1 else i1)).
    { unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i0 = true) by (subst i0; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i0. clear EK.
    pose proof (size_class_range (i0 + 1) ltac:(lia)) as SR1.
    step. step. rewrite (unsigned_lit (120 - i0)) by lia. replace (121 - (120 - i0)) with (i0 + 1) by lia.
    step. rewrite (unsigned_lit (i0 + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. replace (87200 + (i0 + 1) * 2) with (87200 + 2 * (i0 + 1)) by lia.
    pose proof (rsize_classes_read m (i0 + 1) MI ltac:(lia)) as RS1; unfold RSIZE_CLASSES in RS1.
    step. rewrite ?zx16_wz by lia. clear RS1.

    assert (J1 : forall (i1 c : Z) (t1v : word),
      i1 = (if size_class (i0 + 1) <? x then i0 + 2 else i0) -> c = i1 - i0 + 120 ->
      evt rsegs Q (MS (mkR ra1 sp gp tp (Z_to_bv 64 E) t1v y7 s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n) (Z_to_bv 64 q)
                       (Z_to_bv 64 sc) (Z_to_bv 64 (120 - i0)) (Z_to_bv 64 87200) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 c) (Z_to_bv 64 (P + old))
                       s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
            F (Z_to_bv 64 0x49d74) fc None m (seg_rom rsegs))).
    { intros i1 c t1v Hi1 Hc.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i0 + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      step. rewrite (unsigned_lit c), (unsigned_lit (120 - i0)) by lia. replace (c - (120 - i0)) with i1 by lia.
      step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (87200 + i1 * 2) with (87200 + 2 * i1) by lia.
      pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
        replace i1 with (size_to_class n).
        2:{ rewrite STC, STQ. cbv zeta. rewrite <- Hi1. replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
        apply stc_750; assumption || (unfold MMAP_THRESHOLD; lia).
      * rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        replace (i1 + 1) with (size_to_class n).
        2:{ rewrite STC, STQ. cbv zeta. rewrite <- Hi1. replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
        apply stc_750; assumption || (unfold MMAP_THRESHOLD; lia). }

    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i0 + 1))) in K3 by lia.
    + step. eapply J1; [reflexivity|]. replace (size_class (i0 + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + step. step. eapply J1; [reflexivity|]. replace (size_class (i0 + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End STC.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_fast OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_enframe OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocTree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_fp OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_entry.
Import RMallocRep.TwinB RMallocTree.TwinB RF_malloc_entry.TwinB RF_realloc_dec.TwinB.

Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Section STC.
Variables (ra1 sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (P n old G B stride E : Z) (i sc : Z) (mword : Z) (Q : machine_state -> Prop).
Hypotheses (HN : 0 <= n < 2^48) (HO : 0 <= old) (PE : P + old <= E) (EHI : E + 4 < 2^64) (P0 : 0 < P) (SC : 0 <= sc < 64)
           (MI : mem_inv rsegs m).

Definition gstate (pc : Z) (t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29 : word) : machine_state :=
  MS (mkR ra1 sp gp tp t0v t1v y7 s0v s1v (Z_to_bv 64 P) (Z_to_bv 64 n) a2v a3v a4v a5v a6v a7v
          (Z_to_bv 64 (P + old)) s3v s4v s5v s6v s7 s8 s9 s10 s11 y28 y29 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Definition istate (t1v y7 a2v a4v a5v a7v y28 y29 : word) : machine_state :=
  MS (mkR ra1 sp gp tp (Z_to_bv 64 E) t1v y7 s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n) a2v (Z_to_bv 64 sc) a4v a5v
          (Z_to_bv 64 (E + 4)) a7v (Z_to_bv 64 (P + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
     F (Z_to_bv 64 0x4b5dc) fc None m (seg_rom rsegs).

Lemma stc_750 : forall (t1v y7 a4v a5v a7v y28 y29 : word),
  (forall t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29',
      move_cond P n E sc ->
      evt rsegs Q (gstate 0x4b59c t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29')) ->
  (forall t1v y7 a2v a4v a5v a7v y28, n <= E - P -> n < MMAP_THRESHOLD -> sc <= size_to_class n + 1 ->
      evt rsegs Q (istate t1v y7 a2v a4v a5v a7v y28 y29)) ->
  n < MMAP_THRESHOLD -> n <= E - P ->
  evt rsegs Q (MS (mkR ra1 sp gp tp (Z_to_bv 64 E) t1v y7 s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n) (Z_to_bv 64 (size_to_class n))
                       (Z_to_bv 64 sc) a4v a5v (Z_to_bv 64 (E + 4)) a7v (Z_to_bv 64 (P + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
                  F (Z_to_bv 64 0x4b594) fc None m (seg_rom rsegs)).
Proof.
  intros until y29. intros KMOVE KINPL NT NA.
  pose proof (size_to_class_props n ltac:(unfold MMAP_THRESHOLD in *; lia)) as (SCR & SFIT & LG).
  step. rewrite ?(unsigned_lit (size_to_class n)) by lia.
  rewrite (swrap32_small (size_to_class n + 1)) by lia.
  step. if_cases K; zify_cond K; rewrite ?signed_of_Z in K by lia.
  - apply KINPL; lia.
  - apply KMOVE. unfold move_cond. unfold MMAP_THRESHOLD in *. lia.
Qed.

Lemma stc_5c4 : forall (y7 y28 y29 : word),
  (forall t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29',
      move_cond P n E sc ->
      evt rsegs Q (gstate 0x4b59c t0v t1v y7 s0v s1v a2v a3v a4v a5v a6v a7v s3v s4v s5v s6v y28 y29')) ->
  (forall t1v y7 a2v a4v a5v a7v y28, n <= E - P -> n < MMAP_THRESHOLD -> sc <= size_to_class n + 1 ->
      evt rsegs Q (istate t1v y7 a2v a4v a5v a7v y28 y29)) ->
  n < MMAP_THRESHOLD -> n <= E - P ->
  evt rsegs Q (dstate ra1 sp gp tp s0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 F fc m P n old G B stride E i sc mword
                      0x4b408 y7 (Z_to_bv 64 87344) y28 y29).
Proof.
  intros y7 y28 y29 KMOVE KINPL NT NA. unfold dstate.
  pose proof (size_to_class_props n ltac:(unfold MMAP_THRESHOLD in *; lia)) as (SCR & SFIT & LG). unfold MMAP_THRESHOLD in NT.

  step. step. step.
  rewrite (unsigned_lit (n + 3)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  set (q := (n + 3) / 16) in *. assert (QR : 0 <= q < 8191) by (subst q; Z.div_mod_to_equations; lia).
  assert (STC : size_to_class n = stc_q q) by (apply size_to_class_q; lia).
  step. if_cases K2; zify_cond K2; rewrite ?(unsigned_lit n) in K2 by lia.
  -
    replace q with (size_to_class n).
    2:{ rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; subst q; Z.div_mod_to_equations; lia). reflexivity. }
    apply stc_750; assumption || (unfold MMAP_THRESHOLD; lia).
  -
    assert (Q10 : 10 <= q) by (subst q; Z.div_mod_to_equations; lia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (rclz_pow_eq x XR) as [PW RV4].
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    assert (RX : 0 <= x < 2 ^ 13) by lia.

    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.

    step. rewrite (unsigned_lit x), srliw_small by lia.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.

    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.

    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.

    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.

    step. step. rewrite (unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (rclz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    assert (K13 : 3 <= k <= 12) by (apply LG; lia).

    step. step. step.
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR; unfold RDEBRUIJN in DBR.
    step. rewrite ?zxb_b8 by lia. clear DBR.

    step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i0 := 4 * k - 4). assert (IR : 8 <= i0 <= 44) by lia.
    replace (124 - 4 * k) with (120 - i0) by lia.
    assert (STQ : stc_q q = (let i1 := if size_class (i0 + 1) <? x then i0 + 2 else i0 in if size_class i1 <? x then i1 + 1 else i1)).
    { unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i0 = true) by (subst i0; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i0. clear EK.
    pose proof (size_class_range (i0 + 1) ltac:(lia)) as SR1.
    step. step. rewrite (unsigned_lit (120 - i0)) by lia. replace (121 - (120 - i0)) with (i0 + 1) by lia.
    step. rewrite (unsigned_lit (i0 + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. replace (87344 + (i0 + 1) * 2) with (87344 + 2 * (i0 + 1)) by lia.
    pose proof (rsize_classes_read m (i0 + 1) MI ltac:(lia)) as RS1; unfold RSIZE_CLASSES in RS1.
    step. rewrite ?zx16_wz by lia. clear RS1.

    assert (J1 : forall (i1 c : Z) (t1v : word),
      i1 = (if size_class (i0 + 1) <? x then i0 + 2 else i0) -> c = i1 - i0 + 120 ->
      evt rsegs Q (MS (mkR ra1 sp gp tp (Z_to_bv 64 E) t1v y7 s0 (wz G) (Z_to_bv 64 P) (Z_to_bv 64 n) (Z_to_bv 64 q)
                       (Z_to_bv 64 sc) (Z_to_bv 64 (120 - i0)) (Z_to_bv 64 87344) (Z_to_bv 64 (E + 4)) (Z_to_bv 64 c) (Z_to_bv 64 (P + old))
                       s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 t5 t6)
            F (Z_to_bv 64 0x4b578) fc None m (seg_rom rsegs))).
    { intros i1 c t1v Hi1 Hc.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i0 + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      step. rewrite (unsigned_lit c), (unsigned_lit (120 - i0)) by lia. replace (c - (120 - i0)) with i1 by lia.
      step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (87344 + i1 * 2) with (87344 + 2 * i1) by lia.
      pose proof (rsize_classes_read m i1 MI ltac:(lia)) as RS2. unfold RSIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
        replace i1 with (size_to_class n).
        2:{ rewrite STC, STQ. cbv zeta. rewrite <- Hi1. replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
        apply stc_750; assumption || (unfold MMAP_THRESHOLD; lia).
      * rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        replace (i1 + 1) with (size_to_class n).
        2:{ rewrite STC, STQ. cbv zeta. rewrite <- Hi1. replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
        apply stc_750; assumption || (unfold MMAP_THRESHOLD; lia). }

    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i0 + 1))) in K3 by lia.
    + step. eapply J1; [reflexivity|]. replace (size_class (i0 + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + step. step. eapply J1; [reflexivity|]. replace (size_class (i0 + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End STC.

End CEIL.
End TwinB.
