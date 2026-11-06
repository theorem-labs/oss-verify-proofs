(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocFBits.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation ZF n := (repeat (Z_to_bv 8 0) (Z.to_nat n)).

Open Scope Z_scope.
(* [comment removed for export] *)
Lemma bl2z_cons : forall (b : byte) bs, bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. (lazymatch goal with |- ?G => let G' := eval cbn [bytes_le_to_Z] in G in change_no_check G' end). pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
  - apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Lemma lock_byte1 : forall (b0 b1 b2 b3 : byte) (v : word),
  bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v ->
  v_andi (v_srlw (v_lw v) (Z_to_bv 64 8)) 255 = Z_to_bv 64 (bv_unsigned b1).
Proof.
  intros b0 b1 b2 b3 v Hv.
  pose proof (u8_range b0) as R0. pose proof (u8_range b1) as R1. pose proof (u8_range b2) as R2. pose proof (u8_range b3) as R3.
  pose proof (u64_range v) as Rv.
  rewrite !bl2z_cons in Hv. cbn [bytes_le_to_Z] in Hv.
  set (k := bv_unsigned b2 + bv_unsigned b3 * 256) in *.
  set (W := bv_unsigned v) in *.
  assert (HW : W = bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * k)) by lia.
  assert (Hk : 0 <= k < 2 ^ 16) by lia.
  (lazymatch goal with |- ?G => let G' := eval unfold v_andi, v_srlw, v_lw in G in change_no_check G' end). apply f_equal.
  (lazymatch goal with |- ?G => let G' := eval unfold bv_swrap, bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 64) with (2 ^ 64).
  rewrite (u_Z2bv 8) by lia. change (8 mod 32) with 8.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  fold W.
  rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64). change (255 mod 2 ^ 64) with 255.
  assert (E1 : ((W + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) mod 2 ^ 64 mod 2 ^ 32 = W).
  { destruct (Z.lt_ge_cases W (2 ^ 31)) as [L|G].
    - rewrite (Z.mod_small (W + 2 ^ 31)) by lia. replace (W + 2 ^ 31 - 2 ^ 31) with W by lia.
      rewrite (Z.mod_small W) by lia. apply Z.mod_small. lia.
    - replace ((W + 2 ^ 31) mod 2 ^ 32) with (W + 2 ^ 31 - 2 ^ 32) by (Z.div_mod_to_equations; lia).
      replace ((W + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) mod 2 ^ 64) with (2 ^ 64 - 2 ^ 32 + W) by (Z.div_mod_to_equations; lia).
      Z.div_mod_to_equations; lia. }
  rewrite E1. replace (W / 256) with (bv_unsigned b1 + 256 * k) by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (bv_unsigned b1 + 256 * k + 2 ^ 31)) by lia. replace (bv_unsigned b1 + 256 * k + 2 ^ 31 - 2 ^ 31) with (bv_unsigned b1 + 256 * k) by lia.
  rewrite (Z.mod_small (bv_unsigned b1 + 256 * k)) by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  Z.div_mod_to_equations. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma lock_byte1_00 : forall (b2 b3 : byte) (v : word),
  bytes_le_to_Z [Z_to_bv 8 0; Z_to_bv 8 0; b2; b3] = bv_unsigned v ->
  v_andi (v_srlw (v_lw v) (Z_to_bv 64 8)) 255 = Z_to_bv 64 0.
Proof.
  intros b2 b3 v Hv.
  pose proof (u8_range b2) as R2. pose proof (u8_range b3) as R3. pose proof (u64_range v) as Rv.
  rewrite !bl2z_cons in Hv. cbn [bytes_le_to_Z] in Hv.
  change (bv_unsigned (Z_to_bv 8 0)) with 0 in Hv.
  set (k := bv_unsigned b2 + bv_unsigned b3 * 256) in *.
  assert (HW : bv_unsigned v = k * 65536) by lia.
  assert (Hk : 0 <= k < 2 ^ 16) by lia.
  (lazymatch goal with |- ?G => let G' := eval unfold v_andi, v_srlw, v_lw in G in change_no_check G' end). apply f_equal.
  (lazymatch goal with |- ?G => let G' := eval unfold bv_swrap, bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 64) with (2 ^ 64).
  rewrite (u_Z2bv 8) by lia. change (8 mod 32) with 8.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  rewrite HW.
  (* [comment removed for export] *)
  rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64). change (255 mod 2 ^ 64) with 255.
  assert (E1 : ((k * 65536 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) mod 2 ^ 64 mod 2 ^ 32 = k * 65536).
  { destruct (Z.lt_ge_cases (k * 65536) (2 ^ 31)) as [L|G].
    - rewrite (Z.mod_small (k * 65536 + 2 ^ 31)) by lia. replace (k * 65536 + 2 ^ 31 - 2 ^ 31) with (k * 65536) by lia.
      rewrite (Z.mod_small (k * 65536)) by lia. apply Z.mod_small. lia.
    - replace ((k * 65536 + 2 ^ 31) mod 2 ^ 32) with (k * 65536 + 2 ^ 31 - 2 ^ 32) by (Z.div_mod_to_equations; lia).
      replace ((k * 65536 + 2 ^ 31 - 2 ^ 32 - 2 ^ 31) mod 2 ^ 64) with (2 ^ 64 - 2 ^ 32 + k * 65536) by (Z.div_mod_to_equations; lia).
      Z.div_mod_to_equations; lia. }
  rewrite E1. replace (k * 65536 / 256) with (k * 256) by (Z.div_mod_to_equations; lia).
  rewrite (Z.mod_small (k * 256 + 2 ^ 31)) by lia. replace (k * 256 + 2 ^ 31 - 2 ^ 31) with (k * 256) by lia.
  rewrite (Z.mod_small (k * 256)) by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  rewrite Z.mod_mul. reflexivity. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma rdn1_top : forall (m : word -> option byte) (a : word) (b : byte) bs,
  bv_unsigned a + Z.of_nat (length (b :: bs)) <= 2 ^ 64 ->
  rdn ASEGS (wbytes m a (b :: bs)) a 1 = Some [b].
Proof.
  intros m a b bs Hnw. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end). rewrite (wbytes_inside (b :: bs) m a a Hnw) by (cbn [length] in Hnw |- *; lia).
  rewrite Z.sub_diag. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn8_in_fill : forall (m : word -> option byte) (a : word) (n k : Z),
  (0 <= k)%Z -> (k + 8 <= n)%Z -> (bv_unsigned a + n < 2 ^ 64)%Z ->
  rdn ASEGS (wbytes m a (ZF n)) (Z_to_bv 64 (bv_unsigned a + k)) 8 = Some (LE8 (Z_to_bv 64 0)).
Proof.
  intros m a n k Hk Hkn Hnw. pose proof (u64_range a) as Ha.
  transitivity (rdn ASEGS (wbytes m (Z_to_bv 64 (bv_unsigned a + k)) (ZF 8)) (Z_to_bv 64 (bv_unsigned a + k)) 8).
  - apply rdn_ext; [unorm; change (Z.of_nat 8) with 8%Z; lia|]. intros x Hx. revert Hx; unorm; change (Z.of_nat 8) with 8%Z; intros Hx.
    rewrite (wbytes_inside (ZF n) m a x) by (rewrite repeat_length; rewrite Z2Nat.id by lia; lia).
    rewrite (wbytes_inside (ZF 8) m (Z_to_bv 64 (bv_unsigned a + k)) x).
    2:{ rewrite repeat_length. unorm. change (Z.of_nat (Z.to_nat 8)) with 8%Z. lia. }
    2:{ rewrite repeat_length. unorm. change (Z.of_nat (Z.to_nat 8)) with 8%Z. lia. }
    rewrite !nth_repeat. reflexivity.
  - change (LE8 (Z_to_bv 64 0)) with (ZF 8). replace 8%nat with (length (ZF 8)) at 3 by reflexivity.
    apply (rdn_wbytes_hit ASEGS (ZF 8)). rewrite repeat_length. unorm. change (Z.of_nat (Z.to_nat 8)) with 8%Z. lia.
Qed.
End AsAllocFBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocFRc2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac AsAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition fr_dr0 (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v a2v a3v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2296)) (LE8 ra0))
    (at_ S (-2304)) (LE8 s0v))
    (at_ S (-2312)) (LE8 s1v))
    (at_ S (-2320)) (LE8 s2v))
    (at_ S (-2328)) (LE8 s3v))
    (at_ S (-2336)) (LE8 s4v))
    (at_ S (-2344)) (LE8 s5v))
    (at_ S (-2352)) (LE8 s6v))
    (at_ S (-2360)) (LE8 s7v))
    (at_ S (-2368)) (LE8 s8v))
    (at_ S (-2376)) (LE8 s9v))
    (at_ S (-2392)) (LE8 a2v))
    (at_ S (-2384)) (LE8 a3v).
#[local] Hint Unfold fr_dr0 : asfr.

(* [comment removed for export] *)
Definition dr_regs (S : word) (r : bvmap 5 word) : Prop :=
    getr r 2 = at_ S (-2400) /\ getr r 8 = at_ S (-2288) /\ getr r 9 = Z_to_bv 64 0x103f18 /\ getr r 21 = Z_to_bv 64 (2 ^ 37)
    /\ getr r 18 = Z_to_bv 64 (0x103f18 + 64) /\ getr r 19 = Z_to_bv 64 (0x103f18 + 688).
Definition dr_keep (r r' : bvmap 5 word) : Prop :=
    getr r' 3 = getr r 3 /\ getr r' 4 = getr r 4 /\ getr r' 26 = getr r 26 /\ getr r' 27 = getr r 27.

Section DRPRE.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v a2v a3v : word) (tsz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2288).
  Hypothesis H11 : getr regs 11 = at_ S (-2288).
  Hypothesis H12 : getr regs 12 = a2v.
  Hypothesis H13 : getr regs 13 = a3v.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v. Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H22 : getr regs 22 = s6v. Hypothesis H23 : getr regs 23 = s7v. Hypothesis H24 : getr regs 24 = s8v.
  Hypothesis H25 : getr regs 25 = s9v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Htsz : (0 <= tsz < 2 ^ 64)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2400)) 112 = true.
  Hypothesis Rtsz : rdn ASEGS mem (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 tsz)).

  #[local] Abbreviation M0 := (fr_dr0 mem S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v a2v a3v).

  Ltac dr_prefix :=
      an F_4dcf4 D_4dcf4;                              (* [comment removed for export] *)
      fsd F_4dcf8 D_4dcf8 (at_ S (-2296));             (* [comment removed for export] *)
      fsd F_4dcfc D_4dcfc (at_ S (-2304));             (* [comment removed for export] *)
      fsd F_4dd00 D_4dd00 (at_ S (-2312));             (* [comment removed for export] *)
      fsd F_4dd04 D_4dd04 (at_ S (-2320));             (* [comment removed for export] *)
      fsd F_4dd08 D_4dd08 (at_ S (-2328));             (* [comment removed for export] *)
      fsd F_4dd0c D_4dd0c (at_ S (-2336));             (* [comment removed for export] *)
      fsd F_4dd10 D_4dd10 (at_ S (-2344));             (* [comment removed for export] *)
      fsd F_4dd14 D_4dd14 (at_ S (-2352));             (* [comment removed for export] *)
      fsd F_4dd18 D_4dd18 (at_ S (-2360));             (* [comment removed for export] *)
      fsd F_4dd1c D_4dd1c (at_ S (-2368));             (* [comment removed for export] *)
      fsd F_4dd20 D_4dd20 (at_ S (-2376));             (* [comment removed for export] *)
      cld8 F_4dd24 D_4dd24 (Z_to_bv 64 tsz) Rtsz;      (* [comment removed for export] *)
      fsd F_4dd28 D_4dd28 (at_ S (-2392));             (* [comment removed for export] *)
      fsd F_4dd2c D_4dd2c (at_ S (-2384)).             (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma dr_pre_loop : (tsz <> 0)%Z ->
    exists r, msteps ASEGS (mkst regs (0x4dcfc : word) mem rom) (mkst r (0x4dd74 : word) M0 rom)
      /\ dr_regs S r /\ dr_keep regs r /\ getr r 10 = Z_to_bv 64 tsz.
  Proof using Rtsz Hstk Htsz HS H25 H24 H23 H22 H21 H20 H19 H18 H9 H8 H13 H12 H11 H2 H1.
    intros Nz. (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - dr_prefix.
      ab_ft F_4dd30 D_4dd30 ltac:(condz).              (* [comment removed for export] *)
      an F_4dd34 D_4dd34.                              (* [comment removed for export] *)
      an F_4dd38 D_4dd38.                              (* [comment removed for export] *)
      an F_4dd3c D_4dd3c.                              (* [comment removed for export] *)
      an F_4dd40 D_4dd40.                              (* [comment removed for export] *)
      av F_4dd44 D_4dd44 (Z_to_bv 64 (2 ^ 37)) ltac:(valz).   (* [comment removed for export] *)
      an F_4dd48 D_4dd48.                              (* [comment removed for export] *)
      an F_4dd4c D_4dd4c.                              (* [comment removed for export] *)
      an F_4dd50 D_4dd50.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with M0. wd_refl.
    - post.
  Qed.

End DRPRE.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_drb (mem : word -> option byte) (S : word) (tsz tby bsz nx : Z) : word -> option byte :=
  let m1 := wbytes mem (at_ S (-2280)) (LE8 (Z_to_bv 64 nx)) in
  let m2 := if (nx =? 0)%Z then wbytes m1 (at_ S (-2272)) (LE8 (Z_to_bv 64 0)) else m1 in
  wbytes (wbytes m2 (at_ S (-2288)) (LE8 (Z_to_bv 64 (tsz - 1)))) (at_ S (-2264)) (LE8 (Z_to_bv 64 (tby - bsz))).

Section DRBHEAD.
  Variables (mem rom : word -> option byte) (S : word) (tsz tby b bsz nx cnt : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : dr_regs S regs.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 tsz.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Htsz : (1 <= tsz < 2 ^ 28)%Z.
  Hypothesis Htby : (0 <= bsz <= tby /\ tby < 2 ^ 42)%Z.
  Hypothesis Hnx : (0 <= nx < 2 ^ 64)%Z.
  Hypothesis Hcnt : (0 <= cnt <= 1021)%Z.
  Hypothesis Hb : (AIMGHI <= b /\ b + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2288)) 32 = true.
  Hypothesis Rfirst : rdn ASEGS mem (at_ S (-2280)) 8 = Some (LE8 (Z_to_bv 64 b)).
  Hypothesis Rtby : rdn ASEGS mem (at_ S (-2264)) 8 = Some (LE8 (Z_to_bv 64 tby)).
  Hypothesis Rnx : rdn ASEGS mem (Z_to_bv 64 b) 8 = Some (LE8 (Z_to_bv 64 nx)).
  Hypothesis Rbsz : rdn ASEGS mem (Z_to_bv 64 (b + 8)) 8 = Some (LE8 (Z_to_bv 64 bsz)).
  Hypothesis Rcnt : rdn ASEGS mem (Z_to_bv 64 (b + 16)) 8 = Some (LE8 (Z_to_bv 64 cnt)).

  #[local] Abbreviation Mb := (fr_drb mem S tsz tby bsz nx).

  Ltac bh1 :=
      cld8 F_4dd6c D_4dd6c (Z_to_bv 64 b) Rfirst;      (* [comment removed for export] *)
      cld8 F_4dd70 D_4dd70 (Z_to_bv 64 nx) Rnx;        (* [comment removed for export] *)
      fsd F_4dd74 D_4dd74 (at_ S (-2280)).             (* [comment removed for export] *)
  Ltac bh2 :=
      av F_4dd80 D_4dd80 (Z_to_bv 64 (tsz - 1)) ltac:(valz);     (* [comment removed for export] *)
      fsd F_4dd84 D_4dd84 (at_ S (-2288));             (* [comment removed for export] *)
      cld8 F_4dd88 D_4dd88 (Z_to_bv 64 bsz) Rbsz;      (* [comment removed for export] *)
      cld8 F_4dd8c D_4dd8c (Z_to_bv 64 tby) Rtby;      (* [comment removed for export] *)
      av F_4dd90 D_4dd90 (Z_to_bv 64 (tby - bsz)) ltac:(valz);   (* [comment removed for export] *)
      fsd F_4dd94 D_4dd94 (at_ S (-2264));             (* [comment removed for export] *)
      cld8 F_4dd98 D_4dd98 (Z_to_bv 64 cnt) Rcnt.      (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma dr_bhead_items : (cnt <> 0)%Z ->
    exists r, msteps ASEGS (mkst regs (0x4dd74 : word) mem rom) (mkst r (0x4ddb4 : word) Mb rom)
      /\ dr_regs S r /\ dr_keep regs r /\ getr r 20 = Z_to_bv 64 b
      /\ getr r 23 = Z_to_bv 64 (b + 152) /\ getr r 24 = Z_to_bv 64 (cnt + 16) /\ getr r 25 = Z_to_bv 64 16.
  Proof using Rcnt Rbsz Rnx Rtby Rfirst Hstk Hb Hcnt Hnx Htby Htsz HS H10 HR.
    intros Nc. destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_drb in G in change_no_check G' end). destruct (Z.eqb_spec nx 0) as [Enx | Nnx]; (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    - wd_eexists. split.
      + bh1. ab_ft F_4dd78 D_4dd78 ltac:(condz). fsd F_4dd7c D_4dd7c (at_ S (-2272)). bh2.
        ab_ft F_4dd9c D_4dd9c ltac:(condz).            (* [comment removed for export] *)
        av F_4dda0 D_4dda0 (Z_to_bv 64 (b + 152)) ltac:(valz).   (* [comment removed for export] *)
        av F_4dda4 D_4dda4 (Z_to_bv 64 (cnt + 16)) ltac:(valz).  (* [comment removed for export] *)
        an F_4dda8 D_4dda8.                            (* [comment removed for export] *)
        wd_refl.
      + post.
    - wd_eexists. split.
      + bh1. ab_tk F_4dd78 D_4dd78 ltac:(condz). bh2.
        ab_ft F_4dd9c D_4dd9c ltac:(condz).
        av F_4dda0 D_4dda0 (Z_to_bv 64 (b + 152)) ltac:(valz).
        av F_4dda4 D_4dda4 (Z_to_bv 64 (cnt + 16)) ltac:(valz).
        an F_4dda8 D_4dda8.
        wd_refl.
      + post.
  Qed.

  (* [comment removed for export] *)
  Lemma dr_bhead_empty : (cnt = 0)%Z ->
    exists r, msteps ASEGS (mkst regs (0x4dd74 : word) mem rom) (mkst r (0x4ddcc : word) Mb rom)
      /\ dr_regs S r /\ dr_keep regs r /\ getr r 20 = Z_to_bv 64 b.
  Proof using Rcnt Rbsz Rnx Rtby Rfirst Hstk Hb Hcnt Hnx Htby Htsz HS H10 HR.
    intros Ec. destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    (lazymatch goal with |- ?G => let G' := eval unfold fr_drb in G in change_no_check G' end). destruct (Z.eqb_spec nx 0) as [Enx | Nnx]; (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
    - wd_eexists. split.
      + bh1. ab_ft F_4dd78 D_4dd78 ltac:(condz). fsd F_4dd7c D_4dd7c (at_ S (-2272)). bh2.
        ab_tk F_4dd9c D_4dd9c ltac:(condz). wd_refl.
      + post.
    - wd_eexists. split.
      + bh1. ab_tk F_4dd78 D_4dd78 ltac:(condz). bh2.
        ab_tk F_4dd9c D_4dd9c ltac:(condz). wd_refl.
      + post.
  Qed.
End DRBHEAD.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section DRITEM.
  Variables (mem rom : word -> option byte) (S : word) (c7 c8 i9 item : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : dr_regs S regs.
  Hypothesis H23 : getr regs 23 = Z_to_bv 64 c7.
  Hypothesis H24 : getr regs 24 = Z_to_bv 64 c8.
  Hypothesis H25 : getr regs 25 = Z_to_bv 64 i9.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hc7 : (128 <= c7 /\ c7 + 8 < 2 ^ 64)%Z.
  Hypothesis Hi9 : (0 <= i9 < 2 ^ 32 /\ 0 <= c8 < 2 ^ 32)%Z.

  Definition dr_cursor (r : bvmap 5 word) (x7 x8 x9 : Z) : Prop :=
    getr r 23 = Z_to_bv 64 x7 /\ getr r 24 = Z_to_bv 64 x8 /\ getr r 25 = Z_to_bv 64 x9 /\ getr r 20 = getr regs 20.

  (* [comment removed for export] *)
  Lemma dr_item_call :
    rdn ASEGS mem (Z_to_bv 64 (c7 - 128)) 8 = Some (LE8 (Z_to_bv 64 item)) ->
    exists r, msteps ASEGS (mkst regs (0x4ddb4 : word) mem rom) (mkst r (0x4de34 : word) mem rom)
      /\ dr_regs S r /\ dr_keep regs r /\ dr_cursor r c7 c8 i9
      /\ getr r 1 = Z_to_bv 64 0x4ddc0 /\ getr r 10 = at_ S (-2392) /\ getr r 11 = Z_to_bv 64 item.
  Proof using Hc7 H25 H24 H23 HR.
    intros Ritem. destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep, dr_cursor in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - cld8 F_4ddac D_4ddac (Z_to_bv 64 item) Ritem.    (* [comment removed for export] *)
      an F_4ddb0 D_4ddb0.                              (* [comment removed for export] *)
      an F_4ddb4 D_4ddb4.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Lemma dr_item_next_more : (i9 + 1 <> c8)%Z ->
    exists r, msteps ASEGS (mkst regs (0x4ddc0 : word) mem rom) (mkst r (0x4ddb4 : word) mem rom)
      /\ dr_regs S r /\ dr_keep regs r /\ dr_cursor r (c7 + 8) c8 (i9 + 1).
  Proof using Hi9 Hc7 H25 H24 H23 HR.
    intros Nm. destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep, dr_cursor in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - av F_4ddb8 D_4ddb8 (Z_to_bv 64 (i9 + 1)) ltac:(valz).   (* [comment removed for export] *)
      av F_4ddbc D_4ddbc (Z_to_bv 64 (c7 + 8)) ltac:(valz).   (* [comment removed for export] *)
      ab_tk F_4ddc0 D_4ddc0 ltac:(condz).              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
  Lemma dr_item_next_done : (i9 + 1 = c8)%Z ->
    exists r, msteps ASEGS (mkst regs (0x4ddc0 : word) mem rom) (mkst r (0x4ddcc : word) mem rom)
      /\ dr_regs S r /\ dr_keep regs r /\ getr r 20 = getr regs 20.
  Proof using Hi9 Hc7 H25 H24 H23 HR c7.
    intros Em. destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - av F_4ddb8 D_4ddb8 (Z_to_bv 64 (i9 + 1)) ltac:(valz).
      av F_4ddbc D_4ddbc (Z_to_bv 64 (c7 + 8)) ltac:(valz).
      ab_ft F_4ddc0 D_4ddc0 ltac:(condz).              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End DRITEM.

Section DRBFREE.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v cachev : word) (spb b d tsz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis HR : dr_regs S regs.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 b.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hspb : (0 <= spb /\ spb + 2 ^ 37 < 2 ^ 64)%Z.
  Hypothesis Hb : (b = spb + 24 * 2 ^ 32 + d /\ 0 <= d < 2 ^ 32)%Z.                (* [comment removed for export] *)
  Hypothesis Rspb : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).
  Hypothesis Rcache : rdn ASEGS mem (at_ S (-2392)) 8 = Some (LE8 cachev).

  (* [comment removed for export] *)
  Lemma dr_bfree_call :
    exists r, msteps ASEGS (mkst regs (0x4ddcc : word) mem rom) (mkst r (0x4e238 : word) mem rom)
      /\ dr_regs S r /\ dr_keep regs r /\ getr r 20 = Z_to_bv 64 b
      /\ getr r 1 = Z_to_bv 64 0x4ddf8 /\ getr r 10 = cachev /\ getr r 11 = Z_to_bv 64 0x103f18 /\ getr r 12 = Z_to_bv 64 24 /\ getr r 13 = Z_to_bv 64 b.
  Proof using Rcache Rspb Hb Hspb H20 HR d spb.
    destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr. destruct Hb as (Eb & Hd).
    wd_eexists. split.
    - cld8 F_4ddc4 D_4ddc4 (Z_to_bv 64 spb) Rspb.      (* [comment removed for export] *)
      ab_ft F_4ddc8 D_4ddc8 ltac:(condz).              (* [comment removed for export] *)
      av F_4ddcc D_4ddcc (Z_to_bv 64 (spb + 2 ^ 37)) ltac:(valz).   (* [comment removed for export] *)
      ab_ft F_4ddd0 D_4ddd0 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4ddd4 D_4ddd4 cachev Rcache.              (* [comment removed for export] *)
      av F_4ddd8 D_4ddd8 (Z_to_bv 64 (24 * 2 ^ 32 + d)) ltac:(valz).   (* [comment removed for export] *)
      an F_4dddc D_4dddc.                              (* [comment removed for export] *)
      av F_4dde0 D_4dde0 (Z_to_bv 64 24) ltac:(apply (cls_of_off 24 d); lia).   (* [comment removed for export] *)
      an F_4dde4 D_4dde4.                              (* [comment removed for export] *)
      an F_4dde8 D_4dde8.                              (* [comment removed for export] *)
      an F_4ddec D_4ddec.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Hypothesis Rtsz : rdn ASEGS mem (at_ S (-2288)) 8 = Some (LE8 (Z_to_bv 64 tsz)).
  Hypothesis Htsz : (0 <= tsz < 2 ^ 64)%Z.
  Lemma dr_bnext_more : (tsz <> 0)%Z ->
    exists r, msteps ASEGS (mkst regs (0x4ddf8 : word) mem rom) (mkst r (0x4dd74 : word) mem rom)
      /\ dr_regs S r /\ dr_keep regs r /\ getr r 10 = Z_to_bv 64 tsz.
  Proof using Htsz Rtsz HR.
    intros Nz. destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_regs, dr_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - cld8 F_4ddf0 D_4ddf0 (Z_to_bv 64 tsz) Rtsz.      (* [comment removed for export] *)
      ab_tk F_4ddf4 D_4ddf4 ltac:(condz).              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.

  Hypothesis Hret : ret_ok ra0.
  Hypothesis Cra : rdn ASEGS mem (at_ S (-2296)) 8 = Some (LE8 ra0).
  Hypothesis Cs0 : rdn ASEGS mem (at_ S (-2304)) 8 = Some (LE8 s0v).
  Hypothesis Cs1 : rdn ASEGS mem (at_ S (-2312)) 8 = Some (LE8 s1v).
  Hypothesis Cs2 : rdn ASEGS mem (at_ S (-2320)) 8 = Some (LE8 s2v).
  Hypothesis Cs3 : rdn ASEGS mem (at_ S (-2328)) 8 = Some (LE8 s3v).
  Hypothesis Cs4 : rdn ASEGS mem (at_ S (-2336)) 8 = Some (LE8 s4v).
  Hypothesis Cs5 : rdn ASEGS mem (at_ S (-2344)) 8 = Some (LE8 s5v).
  Hypothesis Cs6 : rdn ASEGS mem (at_ S (-2352)) 8 = Some (LE8 s6v).
  Hypothesis Cs7 : rdn ASEGS mem (at_ S (-2360)) 8 = Some (LE8 s7v).
  Hypothesis Cs8 : rdn ASEGS mem (at_ S (-2368)) 8 = Some (LE8 s8v).
  Hypothesis Cs9 : rdn ASEGS mem (at_ S (-2376)) 8 = Some (LE8 s9v).
  Lemma dr_bnext_done : (tsz = 0)%Z ->
    exists r, msteps ASEGS (mkst regs (0x4ddf8 : word) mem rom) (mkst r ra0 mem rom)
      /\ getr r 2 = at_ S (-2288) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 21 = s5v /\ getr r 22 = s6v /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v /\ dr_keep regs r.
  Proof using Cs9 Cs8 Cs7 Cs6 Cs5 Cs4 Cs3 Cs2 Cs1 Cs0 Cra Hret Htsz Rtsz HR.
    intros Ez. destruct HR as (R2 & R8 & R9 & R21 & R18 & R19). (lazymatch goal with |- ?G => let G' := eval unfold dr_keep in G in change_no_check G' end). pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - cld8 F_4ddf0 D_4ddf0 (Z_to_bv 64 tsz) Rtsz.      (* [comment removed for export] *)
      ab_ft F_4ddf4 D_4ddf4 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4ddf8 D_4ddf8 ra0 Cra. cld8 F_4ddfc D_4ddfc s0v Cs0. cld8 F_4de00 D_4de00 s1v Cs1. cld8 F_4de04 D_4de04 s2v Cs2.
      cld8 F_4de08 D_4de08 s3v Cs3. cld8 F_4de0c D_4de0c s4v Cs4. cld8 F_4de10 D_4de10 s5v Cs5. cld8 F_4de14 D_4de14 s6v Cs6.
      cld8 F_4de18 D_4de18 s7v Cs7. cld8 F_4de1c D_4de1c s8v Cs8. cld8 F_4de20 D_4de20 s9v Cs9.
      an F_4de24 D_4de24.                              (* [comment removed for export] *)
      aret F_4de28 D_4de28 ra0.                        (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End DRBFREE.
End FPGen.
End AsAllocFRc2.
Require LinuxProcessSemantics.Riscv.Sem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocFRc3c.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac AsAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Ltac famo F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_amoadd_d with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
      | rd_addr Hr | exact Hv | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

(* [comment removed for export] *)
Definition fr_k5 (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) (T c cnt e : Z) (stw : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2408)) (LE8 ra0))
    (at_ S (-2416)) (LE8 s0v))
    (at_ S (-2424)) (LE8 s1v))
    (at_ S (-2432)) (LE8 s2v))
    (at_ S (-2440)) (LE8 s3v))
    (at_ S (-2448)) (LE8 s4v))
    (Z_to_bv 64 (T + 208 + 80 * c)) (LE4 (cnt + 1)))
    (Z_to_bv 64 (T + 208 + 80 * c + 16 + 4 * cnt)) (LE4 (e / 16)))
    (Z_to_bv 64 (T + 2784)) (LE8 stw).
#[local] Hint Unfold fr_k5 : asfr.

Section K5.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) (T spb c e cnt mx : Z) (bst bcs : list byte).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation pc_ := (T + 208 + 80 * c)%Z.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2400).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (T + 208).
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 0x103f18.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 (spb + c * 2 ^ 32 + e).
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584) /\ T mod 16 = 0)%Z.
  Hypothesis Hspb : (0 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis He : (0 <= e < 2 ^ 32)%Z.
  Hypothesis Hcnt : (0 <= cnt < mx /\ mx <= 16)%Z.                             (* [comment removed for export] *)
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Lbst : length bst = 8%nat.
  Hypothesis Lbcs : length bcs = 8%nat.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2448)) 48 = true.
  Hypothesis HokT : store_ok ASEGS mem (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis Rmx : rdn ASEGS mem (Z_to_bv 64 (pc_ + 4)) 4 = Some (LE4 mx).
  Hypothesis Rcnt : rdn ASEGS mem (Z_to_bv 64 pc_) 4 = Some (LE4 cnt).
  Hypothesis Rcs : rdn ASEGS mem (Z_to_bv 64 (pc_ + 8)) 8 = Some bcs.
  Hypothesis Rst : rdn ASEGS mem (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis Rspb : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).

  #[local] Abbreviation stw := (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 (bytes_le_to_Z bcs)))).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma k5_facts : (cnt * 2 ^ 32 / 2 ^ 30 = 4 * cnt /\ (T + 2784) mod 8 = 0)%Z.
  Proof using Lbcs Lbst He HT bcs bst e s4v S rom. destruct HT as (_ & _ & T16). split; [| lia]. replace (cnt * 2 ^ 32)%Z with (4 * cnt * 2 ^ 30)%Z by lia. rewrite Z.div_mul by lia. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma k5_run :
    exists r, msteps ASEGS (mkst regs (0x4e238 : word) mem rom) (mkst r ra0 (fr_k5 mem S ra0 s0v s1v s2v s3v s4v T c cnt e stw) rom)
      /\ getr r 2 = at_ S (-2400) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rspb Rst Rcs Rcnt Rmx HokT Hstk Lbcs Lbst Hret Hcnt He Hc Hspb HT HS H20 H19 H18 H9 H8 H13 H12 H11 H10 H2 H1 mx spb.
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2 & HT16). unfold hideW in HT2. destruct k5_facts as [Hc4 Hal8].
    pose proof (bytes_le_to_Z_bound bst) as Bst. rewrite Lbst in Bst. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bst.
    pose proof (bytes_le_to_Z_bound bcs) as Bcs. rewrite Lbcs in Bcs. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bcs.
    pose proof (bytes_le_to_Z_nonneg bst) as Bst'. pose proof (bytes_le_to_Z_nonneg bcs) as Bcs'.
    assert (Vst : bytes_le_to_Z bst = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bst))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcs : bytes_le_to_Z bcs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bcs))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcnt : bytes_le_to_Z (LE4 cnt) = bv_unsigned (Z_to_bv 64 cnt)) by (apply bytes4_small; lia).
    assert (Vmx : bytes_le_to_Z (LE4 mx) = bv_unsigned (Z_to_bv 64 mx)) by (apply bytes4_small; lia).
    wd_eexists. split.
    - an F_4e230 D_4e230.                              (* [comment removed for export] *)
      fsd F_4e234 D_4e234 (at_ S (-2408)).             (* [comment removed for export] *)
      fsd F_4e238 D_4e238 (at_ S (-2416)).
      fsd F_4e23c D_4e23c (at_ S (-2424)).
      fsd F_4e240 D_4e240 (at_ S (-2432)).
      fsd F_4e244 D_4e244 (at_ S (-2440)).
      fsd F_4e248 D_4e248 (at_ S (-2448)).
      ab_ft F_4e24c D_4e24c ltac:(condz).              (* [comment removed for export] *)
      an F_4e250 D_4e250.                              (* [comment removed for export] *)
      ab_ft F_4e254 D_4e254 ltac:(condz).              (* [comment removed for export] *)
      an F_4e258 D_4e258.                              (* [comment removed for export] *)
      av F_4e25c D_4e25c (Z_to_bv 64 (80 * c)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_4e260 D_4e260 (Z_to_bv 64 pc_) ltac:(valz).  (* [comment removed for export] *)
      clw F_4e264 D_4e264 (LE4 mx) (Z_to_bv 64 mx) Rmx Vmx.       (* [comment removed for export] *)
      rewrite (v_lw_small mx) by lia.
      ab_ft F_4e268 D_4e268 ltac:(condz).              (* [comment removed for export] *)
      clw F_4e26c D_4e26c (LE4 cnt) (Z_to_bv 64 cnt) Rcnt Vcnt.   (* [comment removed for export] *)
      rewrite (v_lw_small cnt) by lia.
      ab_ft F_4e270 D_4e270 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e274 D_4e274 (Z_to_bv 64 spb) Rspb.      (* [comment removed for export] *)
      av F_4e278 D_4e278 (Z_to_bv 64 (c * 2 ^ 32)) ltac:(apply cls_shl32; lia).   (* [comment removed for export] *)
      av F_4e27c D_4e27c (Z_to_bv 64 (spb + e)) ltac:(valz).      (* [comment removed for export] *)
      av F_4e280 D_4e280 (Z_to_bv 64 (cnt * 2 ^ 32)) ltac:(valz). (* [comment removed for export] *)
      av F_4e284 D_4e284 (Z_to_bv 64 (cnt + 1)) ltac:(valz).      (* [comment removed for export] *)
      av F_4e288 D_4e288 (Z_to_bv 64 e) ltac:(valz).   (* [comment removed for export] *)
      cld F_4e28c D_4e28c bcs (Z_to_bv 64 (bytes_le_to_Z bcs)) Rcs Vcs.   (* [comment removed for export] *)
      an F_4e290 D_4e290.                              (* [comment removed for export] *)
      av F_4e294 D_4e294 (Z_to_bv 64 (4 * cnt)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite <- Hc4; unorm; reflexivity).   (* [comment removed for export] *)
      av F_4e298 D_4e298 (Z_to_bv 64 (T + 2784)) ltac:(valz).     (* [comment removed for export] *)
      av F_4e29c D_4e29c (Z_to_bv 64 (pc_ + 4 * cnt)) ltac:(valz).   (* [comment removed for export] *)
      av F_4e2a0 D_4e2a0 (Z_to_bv 64 (e / 16)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; reflexivity).   (* [comment removed for export] *)
      fsw F_4e2a4 D_4e2a4 (Z_to_bv 64 pc_).            (* [comment removed for export] *)
      fsw F_4e2a8 D_4e2a8 (Z_to_bv 64 (pc_ + 16 + 4 * cnt)).   (* [comment removed for export] *)
      an F_4e2ac D_4e2ac.                              (* [comment removed for export] *)
      famo F_4e2b0 D_4e2b0 bst (Z_to_bv 64 (bytes_le_to_Z bst)) Rst Vst.   (* [comment removed for export] *)
      fld F_4e2b4 D_4e2b4 ra0. fld F_4e2b8 D_4e2b8 s0v. fld F_4e2bc D_4e2bc s1v. fld F_4e2c0 D_4e2c0 s2v.
      fld F_4e2c4 D_4e2c4 s3v. fld F_4e2c8 D_4e2c8 s4v.
      an F_4e2cc D_4e2cc.                              (* [comment removed for export] *)
      aret F_4e2d0 D_4e2d0 ra0.                        (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_k5 mem S ra0 s0v s1v s2v s3v s4v T c cnt e stw). wd_refl.
    - post.
  Qed.
End K5.
End FPGen.
End AsAllocFRc3c.
Module AsAllocFRcS1.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac AsAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

(* [comment removed for export] *)
Fixpoint gbb_scan (p : Z) (l : list Z) (acc : Z) : Z :=
  match l with
  | [] => acc
  | h :: r => gbb_scan p r (if ((h <=? p) && (acc <? h))%bool then h else acc)
  end.

Section FPGen.
Context {fx : FPState}.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.
Ltac pc4 := apply bv_eq; reflexivity.
(* [comment removed for export] *)
Ltac fsb F D aa bb :=
  chain_step; [reflexivity
    | eapply MmapSim.step_sb_at with (a := aa) (b := bb);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; first [reflexivity | f_equal; lia | apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); wd_ulia]
      | gres; rwH; reflexivity
      | first [reflexivity | apply bv_eq; unorm; reflexivity]
      | first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

Lemma sok_seclock : forall m, store_ok ASEGS m (Z_to_bv 64 0x1041c0) 4 = true.
Proof using. intros m. apply store_ok_wseg. vm_compute. reflexivity. Qed.

Lemma v_andi_255_andS : forall x : word, v_andi x 255 = v_and x (Z_to_bv 64 255).
Proof using.
  intros x. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned 64 x) at 1. rewrite v_andi_Z by lia.
  rewrite <- (Z_to_bv_bv_unsigned 64 x) at 2. rewrite v_and_Z by lia. reflexivity.
Qed.
Lemma lock_byte0S : forall (b0 b1 b2 b3 : byte) (v : word),
  bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v -> v_andi (v_lw v) 255 = Z_to_bv 64 (bv_unsigned b0).
Proof using.
  intros b0 b1 b2 b3 v Hv. rewrite v_andi_255_andS.
  rewrite (and_mask_byte [b0; b1; b2; b3] v (Z_to_bv 64 255) 0 eq_refl Hv ltac:(lia) ltac:(reflexivity)).
  (lazymatch goal with |- ?G => let G' := eval cbn [nth Z.of_nat Z.mul] in G in change_no_check G' end). rewrite Z.mul_1_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma gbb_lock_4e0d4 : forall regs mem rom (v : word) b0 b1 b2 b3,
  getr regs 13 = Z_to_bv 64 0x1041c0 -> getr regs 12 = Z_to_bv 64 255 -> getr regs 14 = Z_to_bv 64 1 ->
  rdn ASEGS mem (Z_to_bv 64 0x1041c0) 4%nat = Some [b0; b1; b2; b3] -> bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v ->
  msteps ASEGS (mkst regs (0x4e0dc : word) mem rom)
    (mkst (regupd (regupd regs 15 (v_lw v)) 16 (Z_to_bv 64 0)) (0x4e0f8 : word)
          (wbytes mem (Z_to_bv 64 0x1041c0) [Z_to_bv 8 1; b1; b2; b3]) rom).
Proof using.
  intros regs mem rom v b0 b1 b2 b3 H13 H12 H14 Hrd Hv.
  pose proof (xchg_byte_run ASEGS regs (0x4e0dc : word) (0x4e0e0 : word) (0x4e0e4 : word) (0x4e0e8 : word)
                (0x4e0ec : word) (0x4e0f0 : word) (0x4e0f4 : word) (0x4e0f8 : word) mem rom
                _ _ _ _ _ _ _ _ _ _ _ 15 13 16 14 12 _ [b0; b1; b2; b3] v 0%nat 1%Z
                F_4e0d4 eq_refl D_4e0d4 F_4e0d8 eq_refl D_4e0d8 F_4e0dc eq_refl D_4e0dc F_4e0e0 eq_refl D_4e0e0
                F_4e0e4 eq_refl D_4e0e4 F_4e0e8 eq_refl D_4e0e8 F_4e0ec eq_refl D_4e0ec) as R.
  rewrite H13, H12, H14 in R. cbn [firstn skipn app] in R.
  apply R; clear R; first [regneq | pc4 | apply sok_seclock | unorm; reflexivity | lia | assumption].
Qed.

(* [comment removed for export] *)
Definition fr_gbb0 (mem : word -> option byte) (S ra0 s0v s1v s2v : word) (b1 b2 b3 : byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2456)) (LE8 ra0))
    (at_ S (-2464)) (LE8 s0v))
    (at_ S (-2472)) (LE8 s1v))
    (at_ S (-2480)) (LE8 s2v))
    (Z_to_bv 64 0x1041c0) [Z_to_bv 8 1; b1; b2; b3].
#[local] Hint Unfold fr_gbb0 : asfr.

(* [comment removed for export] *)
Definition gbb_keep (r r' : bvmap 5 word) : Prop :=
  getr r' 1 = getr r 1 /\ getr r' 2 = getr r 2 /\ getr r' 3 = getr r 3 /\ getr r' 4 = getr r 4 /\ getr r' 8 = getr r 8 /\ getr r' 9 = getr r 9
  /\ getr r' 10 = getr r 10 /\ getr r' 11 = getr r 11 /\ getr r' 14 = getr r 14
  /\ getr r' 18 = getr r 18 /\ getr r' 19 = getr r 19 /\ getr r' 20 = getr r 20 /\ getr r' 21 = getr r 21
  /\ getr r' 22 = getr r 22 /\ getr r' 23 = getr r 23 /\ getr r' 24 = getr r 24 /\ getr r' 25 = getr r 25 /\ getr r' 26 = getr r 26 /\ getr r' 27 = getr r 27.

Section GBB1.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v v : word) (b1 b2 b3 : byte) (len ptr : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2448).
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x103f58.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis Hlen : (1 <= len <= 2 ^ 20)%Z.
  Hypothesis Hptr : (0 <= ptr /\ ptr + 8 * len < 2 ^ 47)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2480)) 32 = true.
  Hypothesis Rlock : rdn ASEGS mem (Z_to_bv 64 0x1041c0) 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis HV : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = bv_unsigned v.
  Hypothesis Rn : rdn ASEGS mem (Z_to_bv 64 (0x103f58 + 56)) 8 = Some (LE8 (Z_to_bv 64 len)).
  Hypothesis Rptr : rdn ASEGS mem (Z_to_bv 64 (0x103f58 + 8)) 8 = Some (LE8 (Z_to_bv 64 ptr)).

  Lemma gbb_head :
    exists r, msteps ASEGS (mkst regs (0x4e0b8 : word) mem rom) (mkst r (0x4e124 : word) (fr_gbb0 mem S ra0 s0v s1v s2v b1 b2 b3) rom)
      /\ getr r 2 = at_ S (-2480) /\ getr r 8 = Z_to_bv 64 0x1041c0 /\ getr r 10 = Z_to_bv 64 0x103f58 /\ getr r 11 = getr regs 11
      /\ getr r 12 = Z_to_bv 64 ptr /\ getr r 13 = Z_to_bv 64 0 /\ getr r 14 = Z_to_bv 64 (ptr + 8 * len)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rptr Rn HV Rlock Hstk Hptr Hlen HS H10 H18 H9 H8 H2 H1 v.
    pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - an F_4e0b0 D_4e0b0.                              (* [comment removed for export] *)
      fsd F_4e0b4 D_4e0b4 (at_ S (-2456)).             (* [comment removed for export] *)
      fsd F_4e0b8 D_4e0b8 (at_ S (-2464)).             (* [comment removed for export] *)
      fsd F_4e0bc D_4e0bc (at_ S (-2472)).             (* [comment removed for export] *)
      fsd F_4e0c0 D_4e0c0 (at_ S (-2480)).             (* [comment removed for export] *)
      an F_4e0c4 D_4e0c4.                              (* [comment removed for export] *)
      an F_4e0c8 D_4e0c8.                              (* [comment removed for export] *)
      an F_4e0cc D_4e0cc.                              (* [comment removed for export] *)
      an F_4e0d0 D_4e0d0.                              (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (gbb_lock_4e0d4 _ _ rom v (Z_to_bv 8 0) b1 b2 b3);
          [ gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | rd_addr Rlock
          | exact HV ]. }
      av F_4e0f0 D_4e0f0 (Z_to_bv 64 0) ltac:(rewrite (lock_byte0S (Z_to_bv 8 0) b1 b2 b3 _ HV); unorm; reflexivity).   (* [comment removed for export] *)
      ab_ft F_4e0f4 D_4e0f4 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e0f8 D_4e0f8 (Z_to_bv 64 len) Rn.        (* [comment removed for export] *)
      ab_ft F_4e0fc D_4e0fc ltac:(condz).              (* [comment removed for export] *)
      an F_4e100 D_4e100.                              (* [comment removed for export] *)
      cld8 F_4e104 D_4e104 (Z_to_bv 64 ptr) Rptr.      (* [comment removed for export] *)
      av F_4e108 D_4e108 (Z_to_bv 64 (8 * len)) ltac:(valz).          (* [comment removed for export] *)
      av F_4e10c D_4e10c (Z_to_bv 64 (ptr + 8 * len)) ltac:(valz).    (* [comment removed for export] *)
      an F_4e110 D_4e110.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_gbb0 mem S ra0 s0v s1v s2v b1 b2 b3). wd_refl.
    - post.
  Qed.
End GBB1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma v_sub_modS : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> v_sub (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 ((a - b) mod 2 ^ 64).
Proof using.
  intros a b Ha Hb. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end). rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
  rewrite (Z.mod_small a), (Z.mod_small b) by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma sub_mod_neg : forall p h, (0 <= p < h)%Z -> (h < 2 ^ 64)%Z -> ((p - h) mod 2 ^ 64 = p - h + 2 ^ 64)%Z.
Proof using. intros p h H1 H2. symmetry. apply (Z.mod_unique (p - h) (2 ^ 64) (-1) (p - h + 2 ^ 64)); lia. Qed.

(* [comment removed for export] *)
Lemma gbb_body : forall (regs : bvmap 5 word) (mem rom : word -> option byte) (p a acc h : Z),
  getr regs 12 = Z_to_bv 64 a -> getr regs 13 = Z_to_bv 64 acc -> getr regs 11 = Z_to_bv 64 p ->
  (0 <= acc <= p)%Z -> (p < 2 ^ 63)%Z -> (0 <= h < 2 ^ 63)%Z -> (0 <= a /\ a + 8 < 2 ^ 63)%Z ->
  rdn ASEGS mem (Z_to_bv 64 a) 8 = Some (LE8 (Z_to_bv 64 h)) ->
  exists r, msteps ASEGS (mkst regs (0x4e124 : word) mem rom) (mkst r (0x4e120 : word) mem rom)
    /\ gbb_keep regs r /\ getr r 12 = Z_to_bv 64 (a + 8)
    /\ getr r 13 = Z_to_bv 64 (if ((h <=? p) && (acc <? h))%bool then h else acc).
Proof using.
  intros regs mem rom p a acc h H12 H13 H11 Hacc Hp Hh Ha C0.
  destruct (Z_le_gt_dec h p) as [LE | GT].
  - destruct (Z_lt_le_dec acc h) as [LT | GE].
    + (* [comment removed for export] *)
      replace ((h <=? p) && (acc <? h))%bool with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
      wd_eexists. split; [|split].
      * cld8 F_4e11c D_4e11c (Z_to_bv 64 h) C0.      (* [comment removed for export] *)
        av F_4e120 D_4e120 (Z_to_bv 64 (p - h)) ltac:(valz).      (* [comment removed for export] *)
        av F_4e124 D_4e124 (Z_to_bv 64 (p - acc)) ltac:(valz).    (* [comment removed for export] *)
        an F_4e128 D_4e128.                            (* [comment removed for export] *)
        ab_tk F_4e12c D_4e12c ltac:(condz).            (* [comment removed for export] *)
        ab_ft F_4e13c D_4e13c ltac:(condz).            (* [comment removed for export] *)
        an F_4e140 D_4e140.                            (* [comment removed for export] *)
        an F_4e144 D_4e144.                            (* [comment removed for export] *)
        av F_4e114 D_4e114 (Z_to_bv 64 (a + 8)) ltac:(valz).   (* [comment removed for export] *)
        wd_refl.
      * (lazymatch goal with |- ?G => let G' := eval unfold gbb_keep in G in change_no_check G' end). post.
      * post.
    + (* [comment removed for export] *)
      replace ((h <=? p) && (acc <? h))%bool with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; lia).
      wd_eexists. split; [|split].
      * cld8 F_4e11c D_4e11c (Z_to_bv 64 h) C0.
        av F_4e120 D_4e120 (Z_to_bv 64 (p - h)) ltac:(valz).
        av F_4e124 D_4e124 (Z_to_bv 64 (p - acc)) ltac:(valz).
        an F_4e128 D_4e128.
        ab_ft F_4e12c D_4e12c ltac:(condz).            (* [comment removed for export] *)
        an F_4e130 D_4e130.                            (* [comment removed for export] *)
        ab_ft F_4e134 D_4e134 ltac:(condz).            (* [comment removed for export] *)
        an F_4e138 D_4e138.                            (* [comment removed for export] *)
        an F_4e140 D_4e140.                            (* [comment removed for export] *)
        an F_4e144 D_4e144.                            (* [comment removed for export] *)
        av F_4e114 D_4e114 (Z_to_bv 64 (a + 8)) ltac:(valz).
        wd_refl.
      * (lazymatch goal with |- ?G => let G' := eval unfold gbb_keep in G in change_no_check G' end). post.
      * post.
  - (* [comment removed for export] *)
    replace ((h <=? p) && (acc <? h))%bool with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; lia).
    wd_eexists. split; [|split].
    * cld8 F_4e11c D_4e11c (Z_to_bv 64 h) C0.
      av F_4e120 D_4e120 (Z_to_bv 64 (p - h + 2 ^ 64)) ltac:(rewrite v_sub_modS by lia; rewrite sub_mod_neg by lia; reflexivity).
      av F_4e124 D_4e124 (Z_to_bv 64 (p - acc)) ltac:(valz).
      an F_4e128 D_4e128.
      ab_ft F_4e12c D_4e12c ltac:(condz).              (* [comment removed for export] *)
      an F_4e130 D_4e130.                              (* [comment removed for export] *)
      ab_tk F_4e134 D_4e134 ltac:(condz).              (* [comment removed for export] *)
      av F_4e114 D_4e114 (Z_to_bv 64 (a + 8)) ltac:(valz).
      wd_refl.
    * (lazymatch goal with |- ?G => let G' := eval unfold gbb_keep in G in change_no_check G' end). post.
    * post.
Qed.

Lemma gbb_loop : forall (l : list Z) (regs : bvmap 5 word) (mem rom : word -> option byte) (p a acc : Z),
  l <> [] -> getr regs 12 = Z_to_bv 64 a -> getr regs 13 = Z_to_bv 64 acc -> getr regs 11 = Z_to_bv 64 p ->
  getr regs 14 = Z_to_bv 64 (a + 8 * Z.of_nat (length l)) ->
  (0 <= acc <= p)%Z -> (p < 2 ^ 63)%Z -> Forall (fun h => (0 <= h < 2 ^ 63)%Z) l -> (0 <= a /\ a + 8 * Z.of_nat (length l) < 2 ^ 63)%Z ->
  (forall i h, nth_error l i = Some h -> rdn ASEGS mem (Z_to_bv 64 (a + 8 * Z.of_nat i)) 8 = Some (LE8 (Z_to_bv 64 h))) ->
  exists r, msteps ASEGS (mkst regs (0x4e124 : word) mem rom) (mkst r (0x4e150 : word) mem rom)
    /\ gbb_keep regs r /\ getr r 13 = Z_to_bv 64 (gbb_scan p l acc).
Proof using.
  induction l as [|h l IH]; intros regs mem rom p a acc NE H12 H13 H11 H14 Hacc Hp Hl Ha Hcells; [exfalso; exact (NE eq_refl)|].
  apply Forall_cons_iff in Hl as [Hh Hl]. cbn [length] in *.
  pose proof (Hcells 0%nat h eq_refl) as C0. replace (a + 8 * Z.of_nat 0)%Z with a in C0 by lia.
  destruct (gbb_body regs mem rom p a acc h H12 H13 H11 Hacc Hp Hh ltac:(lia) C0) as (r1 & RUN1 & KP1 & E12 & E13).
  set (acc' := if ((h <=? p) && (acc <? h))%bool then h else acc) in *.
  assert (Hacc' : (0 <= acc' <= p)%Z).
  { (lazymatch goal with |- ?G => let G' := eval unfold acc' in G in change_no_check G' end). destruct ((h <=? p) && (acc <? h))%bool eqn:EB; [|exact Hacc].
    apply andb_prop in EB as [EB1 EB2]. apply Z.leb_le in EB1. lia. }
  pose proof KP1 as (K1 & K2 & K3 & K4 & K8 & K9 & K10 & K11 & K14 & K18 & K19 & K20 & K21 & K22 & K23 & K24 & K25 & K26 & K27).
  destruct l as [|h' l'].
  - (* [comment removed for export] *)
    cbn [length] in *. (lazymatch goal with |- ?G => let G' := eval cbn [gbb_scan] in G in change_no_check G' end). fold acc'.
    assert (X : exists r2, msteps ASEGS (mkst r1 (0x4e120 : word) mem rom) (mkst r2 (0x4e150 : word) mem rom) /\ r2 = r1).
    { wd_eexists. split; [| reflexivity].
      ab_tk F_4e118 D_4e118 ltac:(condz).   (* [comment removed for export] *)
      wd_refl. }
    destruct X as (r2 & RUN2 & ->).
    exists r1. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|]. split; [exact KP1 | exact E13].
  - cbn [length] in *.
    assert (X : exists r2, msteps ASEGS (mkst r1 (0x4e120 : word) mem rom) (mkst r2 (0x4e124 : word) mem rom) /\ r2 = r1).
    { wd_eexists. split; [| reflexivity].
      ab_ft F_4e118 D_4e118 ltac:(condz).   (* [comment removed for export] *)
      wd_refl. }
    destruct X as (r2 & RUN2 & ->).
    destruct (IH r1 mem rom p (a + 8)%Z acc' ltac:(discriminate) E12 E13 ltac:(rewrite K11; exact H11)) as (r3 & RUN3 & KP3 & E3).
    + rewrite K14, H14. f_equal. (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). lia.
    + exact Hacc'.
    + exact Hp.
    + exact Hl.
    + (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end). lia.
    + intros i hi Hi. replace (a + 8 + 8 * Z.of_nat i)%Z with (a + 8 * Z.of_nat (Datatypes.S i))%Z by lia. exact (Hcells (Datatypes.S i) hi Hi).
    + exists r3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]]|].
      split; [| (lazymatch goal with |- ?G => let G' := eval cbn [gbb_scan] in G in change_no_check G' end); fold acc'; exact E3].
      destruct KP3 as (L1 & L2 & L3 & L4 & L8 & L9 & L10 & L11 & L14 & L18 & L19 & L20 & L21 & L22 & L23 & L24 & L25 & L26 & L27).
      (lazymatch goal with |- ?G => let G' := eval unfold gbb_keep in G in change_no_check G' end). repeat split; etransitivity; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_gbb1 (mem : word -> option byte) : word -> option byte := wbytes mem (Z_to_bv 64 0x1041c0) [Z_to_bv 8 0].
#[local] Hint Unfold fr_gbb1 : asfr.

Section GBB3.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v : word) (p h msz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2480).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 0x1041c0.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x103f58.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 p.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 h.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis Hh : (AIMGHI <= h /\ h mod 4096 = 0 /\ 4096 <= msz /\ h + msz <= bv_unsigned S - 3584 /\ h <= p < h + msz)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Rmb : rdn ASEGS mem (Z_to_bv 64 h) 8 = Some (LE8 (Z_to_bv 64 h)).
  Hypothesis Rms : rdn ASEGS mem (Z_to_bv 64 (h + 8)) 8 = Some (LE8 (Z_to_bv 64 msz)).
  Hypothesis Rpg : rdn ASEGS mem (Z_to_bv 64 0x103f58) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Cra : rdn ASEGS mem (at_ S (-2456)) 8 = Some (LE8 ra0).
  Hypothesis Cs0 : rdn ASEGS mem (at_ S (-2464)) 8 = Some (LE8 s0v).
  Hypothesis Cs1 : rdn ASEGS mem (at_ S (-2472)) 8 = Some (LE8 s1v).
  Hypothesis Cs2 : rdn ASEGS mem (at_ S (-2480)) 8 = Some (LE8 s2v).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma pg_and0 : v_and (Z_to_bv 64 4095) (Z_to_bv 64 h) = Z_to_bv 64 0.
  Proof using Hh HS msz p s2v S rom.
    destruct Hh as (G1 & G2 & _).
    assert (Hb : (0 <= h < 2 ^ 64)%Z) by (destruct HS; destruct Hh as (_ & _ & ? & ? & _); pose proof (u64_range S); lia).
    rewrite v_and_Z by lia. f_equal. change 4095%Z with (Z.ones 12). rewrite Z.land_comm, Z.land_ones by lia.
    change (2 ^ 12)%Z with 4096%Z. exact G2.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma gbb_tail :
    exists r, msteps ASEGS (mkst regs (0x4e150 : word) mem rom) (mkst r ra0 (fr_gbb1 mem) rom)
      /\ getr r 2 = at_ S (-2448) /\ getr r 10 = Z_to_bv 64 (h + 4096)
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Cs2 Cs1 Cs0 Cra Rpg Rms Rmb Hret Hh HS H13 H11 H10 H8 H2 msz p.
    pose proof (u64_range S) as HSr. destruct Hh as (G1 & G2 & G3 & G4 & G5).
    pose proof (sok_seclock mem) as Hoklk.
    wd_eexists. split.
    - ab_ft F_4e148 D_4e148 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e14c D_4e14c (Z_to_bv 64 h) Rmb.         (* [comment removed for export] *)
      ab_ft F_4e150 D_4e150 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e154 D_4e154 (Z_to_bv 64 msz) Rms.       (* [comment removed for export] *)
      av F_4e158 D_4e158 (Z_to_bv 64 (h + msz)) ltac:(valz).   (* [comment removed for export] *)
      ab_ft F_4e15c D_4e15c ltac:(condz).              (* [comment removed for export] *)
      ab_ft F_4e160 D_4e160 ltac:(condz).              (* [comment removed for export] *)
      ab_ft F_4e164 D_4e164 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e168 D_4e168 (Z_to_bv 64 4096) Rpg.      (* [comment removed for export] *)
      an F_4e16c D_4e16c.                              (* [comment removed for export] *)
      an F_4e170 D_4e170. rewrite pg_and0.             (* [comment removed for export] *)
      ab_ft F_4e174 D_4e174 ltac:(condz).              (* [comment removed for export] *)
      av F_4e178 D_4e178 (Z_to_bv 64 (h + 4096)) ltac:(valz).   (* [comment removed for export] *)
      an F_4e17c D_4e17c.                              (* [comment removed for export] *)
      afence F_4e1a4 D_4e1a4.                          (* [comment removed for export] *)
      fsb F_4e1a8 D_4e1a8 (Z_to_bv 64 0x1041c0) (Z_to_bv 8 0).   (* [comment removed for export] *)
      cld8 F_4e1ac D_4e1ac ra0 Cra.                    (* [comment removed for export] *)
      cld8 F_4e1b0 D_4e1b0 s0v Cs0. cld8 F_4e1b4 D_4e1b4 s1v Cs1. cld8 F_4e1b8 D_4e1b8 s2v Cs2.
      an F_4e1bc D_4e1bc.                              (* [comment removed for export] *)
      aret F_4e1c0 D_4e1c0 ra0.                        (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_gbb1 mem). wd_refl.
    - post.
  Qed.
End GBB3.
End FPGen.
End AsAllocFRcS1.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac AsAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Ltac famoA F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_amoadd_d with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
      | rd_addr Hr | exact Hv | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

(* [comment removed for export] *)
Definition fr_dlf (mem : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2408)) (LE8 ra0))
    (at_ S (-2416)) (LE8 s0v))
    (at_ S (-2424)) (LE8 s1v))
    (at_ S (-2432)) (LE8 s2v))
    (at_ S (-2440)) (LE8 s3v))
    (at_ S (-2448)) (LE8 s4v).
#[local] Hint Unfold fr_dlf : asfr.

(* [comment removed for export] *)
Definition fr_drn (mem : word -> option byte) (S : word) (pcz cnt' : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2456)) (LE8 (Z_to_bv 64 0x4e3e8)))
    (at_ S (-2472)) (LE8 (Z_to_bv 64 0)))
    (at_ S (-2464)) (LE8 (Z_to_bv 64 0)))
    (at_ S (-2504)) (LE8 (Z_to_bv 64 0x103f18)))
    (at_ S (-2496)) (LE8 (Z_to_bv 64 0)))
    (at_ S (-2488)) (LE8 (Z_to_bv 64 0)))
    (at_ S (-2480)) (LE8 (Z_to_bv 64 0)))
    (Z_to_bv 64 pcz) (LE4 cnt').
#[local] Hint Unfold fr_drn : asfr.

Section DLFHEAD.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) (T c pz mx : Z).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation pc_ := (T + 208 + 80 * c)%Z.
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2400).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 (T + 208).
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 0x103f18.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 c.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 pz.
  Hypothesis H8 : getr regs 8 = s0v.   Hypothesis H9 : getr regs 9 = s1v.   Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v. Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584) /\ T mod 16 = 0)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hmx : (2 <= mx <= 16)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2512)) 112 = true.
  Hypothesis HokT : store_ok ASEGS mem (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis Rmx : rdn ASEGS mem (Z_to_bv 64 (pc_ + 4)) 4 = Some (LE4 mx).
  Hypothesis Rcnt : rdn ASEGS mem (Z_to_bv 64 pc_) 4 = Some (LE4 mx).          (* [comment removed for export] *)

  #[local] Abbreviation n := (mx / 2)%Z.
  #[local] Abbreviation M1 := (fr_drn (fr_dlf mem S ra0 s0v s1v s2v s3v s4v) S pc_ (mx - mx / 2)).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma dlf_facts : (1 <= mx / 2 <= 8 /\ mx - mx / 2 >= 1 /\ mx * 2 ^ 32 / 2 ^ 32 = mx)%Z.
  Proof using Hmx HT T s4v S rom. split; [lia|]. split; [lia|]. rewrite Z.div_mul by lia. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Lemma dlf_drn_head :
    exists r, msteps ASEGS (mkst regs (0x4e238 : word) mem rom) (mkst r (0x4e770 : word) M1 rom)
      /\ getr r 1 = Z_to_bv 64 0x4e630 /\ getr r 2 = at_ S (-2512) /\ getr r 10 = Z_to_bv 64 0x103f18 /\ getr r 11 = at_ S (-2504)
      /\ getr r 13 = Z_to_bv 64 c /\ getr r 14 = Z_to_bv 64 (pc_ + 16 + 4 * (mx - mx / 2)) /\ getr r 15 = Z_to_bv 64 (mx / 2)
      /\ getr r 8 = Z_to_bv 64 pc_ /\ getr r 9 = Z_to_bv 64 (T + 208) /\ getr r 18 = Z_to_bv 64 0x103f18 /\ getr r 19 = Z_to_bv 64 c /\ getr r 20 = Z_to_bv 64 pz
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rcnt Rmx HokT Hstk Hmx Hc HT HS H20 H19 H18 H9 H8 H13 H12 H11 H10 H2 H1.
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2 & HT16). unfold hideW in HT2. destruct dlf_facts as (Hn & Hcn & Hdm).
    assert (Vmx : bytes_le_to_Z (LE4 mx) = bv_unsigned (Z_to_bv 64 mx)) by (apply bytes4_small; lia).
    wd_eexists. split.
    - an F_4e230 D_4e230.                              (* [comment removed for export] *)
      fsd F_4e234 D_4e234 (at_ S (-2408)).
      fsd F_4e238 D_4e238 (at_ S (-2416)).
      fsd F_4e23c D_4e23c (at_ S (-2424)).
      fsd F_4e240 D_4e240 (at_ S (-2432)).
      fsd F_4e244 D_4e244 (at_ S (-2440)).
      fsd F_4e248 D_4e248 (at_ S (-2448)).
      ab_ft F_4e24c D_4e24c ltac:(condz).              (* [comment removed for export] *)
      an F_4e250 D_4e250.                              (* [comment removed for export] *)
      ab_ft F_4e254 D_4e254 ltac:(condz).              (* [comment removed for export] *)
      an F_4e258 D_4e258.                              (* [comment removed for export] *)
      av F_4e25c D_4e25c (Z_to_bv 64 (80 * c)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_mul in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_4e260 D_4e260 (Z_to_bv 64 pc_) ltac:(valz).  (* [comment removed for export] *)
      clw F_4e264 D_4e264 (LE4 mx) (Z_to_bv 64 mx) Rmx Vmx.       (* [comment removed for export] *)
      rewrite (v_lw_small mx) by lia.
      ab_ft F_4e268 D_4e268 ltac:(condz).              (* [comment removed for export] *)
      clw F_4e26c D_4e26c (LE4 mx) (Z_to_bv 64 mx) Rcnt Vmx.      (* [comment removed for export] *)
      rewrite (v_lw_small mx) by lia.
      ab_tk F_4e270 D_4e270 ltac:(condz).              (* [comment removed for export] *)
      an F_4e3c0 D_4e3c0.                              (* [comment removed for export] *)
      an F_4e3c4 D_4e3c4.                              (* [comment removed for export] *)
      an F_4e3c8 D_4e3c8.                              (* [comment removed for export] *)
      an F_4e3cc D_4e3cc.                              (* [comment removed for export] *)
      an F_4e3d0 D_4e3d0.                              (* [comment removed for export] *)
      an F_4e3d4 D_4e3d4.                              (* [comment removed for export] *)
      an F_4e3d8 D_4e3d8.                              (* [comment removed for export] *)
      an F_4e3dc D_4e3dc.                              (* [comment removed for export] *)
      an F_4e5c4 D_4e5c4.                              (* [comment removed for export] *)
      fsd F_4e5c8 D_4e5c8 (at_ S (-2456)).             (* [comment removed for export] *)
      fsd F_4e5cc D_4e5cc (at_ S (-2472)).             (* [comment removed for export] *)
      fsd F_4e5d0 D_4e5d0 (at_ S (-2464)).             (* [comment removed for export] *)
      clw F_4e5d4 D_4e5d4 (LE4 mx) (Z_to_bv 64 mx) Rcnt Vmx.      (* [comment removed for export] *)
      rewrite (v_lw_small mx) by lia.
      clwu F_4e5d8 D_4e5d8 (LE4 mx) (Z_to_bv 64 mx) Rmx Vmx.      (* [comment removed for export] *)
      fsd F_4e5dc D_4e5dc (at_ S (-2504)).             (* [comment removed for export] *)
      fsd F_4e5e0 D_4e5e0 (at_ S (-2496)).
      fsd F_4e5e4 D_4e5e4 (at_ S (-2488)).
      fsd F_4e5e8 D_4e5e8 (at_ S (-2480)).
      av F_4e5ec D_4e5ec (Z_to_bv 64 (mx / 2)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 1)%Z with 2%Z; unorm; reflexivity).   (* [comment removed for export] *)
      av F_4e5f0 D_4e5f0 (Z_to_bv 64 (mx * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      av F_4e5f4 D_4e5f4 (Z_to_bv 64 mx) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite Hdm; unorm; reflexivity).   (* [comment removed for export] *)
      ab_ft F_4e5f8 D_4e5f8 ltac:(condz).              (* [comment removed for export] *)
      av F_4e5fc D_4e5fc (Z_to_bv 64 (mx - mx / 2)) ltac:(valz).   (* [comment removed for export] *)
      an F_4e600 D_4e600.                              (* [comment removed for export] *)
      fsw F_4e604 D_4e604 (Z_to_bv 64 pc_).            (* [comment removed for export] *)
      an F_4e608 D_4e608.                              (* [comment removed for export] *)
      av F_4e60c D_4e60c (Z_to_bv 64 (4 * (mx - mx / 2))) ltac:(valz).   (* [comment removed for export] *)
      av F_4e610 D_4e610 (Z_to_bv 64 (pc_ + 4 * (mx - mx / 2))) ltac:(valz).   (* [comment removed for export] *)
      av F_4e614 D_4e614 (Z_to_bv 64 (pc_ + 16 + 4 * (mx - mx / 2))) ltac:(valz).   (* [comment removed for export] *)
      an F_4e618 D_4e618.                              (* [comment removed for export] *)
      an F_4e61c D_4e61c.                              (* [comment removed for export] *)
      an F_4e620 D_4e620.                              (* [comment removed for export] *)
      an F_4e624 D_4e624.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with M1. wd_refl.
    - post.
  Qed.
End DLFHEAD.

(* [comment removed for export] *)
Definition fr_dtl (mem : word -> option byte) (S : word) (T c cnt' e : Z) (stw : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2520)) (LE8 (Z_to_bv 64 0x4e640)))
    (at_ S (-2528)) (LE8 (Z_to_bv 64 (T + 208 + 80 * c))))
    (at_ S (-2536)) (LE8 (Z_to_bv 64 (T + 208))))
    (at_ S (-2544)) (LE8 (Z_to_bv 64 0x103f18)))
    (Z_to_bv 64 (T + 208 + 80 * c)) (LE4 (cnt' + 1)))
    (Z_to_bv 64 (T + 208 + 80 * c + 16 + 4 * cnt')) (LE4 (e / 16)))
    (Z_to_bv 64 (T + 2784)) (LE8 stw).
#[local] Hint Unfold fr_dtl : asfr.

Section DLFTAIL.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v s3v s4v : word) (T spb c e cnt' : Z) (bst bcs : list byte).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation pc_ := (T + 208 + 80 * c)%Z.
  Hypothesis H2 : getr regs 2 = at_ S (-2512).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 pc_.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 (T + 208).
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 0x103f18.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 c.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 (spb + c * 2 ^ 32 + e).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584) /\ T mod 16 = 0)%Z.
  Hypothesis Hspb : (0 <= spb /\ spb + 2 ^ 37 < 2 ^ 47)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis He : (0 <= e < 2 ^ 32)%Z.
  Hypothesis Hcnt : (0 <= cnt' < 16)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Lbst : length bst = 8%nat.
  Hypothesis Lbcs : length bcs = 8%nat.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2560)) 48 = true.
  Hypothesis HokT : store_ok ASEGS mem (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis Rb0 : rdn ASEGS mem (at_ S (-2480)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Rb1 : rdn ASEGS mem (at_ S (-2472)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Rdra : rdn ASEGS mem (at_ S (-2456)) 8 = Some (LE8 (Z_to_bv 64 0x4e3e8)).
  Hypothesis Cra : rdn ASEGS mem (at_ S (-2408)) 8 = Some (LE8 ra0).
  Hypothesis Cs0 : rdn ASEGS mem (at_ S (-2416)) 8 = Some (LE8 s0v).
  Hypothesis Cs1 : rdn ASEGS mem (at_ S (-2424)) 8 = Some (LE8 s1v).
  Hypothesis Cs2 : rdn ASEGS mem (at_ S (-2432)) 8 = Some (LE8 s2v).
  Hypothesis Cs3 : rdn ASEGS mem (at_ S (-2440)) 8 = Some (LE8 s3v).
  Hypothesis Cs4 : rdn ASEGS mem (at_ S (-2448)) 8 = Some (LE8 s4v).
  Hypothesis Rcnt : rdn ASEGS mem (Z_to_bv 64 pc_) 4 = Some (LE4 cnt').
  Hypothesis Rcs : rdn ASEGS mem (Z_to_bv 64 (pc_ + 8)) 8 = Some bcs.
  Hypothesis Rst : rdn ASEGS mem (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis Rspb : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 32)) 8 = Some (LE8 (Z_to_bv 64 spb)).

  #[local] Abbreviation stw := (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (v_sub (Z_to_bv 64 0) (Z_to_bv 64 (bytes_le_to_Z bcs)))).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma dtl_facts : (cnt' * 2 ^ 32 / 2 ^ 30 = 4 * cnt' /\ (T + 2784) mod 8 = 0)%Z.
  Proof using Lbcs Lbst Hcnt He HT bcs bst e s4v S rom. destruct HT as (_ & _ & T16). split; [| lia]. replace (cnt' * 2 ^ 32)%Z with (4 * cnt' * 2 ^ 30)%Z by lia. rewrite Z.div_mul by lia. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Lemma drn_dlf_tail :
    exists r, msteps ASEGS (mkst regs (0x4e630 : word) mem rom) (mkst r ra0 (fr_dtl mem S T c cnt' e stw) rom)
      /\ getr r 2 = at_ S (-2400) /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Rspb Rst Rcs Rcnt Cs4 Cs3 Cs2 Cs1 Cs0 Cra Rdra Rb1 Rb0 HokT Hstk Lbcs Lbst Hret Hcnt He Hc Hspb HT HS H20 H19 H18 H9 H8 H2 spb.
    pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2 & HT16). unfold hideW in HT2. destruct dtl_facts as [Hc4 Hal8].
    pose proof (bytes_le_to_Z_bound bst) as Bst. rewrite Lbst in Bst. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bst.
    pose proof (bytes_le_to_Z_bound bcs) as Bcs. rewrite Lbcs in Bcs. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bcs.
    pose proof (bytes_le_to_Z_nonneg bst) as Bst'. pose proof (bytes_le_to_Z_nonneg bcs) as Bcs'.
    assert (Vst : bytes_le_to_Z bst = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bst))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcs : bytes_le_to_Z bcs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bcs))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcnt : bytes_le_to_Z (LE4 cnt') = bv_unsigned (Z_to_bv 64 cnt')) by (apply bytes4_small; lia).
    wd_eexists. split.
    - cld8 F_4e628 D_4e628 (Z_to_bv 64 0) Rb0.         (* [comment removed for export] *)
      cld8 F_4e62c D_4e62c (Z_to_bv 64 0) Rb1.         (* [comment removed for export] *)
      an F_4e630 D_4e630.                              (* [comment removed for export] *)
      an F_4e634 D_4e634.                              (* [comment removed for export] *)
      an F_81f80 D_81f80.                              (* [comment removed for export] *)
      fsd F_81f84 D_81f84 (at_ S (-2520)).             (* [comment removed for export] *)
      fsd F_81f88 D_81f88 (at_ S (-2528)).             (* [comment removed for export] *)
      fsd F_81f8c D_81f8c (at_ S (-2536)).             (* [comment removed for export] *)
      fsd F_81f90 D_81f90 (at_ S (-2544)).             (* [comment removed for export] *)
      ab_tk F_81f94 D_81f94 ltac:(condz).              (* [comment removed for export] *)
      fld F_81fd0 D_81fd0 (Z_to_bv 64 0x4e640).        (* [comment removed for export] *)
      fld F_81fd4 D_81fd4 (Z_to_bv 64 pc_).            (* [comment removed for export] *)
      fld F_81fd8 D_81fd8 (Z_to_bv 64 (T + 208)).      (* [comment removed for export] *)
      fld F_81fdc D_81fdc (Z_to_bv 64 0x103f18).       (* [comment removed for export] *)
      an F_81fe0 D_81fe0.                              (* [comment removed for export] *)
      aret F_81fe4 D_81fe4 (Z_to_bv 64 0x4e640).       (* [comment removed for export] *)
      cld8 F_4e638 D_4e638 (Z_to_bv 64 0x4e3e8) Rdra.  (* [comment removed for export] *)
      an F_4e63c D_4e63c.                              (* [comment removed for export] *)
      aret F_4e640 D_4e640 (Z_to_bv 64 0x4e3e8).       (* [comment removed for export] *)
      an F_4e3e0 D_4e3e0.                              (* [comment removed for export] *)
      an F_4e3e4 D_4e3e4.                              (* [comment removed for export] *)
      an F_4e3e8 D_4e3e8.                              (* [comment removed for export] *)
      an F_4e3ec D_4e3ec.                              (* [comment removed for export] *)
      clw F_4e3f0 D_4e3f0 (LE4 cnt') (Z_to_bv 64 cnt') Rcnt Vcnt.   (* [comment removed for export] *)
      rewrite (v_lw_small cnt') by lia.
      an F_4e3f4 D_4e3f4.                              (* [comment removed for export] *)
      cld8 F_4e274 D_4e274 (Z_to_bv 64 spb) Rspb.      (* [comment removed for export] *)
      av F_4e278 D_4e278 (Z_to_bv 64 (c * 2 ^ 32)) ltac:(apply cls_shl32; lia).   (* [comment removed for export] *)
      av F_4e27c D_4e27c (Z_to_bv 64 (spb + e)) ltac:(valz).      (* [comment removed for export] *)
      av F_4e280 D_4e280 (Z_to_bv 64 (cnt' * 2 ^ 32)) ltac:(valz). (* [comment removed for export] *)
      av F_4e284 D_4e284 (Z_to_bv 64 (cnt' + 1)) ltac:(valz).      (* [comment removed for export] *)
      av F_4e288 D_4e288 (Z_to_bv 64 e) ltac:(valz).   (* [comment removed for export] *)
      cld F_4e28c D_4e28c bcs (Z_to_bv 64 (bytes_le_to_Z bcs)) Rcs Vcs.   (* [comment removed for export] *)
      an F_4e290 D_4e290.                              (* [comment removed for export] *)
      av F_4e294 D_4e294 (Z_to_bv 64 (4 * cnt')) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite <- Hc4; unorm; reflexivity).   (* [comment removed for export] *)
      av F_4e298 D_4e298 (Z_to_bv 64 (T + 2784)) ltac:(valz).     (* [comment removed for export] *)
      av F_4e29c D_4e29c (Z_to_bv 64 (pc_ + 4 * cnt')) ltac:(valz).   (* [comment removed for export] *)
      av F_4e2a0 D_4e2a0 (Z_to_bv 64 (e / 16)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; reflexivity).   (* [comment removed for export] *)
      fsw F_4e2a4 D_4e2a4 (Z_to_bv 64 pc_).            (* [comment removed for export] *)
      fsw F_4e2a8 D_4e2a8 (Z_to_bv 64 (pc_ + 16 + 4 * cnt')).   (* [comment removed for export] *)
      an F_4e2ac D_4e2ac.                              (* [comment removed for export] *)
      famoA F_4e2b0 D_4e2b0 bst (Z_to_bv 64 (bytes_le_to_Z bst)) Rst Vst.   (* [comment removed for export] *)
      cld8 F_4e2b4 D_4e2b4 ra0 Cra. cld8 F_4e2b8 D_4e2b8 s0v Cs0. cld8 F_4e2bc D_4e2bc s1v Cs1. cld8 F_4e2c0 D_4e2c0 s2v Cs2.
      cld8 F_4e2c4 D_4e2c4 s3v Cs3. cld8 F_4e2c8 D_4e2c8 s4v Cs4.
      an F_4e2cc D_4e2cc.                              (* [comment removed for export] *)
      aret F_4e2d0 D_4e2d0 ra0.                        (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_dtl mem S T c cnt' e stw). wd_refl.
    - post.
  Qed.
End DLFTAIL.
End FPGen.
