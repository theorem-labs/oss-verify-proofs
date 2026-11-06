(** The inlined pod_nearest(f, 0, 255) of the plain LLVMFuzzerTestOneInput (0x14548 -> 0x145e8 / 0x1464c, cell_value
    at fuzz_headamp.c:105, pod.h:152-171): proof of [near_stmt] (Prog/HeadCheck/Cut.v) from the contracts of its
    soft-float callees (__extendsftf2, __floatditf, __subtf3 with __addtf3, __getf2, __lttf2 = __cmptf2).

    The walk [body] steps the instructions from 0x1454c with this library's tactics, reaches the callees through
    the bridge from the CJ library's evt (CJBridge.v; [br_ext], [br_fd], [br_sub], [br_ge], [br_le], fuzz_role's
    Prog/pod_nearest.v with the image's addresses) and ends at the continuation with the machine model [hn_bin b]
    (Prog/HeadCheck/NearVal.v); [near_holds] adds the load 0x14548 `flw fs0,8(a0)` and turns [hn_bin] into
    [nearest] with [hn_bin_nearest]. The code keeps d, frac and t / r in the frame cells [sp + 0x30, sp + 0x48)
    (low word at sp + 0x38, high word at sp + 0x30, t / r at sp + 0x40), reads 0.5L / -0.5L's high words at
    sp + 0x60 / sp + 0x50, and has no frame of its own; __subtf3 / __addtf3 use the 48 bytes below sp. *)
From Stdlib Require Import ZArith NArith List Lia Bool SpecFloat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.Spec Require SoftFloat.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require C_extendsftf2 C_floatditf.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Nearest.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import NearVal.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr Decode DecodeC.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0 CJBridge.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require G_letf2 G_getf2 G_subtf3.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.I Require IImgP.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import LLVMFuzzerTestOneInput_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadCheck Require Import Facts Cut.
Import ListNotations.
Open Scope Z_scope.

(** ** Single-precision values in the 64-bit FP registers *)
Lemma lor_shift_add : forall a v n, 0 <= n -> 0 <= v < 2^n -> Z.lor (a * 2^n) v = a * 2^n + v.
Proof.
  intros a v n Hn Hv.
  assert (L : Z.land (a * 2^n) v = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i n) as [H|H].
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite <- (Z.mod_small v (2^n)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- Z.lxor_lor by exact L. rewrite Z.add_nocarry_lxor by exact L. reflexivity.
Qed.

Lemma u32_lit : forall z, 0 <= z < 2^32 -> bv_unsigned (Z_to_bv 32 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus.
  change (2 ^ Z.of_N 32) with (2^32). lia.
Qed.

Lemma nan_box_unsigned : forall v : bv 32, bv_unsigned (nan_box v) = 4294967295 * 2^32 + bv_unsigned v.
Proof.
  intros v. unfold nan_box. rewrite bv_concat_unsigned by reflexivity.
  pose proof (bv_unsigned_in_range 32 v) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 32) with (2^32) in R.
  replace (bv_unsigned (Z_to_bv 32 (-1))) with 4294967295 by (vm_compute; reflexivity).
  change (Z.of_N 32) with 32. rewrite Z.shiftl_mul_pow2 by lia. apply lor_shift_add; lia.
Qed.

Lemma unbox_nan_box : forall v : bv 32, unbox_s (nan_box v) = v.
Proof.
  intros v. pose proof (bv_unsigned_in_range 32 v) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 32) with (2^32) in R.
  unfold unbox_s, low32. rewrite bv_extract_unsigned, nan_box_unsigned. change (Z.of_N 32) with 32.
  rewrite Z.shiftr_div_pow2 by lia.
  replace ((4294967295 * 2^32 + bv_unsigned v) / 2^32) with 4294967295
    by (rewrite Z.div_add_l by lia; rewrite (Z.div_small (bv_unsigned v)) by lia; lia).
  replace (bv_wrap 32 4294967295 =? Z.ones 32) with true by (vm_compute; reflexivity).
  apply bv_eq. rewrite bv_extract_unsigned, nan_box_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  unfold bv_wrap. change (bv_modulus 32) with (2^32).
  rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma sgnj_self32 : forall v : bv 32, sgnj_val F_SGNJ v v = v.
Proof.
  intros v. pose proof (bv_unsigned_in_range 32 v) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 32) with (2^32) in R.
  apply bv_eq. unfold sgnj_val, bit. cbv zeta.
  rewrite bv_concat_unsigned by reflexivity.
  rewrite bv_extract_unsigned, Z_to_bv_unsigned. change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r.
  change (Z.of_N (32 - 1)) with 31.
  unfold bv_wrap. change (bv_modulus (32 - 1)) with (2^31). change (bv_modulus 1) with 2.
  apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i 31) as [H1|H1].
  - rewrite Z.shiftl_spec_low by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia. rewrite orb_false_r. rewrite Z.shiftl_spec by lia.
    destruct (Z.eqb_spec i 31) as [->|Hne].
    + destruct (Z.testbit (bv_unsigned v) 31); reflexivity.
    + assert (Hi31 : 0 < i - 31) by lia.
      assert (Hv : Z.testbit (bv_unsigned v) i = false).
      { rewrite <- (Z.mod_small (bv_unsigned v) (2^32)) by lia. apply Z.mod_pow2_bits_high. lia. }
      rewrite Hv. destruct (Z.testbit (bv_unsigned v) 31).
      * change ((if true then 1 else 0) mod 2) with 1.
        apply Z.bits_above_log2; [apply Z.le_0_1 | change (Z.log2 1) with 0; exact Hi31].
      * change ((if false then 1 else 0) mod 2) with 0. apply Z.bits_0.
Qed.

Lemma reg_get_key : forall (R : bvmap 5 word) (r r' : bv 5),
  bv_unsigned r = bv_unsigned r' -> Sem.reg_get R r = Sem.reg_get R r'.
Proof. intros R r r' E. apply bv_eq in E. subst. reflexivity. Qed.

(** Rewrite every read of the FP register file [F] at index [k] with the hypothesis [HF] about index [k]. *)
Ltac fix_reg F HF k :=
  repeat match goal with
  | |- context [Sem.reg_get F ?r] =>
      let z := eval vm_compute in (bv_unsigned r) in
      lazymatch z with
      | k => rewrite (reg_get_key F r (Z_to_bv 5 k) eq_refl), HF
      end
  end.

(** ** The soft-float callees, through the bridge from the CJ library's evt to this library's *)
Lemma br_ext : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x200dc = pc ->
  @C_extendsftf2.extendsftf2_contract I ->
  forall (b : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  Sem.reg_get F (Z_to_bv 5 10) = nan_box (Z_to_bv 32 b) ->
  mem_inv segs m -> MemNorm.task_mem segs m ->
  evt segs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (SF.lo64 (f128_of_f32 (fbox b))))
                    (Z_to_bv 64 (SF.hi64 (f128_of_f32 (fbox b)))) a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom segs) /\
      munch [] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ MemNorm.task_mem segs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
  intros I segs pc HI Hpc H b ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m HF MI TM.
  subst segs pc.
  pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                (mem_inv_to_cj _ m MI TM)) as E.
  refine (evt_bridge _ _ _ _ _ E).
  intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms & MU & WM & MI').
  destruct (mem_inv_of_cj _ m' MI') as [MI2 TM2].
  exists t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  refine (conj _ (conj MU (conj WM (conj MI2 TM2)))).
  rewrite Hms. fix_reg F HF 10%Z. reflexivity.
Qed.

Lemma br_le : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x1b24c = pc ->
  @G_letf2.letf2_contract I ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv segs m -> MemNorm.task_mem segs m ->
  evt segs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                    (Z_to_bv 64 (SF.f128_le (bv_unsigned a0 + 2^64 * bv_unsigned a1)
                                             (bv_unsigned a2 + 2^64 * bv_unsigned a3)))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom segs) /\
      munch [] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ MemNorm.task_mem segs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
  intros I segs pc HI Hpc H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m MI TM.
  subst segs pc.
  pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                (mem_inv_to_cj _ m MI TM)) as E.
  refine (evt_bridge _ _ _ _ _ E).
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms & MU & WM
              & MI').
  destruct (mem_inv_of_cj _ m' MI') as [MI2 TM2].
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  exact (conj Hms (conj MU (conj WM (conj MI2 TM2)))).
Qed.

Lemma br_ge : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x1b314 = pc ->
  @G_getf2.getf2_contract I ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv segs m -> MemNorm.task_mem segs m ->
  evt segs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                    (Z_to_bv 64 (SF.f128_ge (bv_unsigned a0 + 2^64 * bv_unsigned a1)
                                             (bv_unsigned a2 + 2^64 * bv_unsigned a3)))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom segs) /\
      munch [] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ MemNorm.task_mem segs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
  intros I segs pc HI Hpc H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m MI TM.
  subst segs pc.
  pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                (mem_inv_to_cj _ m MI TM)) as E.
  refine (evt_bridge _ _ _ _ _ E).
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms & MU & WM
              & MI').
  destruct (mem_inv_of_cj _ m' MI') as [MI2 TM2].
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  exact (conj Hms (conj MU (conj WM (conj MI2 TM2)))).
Qed.

Lemma br_fd : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x7f000900 = pc ->
  @C_floatditf.floatditf_contract I ->
  forall (t : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  bv_unsigned a0 = SF.wrap64 t -> mem_inv segs m -> MemNorm.task_mem segs m ->
  evt segs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (SF.lo64 (f128_of_i64 t)))
                    (Z_to_bv 64 (SF.hi64 (f128_of_i64 t))) a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom segs) /\
      munch [] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ MemNorm.task_mem segs m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
  intros I segs pc HI Hpc H t ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 F fc m Ht MI TM.
  subst segs pc.
  pose proof (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m t
                (mem_inv_to_cj _ m MI TM) Ht) as E.
  refine (evt_bridge _ _ _ _ _ E).
  intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Hms & MU & WM & MI').
  destruct (mem_inv_of_cj _ m' MI') as [MI2 TM2].
  exists t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  exact (conj Hms (conj MU (conj WM (conj MI2 TM2)))).
Qed.

(** __subtf3 (and the __addtf3 it jumps to) uses the 48 bytes below its sp and rounds with frm. *)
Lemma br_sub : forall (I : RStep.RImg) segs pc, @RStep.img_segs I = segs -> @RStep.sym I 0x1bc70 = pc ->
  @G_subtf3.subtf3_contract I ->
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (S : Z) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  48 <= S < 2^64 -> stk segs m (S - 48) S -> mem_inv segs m -> MemNorm.task_mem segs m -> frm0 fc ->
  evt segs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (fc' : bv 32)
                              (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1
                    (Z_to_bv 64 (SF.lo64 (SF.f128_sub (bv_unsigned a0 + 2^64 * bv_unsigned a1)
                                                      (bv_unsigned a2 + 2^64 * bv_unsigned a3))))
                    (Z_to_bv 64 (SF.hi64 (SF.f128_sub (bv_unsigned a0 + 2^64 * bv_unsigned a1)
                                                      (bv_unsigned a2 + 2^64 * bv_unsigned a3))))
                    a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc' None m' (seg_rom segs) /\
      munch [(S - 48, S)] m m' /\ wmono segs m m' /\ mem_inv segs m' /\ MemNorm.task_mem segs m' /\
      frm0 fc' /\ stk segs m' (S - 48) S)
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom segs)).
Proof.
  intros I segs pc HI Hpc H ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    t3 t4 t5 t6 S F fc m HSr ST MI TM FRM.
  subst segs pc.
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (ST' : CJ.Lib.Frame.stk (@RStep.img_segs I) m (bv_unsigned (Z_to_bv 64 S) - 48) (bv_unsigned (Z_to_bv 64 S)))
    by (rewrite ES; exact ST).
  pose proof (H ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                t3 t4 t5 t6 F fc m ST' (mem_inv_to_cj _ m MI TM) FRM) as E.
  refine (evt_bridge _ _ _ _ _ E).
  intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & fc' & m' & Hms & MU & WM
              & MI' & FRM' & ST2).
  rewrite ES in MU, ST2.
  destruct (mem_inv_of_cj _ m' MI') as [MI2 TM2].
  exists t0', t1', t2', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', fc', m'.
  exact (conj Hms (conj MU (conj WM (conj MI2 (conj TM2 (conj FRM' ST2)))))).
Qed.

(** ** Register-level facts the walk uses *)
Lemma u_lo64 : forall x, bv_unsigned (Z_to_bv 64 (SF.lo64 x)) = SF.lo64 x.
Proof. intros x. apply unsigned_lit. apply SF.wrap64_range. Qed.

Lemma u_hi64 : forall x, bv_unsigned (Z_to_bv 64 (SF.hi64 x)) = SF.hi64 x.
Proof. intros x. apply unsigned_lit. apply SF.wrap64_range. Qed.

Lemma f128_le_range : forall a c, -1 <= SF.f128_le a c <= 1.
Proof.
  intros a c. unfold SF.f128_le, SF.nez64, SF.b2z. cbv zeta.
  repeat match goal with |- context [if ?x then _ else _] => destruct x end; lia.
Qed.

Lemma f128_ge_range : forall a c, -1 <= SF.f128_ge a c <= 1.
Proof.
  intros a c. unfold SF.f128_ge, SF.nez64, SF.b2z. cbv zeta.
  repeat match goal with |- context [if ?x then _ else _] => destruct x end; lia.
Qed.

(** bltz / bgez on a comparison result in {-1, 0, 1}. *)
Lemma lts0 : forall v, -1 <= v <= 1 -> bv_lts (Z_to_bv 64 v) (Z_to_bv 64 0) = (v <? 0).
Proof.
  intros v Hv. assert (C : v = -1 \/ v = 0 \/ v = 1) by lia.
  destruct C as [ -> | [ -> | -> ] ]; vm_compute; reflexivity.
Qed.

Lemma reg_get_set_ne : forall (R : bvmap 5 word) (k r : bv 5) v,
  bv_unsigned k <> bv_unsigned r -> Sem.reg_get (bvmap_set k v R) r = Sem.reg_get R r.
Proof. intros R k r v H. apply freg_get_other. unfold bv_eqb. apply Z.eqb_neq. exact H. Qed.

Lemma bv_mod_lit : forall x, Z_to_bv 64 (x mod 2^64) = Z_to_bv 64 x.
Proof. intros x. apply Z_to_bv_eqm. apply Z.mod_mod. lia. Qed.

(** The FP registers the piece writes (fs0 = f8, fa0 = f10) leave every other one as it was. *)
Ltac hfc :=
  let k := fresh "k" in let H8 := fresh "H8" in let H10 := fresh "H10" in
  intros k H8 H10;
  repeat (rewrite reg_get_set_ne;
          [ | let E := fresh "E" in intro E;
              first [ apply H8; rewrite <- E; reflexivity | apply H10; rewrite <- E; reflexivity ] ]);
  reflexivity.

(** fcvt.l.s, which the walk library's exec lemmas leave out. *)
Lemma exec_fcvt_l_s : forall sz rd rs1 rm c md, rmode_of_field (bv_unsigned rm) (frm_of c) = Some md ->
  exec sz (Fcvt FC_L FC_S rd rs1 rm) c =
  EDone (rset rd (Z_to_bv 64 (fst (fp_to_int fmt_single md true 64 (bv_unsigned (unbox_s (fget c rs1))))))
          (accrue (snd (fp_to_int fmt_single md true 64 (bv_unsigned (unbox_s (fget c rs1)))))
                  (with_pc (c_pc c + sz) c))).
Proof. intros until md; intros H. fcvt_tac H. Qed.

Local Ltac OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib.Step.exec_pre i ::=
  lazymatch goal with
  | |- context [exec ?sz _ ?c] =>
    lazymatch i with
    | Fcvt FC_L FC_S ?rd ?rs1 ?rm => let H := rm_proof rm c in rewrite (exec_fcvt_l_s sz rd rs1 rm c _ H)
    | Fcmp ?op FMT_S ?rd ?rs1 ?rs2 => rewrite (exec_fcmp_s sz op rd rs1 rs2 c)
    | _ => idtac
    end
  end;
  try match goal with
  | FRM : frm0 ?f |- context [slice_get ?f' 5 3] => constr_eq f f'; rewrite (frm0_slice_get f FRM)
  end.

(** Fold the closed second operand of a binary128 compare into the named constant [c]. *)
Ltac fold_c128 c :=
  repeat match goal with
  | |- context [SF.f128_le ?x ?y] =>
      let v := eval vm_compute in y in let w := eval vm_compute in c in constr_eq v w;
      lazymatch y with c => fail | _ => replace y with c by (vm_compute; reflexivity) end
  | |- context [SF.f128_ge ?x ?y] =>
      let v := eval vm_compute in y in let w := eval vm_compute in c in constr_eq v w;
      lazymatch y with c => fail | _ => replace y with c by (vm_compute; reflexivity) end
  end.

Lemma W128_def : forall x, SF.lo64 x + 2^64 * SF.hi64 x = W128 x.
Proof. reflexivity. Qed.
Lemma pn_d_def : forall b, W128 (f128_of_f32 (fbox b)) = pn_d b.
Proof. reflexivity. Qed.
Lemma pn_t_def : forall b, fst (fp_to_int fmt_single RTZ true 64 b) = pn_t b.
Proof. reflexivity. Qed.

(** [hn_bin] at the exits. *)
Lemma hn_eq : forall b X, fst (fp_eq fmt_single b b) = true -> fst (fp_lt fmt_single b 0xbf800000) = false ->
  fst (fp_lt fmt_single 0x43800000 b) = false -> pn_r b = X ->
  hn_bin b = (if 255 <? X mod 2^64 then None else Some (X mod 2^64)).
Proof. intros b X H1 H2 H3 H4. unfold hn_bin. rewrite H1, H2, H3, H4. reflexivity. Qed.

(** ** The walk *)
Section Walk.
Variables (Q : machine_state -> Prop) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
  (m0 : word -> option byte) (b Sp lo : Z).
Hypothesis HEX : @C_extendsftf2.extendsftf2_contract IImgP.N_img.
Hypothesis HFD : @C_floatditf.floatditf_contract IImgP.N_img.
Hypothesis HSB : @G_subtf3.subtf3_contract IImgP.N_img.
Hypothesis HGE : @G_getf2.getf2_contract IImgP.N_img.
Hypothesis HLE : @G_letf2.letf2_contract IImgP.N_img.
Hypothesis Hb : 0 <= b < 2^32.
(** fs0 = f after 0x14548 `flw fs0,8(a0)`; fs1 = -1.0f, fs2 = 256.0f. *)
Hypothesis HF8 : Sem.reg_get F (Z_to_bv 5 8) = Sem.nan_box (Z_to_bv 32 b).
Hypothesis HF9 : Sem.reg_get F (Z_to_bv 5 9) = Sem.nan_box (Z_to_bv 32 F32_M1).
Hypothesis HF18 : Sem.reg_get F (Z_to_bv 5 18) = Sem.nan_box (Z_to_bv 32 F32_256).
Hypothesis Hlo : 0 <= lo.
Hypothesis HLO : lo + 48 <= Sp.
Hypothesis HSpT : Sp + 0x1b0 <= 2^64.

(** The bytes the piece may change: the soft-float stack below sp and the frame cells d / frac / t / r. *)
Definition NW : list ivl := [(Sp - NEAR_STACK, Sp); (Sp + 0x30, Sp + 0x48)].

(** The exits, with the machine model [hn_bin b] in place of [nearest]. *)
Hypothesis K : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word)
    (fc' : bv 32) (m' : word -> option byte),
  frm0 fc' ->
  (forall k : bv 5, bv_unsigned k <> 8 -> bv_unsigned k <> 10 -> Sem.reg_get F' k = Sem.reg_get F k) ->
  munch NW m0 m' -> wmono rsegs m0 m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
  stk rsegs m' lo (Sp + FRAME_LOCALS) ->
  match hn_bin b with
  | Some n =>
      bytes_at rsegs m' (Sp + 0x40) (le8 (Z_to_bv 64 n)) ->
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F' (Z_to_bv 64 0x145e8) fc' None m' (seg_rom rsegs))
  | None =>
      evt rsegs Q
        (MS (mkR ra' (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
            F' (Z_to_bv 64 0x1464c) fc' None m' (seg_rom rsegs))
  end.

(** The memory the walk carries: changed only in [NW], the stack region present and writable, the 0.5L / -0.5L
    cells in place. *)
Definition MemN (m : word -> option byte) : Prop :=
  munch NW m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
  stk rsegs m lo (Sp + FRAME_LOCALS) /\
  bytes_at rsegs m (Sp + 0x60) (le8 (Z_to_bv 64 HALF_HI)) /\
  bytes_at rsegs m (Sp + 0x50) (le8 (Z_to_bv 64 MHALF_HI)).

Lemma MN_mi : forall m, MemN m -> mem_inv rsegs m.
Proof. intros m (_ & _ & H & _). exact H. Qed.
Lemma MN_tm : forall m, MemN m -> MemNorm.task_mem rsegs m.
Proof. intros m (_ & _ & _ & H & _). exact H. Qed.
Lemma MN_h60 : forall m, MemN m -> bytes_at rsegs m (Sp + 0x60) (le8 (Z_to_bv 64 HALF_HI)).
Proof. intros m (_ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma MN_h50 : forall m, MemN m -> bytes_at rsegs m (Sp + 0x50) (le8 (Z_to_bv 64 MHALF_HI)).
Proof. intros m (_ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma MN_stk48 : forall m, MemN m -> stk rsegs m (Sp - 48) Sp.
Proof.
  intros m (_ & _ & _ & _ & ST & _). unfold FRAME_LOCALS in ST.
  destruct (stk_split rsegs m lo (Sp - 48) (Sp + 0x1b0) ST ltac:(lia)) as [_ ST2].
  exact (proj1 (stk_split rsegs m (Sp - 48) Sp (Sp + 0x1b0) ST2 ltac:(lia))).
Qed.

(** A leaf callee writes nothing. *)
Lemma MN_call : forall m m', MemN m -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  MemNorm.task_mem rsegs m' -> MemN m'.
Proof.
  intros m m' (MU & WM & MI & TM & ST & H6 & H5) MU' WM' MI' TM'.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']]. intros x _. exact I.
  - exact (wmono_trans rsegs _ _ _ WM WM').
  - exact MI'.
  - exact TM'.
  - exact (stk_transport_disjoint rsegs [] m m' lo _ ST MU' WM' I).
  - exact (bytes_at_transport rsegs [] m m' _ _ H6 MU' I).
  - exact (bytes_at_transport rsegs [] m m' _ _ H5 MU' I).
Qed.

(** __subtf3 / __addtf3 write the 48 bytes below sp. *)
Lemma MN_sub : forall m m', MemN m -> munch [(Sp - 48, Sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
  MemNorm.task_mem rsegs m' -> stk rsegs m' (Sp - 48) Sp -> MemN m'.
Proof.
  intros m m' (MU & WM & MI & TM & ST & H6 & H5) MU' WM' MI' TM' ST'.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU']].
    unfold sub_fp, NW, NEAR_STACK. cbn [outside]. intros x (O1 & _ & _). split; [exact O1 | exact I].
  - exact (wmono_trans rsegs _ _ _ WM WM').
  - exact MI'.
  - exact TM'.
  - unfold FRAME_LOCALS in *.
    destruct (stk_split rsegs m lo (Sp - 48) (Sp + 0x1b0) ST ltac:(lia)) as [STa STb].
    destruct (stk_split rsegs m (Sp - 48) Sp (Sp + 0x1b0) STb ltac:(lia)) as [_ STc].
    pose proof (stk_transport_disjoint rsegs _ m m' lo (Sp - 48) STa MU' WM'
                  ltac:(cbn [disjoint_from]; split; [lia | exact I])) as STa'.
    pose proof (stk_transport_disjoint rsegs _ m m' Sp (Sp + 0x1b0) STc MU' WM'
                  ltac:(cbn [disjoint_from]; split; [lia | exact I])) as STc'.
    apply (stk_merge rsegs m' lo (Sp - 48)); [exact STa' | | lia].
    apply (stk_merge rsegs m' (Sp - 48) Sp); [exact ST' | exact STc' | lia].
  - apply (bytes_at_transport rsegs _ m m' _ _ H6 MU'). cbn [disjoint_from]. rewrite length_le8.
    split; [lia | exact I].
  - apply (bytes_at_transport rsegs _ m m' _ _ H5 MU'). cbn [disjoint_from]. rewrite length_le8.
    split; [lia | exact I].
Qed.

(** A store of 8 bytes into the frame cells [sp + 0x30, sp + 0x48). *)
Lemma MN_store_ok : forall m a, MemN m -> Sp + 0x30 <= a -> a + 8 <= Sp + 0x48 -> store_ok rsegs m (wa a) 8 = true.
Proof.
  intros m a (_ & _ & _ & _ & ST & _) H1 H2.
  apply (stk_store_ok rsegs m lo (Sp + FRAME_LOCALS) a 8 ST); unfold FRAME_LOCALS; lia.
Qed.

Lemma MN_store : forall m a (v : word), MemN m -> Sp + 0x30 <= a -> a + 8 <= Sp + 0x48 ->
  MemN (write_to_mem m (wa a) (le8 v)) /\ bytes_at rsegs (write_to_mem m (wa a) (le8 v)) a (le8 v).
Proof.
  intros m a v MN H1 H2. pose proof (MN_store_ok m a MN H1 H2) as HS.
  destruct MN as (MU & WM & MI & TM & ST & H6 & H5). unfold FRAME_LOCALS in *.
  assert (HS' : store_ok rsegs m (wa a) (length (le8 v)) = true) by (rewrite length_le8; exact HS).
  split; [split; [|split; [|split; [|split; [|split; [|split]]]]] |].
  - apply munch_write; [exact MU | lia | rewrite length_le8; lia |].
    unfold NW. cbn [inside]. rewrite length_le8. right; left; lia.
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI | exact HS'].
  - apply task_mem_write; [exact TM | exact HS'].
  - apply stk_write; [exact ST | lia | rewrite length_le8; lia].
  - apply bytes_at_write_other; [exact H6 | lia | rewrite length_le8; lia | rewrite !length_le8; lia].
  - apply bytes_at_write_other; [exact H5 | lia | rewrite length_le8; lia | rewrite !length_le8; lia].
  - apply bytes_at_write_same; [lia | rewrite length_le8; lia].
Qed.

(** A frame cell outside a store, a leaf callee or __subtf3's stack keeps its bytes. *)
Lemma D_store : forall m a (v w : word) c, bytes_at rsegs m c (le8 w) -> Sp + 0x30 <= a -> a + 8 <= Sp + 0x48 ->
  c + 8 <= a \/ a + 8 <= c -> bytes_at rsegs (write_to_mem m (wa a) (le8 v)) c (le8 w).
Proof.
  intros m a v w c H H1 H2 H3.
  apply bytes_at_write_other; [exact H | lia | rewrite length_le8; lia | rewrite !length_le8; lia].
Qed.

Lemma D_nil : forall m m' c bs, bytes_at rsegs m c bs -> munch [] m m' -> bytes_at rsegs m' c bs.
Proof. intros m m' c bs H MU. exact (bytes_at_transport rsegs [] m m' c bs H MU I). Qed.

Lemma D_sub : forall m m' c bs, bytes_at rsegs m c bs -> munch [(Sp - 48, Sp)] m m' -> Sp <= c ->
  bytes_at rsegs m' c bs.
Proof.
  intros m m' c bs H MU Hc. apply (bytes_at_transport rsegs _ m m' c bs H MU). cbn [disjoint_from].
  split; [lia | exact I].
Qed.

(** ** The exits 0x1464c (None) and 0x145e8 (Some n, n at sp + 0x40) *)
Lemma exit_none : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
  frm0 fc' -> (forall k : bv 5, bv_unsigned k <> 8 -> bv_unsigned k <> 10 -> Sem.reg_get F' k = Sem.reg_get F k) ->
  MemN m' -> hn_bin b = None ->
  evt rsegs Q
    (MS (mkR ra' (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F' (Z_to_bv 64 0x1464c) fc' None m' (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM HF
    (MU & WM & MI & TM & ST & _) HN.
  pose proof (K ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM HF MU WM MI TM ST) as KK.
  rewrite HN in KK. exact KK.
Qed.

Lemma exit_some : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
    (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte) (n : Z),
  frm0 fc' -> (forall k : bv 5, bv_unsigned k <> 8 -> bv_unsigned k <> 10 -> Sem.reg_get F' k = Sem.reg_get F k) ->
  MemN m' -> hn_bin b = Some n -> bytes_at rsegs m' (Sp + 0x40) (le8 (Z_to_bv 64 n)) ->
  evt rsegs Q
    (MS (mkR ra' (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
        F' (Z_to_bv 64 0x145e8) fc' None m' (seg_rom rsegs)).
Proof.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' n FRM HF
    (MU & WM & MI & TM & ST & _) HN HB.
  pose proof (K ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM HF MU WM MI TM ST) as KK.
  rewrite HN in KK. exact (KK HB).
Qed.

(** The memory and the hypotheses of the state in the goal. *)
Ltac cur_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => m end.
Ltac cur_mn m := lazymatch goal with H : MemN m |- _ => H end.

(** `sd` of a 64-bit word at the frame cell [A]: step, carry [MemN] and the other cells over, name the new memory. *)
Ltac nstore A :=
  let m := cur_mem in let MN := cur_mn m in
  let HS := fresh "HS" in
  pose proof (MN_store_ok m A MN ltac:(lia) ltac:(lia)) as HS; step; clear HS;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m ?AA (le8 ?V)) _) =>
    change (write_to_mem m AA (le8 V)) with (write_to_mem m (wa A) (le8 V));
    let MN' := fresh "MN" in let DD := fresh "D" in
    destruct (MN_store m A V MN ltac:(lia) ltac:(lia)) as [MN' DD];
    repeat match goal with
    | H : bytes_at rsegs m ?c (le8 ?w) |- _ =>
        let H' := fresh "D" in
        pose proof (D_store m A V w c H ltac:(lia) ltac:(lia) ltac:(lia)) as H'; clear H
    end;
    let m' := fresh "m" in
    set (m' := write_to_mem m (wa A) (le8 V)) in *; clearbody m'; first [clear dependent m | clear MN]
  end.

(** `ld` of the frame cell [A]. *)
Ltac nload A :=
  let m := cur_mem in
  match goal with
  | H : bytes_at rsegs m A (le8 ?w) |- _ =>
      let HR := fresh "HR" in pose proof (read_le8 rsegs m A w H) as HR; step; clear HR
  end.

(** After a leaf callee from memory [m] to [m']: carry [MemN] and the frame cells over. *)
Ltac npost m m' MU WM MI TM :=
  let MN := cur_mn m in
  let MN' := fresh "MN" in
  pose proof (MN_call m m' MN MU WM MI TM) as MN';
  repeat match goal with
  | H : bytes_at rsegs m ?c ?bs |- _ =>
      let H' := fresh "D" in pose proof (D_nil m m' c bs H MU) as H'; clear H
  end;
  first [clear dependent m | clear MN MU WM];
  rewrite ret_pc_even by (try lia; reflexivity).

(** ** 0x145dc: 255 < r unsigned goes to 0x1464c, else 0x145e8 *)
Lemma tail : forall (X : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte),
  frm0 fc -> MemN m -> bytes_at rsegs m (Sp + 0x40) (le8 (Z_to_bv 64 X)) ->
  (forall k : bv 5, bv_unsigned k <> 8 -> bv_unsigned k <> 10 -> Sem.reg_get F' k = Sem.reg_get F k) ->
  hn_bin b = (if 255 <? X mod 2^64 then None else Some (X mod 2^64)) ->
  evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F' (Z_to_bv 64 0x145dc) fc None m (seg_rom rsegs)).
Proof.
  intros X ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc m FRM MN D40 HF HN.
  (* 0x145dc addi a0,zero,0xff; ld a1,0x40(sp); bltu a0,a1 *)
  step. pose proof (read_le8 rsegs m (Sp + 0x40) _ D40) as HR. step. clear HR. step.
  match goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
    replace c with (255 <? X mod 2^64) by (unfold bv_ltu; rewrite ?unsigned_lit_wrap; reflexivity) end.
  destruct (255 <? X mod 2^64) eqn:BT; cbv iota.
  - eapply exit_none; [exact FRM | exact HF | exact MN | rewrite HN; try rewrite BT; reflexivity].
  - eapply exit_some; [exact FRM | exact HF | exact MN | rewrite HN; try rewrite BT; reflexivity |].
    rewrite bv_mod_lit. exact D40.
Qed.

(** ** 0x1454c .. 0x145dc *)
Lemma body : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32),
  frm0 fc -> MemN m0 ->
  evt rsegs Q
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1454c) fc None m0 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc FRM MN.
  (* 0x1454c feq.s a0,fs0,fs0; beqz a0 *)
  step. fix_reg F HF8 8%Z. unfold feq_s. rewrite unbox_nan_box, (u32_lit b Hb).
  destruct (fst (fp_eq fmt_single b b)) eqn:FE; unfold bword; step.
  2:{ (* a NaN *)
      if_true. eapply exit_none; [eassumption | intros k _ _; reflexivity | exact MN |].
      unfold hn_bin. rewrite FE. reflexivity. }
  if_false.
  (* 0x14554 flt.s a0,fs0,fs1; bnez a0 *)
  step. fix_reg F HF8 8%Z. fix_reg F HF9 9%Z. unfold flt_s.
  rewrite !unbox_nan_box, (u32_lit b Hb), (u32_lit F32_M1) by (unfold F32_M1; lia). unfold F32_M1.
  destruct (fst (fp_lt fmt_single b 0xbf800000)) eqn:LT1; unfold bword; step.
  { (* f < -1.0f *)
    if_true. eapply exit_none; [eassumption | intros k _ _; reflexivity | exact MN |].
    unfold hn_bin. rewrite FE, LT1. reflexivity. }
  if_false.
  (* 0x1455c flt.s a0,fs2,fs0; bnez a0 *)
  step. fix_reg F HF8 8%Z. fix_reg F HF18 18%Z. unfold flt_s.
  rewrite !unbox_nan_box, (u32_lit b Hb), (u32_lit F32_256) by (unfold F32_256; lia). unfold F32_256.
  destruct (fst (fp_lt fmt_single 0x43800000 b)) eqn:LT2; unfold bword; step.
  { (* 256.0f < f *)
    if_true. eapply exit_none; [eassumption | intros k _ _; reflexivity | exact MN |].
    unfold hn_bin. rewrite FE, LT1, LT2. reflexivity. }
  if_false.
  (* 0x14564 fmv.s fa0,fs0; jal __extendsftf2 *)
  step. fix_reg F HF8 8%Z. rewrite unbox_nan_box, sgnj_self32.
  step.
  eapply evt_cut.
  { eapply (br_ext IImgP.N_img rsegs 0x14df8 eq_refl eq_refl HEX b);
      [ apply freg_get_same; reflexivity | exact (MN_mi _ MN) | exact (MN_tm _ MN) ]. }
  intros ms' (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
              & MI2 & TM2).
  npost m0 m2 MU2 WM2 MI2 TM2.
  (* 0x1456c sd a0,0x38(sp); sd a1,0x30(sp) *)
  nstore (Sp + 56). nstore (Sp + 48).
  (* 0x14574 fcvt.l.s a0,fs0,rtz; sd a0,0x40(sp) *)
  step. fix_reg F HF8 8%Z. rewrite unbox_nan_box, (u32_lit b Hb), pn_t_def.
  nstore (Sp + 64).
  (* 0x1457c jal __floatditf *)
  step.
  let m := cur_mem in let MN := cur_mn m in
  eapply evt_cut;
  [ eapply (br_fd IImgP.N_img rsegs 0x14f54 eq_refl eq_refl HFD (pn_t b));
      [ rewrite unsigned_lit_wrap, SF.wrap64_mod; reflexivity | exact (MN_mi _ MN) | exact (MN_tm _ MN) ]
  | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m4 & -> & MU4 & WM4 & MI4 & TM4);
    npost m m4 MU4 WM4 MI4 TM4 ].
  (* 0x14580 mv a2,a0; mv a3,a1; ld a0,0x38(sp); ld a1,0x30(sp); jal __subtf3 *)
  step. step. nload (Sp + 56). nload (Sp + 48). step.
  let m := cur_mem in let MN := cur_mn m in
  eapply evt_cut;
  [ eapply (br_sub IImgP.N_img rsegs 0x15078 eq_refl eq_refl HSB);
      [ lia | exact (MN_stk48 _ MN) | exact (MN_mi _ MN) | exact (MN_tm _ MN) | eassumption ]
  | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & fc5 & m5 & -> & MU5 & WM5 & MI5 & TM5 & FRM5
                & ST5);
    pose proof (MN_sub m m5 MN MU5 WM5 MI5 TM5 ST5) as MN5;
    repeat match goal with
    | H : bytes_at rsegs m ?c ?bs |- _ =>
        let H' := fresh "D" in pose proof (D_sub m m5 c bs H MU5 ltac:(lia)) as H'; clear H
    end;
    clear dependent m ].
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite !u_lo64, !u_hi64, !W128_def, pn_d_def.
  (* 0x14594 sd a0,0x38(sp); sd a1,0x30(sp) *)
  nstore (Sp + 56). nstore (Sp + 48).
  (* 0x1459c mv a2,zero; ld a3,0x60(sp); jal __getf2 *)
  step.
  let m := cur_mem in let MN := cur_mn m in
  pose proof (read_le8 rsegs m (Sp + 0x60) _ (MN_h60 m MN)) as HR; step; clear HR.
  step.
  let m := cur_mem in let MN := cur_mn m in
  eapply evt_cut;
  [ eapply (br_ge IImgP.N_img rsegs 0x14d3c eq_refl eq_refl HGE); [exact (MN_mi _ MN) | exact (MN_tm _ MN)]
  | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m6 & -> & MU6 & WM6 & MI6 & TM6);
    npost m m6 MU6 WM6 MI6 TM6 ].
  rewrite !u_lo64, !u_hi64, !W128_def. fold_c128 HALF_128.
  (* 0x145a8 bgez a0 *)
  step. rewrite lts0 by apply f128_ge_range. rewrite Z.ltb_antisym, Bool.negb_involutive.
  destruct (0 <=? SF.f128_ge (W128 (SF.f128_sub (pn_d b) (W128 (f128_of_i64 (pn_t b))))) HALF_128) eqn:GE;
    cbv iota.
  { (* frac >= 1/2: 0x145d0 ld a0,0x40(sp); addi a0,a0,1; sd a0,0x40(sp) *)
    nload (Sp + 64). step. nstore (Sp + 64).
    eapply tail; [eassumption | eassumption | eassumption | hfc |].
    apply hn_eq; [exact FE | exact LT1 | exact LT2 |]. unfold pn_r. cbv zeta. rewrite GE. reflexivity. }
  (* 0x145ac ld a0,0x38(sp); ld a1,0x30(sp); mv a2,zero; ld a3,0x50(sp); jal __lttf2 *)
  nload (Sp + 56). nload (Sp + 48). step.
  let m := cur_mem in let MN := cur_mn m in
  pose proof (read_le8 rsegs m (Sp + 0x50) _ (MN_h50 m MN)) as HR; step; clear HR.
  step.
  let m := cur_mem in let MN := cur_mn m in
  eapply evt_cut;
  [ eapply (br_le IImgP.N_img rsegs 0x14c74 eq_refl eq_refl HLE); [exact (MN_mi _ MN) | exact (MN_tm _ MN)]
  | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m7 & -> & MU7 & WM7 & MI7 & TM7);
    npost m m7 MU7 WM7 MI7 TM7 ].
  rewrite !u_lo64, !u_hi64, !W128_def. fold_c128 MHALF_128.
  (* 0x145c0 bgez a0 *)
  step. rewrite lts0 by apply f128_le_range.
  destruct (SF.f128_le (W128 (SF.f128_sub (pn_d b) (W128 (f128_of_i64 (pn_t b))))) MHALF_128 <? 0) eqn:LM;
    cbn [negb]; cbv iota.
  - (* frac < -1/2: 0x145c4 ld a0,0x40(sp); addi a0,a0,-1; j 0x145d8; sd a0,0x40(sp) *)
    nload (Sp + 64). step. step. nstore (Sp + 64).
    eapply tail; [eassumption | eassumption | eassumption | hfc |].
    apply hn_eq; [exact FE | exact LT1 | exact LT2 |]. unfold pn_r. cbv zeta. rewrite GE, LM. lia.
  - (* r = t *)
    eapply tail; [eassumption | eassumption | eassumption | hfc |].
    apply hn_eq; [exact FE | exact LT1 | exact LT2 |]. unfold pn_r. cbv zeta. rewrite GE, LM. reflexivity.
Qed.

End Walk.

(** ** [near_stmt], from the five callee contracts *)
Theorem near_holds : @C_extendsftf2.extendsftf2_contract IImgP.N_img -> @C_floatditf.floatditf_contract IImgP.N_img ->
  @G_subtf3.subtf3_contract IImgP.N_img -> @G_getf2.getf2_contract IImgP.N_img -> @G_letf2.letf2_contract IImgP.N_img ->
  near_stmt.
Proof.
  intros HEX HFD HSB HGE HLE. unfold near_stmt.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo e
    HE HB4 HF9 HF18 H60 H50 ST HLO HAL HROM FRM MI TM K.
  pose proof (Z_to_bv_lit_self sp) as Esp. set (Sp := bv_unsigned sp) in *. clearbody Sp. subst sp.
  pose proof (Z_to_bv_lit_self a0) as Ea0. set (A := bv_unsigned a0) in *. clearbody A. subst a0.
  pose proof ST as (Hlo & HSpT & _). unfold NEAR_STACK in HLO. unfold FRAME_LOCALS in HSpT.
  (* 0x14548 flw fs0,8(a0) *)
  pose proof (ent_word_read rsegs m A e HE HB4) as HR. step. clear HR.
  rewrite extract_rd32 by (rewrite length_firstn; lia). rewrite rd32_firstn.
  pose proof (rd32_range (e_body e)) as Hb.
  eapply body with (b := rd32 (e_body e)) (lo := lo).
  all: lazymatch goal with
       | |- Sem.reg_get (bvmap_set _ _ _) (Z_to_bv 5 8) = _ => apply freg_get_same; reflexivity
       | |- Sem.reg_get (bvmap_set _ _ _) _ = _ => rewrite freg_get_other by reflexivity; assumption
       | |- MemN _ _ _ _ =>
           unfold MemN; refine (conj (munch_refl _ _) (conj (wmono_refl _ _) (conj MI (conj TM (conj ST (conj H60 H50))))))
       | |- forall _, _ => idtac
       | |- _ => first [assumption | lia]
       end.
  intros ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' HF' MU' WM' MI' TM' ST'.
  rewrite (hn_bin_nearest _ Hb).
  apply K; try assumption.
  intros k H8 H10. rewrite (HF' k H8 H10). apply freg_get_other.
  unfold bv_eqb. apply Z.eqb_neq. intro E. apply H8. rewrite <- E. reflexivity.
Qed.
