(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages AImageFacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.examples Require Import X_mmap_fixed.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AF_lkit AF_swar AF_premap2 AF_lalloc1.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition LAL_ENTRY : Z := 0x37578.
Definition LAL_RET1 : Z := 0x37634.    (* [comment removed for export] *)
Definition LAL_RET2 : Z := 0x3768c.    (* [comment removed for export] *)
Definition LAL_RET3 : Z := 0x3769c.    (* [comment removed for export] *)
Definition LAL_RET4 : Z := 0x376a0.    (* [comment removed for export] *)
Definition LAL_BEQ : Z := 0x377d8.     (* [comment removed for export] *)
Definition LAL_TAIL : Z := 0x377dc.    (* [comment removed for export] *)
Definition LAL_ENS : Z := 0x379b0.     (* [comment removed for export] *)
Definition LAL_RET5 : Z := 0x379d4.    (* [comment removed for export] *)
Definition GOT_SECNAME : Z := 0xa4998.   (* [comment removed for export] *)
Definition V_SECNAME : Z := 0xa6860.     (* [comment removed for export] *)
Definition A_SECNAME : Z := 0x19399.

(* [comment removed for export] *)
Definition lal_msz (need : Z) : Z := round_up need 4096 + 4096.

Lemma lal_msz_eq : forall need, 0 <= need < 2^62 -> Z.land (need + 4095) 18446744073709547520 + 4096 = lal_msz need.
Proof. aceil.
  intros need Hn. unfold lal_msz, round_up. rewrite land_m4096 by lia. Z.div_mod_to_equations. lia.
Qed.

Lemma lal_msz_facts : forall need, 0 < need ->
  lal_msz need mod 4096 = 0 /\ need + 4096 <= lal_msz need /\ lal_msz need < need + 8192.
Proof. aceil.
  intros need Hn. unfold lal_msz, round_up. Z.div_mod_to_equations. lia.
Qed.

Lemma land_4095_l : forall x, 0 <= x -> x mod 4096 = 0 -> Z.land 4095 x = 0.
Proof. aceil.
  intros x Hx Hm. rewrite Z.land_comm. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. exact Hm.
Qed.
Lemma land_7_r : forall x, 0 <= x -> x mod 8 = 0 -> Z.land x 7 = 0.
Proof. aceil.
  intros x Hx Hm. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. exact Hm.
Qed.
Lemma land_m8_r : forall x, 0 <= x < 2^64 -> x mod 8 = 0 -> Z.land x 18446744073709551608 = x.
Proof. aceil.
  intros x Hx Hm.
  assert (E : 18446744073709551608%Z = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity. rewrite E.
  assert (D : forall y a b, Z.land y (Z.ldiff a b) = Z.ldiff (Z.land y a) b).
  { intros. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit y n), (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite D. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^3)%Z with 8%Z. Z.div_mod_to_equations. lia.
Qed.

Lemma land_m8_up : forall x, 0 <= x -> x + 8 < 2^64 -> x mod 8 = 0 -> Z.land (x + 7) 18446744073709551608 = x.
Proof. aceil.
  intros x Hx Hb Hm.
  assert (E : 18446744073709551608%Z = Z.ldiff (Z.ones 64) (Z.ones 3)) by reflexivity. rewrite E.
  assert (D : forall y a b, Z.land y (Z.ldiff a b) = Z.ldiff (Z.land y a) b).
  { intros. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit y n), (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite D. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^3)%Z with 8%Z. Z.div_mod_to_equations. lia.
Qed.

Lemma land_le_l : forall a b, 0 <= a -> Z.land a b <= a.
Proof. aceil.
  intros a b Ha.
  assert (D : Z.land (Z.ldiff a b) (Z.land a b) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
    destruct (Z.testbit a n), (Z.testbit b n); reflexivity. }
  pose proof (Z.add_nocarry_lxor _ _ D) as E. rewrite (Z.lxor_lor _ _ D), Z.lor_ldiff_and in E.
  pose proof (proj2 (Z.ldiff_nonneg a b) (or_introl Ha)). lia.
Qed.
Lemma land_le_r : forall a b, 0 <= b -> Z.land a b <= b.
Proof. aceil. intros. rewrite Z.land_comm. apply land_le_l. assumption. Qed.

Section Walk.
Variable P : acc -> Prop.
Hypothesis PDAT : forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).

(* [comment removed for export] *)
Definition lal_frame (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) : list cell :=
  [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lal_A : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo need PA rsz : Z),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 96 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 -> mem_inv asegs m ->
  rw_cells asegs m 0xaa558 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 rsz)] ->
  rw_cells asegs m GOT_SECNAME [C8 (Z_to_bv 64 V_SECNAME)] -> rw_cells asegs m V_SECNAME [C8 (Z_to_bv 64 A_SECNAME)] ->
  0 < need -> need <= 2^40 ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  evtA asegs P (fun ms' => exists (j0 : list byte) m',
      ms' = MS (mkR (Z_to_bv 64 LAL_RET1) (Z_to_bv 64 (bv_unsigned sp - 96)) gp tp t0 t1 t2 (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 0xaa558)
                    (Z_to_bv 64 (lal_msz need)) (Z_to_bv 64 A_SECNAME) (Z_to_bv 64 0) (Z_to_bv 64 8) a4 a5 a6 a7
                    (Z_to_bv 64 (lal_msz need)) (Z_to_bv 64 need) s4 (Z_to_bv 64 8) s6 s7 (Z_to_bv 64 7) s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 a_mmap_ordie) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp - 96)
      /\ rw_cells asegs m' (bv_unsigned sp - 96) (CB 8 j0 :: lal_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xaa558) (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 need) (Z_to_bv 64 8) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 LAL_ENTRY) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until rsz. intros ST LOC LO SPH MI SEC G1 G2 N0 N40 PSTK.
  unfold LAL_ENTRY, LAL_RET1, GOT_SECNAME, V_SECNAME, A_SECNAME, a_mmap_ordie in *.
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 96%nat ST.
  do 12 stepA.                                  (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA. if_false.                             (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA. if_false.                             (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA.               (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA. zstepA. zstepA.                       (* [comment removed for export] *)
  replace (Z.land ((0 - Z.b2z (4096 <? 8)) mod 18446744073709551616) 8) with 0 by reflexivity.
  rewrite Z.add_0_r. rewrite (lal_msz_eq need) by lia.
  pose proof (lal_msz_facts need N0) as (MF1 & MF2 & MF3).
  zstepA. if_cases K; zify_cond K; [| exfalso; revert K; rewrite ?unsigned_lit by lia; lia].   (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  do 2 stepA.                                   (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  apply evtA_done. eexists. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact FR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lal_B1 : forall (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp need mb PA rsz : Z),
  mem_inv asegs m ->
  rw_cells asegs m 0xaa558 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 rsz)] ->
  0 < need -> need mod 8 = 0 -> need <= 2^40 -> 0 < mb -> mb mod 4096 = 0 -> mb + lal_msz need <= alloc_ceiling ->
  evtA asegs P (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 LAL_RET2) (Z_to_bv 64 (usp - 96)) gp tp t0 t1 t2 (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 0xaa558)
                    (Z_to_bv 64 mb) (Z_to_bv 64 4096) (Z_to_bv 64 250) a3 a4 a5 a6 a7
                    (Z_to_bv 64 (lal_msz need)) (Z_to_bv 64 need) (Z_to_bv 64 mb) (Z_to_bv 64 (mb + 4096 + need)) (Z_to_bv 64 (mb + lal_msz need))
                    (Z_to_bv 64 (mb + 4096 + need)) (Z_to_bv 64 7) (Z_to_bv 64 (mb + 4096)) s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x55284) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 LAL_RET1) (Z_to_bv 64 (usp - 96)) gp tp t0 t1 t2 (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 0xaa558) (Z_to_bv 64 mb) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (lal_msz need)) (Z_to_bv 64 need) s4 (Z_to_bv 64 8) s6 s7 (Z_to_bv 64 7) s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 LAL_RET1) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until rsz. intros MI SEC N0 N8 N40 MB0 MB4 MBC. unfold LAL_RET1, LAL_RET2 in *.
  aceil.
  pose proof (lal_msz_facts need N0) as (MF1 & MF2 & MF3).
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstepA. if_cases K; zify_cond K; [exfalso; lia|].   (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  rewrite (land_4095_l mb) by lia.
  zstepA. if_false.                             (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  rewrite (land_7_r (4096 + mb)) by (clear -CEILB MB0 MB4; Z.div_mod_to_equations; lia).
  zstepA. zstepA. zstepA. zstepA.               (* [comment removed for export] *)
  replace (Z.land ((Z.b2z (0 <? 1) + -1) mod 18446744073709551616) 8) with 0 by reflexivity.
  zstepA. zstepA.                               (* [comment removed for export] *)
  rewrite !Z.add_0_l.
  zstepA. zstepA. zstepA.                       (* [comment removed for export] *)
  rewrite (land_m8_r (4096 + mb + need)); [| clear -CEILB MB0 MB4 N8 N0 MBC MF2; Z.div_mod_to_equations; lia| clear -CEILB MB0 MB4 N8 N0; Z.div_mod_to_equations; lia].
  rewrite (land_m8_up (4096 + mb)); [| lia| clear -CEILB MB0 MBC MF2 N0; lia| clear -CEILB MB0 MB4; Z.div_mod_to_equations; lia].
  zstepA.                                       (* [comment removed for export] *)
  do 2 stepA.                                   (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  replace (4096 + mb - mb) with 4096 by lia. replace (4096 + mb + need) with (mb + 4096 + need) by lia.
  replace (lal_msz need + mb) with (mb + lal_msz need) by lia. replace (4096 + mb) with (mb + 4096) by lia.
  apply evtA_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lal_B2 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (need mb : Z),
  mem_inv asegs m -> 0 < need -> 0 < mb -> mb + lal_msz need < 2^64 ->
  evtA asegs P (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 LAL_RET3) sp gp tp t0 t1 t2 s0 s1
                    (Z_to_bv 64 (mb + 4096 + need)) (Z_to_bv 64 (lal_msz need - 4096 - need)) (Z_to_bv 64 250) a3 a4 a5 a6 a7
                    s2 s3 s4 s5 (Z_to_bv 64 (mb + lal_msz need)) (Z_to_bv 64 (mb + 4096 + need)) s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x55284) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 LAL_RET2) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 (mb + lal_msz need)) (Z_to_bv 64 (mb + 4096 + need)) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 LAL_RET2) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until mb. intros MI N0 MB0 MBH. unfold LAL_RET2, LAL_RET3 in *.
  pose proof (lal_msz_facts need N0) as (MF1 & MF2 & MF3).
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstepA.                                       (* [comment removed for export] *)
  do 2 stepA.                                   (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  replace (mb + lal_msz need - (mb + 4096 + need)) with (lal_msz need - 4096 - need) by lia.
  apply evtA_done. reflexivity.
Qed.

Lemma lal_B3 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv asegs m ->
  evtA asegs P (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 LAL_RET4) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x5ca6c) fc None m (seg_rom asegs))
    (MS (mkR (Z_to_bv 64 LAL_RET3) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 LAL_RET3) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until m. intros MI. unfold LAL_RET3, LAL_RET4 in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  stepA. apply evtA_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lal_C : forall (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp need mb PA rsz T tmm tmd ptrc n : Z) (hj : list byte),
  mem_inv asegs m ->
  rw_cells asegs m 0xaa558 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 rsz)] ->
  rw_cells asegs m 0xaa588 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 n); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xaa7c0 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m (T + 2872) [C8 (Z_to_bv 64 tmm); C8 (Z_to_bv 64 tmd)] ->
  rw_cells asegs m mb [CB 32 hj] ->
  0 < need -> need mod 8 = 0 -> need <= 2^40 -> 0x603000 <= mb -> mb mod 4096 = 0 -> mb + lal_msz need <= alloc_ceiling ->
  (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)) (* [comment removed for export] *) ->
  T + 4096 <= alloc_ceiling -> (mb + lal_msz need <= T \/ T + 4096 <= mb) ->
  0 <= tmm < 2^64 -> 0 <= tmd < 2^64 -> 0 <= ptrc < 2^64 -> 0 <= n < 2^20 ->
  (forall a k, T <= a -> a + Z.of_nat k <= T + 4096 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, mb <= a -> a + Z.of_nat k <= mb + 32 -> P (Z_to_bv 64 a, k)) ->
  evtA asegs P (fun ms' => exists (x5 x6 x8 x9 : word) (hj' : list byte) m',
      ms' = MS (mkR (Z_to_bv 64 LAL_RET4) (Z_to_bv 64 (usp - 96)) gp tp t0 t1 t2 (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 0xaa558)
                    (Z_to_bv 64 (mb + 4096)) x5 x6 (Z_to_bv 64 n) (Z_to_bv 64 ptrc) x8 x9 a7
                    (Z_to_bv 64 (lal_msz need)) (Z_to_bv 64 (swar_res (lal_msz need))) (Z_to_bv 64 mb) (Z_to_bv 64 mb) (Z_to_bv 64 (mb + lal_msz need))
                    (Z_to_bv 64 (mb + 4096 + need)) (Z_to_bv 64 7) (Z_to_bv 64 (mb + 4096)) s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 LAL_BEQ) fc None m' (seg_rom asegs)
      /\ munch [(T + 2872, T + 2888); (mb, mb + 24); (0xaa7c0, 0xaa7c4)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' 0xaa7c0 [C4 (Z_to_bv 64 1)]
      /\ rw_cells asegs m' (T + 2872) [C8 (Z_to_bv 64 (tmm + 1)); C8 (Z_to_bv 64 (tmd + lal_msz need))]
      /\ rw_cells asegs m' mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 (lal_msz need)); C8 (Z_to_bv 64 need); CB 8 hj'])
    (MS (mkR (Z_to_bv 64 LAL_RET4) (Z_to_bv 64 (usp - 96)) gp tp t0 t1 t2 (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 0xaa558)
             (Z_to_bv 64 (T + 2800)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (lal_msz need)) (Z_to_bv 64 need) (Z_to_bv 64 mb) (Z_to_bv 64 (mb + 4096 + need)) (Z_to_bv 64 (mb + lal_msz need))
             (Z_to_bv 64 (mb + 4096 + need)) (Z_to_bv 64 7) (Z_to_bv 64 (mb + 4096)) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 LAL_RET4) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until hj. intros MI SEC NRS MTX TST HDR N0 N8 N40 MB0 MB4 MBC HT1 HT2 HTD TM1 TM2 PC0 NR PT PH.
  unfold LAL_RET4, LAL_BEQ in *. pose proof MBC as MBC0. pose proof HT2 as HT20. aceil.
  pose proof (lal_msz_facts need N0) as (MF1 & MF2 & MF3).
  pose proof (munch_refl [(T + 2872, T + 2888); (mb, mb + 24); (0xaa7c0, 0xaa7c4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  rewrite (land_7_r (mb + 4096)) by (clear -CEILB MB0 MB4; Z.div_mod_to_equations; lia).
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA. if_false.                             (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  rewrite (land_4095_l (mb + 4096)) by (clear -CEILB MB0 MB4; Z.div_mod_to_equations; lia).
  zstepA. if_false.                             (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; [exfalso; revert K1; rewrite ?unsigned_lit by lia; clear -CEILB MB0 MBC MF2 N0; lia|].   (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2; [exfalso; revert K2; rewrite ?unsigned_lit by lia; clear -CEILB MB0 MBC MF2 N0; lia|].   (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  replace (mb + 4096 - 4096) with mb by lia.
  zstepA. zstepA. zstepA.                       (* [comment removed for export] *)
  zstepA. if_cases K3; zify_cond K3; [exfalso; revert K3; rewrite ?unsigned_lit by lia; clear -CEILB MF2 N0 MBC MB0; lia|].   (* [comment removed for export] *)
  do 4 zstepA.                                  (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  do 4 zstepA.                                  (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA. if_false.                             (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA. if_false.                             (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  rewrite (Z.shiftr_div_pow2 n 20), Z.div_small by lia.
  zstepA. if_false.                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (XR : 0 < lal_msz need < 2^64) by (clear -CEILB MF2 N0 MBC MB0; lia).
  set (x := lal_msz need) in *.
  do 5 zstepA. set (u1 := Z.lor x (Z.shiftr x 1)) in |- *.
  do 5 zstepA. set (u2 := Z.lor u1 (Z.shiftr u1 2)) in |- *.
  do 8 zstepA. set (u3 := Z.lor u2 (Z.shiftr u2 4)) in |- *.
  do 2 zstepA. set (u4 := Z.lor u3 (Z.shiftr u3 8)) in |- *.
  do 2 zstepA. set (u5 := Z.lor u4 (Z.shiftr u4 16)) in |- *.
  do 2 zstepA. set (u6 := Z.lor u5 (Z.shiftr u5 32)) in |- *.
  zstepA. set (y := Z.lxor u6 18446744073709551615) in |- *.
  assert (YR : inr64 y) by ZBridge.zrange. unfold inr64 in YR.
  do 4 zstepA. set (c1 := y - Z.land (Z.shiftr y 1) 6148914691236517205) in |- *.
  assert (C1R : 0 <= c1 < 2^64).
  { subst c1. pose proof (land_le_l (Z.shiftr y 1) 6148914691236517205 ltac:(apply Z.shiftr_nonneg; lia)).
    pose proof (Z.land_nonneg (Z.shiftr y 1) 6148914691236517205). rewrite Z.shiftr_div_pow2 in * by lia. change (2^1) with 2 in *.
    clear -CEILB YR H H0. Z.div_mod_to_equations. lia. }
  do 6 zstepA. set (c2 := Z.land c1 3689348814741910323 + Z.land (Z.shiftr c1 2) 3689348814741910323) in |- *.
  assert (C2R : 0 <= c2 < 2^63).
  { subst c2. pose proof (land_le_r c1 3689348814741910323 ltac:(lia)). pose proof (land_le_r (Z.shiftr c1 2) 3689348814741910323 ltac:(lia)).
    pose proof (Z.land_nonneg c1 3689348814741910323). pose proof (Z.land_nonneg (Z.shiftr c1 2) 3689348814741910323).
    pose proof (Z.shiftr_nonneg c1 2). clear -CEILB C1R H H0 H1 H2 H3. lia. }
  do 2 zstepA. set (c3 := c2 + Z.shiftr c2 4) in |- *.
  assert (C3R : 0 <= c3 < 2^64).
  { subst c3. pose proof (Z.shiftr_nonneg c2 4). rewrite Z.shiftr_div_pow2 in * by lia. change (2^4) with 16 in *. clear -CEILB C2R H. Z.div_mod_to_equations. lia. }
  do 5 zstepA.
  replace (((Z.land c3 1085102592571150095 * 72340172838076673) mod 18446744073709551616) ≫ 56) with (swar_res x) by reflexivity.
  apply evtA_done. do 6 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  split; [exact MTX|]. split; [exact TST| exact HDR].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lal_D : forall (rav gp tp t0 t1 t2 a1 a2 a4 a5 a6 a7 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (ra s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c : word) (j0 hj : list byte) (bsl ws : list word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp need mb PA rsz ptrc n na nf cur mx ga gm : Z),
  stk asegs m lo (usp - 96) -> alloc_ceiling <= lo -> lo + 96 <= usp -> usp <= 2^47 -> mem_inv asegs m ->
  rw_cells asegs m (usp - 96) (CB 8 j0 :: lal_frame ra s0c s1c s2c s3c s4c s5c s6c s7c s8c s9c) ->
  rw_cells asegs m 0xaa558 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 rsz)] ->
  rw_cells asegs m 0xaa588 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 n); C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xaa5a0 [C8 (Z_to_bv 64 na); C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 mx)] ->
  u64arr asegs m 0xaa5c0 bsl -> length bsl = 64%nat ->
  rw_cells asegs m 0xaa7c0 [C4 (Z_to_bv 64 1)] ->
  rw_cells asegs m 0xaa7d8 [C8 (Z_to_bv 64 ga); C8 (Z_to_bv 64 gm)] ->
  u64arr asegs m PA ws -> (Z.to_nat n < length ws)%nat ->
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 (lal_msz need)); C8 (Z_to_bv 64 need); CB 8 hj] ->
  0 < need -> need <= 2^40 -> 0x603000 <= mb -> mb + lal_msz need <= alloc_ceiling ->
  0x603000 <= PA -> PA + 8 * Z.of_nat (length ws) <= alloc_ceiling -> (mb + lal_msz need <= PA \/ PA + 8 * Z.of_nat (length ws) <= mb) ->
  0 <= n < 2^20 -> 0 <= na < 2^64 -> 0 <= cur -> cur + lal_msz need < 2^64 -> 0 <= mx < 2^64 -> 0 <= ga < 2^64 -> 0 <= gm < 2^64 ->
  (forall a k, lo <= a -> a + Z.of_nat k <= usp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, mb <= a -> a + Z.of_nat k <= mb + 32 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, PA <= a -> a + Z.of_nat k <= PA + 8 * Z.of_nat (length ws) -> P (Z_to_bv 64 a, k)) ->
  evtA asegs P (fun ms' => exists (x11 x12 x13 x14 x15 x16 : word) (bsl' : list word) m',
      ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c (Z_to_bv 64 (mb + 4096)) x11 x12 x13 x14 x15 x16 a7
                    s2c s3c s4c s5c s6c s7c s8c s9c s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ munch [(PA + 8 * n, PA + 8 * n + 8); (mb + 24, mb + 32); (0xaa590, 0xaa599); (0xaa5a0, 0xaa5a8); (0xaa5b0, 0xaa5c0);
                (0xaa5c0 + 8 * Z.log2 (lal_msz need), 0xaa5c0 + 8 * Z.log2 (lal_msz need) + 8); (0xaa7d8, 0xaa7e8); (0xaa7c0, 0xaa7c4)] m m'
      /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo usp
      /\ rw_cells asegs m' 0xaa588 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 (n + 1)); C1 (Z_to_bv 8 0)]
      /\ rw_cells asegs m' 0xaa5a0 [C8 (Z_to_bv 64 (na + 1)); C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 (cur + lal_msz need)); C8 (Z_to_bv 64 (Z.max mx (cur + lal_msz need)))]
      /\ u64arr asegs m' 0xaa5c0 bsl' /\ length bsl' = 64%nat
      /\ rw_cells asegs m' 0xaa7c0 [C4 (Z_to_bv 64 0)]
      /\ rw_cells asegs m' 0xaa7d8 [C8 (Z_to_bv 64 (ga + lal_msz need)); C8 (Z_to_bv 64 (gm + lal_msz need))]
      /\ u64arr asegs m' PA (upd ws (Z.to_nat n) (Z_to_bv 64 mb))
      /\ rw_cells asegs m' mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 (lal_msz need)); C8 (Z_to_bv 64 need); C8 (Z_to_bv 64 n)])
    (MS (mkR rav (Z_to_bv 64 (usp - 96)) gp tp t0 t1 t2 (Z_to_bv 64 0xaa7c8) (Z_to_bv 64 0xaa558)
             (Z_to_bv 64 (mb + 4096)) a1 a2 (Z_to_bv 64 n) a4 a5 a6 a7
             (Z_to_bv 64 (lal_msz need)) (Z_to_bv 64 (swar_res (lal_msz need))) s4 (Z_to_bv 64 mb) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 LAL_TAIL) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until gm. intros ST LOC LO SPH MI FR SEC NRS SST BSL LBSL MTX GST ARR LWS HDR N0 N40 MB0 MBC PA0 PAC PAD NR NA0 CUR0 CURH MX0 GA0 GM0 PSTK PH PPA.
  unfold LAL_RET4, LAL_TAIL in *. pose proof LOC as LOC0. aceil.
  pose proof (lal_msz_facts need N0) as (MF1 & MF2 & MF3).
  assert (XR : 0 < lal_msz need < 2^64) by (clear -CEILB MF2 N0 MBC MB0; lia).
  pose proof (swar_idx (lal_msz need) XR) as IDX. pose proof (swar_res_range (lal_msz need) XR) as IR.
  pose proof (Z.log2_nonneg (lal_msz need)) as LG0.
  assert (LG63 : Z.log2 (lal_msz need) <= 63) by (apply Z.lt_succ_r; change (Z.succ 63) with 64; apply Z.log2_lt_pow2; lia).
  set (idx := Z.log2 (lal_msz need)) in *.
  pose proof (munch_refl [(PA + 8 * n, PA + 8 * n + 8); (mb + 24, mb + 32); (0xaa590, 0xaa599); (0xaa5a0, 0xaa5a8); (0xaa5b0, 0xaa5c0);
                          (0xaa5c0 + 8 * idx, 0xaa5c0 + 8 * idx + 8); (0xaa7d8, 0xaa7e8); (0xaa7c0, 0xaa7c4)] m) as MU.
  pose proof (wmono_refl asegs m) as WM. unfold lal_frame in FR.
  zstepA.                                       (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  rewrite IDX.
  zstepA.                                       (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 n 3) by lia. replace (PA + n * 2 ^ 3) with (PA + 8 * n) by lia.
  (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u64arr_store_ok asegs mx PA ws n (Z_to_bv 64 (PA + 8 * n)) ARR ltac:(lia) ltac:(reflexivity)) as SOK;
    pose proof (u64arr_write asegs mx PA ws n (Z_to_bv 64 mb) ARR ltac:(lia)) as ARR' end.
  stepA.
  all: lazymatch goal with |- P _ => apply PPA; lia | _ => idtac end.
  clear ARR. store_done. rename ARR' into ARR.
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (NTHB : exists bw, nth_error bsl (Z.to_nat idx) = Some bw).
  { destruct (nth_error bsl (Z.to_nat idx)) as [bw|] eqn:E; [exists bw; reflexivity|]. apply nth_error_None in E. lia. }
  destruct NTHB as [bw NTHB].
  zstepA. if_cases KM; zify_cond KM; [| zstepA].   (* [comment removed for export] *)
  all: zstepA; zstepA.                          (* [comment removed for export] *)
  all: rewrite (Z.shiftl_mul_pow2 idx 3) by lia; replace (697688 + idx * 2 ^ 3) with (697688 + 8 * idx) by lia.
  all: pose proof (u64arr_read asegs _ 0xaa5c0 bsl idx bw (Z_to_bv 64 (697688 + 8 * idx + 104)) BSL NTHB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
  all: zstepA; clear RD.                        (* [comment removed for export] *)
  all: zstepA.                                  (* [comment removed for export] *)
  all: zstepA.                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  all: match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u64arr_store_ok asegs mx 0xaa5c0 bsl idx (Z_to_bv 64 (697688 + 8 * idx + 104)) BSL ltac:(rewrite LBSL; lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    pose proof (u64arr_write asegs mx 0xaa5c0 bsl idx (Z_to_bv 64 (bv_unsigned bw + 1)) BSL ltac:(rewrite LBSL; lia)) as BSL' end.
  all: stepA.
  all: lazymatch goal with |- P _ => apply PDAT; lia | _ => idtac end.
  all: replace (697792 + 8 * idx) with (697688 + 8 * idx + 104) in BSL' by lia.
  all: clear BSL; store_done; rename BSL' into BSL.
  all: zstepA.                                  (* [comment removed for export] *)
  all: zstepA.                                  (* [comment removed for export] *)
  all: zstepA.                                  (* [comment removed for export] *)
  all: zstepA.                                  (* [comment removed for export] *)
  all: zstepA.                                  (* [comment removed for export] *)
  all: match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (MTXB : rw_cells asegs mx 0xaa7c0 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)])
      by (eapply rw_cells_reshape; [| | exact MTX]; [cbn; tauto| vm_compute; reflexivity]) end.
  all: clear MTX.
  all: zstepA.                                  (* [comment removed for export] *)
  all: match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (MTX : rw_cells asegs mx 0xaa7c0 [C4 (Z_to_bv 64 0)]) by (eapply rw_cells_reshape; [| | exact MTXB]; [cbn; tauto| vm_compute; reflexivity]) end.
  all: clear MTXB.
  all: do 12 zstepA.                            (* [comment removed for export] *)
  all: stepA.                                   (* [comment removed for export] *)
  all: replace (usp - 96 + 96) with usp by lia; release_frame FR ST usp.
  all: apply evtA_done; do 8 eexists; split; [reflexivity|].
  all: split; [exact MU|]; split; [exact WM|]; split; [exact MI|]; split; [exact ST|]; split; [exact NRS|].
  all: split; [first [replace (Z.max mx (cur + lal_msz need)) with mx by lia | replace (Z.max mx (cur + lal_msz need)) with (cur + lal_msz need) by lia]; exact SST|].
  all: split; [exact BSL|]; split; [rewrite upd_length; exact LBSL|]; split; [exact MTX|]; split; [exact GST|]; split; [exact ARR| exact HDR].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lal_beq : forall (rav sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (n ptrc : Z),
  mem_inv asegs m -> 0 <= n < 2^64 -> 0 <= ptrc < 2^64 ->
  evtA asegs P (fun ms' =>
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 n) (Z_to_bv 64 ptrc) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (if n =? ptrc then LAL_ENS else LAL_TAIL)) fc None m (seg_rom asegs))
    (MS (mkR rav sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 n) (Z_to_bv 64 ptrc) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 LAL_BEQ) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until ptrc. intros MI NR PR. unfold LAL_BEQ, LAL_ENS, LAL_TAIL.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstepA. if_cases K; zify_cond K.
  - rewrite (proj2 (Z.eqb_eq n ptrc) K). apply evtA_done. reflexivity.
  - rewrite (proj2 (Z.eqb_neq n ptrc) K). apply evtA_done. reflexivity.
Qed.

Lemma lal_E1 : forall (rav gp tp t0 t1 t2 a0 a1 a2 a4 a5 a6 a7 s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp n PA rsz res : Z),
  mem_inv asegs m ->
  rw_cells asegs m 0xaa558 [C8 (Z_to_bv 64 4096); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 PA); C8 (Z_to_bv 64 rsz)] ->
  0 <= n < 2^20 -> 0 <= PA -> PA + 8 * n < 2^64 -> 0 <= res < 2^64 ->
  evtA asegs P (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 LAL_RET5) (Z_to_bv 64 (usp - 96)) gp tp t0 t1 t2 s0 (Z_to_bv 64 0xaa558)
                    (Z_to_bv 64 (PA + 8 * n)) (Z_to_bv 64 0x20000) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0xaa568) a5 a6 a7
                    s2 s3 (Z_to_bv 64 res) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x67934) fc None m (seg_rom asegs))
    (MS (mkR rav (Z_to_bv 64 (usp - 96)) gp tp t0 t1 t2 s0 (Z_to_bv 64 0xaa558) (Z_to_bv 64 res) a1 a2 (Z_to_bv 64 n) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 LAL_ENS) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until res. intros MI SEC NR PA0 PAH RR. unfold LAL_ENS, LAL_RET5.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstepA.                                       (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 n 3) by lia. replace (n * 2 ^ 3 + PA) with (PA + 8 * n) by lia.
  do 4 stepA.                                   (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  do 4 stepA.                                   (* [comment removed for export] *)
  do 3 stepA.                                   (* [comment removed for export] *)
  apply evtA_done. reflexivity.
Qed.

Lemma lal_E2 : forall (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (usp n ptrc res : Z),
  mem_inv asegs m ->
  rw_cells asegs m 0xaa588 [C8 (Z_to_bv 64 ptrc); C8 (Z_to_bv 64 n); C1 (Z_to_bv 8 0)] ->
  0 <= n < 2^20 -> 0 <= ptrc < 2^62 -> 0 <= res < 2^64 ->
  evtA asegs P (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 LAL_RET5) (Z_to_bv 64 (usp - 96)) gp tp t0 t1 t2 s0 (Z_to_bv 64 0xaa558)
                    (Z_to_bv 64 res) (Z_to_bv 64 (ptrc + 16384)) (Z_to_bv 64 16384) (Z_to_bv 64 n) a4 a5 a6 a7
                    s2 s3 (Z_to_bv 64 res) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 LAL_TAIL) fc None m' (seg_rom asegs)
      /\ munch [(0xaa588, 0xaa590)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' 0xaa588 [C8 (Z_to_bv 64 (ptrc + 16384)); C8 (Z_to_bv 64 n); C1 (Z_to_bv 8 0)])
    (MS (mkR (Z_to_bv 64 LAL_RET5) (Z_to_bv 64 (usp - 96)) gp tp t0 t1 t2 s0 (Z_to_bv 64 0xaa558) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 res) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 LAL_RET5) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until res. intros MI NRS NR PR RR. unfold LAL_RET5, LAL_TAIL.
  pose proof (munch_refl [(0xaa588, 0xaa590)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  stepA.                                        (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  apply evtA_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact NRS].
Qed.

End Walk.
End RC__1.
