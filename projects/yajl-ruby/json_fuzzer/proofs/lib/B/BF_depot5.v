(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages AImageFacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import XB_mmap_fixed.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_lkit BF_lalloc1 BF_lalloc2 BF_depot4.
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
Definition TLM : Z := 0x5904a0.          (* [comment removed for export] *)
Definition SSo : Z := 0x180488.          (* [comment removed for export] *)
Definition CR_RET : Z := 0x74638.
Definition GC_RET : Z := 0x722f0.
Definition A_NAME_TLM : Z := 0x20504.    (* [comment removed for export] *)
Definition A_NAME_SS : Z := 0x20694.     (* [comment removed for export] *)

Lemma land_m4_r : forall x, 0 <= x < 2^64 -> x mod 4 = 0 -> Z.land x 18446744073709551612 = x.
Proof. aceil.
  intros x Hx Hm.
  assert (E : 18446744073709551612%Z = Z.ldiff (Z.ones 64) (Z.ones 2)) by reflexivity. rewrite E.
  assert (D : forall y a b, Z.land y (Z.ldiff a b) = Z.ldiff (Z.land y a) b).
  { intros. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec.
    destruct (Z.testbit y n), (Z.testbit a n), (Z.testbit b n); reflexivity. }
  rewrite D. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^2)%Z with 4%Z. Z.div_mod_to_equations. lia.
Qed.

Section Walk.
Variable P : acc -> Prop.
Hypothesis PDAT : forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cr_A : forall (ra sp gp tp t0 t1 t2 s0 s1 s2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo idx : Z),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 -> mem_inv bsegs m ->
  statics m ->
  rw_cells bsegs m TLM [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (TLM + 8 + 8 * idx) [C8 (Z_to_bv 64 0)] ->
  0 <= idx < 2^15 ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  (forall a n, TLM <= a -> a + Z.of_nat n <= TLM + 8 + 8 * 2^15 -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (fun ms' => exists (a3' a4' a5' : word) m',
      ms' = MS (mkR (Z_to_bv 64 CR_RET) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 TLM) (Z_to_bv 64 (TLM + 8 * idx))
                    (Z_to_bv 64 1048576) (Z_to_bv 64 A_NAME_TLM) (Z_to_bv 64 0) a3' a4' a5' a6 a7
                    (Z_to_bv 64 V_PAGESIZE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 a_mmap_die) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (TLM, TLM + 4)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp - 32)
      /\ rw_cells bsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells bsegs m' TLM [C4 (Z_to_bv 64 1)]
      /\ rw_cells bsegs m' (TLM + 8 + 8 * idx) [C8 (Z_to_bv 64 0)]
      /\ statics m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 TLM) (Z_to_bv 64 idx) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x74594) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until idx. intros ST LOC LO SPH MI STA MTX M1 HIDX PSTK PTLM. unfold CR_RET, A_NAME_TLM, a_mmap_die, TLM in *.
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (5833888, 5833888 + 4)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  open_statics STA.
  carve_frame 32%nat ST.
  do 5 stepA.                                   (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  zstepA. zstepA. zstepA.                       (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  do 4 zstepA.                                  (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA. if_false.                             (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA. if_false.                             (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  rewrite (Z.shiftl_mul_pow2 idx 3) by lia. change (2^3) with 8.
  replace (5833888 + idx * 8) with (5833888 + 8 + 8 * idx + -8) by lia.
  set (MA := 5833888 + 8 + 8 * idx) in M1.
  assert (HMA : MA = 5833896 + 8 * idx) by reflexivity. clearbody MA.
  replace (5833888 + 8 + 8 * idx + -8) with (MA + -8) by (clear -CEILB HMA; lia).
  zstepA.                                       (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; clear -CEILB HMA HIDX; lia end.
  zstepA.                                       (* [comment removed for export] *)
  zstepA. if_false.                             (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA. if_true.                              (* [comment removed for export] *)
  zstepA. zstepA.                               (* [comment removed for export] *)
  zstepA. if_false.                             (* [comment removed for export] *)
  zstepA. zstepA. zstepA. zstepA. zstepA.       (* [comment removed for export] *)
  zstepA. zstepA. zstepA.                       (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  replace (MA + -8) with (5833888 + 8 * idx) by (clear -CEILB HMA; lia).
  subst MA.
  apply evtA_done. do 4 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|]. split; [exact MTX|]. split; [exact M1|]. close_statics.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cr_B : forall (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (rav s0v s1v s2v r : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp idx : Z),
  stk bsegs m lo (usp - 32) -> alloc_ceiling <= lo -> lo + 32 <= usp -> usp <= 2^47 -> mem_inv bsegs m ->
  rw_cells bsegs m (usp - 32) [C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells bsegs m TLM [C4 (Z_to_bv 64 1)] ->
  rw_cells bsegs m (TLM + 8 + 8 * idx) [C8 (Z_to_bv 64 0)] ->
  0 <= idx < 2^15 ->
  (forall a n, lo <= a -> a + Z.of_nat n <= usp -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (fun ms' => exists m',
      ms' = MS (mkR rav (Z_to_bv 64 usp) gp tp t0 t1 t2 s0v s1v r a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom bsegs)
      /\ munch [(TLM, TLM + 4); (TLM + 8 + 8 * idx, TLM + 16 + 8 * idx)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo usp
      /\ rw_cells bsegs m' TLM [C4 (Z_to_bv 64 0)]
      /\ rw_cells bsegs m' (TLM + 8 + 8 * idx) [C8 r])
    (MS (mkR (Z_to_bv 64 CR_RET) (Z_to_bv 64 (usp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 TLM) (Z_to_bv 64 (TLM + 8 * idx)) r a1 a2 a3 a4 a5 a6 a7
             s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CR_RET) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until idx. intros ST LOC LO SPH MI FR MTX M1 HIDX PSTK. unfold CR_RET, TLM in *.
  pose proof LOC as LOC0. aceil.
  pose proof (munch_refl [(5833888, 5833888 + 4); (5833888 + 8 + 8 * idx, 5833888 + 16 + 8 * idx)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  set (MA := 5833888 + 8 + 8 * idx) in M1, MU.
  assert (HMA : MA = 5833896 + 8 * idx) by reflexivity. clearbody MA.
  replace (5833888 + 16 + 8 * idx) with (MA + 8) in MU by (clear -CEILB HMA; lia).
  replace (5833888 + 8 * idx) with (MA + -8) by (clear -CEILB HMA; lia).
  zstepA.                                       (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; clear -CEILB HMA HIDX; lia end.
  zstepA.                                       (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (MTXB : rw_cells bsegs mx 5833888 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)])
      by (eapply rw_cells_reshape; [| | exact MTX]; [cbn; tauto| vm_compute; reflexivity]) end.
  clear MTX.
  zstepA.                                       (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (MTX : rw_cells bsegs mx 5833888 [C4 (Z_to_bv 64 0)]) by (eapply rw_cells_reshape; [| | exact MTXB]; [cbn; tauto| vm_compute; reflexivity]) end.
  clear MTXB.
  do 5 zstepA.                                  (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  replace (usp - 32 + 32) with usp by lia. release_frame FR ST usp.
  apply evtA_done. eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros xx Hxx; cbn [outside] in Hxx |- *; clear -CEILB Hxx HMA; lia|].
  split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact MTX| first [exact M1| rewrite HMA in M1; exact M1 | replace (5833888 + 8 + 8 * idx) with MA by (clear -CEILB HMA; lia); exact M1]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gc_A : forall (ra sp gp tp t0 t1 t2 s0 s1 s2 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (al : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo b st : Z),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 -> mem_inv bsegs m ->
  rw_cells bsegs m (SSo + 8) [C8 al] ->
  rw_cells bsegs m (SSo + 16 + 16 * b) [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 st)] ->
  rw_cells bsegs m (SSo + 28 + 16 * b) [C4 (Z_to_bv 64 0)] ->
  0 <= b < 0x1000 -> 0 <= st < 2^32 ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (fun ms' => exists (a2' a3' a4' a5' al' : word) m',
      ms' = MS (mkR (Z_to_bv 64 GC_RET) (Z_to_bv 64 (bv_unsigned sp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 (SSo + 28 + 16 * b)) (Z_to_bv 64 (SSo + 16 + 16 * b))
                    (Z_to_bv 64 8388608) (Z_to_bv 64 A_NAME_SS) a2' a3' a4' a5' a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 a_mmap_nrdie) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (SSo + 28 + 16 * b, SSo + 32 + 16 * b); (SSo + 8, SSo + 16)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp - 32)
      /\ rw_cells bsegs m' (bv_unsigned sp - 32) [C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells bsegs m' (SSo + 8) [C8 al']
      /\ rw_cells bsegs m' (SSo + 16 + 16 * b) [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 st)]
      /\ rw_cells bsegs m' (SSo + 28 + 16 * b) [C4 (Z_to_bv 64 1)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SSo + 16 + 16 * b)) (Z_to_bv 64 SSo) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x72280) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until st. intros ST LOC LO SPH MI AL BLK MTX HB HST PSTK. unfold GC_RET, A_NAME_SS, a_mmap_nrdie, SSo in *.
  pose proof LOC as LOC0. aceil.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  set (BI := 1574024 + 16 + 16 * b) in *. assert (HBI : BI = 1574040 + 16 * b) by reflexivity. clearbody BI.
  set (MX := 1574024 + 28 + 16 * b) in *. assert (HMX : MX = BI + 12) by (clear -CEILB HBI; lia). clearbody MX.
  change (1574024 + 8) with 1574032 in *.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (MX, MX + 4); (1574032, 1574040)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 32%nat ST.
  do 5 stepA.                                   (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  replace (BI + 12) with MX by (clear -CEILB HMX; lia).
  zstepA.                                       (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  rewrite (land_m4_r MX) by (clear -CEILB HBI HMX HB; lia).
  zstepA.                                       (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; clear -CEILB HBI HMX HB; lia end.
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  do 4 zstepA.                                  (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; clear -CEILB HBI HMX HB; lia end.
  zstepA. if_false.                             (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA. if_false.                             (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; clear -CEILB HBI HMX HB; lia end.
  zstepA. if_false.                             (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; clear; lia end.
  zstepA. zstepA. zstepA.                       (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  apply evtA_done. do 6 eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros xx Hxx; cbn [outside] in Hxx |- *; clear -CEILB Hxx HBI HMX; lia|].
  split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|].
  split; [exact AL|]. split; [first [exact BLK| rewrite HBI in BLK; exact BLK]| first [exact MTX| rewrite HMX, HBI in MTX; exact MTX]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gc_B : forall (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (rav s0v s1v s2v r : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo usp b st : Z),
  stk bsegs m lo (usp - 32) -> alloc_ceiling <= lo -> lo + 32 <= usp -> usp <= 2^47 -> mem_inv bsegs m ->
  rw_cells bsegs m (usp - 32) [C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells bsegs m (SSo + 16 + 16 * b) [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 st)] ->
  rw_cells bsegs m (SSo + 28 + 16 * b) [C4 (Z_to_bv 64 1)] ->
  0 <= b < 0x1000 -> 0 <= st < 2^32 ->
  (forall a n, lo <= a -> a + Z.of_nat n <= usp -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (fun ms' => exists m',
      ms' = MS (mkR rav (Z_to_bv 64 usp) gp tp t0 t1 t2 s0v s1v r a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom bsegs)
      /\ munch [(SSo + 16 + 16 * b, SSo + 24 + 16 * b); (SSo + 28 + 16 * b, SSo + 32 + 16 * b)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo usp
      /\ rw_cells bsegs m' (SSo + 16 + 16 * b) [C8 r; C4 (Z_to_bv 64 st)]
      /\ rw_cells bsegs m' (SSo + 28 + 16 * b) [C4 (Z_to_bv 64 0)])
    (MS (mkR (Z_to_bv 64 GC_RET) (Z_to_bv 64 (usp - 32)) gp tp t0 t1 t2 (Z_to_bv 64 (SSo + 28 + 16 * b)) (Z_to_bv 64 (SSo + 16 + 16 * b)) r a1 a2 a3 a4 a5 a6 a7
             s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 GC_RET) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until st. intros ST LOC LO SPH MI FR BLK MTX HB HST PSTK. unfold GC_RET, SSo in *.
  pose proof LOC as LOC0. aceil.
  set (BI := 1574024 + 16 + 16 * b) in *. assert (HBI : BI = 1574040 + 16 * b) by reflexivity. clearbody BI.
  set (MX := 1574024 + 28 + 16 * b) in *. assert (HMX : MX = BI + 12) by (clear -CEILB HBI; lia). clearbody MX.
  pose proof (munch_refl [(BI, BI + 8); (MX, MX + 4)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  zstepA.                                       (* [comment removed for export] *)
  zstepA.                                       (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; clear -CEILB HBI HMX HB; lia end.
  zstepA.                                       (* [comment removed for export] *)
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (MTXB : rw_cells bsegs mx MX [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0)])
      by (eapply rw_cells_reshape; [| | exact MTX]; [cbn; tauto| vm_compute; reflexivity]) end.
  clear MTX.
  zstepA.                                       (* [comment removed for export] *)
  all: try lazymatch goal with |- P _ => apply PDAT; clear -CEILB HBI HMX HB; lia end.
  match goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (MTX : rw_cells bsegs mx MX [C4 (Z_to_bv 64 0)]) by (eapply rw_cells_reshape; [| | exact MTXB]; [cbn; tauto| vm_compute; reflexivity]) end.
  clear MTXB.
  do 5 zstepA.                                  (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  replace (usp - 32 + 32) with usp by lia. release_frame FR ST usp.
  apply evtA_done. eexists. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros xx Hxx; cbn [outside] in Hxx |- *; clear -CEILB Hxx HBI HMX; lia|].
  split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [first [exact BLK| rewrite HBI in BLK; exact BLK]| first [exact MTX| rewrite HMX, HBI in MTX; exact MTX]].
Qed.

End Walk.
End RC__1.
