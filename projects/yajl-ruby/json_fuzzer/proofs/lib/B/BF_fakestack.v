(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanState AsanFakeStack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BI_shadow BF_kit BF_fakestack_rep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac showpc := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc end.
(* [comment removed for export] *)
Ltac cstep := zstepA; try first [if_true | if_false].

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
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
Definition MTS2 : Z := 0x3e2a0.
Definition a_high_mem (SB p : Z) : Prop := SB + 0x100000000000 <= p <= A_HIGHEND_VAL.
(* [comment removed for export] *)
Definition a_in_mem2 (SB p : Z) : Prop := (0 <= p < SB) \/ a_high_mem SB p.

Definition mts2_post (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (SB p : Z) : machine_state -> Prop :=
  fun ms' => exists t0 a1 a2 a3 a4 a5 a6 a7,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (SB + Z.shiftr p 3)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom bsegs)
    /\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m.

Section MTS.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : mem) (SB p : Z).
Hypothesis MI : mem_inv bsegs m.
Hypothesis G : icp_globals bsegs m SB.
Hypothesis HP : a_in_mem2 SB p.
Hypothesis PIMG : forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k).

Lemma mts2_walk : forall x10, x10 = Z_to_bv 64 p ->
  evtA bsegs P (mts2_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SB p)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MTS2) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros x10 ->. unfold MTS2.
  assert (MU : munch [] m m) by apply munch_refl. assert (WM : wmono bsegs m m) by apply wmono_refl.
  unfold a_in_mem2, a_high_mem, A_HIGHEND_VAL in HP.
  pose proof G as G'. icp_globals_open G.
  stepA. stepA. stepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  replace (SB <? SB + -1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.add].
  change ((-1) mod 18446744073709551616) with (Z.ones 64).
  rewrite (Z.land_comm (Z.ones 64)), Z.land_ones, Z.mod_small by lia.
  zstepA. (* [comment removed for export] *) if_cases KL; zify_cond KL.
  - (* [comment removed for export] *) zstepA. zstepA. zstepA. (* [comment removed for export] *) finishA.
  - (* [comment removed for export] *)
    stepA. stepA. stepA. stepA. stepA. stepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *) zstepA. (* [comment removed for export] *)
    if_cases KM; zify_cond KM. 2:{ exfalso. revert KM. cbn. lia. }
    stepA. stepA. stepA. (* [comment removed for export] *)
    zstepA. zstepA. (* [comment removed for export] *)
    zstepA. (* [comment removed for export] *) if_cases KH1; zify_cond KH1. { exfalso. revert KH1. cbn. lia. }
    zstepA. (* [comment removed for export] *) if_cases KH2; zify_cond KH2. { exfalso. revert KH2. cbn. lia. }
    zstepA. zstepA. zstepA. (* [comment removed for export] *) finishA.
Qed.
End MTS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MUSL_TGA : Z := 0x9f4c0.
Definition tga_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists a1 a2,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FS_TP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom bsegs)
    /\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m.

Section TGA.
Variable P : acc -> Prop.
Lemma musl_tga_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv bsegs m ->
  tp = Z_to_bv 64 FS_TP -> a0 = Z_to_bv 64 0xa6280 ->
  rw_cells bsegs m 0xa6280 [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0xfffffffffffff800)] ->
  rw_cells bsegs m 0x5e1548 [C8 (Z_to_bv 64 0x5e1570)] ->
  rw_cells bsegs m 0x5e1578 [C8 (Z_to_bv 64 0x5e1d50)] ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  evtA bsegs P (tga_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MUSL_TGA) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until m. intros MI -> -> DESC DTV DTV1 PIMG. unfold MUSL_TGA, FS_TP in *.
  assert (MU : munch [] m m) by apply munch_refl. assert (WM : wmono bsegs m m) by apply wmono_refl.
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  zstepA. (* [comment removed for export] *)
  finishA.
Qed.
End TGA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition GCT : Z := 0x5d6ac.
Definition gct_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo thr : Z) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 thr) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Section GCTW.
Variable P : acc -> Prop.
Lemma gct_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo ctx thr : Z),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 FS_TP ->
  rw_cells bsegs m 0xade20 [C1 (Z_to_bv 8 1)] -> rw_cells bsegs m 0xade24 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x5e14f8 [C8 (Z_to_bv 64 0x6028f8)] -> rw_cells bsegs m 0x6028f8 [C8 (Z_to_bv 64 ctx)] ->
  rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 thr)] -> 0 < ctx -> ctx + 160 <= alloc_ceiling ->
  (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, ctx <= a -> a + Z.of_nat k <= ctx + 160 -> P (Z_to_bv 64 a, k)) ->
  evtA bsegs P (gct_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo thr)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 GCT) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until thr. intros ST LOC LO SPH MI -> KI KEY TSD TSD0 CTXT C0 C1 PSTK PIMG PCTX. unfold GCT, FS_TP in *.
  aceil.
  assert (MU : munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 16%nat ST.
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  assert (E0 : sx32 (Z_to_bv 64 0) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity). rewrite E0. clear E0.
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  if_cases KC; zify_cond KC; try (exfalso; lia).
  cstep. (* [comment removed for export] *)
  cstep. cstep. cstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finishA.
Qed.
End GCTW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition DTLS_F : Z := 0x6adc0.
Definition dtls_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists a1 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Section DTLSW.
Variable P : acc -> Prop.
Lemma dtls_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo cf vb dto dtls dtv1 : Z),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 FS_TP -> a0 = Z_to_bv 64 0xa6280 ->
  rw_cells bsegs m 0xa6280 [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0xfffffffffffff800)] ->
  rw_cells bsegs m 0xa5590 [C8 (Z_to_bv 64 cf)] -> rw_cells bsegs m (cf + 137) [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xa55f0 [C8 (Z_to_bv 64 vb)] -> rw_cells bsegs m vb [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xa6290 [C8 (Z_to_bv 64 dto)] -> rw_cells bsegs m (dto + FS_TP) [C8 (Z_to_bv 64 dtls)] ->
  0x10000 <= cf -> cf + 138 <= 0x603000 -> 0x10000 <= vb -> vb + 4 <= 0x603000 -> 0 <= dto -> FS_TP + dto + 8 <= 0x603000 ->
  rw_cells bsegs m (dtls + 24) [C8 (Z_to_bv 64 dtv1)] -> dtv1 <> 0 -> 0 <= dtv1 < 2^64 ->
  0 < dtls -> dtls + 4096 <= alloc_ceiling ->
  (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, dtls <= a -> a + Z.of_nat k <= dtls + 4096 -> P (Z_to_bv 64 a, k)) ->
  evtA bsegs P (dtls_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DTLS_F) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until dtv1. intros ST LOC LO SPH MI -> -> DESC GF CF GV VB GD DT CF1 CF2 VB1 VB2 DT1 DT2 DTV NZ DV D0 D1 PSTK PIMG PDT.
  unfold DTLS_F, FS_TP in *. aceil.
  assert (MU : munch [(bv_unsigned sp - 144, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 144%nat ST.
  cstep. (* [comment removed for export] *)
  do 13 cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  assert (E0 : sx32 (Z_to_bv 64 0) = Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity). rewrite E0. clear E0.
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  showpc. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *) if_cases K1; zify_cond K1; try (exfalso; revert K1; cbn; lia).
  cstep. (* [comment removed for export] *) if_cases K2; zify_cond K2; try (exfalso; lia).
  cstep. (* [comment removed for export] *) if_cases K3; zify_cond K3; try (exfalso; lia).
  cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *) if_cases K4; zify_cond K4; try (exfalso; lia).
  cstep. (* [comment removed for export] *)
  do 13 cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). finishA.
Qed.
End DTLSW.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition TGA_THUNK : Z := 0x43018.
Definition tga_icp_post (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists a1 a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FS_TP) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Section TGAICP.
Variable P : acc -> Prop.
Lemma tga_icp_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (E : aenv) (fsbase : Z) (pl : fs_plumb),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 176 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 FS_TP -> a0 = Z_to_bv 64 0xa6280 ->
  FSEnv bsegs E fsbase pl m ->
  (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, fp_ctx pl <= a -> a + Z.of_nat k <= fp_ctx pl + 160 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, ae_thread E <= a -> a + Z.of_nat k <= ae_thread E + 64 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, fp_dtls pl <= a -> a + Z.of_nat k <= fp_dtls pl + 4096 -> P (Z_to_bv 64 a, k)) ->
  evtA bsegs P (tga_icp_post ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 TGA_THUNK) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until pl. intros ST LOC LO SPH MI Htp -> ENV PSTK PIMG PCTX PTHR PDT.
  pose proof ENV as (DESC & REAL & INI & DTV & DTV1 & TLS & KI & KEY & TSD & TSD0 & CTXT & THR & (cf & vb & dto & GF & CF & GV & VB & GD & DT & CF1 & CF2 & VB1 & VB2 & DT1 & DT2 & PinCF & PinVB & PinDT) & DTVE & NZ & DVR & D0 & D1 & D8 & C0 & C1 & C8 & T0 & T1 & T8 & GSB & SBV).
  unfold TGA_THUNK in *. pose proof LOC as LOC'. aceil.
  assert (MU : munch [(bv_unsigned sp - 176, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 32%nat ST.
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  do 4 cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  showpc.
  call_spA (try_init_walk P);
    [ eassumption | exact LOC' | lia | lia | exact MI | eassumption
    | intros a k Ha Hk; apply PSTK; lia | intros a k Ha Hk; apply PIMG; lia | ].
  cstep. cstep. (* [comment removed for export] *)
  cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  showpc.
  callA (musl_tga_walk P); [ eassumption | exact Htp | reflexivity | eassumption | eassumption | eassumption | exact PIMG | ].
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  call_spA (gct_walk P);
    [ eassumption | exact LOC' | lia | lia | eassumption | exact Htp | eassumption | eassumption | eassumption | eassumption | eassumption
    | lia | exact C1 | intros a k Ha Hk; apply PSTK; lia | exact PIMG | exact PCTX | ].
  cstep. (* [comment removed for export] *) if_cases KT; zify_cond KT; try (exfalso; lia).
  cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  call_spA (dtls_walk P);
    [ eassumption | exact LOC' | lia | lia | eassumption | exact Htp | reflexivity
    | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
    | lia | lia | lia | lia | lia | lia | eassumption | exact NZ | exact DVR | lia | exact D1
    | intros a k Ha Hk; apply PSTK; lia | exact PIMG | exact PDT | ].
  cstep. (* [comment removed for export] *)
  do 4 cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  all: lazymatch goal with |- evtA _ _ _ _ => showpc | |- ?g => idtac "GOAL" g end.
  lazymatch goal with H : rw_cells bsegs ?mx (bv_unsigned sp + -32) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with S : stk bsegs mx lo _ |- _ => release_frame H S (bv_unsigned sp) end end.
  finishA.
Qed.
End TGAICP.
End RC__1.
