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
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA MmStep AImages AImageFacts LazyModel ImplRzA NodesA_mm.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import XB_mmap_fixed.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_kit BF_kit2 BF_lkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.

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
Section LDTAIL.
Variable P : acc -> Prop.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variable Q : machine_state -> Prop.
Variables (m : mem) (lo A L : Z) (nd3 ix : word) (TSD CTX T mu mud : Z).
(* [comment removed for export] *)
Variables (s0c s1c s2c rac : word).
Hypothesis SK : stk bsegs m lo (bv_unsigned sp).
Hypothesis LOC : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 32.
Hypothesis SPH : bv_unsigned sp + 32 <= 2^47.
Hypothesis MI : mem_inv bsegs m.
Hypothesis FR : rw_cells bsegs m (bv_unsigned sp) [C8 s2c; C8 s1c; C8 s0c; C8 rac].
Hypothesis HA : 0x603000 <= A /\ A + 32 <= alloc_ceiling.
Hypothesis HDRC : rw_cells bsegs m A [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 L); C8 nd3; C8 ix].
Hypothesis TC : thread_cells m tp TSD CTX T.
Hypothesis HT1 : 0x5d0810 <= TSD. Hypothesis HT2 : TSD + 8 <= 0x603000.
Hypothesis HC1 : 0 < CTX.   (* [comment removed for export] *) Hypothesis HC2 : CTX + 4096 <= alloc_ceiling.
Hypothesis HT3 : (0x1000 <= T /\ (T + 4096 <= 0x10000 \/ 0x603000 <= T)).   (* [comment removed for export] *) Hypothesis HT4 : T + 4096 <= alloc_ceiling.
Hypothesis HTP : 0x5d0810 + 88 <= bv_unsigned tp < 0x603000.
Hypothesis TST : rw_cells bsegs m (T + 2888) [C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 mud)].   (* [comment removed for export] *)
Hypothesis HAT : A + 32 <= T \/ T + 4096 <= A.
Hypothesis HAC : A + 32 <= CTX \/ CTX + 4096 <= A.
Hypothesis HTC : CTX + 160 <= T \/ T + 4096 <= CTX.
Hypothesis HV : 0 <= mu < 2^64 /\ 0 <= mud < 2^64.
Hypothesis PSTK : forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp + 32 -> P (Z_to_bv 64 a, n).
Hypothesis PDAT : forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).
Hypothesis PCTX : P (Z_to_bv 64 (CTX + 152), 8%nat).
Hypothesis PT : forall a n, T <= a -> a + Z.of_nat n <= T + 4096 -> P (Z_to_bv 64 a, n).
Hypothesis PHC : forall a n, A <= a -> a + Z.of_nat n <= A + 32 -> P (Z_to_bv 64 a, n).

Lemma ldtail_walk :
  (forall m' (a3' a4' t0' t1' t2' a5' a6' a7' t3' t4' t5' t6' : word),
     mem_inv bsegs m' -> stk bsegs m' lo (bv_unsigned sp + 32) ->
     wmono bsegs m m' -> munch [(bv_unsigned sp - 32, bv_unsigned sp + 32); (T + 2888, T + 2904)] m m' ->
     rw_cells bsegs m' (T + 2888) [C8 (Z_to_bv 64 (mu + 1)); C8 (Z_to_bv 64 (mud + L))] ->
     rw_cells bsegs m' A [C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 L); C8 nd3; C8 ix] ->
     thread_cells m' tp TSD CTX T ->
     evtA bsegs P Q (MS (mkR rac (Z_to_bv 64 (bv_unsigned sp + 32)) gp tp t0' t1' t2' s0c s1c (Z_to_bv 64 A) (Z_to_bv 64 L) (Z_to_bv 64 0)
                            a3' a4' a5' a6' a7' s2c s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (Z_to_bv 64 0x67278) fc None m' (seg_rom bsegs))) ->
  evtA bsegs P Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 L) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x35330) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros CONT.
  pose proof LOC as LOC0. aceil.
  destruct TC as (TC1 & TC2 & TC3 & TC4 & TC5).
  assert (MU : munch [(bv_unsigned sp - 32, bv_unsigned sp + 32); (T + 2888, T + 2904)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  zstepA. (* [comment removed for export] *)
  call_spA (gcts_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD CTX T);
    [exact SK| exact LOC0| lia| lia| exact MI| exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| lia| exact HT2| lia| exact HC2| lia
    | lia| intros; apply PSTK; lia| exact PDAT| exact PCTX|].
  rename POST into SK.
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  zstepA. zstepA. (* [comment removed for export] *)
  do 4 zstepA.    (* [comment removed for export] *)
  zstepA.         (* [comment removed for export] *)
  release_frame FR SK (bv_unsigned sp + 32).
  zstepA.         (* [comment removed for export] *)
  eapply CONT; [exact MI0| exact SK| exact WM| exact MU| | exact HDRC| exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))].
  exact TST.
Qed.
End LDTAIL.

Definition a_unmap_or_die := 0x67278.
Definition a_munmap_spin := 0x61374.

(* [comment removed for export] *)
Definition umd_statics (m : mem) : Prop :=
     rw_cells bsegs m 0xa5590 [C8 (Z_to_bv 64 0x1400e8)] /\ rw_cells bsegs m 0x140178 [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m 0xa55e0 [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 0x1400dc)] /\ rw_cells bsegs m 0x1400dc [C4 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Definition ushape (A L : Z) (r : word) (u : bool) : resp :=
  if u then mkEffectU r [] [] [(Z_to_bv 64 A, Z_to_bv 64 L)] [] [] else mkEffectU r [] [] [] [] [].

Section UMD.
Variable P : acc -> Prop.
Hypothesis PDATA : forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).

Definition umd_post {X} (R : X -> word -> bool -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A L : Z) (lo : Z) (m : mem) (a : X) : machine_state -> Prop :=
  fun ms' => exists (r : word) (u : bool) (R' : bvmap 5 word) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = (if is_err r
           then MS R' F (Z_to_bv 64 a_munmap_spin) fc None m' (seg_rom bsegs)           (* [comment removed for export] *)
           else MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m' (seg_rom bsegs))                                (* [comment removed for export] *)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + L)] m m'
    /\ (u = false -> wmono bsegs m m') /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp) /\ umd_statics m'
    /\ R a r u.

Lemma unmap_or_die_specA : forall {X} (dec : resp -> option X) (R : X -> word -> bool -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (A L : Z) (lo : Z),
  (forall rsp a, dec rsp = Some a -> exists r u, R a r u /\ rsp = ushape A L r u) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m -> umd_statics m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 L -> a2 = Z_to_bv 64 0 ->
  b_image_end <= A -> 0 < L -> A + L <= lo ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  implA bsegs (at_nodeA bsegs) P (enode (NMunmap A L) dec)
       (epost (umd_post R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A L lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 a_unmap_or_die) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until lo. intros DEC ST LOC LO SPH MI STA -> -> -> AI L0 AL PSTK. unfold a_unmap_or_die.
  unfold b_image_end in AI. pose proof LOC as LOC'. aceil.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (A, A + L)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  destruct STA as (G1 & V1 & G2 & V2).
  apply implA_enode.
  carve_frame 48%nat ST.
  do 5 stepA.                                   (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { exfalso. lia. }   (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  do 3 stepA.                                   (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  stepA.                                        (* [comment removed for export] *)
  step_ecallA.
  split. { at_nodeA_solve. }
  intros rsp ans Hdec. destruct (DEC rsp ans Hdec) as (r & u & HR & ->). clear Hdec.
  pose proof (bv_unsigned_in_range 64 r) as RR. change (bv_modulus 64) with (2^64)%Z in RR.
  destruct u; unfold ushape; cbv iota; sys_nret.
  all: stepA.                                   (* [comment removed for export] *)
  all: do 2 stepA.                              (* [comment removed for export] *)
  all: stepA.                                   (* [comment removed for export] *)
  all: stepA.                                   (* [comment removed for export] *)
  all: stepA.                                   (* [comment removed for export] *)
  all: zstepA; zstepA.                          (* [comment removed for export] *)
  all: zstepA; if_cases K; zify_cond K.         (* [comment removed for export] *)
  all: lazymatch goal with
       | |- evtA _ _ _ (MS _ _ (Z_to_bv 64 416288) _ _ _ _) =>
           (* [comment removed for export] *)
           zstepA;
           replace (18446744073709547520 <? bv_unsigned r) with false by (symmetry; apply (proj2 (Z.ltb_ge _ _)); lia);
           cbn [Z.b2z];
           stepA; (* [comment removed for export] *)
           zstepA; if_false; (* [comment removed for export] *)
           stepA; stepA; (* [comment removed for export] *)
           do 2 stepA; (* [comment removed for export] *)
           zstepA; (* [comment removed for export] *)
           zstepA; if_true; (* [comment removed for export] *)
           stepA; (* [comment removed for export] *)
           do 5 stepA; (* [comment removed for export] *)
           release_frame FR ST (bv_unsigned sp);
           stepA (* [comment removed for export] *)
       | _ =>
           (* [comment removed for export] *)
           zstepA; (let K1 := fresh "K" in if_cases K1; zify_cond K1; [exfalso; lia|]); (* [comment removed for export] *)
           zstepA; zstepA; (* [comment removed for export] *)
           zstepA;
           replace (18446744073709547520 <? bv_unsigned r) with true by (symmetry; apply (proj2 (Z.ltb_lt _ _)); lia);
           cbn [Z.b2z];
           stepA; (* [comment removed for export] *)
           zstepA; if_true; (* [comment removed for export] *)
           zstepA; (* [comment removed for export] *)
           do 3 stepA; (* [comment removed for export] *)
           stepA; (* [comment removed for export] *)
           carve_frame 16%nat ST;
           stepA; stepA; (* [comment removed for export] *)
           do 2 stepA; (* [comment removed for export] *)
           do 2 stepA; (* [comment removed for export] *)
           zstepA; if_false; (* [comment removed for export] *)
           do 2 stepA; (* [comment removed for export] *)
           zstepA; if_false; (* [comment removed for export] *)
           release_frame FR0 ST (bv_unsigned sp + -48);
           release_frame FR ST (bv_unsigned sp)
       end.
  all: lazymatch goal with |- evtA _ _ _ (MS ?Rg _ _ _ _ ?mx _) =>
         lazymatch type of HR with ?Rx _ _ ?uu =>
           apply evtA_done; unfold umd_post; exists r, uu, Rg; do 15 eexists; exists mx end end.
  all: split; [ unfold is_err, a_munmap_spin;
                first [ replace (18446744073709547520 <? bv_unsigned r) with false by (symmetry; apply (proj2 (Z.ltb_ge _ _)); lia)
                      | replace (18446744073709547520 <? bv_unsigned r) with true by (symmetry; apply (proj2 (Z.ltb_lt _ _)); lia) ];
                reflexivity |].
  all: split; [exact MU|].
  all: split; [first [intros _; assumption | intros; discriminate] |].
  all: split; [assumption|].
  all: split; [exact ST|].
  all: split; [exact (conj G1 (conj V1 (conj G2 V2)))|].
  all: exact HR.
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.
End UMD.
End RC__1.
