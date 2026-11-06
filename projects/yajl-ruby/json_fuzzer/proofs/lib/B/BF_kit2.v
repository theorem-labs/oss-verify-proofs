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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac cstep := stepA; try first [if_true | if_false].

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
Section Walk.
Variable P : acc -> Prop.

Definition gcts_post (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo T : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (T + 2800)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma gcts_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo TSD CTX T : Z),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m ->
  thread_cells m tp TSD CTX T -> 0xa5000 <= TSD -> TSD + 8 <= 0x603000 -> 0 < CTX -> CTX + 4096 <= alloc_ceiling -> 0 < T < 2^47 ->
  0xa5000 + 88 <= bv_unsigned tp < 0x603000 ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  (forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->
  P (Z_to_bv 64 (CTX + 152), 8%nat) ->
  evtA bsegs P (gcts_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo T)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5c878) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until T. intros ST LOC LO SPH MI (TC1 & TC2 & TC3 & TC4 & TC5) HT1 HT2 HC1 HC2 HT HTP PSTK PDAT P3.
  pose proof LOC as LOC0. aceil.
  assert (MU : munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 16%nat ST.
  do 3 cstep.           (* [comment removed for export] *)
  call_spA (get_current_thread_walk P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo TSD CTX T);
    [exact ST| exact LOC0| lia| lia| exact MI| exact (conj TC1 (conj TC2 (conj TC3 (conj TC4 TC5))))| exact HT1| exact HT2| exact HC1| aceil; lia
    | lia| exact HTP| intros; apply PSTK; lia| exact PDAT| exact P3|].
  zstepA. if_cases K0; zify_cond K0. { exfalso. revert K0. rewrite ?unsigned_lit by lia. lia. }   (* [comment removed for export] *)
  rename POST into ST.
  do 4 cstep.           (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  cstep.                (* [comment removed for export] *)
  replace (T + 2047 + 753) with (T + 2800) by lia.
  finishA.
Qed.

Lemma rss_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv bsegs m -> rw_cells bsegs m 0x130822 [C1 (Z_to_bv 8 0)] ->                   (* [comment removed for export] *)
  (forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (leaf_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m 0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5fc64) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until m. intros MI G PDAT.
  do 4 cstep.
  finishA.
Qed.

(* [comment removed for export] *)
Lemma lsan_dis_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv bsegs m -> rw_cells bsegs m 0xa61f8 [C8 (Z_to_bv 64 0x10)] ->
  rw_cells bsegs m (bv_unsigned tp + 16) [C4 (Z_to_bv 64 0)] -> 0xa5000 <= bv_unsigned tp /\ bv_unsigned tp + 20 <= 0x603000 ->
  (forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (leaf_post ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m 0)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x81270) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until m. intros MI G TPC TPR PDAT.
  pose proof (bv_unsigned_in_range _ tp) as TR.
  do 2 cstep.                         (* [comment removed for export] *)
  cstep.                              (* [comment removed for export] *)
  replace (16 + bv_unsigned tp) with (bv_unsigned tp + 16) by lia || idtac.
  cstep.                              (* [comment removed for export] *)
  change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  do 2 cstep.                         (* [comment removed for export] *)
  finishA.
Qed.

(* [comment removed for export] *)
Definition rmh_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (a0 a1 a2 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma rmh_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp <= 2^47 ->
  mem_inv bsegs m -> rw_cells bsegs m 0x140080 [C8 (Z_to_bv 64 0)] ->                     (* [comment removed for export] *)
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  (forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n)) ->
  evtA bsegs P (rmh_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x61e80) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until lo. intros ST LOC LO SPH MI HK PSTK PDAT.
  pose proof LOC as LOC0. aceil.
  assert (MU : munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  carve_frame 32%nat ST.
  do 7 cstep.           (* [comment removed for export] *)
  cstep. cstep.         (* [comment removed for export] *)
  do 3 cstep.           (* [comment removed for export] *)
  cstep.                (* [comment removed for export] *)
  do 5 cstep.           (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  cstep.                (* [comment removed for export] *)
  finishA.
Qed.

End Walk.
End RC__1.
