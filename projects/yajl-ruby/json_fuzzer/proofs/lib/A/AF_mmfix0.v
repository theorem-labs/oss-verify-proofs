(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import NodesCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SysStepA MmStep AImages AImageFacts LazyModel NodesA ImplRzA NodesA_mm.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.examples Require Import X_mmap_fixed X_mmap_fixed_srz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac from_lit_add :=
  repeat match goal with |- context [Z_to_bv 64 (?a + ?b)] => is_Zlit a; is_Zlit b;
    let v := eval vm_compute in (a + b) in change (Z_to_bv 64 (a + b)) with (Z_to_bv 64 v) end.

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
Section X0.
Variable P : acc -> Prop.
Hypothesis PDATA : forall a n, 0xa4000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).

(* [comment removed for export] *)
Lemma named_fd0_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 272 -> mem_inv asegs m ->
  statics m -> a0 = Z_to_bv 64 0 ->
  (forall a n, lo <= a -> a + Z.of_nat n <= bv_unsigned sp -> P (Z_to_bv 64 a, n)) ->
  evtA asegs P (named_fd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 a3 a4 a5 a6 a7 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 a_named_fd) fc None m (seg_rom asegs)).
Proof. aceil.
  intros until lo. intros ST LOC LO MI STA -> PSTK. unfold a_named_fd.
  aceil.
  open_statics STA.
  assert (MU : munch [(bv_unsigned sp - 272, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono asegs m m) by apply wmono_refl.
  carve_frame 272%nat ST.
  do 8 stepA.                                  (* [comment removed for export] *)
  stepA. stepA.                                (* [comment removed for export] *)
  zstepA. if_true.                             (* [comment removed for export] *)
  zstepA.                                      (* [comment removed for export] *)
  do 8 stepA.                                  (* [comment removed for export] *)
  stepA.                                       (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  finishA. close_statics.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac mfi_after_call rr :=
  do 2 stepA;                                   (* [comment removed for export] *)
  stepA;                                        (* [comment removed for export] *)
  stepA;                                        (* [comment removed for export] *)
  stepA;                                        (* [comment removed for export] *)
  zstepA; zstepA;                               (* [comment removed for export] *)
  zstepA; let K := fresh "K" in if_cases K; zify_cond K.   (* [comment removed for export] *)
Ltac mfi_noerr rr :=
  zstepA;                                       (* [comment removed for export] *)
  replace (18446744073709547520 <? bv_unsigned rr) with false
    by (first [apply (proj2 (Z.ltb_ge _ _)) | symmetry; apply (proj2 (Z.ltb_ge _ _))]; lia);
  cbn [Z.b2z];
  stepA;                                        (* [comment removed for export] *)
  stepA;                                        (* [comment removed for export] *)
  zstepA; if_true.                              (* [comment removed for export] *)
Ltac mfi_err rr :=
  zstepA; let K1 := fresh "K" in if_cases K1; zify_cond K1; [exfalso; lia|];   (* [comment removed for export] *)
  zstepA; zstepA;                               (* [comment removed for export] *)
  zstepA;                                       (* [comment removed for export] *)
  replace (18446744073709547520 <? bv_unsigned rr) with true
    by (first [apply (proj2 (Z.ltb_lt _ _)) | symmetry; apply (proj2 (Z.ltb_lt _ _))]; lia);
  cbn [Z.b2z];
  stepA; stepA;                                 (* [comment removed for export] *)
  zstepA; if_false.                             (* [comment removed for export] *)
Ltac mfi_grant_tail FR ST sp :=
  stepA; stepA;                                 (* [comment removed for export] *)
  do 2 stepA;                                   (* [comment removed for export] *)
  zstepA;                                       (* [comment removed for export] *)
  zstepA; if_true;                              (* [comment removed for export] *)
  stepA;                                        (* [comment removed for export] *)
  stepA;                                        (* [comment removed for export] *)
  zstepA;                                       (* [comment removed for export] *)
  do 6 stepA;                                   (* [comment removed for export] *)
  stepA;                                        (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
Ltac mfi_finish_common :=
  split; [ eapply munch_weaken; [|eassumption]; intros y; cbn; lia |];
  split; [assumption|]; split; [assumption|]; split; [assumption|];
  split; [close_statics|];
  split; [ first [intros _; assumption | intros; discriminate] | assumption ].
Ltac mfi_finish_ret rr u :=
  lazymatch goal with |- evtA _ _ _ (MS ?R ?F ?pc ?fc _ ?m _) =>
    apply evtA_done; unfold mmap_fixed_impl_post; exists rr, u, R; do 14 eexists; exists m end;
  split; [ unfold is_err; replace (18446744073709547520 <? bv_unsigned rr) with false
             by (first [apply (proj2 (Z.ltb_ge _ _)) | symmetry; apply (proj2 (Z.ltb_ge _ _))]; lia); reflexivity |];
  mfi_finish_common.
Ltac mfi_finish_spin rr u :=
  lazymatch goal with |- evtA _ _ _ (MS ?R ?F ?pc ?fc _ ?m _) =>
    apply evtA_done; unfold mmap_fixed_impl_post; exists rr, u, R; do 14 (exists rr); exists m end;
  split; [ unfold is_err, a_mmap_fixed_spin; replace (18446744073709547520 <? bv_unsigned rr) with true
             by (first [apply (proj2 (Z.ltb_lt _ _)) | symmetry; apply (proj2 (Z.ltb_lt _ _))]; lia); reflexivity |];
  mfi_finish_common.
Ltac mfi_errno_tail FR ST sp :=
  do 2 stepA;                                   (* [comment removed for export] *)
  zstepA; if_false;                             (* [comment removed for export] *)
  do 2 stepA;                                   (* [comment removed for export] *)
  zstepA;                                       (* [comment removed for export] *)
  zstepA; if_false;                             (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).

(* [comment removed for export] *)

Section SRZ.
Variables (S : word -> Prop) (N : nat) (EB : Z).

(* [comment removed for export] *)
Definition mfi0_kernel_side (mo : Model) (A L : Z) : Prop :=
  forall mo1, magree mo mo1 -> KIA S N EB mo1 ->
    (forall eff, CHK_fixed_noreserve A L mo1 eff <> CheckUnmodeled)
    /\ (exists eff mo', CHK_fixed_noreserve A L mo1 eff = CheckOk mo' []
                        /\ node_refusal (NMmap A L 3 MAP_FIXED_NORESERVE_RW) mo1 (eff_ret eff) = false)
    /\ (forall eff mo', CHK_fixed_noreserve A L mo1 eff = CheckOk mo' [] ->
          node_refusal (NMmap A L 3 MAP_FIXED_NORESERVE_RW) mo1 (eff_ret eff) = false ->
          exists r, eff = zshape A L r true /\ is_err r = false     (* [comment removed for export] *)
          /\ exists (S' : word -> Prop) (N' : nat) (EB' : Z),
               LI S' N' EB' mo' /\ (forall x, P x -> acc_ok (m_vm_lazy mo') S' x)).

(* [comment removed for export] *)
End SRZ.
End X0.
End RC__1.
