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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import XB_mmap_fixed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section X.
Variable P : acc -> Prop.
Hypothesis PDATA : forall a n, 0xa5000 <= a -> a + Z.of_nat n <= 0x603000 -> P (Z_to_bv 64 a, n).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dec_zs (A L : Z) (e : resp) : option (word * bool) :=
  match e with
  | mkEffectU r [] [] [] [] [] => Some (r, false)
  | mkEffectU r [] [z] [] [] [] =>
      if (bv_eqb (fst z) (Z_to_bv 64 A) && bv_eqb (snd z) (Z_to_bv 64 (mmap_len L)))%bool then Some (r, true) else None
  | _ => None
  end.

Lemma dec_zs_Some : forall A L e a, dec_zs A L e = Some a -> exists r u, a = (r, u) /\ e = zshape A L r u.
Proof.
  intros A L [r ws zs us cs ci] a H. unfold dec_zs in H.
  destruct ws; [|discriminate]. destruct zs as [|[za zn] [|]]; destruct us; try discriminate; destruct cs; try discriminate; destruct ci; try discriminate.
  - injection H as <-. exists r, false. split; reflexivity.
  - cbn [fst snd] in H. destruct (bv_eqb za (Z_to_bv 64 A)) eqn:E1; [|discriminate]. destruct (bv_eqb zn (Z_to_bv 64 (mmap_len L))) eqn:E2; [|discriminate].
    apply bv_eqb_eq in E1. apply bv_eqb_eq in E2. subst. injection H as <-. exists r, true. split; reflexivity.
Qed.

Lemma dec_zs_zshape : forall A L r u, dec_zs A L (zshape A L r u) = Some (r, u).
Proof.
  intros A L r u. destruct u; unfold zshape, dec_zs; cbn [fst snd]; [|reflexivity].
  rewrite !(proj2 (bv_eqb_eq _ _) eq_refl). reflexivity.
Qed.

Definition CHK_fixed_noreserve (A L : Z) (mo : Model) (eff : resp) : check_result :=
  check_mmap (Z_to_bv 64 A) (Z_to_bv 64 L) (Z_to_bv 64 3) (Z_to_bv 64 MAP_FIXED_NORESERVE_RW) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) eff mo.

Section SRZ.
Variables (S : word -> Prop) (N : nat) (EB : Z).

(* [comment removed for export] *)
Definition mfi_kernel_side (mo : Model) (A L : Z) : Prop :=
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

End X.
End RC__1.
