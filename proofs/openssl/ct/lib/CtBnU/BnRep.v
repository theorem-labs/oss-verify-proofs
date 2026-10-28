(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image Arr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Export MallocRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Export HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Export ApRepDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition LIBW_bn : list (Z * Z) :=
  [(2895512, 3241008); (3241008, 3270448); (3270808, 3270992); (3276176, 3277680); (3344080, 3354968); (3355026, 3355027); (3355080, 3355096); (3490128, 3491248)]%Z.
Definition libw (a : Z) : Prop := rin_ivs LIBW_bn a.

From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require HxpInit.
Lemma LIBW_bn_eq : LIBW_bn = HxpInit.LIBW_HX.
Proof. reflexivity. Qed.

Ltac in_libw := intros ? ?; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; cbn in *; lia.

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma ro_cells_agree : forall P m m' A cs,
  agree_on P m m' -> ro_cells ctusegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  ro_cells ctusegs m' A cs.
Proof.
  intros P m m' A cs HP [Hwf HB] HR. split; [exact Hwf|].
  eapply bytes_at_agree; eauto. rewrite cells_bytes_length by assumption. exact HR.
Qed.

Lemma crypto_statics_agree : forall P m m', agree_on P m m' -> (forall a, libw a -> P a) -> crypto_statics m -> crypto_statics m'.
Proof.
  intros P m m' AG HP (H1 & H2 & H3 & H4 & H5 & H6).
  unfold crypto_statics, CR_GOT_MALLOC, CR_GOT_FREE, CR_MEMSET_FUNC, CR_MALLOC_IMPL, CR_FREE_IMPL, CR_NO_CUSTOMIZE in *.
  repeat split; (eapply ro_cells_agree; [exact AG| eassumption|]); intros a Ha; apply HP; revert a Ha; in_libw.
Qed.
End WithCeiling0.
