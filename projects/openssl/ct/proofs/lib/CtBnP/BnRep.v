(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Image Arr.
From OSSVerify.Proofs.openssl.ct.lib.Malloc Require Export MallocRep.
From OSSVerify.Proofs.openssl.ct.lib.CtP Require Import Lib_iface Lib_kit.
From OSSVerify.Proofs.openssl.ct.lib.CtHXP Require Export HxpFacts.
From OSSVerify.Proofs.openssl.ct.lib.CtRepP Require Export ApRepDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition LIBW_bn : list (Z * Z) :=
  [(2609984, 2955912); (2955912, 2985352); (2985728, 2985912); (2991096, 2992176); (3058576, 3069464); (3069522, 3069523); (3069576, 3069592); (3204624, 3205744)]%Z.
Definition libw (a : Z) : Prop := rin_ivs LIBW_bn a.

From OSSVerify.Proofs.openssl.ct.lib.CtHXP Require HxpInit.
Lemma LIBW_bn_eq : LIBW_bn = HxpInit.LIBW_HX.
Proof. reflexivity. Qed.

Ltac in_libw := intros ? ?; unfold libw, LIBW_bn; cbn [rin_ivs fst snd]; cbn in *; lia.

From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.ct.lib.P Require Import Rnd.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma ro_cells_agree : forall P m m' A cs,
  agree_on P m m' -> ro_cells ctpsegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) ->
  ro_cells ctpsegs m' A cs.
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
