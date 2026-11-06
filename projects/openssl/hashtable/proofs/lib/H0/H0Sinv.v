(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CxPlan CxPlanSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Definition NX0t : nat := 12.

Section TailSinv.
  Variables usp STR0 : Z.

  Definition SINVt (E : env) (M : word -> option byte) : Prop :=
    uE E e_sp0 = usp /\ uE E e_str0 = STR0
    /\ edenot E (EVar V_L0) = Z_to_bv 64 0 /\ edenot E (EVar V_ARGC) = Z_to_bv 64 1 /\ edenot E (EVar V_L1) = Z_to_bv 64 0
    /\ eb E 1%nat = [] /\ eb E 2%nat = []
    /\ uE E e_pgsp = pgdown usp
    /\ M (Z_to_bv 64 STR0) = Some (Z_to_bv 8 0).

  Definition argHt (E : env) (a : word) : bool := Z.eqb (bv_unsigned a) STR0.

  Hypothesis Husp : 0x7fff80000000 <= usp.
  Hypothesis Hstr : usp + 192 <= STR0 < 2 ^ 47 - 32.

  Lemma argHt_high : forall E (a : word), argHt E a = true -> CEIL <= bv_unsigned a /\ usp <= bv_unsigned a.
  Proof. intros E a H. unfold argHt in H. apply Z.eqb_eq in H. unfold CEIL. lia. Qed.

  Lemma argHt_agree : forall E E' (a : word), env_agree NX0t E E' -> argHt E a = argHt E' a.
  Proof. reflexivity. Qed.

  Lemma SINVt_frame : forall E M M', (forall a, argHt E a = true -> M' a = M a) -> SINVt E M -> SINVt E M'.
  Proof.
    intros E M M' Hf (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). repeat (split; [assumption|]).
    rewrite Hf; [exact H9|]. unfold argHt. apply Z.eqb_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small; lia.
  Qed.

  Lemma SINVt_agree : forall E E' M, env_agree NX0t E E' -> SINVt E M -> SINVt E' M.
  Proof.
    intros E E' M Hag (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). pose proof Hag as [_ Heb].
    unfold SINVt, uE. rewrite <- !(edenot_agree NX0t E E' _ Hag) by reflexivity. rewrite <- Heb.
    repeat (split; [assumption|]). exact H9.
  Qed.

  Lemma SINVt_pgsp : forall E M, SINVt E M -> uE E e_pgsp = pgdown usp.
  Proof. intros E M H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H)))))))). Qed.
End TailSinv.
