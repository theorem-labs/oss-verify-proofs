(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (one start-up certificate per value of the CONFIG_RSEQ flag, against the join and hand-off states AS/X0n2.v computes in the build, with the start-up shape computed in AS/X0lxR0.v and AS/X0lxR1.v). *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0m4 X0li X0lh X0ll X0ly X0lj X0kj X0lv X0n6 PlanRegen X0n2 X0lxR0 X0lxR1.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma IT0_ok : itab_sound ASEGS IT0.
Proof. apply APS.mk_itab_ranges_sound. Qed.

(** The start-up's shape at each flag: the two certificates are made in AS/X0lxR0.v and AS/X0lxR1.v,
    which compile side by side. *)
Definition startup_shape (r : Z) : shape := if Z.eqb r 1 then startup_shape_1 else startup_shape_0.

Set Default Proof Mode "Classic".

Lemma startup_cert : forall b : bool,
check ASEGS IT0 ASAN_A NX0 X0kj.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_asan (rseq_z b)) KC0 BFUEL FUEL None
      (asan_a_init (rseq_z b)) (su_plan (rseq_z b)) = COk (startup_shape (rseq_z b)).
Proof. intros [|]; [exact startup_cert1 | exact startup_cert0]. Qed.
