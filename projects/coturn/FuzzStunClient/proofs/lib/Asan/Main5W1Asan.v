(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the W1 tree is one per launch rseq layout, collected from that layout's hand-off template HG1_r and decided in Main5W1AsanR0.v and Main5W1AsanR1.v, and the released tree moved to W1TreeA.v with its recorded certificates removed. *)
(* One W1 tree per launch layout r, collected from that layout's hand-off template [HG1_r rsb] and
   decided per r in Main5W1AsanR1.v / Main5W1AsanR0.v; the recorded certificates Main5W1AsanCerts0..7.v of the
   r-free tree are gone. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefs MainGlue ItabAsan VarShift MainCol TOTmplRAsan M5TmplRAsan TreeColA W1TreeA Main5W1AsanR1 Main5W1AsanR0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition TW1 (rsb : bool) : mtree := if rsb then TW1_A1 else TW1_A0.
Lemma TW1_ok : forall rsb, mtree_ok (rsb := rsb) 0%nat 400000%nat 5000%nat IT_asan 1%nat 1%nat (HG1_r rsb) ((root_class 5) ++ [(QFlen, 65535 + 1, QMAX)]) (TW1 rsb) = true.
Proof. intros [|]; [exact TW1_ok1 | exact TW1_ok0]. Qed.
