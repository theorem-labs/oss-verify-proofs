(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim SjModel AtpModel OdModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Atp_h_defs Sj_h_arith Od_pro.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma od_els_shape : forall D d, exists P0 rest,
  od_els D d = (P0, zlength (od_s0 d)) :: rest /\ (P0 = 0 /\ od_s0 d = [] \/ P0 = D + 1 + Z.of_nat 0) /\ od_s0 d = firstn (length (od_s0 d)) (tl d).
Proof.
  intros D d. unfold od_els, od_P, od_s0, od_parts, od_rest. set (d' := tl d).
  pose proof (poffs_length d') as PL. pose proof (poffs_parts d') as PP.
  destruct (poffs d') as [|[o0 n0] tl0] eqn:EP.
  - cbn in PP. rewrite <- PP. cbn. exists 0, []. split; [reflexivity|]. split; [left; split; reflexivity| reflexivity].
  - assert (O0 : o0 = 0%nat).
    { rewrite poffs_eq in EP. destruct d' as [|c l]; [discriminate|]. rewrite poffs_of_unfold in EP. destruct (find_sep (c :: l)); congruence. }
    subst o0. rewrite <- PP. cbn [map nth fst snd skipn].
    assert (LN0 : (n0 <= length d')%nat) by (pose proof (poffs_bound d' (0%nat, n0) ltac:(rewrite EP; left; reflexivity)) as B; cbn in B; lia).
    assert (ZL : zlength (firstn n0 d') = Z.of_nat n0) by (unfold zlength; rewrite firstn_length; lia).
    rewrite ZL. replace (length (firstn n0 d')) with n0 by (rewrite firstn_length; clear - LN0; lia).
    cbn [map app pview fst snd]. do 2 eexists. split; [reflexivity|]. split; [right; reflexivity| reflexivity].
Qed.

Lemma od_sbuf_size_eq : forall L, 0 <= L < 2^32 ->
  Z.land (Z.land (Z.shiftl (Z.shiftr (L * 2863311531) 33) 2 + Z.shiftr (L * 2863311531) 33 + 127) 18446744073709551615) 18446744073709551552 = OD_SBUF L.
Proof. intros L H. unfold OD_SBUF. exact (sbuf_size_eq L H). Qed.
