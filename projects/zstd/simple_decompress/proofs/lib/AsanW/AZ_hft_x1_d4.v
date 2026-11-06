(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import ZdSeqTable ZdSeqBuildThm.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition d4k (sv nb : Z) : Z := 281479271743489 * nb + 72058693566333184 * sv.
Lemma d4k_bytes : forall sv nb, 0 <= sv < 256 -> 0 <= nb < 256 ->
  d4k sv nb mod 2 ^ 64 = d4k sv nb /\
  d4k sv nb mod 256 = nb /\ (d4k sv nb / 256) mod 256 = sv /\ (d4k sv nb / 65536) mod 256 = nb /\ (d4k sv nb / 16777216) mod 256 = sv /\
  (d4k sv nb / 4294967296) mod 256 = nb /\ (d4k sv nb / 1099511627776) mod 256 = sv /\ (d4k sv nb / 281474976710656) mod 256 = nb /\
  (d4k sv nb / 72057594037927936) mod 256 = sv.
Proof.
  set (chk := fun sv nb => let D := d4k sv nb in
     (D mod 2 ^ 64 =? D) && (D mod 256 =? nb) && ((D / 256) mod 256 =? sv) && ((D / 65536) mod 256 =? nb) && ((D / 16777216) mod 256 =? sv)
     && ((D / 4294967296) mod 256 =? nb) && ((D / 1099511627776) mod 256 =? sv) && ((D / 281474976710656) mod 256 =? nb) && ((D / 72057594037927936) mod 256 =? sv)).
  assert (B : forallb (fun sv => forallb (fun nb => chk sv nb) (ZdSeqTable.zseq 256 0)) (ZdSeqTable.zseq 256 0) = true) by (vm_compute; reflexivity).
  intros sv nb Hs Hn. rewrite forallb_forall in B. specialize (B sv ltac:(apply ZdSeqBuildThm.zseq_In_iff; lia)).
  rewrite forallb_forall in B. specialize (B nb ltac:(apply ZdSeqBuildThm.zseq_In_iff; lia)). unfold chk in B. cbv zeta in B.
  repeat (apply andb_prop in B; destruct B as [B ?]).
  repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H end.
  repeat split; assumption.
Qed.
