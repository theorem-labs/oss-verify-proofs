(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac ZBridge.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import CidBits.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma class_id_chk30 : forall_rangeZ (fun s => class_id s <=? 30) 1 65536 = true.
Proof. vm_cast_no_check (eq_refl true). Qed.
Lemma class_id_le30 : forall size, 1 <= size <= 65536 -> 1 <= class_id size <= 30.
Proof.
  intros size Hs. pose proof (class_id_range size Hs) as [A _].
  pose proof (forall_rangeZ_spec (fun s => class_id s <=? 30) 1 65536 size class_id_chk30 ltac:(lia) ltac:(lia)) as C.
  cbv beta in C. apply Z.leb_le in C. lia.
Qed.
