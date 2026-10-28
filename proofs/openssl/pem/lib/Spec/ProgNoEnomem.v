(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ITree Nodes Image Stage.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Decode NodesCfg DecodeCfg.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.pem.lib Require Import TopLevel Obligations.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prog ModelInv LB_Logic UnforcedK LB_Main ProgDetIface.
From OssFuzzTheorems.openssl.pem.images Require Import Plain.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation nstep := NodesCfg.nstep_c (only parsing).
Open Scope Z_scope.

Lemma tsafe_noerr_no_enomem : forall {R} (t : itree node R) mo,
  tsafe nstep node_noerr t mo -> tsafe nstep no_enomem t mo.
Proof.
  intros R t. induction t as [r|n k IH|v k IH]; intros mo H; cbn in *; [exact I| |].
  - destruct H as [Hn Hk]. split; [destruct n; exact Hn|]. intros rsp mo' evs Hst. apply IH. exact (Hk rsp mo' evs Hst).
  - intros a Hv. apply IH. exact (H a Hv).
Qed.

Theorem prog_no_enomem_any : forall segs rstage pc ph lim,
  segs_low segs -> KLIM + SMALLREQ <= lim ->
  prog_no_enomem_stmt segs rstage pc ph lim.
Proof.
  intros segs rstage pc ph lim Hsegs Hlim en inp Hve Hvi.
  apply tsafe_noerr_no_enomem. exact (prog_noerr segs rstage pc ph lim Hsegs Hlim en inp Hve Hvi).
Qed.

Theorem prog_no_enomem_P :
  prog_no_enomem_stmt psegs pstage Plain.M.init_pc Plain.M.phdrs source_alloc_limit.
Proof. apply prog_no_enomem_any; [exact segs_low_psegs| unfold KLIM, SMALLREQ, source_alloc_limit; lia]. Qed.

Theorem prog_no_enomem_U :
  prog_no_enomem_stmt usegs ustage Ubsan.M.init_pc Ubsan.M.phdrs target_alloc_limit.
Proof. apply prog_no_enomem_any; [exact segs_low_usegs| unfold KLIM, SMALLREQ, target_alloc_limit; lia]. Qed.
