(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import ITree Nodes Image Stage.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib Require Import TopLevel Obligations.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prog ModelInv LB_Logic Unforced LB_Main ProgDetIface.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma tsafe_noerr_no_enomem : forall {R} (t : itree node R) mo,
  tsafe nstep node_noerr t mo -> tsafe nstep no_enomem t mo.
Proof.
  intros R t. induction t as [r|n k IH|kc IHc]; intros mo H; cbn in *; [exact I| |intros z; apply IHc; apply H].
  destruct H as [Hn Hk]. split; [destruct n; exact Hn|]. intros rsp mo' evs Hst. apply IH. exact (Hk rsp mo' evs Hst).
Qed.

Lemma tsafe_noerr_unforced : forall {R} (t : itree node R) mo,
  tsafe nstep node_noerr t mo -> tsafe nstep unforced t mo.
Proof. intros R t mo H. exact (tsafe_mono nstep no_enomem unforced t mo no_enomem_unforced (tsafe_noerr_no_enomem t mo H)). Qed.

Theorem prog_no_enomem_any : forall segs rstage pc ph lim,
  segs_pu segs -> KLIM + SMALLREQ <= lim ->
  prog_no_enomem_stmt segs rstage pc ph lim.
Proof.
  intros segs rstage pc ph lim Hsegs Hlim en inp Hve Hvi.
  apply tsafe_noerr_no_enomem. exact (prog_noerr segs rstage pc ph lim Hsegs Hlim en inp Hve Hvi).
Qed.

Definition prog_unforced_stmt (sg : list Segment) (stg : Z) (pc0 : N) (phi : PhdrInfo) (cap : Z) : Prop :=
  forall e i, valid_entry (mkImage sg pc0 phi) e i -> valid_input_either i ->
    tsafe nstep unforced (the_prog sg stg i e) (mo0 sg cap e i).

Theorem prog_unforced_any : forall segs rstage pc ph lim,
  segs_pu segs -> KLIM + SMALLREQ <= lim ->
  prog_unforced_stmt segs rstage pc ph lim.
Proof.
  intros sg stg pc0 phi cap Hpu Hcap e i He Hi.
  refine (tsafe_mono nstep no_enomem unforced _ _ no_enomem_unforced _).
  exact (prog_no_enomem_any sg stg pc0 phi cap Hpu Hcap e i He Hi).
Qed.

Theorem prog_no_enomem_P :
  prog_no_enomem_stmt psegs pstage Plain.M.init_pc Plain.M.phdrs source_alloc_limit.
Proof. apply prog_no_enomem_any; [apply segs_pu_P| unfold KLIM, SMALLREQ, source_alloc_limit; lia]. Qed.

Theorem prog_no_enomem_U :
  prog_no_enomem_stmt usegs ustage Ubsan.M.init_pc Ubsan.M.phdrs target_alloc_limit.
Proof. apply prog_no_enomem_any; [apply segs_pu_U| unfold KLIM, SMALLREQ, target_alloc_limit; lia]. Qed.
