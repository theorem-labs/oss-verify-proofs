(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Malloc MI_Inv MI_Cnt LB_Tables LB_Inv LB_Sum LB_StmtA LB_Raw.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition W : Z := 2^24 + 1.
Definition AMBC : Z := 8.
Definition Pcap (c : Z) : Z :=
if c =? 63 then AMBC
else if (0 <=? c) && (c <? 48) then AMBC
else 0.
Definition RBIG : Z := 3 * (2^26 + 8192) + 5 * W + (24 * 2^24 + 8192).
Lemma PHI_Pcap_eq : PHI Pcap = 231057408.
Proof. vm_compute. reflexivity. Qed.
Lemma PHI_Pcap : PHI Pcap + RBIG <= LBUDGET.
Proof. rewrite PHI_Pcap_eq. unfold RBIG, W, LBUDGET. cbn. lia. Qed.
