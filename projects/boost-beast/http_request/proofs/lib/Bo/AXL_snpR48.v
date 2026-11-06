(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim SymExec SymExec2X SymExec2SoundX SymRunX SymPackX RefMemcpyLib AgentLib.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AXL_snpDisc AXL_snpRun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Open Scope Z_scope. Import SX2. Import SX2S.
Definition R : Z := 48.
Definition reads := Eval vm_compute in (snp_reads R).
Definition script := Eval vm_compute in (snp_script R reads).
Definition run := Eval vm_compute in (snp_run script reads).
Definition car := Eval vm_compute in (carry (s_log (fst (fst run))) (snp_kn reads) []).
