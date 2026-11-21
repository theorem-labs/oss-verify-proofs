(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import ITree Nodes Image Stage.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import TopLevel Obligations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prog ModelInv LB_Logic Unforced LB_Main ProgDetIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_compress_fuzzer_repro.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.World Require Import Tgt_compress_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma tsafe_noerr_no_enomem : forall {R} (t : itree node R) mo,
  tsafe nstep node_noerr t mo -> tsafe nstep no_enomem t mo.
Proof.
  intros R t. induction t as [r|n k IH]; intros mo H; cbn in *; [exact I|].
  destruct H as [Hn Hk]. split; [destruct n; exact Hn|]. intros rsp mo' evs Hst. apply IH. exact (Hk rsp mo' evs Hst).
Qed.

Theorem prog_no_enomem_any : forall segs rstage pc ph lim,
  segs_ok segs -> KLIM + SMALLREQ <= lim ->
  prog_no_enomem_stmt segs rstage pc ph lim.
Proof.
  intros segs rstage pc ph lim Hsegs Hlim en inp Hve Hvi.
  apply tsafe_noerr_no_enomem. exact (prog_noerr segs rstage pc ph lim Hsegs Hlim en inp Hve Hvi).
Qed.

Theorem prog_no_enomem_P_lim : forall lim, KLIM + SMALLREQ <= lim ->
  prog_no_enomem_stmt psegs pstage Src_zlib_compress_fuzzer_repro.M.init_pc Src_zlib_compress_fuzzer_repro.M.phdrs lim.
Proof. intros lim Hlim. apply prog_no_enomem_any; [exact segs_ok_psegs| exact Hlim]. Qed.

Theorem prog_no_enomem_P_2G :
  prog_no_enomem_stmt psegs pstage Src_zlib_compress_fuzzer_repro.M.init_pc Src_zlib_compress_fuzzer_repro.M.phdrs 0x80000000.
Proof. apply prog_no_enomem_P_lim. unfold KLIM, SMALLREQ. lia. Qed.

