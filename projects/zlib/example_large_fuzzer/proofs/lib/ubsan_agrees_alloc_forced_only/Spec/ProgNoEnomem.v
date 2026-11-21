(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Image Stage.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import TopLevel Obligations.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prog ModelInv LB_Logic Unforced LB_Main ProgDetIface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_example_large_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_example_large_fuzzer_ubsan.
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

Theorem prog_no_enomem_P :
  prog_no_enomem_stmt psegs pstage Src_zlib_example_large_fuzzer_repro.M.init_pc Src_zlib_example_large_fuzzer_repro.M.phdrs source_alloc_limit.
Proof. apply prog_no_enomem_any; [exact segs_ok_psegs| unfold KLIM, SMALLREQ, source_alloc_limit; lia]. Qed.

(* [comment removed for export] *)

Theorem prog_no_enomem_U :
  prog_no_enomem_stmt usegs ustage Tgt_example_large_fuzzer_ubsan.M.init_pc Tgt_example_large_fuzzer_ubsan.M.phdrs target_alloc_limit.
Proof. apply prog_no_enomem_any; [exact segs_ok_usegs| unfold KLIM, SMALLREQ, target_alloc_limit; lia]. Qed.
