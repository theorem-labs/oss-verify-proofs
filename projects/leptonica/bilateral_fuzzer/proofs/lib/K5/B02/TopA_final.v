(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (recorded (KReplay) proofs re-proved by tactics). *)
(* [comment removed for export] *)
From OSSVerify.leptonica.bilateral_fuzzer.images Require AsanUbsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Top Require Import TopLevelA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_rep D_libiface RT_gaps_iface RT_gaps_proof TopA_closed RT_fk_iface RT_fk_proof Bi_top Bi_fuzz Bi_fuzz_adapt.

(* THE ENCODED PROOF IS GONE: this file's [KReplay] replay applied the cone lemma WITH the kernel
   premise, which no longer exists, so the encoded term cannot typecheck.  The STATEMENT is this
   file's own, minus that premise; the PROOF is written out in the form the eight sibling trees
   state this same proof in (e.g. kernel_fuzzer K5/A17/TopA_final.v), with this tree's own cone
   arguments.  Nothing is re-encoded. *)
Theorem s3s_closed : topA_runseg_lift -> S3s_stmt AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof.
  intros RUNSEG.
  exact (s3s_of_conetop RUNSEG
           (fun RC GP => bi_cone_of_open RTA RC GP rta_fk_contracts (bi_fuzz_ok RTA) (bi_fuzz_adapt RTA))).
Qed.
