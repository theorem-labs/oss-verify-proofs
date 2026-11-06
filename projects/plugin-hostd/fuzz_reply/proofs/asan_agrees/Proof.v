From OSSVerify.plugin_hostd.fuzz_reply Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyATopX.

(* Compiles when lib/A/ReplyATopX.v (a Theorem Labs lane's DRIVER_CF plug over W8's fr_contract_top_x) has no open premise left:
   top_x's remaining hypotheses, the Variables LSx / RINV and a Theorem Labs lane's allocator realizers. *)
Theorem asan_agrees_holds : Statements.asan_agrees.
Proof. exact ReplyATopX.asan_agrees_x. Qed.
