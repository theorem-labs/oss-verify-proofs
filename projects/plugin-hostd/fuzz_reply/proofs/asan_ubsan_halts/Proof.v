From OSSVerify.plugin_hostd.fuzz_reply Require Statements.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AsanTop.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyBTop.

(* Image B (ASan-UBSan): lib/B/ReplyBTop.v's replyb_TFIB_B_T (the composed theorem with both proved allocator targets
   applied) through lib/A/AsanTop.v. *)
Theorem asan_ubsan_halts_holds : Statements.asan_ubsan_halts.
Proof. exact (AsanTop.reply_asan_ubsan_halts_of_tfib ReplyBTop.replyb_TFIB_B_T). Qed.
