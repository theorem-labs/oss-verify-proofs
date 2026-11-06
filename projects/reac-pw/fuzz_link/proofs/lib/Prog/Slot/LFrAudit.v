(* Audit of the slot's SR frame (S-FR items 1-8): the statement (About: its Section arguments, the callee
   contracts among them) and the assumptions of each top lemma. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require
  LFr LFrRun LFrLo LFrCall LFrAl LFrTx LFrMqDefs LFrMq LFrPo LFrEn.

About LFr.LFF_of_plain.
Print Assumptions LFr.LFF_of_plain.
About LFr.lroom.
Print Assumptions LFr.lroom.
About LFr.cut_close.
Print Assumptions LFr.cut_close.
About LFr.cut_open.
Print Assumptions LFr.cut_open.

About LFrRun.lfr_run.
Print Assumptions LFrRun.lfr_run.
About LFrRun.lfr_own.
Print Assumptions LFrRun.lfr_own.
About LFrRun.cut_evt.
Print Assumptions LFrRun.cut_evt.
About LFrRun.cut_evt_or.
Print Assumptions LFrRun.cut_evt_or.

About LFrLo.lh_mem_carry.
Print Assumptions LFrLo.lh_mem_carry.
About LFrLo.lh_reg_keep.
Print Assumptions LFrLo.lh_reg_keep.

About LFrCall.lfr_call.
Print Assumptions LFrCall.lfr_call.
About LFrCall.lfr_call_core.
Print Assumptions LFrCall.lfr_call_core.
About LFrAl.lfr_calloc.
Print Assumptions LFrAl.lfr_calloc.
About LFrAl.lfr_free.
Print Assumptions LFrAl.lfr_free.
About LFrAl.lfr_free_null.
Print Assumptions LFrAl.lfr_free_null.
About LFrTx.lfr_text_buf.
Print Assumptions LFrTx.lfr_text_buf.
About LFrTx.lfr_text_of.
Print Assumptions LFrTx.lfr_text_of.
About LFrMq.lfr_mark.
Print Assumptions LFrMq.lfr_mark.
About LFrMq.lfr_mark_ok.
Print Assumptions LFrMq.lfr_mark_ok.

About LFrPo.cut_post.
Print Assumptions LFrPo.cut_post.
About LFrPo.cut_post_cfg.
Print Assumptions LFrPo.cut_post_cfg.
About LFrPo.cut_post_lib.
Print Assumptions LFrPo.cut_post_lib.
About LFrPo.lpost_T_mf.
Print Assumptions LFrPo.lpost_T_mf.

About LFrEn.lfr_init.
Print Assumptions LFrEn.lfr_init.
About LFrEn.cut_entry.
Print Assumptions LFrEn.cut_entry.
