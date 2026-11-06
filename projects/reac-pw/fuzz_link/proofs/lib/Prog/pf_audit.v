From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require pf_top mwrite fmemopen memfile_place link_msgs_fit
  printf_core_heap_arm.

About pf_top.pf_mwrite.
Print Assumptions pf_top.pf_mwrite.
About mwrite.mwrite_flush.
Print Assumptions mwrite.mwrite_flush.
About pf_top.pf_mseek.
Print Assumptions pf_top.pf_mseek.
About pf_top.pf_fseeko.
Print Assumptions pf_top.pf_fseeko.
About pf_top.pf_rewind.
Print Assumptions pf_top.pf_rewind.
About pf_top.pf_vfprintf.
Print Assumptions pf_top.pf_vfprintf.
About pf_top.pf_fprintf.
Print Assumptions pf_top.pf_fprintf.
About fmemopen.fmemopen_w_holds.
Print Assumptions fmemopen.fmemopen_w_holds.
About memfile_place.mf_place_of_fresh.
Print Assumptions memfile_place.mf_place_of_fresh.
Print Assumptions link_msgs_fit.fit_emit_code.
Print Assumptions link_msgs_fit.fit_emit_read.
Print Assumptions link_msgs_fit.fit_emit_mark.
Print Assumptions link_msgs_fit.fit_mark_vlan.
Print Assumptions link_msgs_fit.fit_mark_host.
Print Assumptions link_msgs_fit.ifn_largest.
Print Assumptions printf_core_heap_arm.printf_core_heap_arm_ok.
Print Assumptions pf_top.mwrite_writes_avoid_g_say.
Print Assumptions pf_top.mseek_writes_avoid_g_say.
Print Assumptions pf_top.fseeko_writes_avoid_g_say.
Print Assumptions pf_top.rewind_writes_avoid_g_say.
Print Assumptions pf_top.vfprintf_writes_avoid_g_say.
Print Assumptions fmemopen_c.fmemopen_w_avoids_g_say.
