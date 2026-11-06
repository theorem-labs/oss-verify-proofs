(* fuzz_preset, the crt102 walk: the B' WRONG-INSTANCE CHECK (the family lead's rule, 2026-10-29).
   int102's lib/B/Prog/S1ImgB.v Requires lib/A/Prog/S1ImgA.v, so image A's PAImg instance PI_prog_A is in scope in every
   B' file that imports S1ImgB, and an unpinned implicit PA can resolve to it while every name reads B'. This file prints,
   with implicit arguments shown and notations off, the statement of every exported lemma of this lane's two B' files
   (Crt102KitB.v and CrtImgB102.v); the reader checks that every PA / PI argument names the B' instance (PI_prog_B,
   prh_img_B) and that no PI_prog_A / prh_img_A appears. It proves nothing and is read from the build log.
   Inputs of record: as Crt102Glue.v's header. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Crt102KitB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require CrtImgB102.

Set Printing Implicit.
Unset Printing Notations.
Check @Crt102KitB.cb4_fb.
Check @Crt102KitB.cb4_sp.
Check @Crt102KitB.cb4_ar0.
Check @Crt102KitB.cb4_ff.
Check @Crt102KitB.cb4_doc_home.
Check @Crt102KitB.cb4_ro_img.
Check @Crt102KitB.cb4_fregs_trans.
Check @Crt102KitB.cb4_chain.
Check @Crt102KitB.cb4_live_call.
Check @Crt102KitB.cb4_live_mono.
Check @Crt102KitB.cb4_stkc.
Check @Crt102KitB.cb4_rdword_of_val_mem.
Check @Crt102KitB.cb4_fpchain_keep.
Check @CrtImgB102.HB_base_cf.
Check @CrtImgB102.HB_entry_cf.
Check @CrtImgB102.HB_segs_cf.
Check @CrtImgB102.HB_relro_cf.
Check @CrtImgB102.HB_hi_cf.
Check @CrtImgB102.crt_pc_B_cf.
Check @CrtImgB102.crt_cut_pc_B_cf.
Check @CrtImgB102.crt_at_B_cf.
Check @CrtImgB102.crt_abort_B_cf.
Check @CrtImgB102.crt_str_res_B_cf.
Check @CrtImgB102.crt_str_rom_b_B_cf.
Check @CrtImgB102.crt_str_rom_B_cf.
Check @CrtImgB102.crt_got_B_cf.
Check @CrtImgB102.crt_pst_img_B_cf.
Check @CrtImgB102.crt_pst_ro_B_cf.
Check @CrtImgB102.crt_pa_hi_B_cf.
Check @Crt102KitB.cb_J_B_ccnt24.

(* the Records of the glue (the crt102 walk, 2026-10-30): each projection's implicit arguments, so a reader can see that a
   field is read as `crt_live_side HL` with every parameter inferred from HL *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Crt102Glue.
About Crt102Glue.crt_live_side.
About Crt102Glue.crt_side_ledger.
About Crt102Glue.crt_pos_ex.
About Crt102Glue.crt_pos_room.
About Crt102Glue.crt_at_J_B_r0.
About Crt102Glue.crt_at_J_B_count.
About Crt102Glue.crt_at_L3_B_live.
About Crt102Glue.mk_crt_live.
