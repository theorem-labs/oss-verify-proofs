(* Theorem Labs, 2026-10: CHECKS of pj_parse's image-A' walk at the batch kit's cut: the statements and cut / segment
   definitions printed with implicit arguments and no notations (no PI_prog_B / prh_img_B may appear), and the closure
   of every closed lemma. PORTED from the image-B' walk's lib/B/Prog/pj_parse_zcheck.v (sha256 b6e05c231b48; internal record).
   proves no function (kind: check file). No numeral. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PjParseA_defs PjParseA_glue PjParseA_counts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import
PjParseA_seg_ent PjParseA_seg_c1 PjParseA_seg_c2ok PjParseA_seg_ep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PjParseA_seg_c2ref PjParseA_top PjParseA_vac.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require PjParseA_skip PjParseA_inst.
Import ListNotations.
Local Open Scope Z_scope.

Set Printing Implicit. Unset Printing Notations.
Print tpj_parse_specX.
Print pjp_texts.
Print pjp_pre.
Print pjp_pos_pv.
Print pjp_outc.
Print pjp_Q.
Print pjp_FIN.
Print pjp_inv.
Print pjp_invR.
Print pjp_inj.
Print pjp_wb.
Print pjp_C1.
Print pjp_pv_out.
Print pjp_ftie.
Print pjp_C2ok.
Print pjp_C2ref.
Print pjp_C3.
Print pjp_seg_entry.
Print pjp_seg_C1.
Print pjp_seg_C2ok.
Print pjp_seg_C2ref.
Print pjp_seg_C3.
Print pjp_frame_kept_stmt.
Print pjp_g_vis.
Unset Printing Implicit. Set Printing Notations.
Print Assumptions pjp_cw_entry_A.
Print Assumptions PjParseA_vac.pjz_vac_univ_A.
Print Assumptions PjParseA_vac.pjz_vac_cw_A.
Print Assumptions PjParseA_skip.pjs_loop.
Print Assumptions PjParseA_inst.pjp_inst_pf.
Print Assumptions pjp_seg_entry_holds.
Print Assumptions pjp_seg_C1_holds.
Print Assumptions pjp_seg_C2ok_holds.
Print Assumptions pjp_seg_C3_holds.
Print Assumptions pjp_frame_kept_holds.
Print Assumptions pjp_glue_holds.
Print Assumptions pjp_g_univ_holds.
Print Assumptions PjParseA_counts.pjc_cnt_run_parse.
Print Assumptions PjParseA_counts.pjc_pkR_gtrace.
Print Assumptions PjParseA_counts.pjc_hull_budget_pv.
Print Assumptions PjParseA_counts.pjc_hull_budget_after_pv.
Print Assumptions PjParseA_counts.pjc_hull_used_pv.
Print Assumptions PjParseA_seg_c2ref.pjp_seg_C2ref_holds.
Print Assumptions PjParseA_top.pj_parse_holds_A0.
Print Assumptions PjParseA_top.pj_parse_holds_A.
Set Printing Implicit. Unset Printing Notations.
Check PjParseA_top.pj_parse_holds_A.
