(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses from the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id): the image record of lib/AU/HPgCallsSFU.v's Section sf at headamp's own image B, and the five soft-float
   statements of lib/AU/HPgM3dSFU.v proved closed. Proves no function (kind: instance discharge).

   IMG is lib/CJ/RL/I/IImgB.v's N_img: the CJ library's keys mapped to image B's addresses, over lib/AU/Img0U.v's
   rsegs. The symbol facts hold by computation on N_sym: the five routines (HK_EXT .. HK_LT) and the four further
   keys __subtf3's contract reads (__addtf3 0x85950, __fe_getround 0x8611c, __fe_raise_inexact 0x8614c and
   __fe_getround's rounding table 0x21538). The five CJ contracts at N_img are lib/CJ/RL/I/InstB.v's instances.

   hsfu_<routine>_stmt is lib/AU/HPgM3dSFU.v's hvu_sf_<routine>_stmt, exactly that type, under the walk's own Section
   data (fx, rc, SK, B, MT and MTL : ameter_laws MT); hsfu_stmts is their conjunction hvu_sf_stmts. The six calls
   of image B's value piece take them as follows (each at its own return address ret):
     0x835cc __extendsftf2, ra 0x835d0: hsfu_ext_stmt      0x83624 __subtf3, ra 0x83628: hsfu_sub_stmt
     0x83600 __gttf2,       ra 0x83604: hsfu_ge_stmt       0x83638 __getf2,  ra 0x8363c: hsfu_ge_stmt
     0x83610 __floatditf,   ra 0x83614: hsfu_fd_stmt       0x83650 __lttf2,  ra 0x83654: hsfu_lt_stmt *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YK0i YK1b YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.Reloc Require RStep.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.G Require C_extendsftf2 C_floatditf G_subtf3 G_getf2 G_letf2.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.I Require IImgB InstB.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgM3dSFU HPgCallsSFU.
Local Open Scope Z_scope.

(* ======================================== IMG and HIMG ======================================== *)
Lemma hsfu_img_segs : @RStep.img_segs IImgB.N_img = rsegs.
Proof. reflexivity. Qed.

(* ======================================== the symbol facts ======================================== *)
Lemma hsfu_k_ext : @RStep.sym IImgB.N_img 0x200dc = HVU_SF_EXT.
Proof. vm_compute. reflexivity. Qed.
Lemma hsfu_k_fd : @RStep.sym IImgB.N_img 0x7f000900 = HVU_SF_FD.
Proof. vm_compute. reflexivity. Qed.
Lemma hsfu_k_sub : @RStep.sym IImgB.N_img 0x1bc70 = HVU_SF_SUB.
Proof. vm_compute. reflexivity. Qed.
Lemma hsfu_k_ge : @RStep.sym IImgB.N_img 0x1b314 = HVU_SF_GE.
Proof. vm_compute. reflexivity. Qed.
Lemma hsfu_k_lt : @RStep.sym IImgB.N_img 0x1b24c = HVU_SF_LT.
Proof. vm_compute. reflexivity. Qed.
(* __subtf3 runs into __addtf3 0x85950, which calls __fe_getround 0x8611c (its table 0x21538) and
   __fe_raise_inexact 0x8614c. *)
Lemma hsfu_k_add : @RStep.sym IImgB.N_img 0x1bc80 = 0x85950.
Proof. vm_compute. reflexivity. Qed.
Lemma hsfu_k_fe_getround : @RStep.sym IImgB.N_img 0x1c44c = 0x8611c.
Proof. vm_compute. reflexivity. Qed.
Lemma hsfu_k_fe_raise_inexact : @RStep.sym IImgB.N_img 0x1c47c = 0x8614c.
Proof. vm_compute. reflexivity. Qed.
Lemma hsfu_k_round_table : @RStep.sym IImgB.N_img 0x1145c = 0x21538.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== the five CJ contracts at IMG ======================================== *)
Lemma hsfu_c_ext : @C_extendsftf2.extendsftf2_contract IImgB.N_img.
Proof. exact InstB.N_extendsftf2_contract. Qed.
Lemma hsfu_c_fd : @C_floatditf.floatditf_contract IImgB.N_img.
Proof. exact InstB.N_floatditf_contract. Qed.
Lemma hsfu_c_sub : @G_subtf3.subtf3_contract IImgB.N_img.
Proof. exact InstB.N_subtf3_contract. Qed.
Lemma hsfu_c_ge : @G_getf2.getf2_contract IImgB.N_img.
Proof. exact InstB.N_getf2_contract. Qed.
Lemma hsfu_c_lt : @G_letf2.letf2_contract IImgB.N_img.
Proof. exact InstB.N_letf2_contract. Qed.

(* ======================================== the five statements of lib/AU/HPgM3dSFU.v ======================================== *)
Section a.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Lemma hsfu_ext_stmt : @hvu_sf_ext_stmt fx rc SK B MT.
Proof. exact (@hcu_sf_ext fx rc SK B MT MTL IImgB.N_img hsfu_img_segs hsfu_k_ext hsfu_c_ext). Qed.
Lemma hsfu_fd_stmt : @hvu_sf_fd_stmt fx rc SK B MT.
Proof. exact (@hcu_sf_fd fx rc SK B MT MTL IImgB.N_img hsfu_img_segs hsfu_k_fd hsfu_c_fd). Qed.
Lemma hsfu_sub_stmt : @hvu_sf_sub_stmt fx rc SK B MT.
Proof. exact (@hcu_sf_sub fx rc SK B MT MTL IImgB.N_img hsfu_img_segs hsfu_k_sub hsfu_c_sub). Qed.
Lemma hsfu_ge_stmt : @hvu_sf_ge_stmt fx rc SK B MT.
Proof. exact (@hcu_sf_ge fx rc SK B MT MTL IImgB.N_img hsfu_img_segs hsfu_k_ge hsfu_c_ge). Qed.
Lemma hsfu_lt_stmt : @hvu_sf_lt_stmt fx rc SK B MT.
Proof. exact (@hcu_sf_lt fx rc SK B MT MTL IImgB.N_img hsfu_img_segs hsfu_k_lt hsfu_c_lt). Qed.
Lemma hsfu_stmts : @hvu_sf_stmts fx rc SK B MT.
Proof.
split; [exact hsfu_ext_stmt|]. split; [exact hsfu_fd_stmt|]. split; [exact hsfu_sub_stmt|].
split; [exact hsfu_ge_stmt | exact hsfu_lt_stmt].
Qed.
End a.

About hcu_sf_ext.
About hsfu_ext_stmt.
About hsfu_stmts.
Print Assumptions hsfu_img_segs.
Print Assumptions hsfu_k_ext.
Print Assumptions hsfu_k_fd.
Print Assumptions hsfu_k_sub.
Print Assumptions hsfu_k_ge.
Print Assumptions hsfu_k_lt.
Print Assumptions hsfu_k_add.
Print Assumptions hsfu_k_fe_getround.
Print Assumptions hsfu_k_fe_raise_inexact.
Print Assumptions hsfu_k_round_table.
Print Assumptions hsfu_c_ext.
Print Assumptions hsfu_c_fd.
Print Assumptions hsfu_c_sub.
Print Assumptions hsfu_c_ge.
Print Assumptions hsfu_c_lt.
Print Assumptions hsfu_ext_stmt.
Print Assumptions hsfu_fd_stmt.
Print Assumptions hsfu_sub_stmt.
Print Assumptions hsfu_ge_stmt.
Print Assumptions hsfu_lt_stmt.
Print Assumptions hsfu_stmts.
