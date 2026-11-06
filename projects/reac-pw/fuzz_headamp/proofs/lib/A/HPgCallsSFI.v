(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; addresses from the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id): the image record of lib/A/HPgCallsSF.v's Section sf at headamp's own image A. Proves no function (kind:
   instance discharge).

   IMG is lib/CJ/RL/I/IImgA.v's N_img: the CJ library's keys mapped to image A's addresses, over lib/A/Img0.v's
   rsegs. The symbol facts hold by computation on N_sym: the five routines HPgCallsSF calls (HK_EXT .. HK_LT) and
   the four further keys __subtf3's contract reads (__addtf3, __fe_getround, __fe_raise_inexact and
   __fe_getround's rounding table). The five CJ contracts at N_img are lib/CJ/RL/I/InstA.v's instances: the CJ
   proofs of lib/CJ/RL/G instantiated at N_img, whose code, read-only-byte and near-distance premises InstA.v
   checks by computation against rsegs.

   hsf_<routine>_call is HPgCallsSF's hc_sf_<routine>_call with IMG and its four image hypotheses for that routine
   supplied (HIMG, its symbol fact, its contract): no hypothesis about the image remains; what remains is the
   walk's own Section data (fx, rc, SK, B, MT and MTL : ameter_laws MT), as in hc_sf_<routine>_call. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.CJ.RL.I Require IImgA InstA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgCallsSF.
Local Open Scope Z_scope.

(* ======================================== IMG and HIMG ======================================== *)
Lemma hsf_img_segs : @RStep.img_segs IImgA.N_img = rsegs.
Proof. reflexivity. Qed.

(* ======================================== the symbol facts ======================================== *)
Lemma hsf_k_ext : @RStep.sym IImgA.N_img 0x200dc = A_SF_EXT.
Proof. vm_compute. reflexivity. Qed.
Lemma hsf_k_fd : @RStep.sym IImgA.N_img 0x7f000900 = A_SF_FD.
Proof. vm_compute. reflexivity. Qed.
Lemma hsf_k_sub : @RStep.sym IImgA.N_img 0x1bc70 = A_SF_SUB.
Proof. vm_compute. reflexivity. Qed.
Lemma hsf_k_ge : @RStep.sym IImgA.N_img 0x1b314 = A_SF_GE.
Proof. vm_compute. reflexivity. Qed.
Lemma hsf_k_lt : @RStep.sym IImgA.N_img 0x1b24c = A_SF_LT.
Proof. vm_compute. reflexivity. Qed.
(* __subtf3 runs into __addtf3 0x854d8, which calls __fe_getround 0x85ca4 (its table 0x214f8) and
   __fe_raise_inexact 0x85cd4. *)
Lemma hsf_k_add : @RStep.sym IImgA.N_img 0x1bc80 = 0x854d8.
Proof. vm_compute. reflexivity. Qed.
Lemma hsf_k_fe_getround : @RStep.sym IImgA.N_img 0x1c44c = 0x85ca4.
Proof. vm_compute. reflexivity. Qed.
Lemma hsf_k_fe_raise_inexact : @RStep.sym IImgA.N_img 0x1c47c = 0x85cd4.
Proof. vm_compute. reflexivity. Qed.
Lemma hsf_k_round_table : @RStep.sym IImgA.N_img 0x1145c = 0x214f8.
Proof. vm_compute. reflexivity. Qed.

(* ======================================== the five CJ contracts at IMG ======================================== *)
Lemma hsf_c_ext : @C_extendsftf2.extendsftf2_contract IImgA.N_img.
Proof. exact InstA.N_extendsftf2_contract. Qed.
Lemma hsf_c_fd : @C_floatditf.floatditf_contract IImgA.N_img.
Proof. exact InstA.N_floatditf_contract. Qed.
Lemma hsf_c_sub : @G_subtf3.subtf3_contract IImgA.N_img.
Proof. exact InstA.N_subtf3_contract. Qed.
Lemma hsf_c_ge : @G_getf2.getf2_contract IImgA.N_img.
Proof. exact InstA.N_getf2_contract. Qed.
Lemma hsf_c_lt : @G_letf2.letf2_contract IImgA.N_img.
Proof. exact InstA.N_letf2_contract. Qed.

(* ======================================== the five call adapters at IMG ======================================== *)
Section a.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* 0x834c4 jal __extendsftf2 0x85248 *)
Definition hsf_extendsftf2_call :=
  @hc_sf_extendsftf2_call fx rc SK B MT MTL IImgA.N_img hsf_img_segs hsf_k_ext hsf_c_ext.
(* 0x834d8 jal __floatditf 0x853a4 *)
Definition hsf_floatditf_call :=
  @hc_sf_floatditf_call fx rc SK B MT MTL IImgA.N_img hsf_img_segs hsf_k_fd hsf_c_fd.
(* 0x834ec jal __subtf3 0x854c8 (into __addtf3 0x854d8) *)
Definition hsf_subtf3_call :=
  @hc_sf_subtf3_call fx rc SK B MT MTL IImgA.N_img hsf_img_segs hsf_k_sub hsf_c_sub.
(* 0x83500 jal __getf2 0x84ffc *)
Definition hsf_getf2_call :=
  @hc_sf_getf2_call fx rc SK B MT MTL IImgA.N_img hsf_img_segs hsf_k_ge hsf_c_ge.
(* 0x83518 jal __lttf2 0x84f34 *)
Definition hsf_lttf2_call :=
  @hc_sf_lttf2_call fx rc SK B MT MTL IImgA.N_img hsf_img_segs hsf_k_lt hsf_c_lt.
End a.

About hsf_extendsftf2_call.
About hsf_floatditf_call.
About hsf_subtf3_call.
About hsf_getf2_call.
About hsf_lttf2_call.
Print Assumptions hsf_img_segs.
Print Assumptions hsf_k_ext.
Print Assumptions hsf_k_fd.
Print Assumptions hsf_k_sub.
Print Assumptions hsf_k_ge.
Print Assumptions hsf_k_lt.
Print Assumptions hsf_k_add.
Print Assumptions hsf_k_fe_getround.
Print Assumptions hsf_k_fe_raise_inexact.
Print Assumptions hsf_k_round_table.
Print Assumptions hsf_c_ext.
Print Assumptions hsf_c_fd.
Print Assumptions hsf_c_sub.
Print Assumptions hsf_c_ge.
Print Assumptions hsf_c_lt.
Print Assumptions hsf_extendsftf2_call.
Print Assumptions hsf_floatditf_call.
Print Assumptions hsf_subtf3_call.
Print Assumptions hsf_getf2_call.
Print Assumptions hsf_lttf2_call.
