(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutOpsD CutHeap CutAutoD CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutCert Require Import Pm10CutKitD_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import DecAssume.
Import ListNotations. Import AX2. Import AX2B.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1000000. Set Printing Depth 1000000.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_decfloat5_csrc_T_u Cut_decfloat5_csrc_R0p0_u Cut_decfloat5_csrc_R0p1_u Cut_decfloat5_csrc_R0p2_u Cut_decfloat5_csrc_R0p3_u Cut_decfloat5_csrc_R1p0_u Cut_decfloat5_csrc_R1p1_u Cut_decfloat5_csrc_R2_u Cut_decfloat5_csrc_R3_u Cut_decfloat5_csrc_R4_u Cut_decfloat5_csrc_R5_u Cut_decfloat5_csrc_R6_u Cut_decfloat5_csrc_R7_u Cut_decfloat5_csrc_R8_u Cut_decfloat5_csrc_R9_u Cut_decfloat5_csrc_R10_u Cut_decfloat5_csrc_R11_u Cut_decfloat5_csrc_D_u.
Lemma lsub180 : CXD.lems_chk LEMS (CAD.po_ops o180) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert180 : src0_cutd_cert ITR BF cp180 (CAD.po_ops o180) (CAD.po_ops2 o180) (CAD.po_plan o180) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub181 : CXD.lems_chk LEMS (CAD.po_ops o181) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert181 : src0_cutd_cert ITR BF cp181 (CAD.po_ops o181) (CAD.po_ops2 o181) (CAD.po_plan o181) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub182 : CXD.lems_chk LEMS (CAD.po_ops o182) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert182 : src0_cutd_cert ITR BF cp182 (CAD.po_ops o182) (CAD.po_ops2 o182) (CAD.po_plan o182) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub183 : CXD.lems_chk LEMS (CAD.po_ops o183) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert183 : src0_cutd_cert ITR BF cp183 (CAD.po_ops o183) (CAD.po_ops2 o183) (CAD.po_plan o183) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub184 : CXD.lems_chk LEMS (CAD.po_ops o184) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert184 : src0_cutd_cert ITR BF cp184 (CAD.po_ops o184) (CAD.po_ops2 o184) (CAD.po_plan o184) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub185 : CXD.lems_chk LEMS (CAD.po_ops o185) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert185 : src0_cutd_cert ITR BF cp185 (CAD.po_ops o185) (CAD.po_ops2 o185) (CAD.po_plan o185) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub186 : CXD.lems_chk LEMS (CAD.po_ops o186) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert186 : src0_cutd_cert ITR BF cp186 (CAD.po_ops o186) (CAD.po_ops2 o186) (CAD.po_plan o186) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub187 : CXD.lems_chk LEMS (CAD.po_ops o187) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert187 : src0_cutd_cert ITR BF cp187 (CAD.po_ops o187) (CAD.po_ops2 o187) (CAD.po_plan o187) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub188 : CXD.lems_chk LEMS (CAD.po_ops o188) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert188 : src0_cutd_cert ITR BF cp188 (CAD.po_ops o188) (CAD.po_ops2 o188) (CAD.po_plan o188) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub189 : CXD.lems_chk LEMS (CAD.po_ops o189) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert189 : src0_cutd_cert ITR BF cp189 (CAD.po_ops o189) (CAD.po_ops2 o189) (CAD.po_plan o189) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub190 : CXD.lems_chk LEMS (CAD.po_ops o190) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert190 : src0_cutd_cert ITR BF cp190 (CAD.po_ops o190) (CAD.po_ops2 o190) (CAD.po_plan o190) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub191 : CXD.lems_chk LEMS (CAD.po_ops o191) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert191 : src0_cutd_cert ITR BF cp191 (CAD.po_ops o191) (CAD.po_ops2 o191) (CAD.po_plan o191) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub192 : CXD.lems_chk LEMS (CAD.po_ops o192) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert192 : src0_cutd_cert ITR BF cp192 (CAD.po_ops o192) (CAD.po_ops2 o192) (CAD.po_plan o192) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub193 : CXD.lems_chk LEMS (CAD.po_ops o193) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert193 : src0_cutd_cert ITR BF cp193 (CAD.po_ops o193) (CAD.po_ops2 o193) (CAD.po_plan o193) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub194 : CXD.lems_chk LEMS (CAD.po_ops o194) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert194 : src0_cutd_cert ITR BF cp194 (CAD.po_ops o194) (CAD.po_ops2 o194) (CAD.po_plan o194) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub195 : CXD.lems_chk LEMS (CAD.po_ops o195) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert195 : src0_cutd_cert ITR BF cp195 (CAD.po_ops o195) (CAD.po_ops2 o195) (CAD.po_plan o195) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub196 : CXD.lems_chk LEMS (CAD.po_ops o196) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert196 : src0_cutd_cert ITR BF cp196 (CAD.po_ops o196) (CAD.po_ops2 o196) (CAD.po_plan o196) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub197 : CXD.lems_chk LEMS (CAD.po_ops o197) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert197 : src0_cutd_cert ITR BF cp197 (CAD.po_ops o197) (CAD.po_ops2 o197) (CAD.po_plan o197) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub198 : CXD.lems_chk LEMS (CAD.po_ops o198) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert198 : src0_cutd_cert ITR BF cp198 (CAD.po_ops o198) (CAD.po_ops2 o198) (CAD.po_plan o198) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub199 : CXD.lems_chk LEMS (CAD.po_ops o199) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert199 : src0_cutd_cert ITR BF cp199 (CAD.po_ops o199) (CAD.po_ops2 o199) (CAD.po_plan o199) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub200 : CXD.lems_chk LEMS (CAD.po_ops o200) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert200 : src0_cutd_cert ITR BF cp200 (CAD.po_ops o200) (CAD.po_ops2 o200) (CAD.po_plan o200) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub201 : CXD.lems_chk LEMS (CAD.po_ops o201) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert201 : src0_cutd_cert ITR BF cp201 (CAD.po_ops o201) (CAD.po_ops2 o201) (CAD.po_plan o201) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub202 : CXD.lems_chk LEMS (CAD.po_ops o202) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert202 : src0_cutd_cert ITR BF cp202 (CAD.po_ops o202) (CAD.po_ops2 o202) (CAD.po_plan o202) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub203 : CXD.lems_chk LEMS (CAD.po_ops o203) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert203 : src0_cutd_cert ITR BF cp203 (CAD.po_ops o203) (CAD.po_ops2 o203) (CAD.po_plan o203) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub204 : CXD.lems_chk LEMS (CAD.po_ops o204) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert204 : src0_cutd_cert ITR BF cp204 (CAD.po_ops o204) (CAD.po_ops2 o204) (CAD.po_plan o204) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub205 : CXD.lems_chk LEMS (CAD.po_ops o205) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert205 : src0_cutd_cert ITR BF cp205 (CAD.po_ops o205) (CAD.po_ops2 o205) (CAD.po_plan o205) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub206 : CXD.lems_chk LEMS (CAD.po_ops o206) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert206 : src0_cutd_cert ITR BF cp206 (CAD.po_ops o206) (CAD.po_ops2 o206) (CAD.po_plan o206) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub207 : CXD.lems_chk LEMS (CAD.po_ops o207) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert207 : src0_cutd_cert ITR BF cp207 (CAD.po_ops o207) (CAD.po_ops2 o207) (CAD.po_plan o207) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub208 : CXD.lems_chk LEMS (CAD.po_ops o208) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert208 : src0_cutd_cert ITR BF cp208 (CAD.po_ops o208) (CAD.po_ops2 o208) (CAD.po_plan o208) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub209 : CXD.lems_chk LEMS (CAD.po_ops o209) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert209 : src0_cutd_cert ITR BF cp209 (CAD.po_ops o209) (CAD.po_ops2 o209) (CAD.po_plan o209) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub210 : CXD.lems_chk LEMS (CAD.po_ops o210) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert210 : src0_cutd_cert ITR BF cp210 (CAD.po_ops o210) (CAD.po_ops2 o210) (CAD.po_plan o210) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub211 : CXD.lems_chk LEMS (CAD.po_ops o211) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert211 : src0_cutd_cert ITR BF cp211 (CAD.po_ops o211) (CAD.po_ops2 o211) (CAD.po_plan o211) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub212 : CXD.lems_chk LEMS (CAD.po_ops o212) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert212 : src0_cutd_cert ITR BF cp212 (CAD.po_ops o212) (CAD.po_ops2 o212) (CAD.po_plan o212) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub213 : CXD.lems_chk LEMS (CAD.po_ops o213) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert213 : src0_cutd_cert ITR BF cp213 (CAD.po_ops o213) (CAD.po_ops2 o213) (CAD.po_plan o213) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub214 : CXD.lems_chk LEMS (CAD.po_ops o214) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert214 : src0_cutd_cert ITR BF cp214 (CAD.po_ops o214) (CAD.po_ops2 o214) (CAD.po_plan o214) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub215 : CXD.lems_chk LEMS (CAD.po_ops o215) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert215 : src0_cutd_cert ITR BF cp215 (CAD.po_ops o215) (CAD.po_ops2 o215) (CAD.po_plan o215) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub216 : CXD.lems_chk LEMS (CAD.po_ops o216) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert216 : src0_cutd_cert ITR BF cp216 (CAD.po_ops o216) (CAD.po_ops2 o216) (CAD.po_plan o216) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub217 : CXD.lems_chk LEMS (CAD.po_ops o217) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert217 : src0_cutd_cert ITR BF cp217 (CAD.po_ops o217) (CAD.po_ops2 o217) (CAD.po_plan o217) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub218 : CXD.lems_chk LEMS (CAD.po_ops o218) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert218 : src0_cutd_cert ITR BF cp218 (CAD.po_ops o218) (CAD.po_ops2 o218) (CAD.po_plan o218) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub219 : CXD.lems_chk LEMS (CAD.po_ops o219) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert219 : src0_cutd_cert ITR BF cp219 (CAD.po_ops o219) (CAD.po_ops2 o219) (CAD.po_plan o219) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub220 : CXD.lems_chk LEMS (CAD.po_ops o220) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert220 : src0_cutd_cert ITR BF cp220 (CAD.po_ops o220) (CAD.po_ops2 o220) (CAD.po_plan o220) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub221 : CXD.lems_chk LEMS (CAD.po_ops o221) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert221 : src0_cutd_cert ITR BF cp221 (CAD.po_ops o221) (CAD.po_ops2 o221) (CAD.po_plan o221) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub222 : CXD.lems_chk LEMS (CAD.po_ops o222) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert222 : src0_cutd_cert ITR BF cp222 (CAD.po_ops o222) (CAD.po_ops2 o222) (CAD.po_plan o222) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub223 : CXD.lems_chk LEMS (CAD.po_ops o223) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert223 : src0_cutd_cert ITR BF cp223 (CAD.po_ops o223) (CAD.po_ops2 o223) (CAD.po_plan o223) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub224 : CXD.lems_chk LEMS (CAD.po_ops o224) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert224 : src0_cutd_cert ITR BF cp224 (CAD.po_ops o224) (CAD.po_ops2 o224) (CAD.po_plan o224) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub225 : CXD.lems_chk LEMS (CAD.po_ops o225) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert225 : src0_cutd_cert ITR BF cp225 (CAD.po_ops o225) (CAD.po_ops2 o225) (CAD.po_plan o225) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub226 : CXD.lems_chk LEMS (CAD.po_ops o226) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert226 : src0_cutd_cert ITR BF cp226 (CAD.po_ops o226) (CAD.po_ops2 o226) (CAD.po_plan o226) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub227 : CXD.lems_chk LEMS (CAD.po_ops o227) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert227 : src0_cutd_cert ITR BF cp227 (CAD.po_ops o227) (CAD.po_ops2 o227) (CAD.po_plan o227) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub228 : CXD.lems_chk LEMS (CAD.po_ops o228) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert228 : src0_cutd_cert ITR BF cp228 (CAD.po_ops o228) (CAD.po_ops2 o228) (CAD.po_plan o228) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub229 : CXD.lems_chk LEMS (CAD.po_ops o229) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert229 : src0_cutd_cert ITR BF cp229 (CAD.po_ops o229) (CAD.po_ops2 o229) (CAD.po_plan o229) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub230 : CXD.lems_chk LEMS (CAD.po_ops o230) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert230 : src0_cutd_cert ITR BF cp230 (CAD.po_ops o230) (CAD.po_ops2 o230) (CAD.po_plan o230) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub231 : CXD.lems_chk LEMS (CAD.po_ops o231) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert231 : src0_cutd_cert ITR BF cp231 (CAD.po_ops o231) (CAD.po_ops2 o231) (CAD.po_plan o231) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub232 : CXD.lems_chk LEMS (CAD.po_ops o232) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert232 : src0_cutd_cert ITR BF cp232 (CAD.po_ops o232) (CAD.po_ops2 o232) (CAD.po_plan o232) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub233 : CXD.lems_chk LEMS (CAD.po_ops o233) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert233 : src0_cutd_cert ITR BF cp233 (CAD.po_ops o233) (CAD.po_ops2 o233) (CAD.po_plan o233) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub234 : CXD.lems_chk LEMS (CAD.po_ops o234) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert234 : src0_cutd_cert ITR BF cp234 (CAD.po_ops o234) (CAD.po_ops2 o234) (CAD.po_plan o234) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub235 : CXD.lems_chk LEMS (CAD.po_ops o235) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert235 : src0_cutd_cert ITR BF cp235 (CAD.po_ops o235) (CAD.po_ops2 o235) (CAD.po_plan o235) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub236 : CXD.lems_chk LEMS (CAD.po_ops o236) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert236 : src0_cutd_cert ITR BF cp236 (CAD.po_ops o236) (CAD.po_ops2 o236) (CAD.po_plan o236) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub237 : CXD.lems_chk LEMS (CAD.po_ops o237) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert237 : src0_cutd_cert ITR BF cp237 (CAD.po_ops o237) (CAD.po_ops2 o237) (CAD.po_plan o237) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub238 : CXD.lems_chk LEMS (CAD.po_ops o238) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert238 : src0_cutd_cert ITR BF cp238 (CAD.po_ops o238) (CAD.po_ops2 o238) (CAD.po_plan o238) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma lsub239 : CXD.lems_chk LEMS (CAD.po_ops o239) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma cert239 : src0_cutd_cert ITR BF cp239 (CAD.po_ops o239) (CAD.po_ops2 o239) (CAD.po_plan o239) = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
