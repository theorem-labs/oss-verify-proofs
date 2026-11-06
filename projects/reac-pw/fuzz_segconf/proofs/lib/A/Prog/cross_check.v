(* The walk of cross_check on reac-pw/fuzz_segconf's ASan image A (fuzz_segconf.asan 0x89218, 724 bytes, 181
   instructions): its contract lib/A/Prog/cross_check_c.v at image A's values, from the three segments
   (cross_check_s1.v, cross_check_s2.v, cross_check_s3.v) chained by cross_check_a.v over the vocabulary of
   cross_check_d.v, with the pure lemmas of cross_check_f.v and the refuse call-site lemmas of
   cross_check_r.v.
   The image-A values are SegInstA.v's (STK_cross_check = 128 + STK_refuse, seg_litA_rc, gotwA, guardA, RLO_A,
   RHI_A); the entry is BASE + AF_cross_check and refuse's BASE + AF_refuse (SegList.v); the two formats are
   the listing's objects A_OBJ 73 (0x21c00, F_xmodel) and A_OBJ 74 (0x21ca0, F_xbox), tied to seg_litA_rc by
   seg_val_objs. The one program callee's contract, refuse_contract, is a Section hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibF PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c cross_check_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
cross_check_d cross_check_a cross_check_s1 cross_check_s2 cross_check_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ============================== the contract at image A ============================== *)
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
Section i.
Variable B : asyms.
(* the per-binary records the walk takes, and refuse's contract at image A's numbers. RELRO and SSPAR are the
   two image facts no contract carries and no PAImg field gives: the read-only window lies in the image
   (the donor's cw_ro_imgP, chain_words_d.v:228) and the stack-protector pair reads back at every state with
   AR (the donor's recorder-cells record; the image-A owner's ROUTE (A) of 2026-10-30 17:0xZ, the shape the parse walk's
   reac_segconf_parse.v uses). At image A they come from the stage-2 records SegRecBase and
   SegRecCells.seg_rec_cells over HB : SegBSyms B and IMG : seg_img_facts, which wait on listing stage 2;
   until those compile they stay hypotheses here and show up in `About cross_check_walk`. *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis VOBJ : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis RELRO : forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a.
Hypothesis SSPX : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotwA guardA.
Hypothesis REFUSE : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse SEG_RLO SEG_RHI seg_litA_rc gotwA guardA.
(* the two formats cross_check passes are the listing's objects 73 and 74 *)
Lemma cc_litA_xmodel : seg_litA_rc F_xmodel = VAL (A_OBJ 73).
Proof. rewrite (VOBJ 73%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma cc_litA_xbox : seg_litA_rc F_xbox = VAL (A_OBJ 74).
Proof. rewrite (VOBJ 74%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma cc_STK_refuse_nonneg : 0 <= STK_refuse.
Proof. unfold STK_refuse, ESTACK. lia. Qed.
Theorem cross_check_walk :
  cross_check_contract SEGS B (BASE + AF_cross_check) STK_cross_check RLO_A RHI_A seg_litA_rc gotwA guardA.
Proof.
unfold cross_check_contract.
intros ly S W regs mem md ch c rcs HPRE HROD H10 Hc64 HCC HROOM HNEV.
pose (v := mkCCX ly S W regs mem md ch c rcs).
assert (HP : cc_pre B seg_litA_rc gotwA guardA STK_refuse v)
  by exact (cc_pre_of B seg_litA_rc gotwA guardA STK_refuse v HPRE HROD H10 Hc64 HCC HROOM HNEV).
(* rounding mode 0 is cross_check_pre's seventh conjunct (sa_frm0), which is PaFx's frm0 at this FP state *)
assert (HFRM : frm0 fx)
  by exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HCC))))))).
exact (cc_run B seg_litA_rc gotwA guardA STK_refuse
  (fun fx0 => cross_check_s1.cc_s1 (fx := fx0) B seg_litA_rc gotwA guardA STK_refuse TL TLF VOBJ SIGP
     RELRO SSPX cc_litA_xmodel cc_litA_xbox cc_STK_refuse_nonneg REFUSE)
  (fun fx0 => cross_check_s2.cc_s2 (fx := fx0) B seg_litA_rc gotwA guardA STK_refuse TL TLF VOBJ SIGP
     RELRO SSPX cc_litA_xmodel cc_litA_xbox cc_STK_refuse_nonneg REFUSE)
  (fun fx0 => cross_check_s3.cc_s3 (fx := fx0) B seg_litA_rc gotwA guardA STK_refuse TL TLF VOBJ SIGP
     RELRO SSPX cc_litA_xmodel cc_litA_xbox cc_STK_refuse_nonneg REFUSE)
  v HP HFRM).
Qed.
End i.
End h.
End g.
