(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): segment B11a of
   reac_segconf_parse_file's walk, S_B11a of lib/B/Prog/pf_pieces.v, from its pieces. The B11a segment lane of the image-B G3 walk owner,
   2026-10-30.
   proves function reac_segconf_parse_file (segment B11a of its walk; reuse search and CONFIRM:
   the rule-24 lookup record). Verdict: none released; ADAPTED from
   a working branch + U piece walks (the image-A G3 walk owner's image-A segment A11a, the unit owner's UBSan piece P7),
   re-derived on image B's code.

   S_B11a : forall (f0 : YK11.FPState) (n : nat), HA_MISS n -> HA_LOWOUT n -> H_MODEL (fx := f0) B n.
   MODEL 0x886d4 -> MISS 0x88a50 (by_token NULL) or LOWOUT 0x88c70 (a hit). The internal cuts and their statements
   are in pf_seg_B11a_k.v; every internal cut targets b11_post (SegModel.r_key's model branch, b11f_r_key):
     MODEL -> CHK                 pf_seg_B11a_m.v  b11_model_ok   0x886d4-0x886dc (3 insns)
     CHK -> LOOP 0 | ZST 0        pf_seg_B11a_l.v  b11_chk_ok     0x886e0-0x88700, 0x889a8 (10)       B#18
     LOOP li -> LOOP li+1 | ZST   pf_seg_B11a_l.v  b11_loop_ok    0x88704-0x88754 (21)                T18, B#19
     ZST li -> RBT                pf_seg_B11a_z.v  b11_zst_ok     0x889ac-0x889d8 (12) + by_token     T21, B#26
     RBT -> MISS | RS1            pf_seg_B11a_h.v  b11_rbt_ok     0x889dc-0x88a04 (11) + snprintf #1  T22
     RS1 -> LOWOUT                pf_seg_B11a_t.v  b11_rs1_ok     0x88a08-0x88a44 (16) + snprintf #2  B#27
   73 instructions on the fast path; the 18 slow-arm / error-call instructions of the four checks (0x89010-0x89028,
   0x89034-0x89044, 0x89244-0x8924c, 0x8929c-0x892ac, plus 0x88758-0x88760) are unreachable: each check is covered
   by a shadow entry from the cut's addressability facts, so its slow arm is never entered. 91 in all.
   Section hypotheses (pf_pieces.v's list for B11a): the snprintf carrier (two sites), reac_box_catalogue_by_token's
   contract, the listing's object atoms (seg_val_objs: "%s" = A_OBJ 35 = 0x21340) and program call targets
   (seg_sig_prog), each runtime / callee entry at every FP state. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegInstB reac_box_catalogue_by_token_c
  pf_pieces pf_seg_B11a_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require pf_seg_B11a_m pf_seg_B11a_l pf_seg_B11a_z
  pf_seg_B11a_h pf_seg_B11a_t.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
Variable B : asyms.
Hypothesis BYTOKEN : forall fx0 : YK11.FPState, @reac_box_catalogue_by_token_contract fx0 rc SK SEGS B
  (BASE + AF_reac_box_catalogue_by_token) STK_reac_box_catalogue_by_token RLO_A RHI_A catA.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis VO : seg_val_objs (PI := PI).
Hypothesis SIGP : seg_sig_prog (PI := PI).

Theorem S_B11a_holds : S_B11a B.
Proof.
intros f0 n HMISS HLOW.
assert (RS1 : forall fx1 : YK11.FPState, B11_RS1_stmt (fx := fx1) B n)
  by (intros fx1; apply pf_seg_B11a_t.b11_rs1_ok; assumption).
assert (RBT : B11_RBT_stmt (fx := f0) B n) by (apply pf_seg_B11a_h.b11_rbt_ok; assumption).
assert (ZST : forall li, B11_ZST_stmt (fx := f0) B n li) by (apply pf_seg_B11a_z.b11_zst_ok; assumption).
apply pf_seg_B11a_m.b11_model_ok.
apply pf_seg_B11a_l.b11_chk_ok; [apply pf_seg_B11a_l.b11_loop_ok; exact ZST | exact ZST].
Qed.
End d.
