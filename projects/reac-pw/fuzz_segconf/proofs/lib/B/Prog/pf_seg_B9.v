(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): segment B9 of
   reac_segconf_parse_file's walk, the theorem S_B9 of lib/B/Prog/pf_pieces.v from its stretches (lib/B/Prog/
   pf_seg_B9_d.v SB9_1 .. SB9_10, and KREF -> TAIL). The B9 segment lane of the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B9; reuse search and CONFIRM:
   the rule-24 lookup record, the rule-24 checker 2026-10-30T16:55:47Z; reuse verdict none
   released; ADAPTED from the image-A G3 walk owner's image-A segment walk on a working branch (pf_a9.v a9_compose,
   pf_a9_d.v) and the unit owner's UBSan piece walk lib/U/Prog/pf_p5.v (a working branch), re-derived on
   image B's code).
   b9_compose chains the stretches backwards: KREF (S_B9's second conjunct, at the segment's FP state) closes J9;
   then J8 .. J6 with the IGN / MODEL / ROLE exits, K5 with the HREF exit, J4 .. J2, J1 with the REF3 exit, and KEY.
   Every exit cut is pf_pieces.v's HA_ form, instantiated at the segment's FP state f0 (strchr, trim, strlen and
   strcasecmp keep the FP state; only refuse changes it, inside the KREF stretch). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa
  SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c trim_c
  reac_segconf_parse_file_c SegInstB pf_pieces pf_seg_B9_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt SegObj SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require pf_seg_B9_s1 pf_seg_B9_s2 pf_seg_B9_s3
  pf_seg_B9_s4 pf_seg_B9_s5 pf_seg_B9_s6 pf_seg_B9_s7 pf_seg_B9_s10 pf_seg_B9_s11.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section s.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.

(* the decomposition of pf_seg_B9_d.v is checked end to end: the ten stretches at every FP state and the KREF
   stretch give pf_pieces.v's S_B9 *)
Lemma b9_compose :
  (forall f0 : YK11.FPState, SB9_1 (fx := f0) B) -> (forall f0 : YK11.FPState, SB9_2 (fx := f0) B) ->
  (forall f0 : YK11.FPState, SB9_3 (fx := f0) B) -> (forall f0 : YK11.FPState, SB9_4 (fx := f0) B) ->
  (forall f0 : YK11.FPState, SB9_5 (fx := f0) B) -> (forall f0 : YK11.FPState, SB9_6 (fx := f0) B) ->
  (forall f0 : YK11.FPState, SB9_7 (fx := f0) B) -> (forall f0 : YK11.FPState, SB9_8 (fx := f0) B) ->
  (forall f0 : YK11.FPState, SB9_9 (fx := f0) B) -> (forall f0 : YK11.FPState, SB9_10 (fx := f0) B) ->
  (forall (f0 : YK11.FPState) (n : nat), HA_TAIL B n -> H_KREF (fx := f0) B n) ->
  S_B9 B.
Proof.
intros S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 f0 n. split; [|exact (S11 f0 n)].
intros HR HM HI HR3 HH HT.
apply (S1 f0 n). apply (S2 f0 n (HR3 f0)). apply (S3 f0 n). apply (S4 f0 n). apply (S5 f0 n).
apply (S6 f0 n (HH f0)). apply (S7 f0 n (HR f0)). apply (S8 f0 n (HM f0)). apply (S9 f0 n (HI f0)).
apply (S10 f0 n). exact (S11 f0 n HT).
Qed.

End s.

(** ** S_B9 (pf_pieces.v) proved: the stretch theorems of pf_seg_B9_s1 .. s11.v composed by b9_compose. The Section
    hypotheses are the callee contracts of B9's calls at image B's entries (strchr, strlen, strcasecmp carriers at
    the listing's trampolines; trim_contract and refuse_contract at BASE + AF_<F> with SegInstB's numbers) and the
    listing / record facts the walks share (SIGP, OBJ, VRO: B's SegObj; SSPX: the stack-protector cells at every AR
    state, after refuse only; TL: PALib, the errno cell's place for the art steps). *)
Section w.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis ASTRCHR : forall fx0 : YK11.FPState, @RtSeg.astrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strchr).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis ASTRCASECMP : forall fx0 : YK11.FPState, @RtSeg.astrcasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcasecmp).
Hypothesis TRIM : forall fx0 : YK11.FPState, trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Hypothesis REFUSE : forall fx0 : YK11.FPState, refuse_contract (fx := fx0) SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Hypothesis TL : PALib B.

Theorem S_B9_holds : S_B9 B.
Proof.
apply b9_compose; intros f0;
  first [ eapply pf_seg_B9_s1.b9_s1 | eapply pf_seg_B9_s2.b9_s2 | eapply pf_seg_B9_s3.b9_s3
        | eapply pf_seg_B9_s4.b9_s4 | eapply pf_seg_B9_s5.b9_s5 | eapply pf_seg_B9_s6.b9_s6
        | eapply pf_seg_B9_s7.b9_s7 | eapply pf_seg_B9_s7.b9_s8 | eapply pf_seg_B9_s7.b9_s9
        | eapply pf_seg_B9_s10.b9_s10 | eapply pf_seg_B9_s11.b9_s11 ]; eassumption.
Qed.
End w.
