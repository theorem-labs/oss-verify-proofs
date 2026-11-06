(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): segment A7 of reac_segconf_parse_file's walk, the
   header branch -- HDR 0x87f6c -> TAIL 0x88068 or SEG 0x887a4, CLR 0x880fc -> TAIL, RS3 0x88100 -> TAIL.
   97 instructions, inline checks 8, 13, 20, 21, and nine calls (strchr 0x87f74; refuse 0x88060, 0x880f8,
   0x8835c, 0x88794; trim 0x880c4, 0x88310; strncasecmp 0x880dc; strlen 0x88338).
   Segment A7's proof, 2026-10-30.

   This file ASSEMBLES the segment. The statement S_A7 is pf_pieces.v's; the five pieces A7_S_FUN, A7_S_UNK,
   A7_S_KWOK, A7_S_CLOSE and A7_S_HDR and the four internal cuts they run between are pf_a7_m.v's; the pieces
   themselves are proved in pf_a7_cr.v (FUN, and the two short exits CLR and RS3), pf_a7_u.v (UNK),
   pf_a7_w3.v (KWOK), pf_a7_w2.v (CLOSE) and pf_a7_w1.v (HDR), on the mid-walk seed pf_a7_q.v, the call-site
   lemmas pf_a7_s.v (rule 1j-bis) and the interceptor premises pf_a7_r.v, over the vocabulary pf_a7_d.v and
   the pure spine pf_a7_f.v.

   `a7_assemble` is the chaining, and it is where the order of the pieces is fixed:
     H_CLR and H_RS3 come straight from HA_TAIL;
     H_FUN from HA_TAIL; H_UNK from H_CLR at every FP state (its refuse call returns at another one);
     H_KWOK from H_FUN, H_UNK and HA_SEG; H_CLOSE from H_KWOK and H_UNK; H_HDR from H_FUN and H_CLOSE.
   Every cut a call can land on is taken at EVERY FP state, which is why the HA_ forms of pf_a7_m.v and not
   the bare H_ forms are chained.

   `pf_a7_holds : S_A7 B` is the segment. Its Section hypotheses are the union of the pieces':
     the callees, each at every FP state and at image A's numbers (pf_pieces.v's list for A7):
       TRIM     trim_contract at BASE + AF_trim, STK_trim, RLO_A, RHI_A                (0x880c4, 0x88310)
       REF      refuse_contract at BASE + AF_refuse, STK_refuse, RLO_A, RHI_A, seg_litA_rc, gotwA, guardA
                                                                  (0x88060, 0x880f8, 0x8835c, 0x88794)
       ASTRCHR  RtSeg.astrchr_realizes at pa_sigma SS___interceptor_trampoline_strchr        (0x87f74)
       ANCASE   RtSeg.astrncasecmp_realizes at pa_sigma SS___interceptor_trampoline_strncasecmp (0x880dc)
       ASTRLEN  RtString.astrlen_realizes at pa_sigma SS___interceptor_trampoline_strlen     (0x88338)
     the listing's facts over the abstract instance, which the pinned instance gives by computation:
       TL       PALib B: the errno cell PaArt.aj_art_at asks of an interceptor call (SegRecRest.seg_palib)
       SIGP     seg_sig_prog: the call targets of trim and refuse read as BASE + AF_<F>
       OBJ      seg_val_objs: the literal atoms the auipc / addi pairs form (F_after, F_notclosed,
                S_segment, F_unknown, F_noname, F_toolong)
     FORCED only by pf_a6_k.v's a6_base_move, the rebuild of pf_base after a refuse call, and used nowhere
     else (refuse's post gives only its journal, which keeps an image byte only when it is not an owned
     static, YCbq.v ajournal; arodata_okP after refuse needs pa_relro_img):
       VRO      seg_val_relro
       SSPX     sa_ssp gotwA guardA at every AR state, discharged by SegRecCells.seg_rec_cells (stage 2) *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a7_m pf_a7_cr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib SegObj refuse_c trim_c
  pf_a7_u pf_a7_w1 pf_a7_w2 pf_a7_w3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section a.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.

(* the five pieces and the two short exits give S_A7 *)
Theorem a7_assemble :
  A7_S_FUN B -> A7_S_UNK B -> A7_S_KWOK B -> A7_S_CLOSE B -> A7_S_HDR B ->
  (forall (n : nat), HA_TAIL B n -> forall f1 : YK11.FPState, H_CLR (fx := f1) B n) ->
  (forall (n : nat), HA_TAIL B n -> forall f1 : YK11.FPState, H_RS3 (fx := f1) B n) ->
  S_A7 B.
Proof.
intros FUN UNK KWOK CLOSE HDR CLR RS3.
unfold S_A7. intros f0 n.
split; [|split].
- intros HT HS.
  assert (ACLR : forall f1 : YK11.FPState, H_CLR (fx := f1) B n) by (intros f1; exact (CLR n HT f1)).
  assert (AFUN : HA_FUN B n) by (intros f1; exact (FUN f1 n HT)).
  assert (AUNK : HA_UNK B n) by (intros f1; exact (UNK f1 n ACLR)).
  assert (AKWOK : HA_KWOK B n) by (intros f1; exact (KWOK f1 n AFUN AUNK HS)).
  assert (ACLOSE : HA_CLOSE B n) by (intros f1; exact (CLOSE f1 n AKWOK AUNK)).
  exact (HDR f0 n AFUN ACLOSE).
- intros HT. exact (CLR n HT f0).
- intros HT. exact (RS3 n HT f0).
Qed.
End a.

(* the three pieces pf_a7_cr.v proves (FUN, CLR, RS3) put in: what is left of S_A7 is the four walk pieces *)
Section b.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.
Theorem a7_from_walks :
  A7_S_UNK B -> A7_S_KWOK B -> A7_S_CLOSE B -> A7_S_HDR B -> S_A7 B.
Proof.
intros UNK KWOK CLOSE HDR.
exact (a7_assemble B (a7_fun B) UNK KWOK CLOSE HDR (a7_clr B) (a7_rs3 B)).
Qed.
End b.

(* the segment *)
Section c.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Hypothesis TRIM : forall fx0 : YK11.FPState,
  @trim_contract fx0 rc SK SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Hypothesis REF : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis ASTRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strchr).
Hypothesis ANCASE : forall fx0 : YK11.FPState,
  @RtSeg.astrncasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strncasecmp).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis TL : PALib B.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

Theorem pf_a7_holds : S_A7 B.
Proof.
apply (a7_from_walks B).
- eapply a7_u; eassumption.
- eapply a7_w3; eassumption.
- eapply a7_w2; eassumption.
- eapply a7_w1; eassumption.
Qed.
End c.
