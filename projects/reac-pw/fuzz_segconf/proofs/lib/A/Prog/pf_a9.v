(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the ASSEMBLY of segment A9 of reac_segconf_parse_file's
   walk. `a9_compose` chains the five stretch statements of lib/A/Prog/pf_a9_d.v into pf_pieces.v's `S_A9 B`;
   `pf_a9_holds` is that composition with the five stretch theorems put in.
   Segment A9's proof, by the G3 walk owner, 2026-10-30.

   proves no function (kind: segment lemma of reac_segconf_parse_file's image-A walk, segment A9; the whole
   function's rule-24 line and the G3 walk owner's CONFIRM of 2026-10-30T15:42:08Z are in the unit's internal
   record, commit dfb49d6ad789, path records/segp/g3-lookup.md, reuse verdict
   none: written new)

   THE CHAIN, read from the last cut back to the first, as chain_words_a.v chains its six segments:
     SA9_E  HA_TAIL n                                   -> from_K9 n   (the refuse call at 0x88510)
     SA9_D  HA_REF3 / HA_ROLE / HA_MODEL / HA_IGN, from_K9 n -> from_K5 n   (the four strcasecmp at 0x8814c)
     SA9_C  from_K5 n                                   -> from_K3 n   (the unquote block at 0x87ff4)
     SA9_B  from_K3 n                                   -> from_K2 n   (trim #2 and strlen at 0x87fe4)
     SA9_A  HA_REF3 n, from_K2 n                        -> H_KEY n     (strchr, check 9, trim #1 at 0x87fac)
   Every internal cut is at the segment's own FP state f0; only SA9_E crosses a call that changes it, and its
   TAIL exit is taken at every FP state (HA_TAIL), so the chain is one application each. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase
  reac_segconf_parse_file_c SegInstA SegObj SegPaLib trim_c refuse_c pf_pieces pf_a9_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require pf_a9_s1 pf_a9_s2 pf_a9_s3 pf_a9_s4 pf_a9_s5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section g.
Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
Variable B : asyms.

Lemma a9_compose :
  (forall f0 : YK11.FPState, SA9_A (fx := f0) B) ->
  (forall f0 : YK11.FPState, SA9_B (fx := f0) B) ->
  (forall f0 : YK11.FPState, SA9_C (fx := f0) B) ->
  (forall f0 : YK11.FPState, SA9_D (fx := f0) B) ->
  (forall f0 : YK11.FPState, SA9_E (fx := f0) B) ->
  S_A9 B.
Proof.
intros HA HB HC HD HE.
unfold S_A9. intros f0 n ROLE MODEL IGN REF3 TAIL.
exact (HA f0 n REF3
         (HB f0 n
            (HC f0 n
               (HD f0 n REF3 ROLE MODEL IGN
                  (HE f0 n TAIL))))).
Qed.

(** ** The segment: the five stretch theorems put into a9_compose.
    Section hypotheses, each named where it is used:
    - the callee texts pf_pieces.v's list names for A9, at listing terms (the image-A owner's ruling 16:54Z):
      ASTRCHR (RtSeg row 6, stretch A), ASTRLEN (RtString row 16, stretch B), ASTRCASECMP (RtSeg row 10,
      stretch D), TRIM (trim_contract, stretches A and B), REFUSE (refuse_contract, stretch E);
    - the listing's facts over the walk's abstract instance (SegObj.v / SegPaLib.v; the pinned instance gives
      each by computation): TL (the errno cell `aj_art_at` needs, stretches A, B, D), SIGP (the program
      call targets, stretches A, B, E), OBJ (the literal atoms A_OBJ 40, 43-48, 61, stretches A, D);
    - VRO and SSPX, in stretch E ONLY, forced by pf_a6_k.a6_base_move where pf_base is rebuilt AFTER the
      refuse call (refuse's post gives only its journal; the journal keeps an image byte only when it is not
      in as_owned_static B, YCbq.v:479, and whether the GOT word 0xa36d8 and the guard 0x5ff078 are owned
      statics is a record fact of listing stage 2, SegRecCells.seg_rec_cells; arodata_okP after refuse needs
      pa_relro_img). The G3 walk owner's accepted exception; both are discharged from listing stage 2.
    No SSPX / VRO / ROMV anywhere else: stretches A-D re-derive sa_ssp, arodata_okP and rt_rom_view from
    pf_base (pf_a5_k.a5_move0, a5_rom), and stretch C takes no hypothesis at all. *)
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Hypothesis TL : PALib B.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis ASTRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strchr).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis ASTRCASECMP : forall fx0 : YK11.FPState,
  @RtSeg.astrcasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcasecmp).
Hypothesis TRIM : forall fx0 : YK11.FPState,
  trim_contract (fx := fx0) SEGS B (BASE + AF_trim) STK_trim RLO_A RHI_A.
Hypothesis REFUSE : forall fx0 : YK11.FPState,
  refuse_contract (fx := fx0) SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis SSPX : forall ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

Theorem pf_a9_holds : S_A9 B.
Proof.
apply a9_compose.
- intros f0. exact (@pf_a9_s1.a9_sA f0 rc SK PI B TL SIGP OBJ ASTRCHR TRIM).
- intros f0. exact (@pf_a9_s2.a9_sB f0 rc SK PI B TL SIGP ASTRLEN TRIM).
- intros f0. exact (@pf_a9_s3.a9_sC f0 rc SK PI B).
- intros f0. exact (@pf_a9_s4.a9_sD f0 rc SK PI B TL OBJ ASTRCASECMP).
- intros f0. exact (@pf_a9_s5.a9_sE f0 rc SK PI B SIGP VRO REFUSE SSPX).
Qed.

End g.
