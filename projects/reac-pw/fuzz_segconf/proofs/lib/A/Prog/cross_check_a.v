(* The chaining of the walk of cross_check on reac-pw/fuzz_segconf's ASan image A (fuzz_segconf.asan 0x89218,
   724 bytes, 181 instructions): the three segment statements of cross_check_d.v and the induction over the
   passes of the loop, for any image parameters (cross_check.v instantiates them at image A).

     cross_check_s1.v  cc_s1  the entry 0x89218-0x892a8 and the inline check of c->n, to the loop head or to
                              the epilogue
     cross_check_s2.v  cc_s2  one pass of the loop 0x892ac-0x893d0 with the check stubs and the two refuse
                              calls (0x89350 F_xmodel, 0x8939c F_xbox)
     cross_check_s3.v  cc_s3  the epilogue 0x89460-0x89498
     cross_check_f.v          the pure model and encoding lemmas
     cross_check_r.v          the premises of the two refuse call sites (rule 1j-bis) and what survives a call

   The loop is closed by induction on the passes left (cc_loop), as
   proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_a.v's cw_loop does for the member loop of
   chain_words (origin/ossv/recipes 501c0d516c69). Every pass calls refuse, whose post is apost_baseF, so the
   next pass is taken at every FP state that has rounding mode 0: PaFx.fxrel_frm0 carries frm0 across the call
   and PaFx.srr_apost_baseF_lift carries the post back to the entry's FP state. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaFx PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c cross_check_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import cross_check_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
Section e.
Variable B : asyms.
Variable lit : list Z -> Z.
Variables gotw guard STK_REF : Z.
(* every pass of the loop reaches the post: by induction on the passes left, cc_n v - i. A pass index at or
   beyond cc_n v has no state, because INV_LOOP asks 0 <= i < cc_n v (the ASan loop is rotated: its head is
   reached only with a pass to run). *)
Lemma cc_loop : (forall fx0 : YK11.FPState, cc_S2P (fx := fx0) B lit gotw guard STK_REF) ->
  forall v, cc_pre B lit gotw guard STK_REF v ->
  (forall fx0 : YK11.FPState, from_EPI (fx := fx0) B lit gotw guard STK_REF v) ->
  forall i (fx0 : YK11.FPState), frm0 fx0 -> from_LOOP (fx := fx0) B lit gotw guard STK_REF v i.
Proof.
intros S2 v HP HEPI.
assert (H : forall k i (fx0 : YK11.FPState), (Z.to_nat (cc_n v - i) <= k)%nat -> frm0 fx0 ->
  from_LOOP (fx := fx0) B lit gotw guard STK_REF v i).
{ induction k as [|k IH]; intros i fx0 Hk Hfrm.
  - intros ly3 S3 W3 regs3 mem3 md3 HINV. exfalso.
    destruct HINV as (_ & _ & Hi & _). lia.
  - destruct (Z_lt_le_dec i (cc_n v)) as [Hlt | Hge].
    + apply (S2 fx0 v i Hfrm HP HEPI). intros fx1 Hfrm1. apply (IH (i + 1) fx1); [lia | exact Hfrm1].
    + intros ly3 S3 W3 regs3 mem3 md3 HINV. exfalso.
      destruct HINV as (_ & _ & Hi & _). lia. }
intros i fx0 Hfrm. exact (H (Z.to_nat (cc_n v - i)) i fx0 (le_n _) Hfrm).
Qed.
(* the three segments and the loop take every entry state with cc_pre and rounding mode 0 to the statement's
   post. Rounding mode 0 is cross_check_pre's sa_frm0 conjunct, which cc_pre leaves out because it is the one
   premise that names the FP state (cross_check_d.v). *)
Theorem cc_run : (forall fx0 : YK11.FPState, cc_S1P (fx := fx0) B lit gotw guard STK_REF) ->
  (forall fx0 : YK11.FPState, cc_S2P (fx := fx0) B lit gotw guard STK_REF) ->
  (forall fx0 : YK11.FPState, cc_S3P (fx := fx0) B lit gotw guard STK_REF) ->
  forall v, cc_pre B lit gotw guard STK_REF v -> frm0 fx ->
  SRr SEGS (x_W v) (cfg_at SEGS (BASE + AF_cross_check) (x_regs v) (x_mem v) (x_md v))
    (cc_post B lit gotw guard STK_REF v).
Proof.
intros S1 S2 S3 v HP HFRM.
assert (HEPI : forall fx0 : YK11.FPState, from_EPI (fx := fx0) B lit gotw guard STK_REF v)
  by (intros fx0; exact (S3 fx0 v HP)).
exact (S1 fx v HP (HEPI fx) (cc_loop S2 v HP HEPI 0 fx HFRM)).
Qed.
End e.
End f.
End d.

