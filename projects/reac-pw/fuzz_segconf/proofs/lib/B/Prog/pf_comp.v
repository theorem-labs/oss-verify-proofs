(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): reac_segconf_parse_file's
   contract from its 16 segment statements (lib/B/Prog/pf_pieces.v's pf_pieces_give_contract, the image-B piece statements at
   80a6c9c97a8b), proved. The image-B composition lane of the image-B G3 walk owner, 2026-10-30.
   ADAPTED from the image-A G3 walk owner's image-A composition lib/A/Prog/pf_compose.v (commit 48b245830d40,
   the image-A composition lane): the same proof over B's cut set (B's new cuts HREF, REFTL, KREF, KREFM; A's RS3 has no B twin).
   The composition is logic over the cut statements only: the class-5 frame take (B1) and release (B4) and the lift
   of each exit cut taken at every FP state (HA_<CUT>, PaFx's srr_apost_baseF_lift) are inside the segments.
   - H_DONE at every FP state is S_B4; H_TAIL 0 holds outright (INV_TAIL 0 says the rest is shorter than 0);
   - within one n the mid-line cuts follow from H_TAIL n in the order LOWOUT, KREFM (S_B11c), MISS (S_B11b),
     MODEL (S_B11a); PROV2, NEW, FOUND (S_B8b); KREF (S_B9's second part); IGN (S_B12); INTENT (S_B10b), ROLE
     (S_B10a); REF3, LONG (S_B6); HREF, REFTL (S_B7's second and third parts); SEG (S_B8a); HDR (S_B7's first
     part); KEY (S_B9's first part); then H_HEAD n (S_B5h). CLR (S_B7's fourth part) is entered only from B7's own
     code, so no other statement takes it;
   - H_TAIL (S n) from H_HEAD n and H_DONE (S_B5t, pred (S n) = n), so H_TAIL and H_HEAD hold at every n by
     induction on the plain measure n;
   - S_B3 (H_HEAD at every n, H_DONE), S_B2, S_B1 close the entry; H_ENTRY at the ambient FP state is the contract
     once its premises are packed into the bundle pfv: pf_cx holds reac_segconf_parse_file_pre at SOME FP state
     (here the ambient one), and H_ENTRY's sa_frm0 is the 15th conjunct of the contract's reader_pre.
   Every exit cut a segment statement takes is an entry cut another statement gives at the same n (or at pred n
   for S_B5t, at every n for S_B3): no cut mismatch. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section g.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.
Theorem pf_pieces_give_contract_holds : pf_pieces_give_contract B.
Proof.
unfold pf_pieces_give_contract.
intros B1 B2 B3 B4 [B5h B5t] B6 B7 B8a B8b B9 B10a B10b B11a B11b B11c B12.
assert (DONE : HA_DONE B) by (intros f; apply B4).
assert (TAIL0 : HA_TAIL B 0).
{ intros f. unfold H_TAIL. intros v pos lyc Sc Wc rX memc mdc cf cur nm o ln d (_ & _ & Hlt & _). lia. }
assert (MIDS : forall n, HA_TAIL B n -> HA_HEAD B n).
{ intros n T.
  assert (LOWOUT : HA_LOWOUT B n) by (intros f; exact (proj2 (B11c f n) T)).
  assert (KREFM : HA_KREFM B n) by (intros f; exact (proj1 (B11c f n) T)).
  assert (MISS : HA_MISS B n) by (intros f; exact (B11b f n KREFM)).
  assert (MODEL : HA_MODEL B n) by (intros f; exact (B11a f n MISS LOWOUT)).
  assert (PROV2 : HA_PROV2 B n) by (intros f; exact (proj2 (proj2 (B8b f n)) T)).
  assert (NEW : HA_NEW B n) by (intros f; exact (proj1 (B8b f n) T)).
  assert (FOUND : HA_FOUND B n) by (intros f; exact (proj1 (proj2 (B8b f n)) T)).
  assert (KREF : HA_KREF B n) by (intros f; exact (proj2 (B9 f n) T)).
  assert (IGN : HA_IGN B n) by (intros f; exact (B12 f n KREF PROV2)).
  assert (INTENT : HA_INTENT B n) by (intros f; exact (B10b f n T)).
  assert (ROLE : HA_ROLE B n) by (intros f; exact (B10a f n INTENT)).
  assert (REF3 : HA_REF3 B n) by (intros f; exact (proj2 (B6 f n) T)).
  assert (LONG : HA_LONG B n) by (intros f; exact (proj1 (B6 f n) T)).
  assert (HREF : HA_HREF B n) by (intros f; exact (proj1 (proj2 (B7 f n)) T)).
  assert (REFTL : HA_REFTL B n) by (intros f; exact (proj1 (proj2 (proj2 (B7 f n))) T)).
  assert (SEG : HA_SEG B n) by (intros f; exact (B8a f n NEW FOUND REFTL)).
  assert (HDR : HA_HDR B n) by (intros f; exact (proj1 (B7 f n) T SEG)).
  assert (KEY : HA_KEY B n) by (intros f; exact (proj1 (B9 f n) ROLE MODEL IGN REF3 HREF T)).
  intros f. exact (B5h f n LONG HDR KEY T). }
assert (TAILS : forall n, HA_TAIL B n).
{ induction n as [|n IH]; [exact TAIL0|].
  intros f. exact (B5t f (S n) (MIDS n IH) DONE). }
assert (HEADS : forall n, HA_HEAD B n) by (intros n; exact (MIDS n (TAILS n))).
assert (FRAME : HA_FRAME B) by (intros f; exact (B3 f HEADS DONE)).
assert (FTAKEN : HA_FTAKEN B) by (intros f; exact (B2 f FRAME)).
pose proof (B1 fx FTAKEN) as ENTRY.
unfold reac_segconf_parse_file_contract.
intros ly S W regs mem md ch c t lp rcs s lab HPRE HROD H10 Hc H11 Ht H12 Hl HPF HROOM HEV.
(* sa_frm0 is reader_pre's 15th conjunct *)
pose proof HPF as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFRM & _) & _).
exact (ENTRY (mkPFV ly S W regs mem md ch c t lp rcs s lab)
  (conj HPRE (conj HROD (conj H10 (conj Hc (conj H11 (conj Ht (conj H12 (conj Hl
    (conj (ex_intro _ fx HPF) (conj HROOM HEV)))))))))) HFRM).
Qed.
End g.
