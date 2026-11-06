(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): reac_segconf_parse_file's contract from its 15 segment
   statements (lib/A/Prog/pf_pieces.v's pf_pieces_give_contract), proved. By the G3 walk owner, 2026-10-30.
   The proof is the one the G3 walk owner checked in a scratch file (the lane's notes, not in the tree):
   - H_DONE at every FP state is S_A4; H_TAIL 0 holds outright (its rest would be shorter than 0);
   - within one n the mid-line cuts follow from H_TAIL n in the order LOWOUT, MISS, MODEL; PROV2, NEW, FOUND;
     RS3, CLR; IGN; INTENT, ROLE; REF3, LONG; SEG, HDR; KEY; then H_HEAD n (S_A5's head part);
   - H_TAIL (S n) from H_HEAD n and H_DONE (S_A5's tail part), so H_TAIL and H_HEAD hold at every n by induction;
   - S_A3, S_A2, S_A1 close the entry; H_ENTRY at the ambient FP state is the contract once its premises are packed
     into the bundle pfv: pf_cx holds reac_segconf_parse_file_pre at SOME FP state (here the ambient one), and
     H_ENTRY's sa_frm0 is the 15th conjunct of the contract's reader_pre. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_pieces.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section g.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
Variable B : asyms.
Theorem pf_pieces_give_contract_holds : pf_pieces_give_contract B.
Proof.
unfold pf_pieces_give_contract.
intros A1 A2 A3 A4 A5 A6 A7 A8a A8b A9 A10a A10b A11a A11b A12.
assert (DONE : HA_DONE B) by (intros f; apply A4).
assert (TAIL0 : HA_TAIL B 0).
{ intros f. unfold H_TAIL. intros v pos lyc Sc Wc rX memc mdc cf cur nm o ln d (_ & _ & Hlt & _). lia. }
assert (MIDS : forall n, HA_TAIL B n -> HA_HEAD B n).
{ intros n T.
  assert (LOWOUT : HA_LOWOUT B n) by (intros f; exact (proj2 (A11b f n) T)).
  assert (MISS : HA_MISS B n) by (intros f; exact (proj1 (A11b f n) T)).
  assert (MODEL : HA_MODEL B n) by (intros f; exact (A11a f n MISS LOWOUT)).
  assert (PROV2 : HA_PROV2 B n) by (intros f; exact (proj2 (proj2 (A8b f n)) T)).
  assert (NEW : HA_NEW B n) by (intros f; exact (proj1 (A8b f n) T)).
  assert (FOUND : HA_FOUND B n) by (intros f; exact (proj1 (proj2 (A8b f n)) T)).
  assert (RS3 : HA_RS3 B n) by (intros f; exact (proj2 (proj2 (A7 f n)) T)).
  assert (CLR : HA_CLR B n) by (intros f; exact (proj1 (proj2 (A7 f n)) T)).
  assert (IGN : HA_IGN B n) by (intros f; exact (A12 f n RS3 PROV2)).
  assert (INTENT : HA_INTENT B n) by (intros f; exact (A10b f n T)).
  assert (ROLE : HA_ROLE B n) by (intros f; exact (A10a f n INTENT)).
  assert (REF3 : HA_REF3 B n) by (intros f; exact (proj2 (A6 f n) T)).
  assert (LONG : HA_LONG B n) by (intros f; exact (proj1 (A6 f n) T)).
  assert (SEG : HA_SEG B n) by (intros f; exact (A8a f n NEW FOUND CLR)).
  assert (HDR : HA_HDR B n) by (intros f; exact (proj1 (A7 f n) T SEG)).
  assert (KEY : HA_KEY B n) by (intros f; exact (A9 f n ROLE MODEL IGN REF3 T)).
  intros f. exact (proj1 (A5 f n) LONG HDR KEY T). }
assert (TAILS : forall n, HA_TAIL B n).
{ induction n as [|n IH]; [exact TAIL0|].
  intros f. exact (proj2 (A5 f (S n)) (MIDS n IH) DONE). }
assert (HEADS : forall n, HA_HEAD B n) by (intros n; exact (MIDS n (TAILS n))).
assert (FRAME : HA_FRAME B) by (intros f; exact (A3 f HEADS DONE)).
assert (FTAKEN : HA_FTAKEN B) by (intros f; exact (A2 f FRAME)).
pose proof (A1 fx FTAKEN) as ENTRY.
unfold reac_segconf_parse_file_contract.
intros ly S W regs mem md ch c t lp rcs s lab HPRE HROD H10 Hc H11 Ht H12 Hl HPF HROOM HEV.
(* sa_frm0 is reader_pre's 15th conjunct *)
pose proof HPF as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFRM & _) & _).
exact (ENTRY (mkPFV ly S W regs mem md ch c t lp rcs s lab)
  (conj HPRE (conj HROD (conj H10 (conj Hc (conj H11 (conj Ht (conj H12 (conj Hl
    (conj (ex_intro _ fx HPF) (conj HROOM HEV)))))))))) HFRM).
Qed.
End g.
