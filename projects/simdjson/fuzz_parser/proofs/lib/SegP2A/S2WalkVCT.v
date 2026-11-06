(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec AxSymExec3 AxSymExec3Sound MemSplit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLearn SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim SjStage1 SjInvPath SjInv SjS2Inv SjS2Tab.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Ghost S2Lin S2Dig S2StrVC S2G2 S2WalkVC S2WalkLem S2WalkVCok.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2.
Open Scope Z_scope.

Definition keepK (K : kentry) : bool :=
  match K with
  | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ | KImg _ _ | KUnk _ _ => true
  | KFill (SA b o) (ELit n) _ | KZero (SA b o) (ELit n) =>
      match b with ELit _ => false | _ => if Z.leb n 4096 then Z.ltb o 1073741824 else false end
  | _ => false
  end.
Definition keepS (s : sidecond) : bool :=
  match s with
  | SCReadBase a w sx _ => if sx then (if Nat.eqb w 1 then negb (Z.eqb (a_off a) 2147450880) else true) else true
  | _ => true
  end.
Definition trimc (c : SG.vc) : SG.vc :=
  SG.VC (List.filter keepK (SG.vc_kn c)) (List.filter keepS (SG.vc_path c)) (SG.vc_log c) (SG.vc_src c) (SG.vc_tgt c) (SG.vc_facts c).

Definition wvc_okT (segs : list Segment) (MF TD : Z) (c : SG.vc) : bool := wvc_ok segs MF TD (trimc c).

Lemma Forall_filter_sub : forall {T : Type} (P : T -> Prop) (f : T -> bool) l, Forall P l -> Forall P (List.filter f l).
Proof.
  intros T P f l H. induction H as [|x l Hx Hl IH]; cbn; [constructor|].
  destruct (f x); [constructor; assumption | exact IH].
Qed.

Lemma vc_holds_trim : forall segs GP c, SG.vc_holds segs GP (trimc c) -> SG.vc_holds segs GP c.
Proof.
  intros segs GP c H E m HK HP HL HS.
  exact (H E m (Forall_filter_sub _ _ _ HK) (Forall_filter_sub _ _ _ HP) HL HS).
Qed.

Section Sound.
  Variable segs : list Segment.
  Variables data idxs : list Z.
  Variable MF : Z.
  Hypothesis MF_rng : 0 <= MF <= 2 ^ 30.
  Variable TD : Z.
  Hypothesis TD_rng : 0 <= TD /\ TD + 3544 < 2 ^ 64.
  Hypothesis D2V_IMG : forall m i, (forall x, TD <= x < TD + 3544 -> m (Z_to_bv 64 x) = None) -> 0 <= i < 886 ->
    rdn segs m (Z_to_bv 64 (TD + 4 * i)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (d2v i))).

  Theorem wvc_okT_sound : forall c, wvc_okT segs MF TD c = true -> SG.vc_holds segs (gp2 segs data idxs) c.
  Proof.
    intros c H. apply vc_holds_trim. exact (wvc_ok_sound segs data idxs MF MF_rng TD TD_rng D2V_IMG (trimc c) H).
  Qed.
End Sound.
