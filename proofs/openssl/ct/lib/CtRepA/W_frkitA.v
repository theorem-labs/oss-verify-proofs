(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge Arr FP Frame Cells Step RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog BnBase BnModel BnTree ApBase.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition fr_blk_okA (f : Z) (k : nat) (W : list (Z * Z)) (b : block) : Prop :=
  off_fr f k b
  \/ (Forall (fun iv => (shad f <= fst iv /\ snd iv <= shad f + fs_size k / 8) -> (snd iv <= shad (blk_addr b) \/ shad (blk_addr b + (blk_size b - 1)) < fst iv)) W).

Lemma AH_frame_frSA : forall Σ OW LB m m' W f k,
  In (f, k) FR -> AHEAP Σ OW LB m -> munch W m m' -> wmono ctasegs m m' ->
  Forall (fr_write_ok (OW ++ LB) f k) W -> (forall b, In b LB -> fr_blk_okA f k W b) -> AHEAP Σ OW LB m'.
Proof.
  intros Σ OW LB m m' W f k Hf H MU WM HW OFF. pose proof H as (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & FP & AP) & Rest).
  destruct (AH_fr_geo _ _ _ _ f k H Hf) as (G1 & G2 & G3 & G4 & G5). pose proof (AH_ceil _ _ _ _ H) as (C1 & C2 & C3).
  split; [| split; [exact HS | split; [exact HFr | split; [| exact Rest]]]].
  - apply (af_frame RT AF Σ m m' ACEIL HA); [unfold BnHeapA.ACEIL; rewrite HS; lia | | exact WM].
    intros a Hna. apply MU. rewrite HFr in Hna.
    clear - H HW Hna Hf. induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|].
    apply Forall_cons_iff in HW as [H1 H2]. split; [| exact (IH H2)].
    intros [L1 L2]. apply Hna. destruct H1 as [H1|[[X1 X2]|[X1 X2]]]; cbn [fst snd] in *.
    + apply (AH_aclient _ _ _ _ ACEIL _ H).
      destruct H1 as [[D1 D2]|[D|(b & Hb & D1 & D2)]]; cbn [fst snd] in *.
      * left. lia.
      * right; left. apply D. lia.
      * right; right. exists b. split; [exact Hb | lia].
    + right; right; right; left. exists f, k. split; [exact Hf | lia].
    + right; right; right; right. exists f, k. split; [exact Hf |]. rewrite shad_fr_end. lia.
  - split; [exact (fr_wr_wmono m m' FW WM)|]. exists PB, LBr. split; [exact P1|]. split; [exact P2|]. split; [| exact AP].
    apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) FP b Hb) as PK. destruct PK as (PI & Hn & WR & AC).
    split; [exact PI|]. split; [exact Hn|]. split; [exact (wr_at_transport ctasegs m m' _ _ WR WM)|].
    assert (HbL : In b LB) by (eapply Permutation_in; [symmetry; exact P1 | apply in_or_app; left; exact Hb]).
    assert (B0 : 0 < blk_addr b) by (destruct PI as (f' & k' & Hf' & Q1 & Q2); destruct (AH_fr_range _ _ _ _ f' k' H Hf') as (R1 & _); lia).
    eapply acc_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | exact AC |].
    intros i Hi. pose proof (pb_shadow_range _ _ _ _ b i H PI Hi) as SR.
    pose proof (shad_mono (blk_addr b) (blk_addr b + i) ltac:(lia)) as SM1. pose proof (shad_mono (blk_addr b + i) (blk_addr b + (blk_size b - 1)) ltac:(lia)) as SM2.
    destruct (OFF b HbL) as [O|O].
    + pose proof (off_fr_shadow f k b i ltac:(clear - G2; Z.div_mod_to_equations; lia) ltac:(lia) O Hi) as SO.
      clear - HW SR SO H G1 G3 G4 G5 C1 C2 C3 Hf. induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|].
      apply Forall_cons_iff in HW as [H1 H2]. split; [| exact (IH H2)].
      intros [L1 L2]. destruct H1 as [H1|[[X1 X2]|[X1 X2]]]; cbn [fst snd] in *.
      * destruct H1 as [[D1 D2]|[D|(b' & Hb' & D1 & D2)]]; cbn [fst snd] in *.
        -- unfold SHHI in *. lia.
        -- destruct (D _ (conj L1 L2)) as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
           unfold SHLO in SR. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
        -- pose proof (AH_offsh _ _ _ _ b' H Hb') as O'. lia.
      * unfold SHLO, SHHI in SR. lia.
      * lia.
    + clear - HW SR SM1 SM2 O H G1 G3 G4 G5 C1 C2 C3 Hf. induction W as [|[lo hi] W IH]; cbn [outside]; [exact I|].
      apply Forall_cons_iff in HW as [H1 H2]. apply Forall_cons_iff in O as [O1 O2]. split; [| exact (IH H2 O2)].
      intros [L1 L2]. destruct H1 as [H1|[[X1 X2]|[X1 X2]]]; cbn [fst snd] in *.
      * destruct H1 as [[D1 D2]|[D|(b' & Hb' & D1 & D2)]]; cbn [fst snd] in *.
        -- unfold SHHI in *. lia.
        -- destruct (D _ (conj L1 L2)) as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
           unfold SHLO in SR. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
        -- pose proof (AH_offsh _ _ _ _ b' H Hb') as O'. lia.
      * unfold SHLO, SHHI in SR. lia.
      * specialize (O1 (conj X1 X2)). lia.
Qed.

End WithRT.
