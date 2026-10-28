(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import BnBase.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import RT_iface D_defs.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnW Require Import BnMem BnTacX BnKaraMem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit AsLoop. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnIfaceA AsStruct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma client_static_rangeA : forall x, client_static x -> 65536 <= x < SEGTOP_A.
Proof.
  intros x [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. unfold SEGTOP_A.
  destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
Qed.

Section Bundle.
  Context {AR : ARun}.
  Local Notation RT := (@ar_RT AR).
  Local Notation ACEIL := (@BnHeapA.ACEIL AR).
  Local Notation AHEAP := (@BnHeapA.AHEAP AR).
  Variables (Σ : rts RT) (OW LB : list block).
  Variables (m : mem) (rp tq ap bp SP lo : Z) (a b : list Z) (nR nT : nat) (FS SK FB : Z).
  Variables (bR bT bA bB : block).
  Hypothesis FS0 : 0 <= FS.
  Hypothesis FBE : FB = SP - FS.
  Hypothesis SK0 : 0 <= SK.
  Hypothesis DRA : rp + 8 * Z.of_nat nR <= ap \/ ap + 8 * Z.of_nat (length a) <= rp.
  Hypothesis DRB : rp + 8 * Z.of_nat nR <= bp \/ bp + 8 * Z.of_nat (length b) <= rp.
  Hypothesis DTA : tq + 8 * Z.of_nat nT <= ap \/ ap + 8 * Z.of_nat (length a) <= tq.
  Hypothesis DTB : tq + 8 * Z.of_nat nT <= bp \/ bp + 8 * Z.of_nat (length b) <= tq.
  Hypothesis DRT : rp + 8 * Z.of_nat nR <= tq \/ tq + 8 * Z.of_nat nT <= rp.
  Hypothesis SEPR : rp + 8 * Z.of_nat nR <= SP - FS - SK \/ SP <= rp.
  Hypothesis SEPT : tq + 8 * Z.of_nat nT <= SP - FS - SK \/ SP <= tq.
  Hypothesis SEPA : ap + 8 * Z.of_nat (length a) <= SP - FS - SK \/ SP <= ap.
  Hypothesis SEPB : bp + 8 * Z.of_nat (length b) <= SP - FS - SK \/ SP <= bp.
  (* [comment removed for export] *)
  Hypothesis INR : In bR OW.
  Hypothesis INT : In bT OW.
  Hypothesis INA : In bA (OW ++ LB).
  Hypothesis INB : In bB (OW ++ LB).
  Hypothesis RGR : blk_addr bR <= rp /\ rp + 8 * Z.of_nat nR <= blk_addr bR + blk_size bR.
  Hypothesis RGT : blk_addr bT <= tq /\ tq + 8 * Z.of_nat nT <= blk_addr bT + blk_size bT.
  Hypothesis RGA : blk_addr bA <= ap /\ ap + 8 * Z.of_nat (length a) <= blk_addr bA + blk_size bA.
  Hypothesis RGB : blk_addr bB <= bp /\ bp + 8 * Z.of_nat (length b) <= blk_addr bB + blk_size bB.
  Hypothesis CEIL : ACEIL <= lo.
  Hypothesis LOK : lo <= SP - FS - SK.
  Hypothesis SPT : SP <= USTACK_TOP.

  (* [comment removed for export] *)
  Definition KAGP (sp' : Z) (x : Z) : Prop :=
    aclient_addr (OW ++ LB) sp' x /\ ~ (rp <= x < rp + 8 * Z.of_nat nR) /\ ~ (tq <= x < tq + 8 * Z.of_nat nT).
  Definition KAG (m0 m1 : mem) : Prop := agree_on (KAGP SP) m0 m1.

  (* [comment removed for export] *)
  Definition KW (offR lenR offT lenT : nat) : list ivl :=
    [(rp + 8 * Z.of_nat offR, rp + 8 * Z.of_nat offR + 8 * Z.of_nat lenR);
     (tq + 8 * Z.of_nat offT, tq + 8 * Z.of_nat offT + 8 * Z.of_nat lenT);
     (FB - SK, FB)].

  Definition KB (cells : list cell) (m1 : mem) (R T : list Z) : Prop :=
    limbs R /\ limbs T /\ length R = nR /\ length T = nT /\
    limbs_at bsegs m1 rp R /\ limbs_at bsegs m1 tq T /\ limbs_at bsegs m1 ap a /\ limbs_at bsegs m1 bp b /\
    wr_at bsegs m1 rp (8 * Z.of_nat nR) /\ wr_at bsegs m1 tq (8 * Z.of_nat nT) /\
    rw_cells bsegs m1 FB cells /\ stk bsegs m1 lo FB /\ mem_inv bsegs m1 /\
    AHEAP Σ OW LB m1 /\ KAG m m1 /\ wmono bsegs m m1.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition kw_ok (iv : Z * Z) : Prop :=
    (lo <= fst iv /\ snd iv <= SP) \/ (rp <= fst iv /\ snd iv <= rp + 8 * Z.of_nat nR) \/ (tq <= fst iv /\ snd iv <= tq + 8 * Z.of_nat nT).

  Lemma kw_heap : forall W m1 m2, AHEAP Σ OW LB m1 -> munch W m1 m2 -> wmono bsegs m1 m2 -> Forall kw_ok W -> AHEAP Σ OW LB m2.
  Proof using All.
    intros W m1 m2 HEAP MU WM HW. eapply (seg_heap Σ OW LB m1 m2 W lo SP HEAP MU WM); [ | exact CEIL | exact SPT].
    eapply Forall_impl; [|exact HW]. intros [x y] [H|[H|H]]; cbn [fst snd] in *.
    - left. exact H.
    - right. exists bR. split; [exact INR|]. cbn [fst snd]. lia.
    - right. exists bT. split; [exact INT|]. cbn [fst snd]. lia.
  Qed.

  Lemma kw_agree : forall W m1 m2, AHEAP Σ OW LB m1 -> munch W m1 m2 -> Forall kw_ok W -> KAG m1 m2.
  Proof using All.
    intros W m1 m2 HEAP MU HW. unfold KAG. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|].
    intros x (Hc & HnR & HnT). pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). clear MU.
    induction HW as [|[p q] W Hiv HW IH]; [exact I|]. cbn [outside]. split; [|exact IH].
    intros Hx. destruct Hiv as [H|[H|H]]; cbn [fst snd] in H.
    - destruct Hc as [Hc|[Hc|(bb & Hb & Hr)]]; [lia | |].
      + pose proof (client_static_rangeA x Hc). lia.
      + pose proof (AH_range_gen _ _ _ _ bb HEAP Hb) as (_ & _ & _ & BC & _). lia.
    - apply HnR. lia.
    - apply HnT. lia.
  Qed.

  Lemma KB_upd : forall cells m1 m2 R T offR segR offT segT,
    Z.of_nat (cells_size cells) = FS ->
    KB cells m1 R T ->
    munch (KW offR (length segR) offT (length segT)) m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo FB ->
    limbs segR -> limbs segT -> (offR + length segR <= nR)%nat -> (offT + length segT <= nT)%nat ->
    limbs_at bsegs m2 (rp + 8 * Z.of_nat offR) segR -> limbs_at bsegs m2 (tq + 8 * Z.of_nat offT) segT ->
    KB cells m2 (splice R offR segR) (splice T offT segT).
  Proof using All.
    intros cells m1 m2 R T offR segR offT segT CS (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & AG & WM)
           MUc WMc MIc STc LsR LsT HoR HoT HsR HsT.
    assert (KOK : Forall kw_ok (KW offR (length segR) offT (length segT))).
    { unfold KW. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]; unfold kw_ok; cbn [fst snd].
      - right; left. lia.
      - right; right. lia.
      - left. lia. }
    unfold KB.
    split; [apply splice_limbs; assumption|]. split; [apply splice_limbs; assumption|].
    split; [rewrite splice_length; lia|]. split; [rewrite splice_length; lia|].
    split. { eapply limbs_at_splice; [exact HR | exact MUc | lia | exact HsR | |]; unfold KW; cbn [disjoint_from]; rewrite ?ER;
             clear - HoR HoT DRT SEPR FS0 SK0 FBE; lia. }
    split. { eapply limbs_at_splice; [exact HT | exact MUc | lia | exact HsT | |]; unfold KW; cbn [disjoint_from]; rewrite ?ET;
             clear - HoR HoT DRT SEPT FS0 SK0 FBE; lia. }
    split. { eapply limbs_at_transport; [exact HA | exact MUc |]. unfold KW; cbn [disjoint_from]. clear - HoR HoT DRA DTA SEPA FS0 SK0 FBE. lia. }
    split. { eapply limbs_at_transport; [exact HB | exact MUc |]. unfold KW; cbn [disjoint_from]. clear - HoR HoT DRB DTB SEPB FS0 SK0 FBE. lia. }
    split. { eapply wr_at_transport; [exact WR | exact WMc]. }
    split. { eapply wr_at_transport; [exact WT | exact WMc]. }
    split. { eapply rw_cells_transport; [exact FR | exact MUc | exact WMc |]. unfold KW; cbn [disjoint_from]. rewrite CS.
             clear - HoR HoT SEPR SEPT FS0 SK0 FBE. lia. }
    split; [exact STc|]. split; [exact MIc|].
    split. { exact (kw_heap _ m1 m2 HEAP MUc WMc KOK). }
    split. { eapply agree_on_trans; [exact AG | exact (kw_agree _ m1 m2 HEAP MUc KOK)]. }
    eapply wmono_trans; [exact WM | exact WMc].
  Qed.
  (* [comment removed for export] *)
  Lemma KB_after_R : forall cells m1 m2 R T off seg len8 fsz,
    Z.of_nat (cells_size cells) = FS -> KB cells m1 R T ->
    munch [(rp + 8 * Z.of_nat off, rp + 8 * Z.of_nat off + len8); (FB - fsz, FB)] m1 m2 ->
    len8 = 8 * Z.of_nat (length seg) -> 0 <= fsz <= SK ->
    wmono bsegs m1 m2 -> mem_inv bsegs m2 -> limbs_at bsegs m2 (rp + 8 * Z.of_nat off) seg -> stk bsegs m2 lo FB ->
    limbs seg -> (off + length seg <= nR)%nat ->
    KB cells m2 (splice R off seg) T.
  Proof using All.
    intros cells m1 m2 R T off seg len8 fsz CS I MUc E8 Hf WMc MIc HS STc LS Ho.
    pose proof I as (_ & _ & _ & ET & _ & HT & _).
    pose proof (limbs_at_bound _ _ _ _ HT) as BT.
    rewrite <- (splice_nil T 0) by lia.
    eapply KB_upd with (m1 := m1); try eassumption.
    - eapply munch_weaken; [|exact MUc]. unfold sub_fp, KW. cbn [outside length]. intros x Hx. clear - Hx E8 Hf. lia.
    - constructor.
    - cbn [length]. lia.
    - apply limbs_at_nil. clear - BT. lia.
  Qed.
  Lemma KB_after_T : forall cells m1 m2 R T off seg len8 fsz,
    Z.of_nat (cells_size cells) = FS -> KB cells m1 R T ->
    munch [(tq + 8 * Z.of_nat off, tq + 8 * Z.of_nat off + len8); (FB - fsz, FB)] m1 m2 ->
    len8 = 8 * Z.of_nat (length seg) -> 0 <= fsz <= SK ->
    wmono bsegs m1 m2 -> mem_inv bsegs m2 -> limbs_at bsegs m2 (tq + 8 * Z.of_nat off) seg -> stk bsegs m2 lo FB ->
    limbs seg -> (off + length seg <= nT)%nat ->
    KB cells m2 R (splice T off seg).
  Proof using All.
    intros cells m1 m2 R T off seg len8 fsz CS I MUc E8 Hf WMc MIc HS STc LS Ho.
    pose proof I as (_ & _ & ER & _ & HR & _).
    pose proof (limbs_at_bound _ _ _ _ HR) as BR.
    rewrite <- (splice_nil R 0) by lia.
    eapply KB_upd with (m1 := m1); try eassumption.
    - eapply munch_weaken; [|exact MUc]. unfold sub_fp, KW. cbn [outside length]. intros x Hx. clear - Hx E8 Hf. lia.
    - constructor.
    - cbn [length]. lia.
    - apply limbs_at_nil. clear - BR. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma KB_after_ro : forall cells m1 m2 R T fsz,
    Z.of_nat (cells_size cells) = FS -> KB cells m1 R T ->
    munch [(FB - fsz, FB)] m1 m2 -> 0 <= fsz <= SK ->
    wmono bsegs m1 m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo FB ->
    KB cells m2 R T.
  Proof using All.
    intros cells m1 m2 R T fsz CS I MUc Hf WMc MIc STc.
    pose proof I as (_ & _ & ER & ET & HR & HT & _).
    pose proof (limbs_at_bound _ _ _ _ HR) as BR. pose proof (limbs_at_bound _ _ _ _ HT) as BT.
    rewrite <- (splice_nil R 0) by lia. rewrite <- (splice_nil T 0) by lia.
    eapply KB_upd with (m1 := m1); try eassumption.
    - eapply munch_weaken; [|exact MUc]. unfold sub_fp, KW. cbn [outside length]. intros x Hx. clear - Hx Hf. lia.
    - constructor.
    - constructor.
    - cbn [length]. lia.
    - cbn [length]. lia.
    - apply limbs_at_nil. clear - BR. lia.
    - apply limbs_at_nil. clear - BT. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma KB_after_RT : forall cells m1 m2 R T offR segR offT segT lenR8 lenT8 fsz,
    Z.of_nat (cells_size cells) = FS -> KB cells m1 R T ->
    munch [(rp + 8 * Z.of_nat offR, rp + 8 * Z.of_nat offR + lenR8); (tq + 8 * Z.of_nat offT, tq + 8 * Z.of_nat offT + lenT8); (FB - fsz, FB)] m1 m2 ->
    lenR8 = 8 * Z.of_nat (length segR) -> lenT8 = 8 * Z.of_nat (length segT) -> 0 <= fsz <= SK ->
    wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
    limbs_at bsegs m2 (rp + 8 * Z.of_nat offR) segR -> limbs_at bsegs m2 (tq + 8 * Z.of_nat offT) segT -> stk bsegs m2 lo FB ->
    limbs segR -> limbs segT -> (offR + length segR <= nR)%nat -> (offT + length segT <= nT)%nat ->
    KB cells m2 (splice R offR segR) (splice T offT segT).
  Proof using All.
    intros cells m1 m2 R T offR segR offT segT lenR8 lenT8 fsz CS I MUc ER8 ET8 Hf WMc MIc HSR HST STc LSR LST HoR HoT.
    eapply KB_upd with (m1 := m1); try eassumption.
    eapply munch_weaken; [|exact MUc]. unfold sub_fp, KW. cbn [outside length]. intros x Hx. clear - Hx ER8 ET8 Hf. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma KB_after_TT : forall cells m1 m2 R T off off2 seg1 seg2 len18 len28 fsz,
    Z.of_nat (cells_size cells) = FS -> KB cells m1 R T ->
    munch [(tq + 8 * Z.of_nat off, tq + 8 * Z.of_nat off + len18); (tq + 8 * Z.of_nat off2, tq + 8 * Z.of_nat off2 + len28); (FB - fsz, FB)] m1 m2 ->
    len18 = 8 * Z.of_nat (length seg1) -> len28 = 8 * Z.of_nat (length seg2) -> off2 = (off + length seg1)%nat -> 0 <= fsz <= SK ->
    wmono bsegs m1 m2 -> mem_inv bsegs m2 ->
    limbs_at bsegs m2 (tq + 8 * Z.of_nat off) seg1 -> limbs_at bsegs m2 (tq + 8 * Z.of_nat off2) seg2 -> stk bsegs m2 lo FB ->
    limbs seg1 -> limbs seg2 -> (off2 + length seg2 <= nT)%nat ->
    KB cells m2 R (splice T off (seg1 ++ seg2)).
  Proof using All.
    intros cells m1 m2 R T off off2 seg1 seg2 len18 len28 fsz CS I MUc E18 E28 Eo Hf WMc MIc HS1 HS2 STc LS1 LS2 Ho.
    pose proof I as (_ & _ & ER & _ & HR & _).
    pose proof (limbs_at_bound _ _ _ _ HR) as BR.
    rewrite <- (splice_nil R 0) by lia.
    eapply KB_upd with (m1 := m1); try eassumption.
    - eapply munch_weaken; [|exact MUc]. unfold sub_fp, KW. cbn [outside length]. rewrite length_app. intros x Hx. clear - Hx E18 E28 Eo Hf. lia.
    - constructor.
    - apply limbs_app; assumption.
    - cbn [length]. lia.
    - rewrite length_app. lia.
    - apply limbs_at_nil. clear - BR. lia.
    - apply limbs_at_app. split; [exact HS1|].
      replace (tq + 8 * Z.of_nat off + 8 * Z.of_nat (length seg1)) with (tq + 8 * Z.of_nat off2) by (subst off2; lia). exact HS2.
  Qed.


  (* [comment removed for export] *)
  Lemma KB_cps : forall cells m1 m2 R T offR segR offT segT,
    Z.of_nat (cells_size cells) = FS ->
    KB cells m1 R T ->
    AHEAP Σ OW LB m2 ->
    agree_on (fun x => aclient_addr (OW ++ LB) FB x
                       /\ ~ (rp + 8 * Z.of_nat offR <= x < rp + 8 * Z.of_nat offR + 8 * Z.of_nat (length segR))
                       /\ ~ (tq + 8 * Z.of_nat offT <= x < tq + 8 * Z.of_nat offT + 8 * Z.of_nat (length segT))) m1 m2 ->
    wmono bsegs m1 m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo FB ->
    limbs segR -> limbs segT -> (offR + length segR <= nR)%nat -> (offT + length segT <= nT)%nat ->
    limbs_at bsegs m2 (rp + 8 * Z.of_nat offR) segR -> limbs_at bsegs m2 (tq + 8 * Z.of_nat offT) segT ->
    KB cells m2 (splice R offR segR) (splice T offT segT).
  Proof using All.
    intros cells m1 m2 R T offR segR offT segT CS (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & AG & WM)
           HEAP2 AGc WMc MIc STc LsR LsT HoR HoT HsR HsT.
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _).
    assert (INBLK : forall bb p n x, In bb (OW ++ LB) -> blk_addr bb <= p -> p + n <= blk_addr bb + blk_size bb -> p <= x < p + n ->
              aclient_addr (OW ++ LB) FB x).
    { intros bb p n x Hb H1 H2 Hx. right. right. exists bb. split; [exact Hb | lia]. }
    assert (INRb : In bR (OW ++ LB)) by (apply in_or_app; left; exact INR).
    assert (INTb : In bT (OW ++ LB)) by (apply in_or_app; left; exact INT).
    (* [comment removed for export] *)
    assert (TR : forall bb p (l : list Z), In bb (OW ++ LB) -> blk_addr bb <= p -> p + 8 * Z.of_nat (length l) <= blk_addr bb + blk_size bb ->
              (p + 8 * Z.of_nat (length l) <= rp + 8 * Z.of_nat offR \/ rp + 8 * Z.of_nat offR + 8 * Z.of_nat (length segR) <= p) ->
              (p + 8 * Z.of_nat (length l) <= tq + 8 * Z.of_nat offT \/ tq + 8 * Z.of_nat offT + 8 * Z.of_nat (length segT) <= p) ->
              limbs_at bsegs m1 p l -> limbs_at bsegs m2 p l).
    { intros bb p l Hb H1 H2 D1 D2 HL. unfold limbs_at in *. eapply bytes_at_agree; [exact AGc | exact HL |].
      rewrite lbytes_lengthZ. intros x Hx. split; [eapply (INBLK bb p _ x Hb H1 H2); lia |]. split; lia. }
    pose proof (limbs_at_firstn bsegs m1 rp R offR HR) as HR1.
    pose proof (limbs_at_skipn bsegs m1 rp R (offR + length segR) HR ltac:(lia)) as HR3.
    pose proof (limbs_at_firstn bsegs m1 tq T offT HT) as HT1.
    pose proof (limbs_at_skipn bsegs m1 tq T (offT + length segT) HT ltac:(lia)) as HT3.
    unfold KB.
    split; [apply splice_limbs; assumption|]. split; [apply splice_limbs; assumption|].
    split; [rewrite splice_length; lia|]. split; [rewrite splice_length; lia|].
    split.
    { unfold splice. apply limbs_at_app. split.
      - apply (TR bR); [exact INRb | lia | rewrite length_firstn, Nat.min_l by lia; lia | rewrite length_firstn, Nat.min_l by lia; lia
                       | rewrite length_firstn, Nat.min_l by lia; clear - DRT HoR HoT ER ET; lia | exact HR1].
      - rewrite length_firstn, Nat.min_l by lia. apply limbs_at_app. split; [exact HsR|].
        replace (rp + 8 * Z.of_nat offR + 8 * Z.of_nat (length segR)) with (rp + 8 * Z.of_nat (offR + length segR)) by lia.
        apply (TR bR); [exact INRb | lia | rewrite length_skipn; lia | rewrite length_skipn; lia
                       | rewrite length_skipn; clear - DRT HoR HoT ER ET; lia | exact HR3]. }
    split.
    { unfold splice. apply limbs_at_app. split.
      - apply (TR bT); [exact INTb | lia | rewrite length_firstn, Nat.min_l by lia; lia
                       | rewrite length_firstn, Nat.min_l by lia; clear - DRT HoR HoT ER ET; lia | rewrite length_firstn, Nat.min_l by lia; lia | exact HT1].
      - rewrite length_firstn, Nat.min_l by lia. apply limbs_at_app. split; [exact HsT|].
        replace (tq + 8 * Z.of_nat offT + 8 * Z.of_nat (length segT)) with (tq + 8 * Z.of_nat (offT + length segT)) by lia.
        apply (TR bT); [exact INTb | lia | rewrite length_skipn; lia
                       | rewrite length_skipn; clear - DRT HoR HoT ER ET; lia | rewrite length_skipn; lia | exact HT3]. }
    split. { apply (TR bA); [exact INA | lia | lia | clear - DRA HoR; lia | clear - DTA HoT; lia | exact HA]. }
    split. { apply (TR bB); [exact INB | lia | lia | clear - DRB HoR; lia | clear - DTB HoT; lia | exact HB]. }
    split. { eapply wr_at_transport; [exact WR | exact WMc]. }
    split. { eapply wr_at_transport; [exact WT | exact WMc]. }
    split. { eapply rw_cells_agree; [exact AGc | exact FR |]. rewrite CS. intros x Hx.
             split; [left; lia|]. split; [clear - Hx HoR SEPR FS0 SK0 FBE; lia | clear - Hx HoT SEPT FS0 SK0 FBE; lia]. }
    split; [exact STc|]. split; [exact MIc|]. split; [exact HEAP2|].
    split. { eapply agree_on_trans; [exact AG|]. eapply agree_on_mono; [exact AGc|]. unfold KAGP.
             intros x (Hc & HnR & HnT). split; [|split; [clear - HnR HoR; lia | clear - HnT HoT; lia]].
             destruct Hc as [Hc|[Hc|Hc]]; [left; lia | right; left; exact Hc | right; right; exact Hc]. }
    eapply wmono_trans; [exact WM | exact WMc].
  Qed.

  (* [comment removed for export] *)
  Lemma KB_cps_TT : forall cells m1 m2 R T off off2 seg1 seg2,
    Z.of_nat (cells_size cells) = FS ->
    KB cells m1 R T ->
    AHEAP Σ OW LB m2 ->
    agree_on (fun x => aclient_addr (OW ++ LB) FB x
                       /\ ~ (tq + 8 * Z.of_nat off <= x < tq + 8 * Z.of_nat off + 8 * Z.of_nat (length seg1))
                       /\ ~ (tq + 8 * Z.of_nat off2 <= x < tq + 8 * Z.of_nat off2 + 8 * Z.of_nat (length seg2))) m1 m2 ->
    off2 = (off + length seg1)%nat ->
    wmono bsegs m1 m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo FB ->
    limbs seg1 -> limbs seg2 -> (off2 + length seg2 <= nT)%nat ->
    limbs_at bsegs m2 (tq + 8 * Z.of_nat off) seg1 -> limbs_at bsegs m2 (tq + 8 * Z.of_nat off2) seg2 ->
    KB cells m2 R (splice T off (seg1 ++ seg2)).
  Proof using All.
    intros cells m1 m2 R T off off2 seg1 seg2 CS I HEAP2 AGc Eo WMc MIc STc LS1 LS2 Ho HS1 HS2.
    pose proof I as (_ & _ & ER & _ & HR & _).
    pose proof (limbs_at_bound _ _ _ _ HR) as BR.
    rewrite <- (splice_nil R 0) by lia.
    eapply KB_cps with (m1 := m1); try eassumption.
    - eapply agree_on_mono; [exact AGc|]. intros x (Hc & _ & HnT). split; [exact Hc|].
      rewrite length_app in HnT. split; [clear - HnT Eo; lia | clear - HnT Eo; lia].
    - constructor.
    - apply limbs_app; assumption.
    - cbn [length]. lia.
    - rewrite length_app. lia.
    - apply limbs_at_nil. clear - BR. lia.
    - apply limbs_at_app. split; [exact HS1|].
      replace (tq + 8 * Z.of_nat off + 8 * Z.of_nat (length seg1)) with (tq + 8 * Z.of_nat off2) by (subst off2; lia). exact HS2.
  Qed.

  (* [comment removed for export] *)
  Lemma KB_cps_T : forall cells m1 m2 R T off seg,
    Z.of_nat (cells_size cells) = FS ->
    KB cells m1 R T ->
    AHEAP Σ OW LB m2 ->
    agree_on (fun x => aclient_addr (OW ++ LB) FB x
                       /\ ~ (tq + 8 * Z.of_nat off <= x < tq + 8 * Z.of_nat off + 8 * Z.of_nat (length seg))) m1 m2 ->
    wmono bsegs m1 m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo FB ->
    limbs seg -> (off + length seg <= nT)%nat ->
    limbs_at bsegs m2 (tq + 8 * Z.of_nat off) seg ->
    KB cells m2 R (splice T off seg).
  Proof using All.
    intros cells m1 m2 R T off seg CS I HEAP2 AGc WMc MIc STc LS Ho HS.
    pose proof I as (_ & _ & ER & _ & HR & _).
    pose proof (limbs_at_bound _ _ _ _ HR) as BR.
    rewrite <- (splice_nil R 0) by lia.
    eapply KB_cps with (m1 := m1); try eassumption.
    - eapply agree_on_mono; [exact AGc|]. intros x (Hc & _ & HnT). split; [exact Hc | exact HnT].
    - constructor.
    - cbn [length]. lia.
    - apply limbs_at_nil. clear - BR. lia.
  Qed.
  Lemma KB_cps_R : forall cells m1 m2 R T off seg,
    Z.of_nat (cells_size cells) = FS ->
    KB cells m1 R T ->
    AHEAP Σ OW LB m2 ->
    agree_on (fun x => aclient_addr (OW ++ LB) FB x
                       /\ ~ (rp + 8 * Z.of_nat off <= x < rp + 8 * Z.of_nat off + 8 * Z.of_nat (length seg))) m1 m2 ->
    wmono bsegs m1 m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo FB ->
    limbs seg -> (off + length seg <= nR)%nat ->
    limbs_at bsegs m2 (rp + 8 * Z.of_nat off) seg ->
    KB cells m2 (splice R off seg) T.
  Proof using All.
    intros cells m1 m2 R T off seg CS I HEAP2 AGc WMc MIc STc LS Ho HS.
    pose proof I as (_ & _ & _ & ET & _ & HT & _).
    pose proof (limbs_at_bound _ _ _ _ HT) as BT.
    rewrite <- (splice_nil T 0) by lia.
    eapply KB_cps with (m1 := m1); try eassumption.
    - eapply agree_on_mono; [exact AGc|]. intros x (Hc & HnR & _). split; [exact Hc | exact HnR].
    - constructor.
    - cbn [length]. lia.
    - apply limbs_at_nil. clear - BT. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma KB_frame : forall cells cells' m1 m2 R T,
    KB cells m1 R T ->
    munch [(FB, FB + FS)] m1 m2 -> wmono bsegs m1 m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo FB ->
    rw_cells bsegs m2 FB cells' ->
    KB cells' m2 R T.
  Proof using All.
    intros cells cells' m1 m2 R T (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & AG & WM) MUc WMc MIc STc FR'.
    assert (KOK : Forall kw_ok [(FB, FB + FS)]).
    { apply Forall_cons; [|apply Forall_nil]. unfold kw_ok. cbn [fst snd]. left. lia. }
    unfold KB.
    split; [exact LR|]. split; [exact LT|]. split; [exact ER|]. split; [exact ET|].
    split. { eapply limbs_at_transport; [exact HR | exact MUc |]. cbn [disjoint_from]. rewrite ER. clear - SEPR FS0 SK0 FBE. lia. }
    split. { eapply limbs_at_transport; [exact HT | exact MUc |]. cbn [disjoint_from]. rewrite ET. clear - SEPT FS0 SK0 FBE. lia. }
    split. { eapply limbs_at_transport; [exact HA | exact MUc |]. cbn [disjoint_from]. clear - SEPA FS0 SK0 FBE. lia. }
    split. { eapply limbs_at_transport; [exact HB | exact MUc |]. cbn [disjoint_from]. clear - SEPB FS0 SK0 FBE. lia. }
    split. { eapply wr_at_transport; [exact WR | exact WMc]. }
    split. { eapply wr_at_transport; [exact WT | exact WMc]. }
    split; [exact FR'|]. split; [exact STc|]. split; [exact MIc|].
    split. { exact (kw_heap _ m1 m2 HEAP MUc WMc KOK). }
    split. { eapply agree_on_trans; [exact AG | exact (kw_agree _ m1 m2 HEAP MUc KOK)]. }
    eapply wmono_trans; [exact WM | exact WMc].
  Qed.

  (* [comment removed for export] *)
  Lemma KB_storeR : forall cells m1 R T (i : nat) v,
    Z.of_nat (cells_size cells) = FS ->
    KB cells m1 R T -> (i < nR)%nat -> limb v ->
    store_ok bsegs m1 (wa (rp + 8 * Z.of_nat i)) 8 = true /\
    KB cells (write_to_mem m1 (wa (rp + 8 * Z.of_nat i)) (le8 (Z_to_bv 64 v))) (upd R i v) T.
  Proof using All.
    intros cells m1 R T i v CS (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & HEAP & AG & WM) Hi Hv.
    pose proof (limbs_at_bound _ _ _ _ HA) as BA. pose proof (limbs_at_bound _ _ _ _ HB) as BB.
    pose proof (limbs_at_bound _ _ _ _ HT) as BT. pose proof (limbs_at_bound _ _ _ _ HR) as BR.
    pose proof (rw_cells_bound _ _ _ _ FR) as BF. rewrite CS in BF.
    rewrite ER in BR. rewrite ET in BT. change (2 ^ 64) with 18446744073709551616 in *.
    assert (L8 : length (le8 (Z_to_bv 64 v)) = 8%nat) by apply length_le8.
    assert (SOK : store_ok bsegs m1 (wa (rp + 8 * Z.of_nat i)) 8 = true).
    { apply (wr_at_store_ok bsegs m1 rp (8 * Z.of_nat nR)); [exact WR | lia | lia]. }
    split; [exact SOK|].
    assert (MUw : munch [(rp + 8 * Z.of_nat i, rp + 8 * Z.of_nat i + 8)] m1 (write_to_mem m1 (wa (rp + 8 * Z.of_nat i)) (le8 (Z_to_bv 64 v)))).
    { apply munch_write; [apply munch_refl | lia | rewrite L8; lia | rewrite L8; cbn [inside]; left; lia]. }
    assert (WMw : wmono bsegs m1 (write_to_mem m1 (wa (rp + 8 * Z.of_nat i)) (le8 (Z_to_bv 64 v)))) by (apply wmono_write; apply wmono_refl).
    assert (KOK : Forall kw_ok [(rp + 8 * Z.of_nat i, rp + 8 * Z.of_nat i + 8)]).
    { apply Forall_cons; [|apply Forall_nil]. unfold kw_ok. cbn [fst snd]. right. left. lia. }
    unfold KB.
    split; [apply upd_limbs; assumption|]. split; [exact LT|].
    split; [rewrite upd_length; lia|]. split; [exact ET|].
    split.
    { unfold upd, splice. cbn [length].
      pose proof (limbs_at_firstn bsegs m1 rp R i HR) as H1.
      pose proof (limbs_at_skipn bsegs m1 rp R (i + 1) HR ltac:(lia)) as H3.
      apply limbs_at_app. split.
      - apply limbs_at_write_other; [exact H1 | lia | rewrite L8; lia | rewrite L8, length_firstn, Nat.min_l by lia; left; lia].
      - rewrite length_firstn, Nat.min_l by lia. apply limbs_at_app. split.
        + unfold limbs_at. rewrite lbytes_cons, lbytes_nil, app_nil_r. apply bytes_at_write_same; [lia | rewrite L8; lia].
        + cbn [length]. replace (rp + 8 * Z.of_nat i + 8 * Z.of_nat 1) with (rp + 8 * Z.of_nat (i + 1)) by lia.
          apply limbs_at_write_other; [exact H3 | lia | rewrite L8; lia | rewrite L8; right; lia]. }
    split. { apply limbs_at_write_other; [exact HT | lia | rewrite L8; lia | rewrite L8, ET; clear - DRT Hi; lia]. }
    split. { apply limbs_at_write_other; [exact HA | lia | rewrite L8; lia | rewrite L8; clear - DRA Hi; lia]. }
    split. { apply limbs_at_write_other; [exact HB | lia | rewrite L8; lia | rewrite L8; clear - DRB Hi; lia]. }
    split; [apply wr_at_write; exact WR|]. split; [apply wr_at_write; exact WT|].
    split. { apply rw_cells_frame; [exact FR | lia | rewrite L8; lia | rewrite L8, CS; clear - SEPR Hi FBE SK0 FS0; lia]. }
    split. { apply stk_write; [exact ST | lia | rewrite L8; lia]. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { exact (kw_heap _ m1 _ HEAP MUw WMw KOK). }
    split. { eapply agree_on_trans; [exact AG | exact (kw_agree _ m1 _ HEAP MUw KOK)]. }
    eapply wmono_trans; [exact WM | exact WMw].
  Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
  Lemma KB_R : forall cells m1 R T off len, KB cells m1 R T -> (off + len <= nR)%nat ->
    limbs_at bsegs m1 (rp + 8 * Z.of_nat off) (slice R off len) /\ limbs (slice R off len) /\ length (slice R off len) = len /\
    wr_at bsegs m1 (rp + 8 * Z.of_nat off) (8 * Z.of_nat len).
  Proof using All.
    intros cells m1 R T off len (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & _) H.
    split; [apply limbs_at_slice; [exact HR | lia]|]. split; [apply slice_limbs; exact LR|]. split; [apply slice_length; lia|].
    replace (rp + 8 * Z.of_nat off) with (rp + (8 * Z.of_nat off)) by lia. eapply wr_at_sub; [exact WR | lia | lia | lia].
  Qed.
  Lemma KB_T : forall cells m1 R T off len, KB cells m1 R T -> (off + len <= nT)%nat ->
    limbs_at bsegs m1 (tq + 8 * Z.of_nat off) (slice T off len) /\ limbs (slice T off len) /\ length (slice T off len) = len /\
    wr_at bsegs m1 (tq + 8 * Z.of_nat off) (8 * Z.of_nat len).
  Proof using All.
    intros cells m1 R T off len (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & _) H.
    split; [apply limbs_at_slice; [exact HT | lia]|]. split; [apply slice_limbs; exact LT|]. split; [apply slice_length; lia|].
    replace (tq + 8 * Z.of_nat off) with (tq + (8 * Z.of_nat off)) by lia. eapply wr_at_sub; [exact WT | lia | lia | lia].
  Qed.
  Lemma KB_Tskip : forall cells m1 R T off, KB cells m1 R T -> (off <= nT)%nat ->
    limbs_at bsegs m1 (tq + 8 * Z.of_nat off) (skipn off T) /\ limbs (skipn off T) /\ length (skipn off T) = (nT - off)%nat /\
    wr_at bsegs m1 (tq + 8 * Z.of_nat off) (8 * Z.of_nat (nT - off)).
  Proof using All.
    intros cells m1 R T off (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & _) H.
    split; [apply limbs_at_skipn; [exact HT | lia]|]. split; [apply limbs_skipn; exact LT|]. split; [rewrite length_skipn; lia|].
    replace (tq + 8 * Z.of_nat off) with (tq + (8 * Z.of_nat off)) by lia. eapply wr_at_sub; [exact WT | lia | lia | lia].
  Qed.
  Lemma KB_a : forall cells m1 R T off len, KB cells m1 R T -> (off + len <= length a)%nat ->
    limbs_at bsegs m1 (ap + 8 * Z.of_nat off) (slice a off len).
  Proof using All. intros cells m1 R T off len (_ & _ & _ & _ & _ & _ & HA & _) H. apply limbs_at_slice; [exact HA | lia]. Qed.
  Lemma KB_b : forall cells m1 R T off len, KB cells m1 R T -> (off + len <= length b)%nat ->
    limbs_at bsegs m1 (bp + 8 * Z.of_nat off) (slice b off len).
  Proof using All. intros cells m1 R T off len (_ & _ & _ & _ & _ & _ & _ & HB & _) H. apply limbs_at_slice; [exact HB | lia]. Qed.
  Lemma KB_stk : forall cells m1 R T, KB cells m1 R T -> stk bsegs m1 lo FB /\ mem_inv bsegs m1.
  Proof using All. intros cells m1 R T (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ST & MI & _). split; assumption. Qed.
  Lemma KB_len : forall cells m1 R T, KB cells m1 R T -> limbs R /\ limbs T /\ length R = nR /\ length T = nT.
  Proof using All. intros cells m1 R T (LR & LT & ER & ET & _). repeat split; assumption. Qed.
  Lemma KB_bounds : forall cells m1 R T, KB cells m1 R T -> (0 < nR)%nat -> (0 < nT)%nat ->
    0 <= rp /\ rp + 8 * Z.of_nat nR <= 140737488355328 /\ 0 <= tq /\ tq + 8 * Z.of_nat nT <= 140737488355328 /\
    0 <= ap /\ ap + 8 * Z.of_nat (length a) <= 18446744073709551616 /\ 0 <= bp /\ bp + 8 * Z.of_nat (length b) <= 18446744073709551616.
  Proof using All.
    intros cells m1 R T (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & _) HnR HnT.
    pose proof (limbs_at_bound _ _ _ _ HA) as BA. pose proof (limbs_at_bound _ _ _ _ HB) as BB.
    pose proof (wr_at_below bsegs m1 rp _ MI WR ltac:(lia)) as BR. pose proof (wr_at_below bsegs m1 tq _ MI WT ltac:(lia)) as BT.
    destruct WR as (W0 & W1 & _). destruct WT as (W2 & W3 & _).
    change (2 ^ 64) with 18446744073709551616 in *. unfold UTOP in *. clear - BA BB BR BT W0 W1 W2 W3. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma KB_bounds_ab : forall cells m1 R T, KB cells m1 R T -> (0 < length a)%nat -> (0 < length b)%nat ->
    ap + 8 * Z.of_nat (length a) <= 140737488355328 /\ bp + 8 * Z.of_nat (length b) <= 140737488355328.
  Proof using All.
    intros cells m1 R T (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & _) Ha Hb.
    assert (Na : lbytes a <> []) by (intros E; apply (f_equal (@length byte)) in E; rewrite lbytes_length in E; cbn in E; lia).
    assert (Nb : lbytes b <> []) by (intros E; apply (f_equal (@length byte)) in E; rewrite lbytes_length in E; cbn in E; lia).
    pose proof (bytes_at_below bsegs m1 ap _ MI HA Na) as BA. pose proof (bytes_at_below bsegs m1 bp _ MI HB Nb) as BB.
    rewrite lbytes_lengthZ in BA, BB. unfold UTOP in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma KB_heap : forall cells m1 R T, KB cells m1 R T -> AHEAP Σ OW LB m1.
  Proof using All. intros cells m1 R T (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEAP & _). exact HEAP. Qed.
  Lemma KB_shb : forall cells m1 R T, KB cells m1 R T -> shb_cells bsegs 6163672 6961656 m1.
  Proof using All. intros cells m1 R T I. exact (AH_shb _ _ _ _ (KB_heap _ _ _ _ I)). Qed.
  Lemma KB_accR : forall cells m1 R T off len, KB cells m1 R T -> (off + len <= nR)%nat -> acc bsegs m1 (rp + 8 * Z.of_nat off) (8 * Z.of_nat len).
  Proof using All.
    intros cells m1 R T off len I H. eapply (AH_acc_in _ _ _ _ bR); [exact (KB_heap _ _ _ _ I) | apply in_or_app; left; exact INR | lia | lia].
  Qed.
  Lemma KB_accT : forall cells m1 R T off len, KB cells m1 R T -> (off + len <= nT)%nat -> acc bsegs m1 (tq + 8 * Z.of_nat off) (8 * Z.of_nat len).
  Proof using All.
    intros cells m1 R T off len I H. eapply (AH_acc_in _ _ _ _ bT); [exact (KB_heap _ _ _ _ I) | apply in_or_app; left; exact INT | lia | lia].
  Qed.
  Lemma KB_acca : forall cells m1 R T off len, KB cells m1 R T -> (off + len <= length a)%nat -> acc bsegs m1 (ap + 8 * Z.of_nat off) (8 * Z.of_nat len).
  Proof using All. intros cells m1 R T off len I H. eapply (AH_acc_in _ _ _ _ bA); [exact (KB_heap _ _ _ _ I) | exact INA | lia | lia]. Qed.
  Lemma KB_accb : forall cells m1 R T off len, KB cells m1 R T -> (off + len <= length b)%nat -> acc bsegs m1 (bp + 8 * Z.of_nat off) (8 * Z.of_nat len).
  Proof using All. intros cells m1 R T off len I H. eapply (AH_acc_in _ _ _ _ bB); [exact (KB_heap _ _ _ _ I) | exact INB | lia | lia]. Qed.
  (* [comment removed for export] *)
  Lemma KB_offR : forall cells m1 R T, KB cells m1 R T ->
    (rp + 8 * Z.of_nat nR <= SHLO \/ SHHI <= rp) /\ (rp + 8 * Z.of_nat nR <= 65536 \/ 12570624 <= rp).
  Proof using All.
    intros cells m1 R T I. pose proof (KB_heap _ _ _ _ I) as HEAP. assert (Hb : In bR (OW ++ LB)) by (apply in_or_app; left; exact INR).
    pose proof (AH_offsh _ _ _ _ bR HEAP Hb) as O. pose proof (AH_range_gen _ _ _ _ bR HEAP Hb) as (_ & _ & _ & _ & G). lia.
  Qed.
  Lemma KB_offT : forall cells m1 R T, KB cells m1 R T ->
    (tq + 8 * Z.of_nat nT <= SHLO \/ SHHI <= tq) /\ (tq + 8 * Z.of_nat nT <= 65536 \/ 12570624 <= tq).
  Proof using All.
    intros cells m1 R T I. pose proof (KB_heap _ _ _ _ I) as HEAP. assert (Hb : In bT (OW ++ LB)) by (apply in_or_app; left; exact INT).
    pose proof (AH_offsh _ _ _ _ bT HEAP Hb) as O. pose proof (AH_range_gen _ _ _ _ bT HEAP Hb) as (_ & _ & _ & _ & G). lia.
  Qed.
  (* [comment removed for export] *)
  Lemma KB_accRz : forall cells m1 R T p l, KB cells m1 R T -> rp <= p /\ p + l <= rp + 8 * Z.of_nat nR -> acc bsegs m1 p l.
  Proof using All.
    intros cells m1 R T p l I H. eapply (AH_acc_in _ _ _ _ bR); [exact (KB_heap _ _ _ _ I) | apply in_or_app; left; exact INR | lia | lia].
  Qed.
  Lemma KB_accTz : forall cells m1 R T p l, KB cells m1 R T -> tq <= p /\ p + l <= tq + 8 * Z.of_nat nT -> acc bsegs m1 p l.
  Proof using All.
    intros cells m1 R T p l I H. eapply (AH_acc_in _ _ _ _ bT); [exact (KB_heap _ _ _ _ I) | apply in_or_app; left; exact INT | lia | lia].
  Qed.
  Lemma KB_accaz : forall cells m1 R T p l, KB cells m1 R T -> ap <= p /\ p + l <= ap + 8 * Z.of_nat (length a) -> acc bsegs m1 p l.
  Proof using All. intros cells m1 R T p l I H. eapply (AH_acc_in _ _ _ _ bA); [exact (KB_heap _ _ _ _ I) | exact INA | lia | lia]. Qed.
  Lemma KB_accbz : forall cells m1 R T p l, KB cells m1 R T -> bp <= p /\ p + l <= bp + 8 * Z.of_nat (length b) -> acc bsegs m1 p l.
  Proof using All. intros cells m1 R T p l I H. eapply (AH_acc_in _ _ _ _ bB); [exact (KB_heap _ _ _ _ I) | exact INB | lia | lia]. Qed.
  Lemma KB_shhi : forall cells m1 R T, KB cells m1 R T -> SHHI <= lo.
  Proof using All. intros cells m1 R T I. pose proof (AH_ceil _ _ _ _ (KB_heap _ _ _ _ I)) as (_ & C & _). lia. Qed.
  (* [comment removed for export] *)
  Lemma KB_aptR : forall cells m1 R T p q r l, KB cells m1 R T -> p mod 8 = 0 -> q mod 8 = 0 -> r mod 8 = 0 ->
    rp <= p /\ p + 8 * l <= rp + 8 * Z.of_nat nR -> aptrs3 p q r l lo.
  Proof using All.
    intros cells m1 R T p q r l I Hp Hq Hr H. pose proof (KB_offR _ _ _ _ I) as (O & _). pose proof (KB_shhi _ _ _ _ I) as C.
    unfold aptrs3. split; [exact Hp|]. split; [exact Hq|]. split; [exact Hr|]. split; [lia | exact C].
  Qed.
  Lemma KB_aptT : forall cells m1 R T p q r l, KB cells m1 R T -> p mod 8 = 0 -> q mod 8 = 0 -> r mod 8 = 0 ->
    tq <= p /\ p + 8 * l <= tq + 8 * Z.of_nat nT -> aptrs3 p q r l lo.
  Proof using All.
    intros cells m1 R T p q r l I Hp Hq Hr H. pose proof (KB_offT _ _ _ _ I) as (O & _). pose proof (KB_shhi _ _ _ _ I) as C.
    unfold aptrs3. split; [exact Hp|]. split; [exact Hq|]. split; [exact Hr|]. split; [lia | exact C].
  Qed.
  (* [comment removed for export] *)
  Lemma KB_offiR : forall cells m1 R T p l, KB cells m1 R T -> rp <= p /\ p + l <= rp + 8 * Z.of_nat nR -> p + l <= 65536 \/ 12570624 <= p.
  Proof using All. intros cells m1 R T p l I H. pose proof (KB_offR _ _ _ _ I) as (_ & O). lia. Qed.
  Lemma KB_offiT : forall cells m1 R T p l, KB cells m1 R T -> tq <= p /\ p + l <= tq + 8 * Z.of_nat nT -> p + l <= 65536 \/ 12570624 <= p.
  Proof using All. intros cells m1 R T p l I H. pose proof (KB_offT _ _ _ _ I) as (_ & O). lia. Qed.
  (* [comment removed for export] *)
  Lemma KB_pos : forall cells m1 R T, KB cells m1 R T -> 0 < rp /\ 0 < tq /\ 0 < ap /\ 0 < bp.
  Proof using All.
    intros cells m1 R T I. pose proof (KB_heap _ _ _ _ I) as H.
    pose proof (AH_range_gen _ _ _ _ bR H (in_or_app _ _ _ (or_introl INR))) as (P1 & _).
    pose proof (AH_range_gen _ _ _ _ bT H (in_or_app _ _ _ (or_introl INT))) as (P2 & _).
    pose proof (AH_range_gen _ _ _ _ bA H INA) as (P3 & _).
    pose proof (AH_range_gen _ _ _ _ bB H INB) as (P4 & _).
    lia.
  Qed.
End Bundle.

Lemma mod8_add8 : forall p k, p mod 8 = 0 -> (p + 8 * k) mod 8 = 0.
Proof. intros p k H. Z.div_mod_to_equations. lia. Qed.
