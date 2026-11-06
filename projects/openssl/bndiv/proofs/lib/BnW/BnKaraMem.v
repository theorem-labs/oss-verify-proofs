(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.bndiv.lib.Lib Require Import Tac Arr.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase.
From OSSVerify.Proofs.openssl.bndiv.lib.BnW Require Import BnMem BnTacX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma splice_nil : forall l off, (off <= length l)%nat -> splice l off [] = l.
Proof. intros l off H. unfold splice. cbn [app length]. rewrite Nat.add_0_r. apply firstn_skipn. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma limbs_at_slice : forall m A L off len, limbs_at segs m A L -> (off + len <= length L)%nat ->
  limbs_at segs m (A + 8 * Z.of_nat off) (slice L off len).
Proof.
  intros m A L off len H Hl. unfold slice.
  rewrite <- (firstn_skipn off L) in H. apply limbs_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn len (skipn off L)) in H. apply limbs_at_app in H. exact (proj1 H).
Qed.

Lemma limbs_at_firstn : forall m A L len, limbs_at segs m A L -> limbs_at segs m A (firstn len L).
Proof. intros m A L len H. rewrite <- (firstn_skipn len L) in H. apply limbs_at_app in H. exact (proj1 H). Qed.

Lemma limbs_at_skipn : forall m A L off, limbs_at segs m A L -> (off <= length L)%nat ->
  limbs_at segs m (A + 8 * Z.of_nat off) (skipn off L).
Proof.
  intros m A L off H Hl. rewrite <- (firstn_skipn off L) in H. apply limbs_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Lemma limbs_at_splice : forall W m1 m2 A L off seg,
  limbs_at segs m1 A L -> munch W m1 m2 -> (off + length seg <= length L)%nat ->
  limbs_at segs m2 (A + 8 * Z.of_nat off) seg ->
  disjoint_from W A (8 * Z.of_nat off) ->
  disjoint_from W (A + 8 * Z.of_nat (off + length seg)) (8 * Z.of_nat (length L - (off + length seg))) ->
  limbs_at segs m2 A (splice L off seg).
Proof.
  intros W m1 m2 A L off seg H MU Hl HS D1 D2. unfold splice.
  pose proof (limbs_at_firstn m1 A L off H) as H1.
  pose proof (limbs_at_skipn m1 A L (off + length seg) H ltac:(lia)) as H3.
  apply limbs_at_app. split.
  - eapply limbs_at_transport; [exact H1 | exact MU |]. rewrite length_firstn, Nat.min_l by lia. exact D1.
  - rewrite length_firstn, Nat.min_l by lia. apply limbs_at_app. split; [exact HS|].
    replace (A + 8 * Z.of_nat off + 8 * Z.of_nat (length seg)) with (A + 8 * Z.of_nat (off + length seg)) by lia.
    eapply limbs_at_transport; [exact H3 | exact MU |]. rewrite length_skipn. exact D2.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_forget_C8 : forall m A pre w post,
  rw_cells segs m A (pre ++ C8 w :: post) -> rw_cells segs m A (pre ++ CB 8 (le8 w) :: post).
Proof.
  intros m A pre w post [[Hwf Hb] Hw]. split; [split|].
  - apply cells_wf_app in Hwf. destruct Hwf as [H1 H2]. apply cells_wf_app. split; [exact H1|].
    destruct H2 as [_ H2]. split; [exact (length_le8 w) | exact H2].
  - rewrite !cells_bytes_app in *. cbn [cells_bytes cbytes] in *. exact Hb.
  - rewrite !cells_size_app in *. cbn [cells_size csize] in *. exact Hw.
Qed.

Section Bundle.
  Variables (m : word -> option byte) (rp tq ap bp SP lo : Z) (a b : list Z) (nR nT : nat) (FS SK FB : Z).
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

  Definition KWfin : list ivl := [(rp, rp + 8 * Z.of_nat nR); (tq, tq + 8 * Z.of_nat nT); (SP - FS - SK, SP)].
  (* [comment removed for export] *)
  Definition KW (offR lenR offT lenT : nat) : list ivl :=
    [(rp + 8 * Z.of_nat offR, rp + 8 * Z.of_nat offR + 8 * Z.of_nat lenR);
     (tq + 8 * Z.of_nat offT, tq + 8 * Z.of_nat offT + 8 * Z.of_nat lenT);
     (FB - SK, FB)].

  Definition KB (cells : list cell) (m1 : word -> option byte) (R T : list Z) : Prop :=
    limbs R /\ limbs T /\ length R = nR /\ length T = nT /\
    limbs_at segs m1 rp R /\ limbs_at segs m1 tq T /\ limbs_at segs m1 ap a /\ limbs_at segs m1 bp b /\
    wr_at segs m1 rp (8 * Z.of_nat nR) /\ wr_at segs m1 tq (8 * Z.of_nat nT) /\
    rw_cells segs m1 FB cells /\ stk segs m1 lo FB /\ mem_inv segs m1 /\
    munch KWfin m m1 /\ wmono segs m m1.

  Lemma KB_upd : forall cells m1 m2 R T offR segR offT segT,
    Z.of_nat (cells_size cells) = FS ->
    KB cells m1 R T ->
    munch (KW offR (length segR) offT (length segT)) m1 m2 -> wmono segs m1 m2 -> mem_inv segs m2 -> stk segs m2 lo FB ->
    limbs segR -> limbs segT -> (offR + length segR <= nR)%nat -> (offT + length segT <= nT)%nat ->
    limbs_at segs m2 (rp + 8 * Z.of_nat offR) segR -> limbs_at segs m2 (tq + 8 * Z.of_nat offT) segT ->
    KB cells m2 (splice R offR segR) (splice T offT segT).
  Proof using FS0 FBE SK0 DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB.
    intros cells m1 m2 R T offR segR offT segT CS (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM)
           MUc WMc MIc STc LsR LsT HoR HoT HsR HsT.
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
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
             unfold sub_fp, KW, KWfin. cbn [outside]. intros x Hx. clear - Hx HoR HoT FS0 SK0 FBE. lia. }
    eapply wmono_trans; [exact WM | exact WMc].
  Qed.

  (* [comment removed for export] *)
  Lemma KB_after_R : forall cells m1 m2 R T off seg len8 fsz,
    Z.of_nat (cells_size cells) = FS -> KB cells m1 R T ->
    munch [(rp + 8 * Z.of_nat off, rp + 8 * Z.of_nat off + len8); (FB - fsz, FB)] m1 m2 ->
    len8 = 8 * Z.of_nat (length seg) -> 0 <= fsz <= SK ->
    wmono segs m1 m2 -> mem_inv segs m2 -> limbs_at segs m2 (rp + 8 * Z.of_nat off) seg -> stk segs m2 lo FB ->
    limbs seg -> (off + length seg <= nR)%nat ->
    KB cells m2 (splice R off seg) T.
  Proof using FS0 FBE SK0 DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB.
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
    wmono segs m1 m2 -> mem_inv segs m2 -> limbs_at segs m2 (tq + 8 * Z.of_nat off) seg -> stk segs m2 lo FB ->
    limbs seg -> (off + length seg <= nT)%nat ->
    KB cells m2 R (splice T off seg).
  Proof using FS0 FBE SK0 DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB.
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
    wmono segs m1 m2 -> mem_inv segs m2 -> stk segs m2 lo FB ->
    KB cells m2 R T.
  Proof using FS0 FBE SK0 DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB.
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
    wmono segs m1 m2 -> mem_inv segs m2 ->
    limbs_at segs m2 (rp + 8 * Z.of_nat offR) segR -> limbs_at segs m2 (tq + 8 * Z.of_nat offT) segT -> stk segs m2 lo FB ->
    limbs segR -> limbs segT -> (offR + length segR <= nR)%nat -> (offT + length segT <= nT)%nat ->
    KB cells m2 (splice R offR segR) (splice T offT segT).
  Proof using FS0 FBE SK0 DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB.
    intros cells m1 m2 R T offR segR offT segT lenR8 lenT8 fsz CS I MUc ER8 ET8 Hf WMc MIc HSR HST STc LSR LST HoR HoT.
    eapply KB_upd with (m1 := m1); try eassumption.
    eapply munch_weaken; [|exact MUc]. unfold sub_fp, KW. cbn [outside length]. intros x Hx. clear - Hx ER8 ET8 Hf. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma KB_after_TT : forall cells m1 m2 R T off off2 seg1 seg2 len18 len28 fsz,
    Z.of_nat (cells_size cells) = FS -> KB cells m1 R T ->
    munch [(tq + 8 * Z.of_nat off, tq + 8 * Z.of_nat off + len18); (tq + 8 * Z.of_nat off2, tq + 8 * Z.of_nat off2 + len28); (FB - fsz, FB)] m1 m2 ->
    len18 = 8 * Z.of_nat (length seg1) -> len28 = 8 * Z.of_nat (length seg2) -> off2 = (off + length seg1)%nat -> 0 <= fsz <= SK ->
    wmono segs m1 m2 -> mem_inv segs m2 ->
    limbs_at segs m2 (tq + 8 * Z.of_nat off) seg1 -> limbs_at segs m2 (tq + 8 * Z.of_nat off2) seg2 -> stk segs m2 lo FB ->
    limbs seg1 -> limbs seg2 -> (off2 + length seg2 <= nT)%nat ->
    KB cells m2 R (splice T off (seg1 ++ seg2)).
  Proof using FS0 FBE SK0 DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB.
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
  Lemma KB_frame : forall cells cells' m1 m2 R T,
    KB cells m1 R T ->
    munch [(FB, FB + FS)] m1 m2 -> wmono segs m1 m2 -> mem_inv segs m2 -> stk segs m2 lo FB ->
    rw_cells segs m2 FB cells' ->
    KB cells' m2 R T.
  Proof using FS0 FBE SK0 SEPR SEPT SEPA SEPB.
    intros cells cells' m1 m2 R T (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM) MUc WMc MIc STc FR'.
    unfold KB.
    split; [exact LR|]. split; [exact LT|]. split; [exact ER|]. split; [exact ET|].
    split. { eapply limbs_at_transport; [exact HR | exact MUc |]. cbn [disjoint_from]. rewrite ER. clear - SEPR FS0 SK0 FBE. lia. }
    split. { eapply limbs_at_transport; [exact HT | exact MUc |]. cbn [disjoint_from]. rewrite ET. clear - SEPT FS0 SK0 FBE. lia. }
    split. { eapply limbs_at_transport; [exact HA | exact MUc |]. cbn [disjoint_from]. clear - SEPA FS0 SK0 FBE. lia. }
    split. { eapply limbs_at_transport; [exact HB | exact MUc |]. cbn [disjoint_from]. clear - SEPB FS0 SK0 FBE. lia. }
    split. { eapply wr_at_transport; [exact WR | exact WMc]. }
    split. { eapply wr_at_transport; [exact WT | exact WMc]. }
    split; [exact FR'|]. split; [exact STc|]. split; [exact MIc|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MUc].
             unfold sub_fp, KWfin. cbn [outside]. intros x Hx. clear - Hx FS0 SK0 FBE. lia. }
    eapply wmono_trans; [exact WM | exact WMc].
  Qed.

  (* [comment removed for export] *)
  Lemma KB_storeR : forall cells m1 R T (i : nat) v,
    Z.of_nat (cells_size cells) = FS ->
    KB cells m1 R T -> (i < nR)%nat -> limb v ->
    store_ok segs m1 (wa (rp + 8 * Z.of_nat i)) 8 = true /\
    KB cells (write_to_mem m1 (wa (rp + 8 * Z.of_nat i)) (le8 (Z_to_bv 64 v))) (upd R i v) T.
  Proof using FS0 FBE SK0 DRA DRB DRT SEPR.
    pose proof (hide_intro _ DRA) as hDRA. pose proof (hide_intro _ DRB) as hDRB. pose proof (hide_intro _ DRT) as hDRT.
    pose proof (hide_intro _ SEPR) as hSEPR. clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB.
    intros cells m1 R T i v CS (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & MU & WM) Hi Hv.
    pose proof (limbs_at_bound _ _ _ _ HA) as BA. pose proof (limbs_at_bound _ _ _ _ HB) as BB.
    pose proof (limbs_at_bound _ _ _ _ HT) as BT. pose proof (limbs_at_bound _ _ _ _ HR) as BR.
    pose proof (rw_cells_bound _ _ _ _ FR) as BF. rewrite CS in BF.
    rewrite ER in BR. rewrite ET in BT. change (2 ^ 64) with 18446744073709551616 in *.
    assert (L8 : length (le8 (Z_to_bv 64 v)) = 8%nat) by apply length_le8.
    assert (SOK : store_ok segs m1 (wa (rp + 8 * Z.of_nat i)) 8 = true).
    { apply (wr_at_store_ok segs m1 rp (8 * Z.of_nat nR)); [exact WR | lia | lia]. }
    split; [exact SOK|]. unfold KB.
    split; [apply upd_limbs; assumption|]. split; [exact LT|].
    split; [rewrite upd_length; lia|]. split; [exact ET|].
    split.
    { unfold upd, splice. cbn [length].
      pose proof (limbs_at_firstn m1 rp R i HR) as H1.
      pose proof (limbs_at_skipn m1 rp R (i + 1) HR ltac:(lia)) as H3.
      apply limbs_at_app. split.
      - apply limbs_at_write_other; [exact H1 | lia | rewrite L8; lia | rewrite L8, length_firstn, Nat.min_l by lia; left; lia].
      - rewrite length_firstn, Nat.min_l by lia. apply limbs_at_app. split.
        + unfold limbs_at. rewrite lbytes_cons, lbytes_nil, app_nil_r. apply bytes_at_write_same; [lia | rewrite L8; lia].
        + cbn [length]. replace (rp + 8 * Z.of_nat i + 8 * Z.of_nat 1) with (rp + 8 * Z.of_nat (i + 1)) by lia.
          apply limbs_at_write_other; [exact H3 | lia | rewrite L8; lia | rewrite L8; right; lia]. }
    split. { apply limbs_at_write_other; [exact HT | lia | rewrite L8; lia | rewrite L8, ET; apply hide_elim in hDRT; clear - hDRT Hi; lia]. }
    split. { apply limbs_at_write_other; [exact HA | lia | rewrite L8; lia | rewrite L8; apply hide_elim in hDRA; clear - hDRA Hi; lia]. }
    split. { apply limbs_at_write_other; [exact HB | lia | rewrite L8; lia | rewrite L8; apply hide_elim in hDRB; clear - hDRB Hi; lia]. }
    split; [apply wr_at_write; exact WR|]. split; [apply wr_at_write; exact WT|].
    split. { apply rw_cells_frame; [exact FR | lia | rewrite L8; lia | rewrite L8, CS; apply hide_elim in hSEPR; clear - hSEPR Hi FBE SK0 FS0; lia]. }
    split. { apply stk_write; [exact ST | lia | rewrite L8; lia]. }
    split. { apply mem_inv_store; [exact MI | rewrite L8; exact SOK]. }
    split. { apply munch_write; [exact MU | lia | rewrite L8; lia | rewrite L8; unfold KWfin; cbn [inside]; left; clear - Hi; lia]. }
    apply wmono_write. exact WM.
  Qed.

  (* [comment removed for export] *)
  Lemma KB_recell : forall cells cells' m1 R T, KB cells m1 R T -> rw_cells segs m1 FB cells' -> KB cells' m1 R T.
  Proof.
    clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB.
    intros cells cells' m1 R T (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & REST) FR'.
    unfold KB. repeat (split; [assumption|]). exact REST.
  Qed.

  (* [comment removed for export] *)
  Lemma KB_R : forall cells m1 R T off len, KB cells m1 R T -> (off + len <= nR)%nat ->
    limbs_at segs m1 (rp + 8 * Z.of_nat off) (slice R off len) /\ limbs (slice R off len) /\ length (slice R off len) = len /\
    wr_at segs m1 (rp + 8 * Z.of_nat off) (8 * Z.of_nat len).
  Proof.
    clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB.
    intros cells m1 R T off len (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & _) H.
    split; [apply limbs_at_slice; [exact HR | lia]|]. split; [apply slice_limbs; exact LR|]. split; [apply slice_length; lia|].
    replace (rp + 8 * Z.of_nat off) with (rp + (8 * Z.of_nat off)) by lia. eapply wr_at_sub; [exact WR | lia | lia | lia].
  Qed.
  Lemma KB_T : forall cells m1 R T off len, KB cells m1 R T -> (off + len <= nT)%nat ->
    limbs_at segs m1 (tq + 8 * Z.of_nat off) (slice T off len) /\ limbs (slice T off len) /\ length (slice T off len) = len /\
    wr_at segs m1 (tq + 8 * Z.of_nat off) (8 * Z.of_nat len).
  Proof.
    clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB.
    intros cells m1 R T off len (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & _) H.
    split; [apply limbs_at_slice; [exact HT | lia]|]. split; [apply slice_limbs; exact LT|]. split; [apply slice_length; lia|].
    replace (tq + 8 * Z.of_nat off) with (tq + (8 * Z.of_nat off)) by lia. eapply wr_at_sub; [exact WT | lia | lia | lia].
  Qed.
  Lemma KB_Tskip : forall cells m1 R T off, KB cells m1 R T -> (off <= nT)%nat ->
    limbs_at segs m1 (tq + 8 * Z.of_nat off) (skipn off T) /\ limbs (skipn off T) /\ length (skipn off T) = (nT - off)%nat /\
    wr_at segs m1 (tq + 8 * Z.of_nat off) (8 * Z.of_nat (nT - off)).
  Proof.
    clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB.
    intros cells m1 R T off (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & _) H.
    split; [apply limbs_at_skipn; [exact HT | lia]|]. split; [apply limbs_skipn; exact LT|]. split; [rewrite length_skipn; lia|].
    replace (tq + 8 * Z.of_nat off) with (tq + (8 * Z.of_nat off)) by lia. eapply wr_at_sub; [exact WT | lia | lia | lia].
  Qed.
  Lemma KB_a : forall cells m1 R T off len, KB cells m1 R T -> (off + len <= length a)%nat ->
    limbs_at segs m1 (ap + 8 * Z.of_nat off) (slice a off len).
  Proof. intros cells m1 R T off len (_ & _ & _ & _ & _ & _ & HA & _) H. apply limbs_at_slice; [exact HA | lia]. Qed.
  Lemma KB_b : forall cells m1 R T off len, KB cells m1 R T -> (off + len <= length b)%nat ->
    limbs_at segs m1 (bp + 8 * Z.of_nat off) (slice b off len).
  Proof. intros cells m1 R T off len (_ & _ & _ & _ & _ & _ & _ & HB & _) H. apply limbs_at_slice; [exact HB | lia]. Qed.
  Lemma KB_stk : forall cells m1 R T, KB cells m1 R T -> stk segs m1 lo FB /\ mem_inv segs m1.
  Proof. intros cells m1 R T (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ST & MI & _). split; assumption. Qed.
  Lemma KB_len : forall cells m1 R T, KB cells m1 R T -> limbs R /\ limbs T /\ length R = nR /\ length T = nT.
  Proof. intros cells m1 R T (LR & LT & ER & ET & _). repeat split; assumption. Qed.
  Lemma KB_bounds : forall cells m1 R T, KB cells m1 R T -> (0 < nR)%nat -> (0 < nT)%nat ->
    0 <= rp /\ rp + 8 * Z.of_nat nR <= 140737488355328 /\ 0 <= tq /\ tq + 8 * Z.of_nat nT <= 140737488355328 /\
    0 <= ap /\ ap + 8 * Z.of_nat (length a) <= 18446744073709551616 /\ 0 <= bp /\ bp + 8 * Z.of_nat (length b) <= 18446744073709551616.
  Proof.
    clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB.
    intros cells m1 R T (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & _) HnR HnT.
    pose proof (limbs_at_bound _ _ _ _ HA) as BA. pose proof (limbs_at_bound _ _ _ _ HB) as BB.
    pose proof (wr_at_below segs m1 rp _ MI WR ltac:(lia)) as BR. pose proof (wr_at_below segs m1 tq _ MI WT ltac:(lia)) as BT.
    destruct WR as (W0 & W1 & _). destruct WT as (W2 & W3 & _).
    change (2 ^ 64) with 18446744073709551616 in *. unfold UTOP in *. clear - BA BB BR BT W0 W1 W2 W3. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma KB_bounds_ab : forall cells m1 R T, KB cells m1 R T -> (0 < length a)%nat -> (0 < length b)%nat ->
    ap + 8 * Z.of_nat (length a) <= 140737488355328 /\ bp + 8 * Z.of_nat (length b) <= 140737488355328.
  Proof.
    clear DRA DRB DTA DTB DRT SEPR SEPT SEPA SEPB.
    intros cells m1 R T (LR & LT & ER & ET & HR & HT & HA & HB & WR & WT & FR & ST & MI & _) Ha Hb.
    assert (Na : lbytes a <> []) by (intros E; apply (f_equal (@length byte)) in E; rewrite lbytes_length in E; cbn in E; lia).
    assert (Nb : lbytes b <> []) by (intros E; apply (f_equal (@length byte)) in E; rewrite lbytes_length in E; cbn in E; lia).
    pose proof (bytes_at_below segs m1 ap _ MI HA Na) as BA. pose proof (bytes_at_below segs m1 bp _ MI HB Nb) as BB.
    rewrite lbytes_lengthZ in BA, BB. unfold UTOP in *. lia.
  Qed.
End Bundle.
End WithSegs.
