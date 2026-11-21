(** * Bridge.Infl.IArmLenDec — pair I10 (helper pci-len): the two-level decode of LEN and
    DIST, as one S5 statement sequence against RT's [inf_decode].

    [dseq p root k REST] is S5's [DECODE1], then [DECODE2] + [DROPBITS] + [add_back] of the
    root entry when it is a link ([tsub k]), then [DROPBITS] + [add_back] of the entry, then
    [REST entry].  LEN ([InflateArms.v:249-261]) and DIST ([:213-223]) are both this
    sequence followed by their own tail.  [dseq_sim] carries [icb] (= [icore] + the two
    tables) to RT's post-decode state and returns the entry facts the tails need. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateFast InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits IArmLitKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Definition dseq (p : IS.codeptr) (root : Z) (k : tkind) (REST : Z -> IS.AM unit) : IS.AM unit :=
  IS.abind (IA.DECODE1 p root) (fun here =>
  IS.abind (if tsub k (IS.code_op here) then
              IS.abind (IA.DECODE2 p here) (fun here2 =>
              IS.abind (IA.DROPBITS (IS.code_bits here)) (fun _ =>
              IS.abind (IA.add_back IS.ivar_ref (IS.code_bits here)) (fun _ =>
              IS.aret here2)))
            else IS.aret here) (fun here =>
  IS.abind (IA.DROPBITS (IS.code_bits here)) (fun _ =>
  IS.abind (IA.add_back IS.ivar_ref (IS.code_bits here)) (fun _ =>
  REST here)))).

Lemma abind_assoc : forall {A B C} (m : IS.AM A) (f : A -> IS.AM B) (g : B -> IS.AM C) w,
  IS.abind (IS.abind m f) g w = IS.abind m (fun x => IS.abind (f x) g) w.
Proof. intros. unfold IS.abind. destruct (m w); reflexivity. Qed.

Lemma abind_aret : forall {A B} (a : A) (f : A -> IS.AM B) w, IS.abind (IS.aret a) f w = f a w.
Proof. reflexivity. Qed.

Lemma add_back_eq : forall v w,
  IA.add_back IS.ivar_ref v w
  = IS.ARun tt (IS.wset_s w (IS.iset_back (IS.w_s w) (swrap32 (IS.is_back (IS.w_s w) + v)))).
Proof. reflexivity. Qed.

Ltac astep E := rewrite (abind_ARun _ _ _ _ _ E); cbv beta.
Ltac astep_back := erewrite (abind_ARun _ _ _ _ _ (add_back_eq _ _)); cbv beta.

Lemma dseq_sim : forall k p root g REST W0 Q0 h b' nb,
  icb W0 Q0 ->
  tview (IS.code_at (IS.w_s W0) p) g root k ->
  RI.inf_decode (fun h => tsub k (RBa.c_op h)) g root (RI.q_br Q0) = RI.DecOk h b' nb ->
  exists W', dseq p root k REST W0 = REST (RBa.code_enc h) W'
    /\ icb W' (RI.qset_br (RI.qset_st Q0 (RI.set_back (RI.q_st Q0)
                                          (RI.u_back (RI.s_cur (RI.q_st Q0)) + nb))) b')
    /\ code_rng h /\ tent k (RBa.code_enc h) /\ tsub k (RBa.c_op h) = false.
Proof.
  intros k p root g REST W0 Q0 h b' nb Hb Htv Hd.
  pose proof (icb_brel _ _ Hb) as Hbr.
  pose proof Htv as [Hroot Htv'].
  unfold RI.inf_decode in Hd.
  destruct (RI.inf_fetch g root (RI.q_br Q0)) as [h0 b0| |] eqn:Ef; try discriminate.
  destruct (decode1_sim W0 (RI.q_br Q0) b0 p g root k h0 Hbr Htv Ef)
    as (E1 & Hb0 & Hin0 & Hsum0 & (x & Hx & _ & Eh0) & Hc0).
  subst h0.
  destruct (Htv' x Hx) as (Efx & Hrx & _ & Htx & Hsx).
  pose proof Hrx as (Hop & Hbits & Hval).
  pose proof (fetch_bnx _ _ _ _ _ Ef) as (Hbn0 & _).
  assert (Hcb0 : icb (wbr W0 b0) (RI.qset_br Q0 b0))
    by (apply B_br; [exact Hb | exact Hb0 | exact Hin0 | exact Hsum0 | lia]).
  unfold dseq. astep E1.
  rewrite (enc_op _ Hrx).
  destruct (tsub k (RBa.c_op (g x))) eqn:Es.
  - (* the root entry is a link: second level *)
    destruct (RI.inf_fetch2 g (g x) b0) as [h1 b1| |] eqn:Ef2; try discriminate.
    cbv zeta in Hd. injection Hd as <- <- <-.
    assert (Htv0 : tview (IS.code_at (IS.w_s (wbr W0 b0)) p) g root k) by (rewrite wbr_s; exact Htv).
    destruct (decode2_sim (wbr W0 b0) b0 b1 p g root k x h1 Hb0 Htv0 Hx Es Hc0 Ef2)
      as (E2 & Hb1 & Hin1 & Hsum1 & (y & Hy & Eh1) & Hc1).
    rewrite wbr_wbr in E2, Hb1.
    pose proof (fetch2_bnx _ _ _ _ _ Ef2) as (Hbn1 & _).
    (* the sub-table entry *)
    rewrite Efx, (enc_op _ Hrx), (enc_val _ Hrx) in Hsx.
    destruct (Hsx Es) as (_ & _ & _ & Hz).
    destruct (Hz y Hy) as (Efz & Hrz & _ & Hsz & Htz).
    cbv zeta in Efz, Hrz, Hsz, Htz. rewrite <- Eh1 in Efz, Hrz.
    rewrite Efz in Hsz, Htz. rewrite (enc_op _ Hrz) in Hsz.
    pose proof Hrz as (Hop1 & Hbits1 & Hval1).
    cbv beta iota.
    rewrite abind_assoc. astep E2.
    rewrite (enc_bits _ Hrx).
    (* drop the root entry's bits *)
    assert (Hcb1 : icb (wbr W0 b1) (RI.qset_br (RI.qset_br Q0 b0) b1)).
    { pose proof (B_br _ _ b1 Hcb0) as HH. rewrite wbr_wbr in HH. apply HH; clear HH.
      - exact Hb1.
      - rewrite Hin1. reflexivity.
      - cbn [RI.q_br RI.qset_br]. lia.
      - cbn [RI.q_br RI.qset_br]. lia. }
    destruct (dropbits_sim (wbr W0 b1) b1 (RBa.c_bits (g x)) Hb1 ltac:(lia)) as (E3 & Hb2).
    rewrite wbr_wbr in E3, Hb2.
    set (b2 := RB.br_dropbits (RBa.c_bits (g x)) b1) in *.
    assert (Hcb2 : icb (wbr W0 b2) (RI.qset_br (RI.qset_br (RI.qset_br Q0 b0) b1) b2)).
    { pose proof (B_br _ _ b2 Hcb1) as HH. rewrite wbr_wbr in HH. apply HH; clear HH.
      - exact Hb2.
      - reflexivity.
      - reflexivity.
      - unfold b2. rewrite drop_bnx. cbn [RI.q_br RI.qset_br]. lia. }
    rewrite abind_assoc. astep E3.
    rewrite abind_assoc. astep_back.
    rewrite abind_aret. cbv beta.
    pose proof (B_addback _ _ (RBa.c_bits (g x)) Hcb2) as Hcb3.
    match type of Hcb3 with icb ?W ?Q => set (W3 := W) in *; set (Q3 := Q) in * end.
    rewrite (enc_bits _ Hrz).
    (* drop the sub-table entry's bits *)
    assert (Hd4 : 0 <= RBa.c_bits h1 <= RB.br_bits b2) by (unfold b2; cbn [RB.br_dropbits RB.br_bits]; lia).
    destruct (dropbits_sim W3 b2 (RBa.c_bits h1) (icb_brel _ _ Hcb3) Hd4) as (E4 & Hb4).
    astep E4.
    assert (Hcb4 : icb (wbr W3 (RB.br_dropbits (RBa.c_bits h1) b2))
                       (RI.qset_br Q3 (RB.br_dropbits (RBa.c_bits h1) b2))).
    { apply B_br; [exact Hcb3 | exact Hb4 | reflexivity | reflexivity |].
      rewrite drop_bnx. change (RI.q_br Q3) with b2. lia. }
    astep_back.
    eexists. split; [reflexivity|].
    split; [|split; [exact Hrz | split; [exact Htz | exact Hsz]]].
    rewrite Z.add_assoc.
    exact (B_addback _ _ (RBa.c_bits h1) Hcb4).
  - (* the root entry is the entry *)
    injection Hd as <- <- <-.
    cbv beta iota. rewrite abind_aret. cbv beta.
    rewrite (enc_bits _ Hrx).
    destruct (dropbits_sim (wbr W0 b0) b0 (RBa.c_bits (g x)) Hb0 ltac:(lia)) as (E3 & Hb2).
    rewrite wbr_wbr in E3, Hb2.
    astep E3.
    assert (Hcb2 : icb (wbr W0 (RB.br_dropbits (RBa.c_bits (g x)) b0))
                       (RI.qset_br (RI.qset_br Q0 b0) (RB.br_dropbits (RBa.c_bits (g x)) b0))).
    { pose proof (B_br _ _ (RB.br_dropbits (RBa.c_bits (g x)) b0) Hcb0) as HH. rewrite wbr_wbr in HH.
      apply HH; clear HH.
      - exact Hb2.
      - reflexivity.
      - reflexivity.
      - rewrite drop_bnx. cbn [RI.q_br RI.qset_br]. lia. }
    astep_back.
    eexists. split; [reflexivity|].
    split; [|split; [exact Hrx | split; [rewrite <- Efx; exact Htx | exact Es]]].
    exact (B_addback _ _ (RBa.c_bits (g x)) Hcb2).
Qed.
