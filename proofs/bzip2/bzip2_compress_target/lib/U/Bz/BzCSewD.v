(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzLemmasT BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCPermF BzCPermF2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCPermM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Lemma ms_copy_bwd_S : forall f a1 ce a2 bd nblock ss j,
  ms_copy_bwd (S f) a1 ce a2 bd nblock ss j =
  (if zget ce ss <? j then
     let k := rd32 a1 j - 1 in let k := if k <? 0 then k + nblock else k in
     let c1 := rd8 a2 k in
     let '(a1, ce) := (if zget bd c1 =? 0 then (wr32 a1 (zget ce c1) k, zset ce c1 (zget ce c1 - 1)) else (a1, ce)) in
     ms_copy_bwd f a1 ce a2 bd nblock ss (j - 1)
   else (a1, ce, j)).
Proof. reflexivity. Qed.

Section CopyB.
  Variables (a2 : zarr) (nb ss : Z) (bd P0 A0 : zarr) (csA : zarr).
  Hypothesis BB : forall i, 0 <= rd8 a2 i < 256.
  Hypothesis NB : 1 <= nb <= 2097151.
  Hypothesis SS : 0 <= ss < 256.
  Hypothesis BD : zget bd ss = 0.
  Hypothesis P0X : PINV a2 nb P0.
  Hypothesis NA : NALL a2 nb ss.
  (* [comment removed for export] *)
  Variable a2r : zarr.
  Hypothesis AGR : forall k, 0 <= k < nb -> rd8 a2r k = rd8 a2 k.
  (* [comment removed for export] *)
  Hypothesis FW : FWPOST a2 nb ss bd P0 A0 csA.

  Local Notation KEY := (key a2 nb).
  Local Notation NXT := (nxt nb).
  Local Notation CLM := (ClM a2 nb).
  Local Notation PRV := (prv nb).
  Local Notation SD := (SIDE a2 nb ss).
  Local Notation cs0 := (cs0 a2 nb ss).
  Local Notation ce1 := (ce1 a2 nb ss).
  Local Notation csF := (csF a2 nb ss).
  Local Notation B0 := (B0 a2 nb ss).
  Local Notation B1 := (B1 a2 nb ss).
  Local Notation Fset := (Fset a2 nb ss).

  (* [comment removed for export] *)
  Lemma A0_frame : forall p, (forall c, 0 <= c < 256 -> zget bd c = 0 -> ~ (cs0 c <= p < csF c)) -> rd32 A0 p = rd32 P0 p.
  Proof. exact (fp_frame _ _ _ _ _ _ _ FW). Qed.

  (* [comment removed for export] *)
  Lemma A0_tail : forall p, ce1 ss <= p < B1 -> rd32 A0 p = rd32 P0 p.
  Proof.
    intros p Hp. apply A0_frame. intros c Hc Bc R. pose proof (csF_le_ce1 a2 nb ss BB NB SS NA c Hc).
    apply (tail_no_reg a2 nb ss BB NB SS c p Hc Hp). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Record BWI (a1 ce : zarr) (j : Z) : Prop := {
    bw0 : forall c, 0 <= c < 256 -> zget ce c <= ce1 c - 1 /\ (zget bd c <> 0 -> zget ce c = ce1 c - 1) /\ (zget bd c = 0 -> csF c - 1 <= zget ce c);
    bw1 : zget ce ss <= j < B1;
    bw3 : forall p, (forall c, 0 <= c < 256 -> zget bd c = 0 -> ~ (zget ce c < p < ce1 c)) -> rd32 a1 p = rd32 A0 p;
    bw4 : forall c q, 0 <= c < 256 -> zget bd c = 0 -> zget ce c < q < ce1 c ->
            (0 <= rd32 a1 q < nb /\ KEY (rd32 a1 q) = 256 * c + ss /\ SD (rd32 a1 q) = Some false) /\
            (exists p', j < p' < B1 /\ rd32 a1 p' = NXT (rd32 a1 q));
    bw5 : forall c q q', 0 <= c < 256 -> zget bd c = 0 -> zget ce c < q < ce1 c -> zget ce c < q' < ce1 c ->
            rd32 a1 q = rd32 a1 q' -> q = q';
    bw6 : forall c k p', 0 <= c < 256 -> zget bd c = 0 -> 0 <= k < nb -> KEY k = 256 * c + ss ->
            j < p' < B1 -> rd32 a1 p' = NXT k -> exists q, zget ce c < q < ce1 c /\ rd32 a1 q = k }.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bw_scan : forall a1 ce j, BWI a1 ce j -> forall p, zget ce ss < p < B1 ->
    0 <= rd32 a1 p < nb /\ rd8 a2 (rd32 a1 p) = ss /\ SD (rd32 a1 p) = Some false /\
    (ce1 ss <= p -> rd32 a1 p = rd32 P0 p) /\ (p < ce1 ss -> KEY (rd32 a1 p) = 256 * ss + ss).
  Proof.
    intros a1 ce j IV p Hp.
    destruct (Z.lt_ge_cases p (ce1 ss)) as [L|G].
    - cps_destruct (proj1 (bw4 _ _ _ IV ss p SS BD ltac:(lia))) as (R1 & R2 & R3).
      destruct (proj1 (key_chars a2 nb BB (rd32 a1 p) ss ss SS) R2) as [E1 E2].
      repeat split; try assumption; try lia.
    - assert (E : rd32 a1 p = rd32 P0 p).
      { rewrite <- (A0_tail p) by lia. apply (bw3 _ _ _ IV). intros c Hc Bc R. pose proof (proj2 (proj2 (bw0 _ _ _ IV c Hc)) Bc).
        pose proof (csF_le_ce1 a2 nb ss BB NB SS NA c Hc).
        apply (tail_no_reg a2 nb ss BB NB SS c p Hc ltac:(lia)). lia. }
      rewrite E. cps_destruct (tail_val a2 nb ss P0 BB NB SS P0X p ltac:(lia)) as (R1 & R2 & R3 & R4). repeat split; try assumption; try lia.
  Qed.

  Lemma bw_scan_inj : forall a1 ce j, BWI a1 ce j -> forall p q, zget ce ss < p < B1 -> zget ce ss < q < B1 ->
    rd32 a1 p = rd32 a1 q -> p = q.
  Proof.
    intros a1 ce j IV p q Hp Hq E.
    cps_destruct (bw_scan a1 ce j IV p Hp) as (_ & _ & _ & Sp & Fp). cps_destruct (bw_scan a1 ce j IV q Hq) as (_ & _ & _ & Sq & Fq).
    destruct (Z.lt_ge_cases p (ce1 ss)) as [Lp|Gp]; destruct (Z.lt_ge_cases q (ce1 ss)) as [Lq|Gq].
    - apply (bw5 _ _ _ IV ss); try assumption; lia.
    - exfalso. cps_destruct (tail_val a2 nb ss P0 BB NB SS P0X q ltac:(lia)) as (_ & _ & R3 & _). specialize (Fp Lp).
      destruct (proj1 (key_chars a2 nb BB (rd32 a1 p) ss ss SS) Fp) as [_ E2]. rewrite E, Sq in E2 by lia. cbv beta in R3. lia.
    - exfalso. cps_destruct (tail_val a2 nb ss P0 BB NB SS P0X p ltac:(lia)) as (_ & _ & R3 & _). specialize (Fq Lq).
      destruct (proj1 (key_chars a2 nb BB (rd32 a1 q) ss ss SS) Fq) as [_ E2]. rewrite <- E, Sp in E2 by lia. cbv beta in R3. lia.
    - apply (tail_inj a2 nb ss P0 BB NB SS P0X); try lia; (rewrite <- Sp, <- Sq by lia; exact E).
  Qed.

  (* [comment removed for export] *)
  Lemma bw_fit : forall a1 ce j, BWI a1 ce j -> forall c (k : Z), 0 <= c < 256 -> zget bd c = 0 ->
    In k (Fset c false) -> (forall q, zget ce c < q < ce1 c -> rd32 a1 q <> k) -> csF c <= zget ce c.
  Proof.
    intros a1 ce j IV c k Hc Bc Hk NEW.
    pose proof (proj1 (bw0 _ _ _ IV c Hc)) as L0.
    pose proof (region_lt a1 (zget ce c + 1) (ce1 c) (Fset c false) k (Fset_NoDup a2 nb ss c false) ltac:(lia) Hk) as RL.
    pose proof (Fset_sum a2 nb ss BB NB SS NA c Hc).
    assert (ce1 c - (zget ce c + 1) + 1 <= Z.of_nat (length (Fset c false))).
    { apply RL.
      - intros q Hq. split; [apply (in_Fset a2 nb ss NB SS); exact (proj1 (bw4 _ _ _ IV c q Hc Bc ltac:(lia)))| apply NEW; lia].
      - intros q q' Hq Hq'. apply (bw5 _ _ _ IV c); try assumption; lia. }
    unfold BzCSewC.csF. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma BWI_init : forall ce, (forall c, 0 <= c < 256 -> zget ce c = ce1 c - 1) -> BWI A0 ce (B1 - 1).
  Proof.
    intros ce H. pose proof (S1_le_B1 a2 nb ss SS). constructor.
    - intros c Hc. rewrite H by lia. pose proof (csF_le_ce1 a2 nb ss BB NB SS NA c Hc). split; [lia|]. split; [intros; reflexivity| intros; lia].
    - rewrite (H ss SS). unfold BzCSewC.ce1, BzCSewC.B1 in *. lia.
    - intros; reflexivity.
    - intros c q Hc Bc Hq. rewrite H in Hq by lia. lia.
    - intros c q q' Hc Bc Hq. rewrite H in Hq by lia. lia.
    - intros c k p' Hc Bc Hk Kk Hp'. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma BWI_step : forall a1 ce j, BWI a1 ce j -> zget ce ss < j ->
    let u := rd32 a1 j in let k := PRV u in let c1 := rd8 a2 k in
    0 <= u < nb /\ 0 <= k < nb /\ 0 <= c1 < 256 /\ KEY k = 256 * c1 + ss /\
    (zget bd c1 = 0 -> csF c1 <= zget ce c1 < ce1 c1 /\
       BWI (wr32 a1 (zget ce c1) k) (zset ce c1 (zget ce c1 - 1)) (j - 1)) /\
    (zget bd c1 <> 0 -> BWI a1 ce (j - 1)).
  Proof.
    intros a1 ce j IV LT. cbv zeta.
    pose proof (bw1 _ _ _ IV) as J.
    cps_destruct (bw_scan a1 ce j IV j ltac:(lia)) as (Ru & Bu & Su & _ & _).
    set (u := rd32 a1 j) in *.
    pose proof (prv_range nb NB u Ru) as Rk. set (k := PRV u) in *.
    pose proof (BB k) as Rc. set (c1 := rd8 a2 k) in *.
    assert (Ek : NXT k = u) by (subst k; apply nxt_prv; exact Ru).
    assert (Kk : KEY k = 256 * c1 + ss). { apply (proj2 (key_chars a2 nb BB k c1 ss SS)). split; [reflexivity| rewrite Ek; exact Bu]. }
    assert (Sk : SD k = Some false). { rewrite (SIDE_nxt a2 nb NB ss NA k Rk) by (rewrite Ek; exact Bu). rewrite Ek. exact Su. }
    split; [exact Ru|]. split; [exact Rk|]. split; [exact Rc|]. split; [exact Kk|]. split.
    - intros Bc1.
      cps_pose (bw0 _ _ _ IV c1 Rc) as (L0 & _ & LF). specialize (LF Bc1).
      set (w := zget ce c1) in *. assert (Ew : w = zget ce c1) by reflexivity.
      assert (NEW : forall q, w < q < ce1 c1 -> rd32 a1 q <> k).
      { intros q Hq E. cps_destruct (proj2 (bw4 _ _ _ IV c1 q Rc Bc1 Hq)) as (p' & Hp' & Ep').
        rewrite E, Ek in Ep'. pose proof (bw_scan_inj a1 ce j IV p' j ltac:(lia) ltac:(lia) Ep'). lia. }
      assert (FIT : csF c1 <= w).
      { apply (bw_fit a1 ce j IV c1 k Rc Bc1); [| exact NEW]. apply (in_Fset a2 nb ss NB SS). split; [exact Rk| split; [exact Kk| exact Sk]]. }
      pose proof (csF_le_ce1 a2 nb ss BB NB SS NA c1 Rc) as CF.
      split; [split; [exact FIT| lia]|].
      assert (W1 : forall p, zget ce ss < p < B1 -> p <> w).
      { intros p Hp E. subst p. destruct (Z.eq_dec c1 ss) as [E1|N1].
        - subst w. rewrite E1 in Hp. lia.
        - destruct (Z.lt_ge_cases w (ce1 ss)) as [Lw|Gw].
          + pose proof (proj2 (proj2 (bw0 _ _ _ IV ss SS)) BD). pose proof (csF_le_ce1 a2 nb ss BB NB SS NA ss SS).
            apply (reg_disjoint a2 nb ss ss c1 w ltac:(congruence)); unfold BzCSewC.cs0, BzCSewC.ce1, BzCSewC.csF in *; lia.
          + apply (tail_no_reg a2 nb ss BB NB SS c1 w Rc ltac:(lia)). unfold BzCSewC.cs0, BzCSewC.ce1, BzCSewC.csF in *. lia. }
      assert (WQ : forall c q, 0 <= c < 256 -> zget bd c = 0 -> zget ce c < q < ce1 c -> q <> w).
      { intros c q Hc Bc Hq E. subst q. destruct (Z.eq_dec c c1) as [->|NE]; [lia|].
        pose proof (proj2 (proj2 (bw0 _ _ _ IV c Hc)) Bc). pose proof (csF_le_ce1 a2 nb ss BB NB SS NA c Hc).
        apply (reg_disjoint a2 nb ss c c1 w NE); unfold BzCSewC.cs0, BzCSewC.ce1, BzCSewC.csF in *; lia. }
      assert (RD : forall p, p <> w -> rd32 (wr32 a1 w k) p = rd32 a1 p) by (intros; apply rd32_wr32_other; assumption).
      assert (RW : rd32 (wr32 a1 w k) w = k) by (apply rd32_wr32_same; lia).
      assert (CE : forall c, zget (zset ce c1 (w - 1)) c = (if c =? c1 then w - 1 else zget ce c)) by (intros; apply zget_zset).
      constructor.
      + intros c Hc. rewrite CE. destruct (Z.eqb_spec c c1) as [->|NE]; [| exact (bw0 _ _ _ IV c Hc)].
        split; [lia|]. split; [intros X; exfalso; exact (X Bc1)| intros _; lia].
      + rewrite CE. destruct (Z.eqb_spec ss c1) as [E|NE]; [subst w; rewrite <- E; lia| lia].
      + intros p Hp. rewrite RD.
        * apply (bw3 _ _ _ IV). intros c Hc Bc R. apply (Hp c Hc Bc). rewrite CE. destruct (Z.eqb_spec c c1) as [->|NE]; lia.
        * intros E. subst p. apply (Hp c1 Rc Bc1). rewrite CE, Z.eqb_refl. lia.
      + intros c q Hc Bc Hq. rewrite CE in Hq.
        destruct (Z.eqb_spec c c1) as [->|NE].
        * destruct (Z.eq_dec q w) as [->|NQ].
          -- rewrite RW. split; [split; [exact Rk| split; [exact Kk| exact Sk]]|].
             exists j. split; [lia|]. rewrite RD by (apply W1; lia). symmetry. exact Ek.
          -- assert (Hq' : w < q < ce1 c1) by lia. rewrite (RD q NQ).
             destruct (bw4 _ _ _ IV c1 q Rc Bc1 Hq') as [X (p' & Hp' & E')]. split; [exact X|].
             exists p'. split; [lia|]. rewrite RD by (apply W1; lia). exact E'.
        * rewrite (RD q (WQ c q Hc Bc Hq)).
          destruct (bw4 _ _ _ IV c q Hc Bc Hq) as [X (p' & Hp' & E')]. split; [exact X|].
          exists p'. split; [lia|]. rewrite RD by (apply W1; lia). exact E'.
      + intros c q q' Hc Bc Hq Hq' E. rewrite CE in Hq, Hq'.
        destruct (Z.eqb_spec c c1) as [->|NE].
        * destruct (Z.eq_dec q w) as [->|NQ], (Z.eq_dec q' w) as [->|NQ']; [reflexivity| | |].
          -- exfalso. rewrite RW, (RD q' NQ') in E. apply (NEW q' ltac:(lia)). symmetry. exact E.
          -- exfalso. rewrite RW, (RD q NQ) in E. apply (NEW q ltac:(lia)). exact E.
          -- rewrite (RD q NQ), (RD q' NQ') in E. apply (bw5 _ _ _ IV c1 q q' Rc Bc1 ltac:(lia) ltac:(lia) E).
        * rewrite (RD q (WQ c q Hc Bc Hq)), (RD q' (WQ c q' Hc Bc Hq')) in E. apply (bw5 _ _ _ IV c q q' Hc Bc Hq Hq' E).
      + intros c k' p' Hc Bc Hk' Kk' Hp' E'. rewrite CE. rewrite RD in E' by (apply W1; lia).
        destruct (Z.eq_dec p' j) as [->|NP].
        * assert (k' = k). { apply (nxt_inj nb k' k Hk' Rk). rewrite Ek. fold u in E'. rewrite <- E'. reflexivity. }
          subst k'. rewrite Kk in Kk'. assert (c = c1) by lia. subst c. rewrite Z.eqb_refl.
          exists w. split; [lia| exact RW].
        * cps_destruct (bw6 _ _ _ IV c k' p' Hc Bc Hk' Kk' ltac:(lia) E') as (q & Hq & Eq).
          exists q. split; [destruct (Z.eqb_spec c c1) as [->|NE]; lia|]. rewrite (RD q (WQ c q Hc Bc Hq)). exact Eq.
    - intros Bc1. constructor.
      + exact (bw0 _ _ _ IV).
      + lia.
      + exact (bw3 _ _ _ IV).
      + intros c q Hc Bc Hq. destruct (bw4 _ _ _ IV c q Hc Bc Hq) as [X (p' & Hp' & E')]. split; [exact X|]. exists p'. split; [lia| exact E'].
      + exact (bw5 _ _ _ IV).
      + intros c k' p' Hc Bc Hk' Kk' Hp' E'. destruct (Z.eq_dec p' j) as [->|NE].
        * exfalso. assert (k' = k). { apply (nxt_inj nb k' k Hk' Rk). rewrite Ek. fold u in E'. rewrite <- E'. reflexivity. }
          subst k'. rewrite Kk in Kk'. assert (c = c1) by lia. subst c. exact (Bc1 Bc).
        * apply (bw6 _ _ _ IV c k' p'); try assumption. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma BWI_loop : forall f a1 ce j, BWI a1 ce j -> j + 1 < Z.of_nat f ->
    let r := ms_copy_bwd f a1 ce a2r bd nb ss j in
    BWI (fst (fst r)) (snd (fst r)) (snd r) /\ snd r = zget (snd (fst r)) ss.
  Proof.
    induction f as [|f IH]; intros a1 ce j IV Hf; cbv zeta.
    - exfalso. pose proof (bw1 _ _ _ IV). pose proof (proj2 (proj2 (bw0 _ _ _ IV ss SS)) BD). pose proof (csF_le_ce1 a2 nb ss BB NB SS NA ss SS).
      pose proof (cs0_ge_0 a2 nb ss NB ss). cbn in Hf. lia.
    - rewrite ms_copy_bwd_S. destruct (Z.ltb_spec (zget ce ss) j) as [LT|GE].
      + pose proof (BWI_step a1 ce j IV LT) as ST. cbv zeta in ST. cps_destruct ST as (Ru & Rk & Rc & Kk & CASE0 & CASE1).
        cbv zeta. rewrite (prv_model' nb NB (rd32 a1 j) Ru). rewrite (AGR (PRV (rd32 a1 j)) Rk).
        destruct (Z.eqb_spec (zget bd (rd8 a2 (PRV (rd32 a1 j)))) 0) as [Bz|Bnz].
        * destruct (CASE0 Bz) as [_ IV']. apply (IH _ _ (j - 1) IV'). lia.
        * apply (IH a1 ce (j - 1) (CASE1 Bnz)). lia.
      + cbn [fst snd]. split; [exact IV|]. pose proof (bw1 _ _ _ IV). lia.
  Qed.

  Lemma BW_all_scanned : forall a1 ce X, BWI a1 ce X -> X = zget ce ss ->
    forall n u, 0 <= u < nb -> rd8 a2 u = ss -> side a2 nb ss n u = Some false -> exists p, X < p < B1 /\ rd32 a1 p = u.
  Proof.
    intros a1 ce X IV HX. induction n as [|n IH]; intros u Hu Bu Hs; [cbn in Hs; discriminate|].
    rewrite (side_S a2 nb ss) in Hs. cbv beta in Hs.
    destruct (Z.eqb_spec (rd8 a2 (NXT u)) ss) as [Bn|Bn].
    - cps_destruct (IH (NXT u) (nxt_range nb NB u Hu) Bn Hs) as (p' & Hp' & E').
      assert (Ku : KEY u = 256 * ss + ss) by (apply (proj2 (key_chars a2 nb BB u ss ss SS)); split; assumption).
      cps_destruct (bw6 _ _ _ IV ss u p' SS BD Hu Ku ltac:(lia) E') as (q & Hq & Eq).
      exists q. split; [| exact Eq]. pose proof (S1_le_B1 a2 nb ss SS). unfold BzCSewC.ce1, BzCSewC.B1 in *. lia.
    - injection Hs as Hs'. apply Z.ltb_ge in Hs'. pose proof (BB (NXT u)) as Bc.
      set (c := rd8 a2 (NXT u)) in *.
      assert (Ku : KEY u = 256 * ss + c) by (apply (proj2 (key_chars a2 nb BB u ss c ltac:(lia))); split; [assumption| reflexivity]).
      cps_destruct (BEX_cover a2 nb NB P0 (256 * ss + c) (P0X (256 * ss + c) ltac:(nia)) u Hu Ku) as (p & Hp & Ep).
      assert (Rp : ce1 ss <= p < B1).
      { unfold BzCSewC.ce1, BzCSewC.B1. pose proof (ClM_mono a2 nb (256 * ss + ss + 1) (256 * ss + c) ltac:(lia)).
        pose proof (ClM_mono a2 nb (256 * ss + c + 1) (256 * (ss + 1)) ltac:(lia)). lia. }
      exists p. pose proof (bw1 _ _ _ IV). pose proof (proj1 (bw0 _ _ _ IV ss SS)). split; [unfold BzCSewC.ce1 in *; lia|].
      rewrite <- Ep, <- (A0_tail p Rp). apply (bw3 _ _ _ IV). intros c' Hc' Bc' R. pose proof (proj2 (proj2 (bw0 _ _ _ IV c' Hc')) Bc').
      pose proof (csF_le_ce1 a2 nb ss BB NB SS NA c' Hc').
      apply (tail_no_reg a2 nb ss BB NB SS c' p Hc' Rp). lia.
  Qed.

  Definition ceB (c : Z) : Z := ce1 c - 1 - Z.of_nat (length (Fset c false)).

  Lemma BW_regions : forall a1 ce X, BWI a1 ce X -> X = zget ce ss ->
    forall c, 0 <= c < 256 -> zget bd c = 0 ->
      zget ce c = ceB c /\
      (forall q, zget ce c < q < ce1 c -> In (rd32 a1 q) (Fset c false)) /\
      (forall q q', zget ce c < q < ce1 c -> zget ce c < q' < ce1 c -> rd32 a1 q = rd32 a1 q' -> q = q') /\
      (forall k, In k (Fset c false) -> exists q, zget ce c < q < ce1 c /\ rd32 a1 q = k).
  Proof.
    intros a1 ce X IV HX c Hc Bc.
    assert (IN : forall q, zget ce c < q < ce1 c -> In (rd32 a1 q) (Fset c false)).
    { intros q Hq. apply (in_Fset a2 nb ss NB SS). exact (proj1 (bw4 _ _ _ IV c q Hc Bc Hq)). }
    assert (INJ : forall q q', zget ce c < q < ce1 c -> zget ce c < q' < ce1 c -> rd32 a1 q = rd32 a1 q' -> q = q').
    { intros q q'. apply (bw5 _ _ _ IV c); assumption. }
    assert (COV : forall k, In k (Fset c false) -> exists q, zget ce c < q < ce1 c /\ rd32 a1 q = k).
    { intros k Hk. apply (in_Fset a2 nb ss NB SS) in Hk. cps_destruct Hk as (Rk & Kk & Sk).
      destruct (proj1 (key_chars a2 nb BB k c ss SS) Kk) as [_ Bn].
      pose proof (SIDE_nxt a2 nb NB ss NA k Rk Bn) as SN. cbv beta in SN. rewrite Sk in SN.
      cps_destruct (BW_all_scanned a1 ce X IV HX (Z.to_nat nb) (NXT k) (nxt_range nb NB k Rk) Bn (eq_sym SN)) as (p & Hp & Ep).
      exact (bw6 _ _ _ IV c k p Hc Bc Rk Kk Hp Ep). }
    split; [| split; [exact IN| split; [exact INJ| exact COV]]].
    pose proof (proj1 (bw0 _ _ _ IV c Hc)) as L0.
    pose proof (region_eq a1 (zget ce c + 1) (ce1 c) (Fset c false) (Fset_NoDup a2 nb ss c false) ltac:(lia)
                  ltac:(intros q Hq; apply IN; lia) ltac:(intros q q' Hq Hq'; apply INJ; lia)) as RE.
    unfold ceB. assert (ce1 c - (zget ce c + 1) = Z.of_nat (length (Fset c false))); [|lia].
    apply RE. intros x Hx. cps_destruct (COV x Hx) as (q & Hq & Eq). exists q. split; [lia| exact Eq].
  Qed.

  Record BWPOST (a1 ce : zarr) : Prop := {
    bp_ce : forall c, 0 <= c < 256 -> zget ce c = (if zget bd c =? 0 then ceB c else ce1 c - 1);
    bp_frame : forall p, (forall c, 0 <= c < 256 -> zget bd c = 0 -> ~ (ceB c < p < ce1 c)) -> rd32 a1 p = rd32 A0 p;
    bp_in : forall c q, 0 <= c < 256 -> zget bd c = 0 -> ceB c < q < ce1 c -> In (rd32 a1 q) (Fset c false);
    bp_inj : forall c q q', 0 <= c < 256 -> zget bd c = 0 -> ceB c < q < ce1 c -> ceB c < q' < ce1 c -> rd32 a1 q = rd32 a1 q' -> q = q';
    bp_cov : forall c k, 0 <= c < 256 -> zget bd c = 0 -> In k (Fset c false) -> exists q, ceB c < q < ce1 c /\ rd32 a1 q = k;
    bp_meet : forall c, 0 <= c < 256 -> zget bd c = 0 -> ceB c = csF c - 1 }.

  Theorem backward_scan : forall ce, (forall c, 0 <= c < 256 -> zget ce c = ce1 c - 1) ->
    let r := ms_copy_bwd (S (Z.to_nat nb)) A0 ce a2r bd nb ss (B1 - 1) in
    BWPOST (fst (fst r)) (snd (fst r)) /\ snd r = zget (snd (fst r)) ss.
  Proof.
    intros ce Hce. cbv zeta.
    pose proof (BWI_loop (S (Z.to_nat nb)) A0 ce (B1 - 1) (BWI_init ce Hce) ltac:(pose proof (B1_le_nb a2 nb ss NB); lia)) as L. cbv zeta in L.
    destruct (ms_copy_bwd _ _ _ _ _ _ _ _) as [[a1 ce'] X]. cbn [fst snd] in *. destruct L as [IV HX].
    split; [| exact HX].
    assert (CE : forall c, 0 <= c < 256 -> zget bd c = 0 -> zget ce' c = ceB c).
    { intros c Hc Bc. exact (proj1 (BW_regions a1 ce' X IV HX c Hc Bc)). }
    constructor.
    - intros c Hc. destruct (Z.eqb_spec (zget bd c) 0) as [Bc|Bc]; [apply CE; assumption|]. apply (proj1 (proj2 (bw0 _ _ _ IV c Hc))). exact Bc.
    - intros p Hp. apply (bw3 _ _ _ IV). intros c Hc Bc. rewrite CE by assumption. apply Hp; assumption.
    - intros c q Hc Bc Hq. rewrite <- CE in Hq by assumption. exact (proj1 (proj2 (BW_regions a1 ce' X IV HX c Hc Bc)) q Hq).
    - intros c q q' Hc Bc Hq Hq'. rewrite <- CE in Hq, Hq' by assumption. exact (proj1 (proj2 (proj2 (BW_regions a1 ce' X IV HX c Hc Bc))) q q' Hq Hq').
    - intros c k Hc Bc Hk. rewrite <- CE by assumption. exact (proj2 (proj2 (proj2 (BW_regions a1 ce' X IV HX c Hc Bc))) k Hk).
    - intros c Hc Bc. unfold ceB, BzCSewC.csF. pose proof (Fset_sum a2 nb ss BB NB SS NA c Hc). unfold BzCSewC.cs0, BzCSewC.ce1 in *. lia.
  Qed.
End CopyB.
