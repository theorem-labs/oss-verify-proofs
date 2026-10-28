(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzLemmasT BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCPermF BzCPermF2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCPermM BzCQsortM1 BzCQsortM2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewA.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC BzCSewD BzCSewE.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCQsortM2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA.BzCBudget OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewA OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewE.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ms_step1_S : forall n qoff nblock ss j s,
  ms_step1 (S n) qoff nblock ss j s =
  (if s_exit s then s else
   if j =? ss then ms_step1 n qoff nblock ss (j + 1) s else
   let sb := Z.shiftl ss 8 + j in
   let ft := s_ft s in
   let '(s1, stop) :=
     (if negb (has_setmask (zget ft sb)) then
        let lo := clearmask (zget ft sb) in
        let hi := clearmask (zget ft (sb + 1)) - 1 in
        if lo <? hi then
          let '(a1, budget, mql) := mainQSort3 (s_a1 s) (s_a2 s) qoff nblock lo hi BZ_N_RADIX (s_budget s) (s_mql s) in
          let s1 := MSS a1 (s_a2 s) ft (s_bd s) (s_cs s) (s_ce s) budget (s_nqs s + (hi - lo + 1)) mql false in
          if budget <? 0 then (MSS a1 (s_a2 s) ft (s_bd s) (s_cs s) (s_ce s) budget (s_nqs s + (hi - lo + 1)) mql true, true)
          else (s1, false)
        else (s, false)
      else (s, false)) in
   if stop then s1 else
   let s2 := MSS (s_a1 s1) (s_a2 s1) (zset (s_ft s1) sb (Z.lor (zget (s_ft s1) sb) SETMASK)) (s_bd s1) (s_cs s1) (s_ce s1)
                 (s_budget s1) (s_nqs s1) (s_mql s1) false in
   ms_step1 n qoff nblock ss (j + 1) s2).
Proof. reflexivity. Qed.
Lemma ms_copy_init_S : forall n cs ce ft ss j,
  ms_copy_init (S n) cs ce ft ss j =
  ms_copy_init n (zset cs j (clearmask (zget ft (Z.shiftl j 8 + ss)))) (zset ce j (clearmask (zget ft (Z.shiftl j 8 + ss + 1)) - 1)) ft ss (j + 1).
Proof. reflexivity. Qed.
Lemma ms_mark_S : forall n ft ss j,
  ms_mark (S n) ft ss j = ms_mark n (let x := Z.shiftl j 8 + ss in zset ft x (Z.lor (zget ft x) SETMASK)) ss (j + 1).
Proof. reflexivity. Qed.
Lemma ms_shifts_S : forall f b sh, ms_shifts (S f) b sh = (if 65534 <? Z.shiftr b sh then ms_shifts f b (sh + 1) else sh).
Proof. reflexivity. Qed.
Lemma ms_quad_S : forall n a2 a1 qoff nblock bbStart shifts j,
  ms_quad (S n) a2 a1 qoff nblock bbStart shifts j =
  (let a2u := rd32 a1 (bbStart + j) in
   let qVal := Z.shiftr j shifts in
   let a2' := qwr a2 qoff a2u qVal in
   let a2'' := if a2u <? BZ_N_OVERSHOOT then qwr a2' qoff (a2u + nblock) qVal else a2' in
   ms_quad n a2'' a1 qoff nblock bbStart shifts (j - 1)).
Proof. reflexivity. Qed.
Lemma ms_bigs_S : forall n ro qoff nblock i s,
  ms_bigs (S n) ro qoff nblock i s = (let s1 := ms_big ro qoff nblock i s in if s_exit s1 then s1 else ms_bigs n ro qoff nblock (i + 1) s1).
Proof. reflexivity. Qed.

Lemma shl8 : forall x, Z.shiftl x 8 = 256 * x.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256. lia. Qed.

(* [comment removed for export] *)
Lemma rd8_qwr_low : forall a qoff i v k, k < qoff -> 0 <= i -> rd8 (qwr a qoff i v) k = rd8 a k.
Proof. intros a qoff i v k Hk Hi. unfold qwr, wr16, rd8. rewrite !zget_zset_other by lia. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ms_shifts_spec : forall f b sh, 0 <= b -> 0 <= sh -> Z.shiftr b (sh + Z.of_nat f) <= 65534 ->
  let r := ms_shifts f b sh in sh <= r <= sh + Z.of_nat f /\ Z.shiftr b r <= 65534.
Proof.
  induction f as [|f IH]; intros b sh Hb Hsh Hf; cbv zeta.
  - cbn [ms_shifts]. replace (sh + Z.of_nat 0) with sh in Hf by lia. lia.
  - rewrite ms_shifts_S. destruct (Z.ltb_spec 65534 (Z.shiftr b sh)) as [L|L].
    + specialize (IH b (sh + 1) Hb ltac:(lia)). cbv zeta in IH.
      replace (sh + 1 + Z.of_nat f) with (sh + Z.of_nat (S f)) in IH by lia. destruct (IH Hf). lia.
    + lia.
Qed.

(* [comment removed for export] *)
Lemma ms_shifts_main : forall b, 0 <= b < 2097152 ->
  let r := ms_shifts 40 b 0 in 0 <= r <= 40 /\ Z.shiftr b r <= 65534 /\ Z.shiftr (b - 1) r <= 65535 /\
  (forall j, 0 <= j < b -> 0 <= Z.shiftr j r <= 65535).
Proof.
  intros b Hb. cbv zeta.
  pose proof (ms_shifts_spec 40 b 0 ltac:(lia) ltac:(lia)) as SP. cbv zeta in SP.
  destruct SP as [R1 R2].
  { rewrite Z.shiftr_div_pow2 by lia. apply Z.div_le_upper_bound; [lia|]. change (Z.of_nat 40) with 40. cbn [Z.add].
    assert (2 ^ 21 <= 2 ^ 40) by (apply Z.pow_le_mono_r; lia). change (2 ^ 21) with 2097152 in H. nia. }
  set (r := ms_shifts 40 b 0) in *.
  assert (P : 0 < 2 ^ r) by (apply Z.pow_pos_nonneg; lia).
  split; [lia|]. split; [exact R2|]. rewrite !Z.shiftr_div_pow2 in * by lia. split.
  - pose proof (Z.div_le_mono (b - 1) b (2 ^ r) P ltac:(lia)). lia.
  - intros j Hj. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|]. pose proof (Z.div_le_mono j b (2 ^ r) P ltac:(lia)). lia.
Qed.

Section Main.
  Variables (a2 : zarr) (nb qoff : Z) (ro : zarr).
  Hypothesis BB : forall i, 0 <= rd8 a2 i < 256.
  Hypothesis NB : 1 <= nb <= 2097151.
  Hypothesis NB2 : nb <= 1000000.
  Hypothesis QO : nb + 34 <= qoff.
  Hypothesis RO : forall i, 0 <= i < 256 -> 0 <= zget ro i < 256.
  Hypothesis ROinj : forall i i', 0 <= i < 256 -> 0 <= i' < 256 -> zget ro i = zget ro i' -> i = i'.

  Local Notation KEY := (key a2 nb).
  Local Notation CLM := (ClM a2 nb).

  (* [comment removed for export] *)
  Variable a2x : zarr.
  Hypothesis AX : forall k, 0 <= k < nb -> rd8 a2x k = rd8 a2 k.

  Definition FT (ft : zarr) : Prop := forall v, 0 <= v <= 65536 -> ftcell (zget ft v) (CLM v).

  Record MI (i : Z) (s : mss) : Prop := {
    mi_pinv : PINV a2 nb (s_a1 s);
    mi_a2 : forall k, 0 <= k < nb + 34 -> rd8 (s_a2 s) k = rd8 a2x k;
    mi_ft : FT (s_ft s);
    mi_bd01 : forall c, 0 <= c < 256 -> zget (s_bd s) c = 0 \/ zget (s_bd s) c = 1;
    mi_bd : forall c, 0 <= c < 256 -> (zget (s_bd s) c <> 0 <-> exists i', 0 <= i' < i /\ zget ro i' = c);
    mi_exit : s_exit s = false }.

  Lemma ClM_lt : forall v, 0 <= CLM v < 2097152.
  Proof. intros v. pose proof (ClM_range a2 nb ltac:(lia) v). lia. Qed.

  Lemma FT_lohi : forall ft v, FT ft -> 0 <= v <= 65535 ->
    clearmask (zget ft v) = CLM v /\ clearmask (zget ft (v + 1)) = CLM (v + 1) /\
    0 <= zget ft v < 4294967296 /\ 0 <= zget ft (v + 1) < 4294967296.
  Proof.
    intros ft v F Hv. pose proof (ClM_lt v). pose proof (ClM_lt (v + 1)).
    split; [apply ftcell_clear; [lia| apply F; lia]|]. split; [apply ftcell_clear; [lia| apply F; lia]|].
    split; (eapply ftcell_range; [| apply F; lia]); lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition S1I (s0 s : mss) : Prop :=
    PINV a2 nb (s_a1 s) /\ FT (s_ft s) /\ s_a2 s = s_a2 s0 /\ s_bd s = s_bd s0.

  Lemma ms_step1_inv : forall n ss j s0 s, 0 <= ss < 256 -> 0 <= j -> j + Z.of_nat n <= 256 -> S1I s0 s ->
    S1I s0 (ms_step1 n qoff nb ss j s).
  Proof.
    induction n as [|n IH]; intros ss j s0 s Hss Hj Hn IV; [exact IV|].
    rewrite ms_step1_S. destruct (s_exit s); [exact IV|].
    destruct (Z.eqb_spec j ss) as [->|NE]; [apply IH; try assumption; lia|].
    cbv zeta. rewrite shl8.
    cps_destruct IV as (P & F & EA & EB).
    cps_pose (FT_lohi (s_ft s) (256 * ss + j) F ltac:(lia)) as (C1 & C2 & R1 & R2). rewrite C1, C2.
    set (sb := 256 * ss + j) in *.
    assert (MARK : forall s1, S1I s0 s1 ->
      S1I s0 (MSS (s_a1 s1) (s_a2 s1) (zset (s_ft s1) sb (Z.lor (zget (s_ft s1) sb) SETMASK)) (s_bd s1) (s_cs s1) (s_ce s1) (s_budget s1) (s_nqs s1) (s_mql s1) false)).
    { (intros s1; cps_intros (P1 & F1 & EA1 & EB1)). split; [exact P1|]. split; [| split; assumption]. cbn [s_ft].
      intros v Hv. rewrite zget_zset. destruct (Z.eqb_spec v sb) as [->|NV]; [apply ftcell_mark|]; apply F1; lia. }
    destruct (negb (has_setmask (zget (s_ft s) sb))).
    - destruct (Z.ltb_spec (CLM sb) (CLM (sb + 1) - 1)) as [LT|GE].
      + pose proof (mqs3_perm_frame nb ltac:(lia) (CLM sb) (CLM (sb + 1) - 1) BZ_N_RADIX (s_a2 s) qoff nb ltac:(unfold BZ_N_RADIX; lia)
                      ltac:(pose proof (ClM_lt sb); lia) ltac:(pose proof (ClM_range a2 nb ltac:(lia) (sb + 1)); lia) ltac:(pose proof (ClM_range a2 nb ltac:(lia) (sb + 1)); pose proof (ClM_lt sb); change (21 * 2 ^ 16) with 1376256; lia)
                      (s_a1 s) (s_budget s) (s_mql s) (PINV_perm a2 nb BB NB _ P) ltac:(lia)) as MQ.
        cbv zeta in MQ. destruct (mainQSort3 _ _ _ _ _ _ _ _ _) as [[a1 budget] mql]. cbn [fst] in MQ. destruct MQ as [PM FR].
        assert (P' : PINV a2 nb a1).
        { apply (PINV_perm_frame a2 nb BB NB (s_a1 s) a1 sb P ltac:(pose proof (key_range a2 nb BB 0); lia) PM FR). }
        destruct (Z.ltb_spec budget 0) as [BL|BG].
        * (* [comment removed for export] *) split; [exact P'|]. cbn. split; [exact F| split; assumption].
        * apply IH; [exact Hss| lia| lia|]. apply MARK. split; [exact P'|]. cbn. split; [exact F| split; assumption].
      + apply IH; [exact Hss| lia| lia|]. apply MARK. split; [exact P|]. split; [exact F| split; assumption].
    - apply IH; [exact Hss| lia| lia|]. apply MARK. split; [exact P|]. split; [exact F| split; assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ms_copy_init_spec : forall n cs ce ft ss j0, FT ft -> 0 <= ss < 256 -> 0 <= j0 -> j0 + Z.of_nat n <= 256 ->
    let r := ms_copy_init n cs ce ft ss j0 in
    (forall c, j0 <= c < j0 + Z.of_nat n -> zget (fst r) c = CLM (256 * c + ss) /\ zget (snd r) c = CLM (256 * c + ss + 1) - 1) /\
    (forall c, (c < j0 \/ j0 + Z.of_nat n <= c) -> zget (fst r) c = zget cs c /\ zget (snd r) c = zget ce c).
  Proof.
    induction n as [|n IH]; intros cs ce ft ss j0 F Hss Hj Hn; cbv zeta.
    - cbn [ms_copy_init fst snd]. split; [intros; lia| intros; split; reflexivity].
    - rewrite ms_copy_init_S. rewrite shl8.
      cps_pose (FT_lohi ft (256 * j0 + ss) F ltac:(lia)) as (C1 & C2 & _). rewrite C1, C2.
      destruct (IH (zset cs j0 (CLM (256 * j0 + ss))) (zset ce j0 (CLM (256 * j0 + ss + 1) - 1)) ft ss (j0 + 1) F Hss ltac:(lia) ltac:(lia)) as [V Fr].
      split.
      + intros c Hc. destruct (Z.eq_dec c j0) as [->|NE].
        * destruct (Fr j0 ltac:(lia)) as [F1 F2]. rewrite F1, F2, !zget_zset_same. split; reflexivity.
        * apply V. lia.
      + intros c Hc. destruct (Fr c ltac:(lia)) as [F1 F2]. rewrite F1, F2, !zget_zset_other by lia. split; reflexivity.
  Qed.

  Lemma ms_mark_spec : forall n ft ss j0, FT ft -> 0 <= ss < 256 -> 0 <= j0 -> j0 + Z.of_nat n <= 256 -> FT (ms_mark n ft ss j0).
  Proof.
    induction n as [|n IH]; intros ft ss j0 F Hss Hj Hn; [exact F|].
    rewrite ms_mark_S. cbv zeta. rewrite shl8. apply IH; [| exact Hss| lia| lia].
    intros v Hv. rewrite zget_zset. destruct (Z.eqb_spec v (256 * j0 + ss)) as [->|NV]; [apply ftcell_mark|]; apply F; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma ms_quad_low : forall n b a1 bbStart shifts j, (forall x, 0 <= x <= j -> 0 <= rd32 a1 (bbStart + x) < nb) -> j + 1 = Z.of_nat n ->
    forall k, 0 <= k < nb + 34 -> rd8 (ms_quad n b a1 qoff nb bbStart shifts j) k = rd8 b k.
  Proof.
    induction n as [|n IH]; intros b a1 bbStart shifts j RG Hj k Hk; [reflexivity|].
    rewrite ms_quad_S. cbv zeta.
    pose proof (RG j ltac:(lia)) as Ru.
    rewrite IH; [| intros; apply RG; lia| lia| exact Hk].
    destruct (Z.ltb_spec (rd32 a1 (bbStart + j)) BZ_N_OVERSHOOT); repeat (rewrite rd8_qwr_low by lia); reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem ms_big_MI : forall i s, 0 <= i < 256 -> MI i s ->
    let s' := ms_big ro qoff nb i s in (s_exit s' = true /\ (forall k, 0 <= k < nb + 34 -> rd8 (s_a2 s') k = rd8 a2x k)) \/ MI (i + 1) s'.
  Proof.
    intros i s Hi IV. cbv zeta. unfold ms_big. cbv zeta.
    pose proof (RO i Hi) as Hss. set (ss := zget ro i) in *.
    pose proof (ms_step1_inv 256 ss 0 s s Hss ltac:(lia) ltac:(cbn; lia) (conj (mi_pinv _ _ IV) (conj (mi_ft _ _ IV) (conj eq_refl eq_refl)))) as S1.
    set (s1 := ms_step1 256 qoff nb ss 0 s) in *. cps_destruct S1 as (P1 & F1 & EA1 & EB1).
    destruct (s_exit s1) eqn:EX1; [left; split; [exact EX1| intros k Hk; rewrite EA1; apply (mi_a2 _ _ IV); exact Hk]| right].
    (* [comment removed for export] *)
    pose proof (ms_copy_init_spec 256 (s_cs s1) (s_ce s1) (s_ft s1) ss 0 F1 Hss ltac:(lia) ltac:(cbn; lia)) as CI. cbv zeta in CI.
    destruct (ms_copy_init 256 (s_cs s1) (s_ce s1) (s_ft s1) ss 0) as [cs ce]. cbn [fst snd] in CI. destruct CI as [CI _].
    change (Z.of_nat 256) with 256 in CI.
    assert (BD0 : zget (s_bd s1) ss = 0).
    { rewrite EB1. destruct (mi_bd01 _ _ IV ss Hss) as [E|E]; [exact E|]. exfalso.
      cps_destruct (proj1 (mi_bd _ _ IV ss Hss) ltac:(rewrite E; lia)) as (i' & Hi' & Ei'). pose proof (ROinj i' i ltac:(lia) Hi Ei'). lia. }
    rewrite ?(shl8 ss), ?(shl8 (ss + 1)). pose proof (FT_lohi (s_ft s1) (256 * ss) F1 ltac:(lia)) as (C1 & _). rewrite C1.
    replace (256 * (ss + 1)) with (256 * ss + 255 + 1) by lia.
    cps_pose (FT_lohi (s_ft s1) (256 * ss + 255) F1 ltac:(lia)) as (_ & C2 & _). rewrite C2. replace (256 * ss + 255 + 1) with (256 * (ss + 1)) by lia.
    assert (AGR : forall k, 0 <= k < nb -> rd8 (s_a2 s1) k = rd8 a2 k).
    { intros k Hk. rewrite EA1, (mi_a2 _ _ IV) by lia. apply AX. exact Hk. }
    pose proof (step2_exact a2 nb ss (s_bd s1) (s_a1 s1) (s_a2 s1) BB NB Hss BD0 P1 AGR cs ce
                  ltac:(intros c Hc; apply (proj1 (CI c Hc))) ltac:(intros c Hc; apply (proj2 (CI c Hc)))) as S2.
    cbv zeta in S2. unfold BzCSewC.B0, BzCSewC.B1 in S2.
    destruct (ms_copy_fwd _ _ _ _ _ _ _ _) as [[af csf] jf]. cbn [fst snd] in S2.
    destruct (ms_copy_bwd _ _ _ _ _ _ _ _) as [[ab ceb] jb]. cbn [fst snd] in S2.
    cps_destruct S2 as (P2 & MEET & RNG & FRM & _ & _).
    (* [comment removed for export] *)
    constructor; cbn [s_a1 s_a2 s_ft s_bd s_exit].
    - exact P2.
    - intros k Hk. destruct (Z.ltb_spec i 255) as [L|L]; [| rewrite EA1; apply (mi_a2 _ _ IV); exact Hk].
      rewrite ms_quad_low; [rewrite EA1; apply (mi_a2 _ _ IV); exact Hk| | | exact Hk].
      + intros x Hx. pose proof (ms_mark_spec 256 (s_ft s1) ss 0 F1 Hss ltac:(lia) ltac:(cbn; lia)) as FM.
        rewrite ?(shl8 ss), ?(shl8 (ss + 1)). pose proof (FT_lohi _ (256 * ss) FM ltac:(lia)) as (D1 & _). rewrite D1.
        apply (proj1 (PINV_perm a2 nb BB NB ab P2)).
        replace (256 * (ss + 1)) with (256 * ss + 255 + 1) in Hx by lia.
        cps_pose (FT_lohi _ (256 * ss + 255) FM ltac:(lia)) as (_ & D2 & _). rewrite D2 in Hx.
        pose proof (ClM_range a2 nb ltac:(lia) (256 * ss)). pose proof (ClM_range a2 nb ltac:(lia) (256 * ss + 255 + 1)). lia.
      + rewrite ?(shl8 ss), ?(shl8 (ss + 1)). pose proof (ms_mark_spec 256 (s_ft s1) ss 0 F1 Hss ltac:(lia) ltac:(cbn; lia)) as FM.
        pose proof (FT_lohi _ (256 * ss) FM ltac:(lia)) as (D1 & _). rewrite D1.
        replace (256 * (ss + 1)) with (256 * ss + 255 + 1) by lia.
        cps_pose (FT_lohi _ (256 * ss + 255) FM ltac:(lia)) as (_ & D2 & _). rewrite D2.
        pose proof (ClM_mono a2 nb (256 * ss) (256 * ss + 255 + 1) ltac:(lia)). lia.
    - apply ms_mark_spec; [exact F1| exact Hss| lia| cbn; lia].
    - intros c Hc. rewrite zget_zset, EB1. destruct (Z.eqb_spec c ss) as [->|NC]; [right; reflexivity|]. apply (mi_bd01 _ _ IV). exact Hc.
    - intros c Hc. rewrite zget_zset, EB1. destruct (Z.eqb_spec c ss) as [->|NC].
      + split; [intros _; exists i; split; [lia| reflexivity]| intros; lia].
      + rewrite (mi_bd _ _ IV c Hc). split.
        * cps_intros (i' & Hi' & E). exists i'. split; [lia| exact E].
        * cps_intros (i' & Hi' & E). destruct (Z.eq_dec i' i) as [->|NI]; [exfalso; apply NC; rewrite <- E; reflexivity|].
          exists i'. split; [lia| exact E].
    - reflexivity.
  Qed.

  Theorem ms_bigs_MI : forall n i s, 0 <= i -> i + Z.of_nat n <= 256 -> MI i s ->
    let s' := ms_bigs n ro qoff nb i s in (s_exit s' = true /\ (forall k, 0 <= k < nb + 34 -> rd8 (s_a2 s') k = rd8 a2x k)) \/ MI (i + Z.of_nat n) s'.
  Proof.
    induction n as [|n IH]; intros i s Hi Hn IV; cbv zeta.
    - cbn [ms_bigs]. right. replace (i + Z.of_nat 0) with i by lia. exact IV.
    - rewrite ms_bigs_S. cbv zeta. destruct (ms_big_MI i s ltac:(lia) IV) as [[EX A2]|IV'].
      + rewrite EX. left. split; [exact EX| exact A2].
      + rewrite (mi_exit _ _ IV'). replace (i + Z.of_nat (S n)) with (i + 1 + Z.of_nat n) by lia. apply IH; [lia| lia| exact IV'].
  Qed.
End Main.
