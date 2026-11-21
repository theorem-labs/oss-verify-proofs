(** * EnoughFitsB11 — session 8 (S2, part 1): examineF memo-soundness
    machinery — the traversal domain, the memo invariant, and the
    window forcing.

    KEY STRUCTURAL FACT (corrects the f-c-era reading): the use-window
    FORCES completion at the max depth.  At len = mxa - 1 the window is
    the singleton use = 2*left - syms whose child is complete (or the
    window is empty); so no loop node ever lives past len = mxa - 1,
    the traversal never leaves the domain, and every visited juncture
    packs injectively into key5 (dom5).  The memo invariant MINV is
    len-STRATIFIED: a node's own key is added BEFORE its subtree runs
    (enough.c:408-410), which is sound exactly because a subtree only
    queries keys at strictly larger lens. *)

From Stdlib Require Import ZArith List Lia Bool FMapPositive.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsA12 EnoughFitsB1
  EnoughFitsB2 EnoughFitsB4 EnoughFitsB8 EnoughFitsPhi.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The traversal domain.
   ========================================================================== *)

Definition DOMS (rt mxa syms left len mem rem : Z) : Prop :=
  0 <= syms <= 2 ^ 21
  /\ 0 <= left <= syms
  /\ rt + 1 <= len <= mxa
  /\ (len <= mxa - 1 \/ syms = left)
  /\ 0 <= mem <= 2 ^ 15 + len * 2 ^ 22
  /\ 0 <= rem <= 2 ^ (len - rt).

Lemma doms_dom5 : forall rt mxa syms left len mem rem,
  1 <= rt -> mxa <= 15 ->
  DOMS rt mxa syms left len mem rem ->
  dom5 syms left len mem rem.
Proof.
  intros rt mxa syms left len mem rem Hrt Hmx
         (Hs & Hl & Hlen & _ & Hm & Hr).
  unfold dom5, W.
  assert (H20 : (2:Z) ^ 21 = 2097152) by (vm_compute; reflexivity).
  assert (H40 : (2:Z) ^ 40 = 1099511627776) by (vm_compute; reflexivity).
  assert (H15 : (2:Z) ^ 15 = 32768) by (vm_compute; reflexivity).
  assert (H21 : (2:Z) ^ 22 = 4194304) by (vm_compute; reflexivity).
  assert (Hsub : 2 ^ (len - rt) <= 2 ^ 14).
  { apply Z.pow_le_mono_r; [clear; lia | clear -Hlen Hrt Hmx; lia]. }
  assert (H14 : (2:Z) ^ 14 = 16384) by (vm_compute; reflexivity).
  repeat split; try (clear -Hs Hl Hlen Hm Hr Hrt Hmx H20 H40 H15 H21
                       Hsub H14; lia).
Qed.

(* ==========================================================================
   2.  The window: bounds, feasibility transport, and the forcing.
   ========================================================================== *)

Lemma most_le_left : forall mxa syms left len,
  0 <= left <= syms -> len <= mxa - 1 ->
  (left * 2 ^ (mxa - len) - syms) / (2 ^ (mxa - len) - 1) <= left.
Proof.
  intros mxa syms left len Hl Hlen.
  assert (HD : 2 <= 2 ^ (mxa - len)).
  { pose proof (Z.pow_le_mono_r 2 1 (mxa - len)
                  ltac:(clear; lia) ltac:(clear -Hlen; lia)) as H.
    clear -H; lia. }
  apply Z.div_le_upper_bound; [clear -HD; lia|].
  replace ((2 ^ (mxa - len) - 1) * left)
    with (left * 2 ^ (mxa - len) - left) by ring.
  clear -Hl; lia.
Qed.

Lemma least_child : forall syms left use,
  Z.max 0 (2 * left - syms) <= use ->
  2 * (left - use) <= syms - use.
Proof. intros. clear -H; lia. Qed.

(** The forcing at the last live level: the window is a singleton
    whose child is complete, or empty. *)
Lemma window_forcing : forall mxa syms left,
  0 <= left <= syms ->
  let least := Z.max 0 (2 * left - syms) in
  let most := (left * 2 ^ (mxa - (mxa - 1)) - syms)
              / (2 ^ (mxa - (mxa - 1)) - 1) in
  (2 * left - syms < 0 /\ Z.to_nat (most - least + 1) = 0%nat)
  \/ (0 <= 2 * left - syms /\ least = most
      /\ syms - least = 2 * (left - least)).
Proof.
  intros mxa syms left Hl.
  cbv zeta.
  replace (mxa - (mxa - 1)) with 1 by (clear; lia).
  change ((2:Z) ^ 1) with 2.
  rewrite Z.div_1_r.
  destruct (Z.lt_ge_cases (2 * left - syms) 0) as [Hneg|Hpos].
  - left. split; [exact Hneg|].
    rewrite Z.max_l by (clear -Hneg; lia).
    clear -Hneg; lia.
  - right. split; [exact Hpos|].
    rewrite Z.max_r by (clear -Hpos; lia).
    split; [clear; lia | clear; lia].
Qed.

(* ==========================================================================
   3.  Chain caps along a level.
   ========================================================================== *)

Lemma chain_code_caps : forall s m r,
  1 <= s -> 0 <= r <= s ->
  0 <= snd (chain_code s m r) <= s
  /\ m <= fst (chain_code s m r) <= m + s.
Proof.
  intros s m r Hs Hr.
  unfold chain_code.
  destruct (Z.eqb_spec r 0) as [->|Hne]; cbn [fst snd].
  - split; clear -Hs Hr; lia.
  - split; clear -Hs Hr Hne; lia.
Qed.

Lemma chain_codes_rem_cap : forall k s m r,
  1 <= s -> 0 <= r <= s ->
  0 <= snd (chain_codes k s m r) <= s.
Proof.
  induction k as [|k IH]; intros s m r Hs Hr.
  - cbn [chain_codes snd]. exact Hr.
  - cbn [chain_codes].
    destruct (chain_code s m r) as [m' r'] eqn:EC.
    pose proof (chain_code_caps s m r Hs Hr) as [Hr' _].
    rewrite EC in Hr'. cbn [snd] in Hr'.
    apply IH; [exact Hs | exact Hr'].
Qed.

(** Mem through a level, via the Phi law: bounded by the codes taken
    plus one table. *)
Lemma chain_codes_mem_cap : forall k s m r,
  1 <= s -> 0 <= r <= s ->
  fst (chain_codes k s m r) <= m + Z.of_nat k + s.
Proof.
  intros k s m r Hs Hr.
  pose proof (chain_phi k s m r) as HPhi.
  pose proof (chain_codes_rem_cap k s m r Hs Hr) as [_ Hub].
  clear -HPhi Hub Hr; lia.
Qed.

(* ==========================================================================
   4.  The memo invariant, len-stratified and fuel-linked.
   ========================================================================== *)

Definition MINV (mxa rt B : Z) (done : PM.t unit) (large ell : Z) : Prop :=
  forall s l L m r,
    dom5 s l L m r ->
    ell <= L ->
    PM.find (key5 s l L m r) done = Some tt ->
    dp_max (Z.to_nat (B - L)) mxa rt s l L m r <= large.

Lemma minv_mono : forall mxa rt B done large large' ell ell',
  large <= large' -> ell <= ell' ->
  MINV mxa rt B done large ell ->
  MINV mxa rt B done large' ell'.
Proof.
  intros mxa rt B done large large' ell ell' Hg He HM s l L m r Hd HL Hf.
  eapply Z.le_trans; [apply (HM s l L m r Hd) | exact Hg].
  - clear -HL He; lia.
  - exact Hf.
Qed.

Lemma minv_add : forall mxa rt B done large ell s0 l0 L0 m0 r0,
  dom5 s0 l0 L0 m0 r0 ->
  ell <= L0 ->
  dp_max (Z.to_nat (B - L0)) mxa rt s0 l0 L0 m0 r0 <= large ->
  MINV mxa rt B done large ell ->
  MINV mxa rt B (PM.add (key5 s0 l0 L0 m0 r0) tt done) large ell.
Proof.
  intros mxa rt B done large ell s0 l0 L0 m0 r0 Hd0 HL0 Hdp HM
         s l L m r Hd HL Hf.
  destruct (PM.E.eq_dec (key5 s l L m r) (key5 s0 l0 L0 m0 r0))
    as [He|Hne].
  - pose proof (key5_inj s l L m r s0 l0 L0 m0 r0 Hd Hd0 He)
      as (-> & -> & -> & -> & ->).
    exact Hdp.
  - rewrite PM.gso in Hf by exact Hne.
    exact (HM s l L m r Hd HL Hf).
Qed.

Lemma minv_addself : forall mxa rt B done large ell s0 l0 L0 m0 r0,
  dom5 s0 l0 L0 m0 r0 ->
  ell = L0 ->
  MINV mxa rt B done large ell ->
  MINV mxa rt B (PM.add (key5 s0 l0 L0 m0 r0) tt done) large (ell + 1).
Proof.
  intros mxa rt B done large ell s0 l0 L0 m0 r0 Hd0 -> HM
         s l L m r Hd HL Hf.
  destruct (PM.E.eq_dec (key5 s l L m r) (key5 s0 l0 L0 m0 r0))
    as [He|Hne].
  - exfalso.
    pose proof (key5_inj s l L m r s0 l0 L0 m0 r0 Hd Hd0 He)
      as (_ & _ & HLe & _).
    clear -HL HLe; lia.
  - rewrite PM.gso in Hf by exact Hne.
    apply (HM s l L m r Hd ltac:(clear -HL; lia) Hf).
Qed.

(* ==========================================================================
   5.  The use loop, reified (the anonymous fix, as a constant the
       induction can speak about).
   ========================================================================== *)

Fixpoint eloopF (f : nat) (mxa rt syms left len subsz : Z)
                (n : nat) (use mem rem : Z) (st : Z * PM.t unit)
  : Z * PM.t unit :=
  match n with
  | O => st
  | S n' =>
      let st1 :=
        examineF f mxa rt (syms - use) (2 * (left - use)) (len + 1)
                 (mem + (if rem =? 0 then 0 else subsz)) (2 * rem) st in
      let '(mem', rem') :=
        if rem =? 0 then (mem + subsz, subsz - 1) else (mem, rem - 1) in
      eloopF f mxa rt syms left len subsz n' (use + 1) mem' rem' st1
  end.

Lemma examineF_fresh_eq :
  forall f mxa rt syms left len mem rem large done,
  (syms =? left) = false ->
  PM.find (key5 syms left len mem rem) done = None ->
  examineF (S f) mxa rt syms left len mem rem (large, done)
  = (let '(u1, m1, r1) :=
       drain (Z.to_nat (Z.max 0 (2 * left - syms)) + 2) (2 ^ (len - rt))
             (Z.max 0 (2 * left - syms)) mem rem in
     eloopF f mxa rt syms left len (2 ^ (len - rt))
       (Z.to_nat ((left * 2 ^ (mxa - len) - syms)
                  / (2 ^ (mxa - len) - 1)
                  - Z.max 0 (2 * left - syms) + 1))
       (Z.max 0 (2 * left - syms)) m1 (r1 - u1)
       (large, PM.add (key5 syms left len mem rem) tt done)).
Proof.
  intros f mxa rt syms left len mem rem large done Hne HF.
  cbn [examineF].
  rewrite Hne, HF.
  destruct (drain (Z.to_nat (Z.max 0 (2 * left - syms)) + 2)
              (2 ^ (len - rt)) (Z.max 0 (2 * left - syms)) mem rem)
    as [[u1 m1] r1].
  generalize (Z.to_nat ((left * 2 ^ (mxa - len) - syms)
                        / (2 ^ (mxa - len) - 1)
                        - Z.max 0 (2 * left - syms) + 1)) as n.
  generalize (large, PM.add (key5 syms left len mem rem) tt done) as st.
  generalize (r1 - u1) as rr.
  generalize m1 as mm.
  generalize (Z.max 0 (2 * left - syms)) as u0.
  intros u0 mm rr st n.
  revert u0 mm rr st.
  induction n as [|n IH]; intros u0 mm rr st.
  - reflexivity.
  - cbn [eloopF].
    cbv beta iota.
    destruct st as [lg dn].
    destruct (rr =? 0) eqn:HR0; cbv beta iota; apply IH.
Qed.

(* ==========================================================================
   6.  THE MEMO-SOUNDNESS.
   ========================================================================== *)

(** The per-fuel statement (the loop lemma consumes it as its IH). *)
Definition EXS (f : nat) (rt mxa B : Z) : Prop :=
  forall syms left len mem rem large done,
    Z.of_nat f = B - len ->
    DOMS rt mxa syms left len mem rem ->
    0 <= large ->
    MINV mxa rt B done large len ->
    large <= fst (examineF f mxa rt syms left len mem rem (large, done))
    /\ MINV mxa rt B
         (snd (examineF f mxa rt syms left len mem rem (large, done)))
         (fst (examineF f mxa rt syms left len mem rem (large, done))) len
    /\ (forall s l L m r, dom5 s l L m r -> L < len ->
          PM.find (key5 s l L m r)
            (snd (examineF f mxa rt syms left len mem rem (large, done)))
          = PM.find (key5 s l L m r) done)
    /\ dp_max f mxa rt syms left len mem rem
       <= fst (examineF f mxa rt syms left len mem rem (large, done)).

Lemma eloop_sound :
  forall (f : nat) (rt mxa B syms left len mem0 rem0 : Z),
  1 <= rt -> rt <= mxa <= 15 -> B <= 34 ->
  Z.of_nat (S f) = B - len ->
  0 <= syms <= 2 ^ 21 -> 0 <= left <= syms ->
  rt + 1 <= len <= mxa - 1 ->
  0 <= mem0 <= 2 ^ 15 + len * 2 ^ 22 ->
  0 <= rem0 <= 2 ^ (len - rt) ->
  EXS f rt mxa B ->
  forall (n : nat) (use memL remL lg : Z) (dn : PM.t unit) (acc : Z),
    Z.max 0 (2 * left - syms) <= use ->
    Z.of_nat n <= Z.max 0 ((left * 2 ^ (mxa - len) - syms)
                           / (2 ^ (mxa - len) - 1) - use + 1) ->
    (memL, remL) = chain_codes (Z.to_nat use) (2 ^ (len - rt)) mem0 rem0 ->
    0 <= acc <= lg ->
    0 <= lg ->
    MINV mxa rt B dn lg (len + 1) ->
    lg <= fst (eloopF f mxa rt syms left len (2 ^ (len - rt))
                 n use memL remL (lg, dn))
    /\ MINV mxa rt B
         (snd (eloopF f mxa rt syms left len (2 ^ (len - rt))
                 n use memL remL (lg, dn)))
         (fst (eloopF f mxa rt syms left len (2 ^ (len - rt))
                 n use memL remL (lg, dn))) (len + 1)
    /\ (forall s l L m r, dom5 s l L m r -> L <= len ->
          PM.find (key5 s l L m r)
            (snd (eloopF f mxa rt syms left len (2 ^ (len - rt))
                    n use memL remL (lg, dn)))
          = PM.find (key5 s l L m r) dn)
    /\ dpm_loop
         (fun u m r => dp_max f mxa rt (syms - u) (2 * (left - u))
                         (len + 1)
                         (m + (if r =? 0 then 0 else 2 ^ (len - rt)))
                         (2 * r))
         (2 ^ (len - rt)) n use memL remL acc
       <= fst (eloopF f mxa rt syms left len (2 ^ (len - rt))
                 n use memL remL (lg, dn)).
Proof.
  intros f rt mxa B syms left len mem0 rem0
         Hrt Hmx HB Hlink Hs Hl Hlen Hm0 Hr0 HIH.
  induction n as [|n IHn]; intros use memL remL lg dn acc
    Huse Hwin Hcomp Hacc Hlg HM.
  - cbn [eloopF dpm_loop fst snd].
    split; [clear; lia|].
    split; [exact HM|].
    split; [intros; reflexivity|].
    clear -Hacc; lia.
  - assert (HSB1 : 1 <= 2 ^ (len - rt)).
    { pose proof (Z.pow_pos_nonneg 2 (len - rt)
                    ltac:(clear; lia) ltac:(clear -Hlen; lia)) as H.
      clear -H; lia. }
    assert (Husemost : use <= (left * 2 ^ (mxa - len) - syms)
                              / (2 ^ (mxa - len) - 1)).
    { clear -Hwin. lia. }
    assert (Hmostl : (left * 2 ^ (mxa - len) - syms)
                     / (2 ^ (mxa - len) - 1) <= left)
      by (apply most_le_left; [exact Hl | clear -Hlen; lia]).
    (* the composite's caps *)
    assert (HmemL : 0 <= memL /\ memL <= mem0 + use + 2 ^ (len - rt)).
    { pose proof (chain_codes_mem_mono (Z.to_nat use) (2 ^ (len - rt))
                    mem0 rem0 ltac:(clear -HSB1; lia)) as Hlo.
      pose proof (chain_codes_mem_cap (Z.to_nat use) (2 ^ (len - rt))
                    mem0 rem0 HSB1 Hr0) as Hhi.
      rewrite <- Hcomp in Hlo, Hhi. cbn [fst] in Hlo, Hhi.
      rewrite Z2Nat.id in Hhi by (clear -Huse; lia).
      clear -Hlo Hhi Hm0; lia. }
    assert (HremL : 0 <= remL <= 2 ^ (len - rt)).
    { pose proof (chain_codes_rem_cap (Z.to_nat use) (2 ^ (len - rt))
                    mem0 rem0 HSB1 Hr0) as H.
      rewrite <- Hcomp in H. cbn [snd] in H.
      exact H. }
    (* the child's arguments *)
    set (syms' := syms - use).
    set (left' := 2 * (left - use)).
    set (mem' := memL + (if remL =? 0 then 0 else 2 ^ (len - rt))).
    set (rem' := 2 * remL).
    assert (Hchild : DOMS rt mxa syms' left' (len + 1) mem' rem').
    { unfold DOMS, syms', left', mem', rem'.
      assert (Hp21 : (2:Z) ^ 22 = 4194304) by (vm_compute; reflexivity).
      assert (Hp20 : (2:Z) ^ 21 = 2097152) by (vm_compute; reflexivity).
      assert (Hp15 : (2:Z) ^ 15 = 32768) by (vm_compute; reflexivity).
      assert (Hsub14 : 2 ^ (len - rt) <= 2 ^ 14)
        by (apply Z.pow_le_mono_r; [clear; lia | clear -Hlen Hrt Hmx; lia]).
      assert (Hp14 : (2:Z) ^ 14 = 16384) by (vm_compute; reflexivity).
      assert (Hpow1 : 2 ^ (len + 1 - rt) = 2 * 2 ^ (len - rt)).
      { rewrite <- Z.pow_succ_r by (clear -Hlen; lia).
        f_equal. clear; lia. }
      split; [clear -Hs Huse Husemost Hmostl Hl; lia|].
      split; [pose proof (least_child syms left use Huse);
              clear -H Huse Husemost Hmostl Hl; lia|].
      split; [clear -Hlen; lia|].
      split.
      { destruct (Z.le_gt_cases (len + 1) (mxa - 1)) as [Hle|Hgt];
          [left; exact Hle | right].
        assert (Hleq : len = mxa - 1) by (clear -Hgt Hlen; lia).
        pose proof (window_forcing mxa syms left Hl) as HWF.
        cbv zeta in HWF.
        rewrite <- Hleq in HWF.
        destruct HWF as [(Hneg & HN0) | (Hpos & Hlm & Hcm)].
        - exfalso.
          rewrite Z.max_l in Huse by (clear -Hneg; lia).
          rewrite Z.max_l in HN0 by (clear -Hneg; lia).
          clear -Hwin Hneg Huse Husemost HN0; lia.
        - rewrite Z.max_r in Huse by (clear -Hpos; lia).
          assert (Hue : use = 2 * left - syms)
            by (clear -Huse Husemost Hlm Hpos; lia).
          rewrite Z.max_r in Hcm, Hlm by (clear -Hpos; lia).
          clear -Hue Hcm; lia. }
      split.
      { split; [destruct (remL =? 0); clear -HmemL HSB1; lia|].
        destruct (remL =? 0);
          clear -HmemL Hm0 Hs Huse Husemost Hmostl Hl Hsub14 Hp14 Hp20
                 Hp21; lia. }
      split; [destruct HremL as [Hr1 _]; clear -Hr1; lia|].
      rewrite Hpow1. clear -HremL; lia. }
    assert (Hlink' : Z.of_nat f = B - (len + 1)) by (clear -Hlink; lia).
    cbn [eloopF dpm_loop].
    fold syms' left'.
    replace (memL + (if remL =? 0 then 0 else 2 ^ (len - rt)))
      with mem' by reflexivity.
    replace (2 * remL) with rem' by reflexivity.
    destruct (examineF f mxa rt syms' left' (len + 1) mem' rem' (lg, dn))
      as [lgc dnc] eqn:HEc.
    pose proof (HIH syms' left' (len + 1) mem' rem' lg dn
                  Hlink' Hchild Hlg HM) as (Hga & HMc & HFRc & Hdpc).
    rewrite HEc in Hga, HMc, HFRc, Hdpc.
    cbn [fst snd] in Hga, HMc, HFRc, Hdpc.
    (* the loop's own chain step *)
    change (if remL =? 0 then (memL + 2 ^ (len - rt), 2 ^ (len - rt) - 1)
            else (memL, remL - 1))
      with (chain_code (2 ^ (len - rt)) memL remL).
    destruct (chain_code (2 ^ (len - rt)) memL remL) as [memN remN] eqn:HCC.
    assert (HcompN : (memN, remN)
                     = chain_codes (Z.to_nat (use + 1)) (2 ^ (len - rt))
                         mem0 rem0).
    { replace (Z.to_nat (use + 1)) with (Z.to_nat use + 1)%nat
        by (clear -Huse; lia).
      rewrite chain_codes_compose.
      rewrite <- Hcomp.
      cbn [fst snd chain_codes].
      rewrite HCC.
      reflexivity. }
    pose proof (IHn (use + 1) memN remN lgc dnc
                  (Z.max acc
                     (dp_max f mxa rt syms' left' (len + 1) mem' rem'))
                  ltac:(clear -Huse; lia)
                  ltac:(clear -Hwin; lia)
                  HcompN
                  ltac:(split; [clear -Hacc; lia|];
                        apply Z.max_lub;
                        [clear -Hacc Hga; lia | exact Hdpc])
                  ltac:(clear -Hlg Hga; lia)
                  HMc) as (Hga2 & HM2 & HFR2 & Hdp2).
    split; [clear -Hga Hga2; lia|].
    split; [exact HM2|].
    split.
    { intros s l L m r Hd HL.
      rewrite (HFR2 s l L m r Hd HL).
      apply (HFRc s l L m r Hd).
      clear -HL; lia. }
    exact Hdp2.
Qed.

Theorem examine_sound : forall (f : nat) (rt mxa B : Z),
  1 <= rt -> rt <= mxa <= 15 -> B <= 34 ->
  EXS f rt mxa B.
Proof.
  induction f as [|f IH]; intros rt mxa B Hrt Hmx HB;
    unfold EXS; intros syms left len mem rem large done
                       Hlink Hdoms Hlg HM.
  - cbn [examineF dp_max fst snd].
    split; [clear; lia|].
    split; [exact HM|].
    split; [intros; reflexivity|].
    exact Hlg.
  - pose proof Hdoms as Hdoms2.
    destruct Hdoms2 as (Hs & Hl & Hlen & Hor & Hm & Hr).
    assert (Hd5 : dom5 syms left len mem rem)
      by (apply (doms_dom5 rt mxa);
          [exact Hrt | clear -Hmx; lia | exact Hdoms]).
    destruct (Z.eqb_spec syms left) as [Heq | Hne].
    + (* complete node *)
      cbn [examineF dp_max].
      destruct (Z.eqb_spec syms left) as [_|Habs];
        [| exfalso; exact (Habs Heq)].
      destruct (drain (Z.to_nat left + 2) (2 ^ (len - rt)) left mem rem)
        as [[u1 m1] r1] eqn:Hd.
      cbn [fst snd].
      split; [pose proof (Z.le_max_l large m1) as H; clear -H; lia|].
      split.
      { apply (minv_mono mxa rt B done large (Z.max large m1) len len);
          [pose proof (Z.le_max_l large m1) as H; clear -H; lia
           | clear; lia | exact HM]. }
      split; [intros; reflexivity|].
      pose proof (Z.le_max_r large m1) as H. clear -H; lia.
    + assert (Hlen1 : len <= mxa - 1)
        by (destruct Hor as [Ho|Ho]; [exact Ho | exfalso; exact (Hne Ho)]).
      assert (Hneb : (syms =? left) = false) by (apply Z.eqb_neq; exact Hne).
      destruct (PM.find (key5 syms left len mem rem) done)
        as [[]|] eqn:HF.
      * (* memo hit *)
        assert (HEeq : examineF (S f) mxa rt syms left len mem rem
                         (large, done) = (large, done)).
        { cbn [examineF]. rewrite Hneb, HF. reflexivity. }
        rewrite HEeq.
        cbn [fst snd].
        split; [clear; lia|].
        split; [exact HM|].
        split; [intros; reflexivity|].
        pose proof (HM syms left len mem rem Hd5 ltac:(clear; lia) HF)
          as Hdp.
        replace (Z.to_nat (B - len)) with (S f) in Hdp
          by (clear -Hlink; lia).
        exact Hdp.
      * (* fresh node *)
        rewrite (examineF_fresh_eq f mxa rt syms left len mem rem
                   large done Hneb HF).
        cbn [dp_max].
        destruct (Z.eqb_spec syms left) as [Habs|_];
          [exfalso; exact (Hne Habs)|].
        unfold dpm_least, dpm_most.
        destruct (drain (Z.to_nat (Z.max 0 (2 * left - syms)) + 2)
                    (2 ^ (len - rt)) (Z.max 0 (2 * left - syms)) mem rem)
          as [[u1 m1] r1] eqn:Hd.
        assert (HSB1 : 1 <= 2 ^ (len - rt)).
        { pose proof (Z.pow_pos_nonneg 2 (len - rt)
                        ltac:(clear; lia) ltac:(clear -Hlen; lia)) as H.
          clear -H; lia. }
        pose proof (drain_chain (2 ^ (len - rt))
                      (Z.max 0 (2 * left - syms)) mem rem
                      ltac:(clear -HSB1; lia)
                      ltac:(clear -Hr; lia)
                      ltac:(clear; lia)) as HDC.
        rewrite Hd in HDC. cbn [fst snd] in HDC.
        assert (Hcomp0 : (m1, r1 - u1)
                         = chain_codes (Z.to_nat (Z.max 0 (2 * left - syms)))
                             (2 ^ (len - rt)) mem rem)
          by (rewrite HDC; reflexivity).
        assert (HM1 : MINV mxa rt B
                        (PM.add (key5 syms left len mem rem) tt done)
                        large (len + 1))
          by (apply (minv_addself mxa rt B done large len
                       syms left len mem rem Hd5 eq_refl HM)).
        pose proof (eloop_sound f rt mxa B syms left len mem rem
                      Hrt Hmx HB Hlink Hs Hl
                      ltac:(clear -Hlen Hlen1; lia) Hm Hr
                      (IH rt mxa B Hrt Hmx HB)
                      (Z.to_nat ((left * 2 ^ (mxa - len) - syms)
                                 / (2 ^ (mxa - len) - 1)
                                 - Z.max 0 (2 * left - syms) + 1))
                      (Z.max 0 (2 * left - syms)) m1 (r1 - u1) large
                      (PM.add (key5 syms left len mem rem) tt done) 0
                      ltac:(clear; lia)
                      ltac:(clear; lia)
                      Hcomp0
                      ltac:(clear -Hlg; lia)
                      Hlg HM1) as (Hga & HMc & HFRc & Hdpc).
        split; [exact Hga|].
        split.
        { (* restore the invariant at len *)
          intros s l L m r Hd6 HL Hf2.
          destruct (Z.le_gt_cases (len + 1) L) as [HLc|HLe].
          - exact (HMc s l L m r Hd6 HLc Hf2).
          - assert (HLl : L = len) by (clear -HL HLe; lia).
            rewrite (HFRc s l L m r Hd6 ltac:(clear -HLl; lia)) in Hf2.
            destruct (PM.E.eq_dec (key5 s l L m r)
                        (key5 syms left len mem rem)) as [He|Hne2].
            + pose proof (key5_inj s l L m r syms left len mem rem
                            Hd6 Hd5 He) as (-> & -> & -> & -> & ->).
              replace (Z.to_nat (B - len)) with (S f)
                by (clear -Hlink; lia).
              cbn [dp_max].
              destruct (Z.eqb_spec syms left) as [Habs2|_];
                [exfalso; exact (Hne Habs2)|].
              unfold dpm_least, dpm_most.
              rewrite Hd.
              exact Hdpc.
            + rewrite PM.gso in Hf2 by exact Hne2.
              eapply Z.le_trans;
                [apply (HM s l L m r Hd6 ltac:(clear -HLl; lia) Hf2)
                 | exact Hga].
        }
        split.
        { (* the strict frame *)
          intros s l L m r Hd6 HL.
          rewrite (HFRc s l L m r Hd6 ltac:(clear -HL; lia)).
          apply PM.gso.
          intro He.
          pose proof (key5_inj s l L m r syms left len mem rem
                        Hd6 Hd5 He) as (_ & _ & HLe & _).
          clear -HL HLe; lia. }
        exact Hdpc.
Qed.
