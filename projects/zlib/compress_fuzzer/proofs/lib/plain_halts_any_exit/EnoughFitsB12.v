(** * EnoughFitsB12 — session 8 (S2, part 2): the phase covers every
    gated seed.

    enough_phase's two loops, reified; any run only grows the max and
    preserves the seed-level memo invariant (every call is an
    examine_sound instance); and the run SPLITS at the target cell
    (n0, left0) — the inner loop steps left BY 2 from 2, so kleft's
    evenness is the coverage fact (finding f-d's corollary). *)

From Stdlib Require Import ZArith List Lia Bool FMapPositive.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsA12 EnoughFitsB1
  EnoughFitsB2 EnoughFitsB4 EnoughFitsB8 EnoughFitsB11.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The phase loops, reified.
   ========================================================================== *)

Fixpoint einF (efuel : nat) (mx rt : Z) (numm : PM.t Z) (n : Z)
              (j : nat) (left : Z) (st : Z * PM.t unit) : Z * PM.t unit :=
  match j with
  | O => st
  | S j' =>
      let st1 :=
        if (rt + 1 <? mx) && memo_nonzero numm (key3 n left (rt + 1))
        then examineF efuel mx rt n left (rt + 1) (2 ^ rt) 0 st
        else st in
      let st2 :=
        if memo_nonzero numm (key3 n left rt) && (n <=? 2 * left)
        then examineF efuel mx rt (2 * (n - left)) (2 * (n - left))
                      (rt + 1) (2 ^ rt) 0 st1
        else st1 in
      einF efuel mx rt numm n j' (left + 2) st2
  end.

Fixpoint eoutF (efuel : nat) (mx rt : Z) (numm : PM.t Z)
               (i : nat) (n : Z) (st : Z * PM.t unit) : Z * PM.t unit :=
  match i with
  | O => st
  | S i' =>
      let st' := einF efuel mx rt numm n (Z.to_nat ((n - 1) / 2)) 2 st in
      eoutF efuel mx rt numm i' (n + 1) st'
  end.

Lemma enough_phase_eq : forall mx rt syms numm,
  rt < mx ->
  enough_phase mx rt syms numm
  = fst (eoutF (Z.to_nat mx + 1) mx rt numm (Z.to_nat (syms - 2)) 3
          (2 ^ rt, PM.empty unit)).
Proof.
  intros mx rt syms numm Hlt.
  unfold enough_phase.
  destruct (Z.ltb_spec rt mx) as [_|Habs];
    [| exfalso; clear -Hlt Habs; lia].
  f_equal.
  generalize (2 ^ rt, PM.empty unit) as st.
  generalize 3 as n0.
  generalize (Z.to_nat (syms - 2)) as i.
  intros i.
  induction i as [|i IHo]; intros n0 st.
  - reflexivity.
  - cbn [eoutF].
    cbv beta iota.
    match goal with
    | |- context [?F (Z.to_nat ((n0 - 1) / 2)) 2 st] =>
        assert (HIN : forall (j : nat) (l1 : Z) (s1 : Z * PM.t unit),
                   F j l1 s1
                   = einF (Z.to_nat mx + 1) mx rt numm n0 j l1 s1)
    end.
    { intro j; induction j as [|j IHj]; intros l1 s1.
      - reflexivity.
      - cbn [einF]. cbv beta iota. apply IHj. }
    rewrite HIN.
    apply (IHo (n0 + 1)).
Qed.

(* ==========================================================================
   2.  Every call only grows the max and preserves the invariant.
   ========================================================================== *)

Section Phase.
  Variable mx rt B : Z.
  Variable numm : PM.t Z.
  Hypothesis Hrt : 1 <= rt.
  Hypothesis Hmx : rt <= mx <= 15.
  Hypothesis HB : B = mx + rt + 2.
  Hypothesis Hlt : rt + 1 <= mx - 1.

  Let efuel : nat := (Z.to_nat mx + 1)%nat.

  Lemma efuel_link : Z.of_nat efuel = B - (rt + 1).
  Proof.
    unfold efuel.
    rewrite Nat2Z.inj_add, Z2Nat.id by (clear -Hmx Hrt; lia).
    clear -HB; lia.
  Qed.

  Lemma seed_doms1 : forall n left,
    0 <= n <= 2 ^ 21 -> 0 <= left <= n ->
    DOMS rt mx n left (rt + 1) (2 ^ rt) 0.
  Proof.
    intros n left Hn Hl.
    unfold DOMS.
    assert (H15 : (2:Z) ^ 15 = 32768) by (vm_compute; reflexivity).
    assert (Hprt : 2 ^ rt <= 2 ^ 15)
      by (apply Z.pow_le_mono_r; clear -Hrt Hmx Hlt; lia).
    assert (Hprt0 : 0 < 2 ^ rt)
      by (apply Z.pow_pos_nonneg; clear -Hrt; lia).
    assert (Hp22 : 0 <= (rt + 1) * 2 ^ 22)
      by (apply Z.mul_nonneg_nonneg;
          [clear -Hrt; lia | vm_compute; clear; discriminate]).
    assert (Hsub0 : 0 <= 2 ^ (rt + 1 - rt))
      by (apply Z.pow_nonneg; clear; lia).
    split; [exact Hn|].
    split; [exact Hl|].
    split; [clear -Hlt Hmx; lia|].
    split; [left; clear -Hlt; lia|].
    split; [clear -Hprt Hprt0 H15 Hp22; lia|].
    split; [clear; lia | exact Hsub0].
  Qed.

  Lemma seed_doms2 : forall q,
    0 <= q <= 2 ^ 21 ->
    DOMS rt mx q q (rt + 1) (2 ^ rt) 0.
  Proof.
    intros q Hq.
    unfold DOMS.
    assert (H15 : (2:Z) ^ 15 = 32768) by (vm_compute; reflexivity).
    assert (Hprt : 2 ^ rt <= 2 ^ 15)
      by (apply Z.pow_le_mono_r; clear -Hrt Hmx Hlt; lia).
    assert (Hprt0 : 0 < 2 ^ rt)
      by (apply Z.pow_pos_nonneg; clear -Hrt; lia).
    assert (Hp22 : 0 <= (rt + 1) * 2 ^ 22)
      by (apply Z.mul_nonneg_nonneg;
          [clear -Hrt; lia | vm_compute; clear; discriminate]).
    assert (Hsub0 : 0 <= 2 ^ (rt + 1 - rt))
      by (apply Z.pow_nonneg; clear; lia).
    split; [exact Hq|].
    split; [clear -Hq; lia|].
    split; [clear -Hlt Hmx; lia|].
    split; [right; reflexivity|].
    split; [clear -Hprt Hprt0 H15 Hp22; lia|].
    split; [clear; lia | exact Hsub0].
  Qed.

  Definition PHINV (st : Z * PM.t unit) : Prop :=
    0 <= fst st /\ MINV mx rt B (snd st) (fst st) (rt + 1).

  (** One gated call: grows, preserves, and covers its own seed. *)
  Lemma call_step : forall n left st,
    0 <= n <= 2 ^ 21 -> 0 <= left <= n ->
    PHINV st ->
    fst st <= fst (examineF efuel mx rt n left (rt + 1) (2 ^ rt) 0 st)
    /\ PHINV (examineF efuel mx rt n left (rt + 1) (2 ^ rt) 0 st)
    /\ dp_max efuel mx rt n left (rt + 1) (2 ^ rt) 0
       <= fst (examineF efuel mx rt n left (rt + 1) (2 ^ rt) 0 st).
  Proof.
    intros n left st Hn Hl [Hg HM].
    destruct st as [lg dn].
    cbn [fst snd] in Hg, HM.
    pose proof (examine_sound efuel rt mx B Hrt Hmx
                  ltac:(clear -HB Hmx Hrt; lia)
                  n left (rt + 1) (2 ^ rt) 0 lg dn
                  efuel_link (seed_doms1 n left Hn Hl) Hg HM)
      as (Hga & HMc & _ & Hdp).
    split; [exact Hga|].
    split; [| exact Hdp].
    split; [clear -Hg Hga; lia | exact HMc].
  Qed.

  Lemma call_step2 : forall q st,
    0 <= q <= 2 ^ 21 ->
    PHINV st ->
    fst st <= fst (examineF efuel mx rt q q (rt + 1) (2 ^ rt) 0 st)
    /\ PHINV (examineF efuel mx rt q q (rt + 1) (2 ^ rt) 0 st).
  Proof.
    intros q st Hq [Hg HM].
    destruct st as [lg dn].
    cbn [fst snd] in Hg, HM.
    pose proof (examine_sound efuel rt mx B Hrt Hmx
                  ltac:(clear -HB Hmx Hrt; lia)
                  q q (rt + 1) (2 ^ rt) 0 lg dn
                  efuel_link (seed_doms2 q Hq) Hg HM)
      as (Hga & HMc & _ & _).
    split; [exact Hga|].
    split; [clear -Hg Hga; lia | exact HMc].
  Qed.

  (** One inner iteration (both gated branches). *)
  Lemma ein_body : forall n left st,
    3 <= n <= 2 ^ 20 -> 0 <= left <= n ->
    PHINV st ->
    let st1 := if (rt + 1 <? mx) && memo_nonzero numm (key3 n left (rt + 1))
               then examineF efuel mx rt n left (rt + 1) (2 ^ rt) 0 st
               else st in
    let st2 := if memo_nonzero numm (key3 n left rt) && (n <=? 2 * left)
               then examineF efuel mx rt (2 * (n - left)) (2 * (n - left))
                             (rt + 1) (2 ^ rt) 0 st1
               else st1 in
    fst st <= fst st2 /\ PHINV st2.
  Proof.
    intros n left st Hn Hl HP.
    cbv zeta.
    assert (H2021 : (2:Z) ^ 20 <= 2 ^ 21)
      by (apply Z.pow_le_mono_r; clear; lia).
    set (st1 := if (rt + 1 <? mx) && memo_nonzero numm (key3 n left (rt + 1))
                then examineF efuel mx rt n left (rt + 1) (2 ^ rt) 0 st
                else st).
    assert (H1 : fst st <= fst st1 /\ PHINV st1).
    { unfold st1.
      destruct ((rt + 1 <? mx) && memo_nonzero numm (key3 n left (rt + 1))).
      - pose proof (call_step n left st
                      ltac:(clear -Hn H2021; lia) Hl HP) as (Ha & Hb & _).
        split; [exact Ha | exact Hb].
      - split; [clear; lia | exact HP]. }
    destruct H1 as [Ha1 HP1].
    destruct (memo_nonzero numm (key3 n left rt) && (n <=? 2 * left)).
    - pose proof (call_step2 (2 * (n - left)) st1
                    ltac:(clear -Hn Hl H2021; lia) HP1) as (Ha2 & HP2).
      split; [clear -Ha1 Ha2; lia | exact HP2].
    - split; [exact Ha1 | exact HP1].
  Qed.

  (** The inner loop grows and preserves. *)
  Lemma ein_mono : forall j n left st,
    3 <= n <= 2 ^ 20 -> 0 <= left ->
    left + 2 * Z.of_nat j <= n + 1 ->
    PHINV st ->
    fst st <= fst (einF efuel mx rt numm n j left st)
    /\ PHINV (einF efuel mx rt numm n j left st).
  Proof.
    induction j as [|j IH]; intros n left st Hn Hl Hcap HP.
    - cbn [einF]. split; [clear; lia | exact HP].
    - cbn [einF]. cbv zeta.
      pose proof (ein_body n left st Hn
                    ltac:(clear -Hl Hcap Hn; lia) HP) as HB2.
      cbv zeta in HB2.
      destruct HB2 as [Ha HP2].
      pose proof (IH n (left + 2) _
                    Hn ltac:(clear -Hl; lia)
                    ltac:(clear -Hcap; lia) HP2) as [Ha2 HP3].
      split; [clear -Ha Ha2; lia | exact HP3].
  Qed.

  (** The inner loop covers the target cell. *)
  Lemma ein_covers : forall j n left0 target st,
    3 <= n <= 2 ^ 20 -> 0 <= left0 ->
    left0 + 2 * Z.of_nat j <= n + 1 ->
    0 <= target - left0 ->
    Z.even (target - left0) = true ->
    target - left0 < 2 * Z.of_nat j ->
    target < n ->
    2 <= target ->
    rt + 1 < mx ->
    memo_nonzero numm (key3 n target (rt + 1)) = true ->
    PHINV st ->
    dp_max efuel mx rt n target (rt + 1) (2 ^ rt) 0
    <= fst (einF efuel mx rt numm n j left0 st).
  Proof.
    induction j as [|j IH]; intros n left0 target st Hn Hl0 Hcap Hd
      Hev Hlt2 Htn Ht2 Hrtmx Hgate HP.
    - exfalso. clear -Hlt2 Hd; cbn in Hlt2; lia.
    - cbn [einF]. cbv zeta.
      destruct (Z.eq_dec target left0) as [-> | Hne].
      + (* the target cell: the st1 branch fires *)
        assert (Hg1 : ((rt + 1 <? mx)
                       && memo_nonzero numm (key3 n left0 (rt + 1)))%bool
                      = true).
        { rewrite Hgate.
          destruct (Z.ltb_spec (rt + 1) mx) as [_|Habs];
            [reflexivity | exfalso; clear -Habs Hrtmx; lia]. }
        rewrite Hg1.
        pose proof (call_step n left0 st
                      ltac:(assert ((2:Z)^20 <= 2^21)
                              by (apply Z.pow_le_mono_r; clear; lia);
                            clear -Hn H Ht2; lia)
                      ltac:(clear -Ht2 Htn; lia) HP)
          as (Ha & HP1 & Hdp).
        set (st1 := examineF efuel mx rt n left0 (rt + 1) (2 ^ rt) 0 st)
          in *.
        (* the rest only grows *)
        assert (Hrest : fst st1
                        <= fst (einF efuel mx rt numm n j (left0 + 2)
                                  (if memo_nonzero numm (key3 n left0 rt)
                                      && (n <=? 2 * left0)
                                   then examineF efuel mx rt
                                          (2 * (n - left0))
                                          (2 * (n - left0))
                                          (rt + 1) (2 ^ rt) 0 st1
                                   else st1))
                        /\ True).
        { assert (H2021 : (2:Z) ^ 20 <= 2 ^ 21)
            by (apply Z.pow_le_mono_r; clear; lia).
          set (st2 := if memo_nonzero numm (key3 n left0 rt)
                         && (n <=? 2 * left0)
                      then examineF efuel mx rt (2 * (n - left0))
                             (2 * (n - left0)) (rt + 1) (2 ^ rt) 0 st1
                      else st1).
          assert (H2 : fst st1 <= fst st2 /\ PHINV st2).
          { unfold st2.
            destruct (memo_nonzero numm (key3 n left0 rt)
                        && (n <=? 2 * left0)).
            - pose proof (call_step2 (2 * (n - left0)) st1
                            ltac:(clear -Hn Htn Ht2 H2021; lia) HP1)
                as (Hb & HPb).
              split; [exact Hb | exact HPb].
            - split; [clear; lia | exact HP1]. }
          destruct H2 as [Hb HPb].
          pose proof (ein_mono j n (left0 + 2) st2 Hn
                        ltac:(clear -Ht2; lia)
                        ltac:(clear -Hcap; lia) HPb) as [Hc _].
          split; [clear -Hb Hc; lia | exact I]. }
        destruct Hrest as [Hrest _].
        clear -Hdp Hrest; lia.
      + (* not yet: step and recurse *)
        pose proof (ein_body n left0 st Hn
                      ltac:(clear -Hl0 Hcap Hn; lia) HP) as HB2.
        cbv zeta in HB2.
        destruct HB2 as [_ HP2].
        apply (IH n (left0 + 2) target _ Hn
                 ltac:(clear -Hl0; lia)
                 ltac:(clear -Hcap; lia)
                 ltac:(assert (target - left0 <> 0)
                         by (clear -Hne; lia);
                       assert (target - left0 <> 1)
                         by (intro He;
                             rewrite He in Hev; vm_compute in Hev;
                             discriminate Hev);
                       clear -Hd H H0; lia)
                 ltac:(replace (target - (left0 + 2))
                         with (target - left0 - 2) by (clear; lia);
                       rewrite Z.even_sub;
                       rewrite Hev; vm_compute; reflexivity)
                 ltac:(clear -Hlt2; lia)
                 Htn Ht2 Hrtmx Hgate HP2).
  Qed.

  (** The outer loop: growth and the split at the target row. *)
  Lemma eout_mono : forall i n st,
    3 <= n -> n + Z.of_nat i <= 2 ^ 20 + 1 ->
    PHINV st ->
    fst st <= fst (eoutF efuel mx rt numm i n st)
    /\ PHINV (eoutF efuel mx rt numm i n st).
  Proof.
    induction i as [|i IH]; intros n st Hn Hcap HP.
    - cbn [eoutF]. split; [clear; lia | exact HP].
    - cbn [eoutF]. cbv zeta.
      assert (Hjcap : 2 + 2 * Z.of_nat (Z.to_nat ((n - 1) / 2)) <= n + 1).
      { rewrite Z2Nat.id by (apply Z.div_pos; clear -Hn; lia).
        pose proof (Z.mul_div_le (n - 1) 2 ltac:(clear; lia)) as H.
        clear -H Hn; lia. }
      pose proof (ein_mono (Z.to_nat ((n - 1) / 2)) n 2 st
                    ltac:(clear -Hn Hcap; lia) ltac:(clear; lia)
                    Hjcap HP) as [Ha HP1].
      pose proof (IH (n + 1) _ ltac:(clear -Hn; lia)
                    ltac:(clear -Hcap; lia) HP1) as [Hb HP2].
      split; [clear -Ha Hb; lia | exact HP2].
  Qed.

  Lemma eout_covers : forall i n0 ntarget ltarget st,
    3 <= n0 -> n0 + Z.of_nat i <= 2 ^ 20 + 1 ->
    n0 <= ntarget -> ntarget < n0 + Z.of_nat i ->
    ntarget <= 2 ^ 20 ->
    2 <= ltarget < ntarget ->
    Z.even ltarget = true ->
    rt + 1 < mx ->
    memo_nonzero numm (key3 ntarget ltarget (rt + 1)) = true ->
    PHINV st ->
    dp_max efuel mx rt ntarget ltarget (rt + 1) (2 ^ rt) 0
    <= fst (eoutF efuel mx rt numm i n0 st).
  Proof.
    induction i as [|i IH]; intros n0 ntarget ltarget st Hn0 Hcap Hlo Hhi
      Hnt Hlt' Hev Hrtmx Hgate HP.
    - exfalso. clear -Hlo Hhi; cbn in Hhi; lia.
    - cbn [eoutF]. cbv zeta.
      destruct (Z.eq_dec ntarget n0) as [-> | Hne].
      + (* the target row *)
        assert (Hjcap : 2 + 2 * Z.of_nat (Z.to_nat ((n0 - 1) / 2))
                        <= n0 + 1).
        { rewrite Z2Nat.id by (apply Z.div_pos; clear -Hn0; lia).
          pose proof (Z.mul_div_le (n0 - 1) 2 ltac:(clear; lia)) as H.
          clear -H Hn0; lia. }
        assert (Hcov := ein_covers (Z.to_nat ((n0 - 1) / 2)) n0 2 ltarget st
                          ltac:(clear -Hn0 Hnt; lia) ltac:(clear; lia)
                          Hjcap
                          ltac:(clear -Hlt'; lia)
                          ltac:(rewrite Z.even_sub;
                                rewrite Hev; vm_compute; reflexivity)
                          ltac:(rewrite Z2Nat.id
                                  by (apply Z.div_pos; clear -Hn0; lia);
                                pose proof (Z.mul_succ_div_gt (n0 - 1) 2
                                              ltac:(clear; lia)) as H;
                                clear -H Hlt'; lia)
                          ltac:(clear -Hlt'; lia)
                          ltac:(clear -Hlt'; lia)
                          Hrtmx Hgate HP).
        pose proof (ein_mono (Z.to_nat ((n0 - 1) / 2)) n0 2 st
                      ltac:(clear -Hn0 Hnt; lia) ltac:(clear; lia)
                      Hjcap HP) as [_ HP1].
        pose proof (eout_mono i (n0 + 1) _ ltac:(clear -Hn0; lia)
                      ltac:(clear -Hcap; lia) HP1) as [Hb _].
        clear -Hcov Hb; lia.
      + assert (Hjcap : 2 + 2 * Z.of_nat (Z.to_nat ((n0 - 1) / 2))
                        <= n0 + 1).
        { rewrite Z2Nat.id by (apply Z.div_pos; clear -Hn0; lia).
          pose proof (Z.mul_div_le (n0 - 1) 2 ltac:(clear; lia)) as H.
          clear -H Hn0; lia. }
        pose proof (ein_mono (Z.to_nat ((n0 - 1) / 2)) n0 2 st
                      ltac:(clear -Hn0 Hcap; lia) ltac:(clear; lia)
                      Hjcap HP) as [_ HP1].
        apply (IH (n0 + 1) ntarget ltarget _ ltac:(clear -Hn0; lia)
                 ltac:(clear -Hcap; lia) ltac:(clear -Hlo Hne; lia)
                 ltac:(clear -Hhi; lia) Hnt Hlt' Hev Hrtmx Hgate HP1).
  Qed.

  (** THE COVERAGE: the phase's max dominates the target seed's
      dp_max. *)
  Lemma phase_covers : forall syms ntarget ltarget,
    3 <= ntarget <= syms -> syms <= 2 ^ 20 ->
    2 <= ltarget < ntarget ->
    Z.even ltarget = true ->
    rt + 1 < mx ->
    memo_nonzero numm (key3 ntarget ltarget (rt + 1)) = true ->
    dp_max (S (Z.to_nat mx)) mx rt ntarget ltarget (rt + 1) (2 ^ rt) 0
    <= enough_phase mx rt syms numm.
  Proof.
    intros syms ntarget ltarget Hnt Hsy Hlt' Hev Hrtmx Hgate.
    rewrite enough_phase_eq by (clear -Hrtmx; lia).
    replace (S (Z.to_nat mx)) with efuel
      by (unfold efuel; clear; lia).
    apply (eout_covers (Z.to_nat (syms - 2)) 3 ntarget ltarget
             (2 ^ rt, PM.empty unit)
             ltac:(clear; lia)
             ltac:(rewrite Z2Nat.id by (clear -Hnt; lia);
                   clear -Hsy; lia)
             ltac:(clear -Hnt; lia)
             ltac:(rewrite Z2Nat.id by (clear -Hnt; lia);
                   clear -Hnt; lia)
             ltac:(clear -Hnt Hsy; lia)
             Hlt' Hev Hrtmx Hgate).
    split.
    - cbn [fst]. apply Z.pow_nonneg; clear; lia.
    - intros s l L m r Hd HL Hf.
      rewrite PM.gempty in Hf.
      discriminate Hf.
  Qed.

End Phase.
