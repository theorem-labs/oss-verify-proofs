(** * EnoughFitsB14 — session 8 finale: the oracle statement holds, and
    EnoughFits_capped is UNCONDITIONAL.

    seed_oracle_STMT = the run's plumbing (guards computed per band
    arm, the min-collapses by Hrootmx), the count phase's reachability
    witness (B13: the actual code's walk), and the table phase's
    coverage (B12: enumeration + examineF memo-soundness).  Then B10's
    fit turns it into seed_obligation, and B9's assembly closes
    EnoughFits_STMT at the landed Gap7Strict text. *)

From Stdlib Require Import ZArith List Lia Bool FMapPositive.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Inftrees ItGTblSortWin.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughDP.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import EnoughFitsDesign EnoughFitsA12 EnoughFitsB1
  EnoughFitsB2 EnoughFitsB4 EnoughFitsB8 EnoughFitsB9 EnoughFitsB10
  EnoughFitsB11 EnoughFitsB12 EnoughFitsB13.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Theorem seed_oracle_holds : seed_oracle_STMT.
Proof.
  unfold seed_oracle_STMT.
  intros ty l root0 c st large Hband Hcap Hpre Hroot Hge Hcell.
  set (cnt0 := sw_cnt (lens_of_list l) (Z.of_nat (length l))) in *.
  set (mx := x_max c) in *.
  pose proof (Hctx0 ty l root0 c st Hband Hcap Hpre Hroot) as Hctx.
  pose proof (Hcomp' ty l root0 c st Hband Hcap Hpre Hroot) as Hcomp.
  pose proof (Hcnt0nn' l) as Hnn.
  fold cnt0 in Hctx, Hcomp, Hnn.
  pose proof Hctx as Hctx2.
  destruct Hctx2 as (_ & _ & Hmx15 & Hmxnz & Hmxz & _).
  fold mx in Hmx15, Hmxnz, Hmxz, Hge.
  assert (Hmxpos : 1 <= cnt0 mx)
    by (pose proof (Hnn mx) as H; clear -Hmxnz H; lia).
  assert (HR0p : 1 <= root0)
    by (destruct (band_root ty l root0 Hband) as [->| ->]; clear; lia).
  (* the target cell's ranges *)
  set (n0 := rem_syms cnt0 (root0 + 1) mx).
  set (left0 := kleft cnt0 (root0 + 1)).
  assert (Hin : 1 <= root0 + 1 <= mx) by (clear -Hge HR0p; lia).
  assert (Hfloor : mx - (root0 + 1) + left0 <= n0)
    by (unfold n0, left0;
        apply (syms_floor cnt0 mx Hnn Hmx15 Hmxz Hmxpos Hcomp
                 (root0 + 1) Hin)).
  assert (Hl2 : 2 <= left0)
    by (unfold left0;
        apply (kleft_ge2 cnt0 mx Hnn Hmx15 Hmxz Hmxpos Hcomp
                 (root0 + 1) Hin)).
  assert (Hltn : left0 < n0) by (clear -Hfloor Hl2 Hge; lia).
  assert (Hn3 : 3 <= n0) by (clear -Hfloor Hl2 Hge; lia).
  assert (Hev : Z.even left0 = true) by (unfold left0; apply kleft_even).
  assert (Hncap : n0 <= Z.of_nat (length l)).
  { unfold n0, cnt0.
    apply rem_syms_le_codes.
    clear; lia. }
  assert (Hwcap : rem_syms cnt0 1 mx <= 2 ^ 20).
  { assert (H : rem_syms cnt0 1 mx <= Z.of_nat (length l))
      by (unfold cnt0; apply rem_syms_le_codes; clear; lia).
    pose proof (band_codes286 ty l root0 Hband) as Hc.
    assert ((286:Z) <= 2 ^ 20) by (vm_compute; clear; discriminate).
    clear -H Hc H0; lia. }
  (* the band's syms argument, with its facts kept CORRELATED *)
  set (SY := if ty =? CT_LENS then 286 else 30) in *.
  assert (Hpack : SY = 286 /\ root0 = 9 /\ n0 <= 286
                  \/ SY = 30 /\ root0 = 6 /\ n0 <= 30).
  { pose proof Hband as Hb2.
    destruct Hb2 as [(HtyE & Hlcap & Hr0E)|(HtyE & Hlcap & Hr0E)];
      [left|right]; unfold SY; rewrite HtyE.
    - change (CT_LENS =? CT_LENS) with true. cbv iota.
      split; [reflexivity|].
      split; [exact Hr0E | clear -Hncap Hlcap; lia].
    - change (CT_DISTS =? CT_LENS) with false. cbv iota.
      split; [reflexivity|].
      split; [exact Hr0E | clear -Hncap Hlcap; lia]. }
  assert (HnSY : n0 <= SY)
    by (destruct Hpack as [(HSYe & _ & H)|(HSYe & _ & H)];
        rewrite HSYe; clear -H; lia).
  (* open the run *)
  unfold enough_bound in Hcell.
  destruct (enough_run SY root0 mx) as [[total obound]|] eqn:HRUN;
    [| discriminate Hcell].
  destruct obound as [lg|]; [| discriminate Hcell].
  injection Hcell as <-.
  unfold enough_run in HRUN.
  assert (Hg1 : ((SY <? 2) || (root0 <? 1) || (mx <? 1))%bool = false).
  { destruct Hpack as [(HSYe & Hr0e & _)|(HSYe & Hr0e & _)];
      rewrite HSYe, Hr0e;
      destruct (Z.ltb_spec mx 1) as [Hb|_];
      try (exfalso; clear -Hb Hmx15; lia);
      reflexivity. }
  rewrite Hg1 in HRUN.
  cbv beta iota zeta in HRUN.
  assert (Hmin1 : Z.min mx (SY - 1) = mx).
  { apply Z.min_l.
    destruct Hpack as [(HSYe & _)|(HSYe & _)]; rewrite HSYe;
      clear -Hmx15; lia. }
  rewrite Hmin1 in HRUN.
  assert (Hg2 : (SY - 1 >? 2 ^ mx - 1) = false).
  { rewrite Z.gtb_ltb.
    apply Z.ltb_ge.
    assert (Hp : 2 ^ (root0 + 2) <= 2 ^ mx)
      by (apply Z.pow_le_mono_r; clear -Hge; lia).
    destruct Hpack as [(HSYe & He & _)|(HSYe & He & _)];
      rewrite HSYe; rewrite He in Hp.
    - replace (9 + 2) with 11 in Hp by (clear; lia).
      assert (Hv : (2:Z) ^ 11 = 2048) by (vm_compute; reflexivity).
      rewrite Hv in Hp. clear -Hp; lia.
    - replace (6 + 2) with 8 in Hp by (clear; lia).
      assert (Hv : (2:Z) ^ 8 = 256) by (vm_compute; reflexivity).
      rewrite Hv in Hp. clear -Hp; lia. }
  rewrite Hg2 in HRUN.
  assert (Hg3 : ((mx >? 32) || (root0 >? 32) || (SY >? 2 ^ 20))%bool
                = false).
  { destruct Hpack as [(HSYe & Hr0e & _)|(HSYe & Hr0e & _)];
      rewrite HSYe, Hr0e;
      rewrite !Z.gtb_ltb;
      destruct (Z.ltb_spec 32 mx) as [Ha|_];
      try (exfalso; clear -Ha Hmx15; lia);
      vm_compute; reflexivity. }
  rewrite Hg3 in HRUN.
  assert (Hmin2 : Z.min root0 mx = root0)
    by (apply Z.min_l; clear -Hge; lia).
  rewrite Hmin2 in HRUN.
  destruct ((fix cnt (i : nat) (n sum : Z) (memo : PM.t Z) {struct i}
               : Z * PM.t Z :=
               match i with
               | O => (sum, memo)
               | S i' =>
                   let '(got, memo') :=
                     countF (Z.to_nat mx + 1)%nat mx n 2 1 memo in
                   cnt i' (n + 1) (sum + got) memo'
               end) (Z.to_nat (SY - 1)) 2 0 (PM.empty Z))
    as [total' numm] eqn:HCNT.
  assert (Hg4 : (SY <? 2 ^ (root0 + 1)) = true).
  { destruct Hpack as [(HSYe & Hr0e & _)|(HSYe & Hr0e & _)];
      rewrite HSYe, Hr0e; vm_compute; reflexivity. }
  rewrite Hg4 in HRUN.
  injection HRUN as _ Hlg.
  (* the reach: the walk's top call lives in the fold *)
  assert (Hreach : exists v, PM.find (key3 n0 left0 (root0 + 1)) numm
                             = Some v /\ 1 <= v).
  { assert (Hw1 : wsyms cnt0 mx 1 = rem_syms cnt0 1 mx) by reflexivity.
    pose proof (cnt_fold_reach cnt0 mx root0 Hnn
                  ltac:(clear -Hmx15; lia) Hmxz Hmxpos Hcomp HR0p
                  ltac:(clear -Hge; lia) Hwcap
                  (Z.to_nat (SY - 1)) 2 (PM.empty Z) 0
                  ltac:(clear; lia)
                  ltac:(destruct Hpack as [(HSYe & _)|(HSYe & _)];
                        rewrite HSYe; vm_compute; clear;
                        intros H; discriminate H)
                  ltac:(unfold wsyms;
                        pose proof (syms_ge_left cnt0 mx Hnn Hmx15 Hmxz
                                      Hcomp 1 ltac:(clear -Hmx15; lia))
                          as H;
                        assert (Hk1 : kleft cnt0 1 = 2)
                          by (unfold kleft;
                              change (Z.to_nat (1 - 1)) with 0%nat;
                              reflexivity);
                        clear -H Hk1; lia)
                  ltac:(unfold wsyms;
                        rewrite Z2Nat.id
                          by (destruct Hpack as [(HSYe & _)|(HSYe & _)];
                              rewrite HSYe; clear; lia);
                        assert (H : rem_syms cnt0 1 mx <= SY);
                        [pose proof Hband as Hb3;
                         assert (Hn1 : rem_syms cnt0 1 mx
                                       <= Z.of_nat (length l))
                           by (unfold cnt0; apply rem_syms_le_codes;
                               clear; lia);
                         destruct Hb3 as [(HtyE & Hlcap & _)
                                         |(HtyE & Hlcap & _)];
                         unfold SY; rewrite HtyE;
                         [change (CT_LENS =? CT_LENS) with true
                         |change (CT_DISTS =? CT_LENS) with false];
                         cbv iota; clear -Hn1 Hlcap; lia
                        | clear -H; lia])
                  ltac:(intros k v Hk; rewrite PM.gempty in Hk;
                        discriminate Hk)
                  ltac:(split;
                        [intros L v HL2 Hk; rewrite PM.gempty in Hk;
                         discriminate Hk
                        |intros L HL2 (v0 & Hv0);
                         rewrite PM.gempty in Hv0; discriminate Hv0]))
      as (v & Hv & Hv1).
    rewrite HCNT in Hv. cbn [snd] in Hv.
    exists v.
    split; [exact Hv | exact Hv1]. }
  destruct Hreach as (v & Hv & Hv1).
  assert (Hgate : memo_nonzero numm (key3 n0 left0 (root0 + 1)) = true).
  { unfold memo_nonzero.
    rewrite Hv.
    destruct (Z.eqb_spec v 0) as [He|_];
      [exfalso; clear -He Hv1; lia | reflexivity]. }
  (* the phase covers the cell *)
  rewrite <- Hlg.
  apply (phase_covers mx root0 (mx + root0 + 2) numm HR0p
           ltac:(clear -Hmx15 Hge HR0p; lia) eq_refl
           ltac:(clear -Hge; lia)
           SY n0 left0
           ltac:(clear -Hn3 HnSY; lia)
           ltac:(destruct Hpack as [(HSYe & _)|(HSYe & _)];
                 rewrite HSYe; clear; vm_compute;
                 intros H; discriminate H)
           ltac:(clear -Hl2 Hltn; lia)
           Hev
           ltac:(clear -Hge; lia)
           Hgate).
Qed.

(* ==========================================================================
   THE CLOSE.
   ========================================================================== *)

Theorem seed_obligation_holds : seed_obligation.
Proof.
  exact (seed_obligation_of_oracle seed_oracle_holds).
Qed.

Theorem enough_fits_capped_final : EnoughFits_STMT.
Proof.
  exact (enough_fits_capped_mod_seed seed_obligation_holds).
Qed.
