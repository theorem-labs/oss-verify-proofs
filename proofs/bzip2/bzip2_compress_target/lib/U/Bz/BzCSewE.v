(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCMem BzArrD BzLemmasT BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasFs BzCPermF BzCPermF2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCPermM.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCSewC BzCSewD.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzLemmasT OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSortF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSortM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasFs OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCPermM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC.BzCSewB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewC OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCSewD.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

Lemma cntP_all : forall P n, (forall i, 0 <= i < Z.of_nat n -> P i = true) -> cntP P n = Z.of_nat n.
Proof. induction n as [|n IH]; intros H; cbn [cntP]; [reflexivity|]. rewrite IH by (intros; apply H; lia). rewrite H by lia. lia. Qed.
Lemma cntP_none : forall P n, (forall i, 0 <= i < Z.of_nat n -> P i = false) -> cntP P n = 0.
Proof. induction n as [|n IH]; intros H; cbn [cntP]; [reflexivity|]. rewrite IH by (intros; apply H; lia). rewrite H by lia. lia. Qed.

Section Step2.
  Variables (a2 : zarr) (nb ss : Z) (bd P0 a2r : zarr).
  Hypothesis BB : forall i, 0 <= rd8 a2 i < 256.
  Hypothesis NB : 1 <= nb <= 2097151.
  Hypothesis SS : 0 <= ss < 256.
  Hypothesis BD : zget bd ss = 0.
  Hypothesis P0X : PINV a2 nb P0.
  Hypothesis AGR : forall k, 0 <= k < nb -> rd8 a2r k = rd8 a2 k.

  Local Notation KEY := (key a2 nb).
  Local Notation CLM := (ClM a2 nb).
  Local Notation SD := (SIDE a2 nb ss).
  Local Notation cs0 := (cs0 a2 nb ss).
  Local Notation ce1 := (ce1 a2 nb ss).
  Local Notation B0 := (B0 a2 nb ss).
  Local Notation B1 := (B1 a2 nb ss).

  (* [comment removed for export] *)
  Definition allss : bool := forallb (fun z => rd8 a2 z =? ss) (zrange 0 nb).
  Lemma allss_true : allss = true -> forall z, 0 <= z < nb -> rd8 a2 z = ss.
  Proof.
    intros H z Hz. unfold allss in H. apply Z.eqb_eq. apply (proj1 (forallb_forall (fun z => rd8 a2 z =? ss) (zrange 0 nb)) H z).
    apply in_zrange. exact Hz.
  Qed.
  Lemma allss_false : allss = false -> NALL a2 nb ss.
  Proof.
    intros H. unfold allss in H.
    destruct (existsb (fun z => negb (rd8 a2 z =? ss)) (zrange 0 nb)) eqn:E.
    - apply existsb_exists in E. cps_destruct E as (z & Hz & Bz). apply in_zrange in Hz. exists z. split; [exact Hz|].
      apply Bool.negb_true_iff in Bz. apply Z.eqb_neq in Bz. exact Bz.
    - exfalso. assert (forallb (fun z => rd8 a2 z =? ss) (zrange 0 nb) = true); [|congruence].
      apply forallb_forall. intros z Hz. destruct (rd8 a2 z =? ss) eqn:Q; [reflexivity|].
      assert (existsb (fun z => negb (rd8 a2 z =? ss)) (zrange 0 nb) = true); [|congruence].
      apply existsb_exists. exists z. split; [exact Hz|]. rewrite Q. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma allss_ClM : allss = true -> forall v, (v <= 256 * ss + ss -> CLM v = 0) /\ (256 * ss + ss < v -> CLM v = nb).
  Proof.
    intros H v.
    assert (K : forall z, 0 <= z < nb -> KEY z = 256 * ss + ss).
    { intros z Hz. apply (proj2 (key_chars a2 nb BB z ss ss SS)). split; [apply allss_true; assumption|]. apply allss_true; [exact H| apply nxt_range; assumption]. }
    unfold ClM. split; intros Hv.
    - apply cntP_none. intros i Hi. apply Z.ltb_ge. rewrite K by lia. lia.
    - rewrite cntP_all; [lia|]. intros i Hi. apply Z.ltb_lt. rewrite K by lia. lia.
  Qed.

  Theorem step2_exact : forall cs ce,
    (forall c, 0 <= c < 256 -> zget cs c = cs0 c) -> (forall c, 0 <= c < 256 -> zget ce c = ce1 c - 1) ->
    let rf := ms_copy_fwd (S (Z.to_nat nb)) P0 cs a2r bd nb ss B0 in
    let rb := ms_copy_bwd (S (Z.to_nat nb)) (fst (fst rf)) ce a2r bd nb ss (B1 - 1) in
    let a1 := fst (fst rb) in let cs' := snd (fst rf) in let ce' := snd (fst rb) in
    PINV a2 nb a1 /\
    (zget cs' ss - 1 = zget ce' ss \/ (zget cs' ss = 0 /\ zget ce' ss = nb - 1)) /\
    (forall c, 0 <= c < 256 -> cs0 c <= zget cs' c <= ce1 c /\ cs0 c - 1 <= zget ce' c <= ce1 c - 1 /\
                               (zget bd c <> 0 -> zget cs' c = cs0 c /\ zget ce' c = ce1 c - 1)) /\
    (forall p, (forall c, 0 <= c < 256 -> zget bd c = 0 -> ~ (cs0 c <= p < ce1 c)) -> rd32 a1 p = rd32 P0 p) /\
    snd rf = zget cs' ss /\ snd rb = zget ce' ss.
  Proof.
    intros cs ce Hcs Hce. destruct allss eqn:AL.
    - (* [comment removed for export] *)
      pose proof (allss_ClM AL) as G.
      assert (EB0 : B0 = 0) by (unfold BzCSewC.B0; apply (proj1 (G _)); lia).
      assert (ES0 : cs0 ss = 0) by (unfold BzCSewC.cs0; apply (proj1 (G _)); lia).
      assert (ES1 : ce1 ss = nb) by (unfold BzCSewC.ce1; apply (proj2 (G _)); lia).
      assert (EB1 : B1 = nb) by (unfold BzCSewC.B1; apply (proj2 (G _)); lia).
      cbv zeta. rewrite EB0, EB1. rewrite ms_copy_fwd_S.
      replace (0 <? zget cs ss) with false by (symmetry; apply Z.ltb_ge; rewrite (Hcs ss SS), ES0; lia). cbn [fst snd].
      rewrite ms_copy_bwd_S.
      replace (zget ce ss <? nb - 1) with false by (symmetry; apply Z.ltb_ge; rewrite (Hce ss SS), ES1; lia). cbn [fst snd].
      split; [exact P0X|]. split; [right; rewrite (Hcs ss SS), (Hce ss SS), ES0, ES1; lia|].
      split; [| split; [intros; reflexivity| rewrite (Hcs ss SS), (Hce ss SS), ES0, ES1; split; lia]].
      intros c Hc. rewrite (Hcs c Hc), (Hce c Hc). pose proof (cs0_le_ce1 a2 nb ss c). repeat split; try lia.
    - pose proof (allss_false AL) as NA. cbv zeta.
      pose proof (forward_scan a2 nb ss bd P0 BB NB SS BD P0X NA a2r AGR cs Hcs) as FS. cbv zeta in FS.
      destruct (ms_copy_fwd _ _ _ _ _ _ _ _) as [[A0 cs'] jf]. cbn [fst snd] in *. destruct FS as [FW Jf].
      pose proof (backward_scan a2 nb ss bd P0 A0 cs' BB NB SS BD P0X NA a2r AGR FW ce Hce) as BS. cbv zeta in BS.
      destruct (ms_copy_bwd _ _ _ _ _ _ _ _) as [[a1 ce'] jb]. cbn [fst snd] in *. destruct BS as [BW Jb].
      pose proof (fp_cs _ _ _ _ _ _ _ FW) as CS. pose proof (bp_ce _ _ _ _ _ _ _ BW) as CE.
      pose proof (fun c Hc => csF_le_ce1 a2 nb ss BB NB SS NA c Hc) as CF.
      pose proof (fun c Hc Bc => bp_meet _ _ _ _ _ _ _ BW c Hc Bc) as MEET.
      (* [comment removed for export] *)
      assert (LOW : forall c q, 0 <= c < 256 -> zget bd c = 0 -> cs0 c <= q < csF a2 nb ss c -> rd32 a1 q = rd32 A0 q).
      { intros c q Hc Bc Hq. apply (bp_frame _ _ _ _ _ _ _ BW). intros c' Hc' Bc' R. rewrite (MEET c' Hc' Bc') in R.
        destruct (Z.eq_dec c c') as [<-|NE]; [lia|]. pose proof (CF c Hc). pose proof (CF c' Hc').
        apply (reg_disjoint a2 nb ss c c' q NE); unfold BzCSewC.csF in *; lia. }
      assert (OUT : forall p, (forall c, 0 <= c < 256 -> zget bd c = 0 -> ~ (cs0 c <= p < ce1 c)) -> rd32 a1 p = rd32 P0 p).
      { intros p Hp. rewrite (bp_frame _ _ _ _ _ _ _ BW).
        - apply (fp_frame _ _ _ _ _ _ _ FW). intros c Hc Bc R. pose proof (CF c Hc). apply (Hp c Hc Bc). lia.
        - intros c Hc Bc R. rewrite (MEET c Hc Bc) in R. pose proof (CF c Hc). apply (Hp c Hc Bc). lia. }
      split.
      + (* [comment removed for export] *)
        intros v Hv.
        (* [comment removed for export] *)
        destruct (Z.eq_dec (v mod 256) ss) as [Ev|Nv].
        * set (c := v / 256). assert (Hc : 0 <= c < 256) by (subst c; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
          assert (Hvc : v = 256 * c + ss) by (subst c; rewrite <- Ev; rewrite (Z.div_mod v 256) at 1; lia).
          destruct (Z.eq_dec (zget bd c) 0) as [Bc|Bc].
          -- rewrite Hvc. pose proof (CF c Hc) as CFc. pose proof (MEET c Hc Bc) as Mc. split.
             ++ intros p Hp. change (ClM a2 nb (256 * c + ss)) with (cs0 c) in Hp. change (ClM a2 nb (256 * c + ss + 1)) with (ce1 c) in Hp.
                destruct (Z.lt_ge_cases p (csF a2 nb ss c)) as [L|Ge].
                ** rewrite (LOW c p Hc Bc) by lia. pose proof (fp_in _ _ _ _ _ _ _ FW c p Hc Bc ltac:(lia)) as IN.
                   apply (in_Fset a2 nb ss NB SS) in IN. tauto.
                ** pose proof (bp_in _ _ _ _ _ _ _ BW c p Hc Bc ltac:(lia)) as IN. apply (in_Fset a2 nb ss NB SS) in IN. tauto.
             ++ intros p q Hp Hq E. change (ClM a2 nb (256 * c + ss)) with (cs0 c) in Hp, Hq. change (ClM a2 nb (256 * c + ss + 1)) with (ce1 c) in Hp, Hq.
                destruct (Z.lt_ge_cases p (csF a2 nb ss c)) as [Lp|Gp]; destruct (Z.lt_ge_cases q (csF a2 nb ss c)) as [Lq|Gq].
                ** rewrite (LOW c p Hc Bc), (LOW c q Hc Bc) in E by lia. apply (fp_inj _ _ _ _ _ _ _ FW c p q Hc Bc); lia || exact E.
                ** exfalso. pose proof (fp_in _ _ _ _ _ _ _ FW c p Hc Bc ltac:(lia)) as IP. pose proof (bp_in _ _ _ _ _ _ _ BW c q Hc Bc ltac:(lia)) as IQ.
                   rewrite <- (LOW c p Hc Bc), E in IP by lia. apply (in_Fset a2 nb ss NB SS) in IP. apply (in_Fset a2 nb ss NB SS) in IQ.
                   cps_destruct IP as (_ & _ & SP). cps_destruct IQ as (_ & _ & SQ). congruence.
                ** exfalso. pose proof (fp_in _ _ _ _ _ _ _ FW c q Hc Bc ltac:(lia)) as IQ. pose proof (bp_in _ _ _ _ _ _ _ BW c p Hc Bc ltac:(lia)) as IP.
                   rewrite <- (LOW c q Hc Bc), <- E in IQ by lia. apply (in_Fset a2 nb ss NB SS) in IP. apply (in_Fset a2 nb ss NB SS) in IQ.
                   cps_destruct IP as (_ & _ & SP). cps_destruct IQ as (_ & _ & SQ). congruence.
                ** apply (bp_inj _ _ _ _ _ _ _ BW c p q Hc Bc); lia || exact E.
          -- (* [comment removed for export] *)
             apply (BEX_ext a2 nb P0 a1 v (P0X v Hv)). intros p Hp. apply OUT. intros c' Hc' Bc' R.
             destruct (Z.eq_dec c' c) as [->|NE]; [exact (Bc Bc')|].
             apply (R_disjoint a2 nb v (256 * c' + ss) p ltac:(lia) Hp). exact R.
        * apply (BEX_ext a2 nb P0 a1 v (P0X v Hv)). intros p Hp. apply OUT. intros c' Hc' Bc' R.
          apply (R_disjoint a2 nb v (256 * c' + ss) p); [| exact Hp| exact R].
          intros E. apply Nv. rewrite E. rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia.
      + split; [left; rewrite (CS ss SS), (CE ss SS), BD; cbn; rewrite (MEET ss SS BD); lia|].
        split; [| split; [exact OUT| split; [exact Jf| exact Jb]]].
        intros c Hc. rewrite (CS c Hc), (CE c Hc). pose proof (CF c Hc). pose proof (cs0_le_ce1 a2 nb ss c).
        destruct (Z.eqb_spec (zget bd c) 0) as [Bc|Bc].
        * rewrite (MEET c Hc Bc). repeat split; try lia; intros X; exfalso; exact (X Bc).
        * repeat split; try lia.
  Qed.
End Step2.
