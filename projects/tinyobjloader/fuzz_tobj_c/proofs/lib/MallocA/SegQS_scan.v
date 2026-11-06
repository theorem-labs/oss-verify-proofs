(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "modulo"; "sub"; "pow"; "add"; "leb"; "ltb"; "@Corelib.Init.Logic"; "and"; "eq"; "not"; "or"; "iff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.Model"; "sec_chunk"; "sc_map_beg"; "sc_map_size"; "@Corelib.Init.Datatypes"; "list"; "nat"; "bool"; "Some"; "andb"; "app"; "cons"; "nil"; "option"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA.SegQS_scan"; "upd"; "best"; "@Stdlib.Lists.List"; "In"; "fold_left"; "nth_error"; "@Corelib.Lists.ListDef"; "map"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocA Require Import Model.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition upd (p acc c : Z) : Z := ltac2:(tb__ "0|0|
S13S0L_;S15S7Vc;Vp;A2S8Vacc;Vc;A2A2Vc;Vacc;X13x2").
Definition best (l : list Z) (p : Z) : Z := fold_left (upd p) l 0.

Lemma best_snoc : ltac2:(tb__ "0|0|
S11S0A1S0S0SaS0S1cS16S0R3S17S0R2S18S0A1A3A3R1A2S1bR1S1cR3R1A2R2A3A3Fp;Fc;Fl;").
Proof. intros l c p. unfold best. rewrite fold_left_app. reflexivity. Qed.

Lemma fold_upd_range : ltac2:(tb__ "0|1|
S11S0A1S0S0S9S1Z0R1A2S1R1R2A2A2S9S1R2S1eS0S0S1bR3A1R4R2A5M0A2S1G0R3A2A2F_;Facc;Fp;Fl;").
Proof.
  induction l as [|c l IH]; intros p acc Ha; cbn [fold_left]; [lia|].
  assert (R : 0 <= upd p acc c <= p /\ acc <= upd p acc c).
  { unfold upd. destruct ((c <=? p) && (acc <? c)) eqn:E; [apply andb_prop in E as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2; lia | lia]. }
  pose proof (IH p (upd p acc c) (proj1 R)). lia.
Qed.
Lemma best_range : ltac2:(tb__ "0|2|
S11S0A1S0S1Z0M0R1A2S9S1G0S1cR3R2A2M1A2S1G1R2A2A2F_;Fp;Fl;").
Proof. intros l p Hp. unfold best. pose proof (fold_upd_range l p 0 ltac:(lia)). lia. Qed.

Lemma fold_upd_ge : ltac2:(tb__ "0|0|
S11S0A1S0S0S0S1dS0R1R4A3S1R2R4A2S9S1Z0R4A2S1R4R5A2A2S1R4S1eS0S0S1bR6A1R7R5A5A2F_;F_;F_;Fc;Facc;Fp;Fl;").
Proof.
  induction l as [|d l IH]; intros p acc c Hin Hc Ha; [destruct Hin|]. cbn [fold_left].
  assert (R : 0 <= upd p acc d <= p /\ acc <= upd p acc d).
  { unfold upd. destruct ((d <=? p) && (acc <? d)) eqn:E; [apply andb_prop in E as [E1 E2]; apply Z.leb_le in E1; apply Z.ltb_lt in E2; lia | lia]. }
  destruct Hin as [<-|Hin].
  - pose proof (fold_upd_range l p (upd p acc d) (proj1 R)) as X.
    assert (d <= upd p acc d).
    { unfold upd. destruct ((d <=? p) && (acc <? d)) eqn:E; [lia|]. apply andb_false_iff in E as [E|E]; [apply Z.leb_gt in E; lia | apply Z.ltb_ge in E; lia]. }
    lia.
  - exact (IH p _ c Hin Hc (proj1 R)).
Qed.
Lemma fold_upd_in : ltac2:(tb__ "0|1|
S11S0A1S0S0ScSaS0S1eS0S0S1bR2A1R3R1A5M0R1A3S1dS0G0R3A3A2Facc;Fp;Fl;").
Proof.
  induction l as [|d l IH]; intros p acc; cbn [fold_left]; [left; reflexivity|].
  destruct (IH p (upd p acc d)) as [E|E].
  - rewrite E. unfold upd. destruct ((d <=? p) && (acc <? d)); [right; left; reflexivity | left; reflexivity].
  - right. right. exact E.
Qed.

Theorem best_eq : ltac2:(tb__ "0|0|
S11S0A1S0S0S2Z0R1A2S1dS0R2R4A3S1R3R4A2S0S1dS0R1R7A3S1R2R7A2S1R3R7A2F_;F_;Fc;SaS0S1cR7R6A2R5A3F_;F_;F_;F_;Fh;Fp;Fl;").
Proof.
  intros l p h H0 Hin Hp Hmax. unfold best.
  pose proof (fold_upd_ge l p 0 h Hin Hp ltac:(lia)) as GE.
  pose proof (fold_upd_range l p 0 ltac:(lia)) as RG.
  destruct (fold_upd_in l p 0) as [E|E]; [lia|].
  pose proof (Hmax _ E ltac:(lia)). lia.
Qed.

Lemma upd_machine : ltac2:(tb__ "0|2|
S0S0S0S9S1Z0M0R2A2S1R2R3A2A2S2R4S5Z2Z40A2M1A2S9S1G0R3A2S2R3G1A2A2SdS9S2S3S4R6R4A2G1A2S3S4R6R5A2G1A2A2SbS2R6R4A2A1A2SaS13S15S7R4R6A2S8R5R4A2A2S1aA3A2F_;F_;F_;Fc;Fnr;Fp;").
Proof.
  intros p nr c Hn Hp Hc. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt.
  rewrite (Z.mod_small (p - nr)) by lia. split.
  - intros [H1 H2]. rewrite Z.mod_small in H1 by lia. lia.
  - intros [H1 H2]. rewrite Z.mod_small by lia. lia.
Qed.
Lemma upd_yes : ltac2:(tb__ "0|2|
S0S0S0S9S1Z0M0R2A2S1R2R3A2A2S2R4S5Z2Z40A2M1A2S9S1G0R3A2S2R3G1A2A2S2S3S4R6R4A2G1A2S3S4R6R5A2G1A2A2SbS2R7R5A2A1SaS0S1bR8R7R6A3R6A3F_;F_;F_;F_;F_;Fc;Fnr;Fp;").
Proof. intros p nr c Hn Hp Hc H1 H2. unfold upd. rewrite (proj1 (upd_machine p nr c Hn Hp Hc) (conj H1 H2)). reflexivity. Qed.
Lemma upd_no_lt : ltac2:(tb__ "0|0|
S0S0S0S2R3R1A2SaS0S1bR4R3R2A3R3A3F_;Fc;Fnr;Fp;").
Proof. intros p nr c H. unfold upd. replace (c <=? p) with false by (symmetry; apply Z.leb_gt; exact H). reflexivity. Qed.
Lemma upd_no_ge : ltac2:(tb__ "0|2|
S0S0S0S9S1Z0M0R2A2S1R2R3A2A2S2R4S5Z2Z40A2M1A2S9S1G0R3A2S2R3G1A2A2SbS2S3S4R6R4A2G1A2S3S4R6R5A2G1A2A2A1SaS0S1bR7R6R5A3R6A3F_;F_;F_;F_;Fc;Fnr;Fp;").
Proof.
  intros p nr c Hn Hp Hc H1. unfold upd. destruct ((c <=? p) && (nr <? c)) eqn:E; [|reflexivity].
  exfalso. apply H1. exact (proj1 (proj2 (upd_machine p nr c Hn Hp Hc) E)).
Qed.

Lemma chunk_is_best : ltac2:(tb__ "0|6|
S11SeA1S12SeS0SaS19SeA1M0S1fSeR4R3A3S14SeR2A2A3S9S1SfR3A1M1R2A2S2R2S6G1S10R3A1A2M2A2A2S2Z0M3SfR4A1A2S12SeSaG0S1fSeR9R2A3S14SeR1A2M4A3SbSaS12R9R3A3A1ScS1S6SfR9A1M5S10R9A1A2G1A2S1G2G5A2A2F_;F_;Fch';Fj;S12SeSaG0S1fSeRaR2A3G4A3S2G3S10R2A1A2F_;Fch';Fj;SaS0S1cS20SeS0SfR9A4R6A2SfR7A1A3F_;F_;F_;F_;F_;Fp;Fch;Fi;Fsec;").
Proof.
  intros sec i ch p Hi Hp H0 Hsep Hpos. apply best_eq; [exact H0 | apply in_map; exact (nth_error_In _ _ Hi) | lia |].
  intros c Hc Hcp. apply in_map_iff in Hc as (ch' & <- & Hin'). apply In_nth_error in Hin' as (j & Hj).
  destruct (Nat.eq_dec i j) as [<-|NE]; [rewrite Hi in Hj; injection Hj as <-; lia|].
  pose proof (Hpos j ch' Hj). destruct (Hsep j ch' Hj NE); lia.
Qed.
