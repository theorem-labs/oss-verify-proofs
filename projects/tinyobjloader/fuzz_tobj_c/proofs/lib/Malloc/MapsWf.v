(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Stdlib.Lists.List"; "In"; "filter"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "mwf"; "wdisj"; "range_in_maps"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "prod"; "fst"; "snd"; "bool"; "true"; "app"; "cons"; "pair"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "add"; "mul"; "pow"; "@Corelib.Init.Logic"; "and"; "eq"; "or"; "ex"; "not"; "iff"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "map_remove"; "iv_subtract"; "maps_subtract"; "region_free"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "PGSZ"; "@LinuxProcessSemantics.Riscv.Prelude"; "bv_eqb"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MapsWf"; "mwf_rec"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics State.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma wdisj_sym e e' : ltac2:(tb__ "0|0|
S3Ve;Ve';A2S3Ve';Ve;A2F_;").
Proof. unfold wdisj. tauto. Qed.

Fixpoint mwf_rec (l : list (word * word)) : Prop :=
  match l with
  | [] => True
  | e :: t => 0 < bv_unsigned (snd e) /\ (forall e', In e' t -> wdisj e e') /\ mwf_rec t
  end.

Lemma mwf_rec_iff l : ltac2:(tb__ "0|0|
S19S2Vl;A1S21Vl;A1A2").
Proof.
  induction l as [|e t IH].
  - split; [intros _; exact I|]. intros _ l1 e l2 E. destruct l1; discriminate E.
  - split.
    + intros H. cbn. destruct (H [] e t eq_refl) as [P D]. split; [exact P|]. split; [exact D|].
      apply IH. intros l1 x l2 E. destruct (H (e :: l1) x l2 ltac:(rewrite E; reflexivity)) as [P' D'].
      split; [exact P'|]. intros e' He'. apply D'. cbn. right. exact He'.
    + intros (P & D & T) l1 x l2 E. destruct l1 as [|y l1'].
      * injection E as <- <-. split; [exact P|]. intros e' He'. exact (D e' He').
      * injection E as <- E'. destruct (proj2 IH T l1' x l2 E') as [P' D']. split; [exact P'|].
        intros e' [<-|He']; [|exact (D' e' He')].
        apply wdisj_sym. apply D. rewrite E'. apply in_app_iff. right. left. reflexivity.
Qed.

Lemma mwf_nil : mwf [].
Proof. apply mwf_rec_iff. exact I. Qed.

Lemma mwf_cons e l : ltac2:(tb__ "0|3|
S2Vl;A1S10Z0S6Q40M0S9S5G0A1M1G1Ve;A3A2A2S7G1G1A2M2S0G2R1Vl;A3S3Ve;R2A2F_;Fe';S2SdG2Ve;Vl;A3A1F_;F_;F_;").
Proof. intros H P D. apply mwf_rec_iff. cbn. split; [exact P|]. split; [exact D|]. apply mwf_rec_iff. exact H. Qed.

Lemma mwf_tail e l : ltac2:(tb__ "0|3|
S2SdS7S5Q40M0A1M1G1A2M2Ve;Vl;A3A1S14S2Vl;A1S14S10Z0S6G0S9G1G1Ve;A3A2A2G2S0G2R1Vl;A3S3Ve;R2A2F_;Fe';A2A2F_;").
Proof. intros H. apply mwf_rec_iff in H. cbn in H. destruct H as (P & D & T). split; [apply mwf_rec_iff; exact T|]. auto. Qed.

Lemma mwf_app_inv l1 l2 : ltac2:(tb__ "0|1|
S2ScS7S5Q40A1M0G0A2Vl1;Vl2;A3A1S2Vl2;A1F_;").
Proof. induction l1 as [|e t IH]; [intros H; exact H|]. intros H. apply IH. exact (proj1 (mwf_tail e (t ++ l2) H)). Qed.

Lemma mwf_In_pos l e : ltac2:(tb__ "0|2|
S2Vl;A1S0S7S5Q40M0A1M1G1A2Ve;Vl;A3S10Z0S6G0S9G1G1Ve;A3A2A2F_;F_;").
Proof. intros H Hin. apply in_split in Hin as (l1 & l2 & ->). exact (proj1 (H l1 e l2 eq_refl)). Qed.

Lemma mwf_filter f l : ltac2:(tb__ "0|1|
S2Vl;A1S2S1S7S5Q40A1M0G0A2Vf;Vl;A3A1F_;").
Proof.
  induction l as [|e t IH]; intros H; [exact mwf_nil|].
  destruct (mwf_tail e t H) as (T & P & D). cbn. destruct (f e).
  - apply mwf_cons; [exact (IH T) | exact P |]. intros e' He'. apply filter_In in He' as [He' _]. exact (D e' He').
  - exact (IH T).
Qed.

Lemma region_free_wdisj l lo n : ltac2:(tb__ "0|2|
S15SaS1dVl;Vlo;Vn;A3SbA3S7S5Q40A1M0G0A2M1S0G1R1Vl;A3S3SeG0G0Vlo;Vn;A4R2A2F_;Fe';F_;").
Proof.
  induction l as [|[a sz] t IH]; intros H e' Hin; [destruct Hin|].
  cbn [region_free] in H. apply andb_prop in H as [H1 H2].
  destruct Hin as [<-|Hin]; [|exact (IH H2 e' Hin)].
  unfold wdisj. cbn [fst snd]. apply Bool.negb_true_iff in H1. unfold iv_overlap in H1.
  apply Bool.andb_false_iff in H1 as [H1|H1]; apply Z.ltb_ge in H1; lia.
Qed.

Lemma region_free_app l1 l2 lo n : ltac2:(tb__ "0|1|
S15SaS1dScS7S5Q40A1M0G0A2Vl1;Vl2;A3Vlo;Vn;A3SbA3S15SaS1dVl2;Vlo;Vn;A3SbA3F_;").
Proof. induction l1 as [|[a sz] t IH]; cbn [region_free app]; intros H; [exact H|]. apply andb_prop in H as [_ H]. exact (IH H). Qed.

Lemma wdisj_sub e e0 e' : ltac2:(tb__ "0|4|
S3Ve0;Ve';A2SfS6Q40M0S8S5G0A1M1G1Ve0;A3A2M2S6G0S8G1G1Ve;A3A2M3A2SfS11G3S6G0S9G1G1Ve;A3A2A2S11G2S6G0S9G1G1Ve0;A3A2A2A2S3Ve;Ve';A2F_;F_;F_;").
Proof. unfold wdisj. lia. Qed.

Lemma two64 : bv_modulus 64%N = 2 ^ 64. Proof. reflexivity. Qed.

Lemma iv_subtract_pieces a sz lo hi p : ltac2:(tb__ "0|8|
S10Z0M0S6Q40M1Vsz;A2M2A2S14SfG0Vhi;A2S10Vhi;S13Z2Z40A2A2A2S0S7S5G1A1M3G3A2Vp;S1bVa;Vsz;Vlo;Vhi;A4A3S14S10G0S6G1S9G3G3Vp;A3A2M4A2S14SfS6G1Va;A2M5S6G1S8G3G3Vp;A3A2M6A2S14SfS11G6G4A2M7S11G5G2A2A2S16SfG7Vlo;A2SfVhi;G6A2A2A2A2A2F_;F_;F_;").
Proof.
  intros Hsz Hhi Hin. pose proof (bv_unsigned_in_range _ a) as Ra. pose proof (bv_unsigned_in_range _ sz) as Rs. rewrite two64 in Ra, Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [<-|[]]. cbn [fst snd].
    rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia). lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E; [|destruct Hin]. apply Z.ltb_lt in E. destruct Hin as [<-|[]]. cbn [fst snd].
    rewrite !Z_to_bv_unsigned, !bv_wrap_small by (rewrite two64; lia). lia.
Qed.

Lemma in_maps_subtract t lo hi e' : ltac2:(tb__ "0|2|
S0S7S5Q40A1M0G0A2M1Ve';S1cVt;Vlo;Vhi;A3A3S17G0G0S17G0G0S14S0G1SeG0G0R2R1A4Vt;A3S0G1Ve';S1bR2R1Vlo;Vhi;A4A3A2Lsz';A2La';A2F_;").
Proof.
  induction t as [|[a sz] t IH]; cbn [maps_subtract]; intros H; [destruct H|].
  apply in_app_iff in H as [H|H].
  - exists a, sz. split; [left; reflexivity | exact H].
  - destruct (IH H) as (a' & sz' & Hin & He). exists a', sz'. split; [right; exact Hin | exact He].
Qed.

Lemma mwf_subtract l lo hi : ltac2:(tb__ "0|0|
S14SfZ0Vlo;A2SfVlo;Vhi;A2A2S10Vhi;S13Z2Z40A2A2S2Vl;A1S2S1cVl;Vlo;Vhi;A3A1F_;F_;F_;").
Proof.
  intros Hlh Hhi. induction l as [|[a sz] t IH]; intros H; [exact mwf_nil|].
  destruct (mwf_tail _ t H) as (T & P & D). cbn [maps_subtract].
  specialize (IH T).
  assert (DT : forall p e', In p (iv_subtract a sz lo hi) -> In e' (maps_subtract t lo hi) -> wdisj p e').
  { intros p e' Hp He'. apply in_maps_subtract in He' as (a' & sz' & Hin' & He').
    destruct (iv_subtract_pieces a sz lo hi p P ltac:(lia) Hp) as (P1 & P2 & P3 & _).
    destruct (iv_subtract_pieces a' sz' lo hi e' (mwf_In_pos t _ T Hin') ltac:(lia) He') as (Q1 & Q2 & Q3 & _).
    apply (wdisj_sub p (a, sz)); [| cbn [fst]; lia | cbn [fst snd]; lia].
    apply wdisj_sym. apply (wdisj_sub e' (a', sz')); [| cbn [fst]; lia | cbn [fst snd]; lia].
    apply wdisj_sym. exact (D _ Hin'). }
  assert (PP : forall p, In p (iv_subtract a sz lo hi) -> 0 < bv_unsigned (snd p)).
  { intros p Hp. exact (proj1 (iv_subtract_pieces a sz lo hi p P ltac:(lia) Hp)). }

  unfold iv_subtract in DT, PP |- *.
  destruct (bv_unsigned a <? lo) eqn:E1; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:E2; cbn [app].
  - apply mwf_cons; [apply mwf_cons; [exact IH | apply PP; cbn; tauto | intros e' He'; apply DT; [cbn; tauto | exact He']] | apply PP; cbn; tauto |].
    intros e' [<-|He']; [|apply DT; [cbn; tauto | exact He']].
    apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. pose proof (bv_unsigned_in_range _ a) as Ra. pose proof (bv_unsigned_in_range _ sz) as Rs. rewrite two64 in Ra, Rs.
    unfold wdisj. cbn [fst snd]. rewrite !Z_to_bv_unsigned, !bv_wrap_small by (rewrite two64; lia). left. lia.
  - apply mwf_cons; [exact IH | apply PP; cbn; tauto | intros e' He'; apply DT; [cbn; tauto | exact He']].
  - apply mwf_cons; [exact IH | apply PP; cbn; tauto | intros e' He'; apply DT; [cbn; tauto | exact He']].
  - exact IH.
Qed.

Lemma bv_eqb_self (a : word) : ltac2:(tb__ "0|0|
S15SaS1fQ40Va;Va;A3SbA3").
Proof. unfold bv_eqb. destruct (decide (a = a)); [apply Z.eqb_refl | congruence]. Qed.
Lemma bv_eqb_true (a b : word) : ltac2:(tb__ "0|1|
S15SaS1fQ40M0Va;Vb;A3SbA3S15S5G0A1Va;Vb;A3F_;").
Proof. unfold bv_eqb. destruct (decide (a = b)); [auto |]. intros H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma mwf_remove_other l e e' : ltac2:(tb__ "0|2|
S2Vl;A1S0S7S5Q40A1M0G0A2M1Ve;Vl;A3S0G1Ve';S1aVl;S8G0G0Ve;A3A2A3S14S3Ve;Ve';A2S0G1Ve';Vl;A3A2F_;F_;F_;").
Proof.
  intros H Hin Hin'. unfold map_remove in Hin'. apply filter_In in Hin' as [Hl' Hb].
  split; [|exact Hl']. apply in_split in Hin as (l1 & l2 & ->).
  destruct (H l1 e l2 eq_refl) as [P D].
  apply in_app_iff in Hl' as [X|[<-|X]]; [apply D; apply in_app_iff; left; exact X | | apply D; apply in_app_iff; right; exact X].
  exfalso. rewrite bv_eqb_self in Hb. discriminate Hb.
Qed.

Lemma mwf_remove l a : ltac2:(tb__ "0|0|
S2Vl;A1S2S1aVl;Va;A2A1F_;").
Proof. intros H. unfold map_remove. apply mwf_filter. exact H. Qed.

Lemma wdisj_base_ne e e' : ltac2:(tb__ "0|3|
S3Ve;Ve';A2S10Z0M0S6Q40M1S9S5G1A1M2G2Ve;A3A2A2S10G0S6G1S9G2G2Ve';A3A2A2S18S15G2S8G2G2Ve';A3S8G2G2Ve;A3A3A1F_;F_;F_;").
Proof. unfold wdisj. intros D P P' E. rewrite E in D. lia. Qed.

Lemma map_remove_keeps l e e' : ltac2:(tb__ "0|2|
S2Vl;A1S0S7S5Q40A1M0G0A2M1Ve;Vl;A3S0G1Ve';Vl;A3S3Ve;Ve';A2S0G1Ve';S1aVl;S8G0G0Ve;A3A2A3F_;F_;F_;F_;").
Proof.
  intros H He He' D. unfold map_remove. apply filter_In. split; [exact He'|].
  pose proof (wdisj_base_ne e e' D (mwf_In_pos l e H He) (mwf_In_pos l e' H He')) as NE.
  destruct (bv_eqb (fst e') (fst e)) eqn:E; [|reflexivity]. apply bv_eqb_true in E. exfalso. exact (NE E).
Qed.

Lemma map_remove_other_occ l1 e l2 e' : ltac2:(tb__ "0|3|
S2ScS7S5Q40A1M0G0A2M1Vl1;SdG1Ve;Vl2;A3A3M2A1S0G1Ve';ScG1Vl1;Vl2;A3A3S0G1Ve';S1aG2S8G0G0Ve;A3A2A3F_;F_;").
Proof.
  intros H Hin. destruct (H l1 e l2 eq_refl) as [P D].
  apply (map_remove_keeps _ e e' H); [apply in_app_iff; right; left; reflexivity | | exact (D e' Hin)].
  apply in_app_iff in Hin as [X|X]; apply in_app_iff; [left; exact X | right; right; exact X].
Qed.

Lemma mwf_In_ne_wdisj l e e' : ltac2:(tb__ "0|2|
S2Vl;A1S0S7S5Q40A1M0G0A2M1Ve;Vl;A3S0G1Ve';Vl;A3S18S15G1Ve;Ve';A3A1S3Ve;Ve';A2F_;F_;F_;F_;").
Proof.
  intros H He He' Hne. apply in_split in He as (l1 & l2 & ->).
  destruct (H l1 e l2 eq_refl) as [_ D]. apply D.
  apply in_app_iff in He' as [X|[X|X]]; [apply in_app_iff; left; exact X | exfalso; exact (Hne X) | apply in_app_iff; right; exact X].
Qed.

Lemma in_maps_subtract_intro t lo hi a' sz' e' : ltac2:(tb__ "0|2|
S0S7S5Q40A1M0G0A2M1SeG0G0Va';Vsz';A4Vt;A3S0G1Ve';S1bVa';Vsz';Vlo;Vhi;A4A3S0G1Ve';S1cVt;Vlo;Vhi;A3A3F_;F_;").
Proof.
  induction t as [|[a sz] t IH]; cbn [maps_subtract]; intros Hin He; [destruct Hin|].
  apply in_app_iff. destruct Hin as [E|Hin]; [injection E as -> ->; left; exact He | right; exact (IH Hin He)].
Qed.

Lemma pages_apart (maps : list (word * word)) (lo n b p : Z) : ltac2:(tb__ "0|5|
S7S5Q40M0A1M1G1A2M2S0G2R1Vmaps;A3S16SfS11Vlo;Vn;A2M3S6G0S8G1G1R2A3A2M4A2SfS11G4S6G0S9G1G1R2A3A2A2Vlo;A2A2F_;Fe;S20S14SfZ1R1A2S10R1Vp;A2A2S4Vmaps;S11Vb;S12S1eR2A2A2S1eA3F_;Fk;S10Z0Vn;A2SfZ2Vp;A2S16SfG3S11Vb;S1eA2A2SfS11Vb;S12S1eVp;A2A2Vlo;A2A2F_;F_;F_;F_;").
Proof.
  unfold PGSZ. intros Hfree Hcov Hn Hp.
  destruct (Z_le_dec (lo + n) (b + 4096)) as [|N1]; [left; assumption|].
  destruct (Z_le_dec (b + 4096 * p) lo) as [|N2]; [right; assumption|]. exfalso.
  set (x := Z.max lo (b + 4096)).
  assert (Hx1 : lo <= x < lo + n) by (unfold x; lia).
  assert (Hx2 : b + 4096 <= x < b + 4096 * p) by (unfold x; lia).
  set (k := (x - b) / 4096).
  assert (Hk : b + 4096 * k <= x < b + 4096 * k + 4096).
  { unfold k. pose proof (Z_div_mod_eq_full (x - b) 4096). pose proof (Z.mod_pos_bound (x - b) 4096 ltac:(lia)). lia. }
  assert (Hk1 : 1 <= k < p).
  { unfold k. split.
    - apply Z.div_le_lower_bound; lia.
    - apply Z.div_lt_upper_bound; lia. }
  destruct (Hcov k Hk1) as (e & He & E1 & E2).
  destruct (Hfree e He) as [D|D]; lia.
Qed.
