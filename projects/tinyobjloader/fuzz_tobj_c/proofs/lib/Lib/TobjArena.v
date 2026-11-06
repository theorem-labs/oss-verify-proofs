(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@stdpp.bitvector.definitions"; "bv"; "Z_to_bv"; "bv_unsigned"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "not"; "@Corelib.Init.Datatypes"; "option"; "list"; "nat"; "Some"; "prod"; "length"; "None"; "pair"; "cons"; "fst"; "nil"; "option_map"; "snd"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "of_nat"; "lt"; "pow"; "mul"; "lor"; "shiftl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjArena"; "achain"; "bytes_at"; "rd64"; "node_addr"; "hdr_addr"; "HDR"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "nth"; "Forall"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "bytes_le_to_Z"; "Z_to_le_bytes"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "enc_bytes"; "@Stdlib.Lists.List"; "In"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition HDR : Z := 32.

Fixpoint bytes_at (m : word -> option byte) (a : Z) (k : nat) : option (list byte) :=
  match k with
  | O => Some []
  | S k' => match m (Z_to_bv 64 a), bytes_at m (a + 1) k' with
            | Some b, Some l => Some (b :: l)
            | _, _ => None
            end
  end.

Definition rd64 (m : word -> option byte) (a : Z) : option Z := ltac2:(tb__ "0|0|
S13S9S1Q8A1A1S0S26S1eVm;Va;U8A3A4").

Lemma bytes_at_length : ltac2:(tb__ "0|2|
S1Q40A1S8S1Q8A1M0A1F_;S0SaS9G0A1M1S4S8G1A1S1eR4R3R2A3SbG1R1A2A3S4SaSdG0R2A2R3A3F_;Fl;Fk;Fa;Fm;").
Proof.
  intros m a k. revert a. induction k as [|k IH]; intros a l H; cbn in H.
  - injection H as <-. reflexivity.
  - destruct (m (Z_to_bv 64 a)) as [b|]; [|discriminate].
    destruct (bytes_at m (a + 1) k) as [l'|] eqn:E; [|discriminate].
    injection H as <-. cbn. f_equal. eapply IH. exact E.
Qed.

Lemma bytes_at_nth : ltac2:(tb__ "0|5|
S1Q40M0A1S8S1Q8M1A1M2A1M3F_;S0SaS9G2A1M4S4S8G4A1S1eR4R3R2A3SbG4R1A2A3SaS23R1R4A2S4G3R7S2G0S15R6S17R2A1A2A2A1SbG2S24G2R2R4S2G1Z0A2A4A2A3F_;Fj;F_;Fl;Fk;Fa;Fm;").
Proof.
  intros m a k. revert a. induction k as [|k IH]; intros a l H j Hj; [lia|]. cbn in H.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Eb; [|discriminate].
  destruct (bytes_at m (a + 1) k) as [l'|] eqn:E; [|discriminate]. injection H as <-.
  destruct j as [|j].
  - cbn. rewrite Z.add_0_r. exact Eb.
  - cbn [nth]. replace (a + Z.of_nat (S j)) with (a + 1 + Z.of_nat j) by lia. apply IH; [exact E | lia].
Qed.

Lemma bytes_at_ext : ltac2:(tb__ "0|5|
S1Q40M0A1S8S1Q8A1M1A1M2Fx;M3G3S0SaSaS23R1R2A2S4G2R5S2G0S15R4S17R2A1A2A2M4A1R6G4A1A3F_;Fj;S4S8S9G1A1A1S1eR4R3R2A3S1eR5R3R2A3A3F_;Fk;Fa;Fm';Fm;").
Proof.
  intros m m' a k. revert a. induction k as [|k IH]; intros a H; [reflexivity|]. cbn.
  pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. rewrite H0.
  rewrite (IH (a + 1)); [reflexivity|]. intros j Hj.
  replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia. apply H. lia.
Qed.

Lemma bytes_at_defined : ltac2:(tb__ "0|4|
S1Q40M0A1S8S1Q8A1M1A1M2F_;S0SaS9G1A1M3S4S8G3A1S1eR4R3R2A3SbG3R1A2A3S0S5S16R5R1A2S18R1S15R5S17R4A1A2A2A2S7S4G2R7S2G0R2A2A1SeG1A1A3A1F_;Fz;F_;Fl;Fk;Fa;Fm;").
Proof.
  intros m a k l H z Hz.
  replace z with (a + Z.of_nat (Z.to_nat (z - a))) by lia.
  rewrite (bytes_at_nth m a k l H); [discriminate | lia].
Qed.

Lemma bytes_le_to_Z_bound : ltac2:(tb__ "0|2|
S9S1Q8A1M0A1S5S16Z0S26R1A1M1A2S18G1S19Z2S1aZ8S17SdG0R1A2A1A2A2A2A2Fl;").
Proof.
  induction l as [|b l IH]; cbn [bytes_le_to_Z length]; [lia|].
  pose proof (u8_range b). rewrite Nat2Z.inj_succ.
  replace (8 * Z.succ (Z.of_nat (length l))) with (8 + 8 * Z.of_nat (length l)) by lia.
  rewrite Z.pow_add_r by lia. rewrite Z.shiftl_mul_pow2 by lia.
  assert (Hor : Z.lor (bv_unsigned b) (bytes_le_to_Z l * 2 ^ 8) = bv_unsigned b + bytes_le_to_Z l * 2 ^ 8).
  { rewrite <- Z.lxor_lor by (apply Z.bits_inj'; intros n Hn; rewrite Z.land_spec, Z.bits_0;
      destruct (Z_lt_dec n 8) as [Hl|Hl];
      [rewrite (Z.mul_pow2_bits_low _ 8 n) by lia; apply Bool.andb_false_r
      | rewrite (testbit_u8_high b n) by lia; reflexivity]).
    rewrite <- Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros n Hn; rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_dec n 8) as [Hl|Hl];
      [rewrite (Z.mul_pow2_bits_low _ 8 n) by lia; apply Bool.andb_false_r
      | rewrite (testbit_u8_high b n) by lia; reflexivity]. }
  rewrite Hor. nia.
Qed.

Lemma rd64_range : ltac2:(tb__ "0|0|
S1Q40A1S8S1Q8A1A1F_;S0S0S4S8S0A1S1fR3R2A2SbS0R1A2A3S5S16Z0R2A2S18R2S19Z2Z40A2A2A2F_;Fv;Fa;Fm;").
Proof.
  intros m a v H. unfold rd64 in H. destruct (bytes_at m a 8) as [l|] eqn:E; [|discriminate].
  cbn in H. injection H as <-. pose proof (bytes_le_to_Z_bound l) as B.
  rewrite (bytes_at_length _ _ _ _ E) in B. exact B.
Qed.

Fixpoint achain (m : word -> option byte) (h : Z) (ns : list (Z * Z)) : Prop :=
  match ns with
  | [] => h = 0
  | (b, cap) :: r =>
      h = b /\ b <> 0 /\ 0 <= cap /\
      rd64 m (b + 8) = Some cap /\
      (exists u, rd64 m (b + 16) = Some u /\ u <= cap) /\
      (forall z, b <= z < b + HDR + cap -> m (Z_to_bv 64 z) <> None) /\
      (exists nx, rd64 m b = Some nx /\ achain m nx r)
  end.

Definition hdr_addr (ns : list (Z * Z)) (z : Z) : Prop := ltac2:(tb__ "0|0|
S6S0S0S6S0S0S5S29ScS0S0A2SfS0S0R2R1A4Vns;A3S5S16R2Vz;A2S18Vz;S15R2Z18A2A2A2A2Lcap;A2Lb;A2").
Definition node_addr (ns : list (Z * Z)) (z : Z) : Prop := ltac2:(tb__ "0|0|
S6S0S0S6S0S0S5S29ScS0S0A2SfS0S0R2R1A4Vns;A3S5S16R2Vz;A2S18Vz;S15S15R2S22A2R1A2A2A2A2Lcap;A2Lb;A2").

Lemma achain_caps : ltac2:(tb__ "0|2|
S1Q40A1S8S1Q8A1A1F_;S9ScS0S0A2M0A1S0S1dR3R1R2A3S25G0G0S5S16Z0M1S14S0S0R1A3A2S7S4S0S11S0S0R1A3G1A3A1A2Lbc;R3A3F_;Fh;Fns;Fm;").
Proof.
  intros m ns. induction ns as [|[b cap] r IH]; intros h H; [constructor|].
  cbn in H. destruct H as (-> & Hb & Hc & _ & _ & _ & (nx & _ & Hr)).
  constructor; [cbn; lia|]. exact (IH nx Hr).
Qed.

Lemma hdr_node_addr : ltac2:(tb__ "0|0|
S1Q40A1S8S1Q8A1A1F_;S0S9ScS0S0A2A1S0S1dR4R3R2A3S21R3R2A2S20R4R3A2F_;F_;Fz;Fns;Fh;Fm;").
Proof.
  intros m h ns z HA (b & cap & Hin & Hz). exists b, cap. split; [exact Hin|].
  pose proof (proj1 (Forall_forall _ _) (achain_caps m ns h HA) _ Hin) as [Hc _]. cbn in Hc. unfold HDR. lia.
Qed.

Lemma achain_defined : ltac2:(tb__ "0|3|
S1Q40M0A1S8S1Q8A1M1A1M2F_;S9ScS0S0A2A1S0S0S1dR4R2R3A3S20R4R2A2S7S4G2R6S2G0R3A2A1SeG1A1A3A1F_;F_;Fz;Fh;Fns;Fm;").
Proof.
  intros m ns. induction ns as [|[b cap] r IH]; intros h z HA (b' & cap' & Hin & Hz); [destruct Hin|].
  cbn in HA. destruct HA as (-> & Hb & Hc & Hcap & Hu & Hdef & (nx & Hnx & Hr)).
  destruct Hin as [E|Hin].
  - injection E as <- <-. exact (Hdef z Hz).
  - apply (IH nx z Hr). exists b', cap'. auto.
Qed.

Lemma rd64_ext : ltac2:(tb__ "0|4|
S1Q40M0A1S8S1Q8A1A1M1Fx;M2G2S0S0S5S16R2R1A2S18R1S15R2Z8A2A2A2S4G1R4S2G0R2A2M3A1R5G3A1A3F_;Fz;S4S8S0A1S1fR3R2A2S1fR4R2A2A3F_;Fa;Fm';Fm;").
Proof.
  intros m m' a H. unfold rd64. rewrite (bytes_at_ext m m' a 8); [reflexivity|].
  intros j Hj. apply H. lia.
Qed.

Lemma achain_frame : ltac2:(tb__ "0|6|
S1Q40M0A1M1S8S1Q8A1M2A1M3F_;G1G3Fx;S9ScS0S0A2A1S0S1dR4R1R2A3S0S21R4R1A2S4G3R6S2G0R2A2M4A1R7G4A1A3F_;Fz;S0S20R5R1A2S7S4G3R8G4A1SeG2A1M5A3A1S7S4G3R8S2G0R3A2A1G5A3A1F_;F_;Fz;S1dR6R4R5A3F_;F_;F_;Fh;Fns;Fm';Fm;").
Proof.
  intros m m' ns. induction ns as [|[b cap] r IH]; intros h HA Hh Hd; [exact HA|].
  cbn in HA |- *. destruct HA as (-> & Hb & Hc & Hcap & (u & Hu & Huc) & Hdef & (nx & Hnx & Hr)).
  assert (HH : forall z, b <= z < b + 24 -> m' (Z_to_bv 64 z) = m (Z_to_bv 64 z)).
  { intros z Hz. apply Hh. exists b, cap. split; [left; reflexivity | exact Hz]. }
  split; [reflexivity|]. split; [exact Hb|]. split; [exact Hc|].
  split; [rewrite (rd64_ext m m'); [exact Hcap | intros z Hz; apply HH; lia]|].
  split; [exists u; split; [rewrite (rd64_ext m m'); [exact Hu | intros z Hz; apply HH; lia] | exact Huc]|].
  split.
  - intros z Hz. apply Hd; [|exact (Hdef z Hz)]. exists b, cap. split; [left; reflexivity | exact Hz].
  - exists nx. split; [rewrite (rd64_ext m m'); [exact Hnx | intros z Hz; apply HH; lia]|].
    apply IH; [exact Hr | |].
    + intros z (b' & c' & Hin & Hz). apply Hh. exists b', c'. split; [right; exact Hin | exact Hz].
    + intros z (b' & c' & Hin & Hz). apply Hd. exists b', c'. split; [right; exact Hin | exact Hz].
Qed.

Lemma achain_nil : ltac2:(tb__ "0|2|
S1Q40A1S8S1Q8A1A1F_;S9ScS0S0A2M0A1M1S1dR2Z0R1A3S4G1R2S12G0A1A3F_;Fns;Fm;").
Proof. intros m [|[b c] r] H; [reflexivity|]. cbn in H. destruct H as (E & Hb & _). exfalso. exact (Hb (eq_sym E)). Qed.

Lemma achain_cons : ltac2:(tb__ "0|2|
S1Q40A1S8S1Q8A1A1F_;S0S9ScS0S0A2M0A1M1S1dR3R2R1A3S7S4S0R3Z0A3A1S6S0S0S6G1G1S4G1R5S10G0SfS0S0R6R2A4R1A3A3Lr;A2Lcap;A2F_;F_;Fns;Fh;Fm;").
Proof. intros m h [|[b c] r] H Hh; cbn in H; [exfalso; exact (Hh H)|]. destruct H as (-> & _). exists c, r. reflexivity. Qed.

Lemma lor_shiftl8 : ltac2:(tb__ "0|3|
S1Q8M0A1S0S16Z0R1A2S4S0S1bS3G0R3A2M1S1cR2Z8M2A2A2S15G1S1aR2S19Z2G2A2A2A2A3F_;Fx;Fb;").
Proof.
  intros b x Hx. pose proof (u8_range b). rewrite Z.shiftl_mul_pow2 by lia.
  rewrite <- Z.lxor_lor.
  - rewrite <- Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros n Hn; rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_dec n 8) as [Hl|Hl];
      [rewrite (Z.mul_pow2_bits_low _ 8 n) by lia; apply Bool.andb_false_r
      | rewrite (testbit_u8_high b n) by lia; reflexivity].
  - apply Z.bits_inj'; intros n Hn; rewrite Z.land_spec, Z.bits_0.
    destruct (Z_lt_dec n 8) as [Hl|Hl];
      [rewrite (Z.mul_pow2_bits_low _ 8 n) by lia; apply Bool.andb_false_r
      | rewrite (testbit_u8_high b n) by lia; reflexivity].
Qed.

Lemma Z_to_le_bytes_to_Z : ltac2:(tb__ "0|2|
S9S1Q8A1M0A1M1S4G1S27SdG0R1A2S26R1A1A2R1A3Fl;").
Proof.
  induction l as [|b l IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bytes_le_to_Z_bound l) as Bl. pose proof (u8_range b) as Bb.
  rewrite lor_shiftl8 by lia. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. rewrite bv_wrap8_mod.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia.
    replace ((bv_unsigned b + bytes_le_to_Z l * 2 ^ 8) / 2 ^ 8) with (bytes_le_to_Z l); [exact IH|].
    symmetry. rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma rd64_enc_bytes : ltac2:(tb__ "0|5|
S1Q40M0A1S8S1Q8M1A1M2A1M3F_;S0S0S4S8S0A1S1fR3R2A2SbS0R1A2A3SaS23R1U8M4A2S4G3R6S2G0S15R5S17R2A1A2A2A1SbG2S24G2R2S28G4S2G0R4A2A2S2G1Z0A2A4A2A3F_;Fj;F_;Fv;Fa;Fm;").
Proof.
  intros m a v H j Hj. unfold rd64 in H. destruct (bytes_at m a 8) as [l|] eqn:E; [|discriminate].
  cbn in H. injection H as <-. rewrite (bytes_at_nth m a 8 l E j Hj). f_equal.
  unfold enc_bytes. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_bound l) as B. rewrite (bytes_at_length _ _ _ _ E) in B.
  change (bv_wrap 64 (bytes_le_to_Z l)) with ((bytes_le_to_Z l) mod 2 ^ 64). rewrite Z.mod_small by exact B.
  rewrite <- (bytes_at_length _ _ _ _ E) at 1. rewrite Z_to_le_bytes_to_Z. reflexivity.
Qed.

Lemma bytes_at_of_nth : ltac2:(tb__ "0|5|
S1Q40M0A1S8S1Q8M1A1M2A1M3Fx;SaS0S9G2A1M4S4SaSdG2R1A2R3A3SaS23R1R5A2S4G3R7S2G0S15R5S17R2A1A2A2A1SbG2S24G2R2R4S2G1Z0A2A4A2A3F_;Fj;S4S8G4A1S1eR6R4R5A3SbG4R3A2A3F_;F_;Fl;Fa;Fk;Fm;").
Proof.
  intros m k. induction k as [|k IH]; intros a l L H.
  - destruct l; [reflexivity | discriminate].
  - destruct l as [|x l]; [discriminate|]. cbn.
    pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. cbn in H0. rewrite H0.
    rewrite (IH (a + 1) l); [reflexivity | cbn in L; lia |].
    intros j Hj. replace (a + 1 + Z.of_nat j) with (a + Z.of_nat (S j)) by lia. exact (H (S j) ltac:(lia)).
Qed.

Lemma rd64_of_bytes : ltac2:(tb__ "0|6|
S1Q40M0A1M1S8S1Q8M2A1M3A1M4Fx;S0G1SaS23R1U8M5A2S4G4R5S2G0S15R4S17R2A1A2A2A1SbG3S24G3R2S28G5R3A2S2G2Z0A2A4A2A3F_;Fj;S4S8S0A1S1fR4R3A2SbS0S3G0R2A2A2A3F_;Fw;Fa;Fm;").
Proof.
  intros m a w H.
  assert (E : bytes_at m a 8 = Some (enc_bytes 8 w)).
  { apply bytes_at_of_nth; [unfold enc_bytes; apply length_Z_to_le_bytes | exact H]. }
  unfold rd64. rewrite E. cbn [option_map]. f_equal. unfold enc_bytes.
  rewrite bytes_le_to_Z_of_le_bytes by (pose proof (bv_unsigned_in_range 64 w); lia).
  change (8 * Z.of_nat 8) with 64. apply Z.mod_small. pose proof (bv_unsigned_in_range 64 w) as R. exact R.
Qed.
