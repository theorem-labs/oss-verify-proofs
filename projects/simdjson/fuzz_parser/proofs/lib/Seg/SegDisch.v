(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymStepR.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosFxStep PIosFxSound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegSR SegLin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import AX2. Import AX2B. Import AX2S. Import AX2F.

Module SDI.

Fixpoint rom_cov (segs : list Segment) (lo : Z) (k : nat) : bool :=
  match k with
  | O => true
  | S k' => match seg_rom segs (Z_to_bv 64 lo) with Some _ => rom_cov segs (lo + 1) k' | None => false end
  end.

(* [comment removed for export] *)
Definition rom_iv (segs : list Segment) (lo hi k n : Z) : bool :=
  if Z.leb (hi - lo + n) 65536 then
    if Z.leb 0 lo then if Z.leb 0 (lo + k) then if Z.leb (hi + k + n) (2^64) then rom_cov segs (lo + k) (Z.to_nat (hi - lo + n))
    else false else false else false
  else false.

Lemma rom_iv_and : forall segs lo hi k n, rom_iv segs lo hi k n = true ->
  (Z.leb 0 lo && Z.leb 0 (lo + k) && Z.leb (hi + k + n) (2^64) && Z.leb (hi - lo + n) 65536
   && rom_cov segs (lo + k) (Z.to_nat (hi - lo + n)))%bool = true.
Proof.
  intros segs lo hi k n H. unfold rom_iv in H.
  destruct (Z.leb (hi - lo + n) 65536), (Z.leb 0 lo), (Z.leb 0 (lo + k)), (Z.leb (hi + k + n) (2^64)); try discriminate; exact H.
Qed.

(* [comment removed for export] *)
Definition srng (kn : list kentry) (b : expr) : option (Z * Z) :=
  match SSR.srange (facts_of kn) b with Some (lo, hi) => if Z.leb 0 lo then Some (lo, hi) else None | None => None end.

Definition rom_ok (segs : list Segment) (kn : list kentry) (b : expr) (k n : Z) : bool :=
  if (match erange (facts_of kn) b with Some (lo, hi) => rom_iv segs lo hi k n | None => false end) then true
  else match srng kn b with Some (lo, hi) => rom_iv segs lo hi k n | None => false end.

(* [comment removed for export] *)
Definition rom_ok_s (segs : list Segment) (kn : list kentry) (b : expr) (k n : Z) : bool :=
  match SSR.srange (facts_of kn) b with
  | Some (lo, hi) =>
      if Z.leb (hi - lo + n) 65536 then
        if Z.leb 0 (lo + k) then if Z.ltb (hi + k) (2^64) then if Z.leb (hi + k + n) (2^64) then
          rom_cov segs (lo + k) (Z.to_nat (hi - lo + n))
        else false else false else false
      else false
  | None => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sr_in (kn : list kentry) (rb : expr) (rk n : Z) (kb : expr) (kk : Z) (len : expr) : bool :=
  match kb, len with
  | ELit z0, ELit l0 =>
      match SSR.srange kn rb with
      | Some (lo, hi) => if Z.leb 0 lo then
                           if Z.leb (z0 mod 2 ^ 64 + kk) (lo + rk) then Z.leb (hi + rk + n) (z0 mod 2 ^ 64 + kk + l0 mod 2 ^ 64)
                           else false
                         else false
      | None => false
      end
  | _, _ => false
  end.
Definition defd_cover (kn : list kentry) (b : expr) (k n : Z) (K : kentry) : bool :=
  match K with
  | KUnk (SA kb kk) len | KZero (SA kb kk) len | KFill (SA kb kk) len _ | KBlob (SA kb kk) len _ =>
      if (if SLin.xinside2 kn b k (ELit n) kb kk len then SLin.xinside2 kn b k (ELit 1) kb kk len else false) then true
      else sr_in kn b k n kb kk len
  | _ => false
  end.
Definition unk_rd (kn : list kentry) (b : expr) (k n : Z) : bool :=
  if Z.leb 1 n then if Z.leb n 8 then SLin.lex (defd_cover kn b k n) kn else false else false.

Definition rom_rd (segs : list Segment) (kn : list kentry) (b : expr) (k n : Z) : bool :=
  if rom_ok segs kn b k n then true else if rom_ok_s segs kn b k n then true else unk_rd kn b k n.

Definition rom_disch (segs : list Segment) (kn : list kentry) (i0 : nat) (rb : option (saddr * nat * bool)) (sc : sidecond) : bool :=
  match sc with
  | SCReadBase (SA b k) n sx (EVar j) =>
      (match rb with Some (a', n', sx') => saddr_eqb a' (SA b k) && Nat.eqb n' n && Bool.eqb sx' sx | None => false end
       && Nat.eqb j i0 && Nat.leb 1 n && Nat.leb n 8 && evars_lt i0 b && rom_rd segs kn b k (Z.of_nat n))%bool
  | SCFlat (SA b k) (ELit z) => if (Z.leb 1 z && Z.leb z 8 && rom_ok segs kn b k z)%bool then true else unk_rd kn b k z
  | _ => false
  end.

(* [comment removed for export] *)
Definition flat_iv (lo hi k nh : Z) : bool := (Z.leb 0 (lo + k) && Z.ltb (hi + k) (2^64) && Z.leb (hi + k + nh) (2^64))%bool.

Definition flat_ok (kn : list kentry) (b : expr) (k : Z) (n : expr) : bool :=
  match erange (facts_of kn) n with
  | Some (nl, nh) =>
      if (match erange (facts_of kn) b with Some (lo, hi) => flat_iv lo hi k nh | None => false end) then true
      else match srng kn b with Some (lo, hi) => flat_iv lo hi k nh | None => false end
  | None => false
  end.

(* [comment removed for export] *)
Definition bivs (kn : list kentry) (b : expr) : list (Z * Z) :=
  (match erange (facts_of kn) b with Some iv => [iv] | None => [] end) ++ (match srng kn b with Some iv => [iv] | None => [] end).

Definition iv_apart (kn : list kentry) (b1 : expr) (k1 : Z) (n1 b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match erange (facts_of kn) n1, erange (facts_of kn) n2 with
  | Some (_, h1n), Some (_, h2n) =>
      SLin.lex (fun i1 => SLin.lex (fun i2 =>
        if Z.leb (snd i1 + k1 + h1n) (fst i2 + k2) then true else Z.leb (snd i2 + k2 + h2n) (fst i1 + k1)) (bivs kn b2)) (bivs kn b1)
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xin3 (kn : list kentry) (b1 : expr) (k1 : Z) (n1 b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  if SLin.xinside2 kn b1 k1 n1 b2 k2 n2 then true
  else match b2 with ELit _ => SLin.xinside_f kn b1 k1 n1 b2 k2 n2 | _ => false end.
Definition kd1 (kn : list kentry) (b1 : expr) (k1 : Z) (n1 b2 : expr) (k2 : Z) (n2 : expr) (K : kentry) : bool :=
  match K with
  | KDisj (SA p1 q1) m1 (SA p2 q2) m2 =>
      if xin3 kn b1 k1 n1 p1 q1 m1 then xin3 kn b2 k2 n2 p2 q2 m2
      else if xin3 kn b1 k1 n1 p2 q2 m2 then xin3 kn b2 k2 n2 p1 q1 m1 else false
  | _ => false
  end.
Definition kdisj_apart (kn : list kentry) (b1 : expr) (k1 : Z) (n1 b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  SLin.lex (kd1 kn b1 k1 n1 b2 k2 n2) kn.

Definition disj_disch (kn : list kentry) (sc : sidecond) : bool :=
  match sc with
  | SCDisj (SA b1 k1) n1 (SA b2 k2) n2 =>
      if SLin.apart2 kn b1 k1 n1 b2 k2 n2 then (flat_ok kn b1 k1 n1 && flat_ok kn b2 k2 n2)%bool
      else if iv_apart kn b1 k1 n1 b2 k2 n2 then (flat_ok kn b1 k1 n1 && flat_ok kn b2 k2 n2)%bool
      else if kdisj_apart kn b1 k1 n1 b2 k2 n2 then (flat_ok kn b1 k1 n1 && flat_ok kn b2 k2 n2)%bool else false
  | _ => false
  end.

(* [comment removed for export] *)
Definition rest_ok (segs : list Segment) (bc : bctx) (ss ss' : sym_state) (scs : list sidecond) : bool :=
  forallb (fun sc => if disj_disch (s_know ss) sc then true
                     else (rom_disch segs (s_know ss) (s_next ss) (find_readbase (s_next ss) scs) sc && Nat.ltb (s_next ss) (s_next ss'))%bool)
    (x_filterB segs bc ss ss' scs).

(* [comment removed for export] *)
Definition disch_all (segs : list Segment) (ss ss' : sym_state) (scs : list sidecond) : Prop :=
  forall sc, In sc scs -> x_dischargeable segs ss ss' (find_readbase (s_next ss) scs) sc = true
                          \/ (rom_disch segs (s_know ss) (s_next ss) (find_readbase (s_next ss) scs) sc = true /\ (s_next ss < s_next ss')%nat)
                          \/ disj_disch (s_know ss) sc = true.

Lemma rest_ok_disch : forall segs bc ss ss' scs, bc = mkbc (facts_of (s_know ss)) -> rest_ok segs bc ss ss' scs = true ->
  disch_all segs ss ss' scs.
Proof.
  intros segs bc ss ss' scs Hbc Hrest. unfold rest_ok in Hrest. subst bc. rewrite x_filterB_eq in Hrest.
  intros sc Hin. destruct (x_dischargeable segs ss ss' (find_readbase (s_next ss) scs) sc) eqn:Hx; [left; reflexivity|right].
  assert (Hin' : In sc (x_filter segs ss ss' scs)).
  { unfold x_filter. destruct scs as [|sc0 r]; [destruct Hin|]. apply filter_In. split; [exact Hin|]. rewrite Hx. reflexivity. }
  pose proof (proj1 (forallb_forall _ _) Hrest sc Hin') as Y. cbv beta in Y.
  destruct (disj_disch (s_know ss) sc) eqn:Hd; [right; reflexivity|left].
  apply andb_prop in Y as [Y1 Y2]. apply Nat.ltb_lt in Y2. split; assumption.
Qed.

Section Sound.
Context {fx : FPState}.
Variable segs : list Segment.

Lemma rom_cov_ok : forall k lo, rom_cov segs lo k = true -> forall x, (lo <= x < lo + Z.of_nat k)%Z -> seg_rom segs (Z_to_bv 64 x) <> None.
Proof.
  induction k as [|k IH]; intros lo H x Hx; [lia|]. cbn [rom_cov] in H.
  destruct (seg_rom segs (Z_to_bv 64 lo)) as [b|] eqn:Hb; [|discriminate].
  destruct (Z.eq_dec x lo) as [->|Hne]; [rewrite Hb; discriminate|]. apply (IH (lo + 1)%Z H). lia.
Qed.

Lemma rom_ok_read : forall E base kn b k n, know_ok segs E base kn -> rom_ok segs kn b k (Z.of_nat n) = true -> (1 <= n)%nat ->
  flat E (SA b k) (Z.of_nat n) /\ exists bs, rdn segs base (adenot E (SA b k)) n = Some bs /\ length bs = n.
Proof.
  intros E base kn b k n HK H Hn1.
  assert (IV : exists lo hi, lo <= bv_unsigned (edenot E b) <= hi /\ rom_iv segs lo hi k (Z.of_nat n) = true).
  { unfold rom_ok in H.
    destruct (match erange (facts_of kn) b with Some (lo, hi) => rom_iv segs lo hi k (Z.of_nat n) | None => false end) eqn:H0.
    - destruct (erange (facts_of kn) b) as [[lo hi]|] eqn:Er; [|discriminate].
      exists lo, hi. split; [exact (erange_sound segs E base (facts_of kn) b lo hi (facts_of_ok segs E base _ HK) Er) | exact H0].
    - unfold srng in H. destruct (SSR.srange (facts_of kn) b) as [[lo hi]|] eqn:Es; [|discriminate].
      destruct (Z.leb 0 lo) eqn:Hl; [|discriminate]. apply Z.leb_le in Hl.
      exists lo, hi. split; [exact (SSR.srange_sound_u segs E base (facts_of kn) b lo hi (facts_of_ok segs E base _ HK) Es Hl) | exact H]. }
  clear H. destruct IV as (lo & hi & R & H). apply rom_iv_and in H.
  apply andb_prop in H as [H H3']. apply andb_prop in H as [H H2']. apply andb_prop in H as [H H1].
  apply andb_prop in H as [H0 H0'].
  apply Z.leb_le in H0, H0', H1, H2'.
  assert (Hfl : flat E (SA b k) (Z.of_nat n)) by (unfold flat, estart; cbn [a_base a_off]; lia).
  split; [exact Hfl|].
  apply rdn_defined; rewrite (flat_u E _ _ Hfl); [destruct Hfl as (?&?&?&?); lia|].
  intros j Hj. unfold rd1. destruct (base _); [discriminate|].
  apply (rom_cov_ok _ (lo + k) H3'). unfold estart. cbn [a_base a_off]. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma sr_in_sound : forall E M kn rb rk n kb kk len, know_ok segs E M kn -> sr_in kn rb rk n kb kk len = true ->
  (estart E (SA kb kk) <= estart E (SA rb rk))%Z /\ (estart E (SA rb rk) + n <= estart E (SA kb kk) + elenZ E len)%Z.
Proof.
  intros E M kn rb rk n kb kk len HK H. unfold sr_in in H.
  destruct kb as [z0| | | | | | |]; try discriminate. destruct len as [l0| | | | | | |]; try discriminate.
  destruct (SSR.srange kn rb) as [[lo hi]|] eqn:Hs; [|discriminate].
  destruct (Z.leb 0 lo) eqn:H0; [|discriminate]. apply Z.leb_le in H0.
  destruct (Z.leb (z0 mod 2 ^ 64 + kk) (lo + rk)) eqn:H1; [|discriminate]. apply Z.leb_le in H1. apply Z.leb_le in H.
  pose proof (SSR.srange_sound_u segs E M kn rb lo hi HK Hs H0) as R.
  unfold estart, elenZ. cbn [a_base a_off]. rewrite !edenot_lit, !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z. lia.
Qed.

Lemma unk_rd_flat : forall E base kn b k n, know_ok segs E base kn -> unk_rd kn b k n = true ->
  flat E (SA b k) n /\ forall i, (0 <= i < n)%Z -> base (Z_to_bv 64 (estart E (SA b k) + i)%Z) <> None.
Proof.
  intros E base kn b k n HK H. unfold unk_rd in H.
  destruct (Z.leb 1 n) eqn:H1; [|discriminate]. destruct (Z.leb n 8) eqn:H8; [|discriminate]. apply Z.leb_le in H1, H8.
  apply SLin.lex_exists in H as (K & Hin & HK1).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  assert (Hn : elenZ E (ELit n) = n).
  { unfold elenZ. rewrite edenot_lit, Z_to_bv_unsigned, bv_wrap_small; [reflexivity | unfold bv_modulus; cbn; lia]. }
  assert (H1' : elenZ E (ELit 1) = 1%Z).
  { unfold elenZ. rewrite edenot_lit, Z_to_bv_unsigned, bv_wrap_small; [reflexivity | unfold bv_modulus; cbn; lia]. }
  assert (GEN : forall kb kk len, (if (if SLin.xinside2 kn b k (ELit n) kb kk len then SLin.xinside2 kn b k (ELit 1) kb kk len else false) then true
                                    else sr_in kn b k n kb kk len) = true ->
             flat E (SA kb kk) (elenZ E len) -> (forall i, (0 <= i < elenZ E len)%Z -> base (Z_to_bv 64 (estart E (SA kb kk) + i)%Z) <> None) ->
             flat E (SA b k) n /\ forall i, (0 <= i < n)%Z -> base (Z_to_bv 64 (estart E (SA b k) + i)%Z) <> None).
  { intros kb kk len Hx Hfl Hd.
    assert (AB : (estart E (SA kb kk) <= estart E (SA b k))%Z /\ (estart E (SA b k) + n <= estart E (SA kb kk) + elenZ E len)%Z).
    { destruct (SLin.xinside2 kn b k (ELit n) kb kk len) eqn:Hx0.
      - destruct (SLin.xinside2 kn b k (ELit 1) kb kk len) eqn:Hx1.
        + destruct (SLin.xinside2_sound segs E base kn b k (ELit n) kb kk len HK Hx0) as [A B]. rewrite Hn in B. split; assumption.
        + exact (sr_in_sound E base kn b k n kb kk len HK Hx).
      - exact (sr_in_sound E base kn b k n kb kk len HK Hx). }
    destruct AB as [A B].
    destruct Hfl as (F1 & F2 & F3 & F4).
    split; [unfold flat; lia|].
    intros i Hi. replace (estart E (SA b k) + i)%Z with (estart E (SA kb kk) + (estart E (SA b k) - estart E (SA kb kk) + i))%Z by lia.
    apply Hd. lia. }
  destruct K as [|[kb kk] len|[kb kk] len kk'| | | | | |[kb kk] len c|[kb kk] len]; cbn [defd_cover] in HK1; try discriminate;
    cbn [kentry_ok] in HKK.
  - destruct HKK as [Hfl Hz]. apply (GEN kb kk len HK1 Hfl). intros i Hi. rewrite (Hz i Hi). discriminate.
  - destruct HKK as (Hfl & _ & Hz). apply (GEN kb kk len HK1 Hfl). intros i Hi. rewrite (Hz i Hi). discriminate.
  - destruct HKK as [Hfl Hz]. apply (GEN kb kk len HK1 Hfl). intros i Hi. rewrite (Hz i Hi). discriminate.
  - destruct HKK as [Hfl Hz]. exact (GEN kb kk len HK1 Hfl Hz).
Qed.

Lemma unk_rd_read : forall E base kn b k n, know_ok segs E base kn -> unk_rd kn b k (Z.of_nat n) = true ->
  exists bs, rdn segs base (adenot E (SA b k)) n = Some bs /\ length bs = n.
Proof.
  intros E base kn b k n HK H. destruct (unk_rd_flat E base kn b k (Z.of_nat n) HK H) as [Hfl Hd].
  pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  apply rdn_defined; rewrite Hu; [lia|]. intros j Hj. unfold rd1. specialize (Hd (Z.of_nat j) ltac:(lia)).
  destruct (base _) eqn:Eb; [discriminate|]. exfalso. exact (Hd eq_refl).
Qed.

Lemma rom_rd_read : forall E base kn b k n, know_ok segs E base kn -> rom_rd segs kn b k (Z.of_nat n) = true -> (1 <= n)%nat ->
  exists bs, rdn segs base (adenot E (SA b k)) n = Some bs /\ length bs = n.
Proof.
  intros E base kn b k n HK H Hn1. unfold rom_rd in H.
  destruct (rom_ok segs kn b k (Z.of_nat n)) eqn:Hr.
  - destruct (rom_ok_read E base kn b k n HK Hr Hn1) as (_ & bs & Hbs & Hl). exists bs. split; assumption.
  - destruct (rom_ok_s segs kn b k (Z.of_nat n)) eqn:Hs; [|exact (unk_rd_read E base kn b k n HK H)].
    clear H. rename Hs into H. unfold rom_ok_s in H. destruct (SSR.srange (facts_of kn) b) as [[lo hi]|] eqn:Es; [|discriminate].
    destruct (Z.leb (hi - lo + Z.of_nat n) 65536) eqn:C1; [|discriminate].
    destruct (Z.leb 0 (lo + k)) eqn:C2; [|discriminate]. destruct (Z.ltb (hi + k) (2^64)) eqn:C3; [|discriminate].
    destruct (Z.leb (hi + k + Z.of_nat n) (2^64)) eqn:C4; [|discriminate].
    apply Z.leb_le in C1, C2, C4. apply Z.ltb_lt in C3.
    destruct (SSR.srange_sound_addr segs E base (facts_of kn) b k lo hi (facts_of_ok segs E base _ HK) Es C2 C3) as [A1 A2].
    assert (Hu : bv_unsigned (adenot E (SA b k)) = (bv_unsigned (edenot E b) + k) mod 2^64).
    { unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z_to_bv_unsigned, bv_wrap64_mod. reflexivity. }
    apply rdn_defined; rewrite Hu; [lia|].
    intros j Hj. unfold rd1. destruct (base _); [discriminate|].
    apply (rom_cov_ok _ (lo + k) H). rewrite Z2Nat.id by lia. lia.
Qed.

Lemma rom_discharge_sound : forall E0 E base ss rb sc,
  know_ok segs E base (s_know ss) -> eagree (s_next ss) E0 E ->
  rom_disch segs (s_know ss) (s_next ss) rb sc = true ->
  (forall a n sx, rb = Some (a, n, sx) ->
      exists bs, rdn segs base (adenot E0 a) n = Some bs /\ ev E (s_next ss) = Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))) ->
  sc_denot segs base E sc.
Proof.
  intros E0 E base ss rb0 sc HK Hag H Hrb. unfold rom_disch in H.
  destruct sc as [| [fb fk] fn | | | | [rb rk] rn rsx rv |]; try discriminate.
  - destruct fn as [z| | | | | | |]; try discriminate.
    destruct (Z.leb 1 z && Z.leb z 8 && rom_ok segs (s_know ss) fb fk z)%bool eqn:H0.
    + clear H. rename H0 into H.
      apply andb_prop in H as [H Hr]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H2.
      replace z with (Z.of_nat (Z.to_nat z)) in Hr by lia.
      destruct (rom_ok_read E base _ fb fk (Z.to_nat z) HK Hr ltac:(lia)) as [Hfl _].
      cbn [sc_denot]. rewrite elenZ_lit. rewrite Z2Nat.id in Hfl by lia. rewrite Z.mod_small by lia. exact Hfl.
    + assert (Hz : (1 <= z <= 8)%Z) by (unfold unk_rd in H; destruct (Z.leb 1 z) eqn:A; [|discriminate];
                                     destruct (Z.leb z 8) eqn:B; [|discriminate]; apply Z.leb_le in A, B; lia).
      destruct (unk_rd_flat E base _ fb fk z HK H) as [Hfl _].
      cbn [sc_denot]. rewrite elenZ_lit. rewrite Z.mod_small by lia. exact Hfl.
  - destruct rv as [|j| | | | | |]; try discriminate.
    apply andb_prop in H as [H Hrom]. apply andb_prop in H as [H Hvars]. apply andb_prop in H as [H Hn8].
    apply andb_prop in H as [H Hn1]. apply andb_prop in H as [Hm Hj].
    apply Nat.eqb_eq in Hj. subst j.
    destruct rb0 as [[[a' n'] sx']|]; [|discriminate].
    apply andb_prop in Hm as [Hm Hsx]. apply andb_prop in Hm as [Ha Hn].
    apply saddr_eqb_eq in Ha. apply Nat.eqb_eq in Hn. apply Bool.eqb_prop in Hsx. subst a' n' sx'.
    destruct (Hrb (SA rb rk) rn rsx eq_refl) as (bs & Hbs & Hv).
    cbn [sc_denot edenot]. exists bs. split; [|symmetry; exact Hv].
    replace (adenot E (SA rb rk)) with (adenot E0 (SA rb rk)); [exact Hbs|].
    unfold adenot. cbn [a_base]. rewrite (edenot_evars_lt (s_next ss) E0 E rb Hag Hvars). reflexivity.
Qed.

Lemma flat_ok_sound : forall E base kn b k n, know_ok segs E base kn -> flat_ok kn b k n = true -> flat E (SA b k) (elenZ E n).
Proof.
  intros E base kn b k n HK H. unfold flat_ok in H.
  destruct (erange (facts_of kn) n) as [[nl nh]|] eqn:En; [|discriminate].
  assert (IV : exists lo hi, lo <= bv_unsigned (edenot E b) <= hi /\ flat_iv lo hi k nh = true).
  { destruct (match erange (facts_of kn) b with Some (lo, hi) => flat_iv lo hi k nh | None => false end) eqn:H0.
    - destruct (erange (facts_of kn) b) as [[lo hi]|] eqn:Eb; [|discriminate].
      exists lo, hi. split; [exact (erange_sound segs E base (facts_of kn) b lo hi (facts_of_ok segs E base _ HK) Eb) | exact H0].
    - unfold srng in H. destruct (SSR.srange (facts_of kn) b) as [[lo hi]|] eqn:Es; [|discriminate].
      destruct (Z.leb 0 lo) eqn:Hl; [|discriminate]. apply Z.leb_le in Hl.
      exists lo, hi. split; [exact (SSR.srange_sound_u segs E base (facts_of kn) b lo hi (facts_of_ok segs E base _ HK) Es Hl) | exact H]. }
  clear H. destruct IV as (lo & hi & Rb & H). unfold flat_iv in H.
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H3. apply Z.ltb_lt in H2.
  pose proof (erange_sound segs E base (facts_of kn) n nl nh (facts_of_ok segs E base _ HK) En) as Rn.
  pose proof (bv_unsigned_in_range 64 (edenot E n)) as Rn'. unfold bv_modulus in Rn'. cbn in Rn'.
  unfold flat, estart, elenZ. cbn [a_base a_off]. lia.
Qed.

Lemma bivs_ok : forall E base kn b i, know_ok segs E base kn -> In i (bivs kn b) -> fst i <= bv_unsigned (edenot E b) <= snd i.
Proof.
  intros E base kn b i HK Hi. unfold bivs in Hi. apply in_app_or in Hi as [Hi|Hi].
  - destruct (erange (facts_of kn) b) as [[lo hi]|] eqn:Eb; [|destruct Hi]. destruct Hi as [<-|[]]. cbn [fst snd].
    exact (erange_sound segs E base (facts_of kn) b lo hi (facts_of_ok segs E base _ HK) Eb).
  - unfold srng in Hi. destruct (SSR.srange (facts_of kn) b) as [[lo hi]|] eqn:Es; [|destruct Hi].
    destruct (Z.leb 0 lo) eqn:Hl; [|destruct Hi]. destruct Hi as [<-|[]]. cbn [fst snd]. apply Z.leb_le in Hl.
    exact (SSR.srange_sound_u segs E base (facts_of kn) b lo hi (facts_of_ok segs E base _ HK) Es Hl).
Qed.

Lemma iv_apart_sound : forall E base kn b1 k1 n1 b2 k2 n2, know_ok segs E base kn -> iv_apart kn b1 k1 n1 b2 k2 n2 = true ->
  (estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2) \/ estart E (SA b2 k2) + elenZ E n2 <= estart E (SA b1 k1)).
Proof.
  intros E base kn b1 k1 n1 b2 k2 n2 HK H. unfold iv_apart in H.
  destruct (erange (facts_of kn) n1) as [[l1n h1n]|] eqn:E1; [|discriminate].
  destruct (erange (facts_of kn) n2) as [[l2n h2n]|] eqn:E2; [|discriminate].
  pose proof (erange_sound segs E base (facts_of kn) n1 l1n h1n (facts_of_ok segs E base _ HK) E1) as R1.
  pose proof (erange_sound segs E base (facts_of kn) n2 l2n h2n (facts_of_ok segs E base _ HK) E2) as R2.
  apply SLin.lex_exists in H as (i1 & Hi1 & H). apply SLin.lex_exists in H as (i2 & Hi2 & H).
  pose proof (bivs_ok E base kn b1 i1 HK Hi1) as B1. pose proof (bivs_ok E base kn b2 i2 HK Hi2) as B2.
  unfold estart, elenZ. cbn [a_base a_off].
  destruct (Z.leb (snd i1 + k1 + h1n) (fst i2 + k2)) eqn:T1.
  - apply Z.leb_le in T1. left. lia.
  - apply Z.leb_le in H. right. lia.
Qed.

Lemma xin3_sound : forall E base kn b1 k1 n1 b2 k2 n2, know_ok segs E base kn -> xin3 kn b1 k1 n1 b2 k2 n2 = true ->
  estart E (SA b2 k2) <= estart E (SA b1 k1) /\ estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2) + elenZ E n2.
Proof.
  intros E base kn b1 k1 n1 b2 k2 n2 HK H. unfold xin3 in H.
  destruct (SLin.xinside2 kn b1 k1 n1 b2 k2 n2) eqn:X; [exact (SLin.xinside2_sound segs E base kn _ _ _ _ _ _ HK X)|].
  destruct b2; try discriminate. exact (SLin.xinside_f_sound segs E base kn _ _ _ _ _ _ HK H).
Qed.

Lemma kdisj_apart_sound : forall E base kn b1 k1 n1 b2 k2 n2, know_ok segs E base kn -> kdisj_apart kn b1 k1 n1 b2 k2 n2 = true ->
  (estart E (SA b1 k1) + elenZ E n1 <= estart E (SA b2 k2) \/ estart E (SA b2 k2) + elenZ E n2 <= estart E (SA b1 k1)).
Proof.
  intros E base kn b1 k1 n1 b2 k2 n2 HK H. unfold kdisj_apart in H. apply SLin.lex_exists in H as (K & Hin & H1).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [| | | | | | |[p1 q1] m1 [p2 q2] m2| |]; cbn [kd1] in H1; try discriminate. cbn [kentry_ok] in HKK.
  destruct (xin3 kn b1 k1 n1 p1 q1 m1) eqn:X1.
  - destruct (xin3_sound E base kn b1 k1 n1 p1 q1 m1 HK X1) as [A1 B1].
    destruct (xin3_sound E base kn b2 k2 n2 p2 q2 m2 HK H1) as [A2 B2]. lia.
  - destruct (xin3 kn b1 k1 n1 p2 q2 m2) eqn:X2; [|discriminate].
    destruct (xin3_sound E base kn b1 k1 n1 p2 q2 m2 HK X2) as [A1 B1].
    destruct (xin3_sound E base kn b2 k2 n2 p1 q1 m1 HK H1) as [A2 B2]. lia.
Qed.

Lemma disj_disch_sound : forall E base kn sc, know_ok segs E base kn -> disj_disch kn sc = true -> sc_denot segs base E sc.
Proof.
  intros E base kn sc HK H. destruct sc as [| | [b1 k1] n1 [b2 k2] n2 | | | |]; try discriminate H. cbn [disj_disch] in H.
  destruct (SLin.apart2 kn b1 k1 n1 b2 k2 n2) eqn:Ha.
  - apply andb_prop in H as [F1 F2].
    cbn [sc_denot]. split; [exact (flat_ok_sound E base kn b1 k1 n1 HK F1)|]. split; [exact (flat_ok_sound E base kn b2 k2 n2 HK F2)|].
    exact (SLin.apart2_sound segs E base kn b1 k1 n1 b2 k2 n2 HK Ha).
  - destruct (iv_apart kn b1 k1 n1 b2 k2 n2) eqn:Hi.
    + apply andb_prop in H as [F1 F2].
      cbn [sc_denot]. split; [exact (flat_ok_sound E base kn b1 k1 n1 HK F1)|]. split; [exact (flat_ok_sound E base kn b2 k2 n2 HK F2)|].
      exact (iv_apart_sound E base kn b1 k1 n1 b2 k2 n2 HK Hi).
    + destruct (kdisj_apart kn b1 k1 n1 b2 k2 n2) eqn:Hk; [|discriminate]. apply andb_prop in H as [F1 F2].
      cbn [sc_denot]. split; [exact (flat_ok_sound E base kn b1 k1 n1 HK F1)|]. split; [exact (flat_ok_sound E base kn b2 k2 n2 HK F2)|].
      exact (kdisj_apart_sound E base kn b1 k1 n1 b2 k2 n2 HK Hk).
Qed.

(* [comment removed for export] *)
Lemma disch_val : forall E base rom ss ms ss' scs,
  (s_next ss <= s_next ss')%nat -> disch_all segs ss ss' scs -> st_okX segs E base rom ss ms ->
  exists E1, eagree (s_next ss) E E1 /\ (forall E'', eagree (s_next ss') E1 E'' -> scs_denot segs base E'' scs).
Proof.
  intros E base rom ss ms ss' scs Hle Hdis HX.
  set (i0 := s_next ss) in *.
  pose proof (st_okX_R _ _ _ _ _ _ HX) as HR0.
  destruct (st_okR_parts segs E base rom ss ms HR0) as (Hregs0 & Hmem0 & Hlf0 & Hkn0 & _).
  assert (DIS : forall E'' E1, eagree i0 E E1 -> eagree i0 E1 E'' -> know_ok segs E'' base (s_know ss) ->
                  (forall a n sx, find_readbase i0 scs = Some (a, n, sx) ->
                     exists bs, rdn segs base (adenot E a) n = Some bs /\ ev E'' i0 = Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))) ->
                  scs_denot segs base E'' scs).
  { intros E'' E1 Ha1 Ha'' Hkn'' Hrd.
    assert (HaE : eagree i0 E E'') by (eapply eagree_trans; [exact Ha1 | exact Ha'']).
    unfold scs_denot. apply Forall_forall. intros sc Hin. destruct (Hdis sc Hin) as [D|[D|D]].
    - eapply (x_discharge_sound segs E E''); [exact Hkn'' | exact HaE | exact D |].
      intros a' n' sx' Hrb'. exact (Hrd a' n' sx' Hrb').
    - destruct D as [D _]. eapply (rom_discharge_sound E E''); [exact Hkn'' | exact HaE | exact D |].
      intros a' n' sx' Hrb'. exact (Hrd a' n' sx' Hrb').
    - exact (disj_disch_sound E'' base _ sc Hkn'' D). }
  destruct (find_readbase i0 scs) as [[[a n] sx]|] eqn:Hrb.
  - assert (READ : exists bs, rdn segs base (adenot E a) n = Some bs).
    { destruct (Hdis _ (find_readbase_In _ _ _ _ _ Hrb)) as [D|[D|D]]; [ | | exfalso; unfold disj_disch in D; discriminate D].
      - fold i0 in D. try rewrite Hrb in D. unfold x_dischargeable in D.
        apply andb_prop in D as [D Hcov]. apply andb_prop in D as [D Hn8]. apply andb_prop in D as [D Hn1].
        apply Nat.leb_le in Hn1. apply Nat.leb_le in Hn8. destruct a as [ab ak]. cbn [a_base a_off] in Hcov.
        destruct (kn_readable_sound segs E _ _ base _ ab ak n (facts_of_ok segs E base _ Hkn0) Hkn0 Hn1 Hn8 Hcov) as (_ & bs & Hbs & _).
        exists bs. exact Hbs.
      - destruct D as [D _]. unfold rom_disch in D. destruct a as [ab ak].
        apply andb_prop in D as [D Hrom]. apply andb_prop in D as [D _]. apply andb_prop in D as [D _].
        apply andb_prop in D as [D Hn1]. apply Nat.leb_le in Hn1.
        destruct (rom_rd_read E base _ ab ak n Hkn0 Hrom ltac:(lia)) as (bs & Hbs & _). exists bs. exact Hbs. }
    destruct READ as (bs & Hbs).
    exists (eupd E i0 (Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)))).
    split; [apply eagree_upd|].
    intros E'' Ha''.
    assert (HaE1 : eagree i0 (eupd E i0 (Z_to_bv 64 (extz sx n (bytes_le_to_Z bs)))) E'') by (eapply eagree_le; [exact Ha'' | exact Hle]).
    assert (HaE : eagree i0 E E'') by (eapply eagree_trans; [apply eagree_upd | exact HaE1]).
    destruct (st_okR_parts segs E'' base rom ss ms (HX E'' HaE)) as (_ & _ & _ & Hkn'' & _).
    apply (DIS E'' (eupd E i0 (Z_to_bv 64 (extz sx n (bytes_le_to_Z bs))))); [apply eagree_upd | exact HaE1 | exact Hkn'' |].
    intros a' n' sx' Hrb'. try rewrite Hrb in Hrb'. injection Hrb' as <- <- <-.
    exists bs. split; [exact Hbs|].
    assert (Hlt : (i0 < s_next ss')%nat).
    { destruct (Hdis _ (find_readbase_In _ _ _ _ _ Hrb)) as [D|[D|D]]; [ | | exfalso; unfold disj_disch in D; discriminate D].
      - fold i0 in D. try rewrite Hrb in D. unfold x_dischargeable in D.
        repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H end.
        apply Nat.ltb_lt. assumption.
      - destruct D as [_ D]. exact D. }
    destruct Ha'' as [Hv _]. rewrite <- (Hv i0 Hlt). apply eupd_at.
  - exists E. split; [apply eagree_refl|].
    intros E'' Ha''.
    assert (HaE : eagree i0 E E'') by (eapply eagree_le; [exact Ha'' | exact Hle]).
    destruct (st_okR_parts segs E'' base rom ss ms (HX E'' HaE)) as (_ & _ & _ & Hkn'' & _).
    apply (DIS E'' E); [apply eagree_refl | exact HaE | exact Hkn'' |].
    intros a' n' sx' Hrb'. discriminate.
Qed.

(* [comment removed for export] *)
Lemma disch_closed : forall E base rom ss ms ss' scs,
  find_readbase (s_next ss) scs = None -> disch_all segs ss ss' scs -> st_okX segs E base rom ss ms ->
  forall E'', eagree (s_next ss) E E'' -> scs_denot segs base E'' scs.
Proof.
  intros E base rom ss ms ss' scs Hrb Hdis HX E'' Ha''.
  destruct (st_okR_parts segs E'' base rom ss ms (HX E'' Ha'')) as (_ & _ & _ & Hkn'' & _).
  unfold scs_denot. apply Forall_forall. intros sc Hin. destruct (Hdis sc Hin) as [D|[D|D]].
  - eapply (x_discharge_sound segs E E''); [exact Hkn'' | exact Ha'' | exact D |].
    intros a' n' sx' Hrb'. rewrite Hrb in Hrb'. discriminate.
  - destruct D as [D _]. eapply (rom_discharge_sound E E''); [exact Hkn'' | exact Ha'' | exact D |].
    intros a' n' sx' Hrb'. rewrite Hrb in Hrb'. discriminate.
  - exact (disj_disch_sound E'' base _ sc Hkn'' D).
Qed.

End Sound.
End SDI.
