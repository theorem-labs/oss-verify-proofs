(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmModel.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMF.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lor7 x : 0 <= x -> Z.lor x 7 + 1 = 8 * (x / 8) + 8.
Proof.
  intros Hx. pose proof (Z.add_lor_land x 7) as H.
  assert (E : Z.land x 7 = x mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  rewrite E in H. pose proof (Z.div_mod x 8 ltac:(lia)). lia.
Qed.

Lemma tb_law_le c need : PM.tb_law c -> c - 1 < need -> need < 2 ^ 26 + 16384 -> c <= 2 ^ 26.
Proof.
  intros (j & Hj & Hlt & Hlo & Hmod) Hgrow Hneed.
  destruct (Z_le_gt_dec c (2 ^ 26)) as [Hle|Hgt]; [exact Hle|exfalso].
  assert (Hj12 : 12 <= j).
  { destruct (Z_le_gt_dec 12 j) as [H|H]; [exact H|exfalso].
    assert (2 ^ (15 + j) <= 2 ^ 26) by (apply Z.pow_le_mono_r; lia). lia. }
  assert (Hd : (2 ^ 15 | 2 ^ (3 + j))).
  { exists (2 ^ (j - 12)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  assert (Hm15 : c mod 2 ^ 15 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.divide_trans with (2 ^ (3 + j)); [exact Hd|].
    apply Z.mod_divide; [pose proof (PM.pow2_pos (3 + j)); lia| exact Hmod]. }
  apply Z.mod_divide in Hm15; [|lia]. destruct Hm15 as (q & Hq).
  change (2 ^ 15) with 32768 in Hq. change (2 ^ 26) with 67108864 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma double_core c x : c mod 8 = 0 -> 16384 <= c -> 2 * (c - 1) <= x <= 2 * c - 1 -> 8 * (x / 8) + 8 = 2 * c.
Proof.
  intros Hm Hc Hx. apply Z.mod_divide in Hm; [|lia]. destruct Hm as (q & ->).
  assert (E : x / 8 = 2 * q - 1) by (symmetry; apply (Z.div_unique x 8 (2 * q - 1) (x - 8 * (2 * q - 1))); lia).
  rewrite E. lia.
Qed.

Lemma mod_pow2_le c a b : 0 <= a <= b -> c mod 2 ^ b = 0 -> c mod 2 ^ a = 0.
Proof.
  intros Hab Hm. apply Z.mod_divide; [pose proof (PM.pow2_pos a); lia|].
  apply Z.divide_trans with (2 ^ b); [exists (2 ^ (b - a)); rewrite <- Z.pow_add_r by lia; f_equal; lia|].
  apply Z.mod_divide; [pose proof (PM.pow2_pos b); lia| exact Hm].
Qed.

(* [comment removed for export] *)
Lemma tb_law_step c need c' :
  PM.tb_law c -> 26 <= c -> c - 1 < need -> need <= c - 1 + 16384 -> need < 2 ^ 26 + 16384 ->
  c' = Z.lor (Z.max (2 * (c - 1)) need) 7 + 1 ->
  PM.tb_law c' /\ 2 * (c - 1) <= c' - 1 /\ need <= c' - 1 /\ c' <= 2 ^ 27 /\ c' mod 8 = 0.
Proof.
  intros LAW Hc Hgrow Hstep Hneed ->.
  pose proof (tb_law_le c need LAW Hgrow Hneed) as Hc26.
  destruct LAW as (j & Hj & Hlt & Hlo & Hmod).
  set (x := Z.max (2 * (c - 1)) need). assert (Hx0 : 0 <= x) by (unfold x; lia).
  rewrite (lor7 x Hx0).
  assert (Hm8 : c mod 8 = 0) by (apply (mod_pow2_le c 3 (3 + j)); [lia| exact Hmod]).
  pose proof (Z.div_mod x 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as MB.
  assert (Hge : x <= 8 * (x / 8) + 8 - 1) by lia.
  destruct (Z_lt_le_dec c 16384) as [Hsmall|Hbig].
  - (* [comment removed for export] *)
    assert (j = 0). { destruct Hlo as [E|H]; [exact E|exfalso]. assert (2 ^ 14 <= 2 ^ (14 + j)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 14) with 16384 in *. lia. }
    subst j. assert (Hx : x <= 32766) by (unfold x; lia).
    assert (Hq : x / 8 <= 4095) by (apply Z.div_le_upper_bound; lia).
    assert (M8 : (8 * (x / 8) + 8) mod 8 = 0) by (replace (8 * (x / 8) + 8) with ((x / 8 + 1) * 8) by lia; apply Z.mod_mul; lia).
    split; [|change (2 ^ 27) with 134217728; unfold x in *; repeat split; try lia].
    destruct (Z_lt_le_dec (8 * (x / 8) + 8) 32768) as [Hlt'|Hge'].
    + exists 0. change (2 ^ (15 + 0)) with 32768. change (2 ^ (3 + 0)) with 8. repeat split; lia.
    + exists 1. assert (E : 8 * (x / 8) + 8 = 32768) by lia. rewrite E. change (2 ^ (15 + 1)) with 65536. change (2 ^ (14 + 1)) with 32768.
      change (2 ^ (3 + 1)) with 16. repeat split; first [lia | reflexivity].
  - (* [comment removed for export] *)
    assert (Hx : 2 * (c - 1) <= x <= 2 * c - 1) by (unfold x; lia).
    rewrite (double_core c x Hm8 Hbig Hx).
    assert (M8' : (2 * c) mod 8 = 0).
    { apply Z.mod_divide; [lia|]. apply Z.divide_mul_r. apply Z.mod_divide; [lia| exact Hm8]. }
    assert (LAW' : PM.tb_law (2 * c)).
    { exists (j + 1).
      assert (Hj12 : j <= 12).
      { destruct (Z_le_gt_dec j 12) as [H|H]; [exact H|exfalso]. destruct Hlo as [E|Hlo]; [lia|].
        assert (2 ^ 27 <= 2 ^ (14 + j)) by (apply Z.pow_le_mono_r; lia). change (2 ^ 27) with 134217728 in *. change (2 ^ 26) with 67108864 in *. lia. }
      replace (15 + (j + 1)) with (15 + j + 1) by lia. replace (14 + (j + 1)) with (15 + j) by lia. replace (3 + (j + 1)) with (3 + j + 1) by lia.
      rewrite !(Z.pow_add_r 2 _ 1) by lia. change (2 ^ 1) with 2.
      split; [lia|]. split; [lia|]. split.
      - right. destruct Hlo as [->|Hlo].
        + change (2 ^ (15 + 0)) with 32768. lia.
        + replace (15 + j) with (14 + j + 1) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
      - replace (2 * c) with (c * 2) by lia. rewrite Z.mul_mod_distr_r; [rewrite Hmod; reflexivity| pose proof (PM.pow2_pos (3 + j)); lia| lia]. }
    change (2 ^ 26) with 67108864 in *. change (2 ^ 27) with 134217728.
    split; [exact LAW'|]. split; [lia|]. split; [unfold x in *; lia|]. split; [lia| exact M8'].
Qed.

(* [comment removed for export] *)
Lemma tb_law_first need c' :
  22 < need -> need <= 22 + 16384 -> c' = Z.lor (Z.max 44 need) 7 + 1 ->
  PM.tb_law c' /\ 44 <= c' - 1 /\ need <= c' - 1 /\ c' <= 2 ^ 27 /\ c' mod 8 = 0.
Proof.
  intros H1 H2 ->. set (x := Z.max 44 need). assert (Hx0 : 0 <= x) by (unfold x; lia). rewrite (lor7 x Hx0).
  pose proof (Z.div_mod x 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as MB.
  assert (Hq : x / 8 <= 2051) by (apply Z.div_le_upper_bound; unfold x; lia).
  assert (M8 : (8 * (x / 8) + 8) mod 8 = 0) by (replace (8 * (x / 8) + 8) with ((x / 8 + 1) * 8) by lia; apply Z.mod_mul; lia).
  change (2 ^ 27) with 134217728. split; [|unfold x in *; repeat split; lia].
  exists 0. change (2 ^ (15 + 0)) with 32768. change (2 ^ (3 + 0)) with 8. repeat split; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition credit_le (c c' : credit) : Prop := fst c <= fst c' /\ snd c <= snd c'.

(* [comment removed for export] *)
Lemma pot_text_step L s s' tg :
  2 * PM.vs_cap s <= PM.vs_cap s' ->
  credit_le (PM.credit_add (PM.cost1 L (PM.vs_cap s' + 1)) (PM.pot_text L s' (tg + 1))) (PM.pot_text L s tg).
Proof. intros H. unfold credit_le, PM.credit_add, PM.cost1, PM.pot_text. cbn [fst snd]. split; lia. Qed.

(* [comment removed for export] *)
Lemma pot_stack_step L k : 0 <= k ->
  credit_le (PM.credit_add (PM.cost1 L (32 * 2 ^ (k + 1))) (PM.pot_stack L (k + 1))) (PM.pot_stack L k).
Proof.
  intros Hk. unfold credit_le, PM.credit_add, PM.cost1, PM.pot_stack. cbn [fst snd].
  replace (k + 1 + 1) with (k + 1 + 1) by lia. rewrite (Z.pow_add_r 2 (k + 1) 1) by lia. change (2 ^ 1) with 2. split; lia.
Qed.

(* [comment removed for export] *)
Lemma pot_call_le L n : 0 <= hl_k_per_malloc L <= 8 -> 0 <= hl_b_overhead L <= 6350523 -> 0 <= n < 2 ^ 26 ->
  credit_le (PM.pot_call L n) (512, 2 ^ 29 + 8 * n).
Proof.
  intros HK HB Hn. unfold credit_le, PM.pot_call, PM.credit_add, PM.cost1, PM.pot_stack, PM.pot_text, PM.vs_cap, PM.CHUNK. cbn [fst snd].
  change (2 ^ 12) with 4096. change (2 ^ (0 + 1)) with 2. change (2 ^ 28) with 268435456. change (2 ^ 29) with 536870912. change (2 ^ 26) with 67108864 in Hn.
  split; nia.
Qed.

(* [comment removed for export] *)
Lemma u8_of_u64 (segs : list Segment) (M : word -> option byte) a w : 0 <= w < 2 ^ 64 -> L5.u64_at segs M a w -> L5.u8_at segs M a (w mod 256).
Proof.
  intros Hw H. unfold L5.u64_at, L5.u8_at in *. unfold word_to_le_bytes in H. rewrite L5.unsigned_lit in H by lia.
  change (Z_to_le_bytes 8 w) with (Z_to_bv 8 w :: Z_to_le_bytes 7 (Z.shiftr w 8)) in H.
  change (rdn segs M (Z_to_bv 64 a) 8) with
    (match (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) with
     | Some b => match rdn segs M (Z_to_bv 64 a + 1) 7 with Some rest => Some (b :: rest) | None => None end | None => None end) in H.
  cbn [rdn]. destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom segs (Z_to_bv 64 a) end) as [b0|]; [|discriminate].
  destruct (rdn segs M (Z_to_bv 64 a + 1) 7) as [rest|]; [|discriminate]. injection H as Hb _. rewrite Hb. f_equal. f_equal.
  apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma odd_byte c : c mod 2 = 0 -> 0 <= c -> Z.testbit ((c + 1) mod 256) 0 = true.
Proof.
  intros Hc H0. change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia. rewrite Z.bit0_odd.
  apply Z.mod_divide in Hc; [|lia]. destruct Hc as (q & ->). replace (q * 2 + 1) with (2 * q + 1) by lia. apply Z.odd_odd.
Qed.
Lemma even_byte n : Z.testbit (2 * n) 0 = false.
Proof. apply Z.testbit_even_0. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Agree.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable A : pm_addrs.
Let T3 : (word -> option byte) -> Z -> Z -> Prop := fun _ _ _ => True.
Let T4 : (word -> option byte) -> Z -> Z -> Z -> Prop := fun _ _ _ _ => True.
Variables M M' : word -> option byte.

Abbreviation ag := (L5C.agree_on M M').

Lemma u32_at_agree a v : ag a 4 -> 0 <= a -> a + 4 <= 2 ^ 64 -> L5.u32_at segs M a v -> L5.u32_at segs M' a v.
Proof.
  intros Hag Ha H4 Hu. unfold L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4%nat a Ha ltac:(cbn; lia)); [exact Hu|].
  intros i Hi. apply Hag. cbn in Hi. lia.
Qed.
Lemma zeros_at_agree a n : ag a n -> PM.zeros_at M a n -> PM.zeros_at M' a n.
Proof. intros Hag Z i Hi. rewrite Hag by lia. apply Z. exact Hi. Qed.

Lemma vstr_at_agree o s : 0 <= o -> o + 24 <= 2 ^ 64 -> ag o 24 ->
  (forall c n p, s = PM.VLong c n p -> ag p c) ->
  PM.vstr_at segs T3 M o s -> PM.vstr_at segs T3 M' o s.
Proof.
  intros Ho Ho' AG AGB (D & _ & H). split; [apply (L5C.defined_agree M M' o 24 AG D)|]. split; [exact I|].
  destruct s as [n|c n p].
  - destruct H as (Hn & B0). split; [exact Hn|]. apply (L5C.u8_at_agree segs M M'); [apply (L5C.agree_on_sub M M' o 24); [exact AG|lia|lia]|lia|lia|exact B0].
  - destruct H as (W0 & W8 & W16 & Hn & Hc & He & DB & _).
    repeat split; try assumption; try lia.
    + apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' o 24); [exact AG|lia|lia]|lia|lia|exact W0].
    + apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' o 24); [exact AG|lia|lia]|lia|lia|exact W8].
    + apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' o 24); [exact AG|lia|lia]|lia|lia|exact W16].
    + apply (L5C.defined_agree M M' p c (AGB c n p eq_refl) DB).
Qed.

Lemma pstate_at_agree a s : 0 <= a -> a + 32 <= 2 ^ 64 -> ag a 32 -> PM.pstate_at segs M a s -> PM.pstate_at segs M' a s.
Proof.
  intros Ha Ha' AG (H0 & H8 & H16 & H24). repeat split.
  - apply u32_at_agree; [apply (L5C.agree_on_sub M M' a 32); [exact AG|lia|lia]|lia|lia|exact H0].
  - apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' a 32); [exact AG|lia|lia]|lia|lia|exact H8].
  - apply (L5C.u8_at_agree segs M M'); [apply (L5C.agree_on_sub M M' a 32); [exact AG|lia|lia]|lia|lia|exact H16].
  - apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' a 32); [exact AG|lia|lia]|lia|lia|exact H24].
Qed.

Lemma vec_at_agree v b k stk : 0 <= v -> v + 24 <= 2 ^ 64 -> 0 <= b -> b + 32 * 2 ^ k <= 2 ^ 64 -> ag v 24 -> ag b (32 * 2 ^ k) ->
  PM.vec_at segs T3 T4 M v b k stk -> PM.vec_at segs T3 T4 M' v b k stk.
Proof.
  intros Hv Hv' Hb Hb' AGV AGB (V0 & V8 & V16 & Hk & Hlen & Hal & DB & _ & _ & EL).
  pose proof (PM.pow2_pos k ltac:(lia)) as P2.
  split; [apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' v 24); [exact AGV|lia|lia]|lia|lia|exact V0]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' v 24); [exact AGV|lia|lia]|lia|lia|exact V8]|].
  split; [apply (L5C.u64_at_agree segs M M'); [apply (L5C.agree_on_sub M M' v 24); [exact AGV|lia|lia]|lia|lia|exact V16]|].
  split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
  split; [apply (L5C.defined_agree M M' b _ AGB DB)|]. split; [exact I|]. split; [exact I|].
  intros n Hn. apply pstate_at_agree; [lia|lia| |apply EL; exact Hn].
  apply (L5C.agree_on_sub M M' b (32 * 2 ^ k)); [exact AGB|lia|lia].
Qed.

(* [comment removed for export] *)
Lemma ag_sub a n a' n' : ag a n -> a <= a' -> a' + n' <= a + n -> ag a' n'.
Proof. apply L5C.agree_on_sub. Qed.
Ltac u64x AG H := apply (L5C.u64_at_agree segs M M'); [eapply ag_sub; [exact AG|lia|lia]|lia|lia|exact H].
Ltac u32x AG H := apply u32_at_agree; [eapply ag_sub; [exact AG|lia|lia]|lia|lia|exact H].
Ltac u8x AG H := apply (L5C.u8_at_agree segs M M'); [eapply ag_sub; [exact AG|lia|lia]|lia|lia|exact H].
Ltac defx AG H := apply (L5C.defined_agree M M' _ _); [eapply ag_sub; [exact AG|lia|lia]|exact H].

Lemma iosb_at_agree o vp rdb st : 0 <= o -> o + 152 <= 2 ^ 64 -> ag o 152 -> PM.iosb_at segs A T3 M o vp rdb st -> PM.iosb_at segs A T3 M' o vp rdb st.
Proof.
  intros Ho Ho' AG (H0 & H32 & H36 & H40 & H48 & Z & D & _ & ST).
  split; [u64x AG H0|]. split; [u32x AG H32|]. split; [u32x AG H36|]. split; [u64x AG H40|]. split; [u64x AG H48|].
  split; [apply zeros_at_agree; [eapply ag_sub; [exact AG|lia|lia]|exact Z]|]. split; [defx AG D|]. split; [exact I| exact ST].
Qed.

Lemma nullis_at_agree o : 0 <= o -> o + 232 <= 2 ^ 64 -> ag o 232 -> PM.nullis_at segs A T3 M o -> PM.nullis_at segs A T3 M' o.
Proof.
  intros Ho Ho' AG (H0 & D & _ & H16 & H24 & IOS).
  split; [u64x AG H0|]. split; [defx AG D|]. split; [exact I|]. split; [u64x AG H16|]. split; [u64x AG H24|].
  apply iosb_at_agree; [lia|lia| eapply ag_sub; [exact AG|lia|lia]| exact IOS].
Qed.

Lemma src_fields_at_agree os isp sbp src : 0 <= os -> os + 296 <= 2 ^ 64 -> 0 <= PM.sr_qc src -> PM.sr_qc src + PM.CHUNK <= 2 ^ 64 ->
  ag (os + 240) 56 -> ag (PM.sr_qc src) PM.CHUNK ->
  PM.src_fields_at segs T3 M os isp sbp src -> PM.src_fields_at segs T3 M' os isp sbp src.
Proof.
  intros Ho Ho' Hq Hq' AG AGC (F1 & F2 & F3 & F4 & F5 & F6 & F7 & B1 & B2 & B3 & B4 & DC & _ & _).
  split; [u64x AG F1|]. split; [u64x AG F2|]. split; [defx AG F3|]. split; [u64x AG F4|]. split; [u64x AG F5|]. split; [u64x AG F6|]. split; [u64x AG F7|].
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
  split; [apply (L5C.defined_agree M M' _ _ AGC DC)|]. split; exact I.
Qed.

Lemma iss_at_agree ois str sm : 0 <= ois -> ois + 272 <= 2 ^ 64 -> ag ois 272 -> (forall c n p, str = PM.VLong c n p -> ag p c) ->
  PM.iss_at segs A T3 M ois str sm -> PM.iss_at segs A T3 M' ois str sm.
Proof.
  intros Ho Ho' AG AGB (H0 & D & _ & H16 & H24 & H32 & H40 & H48 & H64 & VS & H104 & H112 & IOS & E1 & E2).
  split; [u64x AG H0|]. split; [defx AG D|]. split; [exact I|]. split; [u64x AG H16|]. split; [u64x AG H24|]. split; [u64x AG H32|].
  split; [u64x AG H40|]. split; [u64x AG H48|]. split; [u64x AG H64|].
  split; [apply vstr_at_agree; [lia|lia| eapply ag_sub; [exact AG|lia|lia]| exact AGB| exact VS]|].
  split; [u64x AG H104|]. split; [u32x AG H112|].
  split; [apply iosb_at_agree; [lia|lia| eapply ag_sub; [exact AG|lia|lia]| exact IOS]|]. split; [exact E1| exact E2].
Qed.

Lemma parser_at_agree op ois s : 0 <= op -> op + 384 <= 2 ^ 64 -> ag op 384 ->
  0 <= PM.sr_qc (PM.p_src s) -> PM.sr_qc (PM.p_src s) + PM.CHUNK <= 2 ^ 64 -> ag (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> ag (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> ag p c) ->
  PM.parser_at segs A T3 T4 M op ois s -> PM.parser_at segs A T3 T4 M' op ois s.
Proof.
  intros Ho Ho' AG Hq Hq' AGC Hb Hb' AGV AGT (H0 & D & _ & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & _ & TB & VEC & B1 & B2 & B3).
  split; [u64x AG H0|]. split; [defx AG D|]. split; [exact I|]. split; [u8x AG H8|]. split; [u8x AG H9|]. split; [u32x AG H12|].
  split; [u8x AG H16|]. split; [u32x AG H20|].
  split; [apply nullis_at_agree; [lia|lia| eapply ag_sub; [exact AG|lia|lia]| exact NI]|].
  split; [apply src_fields_at_agree; [lia|lia|exact Hq|exact Hq'| eapply ag_sub; [exact AG|lia|lia]| exact AGC| exact SRC]|].
  split; [u32x AG H320|]. split; [u64x AG H328|]. split; [exact I|].
  split; [apply vstr_at_agree; [lia|lia| eapply ag_sub; [exact AG|lia|lia]| exact AGT| exact TB]|].
  split; [apply vec_at_agree; [lia|lia|exact Hb|exact Hb'| eapply ag_sub; [exact AG|lia|lia]| exact AGV| exact VEC]|].
  split; [exact B1|]. split; [exact B2| exact B3].
Qed.

End Agree.
End PMF.
