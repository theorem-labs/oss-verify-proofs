(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA HeapIfaceABx L5Defs L5Core PmLayout PmModel PmModelFacts HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMFA.
Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.

Section Agree.
Variable segs : list Segment.
Variable A : pm_addrs.
Variables M M' : word -> option byte.

Abbreviation ag := (L5C.agree_on M M').
(* [comment removed for export] *)
Definition agsh (a n : Z) : Prop := forall x, a <= x < a + n -> M' (Z_to_bv 64 (S x)) = M (Z_to_bv 64 (S x)).
Definition agA (a n : Z) : Prop := ag a n /\ agsh a n.

Lemma agsh_sub a n a' n' : agsh a n -> a <= a' -> a' + n' <= a + n -> agsh a' n'.
Proof. intros H H1 H2 x Hx. apply H. lia. Qed.
Lemma agA_sub a n a' n' : agA a n -> a <= a' -> a' + n' <= a + n -> agA a' n'.
Proof. intros [G S] H1 H2. split; [eapply (L5C.agree_on_sub M M' a n); [exact G|lia|lia] | exact (agsh_sub a n a' n' S H1 H2)]. Qed.

Lemma aacc_agree a n : agsh a n -> aacc M a n -> aacc M' a n.
Proof.
  intros H C x Hx. unfold byte_at in *. rewrite (H x Hx). exact (C x Hx).
Qed.
Lemma accA_agree a n : agsh a n -> accA M a n -> accA M' a n.
Proof. apply aacc_agree. Qed.

(* [comment removed for export] *)
Lemma S_granule b j : b mod 8 = 0 -> 0 <= j -> S b + j = S (b + 8 * j).
Proof. intros Hb Hj. unfold S. rewrite <- Z.add_assoc, (Z.add_comm SB j), Z.add_assoc. f_equal.
  replace (b + 8 * j) with (j * 8 + b) by lia. rewrite Z.div_add_l by lia. lia. Qed.

Lemma annA_agree b u c : b mod 8 = 0 -> 0 <= u <= c -> c mod 8 = 0 -> agsh b c -> annA M b u c -> annA M' b u c.
Proof.
  intros Hb Hu Hc H (Z1 & Zm & Z2).
  assert (C8 : 8 * (c / 8) = c) by (pose proof (Z.div_mod c 8 ltac:(lia)); lia).
  assert (U8 : u / 8 <= c / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_mod u 8 ltac:(lia)) as UD. pose proof (Z.mod_pos_bound u 8 ltac:(lia)) as UM.
  assert (C78 : (c + 7) / 8 = c / 8) by (rewrite <- C8 at 1; replace (8 * (c / 8) + 7) with (7 + (c / 8) * 8) by lia; rewrite Z.div_add by lia; reflexivity).
  split; [|split].
  - intros j Hj. unfold byte_at in *. rewrite (S_granule b j Hb ltac:(lia)). rewrite H by lia.
    rewrite <- (S_granule b j Hb ltac:(lia)). exact (Z1 j Hj).
  - intros Hm. unfold byte_at in *. rewrite (S_granule b (u / 8) Hb ltac:(lia)).
    assert (u < c) by (destruct (Z.eq_dec u c) as [E|N]; [exfalso; apply Hm; rewrite E; exact Hc| lia]).
    rewrite H by lia. rewrite <- (S_granule b (u / 8) Hb ltac:(lia)). exact (Zm Hm).
  - intros j Hj. rewrite C78 in Hj. pose proof (Z.div_le_mono u (u + 7) 8 ltac:(lia) ltac:(lia)) as U7.
    unfold byte_at in *. rewrite (S_granule b j Hb ltac:(lia)). rewrite H by lia.
    rewrite <- (S_granule b j Hb ltac:(lia)). apply Z2. rewrite C78. exact Hj.
Qed.

Lemma mod16_8 b : b mod 16 = 0 -> b mod 8 = 0.
Proof. intros H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 16) with ((q * 2) * 8) by lia. apply Z_mod_mult. Qed.
Lemma blk8 k : (32 * 2 ^ k) mod 8 = 0.
Proof. replace (32 * 2 ^ k) with ((4 * 2 ^ k) * 8) by lia. apply Z_mod_mult. Qed.

Ltac u64x AG H := apply (L5C.u64_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact H].
Ltac u32x AG H := apply (PMF.u32_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact H].
Ltac u8x AG H := apply (L5C.u8_at_agree segs M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|lia|lia|exact H].
Ltac defx AG H := apply (L5C.defined_agree M M' _ _); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|exact H].
Ltac accx SH H := apply accA_agree; [eapply agsh_sub; [exact SH|lia|lia]|exact H].

Lemma vstr_at_agreeA o s : 0 <= o -> o + 24 <= 2 ^ 64 -> agA o 24 ->
  (forall c n p, s = PM.VLong c n p -> agA p c) ->
  PM.vstr_at segs accA M o s -> PM.vstr_at segs accA M' o s.
Proof.
  intros Ho Ho' [AG SH] AGB (D & C & H). split; [apply (L5C.defined_agree M M' o 24 AG D)|]. split; [accx SH C|].
  destruct s as [n|c n p].
  - destruct H as (Hn & B0). split; [exact Hn|]. u8x AG B0.
  - destruct H as (W0 & W8 & W16 & Hn & Hc & He & DB & CB). destruct (AGB c n p eq_refl) as [AGp SHp].
    split; [u64x AG W0|]. split; [u64x AG W8|]. split; [u64x AG W16|]. split; [exact Hn|]. split; [exact Hc|]. split; [exact He|].
    split; [apply (L5C.defined_agree M M' p c AGp DB)|]. accx SHp CB.
Qed.

Lemma vec_at_agreeA v b k stk : 0 <= v -> v + 24 <= 2 ^ 64 -> 0 <= b -> b + 32 * 2 ^ k <= 2 ^ 64 -> L5C.agree_on M M' v 24 -> agA b (32 * 2 ^ k) ->
  PM.vec_at segs accA annA M v b k stk -> PM.vec_at segs accA annA M' v b k stk.
Proof.
  intros Hv Hv' Hb Hb' AGV [AGB SHB] (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AN & EL).
  pose proof (PM.pow2_pos k ltac:(lia)) as P2.
  split; [u64x AGV V0|]. split; [u64x AGV V8|]. split; [u64x AGV V16|].
  split; [exact Hk|]. split; [exact Hlen|]. split; [exact Hal|].
  split; [apply (L5C.defined_agree M M' b _ AGB DB)|]. split; [accx SHB CB|].
  split; [apply annA_agree; [exact (mod16_8 b Hal)| lia| apply blk8| exact SHB| exact AN]|].
  intros n Hn. apply (PMF.pstate_at_agree segs M M'); [lia|lia| |apply EL; exact Hn].
  assert (Z.of_nat n < Z.of_nat (length stk)) by (apply Nat2Z.inj_lt; exact Hn).
  eapply (L5C.agree_on_sub M M' b (32 * 2 ^ k)); [exact AGB|lia|lia].
Qed.

Lemma iosb_at_agreeA o vp rdb st : 0 <= o -> o + 152 <= 2 ^ 64 -> agA o 152 ->
  PM.iosb_at segs A accA M o vp rdb st -> PM.iosb_at segs A accA M' o vp rdb st.
Proof.
  intros Ho Ho' [AG SH] (H0 & H32 & H36 & H40 & H48 & Z & D & C & ST).
  split; [u64x AG H0|]. split; [u32x AG H32|]. split; [u32x AG H36|]. split; [u64x AG H40|]. split; [u64x AG H48|].
  split; [apply (PMF.zeros_at_agree M M'); [eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]|exact Z]|]. split; [defx AG D|].
  split; [accx SH C| exact ST].
Qed.

Lemma nullis_at_agreeA o : 0 <= o -> o + 232 <= 2 ^ 64 -> agA o 232 -> PM.nullis_at segs A accA M o -> PM.nullis_at segs A accA M' o.
Proof.
  intros Ho Ho' AGa (H0 & D & C & H16 & H24 & IOS). destruct AGa as [AG SH] eqn:EA.
  split; [u64x AG H0|]. split; [defx AG D|]. split; [accx SH C|]. split; [u64x AG H16|]. split; [u64x AG H24|].
  apply iosb_at_agreeA; [lia|lia| eapply agA_sub; [exact AGa|lia|lia]| exact IOS].
Qed.

Lemma src_fields_at_agreeA os isp sbp src : 0 <= os -> os + 296 <= 2 ^ 64 -> 0 <= PM.sr_qc src -> PM.sr_qc src + PM.CHUNK <= 2 ^ 64 ->
  agA (os + 240) 56 -> agA (PM.sr_qc src) PM.CHUNK ->
  PM.src_fields_at segs accA M os isp sbp src -> PM.src_fields_at segs accA M' os isp sbp src.
Proof.
  intros Ho Ho' Hq Hq' [AG SH] [AGC SHC] (F1 & F2 & F3 & F4 & F5 & F6 & F7 & B1 & B2 & B3 & B4 & DC & CC & CS).
  split; [u64x AG F1|]. split; [u64x AG F2|]. split; [defx AG F3|]. split; [u64x AG F4|]. split; [u64x AG F5|]. split; [u64x AG F6|]. split; [u64x AG F7|].
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|].
  split; [apply (L5C.defined_agree M M' _ _ AGC DC)|]. split; [accx SHC CC| accx SH CS].
Qed.

Lemma iss_at_agreeA ois str sm : 0 <= ois -> ois + 272 <= 2 ^ 64 -> agA ois 272 -> (forall c n p, str = PM.VLong c n p -> agA p c) ->
  PM.iss_at segs A accA M ois str sm -> PM.iss_at segs A accA M' ois str sm.
Proof.
  intros Ho Ho' AGa AGB (H0 & D & C & H16 & H24 & H32 & H40 & H48 & H64 & VS & H104 & H112 & IOS & E1 & E2). destruct AGa as [AG SH] eqn:EA.
  split; [u64x AG H0|]. split; [defx AG D|]. split; [accx SH C|]. split; [u64x AG H16|]. split; [u64x AG H24|]. split; [u64x AG H32|].
  split; [u64x AG H40|]. split; [u64x AG H48|]. split; [u64x AG H64|].
  split; [apply vstr_at_agreeA; [lia|lia| eapply agA_sub; [exact AGa|lia|lia]| exact AGB| exact VS]|].
  split; [u64x AG H104|]. split; [u32x AG H112|].
  split; [apply iosb_at_agreeA; [lia|lia| eapply agA_sub; [exact AGa|lia|lia]| exact IOS]|]. split; [exact E1| exact E2].
Qed.

Lemma parser_at_agreeA op ois s : 0 <= op -> op + 384 <= 2 ^ 64 -> agA op 384 ->
  0 <= PM.sr_qc (PM.p_src s) -> PM.sr_qc (PM.p_src s) + PM.CHUNK <= 2 ^ 64 -> agA (PM.sr_qc (PM.p_src s)) PM.CHUNK ->
  0 <= PM.p_b s -> PM.p_b s + 32 * 2 ^ PM.p_k s <= 2 ^ 64 -> agA (PM.p_b s) (32 * 2 ^ PM.p_k s) ->
  (forall c n p, PM.p_tb s = PM.VLong c n p -> agA p c) ->
  PM.parser_at segs A accA annA M op ois s -> PM.parser_at segs A accA annA M' op ois s.
Proof.
  intros Ho Ho' AGa Hq Hq' AGC Hb Hb' AGV AGT (H0 & D & C0 & H8 & H9 & H12 & H16 & H20 & NI & SRC & H320 & H328 & C320 & TB & VEC & B1 & B2 & B3).
  destruct AGa as [AG SH] eqn:EA.
  split; [u64x AG H0|]. split; [defx AG D|]. split; [accx SH C0|]. split; [u8x AG H8|]. split; [u8x AG H9|]. split; [u32x AG H12|].
  split; [u8x AG H16|]. split; [u32x AG H20|].
  split; [apply nullis_at_agreeA; [lia|lia| eapply agA_sub; [exact AGa|lia|lia]| exact NI]|].
  split; [apply src_fields_at_agreeA; [lia|lia|exact Hq|exact Hq'| eapply agA_sub; [exact AGa|lia|lia]| exact AGC| exact SRC]|].
  split; [u32x AG H320|]. split; [u64x AG H328|]. split; [accx SH C320|].
  split; [apply vstr_at_agreeA; [lia|lia| eapply agA_sub; [exact AGa|lia|lia]| exact AGT| exact TB]|].
  split; [apply vec_at_agreeA; [lia|lia|exact Hb|exact Hb'| eapply (L5C.agree_on_sub M M'); [exact AG|lia|lia]| exact AGV| exact VEC]|].
  split; [exact B1|]. split; [exact B2| exact B3].
Qed.

End Agree.
End PMFA.
