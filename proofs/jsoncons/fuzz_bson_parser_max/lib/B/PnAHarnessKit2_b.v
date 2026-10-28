(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec StoreOk HeapIface HeapIfaceA L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx
     L5KnA PmLayout PmLayoutA PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PnStatics PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PmModelFactsA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc PgV8 PnModel PnModelFacts. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnBrObjA_b PnStepA_b PnAHarnessKit_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PNHAK2.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition hf (F : Z) : Prop := F mod 8 = 0 /\ 0 <= F /\ F + 2048 <= 2 ^ 47 /\ (BIGSHADOW_HI <= F \/ F + 2048 <= BIGSHADOW_LO).
(* [comment removed for export] *)
Definition pfoot (F slo shi : Z) (Wp : Z -> Prop) : Prop :=
  forall a, Wp a -> (F <= a < F + 2048) \/ (F / 8 + HeapIfaceA.SB <= a < F / 8 + HeapIfaceA.SB + 256) \/ (slo <= a < shi).
(* [comment removed for export] *)
Definition wfi (F : Z) (Wc : list L5.range) : Prop :=
  forall r, In r Wc -> (F <= fst r /\ fst r + snd r <= F + 2048) \/ (65536 <= fst r /\ fst r + snd r <= 0x696000).
Definition wapart (Wc : list L5.range) (o n : Z) : Prop := forall r, In r Wc -> fst r + snd r <= o \/ o + n <= fst r.
Lemma wfi_nil F : wfi F [].
Proof. intros r []. Qed.
Lemma wfi_cons F r Wc : ((F <= fst r /\ fst r + snd r <= F + 2048) \/ (65536 <= fst r /\ fst r + snd r <= 0x696000)) -> wfi F Wc -> wfi F (r :: Wc).
Proof. intros H W r' [<-|Hr]; [exact H| exact (W r' Hr)]. Qed.
Lemma wfi_app F W1 W2 : wfi F W1 -> wfi F W2 -> wfi F (W1 ++ W2).
Proof. intros A B r Hr. apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [exact (A r Hr)| exact (B r Hr)]. Qed.
Lemma wapart_nil o n : wapart [] o n.
Proof. intros r []. Qed.
Lemma wapart_cons r Wc o n : (fst r + snd r <= o \/ o + n <= fst r) -> wapart Wc o n -> wapart (r :: Wc) o n.
Proof. intros H W r' [<-|Hr]; [exact H| exact (W r' Hr)]. Qed.
Lemma wapart_app W1 W2 o n : wapart W1 o n -> wapart W2 o n -> wapart (W1 ++ W2) o n.
Proof. intros A B r Hr. apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [exact (A r Hr)| exact (B r Hr)]. Qed.

(* [comment removed for export] *)
Lemma u64_agA (M1 M2 : word -> option byte) o n a v : PMFA.agA M1 M2 o n -> o <= a -> a + 8 <= o + n -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS M2 a v.
Proof. intros (AG & _) H1 H2 H3 H4. apply (L5C.u64_at_agree RSEGS M1 M2 a v); [intros i Hi; apply AG; lia| lia| lia]. Qed.
Lemma u32_agA (M1 M2 : word -> option byte) o n a v : PMFA.agA M1 M2 o n -> o <= a -> a + 4 <= o + n -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M1 a v -> L5.u32_at RSEGS M2 a v.
Proof. intros (AG & _) H1 H2 H3 H4. apply (PNHAK.u32_agree M1 M2 a v); [intros i Hi; apply AG; lia| lia| lia]. Qed.
Lemma shz_agA (M1 M2 : word -> option byte) o n a g : PMFA.agA M1 M2 o n -> o <= a -> a + 8 * g <= o + n -> a mod 8 = 0 -> 0 <= g ->
  shadow_zero M1 a g -> shadow_zero M2 a g.
Proof.
  intros (_ & SH) H1 H2 H3 H4 SZ j Hj. unfold byte_at in *. specialize (SZ j Hj).
  rewrite (PMFA.S_granule a j H3 ltac:(lia)) in SZ |- *. rewrite (SH (a + 8 * j) ltac:(lia)). exact SZ.
Qed.
Lemma defined_agA (M1 M2 : word -> option byte) o n a k : PMFA.agA M1 M2 o n -> o <= a -> a + k <= o + n ->
  L5.defined M1 a k -> L5.defined M2 a k.
Proof. intros (AG & _) H1 H2 D i Hi. rewrite AG by lia. apply D. exact Hi. Qed.

Lemma zeros_of_shz (M : word -> option byte) o g : shadow_zero M o g -> L5KA.zeros_at M (HeapIfaceA.S o) g.
Proof. intros SZ i Hi. exact (SZ i Hi). Qed.


(* [comment removed for export] *)
Abbreviation bparser_at := (PNM.bparser_at RSEGS PMA.AD PMSPA.accA PMSPA.annA (pa_vp_parser PMA.AD)).
Abbreviation v8_at := (PGV8.v8_at RSEGS PMSPA.accA PMSPA.annA).
Abbreviation bvec_at := (PNM.bvec_at RSEGS PMSPA.accA PMSPA.annA).
Definition hbase (F : Z) (M : word -> option byte) (s s' : PM.vstr) (sm : PM.strm) : Prop :=
  PM.vstr_at RSEGS PMSPA.accA M (F + 32) s /\ PM.iss_at RSEGS PMA.AD PMSPA.accA M (F + 96) s' sm
  /\ L5.u64_at RSEGS M (F + 432) (pa_vp_visitor PMA.AD) /\ shadow_zero M (F + 432) 1 /\ shadow_zero M (F + 96) 34.
Definition hpar (F : Z) (M : word -> option byte) (ps : PNM.bpst) : Prop :=
  bparser_at M (F + 464) (F + 96) ps /\ L5.u64_at RSEGS M (F + 880) (F + 432) /\ PMSPA.accA M (F + 464) 424.
Definition hec (F : Z) (M : word -> option byte) (v c : Z) : Prop :=
  L5.u32_at RSEGS M (F + 1024) v /\ L5.u64_at RSEGS M (F + 1032) c /\ shadow_zero M (F + 1024) 2 /\ L5.defined M (F + 1024) 16.

Lemma shz_frame (M1 M2 : word -> option byte) (Wp : Z -> Prop) o g :
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> (forall j, 0 <= j < g -> ~ Wp (HeapIfaceA.S o + j)) ->
  0 <= HeapIfaceA.S o -> HeapIfaceA.S o + g <= 2 ^ 64 -> shadow_zero M1 o g -> shadow_zero M2 o g.
Proof. intros FR W H0 H1 SZ j Hj. unfold byte_at. rewrite FR; [exact (SZ j Hj)| lia| exact (W j Hj)]. Qed.
(* [comment removed for export] *)
Lemma acc_of_shz (M : word -> option byte) o g a n : shadow_zero M o g -> o mod 8 = 0 -> 0 <= o -> o <= a -> a + n <= o + 8 * g -> PMSPA.accA M a n.
Proof.
  intros SZ Ho Hp H1 H2 x Hx. left. unfold shadow_zero, byte_at, HeapIfaceA.S in *.
  set (q := o / 8) in *. pose proof (Z.div_mod o 8 ltac:(lia)) as Do. rewrite Ho, Z.add_0_r in Do. fold q in Do.
  specialize (SZ (x / 8 - q)). replace (q + SB + (x / 8 - q)) with (x / 8 + SB) in SZ by lia. apply SZ.
  pose proof (Z.div_le_mono o x 8 ltac:(lia) ltac:(lia)) as L1. rewrite Do in L1 at 1. rewrite Z.mul_comm, Z.div_mul in L1 by lia.
  assert (x / 8 < q + g); [| lia]. apply Z.div_lt_upper_bound; [lia|]. lia.
Qed.
Lemma shz_of_acc (M : word -> option byte) o g : PMSPA.accA M o (8 * g) -> o mod 8 = 0 -> 0 <= o -> shadow_zero M o g.
Proof.
  intros C Ho Hp j Hj. unfold PMSPA.accA, aacc in C. unfold byte_at, HeapIfaceA.S in *.
  set (q := o / 8) in *. pose proof (Z.div_mod o 8 ltac:(lia)) as Do. rewrite Ho, Z.add_0_r in Do. fold q in Do.
  destruct (C (o + 8 * j + 7) ltac:(lia)) as [Z0|(v & Bv & Rv & Mv)].
  - replace ((o + 8 * j + 7) / 8) with (q + j) in Z0; [replace (q + SB + j) with (q + j + SB) by lia; exact Z0|].
    rewrite Do. replace (8 * q + 8 * j + 7) with (7 + (q + j) * 8) by lia. rewrite Z.div_add by lia. reflexivity.
  - exfalso. rewrite Do in Mv. replace (8 * q + 8 * j + 7) with (7 + (q + j) * 8) in Mv by lia. rewrite Z_mod_plus_full in Mv. change (7 mod 8) with 7 in Mv. lia.
Qed.

(* [comment removed for export] *)
Definition hsrc (F : Z) (M : word -> option byte) (src : PM.srcst) : Prop :=
  PM.src_fields_at RSEGS PMSPA.accA M (F + 480) (F + 96) (F + 112) src /\ PM.nullis_at RSEGS PMA.AD PMSPA.accA M (F + 488).
Definition hvec (F : Z) (M : word -> option byte) (b k : Z) (stk : list PNM.bstate) : Prop :=
  bvec_at M (F + 856) b k stk /\ L5.defined M (F + 856) 24 /\ PMSPA.accA M (F + 856) 24.
Lemma hdead_of_parser (M : word -> option byte) F ps :
  hpar F M ps ->
  hsrc F M (PNM.b_src ps) /\ PM.vstr_at RSEGS PMSPA.accA M (F + 832) (PNM.b_tb ps) /\ PM.vstr_at RSEGS PMSPA.accA M (F + 808) (PNM.b_nb ps)
  /\ v8_at M (F + 784) (PNM.b_bb ps) /\ hvec F M (PNM.b_sb ps) (PNM.b_sk ps) (PNM.b_stk ps).
Proof.
  intros ((P0 & D & C0 & P8 & P9 & P10 & P12 & NI & SRC & P312 & C312 & BB & NB & TB & VEC & _) & _ & ACC).
  unfold PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK, PNM.PSIZE in *.
  replace (F + 464 + 16 + 8) with (F + 488) in NI by lia. replace (F + 464 + 16) with (F + 480) in SRC by lia. replace (F + 96 + 16) with (F + 112) in SRC by lia.
  replace (F + 464 + 368) with (F + 832) in TB by lia. replace (F + 464 + 344) with (F + 808) in NB by lia.
  replace (F + 464 + 320) with (F + 784) in BB by lia. replace (F + 464 + 392) with (F + 856) in VEC by lia.
  split; [split; [exact SRC| exact NI]|]. split; [exact TB|]. split; [exact NB|]. split; [exact BB|]. split; [exact VEC|]. split.
  - apply (L5.defined_sub M (F + 464) 416 (F + 856) 24 D); lia.
  - intros x Hx. apply ACC. lia.
Qed.

(* [comment removed for export] *)
Lemma iosb_revptr (M1 M2 : word -> option byte) o vp vp' rdb st :
  PM.iosb_at RSEGS PMA.AD PMSPA.accA M1 o vp rdb st -> L5.u64_at RSEGS M2 o vp' ->
  L5C.agree_on M1 M2 (o + 8) 144 -> PMFA.agsh M1 M2 o 152 -> L5.defined M2 o 8 -> 0 <= o -> o + 152 <= 2 ^ 64 ->
  PM.iosb_at RSEGS PMA.AD PMSPA.accA M2 o vp' rdb st.
Proof.
  intros (H0 & H32 & H36 & H40 & H48 & Z & D & C & ST) U AG SH D8 Ho Ho'.
  split; [exact U|]. split; [apply (PNHAK.u32_agree M1 M2 (o + 32) st); [intros i Hi; apply AG; lia| lia| lia| exact H32]|].
  split; [apply (PNHAK.u32_agree M1 M2 (o + 36) 0); [intros i Hi; apply AG; lia| lia| lia| exact H36]|].
  split; [apply (L5C.u64_at_agree RSEGS M1 M2 (o + 40) rdb); [intros i Hi; apply AG; lia| lia| lia| exact H40]|].
  split; [apply (L5C.u64_at_agree RSEGS M1 M2 (o + 48) _); [intros i Hi; apply AG; lia| lia| lia| exact H48]|].
  split; [apply (PMF.zeros_at_agree M1 M2); [intros i Hi; apply AG; lia| exact Z]|].
  split; [intros i Hi; destruct (Z.lt_ge_cases i 8) as [Y|Y]; [apply (D8 i); lia| rewrite AG by lia; apply (D i Hi)]|].
  split; [apply (PMFA.accA_agree M1 M2 o 152 SH C)| exact ST].
Qed.

(* [comment removed for export] *)
Definition hfin (F : Z) (M : word -> option byte) (s : PM.vstr) (st : Z) : Prop :=
  PM.vstr_at RSEGS PMSPA.accA M (F + 32) s /\ L5.u64_at RSEGS M (F + 120) (pa_classic_imp PMA.AD)
  /\ PM.iosb_at RSEGS PMA.AD PMSPA.accA M (F + 216) (pa_vp_iss_ios PMA.AD) (F + 112) st.

(* [comment removed for export] *)
Section AgreeB.
Variables M1 M2 : word -> option byte.
Let NT := fun i : Z => M2 (Z_to_bv 64 i) = M1 (Z_to_bv 64 i).
Let Y := fun i : Z => M1 (Z_to_bv 64 i) <> None -> M2 (Z_to_bv 64 i) <> None.
Let NS := fun i : Z => M2 (Z_to_bv 64 (HeapIfaceA.S i)) = M1 (Z_to_bv 64 (HeapIfaceA.S i)).
Lemma AGXp : forall a n, 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> NT i) -> L5C.agree_on M1 M2 a n.
Proof. intros a n _ _ H i Hi. exact (H i Hi). Qed.
Lemma DKYp : forall i, Y i -> M1 (Z_to_bv 64 i) <> None -> M2 (Z_to_bv 64 i) <> None.
Proof. intros i H. exact H. Qed.
Lemma SHXp : forall a n, (forall i, a <= i < a + n -> NS i) -> PMFA.agsh M1 M2 a n.
Proof. intros a n H i Hi. exact (H i Hi). Qed.
Lemma NT_of_agA o n i : PMFA.agA M1 M2 o n -> o <= i < o + n -> NT i.
Proof. intros [AG _] Hi. exact (AG i Hi). Qed.
Lemma Y_of_agA o n i : PMFA.agA M1 M2 o n -> o <= i < o + n -> Y i.
Proof. intros [AG _] Hi D. unfold NT in *. rewrite (AG i Hi). exact D. Qed.
Lemma NS_of_agA o n i : PMFA.agA M1 M2 o n -> o <= i < o + n -> NS i.
Proof. intros [_ SH] Hi. exact (SH i Hi). Qed.
(* [comment removed for export] *)
Lemma NS_gspan b c i : b mod 8 = 0 -> 0 < c -> PMFA.agsh M1 M2 b c -> b <= i < b + PNBOA.gspan c -> NS i.
Proof.
  intros Hb Hc SH Hi. unfold NS. destruct (Z.lt_ge_cases i (b + c)) as [L|G]; [exact (SH i ltac:(lia))|].
  unfold PNBOA.gspan in Hi. set (q := b / 8) in *. pose proof (Z.div_mod b 8 ltac:(lia)) as Db. rewrite Hb, Z.add_0_r in Db. fold q in Db.
  pose proof (Z.div_mod (c + 7) 8 ltac:(lia)) as D7. pose proof (Z.mod_pos_bound (c + 7) 8 ltac:(lia)) as M7.
  pose proof (Z.div_mod (c - 1) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (c - 1) 8 ltac:(lia)) as M1'.
  assert (E : HeapIfaceA.S i = HeapIfaceA.S (b + c - 1)).
  { unfold HeapIfaceA.S. f_equal. rewrite Db.
    replace (8 * q + c - 1) with ((c - 1) + q * 8) by lia. rewrite Z.div_add by lia.
    assert (X : i = 8 * q + (i - b)) by lia. rewrite X. replace (8 * q + (i - b)) with ((i - b) + q * 8) by lia. rewrite Z.div_add by lia.
    assert ((i - b) / 8 = (c - 1) / 8); [| lia].
    pose proof (Z.div_mod (i - b) 8 ltac:(lia)) as Di. pose proof (Z.mod_pos_bound (i - b) 8 ltac:(lia)) as Mi. nia. }
  rewrite E. exact (SH (b + c - 1) ltac:(lia)).
Qed.

Lemma v8_at_agreeA v x : 0 <= v -> v + 24 <= 2 ^ 64 -> PMFA.agA M1 M2 v 24 ->
  (forall b n c, x = PGV8.V8Blk b n c -> PMFA.agA M1 M2 b c) -> v8_at M1 v x -> v8_at M2 v x.
Proof.
  intros H1 H2 AG AB V8. pose proof V8 as (_ & _ & R).
  apply (PNBOA.v8_keep_x RSEGS M1 M2 NT Y NS AGXp DKYp SHXp v x H1 H2); [| | | | exact V8].
  - intros i Hi. exact (NT_of_agA _ _ i AG Hi).
  - intros i Hi. exact (NS_of_agA _ _ i AG Hi).
  - intros B m Hin i Hi. destruct x as [|b n c]; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
    exact (Y_of_agA _ _ i (AB b n c eq_refl) Hi).
  - intros B m Hin i Hi. destruct x as [|b n c]; cbn in Hin; [destruct Hin|]. destruct Hin as [E0|[]]. injection E0 as <- <-.
    destruct R as (_ & _ & _ & Hn & Hc & Hb & Hal & _). apply (NS_gspan b c i); [| lia| exact (proj2 (AB b n c eq_refl))| exact Hi].
    pose proof (Z.mod_divide b 16 ltac:(lia)) as [X _]. destruct (X Hal) as (q & Hq). rewrite Hq. replace (q * 16) with ((q * 2) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma bvec_at_agreeA v b k stk : 0 <= v -> v + 24 <= 2 ^ 64 -> 0 <= b -> b + PNM.BSZ * 2 ^ k <= 2 ^ 64 ->
  L5C.agree_on M1 M2 v 24 -> PMFA.agA M1 M2 b (PNM.BSZ * 2 ^ k) -> bvec_at M1 v b k stk -> bvec_at M2 v b k stk.
Proof.
  intros H1 H2 H3 H4 AG AGB VE.
  apply (PNBOA.bvec_keep_x RSEGS M1 M2 NT NS AGXp SHXp v b k stk H1 H2 H3 H4); [| | | exact VE].
  - intros i Hi. exact (AG i Hi).
  - intros i Hi. exact (NT_of_agA _ _ i AGB Hi).
  - intros i Hi. exact (NS_of_agA _ _ i AGB Hi).
Qed.
Lemma bparser_at_agreeA op ois s : 0 <= op -> op + PNM.PSIZE <= 2 ^ 64 -> PMFA.agA M1 M2 op PNM.PSIZE ->
  PMFA.agA M1 M2 (PM.sr_qc (PNM.b_src s)) PM.CHUNK -> 0 <= PM.sr_qc (PNM.b_src s) -> PM.sr_qc (PNM.b_src s) + PM.CHUNK <= 2 ^ 64 ->
  PMFA.agA M1 M2 (PNM.b_sb s) (PNM.BSZ * 2 ^ PNM.b_sk s) -> 0 <= PNM.b_sb s -> PNM.b_sb s + PNM.BSZ * 2 ^ PNM.b_sk s <= 2 ^ 64 ->
  (forall b n c, PNM.b_bb s = PGV8.V8Blk b n c -> PMFA.agA M1 M2 b c) ->
  (forall c n p, PNM.b_nb s = PM.VLong c n p -> PMFA.agA M1 M2 p c) ->
  (forall c n p, PNM.b_tb s = PM.VLong c n p -> PMFA.agA M1 M2 p c) ->
  bparser_at M1 op ois s -> bparser_at M2 op ois s.
Proof.
  intros Ho Ho' AG AQ Q0 Q1 ASB B0 B1 ABB ANB ATB PA.
  pose proof PA as (_ & _ & _ & M8 & M9 & _ & _ & _ & SRC & _ & _ & BB & NB & TB & STK & M01 & D01).
  unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in *.
  apply (PNBOA.bparser_at_xfer RSEGS PMA.AD (pa_vp_parser PMA.AD) M1 M2 NT Y NS AGXp DKYp SHXp op ois s s Ho ltac:(unfold PNM.PSIZE; lia) PA);
    unfold PNM.PSIZE, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK.
  - intros i Hi. exact (Y_of_agA _ _ i AG Hi).
  - intros i Hi. exact (NS_of_agA _ _ i AG Hi).
  - intros i Hi. exact (NT_of_agA _ _ i AG ltac:(lia)).
  - intros i Hi. exact (NT_of_agA _ _ i AG ltac:(lia)).
  - intros i Hi. exact (NT_of_agA _ _ i AG ltac:(lia)).
  - intros i Hi. exact (NT_of_agA _ _ i AG ltac:(lia)).
  - apply (L5C.u8_at_agree RSEGS M1 M2); [intros i Hi; exact (NT_of_agA _ _ i AG ltac:(lia))| lia| lia| exact M8].
  - apply (L5C.u8_at_agree RSEGS M1 M2); [intros i Hi; exact (NT_of_agA _ _ i AG ltac:(lia))| lia| lia| exact M9].
  - exact M01.
  - exact D01.
  - apply (PNBOA.src_keep_x RSEGS M1 M2 NT NS AGXp SHXp); [lia| lia| lia| lia| | | | | exact SRC].
    + intros i Hi. exact (NT_of_agA _ _ i AG ltac:(lia)).
    + intros i Hi. exact (NT_of_agA _ _ i AQ Hi).
    + intros i Hi. exact (NS_of_agA _ _ i AG ltac:(lia)).
    + intros i Hi. exact (NS_of_agA _ _ i AQ Hi).
  - apply (v8_at_agreeA (op + 320) (PNM.b_bb s)); [lia| lia| eapply PMFA.agA_sub; [exact AG| lia| lia]| exact ABB| exact BB].
  - apply (PMFA.vstr_at_agreeA RSEGS M1 M2 (op + 344) (PNM.b_nb s)); [lia| lia| eapply PMFA.agA_sub; [exact AG| lia| lia]| exact ANB| exact NB].
  - apply (PMFA.vstr_at_agreeA RSEGS M1 M2 (op + 368) (PNM.b_tb s)); [lia| lia| eapply PMFA.agA_sub; [exact AG| lia| lia]| exact ATB| exact TB].
  - apply (bvec_at_agreeA (op + 392)); [lia| lia| lia| lia| intros i Hi; exact (NT_of_agA _ _ i AG ltac:(lia))| exact ASB| exact STK].
Qed.
End AgreeB.

Section K.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (scfg : SpuriousCfg) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C scfg HI.
Let LYa := PMA.ly_as0 L C LY.

(* [comment removed for export] *)
Lemma blk_piece LBx FFx LKx crx Ax Mx Vx (p c F rs slo shi : Z) (Wp : Z -> Prop) (M1 M2 : word -> option byte) :
  ri_inv HI LBx FFx LKx crx Ax Mx Vx -> In (p, c) LBx -> In (F, 5, rs) (FFx ++ LKx) -> hf F -> ahl_ceil ar <= slo -> BIGSHADOW_HI <= slo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> pfoot F slo shi Wp -> PMFA.agA M1 M2 p c.
Proof.
  intros HH Hin HF (F8 & F0 & F1 & FB) S1 S2 FR WP.
  exact (PNHAK.blk_agA L ar C scfg HI HIok LBx FFx LKx crx Ax Mx Vx p c F rs slo shi Wp M1 M2 HH Hin HF F8 F0 F1 FB S1 S2 FR WP).
Qed.
Lemma blk_callee LBx FFx LKx crx Ax Mx Vx (p c F rs : Z) LBc FFc spc scrc Wc (M1 M2 : word -> option byte) :
  ri_inv HI LBx FFx LKx crx Ax Mx Vx -> In (p, c) LBx -> In (F, 5, rs) (FFx ++ LKx) -> hf F ->
  L5CA.ahpres L ar LBc FFc spc scrc Wc M1 M2 -> In (p, c) LBc -> wfi F Wc -> PMFA.agA M1 M2 p c.
Proof.
  intros HH Hin HF (F8 & F0 & F1 & FB) AH Hc WF.
  destruct (PNHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ p c HH Hin) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
  pose proof (PFA (F, 5, rs) HF) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 5) with 2048 in PF.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in PIMG.
  apply (PNHAK.agA_ahpres_blk L ar LBc FFc spc scrc Wc M1 M2 p c AH Hc); [lia| lia|].
  intros x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in *.
  split; intros r Hr Hin'; unfold L5.in_rng in Hin'; destruct (WF r Hr) as [(W1 & W2)|(W1 & W2)]; lia.
Qed.

(* [comment removed for export] *)
Lemma ff_callee LBc FFc spc scrc Wc (M1 M2 : word -> option byte) f F o n :
  L5CA.ahpres L ar LBc FFc spc scrc Wc M1 M2 -> In f FFc -> ff_addr f + 32 <= o -> o + n <= ff_addr f + ff_bytes (ff_class f) - 8 ->
  hf F -> F <= o -> o + n <= F + 2048 -> wfi F Wc -> wapart Wc o n -> PMFA.agA M1 M2 o n.
Proof.
  intros AH Hf H1 H2 (F8 & F0 & F1 & FB) O1 O2 WF WA.
  apply (PNHAK.agA_ahpres_ff L ar LBc FFc spc scrc Wc M1 M2 f o n AH Hf H1 H2); [lia| lia|].
  intros x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in *.
  split; intros r Hr Hin'; unfold L5.in_rng in Hin'.
  - destruct (WA r Hr) as [Y|Y]; lia.
  - destruct (WF r Hr) as [(W1 & W2)|(W1 & W2)]; lia.
Qed.

(* [comment removed for export] *)
Lemma shz_callee LBc FFc spc scrc Wc (M1 M2 : word -> option byte) f F o g :
  L5CA.ahpres L ar LBc FFc spc scrc Wc M1 M2 -> In f FFc -> ff_addr f = F /\ ff_bytes (ff_class f) = 2048 -> hf F -> wfi F Wc ->
  F <= o -> o + 8 * g <= F + 2048 -> o mod 8 = 0 -> 0 <= g -> shadow_zero M1 o g -> shadow_zero M2 o g.
Proof.
  intros (AK & _ & _) Hf (E1 & E2) (F8 & F0 & F1 & FB) WF H1 H2 H3 H4 SZ j Hj. unfold byte_at in *. specialize (SZ j Hj).
  rewrite (PMFA.S_granule o j H3 ltac:(lia)) in SZ |- *.
  pose proof (PMKA.S_in_shadow (o + 8 * j) ltac:(lia)) as SX.
  rewrite AK; [exact SZ|]. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split.
  - right; right; right; right; right; left. exists f. split; [exact Hf|]. rewrite E1, E2. unfold in_shadow_of. split; apply PMKA.S_mono; lia.
  - intros r Hr Hin. unfold L5.in_rng in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX, FB. destruct (WF r Hr) as [(W1 & W2)|(W1 & W2)]; lia.
Qed.


Section Objs.
Variables (LBx : list (Z * Z)) (FFx LKx : list fframe) (crx : credit) (Ax : list (Z * Z)) (Mx : word -> option byte) (Vx : vml) (F rs : Z).
Hypothesis HH : ri_inv HI LBx FFx LKx crx Ax Mx Vx.
Hypothesis HF : In (F, 5, rs) (FFx ++ LKx).
Hypothesis HFF : hf F.

(* [comment removed for export] *)
Variables (slo shi : Z) (Wp : Z -> Prop) (M1 M2 : word -> option byte).
Hypothesis S1 : ahl_ceil ar <= slo.
Hypothesis S2 : BIGSHADOW_HI <= slo.
Hypothesis FR : forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a).
Hypothesis WP : pfoot F slo shi Wp.
Definition oav (o n : Z) : Prop := forall x, o <= x < o + n -> ~ Wp x /\ ~ Wp (HeapIfaceA.S x).
Let BP := fun p c (Hin : In (p, c) LBx) => blk_piece LBx FFx LKx crx Ax Mx Vx p c F rs slo shi Wp M1 M2 HH Hin HF HFF S1 S2 FR WP.

Lemma vstr_keep_piece o s : incl (PM.vs_own s) LBx -> 0 <= o -> o + 24 <= 2 ^ 47 -> oav o 24 ->
  PM.vstr_at RSEGS PMSPA.accA M1 o s -> PM.vstr_at RSEGS PMSPA.accA M2 o s.
Proof.
  intros INC H0 H1 OA VS. apply (PMFA.vstr_at_agreeA RSEGS M1 M2 o s); [lia| lia| apply (PNHAK.agA_frame M1 M2 Wp o 24 FR H0 H1 OA)| | exact VS].
  intros c n p E. apply BP. apply INC; rewrite E; left; reflexivity.
Qed.
Lemma iss_keep_piece o str sm : incl (PM.vs_own str) LBx -> 0 <= o -> o + 272 <= 2 ^ 47 -> oav o 272 ->
  PM.iss_at RSEGS PMA.AD PMSPA.accA M1 o str sm -> PM.iss_at RSEGS PMA.AD PMSPA.accA M2 o str sm.
Proof.
  intros INC H0 H1 OA IS. apply (PMFA.iss_at_agreeA RSEGS PMA.AD M1 M2 o str sm); [lia| lia| apply (PNHAK.agA_frame M1 M2 Wp o 272 FR H0 H1 OA)| | exact IS].
  intros c n p E. apply BP. apply INC; rewrite E; left; reflexivity.
Qed.
Lemma v8_keep_piece o x : incl (PGV8.v8_own x) LBx -> 0 <= o -> o + 24 <= 2 ^ 47 -> oav o 24 -> v8_at M1 o x -> v8_at M2 o x.
Proof.
  intros INC H0 H1 OA V8. apply (v8_at_agreeA M1 M2 o x); [lia| lia| apply (PNHAK.agA_frame M1 M2 Wp o 24 FR H0 H1 OA)| | exact V8].
  intros b n c E. apply BP. apply INC; rewrite E; left; reflexivity.
Qed.
Lemma bparser_keep_piece op ois s : incl (PNM.bparser_own s) LBx -> 0 <= op -> op + PNM.PSIZE <= 2 ^ 47 -> oav op PNM.PSIZE ->
  bparser_at M1 op ois s -> bparser_at M2 op ois s.
Proof.
  intros INC H0 H1 OA PA.
  pose proof (INC _ (PNBOA.own_src s)) as IQ. pose proof (INC _ (PNBOA.own_stk s)) as IB.
  destruct (PNHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IQ) as (Q0 & _ & _ & _ & _ & Q47 & _).
  destruct (PNHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IB) as (B0 & _ & _ & _ & _ & B47 & _).
  apply (bparser_at_agreeA M1 M2 op ois s); [lia| lia| apply (PNHAK.agA_frame M1 M2 Wp op PNM.PSIZE FR H0 H1 OA)| exact (BP _ _ IQ)| lia| lia| exact (BP _ _ IB)| lia| lia| | | | exact PA].
  - intros b n c E. apply BP. apply INC. apply PNBOA.own_bb. rewrite E. left; reflexivity.
  - intros c n p E. apply BP. apply INC. apply PNBOA.own_nb. rewrite E. left; reflexivity.
  - intros c n p E. apply BP. apply INC. apply PNBOA.own_tb. rewrite E. left; reflexivity.
Qed.
Lemma hbase_piece s s' sm : incl (PM.vs_own s' ++ PM.vs_own s) LBx -> oav (F + 32) 24 -> oav (F + 96) 272 -> oav (F + 432) 8 ->
  hbase F M1 s s' sm -> hbase F M2 s s' sm.
Proof.
  intros INC O1 O2 O3 (VS & IS & V1 & V2 & V3). pose proof HFF as (F8 & F0 & F1 & FB).
  assert (AG : PMFA.agA M1 M2 (F + 432) 8) by (apply (PNHAK.agA_frame M1 M2 Wp (F + 432) 8 FR); [lia| lia| exact O3]).
  assert (AGI : PMFA.agA M1 M2 (F + 96) 272) by (apply (PNHAK.agA_frame M1 M2 Wp (F + 96) 272 FR); [lia| lia| exact O2]).
  split; [|split; [|split; [|split]]].
  - apply (vstr_keep_piece (F + 32) s); [intros x Hx; apply INC; apply in_or_app; right; exact Hx| lia| lia| exact O1| exact VS].
  - apply (iss_keep_piece (F + 96) s' sm); [intros x Hx; apply INC; apply in_or_app; left; exact Hx| lia| lia| exact O2| exact IS].
  - apply (u64_agA M1 M2 (F + 432) 8 (F + 432) _ AG); [lia| lia| lia| lia| exact V1].
  - apply (shz_agA M1 M2 (F + 432) 8 (F + 432) 1 AG); [lia| lia| lia| lia| exact V2].
  - apply (shz_agA M1 M2 (F + 96) 272 (F + 96) 34 AGI); [lia| lia| lia| lia| exact V3].
Qed.
Lemma hpar_piece ps : incl (PNM.bparser_own ps) LBx -> oav (F + 464) 424 -> hpar F M1 ps -> hpar F M2 ps.
Proof.
  intros INC O1 (PA & V1 & C1). pose proof HFF as (F8 & F0 & F1 & FB).
  assert (AG : PMFA.agA M1 M2 (F + 464) 424) by (apply (PNHAK.agA_frame M1 M2 Wp (F + 464) 424 FR); [lia| lia| exact O1]).
  split; [|split].
  - apply (bparser_keep_piece (F + 464) (F + 96) ps); [exact INC| lia| unfold PNM.PSIZE; lia| intros x Hx; apply O1; unfold PNM.PSIZE in Hx; lia| exact PA].
  - apply (u64_agA M1 M2 (F + 464) 424 (F + 880) _ AG); [lia| lia| lia| lia| exact V1].
  - apply (PMFA.accA_agree M1 M2 (F + 464) 424 (proj2 AG) C1).
Qed.
Lemma hec_piece v c : oav (F + 1024) 16 -> hec F M1 v c -> hec F M2 v c.
Proof.
  intros O1 (E1 & E2 & E3 & E4). pose proof HFF as (F8 & F0 & F1 & FB).
  assert (AG : PMFA.agA M1 M2 (F + 1024) 16) by (apply (PNHAK.agA_frame M1 M2 Wp (F + 1024) 16 FR); [lia| lia| exact O1]).
  split; [|split; [|split]].
  - apply (u32_agA M1 M2 (F + 1024) 16 (F + 1024) _ AG); [lia| lia| lia| lia| exact E1].
  - apply (u64_agA M1 M2 (F + 1024) 16 (F + 1032) _ AG); [lia| lia| lia| lia| exact E2].
  - apply (shz_agA M1 M2 (F + 1024) 16 (F + 1024) 2 AG); [lia| lia| lia| lia| exact E3].
  - exact (defined_agA M1 M2 (F + 1024) 16 (F + 1024) 16 AG ltac:(lia) ltac:(lia) E4).
Qed.
Lemma hsrc_piece src : In (PM.sr_qc src, PM.CHUNK) LBx -> oav (F + 480) 296 -> hsrc F M1 src -> hsrc F M2 src.
Proof.
  intros IQ O1 (SF & NI). pose proof HFF as (F8 & F0 & F1 & FB).
  destruct (PNHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IQ) as (Q0 & _ & _ & _ & _ & Q47 & _).
  assert (AG : PMFA.agA M1 M2 (F + 480) 296) by (apply (PNHAK.agA_frame M1 M2 Wp (F + 480) 296 FR); [lia| lia| exact O1]).
  split.
  - apply (PMFA.src_fields_at_agreeA RSEGS M1 M2 (F + 480) (F + 96) (F + 112) src); [lia| lia| lia| lia| | | exact SF].
    + replace (F + 480 + 240) with (F + 720) by lia. eapply PMFA.agA_sub; [exact AG| lia| lia].
    + exact (BP _ _ IQ).
  - apply (PMFA.nullis_at_agreeA RSEGS PMA.AD M1 M2 (F + 488)); [lia| lia| eapply PMFA.agA_sub; [exact AG| lia| lia]| exact NI].
Qed.
Lemma hvec_piece b k stk : In (b, PNM.BSZ * 2 ^ k) LBx -> oav (F + 856) 24 -> hvec F M1 b k stk -> hvec F M2 b k stk.
Proof.
  intros IB O1 (VE & D & A). pose proof HFF as (F8 & F0 & F1 & FB).
  destruct (PNHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IB) as (B0 & _ & _ & _ & _ & B47 & _).
  assert (AG : PMFA.agA M1 M2 (F + 856) 24) by (apply (PNHAK.agA_frame M1 M2 Wp (F + 856) 24 FR); [lia| lia| exact O1]).
  split; [|split].
  - apply (bvec_at_agreeA M1 M2 (F + 856) b k stk); [lia| lia| lia| lia| exact (proj1 AG)| exact (BP _ _ IB)| exact VE].
  - exact (defined_agA M1 M2 (F + 856) 24 (F + 856) 24 AG ltac:(lia) ltac:(lia) D).
  - apply (PMFA.accA_agree M1 M2 (F + 856) 24 (proj2 AG) A).
Qed.
Lemma hfin_piece s st : incl (PM.vs_own s) LBx -> oav (F + 32) 24 -> oav (F + 120) 8 -> oav (F + 216) 152 -> hfin F M1 s st -> hfin F M2 s st.
Proof.
  intros INC O1 O2 O3 (VS & LC & IO). pose proof HFF as (F8 & F0 & F1 & FB).
  assert (AG2 : PMFA.agA M1 M2 (F + 120) 8) by (apply (PNHAK.agA_frame M1 M2 Wp (F + 120) 8 FR); [lia| lia| exact O2]).
  assert (AG3 : PMFA.agA M1 M2 (F + 216) 152) by (apply (PNHAK.agA_frame M1 M2 Wp (F + 216) 152 FR); [lia| lia| exact O3]).
  split; [|split].
  - apply (vstr_keep_piece (F + 32) s); [exact INC| lia| lia| exact O1| exact VS].
  - apply (u64_agA M1 M2 (F + 120) 8 (F + 120) _ AG2); [lia| lia| lia| lia| exact LC].
  - apply (PMFA.iosb_at_agreeA RSEGS PMA.AD M1 M2 (F + 216)); [lia| lia| exact AG3| exact IO].
Qed.
End Objs.

Section ObjsC.
Variables (LBx : list (Z * Z)) (FFx LKx : list fframe) (crx : credit) (Ax : list (Z * Z)) (Mx : word -> option byte) (Vx : vml) (F rs : Z).
Hypothesis HH : ri_inv HI LBx FFx LKx crx Ax Mx Vx.
Hypothesis HF : In (F, 5, rs) (FFx ++ LKx).
Hypothesis HFF : hf F.
(* [comment removed for export] *)
Variables (LBc : list (Z * Z)) (FFc : list fframe) (spc scrc : Z) (Wc : list L5.range) (M1 M2 : word -> option byte) (f : fframe).
Hypothesis AH : L5CA.ahpres L ar LBc FFc spc scrc Wc M1 M2.
Hypothesis WF : wfi F Wc.
Hypothesis Hf : In f FFc.
Hypothesis HfF : ff_addr f = F /\ ff_bytes (ff_class f) = 2048.
Let BC := fun p c (Hin : In (p, c) LBx) (Hc : In (p, c) LBc) => blk_callee LBx FFx LKx crx Ax Mx Vx p c F rs LBc FFc spc scrc Wc M1 M2 HH Hin HF HFF AH Hc WF.
Lemma ffc o n : F + 32 <= o -> o + n <= F + 2040 -> wapart Wc o n -> PMFA.agA M1 M2 o n.
Proof.
  intros H1 H2 WA. pose proof HFF as (F8 & F0 & F1 & FB). destruct HfF as (E1 & E2).
  apply (ff_callee LBc FFc spc scrc Wc M1 M2 f F o n AH Hf); [rewrite E1; lia| rewrite E1, E2; lia| exact HFF| lia| lia| exact WF| exact WA].
Qed.

Lemma vstr_keep_callee o s : incl (PM.vs_own s) LBx -> incl (PM.vs_own s) LBc -> F + 32 <= o -> o + 24 <= F + 2040 -> wapart Wc o 24 ->
  PM.vstr_at RSEGS PMSPA.accA M1 o s -> PM.vstr_at RSEGS PMSPA.accA M2 o s.
Proof.
  intros INC INCc H0 H1 OA VS. pose proof HFF as (F8 & F0 & F1 & FB).
  apply (PMFA.vstr_at_agreeA RSEGS M1 M2 o s); [lia| lia| exact (ffc o 24 H0 H1 OA)| | exact VS].
  intros c n p E. apply BC; [apply INC| apply INCc]; rewrite E; left; reflexivity.
Qed.
Lemma iss_keep_callee o str sm : incl (PM.vs_own str) LBx -> incl (PM.vs_own str) LBc -> F + 32 <= o -> o + 272 <= F + 2040 -> wapart Wc o 272 ->
  PM.iss_at RSEGS PMA.AD PMSPA.accA M1 o str sm -> PM.iss_at RSEGS PMA.AD PMSPA.accA M2 o str sm.
Proof.
  intros INC INCc H0 H1 OA IS. pose proof HFF as (F8 & F0 & F1 & FB).
  apply (PMFA.iss_at_agreeA RSEGS PMA.AD M1 M2 o str sm); [lia| lia| exact (ffc o 272 H0 H1 OA)| | exact IS].
  intros c n p E. apply BC; [apply INC| apply INCc]; rewrite E; left; reflexivity.
Qed.
Lemma v8_keep_callee o x : incl (PGV8.v8_own x) LBx -> incl (PGV8.v8_own x) LBc -> F + 32 <= o -> o + 24 <= F + 2040 -> wapart Wc o 24 ->
  v8_at M1 o x -> v8_at M2 o x.
Proof.
  intros INC INCc H0 H1 OA V8. pose proof HFF as (F8 & F0 & F1 & FB).
  apply (v8_at_agreeA M1 M2 o x); [lia| lia| exact (ffc o 24 H0 H1 OA)| | exact V8].
  intros b n c E. apply BC; [apply INC| apply INCc]; rewrite E; left; reflexivity.
Qed.
Lemma bparser_keep_callee op ois s : incl (PNM.bparser_own s) LBx -> incl (PNM.bparser_own s) LBc -> F + 32 <= op -> op + PNM.PSIZE <= F + 2040 -> wapart Wc op PNM.PSIZE ->
  bparser_at M1 op ois s -> bparser_at M2 op ois s.
Proof.
  intros INC INCc H0 H1 OA PA. pose proof HFF as (F8 & F0 & F1 & FB).
  pose proof (INC _ (PNBOA.own_src s)) as IQ. pose proof (INC _ (PNBOA.own_stk s)) as IB.
  destruct (PNHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IQ) as (Q0 & _ & _ & _ & _ & Q47 & _).
  destruct (PNHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IB) as (B0 & _ & _ & _ & _ & B47 & _).
  apply (bparser_at_agreeA M1 M2 op ois s); [lia| unfold PNM.PSIZE in *; lia| exact (ffc op PNM.PSIZE H0 H1 OA)| | lia| lia| | lia| lia| | | | exact PA].
  - exact (BC _ _ IQ (INCc _ (PNBOA.own_src s))).
  - exact (BC _ _ IB (INCc _ (PNBOA.own_stk s))).
  - intros b n c E. apply BC; [apply INC| apply INCc]; apply PNBOA.own_bb; rewrite E; left; reflexivity.
  - intros c n p E. apply BC; [apply INC| apply INCc]; apply PNBOA.own_nb; rewrite E; left; reflexivity.
  - intros c n p E. apply BC; [apply INC| apply INCc]; apply PNBOA.own_tb; rewrite E; left; reflexivity.
Qed.
Lemma shz_keep_callee o g : F <= o -> o + 8 * g <= F + 2048 -> o mod 8 = 0 -> 0 <= g -> shadow_zero M1 o g -> shadow_zero M2 o g.
Proof. intros H1 H2 H3 H4. exact (shz_callee LBc FFc spc scrc Wc M1 M2 f F o g AH Hf HfF HFF WF H1 H2 H3 H4). Qed.
Lemma hbase_callee s s' sm : incl (PM.vs_own s' ++ PM.vs_own s) LBx -> incl (PM.vs_own s' ++ PM.vs_own s) LBc ->
  wapart Wc (F + 32) 24 -> wapart Wc (F + 96) 272 -> wapart Wc (F + 432) 8 -> hbase F M1 s s' sm -> hbase F M2 s s' sm.
Proof.
  intros INC INCc O1 O2 O3 (VS & IS & V1 & V2 & V3). pose proof HFF as (F8 & F0 & F1 & FB).
  pose proof (ffc (F + 432) 8 ltac:(lia) ltac:(lia) O3) as AG.
  split; [|split; [|split; [|split]]].
  - apply (vstr_keep_callee (F + 32) s); [intros x Hx; apply INC; apply in_or_app; right; exact Hx| intros x Hx; apply INCc; apply in_or_app; right; exact Hx| lia| lia| exact O1| exact VS].
  - apply (iss_keep_callee (F + 96) s' sm); [intros x Hx; apply INC; apply in_or_app; left; exact Hx| intros x Hx; apply INCc; apply in_or_app; left; exact Hx| lia| lia| exact O2| exact IS].
  - apply (u64_agA M1 M2 (F + 432) 8 (F + 432) _ AG); [lia| lia| lia| lia| exact V1].
  - apply (shz_keep_callee (F + 432) 1); [lia| lia| lia| lia| exact V2].
  - apply (shz_keep_callee (F + 96) 34); [lia| lia| lia| lia| exact V3].
Qed.
Lemma hpar_callee ps : incl (PNM.bparser_own ps) LBx -> incl (PNM.bparser_own ps) LBc -> wapart Wc (F + 464) 424 -> hpar F M1 ps -> hpar F M2 ps.
Proof.
  intros INC INCc O1 (PA & V1 & C1). pose proof HFF as (F8 & F0 & F1 & FB).
  pose proof (ffc (F + 464) 424 ltac:(lia) ltac:(lia) O1) as AG.
  split; [|split].
  - apply (bparser_keep_callee (F + 464) (F + 96) ps); [exact INC| exact INCc| lia| unfold PNM.PSIZE; lia| intros r Hr; destruct (O1 r Hr); unfold PNM.PSIZE; lia| exact PA].
  - apply (u64_agA M1 M2 (F + 464) 424 (F + 880) _ AG); [lia| lia| lia| lia| exact V1].
  - apply (PMFA.accA_agree M1 M2 (F + 464) 424 (proj2 AG) C1).
Qed.
Lemma hec_callee v c : wapart Wc (F + 1024) 16 -> hec F M1 v c -> hec F M2 v c.
Proof.
  intros O1 (E1 & E2 & E3 & E4). pose proof HFF as (F8 & F0 & F1 & FB).
  pose proof (ffc (F + 1024) 16 ltac:(lia) ltac:(lia) O1) as AG.
  split; [|split; [|split]].
  - apply (u32_agA M1 M2 (F + 1024) 16 (F + 1024) _ AG); [lia| lia| lia| lia| exact E1].
  - apply (u64_agA M1 M2 (F + 1024) 16 (F + 1032) _ AG); [lia| lia| lia| lia| exact E2].
  - apply (shz_keep_callee (F + 1024) 2); [lia| lia| lia| lia| exact E3].
  - exact (defined_agA M1 M2 (F + 1024) 16 (F + 1024) 16 AG ltac:(lia) ltac:(lia) E4).
Qed.
Lemma hsrc_callee src : In (PM.sr_qc src, PM.CHUNK) LBx -> In (PM.sr_qc src, PM.CHUNK) LBc -> wapart Wc (F + 480) 296 -> hsrc F M1 src -> hsrc F M2 src.
Proof.
  intros IQ IQc O1 (SF & NI). pose proof HFF as (F8 & F0 & F1 & FB).
  destruct (PNHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IQ) as (Q0 & _ & _ & _ & _ & Q47 & _).
  pose proof (ffc (F + 480) 296 ltac:(lia) ltac:(lia) O1) as AG.
  split.
  - apply (PMFA.src_fields_at_agreeA RSEGS M1 M2 (F + 480) (F + 96) (F + 112) src); [lia| lia| lia| lia| | | exact SF].
    + replace (F + 480 + 240) with (F + 720) by lia. eapply PMFA.agA_sub; [exact AG| lia| lia].
    + exact (BC _ _ IQ IQc).
  - apply (PMFA.nullis_at_agreeA RSEGS PMA.AD M1 M2 (F + 488)); [lia| lia| eapply PMFA.agA_sub; [exact AG| lia| lia]| exact NI].
Qed.
Lemma hvec_callee b k stk : In (b, PNM.BSZ * 2 ^ k) LBx -> In (b, PNM.BSZ * 2 ^ k) LBc -> wapart Wc (F + 856) 24 -> hvec F M1 b k stk -> hvec F M2 b k stk.
Proof.
  intros IB IBc O1 (VE & D & A). pose proof HFF as (F8 & F0 & F1 & FB).
  destruct (PNHAK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ _ _ HH IB) as (B0 & _ & _ & _ & _ & B47 & _).
  pose proof (ffc (F + 856) 24 ltac:(lia) ltac:(lia) O1) as AG.
  split; [|split].
  - apply (bvec_at_agreeA M1 M2 (F + 856) b k stk); [lia| lia| lia| lia| exact (proj1 AG)| exact (BC _ _ IB IBc)| exact VE].
  - exact (defined_agA M1 M2 (F + 856) 24 (F + 856) 24 AG ltac:(lia) ltac:(lia) D).
  - apply (PMFA.accA_agree M1 M2 (F + 856) 24 (proj2 AG) A).
Qed.
Lemma hfin_callee s st : incl (PM.vs_own s) LBx -> incl (PM.vs_own s) LBc -> wapart Wc (F + 32) 24 -> wapart Wc (F + 120) 8 -> wapart Wc (F + 216) 152 ->
  hfin F M1 s st -> hfin F M2 s st.
Proof.
  intros INC INCc O1 O2 O3 (VS & LC & IO). pose proof HFF as (F8 & F0 & F1 & FB).
  pose proof (ffc (F + 120) 8 ltac:(lia) ltac:(lia) O2) as AG2. pose proof (ffc (F + 216) 152 ltac:(lia) ltac:(lia) O3) as AG3.
  split; [|split].
  - apply (vstr_keep_callee (F + 32) s); [exact INC| exact INCc| lia| lia| exact O1| exact VS].
  - apply (u64_agA M1 M2 (F + 120) 8 (F + 120) _ AG2); [lia| lia| lia| lia| exact LC].
  - apply (PMFA.iosb_at_agreeA RSEGS PMA.AD M1 M2 (F + 216)); [lia| lia| exact AG3| exact IO].
Qed.
End ObjsC.
End K.
End PNHAK2.
