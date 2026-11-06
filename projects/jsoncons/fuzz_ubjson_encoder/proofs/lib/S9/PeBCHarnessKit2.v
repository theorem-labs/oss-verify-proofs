(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk HeapIface HeapIfaceA L5Defs L5Core L5DefsAB0 L5CoreAB0S9 L5StepARB0S9 HeapIfaceAEx L5KnA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA PnLayout PeLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA PnStatics PnStaticsA PmSpecsA PeSpecsAb PmModelFactsA PeStepAB0.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayoutB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PeBCHarnessStmts PeBCHarnessKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEBHK2.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Definition hf (F : Z) : Prop := F mod 8 = 0 /\ 0 <= F /\ F + 2048 <= 2 ^ 47 /\ (BIGSHADOW_HI <= F \/ F + 2048 <= BIGSHADOW_LO).

Definition pfoot (F slo shi : Z) (Wp : Z -> Prop) : Prop :=
  forall a, Wp a -> (F <= a < F + 2048) \/ (F / 8 + HeapIfaceA.SB <= a < F / 8 + HeapIfaceA.SB + 256) \/ (slo <= a < shi).

Definition wfi (F : Z) (Wc : list L5.range) : Prop :=
  forall r, In r Wc -> (F <= fst r /\ fst r + snd r <= F + 2048) \/ (65536 <= fst r /\ fst r + snd r <= 0x69c000).
Definition wapart (Wc : list L5.range) (o n : Z) : Prop := forall r, In r Wc -> fst r + snd r <= o \/ o + n <= fst r.
Lemma wfi_nil F : wfi F [].
Proof. intros r []. Qed.
Lemma wfi_cons F r Wc : ((F <= fst r /\ fst r + snd r <= F + 2048) \/ (65536 <= fst r /\ fst r + snd r <= 0x69c000)) -> wfi F Wc -> wfi F (r :: Wc).
Proof. intros H W r' [<-|Hr]; [exact H| exact (W r' Hr)]. Qed.
Lemma wfi_app F W1 W2 : wfi F W1 -> wfi F W2 -> wfi F (W1 ++ W2).
Proof. intros A B r Hr. apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [exact (A r Hr)| exact (B r Hr)]. Qed.
Lemma wapart_nil o n : wapart [] o n.
Proof. intros r []. Qed.
Lemma wapart_cons r Wc o n : (fst r + snd r <= o \/ o + n <= fst r) -> wapart Wc o n -> wapart (r :: Wc) o n.
Proof. intros H W r' [<-|Hr]; [exact H| exact (W r' Hr)]. Qed.
Lemma wapart_app W1 W2 o n : wapart W1 o n -> wapart W2 o n -> wapart (W1 ++ W2) o n.
Proof. intros A B r Hr. apply in_app_or in Hr. destruct Hr as [Hr|Hr]; [exact (A r Hr)| exact (B r Hr)]. Qed.

Lemma u64_agA (M1 M2 : word -> option byte) o n a v : PMFA.agA M1 M2 o n -> o <= a -> a + 8 <= o + n -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS M2 a v.
Proof. intros (AG & _) H1 H2 H3 H4. apply (L5C.u64_at_agree RSEGS M1 M2 a v); [intros i Hi; apply AG; lia| lia| lia]. Qed.
Lemma u32_agA (M1 M2 : word -> option byte) o n a v : PMFA.agA M1 M2 o n -> o <= a -> a + 4 <= o + n -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M1 a v -> L5.u32_at RSEGS M2 a v.
Proof. intros (AG & _) H1 H2 H3 H4. apply (PEBHK.u32_agree M1 M2 a v); [intros i Hi; apply AG; lia| lia| lia]. Qed.
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

Definition hbase (F : Z) (M : word -> option byte) (s s' : PM.vstr) (sm : PM.strm) : Prop :=
  PM.vstr_at RSEGS PMSPA.accA M (F + 32) s /\ PM.iss_at RSEGS AD PMSPA.accA M (F + 96) s' sm /\ shadow_zero M (F + 96) 34.
Definition hec (F : Z) (M : word -> option byte) (v c : Z) : Prop :=
  L5.u32_at RSEGS M (F + 1120) v /\ L5.u64_at RSEGS M (F + 1128) c /\ shadow_zero M (F + 1120) 2 /\ L5.defined M (F + 1120) 16.

Lemma shz_frame (M1 M2 : word -> option byte) (Wp : Z -> Prop) o g :
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> (forall j, 0 <= j < g -> ~ Wp (HeapIfaceA.S o + j)) ->
  0 <= HeapIfaceA.S o -> HeapIfaceA.S o + g <= 2 ^ 64 -> shadow_zero M1 o g -> shadow_zero M2 o g.
Proof. intros FR W H0 H1 SZ j Hj. unfold byte_at. rewrite FR; [exact (SZ j Hj)| lia| exact (W j Hj)]. Qed.

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

End AgreeB.

Section K.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (scfg : SpuriousCfg) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C scfg HI.
Let LYa := PMB.ly_as0 L C LY.

Lemma blk_piece LBx FFx LKx crx Ax Mx Vx (p c F rs slo shi : Z) (Wp : Z -> Prop) (M1 M2 : word -> option byte) :
  ri_inv HI LBx FFx LKx crx Ax Mx Vx -> In (p, c) LBx -> In (F, 5, rs) (FFx ++ LKx) -> hf F -> ahl_ceil ar <= slo -> BIGSHADOW_HI <= slo ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> pfoot F slo shi Wp -> PMFA.agA M1 M2 p c.
Proof.
  intros HH Hin HF (F8 & F0 & F1 & FB) S1 S2 FR WP.
  exact (PEBHK.blk_agA L ar C scfg HI HIok LBx FFx LKx crx Ax Mx Vx p c F rs slo shi Wp M1 M2 HH Hin HF F8 F0 F1 FB S1 S2 FR WP).
Qed.
Lemma blk_callee LBx FFx LKx crx Ax Mx Vx (p c F rs : Z) LBc FFc spc scrc Wc (M1 M2 : word -> option byte) :
  ri_inv HI LBx FFx LKx crx Ax Mx Vx -> In (p, c) LBx -> In (F, 5, rs) (FFx ++ LKx) -> hf F ->
  L5CA.ahpres L ar LBc FFc spc scrc Wc M1 M2 -> In (p, c) LBc -> wfi F Wc -> PMFA.agA M1 M2 p c.
Proof.
  intros HH Hin HF (F8 & F0 & F1 & FB) AH Hc WF.
  destruct (PEBHK.blk_facts L ar C scfg HI HIok _ _ _ _ _ _ _ p c HH Hin) as (P0 & P3 & P4 & P5 & PSH & P47 & PIMG & PFA).
  pose proof (PFA (F, 5, rs) HF) as PF. cbn [ff_addr ff_class fst snd] in PF. change (ff_bytes 5) with 2048 in PF.
  rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in PIMG.
  apply (PEBHK.agA_ahpres_blk L ar LBc FFc spc scrc Wc M1 M2 p c AH Hc); [lia| lia|].
  intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in *.
  split; intros r Hr Hin'; unfold L5.in_rng in Hin'; destruct (WF r Hr) as [(W1 & W2)|(W1 & W2)]; lia.
Qed.

Lemma ff_callee LBc FFc spc scrc Wc (M1 M2 : word -> option byte) f F o n :
  L5CA.ahpres L ar LBc FFc spc scrc Wc M1 M2 -> In f FFc -> ff_addr f + 32 <= o -> o + n <= ff_addr f + ff_bytes (ff_class f) - 8 ->
  hf F -> F <= o -> o + n <= F + 2048 -> wfi F Wc -> wapart Wc o n -> PMFA.agA M1 M2 o n.
Proof.
  intros AH Hf H1 H2 (F8 & F0 & F1 & FB) O1 O2 WF WA.
  apply (PEBHK.agA_ahpres_ff L ar LBc FFc spc scrc Wc M1 M2 f o n AH Hf H1 H2); [lia| lia|].
  intros x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in *.
  split; intros r Hr Hin'; unfold L5.in_rng in Hin'.
  - destruct (WA r Hr) as [Y|Y]; lia.
  - destruct (WF r Hr) as [(W1 & W2)|(W1 & W2)]; lia.
Qed.

Lemma shz_callee LBc FFc spc scrc Wc (M1 M2 : word -> option byte) f F o g :
  L5CA.ahpres L ar LBc FFc spc scrc Wc M1 M2 -> In f FFc -> ff_addr f = F /\ ff_bytes (ff_class f) = 2048 -> hf F -> wfi F Wc ->
  F <= o -> o + 8 * g <= F + 2048 -> o mod 8 = 0 -> 0 <= g -> shadow_zero M1 o g -> shadow_zero M2 o g.
Proof.
  intros (AK & _ & _) Hf (E1 & E2) (F8 & F0 & F1 & FB) WF H1 H2 H3 H4 SZ j Hj. unfold byte_at in *. specialize (SZ j Hj).
  rewrite (PMFA.S_granule o j H3 ltac:(lia)) in SZ |- *.
  pose proof (PMKB.S_in_shadow (o + 8 * j) ltac:(lia)) as SX.
  rewrite AK; [exact SZ|]. split; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia|]. split.
  - right; right; right; right; right; left. exists f. split; [exact Hf|]. rewrite E1, E2. unfold in_shadow_of. split; apply PMKB.S_mono; lia.
  - intros r Hr Hin. unfold L5.in_rng in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX, FB. destruct (WF r Hr) as [(W1 & W2)|(W1 & W2)]; lia.
Qed.

Section Objs.
Variables (LBx : list (Z * Z)) (FFx LKx : list fframe) (crx : credit) (Ax : list (Z * Z)) (Mx : word -> option byte) (Vx : vml) (F rs : Z).
Hypothesis HH : ri_inv HI LBx FFx LKx crx Ax Mx Vx.
Hypothesis HF : In (F, 5, rs) (FFx ++ LKx).
Hypothesis HFF : hf F.

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
  intros INC H0 H1 OA VS. apply (PMFA.vstr_at_agreeA RSEGS M1 M2 o s); [lia| lia| apply (PEBHK.agA_frame M1 M2 Wp o 24 FR H0 H1 OA)| | exact VS].
  intros c n p E. apply BP. apply INC; rewrite E; left; reflexivity.
Qed.
Lemma iss_keep_piece o str sm : incl (PM.vs_own str) LBx -> 0 <= o -> o + 272 <= 2 ^ 47 -> oav o 272 ->
  PM.iss_at RSEGS AD PMSPA.accA M1 o str sm -> PM.iss_at RSEGS AD PMSPA.accA M2 o str sm.
Proof.
  intros INC H0 H1 OA IS. apply (PMFA.iss_at_agreeA RSEGS AD M1 M2 o str sm); [lia| lia| apply (PEBHK.agA_frame M1 M2 Wp o 272 FR H0 H1 OA)| | exact IS].
  intros c n p E. apply BP. apply INC; rewrite E; left; reflexivity.
Qed.
Lemma hbase_piece s s' sm : incl (PM.vs_own s' ++ PM.vs_own s) LBx -> oav (F + 32) 24 -> oav (F + 96) 272 ->
  hbase F M1 s s' sm -> hbase F M2 s s' sm.
Proof.
  intros INC O1 O2 (VS & IS & V3). pose proof HFF as (F8 & F0 & F1 & FB).
  assert (AGI : PMFA.agA M1 M2 (F + 96) 272) by (apply (PEBHK.agA_frame M1 M2 Wp (F + 96) 272 FR); [lia| lia| exact O2]).
  split; [|split].
  - apply (vstr_keep_piece (F + 32) s); [intros x Hx; apply INC; apply in_or_app; right; exact Hx| lia| lia| exact O1| exact VS].
  - apply (iss_keep_piece (F + 96) s' sm); [intros x Hx; apply INC; apply in_or_app; left; exact Hx| lia| lia| exact O2| exact IS].
  - apply (shz_agA M1 M2 (F + 96) 272 (F + 96) 34 AGI); [lia| lia| lia| lia| exact V3].
Qed.
Lemma hec_piece v c : oav (F + 1120) 16 -> hec F M1 v c -> hec F M2 v c.
Proof.
  intros O1 (E1 & E2 & E3 & E4). pose proof HFF as (F8 & F0 & F1 & FB).
  assert (AG : PMFA.agA M1 M2 (F + 1120) 16) by (apply (PEBHK.agA_frame M1 M2 Wp (F + 1120) 16 FR); [lia| lia| exact O1]).
  split; [|split; [|split]].
  - apply (u32_agA M1 M2 (F + 1120) 16 (F + 1120) _ AG); [lia| lia| lia| lia| exact E1].
  - apply (u64_agA M1 M2 (F + 1120) 16 (F + 1128) _ AG); [lia| lia| lia| lia| exact E2].
  - apply (shz_agA M1 M2 (F + 1120) 16 (F + 1120) 2 AG); [lia| lia| lia| lia| exact E3].
  - exact (defined_agA M1 M2 (F + 1120) 16 (F + 1120) 16 AG ltac:(lia) ltac:(lia) E4).
Qed.
End Objs.

Section ObjsC.
Variables (LBx : list (Z * Z)) (FFx LKx : list fframe) (crx : credit) (Ax : list (Z * Z)) (Mx : word -> option byte) (Vx : vml) (F rs : Z).
Hypothesis HH : ri_inv HI LBx FFx LKx crx Ax Mx Vx.
Hypothesis HF : In (F, 5, rs) (FFx ++ LKx).
Hypothesis HFF : hf F.

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
  PM.iss_at RSEGS AD PMSPA.accA M1 o str sm -> PM.iss_at RSEGS AD PMSPA.accA M2 o str sm.
Proof.
  intros INC INCc H0 H1 OA IS. pose proof HFF as (F8 & F0 & F1 & FB).
  apply (PMFA.iss_at_agreeA RSEGS AD M1 M2 o str sm); [lia| lia| exact (ffc o 272 H0 H1 OA)| | exact IS].
  intros c n p E. apply BC; [apply INC| apply INCc]; rewrite E; left; reflexivity.
Qed.
Lemma shz_keep_callee o g : F <= o -> o + 8 * g <= F + 2048 -> o mod 8 = 0 -> 0 <= g -> shadow_zero M1 o g -> shadow_zero M2 o g.
Proof. intros H1 H2 H3 H4. exact (shz_callee LBc FFc spc scrc Wc M1 M2 f F o g AH Hf HfF HFF WF H1 H2 H3 H4). Qed.
Lemma hbase_callee s s' sm : incl (PM.vs_own s' ++ PM.vs_own s) LBx -> incl (PM.vs_own s' ++ PM.vs_own s) LBc ->
  wapart Wc (F + 32) 24 -> wapart Wc (F + 96) 272 -> hbase F M1 s s' sm -> hbase F M2 s s' sm.
Proof.
  intros INC INCc O1 O2 (VS & IS & V3). pose proof HFF as (F8 & F0 & F1 & FB).
  split; [|split].
  - apply (vstr_keep_callee (F + 32) s); [intros x Hx; apply INC; apply in_or_app; right; exact Hx| intros x Hx; apply INCc; apply in_or_app; right; exact Hx| lia| lia| exact O1| exact VS].
  - apply (iss_keep_callee (F + 96) s' sm); [intros x Hx; apply INC; apply in_or_app; left; exact Hx| intros x Hx; apply INCc; apply in_or_app; left; exact Hx| lia| lia| exact O2| exact IS].
  - apply (shz_keep_callee (F + 96) 34); [lia| lia| lia| lia| exact V3].
Qed.
Lemma hec_callee v c : wapart Wc (F + 1120) 16 -> hec F M1 v c -> hec F M2 v c.
Proof.
  intros O1 (E1 & E2 & E3 & E4). pose proof HFF as (F8 & F0 & F1 & FB).
  pose proof (ffc (F + 1120) 16 ltac:(lia) ltac:(lia) O1) as AG.
  split; [|split; [|split]].
  - apply (u32_agA M1 M2 (F + 1120) 16 (F + 1120) _ AG); [lia| lia| lia| lia| exact E1].
  - apply (u64_agA M1 M2 (F + 1120) 16 (F + 1128) _ AG); [lia| lia| lia| lia| exact E2].
  - apply (shz_keep_callee (F + 1120) 2); [lia| lia| lia| lia| exact E3].
  - exact (defined_agA M1 M2 (F + 1120) 16 (F + 1120) 16 AG ltac:(lia) ltac:(lia) E4).
Qed.
End ObjsC.
End K.
End PEBHK2.
