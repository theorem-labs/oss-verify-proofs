(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5KnA L5LazyA L5DefsA L5CoreAS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmSpecs PmSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PESKA.

Record sink_policyA : Type := SPA {
  spa_mode : Prop;
  spa_cap : Z -> Prop;
  spa_nmax : Z;
  spa_pot : Z -> credit;
  spa_hb : Z -> Prop
}.

Record sink_policyA_ok (L : asan_layout) (P : sink_policyA) : Prop := SPAO {
  spao_pot_nonneg : forall c, PESK.is_cap c -> 0 <= c <= spa_nmax P -> 0 <= fst (spa_pot P c) /\ 0 <= snd (spa_pot P c);
  spao_hb_mono : forall h h', spa_hb P h -> h' <= h -> spa_hb P h';

  spao_next : forall c h, PESK.is_cap c -> (0 < c -> spa_cap P c) -> spa_hb P h -> c <= h ->
              0 < PESK.cap_next c <= spa_nmax P
              /\ acredit_ok L (spa_pot P c) (PESK.cap_next c)
              /\ PMSP.credit_le (spa_pot P (PESK.cap_next c)) (adebit L (spa_pot P c) (PESK.cap_next c));
  spao_nmax_pos : 0 < spa_nmax P;

  spao_copy : forall c, PESK.is_cap c -> 0 < PESK.cap_next c <= spa_nmax P -> spa_cap P (PESK.cap_next c) -> c <= 2 ^ 32
}.

Section WithImage.
Context {SCFG_P : ScfgP}.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variable E : pe_addrs.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.

Abbreviation accA := PMSPA.accA.
Abbreviation annA := PMSPA.annA.
Abbreviation entryA := (PMSPA.entryA A L ar).
Abbreviation ffroomA := PMSPA.ffroomA.
Abbreviation ffrsA := PMSPA.ffrsA.
Abbreviation aobjA := PMSPA.aobjA.
Abbreviation pm_scr := PMSPA.pm_scr.
Abbreviation cfg := (@PMSPA.cfg segs).

Definition sink_atA (P : sink_policyA) (M : word -> option byte) (o : Z) (k : PESK.sink) : Prop :=
  L5.u64_at segs M o (PESK.sk_b k) /\ L5.u64_at segs M (o + 8) (PESK.sk_b k + PESK.sk_z k) /\ L5.u64_at segs M (o + 16) (PESK.sk_b k + PESK.sk_c k)
  /\ L5.defined M o 24 /\ accA M o 24
  /\ 0 <= PESK.sk_z k <= PESK.sk_c k /\ PESK.is_cap (PESK.sk_c k)
  /\ (PESK.sk_c k = 0 -> PESK.sk_b k = 0)
  /\ (0 < PESK.sk_c k ->
        L5.defined M (PESK.sk_b k) (PESK.sk_c k) /\ accA M (PESK.sk_b k) (PESK.sk_z k) /\ annA M (PESK.sk_b k) (PESK.sk_z k) (PESK.sk_c k)
        /\ ablock_range L ar (PESK.sk_b k) (PESK.sk_c k) /\ spa_cap P (PESK.sk_c k)
        /\ PESK.sk_c k <= spa_nmax P).

Lemma sink_potA_nonneg P M o k : sink_policyA_ok L P -> sink_atA P M o k -> 0 <= fst (spa_pot P (PESK.sk_c k)) /\ 0 <= snd (spa_pot P (PESK.sk_c k)).
Proof.
  intros PO (_ & _ & _ & _ & _ & Hzc & Hcap & Hc0 & Hlive). pose proof (spao_nmax_pos L P PO) as Hn.
  apply (spao_pot_nonneg L P PO _ Hcap). destruct (Z.eq_dec (PESK.sk_c k) 0) as [->|Hne]; [lia|].
  destruct (Hlive ltac:(lia)) as (_ & _ & _ & _ & _ & Hle). lia.
Qed.

Definition opnew_n_spec (NMAX : Z) (NG : Z -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (n sp r : Z),
    ri_inv HI LB FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NMAX -> acredit_ok L cr n ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (hl_tp L) -> L5CA.astk ar M sp PMSPA.OPNEW_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (Aw' : list (Z * Z)) (q : Z),
        getr R' 10%bv = Z_to_bv 64 q -> regs_preserved R R' ->
        L5CA.afresh L ar LB (FF ++ LK) M' q n ->
        L5CA.ahpres L ar LB FF sp PMSPA.OPNEW_SCR [] M M' ->
        model_rt model model' -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI ((q, n) :: LB) FF LK (adebit L cr n) Aw' M' (vml_of model') ->
        NG n ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (pa_opnew A) M model) K.

Lemma opnew_n_spec_mono (N N' : Z) (NG NG' : Z -> Prop) :
  N <= N' -> (forall n, 0 < n <= N -> NG' n -> NG n) -> opnew_n_spec N' NG' -> opnew_n_spec N NG.
Proof.
  intros LE IMP W fx R M model K LB FF LK Aw cr n sp r RI AM HK G10 Hn CR G1 RA G2 G4 STK KONT.
  apply (W fx R M model K LB FF LK Aw cr n sp r RI AM HK G10 ltac:(lia) CR G1 RA G2 G4 STK).
  intros fx' R' M' model' Aw' q H10 RP FR HP RT IA AM' RI' HNG.
  exact (KONT fx' R' M' model' Aw' q H10 RP FR HP RT IA AM' RI' (IMP n Hn HNG)).
Qed.

Definition pv_ok (FF : list fframe) (M : word -> option byte) (sp o pv : Z) : Prop :=
  L5.defined M pv 1 /\ byte_at M (HeapIfaceA.S pv) 0   /\ (pv + 1 <= o \/ o + 24 <= pv)
  /\ ((sp <= pv /\ pv + 1 <= ar_sptop ar) \/ aobjA FF pv 1).

Definition push_back_specA (P : sink_policyA) : Prop :=
  spa_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (o pv sp r : Z) (k : PESK.sink),
    ri_inv HI (PESK.sink_own k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    entryA R M sp r 0 -> ffroomA 0 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 pv ->
    sink_atA P M o k ->
    aobjA FF o 24 -> o mod 8 = 0 ->
    pv_ok FF M sp o pv ->
    (PESK.sk_z k = PESK.sk_c k ->
        0 < PESK.cap_next (PESK.sk_c k) <= spa_nmax P
        /\ acredit_ok L (spa_pot P (PESK.sk_c k)) (PESK.cap_next (PESK.sk_c k))
        /\ PMSP.credit_le (spa_pot P (PESK.cap_next (PESK.sk_c k))) (adebit L (spa_pot P (PESK.sk_c k)) (PESK.cap_next (PESK.sk_c k)))) ->
    PMSP.credit_le (spa_pot P (PESK.sk_c k)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (cr' : credit) (b' : Z),
        regs_preserved R R' ->
        sink_atA P M' o (PESK.sk_push k b') ->
        L5CA.ahpres L ar LBX FF sp (pm_scr 0) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (spa_pot P (PESK.sk_c k)) (spa_pot P (PESK.sk_c (PESK.sk_push k b'))) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PESK.sink_own (PESK.sk_push k b') ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R (pe_push_back E) M model) K.

Definition push_back_ind_specA (pc : Z) (P : sink_policyA) : Prop :=
  spa_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z)) (cr : credit) (q rr o pv sp r : Z) (k : PESK.sink),
    ri_inv HI (PESK.sink_own k ++ LBX) FF LK cr Aw M (vml_of model) -> L5CA.amodel_ok Aw model -> K [] ->
    entryA R M sp r 1 -> ffroomA 1 FF LK -> ffrsA FF sp ->
    getr R 10%bv = Z_to_bv 64 q -> getr R 11%bv = Z_to_bv 64 pv ->
    L5.u64_at segs M q rr -> rr mod 8 = 0 -> 0 < rr -> L5.u64_at segs M rr o -> 0 < o ->
    L5.defined M q 8 -> accA M q 8 -> ((sp <= q /\ q + 8 <= ar_sptop ar) \/ aobjA FF q 8) ->
    aobjA FF rr 8 -> L5.defined M rr 8 -> accA M rr 8 ->
    sink_atA P M o k ->
    aobjA FF o 24 -> o mod 8 = 0 ->
    pv_ok FF M sp o pv ->
    (PESK.sk_z k = PESK.sk_c k ->
        0 < PESK.cap_next (PESK.sk_c k) <= spa_nmax P
        /\ acredit_ok L (spa_pot P (PESK.sk_c k)) (PESK.cap_next (PESK.sk_c k))
        /\ PMSP.credit_le (spa_pot P (PESK.cap_next (PESK.sk_c k))) (adebit L (spa_pot P (PESK.sk_c k)) (PESK.cap_next (PESK.sk_c k)))) ->
    PMSP.credit_le (spa_pot P (PESK.sk_c k)) cr ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z)) (cr' : credit) (b' : Z),
        regs_preserved R R' ->
        sink_atA P M' o (PESK.sk_push k b') ->
        L5CA.ahpres L ar LBX FF sp (pm_scr 1) [(o, 24)] M M' ->
        PMSP.credit_keep cr cr' (spa_pot P (PESK.sk_c k)) (spa_pot P (PESK.sk_c (PESK.sk_push k b'))) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' ->
        ri_inv HI (PESK.sink_own (PESK.sk_push k b') ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes segs SCFG (@cfg fx' R' r M' model') K) ->
    srealizes segs SCFG (@cfg fx R pc M model) K.
End WithImage.

Section Policies.
Variable L : asan_layout.

Definition steps (c : Z) : Z := if c =? 0 then 0 else Z.log2 c + 1.
Definition cum2 (c : Z) : Z := if c =? 0 then 0 else 2 * c - 1.

Definition potT (zmax c : Z) : credit :=
  (hl_k_per_malloc L * (steps zmax - steps c),
   hl_b_lin L * (cum2 zmax - cum2 c) + hl_b_overhead L * (steps zmax - steps c)).

Definition SP_TA (zmax hb : Z) : sink_policyA := SPA True (fun _ => True) zmax (potT zmax) (fun h => h <= hb).

Lemma steps_0 : steps 0 = 0. Proof. reflexivity. Qed.
Lemma steps_pow2 e : 0 <= e -> steps (2 ^ e) = e + 1.
Proof.
  intros He. unfold steps. pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) He).
  replace (2 ^ e =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.log2_pow2 by lia. reflexivity.
Qed.
Lemma cum2_0 : cum2 0 = 0. Proof. reflexivity. Qed.
Lemma cum2_pos c : 0 < c -> cum2 c = 2 * c - 1.
Proof. intros Hc. unfold cum2. replace (c =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. Qed.
Lemma cap_next_pow2 c : PESK.is_cap c -> exists e, 0 <= e /\ PESK.cap_next c = 2 ^ e /\ steps (PESK.cap_next c) = steps c + 1 /\ cum2 (PESK.cap_next c) = cum2 c + PESK.cap_next c.
Proof.
  intros [->|(e & He & ->)]; unfold PESK.cap_next.
  - exists 0. cbn. repeat split; lia.
  - pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) He) as Hp.
    replace (2 ^ e =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    exists (e + 1). assert (E2 : 2 ^ (e + 1) = 2 * 2 ^ e) by (rewrite Z.pow_add_r, Z.pow_1_r; lia).
    rewrite <- E2. rewrite (steps_pow2 (e + 1)), (steps_pow2 e) by lia. rewrite !cum2_pos by lia. repeat split; lia.
Qed.

Lemma potT_growth J c : 1 <= J -> 0 <= hl_k_per_malloc L -> 0 <= hl_b_lin L -> 0 <= hl_b_overhead L ->
  PESK.is_cap c -> c < 2 ^ J ->
  0 < PESK.cap_next c <= 2 ^ J
  /\ acredit_ok L (potT (2 ^ J) c) (PESK.cap_next c)
  /\ PMSP.credit_le (potT (2 ^ J) (PESK.cap_next c)) (adebit L (potT (2 ^ J) c) (PESK.cap_next c)).
Proof.
  intros HJ HK HLIN HOV Hcap Hcz.
  pose proof (Z.pow_pos_nonneg 2 J ltac:(lia) ltac:(lia)) as HZ.
  assert (SZ : steps (2 ^ J) = J + 1) by (apply steps_pow2; lia).
  assert (CZ : cum2 (2 ^ J) = 2 * 2 ^ J - 1) by (apply cum2_pos; lia).
  destruct (cap_next_pow2 c Hcap) as (e & He & Ec & Es & Ecum).
  pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) He) as Hpe.
  assert (Hc0 : 0 <= c) by (destruct Hcap as [->|(e0 & He0 & ->)]; [lia| apply Z.pow_nonneg; lia]).

  assert (Hnext : PESK.cap_next c <= 2 ^ J).
  { rewrite Ec. destruct Hcap as [->|(e0 & He0 & ->)].
    - cbn in Ec. assert (e = 0) by (destruct (Z.eq_dec e 0); [lia|]; assert (2 ^ 1 <= 2 ^ e) by (apply Z.pow_le_mono_r; lia); rewrite Z.pow_1_r in *; lia).
      subst e. apply Z.pow_le_mono_r; lia.
    - unfold PESK.cap_next in Ec. pose proof (Z.pow_pos_nonneg 2 e0 ltac:(lia) He0).
      replace (2 ^ e0 =? 0) with false in Ec by (symmetry; apply Z.eqb_neq; lia).
      apply (PESK.pow2_le_half e J He ltac:(lia)). rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. }
  assert (HSc : steps (PESK.cap_next c) <= steps (2 ^ J)).
  { rewrite Ec, (steps_pow2 e He), SZ. assert (e <= J) by (apply (Z.pow_le_mono_r_iff 2); lia). lia. }
  assert (HCc : cum2 (PESK.cap_next c) <= cum2 (2 ^ J)).
  { rewrite Ec, (cum2_pos (2 ^ e)), CZ by lia. rewrite <- Ec. lia. }
  split; [lia|]. unfold potT, acredit_ok, adebit, PMSP.credit_le. cbn [fst snd]. split.
  + split.
    * assert (1 <= steps (2 ^ J) - steps c) by lia.
      rewrite <- (Z.mul_1_r (hl_k_per_malloc L)) at 1. apply Z.mul_le_mono_nonneg_l; lia.
    * assert (H1 : PESK.cap_next c <= cum2 (2 ^ J) - cum2 c) by lia.
      assert (H2 : 1 <= steps (2 ^ J) - steps c) by lia.
      assert (hl_b_lin L * PESK.cap_next c <= hl_b_lin L * (cum2 (2 ^ J) - cum2 c)) by (apply Z.mul_le_mono_nonneg_l; lia).
      assert (hl_b_overhead L * 1 <= hl_b_overhead L * (steps (2 ^ J) - steps c)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
  + rewrite Es, Ecum. split; [nia|nia].
Qed.

Lemma potT_nonneg J c : 1 <= J -> 0 <= hl_k_per_malloc L -> 0 <= hl_b_lin L -> 0 <= hl_b_overhead L ->
  PESK.is_cap c -> 0 <= c <= 2 ^ J -> 0 <= fst (potT (2 ^ J) c) /\ 0 <= snd (potT (2 ^ J) c).
Proof.
  intros HJ HK HLIN HOV Hcap [Hc0 Hcz].
  pose proof (Z.pow_pos_nonneg 2 J ltac:(lia) ltac:(lia)) as HZ.
  assert (SZ : steps (2 ^ J) = J + 1) by (apply steps_pow2; lia).
  assert (CZ : cum2 (2 ^ J) = 2 * 2 ^ J - 1) by (apply cum2_pos; lia).
  unfold potT. cbn [fst snd].
  assert (HS : steps c <= steps (2 ^ J) /\ cum2 c <= cum2 (2 ^ J)).
  { destruct Hcap as [->|(e & He & ->)].
    - rewrite steps_0, cum2_0, SZ, CZ. lia.
    - pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) He).
      assert (e <= J) by (apply (Z.pow_le_mono_r_iff 2); lia).
      rewrite (steps_pow2 e He), SZ, (cum2_pos (2 ^ e)), CZ by lia. split; [lia|]. lia. }
  destruct HS as [HS1 HS2]. split; [apply Z.mul_nonneg_nonneg; lia|].
  apply Z.add_nonneg_nonneg; apply Z.mul_nonneg_nonneg; lia.
Qed.

Lemma copy_bound c K : PESK.is_cap c -> 0 < PESK.cap_next c -> PESK.cap_next c < 2 ^ K -> K <= 34 -> c <= 2 ^ 32.
Proof.
  intros Hcap Hp Hlt HK. destruct Hcap as [->|(e & He & ->)]; [apply Z.pow_nonneg; lia|].
  unfold PESK.cap_next in Hp, Hlt. pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) He) as Hpe.
  replace (2 ^ e =? 0) with false in Hlt by (symmetry; apply Z.eqb_neq; lia).
  assert (E2 : 2 * 2 ^ e = 2 ^ (e + 1)) by (rewrite Z.pow_add_r, Z.pow_1_r; lia). rewrite E2 in Hlt.
  assert (e + 1 < K). { destruct (Z_lt_le_dec (e + 1) K) as [X|X]; [exact X|]. exfalso. assert (2 ^ K <= 2 ^ (e + 1)) by (apply Z.pow_le_mono_r; lia). lia. }
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma SP_TA_ok J hb : 1 <= J <= 33 -> hb < 2 ^ J ->
  0 <= hl_k_per_malloc L -> 0 <= hl_b_lin L -> 0 <= hl_b_overhead L ->
  sink_policyA_ok L (SP_TA (2 ^ J) hb).
Proof.
  intros HJ HHB HK HLIN HOV.
  constructor; cbn -[Z.pow Z.mul Z.sub Z.add steps cum2 potT].
  - intros c Hcap Hc. exact (potT_nonneg J c (proj1 HJ) HK HLIN HOV Hcap Hc).
  - intros h h' Hh Hle. lia.
  - intros c h Hcap _ Hh Hch. exact (potT_growth J c (proj1 HJ) HK HLIN HOV Hcap ltac:(lia)).
  - apply Z.pow_pos_nonneg; lia.
  - intros c Hcap Hn _. apply (copy_bound c (J + 1) Hcap (proj1 Hn)); [|lia].
    rewrite Z.pow_add_r, Z.pow_1_r by lia. lia.
Qed.

Section ModeS.
Context {bmK : BMode}.
Definition SP_SA (J : Z) : sink_policyA := SPA (bm_on = true) (fun c => c < 2 ^ J) (2 ^ J) (potT (2 ^ J)) (fun _ => True).

Lemma SP_SA_ok J : 1 <= J <= 34 ->
  0 <= hl_k_per_malloc L -> 0 <= hl_b_lin L -> 0 <= hl_b_overhead L ->
  sink_policyA_ok L (SP_SA J).
Proof.
  intros HJ HK HLIN HOV.
  constructor; cbn -[Z.pow Z.mul Z.sub Z.add steps cum2 potT].
  - intros c Hcap Hc. exact (potT_nonneg J c (proj1 HJ) HK HLIN HOV Hcap Hc).
  - intros h h' _ _. exact I.
  - intros c h Hcap Hlearn _ _. apply (potT_growth J c (proj1 HJ) HK HLIN HOV Hcap).
    destruct Hcap as [->|(e & He & ->)]; [apply Z.pow_pos_nonneg; lia|].
    apply Hlearn. apply Z.pow_pos_nonneg; lia.
  - apply Z.pow_pos_nonneg; lia.
  - intros c Hcap Hn Hlt. exact (copy_bound c J Hcap (proj1 Hn) Hlt (proj2 HJ)).
Qed.

Lemma SP_SA_learn J (NG : Z -> Prop) : (forall n, NG n -> n < 2 ^ J) -> forall n, 0 < n <= spa_nmax (SP_SA J) -> NG n -> spa_cap (SP_SA J) n.
Proof. intros H n _ Hn. cbn. exact (H n Hn). Qed.

End ModeS.
End Policies.

End PESKA.
