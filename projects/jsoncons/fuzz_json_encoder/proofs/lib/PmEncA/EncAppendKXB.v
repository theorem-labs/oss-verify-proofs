(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct AsanAcctShape
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5PlanKit Pm5L5DefsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmHeapIfaceA IcptIfaceA StartupAux.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutAuto CutLib CutHeap CutHeap2 CutL5 CutCertA CutHeapA CutL5A CutBridgeA CutRtA CutRtB CutRtCpsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibSpecs PmEncSpecs PmLibDefsA PmLibSpecsA PmEncSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.PmEncA Require Import EncKitXB EncMemXB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module EAKA.
Import PMES.
Definition mem := (word -> option byte).

(* [comment removed for export] *)
Definition gbase (q : Z) : Z := q - q mod 8.
Definition gcnt (q k : Z) : Z := (q mod 8 + k + 7) / 8.
Lemma gran_cover : forall q k, 0 <= q -> 0 < k -> gbase q <= q /\ q + k <= gbase q + 8 * gcnt q k /\ gbase q mod 8 = 0 /\ 0 < gcnt q k /\ gbase q + 8 * gcnt q k <= q + k + 7 /\ 0 <= gbase q.
Proof.
  intros q k Hq Hk. unfold gbase, gcnt. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as MB. pose proof (Z_div_mod_eq_full q 8) as DQ.
  pose proof (Z_div_mod_eq_full (q mod 8 + k + 7) 8) as D2. pose proof (Z.mod_pos_bound (q mod 8 + k + 7) 8 ltac:(lia)) as M2.
  split; [lia|]. split; [lia|]. split; [replace (q - q mod 8) with (8 * (q / 8)) by lia; rewrite Z.mul_comm; apply Z_mod_mult|].
  split; [apply Z.div_str_pos; lia|]. split; [lia | lia].
Qed.
Lemma gran_last : forall q k, 0 <= q -> 0 < k -> (gbase q + 8 * gcnt q k - 1) / 8 = (q + k - 1) / 8.
Proof.
  intros q k Hq Hk. unfold gbase, gcnt. pose proof (Z_div_mod_eq_full q 8). pose proof (Z.mod_pos_bound q 8 ltac:(lia)).
  pose proof (Z_div_mod_eq_full (q mod 8 + k + 7) 8). pose proof (Z.mod_pos_bound (q mod 8 + k + 7) 8 ltac:(lia)).
  pose proof (Z_div_mod_eq_full (q + k - 1) 8). pose proof (Z.mod_pos_bound (q + k - 1) 8 ltac:(lia)).
  pose proof (Z_div_mod_eq_full (q - q mod 8 + 8 * ((q mod 8 + k + 7) / 8) - 1) 8). pose proof (Z.mod_pos_bound (q - q mod 8 + 8 * ((q mod 8 + k + 7) / 8) - 1) 8 ltac:(lia)). lia.
Qed.
Lemma gran_end : forall q k, 0 <= q -> 0 < k -> q + k <= 2 ^ 47 -> gbase q + 8 * gcnt q k <= 2 ^ 47.
Proof.
  intros q k Hq Hk H47. pose proof (gran_last q k Hq Hk) as GL.
  pose proof (Z_div_mod_eq_full (gbase q + 8 * gcnt q k - 1) 8). pose proof (Z.mod_pos_bound (gbase q + 8 * gcnt q k - 1) 8 ltac:(lia)).
  pose proof (Z.div_le_mono (q + k - 1) (2 ^ 47 - 1) 8 ltac:(lia) ltac:(lia)). change ((2 ^ 47 - 1) / 8) with (2 ^ 44 - 1) in *. lia.
Qed.
(* [comment removed for export] *)
Lemma aacc_of_gran_zero : forall (M : mem) q k, 0 <= q -> 0 < k -> PMESA.gran_zero M q k -> aacc M q k.
Proof.
  intros M q k Hq Hk GZ. destruct (gran_cover q k Hq Hk) as (G1 & G2 & G3 & G4 & G5 & G6).
  exact (EMA.aacc_of_shz M (gbase q) (gcnt q k) q k GZ G3 G1 G2).
Qed.
(* [comment removed for export] *)
Lemma gran_zero_of_blockz : forall (M : mem) b n q k, b mod 8 = 0 -> n mod 8 = 0 -> 0 <= b -> b <= q -> q + k <= b + n -> 0 < k -> shadow_zero M b (n / 8) -> PMESA.gran_zero M q k.
Proof.
  intros M b n q k B8 N8 B0 H1 H2 Hk SZ. unfold PMESA.gran_zero. destruct (gran_cover q k ltac:(lia) Hk) as (G1 & G2 & G3 & G4 & G5 & G6). fold (gbase q). fold (gcnt q k).
  fold (gbase q) in G1, G2, G3, G5, G6. fold (gcnt q k) in G2, G4, G5.
  intros j Hj. unfold shadow_zero in SZ.
  replace (S (gbase q) + j) with (S b + ((gbase q - b) / 8 + j)) by (unfold S, gbase in *; lia).
  apply SZ. unfold gbase, gcnt in *. lia.
Qed.
(* [comment removed for export] *)
Section Bytes.
Variable segs : list Segment.
Lemma bytes_of_defined : forall (M : mem) (n : nat) p, 0 <= p -> p + Z.of_nat n <= 2 ^ 63 -> L5.defined M p (Z.of_nat n) ->
  exists bs : list Z, length bs = n /\ L5.bytes_at segs M p bs.
Proof.
  intros M n. induction n as [|n IH]; intros p Hp Hn D.
  - exists []. split; [reflexivity|]. intros i Hi. cbn in Hi. lia.
  - destruct (IH (p + 1) ltac:(lia) ltac:(lia)) as (bs & Hl & Hb).
    { intros i Hi. replace (p + 1 + i) with (p + (1 + i)) by lia. apply D. lia. }
    pose proof (D 0 ltac:(lia)) as D0. rewrite Z.add_0_r in D0. destruct (M (Z_to_bv 64 p)) as [b|] eqn:EM; [|contradiction].
    exists (bv_unsigned b :: bs). split; [cbn; lia|]. intros i Hi. destruct i as [|i].
    + cbn [nth]. rewrite Z.add_0_r. unfold L5.u8_at. cbn [rdn]. rewrite EM. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + cbn [nth]. replace (p + Z.of_nat (Datatypes.S i)) with (p + 1 + Z.of_nat i) by lia. apply Hb. cbn in Hi. lia.
Qed.
Lemma u64_of_defined : forall (M : mem) a, L5.defined M a 8 -> exists v, 0 <= v < 2 ^ 64 /\ L5.u64_at segs M a v.
Proof.
  intros M a Hd.
  assert (RD : forall (k : nat) b, (forall i, 0 <= i < Z.of_nat k -> M (Z_to_bv 64 (b + i)) <> None) -> exists bs, rdn segs M (Z_to_bv 64 b) k = Some bs /\ length bs = k).
  { induction k as [|k IH]; intros b H; [exists []; split; reflexivity|].
    destruct (IH (b + 1)) as (bs & Hr & Hl); [intros i Hi; replace (b + 1 + i) with (b + (1 + i)) by lia; apply H; lia|].
    pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (M (Z_to_bv 64 b)) as [x|] eqn:Hb; [|contradiction].
    exists (x :: bs). cbn [rdn]. rewrite Hb, L5C.add1_lit, Hr. split; [reflexivity | cbn [length]; lia]. }
  destruct (RD 8%nat a Hd) as (bs & Hr & Hl). exists (bytes_le_to_Z bs).
  pose proof (PropExec.bytes_le_to_Z_nonneg bs) as N0. pose proof (AX2S.bytes_le_to_Z_bound bs) as N1. rewrite Hl in N1. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in N1.
  split; [lia|]. unfold L5.u64_at. rewrite Hr. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hl | lia].
Qed.
Lemma u64_low_byte : forall (M : mem) a w b, L5.u64_at segs M a w -> L5.u8_at segs M a b -> 0 <= w < 2 ^ 64 -> 0 <= b < 256 -> w mod 256 = b.
Proof.
  intros M a w b H H0 Hw Hb. unfold L5.u64_at, L5.u8_at in *.
  pose proof (rdn_low_bytes segs M (Z_to_bv 64 a) (Z_to_bv 64 w) 1 ltac:(lia) H) as X. rewrite H0 in X.
  assert (X' : Z_to_bv 8 b = Z_to_bv 8 (bv_unsigned (Z_to_bv 64 w))) by (unfold word_to_le_bytes in X; cbn [Z_to_le_bytes] in X; congruence).
  rewrite (L5.unsigned_lit w Hw) in X'. apply (f_equal bv_unsigned) in X'. rewrite !Z_to_bv_unsigned in X'.
  unfold bv_wrap, bv_modulus in X'. change (2 ^ Z.of_N 8) with 256 in X'. rewrite (Z.mod_small b) in X' by lia. symmetry. exact X'.
Qed.
(* [comment removed for export] *)
Lemma short_word0 : forall (M : mem) o (s : list Z), L5.lstr_short segs M o s -> L5.defined M o 24 ->
  exists u, 0 <= u < 2 ^ 56 /\ L5.u64_at segs M o (2 * Z.of_nat (length s) + 256 * u).
Proof.
  intros M o s (Hl & B0 & _) D. destruct (u64_of_defined M o) as (w & Hw & W0); [intros i Hi; apply D; lia|].
  pose proof (u64_low_byte M o w _ W0 B0 Hw ltac:(lia)) as E. exists (w / 256).
  pose proof (Z.div_mod w 256 ltac:(lia)) as DM. rewrite E in DM.
  split; [split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]|]. replace (2 * Z.of_nat (length s) + 256 * (w / 256)) with w by lia. exact W0.
Qed.
End Bytes.

Section K.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable C : asan_statics_cells.
Variable HI : asan_iface.
Variable IC : PMLA.consts.
Hypothesis HIok : PmHeapIfaceA.asan_iface_ok L ar C SCFG HI.
Hypothesis LAY : L5A.as0_layout L C.
(* [comment removed for export] *)
Hypothesis IMG_RO_ok : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a.

(* [comment removed for export] *)
Definition loc_cls (LBd : list (Z * Z)) (FF : list fframe) (sp o q k : Z) : Prop :=
     (sp <= q /\ q + k <= ar_sptop ar /\ PMLA.apart q k o 24)
  \/ (exists b n, In (b, n) LBd /\ b <= q /\ q + k <= b + n)
  \/ (CL5A.ainfr FF q k /\ PMLA.apart q k o 24).
(* [comment removed for export] *)
Definition img_cls (q k : Z) : Prop := PMLA.IMG_RO_LO IC <= q /\ q + k <= PMLA.IMG_RO_HI IC /\ PMESA.img_aacc HI q k.
(* [comment removed for export] *)
Definition srcK (M : mem) (LBd : list (Z * Z)) (FF : list fframe) (sp o q : Z) (src : list Z) : Prop :=
  L5.bytes_at (hl_segs L) M q src /\ (img_cls q (len src) \/ (loc_cls LBd FF sp o q (len src) /\ PMESA.gran_zero M q (len src))).

(* [comment removed for export] *)
Lemma srcK_intro : forall (M : mem) LB LBd FF sp o rep q (src : list Z),
  CHA.rng_facts L ar LB FF -> incl (lb_drop rep LB) LB -> LBd = lb_drop rep LB -> 1 <= len src ->
  L5.bytes_at (hl_segs L) M q src -> PMESA.src_okA ar HI IC M LB FF sp o rep q (len src) -> srcK M LBd FF sp o q src.
Proof.
  intros M LB LBd FF sp o rep q src RF Hincl -> Hn Hb Hs. split; [exact Hb|].
  destruct Hs as [H0 | [(I1 & I2 & I3 & I4) | [(S1 & S2 & S3 & S4 & S5) | [(D1 & (b & n & Hin & N8 & B1 & B2 & SZ)) | (F1 & F2 & F3 & F4)]]]].
  - exfalso. clear - H0 Hn. lia.
  - left. exact (conj I1 (conj I2 I4)).
  - right. split; [left; exact (conj S1 (conj S2 S3)) | exact S5].
  - right. pose proof (CHA.rf_blk _ _ _ _ RF (b, n) (Hincl _ Hin)) as (R0 & R1 & R16 & R3 & R4 & R5). cbn [fst snd] in R0, R1, R16, R3, R4, R5.
    split; [right; left; exists b, n; exact (conj Hin (conj B1 B2))|].
    exact (gran_zero_of_blockz M b n q (len src) (CHA.mod8_of_16 _ R16) N8 ltac:(clear - R0; lia) B1 B2 ltac:(clear - Hn; lia) SZ).
  - right. split; [right; right; exact (conj F2 F3) | exact F4].
Qed.

(* [comment removed for export] *)
Lemma src_rng : forall (M : mem) LBd LB FF sp o q (src : list Z),
  srcK M LBd FF sp o q src -> CHA.rng_facts L ar LB FF -> incl LBd LB -> ahl_ceil ar <= sp -> 1 <= len src ->
  4096 <= q /\ q + len src <= 2 ^ 47 /\ app_rng ar q (len src)
  /\ ((q + len src <= PMLA.IMG_RO_HI IC /\ img_cls q (len src)) \/ (sp <= q /\ q + len src <= ar_sptop ar) \/ q + len src <= ahl_ceil ar).
Proof.
  intros M LBd LB FF sp o q src [_ HC] RF Hincl CSP Hn.
  pose proof (L5A.aly_img_lo L C LAY) as ILO. pose proof (L5A.aly_img_hi L C LAY) as IHI.
  destruct (CHA.rf_ceil _ _ _ _ RF) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RF) as (SP1 & SP16).
  unfold app_rng, BIGSHADOW_LO, BIGSHADOW_HI in *.
  destruct HC as [IMG | [LC _]].
  - pose proof IMG as (I1 & I2 & I3). destruct (IMG_RO_ok q ltac:(clear - I1 I2 Hn; lia)) as [X1 _]. destruct (IMG_RO_ok (q + len src - 1) ltac:(clear - I1 I2 Hn; lia)) as [X2 _].
    rewrite ILO, IHI in *. split; [clear - X1; lia|]. split; [clear - X2; lia|]. split; [clear - X1 X2 CL CSP SP1; lia|]. left. exact (conj I2 IMG).
  - destruct LC as [(S1 & S2 & S3) | [(b & n & Hin & B1 & B2) | ((f & Hf & F1 & F2) & F3)]].
    + split; [clear - S1 CSP CL; lia|]. split; [clear - S2 SP1; lia|]. split; [clear - S1 S2 CSP CL SP1; lia|]. right; left. exact (conj S1 S2).
    + pose proof (CHA.rf_blk _ _ _ _ RF (b, n) (Hincl _ Hin)) as (R0 & R1 & R16 & R3 & R4 & (R5 & R6 & R7)). cbn [fst snd] in *. unfold BIGSHADOW_LO, BIGSHADOW_HI in R6.
      split; [clear - R0 B1; lia|]. split; [clear - R7 B2; lia|]. split; [clear - R0 R4 R6 R7 B1 B2 CSP SP1; lia|]. right; right. clear - R4 B2; lia.
    + destruct (CL5A.infr_rng L ar LB FF q (len src) RF (ex_intro _ f (conj Hf (conj F1 F2))) ltac:(clear - Hn; lia)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      destruct (CHA.rf_fs _ _ _ _ RF) as ((A0 & A1 & A2) & A3 & A4). unfold BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in *. rewrite ILO, IHI in *.
      split; [clear - Q1 A4 A0; lia|]. split; [exact Q6|]. split; [clear - Q3 Q4 Q5 Q6 CSP SP1; lia|]. right; right. exact Q4.
Qed.
(* [comment removed for export] *)
Lemma src_aclient : forall (M : mem) LBd LB FF sp o q (src : list Z) LBx spx scrx,
  srcK M LBd FF sp o q src -> CHA.rng_facts L ar LB FF -> incl LBd LB -> incl LBd LBx -> spx <= sp -> ahl_ceil ar <= sp -> 1 <= len src ->
  forall a, q <= a < q + len src -> 0 <= a < 2 ^ 64 /\ aclient L ar LBx FF spx scrx a /\ (hl_img_lo L <= a < hl_img_hi L \/ ahl_ceil ar <= a \/ in_block LBd a \/ in_fframe FF a).
Proof.
  intros M LBd LB FF sp o q src LBx spx scrx SK RF Hincl Hx Hspx CSP Hn a Ha. pose proof SK as [_ HC].
  destruct (src_rng M LBd LB FF sp o q src SK RF Hincl CSP Hn) as (Q0 & Q1 & Q2 & _).
  split; [clear - Q0 Q1 Ha; lia|].
  destruct HC as [(I1 & I2 & I3) | [LC _]].
  - destruct (IMG_RO_ok a ltac:(clear - I1 I2 Ha; lia)) as [X1 X2]. split; [right; right; left; exact (conj X1 X2) | left; exact X1].
  - destruct LC as [(S1 & S2 & S3) | [(b & n & Hin & B1 & B2) | ((f & Hf & F1 & F2) & F3)]].
    + split; [right; left; split; [clear - S1 S2 CSP Ha Q1; lia | clear - S1 Hspx Ha; lia] | right; left; clear - S1 CSP Ha; lia].
    + split; [left; exists (b, n); split; [exact (Hx _ Hin) | cbn [fst snd]; clear - B1 B2 Ha; lia] | right; right; left; exists (b, n); split; [exact Hin | cbn [fst snd]; clear - B1 B2 Ha; lia]].
    + assert (FR : in_fframe FF a) by (exists f; split; [exact Hf | clear - F1 F2 Ha; lia]). split; [right; right; right; left; exact FR | right; right; right; exact FR].
Qed.

(* [comment removed for export] *)
Lemma srcsh_aclient : forall (M : mem) LBd LB FF sp o q (src : list Z) LBx spx scrx,
  srcK M LBd FF sp o q src -> loc_cls LBd FF sp o q (len src) -> CHA.rng_facts L ar LB FF -> incl LBd LB -> incl LBd LBx -> ahl_ceil ar <= sp -> sp mod 16 = 0 -> 1 <= len src ->
  forall a, in_shadow_of (gbase q) (8 * gcnt q (len src)) a -> 2147450880 <= a < 17594333495296 /\ aclient L ar LBx FF spx scrx a.
Proof.
  intros M LBd LB FF sp o q src LBx spx scrx SK LC RF Hincl Hx CSP S16 Hn a Ha.
  destruct (src_rng M LBd LB FF sp o q src SK RF Hincl CSP Hn) as (Q0 & Q1 & Q2 & _).
  destruct (CHA.rf_ceil _ _ _ _ RF) as (CL & C8). destruct (CHA.rf_sptop _ _ _ _ RF) as (SP1 & SP16).
  destruct (gran_cover q (len src) ltac:(clear - Q0; lia) ltac:(clear - Hn; lia)) as (G1 & G2 & G3 & G4 & G5 & G6).
  assert (SHR : forall p n x, 0 <= p -> 0 < n -> p + n <= 2 ^ 47 -> in_shadow_of p n x -> 2147450880 <= x < 17594333495296) by exact CHA.shadow_range.
  destruct LC as [(S1 & S2 & S3) | [(b & n & Hin & B1 & B2) | ((f & Hf & F1 & F2) & F3)]].
  - (* [comment removed for export] *)
    assert (LO : sp <= gbase q) by (unfold gbase; clear - S1 S16; pose proof (Z_div_mod_eq_full sp 16); pose proof (Z_div_mod_eq_full q 8); pose proof (Z.mod_pos_bound q 8 ltac:(lia)); lia).
    assert (HIb : gbase q + 8 * gcnt q (len src) <= ar_sptop ar) by (unfold gbase, gcnt in *; clear - S2 SP16 G5; pose proof (Z_div_mod_eq_full (ar_sptop ar) 16); lia).
    split; [exact (SHR (gbase q) (8 * gcnt q (len src)) a G6 ltac:(clear - G4; lia) ltac:(clear - HIb SP1; lia) Ha)|].
    do 4 right. left. unfold in_shadow_of, S in Ha |- *. clear - Ha LO HIb CSP SP1 G4.
    assert (D1 : ahl_ceil ar / 8 <= gbase q / 8) by (apply Z.div_le_mono; lia).
    assert (D2 : (gbase q + 8 * gcnt q (len src) - 1) / 8 <= (ahl_ceil ar + (2 ^ 47 - ahl_ceil ar) - 1) / 8) by (apply Z.div_le_mono; lia). lia.
  - (* [comment removed for export] *)
    pose proof (CHA.rf_blk _ _ _ _ RF (b, n) (Hincl _ Hin)) as (R0 & R1 & R16 & R3 & R4 & (R5 & R6 & R7)). cbn [fst snd] in *.
    assert (Hs : in_shadow_of b n a).
    { unfold in_shadow_of, S in Ha |- *. assert (D1 : b / 8 <= gbase q / 8) by (apply Z.div_le_mono; [clear; lia|]; clear - B1 R16; unfold gbase; pose proof (Z.mod_pos_bound q 8 ltac:(lia)); pose proof (Z_div_mod_eq_full q 8); pose proof (Z_div_mod_eq_full b 16); lia).
      assert (D2 : (gbase q + 8 * gcnt q (len src) - 1) / 8 <= (b + n - 1) / 8) by (rewrite (gran_last q (len src) ltac:(clear - Q0; lia) ltac:(clear - Hn; lia)); apply Z.div_le_mono; [clear; lia | clear - B2; lia]).
      clear - Ha D1 D2. lia. }
    split; [exact (SHR b n a R5 R3 R7 Hs)|]. do 6 right. exists (b, n). split; [exact (Hx _ Hin) | exact Hs].
  - (* [comment removed for export] *)
    destruct (CL5A.infr_rng L ar LB FF q (len src) RF (ex_intro _ f (conj Hf (conj F1 F2))) ltac:(clear - Hn; lia)) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
    destruct (CHA.rf_frm _ _ _ _ RF f Hf) as (W1 & W2 & W3 & W4 & W5). destruct (CHA.rf_fs _ _ _ _ RF) as ((A0 & A1 & A2) & A3 & A4).
    assert (Hs : in_shadow_of (ff_addr f) (ff_bytes (ff_class f)) a).
    { unfold in_shadow_of, S in Ha |- *. assert (D1 : ff_addr f / 8 <= gbase q / 8) by (apply Z.div_le_mono; [clear; lia|]; clear - F1 W3; unfold gbase; pose proof (Z.mod_pos_bound q 8 ltac:(lia)); pose proof (Z_div_mod_eq_full q 8); pose proof (Z_div_mod_eq_full (ff_addr f) 64); lia).
      assert (D2 : (gbase q + 8 * gcnt q (len src) - 1) / 8 <= (ff_addr f + ff_bytes (ff_class f) - 1) / 8) by (rewrite (gran_last q (len src) ltac:(clear - Q0; lia) ltac:(clear - Hn; lia)); apply Z.div_le_mono; [clear; lia | clear - F2; lia]).
      clear - Ha D1 D2. lia. }
    split; [exact (SHR (ff_addr f) (ff_bytes (ff_class f)) a ltac:(clear - A0 W1; lia) ltac:(clear - W5; lia) ltac:(clear - W2 A2 A3 R6 R4; unfold FS_BYTES in *; lia) Hs)|].
    do 5 right. left. exists f. split; [exact Hf | exact Hs].
Qed.

(* [comment removed for export] *)
Lemma srcK_ag : forall (M M' : mem) LBd FF sp o q (src : list Z),
  0 <= q -> q + len src <= 2 ^ 47 ->
  (forall a, q <= a < q + len src -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  (loc_cls LBd FF sp o q (len src) -> forall a, in_shadow_of (gbase q) (8 * gcnt q (len src)) a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  srcK M LBd FF sp o q src -> srcK M' LBd FF sp o q src.
Proof.
  intros M M' LBd FF sp o q src Hq Hhi AB ASH [HB HC]. split.
  - intros i Hi. apply (CL5A.u8_same (hl_segs L) M M' (q + Z.of_nat i)); [clear - Hq; lia | unfold len in Hhi; clear - Hhi Hi; lia | apply AB; unfold len; clear - Hi; lia | exact (HB i Hi)].
  - destruct HC as [IMG | [LC GZ]]; [left; exact IMG | right]. split; [exact LC|].
    unfold PMESA.gran_zero in *. fold (gbase q) in GZ |- *. fold (gcnt q (len src)) in GZ |- *.
    intros j Hj. unfold byte_at in *. rewrite (ASH LC (S (gbase q) + j)); [exact (GZ j Hj)|]. unfold in_shadow_of. unfold S. clear - Hj. lia.
Qed.
(* [comment removed for export] *)
Lemma src_mem_src : forall (M' : mem) LBd LB FF sp o q (src : list Z) LBc LKc crc Ac Vc spc scrc,
  srcK M' LBd FF sp o q src -> CHA.rng_facts L ar LB FF -> incl LBd LB -> incl LBd LBc -> ri_inv HI LBc FF LKc crc Ac M' Vc ->
  spc <= sp -> ahl_ceil ar <= sp -> 1 <= len src ->
  CRC.mem_src L ar LBc FF spc scrc M' q (len src) (map (Z_to_bv 8) src).
Proof.
  intros M' LBd LB FF sp o q src LBc LKc crc Ac Vc spc scrc SK RF Hincl Hx HHc Hspc CSP Hn.
  destruct (src_rng M' LBd LB FF sp o q src SK RF Hincl CSP Hn) as (Q0 & Q1 & Q2 & _). pose proof SK as [HB HC].
  split; [|split; [clear - Q0 Q1; lia | split; [exact Q2 | split]]].
  - destruct HC as [(I1 & I2 & I3) | [LC GZ]]; [exact (I3 _ _ _ _ _ _ _ HHc) | exact (aacc_of_gran_zero M' q (len src) ltac:(clear - Q0; lia) ltac:(clear - Hn; lia) GZ)].
  - intros i Hi. right. exact (proj1 (proj2 (src_aclient M' LBd LB FF sp o q src LBc spc scrc SK RF Hincl Hx Hspc CSP Hn (q + i) ltac:(clear - Hi; lia)))).
  - unfold len. rewrite Nat2Z.id. exact (L5C.bytes_at_rdn (hl_segs L) M' src q ltac:(clear - Q0; lia) ltac:(unfold len in Q1; clear - Q1; lia) HB).
Qed.

(* [comment removed for export] *)
Lemma src_nofoot : forall (M : mem) LBd LB FF sp o q (src : list Z) (SCRx : Z) (BLx : list (Z * Z)),
  srcK M LBd FF sp o q src -> CHA.rng_facts L ar LB FF -> incl LBd LB -> ahl_ceil ar + SCRx <= sp -> 1 <= len src ->
  CL5A.ainfr FF o 24 ->
  (forall b, In b BLx -> q + len src <= fst b \/ fst b + snd b <= q) ->
  (forall b f, In b LBd -> In f FF -> fst b + snd b <= ff_addr f \/ ff_addr f + ff_bytes (ff_class f) <= fst b) ->
  forall a, q <= a < q + len src ->
  ~ ((sp - SCRx <= a < sp) \/ (exists r, In r [(o, 24)] /\ L5.in_rng r a) \/ in_block BLx a \/ in_fframe [] a \/ (exists f, In f [] /\ in_shadow_of (ff_addr f) (ff_bytes (ff_class f)) a)).
Proof.
  intros M LBd LB FF sp o q src SCRx BLx SK RF Hincl CSP Hn Ofr HBL HBF a Ha [X | [X | [X | [X | X]]]].
  - pose proof SK as [_ HC]. pose proof (L5A.aly_img_hi L C LAY) as IHI. destruct (CHA.rf_ceil _ _ _ _ RF) as (CL & _).
    destruct HC as [(I1 & I2 & I3) | [LC _]].
    + destruct (IMG_RO_ok a ltac:(clear - I1 I2 Ha; lia)) as [X1 _]. rewrite IHI in X1. clear - X X1 CL CSP. lia.
    + destruct LC as [(S1 & S2 & S3) | [(b & n & Hin & B1 & B2) | ((f & Hf & F1 & F2) & F3)]].
      * clear - X S1 Ha. lia.
      * pose proof (CHA.rf_blk _ _ _ _ RF (b, n) (Hincl _ Hin)) as (R0 & R1 & R16 & R3 & R4 & R5). cbn [fst snd] in R4. clear - X Ha B2 R4 CSP. lia.
      * destruct (CL5A.infr_rng L ar LB FF q (len src) RF (ex_intro _ f (conj Hf (conj F1 F2))) ltac:(clear - Hn; lia)) as (_ & _ & _ & R4 & _). clear - X Ha R4 CSP. lia.
  - destruct X as (r & [<-|[]] & Hin). unfold L5.in_rng in Hin. cbn [fst snd] in Hin. pose proof SK as [_ HC].
    destruct HC as [(I1 & I2 & I3) | [LC _]].
    + destruct (IMG_RO_ok a ltac:(clear - I1 I2 Ha; lia)) as [X1 _]. destruct (CL5A.infr_rng L ar LB FF o 24 RF Ofr ltac:(clear; lia)) as (_ & _ & _ & _ & _ & _ & O7). clear - X1 O7 Hin. lia.
    + destruct LC as [(S1 & S2 & S3) | [(b & n & Hinb & B1 & B2) | ((f & Hf & F1 & F2) & F3)]].
      * unfold PMLA.apart in S3. clear - S3 Hin Ha. lia.
      * destruct Ofr as (fo & Hfo & O1 & O2). destruct (HBF (b, n) fo Hinb Hfo) as [Y|Y]; cbn [fst snd] in Y; clear - Y Hin Ha B1 B2 O1 O2; lia.
      * unfold PMLA.apart in F3. clear - F3 Hin Ha. lia.
  - destruct X as (b & Hb & Hin). destruct (HBL b Hb) as [Y|Y]; clear - Y Hin Ha; lia.
  - destruct X as (f & [] & _).
  - destruct X as (f & [] & _).
Qed.
(* [comment removed for export] *)
Lemma src_apart_blk : forall (M : mem) LBd LB FF sp o q (src : list Z) u m LBX,
  srcK M LBd FF sp o q src -> CHA.rng_facts L ar LB FF -> incl LBd LB -> ahl_ceil ar <= sp -> 1 <= len src ->
  ablock_range L ar u m -> blocks_apart u m LBX -> incl LBd LBX -> fframes_apart u m FF ->
  q + len src <= u \/ u + m <= q.
Proof.
  intros M LBd LB FF sp o q src u m LBX SK RF Hincl CSP Hn (U0 & U1 & U16 & U3 & U4 & U5) HBA Hx HFA. pose proof SK as [_ HC].
  destruct HC as [(I1 & I2 & I3) | [LC _]].
  - destruct (IMG_RO_ok q ltac:(clear - I1 I2 Hn; lia)) as [X1 _]. destruct (IMG_RO_ok (q + len src - 1) ltac:(clear - I1 I2 Hn; lia)) as [X2 _]. clear - X1 X2 U1 Hn. lia.
  - destruct LC as [(S1 & S2 & S3) | [(b & n & Hin & B1 & B2) | ((f & Hf & F1 & F2) & F3)]].
    + clear - S1 U4 CSP. lia.
    + destruct (HBA (b, n) (Hx _ Hin)) as [Y|Y]; cbn [fst snd] in Y; clear - Y B1 B2; lia.
    + destruct (HFA f Hf) as [Y|Y]; clear - Y F1 F2; lia.
Qed.

(* [comment removed for export] *)
Lemma src_apart_obj : forall (M : mem) LBd LB FF sp o q (src : list Z),
  srcK M LBd FF sp o q src -> CHA.rng_facts L ar LB FF -> incl LBd LB -> 1 <= len src -> CL5A.ainfr FF o 24 ->
  (forall b f, In b LBd -> In f FF -> fst b + snd b <= ff_addr f \/ ff_addr f + ff_bytes (ff_class f) <= fst b) ->
  q + len src <= o \/ o + 24 <= q.
Proof.
  intros M LBd LB FF sp o q src SK RF Hincl Hn Ofr HBF. pose proof SK as [_ HC].
  destruct (CL5A.infr_rng L ar LB FF o 24 RF Ofr ltac:(clear; lia)) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  destruct HC as [(I1 & I2 & I3) | [LC _]].
  - destruct (IMG_RO_ok q ltac:(clear - I1 I2 Hn; lia)) as [X1 _]. destruct (IMG_RO_ok (q + len src - 1) ltac:(clear - I1 I2 Hn; lia)) as [X2 _]. clear - X1 X2 O7 Hn. lia.
  - destruct LC as [(S1 & S2 & S3) | [(b & n & Hin & B1 & B2) | (F12 & F3)]]; [exact S3 | | exact F3].
    destruct Ofr as (f & Hf & F1 & F2). destruct (HBF (b, n) f Hin Hf) as [Y|Y]; cbn [fst snd] in Y; clear - Y B1 B2 F1 F2; lia.
Qed.
End K.
End EAKA.
