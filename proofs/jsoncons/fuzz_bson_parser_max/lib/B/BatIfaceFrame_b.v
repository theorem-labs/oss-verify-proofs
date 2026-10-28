(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceABx ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatPoison_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatDepot_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInv_b BatLift_b BatFsInv_b BatFsInvLaws_b BatIfaceLaws_b BatInvFrame_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx ShadowRLawsB.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Lemma art_S_range47 : forall y, 0 <= y < 2 ^ 47 -> 0x7fff8000 <= HeapIfaceA.S y < 0x10007fff8000.
Proof.
  intros y Hy. unfold HeapIfaceA.S, HeapIfaceA.SB. pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)).
  assert (y / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma art_shadow_of_range : forall lo n a, 0 <= lo -> 0 < n -> lo + n <= 2 ^ 47 -> in_shadow_of lo n a -> 0x7fff8000 <= a < 0x10007fff8000.
Proof. intros lo n a Hlo Hn Hhi (H1 & H2). pose proof (art_S_range47 lo ltac:(lia)). pose proof (art_S_range47 (lo + n - 1) ltac:(lia)). lia. Qed.
(* [comment removed for export] *)
Lemma art_shadow_apart : forall lo n b m a, 8 * (b / 8) = b -> 8 * ((b + m) / 8) = b + m -> 0 < n -> (lo + n <= b \/ b + m <= lo) ->
  in_shadow_of lo n a -> ~ (HeapIfaceA.S b <= a < HeapIfaceA.S (b + m)).
Proof.
  intros lo n b m a E1 E2 Hn AP (H1 & H2) (K1 & K2). unfold HeapIfaceA.S in *.
  pose proof (Z.mul_div_le lo 8 ltac:(lia)). pose proof (Z.mul_succ_div_gt lo 8 ltac:(lia)).
  pose proof (Z.mul_div_le (lo + n - 1) 8 ltac:(lia)). pose proof (Z.mul_succ_div_gt (lo + n - 1) 8 ltac:(lia)). lia.
Qed.

Lemma block_shadow_dec : forall LB a, block_shadow LB a \/ ~ block_shadow LB a.
Proof.
  induction LB as [|b r IH]; intros a; [right; intros (x & [] & _)|].
  destruct (IH a) as [Y|N]; [left; destruct Y as (x & Hx & S); exists x; split; [right; exact Hx|exact S]|].
  destruct (Z_le_dec (HeapIfaceA.S (fst b)) a) as [L1|L1]; [destruct (Z_le_dec a (HeapIfaceA.S (fst b + snd b - 1))) as [L2|L2]|].
  - left. exists b. split; [left; reflexivity|split; assumption].
  - right. intros (x & [<-|Hx] & S); [unfold in_shadow_of in S; lia|apply N; exists x; split; assumption].
  - right. intros (x & [<-|Hx] & S); [unfold in_shadow_of in S; lia|apply N; exists x; split; assumption].
Qed.

(* [comment removed for export] *)
Lemma art_binv_mem : forall segs MAPS0 RESV0 NOACC0 CEIL BASE BUDGET log A (M M' : word -> option byte) model,
  BInv segs MAPS0 RESV0 NOACC0 CEIL BASE BUDGET log A M model ->
  (forall x : word, bhid A model x = true -> M' x = M x) -> mem_grows M M' ->
  BInv segs MAPS0 RESV0 NOACC0 CEIL BASE BUDGET log A M' model.
Proof.
  intros segs MAPS0 RESV0 NOACC0 CEIL BASE BUDGET log A M M' model B HID GR. destruct B as [? ? ? ? ? ? ? ? ? ? ? ? BZ BS ? ? ? ?]. constructor; try assumption.
  - intros a Ha Hc. rewrite (HID a Ha). exact (BZ a Ha Hc).
  - intros a Ha. apply GR. exact (BS a Ha).
Qed.

Lemma art_S_mono : forall a b, a <= b -> HeapIfaceA.S a <= HeapIfaceA.S b.
Proof. intros a b H. unfold HeapIfaceA.S. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.
Lemma art_S_blk_hi : forall u0 n0 j, 0 < n0 -> (j < n0 / 8 \/ (j = n0 / 8 /\ n0 mod 8 <> 0)) -> HeapIfaceA.S u0 + j <= HeapIfaceA.S (u0 + n0 - 1).
Proof.
  intros u0 n0 j Hn0 Hj. unfold HeapIfaceA.S.
  pose proof (Z.div_mod u0 8 ltac:(lia)) as Du. pose proof (Z.mod_pos_bound u0 8 ltac:(lia)) as Ru.
  pose proof (Z.div_mod n0 8 ltac:(lia)) as Dn. pose proof (Z.mod_pos_bound n0 8 ltac:(lia)) as Rn.
  assert (E : u0 / 8 + j <= (u0 + n0 - 1) / 8); [|lia].
  apply Z.div_le_lower_bound; [lia|]. destruct Hj as [Hj|[Hj Hm]]; lia.
Qed.
Lemma art_mod4096_al8 : forall r, r mod 4096 = 0 -> 8 * (r / 8) = r.
Proof. intros r H. pose proof (Z.div_mod r 4096 ltac:(lia)) as D. rewrite H, Z.add_0_r in D. rewrite D at 1. replace (4096 * (r / 4096)) with ((512 * (r / 4096)) * 8) by lia. rewrite Z.div_mul by lia. lia. Qed.

Section Frame.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable L : asan_layout.
Hypothesis HLsegs : hl_segs L = ASEGS.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
Hypothesis HLtls : forall a, (rn_tp rn - 88 <= a < rn_tp rn - 80 \/ rn_tsd rn + 8 * rn_key rn <= a < rn_tsd rn + 8 * rn_key rn + 8
                              \/ 0x673cf8 <= a < 0x673d00 \/ 0x673d28 <= a < 0x673d30 \/ rn_tp rn <= a < rn_tp rn + 8
                              \/ rn_tp rn + rn_loff rn <= a < rn_tp rn + rn_loff rn + 4) -> hl_rt_static L a.
Hypothesis HLro : forall a, 0x10000 <= a < 0x139000 -> hl_rt_ro L a.
Hypothesis HLcs : forall a, (0x1392d8 <= a < 0x1392e0 \/ 0x1393a0 <= a < 0x1393b8 \/ rn_tp rn + 8 <= a < rn_tp rn + 16) -> hl_rt_static L a.   (* [comment removed for export] *)

(* [comment removed for export] *)
Section State.
Variables (G : art_gs art_fsg) (LB : list (Z * Z)) (FF LK : list fframe) (A : list (Z * Z)) (M Mr : word -> option byte) (lazy : list (word * word)).
Hypothesis REP : art_alloc_rep art_fsg rn G LB Mr.
Hypothesis FS : art_fsinv rn (g_fs art_fsg G) FF LK M.
Hypothesis CLI : art_client_ok rn LB FF LK A M.
Hypothesis LIVEOK : live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)).
Hypothesis KN : art_kn_ok MAPS0 RESV0 rn.
Hypothesis LZ : art_lazy_ok art_fsg rn G A lazy.
Hypothesis EG : art_eager_ok LB A lazy.

#[using="G LB Mr REP"] Lemma art_hi_bounds : 0x10007fff8000 <= rn_HI rn /\ rn_HI rn + 8388608 <= 2 ^ 47.
Proof. destruct REP as (ROK & _). rok_open ROK. geo_open GEO. split; assumption. Qed.

(* [comment removed for export] *)
#[using="MAPS0 RESV0 LIVEOK KN"] Lemma art_live_facts : forall p, In p (art_live (g_log art_fsg G)) ->
  0 < fst p /\ 0 < snd p /\ fst p mod 4096 = 0 /\ snd p mod 4096 = 0 /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
  /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o)).
Proof.
  intros p Hp. destruct LIVEOK as (LO & _). destruct (LO p Hp) as (P0 & P1 & P2 & P3 & P4 & P5 & P6). unfold SHLO, SHHI in P5.
  repeat (split; [assumption|]). intros o Ho. destruct (KN o Ho) as (q & Hq & Q1 & Q2). specialize (P6 q Hq). unfold apart. lia.
Qed.

(* [comment removed for export] *)
#[using="G LK M FS"] Lemma art_frame_facts : forall f, In f FF -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f).
Proof. intros f Hf. pose proof (fsinv_frame_in rn _ FF LK M FS f ltac:(apply in_or_app; left; exact Hf)). lia. Qed.
#[using="G LB Mr REP"] Lemma art_fs_facts : 4096 <= ar_fs (rn_ar rn) /\ ar_fs (rn_ar rn) + FS_BYTES <= rn_HI rn /\ (ar_fs (rn_ar rn) + FS_BYTES <= 0x10000 \/ 0x696000 <= ar_fs (rn_ar rn))
  /\ (ar_fs (rn_ar rn) + FS_BYTES <= 0x7fff7000 \/ 0x10007fff8000 <= ar_fs (rn_ar rn)).
Proof.
  destruct REP as (ROK & _). rok_open ROK. destruct Fapp as (_ & Fap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Fap. repeat split; assumption.
Qed.

(* [comment removed for export] *)
#[using="HLlo HLhi G LK A M Mr REP FS CLI"] Lemma art_priv_app : forall a, a < rn_HI rn -> ~ in_block LB a -> (~ (0x10000 <= a < 0x696000) \/ hl_rt_static L a \/ hl_rt_ro L a) -> ~ in_fframe FF a ->
  (a < 0x7fff8000 \/ 0x10007fff8000 <= a) -> art_private L (rn_ar rn) LB FF a.
Proof.
  intros a Hhi NB IMG NF APP. destruct art_hi_bounds as (HI1 & HI2). destruct art_fs_facts as (F1 & F2 & F3 & F4).
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
  assert (NSH : forall lo n, 0 <= lo -> 0 < n -> lo + n <= 2 ^ 47 -> ~ in_shadow_of lo n a).
  { intros lo n H1 H2 H3 SH. pose proof (art_shadow_of_range lo n a H1 H2 H3 SH). lia. }
  assert (C3F : hl_rt_ro L a \/ ~ ((hl_img_lo L <= a < hl_img_hi L) /\ ~ hl_rt_static L a)).
  { destruct IMG as [NI|[ST|RO]]; [right|right|left; exact RO]; intros (C & C'); [rewrite HLlo, HLhi in C; exact (NI C)|exact (C' ST)]. }
  destruct C3F as [RO|C3F]; [right; left; exact RO|]. left. intros CL. unfold aclient, aclient_g in CL.
  destruct CL as [C|[(C & _)|[C|[C|[C|[(f & Hf & C)|(b & Hb & C)]]]]]].
  - exact (NB C).
  - rewrite HIeq in C. lia.
  - exact (C3F C).
  - exact (NF C).
  - apply (NSH (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn))); [rewrite HIeq; lia|rewrite HIeq; lia|lia|exact C].
  - destruct (art_frame_facts f Hf) as (K1 & K2 & K3). apply (NSH (ff_addr f) (ff_bytes (ff_class f))); [lia|exact K3|unfold FS_BYTES in *; lia|exact C].
  - destruct CLI as (CB & _). destruct (CB b Hb) as (B1 & _ & _ & B4 & B5 & _). rewrite HIeq in B5. apply (NSH (fst b) (snd b)); [lia|exact B4|lia|exact C].
Qed.

(* [comment removed for export] *)
#[using="HLlo HLhi G LK A M Mr REP FS CLI"] Lemma art_priv_shadow : forall a b m, 8 * (b / 8) = b -> 8 * ((b + m) / 8) = b + m -> 0 <= b -> 0 < m -> b + m <= rn_HI rn ->
  (b + m <= 0x7fff7000 \/ 0x10007fff8000 <= b) -> apart b m (ar_fs (rn_ar rn)) FS_BYTES ->
  HeapIfaceA.S b <= a < HeapIfaceA.S (b + m) -> art_private L (rn_ar rn) LB FF a.
Proof.
  intros a b m E1 E2 Hb Hm Hhi APP AF Ha. destruct art_hi_bounds as (HI1 & HI2). destruct art_fs_facts as (F1 & F2 & F3 & F4).
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
  assert (RA : 0x7fff8000 <= a < 0x10007fff8000).
  { unfold HeapIfaceA.S, HeapIfaceA.SB in Ha. pose proof (Z.div_pos b 8 ltac:(lia) ltac:(lia)). assert ((b + m) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
  destruct (block_shadow_dec LB a) as [Y|N]; [right; right; exact Y|]. left. intros CL. unfold aclient, aclient_g in CL.
  destruct CL as [(x & Hx & C)|[(C & _)|[(C & _)|[(f & Hf & C & _)|[C|[(f & Hf & C)|C]]]]]].
  - destruct CLI as (CB & _). destruct (CB x Hx) as (_ & _ & _ & _ & _ & (_ & B6 & _) & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in B6. lia.
  - rewrite HIeq in C. lia.
  - rewrite HLlo, HLhi in C. lia.
  - destruct (art_frame_facts f Hf) as (K1 & K2 & K3). unfold FS_BYTES in *. lia.
  - destruct C as (C1 & _). pose proof (art_S_mono (b + m) (ahl_ceil (rn_ar rn)) ltac:(rewrite HIeq; lia)). lia.
  - destruct (art_frame_facts f Hf) as (K1 & K2 & K3).
    apply (art_shadow_apart (ff_addr f) (ff_bytes (ff_class f)) b m a E1 E2 K3); [unfold apart, FS_BYTES in *; lia|exact C|exact Ha].
  - exact (N C).
Qed.

(* [comment removed for export] *)
#[using="HLlo HLhi G LK M Mr REP FS CLI LZ EG"] Lemma art_priv_hidden : forall x : word, mkH lazy A x = true -> art_private L (rn_ar rn) LB FF (U x).
Proof.
  intros x Hx. unfold mkH in Hx. apply andb_prop in Hx as [Hl Ha]. apply negb_true_iff in Ha.
  destruct REP as (ROK & _). destruct LZ as (L1 & _). destruct (art_lazy_zone_bounds art_fsg rn G (U x) ROK (L1 x Hl)) as (B1 & B2).
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
  assert (AL : forall lo n, shadow_allowed A lo n -> ~ in_shadow_of lo n (U x)).
  { intros lo n SA SH. specialize (SA (U x) SH). rewrite Z_to_bv_bv_unsigned in SA. rewrite SA in Ha. discriminate Ha. }
  destruct CLI as (CB & _ & CSA1 & CSA2 & _).
  left. intros CL. unfold aclient, aclient_g in CL.
  destruct CL as [(b & Hb & C)|[(C & _)|[(C & _)|[(f & Hf & C & _)|[C|[(f & Hf & C)|(b & Hb & C)]]]]]].
  - rewrite (proj2 EG b x Hb C) in Hl. discriminate Hl.
  - rewrite HIeq in C. lia.
  - rewrite HLlo, HLhi in C. lia.
  - destruct (art_frame_facts f Hf) as (K1 & K2 & K3). apply B2. lia.
  - exact (AL _ _ CSA1 C).
  - destruct (art_frame_facts f Hf) as (K1 & K2 & K3). apply (AL _ _ CSA2). destruct C as (C1 & C2). split.
    + eapply Z.le_trans; [apply (art_S_mono (ar_fs (rn_ar rn)) (ff_addr f)); lia|exact C1].
    + eapply Z.le_trans; [exact C2|apply art_S_mono; lia].
  - destruct (CB b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & B9 & _). exact (AL _ _ B9 C).
Qed.

(* [comment removed for export] *)
#[using="FF LK A M Mr REP CLI"] Lemma art_block_geo : forall b, In b LB -> 0 < snd b /\
  ((rn_spb rn <= fst b /\ fst b + snd b <= rn_spb rn + 2 ^ 37) \/ (exists p, In p (art_live (g_log art_fsg G)) /\ fst p <= fst b /\ fst b + snd b <= fst p + snd p)).
Proof.
  intros b Hb. destruct CLI as (CB & _). destruct (CB b Hb) as (_ & _ & _ & B4 & _). split; [exact B4|].
  pose proof REP as (_ & _ & _ & (_ & PRIM & _) & CH & SEC & _ & _ & _ & BL & _).
  destruct (BL b Hb) as [(c0 & w0 & Hc0 & V0 & St0)|(s & Hs & Hq & Eu & En0)].
  - left. specialize (CH c0 Hc0). cbv zeta in CH. destruct CH as (_ & _ & _ & III). specialize (III w0 V0). rewrite St0 in III. destruct III as (_ & J2 & J3 & _).
    destruct (PRIM c0 Hc0) as (_ & OK0 & _). destruct OK0 as (_ & (_ & Haumu) & _ & _ & _ & Hmu3 & _). destruct V0 as (V0 & V1 & _). clear - J2 J3 Haumu Hmu3 V0 V1 Hc0. lia.
  - right. destruct SEC as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _). destruct (In_nth_error _ _ Hs) as (i & Hi).
    destruct (SALL i s Hi) as (_ & P2 & _ & _ & _ & _ & P7 & P8 & _). exists (sc_map s, sc_msize s). cbn [fst snd]. rewrite <- Eu, <- En0. split; [exact P2|]. clear - P7 P8. lia.
Qed.

(* [comment removed for export] *)
#[using="MAPS0 RESV0 HLlo HLhi HLst HLtls HLro LK A M Mr REP FS CLI LIVEOK KN"] Lemma art_priv_zone : forall a, art_alloc_zone art_fsg rn G a -> ~ in_block LB a -> art_private L (rn_ar rn) LB FF a.
Proof.
  intros a Z NB. destruct art_hi_bounds as (HI1 & HI2). destruct art_fs_facts as (F1 & F2 & F3 & F4).
  assert (NFR : forall lo n, apart lo n (ar_fs (rn_ar rn)) FS_BYTES -> lo <= a < lo + n -> ~ in_fframe FF a).
  { intros lo n AP Ha (f & Hf & C & _). destruct (art_frame_facts f Hf) as (K1 & K2 & K3). unfold apart, FS_BYTES in *. lia. }
  assert (NFI : 0x10000 <= a < 0x696000 -> ~ in_fframe FF a).
  { intros Ha (f & Hf & C & _). destruct (art_frame_facts f Hf) as (K1 & K2 & K3). unfold FS_BYTES in *. lia. }
  pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  destruct Z as [Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]]]]]]].
  - (* [comment removed for export] *) apply art_priv_app; [unfold art_zone_statics in Z; clear - Z HI1; lia|exact NB|right; left; exact (HLst a Z)|apply NFI; unfold art_zone_statics in Z; clear - Z; lia|unfold art_zone_statics in Z; clear - Z; lia].
  - (* [comment removed for export] *) destruct Z as (Z & _). apply art_priv_app; [clear - Z G8; lia|exact NB|left; clear - Z G9; lia|exact (NFR (rn_t rn) 4096 ltac:(clear - Aft; unfold apart in *; lia) Z)|clear - Z G10; lia].
  - (* [comment removed for export] *) apply art_priv_app; [clear - Z G14; lia|exact NB|left; clear - Z G15; lia|exact (NFR (rn_ctx rn) 4096 ltac:(clear - Afc; unfold apart in *; lia) Z)|clear - Z G16; lia].
  - (* [comment removed for export] *) unfold art_zone_kspace in Z.
    apply art_priv_app; [clear - Z Kend; lia|exact NB|left; clear - Z Khi; lia|exact (NFR (rn_kbase rn) 0x2000011000 ltac:(clear - Afkb; unfold apart in *; lia) Z)|clear - Z Khi; lia].
  - (* [comment removed for export] *) destruct Z as [Z|(p & Hp & Z)].
    + destruct Papp as (_ & Pap & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in Pap.
      apply art_priv_app; [clear - Z Phi; lia|exact NB|left; clear - Z Plo; lia|exact (NFR (rn_parr rn) (2 ^ 23) ltac:(clear - Afp; unfold apart in *; lia) Z)|clear - Z Pap; lia].
    + destruct (art_live_facts p Hp) as (L0 & L1 & _ & _ & L4 & L5 & LO).
      pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))) as Af. cbn [fst snd] in Af.
      pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))) as Ai1.
      pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))) as Ai2.
      pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))))) as Ai3.
      pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))))) as Ai4.
      cbn [fst snd] in Ai1, Ai2, Ai3, Ai4.
      apply art_priv_app; [clear - Z L4; lia|exact NB|left; clear - Z L1 Ai1 Ai2 Ai3 Ai4; unfold apart in *; lia|exact (NFR (fst p) (snd p) Af Z)|clear - Z L5; lia].
  - (* [comment removed for export] *) unfold art_zone_depot, dprivD in Z. destruct Z as [Z|[Z|Z]].
    + apply art_priv_app; [clear - Z HI1; lia|exact NB|right; left; apply HLst; unfold art_zone_statics; clear - Z; lia|apply NFI; clear - Z; lia|clear - Z; lia].
    + apply art_priv_app; [clear - Z Dl2; lia|exact NB|left; clear - Z Il2; lia|exact (NFR (rn_l2 rn) (2 ^ 20) ltac:(clear - Afl; unfold apart in *; lia) Z)|clear - Z Al2s; unfold apart in *; lia].
    + apply art_priv_app; [clear - Z Dblk; lia|exact NB|left; clear - Z Iblk; lia|exact (NFR (rn_blk rn) (2 ^ 23) ltac:(clear - Afb; unfold apart in *; lia) Z)|clear - Z Abs; unfold apart in *; lia].
  - (* [comment removed for export] *) destruct Z as [Z|(p & Hp & Z)].
    + apply (art_priv_shadow a (rn_kbase rn) 0x2000011000); [exact (art_mod4096_al8 _ Kal)| |clear - Khi; lia|lia|exact Kend|right; exact Khi|clear - Afkb; unfold apart in *; lia|exact Z].
      apply art_mod4096_al8. rewrite Z.add_mod by lia. rewrite Kal. reflexivity.
    + destruct (art_live_facts p Hp) as (L0 & L1 & L2 & L3 & L4 & L5 & LO).
      pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))) as Af. cbn [fst snd] in Af.
      apply (art_priv_shadow a (fst p) (snd p)); [exact (art_mod4096_al8 _ L2)| |lia|exact L1|exact L4|exact L5|exact Af|exact Z].
      apply art_mod4096_al8. rewrite Z.add_mod by lia. rewrite L2, L3. reflexivity.
  - (* [comment removed for export] *) right; left. exact (HLro a Z).
  - apply art_priv_app; [clear - Z HI1 G20; lia|exact NB|right; left; apply HLtls; left; exact Z|apply NFI; clear - Z G19 G20 Htpd; lia|clear - Z G20; lia].
  - apply art_priv_app; [clear - Z HI1 G22 Hkey; lia|exact NB|right; left; apply HLtls; right; left; exact Z|apply NFI; clear - Z G21 G22 Hkey; lia|clear - Z G22 Hkey; lia].
  - apply art_priv_app; [clear - Z HI1; lia|exact NB|right; left; apply HLtls; do 2 right; left; exact Z|apply NFI; clear - Z; lia|clear - Z; lia].
  - apply art_priv_app; [clear - Z HI1; lia|exact NB|right; left; apply HLtls; do 3 right; left; exact Z|apply NFI; clear - Z; lia|clear - Z; lia].
Qed.

(* [comment removed for export] *)
#[using="MAPS0 RESV0 HLlo HLhi HLtls G LK A M Mr REP FS CLI LIVEOK KN"] Lemma art_priv_fs3 : forall a, fs_zone3 rn a -> ~ in_fframe FF a -> art_private L (rn_ar rn) LB FF a.
Proof.
  intros a Z NF. destruct art_hi_bounds as (HI1 & HI2). destruct art_fs_facts as (F1 & F2 & F3 & F4).
  pose proof REP as (ROK & _). rok_open ROK. geo_open GEO. destruct CLI as (CB & _).
  destruct Z as [Z|[Z|Z]].
  - apply art_priv_app; [clear - Z F2; lia| |left; clear - Z F3; unfold FS_BYTES in *; lia|exact NF|clear - Z F4; unfold FS_BYTES in *; lia].
    intros (b & Hb & R). destruct (CB b Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B12 & _). clear - Z R B12. lia.
  - apply art_priv_app; [clear - Z G8; lia| |left; clear - Z G9; lia|exact NF|clear - Z G10; lia].
    intros (b & Hb & R). destruct (art_block_geo b Hb) as (Hn0 & [K|(p & Hp & K1 & K2)]).
    + clear - Z R K G11. unfold apart in *. lia.
    + destruct (art_live_facts p Hp) as (_ & _ & _ & _ & _ & _ & LO). pose proof (LO _ (or_introl eq_refl)) as At. cbn [fst snd] in At. clear - Z R K1 K2 At. unfold apart in *. lia.
  - apply art_priv_app; [clear - Z HI1 G20; lia| |right; left; apply HLtls; tauto|exact NF|clear - Z G20; lia].
    intros (b & Hb & R). destruct (CB b Hb) as (_ & B2 & _). clear - Z R B2 G19 G20. lia.
Qed.
(* [comment removed for export] *)
#[using="G LB FF LK M Mr REP FS"] Lemma art_cs_not_fs : forall a, cs_zone rn a -> ~ (ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES).
Proof.
  intros a Z X. destruct art_fs_facts as (F1 & F2 & F3 & F4). pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  destruct (fsinv_cs _ _ _ _ _ FS) as ((Q1 & Q2 & Q3) & _). unfold FS_BYTES, apart in *.
  destruct Z as [Z|[Z|[Z|[Z|Z]]]].
  - clear - Z X F3. lia.
  - clear - Z X F3. lia.
  - clear - Z X F3 G19 Q1. lia.
  - clear - Z X Adf. lia.
  - change (HeapIfaceA.S 0x10000) with 2147459072 in Z. change (HeapIfaceA.S 0x696000) with 2148314112 in Z. clear - Z X F4. lia.
Qed.
#[using="MAPS0 RESV0 HLlo HLhi G LK A M Mr REP FS CLI LIVEOK KN"] Lemma art_priv_dtls : forall a, rn_dtls rn <= a < rn_dtls rn + 4096 -> art_private L (rn_ar rn) LB FF a.
Proof.
  intros a Z. destruct art_hi_bounds as (HI1 & HI2). destruct art_fs_facts as (F1 & F2 & F3 & F4).
  pose proof REP as (ROK & _). rok_open ROK. geo_open GEO. pose proof CLI as (CB & _).
  destruct D3 as (_ & D3a & _). unfold BIGSHADOW_LO, BIGSHADOW_HI in D3a.
  apply art_priv_app; [clear - Z D1; lia | | left; clear - Z D2; lia | | clear - Z D3a; lia].
  - intros (b & Hb & R). destruct (art_block_geo b Hb) as (Hn0 & [K|(p & Hp & K1 & K2)]).
    + clear - Z R K Adk Kspb. unfold apart in *. lia.
    + destruct (art_live_facts p Hp) as (_ & _ & _ & _ & _ & _ & LO).
      pose proof (LO (rn_dtls rn, 4096) ltac:(unfold art_objs; do 11 right; left; reflexivity)) as At. cbn [fst snd] in At. clear - Z R K1 K2 At. unfold apart in *. lia.
  - intros (f & Hf & C & _). destruct (art_frame_facts f Hf) as (K1 & K2 & K3). clear - Z C K1 K2 Adf. unfold apart, FS_BYTES in *. lia.
Qed.
#[using="MAPS0 RESV0 HLlo HLhi HLcs G LK A M Mr REP FS CLI LIVEOK KN"] Lemma art_priv_cs : forall a, cs_zone rn a -> art_private L (rn_ar rn) LB FF a.
Proof.
  intros a Z. destruct art_hi_bounds as (HI1 & HI2). destruct art_fs_facts as (F1 & F2 & F3 & F4).
  pose proof (art_cs_not_fs a Z) as NFS.
  assert (NF : ~ in_fframe FF a).
  { intros (f & Hf & C & _). destruct (art_frame_facts f Hf) as (K1 & K2 & K3). apply NFS. unfold FS_BYTES in *. clear - C K1 K2. lia. }
  pose proof REP as (ROK & _). rok_open ROK. geo_open GEO. pose proof CLI as (CB & _).
  destruct (fsinv_cs _ _ _ _ _ FS) as ((Q1 & Q2 & Q3) & _).
  assert (NBI : 0x10000 <= a < 0x696000 -> ~ in_block LB a).
  { intros Ha (b & Hb & R). destruct (CB b Hb) as (_ & B2 & _). clear - Ha R B2. lia. }
  destruct Z as [Z|[Z|[Z|[Z|Z]]]].
  - apply art_priv_app; [clear - Z HI1; lia | apply NBI; clear - Z; lia | right; left; apply HLcs; clear - Z; lia | exact NF | clear - Z; lia].
  - apply art_priv_app; [clear - Z HI1; lia | apply NBI; clear - Z; lia | right; left; apply HLcs; clear - Z; lia | exact NF | clear - Z; lia].
  - apply art_priv_app; [clear - Z HI1 Q1; lia | apply NBI; clear - Z G19 Q1; lia | right; left; apply HLcs; clear - Z; lia | exact NF | clear - Z Q1; lia].
  - apply art_priv_dtls. clear - Z. lia.
  - apply (art_priv_shadow a 0x10000 0x686000); [reflexivity | reflexivity | lia | lia | clear - HI1; lia | left; lia | clear - F3; unfold apart, FS_BYTES in *; lia | exact Z].
Qed.
End State.

Let AFL : art_alloc_rep_frame_law art_fsg MAPS0 RESV0 := art_alloc_rep_frame_law_proved art_fsg MAPS0 RESV0.
#[local] Abbreviation HI := (art_iface art_fsg MAPS0 RESV0 NOACC0 BASE BUDGET art_fsinv rn).

#[using="HLlo HLhi HLst HLtls HLro HLcs AFL"] Theorem art_law_frame : rt_frame L (rn_ar rn) HI.
Proof.
  intros LB FF LK cr A M M' V (G & REP & FS & BV & CRED & CLI & KN & LZ & EG) PRIV MONO.
  pose proof (BINV_live _ _ _ _ _ _ _ _ _ _ _ _ BV) as LIVEOK.
  assert (PV : forall x : word, art_private L (rn_ar rn) LB FF (U x) -> M' x = M x).
  { intros x Hp. specialize (PRIV (U x) (u64_range x) Hp). rewrite Z_to_bv_bv_unsigned in PRIV. exact PRIV. }
  set (H := mkH (snd V) A) in *.
  assert (HIDEQ : forall x : word, H x = true -> M' x = M x).
  { intros x Hx. apply PV. exact (art_priv_hidden G LB FF LK A M (mrestrict H M) (snd V) REP FS CLI LZ EG x Hx). }
  exists G.
  split.
  { apply (AFL rn G LB (mrestrict H M) (mrestrict H M') REP).
    - intros x Dx. unfold mrestrict in *. destruct (H x); [exact Dx|apply MONO; exact Dx].
    - intros x Zx NB. unfold mrestrict. destruct (H x) eqn:E; [reflexivity|]. apply PV.
      exact (art_priv_zone G LB FF LK A M (mrestrict H M) REP FS CLI LIVEOK KN (U x) Zx NB).
    - pose proof REP as (ROK & _ & (_ & _ & _ & _ & _ & _ & _ & C7) & _). rok_open ROK. geo_open GEO.
      apply (art_cell_agree ASEGS (mrestrict H M) (mrestrict H M')); [|clear - Hloff Hloff' G19; lia|cbn; clear - Hloff'' ; lia|exact C7].
      intros x Hx. unfold mrestrict. destruct (H x) eqn:E; [reflexivity|]. apply PV. destruct (art_hi_bounds G LB (mrestrict H M) REP) as (HI1 & _).
      apply (art_priv_app G LB FF LK A M (mrestrict H M) REP FS CLI); [clear - Hx Hloff'' HI1; cbn in Hx; lia| |right; left; apply HLtls; cbn in Hx; clear - Hx; lia| |clear - Hx Hloff''; cbn in Hx; lia].
      + intros (b & Hb & R). destruct CLI as (CB & _). destruct (CB b Hb) as (_ & B2 & _). clear - Hx R B2 Hloff' Hloff''. cbn in Hx. lia.
      + intros (f & Hf & C & _). destruct (art_frame_facts G FF LK M FS f Hf) as (K1 & K2 & K3). clear - Hx C K1 K2 Fimg Hloff' Hloff''. unfold FS_BYTES in *. cbn in Hx. lia.
    - exact LIVEOK.
    - exact KN. }
  split.
  { apply (art_fsinv_client_proved rn (g_fs art_fsg G) FF LK M M' FS MONO).
    - intros x a Z NF. apply PV. exact (art_priv_fs3 G LB FF LK A M (mrestrict H M) REP FS CLI LIVEOK KN a Z NF).
    - intros x Z. apply PV. exact (art_priv_cs G LB FF LK A M (mrestrict H M) REP FS CLI LIVEOK KN (U x) Z). }
  split.
  { destruct BV as (AW & LO & BF). split; [exact AW|]. split; [exact LO|]. intros model E1 E2 Hh Hm.
    apply (art_binv_mem _ _ _ _ _ _ _ _ _ M M' model (BF model E1 E2 Hh Hm)); [|exact MONO].
    intros x Hx. apply HIDEQ. unfold bhid in Hx. rewrite E2 in Hx. exact Hx. }
  split; [exact CRED|].
  split.
  { destruct CLI as (CB & CREST). split; [|exact CREST]. intros b Hb. destruct (CB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & BREST).
    repeat (split; [assumption|]). split; [intros i Hi; apply MONO; exact (B7 i Hi)|]. split; [|exact BREST].
    assert (T : forall j v, 0 <= j -> (j < snd b / 8 \/ (j = snd b / 8 /\ snd b mod 8 <> 0)) -> byte_at M (HeapIfaceA.S (fst b) + j) v -> byte_at M' (HeapIfaceA.S (fst b) + j) v).
    { intros j v Hj0 Hj B. unfold byte_at in *. rewrite PRIV; [exact B| |right; right; exists b; split; [exact Hb|]].
      - pose proof (art_S_blk_hi (fst b) (snd b) j B4 Hj) as H1.
        assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in B5. destruct (art_hi_bounds G LB (mrestrict H M) REP) as (_ & HI2).
        pose proof (art_S_range47 (fst b) ltac:(clear - B1 B4 B5 HI2; lia)) as H0.
        pose proof (art_S_range47 (fst b + snd b - 1) ltac:(clear - B1 B4 B5 HI2; lia)) as H2. clear - Hj0 H0 H1 H2. lia.
      - split; [clear - Hj0; lia|exact (art_S_blk_hi (fst b) (snd b) j B4 Hj)]. }
    apply (shadow_blkR_tby M M' (fst b) (snd b) B4); [intros j Hj0 Hj v Bv; exact (T j v Hj0 Hj Bv)|exact B8]. }
  split; [exact KN|]. split; [exact LZ|exact EG].
Qed.

(* [comment removed for export] *)
Hypothesis HCtp : rn_tp rn = 0x673d00.
Hypothesis HCloff : rn_loff rn = 0x10.
Hypothesis HCtsd : rn_tsd rn = 0x6951b8.
Hypothesis HCkey : rn_key rn = 0.
Hypothesis HLtp : hl_tp L = 0x673d00.

Section Ctr.
Variables (G : art_gs art_fsg) (LB : list (Z * Z)) (Mr : word -> option byte).
Hypothesis REP : art_alloc_rep art_fsg rn G LB Mr.
Hypothesis LIVEOK : live_ok MAPS0 RESV0 (rn_HI rn) (art_live (g_log art_fsg G)).
Hypothesis KN : art_kn_ok MAPS0 RESV0 rn.
#[using="HCtp HCloff HCtsd HCkey MAPS0 RESV0 LB Mr REP LIVEOK KN"] Lemma art_zone_not_ctr : forall a, art_alloc_zone art_fsg rn G a -> ~ (0x673d10 <= a < 0x673d14).
Proof.
  intros a Z Hc. pose proof REP as (ROK & _). rok_open ROK. geo_open GEO.
  assert (SB0 : forall y, 0 <= y -> 0x7fff8000 <= HeapIfaceA.S y) by (intros y Hy; unfold HeapIfaceA.S, HeapIfaceA.SB; pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)); lia).
  destruct Z as [Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|[Z|Z]]]]]]]]]]].
  - unfold art_zone_statics in Z. clear - Z Hc. lia.
  - destruct Z as (Z & _). clear - Z Hc G9. lia.
  - clear - Z Hc G15. lia.
  - unfold art_zone_kspace in Z. clear - Z Hc Khi. lia.
  - destruct Z as [Z|(p & Hp & Z)].
    + clear - Z Hc Plo. lia.
    + destruct (art_live_facts G LIVEOK KN p Hp) as (L0 & L1 & _ & _ & L4 & L5 & LO).
      pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))) as Ai1.
      pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))) as Ai2.
      pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl))))))))))) as Ai3.
      pose proof (LO _ (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_intror (or_introl eq_refl)))))))))))) as Ai4.
      cbn [fst snd] in Ai1, Ai2, Ai3, Ai4. clear - Z Hc L1 Ai1 Ai2 Ai3 Ai4. unfold apart in *. lia.
  - unfold art_zone_depot, dprivD in Z. destruct Z as [Z|[Z|Z]]; [clear - Z Hc; lia|clear - Z Hc Il2; lia|clear - Z Hc Iblk; lia].
  - destruct Z as [Z|(p & Hp & Z)].
    + pose proof (SB0 (rn_kbase rn) ltac:(lia)). clear - Z Hc H. lia.
    + destruct (art_live_facts G LIVEOK KN p Hp) as (L0 & _). pose proof (SB0 (fst p) ltac:(lia)). clear - Z Hc H. lia.
  - clear - Z Hc. lia.
  - rewrite HCtp in Z. clear - Z Hc. lia.
  - rewrite HCtsd, HCkey in Z. clear - Z Hc. lia.
  - clear - Z Hc. lia.
  - clear - Z Hc. lia.
Qed.
End Ctr.

#[using="HLsegs HLlo HLhi HLst HLtls HLro HLcs HCtp HCloff HCtsd HCkey HLtp AFL"] Theorem art_law_frame_ctr : HAJ.rt_frame_ctr L (rn_ar rn) HI.
Proof.
  intros LB FF LK cr A M M' V (G & REP & FS & BV & CRED & CLI & KN & LZ & EG) PRIV CTR MONO.
  pose proof (BINV_live _ _ _ _ _ _ _ _ _ _ _ _ BV) as LIVEOK.
  rewrite HLtp in PRIV, CTR. rewrite HLsegs in CTR.
  assert (PV : forall x : word, art_private L (rn_ar rn) LB FF (U x) -> ~ (0x673d10 <= U x < 0x673d14) -> M' x = M x).
  { intros x Hp Hn. specialize (PRIV (U x) (u64_range x) Hp ltac:(clear - Hn; lia)). rewrite Z_to_bv_bv_unsigned in PRIV. exact PRIV. }
  set (H := mkH (snd V) A) in *.
  assert (HNC : forall x : word, H x = true -> ~ (0x673d10 <= U x < 0x673d14)).
  { intros x Hx. unfold H, mkH in Hx. apply andb_prop in Hx as [Hl _]. pose proof REP as (ROK & _). destruct LZ as (L1 & _).
    destruct (art_lazy_zone_bounds art_fsg rn G (U x) ROK (L1 x Hl)) as ((B1 & _) & _). clear - B1. lia. }
  assert (HIDEQ : forall x : word, H x = true -> M' x = M x).
  { intros x Hx. apply PV; [exact (art_priv_hidden G LB FF LK A M (mrestrict H M) (snd V) REP FS CLI LZ EG x Hx)|exact (HNC x Hx)]. }
  exists G.
  split.
  { apply (AFL rn G LB (mrestrict H M) (mrestrict H M') REP).
    - intros x Dx. unfold mrestrict in *. destruct (H x); [exact Dx|apply MONO; exact Dx].
    - intros x Zx NB. unfold mrestrict. destruct (H x) eqn:E; [reflexivity|]. apply PV.
      + exact (art_priv_zone G LB FF LK A M (mrestrict H M) REP FS CLI LIVEOK KN (U x) Zx NB).
      + exact (art_zone_not_ctr G LB (mrestrict H M) REP LIVEOK KN (U x) Zx).
    - rewrite HCtp, HCloff. change (0x673d00 + 0x10) with 0x673d10.
      apply (art_cell_agree ASEGS M' (mrestrict H M')); [|clear; lia|cbn; clear; lia|exact CTR].
      intros x Hx. unfold mrestrict. destruct (H x) eqn:E; [|reflexivity]. exfalso. apply (HNC x E). cbn in Hx. clear - Hx. lia.
    - exact LIVEOK.
    - exact KN. }
  split.
  { apply (art_fsinv_client_proved rn (g_fs art_fsg G) FF LK M M' FS MONO).
    - intros x a Z NF. apply PV; [exact (art_priv_fs3 G LB FF LK A M (mrestrict H M) REP FS CLI LIVEOK KN a Z NF)|].
      pose proof REP as (ROK & _). rok_open ROK. geo_open GEO. destruct (art_fs_facts G LB (mrestrict H M) REP) as (F1 & F2 & F3 & F4).
      unfold fs_zone3, FS_BYTES in *. rewrite HCtp in Z. cbv zeta in Z. clear - Z F3 G9. unfold a in Z. lia.
    - intros x Z. apply PV; [exact (art_priv_cs G LB FF LK A M (mrestrict H M) REP FS CLI LIVEOK KN (U x) Z)|].
      pose proof REP as (ROK & _). rok_open ROK. geo_open GEO. unfold cs_zone in Z. rewrite HCtp in Z.
      assert (SB0 : forall y, 0 <= y -> 0x7fff8000 <= HeapIfaceA.S y) by (intros y Hy; unfold HeapIfaceA.S, HeapIfaceA.SB; pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)); lia).
      pose proof (SB0 0x10000 ltac:(lia)) as S1. clear - Z S1 D2. lia. }
  split.
  { destruct BV as (AW & LO & BF). split; [exact AW|]. split; [exact LO|]. intros model E1 E2 Hh Hm.
    apply (art_binv_mem _ _ _ _ _ _ _ _ _ M M' model (BF model E1 E2 Hh Hm)); [|exact MONO].
    intros x Hx. apply HIDEQ. unfold bhid in Hx. rewrite E2 in Hx. exact Hx. }
  split; [exact CRED|].
  split.
  { destruct CLI as (CB & CREST). split; [|exact CREST]. intros b Hb. destruct (CB b Hb) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & BREST).
    repeat (split; [assumption|]). split; [intros i Hi; apply MONO; exact (B7 i Hi)|]. split; [|exact BREST].
    assert (T : forall j v, 0 <= j -> (j < snd b / 8 \/ (j = snd b / 8 /\ snd b mod 8 <> 0)) -> byte_at M (HeapIfaceA.S (fst b) + j) v -> byte_at M' (HeapIfaceA.S (fst b) + j) v).
    { intros j v Hj0 Hj B. unfold byte_at in *.
      pose proof (art_S_blk_hi (fst b) (snd b) j B4 Hj) as H1.
      assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity. rewrite HIeq in B5. destruct (art_hi_bounds G LB (mrestrict H M) REP) as (_ & HI2).
      pose proof (art_S_range47 (fst b) ltac:(clear - B1 B4 B5 HI2; lia)) as H0.
      pose proof (art_S_range47 (fst b + snd b - 1) ltac:(clear - B1 B4 B5 HI2; lia)) as H2.
      rewrite PRIV; [exact B| clear - Hj0 H0 H1 H2; lia |right; right; exists b; split; [exact Hb|]|clear - Hj0 H0 H1 H2; lia].
      split; [clear - Hj0; lia|exact H1]. }
    apply (shadow_blkR_tby M M' (fst b) (snd b) B4); [intros j Hj0 Hj v Bv; exact (T j v Hj0 Hj Bv)|exact B8]. }
  split; [exact KN|]. split; [exact LZ|exact EG].
Qed.
End Frame.
