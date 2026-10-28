(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame BCells BStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_HKit LbB_Perm.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition set_scal (c d : stateC) : stateC :=
  {| st_words := st_words d; st_nwords := st_nwords d; st_diag := st_diag d; st_widx := st_widx d;
     st_icount := st_icount d; st_endian := st_endian d; st_flags := st_flags d;
     st_m1 := st_m1 c; st_m2 := st_m2 c; st_m3 := st_m3 c; st_v1 := st_v1 c; st_v2 := st_v2 c; st_v3 := st_v3 c |}.
Definition set_m1 (c : stateC) (t : Z * Z * list (Z * (Z * Z))) : stateC :=
  {| st_words := st_words c; st_nwords := st_nwords c; st_diag := st_diag c; st_widx := st_widx c;
     st_icount := st_icount c; st_endian := st_endian c; st_flags := st_flags c;
     st_m1 := t; st_m2 := st_m2 c; st_m3 := st_m3 c; st_v1 := st_v1 c; st_v2 := st_v2 c; st_v3 := st_v3 c |}.
Definition set_m2 (c : stateC) (t : Z * Z * list (Z * (Z * (Z * Z * Z)))) : stateC :=
  {| st_words := st_words c; st_nwords := st_nwords c; st_diag := st_diag c; st_widx := st_widx c;
     st_icount := st_icount c; st_endian := st_endian c; st_flags := st_flags c;
     st_m1 := st_m1 c; st_m2 := t; st_m3 := st_m3 c; st_v1 := st_v1 c; st_v2 := st_v2 c; st_v3 := st_v3 c |}.
Definition set_m3 (c : stateC) (t : Z * Z * list (Z * (Z * Z))) : stateC :=
  {| st_words := st_words c; st_nwords := st_nwords c; st_diag := st_diag c; st_widx := st_widx c;
     st_icount := st_icount c; st_endian := st_endian c; st_flags := st_flags c;
     st_m1 := st_m1 c; st_m2 := st_m2 c; st_m3 := t; st_v1 := st_v1 c; st_v2 := st_v2 c; st_v3 := st_v3 c |}.
Definition set_v1 (c : stateC) (t : Z * Z * Z) : stateC :=
  {| st_words := st_words c; st_nwords := st_nwords c; st_diag := st_diag c; st_widx := st_widx c;
     st_icount := st_icount c; st_endian := st_endian c; st_flags := st_flags c;
     st_m1 := st_m1 c; st_m2 := st_m2 c; st_m3 := st_m3 c; st_v1 := t; st_v2 := st_v2 c; st_v3 := st_v3 c |}.
Definition set_v2 (c : stateC) (t : Z * Z * Z) : stateC :=
  {| st_words := st_words c; st_nwords := st_nwords c; st_diag := st_diag c; st_widx := st_widx c;
     st_icount := st_icount c; st_endian := st_endian c; st_flags := st_flags c;
     st_m1 := st_m1 c; st_m2 := st_m2 c; st_m3 := st_m3 c; st_v1 := st_v1 c; st_v2 := t; st_v3 := st_v3 c |}.
Definition set_v3 (c : stateC) (t : Z * Z * Z) : stateC :=
  {| st_words := st_words c; st_nwords := st_nwords c; st_diag := st_diag c; st_widx := st_widx c;
     st_icount := st_icount c; st_endian := st_endian c; st_flags := st_flags c;
     st_m1 := st_m1 c; st_m2 := st_m2 c; st_m3 := st_m3 c; st_v1 := st_v1 c; st_v2 := st_v2 c; st_v3 := t |}.

Definition cb_m1 (c : stateC) : list (Z * Z) := umap_blocks 24 (t3a (st_m1 c)) (t3b (st_m1 c)) (t3c (st_m1 c)).
Definition cb_m2 (c : stateC) : list (Z * Z) := umap_blocks 32 (t3a (st_m2 c)) (t3b (st_m2 c)) (t3c (st_m2 c)).
Definition cb_m3 (c : stateC) : list (Z * Z) := umap_blocks 24 (t3a (st_m3 c)) (t3b (st_m3 c)) (t3c (st_m3 c)).
Definition cb_v1 (c : stateC) : list (Z * Z) := vec_blocks (st_v1 c).
Definition cb_v2 (c : stateC) : list (Z * Z) := vec_blocks (st_v2 c).
Definition cb_v3 (c : stateC) : list (Z * Z) := vec_blocks (st_v3 c).

Lemma state_blocks_cb : forall c, state_blocks c = cb_m1 c ++ cb_m2 c ++ cb_m3 c ++ cb_v1 c ++ cb_v2 c ++ cb_v3 c.
Proof. reflexivity. Qed.

Lemma rw_cells_of_cellw2 : forall M a v, cellw ASEGS M a 2 v -> AIMG_TOP <= a -> a + 2 <= 2 ^ 64 ->
  rw_cells asegs M a [C2 (Z_to_bv 64 v)].
Proof.
  intros M a v [Hv Hr] Ha Ha8. pose proof Ha as Ha0. unfold AIMG_TOP in Ha0.
  assert (BA : bytes_at asegs M a (word_to_le_bytes 2 (Z_to_bv 64 v))).
  { apply LbB_Conv.bytes_at_of_rdn; [lia | rewrite CatExec.length_N_to_le_bytes; lia | rewrite CatExec.length_N_to_le_bytes; exact Hr]. }
  split; [split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BA]|].
  pose proof (wr_at_of_bytes_hi M a _ BA Ha) as W. rewrite CatExec.length_N_to_le_bytes in W. exact W.
Qed.

Lemma cellw_copy : forall m m' a a' src k (w : N) v,
  bytes_at asegs m a src -> bytes_at asegs m' a' src -> cellw asegs m (a + k) w v -> 0 <= k ->
  k + Z.of_N w <= Z.of_nat (length src) -> cellw asegs m' (a' + k) w v.
Proof.
  intros m m' a a' src k w v BA BA' [Hv Hr] Hk Hkw. split; [exact Hv|].
  rewrite LbB_Conv.rdn_HL in Hr |- *.
  pose proof (bytes_at_rdn asegs m a src (Z.to_nat k) (N.to_nat w) BA ltac:(lia)) as R1.
  pose proof (bytes_at_rdn asegs m' a' src (Z.to_nat k) (N.to_nat w) BA' ltac:(lia)) as R2.
  rewrite Z2Nat.id in R1, R2 by lia. unfold wa in R1, R2. rewrite R1 in Hr. rewrite R2. exact Hr.
Qed.

Section Tr.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition OBJX (LBk : list block) (SP : Z) (X : list (Z * Z)) (st lo hi : Z) : Prop :=
    forall a, st <= a < st + 240 -> ~ (st + lo <= a < st + hi) -> xclient H LBk SP X a.

  Definition BLKX (LBk : list block) (SP : Z) (X : list (Z * Z)) (LBb : list block) (bs : list (Z * Z)) : Prop :=
    forall p n, In (p, n) bs -> (forall a, p <= a < p + n -> xclient H LBk SP X a) /\ In (p, n) (lbl LBb).

  Definition BLKSH (LBk : list block) (SP : Z) (X : list (Z * Z)) (bs : list (Z * Z)) : Prop :=
    forall p n, In (p, n) bs -> forall a, sh p <= a < sh p + nsh n -> xclient H LBk SP X a.

  Lemma BLKX_app : forall LBk SP X LBb l1 l2, BLKX LBk SP X LBb (l1 ++ l2) <-> BLKX LBk SP X LBb l1 /\ BLKX LBk SP X LBb l2.
  Proof.
    intros. unfold BLKX. split.
    - intros K. split; intros p n Hin; apply K; apply in_or_app; [left | right]; exact Hin.
    - intros [K1 K2] p n Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [apply K1 | apply K2]; exact Hin.
  Qed.
  Lemma BLKSH_app : forall LBk SP X l1 l2, BLKSH LBk SP X (l1 ++ l2) <-> BLKSH LBk SP X l1 /\ BLKSH LBk SP X l2.
  Proof.
    intros. unfold BLKSH. split.
    - intros K. split; intros p n Hin; apply K; apply in_or_app; [left | right]; exact Hin.
    - intros [K1 K2] p n Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin]; [apply K1 | apply K2]; exact Hin.
  Qed.

  Lemma agree_xp : forall LBk SP X m m' a n,
    xpres H LBk SP X m m' -> (forall i, 0 <= i < n -> xclient H LBk SP X (a + i)) -> 0 <= a -> a + n <= 2 ^ 64 ->
    agree_on m m' a n.
  Proof.
    intros LBk SP X m m' a n XP HC Ha Han i Hi. destruct (XP (a + i) ltac:(lia) (HC i Hi)) as [E _]. exact E.
  Qed.

  Lemma cellw_xp : forall LBk SP X m m' a (w : N) v,
    xpres H LBk SP X m m' -> cellw ASEGS m a w v -> (forall i, 0 <= i < Z.of_N w -> xclient H LBk SP X (a + i)) ->
    0 <= a < 2 ^ 64 -> a + Z.of_N w <= 2 ^ 64 -> cellw ASEGS m' a w v.
  Proof.
    intros LBk SP X m m' a w v XP C HC Ha Haw. eapply cellw_agree; [exact C | | exact Ha | exact Haw].
    eapply agree_xp; [exact XP | exact HC | lia | exact Haw].
  Qed.

  Lemma defined_xp : forall LBk SP X m m' a n,
    xpres H LBk SP X m m' -> defined m a n -> (forall i, 0 <= i < n -> xclient H LBk SP X (a + i)) ->
    0 <= a -> a + n <= 2 ^ 64 -> defined m' a n.
  Proof.
    intros LBk SP X m m' a n XP D HC Ha Han. eapply defined_agree; [exact D|]. eapply agree_xp; eassumption.
  Qed.

  Lemma umapx_xp : forall NS V (nval : mem -> Z -> V -> Prop) LBk SP X LBa LBb m m' o bl bc (ents : list (Z * (Z * V))),
    (forall M M' p v, nval M p v -> agree_on M M' (p + 20) (NS - 20) -> 0 < p -> p + NS <= 2 ^ 47 -> nval M' p v) ->
    24 <= NS ->
    xpres H LBk SP X m m' -> umapx MI_A NS nval (lbl LBa) m o bl bc ents ->
    (forall i, 0 <= i < 40 -> xclient H LBk SP X (o + i)) ->
    BLKX LBk SP X LBb (umap_blocks NS bl bc ents) ->
    umapx MI_A NS nval (lbl LBb) m' o bl bc ents.
  Proof.
    intros NS V nval LBk SP X LBa LBb m m' o bl bc ents NVA HNS XP U HO HB.
    pose proof (u_obj_lo U) as OL. pose proof (u_obj_hi U) as OH.
    pose proof (u_bl_hi U) as BH. pose proof (u_bl_lo U) as BLL.
    eapply (umapx_agree ASEGS LY_A MI_A NS V nval NVA HNS); [exact U | |].
    - intros a Ha. unfold umap_foot in Ha.
      destruct Ha as [Ha|[(Hbc & Ha)|(p & Hp & Ha)]].
      + destruct (XP a ltac:(lia) ltac:(replace a with (o + (a - o)) by lia; apply HO; lia)) as [E _].
        change (Z_to_bv 64 a) with (wa a). exact E.
      + assert (IB : In (bl, 8 * bc) (umap_blocks NS bl bc ents)).
        { unfold umap_blocks. destruct (Z.eqb_spec bc 0); [contradiction|]. apply in_or_app. left. left. reflexivity. }
        destruct (HB _ _ IB) as [K _]. specialize (BLL Hbc).
        destruct (XP a ltac:(lia) (K a Ha)) as [E _]. change (Z_to_bv 64 a) with (wa a). exact E.
      + apply in_map_iff in Hp. destruct Hp as [[p' [k v]] [Ep Hin]]. cbn in Ep. subst p'.
        assert (IB : In (p, NS) (umap_blocks NS bl bc ents)).
        { unfold umap_blocks. apply in_or_app. right. apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin]. }
        destruct (HB _ _ IB) as [K _].
        destruct (u_node U p k v Hin) as (_ & P0 & P1 & _).
        destruct (XP a ltac:(lia) (K a Ha)) as [E _]. change (Z_to_bv 64 a) with (wa a). exact E.
    - intros p n Hin _. exact (proj2 (HB p n Hin)).
  Qed.

  Lemma vraw_xp : forall LBk SP X LBa LBb m m' v b e c,
    xpres H LBk SP X m m' -> vraw MI_A (lbl LBa) m v b e c ->
    (forall i, 0 <= i < 24 -> xclient H LBk SP X (v + i)) -> 0 <= v -> v + 24 <= 2 ^ 64 ->
    BLKX LBk SP X LBb (vec_blocks (b, e, c)) ->
    vraw MI_A (lbl LBb) m' v b e c.
  Proof.
    intros LBk SP X LBa LBb m m' v b e c XP [Vb Ve Vc Vk] HC V0 V24 HB.
    constructor.
    - eapply cellw_xp; [exact XP | exact Vb | intros i Hi; apply HC; cbn in Hi; lia | lia | cbn; lia].
    - eapply cellw_xp; [exact XP | exact Ve | intros i Hi; replace (v + 8 + i) with (v + (8 + i)) by lia; apply HC; cbn in Hi; lia
                       | lia | cbn; lia].
    - eapply cellw_xp; [exact XP | exact Vc | intros i Hi; replace (v + 16 + i) with (v + (16 + i)) by lia; apply HC; cbn in Hi; lia
                       | lia | cbn; lia].
    - destruct Vk as [Z0|(Hb & Hin & Hr)]; [left; exact Z0 | right].
      split; [exact Hb|]. split; [|exact Hr].
      assert (IB : In (b, c - b) (vec_blocks (b, e, c))).
      { unfold vec_blocks, t3a, t3c. cbn [fst snd]. destruct (Z.eqb_spec b 0); [contradiction | left; reflexivity]. }
      exact (proj2 (HB _ _ IB)).
  Qed.

  Lemma SHAD_xp : forall LBk SP X m m' A sbs,
    xpres H LBk SP X m m' -> SHAD m A sbs ->
    (forall a, sh A <= a < sh A + Z.of_nat (length sbs) -> xclient H LBk SP X a) -> SHAD m' A sbs.
  Proof.
    intros LBk SP X m m' A sbs XP (A0 & A8 & [UB UW]) HC. split; [exact A0|]. split; [exact A8|]. split.
    - destruct UB as (B0 & B1 & B). split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (B i Hi). unfold mrd.
      destruct (XP (sh A + Z.of_nat i) ltac:(lia) (HC (sh A + Z.of_nat i) ltac:(lia))) as [E _]. rewrite E. reflexivity.
    - destruct UW as (W0 & W1 & W). split; [exact W0|]. split; [exact W1|]. intros i Hi.
      destruct (XP (sh A + i) ltac:(lia) (HC (sh A + i) ltac:(lia))) as [_ WW]. apply WW. apply W. exact Hi.
  Qed.

  Lemma addressable_xp : forall LBk SP X m m' A n,
    xpres H LBk SP X m m' -> addressable m A n ->
    (forall a, sh A <= a < sh A + nsh n -> xclient H LBk SP X a) -> addressable m' A n.
  Proof.
    intros LBk SP X m m' A n XP [Hn S] HC. split; [exact Hn|]. eapply SHAD_xp; [exact XP | exact S |].
    rewrite shadow_of_length by lia. exact HC.
  Qed.

  Lemma umap_sh_xp : forall V NS LBk SP X m m' (t : Z * Z * list (Z * (Z * V))),
    xpres H LBk SP X m m' -> umap_sh m NS t -> BLKSH LBk SP X (umap_blocks NS (t3a t) (t3b t) (t3c t)) -> umap_sh m' NS t.
  Proof.
    intros V NS LBk SP X m m' [[bl bc] ents] XP [S1 S2] HB. unfold t3a, t3b, t3c in *. cbn [fst snd] in *. split.
    - intros Hbc. eapply addressable_xp; [exact XP | exact (S1 Hbc) |]. apply HB.
      unfold umap_blocks. destruct (Z.eqb_spec bc 0); [contradiction|]. apply in_or_app. left. left. reflexivity.
    - intros p k v Hin. eapply addressable_xp; [exact XP | exact (S2 p k v Hin) |]. apply HB.
      unfold umap_blocks. apply in_or_app. right. apply in_map_iff. exists (p, (k, v)). split; [reflexivity | exact Hin].
  Qed.

  Lemma vec_sh_xp : forall LBk SP X m m' (v : Z * Z * Z),
    xpres H LBk SP X m m' -> vec_sh m v -> t3a v <= t3b v <= t3c v -> BLKSH LBk SP X (vec_blocks v) -> vec_sh m' v.
  Proof.
    intros LBk SP X m m' [[b e] c] XP S R HB. unfold vec_sh, vec_blocks, t3a, t3b, t3c in *. cbn [fst snd] in *.
    intros Hb. eapply SHAD_xp; [exact XP | exact (S Hb) |].
    unfold cc_gen, poison_bytes. rewrite length_app, repeat_length, Nat2Z.inj_add, shadow_of_length by lia.
    assert (NM : nsh (e - b) <= nsh (c - b)) by (unfold nsh; apply Z.div_le_mono; lia).
    intros a Ha. apply (HB b (c - b)); [destruct (Z.eqb_spec b 0); [contradiction | left; reflexivity]|]. lia.
  Qed.

  Lemma objx_at0 : forall LBk SP X st lo hi, OBJX LBk SP X st lo hi ->
    forall n, n <= lo -> lo <= 240 -> forall i, 0 <= i < n -> xclient H LBk SP X (st + i).
  Proof. intros LBk SP X st lo hi OX n H1 H2 i Hi. apply OX; lia. Qed.
  Lemma objx_at : forall LBk SP X st lo hi, OBJX LBk SP X st lo hi ->
    forall off n, 0 <= off -> off + n <= 240 -> (off + n <= lo \/ hi <= off) ->
    forall i, 0 <= i < n -> xclient H LBk SP X (st + off + i).
  Proof. intros LBk SP X st lo hi OX off n H1 H2 H3 i Hi. apply OX; lia. Qed.
  Lemma BLKX_split5 : forall LBk SP X LBb l1 l2 l3 l4 l5, BLKX LBk SP X LBb (l1 ++ l2 ++ l3 ++ l4 ++ l5) ->
    BLKX LBk SP X LBb l1 /\ BLKX LBk SP X LBb l2 /\ BLKX LBk SP X LBb l3 /\ BLKX LBk SP X LBb l4 /\ BLKX LBk SP X LBb l5.
  Proof.
    intros LBk SP X LBb l1 l2 l3 l4 l5 K.
    apply BLKX_app in K as [K1 K]. apply BLKX_app in K as [K2 K]. apply BLKX_app in K as [K3 K]. apply BLKX_app in K as [K4 K5].
    tauto.
  Qed.
  Lemma BLKSH_split5 : forall LBk SP X l1 l2 l3 l4 l5, BLKSH LBk SP X (l1 ++ l2 ++ l3 ++ l4 ++ l5) ->
    BLKSH LBk SP X l1 /\ BLKSH LBk SP X l2 /\ BLKSH LBk SP X l3 /\ BLKSH LBk SP X l4 /\ BLKSH LBk SP X l5.
  Proof.
    intros LBk SP X l1 l2 l3 l4 l5 K.
    apply BLKSH_app in K as [K1 K]. apply BLKSH_app in K as [K2 K]. apply BLKSH_app in K as [K3 K]. apply BLKSH_app in K as [K4 K5].
    tauto.
  Qed.

Lemma defined_of_cellw8_hi : forall M a v, cellw ASEGS M a 8 v -> AIMG_TOP <= a -> a + 8 <= 2 ^ 64 -> defined M a 8.
Proof.
  intros M a v C Ha Ha8. pose proof (rw_cells_of_cellw8 M a v C Ha Ha8) as R.
  exact (defined_of_rw_cells_hi M a _ R Ha).
Qed.
Lemma vraw_defined : forall A m v b e c, vraw MI_A A m v b e c -> AIMG_TOP <= v -> v + 24 <= 2 ^ 64 -> defined m v 24.
Proof.
  intros A m v b e c [Vb Ve Vc _] H1 H2.
  pose proof (defined_of_cellw8_hi _ _ _ Vb ltac:(lia) ltac:(lia)) as D0.
  pose proof (defined_of_cellw8_hi _ _ _ Ve ltac:(lia) ltac:(lia)) as D1.
  pose proof (defined_of_cellw8_hi _ _ _ Vc ltac:(lia) ltac:(lia)) as D2.
  intros i Hi.
  destruct (Z_lt_le_dec i 8); [apply D0; lia|]. destruct (Z_lt_le_dec i 16).
  - replace (v + i) with (v + 8 + (i - 8)) by lia. apply D1. lia.
  - replace (v + i) with (v + 16 + (i - 16)) by lia. apply D2. lia.
Qed.
Lemma vord_of_vraw : forall A m v b e c, vraw MI_A A m v b e c -> b <= e <= c.
Proof. intros A m v b e c [_ _ _ [K|(_ & _ & K)]]; lia. Qed.
Lemma vord_of_rep : forall LB m st c, state_repA LB m st c ->
  (t3a (st_v1 c) <= t3b (st_v1 c) <= t3c (st_v1 c)) /\ (t3a (st_v2 c) <= t3b (st_v2 c) <= t3c (st_v2 c))
  /\ (t3a (st_v3 c) <= t3b (st_v3 c) <= t3c (st_v3 c)).
Proof.
  intros LB m st c R. unfold state_repA in R. destruct R as [R _].
  split; [exact (vord_of_vraw _ _ _ _ _ _ (sr_v1 _ _ _ _ _ _ _ R))|].
  split; [exact (vord_of_vraw _ _ _ _ _ _ (sr_v2 _ _ _ _ _ _ _ R)) | exact (vord_of_vraw _ _ _ _ _ _ (sr_v3 _ _ _ _ _ _ _ R))].
Qed.

  Lemma rep_upd_m1 : forall LBa LBb LBk SP X m m' st c (t : Z * Z * list (Z * (Z * Z))),
    state_repA LBa m st c -> xpres H LBk SP X m m' -> OBJX LBk SP X st 48 88 ->
    BLKX LBk SP X LBb (cb_m2 c ++ cb_m3 c ++ cb_v1 c ++ cb_v2 c ++ cb_v3 c) ->
    umapx MI_A 24 (nval24 ASEGS) (lbl LBb) m' (st + 48) (t3a t) (t3b t) (t3c t) ->
    NoDup (map fst (state_blocks (set_m1 c t))) -> AIMG_TOP <= st -> st + 240 <= 2 ^ 47 ->
    state_repA LBb m' st (set_m1 c t).
  Proof.
    intros LBa LBb LBk SP X m m' st c t R XP OX BK NEW NDP STL STH.
    pose proof STL as STL'. unfold AIMG_TOP in STL'.
    unfold state_repA in R |- *. destruct R as [R RV]. split; [|exact RV].
    destruct R as [R_w0 R_w1 R_w2 R_w3 R_w4 R_w5 R_w6 R_m1 R_m2 R_m3 R_v1 R_v2 R_v3 R_def R_al R_nd].
    pose proof (HRep.h_def (u_hdr NEW)) as ND.
    pose proof (BLKX_split5 _ _ _ _ _ _ _ _ _ BK) as (BK_m2 & BK_m3 & BK_v1 & BK_v2 & BK_v3).
    constructor; cbn [set_m1 st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
    - eapply cellw_xp; [exact XP | exact R_w0 | exact (objx_at0 _ _ _ _ _ _ OX 8 ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w1 | exact (objx_at _ _ _ _ _ _ OX 8 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w2 | exact (objx_at _ _ _ _ _ _ OX 16 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w3 | exact (objx_at _ _ _ _ _ _ OX 24 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w4 | exact (objx_at _ _ _ _ _ _ OX 32 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w5 | exact (objx_at _ _ _ _ _ _ OX 40 4 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | cbn; lia].
    - eapply cellw_xp; [exact XP | exact R_w6 | exact (objx_at _ _ _ _ _ _ OX 44 2 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | cbn; lia].
    - exact NEW.
    - eapply (umapx_xp 32 (Z * Z * Z) (nval32 ASEGS) LBk SP X LBa LBb m m' (st + 88)); [exact (nval32_agree ASEGS) | lia | exact XP | exact R_m2 | exact (objx_at _ _ _ _ _ _ OX 88 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m2) ].
    - eapply (umapx_xp 24 Z (nval24 ASEGS) LBk SP X LBa LBb m m' (st + 128)); [exact (nval24_agree ASEGS) | lia | exact XP | exact R_m3 | exact (objx_at _ _ _ _ _ _ OX 128 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m3) ].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 168)); [exact XP | exact R_v1 | exact (objx_at _ _ _ _ _ _ OX 168 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v1) ].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 192)); [exact XP | exact R_v2 | exact (objx_at _ _ _ _ _ _ OX 192 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v2) ].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 216)); [exact XP | exact R_v3 | exact (objx_at _ _ _ _ _ _ OX 216 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v3) ].
    - intros i Hi. destruct (Z_lt_le_dec i 48) as [Li|Li]; [|destruct (Z_lt_le_dec i 88) as [Ui|Ui]].
      + assert (D1 : defined m' (st + i) 1).
        { eapply (defined_xp LBk SP X m m' (st + i) 1); [exact XP | | | lia | lia].
          * intros k Hk. replace (st + i + k) with (st + (i + k)) by lia. apply R_def. lia.
          * intros k Hk. apply OX; lia. }
        specialize (D1 0 ltac:(lia)). rewrite Z.add_0_r in D1. exact D1.
      + replace (st + i) with (st + 48 + (i - 48)) by lia. apply ND. lia.
      + assert (D1 : defined m' (st + i) 1).
        { eapply (defined_xp LBk SP X m m' (st + i) 1); [exact XP | | | lia | lia].
          * intros k Hk. replace (st + i + k) with (st + (i + k)) by lia. apply R_def. lia.
          * intros k Hk. apply OX; lia. }
        specialize (D1 0 ltac:(lia)). rewrite Z.add_0_r in D1. exact D1.
    - exact R_al.
    - exact NDP.
  Qed.

  Lemma rep_upd_m2 : forall LBa LBb LBk SP X m m' st c (t : Z * Z * list (Z * (Z * (Z * Z * Z)))),
    state_repA LBa m st c -> xpres H LBk SP X m m' -> OBJX LBk SP X st 88 128 ->
    BLKX LBk SP X LBb (cb_m1 c ++ cb_m3 c ++ cb_v1 c ++ cb_v2 c ++ cb_v3 c) ->
    umapx MI_A 32 (nval32 ASEGS) (lbl LBb) m' (st + 88) (t3a t) (t3b t) (t3c t) ->
    NoDup (map fst (state_blocks (set_m2 c t))) -> AIMG_TOP <= st -> st + 240 <= 2 ^ 47 ->
    state_repA LBb m' st (set_m2 c t).
  Proof.
    intros LBa LBb LBk SP X m m' st c t R XP OX BK NEW NDP STL STH.
    pose proof STL as STL'. unfold AIMG_TOP in STL'.
    unfold state_repA in R |- *. destruct R as [R RV]. split; [|exact RV].
    destruct R as [R_w0 R_w1 R_w2 R_w3 R_w4 R_w5 R_w6 R_m1 R_m2 R_m3 R_v1 R_v2 R_v3 R_def R_al R_nd].
    pose proof (HRep.h_def (u_hdr NEW)) as ND.
    pose proof (BLKX_split5 _ _ _ _ _ _ _ _ _ BK) as (BK_m1 & BK_m3 & BK_v1 & BK_v2 & BK_v3).
    constructor; cbn [set_m2 st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
    - eapply cellw_xp; [exact XP | exact R_w0 | exact (objx_at0 _ _ _ _ _ _ OX 8 ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w1 | exact (objx_at _ _ _ _ _ _ OX 8 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w2 | exact (objx_at _ _ _ _ _ _ OX 16 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w3 | exact (objx_at _ _ _ _ _ _ OX 24 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w4 | exact (objx_at _ _ _ _ _ _ OX 32 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w5 | exact (objx_at _ _ _ _ _ _ OX 40 4 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | cbn; lia].
    - eapply cellw_xp; [exact XP | exact R_w6 | exact (objx_at _ _ _ _ _ _ OX 44 2 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | cbn; lia].
    - eapply (umapx_xp 24 Z (nval24 ASEGS) LBk SP X LBa LBb m m' (st + 48)); [exact (nval24_agree ASEGS) | lia | exact XP | exact R_m1 | exact (objx_at _ _ _ _ _ _ OX 48 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m1) ].
    - exact NEW.
    - eapply (umapx_xp 24 Z (nval24 ASEGS) LBk SP X LBa LBb m m' (st + 128)); [exact (nval24_agree ASEGS) | lia | exact XP | exact R_m3 | exact (objx_at _ _ _ _ _ _ OX 128 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m3) ].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 168)); [exact XP | exact R_v1 | exact (objx_at _ _ _ _ _ _ OX 168 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v1) ].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 192)); [exact XP | exact R_v2 | exact (objx_at _ _ _ _ _ _ OX 192 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v2) ].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 216)); [exact XP | exact R_v3 | exact (objx_at _ _ _ _ _ _ OX 216 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v3) ].
    - intros i Hi. destruct (Z_lt_le_dec i 88) as [Li|Li]; [|destruct (Z_lt_le_dec i 128) as [Ui|Ui]].
      + assert (D1 : defined m' (st + i) 1).
        { eapply (defined_xp LBk SP X m m' (st + i) 1); [exact XP | | | lia | lia].
          * intros k Hk. replace (st + i + k) with (st + (i + k)) by lia. apply R_def. lia.
          * intros k Hk. apply OX; lia. }
        specialize (D1 0 ltac:(lia)). rewrite Z.add_0_r in D1. exact D1.
      + replace (st + i) with (st + 88 + (i - 88)) by lia. apply ND. lia.
      + assert (D1 : defined m' (st + i) 1).
        { eapply (defined_xp LBk SP X m m' (st + i) 1); [exact XP | | | lia | lia].
          * intros k Hk. replace (st + i + k) with (st + (i + k)) by lia. apply R_def. lia.
          * intros k Hk. apply OX; lia. }
        specialize (D1 0 ltac:(lia)). rewrite Z.add_0_r in D1. exact D1.
    - exact R_al.
    - exact NDP.
  Qed.

  Lemma rep_upd_m3 : forall LBa LBb LBk SP X m m' st c (t : Z * Z * list (Z * (Z * Z))),
    state_repA LBa m st c -> xpres H LBk SP X m m' -> OBJX LBk SP X st 128 168 ->
    BLKX LBk SP X LBb (cb_m1 c ++ cb_m2 c ++ cb_v1 c ++ cb_v2 c ++ cb_v3 c) ->
    umapx MI_A 24 (nval24 ASEGS) (lbl LBb) m' (st + 128) (t3a t) (t3b t) (t3c t) ->
    NoDup (map fst (state_blocks (set_m3 c t))) -> AIMG_TOP <= st -> st + 240 <= 2 ^ 47 ->
    state_repA LBb m' st (set_m3 c t).
  Proof.
    intros LBa LBb LBk SP X m m' st c t R XP OX BK NEW NDP STL STH.
    pose proof STL as STL'. unfold AIMG_TOP in STL'.
    unfold state_repA in R |- *. destruct R as [R RV]. split; [|exact RV].
    destruct R as [R_w0 R_w1 R_w2 R_w3 R_w4 R_w5 R_w6 R_m1 R_m2 R_m3 R_v1 R_v2 R_v3 R_def R_al R_nd].
    pose proof (HRep.h_def (u_hdr NEW)) as ND.
    pose proof (BLKX_split5 _ _ _ _ _ _ _ _ _ BK) as (BK_m1 & BK_m2 & BK_v1 & BK_v2 & BK_v3).
    constructor; cbn [set_m3 st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
    - eapply cellw_xp; [exact XP | exact R_w0 | exact (objx_at0 _ _ _ _ _ _ OX 8 ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w1 | exact (objx_at _ _ _ _ _ _ OX 8 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w2 | exact (objx_at _ _ _ _ _ _ OX 16 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w3 | exact (objx_at _ _ _ _ _ _ OX 24 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w4 | exact (objx_at _ _ _ _ _ _ OX 32 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w5 | exact (objx_at _ _ _ _ _ _ OX 40 4 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | cbn; lia].
    - eapply cellw_xp; [exact XP | exact R_w6 | exact (objx_at _ _ _ _ _ _ OX 44 2 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | cbn; lia].
    - eapply (umapx_xp 24 Z (nval24 ASEGS) LBk SP X LBa LBb m m' (st + 48)); [exact (nval24_agree ASEGS) | lia | exact XP | exact R_m1 | exact (objx_at _ _ _ _ _ _ OX 48 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m1) ].
    - eapply (umapx_xp 32 (Z * Z * Z) (nval32 ASEGS) LBk SP X LBa LBb m m' (st + 88)); [exact (nval32_agree ASEGS) | lia | exact XP | exact R_m2 | exact (objx_at _ _ _ _ _ _ OX 88 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m2) ].
    - exact NEW.
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 168)); [exact XP | exact R_v1 | exact (objx_at _ _ _ _ _ _ OX 168 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v1) ].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 192)); [exact XP | exact R_v2 | exact (objx_at _ _ _ _ _ _ OX 192 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v2) ].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 216)); [exact XP | exact R_v3 | exact (objx_at _ _ _ _ _ _ OX 216 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v3) ].
    - intros i Hi. destruct (Z_lt_le_dec i 128) as [Li|Li]; [|destruct (Z_lt_le_dec i 168) as [Ui|Ui]].
      + assert (D1 : defined m' (st + i) 1).
        { eapply (defined_xp LBk SP X m m' (st + i) 1); [exact XP | | | lia | lia].
          * intros k Hk. replace (st + i + k) with (st + (i + k)) by lia. apply R_def. lia.
          * intros k Hk. apply OX; lia. }
        specialize (D1 0 ltac:(lia)). rewrite Z.add_0_r in D1. exact D1.
      + replace (st + i) with (st + 128 + (i - 128)) by lia. apply ND. lia.
      + assert (D1 : defined m' (st + i) 1).
        { eapply (defined_xp LBk SP X m m' (st + i) 1); [exact XP | | | lia | lia].
          * intros k Hk. replace (st + i + k) with (st + (i + k)) by lia. apply R_def. lia.
          * intros k Hk. apply OX; lia. }
        specialize (D1 0 ltac:(lia)). rewrite Z.add_0_r in D1. exact D1.
    - exact R_al.
    - exact NDP.
  Qed.

  Lemma rep_upd_v1 : forall LBa LBb LBk SP X m m' st c (t : Z * Z * Z),
    state_repA LBa m st c -> xpres H LBk SP X m m' -> OBJX LBk SP X st 168 192 ->
    BLKX LBk SP X LBb (cb_m1 c ++ cb_m2 c ++ cb_m3 c ++ cb_v2 c ++ cb_v3 c) ->
    vraw MI_A (lbl LBb) m' (st + 168) (t3a t) (t3b t) (t3c t) ->
    NoDup (map fst (state_blocks (set_v1 c t))) -> AIMG_TOP <= st -> st + 240 <= 2 ^ 47 ->
    (t3a t <> 0 -> (t3b t - t3a t) mod 20 = 0) ->
    state_repA LBb m' st (set_v1 c t).
  Proof.
    intros LBa LBb LBk SP X m m' st c t R XP OX BK NEW NDP STL STH VS.
    pose proof STL as STL'. unfold AIMG_TOP in STL'.
    unfold state_repA in R |- *. destruct R as [R RV]. destruct RV as (RV1 & RV2 & RV3). split; [|exact (conj VS (conj RV2 RV3))].
    destruct R as [R_w0 R_w1 R_w2 R_w3 R_w4 R_w5 R_w6 R_m1 R_m2 R_m3 R_v1 R_v2 R_v3 R_def R_al R_nd].
    assert (ND : defined m' (st + 168) 24) by (apply (vraw_defined _ _ _ _ _ _ NEW); unfold AIMG_TOP in *; lia).
    pose proof (BLKX_split5 _ _ _ _ _ _ _ _ _ BK) as (BK_m1 & BK_m2 & BK_m3 & BK_v2 & BK_v3).
    constructor; cbn [set_v1 st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
    - eapply cellw_xp; [exact XP | exact R_w0 | exact (objx_at0 _ _ _ _ _ _ OX 8 ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w1 | exact (objx_at _ _ _ _ _ _ OX 8 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w2 | exact (objx_at _ _ _ _ _ _ OX 16 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w3 | exact (objx_at _ _ _ _ _ _ OX 24 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w4 | exact (objx_at _ _ _ _ _ _ OX 32 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w5 | exact (objx_at _ _ _ _ _ _ OX 40 4 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | cbn; lia].
    - eapply cellw_xp; [exact XP | exact R_w6 | exact (objx_at _ _ _ _ _ _ OX 44 2 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | cbn; lia].
    - eapply (umapx_xp 24 Z (nval24 ASEGS) LBk SP X LBa LBb m m' (st + 48)); [exact (nval24_agree ASEGS) | lia | exact XP | exact R_m1 | exact (objx_at _ _ _ _ _ _ OX 48 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m1) ].
    - eapply (umapx_xp 32 (Z * Z * Z) (nval32 ASEGS) LBk SP X LBa LBb m m' (st + 88)); [exact (nval32_agree ASEGS) | lia | exact XP | exact R_m2 | exact (objx_at _ _ _ _ _ _ OX 88 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m2) ].
    - eapply (umapx_xp 24 Z (nval24 ASEGS) LBk SP X LBa LBb m m' (st + 128)); [exact (nval24_agree ASEGS) | lia | exact XP | exact R_m3 | exact (objx_at _ _ _ _ _ _ OX 128 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m3) ].
    - exact NEW.
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 192)); [exact XP | exact R_v2 | exact (objx_at _ _ _ _ _ _ OX 192 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v2) ].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 216)); [exact XP | exact R_v3 | exact (objx_at _ _ _ _ _ _ OX 216 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v3) ].
    - intros i Hi. destruct (Z_lt_le_dec i 168) as [Li|Li]; [|destruct (Z_lt_le_dec i 192) as [Ui|Ui]].
      + assert (D1 : defined m' (st + i) 1).
        { eapply (defined_xp LBk SP X m m' (st + i) 1); [exact XP | | | lia | lia].
          * intros k Hk. replace (st + i + k) with (st + (i + k)) by lia. apply R_def. lia.
          * intros k Hk. apply OX; lia. }
        specialize (D1 0 ltac:(lia)). rewrite Z.add_0_r in D1. exact D1.
      + replace (st + i) with (st + 168 + (i - 168)) by lia. apply ND. lia.
      + assert (D1 : defined m' (st + i) 1).
        { eapply (defined_xp LBk SP X m m' (st + i) 1); [exact XP | | | lia | lia].
          * intros k Hk. replace (st + i + k) with (st + (i + k)) by lia. apply R_def. lia.
          * intros k Hk. apply OX; lia. }
        specialize (D1 0 ltac:(lia)). rewrite Z.add_0_r in D1. exact D1.
    - exact R_al.
    - exact NDP.
  Qed.

  Lemma rep_upd_v2 : forall LBa LBb LBk SP X m m' st c (t : Z * Z * Z),
    state_repA LBa m st c -> xpres H LBk SP X m m' -> OBJX LBk SP X st 192 216 ->
    BLKX LBk SP X LBb (cb_m1 c ++ cb_m2 c ++ cb_m3 c ++ cb_v1 c ++ cb_v3 c) ->
    vraw MI_A (lbl LBb) m' (st + 192) (t3a t) (t3b t) (t3c t) ->
    NoDup (map fst (state_blocks (set_v2 c t))) -> AIMG_TOP <= st -> st + 240 <= 2 ^ 47 ->
    (t3a t <> 0 -> (t3b t - t3a t) mod 4 = 0) ->
    state_repA LBb m' st (set_v2 c t).
  Proof.
    intros LBa LBb LBk SP X m m' st c t R XP OX BK NEW NDP STL STH VS.
    pose proof STL as STL'. unfold AIMG_TOP in STL'.
    unfold state_repA in R |- *. destruct R as [R RV]. destruct RV as (RV1 & RV2 & RV3). split; [|exact (conj RV1 (conj VS RV3))].
    destruct R as [R_w0 R_w1 R_w2 R_w3 R_w4 R_w5 R_w6 R_m1 R_m2 R_m3 R_v1 R_v2 R_v3 R_def R_al R_nd].
    assert (ND : defined m' (st + 192) 24) by (apply (vraw_defined _ _ _ _ _ _ NEW); unfold AIMG_TOP in *; lia).
    pose proof (BLKX_split5 _ _ _ _ _ _ _ _ _ BK) as (BK_m1 & BK_m2 & BK_m3 & BK_v1 & BK_v3).
    constructor; cbn [set_v2 st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
    - eapply cellw_xp; [exact XP | exact R_w0 | exact (objx_at0 _ _ _ _ _ _ OX 8 ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w1 | exact (objx_at _ _ _ _ _ _ OX 8 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w2 | exact (objx_at _ _ _ _ _ _ OX 16 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w3 | exact (objx_at _ _ _ _ _ _ OX 24 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w4 | exact (objx_at _ _ _ _ _ _ OX 32 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w5 | exact (objx_at _ _ _ _ _ _ OX 40 4 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | cbn; lia].
    - eapply cellw_xp; [exact XP | exact R_w6 | exact (objx_at _ _ _ _ _ _ OX 44 2 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | cbn; lia].
    - eapply (umapx_xp 24 Z (nval24 ASEGS) LBk SP X LBa LBb m m' (st + 48)); [exact (nval24_agree ASEGS) | lia | exact XP | exact R_m1 | exact (objx_at _ _ _ _ _ _ OX 48 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m1) ].
    - eapply (umapx_xp 32 (Z * Z * Z) (nval32 ASEGS) LBk SP X LBa LBb m m' (st + 88)); [exact (nval32_agree ASEGS) | lia | exact XP | exact R_m2 | exact (objx_at _ _ _ _ _ _ OX 88 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m2) ].
    - eapply (umapx_xp 24 Z (nval24 ASEGS) LBk SP X LBa LBb m m' (st + 128)); [exact (nval24_agree ASEGS) | lia | exact XP | exact R_m3 | exact (objx_at _ _ _ _ _ _ OX 128 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m3) ].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 168)); [exact XP | exact R_v1 | exact (objx_at _ _ _ _ _ _ OX 168 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v1) ].
    - exact NEW.
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 216)); [exact XP | exact R_v3 | exact (objx_at _ _ _ _ _ _ OX 216 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v3) ].
    - intros i Hi. destruct (Z_lt_le_dec i 192) as [Li|Li]; [|destruct (Z_lt_le_dec i 216) as [Ui|Ui]].
      + assert (D1 : defined m' (st + i) 1).
        { eapply (defined_xp LBk SP X m m' (st + i) 1); [exact XP | | | lia | lia].
          * intros k Hk. replace (st + i + k) with (st + (i + k)) by lia. apply R_def. lia.
          * intros k Hk. apply OX; lia. }
        specialize (D1 0 ltac:(lia)). rewrite Z.add_0_r in D1. exact D1.
      + replace (st + i) with (st + 192 + (i - 192)) by lia. apply ND. lia.
      + assert (D1 : defined m' (st + i) 1).
        { eapply (defined_xp LBk SP X m m' (st + i) 1); [exact XP | | | lia | lia].
          * intros k Hk. replace (st + i + k) with (st + (i + k)) by lia. apply R_def. lia.
          * intros k Hk. apply OX; lia. }
        specialize (D1 0 ltac:(lia)). rewrite Z.add_0_r in D1. exact D1.
    - exact R_al.
    - exact NDP.
  Qed.

  Lemma rep_upd_v3 : forall LBa LBb LBk SP X m m' st c (t : Z * Z * Z),
    state_repA LBa m st c -> xpres H LBk SP X m m' -> OBJX LBk SP X st 216 240 ->
    BLKX LBk SP X LBb (cb_m1 c ++ cb_m2 c ++ cb_m3 c ++ cb_v1 c ++ cb_v2 c) ->
    vraw MI_A (lbl LBb) m' (st + 216) (t3a t) (t3b t) (t3c t) ->
    NoDup (map fst (state_blocks (set_v3 c t))) -> AIMG_TOP <= st -> st + 240 <= 2 ^ 47 ->
    (t3a t <> 0 -> (t3b t - t3a t) mod 4 = 0) ->
    state_repA LBb m' st (set_v3 c t).
  Proof.
    intros LBa LBb LBk SP X m m' st c t R XP OX BK NEW NDP STL STH VS.
    pose proof STL as STL'. unfold AIMG_TOP in STL'.
    unfold state_repA in R |- *. destruct R as [R RV]. destruct RV as (RV1 & RV2 & RV3). split; [|exact (conj RV1 (conj RV2 VS))].
    destruct R as [R_w0 R_w1 R_w2 R_w3 R_w4 R_w5 R_w6 R_m1 R_m2 R_m3 R_v1 R_v2 R_v3 R_def R_al R_nd].
    assert (ND : defined m' (st + 216) 24) by (apply (vraw_defined _ _ _ _ _ _ NEW); unfold AIMG_TOP in *; lia).
    pose proof (BLKX_split5 _ _ _ _ _ _ _ _ _ BK) as (BK_m1 & BK_m2 & BK_m3 & BK_v1 & BK_v2).
    constructor; cbn [set_v3 st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
    - eapply cellw_xp; [exact XP | exact R_w0 | exact (objx_at0 _ _ _ _ _ _ OX 8 ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w1 | exact (objx_at _ _ _ _ _ _ OX 8 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w2 | exact (objx_at _ _ _ _ _ _ OX 16 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w3 | exact (objx_at _ _ _ _ _ _ OX 24 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w4 | exact (objx_at _ _ _ _ _ _ OX 32 8 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | lia].
    - eapply cellw_xp; [exact XP | exact R_w5 | exact (objx_at _ _ _ _ _ _ OX 40 4 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | cbn; lia].
    - eapply cellw_xp; [exact XP | exact R_w6 | exact (objx_at _ _ _ _ _ _ OX 44 2 ltac:(lia) ltac:(lia) ltac:(lia)) | unfold AIMG_TOP in STL; lia | cbn; lia].
    - eapply (umapx_xp 24 Z (nval24 ASEGS) LBk SP X LBa LBb m m' (st + 48)); [exact (nval24_agree ASEGS) | lia | exact XP | exact R_m1 | exact (objx_at _ _ _ _ _ _ OX 48 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m1) ].
    - eapply (umapx_xp 32 (Z * Z * Z) (nval32 ASEGS) LBk SP X LBa LBb m m' (st + 88)); [exact (nval32_agree ASEGS) | lia | exact XP | exact R_m2 | exact (objx_at _ _ _ _ _ _ OX 88 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m2) ].
    - eapply (umapx_xp 24 Z (nval24 ASEGS) LBk SP X LBa LBb m m' (st + 128)); [exact (nval24_agree ASEGS) | lia | exact XP | exact R_m3 | exact (objx_at _ _ _ _ _ _ OX 128 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact (BK_m3) ].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 168)); [exact XP | exact R_v1 | exact (objx_at _ _ _ _ _ _ OX 168 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v1) ].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 192)); [exact XP | exact R_v2 | exact (objx_at _ _ _ _ _ _ OX 192 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact (BK_v2) ].
    - exact NEW.
    - intros i Hi. destruct (Z_lt_le_dec i 216) as [Li|Li]; [|destruct (Z_lt_le_dec i 240) as [Ui|Ui]].
      + assert (D1 : defined m' (st + i) 1).
        { eapply (defined_xp LBk SP X m m' (st + i) 1); [exact XP | | | lia | lia].
          * intros k Hk. replace (st + i + k) with (st + (i + k)) by lia. apply R_def. lia.
          * intros k Hk. apply OX; lia. }
        specialize (D1 0 ltac:(lia)). rewrite Z.add_0_r in D1. exact D1.
      + replace (st + i) with (st + 216 + (i - 216)) by lia. apply ND. lia.
      + assert (D1 : defined m' (st + i) 1).
        { eapply (defined_xp LBk SP X m m' (st + i) 1); [exact XP | | | lia | lia].
          * intros k Hk. replace (st + i + k) with (st + (i + k)) by lia. apply R_def. lia.
          * intros k Hk. apply OX; lia. }
        specialize (D1 0 ltac:(lia)). rewrite Z.add_0_r in D1. exact D1.
    - exact R_al.
    - exact NDP.
  Qed.

  Lemma sh_upd_m1 : forall LBa LBk SP X m m' st c (t : Z * Z * list (Z * (Z * Z))),
    state_repA LBa m st c -> state_sh m c -> xpres H LBk SP X m m' ->
    BLKSH LBk SP X (cb_m2 c ++ cb_m3 c ++ cb_v1 c ++ cb_v2 c ++ cb_v3 c) -> umap_sh m' 24 t ->
    state_sh m' (set_m1 c t).
  Proof.
    intros LBa LBk SP X m m' st c t R S XP BS NEW.
    pose proof (vord_of_rep _ _ _ _ R) as (O_v1 & O_v2 & O_v3).
    destruct S as (S_m1 & S_m2 & S_m3 & S_v1 & S_v2 & S_v3).
    pose proof (BLKSH_split5 _ _ _ _ _ _ _ _ BS) as (BS_m2 & BS_m3 & BS_v1 & BS_v2 & BS_v3).
    unfold state_sh. cbn [set_m1 st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
    split; [exact NEW|]. split; [eapply umap_sh_xp; [exact XP | exact S_m2 | exact BS_m2]|]. split; [eapply umap_sh_xp; [exact XP | exact S_m3 | exact BS_m3]|]. split; [eapply vec_sh_xp; [exact XP | exact S_v1 | exact O_v1 | exact BS_v1]|]. split; [eapply vec_sh_xp; [exact XP | exact S_v2 | exact O_v2 | exact BS_v2]|]. eapply vec_sh_xp; [exact XP | exact S_v3 | exact O_v3 | exact BS_v3].
  Qed.

  Lemma sh_upd_m2 : forall LBa LBk SP X m m' st c (t : Z * Z * list (Z * (Z * (Z * Z * Z)))),
    state_repA LBa m st c -> state_sh m c -> xpres H LBk SP X m m' ->
    BLKSH LBk SP X (cb_m1 c ++ cb_m3 c ++ cb_v1 c ++ cb_v2 c ++ cb_v3 c) -> umap_sh m' 32 t ->
    state_sh m' (set_m2 c t).
  Proof.
    intros LBa LBk SP X m m' st c t R S XP BS NEW.
    pose proof (vord_of_rep _ _ _ _ R) as (O_v1 & O_v2 & O_v3).
    destruct S as (S_m1 & S_m2 & S_m3 & S_v1 & S_v2 & S_v3).
    pose proof (BLKSH_split5 _ _ _ _ _ _ _ _ BS) as (BS_m1 & BS_m3 & BS_v1 & BS_v2 & BS_v3).
    unfold state_sh. cbn [set_m2 st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
    split; [eapply umap_sh_xp; [exact XP | exact S_m1 | exact BS_m1]|]. split; [exact NEW|]. split; [eapply umap_sh_xp; [exact XP | exact S_m3 | exact BS_m3]|]. split; [eapply vec_sh_xp; [exact XP | exact S_v1 | exact O_v1 | exact BS_v1]|]. split; [eapply vec_sh_xp; [exact XP | exact S_v2 | exact O_v2 | exact BS_v2]|]. eapply vec_sh_xp; [exact XP | exact S_v3 | exact O_v3 | exact BS_v3].
  Qed.

  Lemma sh_upd_m3 : forall LBa LBk SP X m m' st c (t : Z * Z * list (Z * (Z * Z))),
    state_repA LBa m st c -> state_sh m c -> xpres H LBk SP X m m' ->
    BLKSH LBk SP X (cb_m1 c ++ cb_m2 c ++ cb_v1 c ++ cb_v2 c ++ cb_v3 c) -> umap_sh m' 24 t ->
    state_sh m' (set_m3 c t).
  Proof.
    intros LBa LBk SP X m m' st c t R S XP BS NEW.
    pose proof (vord_of_rep _ _ _ _ R) as (O_v1 & O_v2 & O_v3).
    destruct S as (S_m1 & S_m2 & S_m3 & S_v1 & S_v2 & S_v3).
    pose proof (BLKSH_split5 _ _ _ _ _ _ _ _ BS) as (BS_m1 & BS_m2 & BS_v1 & BS_v2 & BS_v3).
    unfold state_sh. cbn [set_m3 st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
    split; [eapply umap_sh_xp; [exact XP | exact S_m1 | exact BS_m1]|]. split; [eapply umap_sh_xp; [exact XP | exact S_m2 | exact BS_m2]|]. split; [exact NEW|]. split; [eapply vec_sh_xp; [exact XP | exact S_v1 | exact O_v1 | exact BS_v1]|]. split; [eapply vec_sh_xp; [exact XP | exact S_v2 | exact O_v2 | exact BS_v2]|]. eapply vec_sh_xp; [exact XP | exact S_v3 | exact O_v3 | exact BS_v3].
  Qed.

  Lemma sh_upd_v1 : forall LBa LBk SP X m m' st c (t : Z * Z * Z),
    state_repA LBa m st c -> state_sh m c -> xpres H LBk SP X m m' ->
    BLKSH LBk SP X (cb_m1 c ++ cb_m2 c ++ cb_m3 c ++ cb_v2 c ++ cb_v3 c) -> vec_sh m' t ->
    state_sh m' (set_v1 c t).
  Proof.
    intros LBa LBk SP X m m' st c t R S XP BS NEW.
    pose proof (vord_of_rep _ _ _ _ R) as (O_v1 & O_v2 & O_v3).
    destruct S as (S_m1 & S_m2 & S_m3 & S_v1 & S_v2 & S_v3).
    pose proof (BLKSH_split5 _ _ _ _ _ _ _ _ BS) as (BS_m1 & BS_m2 & BS_m3 & BS_v2 & BS_v3).
    unfold state_sh. cbn [set_v1 st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
    split; [eapply umap_sh_xp; [exact XP | exact S_m1 | exact BS_m1]|]. split; [eapply umap_sh_xp; [exact XP | exact S_m2 | exact BS_m2]|]. split; [eapply umap_sh_xp; [exact XP | exact S_m3 | exact BS_m3]|]. split; [exact NEW|]. split; [eapply vec_sh_xp; [exact XP | exact S_v2 | exact O_v2 | exact BS_v2]|]. eapply vec_sh_xp; [exact XP | exact S_v3 | exact O_v3 | exact BS_v3].
  Qed.

  Lemma sh_upd_v2 : forall LBa LBk SP X m m' st c (t : Z * Z * Z),
    state_repA LBa m st c -> state_sh m c -> xpres H LBk SP X m m' ->
    BLKSH LBk SP X (cb_m1 c ++ cb_m2 c ++ cb_m3 c ++ cb_v1 c ++ cb_v3 c) -> vec_sh m' t ->
    state_sh m' (set_v2 c t).
  Proof.
    intros LBa LBk SP X m m' st c t R S XP BS NEW.
    pose proof (vord_of_rep _ _ _ _ R) as (O_v1 & O_v2 & O_v3).
    destruct S as (S_m1 & S_m2 & S_m3 & S_v1 & S_v2 & S_v3).
    pose proof (BLKSH_split5 _ _ _ _ _ _ _ _ BS) as (BS_m1 & BS_m2 & BS_m3 & BS_v1 & BS_v3).
    unfold state_sh. cbn [set_v2 st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
    split; [eapply umap_sh_xp; [exact XP | exact S_m1 | exact BS_m1]|]. split; [eapply umap_sh_xp; [exact XP | exact S_m2 | exact BS_m2]|]. split; [eapply umap_sh_xp; [exact XP | exact S_m3 | exact BS_m3]|]. split; [eapply vec_sh_xp; [exact XP | exact S_v1 | exact O_v1 | exact BS_v1]|]. split; [exact NEW|]. eapply vec_sh_xp; [exact XP | exact S_v3 | exact O_v3 | exact BS_v3].
  Qed.

  Lemma sh_upd_v3 : forall LBa LBk SP X m m' st c (t : Z * Z * Z),
    state_repA LBa m st c -> state_sh m c -> xpres H LBk SP X m m' ->
    BLKSH LBk SP X (cb_m1 c ++ cb_m2 c ++ cb_m3 c ++ cb_v1 c ++ cb_v2 c) -> vec_sh m' t ->
    state_sh m' (set_v3 c t).
  Proof.
    intros LBa LBk SP X m m' st c t R S XP BS NEW.
    pose proof (vord_of_rep _ _ _ _ R) as (O_v1 & O_v2 & O_v3).
    destruct S as (S_m1 & S_m2 & S_m3 & S_v1 & S_v2 & S_v3).
    pose proof (BLKSH_split5 _ _ _ _ _ _ _ _ BS) as (BS_m1 & BS_m2 & BS_m3 & BS_v1 & BS_v2).
    unfold state_sh. cbn [set_v3 st_m1 st_m2 st_m3 st_v1 st_v2 st_v3].
    split; [eapply umap_sh_xp; [exact XP | exact S_m1 | exact BS_m1]|]. split; [eapply umap_sh_xp; [exact XP | exact S_m2 | exact BS_m2]|]. split; [eapply umap_sh_xp; [exact XP | exact S_m3 | exact BS_m3]|]. split; [eapply vec_sh_xp; [exact XP | exact S_v1 | exact O_v1 | exact BS_v1]|]. split; [eapply vec_sh_xp; [exact XP | exact S_v2 | exact O_v2 | exact BS_v2]|]. exact NEW.
  Qed.

  Definition scal_cells (m : mem) (st : Z) (d : stateC) : Prop :=
    cell8 ASEGS m st (st_words d) /\ cell8 ASEGS m (st + 8) (st_nwords d) /\ cell8 ASEGS m (st + 16) (st_diag d)
    /\ cell8 ASEGS m (st + 24) (st_widx d) /\ cell8 ASEGS m (st + 32) (st_icount d) /\ cell4 ASEGS m (st + 40) (st_endian d)
    /\ cellw ASEGS m (st + 44) 2 (st_flags d).

  Lemma scal_of_rep : forall LB m st c, state_repA LB m st c -> scal_cells m st c.
  Proof.
    intros LB m st c R. unfold state_repA in R. destruct R as [R _].
    destruct R as [R_w0 R_w1 R_w2 R_w3 R_w4 R_w5 R_w6 _ _ _ _ _ _ _ _ _].
    exact (conj R_w0 (conj R_w1 (conj R_w2 (conj R_w3 (conj R_w4 (conj R_w5 R_w6)))))).
  Qed.

  Lemma rep_upd_scal : forall LBa LBb LBk SP X m m' st c d,
    state_repA LBa m st c -> xpres H LBk SP X m m' -> OBJX LBk SP X st 0 46 ->
    BLKX LBk SP X LBb (state_blocks c) -> scal_cells m' st d -> AIMG_TOP <= st -> st + 240 <= 2 ^ 47 ->
    state_repA LBb m' st (set_scal c d).
  Proof.
    intros LBa LBb LBk SP X m m' st c d R XP OX BK NEW STL STH.
    pose proof STL as STL'. unfold AIMG_TOP in STL'.
    unfold state_repA in R |- *. destruct R as [R RV]. split; [|exact RV].
    destruct R as [R_w0 R_w1 R_w2 R_w3 R_w4 R_w5 R_w6 R_m1 R_m2 R_m3 R_v1 R_v2 R_v3 R_def R_al R_nd].
    destruct NEW as (N0 & N1 & N2 & N3 & N4 & N5 & N6).
    rewrite state_blocks_cb in BK.
    apply BLKX_app in BK as [BK_m1 BK]. apply BLKX_app in BK as [BK_m2 BK]. apply BLKX_app in BK as [BK_m3 BK].
    apply BLKX_app in BK as [BK_v1 BK]. apply BLKX_app in BK as [BK_v2 BK_v3].
    assert (ND : defined m' st 46).
    { intros i Hi.
      assert (RW : forall a (w : N) v, cellw ASEGS m' a w v -> AIMG_TOP <= a -> a + Z.of_N w <= 2 ^ 64 -> (w = 8 \/ w = 4 \/ w = 2)%N ->
                   defined m' a (Z.of_N w)).
      { intros a w v C Ha Hw Hw'. destruct Hw' as [E|[E|E]]; subst w.
        - exact (defined_of_cellw8_hi _ _ _ C Ha Hw).
        - exact (defined_of_rw_cells_hi _ _ _ (rw_cells_of_cellw4 _ _ _ C Ha Hw) Ha).
        - exact (defined_of_rw_cells_hi _ _ _ (rw_cells_of_cellw2 _ _ _ C Ha Hw) Ha). }
      destruct (Z_lt_le_dec i 8). { apply (RW _ _ _ N0); [lia | cbn; lia | tauto | lia]. }
      destruct (Z_lt_le_dec i 16). { replace (st + i) with (st + 8 + (i - 8)) by lia. apply (RW _ _ _ N1); [lia | cbn; lia | tauto | cbn; lia]. }
      destruct (Z_lt_le_dec i 24). { replace (st + i) with (st + 16 + (i - 16)) by lia. apply (RW _ _ _ N2); [lia | cbn; lia | tauto | cbn; lia]. }
      destruct (Z_lt_le_dec i 32). { replace (st + i) with (st + 24 + (i - 24)) by lia. apply (RW _ _ _ N3); [lia | cbn; lia | tauto | cbn; lia]. }
      destruct (Z_lt_le_dec i 40). { replace (st + i) with (st + 32 + (i - 32)) by lia. apply (RW _ _ _ N4); [lia | cbn; lia | tauto | cbn; lia]. }
      destruct (Z_lt_le_dec i 44). { replace (st + i) with (st + 40 + (i - 40)) by lia. apply (RW _ _ _ N5); [lia | cbn; lia | tauto | cbn; lia]. }
      replace (st + i) with (st + 44 + (i - 44)) by lia. apply (RW _ _ _ N6); [lia | cbn; lia | tauto | cbn; lia]. }
    constructor; cbn [set_scal st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3];
      try assumption.
    - eapply (umapx_xp 24 Z (nval24 ASEGS) LBk SP X LBa LBb m m' (st + 48)); [exact (nval24_agree ASEGS) | lia | exact XP | exact R_m1 | exact (objx_at _ _ _ _ _ _ OX 48 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact BK_m1].
    - eapply (umapx_xp 32 (Z * Z * Z) (nval32 ASEGS) LBk SP X LBa LBb m m' (st + 88)); [exact (nval32_agree ASEGS) | lia | exact XP | exact R_m2 | exact (objx_at _ _ _ _ _ _ OX 88 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact BK_m2].
    - eapply (umapx_xp 24 Z (nval24 ASEGS) LBk SP X LBa LBb m m' (st + 128)); [exact (nval24_agree ASEGS) | lia | exact XP | exact R_m3 | exact (objx_at _ _ _ _ _ _ OX 128 40 ltac:(lia) ltac:(lia) ltac:(lia)) | exact BK_m3].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 168)); [exact XP | exact R_v1 | exact (objx_at _ _ _ _ _ _ OX 168 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact BK_v1].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 192)); [exact XP | exact R_v2 | exact (objx_at _ _ _ _ _ _ OX 192 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact BK_v2].
    - eapply (vraw_xp LBk SP X LBa LBb m m' (st + 216)); [exact XP | exact R_v3 | exact (objx_at _ _ _ _ _ _ OX 216 24 ltac:(lia) ltac:(lia) ltac:(lia)) | lia | lia | exact BK_v3].
    - intros i Hi. destruct (Z_lt_le_dec i 46) as [Li|Li]; [apply ND; lia|].
      assert (D1 : defined m' (st + i) 1).
      { eapply (defined_xp LBk SP X m m' (st + i) 1); [exact XP | | | lia | lia].
        * intros k Hk. replace (st + i + k) with (st + (i + k)) by lia. apply R_def. lia.
        * intros k Hk. apply OX; lia. }
      specialize (D1 0 ltac:(lia)). rewrite Z.add_0_r in D1. exact D1.
  Qed.

  Lemma rep_keep : forall LBa LBb LBk SP X m m' st c,
    state_repA LBa m st c -> xpres H LBk SP X m m' -> OBJX LBk SP X st 0 0 ->
    BLKX LBk SP X LBb (state_blocks c) -> AIMG_TOP <= st -> st + 240 <= 2 ^ 47 ->
    state_repA LBb m' st c.
  Proof.
    intros LBa LBb LBk SP X m m' st c R XP OX BK STL STH.
    assert (OX' : OBJX LBk SP X st 0 46) by (intros a Ha _; apply OX; lia).
    pose proof (rep_upd_scal LBa LBb LBk SP X m m' st c c R XP OX' BK) as K.
    assert (SC : scal_cells m' st c).
    { pose proof (scal_of_rep _ _ _ _ R) as (N0 & N1 & N2 & N3 & N4 & N5 & N6). pose proof STL as STL'. unfold AIMG_TOP in STL'.
      split; [eapply cellw_xp; [exact XP | exact N0 | intros i Hi; apply OX; lia | lia | lia]|].
      split; [eapply cellw_xp; [exact XP | exact N1 | intros i Hi; apply OX; lia | lia | lia]|].
      split; [eapply cellw_xp; [exact XP | exact N2 | intros i Hi; apply OX; lia | lia | lia]|].
      split; [eapply cellw_xp; [exact XP | exact N3 | intros i Hi; apply OX; lia | lia | lia]|].
      split; [eapply cellw_xp; [exact XP | exact N4 | intros i Hi; apply OX; lia | lia | lia]|].
      split; [eapply cellw_xp; [exact XP | exact N5 | intros i Hi; apply OX; lia | lia | cbn; lia]|].
      eapply cellw_xp; [exact XP | exact N6 | intros i Hi; apply OX; lia | lia | cbn; lia]. }
    specialize (K SC STL STH). destruct c. exact K.
  Qed.

  Lemma sh_keep : forall LBa LBk SP X m m' st c,
    state_repA LBa m st c -> state_sh m c -> xpres H LBk SP X m m' -> BLKSH LBk SP X (state_blocks c) -> state_sh m' c.
  Proof.
    intros LBa LBk SP X m m' st c R S XP BS.
    pose proof (vord_of_rep _ _ _ _ R) as (O_v1 & O_v2 & O_v3).
    destruct S as (S_m1 & S_m2 & S_m3 & S_v1 & S_v2 & S_v3).
    rewrite state_blocks_cb in BS.
    apply BLKSH_app in BS as [BS_m1 BS]. apply BLKSH_app in BS as [BS_m2 BS]. apply BLKSH_app in BS as [BS_m3 BS].
    apply BLKSH_app in BS as [BS_v1 BS]. apply BLKSH_app in BS as [BS_v2 BS_v3].
    split; [eapply umap_sh_xp; [exact XP | exact S_m1 | exact BS_m1]|]. split; [eapply umap_sh_xp; [exact XP | exact S_m2 | exact BS_m2]|].
    split; [eapply umap_sh_xp; [exact XP | exact S_m3 | exact BS_m3]|].
    split; [eapply vec_sh_xp; [exact XP | exact S_v1 | exact O_v1 | exact BS_v1]|].
    split; [eapply vec_sh_xp; [exact XP | exact S_v2 | exact O_v2 | exact BS_v2]|].
    eapply vec_sh_xp; [exact XP | exact S_v3 | exact O_v3 | exact BS_v3].
  Qed.
End Tr.

Lemma sh_disj16 : forall A n B k, 0 <= A -> A mod 8 = 0 -> 0 <= n -> 0 <= B -> B mod 8 = 0 -> 0 <= k ->
  (A + n + 16 <= B \/ B + k + 16 <= A) -> sh A + nsh n <= sh B \/ sh B + nsh k <= sh A.
Proof. intros A n B k HA HA8 Hn HB HB8 Hk D. unfold sh, nsh. Z.div_mod_to_equations. lia. Qed.

Section KitH.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma objx_intro : forall LBk SP X st lo hi,
    (as_FSB H <= st /\ st + 240 <= as_FSB H + AFS_SIZE) \/ SP <= st ->
    (forall a, st <= a < st + 240 -> ~ (st + lo <= a < st + hi) -> ~ rin_ivs X a) ->
    OBJX H LBk SP X st lo hi.
  Proof.
    intros LBk SP X st lo hi HS HX a Ha Hw. split; [| exact (HX a Ha Hw)].
    unfold aclient_addr. destruct HS as [HS|HS]; [right; right; right; right; left; lia | left; lia].
  Qed.

  Lemma blkx_intro : forall LBk SP X LBb bs,
    (forall p n, In (p, n) bs -> In (p, n) (lbl LBk) /\ In (p, n) (lbl LBb) /\ (forall a, p <= a < p + n -> ~ rin_ivs X a)) ->
    BLKX H LBk SP X LBb bs.
  Proof.
    intros LBk SP X LBb bs K p n Hin. destruct (K p n Hin) as (K1 & K2 & K3). split; [|exact K2].
    intros a Ha. split; [|exact (K3 a Ha)].
    destruct (lbl_in_inv _ _ _ K1) as (q & Hq).
    right; right; left. exists (q, p, n). split; [exact Hq | unfold blk_addr, blk_size; cbn; lia].
  Qed.

  Lemma blksh_intro : forall LBk SP X bs,
    (forall p n, In (p, n) bs -> In (p, n) (lbl LBk) /\ (forall a, sh p <= a < sh p + nsh n -> ~ rin_ivs X a)) ->
    BLKSH H LBk SP X bs.
  Proof.
    intros LBk SP X bs K p n Hin a Ha. destruct (K p n Hin) as (K1 & K3). split; [|exact (K3 a Ha)].
    destruct (lbl_in_inv _ _ _ K1) as (q & Hq).
    right; right; right; left. exists (q, p, n). split; [exact Hq | unfold blk_addr, blk_size; cbn; lia].
  Qed.

  Lemma nodup_addr_gen : forall LB, List.NoDup (map blk_id LB) ->
    (forall b1 b2, In b1 LB -> In b2 LB -> blk_id b1 <> blk_id b2 -> blk_addr b1 <> blk_addr b2) -> List.NoDup (map blk_addr LB).
  Proof.
    induction LB as [|b LB IH]; intros ND D; [constructor|]. cbn [map] in *. inversion ND as [|? ? NI ND']; subst.
    constructor.
    - intros Hin. apply in_map_iff in Hin. destruct Hin as (b' & E & Hb').
      assert (NE : blk_id b <> blk_id b') by (intros E'; apply NI; rewrite E'; apply in_map_iff; exists b'; split; [reflexivity | exact Hb']).
      exact (D b b' (or_introl eq_refl) (or_intror Hb') NE (eq_sym E)).
    - apply IH; [exact ND'|]. intros b1 b2 H1 H2. apply D; right; assumption.
  Qed.

  Lemma nodup_addr_of_RHEAP : forall s LB m, as_RHEAP H s LB m -> List.NoDup (map blk_addr LB).
  Proof.
    intros s LB m RH. apply nodup_addr_gen; [exact (ah_nodup H HH _ _ _ RH)|].
    intros b1 b2 H1 H2 NE E. pose proof (ah_disj H HH _ _ _ b1 b2 RH H1 H2 NE) as D.
    pose proof (ah_blocks H HH _ _ _ b1 RH H1) as (_ & _ & B1n & _).
    pose proof (ah_blocks H HH _ _ _ b2 RH H2) as (_ & _ & B2n & _). lia.
  Qed.

  Lemma nodup_fst_of_perm : forall s LB m LBx LBy bs, as_RHEAP H s LB m -> Permutation LB (LBx ++ LBy) ->
    Permutation (lbl LBx) bs -> List.NoDup (map fst bs).
  Proof.
    intros s LB m LBx LBy bs RH P Q.
    pose proof (nodup_addr_of_RHEAP s LB m RH) as ND.
    assert (ND2 : List.NoDup (map blk_addr (LBx ++ LBy))) by (eapply Permutation_NoDup; [apply Permutation_map; exact P | exact ND]).
    rewrite map_app in ND2. apply NoDup_app_remove_r in ND2.
    assert (E : map fst (lbl LBx) = map blk_addr LBx) by (unfold lbl; rewrite map_map; reflexivity).
    eapply Permutation_NoDup; [apply Permutation_map; exact Q | rewrite E; exact ND2].
  Qed.

  Lemma nodup_fst_of_perm' : forall s LB m LBx LBy bs, as_RHEAP H s LB m -> Permutation LB (LBx ++ LBy) ->
    Permutation (lbl LBx) bs -> NoDup (map fst bs).
  Proof. intros s LB m LBx LBy bs RH P Q. apply NoDup_ListNoDup. exact (nodup_fst_of_perm s LB m LBx LBy bs RH P Q). Qed.

  Lemma lb_remove_notin2 : forall p LB b, List.NoDup (map blk_id LB) -> In b (as_lb_remove H p LB) -> blk_id b <> p.
  Proof.
    pose proof (ah_lb_remove H HH) as (L1 & L2 & L3).
    intros p LB. induction LB as [|b0 LB IH]; intros b ND Hb.
    - exfalso. exact (L3 p [] b Hb).
    - cbn [map] in ND. inversion ND as [|? ? NI ND']; subst.
      destruct (Z.eq_dec (blk_id b0) p) as [E|E].
      + destruct b0 as [[p0 A0] n0]. unfold blk_id in E. cbn in E. subst p0.
        rewrite L1 in Hb by exact NI. intros Eb. apply NI. rewrite <- Eb. apply in_map_iff. exists b. split; [reflexivity | exact Hb].
      + rewrite (L2 p b0 LB E) in Hb. destruct Hb as [Hb|Hb]; [subst b; exact E | exact (IH b ND' Hb)].
  Qed.

  Lemma xpres_drop_blk : forall s LB pid A n SP X m0 m m',
    as_RHEAP H s LB m0 -> In (pid, A, n) LB -> aceil <= SP ->
    xpres H (as_lb_remove H pid LB) SP (X ++ [(A, A + n); (sh A, sh A + nsh n)]) m m' ->
    xpres H (as_lb_remove H pid LB) SP X m m'.
  Proof.
    intros s LB pid A n SP X m0 m m' RH IN HSP XP a Ha [Hc Hx]. apply XP; [exact Ha|]. split; [exact Hc|].
    rewrite rin_ivs_app. intros [K|K]; [exact (Hx K)|]. cbn [rin_ivs fst snd] in K.
    pose proof (ah_blocks H HH _ _ _ _ RH IN) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
    unfold blk_addr, blk_size in R0, R16, Rn, RI, RC, RF, RAPP. cbn [fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
    pose proof (ah_fsb H HH _ _ _ RH) as (F1 & F2 & F3 & F4).
    pose proof (ah_nodup H HH _ _ _ RH) as ND.
    pose proof aceil_facts as ACF.
    pose proof (ah_lb_remove H HH) as (_ & _ & L3).
    assert (SHA : sh A + nsh n <= sh aceil) by (unfold sh, nsh; destruct ACF as (_ & ACM & _); Z.div_mod_to_equations; nia).
    assert (SHB : sh aceil < AHI_LO) by (unfold sh, AHI_LO; rewrite ASHADOW_BASE_val; destruct ACF as (ACB & _); Z.div_mod_to_equations; lia).
    assert (SHL : ASHADOW_BASE <= sh A) by (unfold sh; pose proof (Z.div_pos A 8); lia).
    unfold AIMG_TOP in RI. unfold ASHADOW_BASE in SHL.
    assert (APPB : (A + n <= ALOWSH_LO) \/ (AHI_LO <= A)) by (unfold aapp, aapp_lo, aapp_hi in RAPP; destruct RAPP as [[_ P]|[P _]]; [left | right]; lia).
    unfold ALOWSH_LO, AHI_LO in APPB, SHB.
    unfold aclient_addr in Hc.
    destruct Hc as [Hc|[Hc|[(b & Hb & Hr)|[(b & Hb & Hr)|[Hc|[Hc|Hc]]]]]].
    - destruct ACF as (ACB & _). destruct K as [K|[K|K]]; [lia | lia | exact K].
    - unfold aimg_client in Hc. destruct K as [K|[K|K]]; [lia | lia | exact K].
    - pose proof (L3 _ _ _ Hb) as Hb'.
      pose proof (lb_remove_notin2 pid LB b ND Hb) as Hid.
      pose proof (ah_disj H HH _ _ _ (pid, A, n) b RH IN Hb' (fun E => Hid (eq_sym E))) as D.
      pose proof (ah_blocks H HH _ _ _ b RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      destruct b as [[pb Ab] nb]. unfold blk_addr, blk_size in *. cbn [fst snd] in *.
      assert (QB : (Ab + nb <= 0x7fff7000) \/ (0x10007fff8000 <= Ab))
        by (unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in QAPP; destruct QAPP as [[_ P]|[P _]]; [left | right]; lia).
      destruct K as [K|[K|K]]; [lia | lia | exact K].
    - pose proof (L3 _ _ _ Hb) as Hb'.
      pose proof (lb_remove_notin2 pid LB b ND Hb) as Hid.
      pose proof (ah_disj H HH _ _ _ (pid, A, n) b RH IN Hb' (fun E => Hid (eq_sym E))) as D.
      pose proof (ah_blocks H HH _ _ _ b RH Hb') as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      destruct b as [[pb Ab] nb]. unfold blk_addr, blk_size in *. cbn [fst snd] in *.
      assert (SHQ : sh Ab + nsh nb <= AHI_LO) by (apply sh_nsh_high; [lia | lia | unfold AAPP_HI; destruct ACF as (ACB & _); lia]).
      assert (SHQ2 : ASHADOW_BASE <= sh Ab) by (unfold sh; pose proof (Z.div_pos Ab 8); lia).
      unfold AHI_LO, ASHADOW_BASE in SHQ, SHQ2.
      destruct K as [K|[K|K]]; [lia | | exact K].
      assert (A8 : A mod 8 = 0) by (clear - R16; Z.div_mod_to_equations; lia).
      assert (B8 : Ab mod 8 = 0) by (clear - Q16; Z.div_mod_to_equations; lia).
      pose proof (sh_disj16 A n Ab nb ltac:(lia) A8 Rn ltac:(lia) B8 Qn ltac:(lia)) as SD. lia.
    - unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in F4. unfold AFS_SIZE in *.
      destruct K as [K|[K|K]]; [lia | | exact K].
      destruct F4 as [[_ P]|[P _]]; lia.
    - destruct K as [K|[K|K]].
      + destruct ACF as (ACB & _).
        unfold sh in Hc. rewrite ASHADOW_BASE_val in Hc. unfold AFS_SIZE in Hc.
        assert (FT : as_FSB H + 0xb09000 <= 0x7fffff800000) by (unfold AFS_SIZE in F2; lia).
        clear - K Hc APPB FT F1 RI. unfold AIMG_TOP in F1.
        Z.div_mod_to_equations. lia.
      + assert (FB0 : 0 <= as_FSB H) by (unfold AIMG_TOP in F1; lia).
        assert (FB8 : as_FSB H mod 8 = 0) by (clear - F3; Z.div_mod_to_equations; lia).
        assert (A8 : A mod 8 = 0) by (clear - R16; Z.div_mod_to_equations; lia).
        pose proof (sh_disj16 A n (as_FSB H) AFS_SIZE ltac:(lia) A8 Rn FB0 FB8 ltac:(unfold AFS_SIZE; lia)
                      ltac:(unfold AFS_SIZE in *; lia)) as SD.
        assert (E : sh (as_FSB H + AFS_SIZE) = sh (as_FSB H) + nsh AFS_SIZE).
        { unfold sh, nsh, AFS_SIZE. clear - FB8 FB0. Z.div_mod_to_equations. lia. }
        rewrite E in Hc. lia.
      + exact K.
    - assert (NN : 0 <= nsh n) by (unfold nsh; apply Z.div_pos; lia).
      unfold AHI_LO in Hc. destruct K as [K|[K|K]]; [lia | lia | exact K].
  Qed.
End KitH.

Lemma rw_cells_of_vraw : forall A m v b e c, vraw MI_A A m v b e c -> AIMG_TOP <= v -> v + 24 <= 2 ^ 64 ->
  rw_cells asegs m v [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 c)].
Proof.
  intros A m v b e c [Vb Ve Vc _] H1 H2. pose proof H1 as H1'. unfold AIMG_TOP in H1'.
  change [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 c)]
    with ([C8 (Z_to_bv 64 b)] ++ [C8 (Z_to_bv 64 e)] ++ [C8 (Z_to_bv 64 c)]).
  apply rw_cells_app. split; [apply rw_cells_of_cellw8; [exact Vb | exact H1 | lia]|].
  apply rw_cells_app. split.
  - eapply rw_cells_addr; [apply rw_cells_of_cellw8; [exact Ve | unfold AIMG_TOP; lia | lia] | cbn; lia].
  - eapply rw_cells_addr; [apply rw_cells_of_cellw8; [exact Vc | unfold AIMG_TOP; lia | lia] | cbn; lia].
Qed.

Lemma vraw_of_rw_cells : forall A m v b e c,
  rw_cells asegs m v [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 c)] ->
  0 <= b < 2 ^ 64 -> 0 <= e < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= v ->
  ((b = 0 /\ e = 0 /\ c = 0) \/ (b <> 0 /\ In (b, c - b) (live MI_A A) /\ b <= e <= c)) ->
  vraw MI_A A m v b e c.
Proof.
  intros A m v b e c RC Hb He Hc Hv K.
  change [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 c)]
    with ([C8 (Z_to_bv 64 b)] ++ [C8 (Z_to_bv 64 e)] ++ [C8 (Z_to_bv 64 c)]) in RC.
  apply rw_cells_app in RC as [R0 RC]. apply rw_cells_app in RC as [R8 R16].
  assert (R8' : rw_cells asegs m (v + 8) [C8 (Z_to_bv 64 e)]) by (eapply rw_cells_addr; [exact R8 | cbn; lia]).
  assert (R16' : rw_cells asegs m (v + 16) [C8 (Z_to_bv 64 c)]) by (eapply rw_cells_addr; [exact R16 | cbn; lia]).
  clear R8 R16. rename R8' into R8. rename R16' into R16.
  constructor.
  - exact (cellw8_of_rw_cells m v b R0 Hb Hv).
  - exact (cellw8_of_rw_cells m (v + 8) e R8 He ltac:(lia)).
  - exact (cellw8_of_rw_cells m (v + 16) c R16 Hc ltac:(lia)).
  - exact K.
Qed.
