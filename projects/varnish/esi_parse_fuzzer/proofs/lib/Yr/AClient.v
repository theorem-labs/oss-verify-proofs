(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Image Bytes Walk Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Client.
Context {Clg : Ceiling} {L : clayout} {AI : AsanAlloc L}.   (* [comment removed for export] *)
Let segs := cl_segs L.

(* [comment removed for export] *)
Lemma layout_facts :
  4096 <= cl_image_lo L <= cl_rw_lo L /\ cl_rw_lo L <= cl_image_hi L /\ cl_image_hi L <= 2147446784
  /\ 17594333495296 + 65536 <= alloc_ceiling /\ 140735332483072 <= alloc_ceiling <= 140737479966720
  /\ cl_rw_lo L <= cl_errno L /\ cl_errno L + 4 <= cl_image_hi L.
Proof.
  pose proof (as_layout_order L) as LO. pose proof (as_errno_where L) as EW. pose proof alloc_ceiling_val as CV.
  unfold kLowShadowMapBeg, kHighMemBeg in LO. lia.
Qed.

(* [comment removed for export] *)
Definition crange (A : AS) (v : mem) (a n : Z) : Prop :=
  0 <= a /\ a + n <= 2^64 /\
  forall i, 0 <= i < n ->
    ~ owned A (a + i) /\ ~ (cl_errno L <= a + i < cl_errno L + 4)
    /\ (v (Z_to_bv 64 (a + i)) <> None \/ in_image L (a + i)).

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma crange_stack : forall A m md v a n,
  ainv A m md -> alloc_ceiling <= a -> a + n <= 2^64 -> mapped v a n -> crange A v a n.
Proof.
  intros A m md v a n AI0 Hc Hn Hm. pose proof layout_facts as LO.
  split; [lia|]. split; [exact Hn|].
  intros i Hi. split; [|split].
  - intros Ho. destruct (as_owned_where L A m md (a + i) AI0 Ho) as [Hs|[[_ Hlt] _]].
    + apply (as_static_where L) in Hs. lia.
    + lia.
  - lia.
  - left. apply Hm. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma crange_data : forall A m md v a n,
  ainv A m md -> cl_rw_lo L <= a -> a + n <= cl_image_hi L -> 0 <= n ->
  (forall i, 0 <= i < n -> ~ cl_static L (a + i)) ->
  (a + n <= cl_errno L \/ cl_errno L + 4 <= a) ->
  crange A v a n.
Proof.
  intros A m md v a n AI0 Hlo Hhi Hn Hs He. pose proof layout_facts as LO.
  split; [lia|]. split; [lia|].
  intros i Hi. split; [|split].
  - intros Ho. destruct (as_owned_where L A m md (a + i) AI0 Ho) as [Hst|[_ Hni]]; [exact (Hs i Hi Hst)| apply Hni; unfold in_image; lia].
  - lia.
  - right. unfold in_image. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma crange_block : forall A m md p k a n,
  ainv A m md -> a_live A p = Some k -> p <= a -> a + n <= p + k -> 0 <= n ->
  crange A (aview A m) a n.
Proof.
  intros A m md p k a n AI0 HL Hp Hn Hn0.
  (first [ pose proof ((as_live_ok L A m md p k AI0 HL)) as dR_1; dand8 dR_1 as K0 AL LO HI IMG MP NO _ | destruct (as_live_ok L A m md p k AI0 HL) as (K0 & AL & LO & HI & IMG & MP & NO & _) ]).
  pose proof layout_facts as LO'.
  unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in LO.   (* [comment removed for export] *)
  split; [lia|]. split; [lia|].
  intros i Hi. split; [|split].
  - replace (a + i) with (p + (a - p + i)) by lia. apply NO. lia.
  - lia.
  - left. replace (a + i) with (p + (a - p + i)) by lia. apply MP. lia.
Qed.

(* [comment removed for export] *)
Lemma crange_fframe : forall A m md ff k age a n,
  ainv A m md -> a_frame A ff = Some (k, age) -> ff <= a -> a + n <= ff + fsize k - 8 -> 0 <= n ->
  crange A (aview A m) a n.
Proof.
  intros A m md ff k age a n AI0 HF Hp Hn Hn0.
  (first [ pose proof ((as_frame_ok L A m md ff k age AI0 HF)) as dR_2; dand11 dR_2 as K0 AL LO HI IMG WR MP _ _ NO _ | destruct (as_frame_ok L A m md ff k age AI0 HF) as (K0 & AL & LO & HI & IMG & WR & MP & _ & _ & NO & _) ]).
  pose proof layout_facts as LO'.
  assert (FS : 8 <= fsize k) by (unfold fsize; pose proof (Z.pow_pos_nonneg 2 k); nia).
  unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in LO.   (* [comment removed for export] *)
  split; [lia|]. split; [lia|].
  intros i Hi. split; [|split].
  - replace (a + i) with (ff + (a - ff + i)) by lia. apply NO. lia.
  - lia.
  - left. replace (a + i) with (ff + (a - ff + i)) by lia. apply MP. lia.
Qed.

(* [comment removed for export] *)
Lemma crange_fshadow : forall A m md ff k age a n,
  ainv A m md -> a_frame A ff = Some (k, age) -> sh ff <= a -> a + n <= sh ff + fsize k / 8 -> 0 <= n ->
  crange A (aview A m) a n.
Proof.
  intros A m md ff k age a n AI0 HF Hp Hn Hn0.
  (first [ pose proof ((as_frame_ok L A m md ff k age AI0 HF)) as dR_3; dand11 dR_3 as K0 AL LO HI IMG _ _ WR MP _ NO | destruct (as_frame_ok L A m md ff k age AI0 HF) as (K0 & AL & LO & HI & IMG & _ & _ & WR & MP & _ & NO) ]).
  pose proof layout_facts as LO'.
  (first [ dand3 WR as W0 W1 W | destruct WR as (W0 & W1 & W) ]).
  split; [lia|]. split; [lia|].
  intros i Hi. split; [|split].
  - replace (a + i) with (sh ff + (a - sh ff + i)) by lia. apply NO. lia.
  - (* [comment removed for export] *)
    assert (0 <= ff / 8) by (apply Z.div_pos; unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in LO; lia).
    unfold sh, kShadowOffset in *. lia.
  - left. replace (a + i) with (sh ff + (a - sh ff + i)) by lia. apply MP. lia.
Qed.

(* [comment removed for export] *)
Section Transport.
Variables (A A' : AS) (sp win : Z) (victim newb : Z -> Prop) (v v' : mem).
Hypothesis FR : frame_ok L (owned A) (owned A') sp win victim newb v v'.

Let F1 := proj1 FR.
Let F2 := proj1 (proj2 FR).
Let F4 := proj1 (proj2 (proj2 (proj2 FR))).
Let F5 := proj1 (proj2 (proj2 (proj2 (proj2 FR)))).

(* [comment removed for export] *)
Definition avoids_call (a n : Z) : Prop :=
  (a + n <= sp - win \/ sp <= a) /\ (forall i, 0 <= i < n -> ~ victim (a + i)).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End Transport.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma newblock_cells : forall A' m' md' r n,
  ainv A' m' md' -> a_live A' r = Some n ->
  exists junk, length junk = Z.to_nat n /\ rw_cells segs (aview A' m') r [CB (Z.to_nat n) junk] /\ crange A' (aview A' m') r n.
Proof.
  intros A' m' md' r n AI' HL.
  (first [ pose proof ((as_live_ok L A' m' md' r n AI' HL)) as dR_10; dand8 dR_10 as N0 AL LO HI IMG MP NO _ | destruct (as_live_ok L A' m' md' r n AI' HL) as (N0 & AL & LO & HI & IMG & MP & NO & _) ]).
  change (aview_of (ahull A') m') with (aview A' m') in MP.
  pose proof layout_facts as LO'.
  unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in LO.   (* [comment removed for export] *)
  set (v' := aview A' m') in *.
  assert (G : forall i, 0 <= i < n -> exists b, v' (Z_to_bv 64 (r + i)) = Some b).
  { intros i Hi. specialize (MP i Hi). destruct (v' (Z_to_bv 64 (r + i))) as [b|]; [exists b; reflexivity| exfalso; apply MP; reflexivity]. }
  assert (REC : forall k, (k <= Z.to_nat n)%nat -> exists bs, length bs = k /\
            forall i, (i < k)%nat -> v' (Z_to_bv 64 (r + (n - Z.of_nat k) + Z.of_nat i)) = nth_error bs i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi. cbn in Hi. lia.
    - (first [ pose proof ((IH ltac:(lia))) as dR_11; dex1 dR_11 as bs; destruct dR_11 as [Lb Hbs] | pose proof ((IH ltac:(lia))) as dR_11; dand3 dR_11 as bs Lb Hbs | destruct (IH ltac:(lia)) as (bs & Lb & Hbs) ]). destruct (G (n - Z.of_nat (S k)) ltac:(lia)) as (b & Hb).
      exists (b :: bs). split; [cbn; lia|]. intros [|i] Hi.
      + cbn. rewrite <- Hb. f_equal. f_equal. lia.
      + cbn. rewrite <- (Hbs i ltac:(lia)). f_equal. f_equal. lia. }
  (first [ pose proof ((REC (Z.to_nat n) ltac:(lia))) as dR_12; dex1 dR_12 as junk; destruct dR_12 as [LJ HJ] | pose proof ((REC (Z.to_nat n) ltac:(lia))) as dR_12; dand3 dR_12 as junk LJ HJ | destruct (REC (Z.to_nat n) ltac:(lia)) as (junk & LJ & HJ) ]).
  exists junk. split; [exact LJ|]. split.
  - split.
    + split; [cbn; split; [exact LJ| exact I]|]. cbn [cells_bytes cbytes]. rewrite app_nil_r.
      split; [lia|]. split; [rewrite LJ; lia|]. intros i Hi. unfold mrd, wa.
      specialize (HJ i ltac:(rewrite LJ in Hi; exact Hi)).
      replace (r + (n - Z.of_nat (Z.to_nat n)) + Z.of_nat i) with (r + Z.of_nat i) in HJ by lia.
      rewrite HJ. destruct (nth_error junk i) eqn:E; [reflexivity|]. apply nth_error_None in E. rewrite LJ in Hi. lia.
    + cbn [cells_size csize Nat.add]. split; [lia|]. split; [lia|]. intros i Hi. unfold wview, wa.
      destruct (G i ltac:(lia)) as (b & Hb). rewrite Hb. discriminate.
  - split; [lia|]. split; [lia|]. intros i Hi. split; [apply NO; exact Hi|]. split; [lia|]. left. apply MP. exact Hi.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stk_mapped : forall v lo hi a n,
  stk segs v lo hi -> alloc_ceiling <= lo -> lo <= a -> a + n <= hi -> mapped v a n.
Proof.
  (intros v lo hi a n; (first [ intro dR_47; dand3 dR_47 as S0 S1 S | intros (S0 & S1 & S) ]); intros Hlo Ha Hn i Hi E).
  destruct (S (a + i) ltac:(lia)) as [W _]. apply W. unfold wview, wa. rewrite E.
  subst segs. pose proof layout_facts as LO.
  rewrite (as_find_segment_outside L (Z_to_bv 64 (a + i))); [reflexivity|]. unfold in_image. rewrite unsigned_lit; lia.
Qed.

(* [comment removed for export] *)

End Client.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition off_image (L : clayout) (a n : Z) : Prop := a + n <= cl_image_lo L \/ cl_image_hi L <= a.

Section CFrame.
  Context {Clg : Ceiling} (L : clayout) {AI : AsanAlloc L}.   (* [comment removed for export] *)
  Let segs := cl_segs L.

  Definition cframe (o o' : Z -> Prop) (sp win : Z) (V N : Z -> Prop) (v v' : mem) : Prop :=
       (forall a, 0 <= a < 2^64 -> ~ o a -> (v (Z_to_bv 64 a) <> None \/ in_image L a) ->
                  ~ (sp - win <= a < sp) -> ~ (cl_errno L <= a < cl_errno L + 4) -> ~ V a ->
                  v' (Z_to_bv 64 a) = v (Z_to_bv 64 a) /\ ~ o' a)
    /\ mapped v' (sp - win) win
    /\ (forall a, 0 <= a < 2^64 -> ~ (sp - win <= a < sp) -> ~ (cl_errno L <= a < cl_errno L + 4) ->
                  N a -> o a \/ V a \/ (v (Z_to_bv 64 a) = None /\ ~ in_image L a)).

  Lemma cframe_of_frame_ok : forall o o' sp win V N v v',
    frame_ok L o o' sp win V N v v' -> cframe o o' sp win V N v v'.
  Proof.
    (intros o o' sp win V N v v'; (first [ intro dR_48; dand7 dR_48 as F1 F2 F3 F4 F5 F6 F7 | intros (F1 & F2 & F3 & F4 & F5 & F6 & F7) ])). split; [|split; [exact F3|]].
    - intros a Ha NO VIS NW NE NV.
      assert (NO' : ~ o' a).
      { intros O'. destruct (F5 a Ha O') as [X|[X|[X [_ Hni]]]]; [exact (NO X)| exact (NV X)|].
        destruct VIS as [Y|Y]; [exact (Y X)| exact (Hni Y)]. }
      split; [|exact NO'].
      apply F1; [exact Ha| exact NO| exact NO'| exact NW| exact NE| exact NV|].
      intros NB. destruct (F4 a Ha NB) as [X|[X|[X [_ Hni]]]]; [exact (NO X)| exact (NV X)|].
      destruct VIS as [Y|Y]; [exact (Y X)| exact (Hni Y)].
    - intros a Ha NW NE NB. destruct (F4 a Ha NB) as [X|[X|[X [_ Hni]]]]; [left; exact X| right; left; exact X|].
      right; right. split; [exact X| exact Hni].
  Qed.

  Lemma cframe_weaken : forall o o' sp win win' (V V' N N' : Z -> Prop) v v',
    cframe o o' sp win V N v v' -> win <= win' -> mapped v' (sp - win') win' ->
    (forall a, V a -> V' a) -> (forall a, N' a -> N a) ->
    cframe o o' sp win' V' N' v v'.
  Proof.
    (intros o o' sp win win' V V' N N' v v'; (first [ intro dR_49; dand3 dR_49 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros Hw MAP HV HN). split; [|split; [exact MAP|]].
    - intros a Ha NO VIS NW NE NV. apply C1; [exact Ha| exact NO| exact VIS| lia| exact NE| intros X; apply NV, HV, X].
    - intros a Ha NW NE NB. destruct (C3 a Ha ltac:(lia) NE (HN a NB)) as [X|[X|X]]; [left; exact X| right; left; apply HV, X| right; right; exact X].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma cframe_stores : forall o sp win (V : Z -> Prop) v v0 (W : list (Z * Z)),
    munch W v v0 ->
    (forall a, 0 <= a < 2^64 -> ~ outside W a -> (sp - win <= a < sp) \/ V a) ->
    mapped v0 (sp - win) win ->
    cframe o o sp win V nowhere v v0.
  Proof.
    intros o sp win V v v0 W MU IN MAP. split; [|split; [exact MAP|]].
    - intros a Ha NO VIS NW NE NV. split; [|exact NO].
      apply (MU (Z_to_bv 64 a)). rewrite unsigned_lit by lia.
      destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso. destruct (IN a Ha X); tauto.
    - intros a _ _ _ X. destruct X.
  Qed.

  Lemma cframe_noalloc : forall o sp win (V N : Z -> Prop) v v0 (W : list (Z * Z)),
    munch W v v0 ->
    (forall a, 0 <= a < 2^64 -> ~ outside W a -> (sp - win <= a < sp) \/ V a) ->
    mapped v0 (sp - win) win ->
    (forall a, N a -> V a) ->
    cframe o o sp win V N v v0.
  Proof.
    intros o sp win V N v v0 W MU IN MAP NV.
    (first [ pose proof ((cframe_stores o sp win V v v0 W MU IN MAP)) as dR_13; dand3 dR_13 as C1 C2 _ | destruct (cframe_stores o sp win V v v0 W MU IN MAP) as (C1 & C2 & _) ]).
    split; [exact C1|]. split; [exact C2|]. intros a _ _ _ X. right; left. apply NV, X.
  Qed.

  (* [comment removed for export] *)
  Lemma cframe_extend :
    forall o o' (sp' win sp WIN : Z) (V V' N N' : Z -> Prop) (v v0 v' v'' : mem) (W1 W2 : list (Z * Z)),
      munch W1 v v0 ->
      (forall a, 0 <= a < 2^64 -> ~ outside W1 a -> (sp - WIN <= a < sp) \/ V' a) ->
      cframe o o' sp' win V N v0 v' ->
      sp - WIN <= sp' - win -> sp' <= sp ->
      (forall a, V a -> V' a) -> (forall a, N' a -> N a \/ V' a) ->
      munch W2 v' v'' ->
      (forall a, 0 <= a < 2^64 -> ~ outside W2 a -> (sp - WIN <= a < sp) \/ V' a \/ N a) ->
      mapped v'' (sp - WIN) WIN ->
      cframe o o' sp WIN V' N' v v''.
  Proof.
    (intros o o' sp' win sp WIN V V' N N' v v0 v' v'' W1 W2 MU1 IN1; (first [ intro dR_51; dand3 dR_51 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros Hlo Hhi HV HN MU2 IN2 MAP).
    split; [|split; [exact MAP|]].
    - intros a Ha NO VIS NW NE NV.
      assert (O1 : outside W1 a).
      { destruct (Classical_Prop.classic (outside W1 a)) as [X|X]; [exact X|]. exfalso. destruct (IN1 a Ha X); tauto. }
      assert (E1 : v0 (Z_to_bv 64 a) = v (Z_to_bv 64 a)).
      { apply (MU1 (Z_to_bv 64 a)). rewrite unsigned_lit by lia. exact O1. }
      destruct (C1 a Ha NO ltac:(rewrite E1; exact VIS) ltac:(lia) NE ltac:(intros X; apply NV, HV, X)) as [E2 NO'].
      assert (O2 : outside W2 a).
      { destruct (Classical_Prop.classic (outside W2 a)) as [X|X]; [exact X|]. exfalso.
        destruct (IN2 a Ha X) as [Y|[Y|Y]]; [tauto| tauto|].
        destruct (C3 a Ha ltac:(lia) NE Y) as [Z1|[Z1|[Z1 Z2]]]; [exact (NO Z1)| exact (NV (HV a Z1))|].
        rewrite E1 in Z1. destruct VIS as [U|U]; [exact (U Z1)| exact (Z2 U)]. }
      split; [|exact NO'].
      rewrite (MU2 (Z_to_bv 64 a)) by (rewrite unsigned_lit by lia; exact O2). rewrite E2. exact E1.
    - intros a Ha NW NE NB.
      destruct (HN a NB) as [HNa|HVa]; [| right; left; exact HVa].
      destruct (C3 a Ha ltac:(lia) NE HNa) as [X|[X|[X Y]]]; [left; exact X| right; left; apply HV, X|].
      destruct (Classical_Prop.classic (outside W1 a)) as [O1|O1].
      + right; right. split; [|exact Y]. rewrite <- (MU1 (Z_to_bv 64 a)); [exact X|]. rewrite unsigned_lit by lia. exact O1.
      + destruct (IN1 a Ha O1) as [Z1|Z1]; [lia| right; left; exact Z1].
  Qed.

  Lemma cframe_reframe : forall o o' sp' win' sp win V N v v',
    cframe o o' sp' win' V N v v' -> sp - win <= sp' - win' -> sp' <= sp ->
    mapped v' (sp - win) win ->
    cframe o o' sp win V N v v'.
  Proof.
    (intros o o' sp' win' sp win V N v v'; (first [ intro dR_52; dand3 dR_52 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros Hlo Hhi MAP). split; [|split; [exact MAP|]].
    - intros a Ha NO VIS NW NE NV. apply C1; [exact Ha| exact NO| exact VIS| lia| exact NE| exact NV].
    - intros a Ha NW NE NB. apply C3; [exact Ha| lia| exact NE| exact NB].
  Qed.

  Lemma cframe_seq : forall o o1 o2 sp w1 w2 W (V1 N1 V2 N2 V N : Z -> Prop) v v1 v2,
    cframe o o1 sp w1 V1 N1 v v1 -> cframe o1 o2 sp w2 V2 N2 v1 v2 ->
    w1 <= W -> w2 <= W -> mapped v2 (sp - W) W ->
    (forall a, V1 a -> V a) -> (forall a, V2 a -> N1 a \/ V a) -> (forall a, N a -> N1 a \/ N2 a \/ V a) ->
    cframe o o2 sp W V N v v2.
  Proof.
    (intros o o1 o2 sp w1 w2 W V1 N1 V2 N2 V N v v1 v2; (first [ intro dR_53; dand3 dR_53 as C1 C2 C3 | intros (C1 & C2 & C3) ]); (first [ intro dR_54; dand3 dR_54 as D1 D2 D3 | intros (D1 & D2 & D3) ]); intros Hw1 Hw2 MAP HV1 HV2 HN0).
    assert (HN : forall a, ~ V a -> N a -> N1 a \/ N2 a) by (intros a X Y; destruct (HN0 a Y) as [U|[U|U]]; tauto).
    split; [|split; [exact MAP|]].
    - intros a Ha NO VIS NW NE NV.
      destruct (C1 a Ha NO VIS ltac:(lia) NE ltac:(intros X; apply NV, HV1, X)) as [E1 NO1].
      assert (NV2 : ~ V2 a).
      { intros X. destruct (HV2 a X) as [Y|Y]; [|exact (NV Y)].
        destruct (C3 a Ha ltac:(lia) NE Y) as [Z1|[Z1|[Z1 Z2]]]; [exact (NO Z1)| exact (NV (HV1 a Z1))|].
        destruct VIS as [U|U]; [exact (U Z1)| exact (Z2 U)]. }
      destruct (D1 a Ha NO1 ltac:(rewrite E1; exact VIS) ltac:(lia) NE NV2) as [E2 NO2].
      split; [rewrite E2; exact E1| exact NO2].
    - intros a Ha NW NE NB.
      destruct (Classical_Prop.classic (o a)) as [O|NO]; [left; exact O|].
      destruct (Classical_Prop.classic (V a)) as [HVa|NVa]; [right; left; exact HVa|].
      destruct (Classical_Prop.classic (v (Z_to_bv 64 a) <> None \/ in_image L a)) as [VIS|NVIS].
      2:{ right; right. split; [| intros X; apply NVIS; right; exact X].
          destruct (v (Z_to_bv 64 a)); [exfalso; apply NVIS; left; discriminate| reflexivity]. }
      exfalso.
      destruct (C1 a Ha NO VIS ltac:(lia) NE ltac:(intros X; apply NVa, HV1, X)) as [E1 NO1].
      assert (N1X : ~ N1 a).
      { intros X. destruct (C3 a Ha ltac:(lia) NE X) as [Z1|[Z1|[Z1 Z2]]]; [exact (NO Z1)| exact (NVa (HV1 a Z1))|].
        destruct VIS as [U|U]; [exact (U Z1)| exact (Z2 U)]. }
      destruct (HN a NVa NB) as [X|X]; [exact (N1X X)|].
      destruct (D3 a Ha ltac:(lia) NE X) as [Z1|[Z1|[Z1 Z2]]]; [exact (NO1 Z1)| |].
      + destruct (HV2 a Z1) as [Y|Y]; [exact (N1X Y)| exact (NVa Y)].
      + rewrite E1 in Z1. destruct VIS as [U|U]; [exact (U Z1)| exact (Z2 U)].
  Qed.

  (* [comment removed for export] *)
  Section Transport.
    Variables (A A' : AS) (sp win : Z) (V N : Z -> Prop) (v v' : mem).
    Hypothesis CF : cframe (owned A) (owned A') sp win V N v v'.

    Lemma crange_csame : forall a n, crange A v a n -> avoids_call sp win V a n ->
      forall i, 0 <= i < n -> v' (Z_to_bv 64 (a + i)) = v (Z_to_bv 64 (a + i)).
    Proof.
      (intros a n; (first [ intro dR_55; dand3 dR_55 as H0 H1 H | intros (H0 & H1 & H) ]); intros [W HV] i Hi). (first [ pose proof ((H i Hi)) as dR_14; dand3 dR_14 as NO NE MP | destruct (H i Hi) as (NO & NE & MP) ]).
      destruct CF as (C1 & _ & _). apply (C1 (a + i)); [lia| exact NO| exact MP| lia| exact NE| apply HV; exact Hi].
    Qed.

    Lemma bytes_at_ccall : forall a bs, crange A v a (Z.of_nat (length bs)) -> avoids_call sp win V a (Z.of_nat (length bs)) ->
      bytes_at segs v a bs -> bytes_at segs v' a bs.
    Proof.
      (intros a bs C AV; (first [ intro dR_56; dand3 dR_56 as B0 B1 B | intros (B0 & B1 & B) ])). split; [exact B0|]. split; [exact B1|].
      intros i Hi. specialize (B i Hi). unfold mrd in *. unfold wa in *.
      rewrite (crange_csame a _ C AV (Z.of_nat i) ltac:(lia)). exact B.
    Qed.

    Lemma wr_at_ccall : forall a n, crange A v a n -> avoids_call sp win V a n -> wr_at segs v a n -> wr_at segs v' a n.
    Proof.
      (intros a n C AV; (first [ intro dR_57; dand3 dR_57 as W0 W1 W | intros (W0 & W1 & W) ])). split; [exact W0|]. split; [exact W1|].
      intros i Hi. specialize (W i Hi). unfold wview in *. unfold wa in *.
      rewrite (crange_csame a n C AV i Hi). exact W.
    Qed.

    Lemma rw_cells_ccall : forall a cs, crange A v a (Z.of_nat (cells_size cs)) -> avoids_call sp win V a (Z.of_nat (cells_size cs)) ->
      rw_cells segs v a cs -> rw_cells segs v' a cs.
    Proof.
      intros a cs C AV [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
      - apply bytes_at_ccall; [rewrite cells_bytes_length by exact Hwf; exact C| rewrite cells_bytes_length by exact Hwf; exact AV| exact HB].
      - apply wr_at_ccall; assumption.
    Qed.

    Lemma ro_cells_ccall : forall a cs, crange A v a (Z.of_nat (cells_size cs)) -> avoids_call sp win V a (Z.of_nat (cells_size cs)) ->
      ro_cells segs v a cs -> ro_cells segs v' a cs.
    Proof.
      intros a cs C AV [Hwf HB]. split; [exact Hwf|].
      apply bytes_at_ccall; [rewrite cells_bytes_length by exact Hwf; exact C| rewrite cells_bytes_length by exact Hwf; exact AV| exact HB].
    Qed.

    Lemma u8arr_ccall : forall a bs, crange A v a (Z.of_nat (length bs)) -> avoids_call sp win V a (Z.of_nat (length bs)) ->
      u8arr segs v a bs -> u8arr segs v' a bs.
    Proof.
      intros a bs C AV [HB HW]. split; [apply bytes_at_ccall; assumption| apply wr_at_ccall; assumption].
    Qed.

    Lemma crange_ccall : forall a n, crange A v a n -> avoids_call sp win V a n -> crange A' v' a n.
    Proof.
      intros a n C AV. (first [ pose proof (C) as dR_15; dand3 dR_15 as H0 H1 H | pose proof C as (H0 & H1 & H) ]). split; [exact H0|]. split; [exact H1|].
      intros i Hi. (first [ pose proof ((H i Hi)) as dR_16; dand3 dR_16 as NO NE MP | destruct (H i Hi) as (NO & NE & MP) ]). destruct AV as [W HV].
      destruct CF as (C1 & _ & _).
      destruct (C1 (a + i) ltac:(lia) NO MP ltac:(lia) NE (HV i Hi)) as [E NO'].
      split; [exact NO'|]. split; [exact NE|]. rewrite E. exact MP.
    Qed.

    Lemma newblock_cdisjoint : forall r n a k,
      (forall x, r <= x < r + n -> N x) ->
      crange A v a k -> avoids_call sp win V a k ->
      a + k <= r \/ r + n <= a \/ k <= 0 \/ n <= 0.
    Proof.
      (intros r n a k HN; (first [ intro dR_58; dand3 dR_58 as C0 C1' C | intros (C0 & C1' & C) ]); intros [W HV]).
      destruct CF as (C1 & C2 & C3).
      destruct (Z_lt_le_dec 0 k) as [Hk|Hk]; [|lia]. destruct (Z_lt_le_dec 0 n) as [Hn|Hn]; [|lia].
      destruct (Z_lt_le_dec (a + k) (r + 1)) as [|H1]; [lia|]. destruct (Z_lt_le_dec (r + n) (a + 1)) as [|H2]; [lia|].
      exfalso. set (x := Z.max a r).
      assert (Hxa : a <= x < a + k) by (unfold x; lia). assert (Hxr : r <= x < r + n) by (unfold x; lia).
      (first [ pose proof ((C (x - a) ltac:(lia))) as dR_17; dand3 dR_17 as NO NE MP | destruct (C (x - a) ltac:(lia)) as (NO & NE & MP) ]). replace (a + (x - a)) with x in * by lia.
      destruct (C3 x ltac:(lia) ltac:(lia) NE (HN x Hxr)) as [O|[HVx|[Hm Hni]]].
      - exact (NO O).
      - apply (HV (x - a) ltac:(lia)). replace (a + (x - a)) with x by lia. exact HVx.
      - destruct MP as [MP|MP]; [exact (MP Hm)| exact (Hni MP)].
    Qed.
  End Transport.

  Lemma stk_ccall : forall A A' m md v v' (sp win : Z) V N lo hi,
    ainv A m md -> cframe (owned A) (owned A') sp win V N v v' ->
    stk segs v lo hi -> alloc_ceiling <= lo -> lo <= sp - win -> sp <= hi ->
    (forall a, lo <= a < hi -> ~ V a) ->
    stk segs v' lo hi.
  Proof.
    (intros A A' m md v v' sp win V N lo hi AI0; (first [ intro dR_59; dand3 dR_59 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros ST Hlo Hw Hsp HV).
    (first [ dand3 ST as S0 S1 S | destruct ST as (S0 & S1 & S) ]). split; [exact S0|]. split; [exact S1|].
    pose proof layout_facts as LO.
    intros a Ha.
    assert (NO : ~ owned A a).
    { intros O. destruct (as_owned_where L A m md a AI0 O) as [Hs|[[_ Hlt] _]]; [apply (as_static_where L) in Hs; lia| lia]. }
    destruct (Classical_Prop.classic (sp - win <= a < sp)) as [Hin|Hout].
    - assert (Hm : v' (wa a) <> None).
      { unfold wa. replace a with (sp - win + (a - (sp - win))) by lia. apply C2. lia. }
      split.
      + unfold wview. destruct (v' (wa a)); [discriminate| exfalso; apply Hm; reflexivity].
      + unfold mrd. destruct (v' (wa a)) as [b|]; [exists b; reflexivity| exfalso; apply Hm; reflexivity].
    - destruct (S a Ha) as [W [b Hb']].
      assert (VISm : v (Z_to_bv 64 a) <> None).
      { intros E. unfold mrd, wa in Hb'. rewrite E in Hb'. subst segs.
        rewrite (as_seg_rom_outside L) in Hb'; [discriminate|]. unfold in_image. rewrite unsigned_lit by lia. lia. }
      destruct (C1 a ltac:(lia) NO (or_introl VISm) Hout ltac:(lia) (HV a Ha)) as [E _].
      split.
      + unfold wview, wa in *. rewrite E. exact W.
      + exists b. unfold mrd, wa in *. rewrite E. exact Hb'.
  Qed.
End CFrame.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section OwnStores.
  Context {Clg : Ceiling} (L : clayout) {AI : AsanAlloc L}.   (* [comment removed for export] *)
  Let segs := cl_segs L.

  (* [comment removed for export] *)
  Fixpoint client_fp (A : AS) (v : mem) (W : list (Z * Z)) : Prop :=
    match W with
    | [] => True
    | (lo, hi) :: W' => (alloc_ceiling <= lo /\ hi <= 2^64 /\ mapped v lo (hi - lo)
                         \/ (exists p n, a_live A p = Some n /\ p <= lo /\ hi <= p + n)
                         \/ (exists ff k age, a_frame A ff = Some (k, age) /\ ff <= lo /\ hi <= ff + fsize k - 8)
                         \/ (exists ff k age, a_frame A ff = Some (k, age) /\ sh ff <= lo /\ hi <= sh ff + fsize k / 8))
                        /\ client_fp A v W'
    end.

  Lemma client_fp_cases : forall A v W a,
    client_fp A v W -> ~ outside W a ->
    (alloc_ceiling <= a < 2^64 /\ v (Z_to_bv 64 a) <> None)
    \/ (exists p n, a_live A p = Some n /\ p <= a < p + n)
    \/ (exists ff k age, a_frame A ff = Some (k, age) /\ ff <= a < ff + fsize k - 8)
    \/ (exists ff k age, a_frame A ff = Some (k, age) /\ sh ff <= a < sh ff + fsize k / 8).
  Proof.
    intros A v W a CF NO. induction W as [|[lo hi] W IH]; cbn in *; [tauto|].
    destruct CF as [HW CF].
    assert (CASE : (lo <= a < hi) \/ ~ outside W a) by tauto.
    destruct CASE as [Hin|Hrest]; [|apply IH; assumption].
    destruct HW as [(Hc & Hh & HM)|[(p & n & HL & Hp & Hn)|[(ff & k & age & HF & H1 & H2)|(ff & k & age & HF & H1 & H2)]]].
    - left. split; [lia|]. replace a with (lo + (a - lo)) by lia. apply HM. lia.
    - right; left. exists p, n. split; [exact HL|lia].
    - right; right; left. exists ff, k, age. split; [exact HF| lia].
    - right; right; right. exists ff, k, age. split; [exact HF| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma client_fp_facts : forall A m md W a,
    ainv A m md -> client_fp A (aview A m) W -> ~ outside W a ->
    ~ owned A a /\ ~ cl_shared L a /\ ~ in_image L a /\ 0 <= a < 2^64 /\ aview A m (Z_to_bv 64 a) <> None.
  Proof.
    intros A m md W a AI0 CF NO. pose proof layout_facts as LO.
    destruct (client_fp_cases A _ W a CF NO) as [[Hc HM]|[(p & n & HL & Hp)|[(ff & k & age & HF & H1)|(ff & k & age & HF & H1)]]].
    - split; [|split; [|split; [|split; [lia|exact HM]]]].
      + intros O. destruct (as_owned_where L A m md a AI0 O) as [Hs|[[Hge Hlt] Hni]]; [apply (as_static_where L) in Hs; lia| lia].
      + intros Sh. apply (as_shared_where L) in Sh. lia.
      + unfold in_image. lia.
    - (first [ pose proof ((as_live_ok L A m md p n AI0 HL)) as dR_19; dand8 dR_19 as N0 AL PLO PHI IMG MP NOW _ | destruct (as_live_ok L A m md p n AI0 HL) as (N0 & AL & PLO & PHI & IMG & MP & NOW & _) ]).
      unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in PLO.   (* [comment removed for export] *)
      split; [|split; [|split; [|split; [lia|]]]].
      + replace a with (p + (a - p)) by lia. apply NOW. lia.
      + intros Sh. apply (as_shared_where L) in Sh. lia.
      + unfold in_image. lia.
      + replace a with (p + (a - p)) by lia. apply MP. lia.
    - (first [ pose proof ((as_frame_ok L A m md ff k age AI0 HF)) as dR_20; dand11 dR_20 as K0 AL PLO PHI IMG WR MP _ _ NOW _ | destruct (as_frame_ok L A m md ff k age AI0 HF) as (K0 & AL & PLO & PHI & IMG & WR & MP & _ & _ & NOW & _) ]).
      unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in PLO.   (* [comment removed for export] *)
      split; [|split; [|split; [|split; [lia|]]]].
      + replace a with (ff + (a - ff)) by lia. apply NOW. lia.
      + intros Sh. apply (as_shared_where L) in Sh. lia.
      + unfold in_image. lia.
      + replace a with (ff + (a - ff)) by lia. apply MP. lia.
    - (first [ pose proof ((as_frame_ok L A m md ff k age AI0 HF)) as dR_21; dand11 dR_21 as K0 AL PLO PHI IMG _ _ WR MP _ NOW | destruct (as_frame_ok L A m md ff k age AI0 HF) as (K0 & AL & PLO & PHI & IMG & _ & _ & WR & MP & _ & NOW) ]).
      unfold app_range, app_lo, app_hi, kLowAppEnd, kLowShadowMapBeg, kHighMemBeg in PLO. (first [ dand3 WR as W0 W1 _ | destruct WR as (W0 & W1 & _) ]).
      assert (0 <= ff / 8) by (apply Z.div_pos; lia).
      split; [|split; [|split; [|split; [unfold sh, kShadowOffset in *; lia|]]]].
      + replace a with (sh ff + (a - sh ff)) by lia. apply NOW. lia.
      + intros Sh. apply (as_shared_where L) in Sh. unfold sh, kShadowOffset in *. lia.
      + unfold in_image, sh, kShadowOffset in *. lia.
      + replace a with (sh ff + (a - sh ff)) by lia. apply MP. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma aview_recombine : forall A m (v' : mem),
    (forall a, hidc (ahull A) a = true -> v' a = None) ->
    aview A (munrestrict (hidc (ahull A)) m v') = v'.
  Proof.
    intros A m v' HC. unfold aview, aview_of. rewrite mrestrict_munrestrict. apply mrestrict_clean_id. exact HC.
  Qed.

  (* [comment removed for export] *)
  Theorem ainv_munch : forall A m md md' (v' : mem) (W : list (Z * Z)),
    ainv A m md ->
    munch W (aview A m) v' -> wmono segs (aview A m) v' ->
    client_fp A (aview A m) W ->
    (forall a, hidc (ahull A) a = true -> v' a = None) ->
    MInv (ahull A) (alhull A) (aeager A) md' -> same_but_materialized md md' ->
    ainv A (munrestrict (hidc (ahull A)) m v') md'.
  Proof.
    intros A m md md' v' W AI0 MU WM CF HC MI SB.
    set (m1 := munrestrict (hidc (ahull A)) m v').
    assert (EV : aview_of (ahull A) m1 = v') by (apply aview_recombine; exact HC).
    pose proof layout_facts as LO.
    (* [comment removed for export] *)
    assert (EQ : forall a, 0 <= a < 2^64 -> outside W a -> v' (Z_to_bv 64 a) = aview A m (Z_to_bv 64 a)).
    { intros a Ha Ho. apply (MU (Z_to_bv 64 a)). rewrite unsigned_lit by lia. exact Ho. }
    (* [comment removed for export] *)
    assert (EQo : forall a, (owned A a \/ cl_shared L a) -> v' (Z_to_bv 64 a) = aview A m (Z_to_bv 64 a)).
    { intros a Ho.
      assert (Ra : 0 <= a < 2^64).
      { destruct Ho as [O|Sh].
        - destruct (as_owned_where L A m md a AI0 O) as [Hs|[[Hge Hlt] Hni]]; [apply (as_static_where L) in Hs; lia| lia].
        - apply (as_shared_where L) in Sh. lia. }
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN]; [exact (EQ a Ra OUT)|].
      exfalso. (first [ pose proof ((client_fp_facts A m md W a AI0 CF NIN)) as dR_23; dand3 dR_23 as NO NS _ | destruct (client_fp_facts A m md W a AI0 CF NIN) as (NO & NS & _) ]). tauto. }
    apply (as_frame L A [] m m1 md md' AI0).
    - intros ff [].
    - constructor.
    - (* [comment removed for export] *)
      intros a Ha. unfold m1. apply munrestrict_hidden. exact Ha.
    - (* [comment removed for export] *)
      intros a O. left. rewrite EV. apply EQo. left; exact O.
    - (* [comment removed for export] *)
      intros ff k age fa [].
    - (* [comment removed for export] *)
      intros a Sh. rewrite EV. apply EQo. right; exact Sh.
    - (* [comment removed for export] *)
      intros a Ha Hni VIS. rewrite EV.
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN].
      + rewrite (EQ a Ha OUT). exact VIS.
      + (* [comment removed for export] *)
        specialize (WM (Z_to_bv 64 a)). unfold wview in WM. subst segs.
        rewrite (as_find_segment_outside L (Z_to_bv 64 a)) in WM by (rewrite unsigned_lit by lia; exact Hni).
        change (aview_of (ahull A) m) with (aview A m) in VIS.
        destruct (aview A m (Z_to_bv 64 a)); [|exfalso; apply VIS; reflexivity].
        destruct (v' (Z_to_bv 64 a)); [discriminate|]. exfalso. apply WM; [discriminate| reflexivity].
    - (* [comment removed for export] *)
      intros a Ha Hni VIS'. rewrite EV in VIS'. change (aview_of (ahull A) m) with (aview A m).
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN].
      + rewrite <- (EQ a Ha OUT). exact VIS'.
      + (first [ pose proof ((client_fp_facts A m md W a AI0 CF NIN)) as dR_24; dand5 dR_24 as _ _ _ _ VIS | destruct (client_fp_facts A m md W a AI0 CF NIN) as (_ & _ & _ & _ & VIS) ]). exact VIS.
    - exact MI.
    - exact SB.
  Qed.

  (* [comment removed for export] *)
  Definition flag_ivl (A : AS) (rel : list Z) (v : mem) (lo hi : Z) : Prop :=
    exists ff k age (faw : word), In ff rel /\ a_frame A ff = Some (k, age) /\
      bytes_at segs v (ff + fsize k - 8) (le8 faw) /\ lo = bv_unsigned faw /\ hi = bv_unsigned faw + 1.

  Fixpoint client_fp_rel (A : AS) (rel : list Z) (v : mem) (W : list (Z * Z)) : Prop :=
    match W with
    | [] => True
    | (lo, hi) :: W' => (alloc_ceiling <= lo /\ hi <= 2^64 /\ mapped v lo (hi - lo)
                         \/ (exists p n, a_live A p = Some n /\ p <= lo /\ hi <= p + n)
                         \/ (exists ff k age, a_frame A ff = Some (k, age) /\ ff <= lo /\ hi <= ff + fsize k - 8)
                         \/ (exists ff k age, a_frame A ff = Some (k, age) /\ sh ff <= lo /\ hi <= sh ff + fsize k / 8)
                         \/ flag_ivl A rel v lo hi)
                        /\ client_fp_rel A rel v W'
    end.

  (* [comment removed for export] *)

  Lemma client_fp_rel_cases : forall A rel v W a,
    client_fp_rel A rel v W -> ~ outside W a ->
    (alloc_ceiling <= a < 2^64 /\ v (Z_to_bv 64 a) <> None)
    \/ (exists p n, a_live A p = Some n /\ p <= a < p + n)
    \/ (exists ff k age, a_frame A ff = Some (k, age) /\ ff <= a < ff + fsize k - 8)
    \/ (exists ff k age, a_frame A ff = Some (k, age) /\ sh ff <= a < sh ff + fsize k / 8)
    \/ (exists ff k age (faw : word), In ff rel /\ a_frame A ff = Some (k, age) /\
          bytes_at segs v (ff + fsize k - 8) (le8 faw) /\ a = bv_unsigned faw).
  Proof.
    intros A rel v W a CF NO. induction W as [|[lo hi] W IH]; cbn in *; [tauto|].
    destruct CF as [HW CF].
    assert (CASE : (lo <= a < hi) \/ ~ outside W a) by tauto.
    destruct CASE as [Hin|Hrest]; [|apply IH; assumption].
    destruct HW as [(Hc & Hh & HM)|[(p & n & HL & Hp & Hn)|[(ff & k & age & HF & H1 & H2)|[(ff & k & age & HF & H1 & H2)|(ff & k & age & faw & IN & HF & FB & -> & ->)]]]].
    - left. split; [lia|]. replace a with (lo + (a - lo)) by lia. apply HM. lia.
    - right; left. exists p, n. split; [exact HL|lia].
    - right; right; left. exists ff, k, age. split; [exact HF| lia].
    - right; right; right; left. exists ff, k, age. split; [exact HF| lia].
    - right; right; right; right. exists ff, k, age, faw. split; [exact IN|]. split; [exact HF|]. split; [exact FB|]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_at_same : forall (v : mem) a bs1 bs2,
    bytes_at segs v a bs1 -> bytes_at segs v a bs2 -> length bs1 = length bs2 -> bs1 = bs2.
  Proof.
    (intros v a bs1 bs2; (first [ intro dR_60; dand3 dR_60 as _ _ H1 | intros (_ & _ & H1) ]); (first [ intro dR_61; dand3 dR_61 as _ _ H2 | intros (_ & _ & H2) ]); intros HL). apply nth_error_ext. intros i.
    destruct (Nat.lt_ge_cases i (length bs1)) as [LT|GE].
    - rewrite <- (H1 i LT). apply H2. lia.
    - rewrite (proj2 (nth_error_None bs1 i)) by lia. rewrite (proj2 (nth_error_None bs2 i)) by lia. reflexivity.
  Qed.

  Lemma le8_inj : forall w1 w2 : word, le8 w1 = le8 w2 -> w1 = w2.
  Proof. intros w1 w2 E. rewrite <- (le_bytes_to_word_le8 w1), <- (le_bytes_to_word_le8 w2), E. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma flag_facts : forall A m md ff k age (faw : word),
    ainv A m md -> a_frame A ff = Some (k, age) ->
    bytes_at segs (aview A m) (ff + fsize k - 8) (le8 faw) ->
    owned A (bv_unsigned faw) /\ ~ cl_shared L (bv_unsigned faw) /\ ~ in_image L (bv_unsigned faw)
    /\ aview A m (Z_to_bv 64 (bv_unsigned faw)) <> None
    /\ (forall fa', bytes_at segs (aview A m) (ff + fsize k - 8) (le8 (Z_to_bv 64 fa')) -> 0 <= fa' < 2^64 -> fa' = bv_unsigned faw).
  Proof.
    intros A m md ff k age faw AI0 HF FB. pose proof layout_facts as LO.
    assert (UNIQ : forall fa', bytes_at segs (aview A m) (ff + fsize k - 8) (le8 (Z_to_bv 64 fa')) -> 0 <= fa' < 2^64 -> fa' = bv_unsigned faw).
    { intros fa' FB' R. pose proof (bytes_at_same _ _ _ _ FB' FB ltac:(rewrite !length_le8; reflexivity)) as EQ.
      apply le8_inj in EQ. rewrite <- EQ. rewrite unsigned_lit by lia. reflexivity. }
    (first [ pose proof ((as_sframe_flag L A m md ff k age AI0 HF)) as dR_25; dex1 dR_25 as fa'; dand5 dR_25 as FB' OW NI WR _ | pose proof ((as_sframe_flag L A m md ff k age AI0 HF)) as dR_25; dand6 dR_25 as fa' FB' OW NI WR _ | destruct (as_sframe_flag L A m md ff k age AI0 HF) as (fa' & FB' & OW & NI & WR & _) ]).
    (first [ dand3 WR as W0 W1 W2 | destruct WR as (W0 & W1 & W2) ]).
    pose proof (UNIQ fa' FB' ltac:(lia)) as E. subst fa'.
    split; [exact OW|]. split.
    - intros SH. destruct (as_owned_where L A m md _ AI0 OW) as [ST|[HZ NI']].
      + exact (as_shared_not_static L _ SH ST).
      + apply (as_shared_where L) in SH. apply NI'. unfold in_image. lia.
    - split; [exact NI|]. split; [|exact UNIQ].
      specialize (W2 0 ltac:(lia)). rewrite Z.add_0_r in W2. unfold wview in W2.
      change (aview_of (ahull A) m) with (aview A m) in W2. unfold wa in W2.
      destruct (aview A m (Z_to_bv 64 (bv_unsigned faw))) eqn:Ev; [discriminate|].
      subst segs. rewrite (as_find_segment_outside L) in W2; [exact W2|]. rewrite unsigned_lit by lia. exact NI.
  Qed.

  (* [comment removed for export] *)
  Lemma flag_cell_rw : forall A m md ff k age (faw : word),
    ainv A m md -> a_frame A ff = Some (k, age) ->
    bytes_at segs (aview A m) (ff + fsize k - 8) (le8 faw) ->
    exists b, Step.rw_cells segs (aview A m) (bv_unsigned faw) [C1 b].
  Proof.
    intros A m md ff k age faw AI0 HF FB.
    (first [ pose proof ((flag_facts A m md ff k age faw AI0 HF FB)) as dR_27; dand5 dR_27 as OW NS NI VIS UNIQ | destruct (flag_facts A m md ff k age faw AI0 HF FB) as (OW & NS & NI & VIS & UNIQ) ]).
    (first [ pose proof ((as_sframe_flag L A m md ff k age AI0 HF)) as dR_28; dex1 dR_28 as fa'; dand5 dR_28 as FB' _ _ WR _ | pose proof ((as_sframe_flag L A m md ff k age AI0 HF)) as dR_28; dand6 dR_28 as fa' FB' _ _ WR _ | destruct (as_sframe_flag L A m md ff k age AI0 HF) as (fa' & FB' & _ & _ & WR & _) ]).
    (first [ pose proof (WR) as dR_29; dand3 dR_29 as W0 W1 _ | pose proof WR as (W0 & W1 & _) ]). rewrite (UNIQ fa' FB' ltac:(lia)) in WR.
    destruct (aview A m (Z_to_bv 64 (bv_unsigned faw))) as [b|] eqn:Eb; [|exfalso; exact (VIS eq_refl)].
    pose proof (bv_unsigned_in_range 64 faw) as FR64. unfold bv_modulus in FR64.
    exists b. split; [|exact WR]. split; [exact (conj I I)|].
    split; [lia|]. split; [cbn [Cells.cells_bytes Cells.cbytes app length]; lia|].
    intros i Hi. cbn [Cells.cells_bytes Cells.cbytes app length] in Hi. destruct i; [|lia].
    cbn [Cells.cells_bytes Cells.cbytes app nth_error]. rewrite Z.add_0_r. unfold mrd, wa. rewrite Eb. reflexivity.
  Qed.

  Theorem ainv_munch_release : forall A (rel : list Z) m md md' (v' : mem) (W : list (Z * Z)),
    ainv A m md ->
    (forall ff, In ff rel -> exists k age, a_frame A ff = Some (k, age)) -> NoDup rel ->
    munch W (aview A m) v' -> wmono segs (aview A m) v' ->
    client_fp_rel A rel (aview A m) W ->
    (forall ff k age (faw : word), In ff rel -> a_frame A ff = Some (k, age) ->
        bytes_at segs (aview A m) (ff + fsize k - 8) (le8 faw) -> v' faw = Some (Z_to_bv 8 0)) ->
    (forall a, hidc (ahull A) a = true -> v' a = None) ->
    MInv (ahull A) (alhull A) (aeager A) md' -> same_but_materialized md md' ->
    ainv (fold_left a_release rel A) (munrestrict (hidc (ahull A)) m v') md'.
  Proof.
    intros A rel m md md' v' W AI0 REL ND MU WM CF FLAG HC MI SB.
    set (m1 := munrestrict (hidc (ahull A)) m v').
    assert (EV : aview_of (ahull A) m1 = v') by (apply aview_recombine; exact HC).
    pose proof layout_facts as LO.
    assert (EQ : forall a, 0 <= a < 2^64 -> outside W a -> v' (Z_to_bv 64 a) = aview A m (Z_to_bv 64 a)).
    { intros a Ha Ho. apply (MU (Z_to_bv 64 a)). rewrite unsigned_lit by lia. exact Ho. }
    (* [comment removed for export] *)
    assert (INW : forall a, ~ outside W a ->
              (~ owned A a /\ ~ cl_shared L a /\ ~ in_image L a /\ 0 <= a < 2^64 /\ aview A m (Z_to_bv 64 a) <> None)
              \/ (exists ff k age (faw : word), In ff rel /\ a_frame A ff = Some (k, age) /\
                    bytes_at segs (aview A m) (ff + fsize k - 8) (le8 faw) /\ a = bv_unsigned faw)).
    { intros a NIN.
      destruct (client_fp_rel_cases A rel _ W a CF NIN) as [C|[C|[C|[C|C]]]]; [left|left|left|left|right; exact C].
      - apply (client_fp_facts A m md [(a, a+1)] a AI0); cbn; [|lia]. split; [|exact I]. left. destruct C as [C1 C2].
        split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with a by lia. exact C2.
      - (first [ dex2 C as p n; destruct C as [HL Hp] | dand4 C as p n HL Hp | destruct C as (p & n & HL & Hp) ]). apply (client_fp_facts A m md [(a, a+1)] a AI0); cbn; [|lia]. split; [|exact I].
        right; left. exists p, n. split; [exact HL|lia].
      - (first [ dex3 C as ff k age; destruct C as [HF H1] | dand5 C as ff k age HF H1 | destruct C as (ff & k & age & HF & H1) ]). apply (client_fp_facts A m md [(a, a+1)] a AI0); cbn; [|lia]. split; [|exact I].
        right; right; left. exists ff, k, age. split; [exact HF|lia].
      - (first [ dex3 C as ff k age; destruct C as [HF H1] | dand5 C as ff k age HF H1 | destruct C as (ff & k & age & HF & H1) ]). apply (client_fp_facts A m md [(a, a+1)] a AI0); cbn; [|lia]. split; [|exact I].
        right; right; right. exists ff, k, age. split; [exact HF|lia]. }
    (* [comment removed for export] *)
    assert (EQs : forall a, cl_shared L a -> v' (Z_to_bv 64 a) = aview A m (Z_to_bv 64 a)).
    { intros a Sh. pose proof (as_shared_where L a Sh) as Ra.
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN]; [apply (EQ a); [lia|exact OUT]|].
      exfalso. destruct (INW a NIN) as [(NO & NS & _)|(ff & k & age & faw & IN & HF & FB & ->)]; [tauto|].
      (first [ pose proof ((flag_facts A m md ff k age faw AI0 HF FB)) as dR_33; dand3 dR_33 as _ NS _ | destruct (flag_facts A m md ff k age faw AI0 HF FB) as (_ & NS & _) ]). exact (NS Sh). }
    apply (as_frame L A rel m m1 md md' AI0 REL ND).
    - intros a Ha. unfold m1. apply munrestrict_hidden. exact Ha.
    - (* [comment removed for export] *)
      intros a O. rewrite EV.
      assert (Ra : 0 <= a < 2^64).
      { destruct (as_owned_where L A m md a AI0 O) as [Hs|[[Hge Hlt] Hni]]; [apply (as_static_where L) in Hs; lia| lia]. }
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN]; [left; exact (EQ a Ra OUT)|].
      destruct (INW a NIN) as [(NO & _)|(ff & k & age & faw & IN & HF & FB & ->)]; [tauto|].
      right. exists ff, k, age, (bv_unsigned faw). split; [exact IN|]. split; [exact HF|]. split; [reflexivity|].
      split; [rewrite Z_to_bv_bv_unsigned; exact FB|].
      rewrite Z_to_bv_bv_unsigned. exact (FLAG ff k age faw IN HF FB).
    - (* [comment removed for export] *)
      intros ff k age fa IN HF FB. rewrite EV.
      (first [ pose proof ((as_sframe_flag L A m md ff k age AI0 HF)) as dR_34; dex1 dR_34 as fa0; dand5 dR_34 as FB0 _ _ WR _ | pose proof ((as_sframe_flag L A m md ff k age AI0 HF)) as dR_34; dand6 dR_34 as fa0 FB0 _ _ WR _ | destruct (as_sframe_flag L A m md ff k age AI0 HF) as (fa0 & FB0 & _ & _ & WR & _) ]). (first [ dand3 WR as W0 W1 _ | destruct WR as (W0 & W1 & _) ]).
      change (aview_of (ahull A) m) with (aview A m) in FB, FB0.
      (first [ pose proof ((flag_facts A m md ff k age (Z_to_bv 64 fa0) AI0 HF ltac:(exact FB0))) as dR_36; dand5 dR_36 as _ _ _ _ UNIQ | destruct (flag_facts A m md ff k age (Z_to_bv 64 fa0) AI0 HF ltac:(exact FB0)) as (_ & _ & _ & _ & UNIQ) ]).
      pose proof (UNIQ fa FB) as Efa.
      pose proof (bytes_at_same _ _ _ _ FB FB0 ltac:(rewrite !length_le8; reflexivity)) as EQ8. apply le8_inj in EQ8.
      rewrite EQ8. exact (FLAG ff k age (Z_to_bv 64 fa0) IN HF FB0).
    - intros a Sh. rewrite EV. apply EQs. exact Sh.
    - (* [comment removed for export] *)
      intros a Ha Hni VIS. rewrite EV.
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN].
      + rewrite (EQ a Ha OUT). exact VIS.
      + specialize (WM (Z_to_bv 64 a)). unfold wview in WM. change segs with (cl_segs L) in WM.
        rewrite (as_find_segment_outside L (Z_to_bv 64 a)) in WM by (rewrite unsigned_lit by lia; exact Hni).
        change (aview_of (ahull A) m) with (aview A m) in VIS.
        destruct (aview A m (Z_to_bv 64 a)); [|exfalso; apply VIS; reflexivity].
        destruct (v' (Z_to_bv 64 a)); [discriminate|]. exfalso. apply WM; [discriminate| reflexivity].
    - (* [comment removed for export] *)
      intros a Ha Hni VIS'. rewrite EV in VIS'. change (aview_of (ahull A) m) with (aview A m).
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN].
      + rewrite <- (EQ a Ha OUT). exact VIS'.
      + destruct (INW a NIN) as [(_ & _ & _ & _ & V)|(ff & k & age & faw & IN & HF & FB & ->)]; [exact V|].
        (first [ pose proof ((flag_facts A m md ff k age faw AI0 HF FB)) as dR_37; dand5 dR_37 as _ _ _ V _ | destruct (flag_facts A m md ff k age faw AI0 HF FB) as (_ & _ & _ & V & _) ]). exact V.
    - exact MI.
    - exact SB.
  Qed.

  (* [comment removed for export] *)
  Lemma aview_release1 : forall A m md ff k age m1,
    ainv A m md -> a_frame A ff = Some (k, age) -> aview (a_release A ff) m1 = aview A m1.
  Proof.
    intros A m md ff k age m1 AI0 HF. unfold aview.
    (first [ pose proof ((as_release_spec L A m md ff k age AI0 HF)) as dR_38; dand10 dR_38 as _ _ _ _ _ _ _ _ HH _ | destruct (as_release_spec L A m md ff k age AI0 HF) as (_ & _ & _ & _ & _ & _ & _ & _ & HH & _) ]). rewrite HH. reflexivity.   (* [comment removed for export] *)
  Qed.
End OwnStores.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma amd_frame_sbm : forall md md', same_but_materialized md md' -> m_halted md = None -> amd_frame md md'.
Proof.
  intros md md' SB Hh. unfold same_but_materialized in SB. unfold amd_frame. rewrite SB.
  unfold with_vm_backing. destruct md as [fd [maps lazy mat] io fs proc lim tm sc sg]; cbn.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try reflexivity. unfold m_halted in *. cbn in *. exact Hh.
Qed.

Lemma amd_frame_sbm_l : forall md0 md md', same_but_materialized md0 md -> m_halted md0 = None ->
  amd_frame md md' -> amd_frame md0 md'.
Proof. intros md0 md md' SB Hh AF. eapply amd_frame_trans; [apply amd_frame_sbm; eassumption | exact AF]. Qed.

Lemma amd_frame_sbm_r : forall md md' md'', amd_frame md md' -> same_but_materialized md' md'' ->
  amd_frame md md''.
Proof.
  intros md md' md'' AF SB. eapply amd_frame_trans; [exact AF | apply amd_frame_sbm; [exact SB|]].
  unfold amd_frame in AF. tauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Geom.
  Context {Clg : Ceiling} (L : clayout) {AI : AsanAlloc L}.   (* [comment removed for export] *)
  Let segs := cl_segs L.

  Lemma off_image_sub : forall a n a' n', off_image L a n -> a <= a' -> a' + n' <= a + n -> off_image L a' n'.
  Proof. unfold off_image. intros. lia. Qed.
  Lemma off_image_stack : forall a n, alloc_ceiling <= a -> off_image L a n.
  Proof. unfold off_image. intros. pose proof layout_facts. right. lia. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma off_image_app : forall a n, app_range L a n -> off_image L a n.
  Proof.
    unfold off_image, app_range, app_lo, app_hi. intros a n H. pose proof layout_facts. unfold kHighMemBeg in *. lia.
  Qed.
  Lemma app_range_pos : forall a n, app_range L a n -> 4096 <= a /\ 0 <= n /\ a + n <= alloc_ceiling.
  Proof.
    unfold app_range, app_lo, app_hi, kLowAppEnd. intros a n H. pose proof layout_facts. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma app_shadow_apart : forall a n, app_range L a n -> shadow_apart a n.
  Proof.
    unfold app_range, app_lo, app_hi, shadow_apart, kLowAppEnd, sh. intros a n H. pose proof layout_facts.
    unfold kLowShadowMapBeg, kHighMemBeg, kShadowOffset in *. Z.div_mod_to_equations. lia.
  Qed.
  Lemma app_noshadow_of : forall a n, app_range L a n -> app_noshadow a n.
  Proof. unfold app_range, app_lo, app_hi, app_noshadow, kLowAppEnd. intros a n H. lia. Qed.
  Lemma off_image_shadow : forall a n, 0 <= a -> off_image L (sh a) n.
  Proof.
    unfold off_image. intros a n Ha. pose proof layout_facts. unfold sh, kShadowOffset in *.
    right. pose proof (Z.div_pos a 8 Ha ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma live_geom : forall A m md p n, ainv A m md -> a_live A p = Some n ->
    0 <= n < REQ_MAX /\ p mod 16 = 0 /\ app_range L p n /\ p + n <= alloc_ceiling /\ off_image L p n /\
    mapped (aview A m) p n /\ (forall i, 0 <= i < n -> ~ owned A (p + i)).
  Proof.
    intros A m md p n AI0 LV. (first [ pose proof ((as_live_ok L A m md p n AI0 LV)) as dR_39; dand8 dR_39 as A1 A2 A3 A4 A5 A6 A7 _ | destruct (as_live_ok L A m md p n AI0 LV) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & _) ]).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
    split; [apply off_image_app; exact A3|]. split; [exact A6| exact A7].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma fframe_geom : forall A m md ff k age, ainv A m md -> a_frame A ff = Some (k, age) ->
    0 <= k <= 10 /\ 64 <= fsize k <= 65536 /\ app_range L ff (fsize k) /\ ff + fsize k <= alloc_ceiling /\
    off_image L ff (fsize k) /\ off_image L (sh ff) (fsize k / 8) /\
    mapped (aview A m) ff (fsize k) /\ mapped (aview A m) (sh ff) (fsize k / 8) /\
    wr_at segs (aview A m) ff (fsize k - 8) /\ wr_at segs (aview A m) (sh ff) (fsize k / 8).
  Proof.
    intros A m md ff k age AI0 HF.
    (first [ pose proof ((as_frame_ok L A m md ff k age AI0 HF)) as dR_40; dand11 dR_40 as K0 AL PLO PHI IMG WR MP WRS MPS _ _ | destruct (as_frame_ok L A m md ff k age AI0 HF) as (K0 & AL & PLO & PHI & IMG & WR & MP & WRS & MPS & _ & _) ]).
    assert (FS : 64 <= fsize k <= 65536).
    { unfold fsize. split.
      - pose proof (Z.pow_le_mono_r 2 0 k ltac:(lia) ltac:(lia)). rewrite Z.pow_0_r in H. lia.
      - pose proof (Z.pow_le_mono_r 2 k 10 ltac:(lia) ltac:(lia)). change (2 ^ 10) with 1024 in H. lia. }
    change (aview_of (ahull A) m) with (aview A m) in WR, MP, WRS, MPS.
    split; [exact K0|]. split; [exact FS|]. split; [exact PLO|]. split; [exact PHI|].
    split; [apply off_image_app; exact PLO|]. split; [apply off_image_shadow; pose proof (app_range_pos _ _ PLO); lia|].
    split; [exact MP|]. split; [exact MPS|]. split; [exact WR| exact WRS].
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_mapped : forall v a cs,
    rw_cells segs v a cs -> off_image L a (Z.of_nat (cells_size cs)) ->
    mapped v a (Z.of_nat (cells_size cs)).
  Proof.
    unfold off_image. intros v a cs [_ (W0 & W1 & W)] Ha i Hi E.
    specialize (W i Hi). unfold wview, wa in W. rewrite E in W.
    subst segs. rewrite (as_find_segment_outside L) in W; [exact (W eq_refl)|].
    unfold in_image. rewrite unsigned_lit; lia.
  Qed.
  Lemma u8arr_mapped : forall v a bs,
    u8arr segs v a bs -> off_image L a (Z.of_nat (length bs)) ->
    mapped v a (Z.of_nat (length bs)).
  Proof.
    unfold off_image. intros v a bs [_ (W0 & W1 & W)] Ha i Hi E.
    specialize (W i Hi). unfold wview, wa in W. rewrite E in W.
    subst segs. rewrite (as_find_segment_outside L) in W; [exact (W eq_refl)|].
    unfold in_image. rewrite unsigned_lit; lia.
  Qed.
  Lemma bytes_at_mapped : forall v a bs,
    bytes_at segs v a bs -> off_image L a (Z.of_nat (length bs)) ->
    mapped v a (Z.of_nat (length bs)).
  Proof.
    unfold off_image. (intros v a bs; (first [ intro dR_62; dand3 dR_62 as B0 B1 B | intros (B0 & B1 & B) ]); intros Ha i Hi E).
    specialize (B (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in B by lia.
    unfold mrd, wa in B. rewrite E in B. subst segs.
    rewrite (as_seg_rom_outside L) in B by (unfold in_image; rewrite unsigned_lit; lia).
    destruct (nth_error bs (Z.to_nat i)) eqn:En; [discriminate|]. apply nth_error_None in En. lia.
  Qed.
  Lemma wr_at_mapped : forall v a n,
    wr_at segs v a n -> off_image L a n -> mapped v a n.
  Proof.
    unfold off_image. (intros v a n; (first [ intro dR_63; dand3 dR_63 as W0 W1 W | intros (W0 & W1 & W) ]); intros Ha i Hi E).
    specialize (W i Hi). unfold wview, wa in W. rewrite E in W.
    subst segs. rewrite (as_find_segment_outside L) in W; [exact (W eq_refl)|].
    unfold in_image. rewrite unsigned_lit; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma window_mapped : forall v lo a sp W cs,
    stk segs v lo a -> rw_cells segs v a cs -> a + Z.of_nat (cells_size cs) = sp ->
    alloc_ceiling <= lo -> lo <= sp - W -> sp - W <= a -> mapped v (sp - W) W.
  Proof.
    intros v lo a sp W cs ST FR SZ CE LO HA i Hi.
    pose proof layout_facts as LAY.
    destruct (Z_lt_le_dec (sp - W + i) a) as [Hb|Hb].
    - apply (stk_mapped (L:=L) v lo a (sp - W) (a - (sp - W)) ST CE ltac:(lia) ltac:(lia)). lia.
    - pose proof (rw_cells_mapped v a cs FR ltac:(apply off_image_stack; lia)) as M.
      replace (sp - W + i) with (a + (sp - W + i - a)) by lia. apply M. lia.
  Qed.

  Lemma mapped_sub : forall (v : mem) a n a' n', mapped v a n -> a <= a' -> a' + n' <= a + n -> mapped v a' n'.
  Proof. intros v a n a' n' H H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia. Qed.

  (* [comment removed for export] *)
  Definition cvar (A : AS) (sp : Z) (excl : list Z) (a n : Z) : Prop :=
    (alloc_ceiling <= a /\ sp <= a /\ a + n <= 2^64) \/
    (exists p k, a_live A p = Some k /\ ~ In p excl /\ p <= a /\ a + n <= p + k) \/
    (exists ff k age, a_frame A ff = Some (k, age) /\ ff <= a /\ a + n <= ff + fsize k - 8).

  (* [comment removed for export] *)
End Geom.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac fold_cl_segs :=
  repeat match goal with
  | H : context [cl_segs ?L] |- _ => let v := eval cbv beta iota delta [cl_segs L] in (cl_segs L) in change (cl_segs L) with v in H
  | |- context [cl_segs ?L] => let v := eval cbv beta iota delta [cl_segs L] in (cl_segs L) in change (cl_segs L) with v
  end.
Ltac fold_aview :=
  repeat match goal with
  | H : context [aview_of (@ahull ?C ?L ?AI ?A) ?m] |- _ => change (aview_of (@ahull C L AI A) m) with (@aview C L AI A m) in H   (* [comment removed for export] *)
  | |- context [aview_of (@ahull ?C ?L ?AI ?A) ?m] => change (aview_of (@ahull C L AI A) m) with (@aview C L AI A m)
  end.
(* [comment removed for export] *)
Ltac fix_ret_pc :=
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?z)] => rewrite (ret_pc_even z) by first [lia | reflexivity]
  end.

Ltac acall_consts := unfold ASTK in *.
Ltac avoids_solve :=
  cbn [Cells.cells_size Cells.csize Nat.add length app];
  split; [ lia | intros ? ? X; unfold newblk, frm in X; unfold blk, nowhere in X; cbn beta in X; lia ].

(* [comment removed for export] *)
Ltac acall_xfer FRK :=
  acall_consts;
  lazymatch type of FRK with
  | frame_ok ?L _ _ _ _ _ _ _ _ => apply (cframe_of_frame_ok L) in FRK
  | _ => idtac
  end;
  lazymatch type of FRK with
  | cframe ?L (owned ?A) (owned ?A') ?sp ?win ?V ?N ?v ?v' =>
    repeat match goal with
    | H : Step.rw_cells ?segs v ?a ?cs |- _ =>
        first [ match goal with C : crange A v _ _ |- _ =>
                  apply (rw_cells_ccall L A A' sp win V N v v' FRK a cs) in H;
                  [ | exact C | avoids_solve ] end
              | idtac "note: dropping hypothesis (call):" H; clear H ]
    | H : Step.ro_cells ?segs v ?a ?cs |- _ =>
        first [ match goal with C : crange A v _ _ |- _ =>
                  apply (ro_cells_ccall L A A' sp win V N v v' FRK a cs) in H;
                  [ | exact C | avoids_solve ] end
              | idtac "note: dropping hypothesis (call):" H; clear H ]
    | H : bytes_at ?segs v ?a ?bs |- _ =>
        first [ match goal with C : crange A v _ _ |- _ =>
                  apply (bytes_at_ccall L A A' sp win V N v v' FRK a bs) in H;
                  [ | exact C | avoids_solve ] end
              | idtac "note: dropping hypothesis (call):" H; clear H ]
    | H : Arr.u8arr ?segs v ?a ?bs |- _ =>
        first [ match goal with C : crange A v _ _ |- _ =>
                  apply (u8arr_ccall L A A' sp win V N v v' FRK a bs) in H;
                  [ | exact C | avoids_solve ] end
              | idtac "note: dropping hypothesis (call):" H; clear H ]
    | H : stk ?segs v ?lo ?hi |- _ =>
        first [ match goal with AI0 : ainv A ?m ?md |- _ =>
                  apply (stk_ccall L A A' m md v v' sp win V N lo hi AI0 FRK) in H;
                  [ | lia | lia | lia | intros ? ? X; unfold newblk, frm in X; unfold blk, nowhere in X; cbn beta in X; lia ] end
              | idtac "note: dropping hypothesis (call):" H; clear H ]
    | H : mem_inv ?segs v |- _ => clear H
    end;
    repeat match goal with
    | C : crange A v ?a ?n |- _ =>
        first [ apply (crange_ccall L A A' sp win V N v v' FRK a n) in C; [ | avoids_solve ]
              | clear C ]
    end
  end.

(* [comment removed for export] *)
Ltac off_image_solve L :=
  cbn [Cells.cells_size Cells.csize Nat.add length app]; try rewrite !Arr.upd_length;
  first [ assumption
        | apply (@off_image_stack L _); lia
        | match goal with H : off_image _ _ _ |- _ => apply (off_image_sub L _ _ _ _ H); cbn [Cells.cells_size Cells.csize Nat.add length app]; lia end ].

Ltac prove_mapped1 :=
  first [ match goal with H : mapped ?m ?a ?n |- mapped ?m ?a ?n' => apply (mapped_sub _ m a n a n' H); lia end
        | match goal with H : mapped ?m ?a ?n |- mapped ?m ?a' ?n' => apply (mapped_sub _ m a n a' n' H); lia end ].

(* [comment removed for export] *)
Ltac pose_mapped L vx :=
  repeat match goal with
  | H : Step.rw_cells ?segs vx ?a ?cs |- _ =>
      lazymatch goal with
      | _ : mapped vx a _ |- _ => fail
      | _ => let M := fresh "MAP" in
             pose proof (rw_cells_mapped L vx a cs H ltac:(off_image_solve L)) as M;
             cbn [Cells.cells_size Cells.csize Nat.add length app] in M
      end
  | H : Arr.u8arr ?segs vx ?a ?bs |- _ =>
      lazymatch goal with
      | _ : mapped vx a _ |- _ => fail
      | _ => let M := fresh "MAP" in
             pose proof (u8arr_mapped L vx a bs H ltac:(off_image_solve L)) as M;
             try rewrite !Arr.upd_length in M
      end
  | H : stk ?segs vx ?lo ?hi |- _ =>
      lazymatch goal with
      | _ : mapped vx lo _ |- _ => fail
      | _ => let M := fresh "MAP" in
             pose proof (stk_mapped (L:=L) vx lo hi lo (hi - lo) H ltac:(lia) ltac:(lia) ltac:(lia)) as M
      end
  end.

(* [comment removed for export] *)
Ltac pose_cranges L A vx AINVx :=
  repeat match goal with
  | H : Step.rw_cells ?segs vx ?a ?cs |- _ =>
      lazymatch goal with
      | _ : crange A vx a _ |- _ => fail
      | _ => let C := fresh "CR" in
             first [ match goal with LV : a_live A a = Some ?n |- _ =>
                       pose proof (crange_block A _ _ a n a (Z.of_nat (Cells.cells_size cs)) AINVx LV
                                     ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as C end
                   | pose proof (crange_stack A _ _ vx a (Z.of_nat (Cells.cells_size cs)) AINVx
                                     ltac:(pose proof alloc_ceiling_val; cbn; lia) ltac:(cbn; lia)
                                     (rw_cells_mapped L vx a cs H ltac:(off_image_solve L))) as C ];
             cbn [Cells.cells_size Cells.csize Nat.add length app] in C
      end
  | H : Arr.u8arr ?segs vx ?a ?bs |- _ =>
      lazymatch goal with
      | _ : crange A vx a _ |- _ => fail
      | _ => let C := fresh "CR" in
             first [ match goal with LV : a_live A a = Some ?n |- _ =>
                       pose proof (crange_block A _ _ a n a (Z.of_nat (length bs)) AINVx LV
                                     ltac:(lia) ltac:(try rewrite !Arr.upd_length; lia) ltac:(lia)) as C end
                   | pose proof (crange_stack A _ _ vx a (Z.of_nat (length bs)) AINVx
                                     ltac:(pose proof alloc_ceiling_val; cbn; lia) ltac:(lia)
                                     (u8arr_mapped L vx a bs H ltac:(off_image_solve L))) as C ];
             try rewrite !Arr.upd_length in C
      end
  end.
