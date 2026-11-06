(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec.

Module Allovwl.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim RefMocc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Image Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Section Client.
Context {Clg : Ceiling} {L : AllocLayout} {AI : AllocSpec L}.   (* [comment removed for export] *)
Let segs := al_segs L.

(* [comment removed for export] *)
Let ro_addr_iff := as_ro_addr_iff (L:=L).
Let seg_rom_above := as_seg_rom_above (L:=L).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition crange (A : AS) (m : mem) (a n : Z) : Prop :=
  0 <= a /\ a + n <= 2^64 /\
  forall i, 0 <= i < n ->
    ~ owned A (a + i) /\ ~ (al_errno L <= a + i < al_errno L + 4)
    /\ (m (Z_to_bv 64 (a + i)) <> None \/ in_image L (a + i)).

Lemma crange_sub : forall A m a n a' n',
  crange A m a n -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> crange A m a' n'.
Proof.
  (intros A m a n a' n'; (first [ intro dR_10; dand3 dR_10 as H0 H1 H | intros (H0 & H1 & H) ]); intros Ha Hn Hn'). split; [lia|]. split; [lia|].
  intros i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

(* [comment removed for export] *)
Lemma crange_stack : forall A m md a n,
  ainv A m md -> alloc_ceiling <= a -> a + n <= 2^64 -> mapped m a n -> crange A m a n.
Proof.
  intros A m md a n AI0 Hc Hn Hm. pose proof (as_layout_order ) as LO. pose proof (as_errno_where ) as EW.
  split; [pose proof alloc_ceiling_val; lia|]. split; [exact Hn|].
  intros i Hi. split; [|split].
  - intros Ho. destruct (as_owned_where A m md (a + i) AI0 Ho) as [Hs|[[_ Hlt] _]].
    + apply as_static_where in Hs. lia.
    + lia.
  - lia.
  - left. apply Hm. exact Hi.
Qed.

(* [comment removed for export] *)
Lemma crange_data : forall A m md a n,
  ainv A m md -> al_rw_lo L <= a -> a + n <= al_image_hi L -> 0 <= n ->
  (forall i, 0 <= i < n -> ~ al_static L (a + i)) ->
  (a + n <= al_errno L \/ al_errno L + 4 <= a) ->
  crange A m a n.
Proof.
  intros A m md a n AI0 Hlo Hhi Hn Hs He. pose proof (as_layout_order ) as LO.
  split; [lia|]. split; [pose proof alloc_ceiling_val; lia|].
  intros i Hi. split; [|split].
  - intros Ho. destruct (as_owned_where A m md (a + i) AI0 Ho) as [Hst|[_ Hni]]; [exact (Hs i Hi Hst)| apply Hni; unfold in_image; lia].
  - lia.
  - right. unfold in_image. lia.
Qed.

(* [comment removed for export] *)
Lemma crange_image_ro : forall A m md a n,
  ainv A m md -> al_image_lo L <= a -> a + n <= al_rw_lo L -> 0 <= n -> crange A m a n.
Proof.
  intros A m md a n AI0 Hlo Hhi Hn. pose proof (as_layout_order ) as LO. pose proof (as_errno_where ) as EW.
  split; [lia|]. split; [pose proof alloc_ceiling_val; lia|].
  intros i Hi. split; [|split].
  - intros Ho. destruct (as_owned_where A m md (a + i) AI0 Ho) as [Hst|[_ Hni]]; [apply as_static_where in Hst; lia| apply Hni; unfold in_image; lia].
  - lia.
  - right. unfold in_image. lia.
Qed.

(* [comment removed for export] *)
Lemma crange_block : forall A m md p k a n,
  ainv A m md -> a_live A p = Some k -> p <= a -> a + n <= p + k -> 0 <= n -> crange A m a n.
Proof.
  intros A m md p k a n AI0 HL Hp Hn Hn0.
  (first [ pose proof ((as_live_ok A m md p k AI0 HL)) as dR_1; dand7 dR_1 as K0 AL LO HI IMG MP NO | destruct (as_live_ok A m md p k AI0 HL) as (K0 & AL & LO & HI & IMG & MP & NO) ]).
  pose proof (as_layout_order ) as LO'. pose proof (as_errno_where ) as EW. pose proof alloc_ceiling_val.
  split; [lia|]. split; [lia|].
  intros i Hi. split; [|split].
  - replace (a + i) with (p + (a - p + i)) by lia. apply NO. lia.
  - lia.
  - left. replace (a + i) with (p + (a - p + i)) by lia. apply MP. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Transport.
Variables (A A' : AS) (sp win : Z) (victim newb : Z -> Prop) (m m' : mem).
Hypothesis FR : frame_ok L (owned A) (owned A') sp win victim newb m m'.

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
  exists junk, length junk = Z.to_nat n /\ rw_cells segs m' r [CB (Z.to_nat n) junk] /\ crange A' m' r n.
Proof.
  intros A' m' md' r n AI' HL.
  (first [ pose proof ((as_live_ok A' m' md' r n AI' HL)) as dR_7; dand7 dR_7 as N0 AL LO HI IMG MP NO | destruct (as_live_ok A' m' md' r n AI' HL) as (N0 & AL & LO & HI & IMG & MP & NO) ]).
  pose proof alloc_ceiling_val as CV. pose proof (as_errno_where ) as EW. pose proof (as_layout_order ) as LO'.
  assert (G : forall i, 0 <= i < n -> exists b, m' (Z_to_bv 64 (r + i)) = Some b).
  { intros i Hi. specialize (MP i Hi). destruct (m' (Z_to_bv 64 (r + i))) as [b|]; [exists b; reflexivity| exfalso; apply MP; reflexivity]. }
  assert (REC : forall k, (k <= Z.to_nat n)%nat -> exists bs, length bs = k /\
            forall i, (i < k)%nat -> m' (Z_to_bv 64 (r + (n - Z.of_nat k) + Z.of_nat i)) = nth_error bs i).
  { induction k as [|k IH]; intros Hk.
    - exists []. split; [reflexivity|]. intros i Hi. cbn in Hi. lia.
    - (first [ pose proof ((IH ltac:(lia))) as dR_8; dex1 dR_8 as bs; destruct dR_8 as [Lb Hbs] | pose proof ((IH ltac:(lia))) as dR_8; dand3 dR_8 as bs Lb Hbs | destruct (IH ltac:(lia)) as (bs & Lb & Hbs) ]). destruct (G (n - Z.of_nat (S k)) ltac:(lia)) as (b & Hb).
      exists (b :: bs). split; [cbn; lia|]. intros [|i] Hi.
      + cbn. rewrite <- Hb. f_equal. f_equal. lia.
      + cbn. rewrite <- (Hbs i ltac:(lia)). f_equal. f_equal. lia. }
  (first [ pose proof ((REC (Z.to_nat n) ltac:(lia))) as dR_9; dex1 dR_9 as junk; destruct dR_9 as [LJ HJ] | pose proof ((REC (Z.to_nat n) ltac:(lia))) as dR_9; dand3 dR_9 as junk LJ HJ | destruct (REC (Z.to_nat n) ltac:(lia)) as (junk & LJ & HJ) ]).
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
Lemma stk_mapped : forall m lo hi a n,
  stk segs m lo hi -> alloc_ceiling <= lo -> lo <= a -> a + n <= hi -> mapped m a n.
Proof.
  (intros m lo hi a n; (first [ intro dR_16; dand3 dR_16 as S0 S1 S | intros (S0 & S1 & S) ]); intros Hlo Ha Hn i Hi E).
  destruct (S (a + i) ltac:(lia)) as [W _]. apply W. unfold wview, wa. rewrite E.
  subst segs. pose proof (as_layout_order) as LO. pose proof alloc_ceiling_val.
  rewrite (as_find_segment_above (Z_to_bv 64 (a + i))); [reflexivity|]. rewrite unsigned_lit; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

End Client.
End Allovwl.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ALLOC_MAX : Z := 2^32.
Definition EXT_MAX : Z := 2^30 - 4096.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land_pagemask : forall x, 0 <= x < 2^63 ->
  Z.land x 9223372036854771712 = x / 4096 * 4096.
Proof.
  intros x Hx.
  assert (E : 9223372036854771712 = Z.ldiff (Z.ones 63) (Z.ones 12)) by reflexivity.
  rewrite E. apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.ldiff_spec, !Z.testbit_ones_nonneg by lia.
  replace (x / 4096 * 4096) with (Z.shiftl (Z.shiftr x 12) 12).
  2:{ rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity. }
  destruct (Z.ltb_spec i 12) as [Hlt|Hge].
  - rewrite Z.shiftl_spec_low by lia.
    destruct (Z.testbit x i); cbn; rewrite ?Bool.andb_false_r; reflexivity.
  - rewrite Z.shiftl_spec_high, Z.shiftr_spec by lia. replace (i - 12 + 12) with i by lia.
    destruct (Z.ltb_spec i 63) as [Hlt2|Hge2].
    + cbn. rewrite Bool.andb_true_r. reflexivity.
    + cbn. rewrite Bool.andb_false_r. symmetry. apply Z.bits_above_log2; [lia|].
      destruct (Z.eq_dec x 0) as [->|Hnz]; [cbn; lia|]. apply Z.log2_lt_pow2; [lia|].
      eapply Z.lt_le_trans; [apply (proj2 Hx)|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma roundup_pagemask : forall sz, 0 <= sz -> sz + 4095 < 2^63 ->
  Z.land (sz + 4095) 9223372036854771712 = (sz + 4095) / 4096 * 4096.
Proof. intros. apply land_pagemask. lia. Qed.

(* [comment removed for export] *)

Section S.
  Context {Clg : Ceiling} (L : AllocLayout) {AI : AllocSpec L}.   (* [comment removed for export] *)
  Let segs := al_segs L.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint client_fp (A : AS) (W : list ivl) : Prop :=
    match W with
    | [] => True
    | (lo, hi) :: W' => (alloc_ceiling <= lo /\ hi <= 2^64
                         \/ (exists p n, a_live A p = Some n /\ p <= lo /\ hi <= p + n)
                         \/ (lo = al_errno L /\ hi = al_errno L + 4)
                         \/ (al_rw_lo L <= lo /\ hi <= al_image_hi L /\
                             forall a, lo <= a < hi -> ~ al_static L a /\ ~ al_shared L a))
                        /\ client_fp A W'
    end.

  Lemma client_fp_cases : forall A W a,
    client_fp A W -> ~ outside W a ->
    (alloc_ceiling <= a < 2^64) \/ (exists p n, a_live A p = Some n /\ p <= a < p + n)
    \/ (al_errno L <= a < al_errno L + 4)
    \/ (al_rw_lo L <= a < al_image_hi L /\ ~ al_static L a /\ ~ al_shared L a).
  Proof.
    intros A W a CF NO. induction W as [|[lo hi] W IH]; cbn in *; [tauto|].
    destruct CF as [HW CF].
    assert (CASE : (lo <= a < hi) \/ ~ outside W a) by tauto.
    destruct CASE as [Hin|Hrest]; [|apply IH; assumption].
    destruct HW as [[Hc Hh]|[(p & n & HL & Hp & Hn)|[[E1 E2]|(D1 & D2 & D3)]]]; [left; lia| | right; right; left; lia|].
    - right; left. exists p, n. split; [exact HL|lia].
    - right; right; right. destruct (D3 a Hin) as [X Y]. split; [lia|]. split; assumption.
  Qed.

  Lemma client_fp_not_owned : forall A m md W a,
    ainv A m md -> client_fp A W -> ~ outside W a -> ~ owned A a /\ ~ al_shared L a /\ 0 <= a < 2^64.
  Proof.
    intros A m md W a AI0 CF NO. pose proof (as_layout_order (L:=L)) as LO. pose proof alloc_ceiling_val as CV.
    pose proof (as_errno_where (L:=L)) as EW.
    destruct (client_fp_cases A W a CF NO) as [[Hc Hh]|[(p & n & HL & Hp & Hn)|[HE|(HD & NS & NSH)]]].
    - split; [|split; [|lia]].
      + intros O. destruct (as_owned_where A m md a AI0 O) as [Hs|[[Hge Hlt] Hni]]; [apply as_static_where in Hs; lia| lia].
      + intros Sh. apply as_shared_where in Sh. lia.
    - (first [ pose proof ((as_live_ok A m md p n AI0 HL)) as dR_1; dand7 dR_1 as N0 AL PLO PHI IMG MP NOW | destruct (as_live_ok A m md p n AI0 HL) as (N0 & AL & PLO & PHI & IMG & MP & NOW) ]).
      split; [|split; [|lia]].
      + replace a with (p + (a - p)) by lia. apply NOW. lia.
      + intros Sh. apply as_shared_where in Sh. lia.
    - pose proof (as_errno_not_static (L:=L) (a - al_errno L) ltac:(lia)) as [NS NSH].
      replace (al_errno L + (a - al_errno L)) with a in NS, NSH by lia.
      split; [|split; [exact NSH|lia]].
      intros O. destruct (as_owned_where A m md a AI0 O) as [Hs|[[Hge Hlt] Hni]]; [exact (NS Hs)|].
      apply Hni. unfold in_image. lia.
    - split; [|split; [exact NSH|lia]].
      intros O. destruct (as_owned_where A m md a AI0 O) as [Hs|[[Hge Hlt] Hni]]; [exact (NS Hs)|].
      apply Hni. unfold in_image. lia.
  Qed.

  Lemma ainv_munch : forall A m m1 md W,
    ainv A m md -> munch W m m1 -> wmono segs m m1 -> client_fp A W -> ainv A m1 md.
  Proof.
    intros A m m1 md W AI0 MU WM CF.
    pose proof (as_lazy_nil A m md AI0) as [HL HH].
    assert (EQ : forall a, (owned A a \/ al_shared L a) -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a Ho.
      assert (R : 0 <= a < 2^64).
      { destruct Ho as [O|Sh].
        - pose proof (as_layout_order (L:=L)) as LO. pose proof alloc_ceiling_val.
          destruct (as_owned_where A m md a AI0 O) as [Hs|[[Hge Hlt] Hni]]; [apply as_static_where in Hs; lia| unfold in_image in Hni; lia].
        - apply as_shared_where in Sh. pose proof (as_layout_order (L:=L)). pose proof alloc_ceiling_val. lia. }
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN].
      - apply (MU (Z_to_bv 64 a)). rewrite unsigned_lit by lia. exact OUT.
      - exfalso. (first [ pose proof ((client_fp_not_owned A m md W a AI0 CF NIN)) as dR_2; dand3 dR_2 as NO NS _ | destruct (client_fp_not_owned A m md W a AI0 CF NIN) as (NO & NS & _) ]). tauto. }
    eapply (as_frame A m m1 md md AI0).
    - intros a O. apply EQ. left; exact O.
    - intros a Sh. apply EQ. right; exact Sh.
    - intros p n i HLv Hi.
      (first [ pose proof ((as_live_ok A m md p n AI0 HLv)) as dR_3; dand7 dR_3 as N0 AL PLO PHI IMG MP NOW | destruct (as_live_ok A m md p n AI0 HLv) as (N0 & AL & PLO & PHI & IMG & MP & NOW) ]).
      specialize (MP i Hi). specialize (WM (Z_to_bv 64 (p + i))).
      unfold wview in WM. pose proof alloc_ceiling_val. pose proof (as_layout_order (L:=L)).
      rewrite (as_find_segment_outside (L:=L)) in WM by (unfold in_image; rewrite unsigned_lit; lia).
      destruct (m (Z_to_bv 64 (p + i))); [|exfalso; apply MP; reflexivity].
      destruct (m1 (Z_to_bv 64 (p + i))); [discriminate|]. exfalso. apply WM; [discriminate|reflexivity].
    - intros a Ha Hm1. destruct Ha as [[Hge Hlt] Hni].
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN].
      + rewrite <- (MU (Z_to_bv 64 a)); [exact Hm1|]. pose proof alloc_ceiling_val. pose proof (as_layout_order (L:=L)).
        rewrite unsigned_lit by lia. exact OUT.
      + pose proof alloc_ceiling_val as CV. pose proof (as_errno_where (L:=L)) as EW. pose proof (as_layout_order (L:=L)) as LO'.
        destruct (client_fp_cases A W a CF NIN) as [[Hc Hh]|[(p & n & HLv & Hp & Hn)|[HE|(HD & _ & _)]]]; [lia| | exfalso; apply Hni; unfold in_image; lia | exfalso; apply Hni; unfold in_image; lia].
        (first [ pose proof ((as_live_ok A m md p n AI0 HLv)) as dR_4; dand7 dR_4 as N0 AL PLO PHI IMG MP NOW | destruct (as_live_ok A m md p n AI0 HLv) as (N0 & AL & PLO & PHI & IMG & MP & NOW) ]).
        replace a with (p + (a - p)) by lia. apply MP. lia.
    - reflexivity.
    - exact HH.
  Qed.
End S.

(* [comment removed for export] *)
Definition off_image (L : AllocLayout) (a n : Z) : Prop := a + n <= al_image_lo L \/ al_image_hi L <= a.

Section S2.
  Context {Clg : Ceiling} (L : AllocLayout) {AI : AllocSpec L}.   (* [comment removed for export] *)
  Let segs := al_segs L.

  Lemma off_image_sub : forall a n a' n', off_image L a n -> a <= a' -> a' + n' <= a + n -> off_image L a' n'.
  Proof. unfold off_image. intros. lia. Qed.
  Lemma off_image_stack : forall a n, alloc_ceiling <= a -> off_image L a n.
  Proof. unfold off_image. intros. pose proof (as_layout_order (L:=L)). right. lia. Qed.
  (* [comment removed for export] *)
  Lemma live_geom : forall A m md p n, ainv A m md -> a_live A p = Some n ->
    0 <= n /\ p mod 16 = 0 /\ 4096 <= p /\ p + n <= alloc_ceiling /\ off_image L p n /\ mapped m p n /\
    (forall i, 0 <= i < n -> ~ owned A (p + i)).
  Proof. intros A m md p n AI0 LV. exact (as_live_ok A m md p n AI0 LV). Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_mapped : forall m a cs,
    rw_cells segs m a cs -> off_image L a (Z.of_nat (cells_size cs)) ->
    mapped m a (Z.of_nat (cells_size cs)).
  Proof.
    unfold off_image. intros m a cs [_ (W0 & W1 & W)] Ha i Hi E.
    specialize (W i Hi). unfold wview, wa in W. rewrite E in W.
    subst segs. rewrite (as_find_segment_outside (L:=L)) in W; [exact (W eq_refl)|].
    unfold in_image. rewrite unsigned_lit; lia.
  Qed.
  Lemma u8arr_mapped : forall m a bs,
    u8arr segs m a bs -> off_image L a (Z.of_nat (length bs)) ->
    mapped m a (Z.of_nat (length bs)).
  Proof.
    unfold off_image. intros m a bs [_ (W0 & W1 & W)] Ha i Hi E.
    specialize (W i Hi). unfold wview, wa in W. rewrite E in W.
    subst segs. rewrite (as_find_segment_outside (L:=L)) in W; [exact (W eq_refl)|].
    unfold in_image. rewrite unsigned_lit; lia.
  Qed.
End S2.

(* [comment removed for export] *)
Ltac fold_al_segs :=
  repeat match goal with
  | H : context [al_segs ?L] |- _ => let v := eval cbv beta iota delta [al_segs L] in (al_segs L) in change (al_segs L) with v in H
  | |- context [al_segs ?L] => let v := eval cbv beta iota delta [al_segs L] in (al_segs L) in change (al_segs L) with v
  | |- context [al_rom ?L] => let v := eval cbv beta iota delta [al_rom al_segs L] in (al_rom L) in change (al_rom L) with v
  end.
(* [comment removed for export] *)
Ltac fix_ret_pc :=
  repeat match goal with
  | |- context [ret_pc (Z_to_bv 64 ?z)] => rewrite (ret_pc_even z) by first [lia | reflexivity]
  end.
Ltac rz_resume MDH MDL :=
  fold_al_segs; rewrite ?mkst_MS; fix_ret_pc;
  apply rz_go; [exact MDH | exact MDL |].

(* [comment removed for export] *)
Section CFrame.
  Context {Clg : Ceiling} (L : AllocLayout) {AI : AllocSpec L}.   (* [comment removed for export] *)
  Let segs := al_segs L.

  Definition cframe (o o' : Z -> Prop) (sp win : Z) (V N : Z -> Prop) (m m' : mem) : Prop :=
       (forall a, 0 <= a < 2^64 -> ~ o a -> (m (Z_to_bv 64 a) <> None \/ in_image L a) ->
                  ~ (sp - win <= a < sp) -> ~ (al_errno L <= a < al_errno L + 4) -> ~ V a ->
                  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) /\ ~ o' a)
    /\ mapped m' (sp - win) win
    /\ (forall a, 0 <= a < 2^64 -> ~ (sp - win <= a < sp) -> ~ (al_errno L <= a < al_errno L + 4) ->
                  N a -> o a \/ V a \/ (m (Z_to_bv 64 a) = None /\ ~ in_image L a)).

  Lemma cframe_of_frame_ok : forall o o' sp win V N m m',
    frame_ok L o o' sp win V N m m' -> cframe o o' sp win V N m m'.
  Proof.
    (intros o o' sp win V N m m'; (first [ intro dR_12; dand7 dR_12 as F1 F2 F3 F4 F5 F6 F7 | intros (F1 & F2 & F3 & F4 & F5 & F6 & F7) ])). split; [|split; [exact F3|]].
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

  Lemma cframe_weaken : forall o o' sp win win' (V V' N N' : Z -> Prop) m m',
    cframe o o' sp win V N m m' -> win <= win' -> mapped m' (sp - win') win' ->
    (forall a, V a -> V' a) -> (forall a, N' a -> N a) ->
    cframe o o' sp win' V' N' m m'.
  Proof.
    (intros o o' sp win win' V V' N N' m m'; (first [ intro dR_13; dand3 dR_13 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros Hw MAP HV HN). split; [|split; [exact MAP|]].
    - intros a Ha NO VIS NW NE NV. apply C1; [exact Ha| exact NO| exact VIS| lia| exact NE| intros X; apply NV, HV, X].
    - intros a Ha NW NE NB. destruct (C3 a Ha ltac:(lia) NE (HN a NB)) as [X|[X|X]]; [left; exact X| right; left; apply HV, X| right; right; exact X].
  Qed.

  (* [comment removed for export] *)
  Lemma cframe_stores : forall o sp win (V : Z -> Prop) m m0 (W : list ivl),
    munch W m m0 ->
    (forall a, 0 <= a < 2^64 -> ~ outside W a -> (sp - win <= a < sp) \/ V a) ->
    mapped m0 (sp - win) win ->
    cframe o o sp win V nowhere m m0.
  Proof.
    intros o sp win V m m0 W MU IN MAP. split; [|split; [exact MAP|]].
    - intros a Ha NO VIS NW NE NV. split; [|exact NO].
      apply (MU (Z_to_bv 64 a)). rewrite unsigned_lit by lia.
      destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso. destruct (IN a Ha X); tauto.
    - intros a _ _ _ X. destruct X.
  Qed.

  (* [comment removed for export] *)
  Lemma cframe_noalloc : forall o sp win (V N : Z -> Prop) m m0 (W : list ivl),
    munch W m m0 ->
    (forall a, 0 <= a < 2^64 -> ~ outside W a -> (sp - win <= a < sp) \/ V a) ->
    mapped m0 (sp - win) win ->
    (forall a, N a -> V a) ->
    cframe o o sp win V N m m0.
  Proof.
    intros o sp win V N m m0 W MU IN MAP NV.
    (first [ pose proof ((cframe_stores o sp win V m m0 W MU IN MAP)) as dR_5; dand3 dR_5 as C1 C2 _ | destruct (cframe_stores o sp win V m m0 W MU IN MAP) as (C1 & C2 & _) ]).
    split; [exact C1|]. split; [exact C2|]. intros a _ _ _ X. right; left. apply NV, X.
  Qed.

  (* [comment removed for export] *)
  Lemma cframe_extend :
    forall o o' (sp' win sp WIN : Z) (V V' N N' : Z -> Prop) (m m0 m' m'' : mem) (W1 W2 : list ivl),
      munch W1 m m0 ->
      (forall a, 0 <= a < 2^64 -> ~ outside W1 a -> (sp - WIN <= a < sp) \/ V' a) ->
      cframe o o' sp' win V N m0 m' ->
      sp - WIN <= sp' - win -> sp' <= sp ->
      (forall a, V a -> V' a) -> (forall a, N' a -> N a \/ V' a) ->
      munch W2 m' m'' ->
      (forall a, 0 <= a < 2^64 -> ~ outside W2 a -> (sp - WIN <= a < sp) \/ V' a \/ N a) ->
      mapped m'' (sp - WIN) WIN ->
      cframe o o' sp WIN V' N' m m''.
  Proof.
    (intros o o' sp' win sp WIN V V' N N' m m0 m' m'' W1 W2 MU1 IN1; (first [ intro dR_14; dand3 dR_14 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros Hlo Hhi HV HN MU2 IN2 MAP).
    split; [|split; [exact MAP|]].
    - intros a Ha NO VIS NW NE NV.
      assert (O1 : outside W1 a).
      { destruct (Classical_Prop.classic (outside W1 a)) as [X|X]; [exact X|]. exfalso. destruct (IN1 a Ha X); tauto. }
      assert (E1 : m0 (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
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

  (* [comment removed for export] *)
  Lemma cframe_reframe : forall o o' sp' win' sp win V N m m',
    cframe o o' sp' win' V N m m' -> sp - win <= sp' - win' -> sp' <= sp ->
    mapped m' (sp - win) win ->
    cframe o o' sp win V N m m'.
  Proof.
    (intros o o' sp' win' sp win V N m m'; (first [ intro dR_15; dand3 dR_15 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros Hlo Hhi MAP). split; [|split; [exact MAP|]].
    - intros a Ha NO VIS NW NE NV. apply C1; [exact Ha| exact NO| exact VIS| lia| exact NE| exact NV].
    - intros a Ha NW NE NB. apply C3; [exact Ha| lia| exact NE| exact NB].
  Qed.

  (* [comment removed for export] *)
  Lemma cframe_seq : forall o o1 o2 sp w1 w2 W (V1 N1 V2 N2 V N : Z -> Prop) m m1 m2,
    cframe o o1 sp w1 V1 N1 m m1 -> cframe o1 o2 sp w2 V2 N2 m1 m2 ->
    w1 <= W -> w2 <= W -> mapped m2 (sp - W) W ->
    (forall a, V1 a -> V a) -> (forall a, V2 a -> N1 a \/ V a) -> (forall a, N a -> N1 a \/ N2 a \/ V a) ->
    cframe o o2 sp W V N m m2.
  Proof.
    (intros o o1 o2 sp w1 w2 W V1 N1 V2 N2 V N m m1 m2; (first [ intro dR_16; dand3 dR_16 as C1 C2 C3 | intros (C1 & C2 & C3) ]); (first [ intro dR_17; dand3 dR_17 as D1 D2 D3 | intros (D1 & D2 & D3) ]); intros Hw1 Hw2 MAP HV1 HV2 HN0).
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
      (* [comment removed for export] *)
      destruct (Classical_Prop.classic (o a)) as [O|NO]; [left; exact O|].
      destruct (Classical_Prop.classic (V a)) as [HVa|NVa]; [right; left; exact HVa|].
      destruct (Classical_Prop.classic (m (Z_to_bv 64 a) <> None \/ in_image L a)) as [VIS|NVIS].
      2:{ right; right. split; [| intros X; apply NVIS; right; exact X].
          destruct (m (Z_to_bv 64 a)); [exfalso; apply NVIS; left; discriminate| reflexivity]. }
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
    Variables (A A' : AS) (sp win : Z) (V N : Z -> Prop) (m m' : mem).
    Hypothesis CF : cframe (owned A) (owned A') sp win V N m m'.

    Lemma crange_csame : forall a n, crange A m a n -> avoids_call sp win V a n ->
      forall i, 0 <= i < n -> m' (Z_to_bv 64 (a + i)) = m (Z_to_bv 64 (a + i)).
    Proof.
      (intros a n; (first [ intro dR_18; dand3 dR_18 as H0 H1 H | intros (H0 & H1 & H) ]); intros [W HV] i Hi). (first [ pose proof ((H i Hi)) as dR_6; dand3 dR_6 as NO NE MP | destruct (H i Hi) as (NO & NE & MP) ]).
      destruct CF as (C1 & _ & _). apply (C1 (a + i)); [lia| exact NO| exact MP| lia| exact NE| apply HV; exact Hi].
    Qed.

    Lemma bytes_at_ccall : forall a bs, crange A m a (Z.of_nat (length bs)) -> avoids_call sp win V a (Z.of_nat (length bs)) ->
      bytes_at segs m a bs -> bytes_at segs m' a bs.
    Proof.
      (intros a bs C AV; (first [ intro dR_19; dand3 dR_19 as B0 B1 B | intros (B0 & B1 & B) ])). split; [exact B0|]. split; [exact B1|].
      intros i Hi. specialize (B i Hi). unfold mrd in *. unfold wa in *.
      rewrite (crange_csame a _ C AV (Z.of_nat i) ltac:(lia)). exact B.
    Qed.

    Lemma wr_at_ccall : forall a n, crange A m a n -> avoids_call sp win V a n -> wr_at segs m a n -> wr_at segs m' a n.
    Proof.
      (intros a n C AV; (first [ intro dR_20; dand3 dR_20 as W0 W1 W | intros (W0 & W1 & W) ])). split; [exact W0|]. split; [exact W1|].
      intros i Hi. specialize (W i Hi). unfold wview in *. unfold wa in *.
      rewrite (crange_csame a n C AV i Hi). exact W.
    Qed.

    Lemma rw_cells_ccall : forall a cs, crange A m a (Z.of_nat (cells_size cs)) -> avoids_call sp win V a (Z.of_nat (cells_size cs)) ->
      rw_cells segs m a cs -> rw_cells segs m' a cs.
    Proof.
      intros a cs C AV [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
      - apply bytes_at_ccall; [rewrite cells_bytes_length by exact Hwf; exact C| rewrite cells_bytes_length by exact Hwf; exact AV| exact HB].
      - apply wr_at_ccall; assumption.
    Qed.

    Lemma ro_cells_ccall : forall a cs, crange A m a (Z.of_nat (cells_size cs)) -> avoids_call sp win V a (Z.of_nat (cells_size cs)) ->
      ro_cells segs m a cs -> ro_cells segs m' a cs.
    Proof.
      intros a cs C AV [Hwf HB]. split; [exact Hwf|].
      apply bytes_at_ccall; [rewrite cells_bytes_length by exact Hwf; exact C| rewrite cells_bytes_length by exact Hwf; exact AV| exact HB].
    Qed.

    Lemma u8arr_ccall : forall a bs, crange A m a (Z.of_nat (length bs)) -> avoids_call sp win V a (Z.of_nat (length bs)) ->
      u8arr segs m a bs -> u8arr segs m' a bs.
    Proof.
      intros a bs C AV [HB HW]. split; [apply bytes_at_ccall; assumption| apply wr_at_ccall; assumption].
    Qed.

    Lemma crange_ccall : forall a n, crange A m a n -> avoids_call sp win V a n -> crange A' m' a n.
    Proof.
      intros a n C AV. (first [ pose proof (C) as dR_7; dand3 dR_7 as H0 H1 H | pose proof C as (H0 & H1 & H) ]). split; [exact H0|]. split; [exact H1|].
      intros i Hi. (first [ pose proof ((H i Hi)) as dR_8; dand3 dR_8 as NO NE MP | destruct (H i Hi) as (NO & NE & MP) ]). destruct AV as [W HV].
      destruct CF as (C1 & _ & _).
      destruct (C1 (a + i) ltac:(lia) NO MP ltac:(lia) NE (HV i Hi)) as [E NO'].
      split; [exact NO'|]. split; [exact NE|]. rewrite E. exact MP.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
  End Transport.

  (* [comment removed for export] *)
  Lemma stk_ccall : forall A A' m md m' (sp win : Z) V N lo hi,
    ainv A m md -> cframe (owned A) (owned A') sp win V N m m' ->
    stk segs m lo hi -> alloc_ceiling <= lo -> lo <= sp - win -> sp <= hi ->
    (forall a, lo <= a < hi -> ~ V a) ->
    stk segs m' lo hi.
  Proof.
    (intros A A' m md m' sp win V N lo hi AI0; (first [ intro dR_22; dand3 dR_22 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros ST Hlo Hw Hsp HV).
    (first [ dand3 ST as S0 S1 S | destruct ST as (S0 & S1 & S) ]). split; [exact S0|]. split; [exact S1|].
    pose proof (as_layout_order (L:=L)) as LO. pose proof (as_errno_where (L:=L)) as EW. pose proof alloc_ceiling_val as CV.
    intros a Ha.
    assert (NO : ~ owned A a).
    { intros O. destruct (as_owned_where A m md a AI0 O) as [Hs|[[_ Hlt] _]]; [apply as_static_where in Hs; lia| lia]. }
    destruct (Classical_Prop.classic (sp - win <= a < sp)) as [Hin|Hout].
    - assert (Hm : m' (wa a) <> None).
      { unfold wa. replace a with (sp - win + (a - (sp - win))) by lia. apply C2. lia. }
      split.
      + unfold wview. destruct (m' (wa a)); [discriminate| exfalso; apply Hm; reflexivity].
      + unfold mrd. destruct (m' (wa a)) as [b|]; [exists b; reflexivity| exfalso; apply Hm; reflexivity].
    - destruct (S a Ha) as [W [b Hb']].
      assert (VISm : m (Z_to_bv 64 a) <> None).
      { intros E. unfold mrd, wa in Hb'. rewrite E in Hb'. subst segs.
        rewrite (as_seg_rom_outside (L:=L)) in Hb'; [discriminate|]. unfold in_image. rewrite unsigned_lit by lia. lia. }
      destruct (C1 a ltac:(lia) NO (or_introl VISm) Hout ltac:(lia) (HV a Ha)) as [E _].
      split.
      + unfold wview, wa in *. rewrite E. exact W.
      + exists b. unfold mrd, wa in *. rewrite E. exact Hb'.
  Qed.
End CFrame.


(* [comment removed for export] *)
Ltac acall_consts := unfold MALLOC_STACK, FREE_STACK, CALLOC_STACK, REALLOC_STACK in *.
Ltac avoids_solve :=
  cbn [Cells.cells_size Cells.csize Nat.add length app];
  split; [ lia | intros ? ? X; unfold blk, nowhere in X; cbn beta in X; lia ].

Ltac acall_xfer FRK :=
  acall_consts;
  lazymatch type of FRK with
  | frame_ok ?L _ _ _ _ _ _ _ _ => apply (cframe_of_frame_ok L) in FRK
  | _ => idtac
  end;
  lazymatch type of FRK with
  | cframe ?L (owned ?A) (owned ?A') ?sp ?win ?V ?N ?m ?m' =>
    repeat match goal with
    | H : Step.rw_cells ?segs m ?a ?cs |- _ =>
        first [ match goal with C : crange A m _ _ |- _ =>
                  apply (rw_cells_ccall L A A' sp win V N m m' FRK a cs) in H;
                  [ | exact C | avoids_solve ] end
              | idtac "note: dropping hypothesis (call):" H; clear H ]
    | H : Step.ro_cells ?segs m ?a ?cs |- _ =>
        first [ match goal with C : crange A m _ _ |- _ =>
                  apply (ro_cells_ccall L A A' sp win V N m m' FRK a cs) in H;
                  [ | exact C | avoids_solve ] end
              | idtac "note: dropping hypothesis (call):" H; clear H ]
    | H : bytes_at ?segs m ?a ?bs |- _ =>
        first [ match goal with C : crange A m _ _ |- _ =>
                  apply (bytes_at_ccall L A A' sp win V N m m' FRK a bs) in H;
                  [ | exact C | avoids_solve ] end
              | idtac "note: dropping hypothesis (call):" H; clear H ]
    | H : Arr.u8arr ?segs m ?a ?bs |- _ =>
        first [ match goal with C : crange A m _ _ |- _ =>
                  apply (u8arr_ccall L A A' sp win V N m m' FRK a bs) in H;
                  [ | exact C | avoids_solve ] end
              | idtac "note: dropping hypothesis (call):" H; clear H ]
    | H : stk ?segs m ?lo ?hi |- _ =>
        first [ match goal with AI0 : ainv A m ?md |- _ =>
                  apply (stk_ccall L A A' m md m' sp win V N lo hi AI0 FRK) in H;
                  [ | lia | lia | lia | intros ? ? X; unfold blk, nowhere in X; cbn beta in X; lia ] end
              | idtac "note: dropping hypothesis (call):" H; clear H ]
    | H : mem_inv ?segs m |- _ => clear H
    end;
    repeat match goal with
    | C : crange A m ?a ?n |- _ =>
        first [ apply (crange_ccall L A A' sp win V N m m' FRK a n) in C; [ | avoids_solve ]
              | clear C ]
    end
  end.


(* [comment removed for export] *)
Section MappedHelpers.
  Lemma mapped_sub : forall m a n a' n', mapped m a n -> a <= a' -> a' + n' <= a + n -> mapped m a' n'.
  Proof. intros m a n a' n' H H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia. Qed.
End MappedHelpers.
Ltac prove_mapped1 :=
  first [ match goal with H : mapped ?m ?a ?n |- mapped ?m ?a ?n' => apply (mapped_sub m a n a n' H); lia end
        | match goal with H : mapped ?m ?a ?n |- mapped ?m ?a' ?n' => apply (mapped_sub m a n a' n' H); lia end ].

(* [comment removed for export] *)
Section CVar.
  Context {Clg : Ceiling} (L : AllocLayout) {AI : AllocSpec L}.   (* [comment removed for export] *)

  Definition cvar (A : AS) (sp : Z) (excl : list Z) (a n : Z) : Prop :=
    (alloc_ceiling <= a /\ sp <= a /\ a + n <= 2^64) \/
    (exists p k, a_live A p = Some k /\ ~ In p excl /\ p <= a /\ a + n <= p + k).

  Lemma cvar_facts : forall A m md sp excl a n lo,
    ainv A m md -> cvar A sp excl a n -> alloc_ceiling <= lo -> lo <= sp ->
       (alloc_ceiling <= a /\ a + n <= 2^64 \/ (exists p k, a_live A p = Some k /\ p <= a /\ a + n <= p + k)
        \/ (a = al_errno L /\ a + n = al_errno L + 4)
        \/ (al_rw_lo L <= a /\ a + n <= al_image_hi L /\ forall x, a <= x < a + n -> ~ al_static L x /\ ~ al_shared L x))
    /\ (sp <= a \/ a + n <= lo) /\ 4096 <= a /\ a + n <= 2^64
    /\ off_image L a n
    /\ (forall q j, In q excl -> a_live A q = Some j -> a + n <= q \/ q + j <= a).
  Proof.
    unfold off_image. intros A m md sp excl a n lo AI0 CV CE LO.
    pose proof (as_layout_order (L:=L)) as LAY. pose proof alloc_ceiling_val as ACV.
    destruct CV as [(C1 & C2 & C3)|(p & k & LV & NI & P1 & P2)].
    - split; [left; lia|]. split; [left; lia|]. split; [lia|]. split; [lia|]. split; [right; lia|].
      intros q j _ LQ. destruct (as_live_ok A m md q j AI0 LQ) as (? & ? & ? & ? & _). lia.
    - (first [ pose proof ((as_live_ok A m md p k AI0 LV)) as dR_11; dand6 dR_11 as K0 _ PLO PHI IMG _ | destruct (as_live_ok A m md p k AI0 LV) as (K0 & _ & PLO & PHI & IMG & _) ]).
      split; [right; left; exists p, k; split; [exact LV| lia]|]. split; [right; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      intros q j IQ LQ.
      assert (NE : p <> q) by (intros ->; exact (NI IQ)).
      destruct (as_live_ok A m md q j AI0 LQ) as (J0 & _).
      pose proof (as_live_disjoint A m md p k q j AI0 LV LQ NE). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma crange_of_cfp : forall A m md a n,
    ainv A m md ->
    (alloc_ceiling <= a /\ a + n <= 2^64 \/ (exists p k, a_live A p = Some k /\ p <= a /\ a + n <= p + k)
     \/ (a = al_errno L /\ a + n = al_errno L + 4)
     \/ (al_rw_lo L <= a /\ a + n <= al_image_hi L /\ forall x, a <= x < a + n -> ~ al_static L x /\ ~ al_shared L x)) ->
    mapped m a n -> 0 < n -> off_image L a n -> crange A m a n.
  Proof.
    intros A m md a n AI0 [[C1 C2]|[(p & k & LV & P1 & P2)|[[E1 E2]|(D1 & D2 & D3)]]] MP N0 OI.
    - eapply crange_stack; [exact AI0| exact C1| exact C2| exact MP].
    - eapply crange_block; [exact AI0| exact LV| exact P1| exact P2| lia].
    - exfalso. unfold off_image in OI. pose proof (as_errno_where (L:=L)). pose proof (as_layout_order (L:=L)). lia.
    - exfalso. unfold off_image in OI. pose proof (as_layout_order (L:=L)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma cvar_keep : forall A A' sp excl excl' a n,
    cvar A sp excl a n ->
    (forall p k, a_live A p = Some k -> ~ In p excl -> a_live A' p = Some k /\ ~ In p excl') ->
    cvar A' sp excl' a n.
  Proof.
    intros A A' sp excl excl' a n [C|(p & k & LV & NI & P1 & P2)] HK; [left; exact C|].
    right. destruct (HK p k LV NI) as [LV' NI']. exists p, k. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.
End CVar.

Lemma md_frame_refl : forall md, m_vm_lazy md = [] -> m_halted md = None -> md_frame md md.
Proof. intros md L H. unfold md_frame. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | reflexivity]. Qed.

Lemma md_frame_trans : forall md md1 md2, md_frame md md1 -> md_frame md1 md2 -> md_frame md md2.
Proof.
  intros md md1 md2 A B. unfold md_frame in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | etransitivity; eassumption].
Qed.

(* [comment removed for export] *)
Section WindowMapped.
  Context {Clg : Ceiling} (L : AllocLayout) {AI : AllocSpec L}.   (* [comment removed for export] *)
  Lemma window_mapped : forall m lo a sp W cs,
    stk (al_segs L) m lo a -> rw_cells (al_segs L) m a cs -> a + Z.of_nat (cells_size cs) = sp ->
    alloc_ceiling <= lo -> lo <= sp - W -> sp - W <= a -> mapped m (sp - W) W.
  Proof.
    intros m lo a sp W cs ST FR SZ CE LO HA i Hi.
    pose proof (as_layout_order (L:=L)) as LAY. pose proof alloc_ceiling_val as CV.
    destruct (Z_lt_le_dec (sp - W + i) a) as [Hb|Hb].
    - apply (stk_mapped (L:=L) m lo a (sp - W) (a - (sp - W)) ST CE ltac:(lia) ltac:(lia)). lia.
    - pose proof (rw_cells_mapped L m a cs FR ltac:(apply (@off_image_stack _ L _); lia)) as M.
      replace (sp - W + i) with (a + (sp - W + i - a)) by lia. apply M. lia.
  Qed.
End WindowMapped.

(* [comment removed for export] *)
Ltac cps_done := apply evt_done; cbv beta delta [rz_at].

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac off_image_solve L :=
  cbn [Cells.cells_size Cells.csize Nat.add length app]; try rewrite !Arr.upd_length;
  first [ assumption
        | apply (@off_image_stack _ L _); lia
        | match goal with H : off_image _ _ _ |- _ => apply (@off_image_sub L _ _ _ _ H); cbn [Cells.cells_size Cells.csize Nat.add length app]; lia end ].

Ltac pose_mapped L mx :=
  repeat match goal with
  | H : Step.rw_cells ?segs mx ?a ?cs |- _ =>
      lazymatch goal with
      | _ : mapped mx a _ |- _ => fail
      | _ => let M := fresh "MAP" in
             pose proof (rw_cells_mapped L mx a cs H ltac:(off_image_solve L)) as M;
             cbn [Cells.cells_size Cells.csize Nat.add length app] in M
      end
  | H : Arr.u8arr ?segs mx ?a ?bs |- _ =>
      lazymatch goal with
      | _ : mapped mx a _ |- _ => fail
      | _ => let M := fresh "MAP" in
             pose proof (u8arr_mapped L mx a bs H ltac:(off_image_solve L)) as M;
             try rewrite !Arr.upd_length in M
      end
  | H : stk ?segs mx ?lo ?hi |- _ =>
      lazymatch goal with
      | _ : mapped mx lo _ |- _ => fail
      | _ => let M := fresh "MAP" in
             pose proof (stk_mapped (L:=L) mx lo hi lo (hi - lo) H ltac:(lia) ltac:(lia) ltac:(lia)) as M
      end
  end.

Ltac pose_cranges L A mx AINVx :=
  repeat match goal with
  | H : Step.rw_cells ?segs mx ?a ?cs |- _ =>
      lazymatch goal with
      | _ : crange A mx a _ |- _ => fail
      | _ => let C := fresh "CR" in
             first [ match goal with LV : a_live A a = Some ?n |- _ =>
                       pose proof (crange_block (L:=L) A mx _ a n a (Z.of_nat (Cells.cells_size cs)) AINVx LV
                                     ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as C end
                   | pose proof (crange_stack (L:=L) A mx _ a (Z.of_nat (Cells.cells_size cs)) AINVx
                                     ltac:(pose proof alloc_ceiling_val; cbn; lia) ltac:(cbn; lia)
                                     (rw_cells_mapped L mx a cs H ltac:(off_image_solve L))) as C ];
             cbn [Cells.cells_size Cells.csize Nat.add length app] in C
      end
  | H : Arr.u8arr ?segs mx ?a ?bs |- _ =>
      lazymatch goal with
      | _ : crange A mx a _ |- _ => fail
      | _ => let C := fresh "CR" in
             first [ match goal with LV : a_live A a = Some ?n |- _ =>
                       pose proof (crange_block (L:=L) A mx _ a n a (Z.of_nat (length bs)) AINVx LV
                                     ltac:(lia) ltac:(try rewrite !Arr.upd_length; lia) ltac:(lia)) as C end
                   | pose proof (crange_stack (L:=L) A mx _ a (Z.of_nat (length bs)) AINVx
                                     ltac:(pose proof alloc_ceiling_val; cbn; lia) ltac:(lia)
                                     (u8arr_mapped L mx a bs H ltac:(off_image_solve L))) as C ];
             try rewrite !Arr.upd_length in C
      end
  end.


Section S3.
  Context {Clg : Ceiling} (L : AllocLayout) {AI : AllocSpec L}.   (* [comment removed for export] *)
  Let segs := al_segs L.
  (* [comment removed for export] *)
  Lemma bytes_at_mapped : forall m a bs,
    bytes_at segs m a bs -> off_image L a (Z.of_nat (length bs)) ->
    mapped m a (Z.of_nat (length bs)).
  Proof.
    unfold off_image. (intros m a bs; (first [ intro dR_23; dand3 dR_23 as B0 B1 B | intros (B0 & B1 & B) ]); intros Ha i Hi E).
    specialize (B (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in B by lia.
    unfold mrd, wa in B. rewrite E in B. subst segs.
    rewrite (as_seg_rom_outside (L:=L)) in B by (unfold in_image; rewrite unsigned_lit; lia).
    destruct (nth_error bs (Z.to_nat i)) eqn:En; [discriminate|]. apply nth_error_None in En. lia.
  Qed.
End S3.
