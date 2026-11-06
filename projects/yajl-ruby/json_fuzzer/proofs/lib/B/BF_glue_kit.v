(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StdioBase Malloc.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanRepFrame AsanDepot.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_base B_iface BF_fakestack_rep BF_place B_bundle B_benv5 B_init5 B_balloc5 B_rtok5 B_bframe BF_tkit BF_alloc_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import LiaA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac lia ::= LiaA.liaA.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma aheap_pres_trans : forall LB LF SP m1 m2 m3,
  aheap_pres bsegs ACONSTS LB LF SP m1 m2 -> aheap_pres bsegs ACONSTS LB LF SP m2 m3 -> aheap_pres bsegs ACONSTS LB LF SP m1 m3.
Proof.
  intros LB LF SP m1 m2 m3 H1 H2 a Ha HC. destruct (H1 a Ha HC) as [E1 W1]. destruct (H2 a Ha HC) as [E2 W2].
  split; [rewrite E2; exact E1| intros W; exact (W2 (W1 W))].
Qed.

Lemma aheap_pres_sp_mono : forall LB LF SP SP' m m',
  aheap_pres bsegs ACONSTS LB LF SP' m m' -> SP' <= SP -> aheap_pres bsegs ACONSTS LB LF SP m m'.
Proof.
  intros LB LF SP SP' m m' H LE a Ha HC. apply H; [exact Ha|].
  destruct HC as [X|X]; [left; lia| right; exact X].
Qed.

(* [comment removed for export] *)
Definition nonempty_ivls (W : list (Z * Z)) : list (Z * Z) := List.filter (fun iv => fst iv <? snd iv) W.
Lemma outside_nonempty : forall W x, outside (nonempty_ivls W) x -> outside W x.
Proof.
  intros W x. induction W as [|[lo hi] W IH]; intros Hx; [exact I|]. cbn [nonempty_ivls List.filter fst snd] in Hx.
  destruct (lo <? hi) eqn:E; cbn [outside] in Hx |- *.
  - destruct Hx as [H1 H2]. split; [exact H1| exact (IH H2)].
  - apply Z.ltb_ge in E. split; [lia| exact (IH Hx)].
Qed.
Lemma munch_nonempty : forall W (m m' : mem), munch W m m' -> munch (nonempty_ivls W) m m'.
Proof. intros W m m' MU. eapply munch_weaken; [| exact MU]. unfold sub_fp. intros x Hx. apply outside_nonempty. exact Hx. Qed.
Lemma nonempty_ivls_In : forall W iv, In iv (nonempty_ivls W) -> In iv W /\ fst iv < snd iv.
Proof. intros W iv H. unfold nonempty_ivls in H. apply filter_In in H as [H1 H2]. apply Z.ltb_lt in H2. auto. Qed.

Lemma disjoint_from_below : forall (W : list (Z * Z)) A k,
  Forall (fun iv => snd iv <= A) W -> disjoint_from W A k.
Proof.
  intros W A k FW. induction W as [|[x y] W IH]; [exact I|]. cbn [disjoint_from].
  pose proof (Forall_inv FW) as F1. cbn [fst snd] in F1. split; [right; exact F1| exact (IH (Forall_inv_tail FW))].
Qed.

Section GK.
Variable E0 : aenv.
Variable FSB0 : Z.
Variable HR0 : list (Z * Z).
Variables L0 RES0 : list (word * word).
Variable EB0 : Z.
Variable PL0 : fs_plumb.
Hypothesis ENV0 : env0_ok5 E0.
Hypothesis PL0OK : pl0_ok5 E0 PL0.

#[local] Notation AHKc := (BF_tkit.AHKc E0 FSB0 HR0 L0 RES0 EB0 PL0).
Ltac cstat := try clear ENV0; try clear PL0OK.
Ltac wfe_open WE :=
  destruct WE as (WE1 & WE2 & WE3 & WE4 & WE5 & WE6 & WE7 & WE8 & WE9 & WE10 & WE11 & WE12 & WE13 & WE14 & WE15 & WE16 & WE17 & WE18 &
                  WE19 & WE20 & WE21 & WE22 & WE23 & WE24 & WE25 & WE26 & WE27 & WE28 & WE29 & WE30 & WE31 & WE32 & WE33 & WE34 & WE35rest).

(* [comment removed for export] *)
Lemma live_block_placed : forall s LB LF m mo blo bsz,
  AHKc s LB LF m mo -> In (blo, bsz) (live_blocks (aps_alloc s)) ->
  0x603000 <= blo /\ blo + bsz <= alloc_ceiling /\ (blo + bsz <= 0x7fff7000 \/ 0x10007fff8000 <= blo) /\ 1 <= bsz /\ blo mod 16 = 0.
Proof.
  intros s LB LF m mo blo bsz AH LIVE. unfold BF_tkit.AHKc in AH. pose proof AH as AH0. ahk_open AH.
  destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ AH0) as [EE _].
  pose proof (live_block_geom E0 FSB0 s mo (mkABlock blo bsz) Hwf Hkern Henv LIVE) as ((P1 & P2 & P3) & AL & _). cbn [ab_addr ab_size] in P1, P2, P3, AL.
  rewrite EE in Hwf. destruct (live_block_loc E0 [] [] (aps_alloc s) blo bsz Hwf LIVE) as (k & cm & _ & _ & _ & U3 & _).
  unfold A_IMG_END in P1. unfold A_LOWAPP_END, A_HIGH_BEG in P3. cstat. repeat split; try assumption.
Qed.

(* [comment removed for export] *)
Lemma aclient_addr_where : forall s LB LF m mo SP a,
  AHKc s LB LF m mo -> aclient_addr ACONSTS LB LF SP a ->
  SP <= a \/ (0x603000 <= a < alloc_ceiling) \/ adrv_static ACONSTS a.
Proof.
  intros s LB LF m mo SP a AH HC. pose proof ceil_range as CR.
  destruct HC as [H|[H|[H|H]]]; [left; exact H| right; left| right; left| right; right; exact H].
  - destruct H as (bb & Hbb & Rbb). destruct (AHK_blocks _ _ _ _ _ _ _ _ s LB LF m mo AH) as (BR & _).
    destruct (BR bb Hbb) as (B1 & B2 & B3 & B4 & B5). cbn [c_img_hi ACONSTS] in B5. cstat. clear -Rbb B4 B5. lia.
  - destruct H as ([Nf ff] & Hff & Rff). cbn [fst snd] in Rff. unfold BF_tkit.AHKc in AH. pose proof AH as AH0. ahk_open AH.
    destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ AH0) as [EE EFS]. rewrite EE, EFS in Hfs.
    pose proof (fframe_geom E0 FSB0 (aps_fs s) LF m Nf ff Hfs Hff) as (GN & G1 & G2 & G3 & G4).
    destruct Henv as (V1 & V2 & V3 & V4 & V5 & V6 & EIN & EF1 & EF2 & _ & EFS' & EI1 & EI2). rewrite EE in *. rewrite EFS in *.
    pose proof (proj1 Hwf) as WE. wfe_open WE. pose proof WE34 as IS. unfold img_sep in IS. rewrite EF1, EF2, EI1 in IS.
    unfold app_mem in V3. rewrite kLowAppEnd_val, kHighMemBeg_val in V3. unfold kFsBytes, ff_bytes, A_SB in *.
    assert (HN01 : Nf = 0 \/ Nf = 1) by (clear -GN; lia).
    cstat. clear -CR Rff G1 G2 V3 V4 IS EI2 HN01.
    destruct HN01 as [-> | ->];
      [change (Z.shiftl 64 0) with 64 in *; change (Z.shiftl 8 0) with 8 in *| change (Z.shiftl 64 1) with 128 in *; change (Z.shiftl 8 1) with 16 in *];
      destruct Rff as [Rff|Rff]; (split; [| ]); Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma aheap_pres_shell : forall s LB LF m mo W m' SP,
  AHKc s LB LF m mo -> munch W m m' -> wmono bsegs m m' -> alloc_ceiling <= SP ->
  Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= SP) \/ (c_errno ACONSTS <= fst iv /\ snd iv <= c_errno ACONSTS + 4)) W ->
  aheap_pres bsegs ACONSTS LB LF SP m m'.
Proof.
  intros s LB LF m mo W m' SP AH MU WM HSP FW a Ha HC. split; [| intros X; exact (WM _ X)].
  apply MU. rewrite wa_unsigned by exact Ha. eapply outside_of_Forall; [exact FW|]. intros iv Hiv X. cbn beta in Hiv. cbn [c_errno ACONSTS] in Hiv. pose proof ceil_range as CR.
  destruct (aclient_addr_where _ _ _ _ _ _ _ AH HC) as [C|[C|C]]; cstat.
  - clear -X C Hiv HSP CR. lia.
  - clear -X C Hiv HSP CR. lia.
  - unfold adrv_static in C. cbn [c_seg3_lo c_seg3_hi c_initialized c_ystat_lo c_ystat_hi ACONSTS] in C. clear -X C Hiv HSP CR. lia.
Qed.

(* [comment removed for export] *)
Lemma aw_ok_below : forall a a' mo' lo sp iv,
  aw_ok E0 a a' lo sp iv -> AWf E0 [] [] a -> AWf E0 [] [] a' -> AKern E0 a' mo' ->
  fst iv < snd iv -> snd iv <= sp \/ snd iv <= alloc_ceiling.
Proof.
  intros a a' mo' lo sp iv AW WF WF' K' NE. pose proof ceil_range as CR.
  pose proof (proj1 WF') as WE. wfe_open WE.
  destruct ENV0 as (N1 & N2 & N3 & N4 & _).
  unfold aw_ok in AW. cbn [fst snd] in AW.
  destruct AW as [X|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]].
  - left. cstat. clear -X. lia.
  - right. destruct X as (r & Hr & R1 & R2). pose proof (img_mut_low r Hr) as L. cstat. clear -R2 L CR. lia.
  - right. destruct X as (r & Hr & R1 & R2). unfold arep_thr_ranges in Hr.
    unfold kThrStackTop, kThrQCache, kThrCache, kPerClassSize, kNumClasses, kThrCacheStats, kThrStats, kThrUnwinding in Hr.
    cbn [In] in Hr. cstat. clear -Hr R2 WE15. decompose [or] Hr; try contradiction; subst r; cbn [fst snd] in R2; lia.
  - right. unfold kResvLen in *. cstat. clear -X WE5. lia.
  - right. unfold kPtrArrayLen in *. cstat. clear -X WE17. lia.
  - right. destruct X as (sc & Hsc & R1 & R2).
    assert (G : sc_map_beg sc + sc_map_size sc <= alloc_ceiling).
    { destruct Hsc as [Hsc|Hsc].
      - pose proof WF as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & Q & _). exact Q.
      - pose proof WF' as (_ & _ & _ & _ & _ & (_ & _ & S3 & _) & _). destruct (S3 sc Hsc) as (_ & _ & Q & _). exact Q. }
    cstat. clear -R2 G. lia.
  - right. destruct X as (b & [<-|Hb] & R1 & R2); [destruct N3 as (_ & Q & _); cstat; clear -R2 Q; lia|].
    destruct (ak_blocks_sep _ _ _ K' b kDepotNodeBlockBytes (or_introl (conj Hb eq_refl))) as (_ & B2 & _).
    cstat. clear -R2 B2. lia.
  - right. destruct X as (b & [<-|Hb] & R1 & R2); [destruct N4 as (_ & Q & _); cstat; clear -R2 Q; lia|].
    destruct (ak_blocks_sep _ _ _ K' b kStoreBlockBytes (or_intror (conj Hb eq_refl))) as (_ & B2 & _).
    cstat. clear -R2 B2. lia.
  - right. destruct X as ([(R1 & R2)|(R1 & R2)] & _); rewrite ?kHighMemBeg_val, ?kLowAppEnd_val in R2; unfold A_SB in R2; cstat; clear -R2 CR; lia.
Qed.

(* [comment removed for export] *)
Lemma shell_cells_pres : forall a a' mo' lo sp W (m m' : mem) A cs,
  munch W m m' -> wmono bsegs m m' -> Forall (aw_ok E0 a a' lo sp) W ->
  AWf E0 [] [] a -> AWf E0 [] [] a' -> AKern E0 a' mo' ->
  sp <= A -> alloc_ceiling <= A ->
  rw_cells bsegs m A cs -> rw_cells bsegs m' A cs.
Proof.
  intros a a' mo' lo sp W m m' A cs MU WM FW WF WF' K' H1 H2 RC.
  eapply rw_cells_transport; [exact RC| exact (munch_nonempty _ _ _ MU)| exact WM|].
  apply disjoint_from_below. apply Forall_forall. intros iv Hiv. apply nonempty_ivls_In in Hiv as [Hiv LT].
  pose proof (proj1 (Forall_forall _ _) FW iv Hiv) as F1.
  destruct (aw_ok_below a a' mo' lo sp iv F1 WF WF' K' LT); cstat; clear -H H1 H2; lia.
Qed.

(* [comment removed for export] *)
Definition imgU (x : Z) : Prop := 0x10000 <= x < 0x603000 /\ ~ in_cells img_mut x.
Lemma adrv_static_imgU : forall x, adrv_static ACONSTS x -> imgU x.
Proof.
  intros x H. unfold adrv_static in H. cbn [c_seg3_lo c_seg3_hi c_initialized c_ystat_lo c_ystat_hi ACONSTS] in H.
  split; [cstat; clear -H; lia|]. intros (c & Hc & R). unfold img_mut in Hc.
  cbn [aic_instance aic_internal_alloc_initialized aic_internal_allocator_instance aic_theDepot aic_stackStore both_ic c_errno ACONSTS] in Hc.
  cbn [In] in Hc. cstat. decompose [or] Hc; try contradiction; subst c; cbn [fst snd] in R; clear -H R; lia.
Qed.
Lemma rtU_where2 : forall a, (fun (_ : aenv) (x : Z) => imgU x) E0 a -> (0x10000 <= a < 0x603000 /\ ~ in_cells img_mut a) \/ rt_high2 E0 PL0 a.
Proof. intros a H. left. exact H. Qed.
Lemma soU_where2 : forall a, imgU a -> 0x10000 <= a < 0x603000 /\ ~ in_cells img_mut a.
Proof. intros a H. exact H. Qed.

Theorem aw_client_pres : forall s LB LF m mo (a' : astate) (mo' : Model) (m' : mem) (W : list (Z * Z)) (lo usp : Z) (LB' : list ablock),
  AHKc s LB LF m mo -> AWf E0 [] [] a' -> AKern E0 a' mo' ->
  munch W m m' -> wmono bsegs m m' -> Forall (aw_ok E0 (aps_alloc s) a' lo usp) W -> alloc_ceiling <= lo -> lo <= usp ->
  (forall b, In b LB' -> In b LB /\ Forall (fun iv => snd iv <= fst iv \/ snd iv <= ab_addr b \/ ab_addr b + ab_size b <= fst iv) W) ->
  aheap_pres bsegs ACONSTS LB' LF usp m m'.
Proof.
  intros s LB LF m mo a' mo' m' W lo usp LB' AH WF' K' MU WM FW LOC LOU SUB z Hz HC.
  split; [| intros X; exact (WM _ X)].
  unfold BF_tkit.AHKc in AH. pose proof AH as AH0. ahk_open AH. destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ AH0) as [EE EFS].
  rewrite EE in Hwf, Hfs. rewrite EFS in Hfs.
  assert (F4K : FSB0 mod 4096 = 0) by (destruct Hfs as (G1 & _); exact G1).
  assert (SF : sfacts E0 FSB0 PL0) by (apply (sfacts_of E0 FSB0 PL0 PL0OK s); [exact Hwf| exact Henv| reflexivity| exact F4K]).
  (* [comment removed for export] *)
  assert (REST : forall x, fs_fp FSB0 x \/ imgU x -> m' (wa x) = m (wa x)).
  { intros x Hx. eapply (aw_munch_rest E0 FSB0 PL0 ENV0 PL0OK (fun _ y => imgU y) rtU_where2 imgU soU_where2 (aps_alloc s) a' mo' lo usp W m m' x SF Hwf WF' K' LOC MU FW).
    unfold rest_fp. destruct Hx as [Hx|Hx]; [left; exact Hx| do 5 right; left; exact Hx]. }
  destruct HC as [HC|[HC|[HC|HC]]].
  - (* [comment removed for export] *)
    apply MU. rewrite wa_unsigned by exact Hz. eapply outside_of_Forall; [exact FW|]. intros iv AW Hin.
    destruct (aw_ok_below (aps_alloc s) a' mo' lo usp iv AW Hwf WF' K' ltac:(clear -Hin; lia)) as [X|X]; cstat; [clear -X HC Hin LOU; lia| clear -X HC Hin LOC LOU; lia].
  - (* [comment removed for export] *)
    destruct HC as (b & Hb & Rb). destruct (SUB b Hb) as [_ AV].
    apply MU. rewrite wa_unsigned by exact Hz. eapply outside_of_Forall; [exact AV|]. intros iv X Hin. cbn beta in X.
    cstat. clear -X Rb Hin. lia.
  - (* [comment removed for export] *)
    apply REST. left. destruct HC as ([Nf ff] & Hff & Rff). cbn [fst snd] in Rff.
    pose proof (fframe_geom E0 FSB0 (aps_fs s) LF m Nf ff Hfs Hff) as (GN & G1 & G2 & _).
    unfold fs_fp, fs_shadow, kFsBytes, ff_bytes, FS_SB, A_SB in *.
    assert (HN01 : Nf = 0 \/ Nf = 1) by (clear -GN; lia). cstat. clear -Rff G1 G2 HN01 F4K.
    destruct HN01 as [-> | ->];
      [change (Z.shiftl 64 0) with 64 in *; change (Z.shiftl 8 0) with 8 in *| change (Z.shiftl 64 1) with 128 in *; change (Z.shiftl 8 1) with 16 in *];
      (destruct Rff as [Rff|Rff]; [left| right]); Z.div_mod_to_equations; lia.
  - (* [comment removed for export] *)
    apply REST. right. exact (adrv_static_imgU z HC).
Qed.

(* [comment removed for export] *)
Corollary aw_client_pres_all : forall s LB LF m mo W m' mo' a' lo sp,
  AHKc s LB LF m mo -> alloc_ceiling <= lo -> lo <= sp -> munch W m m' -> wmono bsegs m m' ->
  Forall (aw_ok E0 (aps_alloc s) a' lo sp) W ->
  Forall (fun iv => forall blo bsz, In (blo, bsz) (live_blocks (aps_alloc s)) -> snd iv <= fst iv \/ snd iv <= blo \/ blo + bsz <= fst iv) W ->
  AWf E0 [] [] a' -> AKern E0 a' mo' ->
  aheap_pres bsegs ACONSTS LB LF sp m m'.
Proof.
  intros s LB LF m mo W m' mo' a' lo sp H LOC LOU MU WM FW AV WF' K'.
  eapply aw_client_pres; [exact H| exact WF'| exact K'| exact MU| exact WM| exact FW| exact LOC| exact LOU|].
  intros b Hb. split; [exact Hb|]. apply Forall_forall. intros iv Hiv.
  unfold BF_tkit.AHKc in H. pose proof H as H0. ahk_open H. apply (proj1 (Forall_forall _ _) AV iv Hiv (ab_addr b) (ab_size b)).
  exact (blocks_match_In _ _ _ Hbm Hb).
Qed.

(* [comment removed for export] *)
Theorem aw_client_pres_nw : forall s LB LF m mo (a' : astate) (mo' : Model) (m' : mem) (W : list (Z * Z)) (lo usp : Z) (LB' : list ablock),
  AHKc s LB LF m mo -> AWf E0 [] [] a' -> AKern E0 a' mo' ->
  munch W m m' -> Forall (aw_ok E0 (aps_alloc s) a' lo usp) W -> alloc_ceiling <= lo -> lo <= usp ->
  (forall b, In b LB' -> In b LB /\ Forall (fun iv => snd iv <= fst iv \/ snd iv <= ab_addr b \/ ab_addr b + ab_size b <= fst iv) W) ->
  aheap_pres bsegs ACONSTS LB' LF usp m m'.
Proof.
  intros s LB LF m mo a' mo' m' W lo usp LB' AH WF' K' MU FW LOC LOU SUB z Hz HC.
  assert (E : m' (wa z) = m (wa z)).
  { unfold BF_tkit.AHKc in AH. pose proof AH as AH0. ahk_open AH. destruct (AHK_env _ _ _ _ _ _ _ _ _ _ _ _ _ AH0) as [EE EFS].
    rewrite EE in Hwf, Hfs. rewrite EFS in Hfs.
    assert (F4K : FSB0 mod 4096 = 0) by (destruct Hfs as (G1 & _); exact G1).
    assert (SF : sfacts E0 FSB0 PL0) by (apply (sfacts_of E0 FSB0 PL0 PL0OK s); [exact Hwf| exact Henv| reflexivity| exact F4K]).
    assert (REST : forall x, fs_fp FSB0 x \/ imgU x -> m' (wa x) = m (wa x)).
    { intros x Hx. eapply (aw_munch_rest E0 FSB0 PL0 ENV0 PL0OK (fun _ y => imgU y) rtU_where2 imgU soU_where2 (aps_alloc s) a' mo' lo usp W m m' x SF Hwf WF' K' LOC MU FW).
      unfold rest_fp. destruct Hx as [Hx|Hx]; [left; exact Hx| do 5 right; left; exact Hx]. }
    destruct HC as [HC|[HC|[HC|HC]]].
    - apply MU. rewrite wa_unsigned by exact Hz. eapply outside_of_Forall; [exact FW|]. intros iv AW Hin.
      destruct (aw_ok_below (aps_alloc s) a' mo' lo usp iv AW Hwf WF' K' ltac:(clear -Hin; lia)) as [X|X]; cstat; [clear -X HC Hin LOU; lia| clear -X HC Hin LOC LOU; lia].
    - destruct HC as (b & Hb & Rb). destruct (SUB b Hb) as [_ AV].
      apply MU. rewrite wa_unsigned by exact Hz. eapply outside_of_Forall; [exact AV|]. intros iv X Hin. cbn beta in X.
      cstat. clear -X Rb Hin. lia.
    - apply REST. left. destruct HC as ([Nf ff] & Hff & Rff). cbn [fst snd] in Rff.
      pose proof (fframe_geom E0 FSB0 (aps_fs s) LF m Nf ff Hfs Hff) as (GN & G1 & G2 & _).
      unfold fs_fp, fs_shadow, kFsBytes, ff_bytes, FS_SB, A_SB in *.
      assert (HN01 : Nf = 0 \/ Nf = 1) by (clear -GN; lia). cstat. clear -Rff G1 G2 HN01 F4K.
      destruct HN01 as [-> | ->];
        [change (Z.shiftl 64 0) with 64 in *; change (Z.shiftl 8 0) with 8 in *| change (Z.shiftl 64 1) with 128 in *; change (Z.shiftl 8 1) with 16 in *];
        (destruct Rff as [Rff|Rff]; [left| right]); Z.div_mod_to_equations; lia.
    - apply REST. right. exact (adrv_static_imgU z HC). }
  split; [exact E|]. unfold wview. rewrite E. intros X. exact X.
Qed.

End GK.
End RC__1.
