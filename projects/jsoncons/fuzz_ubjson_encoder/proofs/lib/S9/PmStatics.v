(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk HeapIface LibIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMST.

Record st : Type := ST { st_loc : bool; st_sys : bool; st_err : bool }.
Definition g0 : st := ST false false false.

Definition st_le (g g' : st) : Prop :=
  (st_loc g = true -> st_loc g' = true) /\ (st_sys g = true -> st_sys g' = true) /\ (st_err g = true -> st_err g' = true).

Section Statics.
Variable segs : list Segment. Context {bmK : BMode}.
Variable A : pm_addrs.

Definition img_clear_l (M : word -> option byte) (l : list (Z * Z)) : Prop :=
  forall iv, In iv l -> L5.img_clear M (fst iv) (snd iv).

Definition atexit_st (M : word -> option byte) (reg : bool) : Prop :=
  let X := pa_atexit A in
  if reg then
       L5.img_clear M X (X + 8) /\ L5.u32_at segs M (X + 8) 1 /\ L5.img_clear M (X + 12) (X + 16)
    /\ L5.u64_at segs M (X + 16) (X + 24) /\ L5.img_clear M (X + 24) (X + 32)
    /\ L5.u64_at segs M (X + 32) (pa_errcat_dtor A) /\ L5.img_clear M (X + 40) (X + 288)
    /\ L5.u64_at segs M (X + 288) (pa_errcat_obj A) /\ L5.img_clear M (X + 296) (X + 544)
  else L5.img_clear M X (X + 544).

Definition loc_ok (M : word -> option byte) (b : bool) : Prop :=
  if b then L5.u8_at segs M (pa_glocale A + 40) 1 /\ L5.u64_at segs M (pa_glocale A + 32) (pa_classic_imp A)
  else img_clear_l M (pa_loc_foot A).
Definition sys_ok (M : word -> option byte) (b : bool) : Prop :=
  if b then L5.u8_at segs M (pa_syscat_guard A) 1 else L5.img_clear M (pa_syscat_guard A) (pa_syscat_guard A + 2).
Definition err_ok (M : word -> option byte) (b : bool) : Prop :=
  (if b then L5.u8_at segs M (pa_errcat_guard A) 1 else L5.img_clear M (pa_errcat_guard A) (pa_errcat_guard A + 2))
  /\ atexit_st M b.

Definition base_ok (M : word -> option byte) : Prop :=
  L5.img_clear M 65536 (pa_rw_lo A)
  /\ (exists canary, 0 <= canary < 2 ^ 64 /\ L5.u64_at segs M (pa_canary A) canary)
  /\ L5.img_clear M (pa_need_locks A) (pa_need_locks A + 1)
  /\ L5.img_clear M (pa_locale_lock A) (pa_locale_lock A + 4).

Definition ls_ok (g : st) (M : word -> option byte) : Prop :=
  base_ok M /\ loc_ok M (st_loc g) /\ sys_ok M (st_sys g) /\ err_ok M (st_err g).

Record addrs_wf : Prop := AWF {
  aw_rw : 65536 <= pa_rw_lo A < 2 ^ 40;
  aw_canary : 0 <= pa_canary A < 2 ^ 40;
  aw_errg : 0 <= pa_errcat_guard A < 2 ^ 40;
  aw_sysg : 0 <= pa_syscat_guard A < 2 ^ 40;
  aw_gloc : 0 <= pa_glocale A < 2 ^ 40;
  aw_atexit : 0 <= pa_atexit A < 2 ^ 40;
  aw_nl : 0 <= pa_need_locks A < 2 ^ 40;
  aw_ll : 0 <= pa_locale_lock A < 2 ^ 40;
  aw_locfoot : forall iv, In iv (pa_loc_foot A) -> 0 <= fst iv /\ snd iv < 2 ^ 40;
  aw_gloc_in : exists iv, In iv (pa_loc_foot A) /\ fst iv <= pa_glocale A + 32 /\ pa_glocale A + 41 <= snd iv
}.

Definition dep (a : Z) : Prop :=
  (exists iv, In iv (pm_foot A) /\ fst iv <= a < snd iv) \/ (pa_canary A <= a < pa_canary A + 8)
  \/ (exists iv, In iv (pm_initc A) /\ fst iv <= a < snd iv).

Lemma in_foot_errg a : pa_errcat_guard A <= a < pa_errcat_guard A + 2 -> dep a.
Proof. intros H. left. exists (pa_errcat_guard A, pa_errcat_guard A + 2). split; [unfold pm_foot; cbn; auto| cbn; lia]. Qed.
Lemma in_foot_sysg a : pa_syscat_guard A <= a < pa_syscat_guard A + 2 -> dep a.
Proof. intros H. left. exists (pa_syscat_guard A, pa_syscat_guard A + 2). split; [unfold pm_foot; cbn; auto| cbn; lia]. Qed.
Lemma in_foot_loc iv a : In iv (pa_loc_foot A) -> fst iv <= a < snd iv -> dep a.
Proof. intros Hin H. left. exists iv. split; [|exact H]. unfold pm_foot. cbn [app]. right. right. apply in_or_app. left. exact Hin. Qed.
Lemma in_foot_atexit a : pa_atexit A <= a < pa_atexit A + 544 -> dep a.
Proof.
  intros H. left. exists (pa_atexit A, pa_atexit A + 544). split; [|cbn; lia].
  unfold pm_foot. cbn [app]. right. right. apply in_or_app. right. cbn. auto.
Qed.
Lemma in_foot_nl a : pa_need_locks A <= a < pa_need_locks A + 1 -> dep a.
Proof. intros H. right. right. exists (pa_need_locks A, pa_need_locks A + 1). split; [cbn; auto| cbn; lia]. Qed.
Lemma in_foot_ll a : pa_locale_lock A <= a < pa_locale_lock A + 4 -> dep a.
Proof. intros H. right. right. exists (pa_locale_lock A, pa_locale_lock A + 4). split; [cbn; auto| cbn; lia]. Qed.

Section Frame.
Hypothesis WF : addrs_wf.
Variables M M' : word -> option byte.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> dep a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis RO : forall a, 65536 <= a < pa_rw_lo A -> M (Z_to_bv 64 a) = None -> M' (Z_to_bv 64 a) = None.

Lemma clear_dep lo hi : 0 <= lo -> hi < 2 ^ 47 -> (forall a, lo <= a < hi -> dep a) -> L5.img_clear M lo hi -> L5.img_clear M' lo hi.
Proof. intros Hlo Hhi D C i Hi. rewrite AG; [apply C; exact Hi| lia| apply D; exact Hi]. Qed.
Lemma u8_dep a v : 0 <= a < 2 ^ 47 -> dep a -> L5.u8_at segs M a v -> L5.u8_at segs M' a v.
Proof. intros Ha D. apply (L5C.u8_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG; [lia|]. replace i with a by lia. exact D. Qed.
Lemma u32_dep a v : 0 <= a < 2 ^ 47 -> (forall i, a <= i < a + 4 -> dep i) -> L5.u32_at segs M a v -> L5.u32_at segs M' a v.
Proof.
  intros Ha D H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4%nat a); [exact H|lia|cbn; lia|].
  intros i Hi. apply AG; [cbn in Hi; lia|]. apply D. cbn in Hi. lia.
Qed.
Lemma u64_dep a v : 0 <= a < 2 ^ 47 -> (forall i, a <= i < a + 8 -> dep i) -> L5.u64_at segs M a v -> L5.u64_at segs M' a v.
Proof. intros Ha D. apply (L5C.u64_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG; [lia|]. apply D. exact Hi. Qed.

Local Ltac cdep tac := lazymatch goal with |- L5.img_clear _ ?lo ?hi => apply (clear_dep lo hi); [lia| lia| tac| try assumption] end.

Lemma atexit_frame b : atexit_st M b -> atexit_st M' b.
Proof.
  pose proof (aw_atexit WF) as HX. unfold atexit_st. cbv zeta. destruct b.
  - intros (C1 & S & C2 & H & C3 & F0 & C4 & A0 & C5).
    repeat split.
    + cdep ltac:(intros; apply in_foot_atexit; lia).
    + apply u32_dep; [lia| intros; apply in_foot_atexit; lia| exact S].
    + cdep ltac:(intros; apply in_foot_atexit; lia).
    + apply u64_dep; [lia| intros; apply in_foot_atexit; lia| exact H].
    + cdep ltac:(intros; apply in_foot_atexit; lia).
    + apply u64_dep; [lia| intros; apply in_foot_atexit; lia| exact F0].
    + cdep ltac:(intros; apply in_foot_atexit; lia).
    + apply u64_dep; [lia| intros; apply in_foot_atexit; lia| exact A0].
    + cdep ltac:(intros; apply in_foot_atexit; lia).
  - intros C. cdep ltac:(intros; apply in_foot_atexit; lia).
Qed.

Lemma ls_ok_frame g : ls_ok g M -> ls_ok g M'.
Proof.
  intros ((RO0 & (can & Hcan & CAN) & NL & LL) & LOC & SYS & (ERG & ATX)).
  pose proof (aw_rw WF) as Hrw. pose proof (aw_canary WF) as Hcn. pose proof (aw_errg WF) as Heg. pose proof (aw_sysg WF) as Hsg.
  pose proof (aw_gloc WF) as Hgl. pose proof (aw_nl WF) as Hnl. pose proof (aw_ll WF) as Hll.
  split; [|split; [|split]].
  - split; [|split; [|split]].
    + intros i Hi. apply RO; [exact Hi| apply RO0; exact Hi].
    + exists can. split; [exact Hcan|]. apply u64_dep; [lia| intros i Hi; right; left; exact Hi| exact CAN].
    + cdep ltac:(intros; apply in_foot_nl; lia).
    + cdep ltac:(intros; apply in_foot_ll; lia).
  - unfold loc_ok in *. destruct (st_loc g).
    + destruct LOC as (G & P). destruct (aw_gloc_in WF) as (iv & Hin & Hlo & Hhi). split.
      * apply u8_dep; [lia| apply (in_foot_loc iv); [exact Hin| lia]| exact G].
      * apply u64_dep; [lia| intros i Hi; apply (in_foot_loc iv); [exact Hin| lia]| exact P].
    + intros iv Hin. destruct (aw_locfoot WF iv Hin) as [L1 L2].
      apply (clear_dep (fst iv) (snd iv)); [lia| lia| intros a Ha; apply (in_foot_loc iv); assumption| apply LOC; exact Hin].
  - unfold sys_ok in *. destruct (st_sys g).
    + apply u8_dep; [lia| apply in_foot_sysg; lia| exact SYS].
    + cdep ltac:(intros; apply in_foot_sysg; lia).
  - split.
    + destruct (st_err g).
      * apply u8_dep; [lia| apply in_foot_errg; lia| exact ERG].
      * cdep ltac:(intros; apply in_foot_errg; lia).
    + apply atexit_frame. exact ATX.
Qed.
End Frame.

Lemma atexit_agree (WF : addrs_wf) M M' b :
  (forall i, pa_atexit A <= i < pa_atexit A + 544 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> atexit_st M b -> atexit_st M' b.
Proof.
  intros AG. pose proof (aw_atexit WF) as HX. unfold atexit_st. cbv zeta.
  assert (C : forall lo hi, pa_atexit A <= lo -> hi <= pa_atexit A + 544 -> L5.img_clear M lo hi -> L5.img_clear M' lo hi).
  { intros lo hi H1 H2 CL i Hi. rewrite AG by lia. apply CL. exact Hi. }
  assert (U8 : forall a v, pa_atexit A <= a -> a + 8 <= pa_atexit A + 544 -> L5.u64_at segs M a v -> L5.u64_at segs M' a v).
  { intros a v H1 H2. apply (L5C.u64_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG. lia. }
  assert (U4 : forall a v, pa_atexit A <= a -> a + 4 <= pa_atexit A + 544 -> L5.u32_at segs M a v -> L5.u32_at segs M' a v).
  { intros a v H1 H2 H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4%nat a); [exact H|lia|cbn; lia|]. intros i Hi. apply AG. cbn in Hi. lia. }
  destruct b.
  - intros (C1 & S & C2 & H & C3 & F0 & C4 & A0 & C5).
    split; [apply (C (pa_atexit A) (pa_atexit A + 8)); [lia|lia|exact C1]|].
    split; [apply (U4 (pa_atexit A + 8) 1); [lia|lia|exact S]|].
    split; [apply (C (pa_atexit A + 12) (pa_atexit A + 16)); [lia|lia|exact C2]|].
    split; [apply (U8 (pa_atexit A + 16) (pa_atexit A + 24)); [lia|lia|exact H]|].
    split; [apply (C (pa_atexit A + 24) (pa_atexit A + 32)); [lia|lia|exact C3]|].
    split; [apply (U8 (pa_atexit A + 32) (pa_errcat_dtor A)); [lia|lia|exact F0]|].
    split; [apply (C (pa_atexit A + 40) (pa_atexit A + 288)); [lia|lia|exact C4]|].
    split; [apply (U8 (pa_atexit A + 288) (pa_errcat_obj A)); [lia|lia|exact A0]|].
    apply (C (pa_atexit A + 296) (pa_atexit A + 544)); [lia|lia|exact C5].
  - apply C; lia.
Qed.

Lemma pm_statics_exit g M : ls_ok g M -> atexit_st M (st_err g).
Proof. intros (_ & _ & _ & (_ & H)). exact H. Qed.

Definition TopLS : lib_statics := {| ls_state := st; LibIface.ls_ok := ls_ok; ls_g0 := g0 |}.

Record lay_ok (Lay : lib_layout) : Prop := LAYOK {
  lk_segs : hl_segs (ll_heap Lay) = segs;
  lk_foot : ll_foot Lay = pm_foot A;
  lk_rw : ll_rw_lo Lay = pa_rw_lo A;
  lk_guard : ll_guard Lay = pa_canary A;
  lk_guard_initc : exists iv, In iv (ll_initc Lay) /\ fst iv <= pa_canary A /\ pa_canary A + 8 <= snd iv;
  lk_initc : forall iv, In iv (pm_initc A) -> exists iv', In iv' (ll_initc Lay) /\ fst iv' <= fst iv /\ snd iv <= snd iv';
  lk_init_initc : forall iv, In iv (pm_initc A) -> exists iv', In iv' (ll_init_img Lay) /\ fst iv' <= fst iv /\ snd iv <= snd iv';

  lk_init_ro : exists iv, In iv (ll_init_img Lay) /\ fst iv <= 65536 /\ pa_rw_lo A <= snd iv;
  lk_init_foot : forall iv, In iv (pm_foot A) -> exists iv', In iv' (ll_init_img Lay) /\ fst iv' <= fst iv /\ snd iv <= snd iv'
}.

Lemma pm_statics_frame Lay : addrs_wf -> lay_ok Lay -> lib_statics_frame Lay TopLS.
Proof.
  intros WF LK g M M' H FOOT RO INITC. cbn [LibIface.ls_ok TopLS] in *.
  apply (ls_ok_frame WF M M'); [| |exact H].
  - intros a Ha [(iv & Hin & Hr)|[Hc|(iv & Hin & Hr)]].
    + apply FOOT; [exact Ha|]. exists iv. rewrite (lk_foot Lay LK). split; assumption.
    + apply INITC; [exact Ha|]. left. destruct (lk_guard_initc Lay LK) as (iv & Hin & H1 & H2). exists iv. split; [exact Hin| lia].
    + apply INITC; [exact Ha|]. left. destruct (lk_initc Lay LK iv Hin) as (iv' & Hin' & H1 & H2). exists iv'. split; [exact Hin'| lia].
  - intros a Ha Hn. pose proof (aw_rw WF) as RW. apply RO; [rewrite (lk_rw Lay LK), L5.unsigned_lit by lia; lia| exact Hn].
Qed.

Lemma pm_statics_init Lay : addrs_wf -> lay_ok Lay -> lib_statics_init Lay TopLS.
Proof.
  intros WF LK av uid rnd tid canary hw M IF. cbn [LibIface.ls_ok TopLS ls_g0].
  unfold lib_init_facts in IF. cbv zeta in IF.
  destruct IF as (IMG & _ & _ & _ & _ & _ & _ & GU & HC & _).
  assert (CL : forall iv, In iv (pm_foot A) -> L5.img_clear M (fst iv) (snd iv)).
  { intros iv Hin. destruct (lk_init_foot Lay LK iv Hin) as (iv' & Hin' & H1 & H2). intros i Hi. apply (IMG iv' i Hin'). lia. }
  unfold ls_ok, g0. cbn [st_loc st_sys st_err].
  split; [|split; [|split]].
  - split; [|split; [|split]].
    + destruct (lk_init_ro Lay LK) as (iv & Hin & H1 & H2). intros i Hi. apply (IMG iv i Hin). lia.
    + exists canary. split; [exact HC|]. unfold cellz in GU. rewrite (lk_guard Lay LK), (lk_segs Lay LK) in GU. exact GU.
    + destruct (lk_init_initc Lay LK (pa_need_locks A, pa_need_locks A + 1) ltac:(cbn; auto)) as (iv' & Hin' & H1 & H2).
      intros i Hi. apply (IMG iv' i Hin'). cbn [fst snd] in *. lia.
    + destruct (lk_init_initc Lay LK (pa_locale_lock A, pa_locale_lock A + 4) ltac:(cbn; auto)) as (iv' & Hin' & H1 & H2).
      intros i Hi. apply (IMG iv' i Hin'). cbn [fst snd] in *. lia.
  - unfold loc_ok. intros iv Hin. apply CL. unfold pm_foot. cbn [app]. right. right. apply in_or_app. left. exact Hin.
  - unfold sys_ok. apply (CL (pa_syscat_guard A, pa_syscat_guard A + 2)). unfold pm_foot. cbn. auto.
  - split.
    + apply (CL (pa_errcat_guard A, pa_errcat_guard A + 2)). unfold pm_foot. cbn. auto.
    + unfold atexit_st. cbv zeta. apply (CL (pa_atexit A, pa_atexit A + 544)). unfold pm_foot. cbn [app]. right. right. apply in_or_app. right. cbn. auto.
Qed.

End Statics.
End PMST.
