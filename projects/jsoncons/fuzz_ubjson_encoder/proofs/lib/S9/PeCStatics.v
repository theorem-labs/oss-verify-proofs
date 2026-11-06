(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk HeapIface LibIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEST.

Section Statics.
Variable segs : list Segment. Context {bmK : BMode}.
Variable A : pm_addrs.
Variable E : pe_addrs.

Abbreviation st := PMST.st.
Abbreviation st_loc := PMST.st_loc.
Abbreviation st_sys := PMST.st_sys.
Abbreviation st_err := PMST.st_err.
Abbreviation g0 := PMST.g0.
Abbreviation loc_ok := (PMST.loc_ok segs A).
Abbreviation sys_ok := (PMST.sys_ok segs A).
Abbreviation base_ok := (PMST.base_ok segs A).
Abbreviation addrs_wf := (PMST.addrs_wf A).
Abbreviation dep := (PMST.dep A).
Abbreviation aw_rw := (PMST.aw_rw A).
Abbreviation aw_canary := (PMST.aw_canary A).
Abbreviation aw_errg := (PMST.aw_errg A).
Abbreviation aw_sysg := (PMST.aw_sysg A).
Abbreviation aw_gloc := (PMST.aw_gloc A).
Abbreviation aw_atexit := (PMST.aw_atexit A).
Abbreviation aw_nl := (PMST.aw_nl A).
Abbreviation aw_ll := (PMST.aw_ll A).
Abbreviation aw_locfoot := (PMST.aw_locfoot A).
Abbreviation aw_gloc_in := (PMST.aw_gloc_in A).
Abbreviation in_foot_errg := (PMST.in_foot_errg A).
Abbreviation in_foot_sysg := (PMST.in_foot_sysg A).
Abbreviation in_foot_loc := (PMST.in_foot_loc A).
Abbreviation in_foot_atexit := (PMST.in_foot_atexit A).
Abbreviation in_foot_nl := (PMST.in_foot_nl A).
Abbreviation in_foot_ll := (PMST.in_foot_ll A).

Definition atexit_st (M : word -> option byte) (reg : bool) : Prop :=
  let X := pa_atexit A in
     L5.img_clear M X (X + 8)
  /\ L5.u32_at segs M (X + 8) (if reg then 2 else 1)
  /\ L5.img_clear M (X + 12) (X + 16)
  /\ L5.u64_at segs M (X + 16) (X + 24)
  /\ L5.img_clear M (X + 24) (X + 32)
  /\ L5.u64_at segs M (X + 32) (pe_drv_call E)
  /\ (if reg then L5.u64_at segs M (X + 40) (pa_errcat_dtor A) else L5.img_clear M (X + 40) (X + 48))
  /\ L5.img_clear M (X + 48) (X + 288)
  /\ L5.u64_at segs M (X + 288) (pe_drv_guard E)
  /\ (if reg then L5.u64_at segs M (X + 296) (pa_errcat_obj A) else L5.img_clear M (X + 296) (X + 304))
  /\ L5.img_clear M (X + 304) (X + 544).

Definition ax_img : list (Z * Z) :=
  let X := pa_atexit A in [(X, X + 8); (X + 12, X + 16); (X + 24, X + 32); (X + 40, X + 288); (X + 296, X + 544)].
Definition ax_cells : list (Z * Z * Z) :=
  let X := pa_atexit A in [(X + 8, 4, 1); (X + 16, 8, X + 24); (X + 32, 8, pe_drv_call E); (X + 288, 8, pe_drv_guard E)].

Definition pm_foot_lib : list (Z * Z) :=
  [(pa_errcat_guard A, pa_errcat_guard A + 2); (pa_syscat_guard A, pa_syscat_guard A + 2)] ++ pa_loc_foot A.

Definition err_ok (M : word -> option byte) (b : bool) : Prop :=
  (if b then L5.u8_at segs M (pa_errcat_guard A) 1 else L5.img_clear M (pa_errcat_guard A) (pa_errcat_guard A + 2))
  /\ atexit_st M b.

Definition ls_ok (g : st) (M : word -> option byte) : Prop :=
  base_ok M /\ loc_ok M (st_loc g) /\ sys_ok M (st_sys g) /\ err_ok M (st_err g).

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
  pose proof (aw_atexit WF) as HX. unfold atexit_st. cbv zeta.
  intros (C1 & S & C2 & H & C3 & F0 & F1 & C4 & A0 & A1 & C5).
  split; [cdep ltac:(intros; apply in_foot_atexit; lia)|].
  split; [apply u32_dep; [lia| intros; apply in_foot_atexit; lia| exact S]|].
  split; [cdep ltac:(intros; apply in_foot_atexit; lia)|].
  split; [apply u64_dep; [lia| intros; apply in_foot_atexit; lia| exact H]|].
  split; [cdep ltac:(intros; apply in_foot_atexit; lia)|].
  split; [apply u64_dep; [lia| intros; apply in_foot_atexit; lia| exact F0]|].
  split; [destruct b; [apply u64_dep; [lia| intros; apply in_foot_atexit; lia| exact F1] | cdep ltac:(intros; apply in_foot_atexit; lia)]|].
  split; [cdep ltac:(intros; apply in_foot_atexit; lia)|].
  split; [apply u64_dep; [lia| intros; apply in_foot_atexit; lia| exact A0]|].
  split; [destruct b; [apply u64_dep; [lia| intros; apply in_foot_atexit; lia| exact A1] | cdep ltac:(intros; apply in_foot_atexit; lia)]|].
  cdep ltac:(intros; apply in_foot_atexit; lia).
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
  - unfold PMST.loc_ok in *. destruct (st_loc g).
    + destruct LOC as (G & P). destruct (aw_gloc_in WF) as (iv & Hin & Hlo & Hhi). split.
      * apply u8_dep; [lia| apply (in_foot_loc iv); [exact Hin| lia]| exact G].
      * apply u64_dep; [lia| intros i Hi; apply (in_foot_loc iv); [exact Hin| lia]| exact P].
    + intros iv Hin. destruct (aw_locfoot WF iv Hin) as [L1 L2].
      apply (clear_dep (fst iv) (snd iv)); [lia| lia| intros a Ha; apply (in_foot_loc iv); assumption| apply LOC; exact Hin].
  - unfold PMST.sys_ok in *. destruct (st_sys g).
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
  intros (C1 & S & C2 & H & C3 & F0 & F1 & C4 & A0 & A1 & C5).
  split; [apply (C (pa_atexit A) (pa_atexit A + 8)); [lia|lia|exact C1]|].
  split; [apply (U4 (pa_atexit A + 8)); [lia|lia|exact S]|].
  split; [apply (C (pa_atexit A + 12) (pa_atexit A + 16)); [lia|lia|exact C2]|].
  split; [apply (U8 (pa_atexit A + 16) (pa_atexit A + 24)); [lia|lia|exact H]|].
  split; [apply (C (pa_atexit A + 24) (pa_atexit A + 32)); [lia|lia|exact C3]|].
  split; [apply (U8 (pa_atexit A + 32) (pe_drv_call E)); [lia|lia|exact F0]|].
  split; [destruct b; [apply (U8 (pa_atexit A + 40) (pa_errcat_dtor A)); [lia|lia|exact F1] | apply (C (pa_atexit A + 40) (pa_atexit A + 48)); [lia|lia|exact F1]]|].
  split; [apply (C (pa_atexit A + 48) (pa_atexit A + 288)); [lia|lia|exact C4]|].
  split; [apply (U8 (pa_atexit A + 288) (pe_drv_guard E)); [lia|lia|exact A0]|].
  split; [destruct b; [apply (U8 (pa_atexit A + 296) (pa_errcat_obj A)); [lia|lia|exact A1] | apply (C (pa_atexit A + 296) (pa_atexit A + 304)); [lia|lia|exact A1]]|].
  apply (C (pa_atexit A + 304) (pa_atexit A + 544)); [lia|lia|exact C5].
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
  lk_init_foot : forall iv, In iv pm_foot_lib -> exists iv', In iv' (ll_init_img Lay) /\ fst iv' <= fst iv /\ snd iv <= snd iv';

  lk_init_ax_img : forall iv, In iv ax_img -> exists iv', In iv' (ll_init_img Lay) /\ fst iv' <= fst iv /\ snd iv <= snd iv';
  lk_init_ax_cells : forall c, In c ax_cells -> In c (ll_init_cells Lay)
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
  destruct IF as (IMG & _ & _ & _ & _ & _ & _ & GU & HC & REST).
  assert (CELLS : Forall (fun c : Z * Z * Z => cellz (hl_segs (ll_heap Lay)) M (fst (fst c)) (Z.to_nat (snd (fst c))) (snd c)) (ll_init_cells Lay)).
  { repeat match type of REST with _ /\ _ => apply proj2 in REST end. exact REST. }
  rewrite (lk_segs Lay LK) in CELLS. rewrite Forall_forall in CELLS.
  assert (CL : forall iv, In iv pm_foot_lib -> L5.img_clear M (fst iv) (snd iv)).
  { intros iv Hin. destruct (lk_init_foot Lay LK iv Hin) as (iv' & Hin' & H1 & H2). intros i Hi. apply (IMG iv' i Hin'). lia. }
  assert (CA : forall iv, In iv ax_img -> L5.img_clear M (fst iv) (snd iv)).
  { intros iv Hin. destruct (lk_init_ax_img Lay LK iv Hin) as (iv' & Hin' & H1 & H2). intros i Hi. apply (IMG iv' i Hin'). lia. }
  assert (CC : forall c, In c ax_cells -> cellz segs M (fst (fst c)) (Z.to_nat (snd (fst c))) (snd c)).
  { intros c Hin. apply CELLS. apply (lk_init_ax_cells Lay LK). exact Hin. }
  unfold ls_ok, PMST.g0. cbn [PMST.st_loc PMST.st_sys PMST.st_err].
  split; [|split; [|split]].
  - split; [|split; [|split]].
    + destruct (lk_init_ro Lay LK) as (iv & Hin & H1 & H2). intros i Hi. apply (IMG iv i Hin). lia.
    + exists canary. split; [exact HC|]. unfold cellz in GU. rewrite (lk_guard Lay LK), (lk_segs Lay LK) in GU. exact GU.
    + destruct (lk_init_initc Lay LK (pa_need_locks A, pa_need_locks A + 1) ltac:(cbn; auto)) as (iv' & Hin' & H1 & H2).
      intros i Hi. apply (IMG iv' i Hin'). cbn [fst snd] in *. lia.
    + destruct (lk_init_initc Lay LK (pa_locale_lock A, pa_locale_lock A + 4) ltac:(cbn; auto)) as (iv' & Hin' & H1 & H2).
      intros i Hi. apply (IMG iv' i Hin'). cbn [fst snd] in *. lia.
  - unfold PMST.loc_ok. intros iv Hin. apply CL. unfold pm_foot_lib. cbn [app]. right. right. exact Hin.
  - unfold PMST.sys_ok. apply (CL (pa_syscat_guard A, pa_syscat_guard A + 2)). unfold pm_foot_lib. cbn. auto.
  - split.
    + apply (CL (pa_errcat_guard A, pa_errcat_guard A + 2)). unfold pm_foot_lib. cbn. auto.
    + unfold atexit_st. cbv zeta.
      split; [apply (CA (pa_atexit A, pa_atexit A + 8)); cbn; auto|].
      split; [apply (CC (pa_atexit A + 8, 4, 1)); cbn; auto|].
      split; [apply (CA (pa_atexit A + 12, pa_atexit A + 16)); cbn; auto|].
      split; [apply (CC (pa_atexit A + 16, 8, pa_atexit A + 24)); cbn; auto|].
      split; [apply (CA (pa_atexit A + 24, pa_atexit A + 32)); cbn; auto|].
      split; [apply (CC (pa_atexit A + 32, 8, pe_drv_call E)); cbn; auto 6|].
      split; [intros i Hi; apply (CA (pa_atexit A + 40, pa_atexit A + 288)); cbn; [auto 6| lia]|].
      split; [intros i Hi; apply (CA (pa_atexit A + 40, pa_atexit A + 288)); cbn; [auto 6| lia]|].
      split; [apply (CC (pa_atexit A + 288, 8, pe_drv_guard E)); cbn; auto 7|].
      split; [intros i Hi; apply (CA (pa_atexit A + 296, pa_atexit A + 544)); cbn; [auto 7| lia]|].
      intros i Hi; apply (CA (pa_atexit A + 296, pa_atexit A + 544)); cbn; [auto 7| lia].
Qed.

End Statics.
End PEST.
