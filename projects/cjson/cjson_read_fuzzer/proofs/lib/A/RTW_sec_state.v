(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS2.LNodesMM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep RT_kit CJ_iface RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_secz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_secz.RT_artZ.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_front.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_secz RT_sec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition sec_grow (st : rtstate) : bool := nsec st =? st_nreserved st.

Definition st_secreg (st : rtstate) (mb n : Z) : rtstate :=
  match st with
  | mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5 =>
    mkRT a1 a2 a3 a4 a5 a6 a7 (a8 + (if zlen a9 =? a8 then 2^14 else 0)) (a9 ++ [(mb, n)]) a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP ((mb, n) :: SP) QP b4 b5
  end.

Lemma st_secreg_fields : forall st mb n,
  st_sec (st_secreg st mb n) = st_sec st ++ [(mb, n)] /\ st_spend (st_secreg st mb n) = (mb, n) :: st_spend st
  /\ st_nreserved (st_secreg st mb n) = st_nreserved st + (if sec_grow st then 2^14 else 0)
  /\ st_pa (st_secreg st mb n) = st_pa st /\ st_t (st_secreg st mb n) = st_t st /\ st_sp0 (st_secreg st mb n) = st_sp0 st
  /\ st_lb (st_secreg st mb n) = st_lb st /\ st_lf (st_secreg st mb n) = st_lf st /\ st_trs (st_secreg st mb n) = st_trs st
  /\ st_depot (st_secreg st mb n) = st_depot st /\ st_ctx (st_secreg st mb n) = st_ctx st
  /\ nsec (st_secreg st mb n) = nsec st + 1.
Proof.
  intros st mb n. destruct st. unfold sec_grow, nsec. cbn. repeat (split; [reflexivity|]).
  unfold zlen. rewrite length_app. cbn. lia.
Qed.

Section W.
  Variables (st : rtstate) (mb n : Z).
  Hypothesis WF : RTWF st.
  Hypothesis HP : bprim n = false.
  Hypothesis Hn : 0 <= n.
  Hypothesis Hneed : needed n <= 2^40.
  Hypothesis Hal : mb mod 4096 = 0.
  Hypothesis Hlo : ablk mb (mb + smapsize n).   (* [comment removed for export] *)
  Hypothesis Hhi : mb + smapsize n <= CEIL.
  Hypothesis FRESH : forall r, In r (rt_ranges st) -> mb + smapsize n <= fst r \/ snd r <= mb.
  Hypothesis ROOM : nsec st < 2^20.

  Lemma RTWF_secreg' : RTWF (st_secreg st mb n).
  Proof. destruct st. eapply RTWF_secreg; eauto. Qed.
  Lemma rt_prov_secreg' : rt_prov (st_secreg st mb n) + (if sec_grow st then PTRC else 0) <= rt_prov st + SEC_SLOT_TAX + 16.
  Proof. unfold sec_grow, nsec. destruct st. eapply (rt_prov_secreg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ WF); eauto. Qed.
  Lemma secreg_rel' : sec_alloc_rel st (st_secreg st mb n) n (sec_alloc_beg mb).
  Proof. destruct st. eapply secreg_rel; eauto. Qed.
  Lemma secreg_same' : same_but_secondary st (st_secreg st mb n).
  Proof. destruct st. eapply secreg_same; eauto. Qed.
  Lemma sec_index_new' : sec_index (st_secreg st mb n) mb = nsec st.
  Proof. destruct st. eapply sec_index_new; eauto. Qed.
  Lemma sec_index_old' : forall x, In x (map fst (st_sec st)) -> sec_index (st_secreg st mb n) x = sec_index st x.
  Proof. destruct st. eapply sec_index_old; eauto. Qed.
  Lemma sec_nth_old' : forall i, 0 <= i < nsec st -> nthz (st_sec (st_secreg st mb n)) i (0,0) = nthz (st_sec st) i (0,0).
  Proof. destruct st. eapply sec_nth_old; eauto. Qed.
  Lemma sec_nth_new' : nthz (st_sec (st_secreg st mb n)) (nsec st) (0,0) = (mb, n).
  Proof. destruct st. eapply sec_nth_new; eauto. Qed.
  Lemma user_new' : ~ In (sec_user mb, n) (all_blocks st).
  Proof. destruct st. eapply user_new; eauto. Qed.
  Lemma mbn_new_spend' : ~ In (mb, n) (st_spend st).
  Proof. destruct st. eapply mbn_new_spend; eauto. Qed.
  Lemma mb_new' : ~ In mb (map fst (st_sec st)).
  Proof. destruct st. eapply mb_new; eauto. Qed.
  Lemma secreg_all_blocks' : all_blocks (st_secreg st mb n) = all_blocks st.
  Proof. destruct st. reflexivity. Qed.
  Lemma RTMODEL_secreg' : forall mo, RTMODEL st mo -> mb + smapsize n <= 2^64 -> sec_plain mo mb (smapsize n) ->
    RTMODEL (st_secreg st mb n) (mm_add_map (wz mb) (wz (smapsize n)) mo).
  Proof. intros mo HM HB PL. destruct st. eapply RTMODEL_secreg; eauto. Qed.
  Lemma GWIN_secreg' : forall m mo g, GWIN st m mo g -> GWIN (st_secreg st mb n) m mo g.
  Proof. intros m mo g H. destruct st. exact H. Qed.
  (* [comment removed for export] *)
  Lemma SWIN_secreg' : forall g g', SWIN st g -> gmono g g' -> sec_win g' mb n -> SWIN (st_secreg st mb n) g'.
  Proof.
    intros g g' HS GM HW e He. pose proof (st_secreg_fields st mb n) as (E1 & _). rewrite E1 in He.
    apply in_app_iff in He as [He|[<-|[]]]; [exact (SWIN_mono st g g' HS GM e He)| exact HW].
  Qed.
  Lemma RTSH_secreg' : forall x, RTSH (st_secreg st mb n) x <-> RTSH st x.
  Proof. intros x. destruct st. unfold RTSH. cbn. tauto. Qed.

  Lemma secreg_fixed_site' : forall mo, LOK asegs mo -> RTMODEL st mo -> sec_grow st = true ->
    mmap_fixed_site mo (st_pa st + 8 * st_nreserved st) PTRARR_BLOCK.
  Proof. intros mo HO HM HG. unfold sec_grow, nsec in HG. destruct st. eapply secreg_fixed_site; eauto. Qed.
  Lemma RTMODEL_commit_pa' : forall mo st0, LOK asegs mo -> RTMODEL st mo -> RTMODEL st0 mo -> sec_grow st = true ->
    RTMODEL st0 (mm_commit (wz (st_pa st + 8 * st_nreserved st)) (wz PTRARR_BLOCK) mo).
  Proof. intros mo st0 HO HM HM0 HG. unfold sec_grow, nsec in HG. destruct st. eapply RTMODEL_commit_pa; eauto. Qed.
  Lemma GWIN_commit_pa' : forall mo st0 m g, LOK asegs mo -> RTMODEL st mo -> GWIN st0 m mo g -> sec_grow st = true ->
    GWIN st0 m (mm_commit (wz (st_pa st + 8 * st_nreserved st)) (wz PTRARR_BLOCK) mo) g.
  Proof. intros mo st0 m g HO HM HG0 HG. unfold sec_grow, nsec in HG. destruct st. eapply GWIN_commit_pa; eauto. Qed.
  Lemma lzf_commit_imp' : forall mo (x : word), LOK asegs mo -> RTMODEL st mo -> sec_grow st = true ->
    lzf (mm_commit (wz (st_pa st + 8 * st_nreserved st)) (wz PTRARR_BLOCK) mo) x = true -> lzf mo x = true.
  Proof. intros mo x HO HM HG. unfold sec_grow, nsec in HG. destruct st. eapply lzf_commit_imp; eauto. Qed.
End W.


End CeilWrap.
