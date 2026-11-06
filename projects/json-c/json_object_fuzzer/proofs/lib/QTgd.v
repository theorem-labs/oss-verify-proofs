(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH QQIi QdTb QHWH Q1lV Qcrs QUcd QCUT QwAs Qc6I QJFf Qsn5 Qknc QBrp Q2ui Q1KO QNqr QeDS QLiw QFL8 QRGF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.

Import QQIi QdTb QHWH Q1lV.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf Qsn5 QJFf.Mq1 Qknc QBrp Q2ui Q1KO.
Import QNqr QeDS QNqr.Mq0 QeDS.Mq1 QLiw.Mq2.
Import QFL8 QRGF.
Import ListNotations.
Open Scope Z_scope.

Section NodeRulesDrv.
Variable segs : list Segment.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.

Local Notation NS := (nodesA_sound segs LV Hsegs Hsh Hbx Hbc).

Lemma ajv_silent_node : forall (T : QRjH.TSet) (n : node) c msv,
at_nodeA LV segs n msv -> CKv LV c ->
is_spinA n = false -> nsafeA LV n (cfg_model c) ->
(forall mo1 code mo', ~ nexit_raw n mo1 code mo') ->
(forall mo1 rsp mo' evs, nstep_raw LV n mo1 rsp mo' evs -> evs = []) ->
(forall mo1 rsp c', drift LV (cfg_model c) mo1 -> nstep_raw LV n mo1 rsp (cfg_model c') [] -> CKv LV c' ->
AJv segs LV T c' (nret msv rsp)) ->
AJv segs LV T c msv.
Proof.
intros T n c msv Hat [HC Hh] Hsp Hns Hnx Hsil HK. unfold AJv.
apply (vj_silent node segs LV Hwx Hsegs (at_nodeA LV segs) (nstep_raw LV) nexit_raw (nsafeA LV) (xinvA LV) is_spinA rvarA (jsome LV)
(jsome_stable LV) NS (JS segs T) (js_nclosed segs T) n c msv Hat HC Hsp Hns).
- intros mo1 code mo' _. apply Hnx.
- intros rsp mo' evs (mo1 & _ & Hr). exact (Hsil mo1 rsp mo' evs Hr).
- intros rsp c1 (mo1 & Hd & Hr) HC1 Hh1. exact (HK mo1 rsp c1 Hd Hr (conj HC1 Hh1)).
Qed.

Lemma m_fds_with_fds : forall f mo, m_fds (with_fds f mo) = f.   Proof. intros f []; reflexivity. Qed.
Lemma m_fs_with_fds : forall f mo, m_fs (with_fds f mo) = m_fs mo.   Proof. intros f []; reflexivity. Qed.
Lemma vmrel_with_fds : forall f mo, vmrel LV mo (with_fds f mo).
Proof.
intros f mo. split; [destruct mo; reflexivity|]. apply Phi_ext; [split; destruct mo; reflexivity | destruct mo; reflexivity].
Qed.

Lemma cnext_fds : forall c c' mo1 mo2, CKv LV c' ->
drift LV (cfg_model c) mo1 -> (mo2 = mo1 \/ exists f, mo2 = with_fds f mo1) -> drift LV mo2 (cfg_model c') ->
CNEXTv LV c c' /\ m_fs (cfg_model c') = m_fs (cfg_model c) /\ m_fds (cfg_model c') = m_fds mo2 /\ m_fds mo1 = m_fds (cfg_model c).
Proof.
intros c c' mo1 mo2 HCK Hd1 Hm Hd2.
pose proof (drift_frame LV _ _ Hd1) as (F1 & S1 & _). pose proof (drift_frame LV _ _ Hd2) as (F2 & S2 & _).
split; [split; [exact HCK|]|].
- eapply vmrel_trans; [exact (vmrel_drift LV _ _ Hd1)|]. eapply vmrel_trans; [|exact (vmrel_drift LV _ _ Hd2)].
destruct Hm as [-> | (f & ->)]; [apply vmrel_refl | apply vmrel_with_fds].
- split; [|split; [exact F2 | exact F1]].
rewrite S2. destruct Hm as [-> | (f & ->)]; [exact S1 | rewrite m_fs_with_fds; exact S1].
Qed.

Theorem ajv_close : forall (T : QRjH.TSet) fd e c msv,
at_nodeA LV segs (NClose fd) msv -> CKv LV c ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 fd) = Some e ->
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = fd_remove (m_fds (cfg_model c)) (Z_to_bv 64 fd) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (eff0 (Z_to_bv 64 0)))) ->
AJv segs LV T c msv.
Proof.
intros T fd e c msv Hat HCK Hlk HK.
apply (ajv_silent_node T (NClose fd) c msv Hat HCK eq_refl I).
- intros mo1 code mo' [].
- intros mo1 rsp mo' evs (mo2 & Hn & _). cbn [nstep] in Hn. exact (proj1 Hn).
- intros mo1 rsp c' Hd (mo2 & Hn & Hd2) HCK'. cbn [nstep] in Hn. destruct Hn as (_ & _ & Hm).
pose proof (drift_frame LV _ _ Hd) as (F1 & _). rewrite F1, Hlk in Hm. destruct Hm as [-> ->].
destruct (cnext_fds c c' mo1 _ HCK' Hd (or_intror (ex_intro _ _ eq_refl)) Hd2) as (HN & HS & HF & HF1).
apply (HK c' HN); [| exact HS]. rewrite HF, m_fds_with_fds, ?HF1. reflexivity.
Qed.

Theorem ajv_ioctl_winsz : forall (T : QRjH.TSet) fd req c msv,
at_nodeA LV segs (NIoctl fd req) msv -> CKv LV c ->
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (efferr ENOTTY))) ->
AJv segs LV T c msv.
Proof.
intros T fd req c msv Hat HCK HK.
apply (ajv_silent_node T (NIoctl fd req) c msv Hat HCK eq_refl I).
- intros mo1 code mo' [].
- intros mo1 rsp mo' evs (mo2 & Hn & _). cbn [nstep] in Hn. exact (proj1 Hn).
- intros mo1 rsp c' Hd (mo2 & Hn & Hd2) HCK'. cbn [nstep] in Hn. destruct Hn as (_ & -> & ->).
destruct (cnext_fds c c' mo1 _ HCK' Hd (or_introl eq_refl) Hd2) as (HN & HS & HF & HF1).
apply (HK c' HN); [| exact HS]. rewrite HF, ?HF1. reflexivity.
Qed.

Theorem ajv_read_file : forall (T : QRjH.TSet) fd buf count p off data c msv,
at_nodeA LV segs (NRead fd buf count) msv -> CKv LV c ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 fd) = Some (FdFile p off) ->
fs_lookup (m_fs (cfg_model c)) p = Some data ->
let bs := file_read data off (Z_to_bv 64 count) in
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = fd_insert (m_fds (cfg_model c)) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv) ->
m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) []))) ->
AJv segs LV T c msv.
Proof.
intros T fd buf count p off data c msv Hat HCK Hlk Hfs bs HK.
apply (ajv_silent_node T (NRead fd buf count) c msv Hat HCK eq_refl I).
- intros mo1 code mo' [].
- intros mo1 rsp mo' evs (mo2 & Hn & _). cbn [nstep] in Hn. exact (proj1 Hn).
- intros mo1 rsp c' Hd (mo2 & Hn & Hd2) HCK'. cbn [nstep] in Hn. destruct Hn as (_ & Hm).
pose proof (drift_frame LV _ _ Hd) as (F1 & S1 & _). rewrite F1, Hlk, S1, Hfs in Hm. cbn zeta in Hm. destruct Hm as [-> ->].
destruct (cnext_fds c c' mo1 _ HCK' Hd (or_intror (ex_intro _ _ eq_refl)) Hd2) as (HN & HS & HF & HF1).
apply (HK c' HN); [| exact HS]. rewrite HF, m_fds_with_fds, ?HF1. reflexivity.
Qed.

Theorem ajv_read_dir : forall (T : QRjH.TSet) fd buf count c msv,
at_nodeA LV segs (NRead fd buf count) msv -> CKv LV c ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 fd) = Some FdDir ->
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (efferr EISDIR))) ->
AJv segs LV T c msv.
Proof.
intros T fd buf count c msv Hat HCK Hlk HK.
apply (ajv_silent_node T (NRead fd buf count) c msv Hat HCK eq_refl I).
- intros mo1 code mo' [].
- intros mo1 rsp mo' evs (mo2 & Hn & _). cbn [nstep] in Hn. exact (proj1 Hn).
- intros mo1 rsp c' Hd (mo2 & Hn & Hd2) HCK'. cbn [nstep] in Hn. destruct Hn as (_ & Hm).
pose proof (drift_frame LV _ _ Hd) as (F1 & _). rewrite F1, Hlk in Hm. destruct Hm as [-> ->].
destruct (cnext_fds c c' mo1 _ HCK' Hd (or_introl eq_refl) Hd2) as (HN & HS & HF & HF1).
apply (HK c' HN); [| exact HS]. rewrite HF, ?HF1. reflexivity.
Qed.

Lemma open_single : forall (T : QRjH.TSet) path e c msv,
at_nodeA LV segs (NOpen path) msv -> CKv LV c ->
(forall mo1 rsp mo2, drift LV (cfg_model c) mo1 -> nstep (NOpen path) mo1 rsp mo2 [] -> rsp = efferr e /\ mo2 = mo1) ->
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (efferr e))) ->
AJv segs LV T c msv.
Proof.
intros T path e c msv Hat HCK Hone HK.
apply (ajv_silent_node T (NOpen path) c msv Hat HCK eq_refl I).
- intros mo1 code mo' [].
- intros mo1 rsp mo' evs (mo2 & Hn & _). cbn [nstep] in Hn. exact (proj1 Hn).
- intros mo1 rsp c' Hd (mo2 & Hn & Hd2) HCK'. destruct (Hone mo1 rsp mo2 Hd Hn) as [-> ->].
destruct (cnext_fds c c' mo1 _ HCK' Hd (or_introl eq_refl) Hd2) as (HN & HS & HF & HF1).
apply (HK c' HN); [| exact HS]. rewrite HF, ?HF1. reflexivity.
Qed.

Theorem ajv_open_toolong : forall (T : QRjH.TSet) path c msv,
at_nodeA LV segs (NOpen path) msv -> CKv LV c -> (path_max <= length path)%nat ->
(forall c', CNEXTv LV c c' -> m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (efferr ENAMETOOLONG))) ->
AJv segs LV T c msv.
Proof.
intros T path c msv Hat HCK Hlen HK. apply (open_single T path ENAMETOOLONG c msv Hat HCK); [|exact HK].
intros mo1 rsp mo2 _ Hn. cbn [nstep] in Hn. destruct Hn as [_ Hn].
replace (path_max <=? length path)%nat with true in Hn by (symmetry; apply Nat.leb_le; exact Hlen). exact Hn.
Qed.

Theorem ajv_open_empty : forall (T : QRjH.TSet) c msv,
at_nodeA LV segs (NOpen []) msv -> CKv LV c ->
(forall c', CNEXTv LV c c' -> m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (efferr ENOENT))) ->
AJv segs LV T c msv.
Proof.
intros T c msv Hat HCK HK. apply (open_single T [] ENOENT c msv Hat HCK); [|exact HK].
intros mo1 rsp mo2 _ Hn. cbn [nstep] in Hn. destruct Hn as [_ Hn]. cbn in Hn. exact Hn.
Qed.

Theorem ajv_open_absent : forall (T : QRjH.TSet) path c msv,
at_nodeA LV segs (NOpen path) msv -> CKv LV c ->
(length path < path_max)%nat -> path <> [] -> path_eqb path dot_path = false ->
fs_lookup (m_fs (cfg_model c)) path = None ->
(forall c', CNEXTv LV c c' -> m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (efferr ENOENT))) ->
AJv segs LV T c msv.
Proof.
intros T path c msv Hat HCK Hlen Hne Hdot Hfs HK. apply (open_single T path ENOENT c msv Hat HCK); [|exact HK].
intros mo1 rsp mo2 Hd Hn. cbn [nstep] in Hn. destruct Hn as [_ Hn].
replace (path_max <=? length path)%nat with false in Hn by (symmetry; apply Nat.leb_gt; exact Hlen).
destruct path as [|b path']; [contradiction|]. rewrite Hdot in Hn.
pose proof (drift_frame LV _ _ Hd) as (_ & S1 & _). rewrite S1, Hfs in Hn. exact Hn.
Qed.

Local Notation vis := (vj_vis_k node segs LV (at_nodeA LV segs) (nstep_raw LV) nexit_raw (nsafeA LV) (xinvA LV) is_spinA rvarA (jsome LV)
(jsome_stable LV) NS).

Lemma t_emit_nil : forall (T : TSet) tr, T [] -> (t_emit [] T tr <-> T tr).
Proof.
intros T tr H0. unfold t_emit. split.
- intros [Hp|(tr' & -> & Ht)]; [destruct tr; [exact H0 | destruct Hp] | exact Ht].
- intros Ht. right. exists tr. split; [reflexivity | exact Ht].
Qed.

Lemma ajv_open_result : forall (TA TB : QRjH.TSet) path ent c msv,
at_nodeA LV segs (NOpen path) msv -> CKv LV c ->
(forall mo1 rsp mo2 evs, drift LV (cfg_model c) mo1 ->
(nstep (NOpen path) mo1 rsp mo2 evs <-> evs = [] /\ open_result mo1 ent rsp mo2)) ->
fd_lookup (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) = None ->
TA [] -> TB [] ->
(forall e c', In e openat_errnos -> CNEXTv LV c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV TA c' (nret msv (efferr e))) ->
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = fd_insert (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) ent ->
m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV TB c' (nret msv (eff0 (alloc_fd (m_fds (cfg_model c)))))) ->
AJv segs LV (QRjH.t_alt2 TA TB) c msv.
Proof.
intros TA TB path ent c msv Hat [HC Hh] Hst Hfree HA0 HB0 KA KB. unfold AJv.
set (fds0 := m_fds (cfg_model c)) in *.

apply (vis (NOpen path) (fun _ mo' _ => match fd_lookup (m_fds mo') (alloc_fd fds0) with Some _ => TB | None => TA end) _ c msv eq_refl Hat HC I).
- intros r r2 mo' mo2 evs _ Hs. destruct (msim_facts LV _ _ Hs) as (F & _). rewrite F. apply t_eq_refl.
- intros mo1 rsp evs c1 Hd (mo2 & Hn & Hd2) HC1 Hh1 _.
apply (Hst mo1 rsp mo2 evs Hd) in Hn. destruct Hn as [-> Hr].
pose proof (drift_frame LV _ _ Hd) as (F1 & _). pose proof (drift_frame LV _ _ Hd2) as (F2 & _). fold fds0 in F1.
destruct Hr as [(e & He & -> & ->)|(Hf & -> & ->)].
+ destruct (cnext_fds c c1 mo1 _ (conj HC1 Hh1) Hd (or_introl eq_refl) Hd2) as (HN & HS & HF & HF1).
rewrite F2, F1, Hfree. apply (KA e c1 He HN); [rewrite HF, HF1; reflexivity | exact HS].
+ destruct (cnext_fds c c1 mo1 _ (conj HC1 Hh1) Hd (or_intror (ex_intro _ _ eq_refl)) Hd2) as (HN & HS & HF & HF1).
rewrite F2, m_fds_with_fds, F1, fd_lookup_insert, bv_eqb_refl. rewrite ?F1. apply (KB c1 HN); [| exact HS].
rewrite HF, m_fds_with_fds, ?F1. reflexivity.
- intros mo1 Hd tr. pose proof (drift_frame LV _ _ Hd) as (F1 & _). fold fds0 in F1. unfold QRjH.t_alt2. split.
+ intros [Ha|Hb].
* right; left. exists (efferr ENOMEM), mo1, []. split.
{ exists mo1. split; [|apply drift_refl]. apply (Hst mo1 _ _ _ Hd). split; [reflexivity|]. left. exists ENOMEM. split; [left; reflexivity | split; reflexivity]. }
rewrite F1, Hfree. apply t_emit_nil; assumption.
* right; left. exists (eff0 (alloc_fd (m_fds mo1))), (with_fds (fd_insert (m_fds mo1) (alloc_fd (m_fds mo1)) ent) mo1), []. split.
{ eexists. split; [|apply drift_refl]. apply (Hst mo1 _ _ _ Hd). split; [reflexivity|]. right. rewrite F1. split; [exact Hfree | split; reflexivity]. }
rewrite m_fds_with_fds, F1, fd_lookup_insert, bv_eqb_refl. apply t_emit_nil; assumption.
+ intros [->|[(rsp & mo' & evs & (mo2 & Hn & Hd2) & Hem)|(code & mo' & [] & _)]]; [left; exact HA0|].
apply (Hst mo1 rsp mo2 evs Hd) in Hn. destruct Hn as [-> Hr]. pose proof (drift_frame LV _ _ Hd2) as (F2 & _). rewrite F2 in Hem.
destruct Hr as [(e & He & -> & ->)|(Hf & -> & ->)].
* rewrite F1, Hfree in Hem. left. apply (t_emit_nil TA tr HA0). exact Hem.
* rewrite m_fds_with_fds, F1, fd_lookup_insert, bv_eqb_refl in Hem. right. apply (t_emit_nil TB tr HB0). exact Hem.
Qed.

Theorem ajv_open_file : forall (TA TB : QRjH.TSet) path d c msv,
at_nodeA LV segs (NOpen path) msv -> CKv LV c ->
(length path < path_max)%nat -> path <> [] -> path_eqb path dot_path = false ->
fs_lookup (m_fs (cfg_model c)) path = Some d ->
fd_lookup (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) = None ->
TA [] -> TB [] ->
(forall e c', In e openat_errnos -> CNEXTv LV c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV TA c' (nret msv (efferr e))) ->
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = fd_insert (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) (FdFile path (Z_to_bv 64 0)) ->
m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV TB c' (nret msv (eff0 (alloc_fd (m_fds (cfg_model c)))))) ->
AJv segs LV (QRjH.t_alt2 TA TB) c msv.
Proof.
intros TA TB path d c msv Hat HCK Hlen Hne Hdot Hfs Hfree HA0 HB0 KA KB.
apply (ajv_open_result TA TB path (FdFile path (Z_to_bv 64 0)) c msv Hat HCK); try assumption.
intros mo1 rsp mo2 evs Hd. pose proof (drift_frame LV _ _ Hd) as (_ & S1 & _). cbn [nstep].
replace (path_max <=? length path)%nat with false by (symmetry; apply Nat.leb_gt; exact Hlen).
destruct path as [|b path']; [contradiction|]. rewrite Hdot, S1, Hfs. tauto.
Qed.

Theorem ajv_open_dot : forall (TA TB : QRjH.TSet) c msv,
at_nodeA LV segs (NOpen dot_path) msv -> CKv LV c ->
fd_lookup (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) = None ->
TA [] -> TB [] ->
(forall e c', In e openat_errnos -> CNEXTv LV c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV TA c' (nret msv (efferr e))) ->
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = fd_insert (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) FdDir ->
m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV TB c' (nret msv (eff0 (alloc_fd (m_fds (cfg_model c)))))) ->
AJv segs LV (QRjH.t_alt2 TA TB) c msv.
Proof.
intros TA TB c msv Hat HCK Hfree HA0 HB0 KA KB.
apply (ajv_open_result TA TB dot_path FdDir c msv Hat HCK); try assumption.
intros mo1 rsp mo2 evs Hd. cbn [nstep]. change (path_max <=? length dot_path)%nat with false.
change (path_eqb dot_path dot_path) with true. cbv iota. unfold dot_path. tauto.
Qed.

Theorem ajv_exit : forall (code : Z) c msv,
at_nodeA LV segs (NExit code) msv -> CKv LV c ->
AJv segs LV (QRjH.t_exit (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) (m_fs (cfg_model c))) c msv.
Proof. intros code c msv Hat [HC _]. exact (vjA_exit segs LV Hsegs Hsh Hbx Hbc code c msv Hat HC). Qed.

Theorem ajv_writev : forall (fd : Z) (bufs : list (list byte)) (Tn : nat -> QRjH.TSet) c msv,
at_nodeA LV segs (NWritev fd bufs) msv -> CKv LV c ->
(1 <= length (concat bufs))%nat ->
(forall (k : nat) c', (1 <= k)%nat -> (k <= length (concat bufs))%nat -> CNEXTv LV c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV (Tn k) c' (nret msv (eff0 (Z_to_bv 64 (Z.of_nat k))))) ->
AJv segs LV (QRjH.t_alt (fun i : QRjH.wr_index (concat bufs) =>
QRjH.t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (concat bufs))) (Tn (proj1_sig i)))) c msv.
Proof.
intros fd bufs Tn c msv Hat [HC Hh] Hnb HK.
apply (vjA_writev segs LV Hsegs Hsh Hbx Hbc fd bufs Tn c msv Hat HC Hnb).
intros k c1 Hk1 Hk2 Hd HC1 Hh1 _. pose proof (drift_frame LV _ _ Hd) as (F1 & S1 & _).
apply (HK k c1 Hk1 Hk2); [split; [split; assumption | exact (vmrel_drift LV _ _ Hd)] | exact F1 | exact S1].
Qed.

Theorem ajv_writev0 : forall (T : QRjH.TSet) (fd : Z) (bufs : list (list byte)) c msv,
at_nodeA LV segs (NWritev fd bufs) msv -> CKv LV c -> concat bufs = [] ->
(forall c', CNEXTv LV c c' -> m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (eff0 (Z_to_bv 64 0)))) ->
AJv segs LV T c msv.
Proof.
intros T fd bufs c msv Hat HCK Hnil HK.
apply (ajv_silent_node T (NWritev fd bufs) c msv Hat HCK eq_refl I).
- intros mo1 code mo' [].
- intros mo1 rsp mo' evs (mo2 & Hn & _). cbn [nstep] in Hn. destruct Hn as (_ & [(_ & _ & E)|(k & Hk & _)]); [exact E|]. rewrite Hnil in Hk. cbn in Hk. lia.
- intros mo1 rsp c' Hd (mo2 & Hn & Hd2) HCK'. cbn [nstep] in Hn. destruct Hn as (-> & [(_ & -> & _)|(k & Hk & _)]); [|rewrite Hnil in Hk; cbn in Hk; lia].
destruct (cnext_fds c c' mo1 _ HCK' Hd (or_introl eq_refl) Hd2) as (HN & HS & HF & HF1).
apply (HK c' HN); [| exact HS]. rewrite HF, ?HF1. reflexivity.
Qed.
End NodeRulesDrv.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQIi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQIi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHWH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHWH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1lV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qcrs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUcd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUcd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCUT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCUT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwAs.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc6I. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsn5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsn5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJFf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJFf.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qknc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qknc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBrp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBrp. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2ui.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2ui. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1KO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1KO.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeDS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeDS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNqr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNqr.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeDS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeDS.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLiw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLiw.Mq2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QFL8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFL8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRGF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRGF.
Import ListNotations.
Open Scope Z_scope.

Section NodeRulesDrv.
Variable segs : list Segment.
Variable LV : lvp.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_in_base LV segs.
Hypothesis Hsh : shoff_ok LV.
Hypothesis Hbx : bands_excl LV.
Hypothesis Hbc : bands_cover LV.

Local Notation NS := (nodesA_sound segs LV Hsegs Hsh Hbx Hbc).

Lemma ajv_silent_node : forall (T : QRjH.TSet) (n : node) c msv,
at_nodeA LV segs n msv -> CKv LV c ->
is_spinA n = false -> nsafeA LV n (cfg_model c) ->
(forall mo1 code mo', ~ nexit_raw n mo1 code mo') ->
(forall mo1 rsp mo' evs, nstep_raw LV n mo1 rsp mo' evs -> evs = []) ->
(forall mo1 rsp c', drift LV (cfg_model c) mo1 -> nstep_raw LV n mo1 rsp (cfg_model c') [] -> CKv LV c' ->
AJv segs LV T c' (nret msv rsp)) ->
AJv segs LV T c msv.
Proof.
intros T n c msv Hat [HC Hh] Hsp Hns Hnx Hsil HK. unfold AJv.
apply (vj_silent node segs LV Hwx Hsegs (at_nodeA LV segs) (nstep_raw LV) nexit_raw (nsafeA LV) (xinvA LV) is_spinA rvarA (jsome LV)
(jsome_stable LV) NS (JS segs T) (js_nclosed segs T) n c msv Hat HC Hsp Hns).
- intros mo1 code mo' _. apply Hnx.
- intros rsp mo' evs (mo1 & _ & Hr). exact (Hsil mo1 rsp mo' evs Hr).
- intros rsp c1 (mo1 & Hd & Hr) HC1 Hh1. exact (HK mo1 rsp c1 Hd Hr (conj HC1 Hh1)).
Qed.

Lemma m_fds_with_fds : forall f mo, m_fds (with_fds f mo) = f.   Proof. intros f []; reflexivity. Qed.
Lemma m_fs_with_fds : forall f mo, m_fs (with_fds f mo) = m_fs mo.   Proof. intros f []; reflexivity. Qed.
Lemma vmrel_with_fds : forall f mo, vmrel LV mo (with_fds f mo).
Proof.
intros f mo. split; [destruct mo; reflexivity|]. apply Phi_ext; [split; destruct mo; reflexivity | destruct mo; reflexivity].
Qed.

Lemma cnext_fds : forall c c' mo1 mo2, CKv LV c' ->
drift LV (cfg_model c) mo1 -> (mo2 = mo1 \/ exists f, mo2 = with_fds f mo1) -> drift LV mo2 (cfg_model c') ->
CNEXTv LV c c' /\ m_fs (cfg_model c') = m_fs (cfg_model c) /\ m_fds (cfg_model c') = m_fds mo2 /\ m_fds mo1 = m_fds (cfg_model c).
Proof.
intros c c' mo1 mo2 HCK Hd1 Hm Hd2.
pose proof (drift_frame LV _ _ Hd1) as (F1 & S1 & _). pose proof (drift_frame LV _ _ Hd2) as (F2 & S2 & _).
split; [split; [exact HCK|]|].
- eapply vmrel_trans; [exact (vmrel_drift LV _ _ Hd1)|]. eapply vmrel_trans; [|exact (vmrel_drift LV _ _ Hd2)].
destruct Hm as [-> | (f & ->)]; [apply vmrel_refl | apply vmrel_with_fds].
- split; [|split; [exact F2 | exact F1]].
rewrite S2. destruct Hm as [-> | (f & ->)]; [exact S1 | rewrite m_fs_with_fds; exact S1].
Qed.

Theorem ajv_close : forall (T : QRjH.TSet) fd e c msv,
at_nodeA LV segs (NClose fd) msv -> CKv LV c ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 fd) = Some e ->
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = fd_remove (m_fds (cfg_model c)) (Z_to_bv 64 fd) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (eff0 (Z_to_bv 64 0)))) ->
AJv segs LV T c msv.
Proof.
intros T fd e c msv Hat HCK Hlk HK.
apply (ajv_silent_node T (NClose fd) c msv Hat HCK eq_refl I).
- intros mo1 code mo' [].
- intros mo1 rsp mo' evs (mo2 & Hn & _). cbn [nstep] in Hn. exact (proj1 Hn).
- intros mo1 rsp c' Hd (mo2 & Hn & Hd2) HCK'. cbn [nstep] in Hn. destruct Hn as (_ & _ & Hm).
pose proof (drift_frame LV _ _ Hd) as (F1 & _). rewrite F1, Hlk in Hm. destruct Hm as [-> ->].
destruct (cnext_fds c c' mo1 _ HCK' Hd (or_intror (ex_intro _ _ eq_refl)) Hd2) as (HN & HS & HF & HF1).
apply (HK c' HN); [| exact HS]. rewrite HF, m_fds_with_fds, ?HF1. reflexivity.
Qed.

Theorem ajv_ioctl_winsz : forall (T : QRjH.TSet) fd req c msv,
at_nodeA LV segs (NIoctl fd req) msv -> CKv LV c ->
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (efferr ENOTTY))) ->
AJv segs LV T c msv.
Proof.
intros T fd req c msv Hat HCK HK.
apply (ajv_silent_node T (NIoctl fd req) c msv Hat HCK eq_refl I).
- intros mo1 code mo' [].
- intros mo1 rsp mo' evs (mo2 & Hn & _). cbn [nstep] in Hn. exact (proj1 Hn).
- intros mo1 rsp c' Hd (mo2 & Hn & Hd2) HCK'. cbn [nstep] in Hn. destruct Hn as (_ & -> & ->).
destruct (cnext_fds c c' mo1 _ HCK' Hd (or_introl eq_refl) Hd2) as (HN & HS & HF & HF1).
apply (HK c' HN); [| exact HS]. rewrite HF, ?HF1. reflexivity.
Qed.

Theorem ajv_read_file : forall (T : QRjH.TSet) fd buf count p off data c msv,
at_nodeA LV segs (NRead fd buf count) msv -> CKv LV c ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 fd) = Some (FdFile p off) ->
fs_lookup (m_fs (cfg_model c)) p = Some data ->
let bs := file_read data off (Z_to_bv 64 count) in
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = fd_insert (m_fds (cfg_model c)) (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv) ->
m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (mkEffect (len_word bs) (delivered_writes (Z_to_bv 64 buf) bs) []))) ->
AJv segs LV T c msv.
Proof.
intros T fd buf count p off data c msv Hat HCK Hlk Hfs bs HK.
apply (ajv_silent_node T (NRead fd buf count) c msv Hat HCK eq_refl I).
- intros mo1 code mo' [].
- intros mo1 rsp mo' evs (mo2 & Hn & _). cbn [nstep] in Hn. exact (proj1 Hn).
- intros mo1 rsp c' Hd (mo2 & Hn & Hd2) HCK'. cbn [nstep] in Hn. destruct Hn as (_ & Hm).
pose proof (drift_frame LV _ _ Hd) as (F1 & S1 & _). rewrite F1, Hlk, S1, Hfs in Hm. cbn zeta in Hm. destruct Hm as [-> ->].
destruct (cnext_fds c c' mo1 _ HCK' Hd (or_intror (ex_intro _ _ eq_refl)) Hd2) as (HN & HS & HF & HF1).
apply (HK c' HN); [| exact HS]. rewrite HF, m_fds_with_fds, ?HF1. reflexivity.
Qed.

Theorem ajv_read_dir : forall (T : QRjH.TSet) fd buf count c msv,
at_nodeA LV segs (NRead fd buf count) msv -> CKv LV c ->
fd_lookup (m_fds (cfg_model c)) (Z_to_bv 64 fd) = Some FdDir ->
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (efferr EISDIR))) ->
AJv segs LV T c msv.
Proof.
intros T fd buf count c msv Hat HCK Hlk HK.
apply (ajv_silent_node T (NRead fd buf count) c msv Hat HCK eq_refl I).
- intros mo1 code mo' [].
- intros mo1 rsp mo' evs (mo2 & Hn & _). cbn [nstep] in Hn. exact (proj1 Hn).
- intros mo1 rsp c' Hd (mo2 & Hn & Hd2) HCK'. cbn [nstep] in Hn. destruct Hn as (_ & Hm).
pose proof (drift_frame LV _ _ Hd) as (F1 & _). rewrite F1, Hlk in Hm. destruct Hm as [-> ->].
destruct (cnext_fds c c' mo1 _ HCK' Hd (or_introl eq_refl) Hd2) as (HN & HS & HF & HF1).
apply (HK c' HN); [| exact HS]. rewrite HF, ?HF1. reflexivity.
Qed.

Lemma open_single : forall (T : QRjH.TSet) path e c msv,
at_nodeA LV segs (NOpen path) msv -> CKv LV c ->
(forall mo1 rsp mo2, drift LV (cfg_model c) mo1 -> nstep (NOpen path) mo1 rsp mo2 [] -> rsp = efferr e /\ mo2 = mo1) ->
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (efferr e))) ->
AJv segs LV T c msv.
Proof.
intros T path e c msv Hat HCK Hone HK.
apply (ajv_silent_node T (NOpen path) c msv Hat HCK eq_refl I).
- intros mo1 code mo' [].
- intros mo1 rsp mo' evs (mo2 & Hn & _). cbn [nstep] in Hn. exact (proj1 Hn).
- intros mo1 rsp c' Hd (mo2 & Hn & Hd2) HCK'. destruct (Hone mo1 rsp mo2 Hd Hn) as [-> ->].
destruct (cnext_fds c c' mo1 _ HCK' Hd (or_introl eq_refl) Hd2) as (HN & HS & HF & HF1).
apply (HK c' HN); [| exact HS]. rewrite HF, ?HF1. reflexivity.
Qed.

Theorem ajv_open_toolong : forall (T : QRjH.TSet) path c msv,
at_nodeA LV segs (NOpen path) msv -> CKv LV c -> (path_max <= length path)%nat ->
(forall c', CNEXTv LV c c' -> m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (efferr ENAMETOOLONG))) ->
AJv segs LV T c msv.
Proof.
intros T path c msv Hat HCK Hlen HK. apply (open_single T path ENAMETOOLONG c msv Hat HCK); [|exact HK].
intros mo1 rsp mo2 _ Hn. cbn [nstep] in Hn. destruct Hn as [_ Hn].
replace (path_max <=? length path)%nat with true in Hn by (symmetry; apply Nat.leb_le; exact Hlen). exact Hn.
Qed.

Theorem ajv_open_empty : forall (T : QRjH.TSet) c msv,
at_nodeA LV segs (NOpen []) msv -> CKv LV c ->
(forall c', CNEXTv LV c c' -> m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (efferr ENOENT))) ->
AJv segs LV T c msv.
Proof.
intros T c msv Hat HCK HK. apply (open_single T [] ENOENT c msv Hat HCK); [|exact HK].
intros mo1 rsp mo2 _ Hn. cbn [nstep] in Hn. destruct Hn as [_ Hn]. cbn in Hn. exact Hn.
Qed.

Theorem ajv_open_absent : forall (T : QRjH.TSet) path c msv,
at_nodeA LV segs (NOpen path) msv -> CKv LV c ->
(length path < path_max)%nat -> path <> [] -> path_eqb path dot_path = false ->
fs_lookup (m_fs (cfg_model c)) path = None ->
(forall c', CNEXTv LV c c' -> m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (efferr ENOENT))) ->
AJv segs LV T c msv.
Proof.
intros T path c msv Hat HCK Hlen Hne Hdot Hfs HK. apply (open_single T path ENOENT c msv Hat HCK); [|exact HK].
intros mo1 rsp mo2 Hd Hn. cbn [nstep] in Hn. destruct Hn as [_ Hn].
replace (path_max <=? length path)%nat with false in Hn by (symmetry; apply Nat.leb_gt; exact Hlen).
destruct path as [|b path']; [contradiction|]. rewrite Hdot in Hn.
pose proof (drift_frame LV _ _ Hd) as (_ & S1 & _). rewrite S1, Hfs in Hn. exact Hn.
Qed.

Local Notation vis := (vj_vis_k node segs LV (at_nodeA LV segs) (nstep_raw LV) nexit_raw (nsafeA LV) (xinvA LV) is_spinA rvarA (jsome LV)
(jsome_stable LV) NS).

Lemma t_emit_nil : forall (T : TSet) tr, T [] -> (t_emit [] T tr <-> T tr).
Proof.
intros T tr H0. unfold t_emit. split.
- intros [Hp|(tr' & -> & Ht)]; [destruct tr; [exact H0 | destruct Hp] | exact Ht].
- intros Ht. right. exists tr. split; [reflexivity | exact Ht].
Qed.

Lemma ajv_open_result : forall (TA TB : QRjH.TSet) path ent c msv,
at_nodeA LV segs (NOpen path) msv -> CKv LV c ->
(forall mo1 rsp mo2 evs, drift LV (cfg_model c) mo1 ->
(nstep (NOpen path) mo1 rsp mo2 evs <-> evs = [] /\ open_result mo1 ent rsp mo2)) ->
fd_lookup (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) = None ->
TA [] -> TB [] ->
(forall e c', In e openat_errnos -> CNEXTv LV c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV TA c' (nret msv (efferr e))) ->
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = fd_insert (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) ent ->
m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV TB c' (nret msv (eff0 (alloc_fd (m_fds (cfg_model c)))))) ->
AJv segs LV (QRjH.t_alt2 TA TB) c msv.
Proof.
intros TA TB path ent c msv Hat [HC Hh] Hst Hfree HA0 HB0 KA KB. unfold AJv.
set (fds0 := m_fds (cfg_model c)) in *.

apply (vis (NOpen path) (fun _ mo' _ => match fd_lookup (m_fds mo') (alloc_fd fds0) with Some _ => TB | None => TA end) _ c msv eq_refl Hat HC I).
- intros r r2 mo' mo2 evs _ Hs. destruct (msim_facts LV _ _ Hs) as (F & _). rewrite F. apply t_eq_refl.
- intros mo1 rsp evs c1 Hd (mo2 & Hn & Hd2) HC1 Hh1 _.
apply (Hst mo1 rsp mo2 evs Hd) in Hn. destruct Hn as [-> Hr].
pose proof (drift_frame LV _ _ Hd) as (F1 & _). pose proof (drift_frame LV _ _ Hd2) as (F2 & _). fold fds0 in F1.
destruct Hr as [(e & He & -> & ->)|(Hf & -> & ->)].
+ destruct (cnext_fds c c1 mo1 _ (conj HC1 Hh1) Hd (or_introl eq_refl) Hd2) as (HN & HS & HF & HF1).
rewrite F2, F1, Hfree. apply (KA e c1 He HN); [rewrite HF, HF1; reflexivity | exact HS].
+ destruct (cnext_fds c c1 mo1 _ (conj HC1 Hh1) Hd (or_intror (ex_intro _ _ eq_refl)) Hd2) as (HN & HS & HF & HF1).
rewrite F2, m_fds_with_fds, F1, fd_lookup_insert, bv_eqb_refl. rewrite ?F1. apply (KB c1 HN); [| exact HS].
rewrite HF, m_fds_with_fds, ?F1. reflexivity.
- intros mo1 Hd tr. pose proof (drift_frame LV _ _ Hd) as (F1 & _). fold fds0 in F1. unfold QRjH.t_alt2. split.
+ intros [Ha|Hb].
* right; left. exists (efferr ENOMEM), mo1, []. split.
{ exists mo1. split; [|apply drift_refl]. apply (Hst mo1 _ _ _ Hd). split; [reflexivity|]. left. exists ENOMEM. split; [left; reflexivity | split; reflexivity]. }
rewrite F1, Hfree. apply t_emit_nil; assumption.
* right; left. exists (eff0 (alloc_fd (m_fds mo1))), (with_fds (fd_insert (m_fds mo1) (alloc_fd (m_fds mo1)) ent) mo1), []. split.
{ eexists. split; [|apply drift_refl]. apply (Hst mo1 _ _ _ Hd). split; [reflexivity|]. right. rewrite F1. split; [exact Hfree | split; reflexivity]. }
rewrite m_fds_with_fds, F1, fd_lookup_insert, bv_eqb_refl. apply t_emit_nil; assumption.
+ intros [->|[(rsp & mo' & evs & (mo2 & Hn & Hd2) & Hem)|(code & mo' & [] & _)]]; [left; exact HA0|].
apply (Hst mo1 rsp mo2 evs Hd) in Hn. destruct Hn as [-> Hr]. pose proof (drift_frame LV _ _ Hd2) as (F2 & _). rewrite F2 in Hem.
destruct Hr as [(e & He & -> & ->)|(Hf & -> & ->)].
* rewrite F1, Hfree in Hem. left. apply (t_emit_nil TA tr HA0). exact Hem.
* rewrite m_fds_with_fds, F1, fd_lookup_insert, bv_eqb_refl in Hem. right. apply (t_emit_nil TB tr HB0). exact Hem.
Qed.

Theorem ajv_open_file : forall (TA TB : QRjH.TSet) path d c msv,
at_nodeA LV segs (NOpen path) msv -> CKv LV c ->
(length path < path_max)%nat -> path <> [] -> path_eqb path dot_path = false ->
fs_lookup (m_fs (cfg_model c)) path = Some d ->
fd_lookup (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) = None ->
TA [] -> TB [] ->
(forall e c', In e openat_errnos -> CNEXTv LV c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV TA c' (nret msv (efferr e))) ->
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = fd_insert (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) (FdFile path (Z_to_bv 64 0)) ->
m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV TB c' (nret msv (eff0 (alloc_fd (m_fds (cfg_model c)))))) ->
AJv segs LV (QRjH.t_alt2 TA TB) c msv.
Proof.
intros TA TB path d c msv Hat HCK Hlen Hne Hdot Hfs Hfree HA0 HB0 KA KB.
apply (ajv_open_result TA TB path (FdFile path (Z_to_bv 64 0)) c msv Hat HCK); try assumption.
intros mo1 rsp mo2 evs Hd. pose proof (drift_frame LV _ _ Hd) as (_ & S1 & _). cbn [nstep].
replace (path_max <=? length path)%nat with false by (symmetry; apply Nat.leb_gt; exact Hlen).
destruct path as [|b path']; [contradiction|]. rewrite Hdot, S1, Hfs. tauto.
Qed.

Theorem ajv_open_dot : forall (TA TB : QRjH.TSet) c msv,
at_nodeA LV segs (NOpen dot_path) msv -> CKv LV c ->
fd_lookup (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) = None ->
TA [] -> TB [] ->
(forall e c', In e openat_errnos -> CNEXTv LV c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV TA c' (nret msv (efferr e))) ->
(forall c', CNEXTv LV c c' ->
m_fds (cfg_model c') = fd_insert (m_fds (cfg_model c)) (alloc_fd (m_fds (cfg_model c))) FdDir ->
m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV TB c' (nret msv (eff0 (alloc_fd (m_fds (cfg_model c)))))) ->
AJv segs LV (QRjH.t_alt2 TA TB) c msv.
Proof.
intros TA TB c msv Hat HCK Hfree HA0 HB0 KA KB.
apply (ajv_open_result TA TB dot_path FdDir c msv Hat HCK); try assumption.
intros mo1 rsp mo2 evs Hd. cbn [nstep]. change (path_max <=? length dot_path)%nat with false.
change (path_eqb dot_path dot_path) with true. cbv iota. unfold dot_path. tauto.
Qed.

Theorem ajv_exit : forall (code : Z) c msv,
at_nodeA LV segs (NExit code) msv -> CKv LV c ->
AJv segs LV (QRjH.t_exit (bv_and (Z_to_bv 64 code) (Z_to_bv 64 255)) (m_fs (cfg_model c))) c msv.
Proof. intros code c msv Hat [HC _]. exact (vjA_exit segs LV Hsegs Hsh Hbx Hbc code c msv Hat HC). Qed.

Theorem ajv_writev : forall (fd : Z) (bufs : list (list byte)) (Tn : nat -> QRjH.TSet) c msv,
at_nodeA LV segs (NWritev fd bufs) msv -> CKv LV c ->
(1 <= length (concat bufs))%nat ->
(forall (k : nat) c', (1 <= k)%nat -> (k <= length (concat bufs))%nat -> CNEXTv LV c c' ->
m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV (Tn k) c' (nret msv (eff0 (Z_to_bv 64 (Z.of_nat k))))) ->
AJv segs LV (QRjH.t_alt (fun i : QRjH.wr_index (concat bufs) =>
QRjH.t_emit (map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig i) (concat bufs))) (Tn (proj1_sig i)))) c msv.
Proof.
intros fd bufs Tn c msv Hat [HC Hh] Hnb HK.
apply (vjA_writev segs LV Hsegs Hsh Hbx Hbc fd bufs Tn c msv Hat HC Hnb).
intros k c1 Hk1 Hk2 Hd HC1 Hh1 _. pose proof (drift_frame LV _ _ Hd) as (F1 & S1 & _).
apply (HK k c1 Hk1 Hk2); [split; [split; assumption | exact (vmrel_drift LV _ _ Hd)] | exact F1 | exact S1].
Qed.

Theorem ajv_writev0 : forall (T : QRjH.TSet) (fd : Z) (bufs : list (list byte)) c msv,
at_nodeA LV segs (NWritev fd bufs) msv -> CKv LV c -> concat bufs = [] ->
(forall c', CNEXTv LV c c' -> m_fds (cfg_model c') = m_fds (cfg_model c) -> m_fs (cfg_model c') = m_fs (cfg_model c) ->
AJv segs LV T c' (nret msv (eff0 (Z_to_bv 64 0)))) ->
AJv segs LV T c msv.
Proof.
intros T fd bufs c msv Hat HCK Hnil HK.
apply (ajv_silent_node T (NWritev fd bufs) c msv Hat HCK eq_refl I).
- intros mo1 code mo' [].
- intros mo1 rsp mo' evs (mo2 & Hn & _). cbn [nstep] in Hn. destruct Hn as (_ & [(_ & _ & E)|(k & Hk & _)]); [exact E|]. rewrite Hnil in Hk. cbn in Hk. lia.
- intros mo1 rsp c' Hd (mo2 & Hn & Hd2) HCK'. cbn [nstep] in Hn. destruct Hn as (-> & [(_ & -> & _)|(k & Hk & _)]); [|rewrite Hnil in Hk; cbn in Hk; lia].
destruct (cnext_fds c c' mo1 _ HCK' Hd (or_introl eq_refl) Hd2) as (HN & HS & HF & HF1).
apply (HK c' HN); [| exact HS]. rewrite HF, ?HF1. reflexivity.
Qed.
End NodeRulesDrv.
