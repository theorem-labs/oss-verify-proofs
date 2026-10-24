(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Class sink_head : Type := mkSinkHead { sk_ofl_head : Z }.
Definition sink_path_Z : list Z := [47; 116; 109; 112; 47; 111; 117; 116; 46; 103; 105; 102].
Definition sink_path : Fs.path := map (fun z => Z_to_bv 8 z) sink_path_Z.
Definition sink_mode_Z : list Z := [119; 98].
Definition sink_token : Z * Z := (0, 1).
Definition os_upd (vm' : VmMaps) (fds' : list (word * FdEntry)) (fs' : Fs.Fs)
(pins' : list (Fs.path * list byte)) (m : Model) : Model :=
mkModelOf (mkFdState fds' (m_pipes m))
(mkVmState vm' (m_vm_lazy m) (m_vm_materialized m))
(m_io m) (mkFsState fs')
(mkProcState (m_halted m) (m_tid m) (m_creds m)
(m_setsid_succeeded m) (m_sigmask m)
(m_has_children m) (m_utsname m)
(m_sigaltstack_installed m)
(procst_killed (m_proc m)) (m_sigabrt_pending m)
(m_abort_terminal m) pins')
(m_lim m) (m_time m).
Lemma os_upd_self : forall m, m = os_upd (m_vmmaps m) (m_fds m) (m_fs m) (m_statpins m) m.
Proof. intros [[t p] [v l z] io [fs] [h ti c ss sm ch u sa k sp at_ pins] li tm]. reflexivity. Qed.
Lemma os_upd_twice : forall v1 f1 s1 p1 v2 f2 s2 p2 m,
os_upd v2 f2 s2 p2 (os_upd v1 f1 s1 p1 m) = os_upd v2 f2 s2 p2 m.
Proof. intros. reflexivity. Qed.
Lemma with_vmmaps_os_upd : forall vm' m, with_vmmaps vm' m = os_upd vm' (m_fds m) (m_fs m) (m_statpins m) m.
Proof. intros vm' [[t p] [v l z] io [fs] [h ti c ss sm ch u sa k sp at_ pins] li tm]. reflexivity. Qed.
Lemma with_fds_os_upd : forall fds' m, with_fds fds' m = os_upd (m_vmmaps m) fds' (m_fs m) (m_statpins m) m.
Proof. intros fds' [[t p] [v l z] io [fs] [h ti c ss sm ch u sa k sp at_ pins] li tm]. reflexivity. Qed.
Lemma with_fs_os_upd : forall fs' m,
with_fs fs' m = os_upd (m_vmmaps m) (m_fds m) fs' (statpins_restrict fs' (m_statpins m)) m.
Proof. intros fs' [[t p] [v l z] io [fs] [h ti c ss sm ch u sa k sp at_ pins] li tm]. reflexivity. Qed.
Lemma os_upd_vmmaps : forall v f s p m, m_vmmaps (os_upd v f s p m) = v.            Proof. reflexivity. Qed.
Lemma os_upd_fds : forall v f s p m, m_fds (os_upd v f s p m) = f.                  Proof. reflexivity. Qed.
Lemma os_upd_fs : forall v f s p m, m_fs (os_upd v f s p m) = s.                    Proof. reflexivity. Qed.
Lemma os_upd_statpins : forall v f s p m, m_statpins (os_upd v f s p m) = p.        Proof. reflexivity. Qed.
Lemma os_upd_halted : forall v f s p m, m_halted (os_upd v f s p m) = m_halted m.   Proof. reflexivity. Qed.
Lemma os_upd_vm_lazy : forall v f s p m, m_vm_lazy (os_upd v f s p m) = m_vm_lazy m. Proof. reflexivity. Qed.
Lemma os_upd_io : forall v f s p m, m_io (os_upd v f s p m) = m_io m.               Proof. reflexivity. Qed.
Lemma os_upd_pipes : forall v f s p m, m_pipes (os_upd v f s p m) = m_pipes m.      Proof. reflexivity. Qed.
Lemma os_upd_lim : forall v f s p m, m_lim (os_upd v f s p m) = m_lim m.            Proof. reflexivity. Qed.
Lemma os_upd_time : forall v f s p m, m_time (os_upd v f s p m) = m_time m.         Proof. reflexivity. Qed.
Definition sinkish (e : option FdEntry) : Prop := e = None \/ exists off, e = Some (FdFileW sink_path off).
Definition fds_rel (fds fds' : list (word * FdEntry)) : Prop :=
forall fd, fd_lookup fds' fd = fd_lookup fds fd \/ (sinkish (fd_lookup fds fd) /\ sinkish (fd_lookup fds' fd)).
Definition fs_rel (fs fs' : Fs.Fs) : Prop :=
forall p, p <> sink_path -> Fs.fs_lookup fs' p = Fs.fs_lookup fs p.
Lemma fds_rel_refl : forall f, fds_rel f f.
Proof. intros f fd. left. reflexivity. Qed.
Lemma fds_rel_trans : forall f1 f2 f3, fds_rel f1 f2 -> fds_rel f2 f3 -> fds_rel f1 f3.
Proof.
intros f1 f2 f3 H12 H23 fd. destruct (H12 fd) as [E12 | [S1 S2]]; destruct (H23 fd) as [E23 | [T2 T3]].
- left. rewrite E23. exact E12.
- right. split; [rewrite <- E12; exact T2 | exact T3].
- right. split; [exact S1 | rewrite E23; exact S2].
- right. split; [exact S1 | exact T3].
Qed.
Lemma fs_rel_refl : forall f, fs_rel f f.
Proof. intros f p _. reflexivity. Qed.
Lemma fs_rel_trans : forall f1 f2 f3, fs_rel f1 f2 -> fs_rel f2 f3 -> fs_rel f1 f3.
Proof. intros f1 f2 f3 H12 H23 p Hp. rewrite (H23 p Hp). exact (H12 p Hp). Qed.
Definition in_fp (FP : list (Z * Z)) (a : Z) : Prop := exists r, In r FP /\ fst r <= a < snd r.
Section b.
Definition sink_open_fp (FP : list (Z * Z)) : Prop := in_fp FP 0.
Lemma sink_open_token : forall FP, In sink_token FP -> sink_open_fp FP.
Proof. intros FP H. exists sink_token. split; [exact H | cbn; lia]. Qed.
Definition os_step (FP : list (Z * Z)) (md md' : Model) : Prop :=
exists vm' fds' fs' pins',
md' = os_upd vm' fds' fs' pins' md /\
fds_rel (m_fds md) fds' /\ fs_rel (m_fs md) fs' /\
(Fs.fs_sorted (m_fs md) = true -> Fs.fs_sorted fs' = true) /\
(~ sink_open_fp FP -> fds' = m_fds md /\ fs' = m_fs md /\ pins' = m_statpins md).
Lemma os_step_refl : forall FP md, os_step FP md md.
Proof.
intros FP md. exists (m_vmmaps md), (m_fds md), (m_fs md), (m_statpins md).
split; [apply os_upd_self|]. split; [apply fds_rel_refl|]. split; [apply fs_rel_refl|]. split; [auto|]. intros _. auto.
Qed.
Lemma os_step_vmmaps : forall FP md vm', os_step FP md (with_vmmaps vm' md).
Proof.
intros FP md vm'. exists vm', (m_fds md), (m_fs md), (m_statpins md).
split; [apply with_vmmaps_os_upd|]. split; [apply fds_rel_refl|]. split; [apply fs_rel_refl|]. split; [auto|]. intros _. auto.
Qed.
Lemma os_step_trans : forall FP FP1 md1 md2 md3,
(sink_open_fp FP1 -> sink_open_fp FP) ->
os_step FP md1 md2 -> os_step FP1 md2 md3 -> os_step FP md1 md3.
Proof.
intros FP FP1 md1 md2 md3 HF (v & f & s & p & -> & Hf & Hs & Hso & Hg) (v2 & f2 & s2 & p2 & -> & Hf2 & Hs2 & Hso2 & Hg2).
rewrite os_upd_fds in Hf2. rewrite os_upd_fs in Hs2, Hso2. rewrite os_upd_fds, os_upd_fs, os_upd_statpins in Hg2.
exists v2, f2, s2, p2. split; [apply os_upd_twice|].
split; [exact (fds_rel_trans _ _ _ Hf Hf2)|]. split; [exact (fs_rel_trans _ _ _ Hs Hs2)|]. split; [auto|].
intros Hn. destruct (Hg Hn) as (-> & -> & ->).
assert (Hn1 : ~ sink_open_fp FP1) by (intros H1; exact (Hn (HF H1))).
exact (Hg2 Hn1).
Qed.
Lemma os_step_trans_same : forall FP md1 md2 md3, os_step FP md1 md2 -> os_step FP md2 md3 -> os_step FP md1 md3.
Proof. intros FP md1 md2 md3. apply os_step_trans. auto. Qed.
Lemma os_step_then_vmmaps : forall FP md md' vm', os_step FP md md' -> os_step FP md (with_vmmaps vm' md').
Proof. intros FP md md' vm' H. eapply os_step_trans_same; [exact H | apply os_step_vmmaps]. Qed.
Lemma os_step_mono : forall FP FP' md md', (sink_open_fp FP -> sink_open_fp FP') -> os_step FP md md' -> os_step FP' md md'.
Proof.
intros FP FP' md md' HF (v & f & s & p & E & Hf & Hs & Hso & Hg). exists v, f, s, p.
split; [exact E|]. split; [exact Hf|]. split; [exact Hs|]. split; [exact Hso|]. intros Hn. apply Hg. intros H. exact (Hn (HF H)).
Qed.
Lemma os_step_halted : forall FP md md', os_step FP md md' -> m_halted md' = m_halted md.
Proof. intros FP md md' (v & f & s & p & -> & _). reflexivity. Qed.
Lemma os_step_vm_lazy : forall FP md md', os_step FP md md' -> m_vm_lazy md' = m_vm_lazy md.
Proof. intros FP md md' (v & f & s & p & -> & _). reflexivity. Qed.
Lemma os_step_io : forall FP md md', os_step FP md md' -> m_io md' = m_io md.
Proof. intros FP md md' (v & f & s & p & -> & _). reflexivity. Qed.
Lemma os_step_shielded : forall FP md md', os_step FP md md' -> ~ sink_open_fp FP ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md /\ m_statpins md' = m_statpins md.
Proof.
intros FP md md' (v & f & s & p & -> & _ & _ & _ & Hg) Hn. destruct (Hg Hn) as (-> & -> & ->).
rewrite os_upd_fds, os_upd_fs, os_upd_statpins. auto.
Qed.
Lemma os_step_fds : forall FP md md', os_step FP md md' -> fds_rel (m_fds md) (m_fds md').
Proof. intros FP md md' (v & f & s & p & -> & Hf & _). exact Hf. Qed.
Lemma os_step_fs : forall FP md md', os_step FP md md' -> fs_rel (m_fs md) (m_fs md').
Proof. intros FP md md' (v & f & s & p & -> & _ & Hs & _). exact Hs. Qed.
Lemma os_step_sorted : forall FP md md', os_step FP md md' -> Fs.fs_sorted (m_fs md) = true -> Fs.fs_sorted (m_fs md') = true.
Proof. intros FP md md' (v & f & s & p & -> & _ & _ & Hso & _). exact Hso. Qed.
Lemma os_step_intro : forall FP md vm' fds' fs' pins',
sink_open_fp FP -> fds_rel (m_fds md) fds' -> fs_rel (m_fs md) fs' ->
(Fs.fs_sorted (m_fs md) = true -> Fs.fs_sorted fs' = true) ->
os_step FP md (os_upd vm' fds' fs' pins' md).
Proof.
intros FP md vm' fds' fs' pins' Ho Hf Hs Hso. exists vm', fds', fs', pins'.
split; [reflexivity|]. split; [exact Hf|]. split; [exact Hs|]. split; [exact Hso|]. intros Hn. exfalso. exact (Hn Ho).
Qed.
End b.
