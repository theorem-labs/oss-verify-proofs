(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YE03.v, with its module paths changed. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI04 YI00 YI16 YK0r.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Lemma fs_lt_head_keys : forall r a, Fs.fs_sorted r = true -> Fs.fs_lt_head a r = true -> Forall (fun qd => fst qd <> a) r.
Proof.
induction r as [|[q d] r IH]; intros a Hs Hh; [constructor|].
rewrite Fs.fs_sorted_cons, Bool.andb_true_iff in Hs. destruct Hs as [Hq Hr]. cbn [Fs.fs_lt_head] in Hh.
constructor.
- cbn [fst]. intros ->. rewrite path_ltb_irrefl in Hh. discriminate Hh.
- apply IH; [exact Hr|]. destruct r as [|[q' d'] r']; [reflexivity|]. cbn [Fs.fs_lt_head] in Hq |- *. exact (Fs.path_ltb_trans _ _ _ Hh Hq).
Qed.
Lemma fs_ext : forall f1 f2, Fs.fs_sorted f1 = true -> Fs.fs_sorted f2 = true ->
(forall q, Fs.fs_lookup f1 q = Fs.fs_lookup f2 q) -> f1 = f2.
Proof.
induction f1 as [|[p d] r1 IH]; intros f2 H1 H2 HL.
- destruct f2 as [|[q e] r2]; [reflexivity|]. specialize (HL q). cbn [Fs.fs_lookup] in HL. rewrite Fs.path_eqb_refl in HL. discriminate HL.
- destruct f2 as [|[q e] r2].
{ specialize (HL p). cbn [Fs.fs_lookup] in HL. rewrite Fs.path_eqb_refl in HL. discriminate HL. }
destruct (Fs.path_eqb p q) eqn:Epq.
+ apply Fs.path_eqb_eq in Epq. subst q.
pose proof (HL p) as Hp. cbn [Fs.fs_lookup] in Hp. rewrite Fs.path_eqb_refl in Hp. injection Hp as <-.
f_equal. rewrite Fs.fs_sorted_cons, Bool.andb_true_iff in H1, H2. destruct H1 as [Hh1 Hr1]. destruct H2 as [Hh2 Hr2].
apply (IH r2 Hr1 Hr2). intros k. destruct (Fs.path_eqb k p) eqn:Ek.
* apply Fs.path_eqb_eq in Ek. subst k.
rewrite (Fs.fs_lookup_none_of_keys r1 p (fs_lt_head_keys r1 p Hr1 Hh1)), (Fs.fs_lookup_none_of_keys r2 p (fs_lt_head_keys r2 p Hr2 Hh2)). reflexivity.
* specialize (HL k). cbn [Fs.fs_lookup] in HL. rewrite Ek in HL. exact HL.
+ exfalso. destruct (Fs.path_ltb p q) eqn:Elt.
* pose proof (HL p) as Hp. cbn [Fs.fs_lookup] in Hp. rewrite Fs.path_eqb_refl, Epq in Hp.
rewrite Fs.fs_sorted_cons, Bool.andb_true_iff in H2. destruct H2 as [Hh2 Hr2].
assert (Hn : Fs.fs_lookup r2 p = None).
{ apply Fs.fs_lookup_none_of_keys. apply (fs_lt_head_keys r2 p Hr2).
destruct r2 as [|[q' d'] r']; [reflexivity|]. cbn [Fs.fs_lt_head] in Hh2 |- *. exact (Fs.path_ltb_trans _ _ _ Elt Hh2). }
rewrite Hn in Hp. discriminate Hp.
* pose proof (Fs.path_ltb_total p q Elt Epq) as Egt.
pose proof (HL q) as Hq. cbn [Fs.fs_lookup] in Hq. rewrite Fs.path_eqb_refl in Hq.
rewrite YK0r.path_eqb_sym, Epq in Hq.
rewrite Fs.fs_sorted_cons, Bool.andb_true_iff in H1. destruct H1 as [Hh1 Hr1].
assert (Hn : Fs.fs_lookup r1 q = None).
{ apply Fs.fs_lookup_none_of_keys. apply (fs_lt_head_keys r1 q Hr1).
destruct r1 as [|[q' d'] r']; [reflexivity|]. cbn [Fs.fs_lt_head] in Hh1 |- *. exact (Fs.path_ltb_trans _ _ _ Egt Hh1). }
rewrite Hn in Hq. discriminate Hq.
Qed.
Definition names_sink (e : FdEntry) : Prop :=
match e with FdFile p _ | FdFileW p _ | FdFileA p _ | FdFileRW p _ => p = sink_path | _ => False end.
Lemma fd_names_path_lookup : forall fds fd e,
Namei.fd_names_path fds sink_path = false -> fd_lookup fds fd = Some e -> ~ names_sink e.
Proof.
induction fds as [|[k e0] r IH]; intros fd e Hs Hl; [discriminate Hl|].
cbn [fd_lookup] in Hl.
assert (Hr : Namei.fd_names_path r sink_path = false).
{ cbn [Namei.fd_names_path] in Hs. destruct e0; try exact Hs; apply Bool.orb_false_iff in Hs; exact (proj2 Hs). }
destruct (bv_eqb k fd); [|exact (IH fd e Hr Hl)].
injection Hl as <-. intros Hn. cbn [Namei.fd_names_path] in Hs.
destruct e0; cbn in Hn; try contradiction; subst p;
apply Bool.orb_false_iff in Hs; destruct Hs as [Hs _]; rewrite Fs.path_eqb_refl in Hs; discriminate Hs.
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section J.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable K : asink_syms.
Local Notation ajournal := (ajournal segs B).
Local Notation rd W mem := (mrestrict (w_H W) mem).
Lemma ajournal_aos : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> aos_step FP md md'.
Proof. intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ. exact (proj1 (proj2 (proj2 (proj2 (proj2 HJ))))). Qed.
Lemma ajournal_sorted : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> Fs.fs_sorted (m_fs md) = true -> Fs.fs_sorted (m_fs md') = true.
Proof. intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ Hs. pose proof (ajournal_aos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (_ & _ & _ & _ & Hso & _). exact (Hso Hs). Qed.
Lemma ajournal_fs_canon : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k (f : Fs.Fs),
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> Fs.fs_sorted (m_fs md) = true -> Fs.fs_sorted f = true ->
(forall q, q <> sink_path -> Fs.fs_lookup f q = Fs.fs_lookup (m_fs md) q) ->
Fs.fs_lookup (m_fs md') sink_path = Fs.fs_lookup f sink_path ->
m_fs md' = f.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k f HJ Hs Hf Hq Hk.
pose proof (ajournal_aos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (_ & _ & _ & Hrel & Hso & _).
apply fs_ext; [exact (Hso Hs) | exact Hf |].
intros q. destruct (list_eq_dec (@bv_eq_dec 8) q sink_path) as [-> | Hne]; [exact Hk|].
rewrite (Hq q Hne). exact (Hrel q Hne).
Qed.
Lemma ajournal_fs_set : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k d,
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> Fs.fs_sorted (m_fs md) = true ->
Fs.fs_lookup (m_fs md') sink_path = Some d -> m_fs md' = Fs.fs_set (m_fs md) sink_path d.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k d HJ Hs Hk.
apply (ajournal_fs_canon STK sp0 FP ly S W mem md own ly' S' W' mem' md' k _ HJ Hs (fs_set_sorted _ _ _ Hs)).
- intros q Hq. apply fs_lookup_set_other. exact Hq.
- rewrite fs_lookup_set_same. exact Hk.
Qed.
Lemma ajournal_fs_same : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k -> Fs.fs_sorted (m_fs md) = true ->
Fs.fs_lookup (m_fs md') sink_path = Fs.fs_lookup (m_fs md) sink_path -> m_fs md' = m_fs md.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ Hs Hk.
apply (ajournal_fs_canon STK sp0 FP ly S W mem md own ly' S' W' mem' md' k _ HJ Hs Hs); [intros q _; reflexivity | exact Hk].
Qed.
Lemma ajournal_fds_restored : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
asink_none segs K (rd W mem) md -> asink_none segs K (rd W' mem') md' ->
forall fd, fd_lookup (m_fds md') fd = fd_lookup (m_fds md) fd.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ (_ & _ & Hn0) (_ & _ & Hn0') fd.
pose proof (ajournal_aos _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (_ & _ & Hfds & _).
pose proof (fun fd e => fd_names_path_lookup (m_fds md) fd e Hn0) as Hn.
pose proof (fun fd e => fd_names_path_lookup (m_fds md') fd e Hn0') as Hn'.
destruct (Hfds fd) as [E | [[E1 | (o1 & E1)] [E2 | (o2 & E2)]]].
- exact E.
- rewrite E1, E2. reflexivity.
- exfalso. exact (Hn' fd _ E2 eq_refl).
- exfalso. exact (Hn fd _ E1 eq_refl).
- exfalso. exact (Hn fd _ E1 eq_refl).
Qed.
End J.
End b.
