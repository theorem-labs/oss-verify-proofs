(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bz X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ra X1qu X1ri X1r3 X1r4
X1nt X1rh X1re X1qz X1rg X1od X1rm X1o8 X1r6
X1r8 X1nu X1o3 X1o5 X1o4 X1o6 X1o7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Definition diag_bytes (d : diag_msg) : list Z :=
match d with
| DUsage a => msg_usage a
| DCannotOpen p => msg_cannot_open p
| DReadError p => msg_read_error p
| DOom => concat pieces_oom
| DTooBig => msg_too_big
| DShortHdr => msg_short_hdr
| DCfgOverrun => msg_cfg_overrun
end.

Lemma concat_pieces_usage : forall a, concat (pieces_usage a) = msg_usage a.
Proof. intros a. unfold pieces_usage, msg_usage. cbn [concat]. rewrite !app_nil_l, app_nil_r. reflexivity. Qed.
Lemma concat_pieces_cannot_open : forall a, concat (pieces_cannot_open a) = msg_cannot_open a.
Proof. intros a. unfold pieces_cannot_open, msg_cannot_open. cbn [concat]. rewrite !app_nil_l. reflexivity. Qed.
Lemma concat_pieces_read_error : forall a, concat (pieces_read_error a) = msg_read_error a.
Proof. intros a. unfold pieces_read_error, msg_read_error. cbn [concat]. rewrite !app_nil_l. reflexivity. Qed.

Section Diag.
Context {St : Type}.
Variable sel : option bool.
Variable X : list event -> Prop.

Lemma s_diag_E : forall d tr0 (Kt : St -> Model -> Prop),
mspecE sel X (fun s mo tr => Kt s mo /\ tr = tr0) (@s_diag St d)
(fun _ s mo tr => Kt s mo /\ tr = tr0 ++ evw 2 (diag_bytes d)).
Proof.
intros d tr0 Kt. destruct d as [a|a|a| | | |]; cbn [s_diag diag_bytes] in *.
- eapply mspecE_post; [apply stderr_fprintf_E|].
intros _ s mo tr [HK ->]. split; [exact HK|]. rewrite concat_pieces_usage. reflexivity.
- eapply mspecE_post; [apply stderr_fprintf_E|].
intros _ s mo tr [HK ->]. split; [exact HK|]. rewrite concat_pieces_cannot_open. reflexivity.
- eapply mspecE_post; [apply stderr_fprintf_E|].
intros _ s mo tr [HK ->]. split; [exact HK|]. rewrite concat_pieces_read_error. reflexivity.
- apply stderr_fwrite_E.
- eapply mspecE_post; [apply stderr_fprintf_E|].
intros _ s mo tr [HK ->]. split; [exact HK|]. reflexivity.
- apply stderr_fwrite_E.
- apply stderr_fwrite_E.
Qed.

End Diag.

Definition fds_std : list (word * FdEntry) :=
[ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
(Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
(Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].

Lemma alloc_fd_std : alloc_fd fds_std = Z_to_bv 64 3.
Proof. vm_compute. reflexivity. Qed.

Lemma fd_free_std : fd_free_b fds_std = true.
Proof. vm_compute. reflexivity. Qed.

Lemma open_class_cases : forall path fs,
(openable_b (map (Z_to_bv 8) path) fs = false /\ open_class path fs = OCFail)
\/ (openable_b (map (Z_to_bv 8) path) fs = true /\ path_eqb (map (Z_to_bv 8) path) dot_path = true /\ open_class path fs = OCDir)
\/ (openable_b (map (Z_to_bv 8) path) fs = true /\ path_eqb (map (Z_to_bv 8) path) dot_path = false /\
exists data, fs_lookup fs (map (Z_to_bv 8) path) = Some data /\ open_class path fs = OCFile data).
Proof.
intros path fs. unfold openable_b, open_class. cbv zeta.
destruct (path_max <=? length (map (Z_to_bv 8) path))%nat; [left; auto|].
destruct (map (Z_to_bv 8) path) as [|c p'] eqn:E; [left; auto|].
destruct (path_eqb (c :: p') dot_path) eqn:Ed; [right; left; auto|].
destruct (fs_lookup fs (c :: p')) as [data|] eqn:Ef; [right; right; eauto| left; auto].
Qed.

Definition compat (sel : option bool) (b : bool) : Prop := forall b', sel = Some b' -> b = b'.

Definition sel_default (sel : option bool) : bool := match sel with Some b => b | None => false end.

Lemma compat_default : forall sel, compat sel (sel_default sel).
Proof. intros [b|] b' E; [injection E as ->; reflexivity| discriminate]. Qed.

Definition ra_trace (path : list Z) (fs : Fs) (b : bool) : ctrace :=
match (if b then open_class path fs else OCFail) with
| OCFail => ct_diag (msg_cannot_open path)
| OCDir => ct_diag (msg_read_error path)
| OCFile data => file_trace (map bv_unsigned data)
end.

Lemma ctrace_of_2 : forall argv fs b, Z.of_nat (length argv) = 2 -> ctrace_of argv fs b = ra_trace (nth 1 argv []) fs b.
Proof. intros argv fs b H. unfold ctrace_of. rewrite H. reflexivity. Qed.

Lemma ctrace_of_usage : forall argv fs b, Z.of_nat (length argv) <> 2 ->
ctrace_of argv fs b = ct_diag (msg_usage (nth 0 argv [])).
Proof. intros argv fs b H. unfold ctrace_of. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma firstn_add_skipn : forall {A} n k (l : list A), (n <= length l)%nat ->
firstn n l ++ firstn k (skipn n l) = firstn (n + k) l.
Proof.
intros A n. induction n as [|n IH]; intros k l H; [reflexivity|].
destruct l as [|x l]; cbn in H; [lia|]. cbn [firstn skipn app Nat.add]. f_equal. apply IH. lia.
Qed.

Lemma firstn_prefix_len : forall {A} n c (l : list A), (n <= length l)%nat ->
firstn n l ++ firstn c (skipn n l) = firstn (n + length (firstn c (skipn n l))) l.
Proof.
intros A n c l H. rewrite <- firstn_add_skipn by exact H. f_equal.
rewrite length_firstn. rewrite firstn_min_length. reflexivity.
Qed.

Lemma file_read_lit : forall data n cnt, 0 <= cnt < 2^64 -> Z.of_nat n < 2^64 ->
file_read data (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 cnt) = firstn (Z.to_nat cnt) (skipn n data).
Proof.
intros data n cnt Hc Hn. rewrite file_read_unguarded. unfold word_to_nat. rewrite !unsigned_lit by lia.
rewrite Nat2Z.id. reflexivity.
Qed.

Definition capk (c : Z) : Prop := exists k, (k <= 10)%nat /\ c = 65536 * 2 ^ (Z.of_nat k).

Lemma capk_le : forall c, capk c -> 65536 <= c <= 67108864.
Proof.
intros c (k & Hk & ->). split.
- pose proof (Z.pow_le_mono_r 2 0 (Z.of_nat k) ltac:(lia) ltac:(lia)). lia.
- pose proof (Z.pow_le_mono_r 2 (Z.of_nat k) 10 ltac:(lia) ltac:(lia)). change (2^10) with 1024 in *. lia.
Qed.

Lemma capk_double : forall c, capk c -> c < 67108864 -> capk (c * 2).
Proof.
intros c (k & Hk & ->) Hlt. exists (S k). split.
- destruct (Nat.eq_dec k 10) as [->|NE]; [cbn in Hlt; lia| lia].
- rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
Qed.

Section ReadLoop.
Variable sel : option bool.
Variable X : list event -> Prop.
Variable rstage : Z.
Variable fs : Fs.
Variable path : list Z.
Variable tr0 : list event.

Definition Ifile (p : list byte) (data : list byte) (st : @rd_st bptr) : assnE PState :=
fun s mo tr => exists n, rd_content st = map bv_unsigned (firstn n data) /\ (n <= length data)%nat
/\ fd_lookup (m_fds mo) (Z_to_bv 64 3) = Some (FdFile p (Z_to_bv 64 (Z.of_nat n)))
/\ m_fs mo = fs /\ fs_lookup fs p = Some data
/\ Z.of_nat n <= rd_cap st /\ capk (rd_cap st) /\ ps_so s = stdout_init /\ tr = tr0.

Definition Qfile (data : list byte) (r : rd_result (ptr:=bptr)) : assnE PState :=
fun s mo tr => m_fs mo = fs /\ ps_so s = stdout_init /\
match r with
| RdExit => 67108864 <= zlength data /\ tr = tr0 ++ evw 2 msg_too_big
| RdDone _ content => content = map bv_unsigned data /\ zlength data < 67108864 /\ tr = tr0
end.

Definition Kobs (fds : list (word * FdEntry)) (so : stdout_st) (tr1 : list event) : assnE PState :=
fun s mo tr => m_fds mo = fds /\ m_fs mo = fs /\ ps_so s = so /\ tr = tr1.

Lemma Kobs_fstable : forall fds so tr1, fstable (Kobs fds so tr1).
Proof. intros fds so tr1 s mo tr s' mo' (H1 & H2 & H3 & H4) Hso Hfd Hfs. unfold Kobs. splits; congruence. Qed.

Lemma read_loop_body_file_E : forall p data st,
mspecE sel X (Ifile p data st) (read_loop_body io_diag raw_malloc raw_free rstage 3 path st)
(fun r => match r with inl st' => Ifile p data st' | inr v => Qfile data v end).
Proof.
intros p data st. unfold read_loop_body.
apply mspecE_pointwise. intros s0 mo0 tr1 (n & Hc & Hn & Hfd & Hfs & Hdata & Hcap & Hk & Hso & ->).
pose proof (capk_le _ Hk) as Hkb.
assert (Hlen : zlength (rd_content st) = Z.of_nat n).
{ rewrite Hc. unfold zlength. rewrite length_map, length_firstn. lia. }
eapply mspecE_bind with (Q1 := fun g s mo tr => match g with
| None => Qfile data RdExit s mo tr
| Some st1 => Ifile p data st1 s mo tr /\ rd_content st1 = rd_content st /\ Z.of_nat n < rd_cap st1 end).
- destruct (Z.eqb_spec (zlength (rd_content st)) (rd_cap st)) as [Eq|NE].
+ destruct (MAX_INPUT <=? rd_cap st) eqn:Emax.
* apply Z.leb_le in Emax. unfold MAX_INPUT in Emax.
eapply mspecE_seq.
{ eapply mspecE_pre; [apply (s_diag_E sel X DTooBig tr0 (fun s mo => s = s0 /\ mo = mo0))|].
intros s mo tr (-> & -> & ->). auto. }
intros _. apply mspecE_ret. intros s mo tr ((-> & ->) & ->). unfold Qfile. splits; [exact Hfs| exact Hso| |reflexivity].
assert (Z.of_nat n = 67108864) by lia. unfold zlength. lia.
* apply Z.leb_gt in Emax. unfold MAX_INPUT in Emax.
eapply mspecE_bind.
{ eapply mspecE_pre; [apply (raw_malloc_E sel X (rd_cap st * 2) (Kobs (m_fds mo0) stdout_init tr0)); [apply Kobs_fstable| apply size_ok; lia]|].
intros s mo tr (-> & -> & ->). unfold Kobs. auto. }
intros [nb|]; [|apply mspecE_pure; intros []; reflexivity].
apply mspecE_pure. intros _.
eapply mspecE_seq; [apply raw_free_E; apply Kobs_fstable|]. intros _.
apply mspecE_ret. intros s mo tr (Hfd' & Hfs' & Hso' & ->). unfold Ifile. cbn [rd_content rd_cap].
split; [|split; [reflexivity| lia]].
exists n. splits; auto; try congruence; try lia. apply capk_double; [exact Hk| lia].
+ apply mspecE_ret. intros s mo tr (-> & -> & ->). split; [|split; [reflexivity| lia]].
exists n. splits; auto.
- intros [st1|]; [|apply mspecE_ret; intros s mo tr H; exact H].
apply mspecE_pointwise. intros s1 mo1 tr1' ((n' & Hc1 & Hn1 & Hfd1 & Hfs1 & _ & Hcap1 & Hk1 & Hso1 & ->) & Hc' & Hlt).
assert (En : n' = n).
{ rewrite Hc in Hc'. rewrite Hc1 in Hc'. apply (f_equal (@length Z)) in Hc'. rewrite !length_map, !length_firstn in Hc'. lia. }
subst n'.
pose proof (capk_le _ Hk1) as Hkb1.
cbv zeta. rewrite Hlen.
set (cnt := if READ_CAP <? rd_cap st1 - Z.of_nat n then READ_CAP else rd_cap st1 - Z.of_nat n).
assert (Hcnt : 0 < cnt <= rd_cap st1 - Z.of_nat n /\ cnt <= 65536).
{ unfold cnt, READ_CAP. destruct (Z.ltb_spec 65536 (rd_cap st1 - Z.of_nat n)); lia. }
eapply mspecE_bind with (Q1 := fun a s mo tr => s = s1 /\ tr = tr0 /\ m_fs mo = fs /\
a = RdData (file_read data (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 cnt)) /\
fd_lookup (m_fds mo) (Z_to_bv 64 3) = Some (FdFile p (Z_to_bv 64 (Z.of_nat n + Z.of_nat (length (file_read data (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 cnt))))))).
{ apply msysE_node; [exact I| |].
- intros s mo tr (-> & -> & ->). apply nprog_read. rewrite Hfd1, Hfs1. rewrite Hdata. discriminate.
- intros s mo tr rsp mo' evs a (-> & -> & ->) Hst Hd.
rewrite <- Hfs1 in Hdata.
destruct (stepR_read_file sel 3 rstage cnt mo1 rsp mo' evs a p (Z_to_bv 64 (Z.of_nat n)) data ltac:(lia) Hfd1 Hdata Hst Hd)
as (-> & -> & ->).
rewrite app_nil_r. splits; auto.
rewrite m_fds_with_fds, fd_lookup_insert, bv_eqb_refl. unfold len_word. rewrite lit_add_lit. reflexivity. }
intros a. apply mspecE_pointwise. intros s2 mo2 tr2 (-> & -> & Hfs2 & -> & Hfd2).
rewrite (file_read_lit data n cnt) in Hfd2 |- * by lia.
set (bs := firstn (Z.to_nat cnt) (skipn n data)) in *.
destruct (Nat.eqb_spec (length bs) 0) as [E0|NE0].
+ apply mspecE_ret. intros s mo tr (-> & -> & ->). unfold Qfile. splits; [exact Hfs2| exact Hso1| | |reflexivity].
* rewrite Hc1. f_equal. apply length_zero_iff_nil in E0. unfold bs in E0.
assert (Hsk : skipn n data = []).
{ destruct (skipn n data) as [|x l] eqn:Esk; [reflexivity|]. exfalso.
destruct (Z.to_nat cnt) eqn:Ec; [lia|]. cbn in E0. discriminate. }
assert (Hnd : n = length data).
{ pose proof (length_skipn n data) as L. rewrite Hsk in L. cbn in L. lia. }
subst n. apply firstn_all.
* assert (Hsk : skipn n data = []).
{ apply length_zero_iff_nil in E0. unfold bs in E0.
destruct (skipn n data) as [|x l] eqn:Esk; [reflexivity|]. exfalso.
destruct (Z.to_nat cnt) eqn:Ec; [lia|]. cbn in E0. discriminate. }
pose proof (length_skipn n data) as L. rewrite Hsk in L. cbn in L. unfold zlength. lia.
+ apply mspecE_ret. intros s mo tr (-> & -> & ->). unfold Ifile. cbn [rd_content rd_cap].
exists (n + length bs)%nat. splits; auto.
* rewrite Hc1. unfold u8s_of_bytes. rewrite <- map_app. f_equal. apply firstn_prefix_len. exact Hn1.
* unfold bs. rewrite length_firstn, length_skipn. lia.
* rewrite Hfd2. f_equal. f_equal. f_equal. lia.
* unfold bs. rewrite length_firstn. lia.
Qed.

Definition Idir (st : @rd_st bptr) : assnE PState :=
fun s mo tr => fd_lookup (m_fds mo) (Z_to_bv 64 3) = Some FdDir /\ m_fs mo = fs /\ ps_so s = stdout_init /\ tr = tr0
/\ rd_content st = [] /\ rd_cap st = 65536.

Definition Qdir (r : rd_result (ptr:=bptr)) : assnE PState :=
fun s mo tr => r = RdExit /\ m_fs mo = fs /\ ps_so s = stdout_init /\ tr = tr0 ++ evw 2 (msg_read_error path).

Lemma read_loop_body_dir_E : forall st,
mspecE sel X (Idir st) (read_loop_body io_diag raw_malloc raw_free rstage 3 path st)
(fun r => match r with inl st' => Idir st' | inr v => Qdir v end).
Proof.
intros st. unfold read_loop_body.
apply mspecE_pointwise. intros s0 mo0 tr1 (Hfd & Hfs & Hso & -> & Hc & Hcap).
rewrite Hc, Hcap. cbn [zlength length Z.of_nat]. change (0 =? 65536) with false. cbv iota.
eapply mspecE_bind with (Q1 := fun g s mo tr => g = Some st /\ s = s0 /\ mo = mo0 /\ tr = tr0); [apply mspecE_ret; auto|].
intros g. apply mspecE_pointwise. intros s1 mo1 tr2 (-> & -> & -> & ->).
cbv zeta. rewrite Hcap, Hc. change (if READ_CAP <? 65536 - zlength (@nil Z) then READ_CAP else 65536 - zlength (@nil Z)) with 65536.
eapply mspecE_bind with (Q1 := fun a s mo tr => s = s0 /\ mo = mo0 /\ tr = tr0 /\ exists e, a = RdErr e).
{ apply msysE_node; [exact I| |].
- intros s mo tr (-> & -> & ->). apply nprog_read. rewrite Hfd. exact I.
- intros s mo tr rsp mo' evs a (-> & -> & ->) Hst Hd.
destruct (stepR_read_dir sel 3 rstage 65536 mo0 rsp mo' evs a ltac:(lia) Hfd Hst Hd) as (-> & -> & He).
rewrite app_nil_r. auto. }
intros a. apply mspecE_pointwise. intros s2 mo2 tr3 (-> & -> & -> & e & ->).
eapply mspecE_seq.
{ eapply mspecE_pre; [apply (s_diag_E sel X (DReadError path) tr0 (fun s mo => s = s0 /\ mo = mo0))|].
intros s mo tr (-> & -> & ->). auto. }
intros _. apply mspecE_ret. intros s mo tr ((-> & ->) & ->). unfold Qdir. auto.
Qed.

End ReadLoop.

Section ReadAll.
Variable sel : option bool.
Variable X : list event -> Prop.
Variable rstage : Z.
Variable fs : Fs.
Variable path : list Z.
Variable tr0 : list event.

Definition Qra (r : rd_result (ptr:=bptr)) : assnE PState :=
fun s mo tr => m_fs mo = fs /\ ps_so s = stdout_init /\
match r with
| RdExit => exists b, compat sel b /\ tr = tr0 ++ ct_flat (ra_trace path fs b) /\ ct_code (ra_trace path fs b) = 2
/\ (forall data, (if b then open_class path fs else OCFail) = OCFile data -> 67108864 <= zlength data)
| RdDone _ content => exists data, open_class path fs = OCFile data /\ content = map bv_unsigned data
/\ zlength data < 67108864 /\ compat sel true /\ tr = tr0
end.

Lemma Z_to_bv_3 : forall v, 3 <= v <= 4096 -> Z_to_bv 64 v = Z_to_bv 64 3 -> v = 3.
Proof.
intros v Hv E. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. exact E.
Qed.

Lemma read_all_E :
mspecE sel X (fun s mo tr => m_fds mo = fds_std /\ m_fs mo = fs /\ ps_so s = stdout_init /\ tr = tr0)
(read_all io_diag raw_malloc raw_free rstage path) Qra.
Proof.
unfold read_all. apply mspecE_pointwise. intros s0 mo0 tr1 (Hfd0 & Hfs0 & Hso0 & ->).
set (p := map (Z_to_bv 8) path).
eapply mspecE_bind with (Q1 := fun a s mo tr => s = s0 /\ tr = tr0 /\ m_fs mo = fs /\
match a with
| SErr _ => (forall b, sel = Some b -> b && open_admits p mo0 = false)
| SVal v => v = 3 /\ openable_b p fs = true /\ compat sel true
/\ m_fds mo = fd_insert fds_std (Z_to_bv 64 3) (if path_eqb p dot_path then FdDir else FdFile p (Z_to_bv 64 0))
end).
{ apply msysE_node; [exact I| intros; apply nprog_open|].
intros s mo tr rsp mo' evs a (-> & -> & ->) Hst Hd.
destruct (stepR_open sel p mo0 rsp mo' evs a Hst Hd) as (-> & Ha). rewrite app_nil_r.
destruct a as [e|v].
- destruct Ha as (-> & Hb). auto.
- destruct Ha as (Hv & Hr & Hop & Hb & ->). rewrite Hfd0, alloc_fd_std in Hv. apply Z_to_bv_3 in Hv; [|exact Hr]. subst v.
rewrite m_fs_with_fds, m_fds_with_fds. rewrite Hfs0 in Hop. rewrite Hfd0. splits; auto.
intros b' E. destruct (Hb b' E) as [-> _]. reflexivity. }
intros a. apply mspecE_pointwise. intros s1 mo1 tr2 (-> & -> & Hfs1 & Ha).
destruct a as [e|v].
-
eapply mspecE_seq.
{ eapply mspecE_pre; [apply (s_diag_E sel X (DCannotOpen path) tr0 (fun s mo => s = s0 /\ mo = mo1))|].
intros s mo tr (-> & -> & ->). auto. }
intros _. apply mspecE_ret. intros s mo tr ((-> & ->) & ->). unfold Qra. splits; auto.
exists (sel_default sel). split; [apply compat_default|].
assert (Hc : ra_trace path fs (sel_default sel) = ct_diag (msg_cannot_open path) /\ (if sel_default sel then open_class path fs else OCFail) = OCFail).
{ unfold ra_trace. destruct (sel_default sel) eqn:Ed; [|split; reflexivity].
destruct sel as [b|]; [|discriminate]. cbn in Ed. subst b. specialize (Ha true eq_refl).
cbn [andb] in Ha. unfold open_admits in Ha. rewrite Hfd0, fd_free_std, Hfs0, andb_true_r in Ha.
destruct (open_class_cases path fs) as [(_ & ->)|[(Hop & _)|(Hop & _)]]; [split; reflexivity| fold p in Hop; congruence| fold p in Hop; congruence]. }
destruct Hc as [Hc Hc2]. rewrite Hc, ct_flat_diag. cbn [ct_code ct_diag]. splits; auto.
intros data Hd. rewrite Hc2 in Hd. discriminate.
- destruct Ha as (-> & Hop & Hcomp & Hfd1).
eapply mspecE_bind.
{ eapply mspecE_pre; [apply (raw_malloc_E sel X 65536 (Kobs fs (m_fds mo1) stdout_init tr0)); [apply Kobs_fstable| apply size_ok; lia]|].
intros s mo tr (-> & -> & ->). unfold Kobs. auto. }
intros [buf|]; [|apply mspecE_pure; intros []; reflexivity]. apply mspecE_pure. intros _.
destruct (open_class_cases path fs) as [(Hop' & _)|[(_ & Hdot & Hcl)|(_ & Hndot & data & Hdata & Hcl)]];
[fold p in Hop'; congruence| |].
+
fold p in Hdot. rewrite Hdot in Hfd1.
eapply mspecE_bind.
{ eapply mspecE_pre.
- apply (mspecE_loop sel X (read_loop_body io_diag raw_malloc raw_free rstage 3 path)
(Idir fs tr0) (Qdir fs path tr0)).
intros st. apply read_loop_body_dir_E.
- intros s mo tr (Hfd & Hfs & Hso & ->). unfold Idir. cbn [rd_content rd_cap]. splits; auto.
rewrite Hfd, Hfd1, fd_lookup_insert, bv_eqb_refl. reflexivity. }
intros r. apply mspecE_pointwise. intros s2 mo2 tr3 (-> & Hfs2 & Hso2 & ->).
apply mspecE_ret. intros s mo tr (-> & -> & ->). unfold Qra. splits; auto.
exists true. split; [exact Hcomp|]. unfold ra_trace. rewrite Hcl, ct_flat_diag. cbn [ct_code ct_diag]. splits; auto.
intros data Hd. discriminate.
+
fold p in Hndot, Hdata. rewrite Hndot in Hfd1.
eapply mspecE_bind.
{ eapply mspecE_pre.
- apply (mspecE_loop sel X (read_loop_body io_diag raw_malloc raw_free rstage 3 path)
(Ifile fs tr0 p data) (Qfile fs tr0 data)).
intros st. apply read_loop_body_file_E.
- intros s mo tr (Hfd & Hfs & Hso & ->). unfold Ifile. exists 0%nat. cbn [rd_content rd_cap firstn map].
splits; auto; try lia.
+ rewrite Hfd, Hfd1, fd_lookup_insert, bv_eqb_refl. reflexivity.
+ exists 0%nat. split; [lia| reflexivity]. }
intros r. destruct r as [|buf' content].
* apply mspecE_ret. intros s mo tr (Hfs2 & Hso2 & Hbig & ->). unfold Qra. splits; auto.
exists true. split; [exact Hcomp|]. unfold ra_trace. rewrite Hcl.
assert (Ht : file_trace (map bv_unsigned data) = ct_diag msg_too_big).
{ unfold file_trace. replace (zlength (map bv_unsigned data)) with (zlength data) by (unfold zlength; rewrite length_map; reflexivity).
destruct (Z.leb_spec 67108864 (zlength data)); [reflexivity| lia]. }
rewrite Ht, ct_flat_diag. cbn [ct_code ct_diag]. splits; auto.
intros data' Hd. injection Hd as <-. exact Hbig.
* apply mspecE_pointwise. intros s2 mo2 tr3 (Hfs2 & Hso2 & -> & Hsmall & ->).
eapply mspecE_bind with (Q1 := fun _ s mo tr => s = s2 /\ m_fs mo = fs /\ tr = tr0).
{ apply msysE_node; [exact I| intros; apply nprog_close; lia|].
intros s mo tr rsp mo' evs a (-> & -> & ->) Hst Hd. destruct (stepR_close sel 3 mo2 rsp mo' evs Hst) as (-> & Hfs').
rewrite app_nil_r. splits; congruence. }
intros _. apply mspecE_ret. intros s mo tr (-> & Hfs3 & ->). unfold Qra. splits; auto.
exists data. auto.
Qed.

End ReadAll.

Section Main.
Variable sel : option bool.
Variable X : list event -> Prop.
Variable rstage : Z.
Variable fs : Fs.
Variable tr0 : list event.

Definition Qmain (argv : list (list Z)) (code : Z) : assnE PState :=
fun s mo tr => exists b, compat sel b /\ code = ct_code (ctrace_of argv fs b) /\ m_fs mo = fs
/\ tr ++ evw 1 (so_buf (ps_so s)) = tr0 ++ ct_flat (ctrace_of argv fs b)
/\ run_defined fs argv b.

Lemma Km_fs : Km_ok (fun mo => m_fs mo = fs).
Proof. intros mo mo' H _ E. congruence. Qed.

Lemma zlength_map_bv : forall (data : list byte), zlength (map bv_unsigned data) = zlength data.
Proof. intros. unfold zlength. rewrite length_map. reflexivity. Qed.

Lemma err_exit_E : forall d buf fds tr1,
mspecE sel X (Kobs fs fds stdout_init tr1)
(mbind (io_diag d) (fun _ => mbind (raw_free buf) (fun _ => mret 2)))
(fun c s mo tr => c = 2 /\ m_fs mo = fs /\ ps_so s = stdout_init /\ tr = tr1 ++ evw 2 (diag_bytes d)).
Proof.
intros d buf fds tr1.
eapply mspecE_seq with (R := Kobs fs fds stdout_init (tr1 ++ evw 2 (diag_bytes d))).
{ eapply mspecE_conseq; [apply (s_diag_E sel X d tr1 (fun s mo => m_fds mo = fds /\ m_fs mo = fs /\ ps_so s = stdout_init))| |].
- intros s mo tr (H1 & H2 & H3 & H4). auto.
- intros _ s mo tr ((H1 & H2 & H3) & H4). unfold Kobs. auto. }
intros _. eapply mspecE_seq; [apply raw_free_E; apply Kobs_fstable|]. intros _.
apply mspecE_ret. intros s mo tr (H1 & H2 & H3 & H4). auto.
Qed.

Lemma file_trace_ok : forall content eb, zlength content < 67108864 ->
~ zlength content < HDR_MIN -> ~ zlength content < HDR_MIN + Z.land (le16 content) 0x7fff ->
canon_fuzz (skipn (Z.to_nat (6 + Z.land (le16 content) 0x7fff)) content) = (0, eb) ->
let n := Z.to_nat (1 + Z.land (if 0 <? Z.land (le16 content) 0x7fff then znth content 2 else 0) 3) in
ct_code (file_trace content) = 0 /\
ct_flat (file_trace content) = calls_events eb n ++ evw 1 (zeros_out (n - 1)).
Proof.
intros content eb Hb H1 H2 Hcf n. unfold file_trace, HDR_MIN, le16 in *.
destruct (Z.leb_spec 67108864 (zlength content)); [lia|]. destruct (Z.ltb_spec (zlength content) 6); [lia|].
unfold cfg_len, cfg_word. destruct (Z.ltb_spec (zlength content) (6 + Z.land (znth content 0 + znth content 1 * 256) 32767)); [lia|].
unfold target_trace, cfg_payload, cfg_calls, cfg_count, cfg_len, cfg_word. rewrite Hcf. fold n.
cbn [ct_code]. split; [destruct (Z.testbit _ 15); reflexivity|].
destruct (calls_pos (if 0 <? Z.land (znth content 0 + znth content 1 * 256) 32767 then znth content 2 else 0)) as [Hn1 _].
fold n in Hn1. destruct n as [|j]; [lia|]. replace (S j - 1)%nat with j by lia.
unfold ct_flat. cbn [ct_segs]. rewrite !map_app, !concat_app. cbn [map concat seg_events fst snd calls_events].
rewrite !app_nil_r, <- !app_assoc. do 2 f_equal.
change (emit_bytes 0) with [48; 10]. fold (zeros_out j). f_equal.
clear. induction j as [|j IH]; [reflexivity|]. cbn [repeat map concat seg_events fst snd]. rewrite IH. reflexivity.
Qed.

Lemma main_model_E : forall argv,
mspecE sel X (fun s mo tr => m_fds mo = fds_std /\ m_fs mo = fs /\ ps_so s = stdout_init /\ tr = tr0)
(main_model io_diag raw_malloc raw_free rstage (target_alloc_init (St:=PState)) X1r6.run (target_alloc_count (St:=PState)) argv) (Qmain argv).
Proof.
intros argv. unfold main_model.
apply mspecE_pointwise. intros s0 mo0 tr1 (Hfd0 & Hfs0 & Hso0 & ->).
destruct (Z.eqb_spec (Z.of_nat (length argv)) 2) as [E2|NE2]; cbn [negb].
-
eapply mspecE_bind; [eapply mspecE_pre; [apply (read_all_E sel X rstage fs (nth 1 argv []) tr0)|]|].
{ intros s mo tr (-> & -> & ->). auto. }
intros [|buf content].
+ apply mspecE_ret. intros s mo tr (Hfs & Hso & b & Hb & -> & Hcode & Hbig). exists b.
rewrite ctrace_of_2 by exact E2. splits; auto.
* rewrite Hso. cbn [so_buf stdout_init evw map]. rewrite app_nil_r. reflexivity.
* intros _ data Hd content Hsmall _ _. specialize (Hbig data Hd). unfold content in Hsmall. rewrite zlength_map_bv in Hsmall. lia.
+ apply mspecE_pointwise. intros s1 mo1 tr2 (Hfs1 & Hso1 & data & Hcl & -> & Hsmall & Hcomp & ->).
assert (Hct : ctrace_of argv fs true = file_trace (map bv_unsigned data)).
{ rewrite ctrace_of_2 by exact E2. unfold ra_trace. rewrite Hcl. reflexivity. }
pose proof (zlength_map_bv data) as Hzl.
set (content := map bv_unsigned data) in *.
assert (Herr : forall d, file_trace content = ct_diag (diag_bytes d) ->
(zlength content < 6 \/ zlength content < 6 + cfg_len content) ->
mspecE sel X (fun s mo tr => s = s1 /\ mo = mo1 /\ tr = tr0)
(mbind (io_diag d) (fun _ => mbind (raw_free buf) (fun _ => mret 2))) (Qmain argv)).
{ intros d Hft Hbad. eapply mspecE_conseq; [apply (err_exit_E d buf (m_fds mo1) tr0)| |].
- intros s mo tr (-> & -> & ->). unfold Kobs. auto.
- intros c s mo tr (-> & Hfs & Hso & ->). exists true. rewrite Hct, Hft, ct_flat_diag. cbn [ct_code ct_diag].
splits; auto.
+ rewrite Hso. cbn [so_buf stdout_init evw map]. apply app_nil_r.
+ intros _ data' Hd'. rewrite Hcl in Hd'. injection Hd' as <-. fold content. cbv zeta. intros _ N1 N2. lia. }
cbv zeta.
destruct (Z.ltb_spec (zlength content) HDR_MIN) as [Hshort|Hlong].
* apply Herr; [|left; exact Hshort]. unfold file_trace, HDR_MIN in *.
destruct (Z.leb_spec 67108864 (zlength content)); [lia|]. destruct (Z.ltb_spec (zlength content) 6); [reflexivity| lia].
* destruct (Z.ltb_spec (zlength content) (HDR_MIN + Z.land (le16 content) 0x7fff)) as [Hov|Hok].
-- apply Herr; [|right; exact Hov]. unfold file_trace, HDR_MIN, cfg_len, cfg_word, le16 in *.
destruct (Z.leb_spec 67108864 (zlength content)); [lia|]. destruct (Z.ltb_spec (zlength content) 6); [lia|].
destruct (Z.ltb_spec (zlength content) (6 + Z.land (znth content 0 + znth content 1 * 256) 32767)); [reflexivity| lia].
-- set (cfg := if 0 <? Z.land (le16 content) 0x7fff then znth content 2 else 0) in *.
set (payload := skipn (Z.to_nat (6 + Z.land (le16 content) 0x7fff)) content) in *.
set (n := Z.to_nat (1 + Z.land cfg 3)).

eapply mspecE_seq with (R := SoA ps_so (fun mo => m_fs mo = fs) stdout_init tr0).
{ unfold target_alloc_init. apply mspecE_ret. intros s mo tr (-> & -> & ->). unfold SoA. auto. }
intros _.
eapply mspecE_bind.
{ apply (target_run_E sel X (fun mo => m_fs mo = fs) cfg payload tr0 Km_fs).
unfold payload, zlength in *. rewrite length_skipn. lia. }
intros status. apply mspecE_exI. intros eb.
apply mspecE_pure_l; intros Hcf. apply mspecE_pure_l; intros Hdef. apply mspecE_pure_l; intros ->. fold n.
eapply mspecE_bind with (Q1 := fun st' => fun s mo tr => SoA ps_so (fun mo => m_fs mo = fs) (so_after n) (tr0 ++ calls_events eb n) s mo tr /\ st' = 0).
{ destruct (Z.testbit (le16 content) 15).
- unfold target_alloc_count.
eapply mspecE_bind with (Q1 := fun k s mo tr => SoA ps_so (fun mo => m_fs mo = fs) (so_after n) (tr0 ++ calls_events eb n) s mo tr /\ k = 0);
[apply mspecE_ret; intros s mo tr H; auto|].
intros k. apply mspecE_pure. intros ->. apply mspecE_ret. intros s mo tr H. split; [exact H|]. reflexivity.
- apply mspecE_ret. intros s mo tr H. auto. }
intros status'. apply mspecE_pure. intros ->.
eapply mspecE_seq; [apply raw_free_E; apply SoA_fstable; apply Km_fs|]. intros _.
apply mspecE_ret. intros s mo tr (Hfs & Hso & ->). exists true. rewrite Hct.
destruct (file_trace_ok content eb ltac:(lia) ltac:(lia) ltac:(lia) Hcf) as [Hcode Hflat]. fold cfg n in Hflat.
rewrite Hcode, Hflat, Hso. splits; auto.
++ destruct (calls_pos cfg) as [Hn1 _]. fold n in Hn1. destruct n as [|j]; [lia|].
cbn [so_after so_buf]. replace (S j - 1)%nat with j by lia. rewrite <- app_assoc. reflexivity.
++ intros _ data' Hd'. rewrite Hcl in Hd'. injection Hd' as <-. fold content. cbv zeta. intros _ _ _.
unfold cfg_payload, cfg_len, cfg_word. exact Hdef.
-
eapply mspecE_seq.
{ eapply mspecE_pre; [apply (s_diag_E sel X (DUsage (nth 0 argv [])) tr0 (fun s mo => s = s0 /\ mo = mo0))|].
intros s mo tr (-> & -> & ->). auto. }
intros _. apply mspecE_ret. intros s mo tr ((-> & ->) & ->). exists (sel_default sel).
rewrite ctrace_of_usage by exact NE2. rewrite ct_flat_diag. cbn [ct_code ct_diag diag_bytes]. split; [apply compat_default|].
splits; auto.
+ rewrite Hso0. cbn [so_buf stdout_init evw map]. apply app_nil_r.
+ intros E2. contradiction.
Qed.

End Main.
