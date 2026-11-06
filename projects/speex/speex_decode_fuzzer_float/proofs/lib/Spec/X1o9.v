(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ri X1r0 X1rm X1o8.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Section TargetRunSpec.
Context {St ptr : Type}.
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variable emit : Z -> M St unit.
Variable fuzz : list Z -> M St Z.
Variable own : list ptr -> assn St.

Hypothesis Hdm : forall X n, 0 <= n ->
mspec (own X) (drv_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo | None => own X s mo end).
Hypothesis Hdf : forall X p, mspec (own (p :: X)) (drv_free p) (fun _ => own X).
Hypothesis Hemit : forall X rc, mspec (own X) (emit rc) (fun _ => own X).
Hypothesis Hfuzz : forall X payload, bytes_ok payload -> mspec (own X) (fuzz payload) (fun _ => own X).

#[using="Hemit Hfuzz"] Lemma run_calls_spec : forall X n payload rc, bytes_ok payload ->
mspec (own X) (run_calls emit fuzz n payload rc) (fun _ => own X).
Proof.
intros X n. induction n as [|n IH]; intros payload rc Hb; cbn [run_calls].
- apply mspec_ret. intros s mo H. exact H.
- eapply mspec_seq; [apply Hfuzz; exact Hb|]. intros rc'. eapply mspec_seq; [apply Hemit|]. intros _. apply IH. exact Hb.
Qed.

#[using="Hdm Hdf Hemit Hfuzz"] Theorem target_run_spec : forall X cfg payload, bytes_ok payload ->
mspec (own X) (target_run drv_malloc drv_free emit fuzz cfg payload) (fun _ => own X).
Proof.
intros X cfg payload Hb. unfold target_run.
eapply mspec_bind with (Q1 := fun owned s mo => match owned with
| None => own X s mo
| Some None => own X s mo
| Some (Some q) => own (q :: X) s mo end).
{ apply mspec_if; intros _.
- apply mspec_ret. intros s mo H. exact H.
- eapply mspec_bind; [apply Hdm; apply zlength_nonneg|]. intros [q|]; apply mspec_ret; intros s mo H; exact H. }
intros [[q|]|]; cbn beta iota.
- eapply mspec_seq; [apply run_calls_spec; exact Hb|]. intros rc. eapply mspec_seq; [apply Hdf|]. intros _.
apply mspec_ret. intros s mo H. exact H.
- eapply mspec_seq; [apply run_calls_spec; exact Hb|]. intros rc. eapply mspec_seq; [apply mspec_ret; intros s mo H; exact H|]. intros _.
apply mspec_ret. intros s mo H. exact H.
- apply mspec_ret. intros s mo H. exact H.
Qed.
End TargetRunSpec.

Section DriverSpec.
Context {St ptr : Type}.
Variable io_diag : diag_msg -> M St unit.
Variable drv_malloc : Z -> M St (option ptr).
Variable drv_free : ptr -> M St unit.
Variable read_stage : Z.
Variable alloc_init : Z -> M St unit.
Variable run : Z -> list Z -> M St Z.
Variable alloc_count : M St Z.

Variable own : list ptr -> assn St.

Definition diag_ok (d : diag_msg) : Prop :=
match d with
| DUsage a | DCannotOpen a | DReadError a => zlength a < 2^17
| _ => True
end.

Hypothesis Hdm : forall X n, 0 <= n ->
mspec (own X) (drv_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p, mspec (own (p :: X)) (drv_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hdiag : forall X d, diag_ok d -> mspec (own X) (io_diag d) (fun _ => own X).
Hypothesis Hinit : forall X bm, mspec (own X) (alloc_init bm) (fun _ => own X).
Hypothesis Hcount : forall X, mspec (own X) alloc_count (fun _ => own X).
Hypothesis Hrun : forall X cfg payload, bytes_ok payload -> mspec (own X) (run cfg payload) (fun _ => own X).

Hypothesis Hown_minv : forall X s mo, own X s mo -> minv mo /\ m_halted mo = None.
Hypothesis Hown_fds : forall X s mo mo', own X s mo ->
m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> own X s mo'.

#[using="Hown_minv Hown_fds"] Lemma own_after_node : forall X s mo n rsp mo' evs,
own X s mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo ->
match n with NMmap _ _ _ flags => mmap_noreserve_b (Z_to_bv 64 flags) = false | _ => True end ->
own X s mo'.
Proof.
intros X s mo n rsp mo' evs Ho Hst Hvm Hfl. destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
destruct (minv_preserved n mo rsp mo' evs Hfl Hmi Hh Hst) as [Hh' Hmi']. eapply Hown_fds; eauto.
Qed.

Definition rd_inv (X : list ptr) (st : rd_st) : assn St := fun s mo =>
own (rd_buf st :: X) s mo
/\ zlength (rd_content st) <= rd_cap st
/\ (exists k, (k <= 10)%nat /\ rd_cap st = 65536 * 2 ^ (Z.of_nat k))
/\ bytes_ok (rd_content st).

Definition rd_meas (st : @rd_st ptr) : nat := Z.to_nat (MAX_INPUT + 1 - zlength (rd_content st)).

#[using="Type"] Lemma zlength_app' {A} (l1 l2 : list A) : zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. unfold zlength. rewrite length_app. lia. Qed.
#[using="Type"] Lemma zlength_u8s : forall bs, zlength (u8s_of_bytes bs) = zlength bs.
Proof. intros. unfold u8s_of_bytes, zlength. rewrite length_map. reflexivity. Qed.
#[using="Type"] Lemma bytes_ok_u8s : forall bs, bytes_ok (u8s_of_bytes bs).
Proof.
intros bs. unfold u8s_of_bytes, bytes_ok. apply Forall_map. apply Forall_forall. intros b _.
pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

#[using="Type"] Lemma pow2_le_1024 : forall k, (k <= 10)%nat -> 2 ^ Z.of_nat k <= 1024.
Proof.
intros k Hk. change 1024 with (2 ^ 10). apply Z.pow_le_mono_r; lia.
Qed.

#[using="Hdm Hdf Hperm Hdiag Hown_minv Hown_fds"] Lemma read_loop_body_spec : forall X fd path st,
zlength path < 2^17 -> 0 <= fd ->
mspec (rd_inv X st) (read_loop_body io_diag drv_malloc drv_free read_stage fd path st)
(fun r s mo => match r with
| inl st' => rd_inv X st' s mo /\ (rd_meas st' < rd_meas st)%nat
| inr RdExit => exists X', own X' s mo
| inr (RdDone buf content) => own (buf :: X) s mo /\ zlength content <= MAX_INPUT /\ bytes_ok content
end).
Proof.
intros X fd path st Hpath Hfd. unfold read_loop_body.
eapply mspec_bind with
(Q1 := fun g s mo => match g with
| None => exists X', own X' s mo
| Some st1 => rd_inv X st1 s mo /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1
end).
{ apply mspec_if_pre.
- apply mspec_if_pre.
+ eapply mspec_seq; [eapply mspec_pre; [apply Hdiag; exact I|]|].
{ intros s mo [[[Ho _] _] _]. exact Ho. }
intros _. apply mspec_ret. intros s mo Ho. exists (rd_buf st :: X). exact Ho.
+ apply mspec_pointwise. intros s0 mo0 [[(Ho0 & Hlen & (k & Hk & Hcap) & Hbytes) Heq] Hlt].
apply Z.eqb_eq in Heq. apply Z.leb_gt in Hlt.
pose proof (pow2_le_1024 k Hk) as Hp.
eapply mspec_bind. { eapply mspec_pre; [apply Hdm; lia|]. intros s mo [-> ->]. exact Ho0. }
intros [nb|]; cbn beta iota.
* apply mspec_pure. intros _. eapply mspec_seq.
{ eapply mspec_pre; [apply (Hdf (nb :: X) (rd_buf st))|].
intros s mo Ho. eapply Hperm; [apply perm_swap| exact Ho]. }
intros _. apply mspec_ret. intros s mo Ho. cbn. unfold rd_inv. cbn. splits; auto; try lia.
exists (S k). split; [unfold MAX_INPUT in Hlt; assert (k <> 10)%nat by (intros ->; cbn in Hcap; lia); lia|].
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
* eapply mspec_seq; [apply Hdiag; exact I|]. intros _. apply mspec_ret. intros s mo Ho. exists (rd_buf st :: X). exact Ho.
- apply mspec_ret. intros s mo [[Ho [Hlen [Hk Hb]]] Hne]. apply Z.eqb_neq in Hne. split; [|split; [reflexivity|lia]]. split; [exact Ho|]. auto. }
intros [st1|]; cbn beta iota.
2:{ apply mspec_ret. intros s mo H. exact H. }
apply mspec_pointwise. intros s1 mo1 ((Ho & Hlen & (k & Hk & Hcap) & Hbytes) & Hct & Hlt).
pose proof (pow2_le_1024 k Hk) as Hp.
set (cnt := if READ_CAP <? rd_cap st1 - zlength (rd_content st) then READ_CAP else rd_cap st1 - zlength (rd_content st)).
assert (Hcnt : 1 <= cnt <= rd_cap st1 - zlength (rd_content st) /\ cnt <= READ_CAP).
{ subst cnt. unfold READ_CAP. destruct (Z.ltb_spec 65536 (rd_cap st1 - zlength (rd_content st))); lia. }
apply mspec_bind with (Q1 := fun a s mo => s = s1 /\ own (rd_buf st1 :: X) s mo /\
match a with RdErr _ => True | RdData bs => zlength bs <= cnt end).
{ apply mspec_sys. intros s mo [-> ->]. split; [exact I|].
intros rsp mo' evs Hst.
pose proof (nstep_dec_read fd _ cnt mo1 rsp mo' evs ltac:(unfold READ_CAP in *; lia) Hst) as (_ & a & Hdec & Ha).
exists a. split; [exact Hdec|].
cbn beta. split; [reflexivity|].
assert (Hvm : m_vmmaps mo' = m_vmmaps mo1).
{ destruct a as [e|bs]; [destruct Ha as [-> _]; reflexivity|].
destruct Ha as (p & off & data & _ & _ & _ & ->). reflexivity. }
split; [eapply own_after_node; eauto; exact I|].
destruct a as [e|bs]; [exact I|]. destruct Ha as (p & off & data & _ & _ & -> & _).
unfold zlength. pose proof (length_file_read_le_count data off cnt ltac:(unfold READ_CAP in *; lia)). lia. }
intros [e|bs]; cbn beta iota.
- eapply mspec_seq. { eapply mspec_pre; [apply Hdiag; exact Hpath|]. intros s mo (_ & Ho' & _). exact Ho'. }
intros _. apply mspec_ret. intros s mo Ho'. exists (rd_buf st1 :: X). exact Ho'.
- apply mspec_if; intros C.
+ apply mspec_ret. intros s mo (-> & Ho' & _). split; [exact Ho'|]. split; [rewrite Hct; unfold MAX_INPUT in *; lia| exact Hbytes].
+ apply mspec_ret. intros s mo (-> & Ho' & Hbs). apply Nat.eqb_neq in C.
assert (1 <= zlength bs) by (unfold zlength in *; destruct bs; cbn in *; [congruence|lia]).
split.
* unfold rd_inv. cbn. split; [exact Ho'|]. rewrite zlength_app', zlength_u8s, Hct. split; [lia|]. split; [exists k; auto|].
unfold bytes_ok in *. rewrite ?Hct in Hbytes. apply Forall_app. split; [exact Hbytes| apply bytes_ok_u8s].
* unfold rd_meas. cbn. rewrite zlength_app', zlength_u8s, Hct. unfold MAX_INPUT in *. lia.
Qed.

Definition path_arg_ok (a : list Z) : Prop :=
path_has_slash (map (Z_to_bv 8) a) = false /\ path_eqb (map (Z_to_bv 8) a) dotdot_path = false.

#[using="Hdm Hdf Hperm Hdiag Hown_minv Hown_fds"] Lemma read_all_spec : forall X path, zlength path < 2^17 -> path_arg_ok path ->
mspec (own X) (read_all io_diag drv_malloc drv_free read_stage path)
(fun r s mo => match r with
| RdExit => exists X', own X' s mo
| RdDone buf content => own (buf :: X) s mo /\ zlength content <= MAX_INPUT /\ bytes_ok content
end).
Proof.
intros X path Hpath Hpok. unfold read_all.
apply mspec_bind with (Q1 := fun r s mo => own X s mo /\ match r with SVal fd => 0 <= fd | SErr _ => True end).
{ apply mspec_sys. intros s mo Ho. split; [exact Hpok|]. intros rsp mo' evs Hst.
destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
pose proof (nstep_dec_open _ mo rsp mo' evs Hmi Hst) as (_ & a & Hdec & Ha).
exists a. split; [exact Hdec|]. cbn beta.
assert (Hvm : m_vmmaps mo' = m_vmmaps mo).
{ destruct a as [e|fd]; [destruct Ha as [-> _]; reflexivity|]. destruct Ha as (_ & _ & _ & ent & _ & ->). reflexivity. }
split; [eapply own_after_node; eauto; exact I|]. destruct a as [e|fd]; [exact I|]. lia. }
intros [e|fd]; cbn beta iota.
- apply mspec_pure. intros _. eapply mspec_seq; [apply Hdiag; exact Hpath|]. intros _. apply mspec_ret. intros s mo Ho. exists X. exact Ho.
- apply mspec_pure. intros Hfd. eapply mspec_bind; [apply Hdm; lia|]. intros [buf|]; cbn beta iota.
2:{ eapply mspec_seq; [apply Hdiag; exact I|]. intros _. apply mspec_ret. intros s mo Ho. exists X. exact Ho. }
apply mspec_pure. intros _.
eapply mspec_bind.
+ eapply mspec_pre.
* apply (mspec_loop (read_loop_body io_diag drv_malloc drv_free read_stage fd path) (rd_inv X)
(fun r s mo => match r with RdExit => exists X', own X' s mo
| RdDone buf content => own (buf :: X) s mo /\ zlength content <= MAX_INPUT /\ bytes_ok content end)
rd_meas).
{ intros st. eapply mspec_post; [apply read_loop_body_spec; [exact Hpath| exact Hfd]|].
intros [st'|[|b c]] s mo H; exact H. }
unfold rd_meas, READ_FUEL. cbn [rd_content]. unfold zlength. cbn [length Z.of_nat]. unfold MAX_INPUT. lia.
* intros s mo Ho. unfold rd_inv. cbn. split; [exact Ho|]. split; [unfold zlength; cbn; lia|]. split; [exists 0%nat; split; [lia|reflexivity]|].
constructor.
+ intros [|buf' content]; cbn beta iota; [apply mspec_ret; intros s mo H; exact H|].
apply mspec_pointwise. intros s1 mo1 [Ho1 Hlen].
eapply mspec_bind with (Q1 := fun _ s mo => own (buf' :: X) s mo).
* apply mspec_sys. intros s mo [-> ->]. split; [exact I|]. intros rsp mo' evs Hst.
pose proof (nstep_dec_close fd mo1 rsp mo' evs Hst) as (_ & a & Hdec & Ha).
exists a. split; [exact Hdec|]. cbn beta.
assert (Hvm : m_vmmaps mo' = m_vmmaps mo1).
{ destruct a as [e|v]; [destruct Ha as (_ & -> & _); reflexivity|]. destruct Ha as (_ & _ & ->). reflexivity. }
eapply own_after_node; eauto; exact I.
* intros _. apply mspec_ret. intros s mo Ho. split; [exact Ho| exact Hlen].
Qed.

#[using="Type"] Lemma bytes_ok_skipn : forall n (l : list Z), bytes_ok l -> bytes_ok (skipn n l).
Proof. intros n l H. unfold bytes_ok in *. rewrite <- (firstn_skipn n l) in H. apply Forall_app in H. tauto. Qed.

#[using="Hdm Hdf Hperm Hdiag Hinit Hcount Hrun Hown_minv Hown_fds"] Lemma main_model_spec : forall X argv,
Forall (fun a => zlength a < 2^17) argv -> Forall path_arg_ok (tl argv) ->
mspec (own X) (main_model io_diag drv_malloc drv_free read_stage alloc_init run alloc_count argv)
(fun _ s mo => exists X', own X' s mo).
Proof.
intros X argv Hargv Htl. unfold main_model.
assert (Hnth : forall i, zlength (nth i argv []) < 2^17).
{ intros i. destruct (nth_in_or_default i argv []) as [Hin| ->]; [|unfold zlength; cbn; lia].
exact (proj1 (Forall_forall _ _) Hargv _ Hin). }
apply mspec_if; intros Hlen2.
{ eapply mspec_seq; [apply Hdiag; cbn; apply Hnth|]. intros _. apply mspec_ret. intros s mo Ho. exists X; exact Ho. }
assert (Hp1 : path_arg_ok (nth 1 argv [])).
{ apply Bool.negb_false_iff in Hlen2. apply Z.eqb_eq in Hlen2. destruct argv as [|a0 [|a1 rest]]; cbn in Hlen2; try lia.
exact (Forall_inv Htl). }
eapply mspec_bind; [apply read_all_spec; [apply Hnth| exact Hp1]|].
intros [|buf content]; cbn beta iota; [apply mspec_ret; intros s mo H; exact H|].
apply mspec_pure. intros [Hlen Hbytes].
apply mspec_if; intros _.
{ eapply mspec_seq; [apply Hdiag; exact I|]. intros _. eapply mspec_seq; [apply Hdf|]. intros _. apply mspec_ret. intros s mo Ho; exists X; exact Ho. }
apply mspec_if; intros _.
{ eapply mspec_seq; [apply Hdiag; exact I|]. intros _. eapply mspec_seq; [apply Hdf|]. intros _. apply mspec_ret. intros s mo Ho; exists X; exact Ho. }
eapply mspec_seq; [apply Hinit|]. intros _.
eapply mspec_seq; [apply Hrun; apply bytes_ok_skipn; exact Hbytes|]. intros status.
eapply mspec_seq with (R := own (buf :: X)).
{ destruct (Z.testbit _ 15); [|apply mspec_ret; intros s mo H; exact H].
eapply mspec_seq; [apply Hcount|]. intros n. apply mspec_ret. intros s mo H; exact H. }
intros status'. eapply mspec_seq; [apply Hdf|]. intros _. apply mspec_ret. intros s mo Ho. exists X. exact Ho.
Qed.

End DriverSpec.
