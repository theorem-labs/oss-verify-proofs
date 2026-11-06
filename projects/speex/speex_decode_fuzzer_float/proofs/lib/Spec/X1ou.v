(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ri X1r0 X1o8 X1o9 X1pe X1os X1ok.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Section DriverL.
Context {St ptr : Type}.
Variable B : Z.
Variable io_diag : diag_msg -> X1qx.M St unit.
Variable drv_malloc : Z -> X1qx.M St (option ptr).
Variable drv_free : ptr -> X1qx.M St unit.
Variable read_stage : Z.
Variable alloc_init : Z -> X1qx.M St unit.
Variable run : Z -> list Z -> X1qx.M St Z.
Variable alloc_count : X1qx.M St Z.

Variable own : list (ptr * Z) -> assn St.

Variable mal_ok : list (ptr * Z) -> Z -> Prop.

Hypothesis Hdm : forall X n, 0 <= n ->
mspecL B (fun s mo => own X s mo /\ mal_ok X n) (drv_malloc n)
(fun r s mo => match r with Some p => own ((p, n) :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p n, mspecL B (own ((p, n) :: X)) (drv_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hdiag : forall X d, mspecL B (own X) (io_diag d) (fun _ => own X).
Hypothesis Hinit : forall X bm, mspecL B (own X) (alloc_init bm) (fun _ => own X).
Hypothesis Hcount : forall X, mspecL B (own X) alloc_count (fun _ => own X).

Hypothesis Hrun : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT -> bytes_ok payload ->
mspecL B (own [(b, cap)]) (run cfg payload) (fun _ => own [(b, cap)]).
Hypothesis Hown_minv : forall X s mo, own X s mo -> minv mo /\ m_halted mo = None.
Hypothesis Hown_vm : forall X s mo mo', own X s mo ->
m_vm mo' = m_vm mo -> minv mo' -> m_halted mo' = None -> own X s mo'.
Hypothesis Hown_live : forall X s mo, own X s mo -> step_live B mo.

Hypothesis OK_first : mal_ok [] 65536.
Hypothesis OK_grow : forall b k, (k <= 9)%nat -> mal_ok [(b, 65536 * 2 ^ Z.of_nat k)] (65536 * 2 ^ Z.of_nat k * 2).

#[using="Hown_minv Hown_vm Hown_live"] Lemma own_after_nodeL : forall X s mo n rsp mo' evs,
own X s mo -> nstep n mo rsp mo' evs -> m_vm mo' = m_vm mo ->
match n with NMmap _ _ _ flags => mmap_noreserve_b (Z_to_bv 64 flags) = false | _ => True end ->
own X s mo' /\ step_live B mo'.
Proof.
intros X s mo n rsp mo' evs Ho Hst Hvm Hfl. destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
destruct (minv_preserved n mo rsp mo' evs Hfl Hmi Hh Hst) as [Hh' Hmi'].
assert (Ho' : own X s mo') by (eapply Hown_vm; eauto). split; [exact Ho'| exact (Hown_live _ _ _ Ho')].
Qed.

Definition rd_invL (st : rd_st) : assn St := fun s mo =>
own [(rd_buf st, rd_cap st)] s mo
/\ zlength (rd_content st) <= rd_cap st
/\ (exists k, (k <= 10)%nat /\ rd_cap st = 65536 * 2 ^ (Z.of_nat k))
/\ bytes_ok (rd_content st).

#[using="mal_ok Hdm Hdf Hperm Hdiag Hown_minv Hown_vm Hown_live OK_grow"] Lemma read_loop_body_L : forall fd path st, 0 <= fd ->
mspecL B (rd_invL st) (read_loop_body io_diag drv_malloc drv_free read_stage fd path st)
(fun r s mo => match r with
| inl st' => rd_invL st' s mo
| inr RdExit => exists X', own X' s mo
| inr (RdDone buf content) => (exists k, (k <= 10)%nat /\ own [(buf, 65536 * 2 ^ Z.of_nat k)] s mo /\ zlength content <= 65536 * 2 ^ Z.of_nat k)
/\ zlength content <= MAX_INPUT /\ bytes_ok content
end).
Proof.
intros fd path st Hfd. unfold read_loop_body.
eapply mspecL_bind with
(Q1 := fun g s mo => match g with
| None => exists X', own X' s mo
| Some st1 => rd_invL st1 s mo /\ rd_content st1 = rd_content st /\ zlength (rd_content st) < rd_cap st1
end).
{ apply mspecL_if_pre.
- apply mspecL_if_pre.
+ eapply mspecL_seq; [eapply mspecL_pre; [apply Hdiag|]|].
{ intros s mo [[[Ho _] _] _]. exact Ho. }
intros _. apply mspecL_ret. intros s mo Ho. exists [(rd_buf st, rd_cap st)]. exact Ho.
+ apply mspecL_pointwise. intros s0 mo0 [[(Ho0 & Hlen & (k & Hk & Hcap) & Hbytes) Heq] Hlt].
apply Z.eqb_eq in Heq. apply Z.leb_gt in Hlt.
pose proof (pow2_le_1024 k Hk) as Hp.
assert (Hk9 : (k <= 9)%nat) by (unfold MAX_INPUT in Hlt; assert (k <> 10)%nat by (intros ->; cbn in Hcap; lia); lia).
eapply mspecL_bind. { eapply mspecL_pre; [apply Hdm; lia|]. intros s mo [-> ->]. split; [exact Ho0|]. rewrite Hcap. apply OK_grow. exact Hk9. }
intros [nb|]; cbn beta iota.
* apply mspecL_pure. intros _. eapply mspecL_seq.
{ eapply mspecL_pre; [apply (Hdf [(nb, rd_cap st * 2)] (rd_buf st) (rd_cap st))|].
intros s mo Ho. eapply Hperm; [apply perm_swap| exact Ho]. }
intros _. apply mspecL_ret. intros s mo Ho. cbn. unfold rd_invL. cbn. splits; auto; try lia.
exists (S k). split; [lia|]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
* eapply mspecL_seq; [apply Hdiag|]. intros _. apply mspecL_ret. intros s mo Ho. exists [(rd_buf st, rd_cap st)]. exact Ho.
- apply mspecL_ret. intros s mo [[Ho [Hlen [Hk Hb]]] Hne]. apply Z.eqb_neq in Hne. split; [|split; [reflexivity|lia]]. split; [exact Ho|]. auto. }
intros [st1|]; cbn beta iota.
2:{ apply mspecL_ret. intros s mo H. exact H. }
apply mspecL_pointwise. intros s1 mo1 ((Ho & Hlen & (k & Hk & Hcap) & Hbytes) & Hct & Hlt).
pose proof (pow2_le_1024 k Hk) as Hp.
set (cnt := if READ_CAP <? rd_cap st1 - zlength (rd_content st) then READ_CAP else rd_cap st1 - zlength (rd_content st)).
assert (Hcnt : 1 <= cnt <= rd_cap st1 - zlength (rd_content st) /\ cnt <= READ_CAP).
{ subst cnt. unfold READ_CAP. destruct (Z.ltb_spec 65536 (rd_cap st1 - zlength (rd_content st))); lia. }
apply mspecL_bind with (Q1 := fun a s mo => s = s1 /\ own [(rd_buf st1, rd_cap st1)] s mo /\
match a with RdErr _ => True | RdData bs => zlength bs <= cnt end).
{ apply mspecL_sys; [intros; apply nroomE_I; exact Logic.I|]. intros s mo [-> ->]. intros rsp mo' evs Hst.
pose proof (nstep_dec_read fd _ cnt mo1 rsp mo' evs ltac:(unfold READ_CAP in *; lia) Hst) as (_ & a & Hdec & Ha).
assert (Hvm : m_vm mo' = m_vm mo1).
{ destruct a as [e|bs]; [destruct Ha as [-> _]; reflexivity|].
destruct Ha as (p & off & data & _ & _ & _ & ->). apply m_vm_with_fds. }
destruct (own_after_nodeL _ _ _ _ _ _ _ Ho Hst Hvm I) as [Ho' LB]. split; [exact LB|].
intros a' Ha'. rewrite Hdec in Ha'. injection Ha' as <-. cbn beta.
split; [reflexivity|]. split; [exact Ho'|].
destruct a as [e|bs]; [exact I|]. destruct Ha as (p & off & data & _ & _ & -> & _).
unfold zlength. pose proof (length_file_read_le_count data off cnt ltac:(unfold READ_CAP in *; lia)). lia. }
intros [e|bs]; cbn beta iota.
- eapply mspecL_seq. { eapply mspecL_pre; [apply Hdiag|]. intros s mo (_ & Ho' & _). exact Ho'. }
intros _. apply mspecL_ret. intros s mo Ho'. exists [(rd_buf st1, rd_cap st1)]. exact Ho'.
- apply mspecL_if; intros C.
+ apply mspecL_ret. intros s mo (-> & Ho' & _). split; [exists k; rewrite <- Hcap; split; [exact Hk|]; split; [exact Ho'|]; rewrite Hct; lia|].
split; [rewrite Hct; unfold MAX_INPUT in *; lia| exact Hbytes].
+ apply mspecL_ret. intros s mo (-> & Ho' & Hbs). apply Nat.eqb_neq in C.
assert (1 <= zlength bs) by (unfold zlength in *; destruct bs; cbn in *; [congruence|lia]).
unfold rd_invL. cbn. split; [exact Ho'|]. rewrite zlength_app', zlength_u8s, Hct. split; [lia|]. split; [exists k; auto|].
unfold bytes_ok in *. rewrite ?Hct in Hbytes. apply Forall_app. split; [exact Hbytes| apply bytes_ok_u8s].
Qed.

#[using="mal_ok Hdm Hdf Hperm Hdiag Hown_minv Hown_vm Hown_live OK_first OK_grow"] Lemma read_all_L : forall path,
mspecL B (own []) (read_all io_diag drv_malloc drv_free read_stage path)
(fun r s mo => match r with
| RdExit => exists X', own X' s mo
| RdDone buf content => (exists k, (k <= 10)%nat /\ own [(buf, 65536 * 2 ^ Z.of_nat k)] s mo /\ zlength content <= 65536 * 2 ^ Z.of_nat k)
/\ zlength content <= MAX_INPUT /\ bytes_ok content
end).
Proof.
intros path. unfold read_all.
apply mspecL_bind with (Q1 := fun r s mo => own [] s mo /\ match r with SVal fd => 0 <= fd | SErr _ => True end).
{ apply mspecL_sys; [intros; apply nroomE_I; exact Logic.I|]. intros s mo Ho. intros rsp mo' evs Hst.
destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
pose proof (nstep_dec_open _ mo rsp mo' evs Hmi Hst) as (_ & a & Hdec & Ha).
assert (Hvm : m_vm mo' = m_vm mo).
{ destruct a as [e|fd]; [destruct Ha as [-> _]; reflexivity|]. destruct Ha as (_ & _ & _ & ent & _ & ->). apply m_vm_with_fds. }
destruct (own_after_nodeL _ _ _ _ _ _ _ Ho Hst Hvm I) as [Ho' LB]. split; [exact LB|].
intros a' Ha'. rewrite Hdec in Ha'. injection Ha' as <-. cbn beta.
split; [exact Ho'|]. destruct a as [e|fd]; [exact I|]. lia. }
intros [e|fd]; cbn beta iota.
- apply mspecL_pure. intros _. eapply mspecL_seq; [apply Hdiag|]. intros _. apply mspecL_ret. intros s mo Ho. exists []. exact Ho.
- apply mspecL_pure. intros Hfd. eapply mspecL_bind; [eapply mspecL_pre; [apply Hdm; lia| intros s mo Ho; split; [exact Ho| exact OK_first]]|]. intros [buf|]; cbn beta iota.
2:{ eapply mspecL_seq; [apply Hdiag|]. intros _. apply mspecL_ret. intros s mo Ho. exists []. exact Ho. }
apply mspecL_pure. intros _.
eapply mspecL_bind.
+ eapply mspecL_pre.
* apply (mspecL_loop B (read_loop_body io_diag drv_malloc drv_free read_stage fd path) rd_invL
(fun r s mo => match r with RdExit => exists X', own X' s mo
| RdDone buf content => (exists k, (k <= 10)%nat /\ own [(buf, 65536 * 2 ^ Z.of_nat k)] s mo /\ zlength content <= 65536 * 2 ^ Z.of_nat k)
/\ zlength content <= MAX_INPUT /\ bytes_ok content end)).
intros st. eapply mspecL_post; [apply read_loop_body_L; exact Hfd|].
intros [st'|[|b c]] s mo H; exact H.
* intros s mo Ho. unfold rd_invL. cbn. split; [exact Ho|]. split; [unfold zlength; cbn; lia|]. split; [exists 0%nat; split; [lia|reflexivity]|].
constructor.
+ intros [|buf' content]; cbn beta iota; [apply mspecL_ret; intros s mo H; exact H|].
apply mspecL_pointwise. intros s1 mo1 [(k & Hk & Ho1 & Hck) Hlen].
eapply mspecL_bind with (Q1 := fun _ s mo => own [(buf', 65536 * 2 ^ Z.of_nat k)] s mo).
* apply mspecL_sys; [intros; apply nroomE_I; exact Logic.I|]. intros s mo [-> ->]. intros rsp mo' evs Hst.
pose proof (nstep_dec_close fd mo1 rsp mo' evs Hst) as (_ & a & Hdec & Ha).
assert (Hvm : m_vm mo' = m_vm mo1).
{ destruct a as [e|v]; [destruct Ha as (_ & -> & _); reflexivity|]. destruct Ha as (_ & _ & ->). apply m_vm_with_fds. }
destruct (own_after_nodeL _ _ _ _ _ _ _ Ho1 Hst Hvm I) as [Ho' LB]. split; [exact LB|]. intros; exact Ho'.
* intros _. apply mspecL_ret. intros s mo Ho. split; [| exact Hlen]. exists k. auto.
Qed.

#[using="mal_ok Hdm Hdf Hperm Hdiag Hinit Hcount Hrun Hown_minv Hown_vm Hown_live OK_first OK_grow"] Lemma main_model_L : forall argv,
mspecL B (own []) (main_model io_diag drv_malloc drv_free read_stage alloc_init run alloc_count argv)
(fun _ s mo => exists X', own X' s mo).
Proof.
intros argv. unfold main_model.
apply mspecL_if; intros _.
{ eapply mspecL_seq; [apply Hdiag|]. intros _. apply mspecL_ret. intros s mo Ho. exists []; exact Ho. }
eapply mspecL_bind; [apply read_all_L|].
intros [|buf content]; cbn beta iota; [apply mspecL_ret; intros s mo H; exact H|].
apply mspecL_pure. intros [Hlen Hbytes]. apply mspecL_exI. intros k. apply mspecL_pure_l. intros Hk.
apply (mspecL_pre B _ (fun s mo => own [(buf, 65536 * 2 ^ Z.of_nat k)] s mo /\ zlength content <= 65536 * 2 ^ Z.of_nat k)); [| intros s mo H; exact H].
apply mspecL_pointwise. intros s0 mo0 [Ho0 Hck]. apply (mspecL_pre B _ (own [(buf, 65536 * 2 ^ Z.of_nat k)])); [| intros s mo [-> ->]; exact Ho0].
pose proof (pow2_le_1024 k Hk) as Hp.
apply mspecL_if; intros _.
{ eapply mspecL_seq; [apply Hdiag|]. intros _. eapply mspecL_seq; [apply Hdf|]. intros _. apply mspecL_ret. intros s mo Ho; exists []; exact Ho. }
apply mspecL_if; intros _.
{ eapply mspecL_seq; [apply Hdiag|]. intros _. eapply mspecL_seq; [apply Hdf|]. intros _. apply mspecL_ret. intros s mo Ho; exists []; exact Ho. }
eapply mspecL_seq; [apply Hinit|]. intros _.
assert (Hcap : 65536 <= 65536 * 2 ^ Z.of_nat k <= MAX_INPUT) by (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)); unfold MAX_INPUT; lia).
eapply mspecL_seq; [apply Hrun; [exact Hcap| etransitivity; [| exact Hlen]; unfold zlength; rewrite length_skipn; lia| apply bytes_ok_skipn; exact Hbytes]|]. intros status.
eapply mspecL_seq with (R := own [(buf, 65536 * 2 ^ Z.of_nat k)]).
{ destruct (Z.testbit _ 15); [|apply mspecL_ret; intros s mo H; exact H].
eapply mspecL_seq; [apply Hcount|]. intros n. apply mspecL_ret. intros s mo H; exact H. }
intros status'. eapply mspecL_seq; [apply Hdf|]. intros _. apply mspecL_ret. intros s mo Ho. exists []. exact Ho.
Qed.
End DriverL.
