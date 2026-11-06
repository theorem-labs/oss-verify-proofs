(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode Image.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad MSafe MSafeP STree Malloc Stdio PState Harness Adapter Driver Prog KInv KLink KEv KEvP TargetSafe.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Section DriverSpec.
Context {St ptr : Type}.
Variable io : IOStyle St.
Variable drv_malloc : Z -> Monad.M St (option ptr).
Variable drv_free : ptr -> Monad.M St unit.
Variable read_stage : Z.
Variable alloc_init : Z -> Monad.M St unit.
Variable run : Z -> list Z -> Monad.M St Z.
Variable alloc_count : Monad.M St Z.
Variable own : list ptr -> assn St.
Definition ARG_MAX_LEN : Z := 131071.
Definition diag_ok (d : diag_msg) : Prop :=
match d with
| DUsage a | DCannotOpen a | DReadError a => zlength a <= ARG_MAX_LEN
| _ => True
end.
Hypothesis Hdm : forall X n, 0 <= n ->
mspec (own X) (drv_malloc n) (fun r s mo => match r with Some p => own (p :: X) s mo /\ n < 2^63 | None => own X s mo end).
Hypothesis Hdf : forall X p, mspec (own (p :: X)) (drv_free p) (fun _ => own X).
Hypothesis Hperm : forall X Y s mo, Permutation X Y -> own X s mo -> own Y s mo.
Hypothesis Hdiag : forall X d, diag_ok d -> mspec (own X) (io_diag io d) (fun _ => own X).
Hypothesis Hexit : forall X, mspec (own X) (io_exit io) (fun _ => own X).
Hypothesis Hinit : forall X bm, mspec (own X) (alloc_init bm) (fun _ => own X).
Hypothesis Hcount : forall X, mspec (own X) alloc_count (fun _ => own X).
Hypothesis Hrun : forall X cfg payload, zlength payload <= MAX_INPUT -> mspecP (own X) (run cfg payload) (fun _ => own X).
Hypothesis Hown_minv : forall X s mo, own X s mo -> minv mo /\ m_halted mo = None.
Hypothesis Hown_fds : forall X s mo mo', own X s mo ->
m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> own X s mo'.
#[using="Hown_minv Hown_fds"] Lemma own_after_node : forall X s mo n rsp mo' evs,
own X s mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> own X s mo'.
Proof.
intros X s mo n rsp mo' evs Ho Hst Hvm. destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hst) as [Hh' Hmi']. eapply Hown_fds; eauto.
Qed.
Definition rd_inv (X : list ptr) (st : rd_st) : assn St := fun s mo =>
own (rd_buf st :: X) s mo
/\ zlength (rd_content st) <= rd_cap st
/\ (exists k, (k <= 10)%nat /\ rd_cap st = 65536 * 2 ^ (Z.of_nat k)).
Definition rd_meas (st : @rd_st ptr) : nat := Z.to_nat (MAX_INPUT + 1 - zlength (rd_content st)).
#[using="Type"] Lemma zlength_app {A} (l1 l2 : list A) : zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. unfold zlength. rewrite length_app. Local Ltac2 Set LiaHints.tbl := fun () => "0010>62102050378.23000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma zlength_u8s : forall bs, zlength (u8s_of_bytes bs) = zlength bs.
Proof. intros. unfold u8s_of_bytes, zlength. rewrite length_map. reflexivity. Qed.
#[using="Type"] Lemma pow2_le_1024 : forall k, (k <= 10)%nat -> 2 ^ Z.of_nat k <= 1024.
Proof.
intros k Hk. change 1024 with (2 ^ 10). apply Z.pow_le_mono_r; lia.
Qed.
#[using="Hdm Hdf Hperm Hdiag Hown_minv Hown_fds"] Lemma read_loop_body_spec : forall X fd path st,
zlength path <= ARG_MAX_LEN -> 0 <= fd ->
mspec (rd_inv X st) (read_loop_body io drv_malloc drv_free read_stage fd path st)
(fun r s mo => match r with
| inl st' => rd_inv X st' s mo /\ (rd_meas st' < rd_meas st)%nat
| inr RdExit => exists X', own X' s mo
| inr (RdDone buf content) => own (buf :: X) s mo /\ zlength content <= MAX_INPUT
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
+ apply mspec_pointwise. intros s0 mo0 [[(Ho0 & Hlen & k & Hk & Hcap) Heq] Hlt].
apply Z.eqb_eq in Heq. apply Z.leb_gt in Hlt.
pose proof (pow2_le_1024 k Hk) as Hp.
eapply mspec_bind. { Local Ltac2 Set LiaHints.tbl := fun () => "00A0>14527508098.411554928023.46 17979118143.4422285582869.3830660695437.4035139066338.3842754480356.5044498954964.3648246744460.3249158301540.4049959518760.4654540294333.4056081126708.4659308587026.396156627085.49 6156627222.44 8208523370.40 00000600D00T00^00k01101701@01J01N01V01_02102A02K02U02VS2Hk1HS2Hk5Hwant3HbsS2Hk4Hcap3Hlt2HpS2Hk3Hlt1HS2Hk4Hcap3HeqS2Hk1HS2Hk1HS2Hk4HcapS4Hlen3HneS2HkS2Hk3HbsS2Hk4HcapS2Hk4Hcap3Hlt2Hp1HS4Hcap2Hk3Hlt2HpS2Hk5HwantS2Hk5HwantF".
eapply mspec_pre; [apply Hdm; lia|]. intros s mo [-> ->]. exact Ho0. }
intros [nb|]; cbn beta iota.
* apply mspec_pure. intros _. eapply mspec_seq.
{ eapply mspec_pre; [apply (Hdf (nb :: X) (rd_buf st))|].
intros s mo Ho. eapply Hperm; [apply perm_swap| exact Ho]. }
intros _. apply mspec_ret. intros s mo Ho. cbn. unfold rd_inv. cbn. splits; auto; try lia.
exists (S k). split; [unfold MAX_INPUT in Hlt; assert (k <> 10)%nat by (intros ->; cbn in Hcap; lia); lia|].
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
* eapply mspec_seq; [apply Hdiag; exact I|]. intros _. apply mspec_ret. intros s mo Ho. exists (rd_buf st :: X). exact Ho.
- apply mspec_ret. intros s mo [[Ho [Hlen Hk]] Hne]. apply Z.eqb_neq in Hne. split; [|split; [reflexivity|lia]]. split; [exact Ho|]. auto. }
intros [st1|]; cbn beta iota.
2:{ apply mspec_ret. intros s mo H. exact H. }
apply mspec_pointwise. intros s1 mo1 ((Ho & Hlen & k & Hk & Hcap) & Hct & Hlt).
pose proof (pow2_le_1024 k Hk) as Hp.
set (want0 := rd_cap st1 - zlength (rd_content st)).
set (want := if 65536 <? want0 then 65536 else want0).
assert (Hwant : 0 < want <= want0 /\ want <= 65536).
{ subst want want0. destruct (Z.ltb_spec 65536 (rd_cap st1 - zlength (rd_content st))); lia. }
apply mspec_bind with (Q1 := fun a s mo => s = s1 /\ own (rd_buf st1 :: X) s mo /\
match a with RdErr _ => True | RdData bs => zlength bs <= want end).
{ apply mspec_sys. intros s mo [-> ->]. split; [exact I|].
intros rsp mo' evs Hst.
pose proof (nstep_dec_read fd _ want mo1 rsp mo' evs ltac:(unfold MAX_INPUT, zlength in *; lia) Hst) as (_ & a & Hdec & Ha).
exists a. split; [exact Hdec|].
cbn beta. split; [reflexivity|].
assert (Hvm : m_vmmaps mo' = m_vmmaps mo1).
{ destruct a as [e|bs]; [destruct Ha as [-> _]; reflexivity|].
destruct Ha as (p & off & data & _ & _ & _ & ->). reflexivity. }
split; [eapply own_after_node; eauto|].
destruct a as [e|bs]; [exact I|]. destruct Ha as (p & off & data & _ & _ & -> & _).
unfold zlength. pose proof (length_file_read_le_count data off want ltac:(unfold zlength, MAX_INPUT in *; lia)). lia. }
intros [e|bs]; cbn beta iota.
- eapply mspec_seq. { eapply mspec_pre; [apply Hdiag; exact Hpath|]. intros s mo (_ & Ho' & _). exact Ho'. }
intros _. apply mspec_ret. intros s mo Ho'. exists (rd_buf st1 :: X). exact Ho'.
- apply mspec_if; intros C.
+ apply mspec_ret. intros s mo (-> & Ho' & _). split; [exact Ho'|]. rewrite Hct. unfold MAX_INPUT in *. lia.
+ apply mspec_ret. intros s mo (-> & Ho' & Hbs). apply Nat.eqb_neq in C.
assert (1 <= zlength bs) by (unfold zlength in *; destruct bs; cbn in *; [congruence|lia]).
split.
* unfold rd_inv. cbn. split; [exact Ho'|]. rewrite zlength_app, zlength_u8s, Hct. split; [lia|]. exists k. auto.
* unfold rd_meas. cbn. rewrite zlength_app, zlength_u8s, Hct. unfold MAX_INPUT in *. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma m_vmmaps_with_fds : forall f mo, m_vmmaps (with_fds f mo) = m_vmmaps mo.
Proof. reflexivity. Qed.
#[using="Hdm Hdf Hperm Hdiag Hown_minv Hown_fds"] Lemma read_all_spec : forall X path, zlength path <= ARG_MAX_LEN ->
mspec (own X) (read_all io drv_malloc drv_free read_stage path)
(fun r s mo => match r with
| RdExit => exists X', own X' s mo
| RdDone buf content => own (buf :: X) s mo /\ zlength content <= MAX_INPUT
end).
Proof.
intros X path Hpath. unfold read_all.
apply mspec_bind with (Q1 := fun r s mo => own X s mo /\ match r with SVal fd => 0 <= fd | SErr _ => True end).
{ apply mspec_sys. intros s mo Ho. split; [exact I|]. intros rsp mo' evs Hst.
destruct (Hown_minv _ _ _ Ho) as [Hmi Hh].
pose proof (nstep_dec_open _ mo rsp mo' evs Hmi Hst) as (_ & a & Hdec & Ha).
exists a. split; [exact Hdec|]. cbn beta.
assert (Hvm : m_vmmaps mo' = m_vmmaps mo).
{ destruct a as [e|fd]; [destruct Ha as [-> _]; reflexivity|]. destruct Ha as (_ & _ & _ & ent & _ & ->). reflexivity. }
split; [eapply own_after_node; eauto|]. destruct a as [e|fd]; [exact I|]. Local Ltac2 Set LiaHints.tbl := fun () => "0050>1542078869.29 18926758138.2543365953645.2950411798476.2651752059261.36000001002003004008SSSSS2Ha".
lia. }
intros [e|fd]; cbn beta iota.
- apply mspec_pure. intros _. eapply mspec_seq; [apply Hdiag; exact Hpath|]. intros _. apply mspec_ret. intros s mo Ho. exists X. exact Ho.
- apply mspec_pure. intros Hfd. eapply mspec_bind; [apply Hdm; lia|]. intros [buf|]; cbn beta iota.
2:{ eapply mspec_seq; [apply Hdiag; exact I|]. intros _. apply mspec_ret. intros s mo Ho. exists X. exact Ho. }
apply mspec_pure. intros _.
eapply mspec_bind.
+ eapply mspec_pre.
* apply (mspec_loop (read_loop_body io drv_malloc drv_free read_stage fd path) (rd_inv X)
(fun r s mo => match r with RdExit => exists X', own X' s mo
| RdDone buf content => own (buf :: X) s mo /\ zlength content <= MAX_INPUT end)
rd_meas).
{ intros st. eapply mspec_post; [apply read_loop_body_spec; [exact Hpath| exact Hfd]|].
intros [st'|[|b c]] s mo H; exact H. }
unfold rd_meas, READ_FUEL. cbn [rd_content]. unfold zlength. cbn [length Z.of_nat]. unfold MAX_INPUT. lia.
* intros s mo Ho. unfold rd_inv. cbn. split; [exact Ho|]. split; [unfold zlength; cbn; lia|]. exists 0%nat. split; [lia|reflexivity].
+ intros [|buf' content]; cbn beta iota; [apply mspec_ret; intros s mo H; exact H|].
apply mspec_pointwise. intros s1 mo1 [Ho1 Hlen].
eapply mspec_bind with (Q1 := fun _ s mo => own (buf' :: X) s mo).
* apply mspec_sys. intros s mo [-> ->]. split; [exact I|]. intros rsp mo' evs Hst.
pose proof (nstep_dec_close fd mo1 rsp mo' evs Hst) as (_ & a & Hdec & Ha).
exists a. split; [exact Hdec|]. cbn beta.
assert (Hvm : m_vmmaps mo' = m_vmmaps mo1).
{ destruct a as [e|v]; [destruct Ha as (_ & -> & _); reflexivity|]. destruct Ha as (_ & _ & ->). reflexivity. }
eapply own_after_node; eauto.
* intros _. apply mspec_ret. intros s mo Ho. split; [exact Ho| exact Hlen].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma zlength_skipn_le : forall {A} n (l : list A), zlength (skipn n l) <= zlength l.
Proof. intros. unfold zlength. rewrite length_skipn. Local Ltac2 Set LiaHints.tbl := fun () => "0010>61799526425.23000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Hdm Hdf Hperm Hdiag Hinit Hcount Hrun Hown_minv Hown_fds"] Lemma main_model_spec : forall X argv,
Forall (fun a => zlength a <= ARG_MAX_LEN) argv ->
mspecP (own X) (main_model io drv_malloc drv_free read_stage alloc_init run alloc_count argv)
(fun _ s mo => exists X', own X' s mo).
Proof.
intros X argv Hargv. unfold main_model.
assert (Hnth : forall i, zlength (nth i argv []) <= ARG_MAX_LEN).
{ intros i. Local Ltac2 Set LiaHints.tbl := fun () => "0020>27190893083.2843645105351.24000008009S4Hlen1HS".
destruct (nth_in_or_default i argv []) as [Hin| ->]; [|unfold zlength, ARG_MAX_LEN; cbn; lia].
exact (proj1 (Forall_forall _ _) Hargv _ Hin). }
apply mspecP_if; intros _.
{ apply mspec_mspecP. eapply mspec_seq; [apply Hdiag; cbn; apply Hnth|]. intros _. apply mspec_ret. intros s mo Ho. exists X; exact Ho. }
eapply mspecP_bind; [apply mspec_mspecP; apply read_all_spec; apply Hnth|].
intros [|buf content]; cbn beta iota; [apply mspecP_ret; intros s mo H; exact H|].
apply mspecP_pure. intros Hlen.
apply mspecP_if; intros _.
{ apply mspec_mspecP. eapply mspec_seq; [apply Hdiag; exact I|]. intros _. eapply mspec_seq; [apply Hdf|]. intros _. apply mspec_ret. intros s mo Ho; exists X; exact Ho. }
apply mspecP_if; intros _.
{ apply mspec_mspecP. eapply mspec_seq; [apply Hdiag; exact I|]. intros _. eapply mspec_seq; [apply Hdf|]. intros _. apply mspec_ret. intros s mo Ho; exists X; exact Ho. }
eapply mspecP_seq; [apply mspec_mspecP; apply Hinit|]. intros _.
eapply mspecP_seq; [apply Hrun; pose proof (zlength_skipn_le (Z.to_nat (6 + Z.land (le16 content) 0x7fff)) content); lia|]. intros status.
eapply mspecP_seq with (R := own (buf :: X)).
{ destruct (Z.testbit _ 15); [|apply mspecP_ret; intros s mo H; exact H].
eapply mspecP_seq; [apply mspec_mspecP; apply Hcount|]. intros n. apply mspecP_ret. intros s mo H; exact H. }
intros status'. eapply mspecP_seq; [apply mspec_mspecP; apply Hdf|]. intros _. apply mspecP_ret. intros s mo Ho. exists X. exact Ho.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Hexit"] Lemma exit_model_spec : forall code,
mspecP (fun s mo => exists X, own X s mo) (exit_model io code) (fun _ _ _ => False).
Proof.
intros code. unfold exit_model. eapply mspecP_seq with (R := fun s mo => exists X, own X s mo).
- apply mspecP_exI. intros X. eapply mspecP_post; [apply mspec_mspecP; apply Hexit|]. intros a s mo Ho. exists X. exact Ho.
- intros _. apply mspecP_sys. intros s mo _. split; [exact I|]. intros rsp mo' evs Hst. destruct (nstep_exit_none _ _ _ _ _ Hst).
Qed.
End DriverSpec.
Definition so_ok (so : stdout_st) : Prop := zlength (so_buf so) <= STDOUT_BUFSIZ.
Definition Gso : PState -> Model -> Prop := fun s _ => so_ok (ps_so s).
Lemma frame_ok_Gso : frame_ok Gso.
Proof. intros s s' mo mo' _ Hso _ H. unfold Gso in *. rewrite Hso. exact H. Qed.
Definition GI (X : list bptr) : assn PState := OWN X Gso.
Lemma KL_fds : forall L pbrk mo mo',
KL L pbrk mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> KL L pbrk mo'.
Proof.
intros L pbrk mo mo' K Hvm Hmi Hh. destruct K. constructor; try (rewrite Hvm); auto.
Qed.
Lemma GI_minv : forall X s mo, GI X s mo -> minv mo /\ m_halted mo = None.
Proof. intros X s mo [(L & _ & K & _) _]. split; [exact (kl_minv _ _ _ K)| exact (kl_halt _ _ _ K)]. Qed.
Lemma GI_fds : forall X s mo mo', GI X s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> GI X s mo'.
Proof.
intros X s mo mo' [(L & Hc & K & Hi) [Hnd HG]] Hvm Hmi Hh. split; [|split; [exact Hnd| exact HG]].
exists L. split; [exact Hc|]. split; [eapply KL_fds; eauto| exact Hi].
Qed.
Lemma GI_perm : forall X Y s mo, Permutation X Y -> GI X s mo -> GI Y s mo.
Proof. intros. eapply OWN_perm; eauto. Qed.
Lemma GI_after_node : forall X s mo n rsp mo' evs,
GI X s mo -> nstep n mo rsp mo' evs -> m_vmmaps mo' = m_vmmaps mo -> GI X s mo'.
Proof.
intros X s mo n rsp mo' evs Ho Hst Hvm. destruct (GI_minv _ _ _ Ho) as [Hmi Hh].
destruct (minv_preserved n mo rsp mo' evs Hmi Hh Hst) as [Hh' Hmi']. eapply GI_fds; eauto.
Qed.
Lemma GI_set_so : forall X s mo v, GI X s mo -> so_ok v -> GI X (set_so_ps v s) mo.
Proof. intros X s mo v H Hv. eapply OWN_other; [exact H|reflexivity|reflexivity| exact Hv]. Qed.
Lemma raw_malloc_GI : forall X n, 0 <= n ->
mspec (GI X) (raw_malloc n) (fun r s mo => match r with Some p => GI (p :: X) s mo /\ n < 2^63 | None => GI X s mo end).
Proof. intros. apply raw_malloc_spec; [apply frame_ok_Gso| assumption]. Qed.
Lemma raw_free_GI : forall X p, mspec (GI (p :: X)) (raw_free p) (fun _ => GI X).
Proof. intros. apply raw_free_spec. apply frame_ok_Gso. Qed.
Lemma raw_malloc_GIP : forall X n, 0 <= n <= OPNEW_MAX ->
mspecP (GI X) (raw_malloc n) (fun r s mo => match r with Some p => GI (p :: X) s mo /\ n < 2^63 | None => False end).
Proof.
intros X n Hn. Local Ltac2 Set LiaHints.tbl := fun () => "0020=18539273086.32424960062.3 000004008S2HnS2Hn".
apply raw_malloc_specP; [apply frame_ok_Gso| lia|]. unfold size_overflows, OPNEW_MAX in *. apply Z.leb_gt. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma alloc_init_GI : forall X bm, mspec (GI X) (alloc_init bm) (fun _ => GI X).
Proof. intros X bm. unfold alloc_init, Adapter.target_alloc_init. apply mspec_ret. intros s mo H; exact H. Qed.
Lemma alloc_count_GI : forall X, mspec (GI X) alloc_count (fun _ => GI X).
Proof. intros X. unfold alloc_count, Adapter.target_alloc_count. apply mspec_ret. intros s mo H; exact H. Qed.
Lemma startup_GI : forall X, mspec (GI X) startup (fun _ => GI X).
Proof.
intros X. unfold startup. eapply mspec_seq; [|intros _; apply mspec_ret; intros s mo H; exact H].
apply mspec_sys. intros s mo Ho. split; [exact I|]. intros rsp mo' evs Hst.
destruct (GI_minv _ _ _ Ho) as [Hmi Hh].
pose proof (nstep_dec_set_tid mo rsp mo' evs Hmi Hst) as (_ & t & Hdec & _ & Hmo).
exists t. split; [exact Hdec|]. eapply GI_after_node; [exact Ho| exact Hst|].
destruct Hmo as [[_ ->]|[_ ->]]; reflexivity.
Qed.
Lemma length_to_bytes : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.
Lemma length_concat_to_bytes : forall iov, length (concat (map to_bytes iov)) = length (concat iov).
Proof. induction iov as [|a iov IH]; cbn; [reflexivity|]. rewrite !length_app, length_to_bytes, IH. reflexivity. Qed.
Lemma iov_total_eq : forall iov, iov_total iov = Z.of_nat (length (concat iov)).
Proof. intros. reflexivity. Qed.
Lemma iov_advance_shrinks : forall iov cnt, 1 <= cnt -> (0 < length (concat iov))%nat ->
(length (concat (iov_advance iov cnt)) < length (concat iov))%nat.
Proof.
intros iov cnt Hc Hpos. Local Ltac2 Set LiaHints.tbl := fun () => "0060=15043033658.425381605119.427163660449.536478074771.942830613005.88910365851.8 00000800A00I00T00_00jS4Hpos1HS2Hc4HposS4Hpos1HS4Hpos1H2H1S4Hpos1H2H0S4Hpos1H2H0".
assert (1 <= Z.to_nat cnt)%nat by lia.
destruct iov as [|a [|b rest]]; cbn in *.
- lia.
- rewrite !app_nil_r in *. rewrite length_skipn. lia.
- rewrite !length_app in Hpos. destruct (Z.ltb_spec (zlength a) cnt); cbn; rewrite ?app_nil_r, ?length_app, ?length_skipn; unfold zlength in *.
+ assert (1 <= Z.to_nat (cnt - Z.of_nat (length a)))%nat by lia. lia.
+ lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma stdio_write_loop_GI : forall X fd fuel iov,
(length (concat iov) < fuel)%nat -> Z.of_nat (length (concat iov)) < 2^63 ->
mspec (GI X) (stdio_write_loop fuel fd iov) (fun _ => GI X).
Proof.
intros X fd fuel. Local Ltac2 Set LiaHints.tbl := fun () => "0060>1382157256.5  34124135552.1635425576734.1640552417260.1447099233985.1347099233985.1400000400@00I00P00V00cS2HfS2Hf2Hb2H21HS2Hf2H21HS2Hf2HbS2Hf1HS2Hf1H2H03Hne".
induction fuel as [|fuel IH]; intros iov Hf Hb; [lia|].
cbn [stdio_write_loop].
eapply mspec_bind with (Q1 := fun cnt s mo => GI X s mo /\
((length (concat iov) = 0%nat /\ cnt = 0) \/ 1 <= cnt <= Z.of_nat (length (concat iov)))).
- apply mspec_sys. intros s mo Ho. split; [exact I|]. intros rsp mo' evs Hst.
pose proof (nstep_dec_writev fd (map to_bytes iov) mo rsp mo' evs ltac:(rewrite length_concat_to_bytes; lia) Hst) as (k & Hdec & Hk & -> & _).
rewrite length_concat_to_bytes in Hdec, Hk. exists k. rewrite iov_total_eq. split; [exact Hdec|]. split; [exact Ho| exact Hk].
- intros cnt. apply mspec_if_pre.
+ apply mspec_ret. intros s mo [[H _] _]. exact H.
+ apply mspec_pointwise. intros s0 mo0 [[Ho Hk] Hne]. rewrite iov_total_eq in Hne. apply Z.eqb_neq in Hne.
assert (1 <= cnt /\ (0 < length (concat iov))%nat) as [H1 H2] by (destruct Hk as [[? ?]|?]; lia).
pose proof (iov_advance_shrinks iov cnt H1 H2).
eapply mspec_pre; [apply IH; lia|]. intros s mo [-> ->]. exact Ho.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma stdio_write_GI : forall X fd buf s, zlength buf + zlength s <= WRITE_MAX ->
mspec (GI X) (stdio_write fd buf s) (fun _ => GI X).
Proof.
intros X fd buf s Hlen. unfold stdio_write.
Local Ltac2 Set LiaHints.tbl := fun () => "0050=13539967204.716559811398.622472561617.732809512824.558286826718.700000300;00C00D00ES1ES4Hlen1HS4Hlen1ESS".
destruct (Z.ltb_spec WRITE_MAX (zlength buf + zlength s)); [lia|].
assert (E : length (concat (match buf with [] => [s] | _ :: _ => [buf; s] end)) = (length buf + length s)%nat).
{ destruct buf; cbn; rewrite ?app_nil_r, ?length_app; cbn; lia. }
apply stdio_write_loop_GI; rewrite E; unfold zlength, WRITE_MAX in *; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma upd_so_GI : forall X f,
mspec (fun s mo => GI X s mo /\ so_ok (f (ps_so s))) (upd_so ps_so set_so_ps f)
(fun _ s mo => GI X s mo /\ exists so0, ps_so s = f so0).
Proof.
intros X f. unfold upd_so. apply mspec_upd'. intros s mo [Ho Hok]. split; [apply GI_set_so; [exact Ho| exact Hok]|]. cbn. eauto.
Qed.
Lemma rd_so_GI : forall (X : list bptr) (P : assn PState), mspec P (rd_so ps_so) (fun so s mo => P s mo /\ so = ps_so s).
Proof.
intros X P. unfold rd_so. eapply mspec_bind; [apply mspec_get|]. intros s0. apply mspec_ret.
intros s mo [-> Ho]. split; [exact Ho| reflexivity].
Qed.
Lemma GI_so_ok : forall X s mo, GI X s mo -> so_ok (ps_so s).
Proof. intros X s mo H. exact (OWN_G _ _ _ _ H). Qed.
Definition PIECE_MAX : Z := 1048576.
Lemma stdout_stdio_write_GI : forall X s, zlength s <= PIECE_MAX ->
mspec (GI X) (stdout_stdio_write ps_so set_so_ps s) (fun _ s mo => GI X s mo /\ so_buf (ps_so s) = []).
Proof.
intros X s Hs. unfold stdout_stdio_write. eapply mspec_bind; [apply (rd_so_GI X)|]. intros so.
apply mspec_pointwise. intros s1 mo1 [Ho ->]. pose proof (GI_so_ok _ _ _ Ho) as Hok. unfold so_ok, STDOUT_BUFSIZ in Hok.
eapply mspec_seq. { Local Ltac2 Set LiaHints.tbl := fun () => "0020>43368050741.107373824191.7  000001009SS2Hs3Hok".
eapply mspec_pre; [apply stdio_write_GI; unfold PIECE_MAX, WRITE_MAX in *; lia|]. intros s' mo' [-> ->]; exact Ho. }
intros _. eapply mspec_conseq; [apply upd_so_GI| |].
- intros s' mo' Ho'. split; [exact Ho'|]. unfold so_ok, zlength, STDOUT_BUFSIZ; cbn; lia.
- intros [] s' mo' [Ho' [so0 ->]]. split; [exact Ho'| reflexivity].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma stdout_writefn_GI : forall X s, zlength s <= PIECE_MAX ->
mspec (GI X) (stdout_writefn ps_so set_so_ps s) (fun _ s mo => GI X s mo /\ so_buf (ps_so s) = []).
Proof.
intros X s Hs. unfold stdout_writefn. eapply mspec_bind; [apply (rd_so_GI X)|]. intros so.
apply mspec_pointwise. intros s1 mo1 [Ho ->].
eapply mspec_seq with (R := GI X).
- destruct (so_first (ps_so s1)).
+ eapply mspec_seq.
{ eapply mspec_conseq; [apply upd_so_GI| |]; [intros s' mo' [-> ->]; split; [exact Ho| exact (GI_so_ok _ _ _ Ho)]| intros [] s' mo' [H _]; exact H]. }
intros _. eapply mspec_bind with (Q1 := fun r s mo => GI X s mo /\ match r with SErr _ => True | SVal _ => False end).
* apply mspec_sys. intros s' mo' Ho'. split; [exact I|]. intros rsp mo'' evs Hst.
pose proof (nstep_dec_ioctl 1 TIOCGWINSZ mo' rsp mo'' evs Hst) as (Hdec & -> & _).
eexists. split; [exact Hdec|]. split; [exact Ho'| exact I].
* intros [e|v]; [| intros s' mo' [_ []]].
eapply mspec_conseq; [apply upd_so_GI| |]; [intros s' mo' [H _]; split; [exact H| exact (GI_so_ok _ _ _ H)]| intros [] s' mo' [H _]; exact H].
+ apply mspec_ret. intros s' mo' [-> ->]; exact Ho.
- intros _. apply stdout_stdio_write_GI. exact Hs.
Qed.
Lemma zlength_firstn_le' : forall {A} n (l : list A), zlength (firstn n l) <= zlength l.
Proof. intros. unfold zlength. rewrite firstn_length. Local Ltac2 Set LiaHints.tbl := fun () => "0010=13684951543.3000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma stdout_towrite_GI : forall X, mspec (GI X) (stdout_towrite ps_so set_so_ps) (fun _ => GI X).
Proof.
intros X. unfold stdout_towrite. eapply mspec_conseq; [apply upd_so_GI| |].
- intros s mo Ho. split; [exact Ho|]. pose proof (GI_so_ok _ _ _ Ho) as Hok. destruct (so_active (ps_so s)); [exact Hok|].
Local Ltac2 Set LiaHints.tbl := fun () => "0010=43368050801.5000001S".
unfold so_ok, zlength, STDOUT_BUFSIZ; cbn; lia.
- intros [] s mo [H _]; exact H.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma stdout_fwritex_GI : forall X s, zlength s <= PIECE_MAX ->
mspec (GI X) (stdout_fwritex ps_so set_so_ps s) (fun _ => GI X).
Proof.
intros X s Hs. unfold stdout_fwritex.
eapply mspec_seq; [apply stdout_towrite_GI|]. intros _.
eapply mspec_bind; [apply (rd_so_GI X)|]. intros so.
apply mspec_pointwise. intros s1 mo1 [Ho ->]. pose proof (GI_so_ok _ _ _ Ho) as Hok. unfold so_ok, STDOUT_BUFSIZ in Hok.
apply mspec_if; intros C1.
{ eapply mspec_conseq; [apply stdout_writefn_GI; exact Hs| intros s' mo' [-> ->]; exact Ho| intros [] s' mo' [H _]; exact H]. }
apply Z.ltb_ge in C1.
destruct (so_lbf_nl (ps_so s1)).
- set (i := after_last_nl s).
eapply mspec_seq with (R := fun s' mo => GI X s' mo /\ zlength (so_buf (ps_so s')) + zlength (skipn (Z.to_nat i) s) <= STDOUT_BUFSIZ).
+ destruct (0 <? i).
* Local Ltac2 Set LiaHints.tbl := fun () => "0040>3209770873.10 33053680748.1041303976697.147375765985.8  00000600<00C00GS2C11HS2Hs1HS2C12H0S2C1".
eapply mspec_conseq; [apply stdout_writefn_GI; pose proof (zlength_firstn_le' (Z.to_nat i) s); lia| intros s' mo' [-> ->]; exact Ho|].
intros [] s' mo' [H Hb]. split; [exact H|]. rewrite Hb. pose proof (zlength_skipn_le (Z.to_nat i) s). unfold zlength, STDOUT_BUFSIZ in *; cbn; lia.
* apply mspec_ret. intros s' mo' [-> ->]. split; [exact Ho|]. pose proof (zlength_skipn_le (Z.to_nat i) s). unfold STDOUT_BUFSIZ in *; lia.
+ intros _. eapply mspec_conseq; [apply upd_so_GI| |]; [| intros [] s' mo' [H _]; exact H].
intros s' mo' [H Hb]. split; [exact H|]. unfold so_ok. cbn. rewrite zlength_app. exact Hb.
- eapply mspec_conseq; [apply upd_so_GI| |]; [| intros [] s' mo' [H _]; exact H].
intros s' mo' [-> ->]. split; [exact Ho|]. unfold so_ok. cbn. rewrite zlength_app. unfold STDOUT_BUFSIZ in *; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma out_pieces_GI : forall X ps, Forall (fun p => zlength p <= PIECE_MAX) ps ->
mspec (GI X) (out_pieces ps_so set_so_ps ps) (fun _ => GI X).
Proof.
intros X ps Hps. induction Hps as [|p ps Hp Hps IH]; cbn [out_pieces].
- apply mspec_ret. intros s mo H; exact H.
- eapply mspec_seq; [apply stdout_fwritex_GI; exact Hp|]. intros _. exact IH.
Qed.
Lemma stdout_vprintf_GI : forall X ps, Forall (fun p => zlength p <= PIECE_MAX) ps ->
mspec (GI X) (stdout_vprintf ps_so set_so_ps ps) (fun _ => GI X).
Proof.
intros X ps Hps. unfold stdout_vprintf. eapply mspec_seq; [apply stdout_towrite_GI|]. intros _. apply out_pieces_GI. exact Hps.
Qed.
Lemma stdout_exit_flush_GI : forall X, mspec (GI X) (stdout_exit_flush ps_so set_so_ps) (fun _ => GI X).
Proof.
intros X. unfold stdout_exit_flush. eapply mspec_bind; [apply (rd_so_GI X)|]. intros so.
apply mspec_pointwise. intros s1 mo1 [Ho ->]. destruct (0 <? _).
- Local Ltac2 Set LiaHints.tbl := fun () => "0010=43365953645.4000001S".
eapply mspec_conseq; [apply stdout_writefn_GI; unfold zlength, PIECE_MAX; cbn; lia| intros s' mo' [-> ->]; exact Ho| intros [] s' mo' [H _]; exact H].
- apply mspec_ret. intros s' mo' [-> ->]; exact Ho.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma stderr_pieces_GI : forall X ps buf, zlength buf <= INTERNAL_BUFSIZ -> Forall (fun p => zlength p <= PIECE_MAX) ps ->
mspec (GI X) (stderr_pieces buf ps) (fun buf' s mo => GI X s mo /\ zlength buf' <= INTERNAL_BUFSIZ).
Proof.
intros X ps. induction ps as [|p ps IH]; intros buf Hbuf Hps; cbn [stderr_pieces].
- apply mspec_ret. intros s mo H. auto.
- inversion Hps; subst. unfold INTERNAL_BUFSIZ, PIECE_MAX in *. apply mspec_if; intros C.
+ Local Ltac2 Set LiaHints.tbl := fun () => "0030>17162000922.1026729265166.1041082011929.1000000300<00=S1CS4Hbuf2H1S".
eapply mspec_seq; [apply stdio_write_GI; unfold zlength, WRITE_MAX in *; lia|]. intros _. apply IH; [unfold zlength; cbn; lia| assumption].
+ apply Z.ltb_ge in C. apply IH; [rewrite zlength_app; lia| assumption].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma stderr_fprintf_GI : forall X ps, Forall (fun p => zlength p <= PIECE_MAX) ps ->
mspec (GI X) (stderr_fprintf ps) (fun _ => GI X).
Proof.
intros X ps Hps. unfold stderr_fprintf. Local Ltac2 Set LiaHints.tbl := fun () => "0020=41086295017.359077922741.8000001005SS2Hb".
eapply mspec_bind; [apply stderr_pieces_GI; [unfold zlength, INTERNAL_BUFSIZ; cbn; lia| exact Hps]|].
intros buf. apply mspec_pointwise. intros s1 mo1 [Ho Hb]. unfold INTERNAL_BUFSIZ in Hb.
eapply mspec_pre; [apply stdio_write_GI; unfold zlength, WRITE_MAX in *; cbn; lia|]. intros s mo [-> ->]; exact Ho.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma stderr_fwrite_GI : forall X s, zlength s <= PIECE_MAX -> mspec (GI X) (stderr_fwrite s) (fun _ => GI X).
Proof.
intros X s Hs. unfold stderr_fwrite. apply mspec_if; intros _; [|apply mspec_ret; intros s0 mo H; exact H].
apply stdio_write_GI. Local Ltac2 Set LiaHints.tbl := fun () => "0010=41303967804.3000004S2Hs".
unfold zlength, PIECE_MAX, WRITE_MAX in *; cbn; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma s_diag_GI : forall X d, diag_ok d -> mspec (GI X) (s_diag d) (fun _ => GI X).
Proof.
intros X d Hd. unfold s_diag. destruct d; cbn in Hd; unfold ARG_MAX_LEN in *.
all: try (apply stderr_fprintf_GI; repeat constructor; unfold zlength, PIECE_MAX in *; cbn; lia).
all: apply stderr_fwrite_GI; unfold zlength, PIECE_MAX; cbn; lia.
Qed.
Lemma fmt_u_length : forall fuel n acc, (length (digits_aux fuel n acc) <= fuel + length acc)%nat.
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "0030=23139961700.424928963119.247839791572.4000001002003SSS".
induction fuel as [|fuel IH]; intros n acc; cbn [digits_aux]; [lia|].
destruct (n =? 0); [cbn; lia|]. etransitivity; [apply IH|]. cbn. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma pieces_pct_d_short : forall v, Forall (fun p => zlength p <= PIECE_MAX) (pieces_pct_d v).
Proof.
intros v. unfold pieces_pct_d, fmt_u.
pose proof (fmt_u_length 20 v []) as L1. pose proof (fmt_u_length 20 (- v) []) as L2. cbn [length] in L1, L2.
destruct (v =? 0); [|destruct (v <? 0)]; repeat constructor; unfold zlength, PIECE_MAX; cbn [length]; lia.
Qed.
Lemma s_emit_GI : forall X v, mspec (GI X) (s_emit ps_so set_so_ps v) (fun _ => GI X).
Proof. intros X v. unfold s_emit. apply stdout_vprintf_GI. apply pieces_pct_d_short. Qed.
Lemma GI_leak : forall X Y s mo, GI (Y ++ X) s mo -> GI X s mo.
Proof.
intros X Y s mo [(L & Hc & K & Hi) [Hnd HG]]. split; [|split; [|exact HG]].
- exists L. split; [exact Hc|]. split; [exact K|]. intros c Hc'. apply Hi. rewrite map_app. apply in_or_app. right. exact Hc'.
- rewrite map_app in Hnd. apply List.NoDup_app_remove_l in Hnd. exact Hnd.
Qed.
Lemma run_GI : forall X cfg payload, zlength payload <= MAX_INPUT -> mspecP (GI X) (run cfg payload) (fun _ => GI X).
Proof.
intros X cfg payload Hlen. unfold run, fuzz_one.
apply (target_run_spec raw_malloc raw_free new_handler (io_emit io) GI).
- apply raw_malloc_GI. - apply raw_malloc_GIP. - apply raw_free_GI. - apply GI_perm. - apply GI_leak.
- intros X' v. apply s_emit_GI. - exact Hlen.
Qed.
Theorem prog_with_GIP : forall rs argv,
Forall (fun a => zlength a <= ARG_MAX_LEN) argv ->
mspecP (GI []) (prog_with rs argv) (fun _ _ _ => False).
Proof.
intros rs argv Hargv. unfold prog_with.
eapply mspecP_seq; [apply mspec_mspecP; apply startup_GI|]. intros _.
eapply mspecP_bind.
- eapply (main_model_spec io raw_malloc raw_free rs alloc_init run alloc_count GI);
first [ exact Hargv | apply raw_malloc_GI | apply raw_free_GI | apply GI_perm
| (intros; apply s_diag_GI; assumption) | apply stdout_exit_flush_GI
| apply alloc_init_GI | apply alloc_count_GI | apply run_GI | apply GI_minv | apply GI_fds ].
- intros code. eapply (exit_model_spec io GI); first [apply stdout_exit_flush_GI | apply GI_minv | apply GI_fds].
Qed.
Lemma reserved_top_ge : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
cbn [reserved_top]. Local Ltac2 Set LiaHints.tbl := fun () => "0020=16825179538.425708821631.6000001005SS2IH".
destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma GI_init : forall segs brk0 mbase sp lim inp atop,
valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) ->
sp_window_lo <= bv_unsigned sp <= sp_window_hi ->
atop = bv_unsigned sp - stack_max_size ->
reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
GI [] (ps_init (reservedZ segs) atop) (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
intros segs brk0 mbase sp lim inp atop (Hlo & Hhi & Hal) Hpos Hsp Eatop Hceil. unfold GI, OWN.
pose proof alloc_ceiling_lo_val as Hclo.
Local Ltac2 Set LiaHints.tbl := fun () => "0040>13807164177.1814152173418.1533668031574.2143368053096.1600000R00]00d00eS3Hlo3Hhi3Hal4Hpos3Hsp5Eatop5HceilS3Hsp5EatopS3Hlo1HS".
assert (Hat : 0 < atop <= atop_hi) by (unfold atop_hi, sp_window_lo, sp_window_hi, stack_max_size in *; lia).
split; [|split; [apply List.NoDup_nil| unfold Gso, so_ok; cbn [ps_so ps_init so_buf stdout_init]; unfold zlength, STDOUT_BUFSIZ; cbn; lia]].
exists (led_init (reservedZ segs) atop). split; [apply creach_init; exact Hat|]. split; [|intros c []].
assert (Evm : m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp)
= mkVmMapsFull (segments_reserved segs) [] [] brk0 brk0 lim mbase sp) by reflexivity.
assert (Eh : m_halted (init_model (segments_reserved segs) brk0 mbase sp lim inp) = None) by reflexivity.
constructor; rewrite ?Evm; cbn -[Z.pow Z.mul Z.add Z.sub init_model alloc_top].
- apply minv_init. exact Hsp.
- exact Eh.
- split; [intros e []| apply pwdisj_nil].
- reflexivity.
- intros e Hin. pose proof (reserved_top_ge _ _ Hin). unfold ehi. lia.
- unfold PGSZ in *. unfold page_size in Hal. unfold alloc_ceiling_lo, sp_window_lo, stack_max_size in *. lia.
- intros b l [].
- intros b l k [].
- apply List.NoDup_nil.
- intros b l H. discriminate.
- split; reflexivity.
- unfold alloc_top. cbn [vm_init_sp]. exact Eatop.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma argv_Z_short : forall argv, valid_argv argv -> Forall (fun a => zlength a <= ARG_MAX_LEN) (argv_Z argv).
Proof.
intros argv (_ & _ & HF & _). unfold argv_Z. apply Forall_map. eapply Forall_impl; [|exact HF].
intros a Ha. unfold zlength, ARG_MAX_LEN in *. rewrite length_map. Local Ltac2 Set LiaHints.tbl := fun () => "0010=49917309728.4000004S2Ha".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma prog_argv_atop_only : forall segs rs inp inp' en en',
in_argv inp = in_argv inp' -> InitMem.entry_atop en = InitMem.entry_atop en' ->
Prog.prog segs rs inp en = Prog.prog segs rs inp' en'.
Proof. intros segs rs inp inp' en en' H E. unfold prog. rewrite H, E. reflexivity. Qed.
