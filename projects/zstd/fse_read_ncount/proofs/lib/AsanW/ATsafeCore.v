(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import AcctCore ExecF ITreeA ModelX MmXfer NodesA.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Monad RSimProg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AProto.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Section Core.
Variable NMAX : nat.
Definition postT (R : Type) : Type := R -> footprint -> alw -> Model -> Prop.
Fixpoint TS {R} (RNG : footprint) (A : alw) (t : itree node R) (mo : Model) (Q : postT R) {struct t} : Prop :=
acct_ok NMAX RNG A mo /\
match t with
| Ret r => Q r RNG A mo
| Vis n k => nsafeA NMAX n mo /\
forall rsp mo' evs, nstepA n mo rsp mo' evs ->
exists RNG' A', fstepS n rsp RNG RNG' /\ alw_le A A' /\ TS RNG' A' (k rsp) mo' Q
end.
#[using="Type"] Lemma TS_unfold_vis : forall {R} RNG A n (k : resp -> itree node R) mo Q,
TS RNG A (Vis n k) mo Q <->
(acct_ok NMAX RNG A mo /\ nsafeA NMAX n mo /\
forall rsp mo' evs, nstepA n mo rsp mo' evs ->
exists RNG' A', fstepS n rsp RNG RNG' /\ alw_le A A' /\ TS RNG' A' (k rsp) mo' Q).
Proof. intros. cbn. tauto. Qed.
#[using="Type"] Lemma TS_tsafeA : forall {R} (t : itree node R) RNG A mo Q,
TS RNG A t mo Q -> tsafeA nstepA (nsafeA NMAX) fstepS NMAX RNG A t mo.
Proof.
intros R t. induction t as [r|n k IH]; intros RNG A mo Q H; cbn in H |- *.
- split; [exact (proj1 H)| exact I].
- destruct H as (HA & HS & HK). split; [exact HA|]. split; [exact HS|].
intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (RNG' & A' & HF & HL & HT).
exists RNG', A'. split; [exact HF|]. split; [exact HL|]. eapply IH. exact HT.
Qed.
#[using="Type"] Lemma TS_mono : forall {R} (t : itree node R) RNG A mo (Q Q' : postT R),
TS RNG A t mo Q -> (forall r RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q r RNG' A' mo' -> Q' r RNG' A' mo') -> TS RNG A t mo Q'.
Proof.
intros R t. induction t as [r|n k IH]; intros RNG A mo Q Q' H HQ; cbn in H |- *.
- destruct H as [HA HQ1]. split; [exact HA| apply HQ; assumption].
- destruct H as (HA & HS & HK). split; [exact HA|]. split; [exact HS|].
intros rsp mo' evs Hst. destruct (HK rsp mo' evs Hst) as (RNG' & A' & HF & HL & HT).
exists RNG', A'. split; [exact HF|]. split; [exact HL|]. eapply IH; [exact HT| exact HQ].
Qed.
#[using="Type"] Lemma TS_ret : forall {R} (r : R) RNG A mo (Q : postT R),
acct_ok NMAX RNG A mo -> Q r RNG A mo -> TS RNG A (Ret r) mo Q.
Proof. intros. cbn. split; assumption. Qed.
#[using="Type"] Lemma TS_bind : forall {X Y} (t : itree node X) (k : X -> itree node Y) RNG A mo (Q1 : postT X) (Q : postT Y),
TS RNG A t mo Q1 ->
(forall r RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q1 r RNG' A' mo' -> TS RNG' A' (k r) mo' Q) ->
TS RNG A (bind node t k) mo Q.
Proof.
intros X Y t. induction t as [r|n k0 IH]; intros k RNG A mo Q1 Q H HK; cbn in H.
- destruct H as [HA H1]. cbn. apply HK; assumption.
- destruct H as (HA & HS & HC). cbn. split; [exact HA|]. split; [exact HS|].
intros rsp mo' evs Hst. destruct (HC rsp mo' evs Hst) as (RNG' & A' & HF & HL & HT).
exists RNG', A'. split; [exact HF|]. split; [exact HL|]. eapply IH; [exact HT| exact HK].
Qed.
Definition EQ {X} (Q : postT X) : postT (exc X) :=
fun r RNG A mo => match r with Unr => True | Ok x => Q x RNG A mo end.
#[using="Type"] Lemma TS_ebind : forall {X Y} (t : itree node (exc X)) (f : X -> itree node (exc Y)) RNG A mo (Q1 : postT X) (Q : postT Y),
TS RNG A t mo (EQ Q1) ->
(forall x RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q1 x RNG' A' mo' -> TS RNG' A' (f x) mo' (EQ Q)) ->
TS RNG A (ebind t f) mo (EQ Q).
Proof.
intros X Y t f RNG A mo Q1 Q H HK. unfold ebind. eapply TS_bind; [exact H|].
intros [|x] RNG' A' mo' HA H1; cbn in H1.
- apply TS_ret; [exact HA| exact I].
- apply HK; assumption.
Qed.
#[using="Type"] Lemma TS_ret_ok : forall {X} (x : X) RNG A mo (Q : postT X),
acct_ok NMAX RNG A mo -> Q x RNG A mo -> TS RNG A (Ret (Ok x)) mo (EQ Q).
Proof. intros. apply TS_ret; assumption. Qed.
#[using="Type"] Lemma TS_ret_unr : forall {X} RNG A mo (Q : postT X), acct_ok NMAX RNG A mo -> TS RNG A (Ret Unr) mo (EQ Q).
Proof. intros. apply TS_ret; [assumption| exact I]. Qed.
#[using="Type"] Lemma TS_EQ_mono : forall {X} (t : itree node (exc X)) RNG A mo (Q Q' : postT X),
TS RNG A t mo (EQ Q) -> (forall x RNG' A' mo', acct_ok NMAX RNG' A' mo' -> Q x RNG' A' mo' -> Q' x RNG' A' mo') ->
TS RNG A t mo (EQ Q').
Proof. intros X t RNG A mo Q Q' H HQ. eapply TS_mono; [exact H|]. intros [|x] RNG' A' mo' HA H1; cbn in *; [exact I| apply HQ; assumption]. Qed.
#[using="Type"] Lemma acct_ok_vm : forall RNG A mo mo',
m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_vm_materialized mo' = m_vm_materialized mo ->
acct_ok NMAX RNG A mo -> acct_ok NMAX RNG A mo'.
Proof.
intros RNG A mo mo' E1 E2 E3 (F & L & R). unfold acct_ok. rewrite E2, E1.
split; [exact F|]. split; [exact L|]. unfold nonlazy_bytes in *. rewrite E1, E2. exact R.
Qed.
#[using="Type"] Lemma acct_ok_with_fds : forall RNG A f mo, acct_ok NMAX RNG A mo -> acct_ok NMAX RNG A (with_fds f mo).
Proof. intros. eapply acct_ok_vm; [ | | | eassumption]; reflexivity. Qed.
#[using="Type"] Lemma acct_ok_with_tid : forall RNG A t mo, acct_ok NMAX RNG A mo -> acct_ok NMAX RNG A (with_tid t mo).
Proof. intros. eapply acct_ok_vm; [ | | | eassumption]; reflexivity. Qed.
#[using="Type"] Lemma nstep_io_shape : forall n mo eff mo' evs,
io_node n -> nstep n mo eff mo' evs -> mo' = mo \/ (exists f, mo' = with_fds f mo) \/ (exists t, mo' = with_tid t mo).
Proof.
intros n mo eff mo' evs Hio H. destruct n; cbn in Hio; try contradiction; cbn [nstep] in H.
- destruct H as (k & _ & _ & -> & _). left; reflexivity.
- destruct H as [-> _]. left; reflexivity.
- destruct H as [_ H]. destruct (Nat.leb path_max (length path)); [destruct H as [_ ->]; left; reflexivity|].
assert (OR : forall ent, open_result mo ent eff mo' -> mo' = mo \/ (exists f, mo' = with_fds f mo) \/ (exists t, mo' = with_tid t mo)).
{ intros ent [(e & _ & _ & ->)|(_ & _ & ->)]; [left; reflexivity| right; left; eexists; reflexivity]. }
destruct path; [destruct H as [_ ->]; left; reflexivity|].
match type of H with (if ?c then _ else _) => destruct c; [apply (OR _ H)|] end.
destruct (fs_lookup _ _); [apply (OR _ H)| destruct H as [_ ->]; left; reflexivity].
- destruct H as [_ H]. destruct (fd_lookup _ _) as [[ch|p off|p1 off1|p2 off2|p3 off3| |sk|pid pw|dnr dnw| ]|]; try contradiction;
try (destruct H as [_ ->]; left; reflexivity).
destruct (fs_lookup _ _); [|contradiction]. destruct H as [_ ->]. right; left; eexists; reflexivity.
- destruct H as (_ & _ & H). destruct (fd_lookup _ _); destruct H as [_ ->]; [right; left; eexists; reflexivity| left; reflexivity].
- destruct H as (_ & _ & ->). left; reflexivity.
- destruct H as (_ & t & _ & H). destruct (m_tid mo); destruct H as [_ ->]; [left; reflexivity| right; right; eexists; reflexivity].
Qed.
#[using="Type"] Lemma acct_ok_io : forall n mo eff mo' evs RNG A,
io_node n -> nstep n mo eff mo' evs -> acct_ok NMAX RNG A mo -> acct_ok NMAX RNG A mo'.
Proof.
intros n mo eff mo' evs RNG A Hio Hst HA.
destruct (nstep_io_shape n mo eff mo' evs Hio Hst) as [-> | [(f & ->) | (t & ->)]];
[exact HA| apply acct_ok_with_fds; exact HA| apply acct_ok_with_tid; exact HA].
Qed.
#[using="Type"] Lemma TS_io : forall {R} n (k : resp -> itree node R) RNG A mo (Q : postT R),
io_node n -> acct_ok NMAX RNG A mo ->
(forall rsp mo' evs, nstep n mo rsp mo' evs -> acct_ok NMAX RNG A mo' -> TS RNG A (k rsp) mo' Q) ->
TS RNG A (Vis n k) mo Q.
Proof.
intros R n k RNG A mo Q Hio HA HK. cbn. split; [exact HA|]. split.
{ split; [destruct n; cbn in Hio |- *; try contradiction; exact I | destruct n; cbn in Hio |- *; try contradiction; exact I]. }
intros rsp mo' evs Hst.
assert (Hst' : nstep n mo rsp mo' evs) by (destruct n; cbn in Hio; try contradiction; exact Hst).
exists RNG, A. split; [apply fstepS_id; destruct n; cbn in Hio |- *; try contradiction; exact I|].
split; [apply alw_le_refl|]. apply (HK rsp mo' evs); [exact Hst'| eapply (acct_ok_io n mo rsp mo' evs); eauto].
Qed.
Section Triples.
Context {St : Type}.
Definition preT : Type := footprint -> alw -> St -> Model -> Prop.
Definition postM (X : Type) : Type := X -> footprint -> alw -> St -> Model -> Prop.
Definition MQ {X} (Q : postM X) : postT (exc (X * St)) := EQ (fun p RNG A mo => Q (fst p) RNG A (snd p) mo).
Definition TSM {X} (P : preT) (m : M St X) (Q : postM X) : Prop :=
forall RNG A s mo, P RNG A s mo -> TS RNG A (m s) mo (MQ Q).
#[using="Type"] Lemma TSM_conseq : forall {X} (P P' : preT) (m : M St X) (Q Q' : postM X),
TSM P m Q -> (forall RNG A s mo, P' RNG A s mo -> P RNG A s mo) ->
(forall x RNG A s mo, acct_ok NMAX RNG A mo -> Q x RNG A s mo -> Q' x RNG A s mo) -> TSM P' m Q'.
Proof.
intros X P P' m Q Q' H HP HQ RNG A s mo Hp. eapply TS_EQ_mono; [apply H; apply HP; exact Hp|].
intros [x s'] RNG' A' mo' HA H1. cbn in *. apply HQ; assumption.
Qed.
#[using="Type"] Lemma TSM_pre : forall {X} (P P' : preT) (m : M St X) (Q : postM X),
TSM P m Q -> (forall RNG A s mo, P' RNG A s mo -> P RNG A s mo) -> TSM P' m Q.
Proof. intros. eapply TSM_conseq; eauto. Qed.
#[using="Type"] Lemma TSM_post : forall {X} (P : preT) (m : M St X) (Q Q' : postM X),
TSM P m Q -> (forall x RNG A s mo, acct_ok NMAX RNG A mo -> Q x RNG A s mo -> Q' x RNG A s mo) -> TSM P m Q'.
Proof. intros. eapply TSM_conseq; eauto. Qed.
#[using="Type"] Lemma TSM_ret : forall {X} (x : X) (P : preT) (Q : postM X),
(forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo /\ Q x RNG A s mo) -> TSM P (mret x) Q.
Proof. intros X x P Q H RNG A s mo Hp. destruct (H _ _ _ _ Hp) as [HA HQ]. apply TS_ret_ok; [exact HA| exact HQ]. Qed.
#[using="Type"] Lemma TSM_munr : forall {X} (P : preT) (Q : postM X),
(forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) -> TSM P (munr (A:=X)) Q.
Proof. intros X P Q H RNG A s mo Hp. apply TS_ret_unr. apply (H _ _ _ _ Hp). Qed.
#[using="Type"] Lemma TSM_bind : forall {X Y} (P : preT) (m : M St X) (f : X -> M St Y) (Q1 : postM X) (Q : postM Y),
TSM P m Q1 -> (forall x, TSM (fun RNG A s mo => acct_ok NMAX RNG A mo /\ Q1 x RNG A s mo) (f x) Q) -> TSM P (mbind m f) Q.
Proof.
intros X Y P m f Q1 Q Hm Hf RNG A s mo Hp. unfold mbind. eapply TS_ebind; [apply Hm; exact Hp|].
intros [x s'] RNG' A' mo' HA H1. cbn in H1. apply Hf. split; assumption.
Qed.
#[using="Type"] Lemma TSM_get : forall (P : preT),
(forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) ->
TSM P mget (fun s' RNG A s mo => s' = s /\ P RNG A s mo).
Proof. intros P H RNG A s mo Hp. apply TS_ret_ok; [apply (H _ _ _ _ Hp)|]. cbn. auto. Qed.
#[using="Type"] Lemma TSM_upd : forall (f : St -> St) (P : preT),
(forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) ->
TSM P (mupd f) (fun _ RNG A s' mo => exists s, s' = f s /\ P RNG A s mo).
Proof. intros f P H RNG A s mo Hp. apply TS_ret_ok; [apply (H _ _ _ _ Hp)|]. cbn. eauto. Qed.
#[using="Type"] Lemma TSM_bind_get : forall {X} (P : preT) (k : St -> M St X) (Q : postM X),
(forall s0, TSM (fun RNG A s mo => s = s0 /\ P RNG A s mo) (k s0) Q) ->
(forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) ->
TSM P (mbind mget k) Q.
Proof.
intros X P k Q Hk HA RNG A s mo Hp. unfold mbind, mget. cbn. apply Hk. auto.
Qed.
#[using="Type"] Lemma TSM_if : forall {X} (b : bool) (P : preT) (m1 m2 : M St X) (Q : postM X),
(b = true -> TSM P m1 Q) -> (b = false -> TSM P m2 Q) -> TSM P (if b then m1 else m2) Q.
Proof. intros X [|] P m1 m2 Q H1 H2; [apply H1| apply H2]; reflexivity. Qed.
#[using="Type"] Lemma TSM_pure : forall {X} (P : preT) (phi : Prop) (m : M St X) (Q : postM X),
(forall RNG A s mo, P RNG A s mo -> phi) -> (phi -> TSM P m Q) -> TSM P m Q.
Proof. intros X P phi m Q Hphi H RNG A s mo Hp. apply (H (Hphi _ _ _ _ Hp)). exact Hp. Qed.
#[using="Type"] Lemma TSM_exI : forall {X T} (P : T -> preT) (m : M St X) (Q : postM X),
(forall x, TSM (P x) m Q) -> TSM (fun RNG A s mo => exists x, P x RNG A s mo) m Q.
Proof. intros X T P m Q H RNG A s mo (x & Hp). apply (H x). exact Hp. Qed.
#[using="Type"] Lemma TSM_loop : forall {X R} (I : X -> preT) (Q : postM R) (body : X -> M St (X + R)),
(forall x, TSM (I x) (body x) (fun r RNG A s mo => match r with inl x' => I x' RNG A s mo | inr r => Q r RNG A s mo end)) ->
(forall x RNG A s mo, I x RNG A s mo -> acct_ok NMAX RNG A mo) ->
forall fuel x, TSM (I x) (mloop fuel body x) Q.
Proof.
intros X R I Q body HB HA fuel. induction fuel as [|fuel IH]; intros x.
- cbn. apply TSM_munr. apply HA.
- cbn [mloop]. eapply TSM_bind; [apply HB|]. intros [x'|r].
+ eapply TSM_pre; [apply IH|]. cbv beta. intros RNG A s mo [_ H]; exact H.
+ apply TSM_ret. cbv beta. intros RNG A s mo [H1 H2]. auto.
Qed.
#[using="Type"] Lemma TSM_msys_io : forall {X} n (dec : resp -> option X) (P : preT) (Q : postM X),
io_node n ->
(forall RNG A s mo, P RNG A s mo -> acct_ok NMAX RNG A mo) ->
(forall RNG A s mo rsp mo' evs x, P RNG A s mo -> nstep n mo rsp mo' evs -> dec rsp = Some x -> Q x RNG A s mo') ->
TSM P (msys n dec) Q.
Proof.
intros X n dec P Q Hio HA HQ RNG A s mo Hp. unfold msys, enode.
apply TS_io; [exact Hio| apply (HA _ _ _ _ Hp)|].
intros rsp mo' evs Hst HA'. destruct (dec rsp) as [x|] eqn:E.
- apply TS_ret_ok; [exact HA'|]. cbn. eapply HQ; eauto.
- apply TS_ret_unr. exact HA'.
Qed.
End Triples.
End Core.
End CANSEC1.
Arguments TS NMAX {R} RNG A t mo Q.
Arguments TSM NMAX {St X} P m Q.
Arguments MQ {St X} Q.
Arguments EQ {X} Q.
Section CANSEC2. Context {rc : runConstT}.
Definition abud (A : alw) (k : Z) : Prop :=
exists L : list word, List.NoDup L /\ Z.of_nat (length L) <= k /\ forall p, A p -> In p L.
#[using="Type"] Lemma abud_mono : forall A k k', abud A k -> k <= k' -> abud A k'.
Proof. intros A k k' (L & N & Hl & HL) Hk. exists L. split; [exact N|]. Local Ltac2 Set LiaHints.tbl := fun () => "0010=14127638378.9000007S2Hl2Hk".
split; [lia| exact HL]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition aunion (A : alw) (ps : list word) : alw := fun p => A p \/ In p ps.
#[using="Type"] Lemma aunion_le : forall A ps, alw_le A (aunion A ps).
Proof. intros A ps p H. left; exact H. Qed.
#[using="Type"] Lemma aunion_in : forall A ps p, In p ps -> aunion A ps p.
Proof. intros A ps p H. right; exact H. Qed.
#[using="Type"] Lemma nodup_extend : forall (L ps : list word), List.NoDup L ->
exists L', List.NoDup L' /\ (length L' <= length L + length ps)%nat /\ (forall p, In p L \/ In p ps -> In p L').
Proof.
intros L ps N. induction ps as [|q ps IH].
- exists L. split; [exact N|]. Local Ltac2 Set LiaHints.tbl := fun () => "0030>16484582029.1019256902453.3 53623619163.1000000600700=S4HlenSS4Hlen".
split; [cbn; lia|]. intros p [H|[]]; exact H.
- destruct IH as (L' & N' & Hlen & HL').
destruct (in_dec (fun x y => bv_eq_dec _ x y) q L') as [Hin|Hnin].
+ exists L'. split; [exact N'|]. split; [cbn; lia|].
intros p [H|[<-|H]]; [apply HL'; left; exact H| exact Hin| apply HL'; right; exact H].
+ exists (q :: L'). split; [constructor; [exact Hnin| exact N']|]. split; [cbn; lia|].
intros p [H|[<-|H]]; [right; apply HL'; left; exact H| left; reflexivity| right; apply HL'; right; exact H].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma abud_union : forall A k ps, abud A k -> abud (aunion A ps) (k + Z.of_nat (length ps)).
Proof.
intros A k ps (L & N & Hl & HL). destruct (nodup_extend L ps N) as (L' & N' & Hlen & HL').
exists L'. split; [exact N'|]. Local Ltac2 Set LiaHints.tbl := fun () => "0010>40444394064.12000009S2Hl4Hlen".
split; [lia|]. intros p [H|H]; apply HL'; [left; apply HL; exact H| right; exact H].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Fixpoint pages_from (p0 : Z) (n : nat) : list word :=
match n with O => [] | S n' => Z_to_bv 64 p0 :: pages_from (p0 + 4096) n' end.
#[using="Type"] Lemma pages_from_length : forall p0 n, length (pages_from p0 n) = n.
Proof. intros p0 n. revert p0. induction n; intros; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.
#[using="Type"] Lemma pages_from_in : forall p0 n (i : nat), (i < n)%nat -> In (Z_to_bv 64 (p0 + 4096 * Z.of_nat i)) (pages_from p0 n).
Proof.
intros p0 n. revert p0. Local Ltac2 Set LiaHints.tbl := fun () => "0040=43649783964.653768766698.654514058377.59177610580.4 00000400800<00@S2HiS2HiS2HiS2Hi".
induction n as [|n IH]; intros p0 i Hi; [lia|]. cbn. destruct i as [|i].
- left. f_equal. lia.
- right. replace (p0 + 4096 * Z.of_nat (S i)) with (p0 + 4096 + 4096 * Z.of_nat i) by lia. apply IH. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition range_pages (lo len : Z) : list word :=
pages_from (lo / 4096 * 4096) (Z.to_nat ((lo + len - 1) / 4096 - lo / 4096 + 1)).
#[using="Type"] Lemma range_pages_length : forall lo len, 0 <= lo -> 0 < len ->
Z.of_nat (length (range_pages lo len)) <= len / 4096 + 2.
Proof.
intros lo len Hlo Hlen. unfold range_pages. rewrite pages_from_length.
Local Ltac2 Set LiaHints.tbl := fun () => "0070>18926759668.7 18926759926.9 18928845099.1018928845357.8 18930958230.6 18939331882.5 4193760632.11 00000100200300400500600MSSSSSSS4Hlen1H2H02H12H22H32H4".
pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
pose proof (Z.div_mod (lo + len - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (lo + len - 1) 4096 ltac:(lia)).
pose proof (Z.div_mod len 4096 ltac:(lia)). pose proof (Z.mod_pos_bound len 4096 ltac:(lia)). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma range_pages_spec : forall lo len z, 0 <= lo -> lo <= z < lo + len ->
In (page_base_of z) (range_pages lo len).
Proof.
intros lo len z Hlo Hz. unfold range_pages, page_base_of, page_size.
Local Ltac2 Set LiaHints.tbl := fun () => "00<0>18926750654.6 18926759668.8 18926759926.1018928648749.1318928845099.1118928845226.1218928845357.9 18930958230.7 23254035887.1237918913158.1451768429553.1464676900652.1300000100200300400500600700800<00N00]00aSSSSSSSSS2HzS2Hz1H2H02H32H42D2S2Hz1H2H02H12H2S2Hz".
pose proof (Z.div_mod lo 4096 ltac:(lia)). pose proof (Z.mod_pos_bound lo 4096 ltac:(lia)).
pose proof (Z.div_mod z 4096 ltac:(lia)). pose proof (Z.mod_pos_bound z 4096 ltac:(lia)).
pose proof (Z.div_mod (lo + len - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (lo + len - 1) 4096 ltac:(lia)).
assert (D1 : lo / 4096 <= z / 4096) by (apply Z.div_le_mono; lia).
assert (D2 : z / 4096 <= (lo + len - 1) / 4096) by (apply Z.div_le_mono; lia).
replace (z / 4096 * 4096) with (lo / 4096 * 4096 + 4096 * Z.of_nat (Z.to_nat (z / 4096 - lo / 4096))) by lia.
apply pages_from_in. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rng_fp_ok_union : forall lz A lo len ps,
0 <= lo -> lo + len <= 2^64 -> (forall z, lo <= z < lo + len -> In (page_base_of z) ps) ->
rng (fp_ok lz (aunion A ps)) lo len.
Proof.
intros lz A lo len ps Hlo Hhi H. apply rng_fp_ok; [exact Hlo| exact Hhi|]. intros z Hz. right. right. apply H. exact Hz.
Qed.
End CANSEC2.
