(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad MSafe Sim MPaths STree Malloc Stdio Harness Adapter Driver StepB.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Notation M := Monad.M.
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Section FsimEq.
Context {StG StC : Type}.
Variables (debtG : StG -> list event) (debtC : StC -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Local Notation rel := (rel StG StC).
Local Notation fsim := (fsim debtG debtC stepG).
Definition fsimeq {A} (R : rel) (mG : M StG A) (mC : M StC A) (Q : A -> rel) : Prop :=
fsim R mG mC (fun a b sG moG sC moC => a = b /\ Q a sG moG sC moC).
End FsimEq.
Definition E1 (l : list Z) : list event := map (WriteEv (Z_to_bv 64 1)) (to_bytes l).
Definition E2 (l : list Z) : list event := map (WriteEv (Z_to_bv 64 2)) (to_bytes l).
Lemma to_bytes_length : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.
Definition PIECE_MAX : Z := 1048576.
Section Det.
Context {St : Type}.
Context {stp : node -> Model -> resp -> Model -> list event -> Prop}.
Definition detio {A} (t : itree node (exc (A * St))) (mo : Model) (P : list event -> A -> St -> Prop) : Prop :=
exists tr a s', tpath stp t mo tr (Ok (a, s')) mo /\ P tr a s'
/\ (forall tr' x mo', tpath stp t mo tr' x mo' -> x = Ok (a, s') /\ mo' = mo /\ tr' = tr)
/\ (forall tr', ~ texit stp nexit t mo tr').
End Det.
Section StdioChar.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis get_set : forall v s, get_so (set_so v s) = v.
Hypothesis set_set : forall v w s, set_so v (set_so w s) = set_so v s.
Hypothesis set_get : forall s, set_so (get_so s) s = s.
Context {stp : node -> Model -> resp -> Model -> list event -> Prop}.
Hypothesis st_sub : forall n mo r mo' e, ~ nf_node n -> stp n mo r mo' e -> nstep n mo r mo' e.
Hypothesis st_same : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> stp n mo r mo e.
Local Notation detio := (detio (stp:=stp)).
#[using="Type"] Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros n l. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.
#[using="Type"] Lemma to_bytes_app : forall a b, to_bytes (a ++ b) = to_bytes a ++ to_bytes b.
Proof. intros. unfold to_bytes. apply map_app. Qed.
#[using="Type"] Lemma iov_advance_concat : forall iov cnt, (length iov <= 2)%nat -> 0 <= cnt <= Z.of_nat (length (concat iov)) ->
concat (map to_bytes (iov_advance iov cnt)) = skipn (Z.to_nat cnt) (concat (map to_bytes iov))
/\ (length (iov_advance iov cnt) <= 2)%nat.
Proof.
intros iov cnt Hl Hc. Local Ltac2 Set LiaHints.tbl := fun () => "0080>11243032820.1616007654544.1523094145225.1323100433956.1528200660786.1241480806399.1544831285033.1567643081.15   00000400:00;00?00C00I00O00SS2HlS2Hc1HSS2HcS2HcS2Hc1HS2Hc1HS2Hc".
destruct iov as [|a [|b [|c rest]]]; cbn in Hl, Hc |- *; [| | |lia].
- split; [destruct (Z.to_nat cnt); reflexivity| lia].
- rewrite !app_nil_r. split; [apply to_bytes_skipn| cbn; lia].
- rewrite app_nil_r in *. rewrite length_app in Hc. destruct (Z.ltb_spec (zlength a) cnt); cbn; rewrite ?app_nil_r.
+ unfold zlength in *. split; [|lia]. rewrite to_bytes_skipn, skipn_app, to_bytes_length.
replace (skipn (Z.to_nat cnt) (to_bytes a)) with (@nil byte) by (symmetry; apply skipn_all2; rewrite to_bytes_length; lia).
cbn. f_equal. lia.
+ unfold zlength in *. split; [|lia]. rewrite to_bytes_skipn, skipn_app, to_bytes_length.
replace (Z.to_nat cnt - length a)%nat with 0%nat by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma length_concat_to_bytes' : forall iov, length (concat (map to_bytes iov)) = length (concat iov).
Proof. induction iov as [|a iov IH]; cbn; [reflexivity|]. rewrite !length_app, to_bytes_length, IH. reflexivity. Qed.
#[using="st_sub st_same"] Lemma stdio_write_loop_det : forall fuel fd iov (st : St) mo,
(length (concat (map to_bytes iov)) < fuel)%nat -> (length iov <= 2)%nat -> Z.of_nat (length (concat (map to_bytes iov))) < 2^63 ->
detio (stdio_write_loop (St:=St) fuel fd iov st) mo
(fun tr _ s' => s' = st /\ tr = map (WriteEv (Z_to_bv 64 fd)) (concat (map to_bytes iov))).
Proof.
Local Ltac2 Set LiaHints.tbl := fun () => "00>0>1448173107.16 1876134254.26 22481159167.3622481159167.3829406272477.253376111990.36 3376111990.38 45774887436.264614126463.23 64831266161.2467186943210.3367186943210.358184223268.23 9753470396.23 00000700A00Y01101;01P01e01o02802B02M02X02b02lS2Hf2HlS2Hf2Hl2HkS2Hf2Hl2Hb3Hlt3Hl'5Hlen'S2Hf2Hl2Hb3Hlt3Hl'5Hlen'S2Hf2Hl2HbS2Hf2Hl3Hlt3Hl'5Hlen'S2Hf2Hl3Hlt3Hl'5Hlen'S2Hf2Hl2HkS2Hf2Hl1ES2Hf2Hl2NES2Hf2Hl3HltS2Hf2Hl3HltS2Hf2Hl2HbS2Hf2Hl2NE".
induction fuel as [|fuel IH]; intros fd iov st mo Hf Hl Hb; [lia|]. cbn [stdio_write_loop].
set (all := concat (map to_bytes iov)) in *. set (T := Z.of_nat (length all)) in *.
assert (Htot : iov_total iov = T). { unfold iov_total, zlength. subst T all. rewrite length_concat_to_bytes'. reflexivity. }
rewrite Htot.
assert (Hans : forall rsp mo' evs, stp (NWritev fd (map to_bytes iov)) mo rsp mo' evs ->
mo' = mo /\ exists k, 0 <= k <= T /\ (k = T \/ 1 <= k < T) /\ dec_writev T rsp = Some k /\
evs = map (WriteEv (Z_to_bv 64 fd)) (firstn (Z.to_nat k) all)).
{ intros rsp mo' evs Hst. apply st_sub in Hst; [|cbn; tauto]. pose proof (nstep_dec_writev fd (map to_bytes iov) mo rsp mo' evs ltac:(fold all T; lia) Hst) as (k & Hd & Hk & -> & ->).
fold all in Hd, Hk |- *. fold T in Hd, Hk. split; [reflexivity|]. exists k. split; [lia|]. split; [lia|]. split; [exact Hd| reflexivity]. }
assert (HstF : stp (NWritev fd (map to_bytes iov)) mo (eff0 (Z_to_bv 64 T)) mo (map (WriteEv (Z_to_bv 64 fd)) all)).
{ apply st_same; [cbn; tauto|]. cbn [nstep]. split; [reflexivity|]. fold all. fold T. destruct (Z.eqb_spec T 0) as [E|NE].
- split; [rewrite E; reflexivity|]. subst T. destruct all; [reflexivity| cbn in E; lia].
- exists T. split; [lia|]. split; [reflexivity|]. subst T. rewrite Nat2Z.id, firstn_all. reflexivity. }
assert (HdF : dec_writev T (eff0 (Z_to_bv 64 T)) = Some T).
{ unfold dec_writev, dec_count, dec_count0, eff0. rewrite unsigned_lit by lia. destruct (Z.eqb_spec T 0) as [E|NE].
- rewrite E. reflexivity.
- replace (1 <=? T) with true by (symmetry; apply Z.leb_le; lia). rewrite Z.leb_refl. reflexivity. }
exists (map (WriteEv (Z_to_bv 64 fd)) all), tt, st. split; [|split; [auto|split]].
- apply tpath_mbind_ok. exists (map (WriteEv (Z_to_bv 64 fd)) all), T, st, mo, []. split; [apply tpath_msys_ok; exists (eff0 (Z_to_bv 64 T)); auto|].
rewrite Z.eqb_refl, app_nil_r. split; [apply tpath_mret; auto| reflexivity].
- intros tr' x mo' Hp. apply tpath_mbind_any in Hp as [[Hp ->]|(tr1 & cnt & s1 & mo1 & tr2 & Hp1 & Hp2 & ->)].
+ exfalso. apply tpath_msys_any in Hp as (rsp & Hst & E). destruct (Hans _ _ _ Hst) as (_ & k & _ & _ & Hd & _). rewrite Hd in E. discriminate.
+ apply tpath_msys_ok in Hp1 as (rsp & Hst & Hd & ->). destruct (Hans _ _ _ Hst) as (-> & k & Hk & Hcase & Hd' & ->).
rewrite Hd in Hd'. injection Hd' as <-.
destruct (Z.eqb_spec cnt T) as [->|NE].
* apply tpath_mret in Hp2 as (-> & -> & ->). rewrite app_nil_r. subst T. rewrite Nat2Z.id, firstn_all. auto.
* destruct Hcase as [->|Hlt]; [congruence|].
destruct (iov_advance_concat iov cnt Hl ltac:(fold all T; rewrite <- length_concat_to_bytes'; fold all; lia)) as [Ec Hl'].
fold all in Ec.
assert (Hlen' : length (concat (map to_bytes (iov_advance iov cnt))) = (length all - Z.to_nat cnt)%nat).
{ rewrite Ec, length_skipn. reflexivity. }
destruct (IH fd (iov_advance iov cnt) st mo ltac:(rewrite Hlen'; lia) Hl' ltac:(rewrite Hlen'; lia)) as (trI & [] & sI & _ & [-> ->] & HuI & _).
destruct (HuI _ _ _ Hp2) as (-> & -> & ->). rewrite Ec, <- map_app, firstn_skipn. auto.
- intros tr' Hx. apply texit_mbind in Hx as [Hx|(tr1 & cnt & s1 & mo1 & tr2 & Hp1 & Hx2 & ->)].
+ exact (texit_msys_nonexit (NWritev fd (map to_bytes iov)) _ _ _ _ I Hx).
+ apply tpath_msys_ok in Hp1 as (rsp & Hst & Hd & ->). destruct (Hans _ _ _ Hst) as (-> & k & Hk & Hcase & Hd' & ->).
rewrite Hd in Hd'. injection Hd' as <-.
destruct (Z.eqb_spec cnt T) as [->|NE]; [exact Hx2|].
destruct Hcase as [->|Hlt]; [congruence|].
destruct (iov_advance_concat iov cnt Hl ltac:(fold all T; rewrite <- length_concat_to_bytes'; fold all; lia)) as [Ec Hl']. fold all in Ec.
assert (Hlen' : length (concat (map to_bytes (iov_advance iov cnt))) = (length all - Z.to_nat cnt)%nat).
{ rewrite Ec, length_skipn. reflexivity. }
destruct (IH fd (iov_advance iov cnt) st mo ltac:(rewrite Hlen'; lia) Hl' ltac:(rewrite Hlen'; lia)) as (trI & aI & sI & _ & _ & _ & HxI).
exact (HxI _ Hx2).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="st_sub st_same"] Lemma stdio_write_det : forall fd buf s (st : St) mo, zlength buf + zlength s <= WRITE_MAX ->
detio (stdio_write (St:=St) fd buf s st) mo (fun tr _ s' => s' = st /\ tr = map (WriteEv (Z_to_bv 64 fd)) (to_bytes (buf ++ s))).
Proof.
intros fd buf s st mo Hlen. unfold stdio_write.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>13546083599.1922466479674.1923094145225.1648155385697.1673936932.18   00000400=00>00F00GS2HlS4Hlen2HlSS4Hlen1HS".
destruct (Z.ltb_spec WRITE_MAX (zlength buf + zlength s)); [lia|].
set (iov := match buf with [] => [s] | _ :: _ => [buf; s] end).
assert (Hc : concat (map to_bytes iov) = to_bytes (buf ++ s)). { subst iov. destruct buf; cbn; rewrite ?app_nil_r, ?to_bytes_app; reflexivity. }
assert (Hl : (length iov <= 2)%nat) by (subst iov; destruct buf; cbn; lia).
rewrite <- Hc. apply stdio_write_loop_det; [| exact Hl|]; rewrite Hc, to_bytes_length, length_app; unfold zlength, WRITE_MAX in *; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Let upd_so := (upd_so get_so set_so).
Let rd_so := (rd_so (St:=St) get_so).
End StdioChar.
Local Open Scope list_scope. Local Open Scope Z_scope.
Definition diag_short (d : diag_msg) : Prop :=
match d with
| DUsage a | DCannotOpen a | DReadError a => zlength a <= PIECE_MAX
| _ => True
end.
Section IOS.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Hypothesis get_set : forall v s, get_so (set_so v s) = v.
Hypothesis set_set : forall v w s, set_so v (set_so w s) = set_so v s.
Hypothesis set_get : forall s, set_so (get_so s) s = s.
Context {stp : node -> Model -> resp -> Model -> list event -> Prop}.
Hypothesis st_sub : forall n mo r mo' e, ~ nf_node n -> stp n mo r mo' e -> nstep n mo r mo' e.
Hypothesis st_same : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> stp n mo r mo e.
Local Notation detio := (detio (stp:=stp)).
End IOS.
Section DetSim.
Context {StG StC : Type} (debtG : StG -> list event) (debtC : StC -> list event).
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
End DetSim.
Section StdioSim.
Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
Let d0 : St -> list event := fun _ => [].
Variable stepG : node -> Model -> resp -> Model -> list event -> Prop.
Hypothesis stepG_sub : forall n mo r mo' e, ~ nf_node n -> stepG n mo r mo' e -> nstep n mo r mo' e.
Hypothesis stepG_same : forall n mo r e, ~ nf_node n -> nstep n mo r mo e -> stepG n mo r mo e.
Variable R : rel St St.
Hypothesis HRget : forall sG moG sC moC, R sG moG sC moC -> get_so sG = get_so sC.
Hypothesis HRset : forall sG moG sC moC v, R sG moG sC moC -> R (set_so v sG) moG (set_so v sC) moC.
Local Notation fsimeq := (fsimeq d0 d0 stepG).
Local Notation fsim := (fsim d0 d0 stepG).
Let upd_so := (upd_so get_so set_so).
Let rd_so := (rd_so (St:=St) get_so).
End StdioSim.
