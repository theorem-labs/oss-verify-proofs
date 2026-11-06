(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AxSymExec3 AxSymExec3Sound.
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.
Import AX2. Import AX2S.
Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
match e with
| ELit _ => true
| EVar n => Nat.ltb n b
| EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
| EExt _ _ _ x => expr_vars_lt b x
| EBlob _ _ _ _ => true
end.
Definition saddr_vars_lt (b : nat) (a : saddr) : bool := expr_vars_lt b (a_base a).
Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.
Definition kentry_vars_lt (b : nat) (K : kentry) : bool :=
match K with
| KWord a _ v => saddr_vars_lt b a && expr_vars_lt b v
| KZero a n => saddr_vars_lt b a && expr_vars_lt b n
| KBlob a n _ => saddr_vars_lt b a && expr_vars_lt b n
| KImg _ _ => true
| KAlign e _ => expr_vars_lt b e
| KRange e _ _ => expr_vars_lt b e
| KWr a n => saddr_vars_lt b a && expr_vars_lt b n
| KDisj a1 n1 a2 n2 => saddr_vars_lt b a1 && expr_vars_lt b n1 && saddr_vars_lt b a2 && expr_vars_lt b n2
| KFill a n _ => saddr_vars_lt b a && expr_vars_lt b n
| KUnk a n => saddr_vars_lt b a && expr_vars_lt b n
end.
Fixpoint kn_vars_lt (b : nat) (kn : list kentry) : bool :=
match kn with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.
Definition env_agree (b : nat) (E E' : env) : Prop :=
(forall n, (n < b)%nat -> ev E n = ev E' n) /\ eb E = eb E'.
Lemma edenot_agree : forall b E E' e,
env_agree b E E' -> expr_vars_lt b e = true -> edenot E e = edenot E' e.
Proof.
intros b E E' e [Hv Hb]. induction e; cbn [expr_vars_lt edenot]; intros H;
repeat match goal with
| H : (_ && _)%bool = true |- _ => apply andb_prop in H; destruct H
end;
try reflexivity;
try (rewrite IHe1, IHe2 by assumption; reflexivity);
try (rewrite IHe by assumption; reflexivity).
- apply Nat.ltb_lt in H. apply Hv. exact H.
- rewrite Hb. reflexivity.
Qed.
Lemma adenot_agree : forall b E E' a,
env_agree b E E' -> saddr_vars_lt b a = true -> adenot E a = adenot E' a.
Proof.
intros b E E' a Ha H. unfold adenot. rewrite (edenot_agree b E E' _ Ha H). reflexivity.
Qed.
Lemma regs_ok_agree : forall b E E' sr regs,
env_agree b E E' -> sr_vars_lt b sr = true -> regs_ok E sr regs -> regs_ok E' sr regs.
Proof.
intros b E E' sr regs Ha Hsr HR r. rewrite (HR r).
unfold sr_get. destruct (bv_eqb r 0); [reflexivity|].
assert (Hnth : forall i, expr_vars_lt b (nth i sr (ELit 0)) = true).
{ clear HR r. induction sr as [|e t IH]; intros i.
- destruct i; reflexivity.
- cbn [sr_vars_lt] in Hsr. apply andb_prop in Hsr as [He Ht].
destruct i; [exact He | apply IH; exact Ht]. }
apply (edenot_agree b); [exact Ha | apply Hnth].
Qed.
Lemma flat_agree : forall b E E' a n,
env_agree b E E' -> saddr_vars_lt b a = true -> flat E a n <-> flat E' a n.
Proof.
intros b E E' a n Ha H. unfold flat, estart.
rewrite (edenot_agree b E E' (a_base a) Ha H). tauto.
Qed.
Lemma know_ok_agree : forall segs b E E' base kn,
env_agree b E E' -> kn_vars_lt b kn = true -> know_ok segs E base kn -> know_ok segs E' base kn.
Proof.
intros segs b E E' base kn Ha. induction kn as [|K r IH]; cbn [kn_vars_lt]; intros H Hk.
- constructor.
- apply andb_prop in H as [HK Hr]. apply Forall_cons_iff in Hk as [Hk1 Hk2].
constructor; [| apply IH; assumption].
destruct Ha as [Hv Hb].
destruct K as [a w v|a n|a n k|lo hi|ae am|re rlo rhi|wa wn|da1 dn1 da2 dn2|a n fc|a n]; cbn [kentry_vars_lt kentry_ok] in *;
[ | | | | rewrite <- (edenot_agree b E E' ae (conj Hv Hb) HK); exact Hk1
| rewrite <- (edenot_agree b E E' re (conj Hv Hb) HK); exact Hk1
| apply andb_prop in HK as [HK1 HK2]; unfold flat, estart, elenZ in *;
rewrite <- (edenot_agree b E E' (a_base wa) (conj Hv Hb) HK1), <- (edenot_agree b E E' wn (conj Hv Hb) HK2); exact Hk1
| apply andb_prop in HK as [HK HK4]; apply andb_prop in HK as [HK HK3]; apply andb_prop in HK as [HK1 HK2];
unfold estart, elenZ in *;
rewrite <- (edenot_agree b E E' (a_base da1) (conj Hv Hb) HK1), <- (edenot_agree b E E' dn1 (conj Hv Hb) HK2),
<- (edenot_agree b E E' (a_base da2) (conj Hv Hb) HK3), <- (edenot_agree b E E' dn2 (conj Hv Hb) HK4); exact Hk1
| | ].
+ apply andb_prop in HK as [H1 H2].
rewrite <- (adenot_agree b E E' a (conj Hv Hb) H1), <- (edenot_agree b E E' v (conj Hv Hb) H2).
destruct Hk1 as (A & B & C). split; [exact A|]. split; [|exact C].
apply (flat_agree b E E' a _ (conj Hv Hb) H1). exact B.
+ apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
destruct Hk1 as [A B]. split; [|exact B].
unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
+ apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *. rewrite <- Hb.
rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
destruct Hk1 as (A & B & C). split; [|split; [exact B | exact C]].
unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
+ exact Hk1.
+
apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
destruct Hk1 as [A B]. split; [|exact B].
unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
+
apply andb_prop in HK as [H1 H2]. unfold elenZ, estart in *.
rewrite <- (edenot_agree b E E' n (conj Hv Hb) H2), <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1).
destruct Hk1 as [A B]. split; [|exact B].
unfold flat, estart in *. rewrite <- (edenot_agree b E E' (a_base a) (conj Hv Hb) H1). exact A.
Qed.
Section Run.
Variable segs : list Segment.
#[using="Type"] Lemma st_ok_entry : forall E base rom pc sr kn nx regs,
regs_ok E sr regs -> know_ok segs E base kn ->
st_ok segs E base rom (SS pc sr [] kn nx) (mkst regs (Z_to_bv 64 pc) base rom).
Proof.
intros E base rom pc sr kn nx regs HR HK. exists regs. cbn [s_pc s_log s_regs s_know mem_denot].
split; [reflexivity|]. split; [exact HR|]. split; [exact I | exact HK].
Qed.
#[using="Type"] Lemma eagree_env_agree : forall b E E', eagree b E E' <-> env_agree b E E'.
Proof. intros b E E'. unfold eagree, env_agree. tauto. Qed.
#[using="Type"] Lemma st_okX_entry : forall E base rom pc sr kn nx regs,
regs_ok E sr regs -> know_ok segs E base kn ->
sr_vars_lt nx sr = true -> kn_vars_lt nx kn = true ->
forall E', eagree nx E E' -> st_ok segs E' base rom (SS pc sr [] kn nx) (mkst regs (Z_to_bv 64 pc) base rom).
Proof.
intros E base rom pc sr kn nx regs HR HK Hsr Hkn E' Ha. apply eagree_env_agree in Ha.
apply st_ok_entry.
- eapply regs_ok_agree; [exact Ha | exact Hsr | exact HR].
- eapply know_ok_agree; [exact Ha | exact Hkn | exact HK].
Qed.
#[using="Type"] Theorem runTX_sound : forall t K fuel stops pc sr kn nx E base rom regs,
itab_sound segs t ->
regs_ok E sr regs -> know_ok segs E base kn ->
sr_vars_lt nx sr = true -> kn_vars_lt nx kn = true ->
let ss' := sym_execTX segs t K fuel true stops (SS pc sr [] kn nx) in
exists E' R, env_agree nx E E'
/\ (nx <= s_next ss')%nat
/\ regs_ok E' (s_regs ss') R
/\ log_flat E' (s_log ss')
/\ know_ok segs E' base (s_know ss')
/\ msteps segs (mkst regs (Z_to_bv 64 pc) base rom)
(mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)
/\ (forall E'', env_agree (s_next ss') E' E'' ->
st_ok segs E'' base rom ss' (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E' base (s_log ss')) rom)).
Proof.
intros t K fuel stops pc sr kn nx E base rom regs Ht HR HK Hsr Hkn.
destruct (sym_execTX_ex segs t K fuel true stops (SS pc sr [] kn nx) E base rom _ Ht
(st_okX_entry E base rom pc sr kn nx regs HR HK Hsr Hkn)) as (E' & R & Ha & Hle & HR' & Hlf & HK' & Hms & HALL).
exists E', R. split; [apply eagree_env_agree; exact Ha|]. split; [exact Hle|].
split; [exact HR'|]. split; [exact Hlf|]. split; [exact HK'|]. split; [exact Hms|].
intros E'' Ha''. apply HALL. apply eagree_env_agree. exact Ha''.
Qed.
#[using="Type"] Lemma reg_val : forall E sr R (r : reg), regs_ok E sr R -> getr R r = edenot E (sr_get sr r).
Proof. intros E sr R r HR. apply HR. Qed.
#[using="Type"] Lemma regs_ok_set : forall E sr R (rd : reg) v e,
regs_ok E sr R -> rd <> 0%bv -> edenot E e = v ->
regs_ok E (sr_upd sr (ridx rd) e) (regupd R rd v).
Proof.
intros E sr R rd v e HR Hrd He.
pose proof (regs_ok_upd E sr R rd v e HR He) as H.
assert (Hb : bv_eqb rd 0 = false).
{ unfold bv_eqb. apply Z.eqb_neq. intros Hc. apply Hrd. apply bv_eq. exact Hc. }
rewrite Hb in H. exact H.
Qed.
End Run.
