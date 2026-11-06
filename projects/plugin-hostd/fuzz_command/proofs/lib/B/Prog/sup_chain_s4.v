(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the TAIL segment of sup_chain's walk on plugin-hostd/fuzz_command's ASan+UBSan
   build (fuzz_command.asan-ubsan), from the loop exit BASE + SCB_LEXIT = 0x8c444 to the return 0x8c558, against the
   interface lib/B/Prog/sup_chain_d.v (scb_lctx, scb_inv) and the helpers lib/B/Prog/sup_chain_aux.v. Statement from
   a Theorem Labs lane 707acd856cb (lib/B/Prog/sup_chain_c.v, tsup_chain_spec). The block bookkeeping of the post is the pure lemma
   scb4_final_blocks; the release segment 0x8c47c .. 0x8c558 is scb4_rel; scb_tail composes the four calls with both.

   The code: ld s2,8(s1) (the slot); arg_s(slot, list) 0x8c450; free(list) 0x8c458; rec_shape_of("chain", 5)
   0x8c468; answer(slot, shape, 1) 0x8c478 with this call's class-1 frame still live; then the inline release
   0x8c47c .. 0x8c4e4 (the magic 0x45e0360e at F, f5 at the frame's 16 shadow bytes, the flag byte through the word
   at F + 120), the epilogue (the saved registers back, sp := s0 - 192 + 192) and `ret`. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c rec_calls_free_c mix_call_c hand_back_c record_c arg_s_c rec_shape_of_c answer_c sup_chain_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts RecBLemmas sup_chain_aux sup_chain_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* a register's symbolic value in a symbolic state, without normalising the denotation (B_answer_code's preg) *)
Ltac preg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.

Ltac norm_ssp HS :=
lazymatch type of HS with
| st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
| st_ok _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS
end.

(* an address outside every write window of a symbolic memory *)
Ltac nwin_tac rwt :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rwt Hr | ]);
destruct Hin.

(* ---------- the block bookkeeping of sup_chain's B tail (pure list reasoning) ---------- *)
(* rs is the allocator's rounded size; SEP: two different live blocks do not overlap *)
Definition scb4_sep (rs : Z -> Z) (bl : list (Z * Z)) : Prop :=
forall b m p n, In (b, m) bl -> In (p, n) bl -> (b, m) <> (p, n) -> b + rs m <= p \/ p + rs n <= b.

Lemma scb4_pair_dec : forall x y : Z * Z, {x = y} + {x <> y}.
Proof. intros x y. decide equality; apply Z.eq_dec. Defined.

Lemma scb4_in_dec : forall (pn : Z * Z) l, {In pn l} + {~ In pn l}.
Proof. intros pn l. exact (in_dec scb4_pair_dec pn l). Defined.

Lemma scb4_perm_in : forall (l l' : list (Z * Z)) x, Permutation l l' -> In x l -> In x l'.
Proof. intros l l' x P H. eapply Permutation_in; [exact P | exact H]. Qed.

Lemma scb4_perm_nodup : forall (l l' : list (Z * Z)), Permutation l l' -> List.NoDup l -> List.NoDup l'.
Proof. intros l l' P H. eapply Permutation_NoDup; [exact P | exact H]. Qed.

(* a block apart from every block of l, with a positive size, is not in l *)
Lemma scb4_apart_notin : forall (a k : Z) (l : list (Z * Z)), 0 < k ->
Forall (fun qk => iv_apart a k (fst qk) (snd qk)) l -> ~ In (a, k) l.
Proof.
intros a k l Hk HF Hin. rewrite Forall_forall in HF. specialize (HF _ Hin).
unfold iv_apart in HF. cbn [fst snd] in HF. clear Hin. lia.
Qed.
(* a block answer frees: the recorder's block whose start is the old answer (answer_code.v:152-156) *)
Lemma scb4_in_filter : forall (old : Z) (l : list (Z * Z)) x,
In x (filter (fun pn : Z * Z => fst pn =? old) l) -> In x l.
Proof.
intros old l x. induction l as [|y l IH]; intros H; [cbn in H; contradiction|].
cbn in H. destruct (decide _) in H;
[destruct H as [<- | H]; [left; reflexivity | right; apply IH; exact H] | right; apply IH; exact H].
Qed.

(* the two parts of a duplicate-free list are disjoint *)
Lemma scb4_nodup_disj : forall (l l' : list (Z * Z)) x, List.NoDup (l ++ l') -> In x l -> ~ In x l'.
Proof.
induction l as [|a l IH]; intros l' x ND Hx Hx'; [destruct Hx|].
cbn [app] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [Ha ND'].
destruct Hx as [Ex|Hx].
- subst x. apply Ha. apply in_or_app. right. exact Hx'.
- exact (IH l' x ND' Hx Hx').
Qed.

(* two live blocks with the same start are the same block *)
Lemma scb4_same : forall (rs : Z -> Z) bl a k m, (forall m, 0 <= m -> 1 <= rs m /\ m <= rs m) ->
scb4_sep rs bl -> (forall b m, In (b, m) bl -> 0 <= m) -> In (a, k) bl -> In (a, m) bl -> (a, k) = (a, m).
Proof.
intros rs bl a k m Hrs S P Hk Hm. destruct (scb4_pair_dec (a, k) (a, m)) as [E|E]; [exact E|].
exfalso. pose proof (P a k Hk) as Pk. pose proof (P a m Hm) as Pm.
destruct (Hrs k Pk). destruct (Hrs m Pm). destruct (S a k a m Hk Hm E); clear Hrs S P Hk Hm E; lia.
Qed.

(* two different live blocks are apart, by their requested sizes *)
Lemma scb4_apart : forall (rs : Z -> Z) bl b m p n, (forall m, 0 <= m -> 1 <= rs m /\ m <= rs m) ->
scb4_sep rs bl -> (forall b m, In (b, m) bl -> 0 <= m) -> In (b, m) bl -> In (p, n) bl -> (b, m) <> (p, n) ->
iv_apart b m p n.
Proof.
intros rs bl b m p n Hrs S P Hb Hp E. pose proof (P b m Hb) as Pm. pose proof (P p n Hp) as Pn.
destruct (Hrs m Pm). destruct (Hrs n Pn). unfold iv_apart.
destruct (S b m p n Hb Hp E); clear Hrs S P Hb Hp E; lia.
Qed.

(* bl0: the live blocks at the entry, O the recorder's; record() frees Frec, leaving bl1; xmalloc makes (lst, nl), two
   arg_s calls make (p1, m1) and (p2, m2) (blL), a third makes (p3, n3) (blA3); free(lst) and rec_shape_of leave blS;
   answer frees the old answer (start old) and makes (q1, n) (the recorder's) and (q2, n) (the caller's): bl' / O' *)
Lemma scb4_final_blocks : forall (rs : Z -> Z) (bl0 bl1 Frec O O1 blL blA3 l1 l2 blS bl' O' : list (Z * Z))
  (lst nl p1 m1 p2 m2 p3 n3 old q1 q2 n : Z),
(forall m, 0 <= m -> 1 <= rs m /\ m <= rs m) ->
(forall pn, In pn O -> In pn bl0) ->
List.NoDup bl0 ->
Permutation bl0 (bl1 ++ Frec) ->
(forall pn, In pn Frec -> In pn O) ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn Frec) ->
Permutation blL ((p2, m2) :: (p1, m1) :: (lst, nl) :: bl1) ->
Forall (fun qk => iv_apart lst nl (fst qk) (snd qk)) bl1 ->
Forall (fun qk => iv_apart p1 m1 (fst qk) (snd qk)) ((lst, nl) :: bl1) ->
Forall (fun qk => iv_apart p2 m2 (fst qk) (snd qk)) ((p1, m1) :: (lst, nl) :: bl1) ->
0 < nl -> 0 < m1 -> 0 < m2 -> 0 < n3 ->
Permutation blA3 ((p3, n3) :: blL) ->
Forall (fun qk => iv_apart p3 n3 (fst qk) (snd qk)) blL ->
blA3 = l1 ++ (lst, nl) :: l2 -> List.NoDup blA3 ->
Permutation blS (l1 ++ l2) ->
(forall pn, In pn blS -> fst pn = old -> In pn ((p3, n3) :: (p2, m2) :: (p1, m1) :: O1)) ->
(forall pn, In pn blS -> fst pn <> old -> pn <> (q1, n) /\ pn <> (q2, n)) ->
q1 <> q2 ->
(forall pn, In pn bl' <-> (In pn blS /\ fst pn <> old) \/ pn = (q1, n) \/ pn = (q2, n)) ->
(forall pn, In pn O' <-> (In pn ((p3, n3) :: (p2, m2) :: (p1, m1) :: O1) /\ fst pn <> old) \/ pn = (q1, n)) ->
scb4_sep rs bl' -> (forall b m, In (b, m) bl' -> 0 <= m) ->
(forall pn, In pn O' -> In pn O \/ ~ In pn bl0) /\
In (q2, n) bl' /\
(forall pn, In pn bl0 -> ~ In pn O -> pn <> (q2, n)) /\
~ In q2 (map fst O') /\
(forall pn, In pn bl0 -> ~ In pn O -> In pn bl' /\ iv_apart (fst pn) (snd pn) q2 n) /\
(forall pn, In pn bl' -> (In pn bl0 /\ ~ In pn O) \/ In pn O' \/ pn = (q2, n)).
Proof.
intros rs bl0 bl1 Frec O O1 blL blA3 l1 l2 blS bl' O' lst nl p1 m1 p2 m2 p3 n3 old q1 q2 n
  Hrs HOb ND0 P0 HFO HO1 PL Alst Ap1 Ap2 Hnl Hm1 Hm2 Hn3 PA3 Ap3 Esp NDA3 PS Hold Hfr Hq12 HB' HO' SB PB.
(* record(): bl1 and Frec split bl0 without overlap *)
assert (ND1 : List.NoDup (bl1 ++ Frec)) by exact (scb4_perm_nodup _ _ P0 ND0).
assert (B10 : forall pn, In pn bl1 -> In pn bl0).
{ intros pn H. apply (scb4_perm_in _ _ pn (Permutation_sym P0)). apply in_or_app. left. exact H. }
assert (B1F : forall pn, In pn bl1 -> ~ In pn Frec) by (intros pn H; exact (scb4_nodup_disj bl1 Frec pn ND1 H)).
assert (B0 : forall pn, In pn bl0 -> In pn bl1 \/ In pn Frec).
{ intros pn H. apply in_app_or. exact (scb4_perm_in _ _ pn P0 H). }
(* a block live at the entry and not the recorder's survives record() *)
assert (B01 : forall pn, In pn bl0 -> ~ In pn O -> In pn bl1).
{ intros pn H HnO. destruct (B0 pn H) as [H1|H1]; [exact H1 | exfalso; exact (HnO (HFO _ H1))]. }
(* the members of blL and blA3 *)
assert (LL : forall pn, In pn ((p2, m2) :: (p1, m1) :: (lst, nl) :: bl1) -> In pn blL)
  by (intros pn H; exact (scb4_perm_in _ _ pn (Permutation_sym PL) H)).
assert (L1 : forall pn, In pn bl1 -> In pn blL).
{ intros pn H. apply LL. right. right. right. exact H. }
assert (AA : forall pn, In pn ((p3, n3) :: blL) -> In pn blA3)
  by (intros pn H; exact (scb4_perm_in _ _ pn (Permutation_sym PA3) H)).
(* the new blocks are not in bl1, and are not the text block *)
assert (Nlst : ~ In (lst, nl) bl1) by exact (scb4_apart_notin lst nl bl1 Hnl Alst).
assert (Np1 : ~ In (p1, m1) bl1).
{ intros H. apply (scb4_apart_notin p1 m1 ((lst, nl) :: bl1) Hm1 Ap1). right. exact H. }
assert (Np2 : ~ In (p2, m2) bl1).
{ intros H. apply (scb4_apart_notin p2 m2 ((p1, m1) :: (lst, nl) :: bl1) Hm2 Ap2). right. right. exact H. }
assert (Np3 : ~ In (p3, n3) bl1).
{ intros H. exact (scb4_apart_notin p3 n3 blL Hn3 Ap3 (L1 _ H)). }
assert (Ep1 : (p1, m1) <> (lst, nl)).
{ intros E. apply (scb4_apart_notin p1 m1 ((lst, nl) :: bl1) Hm1 Ap1). rewrite E. apply in_eq. }
assert (Ep2 : (p2, m2) <> (lst, nl)).
{ intros E. apply (scb4_apart_notin p2 m2 ((p1, m1) :: (lst, nl) :: bl1) Hm2 Ap2). rewrite E.
  apply in_cons. apply in_eq. }
assert (Ep3 : (p3, n3) <> (lst, nl)).
{ intros E. apply (scb4_apart_notin p3 n3 blL Hn3 Ap3). rewrite E. apply LL. apply in_cons. apply in_cons.
  apply in_eq. }
(* free(lst) and rec_shape_of: blA3 without the text block is blS *)
assert (AS : forall pn, In pn blA3 -> pn <> (lst, nl) -> In pn blS).
{ intros pn H E. rewrite Esp in H. apply (scb4_perm_in _ _ pn (Permutation_sym PS)).
  apply in_app_or in H. apply in_or_app. destruct H as [H|[H|H]].
  - left. exact H.
  - exfalso. exact (E (eq_sym H)).
  - right. exact H. }
assert (NLS : ~ In (lst, nl) (l1 ++ l2)) by (apply List.NoDup_remove_2; rewrite <- Esp; exact NDA3).
assert (SA : forall pn, In pn blS -> In pn ((p3, n3) :: (p2, m2) :: (p1, m1) :: bl1)).
{ intros pn H. pose proof (scb4_perm_in _ _ pn PS H) as H1.
  assert (Hne : pn <> (lst, nl)) by (intros E; subst pn; exact (NLS H1)).
  assert (H2 : In pn blA3).
  { rewrite Esp. apply in_app_or in H1. apply in_or_app.
    destruct H1 as [H1|H1]; [left; exact H1 | right; right; exact H1]. }
  apply (scb4_perm_in _ _ pn PA3) in H2. destruct H2 as [E|H2]; [left; exact E|].
  apply (scb4_perm_in _ _ pn PL) in H2. destruct H2 as [E|[E|[E|H2]]].
  - right. left. exact E.
  - right. right. left. exact E.
  - exfalso. exact (Hne (eq_sym E)).
  - right. right. right. exact H2. }
(* the recorder's list at answer's entry lies in blS *)
assert (OAS : forall pn, In pn ((p3, n3) :: (p2, m2) :: (p1, m1) :: O1) -> In pn blS).
{ intros pn H. destruct H as [E|[E|[E|H]]].
  - subst pn. apply AS; [apply AA; left; reflexivity | exact Ep3].
  - subst pn. apply AS; [apply AA; right; apply LL; left; reflexivity | exact Ep2].
  - subst pn. apply AS; [apply AA; right; apply LL; right; left; reflexivity | exact Ep1].
  - apply (proj1 (HO1 pn)) in H. destruct H as [HO HnF].
    assert (H1 : In pn bl1).
    { destruct (B0 pn (HOb pn HO)) as [H1|H1]; [exact H1 | exfalso; exact (HnF H1)]. }
    apply AS; [apply AA; right; exact (L1 pn H1) | intros E; subst pn; exact (Nlst H1)]. }
(* a block kept by record() and not the recorder's is not in the recorder's list *)
assert (KEPT : forall pn, In pn bl1 -> ~ In pn O -> ~ In pn ((p3, n3) :: (p2, m2) :: (p1, m1) :: O1)).
{ intros pn H1 HnO H. destruct H as [E|[E|[E|H]]].
  - subst pn. exact (Np3 H1).
  - subst pn. exact (Np2 H1).
  - subst pn. exact (Np1 H1).
  - exact (HnO (proj1 (proj1 (HO1 pn) H))). }
(* such a block reaches blS, with a start other than the old answer's *)
assert (KS : forall pn, In pn bl1 -> ~ In pn O -> In pn blS /\ fst pn <> old).
{ intros pn H1 HnO.
  assert (HS : In pn blS).
  { apply AS; [apply AA; right; exact (L1 pn H1) | intros E; subst pn; exact (Nlst H1)]. }
  split; [exact HS|]. intros E. exact (KEPT pn H1 HnO (Hold pn HS E)). }
(* a block of the recorder's list live at the entry is the recorder's *)
assert (OAO : forall pn, In pn ((p3, n3) :: (p2, m2) :: (p1, m1) :: O1) -> In pn bl0 -> In pn O).
{ intros pn H H0. destruct (scb4_in_dec pn O) as [HO|HnO]; [exact HO|].
  exfalso. exact (KEPT pn (B01 pn H0 HnO) HnO H). }
assert (Hq2 : In (q2, n) bl') by (apply (proj2 (HB' (q2, n))); right; right; reflexivity).
split.
{ intros pn Hpn. apply (proj1 (HO' pn)) in Hpn.
  destruct (scb4_in_dec pn bl0) as [H0|H0]; [left | right; exact H0].
  destruct Hpn as [[Hpn _] | E]; [exact (OAO pn Hpn H0)|].
  subst pn. destruct (scb4_in_dec (q1, n) O) as [HO|HnO]; [exact HO | exfalso].
  destruct (KS _ (B01 _ H0 HnO) HnO) as [HS Hne].
  exact (proj1 (Hfr _ HS Hne) eq_refl). }
split; [exact Hq2|].
split.
{ intros pn H0 HnO E. destruct (KS pn (B01 pn H0 HnO) HnO) as [HS Hne].
  exact (proj2 (Hfr pn HS Hne) E). }
split.
{ intros Hm. apply in_map_iff in Hm. destruct Hm as ([a k] & Ea & Hk). cbn [fst] in Ea. subst a.
  apply (proj1 (HO' (q2, k))) in Hk. destruct Hk as [[Hk Hne] | Hk].
  - pose proof (OAS _ Hk) as HS.
    assert (HkB : In (q2, k) bl') by (apply (proj2 (HB' (q2, k))); left; split; [exact HS | exact Hne]).
    pose proof (scb4_same rs bl' q2 k n Hrs SB PB HkB Hq2) as E.
    exact (proj2 (Hfr _ HS Hne) E).
  - injection Hk as E1 E2. exact (Hq12 (eq_sym E1)). }
split.
{ intros pn H0 HnO. destruct (KS pn (B01 pn H0 HnO) HnO) as [HS Hne].
  assert (HpB : In pn bl') by (apply (proj2 (HB' pn)); left; split; assumption).
  split; [exact HpB|].
  destruct pn as [a k]. cbn [fst snd].
  apply (scb4_apart rs bl' a k q2 n Hrs SB PB HpB Hq2).
  exact (proj2 (Hfr _ HS Hne)). }
intros pn Hpn. apply (proj1 (HB' pn)) in Hpn. destruct Hpn as [[HS Hne] | [E | E]].
- assert (HinO' : In pn ((p3, n3) :: (p2, m2) :: (p1, m1) :: O1) -> In pn O')
    by (intros H; apply (proj2 (HO' pn)); left; split; [exact H | exact Hne]).
  pose proof (SA pn HS) as H. destruct H as [E|[E|[E|H1]]].
  + right. left. apply HinO'. left. exact E.
  + right. left. apply HinO'. right. left. exact E.
  + right. left. apply HinO'. right. right. left. exact E.
  + destruct (scb4_in_dec pn O) as [HO|HnO].
    * right. left. apply HinO'. right. right. right. apply (proj2 (HO1 pn)).
      split; [exact HO | exact (B1F pn H1)].
    * left. split; [exact (B10 pn H1) | exact HnO].
- right. left. apply (proj2 (HO' pn)). right. exact E.
- right. right. exact E.
Qed.
(* a block of the recorder's list at answer's entry that was live at the function's entry is the recorder's *)
Lemma scb4_OA_O : forall (bl0 bl1 Frec O O1 blL : list (Z * Z)) (lst nl p1 m1 p2 m2 p3 n3 : Z),
Permutation bl0 (bl1 ++ Frec) -> (forall pn, In pn Frec -> In pn O) ->
(forall pn, In pn O1 <-> In pn O /\ ~ In pn Frec) ->
Permutation blL ((p2, m2) :: (p1, m1) :: (lst, nl) :: bl1) ->
Forall (fun qk => iv_apart p1 m1 (fst qk) (snd qk)) ((lst, nl) :: bl1) ->
Forall (fun qk => iv_apart p2 m2 (fst qk) (snd qk)) ((p1, m1) :: (lst, nl) :: bl1) ->
0 < m1 -> 0 < m2 -> 0 < n3 ->
Forall (fun qk => iv_apart p3 n3 (fst qk) (snd qk)) blL ->
forall pn, In pn ((p3, n3) :: (p2, m2) :: (p1, m1) :: O1) -> In pn bl0 -> In pn O.
Proof.
intros bl0 bl1 Frec O O1 blL lst nl p1 m1 p2 m2 p3 n3 P0 HFO HO1 PL Ap1 Ap2 Hm1 Hm2 Hn3 Ap3 pn Hpn H0.
assert (B0 : In pn bl1 \/ In pn Frec) by (apply in_app_or; exact (scb4_perm_in _ _ pn P0 H0)).
destruct B0 as [H1 | HF]; [| exact (HFO pn HF)].
destruct Hpn as [E | [E | [E | H]]].
- subst pn. exfalso. apply (scb4_apart_notin p3 n3 blL Hn3 Ap3).
  apply (scb4_perm_in _ _ _ (Permutation_sym PL)). right. right. right. exact H1.
- subst pn. exfalso. apply (scb4_apart_notin p2 m2 _ Hm2 Ap2). right. right. exact H1.
- subst pn. exfalso. apply (scb4_apart_notin p1 m1 _ Hm1 Ap1). right. exact H1.
- exact (proj1 (proj1 (HO1 pn) H)).
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses this segment uses (lib/B/Prog/sup_chain_c.v, a Theorem Labs lane 707acd856cb) *)
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TREC_SHAPE_OF : forall fx0 : YK11.FPState, @trec_shape_of_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis VOBJS : cmd_val_objs.
(* the walk's hypotheses (a Theorem Labs lane convention, model lib/B/Prog/sup_reset.v:302-337) *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTLF : ameter_fs_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis cmd_palib : forall B0, CmdBSyms B0 -> PALib B0.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let TL : PALib B := cmd_palib B HB.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let CMD_RO_IN : cmd_ro_in (in_roP SEGS RLO RHI) := CmdRecRo.CMD_RO_IN (SK := SK) SEGS B LAWS HB IMG.
Let cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC :=
  CmdRecRest.cmd_ro_prog_apart (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem) :=
  CmdRecRo.cmd_ro_ok_of_aro (SK := SK) SEGS B LAWS HB IMG.
Let cmd_rodata_kept : forall ly S (W : world SEGS) mem md ly' S' (W' : world SEGS) mem' md' STK sp0 FP own k,
  AR SEGS B ly S W mem md ->
  ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall a, inFP FP a -> Exists (in_zr a) TFIB_PROG_STATIC \/
     exists b n, In (b, n) (ablocks B ly S ++ ablocks B ly' S') /\ b <= a < b + req_size n) ->
  arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem') :=
  CmdRecRest.cmd_rodata_kept (SK := SK) SEGS B LAWS HB IMG.
Let RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a := cif_relro_img SEGS B IMG.
Let ROB : ro_below_ofl SEGS RLO RHI := cif_ro_below_ofl SEGS B IMG.
Lemma scb4_region_kept_hi2 : forall E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview SEGS H2 m2 a = aview SEGS H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept SEGS E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- intros _. apply (apresent_writable SEGS). apply Hp. exact Ha.
Qed.

(* ---------- the recorder's state survives writes outside g_rec, record.spill and its own blocks ----------
   (lib/B/Prog/answer_code.v:305-429, :441-469, verbatim) *)
Lemma aval_mem8_eq : forall rd a v1 v2, aval_mem rd a 8 v1 -> aval_mem rd a 8 v2 ->
0 <= v1 < 2 ^ 64 -> 0 <= v2 < 2 ^ 64 -> v1 = v2.
Proof.
intros rd a v1 v2 H1 H2 Bd1 Bd2.
assert (E : forall k, (k < 8)%nat -> YG0f.le_byte v1 8 k = YG0f.le_byte v2 8 k).
{ intros k Hk. pose proof (H1 k Hk) as X1. rewrite (H2 k Hk) in X1. injection X1 as X. symmetry. exact X. }
rewrite <- (le_bytes8 v1 Bd1), <- (le_bytes8 v2 Bd2).
rewrite (E 0%nat), (E 1%nat), (E 2%nat), (E 3%nat), (E 4%nat), (E 5%nat), (E 6%nat), (E 7%nat) by lia. reflexivity.
Qed.
Lemma aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma acall_at_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.
Lemma rec_repA_in : forall ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros ly S rd R O (Q & HA & HO) pn Hpn. apply HO in Hpn. unfold lay_blocks in Hpn.
destruct HA as (_ & _ & _ & (Hc1 & Hc2 & _ & Hc4 & Hsp & _) & Ha & Hr & _ & _).
apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]; [|apply in_app_iff in Hpn as [Hpn | Hpn]]].
- apply in_concat in Hpn as (P & HP & Hin). apply In_nth_error in HP as (i & Hi).
destruct (nth_error (r_calls R) i) as [c|] eqn:Hc.
+ destruct (Hc4 i c P Hc Hi) as ((_ & _ & HL & _ & _ & _ & H7) & _).
apply In_nth_error in Hin as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Hs.
* exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
* exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some P k) ltac:(rewrite Hk; discriminate)). lia.
+ exfalso. apply nth_error_None in Hc. pose proof (proj1 (nth_error_Some (l_calls Q) i) ltac:(rewrite Hi; discriminate)). lia.
- destruct Hsp as (_ & _ & HL & _ & _ & _ & H7). apply In_nth_error in Hpn as (k & Hk).
destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs.
+ exact (proj1 (proj2 (proj2 (H7 k s pn Hs Hk)))).
+ exfalso. apply nth_error_None in Hs. pose proof (proj1 (nth_error_Some (l_spill Q) k) ltac:(rewrite Hk; discriminate)). lia.
- unfold aanswer_at in Ha. destruct (r_answer R), (l_answer Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 Ha))).
- unfold areply_at in Hr. destruct (r_reply R), (l_reply Q) as [q|]; cbn in Hpn; try contradiction; try tauto.
destruct Hpn as [<- | []]. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hr))))).
Qed.
Lemma rec_repA_kept : forall ly S rd ly' S' rd' R O, rec_repA B ly S rd R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
(forall a, A_G_REC <= a < A_G_REC + 960 -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + 56 -> rd' a = rd a) ->
(forall p n i, In (p, n) O -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
rec_repA B ly' S' rd' R O.
Proof.
intros ly S rd ly' S' rd' R O (Q & HA & HO) Hbl Hg Hs Hb. exists Q. split; [|exact HO].
assert (HblQ : forall pn, In pn (lay_blocks Q) -> In pn (ablocks B ly' S')) by (intros pn Hpn; apply Hbl, HO, Hpn).
assert (HbQ : forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
by (intros [p n] i Hpn Hi; apply (Hb p n i (proj2 (HO (p, n)) Hpn) Hi)).
unfold lay_blocks in HblQ, HbQ.
destruct HA as (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & Ha & Hr & (S1 & S2 & S3 & S4 & S5 & S6) & Hown).
unfold arep_at, ag1_calls, ag1_scalars, aanswer_at, areply_at in *.
unfold OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_REPLY, OFF_REPLY_SIZE, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST, CALL_SIZE in *.
split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
split.
{ split; [exact C1|]. split; [exact C2|].
split; [apply (aval_mem_kept rd); [exact C3 | intros k Hk; apply Hg; lia]|].
split.
- intros i c P Hc Hp. destruct (C4 i c P Hc Hp) as [HC HF]. split; [|exact HF].
pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Hc; discriminate)) as Hi.
pose proof HC as (_ & HL6 & _).
apply (acall_at_kept (ablocks B ly S) _ rd); [exact HC | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
+ intros j Hj. rewrite <- !Z.add_assoc. apply Hg. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. left. apply in_concat. exists P. split; [exact (nth_error_In _ _ Hp) | exact Hpn].
- split; [|exact C6].
pose proof C5 as (_ & HL6 & _).
apply (acall_at_kept (ablocks B ly S) _ rd); [exact C5 | | |].
+ intros pn Hpn. apply HblQ. apply in_app_iff. right. apply in_app_iff. left. exact Hpn.
+ intros j Hj. apply Hs. unfold CALL_OFF_ARGS in Hj. lia.
+ intros pn j Hpn Hj. apply HbQ; [|exact Hj]. apply in_app_iff. right. apply in_app_iff. left. exact Hpn. }
split.
{ destruct (r_answer R) as [x|], (l_answer Q) as [q|]; try contradiction.
- destruct Ha as (A1 & A2 & A3 & A4 & A5 & A6).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (Some q) ++ oblk (l_reply Q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [exact A2|]. split; [apply HblQ; exact Hq|]. split; [exact A4|].
split; [apply (rastr_kept rd); [exact A5 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A6].
- apply (aval_mem_kept rd); [exact Ha | intros k Hk; apply Hg; lia]. }
split.
{ destruct (r_reply R) as [x|], (l_reply Q) as [q|]; try contradiction.
- destruct Hr as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (Hq : In q (concat (l_calls Q) ++ l_spill Q ++ oblk (l_answer Q) ++ oblk (Some q)))
by (apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; right; left; reflexivity).
split; [apply (aval_mem_kept rd); [exact A1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact A2 | intros k Hk; apply Hg; lia]|].
split; [exact A3|]. split; [exact A4|]. split; [apply HblQ; exact Hq|]. split; [exact A6|].
split; [apply (rabytes_kept rd); [exact A7 | intros i Hi; apply HbQ; [exact Hq | lia]] | exact A8].
- destruct Hr as [A1 A2]. split; apply (aval_mem_kept rd); first [exact A1 | exact A2 | intros k Hk; apply Hg; lia]. }
split; [|exact Hown].
split; [apply (aval_mem_kept rd); [exact S1 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S2 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S3 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S4 | intros k Hk; apply Hg; lia]|].
split; [apply (aval_mem_kept rd); [exact S5 | intros k Hk; apply Hg; lia]|].
exact S6.
Qed.
Lemma old_in_O : forall ly S (W : world SEGS) mem md R O old pn, AR SEGS B ly S W mem md ->
rec_repA B ly S (rdW W mem) R O ->
aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 old -> 0 <= old < 2 ^ 64 ->
In pn (ablocks B ly S) -> fst pn = old -> In pn O.
Proof.
intros ly S W mem md R O old [p nn] HAR HREP HOLD Hold Hpn Hfst. cbn [fst] in Hfst. subst p.
pose proof HREP as (Q & HA & HO).
destruct HA as (_ & _ & _ & _ & Ha & _). unfold aanswer_at in Ha.
destruct (al_blocks _ _ LAWS _ _ _ _ _ old nn HAR Hpn) as (_ & Hp4096 & Hpc & _ & _ & _ & Hn).
pose proof alloc_ceiling_lt as Hac.
destruct (r_answer R) as [x|], (l_answer Q) as [[q m]|] eqn:EQ; try contradiction.
- destruct Ha as (A1 & A2 & A3 & _). cbn [fst snd] in *.
destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HAR A3) as (_ & Hq4096 & Hqc & _ & _ & _ & Hm).
assert (Rq : 0 <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
assert (Eq : q = old) by (apply (aval_mem8_eq _ _ q old A1 HOLD); [lia | exact Hold]). subst q.
assert (HqO : In (old, m) O).
{ apply HO. unfold lay_blocks. rewrite EQ. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left. left. reflexivity. }
destruct (Z.eq_dec nn m) as [<- | Nnm]; [exact HqO|].
assert (Ne : (old, nn) <> (old, m)) by (intros E; injection E; lia).
exfalso. pose proof (sep_blocks SEGS B LAWS ly S W mem md old nn old m HAR Hpn A3 Ne) as Hd.
unfold zdisjoint, req_size in Hd. cbn [fst snd] in Hd. destruct (Z.eqb_spec nn 0), (Z.eqb_spec m 0); lia.
- assert (E0 : old = 0) by (apply (aval_mem8_eq _ _ old 0 HOLD Ha); lia). lia.
Qed.
(* ---------- the frame-flag law (a Theorem Labs lane's CmdRecRest.cmd_frame_flag_law is stated at tfibsegs, so it is named here) ---------- *)
Hypothesis cmd_frame_flag_law : forall B0, frame_flag_lawP SEGS B0.
Let FFL : frame_flag_lawP SEGS B := cmd_frame_flag_law B.

Lemma scb4_rdword_kept : forall (W : world SEGS) (m m' : word -> option byte) a v, 0 <= v < 2 ^ 64 ->
rdword (rdW W m) a = Some v -> (forall i, 0 <= i < 8 -> rdW W m' (a + i) = rdW W m (a + i)) ->
rdword (rdW W m') a = Some v.
Proof.
intros W m m' a v Hv Hr Hk.
apply (rdword_of_val_mem SEGS); [|exact Hv].
apply (recb_val_mem_frame_m (w_H W) (w_H W) m m' a 8%nat v); [exact (val_mem_of_rdword SEGS _ _ _ _ Hr) | exact Hk].
Qed.

(* the recorder's answer pointer, and the block it points at (lib/A/Prog/sup_chain_s6.v sc6_repA_answer) *)
Lemma scb4_repA_answer : forall ly S rd R O, rec_repA B ly S rd R O ->
exists old, aval_mem rd (A_G_REC + OFF_ANSWER) 8 old /\ (old = 0 \/ exists pn, In pn O /\ fst pn = old).
Proof.
intros ly S rd R O (Q & HQ & HO).
destruct HQ as (_ & _ & _ & _ & HAn & _).
unfold aanswer_at in HAn.
destruct (r_answer R) as [x|] eqn:Ea; destruct (l_answer Q) as [pn|] eqn:Eq; try contradiction.
- destruct HAn as (N1 & _). exists (fst pn). split; [exact N1|]. right. exists pn. split; [|reflexivity].
  apply HO. unfold lay_blocks. rewrite Eq. cbn [oblk].
  apply in_or_app. right. apply in_or_app. right. apply in_or_app. left. left. reflexivity.
- exists 0. split; [exact HAn | left; reflexivity].
Qed.
(* a string argument survives a change of its bytes' reader that keeps those bytes *)
Lemma scb4_argA_keep : forall ly S (rd rd' : reader) ro O p x,
astr_argA B ly S rd ro O p (Some x) ->
(forall i, 0 <= i < Z.of_nat (length x) + 1 -> rd' (p + i) = rd (p + i)) ->
astr_argA B ly S rd' ro O p (Some x).
Proof.
intros ly S rd rd' ro O p x (H0 & Hs & Hl & Har) K.
split; [exact H0|]. split; [apply (rastr_kept rd); [exact Hs | exact K]|]. split; [exact Hl | exact Har].
Qed.
(* the bytes of a string argument lie below the allocator's ceiling *)
Lemma scb4_argA_lo : forall ly S (W : world SEGS) mem md (rd : reader) O p x, AR SEGS B ly S W mem md ->
astr_argA B ly S rd (in_roP SEGS RLO RHI) O p (Some x) ->
forall i, 0 <= i < Z.of_nat (length x) + 1 -> 0 <= p + i < alloc_ceiling.
Proof.
intros ly S W mem md rd O p x HAR (H0 & Hs & Hl & Har) i Hi.
pose proof asan_consts as (CA1 & _).
destruct Har as [((q & k & Hin & Hq1 & Hq2) & _) | (Hro & _)].
- destruct (al_blocks _ _ LAWS ly S W mem md q k HAR Hin) as (_ & Hq4096 & Hqc & _ & _ & _ & Hk0).
  pose proof (req_size_pos k ltac:(lia)) as [Rk1 Rk2]. lia.
- destruct (Hro i Hi) as (Hr & _ & _). destruct (cmd_ro_prog_apart _ Hr) as [Himg _].
  pose proof (pa_segs_low _ Himg) as Hlo. unfold kLowMemEnd in Hlo. lia.
Qed.
Lemma scb4_fits : fits (shape_of scb_verb).
Proof. unfold fits. apply Z.leb_le. vm_compute. reflexivity. Qed.
(* the call record() recorded lies in the slot rec_slot (answer_c's slot premise) *)
Lemma scb4_entry : forall (R0 : rstate) fn (A : list (list byte)),
(exists k, nth_error (r_calls (rec_record R0 fn A)) k = Some (fn, A) /\
   rec_slot R0 = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
(rec_slot R0 = A_REC_SPILL /\ (fn, A) = r_spill (rec_record R0 fn A)).
Proof.
intros R0 fn A. unfold rec_record, rec_slot.
destruct (Nat.ltb (length (r_calls R0)) 16) eqn:Ek.
- left. exists (length (r_calls R0)). split; [|reflexivity].
  cbn [r_calls set_calls]. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
- right. split; reflexivity.
Qed.
(* ---------- the symbolic state at the loop exit 0x8c444 ---------- *)
(* the atoms above the registers: the 13 saved registers' entry values (atoms 32 .. 44), the slot (45), the class-1
   frame F (46), its shadow address SB + F / 8 (47) and its flag address (48) *)
Definition scb4_ext (regs : bvmap 5 word) (c F FL : Z) : list word :=
map (fun r => getr regs (Z_to_bv 5 r)) scb_saved ++ map (Z_to_bv 64) [c; F; SB + F / 8; FL].
(* the saved registers at entry sp - 8 - 8j, read-only here (the epilogue only loads them) *)
Definition scb4_saveR : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 (-104) 0
[YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk (-16) (CVal 8 (SOff 33 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 34 0)); YP09.mkChunk (-32) (CVal 8 (SOff 35 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-48) (CVal 8 (SOff 37 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 38 0)); YP09.mkChunk (-64) (CVal 8 (SOff 39 0));
 YP09.mkChunk (-72) (CVal 8 (SOff 40 0)); YP09.mkChunk (-80) (CVal 8 (SOff 41 0));
 YP09.mkChunk (-88) (CVal 8 (SOff 42 0)); YP09.mkChunk (-96) (CVal 8 (SOff 43 0));
 YP09.mkChunk (-104) (CVal 8 (SOff 44 0))].
(* the own stack words the tail reads: the slot at sp1 + 8, the frame at sp1 + 16 and sp1 + 32, its shadow at
   sp1 + 24 *)
Definition scb4_wordsR : YP09.region := YP09.mkRegion (Some 9%nat) 8 40 8 8
[YP09.mkChunk 8 (CVal 8 (SOff 45 0)); YP09.mkChunk 16 (CVal 8 (SOff 46 0));
 YP09.mkChunk 24 (CVal 8 (SOff 47 0)); YP09.mkChunk 32 (CVal 8 (SOff 46 0))].
(* the frame's flag word (read at 0x8c4dc, in the release segment; carried across the calls here) *)
Definition scb4_flgR : YP09.region := YP09.mkRegion (Some 46%nat) 120 128 120 120
[YP09.mkChunk 120 (CVal 8 (SOff 48 0))].
Definition scb4_facts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46 - 256) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
         (9%nat, mkAF (2 ^ 46 - 256) (2 ^ 47) 5); (46%nat, HPTR 5)] [] [].
Definition scb4_ss : sstate := mkSS SCB_LEXIT sr_atoms [scb4_saveR; scb4_wordsR; scb4_flgR] None scb4_facts.

Lemma scb4_seed : forall (fxv : YK11.FPState) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (regsc regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (fpos c : Z),
AR SEGS B lyc Sc Wc memc mdc -> In (1, fpos) (frames Sc) ->
alloc_ceiling + SUP_CHAIN_STK <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - SUP_CHAIN_STK <= a < spZ regs -> apresent (w_H Wc) memc a) ->
spZ regsc = scb_sp1 (spZ regs) -> getr regsc 8 = w64 (spZ regs) -> getr regsc 9 = w64 (scb_sp1 (spZ regs)) ->
0 <= c < 2 ^ 64 ->
scb_frame_at (mrestrict (w_H Wc) memc) (spZ regs) regs ->
val_mem SEGS (mrestrict (w_H Wc) memc) (scb_sp1 (spZ regs) + 8) 8 c ->
val_mem SEGS (mrestrict (w_H Wc) memc) (scb_sp1 (spZ regs) + 16) 8 (frame_addr lyc 1 fpos) ->
val_mem SEGS (mrestrict (w_H Wc) memc) (scb_sp1 (spZ regs) + 24) 8 (SB + frame_addr lyc 1 fpos / 8) ->
val_mem SEGS (mrestrict (w_H Wc) memc) (scb_sp1 (spZ regs) + 32) 8 (frame_addr lyc 1 fpos) ->
rdword (rdW Wc memc) (frame_addr lyc 1 fpos + 120) = Some (flag_addr lyc 1 fpos) ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (scb4_ext regs c (frame_addr lyc 1 fpos) (flag_addr lyc 1 fpos)))) scb4_ss
(restrict (w_H Wc) (@mkst fxv regsc (Z_to_bv 64 (BASE + SCB_LEXIT)) memc (seg_rom SEGS))).
Proof.
intros fxv lyc Sc Wc regsc regs memc mdc fpos c HAR Hfin Hsp46 Hsp16 Hpres Hspc R8 R9 Hc HFR HW8 HW16 HW24 HW32 HFLG.
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
assert (HSTK : SUP_CHAIN_STK = 16800) by (vm_compute; reflexivity).
set (sp0 := spZ regs) in *. unfold scb_sp1 in *. set (sp1 := 32 * ((sp0 - 192) / 32)) in *.
set (F := frame_addr lyc 1 fpos) in *. set (FL := flag_addr lyc 1 fpos) in *.
destruct (scb_sp1_facts sp0 Hsp16 ltac:(lia)) as (Hsp1 & Hsp1a & Hsp1b). fold sp1 in Hsp1, Hsp1a, Hsp1b.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR Hfin) as (HF4096 & HFceil & _). fold F in HF4096, HFceil.
destruct (frame_al64 SEGS B _ _ _ _ _ 1 fpos HAR Hfin) as (HF64 & _ & _). fold F in HF64.
destruct (FFL _ _ _ _ _ 1 fpos HAR Hfin) as (_ & _ & _ & (HFL4096 & _ & HFLceil)). fold FL in HFL4096, HFLceil.
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF32 : F mod 32 = 0).
{ rewrite HFq. replace (64 * (F / 64)) with ((2 * (F / 64)) * 32) by lia. apply Z_mod_mult. }
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsc (scb4_ext regs c F FL))).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 17)%nat -> ew E (32 + j) = nth j (scb4_ext regs c F FL) (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : bv_unsigned (ew E 2) = sp1)
  by (rewrite (EL 2%nat 2%bv eq_refl); unfold spZ in Hspc; exact Hspc).
assert (E8 : bv_unsigned (ew E 8) = sp0)
  by (rewrite (EL 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (E9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EL 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E45 : ew E 45 = Z_to_bv 64 c) by (exact (EX 13%nat ltac:(lia))).
assert (E46 : ew E 46 = Z_to_bv 64 F) by (exact (EX 14%nat ltac:(lia))).
assert (E47 : ew E 47 = Z_to_bv 64 (SB + F / 8)) by (exact (EX 15%nat ltac:(lia))).
assert (E48 : ew E 48 = Z_to_bv 64 FL) by (exact (EX 16%nat ltac:(lia))).
assert (U45 : bv_unsigned (ew E 45) = c) by (rewrite E45; apply unsigned_lit_small; lia).
assert (U46 : bv_unsigned (ew E 46) = F) by (rewrite E46; apply unsigned_lit_small; lia).
assert (CHK : forall (od : Z) (m : nat) (r : Z),
  ew E m = getr regs (Z_to_bv 5 r) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp0 + od) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))) ->
  YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) sp0 (YP09.mkChunk od (CVal 8 (SOff m 0)))).
{ intros od m r Hm Hv.
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr.
  apply (chunk_ok_val SEGS E _ sp0 od 8 (SOff m 0) (bv_unsigned (getr regs (Z_to_bv 5 r))));
  [ rewrite scb_denot_off0, Hm; symmetry; apply Z_to_bv_bv_unsigned
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hv ]. }
assert (CHW : forall (od v : Z) (m : nat), ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1 + od) 8 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H Wc) memc) sp1 (YP09.mkChunk od (CVal 8 (SOff m 0)))).
{ intros od v m Hm Hv Hval.
  apply (chunk_ok_val SEGS E _ sp1 od 8 (SOff m 0) v);
  [ rewrite scb_denot_off0; exact Hm
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hval ]. }
pose proof (HFR 0%nat 1 eq_refl) as FR0. pose proof (HFR 1%nat 8 eq_refl) as FR1.
pose proof (HFR 2%nat 9 eq_refl) as FR2. pose proof (HFR 3%nat 18 eq_refl) as FR3.
pose proof (HFR 4%nat 19 eq_refl) as FR4. pose proof (HFR 5%nat 20 eq_refl) as FR5.
pose proof (HFR 6%nat 21 eq_refl) as FR6. pose proof (HFR 7%nat 22 eq_refl) as FR7.
pose proof (HFR 8%nat 23 eq_refl) as FR8. pose proof (HFR 9%nat 24 eq_refl) as FR9.
pose proof (HFR 10%nat 25 eq_refl) as FR10. pose proof (HFR 11%nat 26 eq_refl) as FR11.
pose proof (HFR 12%nat 27 eq_refl) as FR12.
cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in FR0, FR1, FR2, FR3, FR4, FR5, FR6, FR7, FR8, FR9, FR10, FR11, FR12.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold scb4_ss, scb4_saveR, scb4_wordsR, scb4_flgR.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite E8. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * repeat apply Forall_cons; try apply Forall_nil.
      -- apply (CHK (-8) 32%nat 1 (EX 0%nat ltac:(lia))). replace (sp0 + -8) with (sp0 - 8 - 8 * 0) by lia. exact FR0.
      -- apply (CHK (-16) 33%nat 8 (EX 1%nat ltac:(lia))). replace (sp0 + -16) with (sp0 - 8 - 8 * 1) by lia. exact FR1.
      -- apply (CHK (-24) 34%nat 9 (EX 2%nat ltac:(lia))). replace (sp0 + -24) with (sp0 - 8 - 8 * 2) by lia. exact FR2.
      -- apply (CHK (-32) 35%nat 18 (EX 3%nat ltac:(lia))). replace (sp0 + -32) with (sp0 - 8 - 8 * 3) by lia. exact FR3.
      -- apply (CHK (-40) 36%nat 19 (EX 4%nat ltac:(lia))). replace (sp0 + -40) with (sp0 - 8 - 8 * 4) by lia. exact FR4.
      -- apply (CHK (-48) 37%nat 20 (EX 5%nat ltac:(lia))). replace (sp0 + -48) with (sp0 - 8 - 8 * 5) by lia. exact FR5.
      -- apply (CHK (-56) 38%nat 21 (EX 6%nat ltac:(lia))). replace (sp0 + -56) with (sp0 - 8 - 8 * 6) by lia. exact FR6.
      -- apply (CHK (-64) 39%nat 22 (EX 7%nat ltac:(lia))). replace (sp0 + -64) with (sp0 - 8 - 8 * 7) by lia. exact FR7.
      -- apply (CHK (-72) 40%nat 23 (EX 8%nat ltac:(lia))). replace (sp0 + -72) with (sp0 - 8 - 8 * 8) by lia. exact FR8.
      -- apply (CHK (-80) 41%nat 24 (EX 9%nat ltac:(lia))). replace (sp0 + -80) with (sp0 - 8 - 8 * 9) by lia. exact FR9.
      -- apply (CHK (-88) 42%nat 25 (EX 10%nat ltac:(lia))). replace (sp0 + -88) with (sp0 - 8 - 8 * 10) by lia. exact FR10.
      -- apply (CHK (-96) 43%nat 26 (EX 11%nat ltac:(lia))). replace (sp0 + -96) with (sp0 - 8 - 8 * 11) by lia. exact FR11.
      -- apply (CHK (-104) 44%nat 27 (EX 12%nat ltac:(lia))). replace (sp0 + -104) with (sp0 - 8 - 8 * 12) by lia. exact FR12.
  + cbn [base_val]. rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (CHW 8 c 45%nat E45 ltac:(lia) HW8).
    * apply (CHW 16 F 46%nat E46 ltac:(lia) HW16).
    * apply (CHW 24 (SB + F / 8) 47%nat E47 ltac:(unfold SB; lia) HW24).
    * apply (CHW 32 F 46%nat E46 ltac:(lia) HW32).
  + cbn [base_val]. rewrite U46. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ F 120 8 (SOff 48 0) FL);
    [ rewrite scb_denot_off0; exact E48
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
    | cbn; lia
    | exact (val_mem_of_rdword SEGS _ _ _ _ HFLG) ].
- apply pairwise_disjoint_of_extents.
  unfold scb4_ss, scb4_saveR, scb4_wordsR, scb4_flgR, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite E8, E9, U46.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split | |- True => exact I end; first [left; lia | right; lia].
- unfold scb4_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
  rewrite E2, E8, E9, U46. change (2 ^ 4) with 16. change (2 ^ 5) with 32.
  rewrite Hsp16, Hsp1a, HF32. repeat split; lia.
Qed.

(* g_rec and record.spill: image bytes outside the runtime's owned ranges and the errno cell *)
Lemma scb4_rec_unowned : forall a, A_G_REC <= a < A_G_REC + 960 \/ A_REC_SPILL <= a < A_REC_SPILL + 56 ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros a Ha. assert (HP : Exists (in_zr a) TFIB_PROG_STATIC).
{ destruct Ha as [Ha | Ha]; [apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd];
  unfold in_zr; cbn [fst snd]; unfold A_G_REC, A_REC_SPILL in *; lia. }
split; [exact (cmd_prog_img a HP)|].
assert (HP' : Exists (in_zr a) (as_prog_static B)) by (rewrite (ts_prog B HB); exact HP).
destruct (prog_static_sep B a (ts_ok B HB) HP') as (H1 & H2 & _). split; assumption.
Qed.
(* the recorder's state across a journal whose footprint misses its bytes *)
Lemma scb4_rep_aj : forall STK sp FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k R O,
ajournal SEGS B STK sp FP ly S W mem md own ly' S' W' mem' md' k ->
rec_repA B ly S (rdW W mem) R O ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
~ YI16.sink_open_fp FP ->
(forall p n i, In (p, n) O -> 0 <= i < n -> ~ inFP FP (p + i)) ->
(forall a, A_G_REC <= a < A_G_REC + 960 \/ A_REC_SPILL <= a < A_REC_SPILL + 56 -> ~ inFP FP a) ->
rec_repA B ly' S' (rdW W' mem') R O.
Proof.
intros STK sp FP ly S W mem md own ly' S' W' mem' md' k R O HJ HREP HO H0 HFb HFg.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FJ2 & FJ3 & _).
apply (rec_repA_kept ly S (rdW W mem) ly' S' (rdW W' mem') R O HREP HO).
- intros a Ha. destruct (scb4_rec_unowned a (or_introl Ha)) as (Hi & Ho & He).
  apply FJ3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [exact H0 | exact (HFg a (or_introl Ha))]].
- intros a Ha. destruct (scb4_rec_unowned a (or_intror Ha)) as (Hi & Ho & He).
  apply FJ3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [exact H0 | exact (HFg a (or_intror Ha))]].
- intros p n i Hin Hi. pose proof (rec_repA_in ly S _ R O HREP (p, n) Hin) as Hb.
  pose proof (req_size_pos n ltac:(lia)) as [Rn1 Rn2].
  apply (FJ2 p n i); [exact Hb | exact (HO _ Hin) | lia | exact (HFb p n i Hin Hi)].
Qed.
(* a string argument's bytes across a journal whose footprint misses them and whose stack window is above them *)
Lemma scb4_argA_aj : forall STK sp FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k O p x,
ajournal SEGS B STK sp FP ly S W mem md own ly' S' W' mem' md' k ->
astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O p (Some x) ->
(forall pn, In pn (ablocks B ly S) -> In pn (ablocks B ly' S')) ->
~ YI16.sink_open_fp FP ->
(forall i, 0 <= i < Z.of_nat (length x) + 1 -> ~ inFP FP (p + i)) ->
astr_argA B ly' S' (rdW W' mem') (in_roP SEGS RLO RHI) O p (Some x).
Proof.
intros STK sp FP ly S W mem md own ly' S' W' mem' md' k O p x HJ HA Hbl H0 HF.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FJ2 & FJ3 & _).
destruct HA as (H1 & Hs & Hl & Har).
assert (K : forall i, 0 <= i < Z.of_nat (length x) + 1 -> rdW W' mem' (p + i) = rdW W mem (p + i)).
{ intros i Hi. destruct Har as [((q & k0 & Hin & Hq1 & Hq2) & _) | (Hro & _)].
  - replace (p + i) with (q + (p + i - q)) by lia.
    pose proof (req_size_pos k0 ltac:(lia)) as [Rk1 Rk2].
    apply (FJ2 q k0 (p + i - q)); [exact Hin | exact (Hbl _ Hin) | lia |
      replace (q + (p + i - q)) with (p + i) by lia; exact (HF i Hi)].
  - destruct (Hro i Hi) as (Hr & Hno & Hne).
    apply FJ3; [exact (proj1 (cmd_ro_prog_apart _ Hr)) | exact Hno | exact Hne |
      apply fp_spares_closed; [exact H0 | exact (HF i Hi)]]. }
split; [exact H1|]. split; [apply (rastr_kept (rdW W mem)); [exact Hs | exact K]|]. split; [exact Hl|].
destruct Har as [(HB1 & HB2) | HR]; [left; split; [|exact HB2] | right; exact HR].
destruct HB1 as (q & k0 & Hin & Hq). exists q, k0. split; [exact (Hbl _ Hin) | exact Hq].
Qed.
(* the saved registers, read off the walk's stack region *)
Lemma scb4_frame_of_region : forall E H (m : word -> option byte) (sp0 : Z) (regs : bvmap 5 word),
bv_unsigned (ew E 8) = sp0 ->
(forall j, (j < 13)%nat -> ew E (32 + j) = getr regs (Z_to_bv 5 (nth j scb_saved 0))) ->
YP09.region_ok SEGS E (mrestrict H m) scb4_saveR ->
scb_frame_at (mrestrict H m) sp0 regs.
Proof.
intros E H m sp0 regs H8 HX HR.
assert (G : forall jj : nat, (jj < 13)%nat ->
  In (YP09.mkChunk (-8 - 8 * Z.of_nat jj) (CVal 8 (SOff (32 + jj) 0))) (YP09.r_chunks scb4_saveR) ->
  val_mem SEGS (mrestrict H m) (sp0 - 8 - 8 * Z.of_nat jj) 8
    (bv_unsigned (getr regs (Z_to_bv 5 (nth jj scb_saved 0))))).
{ intros jj Hjj Hin.
  replace (sp0 - 8 - 8 * Z.of_nat jj) with (sp0 + (-8 - 8 * Z.of_nat jj)) by lia.
  refine (field_of_region E _ 8%nat sp0 _ (-104) 0 (-104) 0 (-8 - 8 * Z.of_nat jj) 8%N
    (SOff (32 + jj) 0) _ HR H8 Hin _ _ _);
  [ rewrite scb_denot_off0, (HX jj Hjj); symmetry; apply Z_to_bv_bv_unsigned
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
  | cbn [YP09.r_lo YP09.r_hi]; lia ]. }
intros j r Hj.
assert (GI : forall jj : nat, (jj < 13)%nat ->
  In (YP09.mkChunk (-8 - 8 * Z.of_nat jj) (CVal 8 (SOff (32 + jj) 0))) (YP09.r_chunks scb4_saveR)).
{ intros jj Hjj. unfold scb4_saveR.
  do 13 (destruct jj as [|jj]; [cbn; tauto|]). lia. }
destruct j as [|j]; [cbn [nth_error scb_saved] in Hj; injection Hj as <-;
  exact (G 0%nat ltac:(lia) (GI 0%nat ltac:(lia)))|].
destruct j as [|j]; [cbn [nth_error scb_saved] in Hj; injection Hj as <-;
  exact (G 1%nat ltac:(lia) (GI 1%nat ltac:(lia)))|].
destruct j as [|j]; [cbn [nth_error scb_saved] in Hj; injection Hj as <-;
  exact (G 2%nat ltac:(lia) (GI 2%nat ltac:(lia)))|].
destruct j as [|j]; [cbn [nth_error scb_saved] in Hj; injection Hj as <-;
  exact (G 3%nat ltac:(lia) (GI 3%nat ltac:(lia)))|].
destruct j as [|j]; [cbn [nth_error scb_saved] in Hj; injection Hj as <-;
  exact (G 4%nat ltac:(lia) (GI 4%nat ltac:(lia)))|].
destruct j as [|j]; [cbn [nth_error scb_saved] in Hj; injection Hj as <-;
  exact (G 5%nat ltac:(lia) (GI 5%nat ltac:(lia)))|].
destruct j as [|j]; [cbn [nth_error scb_saved] in Hj; injection Hj as <-;
  exact (G 6%nat ltac:(lia) (GI 6%nat ltac:(lia)))|].
destruct j as [|j]; [cbn [nth_error scb_saved] in Hj; injection Hj as <-;
  exact (G 7%nat ltac:(lia) (GI 7%nat ltac:(lia)))|].
destruct j as [|j]; [cbn [nth_error scb_saved] in Hj; injection Hj as <-;
  exact (G 8%nat ltac:(lia) (GI 8%nat ltac:(lia)))|].
destruct j as [|j]; [cbn [nth_error scb_saved] in Hj; injection Hj as <-;
  exact (G 9%nat ltac:(lia) (GI 9%nat ltac:(lia)))|].
destruct j as [|j]; [cbn [nth_error scb_saved] in Hj; injection Hj as <-;
  exact (G 10%nat ltac:(lia) (GI 10%nat ltac:(lia)))|].
destruct j as [|j]; [cbn [nth_error scb_saved] in Hj; injection Hj as <-;
  exact (G 11%nat ltac:(lia) (GI 11%nat ltac:(lia)))|].
destruct j as [|j]; [cbn [nth_error scb_saved] in Hj; injection Hj as <-;
  exact (G 12%nat ltac:(lia) (GI 12%nat ltac:(lia)))|].
exfalso. pose proof (proj1 (nth_error_Some scb_saved _) ltac:(rewrite Hj; discriminate)) as Hlen.
unfold scb_saved in Hlen. cbn [length] in Hlen. lia.
Qed.

(* ---------- the release, the epilogue and the return (0x8c47c .. 0x8c558) ---------- *)
(* the atoms above the registers at 0x8c47c: the 13 saved registers' entry values (atoms 32 .. 44, the order of
   scb_saved), the class-1 frame F (45), its shadow address SB + F / 8 (46) and its flag address FL (47) *)
Definition scb4_relext (regs : bvmap 5 word) (F FL : Z) : list word :=
map (fun r => getr regs (Z_to_bv 5 r)) scb_saved ++ map (Z_to_bv 64) [F; SB + F / 8; FL].
(* the saved registers at entry sp - 8 - 8j (the epilogue loads them) *)
Definition scb4_relsaveR : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 (-104) 0
[YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk (-16) (CVal 8 (SOff 33 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 34 0)); YP09.mkChunk (-32) (CVal 8 (SOff 35 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-48) (CVal 8 (SOff 37 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 38 0)); YP09.mkChunk (-64) (CVal 8 (SOff 39 0));
 YP09.mkChunk (-72) (CVal 8 (SOff 40 0)); YP09.mkChunk (-80) (CVal 8 (SOff 41 0));
 YP09.mkChunk (-88) (CVal 8 (SOff 42 0)); YP09.mkChunk (-96) (CVal 8 (SOff 43 0));
 YP09.mkChunk (-104) (CVal 8 (SOff 44 0))].
(* the three stack words the release reads: F at sp1 + 16 and sp1 + 32, its shadow at sp1 + 24 *)
Definition scb4_relwordsR : YP09.region := YP09.mkRegion (Some 9%nat) 16 40 16 16
[YP09.mkChunk 16 (CVal 8 (SOff 45 0)); YP09.mkChunk 24 (CVal 8 (SOff 46 0)); YP09.mkChunk 32 (CVal 8 (SOff 45 0))].
(* the frame's header (the magic at F + 0), its flag word, its 16 shadow bytes, its flag byte *)
Definition scb4_relhdrR : YP09.region := YP09.mkRegion (Some 45%nat) 0 32 0 24 [].
Definition scb4_relflgR : YP09.region := YP09.mkRegion (Some 45%nat) 120 128 120 120 [YP09.mkChunk 120 (CVal 8 (SOff 47 0))].
Definition scb4_relshdR : YP09.region := YP09.mkRegion (Some 46%nat) 0 16 0 16 [].
Definition scb4_relfbR : YP09.region := YP09.mkRegion (Some 47%nat) 0 1 0 1 [].
Definition scb4_relregions : smem := [scb4_relsaveR; scb4_relwordsR; scb4_relhdrR; scb4_relflgR; scb4_relshdR].
Definition scb4_relfacts : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46 - 256) (2 ^ 47) 5); (8%nat, mkAF (2 ^ 46) (2 ^ 47) 4);
         (9%nat, mkAF (2 ^ 46 - 256) (2 ^ 47) 5); (45%nat, HPTR 5); (46%nat, mkAF SB (SB + 2 ^ 44) 0);
         (47%nat, mkAF 4096 140737479966720 0)] [] [].
Definition scb4_relss : sstate := mkSS SCB_REL sr_atoms scb4_relregions None scb4_relfacts.


(* the symbolic state at 0x8c47c: the registers, the saved registers below the entry sp, the three stack words, the
   frame's header, flag word and shadow, and the facts on sp1, the entry sp, F, its shadow and its flag address *)
Lemma scb4_relseed : forall (fxv : YK11.FPState) (ly6 : alayout) (S6 : astate) (W6 : world SEGS)
  (regs6 regs : bvmap 5 word) (mem6 : word -> option byte) (md6 : Model) (fpos : Z),
AR SEGS B ly6 S6 W6 mem6 md6 -> In (1, fpos) (frames S6) ->
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 -> alloc_ceiling + SUP_CHAIN_STK <= spZ regs ->
(forall a, spZ regs - SUP_CHAIN_STK <= a < spZ regs -> apresent (w_H W6) mem6 a) ->
spZ regs6 = scb_sp1 (spZ regs) -> getr regs6 8 = w64 (spZ regs) -> getr regs6 9 = w64 (scb_sp1 (spZ regs)) ->
scb_frame_at (mrestrict (w_H W6) mem6) (spZ regs) regs ->
val_mem SEGS (mrestrict (w_H W6) mem6) (scb_sp1 (spZ regs) + 16) 8 (frame_addr ly6 1 fpos) ->
val_mem SEGS (mrestrict (w_H W6) mem6) (scb_sp1 (spZ regs) + 24) 8 (SB + frame_addr ly6 1 fpos / 8) ->
val_mem SEGS (mrestrict (w_H W6) mem6) (scb_sp1 (spZ regs) + 32) 8 (frame_addr ly6 1 fpos) ->
rdword (rdW W6 mem6) (frame_addr ly6 1 fpos + 120) = Some (flag_addr ly6 1 fpos) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs6 (scb4_relext regs (frame_addr ly6 1 fpos) (flag_addr ly6 1 fpos)))) scb4_relss
  (restrict (w_H W6) (@mkst fxv regs6 (Z_to_bv 64 (BASE + SCB_REL)) mem6 (seg_rom SEGS))).
Proof.
intros fxv ly6 S6 W6 regs6 regs mem6 md6 fpos HAR Hfin Hsp46 Hsp16 Hstk Hpres Hspc R8 R9 HFR HW16 HW24 HW32 HFLG.
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
assert (HSTK : SUP_CHAIN_STK = 16800) by (vm_compute; reflexivity).
assert (HSB : SB = 0x7fff8000) by reflexivity.
rewrite HSTK in Hstk, Hpres.
set (sp0 := spZ regs) in *. set (sp1 := scb_sp1 sp0) in *.
set (F := frame_addr ly6 1 fpos) in *. set (FL := flag_addr ly6 1 fpos) in *.
destruct (scb_sp1_facts sp0 Hsp16 ltac:(lia)) as (Hsp1 & Hsp1a & _).
change (32 * ((sp0 - 192) / 32)) with sp1 in Hsp1, Hsp1a.
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR Hfin) as (HF32 & HFapp & HFpres & HFSpres).
fold F in HF32, HFapp, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR Hfin) as (HF4096 & HFceil & _). fold F in HF4096, HFceil.
destruct (FFL _ _ _ _ _ 1 fpos HAR Hfin) as (_ & _ & _ & (HFL4096 & _ & HFLceil)). fold FL in HFL4096, HFLceil.
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
pose proof (Z.div_mod F 8 ltac:(lia)) as HFd. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as HFm.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs6 (scb4_relext regs F FL))).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs6 r)
  by (intros n r Hn; exact (ew_Eimg_Ereg_nat regs6 _ n r Hn)).
assert (EX : forall j, (j < 16)%nat -> ew E (32 + j) = nth j (scb4_relext regs F FL) (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite (EL 2%nat 2%bv eq_refl); exact Hspc).
assert (U8 : bv_unsigned (ew E 8) = sp0)
  by (rewrite (EL 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EL 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E45 : ew E 45 = Z_to_bv 64 F) by exact (EX 13%nat ltac:(lia)).
assert (E46 : ew E 46 = Z_to_bv 64 (SB + F / 8)) by exact (EX 14%nat ltac:(lia)).
assert (E47 : ew E 47 = Z_to_bv 64 FL) by exact (EX 15%nat ltac:(lia)).
assert (U45 : bv_unsigned (ew E 45) = F) by (rewrite E45; apply unsigned_lit_small; lia).
assert (U46 : bv_unsigned (ew E 46) = SB + F / 8) by (rewrite E46; apply unsigned_lit_small; lia).
assert (U47 : bv_unsigned (ew E 47) = FL) by (rewrite E47; apply unsigned_lit_small; lia).
assert (CHK : forall (od : Z) (m : nat) (r : Z),
  ew E m = getr regs (Z_to_bv 5 r) ->
  val_mem SEGS (mrestrict (w_H W6) mem6) (sp0 + od) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))) ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W6) mem6) sp0 (YP09.mkChunk od (CVal 8 (SOff m 0)))).
{ intros od m r Hm Hv.
  pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr.
  apply (chunk_ok_val SEGS E _ sp0 od 8 (SOff m 0) (bv_unsigned (getr regs (Z_to_bv 5 r))));
  [ rewrite scb_denot_off0, Hm, Z_to_bv_bv_unsigned; reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hv ]. }
assert (CHW : forall (od v : Z) (m : nat), ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W6) mem6) (sp1 + od) 8 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W6) mem6) sp1 (YP09.mkChunk od (CVal 8 (SOff m 0)))).
{ intros od v m Hm Hv Hval.
  apply (chunk_ok_val SEGS E _ sp1 od 8 (SOff m 0) v);
  [ rewrite scb_denot_off0; exact Hm
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact Hval ]. }
pose proof (HFR 0%nat 1 eq_refl) as FR0. pose proof (HFR 1%nat 8 eq_refl) as FR1.
pose proof (HFR 2%nat 9 eq_refl) as FR2. pose proof (HFR 3%nat 18 eq_refl) as FR3.
pose proof (HFR 4%nat 19 eq_refl) as FR4. pose proof (HFR 5%nat 20 eq_refl) as FR5.
pose proof (HFR 6%nat 21 eq_refl) as FR6. pose proof (HFR 7%nat 22 eq_refl) as FR7.
pose proof (HFR 8%nat 23 eq_refl) as FR8. pose proof (HFR 9%nat 24 eq_refl) as FR9.
pose proof (HFR 10%nat 25 eq_refl) as FR10. pose proof (HFR 11%nat 26 eq_refl) as FR11.
pose proof (HFR 12%nat 27 eq_refl) as FR12.
cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in FR0, FR1, FR2, FR3, FR4, FR5, FR6, FR7, FR8, FR9, FR10, FR11, FR12.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold scb4_relregions, scb4_relsaveR, scb4_relwordsR, scb4_relhdrR, scb4_relflgR, scb4_relshdR.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite U8. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    * repeat apply Forall_cons; try apply Forall_nil.
      -- apply (CHK (-8) 32%nat 1 (EX 0%nat ltac:(lia))). replace (sp0 + -8) with (sp0 - 8 - 8 * 0) by lia. exact FR0.
      -- apply (CHK (-16) 33%nat 8 (EX 1%nat ltac:(lia))). replace (sp0 + -16) with (sp0 - 8 - 8 * 1) by lia. exact FR1.
      -- apply (CHK (-24) 34%nat 9 (EX 2%nat ltac:(lia))). replace (sp0 + -24) with (sp0 - 8 - 8 * 2) by lia. exact FR2.
      -- apply (CHK (-32) 35%nat 18 (EX 3%nat ltac:(lia))). replace (sp0 + -32) with (sp0 - 8 - 8 * 3) by lia. exact FR3.
      -- apply (CHK (-40) 36%nat 19 (EX 4%nat ltac:(lia))). replace (sp0 + -40) with (sp0 - 8 - 8 * 4) by lia. exact FR4.
      -- apply (CHK (-48) 37%nat 20 (EX 5%nat ltac:(lia))). replace (sp0 + -48) with (sp0 - 8 - 8 * 5) by lia. exact FR5.
      -- apply (CHK (-56) 38%nat 21 (EX 6%nat ltac:(lia))). replace (sp0 + -56) with (sp0 - 8 - 8 * 6) by lia. exact FR6.
      -- apply (CHK (-64) 39%nat 22 (EX 7%nat ltac:(lia))). replace (sp0 + -64) with (sp0 - 8 - 8 * 7) by lia. exact FR7.
      -- apply (CHK (-72) 40%nat 23 (EX 8%nat ltac:(lia))). replace (sp0 + -72) with (sp0 - 8 - 8 * 8) by lia. exact FR8.
      -- apply (CHK (-80) 41%nat 24 (EX 9%nat ltac:(lia))). replace (sp0 + -80) with (sp0 - 8 - 8 * 9) by lia. exact FR9.
      -- apply (CHK (-88) 42%nat 25 (EX 10%nat ltac:(lia))). replace (sp0 + -88) with (sp0 - 8 - 8 * 10) by lia. exact FR10.
      -- apply (CHK (-96) 43%nat 26 (EX 11%nat ltac:(lia))). replace (sp0 + -96) with (sp0 - 8 - 8 * 11) by lia. exact FR11.
      -- apply (CHK (-104) 44%nat 27 (EX 12%nat ltac:(lia))). replace (sp0 + -104) with (sp0 - 8 - 8 * 12) by lia. exact FR12.
  + cbn [base_val]. rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (CHW 16 F 45%nat E45 ltac:(lia) HW16).
    * apply (CHW 24 (SB + F / 8) 46%nat E46 ltac:(lia) HW24).
    * apply (CHW 32 F 45%nat E45 ltac:(lia) HW32).
  + cbn [base_val]. rewrite U45. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (F + o) ltac:(lia))).
  + cbn [base_val]. rewrite U45. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ F 120 8 (SOff 47 0) FL);
    [ rewrite scb_denot_off0; exact E47
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
    | cbn; lia
    | exact (val_mem_of_rdword SEGS _ _ _ _ HFLG) ].
  + cbn [base_val]. rewrite U46. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS).
    replace (SB + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia).
    exact (proj1 (HFSpres o ltac:(lia))).
- apply pairwise_disjoint_of_extents.
  unfold scb4_relregions, scb4_relsaveR, scb4_relwordsR, scb4_relhdrR, scb4_relflgR, scb4_relshdR, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite U8, U9, U45, U46.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- unfold scb4_relfacts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
  rewrite U2, U8, U9, U45, U46, U47. change (2 ^ 4) with 16. change (2 ^ 5) with 32.
  rewrite !Z.pow_0_r, !Z.mod_1_r. rewrite Hsp16, Hsp1a, HF32. repeat split; lia.
Qed.

Section rel.
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Variables (O : list (Z * Z)) (fr0 : bvmap 5 word) (csr0 : bv 32).

Lemma scb4_rel : forall (fxv : YK11.FPState) (ly6 : alayout) (S6 : astate) (W6 : world SEGS)
  (regs6 : bvmap 5 word) (mem6 : word -> option byte) (md6 : Model) (fpos q kk EVt : Z)
  (QQ : alayout -> astate -> world SEGS -> (word -> option byte) -> Model -> Prop),
scb_fxok fr0 csr0 fxv ->
(* the journal from the function's entry, with the class-1 frame as this call's own *)
ajournal SEGS B SUP_CHAIN_STK (spZ regs) (SCB_FP O) ly S W mem md [(1, fpos)] ly6 S6 W6 mem6 md6 kk ->
kk <= EVt ->
(* the entry's stack and return address (afn_pre's) *)
2 ^ 46 <= spZ regs -> YK0s.ret_ok (getr regs 1) ->
(* the registers at 0x8c47c *)
spZ regs6 = scb_sp1 (spZ regs) -> getr regs6 3 = getr regs 3 -> getr regs6 4 = getr regs 4 ->
getr regs6 8 = w64 (spZ regs) -> getr regs6 9 = w64 (scb_sp1 (spZ regs)) -> getr regs6 10 = w64 q ->
(* the memory at 0x8c47c: the 13 saved registers, the three stack words the release reads, the flag word *)
scb_frame_at (mrestrict (w_H W6) mem6) (spZ regs) regs ->
val_mem SEGS (mrestrict (w_H W6) mem6) (scb_sp1 (spZ regs) + 16) 8 (frame_addr ly6 1 fpos) ->
val_mem SEGS (mrestrict (w_H W6) mem6) (scb_sp1 (spZ regs) + 24) 8 (SB + frame_addr ly6 1 fpos / 8) ->
val_mem SEGS (mrestrict (w_H W6) mem6) (scb_sp1 (spZ regs) + 32) 8 (frame_addr ly6 1 fpos) ->
rdword (rdW W6 mem6) (frame_addr ly6 1 fpos + 120) = Some (flag_addr ly6 1 fpos) ->
(* what the caller's post needs of the state the release leaves: the release writes only the frame, its shadow and
   its flag byte, so every byte of g_rec, of record.spill and of a live block is the one at 0x8c47c *)
(forall (W' : world SEGS) (mem' : word -> option byte) (md' : Model),
   AR SEGS B ly6 (stack_free_state 1 fpos S6) W' mem' md' ->
   wle W6 W' ->
   (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
      (exists p n, In (p, n) (ablocks B ly6 S6) /\ p <= a < p + req_size n)) ->
      rdW W' mem' a = rdW W6 mem6 a) ->
   QQ ly6 (stack_free_state 1 fpos S6) W' mem' md') ->
SRr SEGS W6 (@cfg_at fxv SEGS (BASE + SCB_REL) regs6 mem6 md6)
  (scb_postF B fr0 csr0 SUP_CHAIN_STK (SCB_FP O) regs ly S W mem md EVt
     (fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 q /\ QQ ly' S' W' mem' md')).
Proof.
intros fxv ly6 S6 W6 regs6 mem6 md6 fpos q kk EVt QQ HFX HJ6 Hkk Hsp46 Hra H2 H3 H4 H8 H9 H10 HFR HW16 HW24 HW32 HFLG HQQ.
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
assert (HSTK : SUP_CHAIN_STK = 16800) by (vm_compute; reflexivity).
assert (HSB : SB = 0x7fff8000) by reflexivity.
pose proof HJ6 as (HAR6 & _ & _ & _ & _ & Hfrs6 & _ & _ & _ & _ & _ & _ & _ & HJpres & HJstk & _).
destruct HJstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (Hfin : In (1, fpos) (frames S6)) by (rewrite Hfrs6; left; reflexivity).
destruct (scb_sp1_facts (spZ regs) Hal16 ltac:(lia)) as (Hsp1 & _ & _).
change (32 * ((spZ regs - 192) / 32)) with (scb_sp1 (spZ regs)) in Hsp1.
pose proof (scb4_relseed fxv ly6 S6 W6 regs6 regs mem6 md6 fpos HAR6 Hfin ltac:(lia) Hal16 ltac:(lia) HJpres
  H2 H8 H9 HFR HW16 HW24 HW32 HFLG) as HS.
set (F := frame_addr ly6 1 fpos) in *. set (FL := flag_addr ly6 1 fpos) in *.
set (E := Eimg (Ereg regs6 (scb4_relext regs F FL))) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply Eimg_env).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs6 r)
  by (intros n r Hn; exact (ew_Eimg_Ereg_nat regs6 _ n r Hn)).
assert (EX : forall j, (j < 16)%nat -> ew E (32 + j) = nth j (scb4_relext regs F FL) (Z_to_bv 64 0)).
{ intros j Hj. unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
(* the frame, its shadow and its flag byte: apart from each other, from the stack and from the image *)
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR6 Hfin) as (HF32 & HFapp & HFpres & HFSpres).
fold F in HF32, HFapp, HFpres, HFSpres.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HAR6 Hfin) as (HF4096 & HFceil & _). fold F in HF4096, HFceil.
pose proof (frm_off_imgP _ _ _ _ _ _ _ _ HAR6 Hfin) as HFoff. fold F in HFoff. unfold off_img in HFoff.
destruct (FFL _ _ _ _ _ 1 fpos HAR6 Hfin) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLceil)).
fold FL in HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLceil.
change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
assert (HF8 : 512 <= F / 8 < 2 ^ 44) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
assert (HF8b : F / 8 <= 17592185978880) by (apply Z.div_le_upper_bound; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
unfold zone2, off_img in HFLz.
assert (HFLnS : ~ (SB + F / 8 <= FL < SB + F / 8 + 16)).
{ intros Hx. apply (proj2 (HFSpres (FL - (SB + F / 8)) ltac:(lia))).
  replace (shadow_addr F + (FL - (SB + F / 8))) with FL by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia).
  exact HFLo. }
assert (HFLnF : ~ (F <= FL < F + 128)) by (intros Hx; exact (proj2 (HFpres FL Hx) HFLo)).
(* the values of the atoms the regions are based on *)
assert (U8 : bv_unsigned (ew E 8) = spZ regs)
  by (rewrite (EL 8%nat 8%bv eq_refl), H8; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = scb_sp1 (spZ regs))
  by (rewrite (EL 9%nat 9%bv eq_refl), H9; unfold w64; apply unsigned_lit_small; lia).
assert (E45 : ew E 45 = Z_to_bv 64 F) by exact (EX 13%nat ltac:(lia)).
assert (E46 : ew E 46 = Z_to_bv 64 (SB + F / 8)) by exact (EX 14%nat ltac:(lia)).
assert (E47 : ew E 47 = Z_to_bv 64 FL) by exact (EX 15%nat ltac:(lia)).
assert (U45 : bv_unsigned (ew E 45) = F) by (rewrite E45; apply unsigned_lit_small; lia).
assert (U46 : bv_unsigned (ew E 46) = SB + F / 8) by (rewrite E46; apply unsigned_lit_small; lia).
assert (U47 : bv_unsigned (ew E 47) = FL) by (rewrite E47; apply unsigned_lit_small; lia).
(* g_rec, record.spill and the live blocks: below the stack, apart from the frame, its shadow and its flag byte *)
assert (KLOC : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
    (exists p n, In (p, n) (ablocks B ly6 S6) /\ p <= a < p + req_size n)) ->
  0 <= a < alloc_ceiling /\ ~ (F <= a < F + 128) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 16) /\ a <> FL).
{ intros a [Ha | [Ha | (p & n & Hpn & Hpa)]].
  - unfold A_G_REC, REC_SIZE in Ha. lia.
  - unfold A_REC_SPILL, SC_SIZE in Ha. lia.
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR6 Hpn) as (_ & Hp4096 & Hpceil & Hpapp & Hpres & _).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ p n 1 fpos HAR6 Hpn Hfin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd. change (fs_frame_bytes 1) with 128 in Hd.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
    split; [lia|]. split; [lia|]. split; [lia|].
    intros ->. exact (proj2 (Hpres FL ltac:(lia)) HFLo). }
(* the flag byte's region, written by the release (B_answer_code.v:1208-1215) *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssv ?msv =>
pose proof (st_ok_pi_add_region Ev ssv msv scb4_relfbR HS eq_refl
ltac:(unfold region_ok, scb4_relfbR; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
rewrite U47; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
intros o Ho; apply (apresent_writable SEGS); replace (FL + o) with FL by lia; exact HFLp)
ltac:(unfold scb4_relss, scb4_relregions, scb4_relsaveR, scb4_relwordsR, scb4_relhdrR, scb4_relflgR, scb4_relshdR, scb4_relfbR;
cbn [all_disjoint ss_mem]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite U47, U8, U9, U45, U46; repeat split; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_ssp HS.
(* 0x8c47c .. 0x8c558: the magic at F, f5 at the frame's 16 shadow bytes, the flag byte := 0 (the release), the
   saved registers back, sp := s0 - 192 + 192; the run stops at `ret` *)
unfold cfg_at. change (w64 (BASE + SCB_REL)) with (Z_to_bv 64 (BASE + SCB_REL)).
pose (RUNF := aj_flag_store_pi B LAWS (YG05.model_laws_ok (as_universe B) (YF0m.ts_universe B HB)) AFREE_LAW FFL).
paj_run_flag_sh RUNF HS HJ6.
- lia.
- intros a (r & Hin & Hr).
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end.
  destruct Hin as [<- | Hin];
  [right; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite U47 in Hr;
   change (flag_addr ly6 1 fpos) with FL; lia|].
  left.
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?U8, ?U9, ?U45, ?U46 in Hr;
    first [ exfalso; lia | left; lia
    | right; right; right; left; exists 1, fpos; split; [left; reflexivity|];
      change (frame_addr ly6 1 fpos) with F;
      first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia
            | right; unfold in_zr, shadow_addr; cbn [fst snd]; rewrite <- SB_SHADOW_OFF;
              change (fs_frame_bytes 1 / 8) with 16; lia ] ] |]).
  destruct Hin.
- intros msr HSr. change (flag_addr ly6 1 fpos) with FL.
  pose proof (st_ok_pi_region_nth E _ _ 0 _ HSr eq_refl) as HR0.
  pose proof (field_of_region E _ 47 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR0 U47 ltac:(cbn [In]; tauto) eq_refl
    ltac:(lia) ltac:(lia)) as HV.
  specialize (HV 0%nat ltac:(lia)). rewrite !Z.add_0_r in HV. rewrite HV. reflexivity.
- cbn [ms_mem mkst] in HFr.
  preg HS (1%bv : bv 5) R1. preg HS (2%bv : bv 5) R2. preg HS (3%bv : bv 5) R3. preg HS (4%bv : bv 5) R4.
  preg HS (8%bv : bv 5) R8. preg HS (9%bv : bv 5) R9. preg HS (10%bv : bv 5) R10.
  preg HS (18%bv : bv 5) R18. preg HS (19%bv : bv 5) R19. preg HS (20%bv : bv 5) R20.
  preg HS (21%bv : bv 5) R21. preg HS (22%bv : bv 5) R22. preg HS (23%bv : bv 5) R23.
  preg HS (24%bv : bv 5) R24. preg HS (25%bv : bv 5) R25. preg HS (26%bv : bv 5) R26.
  preg HS (27%bv : bv 5) R27.
  assert (X0 : ew E 32 = getr regs (Z_to_bv 5 1)) by exact (EX 0%nat ltac:(lia)).
  assert (X1 : ew E 33 = getr regs (Z_to_bv 5 8)) by exact (EX 1%nat ltac:(lia)).
  assert (X2 : ew E 34 = getr regs (Z_to_bv 5 9)) by exact (EX 2%nat ltac:(lia)).
  assert (X3 : ew E 35 = getr regs (Z_to_bv 5 18)) by exact (EX 3%nat ltac:(lia)).
  assert (X4 : ew E 36 = getr regs (Z_to_bv 5 19)) by exact (EX 4%nat ltac:(lia)).
  assert (X5 : ew E 37 = getr regs (Z_to_bv 5 20)) by exact (EX 5%nat ltac:(lia)).
  assert (X6 : ew E 38 = getr regs (Z_to_bv 5 21)) by exact (EX 6%nat ltac:(lia)).
  assert (X7 : ew E 39 = getr regs (Z_to_bv 5 22)) by exact (EX 7%nat ltac:(lia)).
  assert (X8 : ew E 40 = getr regs (Z_to_bv 5 23)) by exact (EX 8%nat ltac:(lia)).
  assert (X9 : ew E 41 = getr regs (Z_to_bv 5 24)) by exact (EX 9%nat ltac:(lia)).
  assert (X10 : ew E 42 = getr regs (Z_to_bv 5 25)) by exact (EX 10%nat ltac:(lia)).
  assert (X11 : ew E 43 = getr regs (Z_to_bv 5 26)) by exact (EX 11%nat ltac:(lia)).
  assert (X12 : ew E 44 = getr regs (Z_to_bv 5 27)) by exact (EX 12%nat ltac:(lia)).
  assert (P1 : getr (ms_regs ms) 1 = getr regs 1)
    by (rewrite R1, scb_denot_off0, X0; f_equal; try (apply bv_eq; reflexivity)).
  assert (P2 : getr (ms_regs ms) 2 = getr regs 2).
  { rewrite R2, scb_denot_off0, (EL 8%nat 8%bv eq_refl), H8. unfold w64, spZ. apply Z_to_bv_bv_unsigned. }
  assert (P3 : getr (ms_regs ms) 3 = getr regs 3) by (rewrite R3, scb_denot_off0, (EL 3%nat 3%bv eq_refl); exact H3).
  assert (P4 : getr (ms_regs ms) 4 = getr regs 4) by (rewrite R4, scb_denot_off0, (EL 4%nat 4%bv eq_refl); exact H4).
  assert (P10 : getr (ms_regs ms) 10 = w64 q)
    by (rewrite R10, scb_denot_off0, (EL 10%nat 10%bv eq_refl); exact H10).
  assert (P8 : getr (ms_regs ms) 8 = getr regs 8)
    by (rewrite R8, scb_denot_off0, X1; f_equal; try (apply bv_eq; reflexivity)).
  assert (P9 : getr (ms_regs ms) 9 = getr regs 9)
    by (rewrite R9, scb_denot_off0, X2; f_equal; try (apply bv_eq; reflexivity)).
  assert (P18 : getr (ms_regs ms) 18 = getr regs 18)
    by (rewrite R18, scb_denot_off0, X3; f_equal; try (apply bv_eq; reflexivity)).
  assert (P19 : getr (ms_regs ms) 19 = getr regs 19)
    by (rewrite R19, scb_denot_off0, X4; f_equal; try (apply bv_eq; reflexivity)).
  assert (P20 : getr (ms_regs ms) 20 = getr regs 20)
    by (rewrite R20, scb_denot_off0, X5; f_equal; try (apply bv_eq; reflexivity)).
  assert (P21 : getr (ms_regs ms) 21 = getr regs 21)
    by (rewrite R21, scb_denot_off0, X6; f_equal; try (apply bv_eq; reflexivity)).
  assert (P22 : getr (ms_regs ms) 22 = getr regs 22)
    by (rewrite R22, scb_denot_off0, X7; f_equal; try (apply bv_eq; reflexivity)).
  assert (P23 : getr (ms_regs ms) 23 = getr regs 23)
    by (rewrite R23, scb_denot_off0, X8; f_equal; try (apply bv_eq; reflexivity)).
  assert (P24 : getr (ms_regs ms) 24 = getr regs 24)
    by (rewrite R24, scb_denot_off0, X9; f_equal; try (apply bv_eq; reflexivity)).
  assert (P25 : getr (ms_regs ms) 25 = getr regs 25)
    by (rewrite R25, scb_denot_off0, X10; f_equal; try (apply bv_eq; reflexivity)).
  assert (P26 : getr (ms_regs ms) 26 = getr regs 26)
    by (rewrite R26, scb_denot_off0, X11; f_equal; try (apply bv_eq; reflexivity)).
  assert (P27 : getr (ms_regs ms) 27 = getr regs 27)
    by (rewrite R27, scb_denot_off0, X12; f_equal; try (apply bv_eq; reflexivity)).
  (* g_rec, record.spill and the live blocks are outside the run's write windows *)
  assert (KEEP : forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
      (exists p n, In (p, n) (ablocks B ly6 S6) /\ p <= a < p + req_size n)) ->
      rdW W6 (ms_mem ms) a = rdW W6 mem6 a).
  { intros a Ha. destruct (KLOC a Ha) as (Ha0 & HnF & HnS & HnFL).
    apply (recb_run_keeps_m E _ (w_H W6) mem6 (ms_mem ms) a HFr); [lia|].
    nwin_tac ltac:(fun H => rewrite ?U8, ?U9, ?U45, ?U46, ?U47 in H; lia). }
  (* the return *)
  eapply (paj_ret_at (PL := PL_cmd) (PI := PI) W6 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold scb_postF.
  pose proof (ajournal_materialize SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat' HJ6) as HJm.
  exists fxv. eexists ly6, (stack_free_state 1 fpos S6), (ms_regs ms), (ms_mem ms), _.
  pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
  split; [rewrite P1, Hra'; reflexivity|].
  split; [exact HFX|].
  split; [eapply (ajournal_mono_k SEGS B); [exact HJm | exact Hkk]|].
  split; [apply aregs_preserved_eqs; assumption|].
  cbv beta. split; [exact P10|].
  apply HQQ; [exact (proj1 HJm) | apply wle_refl | exact KEEP].
Qed.
End rel.

(* ---------- the tail segment: 0x8c444 .. the call of answer, then the release segment ---------- *)
Section tail.
(* the statement's data *)
Variables (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte).
Variables (md : Model) (ch : list (Z * Z * Z)) (id pids : Z) (ids : list Z) (R : rstate) (O : list (Z * Z)).
(* the loop's first arrival, the frame and the text block, and the blocks record() and the two arg_s calls made *)
Variables (lyL : alayout) (SL : astate) (WL : world SEGS) (memL : word -> option byte) (mdL : Model).
Variables (fpos lst : Z) (bl1 Frec O1 : list (Z * Z)) (p1 p2 : Z).
(* the entry's FP registers and fcsr, which the post compares against *)
Variables (fr0 : bvmap 5 word) (csr0 : bv 32).

Lemma scb_tail : forall (fx0 : YK11.FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
afn_pre SEGS B SUP_CHAIN_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
-2 ^ 31 <= id < 2 ^ 31 ->
(1 <= length ids <= 62)%nat -> Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids ->
rec_repA B ly S (rdW W mem) R O ->
Z.of_nat (length (frames S)) <= 7 ->
st_nev S + EV_SUP_CHAIN R <= EV_MAX -> blocks_bytes S + LIVE_SUP_CHAIN R id ids <= LIVE_MAX ->
mo_ok MT S (XM_SUP_CHAIN MT R id ids) ->
scb_lctx B MT ly S W regs mem md id pids ids R O lyL SL WL memL mdL fpos lst bl1 Frec O1 p1 p2 ->
scb_frm0 fx0 -> scb_fxok fr0 csr0 fx0 ->
scb_inv B ly S W regs mem md pids ids R O lyL SL WL memL fpos lst (length ids) regs' mem' md' ->
SRr SEGS WL (@cfg_at fx0 SEGS (BASE + SCB_LEXIT) regs' mem' md')
(scb_postF B fr0 csr0 SUP_CHAIN_STK (SCB_FP O) regs ly S W mem md (EV_SUP_CHAIN R)
(fun ly' S' W' regs2 mem2 md2 => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 sup_chain_m R id ids = (R', t) /\
 getr regs2 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem2) R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\
 ~ In q (map fst O') /\
 astr_atR (rdW W' mem2) q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_CHAIN R id ids /\
 mo_le MT S S' (XM_SUP_CHAIN MT R id ids))).
Proof.
intros fx0 regs' mem' md' HPRE HROD Hid Hids HidsF HREP Hfr Hev Hlive MOK HLC HRM0 HFXOK HINV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (pa_base_lo (PL := PL_cmd)) as HBLO.
pose proof asan_consts as (CA1 & CA2 & CA3 & CA4 & CA5).
assert (HSTK : SUP_CHAIN_STK = 16800) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity. assert (Has : ASTACK = 16384) by reflexivity.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hchain & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HINV as (Hkn & HJL & Hsp' & Hgp' & Htp' & R8' & R9' & R18' & R19' & R20' & R21' & R22' & R23' & R24' &
  R25' & R26' & R27' & HTXT & HKEEP).
destruct HLC as (HJ0 & HPerm0 & HFrecO & HFrecN & HO1 & HPermL & HApL & HAp1 & HAp2 & Hp14096 & Hp24096 & Hlst4096 &
  HREPL & HBBL & HMLEL & HFRM & HWORDS & HFSH & HFLG & HLST0 & HPIDS & HPRNG & HAPlp & HPIDC & HRODL).
set (n := Z.of_nat (length ids)) in *.
set (sp0 := spZ regs) in *.
rewrite (scb_dec_list_all ids) in HTXT.
pose proof (proj1 HJL) as HARL.
pose proof HJL as (_ & HlyL & _ & _ & _ & HfrsL & HnevL & _ & _ & _ & _ & _ & _ & HpresL & _).
assert (Hfin : In (1, fpos) (frames SL)) by (rewrite HfrsL; left; reflexivity).
unfold scb_words in HWORDS. destruct HWORDS as (HW8 & HW16 & HW24 & HW32 & HW40 & HW48 & HW56 & HW80).
(* the frame, the text block and the stack: where they are *)
set (F := frame_addr lyL 1 fpos) in *. set (FL := flag_addr lyL 1 fpos) in *.
destruct (scb_sp1_facts sp0 Hal16 ltac:(lia)) as (Hsp1 & Hsp1a & Hsp1b).
change (32 * ((sp0 - 192) / 32)) with (scb_sp1 sp0) in Hsp1, Hsp1a, Hsp1b.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 fpos HARL Hfin) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp. fold F in HF4096, HFceil, HFapp.
assert (HLin : In (lst, 12 * n + 1) (ablocks B lyL SL))
  by (apply (Permutation_in _ (Permutation_sym HPermL)); right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ lst (12 * n + 1) HARL HLin) as (_ & _ & Hlstceil & _ & _ & _ & _).
assert (Hn62 : 1 <= n <= 62) by (unfold n; lia).
pose proof (req_size_pos (12 * n + 1) ltac:(lia)) as [RL1 RL2].
(* every byte the loop could have changed is in the text block or below sp1; the frame, the stack words and the
   saved registers are not *)
assert (HLO : alloc_ceiling + 16592 <= scb_sp1 sp0) by lia.
assert (HES3 : 3 * ESTACK = 12288) by reflexivity.
assert (KF : forall a, F <= a < F + 128 -> rdW WL mem' a = rdW WL memL a).
{ intros a Ha. pose proof (sep_block_frame SEGS B LAWS lyL SL WL mem' md' lst (12 * n + 1) 1 fpos HARL HLin Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd. change (fs_frame_bytes 1) with 128 in Hd.
  apply HKEEP; [lia | lia | rewrite HES3; lia]. }
assert (KS : forall a, scb_sp1 sp0 + 8 <= a < sp0 -> rdW WL mem' a = rdW WL memL a).
{ intros a Ha. apply HKEEP; [lia | lia | rewrite HES3; lia]. }
(* the memory facts of the first arrival, at the loop's exit *)
assert (HFRM' : scb_frame_at (mrestrict (w_H WL) mem') sp0 regs).
{ intros j r Hj. apply (recb_val_mem_frame_m (w_H WL) (w_H WL) memL mem' _ 8%nat); [exact (HFRM j r Hj)|].
  intros i Hi. apply KS.
  pose proof (proj1 (nth_error_Some scb_saved j) ltac:(rewrite Hj; discriminate)) as Hj13.
  unfold scb_saved in Hj13. cbn [length] in Hj13. lia. }
assert (HW8' : val_mem SEGS (mrestrict (w_H WL) mem') (scb_sp1 sp0 + 8) 8 (rec_slot R))
  by (apply (recb_val_mem_frame_m (w_H WL) (w_H WL) memL mem' _ 8%nat); [exact HW8 | intros i Hi; apply KS; lia]).
assert (HW16' : val_mem SEGS (mrestrict (w_H WL) mem') (scb_sp1 sp0 + 16) 8 F)
  by (apply (recb_val_mem_frame_m (w_H WL) (w_H WL) memL mem' _ 8%nat); [exact HW16 | intros i Hi; apply KS; lia]).
assert (HW24' : val_mem SEGS (mrestrict (w_H WL) mem') (scb_sp1 sp0 + 24) 8 (SB + F / 8))
  by (apply (recb_val_mem_frame_m (w_H WL) (w_H WL) memL mem' _ 8%nat); [exact HW24 | intros i Hi; apply KS; lia]).
assert (HW32' : val_mem SEGS (mrestrict (w_H WL) mem') (scb_sp1 sp0 + 32) 8 F)
  by (apply (recb_val_mem_frame_m (w_H WL) (w_H WL) memL mem' _ 8%nat); [exact HW32 | intros i Hi; apply KS; lia]).
destruct (FFL _ _ _ _ _ 1 fpos HARL Hfin) as (_ & _ & _ & (HFL4096 & _ & HFLceil)). fold FL in HFL4096, HFLceil.
assert (HFLG' : rdword (rdW WL mem') (F + 120) = Some FL)
  by (apply (scb4_rdword_kept WL memL mem' _ FL ltac:(lia) HFLG); intros i Hi; apply KF; lia).
assert (Hslot : 0 <= rec_slot R < 2 ^ 64).
{ unfold rec_slot. destruct (Nat.ltb (length (r_calls R)) 16) eqn:Ek.
  - apply Nat.ltb_lt in Ek. unfold A_G_REC, OFF_CALLS, CALL_SIZE. lia.
  - unfold A_REC_SPILL. lia. }
pose proof (scb4_seed fx0 lyL SL WL regs' regs mem' md' fpos (rec_slot R) HARL Hfin
  ltac:(rewrite HSTK in *; lia) Hal16 HpresL Hsp' R8' R9' Hslot HFRM' HW8' HW16' HW24' HW32' HFLG') as HS.
fold F in HS. fold FL in HS.
remember (Eimg (Ereg regs' (scb4_ext regs (rec_slot R) F FL))) as E0 eqn:HE0 in HS.
assert (HEI : img_env VAL A_LIM E0) by (rewrite HE0; apply Eimg_env).
assert (EL0 : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E0 m = getr regs' r).
{ intros m r Hm. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite HE0, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX0 : forall j, (j < 17)%nat -> ew E0 (32 + j) = nth j (scb4_ext regs (rec_slot R) F FL) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HE0, Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
clear HE0.
assert (V8 : bv_unsigned (ew E0 8) = sp0)
  by (rewrite (EL0 8%nat 8%bv eq_refl), R8'; unfold w64; apply unsigned_lit_small; lia).
assert (V9 : bv_unsigned (ew E0 9) = scb_sp1 sp0)
  by (rewrite (EL0 9%nat 9%bv eq_refl), R9'; unfold w64; apply unsigned_lit_small; lia).
assert (E45' : ew E0 45 = Z_to_bv 64 (rec_slot R)) by (exact (EX0 13%nat ltac:(lia))).
assert (E46' : ew E0 46 = Z_to_bv 64 F) by (exact (EX0 14%nat ltac:(lia))).
assert (V45 : bv_unsigned (ew E0 45) = rec_slot R)
  by (rewrite E45'; apply unsigned_lit_small; lia).
assert (V46 : bv_unsigned (ew E0 46) = F)
  by (rewrite E46'; apply unsigned_lit_small; lia).
assert (V22 : ew E0 22 = w64 lst) by (rewrite (EL0 22%nat 22%bv eq_refl); exact R22').
(* run 1: the slot from sp1 + 8, the arguments, the call of arg_s *)
pose (RUNP := SRr_run_pi_AJ (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS).
pose (RUNC := SRr_run_pi_AJ_call (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS).
unfold cfg_at. change (w64 (BASE + SCB_LEXIT)) with (Z_to_bv 64 (BASE + SCB_LEXIT)).

paj_run_shc RUNP RUNC HS HJL.
{ unfold scb4_ss, scb4_saveR, scb4_wordsR, scb4_flgR. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 8%nat) (d := 0);
  [reflexivity | rewrite V8; lia | cbn; rewrite HSTK; lia | cbn; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  eapply (YCbq.awr_ok_cons_gen SEGS B) with (k := 46%nat); [reflexivity | exact V46 |
  intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists 1, fpos;
  split; [left; reflexivity|];
  left; unfold in_zr; cbn [fst snd]; fold F; change (fs_frame_bytes 1) with 128; lia |].
  apply (awr_ok_nil SEGS B). }
rename ms into msA, mat into matA, HF into HFA, HFr into HFrA, HG into HGA.
(* the facts the callees share: the footprint lies below the allocator's ceiling, the read-only bytes are off it *)
assert (HOS : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hpn; exact (rec_repA_in ly S _ R O HREP pn Hpn)).
assert (HFPlo : forall a, inFP (SCB_FP O) a -> a < alloc_ceiling).
{ intros a (r & Hr & Hra2). unfold SCB_FP in Hr.
  destruct Hr as [<- | [<- | Hr]].
  - cbn [fst snd] in Hra2. unfold A_G_REC, REC_SIZE in *. lia.
  - cbn [fst snd] in Hra2. unfold A_REC_SPILL, SC_SIZE in *. lia.
  - destruct (inFP_ablocks_fp_inv O a ltac:(exists r; split; [exact Hr | exact Hra2])) as (q0 & nq & Hin & Hr2).
    destruct (al_blocks SEGS B LAWS ly S W mem md q0 nq HAR (HOS _ Hin)) as (_ & _ & Hpceil & _). lia. }
assert (HFPRO : forall a, in_roP SEGS RLO RHI a -> ~ inFP (SCB_FP O) a).
{ intros a Hro Hfp. destruct (cmd_ro_prog_apart a Hro) as [Himg Hpg].
  unfold SCB_FP in Hfp. destruct Hfp as (r & Hr & Hra2).
  destruct Hr as [<- | [<- | Hr]].
  - cbn [fst snd] in Hra2. apply Hpg. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_G_REC, REC_SIZE in *. lia.
  - cbn [fst snd] in Hra2. apply Hpg. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd].
    unfold A_REC_SPILL, SC_SIZE in *. lia.
  - destruct (inFP_ablocks_fp_inv O a ltac:(exists r; split; [exact Hr | exact Hra2])) as (q0 & nq & Hin & Hr2).
    exact (proj2 (al_client_img _ _ LAWS ly S W mem md a HAR
      (or_introl (ex_intro _ q0 (ex_intro _ nq (conj (HOS _ Hin) Hr2))))) Himg). }
(* the walk's stack facts at the run's end *)
pose proof HlyL as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (HNFP : forall a, sp0 - 104 <= a < 2 ^ 64 -> ~ inFP (SCB_FP O) a)
  by (intros a Ha Hf; pose proof (HFPlo a Hf); lia).
(* the frame does not meet the image: the recorder's bytes and the live blocks are apart from it *)
pose proof (frm_off_imgP B lyL SL WL mem' md' 1 fpos HARL Hfin) as HFoff.
change (fs_frame_bytes 1) with 128 in HFoff. fold F in HFoff. unfold off_img in HFoff.
assert (HBLKF : forall p nn a, In (p, nn) (ablocks B lyL SL) -> p <= a < p + req_size nn ->
  a < alloc_ceiling /\ ~ (F <= a < F + 128)).
{ intros p nn a Hin Ha.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p nn HARL Hin) as (_ & Hp4096 & Hpceil & _ & _ & _ & _).
  pose proof (sep_block_frame SEGS B LAWS lyL SL WL mem' md' p nn 1 fpos HARL Hin Hfin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd. change (fs_frame_bytes 1) with 128 in Hd.
  split; lia. }
(* the bytes of the recorder: in g_rec, in record.spill, or in one of its blocks at the loop's first arrival *)
set (OL := (p2, scb_m n) :: (p1, scb_m id) :: O1) in *.
assert (HOLin : forall pn, In pn OL -> In pn (ablocks B lyL SL))
  by (intros pn Hpn; exact (rec_repA_in lyL SL _ _ OL HREPL pn Hpn)).
assert (HOLap : forall pn, In pn OL -> iv_apart lst (12 * n + 1) (fst pn) (snd pn)).
{ intros pn Hpn. unfold OL in Hpn. destruct Hpn as [<- | [<- | Hpn]].
  - pose proof (Forall_inv (Forall_inv_tail HAp2)) as Hx. unfold iv_apart in *. cbn [fst snd] in *. lia.
  - pose proof (Forall_inv HAp1) as Hx. unfold iv_apart in *. cbn [fst snd] in *. lia.
  - assert (Hbl : In pn bl1).
    { pose proof (proj1 (HO1 pn) Hpn) as [HpO HpF].
      pose proof (Permutation_in pn HPerm0 (HOS pn HpO)) as Hx.
      apply in_app_or in Hx as [Hx | Hx]; [exact Hx | exfalso; exact (HpF Hx)]. }
    exact (proj1 (Forall_forall _ _) HApL pn Hbl). }
(* g_rec and record.spill are image bytes, so no live block meets them *)
assert (HRECIMG : forall a, A_G_REC <= a < A_G_REC + 960 \/ A_REC_SPILL <= a < A_REC_SPILL + 56 -> in_img SEGS a).
{ intros a Ha. apply cmd_prog_img. destruct Ha as [Ha | Ha].
  - apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_G_REC in Ha. lia.
  - apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_REC_SPILL in Ha. lia. }
assert (HSLOT : forall a, rec_slot R <= a < rec_slot R + CALL_SIZE ->
  A_G_REC <= a < A_G_REC + 960 \/ A_REC_SPILL <= a < A_REC_SPILL + 56).
{ intros a Ha. unfold rec_slot in Ha. destruct (Nat.ltb (length (r_calls R)) 16) eqn:Ek.
  - apply Nat.ltb_lt in Ek. left.
    assert (Hk : 0 <= Z.of_nat (length (r_calls R)) <= 15) by lia.
    unfold A_G_REC, OFF_CALLS, CALL_SIZE in *. lia.
  - right. unfold A_REC_SPILL, CALL_SIZE in *. lia. }
set (KA := fun a : Z => A_G_REC <= a < A_G_REC + 960 \/ A_REC_SPILL <= a < A_REC_SPILL + 56 \/
  (exists p nn, In (p, nn) OL /\ p <= a < p + nn)) in *.
assert (KALOC : forall a, KA a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 128) /\ ~ (lst <= a < lst + 12 * n + 1)).
{ intros a Ha. destruct Ha as [Ha | [Ha | (p & nn & Hin & Hpa)]].
  - split; [unfold A_G_REC in *; lia|]. split; [unfold A_G_REC in *; lia|].
    intros Hc. exact (blk_img SEGS B LAWS lyL SL WL mem' md' lst (12 * n + 1) a HARL HLin ltac:(lia)
      (HRECIMG a (or_introl Ha))).
  - split; [unfold A_REC_SPILL in *; lia|]. split; [unfold A_REC_SPILL in *; lia|].
    intros Hc. exact (blk_img SEGS B LAWS lyL SL WL mem' md' lst (12 * n + 1) a HARL HLin ltac:(lia)
      (HRECIMG a (or_intror Ha))).
  - pose proof (HOLin (p, nn) Hin) as Hin'.
    pose proof (HOLap (p, nn) Hin) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p nn HARL Hin') as (_ & Hp4096 & Hpceil & _ & _ & _ & Hnn).
    pose proof (req_size_pos nn ltac:(lia)) as [Rq1 Rq2].
    destruct (HBLKF p nn a Hin' ltac:(lia)) as [Hlo2 Hnf]. split; [lia|]. split; [exact Hnf | lia]. }
assert (KALm : forall a, KA a -> rdW WL mem' a = rdW WL memL a).
{ intros a Ha. destruct (KALOC a Ha) as (Hb & _ & Hnl). apply HKEEP; [lia | exact Hnl | rewrite HES3; lia]. }
assert (KAA : forall a, KA a -> rdW WL (ms_mem msA) a = rdW WL memL a).
{ intros a Ha. rewrite <- (KALm a Ha). destruct (KALOC a Ha) as (Hb & HnF & _).
  apply (recb_run_keeps_m E0 _ (w_H WL) mem' (ms_mem msA) a HFrA); [lia|].
  nwin_tac ltac:(fun Hr => rewrite ?V8, ?V9, ?V46 in Hr; lia). }
(* the text block's bytes: the run wrote nothing, so they are the loop's *)
assert (KAA2 : forall a, lst <= a < lst + 12 * n + 1 -> rdW WL (ms_mem msA) a = rdW WL mem' a).
{ intros a Ha. destruct (HBLKF lst (12 * n + 1) a HLin ltac:(lia)) as [Hb Hnf].
  apply (recb_run_keeps_m E0 _ (w_H WL) mem' (ms_mem msA) a HFrA); [lia|].
  nwin_tac ltac:(fun Hr => rewrite ?V8, ?V9, ?V46 in Hr; lia). }
(* the event, live-byte and meter budgets of the three calls left *)
assert (HEVsplit : EV_SUP_CHAIN R = scb_kL R + EV_ARG_S + 1 + EV_ANSWER)
  by (unfold EV_SUP_CHAIN, scb_kL; lia).
assert (HEVans : 0 <= EV_ANSWER) by (vm_compute; discriminate).
assert (HEVas : 0 <= EV_ARG_S) by (vm_compute; discriminate).
assert (HLIVEans : 0 <= LIVE_ANSWER (snd (sup_chain_m R id ids))).
{ unfold LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XMALLOC. lia. }
assert (HXMans : 0 <= XM_ANSWER MT (snd (sup_chain_m R id ids))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XMALLOC.
  pose proof (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1))
    ltac:(unfold LIVE_XMALLOC; lia)).
  pose proof (mo_free_nonneg MT MTL). lia. }
assert (HXMfree : 0 <= mo_free MT) by (exact (mo_free_nonneg MT MTL)).
(* the state at the call of arg_s(slot, list) *)
pmkst HS.
preg HS (1%bv : bv 5) P1. preg HS (2%bv : bv 5) P2. preg HS (3%bv : bv 5) P3. preg HS (4%bv : bv 5) P4.
preg HS (8%bv : bv 5) P8. preg HS (10%bv : bv 5) P10. preg HS (11%bv : bv 5) P11.
rewrite scb_denot_off0 in P2, P3, P4, P8, P10, P11.
cbn [sv_denot] in P1. rewrite (img_env_codeptr E0 HEI 24356) in P1.
rewrite (EL0 2%nat 2%bv eq_refl) in P2.
rewrite (EL0 3%nat 3%bv eq_refl), Hgp' in P3. rewrite (EL0 4%nat 4%bv eq_refl), Htp' in P4.
rewrite (EL0 8%nat 8%bv eq_refl), R8' in P8.
rewrite E45' in P10. rewrite V22 in P11.
pose proof (proj1 HJL) as HARA.
assert (Qsp : spZ (ms_regs msA) = sp0 + (scb_sp1 sp0 - sp0)).
{ unfold spZ at 1. rewrite P2. fold (spZ regs'). rewrite Hsp'. lia. }
assert (HRODA : arodata_okP SEGS RLO RHI B (rdW WL (ms_mem msA)))
  by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := ROB) B _ _ (SCB_FP O) ly S W mem md _ lyL SL WL
       (ms_mem msA) _ (scb_kL R) HJL HFPRO HROD).
pose proof (cmd_ro_ok_of_aro lyL SL WL (ms_mem msA) _ HARA HRODA) as HROA.
assert (HREPA : rec_repA B lyL SL (rdW WL (ms_mem msA)) (rec_record R REC_CHAIN [dec id; dec n]) OL).
{ apply (rec_repA_kept lyL SL (rdW WL memL) lyL SL (rdW WL (ms_mem msA)) _ OL HREPL).
  - exact HOLin.
  - intros a Ha. apply KAA. left. exact Ha.
  - intros a Ha. apply KAA. right. left. exact Ha.
  - intros p nn i Hin Hi. apply KAA. right. right. exists p, nn. split; [exact Hin | lia]. }
assert (HSTRA : astr_atR (rdW WL (ms_mem msA)) lst (dec_list ids)).
{ split; [|apply scb_dec_list_nz].
  pose proof (scb_dec_list_len ids HidsF ltac:(lia)) as HLEN.
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (KAA2 (lst + Z.of_nat i) ltac:(lia)).
  exact (HTXT i ltac:(rewrite length_app; cbn [length]; lia)). }
assert (HARGS : astr_argA B lyL SL (rdW WL (ms_mem msA)) (in_roP SEGS RLO RHI) [] lst (Some (dec_list ids))).
{ pose proof (scb_dec_list_len ids HidsF ltac:(lia)) as HLEN.
  pose proof (scb_text_arg ids HidsF ltac:(lia)) as [_ Hle].
  cbv beta iota zeta delta [astr_argA].
  split; [lia|]. split; [exact HSTRA|]. split; [exact Hle|].
  left. split; [|apply Forall_nil]. exists lst, (12 * n + 1). split; [exact HLin | lia]. }
assert (HTAILA : forall x, Some (dec_list ids) = Some x ->
  atail_vis SEGS WL (ms_mem msA) (lst + Z.of_nat (length x))).
{ intros x Hx. injection Hx as <-. pose proof (scb_dec_list_len ids HidsF ltac:(lia)) as HLEN.
  exact (cmd_heap_tail_vis SEGS B LAWS HB lyL SL WL (ms_mem msA) _ lst (12 * n + 1)
    (lst + Z.of_nat (length (dec_list ids))) HARA HLin ltac:(lia)). }
assert (HevA : st_nev SL + EV_ARG_S <= EV_MAX).
{ unfold EV_SUP_CHAIN in Hev. unfold scb_kL in HnevL. lia. }
assert (HliveA : blocks_bytes SL + LIVE_ARG_S (Some (dec_list ids)) <= LIVE_MAX).
{ unfold LIVE_SUP_CHAIN in Hlive. fold n in Hlive. lia. }
assert (HxmA : 0 <= XM_ARG_S MT (Some (dec_list ids))).
{ unfold XM_ARG_S, XM_XMALLOC.
  exact (mo_malloc_nonneg MT MTL (LIVE_XMALLOC (Z.of_nat (length (sarg (Some (dec_list ids)))) + 1))
    ltac:(unfold LIVE_XMALLOC; lia)). }
assert (HmokA : mo_ok MT SL (XM_ARG_S MT (Some (dec_list ids)))).
{ apply (mok_station MT S SL (XM_SUP_CHAIN MT R id ids)
    (XM_RECORD MT R + XM_XMALLOC MT (12 * n + 1) + XM_ARG_S MT (Some (dec id)) + XM_ARG_S MT (Some (dec n)))
    (XM_ARG_S MT (Some (dec_list ids))) MTL MOK HMLEL HxmA).
  unfold XM_SUP_CHAIN. fold n. lia. }
(* the frame chain the callees see: this call's frame record (ra, the caller's s0) on the entry's chain *)
assert (E32' : ew E0 32 = getr regs (Z_to_bv 5 1)) by (exact (EX0 0%nat ltac:(lia))).
assert (E33' : ew E0 33 = getr regs (Z_to_bv 5 8)) by (exact (EX0 1%nat ltac:(lia))).
assert (Hal8 : sp0 mod 8 = 0).
{ pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hal16 in D.
  rewrite D. replace (16 * (sp0 / 16) + 0) with ((2 * (sp0 / 16)) * 8) by lia. apply Z_mod_mult. }
assert (Hs0A : s0Z (ms_regs msA) = sp0)
  by (unfold s0Z; rewrite P8; unfold w64; apply unsigned_lit_small; lia).
pose proof (st_ok_region_nth E0 _ _ 0%nat _ HS eq_refl) as HR0. cbn [ms_mem restrict mkst] in HR0.
assert (HRAw : rdword (rdW WL (ms_mem msA)) (sp0 - 8) = Some (raZ regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
  replace (sp0 - 8) with (sp0 + -8) by lia.
  refine (field_of_region E0 _ 8%nat sp0 _ (-104) 0 (-104) 0 (-8) 8%N (SOff 32 0) (raZ regs) HR0 V8 _ _ _ _);
  [ cbn [In]; tauto
  | rewrite scb_denot_off0, E32'; unfold raZ; rewrite Z_to_bv_bv_unsigned; reflexivity
  | unfold raZ; apply bv_unsigned_in_range | lia ]. }
assert (HS0w : rdword (rdW WL (ms_mem msA)) (sp0 - 16) = Some (s0Z regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
  replace (sp0 - 16) with (sp0 + -16) by lia.
  refine (field_of_region E0 _ 8%nat sp0 _ (-104) 0 (-104) 0 (-16) 8%N (SOff 33 0) (s0Z regs) HR0 V8 _ _ _ _);
  [ cbn [In]; tauto
  | rewrite scb_denot_off0, E33'; unfold s0Z; rewrite Z_to_bv_bv_unsigned; reflexivity
  | unfold s0Z; apply bv_unsigned_in_range | lia ]. }
pose proof HJL as (_ & _ & _ & _ & _ & _ & _ & _ & FJ1 & _).
assert (HKEEPup : forall a, sp0 <= a < 2 ^ 64 -> rdW WL (ms_mem msA) a = rdW W mem a)
  by (intros a Ha; apply FJ1; [lia | lia | apply HNFP; lia]).
assert (HCHA : exists ch1, achain lyL (rdW WL (ms_mem msA)) (sp0 + (scb_sp1 sp0 - sp0)) (s0Z (ms_regs msA)) ch1).
{ rewrite Hs0A. destruct (Z_lt_le_dec sp0 (ly_top lyL - 16)) as [Hlt | Hge].
  - exists ((sp0, raZ regs, s0Z regs) :: ch).
    eapply (achain_push lyL (rdW W mem) (rdW WL (ms_mem msA)) sp0 (s0Z regs) (raZ regs) ch);
    [ exact (achain_ly_top ly lyL _ _ _ _ Etop Hchain) | rewrite Etop; lia | exact HKEEPup
    | exact HRAw | exact HS0w | exact Hra4 | lia | exact Hal8 | exact Hlt | lia ].
  - exists []. left. split; [right; left; lia | reflexivity]. }
destruct HCHA as (chA & HCHA).
assert (SIGAS : SIG CS_arg_s = BASE + AF_arg_s)
  by (destruct (scb_sigs cmd_sig_prog_PB) as (_ & _ & Hx & _); exact Hx).
rewrite SIGAS.
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS WL (ms_regs msA) (ms_mem msA) _ SUP_CHAIN_STK sp0 (SCB_FP O) ly S W mem md
    [(1, fpos)] lyL SL _ (scb_kL R) ARG_S_STK _ EV_ARG_S (scb_sp1 sp0 - sp0) (getr (ms_regs msA) 1) chA _ HJL Qsp);
  [ exact Hsp1b | lia | unfold ARG_S_STK, XMALLOC_STK, ASTACK, ESTACK; lia
  | unfold ARG_S_STK, XMALLOC_STK, ASTACK, ESTACK; rewrite HSTK; lia
  | exact P3 | exact P4 | reflexivity
  | rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite P1, unsigned_lit_small by lia; lia
  | exact HCHA
  | intros HPRE1;
    exact (TARG_S fx0 lyL SL WL (ms_regs msA) (ms_mem msA) _ chA (rec_slot R) lst REC_CHAIN
      [dec id; dec n] (Some (dec_list ids)) R OL HPRE1 HRODA HROA P10 P11 eq_refl HREPA
      (or_introl HARGS) HTAILA
      HevA HliveA HmokA)
  | intros a Ha; destruct Ha as (r & Hr & Hrq); cbn in Hr;
    assert (Hslotr : rec_slot R <= a < rec_slot R + CALL_SIZE)
      by (destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrq; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; cbn in Hrq; lia);
    pose proof (HSLOT a Hslotr) as Hsr;
    right; right; right; right; left;
    split; [destruct Hsr as [Hx | Hx];
      [exists (A_G_REC, A_G_REC + REC_SIZE); split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE; lia]
      |exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE); split; [right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE; lia]]|];
    split; [rewrite (YF0m.ts_prog B HB); destruct Hsr as [Hx | Hx];
      [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_G_REC in *; lia
      |apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold A_REC_SPILL in *; lia]
      | exact (HRECIMG a Hsr)]
  | intros ly2 S2 W2 regs2 mem2 md2 HK a Ha Hw Hn; exfalso;
    destruct Ha as (r & Hr & Hrq); cbn in Hr;
    assert (Hslotr : rec_slot R <= a < rec_slot R + CALL_SIZE)
      by (destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrq; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; cbn in Hrq; lia);
    pose proof (HSLOT a Hslotr) as Hsr;
    destruct Hsr as [Hx | Hx]; unfold A_G_REC, A_REC_SPILL in *; lia ]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJ2c & HP2 & HK2).
rewrite P1.
destruct HK2 as (HBB2 & HMLE2 & [(Hn6 & _ & _) | (_ & pq & Hpq)]).
{ exfalso. cbn in Hn6. unfold REC_ARGS_MAX in Hn6. lia. }
cbv zeta in Hpq. destruct Hpq as (Hpq4096 & Hperm2 & Hfresh2 & HREP2).
pose proof (proj1 HJ2) as HAR2.
pose proof HJ2c as (_ & Hly2 & _ & _ & _ & Hfrs2 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HARA Hly2) as (Eab2 & Efa2 & _).
assert (EFA2 : frame_addr ly2 1 fpos = F) by (rewrite Efa2; reflexivity).
assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; exact Hfin).
destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR2 Hfin2) as (_ & _ & HFpres2 & _).
rewrite EFA2 in HFpres2. change (fs_frame_bytes 1) with 128 in HFpres2.
assert (HnFP1 : forall a, rec_slot R <= a < rec_slot R + CALL_SIZE -> False -> False) by (intros; assumption).
jafter_call_keep_pi HS 49%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0;1;2]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_stack_sub SEGS B E0 _ _ _ lyL SL WL (ms_mem msA) _ ly2 S2 W2 mem2 md2 _ 8%nat
      (-104) 0 (-104) 0 _ sp0 SUP_CHAIN_STK sp0 (SCB_FP O) ly S W mem md [(1, fpos)] _ HJ2c HJ2 V8);
    [ lia | rewrite HSTK; lia | lia | lia | lia |].
    intros a Ha Hf. destruct Hf as (r & Hr & Hrq). cbn in Hr.
    assert (Hslotr : rec_slot R <= a < rec_slot R + CALL_SIZE)
      by (destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrq;
          unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; cbn in Hrq; lia).
    destruct (HSLOT a Hslotr) as [Hx | Hx]; unfold A_G_REC, A_REC_SPILL in *; lia.
  - eapply (region_kept_stack_sub SEGS B E0 _ _ _ lyL SL WL (ms_mem msA) _ ly2 S2 W2 mem2 md2 _ 9%nat
      8 40 8 8 _ (scb_sp1 sp0) SUP_CHAIN_STK sp0 (SCB_FP O) ly S W mem md [(1, fpos)] _ HJ2c HJ2 V9);
    [ lia | rewrite HSTK; lia | lia | lia | lia |].
    intros a Ha Hf. destruct Hf as (r & Hr & Hrq). cbn in Hr.
    assert (Hslotr : rec_slot R <= a < rec_slot R + CALL_SIZE)
      by (destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrq;
          unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; cbn in Hrq; lia).
    destruct (HSLOT a Hslotr) as [Hx | Hx]; unfold A_G_REC, A_REC_SPILL in *; lia.
  - eapply (region_kept_frame_sub (segs := SEGS) B E0 _ _ _ lyL SL WL (ms_mem msA) _ ly2 S2 W2 mem2 md2 _
      46%nat F 120 128 120 120 _ 1 fpos HJ2c V46 Hfin);
    [ lia | change (fs_frame_bytes 1) with 128; lia | | intros a Ha; lia ].
    intros a Ha Hf. destruct Hf as (r & Hr & Hrq). cbn in Hr.
    assert (Hslotr : rec_slot R <= a < rec_slot R + CALL_SIZE)
      by (destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrq;
          unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; cbn in Hrq; lia).
    destruct (HSLOT a Hslotr) as [Hx | Hx]; unfold A_G_REC, A_REC_SPILL in *; lia. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
remember (havoc E0 49 (map (getr regs2) CLOB)) as E1 eqn:HE1 in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall m, (m < 49)%nat -> ew E1 m = ew E0 m) by (intros m Hm; rewrite HE1; apply ew_havoc_old; exact Hm).
clear HE1.
assert (W8 : bv_unsigned (ew E1 8) = sp0) by (rewrite OLD1 by lia; exact V8).
assert (W9 : bv_unsigned (ew E1 9) = scb_sp1 sp0) by (rewrite OLD1 by lia; exact V9).
assert (W46 : bv_unsigned (ew E1 46) = F) by (rewrite OLD1 by lia; exact V46).
(* the frame chain at any later state of the walk *)
assert (CHAIN : forall (lyx : alayout) (Wx : world SEGS) (memx : word -> option byte),
  ly_top lyx = ly_top ly ->
  (forall a, sp0 <= a < 2 ^ 64 -> rdW Wx memx a = rdW W mem a) ->
  rdword (rdW Wx memx) (sp0 - 8) = Some (raZ regs) ->
  rdword (rdW Wx memx) (sp0 - 16) = Some (s0Z regs) ->
  exists ch1, achain lyx (rdW Wx memx) (scb_sp1 sp0) sp0 ch1).
{ intros lyx Wx memx Etx Hk H8 H16. destruct (Z_lt_le_dec sp0 (ly_top lyx - 16)) as [Hlt | Hge].
  - exists ((sp0, raZ regs, s0Z regs) :: ch).
    eapply (achain_push lyx (rdW W mem) (rdW Wx memx) sp0 (s0Z regs) (raZ regs) ch);
    [ exact (achain_ly_top ly lyx _ _ _ _ Etx Hchain) | rewrite Etx; lia | exact Hk | exact H8 | exact H16
    | exact Hra4 | lia | exact Hal8 | exact Hlt | lia ].
  - exists []. left. split; [right; left; lia | reflexivity]. }
(* run 2: a0 := list, the call of the free wrapper *)
paj_run_shc RUNP RUNC HS HJ2.
{ unfold scb4_saveR, scb4_wordsR, scb4_flgR. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 8%nat) (d := 0);
  [reflexivity | rewrite W8; lia | cbn; rewrite HSTK; lia | cbn; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  apply (awr_ok_nil SEGS B). }
rename ms into msB, mat into matB, HF into HFB, HFr into HFrB, HG into HGB.
pmkst HS. rewrite (pal_free B TL).
preg HS (1%bv : bv 5) Q1. preg HS (2%bv : bv 5) Q2. preg HS (3%bv : bv 5) Q3. preg HS (4%bv : bv 5) Q4.
preg HS (8%bv : bv 5) Q8. preg HS (10%bv : bv 5) Q10.
rewrite scb_denot_off0 in Q2, Q3, Q4, Q8, Q10.
cbn [sv_denot] in Q1. rewrite (img_env_codeptr E1 HEI1 24364) in Q1.
rewrite OLD1, (EL0 2%nat 2%bv eq_refl) in Q2 by lia.
rewrite OLD1, (EL0 3%nat 3%bv eq_refl), Hgp' in Q3 by lia. rewrite OLD1, (EL0 4%nat 4%bv eq_refl), Htp' in Q4 by lia.
rewrite OLD1, (EL0 8%nat 8%bv eq_refl), R8' in Q8 by lia.
rewrite OLD1, V22 in Q10 by lia.
pose proof (proj1 HJ2) as HARB.
assert (HinL2 : In (lst, 12 * n + 1) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm2)); right; exact HLin).
assert (Qsp2 : spZ (ms_regs msB) = sp0 + (scb_sp1 sp0 - sp0)).
{ unfold spZ at 1. rewrite Q2. fold (spZ regs'). rewrite Hsp'. lia. }
pose proof HJ2 as (_ & Hly2m & _ & _ & _ & _ & Hnev2 & _ & FJ2 & _).
pose proof Hly2m as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & _).
pose proof (st_ok_region_nth E1 _ _ 0%nat _ HS eq_refl) as HR0B. cbn [ms_mem restrict mkst] in HR0B.
assert (HRAwB : rdword (rdW W2 (ms_mem msB)) (sp0 - 8) = Some (raZ regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
  replace (sp0 - 8) with (sp0 + -8) by lia.
  refine (field_of_region E1 _ 8%nat sp0 _ (-104) 0 (-104) 0 (-8) 8%N (SOff 32 0) (raZ regs) HR0B W8 _ _ _ _);
  [ cbn [In]; tauto
  | rewrite scb_denot_off0, OLD1, E32' by lia; unfold raZ; rewrite Z_to_bv_bv_unsigned; reflexivity
  | unfold raZ; apply bv_unsigned_in_range | lia ]. }
assert (HS0wB : rdword (rdW W2 (ms_mem msB)) (sp0 - 16) = Some (s0Z regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
  replace (sp0 - 16) with (sp0 + -16) by lia.
  refine (field_of_region E1 _ 8%nat sp0 _ (-104) 0 (-104) 0 (-16) 8%N (SOff 33 0) (s0Z regs) HR0B W8 _ _ _ _);
  [ cbn [In]; tauto
  | rewrite scb_denot_off0, OLD1, E33' by lia; unfold s0Z; rewrite Z_to_bv_bv_unsigned; reflexivity
  | unfold s0Z; apply bv_unsigned_in_range | lia ]. }
destruct (CHAIN ly2 W2 (ms_mem msB) Etop2 (fun a Ha => FJ2 a ltac:(lia) ltac:(lia) (HNFP a ltac:(lia)))
  HRAwB HS0wB) as (chB & HCHB).
assert (HCPB : chain_pre ly2 (rdW W2 (ms_mem msB)) (ms_regs msB) chB).
{ apply (achain_chain_pre ly2 _ (scb_sp1 sp0) sp0 chB (ms_regs msB) HCHB);
  [ rewrite Qsp2; lia | unfold s0Z; rewrite Q8; unfold w64; apply unsigned_lit_small; lia
  | unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia ]. }
assert (HMOB : mo_ok MT S2 (mo_free MT)).
{ apply (mok_station MT S S2 (XM_SUP_CHAIN MT R id ids)
    ((XM_RECORD MT R + XM_XMALLOC MT (12 * n + 1) + XM_ARG_S MT (Some (dec id)) + XM_ARG_S MT (Some (dec n))) +
     XM_ARG_S MT (Some (dec_list ids)))
    (mo_free MT) MTL MOK (mle_station MT S SL S2 _ _ MTL HMLEL HMLE2) HXMfree).
  unfold XM_SUP_CHAIN. fold n. lia. }
assert (HCOV : In (lst, 12 * n + 1) (ablocks B ly S) ->
  forall i, 0 <= i < req_size (12 * n + 1) -> inFP (SCB_FP O) (lst + i)).
{ intros Hin0 i Hi.
  assert (HinF : In (lst, 12 * n + 1) Frec).
  { pose proof (Permutation_in _ HPerm0 Hin0) as Hx. apply in_app_or in Hx as [Hx | Hx]; [|exact Hx].
    exfalso. pose proof (proj1 (Forall_forall _ _) HApL _ Hx) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
  destruct (inFP_ablocks_fp O lst (12 * n + 1) i (HFrecO _ HinF) Hi) as (r & Hr & Hrr).
  exists r. split; [right; right; exact Hr | exact Hrr]. }
eapply SRr_bind.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT (AFREE4 fx0) W2 (ms_regs msB) (ms_mem msB) SUP_CHAIN_STK sp0
    (SCB_FP O) ly S W mem md [(1, fpos)] ly2 S2 _ _ lst (12 * n + 1) (scb_sp1 sp0 - sp0)
    (Z_to_bv 64 (BASE + 24364)) chB HJ2 HinL2 Q10 Qsp2 Hsp1b);
  [ lia | rewrite Has, HSTK; lia | exact Q3 | exact Q4 | exact Q1 | apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite HEVsplit in Hev; lia | exact HCPB | exact HCOV | exact HMOB ]. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (l1 & l2 & El1 & El2) & Hfrs3 & HK3
  & HMLE3 & HJ3c).
pose proof HK3 as (HK31 & _ & _ & _ & _ & _).
pose proof HJ3 as (HAR3 & Hly3m & _ & _ & _ & _ & Hnev3 & _ & FJ3 & _ & _ & _ & _ & Hpres3 & _).
jafter_call_keep_pi HS 65%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0;1;2]%nat HS3.
match type of HS3 with ?tq -> _ => assert (HRK : tq); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (scb4_region_kept_hi2 E1 (w_H W2) (w_H W3) (ms_mem msB) mem3 8 sp0); [exact W8 | |].
    + intros a Ha. apply HK31; [lia | lia].
    + intros a Ha. apply Hpres3. rewrite HSTK. lia.
  - apply (scb4_region_kept_hi2 E1 (w_H W2) (w_H W3) (ms_mem msB) mem3 9 (scb_sp1 sp0)); [exact W9 | |].
    + intros a Ha. apply HK31; [lia | lia].
    + intros a Ha. lia.
  - eapply (region_kept_frame_aj SEGS B E1 ly2 S2 W2 (ms_mem msB) W3 mem3 _ _ _ 46%nat 120 128 120 120 _ F 1 fpos
      HK3 W46 Hfin2); [rewrite EFA2; lia | rewrite EFA2; change (fs_frame_bytes 1) with 128; lia | lia |].
    intros a Ha Hb.
    pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 (ms_mem msB) _ lst (12 * n + 1) 1 fpos HARB HinL2 Hfin2) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA2 in Hd. change (fs_frame_bytes 1) with 128 in Hd.
    lia. }
rewrite <- restrict_mkst_fx in HS3. clear HS. rename HS3 into HS.
remember (havoc E1 65 (map (getr regs3) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
assert (OLD2 : forall m, (m < 65)%nat -> ew E2 m = ew E1 m) by (intros m Hm; rewrite HE2; apply ew_havoc_old; exact Hm).
clear HE2.
assert (X8 : bv_unsigned (ew E2 8) = sp0) by (rewrite OLD2 by lia; exact W8).
assert (X9 : bv_unsigned (ew E2 9) = scb_sp1 sp0) by (rewrite OLD2 by lia; exact W9).
assert (X46 : bv_unsigned (ew E2 46) = F) by (rewrite OLD2 by lia; exact W46).
(* run 3: a0 := "chain" (0x21f60), a1 := 5, the call of rec_shape_of *)
paj_run_shc RUNP RUNC HS HJ3.
{ unfold scb4_saveR, scb4_wordsR, scb4_flgR. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 8%nat) (d := 0);
  [reflexivity | rewrite X8; lia | cbn; rewrite HSTK; lia | cbn; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  apply (awr_ok_nil SEGS B). }
rename ms into msC, mat into matC, HF into HFC, HFr into HFrC, HG into HGC.
pmkst HS.
preg HS (1%bv : bv 5) T1. preg HS (2%bv : bv 5) T2. preg HS (3%bv : bv 5) T3. preg HS (4%bv : bv 5) T4.
preg HS (10%bv : bv 5) T10. preg HS (11%bv : bv 5) T11.
cbn [sv_denot] in T1. rewrite (img_env_codeptr E2 HEI2 24380) in T1.
rewrite scb_denot_off0, (img_env_atomP E2 321 HEI2 ltac:(unfold A_TEXT, A_LIM; lia)) in T10.
change (VAL 321) with (VAL (A_OBJ 80)) in T10.
destruct (scb_vals VOBJS) as (_ & _ & _ & _ & _ & _ & _ & VO80). rewrite VO80 in T10.
cbn [sv_denot] in T11.
rewrite scb_denot_off0, OLD2, OLD1, (EL0 2%nat 2%bv eq_refl) in T2 by lia.
rewrite scb_denot_off0, OLD2, OLD1, (EL0 3%nat 3%bv eq_refl), Hgp' in T3 by lia.
rewrite scb_denot_off0, OLD2, OLD1, (EL0 4%nat 4%bv eq_refl), Htp' in T4 by lia.
assert (Qsp3 : spZ (ms_regs msC) = sp0 + (scb_sp1 sp0 - sp0)).
{ unfold spZ at 1. rewrite T2. fold (spZ regs'). rewrite Hsp'. lia. }
pose proof (proj1 HJ3) as HARC.
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hnev3c & _).
assert (HRODC : arodata_okP SEGS RLO RHI B (rdW W3 (ms_mem msC)))
  by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := ROB) B _ _ (SCB_FP O) ly S W mem md _ ly3 S3 W3
       (ms_mem msC) _ _ HJ3 HFPRO HROD).
pose proof (cmd_ro_ok_of_aro ly3 S3 W3 (ms_mem msC) _ HARC HRODC) as HROC.
assert (SIGRS : SIG CS_rec_shape_of = BASE + AF_rec_shape_of)
  by (destruct (scb_sigs cmd_sig_prog_PB) as (_ & _ & _ & Hx & _); exact Hx).
rewrite SIGRS.
eapply SRr_bind.
{ eapply (cl_callS_na B LAWS W3 (ms_regs msC) (ms_mem msC) _ SUP_CHAIN_STK sp0 (SCB_FP O) ly S W mem md
    [(1, fpos)] ly3 S3 _ _ REC_SHAPE_OF_STK [] EV_REC_SHAPE_OF (scb_sp1 sp0 - sp0) (getr (ms_regs msC) 1) _ HJ3 Qsp3);
  [ exact Hsp1b | lia | unfold REC_SHAPE_OF_STK, ESTACK; lia | unfold REC_SHAPE_OF_STK, ESTACK; rewrite HSTK; lia
  | exact T3 | exact T4 | reflexivity | rewrite T1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite T1, unsigned_lit_small by lia; lia
  | intros HPRE3;
    exact (TREC_SHAPE_OF fx0 ly3 S3 W3 (ms_regs msC) (ms_mem msC) _ 0x21f60 scb_verb HPRE3 HRODC T10 ltac:(lia)
      T11 ltac:(cbn; lia) HROC VOBJS (scb_verb_pre B HB ly3 S3 W3 (ms_mem msC) _ HARC HROC CMD_RO_IN)
      ltac:(unfold EV_REC_SHAPE_OF; rewrite HEVsplit in Hev; lia))
  | intros a Ha; exfalso; exact (inFP_nil a Ha) ]. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJ4c & HP4 & HK4).
rewrite T1.
destruct HK4 as ((qsh & Hqsh10 & Hqsh & HSHAPE) & Hperm4 & -> & ->).
pose proof HJ3c as (_ & Hly3c & _ & _ & _ & Hfrs3c & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HARB Hly3c) as (Eab3 & Efa3 & _).
assert (EFA3 : frame_addr ly3 1 fpos = F) by (rewrite Efa3; exact EFA2).
assert (Hfin3 : In (1, fpos) (frames S3)) by (rewrite Hfrs3; exact Hfin2).
jafter_call_keep_pi HS 81%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0;1;2]%nat HS4.
match type of HS4 with ?tq -> _ => assert (HRK : tq); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict mkst]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_stack_sub SEGS B E2 _ _ _ ly3 S3 W3 (ms_mem msC) _ ly3 S3 W4 mem4 md4 _ 8%nat
      (-104) 0 (-104) 0 _ sp0 SUP_CHAIN_STK sp0 (SCB_FP O) ly S W mem md [(1, fpos)] _ HJ4c HJ4 X8);
    [ lia | rewrite HSTK; lia | lia | lia | lia | intros a Ha Hf; exact (inFP_nil a Hf) ].
  - eapply (region_kept_stack_sub SEGS B E2 _ _ _ ly3 S3 W3 (ms_mem msC) _ ly3 S3 W4 mem4 md4 _ 9%nat
      8 40 8 8 _ (scb_sp1 sp0) SUP_CHAIN_STK sp0 (SCB_FP O) ly S W mem md [(1, fpos)] _ HJ4c HJ4 X9);
    [ lia | rewrite HSTK; lia | lia | lia | lia | intros a Ha Hf; exact (inFP_nil a Hf) ].
  - eapply (region_kept_frame_sub (segs := SEGS) B E2 _ _ _ ly3 S3 W3 (ms_mem msC) _ ly3 S3 W4 mem4 md4 _
      46%nat F 120 128 120 120 _ 1 fpos HJ4c X46 Hfin3);
    [ rewrite EFA3; lia | rewrite EFA3; change (fs_frame_bytes 1) with 128; lia
    | intros a Ha Hf; exact (inFP_nil a Hf) | intros a Ha; lia ]. }
rewrite <- restrict_mkst_fx in HS4. clear HS. rename HS4 into HS.
remember (havoc E2 81 (map (getr regs4) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall m, (m < 81)%nat -> ew E3 m = ew E2 m) by (intros m Hm; rewrite HE3; apply ew_havoc_old; exact Hm).
assert (E85 : ew E3 85 = getr regs4 10).
{ rewrite HE3. change 85%nat with (81 + 4)%nat. rewrite (ew_havoc_new E2 81 _ 4 (Z_to_bv 64 0)) by (cbv; lia).
  unfold CLOB. cbn [map nth]. reflexivity. }
clear HE3.
assert (Y8 : bv_unsigned (ew E3 8) = sp0) by (rewrite OLD3 by lia; exact X8).
assert (Y9 : bv_unsigned (ew E3 9) = scb_sp1 sp0) by (rewrite OLD3 by lia; exact X9).
assert (Y46 : bv_unsigned (ew E3 46) = F) by (rewrite OLD3 by lia; exact X46).
(* run 4: a1 := the shape, a2 := 1, a0 := the slot, the call of answer *)
paj_run_shc RUNP RUNC HS HJ4.
{ unfold scb4_saveR, scb4_wordsR, scb4_flgR. cbn [ss_mem].
  eapply (awr_ok_cons_stack_off SEGS B) with (n := 8%nat) (d := 0);
  [reflexivity | rewrite Y8; lia | cbn; rewrite HSTK; lia | cbn; lia |].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  apply (awr_ok_nil SEGS B). }
rename ms into msD, mat into matD, HF into HFD, HFr into HFrD, HG into HGD.
pmkst HS.
preg HS (1%bv : bv 5) U1. preg HS (10%bv : bv 5) U10. preg HS (11%bv : bv 5) U11. preg HS (12%bv : bv 5) U12.
rewrite scb_denot_off0, OLD3, OLD2, OLD1, E45' in U10 by lia.
rewrite scb_denot_off0, E85, Hqsh10 in U11.
cbn [sv_denot] in U1, U12. rewrite (img_env_codeptr E3 HEI3 24396) in U1.
(* the recorder's blocks at the answer's entry: the two arg_s copies, the list text's copy and the earlier ones *)
change (sarg (Some (dec_list ids))) with (dec_list ids) in Hperm2, Hfresh2, HREP2.
set (nd := Z.of_nat (length (dec_list ids)) + 1) in *.
set (OD := (pq, nd) :: OL) in *.
pose proof (scb_dec_list_len ids HidsF ltac:(lia)) as HLEN.
cbn [app] in HREP2.
assert (HODin2 : forall pn, In pn OD -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; exact (rec_repA_in ly2 S2 _ _ OD HREP2 pn Hpn)).
assert (HODap : forall pn, In pn OD -> iv_apart lst (12 * n + 1) (fst pn) (snd pn)).
{ intros pn Hpn. destruct Hpn as [<- | Hpn]; [|exact (HOLap pn Hpn)].
  pose proof (proj1 (Forall_forall _ _) Hfresh2 _ HLin) as Hx. unfold iv_apart in *. cbn [fst snd] in *. lia. }
assert (HODin3 : forall pn, In pn OD -> In pn (ablocks B ly3 S3)).
{ intros pn Hpn. rewrite El2. pose proof (HODin2 pn Hpn) as Hin2.
  assert (Hne : pn <> (lst, 12 * n + 1)).
  { intros ->. pose proof (HODap _ Hpn) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
  rewrite El1 in Hin2. apply in_app_or in Hin2. apply in_or_app.
  destruct Hin2 as [H | [H | H]]; [left; exact H | exfalso; exact (Hne (eq_sym H)) | right; exact H]. }
assert (HODpos : forall p nn, In (p, nn) OD -> 0 <= nn /\ p + req_size nn <= alloc_ceiling /\ 4096 <= p).
{ intros p nn Hin.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p nn HARB (HODin2 (p, nn) Hin)) as (_ & H1 & H2 & _ & _ & _ & H3).
  split; [lia | split; [exact H2 | exact H1]]. }
set (KB := fun a : Z => A_G_REC <= a < A_G_REC + 960 \/ A_REC_SPILL <= a < A_REC_SPILL + 56 \/
  (exists p nn, In (p, nn) OD /\ p <= a < p + nn)) in *.
assert (KBLOC : forall a, KB a -> 0 <= a < alloc_ceiling /\ ~ (F <= a < F + 128) /\
  ~ (lst <= a < lst + req_size (12 * n + 1))).
{ intros a Ha. destruct Ha as [Ha | [Ha | (p & nn & Hin & Hpa)]].
  - split; [unfold A_G_REC in *; lia|]. split; [unfold A_G_REC in *; lia|].
    intros Hc. exact (blk_img SEGS B LAWS lyL SL WL mem' md' lst (12 * n + 1) a HARL HLin Hc
      (HRECIMG a (or_introl Ha))).
  - split; [unfold A_REC_SPILL in *; lia|]. split; [unfold A_REC_SPILL in *; lia|].
    intros Hc. exact (blk_img SEGS B LAWS lyL SL WL mem' md' lst (12 * n + 1) a HARL HLin Hc
      (HRECIMG a (or_intror Ha))).
  - destruct (HODpos p nn Hin) as (Hnn & Hceil2 & Hp4096).
    pose proof (req_size_pos nn ltac:(lia)) as [Rq1 Rq2].
    pose proof (HODap (p, nn) Hin) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap.
    pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 (ms_mem msB) _ p nn 1 fpos HARB (HODin2 (p, nn) Hin) Hfin2) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA2 in Hd. change (fs_frame_bytes 1) with 128 in Hd.
    assert (Hne : (lst, 12 * n + 1) <> (p, nn)) by (intros E; injection E as <- <-; lia).
    pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 (ms_mem msB) _ lst (12 * n + 1) p nn HARB
      (Permutation_in _ (Permutation_sym Hperm2) (or_intror HLin)) (HODin2 (p, nn) Hin) Hne) as Hsep.
    unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
    split; [lia|]. split; lia. }
(* the recorder's bytes do not move from the end of the arg_s call to the answer's entry *)
assert (KD : forall a, KB a -> rdW W4 (ms_mem msD) a = rdW W2 mem2 a).
{ intros a Ha. destruct (KBLOC a Ha) as (Hb0 & HnF & Hnl).
  assert (K4 : rdW W4 (ms_mem msD) a = rdW W4 mem4 a).
  { apply (recb_run_keeps_m E3 _ (w_H W4) mem4 (ms_mem msD) a HFrD); [lia|].
    nwin_tac ltac:(fun Hr => rewrite ?Y8, ?Y9, ?Y46 in Hr; lia). }
  assert (K3 : rdW W3 (ms_mem msC) a = rdW W3 mem3 a).
  { apply (recb_run_keeps_m E2 _ (w_H W3) mem3 (ms_mem msC) a HFrC); [lia|].
    nwin_tac ltac:(fun Hr => rewrite ?X8, ?X9, ?X46 in Hr; lia). }
  assert (K2 : rdW W2 (ms_mem msB) a = rdW W2 mem2 a).
  { apply (recb_run_keeps_m E1 _ (w_H W2) mem2 (ms_mem msB) a HFrB); [lia|].
    nwin_tac ltac:(fun Hr => rewrite ?W8, ?W9, ?W46 in Hr; lia). }
  pose proof HJ4c as (_ & _ & _ & _ & _ & _ & _ & _ & GJ1 & GJ2 & GJ3 & _).
  pose proof HJ3c as (_ & _ & _ & _ & _ & _ & _ & _ & FF1 & FF2 & FF3 & _).
  assert (HnoFP : forall b, ~ inFP ([] : list (Z * Z)) b) by (intros b (r & [] & _)).
  assert (HnoFPf : forall b, A_G_REC <= b < A_G_REC + 960 \/ A_REC_SPILL <= b < A_REC_SPILL + 56 \/
      (exists p nn, In (p, nn) OD /\ p <= b < p + nn) -> ~ inFP (ablocks_fp [(lst, 12 * n + 1)]) b).
  { intros b Hb Hf. destruct (inFP_ablocks_fp_inv [(lst, 12 * n + 1)] b Hf) as (b0 & m0 & Hb0' & Hr).
    destruct Hb0' as [E | []]. injection E as <- <-.
    destruct (KBLOC b Hb) as (_ & _ & Hnl'). apply Hnl'. lia. }
  assert (K34 : rdW W4 mem4 a = rdW W3 (ms_mem msC) a).
  { destruct Ha as [Hx | [Hx | (p & nn & Hin & Hpa)]].
    - destruct (scb4_rec_unowned a (or_introl Hx)) as (Hi & Ho & He).
      apply GJ3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [intros (r & [] & _) | exact (HnoFP a)]].
    - destruct (scb4_rec_unowned a (or_intror Hx)) as (Hi & Ho & He).
      apply GJ3; [exact Hi | exact Ho | exact He | apply fp_spares_closed; [intros (r & [] & _) | exact (HnoFP a)]].
    - destruct (HODpos p nn Hin) as (Hnn & _ & _). pose proof (req_size_pos nn ltac:(lia)) as [Rn1 Rn2].
      replace a with (p + (a - p)) by lia.
      apply (GJ2 p nn (a - p)); [exact (HODin3 (p, nn) Hin) | exact (HODin3 (p, nn) Hin) | lia |].
      exact (HnoFP (p + (a - p))). }
  assert (HnoSink : ~ YI16.sink_open_fp (ablocks_fp [(lst, 12 * n + 1)])).
  { intros Hs. destruct (inFP_ablocks_fp_inv [(lst, 12 * n + 1)] 0 Hs) as (b0 & m0 & Hb0' & Hr).
    destruct Hb0' as [E | []]. injection E as <- <-. lia. }
  assert (K23 : rdW W3 mem3 a = rdW W2 (ms_mem msB) a).
  { destruct Ha as [Hx | [Hx | (p & nn & Hin & Hpa)]].
    - destruct (scb4_rec_unowned a (or_introl Hx)) as (Hi & Ho & He).
      apply FF3; [exact Hi | exact Ho | exact He |
        apply fp_spares_closed; [exact HnoSink | exact (HnoFPf a (or_introl Hx))]].
    - destruct (scb4_rec_unowned a (or_intror Hx)) as (Hi & Ho & He).
      apply FF3; [exact Hi | exact Ho | exact He |
        apply fp_spares_closed; [exact HnoSink | exact (HnoFPf a (or_intror (or_introl Hx)))]].
    - destruct (HODpos p nn Hin) as (Hnn & _ & _). pose proof (req_size_pos nn ltac:(lia)) as [Rn1 Rn2].
      replace a with (p + (a - p)) by lia.
      apply (FF2 p nn (a - p));
      [ exact (HODin2 (p, nn) Hin) | exact (HODin3 (p, nn) Hin) | lia
      | apply HnoFPf; right; right; exists p, nn; split; [exact Hin | lia] ]. }
  rewrite K4, K34, K3, K23, K2. reflexivity. }
assert (HREPD : rec_repA B ly3 S3 (rdW W4 (ms_mem msD))
  (rec_record R REC_CHAIN [dec id; dec n; dec_list ids]) OD).
{ apply (rec_repA_kept ly2 S2 (rdW W2 mem2) ly3 S3 (rdW W4 (ms_mem msD)) _ OD HREP2 HODin3).
  - intros a Ha. apply KD. left. exact Ha.
  - intros a Ha. apply KD. right. left. exact Ha.
  - intros p nn i Hin Hi. apply KD. right. right. exists p, nn. split; [exact Hin | lia]. }
(* the shape the call passes: rec_shape_of's post, at the state the run leaves *)
pose proof (proj1 HJ4) as HAR4.
assert (HSHD : forall O0, astr_argA B ly3 S3 (rdW W4 (ms_mem msD)) (in_roP SEGS RLO RHI) O0 qsh
  (Some (shape_of scb_verb))).
{ intros O0. apply (scb4_argA_keep ly3 S3 (rdW W4 mem4) _ _ O0 qsh _ (HSHAPE O0)).
  intros i Hi. pose proof (scb4_argA_lo ly3 S3 W4 (ms_mem msD) _ (rdW W4 mem4) O0 qsh
    (shape_of scb_verb) HAR4 (HSHAPE O0) i Hi) as Hb.
  apply (recb_run_keeps_m E3 _ (w_H W4) mem4 (ms_mem msD) (qsh + i) HFrD); [lia|].
  nwin_tac ltac:(fun Hr => rewrite ?Y8, ?Y9, ?Y46 in Hr; lia). }
(* the recorder's answer field at the call *)
destruct (scb4_repA_answer ly3 S3 (rdW W4 (ms_mem msD)) _ OD HREPD) as (old & HOLD & HOLDb).
assert (HOLDr : 0 <= old < 2 ^ 64).
{ destruct HOLDb as [-> | ([p0 nn0] & Hin0 & Hf0)]; [lia|]. cbn [fst] in Hf0. subst p0.
  destruct (HODpos old nn0 Hin0) as (Hnn0 & Hceil2 & Hp4096).
  pose proof (req_size_pos nn0 ltac:(lia)) as [Rq1 Rq2]. lia. }
(* the frames this call holds: its own, on the statement's at most 7 *)
assert (HFRC : Z.of_nat (length (frames S3)) <= 8).
{ rewrite Hfrs3, Hfrs2, HfrsL. cbn [length app]. lia. }
(* the budgets of the call *)
assert (HEVRS : EV_REC_SHAPE_OF = 0) by (vm_compute; reflexivity).
assert (HevD : st_nev S3 + EV_ANSWER <= EV_MAX).
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & HnevD & _). rewrite HEVsplit in Hev. unfold scb_kL in *. lia. }
assert (HbbD : blocks_bytes S3 <= blocks_bytes S2 - (12 * n + 1)).
{ assert (Eb3 : blocks_bytes S3 = bsum (ablocks B ly3 S3)) by apply blocks_bytes_bsum.
  assert (Eb2 : blocks_bytes S2 = bsum (ablocks B ly2 S2)) by apply blocks_bytes_bsum.
  rewrite Eb3, Eb2, El1, El2, !bsum_app, bsum_cons. cbn [snd]. lia. }
assert (HliveD : blocks_bytes S3 + LIVE_ANSWER (snd (sup_chain_m R id ids)) <= LIVE_MAX).
{ unfold LIVE_SUP_CHAIN in Hlive. fold n in Hlive.
  pose proof (req_size_pos (12 * n + 1) ltac:(lia)) as [RQ3 RQ4]. lia. }
assert (HmokD : mo_ok MT S3 (XM_ANSWER MT (snd (sup_chain_m R id ids)))).
{ apply (mok_station MT S S3 (XM_SUP_CHAIN MT R id ids)
    ((XM_RECORD MT R + XM_XMALLOC MT (12 * n + 1) + XM_ARG_S MT (Some (dec id)) + XM_ARG_S MT (Some (dec n))) +
     XM_ARG_S MT (Some (dec_list ids)) + mo_free MT)
    (XM_ANSWER MT (snd (sup_chain_m R id ids))) MTL MOK
    (mle_station MT S S2 S3 _ _ MTL (mle_station MT S SL S2 _ _ MTL HMLEL HMLE2) HMLE3) HXMans).
  unfold XM_SUP_CHAIN. fold n. lia. }
assert (HENTRY : (exists k, nth_error (r_calls (rec_record R REC_CHAIN [dec id; dec n; dec_list ids])) k =
    Some (REC_CHAIN, [dec id; dec n; dec_list ids]) /\
    rec_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat k) \/
  (rec_slot R = A_REC_SPILL /\ (REC_CHAIN, [dec id; dec n; dec_list ids]) =
    r_spill (rec_record R REC_CHAIN [dec id; dec n; dec_list ids])))
  by exact (scb4_entry R REC_CHAIN [dec id; dec n; dec_list ids]).
(* the model's step *)
pose proof (scb_model R id ids) as HM. fold n in HM.
(* the state at the call of answer(slot, shape, 1) *)
preg HS (2%bv : bv 5) U2. preg HS (3%bv : bv 5) U3. preg HS (4%bv : bv 5) U4.
preg HS (8%bv : bv 5) U8. preg HS (9%bv : bv 5) U9.
rewrite scb_denot_off0, OLD3, OLD2, OLD1, (EL0 2%nat 2%bv eq_refl) in U2 by lia.
rewrite scb_denot_off0, OLD3, OLD2, OLD1, (EL0 3%nat 3%bv eq_refl), Hgp' in U3 by lia.
rewrite scb_denot_off0, OLD3, OLD2, OLD1, (EL0 4%nat 4%bv eq_refl), Htp' in U4 by lia.
rewrite scb_denot_off0, OLD3, OLD2, OLD1, (EL0 8%nat 8%bv eq_refl), R8' in U8 by lia.
rewrite scb_denot_off0, OLD3, OLD2, OLD1, (EL0 9%nat 9%bv eq_refl), R9' in U9 by lia.
assert (QspD : spZ (ms_regs msD) = sp0 + (scb_sp1 sp0 - sp0)).
{ unfold spZ at 1. rewrite U2. fold (spZ regs'). rewrite Hsp'. lia. }
pose proof (st_ok_region_nth E3 _ _ 0%nat _ HS eq_refl) as HR0D. cbn [ms_mem restrict mkst] in HR0D.
assert (HXD : forall j, (j < 13)%nat -> ew E3 (32 + j) = getr regs (Z_to_bv 5 (nth j scb_saved 0))).
{ intros j Hj. rewrite OLD3, OLD2, OLD1 by lia. rewrite (EX0 j ltac:(lia)).
  do 13 (destruct j as [|j]; [cbn; reflexivity|]). lia. }
assert (HFRD : scb_frame_at (mrestrict (w_H W4) (ms_mem msD)) sp0 regs)
  by exact (scb4_frame_of_region E3 (w_H W4) (ms_mem msD) sp0 regs Y8 HXD HR0D).
assert (HRAwD : rdword (rdW W4 (ms_mem msD)) (sp0 - 8) = Some (raZ regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold raZ; apply bv_unsigned_in_range].
  replace (sp0 - 8) with (sp0 - 8 - 8 * Z.of_nat 0) by lia. exact (HFRD 0%nat 1 eq_refl). }
assert (HS0wD : rdword (rdW W4 (ms_mem msD)) (sp0 - 16) = Some (s0Z regs)).
{ apply (rdword_of_val_mem SEGS); [|unfold s0Z; apply bv_unsigned_in_range].
  replace (sp0 - 16) with (sp0 - 8 - 8 * Z.of_nat 1) by lia. exact (HFRD 1%nat 8 eq_refl). }
pose proof HJ4 as (_ & Hly4m & _ & _ & _ & _ & Hnev4 & _ & FJ4 & _).
pose proof Hly4m as (_ & _ & _ & _ & _ & _ & _ & _ & Etop4 & _).
destruct (CHAIN ly3 W4 (ms_mem msD) Etop4 (fun a Ha => FJ4 a ltac:(lia) ltac:(lia) (HNFP a ltac:(lia)))
  HRAwD HS0wD) as (chD & HCHD).
assert (HRODD : arodata_okP SEGS RLO RHI B (rdW W4 (ms_mem msD)))
  by exact (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := ROB) B _ _ (SCB_FP O) ly S W mem md _ ly3 S3 W4
       (ms_mem msD) _ _ HJ4 HFPRO HROD).
pose proof (cmd_ro_ok_of_aro ly3 S3 W4 (ms_mem msD) _ HAR4 HRODD) as HROD2.
assert (Hchg : true = negb (bv_unsigned (getr (ms_regs msD) 12) =? 0))
  by (rewrite U12; vm_compute; reflexivity).
assert (HASTK : 0 <= ANSWER_STK <= 16592) by (vm_compute; split; discriminate).
rewrite HM in HliveD, HmokD.
assert (SIGAN : SIG CS_answer = BASE + AF_answer)
  by (destruct (scb_sigs cmd_sig_prog_PB) as (_ & _ & _ & _ & Hx); exact Hx).
rewrite SIGAN.
assert (Hs0D : s0Z (ms_regs msD) = sp0)
  by (unfold s0Z; rewrite U8; unfold w64; apply unsigned_lit_small; lia).
(* the call's footprint: g_rec's answer and state fields, and the old answer's block *)
set (FPA := (A_G_REC + OFF_ANSWER, A_G_REC + OFF_ANSWER + 8) ::
            (A_G_REC + OFF_STATE, A_G_REC + OFF_STATE + 8) ::
            ablocks_fp (filter (fun pn => fst pn =? old) OD)) in *.
assert (HFPAlo : forall a, inFP FPA a -> a < alloc_ceiling /\ ~ (F <= a < F + 128) /\
  (A_G_REC <= a < A_G_REC + 960 \/ (exists p0 nn0, In (p0, nn0) OD /\ p0 <= a < p0 + req_size nn0))).
{ intros a (r & Hr & Hrz). unfold FPA in Hr. destruct Hr as [<- | [<- | Hr]].
  - cbn [fst snd] in Hrz. unfold A_G_REC, OFF_ANSWER in *. split; [lia|]. split; [lia|]. left. lia.
  - cbn [fst snd] in Hrz. unfold A_G_REC, OFF_STATE in *. split; [lia|]. split; [lia|]. left. lia.
  - destruct (inFP_ablocks_fp_inv _ a (ex_intro _ r (conj Hr Hrz))) as (p0 & nn0 & Hin0 & Hr0).
    apply scb4_in_filter in Hin0.
    destruct (HODpos p0 nn0 Hin0) as (Hnn0 & Hceil0 & Hp0).
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W4 (ms_mem msD) _ p0 nn0 1 fpos HAR4 (HODin3 _ Hin0) Hfin3) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA3 in Hd. change (fs_frame_bytes 1) with 128 in Hd.
    split; [lia|]. split; [lia|]. right. exists p0, nn0. split; [exact Hin0 | lia]. }
assert (HFPAw : forall a, inFP FPA a ->
  awr_byte SEGS B SUP_CHAIN_STK sp0 (SCB_FP O) (ablocks B ly S) (ablocks B ly3 S3) (frames S) ly3 [(1, fpos)] a).
{ intros a Hf. destruct (HFPAlo a Hf) as (Hlo & HnF & [Hg | (p0 & nn0 & Hin0 & Hr0)]).
  - right; right; right; right; left. split.
    + exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; unfold REC_SIZE; lia].
    + split; [rewrite (YF0m.ts_prog B HB); apply Exists_cons_hd; unfold in_zr; cbn [fst snd];
               unfold A_G_REC in *; lia | exact (HRECIMG a (or_introl Hg))].
  - destruct (scb4_in_dec (p0, nn0) (ablocks B ly S)) as [Hb0 | Hb0].
    + right; left. split.
      * pose proof (scb4_OA_O (ablocks B ly S) bl1 Frec O O1 (ablocks B lyL SL) lst (12 * n + 1) p1 (scb_m id)
          p2 (scb_m n) pq nd HPerm0 HFrecO HO1 HPermL HAp1 HAp2
          ltac:(unfold scb_m; lia) ltac:(unfold scb_m; lia) ltac:(unfold nd; lia) Hfresh2
          (p0, nn0) Hin0 Hb0) as HinO.
        destruct (inFP_ablocks_fp O p0 nn0 (a - p0) HinO ltac:(lia)) as (r2 & Hr2 & Hr3).
        exists r2. split; [right; right; exact Hr2|].
        replace (p0 + (a - p0)) with a in Hr3 by lia. exact Hr3.
      * exists p0, nn0. split; [exact (HODin3 _ Hin0) | exact Hr0].
    + right; right; left. exists p0, nn0. split; [exact (HODin3 _ Hin0) | split; [exact Hb0 | exact Hr0]]. }
eapply SRr_bind.
{ eapply (callS_wideF B LAWS W4 (ms_regs msD) (ms_mem msD) _ SUP_CHAIN_STK sp0 (SCB_FP O) ly S W mem md
    [(1, fpos)] ly3 S3 _ _ ANSWER_STK _ EV_ANSWER (scb_sp1 sp0 - sp0) (getr (ms_regs msD) 1) chD _ HJ4 QspD);
  [ exact Hsp1b | lia | lia | rewrite HSTK; lia
  | exact U3 | exact U4 | reflexivity | rewrite U1; apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite U1, unsigned_lit_small by lia; lia
  | rewrite Hs0D; replace (sp0 + (scb_sp1 sp0 - sp0)) with (scb_sp1 sp0) by lia; exact HCHD
  | intros HPRED;
    exact (TANSWER fx0 ly3 S3 W4 (ms_regs msD) (ms_mem msD) _ chD (rec_slot R) qsh old
      (REC_CHAIN, [dec id; dec n; dec_list ids]) (shape_of scb_verb) true
      (rec_record R REC_CHAIN [dec id; dec n; dec_list ids]) OD
      HPRED HRM0 HFRC HRODD HROD2 U10 Hslot U11 Hqsh Hchg HREPD HOLD HOLDr
      (fun _ => conj (HSHD OD) scb4_fits) (fun _ _ => HENTRY) HevD HliveD HmokD)
  | exact HFPAw
  | intros ly5 S5 W5 regs5 mem5 md5 _ a Ha Hw _; exfalso;
    destruct (HFPAlo a Ha) as (Hlo & _ & _); rewrite HSTK in Hw; lia ]. }
cbv beta. intros W5 c5 Hwle5 (fx5 & ly5 & S5 & regs5 & mem5 & md5 & -> & HFX5a & HFX5b & HJ5 & HJ5c & HP5 & HK5).
cbv zeta in HK5.
destruct HK5 as (q1 & q2 & O' & Hq10 & Hq4096 & Hne12 & Hfr12 & Hbl5 & HREP5 & HO5 & HSTR5 & HBB5 & HMLE5).
rewrite <- HM in Hfr12, Hbl5, HREP5, HO5, HSTR5, HBB5, HMLE5.
rewrite U1.
pose proof (proj1 HJ5) as HAR5.
pose proof HJ5c as (_ & Hly5c & _ & _ & _ & _ & _ & _ & GG1 & _ & _ & GG4 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly5 HAR4 Hly5c) as (_ & Efa5 & _).
assert (EFA5 : frame_addr ly5 1 fpos = F) by (rewrite Efa5; exact EFA3).
assert (ELF : ly_F ly5 = ly_F lyL) by (pose proof EFA5 as E; unfold F, frame_addr in E; lia).
assert (EFL5 : flag_addr ly5 1 fpos = FL) by (unfold FL, flag_addr; rewrite ELF; reflexivity).
(* the registers at 0x8c47c: answer keeps the callee-saved ones *)
assert (PP2 : getr regs5 2 = getr (ms_regs msD) 2) by exact (HP5 2 ltac:(unfold acallee_saved; lia)).
assert (PP3 : getr regs5 3 = getr (ms_regs msD) 3) by exact (HP5 3 ltac:(unfold acallee_saved; lia)).
assert (PP4 : getr regs5 4 = getr (ms_regs msD) 4) by exact (HP5 4 ltac:(unfold acallee_saved; lia)).
assert (PP8 : getr regs5 8 = getr (ms_regs msD) 8) by exact (HP5 8 ltac:(unfold acallee_saved; lia)).
assert (PP9 : getr regs5 9 = getr (ms_regs msD) 9) by exact (HP5 9 ltac:(unfold acallee_saved; lia)).
assert (R2_5 : spZ regs5 = scb_sp1 sp0).
{ unfold spZ. rewrite PP2. fold (spZ (ms_regs msD)). rewrite QspD. lia. }
assert (R3_5 : getr regs5 3 = getr regs 3) by (rewrite PP3, U3; symmetry; exact Hgp).
assert (R4_5 : getr regs5 4 = getr regs 4) by (rewrite PP4, U4; symmetry; exact Htp).
assert (R8_5 : getr regs5 8 = w64 sp0) by (rewrite PP8; exact U8).
assert (R9_5 : getr regs5 9 = w64 (scb_sp1 sp0)) by (rewrite PP9; exact U9).
(* the memory at 0x8c47c: the saved registers, the stack words and the flag word, kept by answer *)
assert (KS5 : forall a, alloc_ceiling <= a < 2 ^ 64 -> scb_sp1 sp0 <= a -> rdW W5 mem5 a = rdW W4 (ms_mem msD) a).
{ intros a Ha Hge. apply GG1; [exact Ha | lia |].
  intros Hf. destruct (HFPAlo a Hf) as (Hlo & _ & _). lia. }
assert (HFR5 : scb_frame_at (mrestrict (w_H W5) mem5) sp0 regs).
{ intros j r Hj. apply (recb_val_mem_frame_m (w_H W4) (w_H W5) (ms_mem msD) mem5 _ 8%nat); [exact (HFRD j r Hj)|].
  pose proof (proj1 (nth_error_Some scb_saved j) ltac:(rewrite Hj; discriminate)) as Hj13.
  unfold scb_saved in Hj13. cbn [length] in Hj13.
  intros i Hi. apply KS5; lia. }
pose proof (st_ok_region_nth E3 _ _ 1%nat _ HS eq_refl) as HR1D. cbn [ms_mem restrict mkst] in HR1D.
pose proof (st_ok_region_nth E3 _ _ 2%nat _ HS eq_refl) as HR2D. cbn [ms_mem restrict mkst] in HR2D.
assert (E47' : ew E0 47 = Z_to_bv 64 (SB + F / 8)) by (exact (EX0 15%nat ltac:(lia))).
assert (E48' : ew E0 48 = Z_to_bv 64 FL) by (exact (EX0 16%nat ltac:(lia))).
assert (HF8' : 0 <= F / 8 <= F) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
assert (HWD : forall od v (m : nat), In (YP09.mkChunk od (CVal 8 (SOff m 0))) (YP09.r_chunks scb4_wordsR) ->
  (m < 49)%nat -> ew E0 m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 8 <= od /\ od + 8 <= 40 ->
  val_mem SEGS (mrestrict (w_H W5) mem5) (scb_sp1 sp0 + od) 8 v).
{ intros od v m Hin Hm Hv Hvr Hod.
  apply (recb_val_mem_frame_m (w_H W4) (w_H W5) (ms_mem msD) mem5 _ 8%nat).
  - refine (field_of_region E3 _ 9%nat (scb_sp1 sp0) _ 8 40 8 8 od 8%N (SOff m 0) v HR1D Y9 Hin _ _ _);
    [ rewrite scb_denot_off0, OLD3, OLD2, OLD1 by lia; exact Hv
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn [YP09.r_lo YP09.r_hi]; lia ].
  - intros i Hi. apply KS5; lia. }
pose proof (HWD 16 F 46%nat ltac:(unfold scb4_wordsR; cbn; tauto) ltac:(lia) E46' ltac:(lia) ltac:(lia)) as HW16_5.
pose proof (HWD 24 (SB + F / 8) 47%nat ltac:(unfold scb4_wordsR; cbn; tauto) ltac:(lia) E47'
  ltac:(unfold SB; lia) ltac:(lia)) as HW24_5.
pose proof (HWD 32 F 46%nat ltac:(unfold scb4_wordsR; cbn; tauto) ltac:(lia) E46' ltac:(lia) ltac:(lia)) as HW32_5.
assert (HFLG5 : rdword (rdW W5 mem5) (F + 120) = Some FL).
{ apply (rdword_of_val_mem SEGS); [|lia].
  apply (recb_val_mem_frame_m (w_H W4) (w_H W5) (ms_mem msD) mem5 _ 8%nat).
  - refine (field_of_region E3 _ 46%nat F _ 120 128 120 120 120 8%N (SOff 48 0) FL HR2D Y46 _ _ _ _);
    [ unfold scb4_flgR; cbn; tauto
    | rewrite scb_denot_off0, OLD3, OLD2, OLD1 by lia; exact E48'
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn [YP09.r_lo YP09.r_hi]; lia ].
  - intros i Hi. apply (GG4 1 fpos); [exact Hfin3 |
      left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite EFA3; change (fs_frame_bytes 1) with 128; lia |].
    intros Hf. destruct (HFPAlo _ Hf) as (_ & HnF & _). apply HnF. lia. }
rewrite <- EFA5 in HW16_5, HW24_5, HW32_5, HFLG5. rewrite <- EFL5 in HFLG5.
(* the FP state answer returns at: the entry's f registers except f10, the entry's fcsr or rounding mode 0 *)
assert (HFX5 : scb_fxok fr0 csr0 fx5).
{ destruct HFXOK as [Hf0 Hc0]. split.
  - intros k Hk. rewrite (HFX5a k Hk). exact (Hf0 k Hk).
  - destruct HFX5b as [Ec | Hz]; [| right; exact Hz].
    destruct Hc0 as [Ec0 | Hz0]; [left; rewrite Ec; exact Ec0 | right; unfold scb_frm0 in *; rewrite Ec; exact Hz0]. }
(* the post the release must leave *)
pose (QQ := fun (ly' : alayout) (S' : astate) (W' : world SEGS) (m' : word -> option byte) (d' : Model) =>
  exists (R' : rstate) (t : list byte) (O'' : list (Z * Z)),
  sup_chain_m R id ids = (R', t) /\ 4096 <= q2 < 2 ^ 64 /\
  rec_repA B ly' S' (rdW W' m') R' O'' /\
  (forall pn, In pn O'' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
  In (q2, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
  (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q2, Z.of_nat (length t) + 1)) /\
  ~ In q2 (map fst O'') /\
  astr_atR (rdW W' m') q2 t /\
  (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
     In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q2 (Z.of_nat (length t) + 1)) /\
  (forall pn, In pn (ablocks B ly' S') ->
     (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O'' \/ pn = (q2, Z.of_nat (length t) + 1)) /\
  blocks_bytes S' <= blocks_bytes S + LIVE_SUP_CHAIN R id ids /\
  mo_le MT S S' (XM_SUP_CHAIN MT R id ids)).
assert (SEP5 : scb4_sep req_size (ablocks B ly5 S5)).
{ intros b m p nn Hb Hp Hne. pose proof (sep_blocks SEGS B LAWS ly5 S5 W5 mem5 md5 b m p nn HAR5 Hb Hp Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. exact Hd. }
assert (POS5 : forall b m, In (b, m) (ablocks B ly5 S5) -> 0 <= m).
{ intros b m Hin. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR5 Hin) as (_ & _ & _ & _ & _ & _ & Hm). lia. }
destruct (scb4_final_blocks req_size (ablocks B ly S) bl1 Frec O O1 (ablocks B lyL SL) (ablocks B ly2 S2)
  l1 l2 (ablocks B ly3 S3) (ablocks B ly5 S5) O' lst (12 * n + 1) p1 (scb_m id) p2 (scb_m n) pq nd old q1 q2
  (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1)
  req_size_pos HOS (recb_ablocks_nodup_m B _ _ _ _ _ HAR) HPerm0 HFrecO HO1 HPermL HApL HAp1 HAp2
  ltac:(lia) ltac:(unfold scb_m; lia) ltac:(unfold scb_m; lia) ltac:(unfold nd; lia)
  Hperm2 Hfresh2 El1 (recb_ablocks_nodup_m B _ _ _ _ _ HARB) ltac:(rewrite El2; apply Permutation_refl)
  (fun pn Hin Hf => old_in_O ly3 S3 W4 (ms_mem msD) _ _ OD old pn HAR4 HREPD HOLD HOLDr Hin Hf)
  Hfr12 Hne12 Hbl5 HO5 SEP5 POS5) as (C1 & C2 & C3 & C4 & C5 & C6).
assert (HQQ : forall (W' : world SEGS) (m' : word -> option byte) (d' : Model),
  AR SEGS B ly5 (stack_free_state 1 fpos S5) W' m' d' -> wle W5 W' ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE \/
     (exists p nn, In (p, nn) (ablocks B ly5 S5) /\ p <= a < p + req_size nn)) -> rdW W' m' a = rdW W5 mem5 a) ->
  QQ ly5 (stack_free_state 1 fpos S5) W' m' d').
{ intros W' m' d' HAR' Hwle' KQ.
  assert (EAB5 : ablocks B ly5 (stack_free_state 1 fpos S5) = ablocks B ly5 S5)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  assert (EBB5 : blocks_bytes (stack_free_state 1 fpos S5) = blocks_bytes S5).
  { assert (B9 : blocks_bytes (stack_free_state 1 fpos S5) = bsum (ablocks B ly5 (stack_free_state 1 fpos S5)))
      by apply blocks_bytes_bsum.
    assert (B5 : blocks_bytes S5 = bsum (ablocks B ly5 S5)) by apply blocks_bytes_bsum.
    rewrite B9, B5, EAB5. reflexivity. }
  exists (fst (sup_chain_m R id ids)), (snd (sup_chain_m R id ids)), O'.
  rewrite EAB5, EBB5.
  split; [apply surjective_pairing|].
  split; [exact Hq4096|].
  split.
  { apply (rec_repA_kept ly5 S5 (rdW W5 mem5) ly5 (stack_free_state 1 fpos S5) (rdW W' m') _ O' HREP5).
    - intros pn Hpn. rewrite EAB5. exact (rec_repA_in _ _ _ _ _ HREP5 pn Hpn).
    - intros a Ha. apply KQ. left. unfold REC_SIZE. exact Ha.
    - intros a Ha. apply KQ. right. left. unfold SC_SIZE. exact Ha.
    - intros p nn i Hin Hi. apply KQ. right. right. exists p, nn.
      pose proof (rec_repA_in _ _ _ _ _ HREP5 (p, nn) Hin) as Hin5.
      pose proof (POS5 p nn Hin5) as Hnn. pose proof (req_size_pos nn Hnn) as [Rq1 Rq2].
      split; [exact Hin5 | lia]. }
  split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
  split.
  { apply (rastr_kept (rdW W5 mem5)); [exact HSTR5|].
    intros i Hi. apply KQ. right. right. exists q2, (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1).
    pose proof (req_size_pos (Z.of_nat (length (snd (sup_chain_m R id ids))) + 1) ltac:(lia)) as [Rq1 Rq2].
    split; [exact C2 | lia]. }
  split; [exact C5|]. split; [exact C6|].
  split.
  { unfold LIVE_SUP_CHAIN. fold n. lia. }
  unfold stack_free_state. apply (mo_le_set_fs_r MT MTLF).
  pose proof (mle_station MT S S3 S5 _ _ MTL
    (mle_station MT S S2 S3 _ _ MTL (mle_station MT S SL S2 _ _ MTL HMLEL HMLE2) HMLE3) HMLE5) as HMS.
  replace (XM_SUP_CHAIN MT R id ids) with
    (XM_RECORD MT R + XM_XMALLOC MT (12 * n + 1) + XM_ARG_S MT (Some (dec id)) + XM_ARG_S MT (Some (dec n)) +
     XM_ARG_S MT (Some (dec_list ids)) + mo_free MT + XM_ANSWER MT (snd (sup_chain_m R id ids)))
    by (unfold XM_SUP_CHAIN; fold n; reflexivity).
  exact HMS. }
(* the release, the epilogue and the return *)
eapply SRr_mono.
{ refine (scb4_rel ly S W regs mem md O fr0 csr0 fx5 ly5 S5 W5 regs5 mem5 md5 fpos q2 _ (EV_SUP_CHAIN R) QQ
    HFX5 HJ5 _ ltac:(lia) Hra R2_5 R3_5 R4_5 R8_5 R9_5 Hq10 HFR5 HW16_5 HW24_5 HW32_5 HFLG5 HQQ).
  rewrite HEVsplit. unfold scb_kL in *. rewrite HEVRS. lia. }
cbv beta. intros W6 c6 _ (fx6 & ly6 & S6 & regs6 & mem6 & md6 & Ec & HFX6 & HJ6 & HP6 & H106 & HQ6).
exists fx6, ly6, S6, regs6, mem6, md6.
split; [exact Ec|]. split; [exact HFX6|]. split; [exact HJ6|]. split; [exact HP6|].
destruct HQ6 as (R' & t & O'' & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
exists R', t, q2, O''.
split; [exact G1|]. split; [exact H106|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
split; [exact G5|]. split; [exact G6|]. split; [exact G7|]. split; [exact G8|]. split; [exact G9|].
split; [exact G10|]. split; [exact G11 | exact G12].
Qed.
End tail.

End e.
End f.
End d.
