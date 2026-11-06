(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec SymStepR.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosFxStep PIosFxSound PIosRegs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLin SegTmpl SegGhost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S. Import AX2F. Import ST.

Module SC.

(* [comment removed for export] *)
Definition wn : Type := (expr * Z * expr)%type.

Definition sub_win (sg : list expr) (w : wn) : wn := let '(b, off, n) := w in (esub sg b, off, esub sg n).

Definition in_win (E : env) (w : wn) (x : Z) : Prop := let '(lo, hi) := SG.win_den E w in (lo <= x < hi).

(* [comment removed for export] *)
Definition win_apart (kn : list kentry) (b : expr) (k : Z) (n : expr) (Wc : list wn) : bool :=
  forallb (fun w => let '(b', k', n') := w in SLin.apart2 kn b k n b' k' n') Wc.

(* [comment removed for export] *)
Definition survives (kn : list kentry) (Wc : list wn) (K : kentry) : bool :=
  match K with
  | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ | KWr _ _ | KUnk _ _ => true
  | KWord a w _ => (Nat.leb w 8 && win_apart kn (a_base a) (a_off a) (elen w) Wc)%bool
  | KZero a n | KBlob a n _ | KFill a n _ => win_apart kn (a_base a) (a_off a) n Wc
  | KImg lo hi => (Z.ltb (hi - lo) (2^64) && win_apart kn (ELit 0) lo (ELit (hi - lo)) Wc)%bool
  end.

(* [comment removed for export] *)
Definition post_sg (G : nat) (sg : list expr) (n0 ns : nat) : list expr :=
  map (fun j => if Nat.ltb j G then nth j sg (ELit 0) else EVar (n0 + j)) (seq 0 ns).

Definition ecomb (E' E2 : env) (n0 : nat) : env :=
  Env (fun v => if Nat.ltb v n0 then ev E' v else ev E2 (v - n0)) (eb E').

Definition is_brb (sc : sidecond) : bool := match sc with SCBr _ _ _ _ => true | _ => false end.

(* [comment removed for export] *)
Definition apart_all (kn : list kentry) (F : list SG.gwin) (Wc : list wn) : bool :=
  forallb (fun f => let '(b, k, n) := f in win_apart kn b k n Wc) F.

(* [comment removed for export] *)
Definition pin1 (kn : list kentry) (b : expr) (k : Z) (n : expr) (w : wn) : bool :=
  let '(b', k', n') := w in SLin.xinside2 kn b k n b' k' n'.
(* [comment removed for export] *)
Definition pin2 (kn : list kentry) (b : expr) (k : Z) (n : expr) (w : wn) : bool :=
  let '(b', k', n') := w in if shares_var b b' then false else SLin.xinside_f kn b k n b' k' n'.
Definition pres_in (kn : list kentry) (PR : option (list wn)) (b : expr) (k : Z) (n : expr) : bool :=
  match PR with
  | None => true
  | Some l => if SLin.lex (pin1 kn b k n) l then true else SLin.lex (pin2 kn b k n) l
  end.

Definition in_PR (E : env) (PR : option (list wn)) (x : Z) : Prop :=
  match PR with None => True | Some l => exists w, In w l /\ in_win E w x end.

Definition survivesP (kn : list kentry) (Wc : list wn) (PR : option (list wn)) (K : kentry) : bool :=
  match K with
  | KRange _ _ _ | KAlign _ _ | KDisj _ _ _ _ | KWr _ _ | KUnk _ _ => true
  | KWord a w _ => if (Nat.leb w 8 && win_apart kn (a_base a) (a_off a) (elen w) Wc)%bool then pres_in kn PR (a_base a) (a_off a) (elen w) else false
  | KZero a n | KBlob a n _ | KFill a n _ => if win_apart kn (a_base a) (a_off a) n Wc then pres_in kn PR (a_base a) (a_off a) n else false
  | KImg lo hi => if (Z.ltb (hi - lo) (2^64) && win_apart kn (ELit 0) lo (ELit (hi - lo)) Wc)%bool
                  then pres_in kn PR (ELit 0) lo (ELit (hi - lo)) else false
  end.

Definition apart_allP (kn : list kentry) (F : list SG.gwin) (Wc : list wn) (PR : option (list wn)) : bool :=
  forallb (fun f => let '(b, k, n) := f in if win_apart kn b k n Wc then pres_in kn PR b k n else false) F.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
Variable segs : list Segment.

Lemma win_apart_ok : forall E M kn b k n Wc, know_ok segs E M kn -> win_apart kn b k n Wc = true ->
  forall w, In w Wc -> forall x, (estart E (SA b k) <= x < estart E (SA b k) + elenZ E n) -> ~ in_win E w x.
Proof.
  intros E M kn b k n Wc HK H w Hw x Hx. unfold win_apart in H.
  pose proof (proj1 (forallb_forall _ _) H w Hw) as A. destruct w as [[b' k'] n']. cbv beta iota in A.
  pose proof (SLin.apart2_sound segs E M kn b k n b' k' n' HK A) as R.
  unfold in_win, SG.win_den. unfold estart, elenZ in R, Hx. cbn [a_base a_off] in R, Hx. lia.
Qed.

(* [comment removed for export] *)
Lemma wrel_grows : forall m m', wrel segs m m' -> mem_grows m m'.
Proof.
  intros m m' H. induction H as [m|m a bs m' Hok H IH]; [apply mem_grows_refl|].
  intros x Hx. apply IH. apply write_to_mem_grows. exact Hx.
Qed.

Lemma survives_ok : forall E M1 M2 kn Wc K,
  know_ok segs E M1 kn -> mem_grows M1 M2 ->
  (forall x : word, (forall w, In w Wc -> ~ in_win E w (bv_unsigned x)) -> M2 x = M1 x) ->
  kentry_ok segs E M1 K -> survives kn Wc K = true -> kentry_ok segs E M2 K.
Proof.
  intros E M1 M2 kn Wc K HK Hg FR HK1 Hs.
  assert (OUTR : forall b k n, win_apart kn b k n Wc = true -> flat E (SA b k) (elenZ E n) ->
            forall i, 0 <= i < elenZ E n -> M2 (Z_to_bv 64 (estart E (SA b k) + i)) = M1 (Z_to_bv 64 (estart E (SA b k) + i))).
  { intros b k n Ha Hfl i Hi. apply FR. intros w Hw. rewrite u_small by (destruct Hfl as (?&?&?&?); lia).
    apply (win_apart_ok E M1 kn b k n Wc HK Ha w Hw). lia. }
  destruct K as [[kb kk] w v|[kb kk] n|[kb kk] n bk|lo hi|ae am|re rlo rhi|[wb wk] wn0|da1 dn1 da2 dn2|[kb kk] n fc|[kb kk] n];
    cbn [survives kentry_ok] in Hs, HK1 |- *.
  - (* [comment removed for export] *) apply andb_prop in Hs as [Hw8 Ha]. apply Nat.leb_le in Hw8. destruct HK1 as (Hw & Hfl & Hrd).
    split; [exact Hw|]. split; [exact Hfl|]. rewrite <- Hrd. apply rdn_ext.
    + rewrite (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
    + intros x Hx. rewrite (flat_u E _ _ Hfl) in Hx. apply FR. intros w' Hw'.
      apply (win_apart_ok E M1 kn kb kk (elen w) Wc HK Ha w' Hw'). rewrite elenZ_elen by exact Hw8. lia.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (OUTR kb kk n Hs Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) destruct HK1 as (Hfl & Hl & Hz). split; [exact Hfl|]. split; [exact Hl|].
    intros i Hi. rewrite (OUTR kb kk n Hs Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) apply andb_prop in Hs as [Hsz Ha]. apply Z.ltb_lt in Hsz. destruct HK1 as (Hlo & Hhi & Hn).
    split; [exact Hlo|]. split; [exact Hhi|]. intros i Hi.
    assert (E0 : estart E (SA (ELit 0) lo) = lo) by (unfold estart; cbn [a_base a_off edenot]; rewrite Z_to_bv_unsigned; reflexivity).
    assert (E1 : elenZ E (ELit (hi - lo)) = hi - lo) by (unfold elenZ; cbn [edenot]; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; apply Z.mod_small; lia).
    rewrite FR; [apply Hn; exact Hi|]. intros w Hw. rewrite u_small by lia.
    apply (win_apart_ok E M1 kn (ELit 0) lo (ELit (hi - lo)) Wc HK Ha w Hw). rewrite E0, E1. lia.
  - exact HK1.
  - exact HK1.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hs0]. split; [exact Hfl|]. intros d m Hd Hm. eapply store_ok_mono; [exact Hg | apply Hs0; assumption].
  - exact HK1.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (OUTR kb kk n Hs Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) apply (kentry_ok_unk_grows segs E M1 M2 _ _ Hg). exact HK1.
Qed.

Lemma survives_all_ok : forall E M1 M2 kn Wc,
  know_ok segs E M1 kn -> mem_grows M1 M2 ->
  (forall x : word, (forall w, In w Wc -> ~ in_win E w (bv_unsigned x)) -> M2 x = M1 x) ->
  know_ok segs E M2 (List.filter (survives kn Wc) kn).
Proof.
  intros E M1 M2 kn Wc HK Hg FR. unfold know_ok. apply Forall_forall. intros K HKin. apply filter_In in HKin as [HKin Hs].
  exact (survives_ok E M1 M2 kn Wc K HK Hg FR (proj1 (Forall_forall _ _) HK K HKin) Hs).
Qed.

Lemma ecomb_agree : forall E' E2 n0, eagree n0 E' (ecomb E' E2 n0).
Proof.
  intros E' E2 n0. split; [|reflexivity]. intros v Hv. cbn [ecomb ev]. apply Nat.ltb_lt in Hv. rewrite Hv. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma post_sg_agree : forall E' E2 G sg n0 ns,
  (forall j, (j < G)%nat -> ev E2 j = edenot E' (nth j sg (ELit 0))) -> eb E2 = eb E' ->
  forallb (expr_vars_lt n0) sg = true ->
  forall j, (j < ns)%nat -> ev (senv (ecomb E' E2 n0) (post_sg G sg n0 ns)) j = ev E2 j.
Proof.
  intros E' E2 G sg n0 ns HG Hb Hc j Hj. cbn [senv ev]. unfold vals_ev, post_sg.
  set (f := fun j0 => if Nat.ltb j0 G then nth j0 sg (ELit 0) else EVar (n0 + j0)).
  rewrite (nth_indep _ (Z_to_bv 64 0) (edenot (ecomb E' E2 n0) (f 0%nat))) by (rewrite !length_map, length_seq; exact Hj).
  rewrite map_nth. rewrite map_nth. rewrite seq_nth by exact Hj. cbn [Nat.add]. unfold f.
  destruct (Nat.ltb j G) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt. rewrite (HG j Hlt).
    assert (Hcl : expr_vars_lt n0 (nth j sg (ELit 0)) = true).
    { destruct (Nat.lt_ge_cases j (length sg)) as [Hl|Hl].
      - exact (proj1 (forallb_forall _ _) Hc _ (nth_In _ _ Hl)).
      - rewrite nth_overflow by exact Hl. reflexivity. }
    symmetry. apply (edenot_agree n0 E' (ecomb E' E2 n0)); [apply eagree_env_agree, ecomb_agree | exact Hcl].
  - cbn [edenot ecomb ev]. destruct (Nat.ltb (n0 + j) n0) eqn:H0; [apply Nat.ltb_lt in H0; lia|].
    f_equal. lia.
Qed.

Lemma expr_vars_lt_mono : forall b b' e, expr_vars_lt b e = true -> (b <= b')%nat -> expr_vars_lt b' e = true.
Proof.
  intros b b' e H Hle. induction e; cbn [expr_vars_lt] in *; try reflexivity;
    try (apply andb_prop in H as [H1 H2]; rewrite IHe1, IHe2 by assumption; reflexivity); try (apply IHe; exact H).
  apply Nat.ltb_lt in H. apply Nat.ltb_lt. lia.
Qed.

Lemma senv_eb : forall E sg, eb (senv E sg) = eb E.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma edenot_ext_lt : forall n E1 E2 e, (forall j, (j < n)%nat -> ev E1 j = ev E2 j) -> eb E1 = eb E2 ->
  expr_vars_lt n e = true -> edenot E1 e = edenot E2 e.
Proof. intros n E1 E2 e Hv Hb He. apply (edenot_agree n E1 E2 e); [split; [exact Hv | exact Hb] | exact He]. Qed.

Lemma br_filter_ok : forall M M' E path, scs_denot segs M E path -> scs_denot segs M' E (List.filter is_brb path).
Proof.
  intros M M' E path H. unfold scs_denot in *. apply Forall_forall. intros sc Hin. apply filter_In in Hin as [Hin Hb].
  pose proof (proj1 (Forall_forall _ _) H sc Hin) as Hs. destruct sc; try discriminate Hb. exact Hs.
Qed.

(* [comment removed for export] *)
Lemma apart_all_ok : forall E M kn F Wc, know_ok segs E M kn -> apart_all kn F Wc = true ->
  forall x : Z, (exists w, In w F /\ let '(lo, hi) := SG.win_den E w in (lo <= x < hi)) -> forall wc, In wc Wc -> ~ in_win E wc x.
Proof.
  intros E M kn F Wc HK H x (f & Hf & Hx) wc Hwc. unfold apart_all in H.
  pose proof (proj1 (forallb_forall _ _) H f Hf) as A. destruct f as [[b k] n]. cbv beta iota in A.
  apply (win_apart_ok E M kn b k n Wc HK A wc Hwc x). unfold SG.win_den in Hx. unfold estart, elenZ. cbn [a_base a_off]. lia.
Qed.

(* [comment removed for export] *)
Lemma pres_in_ok : forall E M kn PR b k n, know_ok segs E M kn -> pres_in kn PR b k n = true ->
  forall x, (estart E (SA b k) <= x < estart E (SA b k) + elenZ E n) -> in_PR E PR x.
Proof.
  intros E M kn [l|] b k n HK H x Hx; [|exact I]. cbn [pres_in] in H.
  assert (C : exists w, In w l /\ (let '(b', k', n') := w in
     estart E (SA b' k') <= estart E (SA b k) /\ estart E (SA b k) + elenZ E n <= estart E (SA b' k') + elenZ E n')).
  { destruct (SLin.lex (pin1 kn b k n) l) eqn:H1.
    - apply SLin.lex_exists in H1 as ([[b' k'] n'] & Hw & Hx'). exists (b', k', n'). split; [exact Hw|]. unfold pin1 in Hx'.
      exact (SLin.xinside2_sound segs E M kn b k n b' k' n' HK Hx').
    - apply SLin.lex_exists in H as ([[b' k'] n'] & Hw & Hx'). exists (b', k', n'). split; [exact Hw|].
      unfold pin2 in Hx'. destruct (shares_var b b'); [discriminate|].
      exact (SLin.xinside_f_sound segs E M kn b k n b' k' n' HK Hx'). }
  destruct C as ([[b' k'] n'] & Hw & A & B).
  exists (b', k', n'). split; [exact Hw|]. unfold in_win, SG.win_den. unfold estart, elenZ in A, B, Hx. cbn [a_base a_off] in A, B, Hx. lia.
Qed.

Lemma survivesP_ok : forall E M1 M2 kn Wc PR K,
  know_ok segs E M1 kn -> mem_grows M1 M2 ->
  (forall x : word, (forall w, In w Wc -> ~ in_win E w (bv_unsigned x)) -> in_PR E PR (bv_unsigned x) -> M2 x = M1 x) ->
  kentry_ok segs E M1 K -> survivesP kn Wc PR K = true -> kentry_ok segs E M2 K.
Proof.
  intros E M1 M2 kn Wc PR K HK Hg FR HK1 Hs.
  assert (OUTR : forall b k n, win_apart kn b k n Wc = true -> pres_in kn PR b k n = true -> flat E (SA b k) (elenZ E n) ->
            forall i, 0 <= i < elenZ E n -> M2 (Z_to_bv 64 (estart E (SA b k) + i)) = M1 (Z_to_bv 64 (estart E (SA b k) + i))).
  { intros b k n Ha Hp Hfl i Hi. apply FR.
    - intros w Hw. rewrite u_small by (destruct Hfl as (?&?&?&?); lia).
      apply (win_apart_ok E M1 kn b k n Wc HK Ha w Hw). lia.
    - rewrite u_small by (destruct Hfl as (?&?&?&?); lia). apply (pres_in_ok E M1 kn PR b k n HK Hp). lia. }
  destruct K as [[kb kk] w v|[kb kk] n|[kb kk] n bk|lo hi|ae am|re rlo rhi|[wb wk] wn0|da1 dn1 da2 dn2|[kb kk] n fc|[kb kk] n];
    cbn [survivesP kentry_ok a_base a_off] in Hs, HK1 |- *.
  - (* [comment removed for export] *) remember (Nat.leb w 8 && win_apart kn kb kk (elen w) Wc)%bool as c eqn:Hc. destruct c; [|cbn in Hs; discriminate].
    symmetry in Hc. apply andb_prop in Hc as [Hw8 Ha]. apply Nat.leb_le in Hw8. destruct HK1 as (Hw & Hfl & Hrd).
    split; [exact Hw|]. split; [exact Hfl|]. rewrite <- Hrd. apply rdn_ext.
    + rewrite (flat_u E _ _ Hfl). destruct Hfl as (?&?&?&?). lia.
    + intros x Hx. rewrite (flat_u E _ _ Hfl) in Hx. apply FR.
      * intros w' Hw'. apply (win_apart_ok E M1 kn kb kk (elen w) Wc HK Ha w' Hw'). rewrite elenZ_elen by exact Hw8. lia.
      * apply (pres_in_ok E M1 kn PR kb kk (elen w) HK Hs). rewrite elenZ_elen by exact Hw8. lia.
  - (* [comment removed for export] *) remember (win_apart kn kb kk n Wc) as c eqn:Ha. destruct c; [|cbn in *; discriminate]. symmetry in Ha.
    destruct HK1 as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (OUTR kb kk n Ha Hs Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) remember (win_apart kn kb kk n Wc) as c eqn:Ha. destruct c; [|cbn in *; discriminate]. symmetry in Ha.
    destruct HK1 as (Hfl & Hl & Hz). split; [exact Hfl|]. split; [exact Hl|].
    intros i Hi. rewrite (OUTR kb kk n Ha Hs Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) remember (Z.ltb (hi - lo) (2^64) && win_apart kn (ELit 0) lo (ELit (hi - lo)) Wc)%bool as c eqn:Hc. destruct c; [|cbn in Hs; discriminate].
    symmetry in Hc. apply andb_prop in Hc as [Hsz Ha]. apply Z.ltb_lt in Hsz. destruct HK1 as (Hlo & Hhi & Hn).
    split; [exact Hlo|]. split; [exact Hhi|]. intros i Hi.
    assert (E0 : estart E (SA (ELit 0) lo) = lo) by (unfold estart; cbn [a_base a_off edenot]; rewrite Z_to_bv_unsigned; reflexivity).
    assert (E1 : elenZ E (ELit (hi - lo)) = hi - lo) by (unfold elenZ; cbn [edenot]; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; apply Z.mod_small; lia).
    rewrite FR; [apply Hn; exact Hi| |].
    + intros w Hw. rewrite u_small by lia.
      apply (win_apart_ok E M1 kn (ELit 0) lo (ELit (hi - lo)) Wc HK Ha w Hw). rewrite E0, E1. lia.
    + rewrite u_small by lia. apply (pres_in_ok E M1 kn PR (ELit 0) lo (ELit (hi - lo)) HK Hs). rewrite E0, E1. lia.
  - exact HK1.
  - exact HK1.
  - (* [comment removed for export] *) destruct HK1 as [Hfl Hs0]. split; [exact Hfl|]. intros d m Hd Hm. eapply store_ok_mono; [exact Hg | apply Hs0; assumption].
  - exact HK1.
  - (* [comment removed for export] *) remember (win_apart kn kb kk n Wc) as c eqn:Ha. destruct c; [|cbn in *; discriminate]. symmetry in Ha.
    destruct HK1 as [Hfl Hz]. split; [exact Hfl|]. intros i Hi. rewrite (OUTR kb kk n Ha Hs Hfl i Hi). apply Hz. exact Hi.
  - (* [comment removed for export] *) apply (kentry_ok_unk_grows segs E M1 M2 _ _ Hg). exact HK1.
Qed.

Lemma survivesP_all_ok : forall E M1 M2 kn Wc PR,
  know_ok segs E M1 kn -> mem_grows M1 M2 ->
  (forall x : word, (forall w, In w Wc -> ~ in_win E w (bv_unsigned x)) -> in_PR E PR (bv_unsigned x) -> M2 x = M1 x) ->
  know_ok segs E M2 (List.filter (survivesP kn Wc PR) kn).
Proof.
  intros E M1 M2 kn Wc PR HK Hg FR. unfold know_ok. apply Forall_forall. intros K HKin. apply filter_In in HKin as [HKin Hs].
  exact (survivesP_ok E M1 M2 kn Wc PR K HK Hg FR (proj1 (Forall_forall _ _) HK K HKin) Hs).
Qed.

(* [comment removed for export] *)
Lemma apart_allP_ok : forall E M kn F Wc PR, know_ok segs E M kn -> apart_allP kn F Wc PR = true ->
  forall x : Z, (exists w, In w F /\ let '(lo, hi) := SG.win_den E w in (lo <= x < hi)) ->
  (forall wc, In wc Wc -> ~ in_win E wc x) /\ in_PR E PR x.
Proof.
  intros E M kn F Wc PR HK H x (f & Hf & Hx). unfold apart_allP in H.
  pose proof (proj1 (forallb_forall _ _) H f Hf) as A. destruct f as [[b k] n]. cbv beta iota in A.
  remember (win_apart kn b k n Wc) as c eqn:Ha. destruct c; [|cbn in *; discriminate]. symmetry in Ha.
  unfold SG.win_den in Hx.
  split.
  - intros wc Hwc. apply (win_apart_ok E M kn b k n Wc HK Ha wc Hwc x). unfold estart, elenZ. cbn [a_base a_off]. lia.
  - apply (pres_in_ok E M kn PR b k n HK A). unfold estart, elenZ. cbn [a_base a_off]. lia.
Qed.

End Sound.
End SC.
