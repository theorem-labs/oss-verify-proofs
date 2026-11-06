(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Fpu Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Import FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Import Prelim SoftFloat.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require FloatScan.
Import OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec.FloatScan.DoubleOps.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require Import FloatScan.
Open Scope Z_scope.

Local Opaque zrepeat.
Local Opaque f128_mul f128_add f128_sub f128_div f128_of_d f128_to_d f128_le f128_ge f128_to_u32 f128_of_u32 f128_of_i32.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u32_range : forall x, 0 <= u32 x < 2^32.
Proof. intros. unfold u32. apply Z.mod_pos_bound. lia. Qed.
Lemma u64_range : forall x, 0 <= u64 x < 2^64.
Proof. intros. unfold u64. apply Z.mod_pos_bound. lia. Qed.
Lemma u32_id : forall x, 0 <= x < 2^32 -> u32 x = x.
Proof. intros. unfold u32. apply Z.mod_small. lia. Qed.
Lemma u64_id : forall x, 0 <= x < 2^64 -> u64 x = x.
Proof. intros. unfold u64. apply Z.mod_small. lia. Qed.
Lemma s32_id : forall x, -2^31 <= x < 2^31 -> s32 x = x.
Proof. intros. unfold s32. rewrite Z.mod_small; lia. Qed.

Lemma MASK_eq : MASK = Z.ones 11.
Proof. reflexivity. Qed.
Lemma land_MASK : forall k, Z.land k MASK = k mod 2048.
Proof. intros. rewrite MASK_eq, Z.land_ones by lia. reflexivity. Qed.
Lemma land_MASK_range : forall k, 0 <= Z.land k MASK < 2048.
Proof. intros. rewrite land_MASK. apply Z.mod_pos_bound. lia. Qed.
Lemma land_MASK_small : forall k, 0 <= k < 2048 -> Z.land k MASK = k.
Proof. intros. rewrite land_MASK. apply Z.mod_small. lia. Qed.

Lemma lor_c_32_120 : forall c, 0 <= c -> c <> 120 -> c <> 88 -> (Z.lor c 32 =? 120) = false.
Proof.
  intros c Hc H1 H2. apply Z.eqb_neq. intros E.
  assert (Ht : forall i, 0 <= i -> i <> 5 -> Z.testbit c i = Z.testbit 120 i).
  { intros i Hi Hn. rewrite <- E, Z.lor_spec.
    replace (Z.testbit 32 i) with false; [now rewrite orb_false_r|].
    symmetry. change 32 with (2^5). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
  destruct (Z.testbit c 5) eqn:B5.
  - apply H1. apply Z.bits_inj'. intros i Hi. destruct (Z.eq_dec i 5); [subst; rewrite B5; reflexivity| now apply Ht].
  - apply H2. apply Z.bits_inj'. intros i Hi. destruct (Z.eq_dec i 5); [subst; rewrite B5; reflexivity|].
    rewrite Ht by lia. change 120 with (Z.lor 88 32). rewrite Z.lor_spec.
    replace (Z.testbit 32 i) with false; [now rewrite orb_false_r|].
    symmetry. change 32 with (2^5). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

(* [comment removed for export] *)
Definition bitlen (x : Z) : Z := if 0 <? x then Z.log2 x + 1 else 0.
Lemma bitlen_nonneg : forall x, 0 <= bitlen x.
Proof. intros. unfold bitlen. destruct (Z.ltb_spec 0 x); [pose proof (Z.log2_nonneg x); lia| lia]. Qed.
Lemma bitlen_le32 : forall x, 0 <= x < 2^32 -> bitlen x <= 32.
Proof.
  intros x Hx. unfold bitlen. destruct (Z.ltb_spec 0 x); [|lia].
  assert (Z.log2 x < 32) by (apply Z.log2_lt_pow2; lia). lia.
Qed.
Lemma bitlen_pos : forall x, 0 < x -> 1 <= bitlen x.
Proof. intros. unfold bitlen. destruct (Z.ltb_spec 0 x); [pose proof (Z.log2_nonneg x); lia|lia]. Qed.
Lemma bitlen_shiftr_lt : forall x s, 0 < x -> 1 <= s -> bitlen (Z.shiftr x s) < bitlen x.
Proof.
  intros x s Hx Hs. unfold bitlen. destruct (Z.ltb_spec 0 x); [|lia].
  destruct (Z.ltb_spec 0 (Z.shiftr x s)); [|pose proof (Z.log2_nonneg x); lia].
  rewrite Z.log2_shiftr by lia.
  rewrite Z.shiftr_div_pow2 in H0 by lia.
  assert (Hxs : 2 ^ s <= x).
  { destruct (Z.lt_ge_cases x (2^s)); [|lia]. rewrite Z.div_small in H0; lia. }
  assert (s <= Z.log2 x). { rewrite <- (Z.log2_pow2 s) by lia. apply Z.log2_le_mono. lia. }
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma znth_neg : forall l i, i < 0 -> znth l i = 0.
Proof. intros. unfold znth. destruct (Z.ltb_spec i 0); [reflexivity|lia]. Qed.
Lemma znth_ge : forall l i, zlength l <= i -> znth l i = 0.
Proof.
  intros l i H. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [reflexivity|].
  apply nth_overflow. lia.
Qed.
Lemma znth_app_l : forall l1 l2 i, i < zlength l1 -> znth (l1 ++ l2) i = znth l1 i.
Proof.
  intros l1 l2 i H. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [reflexivity|].
  apply app_nth1. lia.
Qed.
Lemma znth_app_r : forall l1 l2 i, zlength l1 <= i -> znth (l1 ++ l2) i = znth l2 (i - zlength l1).
Proof.
  intros l1 l2 i H. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [lia|].
  destruct (Z.ltb_spec (i - Z.of_nat (length l1)) 0); [lia|].
  rewrite app_nth2 by lia. f_equal. lia.
Qed.
Lemma znth_In_or : forall l i, znth l i = 0 \/ In (znth l i) l.
Proof.
  intros l i. destruct (Z.lt_ge_cases i 0); [left; now apply znth_neg|].
  destruct (Z.lt_ge_cases i (zlength l)); [right; apply znth_range; lia| left; now apply znth_ge].
Qed.

(* [comment removed for export] *)
Lemma znth_snoc0 : forall l i, znth (l ++ [0]) i = 0 \/ (0 <= i < zlength l /\ In (znth (l ++ [0]) i) l).
Proof.
  intros l i. destruct (Z.lt_ge_cases i 0); [left; now apply znth_neg|].
  destruct (Z.lt_ge_cases i (zlength l)).
  - right. split; [lia|]. rewrite znth_app_l by lia. apply znth_range. lia.
  - left. rewrite znth_app_r by lia. unfold znth. destruct (Z.ltb_spec (i - zlength l) 0); [reflexivity|].
    destruct (Z.to_nat (i - zlength l)) as [|[|n]]; reflexivity.
Qed.

Lemma znth_zrepeat : forall v n i, znth (zrepeat v n) i = (if (0 <=? i) && (i <? n) then v else 0).
Proof.
  intros v n i. Local Transparent zrepeat. unfold znth, zrepeat.
  destruct (Z.ltb_spec i 0); cbn [andb]. { destruct (Z.leb_spec 0 i); [lia|reflexivity]. }
  destruct (Z.leb_spec 0 i); [|lia]. cbn [andb].
  destruct (Z.ltb_spec i n).
  - apply nth_repeat_lt. lia.
  - apply nth_overflow. rewrite repeat_length. lia.
Qed.
Local Opaque zrepeat.

(* [comment removed for export] *)
Definition W32 (x : list Z) : Prop := forall i, 0 <= znth x i < 2^32.
Lemma W32_zrepeat : forall n, W32 (zrepeat 0 n).
Proof. intros n i. rewrite znth_zrepeat. destruct (_ && _); lia. Qed.
Lemma W32_zupd : forall x i v, W32 x -> 0 <= v < 2^32 -> W32 (zupd x i v).
Proof.
  intros x i v Hw Hv j. destruct (Z.eq_dec i j).
  - subst. destruct (Z.lt_ge_cases j 0). { rewrite znth_neg by lia. lia. }
    destruct (Z.lt_ge_cases j (zlength x)).
    + rewrite znth_zupd_eq; [lia|lia].
    + rewrite znth_ge; [lia|]. rewrite zlength_zupd. lia.
  - rewrite znth_zupd_neq by lia. apply Hw.
Qed.
Lemma W32_u32 : forall x i v, W32 x -> W32 (zupd x i (u32 v)).
Proof. intros. apply W32_zupd; [assumption| apply u32_range]. Qed.

Lemma Z_lor_lt_pow2' : forall a b n, 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof. intros. apply Z_lor_lt_pow2; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition setrpos (f : shfile) (r : Z) : shfile :=
  mkSh (sh_buf f) r (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f).

(* [comment removed for export] *)
Definition sh_N (f : shfile) : Z := if sh_stdio f then sh_n f else zlength (sh_buf f) - 1.
Definition sh_wf (f : shfile) : Prop :=
  if sh_stdio f then sh_rpos f <= sh_n f <= zlength (sh_buf f) - 1
  else (exists l, sh_buf f = l ++ [0]) /\ sh_shlim_neg f = false.
Definition Phi (f : shfile) : Z := sh_N f - sh_rpos f.

(* [comment removed for export] *)
Definition contc (c : Z) : Prop := c <> 0 /\ c <> -1.

Ltac getc_cases f :=
  unfold sh_getc; destruct (sh_stdio f) eqn:?ST; cbn [negb];
  [destruct (Z.eqb_spec (sh_rpos f) (sh_n f)); cbn [negb]|].

Lemma sh_getc_buf : forall f, sh_buf (snd (sh_getc f)) = sh_buf f.
Proof. intros f. getc_cases f; reflexivity. Qed.
Lemma sh_getc_stdio : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
Proof. intros f. getc_cases f; cbn; congruence. Qed.
Lemma sh_getc_cnt0 : forall f, sh_cnt0 (snd (sh_getc f)) = sh_cnt0 f.
Proof. intros f. getc_cases f; reflexivity. Qed.
Lemma sh_getc_n : forall f, sh_n (snd (sh_getc f)) = sh_n f.
Proof. intros f. getc_cases f; reflexivity. Qed.
Lemma sh_getc_N : forall f, sh_N (snd (sh_getc f)) = sh_N f.
Proof. intros f. unfold sh_N. getc_cases f; cbn; rewrite ?ST; reflexivity. Qed.
Lemma sh_getc_rpos : forall f, sh_rpos f <= sh_rpos (snd (sh_getc f)) <= sh_rpos f + 1.
Proof. intros f. getc_cases f; cbn; lia. Qed.
Lemma sh_getc_neg : forall f, sh_stdio f = false -> sh_shlim_neg (snd (sh_getc f)) = sh_shlim_neg f.
Proof. intros f H. unfold sh_getc. rewrite H. reflexivity. Qed.
Lemma sh_getc_wf : forall f, sh_wf f -> sh_wf (snd (sh_getc f)).
Proof.
  intros f Hwf. unfold sh_wf in *. getc_cases f; cbn; rewrite ?ST; cbn; try lia. exact Hwf.
Qed.
(* [comment removed for export] *)
Lemma sh_getc_char : forall f,
  (fst (sh_getc f) = -1 /\ sh_rpos (snd (sh_getc f)) = sh_rpos f /\ sh_stdio f = true /\ sh_rpos f = sh_n f)
  \/ (fst (sh_getc f) = znth (sh_buf f) (sh_rpos f) /\ sh_rpos (snd (sh_getc f)) = sh_rpos f + 1
      /\ (sh_stdio f = true -> sh_rpos f <> sh_n f)).
Proof. intros f. getc_cases f; cbn; [left|right|right]; repeat split; auto; try congruence. Qed.
(* [comment removed for export] *)
Lemma sh_getc_cont : forall f, sh_wf f -> contc (fst (sh_getc f)) ->
  sh_rpos (snd (sh_getc f)) = sh_rpos f + 1 /\ sh_rpos f < sh_N f.
Proof.
  intros f Hwf [H0 H1]. unfold sh_wf, sh_N in *.
  destruct (sh_getc_char f) as [(E & _)|(E & R & S)]; [congruence|].
  split; [exact R|]. rewrite E in H0.
  destruct (sh_stdio f) eqn:ST.
  - specialize (S eq_refl). lia.
  - destruct Hwf as [[l Hl] _]. rewrite Hl in H0 |- *.
    destruct (znth_snoc0 l (sh_rpos f)) as [E0|[R0 _]]; [congruence|].
    unfold zlength in *. rewrite length_app. cbn [length]. lia.
Qed.
Lemma sh_getc_nonstdio : forall f, sh_stdio f = false ->
  sh_getc f = (znth (sh_buf f) (sh_rpos f), setrpos f (sh_rpos f + 1)).
Proof. intros f H. unfold sh_getc, setrpos. rewrite H. reflexivity. Qed.

Lemma sh_unget_rpos : forall f, sh_rpos f - 1 <= sh_rpos (sh_unget f) <= sh_rpos f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f); cbn; lia. Qed.
Lemma sh_unget_rpos_nonstdio : forall f, sh_shlim_neg f = false -> sh_rpos (sh_unget f) = sh_rpos f - 1.
Proof. intros f H. unfold sh_unget. rewrite H. reflexivity. Qed.
Lemma sh_unget_buf : forall f, sh_buf (sh_unget f) = sh_buf f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
Lemma sh_unget_stdio : forall f, sh_stdio (sh_unget f) = sh_stdio f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
Lemma sh_unget_cnt0 : forall f, sh_cnt0 (sh_unget f) = sh_cnt0 f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
Lemma sh_unget_n : forall f, sh_n (sh_unget f) = sh_n f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
Lemma sh_unget_neg : forall f, sh_shlim_neg (sh_unget f) = sh_shlim_neg f.
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f) eqn:E; cbn; congruence. Qed.
Lemma sh_unget_N : forall f, sh_N (sh_unget f) = sh_N f.
Proof. intros f. unfold sh_N, sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.
Lemma sh_unget_wf : forall f, sh_wf f -> sh_wf (sh_unget f).
Proof.
  intros f H. unfold sh_wf in *. rewrite sh_unget_stdio, sh_unget_buf, sh_unget_neg.
  pose proof (sh_unget_rpos f). rewrite sh_unget_n. destruct (sh_stdio f); [lia|exact H].
Qed.

Lemma sh_lim0_wf : forall f, sh_wf f -> sh_wf (sh_lim0 f).
Proof. intros f H. unfold sh_wf, sh_lim0 in *. cbn. destruct (sh_stdio f); [lia|]. destruct H; auto. Qed.
Lemma sh_lim0_N : forall f, sh_N (sh_lim0 f) = sh_N f.
Proof. intros f. reflexivity. Qed.

Lemma fs_unget_loop_facts : forall n f,
  sh_N (fs_unget_loop n f) = sh_N f /\ sh_cnt0 (fs_unget_loop n f) = sh_cnt0 f
  /\ sh_stdio (fs_unget_loop n f) = sh_stdio f /\ sh_buf (fs_unget_loop n f) = sh_buf f
  /\ sh_shlim_neg (fs_unget_loop n f) = sh_shlim_neg f /\ sh_n (fs_unget_loop n f) = sh_n f
  /\ sh_rpos f - Z.of_nat n <= sh_rpos (fs_unget_loop n f) <= sh_rpos f
  /\ (sh_shlim_neg f = false -> sh_rpos (fs_unget_loop n f) = sh_rpos f - Z.of_nat n).
Proof.
  induction n as [|n IH]; intros f; cbn [fs_unget_loop].
  - repeat split; lia.
  - destruct (IH (sh_unget f)) as (N2 & C2 & S2 & B2 & G2 & n2 & R2 & E2).
    rewrite N2, C2, S2, B2, G2, n2, sh_unget_N, sh_unget_cnt0, sh_unget_stdio, sh_unget_buf, sh_unget_neg, sh_unget_n.
    pose proof (sh_unget_rpos f).
    repeat split; try lia.
    intros NG. rewrite E2 by (now rewrite sh_unget_neg). rewrite sh_unget_rpos_nonstdio by exact NG. lia.
Qed.
Lemma fs_unget_loop_wf : forall n f, sh_wf f -> sh_wf (fs_unget_loop n f).
Proof. induction n; intros f H; cbn [fs_unget_loop]; [exact H|]. apply IHn. now apply sh_unget_wf. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Loops.
  Context {A B : Type}.

  (* [comment removed for export] *)
  Fixpoint wloop (cond : A -> bool) (body : A -> A) (fuel : nat) (s : A) : option A :=
    match fuel with O => None | S fu => if cond s then wloop cond body fu (body s) else Some s end.

  Lemma wloop_total : forall cond body (I : A -> Prop) (m : A -> Z),
    (forall s, I s -> cond s = true -> I (body s) /\ 0 <= m (body s) < m s) ->
    forall fuel s, I s -> 0 <= m s < Z.of_nat fuel ->
    exists s', wloop cond body fuel s = Some s' /\ I s' /\ cond s' = false.
  Proof.
    intros cond body I m Hstep. induction fuel as [|fu IH]; intros s HI Hm; [lia|].
    cbn. destruct (cond s) eqn:C.
    - destruct (Hstep s HI C) as [HI' Hm']. apply IH; [exact HI'|lia].
    - exists s. auto.
  Qed.

  (* [comment removed for export] *)
  Fixpoint wbloop (cond : A -> bool) (body : A -> A + A) (fuel : nat) (s : A) : option A :=
    match fuel with
    | O => None
    | S fu => if cond s then match body s with inl s' => wbloop cond body fu s' | inr s' => Some s' end else Some s
    end.

  Lemma wbloop_total : forall cond body (I : A -> Prop) (Q : A -> Prop) (m : A -> Z),
    (forall s, I s -> cond s = true ->
       match body s with inl s' => I s' /\ 0 <= m s' < m s | inr s' => Q s' end) ->
    (forall s, I s -> cond s = false -> Q s) ->
    forall fuel s, I s -> 0 <= m s < Z.of_nat fuel ->
    exists s', wbloop cond body fuel s = Some s' /\ Q s'.
  Proof.
    intros cond body I Q m Hstep Hexit. induction fuel as [|fu IH]; intros s HI Hm; [lia|].
    cbn. destruct (cond s) eqn:C.
    - specialize (Hstep s HI C). destruct (body s) as [s'|s'].
      + destruct Hstep as [HI' Hm']. apply IH; [exact HI'|lia].
      + exists s'. auto.
    - exists s. split; [reflexivity| now apply Hexit].
  Qed.

  (* [comment removed for export] *)
  Fixpoint bloop (body : A -> A + B) (fuel : nat) (s : A) : option B :=
    match fuel with
    | O => None
    | S fu => match body s with inl s' => bloop body fu s' | inr r => Some r end
    end.

  Lemma bloop_total : forall body (I : A -> Prop) (Q : B -> Prop) (m : A -> Z),
    (forall s, I s -> match body s with inl s' => I s' /\ 0 <= m s' < m s | inr r => Q r end) ->
    forall fuel s, I s -> 0 <= m s < Z.of_nat fuel ->
    exists r, bloop body fuel s = Some r /\ Q r.
  Proof.
    intros body I Q m Hstep. induction fuel as [|fu IH]; intros s HI Hm; [lia|].
    cbn. specialize (Hstep s HI). destruct (body s) as [s'|r].
    - destruct Hstep as [HI' Hm']. apply IH; [exact HI'|lia].
    - exists r. auto.
  Qed.

  (* [comment removed for export] *)
  Fixpoint owloop (cond : A -> bool) (body : A -> option A) (fuel : nat) (s : A) : option A :=
    match fuel with
    | O => None
    | S fu => if cond s then match body s with Some s' => owloop cond body fu s' | None => None end else Some s
    end.

  Lemma owloop_total : forall cond body (I : A -> Prop) (m : A -> Z),
    (forall s, I s -> cond s = true -> exists s', body s = Some s' /\ I s' /\ 0 <= m s' < m s) ->
    forall fuel s, I s -> 0 <= m s < Z.of_nat fuel ->
    exists s', owloop cond body fuel s = Some s' /\ I s' /\ cond s' = false.
  Proof.
    intros cond body I m Hstep. induction fuel as [|fu IH]; intros s HI Hm; [lia|].
    cbn. destruct (cond s) eqn:C.
    - destruct (Hstep s HI C) as [s' (E & HI' & Hm')]. rewrite E. apply IH; [exact HI'|lia].
    - exists s. auto.
  Qed.

  (* [comment removed for export] *)
  Fixpoint obloop (body : A -> option (A + A)) (fuel : nat) (s : A) : option A :=
    match fuel with
    | O => None
    | S fu => match body s with Some (inl s') => obloop body fu s' | Some (inr s') => Some s' | None => None end
    end.

  Lemma obloop_total : forall body (I : A -> Prop) (Q : A -> Prop) (m : A -> Z),
    (forall s, I s -> exists r, body s = Some r /\
                 match r with inl s' => I s' /\ 0 <= m s' < m s | inr s' => Q s' end) ->
    forall fuel s, I s -> 0 <= m s < Z.of_nat fuel ->
    exists s', obloop body fuel s = Some s' /\ Q s'.
  Proof.
    intros body I Q m Hstep. induction fuel as [|fu IH]; intros s HI Hm; [lia|].
    cbn. destruct (Hstep s HI) as [r [E Hr]]. rewrite E. destruct r as [s'|s'].
    - destruct Hr as [HI' Hm']. apply IH; [exact HI'|lia].
    - exists s'. auto.
  Qed.
End Loops.

(* [comment removed for export] *)
Lemma df_lz_loop_eq : forall fuel st,
  df_lz_loop fuel st = wloop (fun st => let '(g, c, f) := st in c =? 48) df_lz_body fuel st.
Proof. induction fuel; intros [[g c] f]; cbn - [df_lz_body]; [reflexivity|]. destruct (c =? 48); auto. Qed.

Lemma df_rz_loop_eq : forall fuel st,
  df_rz_loop fuel st = wloop (fun st => let '(g, l, c, f) := st in c =? 48) df_rz_body fuel st.
Proof. induction fuel; intros [[[g l] c] f]; cbn - [df_rz_body]; [reflexivity|]. destruct (c =? 48); auto. Qed.

Lemma df_dig_loop_eq : forall fuel s, df_dig_loop fuel s = wbloop df_dig_cond df_dig_body fuel s.
Proof. induction fuel; intros s; cbn - [df_dig_cond df_dig_body]; [reflexivity|]. destruct (df_dig_cond s); [|reflexivity]. destruct (df_dig_body s); auto. Qed.

Lemma df_pad_loop_eq : forall fuel k st,
  df_pad_loop fuel k st = wloop (fun st => fst st <? 9) (df_pad_body k) fuel st.
Proof. induction fuel; intros k [j x]; cbn - [df_pad_body]; [reflexivity|]. destruct (j <? 9); auto. Qed.

Lemma df_tz_loop_eq : forall fuel x z,
  df_tz_loop fuel x z = wloop (fun z => znth x (z - 1) =? 0) df_tz_body fuel z.
Proof. induction fuel; intros x z; cbn - [df_tz_body znth]; [reflexivity|]. destruct (znth x (z - 1) =? 0); auto. Qed.

Lemma df_al_loop_eq : forall fuel p10 z s,
  df_al_loop fuel p10 z s = wloop (fun s => negb (al_k s =? z)) (df_al_body p10) fuel s.
Proof. induction fuel; intros p10 z s; cbn - [df_al_body]; [reflexivity|]. destruct (negb (al_k s =? z)); auto. Qed.

Lemma df_upk_loop_eq : forall fuel a s, df_upk_loop fuel a s = bloop (df_upk_body a) fuel s.
Proof. induction fuel; intros a s; cbn - [df_upk_body]; [reflexivity|]. destruct (df_upk_body a s); auto. Qed.

Lemma df_up_loop_eq : forall fuel s, df_up_loop fuel s = owloop df_up_cond df_up_body fuel s.
Proof. induction fuel; intros s; cbn - [df_up_cond df_up_body]; [reflexivity|]. destruct (df_up_cond s); [|reflexivity]. destruct (df_up_body s); auto. Qed.

Lemma df_dni_loop_eq : forall fuel a z x i,
  df_dni_loop fuel a z x i = wbloop (fun i => i <? LD_B1B_DIG) (df_dni_body a z x) fuel i.
Proof. induction fuel; intros a z x i; cbn - [df_dni_body LD_B1B_DIG]; [reflexivity|]. destruct (i <? LD_B1B_DIG); [|reflexivity]. destruct (df_dni_body a z x i); auto. Qed.

Lemma df_dnk_loop_eq : forall fuel z sh s,
  df_dnk_loop fuel z sh s = wloop (fun s => negb (dk_k s =? z)) (df_dnk_body z sh) fuel s.
Proof. induction fuel; intros z sh s; cbn - [df_dnk_body]; [reflexivity|]. destruct (negb (dk_k s =? z)); auto. Qed.

Lemma df_dn_loop_eq : forall fuel s, df_dn_loop fuel s = obloop df_dn_body fuel s.
Proof. induction fuel; intros s; cbn - [df_dn_body]; [reflexivity|]. destruct (df_dn_body s) as [[?|?]|]; auto. Qed.

Lemma df_asm_loop_eq : forall fuel a s,
  df_asm_loop fuel a s = wloop (fun s => as_i s <? LD_B1B_DIG) (df_asm_body a) fuel s.
Proof. induction fuel; intros a s; cbn - [df_asm_body LD_B1B_DIG]; [reflexivity|]. destruct (as_i s <? LD_B1B_DIG); auto. Qed.

Lemma scanexp_l1_loop_eq : forall fuel st, scanexp_l1_loop fuel st = wloop scanexp_l1_cond scanexp_l1_body fuel st.
Proof. induction fuel; intros st; cbn - [scanexp_l1_cond scanexp_l1_body]; [reflexivity|]. destruct (scanexp_l1_cond st); auto. Qed.
Lemma scanexp_l2_loop_eq : forall fuel st, scanexp_l2_loop fuel st = wloop scanexp_l2_cond scanexp_l2_body fuel st.
Proof. induction fuel; intros st; cbn - [scanexp_l2_cond scanexp_l2_body]; [reflexivity|]. destruct (scanexp_l2_cond st); auto. Qed.
Lemma scanexp_l3_loop_eq : forall fuel st,
  scanexp_l3_loop fuel st = wloop (fun st => isdigitc (fst st)) scanexp_l3_body fuel st.
Proof. induction fuel; intros [c f]; cbn - [scanexp_l3_body isdigitc]; [reflexivity|]. destruct (isdigitc c); auto. Qed.

Lemma fmodl_norm_loop_eq : forall fuel st,
  fmodl_norm_loop fuel st = wloop (fun st => let '(xhi, xlo, ex) := st in Z.shiftr xhi 48 =? 0) fmodl_norm_body fuel st.
Proof. induction fuel; intros [[xhi xlo] ex]; cbn - [fmodl_norm_body Z.shiftr]; [reflexivity|]. destruct (Z.shiftr xhi 48 =? 0); auto. Qed.

Lemma fmodl_sub_loop_eq : forall fuel x yhi ylo ey st,
  fmodl_sub_loop fuel x yhi ylo ey st =
  bloop (fun st => let '(xhi, xlo, ex) := st in
                   if ey <? ex then match fmodl_sub_body x yhi ylo st with inl st' => inl st' | inr r => inr (inr r) end
                   else inr (inl st)) fuel st.
Proof.
  induction fuel; intros x yhi ylo ey [[xhi xlo] ex]; cbn - [fmodl_sub_body Z.ltb]; [reflexivity|].
  destruct (ey <? ex); [|reflexivity]. destruct (fmodl_sub_body x yhi ylo (xhi, xlo, ex)); auto.
Qed.

Lemma fs_ws_loop_eq : forall fuel f,
  fs_ws_loop fuel f = bloop (fun f => let '(c, f') := sh_getc f in if m_isspace c then inl f' else inr (c, f')) fuel f.
Proof. induction fuel; intros f; cbn - [sh_getc m_isspace]; [reflexivity|]. destruct (sh_getc f) as [c f']. destruct (m_isspace c); auto. Qed.

Lemma fs_inf_loop_eq : forall fuel st, fs_inf_loop fuel st = wloop fs_inf_cond fs_inf_body fuel st.
Proof. induction fuel; intros st; cbn - [fs_inf_cond fs_inf_body]; [reflexivity|]. destruct (fs_inf_cond st); auto. Qed.
Lemma fs_nan_loop_eq : forall fuel st, fs_nan_loop fuel st = wloop fs_nan_cond fs_nan_body fuel st.
Proof. induction fuel; intros st; cbn - [fs_nan_cond fs_nan_body]; [reflexivity|]. destruct (fs_nan_cond st); auto. Qed.
Lemma fs_par_loop_eq : forall fuel st, fs_par_loop fuel st = bloop fs_par_body fuel st.
Proof. induction fuel; intros st; cbn - [fs_par_body]; [reflexivity|]. destruct (fs_par_body st); auto. Qed.

Lemma strlen_loop_eq : forall fuel s n, strlen_loop fuel s n = wloop (fun n => nz (znth s n)) (fun n => n + 1) fuel n.
Proof. induction fuel; intros s n; cbn - [nz znth]; [reflexivity|]. destruct (nz (znth s n)); auto. Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Definition V128 (hi lo : Z) : Z := hi * 2^64 + lo.

Lemma hi64_range : forall x, 0 <= hi64 x < 2^64.
Proof. intros. unfold hi64. apply wrap64_range. Qed.
Lemma lo64_range : forall x, 0 <= lo64 x < 2^64.
Proof. intros. unfold lo64. apply wrap64_range. Qed.

Lemma land48_range : forall h, 0 <= Z.land h 0x0000ffffffffffff < 2^48.
Proof.
  intros h. change 0x0000ffffffffffff with (Z.ones 48). rewrite Z.land_ones by lia.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma mant_hi_range : forall h, 2^48 <= Z.lor (Z.land h 0x0000ffffffffffff) (2^48) < 2^49.
Proof.
  intros h. pose proof (land48_range h) as R.
  assert (D : Z.land (Z.land h 0x0000ffffffffffff) (2^48) = 0).
  { rewrite <- Z.land_assoc. change (Z.land 0x0000ffffffffffff (2^48)) with 0. apply Z.land_0_r. }
  rewrite <- Z.lxor_lor by exact D. rewrite <- Z.add_nocarry_lxor by exact D. lia.
Qed.

Lemma mod_mul_add : forall q r M, 0 < M -> 0 <= r < M -> (q * M + r) mod (M * M) = (q mod M) * M + r.
Proof.
  intros q r M HM Hr.
  rewrite (Z.div_mod q M) at 1 by lia.
  replace ((M * (q / M) + q mod M) * M + r) with ((q mod M) * M + r + (q / M) * (M * M)) by ring.
  rewrite Z.mod_add by lia. apply Z.mod_small.
  pose proof (Z.mod_pos_bound q M HM). nia.
Qed.

(* [comment removed for export] *)
Lemma sub128_spec : forall xhi xlo yhi ylo,
  0 <= xlo < 2^64 -> 0 <= ylo < 2^64 ->
  let hi := u64 (xhi - yhi) in
  let lo := u64 (xlo - ylo) in
  let hi' := if xlo <? ylo then u64 (hi - 1) else hi in
  V128 hi' lo = (V128 xhi xlo - V128 yhi ylo) mod 2^128 /\ 0 <= hi' < 2^64 /\ 0 <= lo < 2^64.
Proof.
  intros xhi xlo yhi ylo Hx Hy. cbv zeta. unfold u64, V128.
  set (b := if xlo <? ylo then 1 else 0).
  assert (Hlo : (xlo - ylo) mod 2^64 = xlo - ylo + b * 2^64).
  { unfold b. destruct (Z.ltb_spec xlo ylo).
    - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia.
    - rewrite Z.mod_small; lia. }
  assert (Hhi : (if xlo <? ylo then ((xhi - yhi) mod 2 ^ 64 - 1) mod 2 ^ 64 else (xhi - yhi) mod 2 ^ 64)
                = (xhi - yhi - b) mod 2^64).
  { unfold b. destruct (xlo <? ylo).
    - apply Zminus_mod_idemp_l.
    - f_equal. lia. }
  rewrite Hhi.
  split; [| split; apply Z.mod_pos_bound; lia].
  rewrite Hlo.
  replace (xhi * 2 ^ 64 + xlo - (yhi * 2 ^ 64 + ylo)) with ((xhi - yhi - b) * 2^64 + (xlo - ylo + b * 2^64)) by ring.
  change (2^128) with (2^64 * 2^64).
  rewrite mod_mul_add; [reflexivity|lia|].
  unfold b. destruct (Z.ltb_spec xlo ylo); lia.
Qed.

Lemma shr63_is0 : forall h, 0 <= h < 2^63 -> Z.shiftr h 63 = 0.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
Lemma shr63_pos : forall h, 2^63 <= h -> Z.shiftr h 63 <> 0.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. intros E. apply Z.div_small_iff in E; lia. Qed.
Lemma shr63_bit : forall lo, 0 <= lo < 2^64 -> Z.shiftr lo 63 = lo / 2^63 /\ 0 <= lo / 2^63 <= 1.
Proof.
  intros lo H. rewrite Z.shiftr_div_pow2 by lia. split; [reflexivity|].
  split; [apply Z.div_pos; lia|].
  assert (lo / 2^63 < 2) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* [comment removed for export] *)
Lemma dbl128 : forall hi lo, 0 <= hi < 2^62 -> 0 <= lo < 2^64 ->
  V128 (u64 (2 * hi + Z.shiftr lo 63)) (u64 (2 * lo)) = 2 * V128 hi lo
  /\ u64 (2 * hi + Z.shiftr lo 63) = 2 * hi + lo / 2^63 /\ 0 <= u64 (2 * lo) < 2^64.
Proof.
  intros hi lo Hh Hl. destruct (shr63_bit lo Hl) as [-> Hb].
  unfold u64, V128.
  rewrite (Z.mod_small (2 * hi + lo / 2^63)) by lia.
  split; [|split; [reflexivity| apply Z.mod_pos_bound; lia]].
  rewrite (Z.mod_eq (2 * lo) (2^64)) by lia.
  replace (2 * lo / 2^64) with (lo / 2^63); [ring|].
  change (2^64) with (2 * 2^63). rewrite Z.div_mul_cancel_l by lia. reflexivity.
Qed.

Section FmodlLoops.
  Variables (x yhi ylo : Z).
  Let Y := V128 yhi ylo.
  Hypothesis Hyhi : 2^48 <= yhi < 2^49.
  Hypothesis Hylo : 0 <= ylo < 2^64.

  Definition Isub (st : Z * Z * Z) : Prop :=
    let '(xhi, xlo, ex) := st in 0 <= xlo < 2^64 /\ 0 <= xhi /\ 0 < V128 xhi xlo < 2 * Y.

  Lemma Y_range : 2^112 <= Y < 2^113.
  Proof. unfold Y, V128. lia. Qed.

  Lemma lor_eq0 : forall a b, 0 <= a -> 0 <= b -> (Z.lor a b =? 0) = ((a =? 0) && (b =? 0)).
  Proof.
    intros a b Ha Hb. destruct (Z.eqb_spec (Z.lor a b) 0) as [E|E].
    - apply Z.lor_eq_0_iff in E. destruct E; subst; reflexivity.
    - symmetry. apply andb_false_iff. destruct (Z.eqb_spec a 0); [|now left]. destruct (Z.eqb_spec b 0); [|now right].
      subst. exfalso. apply E. reflexivity.
  Qed.

  Lemma fmodl_sub_body_spec : forall xhi xlo ex, Isub (xhi, xlo, ex) ->
    match fmodl_sub_body x yhi ylo (xhi, xlo, ex) with
    | inl (xhi', xlo', ex') => Isub (xhi', xlo', ex') /\ ex' = ex - 1
    | inr _ => True
    end.
  Proof.
    intros xhi xlo ex (Hxlo & Hxhi & HX). pose proof Y_range as HY.
    assert (Hxhi2 : xhi < 2^50) by (unfold V128 in HX; nia).
    unfold fmodl_sub_body.
    pose proof (sub128_spec xhi xlo yhi ylo Hxlo Hylo) as S. cbv zeta in S.
    set (hi := u64 (xhi - yhi)) in *. set (lo := u64 (xlo - ylo)) in *.
    set (hi' := if xlo <? ylo then u64 (hi - 1) else hi) in *.
    destruct S as (SV & Shi & Slo). fold Y in SV. change (V128 xhi xlo) with (V128 xhi xlo) in SV.
    set (X := V128 xhi xlo) in *.
    destruct (Z.lt_ge_cases X Y) as [LT|GE].
    - (* [comment removed for export] *)
      assert (HV : V128 hi' lo = X - Y + 2^128).
      { rewrite SV. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia. }
      assert (Hhi' : 2^63 <= hi') by (unfold V128 in HV; nia).
      destruct (Z.eqb_spec (Z.shiftr hi' 63) 0) as [E|E]. { exfalso. apply (shr63_pos hi' Hhi'). exact E. }
      destruct (dbl128 xhi xlo ltac:(lia) Hxlo) as (DV & Dhi & Dlo).
      split; [|reflexivity]. unfold Isub. rewrite Dhi. split; [exact Dlo|]. split; [pose proof (shr63_bit xlo Hxlo); lia|].
      rewrite <- Dhi. rewrite DV. subst X. lia.
    - (* [comment removed for export] *)
      assert (HV : V128 hi' lo = X - Y). { rewrite SV. apply Z.mod_small. lia. }
      assert (Hhi' : hi' < 2^49) by (unfold V128 in HV; nia).
      rewrite (shr63_is0 hi') by lia. cbn [Z.eqb].
      rewrite lor_eq0 by lia.
      destruct (Z.eqb_spec hi' 0) as [E1|E1]; destruct (Z.eqb_spec lo 0) as [E2|E2]; cbn [andb]; [exact I| | |].
      all: destruct (dbl128 hi' lo ltac:(lia) ltac:(lia)) as (DV & Dhi & Dlo).
      all: split; [|reflexivity]; unfold Isub; rewrite Dhi; split; [exact Dlo|]; split; [pose proof (shr63_bit lo ltac:(lia)); lia|].
      all: rewrite <- Dhi, DV, HV; unfold V128 in HV |- *; subst X; nia.
  Qed.
End FmodlLoops.

Lemma fmodl_sub_loop_total : forall x yhi ylo ey xhi xlo ex,
  2^48 <= yhi < 2^49 -> 0 <= ylo < 2^64 ->
  Isub yhi ylo (xhi, xlo, ex) ->
  exists r, fmodl_sub_loop (S (Z.to_nat (ex - ey))) x yhi ylo ey (xhi, xlo, ex) = Some r /\
            match r with inl st' => Isub yhi ylo st' | inr _ => True end.
Proof.
  intros x yhi ylo ey xhi xlo ex Hyhi Hylo HI.
  rewrite fmodl_sub_loop_eq.
  apply (bloop_total _ (Isub yhi ylo) _ (fun st => let '(xhi, xlo, ex) := st in Z.max 0 (ex - ey))).
  - intros [[h l] e] HIs. destruct (Z.ltb_spec ey e).
    + pose proof (fmodl_sub_body_spec x yhi ylo Hyhi Hylo h l e HIs) as B.
      destruct (fmodl_sub_body x yhi ylo (h, l, e)) as [[[h' l'] e']|r]; [|exact I].
      destruct B as [B1 B2]. split; [exact B1|]. lia.
    + exact HIs.
  - exact HI.
  - rewrite Nat2Z.inj_succ, ZifyInst.of_nat_to_nat_eq. lia.
Qed.

Definition Inorm (st : Z * Z * Z) : Prop :=
  let '(xhi, xlo, ex) := st in 0 <= xlo < 2^64 /\ 0 <= xhi /\ 0 < V128 xhi xlo < 2^113.

Lemma fmodl_norm_loop_total : forall st, Inorm st ->
  exists st', fmodl_norm_loop 130%nat st = Some st' /\ Inorm st'.
Proof.
  intros st HI. rewrite fmodl_norm_loop_eq.
  destruct (wloop_total (fun st : Z * Z * Z => let '(xhi, _, _) := st in Z.shiftr xhi 48 =? 0) fmodl_norm_body Inorm
             (fun st => let '(xhi, xlo, ex) := st in 112 - Z.log2 (V128 xhi xlo))) with (fuel := 130%nat) (s := st)
    as [st' (E & HI' & _)].
  - intros [[h l] e] (Hl & Hh & HV) C.
    destruct (Z.eqb_spec (Z.shiftr h 48) 0) as [E|E]; [|discriminate C].
    rewrite Z.shiftr_div_pow2 in E by lia. apply Z.div_small_iff in E; [|lia]. destruct E as [E|E]; [|lia].
    assert (HV2 : V128 h l < 2^112) by (unfold V128 in *; nia).
    unfold fmodl_norm_body. destruct (dbl128 h l ltac:(lia) Hl) as (DV & Dhi & Dlo).
    unfold Inorm. rewrite !DV, Dhi.
    pose proof (shr63_bit l Hl).
    assert (HL : Z.log2 (V128 h l) < 112). { apply Z.log2_lt_pow2; lia. }
    rewrite Z.log2_double by lia. pose proof (Z.log2_nonneg (V128 h l)).
    repeat split; try lia.
  - exact HI.
  - destruct st as [[h l] e]. destruct HI as (Hl & Hh & HV).
    assert (Z.log2 (V128 h l) < 113) by (apply Z.log2_lt_pow2; lia). pose proof (Z.log2_nonneg (V128 h l)).
    change (Z.of_nat 130) with 130. lia.
  - exists st'. auto.
Qed.

Definition fmodl_tail (x yhi ylo xhi xlo ex ey sx : Z) : option Z :=
  match fmodl_sub_loop (S (Z.to_nat (ex - ey))) x yhi ylo ey (xhi, xlo, ex) with
  | None => None
  | Some (inr r) => Some r
  | Some (inl (xhi, xlo, ex)) =>
    let hi := u64 (xhi - yhi) in
    let lo := u64 (xlo - ylo) in
    let hi := if xlo <? ylo then u64 (hi - 1) else hi in
    let r :=
      if Z.shiftr hi 63 =? 0 then
        if Z.lor hi lo =? 0 then
          inr (let t := f128_of_i32 0 in f128_mul t x)
        else inl (hi, lo)
      else inl (xhi, xlo) in
    match r with
    | inr v => Some v
    | inl (xhi, xlo) =>
      match fmodl_norm_loop 130%nat (xhi, xlo, ex) with
      | None => None
      | Some (xhi, xlo, ex) =>
        if ex <=? 0 then
          let ux := mk128 (Z.lor (Z.land xhi 0x0000ffffffffffff) (Z.shiftl (Z.land (Z.lor (ex + 120) sx) 0xffff) 48)) xlo in
          Some (f128_mul ux C_2PM120)
        else
          Some (mk128 (Z.lor (Z.land xhi 0x0000ffffffffffff) (Z.shiftl (Z.land (Z.lor ex sx) 0xffff) 48)) xlo)
      end
    end
  end.

Lemma fmodl_tail_total : forall x UX UY ex ey sx,
  fmodl_tail x (Z.lor (Z.land (hi64 UY) 0x0000ffffffffffff) (2^48)) (lo64 UY)
               (Z.lor (Z.land (hi64 UX) 0x0000ffffffffffff) (2^48)) (lo64 UX) ex ey sx <> None.
Proof.
  intros x UX UY ex ey sx. unfold fmodl_tail.
  set (yhi := Z.lor (Z.land (hi64 UY) 0x0000ffffffffffff) (2^48)).
  set (xhi := Z.lor (Z.land (hi64 UX) 0x0000ffffffffffff) (2^48)).
  pose proof (mant_hi_range (hi64 UY)) as HY. pose proof (mant_hi_range (hi64 UX)) as HX.
  fold yhi in HY. fold xhi in HX.
  pose proof (lo64_range UY) as HYL. pose proof (lo64_range UX) as HXL.
  assert (HI : Isub yhi (lo64 UY) (xhi, lo64 UX, ex)).
  { unfold Isub, V128. nia. }
  destruct (fmodl_sub_loop_total x yhi (lo64 UY) ey xhi (lo64 UX) ex HY HYL HI) as [r [-> Hr]].
  destruct r as [[[h l] e]|r]; [|discriminate].
  destruct Hr as (Hl & Hh & HV).
  pose proof (sub128_spec h l yhi (lo64 UY) Hl HYL) as S. cbv zeta in S.
  cbv zeta.
  set (hi := u64 (h - yhi)) in *. set (lo := u64 (l - lo64 UY)) in *.
  set (hi' := if l <? lo64 UY then u64 (hi - 1) else hi) in *.
  destruct S as (SV & Shi & Slo).
  assert (Hh2 : h < 2^50) by (unfold V128 in HV; nia).
  destruct (Z.lt_ge_cases (V128 h l) (V128 yhi (lo64 UY))) as [LT|GE].
  - assert (HV' : V128 hi' lo = V128 h l - V128 yhi (lo64 UY) + 2^128).
    { rewrite SV. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; [lia|]. unfold V128 in *. nia. }
    assert (Hhi' : 2^63 <= hi') by (unfold V128 in HV', LT, HV; nia).
    destruct (Z.eqb_spec (Z.shiftr hi' 63) 0) as [E|E]. { exfalso. exact (shr63_pos hi' Hhi' E). }
    destruct (fmodl_norm_loop_total (h, l, e)) as [[[h2 l2] e2] [-> _]].
    { unfold Inorm. unfold V128 in *. repeat split; try lia; nia. }
    destruct (e2 <=? 0); discriminate.
  - assert (HV' : V128 hi' lo = V128 h l - V128 yhi (lo64 UY)).
    { rewrite SV. apply Z.mod_small. unfold V128 in *. nia. }
    assert (Hhi' : hi' < 2^49) by (unfold V128 in HV', GE, HV; nia).
    rewrite (shr63_is0 hi') by lia. cbn [Z.eqb].
    rewrite lor_eq0 by lia.
    destruct (Z.eqb_spec hi' 0) as [E1|E1]; destruct (Z.eqb_spec lo 0) as [E2|E2]; cbn [andb]; [discriminate| | |].
    all: destruct (fmodl_norm_loop_total (hi', lo, e)) as [[[h2 l2] e2] [-> _]];
      [unfold Inorm; unfold V128 in *; repeat split; try lia; nia|].
    all: destruct (e2 <=? 0); discriminate.
Qed.

Lemma m_fmodl_total : forall x y, m_fmodl x y <> None.
Proof.
  intros x y. unfold m_fmodl.
  destruct (_ || _ || _). { discriminate. }
  cbv zeta.
  destruct (f128_le _ _ <=? 0). { destruct (f128_le _ _ =? 0); discriminate. }
  destruct (Z.land (Z.shiftr (hi64 x) 48) 32767 =? 0), (Z.land (Z.shiftr (hi64 y) 48) 32767 =? 0); cbn iota;
  match goal with |- context [fmodl_sub_loop (S (Z.to_nat (?ex - ?ey))) ?xx (Z.lor (Z.land (hi64 ?UY) _) _) _ ?ey (Z.lor (Z.land (hi64 ?UX) _) _, _, ?ex)] =>
         exact (fmodl_tail_total x UX UY ex ey _) end.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma sh_getc_facts : forall f c f', sh_getc f = (c, f') -> sh_wf f ->
  sh_wf f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f /\ sh_cnt0 f' = sh_cnt0 f /\ sh_N f' = sh_N f
  /\ sh_n f' = sh_n f
  /\ (sh_rpos f <= sh_rpos f' <= sh_rpos f + 1)
  /\ (contc c -> sh_rpos f' = sh_rpos f + 1 /\ sh_rpos f < sh_N f)
  /\ ((c = -1 /\ sh_rpos f' = sh_rpos f /\ sh_shlim_neg f' = true /\ sh_stdio f = true)
      \/ (c = znth (sh_buf f) (sh_rpos f) /\ sh_rpos f' = sh_rpos f + 1 /\ sh_shlim_neg f' = sh_shlim_neg f)).
Proof.
  intros f c f' G W.
  assert (Ef : f' = snd (sh_getc f)) by (rewrite G; reflexivity).
  assert (Ec : c = fst (sh_getc f)) by (rewrite G; reflexivity).
  split. { subst f'. apply sh_getc_wf. exact W. }
  split. { subst f'. apply sh_getc_buf. }
  split. { subst f'. apply sh_getc_stdio. }
  split. { subst f'. apply sh_getc_cnt0. }
  split. { subst f'. apply sh_getc_N. }
  split. { subst f'. apply sh_getc_n. }
  split. { subst f'. apply sh_getc_rpos. }
  split. { subst f' c. apply sh_getc_cont. exact W. }
  subst f' c. unfold sh_getc. destruct (sh_stdio f) eqn:ST; cbn [negb].
  - destruct (Z.eqb_spec (sh_rpos f) (sh_n f)); cbn; [left|right]; repeat split; auto.
  - cbn. right. repeat split; auto.
Qed.

Lemma sh_unget_shape : forall f,
  (sh_shlim_neg f = true /\ sh_unget f = f) \/
  (sh_shlim_neg f = false /\ sh_rpos (sh_unget f) = sh_rpos f - 1 /\ sh_shlim_neg (sh_unget f) = false).
Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f) eqn:E; cbn; [left|right]; repeat split; auto. Qed.

Lemma sh_N_le : forall f, sh_wf f -> sh_N f <= zlength (sh_buf f) - 1.
Proof. intros f W. unfold sh_wf, sh_N in *. destruct (sh_stdio f); lia. Qed.

(* [comment removed for export] *)
Lemma read_char_cases : forall l i, znth (l ++ [0]) i = 0 \/ In (znth (l ++ [0]) i) l.
Proof. intros l i. destruct (znth_snoc0 l i) as [E|[_ I]]; auto. Qed.

Definition contb (c : Z) : bool := negb (c =? 0) && negb (c =? -1).
Lemma contb_spec : forall c, contb c = true <-> contc c.
Proof. intros c. unfold contb, contc. rewrite andb_true_iff, !negb_true_iff, !Z.eqb_neq. tauto. Qed.

(* [comment removed for export] *)
Definition cm (c : Z) (f : shfile) : Z := Z.max 0 (sh_N f - sh_rpos f + 1) + (if contb c then 1 else 0).

Lemma cm_nonneg : forall c f, 0 <= cm c f.
Proof. intros. unfold cm. destruct (contb c); lia. Qed.

(* [comment removed for export] *)
Lemma cm_read : forall f c f', sh_wf f -> sh_getc f = (c, f') -> sh_rpos f <= sh_N f ->
  cm c f' < Z.max 0 (sh_N f - sh_rpos f + 1) + 1 /\ (contc c -> sh_rpos f' <= sh_N f').
Proof.
  intros f c f' W G R. destruct (sh_getc_facts f c f' G W) as (W' & B & S & C0 & N & n & RP & CT & CH).
  unfold cm. rewrite N. destruct (contb c) eqn:CB.
  - apply contb_spec in CB. destruct (CT CB) as [E L]. split; [lia|]. intros _. lia.
  - split; [lia|]. intros CC. apply contb_spec in CC. congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma isdigitc_cont : forall c, isdigitc c = true -> contc c.
Proof.
  intros c H. unfold isdigitc in H. apply Z.ltb_lt in H. unfold u32 in H. unfold contc.
  split; intros ->; cbv in H; discriminate.
Qed.

(* [comment removed for export] *)
Definition SXI (st : Z * Z * shfile) : Prop :=
  let '(v, c, f) := st in sh_wf f /\ (contc c -> sh_rpos f <= sh_N f).

Lemma scanexp_l12_total : forall (cond : Z * Z * shfile -> bool),
  (forall v c f, cond (v, c, f) = true -> isdigitc c = true) ->
  forall fuel v c f r0,
  SXI (v, c, f) -> r0 <= sh_rpos f -> cm c f < Z.of_nat fuel ->
  exists v' c' f', wloop cond scanexp_l1_body fuel (v, c, f) = Some (v', c', f') /\ SXI (v', c', f')
    /\ r0 <= sh_rpos f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f /\ sh_cnt0 f' = sh_cnt0 f /\ sh_N f' = sh_N f /\ sh_n f' = sh_n f
    /\ cm c' f' <= cm c f /\ cond (v', c', f') = false.
Proof.
  intros cond Hcond fuel v c f r0 HI Hr Hm.
  destruct (wloop_total cond scanexp_l1_body
     (fun st => SXI st /\ let '(v', c', f') := st in r0 <= sh_rpos f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f /\ sh_cnt0 f' = sh_cnt0 f /\ sh_N f' = sh_N f /\ sh_n f' = sh_n f /\ cm c' f' <= cm c f)
     (fun st => let '(v', c', f') := st in cm c' f')) with (fuel := fuel) (s := (v, c, f)) as [[[v' c'] f'] (E & (HI' & Q) & C)].
  - intros [[v1 c1] f1] [[W1 C1] (R1 & B1 & S1 & Cn1 & N1 & n1 & M1)] CND.
    pose proof (isdigitc_cont c1 (Hcond _ _ _ CND)) as CC1. specialize (C1 CC1).
    unfold scanexp_l1_body. destruct (sh_getc f1) as [c2 f2] eqn:G.
    destruct (sh_getc_facts f1 c2 f2 G W1) as (W2 & B2 & S2 & C02 & N2 & n2 & RP2 & CT2 & _).
    destruct (cm_read f1 c2 f2 W1 G C1) as [M2 CI2].
    assert (cm c1 f1 = Z.max 0 (sh_N f1 - sh_rpos f1 + 1) + 1) as EQ.
    { unfold cm. replace (contb c1) with true; [reflexivity|]. symmetry. apply contb_spec. exact CC1. }
    unfold SXI. repeat split; try assumption; try lia; try congruence. apply cm_nonneg.
  - repeat split; try (destruct HI; assumption); try lia.
  - split; [apply cm_nonneg| exact Hm].
  - exists v', c', f'. split; [exact E|]. split; [exact HI'|]. split; [|split; [|split; [|split; [|split; [|split;[|split]]]]]]; try tauto.
Qed.

Lemma scanexp_l1_condD : forall v c f, scanexp_l1_cond (v, c, f) = true -> isdigitc c = true.
Proof. intros v c f H. unfold scanexp_l1_cond in H. apply andb_prop in H. tauto. Qed.
Lemma scanexp_l2_condD : forall v c f, scanexp_l2_cond (v, c, f) = true -> isdigitc c = true.
Proof. intros v c f H. unfold scanexp_l2_cond in H. apply andb_prop in H. tauto. Qed.

Lemma scanexp_l3_total : forall fuel c f r0,
  SXI (0, c, f) -> r0 <= sh_rpos f -> cm c f < Z.of_nat fuel ->
  exists c' f', scanexp_l3_loop fuel (c, f) = Some (c', f') /\ SXI (0, c', f')
    /\ r0 <= sh_rpos f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f /\ sh_cnt0 f' = sh_cnt0 f /\ sh_N f' = sh_N f /\ sh_n f' = sh_n f
    /\ isdigitc c' = false.
Proof.
  intros fuel c f r0 HI Hr Hm. rewrite scanexp_l3_loop_eq.
  destruct (wloop_total (fun st : Z * shfile => isdigitc (fst st)) scanexp_l3_body
     (fun st => let '(c', f') := st in SXI (0, c', f') /\ r0 <= sh_rpos f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f /\ sh_cnt0 f' = sh_cnt0 f /\ sh_N f' = sh_N f /\ sh_n f' = sh_n f)
     (fun st => let '(c', f') := st in cm c' f')) with (fuel := fuel) (s := (c, f)) as [[c' f'] (E & (HI' & Q) & C)].
  - intros [c1 f1] [[W1 C1] (R1 & B1 & S1 & Cn1 & N1 & n1)] CND. cbn [fst] in CND.
    pose proof (isdigitc_cont c1 CND) as CC1. specialize (C1 CC1).
    unfold scanexp_l3_body. destruct (sh_getc f1) as [c2 f2] eqn:G.
    destruct (sh_getc_facts f1 c2 f2 G W1) as (W2 & B2 & S2 & C02 & N2 & n2 & RP2 & CT2 & _).
    destruct (cm_read f1 c2 f2 W1 G C1) as [M2 CI2].
    assert (cm c1 f1 = Z.max 0 (sh_N f1 - sh_rpos f1 + 1) + 1) as EQ.
    { unfold cm. replace (contb c1) with true; [reflexivity|]. symmetry. apply contb_spec. exact CC1. }
    unfold SXI. repeat split; try assumption; try lia; try congruence. apply cm_nonneg.
  - repeat split; try (destruct HI; assumption); try lia.
  - split; [apply cm_nonneg| exact Hm].
  - exists c', f'. split; [exact E|]. cbn [fst] in C. tauto.
Qed.

Definition sh_same (f f' : shfile) : Prop :=
  sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f /\ sh_cnt0 f' = sh_cnt0 f /\ sh_N f' = sh_N f /\ sh_n f' = sh_n f.

Lemma sh_same_refl : forall f, sh_same f f.
Proof. intros. unfold sh_same. tauto. Qed.
Lemma sh_same_trans : forall f1 f2 f3, sh_same f1 f2 -> sh_same f2 f3 -> sh_same f1 f3.
Proof. unfold sh_same. intros f1 f2 f3 (A1&A2&A3&A4&A5) (B1&B2&B3&B4&B5). repeat split; congruence. Qed.
Lemma sh_same_getc : forall f c f', sh_getc f = (c, f') -> sh_wf f -> sh_same f f'.
Proof. intros f c f' G W. destruct (sh_getc_facts f c f' G W) as (_ & B & S & C & N & n & _). unfold sh_same. auto. Qed.
Lemma sh_same_unget : forall f, sh_same f (sh_unget f).
Proof. intros f. unfold sh_same. rewrite sh_unget_buf, sh_unget_stdio, sh_unget_cnt0, sh_unget_N, sh_unget_n. tauto. Qed.

Lemma sh_unget_facts : forall f, sh_wf f ->
  sh_wf (sh_unget f) /\ sh_same f (sh_unget f) /\ sh_rpos f - 1 <= sh_rpos (sh_unget f) <= sh_rpos f.
Proof. intros f W. split; [now apply sh_unget_wf|]. split; [apply sh_same_unget| apply sh_unget_rpos]. Qed.

(* [comment removed for export] *)
Definition scanexp_tail (fuelc : nat) (neg c : Z) (f : shfile) : option (shfile * Z) :=
  if negb (isdigitc c) then
    let f := sh_unget f in Some (f, LLONG_MIN_)
  else
  match scanexp_l1_loop fuelc (0, c, f) with
  | None => None
  | Some (x, c, f) =>
  match scanexp_l2_loop fuelc (x, c, f) with
  | None => None
  | Some (y, c, f) =>
  match scanexp_l3_loop fuelc (c, f) with
  | None => None
  | Some (c, f) =>
    let f := sh_unget f in
    Some (f, if nz neg then - y else y)
  end end end.

Lemma scanexp_eq : forall fuelc f pok,
  scanexp fuelc f pok =
    let '(c, f) := sh_getc f in
    let '(neg, c, f) :=
      if (c =? 43) || (c =? 45) then
        let neg := b2z (c =? 45) in
        let '(c, f) := sh_getc f in
        let f := if negb (isdigitc c) && nz pok then sh_unget f else f in
        (neg, c, f)
      else (0, c, f) in
    scanexp_tail fuelc neg c f.
Proof. intros. reflexivity. Qed.

Lemma scanexp_tail_total : forall fuelc neg c f,
  sh_wf f -> (contc c -> sh_rpos f <= sh_N f) -> cm c f < Z.of_nat fuelc ->
  exists f' e, scanexp_tail fuelc neg c f = Some (f', e) /\ sh_wf f' /\ sh_same f f'
    /\ (sh_stdio f = false -> sh_rpos f - 1 <= sh_rpos f').
Proof.
  intros fuelc neg c f W CI M. unfold scanexp_tail.
  destruct (isdigitc c) eqn:D; cbn [negb].
  2:{ destruct (sh_unget_facts f W) as (W' & SM & R). eexists _, _. split; [reflexivity|]. split; [exact W'|]. split; [exact SM|]. intros; lia. }
  pose proof (sh_unget_rpos f) as UR.
  destruct (scanexp_l12_total scanexp_l1_cond scanexp_l1_condD fuelc 0 c f (sh_rpos f)) as [v3 [c3 [f3 (E3 & HI3 & R3 & B3 & S3 & C03 & N3 & n3 & M3 & _)]]].
  { split; [exact W| exact CI]. } { lia. } { exact M. }
  rewrite <- scanexp_l1_loop_eq in E3. rewrite E3.
  destruct (scanexp_l12_total scanexp_l2_cond scanexp_l2_condD fuelc v3 c3 f3 (sh_rpos f)) as [v4 [c4 [f4 (E4 & HI4 & R4 & B4 & S4 & C04 & N4 & n4 & M4 & _)]]].
  { exact HI3. } { lia. } { lia. }
  change scanexp_l1_body with scanexp_l2_body in E4. rewrite <- scanexp_l2_loop_eq in E4. rewrite E4.
  destruct (scanexp_l3_total fuelc c4 f4 (sh_rpos f)) as [c5 [f5 (E5 & HI5 & R5 & B5 & S5 & C05 & N5 & n5 & _)]].
  { destruct HI4 as [W4 CI4]. split; [exact W4| exact CI4]. } { lia. } { lia. }
  rewrite E5. destruct HI5 as [W5 _].
  destruct (sh_unget_facts f5 W5) as (W6 & SM6 & R6).
  eexists _, _. split; [reflexivity|]. split; [exact W6|]. split.
  - eapply sh_same_trans; [|exact SM6]. unfold sh_same. repeat split; congruence.
  - intros; lia.
Qed.

Lemma scanexp_total : forall fuelc f pok,
  sh_wf f -> 0 <= sh_rpos f <= sh_N f -> zlength (sh_buf f) + 2 <= Z.of_nat fuelc ->
  exists f' e, scanexp fuelc f pok = Some (f', e) /\ sh_wf f' /\ sh_same f f'
    /\ (sh_stdio f = false -> sh_rpos f <= sh_rpos f').
Proof.
  intros fuelc f pok W R FU.
  pose proof (sh_N_le f W) as NL.
  rewrite scanexp_eq.
  destruct (sh_getc f) as [c1 f1] eqn:G1.
  destruct (sh_getc_facts f c1 f1 G1 W) as (W1 & B1 & S1 & C1 & N1 & n1 & RP1 & CT1 & SH1).
  pose proof (sh_same_getc f c1 f1 G1 W) as SM1.
  destruct (cm_read f c1 f1 W G1 ltac:(lia)) as [M1 CI1].
  assert (UG : forall g, sh_wf g -> sh_stdio g = false -> sh_rpos (sh_unget g) = sh_rpos g - 1).
  { intros g Wg Sg. apply sh_unget_rpos_nonstdio. unfold sh_wf in Wg. rewrite Sg in Wg. tauto. }
  destruct ((c1 =? 43) || (c1 =? 45)) eqn:SG.
  - assert (CC1 : contc c1). { unfold contc. destruct (Z.eqb_spec c1 43); [subst; split; lia|]. destruct (Z.eqb_spec c1 45); [subst; split; lia| discriminate SG]. }
    destruct (CT1 CC1) as [E1 L1].
    destruct (sh_getc f1) as [c2 f2] eqn:G2.
    destruct (sh_getc_facts f1 c2 f2 G2 W1) as (W2 & B2 & S2 & C2 & N2 & n2 & RP2 & CT2 & SH2).
    destruct (cm_read f1 c2 f2 W1 G2 ltac:(lia)) as [M2 CI2].
    pose proof (sh_same_getc f1 c2 f2 G2 W1) as SM2.
    cbv zeta. destruct (negb (isdigitc c2) && nz pok) eqn:NP.
    + destruct (sh_unget_facts f2 W2) as (W3 & SM3 & R3).
      destruct (scanexp_tail_total fuelc (b2z (c1 =? 45)) c2 (sh_unget f2)) as [f' [e (E & W' & SM' & R')]].
      { exact W3. } { rewrite sh_unget_N. intros CC. specialize (CI2 CC). lia. }
      { unfold cm in *. rewrite sh_unget_N, N2, N1 in *. destruct (contb c2); lia. }
      rewrite E. eexists _, _. split; [reflexivity|]. split; [exact W'|]. split.
      * eapply sh_same_trans; [exact SM1|]. eapply sh_same_trans; [exact SM2|]. eapply sh_same_trans; [exact SM3| exact SM'].
      * intros ST. rewrite sh_unget_stdio in R'. specialize (R' ltac:(congruence)).
        rewrite (UG f2 W2 ltac:(congruence)) in R'.
        destruct SH2 as [(? & ? & ? & ?)|( ? & E2 & ?)]; [congruence| lia].
    + destruct (scanexp_tail_total fuelc (b2z (c1 =? 45)) c2 f2) as [f' [e (E & W' & SM' & R')]].
      { exact W2. } { exact CI2. } { unfold cm in *. rewrite N2, N1 in *. destruct (contb c2); lia. }
      rewrite E. eexists _, _. split; [reflexivity|]. split; [exact W'|]. split.
      * eapply sh_same_trans; [exact SM1|]. eapply sh_same_trans; [exact SM2| exact SM'].
      * intros ST. specialize (R' ltac:(congruence)).
        destruct SH2 as [(? & ? & ? & ?)|( ? & E2 & ?)]; [congruence| lia].
  - destruct (scanexp_tail_total fuelc 0 c1 f1) as [f' [e (E & W' & SM' & R')]].
    { exact W1. } { exact CI1. } { unfold cm in *. rewrite N1 in *. destruct (contb c1); lia. }
    rewrite E. eexists _, _. split; [reflexivity|]. split; [exact W'|]. split.
    + eapply sh_same_trans; [exact SM1| exact SM'].
    + intros ST. specialize (R' ltac:(congruence)).
      destruct SH1 as [(? & ? & ? & ?)|( ? & E2 & ?)]; [congruence| lia].
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition df_p4 (f : shfile) (a z e2 rp : Z) (x : list Z) (bits emin sign emax frac bias : Z) : option (shfile * Z) :=
  (* [comment removed for export] *)
  match df_tz_loop FUEL_RING x z with
  | None => None
  | Some z =>
  (* [comment removed for export] *)
  match (if nz (Z.rem rp 9) then
           let rpm9 := if 0 <=? rp then Z.rem rp 9 else Z.rem rp 9 + 9 in
           let p10 := znth p10s (8 - rpm9) in
           match df_al_loop FUEL_RING p10 z (mkAL a a rp 0 x) with
           | None => None
           | Some (mkAL _ a rp carry x) =>
             let '(z, x) := if nz carry then (z + 1, zupd x z carry) else (z, x) in
             Some (a, z, rp + (9 - rpm9), x)
           end
         else Some (a, z, rp, x)) with
  | None => None
  | Some (a, z, rp, x) =>
  (* [comment removed for export] *)
  match df_up_loop FUEL_SCALE (mkUS rp a z e2 x) with
  | None => None
  | Some (mkUS rp a z e2 x) =>
  (* [comment removed for export] *)
  match df_dn_loop FUEL_SCALE (mkDS rp a z e2 x 0) with
  | None => None
  | Some (mkDS rp a z e2 x i) =>
  match df_final a z x e2 bits emin sign emax frac bias with
  | None => None
  | Some y => Some (f, y)
  end end end end end.

Definition df_p3 (f : shfile) (k lrp lnz : Z) (x : list Z) (bits emin sign emax frac bias : Z) : option (shfile * Z) :=
  let a := 0 in
  let z := k in
  let e2 := 0 in
  let rp := s32 lrp in                                      (* [comment removed for export] *)
  let x0 := znth x 0 in
  (* [comment removed for export] *)
  match (if (lnz <? 9) && (lnz <=? rp) && (rp <? 18) then
           if rp =? 9 then
             let sf := f128_of_i32 sign in                  (* [comment removed for export] *)
             let xf := f128_of_u32 x0 in                    (* [comment removed for export] *)
             Some (inr (f, f128_mul sf xf))                 (* [comment removed for export] *)
           else if rp <? 9 then
             let sf := f128_of_i32 sign in                  (* [comment removed for export] *)
             let xf := f128_of_u32 x0 in                    (* [comment removed for export] *)
             let t := f128_mul sf xf in                     (* [comment removed for export] *)
             let pf := f128_of_i32 (znth p10s (8 - rp)) in  (* [comment removed for export] *)
             Some (inr (f, f128_div t pf))                  (* [comment removed for export] *)
           else
             let bitlim := bits - 3 * (rp - 9) in
             if (30 <? bitlim) || (Z.shiftr x0 bitlim =? 0) then
               let sf := f128_of_i32 sign in                (* [comment removed for export] *)
               let xf := f128_of_u32 x0 in                  (* [comment removed for export] *)
               let t := f128_mul sf xf in                   (* [comment removed for export] *)
               let pf := f128_of_i32 (znth p10s (rp - 10)) in   (* [comment removed for export] *)
               Some (inr (f, f128_mul t pf))                (* [comment removed for export] *)
             else Some (inl tt)
         else Some (inl tt)) with
  | None => None
  | Some (inr r) => Some r
  | Some (inl _) =>
  df_p4 f a z e2 rp x bits emin sign emax frac bias
  end.

Definition df_p2 (f : shfile) (lrp j k dc lnz : Z) (x : list Z) (bits emin sign emax frac bias : Z) : option (shfile * Z) :=
  let x0 := znth x 0 in
  (* [comment removed for export] *)
  if x0 =? 0 then
    let t := fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 sign)) D_ZERO in   (* [comment removed for export] *)
    Some (f, f128_of_d (bv_unsigned t))                     (* [comment removed for export] *)
  else
  (* [comment removed for export] *)
  if (lrp =? dc) && (dc <? 10) && ((30 <? bits) || (Z.shiftr x0 bits =? 0)) then
    let sf := f128_of_i32 sign in                           (* [comment removed for export] *)
    let xf := f128_of_u32 x0 in                             (* [comment removed for export] *)
    Some (f, f128_mul sf xf)                                (* [comment removed for export] *)
  else if Z.quot (- emin) 2 <? lrp then
    let sf := f128_of_i32 sign in                           (* [comment removed for export] *)
    let t := f128_mul sf C_LDBL_MAX in                      (* [comment removed for export] *)
    Some (f, f128_mul t C_LDBL_MAX)                         (* [comment removed for export] *)
  else if lrp <? emin - 2 * LDBL_MANT_DIG_ then
    let sf := f128_of_i32 sign in                           (* [comment removed for export] *)
    let t := f128_mul sf C_LDBL_MIN in                      (* [comment removed for export] *)
    Some (f, f128_mul t C_LDBL_MIN)                         (* [comment removed for export] *)
  else
  (* [comment removed for export] *)
  match (if nz j then
           match df_pad_loop 10%nat k (j, x) with
           | None => None
           | Some (j, x) => Some (k + 1, x)                  (* [comment removed for export] *)
           end
         else Some (k, x)) with
  | None => None
  | Some (k, x) =>
  df_p3 f k lrp lnz x bits emin sign emax frac bias
  end.

Lemma decfloat_eq : forall fuelc f c bits emin sign pok,
  decfloat fuelc f c bits emin sign pok =
  let emax := - emin - bits + 3 in
  let zero0 := f128_of_i32 0 in                             (* [comment removed for export] *)
  let frac := zero0 in
  let bias := zero0 in
  (* [comment removed for export] *)
  match df_lz_loop fuelc (0, c, f) with
  | None => None
  | Some (gotdig, c, f) =>
  match (if c =? 46 then
           let '(c, f) := sh_getc f in                      (* [comment removed for export] *)
           match df_rz_loop fuelc (gotdig, 0, c, f) with
           | None => None
           | Some (gotdig, lrp, c, f) => Some (gotdig, 1, lrp, c, f)
           end
         else Some (gotdig, 0, 0, c, f)) with
  | None => None
  | Some (gotdig, gotrad, lrp, c, f) =>
  let x := zupd (zrepeat 0 KMAX) 0 0 in                     (* [comment removed for export] *)
  match df_dig_loop fuelc (mkDL f c 0 0 lrp 0 0 gotdig gotrad x) with
  | None => None
  | Some (mkDL f c j k lrp dc lnz gotdig gotrad x) =>
  let lrp := if nz gotrad then lrp else dc in               (* [comment removed for export] *)
  (* [comment removed for export] *)
  match (if nz gotdig && (Z.lor c 32 =? 101) then
           match scanexp fuelc f pok with                   (* [comment removed for export] *)
           | None => None
           | Some (f, e10) =>
             if e10 =? LLONG_MIN_ then
               if nz pok then Some (inl (sh_unget f, lrp + 0))            (* [comment removed for export] *)
               else Some (inr (sh_lim0 f, f128_of_i32 0))                 (* [comment removed for export] *)
             else Some (inl (f, lrp + e10))
           end
         else Some (inl ((if 0 <=? c then sh_unget f else f), lrp))) with  (* [comment removed for export] *)
  | None => None
  | Some (inr r) => Some r
  | Some (inl (f, lrp)) =>
  if negb (nz gotdig) then
    Some (sh_lim0 f, f128_of_i32 0)                         (* [comment removed for export] *)
  else
  df_p2 f lrp j k dc lnz x bits emin sign emax frac bias
  end end end end.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DSH (j k : Z) (x : list Z) : Prop :=
  (k = 0 -> (j = 0 -> znth x 0 = 0) /\ (1 <= j -> 10 ^ (j - 1) <= znth x 0 < 10 ^ j))
  /\ (1 <= k -> 10 ^ 8 <= znth x 0 < 10 ^ 9).

Definition DI (f0 : shfile) (s : st_dig) : Prop :=
  sh_wf (dl_f s) /\ sh_same f0 (dl_f s) /\ sh_rpos f0 <= sh_rpos (dl_f s)
  /\ (contc (dl_c s) -> sh_rpos (dl_f s) <= sh_N (dl_f s))
  /\ 0 <= dl_j s <= 8 /\ 0 <= dl_k s <= KMAX - 3
  /\ zlength (dl_x s) = KMAX /\ W32 (dl_x s) /\ DSH (dl_j s) (dl_k s) (dl_x s)
  /\ (dl_k s = 0 /\ dl_j s = 0 -> dl_c s <> 48 /\ (nz (dl_gotrad s) = false -> dl_c s <> 46)).

Definition bchar (c : Z) : Prop := -1 <= c < 256.

Lemma isdigitc_range : forall c, bchar c -> isdigitc c = true -> 48 <= c <= 57.
Proof.
  intros c [Hc1 Hc2] H. unfold isdigitc, u32 in H. apply Z.ltb_lt in H.
  destruct (Z.lt_ge_cases c 48).
  - exfalso. rewrite <- (Z.mod_add _ 1) in H by lia. rewrite Z.mod_small in H; lia.
  - destruct (Z.lt_ge_cases 57 c); [|lia]. exfalso. rewrite Z.mod_small in H; lia.
Qed.

(* [comment removed for export] *)
Definition BB (f : shfile) : Prop := forall i, 0 <= znth (sh_buf f) i < 256.
Lemma BB_of_bytes : forall f l, sh_buf f = l ++ [0] -> Forall (fun c => 0 <= c < 256) l -> BB f.
Proof.
  intros f l E F i. rewrite E. destruct (read_char_cases l i) as [->|I]; [lia|].
  rewrite Forall_forall in F. apply F. exact I.
Qed.
Lemma getc_bchar : forall f c f', BB f -> sh_wf f -> sh_getc f = (c, f') -> bchar c.
Proof.
  intros f c f' B W G. destruct (sh_getc_facts f c f' G W) as (_ & _ & _ & _ & _ & _ & _ & _ & SH).
  unfold bchar. destruct SH as [(-> & _)|(-> & _)]; [lia|]. pose proof (B (sh_rpos f)). lia.
Qed.

Lemma pow10_S : forall j, 0 <= j -> 10 ^ (j + 1) = 10 * 10 ^ j.
Proof. intros. rewrite <- Z.pow_succ_r by lia. f_equal. Qed.
Lemma pow10_le8 : forall j, 0 <= j <= 8 -> 1 <= 10 ^ j <= 10 ^ 8.
Proof. intros. split. { apply Z.pow_le_mono_r with (b := 0) (c := j) in H || idtac. pose proof (Z.pow_pos_nonneg 10 j). lia. } apply Z.pow_le_mono_r; lia. Qed.

Lemma contc_digit_or_dot : forall c, bchar c -> isdigitc c || (c =? 46) = true -> contc c.
Proof.
  intros c B H. apply orb_prop in H. destruct H as [H|H].
  - pose proof (isdigitc_range c B H). unfold contc. lia.
  - apply Z.eqb_eq in H. subst. unfold contc. lia.
Qed.

Lemma DI_intro : forall f0 f c j k lrp dc lnz gd gr x,
  sh_wf f -> sh_same f0 f -> sh_rpos f0 <= sh_rpos f -> (contc c -> sh_rpos f <= sh_N f) ->
  0 <= j <= 8 -> 0 <= k <= KMAX - 3 -> zlength x = KMAX -> W32 x -> DSH j k x ->
  (k = 0 /\ j = 0 -> c <> 48 /\ (nz gr = false -> c <> 46)) ->
  DI f0 (mkDL f c j k lrp dc lnz gd gr x).
Proof. intros. unfold DI; cbn. tauto. Qed.

Lemma cm_cont : forall c f, contc c -> cm c f = Z.max 0 (sh_N f - sh_rpos f + 1) + 1.
Proof. intros c f CC. unfold cm. replace (contb c) with true; [reflexivity|]. symmetry. apply contb_spec. exact CC. Qed.

Lemma df_dig_total : forall fuel f0 s,
  BB f0 -> DI f0 s -> bchar (dl_c s) -> cm (dl_c s) (dl_f s) < Z.of_nat fuel ->
  exists s', df_dig_loop fuel s = Some s' /\ DI f0 s' /\ bchar (dl_c s')
    /\ (df_dig_cond s' = false \/ dl_c s' = 46).
Proof.
  intros fuel f0 s HB HI HC HM. rewrite df_dig_loop_eq.
  apply (wbloop_total df_dig_cond df_dig_body (fun s => DI f0 s /\ bchar (dl_c s))
           (fun s' => DI f0 s' /\ bchar (dl_c s') /\ (df_dig_cond s' = false \/ dl_c s' = 46))
           (fun s => cm (dl_c s) (dl_f s))).
  - intros [f c j k lrp dc lnz gd gr x] [HIs HCs] CND. cbn [dl_c dl_f] in *.
    pose proof HIs as HIcopy.
    destruct HIs as (W & SM & R0 & CI & Hj & Hk & LX & WX & DS & Z0). cbn [dl_f dl_c dl_j dl_k dl_x dl_gotrad] in *.
    assert (CC : contc c) by (apply contc_digit_or_dot; assumption). specialize (CI CC).
    assert (HBf : BB f). { intros i. destruct SM as (Bf & _). rewrite Bf. apply HB. }
    unfold df_dig_body. cbn [dl_c dl_f dl_j dl_k dl_lrp dl_dc dl_lnz dl_gotdig dl_gotrad dl_x].
    destruct (Z.eqb_spec c 46) as [E46|N46].
    + (* [comment removed for export] *)
      destruct (nz gr) eqn:GR.
      * (* [comment removed for export] *) cbn [dl_c dl_f]. split; [exact HIcopy|]. split; [exact HCs| right; exact E46].
      * destruct (sh_getc f) as [c' f'] eqn:G. cbn [dl_c dl_f].
        destruct (sh_getc_facts f c' f' G W) as (W' & B' & S' & C0' & N' & n' & RP' & CT' & SH').
        destruct (cm_read f c' f' W G CI) as [M' CI'].
        assert (Hjk : ~ (k = 0 /\ j = 0)). { intros HH. destruct (Z0 HH) as [_ Z46]. exact (Z46 eq_refl E46). }
        split. 2:{ rewrite (cm_cont c f CC). split; [apply cm_nonneg| exact M']. }
        split; [| eapply getc_bchar; eauto].
        apply DI_intro; [exact W'| eapply sh_same_trans; [exact SM| eapply sh_same_getc; eauto] | lia | exact CI' | lia | lia | exact LX | exact WX | exact DS | intros HH; exfalso; exact (Hjk HH)].
    + (* [comment removed for export] *)
      assert (D : isdigitc c = true). { unfold df_dig_cond in CND. cbn in CND. apply orb_prop in CND. destruct CND as [?|E]; [assumption|]. apply Z.eqb_eq in E. lia. }
      pose proof (isdigitc_range c HCs D) as CR.
      destruct (Z.ltb_spec k (KMAX - 3)) as [LK|GK].
      * (* [comment removed for export] *)
        set (x1 := if nz j then zupd x k (u32 (znth x k * 10 + c - 48)) else zupd x k (c - 48)).
        set (j1 := j + 1).
        destruct (sh_getc f) as [c' f'] eqn:G.
        destruct (sh_getc_facts f c' f' G W) as (W' & B' & S' & C0' & N' & n' & RP' & CT' & SH').
        destruct (cm_read f c' f' W G CI) as [M' CI'].
        assert (WX1 : W32 x1). { subst x1. destruct (nz j); [apply W32_u32; exact WX| apply W32_zupd; [exact WX| lia]]. }
        assert (LX1 : zlength x1 = KMAX). { subst x1. destruct (nz j); rewrite zlength_zupd; exact LX. }
        (* [comment removed for export] *)
        assert (X0 : (1 <= k -> znth x1 0 = znth x 0) /\ (k = 0 -> 10 ^ (j1 - 1) <= znth x1 0 < 10 ^ j1)).
        { destruct DS as [D1 D2]. split.
          - intros K1. subst x1. destruct (nz j); rewrite znth_zupd_neq by lia; reflexivity.
          - intros K0. subst x1 j1. subst k. destruct (D1 eq_refl) as [Dj0 Dj1].
            unfold nz. destruct (Z.eqb_spec j 0) as [J0|J0]; cbn [negb].
            + rewrite znth_zupd_eq by (rewrite LX; unfold KMAX; lia). replace (j + 1 - 1) with 0 by lia. rewrite J0.
              destruct (Z0 ltac:(lia)) as [N48 _]. change (10^0) with 1. change (10^(0+1)) with 10. lia.
            + rewrite znth_zupd_eq by (rewrite LX; unfold KMAX; lia). replace (j + 1 - 1) with j by lia.
              specialize (Dj1 ltac:(lia)).
              assert (P7 : 1 <= 10 ^ (j - 1) <= 10 ^ 7). { split. { pose proof (Z.pow_pos_nonneg 10 (j-1)). lia. } apply Z.pow_le_mono_r; lia. }
              change (10 ^ 7) with 10000000 in P7.
              rewrite pow10_S by lia. replace (10 ^ j) with (10 * 10 ^ (j - 1)) in * by (rewrite <- pow10_S by lia; f_equal; lia).
              rewrite u32_id; [lia|]. lia. }
        destruct X0 as [X0a X0b].
        destruct (Z.eqb_spec j1 9) as [J9|J9]; cbn [dl_c dl_f].
        -- (* [comment removed for export] *)
           split. 2:{ rewrite (cm_cont c f CC). split; [apply cm_nonneg| exact M']. }
           split; [| eapply getc_bchar; eauto].
           apply DI_intro; [exact W'| eapply sh_same_trans; [exact SM| eapply sh_same_getc; eauto] | lia | exact CI' | lia | unfold KMAX in *; lia | exact LX1 | exact WX1 | | intros [? ?]; lia].
           split; [intros; lia|]. intros _. destruct (Z.eq_dec k 0) as [K0|K0].
           ++ specialize (X0b K0). rewrite J9 in X0b. replace (9 - 1) with 8 in X0b by lia. exact X0b.
           ++ rewrite X0a by lia. apply (proj2 DS). lia.
        -- split. 2:{ rewrite (cm_cont c f CC). split; [apply cm_nonneg| exact M']. }
           split; [| eapply getc_bchar; eauto].
           apply DI_intro; [exact W'| eapply sh_same_trans; [exact SM| eapply sh_same_getc; eauto] | lia | exact CI' | subst j1; lia | unfold KMAX in *; lia | exact LX1 | exact WX1 | | subst j1; intros [? ?]; lia].
           split. { intros K0. split; [subst j1; intros; lia|]. intros _. apply X0b. exact K0. } intros K1. rewrite X0a by lia. apply (proj2 DS). lia.
      * (* [comment removed for export] *)
        destruct (sh_getc f) as [c' f'] eqn:G.
        destruct (sh_getc_facts f c' f' G W) as (W' & B' & S' & C0' & N' & n' & RP' & CT' & SH').
        destruct (cm_read f c' f' W G CI) as [M' CI'].
        assert (WXg : forall x1, (x1 = x \/ x1 = zupd x (KMAX - 4) (Z.lor (znth x (KMAX - 4)) 1)) ->
                      W32 x1 /\ zlength x1 = KMAX /\ znth x1 0 = znth x 0).
        { intros x1 [->| ->]; [auto|].
          split; [apply W32_zupd; [exact WX|]|]. { pose proof (WX (KMAX - 4)). apply Z_lor_lt_pow2'; lia. }
          rewrite zlength_zupd, znth_zupd_neq by (unfold KMAX; lia). auto. }
        destruct (negb (c =? 48));
          [destruct (WXg (zupd x (KMAX - 4) (Z.lor (znth x (KMAX - 4)) 1)) ltac:(right; reflexivity)) as (WX1 & LX1 & E0)
          |destruct (WXg x ltac:(left; reflexivity)) as (WX1 & LX1 & E0)];
          cbn [dl_c dl_f].
        all: split; [| rewrite (cm_cont c f CC); split; [apply cm_nonneg| exact M']].
        all: split; [| eapply getc_bchar; eauto].
        all: apply DI_intro; [exact W'| eapply sh_same_trans; [exact SM| eapply sh_same_getc; eauto] | lia | exact CI' | lia | lia | exact LX1 | exact WX1 | | intros [? ?]; unfold KMAX in *; lia].
        all: unfold DSH; try rewrite E0; split; [intros; unfold KMAX in *; lia|]; intros; apply (proj2 DS); lia.
  - intros s' [HI' HC'] CND. auto.
  - split; assumption.
  - split; [apply cm_nonneg| exact HM].
Qed.

(* [comment removed for export] *)
Definition LZI (f0 : shfile) (c : Z) (f : shfile) : Prop :=
  sh_wf f /\ sh_same f0 f /\ sh_rpos f0 <= sh_rpos f /\ (contc c -> sh_rpos f <= sh_N f) /\ bchar c.

Lemma LZI_read : forall f0 c f c' f', BB f0 -> LZI f0 c f -> contc c -> sh_getc f = (c', f') ->
  LZI f0 c' f' /\ 0 <= cm c' f' < cm c f.
Proof.
  intros f0 c f c' f' HB (W & SM & R & CI & BC) CC G.
  specialize (CI CC).
  destruct (sh_getc_facts f c' f' G W) as (W' & B' & S' & C0' & N' & n' & RP' & CT' & SH').
  destruct (cm_read f c' f' W G CI) as [M' CI'].
  assert (HBf : BB f). { intros i. destruct SM as (Bf & _). rewrite Bf. apply HB. }
  split.
  - unfold LZI. split; [exact W'|]. split; [eapply sh_same_trans; [exact SM| eapply sh_same_getc; eauto]|].
    split; [lia|]. split; [exact CI'|]. eapply getc_bchar; eauto.
  - rewrite (cm_cont c f CC). split; [apply cm_nonneg| exact M'].
Qed.

Lemma contc48 : contc 48. Proof. unfold contc. lia. Qed.

Lemma df_lz_total : forall fuel f0 g c f,
  BB f0 -> LZI f0 c f -> cm c f < Z.of_nat fuel ->
  exists g' c' f', df_lz_loop fuel (g, c, f) = Some (g', c', f') /\ LZI f0 c' f' /\ c' <> 48 /\ cm c' f' <= cm c f.
Proof.
  intros fuel f0 g c f HB HI HM. rewrite df_lz_loop_eq.
  destruct (wloop_total (fun st : Z * Z * shfile => let '(_, c, _) := st in c =? 48) df_lz_body
            (fun st => let '(_, c', f') := st in LZI f0 c' f' /\ cm c' f' <= cm c f)
            (fun st => let '(_, c', f') := st in cm c' f')) with (fuel := fuel) (s := (g, c, f))
    as [[[g' c'] f'] (E & [HI' HM'] & C)].
  - intros [[g1 c1] f1] [HI1 M1] C1. apply Z.eqb_eq in C1. subst c1.
    unfold df_lz_body. destruct (sh_getc f1) as [c2 f2] eqn:G.
    destruct (LZI_read f0 48 f1 c2 f2 HB HI1 contc48 G) as [HI2 M2]. split; [split; [exact HI2| lia]| exact M2].
  - split; [exact HI| lia].
  - split; [apply cm_nonneg| exact HM].
  - exists g', c', f'. split; [exact E|]. split; [exact HI'|]. split; [| exact HM']. apply Z.eqb_neq. exact C.
Qed.

Lemma df_rz_total : forall fuel f0 g l c f,
  BB f0 -> LZI f0 c f -> cm c f < Z.of_nat fuel ->
  exists g' l' c' f', df_rz_loop fuel (g, l, c, f) = Some (g', l', c', f') /\ LZI f0 c' f' /\ c' <> 48 /\ cm c' f' <= cm c f.
Proof.
  intros fuel f0 g l c f HB HI HM. rewrite df_rz_loop_eq.
  destruct (wloop_total (fun st : Z * Z * Z * shfile => let '(_, _, c, _) := st in c =? 48) df_rz_body
            (fun st => let '(_, _, c', f') := st in LZI f0 c' f' /\ cm c' f' <= cm c f)
            (fun st => let '(_, _, c', f') := st in cm c' f')) with (fuel := fuel) (s := (g, l, c, f))
    as [[[[g' l'] c'] f'] (E & [HI' HM'] & C)].
  - intros [[[g1 l1] c1] f1] [HI1 M1] C1. apply Z.eqb_eq in C1. subst c1.
    unfold df_rz_body. destruct (sh_getc f1) as [c2 f2] eqn:G.
    destruct (LZI_read f0 48 f1 c2 f2 HB HI1 contc48 G) as [HI2 M2]. split; [split; [exact HI2| lia]| exact M2].
  - split; [exact HI| lia].
  - split; [apply cm_nonneg| exact HM].
  - exists g', l', c', f'. split; [exact E|]. split; [exact HI'|]. split; [| exact HM']. apply Z.eqb_neq. exact C.
Qed.

(* [comment removed for export] *)
Definition P2pre (j k : Z) (x : list Z) : Prop :=
  0 <= j <= 8 /\ 0 <= k <= KMAX - 3 /\ zlength x = KMAX /\ W32 x /\ DSH j k x.

Definition df_p2_total_stmt : Prop :=
  forall f lrp j k dc lnz x sign emax frac bias,
    P2pre j k x ->
    exists y, df_p2 f lrp j k dc lnz x 53 (-1074) sign emax frac bias = Some (f, y).

Lemma lor32_101_cont : forall c, (Z.lor c 32 =? 101) = true -> contc c.
Proof.
  intros c H. apply Z.eqb_eq in H. unfold contc. split; intros ->; cbv in H; discriminate.
Qed.

Lemma decfloat_total : df_p2_total_stmt ->
  forall fuelc f c sign pok,
  sh_wf f -> BB f -> bchar c -> (contc c -> sh_rpos f <= sh_N f) -> 0 <= sh_rpos f ->
  zlength (sh_buf f) + 2 <= Z.of_nat fuelc ->
  (sh_stdio f = false -> sh_cnt0 f + 1 <= sh_rpos f) ->
  exists f' y, decfloat fuelc f c 53 (-1074) sign pok = Some (f', y)
    /\ sh_wf f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f
    /\ (sh_stdio f = false -> sh_cnt0 f' <= sh_rpos f').
Proof.
  intros HP2 fuelc f c sign pok W HB BC CI R0 FU NS.
  pose proof (sh_N_le f W) as NL.
  rewrite decfloat_eq. cbv zeta.
  assert (HI0 : LZI f c f). { unfold LZI. split; [exact W|]. split; [apply sh_same_refl|]. split; [lia|]. split; [exact CI| exact BC]. }
  assert (LNN : 0 <= zlength (sh_buf f)) by (unfold zlength; lia).
  assert (M0 : cm c f < Z.of_nat fuelc). { unfold cm. destruct (contb c); lia. }
  destruct (df_lz_total fuelc f 0 c f HB HI0 M0) as [g1 [c1 [f1 (E1 & HI1 & N48 & M1)]]]. rewrite E1.
  (* [comment removed for export] *)
  match goal with |- context [match ?e with Some _ => _ | None => None end] =>
    assert (HR : exists g2 gr lrp c2 f2, e = Some (g2, gr, lrp, c2, f2) /\ LZI f c2 f2 /\ c2 <> 48 /\ (gr = 0 -> c2 <> 46) /\ (gr = 0 \/ gr = 1) /\ cm c2 f2 <= cm c f)
  end.
  { destruct (Z.eqb_spec c1 46) as [E46|N46].
    - destruct (sh_getc f1) as [c1' f1'] eqn:G.
      assert (CC : contc c1) by (subst; unfold contc; lia).
      destruct (LZI_read f c1 f1 c1' f1' HB HI1 CC G) as [HI1' M1'].
      destruct (df_rz_total fuelc f g1 0 c1' f1' HB HI1' ltac:(lia)) as [g2 [l2 [c2 [f2 (E2 & HI2 & N48' & M2)]]]].
      rewrite E2. eexists _, _, _, _, _. split; [reflexivity|]. split; [exact HI2|]. split; [exact N48'|]. split; [intros; lia|]. split; [lia|lia].
    - eexists _, _, _, _, _. split; [reflexivity|]. split; [exact HI1|]. split; [exact N48|]. split; [intros _; exact N46|]. split; [lia|lia]. }
  destruct HR as [g2 [gr [lrp [c2 [f2 (-> & HI2 & N48' & N46 & GR & M2)]]]]].
  destruct HI2 as (W2 & SM2 & R2 & CI2 & BC2).
  (* [comment removed for export] *)
  set (x0 := zupd (zrepeat 0 KMAX) 0 0).
  assert (DI0 : DI f (mkDL f2 c2 0 0 lrp 0 0 g2 gr x0)).
  { apply DI_intro; try assumption; try lia.
    - unfold KMAX; lia.
    - subst x0. rewrite zlength_zupd. apply zlength_zrepeat. unfold KMAX; lia.
    - subst x0. apply W32_zupd; [apply W32_zrepeat| lia].
    - unfold DSH. subst x0. rewrite znth_zupd_eq by (rewrite zlength_zrepeat; unfold KMAX; lia). split; [|intros; lia]. intros _. split; [reflexivity| intros; lia].
    - intros _. split; [exact N48'|]. intros GZ. apply N46. unfold nz in GZ. destruct (Z.eqb_spec gr 0); [assumption| discriminate GZ]. }
  destruct (df_dig_total fuelc f _ HB DI0 BC2 ltac:(cbn [dl_c dl_f]; lia)) as [s3 (E3 & HI3 & BC3 & X3)].
  rewrite E3. destruct s3 as [f3 c3 j3 k3 lrp3 dc3 lnz3 gd3 gr3 x3]. cbn [dl_c dl_f] in *.
  destruct HI3 as (W3 & SM3 & R3 & CI3 & Hj3 & Hk3 & LX3 & WX3 & DS3 & _). cbn [dl_f dl_c dl_j dl_k dl_x dl_gotrad] in *.
  assert (P2 : P2pre j3 k3 x3) by (unfold P2pre; tauto).
  destruct SM3 as (B3 & S3 & C03 & N3 & n3).
  assert (CLOSE : forall f' lrp',
    sh_wf f' -> sh_buf f' = sh_buf f -> sh_stdio f' = sh_stdio f -> (sh_stdio f = false -> sh_cnt0 f' <= sh_rpos f') ->
    exists f'' y, (if negb (nz gd3) then Some (sh_lim0 f', f128_of_i32 0)
                   else df_p2 f' lrp' j3 k3 dc3 lnz3 x3 53 (-1074) sign (- -1074 - 53 + 3) (f128_of_i32 0) (f128_of_i32 0)) = Some (f'', y)
      /\ sh_wf f'' /\ sh_buf f'' = sh_buf f /\ sh_stdio f'' = sh_stdio f /\ (sh_stdio f = false -> sh_cnt0 f'' <= sh_rpos f'')).
  { intros f' lrp' W' B' S' NS'. destruct (negb (nz gd3)).
    - eexists _, _. split; [reflexivity|]. split; [now apply sh_lim0_wf|]. unfold sh_lim0; cbn. repeat split; try assumption. intros; lia.
    - destruct (HP2 f' lrp' j3 k3 dc3 lnz3 x3 sign (- -1074 - 53 + 3) (f128_of_i32 0) (f128_of_i32 0) P2) as [y Ey].
      rewrite Ey. eexists _, _. split; [reflexivity|]. auto. }
  (* [comment removed for export] *)
  destruct (nz gd3 && (Z.lor c3 32 =? 101)) eqn:EX.
  - apply andb_prop in EX. destruct EX as [_ EX]. pose proof (lor32_101_cont c3 EX) as CC3. specialize (CI3 CC3).
    destruct (scanexp_total fuelc f3 pok W3 ltac:(lia) ltac:(rewrite B3; lia)) as [f4 [e10 (E4 & W4 & SM4 & R4)]].
    rewrite E4. destruct SM4 as (B4 & S4 & C04 & N4 & n4).
    destruct (e10 =? LLONG_MIN_).
    + destruct (nz pok).
      * destruct (sh_unget_facts f4 W4) as (W5 & SM5 & R5). destruct SM5 as (B5 & S5 & C05 & N5 & n5).
        apply CLOSE; [exact W5| congruence| congruence|]. intros ST. rewrite C05, C04, C03. specialize (R4 ltac:(congruence)). specialize (NS ST). lia.
      * eexists _, _. split; [reflexivity|]. split; [now apply sh_lim0_wf|]. unfold sh_lim0; cbn. split; [congruence|]. split; [congruence|]. intros; lia.
    + apply CLOSE; [exact W4| congruence| congruence|]. intros ST. rewrite C04, C03. specialize (R4 ltac:(congruence)). specialize (NS ST). lia.
  - destruct (0 <=? c3).
    + destruct (sh_unget_facts f3 W3) as (W5 & SM5 & R5). destruct SM5 as (B5 & S5 & C05 & N5 & n5).
      apply CLOSE; [exact W5| congruence| congruence|]. intros ST. rewrite C05, C03. specialize (NS ST). lia.
    + apply CLOSE; [exact W3| congruence| congruence|]. intros ST. rewrite C03. specialize (NS ST). lia.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition PADI (k : Z) (x0 : list Z) (st : Z * list Z) : Prop :=
  let '(j, x) := st in
  1 <= j <= 9 /\ zlength x = KMAX /\ W32 x /\
  (k = 0 -> 10 ^ (j - 1) <= znth x 0 < 10 ^ j) /\
  (1 <= k -> znth x 0 = znth x0 0).

Lemma df_pad_total : forall k j x,
  0 <= k < KMAX -> PADI k x (j, x) ->
  exists j' x', df_pad_loop 10%nat k (j, x) = Some (j', x') /\ PADI k x (j', x') /\ j' = 9.
Proof.
  intros k j x Hk HI. rewrite df_pad_loop_eq.
  destruct (wloop_total (fun st : Z * list Z => fst st <? 9) (df_pad_body k) (PADI k x)
             (fun st => 9 - fst st)) with (fuel := 10%nat) (s := (j, x)) as [[j' x'] (E & HI' & C)].
  - intros [j1 x1] (Hj & L1 & W1 & A1 & B1) C1. cbn [fst] in C1. apply Z.ltb_lt in C1.
    unfold df_pad_body. cbn [fst]. split; [|lia].
    unfold PADI. split; [lia|]. split; [now rewrite zlength_zupd|]. split; [now apply W32_u32|].
    split.
    + intros K0. subst k. specialize (A1 eq_refl).
      assert (P7 : 1 <= 10 ^ (j1 - 1) <= 10 ^ 7). { split. { pose proof (Z.pow_pos_nonneg 10 (j1-1)). lia. } apply Z.pow_le_mono_r; lia. }
      change (10 ^ 7) with 10000000 in P7.
      rewrite znth_zupd_eq by (rewrite L1; unfold KMAX; lia).
      replace (j1 + 1 - 1) with j1 by lia.
      replace (10 ^ (j1 + 1)) with (10 * (10 * 10 ^ (j1 - 1))).
      2:{ rewrite pow10_S by lia. f_equal. rewrite <- pow10_S by lia. f_equal. lia. }
      replace (10 ^ j1) with (10 * 10 ^ (j1 - 1)) in * by (rewrite <- pow10_S by lia; f_equal; lia).
      rewrite u32_id; lia.
    + intros K1. rewrite znth_zupd_neq by lia. apply B1. exact K1.
  - exact HI.
  - cbn [fst]. destruct HI as (Hj & _). change (Z.of_nat 10) with 10. lia.
  - exists j', x'. split; [exact E|]. split; [exact HI'|]. cbn [fst] in C. apply Z.ltb_ge in C. destruct HI' as (Hj' & _). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition P3pre (z lrp : Z) (x : list Z) : Prop :=
  1 <= z <= KMAX - 2 /\ zlength x = KMAX /\ W32 x /\ 10 ^ 8 <= znth x 0 < 10 ^ 9 /\ -1300 <= lrp <= 537.

Definition df_p3_total_stmt : Prop :=
  forall f z lrp lnz x sign emax frac bias,
    P3pre z lrp x ->
    exists y, df_p3 f z lrp lnz x 53 (-1074) sign emax frac bias = Some (f, y).

Lemma df_p2_total : df_p3_total_stmt -> df_p2_total_stmt.
Proof.
  intros HP3 f lrp j k dc lnz x sign emax frac bias (Hj & Hk & LX & WX & DS).
  unfold df_p2.
  destruct (Z.eqb_spec (znth x 0) 0) as [X0|X0]. { eexists; reflexivity. }
  destruct (_ && _ && _). { eexists; reflexivity. }
  change (Z.quot (- -1074) 2) with 537. change (-1074 - 2 * LDBL_MANT_DIG_) with (-1300).
  destruct (Z.ltb_spec 537 lrp). { eexists; reflexivity. }
  destruct (Z.ltb_spec lrp (-1300)). { eexists; reflexivity. }
  destruct DS as [D1 D2].
  destruct (nz j) eqn:NJ.
  - assert (J1 : 1 <= j). { unfold nz in NJ. destruct (Z.eqb_spec j 0); [discriminate NJ| lia]. }
    destruct (df_pad_total k j x ltac:(unfold KMAX in *; lia)) as [j' [x' (E & (Hj' & L' & W' & A' & B') & J9)]].
    { unfold PADI. split; [lia|]. split; [exact LX|]. split; [exact WX|]. split.
      - intros K0. apply (proj2 (D1 K0)). lia.
      - intros; reflexivity. }
    rewrite E. apply HP3. unfold P3pre. split; [unfold KMAX in *; lia|]. split; [exact L'|]. split; [exact W'|].
    split; [|lia]. subst j'. destruct (Z.eq_dec k 0) as [K0|K0].
    + specialize (A' K0). replace (9 - 1) with 8 in A' by lia. exact A'.
    + rewrite B' by lia. apply D2. lia.
  - assert (J0 : j = 0). { unfold nz in NJ. destruct (Z.eqb_spec j 0); [lia| discriminate NJ]. }
    assert (K1 : 1 <= k). { destruct (Z.eq_dec k 0) as [K0|]; [|lia]. exfalso. apply X0. apply (proj1 (D1 K0)). exact J0. }
    apply HP3. unfold P3pre. split; [unfold KMAX in *; lia|]. split; [exact LX|]. split; [exact WX|]. split; [apply D2; lia| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition P4pre (z rp : Z) (x : list Z) : Prop :=
  1 <= z <= KMAX - 2 /\ zlength x = KMAX /\ W32 x /\ 10 ^ 8 <= znth x 0 < 10 ^ 9 /\ -1300 <= rp <= 537.

Definition df_p4_total_stmt : Prop :=
  forall f z rp x sign emax frac bias,
    P4pre z rp x ->
    exists y, df_p4 f 0 z 0 rp x 53 (-1074) sign emax frac bias = Some (f, y).

Lemma df_p3_total : df_p4_total_stmt -> df_p3_total_stmt.
Proof.
  intros HP4 f z lrp lnz x sign emax frac bias (Hz & LX & WX & X0 & Hl).
  unfold df_p3. rewrite s32_id by lia.
  destruct (_ && _ && _).
  - destruct (lrp =? 9). { eexists; reflexivity. }
    destruct (lrp <? 9). { eexists; reflexivity. }
    destruct (_ || _). { eexists; reflexivity. }
    apply HP4. unfold P4pre. tauto.
  - apply HP4. unfold P4pre. tauto.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma df_tz_total : forall x z,
  1 <= z <= KMAX - 2 -> znth x 0 <> 0 ->
  exists z', df_tz_loop FUEL_RING x z = Some z' /\ 1 <= z' <= z.
Proof.
  intros x z Hz X0. rewrite df_tz_loop_eq.
  destruct (wloop_total (fun z => znth x (z - 1) =? 0) df_tz_body (fun z' => 1 <= z' <= z) (fun z' => z'))
    with (fuel := FUEL_RING) (s := z) as [z' (E & R & _)].
  - intros z1 R1 C1. apply Z.eqb_eq in C1. unfold df_tz_body.
    assert (z1 <> 1) by (intros ->; apply X0; exact C1). lia.
  - lia.
  - unfold FUEL_RING, KMAX in *. change (Z.of_nat 2050) with 2050. lia.
  - exists z'. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma p10s_val : forall i, 0 <= i <= 7 -> znth p10s i = 10 ^ (i + 1).
Proof.
  intros i Hi.
  assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; reflexivity.
Qed.

Definition ALI (z rp : Z) (x0 : list Z) (s : st_al) : Prop :=
  al_a s = 0 /\ 0 <= al_k s <= z /\ al_rp s = rp /\ 0 <= al_carry s < 2^32 /\
  W32 (al_x s) /\ zlength (al_x s) = KMAX /\
  (al_k s = 0 -> al_x s = x0 /\ al_carry s = 0) /\ (1 <= al_k s -> 1 <= znth (al_x s) 0).

Lemma df_al_total : forall p10 z rp x,
  1 <= z <= KMAX - 2 -> zlength x = KMAX -> W32 x -> 10 ^ 8 <= znth x 0 < 10 ^ 9 ->
  10 <= p10 <= 10 ^ 8 ->
  exists s', df_al_loop FUEL_RING p10 z (mkAL 0 0 rp 0 x) = Some s' /\ ALI z rp x s' /\ al_k s' = z.
Proof.
  intros p10 z rp x Hz LX WX X0 Hp. change (10 ^ 8) with 100000000 in *. change (10 ^ 9) with 1000000000 in *.
  rewrite df_al_loop_eq.
  destruct (wloop_total (fun s => negb (al_k s =? z)) (df_al_body p10) (ALI z rp x) (fun s => z - al_k s))
    with (fuel := FUEL_RING) (s := mkAL 0 0 rp 0 x) as [s' (E & HI & C)].
  - intros [k a rp1 carry x1] (A & K & RP & CR & W1 & L1 & HZ0 & HZ1) C1. cbn [al_a al_k al_rp al_carry al_x] in *.
    destruct (Z.eqb_spec k z); [discriminate C1|]. subst a rp1.
    unfold df_al_body. cbn [al_k al_x al_carry al_a al_rp].
    set (x2 := zupd x1 k (u32 (znth x1 k / p10 + carry))).
    assert (W2 : W32 x2) by (apply W32_u32; exact W1).
    assert (L2 : zlength x2 = KMAX) by (subst x2; now rewrite zlength_zupd).
    assert (X20 : 1 <= znth x2 0).
    { subst x2. destruct (Z.eq_dec k 0) as [->|K0].
      - destruct (HZ0 eq_refl) as [-> ->]. rewrite znth_zupd_eq by (rewrite LX; unfold KMAX; lia).
        assert (1 <= znth x 0 / p10). { apply Z.div_le_lower_bound; lia. }
        assert (znth x 0 / p10 < 2^32). { apply Z.div_lt_upper_bound; lia. }
        rewrite u32_id; lia.
      - rewrite znth_zupd_neq by lia. apply HZ1. lia. }
    destruct ((k =? 0) && (znth x2 k =? 0)) eqn:ADV.
    { exfalso. apply andb_prop in ADV. destruct ADV as [A1 A2]. apply Z.eqb_eq in A1. apply Z.eqb_eq in A2. subst k. lia. }
    cbn [al_a al_k al_rp al_carry al_x]. split; [|lia].
    unfold ALI; cbn. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [apply u32_range|].
    split; [exact W2|]. split; [exact L2|]. split; [intros; lia|]. intros _. exact X20.
  - unfold ALI; cbn. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [exact WX|]. split; [exact LX|]. split; [auto| intros; lia].
  - cbn. unfold FUEL_RING, KMAX in *. change (Z.of_nat 2050) with 2050. lia.
  - exists s'. split; [exact E|]. split; [exact HI|]. destruct (Z.eqb_spec (al_k s') z); [assumption| discriminate C].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rdist (k a : Z) : Z := (k - a) mod 2048.

Lemma land_MASK_mod : forall k, Z.land k MASK = k mod 2048.
Proof. apply land_MASK. Qed.

Lemma rdist_step_down : forall k a, 0 <= k < 2048 -> 0 <= a < 2048 -> k <> a ->
  0 <= rdist (Z.land (k - 1) MASK) a < rdist k a.
Proof.
  intros k a Hk Ha Hne. unfold rdist. rewrite land_MASK_mod.
  rewrite <- Zminus_mod_idemp_l.
  (* [comment removed for export] *)
  destruct (Z.lt_ge_cases k a).
  - (* [comment removed for export] *)
    replace ((k - a) mod 2048) with (k - a + 2048).
    2:{ symmetry. rewrite <- (Z.mod_add _ 1) by lia. apply Z.mod_small. lia. }
    destruct (Z.eq_dec k 0) as [->|K0].
    + change ((0 - 1) mod 2048) with 2047. rewrite Z.mod_small; lia.
    + rewrite (Z.mod_small (k - 1)) by lia. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small; lia.
  - replace ((k - a) mod 2048) with (k - a) by (symmetry; apply Z.mod_small; lia).
    rewrite (Z.mod_small (k - 1)) by lia. rewrite Z.mod_small; lia.
Qed.

Definition UKI (a XA : Z) (s : st_upk) : Prop :=
  0 <= uk_k s < 2048 /\ 0 <= uk_carry s < 2^32 /\ 0 <= uk_z s < 2048 /\ uk_z s <> a /\
  W32 (uk_x s) /\ zlength (uk_x s) = KMAX /\ znth (uk_x s) a = XA.

Definition UKQ (a XA : Z) (s : st_upk) : Prop :=
  exists cin, 0 <= cin < 2^32 /\ W32 (uk_x s) /\ zlength (uk_x s) = KMAX /\ 0 <= uk_z s < 2048 /\ uk_z s <> a /\
    0 <= uk_carry s < 2^32 /\
    (1000000000 < XA * 2^29 + cin -> uk_carry s = (XA * 2^29 + cin) / 1000000000) /\
    (XA * 2^29 + cin <= 1000000000 -> uk_carry s = 0 /\ znth (uk_x s) a = XA * 2^29 + cin).

Lemma upk_tmp_range : forall xk c, 0 <= xk < 2^32 -> 0 <= c < 2^32 ->
  u64 (Z.shiftl xk 29 + c) = xk * 2^29 + c /\ 0 <= xk * 2^29 + c < 2^61 + 2^32 /\ (xk * 2^29 + c) / 1000000000 < 2^32.
Proof.
  intros xk c Hx Hc. rewrite Z.shiftl_mul_pow2 by lia.
  split; [apply u64_id; lia|]. split; [lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma df_upk_total : forall a XA s,
  0 <= a < 2048 -> UKI a XA s ->
  exists s', df_upk_loop FUEL_RING a s = Some s' /\ UKQ a XA s'.
Proof.
  intros a XA s Ha HI. rewrite df_upk_loop_eq.
  apply (bloop_total (df_upk_body a) (UKI a XA) (UKQ a XA) (fun s => rdist (uk_k s) a)).
  - intros [k carry z x] (Hk & Hc & Hz & Hza & WX & LX & XAe). cbn [uk_k uk_carry uk_z uk_x] in *.
    unfold df_upk_body. cbn [uk_k uk_carry uk_z uk_x].
    pose proof (WX k) as Wk.
    destruct (upk_tmp_range (znth x k) carry Wk Hc) as (TE & TR & TD). rewrite TE.
    set (tmp := znth x k * 2^29 + carry) in *.
    set (cx := if 1000000000 <? tmp then (u32 (tmp / 1000000000), zupd x k (u32 (tmp mod 1000000000))) else (0, zupd x k (u32 tmp))).
    assert (CX : exists carry' x', cx = (carry', x') /\ 0 <= carry' < 2^32 /\ W32 x' /\ zlength x' = KMAX /\
                 (forall i, i <> k -> znth x' i = znth x i) /\
                 (1000000000 < tmp -> carry' = tmp / 1000000000) /\
                 (tmp <= 1000000000 -> carry' = 0 /\ znth x' k = tmp)).
    { subst cx. destruct (Z.ltb_spec 1000000000 tmp).
      - eexists _, _. split; [reflexivity|]. split; [apply u32_range|]. split; [now apply W32_u32|]. split; [now rewrite zlength_zupd|].
        split; [intros i Hi; now rewrite znth_zupd_neq by lia|]. split; [intros _; apply u32_id; split; [apply Z.div_pos; lia| exact TD]| intros; lia].
      - eexists _, _. split; [reflexivity|]. split; [lia|]. split; [now apply W32_u32|]. split; [now rewrite zlength_zupd|].
        split; [intros i Hi; now rewrite znth_zupd_neq by lia|]. split; [intros; lia|]. intros _. split; [reflexivity|].
        rewrite znth_zupd_eq by (rewrite LX; unfold KMAX; lia). apply u32_id. lia. }
    destruct CX as [carry' [x' (-> & Hc' & WX' & LX' & OTH & C1 & C2)]].
    set (z' := if (k =? Z.land (z - 1) MASK) && negb (k =? a) && (znth x' k =? 0) then k else z).
    assert (Hz' : 0 <= z' < 2048 /\ z' <> a).
    { subst z'. destruct (Z.eqb_spec k a); cbn [negb andb]. { rewrite andb_false_r. cbn. lia. }
      destruct (_ && _ && _); lia. }
    destruct (Z.eqb_spec k a) as [->|NE].
    + (* [comment removed for export] *)
      unfold UKQ; cbn. exists carry. split; [lia|]. split; [exact WX'|]. split; [exact LX'|]. split; [lia|]. split; [lia|]. split; [lia|].
      subst tmp. rewrite XAe in C1, C2. split; [exact C1| exact C2].
    + cbn [uk_k uk_carry uk_z uk_x]. split.
      * unfold UKI; cbn. split; [apply land_MASK_range|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact WX'|]. split; [exact LX'|].
        rewrite OTH by lia. exact XAe.
      * apply rdist_step_down; lia.
  - exact HI.
  - unfold rdist, FUEL_RING. change (Z.of_nat 2050) with 2050. pose proof (Z.mod_pos_bound (uk_k s - a) 2048 ltac:(lia)). lia.
Qed.

Definition USI (s : st_up) : Prop :=
  0 <= us_a s < 2048 /\ 0 <= us_z s < 2048 /\ us_a s <> us_z s /\ zlength (us_x s) = KMAX /\ W32 (us_x s) /\
  1 <= znth (us_x s) (us_a s) /\ us_rp s mod 9 = 0 /\ -1296 <= us_rp s <= 540.

Definition usm (s : st_up) : Z :=
  Z.max 0 (2 * ((45 - us_rp s) / 9) + (if znth (us_x s) (us_a s) <=? 1 then 1 else 0)).

Lemma df_up_cond_true : forall s, df_up_cond s = true -> us_rp s <= 36.
Proof.
  intros s H. unfold df_up_cond in H. apply orb_prop in H. destruct H as [H|H].
  - apply Z.ltb_lt in H. unfold LD_B1B_DIG in H. lia.
  - apply andb_prop in H. destruct H as [H _]. apply Z.eqb_eq in H. unfold LD_B1B_DIG in H. lia.
Qed.
Lemma df_up_cond_false : forall s, df_up_cond s = false ->
  36 <= us_rp s /\ (us_rp s = 36 -> znth th_list 0 <= znth (us_x s) (us_a s)).
Proof.
  intros s H. unfold df_up_cond in H. apply orb_false_elim in H. destruct H as [H1 H2].
  apply Z.ltb_ge in H1. unfold LD_B1B_DIG in *. split; [lia|]. intros E.
  apply andb_false_iff in H2. destruct H2 as [H2|H2]. { apply Z.eqb_neq in H2. lia. } apply Z.ltb_ge in H2. lia.
Qed.

Lemma mod9_add9 : forall r, r mod 9 = 0 -> (r + 9) mod 9 = 0.
Proof. intros r H. rewrite <- Z.add_mod_idemp_l by lia. rewrite H. reflexivity. Qed.
Lemma div9_add9 : forall r, (45 - (r + 9)) / 9 = (45 - r) / 9 - 1.
Proof. intros r. replace (45 - (r + 9)) with ((45 - r) + (-1) * 9) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma df_up_body_total : forall s, USI s -> df_up_cond s = true ->
  exists s', df_up_body s = Some s' /\ USI s' /\ 0 <= usm s' < usm s.
Proof.
  intros [rp a z e2 x] (Ha & Hz & Haz & LX & WX & XA & M9 & RR) C. cbn [us_rp us_a us_z us_e2 us_x] in *.
  pose proof (df_up_cond_true _ C) as RP36. cbn [us_rp] in RP36.
  unfold df_up_body. cbn [us_rp us_a us_z us_e2 us_x].
  destruct (df_upk_total a (znth x a) (mkUK (Z.land (z - 1) MASK) 0 z x) Ha) as [[k' carry' z' x'] [E Q]].
  { unfold UKI; cbn. split; [apply land_MASK_range|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact WX|]. split; [exact LX| reflexivity]. }
  rewrite E. destruct Q as [cin (Hcin & WX' & LX' & Hz' & Hza' & Hc' & C1 & C2)]. cbn [uk_carry uk_z uk_x] in *.
  set (tmp := znth x a * 2^29 + cin) in *.
  assert (Q9 : 1 <= (45 - rp) / 9). { apply Z.div_le_lower_bound; lia. }
  destruct (nz carry') eqn:NZ.
  - (* [comment removed for export] *)
    assert (Hc1 : 1 <= carry').
    { unfold nz in NZ. destruct (Z.eqb_spec carry' 0); [discriminate NZ|].
      destruct (Z.lt_ge_cases 1000000000 tmp) as [GT|LE]. 2:{ destruct (C2 LE). lia. } lia. }
    set (a' := Z.land (a - 1) MASK).
    pose proof (land_MASK_range (a - 1)) as Ha'. fold a' in Ha'.
    assert (ZX : exists z'' x'', (let '(z, x) := (if a' =? z'
                   then (Z.land (z' - 1) MASK,
                         zupd x' (Z.land (Z.land (z' - 1) MASK - 1) MASK)
                              (Z.lor (znth x' (Z.land (Z.land (z' - 1) MASK - 1) MASK)) (znth x' (Z.land (z' - 1) MASK))))
                   else (z', x')) in Some (mkUS (rp + 9) a' z (e2 - 29) (zupd x a' carry')))
                 = Some (mkUS (rp + 9) a' z'' (e2 - 29) (zupd x'' a' carry')) /\ 0 <= z'' < 2048 /\ z'' <> a' /\ W32 x'' /\ zlength x'' = KMAX).
    { destruct (Z.eqb_spec a' z') as [EQ|NE].
      - eexists _, _. split; [reflexivity|]. split; [apply land_MASK_range|]. split.
        + rewrite land_MASK_mod. intros E2. rewrite EQ in E2.
          (* [comment removed for export] *)
          destruct (Z.eq_dec z' 0) as [Z0'|Z0']. { rewrite Z0' in E2. cbv in E2. lia. }
          rewrite Z.mod_small in E2; lia.
        + split; [|now rewrite zlength_zupd]. apply W32_zupd; [exact WX'|]. pose proof (WX' (Z.land (Z.land (z' - 1) MASK - 1) MASK)). pose proof (WX' (Z.land (z' - 1) MASK)). apply Z_lor_lt_pow2'; lia.
      - eexists _, _. split; [reflexivity|]. auto. }
    destruct ZX as [z'' [x'' (EZ & Hz'' & Hza'' & WX'' & LX'')]].
    eexists. split; [exact EZ|].
    assert (XA' : znth (zupd x'' a' carry') a' = carry'). { apply znth_zupd_eq. rewrite LX''. unfold KMAX. lia. }
    split.
    + unfold USI; cbn. split; [lia|]. split; [lia|]. split; [lia|]. split; [now rewrite zlength_zupd|]. split; [apply W32_zupd; [exact WX''| lia]|].
      split; [rewrite XA'; lia|]. split; [now apply mod9_add9|]. lia.
    + unfold usm; cbn. rewrite XA'. rewrite div9_add9.
      destruct (carry' <=? 1); destruct (znth x a <=? 1); lia.
  - (* [comment removed for export] *)
    assert (Hc0 : carry' = 0). { unfold nz in NZ. destruct (Z.eqb_spec carry' 0); [assumption| discriminate NZ]. }
    assert (LE : tmp <= 1000000000). { destruct (Z.lt_ge_cases 1000000000 tmp) as [GT|]; [|lia]. specialize (C1 GT). exfalso.
      assert (1 <= tmp / 1000000000) by (apply Z.div_le_lower_bound; lia). lia. }
    destruct (C2 LE) as [_ XA'].
    assert (X1 : znth x a = 1) by (subst tmp; nia).
    eexists. split; [reflexivity|]. split.
    + unfold USI; cbn. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact LX'|]. split; [exact WX'|]. split; [rewrite XA'; subst tmp; rewrite X1; change (1 * 2 ^ 29) with 536870912; lia|]. split; [exact M9| lia].
    + unfold usm; cbn. rewrite XA', X1. replace (tmp <=? 1) with false. 2:{ symmetry. apply Z.leb_gt. subst tmp. rewrite X1. change (1 * 2 ^ 29) with 536870912. lia. } rewrite Z.leb_refl. lia.
Qed.

Lemma df_up_total : forall s, USI s ->
  exists s', df_up_loop FUEL_SCALE s = Some s' /\ USI s' /\ df_up_cond s' = false.
Proof.
  intros s HI. rewrite df_up_loop_eq.
  apply (owloop_total df_up_cond df_up_body USI usm).
  - intros s1 H1 C1. apply df_up_body_total; assumption.
  - exact HI.
  - unfold usm, FUEL_SCALE. change (Z.of_nat 2000) with 2000. destruct HI as (_ & _ & _ & _ & _ & _ & _ & RR).
    assert ((45 - us_rp s) / 9 <= 149) by (apply Z.div_le_upper_bound; lia).
    destruct (_ <=? 1); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition TH0 : Z := 10384593.
Lemma th0_val : znth th_list 0 = TH0. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma df_dni_total : forall a z x, 0 <= a < 2048 -> a <> z ->
  exists i, df_dni_loop 6%nat a z x 0 = Some i /\ 0 <= i <= 4 /\ (i <> 4 -> TH0 <= znth x a).
Proof.
  intros a z x Ha Haz. rewrite df_dni_loop_eq.
  destruct (wbloop_total (fun i => i <? LD_B1B_DIG) (df_dni_body a z x)
             (fun i => 0 <= i <= 4 /\ (1 <= i -> TH0 <= znth x a))
             (fun i => 0 <= i <= 4 /\ (i <> 4 -> TH0 <= znth x a))
             (fun i => 4 - i)) with (fuel := 6%nat) (s := 0) as [i (E & Q)].
  - intros i [Hi Hth] C. apply Z.ltb_lt in C. unfold LD_B1B_DIG in C.
    unfold df_dni_body. unfold LD_B1B_DIG.
    destruct (Z.eq_dec i 0) as [->|NZ].
    + rewrite Z.add_0_r, (land_MASK_small a) by lia. rewrite th0_val.
      destruct (Z.eqb_spec a z); [lia|]. cbn [orb].
      destruct (Z.ltb_spec (znth x a) TH0). { split; [lia| intros; lia]. }
      destruct (Z.ltb_spec TH0 (znth x a)). { split; [lia| intros; lia]. }
      split; [| lia]. split; [lia|]. intros; lia.
    + destruct (_ || _). { split; [lia| intros; lia]. }
      destruct (_ <? _). { split; [lia|]. intros _. apply Hth. lia. }
      split; [|lia]. split; [lia|]. intros _. apply Hth. lia.
  - intros i [Hi Hth] C. apply Z.ltb_ge in C. unfold LD_B1B_DIG in C. split; [lia|]. intros; lia.
  - split; [lia| intros; lia].
  - change (Z.of_nat 6) with 6. lia.
  - exists i. split; [exact E| exact Q].
Qed.

Definition rdz (z i : Z) : Z := (z - i) mod 2048.

Lemma rdz_range : forall z i, 0 <= rdz z i < 2048.
Proof. intros. unfold rdz. apply Z.mod_pos_bound. lia. Qed.
Lemma rdz_zero : forall z i, 0 <= z < 2048 -> 0 <= i < 2048 -> rdz z i = 0 -> i = z.
Proof.
  intros z i Hz Hi H. unfold rdz in H. apply Z.mod_divide in H; [|lia]. destruct H as [q Hq]. assert (q = 0) by lia. lia.
Qed.
Lemma rdz_step_up : forall z k, 0 <= k < 2048 -> 0 <= z < 2048 -> k <> z ->
  rdz z (Z.land (k + 1) MASK) = rdz z k - 1.
Proof.
  intros z k Hk Hz Hne. unfold rdz. rewrite land_MASK_mod.
  rewrite Zminus_mod_idemp_r.
  replace (z - (k + 1)) with (z - k - 1) by lia.
  pose proof (Z.mod_pos_bound (z - k) 2048 ltac:(lia)) as R.
  assert (NZ : (z - k) mod 2048 <> 0). { intros E. apply (rdz_zero z k) in E; lia. }
  rewrite <- (Zminus_mod_idemp_l (z - k) 1 2048). rewrite (Z.mod_small ((z - k) mod 2048 - 1)); lia.
Qed.
Lemma rdz_inj : forall z i j, 0 <= z < 2048 -> 0 <= i < 2048 -> 0 <= j < 2048 -> rdz z i = rdz z j -> i = j.
Proof.
  intros z i j Hz Hi Hj H. unfold rdz in H.
  assert (E : ((z - i) - (z - j)) mod 2048 = 0).
  { rewrite Zminus_mod, H, Z.sub_diag. reflexivity. }
  replace (z - i - (z - j)) with (j - i) in E by lia.
  apply Z.mod_divide in E; [|lia]. destruct E as [q Hq]. assert (q = 0 \/ q = 1 \/ q = -1) by lia. lia.
Qed.

(* [comment removed for export] *)
Definition shok (sh : Z) : Prop := sh = 1 \/ sh = 9.
Lemma sh_facts : forall sh, shok sh ->
  1 <= sh /\ Z.shiftl 1 sh - 1 = Z.ones sh /\ 1 <= Z.shiftr 1000000000 sh /\
  Z.shiftr 1000000000 sh * (2 ^ sh - 1) < 1000000000 /\ 0 < 2 ^ sh <= 512.
Proof.
  intros sh [-> | ->].
  - change (Z.shiftl 1 1 - 1) with (Z.ones 1). change (Z.shiftr 1000000000 1) with 500000000. change (2 ^ 1) with 2.
    repeat split; lia.
  - change (Z.shiftl 1 9 - 1) with (Z.ones 9). change (Z.shiftr 1000000000 9) with 1953125. change (2 ^ 9) with 512.
    repeat split; lia.
Qed.

Lemma land_mask_sh : forall v sh, 0 <= v -> shok sh ->
  Z.land v (Z.shiftl 1 sh - 1) = v mod 2 ^ sh /\ 0 <= Z.land v (Z.shiftl 1 sh - 1) < 2 ^ sh.
Proof.
  intros v sh Hv Hs. destruct (sh_facts sh Hs) as (S1 & S2 & _ & _ & S5). rewrite S2, Z.land_ones by lia.
  split; [reflexivity|]. apply Z.mod_pos_bound. lia.
Qed.

Lemma shiftr_small_mask : forall v sh, 0 <= v -> shok sh -> Z.shiftr v sh = 0 -> Z.land v (Z.shiftl 1 sh - 1) = v.
Proof.
  intros v sh Hv Hs H. destruct (sh_facts sh Hs) as (S1 & S2 & _ & _ & S5).
  destruct (land_mask_sh v sh Hv Hs) as [E _]. rewrite E.
  rewrite Z.shiftr_div_pow2 in H by lia. apply Z.div_small_iff in H; [|lia]. apply Z.mod_small. lia.
Qed.

Lemma shiftr_le : forall v sh, 0 <= v -> 1 <= sh -> 0 <= Z.shiftr v sh <= v / 2.
Proof.
  intros v sh Hv Hs. rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia|].
  apply Z.div_le_compat_l; [lia|]. split; [lia|]. change 2 with (2^1) at 1. apply Z.pow_le_mono_r; lia.
Qed.

Section DnK.
  Variables (a z sh i0 rp0 : Z) (x0 : list Z).
  Let XA := znth x0 a.
  Let a1 := Z.land (a + 1) MASK.
  Hypothesis Ha : 0 <= a < 2048.
  Hypothesis Hz : 0 <= z < 2048.
  Hypothesis Haz : a <> z.
  Hypothesis Hsh : shok sh.
  Hypothesis LX0 : zlength x0 = KMAX.
  Hypothesis WX0 : W32 x0.
  Hypothesis XA1 : 1 <= XA.

  Definition DKI (s : st_dnk) : Prop :=
    W32 (dk_x s) /\ zlength (dk_x s) = KMAX /\ 0 <= dk_carry s < 1000000000 /\ 0 <= dk_k s < 2048 /\
    rdz z (dk_k s) <= rdz z a /\
    ( (dk_a s = a /\ dk_i s = i0 /\ dk_rp s = rp0 /\
       (dk_k s = a -> dk_carry s = 0 /\ dk_x s = x0) /\
       (dk_k s <> a -> znth (dk_x s) a = Z.shiftr XA sh /\ 1 <= znth (dk_x s) a))
    \/ (dk_a s = a1 /\ dk_i s = i0 - 1 /\ dk_rp s = rp0 - 9 /\ dk_k s <> a /\ Z.shiftr XA sh = 0 /\
       (dk_k s = a1 -> 1 <= dk_carry s) /\ (dk_k s <> a1 -> 1 <= znth (dk_x s) a1)) ).

  Lemma a1_range : 0 <= a1 < 2048. Proof. unfold a1. apply land_MASK_range. Qed.
  Lemma a1_ne_a : a1 <> a.
  Proof. unfold a1. rewrite land_MASK_mod. intros E. destruct (Z.eq_dec a 2047) as [->|]; [cbv in E; lia|]. rewrite Z.mod_small in E; lia. Qed.
  Lemma rdz_a1 : rdz z a1 = rdz z a - 1.
  Proof. unfold a1. apply rdz_step_up; lia. Qed.

  Lemma df_dnk_body_k : forall s, dk_k (df_dnk_body z sh s) = Z.land (dk_k s + 1) MASK.
  Proof. intros [k c da di drp x]. unfold df_dnk_body. cbn [dk_k dk_carry dk_a dk_i dk_rp dk_x]. destruct (_ && _); reflexivity. Qed.

  Lemma df_dnk_body_ok : forall s, DKI s -> dk_k s <> z ->
    DKI (df_dnk_body z sh s) /\ 0 <= rdz z (dk_k (df_dnk_body z sh s)) < rdz z (dk_k s).
  Proof.
    intros s HI NE. split.
    2:{ rewrite df_dnk_body_k. destruct HI as (_ & _ & _ & Hk & RD & _).
        rewrite rdz_step_up by lia. pose proof (rdz_range z (dk_k s)).
        destruct (Z.eq_dec (rdz z (dk_k s)) 0) as [E|]; [|lia]. exfalso. apply NE. apply (rdz_zero z); lia. }
    destruct s as [k carry da di drp x]. destruct HI as (WX & LX & Hc & Hk & RD & DIS). cbn [dk_k dk_carry dk_a dk_i dk_rp dk_x] in *.
    destruct (sh_facts sh Hsh) as (S1 & S2 & S3 & S4 & S5).
    pose proof (WX k) as Wk.
    destruct (land_mask_sh (znth x k) sh ltac:(lia) Hsh) as [TM TR].
    pose proof (shiftr_le (znth x k) sh ltac:(lia) S1) as SR.
    unfold df_dnk_body. cbn [dk_k dk_carry dk_a dk_i dk_rp dk_x].
    set (tmp := Z.land (znth x k) (Z.shiftl 1 sh - 1)) in *.
    assert (NV : u32 (Z.shiftr (znth x k) sh + carry) = Z.shiftr (znth x k) sh + carry) by (apply u32_id; lia).
    rewrite NV.
    set (x' := zupd x k (Z.shiftr (znth x k) sh + carry)).
    assert (HM1 : Z.shiftr 1000000000 sh * tmp <= Z.shiftr 1000000000 sh * (2 ^ sh - 1)) by (apply Z.mul_le_mono_nonneg_l; clear - TR S3; lia).
    assert (HM0 : 0 <= Z.shiftr 1000000000 sh * tmp) by (apply Z.mul_nonneg_nonneg; clear - TR S3; lia).
    assert (NC : u32 (Z.shiftr 1000000000 sh * tmp) = Z.shiftr 1000000000 sh * tmp) by (apply u32_id; clear - HM1 HM0 S4; lia).
    rewrite NC. set (carry' := Z.shiftr 1000000000 sh * tmp) in *.
    assert (Hc' : 0 <= carry' < 1000000000) by (subst carry'; clear - HM1 HM0 S4; lia).
    clear HM1 HM0.
    assert (WX' : W32 x') by (subst x'; apply W32_zupd; [exact WX| lia]).
    assert (LX' : zlength x' = KMAX) by (subst x'; now rewrite zlength_zupd).
    assert (Xk : znth x' k = Z.shiftr (znth x k) sh + carry). { subst x'. apply znth_zupd_eq. rewrite LX. unfold KMAX. lia. }
    assert (Xo : forall j, j <> k -> znth x' j = znth x j). { intros j Hj. subst x'. apply znth_zupd_neq. lia. }
    pose proof (rdz_step_up z k Hk Hz NE) as RS. pose proof (rdz_range z k) as RR.
    assert (RDpos : 1 <= rdz z k). { destruct (Z.eq_dec (rdz z k) 0) as [E|]; [|lia]. exfalso. apply NE. apply (rdz_zero z k); lia. }
    set (k' := Z.land (k + 1) MASK) in *. pose proof (land_MASK_range (k + 1)) as Hk'. fold k' in Hk'.
    assert (K'a : k' <> a). { intros E. rewrite <- E in RD. lia. }
    destruct DIS as [(Da & Di & Dr & K1 & K2)|(Da & Di & Dr & Kna & XS & K1 & K2)]; subst da di drp.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec k a) as [->|NEa].
      + destruct (K1 eq_refl) as [-> ->]. rewrite Z.add_0_r in *.
        rewrite Z.eqb_refl. cbn [andb].
        destruct (Z.eqb_spec (znth x' a) 0) as [Z0e|Z0e].
        * (* [comment removed for export] *)
          assert (XS : Z.shiftr XA sh = 0) by (unfold XA; rewrite <- Xk; lia).
          unfold DKI; cbn. split; [exact WX'|]. split; [exact LX'|]. split; [exact Hc'|]. split; [exact Hk'|]. split; [lia|].
          right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact K'a|]. split; [exact XS|].
          split; [| intros NE1; exfalso; apply NE1; reflexivity].
          intros _. subst carry' tmp. pose proof (WX0 a) as W0a.
          rewrite (shiftr_small_mask (znth x0 a) sh ltac:(lia) Hsh XS). change (znth x0 a) with XA. nia.
        * unfold DKI; cbn. split; [exact WX'|]. split; [exact LX'|]. split; [exact Hc'|]. split; [exact Hk'|]. split; [lia|].
          left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros E; exfalso; exact (K'a E)|].
          intros _. rewrite Xk. fold XA. split; [reflexivity|]. pose proof (WX' a) as W'a. rewrite Xk in W'a. fold XA in W'a. rewrite Xk in Z0e. fold XA in Z0e. lia.
      + destruct (K2 NEa) as [E1 E2].
        replace ((k =? a) && (znth x' k =? 0)) with false by (destruct (Z.eqb_spec k a); [lia| reflexivity]).
        unfold DKI; cbn. split; [exact WX'|]. split; [exact LX'|]. split; [exact Hc'|]. split; [exact Hk'|]. split; [lia|].
        left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros E; exfalso; exact (K'a E)|].
        intros _. rewrite Xo by lia. auto.
    - (* [comment removed for export] *)
      pose proof a1_ne_a as A1a. pose proof rdz_a1 as RA1. pose proof a1_range as A1r.
      destruct (Z.eq_dec k a1) as [->|NEa1].
      + specialize (K1 eq_refl). rewrite Z.eqb_refl. cbn [andb].
        assert (NZ' : znth x' a1 <> 0) by (rewrite Xk; lia).
        replace (znth x' a1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ').
        unfold DKI; cbn. split; [exact WX'|]. split; [exact LX'|]. split; [exact Hc'|]. split; [exact Hk'|]. split; [lia|].
        right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact K'a|]. split; [exact XS|].
        split. { intros E. exfalso. (* [comment removed for export] *) subst k'. rewrite land_MASK_mod in E.
                 destruct (Z.eq_dec a1 2047) as [E7|E7]; [rewrite E7 in E; cbv in E; lia| rewrite Z.mod_small in E; lia]. }
        intros _. rewrite Xk. lia.
      + replace ((k =? a1) && (znth x' k =? 0)) with false by (destruct (Z.eqb_spec k a1); [lia| reflexivity]).
        unfold DKI; cbn. split; [exact WX'|]. split; [exact LX'|]. split; [exact Hc'|]. split; [exact Hk'|]. split; [lia|].
        right. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact K'a|]. split; [exact XS|].
        split. { intros E. exfalso. (* [comment removed for export] *)
                 assert (rdz z k = rdz z a) by (rewrite <- E in RA1; lia). apply Kna. apply (rdz_inj z); lia. }
        intros _. rewrite Xo by lia. apply K2. exact NEa1.
  Qed.

  Lemma df_dnk_total :
    exists s', df_dnk_loop FUEL_RING z sh (mkDK a 0 a i0 rp0 x0) = Some s' /\ DKI s' /\ dk_k s' = z.
  Proof.
    rewrite df_dnk_loop_eq.
    destruct (wloop_total (fun s => negb (dk_k s =? z)) (df_dnk_body z sh) DKI (fun s => rdz z (dk_k s)))
      with (fuel := FUEL_RING) (s := mkDK a 0 a i0 rp0 x0) as [s' (E & HI & C)].
    - intros s HI C. apply df_dnk_body_ok; [exact HI|]. destruct (Z.eqb_spec (dk_k s) z); [discriminate C| assumption].
    - unfold DKI; cbn. split; [exact WX0|]. split; [exact LX0|]. split; [lia|]. split; [lia|]. split; [lia|].
      left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [auto|]. intros N; exfalso; exact (N eq_refl).
    - cbn. pose proof (rdz_range z a). unfold FUEL_RING. change (Z.of_nat 2050) with 2050. lia.
    - exists s'. split; [exact E|]. split; [exact HI|]. destruct (Z.eqb_spec (dk_k s') z); [assumption| discriminate C].
  Qed.
End DnK.

Definition DSI (s : st_dn) : Prop :=
  0 <= ds_a s < 2048 /\ 0 <= ds_z s < 2048 /\ ds_a s <> ds_z s /\ zlength (ds_x s) = KMAX /\ W32 (ds_x s) /\
  1 <= znth (ds_x s) (ds_a s) /\ ds_rp s mod 9 = 0 /\ 36 <= ds_rp s <= 540.

Definition dsm (s : st_dn) : Z := 33 * ((ds_rp s - 36) / 9) + bitlen (znth (ds_x s) (ds_a s)).

Lemma bitlen_lor1 : forall v, 1 <= v -> bitlen (Z.lor v 1) = bitlen v.
Proof.
  intros v Hv. unfold bitlen.
  assert (1 <= Z.lor v 1). { pose proof (Z.lor_nonneg v 1). destruct (Z.eq_dec (Z.lor v 1) 0) as [E|]; [|lia]. apply Z.lor_eq_0_iff in E. lia. }
  destruct (Z.ltb_spec 0 (Z.lor v 1)); [|lia]. destruct (Z.ltb_spec 0 v); [|lia].
  rewrite Z.log2_lor by lia. change (Z.log2 1) with 0. pose proof (Z.log2_nonneg v). rewrite Z.max_l by lia. reflexivity.
Qed.

Lemma mod9_sub9 : forall r, r mod 9 = 0 -> (r - 9) mod 9 = 0.
Proof. intros r H. replace (r - 9) with (r + (-1) * 9) by lia. rewrite Z.mod_add by lia. exact H. Qed.

Lemma df_dn_body_total : forall s, DSI s ->
  exists r, df_dn_body s = Some r /\
    match r with inl s' => DSI s' /\ 0 <= dsm s' < dsm s | inr s' => True end.
Proof.
  intros [rp a z e2 x i] (Ha & Hz & Haz & LX & WX & XA & M9 & RR). cbn [ds_rp ds_a ds_z ds_e2 ds_x ds_i] in *.
  unfold df_dn_body. cbn [ds_rp ds_a ds_z ds_e2 ds_x ds_i].
  destruct (df_dni_total a z x Ha Haz) as [i1 (E1 & Hi1 & TH)]. rewrite E1.
  change LD_B1B_DIG with 4.
  destruct ((i1 =? 4) && (rp =? 9 * 4)) eqn:EX.
  { eexists. split; [reflexivity|]. exact I. }
  set (sh := if 9 + 9 * 4 <? rp then 9 else 1).
  assert (Hsh : shok sh). { subst sh. destruct (_ <? _); [right|left]; reflexivity. }
  destruct (sh_facts sh Hsh) as (S1 & S2 & S3 & S4 & S5).
  destruct (df_dnk_total a z sh i1 rp x Ha Hz Haz Hsh LX WX XA) as [[k' carry' a' i' rp' x'] (E2 & HI2 & K2)].
  rewrite E2. cbn [dk_k] in K2. subst k'.
  destruct HI2 as (WX' & LX' & Hc' & _ & _ & DIS). cbn [dk_x dk_carry dk_k dk_a dk_i dk_rp] in *.
  (* [comment removed for export] *)
  assert (RP45 : Z.shiftr (znth x a) sh = 0 -> 45 <= rp).
  { intros XS. destruct (Z.eq_dec rp 36) as [E36|NE36].
    - exfalso. subst rp. assert (i1 <> 4). { intros ->. cbn in EX. discriminate EX. }
      specialize (TH H). unfold TH0 in TH.
      assert (sh = 1) by (subst sh; reflexivity). rewrite H0 in XS. rewrite Z.shiftr_div_pow2 in XS by lia.
      change (2^1) with 2 in XS. apply Z.div_small_iff in XS; lia.
    - (* [comment removed for export] *)
      assert (exists q, rp = 9 * q) as [q Hq]. { exists (rp / 9). pose proof (Z.div_mod rp 9 ltac:(lia)). lia. }
      subst rp. lia. }
  set (app := if nz carry' then (if negb (Z.land (z + 1) MASK =? a') then (Z.land (z + 1) MASK, zupd x' z carry')
                                 else (z, zupd x' (Z.land (z - 1) MASK) (Z.lor (znth x' (Z.land (z - 1) MASK)) 1)))
              else (z, x')).
  assert (APP : exists z'' x'', app = (z'', x'') /\ 0 <= z'' < 2048 /\ zlength x'' = KMAX /\ W32 x'' /\
       z'' <> a' /\
       (forall j, j <> z -> j <> Z.land (z - 1) MASK -> znth x'' j = znth x' j) /\
       (a' = z -> 1 <= carry' -> znth x'' a' = carry' /\ z'' <> z) /\
       (znth x'' (Z.land (z - 1) MASK) = znth x' (Z.land (z - 1) MASK) \/ znth x'' (Z.land (z - 1) MASK) = Z.lor (znth x' (Z.land (z - 1) MASK)) 1)).
  { assert (Ha' : 0 <= a' < 2048 /\ (a' = a \/ a' = Z.land (a + 1) MASK)).
    { destruct DIS as [(-> & _)|(-> & _)]; [split; [lia| now left]| split; [apply land_MASK_range| now right]]. }
    destruct Ha' as [Ha'r Ha'c]. subst app.
    destruct (nz carry') eqn:NZ.
    - destruct (Z.eqb_spec (Z.land (z + 1) MASK) a') as [EQ|NE]; cbn [negb].
      + eexists _, _. split; [reflexivity|]. split; [lia|]. split; [now rewrite zlength_zupd|].
        split. { apply W32_zupd; [exact WX'|]. pose proof (WX' (Z.land (z - 1) MASK)). apply Z_lor_lt_pow2'; lia. }
        split. { intros E. rewrite <- E in EQ. rewrite land_MASK_mod in EQ. destruct (Z.eq_dec z 2047) as [E7|E7]; [rewrite E7 in EQ; cbv in EQ; lia| rewrite Z.mod_small in EQ; lia]. }
        split. { intros j H1 H2. rewrite znth_zupd_neq by lia. reflexivity. }
        split. { intros E _. exfalso. rewrite E in EQ. rewrite land_MASK_mod in EQ. destruct (Z.eq_dec z 2047) as [E7|E7]; [rewrite E7 in EQ; cbv in EQ; lia| rewrite Z.mod_small in EQ; lia]. }
        right. apply znth_zupd_eq. rewrite LX'. unfold KMAX. pose proof (land_MASK_range (z - 1)). lia.
      + eexists _, _. split; [reflexivity|]. split; [apply land_MASK_range|]. split; [now rewrite zlength_zupd|].
        split. { apply W32_zupd; [exact WX'| lia]. }
        split. { intros E. apply NE. rewrite E. reflexivity. }
        split. { intros j H1 H2. rewrite znth_zupd_neq by lia. reflexivity. }
        split. { intros E C1. split. { rewrite <- E. apply znth_zupd_eq. rewrite LX'. unfold KMAX. lia. }
                 rewrite land_MASK_mod. destruct (Z.eq_dec z 2047) as [E7|E7]; [rewrite E7; cbv; lia| rewrite Z.mod_small; lia]. }
        left. rewrite znth_zupd_neq; [reflexivity|]. rewrite land_MASK_mod. destruct (Z.eq_dec z 0) as [E0|E0]; [rewrite E0; cbv; lia| rewrite Z.mod_small; lia].
    - assert (carry' = 0) as C0. { unfold nz in NZ. destruct (Z.eqb_spec carry' 0); [assumption| discriminate NZ]. }
      eexists _, _. split; [reflexivity|]. split; [lia|]. split; [exact LX'|]. split; [exact WX'|].
      split. { destruct DIS as [(-> & _)|(-> & _ & _ & _ & _ & K1 & _)]; [lia|]. intros E. specialize (K1 E). lia. }
      split; [intros; reflexivity|]. split; [intros; lia| now left]. }
  destruct APP as [z'' [x'' (EA & Hz'' & LX'' & WX'' & ZA & OTH & APZ & LST)]].
  rewrite EA. cbn iota beta. eexists. split; [reflexivity|]. cbn [ds_rp ds_a ds_x].
  destruct DIS as [(-> & -> & -> & K1 & K2)|(-> & -> & -> & Kna & XS & K1 & K2)].
  - (* [comment removed for export] *)
    destruct (K2 ltac:(lia)) as [XE X1].
    assert (XX : znth x'' a = znth x' a \/ znth x'' a = Z.lor (znth x' a) 1).
    { destruct (Z.eq_dec a (Z.land (z - 1) MASK)) as [E|E].
      - rewrite <- E in LST. exact LST.
      - left. apply OTH; lia. }
    assert (BL : bitlen (znth x'' a) = bitlen (znth x' a) /\ 1 <= znth x'' a).
    { destruct XX as [-> | ->]; [split; [reflexivity| lia]|]. split; [apply bitlen_lor1; lia|].
      pose proof (Z.lor_nonneg (znth x' a) 1). destruct (Z.eq_dec (Z.lor (znth x' a) 1) 0) as [E0|]; [|lia]. apply Z.lor_eq_0_iff in E0. lia. }
    destruct BL as [BL X1''].
    split.
    + unfold DSI; cbn. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact LX''|]. split; [exact WX''|]. split; [exact X1''|]. split; [exact M9| lia].
    + unfold dsm; cbn. rewrite BL, XE. pose proof (bitlen_shiftr_lt (znth x a) sh ltac:(lia) S1). pose proof (bitlen_nonneg (Z.shiftr (znth x a) sh)).
      assert (0 <= (rp - 36) / 9) by (apply Z.div_pos; lia). lia.
  - (* [comment removed for export] *)
    specialize (RP45 XS).
    set (a1 := Z.land (a + 1) MASK) in *. pose proof (land_MASK_range (a + 1)) as A1r. fold a1 in A1r.
    assert (X1'' : 1 <= znth x'' a1).
    { destruct (Z.eq_dec a1 z) as [E|E].
      - specialize (K1 (eq_sym E)). destruct (APZ E K1) as [-> _]. exact K1.
      - specialize (K2 (fun H => E (eq_sym H))). destruct (Z.eq_dec a1 (Z.land (z - 1) MASK)) as [E3|E3].
        + rewrite E3 in K2 |- *. destruct LST as [-> | ->]; [exact K2|].
          pose proof (Z.lor_nonneg (znth x' (Z.land (z - 1) MASK)) 1). destruct (Z.eq_dec (Z.lor (znth x' (Z.land (z - 1) MASK)) 1) 0) as [E0|]; [|lia]. apply Z.lor_eq_0_iff in E0. lia.
        + rewrite OTH by lia. exact K2. }
    split.
    + unfold DSI; cbn. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact LX''|]. split; [exact WX''|]. split; [exact X1''|]. split; [now apply mod9_sub9| lia].
    + unfold dsm; cbn.
      replace ((rp - 9 - 36) / 9) with ((rp - 36) / 9 - 1). 2:{ replace (rp - 9 - 36) with ((rp - 36) + (-1) * 9) by lia. rewrite Z.div_add by lia. lia. }
      pose proof (bitlen_le32 (znth x'' a1) (WX'' a1)). pose proof (bitlen_pos (znth x a) ltac:(lia)). pose proof (bitlen_nonneg (znth x'' a1)).
      assert (1 <= (rp - 36) / 9) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma df_dn_total : forall s, DSI s -> exists s', df_dn_loop FUEL_SCALE s = Some s'.
Proof.
  intros s HI. rewrite df_dn_loop_eq.
  destruct (obloop_total df_dn_body DSI (fun _ => True) dsm) with (fuel := FUEL_SCALE) (s := s) as [s' [E _]].
  - intros s1 H1. apply df_dn_body_total. exact H1.
  - exact HI.
  - unfold dsm, FUEL_SCALE. change (Z.of_nat 2000) with 2000.
    destruct HI as (_ & _ & _ & _ & WX & XA & _ & RR).
    pose proof (bitlen_le32 _ (WX (ds_a s))). pose proof (bitlen_nonneg (znth (ds_x s) (ds_a s))).
    assert (0 <= (ds_rp s - 36) / 9 <= 56). { split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]. }
    lia.
  - exists s'. exact E.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma df_asm_total : forall a s, 0 <= as_i s <= 4 -> exists s', df_asm_loop 5%nat a s = Some s' /\ as_i s' = 4.
Proof.
  intros a s Hi. rewrite df_asm_loop_eq.
  destruct (wloop_total (fun s => as_i s <? LD_B1B_DIG) (df_asm_body a) (fun s => 0 <= as_i s <= 4) (fun s => 4 - as_i s))
    with (fuel := 5%nat) (s := s) as [s' (E & R & C)].
  - intros [i y z x] R1 C1. cbn [as_i] in *. apply Z.ltb_lt in C1. unfold LD_B1B_DIG in C1.
    unfold df_asm_body. cbn [as_i as_y as_z as_x]. destruct (_ =? _); cbn [as_i]; lia.
  - exact Hi.
  - change (Z.of_nat 5) with 5. lia.
  - exists s'. split; [exact E|]. apply Z.ltb_ge in C. unfold LD_B1B_DIG in C. lia.
Qed.

Ltac tot_step :=
  first [ congruence
        | match goal with |- context [match m_fmodl ?a ?b with _ => _ end] =>
            destruct (m_fmodl a b) eqn:?F; [clear F| exfalso; exact (m_fmodl_total _ _ F)] end
        | match goal with |- context [if ?c then _ else _] => destruct c end
        | match goal with |- context [match ?p with pair _ _ => _ end] => destruct p end ].

Lemma df_final_total : forall a z x e2 bits emin sign emax frac bias,
  df_final a z x e2 bits emin sign emax frac bias <> None.
Proof.
  intros. unfold df_final.
  destruct (df_asm_total a (mkAS 0 (f128_of_i32 0) z x) ltac:(cbn; lia)) as [[i y z' x'] [E Hi]]. rewrite E.
  cbv beta iota zeta. repeat (tot_step; cbv beta iota zeta).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma df_p4_total : df_p4_total_stmt.
Proof.
  intros f z rp x sign emax frac bias (Hz & LX & WX & X0 & Hrp).
  assert (HzK : 1 <= z <= 2046) by (unfold KMAX in Hz; lia).
  change (10 ^ 8) with 100000000 in X0. change (10 ^ 9) with 1000000000 in X0.
  unfold df_p4.
  destruct (df_tz_total x z Hz ltac:(lia)) as [z1 [E1 Hz1]]. rewrite E1.
  (* [comment removed for export] *)
  set (al := if nz (Z.rem rp 9) then _ else _).
  assert (AL : exists z2 rp2 x2, al = Some (0, z2, rp2, x2) /\ 1 <= z2 < 2048 /\ zlength x2 = KMAX /\ W32 x2 /\
               1 <= znth x2 0 /\ rp2 mod 9 = 0 /\ -1296 <= rp2 <= 540).
  { subst al. pose proof (Z.quot_rem' rp 9) as QR.
    destruct (nz (Z.rem rp 9)) eqn:NZ.
    - assert (RNZ : Z.rem rp 9 <> 0). { unfold nz in NZ. destruct (Z.eqb_spec (Z.rem rp 9) 0); [discriminate NZ| assumption]. }
      cbv zeta.
      set (rpm9 := if 0 <=? rp then Z.rem rp 9 else Z.rem rp 9 + 9).
      assert (RM : 1 <= rpm9 <= 8 /\ (rp + (9 - rpm9)) mod 9 = 0 /\ -1296 <= rp + (9 - rpm9) <= 540).
      { subst rpm9. destruct (Z.leb_spec 0 rp).
        - pose proof (Z.rem_bound_pos rp 9 ltac:(lia) ltac:(lia)).
          split; [lia|]. split; [| nia].
          replace (rp + (9 - Z.rem rp 9)) with ((rp ÷ 9 + 1) * 9) by lia. apply Z.mod_mul. lia.
        - pose proof (Z.rem_bound_pos_neg rp 9 ltac:(lia) ltac:(lia)).
          split; [lia|]. split; [| nia].
          replace (rp + (9 - (Z.rem rp 9 + 9))) with ((rp ÷ 9) * 9) by lia. apply Z.mod_mul. lia. }
      destruct RM as (R1 & R2 & R3).
      assert (P10 : 10 <= znth p10s (8 - rpm9) <= 10 ^ 8).
      { rewrite p10s_val by lia. replace (8 - rpm9 + 1) with (9 - rpm9) by lia.
        split. { change 10 with (10 ^ 1) at 1. apply Z.pow_le_mono_r; lia. } apply Z.pow_le_mono_r; lia. }
      destruct (df_al_total (znth p10s (8 - rpm9)) z1 rp x ltac:(lia) LX WX ltac:(lia) P10) as [[k2 a2 rp2 carry2 x2] (E2 & HI2 & K2)].
      rewrite E2. destruct HI2 as (A2 & _ & RP2 & C2 & W2 & L2 & _ & X2). cbn [al_k al_a al_rp al_carry al_x] in *. subst a2 rp2 k2.
      specialize (X2 ltac:(lia)).
      destruct (nz carry2).
      + eexists _, _, _. split; [reflexivity|]. split; [lia|]. split; [now rewrite zlength_zupd|]. split; [apply W32_zupd; [exact W2| lia]|].
        split; [rewrite znth_zupd_neq by lia; exact X2|]. split; [exact R2| exact R3].
      + eexists _, _, _. split; [reflexivity|]. split; [lia|]. split; [exact L2|]. split; [exact W2|]. split; [exact X2|]. split; [exact R2| exact R3].
    - assert (RZ : Z.rem rp 9 = 0). { unfold nz in NZ. destruct (Z.eqb_spec (Z.rem rp 9) 0); [assumption| discriminate NZ]. }
      eexists _, _, _. split; [reflexivity|]. split; [lia|]. split; [exact LX|]. split; [exact WX|]. split; [lia|].
      split; [apply (proj1 (Z.rem_mod_eq_0 rp 9 ltac:(lia))); exact RZ| nia]. }
  destruct AL as [z2 [rp2 [x2 (-> & Hz2 & L2 & W2 & X2 & M2 & R2)]]].
  (* [comment removed for export] *)
  destruct (df_up_total (mkUS rp2 0 z2 0 x2)) as [[rp3 a3 z3 e3 x3] (E3 & HI3 & C3)].
  { unfold USI; cbn. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact L2|]. split; [exact W2|]. split; [exact X2|]. split; [exact M2| exact R2]. }
  rewrite E3. destruct HI3 as (Ha3 & Hz3 & Haz3 & L3 & W3 & X3 & M3 & R3). cbn [us_rp us_a us_z us_e2 us_x] in *.
  pose proof (df_up_cond_false _ C3) as [RP36 _]. cbn [us_rp] in RP36.
  (* [comment removed for export] *)
  destruct (df_dn_total (mkDS rp3 a3 z3 e3 x3 0)) as [[rp4 a4 z4 e4 x4 i4] E4].
  { unfold DSI; cbn. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact L3|]. split; [exact W3|]. split; [exact X3|]. split; [exact M3| lia]. }
  rewrite E4.
  destruct (df_final a4 z4 x4 e4 53 (-1074) sign emax frac bias) eqn:EF.
  - eexists; reflexivity.
  - exfalso. exact (df_final_total _ _ _ _ _ _ _ _ _ _ EF).
Qed.

Theorem decfloat_total_all : forall fuelc f c sign pok,
  sh_wf f -> BB f -> bchar c -> (contc c -> sh_rpos f <= sh_N f) -> 0 <= sh_rpos f ->
  zlength (sh_buf f) + 2 <= Z.of_nat fuelc ->
  (sh_stdio f = false -> sh_cnt0 f + 1 <= sh_rpos f) ->
  exists f' y, decfloat fuelc f c 53 (-1074) sign pok = Some (f', y)
    /\ sh_wf f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f
    /\ (sh_stdio f = false -> sh_cnt0 f' <= sh_rpos f').
Proof. apply decfloat_total. apply df_p2_total. apply df_p3_total. apply df_p4_total. Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nonstdio_read : forall f c f', sh_wf f -> sh_stdio f = false -> sh_getc f = (c, f') -> sh_rpos f' = sh_rpos f + 1.
Proof.
  intros f c f' W S G. destruct (sh_getc_facts f c f' G W) as (_ & _ & _ & _ & _ & _ & _ & _ & SH).
  destruct SH as [(_ & _ & _ & S')|(_ & E & _)]; [congruence| exact E].
Qed.

Lemma m_isspace_cont : forall c, m_isspace c = true -> contc c.
Proof.
  intros c H. unfold m_isspace in H. apply orb_prop in H. unfold contc. destruct H as [H|H].
  - apply Z.eqb_eq in H. lia.
  - apply Z.ltb_lt in H. unfold u32 in H. split; intros ->; cbv in H; discriminate.
Qed.

Lemma fs_ws_total : forall fuel f,
  sh_wf f -> BB f -> 0 <= sh_rpos f -> zlength (sh_buf f) + 2 <= Z.of_nat fuel ->
  exists c f', fs_ws_loop fuel f = Some (c, f') /\ sh_wf f' /\ sh_same f f' /\ bchar c /\ m_isspace c = false
    /\ sh_rpos f <= sh_rpos f' /\ (contc c -> sh_rpos f' <= sh_N f')
    /\ (sh_stdio f = false -> sh_rpos f + 1 <= sh_rpos f') /\ (contc c -> sh_rpos f + 1 <= sh_rpos f')
    /\ (sh_shlim_neg f' = true \/ sh_rpos f + 1 <= sh_rpos f').
Proof.
  intros fuel f W HB R FU. pose proof (sh_N_le f W) as NL. assert (LNN : 0 <= zlength (sh_buf f)) by (unfold zlength; lia). rewrite fs_ws_loop_eq.
  destruct (bloop_total (fun f0 => let '(c, f') := sh_getc f0 in if m_isspace c then inl f' else inr (c, f'))
    (fun g => sh_wf g /\ sh_same f g /\ sh_rpos f <= sh_rpos g)
    (fun r => let '(c, f') := r in sh_wf f' /\ sh_same f f' /\ bchar c /\ m_isspace c = false
       /\ sh_rpos f <= sh_rpos f' /\ (contc c -> sh_rpos f' <= sh_N f') /\ (sh_stdio f = false -> sh_rpos f + 1 <= sh_rpos f')
       /\ (contc c -> sh_rpos f + 1 <= sh_rpos f') /\ (sh_shlim_neg f' = true \/ sh_rpos f + 1 <= sh_rpos f'))
    (fun g => Z.max 0 (sh_N g - sh_rpos g + 1))) with (fuel := fuel) (s := f) as [[c f'] [E Q]].
  - intros g (Wg & Sg & Rg). destruct (sh_getc g) as [c g'] eqn:G.
    destruct (sh_getc_facts g c g' G Wg) as (W' & B' & S' & C0' & N' & n' & RP' & CT' & SH').
    assert (BBg : BB g). { intros i. destruct Sg as (Bg & _). rewrite Bg. apply HB. }
    pose proof (getc_bchar g c g' BBg Wg G) as BC.
    destruct (m_isspace c) eqn:SP.
    + pose proof (m_isspace_cont c SP) as CC. destruct (CT' CC) as [E1 L1].
      split. { split; [exact W'|]. split; [eapply sh_same_trans; [exact Sg| eapply sh_same_getc; eauto]| lia]. }
      rewrite N'. lia.
    + split; [exact W'|]. split; [eapply sh_same_trans; [exact Sg| eapply sh_same_getc; eauto]|]. split; [exact BC|]. split; [exact SP|].
      split; [lia|]. split. { intros CC. destruct (CT' CC). rewrite N'. lia. }
      split. { intros ST. destruct Sg as (_ & Sst & _). rewrite (nonstdio_read g c g' Wg ltac:(congruence) G). lia. }
      split. { intros CC. destruct (CT' CC). lia. }
      destruct SH' as [(_ & _ & L & _)|(_ & E & _)]; [left; exact L| right; lia].
  - split; [exact W|]. split; [apply sh_same_refl| lia].
  - lia.
  - exists c, f'. split; [exact E| exact Q].
Qed.

Lemma lor32_eq_cont : forall c v, 97 <= v -> (Z.lor c 32 =? v) = true -> contc c.
Proof.
  intros c v Hv H. apply Z.eqb_eq in H. unfold contc. split; intros ->; cbv in H; lia.
Qed.

Lemma str_infinity_ge : forall i, 0 <= i < 8 -> 97 <= znth str_infinity i.
Proof.
  intros i Hi. assert (H : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct H as [-> |[-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]]; vm_compute; intros HH; discriminate HH.
Qed.
Lemma str_nan_ge : forall i, 0 <= i < 3 -> 97 <= znth str_nan i.
Proof. intros i Hi. assert (H : i = 0 \/ i = 1 \/ i = 2) by lia. destruct H as [-> |[-> | ->]]; vm_compute; intros HH; discriminate HH. Qed.

(* [comment removed for export] *)
Definition PFI (f0 : shfile) (lim : Z) (st : Z * Z * shfile) : Prop :=
  let '(i, c, f) := st in
  0 <= i <= lim /\ sh_wf f /\ sh_same f0 f /\ bchar c /\ (contc c -> sh_rpos f <= sh_N f) /\ sh_rpos f0 <= sh_rpos f
  /\ (sh_stdio f0 = false -> sh_rpos f = sh_rpos f0 + Z.min i (lim - 1)).

Lemma fs_inf_total : forall f c,
  sh_wf f -> BB f -> bchar c -> (contc c -> sh_rpos f <= sh_N f) ->
  exists st, fs_inf_loop 9%nat (0, c, f) = Some st /\ PFI f 8 st /\ fs_inf_cond st = false.
Proof.
  intros f c W HB BC CI. rewrite fs_inf_loop_eq.
  apply (wloop_total fs_inf_cond fs_inf_body (PFI f 8) (fun st => let '(i, _, _) := st in 8 - i)).
  - intros [[i c1] f1] (Hi & W1 & S1 & B1 & CI1 & R1 & NS1) C1.
    unfold fs_inf_cond in C1. apply andb_prop in C1. destruct C1 as [C1a C1b]. apply Z.ltb_lt in C1a.
    pose proof (lor32_eq_cont c1 _ (str_infinity_ge i ltac:(lia)) C1b) as CC. specialize (CI1 CC).
    unfold fs_inf_body. destruct (Z.ltb_spec i 7).
    + destruct (sh_getc f1) as [c2 f2] eqn:G.
      destruct (sh_getc_facts f1 c2 f2 G W1) as (W' & B' & S' & C0' & N' & n' & RP' & CT' & SH').
      assert (BB1 : BB f1). { intros j. destruct S1 as (Bg & _). rewrite Bg. apply HB. }
      split; [|lia]. unfold PFI. split; [lia|]. split; [exact W'|]. split; [eapply sh_same_trans; [exact S1| eapply sh_same_getc; eauto]|].
      split; [eapply getc_bchar; eauto|]. split; [intros CC2; destruct (CT' CC2); rewrite N'; lia|]. split; [lia|].
      intros ST. destruct S1 as (_ & Sst & _). rewrite (nonstdio_read f1 c2 f2 W1 ltac:(congruence) G), (NS1 ST). lia.
    + split; [|lia]. unfold PFI. split; [lia|]. split; [exact W1|]. split; [exact S1|]. split; [exact B1|]. split; [intros _; exact CI1|]. split; [lia|].
      intros ST. rewrite (NS1 ST). lia.
  - unfold PFI. split; [lia|]. split; [exact W|]. split; [apply sh_same_refl|]. split; [exact BC|]. split; [exact CI|]. split; [lia|]. intros; lia.
  - change (Z.of_nat 9) with 9. lia.
Qed.

Lemma fs_nan_total : forall f c,
  sh_wf f -> BB f -> bchar c -> (contc c -> sh_rpos f <= sh_N f) ->
  exists st, fs_nan_loop 4%nat (0, c, f) = Some st /\ PFI f 3 st /\ fs_nan_cond st = false.
Proof.
  intros f c W HB BC CI. rewrite fs_nan_loop_eq.
  apply (wloop_total fs_nan_cond fs_nan_body (PFI f 3) (fun st => let '(i, _, _) := st in 3 - i)).
  - intros [[i c1] f1] (Hi & W1 & S1 & B1 & CI1 & R1 & NS1) C1.
    unfold fs_nan_cond in C1. apply andb_prop in C1. destruct C1 as [C1a C1b]. apply Z.ltb_lt in C1a.
    pose proof (lor32_eq_cont c1 _ (str_nan_ge i ltac:(lia)) C1b) as CC. specialize (CI1 CC).
    unfold fs_nan_body. destruct (Z.ltb_spec i 2).
    + destruct (sh_getc f1) as [c2 f2] eqn:G.
      destruct (sh_getc_facts f1 c2 f2 G W1) as (W' & B' & S' & C0' & N' & n' & RP' & CT' & SH').
      assert (BB1 : BB f1). { intros j. destruct S1 as (Bg & _). rewrite Bg. apply HB. }
      split; [|lia]. unfold PFI. split; [lia|]. split; [exact W'|]. split; [eapply sh_same_trans; [exact S1| eapply sh_same_getc; eauto]|].
      split; [eapply getc_bchar; eauto|]. split; [intros CC2; destruct (CT' CC2); rewrite N'; lia|]. split; [lia|].
      intros ST. destruct S1 as (_ & Sst & _). rewrite (nonstdio_read f1 c2 f2 W1 ltac:(congruence) G), (NS1 ST). lia.
    + split; [|lia]. unfold PFI. split; [lia|]. split; [exact W1|]. split; [exact S1|]. split; [exact B1|]. split; [intros _; exact CI1|]. split; [lia|].
      intros ST. rewrite (NS1 ST). lia.
  - unfold PFI. split; [lia|]. split; [exact W|]. split; [apply sh_same_refl|]. split; [exact BC|]. split; [exact CI|]. split; [lia|]. intros; lia.
  - change (Z.of_nat 4) with 4. lia.
Qed.

(* [comment removed for export] *)
Lemma alnum_cont : forall c, (u32 (c - 48) <? 10) || (u32 (c - 65) <? 26) || (u32 (c - 97) <? 26) || (c =? 95) = true -> contc c.
Proof.
  intros c H. unfold contc. split; intros ->; cbv in H; discriminate.
Qed.

Lemma fs_par_total : forall fuel f,
  sh_wf f -> BB f -> 0 <= sh_rpos f -> zlength (sh_buf f) + 2 <= Z.of_nat fuel ->
  exists i c f', fs_par_loop fuel (1, f) = Some (i, c, f') /\ sh_wf f' /\ sh_same f f' /\ bchar c /\ 1 <= i
    /\ sh_rpos f <= sh_rpos f' /\ (sh_stdio f = false -> sh_rpos f' = sh_rpos f + i).
Proof.
  intros fuel f W HB R FU. pose proof (sh_N_le f W) as NL. assert (LNN : 0 <= zlength (sh_buf f)) by (unfold zlength; lia). rewrite fs_par_loop_eq.
  destruct (bloop_total fs_par_body
    (fun st => let '(i, g) := st in 1 <= i /\ sh_wf g /\ sh_same f g /\ sh_rpos f <= sh_rpos g /\ (sh_stdio f = false -> sh_rpos g = sh_rpos f + i - 1))
    (fun r => let '(i, c, f') := r in sh_wf f' /\ sh_same f f' /\ bchar c /\ 1 <= i /\ sh_rpos f <= sh_rpos f' /\ (sh_stdio f = false -> sh_rpos f' = sh_rpos f + i))
    (fun st => let '(i, g) := st in Z.max 0 (sh_N g - sh_rpos g + 1))) with (fuel := fuel) (s := (1, f)) as [[[i c] f'] [E Q]].
  - intros [i g] (Hi & Wg & Sg & Rg & NSg). unfold fs_par_body.
    destruct (sh_getc g) as [c g'] eqn:G.
    destruct (sh_getc_facts g c g' G Wg) as (W' & B' & S' & C0' & N' & n' & RP' & CT' & SH').
    assert (BBg : BB g). { intros j. destruct Sg as (Bg & _). rewrite Bg. apply HB. }
    pose proof (getc_bchar g c g' BBg Wg G) as BC.
    destruct (_ || _ || _ || _) eqn:AN.
    + pose proof (alnum_cont c AN) as CC. destruct (CT' CC) as [E1 L1].
      split. { split; [lia|]. split; [exact W'|]. split; [eapply sh_same_trans; [exact Sg| eapply sh_same_getc; eauto]|]. split; [lia|]. intros ST. rewrite E1, (NSg ST). lia. }
      rewrite N'. lia.
    + split; [exact W'|]. split; [eapply sh_same_trans; [exact Sg| eapply sh_same_getc; eauto]|]. split; [exact BC|]. split; [lia|]. split; [lia|].
      intros ST. destruct Sg as (_ & Sst & _). rewrite (nonstdio_read g c g' Wg ltac:(congruence) G), (NSg ST). lia.
  - split; [lia|]. split; [exact W|]. split; [apply sh_same_refl|]. split; [lia|]. intros; lia.
  - lia.
  - exists i, c, f'. split; [exact E| exact Q].
Qed.

Lemma fs_inf_loop_mono : forall k i c g i' c' g', fs_inf_loop k (i, c, g) = Some (i', c', g') -> i <= i'.
Proof.
  induction k as [|k IH]; intros i c g i' c' g' H; [discriminate H|]. cbn [fs_inf_loop] in H.
  destruct (fs_inf_cond (i, c, g)).
    match type of H with fs_inf_loop k ?st = _ => destruct st as [[i1 c1] g1] eqn:EB end.
    apply IH in H. unfold fs_inf_body in EB. destruct (i <? 7); [destruct (sh_getc g)|]; inversion EB; subst; lia.
  - inversion H; subst; lia.
Qed.
Lemma fs_inf_loop_i0 : forall k c g c' g', fs_inf_loop k (0, c, g) = Some (0, c', g') -> c' = c /\ g' = g.
Proof.
  intros k c g c' g' H. destruct k as [|k]; [discriminate H|]. cbn [fs_inf_loop] in H.
  destruct (fs_inf_cond (0, c, g)).
  - match type of H with fs_inf_loop k ?st = _ => destruct st as [[i1 c1] g1] eqn:EB end.
    apply fs_inf_loop_mono in H. unfold fs_inf_body in EB. destruct (0 <? 7); [destruct (sh_getc g)|]; inversion EB; subst; lia.
  - inversion H; subst; auto.
Qed.
Lemma fs_nan_loop_mono : forall k i c g i' c' g', fs_nan_loop k (i, c, g) = Some (i', c', g') -> i <= i'.
Proof.
  induction k as [|k IH]; intros i c g i' c' g' H; [discriminate H|]. cbn [fs_nan_loop] in H.
  destruct (fs_nan_cond (i, c, g)).
  - match type of H with fs_nan_loop k ?st = _ => destruct st as [[i1 c1] g1] eqn:EB end.
    apply IH in H. unfold fs_nan_body in EB. destruct (i <? 2); [destruct (sh_getc g)|]; inversion EB; subst; lia.
  - inversion H; subst; lia.
Qed.
Lemma fs_nan_loop_i0 : forall k c g c' g', fs_nan_loop k (0, c, g) = Some (0, c', g') -> c' = c /\ g' = g.
Proof.
  intros k c g c' g' H. destruct k as [|k]; [discriminate H|]. cbn [fs_nan_loop] in H.
  destruct (fs_nan_cond (0, c, g)).
  - match type of H with fs_nan_loop k ?st = _ => destruct st as [[i1 c1] g1] eqn:EB end.
    apply fs_nan_loop_mono in H. unfold fs_nan_body in EB. destruct (0 <? 2); [destruct (sh_getc g)|]; inversion EB; subst; lia.
  - inversion H; subst; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition NX (f : shfile) : Prop := forall i, znth (sh_buf f) i <> 120 /\ znth (sh_buf f) i <> 88.
Lemma NX_of : forall f l, sh_buf f = l ++ [0] -> Forall (fun c => c <> 120 /\ c <> 88) l -> NX f.
Proof.
  intros f l E F i. rewrite E. destruct (read_char_cases l i) as [->|I]; [lia|].
  rewrite Forall_forall in F. apply F. exact I.
Qed.

Lemma hex_test_false : forall f c f', sh_wf f -> BB f -> NX f -> sh_getc f = (c, f') -> (Z.lor c 32 =? 120) = false.
Proof.
  intros f c f' W HB HN G. destruct (sh_getc_facts f c f' G W) as (_ & _ & _ & _ & _ & _ & _ & _ & SH).
  destruct SH as [(-> & _)|(-> & _)]; [reflexivity|].
  destruct (HN (sh_rpos f)) as [N1 N2]. pose proof (HB (sh_rpos f)). apply lor_c_32_120; lia.
Qed.

Lemma floatscan_total : forall fuelc f pok,
  sh_wf f -> BB f -> NX f -> 0 <= sh_rpos f -> zlength (sh_buf f) + 2 <= Z.of_nat fuelc ->
  (sh_stdio f = false -> sh_cnt0 f <= sh_rpos f) ->
  exists f' y, floatscan fuelc f 1 pok = Some (f', y)
    /\ sh_wf f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f
    /\ (sh_stdio f = false -> sh_cnt0 f' <= sh_rpos f').
Proof.
  intros fuelc f pok W HB HN R FU NS.
  pose proof (sh_N_le f W) as NL.
  unfold floatscan. change (1 =? 0) with false. change (1 =? 1) with true. cbn iota. change (-1021 - 53) with (-1074).
  destruct (fs_ws_total fuelc f W HB R FU) as [c1 [f1 (E1 & W1 & S1 & B1 & SP1 & R1 & CI1 & NS1 & CR1 & _)]]. rewrite E1.
  destruct S1 as (Bf1 & St1 & C01 & N1 & n1).
  assert (BB1 : BB f1) by (intros i; rewrite Bf1; apply HB).
  assert (NX1 : NX f1) by (intros i; rewrite Bf1; apply HN).
  (* [comment removed for export] *)
  set (sg := if (c1 =? 43) || (c1 =? 45) then _ else _).
  assert (SG : exists sign c2 f2, sg = (sign, c2, f2) /\ sh_wf f2 /\ sh_same f f2 /\ bchar c2 /\ (contc c2 -> sh_rpos f2 <= sh_N f2)
            /\ 0 <= sh_rpos f2 /\ (sh_stdio f = false -> sh_cnt0 f + 1 <= sh_rpos f2) /\ (contc c2 -> 1 <= sh_rpos f2)).
  { subst sg. destruct ((c1 =? 43) || (c1 =? 45)) eqn:SGN.
    - assert (CC1 : contc c1). { unfold contc. destruct (Z.eqb_spec c1 43); [subst; lia|]. destruct (Z.eqb_spec c1 45); [subst; lia| discriminate SGN]. }
      specialize (CI1 CC1). cbv zeta.
      destruct (sh_getc f1) as [c2 f2] eqn:G2.
      destruct (sh_getc_facts f1 c2 f2 G2 W1) as (W2 & B2 & S2 & C02 & N2 & n2 & RP2 & CT2 & SH2).
      eexists _, _, _. split; [reflexivity|]. split; [exact W2|]. split.
      { eapply sh_same_trans; [| eapply sh_same_getc; eauto]. unfold sh_same; auto. }
      split; [eapply getc_bchar; eauto|]. split; [intros CC; destruct (CT2 CC); rewrite N2; lia|]. split; [lia|].
      split. { intros ST. specialize (NS ST). specialize (NS1 ST). lia. } intros CC. destruct (CT2 CC). lia.
    - eexists _, _, _. split; [reflexivity|]. split; [exact W1|]. split; [unfold sh_same; auto|]. split; [exact B1|]. split; [exact CI1|]. split; [lia|].
      split. { intros ST. specialize (NS ST). specialize (NS1 ST). lia. } intros CC. specialize (CR1 CC). lia. }
  destruct SG as [sign [c2 [f2 (-> & W2 & S2 & B2 & CI2 & R2 & NS2 & CR2)]]].
  destruct S2 as (Bf2 & St2 & C02 & N2 & n2).
  assert (BB2 : BB f2) by (intros i; rewrite Bf2; apply HB).
  assert (NX2 : NX f2) by (intros i; rewrite Bf2; apply HN).
  pose proof (sh_N_le f2 W2) as NL2.
  (* [comment removed for export] *)
  destruct (fs_inf_total f2 c2 W2 BB2 B2 CI2) as [[[i3 c3] f3] (E3 & (Hi3 & W3 & S3 & B3 & CI3 & R3 & NS3) & C3)]. rewrite E3.
  destruct S3 as (Bf3 & St3 & C03 & N3 & n3).
  assert (UNG : forall g n, sh_wf g -> sh_stdio g = sh_stdio f -> (sh_stdio f = false -> sh_rpos (fs_unget_loop n g) = sh_rpos g - Z.of_nat n)).
  { intros g n Wg Sg ST. destruct (fs_unget_loop_facts n g) as (_ & _ & _ & _ & _ & _ & _ & E). apply E.
    unfold sh_wf in Wg. rewrite Sg, ST in Wg. tauto. }
  destruct ((i3 =? 3) || (i3 =? 8) || ((3 <? i3) && nz pok)) eqn:INF.
  { (* [comment removed for export] *)
    match goal with |- exists f' y, Some (?g, _) = Some (f', y) /\ _ => set (g' := g) end.
    assert (HG : sh_wf g' /\ sh_buf g' = sh_buf f /\ sh_stdio g' = sh_stdio f /\ (sh_stdio f = false -> sh_cnt0 g' <= sh_rpos g')).
    { subst g'. destruct (negb (i3 =? 8)) eqn:N8.
      - destruct (sh_unget_facts f3 W3) as (W4 & S4 & R4). destruct S4 as (Bf4 & St4 & C04 & N4 & n4).
        assert (U4 : sh_stdio f = false -> sh_rpos (sh_unget f3) = sh_rpos f3 - 1).
        { intros ST. apply sh_unget_rpos_nonstdio. unfold sh_wf in W3. rewrite St3, St2, ST in W3. tauto. }
        destruct (nz pok).
        + destruct (fs_unget_loop_facts (Z.to_nat (i3 - 3)) (sh_unget f3)) as (N5 & C05 & St5 & Bf5 & G5 & n5 & R5 & E5).
          split; [apply fs_unget_loop_wf; exact W4|]. split; [congruence|]. split; [congruence|].
          intros ST. rewrite C05, C04, C03. rewrite (UNG (sh_unget f3) _ W4 ltac:(congruence) ST), (U4 ST), (NS3 ltac:(congruence)).
          rewrite Z2Nat.id by lia. specialize (NS2 ST).
          assert (i3 <> 8). { intros ->. discriminate N8. } lia.
        + split; [exact W4|]. split; [congruence|]. split; [congruence|].
          intros ST. rewrite C04, C03, (U4 ST), (NS3 ltac:(congruence)). specialize (NS2 ST). lia.
      - split; [exact W3|]. split; [congruence|]. split; [congruence|]. intros ST. rewrite C03, (NS3 ltac:(congruence)). specialize (NS2 ST). lia. }
    destruct HG as (HG1 & HG2 & HG3 & HG4). eexists _, _. split; [reflexivity|]. auto. }
  (* [comment removed for export] *)
  set (nn := if i3 =? 0 then fs_nan_loop 4 (0, c3, f3) else Some (i3, c3, f3)).
  assert (NN : exists i4 c4 f4, nn = Some (i4, c4, f4) /\ 0 <= i4 <= 8 /\ sh_wf f4 /\ sh_same f2 f4 /\ bchar c4 /\ (contc c4 -> sh_rpos f4 <= sh_N f4)
            /\ sh_rpos f2 <= sh_rpos f4 /\ (sh_stdio f = false -> sh_rpos f4 <= sh_rpos f2 + i4) /\ (i4 = 0 -> contc c4 -> 1 <= sh_rpos f4)).
  { subst nn. destruct (Z.eqb_spec i3 0) as [I0|I0].
    - subst i3. destruct (fs_inf_loop_i0 _ _ _ _ _ E3) as [-> ->].
      destruct (fs_nan_total f2 c2 W2 BB2 B2 CI2) as [[[i4 c4] f4] (E4 & (Hi4 & W4 & S4 & B4 & CI4 & R4 & NS4) & C4)].
      rewrite E4. eexists _, _, _. split; [reflexivity|]. split; [lia|]. split; [exact W4|]. split; [exact S4|]. split; [exact B4|]. split; [exact CI4|].
      split; [lia|]. split; [intros ST; rewrite (NS4 ltac:(congruence)); lia|]. intros ->.
      destruct (fs_nan_loop_i0 _ _ _ _ _ E4) as [-> ->]. exact CR2.
    - eexists _, _, _. split; [reflexivity|]. split; [lia|]. split; [exact W3|]. split; [unfold sh_same; auto|]. split; [exact B3|]. split; [exact CI3|].
      split; [lia|]. split; [intros ST; rewrite (NS3 ltac:(congruence)); lia|]. intros; lia. }
  destruct NN as [i4 [c4 [f4 (-> & Hi4 & W4 & S4 & B4 & CI4 & R4 & NS4 & I40)]]].
  destruct S4 as (Bf4 & St4 & C04 & N4 & n4).
  assert (BB4 : BB f4) by (intros i; rewrite Bf4, Bf2; apply HB).
  assert (NX4 : NX f4) by (intros i; rewrite Bf4, Bf2; apply HN).
  pose proof (sh_N_le f4 W4) as NL4.
  destruct (Z.eqb_spec i4 3) as [I3|I3].
  { (* [comment removed for export] *)
    destruct (sh_getc f4) as [c5 f5] eqn:G5.
    destruct (sh_getc_facts f4 c5 f5 G5 W4) as (W5 & B5 & S5 & C05 & N5 & n5 & RP5 & CT5 & SH5).
    destruct (negb (c5 =? 40)).
    { destruct (sh_unget_facts f5 W5) as (W6 & S6 & R6). destruct S6 as (Bf6 & St6 & C06 & N6 & n6).
      eexists _, _. split; [reflexivity|]. split; [exact W6|]. split; [congruence|]. split; [congruence|].
      intros ST. rewrite C06, C05, C04. specialize (NS2 ST). lia. }
    destruct (fs_par_total fuelc f5 W5) as [i6 [c6 [f6 (E6 & W6 & S6 & B6 & Hi6 & R6 & NS6)]]].
    { intros i; rewrite B5, Bf4, Bf2; apply HB. } { lia. } { rewrite B5, Bf4, Bf2. lia. }
    rewrite E6. destruct S6 as (Bf6 & St6 & C06 & N6 & n6).
    destruct (c6 =? 41).
    { eexists _, _. split; [reflexivity|]. split; [exact W6|]. split; [congruence|]. split; [congruence|]. intros ST. rewrite C06, C05, C04. specialize (NS2 ST). lia. }
    destruct (sh_unget_facts f6 W6) as (W7 & S7 & R7). destruct S7 as (Bf7 & St7 & C07 & N7 & n7).
    destruct (negb (nz pok)).
    { eexists _, _. split; [reflexivity|]. split; [now apply sh_lim0_wf|]. unfold sh_lim0; cbn. split; [congruence|]. split; [congruence|]. intros; lia. }
    eexists _, _. split; [reflexivity|]. split; [apply fs_unget_loop_wf; exact W7|].
    destruct (fs_unget_loop_facts (Z.to_nat i6) (sh_unget f6)) as (N8 & C08 & St8 & Bf8 & G8 & n8 & R8 & E8).
    split; [congruence|]. split; [congruence|].
    intros ST. rewrite C08, C07, C06, C05, C04. rewrite (UNG (sh_unget f6) _ W7 ltac:(congruence) ST).
    rewrite sh_unget_rpos_nonstdio. 2:{ unfold sh_wf in W6. rewrite St6, S5, St4, St2, ST in W6. tauto. }
    rewrite (NS6 ltac:(congruence)). rewrite Z2Nat.id by lia.
    rewrite (nonstdio_read f4 c5 f5 W4 ltac:(congruence) G5). specialize (NS2 ST). lia. }
  destruct (nz i4) eqn:NZ4.
  { eexists _, _. split; [reflexivity|]. split; [apply sh_lim0_wf; now apply sh_unget_wf|].
    unfold sh_lim0; cbn. rewrite sh_unget_buf, sh_unget_stdio. split; [congruence|]. split; [congruence|]. intros; lia. }
  assert (I40' : i4 = 0). { unfold nz in NZ4. destruct (Z.eqb_spec i4 0); [assumption| discriminate NZ4]. }
  specialize (I40 I40').
  destruct (Z.eqb_spec c4 48) as [C48|C48].
  - destruct (sh_getc f4) as [c5 f5] eqn:G5.
    destruct (sh_getc_facts f4 c5 f5 G5 W4) as (W5 & B5 & S5 & C05 & N5 & n5 & RP5 & CT5 & SH5).
    rewrite (hex_test_false f4 c5 f5 W4 BB4 NX4 G5).
    destruct (sh_unget_facts f5 W5) as (W6 & S6 & R6). destruct S6 as (Bf6 & St6 & C06 & N6 & n6).
    assert (CC4 : contc c4) by (subst; unfold contc; lia). specialize (CI4 CC4). specialize (I40 CC4).
    destruct (decfloat_total_all fuelc (sh_unget f5) 48 sign pok W6) as [f' [y (E & W' & B' & S' & NS')]].
    + intros i. rewrite Bf6, B5, Bf4, Bf2. apply HB.
    + unfold bchar. lia.
    + intros _. destruct (sh_unget_shape f5) as [(L & EU)|(L & EU & _)].
      * rewrite EU. clear - W5 L. unfold sh_wf in W5. unfold sh_N. destruct (sh_stdio f5) eqn:ST5; [lia|]. destruct W5 as [_ W5b]. congruence.
      * rewrite EU, sh_unget_N, N5. lia.
    + lia.
    + rewrite Bf6, B5, Bf4, Bf2. exact FU.
    + intros ST. rewrite St6 in ST. rewrite C06, C05, C04, C02. rewrite sh_unget_rpos_nonstdio. 2:{ unfold sh_wf in W5. rewrite ST in W5. tauto. }
      rewrite (nonstdio_read f4 c5 f5 W4 ltac:(congruence) G5). specialize (NS2 ltac:(congruence)). lia.
    + rewrite E. eexists _, _. split; [reflexivity|]. split; [exact W'|]. split; [congruence|]. split; [congruence|].
      intros ST. apply NS'. congruence.
  - destruct (decfloat_total_all fuelc f4 c4 sign pok W4 BB4 B4 CI4 ltac:(lia)) as [f' [y (E & W' & B' & S' & NS')]].
    + rewrite Bf4, Bf2. exact FU.
    + intros ST. rewrite C04, C02. specialize (NS2 ltac:(congruence)). lia.
    + rewrite E. eexists _, _. split; [reflexivity|]. split; [exact W'|]. split; [congruence|]. split; [congruence|].
      intros ST. apply NS'. congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zlength_snoc0 : forall l, zlength (l ++ [0]) = zlength l + 1.
Proof. intros. unfold zlength. rewrite length_app. cbn [length]. lia. Qed.
Lemma fuel_of_val : forall s, Z.of_nat (fuel_of s) = zlength s + 2.
Proof. intros. unfold fuel_of, zlength. lia. Qed.

Theorem scan_strtod_total_gen : forall l,
  Forall (fun c => 0 <= c < 256) l -> Forall (fun c => c <> 120 /\ c <> 88) l ->
  exists vd c, scan_strtod (l ++ [0]) = Some (vd, c) /\ 0 <= c.
Proof.
  intros l HB HX. unfold scan_strtod.
  set (f0 := mkSh (l ++ [0]) 0 0 0 false false).
  assert (W0 : sh_wf f0). { unfold sh_wf; cbn. split; [exists l; reflexivity| reflexivity]. }
  destruct (floatscan_total (fuel_of (l ++ [0])) f0 1 W0) as [f' [y (E & W' & B' & S' & NS')]].
  - eapply BB_of_bytes; [reflexivity| exact HB].
  - eapply NX_of; [reflexivity| exact HX].
  - cbn. lia.
  - rewrite fuel_of_val. cbn [sh_buf f0]. lia.
  - cbn. intros; lia.
  - rewrite E. eexists _, _. split; [reflexivity|]. unfold sh_cnt. specialize (NS' eq_refl). lia.
Qed.

Lemma strlen_total : forall l, Forall (fun c => 0 <= c < 256) l ->
  exists n, strlen_loop (fuel_of (l ++ [0])) (l ++ [0]) 0 = Some n /\ 0 <= n <= zlength l /\ znth (l ++ [0]) n = 0.
Proof.
  intros l HB. rewrite strlen_loop_eq.
  destruct (wloop_total (fun n => nz (znth (l ++ [0]) n)) (fun n => n + 1) (fun n => 0 <= n <= zlength l) (fun n => zlength l - n))
    with (fuel := fuel_of (l ++ [0])) (s := 0) as [n (E & R & C)].
  - intros n Hn Cn. unfold nz in Cn. destruct (Z.eqb_spec (znth (l ++ [0]) n) 0) as [E|NE]; [discriminate Cn|].
    destruct (znth_snoc0 l n) as [?|[? _]]; [congruence|]. lia.
  - pose proof (Zle_0_nat (length l)). unfold zlength. lia.
  - rewrite fuel_of_val, zlength_snoc0. unfold zlength. lia.
  - exists n. split; [exact E|]. split; [exact R|]. unfold nz in C. destruct (Z.eqb_spec (znth (l ++ [0]) n) 0); [assumption| discriminate C].
Qed.

Theorem scan_sscanf_lg_total_gen : forall l,
  Forall (fun c => 0 <= c < 256) l -> Forall (fun c => c <> 120 /\ c <> 88) l ->
  scan_sscanf_lg (l ++ [0]) <> None.
Proof.
  intros l HB HX. unfold scan_sscanf_lg.
  destruct (strlen_total l HB) as [n (En & Rn & Zn)]. rewrite En.
  set (f0 := sh_lim0 (mkSh (l ++ [0]) 0 0 n true false)).
  assert (W0 : sh_wf f0). { unfold sh_wf; cbn. rewrite zlength_snoc0. lia. }
  assert (B0 : BB f0). { eapply BB_of_bytes; [reflexivity| exact HB]. }
  assert (FU : zlength (sh_buf f0) + 2 <= Z.of_nat (fuel_of (l ++ [0]))). { rewrite fuel_of_val. cbn. lia. }
  destruct (fs_ws_total (fuel_of (l ++ [0])) f0 W0 B0 ltac:(cbn; lia) FU) as [c1 [f1 (E1 & W1 & S1 & B1 & SP1 & R1 & CI1 & NS1 & CR1 & LA1)]].
  rewrite E1. destruct S1 as (Bf1 & St1 & C01 & N1 & n1).
  assert (RF0 : sh_rpos f0 = 0) by reflexivity. rewrite RF0 in *.
  destruct (sh_unget_facts f1 W1) as (W2 & S2 & R2). destruct S2 as (Bf2 & St2 & C02 & N2 & n2).
  assert (R2' : 0 <= sh_rpos (sh_unget f1)).
  { destruct (sh_unget_shape f1) as [(L & EE)|(L & E & _)]; [rewrite EE; lia|]. destruct LA1 as [L'|L']; [congruence| lia]. }
  pose proof (sh_lim0_wf _ W2) as W3.
  destruct (sh_getc (sh_lim0 (sh_unget f1))) as [c4 f4] eqn:G4.
  destruct (sh_getc_facts _ c4 f4 G4 W3) as (W4 & B4 & S4 & C04 & N4 & n4 & RP4 & CT4 & SH4). cbn [sh_rpos sh_lim0 sh_buf sh_stdio sh_cnt0] in *.
  destruct (Z.ltb_spec c4 0). { discriminate. }
  destruct (sh_unget_facts f4 W4) as (W5 & S5 & R5). destruct S5 as (Bf5 & St5 & C05 & N5 & n5).
  destruct (floatscan_total (fuel_of (l ++ [0])) (sh_unget f4) 0 W5) as [f' [y (E & _)]].
  - intros i. rewrite Bf5, B4. cbn. rewrite sh_unget_buf, Bf1. apply (B0 i).
  - intros i. rewrite Bf5, B4. cbn. rewrite sh_unget_buf, Bf1. cbn. eapply (NX_of f0); [reflexivity| exact HX].
  - destruct (sh_unget_shape f4) as [(L & ->)|(L & E & _)]; [lia|]. rewrite E.
    destruct SH4 as [(-> & _)|(_ & E4 & _)]; [lia|]. rewrite E4. cbn. lia.
  - rewrite Bf5, B4. cbn. rewrite sh_unget_buf, Bf1. exact FU.
  - rewrite St5, S4. cbn. rewrite sh_unget_stdio, St1. cbn. intros; discriminate.
  - rewrite E. destruct (sh_cnt f' =? 0); discriminate.
Qed.
