(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require CatSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require ArgvEnv__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AllocSim2__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.CatSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.CatSim__Common.SeqExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.RefMemcpyLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.ArgvEnv__Common.MemSplit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymExec3 AxSymExec3Sound. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require AxSymRun3__Common. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymExec3Sound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AxSymRun3__Common.AxSymRun3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import StdioSymDrive EntryGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
#[local] Instance driverknow_fx : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.FPState := OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec.fx0.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record hull := HULL { h_base : expr; h_lo : Z; h_hi : Z; h_same : bool }.

Definition hull_sem (E : env) (M M' : word -> option byte) (h : hull) : Prop :=
  let b := bv_unsigned (edenot E (h_base h)) in
  forall x : word, b + h_lo h <= bv_unsigned x < b + h_hi h ->
    if h_same h then M' x = M x else (M' x = None -> M x = None).

Definition hulls_sem (E : env) (M M' : word -> option byte) (hs : list hull) : Prop :=
  Forall (hull_sem E M M') hs.

(* [comment removed for export] *)
Definition fp_in_b (need_same : bool) (hs : list hull) (b : expr) (k : Z) (n : Z) : bool :=
  Z.leb 0 n && Z.ltb n (2 ^ 64)
  && existsb (fun h => expr_eqb b (h_base h) && Z.leb (h_lo h) k && Z.leb (k + n) (h_hi h)
                       && (negb need_same || h_same h)) hs.

Definition kentry_in_hulls_b (hs : list hull) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => fp_in_b true hs b k (Z.of_nat w)
  | KZero (SA b k) (ELit n) => fp_in_b true hs b k n
  | KBlob (SA b k) (ELit n) _ => fp_in_b true hs b k n
  | KFill (SA b k) (ELit n) _ => fp_in_b true hs b k n
  | KUnk (SA b k) (ELit n) => fp_in_b false hs b k n
  | KImg lo hi => fp_in_b true hs (ELit 0) lo (hi - lo)
  | KWr (SA b k) (ELit n) => fp_in_b false hs b k n
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | _ => false
  end.

Definition kn_in_hulls_b (hs : list hull) (kn : list kentry) : bool :=
  forallb (kentry_in_hulls_b hs) kn.

Section Hulls.
Variable segs : list Segment.

#[using="Type"] Lemma fp_in_sound : forall E M M' hs ns b k n,
  hulls_sem E M M' hs -> fp_in_b ns hs b k n = true ->
  forall x : word, bv_unsigned (edenot E b) + k <= bv_unsigned x < bv_unsigned (edenot E b) + k + n ->
    if ns then M' x = M x else (M' x = None -> M x = None).
Proof.
  intros E M M' hs ns b k n Hs Hb x Hx.
  unfold fp_in_b in Hb. apply andb_prop in Hb as [_ Hb]. apply existsb_exists in Hb as (h & Hin & Hh).
  repeat (apply andb_prop in Hh; destruct Hh as [Hh ?]).
  apply expr_eqb_eq in Hh. subst b.
  apply Z.leb_le in H1. apply Z.leb_le in H0.
  pose proof (proj1 (Forall_forall _ _) Hs h Hin x ltac:(lia)) as Hx'.
  destruct ns; cbn [negb orb] in H.
  - rewrite H in Hx'. exact Hx'.
  - destruct (h_same h); [|exact Hx']. intros HN. rewrite <- Hx'. exact HN.
Qed.

#[using="Type"] Lemma fp_in_len : forall ns hs b k n, fp_in_b ns hs b k n = true -> 0 <= n < 2 ^ 64.
Proof.
  intros ns hs b k n Hb. unfold fp_in_b in Hb.
  apply andb_prop in Hb as [Hb _]. apply andb_prop in Hb as [H0 H1].
  apply Z.leb_le in H0. apply Z.ltb_lt in H1. lia.
Qed.

#[using="Type"] Lemma wview_def_mono : forall M M' (x : word),
  (M' x = None -> M x = None) -> wview segs M x <> None -> wview segs M' x <> None.
Proof.
  intros M M' x Himp Hw. unfold wview in *.
  destruct (M' x) as [b'|] eqn:E'; [discriminate|].
  rewrite (Himp eq_refl) in Hw. exact Hw.
Qed.

#[using="Type"] Lemma store_ok_def_mono : forall M M' (a : word) n,
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  (forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat n -> M' x = None -> M x = None) ->
  store_ok segs M a n = true -> store_ok segs M' a n = true.
Proof.
  intros M M' a n Hnw Himp Hs. destruct n as [|n]; [reflexivity|].
  apply store_ok_of_all; [exact Hnw|]. intros x Hx.
  apply (wview_def_mono M M' x (Himp x Hx)). exact (store_ok_all segs M (S n) a Hnw Hs x Hx).
Qed.

#[using="Type"] Lemma kentry_hulls_sound : forall E M M' hs K,
  hulls_sem E M M' hs -> kentry_in_hulls_b hs K = true ->
  kentry_ok segs E M K -> kentry_ok segs E M' K.
Proof.
  intros E M M' hs K Hs Hb HK.
  destruct K as [[b k] w v | [b k] n | [b k] n bk | lo hi | e m | e lo hi | [b k] n | a1 n1 a2 n2 | [b k] n c | [b k] n];
    cbn [kentry_in_hulls_b] in Hb; try (destruct n as [nz| | | | | | |]; try discriminate Hb); cbn [kentry_ok] in *;
    try (pose proof (fp_in_len _ _ _ _ _ Hb) as Hnz).
  - (* [comment removed for export] *) destruct HK as (Hw & Hfl & Hrd). split; [exact Hw|]. split; [exact Hfl|].
    rewrite <- Hrd. pose proof (flat_u E (SA b k) _ Hfl) as Hu.
    destruct Hfl as (F1 & F2 & F3 & F4). unfold estart in Hu, F1, F2, F3, F4. cbn [a_base a_off] in Hu, F1, F2, F3, F4.
    apply rdn_ext; [rewrite Hu; lia|]. intros x Hx. rewrite Hu in Hx.
    exact (fp_in_sound E M M' hs true b k (Z.of_nat w) Hs Hb x ltac:(lia)).
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4). unfold estart, elenZ in *. cbn [a_base a_off edenot] in *.
    rewrite <- (Hz i Hi).
    rewrite u_small in Hi, F4 by lia.
    exact (fp_in_sound E M M' hs true b k nz Hs Hb (Z_to_bv 64 (bv_unsigned (edenot E b) + k + i)) ltac:(rewrite u_small by lia; lia)).
  - (* [comment removed for export] *) destruct HK as (Hfl & Hlen & Hz). split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4). unfold estart, elenZ in *. cbn [a_base a_off edenot] in *.
    rewrite <- (Hz i Hi). rewrite u_small in Hi, F4 by lia.
    exact (fp_in_sound E M M' hs true b k nz Hs Hb (Z_to_bv 64 (bv_unsigned (edenot E b) + k + i)) ltac:(rewrite u_small by lia; lia)).
  - (* [comment removed for export] *) destruct HK as (H0 & H1 & Hn). split; [exact H0|]. split; [exact H1|]. intros i Hi.
    rewrite <- (Hn i Hi).
    exact (fp_in_sound E M M' hs true (ELit 0) lo (hi - lo) Hs Hb (Z_to_bv 64 i)
             ltac:(cbn [edenot]; change (bv_unsigned (Z_to_bv 64 0)) with 0; rewrite u_small by lia; lia)).
  - exact HK.
  - exact HK.
  - (* [comment removed for export] *) destruct HK as [Hfl Hs']. split; [exact Hfl|]. intros d m Hd Hdm.
    destruct Hfl as (F1 & F2 & F3 & F4). unfold estart, elenZ in *. cbn [a_base a_off edenot] in *.
    rewrite u_small in Hdm, F3, F4 by lia. destruct m as [|m]; [reflexivity|].
    apply (store_ok_def_mono M M'); [rewrite u_small by lia; lia | | apply Hs'; [exact Hd | rewrite u_small by lia; exact Hdm]].
    intros x Hx. rewrite u_small in Hx by lia.
    exact (fp_in_sound E M M' hs false b k nz Hs Hb x ltac:(lia)).
  - exact HK.
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi.
    destruct Hfl as (F1 & F2 & F3 & F4). unfold estart, elenZ in *. cbn [a_base a_off edenot] in *.
    rewrite <- (Hz i Hi). rewrite u_small in Hi, F4 by lia.
    exact (fp_in_sound E M M' hs true b k nz Hs Hb (Z_to_bv 64 (bv_unsigned (edenot E b) + k + i)) ltac:(rewrite u_small by lia; lia)).
  - (* [comment removed for export] *) destruct HK as [Hfl Hz]. split; [exact Hfl|]. intros i Hi HN.
    destruct Hfl as (F1 & F2 & F3 & F4). unfold estart, elenZ in *. cbn [a_base a_off edenot] in *.
    rewrite u_small in Hi, F4 by lia.
    apply (Hz i ltac:(rewrite u_small by lia; lia)).
    exact (fp_in_sound E M M' hs false b k nz Hs Hb (Z_to_bv 64 (bv_unsigned (edenot E b) + k + i)) ltac:(rewrite u_small by lia; lia) HN).
Qed.


#[using="Type"] Theorem know_hulls_sound : forall E M M' hs kn,
  hulls_sem E M M' hs -> kn_in_hulls_b hs kn = true ->
  know_ok segs E M kn -> know_ok segs E M' kn.
Proof.
  intros E M M' hs kn Hs Hb HK. unfold know_ok in *. apply Forall_forall. intros K Hin.
  eapply kentry_hulls_sound; [exact Hs | | exact (proj1 (Forall_forall _ _) HK K Hin)].
  exact (proj1 (forallb_forall _ _) Hb K Hin).
Qed.

(* [comment removed for export] *)
#[using="Type"] Corollary know_hulls_filter : forall E M M' hs (keep : kentry -> bool) kn,
  hulls_sem E M M' hs -> kn_in_hulls_b hs (List.filter keep kn) = true ->
  know_ok segs E M kn -> know_ok segs E M' (List.filter keep kn).
Proof.
  intros E M M' hs keep kn Hs Hb HK. eapply know_hulls_sound; [exact Hs | exact Hb |].
  apply know_ok_filter. exact HK.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hull_same_intro : forall E M M' b lo hi,
  (forall x : word, bv_unsigned (edenot E b) + lo <= bv_unsigned x < bv_unsigned (edenot E b) + hi -> M' x = M x) ->
  hull_sem E M M' (HULL b lo hi true).
Proof. intros E M M' b lo hi H x Hx. cbn. apply H. exact Hx. Qed.

#[using="Type"] Lemma hull_weak_intro : forall E M M' b lo hi,
  (forall x : word, bv_unsigned (edenot E b) + lo <= bv_unsigned x < bv_unsigned (edenot E b) + hi ->
                    M' x = None -> M x = None) ->
  hull_sem E M M' (HULL b lo hi false).
Proof. intros E M M' b lo hi H x Hx. cbn. apply H. exact Hx. Qed.

#[using="Type"] Lemma hull_weak_of_grows : forall E M M' b lo hi,
  mem_grows M M' -> hull_sem E M M' (HULL b lo hi false).
Proof.
  intros E M M' b lo hi Hg x Hx. cbn. intros HN. destruct (M x) eqn:EM; [|reflexivity].
  exfalso. exact (Hg x ltac:(rewrite EM; discriminate) HN).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition piece_covered (big : list kentry) (K : kentry) : bool :=
  match K with
  | KImg lo hi => Z.leb 0 lo && existsb (fun B => match B with KImg l h => Z.leb l lo && Z.leb hi h | _ => false end) big
  | _ => false
  end.

#[using="Type"] Lemma kimg_pieces_ok : forall E M big pieces,
  know_ok segs E M big -> forallb (piece_covered big) pieces = true -> know_ok segs E M pieces.
Proof.
  intros E M big pieces HK Hb. unfold know_ok in *. apply Forall_forall. intros K Hin.
  pose proof (proj1 (forallb_forall _ _) Hb K Hin) as HbK.
  destruct K; cbn [piece_covered] in HbK; try discriminate.
  apply andb_prop in HbK as [H0 HbK]. apply Z.leb_le in H0.
  apply existsb_exists in HbK as (B & HinB & HB). destruct B; try discriminate.
  apply andb_prop in HB as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HK _ HinB) as (B0 & B1 & Bn). cbn [kentry_ok].
  split; [exact H0|]. split; [lia|]. intros i Hi. apply Bn. lia.
Qed.

End Hulls.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition is_junk_slot (jb : nat) (i : nat) (e : expr) : bool :=
  match e with EVar v => Nat.eqb v (jb + i) | _ => false end.

(* [comment removed for export] *)
Fixpoint tracked (jb : nat) (sr : list expr) (i : nat) : list nat :=
  match sr with
  | [] => []
  | e :: t => if is_junk_slot jb i e then tracked jb t (S i) else i :: tracked jb t (S i)
  end.

Lemma all_regs_cases : forall r : reg, In (ridx r) (seq 0 32).
Proof. intros r. apply in_seq. pose proof (ridx_range r). lia. Qed.

Lemma tracked_spec : forall jb sr i n,
  (n < length sr)%nat -> ~ In (i + n)%nat (tracked jb sr i) -> is_junk_slot jb (i + n) (nth n sr (ELit 0)) = true.
Proof.
  intros jb sr. induction sr as [|e t IH]; intros i n Hn Hnot; [cbn in Hn; lia|].
  destruct n as [|n].
  - cbn [nth]. rewrite Nat.add_0_r in Hnot |- *. cbn [tracked] in Hnot.
    destruct (is_junk_slot jb i e) eqn:Hj; [reflexivity|]. exfalso. apply Hnot. left. reflexivity.
  - cbn [nth]. replace (i + S n)%nat with (S i + n)%nat in * by lia.
    apply IH; [cbn in Hn; lia|]. intros Hin. apply Hnot. cbn [tracked].
    destruct (is_junk_slot jb i e); [exact Hin | right; exact Hin].
Qed.

Theorem regs_ok_layout : forall pre ebs R sr,
  length sr = 32%nat ->
  (forall i, In i (tracked (length pre) sr 0) -> i <> 0%nat ->
     getr R (Z_to_bv 5 (Z.of_nat i)) = edenot (Env (vals_ev (pre ++ junk_vals R)) ebs) (nth i sr (ELit 0))) ->
  regs_ok (Env (vals_ev (pre ++ junk_vals R)) ebs) sr R.
Proof.
  intros pre ebs R sr Hlen Htr r. unfold sr_get.
  destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
  - pose proof (ridx_range r) as Hr.
    assert (Hne : ridx r <> 0%nat).
    { intros H0. assert (r = 0%bv) by (rewrite <- (ridx_roundtrip r), H0; apply bv_eq; reflexivity). subst r.
      rewrite bv_eqb_refl in Hr0. discriminate. }
    destruct (in_dec Nat.eq_dec (ridx r) (tracked (length pre) sr 0)) as [Hin | Hnot].
    + rewrite <- (ridx_roundtrip r) at 1. exact (Htr (ridx r) Hin Hne).
    + pose proof (tracked_spec (length pre) sr 0 (ridx r) ltac:(lia) Hnot) as Hj. cbn [Nat.add] in Hj.
      destruct (nth (ridx r) sr (ELit 0)); cbn [is_junk_slot] in Hj; try discriminate.
      apply Nat.eqb_eq in Hj. subst n. cbn [edenot ev].
      rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite nth_map_seq by exact Hr. rewrite ridx_roundtrip. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ev_pre : forall pre junk ebs i, (i < length pre)%nat ->
  ev (Env (vals_ev (pre ++ junk)) ebs) i = nth i pre (Z_to_bv 64 0).
Proof. intros. cbn [ev]. apply vals_ev_app_l. assumption. Qed.

Lemma ev_junk : forall pre R ebs (r : reg),
  ev (Env (vals_ev (pre ++ junk_vals R)) ebs) (length pre + ridx r) = getr R r.
Proof.
  intros. cbn [ev]. rewrite vals_ev_app_r. unfold vals_ev, junk_vals.
  rewrite nth_map_seq by apply ridx_range. rewrite ridx_roundtrip. reflexivity.
Qed.

Lemma ev_junk_n : forall pre R ebs n, (n < 32)%nat ->
  ev (Env (vals_ev (pre ++ junk_vals R)) ebs) (length pre + n) = getr R (Z_to_bv 5 (Z.of_nat n)).
Proof.
  intros. cbn [ev]. rewrite vals_ev_app_r. unfold vals_ev, junk_vals.
  rewrite nth_map_seq by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma In_bv_of_unsigned : forall n (r : bv n) (l : list (bv n)),
  In (bv_unsigned r) (map bv_unsigned l) -> In r l.
Proof.
  intros n r l H. apply in_map_iff in H as (x & Hx & Hin). replace r with x; [exact Hin|]. apply bv_eq. exact Hx.
Qed.

(* [comment removed for export] *)
Definition CALLEE_SAVED_N : list nat := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.

Lemma callee_saved_nat : forall i, In i CALLEE_SAVED_N -> In (Z_to_bv 5 (Z.of_nat i)) callee_saved.
Proof.
  intros i Hi. cbn [In CALLEE_SAVED_N] in Hi.
  repeat (destruct Hi as [<-|Hi]); [ .. | destruct Hi]; apply In_bv_of_unsigned; vm_compute; tauto.
Qed.

(* [comment removed for export] *)
Lemma kept_nat : forall (R R' : bvmap 5 word),
  (forall r : reg, In r callee_saved -> getr R' r = getr R r) ->
  forall i, In i CALLEE_SAVED_N -> getr R' (Z_to_bv 5 (Z.of_nat i)) = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof. intros R R' HK i Hi. apply HK. apply callee_saved_nat. exact Hi. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition win3 := (nat * Z * Z)%type.

Definition entry_in_wins_b (wins : list win3) (e : sentry) : bool :=
  match e with SE (SA b k) w _ =>
    existsb (fun wn : win3 => let '(i, lo, hi) := wn in win_in_b i lo hi b k (Z.of_nat w)) wins end.

Definition log_in_wins_b (wins : list win3) (log : list sentry) : bool :=
  forallb (entry_in_wins_b wins) log.

(* [comment removed for export] *)
Definition wins_ok (E : env) (wins : list win3) : Prop :=
  Forall (fun wn : win3 => let '(i, lo, hi) := wn in
            0 <= bv_unsigned (ev E i) + lo /\ bv_unsigned (ev E i) + hi < 2 ^ 64) wins.

Definition out_of_wins (E : env) (wins : list win3) (x : word) : Prop :=
  Forall (fun wn : win3 => let '(i, lo, hi) := wn in
            ~ (bv_unsigned (ev E i) + lo <= bv_unsigned x < bv_unsigned (ev E i) + hi)) wins.

Lemma mem_denot_in_wins : forall E M log wins (x : word),
  log_in_wins_b wins log = true -> wins_ok E wins -> out_of_wins E wins x ->
  mem_denot E M log x = M x.
Proof.
  intros E M log wins x Hb Hw Hx.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_in_wins_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  cbn [entry_in_wins_b] in He. apply existsb_exists in He as ([[i lo] hi] & Hin & He).
  destruct b as [z|i'| | | | | |]; cbn [win_in_b] in He; try discriminate.
  repeat (apply andb_prop in He; destruct He as [He ?]). apply Nat.eqb_eq in He. subst i'.
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  pose proof (proj1 (Forall_forall _ _) Hw _ Hin) as W. cbn in W.
  pose proof (proj1 (Forall_forall _ _) Hx _ Hin) as X. cbn in X.
  cbn [mem_denot]. pose proof (u64_range x).
  rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u_small by lia. lia.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition dpath (segs : list Segment) (c c' : config) : Prop :=
  star_cfg segs CFG c [] c' /\ forall K, OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.realizes segs c' K -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.realizes segs c K.

Lemma dpath_refl : forall segs c, dpath segs c c.
Proof. intros segs c. split; [apply star_cfg_refl | intros K H; exact H]. Qed.

Lemma dpath_trans : forall segs c1 c2 c3, dpath segs c1 c2 -> dpath segs c2 c3 -> dpath segs c1 c3.
Proof.
  intros segs c1 c2 c3 [S1 R1] [S2 R2]. split.
  - eapply star_cfg_trans_nil; eassumption.
  - intros K HK. apply R1. apply R2. exact HK.
Qed.

Lemma dpath_msteps : forall segs ms ms' mdl,
  m_halted mdl = None -> m_vm_lazy mdl = [] -> msteps segs ms ms' ->
  dpath segs (mkCfg ms mdl) (mkCfg ms' mdl).
Proof.
  intros segs ms ms' mdl Hh Hl MS. split.
  - apply star_cfg_msteps; assumption.
  - intros K HK. eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.AllocSim2__Common.ShapeAlg.rz_msteps; eassumption.
Qed.
