(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec ShapeAlg AgentLib. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import Spec. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanInit. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesIO AsanMainLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section WithFP1.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint nocase (s : shape) : bool :=
  match s with
  | SNil | SExit _ => true
  | SEmitP _ _ s' => nocase s'
  | SAlt2 a b => nocase a && nocase b
  | SCase _ _ _ _ | SHole _ | SNext => false
  end.

Lemma t_eq_emit : forall evs T T', t_eq T T' -> t_eq (t_emit evs T) (t_emit evs T').
Proof.
  intros evs T T' H tr. unfold t_emit. split; (intros [Hp | (tr' & -> & HT)]; [left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]]).
Qed.

Lemma t_eq_alt2 : forall A A' B B', t_eq A A' -> t_eq B B' -> t_eq (t_alt2 A B) (t_alt2 A' B').
Proof.
  intros A A' B B' HA HB tr. unfold t_alt2. split; (intros [H|H]; [left; apply HA | right; apply HB]; exact H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive sev : Type := SW (fd b : Z) | SB (fd : Z) (k : nat) | SX (code : Z).

Definition sev_eqb (x y : sev) : bool :=
  match x, y with
  | SW f a, SW g b => Z.eqb f g && Z.eqb a b
  | SB f k, SB g k' => Z.eqb f g && Nat.eqb k k'
  | SX c, SX d => Z.eqb c d
  | _, _ => false
  end.

Lemma sev_eqb_eq : forall x y, sev_eqb x y = true -> x = y.
Proof.
  intros [f a|f k|c] [g b|g k'|d] H; cbn in H; try discriminate.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
  - apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. subst. reflexivity.
  - apply Z.eqb_eq in H. subst. reflexivity.
Qed.

Definition sev_of (fd : Z) (ps : list spiece) : list sev :=
  flat_map (fun p => match p with SPLit bs => map (SW fd) bs | SPBlob k => [SB fd k] end) ps.

(* [comment removed for export] *)
Fixpoint paths (s : shape) : list (list sev) :=
  match s with
  | SNil | SHole _ | SNext => [[]]
  | SExit c => [[SX c]]
  | SEmitP fd ps s' => map (fun p => sev_of fd ps ++ p) (paths s')
  | SAlt2 a b => paths a ++ paths b
  | SCase _ _ a b => paths a ++ paths b
  end.

Fixpoint prefixb (p q : list sev) : bool :=
  match p, q with
  | [], _ => true
  | _ :: _, [] => false
  | x :: p', y :: q' => sev_eqb x y && prefixb p' q'
  end.

Definition sub_paths (P Q : list (list sev)) : bool :=
  forallb (fun p => existsb (fun q => prefixb p q) Q) P.

Definition shape_equiv (s1 s2 : shape) : bool :=
  sub_paths (paths s1) (paths s2) && sub_paths (paths s2) (paths s1).

(* [comment removed for export] *)
Definition sev_evs (E : env) (fs : Fs.Fs) (v : sev) : list event :=
  match v with
  | SW fd b => [WriteEv (Z_to_bv 64 fd) (Z_to_bv 8 b)]
  | SB fd k => map (WriteEv (Z_to_bv 64 fd)) (eb E k)
  | SX c => [ExitEv (Z_to_bv 64 c) fs]
  end.
Definition events (E : env) (fs : Fs.Fs) (p : list sev) : list event := flat_map (sev_evs E fs) p.

Lemma events_app : forall E fs p q, events E fs (p ++ q) = events E fs p ++ events E fs q.
Proof. intros. unfold events. apply flat_map_app. Qed.

Lemma paths_ne : forall s, paths s <> [].
Proof.
  induction s; cbn [paths]; try discriminate.
  - destruct (paths s); [congruence | cbn; discriminate].
  - destruct (paths s1); [congruence | cbn; discriminate].
  - destruct (paths s1); [congruence | cbn; discriminate].
Qed.

Lemma Wp_events : forall E fs fd ps, Wp E fd ps = events E fs (sev_of fd ps).
Proof.
  intros E fs fd ps. unfold Wp, sev_of, events. induction ps as [|p ps IH]; [reflexivity|].
  cbn [flat_map]. rewrite map_app, flat_map_app, IH. f_equal.
  destruct p as [bs|k]; cbn [piece_den flat_map].
  - rewrite map_map. induction bs as [|b bs IHb]; [reflexivity|]. cbn. rewrite IHb. reflexivity.
  - rewrite app_nil_r. reflexivity.
Qed.

Lemma is_prefix_app_l {X} : forall (l a b : list X), is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof. induction l as [|x l IH]; intros a b H; cbn; [exact H | split; [reflexivity | apply IH; exact H]]. Qed.

Lemma is_prefix_refl' {X} : forall (l : list X), is_prefix l l.
Proof. induction l; cbn; auto. Qed.

Lemma is_prefix_trans' {X} : forall (a b c : list X), is_prefix a b -> is_prefix b c -> is_prefix a c.
Proof.
  induction a as [|x a IH]; intros b c H1 H2; [destruct c; exact I|].
  destruct b as [|y b]; [cbn in H1; contradiction|]. destruct c as [|z c]; [cbn in H2; contradiction|].
  cbn in *. destruct H1 as [-> H1]. destruct H2 as [-> H2]. split; [reflexivity | eapply IH; eassumption].
Qed.

(* [comment removed for export] *)
Theorem sd_paths : forall HOLES D E fs s, nocase s = true ->
  forall tr, sd HOLES D E fs s tr <-> exists p, In p (paths s) /\ is_prefix tr (events E fs p).
Proof.
  intros HOLES D E fs s. induction s as [|c|fd ps s IH|a IHa b IHb|e mid s1 IH1 s2 IH2|h|]; intros Hnc tr; cbn [nocase] in Hnc; try discriminate; cbn [sd paths].
  - unfold t_nil. split.
    + intros ->. exists []. split; [left; reflexivity | exact I].
    + intros (p & [<-|[]] & Hp). apply is_prefix_nil_r in Hp. exact Hp.
  - unfold t_exit, t_emit, t_nil. split.
    + intros [Hp | (tr' & -> & ->)]; exists [SX c]; (split; [left; reflexivity|]); [exact Hp | cbn; auto].
    + intros (p & [<-|[]] & Hp). left. exact Hp.
  - specialize (IH Hnc). unfold t_emit. rewrite (Wp_events E fs). split.
    + intros [Hp | (tr' & -> & HT)].
      * destruct (paths s) as [|p0 P] eqn:EP; [exfalso; exact (paths_ne s EP)|].
        exists (sev_of fd ps ++ p0). split; [apply in_map; left; reflexivity|].
        rewrite events_app. apply is_prefix_app_r. exact Hp.
      * apply IH in HT as (p & Hin & Hp). exists (sev_of fd ps ++ p). split; [apply in_map; exact Hin|].
        rewrite events_app. apply is_prefix_app_l. exact Hp.
    + intros (q & Hin & Hq). apply in_map_iff in Hin as (p & <- & Hin).
      rewrite events_app in Hq. apply is_prefix_app_split in Hq as [Hq | (b' & -> & Hq)].
      * left. exact Hq.
      * right. exists b'. split; [reflexivity|]. apply IH. exists p. split; [exact Hin | exact Hq].
  - apply andb_prop in Hnc as [Ha Hb]. specialize (IHa Ha). specialize (IHb Hb). unfold t_alt2. split.
    + intros [H|H]; [apply IHa in H | apply IHb in H]; destruct H as (p & Hin & Hp); exists p; split;
        [apply in_app_iff; left; exact Hin | exact Hp | apply in_app_iff; right; exact Hin | exact Hp].
    + intros (p & Hin & Hp). apply in_app_iff in Hin as [Hin|Hin]; [left; apply IHa | right; apply IHb]; exists p; split; assumption.
Qed.

Lemma prefixb_sound : forall E fs p q, prefixb p q = true -> is_prefix (events E fs p) (events E fs q).
Proof.
  intros E fs p. induction p as [|x p IH]; intros q H; cbn [prefixb] in H.
  - apply is_prefix_nil.
  - destruct q as [|y q]; [discriminate|]. apply andb_prop in H as [H1 H2]. apply sev_eqb_eq in H1. subst y.
    unfold events. cbn [flat_map]. apply is_prefix_app_l. apply IH. exact H2.
Qed.

Lemma sub_paths_sound : forall HOLES D E fs s1 s2, nocase s1 = true -> nocase s2 = true ->
  sub_paths (paths s1) (paths s2) = true -> forall tr, sd HOLES D E fs s1 tr -> sd HOLES D E fs s2 tr.
Proof.
  intros HOLES D E fs s1 s2 H1 H2 HS tr Htr.
  apply (sd_paths HOLES D E fs s1 H1) in Htr as (p & Hin & Hp).
  unfold sub_paths in HS. rewrite forallb_forall in HS. specialize (HS p Hin).
  apply existsb_exists in HS as (q & Hq & Hpq).
  apply (sd_paths HOLES D E fs s2 H2). exists q. split; [exact Hq|].
  eapply is_prefix_trans'; [exact Hp | apply prefixb_sound; exact Hpq].
Qed.

Theorem shape_equiv_sound : forall HOLES D E fs s1 s2, nocase s1 = true -> nocase s2 = true ->
  shape_equiv s1 s2 = true -> t_eq (sd HOLES D E fs s1) (sd HOLES D E fs s2).
Proof.
  intros HOLES D E fs s1 s2 H1 H2 HE tr. unfold shape_equiv in HE. apply andb_prop in HE as [HA HB].
  split; apply sub_paths_sound; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sdecide (F : list kentry) (e : expr) (mid : Z) : option bool :=
  match xhi F e, xlo F e with
  | Some hi, _ => if Z.leb hi mid then Some true
                  else match xlo F e with Some lo => if Z.ltb mid lo then Some false else None | None => None end
  | None, Some lo => if Z.ltb mid lo then Some false else None
  | None, None => None
  end.

Fixpoint sresolve (F : list kentry) (s : shape) : option shape :=
  match s with
  | SNil => Some SNil
  | SExit c => Some (SExit c)
  | SEmitP fd ps s' => match sresolve F s' with Some s'' => Some (SEmitP fd ps s'') | None => None end
  | SAlt2 a b =>
      match sresolve F a, sresolve F b with
      | Some a', Some b' => Some (SAlt2 a' b')
      | _, _ => None
      end
  | SCase e mid s1 s2 =>
      match sdecide F e mid with
      | Some true => sresolve F s1
      | Some false => sresolve F s2
      | None =>
          match sresolve F s1, sresolve F s2 with
          | Some a, Some b => if shape_equiv a b then Some a else None
          | _, _ => None
          end
      end
  | SHole _ | SNext => None
  end.

Lemma sresolve_nocase : forall F s s', sresolve F s = Some s' -> nocase s' = true.
Proof.
  intros F s. induction s as [|c|fd ps s IH|a IHa b IHb|e mid s1 IH1 s2 IH2|h|]; intros s' H; cbn [sresolve] in H; try discriminate.
  - injection H as <-. reflexivity.
  - injection H as <-. reflexivity.
  - destruct (sresolve F s) as [s''|] eqn:Hs; [|discriminate]. injection H as <-. cbn [nocase]. apply IH. reflexivity.
  - destruct (sresolve F a) as [a'|] eqn:Ha; [|discriminate].
    destruct (sresolve F b) as [b'|] eqn:Hb; [|discriminate]. injection H as <-. cbn [nocase].
    rewrite (IHa a' eq_refl), (IHb b' eq_refl). reflexivity.
  - destruct (sdecide F e mid) as [[|]|]; [apply IH1; exact H | apply IH2; exact H |].
    destruct (sresolve F s1) as [a|] eqn:H1; [|discriminate]. destruct (sresolve F s2) as [b|] eqn:H2; [|discriminate].
    destruct (shape_equiv a b); [|discriminate]. injection H as <-. apply IH1. reflexivity.
Qed.
End WithFP1.


Section Resolve.
Context {fx : FPState}.
  Variable SEGS : list Segment.
  Variables (E : env) (M : word -> option byte) (F : list kentry).
  Hypothesis HF : know_ok SEGS E M F.

  Theorem sresolve_sound : forall HOLES D fs s s',
    sresolve F s = Some s' -> t_eq (sd HOLES D E fs s) (sd HOLES D E fs s').
  Proof.
    intros HOLES D fs s. induction s as [|c|fd ps s IH|a IHa b IHb|e mid s1 IH1 s2 IH2|h|]; intros s' H; cbn [sresolve] in H; try discriminate.
    - injection H as <-. apply t_eq_refl.
    - injection H as <-. apply t_eq_refl.
    - destruct (sresolve F s) as [s''|] eqn:Hs; [|discriminate]. injection H as <-. cbn [sd].
      apply t_eq_emit. apply IH. reflexivity.
    - destruct (sresolve F a) as [a'|] eqn:Ha; [|discriminate].
      destruct (sresolve F b) as [b'|] eqn:Hb; [|discriminate]. injection H as <-. cbn [sd].
      apply t_eq_alt2; [apply IHa | apply IHb]; reflexivity.
    - assert (DEC : forall d, sdecide F e mid = Some d -> Z.leb (bv_unsigned (edenot E e)) mid = d).
      { intros d Hd. unfold sdecide in Hd.
        destruct (xhi F e) as [hi|] eqn:Hh.
        - pose proof (xhi_sound SEGS E M F e hi HF Hh) as Xh.
          destruct (Z.leb_spec hi mid); [injection Hd as <-; apply Z.leb_le; lia|].
          destruct (xlo F e) as [lo|] eqn:Hl; [|discriminate].
          pose proof (xlo_sound SEGS E M F e lo HF Hl) as Xl.
          destruct (Z.ltb_spec mid lo); [injection Hd as <-; apply Z.leb_gt; lia | discriminate].
        - destruct (xlo F e) as [lo|] eqn:Hl; [|discriminate].
          pose proof (xlo_sound SEGS E M F e lo HF Hl) as Xl.
          destruct (Z.ltb_spec mid lo); [injection Hd as <-; apply Z.leb_gt; lia | discriminate]. }
      cbn [sd].
      destruct (sdecide F e mid) as [[|]|] eqn:Hdec.
      + rewrite (DEC true eq_refl). apply IH1. exact H.
      + rewrite (DEC false eq_refl). apply IH2. exact H.
      + destruct (sresolve F s1) as [a|] eqn:H1; [|discriminate]. destruct (sresolve F s2) as [b|] eqn:H2; [|discriminate].
        destruct (shape_equiv a b) eqn:Heq; [|discriminate]. injection H as <-.
        destruct (Z.leb (bv_unsigned (edenot E e)) mid); [apply IH1; reflexivity|].
        eapply t_eq_trans; [apply IH2; reflexivity|].
        apply t_eq_sym. apply shape_equiv_sound; [exact (sresolve_nocase F s1 a H1) | exact (sresolve_nocase F s2 b H2) | exact Heq].
  Qed.
End Resolve.
Section WithFP2.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive tgt : Type :=
| TDie (ps : list spiece)      (* [comment removed for export] *)
| TOk (calls : nat)            (* [comment removed for export] *)
| TOpen (t : tgt).             (* [comment removed for export] *)
(* [comment removed for export] *)

Definition zs (s : string) : list Z := map (fun a => Z.of_nat (nat_of_ascii a)) (list_ascii_of_string s).

Definition ps_usage : list spiece := [SPLit (zs "usage: "); SPBlob 1; SPLit (zs " INPUT" ++ [10])].
Definition ps_cannot_open : list spiece := [SPLit (zs "cli: cannot open "); SPBlob 2; SPLit [10]].
Definition ps_read_error : list spiece := [SPLit (zs "cli: read error on "); SPBlob 2; SPLit [10]].
Definition ps_refused : list spiece := [SPLit (zs "cli: input >= 67108864 bytes, refused" ++ [10])].
Definition ps_short : list spiece := [SPLit (zs "cli: input shorter than header" ++ [10])].
Definition ps_overrun : list spiece := [SPLit (zs "cli: config_len overruns input" ++ [10])].
Definition ps_oom : list spiece := [SPLit (zs "cli: out of memory" ++ [10])].
(* [comment removed for export] *)
Definition ps_usage0 : list spiece := [SPLit (zs "usage: " ++ zs " INPUT" ++ [10])].
Definition ps_cannot_open0 : list spiece := [SPLit (zs "cli: cannot open " ++ [10])].

Fixpoint shape_of_tgt (t : tgt) : shape :=
  match t with
  | TDie ps => SEmitP 2 ps (SExit 2)
  | TOk calls => SEmitP 1 [SPLit (concat (repeat [48; 10] calls))] (SExit 0)
  | TOpen t' => SAlt2 (SEmitP 2 ps_cannot_open (SExit 2)) (shape_of_tgt t')
  end.

Lemma shape_of_tgt_nocase : forall t, nocase (shape_of_tgt t) = true.
Proof. induction t; cbn; auto. Qed.

(* [comment removed for export] *)
Lemma zs_s2b : forall s, map (Z_to_bv 8) (zs s) = s2b s.
Proof. intros s. unfold zs, s2b. rewrite map_map. reflexivity. Qed.
End WithFP2.


Section Den.
Context {fx : FPState}.
  Variables (E : env) (argv : list (list byte)) (fs : Fs.Fs).
  Hypothesis HB1 : eb E 1%nat = nth 0 argv [].
  Hypothesis HB2 : eb E 2%nat = nth 1 argv [].

  Lemma sd_alt2 : forall HOLES D a b, sd HOLES D E fs (SAlt2 a b) = t_alt2 (sd HOLES D E fs a) (sd HOLES D E fs b).
  Proof. reflexivity. Qed.

  Lemma Wp_die : forall HOLES D ps msg,
    flat_map (piece_den E) ps = msg ->
    t_eq (sd HOLES D E fs (SEmitP 2 ps (SExit 2))) (t_die msg fs).
  Proof. intros HOLES D ps msg H. cbn [sd]. unfold Wp, t_die, W, exit_code. rewrite H. apply t_eq_refl. Qed.

  Lemma den_usage : flat_map (piece_den E) ps_usage = msg_usage (nth 0 argv []).
  Proof. cbn -[zs Z_to_bv]. rewrite !map_app, !zs_s2b, HB1, app_nil_r. reflexivity. Qed.
  Lemma den_cannot_open : flat_map (piece_den E) ps_cannot_open = msg_cannot_open (nth 1 argv []).
  Proof. cbn -[zs Z_to_bv]. rewrite !zs_s2b, HB2. reflexivity. Qed.
  Lemma den_usage0 : nth 0 argv [] = [] -> flat_map (piece_den E) ps_usage0 = msg_usage (nth 0 argv []).
  Proof. intros H0. cbn -[zs Z_to_bv]. rewrite !map_app, !zs_s2b, H0, app_nil_r. reflexivity. Qed.
  Lemma den_cannot_open0 : nth 1 argv [] = [] -> flat_map (piece_den E) ps_cannot_open0 = msg_cannot_open (nth 1 argv []).
  Proof. intros H1. cbn -[zs Z_to_bv]. rewrite !map_app, !zs_s2b, H1, app_nil_r. reflexivity. Qed.
  Lemma den_read_error : flat_map (piece_den E) ps_read_error = msg_read_error (nth 1 argv []).
  Proof. cbn -[zs Z_to_bv]. rewrite !zs_s2b, HB2. reflexivity. Qed.
  Lemma den_refused : flat_map (piece_den E) ps_refused = msg_refused.
  Proof. cbn -[zs Z_to_bv]. rewrite !map_app, !zs_s2b, app_nil_r. reflexivity. Qed.
  Lemma den_short : flat_map (piece_den E) ps_short = msg_short.
  Proof. cbn -[zs Z_to_bv]. rewrite !map_app, !zs_s2b, app_nil_r. reflexivity. Qed.
  Lemma den_overrun : flat_map (piece_den E) ps_overrun = msg_overrun.
  Proof. cbn -[zs Z_to_bv]. rewrite !map_app, !zs_s2b, app_nil_r. reflexivity. Qed.

  Lemma Wz_zero_lines : forall calls, Wp E 1 [SPLit (concat (repeat [48; 10] calls))] = W 1 (zero_lines calls).
  Proof.
    intros calls. unfold Wp, W. cbn [flat_map piece_den]. rewrite app_nil_r. f_equal.
    induction calls as [|c IH]; [reflexivity|]. cbn [repeat concat zero_lines app map]. rewrite IH. reflexivity.
  Qed.
End Den.
Section WithFP3.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CFGX : expr := ION.CFGX JB.
Definition XCM : expr := ION.XCM JB.

(* [comment removed for export] *)
Definition XB1S : expr := ION.XB1S JB.

(* [comment removed for export] *)
Definition variant : Type := bool * Z * bool.
Definition v_cfg0 (v : variant) : bool := fst (fst v).
Definition v_cmod (v : variant) : Z := snd (fst v).
Definition v_cnt (v : variant) : bool := snd v.
Definition variants : list variant :=
  [(true, 0, false); (true, 1, false); (true, 2, false); (true, 3, false); (false, 0, false); (false, 1, false); (false, 2, false); (false, 3, false);
   (true, 0, true); (true, 1, true); (true, 2, true); (true, 3, true); (false, 0, true); (false, 1, true); (false, 2, true); (false, 3, true)].
Definition vfacts (v : variant) : list kentry :=
  (if v_cfg0 v then KRange CFGX 0 0 else KRange CFGX 1 32767)
  :: KRange XCM (v_cmod v) (v_cmod v)
  :: [if v_cnt v then KRange XB1S (2 ^ 63) (2 ^ 64 - 1) else KRange XB1S 0 (2 ^ 63 - 1)].
Definition variant_of (c : list byte) : variant := (cfglen c =? 0, bz 2 c mod 4, 128 <=? bz 1 c).
Definition calls_of_v (v : variant) : nat := if v_cfg0 v then 1%nat else S (Z.to_nat (v_cmod v)).
Definition vconsistent (C : class) (v : variant) : bool :=
  let cf := cbounds C QCfgLen in
  let cm := cbounds C QCmod in
  let cn := cbounds C QCnt in
  ((if v_cfg0 v then Z.leb (fst cf) 0 else Z.leb 1 (snd cf)) && Z.leb (fst cm) (v_cmod v) && Z.leb (v_cmod v) (snd cm)
   && (if v_cnt v then Z.leb 1 (snd cn) else Z.leb (fst cn) 0))%bool.

Definition if_empty (C : class) (q : qty) (ps0 ps : list spiece) : list spiece :=
  if snd (cbounds C q) <=? 0 then ps0 else ps.

(* [comment removed for export] *)
Definition target_of (C : class) : option tgt :=
  let look := look_of C in
  if look =? 0 then Some (TDie (if_empty C QL0 ps_usage0 ps_usage))
  else if ((look =? 1) || (look =? 2))%bool then Some (TDie (if_empty C QL1 ps_cannot_open0 ps_cannot_open))
  else if look =? 3 then Some (TOpen (TDie ps_read_error))
  else if look =? 4 then
    let f := clamp (cbounds C QFlen) 0 (2 ^ 26) in
    let room := cbounds C QRoom in
    if 2 ^ 26 <=? fst f then Some (TOpen (TDie ps_refused))
    else if snd f <? 6 then Some (TOpen (TDie ps_short))
    else if ((snd f <? 2 ^ 26) && (6 <=? fst f) && (snd room <? 0))%bool then Some (TOpen (TDie ps_overrun))
    else if ((snd f <? 2 ^ 26) && (0 <=? fst room))%bool then Some (TOpen (TOk 0))   (* [comment removed for export] *)
    else None
  else None.

(* [comment removed for export] *)
Fixpoint tv (t : tgt) (v : variant) : tgt :=
  match t with TOk _ => TOk (calls_of_v v) | TOpen t' => TOpen (tv t' v) | TDie ps => TDie ps end.

Definition class_shape_ok (C : class) (s : shape) : bool :=
  match target_of C with
  | None => false
  | Some t => forallb (fun v => negb (vconsistent C v) ||
                match sresolve (vfacts v ++ facts_of_class C) s with
                | Some s' => shape_equiv s' (shape_of_tgt (tv t v))
                | None => false
                end)%bool variants
  end.
End WithFP3.


(* [comment removed for export] *)
Section ShapeSound.
Context {fx : FPState}.
  Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  Let c := content_of argv fs.

  Lemma variant_in : In (variant_of c) variants.
  Proof.
    unfold variant_of, variants. pose proof (Z.mod_pos_bound (bz 2 c) 4 ltac:(lia)) as H.
    assert (E4 : bz 2 c mod 4 = 0 \/ bz 2 c mod 4 = 1 \/ bz 2 c mod 4 = 2 \/ bz 2 c mod 4 = 3) by lia.
    destruct (cfglen c =? 0); destruct (128 <=? bz 1 c); destruct E4 as [-> |[-> |[-> | ->]]]; cbn; tauto.
  Qed.

  Lemma variant_consistent : forall C, in_class C argv fs = true -> vconsistent C (variant_of c) = true.
  Proof.
    intros C HC. unfold vconsistent, variant_of, v_cfg0, v_cmod, v_cnt. cbn [fst snd].
    pose proof (cbounds_sound C QCfgLen argv fs HC (qval_bounds ph sp rdraw argv envp fs uid hw Hva Hfit QCfgLen)) as B1.
    pose proof (cbounds_sound C QCmod argv fs HC (qval_bounds ph sp rdraw argv envp fs uid hw Hva Hfit QCmod)) as B2.
    pose proof (cbounds_sound C QCnt argv fs HC (qval_bounds ph sp rdraw argv envp fs uid hw Hva Hfit QCnt)) as B3.
    cbn [qval] in B1, B2, B3. fold c in B1, B2, B3. pose proof (cfglen_range c). rewrite cmod_eq in B2. pose proof (bz_range 1 c) as R1.
    apply andb_true_intro; split; [apply andb_true_intro; split; [apply andb_true_intro; split|]|]; try (apply Z.leb_le; lia).
    - destruct (Z.eqb_spec (cfglen c) 0); apply Z.leb_le; lia.
    - destruct (Z.leb_spec 128 (bz 1 c)); apply Z.leb_le.
      + assert (1 <= bz 1 c / 128) by (apply Z.div_le_lower_bound; lia). lia.
      + assert (bz 1 c / 128 < 1) by (apply Z.div_lt_upper_bound; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma target4_sound : forall C x E HOLES D a0 p c',
    in_class C argv fs = true -> target_of C = Some (TOpen x) ->
    argv = [a0; p] -> qlook argv fs = 4 -> fs_lookup fs p = Some c' ->
    t_eq (sd HOLES D E fs (shape_of_tgt (tv x (variant_of c')))) (t_body c' fs).
  Proof.
    intros C x E HOLES D a0 p c' HC HT Hargv Hq Hlk.
    pose proof (qval_bounds ph sp rdraw argv envp fs uid hw Hva Hfit) as QB.
    assert (HLK : look_of C = qlook argv fs \/ look_of C = -1).
    { unfold look_of. destruct (Z.eqb_spec (fst (cbounds C QLook)) (snd (cbounds C QLook))); [|right; reflexivity].
      left. pose proof (cbounds_sound C QLook argv fs HC (QB QLook)) as BL. cbn [qval] in BL. lia. }
    pose proof (cbounds_sound C QFlen argv fs HC (QB QFlen)) as BF. cbn [qval] in BF. fold c in BF.
    pose proof (cbounds_sound C QRoom argv fs HC (QB QRoom)) as BR. cbn [qval] in BR. fold c in BR. rewrite room_eq in BR.
    pose proof (cbounds_sound C QCnt argv fs HC (QB QCnt)) as BC. cbn [qval] in BC. fold c in BC.
    assert (Hc : c = c') by (unfold c, content_of; rewrite Hargv, Hlk; reflexivity).
    clearbody c. subst c.
    pose proof (flen_range c') as FR. pose proof (cfglen_range c') as CR.
    unfold target_of in HT.
    destruct HLK as [HL|HL]; [|rewrite HL in HT; cbn in HT; discriminate]. rewrite HL, Hq in HT.
    cbn -[cbounds clamp Z.leb Z.ltb Z.pow] in HT.
    unfold flen in BF, FR, BR.
    assert (CFG : Z.to_nat ((bv_unsigned (nth 0 c' (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 c' (Z_to_bv 8 0))) mod 32768) = Z.to_nat (cfglen c')) by reflexivity.
    assert (CFG' : config_len c' = Z.to_nat (cfglen c')) by reflexivity.
    unfold t_body, lib_lines, lib_status, calls_of, HDR_MIN. rewrite !CFG'.
    destruct (Z.leb_spec (2 ^ 26) (fst (clamp (cbounds C QFlen) 0 (2 ^ 26)))) as [X1|X1].
    { injection HT as <-. unfold MAX_INPUT; cbn [tv shape_of_tgt]; rewrite ?CFG. unfold clamp in X1; cbn [fst snd] in X1.
      destruct (Z.leb_spec 67108864 (Z.of_nat (length c'))); [|exfalso; lia].
      apply Wp_die. apply den_refused. }
    destruct (Z.ltb_spec (snd (clamp (cbounds C QFlen) 0 (2 ^ 26))) 6) as [X2|X2].
    { injection HT as <-. unfold MAX_INPUT; cbn [tv shape_of_tgt]; rewrite ?CFG. unfold clamp in X1, X2; cbn [fst snd] in X1, X2.
      destruct (Z.leb_spec 67108864 (Z.of_nat (length c'))); [exfalso; lia|].
      destruct (Nat.ltb_spec (length c') 6); [|exfalso; lia].
      apply Wp_die. apply den_short. }
    destruct ((snd (clamp (cbounds C QFlen) 0 (2 ^ 26)) <? 2 ^ 26) && (6 <=? fst (clamp (cbounds C QFlen) 0 (2 ^ 26))) && (snd (cbounds C QRoom) <? 0))%bool eqn:X3.
    { injection HT as <-. unfold MAX_INPUT; cbn [tv shape_of_tgt]; rewrite ?CFG. apply andb_prop in X3 as [X3 X5]. apply andb_prop in X3 as [X3 X4].
      apply Z.ltb_lt in X3. apply Z.leb_le in X4. apply Z.ltb_lt in X5. unfold clamp in *; cbn [fst snd] in *.
      destruct (Z.leb_spec 67108864 (Z.of_nat (length c'))); [exfalso; lia|].
      destruct (Nat.ltb_spec (length c') 6); [exfalso; lia|].
      destruct (Nat.ltb_spec (length c') (6 + Z.to_nat (cfglen c'))); [|exfalso; lia].
      apply Wp_die. apply den_overrun. }
    assert (CALLS : calls_of_v (variant_of c') = match Z.to_nat (cfglen c') with 0%nat => 1%nat | S _ => S (Z.to_nat (bv_unsigned (nth 2 c' (Z_to_bv 8 0)) mod 4)) end).
    { unfold calls_of_v, variant_of, v_cfg0, v_cmod. cbn [fst snd]. unfold bz.
      destruct (Z.eqb_spec (cfglen c') 0) as [E0|E0]; [rewrite E0; reflexivity|].
      destruct (Z.to_nat (cfglen c')) eqn:En; [exfalso; lia | reflexivity]. }
    assert (CNT : (32768 <=? bv_unsigned (nth 0 c' (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 c' (Z_to_bv 8 0))) = v_cnt (variant_of c')).
    { unfold variant_of, v_cnt. cbn [snd]. unfold bz, ION.hbyte. pose proof (u8_range (nth 0 c' (Z_to_bv 8 0))) as R0. pose proof (u8_range (nth 1 c' (Z_to_bv 8 0))) as R1.
      set (b0 := bv_unsigned (nth 0 c' (Z_to_bv 8 0))) in *. set (b1 := bv_unsigned (nth 1 c' (Z_to_bv 8 0))) in *.
      destruct (Z.leb_spec 32768 (b0 + 256 * b1)) as [Y|Y]; destruct (Z.leb_spec 128 b1) as [Y'|Y']; try reflexivity; exfalso; lia. }
    destruct ((snd (clamp (cbounds C QFlen) 0 (2 ^ 26)) <? 2 ^ 26) && (0 <=? fst (cbounds C QRoom)))%bool eqn:X4; [|discriminate].
    injection HT as <-. unfold MAX_INPUT; cbn [tv shape_of_tgt]; rewrite ?CFG. apply andb_prop in X4 as [X4 X5]. apply Z.ltb_lt in X4. apply Z.leb_le in X5.
    unfold clamp in *; cbn [fst snd] in *.
    destruct (Z.leb_spec 67108864 (Z.of_nat (length c'))); [exfalso; lia|].
    destruct (Nat.ltb_spec (length c') 6); [exfalso; lia|].
    destruct (Nat.ltb_spec (length c') (6 + Z.to_nat (cfglen c'))); [exfalso; lia|].
    cbn [sd]. rewrite Wz_zero_lines. unfold exit_code. rewrite CALLS. apply t_eq_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma target_of_sound : forall C t E HOLES D,
    in_class C argv fs = true -> target_of C = Some t ->
    eb E 1%nat = nth 0 argv [] -> eb E 2%nat = nth 1 argv [] ->
    t_eq (sd HOLES D E fs (shape_of_tgt (tv t (variant_of c)))) (spec argv fs).
  Proof.
    intros C t E HOLES D HC HT HB1 HB2.
    pose proof (qval_bounds ph sp rdraw argv envp fs uid hw Hva Hfit) as QB.
    assert (HLK : look_of C = qlook argv fs \/ look_of C = -1).
    { unfold look_of. destruct (Z.eqb_spec (fst (cbounds C QLook)) (snd (cbounds C QLook))); [|right; reflexivity].
      left. pose proof (cbounds_sound C QLook argv fs HC (QB QLook)) as BL. cbn [qval] in BL. lia. }
    pose proof (target4_sound C) as T4. pose proof HT as HT0. pose proof HC as HC0.
    (* [comment removed for export] *)
    assert (DU : flat_map (piece_den E) (if_empty C QL0 ps_usage0 ps_usage) = msg_usage (nth 0 argv [])).
    { unfold if_empty. destruct (Z.leb_spec (snd (cbounds C QL0)) 0) as [H0|H0]; [|apply (den_usage E _ HB1)].
      apply den_usage0. pose proof (cbounds_sound C QL0 argv fs HC (QB QL0)) as B0. cbn [qval] in B0.
      destruct (nth 0 argv []); [reflexivity | cbn [length] in B0; exfalso; lia]. }
    assert (DC : flat_map (piece_den E) (if_empty C QL1 ps_cannot_open0 ps_cannot_open) = msg_cannot_open (nth 1 argv [])).
    { unfold if_empty. destruct (Z.leb_spec (snd (cbounds C QL1)) 0) as [H0|H0]; [|apply (den_cannot_open E _ HB2)].
      apply den_cannot_open0. pose proof (cbounds_sound C QL1 argv fs HC (QB QL1)) as B0. cbn [qval] in B0.
      destruct (nth 1 argv []); [reflexivity | cbn [length] in B0; exfalso; lia]. }
    unfold target_of in HT. revert DU DC HT.
    generalize (if_empty C QL0 ps_usage0 ps_usage) (if_empty C QL1 ps_cannot_open0 ps_cannot_open). intros psU psC DU DC HT.
    pose proof (qlook_cases argv fs) as Q.
    destruct HLK as [HL|HL]; [|rewrite HL in HT; cbn in HT; discriminate]. rewrite HL in HT.
    destruct argv as [|a0 [|p [|x r]]]; try (rewrite Q in HT; cbn in HT; injection HT as <-; cbn [tv shape_of_tgt spec];
                                            apply Wp_die; exact DU).
    cbn [nth] in HB1, HB2, DC.
    destruct Q as [[Hq Hl]|[[Hq (Hl & Hp)]|[[Hq Hp]|[Hq (Hne & Hnd & Hl & c' & Hlk & Hc)]]]]; rewrite Hq in HT; cbn -[cbounds clamp Z.leb Z.ltb Z.pow] in HT.
    - injection HT as <-. cbn [tv shape_of_tgt spec]. destruct (Nat.leb_spec 4096 (length p)); [|lia].
      apply Wp_die. exact DC.
    - injection HT as <-. cbn [tv shape_of_tgt spec]. destruct (Nat.leb_spec 4096 (length p)); [lia|].
      destruct Hp as [->|[H1 H2]].
      + cbn [list_byte_eqb]. apply Wp_die. exact DC.
      + destruct (list_byte_eqb p []) eqn:He; [apply Wp_die; exact DC|].
        destruct (list_byte_eqb p dot_path) eqn:Hd; [apply list_byte_eqb_eq in Hd; exfalso; exact (H1 Hd)|].
        rewrite H2. apply Wp_die. exact DC.
    - injection HT as <-. cbn [tv shape_of_tgt spec].
      assert (Hdd : list_byte_eqb Uapi.dot_path dot_path = true) by (apply (proj2 (list_byte_eqb_eq _ _)); reflexivity).
      destruct (Nat.leb_spec 4096 (length p)) as [Hl|Hl]; [rewrite Hp in Hl; cbn in Hl; lia|].
      destruct (list_byte_eqb p []) eqn:He; [apply list_byte_eqb_eq in He; rewrite He in Hp; cbv in Hp; discriminate|].
      destruct (list_byte_eqb p dot_path) eqn:Hd; [|rewrite Hp, Hdd in Hd; discriminate].
      unfold t_opened_dir. rewrite sd_alt2.
      apply t_eq_alt2; [apply Wp_die; apply (den_cannot_open E [a0; p]); exact HB2|].
      apply Wp_die. apply (den_read_error E [a0; p]); exact HB2.
    - cbn [spec]. destruct (Nat.leb_spec 4096 (length p)); [lia|].
      destruct (list_byte_eqb p []) eqn:He; [apply list_byte_eqb_eq in He; congruence|].
      destruct (list_byte_eqb p dot_path) eqn:Hd; [apply list_byte_eqb_eq in Hd; exfalso; apply Hnd; exact Hd|].
      rewrite Hlk. unfold c in *. rewrite Hc in *.
      (* [comment removed for export] *)
      assert (HX : exists x, t = TOpen x).
      { revert HT. generalize (clamp (cbounds C QFlen) 0 (2 ^ 26)) (cbounds C QRoom) (cbounds C QCnt). clear. intros f room cnt HT.
        repeat match type of HT with (if ?b then _ else _) = _ => destruct b end;
          first [injection HT as <-; eexists; reflexivity | discriminate HT]. }
      destruct HX as [x ->]. cbn [tv shape_of_tgt]. rewrite sd_alt2. apply t_eq_alt2.
      + apply Wp_die. apply (den_cannot_open E [a0; p]). exact HB2.
      + unfold t_opened. exact (T4 x E HOLES D a0 p c' HC0 HT0 eq_refl Hq Hlk).
  Qed.

  (* [comment removed for export] *)
  Theorem class_shape_sound : forall SEGS C s E M HOLES D,
    in_class C argv fs = true -> class_shape_ok C s = true ->
    (forall n, (n < 8)%nat -> ev E n = ev (E0 ph sp rdraw brk0 argv envp uid hw) n) ->
    eb E 1%nat = nth 0 argv [] -> eb E 2%nat = nth 1 argv [] ->
    know_ok SEGS E M (vfacts (variant_of c)) ->
    t_eq (sd HOLES D E fs s) (spec argv fs).
  Proof.
    intros SEGS C s E M HOLES D HC HS Hev HB1 HB2 HV.
    unfold class_shape_ok in HS. destruct (target_of C) as [t|] eqn:HT; [|discriminate].
    rewrite forallb_forall in HS. specialize (HS (variant_of c) variant_in).
    rewrite (variant_consistent C HC) in HS. cbn [negb orb] in HS.
    destruct (sresolve (vfacts (variant_of c) ++ facts_of_class C) s) as [s'|] eqn:HR; [|discriminate].
    assert (HF : know_ok SEGS E M (vfacts (variant_of c) ++ facts_of_class C)).
    { apply Forall_app. split; [exact HV | eapply facts_of_class_sound; eassumption]. }
    eapply t_eq_trans; [exact (sresolve_sound SEGS E M _ HF HOLES D fs s s' HR)|].
    eapply t_eq_trans; [exact (shape_equiv_sound HOLES D E fs s' _ (sresolve_nocase _ _ _ HR) (shape_of_tgt_nocase _) HS)|].
    eapply target_of_sound; eassumption.
  Qed.
End ShapeSound.
Section WithFP4.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sdecide_sound : forall SEGS E M F e mid d,
  know_ok SEGS E M F -> sdecide F e mid = Some d -> Z.leb (bv_unsigned (edenot E e)) mid = d.
Proof.
  intros SEGS E M F e mid d HF Hd. unfold sdecide in Hd.
  destruct (xhi F e) as [hi|] eqn:Hh.
  - pose proof (xhi_sound SEGS E M F e hi HF Hh) as Xh.
    destruct (Z.leb_spec hi mid); [injection Hd as <-; apply Z.leb_le; lia|].
    destruct (xlo F e) as [lo|] eqn:Hl; [|discriminate].
    pose proof (xlo_sound SEGS E M F e lo HF Hl) as Xl.
    destruct (Z.ltb_spec mid lo); [injection Hd as <-; apply Z.leb_gt; lia | discriminate].
  - destruct (xlo F e) as [lo|] eqn:Hl; [|discriminate].
    pose proof (xlo_sound SEGS E M F e lo HF Hl) as Xl.
    destruct (Z.ltb_spec mid lo); [injection Hd as <-; apply Z.leb_gt; lia | discriminate].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MAXL : nat := 1%nat.
Definition t_res (L : nat) (argv : list (list byte)) (fs : Fs.Fs) : TSet :=
  match L with
  | 0%nat => spec argv fs
  | _ => match argv with [_; p] => match fs_lookup fs p with Some c => t_opened c fs | None => t_nil end | _ => t_nil end
  end.

Lemma t_body_nil : forall c fs, t_body c fs [].
Proof.
  intros c fs. unfold t_body.
  destruct (MAX_INPUT <=? Z.of_nat (length c)); [apply t_die_nil|].
  destruct (length c <? HDR_MIN)%nat; [apply t_die_nil|].
  destruct (length c <? HDR_MIN + _)%nat; [apply t_die_nil|].
  apply t_emit_has_nil.
Qed.
Lemma t_res_nil : forall L argv fs, t_res L argv fs [].
Proof.
  intros [|L] argv fs; cbn [t_res]; [apply spec_nil|];
    (destruct argv as [|a0 [|p [|x r]]]; try reflexivity; destruct (fs_lookup fs p); [|reflexivity]);
    apply t_body_nil.
Qed.

(* [comment removed for export] *)
Definition alt_shape (L : nat) : shape := SEmitP 2 ps_cannot_open (SExit 2).
(* [comment removed for export] *)
Fixpoint alts (L n : nat) : shape :=
  match n with 0%nat => SNil | S n' => SAlt2 (alt_shape L) (alts (S L) n') end.
Lemma alts_nocase : forall L n, nocase (alts L n) = true.
Proof. intros L n. revert L. induction n; intros L; cbn; [reflexivity|]. rewrite IHn. reflexivity. Qed.

(* [comment removed for export] *)
Definition strip (L : nat) (t : tgt) : option tgt :=
  match L, t with
  | 0%nat, _ => Some t
  | 1%nat, TOpen x => Some x
  | _, _ => None
  end.

Definition class_pay_ok (L : nat) (C : class) (s : shape) : bool :=
  match L with
  | 0%nat => class_shape_ok C s
  | _ =>
    (look_of C =? 4) &&
    match target_of C with
    | Some t =>
        match strip L t with
        | Some x => forallb (fun v => negb (vconsistent C v) ||
                      match sresolve (vfacts v ++ facts_of_class C) s with
                      | Some s' => shape_equiv s' (shape_of_tgt (tv x v))
                      | None => false
                      end)%bool variants
        | None => false
        end
    | None => false
    end
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition omin (a b : option nat) : option nat :=
  match a, b with Some x, Some y => Some (Nat.min x y) | Some x, None => Some x | None, _ => b end.

Fixpoint hsum (lv : nat -> option nat) (F : list kentry) (s : shape) : option (list (option nat * list (list sev))) :=
  match s with
  | SNil => Some [(None, [[]])]
  | SExit c => Some [(None, [[SX c]])]
  | SEmitP fd ps s' =>
      match hsum lv F s' with
      | Some L => if existsb (fun hp => match fst hp with Some _ => true | None => false end) L then None
                  else Some (map (fun hp => (None, map (fun p => sev_of fd ps ++ p) (snd hp))) L)
      | None => None
      end
  | SAlt2 a b =>
      match hsum lv F a, hsum lv F b with
      | Some La, Some Lb => Some (flat_map (fun x => map (fun y => (omin (fst x) (fst y), snd x ++ snd y)) Lb) La)
      | _, _ => None
      end
  | SCase e mid a b =>
      match sdecide F e mid with
      | Some true => hsum lv F a
      | Some false => hsum lv F b
      | None => match hsum lv F a, hsum lv F b with Some La, Some Lb => Some (La ++ Lb) | _, _ => None end
      end
  | SHole h => match lv h with Some L => Some [(Some L, [])] | None => None end
  | SNext => None
  end.

(* [comment removed for export] *)
Definition seg1_ok (L : nat) (hp : option nat * list (list sev)) : bool :=
  match fst hp with
  | Some L2 => Nat.leb L L2 && Nat.leb L2 MAXL
               && sub_paths ([] :: snd hp) (paths (alts L (MAXL - L)))
               && sub_paths (paths (alts L (L2 - L))) ([] :: snd hp)
  | None => false
  end.

Definition seg_ok (lv : nat -> option nat) (L : nat) (F : list kentry) (s : shape) : bool :=
  match hsum lv F s with Some SL => forallb (seg1_ok L) SL | None => false end.

Definition class_seg_ok (lv : nat -> option nat) (L : nat) (C : class) (s : shape) : bool :=
  (look_of C =? 4) &&
  forallb (fun v => negb (vconsistent C v) || seg_ok lv L (vfacts v ++ facts_of_class C) s)%bool variants.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pathset (E : env) (fs : Fs.Fs) (P : list (list sev)) : TSet :=
  fun tr => exists p, In p P /\ is_prefix tr (events E fs p).

Lemma pathset_app : forall E fs P Q tr, pathset E fs (P ++ Q) tr <-> pathset E fs P tr \/ pathset E fs Q tr.
Proof.
  intros E fs P Q tr. unfold pathset. split.
  - intros (p & Hin & Hp). apply in_app_iff in Hin as [Hin|Hin]; [left | right]; exists p; auto.
  - intros [(p & Hin & Hp)|(p & Hin & Hp)]; exists p; split; auto; apply in_app_iff; auto.
Qed.
Lemma pathset_nilcons : forall E fs P tr, pathset E fs ([] :: P) tr <-> tr = [] \/ pathset E fs P tr.
Proof.
  intros E fs P tr. unfold pathset. split.
  - intros (p & [<-|Hin] & Hp); [left; apply is_prefix_nil_r in Hp; exact Hp | right; exists p; auto].
  - intros [->|(p & Hin & Hp)]; [exists []; split; [left; reflexivity | apply is_prefix_nil] | exists p; split; [right; exact Hin | exact Hp]].
Qed.
Lemma sub_paths_pathset : forall E fs P Q, sub_paths P Q = true -> forall tr, pathset E fs P tr -> pathset E fs Q tr.
Proof.
  intros E fs P Q HS tr (p & Hin & Hp). unfold sub_paths in HS. rewrite forallb_forall in HS.
  specialize (HS p Hin). apply existsb_exists in HS as (q & Hq & Hpq).
  exists q. split; [exact Hq|]. eapply is_prefix_trans'; [exact Hp | apply prefixb_sound; exact Hpq].
Qed.
Lemma sd_pathset : forall HOLES D E fs s, nocase s = true -> t_eq (sd HOLES D E fs s) (pathset E fs (paths s)).
Proof. intros HOLES D E fs s Hs tr. apply sd_paths. exact Hs. Qed.
Lemma t_emit_pathset : forall E fs w P, P <> [] ->
  t_eq (t_emit (events E fs w) (pathset E fs P)) (pathset E fs (map (fun p => w ++ p) P)).
Proof.
  intros E fs w P HP tr. unfold t_emit, pathset. split.
  - intros [Hp | (tr' & -> & (p & Hin & Hp))].
    + destruct P as [|p0 P]; [congruence|]. exists (w ++ p0). split; [apply in_map; left; reflexivity|].
      rewrite events_app. apply is_prefix_app_r. exact Hp.
    + exists (w ++ p). split; [apply in_map; exact Hin|]. rewrite events_app. apply is_prefix_app_l. exact Hp.
  - intros (q & Hin & Hq). apply in_map_iff in Hin as (p & <- & Hin).
    rewrite events_app in Hq. apply is_prefix_app_split in Hq as [Hq | (b' & -> & Hq)].
    + left. exact Hq.
    + right. exists b'. split; [reflexivity|]. exists p. auto.
Qed.

Lemma omin_eq : forall a b L, omin a b = Some L -> a = Some L \/ b = Some L.
Proof.
  intros [x|] [y|] L H; cbn [omin] in H; try discriminate; try (injection H as <-); auto.
  destruct (Nat.min_dec x y) as [Hm|Hm]; rewrite Hm; auto.
Qed.
Lemma omin_le_l : forall x b, exists L, omin (Some x) b = Some L /\ (L <= x)%nat.
Proof. intros x [y|]; cbn [omin]; eexists; split; try reflexivity; lia. Qed.
Lemma omin_le_r : forall a y, exists L, omin a (Some y) = Some L /\ (L <= y)%nat.
Proof. intros [x|] y; cbn [omin]; eexists; split; try reflexivity; lia. Qed.

(* [comment removed for export] *)
Lemma hsum_words : forall lv F s SL, hsum lv F s = Some SL -> forall hp, In hp SL -> fst hp = None -> snd hp <> [].
Proof.
  intros lv F s. induction s as [|c|fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; intros SL HS hp Hin Hn; cbn [hsum] in HS; try discriminate.
  - injection HS as <-. destruct Hin as [<-|[]]. cbn. discriminate.
  - injection HS as <-. destruct Hin as [<-|[]]. cbn. discriminate.
  - destruct (hsum lv F s) as [L'|] eqn:HL; [|discriminate].
    destruct (existsb _ L') eqn:HE; [discriminate|]. injection HS as <-.
    apply in_map_iff in Hin as (hp' & <- & Hin'). cbn [fst snd].
    assert (Hn' : fst hp' = None).
    { destruct (fst hp') as [x|] eqn:Hf; [|reflexivity]. exfalso.
      assert (X : existsb (fun hp => match fst hp with Some _ => true | None => false end) L' = true).
      { apply existsb_exists. exists hp'. rewrite Hf. auto. }
      rewrite X in HE. discriminate. }
    pose proof (IH L' eq_refl hp' Hin' Hn') as NE. destruct (snd hp'); [congruence | cbn; discriminate].
  - destruct (hsum lv F a) as [La|] eqn:Ha; [|discriminate]. destruct (hsum lv F b) as [Lb|] eqn:Hb; [|discriminate]. injection HS as <-.
    apply in_flat_map in Hin as (x & Hx & Hin). apply in_map_iff in Hin as (y & <- & Hy). cbn [fst snd] in *.
    assert (Hxn : fst x = None) by (destruct (fst x) as [u|] eqn:Hu; [|reflexivity]; destruct (omin_le_l u (fst y)) as (L0 & HL0 & _); rewrite HL0 in Hn; discriminate).
    pose proof (IHa La eq_refl x Hx Hxn) as NE. destruct (snd x); [congruence | cbn; discriminate].
  - destruct (sdecide F e mid) as [[|]|]; [exact (IHa SL HS hp Hin Hn) | exact (IHb SL HS hp Hin Hn) |].
    destruct (hsum lv F a) as [La|] eqn:Ha; [|discriminate]. destruct (hsum lv F b) as [Lb|] eqn:Hb; [|discriminate]. injection HS as <-.
    apply in_app_iff in Hin as [Hin|Hin]; [exact (IHa La eq_refl hp Hin Hn) | exact (IHb Lb eq_refl hp Hin Hn)].
  - destruct (lv h) as [L|]; [|discriminate]. injection HS as <-. destruct Hin as [<-|[]]. cbn in Hn. discriminate.
Qed.
End WithFP4.


Section SegSound.
Context {fx : FPState}.
  Variable SEGS : list Segment.
  Variables (E : env) (M : word -> option byte) (F : list kentry).
  Hypothesis HF : know_ok SEGS E M F.
  Variable HOLES : nat -> env -> Fs.Fs -> TSet.
  Variable D : TSet.
  Variable fs : Fs.Fs.
  (* [comment removed for export] *)
  Variable RES : nat -> TSet.
  Hypothesis RES_mono : forall L L', (L <= L')%nat -> forall tr, RES L' tr -> RES L tr.
  Hypothesis RES_nil : forall L, RES L [].
  Hypothesis RES_step : forall L, (L < MAXL)%nat -> t_eq (RES L) (t_alt2 (sd HOLES D E fs (alt_shape L)) (RES (S L))).
  (* [comment removed for export] *)
  Variable L0 : nat.
  Variable lv : nat -> option nat.
  Hypothesis HOLES_RES : forall h L, lv h = Some L ->
    exists L', (L0 <= L')%nat /\ (L' <= L)%nat /\ t_eq (HOLES h E fs) (RES L').

  (* [comment removed for export] *)
  Definition bounded (o : option nat) (X : TSet) : Prop :=
    match o with
    | None => forall tr, ~ X tr
    | Some L => (forall tr, RES L tr -> X tr) /\ (forall tr, X tr -> RES L0 tr)
    end.

  Lemma bounded_alt2 : forall a b Xa Xb, bounded a Xa -> bounded b Xb -> bounded (omin a b) (t_alt2 Xa Xb).
  Proof.
    intros [x|] [y|] Xa Xb Ha Hb; cbn [omin bounded] in *; unfold t_alt2.
    - destruct Ha as [Ha1 Ha2], Hb as [Hb1 Hb2]. split.
      + intros tr H. destruct (Nat.min_dec x y) as [Hm|Hm]; rewrite Hm in H; auto.
      + intros tr [H|H]; auto.
    - destruct Ha as [Ha1 Ha2]. split; [intros tr H; auto | intros tr [H|H]; [auto | exfalso; exact (Hb tr H)]].
    - destruct Hb as [Hb1 Hb2]. split; [intros tr H; auto | intros tr [H|H]; [exfalso; exact (Ha tr H) | auto]].
    - intros tr [H|H]; [exact (Ha tr H) | exact (Hb tr H)].
  Qed.

  Lemma hsum_sound : forall s SL, hsum lv F s = Some SL ->
    exists hp X, In hp SL /\ bounded (fst hp) X /\ t_eq (sd HOLES D E fs s) (t_alt2 X (pathset E fs (snd hp))).
  Proof.
    induction s as [|c|fd ps s IH|a IHa b IHb|e mid a IHa b IHb|h|]; intros SL HS; cbn [hsum] in HS; try discriminate; cbn [sd].
    - injection HS as <-. exists (None, [[]]), (fun _ => False). split; [left; reflexivity|]. split; [intros tr H; exact H|].
      intros tr. unfold t_alt2, t_nil. cbn [fst snd]. rewrite pathset_nilcons. split.
      + intros ->. right. left. reflexivity.
      + intros [[]|[->|(p & [] & _)]]. reflexivity.
    - injection HS as <-. exists (None, [[SX c]]), (fun _ => False). split; [left; reflexivity|]. split; [intros tr H; exact H|].
      intros tr. unfold t_alt2, t_exit, t_emit, t_nil, pathset. cbn [fst snd]. split.
      + intros [Hp | (tr' & -> & ->)]; right; exists [SX c]; (split; [left; reflexivity|]); [exact Hp | cbn; auto].
      + intros [[]|(p & [<-|[]] & Hp)]. left. exact Hp.
    - destruct (hsum lv F s) as [L'|] eqn:HL; [|discriminate].
      destruct (existsb _ L') eqn:HE; [discriminate|]. injection HS as <-.
      destruct (IH L' eq_refl) as (hp' & X' & Hin' & HB' & Heq).
      assert (Hn' : fst hp' = None).
      { destruct (fst hp') as [x|] eqn:Hf; [|reflexivity]. exfalso.
        assert (X : existsb (fun hp => match fst hp with Some _ => true | None => false end) L' = true).
        { apply existsb_exists. exists hp'. rewrite Hf. auto. }
        rewrite X in HE. discriminate. }
      rewrite Hn' in HB'. cbn [bounded] in HB'.
      exists (None, map (fun p => sev_of fd ps ++ p) (snd hp')), (fun _ => False).
      split; [apply in_map_iff; exists hp'; auto|]. split; [intros tr H; exact H|].
      rewrite (Wp_events E fs).
      assert (Heq' : t_eq (sd HOLES D E fs s) (pathset E fs (snd hp'))).
      { intros tr. rewrite (Heq tr). unfold t_alt2. split; [intros [H|H]; [exfalso; exact (HB' tr H) | exact H] | intros H; right; exact H]. }
      eapply t_eq_trans; [apply t_eq_emit; exact Heq'|].
      eapply t_eq_trans; [apply t_emit_pathset; exact (hsum_words lv F s L' HL hp' Hin' Hn')|].
      intros tr. unfold t_alt2. cbn [fst snd]. split; [intros H; right; exact H | intros [[]|H]; exact H].
    - destruct (hsum lv F a) as [La|] eqn:Ha; [|discriminate]. destruct (hsum lv F b) as [Lb|] eqn:Hb; [|discriminate]. injection HS as <-.
      destruct (IHa La eq_refl) as (x & Xa & Hx & HBx & Hxe). destruct (IHb Lb eq_refl) as (y & Xb & Hy & HBy & Hye).
      exists (omin (fst x) (fst y), snd x ++ snd y), (t_alt2 Xa Xb). split; [|split].
      + apply in_flat_map. exists x. split; [exact Hx|]. apply in_map_iff. exists y. auto.
      + cbn [fst]. apply bounded_alt2; assumption.
      + eapply t_eq_trans; [apply t_eq_alt2; [exact Hxe | exact Hye]|].
        intros tr. unfold t_alt2. cbn [snd]. rewrite pathset_app. tauto.
    - destruct (sdecide F e mid) as [d|] eqn:Hd.
      + rewrite (sdecide_sound SEGS E M F e mid d HF Hd). destruct d; [exact (IHa SL HS) | exact (IHb SL HS)].
      + destruct (hsum lv F a) as [La|] eqn:Ha; [|discriminate]. destruct (hsum lv F b) as [Lb|] eqn:Hb; [|discriminate]. injection HS as <-.
        destruct (bv_unsigned (edenot E e) <=? mid).
        * destruct (IHa La eq_refl) as (hp & X & Hin & HB & Heq). exists hp, X. split; [apply in_app_iff; left; exact Hin | split; [exact HB | exact Heq]].
        * destruct (IHb Lb eq_refl) as (hp & X & Hin & HB & Heq). exists hp, X. split; [apply in_app_iff; right; exact Hin | split; [exact HB | exact Heq]].
    - destruct (lv h) as [L|] eqn:Hh; [|discriminate]. injection HS as <-.
      destruct (HOLES_RES h L Hh) as (L' & H1 & H2 & Heq).
      exists (Some L, []), (RES L'). split; [left; reflexivity|]. split.
      + cbn [fst bounded]. split; [exact (RES_mono L' L H2) | exact (RES_mono L0 L' H1)].
      + eapply t_eq_trans; [exact Heq|]. intros tr. unfold t_alt2, pathset. cbn [snd]. split; [intros H; left; exact H | intros [H|(p & [] & _)]; exact H].
  Qed.

  (* [comment removed for export] *)
  Lemma alts_res : forall n L, (L + n <= MAXL)%nat -> t_eq (RES L) (t_alt2 (sd HOLES D E fs (alts L n)) (RES (L + n))).
  Proof.
    induction n as [|n IH]; intros L Hn; cbn [alts sd].
    - rewrite Nat.add_0_r. apply t_eq_sym. apply t_alt2_nil_l. apply RES_nil.
    - eapply t_eq_trans; [apply RES_step; unfold MAXL in *; lia|].
      intros tr. pose proof (IH (S L) ltac:(lia) ) as X. rewrite Nat.add_succ_r. rewrite <- Nat.add_succ_l.
      unfold t_alt2 in *. rewrite (X tr). tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma seg1_ok_sound : forall hp X, bounded (fst hp) X -> seg1_ok L0 hp = true ->
    t_eq (t_alt2 X (pathset E fs (snd hp))) (RES L0).
  Proof.
    intros [h P] X HB HS. unfold seg1_ok in HS. cbn [fst snd] in HS, HB. destruct h as [L2|]; [|discriminate].
    destruct HB as [HB1 HB2].
    apply andb_prop in HS as [HS Hreq]. apply andb_prop in HS as [HS Hall]. apply andb_prop in HS as [H1 H2].
    apply Nat.leb_le in H1. apply Nat.leb_le in H2.
    pose proof (alts_res (MAXL - L0) L0 ltac:(unfold MAXL in *; lia)) as ALL.
    pose proof (alts_res (L2 - L0) L0 ltac:(unfold MAXL in *; lia)) as REQ. replace (L0 + (L2 - L0))%nat with L2 in REQ by lia.
    pose proof (sub_paths_pathset E fs _ _ Hall) as SALL. pose proof (sub_paths_pathset E fs _ _ Hreq) as SREQ.
    pose proof (sd_pathset HOLES D E fs (alts L0 (MAXL - L0)) (alts_nocase _ _)) as DALL.
    pose proof (sd_pathset HOLES D E fs (alts L0 (L2 - L0)) (alts_nocase _ _)) as DREQ.
    intros tr. unfold t_alt2. split.
    - intros [HX|HP].
      + exact (HB2 tr HX).
      + apply (ALL tr). left. apply (DALL tr). apply SALL. apply pathset_nilcons. right. exact HP.
    - intros HR. apply (REQ tr) in HR as [HA|HR2].
      + apply (DREQ tr) in HA. apply SREQ in HA. apply pathset_nilcons in HA as [->|HP].
        * left. apply HB1. apply RES_nil.
        * right. exact HP.
      + left. apply HB1. exact HR2.
  Qed.

  Theorem seg_ok_sound : forall s, seg_ok lv L0 F s = true -> t_eq (sd HOLES D E fs s) (RES L0).
  Proof.
    intros s HS. unfold seg_ok in HS. destruct (hsum lv F s) as [SL|] eqn:Hh; [|discriminate].
    destruct (hsum_sound s SL Hh) as (hp & X & Hin & HB & Heq).
    rewrite forallb_forall in HS. eapply t_eq_trans; [exact Heq | apply (seg1_ok_sound hp X HB); apply HS; exact Hin].
  Qed.
End SegSound.

(* [comment removed for export] *)
Section LevelSound.
Context {fx : FPState}.
  Variables (ph : PhdrInfo) (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Variable uid : word.
  Variable hw : word.   (* [comment removed for export] *)
  Hypothesis Hfit : entry_stack_fits sp argv envp.

  (* [comment removed for export] *)
  Lemma look4_input : forall C, in_class C argv fs = true -> look_of C = 4 ->
    exists a0 p c', argv = [a0; p] /\ (length p < 4096)%nat /\ p <> [] /\ p <> Uapi.dot_path /\
                    fs_lookup fs p = Some c' /\ content_of argv fs = c' /\ qlook argv fs = 4.
  Proof.
    intros C HC HL.
    pose proof (look_of_sound ph sp rdraw argv envp fs uid hw Hva Hfit C HC ltac:(lia)) as HLK. rewrite HL in HLK.
    pose proof (qlook_cases argv fs) as Q. clear Hva Hfit.
    destruct argv as [|a0 [|p [|x r]]]; try (rewrite Q in HLK; discriminate).
    destruct Q as [[Hq _]|[[Hq _]|[[Hq _]|[Hq (Hne & Hnd & Hl & c' & Hlk & Hc)]]]]; try (rewrite Hq in HLK; discriminate).
    exists a0, p, c'. repeat split; auto.
  Qed.

  Lemma target4_form : forall C t, look_of C = 4 -> target_of C = Some t -> exists x, t = TOpen x.
  Proof.
    intros C t HL HT. unfold target_of in HT. rewrite HL in HT. cbn -[cbounds clamp Z.leb Z.ltb Z.pow] in HT.
    revert HT. generalize (clamp (cbounds C QFlen) 0 (2 ^ 26)) (cbounds C QRoom) (cbounds C QCnt). intros f room cnt HT.
    repeat match type of HT with (if ?b then _ else _) = _ => destruct b end;
      first [injection HT as <-; eexists; reflexivity | discriminate HT].
  Qed.

  (* [comment removed for export] *)
  Lemma spec_look4 : forall a0 p c', (length p < 4096)%nat -> p <> [] -> p <> Uapi.dot_path -> fs_lookup fs p = Some c' ->
    spec [a0; p] fs = t_alt2 (t_die (msg_cannot_open p) fs) (t_opened c' fs).
  Proof.
    intros a0 p c' Hl Hne Hnd Hlk. cbn [spec].
    destruct (Nat.leb_spec 4096 (length p)); [lia|].
    destruct (list_byte_eqb p []) eqn:He; [apply list_byte_eqb_eq in He; congruence|].
    destruct (list_byte_eqb p dot_path) eqn:Hd; [apply list_byte_eqb_eq in Hd; exfalso; apply Hnd; exact Hd|].
    rewrite Hlk. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem class_pay_sound : forall SEGS L C s E M HOLES D,
    in_class C argv fs = true -> class_pay_ok L C s = true ->
    (forall n, (n < 8)%nat -> ev E n = ev (E0 ph sp rdraw brk0 argv envp uid hw) n) ->
    eb E 1%nat = nth 0 argv [] -> eb E 2%nat = nth 1 argv [] ->
    know_ok SEGS E M (vfacts (variant_of (content_of argv fs))) ->
    t_eq (sd HOLES D E fs s) (t_res L argv fs).
  Proof.
    intros SEGS L C s E M HOLES D HC HS Hev HB1 HB2 HV.
    destruct L as [|L'].
    { cbn [t_res]. eapply class_shape_sound; eassumption. }
    cbn [class_pay_ok] in HS. apply andb_prop in HS as [HL HS]. apply Z.eqb_eq in HL.
    destruct (target_of C) as [t|] eqn:HT; [|discriminate].
    destruct (target4_form C t HL HT) as [x ->].
    destruct (look4_input C HC HL) as (a0 & p & c' & Hargv & Hl & Hne & Hnd & Hlk & Hc & Hq).
    pose proof (target4_sound ph sp rdraw argv envp fs Hva uid hw Hfit C x E HOLES D a0 p c' HC HT Hargv Hq Hlk) as T4.
    assert (HF : know_ok SEGS E M (vfacts (variant_of (content_of argv fs)) ++ facts_of_class C)).
    { apply Forall_app. split; [exact HV | eapply facts_of_class_sound; eassumption]. }
    rewrite Hc in HF.
    assert (RS : forall y, strip (S L') (TOpen x) = Some y ->
              forallb (fun v => negb (vconsistent C v) ||
                 match sresolve (vfacts v ++ facts_of_class C) s with Some s' => shape_equiv s' (shape_of_tgt (tv y v)) | None => false end)%bool variants = true ->
              t_eq (sd HOLES D E fs s) (sd HOLES D E fs (shape_of_tgt (tv y (variant_of c'))))).
    { intros y _ HS'. rewrite forallb_forall in HS'. specialize (HS' (variant_of c')).
      rewrite <- Hc in HS'. specialize (HS' (variant_in argv fs)).
      rewrite (variant_consistent ph sp rdraw argv envp fs Hva uid hw Hfit C HC) in HS'. cbn [negb orb] in HS'. rewrite Hc in HS'.
      destruct (sresolve (vfacts (variant_of c') ++ facts_of_class C) s) as [s'|] eqn:HR; [|discriminate].
      eapply t_eq_trans; [exact (sresolve_sound SEGS E M _ HF HOLES D fs s s' HR)|].
      exact (shape_equiv_sound HOLES D E fs s' _ (sresolve_nocase _ _ _ HR) (shape_of_tgt_nocase _) HS'). }
    destruct L' as [|L'']; cbn [strip] in HS, RS.
    - (* [comment removed for export] *)
      eapply t_eq_trans; [exact (RS _ eq_refl HS)|]. cbn [t_res]. rewrite Hargv, Hlk. exact T4.
    - discriminate HS.
  Qed.

  (* [comment removed for export] *)
  Theorem class_seg_sound : forall SEGS lv L C s E M HOLES D,
    in_class C argv fs = true -> class_seg_ok lv L C s = true ->
    (forall n, (n < 8)%nat -> ev E n = ev (E0 ph sp rdraw brk0 argv envp uid hw) n) ->
    eb E 1%nat = nth 0 argv [] -> eb E 2%nat = nth 1 argv [] ->
    know_ok SEGS E M (vfacts (variant_of (content_of argv fs))) ->
    (forall h L', lv h = Some L' -> exists L'', (L <= L'')%nat /\ (L'' <= L')%nat /\ t_eq (HOLES h E fs) (t_res L'' argv fs)) ->
    t_eq (sd HOLES D E fs s) (t_res L argv fs).
  Proof.
    intros SEGS lv L C s E M HOLES D HC HS Hev HB1 HB2 HV HH.
    unfold class_seg_ok in HS. apply andb_prop in HS as [HL HS]. apply Z.eqb_eq in HL.
    rewrite forallb_forall in HS. specialize (HS (variant_of (content_of argv fs)) (variant_in argv fs)).
    rewrite (variant_consistent ph sp rdraw argv envp fs Hva uid hw Hfit C HC) in HS. cbn [negb orb] in HS.
    assert (HF : know_ok SEGS E M (vfacts (variant_of (content_of argv fs)) ++ facts_of_class C)).
    { apply Forall_app. split; [exact HV | eapply facts_of_class_sound; eassumption]. }
    destruct (look4_input C HC HL) as (a0 & p & c' & Hargv & Hl & Hne & Hnd & Hlk & Hc & Hq).
    refine (seg_ok_sound SEGS E M _ HF HOLES D fs (fun L => t_res L argv fs) _ _ _ L lv HH s HS).
    - (* [comment removed for export] *) intros L1 L2 Hle tr. rewrite Hargv. destruct L1 as [|L1]; destruct L2 as [|L2]; try lia; cbn [t_res]; rewrite ?Hlk; try (intros H; exact H).
      rewrite (spec_look4 a0 p c' Hl Hne Hnd Hlk). intros H. right. exact H.
    - (* [comment removed for export] *) intros L1. apply t_res_nil.
    - (* [comment removed for export] *) intros L1 HL1. rewrite Hargv. destruct L1 as [|L1]; [|unfold MAXL in HL1; lia]; cbn [t_res alt_shape]; rewrite Hlk.
      rewrite (spec_look4 a0 p c' Hl Hne Hnd Hlk). apply t_eq_alt2; [|apply t_eq_refl].
      apply t_eq_sym. apply Wp_die. rewrite Hargv in HB2. apply (den_cannot_open E [a0; p] HB2).
  Qed.
End LevelSound.
