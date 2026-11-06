(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim StdioCore Stdio HeapFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive fkind := KR | KW | KDir | KNull.

Record kfe := mkKfe {
  k_fd : Z;
  k_kind : fkind;
  k_path : list byte;
  k_own : option hptr;
  k_data : option (list byte);   (* [comment removed for export] *)
  k_off : Z
}.

(* [comment removed for export] *)
Definition kfile (kd : fkind) : Prop := kd = KR \/ kd = KW.
Definition knd (e : kfe) : Prop := kfile (k_kind e).
Lemma kfile_KR : kfile KR. Proof. left; reflexivity. Qed.
Lemma kfile_KW : kfile KW. Proof. right; reflexivity. Qed.
Lemma not_kfile_KDir : ~ kfile KDir. Proof. intros [X|X]; discriminate X. Qed.
Lemma not_kfile_KNull : ~ kfile KNull. Proof. intros [X|X]; discriminate X. Qed.
Lemma knd_of_KR e : k_kind e = KR -> knd e. Proof. intros H. unfold knd. rewrite H. exact kfile_KR. Qed.
Lemma knd_of_KW e : k_kind e = KW -> knd e. Proof. intros H. unfold knd. rewrite H. exact kfile_KW. Qed.
Lemma knd_not_KDir e : knd e -> k_kind e <> KDir. Proof. intros [H|H] E; rewrite E in H; discriminate H. Qed.
Lemma knd_not_KNull e : knd e -> k_kind e <> KNull. Proof. intros [H|H] E; rewrite E in H; discriminate H. Qed.
(* [comment removed for export] *)
Ltac kndtac := first [ eapply knd_of_KR; eassumption | eapply knd_of_KW; eassumption
                     | unfold knd, kfile; cbn; first [left; reflexivity | right; reflexivity] ].

Definition mkent (kd : fkind) (p : list byte) (off : word) : FdEntry :=
  match kd with KR => FdFile p off | KW => FdFileW p off | KDir => FdDir | KNull => FdDevNull false true end.
Definition kent (e : kfe) : FdEntry := mkent (k_kind e) (k_path e) (Z_to_bv 64 (k_off e)).

(* [comment removed for export] *)
Definition wkind (path : list byte) : fkind := if path_eqb path devnull_path then KNull else KW.
Lemma wkind_devnull : wkind devnull_path = KNull.
Proof. unfold wkind. rewrite path_eqb_refl. reflexivity. Qed.
Lemma wkind_other path : path <> devnull_path -> wkind path = KW.
Proof. intros NE. unfold wkind. destruct (path_eqb path devnull_path) eqn:E; [apply path_eqb_eq in E; contradiction| reflexivity]. Qed.

(* [comment removed for export] *)
Definition kwr (e : kfe) : Prop := (k_kind e = KW /\ k_data e <> None) \/ k_kind e = KNull.

(* [comment removed for export] *)
Definition FLEN : Z := 2^61.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition kwf (e : kfe) : Prop :=
  3 <= k_fd e < 2^32 /\ 0 <= k_off e /\
  match k_data e with
  | Some d => knd e /\ k_off e <= Z.of_nat (length d) /\ Z.of_nat (length d) <= FLEN /\ (k_kind e = KW -> k_off e = Z.of_nat (length d))
  | None => True
  end.

(* [comment removed for export] *)
Definition kentry (mo : Model) (e : kfe) : Prop :=
  match k_data e with
  | Some d => fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = Some (kent e)
              /\ (knd e -> fs_lookup (m_fs mo) (k_path e) = Some d)
  | None => exists off d, fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = Some (mkent (k_kind e) (k_path e) off)
              /\ (knd e -> fs_lookup (m_fs mo) (k_path e) = Some d /\ bv_unsigned off <= Z.of_nat (length d))
  end.

(* [comment removed for export] *)
Definition fdcls (K : list kfe) (k : word) (en : FdEntry) : Prop :=
  match en with
  | FdChannel _ => bv_unsigned k < 3
  | FdFile p _ => exists e, In e K /\ k_fd e = bv_unsigned k /\ k_kind e = KR /\ k_path e = p
  | FdFileW p _ => exists e, In e K /\ k_fd e = bv_unsigned k /\ k_kind e = KW /\ k_path e = p
  | FdDir => exists e, In e K /\ k_fd e = bv_unsigned k /\ k_kind e = KDir
  | FdDevNull rd wr => exists e, In e K /\ k_fd e = bv_unsigned k /\ k_kind e = KNull /\ rd = false /\ wr = true   (* [comment removed for export] *)
  | _ => False
  end.

(* [comment removed for export] *)
Definition stdx_ok (f : file_st) (fd : Z) : Prop :=
  f_fd f = fd /\ f_chan f = true /\ f_nowr f = false /\ f_rbuf f = [] /\ file_ok f /\ zlength (f_wbuf f) <= f_bufsize f /\ (f_wactive f = false -> f_wbuf f = []).

(* [comment removed for export] *)
Definition fshape (f : file_st) (e : kfe) : Prop :=
  f_chan f = false /\ file_ok f /\ f_fd f = k_fd e /\
  match k_kind e with
  | KW | KNull => f_nowr f = false /\ f_rbuf f = [] /\ zlength (f_wbuf f) <= f_bufsize f /\ (f_wactive f = false -> f_wbuf f = []) /\ f_bufsize f = BUFSIZ
  | KR => f_nord f = false /\ f_wbuf f = [] /\ f_wactive f = false /\ f_bufsize f = BUFSIZ
  | KDir => False
  end.

Definition KP (K : list kfe) : Prop :=
  List.NoDup (map k_fd K)
  /\ (forall e, In e K -> kwf e)
  /\ (forall e e', In e K -> In e' K -> knd e -> knd e' -> k_path e = k_path e' -> e = e')
  /\ (forall e e' h, In e K -> In e' K -> k_own e = Some h -> k_own e' = Some h -> e = e').

Definition CP (K : list kfe) (C : list (list byte * list byte)) : Prop :=
  List.NoDup (map fst C)
  /\ (forall p d, In (p, d) C -> Z.of_nat (length d) <= FLEN /\ forall e, In e K -> knd e -> k_path e <> p).

Definition KM (K : list kfe) (C : list (list byte * list byte)) (mo : Model) : Prop :=
  (forall e, In e K -> kentry mo e)
  /\ (forall p d, In (p, d) C -> fs_lookup (m_fs mo) p = Some d)
  /\ List.NoDup (map fst (m_fds mo))
  /\ (forall k en, In (k, en) (m_fds mo) -> fdcls K k en).

Definition LM (nx : N) (K : list kfe) (l : libc_st hptr) : Prop :=
  stdx_ok (lc_stdout l) 1 /\ stdx_ok (lc_stderr l) 2
  /\ List.NoDup (map fst (lc_files l))
  /\ (forall h f, In (h, f) (lc_files l) -> (h < nx)%N /\
        exists e, In e K /\ k_own e = Some h /\ fshape f e /\ zlength (f_rbuf f) <= k_off e)
  /\ (forall e h, In e K -> k_own e = Some h -> (h < nx)%N).

Definition FI (nx : N) (K : list kfe) (C : list (list byte * list byte)) (l : libc_st hptr) (mo : Model) : Prop :=
  KP K /\ CP K C /\ KM K C mo /\ LM nx K l.

(* [comment removed for export] *)
Definition K_clear (K : list kfe) (p : list byte) : Prop := forall e, In e K -> knd e -> k_path e <> p.

(* [comment removed for export] *)
Definition kdel (fd : Z) (K : list kfe) : list kfe := List.filter (fun e => negb (k_fd e =? fd)) K.
Definition kset (e' : kfe) (K : list kfe) : list kfe := map (fun e => if k_fd e =? k_fd e' then e' else e) K.
Definition kown (h : hptr) (e : kfe) : kfe := mkKfe (k_fd e) (k_kind e) (k_path e) (Some h) (k_data e) (k_off e).
Definition kmove (d : option (list byte)) (off : Z) (e : kfe) : kfe := mkKfe (k_fd e) (k_kind e) (k_path e) (k_own e) d off.
Definition cdel (p : list byte) (C : list (list byte * list byte)) := List.filter (fun pd => negb (path_eqb (fst pd) p)) C.
Fixpoint clookup (C : list (list byte * list byte)) (p : list byte) : option (list byte) :=
  match C with [] => None | (q, d) :: C' => if path_eqb q p then Some d else clookup C' p end.
(* [comment removed for export] *)
Definition cclose (e : kfe) (C : list (list byte * list byte)) :=
  match k_data e, k_kind e with
  | Some d, KR | Some d, KW => (k_path e, d) :: C
  | _, _ => C
  end.
(* [comment removed for export] *)
Definition lrem (e : kfe) (l : libc_st hptr) : libc_st hptr :=
  match k_own e with None => l | Some h => set_files (files_remove N.eqb (lc_files l) h) l end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fd_lookup_In fds k en : fd_lookup fds k = Some en -> In (k, en) fds.
Proof.
  induction fds as [|[k' e'] fds IH]; cbn; [discriminate|].
  destruct (bv_eqb k' k) eqn:E; [apply bv_eqb_eq in E; subst; intros H0; injection H0 as ->; left; reflexivity| intros H0; right; exact (IH H0)].
Qed.

Lemma In_fd_lookup fds k en : List.NoDup (map fst fds) -> In (k, en) fds -> fd_lookup fds k = Some en.
Proof.
  induction fds as [|[k' e'] fds IH]; intros ND Hin; [destruct Hin|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
  cbn. destruct Hin as [E|Hin].
  - injection E as -> ->. rewrite bv_eqb_refl. reflexivity.
  - destruct (bv_eqb k' k) eqn:E; [| exact (IH ND' Hin)].
    apply bv_eqb_eq in E; subst. exfalso. apply NI. apply in_map_iff. exists (k, en). auto.
Qed.

Lemma In_filter_fds (fds : list (word * FdEntry)) fd k en :
  In (k, en) (List.filter (fun p => negb (bv_eqb (fst p) fd)) fds) <-> In (k, en) fds /\ k <> fd.
Proof.
  rewrite filter_In. cbn [fst]. split.
  - intros [Hin Hb]. split; [exact Hin|]. intros ->. rewrite bv_eqb_refl in Hb. discriminate.
  - intros [Hin NE]. split; [exact Hin|]. destruct (bv_eqb k fd) eqn:E; [apply bv_eqb_eq in E; contradiction| reflexivity].
Qed.

Lemma NoDup_filter_fds (fds : list (word * FdEntry)) fd : List.NoDup (map fst fds) -> List.NoDup (map fst (List.filter (fun p => negb (bv_eqb (fst p) fd)) fds)).
Proof.
  induction fds as [|[k e] fds IH]; intros ND; cbn; [constructor|]. inversion ND as [|? ? NI ND']; subst.
  destruct (negb (bv_eqb k fd)); cbn; [| exact (IH ND')]. constructor; [| exact (IH ND')].
  intros Hin. apply NI. apply in_map_iff in Hin as ([k' e'] & E & Hin). cbn in E. subst. apply filter_In in Hin as [Hin _]. apply in_map_iff. exists (k, e'). auto.
Qed.

Lemma NoDup_fd_insert fds fd e : List.NoDup (map fst fds) -> List.NoDup (map fst (fd_insert fds fd e)).
Proof.
  intros ND. unfold fd_insert. cbn. constructor; [| apply NoDup_filter_fds; exact ND].
  intros Hin. apply in_map_iff in Hin as ([k' e'] & E & Hin). cbn in E. subst. apply In_filter_fds in Hin as [_ NE]. exact (NE eq_refl).
Qed.

Lemma NoDup_fd_remove fds fd : List.NoDup (map fst fds) -> List.NoDup (map fst (fd_remove fds fd)).
Proof. intros ND. unfold fd_remove. apply NoDup_filter_fds. exact ND. Qed.

Lemma In_fd_insert fds fd e k en : In (k, en) (fd_insert fds fd e) <-> (k = fd /\ en = e) \/ (In (k, en) fds /\ k <> fd).
Proof.
  unfold fd_insert. cbn. rewrite In_filter_fds. split.
  - intros [E|H]; [injection E as -> ->; left; auto| right; exact H].
  - intros [[-> ->]|H]; [left; reflexivity| right; exact H].
Qed.

Lemma In_fd_remove fds fd k en : In (k, en) (fd_remove fds fd) <-> In (k, en) fds /\ k <> fd.
Proof. unfold fd_remove. apply In_filter_fds. Qed.

(* [comment removed for export] *)
Lemma fd_word k : 0 <= k < 2^32 -> bv_unsigned (Z_to_bv 64 k) = k.
Proof. intros Hk. apply unsigned_lit. lia. Qed.

Lemma fd_eqb a b : 0 <= a < 2^32 -> 0 <= b < 2^32 -> bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros Ha Hb. destruct (Z.eqb_spec a b) as [->|NE]; [apply bv_eqb_refl|].
  apply Bool.not_true_iff_false. intros E. apply bv_eqb_eq in E. apply (f_equal bv_unsigned) in E. rewrite !fd_word in E by lia. exact (NE E).
Qed.

Lemma In_kdel fd K e : In e (kdel fd K) <-> In e K /\ k_fd e <> fd.
Proof.
  unfold kdel. rewrite filter_In. split; intros [H1 H2]; split; auto.
  - intros E. rewrite E, Z.eqb_refl in H2. discriminate.
  - destruct (Z.eqb_spec (k_fd e) fd); [contradiction| reflexivity].
Qed.

Lemma NoDup_kdel fd K : List.NoDup (map k_fd K) -> List.NoDup (map k_fd (kdel fd K)).
Proof.
  induction K as [|e K IH]; intros ND; cbn; [constructor|]. inversion ND as [|? ? NI ND']; subst.
  destruct (negb (k_fd e =? fd)); cbn; [| exact (IH ND')]. constructor; [| exact (IH ND')].
  intros Hin. apply NI. apply in_map_iff in Hin as (e' & E & Hin). apply In_kdel in Hin as [Hin _]. apply in_map_iff. exists e'. auto.
Qed.

Lemma K_fd_inj K e e' : List.NoDup (map k_fd K) -> In e K -> In e' K -> k_fd e = k_fd e' -> e = e'.
Proof.
  induction K as [|x K IH]; intros ND H1 H2 E; [destruct H1|]. inversion ND as [|? ? NI ND']; subst.
  destruct H1 as [<-|H1], H2 as [<-|H2]; [reflexivity| | | exact (IH ND' H1 H2 E)].
  - exfalso. apply NI. rewrite E. apply in_map. exact H2.
  - exfalso. apply NI. rewrite <- E. apply in_map. exact H1.
Qed.

(* [comment removed for export] *)
Lemma kfe_dec_in K x e : List.NoDup (map k_fd K) -> In x K -> In e K -> x = e \/ x <> e.
Proof. intros ND Hx He. destruct (Z.eq_dec (k_fd x) (k_fd e)) as [E|NE]; [left; exact (K_fd_inj K x e ND Hx He E)| right; congruence]. Qed.

Lemma In_kset e' K x : In x (kset e' K) <-> (exists e, In e K /\ k_fd e = k_fd e' /\ x = e') \/ (In x K /\ k_fd x <> k_fd e').
Proof.
  unfold kset. rewrite in_map_iff. split.
  - intros (e & E & He). destruct (Z.eqb_spec (k_fd e) (k_fd e')) as [EQ|NE]; subst; [left; exists e; auto| right; auto].
  - intros [(e & He & E & ->)|[Hx NE]].
    + exists e. rewrite E, Z.eqb_refl. auto.
    + exists x. rewrite (proj2 (Z.eqb_neq _ _) NE). auto.
Qed.

Lemma map_fd_kset e' K : (exists e, In e K /\ k_fd e = k_fd e') \/ True -> map k_fd (kset e' K) = map k_fd K.
Proof.
  intros _. unfold kset. rewrite map_map. apply map_ext_in. intros e _. destruct (Z.eqb_spec (k_fd e) (k_fd e')); [symmetry; assumption| reflexivity].
Qed.

Lemma In_cdel p C q d : In (q, d) (cdel p C) <-> In (q, d) C /\ q <> p.
Proof.
  unfold cdel. rewrite filter_In. cbn [fst]. split.
  - intros [H1 H2]. split; [exact H1|]. intros ->. rewrite path_eqb_refl in H2. discriminate.
  - intros [H1 NE]. split; [exact H1|]. destruct (path_eqb q p) eqn:E; [apply path_eqb_eq in E; contradiction| reflexivity].
Qed.

Lemma NoDup_cdel p C : List.NoDup (map fst C) -> List.NoDup (map fst (cdel p C)).
Proof.
  induction C as [|[q d] C IH]; intros ND; cbn; [constructor|]. inversion ND as [|? ? NI ND']; subst.
  destruct (negb (path_eqb q p)); cbn; [| exact (IH ND')]. constructor; [| exact (IH ND')].
  intros Hin. apply NI. apply in_map_iff in Hin as ([q' d'] & E & Hin). cbn in E; subst. apply (In_cdel p C q d') in Hin as [Hin _]. apply in_map_iff. exists (q, d'). auto.
Qed.

Lemma clookup_In C p d : clookup C p = Some d -> In (p, d) C.
Proof.
  induction C as [|[q d'] C IH]; cbn; [discriminate|]. destruct (path_eqb q p) eqn:E.
  - apply path_eqb_eq in E; subst. intros H; injection H as ->. left; reflexivity.
  - intros H. right. exact (IH H).
Qed.

Lemma In_files_remove (fs : list (hptr * file_st)) h hf : List.NoDup (map fst fs) -> In hf (files_remove N.eqb fs h) <-> In hf fs /\ fst hf <> h.
Proof.
  induction fs as [|[k v] fs IH]; intros ND; cbn; [tauto|]. inversion ND as [|? ? NI ND']; subst.
  destruct (N.eqb_spec k h) as [->|NE].
  - split.
    + intros Hin. split; [right; exact Hin|]. intros E. apply NI. rewrite <- E. apply in_map_iff. exists hf. auto.
    + intros [[<-|Hin] NE]; [cbn in NE; congruence| exact Hin].
  - cbn. rewrite (IH ND'). split.
    + intros [<-|[Hin NE']]; [split; [left; reflexivity| cbn; exact NE]| auto].
    + intros [[<-|Hin] NE']; [left; reflexivity| right; auto].
Qed.

Lemma NoDup_files_remove (fs : list (hptr * file_st)) h : List.NoDup (map fst fs) -> List.NoDup (map fst (files_remove N.eqb fs h)).
Proof.
  induction fs as [|[k v] fs IH]; intros ND; cbn; [constructor|]. inversion ND as [|? ? NI ND']; subst.
  destruct (N.eqb k h); [exact ND'|]. cbn. constructor; [| exact (IH ND')].
  intros Hin. apply NI. apply in_map_iff in Hin as ([k' v'] & E & Hin). apply (In_files_remove fs h (k', v') ND') in Hin as [Hin _]. cbn in E. subst. apply in_map_iff. exists (k, v'). auto.
Qed.

Lemma In_files_update (fs : list (hptr * file_st)) h f hf : List.NoDup (map fst fs) ->
  In hf (files_update N.eqb fs h f) <-> (In hf fs /\ fst hf <> h) \/ (hf = (h, f) /\ In h (map fst fs)).
Proof.
  induction fs as [|[k v] fs IH]; intros ND; cbn; [tauto|]. inversion ND as [|? ? NI ND']; subst.
  destruct (N.eqb_spec k h) as [->|NE]; cbn.
  - split.
    + intros [<-|Hin]; [right; auto|]. left. split; [right; exact Hin|]. intros E. apply NI. rewrite <- E. apply in_map_iff. exists hf. auto.
    + intros [[[<-|Hin] NE]|[-> _]]; [cbn in NE; congruence| right; exact Hin| left; reflexivity].
  - rewrite (IH ND'). split.
    + intros [<-|[[Hin NE']|[-> Hin]]]; [left; split; [left; reflexivity| cbn; exact NE]| left; auto| right; auto].
    + intros [[[<-|Hin] NE']|[-> [E|Hin]]]; [left; reflexivity| right; left; auto| congruence| right; right; auto].
Qed.

Lemma map_fst_files_update (fs : list (hptr * file_st)) h f : map fst (files_update N.eqb fs h f) = map fst fs.
Proof. induction fs as [|[k v] fs IH]; cbn; [reflexivity|]. destruct (N.eqb k h); cbn; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma files_lookup_In (fs : list (hptr * file_st)) h f : files_lookup N.eqb fs h = Some f -> In (h, f) fs.
Proof.
  induction fs as [|[k v] fs IH]; cbn; [discriminate|]. destruct (N.eqb_spec k h) as [->|NE].
  - intros H; injection H as ->. left; reflexivity.
  - intros H. right. exact (IH H).
Qed.

Lemma In_files_lookup (fs : list (hptr * file_st)) h f : List.NoDup (map fst fs) -> In (h, f) fs -> files_lookup N.eqb fs h = Some f.
Proof.
  induction fs as [|[k v] fs IH]; intros ND Hin; [destruct Hin|]. inversion ND as [|? ? NI ND']; subst. cbn.
  destruct Hin as [E|Hin].
  - injection E as -> ->. rewrite N.eqb_refl. reflexivity.
  - destruct (N.eqb_spec k h) as [->|NE]; [| exact (IH ND' Hin)]. exfalso. apply NI. apply in_map_iff. exists (h, f). auto.
Qed.

Lemma NoDup_snoc {A} (l : list A) x : List.NoDup l -> ~ In x l -> List.NoDup (l ++ [x]).
Proof.
  induction l as [|y l IH]; intros ND NI; cbn; [constructor; [intros []| constructor]|]. inversion ND as [|? ? NY ND']; subst.
  constructor; [| apply IH; [exact ND'| intros H; apply NI; right; exact H]].
  rewrite in_app_iff. cbn. intros [H|[E|[]]]; [exact (NY H)| apply NI; left; exact (eq_sym E)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Facts.
Variables (nx : N) (K : list kfe) (C : list (list byte * list byte)) (l : libc_st hptr) (mo : Model).
Hypothesis H : FI nx K C l mo.

#[using="nx C l mo H"] Lemma FI_KP : KP K. Proof. exact (proj1 H). Qed.
#[using="nx l mo H"] Lemma FI_CP : CP K C. Proof. exact (proj1 (proj2 H)). Qed.
#[using="nx l H"] Lemma FI_KM : KM K C mo. Proof. exact (proj1 (proj2 (proj2 H))). Qed.
#[using="C mo H"] Lemma FI_LM : LM nx K l. Proof. exact (proj2 (proj2 (proj2 H))). Qed.

#[using="nx C l mo H"] Lemma FI_kwf e : In e K -> kwf e. Proof. exact (proj1 (proj2 FI_KP) e). Qed.
#[using="nx C l H"] Lemma FI_kentry e : In e K -> kentry mo e. Proof. exact (proj1 FI_KM e). Qed.
#[using="nx K C l H"] Lemma FI_nodup_fds : List.NoDup (map fst (m_fds mo)). Proof. exact (proj1 (proj2 (proj2 FI_KM))). Qed.
#[using="nx C l H"] Lemma FI_fdcls k en : In (k, en) (m_fds mo) -> fdcls K k en. Proof. exact (proj2 (proj2 (proj2 FI_KM)) k en). Qed.
#[using="nx K l H"] Lemma FI_C p d : In (p, d) C -> fs_lookup (m_fs mo) p = Some d. Proof. exact (proj1 (proj2 FI_KM) p d). Qed.
#[using="nx K C mo H"] Lemma FI_stdout : stdx_ok (lc_stdout l) 1. Proof. exact (proj1 FI_LM). Qed.
#[using="nx K C mo H"] Lemma FI_stderr : stdx_ok (lc_stderr l) 2. Proof. exact (proj1 (proj2 FI_LM)). Qed.
#[using="nx K C mo H"] Lemma FI_nodup_files : List.NoDup (map fst (lc_files l)). Proof. exact (proj1 (proj2 (proj2 FI_LM))). Qed.
#[using="C mo H"] Lemma FI_file h f : In (h, f) (lc_files l) -> (h < nx)%N /\ exists e, In e K /\ k_own e = Some h /\ fshape f e /\ zlength (f_rbuf f) <= k_off e.
Proof. exact (proj1 (proj2 (proj2 (proj2 FI_LM))) h f). Qed.
#[using="C l mo H"] Lemma FI_owner e h : In e K -> k_own e = Some h -> (h < nx)%N.
Proof. exact (proj2 (proj2 (proj2 (proj2 FI_LM))) e h). Qed.

(* [comment removed for export] *)
#[using="nx C l H"] Lemma FI_lookup e : In e K -> exists off, fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = Some (mkent (k_kind e) (k_path e) off)
  /\ (k_data e <> None -> off = Z_to_bv 64 (k_off e)).
Proof.
  intros He. pose proof (FI_kentry e He) as KE. unfold kentry in KE. destruct (k_data e) as [d|].
  - exists (Z_to_bv 64 (k_off e)). split; [exact (proj1 KE)| reflexivity].
  - destruct KE as (off & d & L & _). exists off. split; [exact L| intros X; exfalso; exact (X eq_refl)].
Qed.

#[using="nx C l H"] Lemma FI_lookup_exact e d : In e K -> k_data e = Some d ->
  fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = Some (kent e) /\ (knd e -> fs_lookup (m_fs mo) (k_path e) = Some d).
Proof. intros He Hd. pose proof (FI_kentry e He) as KE. unfold kentry in KE. rewrite Hd in KE. exact KE. Qed.

(* [comment removed for export] *)
#[using="nx C l H"] Lemma FI_file_of e : In e K -> knd e -> exists off d,
  fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = Some (mkent (k_kind e) (k_path e) off) /\
  fs_lookup (m_fs mo) (k_path e) = Some d /\ bv_unsigned off <= Z.of_nat (length d) /\
  (forall d0, k_data e = Some d0 -> d = d0 /\ off = Z_to_bv 64 (k_off e) /\ bv_unsigned off = k_off e).
Proof.
  intros He Hn. pose proof (FI_kentry e He) as KE. pose proof (FI_kwf e He) as (R & O & W). unfold kentry in KE.
  destruct (k_data e) as [d|].
  - destruct KE as [L F]. destruct W as (_ & LE & FL & _). exists (Z_to_bv 64 (k_off e)), d. split; [exact L|]. split; [exact (F Hn)|].
    assert (U : bv_unsigned (Z_to_bv 64 (k_off e)) = k_off e) by (apply unsigned_lit; unfold FLEN in FL; lia).
    rewrite U. split; [exact LE|]. intros d0 E; injection E as ->. auto.
  - destruct KE as (off & d & L & F). destruct (F Hn) as [F1 F2]. exists off, d. split; [exact L|]. split; [exact F1|]. split; [exact F2|]. intros; discriminate.
Qed.

(* [comment removed for export] *)
#[using="nx C l H"] Lemma FI_fd_cases k en : fd_lookup (m_fds mo) k = Some en ->
  (exists c, en = FdChannel c /\ bv_unsigned k < 3) \/ (exists e, In e K /\ k_fd e = bv_unsigned k).
Proof.
  intros L. pose proof (FI_fdcls k en (fd_lookup_In _ _ _ L)) as CL. unfold fdcls in CL.
  destruct en; try (destruct CL; fail); [left; eexists; split; [reflexivity| exact CL]| right| right| right| right];
    destruct CL as (e & He & E & _); exists e; auto.
Qed.

(* [comment removed for export] *)
#[using="nx C l mo H"] Lemma FI_fd_inj e e' : In e K -> In e' K -> k_fd e = k_fd e' -> e = e'.
Proof. intros. eapply K_fd_inj; eauto. exact (proj1 FI_KP). Qed.
#[using="nx C l mo H"] Lemma FI_own_inj e e' h : In e K -> In e' K -> k_own e = Some h -> k_own e' = Some h -> e = e'.
Proof. intros. eapply (proj2 (proj2 (proj2 FI_KP))); eauto. Qed.

(* [comment removed for export] *)
#[using="C mo H"] Lemma FI_handle h f : files_lookup N.eqb (lc_files l) h = Some f ->
  exists e, In e K /\ k_own e = Some h /\ fshape f e /\ zlength (f_rbuf f) <= k_off e /\ (h < nx)%N.
Proof.
  intros L. destruct (FI_file h f (files_lookup_In _ _ _ L)) as [Hh (e & He & Ho & Sh & LE)]. exists e. auto 6.
Qed.

(* [comment removed for export] *)
#[using="nx C l H"] Lemma FI_names_path p : K_clear K p -> fd_names_path (m_fds mo) p = false.
Proof.
  intros HC.
  assert (G : forall fds, (forall k en, In (k, en) fds -> In (k, en) (m_fds mo)) -> fd_names_path fds p = false).
  { induction fds as [|[k en] fds IH]; intros SUB; [reflexivity|]. cbn.
    assert (IH' : fd_names_path fds p = false) by (apply IH; intros; apply SUB; right; assumption).
    pose proof (FI_fdcls k en (SUB _ _ (or_introl eq_refl))) as CL.
    assert (CASE : forall q kd, kfile kd -> (exists e, In e K /\ k_fd e = bv_unsigned k /\ k_kind e = kd /\ k_path e = q) -> path_eqb p q || fd_names_path fds p = false).
    { intros q kd Hkd (e & He & _ & Ek & Ep). rewrite IH', orb_false_r. destruct (path_eqb p q) eqn:E; [| reflexivity].
      apply path_eqb_eq in E. exfalso. apply (HC e He); [unfold knd; rewrite Ek; exact Hkd| congruence]. }
    destruct en; try exact IH'; try (destruct CL; fail); (eapply CASE; [| exact CL]); [exact kfile_KR| exact kfile_KW]. }
  apply G. auto.
Qed.

(* [comment removed for export] *)
#[using="nx C l H"] Lemma FI_fresh_fd fd : 0 <= fd < 2^32 -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None -> forall e, In e K -> k_fd e <> fd.
Proof. intros R L e He E. destruct (FI_lookup e He) as (off & L' & _). rewrite E, L in L'. discriminate. Qed.

End Facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma FI_same nx K C l mo mo' : m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> FI nx K C l mo -> FI nx K C l mo'.
Proof.
  intros EF ES (A & B & (M1 & M2 & M3 & M4) & D). split; [exact A|]. split; [exact B|]. split; [| exact D].
  split; [| split; [intros p d Hp; rewrite ES; exact (M2 p d Hp)| split; [rewrite EF; exact M3| intros k en; rewrite EF; exact (M4 k en)]]].
  intros e He. pose proof (M1 e He) as KE. unfold kentry in *. rewrite EF, ES. exact KE.
Qed.

Lemma FI_vm_only nx K C l mo mo' : vm_only mo mo' -> FI nx K C l mo -> FI nx K C l mo'.
Proof. intros (EF & ES & _) H. exact (FI_same _ _ _ _ _ _ EF ES H). Qed.

(* [comment removed for export] *)
Lemma FI_libc nx K C l l' mo :
  stdx_ok (lc_stdout l') 1 -> stdx_ok (lc_stderr l') 2 -> lc_files l' = lc_files l -> FI nx K C l mo -> FI nx K C l' mo.
Proof.
  intros S1 S2 EF (A & B & M & (_ & _ & D3 & D4 & D5)). split; [exact A|]. split; [exact B|]. split; [exact M|].
  split; [exact S1|]. split; [exact S2|]. rewrite EF. exact (conj D3 (conj D4 D5)).
Qed.

Lemma FI_errno nx K C l e mo : FI nx K C l mo -> FI nx K C (set_errno_lc e l) mo.
Proof. intros H. apply (FI_libc nx K C l); [exact (FI_stdout _ _ _ _ _ H)| exact (FI_stderr _ _ _ _ _ H)| reflexivity| exact H]. Qed.

Lemma FI_stdout_upd nx K C l f mo : stdx_ok f 1 -> FI nx K C l mo -> FI nx K C (set_stdout f l) mo.
Proof. intros Hf H. apply (FI_libc nx K C l); [exact Hf| exact (FI_stderr _ _ _ _ _ H)| reflexivity| exact H]. Qed.

Lemma FI_stderr_upd nx K C l f mo : stdx_ok f 2 -> FI nx K C l mo -> FI nx K C (set_stderr f l) mo.
Proof. intros Hf H. apply (FI_libc nx K C l); [exact (FI_stdout _ _ _ _ _ H)| exact Hf| reflexivity| exact H]. Qed.

Lemma FI_mono_nx nx nx' K C l mo : (nx <= nx')%N -> FI nx K C l mo -> FI nx' K C l mo.
Proof.
  intros LE (A & B & M & (D1 & D2 & D3 & D4 & D5)). split; [exact A|]. split; [exact B|]. split; [exact M|].
  split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split.
  - intros h f Hin. destruct (D4 h f Hin) as [Hh X]. split; [lia| exact X].
  - intros e h He Ho. pose proof (D5 e h He Ho). lia.
Qed.

(* [comment removed for export] *)
Lemma FI_open nx K C l mo mo' fd kd path (dopt : option (list byte)) :
  FI nx K C l mo -> 3 <= fd < 2^32 ->
  fd_lookup (m_fds mo) (Z_to_bv 64 fd) = None ->
  K_clear K path ->
  m_fds mo' = fd_insert (m_fds mo) (Z_to_bv 64 fd) (mkent kd path (Z_to_bv 64 0)) ->
  (forall q, q <> path -> fs_lookup (m_fs mo') q = fs_lookup (m_fs mo) q) ->
  (kfile kd -> match dopt with
               | Some d => fs_lookup (m_fs mo') path = Some d /\ Z.of_nat (length d) <= FLEN /\ (kd = KW -> d = [])
               | None => fs_lookup (m_fs mo') path <> None
               end) ->
  (~ kfile kd -> dopt = None) ->      (* [comment removed for export] *)
  FI nx (K ++ [mkKfe fd kd path None dopt 0]) (cdel path C) l mo'.
Proof.
  intros H Hfd Hfresh HC EF EFS NEW DIR. pose proof H as ((A1 & A2 & A3 & A4) & (B1 & B2) & (M1 & M2 & M3 & M4) & (D1 & D2 & D3 & D4 & D5)).
  set (en := mkKfe fd kd path None dopt 0).
  assert (Wfd : bv_unsigned (Z_to_bv 64 fd) = fd) by (apply fd_word; lia).
  pose proof (FI_fresh_fd _ _ _ _ _ H fd ltac:(lia) Hfresh) as NK.
  assert (LK : forall e x, In e K -> fd_lookup (m_fds mo') (Z_to_bv 64 (k_fd e)) = Some x <-> fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = Some x).
  { intros e x He. pose proof (A2 e He) as (R & _). rewrite EF, fd_lookup_insert, fd_eqb by lia.
    replace (fd =? k_fd e) with false by (symmetry; apply Z.eqb_neq; intros E; exact (NK e He (eq_sym E))). tauto. }
  assert (FS : forall e, In e K -> knd e -> fs_lookup (m_fs mo') (k_path e) = fs_lookup (m_fs mo) (k_path e)).
  { intros e He Hn. apply EFS. exact (HC e He Hn). }
  assert (INK : forall e, In e (K ++ [en]) <-> In e K \/ e = en).
  { intros e. rewrite in_app_iff. cbn. intuition. }
  split; [| split; [| split]].
  - (* [comment removed for export] *) split; [| split; [| split]].
    + rewrite map_app. cbn. apply NoDup_snoc; [exact A1|]. intros Hin. apply in_map_iff in Hin as (e & E & He). exact (NK e He E).
    + intros e He. apply INK in He as [He| ->]; [exact (A2 e He)|]. unfold kwf; cbn. split; [lia|]. split; [lia|].
      destruct dopt as [d|]; [| exact I].
      assert (KF : kfile kd) by (destruct kd; [exact kfile_KR| exact kfile_KW| discriminate (DIR not_kfile_KDir)| discriminate (DIR not_kfile_KNull)]).
      destruct (NEW KF) as (_ & FL & Z0). split; [exact KF|]. split; [lia|]. split; [exact FL|]. intros E. rewrite (Z0 E). reflexivity.
    + intros e e' He He' Hn Hn' EP. apply INK in He as [He| ->]; apply INK in He' as [He'| ->]; [exact (A3 e e' He He' Hn Hn' EP)| | | reflexivity].
      * exfalso. exact (HC e He Hn EP).
      * exfalso. exact (HC e' He' Hn' (eq_sym EP)).
    + intros e e' h He He' O O'. apply INK in He as [He| ->]; apply INK in He' as [He'| ->]; [exact (A4 e e' h He He' O O')| cbn in O'; discriminate| cbn in O; discriminate| reflexivity].
  - (* [comment removed for export] *) split; [apply NoDup_cdel; exact B1|]. intros p d Hp. apply In_cdel in Hp as [Hp NE]. destruct (B2 p d Hp) as [FL CL]. split; [exact FL|].
    intros e He Hn. apply INK in He as [He| ->]; [exact (CL e He Hn)| cbn; congruence].
  - (* [comment removed for export] *) split; [| split; [| split]].
    + intros e He. apply INK in He as [He| ->].
      * pose proof (M1 e He) as KE. unfold kentry in *. destruct (k_data e) as [d|].
        -- destruct KE as [L F]. split; [apply (LK e _ He); exact L| intros Hn; rewrite (FS e He Hn); exact (F Hn)].
        -- destruct KE as (off & d & L & F). exists off, d. split; [apply (LK e _ He); exact L| intros Hn; rewrite (FS e He Hn); exact (F Hn)].
      * unfold kentry; cbn. assert (L0 : fd_lookup (m_fds mo') (Z_to_bv 64 fd) = Some (mkent kd path (Z_to_bv 64 0))) by (rewrite EF, fd_lookup_insert, bv_eqb_refl; reflexivity).
        destruct dopt as [d|].
        -- split; [exact L0|]. intros Hn. exact (proj1 (NEW Hn)).
        -- exists (Z_to_bv 64 0). destruct kd.
           ++ destruct (fs_lookup (m_fs mo') path) as [d|] eqn:EL; [| exfalso; exact (NEW kfile_KR eq_refl)]. exists d. split; [exact L0|]. intros _. split; [reflexivity| rewrite unsigned_lit by lia; lia].
           ++ destruct (fs_lookup (m_fs mo') path) as [d|] eqn:EL; [| exfalso; exact (NEW kfile_KW eq_refl)]. exists d. split; [exact L0|]. intros _. split; [reflexivity| rewrite unsigned_lit by lia; lia].
           ++ exists []. split; [exact L0|]. intros Hn. exfalso. exact (not_kfile_KDir Hn).
           ++ exists []. split; [exact L0|]. intros Hn. exfalso. exact (not_kfile_KNull Hn).
    + intros p d Hp. apply In_cdel in Hp as [Hp NE]. rewrite (EFS p NE). exact (M2 p d Hp).
    + rewrite EF. apply NoDup_fd_insert. exact M3.
    + intros k x Hin. rewrite EF in Hin. apply In_fd_insert in Hin as [[-> ->]|[Hin NE]].
      * unfold fdcls. rewrite Wfd. destruct kd; cbn; exists en; rewrite INK; cbn; auto 8.
      * pose proof (M4 k x Hin) as CL. unfold fdcls in *. destruct x; try exact CL; destruct CL as (e & He & R); exists e; rewrite INK; auto.
  - (* [comment removed for export] *) split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split.
    + intros h f Hin. destruct (D4 h f Hin) as [Hh (e & He & X)]. split; [exact Hh|]. exists e. rewrite INK. auto.
    + intros e h He Ho. apply INK in He as [He| ->]; [exact (D5 e h He Ho)| cbn in Ho; discriminate].
Qed.

(* [comment removed for export] *)
Lemma FI_close nx K C l mo mo' e :
  FI nx K C l mo -> In e K ->
  m_fds mo' = fd_remove (m_fds mo) (Z_to_bv 64 (k_fd e)) -> m_fs mo' = m_fs mo ->
  FI nx (kdel (k_fd e) K) (cclose e C) (lrem e l) mo'.
Proof.
  intros H He EF ES. pose proof H as ((A1 & A2 & A3 & A4) & (B1 & B2) & (M1 & M2 & M3 & M4) & (D1 & D2 & D3 & D4 & D5)).
  pose proof (A2 e He) as (Re & _).
  assert (LK : forall e' x, In e' K -> k_fd e' <> k_fd e -> fd_lookup (m_fds mo') (Z_to_bv 64 (k_fd e')) = Some x <-> fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e')) = Some x).
  { intros e' x He' NE. pose proof (A2 e' He') as (R & _). rewrite EF, fd_lookup_remove, fd_eqb by lia. replace (k_fd e =? k_fd e') with false by (symmetry; apply Z.eqb_neq; congruence). tauto. }
  assert (LF : forall h f, In (h, f) (lc_files (lrem e l)) -> In (h, f) (lc_files l) /\ k_own e <> Some h).
  { intros h f Hin. unfold lrem in Hin. destruct (k_own e) as [h0|] eqn:EO; [| split; [exact Hin| discriminate]].
    cbn in Hin. apply (In_files_remove _ _ _ D3) in Hin as [Hin NE]. cbn in NE. split; [exact Hin| congruence]. }
  assert (INC : forall p d, In (p, d) (cclose e C) <-> In (p, d) C \/ (k_data e = Some d /\ knd e /\ p = k_path e)).
  { intros p d. unfold cclose, knd. destruct (k_data e) as [d0|]; [destruct (k_kind e)|]; cbn.
    - split; [intros [E|Hin]; [injection E as E1 E2; subst; right; split; [reflexivity| split; [exact kfile_KR| reflexivity]]| left; exact Hin]| intros [Hin|(E & _ & ->)]; [right; exact Hin| injection E as ->; left; reflexivity]].
    - split; [intros [E|Hin]; [injection E as E1 E2; subst; right; split; [reflexivity| split; [exact kfile_KW| reflexivity]]| left; exact Hin]| intros [Hin|(E & _ & ->)]; [right; exact Hin| injection E as ->; left; reflexivity]].
    - split; [intros Hin; left; exact Hin| intros [Hin|(_ & NE & _)]; [exact Hin| exfalso; exact (not_kfile_KDir NE)]].
    - split; [intros Hin; left; exact Hin| intros [Hin|(_ & NE & _)]; [exact Hin| exfalso; exact (not_kfile_KNull NE)]].
    - split; [intros Hin; left; exact Hin| intros [Hin|(E & _)]; [exact Hin| discriminate]]. }
  split; [| split; [| split]].
  - split; [apply NoDup_kdel; exact A1|]. split; [intros e' He'; apply In_kdel in He' as [He' _]; exact (A2 e' He')|].
    split; [intros e1 e2 H1 H2; apply In_kdel in H1 as [H1 _]; apply In_kdel in H2 as [H2 _]; exact (A3 e1 e2 H1 H2)|].
    intros e1 e2 h H1 H2; apply In_kdel in H1 as [H1 _]; apply In_kdel in H2 as [H2 _]; exact (A4 e1 e2 h H1 H2).
  - split.
    + unfold cclose. destruct (k_data e) as [d0|] eqn:ED; [| exact B1].
      assert (NI : ~ In (k_path e) (map fst C)).
      { intros Hin. apply in_map_iff in Hin as ([p d] & E & Hp). cbn in E; subst. destruct (B2 _ _ Hp) as [_ CL]. apply (CL e He); [| reflexivity].
        pose proof (A2 e He) as (_ & _ & W). rewrite ED in W. exact (proj1 W). }
      destruct (k_kind e); cbn; [constructor; [exact NI| exact B1]| constructor; [exact NI| exact B1]| exact B1| exact B1].
    + intros p d Hp. apply INC in Hp as [Hp|(ED & Hn & ->)].
      * destruct (B2 p d Hp) as [FL CL]. split; [exact FL|]. intros e' He' Hn'. apply In_kdel in He' as [He' _]. exact (CL e' He' Hn').
      * pose proof (A2 e He) as (_ & _ & W). rewrite ED in W. destruct W as (_ & _ & FL & _). split; [exact FL|].
        intros e' He' Hn' EP. apply In_kdel in He' as [He' NE]. apply NE. f_equal. exact (A3 e' e He' He Hn' Hn EP).
  - split; [| split; [| split]].
    + intros e' He'. apply In_kdel in He' as [He' NE]. pose proof (M1 e' He') as KE. unfold kentry in *. rewrite ES. destruct (k_data e') as [d|].
      * destruct KE as [L F]. split; [apply (LK e' _ He' NE); exact L| exact F].
      * destruct KE as (off & d & L & F). exists off, d. split; [apply (LK e' _ He' NE); exact L| exact F].
    + intros p d Hp. rewrite ES. apply INC in Hp as [Hp|(ED & Hn & ->)]; [exact (M2 p d Hp)|].
      pose proof (M1 e He) as KE. unfold kentry in KE. rewrite ED in KE. exact (proj2 KE Hn).
    + rewrite EF. apply NoDup_fd_remove. exact M3.
    + intros k x Hin. rewrite EF in Hin. apply In_fd_remove in Hin as [Hin NE]. pose proof (M4 k x Hin) as CL.
      assert (NE' : bv_unsigned k <> k_fd e) by (intros E; apply NE; rewrite <- E, Z_to_bv_bv_unsigned; reflexivity).
      unfold fdcls in *. destruct x; try exact CL; destruct CL as (e' & He' & E1 & E2); exists e'; (split; [apply In_kdel; split; [exact He'| congruence]| auto]).
  - split; [unfold lrem; destruct (k_own e); exact D1|]. split; [unfold lrem; destruct (k_own e); exact D2|].
    split; [unfold lrem; destruct (k_own e); [cbn; apply NoDup_files_remove; exact D3| exact D3]|].
    split.
    + intros h f Hin. destruct (LF h f Hin) as [Hin' NO]. destruct (D4 h f Hin') as [Hh (e' & He' & Ho & Sh & LE)]. split; [exact Hh|].
      assert (NE : k_fd e' <> k_fd e). { intros E. apply NO. rewrite <- Ho. f_equal. exact (K_fd_inj K e e' A1 He He' (eq_sym E)). }
      exists e'. split; [apply In_kdel; auto| auto].
    + intros e' h He' Ho. apply In_kdel in He' as [He' _]. exact (D5 e' h He' Ho).
Qed.

(* [comment removed for export] *)
Lemma FI_advance nx K C l l' mo mo' e e' newoff :
  FI nx K C l mo -> In e K -> knd e ->
  k_fd e' = k_fd e -> k_kind e' = k_kind e -> k_path e' = k_path e -> k_own e' = k_own e -> kwf e' ->
  m_fds mo' = fd_insert (m_fds mo) (Z_to_bv 64 (k_fd e)) (mkent (k_kind e) (k_path e) newoff) ->
  (forall q, q <> k_path e -> fs_lookup (m_fs mo') q = fs_lookup (m_fs mo) q) ->
  (match k_data e' with
   | Some d' => newoff = Z_to_bv 64 (k_off e') /\ fs_lookup (m_fs mo') (k_path e) = Some d'
   | None => exists d, fs_lookup (m_fs mo') (k_path e) = Some d /\ bv_unsigned newoff <= Z.of_nat (length d)
   end) ->
  lc_stdout l' = lc_stdout l -> lc_stderr l' = lc_stderr l -> List.NoDup (map fst (lc_files l')) ->
  (forall h f', In (h, f') (lc_files l') -> exists f, In (h, f) (lc_files l) /\
      (forall e0, fshape f e0 -> fshape f' e0) /\
      (k_own e = Some h -> zlength (f_rbuf f') <= k_off e') /\
      (k_own e <> Some h -> zlength (f_rbuf f') <= zlength (f_rbuf f))) ->
  FI nx (kset e' K) C l' mo'.
Proof.
  intros H He Hn Efd Ekd Ep Eo W EF EFS NEW SO SE ND LF.
  pose proof H as ((A1 & A2 & A3 & A4) & (B1 & B2) & (M1 & M2 & M3 & M4) & (D1 & D2 & D3 & D4 & D5)).
  pose proof (A2 e He) as (Re & _).
  assert (INK : forall x, In x (kset e' K) <-> (x = e' \/ (In x K /\ k_fd x <> k_fd e))).
  { intros x. rewrite In_kset, Efd. split.
    - intros [(e0 & _ & _ & ->)|X]; [left; reflexivity| right; exact X].
    - intros [->|X]; [left; exists e; auto| right; exact X]. }
  assert (BACK : forall x, In x (kset e' K) -> exists x0, In x0 K /\ k_fd x0 = k_fd x /\ k_kind x0 = k_kind x /\ k_path x0 = k_path x /\ k_own x0 = k_own x /\ (x0 = e -> x = e') /\ (x0 <> e -> x = x0)).
  { intros x Hx. apply INK in Hx as [->|[Hx NE]].
    - exists e. rewrite Efd, Ekd, Ep, Eo. repeat split; auto. intros X; exfalso; exact (X eq_refl).
    - exists x. repeat split; auto. intros ->. exfalso. exact (NE eq_refl). }
  assert (LK : forall x off, In x K -> k_fd x <> k_fd e -> fd_lookup (m_fds mo') (Z_to_bv 64 (k_fd x)) = Some off <-> fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd x)) = Some off).
  { intros x off Hx NE. pose proof (A2 x Hx) as (R & _). rewrite EF, fd_lookup_insert, fd_eqb by lia. replace (k_fd e =? k_fd x) with false by (symmetry; apply Z.eqb_neq; congruence). tauto. }
  assert (LE0 : fd_lookup (m_fds mo') (Z_to_bv 64 (k_fd e)) = Some (mkent (k_kind e) (k_path e) newoff)) by (rewrite EF, fd_lookup_insert, bv_eqb_refl; reflexivity).
  assert (FS : forall x, In x K -> k_fd x <> k_fd e -> knd x -> fs_lookup (m_fs mo') (k_path x) = fs_lookup (m_fs mo) (k_path x)).
  { intros x Hx NE Hnx. apply EFS. intros EP. apply NE. f_equal. exact (A3 x e Hx He Hnx Hn EP). }
  split; [| split; [| split]].
  - split; [| split; [| split]].
    + rewrite map_fd_kset by (right; exact I). exact A1.
    + intros x Hx. apply INK in Hx as [->|[Hx _]]; [exact W| exact (A2 x Hx)].
    + intros x y Hx Hy Hnx Hny EP. destruct (BACK x Hx) as (x0 & Hx0 & Fx & Kx & Px & Ox & Xe & Xn). destruct (BACK y Hy) as (y0 & Hy0 & Fy & Ky & Py & Oy & Ye & Yn).
      assert (x0 = y0) as E0. { apply (A3 x0 y0 Hx0 Hy0); [unfold knd in *; congruence| unfold knd in *; congruence| congruence]. }
      subst y0. destruct (kfe_dec_in K x0 e A1 Hx0 He) as [->|NE0]; [rewrite (Xe eq_refl), (Ye eq_refl); reflexivity| rewrite (Xn NE0), (Yn NE0); reflexivity].
    + intros x y h Hx Hy Ox' Oy'. destruct (BACK x Hx) as (x0 & Hx0 & Fx & Kx & Px & Ox & Xe & Xn). destruct (BACK y Hy) as (y0 & Hy0 & Fy & Ky & Py & Oy & Ye & Yn).
      assert (x0 = y0) as E0 by (apply (A4 x0 y0 h Hx0 Hy0); congruence).
      subst y0. destruct (kfe_dec_in K x0 e A1 Hx0 He) as [->|NE0]; [rewrite (Xe eq_refl), (Ye eq_refl); reflexivity| rewrite (Xn NE0), (Yn NE0); reflexivity].
  - split; [exact B1|]. intros p d Hp. destruct (B2 p d Hp) as [FL CL]. split; [exact FL|]. intros x Hx Hnx.
    destruct (BACK x Hx) as (x0 & Hx0 & _ & Kx & Px & _). rewrite <- Px. apply (CL x0 Hx0). unfold knd in *; congruence.
  - split; [| split; [| split]].
    + intros x Hx. apply INK in Hx as [->|[Hx NE]].
      * unfold kentry. rewrite Efd, Ep. unfold kent. rewrite Ekd, Ep. destruct (k_data e') as [d'|].
        -- destruct NEW as [-> F]. split; [exact LE0| intros _; exact F].
        -- destruct NEW as (d & F & LE). exists newoff, d. split; [exact LE0| intros _; exact (conj F LE)].
      * pose proof (M1 x Hx) as KE. unfold kentry in *. destruct (k_data x) as [d|].
        -- destruct KE as [L F]. split; [apply (LK x _ Hx NE); exact L| intros Hnx; rewrite (FS x Hx NE Hnx); exact (F Hnx)].
        -- destruct KE as (off & d & L & F). exists off, d. split; [apply (LK x _ Hx NE); exact L| intros Hnx; rewrite (FS x Hx NE Hnx); exact (F Hnx)].
    + intros p d Hp. destruct (B2 p d Hp) as [_ CL]. rewrite EFS; [exact (M2 p d Hp)|]. intros EP. exact (CL e He Hn (eq_sym EP)).
    + rewrite EF. apply NoDup_fd_insert. exact M3.
    + intros k x Hin. rewrite EF in Hin. apply In_fd_insert in Hin as [[-> ->]|[Hin NE]].
      * unfold fdcls. rewrite fd_word by lia. destruct (k_kind e) eqn:EK; cbn; [| | exfalso; exact (knd_not_KDir e Hn EK)| exfalso; exact (knd_not_KNull e Hn EK)]; exists e'; rewrite INK; rewrite Efd, Ekd, Ep; auto 6.
      * pose proof (M4 k x Hin) as CL. assert (NE' : bv_unsigned k <> k_fd e) by (intros E; apply NE; rewrite <- E, Z_to_bv_bv_unsigned; reflexivity).
        unfold fdcls in *. destruct x; try exact CL; destruct CL as (x0 & Hx0 & E1 & E2); exists x0; rewrite INK; (split; [right; split; [exact Hx0| congruence]| auto]).
  - split; [rewrite SO; exact D1|]. split; [rewrite SE; exact D2|]. split; [exact ND|]. split.
    + intros h f' Hin. destruct (LF h f' Hin) as (f & Hf & SH & OWN & OTH). destruct (D4 h f Hf) as [Hh (x & Hx & Ho & Sh & LE)]. split; [exact Hh|].
      destruct (kfe_dec_in K x e A1 Hx He) as [->|NE].
      * exists e'. rewrite INK. split; [left; reflexivity|]. rewrite Eo. split; [exact Ho|]. split; [| exact (OWN Ho)].
        destruct Sh as (S1 & S2 & S3 & S4). unfold fshape. rewrite Efd, Ekd. exact (SH e (conj S1 (conj S2 (conj S3 S4)))).
      * assert (NEf : k_fd x <> k_fd e) by (intros E; apply NE; exact (K_fd_inj K x e A1 Hx He E)).
        exists x. rewrite INK. split; [right; auto|]. split; [exact Ho|]. split; [exact (SH _ Sh)|].
        assert (NO : k_own e <> Some h) by (intros E2; apply NE; symmetry; exact (A4 e x h He Hx E2 Ho)).
        pose proof (OTH NO). lia.
    + intros x h Hx Ox. destruct (BACK x Hx) as (x0 & Hx0 & _ & _ & _ & Ox0 & _). rewrite <- Ox0 in Ox. exact (D5 x0 h Hx0 Ox).
Qed.

(* [comment removed for export] *)
Lemma FI_unlink nx K C l mo mo' p :
  FI nx K C l mo -> K_clear K p -> m_fds mo' = m_fds mo -> m_fs mo' = fs_remove (m_fs mo) p ->
  FI nx K (cdel p C) l mo'.
Proof.
  intros H HC EF ES. pose proof H as (A & (B1 & B2) & (M1 & M2 & M3 & M4) & D).
  split; [exact A|]. split; [| split; [| exact D]].
  - split; [apply NoDup_cdel; exact B1|]. intros q d Hq. apply In_cdel in Hq as [Hq _]. exact (B2 q d Hq).
  - split; [| split; [| split; [rewrite EF; exact M3| intros k en; rewrite EF; exact (M4 k en)]]].
    + intros e He. pose proof (M1 e He) as KE. unfold kentry in *. rewrite EF, ES. destruct (k_data e) as [d|].
      * destruct KE as [L F]. split; [exact L|]. intros Hn. rewrite fs_lookup_remove_other by (exact (HC e He Hn)). exact (F Hn).
      * destruct KE as (off & d & L & F). exists off, d. split; [exact L|]. intros Hn. rewrite fs_lookup_remove_other by (exact (HC e He Hn)). exact (F Hn).
    + intros q d Hq. apply In_cdel in Hq as [Hq NE]. rewrite ES, fs_lookup_remove_other by exact NE. exact (M2 q d Hq).
Qed.

(* [comment removed for export] *)
Lemma FI_adopt nx nx' K C l mo e h f :
  FI nx K C l mo -> In e K -> k_own e = None -> (nx <= nx')%N -> (h < nx')%N ->
  ~ In h (map fst (lc_files l)) -> (forall x, In x K -> k_own x <> Some h) ->
  fshape f e -> zlength (f_rbuf f) <= k_off e ->
  FI nx' (kset (kown h e) K) C (set_files ((h, f) :: lc_files l) l) mo.
Proof.
  intros H He Ho LEX Hh NI NOWN Sh LE. pose proof H as ((A1 & A2 & A3 & A4) & (B1 & B2) & (M1 & M2 & M3 & M4) & (D1 & D2 & D3 & D4 & D5)).
  set (e' := kown h e).
  assert (INK : forall x, In x (kset e' K) <-> (x = e' \/ (In x K /\ x <> e))).
  { intros x. rewrite In_kset. cbn. split.
    - intros [(e0 & He0 & E & ->)|[Hx NE]]; [left; reflexivity| right; split; [exact Hx| congruence]].
    - intros [->|[Hx NE]]; [left; exists e; auto| right; split; [exact Hx| intros E; apply NE; exact (K_fd_inj K x e A1 Hx He E)]]. }
  assert (SAME : forall P : kfe -> Prop, (forall x, P x <-> P (mkKfe (k_fd x) (k_kind x) (k_path x) (k_own e') (k_data x) (k_off x))) -> P e -> P e') by (intros P HP; apply HP).
  split; [| split; [| split]].
  - split; [| split; [| split]].
    + rewrite map_fd_kset by (right; exact I). exact A1.
    + intros x Hx. apply INK in Hx as [->|[Hx _]]; [| exact (A2 x Hx)]. pose proof (A2 e He) as W. exact W.
    + intros x y Hx Hy Hnx Hny EP. apply INK in Hx as [->|[Hx NEx]]; apply INK in Hy as [->|[Hy NEy]]; [reflexivity| | | exact (A3 x y Hx Hy Hnx Hny EP)].
      * exfalso. apply NEy. exact (A3 y e Hy He Hny Hnx (eq_sym EP)).
      * exfalso. apply NEx. exact (A3 x e Hx He Hnx Hny EP).
    + intros x y h0 Hx Hy Ox Oy. apply INK in Hx as [->|[Hx NEx]]; apply INK in Hy as [->|[Hy NEy]]; [reflexivity| | | exact (A4 x y h0 Hx Hy Ox Oy)].
      * cbn in Ox. injection Ox as <-. exfalso. exact (NOWN y Hy Oy).
      * cbn in Oy. injection Oy as <-. exfalso. exact (NOWN x Hx Ox).
  - split; [exact B1|]. intros p d Hp. destruct (B2 p d Hp) as [FL CL]. split; [exact FL|]. intros x Hx Hnx. apply INK in Hx as [->|[Hx _]]; [exact (CL e He Hnx)| exact (CL x Hx Hnx)].
  - split; [| split; [exact M2| split; [exact M3|]]].
    + intros x Hx. apply INK in Hx as [->|[Hx _]]; [| exact (M1 x Hx)]. pose proof (M1 e He) as KE. exact KE.
    + intros k en Hin. pose proof (M4 k en Hin) as CL. unfold fdcls in *.
      destruct en; try exact CL; destruct CL as (x & Hx & R); (destruct (kfe_dec_in K x e A1 Hx He) as [->|NE]; [exists e'; rewrite INK; split; [left; reflexivity| exact R]| exists x; rewrite INK; split; [right; auto| exact R]]).
  - split; [exact D1|]. split; [exact D2|]. split; [cbn; constructor; [exact NI| exact D3]|]. split.
    + intros h0 f0 Hin. destruct Hin as [E|Hin].
      * injection E as <- <-. split; [exact Hh|]. exists e'. rewrite INK. split; [left; reflexivity|]. split; [reflexivity|]. split; [exact Sh| exact LE].
      * destruct (D4 h0 f0 Hin) as [Hh0 (x & Hx & Ox & Shx & LEx)]. split; [lia|]. exists x. rewrite INK. split; [| auto].
        right. split; [exact Hx|]. intros ->. rewrite Ho in Ox. discriminate.
    + intros x h0 Hx Ox. apply INK in Hx as [->|[Hx _]]; [cbn in Ox; injection Ox as <-; exact Hh|]. pose proof (D5 x h0 Hx Ox). lia.
Qed.

(* [comment removed for export] *)
Lemma FI_store nx K C l mo e h f0 f :
  FI nx K C l mo -> In (h, f0) (lc_files l) -> In e K -> k_own e = Some h ->
  fshape f e -> zlength (f_rbuf f) <= k_off e ->
  FI nx K C (set_files (files_update N.eqb (lc_files l) h f) l) mo.
Proof.
  intros H Hin He Ho Sh LE. pose proof H as (A & B & M & (D1 & D2 & D3 & D4 & D5)). split; [exact A|]. split; [exact B|]. split; [exact M|].
  split; [exact D1|]. split; [exact D2|]. split; [cbn; rewrite map_fst_files_update; exact D3|]. split; [| exact D5].
  intros h' f' Hin'. cbn in Hin'. apply (In_files_update _ _ _ _ D3) in Hin' as [[Hin' NE]|[E _]].
  - exact (D4 h' f' Hin').
  - injection E as -> ->. destruct (D4 h f0 Hin) as [Hh _]. split; [exact Hh|]. exists e. auto.
Qed.

(* [comment removed for export] *)
Lemma FI_owner_file nx K C l mo e h f :
  FI nx K C l mo -> In e K -> k_own e = Some h -> In (h, f) (lc_files l) -> fshape f e /\ zlength (f_rbuf f) <= k_off e.
Proof.
  intros H He Ho Hin. destruct (FI_file _ _ _ _ _ H h f Hin) as [_ (x & Hx & Ox & Sh & LE)].
  pose proof (FI_own_inj _ _ _ _ _ H x e h Hx He Ox Ho) as ->. exact (conj Sh LE).
Qed.

(* [comment removed for export] *)
Lemma FI_init nx mo :
  List.NoDup (map fst (m_fds mo)) ->
  (forall k en, In (k, en) (m_fds mo) -> exists c, en = FdChannel c /\ bv_unsigned k < 3) ->
  FI nx [] [] libc_init mo.
Proof.
  intros ND CH. split; [| split; [| split]].
  - split; [constructor|]. split; [intros ? []|]. split; [intros ? ? []| intros ? ? ? []].
  - split; [constructor| intros ? ? []].
  - split; [intros ? []|]. split; [intros ? ? []|]. split; [exact ND|]. intros k en Hin. destruct (CH k en Hin) as (c & -> & Hk). exact Hk.
  - unfold LM, libc_init, stdx_ok, stdout_init, stderr_init, file_ok, BUFSIZ, zlength. cbn. split; [repeat split; (reflexivity || lia || (intros; reflexivity))|]. split; [repeat split; (reflexivity || lia || (intros; reflexivity))|].
    split; [constructor|]. split; [intros ? ? []| intros ? ? []].
Qed.
