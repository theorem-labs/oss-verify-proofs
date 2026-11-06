(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Namei.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore Stdio HeapFull Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UBase.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Mem Exec RelSpecMm.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MSafe STree Malloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Fmt.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require StartupFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapDrive HeapSim NodeSim ProgSim.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require EntryCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module UNodes.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes RelSpec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import Prelim Monad StdioCore Stdio HeapFull Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require UFile UBase. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UFile OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

#[local] Notation PS := (PState fheap hptr).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fnode {A} (n : node) (dec : resp -> option A)
    (P : libc_st hptr -> Model -> Prop) (Q : A -> libc_st hptr -> Model -> Prop) : Prop :=
  forall l mo, P l mo -> minv mo ->
    nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ Q a l mo'.

(* [comment removed for export] *)
Lemma unode_lift {A} n dec (P : libc_st hptr -> Model -> Prop) (Q : A -> libc_st hptr -> Model -> Prop)
      (g : libc_st hptr -> libc_st hptr) (W : libc_st hptr -> option hptr -> Prop) :
  fnode n dec P Q ->
  unode n dec (fun (s : PS) mo => P (g (ps_libc s)) mo /\ W (ps_libc s) (ps_outfile s))
              (fun a (s : PS) mo => Q a (g (ps_libc s)) mo /\ W (ps_libc s) (ps_outfile s)).
Proof.
  intros H s mo [HP HW] MI. destruct (H _ _ HP MI) as [Hs Hk]. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk _ _ _ Hst) as (a & Ha & HQ). exists a. auto.
Qed.

Lemma fnode_post {A} n dec P (Q Q' : A -> libc_st hptr -> Model -> Prop) :
  fnode n dec P Q -> (forall a l mo, Q a l mo -> Q' a l mo) -> fnode n dec P Q'.
Proof.
  intros H HQ l mo HP MI. destruct (H l mo HP MI) as [Hs Hk]. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk _ _ _ Hst) as (a & Ha & X). exists a. split; [exact Ha| apply HQ; exact X].
Qed.

Lemma fnode_pre {A} n dec (P P' : libc_st hptr -> Model -> Prop) (Q : A -> libc_st hptr -> Model -> Prop) :
  fnode n dec P' Q -> (forall l mo, P l mo -> P' l mo) -> fnode n dec P Q.
Proof. intros H HP l mo X MI. exact (H l mo (HP _ _ X) MI). Qed.

(* [comment removed for export] *)
Lemma bv_add_lits a b : (Z_to_bv 64 a + Z_to_bv 64 b)%bv = Z_to_bv 64 (a + b).
Proof.
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma unsigned_add_le (x : word) k : 0 <= k -> bv_unsigned (x + Z_to_bv 64 k)%bv <= bv_unsigned x + k.
Proof.
  intros Hk. rewrite bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap.
  pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2^64) in *.
  etransitivity; [apply Z.mod_le; [| lia]| apply Z.add_le_mono_l; apply Z.mod_le; lia].
  pose proof (Z.mod_pos_bound k (2^64) ltac:(lia)). lia.
Qed.

Lemma length_file_read_le d off count :
  0 <= off -> 0 <= count < 2^64 -> off <= Z.of_nat (length d) -> Z.of_nat (length d) < 2^64 ->
  Z.of_nat (length (file_read d (Z_to_bv 64 off) (Z_to_bv 64 count))) <= Z.of_nat (length d) - off.
Proof.
  intros Ho Hc Hle Hd. rewrite file_read_unguarded, length_firstn, length_skipn. unfold word_to_nat. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma kset_self K e : In e K -> List.NoDup (map k_fd K) -> kset e K = K.
Proof.
  intros He ND. unfold kset. rewrite <- (map_id K) at 2. apply map_ext_in. intros x Hx.
  destruct (Z.eqb_spec (k_fd x) (k_fd e)) as [E|NE]; [| reflexivity]. exact (K_fd_inj K e x ND He Hx (eq_sym E)).
Qed.

Section Nodes.
Variables (nx : N) (K : list kfe) (C : list (list byte * list byte)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma fn_ioctl fd req :
  fnode (NIoctl fd req) dec_ioctl (FI nx K C) (fun r l mo => FI nx K C l mo /\ exists e, r = SErr e).
Proof.
  intros l mo H MI. split; [exact I|]. intros rsp mo' evs Hst.
  destruct (nstep_dec_ioctl _ _ _ _ _ _ Hst) as (e & Hd & -> & -> & _). exists (SErr e). split; [exact Hd|]. split; [exact H| exists e; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fn_writev fd bufs :
  Z.of_nat (length (concat bufs)) < 2^64 ->
  fnode (NWritev fd bufs) (dec_writev (Z.of_nat (length (concat bufs)))) (FI nx K C)
        (fun k l mo => FI nx K C l mo /\ ((length (concat bufs) = 0%nat /\ k = 0) \/ 1 <= k <= Z.of_nat (length (concat bufs)))).
Proof.
  intros Hl l mo H MI. split; [exact I|]. intros rsp mo' evs Hst.
  destruct (nstep_dec_writev _ _ _ _ _ _ Hl Hst) as (k & Hk & Hd & -> & _). exists k. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma fn_open path :
  K_clear K path ->
  fnode (NOpen path) dec_open (FI nx K C)
        (fun r l mo => match r with
           | SErr e => FI nx K C l mo /\ 1 <= e <= 4095
           | SVal fd => 3 <= fd <= 4096 /\ exists kd, kd <> KW /\ FI nx (K ++ [mkKfe fd kd path None None 0]) (cdel path C) l mo
           end).
Proof.
  intros HC l mo H MI. split; [exact I|]. intros rsp mo' evs Hst.
  destruct (nstep_dec_open _ _ _ _ _ MI Hst) as (_ & a & Hd & X). exists a. split; [exact Hd|]. destruct a as [e|fd].
  { destruct X as [-> R]. auto. }
  - destruct X as (Efd & R & Fresh & ent & Hent & ->). split; [exact R|].
    assert (NF : path <> [] /\ (path_max <=? length path)%nat = false).
    { destruct Hst as [_ Y]. destruct (path_max <=? length path)%nat eqn:EL.
      - destruct Y as [E _]. exfalso.
        pose proof Hd as Hd'. rewrite E in Hd'. unfold dec_open in Hd'. rewrite dec_plain_err in Hd' by (unfold ENAMETOOLONG; lia). discriminate.
      - split; [| reflexivity]. intros ->. destruct Y as [E _]. pose proof Hd as Hd'. rewrite E in Hd'. unfold dec_open in Hd'. rewrite dec_plain_err in Hd' by (unfold State.ENOENT; lia). discriminate. }
    destruct Hent as [-> | ->].
    + exists KDir. split; [discriminate|]. eapply (FI_open nx K C l mo); [exact H| lia| exact Fresh| exact HC| rewrite m_fds_with_fds; reflexivity| intros; rewrite m_fs_with_fds; reflexivity| intros X; exfalso; exact (not_kfile_KDir X)| intros _; reflexivity].
    + exists KR. split; [discriminate|].
      assert (EX : fs_lookup (m_fs mo) path <> None).
      { destruct Hst as [_ Y]. rewrite (proj2 NF) in Y. destruct path as [|c p']; [exfalso; exact (proj1 NF eq_refl)|].
        destruct (path_eqb (c :: p') dot_path) eqn:ED.
        - (* [comment removed for export] *)
          destruct Y as [(e & HIn & E & _)|(_ & E & E2)].
          + exfalso. pose proof Hd as Hd'. rewrite E in Hd'. unfold dec_open in Hd'. rewrite dec_plain_err in Hd' by (apply openat_errnos_range; exact HIn). discriminate.
          + exfalso. apply (f_equal m_fds) in E2. rewrite !m_fds_with_fds in E2. rewrite <- Efd in E2.
            apply (f_equal (fun fds => fd_lookup fds (Z_to_bv 64 fd))) in E2. rewrite !fd_lookup_insert, bv_eqb_refl in E2. discriminate.
        - destruct (fs_lookup (m_fs mo) (c :: p')); [discriminate|]. destruct Y as [E _].
          exfalso. pose proof Hd as Hd'. rewrite E in Hd'. unfold dec_open in Hd'. rewrite dec_plain_err in Hd' by (unfold State.ENOENT; lia). discriminate. }
      eapply (FI_open nx K C l mo); [exact H| lia| exact Fresh| exact HC| rewrite m_fds_with_fds; reflexivity| intros; rewrite m_fs_with_fds; reflexivity| intros _; rewrite m_fs_with_fds; exact EX| intros _; reflexivity].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fn_open_known path d :
  K_clear K path -> clookup C path = Some d -> path <> dot_path ->
  fnode (NOpen path) dec_open (FI nx K C)
        (fun r l mo => match r with
           | SErr e => FI nx K C l mo /\ 1 <= e <= 4095
           | SVal fd => 3 <= fd <= 4096 /\ FI nx (K ++ [mkKfe fd KR path None (Some d) 0]) (cdel path C) l mo
           end).
Proof.
  intros HC HCd ND l mo H MI. split; [exact I|]. intros rsp mo' evs Hst.
  pose proof (FI_C _ _ _ _ _ H path d (clookup_In _ _ _ HCd)) as FS.
  pose proof (proj1 (proj2 (FI_CP _ _ _ _ _ H) path d (clookup_In _ _ _ HCd))) as FL.
  destruct (nstep_dec_open _ _ _ _ _ MI Hst) as (_ & a & Hd & X). exists a. split; [exact Hd|]. destruct a as [e|fd].
  { destruct X as [-> R]. auto. }
  - destruct X as (Efd & R & Fresh & ent & Hent & ->). split; [exact R|].
    assert (Hent' : ent = FdFile path (Z_to_bv 64 0)).
    { destruct Hst as [_ Y]. destruct (path_max <=? length path)%nat.
      { destruct Y as [E _]. exfalso. pose proof Hd as Hd'. rewrite E in Hd'. unfold dec_open in Hd'. rewrite dec_plain_err in Hd' by (unfold ENAMETOOLONG; lia). discriminate. }
      destruct path as [|c p']. { destruct Y as [E _]. exfalso. pose proof Hd as Hd'. rewrite E in Hd'. unfold dec_open in Hd'. rewrite dec_plain_err in Hd' by (unfold State.ENOENT; lia). discriminate. }
      destruct (path_eqb (c :: p') dot_path) eqn:ED. { apply path_eqb_eq in ED. exfalso. exact (ND ED). }
      rewrite FS in Y. destruct Y as [(e & HIn & E & _)|(_ & _ & E2)].
      + exfalso. pose proof Hd as Hd'. rewrite E in Hd'. unfold dec_open in Hd'. rewrite dec_plain_err in Hd' by (apply openat_errnos_range; exact HIn). discriminate.
      + apply (f_equal m_fds) in E2. rewrite !m_fds_with_fds in E2. rewrite <- Efd in E2. apply (f_equal (fun fds => fd_lookup fds (Z_to_bv 64 fd))) in E2.
        rewrite !fd_lookup_insert, bv_eqb_refl in E2. injection E2 as E2. exact E2. }
    subst ent. eapply (FI_open nx K C l mo); [exact H| lia| exact Fresh| exact HC| rewrite m_fds_with_fds; reflexivity| intros; rewrite m_fs_with_fds; reflexivity| | intros X; exfalso; exact (X kfile_KR)].
    intros _. cbn. rewrite m_fs_with_fds. split; [exact FS|]. split; [exact FL| intros; discriminate].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fn_openw path mode (track : bool) :
  K_clear K path -> (path = devnull_path -> track = false) ->
  fnode (NOpenW path mode) dec_openw (FI nx K C)
        (fun r l mo => match r with
           | SErr e => FI nx K C l mo /\ 1 <= e <= 4095
           | SVal fd => 3 <= fd <= 4096
               /\ FI nx (K ++ [mkKfe fd (wkind path) path None (if track then Some [] else None) 0]) (cdel path C) l mo
               /\ (path <> devnull_path -> fs_under (m_fs mo) path = false)
           end).
Proof.
  intros HC TRK l mo H MI. split; [exact I|]. intros rsp mo' evs Hst.
  destruct (nstep_dec_openw _ _ _ _ _ _ MI Hst) as (_ & a & Hd & X). exists a. split; [exact Hd|]. destruct a as [e|fd].
  { destruct X as [-> R]. auto. }
  destruct X as (_ & R & Fresh & _ & _ & [[-> ->]|(NDV & WD & _ & ->)]); (split; [exact R|]).
  - (* [comment removed for export] *)
    rewrite (TRK eq_refl), wkind_devnull. split; [| intros X; exfalso; exact (X eq_refl)].
    eapply (FI_open nx K C l mo); [exact H| lia| exact Fresh| exact HC| rewrite m_fds_with_fds; reflexivity| intros; rewrite m_fs_with_fds; reflexivity| intros X; exfalso; exact (not_kfile_KNull X)| intros _; reflexivity].
  - rewrite (wkind_other _ NDV). split.
    + eapply (FI_open nx K C l mo); [exact H| lia| exact Fresh| exact HC| rewrite m_fds_with_fds; reflexivity| | | intros X; exfalso; exact (X kfile_KW)].
      * intros q NE. rewrite m_fs_with_fds, m_fs_with_fs. apply fs_lookup_set_other. exact NE.
      * intros _. rewrite m_fs_with_fds, m_fs_with_fs. destruct track.
        -- split; [apply fs_lookup_set_same|]. split; [unfold FLEN; cbn; lia| reflexivity].
        -- rewrite fs_lookup_set_same. discriminate.
    + intros _. rewrite (nstep_fs_under _ _ _ _ _ Hst path). unfold write_dirref in WD. apply orb_false_elim in WD. exact (proj2 WD).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma fn_close e :
  In e K ->
  fnode (NClose (k_fd e)) dec_close (FI nx K C)
        (fun r l mo => r = SVal 0 /\ FI nx (kdel (k_fd e) K) (cclose e C) (lrem e l) mo).
Proof.
  intros He l mo H MI. split; [exact I|]. intros rsp mo' evs Hst.
  destruct (FI_lookup _ _ _ _ _ H e He) as (off & L & _).
  destruct (nstep_dec_close _ _ _ _ _ Hst) as (_ & a & Hd & X). exists a. split; [exact Hd|]. destruct a as [err|v].
  - destruct X as (_ & _ & N0). rewrite L in N0. discriminate.
  - destruct X as (-> & _ & ->). split; [reflexivity|]. eapply FI_close; [exact H| exact He| rewrite m_fds_with_fds; reflexivity| rewrite m_fs_with_fds; reflexivity].
Qed.

#[using="Type"] Lemma fn_close_ok e :
  In e K ->
  fnode (NClose (k_fd e)) dec_close_ok (FI nx K C)
        (fun _ l mo => FI nx (kdel (k_fd e) K) (cclose e C) (lrem e l) mo).
Proof.
  intros He l mo H MI. destruct (fn_close e He l mo H MI) as [Hs Hk]. split; [exact Hs|].
  intros rsp mo' evs Hst. destruct (Hk _ _ _ Hst) as (a & Ha & -> & X). exists tt. unfold dec_close_ok. rewrite Ha. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition read_post (e : kfe) (count : Z) (a : read_ans) (l : libc_st hptr) (mo : Model) : Prop :=
  match a with
  | RdErr _ => k_kind e <> KR /\ FI nx K C l mo
  | RdData bs => k_kind e = KR /\ Z.of_nat (length bs) <= count /\
      match k_data e with
      | Some d => bs = file_read d (Z_to_bv 64 (k_off e)) (Z_to_bv 64 count) /\
                  k_off e + Z.of_nat (length bs) <= Z.of_nat (length d) /\
                  FI nx (kset (kmove (Some d) (k_off e + Z.of_nat (length bs)) e) K) C l mo
      | None => FI nx K C l mo
      end
  end.

#[using="Type"] Lemma read_core e count l mo mo' p off data bs :
  FI nx K C l mo -> In e K -> 0 <= count < 2^64 ->
  fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = Some (FdFile p off) ->
  fs_lookup (m_fs mo) p = Some data ->
  bs = file_read data off (Z_to_bv 64 count) ->
  mo' = with_fds (fd_insert (m_fds mo) (Z_to_bv 64 (k_fd e)) (FdFile p (off + len_word bs)%bv)) mo ->
  read_post e count (RdData bs) l mo'.
Proof.
  intros H He Hc L FS Ebs ->.
  destruct (FI_lookup _ _ _ _ _ H e He) as (off0 & L0 & EX). rewrite L in L0.
  assert (KD : k_kind e = KR /\ p = k_path e /\ off = off0).
  { unfold mkent in L0. destruct (k_kind e); [injection L0 as -> ->; auto| discriminate| discriminate| discriminate]. }
  destruct KD as (KD & -> & ->). pose proof (FI_kwf _ _ _ _ _ H e He) as (R & O & W).
  destruct (FI_file_of _ _ _ _ _ H e He ltac:(kndtac)) as (off1 & d1 & L1 & FS1 & LE1 & EXA).
  rewrite L in L1. unfold mkent in L1. rewrite KD in L1. injection L1 as <-. rewrite FS in FS1. injection FS1 as <-.
  assert (LENB : Z.of_nat (length bs) <= count).
  { subst bs. rewrite file_read_unguarded, length_firstn. unfold word_to_nat. rewrite unsigned_lit by lia. lia. }
  assert (LENF : Z.of_nat (length bs) <= Z.of_nat (length data) - bv_unsigned off0).
  { subst bs. rewrite file_read_unguarded, length_firstn, length_skipn. unfold word_to_nat. rewrite unsigned_lit by lia. lia. }
  pose proof (bv_unsigned_in_range 64 off0) as RO. change (bv_modulus 64) with (2^64) in RO.
  split; [exact KD|]. split; [exact LENB|].
  assert (GO : forall e', e' = kmove (k_data e) (match k_data e with Some _ => k_off e + Z.of_nat (length bs) | None => k_off e end) e ->
               FI nx (kset e' K) C l (with_fds (fd_insert (m_fds mo) (Z_to_bv 64 (k_fd e)) (FdFile (k_path e) (off0 + len_word bs)%bv)) mo)).
  { intros e' ->.
    eapply (FI_advance nx K C l l mo _ e _ (off0 + len_word bs)%bv);
      [exact H| exact He| kndtac| reflexivity| reflexivity| reflexivity| reflexivity| | | intros; rewrite m_fs_with_fds; reflexivity| | reflexivity| reflexivity| exact (FI_nodup_files _ _ _ _ _ H)|].
    - unfold kwf, kmove; cbn. split; [lia|]. destruct (k_data e) as [d|] eqn:ED; [| split; [lia| exact I]].
      destruct (EXA d eq_refl) as (-> & -> & U0). destruct W as (_ & LE & FL & _).
      split; [lia|]. split; [unfold knd; cbn; rewrite KD; exact kfile_KR|]. split; [lia|]. split; [exact FL|]. intros E. congruence.
    - rewrite m_fds_with_fds. unfold mkent. rewrite KD. reflexivity.
    - cbn. rewrite m_fs_with_fds. destruct (k_data e) as [d|] eqn:ED.
      + destruct (EXA d eq_refl) as (-> & -> & U0). split; [| exact FS].
        unfold len_word. rewrite bv_add_lits. reflexivity.
      + exists data. split; [exact FS|]. unfold len_word. pose proof (unsigned_add_le off0 (Z.of_nat (length bs)) ltac:(lia)). lia.
    - intros h f' Hin. exists f'. split; [exact Hin|]. split; [intros e0 X; exact X|]. split; [| intros; lia].
      intros Ho. cbn. destruct (FI_owner_file _ _ _ _ _ _ _ _ H He Ho Hin) as [_ LE']. destruct (k_data e); lia. }
  destruct (k_data e) as [d|] eqn:ED.
  - destruct (EXA d eq_refl) as (-> & E2 & U0). split; [rewrite <- E2; exact Ebs|]. split; [lia|]. apply GO. reflexivity.
  - pose proof (GO _ eq_refl) as G. rewrite kset_self in G; [exact G| | exact (proj1 (FI_KP _ _ _ _ _ H))].
    unfold kmove. destruct e; cbn in *. subst. exact He.
Qed.

#[using="Type"] Lemma read_err e l mo err :
  FI nx K C l mo -> In e K ->
  ((err = EBADF /\ (fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = None \/ (exists p off, fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = Some (FdFileW p off))
                    \/ fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = Some FdNull))     (* [comment removed for export] *)
   \/ (err = EISDIR /\ fd_lookup (m_fds mo) (Z_to_bv 64 (k_fd e)) = Some FdDir)) ->
  k_kind e <> KR.
Proof.
  intros H He X KD. destruct (FI_lookup _ _ _ _ _ H e He) as (off0 & L0 & _). unfold mkent in L0. rewrite KD in L0.
  destruct X as [[_ [N0|[(p & off & L)|L]]]|[_ L]]; rewrite L0 in *; [discriminate| | |]; congruence.
Qed.

#[using="Type"] Lemma fn_read e buf count :
  In e K -> 0 <= count < 2^64 ->
  fnode (NRead (k_fd e) buf count) (dec_read buf count) (FI nx K C) (read_post e count).
Proof.
  intros He Hc l mo H MI. split; [exact I|]. intros rsp mo' evs Hst.
  destruct (nstep_dec_read _ _ _ _ _ _ _ Hc Hst) as (_ & a & Hd & X). exists a. split; [exact Hd|]. destruct a as [err|bs].
  - destruct X as [-> X]. split; [exact (read_err e l mo err H He X)| exact H].
  - destruct X as (p & off & data & L & FS & Ebs & Emo). eapply read_core; eauto.
Qed.

#[using="Type"] Lemma fn_readv e dsts :
  In e K -> Forall (fun d => 0 <= fst d < 2^64 /\ 0 <= snd d < 2^64) dsts -> dsts_total dsts < 2^62 + 2^61 ->
  (k_kind e = KR -> k_data e <> None) ->     (* [comment removed for export] *)
  fnode (NReadv (k_fd e) dsts) (dec_readv dsts) (FI nx K C) (read_post e (dsts_total dsts)).
Proof.
  intros He HF HT2 TRK l mo H MI.
  assert (HT : dsts_total dsts <= 2^64 - 4096) by lia.
  split.
  { (* [comment removed for export] *)
    cbn. intros p off L. destruct (FI_lookup _ _ _ _ _ H e He) as (off0 & L0 & _). rewrite L in L0.
    assert (KD : k_kind e = KR) by (unfold mkent in L0; destruct (k_kind e); [reflexivity| discriminate| discriminate| discriminate]).
    destruct (k_data e) as [d|] eqn:ED; [| exfalso; exact (TRK KD eq_refl)].
    destruct (FI_file_of _ _ _ _ _ H e He ltac:(kndtac)) as (off1 & d1 & L1 & _ & _ & EXA). rewrite L in L1. unfold mkent in L1. rewrite KD in L1. injection L1 as _ <-.
    destruct (EXA d ED) as (_ & _ & U0). pose proof (FI_kwf _ _ _ _ _ H e He) as (_ & _ & W). rewrite ED in W. destruct W as (_ & LE & FL & _).
    unfold FLEN in FL. lia. }
  intros rsp mo' evs Hst.
  pose proof (dsts_total_nonneg dsts ltac:(apply Forall_impl with (2 := HF); intros [? ?] [_ ?]; cbn in *; lia)) as NN.
  destruct (nstep_dec_readv _ _ _ _ _ _ HF HT Hst) as (_ & a & Hd & X). exists a. split; [exact Hd|]. destruct a as [err|bs].
  - destruct X as [-> X]. split; [exact (read_err e l mo err H He X)| exact H].
  - destruct X as (p & off & data & L & FS & Ebs & Emo). eapply read_core; eauto. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma file_write_app d bs : Z.of_nat (length d) < 2^64 -> file_write d (Z_to_bv 64 (Z.of_nat (length d))) bs = d ++ bs.
Proof.
  intros Hd. unfold file_write. destruct bs as [|b bs']; [rewrite app_nil_r; reflexivity|].
  unfold word_to_nat. rewrite unsigned_lit by lia. rewrite Nat2Z.id, Nat.sub_diag. cbn [repeat]. rewrite app_nil_r.
  rewrite firstn_all2 by lia. rewrite skipn_all2 by (cbn; lia). rewrite app_nil_r. reflexivity.
Qed.

#[using="Type"] Lemma fn_writevf e bufs :
  In e K -> kwr e ->     (* [comment removed for export] *)
  match k_data e with Some d => Z.of_nat (length d) + Z.of_nat (length (concat bufs)) <= FLEN | None => Z.of_nat (length (concat bufs)) <= 2^64 - 4096 end ->
  fnode (NWritevF (k_fd e) bufs) (dec_writevf_ok (Z.of_nat (length (concat bufs)))) (FI nx K C)
        (fun r l mo => r = Z.of_nat (length (concat bufs)) /\
           match k_data e with
           | Some d => FI nx (kset (kmove (Some (d ++ concat bufs)) (k_off e + Z.of_nat (length (concat bufs))) e) K) C l mo
           | None => FI nx K C l mo
           end).
Proof.
  intros He KWR BUD l mo H MI. set (bs := concat bufs) in *.
  pose proof (FI_kwf _ _ _ _ _ H e He) as (R & O & W).
  assert (Hl : Z.of_nat (length bs) <= 2^64 - 4096) by (destruct (k_data e); unfold FLEN in BUD; lia).
  destruct KWR as [[KD TRK]|KN].
  2:{ (* [comment removed for export] *)
    destruct (FI_lookup _ _ _ _ _ H e He) as (off & L & _). unfold mkent in L. rewrite KN in L.
    assert (ED : k_data e = None).
    { destruct (k_data e) as [d|]; [| reflexivity]. exfalso. exact (knd_not_KNull e (proj1 W) KN). }
    split; [cbn; right; exact L|].
    intros rsp mo' evs Hst. destruct (nstep_dec_writevf _ _ _ _ _ _ Hl Hst) as (_ & Hd & [(p & off' & data & L' & _)|[_ ->]]); [rewrite L in L'; discriminate|].
    fold bs in Hd. exists (Z.of_nat (length bs)). split; [unfold dec_writevf_ok; rewrite Hd; reflexivity|]. split; [reflexivity|]. rewrite ED. exact H. }
  destruct (k_data e) as [d|] eqn:ED; [| exfalso; exact (TRK eq_refl)]. clear TRK.
  destruct (FI_file_of _ _ _ _ _ H e He ltac:(kndtac)) as (off & d0 & L & FS & LE & EXA). unfold mkent in L. rewrite KD in L.
  destruct (EXA d ED) as (-> & -> & U0). destruct W as (_ & LE' & FL & EQ). specialize (EQ KD).
  split.
  { cbn. left. exists (k_path e), (Z_to_bv 64 (k_off e)), d. split; [exact L|]. split; [exact FS|]. unfold rw_bytes_max. unfold FLEN in *. fold bs. lia. }
  intros rsp mo' evs Hst. destruct (nstep_dec_writevf _ _ _ _ _ _ Hl Hst) as (_ & Hd & [(p & off' & data & L' & FS' & ->)|[L' _]]); [| rewrite L in L'; discriminate].
  rewrite L in L'. injection L' as <- <-. rewrite FS in FS'. injection FS' as <-.
  fold bs in Hd. exists (Z.of_nat (length bs)). split; [unfold dec_writevf_ok; rewrite Hd; reflexivity|]. split; [reflexivity|].
  eapply (FI_advance nx K C l l mo _ e _ (Z_to_bv 64 (k_off e) + len_word bs)%bv);
    [exact H| exact He| kndtac| reflexivity| reflexivity| reflexivity| reflexivity| | | | | reflexivity| reflexivity| exact (FI_nodup_files _ _ _ _ _ H)|].
  - unfold kwf, kmove; cbn. split; [lia|]. rewrite length_app. split; [lia|]. split; [unfold knd; cbn; rewrite KD; exact kfile_KW|]. split; [lia|]. split; [rewrite Nat2Z.inj_add; exact BUD|]. intros _. lia.
  - rewrite m_fds_with_fds. unfold mkent. rewrite KD. reflexivity.
  - intros q NE. rewrite m_fs_with_fds, m_fs_with_fs. apply fs_lookup_set_other. exact NE.
  - cbn. rewrite m_fs_with_fds, m_fs_with_fs, fs_lookup_set_same. rewrite EQ.
    split; [unfold len_word; rewrite bv_add_lits; reflexivity|]. rewrite file_write_app by (unfold FLEN in FL; lia). reflexivity.
  - intros h f' Hin. exists f'. split; [exact Hin|]. split; [intros e0 X; exact X|]. split; [| intros; lia].
    intros Ho. cbn. destruct (FI_owner_file _ _ _ _ _ _ _ _ H He Ho Hin) as [Sh _]. destruct Sh as (_ & _ & _ & Sh). rewrite KD in Sh.
    destruct Sh as (_ & -> & _). unfold zlength. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma fn_lseek e d n :
  In e K -> k_kind e = KR -> k_data e = Some d -> 0 <= n <= k_off e ->
  fnode (NLseek (k_fd e) (- n) SEEK_CUR) dec_lseek_ok (FI nx K C)
        (fun r l mo => r = k_off e - n /\ FI nx (kset (kmove (Some d) (k_off e - n) e) K) C (lrem e l) mo).
Proof.
  intros He KD ED Hn l mo H MI.
  pose proof (FI_kwf _ _ _ _ _ H e He) as (R & O & W). rewrite ED in W. destruct W as (_ & LE & FL & _).
  destruct (FI_lookup_exact _ _ _ _ _ H e d He ED) as [L FS]. specialize (FS ltac:(kndtac)). unfold kent, mkent in L. rewrite KD in L.
  split. { cbn. rewrite L. discriminate. }
  intros rsp mo' evs Hst. destruct Hst as [_ Y]. rewrite L, FS in Y. unfold lseek_result in Y.
  assert (HB : forall cur len, lseek_base (Z_to_bv 64 SEEK_CUR) cur len = Some cur) by (intros; vm_compute; reflexivity).
  rewrite HB in Y. unfold lseek_dest in Y. rewrite unsigned_lit in Y by (unfold FLEN in FL; lia).
  assert (SG : bv_signed (Z_to_bv 64 (- n)) = - n).
  { rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus. change (bv_modulus 64) with (2^64). unfold FLEN in FL. lia. }
  rewrite SG in Y.
  replace ((0 <=? k_off e + - n) && (k_off e + - n <? 2 ^ 63)) with true in Y by (symmetry; apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; unfold FLEN in FL; lia).
  destruct Y as [-> ->]. exists (k_off e - n). split.
  { unfold dec_lseek_ok, dec_lseek. rewrite dec_plain_val; [f_equal; f_equal; lia| unfold FLEN in FL; lia| reflexivity]. }
  split; [reflexivity|].
  replace (k_off e + - n) with (k_off e - n) by lia.
  eapply (FI_advance nx K C l (lrem e l) mo _ e _ (Z_to_bv 64 (k_off e - n)));
    [exact H| exact He| kndtac| reflexivity| reflexivity| reflexivity| reflexivity| | | intros; rewrite m_fs_with_fds; reflexivity| | | | |].
  - unfold kwf, kmove; cbn. split; [lia|]. split; [lia|]. split; [unfold knd; cbn; rewrite KD; exact kfile_KR|]. split; [lia|]. split; [exact FL|]. intros; congruence.
  - rewrite m_fds_with_fds. unfold mkent. rewrite KD. reflexivity.
  - cbn. rewrite m_fs_with_fds. auto.
  - unfold lrem. destruct (k_own e); reflexivity.
  - unfold lrem. destruct (k_own e); reflexivity.
  - unfold lrem. destruct (k_own e); [cbn; apply NoDup_files_remove|]; exact (FI_nodup_files _ _ _ _ _ H).
  - intros h f' Hin. unfold lrem in Hin. destruct (k_own e) as [h0|] eqn:EO.
    + cbn in Hin. apply (In_files_remove _ _ _ (FI_nodup_files _ _ _ _ _ H)) in Hin as [Hin NE]. cbn in NE.
      exists f'. split; [exact Hin|]. split; [intros e0 X; exact X|]. split; [intros E; exfalso; apply NE; congruence| intros; lia].
    + exists f'. split; [exact Hin|]. split; [intros e0 X; exact X|]. split; [intros; discriminate| intros; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma fn_unlink path rmdir :
  K_clear K path ->
  fnode (NUnlink path rmdir) dec_unlink (fun l mo => FI nx K C l mo /\ fs_under (m_fs mo) path = false)
        (fun r l mo => fs_under (m_fs mo) path = false /\
           match r with
           | SErr e => FI nx K C l mo /\ 1 <= e <= 4095
           | SVal v => v = 0 /\ rmdir = false /\ FI nx K (cdel path C) l mo
           end).
Proof.
  intros HC l mo [H NDP] MI. split. { cbn. split; [exact NDP|]. intros _. exact (FI_names_path _ _ _ _ _ H path HC). }
  intros rsp mo' evs Hst. pose proof (nstep_fs_under _ _ _ _ _ Hst path) as FU.
  destruct (nstep_dec_unlink _ _ _ _ _ _ Hst) as (_ & a & Hd & X). exists a. split; [exact Hd|].
  split; [rewrite FU; exact NDP|]. destruct a as [err|v].
  - destruct X as [-> X]. split; [exact H|].
    destruct X as [[_ ->]|[[_ [_ ->]]|[[_ [_ [_ ->]]]|[_ [_ [_ HIn]]]]]]; [destruct rmdir; unfold ENOTEMPTY, State.EISDIR; lia| unfold State.ENOENT; lia| unfold ENOTDIR; lia| apply unlinkat_errnos_range'; exact HIn].
  - destruct X as (-> & _ & _ & -> & _ & ->). split; [reflexivity|]. split; [reflexivity|].
    eapply FI_unlink; [exact H| exact HC| rewrite m_fds_with_fs; reflexivity| rewrite m_fs_with_fs; reflexivity].
Qed.

End Nodes.
End UNodes.

(* [comment removed for export] *)
Module SimMain.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Exec ITree Nodes RelSpec RelSpecMm Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KPin__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require HeapFull Fmt StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require StartupFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Pcap Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KPin__Spec.KPin OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StartupFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Adapter OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW HeapDrive HeapSim NodeSim ProgSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapDrive OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.HeapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.NodeSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

#[local] Notation PS := (PState fheap hptr).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
(* [comment removed for export] *)
Context {CEG CEC : CEIL}.
#[local] Notation fopsG := (full_ops (CE:=CEG)).
#[local] Notation fopsC := (full_ops (CE:=CEC)).
#[using="Type"] Lemma mq_mo0 segsG segsC limG limC enG enC inp : mq (mo0 segsG limG enG inp) (mo0 segsC limC enC inp).
Proof.
  unfold mq, mo0. rewrite !m_fds_init_model, !m_fs_init_model, !m_halted_init_model, !m_tid_init_model, !m_stdin_init_model.
  repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record image_ok (segs : list Segment) (lim : Z) : Prop := mkImageOk {
  io_floor : floor_free segs;
  io_top : 0 < reserved_top (segments_reserved segs);
  io_ceil : reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= band_ceiling;   (* [comment removed for export] *)
  io_blive : reserved_top (segments_reserved segs) + brk_aslr_max + 2 * PGSZ + BLIVE <= bottomup_floor;
  io_lim : BLIVE + RMAX <= lim
}.

#[using="Type"] Lemma image_ok_lim4096 segs lim : image_ok segs lim -> 4096 <= lim.
Proof. intros IO. pose proof (io_lim _ _ IO). unfold BLIVE, RMAX in *. lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma image_ok_ceil {CE : CEIL} segs lim : image_ok segs lim -> reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling.
Proof. intros IO. pose proof (io_ceil _ _ IO) as H. pose proof (@ceil_floor CE) as F. rewrite CEIL_LO_val in F. rewrite band_ceiling_val in H. lia. Qed.

Section SimMain.
(* [comment removed for export] *)
Variables (segsG segsC : list Segment) (limG limC : Z) (enG enC : ExecEntry) (inp : ProcInput).
Variables (tbG tbC : Z) (stkG stkC : stack_site -> Z).
Hypothesis IOG : image_ok segsG limG.
Hypothesis IOC : image_ok segsC limC.
Hypothesis BRKG : valid_brk segsG (en_brk enG).
Hypothesis BRKC : valid_brk segsC (en_brk enC).
Hypothesis TLSG : tls_in_image segsG tbG.
Hypothesis TLSC : tls_in_image segsC tbC.
(* [comment removed for export] *)
Hypothesis VIN : valid_input inp.
Hypothesis CEQG : alloc_ceiling (CEIL:=CEG) = page_round_down_Z (alloc_top (m_vmmaps (mo0 segsG limG enG inp))).
Hypothesis CEQC : alloc_ceiling (CEIL:=CEC) = page_round_down_Z (alloc_top (m_vmmaps (mo0 segsC limC enC inp))).
Variables (secG secC : Z).
Hypothesis SECG : 0 <= secG < 2^64.
Hypothesis SECC : 0 <= secC < 2^64.
(* [comment removed for export] *)
Hypothesis cg_run : forall tm nx config payload,
  zlen (sizes tm) <= 1 -> R63N (sizes tm) <= B26 -> zlength payload < MAX_INPUT ->
  fsimw (npeek segsC) (ProgSim.RQ (CEG:=CEG) (CEC:=CEC) P9 LCI tm nx) (Prog.run fopsG fo_nop stkG config payload) (Prog.run fopsC fo_nop stkC config payload)
        (eqpost (fun _ => fun sG moG sC moC => exists tm' nx',
                   EXT tm tm' /\ PHI P9 + R63N (sizes tm') <= BLIVE /\ ProgSim.RQ (CEG:=CEG) (CEC:=CEC) P9 LCI tm' nx' sG moG sC moC)).

#[local] Notation npk := (npeek segsC).
#[local] Notation RQ := (ProgSim.RQ (CEG:=CEG) (CEC:=CEC) P9 LCI).
#[local] Notation moG0 := (mo0 segsG limG enG inp).
#[local] Notation moC0 := (mo0 segsC limC enC inp).
Definition sG0 : PS := ps_init (fheap_init secG (reservedZ segsG)).
Definition sC0 : PS := ps_init (fheap_init secC (reservedZ segsC)).

(* [comment removed for export] *)
Definition INIT : @rel PS PS := fun sG moG sC moC => sG = sG0 /\ moG = moG0 /\ sC = sC0 /\ moC = moC0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma HQ_main {CE : CEIL} segs lim en sec tb t mo :
  image_ok segs lim -> valid_brk segs (en_brk en) -> 0 <= sec < 2^64 ->
  startup_mo segs lim en inp tb t mo ->
  HeapSim.HQ P9 htrue (set_tls_pin full_ops tb (ps_init (fheap_init sec (reservedZ segs)))) mo.
Proof.
  intros IO BRK SEC (Hvm & _ & _ & Hh & _ & _ & _ & MI & Htb & Hktop). split.
  - cbn [ps_heap set_tls_pin set_tls set_heap ps_init ho_pin full_ops]. rewrite hf_pin_init. unfold tok_blocks. cbn [fh_blk fheap_init]. rewrite map_to_list_empty. cbn [map].
    eapply (FQ_main segs (en_brk en) (en_mmap_base en) (en_sp en) lim tb mo Hvm Hktop MI Hh BRK (io_top _ _ IO) (image_ok_ceil _ _ IO) (io_blive _ _ IO) (io_lim _ _ IO) Htb P9 htrue _ sec SEC);
      [reflexivity| reflexivity| apply P9_ok| exact I].
  - intros k. cbn. rewrite lookup_empty. intros H. exfalso. apply H. reflexivity.
Qed.

#[using="IOG IOC BRKG BRKC SECG SECC"] Lemma RQ_main bG bC t moG moC :
  startup_mo (CE:=CEG) segsG limG enG inp bG t moG -> startup_mo (CE:=CEC) segsC limC enC inp bC t moC ->
  RQ ∅ 0%N (set_tls_pin fopsG bG sG0) moG (set_tls_pin fopsC bC sC0) moC.
Proof.
  intros SG SC. split; [| split; [| split; [| split; [| split; [| split]]]]].
  - split; [exact (HQ_main (CE:=CEG) segsG limG enG secG bG t moG IOG BRKG SECG SG)| split; [exact (HQ_main (CE:=CEC) segsC limC enC secC bC t moC IOC BRKC SECC SC)|]].
    split; reflexivity.
  - cbn. unfold tok_szmap. cbn. apply fmap_empty.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct SG as (_ & F1 & F2 & F3 & F4 & F5 & _). destruct SC as (_ & G1 & G2 & G3 & G4 & G5 & _).
    pose proof (mq_mo0 segsG segsC limG limC enG enC inp) as (M1 & M2 & M3 & M4 & M5).
    unfold mq. rewrite F1, F2, F3, F4, F5, G1, G2, G3, G4, G5. repeat split; congruence.
  - cbn. apply LCI_init.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="IOC TLSC VIN CEQC secG secC SECG SECC"] Lemma startup_exists (s : PS) t : 0 < t < PID_MAX_ENVELOPE ->
  exists tb mo', tpath nstep (startup_model (set_tls_pin fopsC) tbC s) moC0 [] (Ok (tt, set_tls_pin fopsC tb s)) mo'
    /\ startup_mo (CE:=CEC) segsC limC enC inp tb t mo'.
Proof.
  intros Ht.
  assert (Htid0 : m_tid moC0 = None) by (unfold TopLevel.mo0; apply m_tid_init_model).
  set (mo2 := with_tid (Z_to_bv 64 t) moC0).
  assert (Hst2 : nstep NSetTid moC0 (eff0 (Z_to_bv 64 t)) mo2 []).
  { cbn [nstep]. split; [reflexivity|]. exists (Z_to_bv 64 t). split; [reflexivity|]. rewrite Htid0. rewrite unsigned_lit by (unfold PID_MAX_ENVELOPE in *; lia). split; [exact Ht| reflexivity]. }
  assert (TP : tpath nstep (startup_model (set_tls_pin fopsC) tbC s) moC0 [] (Ok (tt, set_tls_pin fopsC tbC s)) mo2).
  { unfold startup_model, mbind, msys, mupd, mret, enode. cbn [tpath ITree.bind ebind fst snd].
    exists (eff0 (Z_to_bv 64 t)), mo2, [], []. split; [exact Hst2|]. split; [| reflexivity].
    pose proof (mo0_minv segsC limC enC inp VIN) as MI0.
    destruct (nstep_dec_set_tid moC0 _ mo2 [] MI0 Hst2) as (_ & t' & Hd & _). rewrite Hd. cbn. split; [reflexivity|]. split; reflexivity. }
  exists tbC, mo2. split; [exact TP|].
  destruct (startup_tpath (CE:=CEC) (set_tls_pin fopsC) segsC limC enC inp tbC TLSC VIN CEQC s [] _ mo2 TP) as (tb' & t' & E & _ & Etb & Ht' & SM).
  (* [comment removed for export] *)
  assert (Et : t' = t).
  { destruct SM as (_ & _ & _ & _ & _ & Htid & _). unfold mo2 in Htid. rewrite m_tid_with_tid in Htid.
    apply (f_equal (fun o => match o with Some w => bv_unsigned w | None => 0 end)) in Htid.
    rewrite !unsigned_lit in Htid by (unfold PID_MAX_ENVELOPE in *; lia). lia. }
  subst t' tb'. exact SM.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma startup_npfree {CE : CEIL} tb (s : PS) : npfree (npeek segsC) (startup_model (set_tls_pin full_ops) tb s).
Proof.
  unfold startup_model, mbind, msys, mupd, mret, enode. cbn [npfree ITree.bind ebind npeek fst snd].
  split; [reflexivity|]. intros rsp2. destruct (dec_set_tid rsp2); cbn; exact I.
Qed.

(* [comment removed for export] *)
#[using="IOG IOC BRKG BRKC TLSG TLSC VIN CEQG CEQC SECG SECC"] Theorem cg_startup :
  fsimw npk INIT (startup_model (set_tls_pin fopsG) tbG) (startup_model (set_tls_pin fopsC) tbC) (fun _ _ => RQ ∅ 0%N).
Proof.
  intros sG moG sC moC (-> & -> & -> & ->). split.
  - intros trG a sG' moG' Hp.
    destruct (startup_tpath (CE:=CEG) (set_tls_pin fopsG) segsG limG enG inp tbG TLSG VIN CEQG sG0 trG _ moG' Hp)
      as (tbG' & t & E & -> & _ & Ht & SMG).
    injection E as _ Es. subst sG'. destruct a.
    destruct (startup_exists sC0 t Ht) as (tbC' & moC' & TPC & SMC).
    eapply wreach_mono; [eapply tpath_wreach; [apply startup_npfree| exact TPC]|].
    intros tr r mo'' (-> & -> & ->). exists tt, (set_tls_pin fopsC tbC' sC0). split; [reflexivity|]. split; [reflexivity|].
    exact (RQ_main tbG' tbC' t moG' moC' SMG SMC).
  - intros trG Hx. exfalso. exact (startup_texit (set_tls_pin fopsG) segsG limG enG inp tbG sG0 trG Hx).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="IOG IOC BRKG BRKC TLSG TLSC VIN CEQG CEQC SECG SECC cg_run"] Theorem cg_prog argv :
  fsimw npk INIT (prog fopsG tbG fo_nop stkG argv) (prog fopsC tbC fo_nop stkC argv) (fun _ _ => INIT).
Proof.
  unfold prog.
  eapply fsimw_bind; [apply cg_startup|]. intros [] [].
  eapply fsimw_bind; [apply (cg_main_prog segsC stkG stkC cg_run 0%N argv)|]. intros codeG codeC.
  apply rq_pure; intros <-. apply fsimw_exI; intros tm'. apply fsimw_exI; intros nx'.
  apply (cg_exit_model segsC P9).
Qed.

End SimMain.

End WithCeil.
End SimMain.

(* [comment removed for export] *)
Module EquivPlan.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ HeapFull StdioCore Stdio StartupFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Pcap Prog. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.HeapFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StartupFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.Driver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prog.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimW ProgSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv Require SimStdio__Equiv. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimW OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.ProgSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimStdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.SimStdio__Equiv.SimDriver OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Equiv.UNodes__Equiv.SimMain.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2 Require Import TopLevel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Top Require Import EntryCeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma budgets_ok : BLIVE + RMAX <= source_alloc_limit /\ BLIVE + RMAX <= target_alloc_limit.
Proof. unfold BLIVE, RMAX, source_alloc_limit, target_alloc_limit. split; lia. Qed.

(* [comment removed for export] *)
Lemma budgets_ok_san : BLIVE + RMAX <= sanitizer_source_limit.
Proof. unfold BLIVE, RMAX, sanitizer_source_limit. lia. Qed.

Lemma valid_entry_brk segs pc ph en inp : valid_entry (mkImage segs pc ph) en inp -> valid_brk segs (en_brk en).
Proof. apply valid_entry_brk'. Qed.

(* [comment removed for export] *)
Definition ptree (segs : list Segment) (tb : ExecEntry -> Z) (stk : ExecEntry -> stack_site -> Z)
    (sec : ExecEntry -> Z) : prog_tree (exc unit) :=
  fun inp en => prog_itree (full_ops (CE:=ceil_of_sp (en_sp en))) (tb en)
                  (fheap_init (sec en) (reservedZ segs)) fo_nop (stk en) (in_argv inp).

Section Plan.
(* [comment removed for export] *)
Variables (segsS : list Segment) (pcS : N) (phS : PhdrInfo).
Variables (segsT : list Segment) (pcT : N) (phT : PhdrInfo).
(* [comment removed for export] *)
Variables (tbS tbT : ExecEntry -> Z) (stkS stkT : ExecEntry -> stack_site -> Z).
Variables (secS secT : ExecEntry -> Z).
Hypothesis SECS : forall en, 0 <= secS en < 2^64.
Hypothesis SECT : forall en, 0 <= secT en < 2^64.

(* [comment removed for export] *)
Definition treeS : prog_tree (exc unit) := ptree segsS tbS stkS secS.
Definition treeT : prog_tree (exc unit) := ptree segsT tbT stkT secT.

(* [comment removed for export] *)
Variables (limS limT : Z).
Hypothesis IOS : image_ok segsS limS.
Hypothesis IOT : image_ok segsT limT.
Hypothesis TLSS : forall en inp, valid_entry (mkImage segsS pcS phS) en inp -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.tls_in_image segsS (tbS en).
Hypothesis TLST : forall en inp, valid_entry (mkImage segsT pcT phT) en inp -> OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.tls_in_image segsT (tbT en).

(* [comment removed for export] *)
Definition run_contract (segsC : list Segment) (stkG stkC : stack_site -> Z) : Prop :=
  forall (CEG CEC : CEIL) tm nx config payload,
    zlen (sizes tm) <= 1 -> R63N (sizes tm) <= B26 -> zlength payload < MAX_INPUT ->
    fsimw (npeek segsC) (RQ (CEG:=CEG) (CEC:=CEC) P9 LCI tm nx)
          (Prog.run (full_ops (CE:=CEG)) fo_nop stkG config payload) (Prog.run (full_ops (CE:=CEC)) fo_nop stkC config payload)
          (eqpost (fun _ => fun sG moG sC moC => exists tm' nx',
                     EXT tm tm' /\ PHI P9 + R63N (sizes tm') <= BLIVE /\ RQ (CEG:=CEG) (CEC:=CEC) P9 LCI tm' nx' sG moG sC moC)).
Hypothesis RUN_ST : forall enS enT, run_contract segsT (stkS enS) (stkT enT).
Hypothesis RUN_TS : forall enS enT, run_contract segsS (stkT enT) (stkS enS).

(* [comment removed for export] *)

#[using="Type"] Lemma prog_texit_wexit : forall {CEG CEC : CEIL} segsC (R : @rel (PState fheap hptr) (PState fheap hptr)) aG aC hG hC stkG stkC argv moG moC,
  fsimw (npeek segsC) R (prog (full_ops (CE:=CEG)) aG fo_nop stkG (argv_Z argv)) (prog (full_ops (CE:=CEC)) aC fo_nop stkC (argv_Z argv)) (fun _ _ => R) ->
  R (ps_init hG) moG (ps_init hC) moC ->
  forall full, texit nstep nexit (prog_itree (full_ops (CE:=CEG)) aG hG fo_nop stkG argv) moG full ->
               wexit (npeek segsC) nstep nexit (prog_itree (full_ops (CE:=CEC)) aC hC fo_nop stkC argv) moC (eq full).
Proof.
  intros CEG CEC segsC R aG aC hG hC stkG stkC argv moG moC Hsim HR full Hx.
  unfold prog_itree in *. apply texit_ebind in Hx.
  destruct (Hsim _ _ _ _ HR) as [HP HE].
  destruct Hx as [Hx|(tr1 & [a s'] & mo1 & tr2 & Hp1 & Hx2 & ->)].
  - apply wexit_ebind_l. exact (HE full Hx).
  - destruct a.
Qed.

#[using="SECS SECT IOS IOT TLSS TLST RUN_ST RUN_TS"] Theorem route_abs_trees_equiv : trees_equiv_lim limS limT segsS pcS phS segsT pcT phT treeS treeT.
Proof.
  apply trees_equiv_lim_of_wexit. intros enS enT inp HvS HvT Hvi. split; intros full Hx.
  - eapply (prog_texit_wexit (CEG:=ceil_of_sp (en_sp enS)) (CEC:=ceil_of_sp (en_sp enT)) segsT
              (INIT segsS segsT limS limT enS enT inp (secS enS) (secT enT))).
    + exact (cg_prog (CEG:=ceil_of_sp (en_sp enS)) (CEC:=ceil_of_sp (en_sp enT))
               segsS segsT limS limT enS enT inp (tbS enS) (tbT enT) (stkS enS) (stkT enT)
               IOS IOT (valid_entry_brk _ _ _ _ _ HvS) (valid_entry_brk _ _ _ _ _ HvT) (TLSS _ _ HvS) (TLST _ _ HvT)
               Hvi (mo0_ceil_valid _ _ _ _ _ _ Hvi HvS) (mo0_ceil_valid _ _ _ _ _ _ Hvi HvT)
               (secS enS) (secT enT) (SECS enS) (SECT enT) (RUN_ST enS enT _ _) (argv_Z (in_argv inp))).
    + repeat split; reflexivity.
    + exact Hx.
  - eapply (prog_texit_wexit (CEG:=ceil_of_sp (en_sp enT)) (CEC:=ceil_of_sp (en_sp enS)) segsS
              (INIT segsT segsS limT limS enT enS inp (secT enT) (secS enS))).
    + exact (cg_prog (CEG:=ceil_of_sp (en_sp enT)) (CEC:=ceil_of_sp (en_sp enS))
               segsT segsS limT limS enT enS inp (tbT enT) (tbS enS) (stkT enT) (stkS enS)
               IOT IOS (valid_entry_brk _ _ _ _ _ HvT) (valid_entry_brk _ _ _ _ _ HvS) (TLST _ _ HvT) (TLSS _ _ HvS)
               Hvi (mo0_ceil_valid _ _ _ _ _ _ Hvi HvT) (mo0_ceil_valid _ _ _ _ _ _ Hvi HvS)
               (secT enT) (secS enS) (SECT enT) (SECS enS) (RUN_TS enS enT _ _) (argv_Z (in_argv inp))).
    + repeat split; reflexivity.
    + exact Hx.
Qed.

(* [comment removed for export] *)
Hypothesis tree_ok_S : exists QS, tree_ok segsS pcS phS limS treeS QS.
Hypothesis tree_ok_T : exists QT, tree_ok segsT pcT phT limT treeT QT.

(* [comment removed for export] *)
#[using="tbS tbT stkS stkT secS secT SECS SECT IOS IOT TLSS TLST RUN_ST RUN_TS tree_ok_S tree_ok_T"] Theorem route_abs_main :
  strong_universal_error_free_T_scfg_budgets CFG limS limT (mkImage segsS pcS phS) (mkImage segsT pcT phT).
Proof.
  destruct tree_ok_S as [QS HS]. destruct tree_ok_T as [QT HT].
  exact (strong_universal_error_free_scfg_budgets_from_trees_gen limS limT
           segsS pcS phS segsT pcT phT treeS treeT QS QT HS HT route_abs_trees_equiv).
Qed.
End Plan.
End EquivPlan.
