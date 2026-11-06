(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import CatSim ShapeAlg AsanAcct AsanAcctShape.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode RzCPS NodesA.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_alt_wall' : forall (ch : word) (rest : list byte) (T : TSet),
  (1 <= length rest)%nat ->
  t_eq (t_alt (fun i : wr_index rest =>
          t_emit (map (WriteEv ch) (firstn (proj1_sig i) rest))
                 (t_emit (map (WriteEv ch) (skipn (proj1_sig i) rest)) T)))
       (t_emit (map (WriteEv ch) rest) T).
Proof.
  intros ch rest T Hnb tr. split.
  - intros [[n [Hn1 Hn2]] Hi]. cbn [proj1_sig] in Hi.
    destruct Hi as [Hp | (tr1 & -> & Hi)].
    + left. eapply is_prefix_trans; [exact Hp|].
      rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
      apply is_prefix_app_r. apply is_prefix_refl.
    + destruct Hi as [Hp | (tr2 & -> & Ht)].
      * left.
        rewrite <- (firstn_skipn n rest) at 2. rewrite map_app.
        apply is_prefix_app_mono. exact Hp.
      * right. exists tr2. split; [|exact Ht].
        rewrite app_assoc, <- map_app, firstn_skipn. reflexivity.
  - intros [Hp | (tr' & -> & Ht)].
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all. left. exact Hp.
    + exists (wr_full rest Hnb). unfold wr_full. cbn [proj1_sig].
      rewrite firstn_all, skipn_all. right.
      exists tr'. split; [reflexivity|].
      cbn [map]. right. exists tr'. split; [reflexivity | exact Ht].
Qed.

Section WriteAll.
Variable segs : list Segment.

Definition wnode (P : config -> Prop) (ch : word) (bs : list byte) (K : nat -> config -> Prop) : Prop :=
  forall (T : nat -> TSet) c, P c ->
    (forall k c', (1 <= k <= length bs)%nat -> K k c' -> realizes segs c' (T k)) ->
    realizes segs c (t_alt (fun i : wr_index bs => t_emit (map (WriteEv ch) (firstn (proj1_sig i) bs)) (T (proj1_sig i)))).

Lemma cpsE_write_all : forall (P : list byte -> config -> Prop) (R : list byte -> nat -> config -> Prop) Q ch,
  (forall rest, rest <> [] -> wnode (P rest) ch rest (R rest)) ->
  (forall rest k, (1 <= k < length rest)%nat -> cps segs (R rest k) (P (skipn k rest))) ->
  (forall rest, rest <> [] -> cps segs (R rest (length rest)) Q) ->
  forall rest, rest <> [] -> cpsE segs (P rest) (map (WriteEv ch) rest) Q.
Proof.
  intros P R Q ch Hnode Hshort Hfull rest.
  induction rest as [rest IH] using (well_founded_induction (Wf_nat.well_founded_ltof _ (@length byte))).
  intros Hne T c HP Hk.
  assert (Hnb : (1 <= length rest)%nat) by (destruct rest; [congruence| cbn; lia]).
  assert (Hcont : forall k c', (1 <= k <= length rest)%nat -> R rest k c' ->
            realizes segs c' (t_emit (map (WriteEv ch) (skipn k rest)) T)).
  { intros k c' Hk1 HR. destruct (Nat.eq_dec k (length rest)) as [->|NE].
    - rewrite skipn_all. cbn [map]. pose proof (Hfull rest Hne T c' HR Hk) as R1.
      eapply rz_conseq; [exact R1|]. apply t_eq_sym. apply t_emit_nil_eq. eapply realizes_nonempty. exact R1.
    - apply (Hshort rest k ltac:(lia) _ c' HR). intros c'' HP''.
      apply (IH (skipn k rest)); [unfold ltof; rewrite length_skipn; lia| |exact HP''| exact Hk].
      intros E. apply (f_equal (@length byte)) in E. rewrite length_skipn in E. cbn in E. lia. }
  pose proof (Hnode rest Hne (fun k => t_emit (map (WriteEv ch) (skipn k rest)) T) c HP Hcont) as Rn.
  eapply rz_conseq; [exact Rn|]. apply t_alt_wall'. exact Hnb.
Qed.

End WriteAll.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma wa_add16 : forall a, (wa a + 16)%bv = wa (a + 16).
Proof. intros a. rewrite wa_add. change (bv_unsigned (16%bv : word)) with 16. reflexivity. Qed.

Lemma copy_iovecs_accesses_avoid : forall (H : word -> bool) mp k a,
  0 <= a -> a + 16 * Z.of_nat k <= 2^64 ->
  (forall i, (i < 16 * k)%nat -> H (wa (a + Z.of_nat i)) = false) ->
  ranges_avoid H (copy_iovecs_accesses mp (wa a) k).
Proof.
  intros H mp. induction k as [|k IH]; intros a Ha Hak Hvis; cbn [copy_iovecs_accesses]; [apply ranges_avoid_nil'|].
  apply ranges_avoid_cons.
  - apply (range_avoids_of_visible H a 16); [lia| lia|]. intros i Hi. apply Hvis. lia.
  - destruct (read_iovec_entry mp (wa a)); try apply ranges_avoid_nil'.
    rewrite wa_add16. apply IH; [lia| lia|].
    intros i Hi. replace (a + 16 + Z.of_nat i) with (a + Z.of_nat (16 + i)) by lia. apply Hvis. lia.
Qed.

Lemma import_iovecs_accesses_avoid : forall (H : word -> bool) mp a n,
  0 <= a -> a + 16 * Z.of_nat n <= 2^64 -> (n <= 1024)%nat ->
  (forall i, (i < 16 * n)%nat -> H (wa (a + Z.of_nat i)) = false) ->
  ranges_avoid H (import_iovecs_accesses mp (wa a) (Z_to_bv 64 (Z.of_nat n))).
Proof.
  intros H mp a n Ha Han Hn Hvis. unfold import_iovecs_accesses.
  destruct (bv_eqb (Z_to_bv 64 (Z.of_nat n)) (Z_to_bv 64 1)) eqn:E1.
  - apply bv_eqb_eq in E1. apply (f_equal bv_unsigned) in E1. rewrite !unsigned_lit in E1 by lia.
    destruct (negb _); [apply ranges_avoid_nil'|]. apply ranges_avoid_cons; [|apply ranges_avoid_nil'].
    apply (range_avoids_of_visible H a 16); [lia| lia|]. intros i Hi. apply Hvis. lia.
  - destruct (bv_eqb _ (Z_to_bv 64 0)); [apply ranges_avoid_nil'|].
    destruct (IOV_MAX <? _); [apply ranges_avoid_nil'|]. destruct (negb _); [apply ranges_avoid_nil'|].
    unfold word_to_nat. rewrite unsigned_lit by lia. rewrite Nat2Z.id.
    apply copy_iovecs_accesses_avoid; assumption.
Qed.

Lemma iov_prefix_accesses_avoid : forall (H : word -> bool) iovs (bufs : list (list byte)) left,
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ Z.of_nat (length bs) < 2^63 /\
             0 <= bv_unsigned (fst iov) /\ bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^64 /\
             (forall i, (i < length bs)%nat -> H (wa (bv_unsigned (fst iov) + Z.of_nat i)) = false)) iovs bufs ->
  ranges_avoid H (iov_prefix_accesses iovs left).
Proof.
  intros H iovs bufs left HF. revert left.
  induction HF as [|[b l] bs iovs bufs (Hl & Hlen & Hb0 & Hb1 & Hvis) _ IH]; intros left;
    destruct left as [|left]; cbn [iov_prefix_accesses]; try apply ranges_avoid_nil'.
  cbn [fst snd] in *. subst l.
  destruct (Nat.eqb _ 0); [apply IH|]. apply ranges_avoid_cons; [|apply IH].
  rewrite <- (wa_unsigned_id b). rewrite word_to_nat_bounded_eq_min.
  unfold word_to_nat. rewrite unsigned_lit by lia. rewrite Nat2Z.id.
  apply (range_avoids_of_visible H); [lia| lia|]. intros i Hi. apply Hvis. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WV.
Variable segs : list Segment.
Variable segtop : Z.
Hypothesis Hwx : wx_segs_nowrap segs.
Hypothesis Hsegs : segs_below_b segs segtop = true.

(* [comment removed for export] *)
Lemma writev_at_transfer : forall (H : word -> bool) ms fd bufs, H_off_segments segs H ->
  at_node segs (NWritev fd bufs) (restrict H ms) ->
  at_node segs (NWritev fd bufs) ms /\
  (exists iovs : list (word * word),
     bytes_at segs (ms_mem ms) (bv_unsigned (areg ms 11)) (iovec_bytes iovs) /\
     (forall i, (i < length (iovec_bytes iovs))%nat -> H (wa (bv_unsigned (areg ms 11) + Z.of_nat i)) = false) /\
     Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                            bv_unsigned (fst iov) + Z.of_nat (length bs) <= 0x800000000000 /\
                            bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs /\
                            (forall i, (i < length bs)%nat -> H (wa (bv_unsigned (fst iov) + Z.of_nat i)) = false)) iovs bufs).
Proof.
  intros H ms fd bufs HH (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Htot & Hrom & Hiotop & iovs & Hiov & Hbufs).
  rewrite restrict_mem, restrict_areg in Hiov. destruct (bytes_at_restrict segs H HH _ _ _ Hiov) as [Hiov' Hvis].
  assert (HF : Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                            bv_unsigned (fst iov) + Z.of_nat (length bs) <= 0x800000000000 /\
                            bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs /\
                            (forall i, (i < length bs)%nat -> H (wa (bv_unsigned (fst iov) + Z.of_nat i)) = false)) iovs bufs).
  { eapply Forall2_impl; [|exact Hbufs]. intros iov bs (Hl & Ht & Hb). rewrite restrict_mem in Hb.
    destruct (bytes_at_restrict segs H HH _ _ _ Hb) as [Hb' Hv]. auto. }
  split.
  - split; [exact Hsvc|]. split; [exact Hfd|]. split; [exact Ha0|]. split; [exact Ha2|]. split; [exact Hcnt|].
    split; [exact Htot|]. split; [exact Hrom|]. split; [exact Hiotop|]. exists iovs. split; [exact Hiov'|].
    eapply Forall2_impl; [|exact HF]. intros iov bs (Hl & Ht & Hb & _). auto.
  - exists iovs. split; [exact Hiov'|]. split; [exact Hvis| exact HF].
Qed.

Theorem ast_writev : forall A Pm PM (K : nat -> machine_state -> Prop) KM fd bufs,
  (1 <= length (concat bufs))%nat -> mat_stable KM ->
  (forall ms, Pm ms -> at_node segs (NWritev fd bufs) ms /\
     forall k, (1 <= k <= length (concat bufs))%nat -> K k (nretA ms (eff0 (Z_to_bv 64 (Z.of_nat k))))) ->
  (forall mo, PM mo -> fd_lookup (m_fds mo) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) /\ KM mo) ->
  wnode segs (AST segtop A Pm PM) (Z_to_bv 64 fd) (concat bufs) (fun k => AST segtop A (K k) KM).
Proof using Hwx Hsegs.
  intros A Pm PM K KM fd bufs Hnb HKM Hm HM T [ms mo] Hc Hkont.
  pose proof (AST_off segs segtop Hsegs A Pm PM _ Hc) as HH. pose proof Hc as (Hmc & HPm & HPM & _). cbn [cfg_ms cfg_model] in *.
  destruct (Hm _ HPm) as (Hat & HK). destruct (HM _ HPM) as (Hfdl & HKMm).
  destruct (writev_at_transfer _ ms fd bufs HH Hat) as [Hat' (iovs & Hiov & Hvisa & HF)].
  pose proof Hat' as (Hsvc & Hfd & Ha0 & Ha2 & Hcnt & Htot & Hrom & Hiotop & _).
  unfold MAX_RW_COUNT in Htot.
  assert (Hbufs : Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\
                               bv_unsigned (fst iov) + Z.of_nat (length bs) <= 0x800000000000 /\
                               bytes_at segs (ms_mem ms) (bv_unsigned (fst iov)) bs) iovs bufs).
  { eapply Forall2_impl; [|exact HF]. intros iov bs (Hl & Ht & Hb & _). auto. }
  destruct (iovs_ok_of_at segs _ _ _ Hrom Hbufs ltac:(lia)) as [Hok HlenT].
  pose proof (Forall2_length Hbufs) as Hleq.
  assert (Hw : w_is0 (Z_to_bv 64 fd) = false) by (destruct Hfd as [-> | ->]; reflexivity).
  set (i := sys_input segs ms (Z_to_bv 64 66)).
  assert (Hsp : forall o, syscall_spec i mo o <->
            writev_spec (Z_to_bv 64 fd) (areg ms 11) (Z_to_bv 64 (Z.of_nat (length iovs))) i mo o).
  { intros o. subst i. rewrite syscall_spec_66 by reflexivity. rewrite in_a0_si, in_a1_si, in_a2_si, Ha0, Ha2, Hleq.
    rewrite fd32_id by (rewrite unsigned_lit; destruct Hfd; lia). reflexivity. }
  assert (Hcnt32 : iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))) = Z_to_bv 64 (Z.of_nat (length iovs))).
  { unfold iovcnt32, abi_low32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. }
  assert (Himp : import_iovecs (in_mem i) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs)))) = ImpOk iovs).
  { rewrite Hcnt32. subst i. rewrite in_mem_si. rewrite <- (wa_unsigned_id (areg ms 11)).
    pose proof (bytes_at_in _ _ _ _ Hrom Hiov) as Hin.
    apply (import_iovecs_bytes_in iovs bufs); [exact Hin| exact HlenT| lia | unfold TASK_SIZE; lia | unfold MAX_RW_COUNT; lia]. }
  set (bs := concat bufs) in *.
  assert (Htotal : iovs_total iovs = Z.of_nat (length bs)) by (subst bs; eapply iovs_total_ok; exact Hok).
  assert (Hg : gather_iovecs (in_mem i) iovs = Some bs) by (subst i bs; rewrite in_mem_si; apply gather_iovecs_ok; exact Hok).
  set (CA := import_iovecs_accesses (in_mem i) (areg ms 11) (iovcnt32 (Z_to_bv 64 (Z.of_nat (length iovs))))).
  assert (Hchar : forall o, syscall_spec i mo o <->
            exists k, (1 <= k <= length bs)%nat /\
              o = Ok (mkEffectU (Z_to_bv 64 (Z.of_nat k)) [] [] [] [] (CA ++ iov_prefix_accesses iovs k))
                     mo (map (WriteEv (Z_to_bv 64 fd)) (firstn k bs))).
  { intros o. rewrite Hsp.
    apply (writev_chan_outcome _ _ _ i mo o (Z_to_bv 64 fd) iovs bs Hfdl Hw Himp); [|exact Hg| lia].
    rewrite Htotal. unfold MAX_RW_COUNT. subst bs. lia. }
  (* [comment removed for export] *)
  assert (HavCA : ranges_avoid (HID A mo) CA).
  { subst CA. rewrite Hcnt32. rewrite <- (wa_unsigned_id (areg ms 11)). pose proof Hiov as (Hb0 & Hb1 & _).
    rewrite length_iovec_bytes in Hb1, Hvisa.
    apply import_iovecs_accesses_avoid; [lia| lia| lia|]. intros k Hk. apply Hvisa. lia. }
  assert (HavP : forall k, ranges_avoid (HID A mo) (iov_prefix_accesses iovs k)).
  { intros k. apply (iov_prefix_accesses_avoid _ iovs bufs k).
    clear -HF HlenT. induction HF as [|iov bs0 iovs bufs (Hl & Ht & Hb & Hv) _ IH]; [constructor|].
    inversion HlenT as [|? ? ? ? (_ & Hlen63 & _) HT']; subst. constructor; [|apply IH; exact HT'].
    pose proof Hb as (Hb0 & Hb1 & _). split; [exact Hl|]. split; [exact Hlen63|]. split; [exact Hb0|]. split; [lia| exact Hv]. }
  destruct (ast_node_core segs segtop A Pm PM (wr_index bs) (fun k => map (WriteEv (Z_to_bv 64 fd)) (firstn (proj1_sig k) bs))
             (fun k => K (proj1_sig k)) (fun _ => KM) ms mo (Z_to_bv 64 66)
             (fun k => mkEffectU (Z_to_bv 64 (Z.of_nat (proj1_sig k))) [] [] [] [] (CA ++ iov_prefix_accesses iovs (proj1_sig k)))
             (fun _ => mo) Hc Hsvc) as (nx & Hnd & Hnx).
  - vm_compute; reflexivity.
  - intros [k Hk]. apply Hchar. exists k. split; [exact Hk| reflexivity].
  - intros r Hr. apply Hchar in Hr as (k & Hk & ->). exists (exist _ k Hk). reflexivity.
  - intros _. apply vm_same_refl.
  - intros k. repeat split; reflexivity.
  - intros [k Hk]. unfold syscall_effect_accesses. cbn [eff_copyins eff_writes write_accesses proj1_sig]. rewrite app_nil_r.
    apply ranges_avoid_app; [exact HavCA| apply HavP].
  - intros [k Hk]. cbn [proj1_sig]. exact (HK k Hk).
  - intros _. exact HKMm.
  - intros _. exact HKM.
  - apply (rz_node segs _ (wr_index bs) _ nx (fun k => T (proj1_sig k)) (wr_full bs Hnb) Hnd).
    intros [k Hk]. apply (Hkont k (nx (exist _ k Hk)) Hk (Hnx _)).
Qed.

End WV.

